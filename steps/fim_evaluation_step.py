
import os
import csv
import math
from collections import Counter
from pathlib import Path
from typing import Dict, List
from zenml import step
import mlflow
import difflib
from dataclasses import dataclass


@dataclass
class FIMMetrics:
    model_name: str
    exact_match: bool
    line_accuracy: float
    similarity_ratio: float
    total_lines_gt: int
    total_lines_generated: int
    matching_lines: int
    edit_distance: int
    bleu_score: float
    rouge_l_f1: float

    def to_dict(self) -> Dict:
        return {
            "Model": self.model_name,
            "Exact_Match": "YES" if self.exact_match else "NO",
            "Line_Accuracy": f"{self.line_accuracy:.2%}",
            "Similarity_Ratio": f"{self.similarity_ratio:.4f}",
            "BLEU": f"{self.bleu_score:.4f}",
            "ROUGE_L_F1": f"{self.rouge_l_f1:.4f}",
            "GT_Lines": self.total_lines_gt,
            "Generated_Lines": self.total_lines_generated,
            "Matching_Lines": self.matching_lines,
            "Edit_Distance": self.edit_distance,
        }


def calculate_edit_distance(s1: str, s2: str) -> int:
    if len(s1) < len(s2):
        return calculate_edit_distance(s2, s1)
    if len(s2) == 0:
        return len(s1)

    previous_row = range(len(s2) + 1)
    for i, c1 in enumerate(s1):
        current_row = [i + 1]
        for j, c2 in enumerate(s2):
            insertions = previous_row[j + 1] + 1
            deletions = current_row[j] + 1
            substitutions = previous_row[j] + (c1 != c2)
            current_row.append(min(insertions, deletions, substitutions))
        previous_row = current_row
    return previous_row[-1]


def calculate_bleu(reference: str, candidate: str, max_n: int = 4) -> float:
    ref_tokens = reference.split()
    cand_tokens = candidate.split()

    if len(cand_tokens) == 0:
        return 0.0

    precisions = []
    for n in range(1, max_n + 1):
        ref_ngrams = Counter([tuple(ref_tokens[i:i+n]) for i in range(len(ref_tokens)-n+1)])
        cand_ngrams = Counter([tuple(cand_tokens[i:i+n]) for i in range(len(cand_tokens)-n+1)])

        overlap = sum((ref_ngrams & cand_ngrams).values())
        total = sum(cand_ngrams.values())

        if total == 0:
            precisions.append(0)
        else:
            precisions.append(overlap / total)

    if min(precisions) == 0:
        return 0.0

    brevity_penalty = min(1.0, math.exp(1 - len(ref_tokens) / len(cand_tokens))) if len(ref_tokens) > 0 else 0
    geometric_mean = math.exp(sum(math.log(p) if p > 0 else float('-inf') for p in precisions) / len(precisions))

    return brevity_penalty * geometric_mean


def calculate_rouge_l(reference: str, candidate: str) -> dict:
    ref_tokens = reference.split()
    cand_tokens = candidate.split()

    if len(ref_tokens) == 0 or len(cand_tokens) == 0:
        return {"precision": 0.0, "recall": 0.0, "f1": 0.0}

    lcs_length = 0
    lengths = [[0] * (len(cand_tokens) + 1) for _ in range(len(ref_tokens) + 1)]

    for i in range(1, len(ref_tokens) + 1):
        for j in range(1, len(cand_tokens) + 1):
            if ref_tokens[i-1] == cand_tokens[j-1]:
                lengths[i][j] = lengths[i-1][j-1] + 1
                lcs_length = max(lcs_length, lengths[i][j])
            else:
                lengths[i][j] = max(lengths[i-1][j], lengths[i][j-1])

    lcs_length = lengths[len(ref_tokens)][len(cand_tokens)]

    precision = lcs_length / len(cand_tokens) if len(cand_tokens) > 0 else 0
    recall = lcs_length / len(ref_tokens) if len(ref_tokens) > 0 else 0
    f1 = 2 * precision * recall / (precision + recall) if (precision + recall) > 0 else 0

    return {"precision": precision, "recall": recall, "f1": f1}


def evaluate_middle_section(generated_path: Path, ground_truth_path: Path, model_name: str) -> FIMMetrics:
    if not generated_path.exists():
        return FIMMetrics(
            model_name=model_name,
            exact_match=False,
            line_accuracy=0.0,
            similarity_ratio=0.0,
            total_lines_gt=0,
            total_lines_generated=0,
            matching_lines=0,
            edit_distance=0,
            bleu_score=0.0,
            rouge_l_f1=0.0
        )

    if not ground_truth_path.exists():
        return FIMMetrics(
            model_name=model_name,
            exact_match=False,
            line_accuracy=0.0,
            similarity_ratio=0.0,
            total_lines_gt=0,
            total_lines_generated=0,
            matching_lines=0,
            edit_distance=0,
            bleu_score=0.0,
            rouge_l_f1=0.0
        )

    generated_text = generated_path.read_text().strip()
    ground_truth_text = ground_truth_path.read_text().strip()
    generated_lines = generated_text.split('\n')
    ground_truth_lines = ground_truth_text.split('\n')

    exact_match = (generated_text == ground_truth_text)
    matcher = difflib.SequenceMatcher(None, ground_truth_lines, generated_lines)
    matching_blocks = matcher.get_matching_blocks()
    matching_lines = sum(block.size for block in matching_blocks if block.size > 0)
    line_accuracy = matching_lines / max(len(ground_truth_lines), 1)
    similarity_ratio = difflib.SequenceMatcher(None, ground_truth_text, generated_text).ratio()
    edit_distance = calculate_edit_distance(ground_truth_text, generated_text)
    bleu_score = calculate_bleu(ground_truth_text, generated_text)
    rouge_scores = calculate_rouge_l(ground_truth_text, generated_text)

    return FIMMetrics(
        model_name=model_name,
        exact_match=exact_match,
        line_accuracy=line_accuracy,
        similarity_ratio=similarity_ratio,
        total_lines_gt=len(ground_truth_lines),
        total_lines_generated=len(generated_lines),
        matching_lines=matching_lines,
        edit_distance=edit_distance,
        bleu_score=bleu_score,
        rouge_l_f1=rouge_scores["f1"]
    )


@step(enable_cache=False)
def evaluate_fim_generation(parsed: dict) -> dict:
    project_root = Path(__file__).resolve().parent.parent
    backend = os.getenv("LLM_BACKEND", "ollama")
    model = os.getenv("LLM_MODEL", "llama3.1")
    custom_output_dir = os.getenv("CUSTOM_OUTPUT_DIR")
    if custom_output_dir:
        model_output_dir = Path(custom_output_dir)
    else:
        model_output_dir = project_root / "outputs" / f"{backend}_{model}"

    generated_dir = model_output_dir / "generated"
    eval_output_dir = model_output_dir / "evaluations"
    eval_output_dir.mkdir(parents=True, exist_ok=True)
    mlflow_dir = model_output_dir / "mlruns"
    mlflow.set_tracking_uri(f"file://{mlflow_dir.resolve()}")
    mlflow.set_experiment(f"tla_fim_eval_{backend}_{model}")

    results = {}
    metrics_list: List[Dict] = []

    for model_name in parsed.keys():
        generated_middle_path = generated_dir / f"{model_name}_middle_generated.txt"
        ground_truth_middle_path = generated_dir / f"{model_name}_middle_ground_truth.txt"

        if not generated_middle_path.exists() or not ground_truth_middle_path.exists():
            continue

        metrics = evaluate_middle_section(generated_middle_path, ground_truth_middle_path, model_name)

        with mlflow.start_run(run_name=f"{model_name}_fim", nested=True):
            mlflow.log_param("model_name", model_name)
            mlflow.log_metric("exact_match", 1.0 if metrics.exact_match else 0.0)
            mlflow.log_metric("line_accuracy", metrics.line_accuracy)
            mlflow.log_metric("similarity_ratio", metrics.similarity_ratio)
            mlflow.log_metric("bleu_score", metrics.bleu_score)
            mlflow.log_metric("rouge_l_f1", metrics.rouge_l_f1)
            mlflow.log_metric("gt_lines", metrics.total_lines_gt)
            mlflow.log_metric("generated_lines", metrics.total_lines_generated)
            mlflow.log_metric("matching_lines", metrics.matching_lines)
            mlflow.log_metric("edit_distance", metrics.edit_distance)
            mlflow.log_artifact(str(generated_middle_path))
            mlflow.log_artifact(str(ground_truth_middle_path))

        results[model_name] = metrics
        metrics_list.append(metrics.to_dict())

    if metrics_list:
        fim_metrics_path = eval_output_dir / "fim_metrics.csv"
        with fim_metrics_path.open("w", newline="") as f:
            fieldnames = ["Model", "Exact_Match", "Line_Accuracy", "Similarity_Ratio",
                         "BLEU", "ROUGE_L_F1", "GT_Lines", "Generated_Lines",
                         "Matching_Lines", "Edit_Distance"]
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(metrics_list)

    return results
