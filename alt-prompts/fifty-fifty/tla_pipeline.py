from zenml import pipeline
from steps.prompt_step import prompt_llm
from steps.parse_step import sanity_check_sany
from steps.evaluate_generated_step import evaluate_tla
from steps.fim_evaluation_step import evaluate_fim_generation
from steps.graph_results import graph_results

@pipeline
def tla_pipeline():
    specs = prompt_llm()
    parsed = sanity_check_sany(specs)
    evaluate_tla(parsed)
    evaluate_fim_generation(parsed)
    graph_results()