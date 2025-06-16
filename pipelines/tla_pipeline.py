from zenml import pipeline
from steps.prompt_step import prompt_llm
from steps.evaluate_generated_step import evaluate_tla
from steps.graph_results import graph_results

@pipeline
def tla_pipeline():
    specs = prompt_llm()
    evaluate_tla(specs)
    graph_results()