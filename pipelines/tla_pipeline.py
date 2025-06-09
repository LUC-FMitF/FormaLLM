from zenml import pipeline
from steps.prompt_step import prompt_llm
from steps.evaluate_generated_step import evaluate_tla

@pipeline
def tla_pipeline():
    specs = prompt_llm()
    evaluate_tla(specs)