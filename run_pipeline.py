from pipelines.tla_pipeline import tla_pipeline

if __name__ == "__main__":
    print("Initiating a new run for the pipeline: tla_pipeline.")
    run = tla_pipeline()
    print(f"Pipeline run ID: {run.id}")