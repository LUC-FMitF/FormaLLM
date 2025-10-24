#!/usr/bin/env python3
import pandas as pd
from pathlib import Path
import matplotlib.pyplot as plt

project_root = Path(__file__).resolve().parent
outputs_dir = project_root / "outputs"
model_dirs = [d for d in outputs_dir.iterdir() if d.is_dir() and not d.name.startswith('.')]
results_data = []

for model_dir in model_dirs:
    model_name = model_dir.name
    results_csv = model_dir / "evaluations" / "evaluation_results.csv"
    if results_csv.exists():
        df = pd.read_csv(results_csv)
        df['LLM'] = model_name
        results_data.append(df)

if not results_data:
    exit(1)

combined_df = pd.concat(results_data, ignore_index=True)
summary = combined_df.groupby(['LLM', 'Result']).size().unstack(fill_value=0)
print(summary)

summary['Total'] = summary.sum(axis=1)
if 'PASS' in summary.columns:
    summary['Success_Rate'] = (summary['PASS'] / summary['Total'] * 100).round(2)
    print(f"\n{'Model':<30} {'Success Rate'}")
    print("-" * 45)
    for model, rate in summary['Success_Rate'].items():
        print(f"{model:<30} {rate:>6.2f}%")

output_path = outputs_dir / "model_comparison.csv"
summary.to_csv(output_path)

fig, axes = plt.subplots(1, 2, figsize=(14, 6))
summary_plot = summary.drop(['Total', 'Success_Rate'] if 'Success_Rate' in summary.columns else ['Total'],
                             axis=1, errors='ignore')
summary_plot.plot(kind='bar', stacked=True, ax=axes[0])
axes[0].set_title('TLA+ Validation Results by Model')
axes[0].set_xlabel('LLM Backend + Model')
axes[0].set_ylabel('Number of Specifications')
axes[0].legend(title='Result', bbox_to_anchor=(1.05, 1), loc='upper left')
axes[0].tick_params(axis='x', rotation=45)

if 'Success_Rate' in summary.columns:
    summary['Success_Rate'].plot(kind='bar', ax=axes[1], color='green', alpha=0.7)
    axes[1].set_title('Success Rate by Model')
    axes[1].set_xlabel('LLM Backend + Model')
    axes[1].set_ylabel('Success Rate (%)')
    axes[1].tick_params(axis='x', rotation=45)
    axes[1].set_ylim(0, 100)
    for i, v in enumerate(summary['Success_Rate']):
        axes[1].text(i, v + 2, f'{v:.1f}%', ha='center', va='bottom')

plt.tight_layout()
plot_path = outputs_dir / "model_comparison.png"
plt.savefig(plot_path, dpi=300, bbox_inches='tight')
