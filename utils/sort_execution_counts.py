import json
from pathlib import Path
from typing import Annotated

import typer


def main(
    notebook_filepaths: Annotated[
        list[Path], typer.Argument(exists=True, dir_okay=False)
    ],
) -> None:
    """
    Sorts execution counts in Jupyter Notebooks.

    Parameters
    ----------
    notebook_filepaths:
        The notebook filepaths
    """
    for notebook_filepath in notebook_filepaths:
        text = notebook_filepath.read_text(encoding='utf-8')
        doc = json.loads(text)

        count = 1
        for cell in doc['cells']:
            if 'execution_count' not in cell:
                continue
            cell['execution_count'] = count
            for o in cell.get('outputs', []):
                if 'execution_count' in o:
                    o['execution_count'] = count
            count = count + 1

        # Same format as Jupyter and VS Code
        sorted_text = json.dumps(doc, indent=1, ensure_ascii=False) + '\n'
        if sorted_text != text:
            notebook_filepath.write_text(sorted_text, encoding='utf-8')
            typer.echo(f'Sorted execution counts in {notebook_filepath}')


if __name__ == '__main__':
    typer.run(main)
