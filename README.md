# SQL Query Equivalence

A command-line tool for checking the equivalence of SQL queries.

## Installation

Run the following command from the repository root to install the dependencies:

```
pip install --upgrade -r requirements.txt 
```

## Usage

By default, command-line interaction is assumed. To check the equivalence of two queries, first place then in some files (for
instance, `q1.sql` and `q2.sql`), and also place the schema definition script in a separate file (for
instance, `schema.sql`). Finally, run the tool as follows:

```
python -m equivalence -c CONNECTION_STRING schema.sql q1.sql q2.sql
```

Here CONNECTION_STRING must be replaced by connection string for your PostgreSQL instance.


## Testing

`pytest` is used for testing, so to run all available tests, use the following command:

```
PYTHONPATH=. pytest -v tests
```