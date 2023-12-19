install-ubuntu-dependencies:
	apt-get update
	apt-get install build-essential libgtk-3-dev

install-python-dependencies-for-application_running:
	pip install -r requirements/application_running_requirements.txt

install-python-dependencies-for-usage:
	pip install -r requirements/usage_requirements.txt

install-python-dependencies-for-development:
	$(MAKE) install-python-dependencies-for-usage
	pip install -r requirements/development_only_requirements.txt

lint:
	black .

lint-without-correcting:
	black . --check

test:
	python -m unittest discover -s . -t .

run-example-usage:
	python -m usage.example1.usage
