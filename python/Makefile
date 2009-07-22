all:
	python setup.py build_ext -i -f
	python setup.py build
	python setup.py sdist

.PHONY: test
test:
	nosetests test
