all:
	python setup_dev.py build_ext -i -f
	python setup.py build sdist

.PHONY: test
test:
	nosetests test
