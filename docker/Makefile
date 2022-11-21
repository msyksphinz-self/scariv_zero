build-env:
	docker build . -f Dockerfile.migrate --platform=linux/amd64 -t msyksphinz/scariv:run_env
	docker push msyksphinz/scariv:run_env

run:
	docker-compose -f top-test.yml build
	docker-compose -f top-test.yml up --abort-on-container-exit

debug:
	cd ../; \
	docker build . -f docker/Dockerfile.test --platform=linux/amd64 -t msyksphinz/scariv:run; \
	docker run -it msyksphinz/scariv:run /bin/bash
