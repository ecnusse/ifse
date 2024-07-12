# IFSE

IFSE is an open-source symbolic execution tool that integrates various methods for combining symbolic execution with fuzzing into KLEE.

## Setup

To set up the environment, create the Docker image using the current directory:

```sh
docker build -t ifse-image:stable .
```

## Run

This command builds a Docker image named `ifse-image`, which contains the complete runtime environment and evaluation tools. To run the image, use the following command:

```sh
docker run -it ifse-image:stable
```

We will package the entire environment, including the source code and experiments, into a single image for release. This will be available soon.

