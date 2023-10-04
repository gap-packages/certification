FROM gapsystem/gap-docker

RUN sudo pip3 install ipywidgets RISE

RUN jupyter-nbextension install rise --user --py

RUN jupyter-nbextension enable rise --user --py

# Update version number each time after gap-docker container is updated
ENV GAP_VERSION 4.11.1

USER gap

# install newer Digraphs
WORKDIR /home/gap/inst/gap-${GAP_VERSION}/pkg

RUN rm -rf digraphs* \
    && wget https://github.com/digraphs/Digraphs/releases/download/v1.6.3/digraphs-1.6.3.tar.gz \
    && gzip -dc digraphs-1.6.3.tar.gz | tar xpv \
    && cd digraphs* \
    && ./configure \
    && make

# install this package
RUN mkdir /home/gap/inst/gap-${GAP_VERSION}/pkg/certification

COPY . /home/gap/inst/gap-${GAP_VERSION}/pkg/certification/

WORKDIR /home/gap/inst/gap-${GAP_VERSION}/pkg/certification
