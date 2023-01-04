FROM bitnami/nginx:latest

COPY /docker/nginx.conf /opt/bitnami/nginx/conf/nginx.conf

COPY /docker/index.html /app/index.html

COPY /webapp /app
