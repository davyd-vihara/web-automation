import unittest
import requests


class TestGithubApi(unittest.TestCase):
    BASE_URL = 'https://api.github.com'
    TOKEN = 'Добавь свой токен'
    TEST_REPO_NAME = 'Hello-World'
    USERNAME = 'davyd-vihara'

    def setup(self):
        # хэдеры для методов POST, PATCH, DELETE
        self.headers = {
            'Authorization': f'Bearer {self.TOKEN}',
            'Accept': 'application/vnd.github+json'
        }
        # флаг — запускать teardown или нет
        self.run_teardown = True

    def teardown(self):
        if self.run_teardown:
            # удаление репозитория
            url = (f'{self.BASE_URL}/repos/{self.USERNAME}/'
                   f'{self.TEST_REPO_NAME}')
            response = requests.delete(url, headers=self.headers)
            assert response.status_code == 204

    def test_get_user(self):
        self.setup()
        # в этом тесте ничего не создаётся, поэтому teardown не нужен
        self.run_teardown = False

        url = f'{self.BASE_URL}/users/{self.USERNAME}'
        response = requests.get(url)

        assert response.status_code == 200

        data = response.json()
        assert data['login'] == self.USERNAME

    def test_create_repo(self):
        self.setup()

        url = f'{self.BASE_URL}/user/repos'
        body = {
            "name": self.TEST_REPO_NAME,
            "description": "Тестовое описание",
            "private": False,
            "is_template": True
        }
        response = requests.post(url, headers=self.headers, json=body)

        assert response.status_code == 201

        data = response.json()
        assert data['name'] == self.TEST_REPO_NAME

        self.teardown()

    def test_update_repo(self):
        self.setup()

        # создание репозитория (без ассёртов)
        url_create = f'{self.BASE_URL}/user/repos'
        body_create = {
            "name": self.TEST_REPO_NAME,
            "description": "Тестовое описание",
            "private": False,
            "is_template": True
        }
        requests.post(url_create, headers=self.headers, json=body_create)

        # обновление репозитория
        new_description = "Новое описание"
        url_update = (f'{self.BASE_URL}/repos/{self.USERNAME}/'
                      f'{self.TEST_REPO_NAME}')
        body_update = {
            "description": new_description
        }
        response = requests.patch(
            url_update, headers=self.headers, json=body_update
        )

        assert response.status_code == 200

        data = response.json()
        assert data['description'] == new_description

        self.teardown()
