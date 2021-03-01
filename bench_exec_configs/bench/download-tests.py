import requests
import os
import tarfile
import glob

TESTS_FOLDER = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tests/')

TESTS_ARCHIVES = [
  'https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uf100-430.tar.gz',
  'https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uuf100-430.tar.gz',
  'https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uf150-645.tar.gz',
  'https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uuf150-645.tar.gz',
  'https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uf175-753.tar.gz',
  'https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uuf175-753.tar.gz',
  'https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uf200-860.tar.gz',
  'https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uuf200-860.tar.gz'
]


def download_test_archive(url):
    print (url)
    archive_name = os.path.basename(url)
    dir_name = archive_name.split('.')[0]
    dir_path = os.path.join(TESTS_FOLDER, dir_name)

    if not os.path.isdir(dir_path):
        os.mkdir(dir_path)
        archive_path = os.path.join(TESTS_FOLDER, archive_name)
        archive_data = requests.get(url).content

        with open(archive_path, 'wb') as archive:
            archive.write(archive_data)
            archive.close()

        tar = tarfile.open(archive_path, "r:gz")
        tar.extractall(path=dir_path)
        tar.close()

        os.remove(archive_path)


def download_test_archives():
    if not os.path.isdir(TESTS_FOLDER):
        os.mkdir(TESTS_FOLDER)

    for test_archive in TESTS_ARCHIVES:
        download_test_archive(test_archive)


def index_tests():
    return sorted(glob.glob(os.path.join(TESTS_FOLDER, "**/*.cnf"), recursive=True))

def main():
    download_test_archives()


main()
