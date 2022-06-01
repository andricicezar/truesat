import requests
import os
import tarfile
import glob
import shutil
import itertools

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

def cut_the_last_2_lines(file_name):
    with open(file_name, "r+", encoding = "utf-8") as file:

        # Move the pointer (similar to a cursor in a text editor) to the end of the file
        file.seek(0, os.SEEK_END)

        # This code means the following code skips the very last character in the file -
        # i.e. in the case the last line is null we delete the last line
        # and the penultimate one
        pos = file.tell() - 1

        # Read each character in the file one at a time from the penultimate
        # character going backwards, searching for a newline character
        # If we find a new line, exit the search
        counter = 0

        while pos > 0 and counter < 2:
            counter += file.read(1) == "\n"
            pos -= 1
            file.seek(pos, os.SEEK_SET)

        # So long as we're not at the start of the file, delete all the characters ahead
        # of this position
        if pos > 0:
            file.seek(pos, os.SEEK_SET)
            file.truncate()

# Function from: https://stackoverflow.com/questions/17547273/flatten-complex-directory-structure-in-python
def flatten(destination):
    all_files = []
    for root, _dirs, files in itertools.islice(os.walk(destination), 1, None):
        for filename in files:
            all_files.append(os.path.join(root, filename))

    for filename in all_files:
        shutil.move(filename, destination)

def modify_files(destination):
    for root, _dirs, files in os.walk(destination):
        for filename in files:
            cut_the_last_2_lines(os.path.join(root, filename))
            cmd = "sed -i 's/ \\{{1,\\}}/ /g' {0}".format(os.path.join(root, filename))
            print("Doing {0}.".format(cmd))
            os.system(cmd)

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
        flatten(dir_path)
        modify_files(dir_path)

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
