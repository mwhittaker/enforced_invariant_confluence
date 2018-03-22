from argparse import ArgumentParser

from iconfluence import *

def _get_parser() -> ArgumentParser:
    checkers = [
        'interactive',
        'guess_and_check',
        'diamond',
    ]

    parser = ArgumentParser()
    parser.add_argument('--verbose', '-v', action='store_true')
    parser.add_argument('--checker', '-c',
                        choices=checkers, default='interactive')
    return parser

def get_checker() -> Checker:
    parser = _get_parser()
    args = parser.parse_args()
    if args.checker == 'interactive':
        return InteractiveChecker(verbose=args.verbose)
    elif args.checker == 'guess_and_check':
        return GuessAndCheckChecker(verbose=args.verbose)
    elif args.checker == 'diamond':
        return DiamondChecker(verbose=args.verbose)
    else:
        raise ValueError(f'Unrecognized checker {args.checker}.')
