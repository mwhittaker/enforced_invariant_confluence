#! /usr/bin/env bash

set -euo pipefail

usage() {
    echo "./launch_ec2_instances"
}

main() {
    if [[ "$#" -ne 0 ]]; then
        usage
        exit 1
    fi

    local -r image_id=ami-ee6f5e8b
    local -r instance_type=m5.xlarge
    local -r key_name=aws-ec2
    local -r security_group_ids=sg-24a1f44c

    # Launch the master.
    aws ec2 run-instances \
        --image-id "$image_id" \
        --instance-type "$instance_type" \
        --key-name "$key_name" \
        --security-group-ids "$security_group_ids" \
        --count 1 \
        --tag-specifications 'ResourceType=instance,Tags=[{Key=Name,Value=master}]'
        # --dry-run

    # Launch everything else.
    aws ec2 run-instances \
        --image-id "$image_id" \
        --instance-type "$instance_type" \
        --key-name "$key_name" \
        --security-group-ids "$security_group_ids" \
        --count 32
        # --dry-run
}

main
