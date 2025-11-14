import matplotlib.pyplot as plt
import os
import sys
import math

def parse_data_file(filepath):
    """
    Parses the data file according to the specified format.

    Args:
        filepath (str): The path to the data file.

    Returns:
        tuple: A tuple containing:
            - sizes (list): The list of sizes (for x-axis).
            - upper_bounds (list): The list of upper bounds.
            - lower_bounds (list): The list of lower bounds.
            - times (list): The list of time values.
            - memory (list): The list of memory consumption values.
            - is_exact (bool): True if the file ends with "Exact. Done.".
    """
    sizes = []
    upper_bounds = []
    lower_bounds = []
    times = []
    memory = []
    is_exact = False

    try:
        with open(filepath, 'r') as f:
            lines = [line.strip() for line in f if line.strip()] # Read all non-empty lines

        # Check for the "Exact. Done." condition at the end of the file
        if lines and lines[-1] == "Exact. Done.":
            is_exact = True
            lines.pop() # Remove the "Exact. Done." line so we don't try to parse it

        # Process the file in chunks of two lines
        i = 0
        while i < len(lines):
            # Line 1: Size, Upper, Lower
            line1_parts = lines[i].split()
            # Line 2: Time, Memory
            line2_parts = lines[i+1].split()

            if len(line1_parts) >= 3 and len(line2_parts) >= 1:
                try:
                    sizes.append(int(line1_parts[0]))
                    upper_bounds.append(math.log2(max(1, int(line1_parts[1]))))
                    lower_bounds.append(math.log2(max(1, int(line1_parts[2]))))
                    times.append(float(line2_parts[0]))
                    memory.append(int(line2_parts[1]) / 1000)
                except (ValueError, IndexError) as e:
                    print(f"Warning: Skipping malformed data block at lines {i+1}-{i+2}. Error: {e}")
            
            i += 2 # Move to the next data block

    except FileNotFoundError:
        print(f"Error: The file '{filepath}' was not found.")
        return None, None, None, None, None

    return sizes, upper_bounds, lower_bounds, times, memory, is_exact

def plot_data(sizes, upper_bounds, lower_bounds, times, memory, is_exact, filename):
    """
    Renders the parsed data into a graph using matplotlib.

    Args:
        sizes (list): The list of sizes (for x-axis).
        upper_bounds (list): The list of upper bounds.
        lower_bounds (list): The list of lower bounds.
        times (list): The list of time values.
        is_exact (bool): True if the "Exact. Done." line should be drawn.
    """
    if not sizes:
        print("No data to plot.")
        return

    fig, ax1 = plt.subplots(figsize=(12, 7))

    # --- Configure the primary Y-axis (left) for Bounds ---
    ax1.set_xlabel('Size (log2 scale)')
    ax1.set_ylabel('Approximation bounds (#solutions) (log2(log2) scale)', color='tab:blue')
    ax1.set_xscale('log', base=2)
    ax1.set_yscale('log', base=2)
    
    # Plot bounds data
    ax1.plot(sizes, upper_bounds, 'o-', color='tab:blue', label='Upper Bound (log2(log2))')
    # Filter out zero lower bounds before plotting on a log scale
    plot_lower_sizes = [s for s, l in zip(sizes, lower_bounds) if l > 0]
    plot_lower_bounds = [l for l in lower_bounds if l > 0]
    if plot_lower_bounds:
        ax1.plot(plot_lower_sizes, plot_lower_bounds, 'x--', color='tab:cyan', label='Lower Bound (log2(log2))')
    
    ax1.tick_params(axis='y', labelcolor='tab:blue')
    ax1.grid(True, which='both', linestyle='--', linewidth=0.5, axis='y')

    # --- Configure the secondary Y-axis (right) for Time ---
    ax2 = ax1.twinx()  # Create a second y-axis that shares the same x-axis
    ax2.set_ylabel('Time (s) / Memory (MiB) (log2)', color='tab:red')
    ax2.set_yscale('log', base=2)
    
    # Plot time data    
    ax2.plot(sizes, times, 's-.', color='tab:red', label='Time (log2, s)')
    ax2.plot(sizes, memory, 's-.', color='tab:green', label='Memory (log2, MiB)')
    
    ax2.tick_params(axis='y', labelcolor='tab:red')
    # The scale is linear by default, so no ax2.set_yscale() is needed.

    # --- Add "Exact. Done." horizontal line if applicable ---
    if is_exact and upper_bounds:
        exact_value = upper_bounds[-1]
        ax1.axhline(y=exact_value, color='tab:cyan', linestyle=':', linewidth=2, 
                    label=f'Solutions (final result)')
        exact_value = times[-1]
        ax2.axhline(y=exact_value, color='tab:red', linestyle=':', linewidth=2, 
                    label=f'Runtime (final result)')
        exact_value = memory[-1]
        ax2.axhline(y=exact_value, color='tab:green', linestyle=':', linewidth=2, 
                    label=f'Memory (final result)')

    # --- Final Touches (Title and Legend) ---
    plt.title(f"Approximation bounds and resources vs. target BDD size ({filename.replace('.png', '')})")

    # Create a unified legend for both axes
    lines1, labels1 = ax1.get_legend_handles_labels()
    lines2, labels2 = ax2.get_legend_handles_labels()
    ax2.legend(lines1 + lines2, labels1 + labels2, loc='upper left', facecolor='white', framealpha=1.0)

    fig.tight_layout()  # Adjust plot to prevent labels from overlapping
    plt.savefig(filename, dpi=300) # Save the plot to a file
    plt.show()


if __name__ == '__main__':
#     # --- Create a sample data file for demonstration ---
#     data_content = """
# 128	15644436298248853142541662886984024276875277263354390404885558651041648382182425903488491847680	0	83	1
# 	0.46	8324
# 256	15905176903219667361584023935100424681489865217743630244966984628559009188552133001879966711808	0	103	1
# 	0.91	8368
# 512	260358660725251502901185714549823646209390804065427477034431701183106859876001472759065477120	0	234	1
# 	1.88	8664
# 1024	1175672130872735622055323634619084465997478340484930004029256841375429050937628899760144384	0	348	1
# 	2.40	8888
# 2048	11420950417395061207935516550215467652150709806787528245439405156855018292721420760776704	0	1722	1
# 	2.80	9156
# 4096	35688952344287514923961833389808630538825153765868016282997163136726823645781623308288	0	1871	1
# 	3.65	9908
# 8192	627426383057752043874344796528675949977414608109853334681643286401917767741771612160	65536	7948	2170
# 	5.02	11432
# 16384	186218922169058177171704482368702049791970148199007136618408396838038037523278594048	0	12238	1
# 	5.85	15116
# 32768	3276604876280178424553760316938164439151230976318846720480511565438128298317716652032	131072	20472	3587
# 	8.14	21336
# 65536	3218753640260021652418372221978411806208718789133158836958036097204830076928	268288	30642	21472
# 	10.73	35036
# 131072	245209557800241894342349152997392083415590781506377100023411137200781262848	283936	25186	104762
# 	13.32	72336
# 262144	1613674127788967969589896854526016484155214460838954695570216039661699072	282880	20848	76474
# 	17.73	112404
# 524288	11002102187274709295282486210475312403493578072308113995995283456	303712	81136	166476
# 	21.38	191996
# 1048576	5732269147262534003580209871317780377108480	360304	795202	606970
# 	25.43	318200
# 2097152	10739829898943174024094535095300114087936	450328	302158	1594525
# 	32.60	550172
# 4194304	471040	471040	2337753	2337753
# 	25.34	322588
# Exact. Done.
# """
#     filename = "data.txt"
#     with open(filename, 'w') as f:
#         f.write(data_content.strip())

#     print(f"Sample data file '{filename}' created.")

    # --- Process the file and generate the plot ---
    sizes, u_bounds, l_bounds, times, memory, is_exact = parse_data_file(sys.argv[1])
    
    if sizes:
        print("Data parsed successfully. Generating plot...")
        plot_filename = sys.argv[1].replace('.out.txt', '.png')
        plot_data(sizes, u_bounds, l_bounds, times, memory, is_exact, plot_filename)
        print(f"Plot saved as '{plot_filename}' and displayed.")