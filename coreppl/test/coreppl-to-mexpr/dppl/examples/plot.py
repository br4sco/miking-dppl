import json
import numpy as np
import matplotlib.pyplot as plt

BLUE = "#3498db"
RED = "#e74c3c"
GREEN = "#27AE60"
CYAN = "cyan"

BLUE = "tab:blue"
RED = "tab:red"
GREEN = "tab:green"
CYAN = "cyan"
ORANGE = "tab:orange"
GRAY = "tab:gray"
PURPLE = "tab:purple"


def post_process_weights_samples(weights, samples):
    w = np.asarray(weights)
    s = np.asarray(samples)
    finite_mask = np.isfinite(w)
    w = w[finite_mask]
    m = max(w)
    w = np.exp(w - m)
    s = s[finite_mask]
    return w, s


def set_grid(ax):
    ax.grid(
        True,
        which="major",
        linestyle="-",
        linewidth=0.5,
        color="gray",
        alpha=0.5,
    )
    ax.grid(
        True,
        which="minor",
        linestyle="--",
        linewidth=0.5,
        color="gray",
        alpha=0.2,
    )
    ax.minorticks_on()


def plot_hist(ax, samples, weights, bins):
    ax.hist(
        samples,
        bins=bins,
        density=True,
        weights=weights,
        color=GREEN,
        edgecolor="black",
    )
    set_grid(ax)


def plot_scalar_dist(file_name):
    try:
        with open(file_name, "r") as file:
            data = json.load(file)
            weights, samples = post_process_weights_samples(
                data["weights"], data["samples"]
            )
            plt.rcParams.update({"font.size": 18})
            fig, ax = plt.subplots(figsize=(8, 6))
            ax.set_xlabel
            fig.suptitle(file_name)
            plot_hist(ax, samples, weights, 200)
            fig.tight_layout()
    except FileNotFoundError:
        print(f"{file} not found")


plot_scalar_dist("bayesian-parameter-estimation-run.json")
plot_scalar_dist("bayesian-parameter-estimation-ivp-solution-run.json")
plot_scalar_dist("bayesian-parameter-estimation-ivp-sensitivity-run.json")


def plot_trace(
    ax, xs, samples, trueTrace, prey_label, pred_label, yminofs, ymaxofs
):
    num_samples = len(samples)
    alpha = min(0.1, 5 / num_samples) if num_samples > 0 else 0.1
    plt.rcParams.update({"font.size": 22})

    def plot(ys, color, label):
        if i == 0:
            ax.plot(
                xs,
                ys,
                color=color,
                alpha=alpha,
                label=label,
            )
        else:
            ax.plot(xs, ys, color=color, alpha=alpha, label=None)

    for i in range(len(samples)):
        ys = samples[i].transpose()
        plot(ys[0], BLUE, None)
    ax.plot(
        xs,
        trueTrace.transpose()[0],
        color="black",
        linestyle="dashed",
        label=prey_label,
        linewidth=2
    )
    for i in range(len(samples)):
        ys = samples[i].transpose()
        plot(ys[1], RED, None)
    ax.plot(
        xs,
        trueTrace.transpose()[1],
        color="black",
        linestyle="dashdot",
        label=pred_label,
        linewidth=2
    )
    ax.set_ylim(
        bottom=np.min(trueTrace) - yminofs,
        top=np.max(trueTrace) + ymaxofs,
    )
    ax.set_xlabel("x")
    legend = ax.legend()
    # legend.legendPatch.set_facecolor("lightgray")
    for lh in legend.legend_handles:
        lh.set_alpha(1)
    set_grid(ax)


def plot_trace_dist(file_name, prey_label, pred_label, yminofs, ymaxofs):
    try:
        with open(file_name, "r") as file:
            data = json.load(file)
            xs = np.asarray(data["xs"])
            trueTrace = np.asarray(data["trueTrace"])
            weights, samples = post_process_weights_samples(
                data["weights"], data["trace"]
            )

            fig, ax = plt.subplots(figsize=(6, 6))
            plot_trace(
                ax,
                xs,
                samples,
                trueTrace,
                prey_label,
                pred_label,
                yminofs,
                yminofs,
            )
            fig.tight_layout()
    except FileNotFoundError:
        print(f"{file} not found")


plot_trace_dist(
    "bayesian-parameter-estimation-ivp-solution-trace-run.json",
    "prey  density",
    "pred. density",
    1,
    4,
)
plot_trace_dist(
    "bayesian-parameter-estimation-ivp-sensitivity-trace-run.json",
    "prey  density sens.",
    "pred. density sens.",
    5,
    7,
)

try:
    file1 = "bayesian-parameter-estimation-run.json"
    with open(file1, "r") as file1:
        file2 = "bayesian-parameter-estimation-ivp-solution-trace-run.json"
        with open(file2, "r") as file2:
            file3 = (
                "bayesian-parameter-estimation-ivp-sensitivity-trace-run.json"
            )
            with open(file3, "r") as file3:
                data1 = json.load(file1)
                data2 = json.load(file2)
                data3 = json.load(file3)

                weights1, samples1 = post_process_weights_samples(
                    data1["weights"], data1["samples"]
                )
                xs2 = np.asarray(data2["xs"])
                trueTrace2 = np.asarray(data2["trueTrace"])
                weights2, samples2 = post_process_weights_samples(
                    data2["weights"], data2["trace"]
                )
                xs3 = np.asarray(data2["xs"])
                trueTrace3 = np.asarray(data3["trueTrace"])
                weights3, samples3 = post_process_weights_samples(
                    data3["weights"], data3["trace"]
                )
                plt.rcParams.update({"font.size": 24})
                fig, ax = plt.subplots(
                    1,
                    3,
                    figsize=(20, 5),
                    gridspec_kw={"width_ratios": [1, 2, 2]},
                    constrained_layout=True,
                )
                ax[0].set_xlim(0, 2)
                plot_hist(ax[0], samples1, weights1, 200)
                ax[0].set_xlabel(r"$\theta$")
                current_ticks = ax[0].get_xticks()
                new_ticks = np.sort(np.unique(np.append(current_ticks, 1.5)))
                ax[0].set_xticks(new_ticks)

                plot_trace(
                    ax[1],
                    xs2,
                    samples2,
                    trueTrace2,
                    r"$y_1(x)$",
                    r"$y_2(x)$",
                    1,
                    4,
                )
                plot_trace(
                    ax[2],
                    xs3,
                    samples3,
                    trueTrace3,
                    r"$\frac{d}{d\theta}y_1(x)$",
                    r"$\frac{d}{d\theta}y_2(x)$",
                    5,
                    7,
                )

except FileNotFoundError:
    print(f"All files not found")


try:
    file = "ode-sensitivites-two-methods-run.json"
    with open(file, "r") as file:
        data = json.load(file)
        xs = np.asarray(data["xs"])
        samples = np.asarray(data["samples"])
        plt.rcParams.update({"font.size": 24})
        fig, ax = plt.subplots(1, 2, figsize=(20, 4), constrained_layout=True)

        def plot(j):
            for i in range(len(samples)):
                ys = samples[i][j].transpose()
                ax[j].plot(
                    xs, ys[0], alpha=5 * min(1, 1 / len(samples)), color=BLUE
                )
                ax[j].plot(
                    xs, ys[1], alpha=5 * min(1, 1 / len(samples)), color=RED
                )
                set_grid(ax[j])
                ax[j].set_xlabel(r"$x$")

        plot(0)
        plot(1)
        ax[0].set_ylabel(r"$s_{\theta}(x)$")
        # fig.tight_layout()
except FileNotFoundError:
    print(f"{file} not found")

try:
    file = "rode-run.json"
    with open(file, "r") as file:
        data = json.load(file)
        xs = np.asarray(data["xs"])
        ys = np.asarray(data["ys"])
        ws = np.asarray(data["ws"])
        plt.rcParams.update({"font.size": 24})
        fig, ax = plt.subplots(1, 2, figsize=(20, 4), constrained_layout=True)

        linestyle = ["-", "-.", "--", ":", (0, (5, 5))]

        for i in range(len(ys)):
            ax[0].plot(
                xs, ys[i], linewidth=2, linestyle=linestyle[i % len(linestyle)]
            )
            ax[1].plot(
                xs, ws[i], linewidth=2, linestyle=linestyle[i % len(linestyle)]
            )

        # plt.subplots_adjust(wspace=2.5)  # Increase horizontal space
        set_grid(ax[0])
        set_grid(ax[1])
        ax[0].set_xlabel(r"$x$")
        ax[0].set_ylabel(r"$y(x)$")
        ax[1].set_xlabel(r"$x$")
        ax[1].set_ylabel(r"$w(x)$")
        # fig.tight_layout()
except FileNotFoundError:
    print(f"{file} not found")

plt.show()
