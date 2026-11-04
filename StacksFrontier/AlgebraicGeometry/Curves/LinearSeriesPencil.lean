module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesMorphism

/-!
# The pencil cut out of a linear series by two basis vectors

A linear series `(ℒ, V)` of degree `d` and dimension `r` on a proper scheme of dimension at most
one over a field, [Stacks, Tag 0CCN], together with a basis `b` of `V` indexed by `Fin (r + 1)`,
determines for every pair of distinct indices `i₀ ≠ i₁` a `𝔤¹_d` on the same scheme: the same
invertible sheaf `ℒ`, with the plane spanned by `b i₀` and `b i₁` as its space of sections.

This is [Stacks, Tag 0CCQ] at dimension one, sharpened in two directions. The sheaf of the
smaller series is `ℒ` itself, so that every statement about one of them is a statement about the
other with no transport; and the plane comes with a basis whose two global sections are exactly
those underlying `b i₀` and `b i₁`, so a consumer knows which two sections of `ℒ` the pencil is
made of.

## Main definitions

* `AlgebraicGeometry.LinearSeries.pencilFamily`: the pair `b i₀`, `b i₁` as a family indexed by
  `Fin 2`, inside the ambient space of degree-zero cohomology.
* `AlgebraicGeometry.LinearSeries.pencil`: the `𝔤¹_d` spanned by two members of a basis.

## Main results

* `AlgebraicGeometry.LinearSeries.linearIndependent_pencilFamily`: two distinct members of a
  basis are linearly independent in the ambient space of sections.
* `AlgebraicGeometry.LinearSeries.pencil_L`: the pencil has the same invertible sheaf as the
  series it comes from.
* `AlgebraicGeometry.LinearSeries.exists_basis_seriesSections_pencil`: the chosen space of
  sections of the pencil has a basis indexed by `Fin 2` whose underlying global sections are
  those underlying `b i₀` and `b i₁`.

## Implementation notes

The space of sections of the pencil is spelled as the span, inside the ambient
`AlgebraicGeometry.cohomologyOverField k f ℒ 0`, of the two-element family
`AlgebraicGeometry.LinearSeries.pencilFamily` rather than as the image under `V.subtype` of a
span inside `V`, which is the spelling of `AlgebraicGeometry.linearSeries_nonempty_of_le`. The
two submodules are equal, and this one is the span of a family in the ambient module on the nose,
so `Module.Basis.span` already produces a basis of it and the pinning of the two sections needs
no transport along that equality.

Keeping `ℒ`, its invertibility and its degree is what makes `pencil_L` hold by `rfl`, and that in
turn is what lets `exists_basis_seriesSections_pencil` compare a family of sections of the
pencil's sheaf with a family of sections of `ℒ` directly.

`Stacks.LinearSeriesMorphism.seriesSections` reads a family in the chosen space of sections as a
family of global sections through `AlgebraicGeometry.cohomologyOverFieldZeroEquivSections`, a
bare `Equiv`; the pinning is therefore an equality of families in `Γ(ℒ, ⊤)` and the linear
algebra all happens on the cohomology side of that bijection.

## References

* [Stacks Project, Tag 0CCN](https://stacks.math.columbia.edu/tag/0CCN)
* [Stacks Project, Tag 0CCQ](https://stacks.math.columbia.edu/tag/0CCQ)
* [Stacks Project, Tag 0CCP](https://stacks.math.columbia.edu/tag/0CCP)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LinearSeries

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} [IsProper f]
  {hdim : topologicalKrullDim X ≤ 1} {d r : ℕ}

/-- The two members `b i₀` and `b i₁` of a basis of the chosen space of sections of a linear
series, as a family indexed by `Fin 2` inside the ambient space of degree-zero cohomology. -/
def pencilFamily (E : LinearSeries k f hdim d r) (b : Module.Basis (Fin (r + 1)) k E.V)
    (i₀ i₁ : Fin (r + 1)) : Fin 2 → cohomologyOverField k f E.L 0 :=
  fun t => (b (if t = 0 then i₀ else i₁) : cohomologyOverField k f E.L 0)

/-- **Two distinct members of a basis are linearly independent in the ambient space of
sections.** The index map `Fin 2 → Fin (r + 1)` is injective because the two indices differ, so
the family is a basis reindexed along an injection and then pushed along the injective inclusion
of the chosen space of sections. -/
theorem linearIndependent_pencilFamily (E : LinearSeries k f hdim d r)
    (b : Module.Basis (Fin (r + 1)) k E.V) {i₀ i₁ : Fin (r + 1)} (hne : i₀ ≠ i₁) :
    LinearIndependent k (pencilFamily E b i₀ i₁) := by
  have hinj : Function.Injective (fun t : Fin 2 => if t = 0 then i₀ else i₁) := by
    intro s t hst
    fin_cases s <;> fin_cases t <;> simp_all
  exact (b.linearIndependent.comp _ hinj).map' E.V.subtype (Submodule.ker_subtype _)

/-- **The pencil spanned by two members of a basis of a linear series**: the `𝔤¹_d` with the same
invertible sheaf of the same degree, whose space of sections is the plane spanned by `b i₀` and
`b i₁`. That plane has dimension two because those two vectors are linearly independent. -/
def pencil (E : LinearSeries k f hdim d r) (b : Module.Basis (Fin (r + 1)) k E.V)
    {i₀ i₁ : Fin (r + 1)} (hne : i₀ ≠ i₁) : LinearSeries k f hdim d 1 where
  L := E.L
  isInvertible := E.isInvertible
  degree_eq := E.degree_eq
  V := Submodule.span k (Set.range (pencilFamily E b i₀ i₁))
  finrank_eq := by
    rw [finrank_span_eq_card (linearIndependent_pencilFamily E b hne), Fintype.card_fin]

/-- **The pencil has the same invertible sheaf as the series it comes from.** -/
theorem pencil_L (E : LinearSeries k f hdim d r) (b : Module.Basis (Fin (r + 1)) k E.V)
    {i₀ i₁ : Fin (r + 1)} (hne : i₀ ≠ i₁) : (E.pencil b hne).L = E.L :=
  rfl

/-- **The two sections of the pencil are the two chosen sections of the series.** The space of
sections of the pencil is by construction the span of the linearly independent pair `b i₀`,
`b i₁`, so `Module.Basis.span` is a basis of it sending `0` to `b i₀` and `1` to `b i₁`; applying
the bijection with global sections to these two vectors gives the two global sections underlying
`b i₀` and `b i₁`. -/
theorem exists_basis_seriesSections_pencil (E : LinearSeries k f hdim d r)
    (b : Module.Basis (Fin (r + 1)) k E.V) {i₀ i₁ : Fin (r + 1)} (hne : i₀ ≠ i₁) :
    ∃ b₁ : Module.Basis (Fin 2) k (E.pencil b hne).V,
      ∀ t : Fin 2, Stacks.LinearSeriesMorphism.seriesSections (E.pencil b hne) b₁ t =
        Stacks.LinearSeriesMorphism.seriesSections E b (if t = 0 then i₀ else i₁) := by
  refine ⟨(Module.Basis.span (linearIndependent_pencilFamily E b hne) :
    Module.Basis (Fin 2) k (Submodule.span k (Set.range (pencilFamily E b i₀ i₁)))),
    fun t => ?_⟩
  exact congrArg (fun x : cohomologyOverField k f E.L 0 =>
      cohomologyOverFieldZeroEquivSections k f E.L x)
    (Module.Basis.coe_span_apply (linearIndependent_pencilFamily E b hne) t)

end AlgebraicGeometry.LinearSeries

end
