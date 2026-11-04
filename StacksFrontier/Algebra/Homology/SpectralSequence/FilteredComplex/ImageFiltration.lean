module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Subobject.Limits
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Defs
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# The filtration of a complex by the images of a system of complexes

Let `𝒜` be an abelian category, `X^•` a `ℤ`-indexed cochain complex of `𝒜`, and suppose given a
family of complexes `S_k^•` indexed by `k : ℕ` together with morphisms `φ_k : S_k^• ⟶ X^•` which
factor through one another: for `k ≤ k'` a morphism `S_{k'}^• ⟶ S_k^•` whose composite with `φ_k`
is `φ_{k'}`.  The images `Im φ_k` are then a decreasing family of subcomplexes of `X^•`, so
setting

`F^k X^• = Im φ_k` for `k ≥ 1` and `F^k X^• = X^•` for `k ≤ 0`

makes `X^•` a filtered complex in the sense of [Stacks, Tag 012L], exhaustive in the strong sense
that its steps in non-positive degrees are the whole complex.  This module performs that
construction once, in an arbitrary abelian category.

It is the shape every *wedge* filtration of a de Rham complex has: the system is the family of
total complexes `Tot(σ^{≥k}P^• ⊗ Ω^•)`, the morphisms are the wedge maps, and the factorisations
are the inclusions `σ^{≥k'}P^• ⟶ σ^{≥k}P^•` between brutal truncations wedged against `Ω^•`.
That system is assembled, for an arbitrary bifunctor on an arbitrary abelian category, in
`StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.WedgeImageSystem`;
`StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltration` is its instance for sheaves of modules on
a ringed site (Stacks Section 50.12, [Stacks, Tag 0FMK]), and the completed de Rham complexes of
the crystalline chapter, whose terms are objects of `AddCommGrpCat` with the module structure
forgotten, are another.  The point of stating both abstractly is that they share them rather than
each carrying a copy.

## Degreewise finiteness

[Stacks, Tag 05S3] concludes from the graded pieces of a filtered complex to its underlying
morphism only for filtrations that are finite in each degree
(`CategoryTheory.Filtration.IsDegreewiseFinite`), and the counterexample in the docstring of
`CochainComplex.quasiIso_hom_of_filteredQuasiIso` shows the hypothesis cannot be dropped.  For a
filtration by images half of it is free: the step at `0` is the whole complex by definition.  The
other half is exactly the vanishing of the system degree by degree, and
`CochainComplex.ImageSystem.isDegreewiseFinite_filtered` records that implication — the image of a
morphism whose source vanishes in degree `n` vanishes in degree `n`, because
`Limits.factorThruImageSubobject` is an epimorphism and evaluation in degree `n` preserves
epimorphisms.

## Main definitions

* `CochainComplex.ImageSystem` — **the datum**: the family `S_k^•`, the morphisms `φ_k` into
  `X^•`, and the factorisations between them.
* `CochainComplex.ImageSystem.filtrationStep` — the `k`-th step `F^k X^•`.
* `CochainComplex.ImageSystem.filtered` — **the filtered complex.**

## Main results

* `CochainComplex.ImageSystem.filtrationStep_antitone` — the steps decrease.
* `CochainComplex.ImageSystem.isIso_filtered_ι_of_nonpos` — the filtration is exhaustive: its
  steps in degrees `≤ 0` are the whole complex.
* `CochainComplex.ImageSystem.isDegreewiseFinite_filtered` — it is degreewise finite as soon as
  the system vanishes degree by degree.

## References

* [Stacks Project, Tag 012L](https://stacks.math.columbia.edu/tag/012L)
* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 05S3](https://stacks.math.columbia.edu/tag/05S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **A system of complexes mapping into `X^•`**, each factoring through its predecessors.  This
is the datum a decreasing filtration of `X^•` by images is built from: `source k` is the `k`-th
member, `hom k` its morphism into `X^•`, and `step` the factorisations, which are what make the
images decrease. -/
public structure ImageSystem (X : CochainComplex C ℤ) where
  /-- The `k`-th member of the system. -/
  source : ℕ → CochainComplex C ℤ
  /-- The morphism of the `k`-th member into the ambient complex. -/
  hom : ∀ k : ℕ, source k ⟶ X
  /-- The factorisation of the later members through the earlier ones. -/
  step : ∀ {k k' : ℕ}, k ≤ k' → (source k' ⟶ source k)
  /-- The factorisations are compatible with the morphisms into the ambient complex. -/
  step_hom : ∀ {k k' : ℕ} (h : k ≤ k'), step h ≫ hom k = hom k'

namespace ImageSystem

variable {X : CochainComplex C ℤ} (S : ImageSystem X)

/-- **The `k`-th step of the filtration by the images of a system**: the image of the `k`-th
morphism for `k ≥ 1`, and the whole complex for `k ≤ 0`.

The step at `k ≤ 0` is `⊤` by definition rather than by a computation.  This is what makes the
exhaustion clause hold with no hypothesis on the system at all; a system whose zeroth morphism
happens to be epimorphic has `Im φ_0 = X^•` anyway, so nothing is lost where the two agree. -/
public def filtrationStep (k : ℤ) : Subobject X :=
  if k ≤ 0 then ⊤ else imageSubobject (S.hom k.toNat)

/-- In non-positive degrees the step is the whole complex. -/
public theorem filtrationStep_of_nonpos {k : ℤ} (hk : k ≤ 0) : S.filtrationStep k = ⊤ := by
  simp only [filtrationStep, if_pos hk]

/-- In positive degrees the step is the image of the corresponding morphism. -/
public theorem filtrationStep_of_pos {k : ℤ} (hk : 0 < k) :
    S.filtrationStep k = imageSubobject (S.hom k.toNat) := by
  simp only [filtrationStep, if_neg (not_le.2 hk)]

/-- **The filtration by images is decreasing.**  This is the content of the factorisations:
`φ_{k'}` factors through `φ_k` for `k ≤ k'`, so its image is smaller. -/
public theorem filtrationStep_antitone : Antitone S.filtrationStep := by
  intro k k' h
  by_cases hk : k ≤ 0
  · exact le_top.trans (S.filtrationStep_of_nonpos hk).ge
  · have hnat : k.toNat ≤ k'.toNat := by omega
    rw [S.filtrationStep_of_pos (not_le.1 hk), S.filtrationStep_of_pos ((not_le.1 hk).trans_le h),
      ← S.step_hom hnat]
    exact imageSubobject_comp_le _ _

/-- **The filtration of `X^•` by the images of a system**, as a filtered complex in the sense of
[Stacks, Tag 012L]. -/
@[stacks 012L "a complex filtered by the images of a system of complexes mapping into it"]
public def filtered : CochainComplex.Filtered C where
  X := X
  filtration := Filtration.ofAntitone S.filtrationStep S.filtrationStep_antitone

/-- The underlying complex of the filtered complex is `X^•`. -/
@[simp] public theorem filtered_X : S.filtered.X = X := rfl

/-- The `k`-th step of the filtered complex is
`CochainComplex.ImageSystem.filtrationStep` at `k`. -/
@[simp] public theorem filtered_subobject (k : ℤ) :
    S.filtered.filtration.subobject (op k) = S.filtrationStep k :=
  Filtration.subobject_ofAntitone S.filtrationStep S.filtrationStep_antitone k

/-- The inclusion of the `k`-th step is the arrow of the `k`-th image subobject. -/
public theorem filtered_ι_app (k : ℤ) :
    S.filtered.filtration.ι.app (op k) = (S.filtrationStep k).arrow := rfl

/-- **The filtration by images is exhaustive**: in degrees `≤ 0` its steps are the whole
complex. -/
public theorem isIso_filtered_ι_of_nonpos {k : ℤ} (hk : k ≤ 0) :
    IsIso (S.filtered.filtration.ι.app (op k)) :=
  (Subobject.isIso_arrow_iff_eq_top (S.filtrationStep k)).2 (S.filtrationStep_of_nonpos hk)

/-- The step at `k ≥ 1` vanishes in a degree in which the `k`-th member of the system vanishes:
`Limits.factorThruImageSubobject` is an epimorphism and evaluation in a degree preserves
epimorphisms. -/
public theorem isZero_filtrationStep_X_of_isZero (k : ℕ) (n : ℤ)
    (hk : IsZero ((S.source (k + 1)).X n)) :
    IsZero (((S.filtrationStep ((k : ℤ) + 1)) : CochainComplex C ℤ).X n) := by
  rw [S.filtrationStep_of_pos (by omega), Int.toNat_natCast_add_one]
  exact IsZero.of_epi ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map
    (factorThruImageSubobject (S.hom (k + 1)))) hk

/-- **The filtration by images is degreewise finite** as soon as the system vanishes degree by
degree.  This is the hypothesis [Stacks, Tag 05S3] needs of both sides in order to conclude from
the graded pieces to the underlying morphism of complexes
(`CochainComplex.quasiIso_hom_of_filteredQuasiIso`); half of it is free here, the step at `0`
being the whole complex by definition.

The vanishing is asked for at a member of index `k + 1` rather than `k` because it is the steps
at *positive* indices that are images; a system vanishing in degree `n` at the index `0` alone
would say nothing about the filtration, whose step at `0` is the whole complex. -/
public theorem isDegreewiseFinite_filtered
    (h : ∀ n : ℤ, ∃ k : ℕ, IsZero ((S.source (k + 1)).X n)) :
    S.filtered.filtration.IsDegreewiseFinite := by
  intro n
  obtain ⟨k, hk⟩ := h n
  refine ⟨0, (k : ℤ) + 1, ?_, ?_⟩
  · have : IsIso (S.filtered.filtration.ι.app (op (0 : ℤ))) :=
      S.isIso_filtered_ι_of_nonpos le_rfl
    exact inferInstanceAs (IsIso ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map
      (S.filtered.filtration.ι.app (op (0 : ℤ)))))
  · exact S.isZero_filtrationStep_X_of_isZero k n hk

end ImageSystem

end CochainComplex

end
