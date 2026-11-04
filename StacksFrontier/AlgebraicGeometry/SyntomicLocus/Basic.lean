module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.SyntomicLocus.Algebra

/-!
# Syntomic morphisms at a point, and the complete-intersection fibre criterion

A morphism of schemes `f : X ⟶ S` is *syntomic at* `x : X` when, on some affine open
neighbourhood `U` of `x` mapping into some affine open `V` of `f x`, the ring map
`Γ(S, V) → Γ(X, U)` is syntomic (Stacks Definition 01UC).  The *closed fibre* of `f` at `x` is
`κ(f x) ⊗_{O_{S, f x}} O_{X, x}`, the local ring of the scheme-theoretic fibre `X_{f x}` at `x`.

The main result is the criterion of Stacks Lemma 01UE in the form needed for base-change
questions: for `f` flat and locally of finite presentation, `f` is syntomic at `x` if and only if
the closed fibre at `x` is a complete intersection over `κ(f x)` (Definition 00SD).  The point of
this form is that the right-hand side refers only to the stalks of `f` at `x` and so is
manifestly independent of the affine chart, whereas the left-hand side is an existential over
charts.

## Main definitions

* `AlgebraicGeometry.IsSyntomicAt`: `f` is syntomic at `x`, Stacks Definition 01UC.
* `AlgebraicGeometry.IsCompleteIntersectionFibreAt`: the closed fibre of `f` at `x` is a complete
  intersection over the residue field of `f x`.

## Main results

* `AlgebraicGeometry.isCompleteIntersectionFibreAt_iff_chart`: the closed fibre condition,
  computed in an arbitrary affine chart.  This is the chart-independence statement.
* `AlgebraicGeometry.isSyntomicAt_iff_isCompleteIntersectionFibreAt`: Stacks Lemma 01UE
  (1) ⟺ (3) for a flat morphism locally of finite presentation.

## Implementation notes

The closed fibre is `κ(O_{S,s}) ⊗_{O_{S,s}} O_{X,x}` rather than the stalk of
`AlgebraicGeometry.Scheme.Hom.fiber` at `AlgebraicGeometry.Scheme.Hom.asFiber`; the two agree,
since the local ring of the fibre at `x` is `O_{X,x}/𝔪_s O_{X,x}`, and this description avoids the
scheme-theoretic fibre altogether.

## References

* [Stacks 01UC](https://stacks.math.columbia.edu/tag/01UC), Definition 29.30.1.
* [Stacks 01UE](https://stacks.math.columbia.edu/tag/01UE), Lemma 29.30.11.
* [Stacks 00SY](https://stacks.math.columbia.edu/tag/00SY), Lemma 10.136.15.
-/

@[expose] public section

open scoped TensorProduct

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **Stacks Project, Tag 01UC.** A morphism of schemes `f : X ⟶ S` is *syntomic at* `x : X` if
there are affine open neighbourhoods `U` of `x` and `V` of `f x`, with `f(U) ⊆ V`, for which the
induced map `Γ(S, V) → Γ(X, U)` is syntomic. -/
def IsSyntomicAt (f : X ⟶ S) (x : X) : Prop :=
  ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ V : S.affineOpens, ∃ hUV : U.1 ≤ f ⁻¹ᵁ V.1,
    letI := (f.appLE V.1 U.1 hUV).hom.toAlgebra; Algebra.Syntomic Γ(S, V.1) Γ(X, U.1)

/-- The closed fibre of `f` at `x` is the fibre `κ(f x) ⊗_{O_{S, f x}} O_{X, x}` of the local
ring map of `f` at `x`; this predicate says that it is a complete intersection over the residue
field `κ(f x)`.  It is the local ring of the scheme-theoretic fibre `X_{f x}` at `x`. -/
def IsCompleteIntersectionFibreAt (f : X ⟶ S) (x : X) : Prop :=
  letI := (f.stalkMap x).hom.toAlgebra
  IsCompleteIntersection (ResidueField (S.presheaf.stalk (f x)))
    (ResidueField (S.presheaf.stalk (f x)) ⊗[S.presheaf.stalk (f x)] (X.presheaf.stalk x))

section Chart

variable (f : X ⟶ S) {x : X} {V : S.Opens} (hV : IsAffineOpen V) {U : X.Opens}
    (hU : IsAffineOpen U) (hUV : U ≤ f ⁻¹ᵁ V) (hx : x ∈ U)

include hV hU hx in
/-- The prime of `Γ(X, U)` at `x` lies over the prime of `Γ(S, V)` at `f x`. -/
theorem liesOver_primeIdealOf_appLE :
    letI := (f.appLE V U hUV).hom.toAlgebra
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.LiesOver (hV.primeIdealOf ⟨f x, hUV hx⟩).asIdeal := by
  let := (f.appLE V U hUV).hom.toAlgebra
  exact ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hx).1).symm⟩

include hV hU hx in
/-- **The closed fibre, computed in an affine chart.**  For `x ∈ U ⊆ f⁻¹(V)` with `U`, `V` affine
open, the closed fibre of `f` at `x` is a complete intersection over `κ(f x)` exactly when the
fibre `κ(p) ⊗ Γ(X, U)_q` of the chart is a complete intersection over `κ(p)`, where `p` and `q`
are the primes of `f x` and `x` in the charts.

The left-hand side is defined in terms of the stalks alone, so this is also the statement that the
right-hand side does not depend on the chart. -/
theorem isCompleteIntersectionFibreAt_iff_chart :
    letI := (f.appLE V U hUV).hom.toAlgebra
    IsCompleteIntersectionFibreAt f x ↔
      IsCompleteIntersection (hV.primeIdealOf ⟨f x, hUV hx⟩).asIdeal.ResidueField
        ((hV.primeIdealOf ⟨f x, hUV hx⟩).asIdeal.Fiber
          (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)) := by
  let := (f.appLE V U hUV).hom.toAlgebra
  let := S.presheaf.algebra_section_stalk (⟨f x, hUV hx⟩ : V)
  let := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  have hps : IsLocalization.AtPrime (S.presheaf.stalk (f x))
      (hV.primeIdealOf ⟨f x, hUV hx⟩).asIdeal := hV.isLocalization_stalk ⟨f x, hUV hx⟩
  have hqs : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  have hlo := liesOver_primeIdealOf_appLE f hV hU hUV hx
  let : Algebra ↑Γ(S, V) ↑(X.presheaf.stalk x) :=
    ((algebraMap Γ(X, U) (X.presheaf.stalk x)).comp
      (algebraMap Γ(S, V) Γ(X, U))).toAlgebra
  have htow : IsScalarTower ↑Γ(S, V) ↑Γ(X, U) ↑(X.presheaf.stalk x) :=
    .of_algebraMap_eq fun _ ↦ rfl
  let : Algebra ↑(S.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have htow' : IsScalarTower ↑Γ(S, V) ↑(S.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) := by
    refine .of_algebraMap_eq fun s ↦ ?_
    show X.presheaf.germ U x hx (f.appLE V U hUV s) =
      f.stalkMap x (S.presheaf.germ V (f x) (hUV hx) s)
    rw [Scheme.Hom.germ_stalkMap_apply f V x (hUV hx) s]
    simp [Scheme.Hom.appLE]
  exact Stacks.SyntomicLocus.isCompleteIntersection_closedFibre_iff
    (hV.primeIdealOf ⟨f x, hUV hx⟩).asIdeal (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    (S.presheaf.stalk (f x)) (X.presheaf.stalk x)

include hV hU hx in
/-- If `Γ(S, V) → Γ(X, U)` becomes syntomic after inverting `g`, and `g` does not vanish at `x`,
then `f` is syntomic at `x`. -/
theorem isSyntomicAt_of_syntomic_localization_away
    (g : Γ(X, U)) (hg : g ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
    (hsyn : letI := (f.appLE V U hUV).hom.toAlgebra;
      Algebra.Syntomic Γ(S, V) (Localization.Away g)) :
    IsSyntomicAt f x := by
  let := (f.appLE V U hUV).hom.toAlgebra
  have hsyn' := hsyn
  have hxg : x ∈ X.basicOpen g := by
    let := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
    have hqs : IsLocalization.AtPrime (X.presheaf.stalk x)
        (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
    rw [Scheme.mem_basicOpen _ g x hx]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal g).mpr hg
  have hle : X.basicOpen g ≤ f ⁻¹ᵁ V := (X.basicOpen_le g).trans hUV
  have hloc := hU.isLocalization_basicOpen g
  let := (f.appLE V (X.basicOpen g) hle).hom.toAlgebra
  have htow : IsScalarTower ↑Γ(S, V) ↑Γ(X, U) ↑Γ(X, X.basicOpen g) := by
    refine .of_algebraMap_eq fun s ↦ ?_
    show f.appLE V (X.basicOpen g) hle s =
      X.presheaf.map (homOfLE (X.basicOpen_le g)).op (f.appLE V U hUV s)
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  exact ⟨⟨X.basicOpen g, hU.basicOpen g⟩, hxg, ⟨V, hV⟩, hle,
    Stacks.SyntomicLocus.Algebra.Syntomic.of_algEquiv
      ((IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g)
        Γ(X, X.basicOpen g)).restrictScalars Γ(S, V))⟩

end Chart

/-- **Stacks Project, Tag 01UE.**  A flat morphism locally of finite presentation is syntomic at
a point exactly when the closed fibre there is a complete intersection over the residue field of
the image point. -/
@[ega "IV 19.3.6"]
theorem isSyntomicAt_iff_isCompleteIntersectionFibreAt (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [Flat f] (x : X) :
    IsSyntomicAt f x ↔ IsCompleteIntersectionFibreAt f x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨⟨U, hU⟩, hx, ⟨V, hV⟩, hUV, hsyn⟩ := h
    let := (f.appLE V U hUV).hom.toAlgebra
    have hsyn' := hsyn
    have hlo := liesOver_primeIdealOf_appLE f hV hU hUV hx
    rw [isCompleteIntersectionFibreAt_iff_chart f hV hU hUV hx]
    exact IsCompleteIntersection.fiber_congr
      (Ideal.over_def (hU.primeIdealOf ⟨x, hx⟩).asIdeal
        (hV.primeIdealOf ⟨f x, hUV hx⟩).asIdeal).symm
      (Algebra.Syntomic.flat_localization_and_isCompleteIntersection_fiber
        (hU.primeIdealOf ⟨x, hx⟩).asIdeal).2
  · obtain ⟨-, ⟨V, hV, rfl⟩, hfxV, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨-, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      hfxV (V.2.preimage f.continuous)
    rw [isCompleteIntersectionFibreAt_iff_chart f hV hU hUV hxU] at h
    have hfp := f.finitePresentation_appLE hV hU hUV
    have hfl := f.flat_appLE hV hU hUV
    algebraize [(f.appLE V U hUV).hom]
    have hlo := liesOver_primeIdealOf_appLE f hV hU hUV hxU
    obtain ⟨g, hg, hsyn⟩ :=
      (Stacks.SyntomicLocus.exists_notMem_syntomic_iff_isCompleteIntersection_fiber
        (hV.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal (hU.primeIdealOf ⟨x, hxU⟩).asIdeal).mpr h
    exact isSyntomicAt_of_syntomic_localization_away f hV hU hUV hxU g hg hsyn

end AlgebraicGeometry
