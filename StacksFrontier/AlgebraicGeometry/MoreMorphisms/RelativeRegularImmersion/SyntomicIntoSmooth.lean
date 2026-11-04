module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.FibreInput
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.Gluing
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion

/-!
# An immersion of a syntomic scheme into a smooth scheme is regular

Let `i : Y ⟶ X` be an immersion and `f : X ⟶ S` a smooth morphism, and suppose the structure
morphism `i ≫ f` of `Y` over `S` is syntomic.  Then `i` is a regular immersion.  In particular
an immersion between two schemes smooth over `S` is regular.

## Main results

* `Stacks.AlgebraicGeometry.isRegularImmersion_of_syntomic_of_smooth`: **Stacks tag 067T**.
* `Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth`: **Stacks tag 067U**.

## Implementation notes

The commuting triangle of the source is encoded by writing the structure morphism of `Y` as the
composite `i ≫ f`, as in `Stacks.AlgebraicGeometry.isRegularImmersion_of_isRelativeQuasiRegular\
Immersion`.

The source reduces 067T to Stacks 063W, which produces a *relative quasi-regular* immersion from
a quasi-regular immersion of fibres, and then to Stacks 063U.  Here the route is shorter and
avoids quasi-regularity altogether, because the fibres supply a *regular* sequence on the nose:
after replacing `X` by the coborder range, so that `i` becomes a closed immersion `j`, the local
rings of the fibre `Γ(X, U)_q/pΓ(X, U)_q` are regular (the chart is smooth over the base,
Stacks 07NF through Stacks 00TT) while those of the fibre of `Y` are complete intersections over
the residue field (the chart is syntomic over the base, Stacks 00SY), so Stacks 00SF gives a
regular sequence generating the ideal of the fibre.  That is exactly the hypothesis of
`Stacks.AlgebraicGeometry.isRegularIdealSheaf_definingIdealOfHom_of_isRegular_fibre`, which runs
the two spreading-out statements of Stacks 062Y (3) and Stacks 046Y and glues;  its conclusion is
regularity of the defining ideal sheaf, which is the definition of a regular immersion.

Both halves of the fibre input are packaged in
`Stacks.RingTheory.SpreadingOut.exists_isRegular_fibre_of_smooth_of_syntomic`;  what this file
adds is the dictionary at a chart:  `Γ(S, W) → Γ(X, U)` is smooth by
`AlgebraicGeometry.Smooth.smooth_appLE`, `Γ(S, W) → Γ(Y, j⁻¹U)` is syntomic by the second item of
`AlgebraicGeometry.syntomic_tfae`, the two are compared by the surjection `j.app U`, and the
defining ideal is finitely generated because source and target of that surjection are of finite
presentation over `Γ(S, W)` (`Algebra.FinitePresentation.ker_fG_of_surjective`).

## References

* [Stacks Project, Lemma 31.22.6 (Tag 067T)](https://stacks.math.columbia.edu/tag/067T)
* [Stacks Project, Lemma 31.22.7 (Tag 067U)](https://stacks.math.columbia.edu/tag/067U)
* [Stacks Project, Lemma 31.22.8 (Tag 063W)](https://stacks.math.columbia.edu/tag/063W)
* [Stacks Project, Lemma 29.30.5 (Tag 01VD)](https://stacks.math.columbia.edu/tag/01VD)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry RingTheory.Sequence
open Stacks.RingTheory.SpreadingOut
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

universe u

section Immersion

variable {Y X S : Scheme.{u}} (i : Y ⟶ X) (f : X ⟶ S)

/-- The comparison of the structure map of `Z` over the base with the one of `Y`. -/
public theorem appLE_comp_app {S Y Z : Scheme.{u}} (g : Y ⟶ S) (j : Z ⟶ Y) {W : S.Opens}
    {U : Y.Opens} (hUW : U ≤ g ⁻¹ᵁ W) :
    (j ≫ g).appLE W (j ⁻¹ᵁ U) (fun _ hz => hUW hz) = g.appLE W U hUW ≫ j.app U := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

/-- **Stacks Project, Tag 067T.**  Let `i : Y ⟶ X` be an immersion and `f : X ⟶ S` a smooth
morphism such that the structure morphism `i ≫ f` of `Y` over `S` is syntomic.  Then `i` is a
regular immersion. -/
@[stacks 067T, sga "6 VII 1.10" "more general"]
theorem isRegularImmersion_of_syntomic_of_smooth [IsImmersion i] [Smooth f]
    (h : Syntomic (i ≫ f)) : IsRegularImmersion i := by
  have : Flat f := AlgebraicGeometry.flat (syntomic_of_smooth f)
  have : LocallyOfFinitePresentation f :=
    AlgebraicGeometry.locallyOfFinitePresentation (syntomic_of_smooth f)
  set g : i.coborderRange.toScheme ⟶ S := i.coborderRange.ι ≫ f with hgdef
  set j : Y ⟶ i.coborderRange.toScheme := i.liftCoborder with hjdef
  have hjg : j ≫ g = i ≫ f := by rw [hgdef, hjdef, ← Category.assoc, i.liftCoborder_ι]
  have hsyn : Syntomic (j ≫ g) := hjg ▸ h
  have : Flat (j ≫ g) := hjg ▸ AlgebraicGeometry.flat h
  have : LocallyOfFinitePresentation (j ≫ g) :=
    AlgebraicGeometry.locallyOfFinitePresentation hsyn
  refine isRegularIdealSheaf_definingIdealOfHom_of_isRegular_fibre g j ?_ ?_
  all_goals
    -- the common chart setup: the algebra structures and the comparison map `j.app U`
    intro W hW U hU hUW
    let _ : Algebra Γ(S, W) Γ(i.coborderRange.toScheme, U) := (g.appLE W U hUW).hom.toAlgebra
    let _ : Algebra Γ(S, W) Γ(Y, j ⁻¹ᵁ U) :=
      ((j ≫ g).appLE W (j ⁻¹ᵁ U) (fun _ hz => hUW hz)).hom.toAlgebra
    let φ : Γ(i.coborderRange.toScheme, U) →ₐ[Γ(S, W)] Γ(Y, j ⁻¹ᵁ U) :=
      { (j.app U).hom with
        commutes' := fun t => by
          rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
            appLE_comp_app g j hUW, CommRingCat.hom_comp]
          rfl }
  · -- the defining ideal is finitely generated over a chart
    have : Algebra.FinitePresentation Γ(S, W) Γ(i.coborderRange.toScheme, U) :=
      g.finitePresentation_appLE hW hU hUW
    have : Algebra.FinitePresentation Γ(S, W) Γ(Y, j ⁻¹ᵁ U) :=
      (j ≫ g).finitePresentation_appLE hW (hU.preimage j) (fun _ hz => hUW hz)
    exact Algebra.FinitePresentation.ker_fG_of_surjective φ
      (Scheme.Hom.app_surjective j U hU)
  · -- the fibre input at a chart
    intro q hq hIq
    have hsm : Algebra.Smooth Γ(S, W) Γ(i.coborderRange.toScheme, U) :=
      (g.smooth_appLE hW hU hUW).toAlgebra
    have htfae := ((syntomic_tfae (j ≫ g)).out 1 2).mp hsyn
    have hsy : Algebra.Syntomic Γ(S, W) Γ(Y, j ⁻¹ᵁ U) :=
      htfae (j ⁻¹ᵁ U) (hU.preimage j) W hW (fun _ hz => hUW hz)
    obtain ⟨r, fs, hfI, -, hreg, hsup⟩ := exists_isRegular_fibre_of_smooth_of_syntomic φ
      (Scheme.Hom.app_surjective j U hU) q hIq
    exact ⟨r, fs, hfI, hreg, hsup⟩

/-- **Stacks Project, Tag 067U.**  An immersion `i : Y ⟶ X` between two schemes smooth over `S`
is a regular immersion.  This is the case of Stacks tag 067T in which the structure morphism of
`Y` is smooth, a smooth morphism being syntomic (Stacks tag 01VD). -/
@[stacks 067U,
  sga "6 VII 1.10",
  sga "1 II 4.16" "X smooth ⇒ i regular",
  sga "6 VIII 1.1" "more general",
  sga "6 VIII 1.3" "more general",
  sga "6 VIII 1.8" "partial, special case",
  sga "6 VIII 2.4" "special case"]
theorem isRegularImmersion_of_smooth_of_smooth [IsImmersion i] [Smooth f] [Smooth (i ≫ f)] :
    IsRegularImmersion i :=
  isRegularImmersion_of_syntomic_of_smooth i f (syntomic_of_smooth (i ≫ f))

end Immersion

end Stacks.AlgebraicGeometry

end
