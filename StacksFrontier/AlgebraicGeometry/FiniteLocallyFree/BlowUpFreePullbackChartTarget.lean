module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RestrictUnitIsoComp
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BlowUpFreeChartDescent
public import StacksFrontier.AlgebraicGeometry.RestrictIso

/-!
# The target trivialisation of the chart comparison, and the uniqueness of the section

For `α : 𝒪_{X'}^{⊕I} ⟶ 𝒢` invertible over an open `P` of `X'`, the inverse of the restriction of
`α` followed by `Stacks.Modules.restrictFreeIso` trivialises `𝒢` over `P`:
`𝒢|_P ≅ 𝒪^{⊕I}|_P ≅ 𝒪_P^{⊕I}`. This file shows that this trivialisation is compatible with
shrinking the open, in the form of `AlgebraicGeometry.restrictChartIso`.

It also shows that the section `AlgebraicGeometry.freeChartBaseSection` of `b : X' ⟶ X` over an
open on which `b` is invertible is the only morphism to `X'` whose composite with `b` is the
inclusion of the open, and hence that the section over a smaller open is the restriction of the
section.

## Main definitions

* `AlgebraicGeometry.freeChartTargetIso`: the trivialisation of `𝒢` over an open of `X'` on
  which `α` is invertible.

## Main results

* `AlgebraicGeometry.eq_freeChartBaseSection`: the section of `b` over an open on which `b` is
  invertible is the only one.
* `AlgebraicGeometry.homOfLE_comp_freeChartBaseSection`: the section over a smaller open is the
  restriction of the section.
* `AlgebraicGeometry.isIso_restrictFunctor_map_preimage_of_le`: `α` stays invertible over the
  preimage of a smaller open.
* `AlgebraicGeometry.restrictChartIso_freeChartTargetIso`: the trivialisation of `𝒢` is
  compatible with shrinking the open.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X X' : Scheme.{u}} (b : X' ⟶ X)

/-! ### The section of `b` over an open on which it is invertible is the only one -/

/-- If `b` is invertible over an open `W`, then every morphism `s : W ⟶ X'` whose composite with
`b` is the inclusion of `W` is the section `AlgebraicGeometry.freeChartBaseSection b W`. -/
theorem eq_freeChartBaseSection (W : X.Opens) [IsIso (b ∣_ W)] (s : W.toScheme ⟶ X')
    (hs : s ≫ b = W.ι) : s = freeChartBaseSection b W := by
  have hrange : Set.range s.base ⊆ Set.range (b ⁻¹ᵁ W).ι.base :=
    range_subset_range_preimage_ι b W s hs (Scheme.Opens.range_ι W).subset
  have hl : IsOpenImmersion.lift (b ⁻¹ᵁ W).ι s hrange ≫ (b ⁻¹ᵁ W).ι = s :=
    IsOpenImmersion.lift_fac _ _ _
  have hcancel : IsOpenImmersion.lift (b ⁻¹ᵁ W).ι s hrange ≫ (b ∣_ W) = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hl, hs,
      Category.id_comp]
  rw [← hl, IsIso.eq_inv_of_inv_hom_id hcancel, freeChartBaseSection]

/-- The section of `b` over a smaller open `W' ≤ W` is the inclusion of `W'` into `W` followed by
the section of `b` over `W`. -/
theorem homOfLE_comp_freeChartBaseSection {W W' : X.Opens} (hW : W' ≤ W) [IsIso (b ∣_ W)]
    [IsIso (b ∣_ W')] :
    X.homOfLE hW ≫ freeChartBaseSection b W = freeChartBaseSection b W' :=
  eq_freeChartBaseSection b W' _ <| by
    rw [Category.assoc, freeChartBaseSection_comp, Scheme.homOfLE_ι]

/-! ### The trivialisation of `𝒢` given by `α` -/

variable {I : Type u} {G : X'.Modules} (α : _root_.SheafOfModules.free.{u} I ⟶ G)

/-- If `α` is invertible over the preimage of `U`, then it is invertible over the preimage of
every `W ≤ U`. -/
theorem isIso_restrictFunctor_map_preimage_of_le {U W : X.Opens} (hW : W ≤ U)
    (hα : IsIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ U).ι).map α)) :
    IsIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ W).ι).map α) :=
  Scheme.Modules.isIso_restrictFunctor_map_of_fac α (b ⁻¹ᵁ U).ι
    (X'.homOfLE (b.preimage_mono hW)) (Scheme.homOfLE_ι X' _) hα

/-- The trivialisation of `𝒢` over an open `P` of `X'` on which `α` is invertible: the inverse
of the restriction of `α`, followed by the isomorphism `Stacks.Modules.restrictFreeIso` between
the restriction of the free module and the free module. -/
def freeChartTargetIso (P : X'.Opens)
    (hα : IsIso ((Scheme.Modules.restrictFunctor P.ι).map α)) :
    Scheme.Modules.restrict G P.ι ≅
      _root_.SheafOfModules.free (R := P.toScheme.ringCatSheaf) I :=
  haveI := hα
  (asIso ((Scheme.Modules.restrictFunctor P.ι).map α)).symm ≪≫
    Stacks.Modules.restrictFreeIso P.ι I

/-- For open immersions `c` and `p` with composite `k`, the isomorphism
`AlgebraicGeometry.restrictCompIso` at the free module, followed by the restriction along `c` of
`Stacks.Modules.restrictFreeIso p I`, is `Stacks.Modules.restrictFreeIso k I` followed by the
inverse of `Stacks.Modules.restrictFreeIso c I`. -/
theorem restrictCompIso_hom_comp_map_restrictFreeIso_hom {T' T : Scheme.{u}} (c : T' ⟶ T)
    (p : T ⟶ X') [IsOpenImmersion c] [IsOpenImmersion p] {k : T' ⟶ X'} (hk : c ≫ p = k)
    [IsOpenImmersion k] (I : Type u) :
    (restrictCompIso c p hk (_root_.SheafOfModules.free.{u} (R := X'.ringCatSheaf) I)).hom ≫
        (Scheme.Modules.restrictFunctor c).map (Stacks.Modules.restrictFreeIso p I).hom =
      (Stacks.Modules.restrictFreeIso k I).hom ≫ (Stacks.Modules.restrictFreeIso c I).inv := by
  have E := Stacks.Modules.restrictFreeIso_inv_comp_restrictCompIso_hom c p hk I
  have hA : (restrictCompIso c p hk
        (_root_.SheafOfModules.free.{u} (R := X'.ringCatSheaf) I)).hom =
      (Stacks.Modules.restrictFreeIso k I).hom ≫
        (Stacks.Modules.restrictFreeIso c I).inv ≫
          (Scheme.Modules.restrictFunctor c).map (Stacks.Modules.restrictFreeIso p I).inv :=
    ((Category.id_comp _).symm.trans
      (congrArg (· ≫ (restrictCompIso c p hk
          (_root_.SheafOfModules.free.{u} (R := X'.ringCatSheaf) I)).hom)
        (Stacks.Modules.restrictFreeIso k I).hom_inv_id.symm)).trans
      ((Category.assoc _ _ _).trans
        (congrArg ((Stacks.Modules.restrictFreeIso k I).hom ≫ ·) E))
  refine (congrArg
    (· ≫ (Scheme.Modules.restrictFunctor c).map
      (Stacks.Modules.restrictFreeIso p I).hom) hA).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg ((Stacks.Modules.restrictFreeIso k I).hom ≫ ·) ?_
  refine (Category.assoc _ _ _).trans ?_
  have hid : (Scheme.Modules.restrictFunctor c).map
        (Stacks.Modules.restrictFreeIso p I).inv ≫
      (Scheme.Modules.restrictFunctor c).map (Stacks.Modules.restrictFreeIso p I).hom =
      𝟙 _ :=
    (((Scheme.Modules.restrictFunctor c).map_comp
      (Stacks.Modules.restrictFreeIso p I).inv
      (Stacks.Modules.restrictFreeIso p I).hom).symm.trans
        (congrArg (Scheme.Modules.restrictFunctor c).map
          (Stacks.Modules.restrictFreeIso p I).inv_hom_id)).trans
      ((Scheme.Modules.restrictFunctor c).map_id _)
  exact (congrArg ((Stacks.Modules.restrictFreeIso c I).inv ≫ ·) hid).trans
    (Category.comp_id _)

/-- The trivialisation of `𝒢` is compatible with shrinking the open: for `P' ≤ P`, the restriction
of `AlgebraicGeometry.freeChartTargetIso` at `P` along the inclusion of `P'` is the trivialisation
at `P'` followed by the inverse of the isomorphism between the restriction of the free module on
`P` and the free module on `P'`. -/
theorem restrictChartIso_freeChartTargetIso {P P' : X'.Opens} (hP : P' ≤ P)
    (hα : IsIso ((Scheme.Modules.restrictFunctor P.ι).map α))
    (hα' : IsIso ((Scheme.Modules.restrictFunctor P'.ι).map α)) :
    restrictChartIso P.ι (freeChartTargetIso α P hα) (X'.homOfLE hP)
          (Scheme.homOfLE_ι X' hP) =
      freeChartTargetIso α P' hα' ≪≫
        (Stacks.Modules.restrictFreeIso (X'.homOfLE hP) I).symm := by
  have := hα
  have := hα'
  refine Iso.ext ?_
  have hnat := restrictCompIso_naturality (X'.homOfLE hP) P.ι (Scheme.homOfLE_ι X' hP) α
  have hstep : (restrictCompIso (X'.homOfLE hP) P.ι (Scheme.homOfLE_ι X' hP) G).hom ≫
      (Scheme.Modules.restrictFunctor (X'.homOfLE hP)).map
        (inv ((Scheme.Modules.restrictFunctor P.ι).map α)) =
      inv ((Scheme.Modules.restrictFunctor P'.ι).map α) ≫
        (restrictCompIso (X'.homOfLE hP) P.ι (Scheme.homOfLE_ι X' hP)
          (_root_.SheafOfModules.free.{u} (R := X'.ringCatSheaf) I)).hom :=
    (congrArg ((restrictCompIso (X'.homOfLE hP) P.ι (Scheme.homOfLE_ι X' hP) G).hom ≫ ·)
      ((Scheme.Modules.restrictFunctor (X'.homOfLE hP)).map_inv
        ((Scheme.Modules.restrictFunctor P.ι).map α))).trans
      ((IsIso.comp_inv_eq _).2
        (((IsIso.eq_inv_comp _).2 hnat).trans (Category.assoc _ _ _).symm))
  change (restrictCompIso (X'.homOfLE hP) P.ι (Scheme.homOfLE_ι X' hP) G).hom ≫
      (Scheme.Modules.restrictFunctor (X'.homOfLE hP)).map
        (inv ((Scheme.Modules.restrictFunctor P.ι).map α) ≫
          (Stacks.Modules.restrictFreeIso P.ι I).hom) =
    (inv ((Scheme.Modules.restrictFunctor P'.ι).map α) ≫
        (Stacks.Modules.restrictFreeIso P'.ι I).hom) ≫
      (Stacks.Modules.restrictFreeIso (X'.homOfLE hP) I).inv
  refine (congrArg ((restrictCompIso (X'.homOfLE hP) P.ι (Scheme.homOfLE_ι X' hP) G).hom ≫ ·)
    ((Scheme.Modules.restrictFunctor (X'.homOfLE hP)).map_comp _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (Scheme.Modules.restrictFunctor (X'.homOfLE hP)).map
    (Stacks.Modules.restrictFreeIso P.ι I).hom) hstep).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (inv ((Scheme.Modules.restrictFunctor P'.ι).map α) ≫ ·)
    (restrictCompIso_hom_comp_map_restrictFreeIso_hom (X'.homOfLE hP) P.ι
      (Scheme.homOfLE_ι X' hP) I)).trans ?_
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry

end
