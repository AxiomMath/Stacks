module

public import StacksFrontier.AlgebraicGeometry.Blowup.CompositeCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.BlowUpIsProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.FiniteTypeIdealSheaf

/-!
# Two-step blow-up towers

Let `W` be a scheme and `I`, `J` quasi-coherent ideal sheaves on `W`, with blow-up
`b_I : Bl_I W ⟶ W` (`AlgebraicGeometry.blowUpToBase`). This file sets up the two-step towers of
Hironaka's example (the source of [Stacks, Tag 08J1]): blow up `I`, then blow up the strict
transform of the closed subscheme cut out by `J`.

The strict transform of `V(J)` along `b_I` is the closed subscheme
`Stacks.StrictTransform.scheme` of the base change `V(J) ×_W Bl_I W` ([Stacks, Tag 080D]); that
base change is a closed subscheme of `Bl_I W` through its second projection, so the strict
transform is a closed subscheme of `Bl_I W`, and its ideal sheaf there is
`AlgebraicGeometry.TwoStepTower.strictCentre I J`. The tower is
`AlgebraicGeometry.TwoStepTower.strictTower I J`, the blow-up of `Bl_I W` in that ideal followed
by `b_I`.

## Main definitions

* `AlgebraicGeometry.TwoStepTower.strictCentre`: the ideal sheaf on `Bl_I W` of the strict
  transform of `V(J)`.
* `AlgebraicGeometry.TwoStepTower.strictTower`: the composite
  `Bl_{strictCentre I J}(Bl_I W) ⟶ Bl_I W ⟶ W`.
* `AlgebraicGeometry.TwoStepTower.totalTowerIso`: for arbitrary `I` and `J`, the towers
  `Bl_{J·𝒪}(Bl_I W) ⟶ W` and `Bl_{I·𝒪}(Bl_J W) ⟶ W` are isomorphic over `W`.
* `AlgebraicGeometry.TwoStepTower.strictTowerIso`: when `V(I)` and `V(J)` are disjoint, the two
  strict-transform towers `strictTower I J` and `strictTower J I` are isomorphic over `W`.

## Main results

* `AlgebraicGeometry.TwoStepTower.isProjective_comp_blowUpToBase`: over a quasi-compact
  quasi-separated base, blowing up a centre of finite type and then a centre of finite type on
  the blow-up is projective in the sense of [Stacks, Tag 01W8].
* `AlgebraicGeometry.TwoStepTower.isFiniteType_strictCentre`: over a locally Noetherian base the
  strict-transform centre of the tower is of finite type, so
  `AlgebraicGeometry.TwoStepTower.isProjective_strictTower`: the strict-transform tower over a
  Noetherian base is projective.
* `AlgebraicGeometry.TwoStepTower.strictCentre_eq_comap_of_disjoint`: when `V(I)` and `V(J)` are
  disjoint, the strict transform of `V(J)` is its total transform, `strictCentre I J =
  J.comap b_I`; `AlgebraicGeometry.TwoStepTower.strictCentre_eq_comap_of_sup_eq_top` is the same
  under `I ⊔ J = ⊤`.

## Implementation notes

The projectivity of a single blow-up is `Stacks.Blowup.isProjective_blowUpToBase`
([Stacks, Tag 02NS]) and the composition is `AlgebraicGeometry.IsProjective.comp`
([Stacks, Tag 0C4P]), which needs the final base to be quasi-compact and quasi-separated only.

Both orders of the tower are compared with the single blow-up in `I * J` through
[Stacks, Tag 080A] (`AlgebraicGeometry.blowUpMulIso`), with `I * J = J * I`. That comparison is
for the *total* transform `J.comap b_I`, and needs no hypothesis; disjointness enters only
through the identification of the strict transform with the total transform. The latter holds
because a point of `V(J) ×_W Bl_I W` lying over `V(I)` would lie over `V(I) ∩ V(J)`, so the
exceptional preimage of the strict transform is empty, and the strict transform is the whole
base change, whose ideal on `Bl_I W` is `J.comap b_I` by the definition of
`AlgebraicGeometry.Scheme.IdealSheafData.comap`.

## References

* [Stacks Project, Tag 08J1](https://stacks.math.columbia.edu/tag/08J1)
* [Stacks Project, Tag 080A](https://stacks.math.columbia.edu/tag/080A)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
* [Stacks Project, Tag 0C4P](https://stacks.math.columbia.edu/tag/0C4P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TwoStepTower

variable {W : Scheme.{u}}

/-! ### The strict-transform centre -/

/-- The ideal sheaf on `Bl_I W` of the strict transform of the closed subscheme `V(J)` along the
blow-up `b_I` ([Stacks, Tag 080D]): the kernel of the composite of the strict transform
`Stacks.StrictTransform.scheme`, a closed subscheme of `V(J) ×_W Bl_I W`, with the projection of
that base change to `Bl_I W`. -/
def strictCentre (I J : W.IdealSheafData) : (blowUp I).IdealSheafData :=
  ((Stacks.StrictTransform.ideal J.subschemeι (blowUpToBase I) (exceptionalIdeal I)).subschemeι ≫
    pullback.snd J.subschemeι (blowUpToBase I)).ker

/-- The two-step tower of Hironaka's example: blow up `W` in `I`, then blow up `Bl_I W` in the
strict transform of `V(J)`, as a morphism to `W`. -/
abbrev strictTower (I J : W.IdealSheafData) : blowUp (strictCentre I J) ⟶ W :=
  blowUpToBase (strictCentre I J) ≫ blowUpToBase I

/-! ### Projectivity -/

/-- The blow-up in a centre of finite type is proper, being projective
([Stacks, Tags 02NS and 01WC]). -/
theorem isProper_blowUpToBase {I : W.IdealSheafData} (hI : I.IsFiniteType) :
    IsProper (blowUpToBase I) :=
  (Stacks.Blowup.isProjective_blowUpToBase I hI).isProper

/-- The blow-up of a quasi-compact scheme in a centre of finite type is quasi-compact. -/
theorem compactSpace_blowUp [CompactSpace W] {I : W.IdealSheafData} (hI : I.IsFiniteType) :
    CompactSpace (blowUp I) :=
  haveI := isProper_blowUpToBase hI
  compactSpace_of_isProper (blowUpToBase I)

/-- The blow-up of a quasi-separated scheme in a centre of finite type is quasi-separated. -/
theorem quasiSeparatedSpace_blowUp [QuasiSeparatedSpace W] {I : W.IdealSheafData}
    (hI : I.IsFiniteType) : QuasiSeparatedSpace (blowUp I) :=
  haveI := isProper_blowUpToBase hI
  quasiSeparatedSpace_of_isProper (blowUpToBase I)

/-- The blow-up of a locally Noetherian scheme in a centre of finite type is locally Noetherian:
the blow-up morphism is of finite type. -/
theorem isLocallyNoetherian_blowUp [IsLocallyNoetherian W] {I : W.IdealSheafData}
    (hI : I.IsFiniteType) : IsLocallyNoetherian (blowUp I) :=
  haveI := isProper_blowUpToBase hI
  LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase I)

/-- On a locally Noetherian scheme every quasi-coherent ideal sheaf is of finite type: its ideal
on an affine open is an ideal of a Noetherian ring. -/
theorem isFiniteType_of_isLocallyNoetherian {X : Scheme.{u}} [IsLocallyNoetherian X]
    (K : X.IdealSheafData) : K.IsFiniteType := fun U ↦
  haveI := IsLocallyNoetherian.component_noetherian U
  (IsNoetherian.noetherian (K.ideal U))

/-- **Projectivity of a two-step blow-up tower.** Over a quasi-compact quasi-separated scheme
`W`, blowing up a centre `I` of finite type and then a centre `Z'` of finite type on `Bl_I W` is
projective in the sense of [Stacks, Tag 01W8]: each blow-up is projective
([Stacks, Tag 02NS]) and the composite of projective morphisms to a quasi-compact
quasi-separated scheme is projective ([Stacks, Tag 0C4P]). -/
theorem isProjective_comp_blowUpToBase [CompactSpace W] [QuasiSeparatedSpace W]
    {I : W.IdealSheafData} (hI : I.IsFiniteType) {Z' : (blowUp I).IdealSheafData}
    (hZ' : Z'.IsFiniteType) :
    IsProjective (blowUpToBase Z' ≫ blowUpToBase I) :=
  IsProjective.comp (Stacks.Blowup.isProjective_blowUpToBase Z' hZ')
    (Stacks.Blowup.isProjective_blowUpToBase I hI)

/-- The total transform `J·𝒪_{Bl_I W}` of a centre of finite type is of finite type. -/
theorem isFiniteType_comap_blowUpToBase (I : W.IdealSheafData) {J : W.IdealSheafData}
    (hJ : J.IsFiniteType) : (J.comap (blowUpToBase I)).IsFiniteType :=
  hJ.comap _

/-- Over a locally Noetherian scheme the strict-transform centre of the tower is of finite
type: the blow-up is locally Noetherian, so every quasi-coherent ideal on it is. -/
theorem isFiniteType_strictCentre [IsLocallyNoetherian W] {I : W.IdealSheafData}
    (hI : I.IsFiniteType) (J : W.IdealSheafData) : (strictCentre I J).IsFiniteType :=
  haveI := isLocallyNoetherian_blowUp hI
  isFiniteType_of_isLocallyNoetherian _

/-- **Projectivity of Hironaka's tower.** Over a Noetherian scheme (quasi-compact,
quasi-separated and locally Noetherian), the tower blowing up `I` and then the strict transform
of `V(J)` is projective in the sense of [Stacks, Tag 01W8]. -/
theorem isProjective_strictTower [CompactSpace W] [QuasiSeparatedSpace W] [IsLocallyNoetherian W]
    {I : W.IdealSheafData} (hI : I.IsFiniteType) (J : W.IdealSheafData) :
    IsProjective (strictTower I J) :=
  isProjective_comp_blowUpToBase hI (isFiniteType_strictCentre hI J)

/-! ### The strict transform off the crossing -/

/-- Two ideal sheaves generating the unit ideal have disjoint supports. -/
theorem disjoint_supportSet_of_sup_eq_top {I J : W.IdealSheafData} (h : I ⊔ J = ⊤) :
    Disjoint I.supportSet J.supportSet := by
  have hs : I.support ⊓ J.support = ⊥ := by
    rw [← Scheme.IdealSheafData.support_sup, h, Scheme.IdealSheafData.support_top]
  exact Set.disjoint_iff_inter_eq_empty.2 (congrArg SetLike.coe hs)

/-- When `V(I)` and `V(J)` are disjoint, no point of `V(J) ×_W Bl_I W` lies over the exceptional
divisor: the exceptional complement of the strict transform is everything. -/
theorem exceptionalComplement_eq_top {I J : W.IdealSheafData}
    (h : Disjoint I.supportSet J.supportSet) :
    Stacks.StrictTransform.exceptionalComplement J.subschemeι (blowUpToBase I)
      (exceptionalIdeal I) = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  change (pullback.snd J.subschemeι (blowUpToBase I)).base x ∈ (exceptionalIdeal I).support.compl
  intro hx
  have hI : (blowUpToBase I).base ((pullback.snd J.subschemeι (blowUpToBase I)).base x) ∈
      I.supportSet := by
    have hx' : (pullback.snd J.subschemeι (blowUpToBase I)).base x ∈
        (I.comap (blowUpToBase I)).support := hx
    rw [Scheme.IdealSheafData.support_comap] at hx'
    exact hx'
  have hJ : (blowUpToBase I).base ((pullback.snd J.subschemeι (blowUpToBase I)).base x) ∈
      J.supportSet := by
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    have hr := Scheme.IdealSheafData.range_subschemeι J
    exact (show Set.range J.subschemeι.base ⊆ J.supportSet from hr.le) ⟨_, rfl⟩
  exact Set.disjoint_left.mp h hI hJ

/-- When `V(I)` and `V(J)` are disjoint, the defining ideal of the strict transform of `V(J)`
inside `V(J) ×_W Bl_I W` is zero. -/
theorem strictTransformIdeal_eq_bot {I J : W.IdealSheafData}
    (h : Disjoint I.supportSet J.supportSet) :
    Stacks.StrictTransform.ideal J.subschemeι (blowUpToBase I) (exceptionalIdeal I) = ⊥ := by
  rw [Stacks.StrictTransform.ideal_eq_ker_ι, exceptionalComplement_eq_top h, ← Scheme.topIso_hom]
  exact Scheme.Hom.ker_eq_bot_of_isIso _

/-- **The strict transform off the crossing.** When `V(I)` and `V(J)` are disjoint, the strict
transform of `V(J)` along the blow-up in `I` is its total transform: the ideal of
`AlgebraicGeometry.TwoStepTower.strictCentre I J` is `J·𝒪_{Bl_I W}`. -/
theorem strictCentre_eq_comap_of_disjoint {I J : W.IdealSheafData}
    (h : Disjoint I.supportSet J.supportSet) :
    strictCentre I J = J.comap (blowUpToBase I) := by
  have : IsIso (Stacks.StrictTransform.ideal J.subschemeι (blowUpToBase I)
      (exceptionalIdeal I)).subschemeι := by
    rw [strictTransformIdeal_eq_bot h]
    infer_instance
  rw [strictCentre, Scheme.Hom.ker_comp_of_isIso, ← pullbackSymmetry_hom_comp_fst,
    Scheme.Hom.ker_comp_of_isIso]
  rfl

/-- The strict transform off the crossing, under `I ⊔ J = ⊤`. -/
theorem strictCentre_eq_comap_of_sup_eq_top {I J : W.IdealSheafData} (h : I ⊔ J = ⊤) :
    strictCentre I J = J.comap (blowUpToBase I) :=
  strictCentre_eq_comap_of_disjoint (disjoint_supportSet_of_sup_eq_top h)

/-- When `V(I)` and `V(J)` are disjoint and `J` is of finite type, the strict-transform centre is
of finite type, with no Noetherian hypothesis. -/
theorem isFiniteType_strictCentre_of_disjoint {I J : W.IdealSheafData}
    (h : Disjoint I.supportSet J.supportSet) (hJ : J.IsFiniteType) :
    (strictCentre I J).IsFiniteType := by
  rw [strictCentre_eq_comap_of_disjoint h]
  exact hJ.comap _

/-! ### The two orders of the tower -/

/-- Equal second centres give isomorphic towers over the base. -/
def towerCongr {I : W.IdealSheafData} {K K' : (blowUp I).IdealSheafData} (h : K = K') :
    Over.mk (blowUpToBase K ≫ blowUpToBase I) ≅ Over.mk (blowUpToBase K' ≫ blowUpToBase I) :=
  eqToIso (by subst h; rfl)

/-- **The two total-transform towers agree.** For arbitrary `I` and `J`, blowing up `I` and then
`J·𝒪_{Bl_I W}`, and blowing up `J` and then `I·𝒪_{Bl_J W}`, give isomorphic schemes over `W`:
both are the blow-up in `I * J = J * I` ([Stacks, Tag 080A]). -/
def totalTowerIso (I J : W.IdealSheafData) :
    Over.mk (blowUpToBase (J.comap (blowUpToBase I)) ≫ blowUpToBase I) ≅
      Over.mk (blowUpToBase (I.comap (blowUpToBase J)) ≫ blowUpToBase J) :=
  blowUpMulIso I J ≪≫ eqToIso (by rw [mul_comm]) ≪≫ (blowUpMulIso J I).symm

/-- When `V(I)` and `V(J)` are disjoint, the strict-transform tower is the blow-up of `W` in
`I * J`, over `W`. -/
def strictTowerMulIso {I J : W.IdealSheafData} (h : Disjoint I.supportSet J.supportSet) :
    Over.mk (strictTower I J) ≅ Over.mk (blowUpToBase (I * J)) :=
  towerCongr (strictCentre_eq_comap_of_disjoint h) ≪≫ blowUpMulIso I J

/-- **The two orders agree off the crossing.** When `V(I)` and `V(J)` are disjoint, blowing up
`I` and then the strict transform of `V(J)`, and blowing up `J` and then the strict transform of
`V(I)`, give isomorphic schemes over `W`. -/
def strictTowerIso {I J : W.IdealSheafData} (h : Disjoint I.supportSet J.supportSet) :
    Over.mk (strictTower I J) ≅ Over.mk (strictTower J I) :=
  towerCongr (strictCentre_eq_comap_of_disjoint h) ≪≫ totalTowerIso I J ≪≫
    (towerCongr (strictCentre_eq_comap_of_disjoint h.symm)).symm

/-- The isomorphism of the two orders of the tower lies over `W`. -/
@[reassoc (attr := simp)]
theorem strictTowerIso_hom_left_comp {I J : W.IdealSheafData}
    (h : Disjoint I.supportSet J.supportSet) :
    (strictTowerIso h).hom.left ≫ strictTower J I = strictTower I J :=
  Over.w (strictTowerIso h).hom

/-- The inverse of the isomorphism of the two orders of the tower lies over `W`. -/
@[reassoc (attr := simp)]
theorem strictTowerIso_inv_left_comp {I J : W.IdealSheafData}
    (h : Disjoint I.supportSet J.supportSet) :
    (strictTowerIso h).inv.left ≫ strictTower I J = strictTower J I :=
  Over.w (strictTowerIso h).inv

end AlgebraicGeometry.TwoStepTower

end
