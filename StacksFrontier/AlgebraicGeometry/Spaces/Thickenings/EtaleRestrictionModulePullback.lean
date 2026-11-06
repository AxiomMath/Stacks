module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AlgebraExtensionEtaleRestriction

/-!
# Étale restriction of modules is the pullback of modules

Let `a : U ⟶ X` be an étale morphism of algebraic spaces. Restriction of `𝒪_X`-modules along `a`
appears in two shapes: `AlgebraicGeometry.Space.etaleRestrictionModule`, which reads the
restricted sections as `𝒪_U`-modules through the identification `a⁻¹𝒪_X ≅ 𝒪_U` of Stacks 03LV
(`AlgebraicGeometry.Space.etaleRestrictionStructureSheafIso`), and
`AlgebraicGeometry.Space.etaleModulePullback`, which reads them through the definitional equality
of the sections of `𝒪_U` and of the restriction of `𝒪_X`. This file shows that the identification
of Stacks 03LV is the identity on sections, so the two shapes are the same functor, and hence
(Stacks Equation 03LW) étale restriction is the pullback `a^*` of modules.

## Main results

* `AlgebraicGeometry.Space.forget_map_etaleRestrictionStructureSheafIso_hom`: the
  identification `a⁻¹𝒪_X ≅ 𝒪_U` is the identity on underlying sheaves of sets.
* `AlgebraicGeometry.Space.etaleRestrictionModule_eq_etaleModulePullback`: the two restriction
  functors agree.
* `AlgebraicGeometry.Space.modulePullbackIsoEtaleRestrictionModule`: `a^* ≅` étale restriction.

## References

* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U X : AlgebraicSpaces B S hS} (a : U ⟶ X) (ha : IsEtale B S hS a.hom)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The identification `a⁻¹𝒪_X ≅ 𝒪_U` of Stacks 03LV is the identity on sections.** It is the
comparison of the inverse image with restriction followed by the inverse-image form of the
structure map, and on underlying sheaves of sets both are the comparison of Stacks 03LQ. -/
theorem forget_map_etaleRestrictionStructureSheafIso_hom :
    (sheafCompose (SmallEtale.topology B S hS U.1) (forget CommRingCat.{u})).map
        (etaleRestrictionStructureSheafIso B S hS a ha).hom = 𝟙 _ := by
  have h2 := forgetRing_fSharpInverseImage_eq_inverseImageIso B S hS a ha
  simp only [etaleRestrictionStructureSheafIso, Iso.trans_hom, Iso.symm_hom,
    Functor.map_comp, etaleInverseImageStructureSheafIso_hom]
  rw [← Functor.mapIso_inv]
  refine (Iso.inv_comp_eq _).2 ?_
  refine Eq.trans ?_ (Category.comp_id _).symm
  refine h2.trans ?_
  rw [Functor.mapIso_hom]
  have hr := inverseImageCommRingRestrictionIso_hom_forget (SmallEtale.topology B S hS U.1)
    (SmallEtale.topology B S hS X.1) (smallEtalePostcomp B S hS a ha)
    (smallEtaleRingedToposHom B S hS a).toToposHom
    (smallToposMorphismTypeU_inverseImageIso B S hS a ha) (smallEtaleRingedTopos B S hS X).O
  exact hr.symm

/-- The identification `a⁻¹𝒪_X ≅ 𝒪_U`, inverted and read on sheaves of rings, is the identity. -/
theorem forget₂_map_etaleRestrictionStructureSheafIso_inv :
    (sheafCompose (SmallEtale.topology B S hS U.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (etaleRestrictionStructureSheafIso B S hS a ha).inv = 𝟙 _ := by
  have h := forget_map_etaleRestrictionStructureSheafIso_hom B S hS a ha
  have hinv : (sheafCompose (SmallEtale.topology B S hS U.1) (forget CommRingCat.{u})).map
      (etaleRestrictionStructureSheafIso B S hS a ha).inv = 𝟙 _ := by
    have e := ((sheafCompose (SmallEtale.topology B S hS U.1) (forget CommRingCat.{u})).mapIso
      (etaleRestrictionStructureSheafIso B S hS a ha)).hom_inv_id
    rw [Functor.mapIso_hom, h, Functor.mapIso_inv] at e
    exact (Category.id_comp _).symm.trans e
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun V => ?_)
  apply RingCat.hom_ext
  refine RingHom.ext fun x => ?_
  exact congrFun (congrArg (fun φ => (φ.hom.app V : _ → _)) hinv) x

/-- **Étale restriction of modules, read through Stacks 03LV, is plain restriction of
sections.** -/
theorem etaleRestrictionModule_eq_etaleModulePullback :
    etaleRestrictionModule B S hS a ha = etaleModulePullback.{u, u} B S hS a ha := by
  unfold etaleRestrictionModule etaleModulePullback
  rw [forget₂_map_etaleRestrictionStructureSheafIso_inv]
  rfl

/-- **Stacks Equation 03LW for étale restriction of modules**: the pullback of modules along an
étale `a : U ⟶ X` is étale restriction. -/
def modulePullbackIsoEtaleRestrictionModule :
    modulePullback B S hS a ≅ etaleRestrictionModule B S hS a ha :=
  modulePullbackIsoEtaleModulePullback B S hS a ha ≪≫
    eqToIso (etaleRestrictionModule_eq_etaleModulePullback B S hS a ha).symm

end AlgebraicGeometry.Space

end
