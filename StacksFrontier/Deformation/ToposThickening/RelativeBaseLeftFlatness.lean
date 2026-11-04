module

public import StacksFrontier.Deformation.ToposThickening.RelativeBaseSquare
public import StacksFrontier.Deformation.ToposThickening.FlatLiftBaseRingComparison
public import StacksFrontier.Deformation.ToposThickening.FlatPushforwardEquivalence
public import StacksFrontier.Deformation.ToposThickening.UniversalFirstOrder.ImageComposition
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget

/-!
# Flatness over the base of the relative square of Situation 08M7

In the relative square of `Deformation.ToposThickening.relBase_comm`, the morphism
`f̃ = (i, f̃^♯) : (Sh(C), O) ⟶ (Sh(D), f'⁻¹t_*O_ℬ)` replaces `p : (Sh(C), O) ⟶ (Sh(ℬ), O_ℬ)`. When
the comparison `θ : f'_*i_*O ≅ t_*p_*O` is the component of a natural isomorphism
`Θ : f'_* ∘ i_* ≅ t_* ∘ p_*` of direct images of sheaves of commutative rings, the two base rings
on `Sh(C)` agree: `i⁻¹f'⁻¹t_*O_ℬ ≅ p⁻¹t⁻¹t_*O_ℬ ≅ p⁻¹O_ℬ`, the first isomorphism conjugate to
`Θ`, the second the counit of `t⁻¹ ⊣ t_*`, invertible because `t` is a thickening. The
isomorphism is compatible with the two structure maps into `O`, so an `O`-module is flat over
`O_ℬ` along `p` exactly when it is flat over the base along `f̃`.

## Main definitions

* `Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompNatIso`: the comparison of iterated
  direct images of sheaves of commutative rings with the direct image along the composite, as a
  natural isomorphism.
* `Deformation.ToposThickening.relBaseLeftRingIso`: the isomorphism `i⁻¹f'⁻¹t_*O_ℬ ≅ p⁻¹O_ℬ`.

## Main results

* `CategoryTheory.Adjunction.conjugateEquiv_symm_app_comp_homEquiv_symm`: transposes along two
  adjunctions with isomorphic right adjoints differ by the conjugate isomorphism.
* `Deformation.ToposThickening.relBaseLeftRingIso_hom_comp`: the isomorphism is compatible with
  the structure maps.
* `Deformation.ToposThickening.isFlat_restrictScalars_relBaseLeft_iff`: flatness over the base
  along `f̃` is flatness along `p`.

## References

* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 0CZU](https://stacks.math.columbia.edu/tag/0CZU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/-- **Transposes along two adjunctions with isomorphic right adjoints differ by the conjugate
isomorphism.** For `L₁ ⊣ R₁`, `L₂ ⊣ R₂` and `Θ : R₁ ≅ R₂`, the transpose along the first
adjunction of `g ≫ Θ⁻¹`, preceded by the conjugate `L₂ ⟶ L₁` of `Θ`, is the transpose of `g`
along the second. -/
theorem CategoryTheory.Adjunction.conjugateEquiv_symm_app_comp_homEquiv_symm {C D : Type*}
    [Category C] [Category D] {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (Θ : R₁ ≅ R₂) {A : C} {B : D} (g : A ⟶ R₂.obj B) :
    ((conjugateEquiv adj₁ adj₂).symm Θ.hom).app A ≫ (adj₁.homEquiv A B).symm (g ≫ Θ.inv.app B) =
      (adj₂.homEquiv A B).symm g := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, ← Category.assoc,
    ← ((conjugateEquiv adj₁ adj₂).symm Θ.hom).naturality, Category.assoc,
    ← conjugateEquiv_counit_symm, ← Category.assoc, ← Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]

namespace Stacks.Sheaves.ToposPushforward

open Stacks.Sheaves.ToposPullback

attribute [local implicit_reducible] Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctor
  Stacks.Sheaves.ToposPullback.pullbackCommRingSheaf MorphismOfTopoi.comp

universe ww ww' ww'' vv uu vv' uu' vv'' uu''

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {E : Type uu''} [Category.{vv''} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [L.HasSheafCompose (forget RingCat.{ww''})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [L.HasSheafCompose (forget₂ CommRingCat.{ww''} RingCat.{ww''})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))
  (g : MorphismOfTopoi (Sheaf K (Type ww')) (Sheaf L (Type ww'')))

/-- **Stacks 01D3, the comparison in part (3), naturally in the sheaf.** The direct image of
sheaves of commutative rings along `f` and then along `g` is the direct image along `g ∘ f`. -/
noncomputable def pushforwardCommRingCompNatIso :
    pushforwardCommRingFunctor f ⋙ pushforwardCommRingFunctor g ≅
      pushforwardCommRingFunctor (g.comp f) :=
  NatIso.ofComponents (fun O ↦ pushforwardCommRingCompIso f g O)
    (fun a ↦ by
      refine (fullyFaithfulForgetCommRingSheaf L).map_injective ?_
      simp only [pushforwardCommRingCompIso, Functor.comp_map, Functor.map_comp,
        pullbackCommRingSheafFunctor_map, forgetCommRingSheaf_map_pullbackCommRingSheafMap,
        forgetCommRingSheaf_map_pullbackCommRingSheafCompIso_hom]
      refine Sheaf.hom_ext (NatTrans.ext (funext fun X ↦ ?_))
      exact RingCat.hom_ext (RingHom.ext fun x ↦ rfl))

/-- The components of `pushforwardCommRingCompNatIso` are the comparisons
`pushforwardCommRingCompIso`. -/
theorem pushforwardCommRingCompNatIso_app (O : Sheaf J CommRingCat.{ww}) :
    (pushforwardCommRingCompNatIso f g).app O = pushforwardCommRingCompIso f g O :=
  rfl

end Stacks.Sheaves.ToposPushforward

open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor inverseImageCommRingFunctor
  commRingImageAdjunction pushforwardCommRingFunctor_isEquivalence)
open Stacks.SheafOfModules.FlatSquareZero (ringMap)

universe v u w v' u' vS uS vS' uS'

namespace Deformation.ToposThickening

section RelativeBase

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, w}} {S' : RingedTopos.{vS', uS', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{w})] [S'.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {i : RingedToposHom X X'} {t : RingedToposHom S S'} {f' : RingedToposHom X' S'}
  {p : RingedToposHom X S}
  (Θ : pushforwardCommRingFunctor i.toToposHom ⋙ pushforwardCommRingFunctor f'.toToposHom ≅
    pushforwardCommRingFunctor p.toToposHom ⋙ pushforwardCommRingFunctor t.toToposHom)

/-- **The two base rings on the original topos agree: `i⁻¹f'⁻¹t_*O_ℬ ≅ p⁻¹O_ℬ`.** The first step
`i⁻¹f'⁻¹ ≅ p⁻¹t⁻¹` is conjugate to `Θ : f'_*i_* ≅ t_*p_*`; the second is the counit
`t⁻¹t_*O_ℬ ≅ O_ℬ`, invertible because the direct image of a first order thickening is an
equivalence. -/
noncomputable def relBaseLeftRingIso (ht : FirstOrderThickening t) :
    (inverseImageCommRingFunctor i.toToposHom).obj (inverseImageReducedBaseRing t f') ≅
      (inverseImageCommRingFunctor p.toToposHom).obj S.O :=
  haveI : (pushforwardCommRingFunctor t.toToposHom).IsEquivalence :=
    pushforwardCommRingFunctor_isEquivalence t.toToposHom ht.equiv
  (asIso (((conjugateEquiv ((commRingImageAdjunction f'.toToposHom).comp
      (commRingImageAdjunction i.toToposHom)) ((commRingImageAdjunction t.toToposHom).comp
        (commRingImageAdjunction p.toToposHom))).symm Θ.hom).app
          ((pushforwardCommRingFunctor t.toToposHom).obj S.O))).symm ≪≫
    (inverseImageCommRingFunctor p.toToposHom).mapIso
      (asIso ((commRingImageAdjunction t.toToposHom).counit.app S.O))

variable {θ : (pushforwardCommRingFunctor f'.toToposHom).obj
    ((pushforwardCommRingFunctor i.toToposHom).obj X.O) ≅
  (pushforwardCommRingFunctor t.toToposHom).obj
    ((pushforwardCommRingFunctor p.toToposHom).obj X.O)}

omit [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **The isomorphism `i⁻¹f'⁻¹t_*O_ℬ ≅ p⁻¹O_ℬ` is compatible with the structure maps**: followed
by `p^♯ : p⁻¹O_ℬ ⟶ O` it is the structure map `i⁻¹f'⁻¹t_*O_ℬ ⟶ O` of `f̃`, the transpose of
`Deformation.ToposThickening.relBaseLeftSharp`, when `θ` is the component of `Θ` at `O`. -/
theorem relBaseLeftRingIso_hom_comp (ht : FirstOrderThickening t)
    (hΘ : Θ.inv.app X.O = θ.inv) :
    (relBaseLeftRingIso Θ ht).hom ≫ p.fSharpInverseImage =
      ((commRingImageAdjunction i.toToposHom).homEquiv _ _).symm
        (relBaseLeftSharp i t f' p θ) := by
  have : (pushforwardCommRingFunctor t.toToposHom).IsEquivalence :=
    pushforwardCommRingFunctor_isEquivalence t.toToposHom ht.equiv
  have key := Adjunction.conjugateEquiv_symm_app_comp_homEquiv_symm
    ((commRingImageAdjunction f'.toToposHom).comp (commRingImageAdjunction i.toToposHom))
    ((commRingImageAdjunction t.toToposHom).comp (commRingImageAdjunction p.toToposHom)) Θ
    ((pushforwardCommRingFunctor t.toToposHom).map p.fSharp)
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv, hΘ] at key
  have h₂ : ((commRingImageAdjunction t.toToposHom).homEquiv _ _).symm
      ((pushforwardCommRingFunctor t.toToposHom).map p.fSharp) =
        (commRingImageAdjunction t.toToposHom).counit.app S.O ≫ p.fSharp := by
    rw [Adjunction.homEquiv_counit, Adjunction.counit_naturality]
  have h₃ : ((commRingImageAdjunction p.toToposHom).homEquiv _ _).symm
      ((commRingImageAdjunction t.toToposHom).counit.app S.O ≫ p.fSharp) =
        (inverseImageCommRingFunctor p.toToposHom).map
          ((commRingImageAdjunction t.toToposHom).counit.app S.O) ≫ p.fSharpInverseImage :=
    (commRingImageAdjunction p.toToposHom).homEquiv_naturality_left_symm _ _
  simp only [Equiv.symm_trans_apply, h₂] at key
  simp only [relBaseLeftRingIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom,
    asIso_hom, Category.assoc]
  rw [← h₃]
  refine Eq.trans (congrArg (CategoryStruct.comp _) key.symm) ?_
  exact IsIso.inv_hom_id_assoc _ _

omit [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The structure map of `f̃` in inverse-image form is the transpose of
`Deformation.ToposThickening.relBaseLeftSharp`. -/
theorem relBaseLeft_fSharpInverseImage :
    (relBaseLeft i t f' p θ).fSharpInverseImage =
      ((commRingImageAdjunction i.toToposHom).homEquiv _ _).symm
        (relBaseLeftSharp i t f' p θ) := by
  unfold RingedToposHom.fSharpInverseImage relBaseLeft
  rfl

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **Flatness over the base along `f̃` is flatness along `p`.** An `O`-module is flat over
`i⁻¹f'⁻¹t_*O_ℬ` exactly when it is flat over `p⁻¹O_ℬ`: the two structure maps into `O` differ by
the isomorphism `Deformation.ToposThickening.relBaseLeftRingIso`, and restriction of scalars along
an isomorphism preserves flatness. -/
theorem isFlat_restrictScalars_relBaseLeft_iff (ht : FirstOrderThickening t)
    (hΘ : Θ.inv.app X.O = θ.inv)
    (Q : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    AlgebraicGeometry.SheafOfModules.IsFlat
        ((SheafOfModules.restrictScalars
          ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
            (relBaseLeft i t f' p θ).fSharpInverseImage)).obj Q) ↔
      AlgebraicGeometry.SheafOfModules.IsFlat
        ((SheafOfModules.restrictScalars
          ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
            p.fSharpInverseImage)).obj Q) := by
  have hmap : (sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
        (relBaseLeft i t f' p θ).fSharpInverseImage =
      ringMap (relBaseLeftRingIso Θ ht).hom ≫
        (sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map p.fSharpInverseImage :=
    (congrArg (sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
      ((relBaseLeft_fSharpInverseImage (i := i) (t := t) (f' := f') (p := p) (θ := θ)).trans
        (relBaseLeftRingIso_hom_comp Θ ht hΘ).symm)).trans (Functor.map_comp _ _ _)
  have hiter : (SheafOfModules.restrictScalars (ringMap (relBaseLeftRingIso Θ ht).hom ≫
        (sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map p.fSharpInverseImage)).obj Q =
      (SheafOfModules.restrictScalars (ringMap (relBaseLeftRingIso Θ ht).hom)).obj
        ((SheafOfModules.restrictScalars
          ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
            p.fSharpInverseImage)).obj Q) :=
    congrArg (fun G => G.obj Q) (Stacks.Sheaves.RingedToposModules.restrictScalars_comp
      (ringMap (relBaseLeftRingIso Θ ht).hom)
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map p.fSharpInverseImage)).symm
  refine (Iff.of_eq (congrArg AlgebraicGeometry.SheafOfModules.IsFlat
    ((congrArg (fun m => (SheafOfModules.restrictScalars m).obj Q) hmap).trans hiter))).trans
      ⟨fun h => ?_, fun h => isFlat_restrictScalars_of_iso (relBaseLeftRingIso Θ ht) _ h⟩
  refine AlgebraicGeometry.SheafOfModules.isFlat_of_iso
    (Stacks.SheafOfModules.restrictScalarsSplitIso
      (ringMap (relBaseLeftRingIso Θ ht).inv) (ringMap (relBaseLeftRingIso Θ ht).hom) ?_ _)
    (isFlat_restrictScalars_of_iso (relBaseLeftRingIso Θ ht).symm _ h)
  exact ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map_comp _ _).symm.trans
    ((congrArg (sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
      (Iso.inv_hom_id _)).trans
        ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map_id _))

end RelativeBase

end Deformation.ToposThickening

end
