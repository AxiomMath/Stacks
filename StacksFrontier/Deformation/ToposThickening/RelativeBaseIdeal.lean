module

public import StacksFrontier.Deformation.ToposThickening.RelativeBaseSquare
public import StacksFrontier.Deformation.ToposThickening.FlatLiftBaseRingComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseFactorisation

/-!
# The ideal of the thickened base, read on the thickened topos

In the relative square of `Deformation.ToposThickening.relBase_comm`, the thickening of the base
`t : (Sh(ℬ), O_ℬ) ⟶ (Sh(ℬ'), O_{ℬ'})` with square-zero ideal `𝒥` is replaced by the thickening
`t̃ = (id, f'⁻¹t^♯) : (Sh(D), f'⁻¹t_*O_ℬ) ⟶ (Sh(D), f'⁻¹O_{ℬ'})`, whose ideal `𝒥̃` is the kernel
of `f'⁻¹t^♯`. This file compares the two ideals after pulling them back to `(Sh(D), O')`:
`f̃'^*𝒥̃ ≅ f'^*𝒥`, where `f̃' = (id, f'^♯) : (Sh(D), O') ⟶ (Sh(D), f'⁻¹O_{ℬ'})`.

The morphism `f'` factors as `f̃'` followed by the projection
`(Sh(D), f'⁻¹O_{ℬ'}) ⟶ (Sh(ℬ'), O_{ℬ'})` whose structure map is the unit of `f'⁻¹ ⊣ f'_*`, so
`f'^* ≅ f̃'^* ∘ (projection)^*`. The pullback along the projection is the inverse image `f'⁻¹`,
its structure map being the identity of `f'⁻¹O_{ℬ'}`, and `f'⁻¹𝒥` is `𝒥̃`, both being the
submodules of `f'⁻¹O_{ℬ'}` whose sections are those killed by the reduction (the inverse image is
left exact).

## Main definitions

* `Deformation.ToposThickening.sectionwiseIsoOfRangeEq`: two sectionwise injective morphisms of
  sheaves of modules into a common target with the same sectionwise images have isomorphic
  sources.
* `Deformation.ToposThickening.relBaseProjection`: the projection
  `(Sh(D), f'⁻¹O_{ℬ'}) ⟶ (Sh(ℬ'), O_{ℬ'})`.
* `Deformation.ToposThickening.relBaseIdealIso`: `𝒥̃ ≅ f'⁻¹𝒥`.
* `Deformation.ToposThickening.relBasePullbackIdealIso`: `f̃'^*𝒥̃ ≅ f'^*𝒥`.

## References

* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 0CZU](https://stacks.math.columbia.edu/tag/0CZU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor inverseImageCommRingFunctor
  commRingImageAdjunction)
open Stacks.Sheaves.ToposPullback (pullbackCommRingSheafFunctorId)
open Stacks.Sheaves.RingedToposModules (inverseImageModules pullbackModuleObjRestrictScalarsIso
  fSharpSet fSharpSetComp pullbackModulesCompIso)

universe v' u' w vS uS vS' uS'

namespace Deformation.ToposThickening

section SectionwiseIso

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {M₁ M₂ N : SheafOfModules.{w} R} (ι₁ : M₁ ⟶ N) (ι₂ : M₂ ⟶ N)
  (h₁ : ∀ U, Function.Injective (ι₁.val.app U)) (h₂ : ∀ U, Function.Injective (ι₂.val.app U))
  (h : ∀ (U : Cᵒᵖ) (x : N.val.obj U), (∃ b, ι₁.val.app U b = x) ↔ (∃ b, ι₂.val.app U b = x))

/-- **Two submodules with the same sections are isomorphic.** Two sectionwise injective
morphisms of sheaves of modules into a common target, with the same image on every object,
have isomorphic sources, the isomorphism commuting with the two morphisms. -/
noncomputable def sectionwiseIsoOfRangeEq : M₁ ≅ M₂ where
  hom := (Stacks.SheafOfModules.existsUnique_factorThrough ι₂ h₂ ι₁
    fun U z => (h U _).1 ⟨z, rfl⟩).exists.choose
  inv := (Stacks.SheafOfModules.existsUnique_factorThrough ι₁ h₁ ι₂
    fun U z => (h U _).2 ⟨z, rfl⟩).exists.choose
  hom_inv_id := (Stacks.SheafOfModules.existsUnique_factorThrough ι₁ h₁ ι₁
      fun U z => ⟨z, rfl⟩).unique
    (by rw [Category.assoc, (Stacks.SheafOfModules.existsUnique_factorThrough ι₁ h₁ ι₂
        fun U z => (h U _).2 ⟨z, rfl⟩).exists.choose_spec,
      (Stacks.SheafOfModules.existsUnique_factorThrough ι₂ h₂ ι₁
        fun U z => (h U _).1 ⟨z, rfl⟩).exists.choose_spec])
    (Category.id_comp _)
  inv_hom_id := (Stacks.SheafOfModules.existsUnique_factorThrough ι₂ h₂ ι₂
      fun U z => ⟨z, rfl⟩).unique
    (by rw [Category.assoc, (Stacks.SheafOfModules.existsUnique_factorThrough ι₂ h₂ ι₁
        fun U z => (h U _).1 ⟨z, rfl⟩).exists.choose_spec,
      (Stacks.SheafOfModules.existsUnique_factorThrough ι₁ h₁ ι₂
        fun U z => (h U _).2 ⟨z, rfl⟩).exists.choose_spec])
    (Category.id_comp _)

/-- The isomorphism `Deformation.ToposThickening.sectionwiseIsoOfRangeEq` commutes with the two
morphisms into the common target. -/
theorem sectionwiseIsoOfRangeEq_hom_comp :
    (sectionwiseIsoOfRangeEq ι₁ ι₂ h₁ h₂ h).hom ≫ ι₂ = ι₁ :=
  (Stacks.SheafOfModules.existsUnique_factorThrough ι₂ h₂ ι₁
    fun U z => (h U _).1 ⟨z, rfl⟩).exists.choose_spec

end SectionwiseIso

section RelativeBase

variable {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, w}} {S' : RingedTopos.{vS', uS', w}}
  [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{w})] [S'.J.HasSheafCompose (forget RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (t : RingedToposHom S S') (f' : RingedToposHom X' S')

/-- **The projection `(Sh(D), f'⁻¹O_{ℬ'}) ⟶ (Sh(ℬ'), O_{ℬ'})`**: the morphism of topoi of `f'`,
with the unit `O_{ℬ'} ⟶ f'_*f'⁻¹O_{ℬ'}` as structure map. -/
noncomputable def relBaseProjection : RingedToposHom (relBaseTop f') S' where
  toToposHom := f'.toToposHom
  fSharp := (commRingImageAdjunction f'.toToposHom).unit.app S'.O

omit [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [S'.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The structure map of the projection, in inverse-image form, is the identity of
`f'⁻¹O_{ℬ'}`. -/
theorem relBaseProjection_fSharpInverseImage :
    (relBaseProjection f').fSharpInverseImage = 𝟙 _ :=
  ((commRingImageAdjunction f'.toToposHom).homEquiv_counit _ _ _).trans
    ((commRingImageAdjunction f'.toToposHom).left_triangle_components _)

variable [X'.J.HasSheafCompose (forget CommRingCat.{w})]

omit [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The comparison `id⁻¹ ≅ id` of sheaves of commutative rings is the identity on underlying
sheaves of sets, in the inverse direction. -/
theorem forget_map_pullbackCommRingSheafFunctorId_inv_app (O : Sheaf X'.J CommRingCat.{w}) :
    (sheafCompose X'.J (forget CommRingCat.{w})).map
        ((pullbackCommRingSheafFunctorId X'.J).inv.app O) =
      𝟙 ((sheafCompose X'.J (forget CommRingCat.{w})).obj O) :=
  (Category.id_comp _).symm.trans
    ((congrArg (· ≫ (sheafCompose X'.J (forget CommRingCat.{w})).map
      ((pullbackCommRingSheafFunctorId X'.J).inv.app O))
        (Stacks.Sheaves.ToposPullback.forget_map_pullbackCommRingSheafFunctorId_hom_app
          (J := X'.J) O).symm).trans
      (((sheafCompose X'.J (forget CommRingCat.{w})).map_comp _ _).symm.trans
        ((congrArg (sheafCompose X'.J (forget CommRingCat.{w})).map
          ((pullbackCommRingSheafFunctorId X'.J).hom_inv_id_app O)).trans
          ((sheafCompose X'.J (forget CommRingCat.{w})).map_id _))))

omit [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [S'.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **The structure maps of `f̃'` and of the projection compose to that of `f'`**, on underlying
sheaves of sets: the hypothesis of the comparison of pullbacks along the factorisation
`f' = (projection) ∘ f̃'`. -/
theorem relBase_fSharpSetComp :
    fSharpSetComp (relBaseRight f').toRingedToposModulesHom
        (relBaseProjection f').toRingedToposModulesHom ≫
        (Functor.leftUnitor f'.toToposHom.pushforward).hom.app
          (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) =
      fSharpSet f'.toRingedToposModulesHom := by
  have hψ := AlgebraicGeometry.RingedToposHom.ringFsharp_forget (relBaseProjection f')
  have hφ := AlgebraicGeometry.RingedToposHom.ringFsharp_forget (relBaseRight f')
  have hχ := AlgebraicGeometry.RingedToposHom.ringFsharp_forget f'
  have h1 : (commRingImageAdjunction f'.toToposHom).unit.app S'.O ≫
      (pushforwardCommRingFunctor f'.toToposHom).map f'.fSharpInverseImage = f'.fSharp :=
    ((commRingImageAdjunction f'.toToposHom).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  have h2 := forget_map_pushforward_map f'.toToposHom (relBaseRight f').fSharp
  have h3 := forget_map_pushforward_map f'.toToposHom
    ((pullbackCommRingSheafFunctorId X'.J).inv.app X'.O)
  have h4 := forget_map_pullbackCommRingSheafFunctorId_inv_app X'.O
  have e1 : fSharpSetComp (relBaseRight f').toRingedToposModulesHom
        (relBaseProjection f').toRingedToposModulesHom ≫
        (Functor.leftUnitor f'.toToposHom.pushforward).hom.app
          (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) =
      (sheafCompose S'.J (forget CommRingCat.{w})).map
          ((commRingImageAdjunction f'.toToposHom).unit.app S'.O) ≫
        f'.toToposHom.pushforward.map ((sheafCompose X'.J (forget CommRingCat.{w})).map
          (relBaseRight f').fSharp) :=
    (Category.comp_id _).trans (congrArg₂ (· ≫ ·) hψ (congrArg _ hφ))
  have e2 : (sheafCompose S'.J (forget CommRingCat.{w})).map
          ((commRingImageAdjunction f'.toToposHom).unit.app S'.O) ≫
        f'.toToposHom.pushforward.map ((sheafCompose X'.J (forget CommRingCat.{w})).map
          (relBaseRight f').fSharp) =
      (sheafCompose S'.J (forget CommRingCat.{w})).map
          (((commRingImageAdjunction f'.toToposHom).unit.app S'.O ≫
            (pushforwardCommRingFunctor f'.toToposHom).map f'.fSharpInverseImage) ≫
              (pushforwardCommRingFunctor f'.toToposHom).map
                ((pullbackCommRingSheafFunctorId X'.J).inv.app X'.O)) := by
    rw [Category.assoc, ← (pushforwardCommRingFunctor f'.toToposHom).map_comp, Functor.map_comp]
    exact congrArg _ h2.symm
  have e3 : (sheafCompose S'.J (forget CommRingCat.{w})).map
          (((commRingImageAdjunction f'.toToposHom).unit.app S'.O ≫
            (pushforwardCommRingFunctor f'.toToposHom).map f'.fSharpInverseImage) ≫
              (pushforwardCommRingFunctor f'.toToposHom).map
                ((pullbackCommRingSheafFunctorId X'.J).inv.app X'.O)) =
      (sheafCompose S'.J (forget CommRingCat.{w})).map f'.fSharp ≫
        f'.toToposHom.pushforward.map ((sheafCompose X'.J (forget CommRingCat.{w})).map
          ((pullbackCommRingSheafFunctorId X'.J).inv.app X'.O)) := by
    rw [h1, Functor.map_comp]
    exact congrArg _ h3
  have e4 : (sheafCompose S'.J (forget CommRingCat.{w})).map f'.fSharp ≫
        f'.toToposHom.pushforward.map ((sheafCompose X'.J (forget CommRingCat.{w})).map
          ((pullbackCommRingSheafFunctorId X'.J).inv.app X'.O)) =
      (sheafCompose S'.J (forget CommRingCat.{w})).map f'.fSharp :=
    (congrArg (_ ≫ ·) ((congrArg f'.toToposHom.pushforward.map h4).trans
      (f'.toToposHom.pushforward.map_id _))).trans (Category.comp_id _)
  exact e1.trans (e2.trans (e3.trans (e4.trans hχ.symm)))

variable [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **`f'^* ≅ f̃'^* ∘ (projection)^*`**: the comparison of pullbacks of sheaves of modules along
the factorisation of `f'` through `f̃'` and the projection (Stacks 03D6). -/
noncomputable def relBasePullbackCompIso :
    f'.toRingedToposModulesHom.pullbackModules ≅
      (relBaseProjection f').toRingedToposModulesHom.pullbackModules ⋙
        (relBaseRight f').toRingedToposModulesHom.pullbackModules :=
  pullbackModulesCompIso (relBaseRight f').toRingedToposModulesHom
    (relBaseProjection f').toRingedToposModulesHom f'.toRingedToposModulesHom
    (Functor.leftUnitor f'.toToposHom.pushforward) (relBase_fSharpSetComp f')

omit [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [S'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [X'.J.HasSheafCompose (forget CommRingCat.{w})] [HasWeakSheafify X'.J AddCommGrpCat.{w}]
    [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The structure map of the projection, at the level of sheaves of rings, is the identity. -/
theorem relBaseProjection_ringFsharpInverseImage :
    (relBaseProjection f').toRingedToposModulesHom.fSharpInverseImage = 𝟙 _ :=
  (congrArg (sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
    (relBaseProjection_fSharpInverseImage f')).trans (CategoryTheory.Functor.map_id _ _)

/-- The structure map of the projection, at the level of sheaves of rings, is an isomorphism. -/
instance isIso_relBaseProjection_fSharpInverseImage :
    IsIso (relBaseProjection f').toRingedToposModulesHom.fSharpInverseImage :=
  ⟨⟨𝟙 _, by rw [relBaseProjection_ringFsharpInverseImage]; exact Category.id_comp _,
    by rw [relBaseProjection_ringFsharpInverseImage]; exact Category.id_comp _⟩⟩

omit [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [S'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [X'.J.HasSheafCompose (forget CommRingCat.{w})] [HasWeakSheafify X'.J AddCommGrpCat.{w}]
    [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The inverse of the structure map of the projection is the identity. -/
theorem relBaseProjection_asIso_inv :
    (asIso (relBaseProjection f').toRingedToposModulesHom.fSharpInverseImage).inv = 𝟙 _ :=
  (Category.comp_id _).symm.trans ((congrArg
    ((asIso (relBaseProjection f').toRingedToposModulesHom.fSharpInverseImage).inv ≫ ·)
      (relBaseProjection_ringFsharpInverseImage f').symm).trans (Iso.inv_hom_id _))

/-- **The pullback along the projection is the inverse image `f'⁻¹`**: its structure map is the
identity of `f'⁻¹O_{ℬ'}`, so it extends scalars along an identity. -/
noncomputable def relBaseProjectionPullbackIso
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)) :
    (relBaseProjection f').toRingedToposModulesHom.pullbackModules.obj M ≅
      (inverseImageModules f'.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).obj M :=
  ((relBaseProjection f').toRingedToposModulesHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso).app
      ((inverseImageModules f'.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).obj M) ≪≫
    eqToIso (congrArg (fun m => (SheafOfModules.restrictScalars m).obj
      ((inverseImageModules f'.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).obj M))
      (relBaseProjection_asIso_inv f'))

omit [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [S'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [X'.J.HasSheafCompose (forget CommRingCat.{w})] [HasWeakSheafify X'.J AddCommGrpCat.{w}]
    [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **A section of `f'⁻¹O_{ℬ'}` is killed by `t̃^♯` exactly when it is killed by the
reduction** `f'⁻¹t^♯`: the two differ by the isomorphism `id⁻¹ ≅ id`. -/
theorem relBaseThickening_fSharp_eq_zero_iff (U : X'.Cᵒᵖ)
    (x : (inverseImageBaseRing f').obj.obj U) :
    (relBaseThickening t f').fSharp.hom.app U x = 0 ↔
      (inverseImageBaseReduction t f').hom.app U x = 0 := by
  constructor
  · intro ha
    have h := congrArg (((pullbackCommRingSheafFunctorId X'.J).hom.app
      (inverseImageReducedBaseRing t f')).hom.app U).hom ha
    exact (Sheaf.commRingIso_hom_inv_app_apply ((pullbackCommRingSheafFunctorId X'.J).app
      (inverseImageReducedBaseRing t f')) U _).symm.trans (h.trans (map_zero _))
  · intro ha
    show (((pullbackCommRingSheafFunctorId X'.J).inv.app
      (inverseImageReducedBaseRing t f')).hom.app U).hom
        (((inverseImageBaseReduction t f').hom.app U).hom x) = 0
    rw [ha, map_zero]

variable [HasSheafify X'.J AddCommGrpCat.{w}]

/-- **`𝒥̃ ≅ f'⁻¹𝒥`.** The ideal of the thickening `t̃` is the inverse image along `f'` of the ideal
of `t`, read as a module over `f'⁻¹O_{ℬ'}`: both are submodules of `f'⁻¹O_{ℬ'}` whose sections are
the sections killed by the reduction `f'⁻¹t^♯`. -/
noncomputable def relBaseIdealIso (ht : FirstOrderThickening t) :
    (relBaseThickeningFirstOrderThickening (f' := f') ht).idealOfThickening.I ≅
      (inverseImageModules f'.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).obj
        ht.idealOfThickening.I :=
  sectionwiseIsoOfRangeEq
      (relBaseThickeningFirstOrderThickening (f' := f') ht).idealOfThickening.incl
      (inverseImageBaseIdealIncl t f' ht)
      (relBaseThickeningFirstOrderThickening (f' := f') ht).idealOfThickening.injective
      (fun U a a' haa => by
        obtain ⟨c, -, huniq⟩ := existsUnique_inverseImageBaseIdeal_section t f' ht U _
          (inverseImageBaseReduction_inverseImageBaseIdealIncl t f' ht U a)
        exact (huniq a rfl).trans (huniq a' haa.symm).symm)
      (fun U x => by
        refine ((relBaseThickeningFirstOrderThickening (f' := f') ht).idealOfThickening.kernel U
          (show (relBaseTop f').O.obj.obj U from x)).symm.trans
          ((relBaseThickening_fSharp_eq_zero_iff t f' U x).trans ⟨fun hx => ?_, ?_⟩)
        · obtain ⟨c, hc, -⟩ := existsUnique_inverseImageBaseIdeal_section t f' ht U x hx
          exact ⟨c, hc⟩
        · rintro ⟨b, rfl⟩
          exact inverseImageBaseReduction_inverseImageBaseIdealIncl t f' ht U b) ≪≫
    eqToIso (congrArg (fun m ↦ (SheafOfModules.restrictScalars m).obj
      (inverseImageBaseIdeal t f' ht)) (ringMap_inverseImageBaseReduction t f')) ≪≫
    pullbackModuleObjRestrictScalarsIso X'.J f'.toToposHom.inverseImage
      ((Stacks.forgetCommRingSheaf S'.J).map t.fSharp) ht.I

/-- **`f̃'^*𝒥̃ ≅ f'^*𝒥`.** The pullback to `(Sh(D), O')` of the ideal of the thickening `t̃` along
`f̃'` is the pullback of the ideal of `t` along `f'`: `f'^* ≅ f̃'^* ∘ (projection)^*`, the pullback
along the projection is `f'⁻¹`, and `f'⁻¹𝒥 ≅ 𝒥̃`. -/
noncomputable def relBasePullbackIdealIso (ht : FirstOrderThickening t) :
    (relBaseRight f').toRingedToposModulesHom.pullbackModules.obj
        (relBaseThickeningFirstOrderThickening (f' := f') ht).idealOfThickening.I ≅
      f'.toRingedToposModulesHom.pullbackModules.obj ht.idealOfThickening.I :=
  (relBaseRight f').toRingedToposModulesHom.pullbackModules.mapIso
      (relBaseIdealIso t f' ht ≪≫ (relBaseProjectionPullbackIso f' ht.idealOfThickening.I).symm) ≪≫
    ((relBasePullbackCompIso f').app ht.idealOfThickening.I).symm

end RelativeBase

end Deformation.ToposThickening

end
