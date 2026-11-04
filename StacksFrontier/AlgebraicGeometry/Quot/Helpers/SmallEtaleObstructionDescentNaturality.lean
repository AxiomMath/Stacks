module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.SmallEtaleThickeningTargetData
public import StacksFrontier.Deformation.ToposThickening.Helpers.ObstructionDescentBasePullback

/-!
# The descended obstruction classes along a factorization of small étale thickenings

For morphisms of algebraic spaces `f : X ⟶ Y`, `g : Y ⟶ Z`, `k : X ⟶ Z` with `f ≫ g = k` whose
morphisms of small étale ringed topoi are first order thickenings, those of `k` and `f` each
sitting in a strict square of Situation 08VV with flat right arrow, the class of Stacks 08VW, part
(1), across `f`, descended to `X`, is the descended class across `k` pushed forward along any map
`λ` of pulled-back ideals compatible with the map of square-zero ideals induced by `g`
(`AlgebraicGeometry.Space.extDescentAddEquiv_symm_existenceObstructionClass_smallEtale`).

This is `Deformation.ToposThickening.ThickeningTargetMorphism.`
`extDescentAddEquiv_symm_existenceObstructionClass_basePullbackIdeal` for the comparison
`Ψ₀ ∘ f_* ≅ k_*` built from `g_*f_* ≅ k_*` of Stacks 03G8, stated for variable algebraic spaces so
that it is elaborated once; the sheaf-theoretic instances of the small étale sites are recorded
first, since instance search reaches them through `AlgebraicGeometry.Space.smallEtaleRingedTopos`
only slowly.

## References

* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe e e' u vS uS wS vS' uS' wS' vT uT wT vT' uT' wT'

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The topology of the small étale ringed topos of `W` admits sheaf composition with the
forgetful functor of `RingCat`. -/
theorem smallEtaleRingedTopos_hasSheafCompose_forget_ringCat (W : AlgebraicSpaces B S hS) :
    (smallEtaleRingedTopos B S hS W).J.HasSheafCompose (forget RingCat.{u}) :=
  inferInstanceAs ((SmallEtale.topology B S hS W.1).HasSheafCompose (forget RingCat.{u}))

/-- The topology of the small étale ringed topos of `W` admits sheaf composition with the
forgetful functor from `CommRingCat` to `RingCat`. -/
theorem smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat (W : AlgebraicSpaces B S hS) :
    (smallEtaleRingedTopos B S hS W).J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) :=
  inferInstanceAs
    ((SmallEtale.topology B S hS W.1).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}))

/-- The topology of the small étale ringed topos of `W` admits sheaf composition with the
forgetful functor of `AddCommGrpCat`. -/
theorem smallEtaleRingedTopos_hasSheafCompose_forget_addCommGrpCat (W : AlgebraicSpaces B S hS) :
    (smallEtaleRingedTopos B S hS W).J.HasSheafCompose (forget AddCommGrpCat.{u}) :=
  inferInstanceAs ((SmallEtale.topology B S hS W.1).HasSheafCompose (forget AddCommGrpCat.{u}))

/-- The topology of the small étale ringed topos of `W` admits sheaf composition with the
forgetful functor of `CommRingCat`. -/
theorem smallEtaleRingedTopos_hasSheafCompose_forget_commRingCat (W : AlgebraicSpaces B S hS) :
    (smallEtaleRingedTopos B S hS W).J.HasSheafCompose (forget CommRingCat.{u}) :=
  inferInstanceAs ((SmallEtale.topology B S hS W.1).HasSheafCompose (forget CommRingCat.{u}))

/-- Presheaves of abelian groups on the small étale ringed topos of `W` admit a weak
sheafification. -/
theorem smallEtaleRingedTopos_hasWeakSheafify_addCommGrpCat (W : AlgebraicSpaces B S hS) :
    HasWeakSheafify (smallEtaleRingedTopos B S hS W).J AddCommGrpCat.{u} :=
  inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS W.1) AddCommGrpCat.{u})

/-- Presheaves of abelian groups on the small étale ringed topos of `W` admit a sheafification. -/
theorem smallEtaleRingedTopos_hasSheafify_addCommGrpCat (W : AlgebraicSpaces B S hS) :
    HasSheafify (smallEtaleRingedTopos B S hS W).J AddCommGrpCat.{u} :=
  inferInstanceAs (HasSheafify (SmallEtale.topology B S hS W.1) AddCommGrpCat.{u})

/-- On the small étale ringed topos of `W`, the morphisms of presheaves of abelian groups that
become isomorphisms after sheafification are exactly the locally bijective ones. -/
theorem smallEtaleRingedTopos_wEqualsLocallyBijective_addCommGrpCat (W : AlgebraicSpaces B S hS) :
    (smallEtaleRingedTopos B S hS W).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstanceAs ((SmallEtale.topology B S hS W.1).WEqualsLocallyBijective AddCommGrpCat.{u})

-- Local priority 10000: these searches through `smallEtaleRingedTopos` exceed the
-- heartbeat budget of the statement below otherwise.
attribute [local instance 10000] smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat
  smallEtaleRingedTopos_hasSheafCompose_forget_addCommGrpCat
  smallEtaleRingedTopos_hasSheafCompose_forget_commRingCat
  smallEtaleRingedTopos_hasWeakSheafify_addCommGrpCat
  smallEtaleRingedTopos_hasSheafify_addCommGrpCat
  smallEtaleRingedTopos_wEqualsLocallyBijective_addCommGrpCat

variable {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k)
  {S₁ : RingedTopos.{vS, uS, wS}} {S'₁ : RingedTopos.{vS', uS', wS'}}
  [S₁.J.HasSheafCompose (forget RingCat.{wS})] [S'₁.J.HasSheafCompose (forget RingCat.{wS'})]
  [S₁.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'₁.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [S₁.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'₁.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify S₁.J AddCommGrpCat.{wS}] [S₁.J.WEqualsLocallyBijective AddCommGrpCat.{wS}]
  {S₂ : RingedTopos.{vT, uT, wT}} {S'₂ : RingedTopos.{vT', uT', wT'}}
  [S₂.J.HasSheafCompose (forget RingCat.{wT})] [S'₂.J.HasSheafCompose (forget RingCat.{wT'})]
  [S₂.J.HasSheafCompose (forget₂ CommRingCat.{wT} RingCat.{wT})]
  [S'₂.J.HasSheafCompose (forget₂ CommRingCat.{wT'} RingCat.{wT'})]
  [S₂.J.HasSheafCompose (forget AddCommGrpCat.{wT})]
  [S'₂.J.HasSheafCompose (forget AddCommGrpCat.{wT'})]
  [HasWeakSheafify S₂.J AddCommGrpCat.{wT}] [S₂.J.WEqualsLocallyBijective AddCommGrpCat.{wT}]
  (hi₁ : FirstOrderThickening.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS k))
  (hi₂ : FirstOrderThickening.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS f))
  (hj : FirstOrderThickening.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS g))
  (t₁ : RingedToposHom S₁ S'₁) (f₁ : RingedToposHom (smallEtaleRingedTopos B S hS X) S₁)
  (f'₁ : RingedToposHom (smallEtaleRingedTopos B S hS Z) S'₁)
  (ht₁ : FirstOrderThickening t₁)
  (comm₁ : f'₁.comp (smallEtaleRingedToposHom B S hS k) = t₁.comp f₁) (hf'₁ : f'₁.IsFlat)
  (hstrict₁ : (MorphismOfThickenings.ofFirstOrderThickenings (smallEtaleRingedToposHom B S hS k)
    t₁ f₁ f'₁ hi₁ ht₁ comm₁).IsStrict)
  (t₂ : RingedToposHom S₂ S'₂) (f₂ : RingedToposHom (smallEtaleRingedTopos B S hS X) S₂)
  (f'₂ : RingedToposHom (smallEtaleRingedTopos B S hS Y) S'₂)
  (ht₂ : FirstOrderThickening t₂)
  (comm₂ : f'₂.comp (smallEtaleRingedToposHom B S hS f) = t₂.comp f₂) (hf'₂ : f'₂.IsFlat)
  (hstrict₂ : (MorphismOfThickenings.ofFirstOrderThickenings (smallEtaleRingedToposHom B S hS f)
    t₂ f₂ f'₂ hi₂ ht₂ comm₂).IsStrict)
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor
      (smallEtaleRingedToposHom B S hS k).toToposHom).obj (smallEtaleRingedTopos B S hS X).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor
      (smallEtaleRingedToposHom B S hS f).toToposHom).obj (smallEtaleRingedTopos B S hS X).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS Z).O))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS Y).O))]
  [HasExt.{e'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS X).O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS X).O))]

include hj in
/-- **The descended classes of Stacks 08VW, part (1), along `f ≫ g = k`.** -/
theorem extDescentAddEquiv_symm_existenceObstructionClass_smallEtale
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X).O))
    (lam : basePullbackIdeal t₁ f₁ ht₁ ⟶ basePullbackIdeal t₂ f₂ ht₂)
    (H : (smallEtaleThickeningTargetOfEq f g k hk).IdealSquareCompatible hi₁ hi₂ t₁ f₁ f'₁ ht₁
      comm₁ hf'₁ hstrict₁ t₂ f₂ f'₂ ht₂ comm₂ hf'₂ hstrict₂
      (smallEtaleThickenedModulesCompIso f g k hk) lam) :
    (extDescentAddEquiv.{u, u + 1, u, u + 1, u, e', e} hi₂ F (basePullbackIdeal t₂ f₂ ht₂)
        2).symm
        (existenceObstructionClass.{u, u + 1, u, u, u + 1, u, e} hi₂
          ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS f)).obj F) _
          (basePullbackIdealTensorIso (smallEtaleRingedToposHom B S hS f) t₂ f₂ f'₂ hi₂ ht₂ comm₂
            hf'₂ hstrict₂
            ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS f)).obj F)).inv) =
      ((extDescentAddEquiv.{u, u + 1, u, u + 1, u, e', e} hi₁ F (basePullbackIdeal t₁ f₁ ht₁)
          2).symm
        (existenceObstructionClass.{u, u + 1, u, u, u + 1, u, e} hi₁
          ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS k)).obj F) _
          (basePullbackIdealTensorIso (smallEtaleRingedToposHom B S hS k) t₁ f₁ f'₁ hi₁ ht₁ comm₁
            hf'₁ hstrict₁
            ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS k)).obj F)).inv)).comp
        (Abelian.Ext.mk₀ (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedTopos B S hS X).O).flip.obj F).map lam)) (add_zero 2) :=
  ThickeningTargetMorphism.extDescentAddEquiv_symm_existenceObstructionClass_basePullbackIdeal
    (D := smallEtaleThickeningTargetOfEq f g k hk) hi₁ hi₂ hj t₁ f₁ f'₁ ht₁ comm₁ hf'₁ hstrict₁
    t₂ f₂ f'₂ ht₂ comm₂ hf'₂ hstrict₂
    (smallEtaleThickenedModulesCompIso f g k hk) (smallEtaleThickeningTargetPushforwardIso f g k hk)
    (moduleSheafFunctor_map_smallEtaleThickenedModulesCompIso_hom_app f g k hk) F lam H

end AlgebraicGeometry.Space

end
