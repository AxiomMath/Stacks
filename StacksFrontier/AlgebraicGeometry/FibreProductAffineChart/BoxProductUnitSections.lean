module

public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.ComparisonSections
public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.BoxProductPureTensors

/-!
# Sections of a box product on an affine chart, attached to sections of the two factors

Let `a : X ⟶ S` and `b : Y ⟶ S`, let `F` and `G` be quasi-coherent modules on `X` and on `Y`, and
let `Spec (A ⊗_R B) ⟶ X ×_S Y` be an affine chart of the fibre product coming from open immersions
`Spec A ⟶ X` and `Spec B ⟶ Y` over `Spec R ⟶ S`. Global sections `x` of `F` and `y` of `G` give a
global section of `F ⊠ G` on the chart: the pure tensor of their pullbacks to `X ×_S Y`, pulled
back along the chart. The chart identifications carry this section to `s ⊗ t`, where `s` and `t`
are the pullbacks of `x` and `y` to `Spec A` and `Spec B`: a pure tensor of sections of `F` and of
`G` corresponds to a pure tensor of sections.

## Main definitions

* `Stacks.FibreProductAffineChart.chartBoxSection`: the global section of `F ⊠ G` on the chart
  attached to a pair of global sections of `F` and of `G`.

## Main results

* `Stacks.FibreProductAffineChart.tensorPullbackSectionsIso_hom_toTensorSheafSection`: the
  sections of a tensor product of two pullbacks on an affine scheme, on the section coming from a
  pure tensor of two pullback-unit images.
* `Stacks.FibreProductAffineChart.chartPullbackExternalTensorIso_hom_chartBoxSection`: the
  sheaf-level chart identification on `chartBoxSection`.
* `Stacks.FibreProductAffineChart.chartExternalTensorSectionsIso_hom_chartBoxSection`: the
  sections of `F ⊠ G` on the chart attached to `x` and `y` correspond to `(1 ⊗ s) ⊗ (1 ⊗ t)`.
* `Stacks.FibreProductAffineChart.chartExternalTensorSectionsBaseIso_hom_chartBoxSection`: over
  the base ring they correspond to `s ⊗ t` in `Γ(Spec A, F) ⊗_R Γ(Spec B, G)`.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry CommRingCat RingHomClass
open Stacks.Tag01VSPullbackTensor
open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace Stacks.FibreProductAffineChart

universe u

/-- The action on elements of a composite of two isomorphisms of modules: if the first carries `m`
to `n` and the second carries `n` to `p`, the composite carries `m` to `p`. -/
theorem moduleIsoTrans_apply {R : Type u} [Ring R] {M N P : ModuleCat.{u} R} (e₁ : M ≅ N)
    (e₂ : N ≅ P) {m : M} {n : N} {p : P} (h₁ : e₁.hom m = n) (h₂ : e₂.hom n = p) :
    (e₁ ≪≫ e₂).hom m = p := by
  subst h₁ h₂; rfl

/-- Restriction of scalars does not change the underlying function of an isomorphism. -/
theorem restrictScalars_mapIso_hom_apply {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    {M N : ModuleCat.{u} S} (e : M ≅ N) (m : (ModuleCat.restrictScalars f).obj M) :
    ((ModuleCat.restrictScalars f).mapIso e).hom m = e.hom m := rfl

/-- An isomorphism of modules on `Spec R` acts on global sections by its component over `⊤`. -/
theorem moduleSpecΓFunctor_mapIso_hom_apply {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (e : M ≅ N) (s : moduleSpecΓFunctor.obj M) :
    (moduleSpecΓFunctor.mapIso e).hom s = Scheme.Modules.Hom.app e.hom ⊤ s := rfl

/-! ### Sections of a tensor product of two pullbacks on an affine scheme -/

open scoped ChangeOfRings in
/-- **Sections of a tensor product of two pullbacks on pure tensors.** The identification of the
global sections on `Spec T` of `(Spec φ) ^* P ⊗ (Spec ψ) ^* Q` with the tensor product over `T` of
the two base-changed modules of sections carries the section coming from the pure tensor of the
pullbacks of `s` and of `t` to `(1 ⊗ s) ⊗ (1 ⊗ t)`. -/
theorem tensorPullbackSectionsIso_hom_toTensorSheafSection {A' B' T : CommRingCat.{u}}
    (φ : A' ⟶ T) (ψ : B' ⟶ T) (P : (Spec A').Modules) (Q : (Spec B').Modules)
    [P.IsQuasicoherent] [Q.IsQuasicoherent] (s : moduleSpecΓFunctor.obj P)
    (t : moduleSpecΓFunctor.obj Q) :
    (tensorPullbackSectionsIso φ ψ P Q).hom
        (toTensorSheafSection (Spec T).toRingedSpace
          ((Scheme.Modules.pullback (Spec.map φ)).obj P)
          ((Scheme.Modules.pullback (Spec.map ψ)).obj Q) (Opposite.op ⊤)
          (modulesPullbackUnit (Spec.map φ) P ⊤ s ⊗ₜ modulesPullbackUnit (Spec.map ψ) Q ⊤ t))
      = (((1 : T) ⊗ₜ[A', φ.hom] s) ⊗ₜ[T] ((1 : T) ⊗ₜ[B', ψ.hom] t) :
          ↑(MonoidalCategory.tensorObj
            ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj P))
            ((ModuleCat.extendScalars ψ.hom).obj (moduleSpecΓFunctor.obj Q)))) := by
  have unit_inv : ∀ {A'' : CommRingCat.{u}} (χ : A'' ⟶ T) (M : (Spec A'').Modules)
      [M.IsQuasicoherent] (m : moduleSpecΓFunctor.obj M),
      (quasicoherentPullbackSectionsIso A'' T χ M).inv (modulesPullbackUnit (Spec.map χ) M ⊤ m) =
        (1 : T) ⊗ₜ[A'', χ.hom] m := fun χ M _ m =>
    (congrArg (fun z => (quasicoherentPullbackSectionsIso _ T χ M).inv z)
      (quasicoherentPullbackSectionsIso_hom_one_tmul _ T χ M m).symm).trans
        (Iso.hom_inv_id_apply _ _)
  have key := (TildeTensor.gammaTensorEquiv ((Scheme.Modules.pullback (Spec.map φ)).obj P)
      ((Scheme.Modules.pullback (Spec.map ψ)).obj Q)).symm_apply_apply
    (modulesPullbackUnit (Spec.map φ) P ⊤ s ⊗ₜ[T] modulesPullbackUnit (Spec.map ψ) Q ⊤ t)
  exact (congrArg (fun z => (MonoidalCategory.tensorIso
        (quasicoherentPullbackSectionsIso A' T φ P).symm
        (quasicoherentPullbackSectionsIso B' T ψ Q).symm).hom z) key).trans
    (congrArg₂ (fun (z : (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj P))
        (w : (ModuleCat.extendScalars ψ.hom).obj (moduleSpecΓFunctor.obj Q)) => z ⊗ₜ[T] w)
      (unit_inv φ P s) (unit_inv ψ Q t))

/-! ### The section of a box product attached to a pair of sections -/

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
  (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (u : Spec (.of A) ⟶ X) (v : Spec (.of B) ⟶ Y) (w : Spec (.of R) ⟶ S)
  (hu : Spec.map (ofHom (algebraMap R A)) ≫ w = u ≫ a)
  (hv : Spec.map (ofHom (algebraMap R B)) ≫ w = v ≫ b)
  (F : X.Modules) (G : Y.Modules)

/-- The global section of `F ⊠ G` on an affine chart of `X ×_S Y` attached to global sections `x`
of `F` and `y` of `G`: the section of `F ⊠ G` coming from the pure tensor of the pullbacks of `x`
and `y` to `X ×_S Y`, pulled back along the chart. -/
def chartBoxSection (x : Γ(F, ⊤)) (y : Γ(G, ⊤)) :
    Γ((Scheme.Modules.pullback (affineChart a b R A B u v w hu hv)).obj
        (externalTensorProduct a b F G), ⊤) :=
  modulesPullbackUnit (affineChart a b R A B u v w hu hv) (externalTensorProduct a b F G) ⊤
    (toTensorSheafSection (pullback a b).toRingedSpace
      ((Scheme.Modules.pullback (pullback.fst a b)).obj F)
      ((Scheme.Modules.pullback (pullback.snd a b)).obj G) (Opposite.op ⊤)
      (modulesPullbackUnit (pullback.fst a b) F ⊤ x ⊗ₜ
        modulesPullbackUnit (pullback.snd a b) G ⊤ y))

/-- **The pullback of a box product along an affine chart on a box section.** The identification of
the pullback of `F ⊠ G` along the chart with the tensor product of the two base changes carries
`Stacks.FibreProductAffineChart.chartBoxSection` to the section coming from the pure tensor of the
pullbacks of `x` to `Spec (A ⊗_R B)` through `Spec A`, and of `y` through `Spec B`. -/
theorem chartPullbackExternalTensorIso_hom_chartBoxSection (x : Γ(F, ⊤)) (y : Γ(G, ⊤)) :
    Scheme.Modules.Hom.app (chartPullbackExternalTensorIso a b R A B u v w hu hv F G).hom ⊤
        (chartBoxSection a b R A B u v w hu hv F G x y)
      = toTensorSheafSection (Spec (CommRingCat.of (A ⊗[R] B))).toRingedSpace
          ((Scheme.Modules.pullback (Spec.map (chartInclLeft R A B))).obj
            ((Scheme.Modules.pullback u).obj F))
          ((Scheme.Modules.pullback (Spec.map (chartInclRight R A B))).obj
            ((Scheme.Modules.pullback v).obj G)) (Opposite.op ⊤)
          (modulesPullbackUnit (Spec.map (chartInclLeft R A B))
              ((Scheme.Modules.pullback u).obj F) ⊤ (modulesPullbackUnit u F ⊤ x) ⊗ₜ
            modulesPullbackUnit (Spec.map (chartInclRight R A B))
              ((Scheme.Modules.pullback v).obj G) ⊤ (modulesPullbackUnit v G ⊤ y)) := by
  have step1 := modulesPullbackUnit_pullbackCongr_hom_top
    (lift_affineChart a b R A B u v w hu hv).symm (externalTensorProduct a b F G)
    (toTensorSheafSection (pullback a b).toRingedSpace
      ((Scheme.Modules.pullback (pullback.fst a b)).obj F)
      ((Scheme.Modules.pullback (pullback.snd a b)).obj G) (Opposite.op ⊤)
      (modulesPullbackUnit (pullback.fst a b) F ⊤ x ⊗ₜ
        modulesPullbackUnit (pullback.snd a b) G ⊤ y))
  have step2 := pullbackLift_externalTensorProductIso_hom_modulesPullbackUnit a b
    (affineChart a b R A B u v w hu hv ≫ pullback.fst a b)
    (affineChart a b R A B u v w hu hv ≫ pullback.snd a b)
    (affineChart_comp_comm a b R A B u v w hu hv) F G x y
  have step3 := tensorSheafMapIso_hom_toTensorSheafSection
    (pullbackCompCongrIso (Spec.map (chartInclLeft R A B)) u
      (affineChart_fst a b R A B u v w hu hv).symm F).symm
    (pullbackCompCongrIso (Spec.map (chartInclRight R A B)) v
      (affineChart_snd a b R A B u v w hu hv).symm G).symm (⊤ : (Spec (.of (A ⊗[R] B))).Opens)
    (modulesPullbackUnit (affineChart a b R A B u v w hu hv ≫ pullback.fst a b) F ⊤ x)
    (modulesPullbackUnit (affineChart a b R A B u v w hu hv ≫ pullback.snd a b) G ⊤ y)
  have step4a := modulesPullbackUnit_pullbackCompCongrIso_inv_top
    (Spec.map (chartInclLeft R A B)) u (affineChart_fst a b R A B u v w hu hv).symm F x
  have step4b := modulesPullbackUnit_pullbackCompCongrIso_inv_top
    (Spec.map (chartInclRight R A B)) v (affineChart_snd a b R A B u v w hu hv).symm G y
  exact modulesHomApp_trans _ _ ⊤ step1 (modulesHomApp_trans _ _ ⊤ step2 (step3.trans
    (congrArg₂ (fun z wz => toTensorSheafSection _ _ _ (Opposite.op ⊤) (z ⊗ₜ wz)) step4a step4b)))

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open scoped ChangeOfRings in
/-- **Sections of a box product on an affine chart, on a box section.** The module of sections of
`F ⊠ G` on the chart, identified with the tensor product over `A ⊗_R B` of the two base changes,
matches `Stacks.FibreProductAffineChart.chartBoxSection` with `(1 ⊗ s) ⊗ (1 ⊗ t)`, where `s` and
`t` are the pullbacks of `x` to `Spec A` and of `y` to `Spec B`. -/
theorem chartExternalTensorSectionsIso_hom_chartBoxSection [F.IsQuasicoherent]
    [G.IsQuasicoherent] (x : Γ(F, ⊤)) (y : Γ(G, ⊤)) :
    (chartExternalTensorSectionsIso a b R A B u v w hu hv F G).hom
        (chartBoxSection a b R A B u v w hu hv F G x y)
      = ((((1 : A ⊗[R] B) ⊗ₜ[A, algebraMap A (A ⊗[R] B)] modulesPullbackUnit u F ⊤ x)
            ⊗ₜ[CommRingCat.of (A ⊗[R] B)]
            ((1 : A ⊗[R] B) ⊗ₜ[B, algebraMap B (A ⊗[R] B)] modulesPullbackUnit v G ⊤ y)) :
          ↑(MonoidalCategory.tensorObj
            ((ModuleCat.extendScalars (chartInclLeft R A B).hom).obj
              (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback u).obj F)))
            ((ModuleCat.extendScalars (chartInclRight R A B).hom).obj
              (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback v).obj G))))) :=
  moduleIsoTrans_apply _ _
    ((moduleSpecΓFunctor_mapIso_hom_apply
        (chartPullbackExternalTensorIso a b R A B u v w hu hv F G)
        (chartBoxSection a b R A B u v w hu hv F G x y)).trans
      (chartPullbackExternalTensorIso_hom_chartBoxSection a b R A B u v w hu hv F G x y))
    (tensorPullbackSectionsIso_hom_toTensorSheafSection (chartInclLeft R A B)
      (chartInclRight R A B) ((Scheme.Modules.pullback u).obj F)
      ((Scheme.Modules.pullback v).obj G) (modulesPullbackUnit u F ⊤ x)
      (modulesPullbackUnit v G ⊤ y))

/-- **Sections of a box product on an affine chart over the base ring, on a box section.** The
module of sections of `F ⊠ G` on the chart, identified as a module over `R` with
`Γ(Spec A, F) ⊗_R Γ(Spec B, G)`, matches the section attached to global sections `x` of `F` and `y`
of `G` with the pure tensor `s ⊗ t` of their pullbacks to `Spec A` and to `Spec B`. -/
theorem chartExternalTensorSectionsBaseIso_hom_chartBoxSection [F.IsQuasicoherent]
    [G.IsQuasicoherent] (x : Γ(F, ⊤)) (y : Γ(G, ⊤)) :
    (chartExternalTensorSectionsBaseIso a b R A B u v w hu hv F G).hom
        (chartBoxSection a b R A B u v w hu hv F G x y)
      = (modulesPullbackUnit u F ⊤ x ⊗ₜ[R] modulesPullbackUnit v G ⊤ y :
          ↑(MonoidalCategory.tensorObj
            ((ModuleCat.restrictScalars (algebraMap R A)).obj
              (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback u).obj F)))
            ((ModuleCat.restrictScalars (algebraMap R B)).obj
              (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback v).obj G))))) :=
  moduleIsoTrans_apply _ _
    ((restrictScalars_mapIso_hom_apply (algebraMap R (A ⊗[R] B))
        (chartExternalTensorSectionsIso a b R A B u v w hu hv F G)
        (chartBoxSection a b R A B u v w hu hv F G x y)).trans
      (chartExternalTensorSectionsIso_hom_chartBoxSection a b R A B u v w hu hv F G x y))
    (Stacks.TensorProductPushout.extendScalarsCancelIso_hom_one_tmul R A B
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback u).obj F))
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback v).obj G))
      (modulesPullbackUnit u F ⊤ x) (modulesPullbackUnit v G ⊤ y))

/-! ### Definitional identities on bare isomorphism variables -/

/-- The action on elements of a composite of two linear equivalences: if the first carries `m` to
`n` and the second carries `n` to `p`, the composite carries `m` to `p`. -/
theorem linearEquivTrans_apply {R M N P : Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] [Module R P]
    (e₁ : M ≃ₗ[R] N) (e₂ : N ≃ₗ[R] P) {m : M} {n : N} {p : P} (h₁ : e₁ m = n)
    (h₂ : e₂ n = p) : e₁.trans e₂ m = p := by
  subst h₁ h₂; rfl

/-- An isomorphism of modules read as a linear equivalence acts on elements by its underlying
morphism. -/
theorem isoToLinearEquiv_apply {R : CommRingCat.{u}} {M N : ModuleCat.{u} R} (e : M ≅ N)
    {m : M} {n : N} (h : e.hom m = n) : e.toLinearEquiv m = n := h

/-- A natural isomorphism of functors into the modules on `Spec R` acts on global sections by the
component of its underlying natural transformation. -/
theorem moduleSpecΓFunctor_mapIso_app_hom_apply {R : CommRingCat.{u}} {C : Type*} [Category C]
    {Φ Ψ : C ⥤ (Spec R).Modules} (e : Φ ≅ Ψ) (M : C)
    (s : moduleSpecΓFunctor.obj (Φ.obj M)) :
    (moduleSpecΓFunctor.mapIso (e.app M)).hom s =
      Scheme.Modules.Hom.app (e.hom.app M) ⊤ s := rfl

/-- The tensor product of two isomorphisms of modules, on a pure tensor. -/
theorem moduleTensorIso_hom_tmul {R : Type u} [CommRing R] {M M' N N' : ModuleCat.{u} R}
    (e : M ≅ M') (e' : N ≅ N') {m : M} {n : N} {m' : M'} {n' : N'}
    (hm : e.hom m = m') (hn : e'.hom n = n') :
    (MonoidalCategory.tensorIso e e').hom (m ⊗ₜ[R] n) = m' ⊗ₜ[R] n' := by
  subst hm hn; rfl

end Stacks.FibreProductAffineChart

end
