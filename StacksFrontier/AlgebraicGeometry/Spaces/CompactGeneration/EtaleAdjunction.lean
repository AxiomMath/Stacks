module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtalePullback
public import StacksFrontier.CategoryTheory.Triangulated.ExcisionGluing

/-!
# Étale restriction on `D_QCoh` and its right adjoint

For an étale, quasi-compact and quasi-separated morphism `f : X ⟶ Y` of algebraic spaces, the
adjunction `Lf^* ⊣ Rf_*` on `D_QCoh`
(`AlgebraicGeometry.Space.quasicoherentDerivedModuleAdjunction`) has the restricted étale
restriction functor as left adjoint, and for an étale monomorphism (an open immersion) its
counit is invertible. These are the restriction functors of the induction over elementary
distinguished squares of [Stacks, Tag 08GP].

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentDerivedModulePullbackIsoEtale`: for `f` étale, the
  restricted `Lf^*` is the restricted étale restriction.
* `AlgebraicGeometry.Space.quasicoherentDerivedEtaleAdjunction`: the adjunction with the
  restricted étale restriction as left adjoint.

## Main results

* `AlgebraicGeometry.Space.isIso_quasicoherentDerivedEtaleAdjunction_counit_of_mono`: for an
  étale monomorphism the counit `(Rj_* E)|_U ⟶ E` is invertible on `D_QCoh`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- The restricted étale restriction functor commutes with the shift. -/
instance commShift_quasicoherentDerivedEtalePullback (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (quasicoherentDerivedEtalePullback B S hS f hf).CommShift ℤ :=
  inferInstanceAs ((ObjectProperty.lift _ _ _).CommShift ℤ)

/-- The restricted étale restriction functor is triangulated. -/
instance isTriangulated_quasicoherentDerivedEtalePullback (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) : (quasicoherentDerivedEtalePullback B S hS f hf).IsTriangulated :=
  inferInstanceAs (ObjectProperty.lift _ _ _).IsTriangulated

/-- For an étale morphism the restricted derived pullback is the restricted étale restriction. -/
def quasicoherentDerivedModulePullbackIsoEtale (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    quasicoherentDerivedModulePullback f ≅ quasicoherentDerivedEtalePullback B S hS f hf :=
  (ObjectProperty.fullyFaithfulι _).whiskeringRight _ |>.preimageIso
    (quasicoherentDerivedModulePullbackCompιIso f ≪≫
      Functor.isoWhiskerLeft _ (smallEtaleDerivedModulePullbackIsoEtale B S hS f hf) ≪≫
      (quasicoherentDerivedEtalePullbackCompιIso B S hS f hf).symm)

/-- The adjunction `f^* ⊣ Rf_*` on `D_QCoh` for an étale, quasi-compact and quasi-separated
morphism, with the restricted étale restriction as left adjoint. -/
def quasicoherentDerivedEtaleAdjunction (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) :
    quasicoherentDerivedEtalePullback B S hS f hf ⊣
      quasicoherentDerivedPushforward B S hS f hfqc hfqs :=
  (quasicoherentDerivedModuleAdjunction B S hS f hfqc hfqs).ofNatIsoLeft
    (quasicoherentDerivedModulePullbackIsoEtale B S hS f hf)

/-- For an étale monomorphism `j` the restricted direct image `Rj_*` is fully faithful on
`D_QCoh`. -/
def quasicoherentDerivedPushforwardFullyFaithfulOfMono (j : X ⟶ Y) (hj : IsEtale B S hS j.hom)
    [Mono j] (hjqc : IsQuasiCompact B S hS j.hom) (hjqs : IsQuasiSeparated B S hS j.hom) :
    (quasicoherentDerivedPushforward B S hS j hjqc hjqs).FullyFaithful :=
  haveI := isIso_etaleDerivedModuleAdjunction_counit_of_mono B S hS j hj
  let hR := (etaleDerivedModuleAdjunction B S hS j hj).fullyFaithfulROfIsIsoCounit
  Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι _)
    ((ObjectProperty.fullyFaithfulι _).comp hR |>.ofIso
      (quasicoherentDerivedPushforwardCompιIso B S hS j hjqc hjqs).symm)

/-- The counit `(Rj_* E)|_U ⟶ E` is invertible on `D_QCoh` for an étale monomorphism `j`, that is
for an open immersion. -/
instance isIso_quasicoherentDerivedEtaleAdjunction_counit_of_mono (j : X ⟶ Y)
    (hj : IsEtale B S hS j.hom) [Mono j] (hjqc : IsQuasiCompact B S hS j.hom)
    (hjqs : IsQuasiSeparated B S hS j.hom) :
    IsIso (quasicoherentDerivedEtaleAdjunction B S hS j hj hjqc hjqs).counit :=
  haveI := (quasicoherentDerivedPushforwardFullyFaithfulOfMono B S hS j hj hjqc hjqs).full
  haveI := (quasicoherentDerivedPushforwardFullyFaithfulOfMono B S hS j hj hjqc hjqs).faithful
  inferInstance

/-- The counit of `f^* ⊣ Rf_*` on `D_QCoh` is invertible at an object `N` of `D_QCoh(𝒪_X)` at
which the counit of `AlgebraicGeometry.Space.etaleDerivedModuleAdjunction` is invertible. -/
theorem isIso_quasicoherentDerivedEtaleAdjunction_counit_app (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (N : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (h : IsIso ((etaleDerivedModuleAdjunction B S hS f hf).counit.app N.obj)) :
    IsIso ((quasicoherentDerivedEtaleAdjunction B S hS f hf hfqc hfqs).counit.app N) := by
  have h' := (Adjunction.isIso_counit_app_iff_bijective_map
    (etaleDerivedModuleAdjunction B S hS f hf) N.obj).1 h
  refine (Adjunction.isIso_counit_app_iff_bijective_map _ _).2 fun M => ?_
  let ι := (QcohDerived B S hS X).ι
  let ιY := (QcohDerived B S hS Y).ι
  let e := quasicoherentDerivedPushforwardCompιIso B S hS f hfqc hfqs
  have hcomm (g : N ⟶ M) : ιY.map ((quasicoherentDerivedPushforward B S hS f hfqc hfqs).map g) =
      e.hom.app N ≫ (derivedModulePushforward B S hS f).map (ι.map g) ≫ e.inv.app M := by
    simpa [ι, ιY] using e.hom.naturality g =≫ e.inv.app M
  have hconj : Function.Bijective (fun t : (derivedModulePushforward B S hS f).obj N.obj ⟶
      (derivedModulePushforward B S hS f).obj M.obj => e.hom.app N ≫ t ≫ e.inv.app M) :=
    ⟨fun t₁ t₂ ht => by simpa using congrArg (fun t => e.inv.app N ≫ t ≫ e.hom.app M) ht,
      fun t => ⟨e.inv.app N ≫ t ≫ e.hom.app M, by simp⟩⟩
  have hall : Function.Bijective (fun g : N ⟶ M =>
      ιY.map ((quasicoherentDerivedPushforward B S hS f hfqc hfqs).map g)) := by
    rw [show (fun g : N ⟶ M =>
        ιY.map ((quasicoherentDerivedPushforward B S hS f hfqc hfqs).map g)) =
        (fun t => e.hom.app N ≫ t ≫ e.inv.app M) ∘
          (fun g : N.obj ⟶ M.obj => (derivedModulePushforward B S hS f).map g) ∘
            (fun g : N ⟶ M => ι.map g) from funext hcomm]
    exact hconj.comp ((h' M.obj).comp ((ObjectProperty.fullyFaithfulι _).map_bijective N M))
  exact (Function.Bijective.of_comp_iff' ((ObjectProperty.fullyFaithfulι _).map_bijective _ _) _).1
    hall

end AlgebraicGeometry.Space

end
