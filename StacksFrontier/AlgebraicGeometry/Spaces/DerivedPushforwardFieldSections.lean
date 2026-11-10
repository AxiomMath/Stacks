module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardSingleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldSpectrumGlobalSectionsExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardGlobalSectionsLinear
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomologyUniverseLift
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerCharacteristic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.SectionUniverseLift

/-!
# The derived direct image to the spectrum of a field computes cohomology

Let `k` be a field, let `X` be an algebraic space and let `f : X ⟶ Spec k` be a morphism of
algebraic spaces.  For every `𝒪_X`-module `𝓜` and every `n`, the global sections over `Spec k`
of the `n`-th cohomology sheaf of the derived direct image of `𝓜` are the `n`-th cohomology of
`𝓜` on `X`:

`Γ(Spec k, Hⁿ(Rf_*(𝓜[0]))) ≅ Hⁿ(X, 𝓜)`

as `k`-vector spaces.

## Main results

* `isPullbackSection_globalSectionsRingHom`: the action of the functions on `Spec k` on `X`
  through `f` is by pullback.
* `globalSectionsHomologyDerivedModulePushforwardFieldIso`:
  `Γ(Spec k, Hⁿ(Rf_*(𝓜[0]))) ≅ Hⁿ(X, 𝓜)` as modules over any ring `A` mapping to `Γ(Spec k)`,
  the right hand side in the form of `eulerCharacteristicAlong`.
* `finrank_globalSectionsHomologyDerivedModulePushforward_eq`: the dimensions over `k` agree.
* `CoherentObject.finrank_globalSectionsHomologyDerivedFibrePushforward_eq`: the same on the
  fibre `X_t ⟶ Spec κ(t)` of an object of `Coh_{X/B}`, with the action of `κ(t)` of
  `CoherentObject.twistedEuler`.

## References

* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
* [Stacks Project, Tag 0D1W](https://stacks.math.columbia.edu/tag/0D1W)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives
attribute [local instance] isGrothendieckAbelian_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (V : BigFppfOver B S hS) {X : AlgebraicSpaces B S hS}

/-- **The functions on `V` act on `X` through `f : X ⟶ V` by pullback**: the image of a
function on `V` in the global functions of `X` is the pullback of its image in the global
functions of the algebraic space represented by `V`. -/
theorem isPullbackSection_globalSectionsRingHom (f : X ⟶ schemeSpace V)
    (a : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj V))) :
    IsPullbackSection B S hS f (globalSectionsRingHom B S hS X.1 X.2 f.hom a)
      (globalSectionsRingHom B S hS (schemeSpace V).1 (schemeSpace V).2 (𝟙 _) a) := by
  intro W j
  have hcomm : chartBaseChangeMap B S hS f W j ≫ chartToScheme B S hS (schemeSpace V).1 (𝟙 _) W =
      chartToScheme B S hS X.1 f.hom j.right.unop := by
    apply yoneda.map_injective
    rw [Functor.map_comp]
    simp only [chartToScheme, Functor.FullyFaithful.map_preimage]
    exact (chartDiagramOfIndex B S hS f W j).comm.symm
  change (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (chartToScheme B S hS X.1 f.hom j.right.unop)).op).hom a =
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS f W j)).op).hom
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (chartToScheme B S hS (schemeSpace V).1 (𝟙 _) W)).op).hom a)
  rw [← hcomm, Functor.map_comp, op_comp, Functor.map_comp]
  rfl

variable {V}

/-- **`Γ(Spec k, Hⁿ(Rf_*(𝓜[0]))) ≅ Hⁿ(X, 𝓜)`**, for a morphism `f : X ⟶ Spec k` of algebraic
spaces to the spectrum of a field and an `𝒪_X`-module `𝓜`, as modules over any ring `A`
acting on `Spec k` through `ψ : A ⟶ Γ(Spec k, 𝒪)`.  The left hand side is a module over the
global functions on `Spec k`, the right hand side, the cohomology of the universe lift of `𝓜`
as in `AlgebraicGeometry.Space.eulerCharacteristicAlong`, a module over the global functions on
`X`; both are read over `A` through the pullback of functions. -/
def globalSectionsHomologyDerivedModulePushforwardFieldIso (K : Type u) [Field K]
    (e : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of K)) {A : Type*} [Ring A]
    (ψ : A →+* Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj V)))
    (f : X ⟶ schemeSpace V) (M : Modules.{u, u} B S hS X.1 X.2) (n : ℕ) :
    (ModuleCat.restrictScalars
        ((globalSectionsRingHom B S hS (schemeSpace V).1 (schemeSpace V).2 (𝟙 _)).comp ψ)).obj
      ((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS (schemeSpace V).1 (schemeSpace V).2).O)).obj
        ((DerivedCategory.homologyFunctor
            (Modules.{u, u} B S hS (schemeSpace V).1 (schemeSpace V).2) n).obj
          ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
            ((DerivedCategory.singleFunctor _ 0).obj M)))) ≅
      (ModuleCat.restrictScalars ((globalSectionsRingHom B S hS X.1 X.2 f.hom).comp ψ)).obj
        ((globalModuleCohomology.{u + 1, u, u, u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) n).obj
          (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} M)) :=
  have := hasSeparator_modules B S hS X.1 X.2
  have := site_hasSheafify_addCommGrp.{u + 1, u, u + 1}
    (J := (smallEtaleRingedSite B S hS X.1 X.2).J)
  have := site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, u + 1}
    (J := (smallEtaleRingedSite B S hS X.1 X.2).J)
  have := moduleSheavesEnoughInjectives.{u + 1, u, u, u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  (ModuleCat.restrictScalars
      ((globalSectionsRingHom B S hS (schemeSpace V).1 (schemeSpace V).2 (𝟙 _)).comp ψ)).mapIso
    (globalSectionsHomologyDerivedModulePushforwardSingleIso B S hS f M
      (acyclicHigherDirectImages_of_field e f M) n) ≪≫
  rightDerivedGlobalSectionsModulePushforwardIsoOfIsPullbackSection B S hS f _ _
    (fun c => isPullbackSection_globalSectionsRingHom B S hS V f (ψ c)) M n ≪≫
  let N := ((globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived
      n).obj M
  let eU : (ModuleCat.uliftFunctor.{u + 1} _).obj N ≃ₗ[_] N := ULift.moduleEquiv
  (ModuleCat.restrictScalars ((globalSectionsRingHom B S hS X.1 X.2 f.hom).comp ψ)).mapIso
    (eU.toModuleIso.symm ≪≫
      (rightDerivedGlobalSectionsUliftIso.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
          n).app M)

/-- **The dimension over `k` of `Γ(Spec k, Hⁿ(Rf_*(𝓜[0])))` is that of `Hⁿ(X, 𝓜)`**, for a
morphism `f : X ⟶ Spec k` of algebraic spaces, the right hand side read as in
`AlgebraicGeometry.Space.eulerCharacteristicAlong` along the ring map `k ⟶ Γ(X, 𝒪_X)` of `f`. -/
theorem finrank_globalSectionsHomologyDerivedModulePushforward_eq (K : Type u) [Field K]
    (e : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of K)) {A : Type*} [Field A]
    (ψ : A →+* Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj V)))
    (f : X ⟶ schemeSpace V) (M : Modules.{u, u} B S hS X.1 X.2) (n : ℕ) :
    Module.finrank A ((ModuleCat.restrictScalars
        ((globalSectionsRingHom B S hS (schemeSpace V).1 (schemeSpace V).2 (𝟙 _)).comp ψ)).obj
      ((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS (schemeSpace V).1 (schemeSpace V).2).O)).obj
        ((DerivedCategory.homologyFunctor
            (Modules.{u, u} B S hS (schemeSpace V).1 (schemeSpace V).2) n).obj
          ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
            ((DerivedCategory.singleFunctor _ 0).obj M))))) =
      Module.finrank A ((ModuleCat.restrictScalars
          ((globalSectionsRingHom B S hS X.1 X.2 f.hom).comp ψ)).obj
        ((globalModuleCohomology.{u + 1, u, u, u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) n).obj
          (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} M))) :=
  LinearEquiv.finrank_eq
    (globalSectionsHomologyDerivedModulePushforwardFieldIso B S hS K e ψ f M n).toLinearEquiv

namespace CoherentObject

variable {B S hS} {D : CoherentSituation B S hS}

/-- **On the fibre of a coherent family, `Γ(Spec κ(t), Hⁿ(Rf_{t,*}(𝓜[0])))` has the dimension of
`Hⁿ(X_t, 𝓜)`** over `κ(t)`, for the projection `f_t : X_t ⟶ Spec κ(t)` of the fibre and any
`𝒪_{X_t}`-module `𝓜`, the right hand side read along
`AlgebraicGeometry.Space.CoherentObject.fibreFieldHom` as in
`AlgebraicGeometry.Space.CoherentObject.twistedEuler`. -/
theorem finrank_globalSectionsHomologyDerivedFibrePushforward_eq (A : CoherentObject D)
    (t : A.testScheme)
    (M : Modules.{u, u} B S hS (A.fibreSpace t).1 (A.fibreSpace t).2) (n : ℕ) :
    Module.finrank (A.testScheme.residueField t) ((ModuleCat.restrictScalars
        ((globalSectionsRingHom B S hS (schemeSpace (A.pointScheme t)).1
          (schemeSpace (A.pointScheme t)).2 (𝟙 _)).comp
          (Scheme.ΓSpecIso (.of (A.testScheme.residueField t))).inv.hom)).obj
      ((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
            (schemeSpace (A.pointScheme t)).1 (schemeSpace (A.pointScheme t)).2).O)).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS
            (schemeSpace (A.pointScheme t)).1 (schemeSpace (A.pointScheme t)).2) n).obj
          ((Stacks.DerivedFunctor.totalRightDerived
              (modulePushforward B S hS (D.projection (A.pointTest t)))).obj
            ((DerivedCategory.singleFunctor _ 0).obj M))))) =
      Module.finrank (A.testScheme.residueField t)
        ((ModuleCat.restrictScalars (A.fibreFieldHom t)).obj
          ((globalModuleCohomology.{u + 1, u, u, u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS (A.fibreSpace t).1 (A.fibreSpace t).2).O) n).obj
            (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} M))) :=
  finrank_globalSectionsHomologyDerivedModulePushforward_eq B S hS (V := A.pointScheme t)
    (X := A.fibreSpace t) (A.testScheme.residueField t)
    (Iso.refl (Spec (.of (A.testScheme.residueField t))))
    (Scheme.ΓSpecIso (.of (A.testScheme.residueField t))).inv.hom
    (D.projection (A.pointTest t)) M n

end CoherentObject

end AlgebraicGeometry.Space
