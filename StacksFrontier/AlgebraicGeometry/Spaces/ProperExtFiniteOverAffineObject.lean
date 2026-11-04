module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperExtFiniteComplexes
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperModuleCohomologyFiniteAffine

/-!
# Finite Ext groups on an algebraic space proper over an affine Noetherian object

Let `S` be a scheme, `V` an object of the big fppf site of `S` whose scheme is affine and locally
Noetherian, and `f : X ⟶ V` a proper morphism of algebraic spaces over `S`.  The ring
`Γ(V, 𝒪_V)` acts on every `𝒪_X`-module through the functions `f^♯ x` it pulls back to `X`
(`AlgebraicGeometry.Space.pullbackToGlobalFunctions`).  This file proves that for this action

* the cohomology `Hⁱ(X, 𝓕)` of a coherent `𝒪_X`-module is a finite `Γ(V, 𝒪_V)`-module
  (Stacks 08AS over the affine object `V` rather than over the base `S = Spec A` of the site);
* for `K ∈ D⁻_Coh(𝒪_X)` and `L ∈ D⁺_Coh(𝒪_X)` the groups `Hom_{D(𝒪_X)}(K, L[n])` are finite
  `Γ(V, 𝒪_V)`-modules (Stacks 0D0T over `V`).

The case `V = Spec A` the base of the site is
`AlgebraicGeometry.Space.moduleFinite_cohomology_of_isProper` and
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper`; the proofs below are those
proofs, with the action of `A` through the base of the site replaced by an arbitrary ring
homomorphism `ψ : R →+* Γ(X, 𝒪_X)` along which the cohomology of coherent modules is finite.

## Main results

* `AlgebraicGeometry.Space.moduleFinite_cohomology_of_isProper_toAffineObject`: `Hⁱ(X, 𝓕)` is a
  finite `Γ(V, 𝒪_V)`-module.
* `AlgebraicGeometry.Space.moduleFinite_hom_shift_of_hasFiniteCoherentCohomologyOver`: on a
  Noetherian algebraic space, finiteness of the cohomology of coherent modules over a Noetherian
  ring `R` acting through `ψ` gives finiteness of `Hom_{D(𝒪_X)}(K, L[n])` over `R`.
* `AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper_toAffineObject`: the two together,
  for `X` proper over `V`.

## References

* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 0D0T](https://stacks.math.columbia.edu/tag/0D0T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite Abelian
open Stacks.Cohomology.SiteModules

universe w u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The functions of an affine object, on its identity chart -/

section Chart

variable (V : BigFppfOver B S hS)

/-- The pullback of functions along a morphism `f : X ⟶ V` to an object of the site, as a ring
homomorphism into the global sections of the structure sheaf of the small étale ringed site
of `X`. -/
abbrev objectRingHom {X : AlgebraicSpaces B S hS}
    (f : X ⟶ (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS)) :
    Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+* GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) :=
  pullbackToGlobalFunctions B S hS X V f

end Chart

/-! ### Stacks 08AS over an affine object -/

section Cohomology

variable (V : BigFppfOver B S hS) {X : AlgebraicSpaces B S hS}

/-- The global sections of an `𝒪_X`-module, read as a `Γ(V, 𝒪_V)`-module through `f`. -/
abbrev globalSectionsOverObject (f : X ⟶ (schemeSpace V : AlgebraicSpaces B S hS)) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ ModuleCat.{u + 1} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  globalSectionsFunctor.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) ⋙
    ModuleCat.restrictScalars (objectRingHom V f)

/-- The sections over the identity chart of `V` of the direct image along `f : X ⟶ V`, read as
a `Γ(V, 𝒪_V)`-module and lifted to the universe of global sections. -/
abbrev pushforwardSectionsOverObject (f : X ⟶ (schemeSpace V : AlgebraicSpaces B S hS)) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ ModuleCat.{u + 1} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  (modulePushforward B S hS f ⋙
    SheafOfModules.evaluation.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)).O))
      (op (idEtaleChart B S hS V))) ⋙
    (ModuleCat.restrictScalars.{u} (idChartRingHom B V) ⋙
      ModuleCat.uliftFunctor.{u + 1} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))

/-- **The global sections of an `𝒪_X`-module are the sections of its direct image over `V`**,
`Γ(V, 𝒪_V)`-linearly, for a morphism `f : X ⟶ V`. -/
def globalSectionsLinearEquivPushforwardSectionsOverObject
    (f : X ⟶ (schemeSpace V : AlgebraicSpaces B S hS))
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (globalSectionsOverObject V f).obj M ≃ₗ[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
      (pushforwardSectionsOverObject V f).obj M where
  toEquiv := globalSectionsEquivPushforwardSections V f M
  map_add' s t := by
    have h := (((globalSectionsModulePushforwardIso B S hS f).app M).inv.hom).map_add s t
    exact congrArg ULift.up (congrArg (fun z : ((modulePushforward B S hS f).obj
      M).sections => z.eval (op (idEtaleChart B S hS V))) h)
  map_smul' a s := by
    have hs : (a • s : (globalSectionsOverObject V f).obj M) =
        SheafOfModules.sectionsMap (globalSmul _ (objectRingHom V f a) M) s :=
      Subtype.ext (funext fun _ => rfl)
    refine (congrArg (globalSectionsEquivPushforwardSections V f M) hs).trans ?_
    refine (globalSectionsEquivPushforwardSections_sectionsMap V f _ s).trans ?_
    have key := (congrArg (fun g => (modulePushforward B S hS f).map
        (globalSmul (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O) (pullbackToGlobalFunctions B S hS X V g a) M))
        (Category.comp_id f).symm).trans
      (modulePushforward_map_globalSmul_pullbackToGlobalFunctions B S hS f (𝟙 _) M a)
    exact congrArg (fun φ : (modulePushforward B S hS f).obj M ⟶
        (modulePushforward B S hS f).obj M =>
      (ULift.up ((φ.val.app (op (idEtaleChart B S hS V))).hom
        ((globalSectionsEquivPushforwardSections V f M) s).down) : ULift.{u + 1} _)) key

/-- `AlgebraicGeometry.Space.globalSectionsLinearEquivPushforwardSectionsOverObject`, natural in
the module. -/
def globalSectionsOverObjectIso (f : X ⟶ (schemeSpace V : AlgebraicSpaces B S hS)) :
    globalSectionsOverObject V f ≅ pushforwardSectionsOverObject V f :=
  NatIso.ofComponents
    (fun M => (globalSectionsLinearEquivPushforwardSectionsOverObject V f M).toModuleIso)
    (fun {M M'} φ => by
      ext s
      exact globalSectionsEquivPushforwardSections_sectionsMap V f φ s)

/-- Restriction of scalars along a ring homomorphism preserves homology. -/
private theorem preservesHomology_restrictScalars {R₁ : Type*} {R₂ : Type*} [Ring R₁] [Ring R₂]
    (φ : R₁ →+* R₂) : (ModuleCat.restrictScalars.{w} φ).PreservesHomology := by
  have : PreservesFiniteLimits (ModuleCat.restrictScalars.{w} φ) :=
    ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have : PreservesFiniteColimits (ModuleCat.restrictScalars.{w} φ) :=
    ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  exact Functor.preservesHomologyOfExact _

attribute [local instance] hasInjectiveResolutions_modules in
/-- **Stacks 08AS over an affine Noetherian object.**  Let `V` be an object of the big fppf site
whose scheme is affine and locally Noetherian, `f : X ⟶ V` a proper morphism of algebraic spaces
and `𝓕` a coherent `𝒪_X`-module.  Then `Hⁱ(X, 𝓕)` is a finite `Γ(V, 𝒪_V)`-module for every
`i ≥ 0`, the functions on `V` acting through `f`. -/
theorem moduleFinite_cohomology_of_isProper_toAffineObject
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    (f : X ⟶ (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS))
    (hf : IsProper B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) (i : ℕ) :
    Module.Finite Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      ((ModuleCat.restrictScalars (objectRingHom V f)).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i).obj F)) := by
  have hfin := hasFiniteCohomologyOver_of_isProper B S hS V hV f hf F hF i
  have := modulePushforward_additive B S hS f
  let O := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj V)
    (isAlgebraicSpace_yoneda B S hS V)).O)
  have : (SheafOfModules.evaluation.{u} O (op (idEtaleChart B S hS V))).Additive :=
    ⟨fun {_ _ _ _} => rfl⟩
  have := preservesHomology_restrictScalars.{u + 1} (objectRingHom V f)
  let E := ModuleCat.restrictScalars.{u} (idChartRingHom B V) ⋙
    ModuleCat.uliftFunctor.{u + 1} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
  have := preservesHomology_restrictScalars.{u} (idChartRingHom B V)
  have : E.PreservesHomology := inferInstance
  let Q := modulePushforward B S hS f ⋙
    SheafOfModules.evaluation.{u} O (op (idEtaleChart B S hS V))
  let Γ := globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  have e₁ := (Functor.rightDerivedCompIso Γ
    (ModuleCat.restrictScalars.{u + 1} (objectRingHom V f)) i).app F
  have e₂ := (Functor.rightDerivedIsoOfNatIso
    (F := Γ ⋙ ModuleCat.restrictScalars.{u + 1} (objectRingHom V f))
    (G := Q ⋙ E) (globalSectionsOverObjectIso V f) i).app F
  have e₃ := (Functor.rightDerivedCompIso Q E i).app F
  have h₁ : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      ((ModuleCat.restrictScalars.{u} (idChartRingHom B V)).obj ((Q.rightDerived i).obj F)) := by
    let l : ((ModuleCat.restrictScalars.{u} (idChartRingHom B V)).obj
        ((Q.rightDerived i).obj F)) →ₛₗ[idChartRingHom B V] ((Q.rightDerived i).obj F) :=
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have : RingHomSurjective (idChartRingHom B V) := ⟨(bijective_idChartRingHom B V).2⟩
    exact (l.finite_iff_of_bijective Function.bijective_id).2 hfin
  have h₂ : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      ((Q.rightDerived i ⋙ E).obj F) :=
    Module.Finite.equiv ULift.moduleEquiv.symm
  have h₃ : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (((Q ⋙ E).rightDerived i).obj F) :=
    Module.Finite.equiv e₃.symm.toLinearEquiv
  have h₄ : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (((Γ ⋙ ModuleCat.restrictScalars.{u + 1}
        (objectRingHom V f)).rightDerived i).obj F) :=
    Module.Finite.equiv e₂.symm.toLinearEquiv
  exact Module.Finite.equiv e₁.toLinearEquiv

end Cohomology

/-! ### Ext out of the structure sheaf, for an arbitrary action -/

section ExtUnit

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B S hS) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
  {R : Type u} [CommRing R]
  (ψ : R →+* GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))

/-- The `𝒪`-modules on the small étale site of an algebraic space, at the universe of the
structure rings, have enough injectives. -/
local instance (priority := 5000) enoughInjectives_modules_extObj :
    EnoughInjectives (Modules.{u, u} B S hS X hX) :=
  enoughInjectives_modules B S hS X hX

/-- **Morphisms out of the structure sheaf are global sections**, `R`-linearly, for the
`R`-linear structure induced by `ψ`. -/
def unitHomLinearEquivOf (M : Modules.{u, u} B S hS X hX) :
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) ψ
    ((linearCoyoneda R (Modules.{u, u} B S hS X hX)).obj
        (op (SheafOfModules.unit _))).obj M ≃ₗ[R]
      (ModuleCat.restrictScalars ψ).obj
        ((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X hX).O)).obj M) :=
  letI := Stacks.SheafOfModules.linearOver
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) ψ
  { toFun := fun φ => M.unitHomEquiv φ
    invFun := fun s => M.unitHomEquiv.symm s
    left_inv := M.unitHomEquiv.left_inv
    right_inv := M.unitHomEquiv.right_inv
    map_add' := fun φ ψ => by
      apply Subtype.ext
      funext U
      rfl
    map_smul' := fun a φ => by
      apply Subtype.ext
      funext U
      change (globalSmul _ (ψ a) _ ≫ φ).val.app U
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X hX).O).obj.obj U) =
        (ψ a).1 U • φ.val.app U
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X hX).O).obj.obj U)
      change φ.val.app U ((ψ a).1 U •
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X hX).O).obj.obj U)) =
        (ψ a).1 U • φ.val.app U
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X hX).O).obj.obj U)
      let φ' : SheafOfModules.unit _ ⟶ M := φ
      exact (φ'.val.app U).hom.map_smul _ _ }

/-- Morphisms out of the structure sheaf are global sections, `R`-linearly and naturally in the
target. -/
def linearCoyonedaUnitIsoOf :
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) ψ
    (linearCoyoneda R (Modules.{u, u} B S hS X hX)).obj
        (op (SheafOfModules.unit _)) ≅
      globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) ⋙
        ModuleCat.restrictScalars ψ :=
  letI := Stacks.SheafOfModules.linearOver
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) ψ
  NatIso.ofComponents (fun M => (unitHomLinearEquivOf B S hS X hX ψ M).toModuleIso)
    (fun _ => rfl)

/-- Finiteness over `R`, through `ψ`, of the cohomology of every coherent `𝒪_X`-module. -/
def HasFiniteCoherentCohomologyOver : Prop :=
  have := hasInjectiveResolutions_modules B S hS X hX
  ∀ (F : Modules.{u, u} B S hS X hX), IsCoherent B S hS X hX F → ∀ n : ℕ,
    Module.Finite R ((ModuleCat.restrictScalars ψ).obj
      (((globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).rightDerived
          n).obj F))

attribute [local instance] hasInjectiveResolutions_modules in
/-- **`Ext^n(𝒪_X, F)` is a finite `R`-module** for a coherent `F`, as soon as the cohomology of
coherent modules is finite over `R` acting through `ψ`: it is an `R`-linear quotient of the
degree-`n` cohomology of `Γ(X, I^•)` for an injective resolution `I^•` of `F`. -/
theorem moduleFinite_ext_unit_of_hasFiniteCoherentCohomologyOver
    (hfin : HasFiniteCoherentCohomologyOver B S hS X hX ψ)
    (F : Modules.{u, u} B S hS X hX) (hF : IsCoherent B S hS X hX F)
    [HasExt.{u + 1} (Modules.{u, u} B S hS X hX)] (n : ℕ) :
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) ψ
    Module.Finite R (Ext (SheafOfModules.unit _) F n) := by
  let := Stacks.SheafOfModules.linearOver
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) ψ
  let I := injectiveResolution F
  refine I.moduleFinite_ext_of_moduleFinite_homology n ?_
  let Γ := globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)
  let res := ModuleCat.restrictScalars.{u + 1} ψ
  have : res.PreservesHomology := preservesHomology_restrictScalars.{u + 1} ψ
  have h₀ := hfin F hF n
  have e₁ := (Functor.rightDerivedCompIso Γ res n).app F
  have e₂ := I.isoRightDerivedObj (Γ ⋙ res) n
  have e₃ := HomologicalComplex.homologyMapIso
    ((NatIso.mapHomologicalComplex (linearCoyonedaUnitIsoOf B S hS X hX ψ) _).app I.cocomplex) n
  have h₁ : Module.Finite R (((Γ ⋙ res).rightDerived n).obj F) :=
    @Module.Finite.equiv _ _ _ _ _ _ _ _ h₀ e₁.symm.toLinearEquiv
  have h₂ : Module.Finite R ((((Γ ⋙ res).mapHomologicalComplex _).obj I.cocomplex).homology n) :=
    Module.Finite.equiv e₂.toLinearEquiv
  exact Module.Finite.equiv e₃.symm.toLinearEquiv

section Hypercohomology

attribute [local instance] isGrothendieckAbelian_modules

variable [HasDerivedCategory.{w} (Modules.{u, u} B S hS X hX)]

/-- A morphism of the derived category inducing an isomorphism on `q`-th homology identifies
the coherence of the two `q`-th homology modules. -/
private theorem isCoherent_homology_iff_of_isIso_homologyMap
    {K L : DerivedCategory (Modules.{u, u} B S hS X hX)} (g : K ⟶ L) (q : ℤ)
    [IsIso ((DerivedCategory.homologyFunctor _ q).map g)] :
    IsCoherent B S hS X hX ((DerivedCategory.homologyFunctor _ q).obj K) ↔
      IsCoherent B S hS X hX ((DerivedCategory.homologyFunctor _ q).obj L) :=
  ⟨isCoherent_of_iso B S hS hX (asIso ((DerivedCategory.homologyFunctor _ q).map g)),
    isCoherent_of_iso B S hS hX (asIso ((DerivedCategory.homologyFunctor _ q).map g)).symm⟩

/-- Morphisms from a `≤ a` object to a `≥ b` object of the derived category vanish for `a < b`. -/
private theorem subsingleton_hom_of_isLE_of_isGE {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory.{w} C] {K L : DerivedCategory C} {a b : ℤ} [K.IsLE a] [L.IsGE b]
    (h : a < b) : Subsingleton (K ⟶ L) :=
  ⟨fun x y => (DerivedCategory.TStructure.t.zero x a b h).trans
    (DerivedCategory.TStructure.t.zero y a b h).symm⟩

/-- **The groups `Hom_{D(𝒪_X)}(𝒪_X, F[n])` are finite `R`-modules** for a coherent `F`, given
finiteness of the cohomology of coherent modules over `R`: for `n ≥ 0` this is
`Ext^n(𝒪_X, F)`, and for `n < 0` it vanishes. -/
theorem moduleFinite_hom_unit_singleFunctor_of_hasFiniteCoherentCohomologyOver
    [IsNoetherianRing R] (hfin : HasFiniteCoherentCohomologyOver B S hS X hX ψ)
    (F : Modules.{u, u} B S hS X hX) (hF : IsCoherent B S hS X hX F) (a : ℤ) :
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) ψ
    Module.Finite R ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X hX) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X hX).O)) ⟶
      (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X hX) a).obj F) := by
  let := Stacks.SheafOfModules.linearOver
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) ψ
  by_cases ha : a ≤ 0
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -a := ⟨(-a).toNat, by omega⟩
    have : HasExt.{u + 1} (Modules.{u, u} B S hS X hX) :=
      HasExt.standard (Modules.{u, u} B S hS X hX)
    have := moduleFinite_ext_unit_of_hasFiniteCoherentCohomologyOver B S hS X hX ψ hfin F hF m
    have e := Ext.homLinearEquiv (R := R) (X := SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))
      (Y := F) (n := m)
    have e' : ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X hX) 0).obj F)⟦(m : ℤ)⟧ ≅
        (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X hX) a).obj F :=
      ((DerivedCategory.singleFunctors (Modules.{u, u} B S hS X hX)).shiftIso (m : ℤ) a 0
        (by omega)).app F
    exact Module.Finite.equiv (e.trans (Linear.homCongr R (Iso.refl
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X hX) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X hX).O)))) e'))
  · have := subsingleton_hom_of_isLE_of_isGE.{w} (a := 0) (b := a) (by omega)
      (K := (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X hX) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X hX).O)))
      (L := (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X hX) a).obj F)
    infer_instance

/-- **The hypercohomology `Hom_{D(𝒪_X)}(𝒪_X, M[n])` of an object `M` with coherent cohomology
concentrated in degrees `[c, c + k]` is a finite `R`-module**, given finiteness of the cohomology
of coherent modules over `R`, by induction on `k` along the truncation triangles. -/
theorem moduleFinite_hom_unit_shift_of_isGE_of_isLE_of_hasFiniteCoherentCohomologyOver
    [IsNoetherianRing R] (hfin : HasFiniteCoherentCohomologyOver B S hS X hX ψ) (k : ℕ)
    (M : DerivedCategory (Modules.{u, u} B S hS X hX)) (c : ℤ) (hGE : M.IsGE c)
    (hLE : M.IsLE (c + k))
    (hq : ∀ q : ℤ, IsCoherent B S hS X hX ((DerivedCategory.homologyFunctor _ q).obj M))
    (n : ℤ) :
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) ψ
    Module.Finite R ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X hX) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X hX).O)) ⟶ M⟦n⟧) := by
  let := Stacks.SheafOfModules.linearOver
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) ψ
  let O := (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X hX) 0).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X hX).O))
  induction k generalizing M c n with
  | zero =>
    have : M.IsLE c := by simpa using hLE
    obtain ⟨F, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE M c
    have hF : IsCoherent B S hS X hX F :=
      isCoherent_of_iso B S hS hX ((DerivedCategory.homologyFunctor _ c).mapIso e ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ c).app F) (hq c)
    have := moduleFinite_hom_unit_singleFunctor_of_hasFiniteCoherentCohomologyOver
      B S hS X hX ψ hfin F hF (c - n)
    have e' : M⟦n⟧ ≅ (DerivedCategory.singleFunctor
        (Modules.{u, u} B S hS X hX) (c - n)).obj F :=
      (shiftFunctor _ n).mapIso e ≪≫ ((DerivedCategory.singleFunctors
        (Modules.{u, u} B S hS X hX)).shiftIso n (c - n) c (by omega)).app F
    exact Module.Finite.equiv (Linear.homCongr R (Iso.refl O) e').symm
  | succ k ih =>
    rw [show c + ((k + 1 : ℕ) : ℤ) = c + (k : ℤ) + 1 by push_cast; ring] at hLE
    set d := c + (k : ℤ) + 1 with hd
    have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished d M
    have := hGE
    have := hLE
    refine Pretriangulated.moduleFinite_hom_obj₂_of_distinguished O _
      (Pretriangulated.Triangle.shift_distinguished _ hT n) ?_ ?_
    · refine ih _ c inferInstance
        (DerivedCategory.TStructure.t.isLE_truncLT_obj M d (c + (k : ℤ)) (by omega))
        (fun q => ?_) n
      by_cases hqd : q < d
      · have : IsIso ((DerivedCategory.homologyFunctor _ q).map
            ((DerivedCategory.TStructure.t.truncLTι d).app M)) :=
          DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃ _ hT q d inferInstance hqd
        exact (isCoherent_homology_iff_of_isIso_homologyMap B S hS X hX
          ((DerivedCategory.TStructure.t.truncLTι d).app M) q).2 (hq q)
      · exact ObjectProperty.prop_of_isZero (isCoherent.{u, u} B S hS X hX)
          (DerivedCategory.isZero_of_isLE _ (d - 1) q (by omega))
    · refine ih _ d inferInstance
        (DerivedCategory.TStructure.t.isLE_of_le ((DerivedCategory.TStructure.t.truncGE d).obj M)
          (c + (k : ℤ) + 1) (d + (k : ℤ)) (by omega))
        (fun q => ?_) n
      by_cases hqd : d ≤ q
      · have : IsIso ((DerivedCategory.homologyFunctor _ q).map
            ((DerivedCategory.TStructure.t.truncGEπ d).app M)) :=
          DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁ _ hT q (d - 1) inferInstance (by omega)
        exact (isCoherent_homology_iff_of_isIso_homologyMap B S hS X hX
          ((DerivedCategory.TStructure.t.truncGEπ d).app M) q).1 (hq q)
      · exact ObjectProperty.prop_of_isZero (isCoherent.{u, u} B S hS X hX)
          (DerivedCategory.isZero_of_isGE _ d q (by omega))

/-- **The hypercohomology `Hom_{D(𝒪_X)}(𝒪_X, N[n])` of an object with coherent cohomology bounded
below is a finite `R`-module**, given finiteness of the cohomology of coherent modules over `R`:
in degree `n` only the truncation `τ_{≤ n} N` contributes, which is bounded, and along its
truncation triangles finiteness passes from the coherent modules placed in one degree. -/
theorem moduleFinite_hom_unit_of_derivedCategoryBPlus_of_hasFiniteCoherentCohomologyOver
    [IsNoetherianRing R] (hfin : HasFiniteCoherentCohomologyOver B S hS X hX ψ)
    (N : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hN : DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B S hS X hX) N)
    (n : ℤ) :
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) ψ
    Module.Finite R ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X hX) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X hX).O)) ⟶ N⟦n⟧) := by
  let := Stacks.SheafOfModules.linearOver
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) ψ
  let O := (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X hX) 0).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X hX).O))
  obtain ⟨a, ha⟩ := hN.1
  have hGE : N.IsGE a := (DerivedCategory.isGE_iff N a).2 ha
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished (n + 1) N
  refine Pretriangulated.moduleFinite_hom_obj₂_of_distinguished O _
    (Pretriangulated.Triangle.shift_distinguished _ hT n) ?_ ?_
  · let lo := min a n
    have hι : ∀ q : ℤ, q < n + 1 → IsIso ((DerivedCategory.homologyFunctor _ q).map
        ((DerivedCategory.TStructure.t.truncLTι (n + 1)).app N)) := fun q hq =>
      DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃ _ hT q (n + 1) inferInstance hq
    have hGE' : ((DerivedCategory.TStructure.t.truncLT (n + 1)).obj N).IsGE lo := by
      rw [DerivedCategory.isGE_iff]
      intro q hq
      have := hι q (by omega)
      exact (ha q (by omega)).of_iso (asIso ((DerivedCategory.homologyFunctor _ q).map
        ((DerivedCategory.TStructure.t.truncLTι (n + 1)).app N)))
    have hLE' : ((DerivedCategory.TStructure.t.truncLT (n + 1)).obj N).IsLE
        (lo + ((n - lo).toNat : ℕ)) :=
      DerivedCategory.TStructure.t.isLE_truncLT_obj N (n + 1) _ (by omega)
    refine moduleFinite_hom_unit_shift_of_isGE_of_isLE_of_hasFiniteCoherentCohomologyOver
      B S hS X hX ψ hfin _ _ lo hGE' hLE' (fun q => ?_) n
    by_cases hq : q < n + 1
    · have := hι q hq
      exact (isCoherent_homology_iff_of_isIso_homologyMap B S hS X hX
        ((DerivedCategory.TStructure.t.truncLTι (n + 1)).app N) q).2 (hN.2 q)
    · exact ObjectProperty.prop_of_isZero (isCoherent.{u, u} B S hS X hX)
        (DerivedCategory.isZero_of_isLE _ n q (by omega))
  · have : ((DerivedCategory.TStructure.t.truncGE (n + 1)).obj N)⟦n⟧.IsGE 1 :=
      DerivedCategory.TStructure.t.isGE_shift _ (n + 1) n 1 (by omega)
    have hs : Subsingleton (O ⟶ ((DerivedCategory.TStructure.t.truncGE (n + 1)).obj N)⟦n⟧) :=
      subsingleton_hom_of_isLE_of_isGE (a := 0) (b := 1) (by omega)
    exact @Module.Finite.of_finite _ _ _ _ _ (@Finite.of_subsingleton _ hs)

end Hypercohomology

end ExtUnit

/-! ### Stacks 0D0T for an arbitrary action -/

section Main

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] pointTopology

attribute [local instance 10000] smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

variable (B S hS) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
  {R : Type u} [CommRing R]
  (ψ : R →+* GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))

/-- **The derived internal Hom `RSheafHom(P, L)` out of a bounded above perfect `P` into
`L ∈ D⁺_Coh(𝒪_X)` comes from an object of `D⁺_Coh(𝒪_X)`** through the model of `D(𝒪_X)`. -/
theorem exists_derivedCategoryBPlus_modelDerived_obj_iso_derivedSheafHom :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X hX)
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleModelRingedSite B S hS X hX).O))
    ∀ (P L : DerivedCategory (Modules.{u, u} B S hS X hX)),
      (smallEtaleRingedSite B S hS X hX).IsPerfect P → ∀ a : ℤ, P.IsLE a →
      DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B S hS X hX) L →
      ∃ N : DerivedCategory (Modules.{u, u} B S hS X hX),
        DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B S hS X hX) N ∧
        Nonempty ((modelDerived B S hS X hX).obj N ≅
          ((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X hX)).obj
            (op ((modelDerived B S hS X hX).obj P))).obj ((modelDerived B S hS X hX).obj L)) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X hX)
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleModelRingedSite B S hS X hX).O))
  intro P L hPperf a hPle hL
  obtain ⟨l, hl⟩ := hL.1
  let Ym := smallEtaleModelRingedSite B S hS X hX
  let e := modulesEquivModelModules B S hS X hX
  let eD := modelDerived B S hS X hX
  have : eD.IsEquivalence := Stacks.Injectives.mapDerivedCategory_isEquivalence e.functor
  have hH : ∀ (i : ℤ) (M : DerivedCategory (Modules.{u, u} B S hS X hX)),
      (DerivedCategory.homologyFunctor _ i).obj (eD.obj M) ≅
        e.functor.obj ((DerivedCategory.homologyFunctor _ i).obj M) := fun i M =>
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso e.functor i).app M
  have hPle' : (eD.obj P).IsLE a := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact (e.functor.map_isZero (((DerivedCategory.isLE_iff P _).1 hPle) i hi)).of_iso (hH i P)
  have hLge' : (eD.obj L).IsGE l := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact (e.functor.map_isZero (hl i hi)).of_iso (hH i L)
  let Z := ((RingedSite.derivedSheafHomBifunctor Ym).obj (op (eD.obj P))).obj (eD.obj L)
  have hZ : Z.IsGE (l - a) :=
    RingedSite.isGE_derivedSheafHom Ym (eD.obj P) (eD.obj L) a l hPle' hLge'
  let N := eD.objPreimage Z
  let eN : eD.obj N ≅ Z := eD.objObjPreimageIso Z
  refine ⟨N, ⟨⟨l - a, fun i hi => ?_⟩, fun i => ?_⟩, ⟨eN⟩⟩
  · have hz : IsZero (e.functor.obj ((DerivedCategory.homologyFunctor _ i).obj N)) :=
      (((DerivedCategory.isGE_iff Z _).1 hZ) i hi).of_iso
        ((hH i N).symm ≪≫ (DerivedCategory.homologyFunctor _ i).mapIso eN)
    exact (e.inverse.map_isZero hz).of_iso (e.unitIso.app _)
  · exact (isCoherent_iff_isCoherentOnSite B S hS X hX _).2
      (isCoherentOnSite_homology_of_modelDerivedSheafHom B S hS X hX P hPperf L
        (fun j => (hL.2 j).toIsCoherentOnSite) N eN i)

/-- **`Hom_{D(𝒪_X)}(P, L[n])` is a finite `R`-module** for a bounded above perfect `P` and
`L ∈ D⁺_Coh(𝒪_X)`, given finiteness of the cohomology of coherent modules over `R`: through the
model it is the hypercohomology of `RSheafHom(P, L) ∈ D⁺_Coh(𝒪_X)` (Stacks 08JA, 0D0S). -/
theorem moduleFinite_hom_shift_of_isPerfect_of_hasFiniteCoherentCohomologyOver
    [IsNoetherianRing R] (hfin : HasFiniteCoherentCohomologyOver B S hS X hX ψ) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X hX)
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) ψ
    ∀ (P L : DerivedCategory (Modules.{u, u} B S hS X hX)),
      (smallEtaleRingedSite B S hS X hX).IsPerfect P → ∀ a : ℤ, P.IsLE a →
      DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B S hS X hX) L →
      ∀ n : ℤ, Module.Finite R (P ⟶ L⟦n⟧) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X hX)
  let := Stacks.SheafOfModules.linearOver
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) ψ
  intro P L hPperf a hPle hL n
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleModelRingedSite B S hS X hX).O))
  obtain ⟨N, hN, ⟨eN⟩⟩ :=
    exists_derivedCategoryBPlus_modelDerived_obj_iso_derivedSheafHom B S hS X hX P L hPperf a
      hPle hL
  let Ym := smallEtaleModelRingedSite B S hS X hX
  let e := modulesEquivModelModules B S hS X hX
  let eD := modelDerived B S hS X hX
  let ψm := (modelGlobalSectionRingHom B S hS X hX).comp ψ
  let : Linear R (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Ym.O)) :=
    Stacks.SheafOfModules.linearOver _ ψm
  have : e.functor.Linear R :=
    modulesEquivModelModules_functor_linear B S hS X hX ψ
  have : eD.IsEquivalence := Stacks.Injectives.mapDerivedCategory_isEquivalence e.functor
  have hfin' := moduleFinite_hom_unit_of_derivedCategoryBPlus_of_hasFiniteCoherentCohomologyOver
    B S hS X hX ψ hfin N hN n
  let OX := (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X hX) 0).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X hX).O))
  have h₇ : Module.Finite R (eD.obj OX ⟶ eD.obj (N⟦n⟧)) :=
    Module.Finite.of_surjective (eD.mapLinearMap R) eD.map_surjective
  let iO : RingedSite.derivedStructureSheaf Ym ≅ eD.obj OX :=
    eqToIso (RingedSite.derivedStructureSheaf_eq_singleFunctor_obj Ym) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (modulesEquivModelModulesUnitIso B S hS X hX).symm ≪≫
      ((e.functor.mapDerivedCategorySingleFunctor 0).app _).symm
  let iR : ((RingedSite.derivedSheafHomBifunctor Ym).obj (op (eD.obj P))).obj
      ((eD.obj L)⟦n⟧) ≅ eD.obj (N⟦n⟧) :=
    ((((RingedSite.derivedSheafHomBifunctor Ym).obj (op (eD.obj P))).commShiftIso n).app
        (eD.obj L)) ≪≫ (CategoryTheory.shiftFunctor _ n).mapIso eN.symm ≪≫
      ((eD.commShiftIso n).app N).symm
  let Ψ : (eD.obj P ⟶ eD.obj (L⟦n⟧)) ≃ₗ[R] (eD.obj OX ⟶ eD.obj (N⟦n⟧)) :=
    (Linear.homCongr R (Iso.refl _) ((eD.commShiftIso n).app L)).trans
      ((RingedSite.homLinearEquivHomStructureSheafDerivedSheafHom Ym ψm (eD.obj P)
        ((eD.obj L)⟦n⟧)).trans (Linear.homCongr R iO iR))
  have h₂ : Module.Finite R (eD.obj P ⟶ eD.obj (L⟦n⟧)) := Module.Finite.equiv Ψ.symm
  exact Module.Finite.of_injective (eD.mapLinearMap R) eD.map_injective

/-- **Stacks 0D0T for an arbitrary action.**  Let `X` be a Noetherian algebraic space, `R` a
Noetherian ring and `ψ : R →+* Γ(X, 𝒪_X)` a ring homomorphism along which the cohomology of every
coherent `𝒪_X`-module is finite.  For `K ∈ D⁻_Coh(𝒪_X)` and `L ∈ D⁺_Coh(𝒪_X)` the group
`Hom_{D(𝒪_X)}(K, L[n])` is then a finite `R`-module for every `n ∈ ℤ`.

The proof is that of `AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper`: `K` is
approximated by a perfect `P` (Stacks 08IK, 08HP), precomposition embeds `Hom(K, L[n])` into
`Hom(P, L[n])`, which is the hypercohomology of `RSheafHom(P, L) ∈ D⁺_Coh(𝒪_X)` (Stacks 08JA,
0D0S), finite by
`moduleFinite_hom_unit_of_derivedCategoryBPlus_of_hasFiniteCoherentCohomologyOver`. -/
theorem moduleFinite_hom_shift_of_hasFiniteCoherentCohomologyOver [IsNoetherianRing R]
    (hXN : IsNoetherian B S hS B.contains_terminal X)
    (hfin : HasFiniteCoherentCohomologyOver B S hS X hX ψ) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X hX)
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) ψ
    ∀ (K L : DerivedCategory (Modules.{u, u} B S hS X hX)),
      DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B S hS X hX) K →
      DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B S hS X hX) L →
      ∀ n : ℤ, Module.Finite R (K ⟶ L⟦n⟧) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X hX)
  let := Stacks.SheafOfModules.linearOver
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) ψ
  intro K L hK hL n
  obtain ⟨b, hb⟩ := hK.1
  obtain ⟨l, hl⟩ := hL.1
  -- `K` is pseudo-coherent (Stacks 08IK) and is approximated by a perfect object (Stacks 08HP)
  obtain ⟨Kc, hKc, ⟨eK⟩⟩ := isPseudoCoherent_of_isCoherent_homology_of_isNoetherian B
    S hS ⟨X, hX⟩ B.contains_terminal hXN K hK.2 ⟨b, hb⟩
  obtain ⟨r, hr⟩ := approximationByPerfectComplexes_of_qcqs B S hS
    B.contains_terminal X hX hXN.1 hXN.2.1 Set.univ isClosed_univ
    (isQuasiCompact_ι_openSubspace_of_eq_empty B S hS X hX _ Set.compl_univ)
  let m := l - n
  let E : QuasicoherentDerivedCategory.{u, u} B S hS X hX :=
    ⟨K, fun i => (hK.2 i).toIsQuasicoherentOnSite⟩
  obtain ⟨P, hPperf, -, α, hiso, hepi⟩ := hr E m ⟨Kc, hKc (m - r), ⟨eK⟩⟩
    (fun _ _ => Set.subset_univ _)
  have : L.IsGE l := (DerivedCategory.isGE_iff L l).2 hl
  have hLn : (L⟦n⟧).IsGE m := DerivedCategory.TStructure.t.isGE_shift L l n m (by omega)
  have hinj := DerivedCategory.precomp_injective_of_approximatesFrom α m ⟨hiso, hepi⟩ hLn
  have hPle : P.IsLE (max m b) := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    have := hiso i (by omega)
    exact (hb i (by omega)).of_iso
      (asIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).map α))
  have := moduleFinite_hom_shift_of_isPerfect_of_hasFiniteCoherentCohomologyOver B S hS X hX ψ
    hfin P L hPperf _ hPle hL n
  exact Module.Finite.of_injective (Linear.leftComp R (L⟦n⟧) α) fun _ _ h => hinj h

/-- **Stacks 0D0T over an affine Noetherian object.**  Let `V` be an object of the big fppf site
whose scheme is affine and locally Noetherian and `f : X ⟶ V` a proper morphism of algebraic
spaces.  For `K ∈ D⁻_Coh(𝒪_X)` and `L ∈ D⁺_Coh(𝒪_X)` the group `Hom_{D(𝒪_X)}(K, L[n])` is a finite
`Γ(V, 𝒪_V)`-module for every `n ∈ ℤ`, the functions on `V` acting through `f`. -/
theorem moduleFinite_hom_shift_of_isProper_toAffineObject (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] {X : AlgebraicSpaces B S hS}
    (f : X ⟶ (schemeSpace V : AlgebraicSpaces B S hS))
    (hf : IsProper B S hS f.hom) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    letI := Stacks.SheafOfModules.linearOver
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
      (objectRingHom V f)
    ∀ (K L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)),
      DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B S hS X.1 X.2) K →
      DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B S hS X.1 X.2) L →
      ∀ n : ℤ, Module.Finite Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (K ⟶ L⟦n⟧) := by
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    have := hV
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  exact moduleFinite_hom_shift_of_hasFiniteCoherentCohomologyOver B S hS X.1 X.2
    (objectRingHom V f)
    (isNoetherian_of_isProper_toAffine B S hS V hV f hf)
    (fun F hF i => moduleFinite_cohomology_of_isProper_toAffineObject V hV f hf F hF i)

end Main

end AlgebraicGeometry.Space

end
