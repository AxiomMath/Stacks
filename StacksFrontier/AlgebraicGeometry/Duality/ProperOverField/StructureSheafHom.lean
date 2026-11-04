module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDualityLinear
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.StructureSheafPullback
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.Duality

/-!
# Morphisms out of the structure sheaf and the trace pairing of a proper scheme over a field

Let `f : X ⟶ Spec k` be quasi-compact and quasi-separated. For `K` in `D_QCoh(𝒪_X)` the
morphisms `𝒪_X ⟶ K` in `D(𝒪_X)` are the degree-zero hypercohomology `H⁰(X, K)`, as `k`-vector
spaces. For `X` proper over `k` this turns the degree-zero duality of [Stacks, Tag 0FVV] into a
*perfect trace*: with `t : Hom(𝒪_X, ω_X^•) ⟶ k` the trace, the pairing
`Hom(𝒪_X, K) × Hom(K, ω_X^•) ⟶ k`, `(x, h) ↦ t(x ≫ h)`, identifies `Hom(K, ω_X^•)` with the dual
of `Hom(𝒪_X, K)`.

## Main definitions

* `Stacks.Duality.structureSheafHomToCohomology` — `Hom(𝒪_X, K) ⟶ H⁰(X, K)`.
* `Stacks.Duality.structureSheafHomLinearEquiv` — `Hom(𝒪_X, K) ≃ₗ[k] H⁰(X, K)` for `K` with
  quasi-coherent cohomology.
* `Stacks.Duality.structureSheafTrace` — the trace `Hom(𝒪_X, ω_X^•) ⟶ k`.

## Main results

* `Stacks.Duality.bijective_structureSheafTrace_comp` — the trace pairing is perfect.

## Implementation notes

The derived category is the locally small model, at which the duality of
[Stacks, Tag 0FVV] is stated, and `k` acts through `AlgebraicGeometry.modulesLinear`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [QuasiCompact f] [QuasiSeparated f]

/-- `Lf^*𝒪_{Spec k} ≅ 𝒪_X` (`Stacks.Duality.derivedPullbackStructureSheafIso`), in the spelling
of `Stacks.Duality.DerivedPushforward.derivedStructureSheaf`. -/
abbrev pullbackDerivedStructureSheafIso :
    (derivedPullback f).obj
        (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))).obj ≅
      (DerivedPushforward.derivedStructureSheaf X).obj :=
  derivedPullbackStructureSheafIso f

/-- `RΓ(Spec k, 𝒪_{Spec k}) ≅ k[0]`, in the spelling used below. -/
def derivedGlobalSectionsBaseIso :
    (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of k)))).obj
        (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))).obj ≅
      baseFieldComplex k :=
  derivedGlobalSectionsStructureSheafIso k

/-- The comparison `Hom_{D(𝒪_X)}(𝒪_X, K) ⟶ H⁰(X, K)`: transpose along `Lf^* ⊣ Rf_*` after
`𝒪_X = Lf^*𝒪_{Spec k}`, apply `RΓ(Spec k, -)`, identify `RΓ(Spec k, 𝒪) = k` and
`RΓ(Spec k, Rf_* K) = RΓ(X, K)`, and evaluate the resulting class at `1`. -/
def structureSheafHomToCohomology (K : DerivedCategory X.Modules) :
    ((DerivedPushforward.derivedStructureSheaf X).obj ⟶ K) →+ derivedCohomologyOverField f K 0 :=
  ({ toFun := fun φ => φ.hom (show k from 1)
     map_zero' := rfl
     map_add' := fun _ _ => rfl } :
      (ModuleCat.of k k ⟶ derivedCohomologyOverField f K 0) →+
        derivedCohomologyOverField f K 0).comp <|
  (DerivedCategory.homologyFromSingle (ModuleCat.of k k) _ 0).comp <|
  (Preadditive.leftComp _ (derivedGlobalSectionsBaseIso (k := k)).inv).comp <|
  (Preadditive.rightComp _
    ((derivedGlobalSectionsOverIsoDerivedPushforwardOfField k f).inv.app K)).comp <|
  (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of k)))).mapAddHom.comp <|
  (Preadditive.leftComp _ ((derivedAdjunction f).unit.app _)).comp <|
  (derivedPushforward f).mapAddHom.comp <|
  Preadditive.leftComp _ (pullbackDerivedStructureSheafIso f).hom

/-- `structureSheafHomToCohomology` sends `u : 𝒪_X ⟶ K` to the image of `1 : k` under the
map `H⁰` of the composite `RΓ(Spec k, 𝒪) ⟶ RΓ(X, K)` induced by `u`. -/
theorem structureSheafHomToCohomology_apply (K : DerivedCategory X.Modules)
    (u : (DerivedPushforward.derivedStructureSheaf X).obj ⟶ K) :
    structureSheafHomToCohomology f K u =
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).inv.app
          (ModuleCat.of k k) ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
          ((derivedGlobalSectionsBaseIso (k := k)).inv ≫
            (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of k)))).map
              ((derivedAdjunction f).unit.app _ ≫
                (derivedPushforward f).map ((pullbackDerivedStructureSheafIso f).hom ≫ u)) ≫
            (derivedGlobalSectionsOverIsoDerivedPushforwardOfField k f).inv.app K)).hom
        (show k from 1) :=
  rfl

/-- **`structureSheafHomToCohomology` is natural in the target.** -/
theorem structureSheafHomToCohomology_naturality {K L : DerivedCategory X.Modules}
    (u : (DerivedPushforward.derivedStructureSheaf X).obj ⟶ K) (g : K ⟶ L) :
    structureSheafHomToCohomology f L (u ≫ g) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
        ((derivedGlobalSectionsOver f).map g)).hom (structureSheafHomToCohomology f K u) := by
  have hnat := (derivedGlobalSectionsOverIsoDerivedPushforwardOfField k f).inv.naturality g
  have key : (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of k)))).map
        ((derivedAdjunction f).unit.app _ ≫
          (derivedPushforward f).map ((pullbackDerivedStructureSheafIso f).hom ≫ u ≫ g)) ≫
        (derivedGlobalSectionsOverIsoDerivedPushforwardOfField k f).inv.app L =
      ((derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of k)))).map
        ((derivedAdjunction f).unit.app _ ≫
          (derivedPushforward f).map ((pullbackDerivedStructureSheafIso f).hom ≫ u)) ≫
        (derivedGlobalSectionsOverIsoDerivedPushforwardOfField k f).inv.app K) ≫
        (derivedGlobalSectionsOver f).map g := by
    rw [← Category.assoc _ u g, (derivedPushforward f).map_comp, ← Category.assoc,
      (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of k)))).map_comp, Category.assoc,
      Category.assoc]
    exact congrArg (fun z => _ ≫ z) hnat
  rw [structureSheafHomToCohomology_apply, structureSheafHomToCohomology_apply]
  refine (congrArg (fun z => ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} k) 0).inv.app (ModuleCat.of k k) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
        ((derivedGlobalSectionsBaseIso (k := k)).inv ≫ z)).hom (show k from 1)) key).trans ?_
  have hgen : ∀ {P₀ P₁ P₂ P₃ : DerivedCategory (ModuleCat.{u} k)} {M₀ : ModuleCat.{u} k}
      (c : M₀ ⟶ (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj P₀)
      (a : P₀ ⟶ P₁) (x : P₁ ⟶ P₂) (b : P₂ ⟶ P₃) (y : M₀),
      (c ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map (a ≫ x ≫ b)).hom y =
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map b).hom
          ((c ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map (a ≫ x)).hom y) := by
    intros
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact hgen _ _ _ _ _

/-- **`Hom_{D(𝒪_X)}(𝒪_X, K) = H⁰(X, K)`** for `K` with quasi-coherent cohomology, as abelian
groups. Each step of `Stacks.Duality.structureSheafHomToCohomology` is bijective: `Lf^*𝒪 ≅ 𝒪`,
the adjunction `Lf^* ⊣ Rf_*`, full faithfulness of `RΓ(Spec k, -)` on `D_QCoh(𝒪_{Spec k})`
([Stacks, Tag 06Z0]), and `k` being projective in degree zero. -/
def structureSheafHomAddEquiv (K : quasiCoherentDerivedCategory X) :
    ((DerivedPushforward.derivedStructureSheaf X).obj ⟶ K.obj) ≃+
      derivedCohomologyOverField f K.obj 0 := by
  let Ok := DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))
  let pushK : quasiCoherentDerivedCategory (Spec (CommRingCat.of k)) :=
    (quasiCoherentDerivedPushforward f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj K
  letI := derivedGlobalSectionsQuasicoherent_isEquivalence (CommRingCat.of k)
  refine AddEquiv.ofBijective (structureSheafHomToCohomology f K.obj) ?_
  have h1 : Function.Bijective
      (fun u : (DerivedPushforward.derivedStructureSheaf X).obj ⟶ K.obj =>
        (pullbackDerivedStructureSheafIso f).hom ≫ u) :=
    ⟨fun _ _ h => by
      simpa using congrArg (fun z => (pullbackDerivedStructureSheafIso f).inv ≫ z) h,
      fun v => ⟨(pullbackDerivedStructureSheafIso f).inv ≫ v, by simp⟩⟩
  have h2 : Function.Bijective (fun v : (derivedPullback f).obj Ok.obj ⟶ K.obj =>
      (derivedAdjunction f).unit.app _ ≫ (derivedPushforward f).map v) := by
    refine ⟨fun a b h => ((derivedAdjunction f).homEquiv _ _).injective ?_, fun y =>
      ⟨((derivedAdjunction f).homEquiv _ _).symm y, ?_⟩⟩
    · rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
      exact h
    · exact ((derivedAdjunction f).homEquiv_unit _ _ _).symm.trans
        (((derivedAdjunction f).homEquiv _ _).apply_symm_apply y)
  have h3 : Function.Bijective (fun y : Ok.obj ⟶ (derivedPushforward f).obj K.obj =>
      (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of k)))).map y) := by
    have hF := (Functor.FullyFaithful.ofFullyFaithful
      (derivedGlobalSectionsQuasicoherent (CommRingCat.of k))).map_bijective (X := Ok)
        (Y := pushK)
    have hι := (ObjectProperty.fullyFaithfulι (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of k)).ringCatSheaf))).map_bijective
      (X := Ok) (Y := pushK)
    have : (fun y : Ok.obj ⟶ (derivedPushforward f).obj K.obj =>
        (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of k)))).map y) =
        (derivedGlobalSectionsQuasicoherent (CommRingCat.of k)).map ∘
          (Equiv.ofBijective _ hι).symm := by
      funext y
      simp only [Function.comp_apply]
      conv_lhs => rw [← Equiv.ofBijective_apply_symm_apply _ hι y]
      rfl
    rw [this]
    exact hF.comp (Equiv.ofBijective _ hι).symm.bijective
  have h4 : Function.Bijective (fun z : (derivedGlobalSectionsOver
      (𝟙 (Spec (CommRingCat.of k)))).obj Ok.obj ⟶
        (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of k)))).obj
          ((derivedPushforward f).obj K.obj) =>
      (derivedGlobalSectionsBaseIso (k := k)).inv ≫ z ≫
        (derivedGlobalSectionsOverIsoDerivedPushforwardOfField k f).inv.app K.obj) :=
    ⟨fun a b h => (cancel_mono _).1 ((cancel_epi _).1 h), fun w =>
      ⟨(derivedGlobalSectionsBaseIso (k := k)).hom ≫ w ≫
          (derivedGlobalSectionsOverIsoDerivedPushforwardOfField k f).hom.app K.obj, by
        simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_app,
          Category.comp_id]⟩⟩
  have h5 := ((DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of k k)
    ((derivedGlobalSectionsOver f).obj K.obj) 0 k) ≪≫ₗ ModuleCat.homLinearEquiv (R := k) ≪≫ₗ
      LinearMap.ringLmapEquivSelf k k _).bijective
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

/-- **`k`-linear global sections are linear for `AlgebraicGeometry.modulesLinear`**: a base
scalar acts on a module sheaf by multiplication by its image in the sections, and on global
sections by its image in `Γ(X, 𝒪_X)`. -/
theorem globalSectionsOver_linear_modulesLinear (Y : Over (Spec (CommRingCat.of k))) :
    letI := modulesLinear k Y
    Functor.Linear k (globalSectionsOver Y.hom) := by
  let := modulesLinear k Y
  refine ⟨fun {M N} φ c => ?_⟩
  ext x
  let x' : (M.val.obj (Opposite.op ⊤) : Type u) := x
  let s : (Y.left.ringCatSheaf.obj.obj (Opposite.op ⊤) : Type u) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Y.hom.appTop).hom c
  change (φ.val.app (Opposite.op ⊤)).hom (baseRingToSections k Y (Opposite.op ⊤) c • x') =
    s • (φ.val.app (Opposite.op ⊤)).hom x'
  rw [map_smul]
  have h : baseRingToSections k Y (Opposite.op ⊤) c = s := by
    simp only [baseRingToSections]
    have : (⊤ : Y.left.Opens).leTop.op = 𝟙 (Opposite.op ⊤) := rfl
    rw [this, CategoryTheory.Functor.map_id]
    rfl
  rw [h]

section OverField

variable (Y : Over (Spec (CommRingCat.of k))) [QuasiCompact Y.hom] [QuasiSeparated Y.hom]

/-- **`Hom_{D(𝒪_X)}(𝒪_X, K) = H⁰(X, K)` as `k`-vector spaces**, for the `k`-linear structure
`AlgebraicGeometry.modulesLinear` of the structure morphism. The additive identification is
`Stacks.Duality.structureSheafHomAddEquiv`; a scalar `c` acts on the left by postcomposition
with `c • 𝟙`, which the naturality of the identification turns into `H⁰(X, c • 𝟙) = c • 𝟙`. -/
def structureSheafHomLinearEquiv (K : quasiCoherentDerivedCategory Y.left) :
    letI := modulesLinear k Y
    ((DerivedPushforward.derivedStructureSheaf Y.left).obj ⟶ K.obj) ≃ₗ[k]
      derivedCohomologyOverField Y.hom K.obj 0 :=
  letI := modulesLinear k Y
  haveI := globalSectionsOver_linear_modulesLinear Y
  { structureSheafHomAddEquiv Y.hom K with
    map_smul' := fun c u => by
      have h : c • u = u ≫ (c • 𝟙 K.obj) := by rw [Linear.comp_smul, Category.comp_id]
      change structureSheafHomToCohomology Y.hom K.obj (c • u) =
        c • structureSheafHomToCohomology Y.hom K.obj u
      rw [h, structureSheafHomToCohomology_naturality, derivedCohomologyOverField_map_smul_id]
      rfl }

/-- `structureSheafHomLinearEquiv` agrees with `structureSheafHomToCohomology`. -/
theorem structureSheafHomLinearEquiv_apply (K : quasiCoherentDerivedCategory Y.left)
    (u : (DerivedPushforward.derivedStructureSheaf Y.left).obj ⟶ K.obj) :
    letI := modulesLinear k Y
    structureSheafHomLinearEquiv Y K u = structureSheafHomToCohomology Y.hom K.obj u :=
  rfl

variable [IsProper Y.hom]

/-- **The trace** `t : Hom(𝒪_X, ω_X^•) ⟶ k` of a proper scheme over `k`: a morphism
`𝒪_X ⟶ ω_X^•` is a class in `H⁰(X, ω_X^•)`, to which the trace `H⁰(X, ω_X^•) ⟶ k` of
[Stacks, Tag 0FVV] is applied. -/
def structureSheafTrace :
    letI := modulesLinear k Y
    ((DerivedPushforward.derivedStructureSheaf Y.left).obj ⟶
      (dualizingComplexOverField Y.hom).obj) →ₗ[k] k :=
  letI := modulesLinear k Y
  (traceOverField Y.hom).hom ∘ₗ
    (structureSheafHomLinearEquiv Y (dualizingComplexOverField Y.hom)).toLinearMap

/-- **The trace pairing is perfect.** For `E` in `D_QCoh(𝒪_X)`, every linear form on
`Hom(𝒪_X, E)` is `x ↦ t(x ≫ h)` for exactly one `h : E ⟶ ω_X^•`. Under
`Hom(𝒪_X, E) = H⁰(X, E)` this is the degree-zero duality of [Stacks, Tag 0FVV],
`Stacks.Duality.bijective_homologyFunctor_map_comp_traceOverField`. -/
theorem bijective_structureSheafTrace_comp (E : quasiCoherentDerivedCategory Y.left) :
    letI := modulesLinear k Y
    Function.Bijective (fun h : E.obj ⟶ (dualizingComplexOverField Y.hom).obj =>
      structureSheafTrace Y ∘ₗ Linear.rightComp k _ h) := by
  let := modulesLinear k Y
  let σ := structureSheafHomLinearEquiv Y E
  have h₁ := bijective_homologyFunctor_map_comp_traceOverField Y.hom E
  have h₂ : Function.Bijective
      (fun φ : derivedCohomologyOverField Y.hom E.obj 0 ⟶ ModuleCat.of k k =>
        φ.hom ∘ₗ σ.toLinearMap) :=
    σ.dualMap.bijective.comp (ModuleCat.homLinearEquiv (S := k)).bijective
  have heq : (fun h : E.obj ⟶ (dualizingComplexOverField Y.hom).obj =>
      structureSheafTrace Y ∘ₗ Linear.rightComp k _ h) =
      (fun φ : derivedCohomologyOverField Y.hom E.obj 0 ⟶ ModuleCat.of k k =>
        φ.hom ∘ₗ σ.toLinearMap) ∘ (fun g : E.obj ⟶ (dualizingComplexOverField Y.hom).obj ↦
        (DerivedCategory.homologyFunctor (ModuleCat k) 0).map
          ((derivedGlobalSectionsOver Y.hom).map g) ≫ traceOverField Y.hom) := by
    funext h
    refine LinearMap.ext fun x => ?_
    change (traceOverField Y.hom).hom (structureSheafHomToCohomology Y.hom _ (x ≫ h)) =
      (traceOverField Y.hom).hom (((DerivedCategory.homologyFunctor (ModuleCat k) 0).map
        ((derivedGlobalSectionsOver Y.hom).map h)).hom (structureSheafHomToCohomology Y.hom _ x))
    exact congrArg (traceOverField Y.hom).hom (structureSheafHomToCohomology_naturality Y.hom x h)
  rw [heq]
  exact h₂.comp h₁

end OverField

end Stacks.Duality
