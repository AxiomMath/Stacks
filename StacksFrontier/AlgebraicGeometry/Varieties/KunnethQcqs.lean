module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactIdentityComparison
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.Basic
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.Locality
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldModules
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ExternalTensorProduct
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethQcqsInputs
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
import StacksCore.Tactic.StacksAttribute

/-!
# The Künneth formula for quasi-compact quasi-separated schemes over a field

Let `k` be a field, let `X` and `Y` be quasi-compact quasi-separated schemes over `k` and let `F`,
`G` be quasi-coherent modules on `X`, `Y`. This file proves [Stacks, Tag 0BEF]: the canonical map

`⨁_{p + q = n} Hᵖ(X, F) ⊗_k Hᑫ(Y, G) ⟶ Hⁿ(X ×_k Y, pr₁^*F ⊗_{𝒪_{X ×_k Y}} pr₂^*G)`

is an isomorphism for every `n`.

## The map, and the proof

The proof is the source's, with the roles of the two factors exchanged (the source projects to
`X`, this file to `Y`; the statement is symmetric). Write `RΓ(X, F) ∈ D⁺(k)` for the derived
global sections and `G ⊗_k - : Mod(k) ⥤ Mod(𝒪_Y)` for the exact functor `V ↦ g^*Ṽ ⊗ G`.

1. **Cohomology and base change.** [Stacks, Tag 0GN5] in its derived form,
   `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_derivedComparison_app_single_of_isAffine_base`,
   identifies `Rpr₂,*(pr₁^*F ⊗ pr₂^*G)` with `G ⊗_k Rf_*F` in `D⁺(𝒪_Y)`; this is the role
   [Stacks, Tag 01XN] plays in the source. Over `Spec k` every module is the sheaf associated to
   its global sections (`AlgebraicGeometry.SpecField.modulesEquiv`), so `Rf_*F` is
   `RΓ(X, F)` read on the point.
2. **Leray** for the flat morphisms `X ⟶ Spec k` and `X ×_k Y ⟶ Y`, whose direct images preserve
   injectives, gives `RΓ(X ×_k Y, pr₁^*F ⊗ pr₂^*G) ≅ RΓ(Y, G ⊗_k RΓ(X, F))`
   (`AlgebraicGeometry.KunnethQcqs.derivedProductIso`).
3. **The derived category of a field.** For `K ∈ D⁺(k)` the canonical map
   `⨁_{a + b = n} Hᵃ(K) ⊗_k Hᵇ(Y, G) ⟶ Hⁿ(RΓ(Y, G ⊗_k K))`, sending `x ⊗ y` to the image of `y`
   under `Hⁿ(RΓ(Y, G ⊗_k x̂))` for the morphism `x̂ : k[-a] ⟶ K` representing `x`, is
   `Stacks.KunnethOverField.kunnethNatTrans`. It is an isomorphism when `K` has bounded
   cohomology (`Stacks.KunnethOverField.isIso_kunnethNatTrans_app`): `K` is the sum of its
   shifted cohomology modules, and cohomology commutes with `G ⊗_k -` because `Hᵇ(Y, -)`
   commutes with filtered colimits on a quasi-compact quasi-separated scheme
   ([Stacks, Tag 01FF]). `RΓ(X, F)` has bounded cohomology by [Stacks, Tag 071L].

The Künneth map `AlgebraicGeometry.KunnethQcqs.kunnethMap` is the map of step 3 at
`K = RΓ(X, F)`, followed by the identification of step 2. Every step is a canonical
isomorphism; no choice enters.

## Main definitions

* `AlgebraicGeometry.KunnethQcqs.derivedProductIso`: `RΓ(Y, G ⊗_k RΓ(X, F)) ≅
  RΓ(X ×_k Y, pr₁^*F ⊗ pr₂^*G)`.
* `AlgebraicGeometry.KunnethQcqs.kunnethMap`: **the Künneth map**.

## Main results

* `AlgebraicGeometry.KunnethQcqs.isIso_kunnethMap`: **[Stacks, Tag 0BEF]**.

## Implementation notes

Cohomology is `AlgebraicGeometry.cohomologyOverField`, the right derived functors of global
sections with their `k`-module structure, and the external tensor product is
`AlgebraicGeometry.externalTensorProduct` of [Stacks, Tag 0G46], which is definitionally the
coefficient functor of [Stacks, Tag 0GN5] applied to `F`. The functors of the proof are restated
in the spelling `SheafOfModules (structureSheafRing Z.toRingedSpace)` of [Stacks, Tag 0GN5]
(`AlgebraicGeometry.KunnethQcqs.Mod`), and their instances recorded there, because that spelling
and `AlgebraicGeometry.Scheme.Modules`, as well as modules over `k` and over `CommRingCat.of k`,
are definitionally equal but reach their instances through different paths.

## References

* [Stacks Project, Tag 0BEF](https://stacks.math.columbia.edu/tag/0BEF)
* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 01XN](https://stacks.math.columbia.edu/tag/01XN)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
open Deformation.Artin.SectionsSheaf RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ModuleBaseChange
open scoped DirectSum TensorProduct

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.KunnethQcqs

variable {k : Type u} [Field k]

/-! ### Cohomology over a field as a right derived functor -/

/-- **`Hⁿ(Z, M)` with its `k`-module structure is the `n`-th right derived functor of `k`-linear
global sections.** -/
def cohomologyOverFieldIso {Z : Scheme.{u}} (s : Z ⟶ Spec (.of k)) (M : Z.Modules) (n : ℕ) :
    cohomologyOverField k s M n ≅ ((sectionsOverBase s).rightDerivedPlus (n : ℤ)).obj M :=
  have := Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appTop).hom
  eqToIso (congrArg (fun ψ : Γ(Spec (.of k), ⊤) ⟶ Γ(Z, ⊤) ↦
      (ModuleCat.restrictScalars.{u} ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ ψ).hom).obj
        (((moduleGlobalSections Z).rightDerived n).obj M)) (Scheme.Hom.appLE_eq_app s)) ≪≫
    ((Functor.rightDerivedCompIso (moduleGlobalSections Z)
      (ModuleCat.restrictScalars.{u} ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appTop).hom)
        n).app M).symm ≪≫
    (Stacks.DerivedIndexing.rightDerivedIso (sectionsOverBase s) n).app M

/-! ### Pushforward preserves injectives -/

/-- The direct image along a flat morphism preserves injective objects. -/
theorem preservesInjectiveObjects_modulePushforward {Z Z' : Scheme.{u}} (h : Z ⟶ Z') [Flat h] :
    (modulePushforward h.toLRSHom.toShHom).PreservesInjectiveObjects :=
  preservesInjectiveObjects_of_isExact _ _ (modulePullbackPushforwardAdjunction h.toLRSHom.toShHom)
    ⟨Stacks.AlgebraicGeometry.FlatBaseChangeDerived.preservesFiniteLimits_pullback h,
      Stacks.AlgebraicGeometry.FlatBaseChangeDerived.preservesFiniteColimits_pullback h⟩

/-- `M ↦ M^~` is additive. -/
theorem tilde_additive (R : CommRingCat.{u}) : (tilde.functor R).Additive := inferInstance

/-- Global sections on an affine scheme are additive. -/
theorem moduleSpecΓFunctor_additive (R : CommRingCat.{u}) :
    (moduleSpecΓFunctor (R := R)).Additive :=
  haveI := (tilde.adjunction (R := R)).rightAdjoint_preservesLimits
  Functor.additive_of_preserves_binary_products _

/-- `M ↦ M^~` is exact. -/
theorem tilde_preservesFiniteLimits (R : CommRingCat.{u}) :
    PreservesFiniteLimits (tilde.functor R) := inferInstance

/-! ### The functors, in the spelling of [Stacks, Tag 0GN5]

The comparison of [Stacks, Tag 0GN5] is stated for sheaves of modules over
`structureSheafRing Z.toRingedSpace`, while `AlgebraicGeometry.Scheme.Modules` and
`Deformation.Artin.SectionsSheaf` use `Z.ringCatSheaf`; the two categories are definitionally
equal but carry their instances through different paths, as do modules over `k` and over
`CommRingCat.of k`. The functors are therefore restated once, with the types the derived
comparison needs, and their instances are recorded for those types. -/

/-- The category of `𝒪_Z`-modules, in the spelling of [Stacks, Tag 0GN5]. -/
abbrev Mod (Z : Scheme.{u}) : Type (u + 1) :=
  SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)

/-- `k`-linear global sections `Γ(Z, -) : Mod(𝒪_Z) ⥤ Mod(k)`. -/
def sections {Z : Scheme.{u}} (s : Z ⟶ Spec (.of k)) : Mod Z ⥤ ModuleCat.{u} k :=
  sectionsOverBase s

/-- The global sections functor `sections s` is additive. -/
instance {Z : Scheme.{u}} (s : Z ⟶ Spec (.of k)) : (sections s).Additive :=
  additive_sectionsOverBase s

/-- Global sections on `Spec k`. -/
def specSections : Mod (Spec (.of k)) ⥤ ModuleCat.{u} k :=
  moduleSpecΓFunctor (R := CommRingCat.of k)

/-- Global sections on `Spec k` form an additive functor. -/
instance : (specSections (k := k)).Additive := moduleSpecΓFunctor_additive (CommRingCat.of k)

/-- The sheaf `M^~` on `Spec k` attached to a `k`-module. -/
def specTilde : ModuleCat.{u} k ⥤ Mod (Spec (.of k)) :=
  tilde.functor (CommRingCat.of k)

/-- The functor `M ↦ M^~` on `Spec k` is additive. -/
instance : (specTilde (k := k)).Additive := tilde_additive (CommRingCat.of k)

/-- The functor `M ↦ M^~` on `Spec k` preserves finite limits. -/
instance : PreservesFiniteLimits (specTilde (k := k)) :=
  tilde_preservesFiniteLimits (CommRingCat.of k)

/-- The functor `M ↦ M^~` on `Spec k` preserves finite colimits. -/
instance : PreservesFiniteColimits (specTilde (k := k)) :=
  Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor (CommRingCat.of k)

/-- On `Spec k`, the sheaf associated to the global sections of a module is the module. -/
def specCounitIso : specSections (k := k) ⋙ specTilde ≅ 𝟭 _ :=
  (SpecField.modulesEquiv (R := CommRingCat.of k) (Field.toIsField k)).counitIso

/-- The direct image `Mod(𝒪_Z) ⥤ Mod(𝒪_{Spec k})`. -/
def pushforward {Z : Scheme.{u}} (s : Z ⟶ Spec (.of k)) : Mod Z ⥤ Mod (Spec (.of k)) :=
  modulePushforward s.toLRSHom.toShHom

/-- The direct image `pushforward s` is additive. -/
instance {Z : Scheme.{u}} (s : Z ⟶ Spec (.of k)) : (pushforward s).Additive :=
  modulePushforward_additive _

/-- For flat `s`, the direct image `pushforward s` preserves injective objects. -/
instance {Z : Scheme.{u}} (s : Z ⟶ Spec (.of k)) [Flat s] :
    (pushforward s).PreservesInjectiveObjects :=
  preservesInjectiveObjects_modulePushforward s

/-- The functor `M ↦ g^*M ⊗ G` on `𝒪_{Spec k}`-modules. -/
def baseTensor {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) (G : Mod Y) :
    Mod (Spec (.of k)) ⥤ Mod Y :=
  baseCoefficients g G

/-- The functor `M ↦ g^*M ⊗ G` is additive. -/
instance {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) (G : Mod Y) : (baseTensor g G).Additive :=
  Stacks.SheafOfModules.additive_pullbackTensorFunctor g.toLRSHom.toShHom G

/-- The functor `M ↦ g^*M ⊗ G` preserves finite limits. -/
instance {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) (G : Mod Y) :
    PreservesFiniteLimits (baseTensor g G) :=
  preservesFiniteLimits_baseCoefficients g G (isFlatOver_of_isField g G)

/-- The functor `M ↦ g^*M ⊗ G` preserves finite colimits. -/
instance {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) (G : Mod Y) :
    PreservesFiniteColimits (baseTensor g G) :=
  preservesFiniteColimits_baseCoefficients g G (isFlatOver_of_isField g G)

/-- The functor `V ↦ G ⊗_k V : Mod(k) ⥤ Mod(𝒪_Y)`. -/
def vectorTensor {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) (G : Mod Y) : ModuleCat.{u} k ⥤ Mod Y :=
  tensorSheafFunctor g G

/-- The functor `V ↦ G ⊗_k V` is additive. -/
instance {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) (G : Mod Y) : (vectorTensor g G).Additive :=
  additive_tensorSheafFunctor g G

/-- The functor `V ↦ G ⊗_k V` preserves finite limits. -/
instance {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) (G : Mod Y) :
    PreservesFiniteLimits (vectorTensor g G) :=
  preservesFiniteLimits_tensorSheafFunctor g G (isFlatOver_of_isField g G)

/-- The functor `V ↦ G ⊗_k V` preserves finite colimits. -/
instance {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) (G : Mod Y) :
    PreservesFiniteColimits (vectorTensor g G) :=
  preservesFiniteColimits_tensorSheafFunctor g G (isFlatOver_of_isField g G)

/-- The direct image of `𝒪`-modules along a morphism of schemes is additive. -/
instance {Z Z' : Scheme.{u}} (h : Z ⟶ Z') :
    Functor.Additive (C := Mod Z) (D := Mod Z') (modulePushforward h.toLRSHom.toShHom) :=
  modulePushforward_additive _

/-- The direct image of `𝒪`-modules along a flat morphism preserves injective objects. -/
instance {Z Z' : Scheme.{u}} (h : Z ⟶ Z') [Flat h] :
    Functor.PreservesInjectiveObjects (C := Mod Z) (D := Mod Z')
      (modulePushforward h.toLRSHom.toShHom) :=
  preservesInjectiveObjects_modulePushforward h

/-! ### The derived global sections of the product -/

section Product

variable {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))

/-- **Leray for the structure morphism**: `RΓ(X, -) ≅ RΓ(Spec k, -) ∘ Rf_*`. -/
def lerayBaseIso [Flat f] :
    (sections f).rightDerivedFunctorPlus ≅
      (pushforward f).rightDerivedFunctorPlus ⋙ (specSections (k := k)).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusCompIso (pushforward f) specSections

/-- `R(M ↦ M^~) ∘ RΓ(Spec k, -) ≅ 𝟭` on `D⁺(𝒪_{Spec k})`. -/
def specDerivedIso :
    (specSections (k := k)).rightDerivedFunctorPlus ⋙ (specTilde (k := k)).rightDerivedFunctorPlus ≅
      𝟭 _ :=
  Functor.rightDerivedFunctorPlusCompIsoOfExact _ _ _ (Iso.refl _) ≪≫
    Functor.rightDerivedFunctorPlusIdIsoOf _ specCounitIso

/-- `R(G ⊗_k -) ≅ R(g^*(-) ⊗ G) ∘ R(M ↦ M^~)`. -/
def vectorTensorDerivedIso (G : Mod Y) :
    (specTilde (k := k)).rightDerivedFunctorPlus ⋙ (baseTensor g G).rightDerivedFunctorPlus ≅
      (vectorTensor g G).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusCompIsoOfExact _ _ _ (Iso.refl _)

/-- **Leray for a flat morphism**: `RΓ(Z, -) ≅ RΓ(Z', -) ∘ Rh_*`. -/
def lerayFlatIso {Z Z' : Scheme.{u}} (h : Z ⟶ Z') [Flat h] (s : Z' ⟶ Spec (.of k)) :
    (sections (h ≫ s)).rightDerivedFunctorPlus ≅
      (modulePushforward h.toLRSHom.toShHom).rightDerivedFunctorPlus ⋙
        (sections s).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusCompIso (C := Mod Z) (D := Mod Z')
    (modulePushforward h.toLRSHom.toShHom) (sections s)

variable [CompactSpace X] [QuasiSeparatedSpace X] (F : Mod X) [F.IsQuasicoherent]
  (G : Mod Y) [G.IsQuasicoherent]

/-- `RΓ(X, F) ∈ D⁺(k)`. -/
abbrev derivedSections : DerivedCategory.Plus (ModuleCat.{u} k) :=
  (sections f).rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor (Mod X) 0).obj F)

/-- The external tensor product `pr₁^*F ⊗ pr₂^*G` on `X ×_k Y`, as the coefficient functor of
[Stacks, Tag 0GN5] applied to `F`. -/
abbrev externalTensor : Mod (pullback f g) :=
  (totalCoefficients (pullback.fst f g) (pullback.snd f g) G).obj F

/-- **Cohomology and base change, derived form** ([Stacks, Tag 0GN5]): for the cartesian square
`X ×_k Y ⟶ Y` over `X ⟶ Spec k`,
`RΓ(Y, G ⊗_k RΓ(X, F)) ≅ RΓ(X ×_k Y, pr₁^*F ⊗ pr₂^*G)` in `D⁺(k)`. -/
def derivedProductIso :
    (sections g).rightDerivedFunctorPlus.obj
        ((vectorTensor g G).rightDerivedFunctorPlus.obj (derivedSections f F)) ≅
      (sections (pullback.snd f g ≫ g)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (Mod (pullback f g)) 0).obj
          (externalTensor f g F G)) :=
  have : QuasiCompact f := (quasiCompact_iff_compactSpace f).mpr inferInstance
  have : QuasiSeparated f := (quasiSeparated_iff_quasiSeparatedSpace f).mpr inferInstance
  have H := IsPullback.of_hasPullback f g
  have hG := isFlatOver_of_isField g G
  have := preservesFiniteLimits_totalCoefficients H G hG
  have := preservesFiniteColimits_totalCoefficients H G hG
  (sections g).rightDerivedFunctorPlus.mapIso
      (((vectorTensorDerivedIso g G).app _).symm ≪≫
        (baseTensor g G).rightDerivedFunctorPlus.mapIso
          ((specTilde (k := k)).rightDerivedFunctorPlus.mapIso ((lerayBaseIso f).app _) ≪≫
            (specDerivedIso (k := k)).app _) ≪≫
        @asIso _ _ _ _ ((derivedComparison G H.w hG).app
          ((DerivedCategory.Plus.singleFunctor (Mod X) 0).obj F))
          (isIso_derivedComparison_app_single_of_isAffine_base H G hG F)) ≪≫
    ((lerayFlatIso (pullback.snd f g) g).app _).symm ≪≫
    (sections (pullback.snd f g ≫ g)).rightDerivedFunctorPlus.mapIso
      ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
        (totalCoefficients (pullback.fst f g) (pullback.snd f g) G) 0).app F).symm

/-! ### The Künneth map -/

/-- Restricting a direct sum along an injection, all of whose missed summands are zero. -/
def comapLinearEquiv {R : Type*} [Semiring R] {ι κ : Type*} (e : ι → κ)
    (he : Function.Injective e) (M : κ → Type*) [∀ j, AddCommMonoid (M j)]
    [∀ j, Module R (M j)] (hzero : ∀ j, j ∉ Set.range e → Subsingleton (M j)) :
    (⨁ j, M j) ≃ₗ[R] ⨁ i, M (e i) := by
  classical
  let φ : (⨁ j, M j) →ₗ[R] ⨁ i, M (e i) :=
    { toFun := DFinsupp.comapDomain e he
      map_add' := DFinsupp.comapDomain_add e he
      map_smul' := DFinsupp.comapDomain_smul e he }
  refine LinearEquiv.ofBijective φ ⟨fun x y h ↦ ?_, fun y ↦ ?_⟩
  · ext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      exact congrArg (fun z ↦ z i) h
    · exact @Subsingleton.elim _ (hzero j hj) _ _
  · induction y using DirectSum.induction_on with
    | zero => exact ⟨0, φ.map_zero⟩
    | of i x => exact ⟨DirectSum.lof R κ M (e i) x, DFinsupp.comapDomain_single e he i x⟩
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', φ.map_add x' y'⟩

/-- The index map `{(p, q) ∈ ℕ² | p + q = n} → {(a, b) ∈ ℤ² | a + b = n}`. -/
def natPairs (n : ℕ) :
    {pq : ℕ × ℕ // pq.1 + pq.2 = n} → Stacks.KunnethOverField.Pairs (n : ℤ) :=
  fun pq ↦ ⟨((pq.1.1 : ℤ), (pq.1.2 : ℤ)), by rw [← Nat.cast_add, pq.2]⟩

/-- `natPairs` is injective. -/
theorem natPairs_injective (n : ℕ) : Function.Injective (natPairs n) := fun x y h ↦ by
  simp only [natPairs, Subtype.mk.injEq, Prod.mk.injEq, Nat.cast_inj] at h
  exact Subtype.ext (Prod.ext h.1 h.2)

/-- A pair of nonnegative integers is in the range of `natPairs`. -/
theorem mem_range_natPairs {n : ℕ} (ab : Stacks.KunnethOverField.Pairs (n : ℤ))
    (h₁ : 0 ≤ ab.1.1) (h₂ : 0 ≤ ab.1.2) : ab ∈ Set.range (natPairs n) := by
  refine ⟨⟨(ab.1.1.toNat, ab.1.2.toNat), ?_⟩, ?_⟩
  · have := ab.2
    omega
  · apply Subtype.ext
    simp [natPairs, Int.toNat_of_nonneg h₁, Int.toNat_of_nonneg h₂]

variable (n : ℕ)

/-- `Hᵖ(RΓ(X, F)) = Hᵖ(X, F)`. -/
def homologyDerivedSectionsIso (p : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) (p : ℤ)).obj (derivedSections f F) ≅
      cohomologyOverField k f F p :=
  (cohomologyOverFieldIso f F p).symm

/-- `Hᑫ(Y, G ⊗_k k) = Hᑫ(Y, G)`. -/
def coeffIso (q : ℕ) :
    Stacks.KunnethOverField.coeff (vectorTensor g G) (sections g) (q : ℤ) ≅
      cohomologyOverField k g G q :=
  ((sections g).rightDerivedPlus (q : ℤ)).mapIso (tensorSheafFunctorObjSelf g G) ≪≫
    (cohomologyOverFieldIso g G q).symm

/-- The source of the Künneth map, `⨁_{p + q = n} Hᵖ(X, F) ⊗_k Hᑫ(Y, G)`. -/
abbrev kunnethSource : Type u :=
  ⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
    cohomologyOverField k f F pq.1.1 ⊗[k] cohomologyOverField k g G pq.1.2

/-- The source of the abstract Künneth map at `RΓ(X, F)` is `⨁_{p + q = n} Hᵖ(X, F) ⊗_k Hᑫ(Y, G)`:
the pairs of integers with a negative entry index zero summands. -/
def sourceLinearEquiv :
    Stacks.KunnethOverField.Source (vectorTensor g G) (sections g) (n : ℤ)
        (derivedSections f F) ≃ₗ[k]
      kunnethSource f g F G n :=
  comapLinearEquiv (natPairs n) (natPairs_injective n) _ (fun ab hab ↦ by
      by_cases h₁ : 0 ≤ ab.1.1
      · have h₂ : ab.1.2 < 0 := by
          by_contra h₂
          exact hab (mem_range_natPairs ab h₁ (not_lt.mp h₂))
        have : Subsingleton
            (Stacks.KunnethOverField.coeff (vectorTensor g G) (sections g) ab.1.2) :=
          ModuleCat.isZero_iff_subsingleton.mp
            (Functor.isZero_rightDerivedPlus_of_neg (sections g)
              ((vectorTensor g G).obj (ModuleCat.of k k)) ab.1.2 h₂)
        exact (TensorProduct.uniqueRight (R := k)
          (M := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) ab.1.1).obj
            (derivedSections f F))).instSubsingleton
      · have : Subsingleton ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) ab.1.1).obj
            (derivedSections f F)) := ModuleCat.isZero_iff_subsingleton.mp
          (Functor.isZero_rightDerivedPlus_of_neg (sections f) F ab.1.1 (not_le.mp h₁))
        exact (TensorProduct.uniqueLeft (R := k)
          (N := Stacks.KunnethOverField.coeff (vectorTensor g G) (sections g)
            ab.1.2)).instSubsingleton)
      ≪≫ₗ
    DirectSum.congrLinearEquiv fun pq ↦ TensorProduct.congr
      (homologyDerivedSectionsIso f F pq.1.1).toLinearEquiv (coeffIso g G pq.1.2).toLinearEquiv

/-- The target of the abstract Künneth map at `RΓ(X, F)` is `Hⁿ(X ×_k Y, pr₁^*F ⊗ pr₂^*G)`. -/
def targetIso :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) (n : ℤ)).obj
        ((Stacks.KunnethOverField.Ξ (vectorTensor g G) (sections g)).obj (derivedSections f F)) ≅
      cohomologyOverField k (pullback.fst f g ≫ f) (externalTensorProduct f g F G) n :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) (n : ℤ)).mapIso
      (derivedProductIso f g F G) ≪≫
    (cohomologyOverFieldIso (pullback.snd f g ≫ g) (externalTensor f g F G) n).symm ≪≫
    eqToIso (by rw [pullback.condition]; rfl)

omit [CompactSpace X] [QuasiSeparatedSpace X] [F.IsQuasicoherent] [G.IsQuasicoherent] in
/-- `Hᵇ(Y, G ⊗_k -)` is `k`-linear on scalars, in the spelling of this file. -/
theorem rightDerivedPlus_sections_map_smul (b : ℤ) (c : k) :
    ((sections g).rightDerivedPlus b).map
      ((vectorTensor g G).map (c • 𝟙 (ModuleCat.of k k))) = c • 𝟙 _ :=
  rightDerivedPlus_map_smul g G b c

/-- The Künneth map, for modules spelled as sheaves over `structureSheafRing`; see
`AlgebraicGeometry.KunnethQcqs.kunnethMap`. -/
def derivedKunnethMap :
    ModuleCat.of k (kunnethSource f g F G n) ⟶
      cohomologyOverField k (pullback.fst f g ≫ f) (externalTensorProduct f g F G) n :=
  (sourceLinearEquiv f g F G n).symm.toModuleIso.hom ≫
    (Stacks.KunnethOverField.kunnethNatTrans (vectorTensor g G) (sections g) (n : ℤ)
      (rightDerivedPlus_sections_map_smul g G)).app (derivedSections f F) ≫
    (targetIso f g F G n).hom

/-- The Künneth map is an isomorphism, for modules spelled as sheaves over `structureSheafRing`;
see `AlgebraicGeometry.KunnethQcqs.isIso_kunnethMap`. -/
theorem isIso_derivedKunnethMap [CompactSpace Y] [QuasiSeparatedSpace Y] :
    IsIso (derivedKunnethMap f g F G n) := by
  obtain ⟨I, hI⟩ := exists_isZero_rightDerivedPlus f
  have := Stacks.KunnethOverField.isIso_kunnethNatTrans_app (vectorTensor g G) (sections g)
    (rightDerivedPlus_sections_map_smul g G)
    (fun b J ↦ preservesColimitsOfShape_rightDerivedPlus g G b (Finset (Discrete J)))
    (n : ℤ) (derivedSections f F) I (fun q hq ↦ @hI F ‹F.IsQuasicoherent› q hq)
  unfold derivedKunnethMap
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' this inferInstance)

end Product

/-! ### The Künneth formula -/

section Kunneth

variable {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  [CompactSpace X] [QuasiSeparatedSpace X] (F : X.Modules) [hF : F.IsQuasicoherent]
  (G : Y.Modules) [hG : G.IsQuasicoherent] (n : ℕ)

/-- **The Künneth map** of [Stacks, Tag 0BEF],
`⨁_{p + q = n} Hᵖ(X, F) ⊗_k Hᑫ(Y, G) ⟶ Hⁿ(X ×_k Y, pr₁^*F ⊗ pr₂^*G)`.

On the summand `(p, q)` it sends `x ⊗ y` to the image of `y ∈ Hᑫ(Y, G)` under
`Hⁿ(RΓ(Y, G ⊗_k x̂))`, where `x̂ : k[-p] ⟶ RΓ(X, F)` is the morphism representing
`x ∈ Hᵖ(X, F)`, read through the cohomology and base change isomorphism
`RΓ(Y, G ⊗_k RΓ(X, F)) ≅ RΓ(X ×_k Y, pr₁^*F ⊗ pr₂^*G)` (`derivedProductIso`). -/
def kunnethMap :
    ModuleCat.of k (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
      cohomologyOverField k f F pq.1.1 ⊗[k] cohomologyOverField k g G pq.1.2) ⟶
      cohomologyOverField k (pullback.fst f g ≫ f) (externalTensorProduct f g F G) n :=
  @derivedKunnethMap k _ X Y f g _ _ F hF G hG n

/-- **[Stacks, Tag 0BEF], the Künneth formula.** Let `k` be a field, let `X` and `Y` be schemes
over `k` and let `F`, `G` be quasi-coherent modules on `X`, `Y`. If `X` and `Y` are quasi-compact
and quasi-separated, the canonical map

`⨁_{p + q = n} Hᵖ(X, F) ⊗_k Hᑫ(Y, G) ⟶ Hⁿ(X ×_{Spec k} Y, pr₁^*F ⊗_{𝒪_{X ×_k Y}} pr₂^*G)`

of `AlgebraicGeometry.KunnethQcqs.kunnethMap` is an isomorphism for every `n`. -/
@[stacks 0BEF]
theorem isIso_kunnethMap [CompactSpace Y] [QuasiSeparatedSpace Y] :
    IsIso (kunnethMap f g F G n) :=
  @isIso_derivedKunnethMap k _ X Y f g _ _ F hF G hG n _ _

/-- **The Künneth isomorphism**
`Hⁿ(X ×_k Y, pr₁^*F ⊗ pr₂^*G) ≅ ⨁_{p + q = n} Hᵖ(X, F) ⊗_k Hᑫ(Y, G)`,
the inverse of the Künneth map `AlgebraicGeometry.KunnethQcqs.kunnethMap`. -/
def kunnethIso [CompactSpace Y] [QuasiSeparatedSpace Y] :
    cohomologyOverField k (pullback.fst f g ≫ f) (externalTensorProduct f g F G) n ≅
      ModuleCat.of k (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
        cohomologyOverField k f F pq.1.1 ⊗[k] cohomologyOverField k g G pq.1.2) :=
  have := isIso_kunnethMap f g F G n
  (asIso (kunnethMap f g F G n)).symm

/-- The inverse of the Künneth isomorphism is the Künneth map. -/
theorem kunnethIso_inv [CompactSpace Y] [QuasiSeparatedSpace Y] :
    (kunnethIso f g F G n).inv = kunnethMap f g F G n :=
  rfl

end Kunneth

end AlgebraicGeometry.KunnethQcqs
