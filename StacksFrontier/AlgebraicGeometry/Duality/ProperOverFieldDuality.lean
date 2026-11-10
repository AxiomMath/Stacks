module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.IntoFieldExtra
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsPushforwardPoint
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensChaoticQuasicoherentEquality
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
public import StacksCore.Tactic.StacksAttribute

/-!
# Duality for a scheme over a field

Let `k` be a field and let `f : X ⟶ Spec k` be a quasi-compact quasi-separated morphism — a
proper `X` over `k`, for instance. The twisted inverse image of [Stacks, Tag 0A9E] applied to
the structure sheaf of `Spec k` is the **dualizing complex**

  `ω_X^• = f^×(𝒪_{Spec k})`,

an object of `D_QCoh(𝒪_X)`, and this file proves the duality that characterizes it: for every
`K` in `D_QCoh(𝒪_X)` and every `i`,

  `Ext^i_X(K, ω_X^•) = Hom_k(H^{-i}(X, K), k)`,

naturally in `K`. This is clause (4) of [Stacks, Tag 0BS2].

## Main definitions

* `Stacks.Duality.dualizingComplexOverField` — `ω_X^• = f^×(𝒪_{Spec k})`.
* `Stacks.Duality.derivedCohomologyOverField` — `H^i(X, K)`, the hypercohomology of an object of
  `D(𝒪_X)` as a `k`-vector space.
* `Stacks.Duality.dualityAddEquivZero` — the duality in degree zero,
  `Hom_{D(𝒪_X)}(K, ω_X^•) = Hom_k(H^0(X, K), k)`.
* `Stacks.Duality.extDualityAddEquiv` — **[Stacks, Tag 0BS2], clause (4)**, the duality in every
  degree, `Ext^i_X(K, ω_X^•) = Hom_k(H^{-i}(X, K), k)`.
* `Stacks.Duality.extDualityAddEquivOfIsProper` — the same for a proper morphism, which is the
  source's own situation, and `Stacks.Duality.extDualityAddEquivStructureSheaf` — the same at
  `K = 𝒪_X`, which is the display of the source.

## Main results

* `Stacks.Duality.extDualityAddEquiv_naturality` and
  `Stacks.Duality.dualityAddEquivZero_naturality` — the identifications are natural in `K`: they
  turn precomposition with `g : K ⟶ L` into postcomposition with `H^{-i}(X, g)`.
* `Stacks.Duality.extDualityAddEquiv_shift` — they are compatible with the shift: the degree-`i`
  identification at `K` is the degree-zero one at `K⟦-i⟧`, transported along the shift
  adjunction on the left and `Stacks.Duality.derivedCohomologyShiftNatIso` on the right.
* `Stacks.Duality.dualityAddEquivZero_apply` and
  `Stacks.Duality.extDualityAddEquiv_apply_trace` — the identification is pairing against the
  trace `Stacks.Duality.dualityTrace : H^0(X, ω_X^•) ⟶ k`, the image of `𝟙`.
* `Stacks.Duality.derivedGlobalSectionsStructureSheafIso` — `RΓ(Spec k, 𝒪_{Spec k}) = k`.
* `Stacks.Duality.derivedCohomologyShiftNatIso` — `H^0(X, K⟦j⟧) = H^j(X, K)`.

## Implementation notes

*The chain.* The duality is the composite of four identifications, each of which is available in
this library with no hypothesis beyond quasi-compactness and quasi-separatedness of `f`:

1. the adjunction `Rf_* ⊣ f^×` of [Stacks, Tag 0A9E], which is
   `Stacks.Duality.relativeDualizingComplexHomEquiv`, and gives
   `Hom_{D_QCoh(X)}(K, f^× 𝒪) = Hom_{D_QCoh(Spec k)}(Rf_* K, 𝒪)`;
2. full faithfulness of `RΓ(Spec k, -) : D_QCoh(𝒪_{Spec k}) ⥤ D(k)`, which is an *equivalence*
   by [Stacks, Tag 06Z0] (`AlgebraicGeometry.derivedGlobalSectionsQuasicoherent_isEquivalence`);
3. the identification `RΓ(X, -) = RΓ(Spec k, -) ∘ Rf_*` of [Stacks, Tag 0D5W] over a field,
   `AlgebraicGeometry.derivedGlobalSectionsOverIsoDerivedPushforwardOfField`, which needs no
   hypothesis on `f` because `Spec k` is a single point, together with
   `RΓ(Spec k, 𝒪_{Spec k}) = k`, which is the unit of the derived Spec–Γ adjunction at `k[0]`;
4. `DerivedCategory.homologyMapToInjectiveEquivAnyModel`: maps in `D(k)` into an injective object
   placed in degree zero are maps on homology, and over a field every object is injective.

*The model.* Everything is at the locally small derived categories
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and `ModuleCat.hasDerivedCategory`. That is
forced by step 1: the right adjoint of [Stacks, Tag 0A9E] comes from Brown representability,
whose `HasCoproducts.{u}` hypothesis is false at `CategoryTheory.HasDerivedCategory.standard`.

*Degree `i` from degree zero.* `Ext^i_X(K, ω_X^•) = Hom_{D(𝒪_X)}(K⟦-i⟧, ω_X^•)` and `D_QCoh(𝒪_X)`
is stable under the shift, so the degree-`i` statement is the degree-zero statement at `K⟦-i⟧`
together with `H^0(X, K⟦-i⟧) = H^{-i}(X, K)`, which is the shift compatibility of `RΓ(X, -)`.

*Additivity.* Each step is an isomorphism of abelian groups, not merely a bijection: the
adjunction is between additive functors (`CategoryTheory.Adjunction.homAddEquiv`), the
comparison functors are additive, and conjugating by isomorphisms is additive
(`CategoryTheory.Linear.homCongr` over `ℤ`).

*The hypotheses of the source.* [Stacks, Tag 0BS2] assumes `X` proper over `k` of dimension at
most one. Clause (4) uses neither the dimension bound nor properness: the source itself says it
"holds by construction", the construction being the adjunction of [Stacks, Tag 0A9E], which asks
only that `f` be quasi-compact and quasi-separated. The statements below are therefore at those
hypotheses, and `Stacks.Duality.extDualityAddEquivOfIsProper` is the specialization to a proper
morphism, which is the source's own situation.

*What of clause (4) is here.* The identification in every degree, its naturality in `K`, and its
compatibility with the shift. The source adds that the identifications are compatible with
distinguished triangles; the two outer maps of a triangle are covered by the naturality above,
while the connecting morphism is a degree-one shifted morphism and compatibility with
precomposition by a shifted morphism of arbitrary degree is not proved here. The footnote of the
source — that the property characterizes `ω_X^•` up to unique isomorphism by Yoneda — is a
separate statement and is not proved here either.

## References

* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace Stacks.Duality

/-! ### Additive Hom-set identifications -/

/-- The Hom-set bijection of a fully faithful additive functor, as an isomorphism of abelian
groups. -/
def fullyFaithfulHomAddEquiv {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] {F : C ⥤ D} (hF : F.FullyFaithful) [F.Additive] (A B : C) :
    (A ⟶ B) ≃+ (F.obj A ⟶ F.obj B) where
  __ := hF.homEquiv
  map_add' _ _ := F.map_add

/-- Conjugating a Hom-group by isomorphisms at the two ends, as an isomorphism of abelian
groups. -/
def homCongrAddEquiv {C : Type*} [Category C] [Preadditive C] {A B A' B' : C}
    (e : A ≅ A') (e' : B ≅ B') : (A ⟶ B) ≃+ (A' ⟶ B') :=
  (Linear.homCongr ℤ e e').toAddEquiv

/-- `homCongrAddEquiv e e'` sends `h` to `e.inv ≫ h ≫ e'.hom`. -/
theorem homCongrAddEquiv_apply {C : Type*} [Category C] [Preadditive C] {A B A' B' : C}
    (e : A ≅ A') (e' : B ≅ B') (h : A ⟶ B) :
    homCongrAddEquiv e e' h = e.inv ≫ h ≫ e'.hom := Category.assoc _ _ _

/-- Precomposition with an isomorphism, as an isomorphism of abelian groups. -/
def precompAddEquiv {C : Type*} [Category C] [Preadditive C] {A A' B : C} (e : A ≅ A') :
    (A ⟶ B) ≃+ (A' ⟶ B) where
  toFun h := e.inv ≫ h
  invFun h := e.hom ≫ h
  left_inv h := by simp
  right_inv h := by simp
  map_add' _ _ := by simp

/-- `precompAddEquiv e` sends `h` to `e.inv ≫ h`. -/
theorem precompAddEquiv_apply {C : Type*} [Category C] [Preadditive C] {A A' B : C} (e : A ≅ A')
    (h : A ⟶ B) : precompAddEquiv (B := B) e h = e.inv ≫ h := rfl

/-- Reassociation across a commuting square, stated over an abstract category: the two
conjugates of a morphism `w` agree when the comparison morphisms form a commuting square. -/
theorem comp_square_assoc {C : Type*} [Category C] {A₁ A₂ B₁ B₂ Y T : C}
    (a : A₁ ⟶ A₂) (b : A₂ ⟶ B₂) (c : A₁ ⟶ B₁) (d : B₁ ⟶ B₂) (w : B₂ ⟶ Y) (t : Y ⟶ T)
    (hsq : c ≫ d = a ≫ b) : a ≫ (b ≫ w) ≫ t = c ≫ d ≫ w ≫ t := by
  rw [Category.assoc, ← Category.assoc a b, ← hsq]
  simp only [Category.assoc]

/-! ### Instances over the base field

`CommRingCat.of k` does not reduce during instance search the way a variable `R : CommRingCat`
does, so the instances below are obtained at a variable and then applied (the `tilde` instances are
obtained the same way, inline, where they are used). -/

/-- Derived global sections `RΓ(Spec R, -)` on `D_QCoh(𝒪_{Spec R})` is an additive functor. -/
theorem derivedGlobalSectionsQuasicoherent_additive (R : CommRingCat.{u}) :
    (derivedGlobalSectionsQuasicoherent R).Additive := inferInstance

/-! ### The base field in degree zero -/

/-- The base field as an object of `D(k)`, placed in degree zero. -/
abbrev baseFieldComplex (k : Type u) [Field k] : DerivedCategory (ModuleCat.{u} k) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)

/-- **Derived sheafification of `k` in degree zero is the structure sheaf of `Spec k` in degree
zero.** On cochain complexes `~` commutes with the single-complex functor, and `R̃ = 𝒪_{Spec R}`
on the nose. -/
def derivedTildeBaseFieldIso (k : Type u) [Field k] :
    ((derivedTilde (CommRingCat.of k)).obj (baseFieldComplex k)).obj ≅
      (Stacks.Duality.DerivedPushforward.derivedStructureSheaf
        (Spec (CommRingCat.of k))).obj :=
  letI : (tilde.functor (CommRingCat.of k)).Additive :=
    (fun R : CommRingCat.{u} => (inferInstance : (tilde.functor R).Additive)) _
  letI : PreservesFiniteLimits (tilde.functor (CommRingCat.of k)) :=
    (fun R : CommRingCat.{u} => (inferInstance : PreservesFiniteLimits (tilde.functor R))) _
  letI := Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor (CommRingCat.of k)
  ((tilde.functor (CommRingCat.of k)).mapDerivedCategorySingleFunctor 0).app (ModuleCat.of k k)

/-- **`RΓ(Spec k, 𝒪_{Spec k}) = k`**, in the derived category: the unit of the derived Spec–Γ
adjunction of [Stacks, Tag 06Z0] is invertible, and `𝒪_{Spec k}` in degree zero is the derived
sheafification of `k` in degree zero. -/
def derivedGlobalSectionsStructureSheafIso (k : Type u) [Field k] :
    (derivedGlobalSectionsQuasicoherent (CommRingCat.of k)).obj
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf
          (Spec (CommRingCat.of k))) ≅
      baseFieldComplex k :=
  have := isIso_derivedTildeGlobalSectionsAdjunction_unit (CommRingCat.of k)
  ((derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of k)))).mapIso
      (derivedTildeBaseFieldIso k)).symm ≪≫
    (asIso ((derivedTildeGlobalSectionsAdjunction (CommRingCat.of k)).val.unit.app
      (baseFieldComplex k))).symm

/-! ### The dualizing complex -/

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [QuasiCompact f] [QuasiSeparated f]

/-- **[Stacks, Tag 0A9E] over a field**: `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{Spec k})` has a right
adjoint, the twisted inverse image `f^×`. -/
instance isLeftAdjoint_quasiCoherentDerivedPushforward_overField :
    (quasiCoherentDerivedPushforward f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).IsLeftAdjoint :=
  isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward f

/-- **The dualizing complex `ω_X^• = f^×(𝒪_{Spec k})`** of [Stacks, Tag 0BS2]: the twisted
inverse image of the structure sheaf of `Spec k`, placed in degree zero. -/
def dualizingComplexOverField : quasiCoherentDerivedCategory X :=
  relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))

/-- **`H^i(X, K)`**, the hypercohomology of an object of `D(𝒪_X)` over the base field: the
degree-`i` cohomology of `RΓ(X, K)`, a `k`-vector space. -/
abbrev derivedCohomologyOverField (K : DerivedCategory X.Modules) (i : ℤ) : ModuleCat.{u} k :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj
    ((derivedGlobalSectionsOver f).obj K)

/-! ### The duality in degree zero -/

/-- The morphism of `D_QCoh(𝒪_X)` underlying a morphism of `D(𝒪_X)` between two objects with
quasi-coherent cohomology. -/
def qcohHom {K L : quasiCoherentDerivedCategory X} (g : K.obj ⟶ L.obj) : K ⟶ L :=
  (ObjectProperty.fullyFaithfulι _).preimage g

/-- The morphism of `D(𝒪_X)` underlying `qcohHom g` is `g`. -/
@[simp]
theorem ι_map_qcohHom {K L : quasiCoherentDerivedCategory X} (g : K.obj ⟶ L.obj) :
    (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
      (A := X.Modules) (SheafOfModules.isQuasicoherent X.ringCatSheaf))).map (qcohHom g) = g :=
  (ObjectProperty.fullyFaithfulι _).map_preimage g

/-- `qcohHom` sends a composite to the composite. -/
theorem qcohHom_comp {K L M : quasiCoherentDerivedCategory X} (g : K.obj ⟶ L.obj)
    (h : L.obj ⟶ M.obj) : qcohHom (g ≫ h) = qcohHom g ≫ qcohHom h :=
  (ObjectProperty.fullyFaithfulι _).map_injective (by
    rw [ι_map_qcohHom, Functor.map_comp, ι_map_qcohHom, ι_map_qcohHom])

/-- Step one of the duality: a morphism of `D(𝒪_X)` between objects with quasi-coherent
cohomology is a morphism of `D_QCoh(𝒪_X)`. -/
def dualityStepSubcategory (K : quasiCoherentDerivedCategory X) :
    (K.obj ⟶ (dualizingComplexOverField f).obj) ≃+ (K ⟶ dualizingComplexOverField f) :=
  (fullyFaithfulHomAddEquiv (ObjectProperty.fullyFaithfulι _) K
    (dualizingComplexOverField f)).symm

/-- `dualityStepSubcategory` sends `u` to `qcohHom u`. -/
theorem dualityStepSubcategory_apply (K : quasiCoherentDerivedCategory X)
    (u : K.obj ⟶ (dualizingComplexOverField f).obj) :
    dualityStepSubcategory f K u = qcohHom u := rfl

/-- Step two of the duality: the adjunction `Rf_* ⊣ f^×` of [Stacks, Tag 0A9E]. -/
def dualityStepAdjunction (K : quasiCoherentDerivedCategory X) :
    (K ⟶ dualizingComplexOverField f) ≃+
      ((quasiCoherentDerivedPushforward f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj K ⟶
        Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))) :=
  ((twistedInverseImageAdjunction f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).homAddEquiv
    K _).symm

/-- Step three of the duality: `RΓ(Spec k, -)` is fully faithful on `D_QCoh(𝒪_{Spec k})`, being
an equivalence by [Stacks, Tag 06Z0]. -/
def dualityStepSections (K : quasiCoherentDerivedCategory X) :
    ((quasiCoherentDerivedPushforward f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj K ⟶
        Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))) ≃+
      ((derivedGlobalSectionsQuasicoherent (CommRingCat.of k)).obj
          ((quasiCoherentDerivedPushforward f
              (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj K) ⟶
        (derivedGlobalSectionsQuasicoherent (CommRingCat.of k)).obj
          (Stacks.Duality.DerivedPushforward.derivedStructureSheaf
            (Spec (CommRingCat.of k)))) :=
  letI := derivedGlobalSectionsQuasicoherent_additive (CommRingCat.of k)
  letI := derivedGlobalSectionsQuasicoherent_isEquivalence (CommRingCat.of k)
  fullyFaithfulHomAddEquiv (Functor.FullyFaithful.ofFullyFaithful
    (derivedGlobalSectionsQuasicoherent (CommRingCat.of k))) _ _

/-- `dualityStepSections` sends `v` to `RΓ(Spec k, v)`. -/
theorem dualityStepSections_apply (K : quasiCoherentDerivedCategory X)
    (v : (quasiCoherentDerivedPushforward f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj K ⟶
      Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))) :
    dualityStepSections f K v =
      (derivedGlobalSectionsQuasicoherent (CommRingCat.of k)).map v := rfl

/-- Step four of the duality: the two identifications `RΓ(Spec k, Rf_* K) = RΓ(X, K)` of
[Stacks, Tag 0D5W] and `RΓ(Spec k, 𝒪_{Spec k}) = k` of [Stacks, Tag 06Z0]. -/
def dualityStepCompare (K : quasiCoherentDerivedCategory X) :
    ((derivedGlobalSectionsQuasicoherent (CommRingCat.of k)).obj
          ((quasiCoherentDerivedPushforward f
              (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj K) ⟶
        (derivedGlobalSectionsQuasicoherent (CommRingCat.of k)).obj
          (Stacks.Duality.DerivedPushforward.derivedStructureSheaf
            (Spec (CommRingCat.of k)))) ≃+
      DerivedCategory.Ext ((derivedGlobalSectionsOver f).obj K.obj) (baseFieldComplex k) 0 :=
  homCongrAddEquiv
    ((derivedGlobalSectionsOverIsoDerivedPushforwardOfField k f).app K.obj).symm
    (derivedGlobalSectionsStructureSheafIso k ≪≫
      ((shiftFunctorZero (DerivedCategory (ModuleCat.{u} k)) ℤ).app
        (baseFieldComplex k)).symm)

/-- The comparison at the target of the duality: `RΓ(Spec k, 𝒪_{Spec k}) = k`, read in the
degree-zero shift in which `Ext^0` is written. -/
def dualityBaseIso :
    (derivedGlobalSectionsQuasicoherent (CommRingCat.of k)).obj
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf
          (Spec (CommRingCat.of k))) ≅
      (shiftFunctor (DerivedCategory (ModuleCat.{u} k)) (0 : ℤ)).obj (baseFieldComplex k) :=
  derivedGlobalSectionsStructureSheafIso k ≪≫
    ((shiftFunctorZero (DerivedCategory (ModuleCat.{u} k)) ℤ).app (baseFieldComplex k)).symm

/-- `dualityStepCompare` sends `w` to `w` preceded by the Leray comparison
`RΓ(X, K) ⟶ RΓ(Spec k, Rf_* K)` and followed by `dualityBaseIso`. -/
theorem dualityStepCompare_apply (K : quasiCoherentDerivedCategory X)
    (w : (derivedGlobalSectionsQuasicoherent (CommRingCat.of k)).obj
        ((quasiCoherentDerivedPushforward f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj K) ⟶
      (derivedGlobalSectionsQuasicoherent (CommRingCat.of k)).obj
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf
          (Spec (CommRingCat.of k)))) :
    dualityStepCompare f K w =
      (derivedGlobalSectionsOverIsoDerivedPushforwardOfField k f).hom.app K.obj ≫ w ≫
        (dualityBaseIso (k := k)).hom :=
  homCongrAddEquiv_apply _ _ w

/-- Derived global sections of the direct image of a morphism of `D_QCoh(𝒪_X)` is derived global
sections of that morphism, pushed to the base. -/
theorem derivedGlobalSectionsQuasicoherent_map_pushforward_qcohHom
    {K L : quasiCoherentDerivedCategory X} (h : K.obj ⟶ L.obj) :
    (derivedGlobalSectionsQuasicoherent (CommRingCat.of k)).map
        ((quasiCoherentDerivedPushforward f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
          (qcohHom h)) =
      (Stacks.Duality.derivedPushforward f ⋙
        derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of k)))).map h :=
  congrArg (fun m => (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of k)))).map
    ((Stacks.Duality.derivedPushforward f).map m)) (ι_map_qcohHom h)

/-- **The duality in degree zero, before passing to homology**: for `K` with quasi-coherent
cohomology,

  `Hom_{D(𝒪_X)}(K, ω_X^•) = Hom_{D(k)}(RΓ(X, K), k)`.

This is the composite of the four steps above. -/
def dualityDerivedHomAddEquiv (K : quasiCoherentDerivedCategory X) :
    (K.obj ⟶ (dualizingComplexOverField f).obj) ≃+
      DerivedCategory.Ext ((derivedGlobalSectionsOver f).obj K.obj) (baseFieldComplex k) 0 :=
  (dualityStepSubcategory f K).trans <| (dualityStepAdjunction f K).trans <|
    (dualityStepSections f K).trans (dualityStepCompare f K)

/-- `dualityDerivedHomAddEquiv` is the composite of the four steps of the duality. -/
theorem dualityDerivedHomAddEquiv_apply (K : quasiCoherentDerivedCategory X)
    (u : K.obj ⟶ (dualizingComplexOverField f).obj) :
    dualityDerivedHomAddEquiv f K u =
      dualityStepCompare f K (dualityStepSections f K
        (dualityStepAdjunction f K (dualityStepSubcategory f K u))) := rfl

/-- **The duality in degree zero: `Hom_{D(𝒪_X)}(K, ω_X^•) = Hom_k(H^0(X, K), k)`** for `K` with
quasi-coherent cohomology. This is clause (4) of [Stacks, Tag 0BS2] at `i = 0`. -/
def dualityAddEquivZero (K : quasiCoherentDerivedCategory X) :
    (K.obj ⟶ (dualizingComplexOverField f).obj) ≃+
      (derivedCohomologyOverField f K.obj 0 ⟶ ModuleCat.of k k) :=
  -- the base field is an injective object of `ModuleCat k`: a field is a semisimple ring
  letI : Injective (ModuleCat.of k k) :=
    letI : Module.Injective k k := Module.injective_of_isSemisimpleRing k _
    Module.injective_object_of_injective_module k _
  (dualityDerivedHomAddEquiv f K).trans <|
    DerivedCategory.homologyMapToInjectiveEquivAnyModel
      ((derivedGlobalSectionsOver f).obj K.obj) (ModuleCat.of k k) 0

/-! ### Naturality in degree zero -/

/-- Step one of the duality turns precomposition with `g` into precomposition with
`qcohHom g`. -/
theorem dualityStepSubcategory_naturality (K L : quasiCoherentDerivedCategory X)
    (g : K.obj ⟶ L.obj) (α : L.obj ⟶ (dualizingComplexOverField f).obj) :
    dualityStepSubcategory f K (g ≫ α) = qcohHom g ≫ dualityStepSubcategory f L α :=
  qcohHom_comp g α

/-- Step two of the duality turns precomposition with `q` into precomposition with
`Rf_* q`. -/
theorem dualityStepAdjunction_naturality (K L : quasiCoherentDerivedCategory X) (q : K ⟶ L)
    (v : L ⟶ dualizingComplexOverField f) :
    dualityStepAdjunction f K (q ≫ v) =
      (quasiCoherentDerivedPushforward f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map q ≫
        dualityStepAdjunction f L v :=
  (twistedInverseImageAdjunction f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).homEquiv_naturality_left_symm q v

/-- Step three of the duality turns precomposition with `Rf_* q` into precomposition with
`RΓ(Spec k, Rf_* q)`. -/
theorem dualityStepSections_naturality (K L : quasiCoherentDerivedCategory X) (q : K ⟶ L)
    (w : (quasiCoherentDerivedPushforward f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj L ⟶
      Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))) :
    dualityStepSections f K
        ((quasiCoherentDerivedPushforward f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map q ≫ w) =
      (derivedGlobalSectionsQuasicoherent (CommRingCat.of k)).map
          ((quasiCoherentDerivedPushforward f
              (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map q) ≫
        dualityStepSections f L w :=
  (derivedGlobalSectionsQuasicoherent (CommRingCat.of k)).map_comp _ _

/-- The Leray comparison of [Stacks, Tag 0D5W] over a field is natural on morphisms of
`D_QCoh(𝒪_X)`. -/
theorem dualityLeray_square {K L : quasiCoherentDerivedCategory X} (h : K.obj ⟶ L.obj) :
    (derivedGlobalSectionsOver f).map h ≫
        (derivedGlobalSectionsOverIsoDerivedPushforwardOfField k f).hom.app L.obj =
      (derivedGlobalSectionsOverIsoDerivedPushforwardOfField k f).hom.app K.obj ≫
        (derivedGlobalSectionsQuasicoherent (CommRingCat.of k)).map
        ((quasiCoherentDerivedPushforward f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
          (qcohHom h)) := by
  rw [derivedGlobalSectionsQuasicoherent_map_pushforward_qcohHom]
  exact (derivedGlobalSectionsOverIsoDerivedPushforwardOfField k f).hom.naturality h

/-- Step four of the duality turns precomposition with `RΓ(Spec k, Rf_* h)` into precomposition
with `RΓ(X, h)`. -/
theorem dualityStepCompare_naturality (K L : quasiCoherentDerivedCategory X)
    (h : K.obj ⟶ L.obj)
    (w : (derivedGlobalSectionsQuasicoherent (CommRingCat.of k)).obj
        ((quasiCoherentDerivedPushforward f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj L) ⟶
      (derivedGlobalSectionsQuasicoherent (CommRingCat.of k)).obj
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf
          (Spec (CommRingCat.of k)))) :
    dualityStepCompare f K
        ((derivedGlobalSectionsQuasicoherent (CommRingCat.of k)).map
        ((quasiCoherentDerivedPushforward f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
          (qcohHom h)) ≫ w) =
      (derivedGlobalSectionsOver f).map h ≫ dualityStepCompare f L w :=
  (dualityStepCompare_apply f K _).trans <|
    (comp_square_assoc _ _ _ _ _ _ (dualityLeray_square f h)).trans
      (congrArg (fun z => (derivedGlobalSectionsOver f).map h ≫ z)
        (dualityStepCompare_apply f L w).symm)

/-- **The degree-zero duality is natural in `K`.** -/
theorem dualityDerivedHomAddEquiv_naturality (K L : quasiCoherentDerivedCategory X)
    (g : K.obj ⟶ L.obj) (α : L.obj ⟶ (dualizingComplexOverField f).obj) :
    dualityDerivedHomAddEquiv f K (g ≫ α) =
      (derivedGlobalSectionsOver f).map g ≫ dualityDerivedHomAddEquiv f L α := by
  refine (dualityDerivedHomAddEquiv_apply f K (g ≫ α)).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => (derivedGlobalSectionsOver f).map g ≫ z)
    (dualityDerivedHomAddEquiv_apply f L α).symm)
  exact (congrArg (fun q => dualityStepCompare f K
        (dualityStepSections f K (dualityStepAdjunction f K q)))
      (dualityStepSubcategory_naturality f K L g α)).trans <|
    (congrArg (fun q => dualityStepCompare f K (dualityStepSections f K q))
      (dualityStepAdjunction_naturality f K L (qcohHom g)
        (dualityStepSubcategory f L α))).trans <|
    (congrArg (fun q => dualityStepCompare f K q)
      (dualityStepSections_naturality f K L (qcohHom g)
        (dualityStepAdjunction f L (dualityStepSubcategory f L α)))).trans
    (dualityStepCompare_naturality f K L g
      (dualityStepSections f L (dualityStepAdjunction f L (dualityStepSubcategory f L α))))

/-- **The degree-zero duality of clause (4) of [Stacks, Tag 0BS2] is natural in `K`.** -/
theorem dualityAddEquivZero_naturality (K L : quasiCoherentDerivedCategory X)
    (g : K.obj ⟶ L.obj) (α : L.obj ⟶ (dualizingComplexOverField f).obj) :
    dualityAddEquivZero f K (g ≫ α) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
          ((derivedGlobalSectionsOver f).map g) ≫ dualityAddEquivZero f L α := by
  -- the base field is an injective object of `ModuleCat k`: a field is a semisimple ring
  let : Injective (ModuleCat.of k k) :=
    let : Module.Injective k k := Module.injective_of_isSemisimpleRing k _
    Module.injective_object_of_injective_module k _
  change DerivedCategory.homologyMapToInjectiveEquivAnyModel
      ((derivedGlobalSectionsOver f).obj K.obj) (ModuleCat.of k k) 0
      (dualityDerivedHomAddEquiv f K (g ≫ α)) = _
  exact (congrArg (fun q => DerivedCategory.homologyMapToInjectiveEquivAnyModel
        ((derivedGlobalSectionsOver f).obj K.obj) (ModuleCat.of k k) 0 q)
      (dualityDerivedHomAddEquiv_naturality f K L g α)).trans
    (DerivedCategory.homologyMapToInjectiveEquivAnyModel_naturality
      ((derivedGlobalSectionsOver f).obj L.obj) ((derivedGlobalSectionsOver f).obj K.obj)
      (ModuleCat.of k k) 0 ((derivedGlobalSectionsOver f).map g)
      (dualityDerivedHomAddEquiv f L α))

/-! ### The trace, and the duality as pairing against it -/

/-- **The trace `H^0(X, ω_X^•) ⟶ k`**: the image of the identity of `ω_X^•` under the degree-zero
duality. Pairing against it *is* the duality (`Stacks.Duality.dualityAddEquivZero_apply`). -/
def dualityTrace :
    derivedCohomologyOverField f (dualizingComplexOverField f).obj 0 ⟶ ModuleCat.of k k :=
  dualityAddEquivZero f (dualizingComplexOverField f) (𝟙 (dualizingComplexOverField f).obj)

/-- **The degree-zero duality is pairing against the trace**: a map `u : K ⟶ ω_X^•` goes to
`H^0(X, u)` followed by `Stacks.Duality.dualityTrace`. This is the naturality of the duality
applied at `L = ω_X^•` and `α = 𝟙`. -/
theorem dualityAddEquivZero_apply (K : quasiCoherentDerivedCategory X)
    (u : K.obj ⟶ (dualizingComplexOverField f).obj) :
    dualityAddEquivZero f K u =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
        ((derivedGlobalSectionsOver f).map u) ≫ dualityTrace f :=
  (congrArg (fun z => dualityAddEquivZero f K z) (Category.comp_id u).symm).trans
    (dualityAddEquivZero_naturality f K (dualizingComplexOverField f) u
      (𝟙 (dualizingComplexOverField f).obj))

/-! ### The duality in every degree -/

/-- The shift of an object with quasi-coherent cohomology again has quasi-coherent cohomology:
`D_QCoh(𝒪_X)` is a triangulated subcategory of `D(𝒪_X)`. -/
def shiftQuasiCoherent (K : quasiCoherentDerivedCategory X) (j : ℤ) :
    quasiCoherentDerivedCategory X :=
  ⟨K.obj⟦j⟧, (DerivedCategoryB.derivedCategoryB
    (A := X.Modules) (SheafOfModules.isQuasicoherent X.ringCatSheaf)).le_shift j K.obj K.property⟩

/-- **`H^0(M⟦j⟧) = H^j(M)` in `D(k)`**, as a natural isomorphism of functors. -/
def homologyShiftNatIso (j : ℤ) :
    shiftFunctor (DerivedCategory (ModuleCat.{u} k)) j ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0 ≅
      DerivedCategory.homologyFunctor (ModuleCat.{u} k) j :=
  Functor.isoWhiskerLeft _
      (eqToIso (DerivedCategory.shift_homologyFunctor (ModuleCat.{u} k) 0)) ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).shiftIso j 0 j (by omega) ≪≫
    (eqToIso (DerivedCategory.shift_homologyFunctor (ModuleCat.{u} k) j)).symm

/-- **`H^0(X, K⟦j⟧) = H^j(X, K)`**, as a natural isomorphism of functors: derived global
sections commute with the shift, and the degree-zero cohomology of a shifted complex of
`k`-modules is the shifted cohomology. -/
def derivedCohomologyShiftNatIso (j : ℤ) :
    shiftFunctor (DerivedCategory X.Modules) j ⋙
        (derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0) ≅
      derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) j :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((derivedGlobalSectionsOver f).commShiftIso j) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (homologyShiftNatIso (k := k) j)

/-- **`H^0(X, K⟦j⟧) = H^j(X, K)`** at an object. -/
def derivedCohomologyShiftIso (K : DerivedCategory X.Modules) (j : ℤ) :
    derivedCohomologyOverField f (K⟦j⟧) 0 ≅ derivedCohomologyOverField f K j :=
  (derivedCohomologyShiftNatIso f j).app K

/-- The shift adjunction `⟦-i⟧ ⊣ ⟦i⟧` on `D(𝒪_X)`, which reads `Ext^i` as a Hom out of a
shift: `Ext^i_X(K, ω_X^•) = Hom_{D(𝒪_X)}(K⟦-i⟧, ω_X^•)`. -/
def dualityStepShift (K : quasiCoherentDerivedCategory X) (i : ℤ) :
    DerivedCategory.Ext K.obj (dualizingComplexOverField f).obj i ≃+
      (K.obj⟦-i⟧ ⟶ (dualizingComplexOverField f).obj) :=
  letI : (shiftEquiv' (DerivedCategory X.Modules) (-i) i (by omega)).functor.Additive :=
    inferInstanceAs (shiftFunctor (DerivedCategory X.Modules) (-i)).Additive
  ((shiftEquiv' (DerivedCategory X.Modules) (-i) i (by omega)).toAdjunction.homAddEquiv
    K.obj (dualizingComplexOverField f).obj).symm

/-- The shift adjunction turns precomposition with `g` into precomposition with `g⟦-i⟧`. -/
theorem dualityStepShift_naturality (K L : quasiCoherentDerivedCategory X) (i : ℤ)
    (g : K.obj ⟶ L.obj)
    (α : DerivedCategory.Ext L.obj (dualizingComplexOverField f).obj i) :
    dualityStepShift f K i (g ≫ α) =
      (shiftFunctor (DerivedCategory X.Modules) (-i)).map g ≫ dualityStepShift f L i α :=
  (shiftEquiv' (DerivedCategory X.Modules) (-i) i
    (by omega)).toAdjunction.homEquiv_naturality_left_symm g α

/-- **[Stacks, Tag 0BS2], clause (4).** For a quasi-compact quasi-separated morphism
`f : X ⟶ Spec k` to the spectrum of a field and for every object `K` of `D_QCoh(𝒪_X)` there is an
identification

  `Ext^i_X(K, ω_X^•) = Hom_k(H^{-i}(X, K), k)`,

where `ω_X^• = f^×(𝒪_{Spec k})` is the dualizing complex. It is an isomorphism of abelian groups,
and it is natural in `K` by `Stacks.Duality.extDualityAddEquiv_naturality`.

The source states this for `X` proper over `k` of dimension at most one; neither hypothesis is
used, the identification being, as the source says, a matter of the construction of `ω_X^•`.
`Stacks.Duality.extDualityAddEquivOfIsProper` is the statement at the source's own hypotheses. -/
@[stacks 0BS2 "clause (4)"]
def extDualityAddEquiv (K : quasiCoherentDerivedCategory X) (i : ℤ) :
    DerivedCategory.Ext K.obj (dualizingComplexOverField f).obj i ≃+
      (derivedCohomologyOverField f K.obj (-i) ⟶ ModuleCat.of k k) :=
  (dualityStepShift f K i).trans <|
    (dualityAddEquivZero f (shiftQuasiCoherent K (-i))).trans <|
    precompAddEquiv (derivedCohomologyShiftIso f K.obj (-i))

/-- `extDualityAddEquiv` is the shift adjunction, followed by the degree-zero duality at
`K⟦-i⟧`, followed by precomposition with `H^{-i}(X, K) = H^0(X, K⟦-i⟧)`. -/
theorem extDualityAddEquiv_apply (K : quasiCoherentDerivedCategory X) (i : ℤ)
    (α : DerivedCategory.Ext K.obj (dualizingComplexOverField f).obj i) :
    extDualityAddEquiv f K i α =
      precompAddEquiv (derivedCohomologyShiftIso f K.obj (-i))
        (dualityAddEquivZero f (shiftQuasiCoherent K (-i)) (dualityStepShift f K i α)) := rfl

/-- **Clause (4) of [Stacks, Tag 0BS2] is natural in `K`.** The identification
`Ext^i_X(K, ω_X^•) = Hom_k(H^{-i}(X, K), k)` turns precomposition with `g : K ⟶ L` into
postcomposition with `H^{-i}(X, g)`. -/
@[stacks 0BS2 "clause (4): naturality"]
theorem extDualityAddEquiv_naturality (K L : quasiCoherentDerivedCategory X) (i : ℤ)
    (g : K.obj ⟶ L.obj)
    (α : DerivedCategory.Ext L.obj (dualizingComplexOverField f).obj i) :
    extDualityAddEquiv f K i (g ≫ α) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (-i)).map
          ((derivedGlobalSectionsOver f).map g) ≫ extDualityAddEquiv f L i α := by
  refine (extDualityAddEquiv_apply f K i (g ≫ α)).trans ?_
  refine Eq.trans ?_ (congrArg (fun z =>
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (-i)).map
        ((derivedGlobalSectionsOver f).map g) ≫ z) (extDualityAddEquiv_apply f L i α).symm)
  refine (congrArg (fun q => precompAddEquiv (derivedCohomologyShiftIso f K.obj (-i))
      (dualityAddEquivZero f (shiftQuasiCoherent K (-i)) q))
    (dualityStepShift_naturality f K L i g α)).trans ?_
  refine (congrArg (fun q => precompAddEquiv (derivedCohomologyShiftIso f K.obj (-i)) q)
    (dualityAddEquivZero_naturality f (shiftQuasiCoherent K (-i)) (shiftQuasiCoherent L (-i))
      ((shiftFunctor (DerivedCategory X.Modules) (-i)).map g)
      (dualityStepShift f L i α))).trans ?_
  exact (Category.assoc (derivedCohomologyShiftIso f K.obj (-i)).inv
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
        ((derivedGlobalSectionsOver f).map
          ((shiftFunctor (DerivedCategory X.Modules) (-i)).map g)))
      (dualityAddEquivZero f (shiftQuasiCoherent L (-i)) (dualityStepShift f L i α))).symm.trans <|
    (congrArg (fun z => z ≫ dualityAddEquivZero f (shiftQuasiCoherent L (-i))
        (dualityStepShift f L i α))
      ((derivedCohomologyShiftNatIso f (-i)).inv.naturality g).symm).trans
    (Category.assoc
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (-i)).map
        ((derivedGlobalSectionsOver f).map g))
      (derivedCohomologyShiftIso f L.obj (-i)).inv
      (dualityAddEquivZero f (shiftQuasiCoherent L (-i)) (dualityStepShift f L i α)))

/-- **The duality in degree `i` is pairing against the trace** too: an `α : Ext^i_X(K, ω_X^•)`,
read through the shift adjunction as a map `K⟦-i⟧ ⟶ ω_X^•`, goes to `H^0(X, -)` of that map
followed by `Stacks.Duality.dualityTrace`, precomposed with the shift comparison
`H^{-i}(X, K) = H^0(X, K⟦-i⟧)`. -/
theorem extDualityAddEquiv_apply_trace (K : quasiCoherentDerivedCategory X) (i : ℤ)
    (α : DerivedCategory.Ext K.obj (dualizingComplexOverField f).obj i) :
    extDualityAddEquiv f K i α =
      (derivedCohomologyShiftIso f K.obj (-i)).inv ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
          ((derivedGlobalSectionsOver f).map (dualityStepShift f K i α)) ≫ dualityTrace f :=
  (extDualityAddEquiv_apply f K i α).trans <|
    congrArg (fun z => (derivedCohomologyShiftIso f K.obj (-i)).inv ≫ z)
      (dualityAddEquivZero_apply f (shiftQuasiCoherent K (-i)) (dualityStepShift f K i α))

/-- **Clause (4) of [Stacks, Tag 0BS2]: the identifications are compatible with the shift.**
The degree-`i` identification at `K` is the degree-zero identification at `K⟦-i⟧`, transported
along the canonical isomorphisms on the two sides: the shift adjunction
`Ext^i_X(K, ω_X^•) = Hom_{D(𝒪_X)}(K⟦-i⟧, ω_X^•)` on the left, and the shift comparison
`H^{-i}(X, K) = H^0(X, K⟦-i⟧)` of `Stacks.Duality.derivedCohomologyShiftNatIso` on the right. -/
@[stacks 0BS2 "clause (4): compatibility with the shift"]
theorem extDualityAddEquiv_shift (K : quasiCoherentDerivedCategory X) (i : ℤ)
    (α : DerivedCategory.Ext K.obj (dualizingComplexOverField f).obj i) :
    extDualityAddEquiv f K i α =
      (derivedCohomologyShiftIso f K.obj (-i)).inv ≫
        dualityAddEquivZero f (shiftQuasiCoherent K (-i)) (dualityStepShift f K i α) :=
  extDualityAddEquiv_apply f K i α

/-! ### The source's own hypotheses, and the structure sheaf -/

/-- **[Stacks, Tag 0BS2], clause (4), for a proper morphism** — the situation of the source.
A proper morphism is quasi-compact and quasi-separated, so this is
`Stacks.Duality.extDualityAddEquiv`; the source's bound on the dimension of `X` plays no part in
this clause. -/
@[stacks 0BS2 "clause (4) for a proper morphism"]
def extDualityAddEquivOfIsProper {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (K : quasiCoherentDerivedCategory X)
    (i : ℤ) :
    DerivedCategory.Ext K.obj (dualizingComplexOverField f).obj i ≃+
      (derivedCohomologyOverField f K.obj (-i) ⟶ ModuleCat.of k k) :=
  extDualityAddEquiv f K i

/-- **Clause (4) of [Stacks, Tag 0BS2] at `K = 𝒪_X`:**

  `Ext^i_X(𝒪_X, ω_X^•) = Hom_k(H^{-i}(X, 𝒪_X), k)`.

The left-hand side is the hypercohomology `H^i(X, ω_X^•)` of the dualizing complex, which is what
the source displays; identifying it with cohomology of the structure sheaf is
`AlgebraicGeometry.derivedHomStructureSheafEquivCohomology`. -/
def extDualityAddEquivStructureSheaf (i : ℤ) :
    DerivedCategory.Ext
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf X).obj
        (dualizingComplexOverField f).obj i ≃+
      (derivedCohomologyOverField f
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf X).obj (-i) ⟶
          ModuleCat.of k k) :=
  extDualityAddEquiv f (Stacks.Duality.DerivedPushforward.derivedStructureSheaf X) i

end Stacks.Duality

end
