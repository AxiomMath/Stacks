module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexLowerVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DegreeZeroCohomology
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.VanishingAndSupport
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularAnyModel
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.LocalBaseVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingLocal
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.DerivedUpperBound
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.LowerShriekDegreeZero
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Normalized
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyOverBaseFunctor
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedPushforwardSupplement
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDualitySupplement
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingExistenceSupplement

/-!
# The dualizing module over a Noetherian local base represents `ℱ ↦ Hom_A(H^d(X, ℱ), ω_A)`

Let `A` be a commutative ring, `f : X ⟶ Spec A` a proper morphism and `ω_S^•` an object of
`D_QCoh(𝒪_{Spec A})`. The relative dualizing complex is `ω_X^• = f^×ω_S^•`
(`Stacks.Duality.relativeDualizingComplex`) and the relative dualizing module is its cohomology
sheaf in degree `-dim(X)`, `ω_X = H^{-dim(X)}(ω_X^•)`
(`Stacks.Duality.relativeDualizingModule`, which carries the definitional clause of
[Stacks, Tag 0AWI]).

This file proves [Stacks, Tag 0AWP] (Lemma 48.22.5) in the situation of Example
[Stacks, Tag 0AWI]: `(A, 𝔪, κ)` Noetherian local, `ω_S^•` corresponding to a normalized
dualizing complex `ω_A^•`, `f` proper, `d` the dimension of the closed fibre and
`dim(X) = d + dim(A)`. Then `ω_X` represents `ℱ ↦ Hom_A(H^d(X, ℱ), ω_A)`.

## What the source says, and what is proved here

The statement is `Stacks.Duality.dualizingModuleRepresentableBy`: a
`CategoryTheory.Functor.RepresentableBy` of the functor
`ℱ ↦ Hom_A(H^d(X, ℱ), ω_A)` on the quasi-coherent `𝒪_X`-modules by `ω_X`, where `H^d(X, ℱ)` is
classical sheaf cohomology with its `A`-module structure
(`Stacks.LocalCohomology.cohomologyOverBaseFunctor`) and `ω_A = H^{-dim(A)}(ω_A^•)`. Two points
are more general than the source: the category is that of quasi-coherent rather than coherent
modules, and `d` enters as an upper bound for the dimension of the closed fibre, together with
`dim(X) = d + dim(A)` (which forces `d` to be that dimension whenever the bound `dim(X) ≤
dim(X_s) + dim(A)` holds). Nothing is assumed beyond the source's hypotheses.

## Main definitions

* `Stacks.Duality.homologyHomAddEquiv` — clause (1) of [Stacks, Tag 06XS] at `a = b`, read as an
  isomorphism of abelian groups.
* `Stacks.Duality.singleShiftHomAddEquiv` — the first two equalities of the source's chain,
  `Hom_{𝒪_X}(ℱ, H^{-m}K) = Hom_{D(𝒪_X)}(ℱ[0]⟦m⟧, K)` for `K` in `D^{≥ -m}`.
* `Stacks.Duality.derivedPushforwardSections` — `RΓ(Spec A, Rf_*K)` as an object of `D(A)`.
* `Stacks.Duality.affineBaseDualityAddEquiv` — the whole chain over an arbitrary affine base.
* `Stacks.Duality.relativeDualizingModuleRepresentabilityOverLocalBase` — the chain over a
  Noetherian local base, with `H^d` read as hypercohomology.
* `Stacks.Duality.derivedPushforwardSectionsHomologyIso` — that hypercohomology is the classical
  `H^d(X, ℱ)`, naturally in `ℱ` ([Stacks, Tag 01XK]).
* `Stacks.Duality.dualizingModuleHomAddEquiv` — `Hom_{𝒪_X}(ℱ, ω_X) = Hom_A(H^d(X, ℱ), ω_A)`.
* `Stacks.Duality.dualizingModuleRepresentableBy` — **[Stacks, Tag 0AWP]**.

## Main results

* `Stacks.Duality.isLE_derivedPushforwardSections_single` — `RΓ(Spec A, Rf_*ℱ)` lies in
  `D^{≤ d}`: Cohomology of Schemes Lemma 30.20.9 ([Stacks, Tag 02V7]) in the form the chain
  consumes.
* `Stacks.Duality.isGE_of_isNormalizedDualizingComplex` — `ω_A^•` lies in `D^{≥ -dim(A)}`, the
  `M = A` case of [Stacks, Tag 0A7U].
* `Stacks.Duality.isLE_derivedPushforward_of_isGE` — `Rf_*` raises an upper bound by at most `d`
  on bounded objects of `D_QCoh(𝒪_X)` (part (3) of [Stacks, Tag 08D4], by dévissage).
* `Stacks.Duality.isGE_relativeDualizingComplex_of_closedFibre_dim_le` — part (1) of
  [Stacks, Tag 0AWN]: `ω_X^•` has no cohomology below `-dim(X)`.
* `Stacks.Duality.affineBaseDualityAddEquiv_naturality`,
  `Stacks.Duality.dualizingModuleHomAddEquiv_naturality` — naturality in `ℱ`.

## The argument

The source's chain of five equalities is

  `Hom_X(ℱ, ω_X) = Ext^{-dim(X)}_X(ℱ, ω_X^•) = Hom_X(ℱ[dim(X)], ω_X^•)`
  `= Hom_X(ℱ[dim(X)], f^!(ω_A^•)) = Hom_S(Rf_*ℱ[dim(X)], ω_A^•) = Hom_A(H^d(X, ℱ), ω_A)`.

Over an affine base it is assembled out of seven steps:

1. `Hom_{𝒪_X}(ℱ, H^{-m}(ω_X^•)) = Hom_{D(𝒪_X)}(ℱ[0]⟦m⟧, ω_X^•)` for `ω_X^•` in `D^{≥ -m}`, by
   clause (1) of [Stacks, Tag 06XS] — the source's first two equalities.
2. The passage to the full subcategory `D_QCoh(𝒪_X)`.
3. The adjunction `Rf_* ⊣ f^×` of [Stacks, Tag 0A9E] — the source's fourth equality
   (`AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward`).
4. `RΓ(Spec A, -) : D_QCoh(𝒪_{Spec A}) ⥤ D(A)` is fully faithful ([Stacks, Tag 06Z0]).
5. `RΓ(Spec A, Rf_*(ℱ[0]⟦m⟧)) = (RΓ(Spec A, Rf_*ℱ[0]))⟦m⟧`.
6. Clause (1) of [Stacks, Tag 06XS] in `D(A)`, for a source in `D^{≤ -e}` and `ω_A^•` in
   `D^{≥ -e}`.
7. `H^{-e}(M⟦m⟧) = H^{m-e}(M)`.

At `m = dim(X)` and `e = dim(A)` the three inputs are the vanishing of `H^i(X, ℱ)` above `d`, the
vanishing of `H^j(ω_A^•)` below `-dim(A)`, and part (1) of [Stacks, Tag 0AWN]. The last is proved
as the source's citation of Lemma 0AWN and dimension theory suggests, in two steps: first
`ω_X^•` is bounded below at all, by [Stacks, Tag 0A9I]
(`Stacks.Duality.exists_isGE_twistedInverseImage_obj`, applied to `ω_S^•`, which lies in
`D^{≥ -dim(A)}` with `ω_A^•`); then the canonical map `τ^{≤ -m-1}(ω_X^•) ⟶ ω_X^•` is zero,
because steps 2–4 identify its Hom-group with `Hom_{D(A)}(RΓ(Spec A, Rf_*τ^{≤ -m-1}(ω_X^•)),
ω_A^•)`, whose source lies in `D^{≤ -e-1}` by the bounded dévissage — the truncation being
bounded by the first step — and whose target lies in `D^{≥ -e}`. A map which is zero and an
isomorphism on `H^j` for `j ≤ -m-1` has zero target there.

## References

* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A9I](https://stacks.math.columbia.edu/tag/0A9I)
* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0AWN](https://stacks.math.columbia.edu/tag/0AWN)
* [Stacks Project, Tag 0AWP](https://stacks.math.columbia.edu/tag/0AWP)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Duality

attribute [local instance] AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward

/-! ### Two generalities about the canonical t-structure -/

/-- **`Hom_{D(C)}(Y, Z) = Hom_C(H^b(Y), H^b(Z))`** for `Y` in `D^{≤ b}` and `Z` in `D^{≥ b}`:
clause (1) of [Stacks, Tag 06XS] at `a = b` and `n = 0`, read as an isomorphism of abelian
groups rather than as a bijection. -/
def homologyHomAddEquiv {C : Type*} [Category C] [Abelian C] [HasDerivedCategory.{u} C]
    (Y Z : DerivedCategory C) (b : ℤ) [Y.IsLE b] [Z.IsGE b] :
    (Y ⟶ Z) ≃+ ((DerivedCategory.homologyFunctor C b).obj Y ⟶
      (DerivedCategory.homologyFunctor C b).obj Z) :=
  AddEquiv.ofBijective (DerivedCategory.homologyFunctor C b).mapAddHom
    (Stacks.Sites.FibredCategory.bijective_homologyFunctor_map_of_isLE_of_isGE Y Z b)

/-- **`H^a(K⟦b⟧) = H^{a+b}(K)`**: the shift isomorphism of the shift sequence that the
cohomology functors of a derived category form. -/
def homologyShiftIso {C : Type*} [Category C] [Abelian C] [HasDerivedCategory.{u} C]
    (K : DerivedCategory C) (a b c : ℤ) (h : b + a = c) :
    (DerivedCategory.homologyFunctor C a).obj (K⟦b⟧) ≅
      (DerivedCategory.homologyFunctor C c).obj K :=
  ((DerivedCategory.homologyFunctor C 0).shiftIso b a c h).app K

/-! ### The first two equalities of the source's chain -/

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  [QuasiCompact f] [QuasiSeparated f]

/-- **`H^{-m}(ℱ[0]⟦m⟧) = ℱ`**: placing a module in degree `-m` and taking the cohomology sheaf
there returns the module. -/
def homologySingleShiftIso (F : X.Modules) (m : ℤ) :
    (DerivedCategory.homologyFunctor X.Modules (-m)).obj
      (((DerivedCategory.singleFunctor X.Modules 0).obj F)⟦m⟧) ≅ F :=
  (DerivedCategory.homologyFunctor X.Modules (-m)).mapIso
      (((DerivedCategory.singleFunctors X.Modules).shiftIso m (-m) 0 (by ring)).app F) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules (-m)).app F

/-- **`Hom_{𝒪_X}(ℱ, H^{-m}(K)) = Hom_{D(𝒪_X)}(ℱ[0]⟦m⟧, K)`** for `K` with no cohomology below
degree `-m`. These are the first two equalities in the proof of [Stacks, Tag 0AWP], taken
together: `ℱ[0]⟦m⟧` lies in `D^{≤ -m}` and `K` in `D^{≥ -m}`, so clause (1) of
[Stacks, Tag 06XS] applies. -/
def singleShiftHomAddEquiv (K : DerivedCategory X.Modules) (m : ℤ) (hge : K.IsGE (-m))
    (F : X.Modules) :
    (F ⟶ (DerivedCategory.homologyFunctor X.Modules (-m)).obj K) ≃+
      ((((DerivedCategory.singleFunctor X.Modules 0).obj F)⟦m⟧) ⟶ K) :=
  have := DerivedCategory.TStructure.t.isLE_shift
    ((DerivedCategory.singleFunctor X.Modules 0).obj F) 0 m (-m) (by ring)
  ((homologyHomAddEquiv (((DerivedCategory.singleFunctor X.Modules 0).obj F)⟦m⟧) K (-m)).trans
    (precompAddEquiv (homologySingleShiftIso F m))).symm


/-! ### Naturality of the chain in the module -/

omit [QuasiCompact f] [QuasiSeparated f] in
/-- **`H^a(K⟦b⟧) = H^{a+b}(K)` is natural in `K`.** -/
theorem homologyShiftIso_inv_naturality {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory.{u} C] {K L : DerivedCategory C} (v : K ⟶ L) (a b c : ℤ)
    (h : b + a = c) :
    (homologyShiftIso K a b c h).inv ≫ (DerivedCategory.homologyFunctor C a).map (v⟦b⟧') =
      (DerivedCategory.homologyFunctor C c).map v ≫ (homologyShiftIso L a b c h).inv :=
  (((DerivedCategory.homologyFunctor C 0).shiftIso b a c h).inv.naturality v).symm

omit [QuasiCompact f] [QuasiSeparated f] in
/-- **`H^{-m}(ℱ[0]⟦m⟧) = ℱ` is natural in `ℱ`.** -/
theorem homologySingleShiftIso_inv_naturality {F G : X.Modules} (u : F ⟶ G) (m : ℤ) :
    u ≫ (homologySingleShiftIso G m).inv =
      (homologySingleShiftIso F m).inv ≫
        (DerivedCategory.homologyFunctor X.Modules (-m)).map
          (((DerivedCategory.singleFunctor X.Modules 0).map u)⟦m⟧') := by
  have h1 : (DerivedCategory.singleFunctor X.Modules (-m)).map u ≫
      ((DerivedCategory.singleFunctors X.Modules).shiftIso m (-m) 0 (by ring)).inv.app G =
        ((DerivedCategory.singleFunctors X.Modules).shiftIso m (-m) 0 (by ring)).inv.app F ≫
          ((DerivedCategory.singleFunctor X.Modules 0).map u)⟦m⟧' :=
    ((DerivedCategory.singleFunctors X.Modules).shiftIso m (-m) 0 (by ring)).inv.naturality u
  have h2 : u ≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules (-m)).inv.app G =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules (-m)).inv.app F ≫
        (DerivedCategory.homologyFunctor X.Modules (-m)).map
          ((DerivedCategory.singleFunctor X.Modules (-m)).map u) :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules (-m)).inv.naturality u
  simp only [homologySingleShiftIso, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv]
  rw [reassoc_of% h2, Category.assoc, ← Functor.map_comp, h1, Functor.map_comp]

omit [QuasiCompact f] [QuasiSeparated f] in
/-- **The first two equalities of the chain are natural in the module.** -/
theorem singleShiftHomAddEquiv_naturality (K : DerivedCategory X.Modules) (m : ℤ)
    (hge : K.IsGE (-m)) {F G : X.Modules} (u : F ⟶ G)
    (φ : G ⟶ (DerivedCategory.homologyFunctor X.Modules (-m)).obj K) :
    singleShiftHomAddEquiv K m hge F (u ≫ φ) =
      ((DerivedCategory.singleFunctor X.Modules 0).map u)⟦m⟧' ≫
        singleShiftHomAddEquiv K m hge G φ := by
  apply (singleShiftHomAddEquiv K m hge F).symm.injective
  rw [AddEquiv.symm_apply_apply]
  show u ≫ φ = (homologySingleShiftIso F m).inv ≫
    (DerivedCategory.homologyFunctor X.Modules (-m)).map
      (((DerivedCategory.singleFunctor X.Modules 0).map u)⟦m⟧' ≫
        singleShiftHomAddEquiv K m hge G φ)
  rw [Functor.map_comp, ← Category.assoc, ← homologySingleShiftIso_inv_naturality,
    Category.assoc]
  congr 1
  exact ((singleShiftHomAddEquiv K m hge G).symm_apply_apply φ).symm

/-! ### The chain over an arbitrary affine base -/

section AffineBase

variable (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  [(quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint]

/-- **`RΓ(Spec A, Rf_*K)`**, the hypercohomology of `K` over the affine base as an object of
`D(A)`: derived direct image followed by the derived global sections of [Stacks, Tag 06Z0].

This is the `A`-module spelling of `H^i(X, K)` that the adjunction of [Stacks, Tag 0A9E]
delivers. For `K = ℱ[0]` its degree-`i` cohomology is the classical `H^i(X, ℱ)` with its
`A`-module structure, by the affine-base degeneration [Stacks, Tag 01XK]; that identification is
run degree by degree inside
`Stacks.Duality.isLE_derivedPushforwardSections_single`. -/
abbrev derivedPushforwardSections (K : quasiCoherentDerivedCategory X) :
    DerivedCategory (ModuleCat.{u} A) :=
  (derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj
    ((quasiCoherentDerivedPushforward f hpush).obj K)

/-- **`RΓ(Spec A, Rf_*(K⟦m⟧)) = (RΓ(Spec A, Rf_*K))⟦m⟧`**: derived direct image and derived
global sections both commute with the shift. -/
def derivedPushforwardSectionsShiftIso (K : quasiCoherentDerivedCategory X) (m : ℤ) :
    derivedPushforwardSections f hpush (shiftQuasiCoherent K m) ≅
      (derivedPushforwardSections f hpush K)⟦m⟧ :=
  (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).mapIso
      (((derivedPushforward f).commShiftIso m).app K.obj) ≪≫
    ((derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).commShiftIso m).app
      ((derivedPushforward f).obj K.obj)

/-- **The chain of [Stacks, Tag 0AWP] over an arbitrary affine base.** For a quasi-compact
quasi-separated `f : X ⟶ Spec A`, an object `ω_S^•` of `D_QCoh(𝒪_{Spec A})` with
`ω_X^• = f^×ω_S^•`, and a quasi-coherent `ℱ`,

  `Hom_{𝒪_X}(ℱ, H^{-m}(ω_X^•)) = Hom_A(H^{m-e}(RΓ(Spec A, Rf_*ℱ)), H^{-e}(ω_A^•))`,

given that `ω_X^•` lies in `D^{≥ -m}`, that `RΓ(Spec A, Rf_*ℱ)` lies in `D^{≤ m-e}` and that
`ω_A^• = RΓ(Spec A, ω_S^•)` lies in `D^{≥ -e}`. At `m = dim(X)` and `e = dim(A)` the left end is
`Hom_X(ℱ, ω_X)` and the right end is `Hom_A(H^d(X, ℱ), ω_A)` for `d = m - e`, the dimension of
the closed fibre.

The seven steps are listed in the module documentation. Nothing about the base enters beyond its
being affine; what makes the three hypotheses available over a Noetherian local base is the
subject of the rest of this file. -/
def affineBaseDualityAddEquiv (ωS : quasiCoherentDerivedCategory (Spec (CommRingCat.of A)))
    (m e : ℤ) (F : X.Modules) (hF : F.IsQuasicoherent)
    (hge : (relativeDualizingComplex f hpush ωS).obj.IsGE (-m))
    (hle : (derivedPushforwardSections f hpush (singleQuasiCoherent F hF 0)).IsLE (m - e))
    (hgeA : ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj ωS).IsGE (-e)) :
    (F ⟶ (DerivedCategory.homologyFunctor X.Modules (-m)).obj
        (relativeDualizingComplex f hpush ωS).obj) ≃+
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (m - e)).obj
          (derivedPushforwardSections f hpush (singleQuasiCoherent F hF 0)) ⟶
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-e)).obj
          ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj ωS)) :=
  have := derivedGlobalSectionsQuasicoherent_additive (CommRingCat.of A)
  have := derivedGlobalSectionsQuasicoherent_isEquivalence (CommRingCat.of A)
  have := DerivedCategory.TStructure.t.isLE_shift
    (derivedPushforwardSections f hpush (singleQuasiCoherent F hF 0)) (m - e) m (-e) (by omega)
  (singleShiftHomAddEquiv _ m hge F).trans <|
    (fullyFaithfulHomAddEquiv (ObjectProperty.fullyFaithfulι _)
        (shiftQuasiCoherent (singleQuasiCoherent F hF 0) m)
        (relativeDualizingComplex f hpush ωS)).symm.trans <|
    (((twistedInverseImageAdjunction f hpush).homAddEquiv
        (shiftQuasiCoherent (singleQuasiCoherent F hF 0) m) ωS).symm).trans <|
    (fullyFaithfulHomAddEquiv (Functor.FullyFaithful.ofFullyFaithful
        (derivedGlobalSectionsQuasicoherent (CommRingCat.of A)))
        ((quasiCoherentDerivedPushforward f hpush).obj
          (shiftQuasiCoherent (singleQuasiCoherent F hF 0) m)) ωS).trans <|
    (precompAddEquiv
      (derivedPushforwardSectionsShiftIso f hpush (singleQuasiCoherent F hF 0) m)).trans <|
    (homologyHomAddEquiv _ _ (-e)).trans <|
    precompAddEquiv (homologyShiftIso
      (derivedPushforwardSections f hpush (singleQuasiCoherent F hF 0)) (-e) m (m - e) (by omega))

omit [QuasiCompact f] [QuasiSeparated f] in
/-- **The shape of the naturality argument for the chain**, over abstract categories: a
composite `i ≫ H₀(j ≫ R₂(R₁ a ≫ ε))` is natural in the source once each of its two
source-dependent isomorphisms `i` and `j` is. -/
theorem chain_naturality_of_squares {𝒳 𝒴 𝒵 ℰ : Type*} [Category 𝒳] [Category 𝒴] [Category 𝒵]
    [Category ℰ] [HasShift 𝒵 ℤ] (R₁ : 𝒳 ⥤ 𝒴) (R₂ : 𝒴 ⥤ 𝒵) (H₀ H₁ : 𝒵 ⥤ ℰ) (m : ℤ)
    {SF SG W : 𝒳} {ωS : 𝒴} {PF PG : 𝒵} (ε : R₁.obj W ⟶ ωS)
    {jF : PF⟦m⟧ ⟶ R₂.obj (R₁.obj SF)} {jG : PG⟦m⟧ ⟶ R₂.obj (R₁.obj SG)}
    {iF : H₁.obj PF ⟶ H₀.obj (PF⟦m⟧)} {iG : H₁.obj PG ⟶ H₀.obj (PG⟦m⟧)}
    {sh : SF ⟶ SG} {p : PF ⟶ PG}
    (hj : jF ≫ R₂.map (R₁.map sh) = p⟦m⟧' ≫ jG)
    (hi : iF ≫ H₀.map (p⟦m⟧') = H₁.map p ≫ iG)
    {aF : SF ⟶ W} {aG : SG ⟶ W} (ha : aF = sh ≫ aG) :
    iF ≫ H₀.map (jF ≫ R₂.map (R₁.map aF ≫ ε)) =
      H₁.map p ≫ iG ≫ H₀.map (jG ≫ R₂.map (R₁.map aG ≫ ε)) := by
  subst ha
  have h1 : jF ≫ R₂.map (R₁.map (sh ≫ aG) ≫ ε) = p⟦m⟧' ≫ jG ≫ R₂.map (R₁.map aG ≫ ε) := by
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hj]
  rw [h1, Functor.map_comp, reassoc_of% hi]

omit [QuasiCompact f] [QuasiSeparated f] in
/-- A composite of morphisms between objects of a full subcategory, read in the subcategory. -/
theorem homMk_comp {C : Type*} [Category C] {P : ObjectProperty C}
    {K L M : P.FullSubcategory} (a : K.obj ⟶ L.obj) (b : L.obj ⟶ M.obj) :
    (ObjectProperty.homMk (a ≫ b) : K ⟶ M) = ObjectProperty.homMk a ≫ ObjectProperty.homMk b :=
  rfl

omit [QuasiCompact f] [QuasiSeparated f] in
/-- Precomposition is carried across a fully faithful functor: the inverse of
`fullyFaithfulHomAddEquiv` for the inclusion of a full subcategory is natural in the source. -/
theorem fullyFaithfulHomAddEquiv_ι_symm_comp {C : Type*} [Category C] [Preadditive C]
    (P : ObjectProperty C) {K K' L : P.FullSubcategory} (g : K' ⟶ K)
    (x : P.ι.obj K ⟶ P.ι.obj L) :
    (fullyFaithfulHomAddEquiv P.fullyFaithfulι K' L).symm (g.hom ≫ x) =
      g ≫ (fullyFaithfulHomAddEquiv P.fullyFaithfulι K L).symm x := by
  apply (fullyFaithfulHomAddEquiv P.fullyFaithfulι K' L).injective
  rw [AddEquiv.apply_symm_apply]
  show g.hom ≫ x = P.ι.map (g ≫ (fullyFaithfulHomAddEquiv P.fullyFaithfulι K L).symm x)
  rw [Functor.map_comp]
  congr 1

omit [QuasiCompact f] [QuasiSeparated f]
  [(quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint] in
/-- **`RΓ(Spec A, Rf_*(K⟦m⟧)) = (RΓ(Spec A, Rf_*K))⟦m⟧` is natural in `K`.** -/
theorem derivedPushforwardSectionsShiftIso_inv_naturality {K L : quasiCoherentDerivedCategory X}
    (U : K ⟶ L) (m : ℤ) :
    (derivedPushforwardSectionsShiftIso f hpush K m).inv ≫
        (derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).map
          ((quasiCoherentDerivedPushforward f hpush).map
            (ObjectProperty.homMk (U.hom⟦m⟧') :
              shiftQuasiCoherent K m ⟶ shiftQuasiCoherent L m)) =
      ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).map
          ((quasiCoherentDerivedPushforward f hpush).map U))⟦m⟧' ≫
        (derivedPushforwardSectionsShiftIso f hpush L m).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  show (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).map
        ((derivedPushforward f).map (U.hom⟦m⟧')) ≫
      ((derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).map
          (((derivedPushforward f).commShiftIso m).hom.app L.obj) ≫
        ((derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).commShiftIso m).hom.app
          ((derivedPushforward f).obj L.obj)) =
    ((derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).map
          (((derivedPushforward f).commShiftIso m).hom.app K.obj) ≫
        ((derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).commShiftIso m).hom.app
          ((derivedPushforward f).obj K.obj)) ≫
      ((derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).map
        ((derivedPushforward f).map U.hom))⟦m⟧'
  rw [← Functor.map_comp_assoc, Functor.commShiftIso_hom_naturality, Functor.map_comp,
    Category.assoc, Category.assoc, Functor.commShiftIso_hom_naturality]

omit [QuasiCompact f] [QuasiSeparated f] in
/-- The value of `Stacks.Duality.affineBaseDualityAddEquiv` on a map `φ : ℱ ⟶ H^{-m}(ω_X^•)`,
written out as a single composite. -/
theorem affineBaseDualityAddEquiv_apply
    (ωS : quasiCoherentDerivedCategory (Spec (CommRingCat.of A)))
    (m e : ℤ) (F : X.Modules) (hF : F.IsQuasicoherent)
    (hge : (relativeDualizingComplex f hpush ωS).obj.IsGE (-m))
    (hle : (derivedPushforwardSections f hpush (singleQuasiCoherent F hF 0)).IsLE (m - e))
    (hgeA : ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj ωS).IsGE (-e))
    (φ : F ⟶ (DerivedCategory.homologyFunctor X.Modules (-m)).obj
      (relativeDualizingComplex f hpush ωS).obj) :
    affineBaseDualityAddEquiv f hpush ωS m e F hF hge hle hgeA φ =
      (homologyShiftIso (derivedPushforwardSections f hpush (singleQuasiCoherent F hF 0))
          (-e) m (m - e) (by omega)).inv ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-e)).map
          ((derivedPushforwardSectionsShiftIso f hpush (singleQuasiCoherent F hF 0) m).inv ≫
            (derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).map
              ((quasiCoherentDerivedPushforward f hpush).map
                  (ObjectProperty.homMk (singleShiftHomAddEquiv _ m hge F φ) :
                    shiftQuasiCoherent (singleQuasiCoherent F hF 0) m ⟶
                      relativeDualizingComplex f hpush ωS) ≫
                (twistedInverseImageAdjunction f hpush).counit.app ωS)) :=
  rfl

omit [QuasiCompact f] [QuasiSeparated f] in
/-- **The chain of [Stacks, Tag 0AWP] over an affine base is natural in the module**:
precomposing a map `𝒢 ⟶ H^{-m}(ω_X^•)` with `u : ℱ ⟶ 𝒢` corresponds to precomposing the
functional with the map `u` induces on `H^{m-e}(RΓ(Spec A, Rf_* -))`. -/
theorem affineBaseDualityAddEquiv_naturality
    (ωS : quasiCoherentDerivedCategory (Spec (CommRingCat.of A)))
    (m e : ℤ) {F G : X.Modules} (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent)
    (hge : (relativeDualizingComplex f hpush ωS).obj.IsGE (-m))
    (hleF : (derivedPushforwardSections f hpush (singleQuasiCoherent F hF 0)).IsLE (m - e))
    (hleG : (derivedPushforwardSections f hpush (singleQuasiCoherent G hG 0)).IsLE (m - e))
    (hgeA : ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj ωS).IsGE (-e))
    (u : F ⟶ G)
    (φ : G ⟶ (DerivedCategory.homologyFunctor X.Modules (-m)).obj
      (relativeDualizingComplex f hpush ωS).obj) :
    affineBaseDualityAddEquiv f hpush ωS m e F hF hge hleF hgeA (u ≫ φ) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (m - e)).map
          ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).map
            ((quasiCoherentDerivedPushforward f hpush).map
              (ObjectProperty.homMk ((DerivedCategory.singleFunctor X.Modules 0).map u) :
                singleQuasiCoherent F hF 0 ⟶ singleQuasiCoherent G hG 0))) ≫
        affineBaseDualityAddEquiv f hpush ωS m e G hG hge hleG hgeA φ := by
  let := derivedGlobalSectionsQuasicoherent_additive (CommRingCat.of A)
  let := derivedGlobalSectionsQuasicoherent_isEquivalence (CommRingCat.of A)
  rw [affineBaseDualityAddEquiv_apply, affineBaseDualityAddEquiv_apply]
  exact chain_naturality_of_squares
    (quasiCoherentDerivedPushforward f hpush)
    (derivedGlobalSectionsQuasicoherent (CommRingCat.of A))
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-e))
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (m - e)) m
    ((twistedInverseImageAdjunction f hpush).counit.app ωS)
    (derivedPushforwardSectionsShiftIso_inv_naturality f hpush
      (ObjectProperty.homMk ((DerivedCategory.singleFunctor X.Modules 0).map u) :
        singleQuasiCoherent F hF 0 ⟶ singleQuasiCoherent G hG 0) m)
    (homologyShiftIso_inv_naturality _ (-e) m (m - e) (by omega))
    (congrArg ObjectProperty.homMk
      (singleShiftHomAddEquiv_naturality (relativeDualizingComplex f hpush ωS).obj m hge u φ))

/-- A module is zero as soon as another module with the same carrier is. -/
private theorem isZero_of_isZero_of_subsingleton {R S : Type*} [Ring R] [Ring S]
    {M : ModuleCat R} {N : ModuleCat S} (h : IsZero M) (hMN : Subsingleton M → Subsingleton N) :
    IsZero N := by
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  exact hMN h

/-- **The first of the three inputs for the last equality of [Stacks, Tag 0AWP]**, over a
Noetherian local base: if the closed fibre of a proper `f : X ⟶ Spec A` has dimension at most
`d`, then `RΓ(Spec A, Rf_*ℱ)` lies in `D^{≤ d}` for every quasi-coherent `ℱ`.

The source cites Cohomology of Schemes Lemma 30.20.9 ([Stacks, Tag 02V7]) for `R^if_*ℱ = 0` when
`i > d`. Over a local base that vanishing is the vanishing of `H^i(X, ℱ)`, which is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_rightDerived_of_closedFibre_dim_le`; the
three steps below carry it across to the `A`-module spelling of the cohomology that the chain
produces. In degree `i` these are: the cohomology of derived global sections on an affine scheme
is the global sections of the cohomology sheaf
(`AlgebraicGeometry.derivedGlobalSectionsQuasicoherentCompHomologyIso`); the cohomology sheaf of
`Rf_*(ℱ[0])` is the classical `R^if_*ℱ`
(`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`); and over an affine base
the global sections of `R^if_*ℱ` are `H^i(X, ℱ)`, which is [Stacks, Tag 01XK]. Restriction of
scalars changes neither the carrier of a module nor therefore its vanishing. -/
theorem isZero_moduleGlobalSections_rightDerived_pushforward [IsNoetherianRing A] [IsLocalRing A]
    [IsProper f] (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber (IsLocalRing.closedPoint A)) ≤ (d : WithBot ℕ∞))
    (p : ℕ) (hp : d < p) (F : X.Modules) (hF : F.IsQuasicoherent) :
    IsZero ((moduleGlobalSections (Spec (CommRingCat.of A))).obj
      (((Scheme.Modules.pushforward f).rightDerived p).obj F)) := by
  let := hF
  have hvan : IsZero (((moduleGlobalSections X).rightDerived p).obj F) :=
    Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_rightDerived_of_closedFibre_dim_le
      f hdim p hp F hF
  refine IsZero.of_iso ?_
    (Stacks.AlgebraicGeometry.ProperCohomologyFinite.cohomologyIsoSectionsRightDerived
      f F p).symm
  exact isZero_of_isZero_of_subsingleton hvan id

/-- `RΓ(Spec A, Rf_*K)` lies in `D^{≤ b}` once the global sections of the cohomology sheaves of
`Rf_*K` vanish above degree `b`. -/
private theorem isLE_derivedPushforwardSections_of_isZero_globalSections
    (g : X ⟶ Spec (CommRingCat.of A))
    (hq : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules i).obj
        ((derivedPushforward g).obj K.obj)).IsQuasicoherent)
    (K : quasiCoherentDerivedCategory X) (b : ℤ)
    (h : ∀ j > b, IsZero ((globalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).obj
      ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules j).obj
        ((derivedPushforward g).obj K.obj)))) :
    (derivedPushforwardSections g hq K).IsLE b := by
  rw [DerivedCategory.isLE_iff]
  intro j hj
  exact IsZero.of_iso (h j hj)
    ((AlgebraicGeometry.derivedGlobalSectionsQuasicoherentCompHomologyIso
      (CommRingCat.of A) j).app ((quasiCoherentDerivedPushforward g hq).obj K))

omit [(quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint] in
/-- If the closed fibre of the proper morphism `f : X ⟶ Spec A` over a Noetherian local ring has
dimension at most `d`, then for a quasi-coherent `𝒪_X`-module `ℱ` the complex `RΓ(Spec A, Rf_*ℱ)`
is concentrated in degrees `≤ d`. -/
theorem isLE_derivedPushforwardSections_single [IsNoetherianRing A] [IsLocalRing A] [IsProper f]
    (d : ℕ) (hdim : topologicalKrullDim (f.fiber (IsLocalRing.closedPoint A)) ≤
      (d : WithBot ℕ∞))
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    (derivedPushforwardSections f hpush (singleQuasiCoherent F hF 0)).IsLE (d : ℤ) := by
  refine isLE_derivedPushforwardSections_of_isZero_globalSections f hpush _ _ fun j hj => ?_
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, (p : ℤ) = j := ⟨j.toNat, by omega⟩
  refine IsZero.of_iso ?_
    ((globalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).mapIso
      ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
        (Scheme.Modules.pushforward f) (derivedPushforward f) (derivedPushforwardUnitAtModel f)
        (Scheme.Modules.exists_quasiIso_isKInjective X) p).app F))
  exact isZero_of_isZero_of_subsingleton
    (isZero_moduleGlobalSections_rightDerived_pushforward f d hdim p (by exact_mod_cast hj) F hF)
    id

/-! ### Part (1) of Tag 0AWN: `ω_X^•` is concentrated in degrees at least `-dim(X)` -/

/-- **`R^if_*ℱ = 0` for `i > d`, as a sheaf**, over a Noetherian local base with closed fibre of
dimension at most `d`. The `A`-module of global sections of `R^if_*ℱ` is `H^i(X, ℱ)` and vanishes
by `Stacks.Duality.isZero_moduleGlobalSections_rightDerived_pushforward`; a quasi-coherent module
on an affine scheme with no global sections is zero. -/
theorem isZero_rightDerivedPlus_pushforward_of_closedFibre_dim_le [IsNoetherianRing A]
    [IsLocalRing A] [IsProper f] (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber (IsLocalRing.closedPoint A)) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) (hF : F.IsQuasicoherent) (p : ℤ) (hp : ((d + 1 : ℕ) : ℤ) ≤ p) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F) := by
  let := hF
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, (q : ℤ) = p := ⟨p.toNat, by omega⟩
  have hnat : IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj F) :=
    Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_sections_of_isAffine _
      (isZero_moduleGlobalSections_rightDerived_pushforward f d hdim q
        (by exact_mod_cast hp) F hF)
  exact IsZero.of_iso hnat
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) q).app F).symm

/-- **`Rf_*(ℱ[n])` lies in `D^{≤ n+d}`** for a quasi-coherent `ℱ`: part (3) of
[Stacks, Tag 08D4] at a module placed in a single degree, fed the sheaf-level vanishing above
the closed-fibre dimension. -/
theorem isLE_derivedPushforward_singleFunctor [IsNoetherianRing A] [IsLocalRing A] [IsProper f]
    (d : ℕ) (hdim : topologicalKrullDim (f.fiber (IsLocalRing.closedPoint A)) ≤
      (d : WithBot ℕ∞))
    (F : X.Modules) (hF : F.IsQuasicoherent) (n : ℤ) :
    ((derivedPushforward f).obj
      ((DerivedCategory.singleFunctor X.Modules n).obj F)).IsLE (n + (d : ℤ)) :=
  have := Stacks.SmallDerivedCategory.isLE_obj_singleFunctor_obj_of_isZero_rightDerivedPlus
    (Scheme.Modules.pushforward f) (derivedPushforward f) (derivedPushforwardUnitAtModel f)
    (Scheme.Modules.exists_quasiIso_isKInjective X) F (d + 1)
    (isZero_rightDerivedPlus_pushforward_of_closedFibre_dim_le f d hdim F hF) n
  DerivedCategory.TStructure.t.isLE_of_le _ (n + ((d + 1 : ℕ) : ℤ) - 1) (n + (d : ℤ))
    (by push_cast; omega)

/-- **`Rf_*` raises an upper cohomological bound by at most `d` on the bounded objects of
`D_QCoh(𝒪_X)`**, over a Noetherian local base whose closed fibre has dimension at most `d`.

The dévissage is on the length of the range of degrees, which is why the lower bound `a` is
needed and why no derived-limit argument — and so no exactness of products in the category of
`𝒪_{Spec A}`-modules — enters: this is
`Stacks.SmallDerivedCategory.isLE_obj_of_isGE`, whose input at a module placed in a single
degree is `Stacks.Duality.isLE_derivedPushforward_singleFunctor`. -/
@[sga "6 III 2.2.2" "special case"]
theorem isLE_derivedPushforward_of_isGE [IsNoetherianRing A] [IsLocalRing A] [IsProper f]
    (d : ℕ) (hdim : topologicalKrullDim (f.fiber (IsLocalRing.closedPoint A)) ≤
      (d : WithBot ℕ∞))
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (a b : ℤ) (hGE : E.IsGE a) (hLE : E.IsLE b) :
    ((derivedPushforward f).obj E).IsLE (b + (d : ℤ)) :=
  Stacks.SmallDerivedCategory.isLE_obj_of_isGE (isQuasicoherentModules X)
    (derivedPushforward f) (d : ℤ)
    (fun M hM n => isLE_derivedPushforward_singleFunctor f d hdim M hM n) E hE a b

omit [QuasiCompact f] [QuasiSeparated f]
  [(quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint] in
/-- **Derived global sections on the affine base preserve an upper cohomological bound** on
`D_QCoh(𝒪_{Spec A})`: the degree-`j` cohomology of `RΓ(Spec A, E)` is the module of global
sections of the degree-`j` cohomology sheaf of `E`
(`AlgebraicGeometry.derivedGlobalSectionsQuasicoherentCompHomologyIso`), and global sections of a
zero object vanish. -/
theorem isLE_derivedPushforwardSections (K : quasiCoherentDerivedCategory X) (b : ℤ)
    (h : ((derivedPushforward f).obj K.obj).IsLE b) :
    (derivedPushforwardSections f hpush K).IsLE b := by
  refine isLE_derivedPushforwardSections_of_isZero_globalSections f hpush K b fun j hj => ?_
  let := h
  exact (globalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).map_isZero
    (DerivedCategory.isZero_of_isLE _ b j hj)

omit [(quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint] in
/-- **The sharpening step of part (1) of [Stacks, Tag 0AWN] over a Noetherian local base.**
Let `f : X ⟶ Spec A` be proper with closed fibre of dimension at most `d`, let
`ω_A^• = RΓ(Spec A, ω_S^•)` lie in `D^{≥ -e}`, and let `m = d + e`. If `ω_X^• = f^×ω_S^•` has no
cohomology below *some* degree `c₀`, then it has none below `-m`.

This is the argument of `Stacks.Duality.isGE_dualizingComplexOverField_of_dim_le` transposed to a
general base. The truncation `τ = τ^{≤ -m-1}(ω_X^•)` lies in `D^{≥ c₀}` and in `D^{≤ -m-1}`, so
it is bounded, and `Stacks.Duality.isLE_derivedPushforward_of_isGE` puts `Rf_*τ` in
`D^{≤ -e-1}`; `Stacks.Duality.isLE_derivedPushforwardSections` puts `RΓ(Spec A, Rf_*τ)` there
too, and no nonzero morphism goes from `D^{≤ -e-1}` to `D^{≥ -e}`. The adjunction of
[Stacks, Tag 0A9E] and the full faithfulness of `RΓ(Spec A, -)` carry that back to
`Hom_{D(𝒪_X)}(τ, ω_X^•) = 0`, so the canonical map `τ ⟶ ω_X^•` is zero while being an
isomorphism on `H^j` for every `j ≤ -m-1`; an isomorphism which is the zero morphism has zero
target.

That `ω_X^•` is bounded below is [Stacks, Tag 0A9I]; the combination is
`Stacks.Duality.isGE_relativeDualizingComplex_of_closedFibre_dim_le`. -/
theorem isGE_relativeDualizingComplex_of_isGE [IsNoetherianRing A] [IsLocalRing A] [IsProper f]
    [(quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint]
    (ωS : quasiCoherentDerivedCategory (Spec (CommRingCat.of A)))
    (d : ℕ) (hdim : topologicalKrullDim (f.fiber (IsLocalRing.closedPoint A)) ≤
      (d : WithBot ℕ∞))
    (m e c₀ : ℤ) (hm : m = (d : ℤ) + e)
    (hb : (relativeDualizingComplex f hpush ωS).obj.IsGE c₀)
    (hgeA : ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj ωS).IsGE (-e)) :
    (relativeDualizingComplex f hpush ωS).obj.IsGE (-m) := by
  let := hb
  let := hgeA
  let := derivedGlobalSectionsQuasicoherent_additive (CommRingCat.of A)
  let := derivedGlobalSectionsQuasicoherent_isEquivalence (CommRingCat.of A)
  set ωX := relativeDualizingComplex f hpush ωS with hωX
  have hτLE : ((DerivedCategory.TStructure.t.truncLE (-m - 1)).obj ωX.obj).IsLE (-m - 1) :=
    DerivedCategory.TStructure.t.isLE_truncLE_obj ωX.obj (-m - 1) (-m - 1) le_rfl
  have hτGE : ((DerivedCategory.TStructure.t.truncLE (-m - 1)).obj ωX.obj).IsGE c₀ :=
    inferInstance
  let := isLE_derivedPushforward_of_isGE f d hdim
    (truncLEQuasiCoherent ωX (-m - 1)).obj
    (truncLEQuasiCoherent ωX (-m - 1)).property c₀ (-m - 1) hτGE hτLE
  have h2 : (derivedPushforwardSections f hpush (truncLEQuasiCoherent ωX (-m - 1))).IsLE
      (-e - 1) :=
    isLE_derivedPushforwardSections f hpush (truncLEQuasiCoherent ωX (-m - 1)) (-e - 1)
      (DerivedCategory.TStructure.t.isLE_of_le _ (-m - 1 + (d : ℤ)) (-e - 1) (by omega))
  have hzero : ∀ g : (DerivedCategory.TStructure.t.truncLE (-m - 1)).obj ωX.obj ⟶ ωX.obj,
      g = 0 := by
    intro g
    let Φ := ((fullyFaithfulHomAddEquiv (ObjectProperty.fullyFaithfulι _)
        (truncLEQuasiCoherent ωX (-m - 1)) ωX).symm.trans <|
      (((twistedInverseImageAdjunction f hpush).homAddEquiv
        (truncLEQuasiCoherent ωX (-m - 1)) ωS).symm).trans <|
      fullyFaithfulHomAddEquiv (Functor.FullyFaithful.ofFullyFaithful
        (derivedGlobalSectionsQuasicoherent (CommRingCat.of A)))
        ((quasiCoherentDerivedPushforward f hpush).obj
          (truncLEQuasiCoherent ωX (-m - 1))) ωS)
    refine Φ.injective (Eq.trans ?_ (map_zero Φ).symm)
    exact DerivedCategory.TStructure.t.zero_of_isLE_of_isGE (Φ g) (-e - 1) (-e) (by omega)
      h2 hgeA
  refine (DerivedCategory.isGE_iff ωX.obj (-m)).2 fun j hj => ?_
  exact isZero_of_isIso_of_eq_zero
    ((DerivedCategory.homologyFunctor X.Modules j).map
      ((DerivedCategory.TStructure.t.truncLEι (-m - 1)).app ωX.obj))
    (Stacks.DerivedTruncation.isIso_homologyMap_truncLEι ωX.obj (-m - 1) j (by omega))
    ((congrArg (fun z => (DerivedCategory.homologyFunctor X.Modules j).map z)
      (hzero ((DerivedCategory.TStructure.t.truncLEι (-m - 1)).app ωX.obj))).trans
      (Functor.map_zero _ _ _))

end AffineBase

/-! ### The second input: a normalized dualizing complex over the local base -/

/-- **`H^j(ω_A^•) = 0` for `j < -dim(A)`**, read at the locally small derived category of
`A`-modules: a normalized dualizing complex over a Noetherian local ring of dimension `n` lies
in `D^{≥ -n}`.

This is the second of the three inputs for the last equality of [Stacks, Tag 0AWP], and it is
the `M = A` case of [Stacks, Tag 0A7U], proved as
`Dualizing.isZero_homology_of_lt_neg_ringKrullDim`. That statement is at
`CategoryTheory.HasDerivedCategory.standard`, where the dualizing-complex development of
`StacksFrontier/RingTheory/Dualizing/` is stated, while the duality of [Stacks, Tag 0A9E] and hence
the chain above live at the locally small `ModuleCat.hasDerivedCategory` — at the standard model
the morphisms of `D(𝒪_X)` are one universe too high for Brown representability. The two models
are compared by `StacksDraft.DerivedModel.modelEquiv`, and
`StacksDraft.DerivedModel.isGE_modelEquiv_iff` says that a cohomological bound is invariant
under that comparison, which is all that is needed: the hypothesis is that `ω_A^•`, transported
to the standard model, is a normalized dualizing complex. -/
theorem isGE_of_isNormalizedDualizingComplex {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : Dualizing.IsNormalizedDualizingComplex.{u, u}
      ((StacksDraft.DerivedModel.modelEquiv (ModuleCat.hasDerivedCategory (R := A))
        (HasDerivedCategory.standard (ModuleCat.{u} A))).functor.obj ωA))
    (n : ℕ) (hn : ringKrullDim A = (n : WithBot ℕ∞)) : ωA.IsGE (-(n : ℤ)) := by
  rw [← StacksDraft.DerivedModel.isGE_modelEquiv_iff
    (ModuleCat.hasDerivedCategory (R := A)) (HasDerivedCategory.standard (ModuleCat.{u} A))]
  rw [@DerivedCategory.isGE_iff (ModuleCat.{u} A) _ _
    (HasDerivedCategory.standard (ModuleCat.{u} A))]
  intro j hj
  exact Dualizing.isZero_homology_of_lt_neg_ringKrullDim _ hωA n hn j (by omega)

/-- **A lower bound for `RΓ(Spec A, ω_S^•)` is a lower bound for `ω_S^•`.** On the affine
`Spec A` the degree-`j` cohomology of `RΓ(Spec A, ω_S^•)` is the module of global sections of
the quasi-coherent sheaf `H^j(ω_S^•)`
(`AlgebraicGeometry.derivedGlobalSectionsQuasicoherentCompHomologyIso`), and a quasi-coherent
module on an affine scheme with no global sections is zero. -/
theorem isGE_obj_of_isGE_derivedGlobalSectionsQuasicoherent {A : Type u} [CommRing A]
    (ωS : quasiCoherentDerivedCategory (Spec (CommRingCat.of A))) (c : ℤ)
    (h : ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj ωS).IsGE c) :
    ωS.obj.IsGE c := by
  rw [DerivedCategory.isGE_iff]
  intro j hj
  let := ωS.property j
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
      ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj ωS)) :=
    DerivedCategory.isZero_of_isGE _ c j hj
  have hΓ : IsZero ((globalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).obj
      ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules j).obj ωS.obj)) :=
    IsZero.of_iso hz ((AlgebraicGeometry.derivedGlobalSectionsQuasicoherentCompHomologyIso
      (CommRingCat.of A) j).app ωS).symm
  refine Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_sections_of_isAffine _ ?_
  exact isZero_of_isZero_of_subsingleton hΓ id

/-- **Part (1) of [Stacks, Tag 0AWN] over a Noetherian local base.** Let `f : X ⟶ Spec A` be
proper with closed fibre of dimension at most `d`, let `ω_A^• = RΓ(Spec A, ω_S^•)` lie in
`D^{≥ -e}`, and let `m = d + e`. Then `ω_X^• = f^×ω_S^•` has no cohomology below degree `-m`.

`ω_S^•` lies in `D^{≥ -e}` with `ω_A^•`
(`Stacks.Duality.isGE_obj_of_isGE_derivedGlobalSectionsQuasicoherent`), so by
[Stacks, Tag 0A9I] (`Stacks.Duality.exists_isGE_twistedInverseImage_obj`) the complex `ω_X^•` is
bounded below, and `Stacks.Duality.isGE_relativeDualizingComplex_of_isGE` sharpens that bound to
`-m`. At `m = dim(X)` this is the vanishing the source's first equality uses. -/
theorem isGE_relativeDualizingComplex_of_closedFibre_dim_le {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [IsProper f] (ωS : quasiCoherentDerivedCategory (Spec (CommRingCat.of A)))
    (d : ℕ) (hdim : topologicalKrullDim (f.fiber (IsLocalRing.closedPoint A)) ≤
      (d : WithBot ℕ∞))
    (m e : ℤ) (hm : m = (d : ℤ) + e)
    (hgeA : ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj ωS).IsGE (-e)) :
    (relativeDualizingComplex f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS).obj.IsGE (-m) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨N, hN⟩ := exists_isGE_twistedInverseImage_obj f
  exact isGE_relativeDualizingComplex_of_isGE f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS d hdim m e (-e - N) hm
    (hN ωS (-e) (isGE_obj_of_isGE_derivedGlobalSectionsQuasicoherent ωS (-e) hgeA)) hgeA

/-! ### [Stacks, Tag 0AWP] over a Noetherian local base -/

/-- **The chain of [Stacks, Tag 0AWP] over a Noetherian local base, with `H^d` read as
hypercohomology.** Let `(A, 𝔪, κ)` be a Noetherian local ring of dimension `e`, let
`f : X ⟶ Spec A` be proper with closed fibre of dimension at most `d` and with `dim(X) = d + e`,
let `ω_S^•` be an object of `D_QCoh(𝒪_{Spec A})` corresponding to a normalized dualizing complex
`ω_A^•`, and let `ω_X = H^{-dim(X)}(f^×ω_S^•)`. Then for every quasi-coherent `ℱ`

  `Hom_{𝒪_X}(ℱ, ω_X) ≅ Hom_A(H^d(RΓ(Spec A, Rf_*ℱ)), ω_A)`,   `ω_A = H^{-e}(ω_A^•)`.

The inputs are all discharged: the adjunction of [Stacks, Tag 0A9E] by
`AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward`, the vanishing of
`H^i(X, ℱ)` above the closed-fibre dimension by
`Stacks.Duality.isLE_derivedPushforwardSections_single`, the vanishing of `H^j(ω_A^•)` below
`-dim(A)` by `Stacks.Duality.isGE_of_isNormalizedDualizingComplex`, and part (1) of
[Stacks, Tag 0AWN] by `Stacks.Duality.isGE_relativeDualizingComplex_of_closedFibre_dim_le`.
`Stacks.Duality.dualizingModuleHomAddEquiv` replaces the hypercohomology by the classical
`H^d(X, ℱ)`. -/
def relativeDualizingModuleRepresentabilityOverLocalBase {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [IsProper f] (ωS : quasiCoherentDerivedCategory (Spec (CommRingCat.of A)))
    (hωA : Dualizing.IsNormalizedDualizingComplex.{u, u}
      ((StacksDraft.DerivedModel.modelEquiv (ModuleCat.hasDerivedCategory (R := A))
        (HasDerivedCategory.standard (ModuleCat.{u} A))).functor.obj
          ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj ωS)))
    (d e : ℕ) (he : ringKrullDim A = (e : WithBot ℕ∞))
    (hfib : topologicalKrullDim (f.fiber (IsLocalRing.closedPoint A)) ≤ (d : WithBot ℕ∞))
    (hdimX : topologicalKrullDim X = ((d + e : ℕ) : WithBot ℕ∞))
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    (F ⟶ relativeDualizingModule f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS) ≃+
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (d : ℤ)).obj
          (derivedPushforwardSections f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
            (singleQuasiCoherent F hF 0)) ⟶
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(e : ℤ))).obj
          ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj ωS)) :=
  (homCongrAddEquiv (Iso.refl F) (eqToIso (relativeDualizingModule_eq_homology f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS hdimX))).trans <|
  (homCongrAddEquiv (Iso.refl F) (eqToIso (congrArg
    (fun i => (DerivedCategory.homologyFunctor X.Modules i).obj
      (relativeDualizingComplex f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS).obj)
    (show -((d + e : ℕ) : ℤ) = -(((d + e : ℕ) : ℤ)) from rfl)))).trans <|
  (affineBaseDualityAddEquiv f (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS
      ((d + e : ℕ) : ℤ) (e : ℤ) F hF
      (isGE_relativeDualizingComplex_of_closedFibre_dim_le f ωS d hfib
        ((d + e : ℕ) : ℤ) (e : ℤ) (by push_cast; omega)
        (isGE_of_isNormalizedDualizingComplex _ hωA e he))
      (by
        have := isLE_derivedPushforwardSections_single f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f) d hfib F hF
        exact DerivedCategory.TStructure.t.isLE_of_le _ (d : ℤ) _ (by push_cast; omega))
      (isGE_of_isNormalizedDualizingComplex _ hωA e he)).trans <|
  homCongrAddEquiv (eqToIso (congrArg
    (fun i => (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (derivedPushforwardSections f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (singleQuasiCoherent F hF 0)))
    (show (((d + e : ℕ) : ℤ) - (e : ℤ)) = (d : ℤ) by push_cast; omega))) (Iso.refl _)

/-- Transport along an equality of degrees commutes with the maps the cohomology functors
induce. -/
theorem eqToHom_homologyFunctor_naturality {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory.{u} C] {K L : DerivedCategory C} (v : K ⟶ L) {i j : ℤ} (h : i = j) :
    eqToHom (congrArg (fun n => (DerivedCategory.homologyFunctor C n).obj K) h) ≫
        (DerivedCategory.homologyFunctor C j).map v =
      (DerivedCategory.homologyFunctor C i).map v ≫
        eqToHom (congrArg (fun n => (DerivedCategory.homologyFunctor C n).obj L) h) := by
  subst h
  simp

/-- **[Stacks, Tag 0AWP] over a Noetherian local base is natural in the module**: precomposing a
map `𝒢 ⟶ ω_X` with `u : ℱ ⟶ 𝒢` corresponds to precomposing the functional on `H^d(X, 𝒢)` with
`H^d(X, u)`. This is what makes `ω_X` *represent* the functor `ℱ ↦ Hom_A(H^d(X, ℱ), ω_A)`
rather than merely have the right Hom-groups. -/
theorem relativeDualizingModuleRepresentabilityOverLocalBase_naturality {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [IsProper f] (ωS : quasiCoherentDerivedCategory (Spec (CommRingCat.of A)))
    (hωA : Dualizing.IsNormalizedDualizingComplex.{u, u}
      ((StacksDraft.DerivedModel.modelEquiv (ModuleCat.hasDerivedCategory (R := A))
        (HasDerivedCategory.standard (ModuleCat.{u} A))).functor.obj
          ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj ωS)))
    (d e : ℕ) (he : ringKrullDim A = (e : WithBot ℕ∞))
    (hfib : topologicalKrullDim (f.fiber (IsLocalRing.closedPoint A)) ≤ (d : WithBot ℕ∞))
    (hdimX : topologicalKrullDim X = ((d + e : ℕ) : WithBot ℕ∞))
    {F G : X.Modules} (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) (u : F ⟶ G)
    (φ : G ⟶ relativeDualizingModule f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS) :
    relativeDualizingModuleRepresentabilityOverLocalBase f ωS hωA d e he hfib hdimX F hF
        (u ≫ φ) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (d : ℤ)).map
          ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).map
            ((quasiCoherentDerivedPushforward f
                (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
              (ObjectProperty.homMk ((DerivedCategory.singleFunctor X.Modules 0).map u) :
                singleQuasiCoherent F hF 0 ⟶ singleQuasiCoherent G hG 0))) ≫
        relativeDualizingModuleRepresentabilityOverLocalBase f ωS hωA d e he hfib hdimX G hG
          φ := by
  simp only [relativeDualizingModuleRepresentabilityOverLocalBase, AddEquiv.trans_apply,
    homCongrAddEquiv_apply, Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id,
    eqToIso.hom, eqToIso.inv, Category.assoc]
  rw [affineBaseDualityAddEquiv_naturality, ← Category.assoc, ← Category.assoc,
    eqToHom_homologyFunctor_naturality _ (by push_cast; omega), Category.assoc]

/-! ### The `A`-module `H^d(X, ℱ)` -/

section Cohomology

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- **A quasi-coherent module placed in degree zero**, as a functor from the quasi-coherent
`𝒪_X`-modules to `D_QCoh(𝒪_X)`. Its value at `ℱ` is `Stacks.Duality.singleQuasiCoherent ℱ _ 0`. -/
def singleQuasiCoherentFunctor :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      quasiCoherentDerivedCategory X :=
  ObjectProperty.lift _
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ DerivedCategory.singleFunctor X.Modules 0)
    (fun F => (singleQuasiCoherent F.obj F.property 0).property)

/-- The ring homomorphism `A ⟶ Γ(X, 𝒪_X)` of a scheme over `A` factors through
`Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`. -/
theorem baseScalars_eq_comp :
    Stacks.LocalCohomology.baseScalars A f =
      f.appTop.hom.comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (𝟙 (Spec (CommRingCat.of A)) : Spec (CommRingCat.of A) ⟶ _).appTop).hom := by
  have h1 : f.appLE ⊤ ⊤ (by simp) = f.appTop := Scheme.Hom.appLE_eq_app f
  rw [Stacks.LocalCohomology.baseScalars, h1, Scheme.Hom.id_appTop, Category.comp_id,
    CommRingCat.hom_comp]

variable [QuasiCompact f] [QuasiSeparated f]
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)

/-- **`H^d(RΓ(Spec A, Rf_*ℱ)) = H^d(X, ℱ)` as `A`-modules, naturally in the quasi-coherent
`ℱ`.** The right side is `Stacks.LocalCohomology.cohomologyOverBaseFunctor`, the `d`-th right
derived functor of `A`-linear global sections. The identification is: the cohomology of derived
global sections on the affine `Spec A` is the global sections of the cohomology sheaf
(`AlgebraicGeometry.derivedGlobalSectionsQuasicoherentCompHomologyIso`); the cohomology sheaf of
`Rf_*(ℱ[0])` is `R^d f_*ℱ`
(`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`); over an affine base the
global sections of `R^d f_*ℱ` are `H^d(X, ℱ)`, which is [Stacks, Tag 01XK]
(`Stacks.Cohomology.AffineBase.affineBaseHigherDirectImageIso`); and restriction of scalars
along `A ⟶ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)` is restriction along the composite and commutes with
right derivation (`Stacks.LocalCohomology.rightDerivedSectionsOverBaseIso`). -/
def derivedPushforwardSectionsHomologyIso (d : ℕ) :
    singleQuasiCoherentFunctor ⋙ quasiCoherentDerivedPushforward f hpush ⋙
        derivedGlobalSectionsQuasicoherent (CommRingCat.of A) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) (d : ℤ) ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
        Stacks.LocalCohomology.cohomologyOverBaseFunctor.{u, u} A f d :=
  Functor.isoWhiskerLeft (singleQuasiCoherentFunctor ⋙ quasiCoherentDerivedPushforward f hpush)
      (AlgebraicGeometry.derivedGlobalSectionsQuasicoherentCompHomologyIso (CommRingCat.of A) d) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι
      (Functor.isoWhiskerRight
        (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
          (Scheme.Modules.pushforward f) (derivedPushforward f) (derivedPushforwardUnitAtModel f)
          (Scheme.Modules.exists_quasiIso_isKInjective X) d)
        (globalSectionsOver (𝟙 (Spec (CommRingCat.of A))))) ≪≫
    Functor.isoWhiskerRight (Stacks.Cohomology.AffineBase.affineBaseHigherDirectImageIso f d).symm
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (𝟙 (Spec (CommRingCat.of A)) : Spec (CommRingCat.of A) ⟶ _).appTop).hom) ≪≫
    Functor.isoWhiskerLeft ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
        (moduleGlobalSections X).rightDerived d)
      (ModuleCat.restrictScalarsComp' _ _ _ (baseScalars_eq_comp f)).symm ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι
      (Stacks.LocalCohomology.rightDerivedSectionsOverBaseIso.{u, u} A f d).symm

end Cohomology

/-! ### [Stacks, Tag 0AWP]: the representation -/

section Representability

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
  (ωS : quasiCoherentDerivedCategory (Spec (CommRingCat.of A)))
  (hωA : Dualizing.IsNormalizedDualizingComplex.{u, u}
    ((StacksDraft.DerivedModel.modelEquiv (ModuleCat.hasDerivedCategory (R := A))
      (HasDerivedCategory.standard (ModuleCat.{u} A))).functor.obj
        ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj ωS)))
  (d e : ℕ) (he : ringKrullDim A = (e : WithBot ℕ∞))
  (hfib : topologicalKrullDim (f.fiber (IsLocalRing.closedPoint A)) ≤ (d : WithBot ℕ∞))
  (hdimX : topologicalKrullDim X = ((d + e : ℕ) : WithBot ℕ∞))

/-- **`Hom_{𝒪_X}(ℱ, ω_X) = Hom_A(H^d(X, ℱ), ω_A)`**, with `H^d(X, ℱ)` the classical sheaf
cohomology of `ℱ` with its `A`-module structure
(`Stacks.LocalCohomology.cohomologyOverBaseFunctor`) and `ω_A = H^{-dim(A)}(ω_A^•)`. This is
`Stacks.Duality.relativeDualizingModuleRepresentabilityOverLocalBase` followed by the
identification `Stacks.Duality.derivedPushforwardSectionsHomologyIso` of the hypercohomology
`H^d(RΓ(Spec A, Rf_*ℱ))` with `H^d(X, ℱ)`. -/
def dualizingModuleHomAddEquiv (F : X.Modules) (hF : F.IsQuasicoherent) :
    (F ⟶ relativeDualizingModule f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS) ≃+
      ((Stacks.LocalCohomology.cohomologyOverBaseFunctor.{u, u} A f d).obj F ⟶
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(e : ℤ))).obj
          ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj ωS)) :=
  (relativeDualizingModuleRepresentabilityOverLocalBase f ωS hωA d e he hfib hdimX F hF).trans
    (precompAddEquiv ((derivedPushforwardSectionsHomologyIso f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f) d).app ⟨F, hF⟩))

/-- `Stacks.Duality.dualizingModuleHomAddEquiv` as a bijection of sets. -/
def dualizingModuleHomEquivCohomologyOverBase (F : X.Modules) (hF : F.IsQuasicoherent) :
    (F ⟶ relativeDualizingModule f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS) ≃
      ((Stacks.LocalCohomology.cohomologyOverBaseFunctor.{u, u} A f d).obj F ⟶
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(e : ℤ))).obj
          ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj ωS)) :=
  (dualizingModuleHomAddEquiv f ωS hωA d e he hfib hdimX F hF).toEquiv

/-- **The identification `Hom_{𝒪_X}(ℱ, ω_X) = Hom_A(H^d(X, ℱ), ω_A)` is natural in `ℱ`**:
precomposing with `u : ℱ ⟶ 𝒢` corresponds to precomposing with `H^d(X, u)`. -/
theorem dualizingModuleHomAddEquiv_naturality {F G : X.Modules} (hF : F.IsQuasicoherent)
    (hG : G.IsQuasicoherent) (u : F ⟶ G)
    (φ : G ⟶ relativeDualizingModule f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS) :
    dualizingModuleHomAddEquiv f ωS hωA d e he hfib hdimX F hF (u ≫ φ) =
      (Stacks.LocalCohomology.cohomologyOverBaseFunctor.{u, u} A f d).map u ≫
        dualizingModuleHomAddEquiv f ωS hωA d e he hfib hdimX G hG φ := by
  refine Eq.trans (congrArg (fun z => ((derivedPushforwardSectionsHomologyIso f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f) d).app ⟨F, hF⟩).inv ≫ z)
    (relativeDualizingModuleRepresentabilityOverLocalBase_naturality f ωS hωA d e he hfib hdimX
      hF hG u φ)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫
      relativeDualizingModuleRepresentabilityOverLocalBase f ωS hωA d e he hfib hdimX G hG φ)
    ((derivedPushforwardSectionsHomologyIso f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f) d).inv.naturality
        (ObjectProperty.homMk u : (⟨F, hF⟩ : (SheafOfModules.isQuasicoherent
          X.ringCatSheaf).FullSubcategory) ⟶ ⟨G, hG⟩)).symm) ?_
  exact Category.assoc _ _ _

/-- **[Stacks, Tag 0AWP].** Let `(A, 𝔪, κ)` be a Noetherian local ring and let `ω_S^•` be an
object of `D_QCoh(𝒪_{Spec A})` corresponding to a normalized dualizing complex `ω_A^•`. Let
`f : X ⟶ Spec A` be proper, `ω_X^• = f^×ω_S^•` and `ω_X = H^{-dim(X)}(ω_X^•)`, as in
Example [Stacks, Tag 0AWI]. Let `d` bound the dimension of the closed fibre `X_s` and suppose
`dim(X) = d + dim(A)`. Then `ω_X` represents the functor

  `ℱ ↦ Hom_A(H^d(X, ℱ), ω_A)`,   `ω_A = H^{-dim(A)}(ω_A^•)`,

on the quasi-coherent `𝒪_X`-modules — so in particular on the coherent ones.

The represented functor is `ℱ ↦ Hom_A(H^d(X, ℱ), ω_A)` with `H^d(X, ℱ)` the classical sheaf
cohomology with its `A`-module structure, and the representation is
`Stacks.Duality.dualizingModuleHomAddEquiv`, natural by
`Stacks.Duality.dualizingModuleHomAddEquiv_naturality`. Nothing is carried: part (1) of
[Stacks, Tag 0AWN], the vanishing of `H^i(ω_X^•)` below `-dim(X)` that the source's first
equality needs, is `Stacks.Duality.isGE_relativeDualizingComplex_of_closedFibre_dim_le`. -/
@[stacks 0AWP "the whole lemma, in the setting of Example 0AWI with omega_X^bullet the twisted \
inverse image of omega_S^bullet (the relative dualizing complex of the 0AWI definition) and \
omega_A = H^{-dim A}(omega_A^bullet); the functor is represented on all quasi-coherent modules, \
which contain the coherent ones, and d may be any upper bound for dim(X_s) with \
dim(X) = d + dim(A)"]
def dualizingModuleRepresentableBy :
    (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
        Stacks.LocalCohomology.cohomologyOverBaseFunctor.{u, u} A f d).op ⋙
      yoneda.obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(e : ℤ))).obj
        ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj ωS))).RepresentableBy
      (⟨relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS,
        isQuasicoherent_relativeDualizingModule f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS⟩ :
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) where
  homEquiv {F} := (ObjectProperty.fullyFaithfulι _).homEquiv.trans
    (dualizingModuleHomEquivCohomologyOverBase f ωS hωA d e he hfib hdimX F.obj F.property)
  homEquiv_comp {F F'} u φ :=
    dualizingModuleHomAddEquiv_naturality f ωS hωA d e he hfib hdimX F.property F'.property
      u.hom φ.hom

end Representability

end Stacks.Duality

end
