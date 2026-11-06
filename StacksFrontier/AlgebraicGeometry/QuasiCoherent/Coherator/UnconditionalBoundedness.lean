module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCoherator
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.UniformBoundAnyModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsAlongIsomorphism
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineSectionsComparison
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.DerivedPushforwardCommutation
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardAnyModel
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.UnboundedMayerVietoris
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksCore.Tactic.StacksAttribute

/-!
# Boundedness of the coherator, without hypotheses

Let `X` be a quasi-compact and quasi-separated scheme and let `DQ_X : D(𝒪_X) ⥤ D_QCoh(𝒪_X)` be a
coherator of `X`, i.e. an exact right adjoint of the inclusion `ι : D_QCoh(𝒪_X) ⥤ D(𝒪_X)`
([Stacks, Tag 0CR0]). This file proves [Stacks, Tag 0CSA]: there is an integer `N` depending only
on `X` and on `DQ_X` such that for every `K` in `D(𝒪_X)` and all integers `a`, `b`, if
`H^i(U, K) = 0` for every affine open `U ⊆ X` and every `i ∉ [a, b]`, then the cohomology sheaves
of `DQ_X(K)` vanish outside `[a, b + N]`.

`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/Boundedness.lean` runs the source's
induction over the quasi-compact opens of `X`
(`Stacks.Duality.Coherator.exists_isGE_isLE_coherator_obj`) from three inputs, which it takes as
arguments. This file supplies all three and so states the tag with nothing but `X` and the
coherator:

* the two Mayer–Vietoris triangles of [Stacks, Tag 08BV] are
  `Stacks.Duality.Coherator.isMayerVietorisApex_restrictPushforward_sup` and
  `Stacks.Duality.Coherator.isMayerVietorisApex_self`, already in the shape
  `Stacks.Duality.Coherator.IsMayerVietorisApex` the estimates consume;
* the affine base case is proved here, as
  `Stacks.Duality.Coherator.hasCoheratorBoundAt_of_isAffineOpen`.

## The affine base case

Let `U` be an affine open of `X`, write `Λ = Γ(X, U)` and let `φ : Spec Λ ⟶ X` be the open
immersion `AlgebraicGeometry.IsAffineOpen.fromSpec`. The source takes `N(U) = 0` for the coherator
of the open subscheme `U` and then pays the finitely many degrees of [Stacks, Tag 08D5] for
`Rj_{U,*}`; the predicate `Stacks.Duality.Coherator.HasCoheratorBoundAt` the induction runs on is
about `DQ_X(Rj_{U,*}(K|_U))`, so that is exactly the shape of the argument here. In four steps:

* **the coherator of `Spec Λ` is `RΓ(Spec Λ, -)` followed by sheafification.** Derived
  sheafification `D(Λ) ⥤ D_QCoh(𝒪_{Spec Λ})` is an equivalence ([Stacks, Tag 06Z0],
  `AlgebraicGeometry.derivedTilde_isEquivalence`) and, followed by `ι`, is left adjoint to
  `RΓ(Spec Λ, -)` (`AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction`). Composing the
  inverse equivalence with that adjunction exhibits `RΓ(Spec Λ, -) ⋙ (-)^~` as a right adjoint of
  `ι`, which is `Stacks.Duality.Coherator.specCoheratorAdjunction`; this is [Stacks, Tag 08D9]
  part (2) in the form the coherator of [Stacks, Tag 0CR0] is stated in. Its cohomology sheaves
  are then read off those of `RΓ(Spec Λ, -)`, sheafification being exact, which is the whole of
  the amplitude estimate on the affine: no degree is lost.
* **`RΓ(Spec Λ, K|_{Spec Λ})` is `RΓ(U, K)`**, which is where the hypothesis of the tag enters:
  `Stacks.Duality.Coherator.nonempty_iso_derivedGlobalSectionsFromSpec`. This is
  `AlgebraicGeometry.IsAffineOpen.nonempty_iso_derivedSectionsSpec` read at the locally small
  model; see the implementation notes.
* **`Rj_{U,*}(K|_U)` is `Rφ_*(K|_{Spec Λ})`**, which lets the whole argument happen on `Spec Λ`
  rather than on the affine scheme `U`:
  `Stacks.Duality.Coherator.nonempty_iso_restrictPushforwardFromSpec`. The two differ by the
  isomorphism `AlgebraicGeometry.IsAffineOpen.isoSpec`, along which restriction of modules is an
  equivalence, so the unit `M ⟶ R(j_U^{-1}φ)_*((j_U^{-1}φ)^*M)` is invertible.
* **the direct image `Rφ_*` costs finitely many degrees at the top and none at the bottom**: the
  first is [Stacks, Tag 08D5] part (2),
  `Stacks.Duality.exists_isLE_derivedPushforward_obj_anyModel`, and the second is left t-exactness
  of a total right derived functor, `Stacks.DerivedFunctor.isGE_totalRightDerived_obj`. The two are
  glued to the coherator of `Spec Λ` by [Stacks, Tag 0CR1],
  `Stacks.Duality.coheratorDerivedPushforwardIso`, which identifies `Rφ_*DQ_{Spec Λ}` with
  `DQ_XRφ_*`.

## Main definitions

* `Stacks.Duality.Coherator.specCoherator` — the coherator of an affine scheme `Spec R`, namely
  `RΓ(Spec R, -) ⋙ (-)^~`.
* `Stacks.Duality.Coherator.specCoheratorAdjunction` — it is a right adjoint of `ι`.

## Main results

* `Stacks.Duality.Coherator.isGE_isLE_specCoherator` — on `Spec R` the coherator has the exact
  amplitude of derived global sections.
* `Stacks.Duality.Coherator.hasCoheratorBoundAt_of_isAffineOpen` — the affine base case of the
  induction.
* `Stacks.Duality.Coherator.exists_isGE_isLE_coherator_obj_of_qcqs` — **[Stacks, Tag 0CSA]**.
* `Stacks.Duality.Coherator.exists_coherator_isGE_isLE_obj_of_qcqs` — the same with the coherator
  produced by [Stacks, Tag 0CR0] rather than given, so that nothing at all is assumed beyond `X`
  being quasi-compact and quasi-separated.

## Implementation notes

*The model.* Everything is at the locally small derived categories of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, which instance search supplies, because
that is the model the coherator of [Stacks, Tag 0CR0] and the vocabulary of [Stacks, Tag 0CR2]
live at. Three results used here are stated in the import closure only at
`CategoryTheory.HasDerivedCategory.standard` and are therefore reproved at a free model:
`AlgebraicGeometry.IsAffineOpen.nonempty_iso_derivedSectionsSpec` — whose own inputs, the
identification `AlgebraicGeometry.IsAffineOpen.restrictFromSpecGlobalSectionsIso` of sections and
the two K-injectivity statements of [Stacks, Tag 08BS], mention no derived category and are
reused as they stand — and the two lemmas
`CategoryTheory.exists_isKInjective_representative` and `CategoryTheory.rightDerivedObjIso` of
`StacksFrontier/Algebra/Homology/DerivedCategory/KInjectiveRepresentative.lean`, which carry a
`[HasDerivedCategory.{u + 1}]` binder. The two private copies below,
`Stacks.Duality.Coherator.rightDerivedObjIsoAnyModel` and
`Stacks.Duality.Coherator.exists_isKInjective_isoAnyModel`, are those proofs with the model left
free; the K-injective criterion of [Stacks, Tag 070K] they rest on,
`Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective`, is itself model-free.

*Why `Spec Γ(X, U)` and not the affine open subscheme `U`.* An affine scheme is isomorphic to a
spectrum, not equal to one, and the affine input of the base case — derived sheafification being
an equivalence whose composite with `ι` has `RΓ` as right adjoint — is available on a spectrum
only. Transporting it along `AlgebraicGeometry.IsAffineOpen.isoSpec` would mean transporting an
adjunction, a derived category and a quasi-coherence property; instead the pair `(φ^*, Rφ_*)` for
`φ : Spec Γ(X, U) ⟶ X` is used throughout, and the single transport that remains is the one
identifying `Rφ_*φ^*` with `Rj_{U,*}j_U^*`, which is uniqueness of right adjoints together with
invertibility of the unit of `(ψ^*, Rψ_*)` for the isomorphism `ψ`.

## References

* [Stacks Project, Tag 0CSA](https://stacks.math.columbia.edu/tag/0CSA)
* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
* [Stacks Project, Tag 0CR1](https://stacks.math.columbia.edu/tag/0CR1)
* [Stacks Project, Tag 0CR2](https://stacks.math.columbia.edu/tag/0CR2)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 08BS](https://stacks.math.columbia.edu/tag/08BS)
* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08D9](https://stacks.math.columbia.edu/tag/08D9)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Duality

universe w u

namespace Stacks.Duality.Coherator

/-! ### Computing a right derived functor on a K-injective complex, at any model -/

/-- A right derived functor is computed by the functor itself on a K-injective complex, at an
arbitrary model of the two derived categories. This is `CategoryTheory.rightDerivedObjIso` with
its `[HasDerivedCategory.{u + 1}]` binders left free; see the implementation notes. -/
private def rightDerivedObjIsoAnyModel {C : Type (u + 1)} [Category.{u} C] [Abelian C]
    [IsGrothendieckAbelian.{u} C] [HasDerivedCategory.{w} C]
    {A : Type (u + 1)} [Category.{u} A] [Abelian A] [HasDerivedCategory.{w} A]
    (F : C ⥤ A) (hF : F.Additive)
    (RF : DerivedCategory C ⥤ DerivedCategory A)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)))
    (I : CochainComplex C ℤ) (hI : I.IsKInjective) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      RF.obj (DerivedCategory.Q.obj I) := by
  have : IsIso (α.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ RF α I
  exact (DerivedCategory.quotientCompQhIso A).symm.app _ ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm.app I) ≪≫
    asIso (α.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)) ≪≫
    RF.mapIso ((DerivedCategory.quotientCompQhIso C).app I)

/-- Every object of the unbounded derived category of a Grothendieck abelian category is
represented by a K-injective complex, at an arbitrary model. This is
`CategoryTheory.exists_isKInjective_representative` with its `[HasDerivedCategory.{u + 1}]` binder
left free. -/
private theorem exists_isKInjective_isoAnyModel {C : Type (u + 1)} [Category.{u} C] [Abelian C]
    [IsGrothendieckAbelian.{u} C] [HasDerivedCategory.{w} C] (E : DerivedCategory C) :
    ∃ I : CochainComplex C ℤ, I.IsKInjective ∧ Nonempty (DerivedCategory.Q.obj I ≅ E) := by
  obtain ⟨I, i, hI, hi⟩ :=
    Stacks.Cohomology.Localization.enoughKInjectives (DerivedCategory.Q.objPreimage E)
  exact ⟨I, hI, ⟨(asIso (DerivedCategory.Q.map i)).symm ≪≫
    DerivedCategory.Q.objObjPreimageIso E⟩⟩

/-! ### The coherator of an affine scheme -/

/-- **The coherator of the affine scheme `Spec R`**: derived global sections `RΓ(Spec R, -)`
followed by derived sheafification `(-)^~ : D(R) ⥤ D_QCoh(𝒪_{Spec R})`.

That this is a right adjoint of `ι` is `Stacks.Duality.Coherator.specCoheratorAdjunction`; this is
[Stacks, Tag 08D9] part (2) in the shape [Stacks, Tag 0CR0] states the coherator in. -/
def specCoherator (R : CommRingCat.{u}) :
    DerivedCategory (Spec R).Modules ⥤ quasiCoherentDerivedCategory (Spec R) :=
  derivedGlobalSectionsOver (𝟙 (Spec R)) ⋙ derivedTilde R

/-- **The coherator of an affine scheme is a right adjoint of
`Stacks.Duality.Coherator.quasiCoherentι`.** Derived sheafification `T : D(R) ⥤ D_QCoh(𝒪_{Spec R})`
is an equivalence ([Stacks, Tag 06Z0]) and `T ⋙ ι ⊣ RΓ(Spec R, -)`; composing `T⁻¹ ⊣ T` with that
adjunction gives `T⁻¹ ⋙ T ⋙ ι ⊣ RΓ(Spec R, -) ⋙ T`, and the counit of the equivalence identifies
the left-hand side with `ι`. -/
def specCoheratorAdjunction (R : CommRingCat.{u}) :
    quasiCoherentι (Spec R) ⊣ specCoherator R :=
  Adjunction.ofNatIsoLeft
    (((derivedTilde R).asEquivalence.symm.toAdjunction).comp
      (derivedTildeGlobalSectionsAdjunction R).val)
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedTilde R).asEquivalence.counitIso
        (quasiCoherentι (Spec R)) ≪≫ Functor.leftUnitor _)

/-- The cohomology sheaves of `ι(DQ_{Spec R}(L))` are the sheafifications of the cohomology
modules of `RΓ(Spec R, L)`: in particular one vanishes as soon as the other does.

Derived sheafification agrees with the termwise sheafification of complexes
(`AlgebraicGeometry.derivedTildeCompι`), and termwise sheafification is exact, so it commutes
with the cohomology functors of the derived categories. -/
theorem isZero_homology_specCoherator (R : CommRingCat.{u})
    (L : DerivedCategory (Spec R).Modules) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((derivedGlobalSectionsOver (𝟙 (Spec R))).obj L))) :
    IsZero ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj
      ((quasiCoherentι (Spec R)).obj ((specCoherator R).obj L))) :=
  IsZero.of_iso ((tilde.functor R).map_isZero h)
    ((DerivedCategory.homologyFunctor (Spec R).Modules i).mapIso
      ((derivedTildeCompι R).app ((derivedGlobalSectionsOver (𝟙 (Spec R))).obj L)) ≪≫
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (tilde.functor R) i).app _)

/-- **On an affine scheme the coherator has exactly the amplitude of derived global sections**: if
`RΓ(Spec R, L)` lives in degrees `[a, b]`, so do the cohomology sheaves of `DQ_{Spec R}(L)`. This
is the base case of [Stacks, Tag 0CSA] before the direct image is applied, and it loses no
degree, which is the source's `N = 0` on an affine. -/
theorem isGE_isLE_specCoherator (R : CommRingCat.{u})
    (L : DerivedCategory (Spec R).Modules) (a b : ℤ)
    (hge : ((derivedGlobalSectionsOver (𝟙 (Spec R))).obj L).IsGE a)
    (hle : ((derivedGlobalSectionsOver (𝟙 (Spec R))).obj L).IsLE b) :
    ((quasiCoherentι (Spec R)).obj ((specCoherator R).obj L)).IsGE a ∧
      ((quasiCoherentι (Spec R)).obj ((specCoherator R).obj L)).IsLE b := by
  constructor
  · rw [DerivedCategory.isGE_iff]
    intro i hi
    exact isZero_homology_specCoherator R L i (DerivedCategory.isZero_of_isGE _ a i hi)
  · rw [DerivedCategory.isLE_iff]
    intro i hi
    exact isZero_homology_specCoherator R L i (DerivedCategory.isZero_of_isLE _ b i hi)

/-! ### Sections over an affine open, read on its spectrum -/

/-- **Derived global sections on the spectrum of an affine open are the derived sections over that
open**, at the locally small model: for every object `K` of `D(𝒪_X)` the complex of
`Γ(X, U)`-modules `RΓ(Spec Γ(X, U), K|_{Spec Γ(X, U)})` is `RΓ(U, K)`. No quasi-coherence is
needed.

This is `AlgebraicGeometry.IsAffineOpen.nonempty_iso_derivedSectionsSpec` with the model left
free, which is what the coherator of [Stacks, Tag 0CR0] needs; its proof is that one, the two
sides being compared on a K-injective representative `I` of `K`, where each is computed by the
underlying functor of sections and the two agree by
`AlgebraicGeometry.IsAffineOpen.restrictFromSpecGlobalSectionsIso`. That the restriction of `I` to
`Spec Γ(X, U)` is again K-injective is [Stacks, Tag 08BS], in the two steps the restriction
factors into. The isomorphism is produced for a fixed object only; it is not claimed to be natural
in `K`. -/
theorem nonempty_iso_derivedGlobalSectionsFromSpec {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (K : DerivedCategory X.Modules) :
    Nonempty ((derivedGlobalSectionsOver (𝟙 (Spec Γ(X, U)))).obj
        ((OpenImmersion.derivedRestrict hU.fromSpec).obj K) ≅
      (derivedSectionsLocallySmall X U).obj K) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_isoAnyModel K
  have h₂ : CochainComplex.IsKInjective
      (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) :=
    Scheme.Modules.isKInjective_mapHomologicalComplex_restrictFunctor_of_isIso
      hU.isoSpec.inv _
      (Scheme.Modules.isKInjective_mapHomologicalComplex_restrictFunctor_ι U I hI)
  have hIS : CochainComplex.IsKInjective
      (((Scheme.Modules.restrictFunctor hU.fromSpec).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
    CochainComplex.isKInjective_of_iso
      ((Functor.mapHomologicalComplexCompIso hU.restrictCompIso (ComplexShape.up ℤ)).app I)
  have eΓ := rightDerivedObjIsoAnyModel (globalSectionsOver (𝟙 (Spec Γ(X, U)))) inferInstance
    (derivedGlobalSectionsOver (𝟙 (Spec Γ(X, U))))
    (derivedGlobalSectionsOverUnit (𝟙 (Spec Γ(X, U)))) inferInstance _ hIS
  have eU := rightDerivedObjIsoAnyModel (Stacks.Cohomology.sectionsFunctor X U) inferInstance
    (derivedSectionsLocallySmall X U) (derivedSectionsLocallySmallUnit X U) inferInstance I hI
  exact ⟨(derivedGlobalSectionsOver (𝟙 (Spec Γ(X, U)))).mapIso
      ((OpenImmersion.derivedRestrict hU.fromSpec).mapIso e.symm ≪≫
        (Scheme.Modules.restrictFunctor hU.fromSpec).mapDerivedCategoryFactors.app I) ≪≫
    eΓ.symm ≪≫ DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso hU.restrictFromSpecGlobalSectionsIso
        (ComplexShape.up ℤ)).app I) ≪≫ eU ≪≫
    (derivedSectionsLocallySmall X U).mapIso e⟩

/-! ### Direct image from the spectrum of an affine open -/

/-- **Restriction of modules along an isomorphism of schemes is an equivalence**, with inverse the
restriction along the inverse isomorphism: the two composites are the restrictions along the two
identities, by `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`. -/
def restrictEquivOfIsIso {Y Z : Scheme.{u}} (k : Y ⟶ Z) [IsIso k] : Z.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.restrictFunctor k)
    (Scheme.Modules.restrictFunctor (inv k))
    (Scheme.Modules.restrictFunctorId.symm ≪≫
      Scheme.Modules.restrictFunctorCongr (IsIso.inv_hom_id k).symm ≪≫
      Scheme.Modules.restrictFunctorComp (inv k) k)
    ((Scheme.Modules.restrictFunctorComp k (inv k)).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (IsIso.hom_inv_id k) ≪≫
      Scheme.Modules.restrictFunctorId)

/-- **Along an isomorphism of schemes the unit `M ⟶ Rk_*(k^*M)` is invertible.** Restriction along
an isomorphism is an equivalence of abelian categories, hence so is the functor it induces on the
unbounded derived categories, and the unit of an adjunction with fully faithful left adjoint is
invertible. -/
theorem isIso_unit_derivedRestrictPushforward_of_isIso {Y Z : Scheme.{u}} (k : Y ⟶ Z) [IsIso k] :
    IsIso (OpenImmersion.derivedRestrictPushforwardAdjunction k).unit := by
  have h : (Scheme.Modules.restrictFunctor k).IsEquivalence :=
    (restrictEquivOfIsIso k).isEquivalence_functor
  have : (OpenImmersion.derivedRestrict k).IsEquivalence :=
    Stacks.DerivedFunctor.isEquivalence_mapDerivedCategory (Scheme.Modules.restrictFunctor k)
  infer_instance

/-- **`Rj_{U,*}(K|_U)` is the derived direct image along `Spec Γ(X, U) ⟶ X` of the restriction of
`K` there**, for `U` an affine open of `X`.

The open immersion `φ = hU.fromSpec` is `ψ ≫ j_U` for the isomorphism
`ψ = hU.isoSpec.inv : Spec Γ(X, U) ⟶ U`, so `φ^*` is `ψ^* ∘ j_U^*`
(`AlgebraicGeometry.IsAffineOpen.restrictCompIso`) and therefore, right adjoints being unique,
`Rφ_*` is `Rj_{U,*} ∘ Rψ_*`. The unit `M ⟶ Rψ_*ψ^*M` is invertible by
`Stacks.Duality.Coherator.isIso_unit_derivedRestrictPushforward_of_isIso`. -/
theorem nonempty_iso_restrictPushforwardFromSpec {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (K : DerivedCategory X.Modules) :
    Nonempty ((derivedPushforward hU.fromSpec).obj
        ((OpenImmersion.derivedRestrict hU.fromSpec).obj K) ≅ restrictPushforward U K) := by
  have L := Functor.mapDerivedCategoryCompIsoOfCompIso hU.restrictCompIso
  have adjc := ((OpenImmersion.derivedRestrictPushforwardAdjunction U.ι).comp
    (OpenImmersion.derivedRestrictPushforwardAdjunction hU.isoSpec.inv)).ofNatIsoLeft L
  have eP := Adjunction.rightAdjointUniq
    (OpenImmersion.derivedRestrictPushforwardAdjunction hU.fromSpec) adjc
  have hunit := isIso_unit_derivedRestrictPushforward_of_isIso hU.isoSpec.inv
  exact ⟨eP.app _ ≪≫ (derivedPushforward U.ι).mapIso
    ((derivedPushforward hU.isoSpec.inv).mapIso (L.app K).symm ≪≫
      (asIso ((OpenImmersion.derivedRestrictPushforwardAdjunction hU.isoSpec.inv).unit.app
        ((OpenImmersion.derivedRestrict U.ι).obj K))).symm)⟩

/-! ### The affine base case -/

/-- **The affine base case of [Stacks, Tag 0CSA].** Let `X` be a quasi-compact quasi-separated
scheme, let `DQ_X` be a coherator of `X` and let `U` be an affine open of `X`. Then the localized
bound `Stacks.Duality.Coherator.HasCoheratorBoundAt` holds at `U`: there is an integer `N`,
independent of `K`, `a` and `b`, with the cohomology sheaves of `DQ_X(Rj_{U,*}(K|_U))` in
`[a, b + N]` whenever the hypercohomology of `K` over the affine opens of `X` lies in `[a, b]`.

Write `Λ = Γ(X, U)` and `φ : Spec Λ ⟶ X` for `AlgebraicGeometry.IsAffineOpen.fromSpec`. By
[Stacks, Tag 0CR1] the object `DQ_X(Rφ_*(K|_{Spec Λ}))` is `Rφ_*(DQ_{Spec Λ}(K|_{Spec Λ}))`; the
coherator of `Spec Λ` is derived global sections followed by sheafification, so that inner object
has the amplitude of `RΓ(Spec Λ, K|_{Spec Λ}) = RΓ(U, K)`, which is `[a, b]` by hypothesis; and
`Rφ_*` preserves the lower bound and raises the upper one by the integer of [Stacks, Tag 08D5]
part (2), which depends on `φ` alone. Finally `Rφ_*(K|_{Spec Λ})` is `Rj_{U,*}(K|_U)`. -/
theorem hasCoheratorBoundAt_of_isAffineOpen {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X]
    {DQ : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X}
    (adj : quasiCoherentι X ⊣ DQ) (U : X.Opens) (hU : IsAffineOpen U) :
    HasCoheratorBoundAt X DQ U := by
  have e0CR1 := coheratorDerivedPushforwardIso hU.fromSpec
    (isQuasicoherent_homology_derivedPushforward_of_qcqs hU.fromSpec)
    (specCoherator Γ(X, U)) DQ (specCoheratorAdjunction Γ(X, U)) adj
  obtain ⟨N, hN⟩ := exists_isLE_derivedPushforward_obj_anyModel hU.fromSpec
  refine ⟨N, fun a b K hK => ?_⟩
  obtain ⟨eSec⟩ := nonempty_iso_derivedGlobalSectionsFromSpec hU K
  obtain ⟨eF⟩ := nonempty_iso_restrictPushforwardFromSpec hU K
  set L := (OpenImmersion.derivedRestrict hU.fromSpec).obj K
  have hz := fun i (h : i < a ∨ b < i) => IsZero.of_iso (hK ⟨U, hU⟩ i h)
    ((DerivedCategory.homologyFunctor _ i).mapIso eSec)
  obtain ⟨hYge, hYle⟩ := isGE_isLE_specCoherator Γ(X, U) L a b
    ((DerivedCategory.isGE_iff _ _).2 fun i hi => hz i (Or.inl hi))
    ((DerivedCategory.isLE_iff _ _).2 fun i hi => hz i (Or.inr hi))
  have ecomp : (quasiCoherentι X).obj (DQ.obj (restrictPushforward U K)) ≅
      (derivedPushforward hU.fromSpec).obj
        ((quasiCoherentι (Spec Γ(X, U))).obj ((specCoherator Γ(X, U)).obj L)) :=
    (quasiCoherentι X).mapIso (DQ.mapIso eF.symm ≪≫ (e0CR1.app L).symm)
  have hgeφ := Stacks.DerivedFunctor.isGE_totalRightDerived_obj
    (Scheme.Modules.pushforward hU.fromSpec)
    ((quasiCoherentι (Spec Γ(X, U))).obj ((specCoherator Γ(X, U)).obj L)) a
  have hleφ := hN ((quasiCoherentι (Spec Γ(X, U))).obj ((specCoherator Γ(X, U)).obj L))
    ((specCoherator Γ(X, U)).obj L).2 b hYle
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso ecomp.symm a,
    DerivedCategory.TStructure.t.isLE_of_iso ecomp.symm (b + N)⟩

/-! ### Tag 0CSA -/

/-- **[Stacks, Tag 0CSA].** Let `X` be a quasi-compact and quasi-separated scheme and let
`DQ_X : D(𝒪_X) ⥤ D_QCoh(𝒪_X)` be a coherator of `X`, i.e. a right adjoint of the inclusion
`ι : D_QCoh(𝒪_X) ⥤ D(𝒪_X)` with the adjunction triangulated — the exact functor `DQ_X` of
[Stacks, Tag 0CR0]. Then there is an integer `N`, depending only on `X` and on `DQ_X` and in
particular not on `K`, `a` or `b`, such that for every object `K` of `D(𝒪_X)` and all integers
`a`, `b`, if `H^i(U, K) = 0` for every affine open `U ⊆ X` and every `i ∉ [a, b]`, then the
cohomology sheaves `H^i(DQ_X(K))` vanish for `i ∉ [a, b + N]`.

This is `Stacks.Duality.Coherator.exists_isGE_isLE_coherator_obj`, the source's induction over the
quasi-compact opens of `X` ([Stacks, Tag 08DR]), with its three inputs supplied: the two
Mayer–Vietoris triangles of [Stacks, Tag 08BV] are
`Stacks.Duality.Coherator.isMayerVietorisApex_restrictPushforward_sup` and
`Stacks.Duality.Coherator.isMayerVietorisApex_self`, and the affine base case is
`Stacks.Duality.Coherator.hasCoheratorBoundAt_of_isAffineOpen`. -/
@[stacks 0CSA]
theorem exists_isGE_isLE_coherator_obj_of_qcqs (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X]
    (DQ : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X)
    (adj : quasiCoherentι X ⊣ DQ) [DQ.CommShift ℤ] [adj.IsTriangulated] :
    ∃ N : ℤ, ∀ (a b : ℤ) (K : DerivedCategory X.Modules), AffineAmplitudeIn X a b K →
      ((quasiCoherentι X).obj (DQ.obj K)).IsGE a ∧
        ((quasiCoherentι X).obj (DQ.obj K)).IsLE (b + N) :=
  exists_isGE_isLE_coherator_obj X DQ adj
    isMayerVietorisApex_restrictPushforward_sup isMayerVietorisApex_self
    (fun U => hasCoheratorBoundAt_of_isAffineOpen adj U.1 U.2)

/-- **[Stacks, Tag 0CSA] with the coherator produced rather than given.** For a quasi-compact
quasi-separated scheme `X` there are a coherator `DQ_X` of `X`, exact and right adjoint to the
inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`, and an integer `N` such that the cohomology sheaves of
`DQ_X(K)` lie in `[a, b + N]` whenever the hypercohomology of `K` over the affine opens of `X`
lies in `[a, b]`.

The coherator is the one of [Stacks, Tag 0CR0],
`Stacks.Duality.Coherator.exists_isTriangulated_rightAdjoint_quasiCoherentι`, and the bound is
`Stacks.Duality.Coherator.exists_isGE_isLE_coherator_obj_of_qcqs`, which holds for every
coherator. -/
theorem exists_coherator_isGE_isLE_obj_of_qcqs (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] :
    ∃ (DQ : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X)
      (adj : quasiCoherentι X ⊣ DQ) (_ : DQ.CommShift ℤ) (_ : adj.IsTriangulated) (N : ℤ),
      ∀ (a b : ℤ) (K : DerivedCategory X.Modules), AffineAmplitudeIn X a b K →
        ((quasiCoherentι X).obj (DQ.obj K)).IsGE a ∧
          ((quasiCoherentι X).obj (DQ.obj K)).IsLE (b + N) := by
  obtain ⟨DQ, adj, hcs, htri⟩ := exists_isTriangulated_rightAdjoint_quasiCoherentι X
  exact ⟨DQ, adj, hcs, htri, exists_isGE_isLE_coherator_obj_of_qcqs X DQ adj⟩

end Stacks.Duality.Coherator

end
