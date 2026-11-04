module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.DeRhamTypeComplexAcyclicCover
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.DeRhamTypeComplexCech
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.RestrictScalarsCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.VanishingTransfer

/-!
# Hypercohomology of a bounded complex with coherent terms on a proper scheme

Let `f : X ⟶ S` be a proper morphism to an affine scheme with `A = Γ(S, 𝒪_S)` Noetherian, and
let `K^•` be a bounded below complex of sheaves of `f^{-1}𝒪_S`-modules on `X` each of whose terms
is (the restriction of scalars of) a coherent `𝒪_X`-module, the differentials being only
`f^{-1}𝒪_S`-linear, as for the de Rham complex `M ⊗ Ω^•_{X/S}` of a module with an integrable
connection. Write `RΓ(X, K^•) ∈ D(A)` for the derived global sections of `K^•`, computed in
sheaves of `f^{-1}𝒪_S`-modules and read over `A` along `A ⟶ Γ(X, f^{-1}𝒪_S)`.

1. The hypercohomology modules `H^j(X, K^•) = H^j(RΓ(X, K^•))` are finite `A`-modules, and they
   vanish for `j > b + t - 1` when `K^•` lives in degrees `≤ b` and `X` is covered by `t` affine
   opens.
2. For a finite cover `𝒰` of `X` by affine opens, `RΓ(X, K^•)` is computed by the total complex
   of the Čech double complex `∏ K^q(U_{i_0 … i_p})` over *ordered* tuples
   (`AlgebraicGeometry.DeRhamTypeComplex.totalCechComplex`): the canonical comparison of
   [Stacks, Tag 08BN] is an isomorphism in `D(A)`, natural in `K^•`. This holds for quasi-coherent
   terms and any cover by affine opens of a scheme with affine diagonal.
3. Consequently the cohomology of that total Čech complex is finite over `A` and vanishes in large
   degrees (`AlgebraicGeometry.DeRhamTypeComplex.moduleFinite_homology_totalCechComplex`,
   `AlgebraicGeometry.DeRhamTypeComplex.isZero_homology_totalCechComplex`).

## Main definitions

* `AlgebraicGeometry.DeRhamTypeComplex.derivedSections`: `RΓ(X, -) : D⁺(f^{-1}𝒪_S) ⥤ D(A)`.
* `AlgebraicGeometry.DeRhamTypeComplex.hypercohomology`: `H^j(X, K^•) = H^j(RΓ(X, K^•))`.
* `AlgebraicGeometry.DeRhamTypeComplex.totalCechToDerivedSections`: the comparison
  `Tot(Č^•(𝒰, K^•)) ⟶ RΓ(X, K^•)` in `D(A)`, natural in `K^•`.
* `AlgebraicGeometry.DeRhamTypeComplex.totalCechIsoDerivedSections` and
  `AlgebraicGeometry.DeRhamTypeComplex.totalCechNatIsoDerivedSections`: the comparison as an
  isomorphism, objectwise and as a natural isomorphism, for quasi-coherent terms.

## Main results

* `AlgebraicGeometry.DeRhamTypeComplex.isIso_totalCechToDerivedSections_app`: (2).
* `AlgebraicGeometry.DeRhamTypeComplex.moduleFinite_homology_derivedSections`,
  `AlgebraicGeometry.DeRhamTypeComplex.isZero_homology_derivedSections` and
  `AlgebraicGeometry.DeRhamTypeComplex.exists_isZero_homology_derivedSections`: (1).
* `AlgebraicGeometry.DeRhamTypeComplex.isZero_hypercohomology_of_lt`: vanishing below the bottom
  degree of `K^•`.
* `AlgebraicGeometry.DeRhamTypeComplex.isPseudoCoherent_derivedSections`: `RΓ(X, K^•)` is a
  pseudo-coherent object of `D(A)` for `K^•` bounded with coherent terms.

## The proof

(2) is the module-coefficient form of [Stacks, Tag 0FLH]
(`AlgebraicGeometry.DeRhamTypeComplex.isIso_cechToDerivedSections_app`): the terms of `K^•` have
no higher cohomology on the finite intersections of the cover, which are affine, by
[Stacks, Tag 01XB], the cohomology of a quasi-coherent `𝒪_X`-module being the same whether it is
computed over `𝒪_X` or over `f^{-1}𝒪_S`. (1) is then (3) read through (2).

## References

* [Stacks Project, Tag 0FLH](https://stacks.math.columbia.edu/tag/0FLH)
* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace ComplexShape
open Stacks.DeRhamDirectImage Stacks.Cohomology.CechSheaf Stacks.Cohomology.CechDerived

universe u

-- Sheafification on the opens of a space is the instance of the small site here; the instance for
-- enlarged coefficients would make the abelian structures built from it differ by unfolding.
attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax

namespace AlgebraicGeometry.DeRhamTypeComplex

attribute [local instance 2000] HasDerivedCategory.standard

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Restriction of scalars preserves finite limits, being the identity on underlying groups. -/
local instance preservesFiniteLimits_restrictScalars' {R R' : Type u} [Ring R] [Ring R']
    (φ : R →+* R') : PreservesFiniteLimits (ModuleCat.restrictScalars.{u} φ) :=
  Stacks.Cohomology.CechAcyclic.preservesFiniteLimits_restrictScalars φ

/-- Restriction of scalars preserves finite colimits, being the identity on underlying groups. -/
local instance preservesFiniteColimits_restrictScalars' {R R' : Type u} [Ring R] [Ring R']
    (φ : R →+* R') : PreservesFiniteColimits (ModuleCat.restrictScalars.{u} φ) := by
  constructor
  intro J _ _
  constructor
  intro G
  infer_instance

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-! ### Acyclicity of the terms on affine opens -/

/-- **A quasi-coherent `𝒪_X`-module read over `f^{-1}𝒪_S` has no higher cohomology on an affine
open**: its cohomology over `f^{-1}𝒪_S` is its cohomology over `𝒪_X`
(`Stacks.Cohomology.ModuleComparison.isZero_hgroup_restrictScalars_iff`), which vanishes in
positive degree by [Stacks, Tag 01XB]. -/
theorem isZero_rightDerived_evaluation_pushforward (V : X.Opens) (hV : IsAffineOpen V)
    (M : X.Modules) [M.IsQuasicoherent] (m : ℕ) (hm : 0 < m) :
    IsZero (((SheafOfModules.evaluation (inverseImageBaseRing f) (op V)).rightDerived m).obj
      ((pushforward (toInverseImageBase f)).obj M)) :=
  (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
    (inverseImageBaseRing f) V m _).2
    ((Stacks.Cohomology.ModuleComparison.isZero_hgroup_restrictScalars_iff
      (inverseImageBaseRingMap f) V m M).2
      (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X M V hV m hm))

/-! ### Derived global sections over the base ring -/

/-- **Derived global sections `RΓ(X, -)` of complexes of `f^{-1}𝒪_S`-modules, over
`A = Γ(S, 𝒪_S)`**: the bounded below right derived functor of global sections, read over `A`
along `A ⟶ Γ(X, f^{-1}𝒪_S)`. -/
def derivedSections :
    CochainComplex.Plus (SheafOfModules.{u} (inverseImageBaseRing f)) ⥤
      DerivedCategory (ModuleCat.{u} Γ(S, ⊤)) :=
  Stacks.Cech.Linear.derivedSectionsFunctor _ (inverseImageBaseRing f) ⊤ ⋙
    (ModuleCat.restrictScalars.{u} (inverseImageBaseRingHom f)).mapDerivedCategory

/-- **The hypercohomology module `H^j(X, K^•) = H^j(RΓ(X, K^•))`**, an `A`-module. -/
abbrev hypercohomology (K : CochainComplex.Plus (SheafOfModules.{u} (inverseImageBaseRing f)))
    (j : ℤ) : ModuleCat.{u} Γ(S, ⊤) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(S, ⊤)) j).obj ((derivedSections f).obj K)

section Cech

variable {I : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)

/-- **The comparison `Tot(Č^•(𝒰, K^•)) ⟶ RΓ(X, K^•)` in `D(A)`**, natural in the bounded below
complex `K^•`: the module-coefficient comparison of [Stacks, Tag 08BN]
(`Stacks.Cech.Linear.cechToDerivedSections`), read over `A`. Its source is the total Čech complex
`totalCechComplex`, read over `A`. -/
def totalCechToDerivedSections :
    CochainComplex.Plus.ι _ ⋙
        Stacks.Cech.Linear.totalCechComplexFunctor _ (inverseImageBaseRing f) ⊤ U hU ⋙
        (ModuleCat.restrictScalars.{u} (inverseImageBaseRingHom f)).mapHomologicalComplex
          (up ℤ) ⋙ DerivedCategory.Q ⟶
      derivedSections f :=
  Functor.whiskerLeft (CochainComplex.Plus.ι _ ⋙
      Stacks.Cech.Linear.totalCechComplexFunctor _ (inverseImageBaseRing f) ⊤ U hU)
      (ModuleCat.restrictScalars.{u} (inverseImageBaseRingHom f)).mapDerivedCategoryFactors.inv ≫
    Functor.whiskerRight ((Stacks.Cech.Linear.cechToDerivedSections _ (inverseImageBaseRing f)
      ⊤).map U hU)
      (ModuleCat.restrictScalars.{u} (inverseImageBaseRingHom f)).mapDerivedCategory

/-- **(2): a cover by affine opens computes `RΓ(X, K^•)`.** On a scheme with affine diagonal
(for instance one proper over an affine scheme, `isAffineHom_diagonal_of_isProper`), for a cover
`𝒰` by affine opens and a bounded below complex `K^•` of `f^{-1}𝒪_S`-modules whose terms are
quasi-coherent `𝒪_X`-modules read over `f^{-1}𝒪_S`, the comparison
`Tot(Č^•(𝒰, K^•)) ⟶ RΓ(X, K^•)` is an isomorphism in `D(A)`. The Čech complex is the one over
ordered tuples (`totalCechComplex`). -/
theorem isIso_totalCechToDerivedSections_app [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hUaff : ∀ i, IsAffineOpen (U i))
    (K : CochainComplex.Plus (SheafOfModules.{u} (inverseImageBaseRing f)))
    (hK : ∀ q, ∃ M : X.Modules, M.IsQuasicoherent ∧
      Nonempty (K.1.X q ≅ (pushforward (toInverseImageBase f)).obj M)) :
    IsIso ((totalCechToDerivedSections f U hU).app K) := by
  have hiso : IsIso (((Stacks.Cech.Linear.cechToDerivedSections _ (inverseImageBaseRing f)
      ⊤).map U hU).app K) := by
    refine isIso_cechToDerivedSections_app _ (inverseImageBaseRing f) ⊤ U hU K
      (fun q r s m hm => ?_)
    obtain ⟨M, hM, ⟨e⟩⟩ := hK q
    have := hM
    exact (isZero_rightDerived_evaluation_pushforward f _
      (IsAffineOpen.iInf fun j => hUaff (s j)) M m hm).of_iso
      (((SheafOfModules.evaluation (inverseImageBaseRing f) (op (⨅ k, U (s k)))).rightDerived
        m).mapIso e)
  exact IsIso.comp_isIso' (Iso.isIso_inv ((ModuleCat.restrictScalars.{u}
    (inverseImageBaseRingHom f)).mapDerivedCategoryFactors.app _))
    ((ModuleCat.restrictScalars.{u} (inverseImageBaseRingHom f)).mapDerivedCategory.map_isIso
      (((Stacks.Cech.Linear.cechToDerivedSections _ (inverseImageBaseRing f) ⊤).map U hU).app K))

/-- **(2) as an isomorphism**: `RΓ(X, K^•) ≅ Tot(Č^•(𝒰, K^•))` in `D(A)` for a cover by affine
opens of a scheme with affine diagonal and a bounded below complex with quasi-coherent terms; it
is the component of the natural transformation `totalCechToDerivedSections`. -/
def totalCechIsoDerivedSections [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hUaff : ∀ i, IsAffineOpen (U i))
    (K : CochainComplex.Plus (SheafOfModules.{u} (inverseImageBaseRing f)))
    (hK : ∀ q, ∃ M : X.Modules, M.IsQuasicoherent ∧
      Nonempty (K.1.X q ≅ (pushforward (toInverseImageBase f)).obj M)) :
    DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars.{u} (inverseImageBaseRingHom f)).mapHomologicalComplex
          (up ℤ)).obj (totalCechComplex f U hU K.1)) ≅ (derivedSections f).obj K :=
  have := isIso_totalCechToDerivedSections_app f U hU hUaff K hK
  asIso ((totalCechToDerivedSections f U hU).app K)

/-- The bounded below complexes of `f^{-1}𝒪_S`-modules whose terms are quasi-coherent
`𝒪_X`-modules read over `f^{-1}𝒪_S`. -/
def quasicoherentTerms :
    ObjectProperty (CochainComplex.Plus (SheafOfModules.{u} (inverseImageBaseRing f))) :=
  fun K => ∀ q, ∃ M : X.Modules, M.IsQuasicoherent ∧
    Nonempty (K.1.X q ≅ (pushforward (toInverseImageBase f)).obj M)

/-- A complex whose terms are coherent `𝒪_X`-modules read over `f^{-1}𝒪_S` has quasi-coherent
terms. -/
private theorem quasicoherentTerms_of_isCoherent
    {K : CochainComplex.Plus (SheafOfModules.{u} (inverseImageBaseRing f))}
    (hK : ∀ q, ∃ M : X.Modules, M.IsCoherent ∧
      Nonempty (K.1.X q ≅ (pushforward (toInverseImageBase f)).obj M)) :
    quasicoherentTerms f K := fun q => by
  obtain ⟨M, hM, he⟩ := hK q
  exact ⟨M, _root_.isQuasicoherent_of_isCoherent M, he⟩

/-- **(2) as a natural isomorphism**: on bounded below complexes with quasi-coherent terms, the
comparison `Tot(Č^•(𝒰, -)) ⟶ RΓ(X, -)` is a natural isomorphism of functors to `D(A)`, for a
cover `𝒰` by affine opens of a scheme with affine diagonal. -/
def totalCechNatIsoDerivedSections [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    (quasicoherentTerms f).ι ⋙ (CochainComplex.Plus.ι _ ⋙
        Stacks.Cech.Linear.totalCechComplexFunctor _ (inverseImageBaseRing f) ⊤ U hU ⋙
        (ModuleCat.restrictScalars.{u} (inverseImageBaseRingHom f)).mapHomologicalComplex
          (up ℤ) ⋙ DerivedCategory.Q) ≅
      (quasicoherentTerms f).ι ⋙ derivedSections f :=
  have : ∀ K : (quasicoherentTerms f).FullSubcategory,
      IsIso ((Functor.whiskerLeft (quasicoherentTerms f).ι
        (totalCechToDerivedSections f U hU)).app K) :=
    fun K => isIso_totalCechToDerivedSections_app f U hU hUaff K.1 K.2
  have := NatIso.isIso_of_isIso_app
    (Functor.whiskerLeft (quasicoherentTerms f).ι (totalCechToDerivedSections f U hU))
  asIso (Functor.whiskerLeft (quasicoherentTerms f).ι (totalCechToDerivedSections f U hU))

/-- The cohomology of `RΓ(X, K^•)` is the cohomology of the total Čech complex, read over `A`,
for a cover by affine opens of a scheme with affine diagonal and a bounded below complex with
quasi-coherent terms. -/
def homologyDerivedSectionsIso [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hUaff : ∀ i, IsAffineOpen (U i))
    (K : CochainComplex.Plus (SheafOfModules.{u} (inverseImageBaseRing f)))
    (hK : ∀ q, ∃ M : X.Modules, M.IsQuasicoherent ∧
      Nonempty (K.1.X q ≅ (pushforward (toInverseImageBase f)).obj M)) (j : ℤ) :
    hypercohomology f K j ≅
      (ModuleCat.restrictScalars.{u} (inverseImageBaseRingHom f)).obj
        ((totalCechComplex f U hU K.1).homology j) :=
  haveI := Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars
    (inverseImageBaseRingHom f)
  (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(S, ⊤)) j).mapIso
      (totalCechIsoDerivedSections f U hU hUaff K hK).symm ≪≫
    (DerivedCategory.homologyFunctorFactors _ j).app _ ≪≫
    ((totalCechComplex f U hU K.1).sc j).mapHomologyIso
      (ModuleCat.restrictScalars.{u} (inverseImageBaseRingHom f))

end Cech

/-! ### (1): finiteness and vanishing of hypercohomology -/

/-- A scheme proper over an affine scheme has a finite cover by affine opens. -/
theorem exists_finite_affine_cover [IsAffine S] [IsProper f] :
    ∃ (I : Type u) (_ : Finite I) (U : I → X.Opens), (∀ i, IsAffineOpen (U i)) ∧
      (⊤ : X.Opens) = ⨆ i, U i := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨s, hs, hcov⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := X)
    (U := ⊤)).mp (by simpa using isCompact_univ)
  refine ⟨s, hs.to_subtype, fun i => (i.1 : X.Opens), fun i => i.1.2, ?_⟩
  rw [hcov, iSup_subtype']

/-- **(1), finiteness: the hypercohomology modules `H^j(X, K^•)` are finite `A`-modules.** Let
`f : X ⟶ S` be proper with `S` affine and locally Noetherian and let `K^•` be a bounded below
complex of `f^{-1}𝒪_S`-modules each of whose terms is a coherent `𝒪_X`-module read over
`f^{-1}𝒪_S` (its differentials being only `f^{-1}𝒪_S`-linear). Then every `H^j(RΓ(X, K^•))` is
a finite `Γ(S, 𝒪_S)`-module: by (2) it is the cohomology of the total Čech complex of a finite
affine cover, which is finite by `moduleFinite_homology_totalCechComplex`. -/
theorem moduleFinite_homology_derivedSections [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
    (K : CochainComplex.Plus (SheafOfModules.{u} (inverseImageBaseRing f)))
    (hK : ∀ q, ∃ M : X.Modules, M.IsCoherent ∧
      Nonempty (K.1.X q ≅ (pushforward (toInverseImageBase f)).obj M)) (j : ℤ) :
    Module.Finite Γ(S, ⊤) (hypercohomology f K j) := by
  have := isAffineHom_diagonal_of_isProper f
  obtain ⟨I, _, U, hUaff, hU⟩ := exists_finite_affine_cover f
  obtain ⟨a, ha⟩ := (CochainComplex.plus_iff _ K.1).mp K.2
  have hfin := moduleFinite_homology_totalCechComplex f U hU hUaff K.1 a hK j
  exact Module.Finite.equiv (homologyDerivedSectionsIso f U hU hUaff K
    (quasicoherentTerms_of_isCoherent f hK) j).symm.toLinearEquiv

/-- **(1), vanishing: the hypercohomology modules `H^j(X, K^•)` vanish for `j > b + t - 1`** when
`K^•` is concentrated in degrees `≤ b`, its terms are quasi-coherent `𝒪_X`-modules read over
`f^{-1}𝒪_S`, and `X`, which has affine diagonal, is covered by `t` affine opens: by (2) and
`isZero_homology_totalCechComplex`. -/
theorem isZero_homology_derivedSections [IsAffineHom (pullback.diagonal (terminal.from X))]
    {I : Type u} [Finite I] (U : I → X.Opens) (hUaff : ∀ i, IsAffineOpen (U i))
    (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (K : CochainComplex.Plus (SheafOfModules.{u} (inverseImageBaseRing f))) (b : ℤ)
    [K.1.IsStrictlyLE b]
    (hK : ∀ q, ∃ M : X.Modules, M.IsQuasicoherent ∧
      Nonempty (K.1.X q ≅ (pushforward (toInverseImageBase f)).obj M))
    (j : ℤ) (hj : b + Nat.card I - 1 < j) :
    IsZero (hypercohomology f K j) := by
  obtain ⟨a, ha⟩ := (CochainComplex.plus_iff _ K.1).mp K.2
  exact (Functor.map_isZero _
    (isZero_homology_totalCechComplex f U hU hUaff K.1 a b hK j hj)).of_iso
    (homologyDerivedSectionsIso f U hU hUaff K hK j)

/-- **(1), vanishing over a proper base: `H^j(X, K^•) = 0` for `j` large.** For `f` proper with
`S` affine and `K^•` bounded with quasi-coherent terms there is `N` with `H^j(RΓ(X, K^•)) = 0` for
all `j > N`; one may take `N = b + t - 1` for any finite affine cover by `t` opens. -/
theorem exists_isZero_homology_derivedSections [IsAffine S] [IsProper f]
    (K : CochainComplex.Plus (SheafOfModules.{u} (inverseImageBaseRing f))) (b : ℤ)
    [K.1.IsStrictlyLE b]
    (hK : ∀ q, ∃ M : X.Modules, M.IsQuasicoherent ∧
      Nonempty (K.1.X q ≅ (pushforward (toInverseImageBase f)).obj M)) :
    ∃ N : ℤ, ∀ j, N < j →
      IsZero (hypercohomology f K j) := by
  have := isAffineHom_diagonal_of_isProper f
  obtain ⟨I, _, U, hUaff, hU⟩ := exists_finite_affine_cover f
  exact ⟨b + Nat.card I - 1, fun j hj =>
    isZero_homology_derivedSections f U hUaff hU K b hK j hj⟩

/-- **`H^j(X, K^•) = 0` below the bottom degree of `K^•`**: for `f` proper with `S` affine and
`K^•` concentrated in degrees `≥ a` with quasi-coherent terms, `H^j(RΓ(X, K^•)) = 0` for `j < a`,
the total Čech complex of a finite affine cover vanishing in those degrees. -/
theorem isZero_hypercohomology_of_lt [IsAffine S] [IsProper f]
    (K : CochainComplex.Plus (SheafOfModules.{u} (inverseImageBaseRing f))) (a : ℤ)
    [K.1.IsStrictlyGE a]
    (hK : ∀ q, ∃ M : X.Modules, M.IsQuasicoherent ∧
      Nonempty (K.1.X q ≅ (pushforward (toInverseImageBase f)).obj M))
    (j : ℤ) (hj : j < a) : IsZero (hypercohomology f K j) := by
  have := isAffineHom_diagonal_of_isProper f
  obtain ⟨I, _, U, hUaff, hU⟩ := exists_finite_affine_cover f
  refine IsZero.of_iso (Functor.map_isZero _ ?_) (homologyDerivedSectionsIso f U hU hUaff K hK j)
  refine IsZero.of_iso ?_ (totalCechComplexHomologyIso f U hU K.1 j)
  exact StacksDraft.TotalComplexQuasiIso.isZero_homology_of_isZero_X j
    (StacksDraft.TotalComplexQuasiIso.isZero_total_X
      (cechBicomplex (inverseImageBaseRing f) ⊤ U hU K.1) a
      (fun q p hp => isZero_cechBicomplex_X_X _ ⊤ U hU K.1 q p (Or.inr hp))
      (fun q hq => (cechComplexIntFunctor (inverseImageBaseRing f) ⊤ U hU).map_isZero
        (K.1.isZero_of_isStrictlyGE a q hq)) j hj)

/-- **`RΓ(X, K^•)` is a pseudo-coherent object of `D(A)`**: for `f` proper with `S` affine and
locally Noetherian and `K^•` a bounded complex of `f^{-1}𝒪_S`-modules with coherent terms, the
hypercohomology modules are finite (`moduleFinite_homology_derivedSections`) and vanish in large
degrees (`exists_isZero_homology_derivedSections`), and over a Noetherian ring a bounded-above
object with finite cohomology is pseudo-coherent. -/
theorem isPseudoCoherent_derivedSections [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
    (K : CochainComplex.Plus (SheafOfModules.{u} (inverseImageBaseRing f))) (b : ℤ)
    [K.1.IsStrictlyLE b]
    (hK : ∀ q, ∃ M : X.Modules, M.IsCoherent ∧
      Nonempty (K.1.X q ≅ (pushforward (toInverseImageBase f)).obj M)) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent ((derivedSections f).obj K) := by
  have : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  exact (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    ((derivedSections f).obj K) 0 Γ(S, ⊤)).2.1.2
    ⟨exists_isZero_homology_derivedSections f K b
      (quasicoherentTerms_of_isCoherent f hK),
      fun i => moduleFinite_homology_derivedSections f K hK i⟩

end AlgebraicGeometry.DeRhamTypeComplex

end
