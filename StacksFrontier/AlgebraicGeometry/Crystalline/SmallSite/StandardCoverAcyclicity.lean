module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyGlue.AffineOpenVanishing
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineAmbientObjects
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChaoticHigherDirectImageWhole
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingAlongAFunctorEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 07JJ: a locally quasi-coherent module is acyclic over an object with `T` or `U` affine

Fix a global crystalline situation `(p, (S, I, γ), X)` and let `F` be a sheaf of
`𝒪_{X/S}`-modules on the small crystalline site `Cris(X/S)` which is locally quasi-coherent, that
is, whose restriction `F_T` to the ambient divided power scheme of every object is a
quasi-coherent `𝒪_T`-module.  This file proves that for every object `A = (U, T, δ)` of
`Cris(X/S)` whose ambient scheme `T` **or** whose thickened scheme `U` is affine, and every
`p > 0`,

`H^p(Cris(X/S)/(U, T, δ), F) = 0`.

The two hypotheses are equivalent, the immersion `U ⟶ T` of an object being a thickening: `U` is
affine as soon as `T` is because a closed immersion is an affine morphism
(`SmallSite.isAffineObject_of_isAffine`), and `T` is affine as soon as `U` is by
[Stacks, Tag 06AD] (`isAffine_target_of_isAffine_source`).

## Main definitions

Names not written in full are in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `standardRestrictCoverings`: for an object `A` with affine ambient scheme `T`, the restriction
  covers of `A` attached to a standard open cover of `T` by basic opens of global sections, and
  for any other object, nothing.
* `HasStandardCechVanishing`: the Čech cohomology of an abelian sheaf vanishes in positive degrees
  on every standard restriction cover.

## Main results

* `Stacks.Cohomology.Cech.iSup_basicOpen_eq_top_of_isStandardOpenCoverOfSpectrum`: the basic
  opens of a standard open cover of the spectrum of an affine scheme cover that scheme.
* `CrystallineThickening.sieve_restrictOpenHom_of_le`: a sieve containing the restriction of an
  object to an open contains its restriction to any smaller open.
* `standardRestrictCoverings_cofinal`: every covering sieve of an object with affine ambient
  scheme is refined by a standard restriction cover.
* `isZero_cechCohomology_of_mem_standardRestrictCoverings`: the positive-degree Čech cohomology of
  the abelian sheaf of a locally quasi-coherent module vanishes on every standard restriction
  cover; `hasStandardCechVanishing_abelianSheaf` is the same as the predicate
  `HasStandardCechVanishing`.
* `subsingleton_ext_of_hasStandardCechVanishing`: for an abelian sheaf satisfying
  `HasStandardCechVanishing`, the `Ext`-groups out of the free abelian sheaf on an object with
  affine ambient scheme vanish in positive degrees.
* `vanishing07JJ_of_hasStandardCechVanishing`: the conclusion of [Stacks, Tag 07JJ] for an
  abelian sheaf satisfying `HasStandardCechVanishing`.
* `vanishing07JJ_abelianSheaf`: [Stacks, Tag 07JJ] for the objects with affine ambient scheme.
* `isAffine_target_of_isAffine_source`: an object of `Cris(X/S)` whose thickened scheme `U` is
  affine has affine ambient divided power scheme `T`.
* `isZero_overCohomology_abelianSheaf_of_isAffine`: [Stacks, Tag 07JJ] for every object with `T`
  or `U` affine.
* `vanishing07JJWhole_abelianSheaf`: the same at the divided power thickenings of the whole of
  `X`.

## References

* [Stacks Project, Tag 07JJ](https://stacks.math.columbia.edu/tag/07JJ)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 01X9](https://stacks.math.columbia.edu/tag/01X9)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 07IG](https://stacks.math.columbia.edu/tag/07IG)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.Cohomology.Cech

/-- The basic opens of a standard open cover of the spectrum of an affine scheme cover that
scheme. -/
theorem iSup_basicOpen_eq_top_of_isStandardOpenCoverOfSpectrum {X : Scheme.{u}} [IsAffine X]
    {n : ℕ} (g : Fin n → Γ(X, ⊤)) (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g) :
    (⨆ i, X.basicOpen (g i)) = ⊤ := by
  simpa only [iSup_range'] using
    ((isAffineOpen_top X).iSup_basicOpen_eq_self_iff (s := Set.range g)).mpr
      (span_range_eq_top_of_isStandardOpenCoverOfSpectrum hg)

/-- Every point of an affine scheme lies in one of the basic opens of a standard open cover of
its spectrum. -/
theorem exists_mem_basicOpen_of_isStandardOpenCoverOfSpectrum {X : Scheme.{u}} [IsAffine X]
    {n : ℕ} (g : Fin n → Γ(X, ⊤)) (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g) (x : X) :
    ∃ i : ULift.{u + 1} (Fin n), x ∈ X.basicOpen (g i.down) := by
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp
    (iSup_basicOpen_eq_top_of_isStandardOpenCoverOfSpectrum g hg ▸ Opens.mem_top x)
  exact ⟨ULift.up j, hj⟩

end Stacks.Cohomology.Cech

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The standard restriction covers -/

/-- **The standard restriction covers of `Cris(X/S)`**: for an object `A` with affine ambient
scheme `T`, the families of restrictions `A|_{T_{g i}} ⟶ A` attached to a finite family `g` of
global sections of `T` whose basic opens form a standard open cover of `Spec Γ(T, 𝒪_T)`, indexed
by `ULift.{u + 1} (Fin n)`; for any other object, nothing. -/
def standardRestrictCoverings (A : CrystallineThickening S) :
    Set { E : PreZeroHypercover.{u + 1} A // E.sieve₀ ∈ smallTopology S A } :=
  {E | A ∈ affineAmbientObjects S ∧
    ∃ (n : ℕ) (g : Fin n → Γ(A.obj.thickening.target.scheme, ⊤)),
      PrimeSpectrum.IsStandardOpenCoverOfSpectrum g ∧
        E.1 = CrystallineThickening.restrictOpenHypercover A
          (fun i : ULift.{u + 1} (Fin n) ↦
            A.obj.thickening.target.scheme.basicOpen (g i.down))}

/-- A standard restriction cover is a restriction cover by affine opens of an object with affine
ambient scheme. -/
theorem standardRestrictCoverings_subset_affineAmbientRestrictCoverings
    {A : CrystallineThickening S} :
    standardRestrictCoverings A ⊆ affineAmbientRestrictCoverings A := by
  rintro ⟨E, hEcov⟩ ⟨hA, n, g, hg, hEeq⟩
  have : IsAffine A.obj.thickening.target.scheme := hA
  exact ⟨hA, ULift.{u + 1} (Fin n), _, fun i ↦ (isAffineOpen_top _).basicOpen (g i.down),
    Stacks.Cohomology.Cech.exists_mem_basicOpen_of_isStandardOpenCoverOfSpectrum g hg, hEeq⟩

/-- The iterated fibre products of a standard restriction cover exist. -/
theorem hasProduct_of_mem_standardRestrictCoverings {A : CrystallineThickening S}
    (E : { E : PreZeroHypercover.{u + 1} A // E.sieve₀ ∈ smallTopology S A })
    (hE : E ∈ standardRestrictCoverings A) (p : ℕ) (i : Fin (p + 1) → E.1.I₀) :
    HasProduct fun a ↦ Over.mk (E.1.f (i a)) :=
  hasProduct_of_mem_affineAmbientRestrictCoverings E
    (standardRestrictCoverings_subset_affineAmbientRestrictCoverings hE) p i

/-- The object covered by a standard restriction cover, the domains of its members, and the
domains of the finite fibre products of its members have affine ambient scheme. -/
theorem standardRestrictCoverings_covObjects {A : CrystallineThickening S}
    (E : { E : PreZeroHypercover.{u + 1} A // E.sieve₀ ∈ smallTopology S A })
    (hE : E ∈ standardRestrictCoverings A) :
    A ∈ affineAmbientObjects S ∧ (∀ i, E.1.X i ∈ affineAmbientObjects S) ∧
      ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (j a))) :=
          hasProduct_of_mem_standardRestrictCoverings E hE
        (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ affineAmbientObjects S :=
  affineAmbientRestrictCoverings_covObjects E
    (standardRestrictCoverings_subset_affineAmbientRestrictCoverings hE)

/-! ### Cofinality of the standard restriction covers -/

/-- A sieve on `A` containing the restriction of `A` to an open of its ambient scheme contains its
restriction to every smaller open. -/
theorem CrystallineThickening.sieve_restrictOpenHom_of_le (A : CrystallineThickening S)
    {V W : A.obj.thickening.target.scheme.Opens} (h : W ≤ V) {R : Sieve A}
    (hR : R (A.restrictOpenHom V)) : R (A.restrictOpenHom W) :=
  CrystallineThickening.sieve_restrictOpenHom_of_restrictOpenHom_comp A h
    (R.downward_closed hR _)

/-- **The standard restriction covers are cofinal over the objects with affine ambient scheme**:
every covering sieve of such an object is refined by one of them. -/
theorem standardRestrictCoverings_cofinal (S : GlobalCrystallineSituation.{u}) :
    ∀ A ∈ affineAmbientObjects S, ∀ R ∈ smallTopology S A,
      ∃ E : { E : PreZeroHypercover.{u + 1} A // E.sieve₀ ∈ smallTopology S A },
        E ∈ standardRestrictCoverings A ∧ E.1.sieve₀ ≤ R := by
  classical
  intro A hA R hR
  set T := A.obj.thickening.target.scheme
  have : IsAffine T := hA
  rw [← restrictCoverage_toGrothendieck] at hR
  choose V hVaff hVmem hVR using
    CrystallineThickening.exists_isAffineOpen_mem_restrictOpenHom_mem_of_saturate
      (Coverage.mem_toGrothendieck.mp hR)
  obtain ⟨W, hWstd, hWcar, hWref⟩ :=
    Stacks.Cohomology.AffineOpen.exists_standardCover_refines T ⊤ (isAffineOpen_top T)
      { ι := ↥T
        carrier := ⊤
        obj := V
        iSup_eq := eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hVmem x⟩ } rfl
  obtain ⟨Wι, Wcar, Wobj, WiSup⟩ := W
  dsimp only at hWstd hWcar hWref
  subst hWcar
  obtain ⟨-, n, g, e, hgstd, hWobj⟩ := hWstd
  obtain ⟨-, hrefine⟩ := hWref
  have hgR : ∀ j : Fin n, R (A.restrictOpenHom (T.basicOpen (g j))) := by
    intro j
    obtain ⟨x, hx⟩ := hrefine (e.symm j)
    refine CrystallineThickening.sieve_restrictOpenHom_of_le A ?_ (hVR x)
    rw [hWobj] at hx
    simpa using hx
  refine ⟨affineRestrictCover A (fun i : ULift.{u + 1} (Fin n) ↦ T.basicOpen (g i.down))
    (Stacks.Cohomology.Cech.exists_mem_basicOpen_of_isStandardOpenCoverOfSpectrum g hgstd),
    ⟨hA, n, g, hgstd, rfl⟩, ?_⟩
  intro Z k hk
  obtain ⟨Y, q, f, ⟨i⟩, rfl⟩ := hk
  exact R.downward_closed (hgR i.down) q

/-! ### The Čech vanishing on the standard restriction covers -/

/-- The positive-degree Čech cohomology of the abelian sheaf of a locally quasi-coherent module
vanishes on every standard restriction cover. -/
theorem isZero_cechCohomology_of_mem_standardRestrictCoverings
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    {A : CrystallineThickening S}
    (E : { E : PreZeroHypercover.{u + 1} A // E.sieve₀ ∈ smallTopology S A })
    (hE : E ∈ standardRestrictCoverings A) (p : ℕ) (hp : 0 < p) :
    letI : ∀ (q : ℕ) (i : Fin (q + 1) → E.1.I₀),
      HasProduct (fun a ↦ Over.mk (E.1.f (i a))) :=
      hasProduct_of_mem_standardRestrictCoverings E hE
    IsZero (Stacks.CechSite.cechCohomology E.1 (abelianSheaf F).obj p) := by
  obtain ⟨E, hEcov⟩ := E
  obtain ⟨hA, n, g, hg, hEeq⟩ := hE
  have : IsAffine A.obj.thickening.target.scheme := hA
  change E = _ at hEeq
  subst hEeq
  exact isZero_cechCohomology_abelianSheaf_of_isStandardOpenCover_ulift F hF A g hg p hp

/-! ### The Čech hypothesis as a condition on an abelian sheaf -/

/-- An abelian sheaf `G` on `Cris(X/S)` at the coefficient universe `u + 1` **has standard Čech
vanishing** if its Čech cohomology on every standard restriction cover vanishes in positive
degrees. -/
def HasStandardCechVanishing (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) : Prop :=
  ∀ {A : CrystallineThickening S}
    (E : { E : PreZeroHypercover.{u + 1} A // E.sieve₀ ∈ smallTopology S A })
    (hE : E ∈ standardRestrictCoverings A) (p : ℕ), 0 < p →
      letI : ∀ (q : ℕ) (i : Fin (q + 1) → E.1.I₀),
        HasProduct (fun a ↦ Over.mk (E.1.f (i a))) :=
        hasProduct_of_mem_standardRestrictCoverings E hE
      IsZero (Stacks.CechSite.cechCohomology E.1 G.obj p)

/-- The abelian sheaf of a locally quasi-coherent module satisfies `HasStandardCechVanishing`. -/
theorem hasStandardCechVanishing_abelianSheaf (F : SheafOfModules.{u} (structureSheaf S))
    (hF : IsLocallyQuasiCoherent F) : HasStandardCechVanishing (abelianSheaf F) :=
  fun E hE p hp ↦ isZero_cechCohomology_of_mem_standardRestrictCoverings F hF E hE p hp

/-! ### Stacks 07JJ -/

/-- **The `Ext`-groups out of the free abelian sheaf on an object with affine ambient scheme
vanish in positive degrees**, for any abelian sheaf satisfying `HasStandardCechVanishing`. -/
theorem subsingleton_ext_of_hasStandardCechVanishing
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (hG : HasStandardCechVanishing G)
    (A : CrystallineThickening S) (hA : A ∈ affineAmbientObjects S) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Ext ((presheafToSheaf (smallTopology S) AddCommGrpCat.{u + 1}).obj
      (uliftYoneda.{u + 1}.obj A ⋙ AddCommGrpCat.free)) G p) :=
  Stacks.CechSite.subsingleton_ext_of_cechCohomology_isZero.{u + 1, u + 1} (smallTopology S)
    (affineAmbientObjects S) standardRestrictCoverings
    (fun E hE ↦ hasProduct_of_mem_standardRestrictCoverings E hE)
    (fun E hE ↦ standardRestrictCoverings_covObjects E hE)
    (standardRestrictCoverings_cofinal S) G
    (fun E hE q hq ↦ hG E hE q hq)
    A hA p hp

open Stacks.Cohomology.FreeYonedaUnivLE in
/-- **The conclusion of [Stacks, Tag 07JJ] for any abelian sheaf satisfying
`HasStandardCechVanishing`**: for every object `(U, T, δ)` of `Cris(X/S)` with `T` affine and
every `p > 0`, the cohomology `H^p(Cris(X/S)/(U, T, δ), G)` of the localized site vanishes. -/
theorem vanishing07JJ_of_hasStandardCechVanishing
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (hG : HasStandardCechVanishing G) :
    Vanishing07JJ S G := by
  intro A hAaff p hp
  have hsub := subsingleton_ext_of_hasStandardCechVanishing G hG A hAaff p hp
  refine IsZero.of_iso ?_ (overCohomologyIsoRightDerivedSections S A G p)
  refine IsZero.of_iso ?_
    (cohomologyPresheafObjIsoRightDerivedSectionsOfEnoughInjectives.{u + 1}
      (smallTopology S) G p A).symm
  exact @AddCommGrpCat.isZero_of_subsingleton _ hsub

/-- **The `Ext`-groups out of the free abelian sheaf on an object with affine ambient scheme
vanish in positive degrees**, for the abelian sheaf attached to a locally quasi-coherent module. -/
theorem subsingleton_ext_abelianSheaf (F : SheafOfModules.{u} (structureSheaf S))
    (hF : IsLocallyQuasiCoherent F) (A : CrystallineThickening S)
    (hA : A ∈ affineAmbientObjects S) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Ext ((presheafToSheaf (smallTopology S) AddCommGrpCat.{u + 1}).obj
      (uliftYoneda.{u + 1}.obj A ⋙ AddCommGrpCat.free)) (abelianSheaf F) p) :=
  subsingleton_ext_of_hasStandardCechVanishing (abelianSheaf F)
    (hasStandardCechVanishing_abelianSheaf F hF) A hA p hp

/-- Let `F` be a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules on the small crystalline site
`Cris(X/S)` of a global crystalline situation. Then for every object `(U, T, δ)` of `Cris(X/S)`
whose ambient divided power scheme `T` is affine, and every `p > 0`, the cohomology of the
localized site vanishes:

`H^p(Cris(X/S)/(U, T, δ), F) = 0`.

The statement is about the abelian sheaf `SmallSite.abelianSheaf F` of the coefficient universe
`u + 1`, which is the universe in which the cohomology of `Cris(X/S)` and of its localizations
exists; the modules of `F` itself live in `Type u`. -/
@[stacks 07JJ "the case of the objects (U, T, δ) whose ambient divided power scheme T is affine, \
in the packaged form SmallSite.Vanishing07JJ that the consumers of the tag in this library use, \
and for the abelian sheaf SmallSite.abelianSheaf F of the coefficient universe u + 1 attached to \
a locally quasi-coherent module F. The source's remaining case of U affine is reduced to this one \
in isZero_overCohomology_abelianSheaf_of_isAffine, which states both"]
theorem vanishing07JJ_abelianSheaf (F : SheafOfModules.{u} (structureSheaf S))
    (hF : IsLocallyQuasiCoherent F) : Vanishing07JJ S (abelianSheaf F) :=
  vanishing07JJ_of_hasStandardCechVanishing (abelianSheaf F)
    (hasStandardCechVanishing_abelianSheaf F hF)

/-! ### The case of an affine thickened scheme -/

/-- An object of `Cris(X/S)` whose thickened scheme `U` is affine has affine ambient divided
power scheme `T`. -/
theorem isAffine_target_of_isAffine_source (A : CrystallineThickening S)
    [IsAffine A.obj.thickening.source] : IsAffine A.obj.thickening.target.scheme :=
  A.obj.thickening.isAffine_target

/-- Let `F` be a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules on the small crystalline site
`Cris(X/S)` of a global crystalline situation. Then for every object `(U, T, δ)` of `Cris(X/S)`
with `T` **or** `U` affine, and every `p > 0`, the cohomology of the localized site vanishes:

`H^p(Cris(X/S)/(U, T, δ), F) = 0`. -/
@[stacks 07JJ "both cases of the hypothesis: the objects (U, T, δ) with T or U affine, for the \
abelian sheaf SmallSite.abelianSheaf F of the coefficient universe u + 1 attached to a locally \
quasi-coherent module F"]
theorem isZero_overCohomology_abelianSheaf_of_isAffine
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (A : CrystallineThickening S)
    (hA : IsAffine A.obj.thickening.target.scheme ∨ IsAffine A.obj.thickening.source)
    (p : ℕ) (hp : 0 < p) :
    IsZero ((overCohomologyFunctor S A p).obj ((restrictToOver S A).obj (abelianSheaf F))) :=
  vanishing07JJ_abelianSheaf F hF A
    (hA.elim id fun h ↦ @isAffine_target_of_isAffine_source S A h) p hp

/-- **[Stacks, Tag 07JJ] at the divided power thickenings of the whole of `X`**, for the abelian
sheaf of a locally quasi-coherent module. -/
theorem vanishing07JJWhole_abelianSheaf [IsAffine S.X]
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F) :
    Vanishing07JJWhole S (abelianSheaf F) :=
  vanishing07JJWhole_of_vanishing07JJ S (vanishing07JJ_abelianSheaf F hF)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
