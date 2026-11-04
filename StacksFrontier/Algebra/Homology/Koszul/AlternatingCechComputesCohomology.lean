module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AlternatingQuasicoherentComparison
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.StandardCoverCofinality
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.Algebra.Homology.Koszul.Situation
public import StacksFrontier.RingTheory.LocalCohomology.Deps.QuasicoherentAffineVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.LinearAlternatingDerivedGlobalSections
import StacksCore.Tactic.StacksAttribute

/-!
# The alternating Čech complex of the standard covering computes derived sections

In the situation of [Stacks, Tag 08CZ] — a ring `A`, a finite sequence `f₁, …, f_r` of elements
of `A`, the affine scheme `X = Spec(A)`, the open `U = D(f₁) ∪ ⋯ ∪ D(f_r)` and its covering
`𝒰 : U = ⋃ᵢ D(fᵢ)` — the total alternating Čech complex of a complex `F^•` of quasi-coherent
`𝒪_U`-modules computes the derived sections of `F^•` over `U` in `D(A)`: the comparison map

`Tot(Č_alt^•(𝒰, F^•)) ⟶ RΓ(U, F^•)`

of [Stacks, Tag 08C1], taken `A`-linearly, is an isomorphism, naturally in `F^•`.

## Main results

* `Koszul.CechSituation.isAffineOpen_iInf_cover`: every finite intersection of members of `𝒰`
  is an affine open of `U`.
* `Koszul.CechSituation.baseCenter`: `A` acting on `𝒪_U`-modules through `A ⟶ Γ(U, 𝒪_U)`.
* `Koszul.CechSituation.isIso_linearAlternatingCechToDerivedComparison`:
  **[Stacks, Tag 08D2]**, the comparison map in `D(A)` is an isomorphism.
* `Koszul.CechSituation.alternatingCechTotalNatIsoDerivedSections`: **[Stacks, Tag 08D2]**,
  the resulting isomorphism in `D(A)`, natural in the complex of quasi-coherent modules.
* `Koszul.CechSituation.isIso_linearAlternatingCechToDerivedComparison_restrict`: the same for
  the restriction to `U` of a complex of quasi-coherent `𝒪_X`-modules, which is the shape in
  which the source states it.
* `Koszul.CechSituation.isIso_alternatingCechToDerivedComparison`: the underlying statement in
  `D(Ab)`.

## Implementation notes

**The `A`-module structures.** Both sides are complexes of `A`-modules through the ring map
`A ⟶ Γ(X, 𝒪_X) ⟶ Γ(U, 𝒪_U)` induced by the open immersion `U ⟶ X`: an element `a` acts on every
`𝒪_U`-module as multiplication by its image, and therefore on sections and on Čech cochains.
The complexes of `A`-modules of `Stacks.Cech.linearAlternatingCechDerivedFunctor` and
`Stacks.Cech.linearUnboundedDerivedGlobalSectionsFunctor` have as underlying complexes of
abelian groups the ones of [Stacks, Tag 08C1], and the comparison map is invertible in `D(A)`
exactly when the one of Tag 08C1 is invertible in `D(Ab)`; the latter is the content of the
source's proof, which deduces the lemma from [Stacks, Tag 08C2] using that the finite
intersections of members of `𝒰` are affine.

**The covering is taken on `U`.** The source's `𝒰` is a covering of `U`, not of `X`, and both
sides of the comparison depend only on the restriction of `F^•` to `U`; accordingly the
statement is about the open subscheme `U` and a complex of quasi-coherent `𝒪_U`-modules. That
is more general than the source, which considers only restrictions of complexes from `X`; the
restricted form is recorded as a corollary, restriction preserving quasi-coherence.

**The index of the covering is lifted.** The Čech theory of [Stacks, Tag 08C1] indexes a
covering by a type in the universe of the space, while the situation indexes `𝒰` by `Fin r`;
`Koszul.CechSituation.coverUlift` is the same family read on `ULift (Fin r)`, and everything
about it is transported from the unlifted family.

**Affineness of the intersections.** A finite intersection of the standard opens of `X` is the
standard open of the product of the corresponding elements, hence affine; the corresponding
intersection in `U` is its preimage under the open immersion `U ⟶ X`, and preimage commutes
with finite infima of opens. The standard opens of the situation are written with
`PrimeSpectrum.basicOpen`, while the affineness statement available is about
`AlgebraicGeometry.Scheme.basicOpen`; the two are identified by
`AlgebraicGeometry.basicOpen_eq_of_affine`, whose ring argument is supplied explicitly because
the carrier of `Spec` is not transparent enough for it to be inferred from the opens alone.

## References

* [Stacks Project, Tag 08D2](https://stacks.math.columbia.edu/tag/08D2)
* [Stacks Project, Tag 08CZ](https://stacks.math.columbia.edu/tag/08CZ)
* [Stacks Project, Tag 08C2](https://stacks.math.columbia.edu/tag/08C2)
* [Stacks Project, Tag 08C1](https://stacks.math.columbia.edu/tag/08C1)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Koszul

/-- Taking preimages of opens along a morphism of schemes commutes with finite infima. -/
theorem preimage_iInf {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} [Finite ι] (V : ι → Y.Opens) :
    f ⁻¹ᵁ (⨅ i, V i) = ⨅ i, f ⁻¹ᵁ V i :=
  Opens.ext (by simp only [Scheme.Hom.coe_preimage, Opens.coe_iInf, Set.preimage_iInter])

namespace CechSituation

variable (S : CechSituation.{u})

/-- A finite intersection of the standard opens `D(fᵢ)` is an affine open of `X = Spec(A)`: it
is the standard open of the product of the corresponding elements. -/
theorem isAffineOpen_iInf_basicOpen {m : ℕ} (s : Fin (m + 1) → Fin S.r) :
    IsAffineOpen (⨅ k, S.basicOpen (s k)) := by
  have key := Stacks.Cohomology.Cech.isAffineOpen_iInf_basicOpen
    (isAffineOpen_top (Spec (CommRingCat.of S.A)))
    (fun i : Fin S.r ↦ (Scheme.ΓSpecIso (CommRingCat.of S.A)).inv (S.f i)) s
  have he : (⨅ k, (Spec (CommRingCat.of S.A)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of S.A)).inv (S.f (s k)))) = ⨅ k, S.basicOpen (s k) :=
    iInf_congr fun k ↦ basicOpen_eq_of_affine (R := CommRingCat.of S.A) (S.f (s k))
  exact he ▸ key

/-- **The finite intersections of the covering `𝒰` are affine opens of `U`.** Such an
intersection is the preimage under the open immersion `U ⟶ X` of the corresponding intersection
of standard opens, which is an affine open contained in `U`. -/
theorem isAffineOpen_iInf_cover {m : ℕ} (s : Fin (m + 1) → Fin S.r) :
    IsAffineOpen (⨅ k, S.cover (s k)) := by
  rw [show (⨅ k, S.cover (s k)) = S.ι ⁻¹ᵁ (⨅ k, S.basicOpen (s k)) from
    (preimage_iInf S.ι _).symm]
  refine (isAffineOpen_iInf_basicOpen S s).preimage_of_isOpenImmersion S.ι ?_
  rw [Scheme.Opens.opensRange_ι]
  exact le_trans (iInf_le _ 0) (le_iSup S.basicOpen (s 0))

/-- The covering `𝒰`, reindexed by a universe lift of `Fin r`. The Čech theory of
[Stacks, Tag 08C1] indexes a covering by a type in the universe of the space. -/
abbrev coverUlift (i : ULift.{u} (Fin S.r)) : S.scheme.Opens := S.cover i.down

/-- The reindexed covering still covers `U`. -/
theorem iSup_coverUlift : (⊤ : S.scheme.Opens) = ⨆ i, S.coverUlift i :=
  (((Equiv.ulift (α := Fin S.r)).iSup_comp (g := S.cover)).trans S.iSup_cover).symm

/-- A finite intersection of members of the reindexed covering is an affine open of `U`. -/
theorem isAffineOpen_iInf_coverUlift {m : ℕ} (s : Fin (m + 1) → ULift.{u} (Fin S.r)) :
    IsAffineOpen (⨅ k, S.coverUlift (s k)) :=
  S.isAffineOpen_iInf_cover fun k ↦ (s k).down

attribute [local instance] HasDerivedCategory.standard

/-- The underlying statement of [Stacks, Tag 08D2] in `D(Ab)`: for a complex `F^•` of
quasi-coherent `𝒪_U`-modules the comparison map `Tot(Č_alt^•(𝒰, F^•)) ⟶ RΓ(U, F^•)` of
[Stacks, Tag 08C1] is an isomorphism. -/
theorem isIso_alternatingCechToDerivedComparison (F : CochainComplex S.scheme.Modules ℤ)
    (hF : ∀ n, (F.X n).IsQuasicoherent) :
    IsIso ((Stacks.Cech.alternatingCechToDerivedComparison (TopCat.of S.scheme)
      S.scheme.ringCatSheaf S.coverUlift S.iSup_coverUlift).app F) :=
  Stacks.Cohomology.AlternatingCech.isIso_alternatingCechToDerivedComparison_of_isAffineOpen
    S.scheme S.coverUlift S.iSup_coverUlift (fun _ s ↦ S.isAffineOpen_iInf_coverUlift s) F hF

/-- The ring map `A ⟶ Γ(U, 𝒪_U)` induced by the open immersion `U ⟶ X = Spec(A)`, followed by
multiplication: `A` acting on every `𝒪_U`-module, naturally in the module. -/
def baseCenter : S.A →+* CatCenter (SheafOfModules.{u} S.scheme.ringCatSheaf) :=
  (Stacks.SheafOfModules.terminalSectionRingHom S.scheme.ringCatSheaf ⊤ isTerminalTop).comp
    (Stacks.Cech.globalRingHom S.ι).hom

/-- On the complex of sections over `U` of a complex of `𝒪_U`-modules, `a ∈ A` acts by its
image in `Γ(U, 𝒪_U)`. -/
theorem baseCenter_smul_sections (K : CochainComplex S.scheme.Modules ℤ) (n : ℤ) (a : S.A)
    (x : ((Stacks.Cech.linearGlobalSectionsComplexFunctor (TopCat.of S.scheme)
      S.scheme.ringCatSheaf S.baseCenter).obj K).X n) :
    (a • x).down = (show S.scheme.ringCatSheaf.obj.obj (op ⊤) from
      (Stacks.Cech.globalRingHom S.ι).hom a) • (show (K.X n).val.obj (op ⊤) from x.down) :=
  Scheme.smul_val_app_top S.scheme S.A (Stacks.Cech.globalRingHom S.ι).hom a (𝟙 (K.X n)) x.down

/-- **Stacks Project, Tag 08D2.** In the situation of [Stacks, Tag 08CZ], for a complex `F^•`
of quasi-coherent `𝒪_U`-modules the comparison map `Tot(Č_alt^•(𝒰, F^•)) ⟶ RΓ(U, F^•)` of
[Stacks, Tag 08C1], taken in `D(A)`, is an isomorphism. -/
@[stacks 08D2 "the canonical map in D(A) is an isomorphism"]
theorem isIso_linearAlternatingCechToDerivedComparison (F : CochainComplex S.scheme.Modules ℤ)
    (hF : ∀ n, (F.X n).IsQuasicoherent) :
    IsIso ((Stacks.Cech.linearAlternatingCechToDerivedComparison (TopCat.of S.scheme)
      S.scheme.ringCatSheaf S.baseCenter S.coverUlift S.iSup_coverUlift).app F) :=
  (Stacks.Cech.isIso_linearAlternatingCechToDerivedComparison_app_iff _ _ _ _ _ F).mpr
    (S.isIso_alternatingCechToDerivedComparison F hF)

/-- The complexes of `𝒪_U`-modules whose terms are quasi-coherent. -/
abbrev QuasicoherentComplex : ObjectProperty (CochainComplex S.scheme.Modules ℤ) :=
  fun F ↦ ∀ n, (F.X n).IsQuasicoherent

/-- **Stacks Project, Tag 08D2.** In the situation of [Stacks, Tag 08CZ], the canonical
isomorphism `Tot(Č_alt^•(𝒰, F^•)) ≅ RΓ(U, F^•)` in `D(A)`, natural in the complex `F^•` of
quasi-coherent `𝒪_U`-modules: its components are the comparison maps of [Stacks, Tag 08C1]. -/
@[stacks 08D2 "the isomorphism in D(A), functorial in F^•"]
def alternatingCechTotalNatIsoDerivedSections :
    S.QuasicoherentComplex.ι ⋙
        Stacks.Cech.linearAlternatingCechDerivedFunctor (TopCat.of S.scheme)
          S.scheme.ringCatSheaf S.baseCenter S.coverUlift ≅
      S.QuasicoherentComplex.ι ⋙
        Stacks.Cech.linearUnboundedDerivedGlobalSectionsFunctor (TopCat.of S.scheme)
          S.scheme.ringCatSheaf S.baseCenter :=
  haveI : ∀ F : S.QuasicoherentComplex.FullSubcategory, IsIso ((Functor.whiskerLeft
      S.QuasicoherentComplex.ι (Stacks.Cech.linearAlternatingCechToDerivedComparison
        (TopCat.of S.scheme) S.scheme.ringCatSheaf S.baseCenter S.coverUlift
        S.iSup_coverUlift)).app F) :=
    fun F ↦ S.isIso_linearAlternatingCechToDerivedComparison F.obj F.property
  haveI := NatIso.isIso_of_isIso_app (Functor.whiskerLeft S.QuasicoherentComplex.ι
    (Stacks.Cech.linearAlternatingCechToDerivedComparison (TopCat.of S.scheme)
      S.scheme.ringCatSheaf S.baseCenter S.coverUlift S.iSup_coverUlift))
  asIso (Functor.whiskerLeft S.QuasicoherentComplex.ι
    (Stacks.Cech.linearAlternatingCechToDerivedComparison (TopCat.of S.scheme)
      S.scheme.ringCatSheaf S.baseCenter S.coverUlift S.iSup_coverUlift))

/-- The components of the isomorphism of [Stacks, Tag 08D2] are the comparison maps of
[Stacks, Tag 08C1] in `D(A)`. -/
theorem alternatingCechTotalNatIsoDerivedSections_hom_app
    (F : S.QuasicoherentComplex.FullSubcategory) :
    S.alternatingCechTotalNatIsoDerivedSections.hom.app F =
      (Stacks.Cech.linearAlternatingCechToDerivedComparison (TopCat.of S.scheme)
        S.scheme.ringCatSheaf S.baseCenter S.coverUlift S.iSup_coverUlift).app F.obj :=
  rfl

/-- **Tag 08D2 for a complex on `X`.** For a complex `F^•` of quasi-coherent `𝒪_X`-modules the
comparison map in `D(A)` for the restriction of `F^•` to `U` is an isomorphism; restriction
along an open immersion preserves quasi-coherence. -/
theorem isIso_linearAlternatingCechToDerivedComparison_restrict
    (F : CochainComplex S.X.Modules ℤ) (hF : ∀ n, (F.X n).IsQuasicoherent) :
    IsIso ((Stacks.Cech.linearAlternatingCechToDerivedComparison (TopCat.of S.scheme)
      S.scheme.ringCatSheaf S.baseCenter S.coverUlift S.iSup_coverUlift).app
      (((Scheme.Modules.restrictFunctor S.ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj F)) :=
  S.isIso_linearAlternatingCechToDerivedComparison _ fun n ↦ by
    have := hF n
    exact Scheme.Modules.isQuasicoherent_restrictFunctor S.ι (F.X n)

end CechSituation

end Koszul

end
