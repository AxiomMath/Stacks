module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentCharacterization
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessUnconditional
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedTensorProjection
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShift
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualAtTheSpaceHypothesis
import StacksCore.Tactic.StacksAttribute

/-!
# Characterizing coherent modules on a scheme proper over a field: (1) ⇒ (2) unconditionally

Let `X` be a scheme proper over a field `k` and let `K` be an object of `D_QCoh(𝒪_X)`.
[Stacks, Tag 0FYD] asserts that the following are *equivalent*:

1. `K` is in `D^b_Coh(𝒪_X)`, and
2. `∑_{i ∈ ℤ} dim_k Ext^i_X(E, K)` is finite for every perfect object `E` of `D(𝒪_X)`.

This file proves the implication (1) ⇒ (2) of that equivalence, at the source's own hypotheses:
`X` proper over `k` and `K` in `D^b_Coh(𝒪_X)`, with no further assumption. The converse
(2) ⇒ (1) is not part of what this file proves; the implementation note "The converse" below
records, tag by tag, what the source's two routes to it require.

`StacksFrontier/AlgebraicGeometry/DerivedVarieties/CoherentCharacterization.lean` states the same
implication with the two inputs of its route through [Stacks, Tag 0FYC] — finiteness of each
`Ext` module and the dual perfect complex — as arguments; this file proves both inputs and needs
neither.

The sum in (2) is the cardinal sum `Cardinal.sum` of the `k`-ranks of the `Ext` modules over the
whole of `ℤ`, and "finite" is `< ℵ₀`; so (2) is the finiteness of the *total* dimension, not the
weaker statement that each `Ext^i_X(E, K)` is finite-dimensional.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.DerivedVarieties.CoherentCharacterization`.

* `isLE_derivedSheafHom_of_isPerfect`: `R𝓗om_{𝒪_X}(E, K)` is cohomologically bounded above when
  `E` is perfect and `K` is bounded above.
* `finite_setOf_not_subsingleton_ext_of_isPerfect`: `Ext^n_X(E, K) = 0` for all but finitely many
  `n`, for `E` perfect and `K` in `D^b_Coh(𝒪_X)` on a scheme proper over a field.
* `cardinalSum_rank_ext_lt_aleph0_of_derivedCategoryBBounded_of_model`: the implication
  (1) ⇒ (2), quantified over a model of derived global sections.
* `hasFiniteTotalExt_of_derivedCategoryBBounded_of_model`: the same, in the `HasFiniteTotalExt`
  spelling.
* `canonicalDerivedSections`, `canonicalDerivedSectionsUnit`: the canonical such model, the total
  right derived functor of termwise global sections and its unit, which exist for every scheme.
* `cardinalSum_rank_ext_lt_aleph0_of_derivedCategoryBBounded'` and
  `hasFiniteTotalExt_of_derivedCategoryBBounded'`: **[Stacks, Tag 0FYD], the implication
  (1) ⇒ (2)**, the two previous statements with the model quantifier discharged, so that nothing
  but `X` proper over `k` and `K` in `D^b_Coh(𝒪_X)` is assumed. These carry the tag.

## Implementation notes

**How (1) ⇒ (2) is proved.** The total sum is finite exactly when every summand is finite and
only finitely many summands are nonzero (`lt_aleph0_cardinalSum_iff` of
`CoherentCharacterization.lean`), and the two halves are proved separately.

* Finiteness of each `Ext^n_X(E, K)` over `k` is [Stacks, Tag 0D0D],
  `Stacks.AlgebraicGeometry.ProperSupportCoherent.moduleFinite_ext_of_proper`: a field is
  Noetherian, `K` lies in `D^+_Coh(𝒪_X)` because it is bounded with coherent cohomology, and the
  perfect object `E` lies in `D^-_Coh(𝒪_X)` by [Stacks, Tag 0FXU].
* Finiteness of the set of degrees in which `Ext^n_X(E, K)` is nonzero is
  `finite_setOf_not_subsingleton_ext_of_isPerfect`. Write `H = R𝓗om_{𝒪_X}(E, K)`. Below the
  range the groups vanish by orthogonality of the t-structure, `E` lying in degrees `≤ b` and
  `K⟦n⟧` in degrees `≥ c - n`. Above the range they vanish because
  `Ext^n_X(E, K) = H^n(X, H)` ([Stacks, Tag 0B6E], in the form
  `AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv`), `H` is bounded above by
  `isLE_derivedSheafHom_of_isPerfect` and has coherent — hence quasi-coherent — cohomology by
  [Stacks, Tag 0D0C], and derived global sections of an object with quasi-coherent cohomology
  lying in degrees `≤ q` lie in degrees `≤ q + N - 1` for an `N` depending only on `X`
  ([Stacks, Tags 071L and 08D4], in the form
  `AlgebraicGeometry.isLE_rightDerivedSections_obj_of_isQuasicoherent`).

**Boundedness above of the derived internal Hom** is where the perfectness of `E` is used, and
it is the one place where [Stacks, Tag 08DQ] enters. The dual `E^∨ = R𝓗om_{𝒪_X}(E, 𝒪_X)` is
perfect by the first assertion of that tag, hence lies in `D^b_Coh(𝒪_X)` by [Stacks, Tag 0FXU]
and so is bounded above; the canonical map `K ⊗^𝐋_{𝒪_X} E^∨ ⟶ R𝓗om_{𝒪_X}(E, K)` of
[Stacks, Tag 08I1] is invertible by the third assertion of [Stacks, Tag 08DQ]; and the derived
tensor product of two objects bounded above is bounded above.

**The passage between the two derived global-sections functors.** [Stacks, Tag 0B6E] reads
`Ext^n` off the abelian-group-valued derived global sections
`Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections` of the ringed site of `X`, while
the cohomological-dimension bound is stated for a derived global-sections functor valued in
modules over `Γ(X, 𝒪_X)`. `derivedForgetIso` identifies the second, with its scalars forgotten,
with the first: both are right derived functors of the abelian-group-valued global sections, by
`Stacks.AlgebraicGeometry.ProperSupportCoherent.derivedLinearSectionsForgetIso` and the
universal property of a right derived functor. `isZero_homology_derivedModuleGlobalSections` is
the consequence used, that a vanishing cohomology module of the one is a vanishing
hypercohomology group of the other.

**The converse, (2) ⇒ (1).** The source gives two routes, and each needs a result this library
does not carry.

* The proper-case route is through More on Morphisms [Stacks, Tag 0GET], whose conclusion is
  that `K` is `Spec k`-perfect; Derived Categories of Schemes [Stacks, Tag 0DI1] then identifies
  that with `D^b_Coh(𝒪_X)`, and the library does carry 0DI1 in the form
  `AlgebraicGeometry.isPerfectRelativeTo_canonical_iff_boundedCoherent`. The library's 0GET,
  `AlgebraicGeometry.eventually_subsingleton_ext_of_derivedGlobalSections_isPerfect`, proves the
  vanishing that the tag's hypothesis produces — that `Ext^i_X(G, K)` and `Hom(G⟦-i⟧, K)` vanish
  for `i ≪ 0` — and not relative perfectness, which in the source's proof rests on
  [Stacks, Tag 0GES], on the implication (2) ⇒ (1) of [Stacks, Tag 0GEH], and on condition (1)
  of [Stacks, Tag 0GEQ].
* The projective-case route assumes `X` projective over `k`, pushes forward along a closed
  immersion `i : X → ℙⁿ_k` and concludes by the implication (4) ⇒ (1) of [Stacks, Tag 0FYB],
  whose proof runs through the Beilinson equivalence over the upper triangular algebra of
  [Stacks, Tag 0CS9] and through regularity of `ℙⁿ_k`.

**Spellings.** `D^b_Coh(𝒪_X)` is `DerivedCategoryB.derivedCategoryBBounded` at the coherence
predicate; `Ext^i_X(E, K)` is `DerivedCategory.Ext`, that is `Hom_{D(𝒪_X)}(E, K⟦i⟧)`;
perfectness is `Stacks.Cohomology.PerfectComplexes.IsPerfect`, the ringed-space notion of
[Stacks, Tag 08CM]; "proper over a field" is `IsProper` on the structure morphism of an object
of `Over (Spec k)`; the `k`-module structure in which `dim_k` is taken is
`AlgebraicGeometry.modulesLinear`, induced by that structure morphism; and the conjunction form
of the finiteness condition is
`Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.HasFiniteTotalExt`. `RΓ(X, -)`
enters as a functor together with a comparison from underived global sections carrying the
right-derived-functor instance, exactly as in [Stacks, Tag 0FYC]; that is a device for model
independence and not a hypothesis on the geometry, and the tagged statements do not carry it at
all — `Functor.HasRightDerivedFunctor` holds for every scheme by instance search, so the device
is discharged at `canonicalDerivedSections` and the conclusion, which mentions no model, is
unchanged. The derived internal Hom is the one of
[Stacks, Tag 0A97] read at the ringed site of opens of `X`; the derived tensor product used in
the boundedness argument is the site-indexed packaging of [Stacks, Tag 06YU] that the derived
dual cluster is stated at, compared with the structure-sheaf-indexed one by
`AlgebraicGeometry.RingedSite.derivedTensorProductDatumOfSite`. The derived category is the
standard model, at the priority used by [Stacks, Tag 0FYC].

## References

* [Stacks Project, Tag 0FYD](https://stacks.math.columbia.edu/tag/0FYD)
* [Stacks Project, Tag 0FYC](https://stacks.math.columbia.edu/tag/0FYC)
* [Stacks Project, Tag 0FYB](https://stacks.math.columbia.edu/tag/0FYB)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
* [Stacks Project, Tag 0D0D](https://stacks.math.columbia.edu/tag/0D0D)
* [Stacks Project, Tag 0D0C](https://stacks.math.columbia.edu/tag/0D0C)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology (sectionsFunctor)

universe u

namespace Stacks.AlgebraicGeometry.DerivedVarieties.CoherentCharacterization

attribute [local instance 100000] HasDerivedCategory.standard

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

attribute [local instance] linearModulesOverTheField

/-! ### Boundedness above of the derived internal Hom out of a perfect object -/

/-- **The derived tensor product adds cohomological upper bounds**, in the site-indexed
packaging of [Stacks, Tag 06YU] that the derived dual cluster of [Stacks, Tag 08DQ] is stated
at. This is `Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct` applied to the datum
`AlgebraicGeometry.RingedSite.derivedTensorProductDatumOfSite`, which reads the site-indexed
derived tensor product as a structure-sheaf-indexed one with the same bifunctor, and with the
two boundedness hypotheses taken explicitly so that the statement applies to objects presented
at the `AlgebraicGeometry.Scheme.Modules` spelling of the category of modules. -/
@[sga "6 I 2.16" "special case",
  sga "6 III 1.11" "(a), special case",
  sga "6 III 1.8" "special case"]
theorem isLE_derivedTensor (X : Scheme.{u}) (K L : DerivedCategory X.Modules) (a b : ℤ)
    (hK : K.IsLE a) (hL : L.IsLE b) :
    (((Stacks.SheafOfModules.derivedTensor X.sheaf).obj K).obj L).IsLE (a + b) := by
  have h : ∀ K' L' : Stacks.DerivedTensor.RingedSite.DerivedModules X.sheaf,
      K'.IsLE a → L'.IsLE b →
      (((Stacks.SheafOfModules.derivedTensor X.sheaf).obj K').obj L').IsLE (a + b) := by
    intro K' L' h1 h2
    have := h1
    have := h2
    exact Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct X.sheaf
      (_root_.AlgebraicGeometry.RingedSite.derivedTensorProductDatumOfSite
        (Stacks.SheafOfModules.ringedSite X.sheaf)
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct
          (Stacks.SheafOfModules.ringedSite X.sheaf)))
      K' L' a b
  exact h K L hK hL

/-- **The derived internal Hom out of a perfect object into a bounded-above object is bounded
above.** Let `X` be a Noetherian scheme, let `E` be a perfect object of `D(𝒪_X)` and let `K` be
an object of `D(𝒪_X)` whose cohomology vanishes above `d`. Then the cohomology of
`R𝓗om_{𝒪_X}(E, K)` vanishes above some degree.

The dual `E^∨ = R𝓗om_{𝒪_X}(E, 𝒪_X)` is perfect by the first assertion of [Stacks, Tag 08DQ],
hence lies in `D^b_Coh(𝒪_X)` by [Stacks, Tag 0FXU] and so vanishes above some `u`; the derived
tensor product `K ⊗^𝐋_{𝒪_X} E^∨` therefore vanishes above `d + u`; and the canonical map
`K ⊗^𝐋_{𝒪_X} E^∨ ⟶ R𝓗om_{𝒪_X}(E, K)` of [Stacks, Tag 08I1] is an isomorphism by the third
assertion of [Stacks, Tag 08DQ]. -/
theorem isLE_derivedSheafHom_of_isPerfect (X : Scheme.{u}) [_root_.AlgebraicGeometry.IsNoetherian X]
    (E K : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (d : ℤ) (hK : K.IsLE d) :
    ∃ q : ℤ, (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op E)).obj K).IsLE q := by
  have hdual := Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace X.toRingedSpace E hE
  obtain ⟨u, hu⟩ :=
    (Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect X _ hdual).1.2
  have hdLE : (Stacks.SheafOfModules.derivedDual X.sheaf E).IsLE u :=
    (DerivedCategory.isLE_iff _ u).mpr hu
  refine ⟨d + u, ?_⟩
  have hten := isLE_derivedTensor X K (Stacks.SheafOfModules.derivedDual X.sheaf E) d u hK hdLE
  have hiso := Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_of_isPerfectSpace
    X.toRingedSpace E K hE
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (asIso (Stacks.SheafOfModules.derivedTensorDualToSheafHom X.sheaf E K)) (d + u)

/-! ### Reading `Ext` off the global derived hom -/

section Bridge

open Stacks.Cohomology.ModuleSections
open Stacks.AlgebraicGeometry.ProperSupportCoherent

variable (X : Scheme.{u})

/-- Global sections over the whole space, read at the ringed-site spelling of the category of
`𝒪_X`-modules. It is `Stacks.Cohomology.sectionsFunctor X ⊤` by `rfl`; the type ascription is
what keeps the instance searches below inside the spelling that
`Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections` is stated at. -/
abbrev siteTopSections :
    _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.SheafOfModules.ringedSite X.sheaf).O) ⥤
      ModuleCat.{u} Γ(X, ⊤) :=
  sectionsFunctor X ⊤

/-- Global sections over the whole space is an additive functor; addition of sections of a sheaf
of modules is computed open by open. -/
instance siteTopSections_additive : (siteTopSections X).Additive where
  map_add := rfl

/-- **Global sections over the whole space, with the scalars forgotten, are the
abelian-group-valued global sections of the ringed site of the space.** Forgetting the scalars
does not change the underlying abelian group, and on the site of opens a compatible family of
sections is its value at the terminal open `⊤`. -/
def topSectionsForgetIso :
    siteTopSections X ⋙ forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ≅
      moduleGlobalSections (Stacks.SheafOfModules.ringedSite X.sheaf) :=
  Stacks.Cohomology.ModuleComparison.evaluationCompForgetIso
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O) ⊤ ≪≫
    Functor.isoWhiskerLeft
      (_root_.SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (Stacks.SheafOfModules.ringedSite X.sheaf).O))
      (abelianGlobalSectionsTopIso X.sheaf).symm

variable
  (RΓ : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O)) ⥤
    DerivedCategory (ModuleCat.{u} Γ(X, ⊤)))
  (α : (siteTopSections X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RΓ)
  [RΓ.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (Stacks.SheafOfModules.ringedSite X.sheaf).O))
      (ComplexShape.up ℤ))]

/-- **Any derived global-sections functor, with the scalars forgotten, is the
abelian-group-valued derived global sections of the ringed site of the space.** It agrees with
the chosen total right derived functor of global sections by the universal property of a right
derived functor, and that one is identified with derived global sections of the site by
`Stacks.AlgebraicGeometry.ProperSupportCoherent.derivedLinearSectionsForgetIso`. -/
def derivedForgetIso :
    RΓ ⋙ (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).mapDerivedCategory ≅
      derivedModuleGlobalSections (Stacks.SheafOfModules.ringedSite X.sheaf) :=
  Functor.isoWhiskerRight
      (Functor.rightDerivedUnique RΓ
        (derivedLinearSections (Z := Stacks.SheafOfModules.ringedSite X.sheaf)
          (siteTopSections X)) α
        (derivedLinearSectionsUnit (Z := Stacks.SheafOfModules.ringedSite X.sheaf)
          (siteTopSections X))
        (HomotopyCategory.quasiIso
          (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
              (Stacks.SheafOfModules.ringedSite X.sheaf).O))
          (ComplexShape.up ℤ)))
      (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).mapDerivedCategory ≪≫
    derivedLinearSectionsForgetIso (Z := Stacks.SheafOfModules.ringedSite X.sheaf)
      (siteTopSections X) (topSectionsForgetIso X)

include α in
/-- **A vanishing cohomology module of derived global sections is a vanishing hypercohomology
group of the ringed site.** The forgetful functor is additive, so it carries the zero module to
the zero group, and it commutes with homology on the derived category because it is exact. -/
theorem isZero_homology_derivedModuleGlobalSections (n : ℤ)
    (W : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O)))
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) n).obj
      (RΓ.obj W))) :
    IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((derivedModuleGlobalSections (Stacks.SheafOfModules.ringedSite X.sheaf)).obj W)) := by
  have h1 : IsZero ((forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) n).obj (RΓ.obj W))) :=
    Functor.map_isZero _ h
  refine h1.of_iso ?_
  exact (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
      ((derivedForgetIso X RΓ α).app W).symm ≪≫
    (Stacks.Homology.derivedHomologyIso
      (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}) n).app (RΓ.obj W)

/-- **Vanishing of the degree-`n` hypercohomology of the derived internal Hom makes the group of
morphisms into the `n`-fold shift vanish.** This is [Stacks, Tag 0B6E] in the form
`AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv`, which identifies the degree-`n`
cohomology of `RHom_{𝒪_X}(E, K) = RΓ(X, R𝓗om_{𝒪_X}(E, K))` with `Hom_{D(𝒪_X)}(E, K⟦n⟧)`. -/
theorem subsingleton_hom_shift_of_isZero (n : ℤ)
    (E K : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O)))
    (h : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      (((_root_.AlgebraicGeometry.RingedSite.globalDerivedHom
        (Stacks.SheafOfModules.ringedSite X.sheaf)).obj (op E)).obj K))) :
    Subsingleton (E ⟶ K⟦n⟧) :=
  have := AddCommGrpCat.subsingleton_of_isZero h
  (_root_.AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv
    (Stacks.SheafOfModules.ringedSite X.sheaf) E K n).toEquiv.symm.subsingleton

end Bridge

/-! ### Stacks 0FYD, the implication (1) ⇒ (2) -/

section Main

open Stacks.Cohomology.ModuleSections

variable {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]
  (RΓ : DerivedCategory X.left.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X.left, ⊤)))
  (α : (sectionsFunctor X.left ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RΓ)
  [RΓ.IsRightDerivedFunctor α (HomotopyCategory.quasiIso X.left.Modules (ComplexShape.up ℤ))]
  (K : DerivedCategory X.left.Modules)

include α in
/-- **Only finitely many of the `Ext` modules are nonzero.** Let `X` be a scheme proper over a
field `k`, let `E` be a perfect object of `D(𝒪_X)` and let `K` be an object of `D^b_Coh(𝒪_X)`.
Then `Ext^n_X(E, K) = 0` for all but finitely many `n`.

Write `H = R𝓗om_{𝒪_X}(E, K)`, let `E` lie in degrees `≤ b` and `K` in degrees `[c, d]`, let `H`
lie in degrees `≤ q` by `isLE_derivedSheafHom_of_isPerfect`, and let `N` be the
cohomological-dimension bound of `X`. Outside `[c - b, q + N - 1]` the group vanishes:

* for `n < c - b`, because `E` lies in degrees `≤ b`, the shift `K⟦n⟧` lies in degrees
  `≥ c - n > b`, and the t-structure has no morphisms from the one to the other;
* for `n > q + N - 1`, because `Ext^n_X(E, K) = H^n(X, H)` by [Stacks, Tag 0B6E], the cohomology
  sheaves of `H` are coherent — hence quasi-coherent — by [Stacks, Tag 0D0C], and derived global
  sections carry an object with quasi-coherent cohomology in degrees `≤ q` into degrees
  `≤ q + N - 1` by [Stacks, Tags 071L and 08D4].

This is the unconditional form of the half of [Stacks, Tag 0FYC] that
`Stacks.AlgebraicGeometry.ProperSupportCoherent.finite_setOf_not_subsingleton_ext_of_isPerfect`
proves from [Stacks, Tag 09M4]: that route consumes the dual perfect complex of
[Stacks, Tag 08DQ] as data, whereas here the dual is produced from the perfectness of `E` and
enters only through `isLE_derivedSheafHom_of_isPerfect`.

The two are therefore not copies of one statement: this one carries no
`Stacks.DerivedQCoh.DualPerfectComplexData` argument, so with the same conclusion it is strictly
the more general of the two. Both sit at the same universes and differ in namespace, so a search
by short name alone reports them as a clash; merging them would discard that generality. -/
theorem finite_setOf_not_subsingleton_ext_of_isPerfect
    (E : DerivedCategory X.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace) E)
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.left.Modules => M.IsCoherent) K) :
    {n : ℤ | ¬ Subsingleton (DerivedCategory.Ext E K n)}.Finite := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have hnoe : _root_.AlgebraicGeometry.IsNoetherian X.left :=
    ProperSupportCoherent.isNoetherian_of_isProper_over_field X
  have : IsLocallyNoetherian X.left := inferInstance
  have hEbc :=
    Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect X.left E hE
  obtain ⟨bE, hbE⟩ := hEbc.1.2
  obtain ⟨c, hc⟩ := hK.1.1
  obtain ⟨d, hd⟩ := hK.1.2
  have hELE : E.IsLE bE := (DerivedCategory.isLE_iff E bE).mpr hbE
  have hKGE : K.IsGE c := (DerivedCategory.isGE_iff K c).mpr hc
  have hKLE : K.IsLE d := (DerivedCategory.isLE_iff K d).mpr hd
  obtain ⟨q, hq⟩ := isLE_derivedSheafHom_of_isPerfect X.left E K hE d hKLE
  obtain ⟨N, hN⟩ :=
    _root_.AlgebraicGeometry.isLE_rightDerivedSections_obj_of_isQuasicoherent X.left RΓ α
  have hcoh := _root_.AlgebraicGeometry.derivedCategoryBPlus_isCoherent_derivedSheafHom X.left E K
    ⟨hEbc.1.2, fun m => CoherentAbelian.isCoherent_iff_stacksIsCoherent.mp (hEbc.2 m)⟩
    ⟨hK.1.1, fun m => CoherentAbelian.isCoherent_iff_stacksIsCoherent.mp (hK.2 m)⟩
  have hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.left.Modules i).obj
      (((Stacks.SheafOfModules.derivedSheafHom X.left.sheaf).obj
        (op E)).obj K)).IsQuasicoherent := by
    intro i
    have hci : _root_.SheafOfModules.IsCoherent
        ((DerivedCategory.homologyFunctor X.left.Modules i).obj
          (((Stacks.SheafOfModules.derivedSheafHom X.left.sheaf).obj (op E)).obj K)) :=
      CoherentAbelian.isCoherent_iff_stacksIsCoherent.mpr (hcoh.2 i)
    exact isQuasicoherent_of_isCoherent _
  have hRΓLE := hN (((Stacks.SheafOfModules.derivedSheafHom X.left.sheaf).obj (op E)).obj K)
    q hqc hq
  refine Set.Finite.subset (Set.finite_Icc (c - bE) (q + N - 1)) ?_
  intro n hn
  replace hn : ¬ Subsingleton (DerivedCategory.Ext E K n) := hn
  by_contra hmem
  simp only [Set.mem_Icc, not_and_or, not_le] at hmem
  refine hn ?_
  rcases hmem with hlt | hlt
  · have hsh : (K⟦n⟧).IsGE (c - n) :=
      DerivedCategory.TStructure.t.isGE_shift K c n (c - n) (by omega)
    exact ⟨fun f g => by
      rw [DerivedCategory.TStructure.t.zero_of_isLE_of_isGE f bE (c - n) (by omega) hELE hsh,
        DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g bE (c - n) (by omega) hELE hsh]⟩
  · have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X.left, ⊤)) n).obj
        (RΓ.obj (((Stacks.SheafOfModules.derivedSheafHom X.left.sheaf).obj (op E)).obj K))) :=
      DerivedCategory.isZero_of_isLE _ (q + N - 1) n (by omega) (hX := hRΓLE)
    have hinst : RΓ.IsRightDerivedFunctor α
        (HomotopyCategory.quasiIso X.left.Modules (ComplexShape.up ℤ)) := inferInstance
    have hz' := @isZero_homology_derivedModuleGlobalSections X.left RΓ α hinst n
      (((Stacks.SheafOfModules.derivedSheafHom X.left.sheaf).obj (op E)).obj K) hz
    exact subsingleton_hom_shift_of_isZero X.left n E K hz'

include α in
/-- **Stacks Project, Tag 0FYD, the implication (1) ⇒ (2).** Let `X` be a scheme proper over a
field `k` and let `K` be an object of `D^b_Coh(𝒪_X)`. Then

`∑_{i ∈ ℤ} dim_k Ext^i_X(E, K) < ∞`

for every perfect object `E` of `D(𝒪_X)`, the dimensions being taken for the canonical
`k`-structure induced by the structure morphism `X ⟶ Spec k`, the sum being the cardinal sum over
all of `ℤ` and `< ∞` being `< ℵ₀`.

The total sum is finite exactly when every summand is finite and only finitely many summands are
nonzero. Every summand is finite by [Stacks, Tag 0D0D]: a field is Noetherian, `K` lies in
`D^+_Coh(𝒪_X)`, and the perfect object `E` lies in `D^-_Coh(𝒪_X)` by [Stacks, Tag 0FXU]. Only
finitely many are nonzero by `finite_setOf_not_subsingleton_ext_of_isPerfect`.

This is the form that quantifies over the model `(RΓ, α)` of derived global sections. The
conclusion mentions no model, so instantiating it at the canonical one gives the same conclusion
with no model binders at all; that is
`cardinalSum_rank_ext_lt_aleph0_of_derivedCategoryBBounded'`, which is where the tag sits. -/
theorem cardinalSum_rank_ext_lt_aleph0_of_derivedCategoryBBounded_of_model
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.left.Modules => M.IsCoherent) K)
    (E : DerivedCategory X.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace) E) :
    Cardinal.sum (fun n : ℤ => Module.rank k (DerivedCategory.Ext E K n)) < Cardinal.aleph0 := by
  have hnoe : _root_.AlgebraicGeometry.IsNoetherian X.left :=
    ProperSupportCoherent.isNoetherian_of_isProper_over_field X
  have hEbc :=
    Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect X.left E hE
  have hfin : ∀ n : ℤ, Module.Finite k (DerivedCategory.Ext E K n) :=
    ProperSupportCoherent.moduleFinite_ext_of_proper X E K ⟨hEbc.1.2, hEbc.2⟩ ⟨hK.1.1, hK.2⟩
  refine ProperSupportCoherent.lt_aleph0_cardinalSum ?_
    fun n => Module.rank_lt_aleph0_iff.2 (hfin n)
  refine (finite_setOf_not_subsingleton_ext_of_isPerfect X RΓ α K E hE hK).subset ?_
  intro n hn hsub
  exact hn (rank_zero_iff.2 hsub)

include α in
/-- **Stacks Project, Tag 0FYD, the implication (1) ⇒ (2), in the `HasFiniteTotalExt`
spelling.** Let `X` be a scheme proper over a field `k` and let `K` be an object of
`D^b_Coh(𝒪_X)`. Then `∑_{i ∈ ℤ} dim_k Ext^i_X(E, K)` is finite for every perfect object `E` of
`D(𝒪_X)`, in the conjunction form
`Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.HasFiniteTotalExt` — condition (3) of
[Stacks, Tag 0FYB] — which `cardinalSum_rank_ext_lt_aleph0_iff_hasFiniteTotalExt` shows is the
same condition as the finiteness of the cardinal sum.

As above, this is the model-quantified form; the tag sits on the model-free
`hasFiniteTotalExt_of_derivedCategoryBBounded'`. -/
theorem hasFiniteTotalExt_of_derivedCategoryBBounded_of_model
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.left.Modules => M.IsCoherent) K)
    (E : DerivedCategory X.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace) E) :
    BeilinsonCoherentCharacterization.HasFiniteTotalExt k X E K :=
  (cardinalSum_rank_ext_lt_aleph0_iff_hasFiniteTotalExt X E K).1
    (cardinalSum_rank_ext_lt_aleph0_of_derivedCategoryBBounded_of_model X RΓ α K hK E hE)

end Main

/-! ### Stacks 0FYD, the implication (1) ⇒ (2), with no model of `RΓ` in the statement -/

section NoModel

open Stacks.Cohomology.ModuleSections

variable {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]
  (K : DerivedCategory X.left.Modules)

/-- **The canonical model of `RΓ(X, -)`**: the total right derived functor of termwise global
sections. It exists for every scheme — `Functor.HasRightDerivedFunctor` holds by instance search
— so the model `(RΓ, α)` that the statements in the previous section quantify over is never
vacuous, and the two theorems below are those statements with the quantifier discharged. -/
abbrev canonicalDerivedSections (Y : Scheme.{u}) :
    DerivedCategory Y.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(Y, ⊤)) :=
  ((sectionsFunctor Y ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))

/-- The comparison from termwise global sections to `canonicalDerivedSections`, the unit that
carries its right-derived-functor instance. -/
abbrev canonicalDerivedSectionsUnit (Y : Scheme.{u}) :
    (sectionsFunctor Y ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ canonicalDerivedSections Y :=
  ((sectionsFunctor Y ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))

/-- **Stacks Project, Tag 0FYD, the implication (1) ⇒ (2).** Let `X` be a scheme proper over a
field `k` and let `K` be an object of `D^b_Coh(𝒪_X)`. Then

`∑_{i ∈ ℤ} dim_k Ext^i_X(E, K) < ∞`

for every perfect object `E` of `D(𝒪_X)`.

The hypotheses are the source's and no others: `X` proper over the field `k`, and `K` bounded
with coherent cohomology. In particular no model of derived global sections appears — this is
`cardinalSum_rank_ext_lt_aleph0_of_derivedCategoryBBounded_of_model` at the canonical model
`canonicalDerivedSections`, whose existence is instance search. -/
@[stacks 0FYD "the implication (1) ⇒ (2), for X proper over a field; no model of RΓ in the \
statement"]
theorem cardinalSum_rank_ext_lt_aleph0_of_derivedCategoryBBounded'
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.left.Modules => M.IsCoherent) K)
    (E : DerivedCategory X.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace) E) :
    Cardinal.sum (fun n : ℤ => Module.rank k (DerivedCategory.Ext E K n)) < Cardinal.aleph0 :=
  cardinalSum_rank_ext_lt_aleph0_of_derivedCategoryBBounded_of_model X
    (canonicalDerivedSections X.left) (canonicalDerivedSectionsUnit X.left) K hK E hE

/-- **Stacks Project, Tag 0FYD, the implication (1) ⇒ (2), in the `HasFiniteTotalExt`
spelling**, with no model of derived global sections in the statement. -/
@[stacks 0FYD "the implication (1) ⇒ (2), as HasFiniteTotalExt, for X proper over a field; no \
model of RΓ in the statement"]
theorem hasFiniteTotalExt_of_derivedCategoryBBounded'
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.left.Modules => M.IsCoherent) K)
    (E : DerivedCategory X.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace) E) :
    BeilinsonCoherentCharacterization.HasFiniteTotalExt k X E K :=
  (cardinalSum_rank_ext_lt_aleph0_iff_hasFiniteTotalExt X E K).1
    (cardinalSum_rank_ext_lt_aleph0_of_derivedCategoryBBounded' X K hK E hE)

end NoModel

end Stacks.AlgebraicGeometry.DerivedVarieties.CoherentCharacterization

end
