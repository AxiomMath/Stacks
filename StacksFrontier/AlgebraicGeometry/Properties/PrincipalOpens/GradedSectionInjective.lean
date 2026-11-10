module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingSections
public import StacksFrontier.AlgebraicGeometry.ModuleSectionExtension.Localization
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GradedSectionsCore
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.NormAmple.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Generators
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Converse
public import StacksCore.Tactic.StacksAttribute

/-!
# The localized graded section map on a nonvanishing open

Let `X` be a quasi-compact scheme, let `L` be an invertible `𝒪_X`-module with global section `s`
and nonvanishing open `X_s`, and let `ℱ` be a quasi-coherent `𝒪_X`-module. This file proves that
the comparison map of [Stacks, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
`(⨁_n Γ(X, ℱ ⊗ L^{⊗ n}))_{(s)} ⟶ Γ(X_s, ℱ|_{X_s})`
is injective -- **part (1) of [Stacks, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)** --
and, for `X` moreover quasi-separated, bijective -- **part (2) of the same tag**.

## Main results

* `Stacks.SheafOfModules.exists_pow_smul_of_eq_zero_of_locally`: **the quasi-compact transport**,
  a twisted global section of `H ⊗ L^{⊗ j}` annihilated near every point by a power of a local
  equation for `s` is annihilated by one power of `s` in `⨁_j Γ(X, H ⊗ L^{⊗ j})`.
* `Stacks.SheafOfModules.exists_pow_smul_twistedSection_restrict_eq_zero`: **the local
  annihilator**, for `ℱ` quasi-coherent a global section of `ℱ ⊗ L^{⊗ n}` vanishing on `X_s` is
  killed near every point by a power of a local equation for `s`.
* `Stacks.SheafOfModules.exists_twistedSection_numerator`: every degree-zero fraction is a
  homogeneous twisted section divided by a power of `s`.
* `Stacks.SheafOfModules.restrict_eq_zero_of_sectionLocalizationMap_eq_zero`: the vanishing
  criterion, a fraction `m / sⁿ` sent to the zero section on `X_s` has `m` restricting to zero
  there.
* `Stacks.SheafOfModules.sectionLocalizationMap_injective_of_locally`: injectivity of the Tag
  0B5L comparison map, granted the local annihilation step.
* `Stacks.SheafOfModules.sectionLocalizationMap_injective`: **[Stacks, Tag 01PW] part (1)**.
* `Stacks.SheafOfModules.twistSectionByPower`: multiplication of a twisted section over an open
  by a power of `s`, raising the twist.
* `Stacks.SheafOfModules.HasTwistedChartExtension` and
  `Stacks.SheafOfModules.HasTwistedCompactAnnihilation`: the two chart-local steps of the proof
  of part (2), named as properties of the data.
* `Stacks.SheafOfModules.hasTwistedCompactAnnihilation`: **part (1) over a quasi-compact open**,
  the second of those two properties, proved.
* `Stacks.SheafOfModules.hasTwistedChartExtension`: **Tag 01P7 on an affine chart**, the first of
  those two properties, proved.
* `Stacks.SheafOfModules.sectionLocalizationMap_bijective`: **[Stacks, Tag 01PW] part (2)**.

## Implementation notes

The argument is the one in the source. A degree-zero fraction is a twisted global section `m` of
`ℱ ⊗ L^{⊗ n}` over `sⁿ`; since `sⁿ` generates `L^{⊗ n}` on `X_s`, dividing by it is the additive
equivalence `Γ(ℱ, X_s) ≃+ Γ(ℱ ⊗ L^{⊗ n}, X_s)` of
`Stacks.SheafOfModules.exists_tensorBasisAt`, so the fraction dies exactly when `m|_{X_s}` does.
Near a point choose an affine open `W` inside an open where `L` has a frame and an open where
`L^{⊗ n}` is trivial; the frame turns `s|_W` into `r · g` and identifies `X_s ∩ W` with
`X.basicOpen r`, the trivialization turns `m|_W` into a section of `ℱ` over `W`, and over an
affine open a section of a quasi-coherent module vanishing on a basic open is killed by a power of
its equation (Tag 01I9). Finally a power of `s` restricted to `W` is divisible by the matching
power of `r`, so the local annihilation passes to the graded action of Tag 01CV; raising the
exponent only multiplies by a further power of `s`, so on a quasi-compact space one exponent works
at every point of a finite cover and the sheaf condition assembles the vanishing.

Part (2) adds surjectivity. Over a chart on which `L` is trivialized a section `t` on `X_s` is,
by Tag 01P7, the fraction of a twisted section of `ℱ ⊗ L^{⊗ N}` by `sᴺ` for every large `N`, and
quasi-compactness of `X` makes one exponent `e` serve a finite cover by such charts. The chart
sections need not agree on a pairwise overlap, but that overlap is quasi-compact because `X` is
quasi-separated, so part (1) there forces agreement after multiplication by `s^{e'}` for one
exponent `e'`; the sheaf condition glues the multiplied sections to a global twisted section of
degree `e + e'` whose fraction by `s^{e + e'}` is `t`. The two chart-local steps are named as
properties of the data, `Stacks.SheafOfModules.HasTwistedChartExtension` and
`Stacks.SheafOfModules.HasTwistedCompactAnnihilation`: each speaks of a single open, neither
mentions the comparison map, and both are results of the source -- Tag 01P7 on an affine chart
trivializing `L`, and part (1) of this tag over a quasi-compact open. **Both are proved here**,
so part (2) carries no hypothesis of its own.

For `Stacks.SheafOfModules.hasTwistedCompactAnnihilation`: on an affine chart inside opens
trivializing `L` and `L^{⊗ n}` the difference of the two sections is killed by a power of the
local equation `r` of `s` (Tag 01I9 for a quasi-coherent module), the matching power of `s` is
divisible by that power of `r`, and quasi-compactness of the open makes one exponent serve a
finite cover, so the sheaf condition identifies the multiplied sections.

For `Stacks.SheafOfModules.hasTwistedChartExtension`: on an affine chart `A` inside an open
where `L` has a frame, the frame identifies `A ⊓ X_s` with `X.basicOpen r`, Tag 01P7 for a
quasi-coherent module extends `rᵉ · t|` to a section `c` over `A`, and `r^{N-e} · c` tensored
with the `N`-th divided power `qᴺ` of `s` on the chart -- the section with `sᴺ|_A = rᴺ · qᴺ` --
is the required twisted section, because over the basic open `rᴺ · t| = r^{N-e} · c|`.

The finite cover, the two uniform exponents, the overlap comparison, the gluing and the fraction
are proved here.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

namespace Stacks.SheafOfModules

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace Opposite DirectSum Limits
open scoped _root_.TensorProduct

universe u

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars

section TwistedSectionAnnihilator

attribute [-instance] CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape

attribute [local implicit_reducible] ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' TensorSheafification.structureSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

attribute [local instance] monoidalCategoryPresheafOfModules symmetricCategoryPresheafOfModules

open MonoidalCategory

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv
  Stacks.SchemeModulesSpelling.sectionRingGradedRing
  Stacks.SchemeModulesSpelling.sectionRingGradingGradedRing
  Stacks.SchemeModulesSpelling.sectionModuleModule

variable (H : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- Acting by `s ^ e` on a homogeneous element of the section module places the graded action in
degree `e + j`. -/
private theorem pow_smul_of (s : L.sections) (e : ℕ) (j : ℤ)
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L j)))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    homogeneousSection X L s ^ e • (DirectSum.of _ j t :
        sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H) =
      DirectSum.of _ ((e : ℤ) + j)
        (sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L H e j
          (sectionPower X L s e) t) := by
  refine Eq.trans (congrArg (fun c => c • (DirectSum.of _ j t :
    sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H))
    (homogeneousSection_pow_eq_of_sectionPower X L s e)) ?_
  exact (chosenModuleStructure (sectionSiteRing X) (sectionSiteSheaf X) L H).smul_eq e j
    (sectionPower X L s e) t

/-- **The transport of a local annihilation statement into the graded module of twisted
sections.** On a quasi-compact scheme, if near every point some power of a local equation for `s`
annihilates the restriction of a twisted global section `t` of `H ⊗ L^{⊗ j}`, then a single power
of `s` annihilates the homogeneous element `t` of `⨁_j Γ(X, H ⊗ L^{⊗ j})`. -/
theorem exists_pow_smul_of_eq_zero_of_locally [CompactSpace X] (s : L.sections) (j : ℤ)
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L j)))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (hlocal : ∀ x : X, ∃ (e : ℕ) (U : Opens X.toRingedSpace)
        (r : (sectionSiteRing X).obj (op U)) (l : L.val.obj (op U)), x ∈ U ∧
      s.eval (op U) = r • l ∧
      r ^ e • ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
          Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
          ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
          (sectionSiteSheaf X) L j)))).val.map
          (terminal.from U).op t = 0) :
    ∃ e : ℕ, homogeneousSection X L s ^ e •
      (DirectSum.of _ j t : sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H) = 0 := by
  obtain ⟨e, he⟩ := exists_sectionModuleAction_eq_zero_of_locally X L H s j t (by
    intro x
    obtain ⟨e, U, r, l, hxU, hsU, hr⟩ := hlocal x
    obtain ⟨q, hq⟩ := sectionPower_restrict_dvd_smul X L s U r l hsU e
    exact ⟨e, U, hxU, sectionModuleAction_restrict_eq_zero_of_smul X L H e j
      (sectionPower X L s e) t U (r ^ e) q hq hr⟩)
  refine ⟨e, (pow_smul_of X L H s e j t).trans ?_⟩
  rw [he]
  exact map_zero _

/-- A fraction with denominator a power of `r` is zero in the localized module exactly when some
power of `r` annihilates its numerator. -/
private alias mk_eq_zero_iff_exists_pow_smul :=
  Stacks.SheafOfModules.localizedModule_mk_eq_zero_iff

/-! ### The local annihilator on a trivializing affine open -/

attribute [local instance] moduleOfSections

/-- **A uniform annihilator for a twisted section of a quasi-coherent module, locally.** Over an
affine open `U` contained in an open trivializing `P`, a section of `A ⊗ P` restricting to zero on
`X.basicOpen r` is annihilated by one power of `r`. -/
private lemma exists_pow_smul_tensorSection_eq_zero
    {Y : Scheme.{u}} {A P : Y.Modules} [A.IsQuasicoherent]
    {U V : Y.Opens} (hU : IsAffineOpen U) (hUV : U ≤ V)
    (e : P.over V ≅ _root_.SheafOfModules.unit
      ((structureSheafRing Y.toRingedSpace).over V)) (r : Γ(Y, U))
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing Y),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing Y)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf Y))⟩).obj (A)).obj (P))).val.obj
      (op U))
    (ht : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing Y),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing Y)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf Y))⟩).obj (A)).obj (P))).val.map
        (homOfLE (Y.basicOpen_le r)).op t = 0) :
    ∃ N : ℕ, r ^ N • t = 0 := by
  let E := tensorOverUnitIso A P V e
  let B := op (Over.mk (homOfLE hUV))
  let a : A.val.obj (op U) := E.hom.val.app B t
  have ha : A.val.map (homOfLE (Y.basicOpen_le r)).op a = 0 := by
    have hn := PresheafOfModules.naturality_apply E.hom.val
      (op (Over.homMk (homOfLE (Y.basicOpen_le r)) :
        Over.mk (homOfLE ((Y.basicOpen_le r).trans hUV)) ⟶ Over.mk (homOfLE hUV))) t
    refine hn.symm.trans ?_
    refine Eq.trans (congrArg
      ((E.hom.val.app (op (Over.mk (homOfLE ((Y.basicOpen_le r).trans hUV))))).hom) ht) ?_
    exact map_zero _
  obtain ⟨N, hN⟩ := Stacks.ModuleSectionExtension.exists_pow_smul_eq_zero A hU r a ha
  have hiso : IsIso (E.hom.val.app B) :=
    ((PresheafOfModules.evaluation _ B).mapIso
      ((_root_.SheafOfModules.forget _).mapIso E)).isIso_hom
  have h1 := (LinearMap.map_smul ((E.hom.val.app B)).hom (r ^ N) t).trans hN
  exact ⟨N, (ConcreteCategory.bijective_of_isIso (E.hom.val.app B)).injective
    (h1.trans (map_zero _).symm)⟩

/-- **Functoriality of the restriction maps.** A global section of a sheaf of modules which
restricts to zero on an open `V` restricts to zero on `X.basicOpen r`, for a local equation `r`
on an open `W` whose basic open is contained in `V`; the restriction is read as the restriction
along `X.basicOpen r ≤ W` of the restriction to `W`, which is the shape the local annihilator
consumes.

Stated for a sheaf of modules over an arbitrary sheaf of rings on the space, so that the module
it is applied to -- a tensor product of a quasi-coherent module with a twist, whose spelling runs
to three lines -- occurs once rather than three times at the point of use, and so that the two
spellings of the structure sheaf are never identified inside the twisted statement at all.
That matters: heartbeats are counted cumulatively over a declaration, and the local annihilator
of a twisted section exceeds the budget only in total. -/
private theorem map_basicOpen_map_terminal_eq_zero
    {R : Sheaf (Opens.grothendieckTopology X.toRingedSpace.carrier) RingCat.{u}}
    (T : SheafOfModules.{u} R)
    {W : X.Opens} (r : (sectionSiteRing X).obj (op W))
    {V : Opens X.toRingedSpace.toPresheafedSpace} (hr : X.basicOpen r ≤ V)
    (t : T.val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (hv : T.val.map (terminal.from V).op t = 0) :
    T.val.map (homOfLE (X.basicOpen_le r)).op (T.val.map (terminal.from W).op t) = 0 := by
  rw [← PresheafOfModules.map_comp_apply]
  have hcomp : (terminal.from W).op ≫ (homOfLE (X.basicOpen_le r)).op =
      (terminal.from V).op ≫ (homOfLE hr).op := Subsingleton.elim _ _
  rw [hcomp, PresheafOfModules.map_comp_apply, hv, map_zero]

/-- **The affine chart on which a local statement about a twisted section is proved.** Around
every point there is an affine open `W` inside a given neighbourhood `Z` of the point, contained
in an open `V` on which `L^{⊗ n}` is isomorphic to the structure sheaf, and carrying a local
equation for `s`: a frame of `L` over `W` writes `s|_W = r · l`, and `X.basicOpen r` lies inside
the open where `s` does not vanish.

Stated separately from the statements that use it for the reason recorded on
`Stacks.SheafOfModules.map_basicOpen_map_terminal_eq_zero`: heartbeats are counted cumulatively
over a declaration, and choosing this chart is what those statements have no budget left for. No
tensor product of a quasi-coherent module occurs here, only the twist itself. -/
private theorem exists_isAffineOpen_localEquation_and_trivialization (n : ℕ) (s : L.sections)
    {x : X} (Z : X.Opens) (hxZ : x ∈ Z) :
    ∃ (W V : X.Opens) (r : (sectionSiteRing X).obj (op W)) (l : L.val.obj (op W)),
      x ∈ W ∧ IsAffineOpen W ∧ W ≤ Z ∧ W ≤ V ∧ s.eval (op W) = r • l ∧
        X.basicOpen r ≤ nonvanishingOpen L s ∧
        Nonempty ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X)
            L (n : ℤ)).over V ≅
          _root_.SheafOfModules.unit ((structureSheafRing X.toRingedSpace).over V)) := by
  obtain ⟨W₀, hxW₀, b₀, hb₀⟩ := exists_bijective_smul_of_isInvertible L x
  have hPinv : IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)) :=
    TensorPower.isInvertible_tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)
  obtain ⟨V, hxV, ⟨eP⟩⟩ := exists_mem_over_iso_unit
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)) x
  obtain ⟨W, hWaff, hxW, hWsub⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ W₀ ⊓ V ⊓ Z from ⟨⟨hxW₀, hxV⟩, hxZ⟩)
  have hWW₀ : W ≤ W₀ := fun z hz => (hWsub hz).1.1
  have hWV : W ≤ V := fun z hz => (hWsub hz).1.2
  have hWZ : W ≤ Z := fun z hz => (hWsub hz).2
  obtain ⟨r, l, hs, hr⟩ := exists_scalar_section_of_generator L s
    (generatorRestrict L hWW₀ ⟨b₀, hb₀⟩)
  exact ⟨W, V, r, l, hxW, hWaff, hWZ, hWV, hs, hr, ⟨eP⟩⟩

variable (F : X.Modules)

/-- **The local annihilator of a twisted global section.** Let `F` be a quasi-coherent
`𝒪_X`-module and let `s` be a global section of an invertible module `L`. A global section `t` of
`F ⊗ L^{⊗ n}` which vanishes on `X_s` is annihilated near every point by a power of a local
equation for `s`. -/
theorem exists_pow_smul_twistedSection_restrict_eq_zero [F.IsQuasicoherent] (s : L.sections)
    (n : ℕ)
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (n : ℤ))))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (hv : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (n : ℤ))))).val.map
        (terminal.from (nonvanishingOpen L s)).op t = 0)
    (x : X) :
    ∃ (e : ℕ) (U : Opens X.toRingedSpace) (r : (sectionSiteRing X).obj (op U))
        (l : L.val.obj (op U)), x ∈ U ∧ s.eval (op U) = r • l ∧
      r ^ e • ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
          Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
          ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
          (sectionSiteSheaf X) L (n : ℤ))))).val.map
          (terminal.from U).op t = 0 := by
  obtain ⟨W, V', r, l, hxW, hWaff, -, hWV', hs, hr, ⟨eP⟩⟩ :=
    exists_isAffineOpen_localEquation_and_trivialization X L n s ⊤ (by trivial)
  have htr := map_basicOpen_map_terminal_eq_zero X _ r hr t hv
  obtain ⟨e, he⟩ := exists_pow_smul_tensorSection_eq_zero (A := F)
    (P := TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))
    hWaff hWV' eP r _ htr
  exact ⟨e, W, r, l, hxW, hs, he⟩


end TwistedSectionAnnihilator

section GradedSectionLocalization

attribute [-instance] CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape

attribute [local implicit_reducible] ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' TensorSheafification.structureSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv
  Stacks.SchemeModulesSpelling.sectionRingGradedRing
  Stacks.SchemeModulesSpelling.sectionRingGradingGradedRing
  Stacks.SchemeModulesSpelling.sectionModuleModule

variable (H : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- The decomposition of the section module into its homogeneous pieces, which instance search
does not find through the two spellings of the structure sheaf. -/
local instance sectionModuleDecompositionLoc : DirectSum.Decomposition
    (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L H) :=
  sectionModuleDecomposition (sectionSiteRing X) (sectionSiteSheaf X) L H

/-- The graded compatibility of the section-ring action, out of reach of instance search for the
same reason. -/
local instance sectionModuleGradedSMulLoc : SetLike.GradedSMul
    (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
    (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L H) :=
  sectionModuleGradedSMul (sectionSiteRing X) (sectionSiteSheaf X) L H

/- The degree-zero homogeneous localization of the section ring acts on the localization of the
graded section module through its embedding into the full localization. Mathlib keeps this
`Module.compHom` action out of instance search, and `sectionAtNonvanishingOpen` is a submodule
over it, so it has to be in scope for that submodule's additive structure to be found at all; it
is the very instance under which Tag 0B5L was stated. -/
local instance sectionAwayModuleLoc (s : L.sections) :
    Module (HomogeneousLocalization.Away
        (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
        (homogeneousSection X L s))
      (LocalizedModule.Away (R := sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
        (homogeneousSection X L s)
        (sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H)) :=
  Module.compHom (R := Localization.Away (homogeneousSection X L s))
    (LocalizedModule.Away (R := sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
      (homogeneousSection X L s)
      (sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H))
    (algebraMap (HomogeneousLocalization.Away
      (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
      (homogeneousSection X L s))
      (Localization.Away (homogeneousSection X L s)))

/-- **Every degree-zero fraction of twisted sections has a homogeneous numerator.** An element of
the degree-zero localization of `⨁_j Γ(X, H ⊗ L^{⊗ j})` at `s` is a homogeneous element of some
degree `n` divided by `sⁿ`. -/
theorem exists_twistedSection_numerator (s : L.sections)
    (z : sectionAtNonvanishingOpen X L H s) :
    ∃ (n : ℕ) (x : sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H),
      x ∈ sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L H (n : ℤ) ∧
      (z : LocalizedModule.Away
          (R := sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
          (homogeneousSection X L s)
          (sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H)) =
        LocalizedModule.mk (S := Submonoid.powers (homogeneousSection X L s)) x
          ⟨homogeneousSection X L s ^ n, ⟨n, rfl⟩⟩ :=
  degreeZeroLocalization_exists_fraction _ _ (homogeneousSection_mem X L s) z

/-- **The vanishing criterion on the nonvanishing open.** If a degree-zero fraction whose
numerator is the twisted global section `m` of degree `n` and whose denominator is `sⁿ` is sent to
the zero section on `X_s`, then `m` already restricts to zero on `X_s`. -/
theorem restrict_eq_zero_of_sectionLocalizationMap_eq_zero (s : L.sections) (n : ℕ)
    (m : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (n : ℤ))))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (z : sectionAtNonvanishingOpen X L H s)
    (hz : (z : LocalizedModule.Away
        (R := sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
        (homogeneousSection X L s)
        (sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H)) =
      LocalizedModule.mk (S := Submonoid.powers (homogeneousSection X L s))
        (DirectSum.of _ (n : ℤ) m) ⟨homogeneousSection X L s ^ n, ⟨n, rfl⟩⟩)
    (h0 : sectionLocalizationMap X L H s z = 0) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (n : ℤ))))).val.map
        (terminal.from (nonvanishingOpen L s)).op m = 0 := by
  obtain ⟨be, hbe⟩ := exists_tensorBasisAt X L H s n
  have hdiv : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (n : ℤ))))).val.map
          (terminal.from (nonvanishingOpen L s)).op m =
      tensorSectionAtOpen X L H (nonvanishingOpen L s) n
        (be.symm (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
            Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
            ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
            (sectionSiteSheaf X) L (n : ℤ))))).val.map
            (terminal.from (nonvanishingOpen L s)).op m))
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.map
          (terminal.from (nonvanishingOpen L s)).op (sectionPower X L s n)) :=
    (be.apply_symm_apply _).symm.trans (hbe _)
  have hval := sectionLocalizationMap_fraction X L H s n m z _ hz hdiv
  have ht0 := hval.symm.trans h0
  exact (be.apply_symm_apply _).symm.trans ((congrArg be ht0).trans be.map_zero)

/-- **Injectivity of the Tag 0B5L comparison map, granted the local annihilation step.** On a
quasi-compact scheme the map `(⨁_n Γ(X, H ⊗ L^{⊗ n}))_{(s)} ⟶ Γ(X_s, H|_{X_s})` is injective as
soon as a twisted global section vanishing on `X_s` is annihilated near every point by a power of
a local equation for `s`. -/
theorem sectionLocalizationMap_injective_of_locally [CompactSpace X] (s : L.sections)
    (hloc : ∀ (n : ℕ) (m : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (n : ℤ))))).val.obj
          (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))),
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
          Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
          ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
          (sectionSiteSheaf X) L (n : ℤ))))).val.map
          (terminal.from (nonvanishingOpen L s)).op m = 0 →
      ∀ x : X, ∃ (e : ℕ) (U : Opens X.toRingedSpace) (r : (sectionSiteRing X).obj (op U))
          (l : L.val.obj (op U)), x ∈ U ∧ s.eval (op U) = r • l ∧
        r ^ e • ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
            Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
            ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
            (sectionSiteSheaf X) L (n : ℤ))))).val.map
            (terminal.from U).op m = 0) :
    Function.Injective (sectionLocalizationMap X L H s) := by
  intro a b hab
  have hsub : sectionLocalizationMap X L H s (a - b) = 0 :=
    ((sectionLocalizationMap X L H s).map_sub a b).trans (sub_eq_zero.mpr hab)
  have hnum := exists_twistedSection_numerator X L H s (a - b)
  obtain ⟨n, xx, hmem, hrep⟩ := hnum
  obtain ⟨m, hm⟩ := hmem
  rw [← hm] at hrep
  have hv := restrict_eq_zero_of_sectionLocalizationMap_eq_zero X L H s n m (a - b) hrep hsub
  have hpow := exists_pow_smul_of_eq_zero_of_locally X L H s (n : ℤ) m (hloc n m hv)
  obtain ⟨e, he⟩ := hpow
  have hzero := hrep.trans ((mk_eq_zero_iff_exists_pow_smul _ _ _).mpr ⟨e, he⟩)
  exact sub_eq_zero.mp (ZeroMemClass.coe_eq_zero.mp hzero)

variable (F : X.Modules)

/-- **[Stacks, Tag 01PW] part (1).** Let `X` be a quasi-compact scheme, let `L` be an invertible
`𝒪_X`-module, let `s` be a global section of `L` and let `ℱ` be a quasi-coherent `𝒪_X`-module.
The comparison map of Tag 0B5L
`(⨁_n Γ(X, ℱ ⊗ L^{⊗ n}))_{(s)} ⟶ Γ(X_s, ℱ|_{X_s})` is injective. -/
@[stacks 01PW "part (1)", ega "I 9.3.1" "(i)"]
theorem sectionLocalizationMap_injective [CompactSpace X] [F.IsQuasicoherent] (s : L.sections) :
    Function.Injective (sectionLocalizationMap X L F s) :=
  sectionLocalizationMap_injective_of_locally X L F s
    (fun n m hv => exists_pow_smul_twistedSection_restrict_eq_zero X L F s n m hv)

/-! ### Part (2): bijectivity on a quasi-compact and quasi-separated scheme -/

/-- Composing two restriction maps of a sheaf of modules is restriction along the composite.

Stated for a sheaf of modules over an arbitrary sheaf of rings on the space for the reason
recorded on `Stacks.SheafOfModules.map_basicOpen_map_terminal_eq_zero`: the modules this and the
three statements after it are used at are tensor products, whose coefficient ring sheaf is the
second of the two spellings of the structure sheaf, and identifying the spellings at each of the
many points of use is what exhausts the heartbeat budget of the twisted statements below. -/
private theorem module_map_comp
    {R : Sheaf (Opens.grothendieckTopology X.toRingedSpace.carrier) RingCat.{u}}
    (M : SheafOfModules.{u} R)
    {U V W : Opens X.toRingedSpace} (f : U ⟶ V) (g : V ⟶ W) (m : M.val.obj (op W)) :
    M.val.presheaf.map f.op (M.val.presheaf.map g.op m) =
      M.val.presheaf.map (g.op ≫ f.op) m :=
  (ConcreteCategory.comp_apply (M.val.presheaf.map g.op) (M.val.presheaf.map f.op) m).symm.trans
    (congrArg (fun k => k m) (M.val.presheaf.map_comp g.op f.op)).symm

/-- Restricting twice along inclusions of opens is restricting once. -/
private theorem res_comp
    {R : Sheaf (Opens.grothendieckTopology X.toRingedSpace.carrier) RingCat.{u}}
    (M : SheafOfModules.{u} R)
    {U₁ U₂ U₃ : Opens X.toRingedSpace} (h₁₂ : U₂ ≤ U₁) (h₂₃ : U₃ ≤ U₂)
    (m : M.val.obj (op U₁)) :
    M.val.map (homOfLE h₂₃).op (M.val.map (homOfLE h₁₂).op m) =
      M.val.map (homOfLE (h₂₃.trans h₁₂)).op m :=
  (module_map_comp X M (homOfLE h₂₃) (homOfLE h₁₂) m).trans
    (congrArg (fun φ => M.val.presheaf.map φ m) (Subsingleton.elim _ _))

/-- **Restriction is independent of the chain it is read along.** Restricting from `U₁` down to
`U₃` through an intermediate open `U₂` is restricting through any other intermediate open `V`:
both are the restriction along `U₃ ≤ U₁`.

This is the step at which a twisted section over a chart and the same section read over the part
of the nonvanishing open inside the ambient open are identified, and it is the costliest
unification of the chart statements below; carrying it out here, at a variable sheaf of modules
where no tensor product occurs, is what keeps those statements inside the heartbeat budget. -/
private theorem res_eq_res
    {R : Sheaf (Opens.grothendieckTopology X.toRingedSpace.carrier) RingCat.{u}}
    (M : SheafOfModules.{u} R)
    {U₁ U₂ U₃ V : Opens X.toRingedSpace} (h₁₂ : U₂ ≤ U₁) (h₂₃ : U₃ ≤ U₂)
    (k₁ : V ≤ U₁) (k₂ : U₃ ≤ V) (m : M.val.obj (op U₁)) :
    M.val.map (homOfLE h₂₃).op (M.val.map (homOfLE h₁₂).op m) =
      M.val.map (homOfLE k₂).op (M.val.map (homOfLE k₁).op m) :=
  (res_comp X M h₁₂ h₂₃ m).trans (res_comp X M k₁ k₂ m).symm

/-- **A difference of sections agreeing on an open dies on any open inside it.** If `a` and `b`
agree on `V ≤ U₁` and `r` is a section over `U₂ ≤ U₁` whose basic open lies in `V`, then the
difference of the restrictions of `a` and `b` to `U₂` vanishes on `X.basicOpen r`, which is the
shape the affine annihilator consumes. -/
private theorem map_basicOpen_map_sub_eq_zero
    {R : Sheaf (Opens.grothendieckTopology X.toRingedSpace.carrier) RingCat.{u}}
    (M : SheafOfModules.{u} R)
    {U₁ U₂ V : Opens X.toRingedSpace} (h₂ : U₂ ≤ U₁) (k : V ≤ U₁)
    (r : (sectionSiteRing X).obj (op U₂)) (hbk : X.basicOpen r ≤ V)
    (a b : M.val.obj (op U₁))
    (hab : M.val.map (homOfLE k).op a = M.val.map (homOfLE k).op b) :
    M.val.map (homOfLE (X.basicOpen_le r)).op
        (M.val.map (homOfLE h₂).op a - M.val.map (homOfLE h₂).op b) = 0 := by
  rw [map_sub, res_eq_res X M h₂ (X.basicOpen_le r) k hbk a,
    res_eq_res X M h₂ (X.basicOpen_le r) k hbk b, hab, sub_self]

/-- Restricting a global section to an open and then further is one restriction. -/
private theorem res_terminal_comp
    {R : Sheaf (Opens.grothendieckTopology X.toRingedSpace.carrier) RingCat.{u}}
    (M : SheafOfModules.{u} R)
    {U₁ U₂ : Opens X.toRingedSpace} (h : U₂ ≤ U₁)
    (m : M.val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    M.val.map (homOfLE h).op (M.val.map (terminal.from U₁).op m) =
      M.val.map (terminal.from U₂).op m :=
  (module_map_comp X M (homOfLE h) (terminal.from U₁) m).trans
    (congrArg (fun φ => M.val.presheaf.map φ m) (Subsingleton.elim _ _))

/-- The section of `H ⊗ L^{⊗ n}` cut out by a section of `H` and a section of the tensor power
is natural in the open. -/
private theorem tensorSectionAtOpen_res (n : ℕ)
    {U V : Opens X.toRingedSpace} (hVU : V ≤ U) (t : H.val.obj (op U))
    (q : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ)).val.obj (op U)) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (n : ℤ))))).val.map
        (homOfLE hVU).op (tensorSectionAtOpen X L H U n t q) =
      tensorSectionAtOpen X L H V n (H.val.map (homOfLE hVU).op t)
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.map
          (homOfLE hVU).op q) :=
  tensorSectionsAt_restrict X H
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))
    (homOfLE hVU).op t q

/-- **A divided power of `s` on a chart moves across the tensor.** If the restriction of `sᴺ` to
an open is `rᴺ` times a section `q` of the `N`-th tensor power there, then tensoring with that
restriction is tensoring `rᴺ · (-)` with `q`.

Stated for a variable sheaf of modules so that the module it is used at -- again a tensor product
whose spelling runs to two lines -- occurs once rather than four times inside the chart statement
below, whose heartbeat budget is exhausted in total rather than at any single step. -/
private theorem tensorSectionAtOpen_map_terminal_sectionPower
    (A : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (s : L.sections)
    {U : Opens X.toRingedSpace} (N : ℕ) (r : (sectionSiteRing X).obj (op U))
    (q : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (N : ℤ)).val.obj (op U))
    (hq : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ)).val.map
      (terminal.from U).op (sectionPower X L s N) = r ^ N • q)
    (c : A.val.obj (op U)) :
    tensorSectionAtOpen X L A U N c
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ)).val.map
          (terminal.from U).op (sectionPower X L s N)) =
      tensorSectionAtOpen X L A U N (r ^ N • c) q := by
  rw [hq]
  exact (tensorSectionsAt_smul_comm X A
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ))
    (op U) (r ^ N) c q).symm

/-- **A compatible family of local sections of a sheaf of modules glues.** On a cover of the whole
space by opens, sections agreeing on the overlaps are the restrictions of one global section. -/
private theorem exists_global_section_of_compatible_cover
    {R : Sheaf (Opens.grothendieckTopology X.toRingedSpace.carrier) RingCat.{u}}
    (M : SheafOfModules.{u} R)
    {ι : Type u} (V : ι → Opens X.toRingedSpace)
    (hcover : ∀ x : X, ∃ i, x ∈ V i)
    (a : ∀ i, M.val.obj (op (V i)))
    (ha : TopCat.Presheaf.IsCompatible M.val.presheaf V a) :
    ∃ b : M.val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))),
      ∀ i, M.val.map (terminal.from (V i)).op b = a i := by
  have hsup : iSup V = (⊤ : Opens X.toRingedSpace.toPresheafedSpace) := by
    refine le_antisymm le_top (fun x _ => ?_)
    obtain ⟨i, hi⟩ := hcover x
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  have hterm : (⊤ : Opens X.toRingedSpace.toPresheafedSpace) =
      ⊤_ (Opens X.toRingedSpace.toPresheafedSpace) :=
    le_antisymm (leOfHom (terminal.from (⊤ : Opens X.toRingedSpace.toPresheafedSpace))) le_top
  have htop : iSup V = ⊤_ (Opens X.toRingedSpace.toPresheafedSpace) := hsup.trans hterm
  obtain ⟨b, hb, _⟩ := TopCat.Presheaf.IsSheaf.isSheafUniqueGluing M.isSheaf V a ha
  have hb' : ∀ i, M.val.presheaf.map (Opens.leSupr V i).op b = a i := hb
  refine ⟨M.val.presheaf.map (eqToHom htop.symm).op b, fun i => ?_⟩
  have hcomp : (eqToHom htop.symm).op ≫ (terminal.from (V i)).op = (Opens.leSupr V i).op :=
    Subsingleton.elim _ _
  change M.val.presheaf.map (terminal.from (V i)).op
      (M.val.presheaf.map (eqToHom htop.symm).op b) = a i
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, hcomp]
  exact hb' i

/-- Two sections of a sheaf of modules over an open agreeing on a cover of it are equal. -/
private theorem sections_eq_of_open_cover
    {R : Sheaf (Opens.grothendieckTopology X.toRingedSpace.carrier) RingCat.{u}}
    (M : SheafOfModules.{u} R)
    (W : Opens X.toRingedSpace) {ι : Type*} (V : ι → Opens X.toRingedSpace)
    (hV : ∀ i, V i ≤ W) (hcover : ∀ x : X, x ∈ W → ∃ i, x ∈ V i)
    (a b : M.val.obj (op W))
    (h : ∀ i, M.val.map (homOfLE (hV i)).op a = M.val.map (homOfLE (hV i)).op b) : a = b := by
  apply TopCat.Presheaf.IsSheaf.section_ext (U := op W) M.isSheaf
  intro x hx
  obtain ⟨i, hxi⟩ := hcover x hx
  exact ⟨V i, hV i, hxi, h i⟩

/-- The coherence isomorphism `(H ⊗ L^{⊗ n}) ⊗ L^{⊗ m} ≅ H ⊗ L^{⊗ (n + m)}`: the associativity
constraint followed by the multiplication of tensor powers. -/
noncomputable def twistedPowerAddIso (n m : ℕ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing
        X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (n : ℤ))))))).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (m : ℤ)))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
          Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
          ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
          (sectionSiteSheaf X) L
          ((n + m : ℕ) : ℤ)))) :=
  Invertible.tensorProductAssociator (sectionSiteRing X) (sectionSiteSheaf X) H
      (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))
      (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ)) ≪≫
    Invertible.tensorProductIso (sectionSiteRing X) (sectionSiteSheaf X) (Iso.refl H)
      (TensorPower.coherentMulIso (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ) (m : ℤ) ≪≫
        TensorPower.tensorPowerReindex (sectionSiteRing X) (sectionSiteSheaf X) L
          (Int.natCast_add n m).symm)

/-- **Multiplication of a twisted section by a power of `s`.** A section of `H ⊗ L^{⊗ n}` over an
open is tensored with the restriction of `s ^ m` and the product read in `H ⊗ L^{⊗ (n + m)}`. -/
noncomputable def twistSectionByPower (s : L.sections) (n m : ℕ)
    (U : Opens X.toRingedSpace)
    (a : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
        (n : ℤ))))).val.obj (op U)) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
        ((n + m : ℕ) : ℤ))))).val.obj (op U) :=
  (twistedPowerAddIso X L H n m).hom.val.app (op U)
    (tensorSectionAtOpen X L
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
          Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
          ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
          (sectionSiteSheaf X) L (n : ℤ))))) U m a
      ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ)).val.map
        (terminal.from U).op (sectionPower X L s m)))

/-- The section of `H ⊗ L^{⊗ n}` cut out by a pair of sections, read through the spelling
`Stacks.SheafOfModules.tensorSectionsAt` that the coherence lemmas are stated at. -/
private theorem tensorSectionAtOpen_eq_tensorSectionsAt
    (A : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (U : Opens X.toRingedSpace) (m : ℕ) (t : A.val.obj (op U))
    (q : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (m : ℤ)).val.obj (op U)) :
    tensorSectionAtOpen X L A U m t q =
      tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) (op U) A
        (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ)) t q :=
  rfl

/-- Multiplying by a power of `s` commutes with restriction to a smaller open. -/
private theorem twistSectionByPower_res (s : L.sections) (n m : ℕ)
    {U V : Opens X.toRingedSpace} (hVU : V ≤ U)
    (a : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
        (n : ℤ))))).val.obj (op U)) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
        ((n + m : ℕ) : ℤ))))).val.map (homOfLE hVU).op
        (twistSectionByPower X L H s n m U a) =
      twistSectionByPower X L H s n m V
        (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
            Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
            ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
            (sectionSiteSheaf X) L
            (n : ℤ))))).val.map (homOfLE hVU).op a) := by
  have hq := res_terminal_comp X
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ)) hVU
    (sectionPower X L s m)
  have hres := tensorSectionAtOpen_res X L
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (n : ℤ))))) m hVU a
    ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ)).val.map
      (terminal.from U).op (sectionPower X L s m))
  unfold twistSectionByPower
  refine Eq.trans (PresheafOfModules.naturality_apply
    (twistedPowerAddIso X L H n m).hom.val (homOfLE hVU).op
    (tensorSectionAtOpen X L
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
          Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
          ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
          (sectionSiteSheaf X) L (n : ℤ))))) U m a
      ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ)).val.map
        (terminal.from U).op (sectionPower X L s m)))).symm ?_
  rw [hres, hq]

/-- **Multiplication by a power of `s` on a pure tensor.** Multiplying `t ⊗ q` by `s ^ m`
multiplies the tensor-power factor: the associator and the coherent multiplication of tensor
powers move `s ^ m` past the twist. -/
private theorem twistSectionByPower_tensorSectionAtOpen (s : L.sections) (n m : ℕ)
    (U : Opens X.toRingedSpace) (t : H.val.obj (op U))
    (q : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ)).val.obj (op U)) :
    twistSectionByPower X L H s n m U (tensorSectionAtOpen X L H U n t q) =
      tensorSectionAtOpen X L H U (n + m) t
        (((sectionRingMulIso X L n m).hom.val.app (op U)).hom
          (tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) (op U)
            (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))
            (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ)) q
            ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
              (m : ℤ)).val.map (terminal.from U).op (sectionPower X L s m)))) := by
  unfold twistSectionByPower twistedPowerAddIso
  simp only [tensorSectionAtOpen_eq_tensorSectionsAt, Iso.trans_hom, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [tensorSections_associatorAt, tensorSections_tensorProductIsoAt]
  rfl

/-- The power sections multiply: `sⁿ · sᵐ = s^{n+m}`. -/
private alias sectionRingMul_sectionPower := sectionPower_add

/-- The defining property of a twisted section over an open — that it restricts on the part of
the nonvanishing open inside it to `t ⊗ sᴺ` — is inherited by any smaller open. -/
private theorem res_tensorSectionAtOpen_inf (s : L.sections) (N : ℕ)
    {V W : Opens X.toRingedSpace} (hWV : W ≤ V)
    (t : H.val.obj (op (nonvanishingOpen L s)))
    (a : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
        (N : ℤ))))).val.obj (op V))
    (ha : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (N : ℤ))))).val.map
        (homOfLE (inf_le_left : V ⊓ nonvanishingOpen L s ≤ V)).op a =
      tensorSectionAtOpen X L H (V ⊓ nonvanishingOpen L s) N
        (H.val.map (homOfLE (inf_le_right : V ⊓ nonvanishingOpen L s ≤
          nonvanishingOpen L s)).op t)
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ)).val.map
          (terminal.from (V ⊓ nonvanishingOpen L s)).op (sectionPower X L s N))) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (N : ℤ))))).val.map
        (homOfLE (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W)).op
        (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
            Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
            ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
            (sectionSiteSheaf X) L
            (N : ℤ))))).val.map (homOfLE hWV).op a) =
      tensorSectionAtOpen X L H (W ⊓ nonvanishingOpen L s) N
        (H.val.map (homOfLE (inf_le_right : W ⊓ nonvanishingOpen L s ≤
          nonvanishingOpen L s)).op t)
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ)).val.map
          (terminal.from (W ⊓ nonvanishingOpen L s)).op (sectionPower X L s N)) := by
  have hle : W ⊓ nonvanishingOpen L s ≤ V ⊓ nonvanishingOpen L s := inf_le_inf_right _ hWV
  have g1 := res_comp X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L
      (N : ℤ))))) hWV (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W) a
  have g2 := res_comp X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L
      (N : ℤ))))) (inf_le_left : V ⊓ nonvanishingOpen L s ≤ V) hle a
  have g3 := congrArg (fun c => ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L
      (N : ℤ))))).val.map (homOfLE hle).op c) ha
  have g4 := tensorSectionAtOpen_res X L H N hle
    (H.val.map (homOfLE (inf_le_right : V ⊓ nonvanishingOpen L s ≤
      nonvanishingOpen L s)).op t)
    ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ)).val.map
      (terminal.from (V ⊓ nonvanishingOpen L s)).op (sectionPower X L s N))
  have g5 := res_comp X H
    (inf_le_right : V ⊓ nonvanishingOpen L s ≤ nonvanishingOpen L s) hle t
  have g6 := res_terminal_comp X (TensorPower.tensorPower (sectionSiteRing X)
    (sectionSiteSheaf X) L (N : ℤ)) hle (sectionPower X L s N)
  refine ((g1.trans g2.symm).trans (g3.trans g4)).trans ?_
  rw [g5, g6]

/-- **The chart step of Tag 01PW's proof, as a property of `(X, L, s, H)`.** Near every point
there is a quasi-compact open `V` and an exponent `n₀` such that every section `t` of `H` over
`X_s` is, for each `N ≥ n₀`, the restriction to `V ⊓ X_s` of a twisted section of
`H ⊗ L^{⊗ N}` over `V` divided by `sᴺ`. This is Tag 01P7 read on a chart trivializing `L`.

No compatibility between the twisted sections at different `N` is asked for: the gluing in
`Stacks.SheafOfModules.exists_fraction_of_section_of_locally` multiplies the chart sections at
the single exponent `n₀` by the uniform power that makes them agree on the overlaps, so the
family is only ever used one degree at a time. -/
def HasTwistedChartExtension (s : L.sections) : Prop :=
  ∀ (t : H.val.obj (op (nonvanishingOpen L s))) (x : X),
    ∃ (V : Opens X.toRingedSpace) (n₀ : ℕ)
      (a : (N : ℕ) → ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
          Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
          ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
          (sectionSiteSheaf X) L (N : ℤ))))).val.obj (op V)),
      x ∈ V ∧ IsCompact (V : Set X) ∧
      ∀ N : ℕ, n₀ ≤ N →
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
            Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
            ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
            (sectionSiteSheaf X)
            L (N : ℤ))))).val.map
          (homOfLE (inf_le_left : V ⊓ nonvanishingOpen L s ≤ V)).op (a N) =
        tensorSectionAtOpen X L H (V ⊓ nonvanishingOpen L s) N
          (H.val.map (homOfLE (inf_le_right : V ⊓ nonvanishingOpen L s ≤
            nonvanishingOpen L s)).op t)
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X)
            L (N : ℤ)).val.map
            (terminal.from (V ⊓ nonvanishingOpen L s)).op (sectionPower X L s N))

/-- **Part (1) of Tag 01PW over a quasi-compact open, as a property of `(X, L, s, H)`.** Two
twisted sections of `H ⊗ L^{⊗ n}` over a quasi-compact open which agree on its intersection with
`X_s` agree after multiplication by every high enough power of `s`. -/
def HasTwistedCompactAnnihilation (s : L.sections) : Prop :=
  ∀ W : Opens X.toRingedSpace, IsCompact (W : Set X) → ∀ (n : ℕ)
    (a b : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X)
        L (n : ℤ))))).val.obj (op W)),
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X)
          L (n : ℤ))))).val.map
        (homOfLE (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W)).op a =
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
          Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
          ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
          (sectionSiteSheaf X)
          L (n : ℤ))))).val.map
        (homOfLE (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W)).op b →
    ∃ k : ℕ, ∀ N : ℕ, k ≤ N →
      twistSectionByPower X L H s n N W a = twistSectionByPower X L H s n N W b

section ChartAnnihilation

attribute [local instance] moduleOfSections

/-- If `r ^ e` carries `u` to `v` then every higher power of `r` carries `u` to a multiple of
`v`. Stated at a bare module for the same reason as the next lemma. -/
private theorem pow_smul_eq_pow_sub_smul {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (ρ : R) (u v : M) (e : ℕ) (h : ρ ^ e • u = v) (N : ℕ) (hN : e ≤ N) :
    ρ ^ N • u = ρ ^ (N - e) • v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [← h, Nat.add_sub_cancel_left, ← mul_smul, ← pow_add, Nat.add_comm k e]

/-- **A local equation for `s` in a frame cuts out the nonvanishing open.** If `g` trivializes
`L` over `U`, the restriction of `s` to `U` is `r • g` and the part of the nonvanishing open
inside `U` is exactly the basic open of `r`.

This sharpens `Stacks.SheafOfModules.exists_scalar_section_of_generator`, which gives only the
inclusion `X.basicOpen r ≤ X_s`; the converse inclusion is the other direction of the same germ
criterion `Stacks.SheafOfModules.mem_nonvanishingLocus_iff_isUnit_ringGerm`. -/
private lemma exists_scalar_section_inf_eq_basicOpen (s : L.sections)
    {U : Opens X.toRingedSpace} (g : GeneratorSections X.toRingedSpace L U) :
    ∃ r : (sectionSiteRing X).obj (op U),
      s.eval (op U) = r • g.val ∧ U ⊓ nonvanishingOpen L s = X.basicOpen r := by
  have hbij := g.property U le_rfl
  rw [generator_restrict_self L U g] at hbij
  obtain ⟨r, hr⟩ := hbij.surjective (s.eval (op U))
  refine ⟨r, hr.symm, le_antisymm (fun z hz => ?_) (fun z hz => ?_)⟩
  · exact (isUnit_ringGerm_iff_mem_basicOpen r z hz.1).mp
      ((mem_nonvanishingLocus_iff_isUnit_ringGerm L s g r hr.symm z hz.1).mp hz.2)
  · exact ⟨X.basicOpen_le r hz,
      (mem_nonvanishingLocus_iff_isUnit_ringGerm L s g r hr.symm z
        (X.basicOpen_le r hz)).mpr
        ((isUnit_ringGerm_iff_mem_basicOpen r z (X.basicOpen_le r hz)).mpr hz)⟩

/-- Two elements whose difference is annihilated by `r ^ e` have equal multiples by every higher
power of `r`. Stated at a bare module so that the exponent arithmetic is not performed against
the sheaf-theoretic types it is used at. -/
private theorem smul_pow_eq_of_pow_smul_sub_eq_zero {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (r : R) (u v : M) (e : ℕ) (h : r ^ e • (u - v) = 0) (N : ℕ) (hN : e ≤ N) :
    r ^ N • u = r ^ N • v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have h1 : r ^ e • u = r ^ e • v := sub_eq_zero.mp ((smul_sub (r ^ e) u v).symm.trans h)
  rw [show r ^ (e + k) = r ^ k * r ^ e by rw [← pow_add, Nat.add_comm], mul_smul, mul_smul, h1]

/-- **The chart step of the comparison over a quasi-compact open.** Let `ℱ` be quasi-coherent and
let `a`, `b` be twisted sections of `ℱ ⊗ L^{⊗ n}` over an open `W` agreeing on `W ⊓ X_s`. Near
every point of `W` there is an open `V ≤ W` and an exponent `e` such that for `N ≥ e` the
multiplied sections `s^N · a` and `s^N · b` already agree on `V`.

The chart is an affine open inside a trivializing open for `L` and one for `L^{⊗ n}`; there the
frame turns `s` into `r · g` and identifies `V ⊓ X_s` with a basic open of `r`, so Tag 01I9 in the
module-valued form `Stacks.ModuleSectionExtension.exists_pow_smul_eq_zero` kills the difference
after one power of `r`, and the matching power of `s` is divisible by it. -/
private theorem exists_pow_twistSectionByPower_restrict_eq [F.IsQuasicoherent] (s : L.sections)
    (n : ℕ) (W : Opens X.toRingedSpace)
    (a b : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X)
        L (n : ℤ))))).val.obj (op W))
    (hab : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X)
            L (n : ℤ))))).val.map
          (homOfLE (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W)).op a =
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
            Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
            ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
            (sectionSiteSheaf X)
            L (n : ℤ))))).val.map
          (homOfLE (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W)).op b)
    (x : X) (hx : x ∈ W) :
    ∃ (V : Opens X.toRingedSpace) (hVW : V ≤ W) (e : ℕ), x ∈ V ∧ ∀ N : ℕ, e ≤ N →
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
          Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
          ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
          (sectionSiteSheaf X)
            L ((n + N : ℕ) : ℤ))))).val.map (homOfLE hVW).op
          (twistSectionByPower X L F s n N W a) =
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
            Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
            ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
            (sectionSiteSheaf X)
            L ((n + N : ℕ) : ℤ))))).val.map (homOfLE hVW).op
          (twistSectionByPower X L F s n N W b) := by
  obtain ⟨A, V', r, l, hxA, hAaff, hAW, hAV', hs, hr, ⟨eP⟩⟩ :=
    exists_isAffineOpen_localEquation_and_trivialization X L n s W hx
  have hle : X.basicOpen r ≤ W ⊓ nonvanishingOpen L s :=
    le_inf ((X.basicOpen_le r).trans hAW) hr
  -- restricting to the chart and then to the basic open of `r` is restricting through `W ⊓ X_s`
  have hzero := map_basicOpen_map_sub_eq_zero X _ hAW
    (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W) r hle a b hab
  obtain ⟨e, he⟩ := exists_pow_smul_tensorSection_eq_zero (A := F)
    (P := TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))
    hAaff hAV' eP r _ hzero
  refine ⟨A, hAW, e, hxA, fun N hN => ?_⟩
  have hsmul := smul_pow_eq_of_pow_smul_sub_eq_zero r _ _ e he N hN
  obtain ⟨q, hq⟩ := sectionPower_restrict_dvd_smul X L s A r l hs N
  rw [twistSectionByPower_res X L F s n N hAW a, twistSectionByPower_res X L F s n N hAW b]
  unfold twistSectionByPower
  rw [tensorSectionAtOpen_map_terminal_sectionPower X L _ s N r q hq,
    tensorSectionAtOpen_map_terminal_sectionPower X L _ s N r q hq, hsmul]

/-- **Part (1) of Tag 01PW over a quasi-compact open.** Let `X` be a scheme, `L` an invertible
`𝒪_X`-module, `s` a global section of `L` and `ℱ` a quasi-coherent `𝒪_X`-module. Two twisted
sections of `ℱ ⊗ L^{⊗ n}` over a quasi-compact open which agree on its intersection with `X_s`
agree after multiplication by every high enough power of `s`: this is
`Stacks.SheafOfModules.HasTwistedCompactAnnihilation`, so that property is not a hypothesis of
part (2) but a theorem. No hypothesis on `X` is needed beyond quasi-compactness of the open
itself, which the finite subcover consumes. -/
theorem hasTwistedCompactAnnihilation [F.IsQuasicoherent] (s : L.sections) :
    HasTwistedCompactAnnihilation X L F s := by
  classical
  intro W hW n a b hab
  choose VV hVV ee hmemV hresV using fun (x : X) (hx : x ∈ W) =>
    exists_pow_twistSectionByPower_restrict_eq X L F s n W a b hab x hx
  obtain ⟨σ, hσ⟩ := hW.elim_finite_subcover
    (fun i : {y : X // y ∈ W} => (VV i.1 i.2 : Set X))
    (fun i => (VV i.1 i.2).isOpen)
    (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩, hmemV z hz⟩)
  obtain ⟨k, hk⟩ := Finite.exists_le fun i : {i : {y : X // y ∈ W} // i ∈ σ} => ee i.1.1 i.1.2
  refine ⟨k, fun N hN => ?_⟩
  refine sections_eq_of_open_cover X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing
      X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X)
      L ((n + N : ℕ) : ℤ))))) W
    (fun i : {i : {y : X // y ∈ W} // i ∈ σ} => VV i.1.1 i.1.2)
    (fun i => hVV i.1.1 i.1.2) (fun z hz => ?_) _ _ (fun i => ?_)
  · obtain ⟨i, hiσ, hzi⟩ : ∃ i ∈ σ, z ∈ VV i.1 i.2 := by simpa using hσ hz
    exact ⟨⟨i, hiσ⟩, hzi⟩
  · exact hresV i.1.1 i.1.2 N ((hk i).trans hN)

/-- **The chart step of Tag 01PW's proof.** Let `X` be a scheme, `L` an invertible `𝒪_X`-module,
`s` a global section of `L` and `ℱ` a quasi-coherent `𝒪_X`-module. Every point has an affine
neighbourhood `A` and an exponent `e` such that every section `t` of `ℱ` over `X_s` is, for each
`N ≥ e`, the restriction to `A ⊓ X_s` of a twisted section of `ℱ ⊗ L^{⊗ N}` over `A` divided by
`sᴺ`: this is `Stacks.SheafOfModules.HasTwistedChartExtension`, so that property is not a
hypothesis of part (2) but a theorem.

On a chart inside a trivializing open the frame turns `s|_A` into `r · g` and identifies
`A ⊓ X_s` with `X.basicOpen r`, so Tag 01P7 in the module-valued form
`Stacks.ModuleSectionExtension.exists_pow_smul_eq_res` extends `rᵉ · t` to a section `c` of `ℱ`
over `A`; tensoring `r^{N-e} · c` with the `N`-th divided power of `s` on the chart gives the
twisted section, and over `X.basicOpen r` the two sides agree because `sᴺ|_A = rᴺ · qᴺ`. -/
theorem hasTwistedChartExtension [F.IsQuasicoherent] (s : L.sections) :
    HasTwistedChartExtension X L F s := by
  classical
  intro t x
  obtain ⟨W₀, hxW₀, g₀, hg₀⟩ := exists_bijective_smul_of_isInvertible L x
  obtain ⟨A, hAaff, hxA, hAW₀⟩ := exists_isAffineOpen_mem_and_subset hxW₀
  obtain ⟨r, hs, hAr⟩ := exists_scalar_section_inf_eq_basicOpen X L s
    (generatorRestrict L hAW₀ (⟨g₀, hg₀⟩ : GeneratorSections X.toRingedSpace L W₀))
  have hr1 : A ⊓ nonvanishingOpen L s ≤ X.basicOpen r := le_of_eq hAr
  have hbO : X.basicOpen r ≤ nonvanishingOpen L s := (le_of_eq hAr.symm).trans inf_le_right
  obtain ⟨e, c, hc⟩ := Stacks.ModuleSectionExtension.exists_pow_smul_eq_res F hAaff r
    (F.val.map (homOfLE hbO).op t)
  choose q hq using fun N : ℕ => sectionPower_restrict_dvd_smul X L s A r
    (generatorRestrict L hAW₀ (⟨g₀, hg₀⟩ : GeneratorSections X.toRingedSpace L W₀)).val hs N
  refine ⟨A, e, fun N => tensorSectionAtOpen X L F A N (r ^ (N - e) • c) (q N), hxA,
    hAaff.isCompact, fun N hN => ?_⟩
  -- the comparison over `X.basicOpen r`, where `t` has an extension and `sᴺ` is `rᴺ` times `qᴺ`
  have hbase : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X)
            L (N : ℤ))))).val.map (homOfLE (X.basicOpen_le r)).op
          (tensorSectionAtOpen X L F A N (r ^ (N - e) • c) (q N)) =
        tensorSectionAtOpen X L F (X.basicOpen r) N (F.val.map (homOfLE hbO).op t)
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ)).val.map
            (terminal.from (X.basicOpen r)).op (sectionPower X L s N)) := by
    -- the scalar identity `rᴺ = r^{N-e} · rᵉ` on the basic open
    have hring : Stacks.ModuleSectionExtension.resR (X.basicOpen_le r) (r ^ N) =
        Stacks.ModuleSectionExtension.resR (X.basicOpen_le r) (r ^ (N - e)) *
          Stacks.ModuleSectionExtension.resR (X.basicOpen_le r) r ^ e := by
      rw [Stacks.ModuleSectionExtension.resR, Stacks.ModuleSectionExtension.resR,
        Stacks.ModuleSectionExtension.resR, map_pow, map_pow, ← pow_add,
        Nat.sub_add_cancel hN]
    have hmod : Stacks.ModuleSectionExtension.resR (X.basicOpen_le r) (r ^ N) •
          Stacks.ModuleSectionExtension.res F hbO t =
        Stacks.ModuleSectionExtension.resR (X.basicOpen_le r) (r ^ (N - e)) •
          Stacks.ModuleSectionExtension.res F (X.basicOpen_le r) c := by
      rw [hring, mul_smul]
      exact congrArg
        (fun z => Stacks.ModuleSectionExtension.resR (X.basicOpen_le r) (r ^ (N - e)) • z) hc
    have e1 := PresheafOfModules.map_smul F.val (homOfLE (X.basicOpen_le r)).op
      (r ^ (N - e)) c
    have e2 := (res_terminal_comp X (TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (N : ℤ)) (X.basicOpen_le r) (sectionPower X L s N)).symm
    have e3 := congrArg (fun z => (TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (N : ℤ)).val.map (homOfLE (X.basicOpen_le r)).op z) (hq N)
    have e4 := PresheafOfModules.map_smul (TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (N : ℤ)).val (homOfLE (X.basicOpen_le r)).op (r ^ N) (q N)
    refine (tensorSectionAtOpen_res X L F N (X.basicOpen_le r) (r ^ (N - e) • c) (q N)).trans ?_
    refine (congrArg (fun y => tensorSectionAtOpen X L F (X.basicOpen r) N y
      ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ)).val.map
        (homOfLE (X.basicOpen_le r)).op (q N))) (e1.trans hmod.symm)).trans ?_
    refine (tensorSectionsAt_smul_comm X F (TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (N : ℤ)) (op (X.basicOpen r)) _ _ _).trans ?_
    exact congrArg (fun z => tensorSectionAtOpen X L F (X.basicOpen r) N
      (F.val.map (homOfLE hbO).op t) z) (e2.trans (e3.trans e4)).symm
  -- restriction to `A ⊓ X_s` factors through `X.basicOpen r`, which it equals
  have step1 : ∀ z : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X)
        L (N : ℤ))))).val.obj (op A),
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
          Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
          ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
          (sectionSiteSheaf X) L (N : ℤ))))).val.map
          (homOfLE (inf_le_left : A ⊓ nonvanishingOpen L s ≤ A)).op z =
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
            Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
            ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
            (sectionSiteSheaf X)
              L (N : ℤ))))).val.map (homOfLE hr1).op
            (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
                Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat
                RingCat) ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower
                (sectionSiteRing X) (sectionSiteSheaf X)
                L (N : ℤ))))).val.map (homOfLE (X.basicOpen_le r)).op z) := by
    exact fun z => (res_comp X _ (X.basicOpen_le r) hr1 z).symm
  have ht2 : F.val.map (homOfLE hr1).op (F.val.map (homOfLE hbO).op t) =
      F.val.map (homOfLE (inf_le_right : A ⊓ nonvanishingOpen L s ≤
        nonvanishingOpen L s)).op t :=
    res_comp X F hbO hr1 t
  have hs2 := res_terminal_comp X (TensorPower.tensorPower (sectionSiteRing X)
    (sectionSiteSheaf X) L (N : ℤ)) hr1 (sectionPower X L s N)
  refine ((step1 _).trans (congrArg (fun z =>
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (N : ℤ))))).val.map
      (homOfLE hr1).op z) hbase)).trans ?_
  exact (tensorSectionAtOpen_res X L F N hr1 (F.val.map (homOfLE hbO).op t)
      ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ)).val.map
        (terminal.from (X.basicOpen r)).op (sectionPower X L s N))).trans
    (congrArg₂ (fun y z => tensorSectionAtOpen X L F (A ⊓ nonvanishingOpen L s) N y z) ht2 hs2)

end ChartAnnihilation

/-- **A family of sections agreeing on the pairwise overlaps of a family of opens is a compatible
family.** This is `TopCat.Presheaf.IsCompatible` read through `homOfLE`, which is the spelling the
restriction lemmas of this file are stated at.

Stated for a sheaf of modules over an arbitrary sheaf of rings on the space, so that the module it
is used at -- a tensor product, whose spelling runs to two lines -- need not be written at all at
the point of use, for the reason recorded on
`Stacks.SheafOfModules.map_basicOpen_map_terminal_eq_zero`. -/
private theorem isCompatible_of_map_eq
    {R : Sheaf (Opens.grothendieckTopology X.toRingedSpace.carrier) RingCat.{u}}
    (M : SheafOfModules.{u} R) {ι : Type*} (V : ι → Opens X.toRingedSpace)
    (a : (i : ι) → M.val.obj (op (V i)))
    (h : ∀ i j : ι, M.val.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (a i) =
      M.val.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (a j)) :
    TopCat.Presheaf.IsCompatible M.val.presheaf V a := by
  intro i j
  exact h i j

/-- **The glued twisted section is the fraction of `t` by `s^{e+e'}` on each chart.** Let `a` be a
twisted section of `H ⊗ L^{⊗ e}` over an open `W` whose restriction to `W ⊓ X_s` is `t ⊗ sᵉ`, and
let `b` be a twisted global section of degree `e + e'` restricting on `W` to the product of `a`
with `s^{e'}`. Then on `W ⊓ X_s` the restriction of `b` already agrees with `t ⊗ s^{e+e'}`.

This is the whole per-chart computation of the gluing statement below -- the two readings of a
restriction of `b`, the defining property of `a`, the multiplication of a pure tensor by a power
of `s` and the multiplicativity of the power sections -- and it is carried out here because
heartbeats are counted cumulatively over a declaration and the gluing statement exceeds the budget
only in total. -/
private theorem map_inf_map_terminal_eq_tensorSectionAtOpen (s : L.sections) (e e' : ℕ)
    (t : H.val.obj (op (nonvanishingOpen L s))) (W : Opens X.toRingedSpace)
    (a : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
        (e : ℤ))))).val.obj (op W))
    (ha : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (e : ℤ))))).val.map
        (homOfLE (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W)).op a =
      tensorSectionAtOpen X L H (W ⊓ nonvanishingOpen L s) e
        (H.val.map (homOfLE (inf_le_right : W ⊓ nonvanishingOpen L s ≤
          nonvanishingOpen L s)).op t)
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (e : ℤ)).val.map
          (terminal.from (W ⊓ nonvanishingOpen L s)).op (sectionPower X L s e)))
    (b : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
        ((e + e' : ℕ) : ℤ))))).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (hb : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
        ((e + e' : ℕ) : ℤ))))).val.map (terminal.from W).op b =
      twistSectionByPower X L H s e e' W a) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
        ((e + e' : ℕ) : ℤ))))).val.map
        (homOfLE (inf_le_right : W ⊓ nonvanishingOpen L s ≤ nonvanishingOpen L s)).op
        (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
            Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
            ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
            (sectionSiteSheaf X) L
            ((e + e' : ℕ) : ℤ))))).val.map (terminal.from (nonvanishingOpen L s)).op b) =
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
          Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
          ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
          (sectionSiteSheaf X) L
          ((e + e' : ℕ) : ℤ))))).val.map
          (homOfLE (inf_le_right : W ⊓ nonvanishingOpen L s ≤ nonvanishingOpen L s)).op
          (tensorSectionAtOpen X L H (nonvanishingOpen L s) (e + e') t
            ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
              ((e + e' : ℕ) : ℤ)).val.map (terminal.from (nonvanishingOpen L s)).op
                (sectionPower X L s (e + e')))) := by
  have h1 := res_terminal_comp X _
    (inf_le_right : W ⊓ nonvanishingOpen L s ≤ nonvanishingOpen L s) b
  have h2 := res_terminal_comp X _
    (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W) b
  have hA := twistSectionByPower_res X L H s e e'
    (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W) a
  have hB := congrArg
    (fun c => twistSectionByPower X L H s e e' (W ⊓ nonvanishingOpen L s) c) ha
  have hC := twistSectionByPower_tensorSectionAtOpen X L H s e e'
    (W ⊓ nonvanishingOpen L s)
    (H.val.map (homOfLE (inf_le_right : W ⊓ nonvanishingOpen L s ≤
      nonvanishingOpen L s)).op t)
    ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (e : ℤ)).val.map
      (terminal.from (W ⊓ nonvanishingOpen L s)).op (sectionPower X L s e))
  have hD := congrArg
    (fun z => tensorSectionAtOpen X L H (W ⊓ nonvanishingOpen L s) (e + e')
      (H.val.map (homOfLE (inf_le_right : W ⊓ nonvanishingOpen L s ≤
        nonvanishingOpen L s)).op t) z)
    (sectionRingMulIso_sectionPower X L s (W ⊓ nonvanishingOpen L s) e e')
  have h4 := tensorSectionAtOpen_res X L H (e + e')
    (inf_le_right : W ⊓ nonvanishingOpen L s ≤ nonvanishingOpen L s) t
    ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      ((e + e' : ℕ) : ℤ)).val.map (terminal.from (nonvanishingOpen L s)).op
        (sectionPower X L s (e + e')))
  have h5 := res_terminal_comp X (TensorPower.tensorPower (sectionSiteRing X)
    (sectionSiteSheaf X) L ((e + e' : ℕ) : ℤ))
    (inf_le_right : W ⊓ nonvanishingOpen L s ≤ nonvanishingOpen L s)
    (sectionPower X L s (e + e'))
  refine ((h1.trans h2.symm).trans ((congrArg
    (fun c => ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
        ((e + e' : ℕ) : ℤ))))).val.map
      (homOfLE (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W)).op c)
        hb).trans (((hA.trans hB).trans hC).trans hD))).trans ?_
  rw [h4, h5]

/-- **Every section on the nonvanishing open is a fraction, granted the two local steps of the
source's proof.** On a quasi-compact, quasi-separated scheme a section `t` of `H` over `X_s`
becomes, after multiplication by a power of `s`, the restriction of a global twisted section. -/
private theorem exists_fraction_of_section_of_locally [CompactSpace X] [QuasiSeparatedSpace X]
    (s : L.sections) (hchart : HasTwistedChartExtension X L H s)
    (hann : HasTwistedCompactAnnihilation X L H s)
    (t : H.val.obj (op (nonvanishingOpen L s))) :
    ∃ (N : ℕ) (b : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
        (N : ℤ))))).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))),
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
          Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
          ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
          (sectionSiteSheaf X) L (N : ℤ))))).val.map
          (terminal.from (nonvanishingOpen L s)).op b =
        tensorSectionAtOpen X L H (nonvanishingOpen L s) N t
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ)).val.map
            (terminal.from (nonvanishingOpen L s)).op (sectionPower X L s N)) := by
  classical
  choose V n₀ aa hmemV hcptV hresV using hchart t
  obtain ⟨σ, hσ⟩ := (CompactSpace.isCompact_univ (X := X)).elim_finite_subcover
    (fun y : X => (V y : Set X)) (fun y => (V y).isOpen)
    (fun z _ => Set.mem_iUnion.2 ⟨z, hmemV z⟩)
  have hcover : ∀ x : X, ∃ y : {y : X // y ∈ σ}, x ∈ V y.1 := by
    intro x
    obtain ⟨y, hyσ, hxy⟩ : ∃ y ∈ σ, x ∈ V y := by simpa using hσ (Set.mem_univ x)
    exact ⟨⟨y, hyσ⟩, hxy⟩
  have hqc : ∀ y z : X, IsCompact ((V y ⊓ V z : Opens X.toRingedSpace) : Set X) := fun y z =>
    QuasiSeparatedSpace.inter_isCompact (V y : Set X) (V z : Set X)
      (V y).isOpen (hcptV y) (V z).isOpen (hcptV z)
  obtain ⟨e, he⟩ := Finite.exists_le fun y : {y : X // y ∈ σ} => n₀ y.1
  have hpair : ∀ y z : {y : X // y ∈ σ}, ∃ k : ℕ, ∀ N : ℕ, k ≤ N →
      twistSectionByPower X L H s e N (V y.1 ⊓ V z.1)
          (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
              Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
              ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
              (sectionSiteSheaf X)
              L (e : ℤ))))).val.map (homOfLE (inf_le_left : V y.1 ⊓ V z.1 ≤ V y.1)).op
                (aa y.1 e)) =
        twistSectionByPower X L H s e N (V y.1 ⊓ V z.1)
          (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
              Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
              ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
              (sectionSiteSheaf X)
              L (e : ℤ))))).val.map (homOfLE (inf_le_right : V y.1 ⊓ V z.1 ≤ V z.1)).op
                (aa z.1 e)) := by
    intro y z
    refine hann (V y.1 ⊓ V z.1) (hqc y.1 z.1) e _ _ ?_
    rw [res_tensorSectionAtOpen_inf X L H s e (inf_le_left : V y.1 ⊓ V z.1 ≤ V y.1) t
        (aa y.1 e) (hresV y.1 e (he y)),
      res_tensorSectionAtOpen_inf X L H s e (inf_le_right : V y.1 ⊓ V z.1 ≤ V z.1) t
        (aa z.1 e) (hresV z.1 e (he z))]
  choose kf hkf using hpair
  obtain ⟨e', he'⟩ := Finite.exists_le fun p : {y : X // y ∈ σ} × {y : X // y ∈ σ} => kf p.1 p.2
  have hcompat := isCompatible_of_map_eq X _ (fun y : {y : X // y ∈ σ} => V y.1)
    (fun y => twistSectionByPower X L H s e e' (V y.1) (aa y.1 e)) (fun y z => by
      rw [twistSectionByPower_res X L H s e e' (inf_le_left : V y.1 ⊓ V z.1 ≤ V y.1) (aa y.1 e),
        twistSectionByPower_res X L H s e e' (inf_le_right : V y.1 ⊓ V z.1 ≤ V z.1) (aa z.1 e)]
      exact hkf y z e' (he' (y, z)))
  obtain ⟨b, hb⟩ := exists_global_section_of_compatible_cover X _
    (fun y : {y : X // y ∈ σ} => V y.1) hcover _ hcompat
  refine ⟨e + e', b, ?_⟩
  refine sections_eq_of_open_cover X
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
        ((e + e' : ℕ) : ℤ)))))
    (nonvanishingOpen L s)
    (fun y : {y : X // y ∈ σ} => V y.1 ⊓ nonvanishingOpen L s)
    (fun _ => inf_le_right) (fun x hx => by
      obtain ⟨y, hy⟩ := hcover x
      exact ⟨y, hy, hx⟩) _ _ (fun y => ?_)
  exact map_inf_map_terminal_eq_tensorSectionAtOpen X L H s e e' t (V y.1) (aa y.1 e)
    (hresV y.1 e (he y)) b (hb y)

/-- **A twisted global section of degree `N` over `sᴺ` is a degree-zero fraction.** -/
private theorem mk_mem_sectionAtNonvanishingOpen (s : L.sections) (N : ℕ)
    (b : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
        (N : ℤ))))).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    LocalizedModule.mk (S := Submonoid.powers (homogeneousSection X L s))
        (DirectSum.of _ (N : ℤ) b) ⟨homogeneousSection X L s ^ N, ⟨N, rfl⟩⟩ ∈
      sectionAtNonvanishingOpen X L H s := by
  have hNsmul : N • ((1 : ℕ) : ℤ) = (N : ℤ) := by simp
  refine Submodule.subset_span ⟨1, N, homogeneousSection_mem X L s, _, ?_, rfl⟩
  rw [hNsmul]
  exact ⟨b, rfl⟩

/-- The degree-zero fraction `m / sᴺ` named by a twisted global section `m` of degree `N`. -/
private noncomputable def fractionOfTwistedSection (s : L.sections) (N : ℕ)
    (b : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
        (N : ℤ))))).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    sectionAtNonvanishingOpen X L H s :=
  ⟨LocalizedModule.mk (S := Submonoid.powers (homogeneousSection X L s))
      (DirectSum.of _ (N : ℤ) b) ⟨homogeneousSection X L s ^ N, ⟨N, rfl⟩⟩,
    mk_mem_sectionAtNonvanishingOpen X L H s N b⟩

/-- The Tag 0B5L map sends `m / sᴺ` to the section of `H` on `X_s` whose product with `sᴺ` is the
restriction of `m`. -/
private theorem sectionLocalizationMap_fractionOfTwistedSection (s : L.sections) (N : ℕ)
    (b : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
        (N : ℤ))))).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (t : H.val.obj (op (nonvanishingOpen L s)))
    (hb : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (H)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (N : ℤ))))).val.map
        (terminal.from (nonvanishingOpen L s)).op b =
      tensorSectionAtOpen X L H (nonvanishingOpen L s) N t
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ)).val.map
          (terminal.from (nonvanishingOpen L s)).op (sectionPower X L s N))) :
    sectionLocalizationMap X L H s (fractionOfTwistedSection X L H s N b) = t :=
  sectionLocalizationMap_fraction X L H s N b (fractionOfTwistedSection X L H s N b) t rfl hb

/-- **Every section on the nonvanishing open is a value of the Tag 0B5L comparison map**, granted
the two local steps. -/
private theorem exists_preimage_of_locally [CompactSpace X]
    [QuasiSeparatedSpace X] (s : L.sections) (hchart : HasTwistedChartExtension X L H s)
    (hann : HasTwistedCompactAnnihilation X L H s)
    (t : H.val.obj (op (nonvanishingOpen L s))) :
    ∃ z : sectionAtNonvanishingOpen X L H s, sectionLocalizationMap X L H s z = t :=
  ⟨fractionOfTwistedSection X L H s
      (exists_fraction_of_section_of_locally X L H s hchart hann t).choose
      (exists_fraction_of_section_of_locally X L H s hchart hann t).choose_spec.choose,
    sectionLocalizationMap_fractionOfTwistedSection X L H s _ _ t
      (exists_fraction_of_section_of_locally X L H s hchart hann t).choose_spec.choose_spec⟩

/-- **[Stacks, Tag 01PW] part (2).** Let `X` be a quasi-compact and quasi-separated scheme, let
`L` be an invertible `𝒪_X`-module, let `s` be a global section of `L` and let `ℱ` be a
quasi-coherent `𝒪_X`-module. The comparison map of Tag 0B5L
`(⨁_n Γ(X, ℱ ⊗ L^{⊗ n}))_{(s)} ⟶ Γ(X_s, ℱ|_{X_s})` is bijective.

Both chart-local steps of the source's proof are theorems here, so the statement asks only for
the quasi-coherence of `ℱ` and the quasi-compactness and quasi-separatedness of `X`:
`Stacks.SheafOfModules.hasTwistedChartExtension` is Tag 01P7 on an affine chart trivializing
`L`, and `Stacks.SheafOfModules.hasTwistedCompactAnnihilation` is part (1) over a quasi-compact
open. -/
@[stacks 01PW "part (2)"]
theorem sectionLocalizationMap_bijective [CompactSpace X] [QuasiSeparatedSpace X]
    [F.IsQuasicoherent] (s : L.sections) :
    Function.Bijective (sectionLocalizationMap X L F s) :=
  ⟨sectionLocalizationMap_injective X L F s,
    fun t => exists_preimage_of_locally X L F s (hasTwistedChartExtension X L F s)
      (hasTwistedCompactAnnihilation X L F s) t⟩

end GradedSectionLocalization

end Stacks.SheafOfModules

end
