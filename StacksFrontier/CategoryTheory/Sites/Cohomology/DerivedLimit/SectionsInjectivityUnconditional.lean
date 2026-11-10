module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.SectionsInjectivity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergenceUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# Injectivity on sections of cohomology of a derived inverse limit, with nothing assumed

[Stacks, Tag 0D6L] is proved in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedLimit/SectionsInjectivity.lean` with the
module universe of the ringed site left entirely free, and therefore with five class hypotheses
that the free universe makes unavailable: sheafification of abelian presheaves, that
sheafification inverts exactly the locally bijective maps, that sheaves of `O`-modules are
Grothendieck abelian, that the Tag 0BKV homotopy sections presheaf has an unbounded right
derived functor, and that the inverse system has a product in the derived category.

None of these is a hypothesis of the source.  Each of them is a *theorem* once the module
universe is large enough to contain the site, which is the only case in which the category of
sheaves of modules is the one the source is talking about.  This file takes the module universe
to be `max u v r w` -- still an arbitrary universe, since `w` is arbitrary -- and discharges all
five, so that the tag is available with no class hypothesis at all beyond the model of the
derived category.  This is the same treatment, at the same module universe, that
`TruncationTowerConvergenceUnconditional.lean` (in this directory) gives to [Stacks, Tag 0D6M].

Note that the module universe of a `RingedSite` is also its *ring* universe:
`AlgebraicGeometry.RingedSite.{u, v, w}` carries a structure sheaf of rings with sections in
`w`, and the sheaves of `O`-modules of this file are `SheafOfModules.{w}`.  Taking the ringed
site to be a `RingedSite.{u, v, max u v r w}` is therefore what "the module universe is
`max u v r w`" means here.

## Main results

* `Stacks.Cohomology.DerivedLimitSections.hasRightDerivedFunctorMaxRingedSite` -- one of the
  five facts, at the module universe `max u v r w`.  Two more are
  `Stacks.Cohomology.hasSheafifyMax` and `Stacks.Cohomology.wEqualsLocallyBijectiveMax`, already
  proved for [Stacks, Tag 0D6M] in `TruncationTowerConvergenceUnconditional.lean` and reused
  here; the last two, Grothendieck abelianness and the countable product, are found by instance
  search (see the implementation notes).
* `Stacks.Cohomology.DerivedLimitSections.derivedSectionsPresheafMax` -- the Tag 0BKV derived
  sections presheaf with those instances supplied, so that it can be named in a statement that
  assumes nothing.
* `DerivedLimitSections.cohomology_derivedLimit_projection_mono_on_sections_unconditional`
  -- **[Stacks, Tag 0D6L]**, with the ringed site's own structure as its only class hypothesis.

## Implementation notes

The five facts come from, in order:

* `Stacks.Cohomology.hasSheafifyMax`, hence
  `Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp`,
* `Stacks.Cohomology.wEqualsLocallyBijectiveMax`, hence
  `Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp`,
* `Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck`,
* `Stacks.Cohomology.Localization.hasRightDerivedFunctorOfGrothendieck`, which computes the
  unbounded right derived functor of any functor out of the homotopy category of a Grothendieck
  abelian category on functorial K-injective resolutions,
* `Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules`.

The last one is the one that is not formal.  `SheafOfModules O` does not satisfy AB4\*, so the
countable products of its derived category cannot be obtained from [Stacks, Tag 07KC]; they come
instead from termwise products of K-injective complexes, [Stacks, Tag 0BK6].

The first two are *not* registered as instances, and are instead applied by hand through `@`.
Their types mention the ring universe `r` and the extra module universe `w` only inside the
coefficient universe `max u v r w`, so instance search meets them with those two universes
undetermined and the resulting level constraints are the ones Lean reports as `stuck at solving
universe constraint`.  The other three name the structure sheaf of the ringed site, which pins
the ring universe, so they are reachable by instance search;
`hasProductsOfShape_derivedCategory_sheafOfModules` is made a local instance here, and the other
two are global ones already.  `derivedSectionsPresheafMax` exists only to carry the two
hand-applied instances into the hypotheses of the statement, where they cannot be inferred.

## References

* [Stacks Project, Tag 0D6L](https://stacks.math.columbia.edu/tag/0D6L)
* [Stacks Project, Tag 0D6M](https://stacks.math.columbia.edu/tag/0D6M)
* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry Stacks.Cohomology.SiteCohomologyPresheaf

namespace Stacks.Cohomology.DerivedLimitSections

universe u v r w

attribute [local instance] HasDerivedCategory.standard

attribute [local instance]
  Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules

section LargeModules

variable (X : RingedSite.{u, v, max u v r w})

/-- **The Tag 0BKV homotopy sections presheaf has an unbounded right derived functor**, once the
module universe contains the site: sheaves of modules are then Grothendieck abelian, so every
cochain complex of them has a functorial K-injective resolution. -/
theorem hasRightDerivedFunctorMaxRingedSite :
    (@homotopySectionsPresheaf X (hasSheafifyMax.{u, v, r, w} (J := X.J))
        (wEqualsLocallyBijectiveMax.{u, v, r, w} (J := X.J))).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (.up ℤ)) :=
  inferInstance

set_option linter.checkUnivs false in
/-- The Tag 0BKV derived sections presheaf of a ringed site whose module universe contains the
site, with its three instances supplied.  Sheafification and local bijectivity cannot be found
by instance search at this universe shape, so the functor is given a name that carries them. -/
abbrev derivedSectionsPresheafMax :
    DerivedCategory (SheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory
        (PresheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :=
  @derivedSectionsPresheaf X (hasSheafifyMax.{u, v, r, w} (J := X.J))
    (wEqualsLocallyBijectiveMax.{u, v, r, w} (J := X.J))
    (hasRightDerivedFunctorMaxRingedSite.{u, v, r, w} X)

/-- **Stacks Project, Tag 0D6L.** Let `(C, O)` be a ringed site, let `(Kₙ)` be an inverse system
in `D(O)` with derived limit `L`, let `V` be an object of `C` and let `m` be an integer.  Suppose
there are an index `N` and a cofinal system of coverings of `V` such that over every member
`Vᵢ` of every covering in the system

* `R¹ lim Hᵐ⁻¹(Vᵢ, Kₙ) = 0`, and
* `Hᵐ(Vᵢ, Kₙ) ⟶ Hᵐ(Vᵢ, K_N)` is injective for `n ≥ N`.

Then `Hᵐ(L)(V) ⟶ Hᵐ(K_N)(V)` is injective.

Nothing is assumed: sheafification, local bijectivity, Grothendieck abelianness, the right
derived functor presenting cohomology and the countable product presenting the derived limit are
all theorems at this module universe, and are supplied above. -/
@[stacks 0D6L]
theorem cohomology_derivedLimit_projection_mono_on_sections_unconditional
    (K : ℕᵒᵖ ⥤ DerivedCategory
      (SheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory
      (SheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory
          (SheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (V : X.C) (m : ℤ) (N : ℕ)
    (Cov : CofinalCoveringSystem X.J V)
    (hlimOne : ∀ 𝒰 : PreZeroHypercover.{max u v} V, Cov.cov 𝒰 →
      ∀ i : 𝒰.I₀,
        let F := K ⋙ derivedSectionsPresheafMax.{u, v, r, w} X ⋙
          DerivedCategory.homologyFunctor
            (PresheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
              (m - 1) ⋙
          PresheafOfModules.evaluation
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (.op (𝒰.X i))
        IsZero (cokernel (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫
              F.map (homOfLE (Nat.le_succ n)).op)))
    (hinj : ∀ 𝒰 : PreZeroHypercover.{max u v} V, Cov.cov 𝒰 →
      ∀ i : 𝒰.I₀,
        let F := K ⋙ derivedSectionsPresheafMax.{u, v, r, w} X ⋙
          DerivedCategory.homologyFunctor
            (PresheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) m ⋙
          PresheafOfModules.evaluation
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (.op (𝒰.X i))
        ∀ (n : ℕ) (hn : N ≤ n), Mono (F.map (homOfLE hn).op)) :
    Mono ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (.op V)).map
      ((DerivedCategory.homologyFunctor
          (SheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m).map
        (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) N))) :=
  @cohomology_derivedLimit_projection_mono_on_sections.{u, v, max u v r w, max u v r w} X
    (hasSheafifyMax.{u, v, r, w} (J := X.J))
    (wEqualsLocallyBijectiveMax.{u, v, r, w} (J := X.J))
    inferInstance
    (hasRightDerivedFunctorMaxRingedSite.{u, v, r, w} X) K L
    inferInstance p hL V m N Cov hlimOne hinj

end LargeModules

end Stacks.Cohomology.DerivedLimitSections

end
