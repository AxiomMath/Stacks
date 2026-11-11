module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.ComparisonDiagram
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.SectionsInjectivityUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.MilnorSequence
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison diagram of a derived inverse limit of cohomology, with nothing assumed

Let `(C, O)` be a ringed site, let `(Kₙ)` be an inverse system in the unbounded derived category
`D(O)` and let `K = R lim Kₙ`, presented by the structural map `p : K ⟶ ∏ Kₙ` of its
distinguished product triangle.  Write `𝓗ᵐₙ` and `𝓗ᵐ` for the cohomology sheaves of `Kₙ` and `K`,
and `U ↦ Hᵐ(U, Kₙ)`, `U ↦ Hᵐ(U, K)` for the cohomology presheaves.  [Stacks, Tag 0BKW] asserts
two things: the commuting square

```
    Hᵐ(-, K)   ⟶   𝓗ᵐ
       ↓             ↓
 lim Hᵐ(-, Kₙ) ⟶ lim 𝓗ᵐₙ
```

whose horizontal maps come from the Tag 0BKV identification of the sheafified cohomology presheaf
with the cohomology sheaf, and, for every object `U` of `C`, the short exact sequence

`0 ⟶ R¹lim Hᵐ⁻¹(U, Kₙ) ⟶ Hᵐ(U, K) ⟶ lim Hᵐ(U, Kₙ) ⟶ 0`,

which is the display (21.23.4.1) of the remark -- [Stacks, Tag 0BKX] -- and which the remark gets
from [Stacks, Tag 0D6K].

Both halves are in the library.  What this file adds is the statement of the tag carrying both of
them at once, and carrying them *unconditionally*.  The square is
`Stacks.Cohomology.DerivedLimitDiagram.cohomologyDerivedLimitDiagram`, stated with the module
universe of the ringed site left entirely free and therefore with five class hypotheses that the
free universe makes unavailable: sheafification of abelian presheaves, that sheafification
inverts exactly the locally bijective maps, that sheaves of `O`-modules are Grothendieck abelian,
that the Tag 0BKV homotopy sections presheaf has an unbounded right derived functor, and that the
inverse system has a product in the derived category.  None of these is a hypothesis of the
source, and each is a *theorem* once the module universe is large enough to contain the site --
the only case in which the category of sheaves of modules is the one the source is talking about.

This file therefore takes the module universe to be `max u v r w` -- still an arbitrary universe,
since `w` is arbitrary -- and discharges all five, so that the tag is available with no class
hypothesis at all beyond the model of the derived category.  This is the same treatment, at the
same module universe, that the module `TruncationTowerConvergenceUnconditional` of
`StacksDraft.CategoryTheory.Sites.Cohomology.DerivedLimit` gives to [Stacks, Tag 0D6M] and
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.SectionsInjectivityUnconditional`
to [Stacks, Tag 0D6L]; the five facts are the same five, and the discharges are those, reused.

Note that the module universe of a `RingedSite` is also its *ring* universe:
`AlgebraicGeometry.RingedSite.{u, v, w}` carries a structure sheaf of rings with sections in `w`,
and the sheaves of `O`-modules here are `SheafOfModules.{w}`.  Taking the ringed site to be a
`RingedSite.{u, v, max u v r w}` is therefore what "the module universe is `max u v r w`" means.

## Main definitions

* `Stacks.Cohomology.DerivedLimitDiagram.sheafificationMax`,
  `Stacks.Cohomology.DerivedLimitDiagram.sheafificationCohomologyPresheafIsoMax`,
  `Stacks.Cohomology.DerivedLimitDiagram.derivedSectionsMax` -- sheafification of presheaves of
  modules, the Tag 0BKV associated-sheaf isomorphism and derived sections over an object of the
  site, each with the discharged instances supplied, so that they can be named in a statement
  that assumes nothing.

## Main results

* `Stacks.Cohomology.DerivedLimitDiagram.cohomologyDerivedLimitDiagram_unconditional` --
  **[Stacks, Tag 0BKW]**: the commuting square and the short exact sequences, with the ringed
  site's own structure as its only class hypothesis.

## Implementation notes

The five facts come from, in order, `Stacks.Cohomology.hasSheafifyMax`,
`Stacks.Cohomology.wEqualsLocallyBijectiveMax`, the instance
`Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck`,
`Stacks.Cohomology.DerivedLimitSections.hasRightDerivedFunctorMaxRingedSite` (named for
[Stacks, Tag 0D6L] at this module universe) and the local instance
`Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules`; the third and the
fifth are found by instance search.  The product is the one that is not
formal: `SheafOfModules O` does not satisfy AB4*, so the countable products of its derived
category come from termwise products of K-injective complexes, [Stacks, Tag 0BK6], which is made
a local instance here so that `∏ᶜ` elaborates in the statement with no hypothesis.

The first two are not instances, for the reason recorded at their definitions: their types
mention the ring universe `r` and the extra module universe `w` only inside the coefficient
universe `max u v r w`, so instance search meets them with those two universes undetermined and
the resulting level constraints are the ones Lean reports as `stuck at solving universe
constraint`.  Restating them with the ringed site named does not help -- the same constraint is
then met while unifying the site of the goal with `X` -- so they are introduced by `haveI` in the
bodies of the three definitions above, each of which has its type ascribed and so pins the
coefficient universe before instance search runs.  Those three definitions exist only to carry
the instances into the statement, where they cannot be inferred; this is the role
`Stacks.Cohomology.DerivedLimitSections.derivedSectionsPresheafMax` plays for Tag 0D6L, and it is
reused here for the cohomology presheaf itself.

The short exact sequences are those of
`Stacks.Cohomology.HypercohomologyEdge.exists_milnor_shortExact_derivedSections`, Tag 0BKX, whose
coefficients are modules over `O(U)` and whose site, ring and module universes are independent,
which is what makes it applicable at this module universe; Tag 0D6K itself is stated with values
in abelian groups and with those three universes collapsed to one.  Only the two maps of the
sequence and its exactness are carried over, with the surjection pinned down by its composites
with the limit projections -- exactly as the square's comparison map into the limit of the
cohomology presheaves is pinned down by its own.  The first derived inverse limit is the cokernel
of the usual `1 - shift` endomorphism of the product, which avoids choosing a right-derived-limit
functor and is the presentation Tags 0BKX and 0D6L already use.

## References

* [Stacks Project, Tag 0BKW](https://stacks.math.columbia.edu/tag/0BKW)
* [Stacks Project, Tag 0BKX](https://stacks.math.columbia.edu/tag/0BKX)
* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
* [Stacks Project, Tag 0D6K](https://stacks.math.columbia.edu/tag/0D6K)
* [Stacks Project, Tag 0D6L](https://stacks.math.columbia.edu/tag/0D6L)
* [Stacks Project, Tag 0D6M](https://stacks.math.columbia.edu/tag/0D6M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry Stacks.Cohomology.SiteCohomologyPresheaf

namespace Stacks.Cohomology.DerivedLimitDiagram

universe u v r w

attribute [local instance] HasDerivedCategory.standard

attribute [local instance]
  Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules

section LargeModules

variable (X : RingedSite.{u, v, max u v r w})

set_option linter.checkUnivs false in
/-- Sheafification of presheaves of modules on a ringed site whose module universe contains the
site, with its instances supplied.  Sheafification of abelian presheaves and local bijectivity
cannot be found by instance search at this universe shape, so the functor is given a name that
carries them. -/
abbrev sheafificationMax :
    PresheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ⥤
      SheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  haveI := hasSheafifyMax.{u, v, r, w} (J := X.J)
  haveI := wEqualsLocallyBijectiveMax.{u, v, r, w} (J := X.J)
  PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)

/-- The Tag 0BKV associated-sheaf isomorphism `S ∘ P ≅ H` of a ringed site whose module universe
contains the site, with its instances supplied: sheafifying the cohomology presheaf
`U ↦ Hᵐ(U, -)` gives the cohomology sheaf `𝓗ᵐ`. -/
abbrev sheafificationCohomologyPresheafIsoMax (m : ℤ) :
    DerivedLimitSections.derivedSectionsPresheafMax.{u, v, r, w} X ⋙
          DerivedCategory.homologyFunctor
            (PresheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) m ⋙
          sheafificationMax.{u, v, r, w} X ≅
        DerivedCategory.homologyFunctor
          (SheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m :=
  haveI := hasSheafifyMax.{u, v, r, w} (J := X.J)
  haveI := wEqualsLocallyBijectiveMax.{u, v, r, w} (J := X.J)
  sheafificationCohomologyPresheafIso X m

set_option linter.checkUnivs false in
/-- Unbounded derived sections over an object of a ringed site whose module universe contains the
site, with its instances supplied.  Its degree-`m` cohomology is the hypercohomology module
`Hᵐ(U, -)` over the ring of sections `O(U)`. -/
abbrev derivedSectionsMax (U : X.C) :
    DerivedCategory (SheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory
        (ModuleCat.{max u v r w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (.op U))) :=
  haveI := hasSheafifyMax.{u, v, r, w} (J := X.J)
  haveI := wEqualsLocallyBijectiveMax.{u, v, r, w} (J := X.J)
  Stacks.Cohomology.HypercohomologyEdge.derivedSections
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U

/-- **Stacks Project, Tag 0BKW.** Let `(C, O)` be a ringed site, let `(Kₙ)` be an inverse system
in `D(O)` and let `K` be a derived limit of it, presented by the structural map `p : K ⟶ ∏ Kₙ` of
its distinguished product triangle.  Fix a degree `m`, write `P` for the cohomology presheaf
functor `M ↦ (U ↦ Hᵐ(U, M))`, `H` for the cohomology sheaf functor, `S` for sheafification and
`e` for the Tag 0BKV identification `S ∘ P ≅ H`.  Then:

* there are comparison maps `a : P K ⟶ lim P Kₙ`, `b : H K ⟶ lim H Kₙ` and
  `c : S (lim P Kₙ) ⟶ lim H Kₙ`, each determined by its composites with the limit projections,
  and the square `S a ≫ c = e ≫ b` commutes; and
* for every object `U` of `C` there is a short exact sequence

  `0 ⟶ R¹lim Hᵐ⁻¹(U, Kₙ) ⟶ Hᵐ(U, K) ⟶ lim Hᵐ(U, Kₙ) ⟶ 0`,

  whose surjection is determined by its composites with the limit projections and whose `R¹lim`
  is the cokernel of the difference map `(xₙ) ↦ (xₙ - fₙ₊₁(xₙ₊₁))`.

The third comparison map is *not* asserted to be invertible: sheafification does not in general
commute with this inverse limit, which is the caveat of the remark.

Nothing is assumed: sheafification, local bijectivity, Grothendieck abelianness, the right
derived functor presenting cohomology and the countable product presenting the derived limit are
all theorems at this module universe, and are supplied here. -/
@[stacks 0BKW "the commuting square and the short exact sequences over the objects of the site"]
theorem cohomologyDerivedLimitDiagram_unconditional
    (K : ℕᵒᵖ ⥤ DerivedCategory
      (SheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory
      (SheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory
          (SheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (m : ℤ) :
    let P := DerivedLimitSections.derivedSectionsPresheafMax.{u, v, r, w} X ⋙
      DerivedCategory.homologyFunctor
        (PresheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) m
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m
    let S := sheafificationMax.{u, v, r, w} X
    let e := sheafificationCohomologyPresheafIsoMax.{u, v, r, w} X m
    (∃ (a : P.obj L ⟶ limit (K ⋙ P))
      (b : H.obj L ⟶ limit (K ⋙ H))
      (c : S.obj (limit (K ⋙ P)) ⟶ limit (K ⋙ H)),
      (∀ n : ℕ,
        a ≫ limit.π (K ⋙ P) ⟨n⟩ =
          P.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) ∧
      (∀ n : ℕ,
        b ≫ limit.π (K ⋙ H) ⟨n⟩ =
          H.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) ∧
      (∀ n : ℕ,
        c ≫ limit.π (K ⋙ H) ⟨n⟩ =
          S.map (limit.π (K ⋙ P) ⟨n⟩) ≫ e.hom.app (K.obj ⟨n⟩)) ∧
      (S.map a ≫ c = e.hom.app L ≫ b)) ∧
    ∀ U : X.C,
      let RG := derivedSectionsMax.{u, v, r, w} X U
      let Mprev := DerivedCategory.homologyFunctor
        (ModuleCat.{max u v r w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (.op U)))
          (m - 1)
      let Mcur := DerivedCategory.homologyFunctor
        (ModuleCat.{max u v r w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (.op U))) m
      let E := K ⋙ RG
      let Fprev := E ⋙ Mprev
      let Fcur := E ⋙ Mcur
      let dprev : (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) ⟶ (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) :=
        Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) (n + 1) ≫
              Fprev.map (homOfLE (Nat.le_succ n)).op
      ∃ (i : cokernel dprev ⟶ Mcur.obj (RG.obj L))
        (q : Mcur.obj (RG.obj L) ⟶ limit Fcur)
        (zero : i ≫ q = 0),
        (ShortComplex.mk i q zero).ShortExact ∧
        ∀ n : ℕ, q ≫ limit.π Fcur ⟨n⟩ =
          Mcur.map (RG.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) := by
  intro P H S e
  refine ⟨@cohomologyDerivedLimitDiagram.{u, v, max u v r w, max u v r w} X
    (hasSheafifyMax.{u, v, r, w} (J := X.J))
    (wEqualsLocallyBijectiveMax.{u, v, r, w} (J := X.J))
    inferInstance
    (DerivedLimitSections.hasRightDerivedFunctorMaxRingedSite.{u, v, r, w} X) K L
    inferInstance p hp m, fun U ↦ ?_⟩
  obtain ⟨_, _, _, _, _, _, i, q, zero, _, _, hse, hq⟩ :=
    @Stacks.Cohomology.HypercohomologyEdge.exists_milnor_shortExact_derivedSections
      X.C _ X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (hasSheafifyMax.{u, v, r, w} (J := X.J))
      (wEqualsLocallyBijectiveMax.{u, v, r, w} (J := X.J))
      inferInstance U K inferInstance L p hp m
  exact ⟨i, q, zero, hse, hq⟩

end LargeModules

end Stacks.Cohomology.DerivedLimitDiagram

end
