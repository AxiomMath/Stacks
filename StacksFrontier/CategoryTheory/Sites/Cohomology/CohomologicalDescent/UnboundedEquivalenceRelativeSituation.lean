module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnboundedEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.BoundedCohomologicalDimensionPushforward
import StacksCore.Tactic.StacksAttribute

/-!
# Derived pullback as an equivalence of unbounded derived categories, with relative bounds

Let `f : (C, 𝒪) ⟶ (C', 𝒪')` be a morphism of ringed sites, let `𝒜 ⊂ Mod(𝒪)` and
`𝒜' ⊂ Mod(𝒪')` be weak Serre subcategories, and assume

1. `f` is flat,
2. `f^*` induces an equivalence `𝒜' ⟶ 𝒜`,
3. `ℱ' ⟶ Rf_*f^*ℱ'` is an isomorphism for every `ℱ'` of `𝒜'`,
4. `C, 𝒪, 𝒜` satisfy the standing Olsson--Laszlo hypothesis of Tag 0D6R,
5. `f` and `𝒜` satisfy the *relative* standing hypothesis of Tag 0D6V.

Then

  `Lf^* : D_{𝒜'}(𝒪') ⟶ D_𝒜(𝒪)`

is an equivalence of categories, with quasi-inverse `Rf_* : D_𝒜(𝒪) ⟶ D_{𝒜'}(𝒪')`. This is
Tag 0D7W, and the content of this file.

## The argument

This is Tag 0D7V with its fifth hypothesis — the Olsson--Laszlo hypothesis of Tag 0D6R for the
*target* site, with its own weak Serre subcategory `𝒜'` — traded for the relative hypothesis of
Tag 0D6V, which instead bounds the cohomology of the modules of `𝒜`, computed on the *source*
site, over the images `u(V'_i)` of the members of cofinal coverings of the objects of a locally
covering class `B'` of the target. The source's proof says that the argument of Tag 0D7V goes
through verbatim with its one appeal to Tag 0D6U replaced by an appeal to Tag 0D6W, and that is
exactly what happens here.

Accordingly the whole argument of Tag 0D7V is isolated in the section `Truncation` below over a
single hypothesis `hTrunc`, the common conclusion of Tag 0D6U part (b) and of Tag 0D6W:

  `Hʲ(Rf_*K) ⟶ Hʲ(Rf_*(τ_{≥ -n}K))` is invertible for `K` in `D_𝒜(𝒪)` and `j ≥ -n`.

Over that hypothesis the three remaining steps are those of Tag 0D7V. Derived pushforward
restricts: for a degree `j`, truncate at `-n ≤ j`; the truncation lies in `D⁺_𝒜(𝒪)`, so its
pushforward lies in `D⁺_{𝒜'}(𝒪')` by the bounded below case, and `hTrunc` identifies `Hʲ` of the
two pushforwards. The counit is invertible on `D_𝒜(𝒪)` degreewise, by reading the naturality
square of the counit at the truncation map in degree `j`, where the truncation map, the counit at
the truncation and `Rf_*` of the truncation map — the last by `hTrunc` — are all invertible. The
unit then follows from the triangle identity, because `f^*` reflects isomorphisms between objects
of `𝒜'`.

Note that Tag 0D6W has no analogue of Tag 0D6U part (a): under the relative hypothesis there is
no cohomological control on the target, and the assertion that `Rf_*` carries `D_𝒜(𝒪)` into
`D_{𝒜'}(𝒪')` is recovered from the truncation comparison together with the bounded below case, as
just described. That is the only structural difference from Tag 0D7V.

## Main definitions

* `Stacks.Cohomology.CohomologicalDescent.derivedPullbackEquivalenceUnboundedRelative`:
  **the equivalence.**
* `Stacks.Cohomology.CohomologicalDescent.derivedAdjunctionUnboundedOfTruncation`: the
  restriction of `Lf^* ⊣ Rf_*` to `D_{𝒜'}(𝒪')` and `D_𝒜(𝒪)`, over the truncation comparison.
* `Stacks.Cohomology.CohomologicalDescent.derivedPullbackEquivalenceUnboundedOfTruncation`: the
  equivalence over the truncation comparison, for a morphism of ringed topoi.

## Main results

* `Stacks.Cohomology.CohomologicalDescent.derivedCategoryB_derivedPullback_obj_relative`: `Lf^*`
  carries `D_{𝒜'}(𝒪')` into `D_𝒜(𝒪)`.
* `Stacks.Cohomology.CohomologicalDescent.derivedCategoryB_derivedPushforward_obj_relative`:
  `Rf_*` carries `D_𝒜(𝒪)` into `D_{𝒜'}(𝒪')`.
* `Stacks.Cohomology.CohomologicalDescent.derivedPullbackEquivalenceUnboundedRelative_functor`
  and `derivedPullbackEquivalenceUnboundedRelative_inverse`: the two functors of the equivalence
  are the restrictions of `Lf^*` and of `Rf_*`.

Along the way:

* `Stacks.Cohomology.CohomologicalDescent.isIso_homology_derivedPushforward_truncGEπ_relative`:
  the truncation comparison of Tag 0D6W, read for the morphism of ringed sites at hand with
  `N = 0`, the vanishing of `Rᵖf_*` above degree zero on `𝒜` coming from hypotheses (2) and (3).
* `Stacks.Cohomology.CohomologicalDescent.derivedCategoryB_derivedPushforward_obj_of_truncation`,
  `isIso_derivedCounit_app_of_derivedCategoryB_of_truncation` and
  `isIso_derivedUnit_app_of_derivedCategoryB_of_truncation`: the three steps above, over the
  truncation comparison.

## Implementation notes

**The morphism is a morphism of ringed sites**, `AlgebraicGeometry.RingedSite.Hom`, as it is in
the source — Tag 0D7V is stated for a morphism of ringed topoi, Tag 0D7W for a morphism of
ringed sites — and it is read as a site-presented morphism of ringed topoi through
`AlgebraicGeometry.RingedSite.Hom.toRingedToposSiteHom`, where the derived pullback, the derived
pushforward and their adjunction live. It is also the setting Tag 0D6W is stated in, because the
identification `Hʲ(V', Rf_*K) = Hʲ(u(V'), K)` its proof rests on is available only for a
morphism of ringed sites. The morphism-of-sites condition is therefore not a hypothesis here but
a field of the morphism, `AlgebraicGeometry.RingedSite.Hom.isMorphismOfSites`. The three
universes of both ringed sites are collapsed, as they already are in
`AlgebraicGeometry.RingedSite.Hom`.

**The two standing hypotheses are carried as loose data**, as they are for Tags 0D6U, 0D6W and
0D7V: a class of objects, an integer bound and a cofinal system of coverings of each member of
the class, rather than `Stacks.Cohomology.OlssonLaszloSituation` and
`Stacks.Cohomology.OlssonLaszloPrimeSituation` arguments, because each of those structures
bundles its own site and sheaf of rings, which here must be those of `X` and of `Y`. So the
hypotheses are the fields of Tag 0D6R and of Tag 0D6V verbatim; in particular the vanishing read
from Tag 0D6V is vanishing of cohomology on the *source* site, over the image `f.u.obj (𝒰.X i)`
of a member of a distinguished covering of the target.

**Flatness is `PreservesFiniteLimits` on `f^*`**, supplied in the form the development uses, the
flatness of the structure map of the auxiliary factorization of `f`; it is what discharges the
input of Tag 093Y that the flat form of Tag 0D6W consumes, and what makes degreewise pullback
exact so that `Lf^*` exists at all. As in Tags 0D7U and 0D7V the final statements open with
`letI`, because the *type* of `Lf^*` mentions the instance saying that degreewise pullback has a
left derived functor, so nothing about `Lf^*` can be written down before that instance is in
scope.

**`Rᵖf_*ℱ` is read as `Hᵖ(Rf_*(ℱ[0]))`**, the convention of Tags 0D6U, 0D6W and 0D7V, so that
every statement is about one and the same functor — the unbounded `Rf_*` of Tag 07A6 — and no
comparison between the bounded below and the unbounded derived functor is needed.

**Only the counit half of the bounded below propagation is needed**, exactly as in Tag 0D7V: Tag
0D7S carries the invertibility of the counit from `𝒜` to `D⁺_𝒜(𝒪)`, which is what the truncation
argument consumes, and the invertibility of the unit on `D_{𝒜'}(𝒪')` then comes from the triangle
identity, so Tag 0D7T is not used.

## References

* [Stacks Project, Tag 0D7W](https://stacks.math.columbia.edu/tag/0D7W)
* [Stacks Project, Tag 0D7V](https://stacks.math.columbia.edu/tag/0D7V)
* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
* [Stacks Project, Tag 0D7S](https://stacks.math.columbia.edu/tag/0D7S)
* [Stacks Project, Tag 0D6R](https://stacks.math.columbia.edu/tag/0D6R)
* [Stacks Project, Tag 0D6V](https://stacks.math.columbia.edu/tag/0D6V)
* [Stacks Project, Tag 0D6U](https://stacks.math.columbia.edu/tag/0D6U)
* [Stacks Project, Tag 0D6W](https://stacks.math.columbia.edu/tag/0D6W)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace Stacks.Cohomology.CohomologicalDescent

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

/-- `Hʲ(Lf^*g)` is invertible if and only if `f^*Hʲ(g)` is. -/
private theorem isIso_homologyFunctor_map_derivedPullback_map_iff
    {X Y : RingedTopos.{u, u, u}}
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (f : RingedToposSiteHom X Y)
    [PreservesFiniteLimits f.pullbackTopos] [PreservesFiniteColimits f.pullbackTopos]
    [(pullbackOnHomotopy f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ))]
    {K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    (j : ℤ) (g : K ⟶ L) :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map ((derivedPullback f).map g)) ↔
      IsIso (f.pullbackTopos.map ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).map g)) :=
  NatIso.isIso_map_iff (derivedPullbackCompHomologyFunctorIso f j) g

/-! ### The equivalence over the truncation comparison

Everything in this section is the argument of Tag 0D7V with its appeal to the Olsson--Laszlo
hypothesis on the target replaced by the hypothesis `hTrunc`, the conclusion that appeal was made
for. Tag 0D6U part (b) and Tag 0D6W both supply `hTrunc`, the former from the hypothesis of Tag
0D6R on the target and the latter from the relative hypothesis of Tag 0D6V; the section is
therefore stated for a morphism of ringed topoi, so that either may feed it. -/

section Truncation

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  (f : RingedToposSiteHom X Y)
  (A : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  (A' : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  [A.IsWeakSerreClass] [A'.IsWeakSerreClass]
  [PreservesFiniteLimits f.pullbackTopos] [PreservesFiniteColimits f.pullbackTopos]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ))]
  (hTrunc : ∀ (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
    DerivedCategoryB.derivedCategoryB A K → ∀ (n : ℕ) (j : ℤ), -(n : ℤ) ≤ j →
      IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).map
        ((derivedPushforward f).map
          ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))))

variable (hA : ∀ M, A' M → A (f.pullbackTopos.obj M))
  (hEquiv : (A.lift (A'.ι ⋙ f.pullbackTopos) (fun N ↦ hA N.obj N.property)).IsEquivalence)
  (hUnit : ∀ M, A' M → IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
    ((DerivedCategory.singleFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M)))

include hTrunc hA hEquiv hUnit in
omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- **`Rf_*` carries `D_𝒜(𝒪)` into `D_{𝒜'}(𝒪')`, over the truncation comparison.** Fix a degree
`j` and truncate at `-n ≤ j`. The truncation lies in `D⁺_𝒜(𝒪)`, so its pushforward lies in
`D⁺_{𝒜'}(𝒪')` by the bounded below case of Tag 0D7U, and the truncation comparison identifies
`Hʲ(Rf_*K)` with `Hʲ` of that pushforward, which therefore lies in `𝒜'`.

This is how the relative situation replaces Tag 0D6U part (a), which has no analogue in Tag
0D6W. -/
theorem derivedCategoryB_derivedPushforward_obj_of_truncation
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : DerivedCategoryB.derivedCategoryB A K) :
    DerivedCategoryB.derivedCategoryB A' ((derivedPushforward f).obj K) := by
  intro j
  obtain ⟨n, hn⟩ : ∃ n : ℕ, -(n : ℤ) ≤ j := ⟨(-j).toNat, by omega⟩
  have := hTrunc K hK n j hn
  refine A'.prop_of_iso (asIso ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).map
      ((derivedPushforward f).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)))).symm ?_
  exact (derivedCategoryBPlus_derivedPushforward_obj_of_exact f A A' hA hEquiv hUnit
    ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K)
    (OlssonLaszlo.truncGETower_obj_mem_plus A K hK n)).2 j

include hTrunc in
omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- **The counit `Lf^*Rf_*K ⟶ K` is invertible for every `K` of `D_𝒜(𝒪)`, over the truncation
comparison.** Fix a degree `j` and truncate at `-n ≤ j`. The truncation map is invertible on
`Hʲ`, the counit at the truncation is invertible because that object lies in `D⁺_𝒜(𝒪)`, and
`Rf_*` of the truncation map is invertible on `Hʲ` by the truncation comparison; applying
`f^* = Hʲ ∘ Lf^*` and reading the naturality square for the counit gives the claim in degree
`j`. -/
theorem isIso_derivedCounit_app_of_derivedCategoryB_of_truncation
    (hCounitPlus : DerivedCategoryB.derivedCategoryBPlus A ≤
      (derivedPullbackPushforwardAdjunctionOfExact f).counitIsIso)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : DerivedCategoryB.derivedCategoryB A K) :
    IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app K) := by
  rw [DerivedCategory.isIso_iff]
  intro j
  obtain ⟨n, hn⟩ : ∃ n : ℕ, -(n : ℤ) ≤ j := ⟨(-j).toNat, by omega⟩
  have hπ := DerivedCategory.isIso_homologyMap_truncGEπ_app (-(n : ℤ)) j hn K
  have hε : IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app
      ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K)) :=
    hCounitPlus _ (OlssonLaszlo.truncGETower_obj_mem_plus A K hK n)
  have hRπ := hTrunc K hK n j hn
  have hLRπ : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map
      ((derivedPullback f).map ((derivedPushforward f).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)))) :=
    (isIso_homologyFunctor_map_derivedPullback_map_iff f j _).2 inferInstance
  have hnat : (DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map
        ((derivedPullback f).map ((derivedPushforward f).map
          ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))) ≫
        (DerivedCategory.homologyFunctor (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map
          ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app
            ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K)) =
      (DerivedCategory.homologyFunctor (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map
          ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app K) ≫
        (DerivedCategory.homologyFunctor (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map
          ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map
      ((derivedPullbackPushforwardAdjunctionOfExact f).counit.naturality
        ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))
  have hcomp : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map
      ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app K) ≫
    (DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map
      ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)) := by
    rw [← hnat]
    exact IsIso.comp_isIso' hLRπ inferInstance
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map
      ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))

include hTrunc hA hEquiv hUnit in
omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- **The unit `K ⟶ Rf_*Lf^*K` is invertible for every `K` of `D_{𝒜'}(𝒪')`, over the truncation
comparison.** By the triangle identity, `Lf^*` of the unit at `K` composed with the counit at
`Lf^*K` is the identity, and the latter is invertible because `Lf^*K` lies in `D_𝒜(𝒪)`; so `Lf^*`
of the unit is invertible. Degreewise this says that `f^*Hʲ` of the unit is invertible, and `f^*`
reflects isomorphisms between objects of `𝒜'`, which both `Hʲ(K)` and `Hʲ(Rf_*Lf^*K)` are. -/
theorem isIso_derivedUnit_app_of_derivedCategoryB_of_truncation
    (hCounitPlus : DerivedCategoryB.derivedCategoryBPlus A ≤
      (derivedPullbackPushforwardAdjunctionOfExact f).counitIsIso)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hK : DerivedCategoryB.derivedCategoryB A' K) :
    IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app K) := by
  have hFK : DerivedCategoryB.derivedCategoryB A ((derivedPullback f).obj K) :=
    derivedCategoryB_derivedPullback_obj_of_exact f A A' hA K hK
  have hGFK : DerivedCategoryB.derivedCategoryB A'
      ((derivedPushforward f).obj ((derivedPullback f).obj K)) :=
    derivedCategoryB_derivedPushforward_obj_of_truncation f A A' hTrunc hA hEquiv hUnit _ hFK
  have hε : IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app
      ((derivedPullback f).obj K)) :=
    isIso_derivedCounit_app_of_derivedCategoryB_of_truncation f A hTrunc hCounitPlus _ hFK
  have hLη : IsIso ((derivedPullback f).map
      ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app K)) := by
    have htri : IsIso ((derivedPullback f).map
        ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app K) ≫
          (derivedPullbackPushforwardAdjunctionOfExact f).counit.app
            ((derivedPullback f).obj K)) := by
      rw [(derivedPullbackPushforwardAdjunctionOfExact f).left_triangle_components K]
      exact (Iso.refl ((derivedPullback f).obj K)).isIso_hom
    exact IsIso.of_isIso_comp_right _
      ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app ((derivedPullback f).obj K))
  rw [DerivedCategory.isIso_iff]
  intro j
  have hpb : IsIso (f.pullbackTopos.map
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).map
        ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app K))) :=
    (isIso_homologyFunctor_map_derivedPullback_map_iff f j _).1 inferInstance
  exact isIso_of_isIso_pullbackTopos_map f A A' hA hEquiv _ (hK j) (hGFK j)

include hTrunc hA hEquiv hUnit in
/-- **The restriction of the derived adjunction `Lf^* ⊣ Rf_*` to the subcategories `D_{𝒜'}(𝒪')`
and `D_𝒜(𝒪)`**, over the truncation comparison. -/
def derivedAdjunctionUnboundedOfTruncation :
    (DerivedCategoryB.derivedCategoryB A).lift
        ((DerivedCategoryB.derivedCategoryB A').ι ⋙ derivedPullback f)
        (fun K ↦ derivedCategoryB_derivedPullback_obj_of_exact f A A' hA K.obj K.property) ⊣
      (DerivedCategoryB.derivedCategoryB A').lift
        ((DerivedCategoryB.derivedCategoryB A).ι ⋙ derivedPushforward f)
        (fun K ↦ derivedCategoryB_derivedPushforward_obj_of_truncation f A A' hTrunc hA hEquiv
          hUnit K.obj K.property) :=
  (derivedPullbackPushforwardAdjunctionOfExact f).restrictFullyFaithful
    (DerivedCategoryB.derivedCategoryB A').fullyFaithfulι
    (DerivedCategoryB.derivedCategoryB A).fullyFaithfulι (Iso.refl _) (Iso.refl _)

include hTrunc hA hEquiv hUnit in
/-- **The equivalence, over the truncation comparison.** The restricted left adjoint is fully
faithful because `D_{𝒜'}(𝒪')` lies in the subcategory of Tag 0D7Q where the unit is invertible,
the restricted right adjoint because `D_𝒜(𝒪)` lies in the subcategory of Tag 0D7R where the
counit is invertible; an adjunction whose two adjoints are fully faithful is an equivalence. -/
def derivedPullbackEquivalenceUnboundedOfTruncation
    (hCounitPlus : DerivedCategoryB.derivedCategoryBPlus A ≤
      (derivedPullbackPushforwardAdjunctionOfExact f).counitIsIso) :
    (DerivedCategoryB.derivedCategoryB A').FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryB A).FullSubcategory :=
  have hUnitB : DerivedCategoryB.derivedCategoryB A' ≤
      (derivedPullbackPushforwardAdjunctionOfExact f).unitIsIso := fun K hK ↦
    isIso_derivedUnit_app_of_derivedCategoryB_of_truncation f A A' hTrunc hA hEquiv hUnit
      hCounitPlus K hK
  have hCounitB : DerivedCategoryB.derivedCategoryB A ≤
      (derivedPullbackPushforwardAdjunctionOfExact f).counitIsIso := fun K hK ↦
    isIso_derivedCounit_app_of_derivedCategoryB_of_truncation f A hTrunc hCounitPlus K hK
  letI hL := (derivedPullbackPushforwardAdjunctionOfExact f).fullyFaithfulιCompLeftAdjointOfLE
    hUnitB
  letI hR := (derivedPullbackPushforwardAdjunctionOfExact f).fullyFaithfulιCompRightAdjointOfLE
    hCounitB
  letI := hL.full
  letI := hL.faithful
  letI := hR.full
  letI := hR.faithful
  (derivedAdjunctionUnboundedOfTruncation f A A' hTrunc hA hEquiv hUnit).toEquivalence

end Truncation

/-! ### Tag 0D7W -/

section Relative

variable {X Y : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  (f : RingedSite.Hom X Y)
  (hf : SheafOfModules.IsFlatMapULift.{u, u, u}
    (StacksPullbackFactorization.auxHomH f.toRingedToposSiteHom).fSharp)
  (A : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  (A' : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  [A.IsWeakSerreClass] [A'.IsWeakSerreClass]
  (hA : ∀ M, A' M → A (f.toRingedToposSiteHom.pullbackTopos.obj M))
  (hEquiv : (A.lift (A'.ι ⋙ f.toRingedToposSiteHom.pullbackTopos)
    (fun N ↦ hA N.obj N.property)).IsEquivalence)
  (B : Set X.C)
  (basisCover : ∀ U : X.C, ∃ 𝒰 : PreZeroHypercover.{u} U,
    𝒰.sieve₀ ∈ X.J U ∧ ∀ i, B (𝒰.X i))
  (degreeBound : ∀ V : X.C, B V → ℤ)
  (coverings : ∀ V : X.C, B V → Stacks.Cohomology.CofinalCoveringSystem X.J V)
  (vanishing : ∀ (V : X.C) (hV : B V) (𝒰 : PreZeroHypercover.{u} V),
    (coverings V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), A F →
        IsZero (Stacks.Cohomology.moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (𝒰.X i) p F))
  (B' : Set Y.C)
  (basisCover' : ∀ U : Y.C, ∃ 𝒰 : PreZeroHypercover.{u} U,
    𝒰.sieve₀ ∈ Y.J U ∧ ∀ i, B' (𝒰.X i))
  (degreeBound' : ∀ V : Y.C, B' V → ℤ)
  (coverings' : ∀ V : Y.C, B' V → Stacks.Cohomology.CofinalCoveringSystem Y.J V)
  (vanishing' : ∀ (V : Y.C) (hV : B' V) (𝒰 : PreZeroHypercover.{u} V),
    (coverings' V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound' V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), A F →
        IsZero (Stacks.Cohomology.moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (f.u.obj (𝒰.X i)) p F))

include hf hA in
omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [A'.IsWeakSerreClass] in
/-- **Stacks 0D7W**, the assertion that derived pullback restricts. Let `f` be a flat morphism of
ringed sites and let `𝒜 ⊂ Mod(𝒪)`, `𝒜' ⊂ Mod(𝒪')` be weak Serre subcategories with
`f^*𝒜' ⊂ 𝒜`. Then `Lf^*` carries `D_{𝒜'}(𝒪')` into `D_𝒜(𝒪)`. Neither standing hypothesis is
needed: derived pullback is degreewise pullback, which is exact, so `Hʲ(Lf^*K)` is `f^*Hʲ(K)`,
and `f^*` carries `𝒜'` into `𝒜`. -/
@[stacks 0D7W "derived pullback"]
theorem derivedCategoryB_derivedPullback_obj_relative :
    letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
      f.isMorphismOfSites_toRingedToposSiteHom hf
    letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f.toRingedToposSiteHom
    ∀ (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))),
      DerivedCategoryB.derivedCategoryB A' K →
        DerivedCategoryB.derivedCategoryB A
          ((derivedPullback f.toRingedToposSiteHom).obj K) := by
  let := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
    f.isMorphismOfSites_toRingedToposSiteHom hf
  let := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
  let := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f.toRingedToposSiteHom
  exact derivedCategoryB_derivedPullback_obj_of_exact f.toRingedToposSiteHom A A' hA

include hf hA hEquiv basisCover vanishing basisCover' vanishing' in
omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [A'.IsWeakSerreClass] in
/-- **The truncation comparison of Tag 0D6W, in the form the equivalence consumes.** For `K` in
`D_𝒜(𝒪)` the canonical map `Hʲ(Rf_*K) ⟶ Hʲ(Rf_*(τ_{≥ -n}K))` is invertible whenever `j ≥ -n`.

This is Tag 0D6W for a flat morphism with `N = 0`; its hypothesis that `Rᵖf_*ℱ` vanish above `N`
on `𝒜` is the statement that `Rf_*ℱ` lies in degrees `≤ 0` for `ℱ` of `𝒜`, which follows from
hypotheses (2) and (3) of Tag 0D7W: writing `ℱ = f^*ℱ'`, the pushforward `Rf_*ℱ` is `ℱ'` placed
in degree zero. -/
theorem isIso_homology_derivedPushforward_truncGEπ_relative
    (hUnit :
      letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
        f.isMorphismOfSites_toRingedToposSiteHom hf
      letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
      letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f.toRingedToposSiteHom
      ∀ M, A' M → IsIso
        ((derivedPullbackPushforwardAdjunctionOfExact f.toRingedToposSiteHom).unit.app
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M))) :
    letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
      f.isMorphismOfSites_toRingedToposSiteHom hf
    letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f.toRingedToposSiteHom
    ∀ (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
      DerivedCategoryB.derivedCategoryB A K → ∀ (n : ℕ) (j : ℤ), -(n : ℤ) ≤ j →
        IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).map
          ((derivedPushforward f.toRingedToposSiteHom).map
            ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))) := by
  let := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
    f.isMorphismOfSites_toRingedToposSiteHom hf
  let := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
  let := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f.toRingedToposSiteHom
  intro K hK n j hj
  exact
    OlssonLaszlo.isIso_homology_derivedPushforward_truncGEπ_of_relativeSituation_of_flat
      f A B basisCover degreeBound coverings vanishing B' basisCover' degreeBound' coverings'
      vanishing' 0
      (fun p hp F hF ↦
        have := isLE_derivedPushforward_singleFunctor_obj_of_exact f.toRingedToposSiteHom A A'
          hA hEquiv hUnit F hF
        DerivedCategory.isZero_of_isLE _ 0 (p : ℤ) hp)
      K hK n j (by omega)

include hf hA hEquiv basisCover vanishing basisCover' vanishing' in
omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- **Stacks 0D7W**, the assertion that derived pushforward restricts. Under the hypotheses of
the source — `f` flat, `f^*` inducing an equivalence `𝒜' ⟶ 𝒜`, the unit `ℱ' ⟶ Rf_*f^*ℱ'`
invertible on `𝒜'`, the source satisfying the Olsson--Laszlo hypothesis of Tag 0D6R and `f`
together with `𝒜` satisfying the relative hypothesis of Tag 0D6V — the pushforward `Rf_*`
carries `D_𝒜(𝒪)` into `D_{𝒜'}(𝒪')`. -/
@[stacks 0D7W "derived pushforward"]
theorem derivedCategoryB_derivedPushforward_obj_relative
    (hUnit :
      letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
        f.isMorphismOfSites_toRingedToposSiteHom hf
      letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
      letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f.toRingedToposSiteHom
      ∀ M, A' M → IsIso
        ((derivedPullbackPushforwardAdjunctionOfExact f.toRingedToposSiteHom).unit.app
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M))) :
    letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
      f.isMorphismOfSites_toRingedToposSiteHom hf
    letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f.toRingedToposSiteHom
    ∀ (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
      DerivedCategoryB.derivedCategoryB A K →
        DerivedCategoryB.derivedCategoryB A'
          ((derivedPushforward f.toRingedToposSiteHom).obj K) := by
  let := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
    f.isMorphismOfSites_toRingedToposSiteHom hf
  let := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
  let := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f.toRingedToposSiteHom
  exact derivedCategoryB_derivedPushforward_obj_of_truncation f.toRingedToposSiteHom A A'
    (isIso_homology_derivedPushforward_truncGEπ_relative f hf A A' hA hEquiv B basisCover
      degreeBound coverings vanishing B' basisCover' degreeBound' coverings' vanishing' hUnit)
    hA hEquiv hUnit

/-- **Stacks 0D7W.** Let `f : (C, 𝒪) ⟶ (C', 𝒪')` be a flat morphism of ringed sites and let
`𝒜 ⊂ Mod(𝒪)`, `𝒜' ⊂ Mod(𝒪')` be weak Serre subcategories such that `f^*` induces an equivalence
`𝒜' ⟶ 𝒜` and the unit `ℱ' ⟶ Rf_*f^*ℱ'` is invertible for every `ℱ'` of `𝒜'`, and assume that
`C, 𝒪, 𝒜` satisfy the standing hypothesis of Tag 0D6R and that `f` together with `𝒜` satisfies
the relative standing hypothesis of Tag 0D6V. Then the derived pullback is an **equivalence**
`D_{𝒜'}(𝒪') ≌ D_𝒜(𝒪)`.

The hypothesis on the unit propagates from `𝒜` to all of `D⁺_𝒜(𝒪)` by Tag 0D7S; the two standing
hypotheses then carry the counit from the bounded below subcategory to the whole derived
category, through Tag 0D6W. This is Tag 0D7V with its appeal to Tag 0D6U replaced by one to Tag
0D6W, which is the source's own description of the proof. -/
@[stacks 0D7W "equivalence"]
def derivedPullbackEquivalenceUnboundedRelative
    (hUnit :
      letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
        f.isMorphismOfSites_toRingedToposSiteHom hf
      letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
      letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f.toRingedToposSiteHom
      ∀ M, A' M → IsIso
        ((derivedPullbackPushforwardAdjunctionOfExact f.toRingedToposSiteHom).unit.app
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M))) :
    (DerivedCategoryB.derivedCategoryB A').FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryB A).FullSubcategory :=
  letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
    f.isMorphismOfSites_toRingedToposSiteHom hf
  letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
  letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f.toRingedToposSiteHom
  derivedPullbackEquivalenceUnboundedOfTruncation f.toRingedToposSiteHom A A'
    (isIso_homology_derivedPushforward_truncGEπ_relative f hf A A' hA hEquiv B basisCover
      degreeBound coverings vanishing B' basisCover' degreeBound' coverings' vanishing' hUnit)
    hA hEquiv hUnit
    (fun K hK ↦ isIso_derivedCounit_app_of_isIso_homology f.toRingedToposSiteHom
      f.isMorphismOfSites_toRingedToposSiteHom hf K
      ((DerivedCategoryB.isBoundedBelow_iff_exists_isGE K).1 hK.1) fun q ↦
        isIso_derivedCounit_app_singleFunctor_obj_of_exact f.toRingedToposSiteHom A A' hA hEquiv
          hUnit _ (hK.2 q))

omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- **Stacks 0D7W**, the identification of the forward functor of the equivalence with the
restriction of the derived pullback. -/
@[stacks 0D7W "forward functor"]
theorem derivedPullbackEquivalenceUnboundedRelative_functor
    (hUnit :
      letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
        f.isMorphismOfSites_toRingedToposSiteHom hf
      letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
      letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f.toRingedToposSiteHom
      ∀ M, A' M → IsIso
        ((derivedPullbackPushforwardAdjunctionOfExact f.toRingedToposSiteHom).unit.app
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M))) :
    letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
      f.isMorphismOfSites_toRingedToposSiteHom hf
    letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f.toRingedToposSiteHom
    (derivedPullbackEquivalenceUnboundedRelative f hf A A' hA hEquiv
      B basisCover degreeBound coverings vanishing
      B' basisCover' degreeBound' coverings' vanishing' hUnit).functor =
      (DerivedCategoryB.derivedCategoryB A).lift
        ((DerivedCategoryB.derivedCategoryB A').ι ⋙
          derivedPullback.{u} f.toRingedToposSiteHom)
        (fun K ↦ derivedCategoryB_derivedPullback_obj_relative f hf A A' hA K.obj
          K.property) :=
  rfl

omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- **Stacks 0D7W**, the identification of the quasi-inverse of the equivalence with the
restriction of the derived pushforward. -/
@[stacks 0D7W "quasi-inverse"]
theorem derivedPullbackEquivalenceUnboundedRelative_inverse
    (hUnit :
      letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
        f.isMorphismOfSites_toRingedToposSiteHom hf
      letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
      letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f.toRingedToposSiteHom
      ∀ M, A' M → IsIso
        ((derivedPullbackPushforwardAdjunctionOfExact f.toRingedToposSiteHom).unit.app
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M))) :
    letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
      f.isMorphismOfSites_toRingedToposSiteHom hf
    letI := f.toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f.toRingedToposSiteHom
    (derivedPullbackEquivalenceUnboundedRelative f hf A A' hA hEquiv
      B basisCover degreeBound coverings vanishing
      B' basisCover' degreeBound' coverings' vanishing' hUnit).inverse =
      (DerivedCategoryB.derivedCategoryB A').lift
        ((DerivedCategoryB.derivedCategoryB A).ι ⋙
          derivedPushforward.{u} f.toRingedToposSiteHom)
        (fun K ↦ derivedCategoryB_derivedPushforward_obj_relative f hf A A' hA hEquiv
          B basisCover degreeBound coverings vanishing
          B' basisCover' degreeBound' coverings' vanishing' hUnit K.obj K.property) :=
  rfl

end Relative

end Stacks.Cohomology.CohomologicalDescent

end
