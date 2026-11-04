module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModuleFibrewise
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialSheafEquivalence

/-!
# The fibrewise reading of a simplicial module is the abelian one, on the nose

Let `(C, J)` be a small site, let `O` be a sheaf of rings on it and let `Δ × C` carry the topology
inherited from `(C, J)` along the projection `π : Δ × C ⥤ C` of [Stacks, Tag 09D0]. There are two
readings of an object of `Δ × C` as a simplicial object on `C`, by restricting to the fibres
`{n} × C`:

* `Stacks.SimplicialModules.fibrewiseMod`, on sheaves of `π^{-1}O`-modules, landing in simplicial
  sheaves of `O`-modules — the functor in which the module-coefficient computation of `Lπ_!` of
  Section 09D0 is stated
  (`Stacks.SimplicialModules.derivedProjectionLowerShriekIsoMooreComplexModules`);
* `Stacks.SimplicialModules.fibrewise`, on sheaves valued in an arbitrary category, landing in
  simplicial sheaves — the functor in which the abelian-coefficient computation is stated
  (`Stacks.SimplicialModules.derivedProjectionLowerShriekIsoMooreComplex`).

This file records that the second is the first read on underlying abelian sheaves, **as an
equality of functors**, which it is because both are restriction along `(φ, 𝟙)` in each section
and nothing is done to the module structure.

## Why this is wanted

The development of [Stacks, Tag 09D2] on the simplicial site —
`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/SimplicialSiteColumnStep.lean`,
`SimplicialSiteBaseChangeStep.lean` and `SimplicialSiteFlatBaseChange.lean` — is
**abelian-valued** throughout: its conclusions are quasi-isomorphisms of complexes of abelian
sheaves on `C`, obtained from `Stacks.SimplicialModules.mooreSheafCochain`. The conclusion of
Tag 09D2 that [Stacks, Tag 09DH] consumes is about `Lπ_!` at *module* coefficients, computed by
`Stacks.SimplicialModules.derivedProjectionLowerShriekIsoMooreBicomplexTotalModules` in
`D(O)` rather than in `D(Ab(C))`.

Those two are joined here. Derived lower shriek itself does **not** commute with forgetting the
module structure (`Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`), which is why the
module-coefficient Section 09D0 had to be proved again rather than deduced; but *once `Lπ_!` has
been computed* as a Moore complex on both sides, the remaining question is whether a map of
complexes of sheaves of `O`-modules is a quasi-isomorphism, and that **is** detected on
underlying abelian sheaves: `SheafOfModules.toSheaf` is exact and reflects isomorphisms
(`Stacks.SheafOfModules.Constant.reflectsIsomorphisms_toSheaf`), so
`HomologicalComplex.quasiIso_map_iff_of_preservesHomology` applies. The equality below is what
identifies the complex that detection produces with the one the abelian development computes.

## Main results

* `Stacks.SimplicialModules.toSheaf_obj_fibreRestrictionMod_obj`: in each simplicial degree, the
  underlying abelian sheaf of the restriction of a sheaf of `π^{-1}O`-modules to the fibre
  `{n} × C` is the restriction of its underlying abelian sheaf.
* `Stacks.SimplicialModules.fibrewiseMod_comp_toSheaf`: **the two fibrewise readings agree**, as
  an equality of functors
  `SheafOfModules(π^{-1}O) ⥤ SimplicialObject (Sheaf J Ab)`.

## Implementation notes

Both statements are `rfl`. The fibre inclusion `i_n : C ⥤ Δ × C` of
`Stacks.SimplicialModules.fibreInclusion` is `CategoryTheory.Functor.prodSectionSnd n`, which is
the functor `Stacks.SimplicialModules.fibrewise` restricts along; the identification
`i_n^{-1}(π^{-1}O) = O` that `Stacks.SimplicialModules.fibreRestrictionMod` uses is the identity
(`Stacks.SimplicialModules.fibreRingMap`), so the pushforward of modules along `i_n` has the
restriction of the underlying abelian sheaf as its underlying abelian sheaf with no comparison
map inserted; and the simplicial structure maps of the two readings are both restriction along
`(φ, 𝟙)`.

## References

* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SimplicialModules

universe w

variable (C : Type w) [SmallCategory C] (J : GrothendieckTopology C)
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  (O : Sheaf J RingCat.{w})

omit [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)] in
/-- **Restriction to a fibre commutes with forgetting the module structure.** The underlying
abelian sheaf of the restriction of a sheaf of `π^{-1}O`-modules `M` to the fibre `{n} × C` is the
degree-`n` term of the fibrewise reading of the underlying abelian sheaf of `M`. Both are the
restriction of the sections of `M` along the fibre inclusion `i_n = prodSectionSnd n`, the
identification `i_n^{-1}(π^{-1}O) = O` inserting nothing. -/
theorem toSheaf_obj_fibreRestrictionMod_obj
    (M : SheafOfModules.{w} (projectionRing C J O)) (n : SimplexCategoryᵒᵖ) :
    (SheafOfModules.toSheaf.{w} O).obj ((fibreRestrictionMod C J O n.unop).obj M) =
      ((fibrewise J AddCommGrpCat.{w}).obj
        ((SheafOfModules.toSheaf.{w} (projectionRing C J O)).obj M)).obj n :=
  rfl

/-- **The module-coefficient fibrewise reading, read on underlying abelian sheaves, is the
abelian fibrewise reading** — an equality of functors

`fibrewiseMod ⋙ (toSheaf O)_* = toSheaf (π^{-1}O) ⋙ fibrewise Ab`.

Both readings restrict along the fibre inclusions `i_n : C ⥤ Δ × C` and take the simplicial
structure map of `φ : m ⟶ n` to be restriction along `(φ, 𝟙)`, and the module structure is
carried along untouched, so there is nothing to compare.

This is what lets the abelian-valued development of [Stacks, Tag 09D2] on the simplicial site be
used for the module-coefficient conclusion that [Stacks, Tag 09DH] needs: a map of complexes of
sheaves of `O`-modules is a quasi-isomorphism exactly when its image under the exact,
isomorphism-reflecting `SheafOfModules.toSheaf` is one, and by this equality that image is the
complex the abelian development computes with. It is not a step of the proof of Tag 09D2 and
carries no tag. -/
theorem fibrewiseMod_comp_toSheaf :
    fibrewiseMod C J O ⋙
        (Functor.whiskeringRight SimplexCategoryᵒᵖ (SheafOfModules.{w} O)
          (Sheaf J AddCommGrpCat.{w})).obj (SheafOfModules.toSheaf.{w} O) =
      SheafOfModules.toSheaf.{w} (projectionRing C J O) ⋙ fibrewise J AddCommGrpCat.{w} :=
  rfl

end Stacks.SimplicialModules

end
