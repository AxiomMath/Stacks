module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# The stalk formula for a pullback, as a mate of the pullback-pushforward adjunction

Let `f : X ⟶ Y` be a morphism of schemes and `x` a point of `X`.  The stalk formula
`Stacks.ModuleSkyscraper.pullbackStalkIso` of Tag 0098,

`(f^*N)_x ≅ 𝒪_{X,x} ⊗_{𝒪_{Y,f x}} N_{f x}`,

is built by conjugating the comparison `Stacks.ModuleSkyscraper.pushSkyIso` of *skyscraper*
adjunctions, so every statement about it speaks of skyscrapers and none of it mentions
`f^* ⊣ f_*`.  That is a real obstruction for a consumer: a statement about the unit or the
counit of `f^* ⊣ f_*` read through stalks cannot be connected to the stalk formula at all.

This file removes the obstruction.  Both sides of the stalk formula are composites of two left
adjoints, so the formula is simultaneously a conjugate across the two *composite* adjunctions
and an iterated mate across the four factors; `CategoryTheory.iterated_mateEquiv_conjugateEquiv`
says those two readings agree.  Reading it the second way identifies the mate of the stalk
formula under `f^* ⊣ f_*` and `extendScalars ⊣ restrictScalars` with the mate of `pushSkyIso`
under the two stalk-skyscraper adjunctions, and that mate is the ordinary germ map

`(f_*M)_{f x} ⟶ M_x`,  `germ_{f x} s ↦ germ_x s`.

With the mate named and computed, `CategoryTheory.mateEquiv_counit` turns into the statement
that the counit of `f^* ⊣ f_*` and the counit of `extendScalars ⊣ restrictScalars` correspond
under the stalk functors, which is the form the derived theory needs.

## Main definitions

* `Stacks.ModuleSkyscraper.pushStalkMap`: the morphism of functors
  `f_* ⋙ (−)_{f x} ⟶ (−)_x ⋙ restrictScalars (f^♯_x)`, defined as the mate of the stalk
  formula under `f^* ⊣ f_*` and `extendScalars (f^♯_x) ⊣ restrictScalars (f^♯_x)`.  It is the
  germ map, by `pushStalkMap_germ`.

## Main results

* `Stacks.ModuleSkyscraper.pushStalkMap_eq_mateEquiv_symm_pushSkyIso`: **the mate lemma.**  The
  mate of the stalk formula across `f^* ⊣ f_*` and `extendScalars ⊣ restrictScalars` is the
  mate of `pushSkyIso` across the two stalk-skyscraper adjunctions.  This is what connects
  `pullbackStalkIso` to the pullback-pushforward adjunction.
* `Stacks.ModuleSkyscraper.pullbackStalkIso_hom_eq_mateEquiv_symm_pushStalkMap`: the
  correspondence runs both ways — the stalk formula is recovered from `pushStalkMap`, so no
  information is lost in passing to the mate.
* `Stacks.ModuleSkyscraper.pushStalkMap_transpose`: the transpose of `pushStalkMap` under the
  stalk-skyscraper adjunction at `f x` is `f_*` of the unit at `x` followed by `pushSkyIso`.
* `Stacks.ModuleSkyscraper.pushStalkMap_germ`: **`pushStalkMap` is the germ map.**  On the germ
  at `f x` of a section of `f_*M` over `V` — that is, of a section of `M` over `f⁻¹V` — it is
  the germ at `x` of that section.  This is what makes the mate lemma a statement about a
  recognisable map rather than about an abstractly transported one.
* `Stacks.ModuleSkyscraper.extendScalars_map_pushStalkMap_comp_counit`: **the counits
  correspond.**  The counit of `f^* ⊣ f_*` at `M`, read on stalks at `x` through the stalk
  formula, is the counit of `extendScalars (f^♯_x) ⊣ restrictScalars (f^♯_x)` at `M_x`
  precomposed with `extendScalars` of `pushStalkMap`.
* `Stacks.ModuleSkyscraper.pullbackPushforwardAdjunction_eq_modulePullbackPushforwardAdjunction`:
  Mathlib's adjunction `f^* ⊣ f_*` for a morphism of schemes *is*
  `RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction` of the underlying morphism
  of ringed spaces, on the nose.  Everything above therefore applies verbatim to the
  ringed-space spelling, which is the one the derived theory is written in.

## Implementation notes

*Which Mathlib lemma does the work.*  `CategoryTheory.iterated_mateEquiv_conjugateEquiv_symm`
is stated for a square whose four sides are all left adjoints, as

`(mateEquiv adj₁ adj₂).symm ((mateEquiv adj₄ adj₃).symm α) = (conjugateEquiv (adj₁.comp adj₄)
(adj₃.comp adj₂)).symm α`.

Instantiating `adj₁` at `f^* ⊣ f_*`, `adj₂` at `extendScalars ⊣ restrictScalars`, `adj₃` at the
stalk-skyscraper adjunction on `Y` at `f x` and `adj₄` at the one on `X` at `x` makes the
right-hand side exactly the definition of `pullbackStalkIso`, whose two composite adjunctions
are `adj₁.comp adj₄` and `adj₃.comp adj₂` as written.  Applying `mateEquiv adj₁ adj₂` to both
sides is the mate lemma.  No hand-rolled mate construction is involved, and in particular the
numbering of the four adjunctions below is forced by that lemma, not chosen.

*Why the germ formula is proved through the transpose and not by unfolding the mate.*
`CategoryTheory.mateEquiv` is a composite of whiskerings and unitors, and unfolding it at an
object produces a composite of three maps of stalks whose source and target types are only
definitionally the sections of `f_*M` over `V` and the sections of `M` over `f⁻¹V`.  Rewriting
under that much definitional slack fails: the germ lemmas of `PullbackStalkColimit.lean` do not
match syntactically.  Transposing across the stalk-skyscraper adjunction at `f x` first removes
the slack, because the transpose is a morphism of sheaves of modules on `Y` and the computation
becomes an equation between two sections over a single open, where the reindexing
`x ∈ f⁻¹V ↔ f x ∈ V` is a reduction.

*Where the mate lemma does and does not get Tag 0E23 moving.*  It supplies precisely the
missing underived compatibility named in the implementation notes of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/ExactPushforwardCounit.lean`.  It is
not by itself the derived statement: carrying it into the derived category still needs the
derived counit (available for an exact pushforward), the characterization of
`AlgebraicGeometry.derivedPullbackStalkIso` — which is phrased against
`AlgebraicGeometry.pullbackComparisonOnComplex`, invertible only at a K-flat complex — and the
identification of `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap` with
`RingTheory.TorIndependence.derivedBaseChangeComparison`.  Nothing here is tagged 0E23.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

universe u

namespace Stacks.ModuleSkyscraper

open CategoryTheory AlgebraicGeometry TopologicalSpace

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)

/-- **Mathlib's `f^* ⊣ f_*` for a morphism of schemes is the ringed-space one.**  Both sides
are `CategoryTheory.SheafOfModules.pullbackPushforwardAdjunction` applied to the same morphism
of `RingCat`-valued sheaves of rings — `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom` on one
side, `RingedSpaceModuleAdjunction.structureSheafHom` on the other — so the equality is
definitional.  It is recorded because the stalk formula and this file are written for schemes
while the derived theory is written for ringed spaces. -/
theorem pullbackPushforwardAdjunction_eq_modulePullbackPushforwardAdjunction :
    Scheme.Modules.pullbackPushforwardAdjunction f =
      RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f.toLRSHom.toShHom := rfl

/-- `pullbackStalkIso` is the conjugate of `pushSkyIso` across the two composite adjunctions,
which is how it is defined; stated so that the mate lemma can rewrite with it. -/
theorem pullbackStalkIso_hom_eq_conjugateEquiv_symm :
    (pullbackStalkIso f x).hom =
      (conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
          (modulesStalkSkyAdjunction X x))
        ((modulesStalkSkyAdjunction Y (f x)).comp
          (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom))).symm
        (pushSkyIso f x).hom := rfl

/-- **The comparison `(f_*M)_{f x} ⟶ M_x`**, as a morphism of functors
`f_* ⋙ (−)_{f x} ⟶ (−)_x ⋙ restrictScalars (f^♯_x)`, defined as the mate of the stalk formula
of Tag 0098 under `f^* ⊣ f_*` and `extendScalars (f^♯_x) ⊣ restrictScalars (f^♯_x)`.

It is the ordinary germ map: `pushStalkMap_germ` computes it on a germ. -/
noncomputable def pushStalkMap :
    Scheme.Modules.pushforward f ⋙ modulesStalkFunctor Y (f x) ⟶
      modulesStalkFunctor X x ⋙ ModuleCat.restrictScalars (f.stalkMap x).hom :=
  mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom)
    (TwoSquare.mk _ _ _ _ (pullbackStalkIso f x).hom)

/-- **The mate lemma.**  The mate of the stalk formula of Tag 0098 under `f^* ⊣ f_*` and
`extendScalars (f^♯_x) ⊣ restrictScalars (f^♯_x)` is the mate of `pushSkyIso` under the two
stalk-skyscraper adjunctions.

Both readings of the same square of four left adjoints are compared by
`CategoryTheory.iterated_mateEquiv_conjugateEquiv_symm`, whose right-hand side at this
instantiation is the definition of `pullbackStalkIso`. -/
theorem pushStalkMap_eq_mateEquiv_symm_pushSkyIso :
    pushStalkMap f x =
      (mateEquiv (modulesStalkSkyAdjunction X x)
        (modulesStalkSkyAdjunction Y (f x))).symm
        (TwoSquare.mk _ _ _ _ (pushSkyIso f x).hom) := by
  have h := iterated_mateEquiv_conjugateEquiv_symm
    (adj₁ := Scheme.Modules.pullbackPushforwardAdjunction f)
    (adj₂ := ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom)
    (adj₃ := modulesStalkSkyAdjunction Y (f x))
    (adj₄ := modulesStalkSkyAdjunction X x)
    (TwoSquare.mk _ _ _ _ (pushSkyIso f x).hom)
  simp only at h
  rw [pushStalkMap, pullbackStalkIso_hom_eq_conjugateEquiv_symm, ← h]
  exact Equiv.apply_symm_apply _ _

/-- The stalk formula is recovered from `pushStalkMap`: the two are mates of each other, so
passing from the stalk formula to the comparison of pushforwards loses nothing. -/
theorem pullbackStalkIso_hom_eq_mateEquiv_symm_pushStalkMap :
    (pullbackStalkIso f x).hom =
      ((mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
        (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom)).symm
        (pushStalkMap f x)) :=
  (Equiv.symm_apply_apply _ _).symm

/-- **The transpose of `pushStalkMap`.**  Under the stalk-skyscraper adjunction at `f x`, the
comparison `(f_*M)_{f x} ⟶ M_x` corresponds to `f_*` of the unit `M ⟶ sky_x(M_x)` followed by
the comparison `f_*(sky_x A) ≅ sky_{f x}(A)` of `pushSkyIso`. -/
theorem pushStalkMap_transpose (M : X.Modules) :
    (modulesStalkSkyAdjunction Y (f x)).homEquiv
        ((Scheme.Modules.pushforward f).obj M)
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
          ((modulesStalkFunctor X x).obj M)) ((pushStalkMap f x).app M) =
      (Scheme.Modules.pushforward f).map ((modulesStalkSkyAdjunction X x).unit.app M) ≫
        (pushSkyIso f x).hom.app ((modulesStalkFunctor X x).obj M) := by
  have hfac : ((mateEquiv (modulesStalkSkyAdjunction X x)
        (modulesStalkSkyAdjunction Y (f x))).symm
        (TwoSquare.mk _ _ _ _ (pushSkyIso f x).hom)).app M =
      (modulesStalkFunctor Y (f x)).map ((Scheme.Modules.pushforward f).map
          ((modulesStalkSkyAdjunction X x).unit.app M)) ≫
        (modulesStalkFunctor Y (f x)).map
          ((pushSkyIso f x).hom.app ((modulesStalkFunctor X x).obj M)) ≫
        (modulesStalkSkyAdjunction Y (f x)).counit.app
          ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
            ((modulesStalkFunctor X x).obj M)) := by
    simp [mateEquiv]
  rw [pushStalkMap_eq_mateEquiv_symm_pushSkyIso, hfac, ← Category.assoc, ← Functor.map_comp,
    Adjunction.homEquiv_naturality_left]
  simp [Adjunction.homEquiv_unit]

/-- **`pushStalkMap` is the germ map.**  A section `s` of `M` over `f⁻¹V` is a section of
`f_*M` over `V`; its germ at `f x` is sent to its germ at `x`. -/
theorem pushStalkMap_germ (M : X.Modules) (V : Y.Opens) (hx : f.base x ∈ V)
    (s : Γ(M, f ⁻¹ᵁ V)) :
    ((pushStalkMap f x).app M)
        ((((Scheme.Modules.pushforward f).obj M).presheaf.germ V (f x) hx) s)
      = (M.presheaf.germ (f ⁻¹ᵁ V) x hx) s :=
  congrArg (fun u ↦ (u.val.app (Opposite.op V)) s ⟨hx⟩) (pushStalkMap_transpose f x M)

/-- **The two counits correspond under the stalk functors.**  Taking the stalk at `x` of the
counit `f^*(f_*M) ⟶ M` of `f^* ⊣ f_*` and transporting along the stalk formula gives the counit
`𝒪_{X,x} ⊗_{𝒪_{Y,f x}} (f_*M)_{f x} ⟶ M_x` of
`extendScalars (f^♯_x) ⊣ restrictScalars (f^♯_x)`, precomposed with `extendScalars` of the germ
map `pushStalkMap`.

This is `CategoryTheory.mateEquiv_counit` at the mate lemma's instantiation, and it is the
compatibility of the stalk formula with the pullback-pushforward adjunction that the derived
theory asks for. -/
theorem extendScalars_map_pushStalkMap_comp_counit (M : X.Modules) :
    (ModuleCat.extendScalars (f.stalkMap x).hom).map ((pushStalkMap f x).app M) ≫
        (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).counit.app
          ((modulesStalkFunctor X x).obj M) =
      (pullbackStalkIso f x).hom.app ((Scheme.Modules.pushforward f).obj M) ≫
        (modulesStalkFunctor X x).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M) :=
  mateEquiv_counit (Scheme.Modules.pullbackPushforwardAdjunction f)
    (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom)
    (TwoSquare.mk _ _ _ _ (pullbackStalkIso f x).hom) M

end Stacks.ModuleSkyscraper
