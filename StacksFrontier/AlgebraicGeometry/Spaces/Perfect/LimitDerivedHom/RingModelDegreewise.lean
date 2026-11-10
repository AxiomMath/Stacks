module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHom
public import StacksFrontier.Homology.HomotopyCategory.FilteredColimitHomDegreewise

/-!
# The ring-level model of Stacks 09RI from a diagram with a degreewise colimit

`AlgebraicGeometry.Space.DescentSituation.RingModel` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHom.lean` is the affine translation
dictionary that the proof of Stacks 09RI consumes.  Four of its nineteen fields describe the
directed system `N` of complexes of `R`-modules and its colimit: that the transition maps compose
(`htrans`), that the maps to `P` are compatible with them (`hcompat`), that `P` is degreewise
covered by the stages (`hsurj`), and that an element of a stage dying in `P` dies at a later stage
(`hzero`).  The last two are the crux; the module documentation of `LimitDerivedHom.lean` records
that they are assertions about the *modules* in a single degree and are the only place where the
colimit is used.

**This file replaces those four fields by a diagram of complexes with a degreewise colimit
cocone**, which is the shape a limit of algebraic spaces delivers: the system is an honest functor
on the stages, so `htrans` and `hcompat` are functoriality and the cocone law, and `hsurj` and
`hzero` are the element-level description of a filtered colimit of modules.

## The universe restriction, and where it is imposed

The index of Situation 09RH is left free in `AlgebraicGeometry.Space.DescentSituation`, which takes
`I : Type v`.  The constructor below requires `I : Type u`, the universe of the modules and of the
spaces.  The restriction is imposed in
`Stacks.FilteredColimitHom.exists_stage_of_isColimit_eval` and
`Stacks.FilteredColimitHom.exists_le_map_eq_zero_of_isColimit_eval`, i.e. exactly where `hsurj` and
`hzero` are proved, and nowhere else; `Stacks.FilteredColimitHom.exists_descends_derived` *takes*
those two clauses and stays universe-polymorphic in its index, as it should, being unconditionally
true.

It is an input of the source and not a weakening.  Situation 09RD indexes its directed system by a
set in the universe of the schemes, and over a larger index set Stacks 09RE — the scheme-level
statement 09RI reduces to — is **false**:
`AlgebraicGeometry.DescentSituation.exists_not_isHomColimit` of
`StacksFrontier/AlgebraicGeometry/Perfect/LimitHomDescent/Counterexample.lean` exhibits a situation
of type 09RD over a preorder in `Type (u+1)` with `E₀ = K₀ = 𝒪_{S₀}` perfect, pseudo-coherent, of
finite Tor dimension and with quasi-coherent cohomology, for which the conclusion fails.  The
scheme-level `AlgebraicGeometry.DescentSituation.isHomColimit` carries the same restriction,
`I : Type u`.

## What this does and does not supply

The four system fields are supplied from the diagram.  The remaining fifteen — the complex `cx`
with its boundedness, finite presentation and projectivity, and the two bijections `stageEquiv`
and `limitEquiv` with their compatibilities — are arguments, exactly as before.  Those are what the
*affine* case of the source's proof produces, out of the perfectness or pseudo-coherence of `E₀`
and the quasi-coherence of `K₀`, through the affine equivalence
`AlgebraicGeometry.Space.representedAffineDerivedEquivalence` (Stacks 08H1) and the comparison of
the small étale and the Zariski site (Stacks 071Q); this file does not produce them and no
`Prop` binder stands in for them.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.RingModel.ofDegreewiseColimit`.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Lemma 36.29.2 (Tag 09RE)](https://stacks.math.columbia.edu/tag/09RE)
* [Stacks Project, Situation 36.29.1 (Tag 09RD)](https://stacks.math.columbia.edu/tag/09RD)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  [∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y), (modulePullback B S hS f).Additive]
  {D : DescentSituation B S hS hZ I} (sys : D.DerivedPullbackSystem)
  (E₀ K₀ : DerivedCategory (Modules.{u, u} B S hS (D.stage D.base).obj
    (D.stage D.base).property))

/-- **The ring-level model of Stacks 09RI whose system of complexes is a diagram with a degreewise
colimit cocone.**  The four fields describing the system — `htrans`, `hcompat`, `hsurj` and
`hzero` — are supplied from the functoriality of `F`, the cocone law of `c`, and the element-level
description of the degreewise filtered colimit; everything else is an argument.

The index of the situation lies in the universe of the spaces.  See "The universe restriction" in
this file's module documentation for why that is an input of the source, and
`AlgebraicGeometry.DescentSituation.exists_not_isHomColimit` for the counterexample over a larger
index. -/
def RingModel.ofDegreewiseColimit (R : Type u) [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (F : D.Stages ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (c : Cocone F)
    (hc : ∀ n : ℤ, IsColimit
      ((HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n).mapCocone c))
    (cx : CochainComplex (ModuleCat.{u} R) ℤ) (W : Finset ℤ)
    (hW : ∀ n : ℤ, n ∉ W → IsZero (cx.X n))
    (hfp : ∀ n : ℤ, Module.FinitePresentation R (cx.X n)) (deg : ℤ)
    (isStrictlyLE : cx.IsStrictlyLE deg) (projective : ∀ n : ℤ, Projective (cx.X n))
    (stageEquiv : ∀ i : D.Stages, (stageObj sys E₀ i ⟶ stageObj sys K₀ i) ≃
      (Stacks.LimitDerivedHom.derivedObj.{w} R cx ⟶
        Stacks.LimitDerivedHom.derivedObj.{w} R (F.obj i)))
    (limitEquiv : (limitObj sys E₀ ⟶ limitObj sys K₀) ≃
      (Stacks.LimitDerivedHom.derivedObj.{w} R cx ⟶
        Stacks.LimitDerivedHom.derivedObj.{w} R c.pt))
    (stageEquiv_homTransition : ∀ (i j : D.Stages) (h : i ≤ j)
      (g : stageObj sys E₀ i ⟶ stageObj sys K₀ i),
      stageEquiv j (homTransition sys E₀ K₀ i j h g) =
        stageEquiv i g ≫ Stacks.LimitDerivedHom.derivedMap.{w} (F.map (homOfLE h)))
    (limitEquiv_homProjection : ∀ (i : D.Stages)
      (g : stageObj sys E₀ i ⟶ stageObj sys K₀ i),
      limitEquiv (homProjection sys E₀ K₀ i g) =
        stageEquiv i g ≫ Stacks.LimitDerivedHom.derivedMap.{w} (c.ι.app i)) :
    RingModel sys E₀ K₀ R :=
  -- the chosen index is a stage at or beyond itself, so the index of the system is nonempty and
  -- hence filtered, which is what the element-level description of the colimit needs
  have : Nonempty D.Stages := ⟨⟨D.base, le_rfl⟩⟩
  { cx := cx
    N := fun i => F.obj i
    t := @fun _ _ h => F.map (homOfLE h)
    P := c.pt
    ι := fun i => c.ι.app i
    htrans := @fun _ _ _ h h' => Stacks.FilteredColimitHom.map_comp_map F h h'
    hcompat := @fun _ _ h => Stacks.FilteredColimitHom.map_comp_ι F h
    hsurj := Stacks.FilteredColimitHom.exists_stage_of_isColimit_eval F hc
    hzero := Stacks.FilteredColimitHom.exists_le_map_eq_zero_of_isColimit_eval F hc
    W := W
    hW := hW
    hfp := hfp
    deg := deg
    isStrictlyLE := isStrictlyLE
    projective := projective
    stageEquiv := stageEquiv
    limitEquiv := limitEquiv
    stageEquiv_homTransition := stageEquiv_homTransition
    limitEquiv_homProjection := limitEquiv_homProjection }

end DescentSituation

end AlgebraicGeometry.Space

end
