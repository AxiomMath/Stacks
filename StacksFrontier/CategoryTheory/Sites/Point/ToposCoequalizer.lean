module

public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
public import Mathlib.CategoryTheory.Sites.Point.Presheaf
public import StacksFrontier.CategoryTheory.Sites.Point.Topos

/-!
# The coequalizer clause of Stacks 05UY

Stacks 05UY asserts that the pushforward `p_* : Set ⥤ Sh(C)` of a point `p` of a topos commutes
with coequalizers. That clause is false (see `errata.md`, 05UY); the other seven properties of
`p_*` listed in 05UY are the theorems `PointOfTopos.*_pushforward` of
`StacksFrontier/CategoryTheory/Sites/Point/Topos.lean`.

## Main results

* `PointOfTopos.preservesColimit_pushforward_of_equivalence`: the corrected clause. For every
  point `p` of every topos, `p_*` commutes with the coequalizer of `f, g : R ⇉ E` whenever the
  relation `{(f r, g r)}` is an equivalence relation on `E`.
* `GrothendieckTopology.Point.not_preservesCoequalizers_pushforward_pointOfTopos_pointBot`: the
  clause as stated fails, for the point of the topos of presheaves on `WalkingParallelPair`
  attached to the object `zero`.

The corrected clause rests on `Types.isSplitCoequalizerOfEquivalence`: the quotient of a set by
an equivalence relation is a *split* coequalizer, and split coequalizers are preserved by every
functor (Mathlib's `IsSplitCoequalizer.map`). The counterexample transports
`Point.subsingleton_fiber_of_preservesCoequalizers` across `Sh(C, ⊥) ≌ PSh(C)`
(`sheafBotEquivalence`).

## References

* [Stacks Project, Tag 05UY](https://stacks.math.columbia.edu/tag/05UY)
-/

@[expose] public section

open CategoryTheory Limits
universe w v u

namespace CategoryTheory.Limits.Types

variable {R E : Type w} (f g : R ⟶ E)

/-- If the relation `{(f r, g r) | r ∈ R}` on `E` is an equivalence relation, then the quotient
map `E → E / ~` is a *split* coequalizer of `f` and `g`: a section `σ` of the quotient map is a
choice of representatives, and since `σ(x̄) ~ x` for every `x`, choosing `r` with
`f r = σ(x̄)` and `g r = x` gives a map `μ : E → R` with `μ ≫ f = π ≫ σ` and `μ ≫ g = 𝟙`. -/
noncomputable def isSplitCoequalizerOfEquivalence
    (h : _root_.Equivalence (Function.Coequalizer.Rel f g)) :
    IsSplitCoequalizer f g (↾(Function.Coequalizer.mk f g)) := by
  classical
  let σ : Function.Coequalizer f g → E := fun q => (Function.Coequalizer.mk_surjective f g q).choose
  have hσ : ∀ q, Function.Coequalizer.mk f g (σ q) = q := fun q =>
    (Function.Coequalizer.mk_surjective f g q).choose_spec
  have hrel : ∀ a b, Function.Coequalizer.Rel f g a b → ∃ r, f r = a ∧ g r = b := by
    rintro _ _ ⟨r⟩
    exact ⟨r, rfl, rfl⟩
  have hμ : ∀ x, ∃ r, f r = σ (Function.Coequalizer.mk f g x) ∧ g r = x := fun x =>
    hrel _ _ (h.eqvGen_iff.1 (Quot.eqvGen_exact (hσ (Function.Coequalizer.mk f g x))))
  exact
    { rightSection := ↾σ
      leftSection := ↾fun x => (hμ x).choose
      condition := by
        ext r
        exact Function.Coequalizer.condition f g r
      rightSection_π := by
        ext q
        exact hσ q
      leftSection_bottom := by
        ext x
        exact (hμ x).choose_spec.2
      leftSection_top := by
        ext x
        exact (hμ x).choose_spec.1 }

end CategoryTheory.Limits.Types

namespace PointOfTopos

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (p : PointOfTopos.{w, v, u} J)

/-- **Stacks 05UY, the coequalizer clause in its corrected form.** The pushforward `p_*` of a
point of a topos commutes with the coequalizer of `f, g : R ⇉ E` whenever the relation
`{(f r, g r)}` on `E` is an equivalence relation, i.e. it carries the quotient `E → E / ~` by an
equivalence relation to a coequalizer in `Sh(C)`.

The clause "commutes with coequalizers" of Stacks 05UY is false for arbitrary pairs
(`GrothendieckTopology.Point.not_preservesCoequalizers_pushforward_pointOfTopos_pointBot`), and
this is the statement that survives (see `errata.md`, 05UY). The quotient by an equivalence
relation is a split coequalizer (`Types.isSplitCoequalizerOfEquivalence`), and split coequalizers
are preserved by every functor (Mathlib's `IsSplitCoequalizer.map`). -/
@[stacks 05UY "the coequalizer clause, corrected: `p_*` commutes with the coequalizer of a pair
  `R ⇉ E` which is an equivalence relation on `E`; for an arbitrary pair the clause is false, see
  `GrothendieckTopology.Point.not_preservesCoequalizers_pushforward_pointOfTopos_pointBot`"]
theorem preservesColimit_pushforward_of_equivalence {R E : Type w} (f g : R ⟶ E)
    (h : _root_.Equivalence (Function.Coequalizer.Rel f g)) :
    PreservesColimit (parallelPair f g) p.pushforward :=
  let t := Types.isSplitCoequalizerOfEquivalence f g h
  preservesColimit_of_preserves_colimit_cocone t.isCoequalizer
    ((isColimitMapCoconeCoforkEquiv p.pushforward t.condition).symm
      (t.map p.pushforward).isCoequalizer)

end PointOfTopos

namespace CategoryTheory.GrothendieckTopology.Point

/-- **The coequalizer clause of Stacks 05UY is false.** There is a point `p` of a topos whose
pushforward `p_* : Set ⥤ Sh(C)` does not commute with coequalizers: take
`C = WalkingParallelPair`, `J = ⊥` (so that `Sh(C, ⊥)` is the category of presheaves,
`sheafBotEquivalence`) and `p` the point of the topos attached to the point `pointBot zero` of
the site, whose fibre functor is `Hom(zero, -)`, so that `u(one) = {left, right}` has two
elements. Since `Sh(C, ⊥) ⥤ PSh(C)` is an equivalence, a preservation of coequalizers by `p_*`
would make the skyscraper presheaf functor preserve them, which
`subsingleton_fiber_of_preservesCoequalizers` forbids. -/
@[stacks 05UY "the coequalizer clause is false: a point of the topos of presheaves on
  `WalkingParallelPair` whose pushforward does not commute with coequalizers; the corrected
  clause is `PointOfTopos.preservesColimit_pushforward_of_equivalence`"]
theorem not_preservesCoequalizers_pushforward_pointOfTopos_pointBot :
    ¬PreservesColimitsOfShape WalkingParallelPair
      (pointBot.{0} (C := WalkingParallelPair) .zero).pointOfTopos.pushforward := by
  intro hp
  have : (sheafToPresheaf (⊥ : GrothendieckTopology WalkingParallelPair) (Type)).IsEquivalence :=
    (sheafBotEquivalence (C := WalkingParallelPair) (A := Type)).isEquivalence_functor
  have hcomp : PreservesColimitsOfShape WalkingParallelPair
      ((pointBot.{0} (C := WalkingParallelPair) .zero).pointOfTopos.pushforward ⋙
        sheafToPresheaf (⊥ : GrothendieckTopology WalkingParallelPair) (Type)) :=
    inferInstance
  have hsub := subsingleton_fiber_of_preservesCoequalizers
    (pointBot.{0} (C := WalkingParallelPair) .zero) hcomp .one
  have hlr := hsub.elim (shrinkYonedaObjObjEquiv.symm WalkingParallelPairHom.left)
    (shrinkYonedaObjObjEquiv.symm WalkingParallelPairHom.right)
  exact absurd (shrinkYonedaObjObjEquiv.symm.injective hlr) (fun h => by cases h)

end CategoryTheory.GrothendieckTopology.Point
