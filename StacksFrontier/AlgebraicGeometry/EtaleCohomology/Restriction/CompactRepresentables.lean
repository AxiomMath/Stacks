module

public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.Presentable.Limits
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Compactness of representable sheaves of sets

An object `X` of a category is *finitely presentable* when `Mor(X, -)` commutes with filtered
colimits. For a sheaf of sets on a site, Yoneda's lemma turns this into a statement about
sections: `Mor(h_U^#, G) = G(U)`, so the sheafified representable `h_U^#` is finitely presentable
exactly when taking sections over `U` commutes with filtered colimits of sheaves. That is not
automatic — a colimit of sheaves is the sheafification of the colimit of the underlying
presheaves, and sections of a sheafification are not sections of the presheaf — but it holds as
soon as the coverings of `U` by finite families with quasi-compact pairwise fibre products are
cofinal among all coverings of `U`, which is part (4) of Stacks 0738.

This file packages that part of Stacks 0738 as a finite-presentability statement, and propagates
it through finite coproducts and coequalizers: a sheaf presented as a coequalizer of two maps
between finite coproducts of such representables is again finitely presentable. Those are
exactly the sheaves the structure theorem Stacks 09Y9 produces from a constructible sheaf of sets
on a quasi-compact quasi-separated scheme, so this is the category-theoretic half of Stacks 09Z4
for sheaves of sets.

## Main results

* `CategoryTheory.Sheaf.coyonedaSheafifiedYonedaIso` — Yoneda's lemma for sheaves of sets in
  functorial form, `Mor(h_U^#, -) ≅ (-)(U)`.
* `CategoryTheory.Sheaf.preservesFilteredColimitsOfSize_sheafSections` — sections over such an
  object commute with filtered colimits of sheaves of sets.
* `CategoryTheory.Sheaf.isFinitelyPresentable_sheafifiedYoneda` — the sheafified representable at
  such an object is finitely presentable.
* `CategoryTheory.Sheaf.isFinitelyPresentable_coequalizer_sigmaSheafifiedYoneda` — so is a
  coequalizer of two maps between finite coproducts of them.
* `CategoryTheory.isFinitelyPresentable_of_isColimit_of_finCategory` — a colimit over a finite
  category of finitely presentable objects is finitely presentable.

## Implementation notes

The Hom-sets of `Sheaf J (Type max u v)`, for `C : Type u` with `Category.{v} C`, live in
`Type (max u v)`, so `max u v` is the level at which finite presentability is asserted here; it
is also the size of index category for which that category of sheaves has all colimits, so it is
the only level at which the hypothesis of Stacks 0738 is available.

The comparison map whose bijectivity Stacks 0738 asserts is `CategoryTheory.Limits.colimit.post`,
which is exactly the map `CategoryTheory.preservesColimit_of_isIso_post` turns into preservation
of a colimit, so no further comparison morphism has to be constructed; and in `Type max u v` the
isomorphisms are the bijections.

The finite coproducts are taken with respect to a `HasColimitsOfShape` instance supplied by the
caller rather than one synthesised here, because a consumer stating a presentation has already
fixed one and the two must agree for the statements to match up.

`Fact Cardinal.aleph0.IsRegular` is a local instance, as in Mathlib's own file on finitely
presentable objects: `IsFinitelyPresentable` is by definition `ℵ₀`-presentability, and every
lemma about the latter requires regularity of the cardinal.

## References

* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- A colimit over a finite category of finitely presentable objects is finitely presentable. -/
@[sga "4 I 8.7.6", sga "4 VI 1.24.2" "more general"]
public theorem isFinitelyPresentable_of_isColimit_of_finCategory
    {D : Type u} [Category.{v} D] [LocallySmall.{w} D]
    {K : Type} [SmallCategory K] [FinCategory K] {Y : K ⥤ D}
    (c : Cocone Y) (hc : IsColimit c) [∀ k, IsFinitelyPresentable.{w} (Y.obj k)] :
    IsFinitelyPresentable.{w} c.pt :=
  isCardinalPresentable_of_isColimit c hc _ ((hasCardinalLT_aleph0_iff _).2 inferInstance)

namespace Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **Yoneda's lemma for sheaves of sets**, as an isomorphism of functors: morphisms out of the
sheafified representable `h_U^#` are the sections over `U`. -/
public def coyonedaSheafifiedYonedaIso (U : C) :
    coyoneda.obj (op ((sheafifiedYoneda J).obj U)) ≅
      (sheafSections J (Type max u v)).obj (op U) :=
  NatIso.ofComponents (fun _ => Equiv.toIso (sectionEquiv J))
    fun β => by ext α; exact sectionEquiv_comp J α β

/-- Sections over an object all of whose coverings are refined by finite coverings with
quasi-compact fibre products commute with filtered colimits of sheaves of sets. This is part (4)
of **Stacks 0738**, read as preservation of colimits rather than as bijectivity of the comparison
map `CategoryTheory.Limits.colimit.post`. -/
public theorem preservesFilteredColimitsOfSize_sheafSections {U : C}
    (H : J.HasFiniteQuasiCompactCoverings U) :
    PreservesFilteredColimitsOfSize.{max u v, max u v}
      ((sheafSections J (Type max u v)).obj (op U)) := by
  refine ⟨fun {I} _ _ => ⟨fun {F} => ?_⟩⟩
  have : IsIso (colimit.post F ((sheafSections J (Type max u v)).obj (op U))) :=
    (isIso_iff_bijective _).2 ((injective_and_bijective_colimit_post_sheafSections J F U).2.2.2 H)
  exact preservesColimit_of_isIso_post _ F

/-- The sheafified representable `h_U^#` is a finitely presentable object of the category of
sheaves of sets, for every object `U` of the site all of whose coverings are refined by finite
coverings with quasi-compact fibre products: part (4) of **Stacks 0738** as finite
presentability. -/
public theorem isFinitelyPresentable_sheafifiedYoneda {U : C}
    (H : J.HasFiniteQuasiCompactCoverings U) :
    IsFinitelyPresentable.{max u v} ((sheafifiedYoneda J).obj U) := by
  rw [isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
  have := preservesFilteredColimitsOfSize_sheafSections J H
  exact ⟨fun _ _ => ⟨preservesColimit_of_natIso _ (coyonedaSheafifiedYonedaIso J U).symm⟩⟩

/-- A finite coproduct of sheafified representables at objects whose coverings are refined by
finite coverings with quasi-compact fibre products is finitely presentable. -/
public theorem isFinitelyPresentable_sigmaSheafifiedYoneda {k : ℕ} (W : Fin k → C)
    (hW : ∀ i, J.HasFiniteQuasiCompactCoverings (W i))
    [HasColimitsOfShape (Discrete (Fin k)) (Sheaf J (Type max u v))] :
    IsFinitelyPresentable.{max u v} (∐ fun i ↦ (sheafifiedYoneda J).obj (W i)) := by
  have : ∀ j : Discrete (Fin k),
      IsFinitelyPresentable.{max u v}
        ((Discrete.functor fun i ↦ (sheafifiedYoneda J).obj (W i)).obj j) := fun ⟨i⟩ =>
    isFinitelyPresentable_sheafifiedYoneda J (hW i)
  exact isFinitelyPresentable_of_isColimit_of_finCategory _ (colimit.isColimit _)

/-- A coequalizer of two maps between finite coproducts of sheafified representables, at objects
whose coverings are refined by finite coverings with quasi-compact fibre products, is finitely
presentable.

This is the shape in which Stacks 09Y9 presents a constructible sheaf of sets on a quasi-compact
quasi-separated scheme, and hence the step of **Stacks 09Z4** for sheaves of sets that does not
depend on the geometry of the small étale site. -/
public theorem isFinitelyPresentable_coequalizer_sigmaSheafifiedYoneda {n m : ℕ}
    (U : Fin n → C) (V : Fin m → C)
    (hU : ∀ i, J.HasFiniteQuasiCompactCoverings (U i))
    (hV : ∀ j, J.HasFiniteQuasiCompactCoverings (V j))
    [HasColimitsOfShape (Discrete (Fin n)) (Sheaf J (Type max u v))]
    [HasColimitsOfShape (Discrete (Fin m)) (Sheaf J (Type max u v))]
    (f g : (∐ fun j ↦ (sheafifiedYoneda J).obj (V j)) ⟶
      ∐ fun i ↦ (sheafifiedYoneda J).obj (U i))
    [HasColimit (parallelPair f g)] :
    IsFinitelyPresentable.{max u v} (coequalizer f g) := by
  have : ∀ j : WalkingParallelPair,
      IsFinitelyPresentable.{max u v} ((parallelPair f g).obj j) := by
    rintro (_ | _)
    · exact isFinitelyPresentable_sigmaSheafifiedYoneda J V hV
    · exact isFinitelyPresentable_sigmaSheafifiedYoneda J U hU
  exact isFinitelyPresentable_of_isColimit_of_finCategory _
    (colimit.isColimit (parallelPair f g))

end Sheaf

end CategoryTheory

end
