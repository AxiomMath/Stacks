module

public import Mathlib.CategoryTheory.EquivalenceRelation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Descent
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.FpqcLocal

/-!
# The quotient of a scheme by an étale equivalence relation, granted representability

Let `S` be a scheme contained in a big fppf site `B`, let `U` be an object of the big fppf site
over `S`, and let `s, t : R ⟶ U` be an étale equivalence relation on `U` in that site. Let `F`
be a presheaf on the site and `c : h_U ⟶ F` a morphism which exhibits `F` as the quotient of
`U` by `R`: `c` is a surjection of sheaves and `R` represents the kernel pair `h_U ×_F h_U`.

This file proves that the quotient map is then surjective and étale, and that `F` is an
algebraic space over `S`, once the representability of morphisms from schemes to `F` is
granted. Representability is the one input that fppf descent supplies and nothing here can:
the sheaf `h_T × F` is representable for each member of a covering, and concluding that `F`
itself is representable is the effectivity of the corresponding descent datum. It is therefore
taken as a hypothesis, separately in its two strengths — representability of the quotient map
alone for the surjectivity and étaleness statements, and representability of every morphism
from a scheme for the algebraic-space statement.

## Main results

* `AlgebraicGeometry.Space.isPullback_comp_of_isKernelPair`: the base change of the quotient
  map along a morphism from a scheme which lifts to `U` is the base change of the target map of
  the relation, hence representable with no further input.
* `AlgebraicGeometry.Space.presheaf_of_isKernelPair`: a base-change stable, fppf local property
  of morphisms of schemes holds for the quotient map after every representable base change as
  soon as it holds for the source map of the relation.
* `AlgebraicGeometry.Space.surjective_of_isKernelPair` and
  `AlgebraicGeometry.Space.etale_of_isKernelPair`: the quotient map is surjective and étale.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_isKernelPair`: the quotient is an algebraic
  space over `S`.
* `AlgebraicGeometry.Space.isSplitEpi_of_isEquivalenceRelation`: the second of two morphisms
  forming an equivalence relation is a split epimorphism, split by the reflexivity witness.

## Implementation notes

Surjectivity and étaleness of the quotient map are both instances of one descent argument, and
are proved by one lemma, `AlgebraicGeometry.Space.presheaf_of_isKernelPair`, applied to the two
properties. The descent is along the quotient map itself: it is a surjection of sheaves, so
`AlgebraicGeometry.Space.presheaf_of_isLocallySurjective_pullback` reduces the property to its
own base change along itself, and the kernel-pair hypothesis identifies that base change with
the source map of the relation. Étaleness is admissible here because it is fppf local on the
base, which is
`AlgebraicGeometry.etale_isLocalAtTarget_fppf`.

Surjectivity of the source map is not a hypothesis: an equivalence relation has a reflexivity
witness, which splits it, and a split epimorphism of schemes is surjective. Étaleness of the
source map is a hypothesis, being part of the definition of an étale equivalence relation.

For the algebraic-space statement, the sheaf condition is a hypothesis, the atlas is the
quotient map with the two properties just proved, and the representable diagonal is
`CategoryTheory.Functor.relativelyRepresentable.diag_iff` applied to the representability
hypothesis; the big fppf site over `S` has a terminal object and pullbacks, hence the binary
products that criterion needs.

The relation is taken in the site rather than in the category of schemes over `S`, so that the
quotient map is a morphism out of a Yoneda image and the statements compose directly with
`AlgebraicGeometry.isAlgebraicSpace_of_surjective_etale_atlas_of_isAlgebraicSpace_quotient`.
No Stacks tag attribute is placed on the four quotient statements, because each carries a
representability hypothesis that the source's own statement does not.

## References

* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
* [Stacks Project, Tag 02W5](https://stacks.math.columbia.edu/tag/02W5)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
* [Stacks Project, Tag 03KD](https://stacks.math.columbia.edu/tag/03KD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A split epimorphism of schemes is surjective: its section is a set-theoretic right
inverse. -/
theorem surjective_of_isSplitEpi {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSplitEpi f] :
    Surjective f := by
  have _ : Surjective (CategoryTheory.section_ f ≫ f) := by
    rw [IsSplitEpi.id]; infer_instance
  exact Surjective.of_comp (CategoryTheory.section_ f) f

namespace Space

/-- The second of two morphisms forming an equivalence relation is a split epimorphism, split
by the reflexivity witness. -/
theorem isSplitEpi_of_isEquivalenceRelation {C : Type*} [Category C] {A X : C}
    (p q : A ⟶ X) [IsEquivalenceRelation p q] : IsSplitEpi q :=
  let e := (IsEquivalenceRelation.nonempty_equivalenceRelation (p₁ := p) (p₂ := q)).some
  ⟨⟨⟨e.r, e.reflexivity₂⟩⟩⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U R : BigFppfOver B S hS}
  (c : yoneda.obj U ⟶ F) {s t : R ⟶ U}

/-- If a morphism `a : V ⟶ U` of the big fppf site over `S` is followed by the quotient map,
the base change of the quotient map along the composite is the base change of the target map of
the relation along `a`. In particular it is representable, with no descent input: this is the
descent datum that a morphism from a scheme to the quotient produces once it lifts to `U`. -/
theorem isPullback_comp_of_isKernelPair {V : BigFppfOver B S hS} (a : V ⟶ U)
    (hker : IsPullback (yoneda.map t) (yoneda.map s) c c) :
    IsPullback (yoneda.map (pullback.snd a s ≫ t)) (yoneda.map (pullback.fst a s))
      c (yoneda.map a ≫ c) := by
  have hsq : IsPullback (yoneda.map (pullback.fst a s)) (yoneda.map (pullback.snd a s))
      (yoneda.map a) (yoneda.map s) := (IsPullback.of_hasPullback a s).map yoneda
  simpa only [Functor.map_comp] using (hsq.paste_vert hker.flip).flip

/-- A base-change stable property of morphisms of schemes which is fppf local on the base holds
for the quotient map after every representable base change as soon as it holds for the source
map of the relation. The quotient map is a surjection of sheaves, so the property descends from
its base change along itself, which the kernel-pair hypothesis identifies with the source
map. -/
theorem presheaf_of_isKernelPair (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    (hker : IsPullback (yoneda.map t) (yoneda.map s) c c)
    (hc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) c)
    (hrep : yoneda.relativelyRepresentable c)
    (hs : P ((BigFppfOver.toScheme B S hS).map s)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf c := by
  refine presheaf_of_isLocallySurjective_pullback B S hS P c c hrep hc ?_
  have hiso : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (hker.isoPullback.hom ≫ pullback.snd c c) := by
    rw [hker.isoPullback_hom_snd]
    exact (presheaf_yoneda_map_iff B S hS ‹P.IsStableUnderBaseChange› s).2 hs
  exact (MorphismProperty.cancel_left_of_respectsIso _ hker.isoPullback.hom _).mp hiso

/-- The quotient map of an equivalence relation is surjective after every representable base
change, granted its representability. -/
theorem surjective_of_isKernelPair
    (hker : IsPullback (yoneda.map t) (yoneda.map s) c c)
    (hc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) c)
    (hrep : yoneda.relativelyRepresentable c) [IsEquivalenceRelation t s] :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c :=
  have _ : IsSplitEpi s := isSplitEpi_of_isEquivalenceRelation t s
  presheaf_of_isKernelPair B S hS c _ hker hc hrep
    (surjective_of_isSplitEpi ((BigFppfOver.toScheme B S hS).map s))

/-- The quotient map of an étale equivalence relation is étale after every representable base
change, granted its representability. -/
theorem etale_of_isKernelPair
    (hker : IsPullback (yoneda.map t) (yoneda.map s) c c)
    (hc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) c)
    (hrep : yoneda.relativelyRepresentable c)
    (hs : Etale ((BigFppfOver.toScheme B S hS).map s)) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c :=
  presheaf_of_isKernelPair B S hS c _ hker hc hrep hs

/-- The quotient of a scheme of the big fppf site over `S` by an étale equivalence relation is
an algebraic space over `S`, granted that every morphism to it from a scheme of the site is
representable. The quotient map is the atlas, surjective and étale by the two statements above,
and the representability hypothesis gives the diagonal. -/
theorem isAlgebraicSpace_of_isKernelPair
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hker : IsPullback (yoneda.map t) (yoneda.map s) c c)
    (hc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) c)
    (hrepAll : ∀ ⦃V : BigFppfOver B S hS⦄ (g : yoneda.obj V ⟶ F),
      yoneda.relativelyRepresentable g)
    [IsEquivalenceRelation t s]
    (hs : Etale ((BigFppfOver.toScheme B S hS).map s)) :
    IsAlgebraicSpace B S hS F := by
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  refine ⟨hF, Functor.relativelyRepresentable.diag_iff.2 fun _ g => hrepAll g, U, c, ?_, ?_⟩
  · exact surjective_of_isKernelPair B S hS c hker hc (hrepAll c)
  · exact etale_of_isKernelPair B S hS c hker hc (hrepAll c) hs

end Space

end AlgebraicGeometry

end
