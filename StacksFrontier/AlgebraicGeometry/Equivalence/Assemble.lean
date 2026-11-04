module

public import StacksFrontier.AlgebraicGeometry.Assembly.ClosedPoints
public import StacksFrontier.AlgebraicGeometry.Gluing.GlueingDataIso

/-!
# Essential surjectivity of the canonical restriction functor, from a per-point chart datum

Let `S` be a scheme and `s : I → S` a finite family of distinct closed points, `V` the open
complement.  A gluing datum consists of a scheme of finite presentation over `V`, one over each
local scheme `Spec 𝒪_{S, s i}`, and an isomorphism of their two restrictions to the punctured
local schemes.  This file shows that such a datum is in the image of
`AlgebraicGeometry.canonicalRestrictionFunctor` as soon as each of its local members admits a
*chart*: an open neighbourhood `W` of `s i` avoiding the other points of the family, a scheme of
finite presentation over `W` whose base change to `Spec 𝒪_{S, s i}` is the given local member,
and an isomorphism of its base change to `V ⊓ W` with that of the given member over `V`,
compatible with the datum's own comparison.

That is the whole of the remaining content of
[Stacks, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)'s `equivalence` label apart from
the chart datum itself, which is
[Stacks, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)'s descent along the punctured
inverse limit.

## The two steps, and why only one square is owed

The charts are glued by `AlgebraicGeometry.exists_finitePresentation_isPullback_glueAvoiding`,
whose two lattice hypotheses the avoidance clause discharges.  Its output is a scheme `X` of
finite presentation over `S` together with *cartesian squares* exhibiting the base chart and
each `W`-chart as restrictions of `X`, and the compatibility of those squares with the given
overlap isomorphisms.

The isomorphism of gluing data is then `AlgebraicGeometry.isoCanonicalRestrictionFunctorObjMk`:
a pair of isomorphisms and one commuting square.  Both isomorphisms come from the cartesian
squares by `CategoryTheory.IsPullback.isoPullback` — the given objects and the chosen base
changes are pullbacks of the same cospan — and the square is
`AlgebraicGeometry.gluingData_square_of_jointly_cartesian`, which needs **only** that the two
families of structure morphisms into `X` intertwine the datum's comparison with the base
change of the chart isomorphism.  Two reductions make that cheap:

* the `snd` components of the square agree by `CategoryTheory.Over.w`, because both sides are
  morphisms over the punctured local scheme, so only the `fst` component is owed;
* the `fst` component is an equation of morphisms into the given local member, and the
  structure morphism of that member down to `X` is a **monomorphism** — it is the base change
  of `AlgebraicGeometry.Scheme.fromSpecStalk`, a preimmersion — so
  `CategoryTheory.cancel_mono` reduces the square to an equation between morphisms into `X`,
  which is exactly the compatibility the gluing supplies.

## Main results

* `AlgebraicGeometry.gluingData_square_of_jointly_cartesian`: the commuting square of an
  isomorphism of gluing data, from the two isomorphisms' compatibility with a family of
  structure morphisms into one scheme over `S`.
* `AlgebraicGeometry.essSurj_canonicalRestrictionFunctor_of_charts`: essential surjectivity of
  the canonical restriction functor from the per-point chart datum.

## Implementation notes

No `@[stacks]` attribute is attached here.  Tag 0E8Q's `equivalence` label has the single
`CategoryTheory.Functor.IsEquivalence` assertion as its covering set, and this file supplies
essential surjectivity conditionally on the chart datum, so it earns no part of it.

The proof of the square is written as a chain of `Eq.trans` against
`CategoryTheory.Category.assoc`, `CategoryTheory.eq_whisker` and `CategoryTheory.whisker_eq`
rather than with `rw` or `simp`.  The reason: the goal produced by
`CategoryTheory.Limits.pullback.hom_ext` composes a morphism whose codomain is spelled through
`AlgebraicGeometry.restrictLocalsToPuncturedLocals` with a projection out of the chosen
pullback, and those two spellings agree only after unfolding a `def`, so the goal is not
type-correct at `implicit` transparency and every keyed rewrite fails on a pattern that is
present.  Term-level composition is checked at default transparency and goes through.

## References

* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
* [Stacks Project, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
  (hs : ∀ i, s i ∈ closedPoints S)

/-- **The commuting square of an isomorphism of gluing data, from joint cartesianness.**  Let
`q : X ⟶ S` be of finite presentation, let `lo` identify its restriction to the open complement
with a gluing datum's open member and `ro` its restrictions to the local schemes with the
datum's local members, and suppose both identifications are compatible with a family of
morphisms `jA`, `jB i` into `X`.  If moreover the datum's own comparison takes `jB i` to `jA`
over each punctured local scheme, the square required by
`AlgebraicGeometry.isoCanonicalRestrictionFunctorObjMk` commutes.

Only the `fst` component of the square is proved: the `snd` components agree because both sides
are morphisms over the punctured local scheme.  The `fst` component is an equation of morphisms
into the datum's local member, and `jB i` is assumed monic, so it is decided by
`CategoryTheory.cancel_mono` from the compatibility equations and the `.2` field of
`AlgebraicGeometry.canonicalRestrictionComparison`. -/
theorem gluingData_square_of_jointly_cartesian (G : glueingData s hs) {X : Scheme.{u}}
    (q : X ⟶ S) (hq : FinitePresentation q)
    (lo : (restrictToComplementOfClosedPoints s hs).obj ⟨Over.mk q, hq⟩ ≅ G.obj.left)
    (ro : (restrictToLocalSchemes s).obj ⟨Over.mk q, hq⟩ ≅ G.obj.right)
    (jA : G.obj.left.obj.left ⟶ X) (jB : ∀ i, (G.obj.right i).obj.left ⟶ X)
    (hmono : ∀ i, Mono (jB i))
    (hlo : lo.hom.hom.left ≫ jA = pullback.fst q (complementOfClosedPoints s hs).ι)
    (hro : ∀ i, (ro.hom i).hom.left ≫ jB i = pullback.fst q (S.fromSpecStalk (s i)))
    (hkey : ∀ i, (G.obj.hom i).hom.left ≫ pullback.fst (G.obj.right i).obj.hom
          ((S.fromSpecStalk (s i) ⁻¹ᵁ complementOfClosedPoints s hs)).ι ≫ jB i =
      pullback.fst G.obj.left.obj.hom
        (S.fromSpecStalk (s i) ∣_ complementOfClosedPoints s hs) ≫ jA) :
    (restrictOpenToPuncturedLocals s hs).map lo.hom ≫ G.obj.hom =
      (canonicalRestrictionComparison s hs).1.hom.app ⟨Over.mk q, hq⟩ ≫
        (restrictLocalsToPuncturedLocals s hs).map ro.hom := by
  funext i
  refine (ObjectProperty.ι _).map_injective (Over.OverMorphism.ext (pullback.hom_ext ?_ ?_))
  · have hmono' := hmono i
    refine (cancel_mono (jB i)).mp ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (_ ≫= hkey i) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (Over.pullback_map_left_comp_fst _ lo.hom.hom =≫ jA) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (_ ≫= hlo) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (_ ≫= (Category.assoc _ _ _).symm) ?_
    refine Eq.trans
      (_ ≫= (Over.pullback_map_left_comp_fst _ (ro.hom i).hom =≫ jB i)) ?_
    refine Eq.trans (_ ≫= Category.assoc _ _ _) ?_
    refine Eq.trans (_ ≫= (_ ≫= hro i)) ?_
    exact (canonicalRestrictionComparison s hs).2 ⟨Over.mk q, hq⟩ i
  · exact (Over.w _).trans (Over.w _).symm

include hs in
/-- **Essential surjectivity of Tag 0E8Q's canonical restriction functor from a per-point chart
datum.**  Suppose that for every gluing datum and every index `i` there is an open neighbourhood
`W` of `s i` avoiding the other points of the family, a scheme `Z` of finite presentation over
`W` whose base change to `Spec 𝒪_{S, s i}` is the datum's `i`-th local member, and an
isomorphism `ψ` of the base changes to `V ⊓ W` of the datum's open member and of `Z`, compatible
with the datum's own comparison over the punctured local scheme.  Then the canonical restriction
functor is essentially surjective.

The chart datum is the content of [Stacks, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA):
`AlgebraicGeometry.exists_affineOpenNhds_model_avoiding` produces the neighbourhood and the
model, and `AlgebraicGeometry.exists_iso_after_baseChange_compat` descends the datum's
comparison to a smaller neighbourhood, which is where `ψ` and the compatibility come from.  The
gluing and the isomorphism of gluing data are what this theorem supplies. -/
theorem essSurj_canonicalRestrictionFunctor_of_charts
    (hdata : ∀ (G : glueingData s hs) (i : I),
      ∃ (W : S.Opens) (hiW : s i ∈ W), (∀ j, j ≠ i → s j ∉ W) ∧
        ∃ (Z : Scheme.{u}) (z : Z ⟶ (W : Scheme.{u})), FinitePresentation z ∧
        ∃ g : (G.obj.right i).obj.left ⟶ Z,
          IsPullback g (G.obj.right i).obj.hom z
            (Scheme.Opens.fromSpecStalkOfMem (X := S) W (s i) hiW) ∧
          ∃ (ψ : (Over.pullback (S.homOfLE (inf_le_left :
                complementOfClosedPoints s hs ⊓ W ≤ complementOfClosedPoints s hs))).obj
              (Over.mk G.obj.left.obj.hom) ≅
            (Over.pullback (S.homOfLE (inf_le_right :
              complementOfClosedPoints s hs ⊓ W ≤ W))).obj (Over.mk z))
            (π : pullback G.obj.left.obj.hom
                (S.fromSpecStalk (s i) ∣_ complementOfClosedPoints s hs) ⟶
              pullback G.obj.left.obj.hom (S.homOfLE (inf_le_left :
                complementOfClosedPoints s hs ⊓ W ≤ complementOfClosedPoints s hs))),
            π ≫ pullback.fst G.obj.left.obj.hom (S.homOfLE (inf_le_left :
                  complementOfClosedPoints s hs ⊓ W ≤ complementOfClosedPoints s hs)) =
                pullback.fst G.obj.left.obj.hom
                  (S.fromSpecStalk (s i) ∣_ complementOfClosedPoints s hs) ∧
              (G.obj.hom i).hom.left ≫ pullback.fst (G.obj.right i).obj.hom
                  ((S.fromSpecStalk (s i) ⁻¹ᵁ complementOfClosedPoints s hs)).ι ≫ g =
                π ≫ ψ.hom.left ≫ pullback.fst z (S.homOfLE (inf_le_right :
                  complementOfClosedPoints s hs ⊓ W ≤ W))) :
    (canonicalRestrictionFunctor s hs).EssSurj := by
  refine essSurj_canonicalRestrictionFunctor_of_exists_iso s hs fun G ↦ ?_
  choose W hiW havoid Z z hz g hg ψ π hπ hcomp using hdata G
  obtain ⟨X, q, jA, hq, sqA, hrest⟩ :=
    exists_finitePresentation_isPullback_glueAvoiding W hiW havoid G.obj.left.property hz ψ
  choose jZ sqZ hcompat using hrest
  have hBX : ∀ i, IsPullback (g i ≫ jZ i) (G.obj.right i).obj.hom q
      (S.fromSpecStalk (s i)) := by
    intro i
    have h := (hg i).flip.paste_vert (sqZ i)
    rw [Scheme.Opens.fromSpecStalkOfMem_ι] at h
    exact h.flip
  have hmono : ∀ i, Mono (g i ≫ jZ i) := by
    intro i
    rw [← IsPullback.isoPullback_hom_fst (hBX i)]
    infer_instance
  have hkey : ∀ i, (G.obj.hom i).hom.left ≫ pullback.fst (G.obj.right i).obj.hom
        ((S.fromSpecStalk (s i) ⁻¹ᵁ complementOfClosedPoints s hs)).ι ≫ (g i ≫ jZ i) =
      pullback.fst G.obj.left.obj.hom
        (S.fromSpecStalk (s i) ∣_ complementOfClosedPoints s hs) ≫ jA := by
    intro i
    refine Eq.trans (_ ≫= (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (hcomp i =≫ jZ i) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (_ ≫= (Category.assoc _ _ _).trans (hcompat i).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact hπ i =≫ jA
  exact ⟨⟨Over.mk q, hq⟩, ⟨isoCanonicalRestrictionFunctorObjMk s hs ⟨Over.mk q, hq⟩ G
    (ObjectProperty.isoMk _ (Over.isoMk sqA.flip.isoPullback.symm
      (IsPullback.isoPullback_inv_snd _)))
    (Pi.isoMk fun i ↦ ObjectProperty.isoMk _ (Over.isoMk (hBX i).isoPullback.symm
      (IsPullback.isoPullback_inv_snd _)))
    (gluingData_square_of_jointly_cartesian s hs G q hq _ _ jA (fun i ↦ g i ≫ jZ i) hmono
      (IsPullback.isoPullback_inv_fst sqA.flip)
      (fun i ↦ IsPullback.isoPullback_inv_fst (hBX i)) hkey)⟩⟩

end AlgebraicGeometry

end
