module

public import StacksFrontier.AlgebraicGeometry.LimitDescent.Faithfulness
public import StacksFrontier.AlgebraicGeometry.LimitDescentFull.Fullness
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GlueingAux2
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Two models over one arbitrary stage become isomorphic over a later stage

Let `S = lim Sᵢ` be a directed inverse limit of schemes with affine transition morphisms, **with
no finiteness hypothesis whatsoever on the stages `Sᵢ`**, and let `Z` be a scheme over `S`.
Suppose `Z` is presented in two ways as the base change of a quasi-compact, quasi-separated
scheme locally of finite presentation over one and the same stage `Sᵢ`.  This file shows that the
two models become isomorphic over a later stage, by an isomorphism compatible with the two
presentations, and that the two models transported to that later stage are again quasi-compact,
quasi-separated and locally of finite presentation over it.

This is the arbitrary-stage replacement for
`AlgebraicGeometry.exists_iso_of_isPullback_of_isPullback`, which assumes the stages quasi-compact
and quasi-separated and both models of finite presentation.
It is the ingredient a glueing induction over the predicate
`AlgebraicGeometry.LimitDescent.HasQcqsModel'` needs in order to identify the two descents of an
intersection of two members of a cover at a single later stage.

## Main results

* `AlgebraicGeometry.LimitDescent.exists_iso_over_after_baseChange_of_small`: the statement above
  in the `CategoryTheory.Over` idiom, where base change is `CategoryTheory.Over.pullback` and a
  presentation of `Z` is an isomorphism in `Over S`.
* `AlgebraicGeometry.LimitDescent.exists_iso_of_isPullback_of_isPullback_of_small`: the same
  statement with both models and both presentations transported to the later stage as pullback
  squares, which is the form the glueing consumes.

## Implementation notes

The two halves of Stacks Tag 0EY1 are available over arbitrary stages, as
`AlgebraicGeometry.LimitDescent.exists_morphism_after_baseChange_of_small` and
`AlgebraicGeometry.LimitDescent.eventually_eq_of_baseChange_eq_of_small`, so the only thing to do
is to assemble an *isomorphism* out of them.  That is
`AlgebraicGeometry.LimitDescent.exists_isIso_baseChange_of_isIso_limit` below, the arbitrary-stage
replacement for `AlgebraicGeometry.exists_isIso_baseChange_of_isIso_limitBaseChange`: fullness
descends the inverse of the base change of `g` to a morphism `g'` over a later stage, there the
base changes of `g ≫ g'` and of the identity to the limit agree, and faithfulness makes them agree
already over a further stage.

The comparison isomorphisms fullness hands back are pinned down by their compatibility with the
first pullback projections, and that is exactly the characterisation
`AlgebraicGeometry.iso_eq_overPullbackCompIso` provides.  Replacing them by
`AlgebraicGeometry.overPullbackCompIso` turns the equation fullness returns into a statement
about which the naturality of `AlgebraicGeometry.overPullbackCompIso` can be used, which is what
makes the two faithfulness inputs a one-line computation.

Transporting a descended morphism from one stage to a later one, and transporting an equality of
descended morphisms, are the two pieces of bookkeeping the argument needs; both are the same
conjugation by `AlgebraicGeometry.overPullbackCompIso`, carried out in
`AlgebraicGeometry.LimitDescent.isIso_overPullback_map_of_isIso_comp` and
`AlgebraicGeometry.LimitDescent.overPullback_map_eq_of_comp_eq`.

The index type is assumed `u`-small, where `u` is the universe of the schemes; this is the
restriction already carried by both halves of the tag, and it comes from the same place.

## References

* [Stacks Project, Tag 0EY1](https://stacks.math.columbia.edu/tag/0EY1)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 081E](https://stacks.math.columbia.edu/tag/081E)

Tags covered: none.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.LimitDescent

/-! ### Base change preserves the hypotheses on a model -/

section BaseChangeHypotheses

variable {S T : Scheme.{u}} (q : T ⟶ S) (X : Over S)

/-- Base change preserves being locally of finite presentation. -/
private lemma locallyOfFinitePresentation_overPullback_hom
    (hX : LocallyOfFinitePresentation X.hom) :
    LocallyOfFinitePresentation ((Over.pullback q).obj X).hom := by
  have := hX
  exact inferInstanceAs (LocallyOfFinitePresentation (pullback.snd X.hom q))

variable [IsAffineHom q]

/-- The first projection of a base change along an affine morphism is affine. -/
private lemma isAffineHom_pullback_fst : IsAffineHom (pullback.fst X.hom q) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback X.hom q).flip inferInstance

/-- Base change along an affine morphism preserves quasi-compactness of the source. -/
private lemma compactSpace_overPullback_left (hX : CompactSpace X.left) :
    CompactSpace ((Over.pullback q).obj X).left := by
  have := hX
  have := isAffineHom_pullback_fst q X
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst X.hom q)

/-- Base change along an affine morphism preserves quasi-separatedness of the source. -/
private lemma quasiSeparatedSpace_overPullback_left (hX : QuasiSeparatedSpace X.left) :
    QuasiSeparatedSpace ((Over.pullback q).obj X).left := by
  have := hX
  have := isAffineHom_pullback_fst q X
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst X.hom q)

end BaseChangeHypotheses

/-! ### Transporting a descended morphism to a later stage -/

section Transport

variable {S S' T : Scheme.{u}} (p : S ⟶ T) (q : S' ⟶ S) (r : S' ⟶ T) {X Y : Over T}

/-- Two morphisms whose iterated base changes agree have equal direct base changes. -/
private lemma overPullback_map_eq_of_comp_eq (h : q ≫ p = r) (u v : X ⟶ Y)
    (huv : (Over.pullback q).map ((Over.pullback p).map u) =
      (Over.pullback q).map ((Over.pullback p).map v)) :
    (Over.pullback r).map u = (Over.pullback r).map v := by
  have hu := overPullbackCompIso_naturality p q r h u
  have hv := overPullbackCompIso_naturality p q r h v
  rw [huv] at hu
  exact (cancel_epi (overPullbackCompIso p q r h X).hom).1 (hu.trans hv.symm)

/-- The comparison isomorphism is natural in the scheme being base changed, read on inverses. -/
private lemma overPullbackCompIso_inv_naturality (h : q ≫ p = r) (u : X ⟶ Y) :
    (overPullbackCompIso p q r h X).inv ≫ (Over.pullback q).map ((Over.pullback p).map u) =
      (Over.pullback r).map u ≫ (overPullbackCompIso p q r h Y).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, overPullbackCompIso_naturality p q r h u]
  simp

/-- A morphism whose iterated base change is an isomorphism has an isomorphism for its direct
base change. -/
private lemma isIso_overPullback_map_of_isIso_comp (h : q ≫ p = r) (u : X ⟶ Y)
    (hu : IsIso ((Over.pullback q).map ((Over.pullback p).map u))) :
    IsIso ((Over.pullback r).map u) := by
  have := hu
  have hnat := overPullbackCompIso_naturality p q r h u
  have heq : (Over.pullback r).map u = (overPullbackCompIso p q r h X).inv ≫
      (Over.pullback q).map ((Over.pullback p).map u) ≫
        (overPullbackCompIso p q r h Y).hom := by
    rw [← hnat]
    simp
  rw [heq]
  infer_instance

end Transport

/-! ### The stages -/

section Stages

variable {I : Type v} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})

/-- Transitivity of the order, read through the opposite category. -/
private lemma homOfLE_op_comp {i j m : I} (hij : i ≤ j) (hjm : j ≤ m) :
    (homOfLE hjm).op ≫ (homOfLE hij).op = (homOfLE (hij.trans hjm)).op :=
  Subsingleton.elim _ _

/-- Transitivity of the order, read through the diagram. -/
private lemma map_homOfLE_op_comp {i j m : I} (hij : i ≤ j) (hjm : j ≤ m) :
    D.map (homOfLE hjm).op ≫ D.map (homOfLE hij).op =
      D.map (homOfLE (hij.trans hjm)).op := by
  rw [← D.map_comp, homOfLE_op_comp]

/-- Transporting a presentation of a scheme over the limit along two successive stages keeps its
first pullback projection. -/
private lemma overPullback_presentation_fst (c : Cone D) {i j m : I} (hij : i ≤ j) (hjm : j ≤ m)
    (X : Over (D.obj (.op i))) {Z : Scheme.{u}} {fZ : Z ⟶ c.pt}
    (e : Over.mk fZ ≅ (Over.pullback (c.π.app (.op i))).obj X)
    (α : (Over.pullback (c.π.app (.op j))).obj ((Over.pullback (D.map (homOfLE hij).op)).obj X) ≅
      (Over.pullback (c.π.app (.op i))).obj X)
    (hα : α.hom.left ≫ pullback.fst X.hom (c.π.app (.op i)) =
      pullback.fst ((Over.pullback (D.map (homOfLE hij).op)).obj X).hom (c.π.app (.op j)) ≫
        pullback.fst X.hom (D.map (homOfLE hij).op)) :
    (e ≪≫ α.symm ≪≫ (overPullbackCompIso (D.map (homOfLE hjm).op) (c.π.app (.op m))
        (c.π.app (.op j)) (c.w _) ((Over.pullback (D.map (homOfLE hij).op)).obj X)).symm ≪≫
      (Over.pullback (c.π.app (.op m))).mapIso (overPullbackCompIso (D.map (homOfLE hij).op)
        (D.map (homOfLE hjm).op) (D.map (homOfLE (hij.trans hjm)).op)
        (map_homOfLE_op_comp D hij hjm) X)).hom.left ≫
      pullback.fst ((Over.pullback (D.map (homOfLE (hij.trans hjm)).op)).obj X).hom
        (c.π.app (.op m)) ≫ pullback.fst X.hom (D.map (homOfLE (hij.trans hjm)).op) =
      e.hom.left ≫ pullback.fst X.hom (c.π.app (.op i)) := by
  have hα₂fst := overPullbackCompIso_fst (D.map (homOfLE hjm).op) (c.π.app (.op m))
    (c.π.app (.op j)) (c.w _) ((Over.pullback (D.map (homOfLE hij).op)).obj X)
  have hγfst := overPullbackCompIso_fst (D.map (homOfLE hij).op) (D.map (homOfLE hjm).op)
    (D.map (homOfLE (hij.trans hjm)).op) (map_homOfLE_op_comp D hij hjm) X
  set α₂ := overPullbackCompIso (D.map (homOfLE hjm).op) (c.π.app (.op m))
    (c.π.app (.op j)) (c.w _) ((Over.pullback (D.map (homOfLE hij).op)).obj X)
  set γ := overPullbackCompIso (D.map (homOfLE hij).op) (D.map (homOfLE hjm).op)
    (D.map (homOfLE (hij.trans hjm)).op) (map_homOfLE_op_comp D hij hjm) X
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Over.comp_left, Category.assoc]
  rw [reassoc_of% overPullback_map_left_fst (c.π.app (.op m)) γ.hom, hγfst,
    reassoc_of% overPullback_inv_left_comp_fst α₂ hα₂fst, overPullback_inv_left_comp_fst α hα]

end Stages

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [Small.{u} I]
  (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)]
  (c : Cone D)

/-- Two morphisms between quasi-compact, quasi-separated models locally of finite presentation
over a stage whose composites become identities over the limit are inverse isomorphisms over some
later stage. -/
private lemma exists_isIso_baseChange_of_comp_eq_id_limit (hc : IsLimit c) (k : I)
    (X Y : Over (D.obj (.op k)))
    (hXqc : CompactSpace X.left) (hXqs : QuasiSeparatedSpace X.left)
    (hYqc : CompactSpace Y.left) (hYqs : QuasiSeparatedSpace Y.left)
    (hX : LocallyOfFinitePresentation X.hom) (hY : LocallyOfFinitePresentation Y.hom)
    (u : X ⟶ Y) (v : Y ⟶ X)
    (huv : (Over.pullback (c.π.app (.op k))).map (u ≫ v) =
      (Over.pullback (c.π.app (.op k))).map (𝟙 _))
    (hvu : (Over.pullback (c.π.app (.op k))).map (v ≫ u) =
      (Over.pullback (c.π.app (.op k))).map (𝟙 _)) :
    ∃ (m : I) (hkm : k ≤ m), IsIso ((Over.pullback (D.map (homOfLE hkm).op)).map u) := by
  obtain ⟨m₁, hkm₁, hA₁⟩ := eventually_eq_of_baseChange_eq_of_small D c hc k X X
    hXqc hXqs hXqc hXqs hX hX _ _ huv
  obtain ⟨m₂, hkm₂, hB₁⟩ := eventually_eq_of_baseChange_eq_of_small D c hc k Y Y
    hYqc hYqs hYqc hYqs hY hY _ _ hvu
  obtain ⟨m, hm₁, hm₂⟩ := directed_of (· ≤ ·) m₁ m₂
  have hkm : k ≤ m := hkm₁.trans hm₁
  have lift : ∀ {m₀ : I} (hkm₀ : k ≤ m₀) (hm₀ : m₀ ≤ m) {P Q : Over (D.obj (.op k))}
      (a b : P ⟶ Q),
      (Over.pullback (D.map (homOfLE hkm₀).op)).map a =
        (Over.pullback (D.map (homOfLE hkm₀).op)).map b →
      (Over.pullback (D.map (homOfLE hkm).op)).map a =
        (Over.pullback (D.map (homOfLE hkm).op)).map b := by
    intro _ hkm₀ hm₀ _ _ _ _ h
    exact overPullback_map_eq_of_comp_eq (D.map (homOfLE hkm₀).op) (D.map (homOfLE hm₀).op)
      (D.map (homOfLE hkm).op) (map_homOfLE_op_comp D hkm₀ hm₀) _ _ (congrArg _ h)
  have hA := lift hkm₁ hm₁ _ _ hA₁
  have hB := lift hkm₂ hm₂ _ _ hB₁
  exact ⟨m, hkm, ⟨⟨(Over.pullback (D.map (homOfLE hkm).op)).map v,
    by rw [← Functor.map_comp, hA, CategoryTheory.Functor.map_id],
    by rw [← Functor.map_comp, hB, CategoryTheory.Functor.map_id]⟩⟩⟩

/-- **Stacks Tag 081E over arbitrary stages**, under the extra hypothesis `Small.{u} I`.

Let `S = lim Sᵢ` be a directed inverse limit of schemes with affine transition morphisms —
nothing is assumed of the stages — let `X`, `Y` be quasi-compact, quasi-separated schemes locally
of finite presentation over a stage `Sᵢ`, and let `g : X ⟶ Y` be a morphism over `Sᵢ` whose base
change to `S` is an isomorphism.  Then the base change of `g` to some later stage is already an
isomorphism.

This is assembled from the two halves of Stacks Tag 0EY1: fullness descends the inverse, and
faithfulness turns the two identities it must satisfy over the limit into identities over a later
stage. -/
@[ega "IV 8.8.2.4" "necessity, special case", sga "3 VIB 10.1" "Direction, partial"]
private lemma exists_isIso_baseChange_of_isIso_limit (hc : IsLimit c) (i : I)
    (X Y : Over (D.obj (.op i)))
    (hXqc : CompactSpace X.left) (hXqs : QuasiSeparatedSpace X.left)
    (hYqc : CompactSpace Y.left) (hYqs : QuasiSeparatedSpace Y.left)
    (hX : LocallyOfFinitePresentation X.hom) (hY : LocallyOfFinitePresentation Y.hom)
    (g : X ⟶ Y) (hg : IsIso ((Over.pullback (c.π.app (.op i))).map g)) :
    ∃ (m : I) (him : i ≤ m), IsIso ((Over.pullback (D.map (homOfLE him).op)).map g) := by
  have := hg
  -- Descend the inverse of the base change of `g` to a morphism `g'` over a stage `k`.
  obtain ⟨k, hik, g', α, β, hα, hβ, hrel⟩ := exists_morphism_after_baseChange_of_small D c hc i
    Y X hYqc hYqs hXqc hXqs hY hX (inv ((Over.pullback (c.π.app (.op i))).map g))
  have hw : c.π.app (.op k) ≫ D.map (homOfLE hik).op = c.π.app (.op i) := c.w _
  -- The comparison isomorphisms fullness returns are the canonical ones.
  rw [iso_eq_overPullbackCompIso _ _ _ hw Y α hα,
    iso_eq_overPullbackCompIso _ _ _ hw X β hβ] at hrel
  -- The two base changes to the limit, in terms of the canonical comparison isomorphisms.
  have hbck := (Iso.inv_comp_eq _).1 (overPullbackCompIso_inv_naturality _ _ _ hw g)
  have hbcg' := (Iso.eq_comp_inv _).2 hrel.symm
  -- Over the limit the two composites are the identity.
  have hlim : (Over.pullback (c.π.app (.op k))).map
        ((Over.pullback (D.map (homOfLE hik).op)).map g ≫ g') =
      (Over.pullback (c.π.app (.op k))).map (𝟙 _) ∧
      (Over.pullback (c.π.app (.op k))).map
        (g' ≫ (Over.pullback (D.map (homOfLE hik).op)).map g) =
      (Over.pullback (c.π.app (.op k))).map (𝟙 _) := by
    constructor <;> (rw [Functor.map_comp, hbck, hbcg']; simp)
  -- Faithfulness turns each identity over the limit into one over a later stage.
  obtain ⟨m, hkm, hmid⟩ := exists_isIso_baseChange_of_comp_eq_id_limit D c hc k
    ((Over.pullback (D.map (homOfLE hik).op)).obj X)
    ((Over.pullback (D.map (homOfLE hik).op)).obj Y)
    (compactSpace_overPullback_left _ X hXqc) (quasiSeparatedSpace_overPullback_left _ X hXqs)
    (compactSpace_overPullback_left _ Y hYqc) (quasiSeparatedSpace_overPullback_left _ Y hYqs)
    (locallyOfFinitePresentation_overPullback_hom _ X hX)
    (locallyOfFinitePresentation_overPullback_hom _ Y hY) _ g' hlim.1 hlim.2
  exact ⟨m, hik.trans hkm, isIso_overPullback_map_of_isIso_comp (D.map (homOfLE hik).op)
    (D.map (homOfLE hkm).op) (D.map (homOfLE (hik.trans hkm)).op)
    (map_homOfLE_op_comp D hik hkm) g hmid⟩

/-- **Two models over one arbitrary stage of the same scheme over the limit become isomorphic
over a later stage**, in the `CategoryTheory.Over` idiom and under the extra hypothesis
`Small.{u} I`.

Let `S = lim Sᵢ` be a directed inverse limit of schemes with affine transition morphisms —
nothing is assumed of the stages — and let `XA`, `XB` be quasi-compact, quasi-separated schemes
locally of finite presentation over a stage `Sᵢ` whose base changes to `S` are both identified
with a fixed scheme `Z` over `S`.  Then the base changes of `XA` and `XB` to some later stage are
isomorphic, by an isomorphism compatible with the two identifications, and the identifications at
the later stage induce the given ones through the first pullback projections.

This is the arbitrary-stage form of
`AlgebraicGeometry.exists_iso_of_isPullback_of_isPullback`'s over-categorical ingredient. -/
@[ega "IV 8.8.2.5" "more general", sga "4 VII 5.2" "a, special case"]
public theorem exists_iso_over_after_baseChange_of_small (hc : IsLimit c) (i : I)
    (XA XB : Over (D.obj (.op i)))
    (hAqc : CompactSpace XA.left) (hAqs : QuasiSeparatedSpace XA.left)
    (hBqc : CompactSpace XB.left) (hBqs : QuasiSeparatedSpace XB.left)
    (hA : LocallyOfFinitePresentation XA.hom) (hB : LocallyOfFinitePresentation XB.hom)
    {Z : Scheme.{u}} (fZ : Z ⟶ c.pt)
    (eA : Over.mk fZ ≅ (Over.pullback (c.π.app (.op i))).obj XA)
    (eB : Over.mk fZ ≅ (Over.pullback (c.π.app (.op i))).obj XB) :
    ∃ (m : I) (him : i ≤ m)
      (ψ : (Over.pullback (D.map (homOfLE him).op)).obj XA ≅
        (Over.pullback (D.map (homOfLE him).op)).obj XB)
      (EA : Over.mk fZ ≅ (Over.pullback (c.π.app (.op m))).obj
        ((Over.pullback (D.map (homOfLE him).op)).obj XA))
      (EB : Over.mk fZ ≅ (Over.pullback (c.π.app (.op m))).obj
        ((Over.pullback (D.map (homOfLE him).op)).obj XB)),
      EA.hom ≫ (Over.pullback (c.π.app (.op m))).map ψ.hom = EB.hom ∧
        EA.hom.left ≫ pullback.fst ((Over.pullback (D.map (homOfLE him).op)).obj XA).hom
              (c.π.app (.op m)) ≫ pullback.fst XA.hom (D.map (homOfLE him).op) =
            eA.hom.left ≫ pullback.fst XA.hom (c.π.app (.op i)) ∧
        EB.hom.left ≫ pullback.fst ((Over.pullback (D.map (homOfLE him).op)).obj XB).hom
              (c.π.app (.op m)) ≫ pullback.fst XB.hom (D.map (homOfLE him).op) =
            eB.hom.left ≫ pullback.fst XB.hom (c.π.app (.op i)) := by
  -- Descend the composite identification to a morphism over a stage `j`.
  obtain ⟨j, hij, g, α, β, hα, hβ, hg⟩ := exists_morphism_after_baseChange_of_small D c hc i
    XA XB hAqc hAqs hBqc hBqs hA hB (eA.symm ≪≫ eB).hom
  have hbcg : (Over.pullback (c.π.app (.op j))).map g = α.hom ≫ eA.inv ≫ eB.hom ≫ β.inv := by
    have h0 : α.hom ≫ eA.inv ≫ eB.hom = (Over.pullback (c.π.app (.op j))).map g ≫ β.hom := by
      simpa only [Iso.trans_hom, Iso.symm_hom] using hg
    exact ((Iso.eq_comp_inv β).2 h0.symm).trans (by simp only [Category.assoc])
  have hIsoBc : IsIso ((Over.pullback (c.π.app (.op j))).map g) := by
    rw [hbcg]
    infer_instance
  -- The hypotheses over the stage `j`.
  have hAqc' := compactSpace_overPullback_left (D.map (homOfLE hij).op) XA hAqc
  have hAqs' := quasiSeparatedSpace_overPullback_left (D.map (homOfLE hij).op) XA hAqs
  have hA' := locallyOfFinitePresentation_overPullback_hom (D.map (homOfLE hij).op) XA hA
  have hBqc' := compactSpace_overPullback_left (D.map (homOfLE hij).op) XB hBqc
  have hBqs' := quasiSeparatedSpace_overPullback_left (D.map (homOfLE hij).op) XB hBqs
  have hB' := locallyOfFinitePresentation_overPullback_hom (D.map (homOfLE hij).op) XB hB
  -- The descended morphism becomes an isomorphism over a stage `m`.
  obtain ⟨m, hjm, hmiso⟩ := exists_isIso_baseChange_of_isIso_limit D c hc j
    ((Over.pullback (D.map (homOfLE hij).op)).obj XA)
    ((Over.pullback (D.map (homOfLE hij).op)).obj XB)
    hAqc' hAqs' hBqc' hBqs' hA' hB' g hIsoBc
  have := hmiso
  -- The comparison isomorphisms between the iterated and the direct base changes.
  set α₂ := overPullbackCompIso (D.map (homOfLE hjm).op) (c.π.app (.op m))
    (c.π.app (.op j)) (c.w _) ((Over.pullback (D.map (homOfLE hij).op)).obj XA) with hα₂
  set β₂ := overPullbackCompIso (D.map (homOfLE hjm).op) (c.π.app (.op m))
    (c.π.app (.op j)) (c.w _) ((Over.pullback (D.map (homOfLE hij).op)).obj XB) with hβ₂
  set γA := overPullbackCompIso (D.map (homOfLE hij).op) (D.map (homOfLE hjm).op)
    (D.map (homOfLE (hij.trans hjm)).op) (map_homOfLE_op_comp D hij hjm) XA with hγA
  set γB := overPullbackCompIso (D.map (homOfLE hij).op) (D.map (homOfLE hjm).op)
    (D.map (homOfLE (hij.trans hjm)).op) (map_homOfLE_op_comp D hij hjm) XB with hγB
  have hnat' : α₂.inv ≫ (Over.pullback (c.π.app (.op m))).map
        ((Over.pullback (D.map (homOfLE hjm).op)).map g) =
      (Over.pullback (c.π.app (.op j))).map g ≫ β₂.inv :=
    overPullbackCompIso_inv_naturality _ _ _ _ g
  refine ⟨m, hij.trans hjm,
    γA.symm ≪≫ asIso ((Over.pullback (D.map (homOfLE hjm).op)).map g) ≪≫ γB,
    eA ≪≫ α.symm ≪≫ α₂.symm ≪≫ (Over.pullback (c.π.app (.op m))).mapIso γA,
    eB ≪≫ β.symm ≪≫ β₂.symm ≪≫ (Over.pullback (c.π.app (.op m))).mapIso γB, ?_, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Functor.mapIso_hom, Functor.map_comp,
      Category.assoc, Iso.hom_inv_id_map_assoc]
    rw [reassoc_of% hnat', hbcg]
    simp
  · exact overPullback_presentation_fst D c hij hjm XA eA α hα
  · exact overPullback_presentation_fst D c hij hjm XB eB β hβ

/-- **Two models over one arbitrary stage of the same scheme over the limit become isomorphic
over a later stage**, as pullback squares and under the extra hypothesis `Small.{u} I`.

Let `S = lim Sᵢ` be a directed inverse limit of schemes with affine transition morphisms —
nothing is assumed of the stages — and let `Z` over `S` be presented in two ways as the base
change of a quasi-compact, quasi-separated scheme locally of finite presentation over a stage
`Sᵢ`.  Then after replacing `Sᵢ` by a later stage `S_m` and both models by their base changes to
`S_m` — which are again quasi-compact, quasi-separated and locally of finite presentation over
`S_m` — the two models are isomorphic over `S_m`, compatibly with the two presentations of `Z`.

This is the arbitrary-stage replacement for
`AlgebraicGeometry.exists_iso_of_isPullback_of_isPullback`, whose hypotheses
`CompactSpace (D.obj i)`, `QuasiSeparatedSpace (D.obj i)` and finite presentation of both models
are all gone; it is the form a glueing induction over
`AlgebraicGeometry.LimitDescent.HasQcqsModel'` consumes. -/
@[ega "IV 8.8.2.5" "more general", sga "3 VIB 10.0" "(i), special case"]
public theorem exists_iso_of_isPullback_of_isPullback_of_small (hc : IsLimit c) (i : I)
    {YA YB Z : Scheme.{u}} {pA : YA ⟶ D.obj (.op i)} {pB : YB ⟶ D.obj (.op i)}
    (hAqc : CompactSpace YA) (hAqs : QuasiSeparatedSpace YA)
    (hBqc : CompactSpace YB) (hBqs : QuasiSeparatedSpace YB)
    (hpA : LocallyOfFinitePresentation pA) (hpB : LocallyOfFinitePresentation pB)
    {fZ : Z ⟶ c.pt} {gA : Z ⟶ YA} {gB : Z ⟶ YB}
    (hA : IsPullback gA fZ pA (c.π.app (.op i)))
    (hB : IsPullback gB fZ pB (c.π.app (.op i))) :
    ∃ (m : I) (him : i ≤ m) (YA' YB' : Scheme.{u}) (pA' : YA' ⟶ D.obj (.op m))
      (pB' : YB' ⟶ D.obj (.op m)) (rA : YA' ⟶ YA) (rB : YB' ⟶ YB) (gA' : Z ⟶ YA')
      (gB' : Z ⟶ YB') (φ : YA' ≅ YB'),
      CompactSpace YA' ∧ QuasiSeparatedSpace YA' ∧ LocallyOfFinitePresentation pA' ∧
      CompactSpace YB' ∧ QuasiSeparatedSpace YB' ∧ LocallyOfFinitePresentation pB' ∧
      IsPullback rA pA' pA (D.map (homOfLE him).op) ∧
      IsPullback rB pB' pB (D.map (homOfLE him).op) ∧
      IsPullback gA' fZ pA' (c.π.app (.op m)) ∧ IsPullback gB' fZ pB' (c.π.app (.op m)) ∧
      φ.hom ≫ pB' = pA' ∧ gA' ≫ φ.hom = gB' ∧ gA' ≫ rA = gA ∧ gB' ≫ rB = gB := by
  obtain ⟨m, him, ψ, EA, EB, hkey, hfA, hfB⟩ := exists_iso_over_after_baseChange_of_small D c hc i
    (Over.mk pA) (Over.mk pB) hAqc hAqs hBqc hBqs hpA hpB fZ
    (Over.isoMk hA.isoPullback (by simp))
    (Over.isoMk hB.isoPullback (by simp))
  refine ⟨m, him, _, _, _, _, pullback.fst pA (D.map (homOfLE him).op),
    pullback.fst pB (D.map (homOfLE him).op),
    EA.hom.left ≫ pullback.fst ((Over.pullback (D.map (homOfLE him).op)).obj
      (Over.mk pA)).hom (c.π.app (.op m)),
    EB.hom.left ≫ pullback.fst ((Over.pullback (D.map (homOfLE him).op)).obj
      (Over.mk pB)).hom (c.π.app (.op m)),
    (Over.forget (D.obj (.op m))).mapIso ψ,
    compactSpace_overPullback_left (D.map (homOfLE him).op) (Over.mk pA) hAqc,
    quasiSeparatedSpace_overPullback_left (D.map (homOfLE him).op) (Over.mk pA) hAqs,
    locallyOfFinitePresentation_overPullback_hom (D.map (homOfLE him).op) (Over.mk pA) hpA,
    compactSpace_overPullback_left (D.map (homOfLE him).op) (Over.mk pB) hBqc,
    quasiSeparatedSpace_overPullback_left (D.map (homOfLE him).op) (Over.mk pB) hBqs,
    locallyOfFinitePresentation_overPullback_hom (D.map (homOfLE him).op) (Over.mk pB) hpB,
    IsPullback.of_hasPullback pA (D.map (homOfLE him).op),
    IsPullback.of_hasPullback pB (D.map (homOfLE him).op),
    isPullback_left_fst_of_overIso _ EA, isPullback_left_fst_of_overIso _ EB, Over.w ψ.hom,
    left_fst_comp_of_overIso_eq ψ EA EB hkey, ?_, ?_⟩
  · refine (Category.assoc _ _ _).trans (hfA.trans ?_)
    simp
  · refine (Category.assoc _ _ _).trans (hfB.trans ?_)
    simp

end AlgebraicGeometry.LimitDescent
