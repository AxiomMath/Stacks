module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.Epi.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Size.Pullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties

/-!
# Points of an algebraic space represented by a monomorphism

A field-valued point of an algebraic space over `S` is a monomorphism when the morphism it
defines from the Yoneda presheaf of its field spectrum is a monomorphism of presheaves.
Such a representative is terminal in its equivalence class: every other representative of
the same point factors through it, uniquely. Consequently two monomorphic representatives
of one point are isomorphic over the space.

## Main results

* `AlgebraicGeometry.Space.FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono`: the
  unique factorization through a monomorphic representative.
* `AlgebraicGeometry.Space.iso_of_mono_of_point_eq`: two monomorphic representatives of the
  same point are isomorphic over the algebraic space.

## Implementation notes

A field-valued point is a section of the presheaf over the object of the site determined by
its field spectrum, hence a morphism out of that object's Yoneda presheaf by
`CategoryTheory.yonedaEquiv`; an isomorphism over the algebraic space is an isomorphism of
those objects of the site carrying one section to the other.

The factorization is produced from the representable diagonal of the algebraic space: the
monomorphic representative `p` is a representable morphism, so its fibre product with any
other representative `q` is again represented by an object of the site, and the projection
to `q` is a monomorphism of schemes with target the spectrum of a field. A monomorphism
into the spectrum of a field out of a nonempty scheme is an isomorphism — this is the
private lemma below, which argues on global sections, where a monomorphism of affine
schemes is an epimorphism of rings and an epimorphism from a field is surjective. The
common extension supplied by equality of the two points is what makes the fibre product
nonempty.

## References

* [Stacks Project, Tag 03E1](https://stacks.math.columbia.edu/tag/03E1)
* [Stacks Project, Tag 0H2X](https://stacks.math.columbia.edu/tag/0H2X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0H2X.** Two representatives of the same point factor uniquely through a
representative whose map to the algebraic space is a monomorphism. -/
@[stacks 0H2X]
theorem FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)
    (p q : FieldValuedPoint B S hS F)
    [Mono (yonedaEquiv.symm p.value)]
    (h : p.class B S hS F = q.class B S hS F) :
    ∃! f : q.siteObject B S hS F ⟶ p.siteObject B S hS F,
      F.map f.op p.value = q.value := by
  classical
  let C := BigFppfOver B S hS
  let T := BigFppfOver.toScheme B S hS
  let _ : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
  let Pobj := p.siteObject B S hS F
  let Qobj := q.siteObject B S hS F
  let α : yoneda.obj Pobj ⟶ F := yonedaEquiv.symm p.value
  let β : yoneda.obj Qobj ⟶ F := yonedaEquiv.symm q.value
  have hα : yoneda.relativelyRepresentable α :=
    (Functor.relativelyRepresentable.diag_iff).1 hF.diagonal_representable α
  let a : hα.pullback β ⟶ Pobj := hα.fst' β
  let b : hα.pullback β ⟶ Qobj := hα.snd β
  have hpull : IsPullback (yoneda.map a) (yoneda.map b) α β := hα.isPullback' β
  obtain ⟨r, ⟨rp, hrpval⟩, ⟨rq, hrqval⟩⟩ := (FieldValuedPoint.class_eq_class_iff
    (B := B) (S := S) (hS := hS) (F := F) p q).1 h
  have hcomm : yoneda.map rp ≫ α = yoneda.map rq ≫ β := by
    simp only [α, β, yonedaEquiv_symm_naturality_left, hrpval, hrqval]
  let w : r.siteObject B S hS F ⟶ hα.pullback β := hα.lift (yoneda.map rp) rq hcomm
  have : Mono α := inferInstance
  have : Mono (yoneda.map b) := hpull.mono_snd_of_mono
  have : Mono b := yoneda.mono_of_mono_map (by infer_instance)
  have : Mono (T.map b) := Functor.map_mono T b
  have hW : Nonempty (T.obj (hα.pullback β)) :=
    ⟨T.map w ⟨IsLocalRing.closedPoint r.carrier,
      (IsLocalRing.closedPoint r.carrier).isPrime⟩⟩
  have : IsIso (T.map b) := isIso_of_mono_to_spec_field (T.map b)
  have : IsIso b := isIso_of_reflects_iso b T
  let f : Qobj ⟶ Pobj := inv b ≫ a
  have hfact : yoneda.map f ≫ α = β := by
    dsimp only [f]
    rw [yoneda.map_comp, Category.assoc, hpull.w, ← Category.assoc, ← yoneda.map_comp,
      IsIso.inv_hom_id, yoneda.map_id]
    simp
  have hiff (g : Qobj ⟶ Pobj) : yoneda.map g ≫ α = β ↔ F.map g.op p.value = q.value := by
    simp only [α, β, yonedaEquiv_symm_naturality_left, EmbeddingLike.apply_eq_iff_eq]
  exact ⟨f, (hiff f).1 hfact, fun g hg ↦
    yoneda.map_injective ((cancel_mono α).1 (((hiff g).2 hg).trans hfact.symm))⟩

/-- **Stacks 03E1.** Monomorphic field-valued representatives of the same point are
isomorphic over the algebraic space. -/
@[stacks 03E1]
theorem iso_of_mono_of_point_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)
    (p q : FieldValuedPoint B S hS F)
    [Mono (yonedaEquiv.symm p.value)] [Mono (yonedaEquiv.symm q.value)]
    (heq : p.class B S hS F = q.class B S hS F) :
    ∃ e : p.siteObject B S hS F ≅ q.siteObject B S hS F,
      F.map e.hom.op q.value = p.value := by
  let unique := FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono
  obtain ⟨f, hf, _⟩ := unique B S hS F hF q p (by simpa using heq.symm)
  obtain ⟨g, hg, _⟩ := unique B S hS F hF p q heq
  obtain ⟨_, _, hp⟩ := unique B S hS F hF p p rfl
  obtain ⟨_, _, hq⟩ := unique B S hS F hF q q rfl
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · exact (hp _ (by simp [Functor.map_comp, hf, hg])).trans (hp _ (by simp)).symm
  · exact (hq _ (by simp [Functor.map_comp, hf, hg])).trans (hq _ (by simp)).symm

end AlgebraicGeometry.Space

end
