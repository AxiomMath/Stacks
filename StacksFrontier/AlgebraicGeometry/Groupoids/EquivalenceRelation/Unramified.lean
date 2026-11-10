module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties

/-!
# Unramified pre-relations with equivalence operations are equivalence relations

Let `j : R ⟶ U ×_S U` be a pre-relation whose source and target maps are unramified.  Suppose
that on points valued in an algebraically closed field the induced relation is an equivalence
relation and `j` is injective, and that reflexivity, symmetry and transitivity are witnessed by
morphisms of schemes.  Then `j` is an internal equivalence relation.

Monicity of `j` is the substance: the diagonal of `j` is an open immersion because `j` itself is
unramified, and it is surjective because two points of `R` valued in an algebraically closed
field with the same image under `j` coincide.  An open immersion that is surjective is an
isomorphism, and a morphism whose diagonal is an isomorphism is monic.  The pointwise
equivalence conditions then come straight from the three given morphisms.

## Main results

* `AlgebraicGeometry.isEquivalenceRelation_of_unramified`: such a pre-relation is an internal
  equivalence relation.

## Implementation notes

The three commutative diagrams of the source are stated componentwise through the two
projections of the pre-relation, and the domain of the composition morphism is the categorical
pullback of the source and target maps in schemes over the base.

## References

* [Stacks Project, Tag 0DT7](https://stacks.math.columbia.edu/tag/0DT7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- If two field-valued points of the source of a morphism of `S`-schemes with the same image
agree, for every algebraically closed field, then the diagonal of the morphism is
surjective. -/
private theorem diagonal_surjective_of_field_injective
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (hfield : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (p : Spec (.of k) ⟶ S),
      Function.Injective (fun r : Over.mk p ⟶ X ↦ r ≫ f)) :
    Surjective (pullback.diagonal f.left) := by
  apply (surjective_iff (pullback.diagonal f.left)).2
  intro q
  let P := pullback.diagonalObj f.left
  let k := AlgebraicClosure (P.residueField q)
  let g : Spec (.of k) ⟶ P :=
    Spec.map (CommRingCat.ofHom (algebraMap (P.residueField q) k)) ≫ P.fromSpecResidueField q
  let p : Spec (.of k) ⟶ S := g ≫ pullback.fst f.left f.left ≫ X.hom
  let r₁ : Over.mk p ⟶ X := Over.homMk (g ≫ pullback.fst f.left f.left)
    (by simp [p])
  let r₂ : Over.mk p ⟶ X := Over.homMk (g ≫ pullback.snd f.left f.left) (by
    change (g ≫ pullback.snd f.left f.left) ≫ X.hom =
      g ≫ pullback.fst f.left f.left ≫ X.hom
    rw [← Over.w f]
    simpa using
      (congrArg (fun z => g ≫ z ≫ Y.hom) pullback.condition).symm)
  have hcomp : r₁ ≫ f = r₂ ≫ f :=
    Over.OverMorphism.ext (congrArg (g ≫ ·) pullback.condition)
  have hlegs : g ≫ pullback.fst f.left f.left =
      g ≫ pullback.snd f.left f.left := congrArg Over.Hom.left (hfield k p hcomp)
  have hg : g = (g ≫ pullback.fst f.left f.left) ≫ pullback.diagonal f.left := by
    apply pullback.hom_ext
    · simp
    · simpa [pullback.diagonal_snd] using hlegs.symm
  refine ⟨(g ≫ pullback.fst f.left f.left) default, ?_⟩
  change ((g ≫ pullback.fst f.left f.left) ≫ pullback.diagonal f.left) default = q
  rw [← hg, Scheme.Hom.comp_apply]
  exact P.fromSpecResidueField_apply q _

/-- **Stacks Project, Tag 0DT7.** An unramified pre-relation which is an equivalence relation on
points over every algebraically closed field, and whose reflexivity, symmetry, and composition
operations are represented by morphisms, is an equivalence relation. -/
@[stacks 0DT7]
theorem isEquivalenceRelation_of_unramified
    {S : Scheme.{u}} {R U : Over S} (j : PreRelation R U)
    [Unramified j.source.left] [Unramified j.target.left]
    (hpoints : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (p : Spec (.of k) ⟶ S),
      (Function.Injective (fun r : Over.mk p ⟶ R ↦ r ≫ j) ∧
        Equivalence (j.Rel (T := Over.mk p))))
    (e : U ⟶ R)
    (he_target : e ≫ j.target = 𝟙 U)
    (he_source : e ≫ j.source = 𝟙 U)
    (i : R ⟶ R)
    (hi_target : i ≫ j.target = j.source)
    (hi_source : i ≫ j.source = j.target)
    (c : pullback j.source j.target ⟶ R)
    (hc_target : c ≫ j.target = pullback.fst j.source j.target ≫ j.target)
    (hc_source : c ≫ j.source = pullback.snd j.source j.target ≫ j.source) :
    IsEquivalenceRelation j.target j.source := by
  rw [isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation]
  constructor
  · have : Unramified j.left := unramified_of_comp j.left (prod.fst : U ⨯ U ⟶ U).left
    have : IsOpenImmersion (pullback.diagonal j.left) :=
      Unramified.isOpenImmersion_diagonal j.left
    have : Surjective (pullback.diagonal j.left) :=
      diagonal_surjective_of_field_injective j (fun k _ _ p => (hpoints k p).1)
    have : Mono j.left := (pullback.isIso_diagonal_iff j.left).1 <|
      (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, inferInstance⟩
    exact Over.mono_of_mono_left j
  · intro T
    constructor
    · intro x
      exact ⟨x ≫ e, by simp [he_target], by simp [he_source]⟩
    · rintro x y ⟨r, hr₁, hr₂⟩
      exact ⟨r ≫ i, by simpa [hi_target] using hr₂,
        by simpa [hi_source] using hr₁⟩
    · rintro x y z ⟨r, hr₁, hr₂⟩ ⟨s, hs₁, hs₂⟩
      refine ⟨pullback.lift r s (hr₂.trans hs₁.symm) ≫ c, ?_, ?_⟩
      · rw [Category.assoc, hc_target, ← Category.assoc, pullback.lift_fst, hr₁]
      · rw [Category.assoc, hc_source, ← Category.assoc, pullback.lift_snd, hs₂]

end AlgebraicGeometry

end
