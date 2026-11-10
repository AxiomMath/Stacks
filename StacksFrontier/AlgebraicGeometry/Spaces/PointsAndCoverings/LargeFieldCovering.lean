module

public import Mathlib.FieldTheory.MvRatFunc.Rank
public import Mathlib.RingTheory.Localization.Cardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative

/-!
# Geometric points over large algebraically closed fields cover the point set

Let `X` and `Y` be algebraic spaces over a scheme `S`. Every point of `Y` is represented by a
geometric point, and one may moreover insist that the algebraically closed field of that
geometric point be at least as large as the cardinal `λ` of a scheme atlas of `Y` and strictly
larger than the cardinal `λ` of a scheme atlas of `X`.

## Main definitions

* `AlgebraicGeometry.Scheme.lambdaCard` is the cardinal `λ(T) = sup {ℵ₀, |κ(t)| ; t ∈ T}`
  attached to a scheme `T` in Stacks 0488. For an algebraic space `X` the source sets
  `λ(X) = λ(U)` for a scheme `U` with a surjective étale morphism `U → X`; here the atlas is
  carried along as an explicit parameter, so the statements apply to any chosen atlas.

## Main results

* `AlgebraicGeometry.Space.exists_geometricPoint_liesOver_of_lambdaCard` is Stacks 0488
  part (2): geometric points cover the point set, with two cardinal bounds imposed on the
  field.

## Implementation notes

Part (1) of the source carries the tag on
`AlgebraicGeometry.Space.exists_geometricRepresentative`, which produces the algebraic closure
of an arbitrary field-valued representative. For part (2) that field has to be enlarged.
Rather than the source's appeal to the existence of an algebraically closed extension of any
prescribed cardinality, a concrete such extension is used: the algebraic
closure of the fraction field of a polynomial ring in `ν` variables over the given field has
cardinality exactly `ν` whenever `ν` is an uncountable cardinal above the cardinality of the
field.

The set-theoretic paragraph of the source — that the enlarged field spectrum is still an
object of the site — is the inequality `ν < B.cutoff`. It holds because `λ` of an object of
the site is bounded by the size of that object, hence lies below the cutoff, and the cutoff is
a strong prelimit, hence closed under the successor-of-a-power step taken here.

## References

* [Stacks Project, Tag 0488](https://stacks.math.columbia.edu/tag/0488)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The cardinal `λ(T) = sup {ℵ₀, |κ(t)| ; t ∈ T}` of Stacks 0488: the smallest infinite
cardinal bounding all cardinalities of residue fields of the scheme `T`. -/
noncomputable def Scheme.lambdaCard (T : Scheme.{u}) : Cardinal.{u} :=
  Cardinal.aleph0 ⊔ ⨆ t : T, Cardinal.mk (T.residueField t)

/-- The cardinal `λ(T)` bounds the cardinality of every residue field of `T`. -/
theorem Scheme.mk_residueField_le_lambdaCard (T : Scheme.{u}) (t : T) :
    Cardinal.mk (T.residueField t) ≤ T.lambdaCard :=
  (le_ciSup Cardinal.bddAbove_of_small t).trans le_sup_right

/-- The cardinal `λ(T)` is bounded by the size of `T`: a residue field is a quotient of a
stalk, and the stalks of `T` have cardinality at most `size T`. -/
theorem Scheme.lambdaCard_le_size (T : Scheme.{u}) : T.lambdaCard ≤ T.size :=
  sup_le T.aleph0_le_size <| ciSup_le' fun t =>
    (Cardinal.mk_le_of_surjective (T.residue_surjective t)).trans (T.mk_stalk_le_size t)

namespace Space

/-- Every point of a presheaf has a geometric representative whose field is above two
prescribed cardinals, strictly above the first, provided both lie below the cutoff of the
site.

This is the cardinality-free heart of Stacks 0488 part (2): the two bounds enter only through
the enlargement of the field of an arbitrary geometric representative. -/
private theorem exists_geometricPoint_above_cardinals
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (α β : Cardinal.{u}) (hα : α < B.cutoff) (hβ : β < B.cutoff)
    (y : points B S hS F) :
    ∃ p : GeometricPoint B S hS F,
      p.LiesOver y ∧ β ≤ Cardinal.mk p.val.carrier ∧ α < Cardinal.mk p.val.carrier := by
  obtain ⟨p₀, hp₀⟩ := exists_geometricRepresentative B S hS F y
  let κ := max (max (max Cardinal.aleph0 α) β) (Cardinal.mk p₀.val.carrier)
  let ν := Order.succ κ
  let ι := ν.ord.ToType
  let L := AlgebraicClosure (FractionRing (MvPolynomial ι p₀.val.carrier))
  have hκaleph : Cardinal.aleph0 ≤ κ := by simp [κ]
  have hακ : α ≤ κ := by simp [κ]
  have hβκ : β ≤ κ := by simp [κ]
  have hk : Cardinal.mk p₀.val.carrier < B.cutoff := by
    have h : (Spec (.of p₀.val.carrier)).size < B.cutoff := p₀.val.contained
    rw [Scheme.size_Spec] at h
    exact (le_max_right _ _).trans_lt h
  have hκ : κ < B.cutoff :=
    max_lt (max_lt (max_lt B.aleph0_lt_cutoff hα) hβ) hk
  have hν : ν < B.cutoff :=
    (Order.succ_le_of_lt (Cardinal.cantor κ)).trans_lt (B.cutoff_isStrongPrelimit hκ)
  have hνpos : Cardinal.aleph0 ≤ ν := hκaleph.trans (Order.le_succ κ)
  have hLcard : Cardinal.mk L ≤ ν := by
    have hfrac : Cardinal.mk (FractionRing (MvPolynomial ι p₀.val.carrier)) ≤ ν := by
      rw [FractionRing.cardinalMk]
      refine MvPolynomial.cardinalMk_le_max.trans ?_
      rw [Cardinal.mk_ord_toType]
      exact max_le (max_le ((le_max_right _ _).trans (Order.le_succ κ)) le_rfl) hνpos
    exact (Algebra.IsAlgebraic.cardinalMk_le_max _ _).trans (max_le hfrac hνpos)
  have hνleL : ν ≤ Cardinal.mk L := by
    let R := MvPolynomial ι p₀.val.carrier
    let K := FractionRing R
    have hf : Function.Injective fun i : ι =>
        algebraMap K (AlgebraicClosure K) (algebraMap R K (MvPolynomial.X i)) := fun i j hij =>
      MvPolynomial.X_injective
        (IsFractionRing.injective R K ((algebraMap K (AlgebraicClosure K)).injective hij))
    simpa [ι] using Cardinal.mk_le_of_injective hf
  have hlargeβ : β ≤ Cardinal.mk L := (hβκ.trans (Order.le_succ κ)).trans hνleL
  have hlargeα : α < Cardinal.mk L := (hακ.trans_lt (Order.lt_succ κ)).trans_le hνleL
  have hLsite : B.Contains (Spec (.of L)) := by
    have hsize : (Spec (.of L)).size ≤ ν := by
      rw [Scheme.size_Spec]
      exact max_le hνpos hLcard
    exact hsize.trans_lt hν
  let g : Spec (.of L) ⟶ Spec (.of p₀.val.carrier) :=
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap p₀.val.carrier L)).op
  let b : Spec (.of L) ⟶ S := g ≫ p₀.val.toBase
  let eOver : Over.mk (⟨b⟩ : B.obj hLsite ⟶ B.obj hS) ⟶ p₀.val.siteObject :=
    Over.homMk (⟨g⟩ : B.obj hLsite ⟶ B.obj p₀.val.contained) (by
      apply B.inclusion.map_injective
      change g ≫ p₀.val.toBase = b
      rfl)
  let q : FieldValuedPoint B S hS F :=
    { carrier := L
      contained := hLsite
      toBase := b
      value := F.map eOver.op p₀.val.value }
  exact ⟨⟨q, inferInstance⟩,
    (FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS F
      ⟨q, FieldValuedPoint.dominates_refl B S hS F q, ⟨eOver, rfl⟩⟩).trans hp₀,
    hlargeβ, hlargeα⟩

/-- **Stacks 0488, part (2).** As `k` ranges over all algebraically closed fields over `S`
with `|k| ≥ λ(Y)` and `|k| > λ(X)` the geometric points `ȳ ∈ Y(k)` cover all of `|Y|`.

Following the source, `λ(X)` and `λ(Y)` are read off from chosen scheme atlases `UX → X` and
`UY → Y`; these are explicit parameters, so the statement applies to any choice. The
algebraic-space hypotheses and the surjectivity and étaleness of the atlases are retained
from the source but are not needed: all that is used of `UX` and `UY` is that they are
objects of the site, whence `λ` of their underlying schemes is below the cutoff. -/
theorem exists_geometricPoint_liesOver_of_lambdaCard
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (_hX : IsAlgebraicSpace B S hS X) (_hY : IsAlgebraicSpace B S hS Y)
    (UX UY : BigFppfOver B S hS)
    (fX : yoneda.obj UX ⟶ X) (fY : yoneda.obj UY ⟶ Y)
    (_hfX_surjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) fX)
    (_hfX_etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) fX)
    (_hfY_surjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) fY)
    (_hfY_etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) fY)
    (y : points B S hS Y) :
    ∃ p : GeometricPoint B S hS Y, p.LiesOver y ∧
      ((BigFppfOver.toScheme B S hS).obj UY).lambdaCard ≤ Cardinal.mk p.val.carrier ∧
      ((BigFppfOver.toScheme B S hS).obj UX).lambdaCard < Cardinal.mk p.val.carrier :=
  exists_geometricPoint_above_cardinals B S hS Y _ _
    ((Scheme.lambdaCard_le_size _).trans_lt UX.left.property)
    ((Scheme.lambdaCard_le_size _).trans_lt UY.left.property) y

end Space

end AlgebraicGeometry

end
