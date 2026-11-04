module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.Examples.GroupSchemes.SectionCover

/-!
# The constant group scheme `(ℤ/2)_S` and its homomorphisms to section covers

The disjoint union `S ⊔ S` with its two coprojections is a section cover of `S` in the sense of
`Stacks.Examples.SectionCoverData`, and its group law multiplies the labels of the two copies
modulo two: it is the constant group scheme `(ℤ/2)_S`. Its structure morphism is finite, hence
proper, and étale.

For any section cover `D` of `S` the morphism `S ⊔ S ⟶ D` sending the copy labelled `b` onto the
chart labelled `b` is a homomorphism of group objects over `S`, and every point of `D` with values
in a field lifts along it, because such a point factors through one of the two charts.

## Main definitions

* `Stacks.Examples.trivialDoubleCover` — `S ⊔ S` as a section cover of `S`.
* `Stacks.Examples.SectionCoverData.fromTrivial` — the morphism `S ⊔ S ⟶ D`.
* `Stacks.Examples.SectionCoverData.overHom` — a morphism of section covers over `S`.

## Main results

* `Stacks.Examples.SectionCoverData.isMonHom_overHom` — a morphism over `S` matching the charts is
  a homomorphism of the group objects.
* `Stacks.Examples.SectionCoverData.exists_comp_fromTrivial_eq` — field-valued points of `D` lift
  along `S ⊔ S ⟶ D`.
* `Stacks.Examples.isFinite_trivialDoubleCover_proj` (the projection is then proper by Mathlib's
  instance for finite morphisms), `etale_trivialDoubleCover_proj`,
  `smooth_trivialDoubleCover_proj` and `locallyOfFinitePresentation_trivialDoubleCover_proj`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Examples

/-- The disjoint union `S ⊔ S`, with its two coprojections as the two sections of the codiagonal:
the constant group scheme `(ℤ/2)_S` as a section cover of `S`. -/
public noncomputable def trivialDoubleCover (S : Scheme.{u}) : SectionCoverData S where
  total := S ⨿ S
  proj := coprod.desc (𝟙 S) (𝟙 S)
  chart b := bif b then coprod.inr else coprod.inl
  chart_comp_proj b := by
    cases b
    · exact coprod.inl_desc (𝟙 S) (𝟙 S)
    · exact coprod.inr_desc (𝟙 S) (𝟙 S)
  isOpenImmersion_chart b := by
    cases b
    · exact inferInstanceAs (IsOpenImmersion (coprod.inl : S ⟶ S ⨿ S))
    · exact inferInstanceAs (IsOpenImmersion (coprod.inr : S ⟶ S ⨿ S))
  exists_chart_eq x := by
    obtain ⟨y, rfl⟩ := (coprodMk S S).surjective x
    cases y with
    | inl y => exact ⟨false, y, (coprodMk_inl S S y).symm⟩
    | inr y => exact ⟨true, y, (coprodMk_inr S S y).symm⟩

/-- The chart labelled `false` of `S ⊔ S` is the left coprojection. -/
public lemma trivialDoubleCover_chart_false (S : Scheme.{u}) :
    (trivialDoubleCover S).chart false = coprod.inl := rfl

/-- The chart labelled `true` of `S ⊔ S` is the right coprojection. -/
public lemma trivialDoubleCover_chart_true (S : Scheme.{u}) :
    (trivialDoubleCover S).chart true = coprod.inr := rfl

/-- The structure morphism of `S ⊔ S` is the codiagonal. -/
public lemma trivialDoubleCover_proj (S : Scheme.{u}) :
    (trivialDoubleCover S).proj = coprod.desc (𝟙 S) (𝟙 S) := rfl

/-- The structure morphism of `S ⊔ S` is finite. -/
public instance isFinite_trivialDoubleCover_proj (S : Scheme.{u}) :
    IsFinite (trivialDoubleCover S).proj :=
  inferInstanceAs (IsFinite (coprod.desc (𝟙 S) (𝟙 S)))

/-- The structure morphism of `S ⊔ S` is étale. -/
public theorem etale_trivialDoubleCover_proj (S : Scheme.{u}) :
    Etale (trivialDoubleCover S).proj :=
  (trivialDoubleCover S).proj_prop _
    (HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)) inferInstance

/-- The structure morphism of `S ⊔ S` is smooth. -/
public theorem smooth_trivialDoubleCover_proj (S : Scheme.{u}) :
    Smooth (trivialDoubleCover S).proj :=
  (trivialDoubleCover S).proj_prop _
    (HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth)) inferInstance

/-- The structure morphism of `S ⊔ S` is locally of finite presentation. -/
public theorem locallyOfFinitePresentation_trivialDoubleCover_proj (S : Scheme.{u}) :
    LocallyOfFinitePresentation (trivialDoubleCover S).proj :=
  (trivialDoubleCover S).proj_prop _
    (HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation))
    inferInstance

namespace SectionCoverData

variable {S : Scheme.{u}}

/-- The morphism `S ⊔ S ⟶ D` sending the copy labelled `b` onto the chart labelled `b`. -/
public noncomputable def fromTrivial (D : SectionCoverData S) :
    (trivialDoubleCover S).total ⟶ D.total :=
  coprod.desc (D.chart false) (D.chart true)

/-- The morphism `S ⊔ S ⟶ D` restricts on the copy labelled `b` to the chart labelled `b`. -/
@[reassoc (attr := simp)]
public lemma chart_comp_fromTrivial (D : SectionCoverData S) (b : Bool) :
    (trivialDoubleCover S).chart b ≫ D.fromTrivial = D.chart b := by
  cases b
  · exact coprod.inl_desc _ _
  · exact coprod.inr_desc _ _

/-- The morphism `S ⊔ S ⟶ D` lies over `S`. -/
@[reassoc (attr := simp)]
public lemma fromTrivial_comp_proj (D : SectionCoverData S) :
    D.fromTrivial ≫ D.proj = (trivialDoubleCover S).proj :=
  coprod.hom_ext
    ((coprod.inl_desc_assoc _ _ _).trans ((D.chart_comp_proj false).trans
      ((trivialDoubleCover S).chart_comp_proj false).symm))
    ((coprod.inr_desc_assoc _ _ _).trans ((D.chart_comp_proj true).trans
      ((trivialDoubleCover S).chart_comp_proj true).symm))

/-- A morphism between the total spaces of two section covers which lies over `S`, as a
morphism of schemes over `S`. -/
public noncomputable def overHom {D D' : SectionCoverData S} (f : D.total ⟶ D'.total)
    (hf : f ≫ D'.proj = D.proj) : D.over ⟶ D'.over :=
  Over.homMk f hf

/-- A morphism over `S` matching the charts carries the section of `D` labelled `b` to the
section of `D'` labelled `b`. -/
public lemma partHom_comp_overHom {D D' : SectionCoverData S} (f : D.total ⟶ D'.total)
    (hf : f ≫ D'.proj = D.proj) (hc : ∀ b, D.chart b ≫ f = D'.chart b) (b : Bool) :
    D.partHom b ≫ overHom f hf = D'.partHom b :=
  Over.OverMorphism.ext (hc b)

private lemma comp_tensorHom_self {T X Y : CategoryTheory.Over S} (x : T ⟶ X ⊗ X) (g : X ⟶ Y) :
    x ≫ (g ⊗ₘ g) = lift (x ≫ fst X X ≫ g) (x ≫ snd X X ≫ g) := by
  ext1 <;> simp

/-- The unit of the group object `D.over` is the section labelled `false`. -/
public lemma grpObj_one (D : SectionCoverData S) :
    (letI := D.grpObj; η[D.over]) = overUnit _ ≫ D.partHom false := rfl

/-- The multiplication of the group object `D.over` is `D.mulHom`. -/
public lemma grpObj_mul (D : SectionCoverData S) :
    (letI := D.grpObj; μ[D.over]) = D.mulHom := rfl

/-- **A morphism of section covers matching the charts is a homomorphism of the group objects.** -/
public theorem isMonHom_overHom {D D' : SectionCoverData S} (f : D.total ⟶ D'.total)
    (hf : f ≫ D'.proj = D.proj) (hc : ∀ b, D.chart b ≫ f = D'.chart b) :
    letI := D.grpObj; letI := D'.grpObj; IsMonHom (overHom f hf) := by
  let := D.grpObj; let := D'.grpObj
  refine ⟨?_, ?_⟩
  · rw [grpObj_one, grpObj_one, Category.assoc, partHom_comp_overHom f hf hc]
  · rw [grpObj_mul, grpObj_mul]
    refine D.over_hom_ext (fst D.over D.over) _ _ fun b V a t hab => ?_
    refine D.over_hom_ext (a ≫ snd D.over D.over) _ _ fun c W a' t' hab' => ?_
    have h₁ : a' ≫ a = lift ((a' ≫ t) ≫ D.partHom b) (t' ≫ D.partHom c) := by
      ext1
      · simp [← hab]
      · simp [← hab']
    simp only [← Category.assoc]
    rw [h₁, D.lift_partHom_comp_mulHom, Category.assoc, partHom_comp_overHom f hf hc,
      comp_tensorHom_self]
    simp only [lift_fst_assoc, lift_snd_assoc, Category.assoc, partHom_comp_overHom f hf hc]
    rw [← Category.assoc a' t, D'.lift_partHom_comp_mulHom]

/-- `S ⊔ S ⟶ D` as a morphism over `S`; it is a homomorphism of the group objects. -/
public noncomputable def fromTrivialOverHom (D : SectionCoverData S) :
    (trivialDoubleCover S).over ⟶ D.over :=
  overHom D.fromTrivial D.fromTrivial_comp_proj

/-- `S ⊔ S ⟶ D` is a homomorphism of group objects over `S`. -/
public theorem isMonHom_fromTrivialOverHom (D : SectionCoverData S) :
    letI := (trivialDoubleCover S).grpObj; letI := D.grpObj; IsMonHom D.fromTrivialOverHom :=
  isMonHom_overHom _ _ D.chart_comp_fromTrivial

/-- A point of a section cover with values in a field factors through one of the charts. -/
public theorem exists_comp_chart_eq (D : SectionCoverData S) (K : Type u) [Field K]
    (h : Spec (.of K) ⟶ D.total) : ∃ (b : Bool) (y : Spec (.of K) ⟶ S), y ≫ D.chart b = h := by
  obtain ⟨b, s, hs⟩ := D.exists_chart_eq (h.base default)
  have := D.isOpenImmersion_chart b
  have hrange : Set.range h ⊆ Set.range (D.chart b) := by
    rintro _ ⟨p, rfl⟩
    exact ⟨s, by rw [Subsingleton.elim p default]; exact hs⟩
  exact ⟨b, IsOpenImmersion.lift (D.chart b) h hrange, IsOpenImmersion.lift_fac _ _ _⟩

/-- **Field-valued points lift along `S ⊔ S ⟶ D`.** -/
public theorem exists_comp_fromTrivial_eq (D : SectionCoverData S) (K : Type u) [Field K]
    (h : Spec (.of K) ⟶ D.total) :
    ∃ z : Spec (.of K) ⟶ (trivialDoubleCover S).total, z ≫ D.fromTrivial = h := by
  obtain ⟨b, y, hy⟩ := D.exists_comp_chart_eq K h
  exact ⟨y ≫ (trivialDoubleCover S).chart b, by rw [Category.assoc, chart_comp_fromTrivial, hy]⟩

end SectionCoverData

end Stacks.Examples

end
