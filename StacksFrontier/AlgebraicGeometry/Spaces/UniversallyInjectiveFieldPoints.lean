module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcChartDescent
public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria

/-!
# Universal injectivity is injectivity on field-valued points

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.
[Stacks Project, Tag 040X] states that the following are equivalent:

1. the map `X(K) → Y(K)` is injective for every field `K` over `S`,
2. for every morphism `Y' ⟶ Y` of algebraic spaces over `S` the induced map
   `|Y' ×_Y X| → |Y'|` is injective, and
3. the diagonal morphism `X ⟶ X ×_Y X` is surjective.

Condition (2) is the definition `AlgebraicGeometry.Space.UniversallyInjective` of
[Stacks Project, Tag 03MV] and condition (3) is surjectivity on points of
`CategoryTheory.Limits.pullback.diagonal`; their equivalence is
`AlgebraicGeometry.Space.universallyInjective_iff_isSurjective_diagonal` of
`StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria`. This file adds condition (1),
as `AlgebraicGeometry.Space.InjectiveOnFieldPoints`, and the two implications relating it to
condition (2), which completes the three-way equivalence.

## Main definitions

* `AlgebraicGeometry.Space.InjectiveOnFieldPoints` is condition (1): the component of the
  morphism at the spectrum of a field over `S` is injective, for every field `K` over `S`.

## Main results

* `AlgebraicGeometry.Space.universallyInjective_of_injectiveOnFieldPoints` is the implication
  (1) ⇒ (2) and `AlgebraicGeometry.Space.injectiveOnFieldPoints_of_universallyInjective` is
  the implication (2) ⇒ (1) of [Stacks Project, Tag 040X];
  `AlgebraicGeometry.Space.universallyInjective_iff_injectiveOnFieldPoints` is the resulting
  equivalence of conditions (1) and (2), and
  `AlgebraicGeometry.Space.injectiveOnFieldPoints_iff_isSurjective_diagonal` the equivalence
  of conditions (1) and (3).
* `AlgebraicGeometry.Space.injectiveOnFieldPoints_tfae` is the three-way equivalence itself.
* `AlgebraicGeometry.Space.eq_of_app_eq_of_universallyInjective` is the implication
  (2) ⇒ (1) stated at a field-valued point of the source: two sections over the spectrum of a
  field with the same image under a universally injective morphism are equal.
* `AlgebraicGeometry.Space.eq_of_map_eq_of_fieldSpecHom`: two sections of an algebraic space
  over the spectrum of a field in the site which agree after restriction along a single
  morphism from the spectrum of a field are equal. This is the one use of
  [Stacks Project, Tag 0APL] in the proof.

## Implementation notes

A field `K` over `S` enters the statement only through the object of the site it represents,
so the quantifier of condition (1) runs over the fields whose spectrum satisfies the site's
size cutoff, exactly as the field-valued points `AlgebraicGeometry.Space.FieldValuedPoint`
and the characterization of [Stacks Project, Tag 03MU],
`AlgebraicGeometry.Space.universallyInjective_iff_injective_on_field_points`, do. For a field
outside the cutoff neither `X(K)` nor `Y(K)` is defined, the two being presheaves on the site.

The implication (1) ⇒ (2) is immediate from
`AlgebraicGeometry.Space.universallyInjective_of_fieldPoints`, whose hypothesis asks only
that two sections over a field spectrum with the same image become equal after *one*
restriction to a field spectrum: condition (1) makes them equal already, so the identity
serves as the restriction. It needs nothing of the algebraicity of the source, of the target
or of the test space.

The implication (2) ⇒ (1) is the source's argument. Given `a₁, a₂ : X(K)` with the same image
`c : Spec(K) → Y`, the pairs `(𝟙, a₁)` and `(𝟙, a₂)` are sections of `Spec(K) ×_{c, Y} X`
over `Spec(K)`, and the two points of the fibre product they define have the same image in
`|Spec(K)|` — namely the point represented by the identity. Condition (2), applied to the
base change along `c` of the representable algebraic space `Spec(K)`, makes those two points
equal, so by `AlgebraicGeometry.Space.FieldValuedPoint.class_eq_class_iff` a single field `Ω`
in the site and two morphisms `α₁, α₂ : Spec(Ω) → Spec(K)` carry both sections to one section
of the fibre product. The first projection of that equality reads `α₁ = α₂`, which is the
source's "composing with the projection to `Spec(K)`", and the second projection then says
that `a₁` and `a₂` agree after restriction along the common value `α`. Since
`Spec(Ω) → Spec(K)` is faithfully flat and quasi-compact, `{α}` is an fpqc covering of the
site, and `X` is a sheaf for the fpqc topology by [Stacks Project, Tag 0APL], so `a₁ = a₂`.
That last step is `AlgebraicGeometry.Space.eq_of_map_eq_of_fieldSpecHom`, which combines
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc` with
`AlgebraicGeometry.Space.sieve_generate_singleton_mem_fpqcTopology_over`.

The source reaches (2) ⇔ (3) through Properties of Spaces, Lemmas
[Stacks Project, Tag 03H4] and [Stacks Project, Tag 03H5]; in this development that
equivalence is already available directly, so only the arrows through condition (1) are
proved here.

## References

* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 03MU](https://stacks.math.columbia.edu/tag/03MU)
* [Stacks Project, Tag 03MV](https://stacks.math.columbia.edu/tag/03MV)
* [Stacks Project, Tag 040X](https://stacks.math.columbia.edu/tag/040X)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Condition (1): injectivity on field-valued points -/

/-- **Stacks 040X, condition (1).** The map `X(K) → Y(K)` induced by a morphism of presheaves
on the big fppf site of `S` is injective for every field `K` over `S`.

A field over `S` is a field `K` together with a morphism `Spec(K) ⟶ S`, and it enters through
the object of the site it represents, so the quantifier runs over the fields whose spectrum
satisfies the site's size cutoff. -/
def InjectiveOnFieldPoints (f : X ⟶ Y) : Prop :=
  ∀ (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (b : Spec (.of K) ⟶ S),
    Function.Injective (f.app (op (Over.mk (⟨b⟩ : B.obj hK ⟶ B.obj hS))))

/-! ### Condition (1) implies condition (2) -/

/-- **Stacks 040X, condition (1) implies condition (2).** A morphism of presheaves on the big
fppf site of `S` which is injective on the field-valued points of every field over `S` is
universally injective.

This is `AlgebraicGeometry.Space.universallyInjective_of_fieldPoints`, whose hypothesis asks
that two sections over a field spectrum with the same image agree after one restriction to a
field spectrum: here they agree already, so the identity serves. Nothing of the algebraicity
of the source, of the target or of the test space is used. -/
theorem universallyInjective_of_injectiveOnFieldPoints (f : X ⟶ Y)
    (hf : InjectiveOnFieldPoints B S hS f) :
    UniversallyInjective B S hS f := by
  refine universallyInjective_of_fieldPoints B S hS f fun p y hy ↦ ?_
  have hpy : p.value = y := hf p.carrier p.contained p.toBase hy
  refine ⟨p, 𝟙 p.siteObject, ?_, ?_⟩
  · simp
  · rw [← hpy]
    simp

/-! ### Descent of an equality of sections along a morphism of field spectra -/

/-- The morphism of schemes underlying a morphism of field spectra is surjective, flat and
quasi-compact: it is `Spec` of a homomorphism of fields, which is faithfully flat because a
field extension is a free module, and a morphism of affine schemes is quasi-compact. -/
@[ega "IV 2.7.3" "(iii)",
  ega "IV 4.4.1" "partial",
  ega "IV 8.1.2" "partial",
  ega "IV 9.1.3" "more general"]
private theorem surjective_flat_quasiCompact_of_fieldSpecHom {K L : Type u} [Field K] [Field L]
    (e : Spec (.of L) ⟶ Spec (.of K)) :
    Surjective e ∧ Flat e ∧ QuasiCompact e := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective e
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- **Two sections of an algebraic space over a field spectrum which agree after one
restriction to a field spectrum are equal.**

A morphism `Spec(Ω) ⟶ Spec(K)` of field spectra in the site is surjective, flat and
quasi-compact, so the sieve it generates is a covering sieve for the fpqc topology of the
site by `AlgebraicGeometry.Space.sieve_generate_singleton_mem_fpqcTopology_over`; an
algebraic space is a sheaf for that topology by [Stacks Project, Tag 0APL], hence separated
for that sieve. This is the one use of Tag 0APL in the proof of
[Stacks Project, Tag 040X]. -/
theorem eq_of_map_eq_of_fieldSpecHom (hX : IsAlgebraicSpace B S hS X)
    {K L : Type u} [Field K] [Field L] {hK : B.Contains (Spec (.of K))}
    {hL : B.Contains (Spec (.of L))} {bK : Spec (.of K) ⟶ S} {bL : Spec (.of L) ⟶ S}
    (α : (Over.mk (⟨bL⟩ : B.obj hL ⟶ B.obj hS)) ⟶ Over.mk (⟨bK⟩ : B.obj hK ⟶ B.obj hS))
    {a₁ a₂ : X.obj (op (Over.mk (⟨bK⟩ : B.obj hK ⟶ B.obj hS)))}
    (h : X.map α.op a₁ = X.map α.op a₂) :
    a₁ = a₂ := by
  obtain ⟨hsurj, hflat, hqc⟩ :=
    surjective_flat_quasiCompact_of_fieldSpecHom (K := K) (L := L)
      ((BigFppfOver.toScheme B S hS).map α)
  have hsheaf := (isSheaf_iff_isSheaf_of_type _ X).mp hX.isSheaf_fpqc
  refine ((hsheaf _ (sieve_generate_singleton_mem_fpqcTopology_over B S hS α hsurj hflat
    hqc)).isSeparatedFor).ext ?_
  rintro W k ⟨Z, u, v, hv, rfl⟩
  cases hv
  rw [op_comp, FunctorToTypes.map_comp_apply, FunctorToTypes.map_comp_apply, h]

/-! ### Condition (2) implies condition (1) -/

/-- **Two sections of an algebraic space over a field spectrum with the same image under a
universally injective morphism are equal.** This is the content of the implication (2) ⇒ (1)
of [Stacks Project, Tag 040X], stated at a field-valued point of the source.

The two sections `p.value` and `y` of `X` over `Spec(K)` have the same image
`c : Spec(K) ⟶ Y`, so they define two points of `Spec(K) ×_{c, Y} X` whose images in
`|Spec(K)|` are both the class of the identity; universal injectivity makes those points
equal, so a single morphism `α : Spec(Ω) ⟶ Spec(K)` of field spectra in the site carries both
sections to one section of the fibre product. Reading off the first projection identifies the
two morphisms produced by the common extension, and the second projection then says that the
sections agree after restriction along `α`, whence they are equal by
`AlgebraicGeometry.Space.eq_of_map_eq_of_fieldSpecHom`. -/
theorem eq_of_app_eq_of_universallyInjective (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (hf : UniversallyInjective B S hS f) (p : FieldValuedPoint B S hS X)
    (y : X.obj (op p.siteObject))
    (hy : f.app (op p.siteObject) p.value = f.app (op p.siteObject) y) :
    p.value = y := by
  obtain ⟨g, hg⟩ : ∃ g : yoneda.obj p.siteObject ⟶ Y,
      g = yonedaEquiv.symm (f.app (op p.siteObject) p.value) := ⟨_, rfl⟩
  -- a section of `X` over `Spec(K)` with the same image as `p.value` gives a section of the
  -- fibre product whose first projection is the identity
  have key : ∀ a : X.obj (op p.siteObject),
      f.app (op p.siteObject) a = f.app (op p.siteObject) p.value →
      ∃ z : (pullback g f).obj (op p.siteObject),
        (pullback.fst g f).app (op p.siteObject) z = 𝟙 p.siteObject ∧
          (pullback.snd g f).app (op p.siteObject) z = a := by
    intro a ha
    refine ⟨yonedaEquiv (pullback.lift (𝟙 (yoneda.obj p.siteObject))
      (yonedaEquiv.symm a) ?_), ?_, ?_⟩
    · rw [Category.id_comp, yonedaEquiv_symm_naturality_right, ha, hg]
    · rw [← yonedaEquiv_comp, pullback.lift_fst]
      rfl
    · rw [← yonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]
  obtain ⟨z₁, hz₁fst, hz₁snd⟩ := key p.value rfl
  obtain ⟨z₂, hz₂fst, hz₂snd⟩ := key y hy.symm
  have hmapeq : ∀ z : (pullback g f).obj (op p.siteObject),
      FieldValuedPoint.map B S hS (pullback g f) (pullback.fst g f) { p with value := z } =
        { p with value := (pullback.fst g f).app (op p.siteObject) z } := fun _ ↦ rfl
  have hcls : FieldValuedPoint.class B S hS (pullback g f) { p with value := z₁ } =
      FieldValuedPoint.class B S hS (pullback g f) { p with value := z₂ } := by
    refine hf (yoneda.obj p.siteObject)
      (isAlgebraicSpace_yoneda B S hS p.siteObject) g ?_
    rw [pointsMap_class, pointsMap_class, hmapeq, hmapeq, hz₁fst, hz₂fst]
  obtain ⟨r, ⟨α₁, hα₁⟩, ⟨α₂, hα₂⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS (pullback g f) _ _).mp hcls
  have hnat : ∀ {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : pullback g f ⟶ W)
      (c : r.siteObject ⟶ p.siteObject) (z : (pullback g f).obj (op p.siteObject)),
      (pullback g f).map c.op z = r.value →
      W.map c.op (φ.app (op p.siteObject) z) = φ.app (op r.siteObject) r.value :=
    fun φ c z hc ↦ by rw [← NatTrans.naturality_apply, hc]
  have hfstα : ∀ (c : r.siteObject ⟶ p.siteObject) (z : (pullback g f).obj (op p.siteObject)),
      (pullback.fst g f).app (op p.siteObject) z = 𝟙 p.siteObject →
      (pullback g f).map c.op z = r.value →
      c = (pullback.fst g f).app (op r.siteObject) r.value := by
    intro c z hz hc
    simpa [hz] using hnat (pullback.fst g f) c z hc
  have hαeq : α₁ = α₂ :=
    (hfstα α₁ z₁ hz₁fst hα₁).trans (hfstα α₂ z₂ hz₂fst hα₂).symm
  refine eq_of_map_eq_of_fieldSpecHom B S hS hX (K := p.carrier) (L := r.carrier)
    (hK := p.contained) (hL := r.contained) (bK := p.toBase) (bL := r.toBase) α₁ ?_
  rw [← hz₁snd, hnat _ α₁ z₁ hα₁, hαeq, ← hz₂snd, hnat _ α₂ z₂ hα₂]

/-- **Stacks 040X, condition (2) implies condition (1).** A universally injective morphism
from an algebraic space over `S` is injective on the field-valued points of every field over
`S`.

This is `AlgebraicGeometry.Space.eq_of_app_eq_of_universallyInjective`, read at the
field-valued point assembled from the field, its structure morphism and the first of the two
sections. -/
theorem injectiveOnFieldPoints_of_universallyInjective (hX : IsAlgebraicSpace B S hS X)
    (f : X ⟶ Y) (hf : UniversallyInjective B S hS f) :
    InjectiveOnFieldPoints B S hS f := fun _ _ hK b _ a₂ hab ↦
  eq_of_app_eq_of_universallyInjective B S hS hX f hf ⟨_, hK, b, _⟩ a₂ hab

/-! ### The three-way equivalence -/

/-- **Stacks 040X, conditions (1) and (2).** A morphism from an algebraic space over `S` is
injective on the field-valued points of every field over `S` if and only if it is universally
injective. -/
theorem universallyInjective_iff_injectiveOnFieldPoints (hX : IsAlgebraicSpace B S hS X)
    (f : X ⟶ Y) :
    UniversallyInjective B S hS f ↔ InjectiveOnFieldPoints B S hS f :=
  ⟨injectiveOnFieldPoints_of_universallyInjective B S hS hX f,
    universallyInjective_of_injectiveOnFieldPoints B S hS f⟩

/-- A morphism from an algebraic space over `S` is injective on the field-valued points of
every field over `S` if and only if its relative diagonal is surjective on points.

This is the composite of the two equivalences of [Stacks Project, Tag 040X] recorded for
convenience; the tag's own registration of it is on
`AlgebraicGeometry.Space.injectiveOnFieldPoints_tfae`, so no `@[stacks]` attribute is attached
here. -/
theorem injectiveOnFieldPoints_iff_isSurjective_diagonal (hX : IsAlgebraicSpace B S hS X)
    (f : X ⟶ Y) :
    InjectiveOnFieldPoints B S hS f ↔ IsSurjective B S hS (pullback.diagonal f) :=
  (universallyInjective_iff_injectiveOnFieldPoints B S hS hX f).symm.trans
    (universallyInjective_iff_isSurjective_diagonal B S hS hX f)

/-- **Stacks 040X.** For a morphism `f : X ⟶ Y` from an algebraic space over `S` the
following are equivalent:

1. the map `X(K) → Y(K)` is injective for every field `K` over `S`,
2. for every morphism `Y' ⟶ Y` of algebraic spaces over `S` the induced map
   `|Y' ×_Y X| → |Y'|` is injective, and
3. the diagonal morphism `X ⟶ X ×_Y X` is surjective. -/
@[stacks 040X]
theorem injectiveOnFieldPoints_tfae (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    List.TFAE [InjectiveOnFieldPoints B S hS f, UniversallyInjective B S hS f,
      IsSurjective B S hS (pullback.diagonal f)] := by
  tfae_have 1 ↔ 2 := (universallyInjective_iff_injectiveOnFieldPoints B S hS hX f).symm
  tfae_have 2 ↔ 3 := universallyInjective_iff_isSurjective_diagonal B S hS hX f
  tfae_finish

end AlgebraicGeometry.Space

end
