module

public import Mathlib.Logic.Relation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic

/-!
# Points of an algebraic space

A point of an algebraic space over `S` is an equivalence class of morphisms from spectra of
fields into it. Two such morphisms are equivalent when they admit a common field-valued
extension over the space.

Everything here is stated for an arbitrary presheaf on the big fppf site of `S`: the
construction never uses the algebraic-space axioms, and it is applied to
represented presheaves as well as to algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Space.FieldValuedPoint` is a representative of a point: a field in the
  working universe whose spectrum lies in the chosen big fppf site, a structure morphism to
  the base, and a section of the presheaf over the resulting object of the site.
* `AlgebraicGeometry.Space.FieldValuedPoint.Dominates` says that one representative is the
  restriction of another along a morphism of field spectra over `S`, and
  `AlgebraicGeometry.Space.FieldValuedPoint.HasCommonExtension` that two representatives
  admit a common such refinement.
* `AlgebraicGeometry.Space.points` is the set of points `|X|`, and
  `AlgebraicGeometry.Space.FieldValuedPoint.class` is the point represented by a
  field-valued point.
* `AlgebraicGeometry.Space.pointsMap` is the map `|f|` on points induced by a morphism of
  presheaves.

## Main results

* `AlgebraicGeometry.Space.FieldValuedPoint.hasCommonExtension_equivalence`: the
  common-extension relation is an equivalence relation. Its transitivity,
  `AlgebraicGeometry.Space.FieldValuedPoint.hasCommonExtension_trans`, is the only
  non-formal clause of Tag 03BU.
* `AlgebraicGeometry.Space.FieldValuedPoint.class_eq_class_iff`: two field-valued points
  define the same point of `|X|` exactly when they admit a *single* common field-valued
  extension.
* `AlgebraicGeometry.Space.FieldValuedPoint.hasCommonExtension_map` says a morphism of
  presheaves preserves common extensions, which is what makes `pointsMap` well defined.

## Implementation notes

The algebraic space is presented as a sheaf on the chosen big fppf site, so a field spectrum
occurring as the source of a field-valued point must be an object of that site; this is the
`contained` field. The quotient is formed by `Quot` on the common-extension relation, hence
by its equivalence closure, and is left transparent so that clients use the usual `Quot`
API without unfolding lemmas. `class_eq_class_iff_eqvGen` identifies equality of classes
with that closure and `class_eq_class_iff` collapses the closure, using transitivity.

Transitivity amalgamates two extensions of a common representative, which is the compositum
of two field extensions, and the work is in producing it *inside the site's size cutoff*.
The construction is geometric rather than ring-theoretic, so that the size bounds of Stacks
000R apply directly: the fibre product `Spec K ×_{Spec M} Spec L` of the two field spectra
over the third is affine, lies in the site by `AlgebraicGeometry.Scheme.size_pullback_lt`,
and is nonempty because a morphism of field spectra is surjective and surjectivity is
stable under base change. A maximal ideal of its ring of global sections then yields a
field whose cardinality is bounded by that ring's, hence by the size of the fibre product,
so its spectrum lies in the site too. This is
`AlgebraicGeometry.Space.exists_fieldSpec_common`, and the rest of transitivity is the
diagram chase that identifies the two restrictions of the section over `Spec M`.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

/-! ### Amalgamating two field extensions inside the site

The three lemmas of this section produce the common extension used by
`AlgebraicGeometry.Space.FieldValuedPoint.hasCommonExtension_trans`. -/

/-- A nontrivial commutative ring admits a ring homomorphism to a field of no larger
cardinality, namely the quotient by a maximal ideal. -/
theorem exists_field_ringHom_of_nontrivial (R : Type u) [CommRing R] [Nontrivial R] :
    ∃ (K : Type u) (_ : Field K), Nonempty (R →+* K) ∧ #K ≤ max ℵ₀ #R := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  have := hm
  exact ⟨R ⧸ m, Ideal.Quotient.field m, ⟨Ideal.Quotient.mk m⟩,
    (mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := m))).trans (le_max_right _ _)⟩

/-- A nonempty affine scheme in a big fppf site receives a morphism from the spectrum of a
field which is itself an object of the site.

The field is the quotient of the ring of global sections by a maximal ideal; its spectrum
satisfies the site's size cutoff because `Scheme.size` bounds the cardinality of the
sections over an affine open. -/
theorem exists_fieldSpec_of_isAffine (B : BigFppfSite.{u}) (P : Scheme.{u}) [IsAffine P]
    (x : P) (hP : B.Contains P) :
    ∃ (K : Type u) (_ : Field K), ∃ _ : B.Contains (Spec (.of K)),
      Nonempty (Spec (.of K) ⟶ P) := by
  have : Nontrivial Γ(P, (⊤ : P.Opens)) :=
    (P.presheaf.germ ⊤ x trivial).hom.domain_nontrivial
  obtain ⟨K, instK, ⟨φ⟩, hcard⟩ := exists_field_ringHom_of_nontrivial Γ(P, (⊤ : P.Opens))
  refine ⟨K, instK, ?_, ⟨Spec.map (CommRingCat.ofHom φ) ≫ P.isoSpec.inv⟩⟩
  refine lt_of_le_of_lt ?_ hP
  rw [Scheme.size_Spec]
  calc max ℵ₀ #K ≤ max ℵ₀ (max ℵ₀ #Γ(P, (⊤ : P.Opens))) := max_le_max le_rfl hcard
    _ = max ℵ₀ #Γ(P, (⊤ : P.Opens)) := by rw [← max_assoc, max_self]
    _ ≤ P.size := max_le P.aleph0_le_size (P.mk_sections_le_size ⟨⊤, isAffineOpen_top P⟩)

/-- Two morphisms of field spectra in a big fppf site with a common target admit a common
extension by the spectrum of a field which is again an object of the site: a compositum of
the two extensions, obtained from a point of their fibre product. -/
theorem exists_fieldSpec_common (B : BigFppfSite.{u}) {K L M : Type u}
    [Field K] [Field L] [Field M]
    (hK : B.Contains (Spec (.of K))) (hL : B.Contains (Spec (.of L)))
    (a : Spec (.of K) ⟶ Spec (.of M)) (b : Spec (.of L) ⟶ Spec (.of M)) :
    ∃ (Ω : Type u) (_ : Field Ω), ∃ _ : B.Contains (Spec (.of Ω)),
      ∃ (ca : Spec (.of Ω) ⟶ Spec (.of K)) (cb : Spec (.of Ω) ⟶ Spec (.of L)),
        ca ≫ a = cb ≫ b := by
  have hsurj : Surjective a := ⟨fun _ ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have hsnd : Surjective (pullback.snd a b) := inferInstance
  obtain ⟨x, -⟩ := hsnd.surj (Classical.arbitrary (Spec (CommRingCat.of L)))
  obtain ⟨Ω, instΩ, hΩ, ⟨w⟩⟩ :=
    exists_fieldSpec_of_isAffine B (pullback a b) x (Scheme.size_pullback_lt a b hK hL)
  refine ⟨Ω, instΩ, hΩ, w ≫ pullback.fst a b, w ≫ pullback.snd a b, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition]

/-! ### Field-valued points -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- A representative of a point of a presheaf over `S`, given by a section over a field
spectrum in the chosen big fppf site. -/
structure FieldValuedPoint where
  /-- The field of definition. -/
  carrier : Type u
  /-- Its field structure. -/
  [field : Field carrier]
  /-- The field spectrum lies in the chosen site. -/
  contained : B.Contains (Spec (.of carrier))
  /-- The structure map to the base. -/
  toBase : Spec (.of carrier) ⟶ S
  /-- The corresponding section of the presheaf. -/
  value : F.obj (Opposite.op (Over.mk
    (⟨toBase⟩ : B.obj contained ⟶ B.obj hS)))

attribute [instance] FieldValuedPoint.field

namespace FieldValuedPoint

/-- The object of the big fppf site over `S` represented by a field-valued point. -/
@[implicit_reducible] noncomputable def siteObject (p : FieldValuedPoint B S hS F) :
    BigFppfOver B S hS :=
  Over.mk (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hS)

/-- A field-valued point is an extension of another if its section is the restriction of
the other's section along a morphism of field spectra over `S`. -/
def Dominates (p q : FieldValuedPoint B S hS F) : Prop :=
  ∃ f : p.siteObject ⟶ q.siteObject, F.map f.op q.value = p.value

/-- Two field-valued points have a common field-valued extension. -/
def HasCommonExtension (p q : FieldValuedPoint B S hS F) : Prop :=
  ∃ r : FieldValuedPoint B S hS F,
    Dominates B S hS F r p ∧ Dominates B S hS F r q

/-- Every representative dominates itself. -/
theorem dominates_refl (p : FieldValuedPoint B S hS F) :
    Dominates B S hS F p p :=
  ⟨𝟙 p.siteObject, by simp⟩

/-- Common extension is reflexive. -/
theorem hasCommonExtension_refl (p : FieldValuedPoint B S hS F) :
    HasCommonExtension B S hS F p p :=
  ⟨p, dominates_refl B S hS F p, dominates_refl B S hS F p⟩

/-- Common extension is symmetric. -/
theorem hasCommonExtension_symm {p q : FieldValuedPoint B S hS F}
    (h : HasCommonExtension B S hS F p q) :
    HasCommonExtension B S hS F q p :=
  Exists.imp (fun _ ↦ And.symm) h

/-- Apply a morphism of presheaves to a field-valued point. -/
noncomputable def map {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : F ⟶ G) (p : FieldValuedPoint B S hS F) :
    FieldValuedPoint B S hS G where
  carrier := p.carrier
  field := p.field
  contained := p.contained
  toBase := p.toBase
  value := α.app (Opposite.op (p.siteObject)) p.value

/-- A morphism of presheaves preserves domination. -/
private theorem dominates_map {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (α : F ⟶ G)
    {r p : FieldValuedPoint B S hS F} (h : Dominates B S hS F r p) :
    Dominates B S hS G (map B S hS F α r) (map B S hS F α p) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f, ?_⟩
  change G.map f.op (α.app _ p.value) = α.app _ r.value
  rw [← hf]
  simpa only [siteObject, types_comp_apply] using
    (congrArg (fun k ↦ k p.value) (α.naturality f.op)).symm

/-- A morphism of presheaves preserves common refinements. -/
theorem hasCommonExtension_map
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : F ⟶ G) {p q : FieldValuedPoint B S hS F}
    (h : HasCommonExtension B S hS F p q) :
    HasCommonExtension B S hS G (map B S hS F α p) (map B S hS F α q) := by
  obtain ⟨r, hp, hq⟩ := h
  exact ⟨map B S hS F α r, dominates_map B S hS F α hp, dominates_map B S hS F α hq⟩

end FieldValuedPoint

/-- **Stacks 03BU.** Points of an algebraic space are equivalence classes of its
field-valued points. -/
@[stacks 03BU "set of points"]
abbrev points : Type (u + 1) :=
  Quot (FieldValuedPoint.HasCommonExtension B S hS F)

/-- The class of a field-valued point. -/
abbrev FieldValuedPoint.class (p : FieldValuedPoint B S hS F) :
    points B S hS F := Quot.mk _ p

/-- **Stacks 03BU.** Common extension is transitive: two extensions of a field-valued point
can be amalgamated over that point. -/
@[stacks 03BU "equivalence of field-valued points"]
theorem FieldValuedPoint.hasCommonExtension_trans
    {p q r : FieldValuedPoint B S hS F}
    (hpq : FieldValuedPoint.HasCommonExtension B S hS F p q)
    (hqr : FieldValuedPoint.HasCommonExtension B S hS F q r) :
    FieldValuedPoint.HasCommonExtension B S hS F p r := by
  obtain ⟨s, ⟨fp, hfp⟩, ⟨fq, hfq⟩⟩ := hpq
  obtain ⟨t, ⟨gq, hgq⟩, ⟨gr, hgr⟩⟩ := hqr
  have hsa : fq.left.hom ≫ q.toBase = s.toBase := congrArg (fun k ↦ k.hom) (Over.w fq)
  have htb : gq.left.hom ≫ q.toBase = t.toBase := congrArg (fun k ↦ k.hom) (Over.w gq)
  obtain ⟨Ω, instΩ, hΩ, ca, cb, key⟩ :=
    exists_fieldSpec_common B (K := s.carrier) (L := t.carrier) (M := q.carrier)
      s.contained t.contained fq.left.hom gq.left.hom
  have hbase : cb ≫ t.toBase = ca ≫ s.toBase := by
    rw [← htb, ← hsa, ← Category.assoc, ← Category.assoc, key]
  let σ : (Over.mk (⟨ca ≫ s.toBase⟩ : B.obj hΩ ⟶ B.obj hS) : BigFppfOver B S hS) ⟶
      s.siteObject := Over.homMk (⟨ca⟩ : B.obj hΩ ⟶ B.obj s.contained) (by ext; rfl)
  let τ : (Over.mk (⟨ca ≫ s.toBase⟩ : B.obj hΩ ⟶ B.obj hS) : BigFppfOver B S hS) ⟶
      t.siteObject := Over.homMk (⟨cb⟩ : B.obj hΩ ⟶ B.obj t.contained) (by ext; exact hbase)
  have hcomm : σ ≫ fq = τ ≫ gq := by
    ext
    exact key
  refine ⟨{ carrier := Ω, contained := hΩ, toBase := ca ≫ s.toBase,
            value := F.map σ.op s.value }, ⟨σ ≫ fp, ?_⟩, ⟨τ ≫ gr, ?_⟩⟩
  · rw [op_comp, F.map_comp, types_comp_apply, hfp]
  · rw [op_comp, F.map_comp, types_comp_apply, hgr, ← hgq, ← hfq]
    simpa using congrArg (fun k ↦ F.map k.op q.value) hcomm.symm

/-- Common extension of field-valued points is an equivalence relation. -/
theorem FieldValuedPoint.hasCommonExtension_equivalence :
    Equivalence (FieldValuedPoint.HasCommonExtension B S hS F) :=
  ⟨FieldValuedPoint.hasCommonExtension_refl B S hS F,
    FieldValuedPoint.hasCommonExtension_symm B S hS F,
    FieldValuedPoint.hasCommonExtension_trans B S hS F⟩

/-- Equality of classes is equality in the equivalence closure of common refinements. -/
theorem FieldValuedPoint.class_eq_class_iff_eqvGen
    (p q : FieldValuedPoint B S hS F) :
    p.class B S hS F = q.class B S hS F ↔
      Relation.EqvGen (FieldValuedPoint.HasCommonExtension B S hS F) p q :=
  Quot.eq

/-- **Stacks 03BU.** Two field-valued representatives define the same point exactly when
they admit a common field-valued extension. -/
@[stacks 03BU "equality of points"]
theorem FieldValuedPoint.class_eq_class_iff
    (p q : FieldValuedPoint B S hS F) :
    p.class B S hS F = q.class B S hS F ↔
      FieldValuedPoint.HasCommonExtension B S hS F p q :=
  (FieldValuedPoint.class_eq_class_iff_eqvGen B S hS F p q).trans
    (Equivalence.eqvGen_iff (FieldValuedPoint.hasCommonExtension_equivalence B S hS F))

/-- A common field-valued extension identifies the two classes. -/
theorem FieldValuedPoint.class_eq_class_of_hasCommonExtension
    {p q : FieldValuedPoint B S hS F}
    (h : FieldValuedPoint.HasCommonExtension B S hS F p q) :
    p.class B S hS F = q.class B S hS F := Quot.sound h

/-- The map on points induced by a morphism of presheaves. -/
noncomputable def pointsMap {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : F ⟶ G) : points B S hS F → points B S hS G :=
  Quot.map (FieldValuedPoint.map B S hS F α)
    (fun _ _ h ↦ FieldValuedPoint.hasCommonExtension_map B S hS F α h)

/-- The point map sends the class of a representative to the class of its image. -/
@[simp]
theorem pointsMap_class {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : F ⟶ G) (p : FieldValuedPoint B S hS F) :
    pointsMap B S hS F α (p.class B S hS F) =
      (FieldValuedPoint.map B S hS F α p).class B S hS G := rfl

/-- The identity of a presheaf acts trivially on field-valued points. -/
@[simp]
theorem FieldValuedPoint.map_id (p : FieldValuedPoint B S hS F) :
    FieldValuedPoint.map B S hS F (𝟙 F) p = p := rfl

/-- The map on field-valued points induced by a composite is the composite of the maps. -/
@[simp]
theorem FieldValuedPoint.map_comp {G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : F ⟶ G) (β : G ⟶ H) (p : FieldValuedPoint B S hS F) :
    FieldValuedPoint.map B S hS F (α ≫ β) p =
      FieldValuedPoint.map B S hS G β (FieldValuedPoint.map B S hS F α p) := rfl

/-- The identity of a presheaf induces the identity on points. -/
@[simp]
theorem pointsMap_id : pointsMap B S hS F (𝟙 F) = id := by
  funext x
  induction x using Quot.ind
  rfl

/-- The map on points induced by a composite is the composite of the maps on points. -/
@[simp]
theorem pointsMap_comp {G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (α : F ⟶ G) (β : G ⟶ H) :
    pointsMap B S hS F (α ≫ β) =
      pointsMap B S hS G β ∘ pointsMap B S hS F α := by
  funext x
  induction x using Quot.ind
  rfl

/-- An isomorphism of presheaves is surjective on points: the inverse gives a preimage. -/
public theorem pointsMap_surjective_of_isIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G)
    [IsIso e] : Function.Surjective (pointsMap B S hS F e) := by
  intro z
  refine ⟨pointsMap B S hS G (inv e) z, ?_⟩
  have h := pointsMap_comp B S hS G (inv e) e
  rw [IsIso.inv_hom_id, pointsMap_id] at h
  exact (congrFun h z).symm


/-- The point set of the range of a monomorphism of presheaves on the big fppf site is the image
of the point map of that monomorphism. -/
public theorem range_pointsMap_ι_range {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    [Mono f] :
    Set.range (pointsMap B S hS (Subfunctor.range f).toFunctor (Subfunctor.range f).ι) =
      Set.range (pointsMap B S hS F f) := by
  have hcomp : pointsMap B S hS F f =
      pointsMap B S hS (Subfunctor.range f).toFunctor (Subfunctor.range f).ι ∘
        pointsMap B S hS F (Subfunctor.toRange f) := by
    rw [← pointsMap_comp, Subfunctor.toRange_ι]
  rw [hcomp, Set.range_comp,
    (pointsMap_surjective_of_isIso B S hS (Subfunctor.toRange f)).range_eq, Set.image_univ]

/-- A containment of subfunctors gives a containment of their point sets. -/
public theorem range_pointsMap_ι_subset_of_le {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U V : Subfunctor F} (h : U ≤ V) :
    Set.range (pointsMap B S hS U.toFunctor U.ι) ⊆
      Set.range (pointsMap B S hS V.toFunctor V.ι) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨pointsMap B S hS U.toFunctor (Subfunctor.homOfLe h) x, ?_⟩
  rw [← Function.comp_apply (f := pointsMap B S hS V.toFunctor V.ι), ← pointsMap_comp,
    Subfunctor.homOfLe_ι]

end AlgebraicGeometry.Space

end
