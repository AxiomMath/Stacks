module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValued
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology

/-!
# Points of algebraic spaces with values in a larger universe

An algebraic space over a scheme `S` of a big fppf site `B` is a presheaf on the big fppf
site of `S` with values in `Type u`, the universe of the schemes, and its point set and point
topology are those of `StacksFrontier.AlgebraicGeometry.Spaces.Points` and
`StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology`. Presheaves with values in a strictly
larger universe occur as soon as colimits of such sheaves are taken: a formal algebraic space
is a sheaf of `Type (u + 1)`. This file carries the point set and the point topology for a
value universe `max w u` with `w` independent of `u`.

Nothing is weakened by the move: a field-valued point is still a section over the spectrum of
a field of `Type u` lying in the site, two of them define the same point exactly when they
have a common field-valued extension, and a set of points is open exactly when its preimage
under every universe-lifted scheme-valued point is cut out by an open subset of the scheme.
`CategoryTheory.uliftYoneda.{u}` and `CategoryTheory.yoneda` are isomorphic, so at `w = u`
the notions below are the ones already in the library.

## Main definitions

* `AlgebraicGeometry.Space.FieldValuedPointULift` is `AlgebraicGeometry.Space.FieldValuedPoint`
  for a presheaf of `Type (max w u)`.
* `AlgebraicGeometry.Space.pointsULift` is `AlgebraicGeometry.Space.points` for such a
  presheaf, and `AlgebraicGeometry.Space.pointsMapULift` the map it induces on points.
* `AlgebraicGeometry.Space.schemePointULift` and
  `AlgebraicGeometry.Space.IsSchemeOpenULift` are
  `AlgebraicGeometry.Space.schemePoint` and `AlgebraicGeometry.Space.IsSchemeOpen` for a
  universe-lifted represented presheaf.
* `AlgebraicGeometry.Space.pointTopologyULift` is `AlgebraicGeometry.Space.pointTopology` for
  a presheaf of `Type (max w u)`.

## Main results

* `AlgebraicGeometry.Space.FieldValuedPointULift.hasCommonExtension_equivalence`: having a
  common field-valued extension is an equivalence relation, so the point set is its set of
  classes.
* `AlgebraicGeometry.Space.FieldValuedPointULift.class_eq_class_iff`: two field-valued
  representatives define the same point exactly when they have a common extension.
* `AlgebraicGeometry.Space.continuous_pointsMapULift`: every morphism of presheaves with
  values in `Type (max w u)` is continuous on points.

## Implementation notes

The field of definition of a field-valued point stays in `Type u`, since the objects of the
site are schemes of that universe; only the section grows, lying in `F.obj _ : Type (max w u)`.
So `AlgebraicGeometry.Space.pointsULift` lands in `Type (max w (u + 1))`, and at `w = u` in
`Type (u + 1)` as `AlgebraicGeometry.Space.points` does.

Transitivity of having a common extension is the one substantial proof, and it is the proof of
`AlgebraicGeometry.Space.FieldValuedPoint.hasCommonExtension_trans`: amalgamating two
extensions of a field-valued point uses only `AlgebraicGeometry.exists_fieldSpec_common`, a
statement about fields of `Type u`, and functoriality of `F`, neither of which constrains the
value universe.

The test objects of the topology are the morphisms out of `CategoryTheory.uliftYoneda.{w}.obj U`,
as they are for every other notion in
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValued`. The section of a field-valued point of
such a presheaf is a universe lift of a morphism of the site, so the underlying scheme point
is read off its `ULift.down`.

`AlgebraicGeometry.Space.pointTopologyULift` is a `def`, not an instance, exactly as
`AlgebraicGeometry.Space.pointTopology` is; a client supplies it with `letI`, or installs it
as a local instance.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u))

/-! ### Field-valued points -/

/-- A representative of a point of a presheaf over `S` with values in a universe `max w u`
independent of the universe `u` of the schemes, given by a section over a field spectrum in
the chosen big fppf site. This is `AlgebraicGeometry.Space.FieldValuedPoint` for such a
presheaf. -/
structure FieldValuedPointULift where
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

attribute [instance] FieldValuedPointULift.field

namespace FieldValuedPointULift

/-- The object of the big fppf site over `S` represented by a field-valued point. -/
@[implicit_reducible] noncomputable def siteObject
    (p : FieldValuedPointULift.{w} B S hS F) : BigFppfOver B S hS :=
  Over.mk (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hS)

/-- A field-valued point is an extension of another if its section is the restriction of the
other's section along a morphism of field spectra over `S`. -/
def Dominates (p q : FieldValuedPointULift.{w} B S hS F) : Prop :=
  ∃ f : p.siteObject B S hS F ⟶ q.siteObject B S hS F, F.map f.op q.value = p.value

/-- Two field-valued points have a common field-valued extension. -/
def HasCommonExtension (p q : FieldValuedPointULift.{w} B S hS F) : Prop :=
  ∃ r : FieldValuedPointULift.{w} B S hS F,
    Dominates B S hS F r p ∧ Dominates B S hS F r q

/-- Every representative dominates itself. -/
theorem dominates_refl (p : FieldValuedPointULift.{w} B S hS F) :
    Dominates B S hS F p p :=
  ⟨𝟙 _, by simp⟩

/-- Common extension is reflexive. -/
theorem hasCommonExtension_refl (p : FieldValuedPointULift.{w} B S hS F) :
    HasCommonExtension B S hS F p p :=
  ⟨p, dominates_refl B S hS F p, dominates_refl B S hS F p⟩

/-- Common extension is symmetric. -/
theorem hasCommonExtension_symm {p q : FieldValuedPointULift.{w} B S hS F}
    (h : HasCommonExtension B S hS F p q) :
    HasCommonExtension B S hS F q p :=
  let ⟨r, hp, hq⟩ := h
  ⟨r, hq, hp⟩

/-- Apply a morphism of presheaves to a field-valued point. -/
noncomputable def map {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (α : F ⟶ G) (p : FieldValuedPointULift.{w} B S hS F) :
    FieldValuedPointULift.{w} B S hS G where
  carrier := p.carrier
  field := p.field
  contained := p.contained
  toBase := p.toBase
  value := α.app (Opposite.op (p.siteObject B S hS F)) p.value

/-- A morphism of presheaves preserves common refinements. -/
theorem hasCommonExtension_map {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (α : F ⟶ G) {p q : FieldValuedPointULift.{w} B S hS F}
    (h : HasCommonExtension B S hS F p q) :
    HasCommonExtension B S hS G (map B S hS F α p) (map B S hS F α q) := by
  have key {x y : FieldValuedPointULift.{w} B S hS F} (h : Dominates B S hS F x y) :
      Dominates B S hS G (map B S hS F α x) (map B S hS F α y) :=
    let ⟨f, hf⟩ := h
    ⟨f, by simp [map, siteObject, ← hf]; rfl⟩
  obtain ⟨r, hp, hq⟩ := h
  exact ⟨map B S hS F α r, key hp, key hq⟩

end FieldValuedPointULift

/-- Points of an algebraic space with values in a universe `max w u` independent of the
universe `u` of the schemes are equivalence classes of its field-valued points. This is
`AlgebraicGeometry.Space.points` for such a presheaf. -/
abbrev pointsULift : Type (max w (u + 1)) :=
  Quot (FieldValuedPointULift.HasCommonExtension.{w} B S hS F)

/-- The class of a field-valued point. -/
abbrev FieldValuedPointULift.class (p : FieldValuedPointULift.{w} B S hS F) :
    pointsULift.{w} B S hS F := Quot.mk _ p

/-- Common extension is transitive: two extensions of a field-valued point can be amalgamated
over that point. -/
theorem FieldValuedPointULift.hasCommonExtension_trans
    {p q r : FieldValuedPointULift.{w} B S hS F}
    (hpq : FieldValuedPointULift.HasCommonExtension B S hS F p q)
    (hqr : FieldValuedPointULift.HasCommonExtension B S hS F q r) :
    FieldValuedPointULift.HasCommonExtension B S hS F p r := by
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
      s.siteObject B S hS F :=
    Over.homMk (⟨ca⟩ : B.obj hΩ ⟶ B.obj s.contained) (by ext; rfl)
  let τ : (Over.mk (⟨ca ≫ s.toBase⟩ : B.obj hΩ ⟶ B.obj hS) : BigFppfOver B S hS) ⟶
      t.siteObject B S hS F :=
    Over.homMk (⟨cb⟩ : B.obj hΩ ⟶ B.obj t.contained) (by ext; exact hbase)
  have hcomm : σ ≫ fq = τ ≫ gq := by
    ext
    exact key
  refine ⟨{ carrier := Ω, contained := hΩ, toBase := ca ≫ s.toBase
            value := F.map σ.op s.value }, ⟨σ ≫ fp, ?_⟩, ⟨τ ≫ gr, ?_⟩⟩
  · rw [op_comp, F.map_comp, types_comp_apply, hfp]
  · rw [op_comp, F.map_comp, types_comp_apply, hgr, ← hgq, ← hfq, ← types_comp_apply,
      ← types_comp_apply, ← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, hcomm]

/-- Common extension of field-valued points is an equivalence relation. -/
theorem FieldValuedPointULift.hasCommonExtension_equivalence :
    Equivalence (FieldValuedPointULift.HasCommonExtension.{w} B S hS F) :=
  ⟨FieldValuedPointULift.hasCommonExtension_refl B S hS F,
    FieldValuedPointULift.hasCommonExtension_symm B S hS F,
    FieldValuedPointULift.hasCommonExtension_trans B S hS F⟩

/-- Equality of classes is equality in the equivalence closure of common refinements. -/
theorem FieldValuedPointULift.class_eq_class_iff_eqvGen
    (p q : FieldValuedPointULift.{w} B S hS F) :
    p.class B S hS F = q.class B S hS F ↔
      Relation.EqvGen (FieldValuedPointULift.HasCommonExtension.{w} B S hS F) p q :=
  Quot.eq

/-- Two field-valued representatives define the same point exactly when they admit a common
field-valued extension. -/
theorem FieldValuedPointULift.class_eq_class_iff
    (p q : FieldValuedPointULift.{w} B S hS F) :
    p.class B S hS F = q.class B S hS F ↔
      FieldValuedPointULift.HasCommonExtension B S hS F p q :=
  (FieldValuedPointULift.class_eq_class_iff_eqvGen B S hS F p q).trans
    (Equivalence.eqvGen_iff (FieldValuedPointULift.hasCommonExtension_equivalence B S hS F))

/-- A common field-valued extension identifies the two classes. -/
theorem FieldValuedPointULift.class_eq_class_of_hasCommonExtension
    {p q : FieldValuedPointULift.{w} B S hS F}
    (h : FieldValuedPointULift.HasCommonExtension B S hS F p q) :
    p.class B S hS F = q.class B S hS F := Quot.sound h

/-- The map on points induced by a morphism of presheaves with values in a universe
`max w u` independent of the universe `u` of the schemes. -/
noncomputable def pointsMapULift {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (α : F ⟶ G) : pointsULift.{w} B S hS F → pointsULift.{w} B S hS G :=
  Quot.map (FieldValuedPointULift.map B S hS F α)
    (fun _ _ h ↦ FieldValuedPointULift.hasCommonExtension_map B S hS F α h)

/-- The map on points sends the class of a field-valued point to the class of its image. -/
@[simp]
theorem pointsMapULift_class {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (α : F ⟶ G) (p : FieldValuedPointULift.{w} B S hS F) :
    pointsMapULift B S hS F α (p.class B S hS F) =
      (FieldValuedPointULift.map B S hS F α p).class B S hS G := rfl

/-- The identity morphism of presheaves fixes every field-valued point. -/
@[simp]
theorem FieldValuedPointULift.map_id (p : FieldValuedPointULift.{w} B S hS F) :
    FieldValuedPointULift.map B S hS F (𝟙 F) p = p := rfl

/-- The image of a field-valued point under a composite `α ≫ β` is its image under `α`, then under
`β`. -/
@[simp]
theorem FieldValuedPointULift.map_comp
    {G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (α : F ⟶ G) (β : G ⟶ H) (p : FieldValuedPointULift.{w} B S hS F) :
    FieldValuedPointULift.map B S hS F (α ≫ β) p =
      FieldValuedPointULift.map B S hS G β (FieldValuedPointULift.map B S hS F α p) := rfl

/-- The identity morphism of presheaves induces the identity map on points. -/
@[simp]
theorem pointsMapULift_id : pointsMapULift.{w} B S hS F (𝟙 F) = id := by
  funext x
  induction x using Quot.ind
  rfl

/-- The map on points induced by a composite `α ≫ β` is the composite of the induced maps. -/
@[simp]
theorem pointsMapULift_comp {G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (α : F ⟶ G) (β : G ⟶ H) :
    pointsMapULift B S hS F (α ≫ β) =
      pointsMapULift B S hS G β ∘ pointsMapULift B S hS F α := by
  funext x
  induction x using Quot.ind
  rfl

/-! ### The topology on points -/

/-- The point of the scheme `U` underlying a field-valued point of its universe-lifted
represented presheaf: the image of the closed point of the field spectrum along the section.
This is `AlgebraicGeometry.Space.schemePoint` for a value universe `max w u` independent of
the universe `u` of the schemes. -/
noncomputable def schemePointULift (U : BigFppfOver B S hS)
    (p : FieldValuedPointULift.{w} B S hS ((uliftYoneda.{w}).obj U)) :
    (BigFppfOver.toScheme B S hS).obj U :=
  (BigFppfOver.toScheme B S hS).map p.value.down (IsLocalRing.closedPoint p.carrier)

/-- Applying a morphism of the site to a field-valued point of a universe-lifted represented
presheaf moves its underlying scheme point along the underlying morphism of schemes. -/
theorem schemePointULift_map_uliftYoneda {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (p : FieldValuedPointULift.{w} B S hS ((uliftYoneda.{w}).obj U)) :
    schemePointULift B S hS V
        (FieldValuedPointULift.map B S hS ((uliftYoneda.{w}).obj U)
          ((uliftYoneda.{w}).map h) p) =
      (BigFppfOver.toScheme B S hS).map h (schemePointULift B S hS U p) := by
  show (BigFppfOver.toScheme B S hS).map (p.value.down ≫ h) _ = _
  rw [Functor.map_comp]
  rfl

/-- A set of points of a universe-lifted represented presheaf is *scheme open* when it is cut
out by an open subset of the representing scheme, membership being tested at the underlying
scheme point of a field-valued representative. This is
`AlgebraicGeometry.Space.IsSchemeOpen` for a value universe `max w u` independent of the
universe `u` of the schemes. -/
def IsSchemeOpenULift (U : BigFppfOver B S hS)
    (W : Set (pointsULift.{w} B S hS ((uliftYoneda.{w}).obj U))) : Prop :=
  ∃ V : Set ((BigFppfOver.toScheme B S hS).obj U), IsOpen V ∧
    ∀ p : FieldValuedPointULift.{w} B S hS ((uliftYoneda.{w}).obj U),
      (p.class B S hS ((uliftYoneda.{w}).obj U) ∈ W ↔ schemePointULift B S hS U p ∈ V)

/-- The topology on the points of a presheaf on the big fppf site of `S` with values in a
universe `max w u` independent of the universe `u` of the schemes: a set of points is open
when its preimage under every universe-lifted scheme-valued point is scheme open. This is
`AlgebraicGeometry.Space.pointTopology` for such a presheaf. -/
@[instance_reducible]
def pointTopologyULift (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)) :
    TopologicalSpace (pointsULift.{w} B S hS F) where
  IsOpen W := ∀ (U : BigFppfOver B S hS) (a : (uliftYoneda.{w}).obj U ⟶ F),
    IsSchemeOpenULift.{w} B S hS U
      (pointsMapULift B S hS ((uliftYoneda.{w}).obj U) a ⁻¹' W)
  isOpen_univ := fun _ _ ↦ ⟨Set.univ, isOpen_univ, fun _ ↦ by simp⟩
  isOpen_inter := by
    rintro W₁ W₂ h₁ h₂ U a
    obtain ⟨V₁, hV₁, hmem₁⟩ := h₁ U a
    obtain ⟨V₂, hV₂, hmem₂⟩ := h₂ U a
    refine ⟨V₁ ∩ V₂, hV₁.inter hV₂, fun p ↦ ?_⟩
    simp only [Set.mem_preimage, Set.mem_inter_iff] at hmem₁ hmem₂ ⊢
    exact and_congr (hmem₁ p) (hmem₂ p)
  isOpen_sUnion := by
    intro s hs U a
    choose V hVopen hVmem using fun W : s ↦ hs W.1 W.2 U a
    refine ⟨⋃ W : s, V W, isOpen_iUnion hVopen, fun p ↦ ?_⟩
    simp only [Set.mem_preimage, Set.mem_sUnion, Set.mem_iUnion] at hVmem ⊢
    constructor
    · rintro ⟨W, hW, hpW⟩
      exact ⟨⟨W, hW⟩, (hVmem ⟨W, hW⟩ p).mp hpW⟩
    · rintro ⟨W, hpW⟩
      exact ⟨W.1, W.2, (hVmem W p).mpr hpW⟩

/-- The open sets of `AlgebraicGeometry.Space.pointTopologyULift` are exactly those whose
preimage under every universe-lifted scheme-valued point is scheme open. -/
theorem isOpen_pointTopologyULift_iff {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (W : Set (pointsULift.{w} B S hS F)) :
    @IsOpen _ (pointTopologyULift.{w} B S hS F) W ↔
      ∀ (U : BigFppfOver B S hS) (a : (uliftYoneda.{w}).obj U ⟶ F),
        IsSchemeOpenULift.{w} B S hS U
          (pointsMapULift B S hS ((uliftYoneda.{w}).obj U) a ⁻¹' W) :=
  Iff.rfl

/-- Every morphism of presheaves on the big fppf site of `S` with values in a universe
`max w u` independent of the universe `u` of the schemes is continuous on points. -/
theorem continuous_pointsMapULift {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (f : F ⟶ G) :
    @Continuous _ _ (pointTopologyULift.{w} B S hS F) (pointTopologyULift.{w} B S hS G)
      (pointsMapULift B S hS F f) := by
  rw [continuous_def]
  intro W hW U a
  simpa only [pointsMapULift_comp, Set.preimage_comp] using hW U (a ≫ f)

end AlgebraicGeometry.Space

end
