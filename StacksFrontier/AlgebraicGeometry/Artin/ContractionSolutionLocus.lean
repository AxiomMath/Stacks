module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolution
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre

/-!
# The contracted locus of a solution obtained from a functorial bijection

In the situation of Stacks 0GH8, recorded by
`AlgebraicGeometry.Artin.ContractionSituation`, Stacks 0GHC says that an algebraic space `X`
locally of finite type over `S` carrying a functorial bijection `F(V) = Mor_S(V, X)` on the
category of locally Noetherian schemes `V` over `S` is a *solution* of the contraction problem:
that the data of `AlgebraicGeometry.Artin.ContractionSituation.Solution` — a proper morphism
`f : X' ⟶ X`, a closed subset `T ⊆ |X|`, an isomorphism `a : X_{/T} ⟶ W`, and the three
conditions recalled in `StacksFrontier.AlgebraicGeometry.Artin.ContractionSolution` — can be
produced for it.

This file constructs the subset `T ⊆ |X|` out of the bijection. A point of `|X|` is a class of
sections over the spectrum of a field (Stacks 03BU), the spectrum of a field is a locally
Noetherian scheme over `S`, and a point lies in `T` when the triple `(Z, u', x̂)` matching its
section has `Z` all of the point space of that spectrum. The inverse image of `T` under every
morphism `ξ : V ⟶ X` from a locally Noetherian scheme `V` over `S` is the `Z` of the triple
matching `ξ`, and `T` is the unique subset of `|X|` with this property.

## Main definitions

* `AlgebraicGeometry.Artin.morOnLocallyNoetherian`: the functor `V ↦ Mor_S(V, X)` on locally
  Noetherian schemes over `S`, the right-hand side of the bijection of Stacks 0GHC, with values
  lifted to `Type (u + 1)`.
* `AlgebraicGeometry.Artin.ContractionSituation.tripleOfMor` and
  `AlgebraicGeometry.Artin.ContractionSituation.tripleOfPoint`: the triple `(Z, u', x̂)` that
  the bijection attaches to a morphism `V ⟶ X` from a locally Noetherian scheme over `S`,
  and the one it attaches to a field-valued point of `X`.
* `AlgebraicGeometry.Artin.ContractionSituation.contractedLocus`: the subset `T ⊆ |X|` of the
  solution.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.preimage_contractedLocus`: for every locally
  Noetherian scheme `V` over `S` and every morphism `ξ : V ⟶ X` the inverse image of `T` under
  `|ξ|` is the subset `Z` of the triple that the bijection attaches to `ξ`.
* `AlgebraicGeometry.Artin.ContractionSituation.eq_contractedLocus_of_preimage`: that
  property determines the subset: any subset of `|X|` with it equals `T`.
* `AlgebraicGeometry.Artin.ContractionSituation.isClosed_preimage_contractedLocus`: the
  inverse image of `T` on every locally Noetherian scheme over `S` is closed.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BY](https://stacks.math.columbia.edu/tag/03BY)
* [Stacks Project, Tag 0AQ2](https://stacks.math.columbia.edu/tag/0AQ2)
* [Stacks Project, Tag 0GE4](https://stacks.math.columbia.edu/tag/0GE4)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
* [Stacks Project, Tag 0GHC](https://stacks.math.columbia.edu/tag/0GHC)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A set of points of the spectrum of a field, viewed as a representable presheaf on the
site, is everything exactly when it contains one point. -/
theorem eq_univ_iff_mem_points_yoneda_siteObject (p : FieldValuedPoint B S hS Y)
    (Z : Set (points B S hS (yoneda.obj p.siteObject)))
    (z : points B S hS (yoneda.obj p.siteObject)) :
    Z = Set.univ ↔ z ∈ Z := by
  refine ⟨fun h ↦ h ▸ Set.mem_univ z, fun h ↦ ?_⟩
  ext y
  simp only [Set.mem_univ, iff_true]
  rwa [(subsingleton_points_yoneda_siteObject B S hS p).elim y z]

/-- For a field-valued point `p` of a representable presheaf `yoneda.obj V`, the section `p`
is a morphism of the site into `V`, and the morphism of presheaves it induces carries every
point of the spectrum of the field to the point represented by `p`. -/
theorem FieldValuedPoint.pointsMap_yoneda_map_eq_class {V : BigFppfOver B S hS}
    (p : FieldValuedPoint B S hS (yoneda.obj V))
    (z : points B S hS (yoneda.obj p.siteObject)) :
    pointsMap B S hS (yoneda.obj p.siteObject) (yoneda.map p.value) z =
      p.class B S hS (yoneda.obj V) := by
  have h : yonedaEquiv.symm p.value = yoneda.map p.value := by
    rw [Equiv.symm_apply_eq, yonedaEquiv_yoneda_map]
  rw [← h]
  exact FieldValuedPoint.pointsMap_eq_class B S hS p z

/-- The site object of a field-valued point is a locally Noetherian scheme over `S`: it is
the spectrum of a field. -/
noncomputable def FieldValuedPoint.locallyNoetherianObject (p : FieldValuedPoint B S hS Y) :
    LocallyNoetherianOver B S hS :=
  ⟨p.siteObject, inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of p.carrier)))⟩

/-- The set of points of the spectrum of the field of `p` is everything exactly when it contains
the class of the tautological field-valued point. -/
private theorem eq_univ_iff_class_tautological_mem (p : FieldValuedPoint B S hS Y)
    (Z : Set (points B S hS (yoneda.obj p.siteObject))) :
    Z = Set.univ ↔ (FieldValuedPoint.tautological B S hS p).class B S hS _ ∈ Z :=
  eq_univ_iff_mem_points_yoneda_siteObject B S hS p Z _

end Space

namespace Artin

attribute [local instance] Space.pointTopology

/-- The functor `V ↦ Mor_S(V, X)` on the locally Noetherian schemes over `S` of Stacks 0GE4,
for an algebraic space `X` over `S` presented as a presheaf on the big fppf site of `S`, with
values lifted to `Type (u + 1)`. -/
noncomputable abbrev morOnLocallyNoetherian (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
      IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op ⋙ X ⋙ uliftFunctor.{u + 1}

namespace ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : contractionFunctor c ≅ morOnLocallyNoetherian B S hS X)

/-- The first component of a transported triple is the inverse image of the first component. -/
theorem mapTriple_Z_eq_preimage {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁)
    (t : Triple c V₁) :
    (mapTriple c φ t).Z =
      Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' t.Z := rfl

/-- Naturality of the functorial bijection of Stacks 0GHC, read on elements and stated in the
types of the two functors. -/
theorem inv_app_map_morOnLocallyNoetherian {V₂ V₁ : LocallyNoetherianOver B S hS}
    (φ : V₂ ⟶ V₁) (y : (morOnLocallyNoetherian B S hS X).obj (Opposite.op V₁)) :
    α.inv.app (Opposite.op V₂) ((morOnLocallyNoetherian B S hS X).map φ.op y) =
      (contractionFunctor c).map φ.op (α.inv.app (Opposite.op V₁) y) :=
  NatTrans.naturality_apply α.inv φ.op y

/-- The triple `(Z, u', x̂)` that the functorial bijection of Stacks 0GHC attaches to a
morphism `ξ : V ⟶ X` from a locally Noetherian scheme `V` over `S`. -/
noncomputable def tripleOfMor (V : LocallyNoetherianOver B S hS)
    (ξ : yoneda.obj V.obj ⟶ X) : Triple c V.obj :=
  α.inv.app (Opposite.op V) (ULift.up (yonedaEquiv ξ))

/-- Naturality of the functorial bijection of Stacks 0GHC: a section restricted along `φ` is
matched with the triple transported along `φ`. -/
theorem inv_app_up_eq_mapTriple {V₂ V₁ : LocallyNoetherianOver B S hS} (φ : V₂.obj ⟶ V₁.obj)
    (x : X.obj (Opposite.op V₁.obj)) (y : X.obj (Opposite.op V₂.obj))
    (hy : X.map φ.op x = y) :
    α.inv.app (Opposite.op V₂) (ULift.up y) =
      mapTriple c φ (α.inv.app (Opposite.op V₁) (ULift.up x)) := by
  subst hy
  exact inv_app_map_morOnLocallyNoetherian c α (ObjectProperty.homMk φ) (ULift.up x)

/-- The triple `(Z, u', x̂)` that the functorial bijection of Stacks 0GHC attaches to a
field-valued point of `X`: the site object of such a point is the spectrum of a field, hence
a locally Noetherian scheme over `S`, and its section is a morphism into `X`. -/
noncomputable def tripleOfPoint (p : Space.FieldValuedPoint B S hS X) :
    Triple c p.siteObject :=
  α.inv.app (Opposite.op (p.locallyNoetherianObject B S hS)) (ULift.up p.value)

/-- When a field-valued point of `X` is the restriction of another along a morphism `f` of
field spectra, its triple is the transport along `f` of the other's. -/
theorem tripleOfPoint_of_dominates {p q : Space.FieldValuedPoint B S hS X}
    (f : q.siteObject ⟶ p.siteObject) (hf : X.map f.op p.value = q.value) :
    tripleOfPoint c α q = mapTriple c f (tripleOfPoint c α p) :=
  inv_app_up_eq_mapTriple c α (V₂ := q.locallyNoetherianObject B S hS)
    (V₁ := p.locallyNoetherianObject B S hS) f p.value q.value hf

/-- The condition on a field-valued point of `X` cutting out the subset `T ⊆ |X|` of the
solution: the triple attached to its section has first component all of the point space of
the spectrum of the field. -/
def MemContractedLocus (p : Space.FieldValuedPoint B S hS X) : Prop :=
  (tripleOfPoint c α p).Z = Set.univ

/-- The condition cutting out `T` is unchanged by passing to a field-valued extension. -/
theorem memContractedLocus_iff_of_dominates {p q : Space.FieldValuedPoint B S hS X}
    (f : q.siteObject ⟶ p.siteObject) (hf : X.map f.op p.value = q.value) :
    MemContractedLocus c α q ↔ MemContractedLocus c α p := by
  rw [MemContractedLocus, MemContractedLocus, tripleOfPoint_of_dominates c α f hf,
    Space.eq_univ_iff_class_tautological_mem B S hS q,
    Space.eq_univ_iff_class_tautological_mem B S hS p,
    mapTriple_Z_eq_preimage, Set.mem_preimage,
    (Space.subsingleton_points_yoneda_siteObject B S hS p).elim
      (Space.pointsMap B S hS (yoneda.obj q.siteObject) (yoneda.map f)
        ((Space.FieldValuedPoint.tautological B S hS q).class B S hS _))
      ((Space.FieldValuedPoint.tautological B S hS p).class B S hS _)]

/-- The condition cutting out `T` depends only on the point of `|X|` represented by a
field-valued point. -/
theorem memContractedLocus_iff_of_hasCommonExtension
    {p q : Space.FieldValuedPoint B S hS X}
    (h : Space.FieldValuedPoint.HasCommonExtension B S hS X p q) :
    MemContractedLocus c α p ↔ MemContractedLocus c α q := by
  obtain ⟨r, ⟨fp, hfp⟩, ⟨fq, hfq⟩⟩ := h
  exact (memContractedLocus_iff_of_dominates c α fp hfp).symm.trans
    (memContractedLocus_iff_of_dominates c α fq hfq)

/-- The subset `T ⊆ |X|` of the solution of Stacks 0GHC, built from the functorial bijection
`F(V) = Mor_S(V, X)`: a point lies in it when the triple `(Z, u', x̂)` matching its section
over the spectrum of a field has `Z` all of that spectrum. -/
noncomputable def contractedLocus : Set (Space.points B S hS X) :=
  {y | Quot.lift (MemContractedLocus c α)
    (fun _ _ h ↦ propext (memContractedLocus_iff_of_hasCommonExtension c α h)) y}

/-- Membership in the subset `T ⊆ |X|` of the solution, tested at a field-valued point. -/
theorem mem_contractedLocus_iff (p : Space.FieldValuedPoint B S hS X) :
    p.class B S hS X ∈ contractedLocus c α ↔ MemContractedLocus c α p := Iff.rfl

/-- A field-valued point of a locally Noetherian scheme `V` over `S` is carried by
`ξ : V ⟶ X` into the subset `T ⊆ |X|` of the solution exactly when it lies in the first
component of the triple matching `ξ`. -/
theorem memContractedLocus_map_iff {V : LocallyNoetherianOver B S hS}
    (ξ : yoneda.obj V.obj ⟶ X) (p : Space.FieldValuedPoint B S hS (yoneda.obj V.obj)) :
    MemContractedLocus c α (Space.FieldValuedPoint.map B S hS _ ξ p) ↔
      p.class B S hS (yoneda.obj V.obj) ∈ (tripleOfMor c α V ξ).Z := by
  have htr : tripleOfPoint c α (Space.FieldValuedPoint.map B S hS _ ξ p) =
      mapTriple c p.value (tripleOfMor c α V ξ) :=
    inv_app_up_eq_mapTriple c α
      (V₂ := (Space.FieldValuedPoint.map B S hS _ ξ p).locallyNoetherianObject B S hS)
      (V₁ := V) p.value (yonedaEquiv ξ) _ (map_yonedaEquiv ξ p.value)
  rw [MemContractedLocus, htr, Space.eq_univ_iff_class_tautological_mem B S hS
      (Space.FieldValuedPoint.map B S hS _ ξ p),
    mapTriple_Z_eq_preimage]
  exact iff_of_eq (congrArg (fun z ↦ z ∈ (tripleOfMor c α V ξ).Z)
    (Space.FieldValuedPoint.pointsMap_yoneda_map_eq_class B S hS p
      ((Space.FieldValuedPoint.tautological B S hS p).class B S hS _)))

/-- The inverse image of the subset `T ⊆ |X|` of the solution under a morphism `ξ : V ⟶ X` from
a locally Noetherian scheme `V` over `S` is the first component `Z` of the triple `(Z, u', x̂)`
that the functorial bijection matches with `ξ`. -/
theorem preimage_contractedLocus (V : LocallyNoetherianOver B S hS)
    (ξ : yoneda.obj V.obj ⟶ X) :
    Space.pointsMap B S hS (yoneda.obj V.obj) ξ ⁻¹' contractedLocus c α =
      (tripleOfMor c α V ξ).Z := by
  ext y
  induction y using Quot.ind with | _ p =>
  exact memContractedLocus_map_iff c α ξ p

/-- The inverse image of the subset `T ⊆ |X|` of the solution on a locally Noetherian scheme
over `S` is closed. -/
theorem isClosed_preimage_contractedLocus (V : LocallyNoetherianOver B S hS)
    (ξ : yoneda.obj V.obj ⟶ X) :
    IsClosed (Space.pointsMap B S hS (yoneda.obj V.obj) ξ ⁻¹' contractedLocus c α) := by
  rw [preimage_contractedLocus]
  exact (tripleOfMor c α V ξ).isClosed_Z

/-- A subset of `|X|` whose inverse image under every morphism from a locally Noetherian scheme
over `S` is the first component of the matching triple is the subset `T`. -/
theorem eq_contractedLocus_of_preimage (T : Set (Space.points B S hS X))
    (hT : ∀ (V : LocallyNoetherianOver B S hS) (ξ : yoneda.obj V.obj ⟶ X),
      Space.pointsMap B S hS (yoneda.obj V.obj) ξ ⁻¹' T = (tripleOfMor c α V ξ).Z) :
    T = contractedLocus c α := by
  ext y
  induction y using Quot.ind with | _ p =>
  have key := (hT (p.locallyNoetherianObject B S hS) (yonedaEquiv.symm p.value)).trans
    (preimage_contractedLocus c α (p.locallyNoetherianObject B S hS)
      (yonedaEquiv.symm p.value)).symm
  have hA : ∀ W : Set (Space.points B S hS X),
      ((Space.FieldValuedPoint.tautological B S hS p).class B S hS
            (yoneda.obj p.siteObject) ∈
          Space.pointsMap B S hS (yoneda.obj p.siteObject)
            (yonedaEquiv.symm p.value) ⁻¹' W) ↔ p.class B S hS X ∈ W := by
    intro W
    rw [Set.mem_preimage, Space.FieldValuedPoint.pointsMap_class_tautological B S hS p]
  exact ((hA T).symm.trans (Set.ext_iff.mp key _)).trans (hA _)

end ContractionSituation

end Artin

end AlgebraicGeometry

end
