module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealizationInv
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealizationPoint

/-!
# Transport across the comparison of two restrictions

Let `G` be a groupoid in algebraic spaces, let `g : U₂ ⟶ U` be a morphism to its object space
and let `E : U₁ ≅ U₂` be an isomorphism.  The arrow spaces of a realization of the restriction
along `E.hom ≫ g` and of a realization of the restriction along `g` are identified by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Restriction.arrowsCompIso`, and their object spaces
by the isomorphism read through the two equalities the realizations record.  That identification
carries composition to composition, so an open finite subgroupoid and a strong splitting of the
one restriction pull back to an open finite subgroupoid and a strong splitting of the other.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Restriction.objectsCompHom` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Restriction.objectsCompInv`: the two mutually
  inverse comparisons of the object spaces of the two restrictions.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid.compIso`: the preimage of an
  open finite subgroupoid under the comparison of the arrow spaces, again an open finite
  subgroupoid.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.StrongSplitting.compIso`: the preimage of a strong
  splitting at a point, a strong splitting at any point the comparison of the object spaces
  carries to it.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Restriction.arrowsCompIso_hom_compose`: the
  identification of the two arrow spaces carries the composite of a composable pair to the
  composite of the images.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid.compIso_arrows` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.StrongSplitting.compIso_toOpenFiniteSubgroupoid`:
  the arrows of the transported subgroupoid are the preimage of the arrows, and the transported
  strong splitting has the transported subgroupoid underlying it.

## Implementation notes

Finiteness of the restricted source and target of the preimage is read off the corresponding
finiteness for the subgroupoid: the comparison of the arrows of the subgroupoid with the arrows
of its preimage is a base change of the comparison of the arrow spaces, hence an isomorphism, and
the two restricted sources agree up to that isomorphism and the comparison of the object spaces.
The groupoid obtained by evaluating the preimage at a test object is the one induced along the
comparison of the object spaces from the evaluation of the subgroupoid, which is what
`Deformation.PointwiseGroupoid.ofIndexing` constructs.

## References

* [Stacks Project, Tag 02VB](https://stacks.math.columbia.edu/tag/02VB)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS B}
  {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂) {g : U₂ ⟶ G.objects}
  (R : Restriction G g) (R' : Restriction G (E.hom ≫ g))

/-- The comparison of the object spaces of the two restrictions: the isomorphism, read between
the two object spaces through the equalities the two realizations record. -/
def Restriction.objectsCompHom : R'.groupoid.objects ⟶ R.groupoid.objects :=
  eqToHom R'.objects_eq ≫ E.hom ≫ eqToHom R.objects_eq.symm

/-- The source of the image of an arrow under the comparison of arrow spaces. -/
theorem Restriction.arrowsCompIso_app_source (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : R'.groupoid.arrows.obj.obj T) :
    R.groupoid.source.hom.app T ((Restriction.arrowsCompIso E R R').hom.hom.app T a) =
      (Restriction.objectsCompHom E R R').hom.app T
        (R'.groupoid.source.hom.app T a) := by
  have h := congrArg (fun m : R'.groupoid.arrows ⟶ R.groupoid.objects => m.hom)
    (Restriction.arrowsCompIso_hom_comp_source E R R')
  exact congrArg (fun k => k a) (NatTrans.congr_app h T)

/-- The target of the image of an arrow under the comparison of arrow spaces. -/
theorem Restriction.arrowsCompIso_app_target (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : R'.groupoid.arrows.obj.obj T) :
    R.groupoid.target.hom.app T ((Restriction.arrowsCompIso E R R').hom.hom.app T a) =
      (Restriction.objectsCompHom E R R').hom.app T
        (R'.groupoid.target.hom.app T a) := by
  have h := congrArg (fun m : R'.groupoid.arrows ⟶ R.groupoid.objects => m.hom)
    (Restriction.arrowsCompIso_hom_comp_target E R R')
  exact congrArg (fun k => k a) (NatTrans.congr_app h T)

/-- The ambient arrow underlying the image of an arrow under the comparison of arrow spaces. -/
theorem Restriction.arrowsCompIso_app_mapArrows (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : R'.groupoid.arrows.obj.obj T) :
    R.hom.toGroupoidHom.mapArrows.app T
        ((Restriction.arrowsCompIso E R R').hom.hom.app T a) =
      R'.hom.toGroupoidHom.mapArrows.app T a :=
  congrArg (fun k => k a)
    (NatTrans.congr_app (Restriction.arrowsCompIso_hom_comp_mapArrows E R R') T)

/-- **The comparison of two restrictions carries composition to composition.**

Both sides are arrows of the restriction along `g` with the same endpoints — the source of the
image of the arrow composed first and the target of the image of the arrow composed last — and
with the same underlying arrow of the ambient groupoid, namely the ambient composite of the two
underlying arrows; so they agree by the uniqueness principle for arrows of a restriction. -/
theorem Restriction.arrowsCompIso_hom_compose (T : (BigFppfOver C S hS)ᵒᵖ)
    (a b : R'.groupoid.arrows.obj.obj T)
    (h : R'.groupoid.source.hom.app T a = R'.groupoid.target.hom.app T b)
    (h' : R.groupoid.source.hom.app T ((Restriction.arrowsCompIso E R R').hom.hom.app T a) =
      R.groupoid.target.hom.app T ((Restriction.arrowsCompIso E R R').hom.hom.app T b)) :
    (Restriction.arrowsCompIso E R R').hom.hom.app T
        (R'.groupoid.toGroupoidInFunctors.compose T a b h) =
      R.groupoid.toGroupoidInFunctors.compose T
        ((Restriction.arrowsCompIso E R R').hom.hom.app T a)
        ((Restriction.arrowsCompIso E R R').hom.hom.app T b) h' := by
  have hcs := Deformation.GroupoidInFunctors.compose_source
    R'.groupoid.toGroupoidInFunctors T (R'.groupoid.source.hom.app T b)
    (R'.groupoid.target.hom.app T b) (R'.groupoid.target.hom.app T a) b a rfl rfl h rfl
  have hct := Deformation.GroupoidInFunctors.compose_target
    R'.groupoid.toGroupoidInFunctors T (R'.groupoid.source.hom.app T b)
    (R'.groupoid.target.hom.app T b) (R'.groupoid.target.hom.app T a) b a rfl rfl h rfl
  refine restriction_arrow_ext G R T
    (R.groupoid.source.hom.app T ((Restriction.arrowsCompIso E R R').hom.hom.app T b))
    (R.groupoid.target.hom.app T ((Restriction.arrowsCompIso E R R').hom.hom.app T a))
    _ _ ?_ ?_ ?_ ?_ ?_
  · refine (Restriction.arrowsCompIso_app_source E R R' T _).trans ?_
    refine Eq.trans ?_ (Restriction.arrowsCompIso_app_source E R R' T b).symm
    exact congrArg ((Restriction.objectsCompHom E R R').hom.app T) hcs
  · refine (Restriction.arrowsCompIso_app_target E R R' T _).trans ?_
    refine Eq.trans ?_ (Restriction.arrowsCompIso_app_target E R R' T a).symm
    exact congrArg ((Restriction.objectsCompHom E R R').hom.app T) hct
  · exact Deformation.GroupoidInFunctors.compose_source R.groupoid.toGroupoidInFunctors T
      (R.groupoid.source.hom.app T ((Restriction.arrowsCompIso E R R').hom.hom.app T b))
      (R.groupoid.target.hom.app T ((Restriction.arrowsCompIso E R R').hom.hom.app T b))
      (R.groupoid.target.hom.app T ((Restriction.arrowsCompIso E R R').hom.hom.app T a))
      ((Restriction.arrowsCompIso E R R').hom.hom.app T b)
      ((Restriction.arrowsCompIso E R R').hom.hom.app T a) rfl rfl h' rfl
  · exact Deformation.GroupoidInFunctors.compose_target R.groupoid.toGroupoidInFunctors T
      (R.groupoid.source.hom.app T ((Restriction.arrowsCompIso E R R').hom.hom.app T b))
      (R.groupoid.target.hom.app T ((Restriction.arrowsCompIso E R R').hom.hom.app T b))
      (R.groupoid.target.hom.app T ((Restriction.arrowsCompIso E R R').hom.hom.app T a))
      ((Restriction.arrowsCompIso E R R').hom.hom.app T b)
      ((Restriction.arrowsCompIso E R R').hom.hom.app T a) rfl rfl h' rfl
  · refine (Restriction.arrowsCompIso_app_mapArrows E R R' T _).trans ?_
    refine (R'.hom.toGroupoidHom.map_comp T a b h).symm.trans ?_
    refine Eq.trans ?_ (R.hom.toGroupoidHom.map_comp T _ _ h')
    exact Deformation.GroupoidInFunctors.compose_eq_of_arrows_eq G.toGroupoidInFunctors T _ _
      (Restriction.arrowsCompIso_app_mapArrows E R R' T a).symm
      (Restriction.arrowsCompIso_app_mapArrows E R R' T b).symm

/-! ### The comparison of the object spaces is invertible -/

/-- The inverse comparison of the object spaces of the two restrictions. -/
def Restriction.objectsCompInv : R.groupoid.objects ⟶ R'.groupoid.objects :=
  eqToHom R.objects_eq ≫ E.inv ≫ eqToHom R'.objects_eq.symm

/-- The two comparisons of the object spaces are mutually inverse. -/
theorem Restriction.objectsCompHom_comp_objectsCompInv :
    Restriction.objectsCompHom E R R' ≫ Restriction.objectsCompInv E R R' =
      𝟙 R'.groupoid.objects := by
  change (eqToHom R'.objects_eq ≫ E.hom ≫ eqToHom R.objects_eq.symm) ≫
    eqToHom R.objects_eq ≫ E.inv ≫ eqToHom R'.objects_eq.symm = 𝟙 _
  simp

/-- The comparison of the object spaces is an isomorphism, being an isomorphism of spaces read
through the two equalities the realizations record. -/
instance Restriction.isIso_objectsCompHom :
    IsIso (Restriction.objectsCompHom E R R') := by
  change IsIso (eqToHom R'.objects_eq ≫ E.hom ≫ eqToHom R.objects_eq.symm)
  infer_instance

/-- A section of the object space is recovered from its image under the comparison. -/
theorem Restriction.objectsCompInv_hom_app (T : (BigFppfOver C S hS)ᵒᵖ)
    (x : R'.groupoid.objects.obj.obj T) :
    (Restriction.objectsCompInv E R R').hom.app T
        ((Restriction.objectsCompHom E R R').hom.app T x) = x :=
  congrArg (fun k => k x) (NatTrans.congr_app (congrArg
    (fun m : R'.groupoid.objects ⟶ R'.groupoid.objects => m.hom)
    (Restriction.objectsCompHom_comp_objectsCompInv E R R')) T)

/-- The comparison of the object spaces is injective on sections. -/
theorem Restriction.objectsCompHom_app_injective (T : (BigFppfOver C S hS)ᵒᵖ) :
    Function.Injective ((Restriction.objectsCompHom E R R').hom.app T) := fun x y h =>
  (Restriction.objectsCompInv_hom_app E R R' T x).symm.trans
    ((congrArg ((Restriction.objectsCompInv E R R').hom.app T) h).trans
      (Restriction.objectsCompInv_hom_app E R R' T y))

/-! ### The comparison of the arrow spaces, read on presheaves -/

/-- The comparison of the arrow spaces carries the source to the source up to the comparison of
the object spaces, read as an equality of morphisms of presheaves. -/
theorem Restriction.arrowsCompIso_hom_hom_comp_source :
    (Restriction.arrowsCompIso E R R').hom.hom ≫ R.groupoid.source.hom =
      R'.groupoid.source.hom ≫ (Restriction.objectsCompHom E R R').hom :=
  congrArg (fun m : R'.groupoid.arrows ⟶ R.groupoid.objects => m.hom)
    (Restriction.arrowsCompIso_hom_comp_source E R R')

/-- The comparison of the arrow spaces carries the target to the target up to the comparison of
the object spaces, read as an equality of morphisms of presheaves. -/
theorem Restriction.arrowsCompIso_hom_hom_comp_target :
    (Restriction.arrowsCompIso E R R').hom.hom ≫ R.groupoid.target.hom =
      R'.groupoid.target.hom ≫ (Restriction.objectsCompHom E R R').hom :=
  congrArg (fun m : R'.groupoid.arrows ⟶ R.groupoid.objects => m.hom)
    (Restriction.arrowsCompIso_hom_comp_target E R R')

/-- A section of the arrow space is recovered from its image under the comparison. -/
theorem Restriction.arrowsCompIso_inv_hom_app (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : R'.groupoid.arrows.obj.obj T) :
    (Restriction.arrowsCompIso E R R').inv.hom.app T
        ((Restriction.arrowsCompIso E R R').hom.hom.app T a) = a :=
  congrArg (fun k => k a) (NatTrans.congr_app
    (ObjectProperty.isoHom_inv_id_hom (Restriction.arrowsCompIso E R R')) T)

/-- A section of the arrow space of the restriction along `g` is the image of its preimage under
the comparison. -/
theorem Restriction.arrowsCompIso_hom_inv_app (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : R.groupoid.arrows.obj.obj T) :
    (Restriction.arrowsCompIso E R R').hom.hom.app T
        ((Restriction.arrowsCompIso E R R').inv.hom.app T a) = a :=
  congrArg (fun k => k a) (NatTrans.congr_app
    (ObjectProperty.isoInv_hom_id_hom (Restriction.arrowsCompIso E R R')) T)

/-! ### Two transport principles -/

/-- Finiteness of a morphism of algebraic spaces transported across isomorphisms of the source
and of the target. -/
theorem isFinite_of_comp_isIso_eq {X Y X' Y' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (a : X' ⟶ X) [IsIso a] {f : X ⟶ Y} (b : Y' ⟶ Y) [IsIso b] (h : X' ⟶ Y')
    (he : h ≫ b = a ≫ f) (hf : Space.IsFinite C S hS f) : Space.IsFinite C S hS h := by
  intro U hU ξ
  obtain ⟨V, p, i, hV, hp, hpb⟩ := hf U hU (ξ ≫ b)
  refine ⟨V, p, i ≫ inv a, hV, hp, ?_⟩
  refine hpb.of_iso (Iso.refl _) (asIso a).symm (Iso.refl _) (asIso b).symm ?_ ?_ ?_ ?_
  · simp
  · simp
  · rw [Iso.symm_hom, Iso.symm_hom, asIso_inv, asIso_inv, IsIso.comp_inv_eq, Category.assoc, he,
      IsIso.inv_hom_id_assoc]
  · simp

/-- Points of presheaves: if `e ≫ f` is the identity then `f` undoes `e` on points. -/
private theorem pointsMap_pointsMap_of_comp_eq_id {F F' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (e : F ⟶ F') (f : F' ⟶ F) (h : e ≫ f = 𝟙 F) (z : Space.points C S hS F) :
    Space.pointsMap C S hS F' f (Space.pointsMap C S hS F e z) = z := by
  have h1 := Space.pointsMap_comp C S hS F e f
  rw [h, Space.pointsMap_id] at h1
  exact (congrFun h1 z).symm

/-- An isomorphism of presheaves on the big fppf site is injective on points: its inverse undoes
it on points. -/
theorem pointsMap_injective_of_isIso {F F' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ F')
    [IsIso e] : Function.Injective (Space.pointsMap C S hS F e) := by
  have h0 := pointsMap_pointsMap_of_comp_eq_id e (inv e) (IsIso.hom_inv_id e)
  exact fun x y h =>
    (h0 x).symm.trans ((congrArg (Space.pointsMap C S hS F' (inv e)) h).trans (h0 y))

/-! ### Transporting an open finite subgroupoid -/

/-- The groupoid in presheaves of an open finite subgroupoid: the ambient object space together
with the arrows of the subgroupoid, its restricted source and target, and its composition. -/
def OpenFiniteSubgroupoid.toGroupoidInFunctors {K : GroupoidInAlgebraicSpaces C S hS B}
    (P : OpenFiniteSubgroupoid K) : Deformation.GroupoidInFunctors ((BigFppfOver C S hS)ᵒᵖ) where
  objects := K.objects.obj
  arrows := P.arrows.toFunctor
  source := P.arrows.ι ≫ K.source.hom
  target := P.arrows.ι ≫ K.target.hom
  comp := P.comp
  pointwiseGroupoid := P.pointwiseGroupoid

/-- The comparison of the arrows of an open finite subgroupoid with the arrows of its preimage is
an isomorphism, being a base change of the comparison of the arrow spaces. -/
theorem OpenFiniteSubgroupoid.isIso_fromPreimage (P : OpenFiniteSubgroupoid R.groupoid) :
    IsIso (P.arrows.fromPreimage (Restriction.arrowsCompIso E R R').hom.hom) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := MorphismProperty.isomorphisms ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u))
    (Subfunctor.isPullback_preimage (Restriction.arrowsCompIso E R R').hom.hom P.arrows).flip
    (MorphismProperty.isomorphisms.infer_property _)

/-- **The arrows of an open finite subgroupoid are closed under the transported composition.**
The comparison of the arrow spaces carries the composite of two arrows whose images lie in the
subgroupoid to the composite of those images, which lies in the subgroupoid. -/
theorem OpenFiniteSubgroupoid.compIso_mem (P : OpenFiniteSubgroupoid R.groupoid)
    (T : (BigFppfOver C S hS)ᵒᵖ) (a b : R'.groupoid.arrows.obj.obj T)
    (ha : (Restriction.arrowsCompIso E R R').hom.hom.app T a ∈ P.arrows.obj T)
    (hb : (Restriction.arrowsCompIso E R R').hom.hom.app T b ∈ P.arrows.obj T)
    (h : R'.groupoid.source.hom.app T a = R'.groupoid.target.hom.app T b) :
    (Restriction.arrowsCompIso E R R').hom.hom.app T
        (R'.groupoid.toGroupoidInFunctors.compose T a b h) ∈ P.arrows.obj T := by
  have h' : R.groupoid.source.hom.app T
        ((Restriction.arrowsCompIso E R R').hom.hom.app T a) =
      R.groupoid.target.hom.app T
        ((Restriction.arrowsCompIso E R R').hom.hom.app T b) :=
    (Restriction.arrowsCompIso_app_source E R R' T a).trans
      ((congrArg ((Restriction.objectsCompHom E R R').hom.app T) h).trans
        (Restriction.arrowsCompIso_app_target E R R' T b).symm)
  have hp : P.arrows.ι.app T (P.comp.app T
      (show (Deformation.composableArrows R.groupoid.objects.obj P.arrows.toFunctor
          (P.arrows.ι ≫ R.groupoid.source.hom)
          (P.arrows.ι ≫ R.groupoid.target.hom)).obj T from
        ⟨(⟨_, ha⟩, ⟨_, hb⟩), h'⟩)) ∈ P.arrows.obj T :=
    (P.comp.app T ⟨(⟨_, ha⟩, ⟨_, hb⟩), h'⟩).2
  rw [P.comp_restricts T ⟨(⟨_, ha⟩, ⟨_, hb⟩), h'⟩] at hp
  rw [Restriction.arrowsCompIso_hom_compose E R R' T a b h h']
  exact hp

/-- A composable pair of arrows of the preimage of an open finite subgroupoid, read as a
composable pair of arrows of the ambient groupoid. -/
def OpenFiniteSubgroupoid.compIsoComposable (P : OpenFiniteSubgroupoid R.groupoid) :
    Deformation.composableArrows R'.groupoid.objects.obj
        (P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).toFunctor
        ((P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).ι ≫
          R'.groupoid.source.hom)
        ((P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).ι ≫
          R'.groupoid.target.hom) ⟶
      Deformation.composableArrows R'.groupoid.objects.obj R'.groupoid.arrows.obj
        R'.groupoid.source.hom R'.groupoid.target.hom where
  app T := ↾fun p => ⟨(p.1.1.1, p.1.2.1), p.2⟩
  naturality T T' f := by
    ext p
    rfl

/-- The transported composition lands in the preimage of the subgroupoid. -/
theorem OpenFiniteSubgroupoid.range_compIsoComposable_le
    (P : OpenFiniteSubgroupoid R.groupoid) :
    Subfunctor.range (OpenFiniteSubgroupoid.compIsoComposable E R R' P ≫
        R'.groupoid.toGroupoidInFunctors.comp) ≤
      P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom := by
  intro T x hx
  obtain ⟨p, rfl⟩ := hx
  change (Restriction.arrowsCompIso E R R').hom.hom.app T
      (R'.groupoid.toGroupoidInFunctors.compose T p.1.1.1 p.1.2.1 p.2) ∈ P.arrows.obj T
  exact OpenFiniteSubgroupoid.compIso_mem E R R' P T p.1.1.1 p.1.2.1 p.1.1.2 p.1.2.2 p.2

/-- Finiteness of a restricted endpoint map of the subgroupoid transfers to its preimage, for any
pair of maps to the object spaces matched by the comparisons. -/
private theorem isFinite_preimage_comp_of_comp_eq (P : OpenFiniteSubgroupoid R.groupoid)
    {f : R.groupoid.arrows.obj ⟶ R.groupoid.objects.obj}
    {f' : R'.groupoid.arrows.obj ⟶ R'.groupoid.objects.obj}
    (he : (Restriction.arrowsCompIso E R R').hom.hom ≫ f =
      f' ≫ (Restriction.objectsCompHom E R R').hom)
    (hf : Space.IsFinite C S hS (P.arrows.ι ≫ f)) :
    Space.IsFinite C S hS
      ((P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).ι ≫ f') := by
  have := OpenFiniteSubgroupoid.isIso_fromPreimage E R R' P
  refine isFinite_of_comp_isIso_eq
    (P.arrows.fromPreimage (Restriction.arrowsCompIso E R R').hom.hom)
    (b := (Restriction.objectsCompHom E R R').hom) _ ?_ hf
  rw [Category.assoc, ← he, ← Category.assoc,
    ← Subfunctor.fromPreimage_ι P.arrows (Restriction.arrowsCompIso E R R').hom.hom,
    Category.assoc]

/-- The restricted source of the preimage of an open finite subgroupoid is finite. -/
theorem OpenFiniteSubgroupoid.isFinite_compIso_source
    (P : OpenFiniteSubgroupoid R.groupoid) :
    Space.IsFinite C S hS
      ((P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).ι ≫
        R'.groupoid.source.hom) :=
  isFinite_preimage_comp_of_comp_eq E R R' P
    (Restriction.arrowsCompIso_hom_hom_comp_source E R R') P.source_finite

/-- The restricted target of the preimage of an open finite subgroupoid is finite. -/
theorem OpenFiniteSubgroupoid.isFinite_compIso_target
    (P : OpenFiniteSubgroupoid R.groupoid) :
    Space.IsFinite C S hS
      ((P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).ι ≫
        R'.groupoid.target.hom) :=
  isFinite_preimage_comp_of_comp_eq E R R' P
    (Restriction.arrowsCompIso_hom_hom_comp_target E R R') P.target_finite

/-! ### The arrows of the preimage -/

/-- The arrows of an open finite subgroupoid over a test object correspond to the arrows of its
preimage, by the comparison of the two arrow spaces. -/
def OpenFiniteSubgroupoid.compIsoArrows (P : OpenFiniteSubgroupoid R.groupoid)
    (T : (BigFppfOver C S hS)ᵒᵖ) :
    P.arrows.toFunctor.obj T ≃
      (P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).toFunctor.obj T where
  toFun a := ⟨(Restriction.arrowsCompIso E R R').inv.hom.app T a.1, by
    change (Restriction.arrowsCompIso E R R').hom.hom.app T
        ((Restriction.arrowsCompIso E R R').inv.hom.app T a.1) ∈ P.arrows.obj T
    rw [Restriction.arrowsCompIso_hom_inv_app]
    exact a.2⟩
  invFun b := ⟨(Restriction.arrowsCompIso E R R').hom.hom.app T b.1, b.2⟩
  left_inv a := Subtype.ext (Restriction.arrowsCompIso_hom_inv_app E R R' T a.1)
  right_inv b := Subtype.ext (Restriction.arrowsCompIso_inv_hom_app E R R' T b.1)

/-- The comparison of the object spaces carries the source of the preimage of an arrow of the
subgroupoid to the source of that arrow. -/
theorem OpenFiniteSubgroupoid.objectsCompHom_source_compIsoArrows
    (P : OpenFiniteSubgroupoid R.groupoid) (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : P.arrows.toFunctor.obj T) :
    (Restriction.objectsCompHom E R R').hom.app T
        (R'.groupoid.source.hom.app T
          ((Restriction.arrowsCompIso E R R').inv.hom.app T a.1)) =
      R.groupoid.source.hom.app T a.1 :=
  (Restriction.arrowsCompIso_app_source E R R' T _).symm.trans
    (congrArg (R.groupoid.source.hom.app T)
      (Restriction.arrowsCompIso_hom_inv_app E R R' T a.1))

/-- The comparison of the object spaces carries the target of the preimage of an arrow of the
subgroupoid to the target of that arrow. -/
theorem OpenFiniteSubgroupoid.objectsCompHom_target_compIsoArrows
    (P : OpenFiniteSubgroupoid R.groupoid) (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : P.arrows.toFunctor.obj T) :
    (Restriction.objectsCompHom E R R').hom.app T
        (R'.groupoid.target.hom.app T
          ((Restriction.arrowsCompIso E R R').inv.hom.app T a.1)) =
      R.groupoid.target.hom.app T a.1 :=
  (Restriction.arrowsCompIso_app_target E R R' T _).symm.trans
    (congrArg (R.groupoid.target.hom.app T)
      (Restriction.arrowsCompIso_hom_inv_app E R R' T a.1))

/-- An arrow of the subgroupoid has source the image of a section exactly when its preimage has
source that section. -/
theorem OpenFiniteSubgroupoid.compIsoArrows_source_iff
    (P : OpenFiniteSubgroupoid R.groupoid) (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : P.arrows.toFunctor.obj T) (x : R'.groupoid.objects.obj.obj T) :
    R.groupoid.source.hom.app T a.1 =
        (Restriction.objectsCompHom E R R').hom.app T x ↔
      R'.groupoid.source.hom.app T
        ((Restriction.arrowsCompIso E R R').inv.hom.app T a.1) = x := by
  rw [← OpenFiniteSubgroupoid.objectsCompHom_source_compIsoArrows E R R' P T a]
  exact (Restriction.objectsCompHom_app_injective E R R' T).eq_iff

/-- An arrow of the subgroupoid has target the image of a section exactly when its preimage has
target that section. -/
theorem OpenFiniteSubgroupoid.compIsoArrows_target_iff
    (P : OpenFiniteSubgroupoid R.groupoid) (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : P.arrows.toFunctor.obj T) (y : R'.groupoid.objects.obj.obj T) :
    R.groupoid.target.hom.app T a.1 =
        (Restriction.objectsCompHom E R R').hom.app T y ↔
      R'.groupoid.target.hom.app T
        ((Restriction.arrowsCompIso E R R').inv.hom.app T a.1) = y := by
  rw [← OpenFiniteSubgroupoid.objectsCompHom_target_compIsoArrows E R R' P T a]
  exact (Restriction.objectsCompHom_app_injective E R R' T).eq_iff

/-- Arrows of an open finite subgroupoid with prescribed endpoints correspond to arrows of its
preimage with the endpoints the comparison of the object spaces matches. -/
def OpenFiniteSubgroupoid.compIsoArrowEquiv (P : OpenFiniteSubgroupoid R.groupoid)
    (T : (BigFppfOver C S hS)ᵒᵖ) (x y : R'.groupoid.objects.obj.obj T) :
    { a : P.arrows.toFunctor.obj T //
        (P.arrows.ι ≫ R.groupoid.source.hom).app T a =
            (Restriction.objectsCompHom E R R').hom.app T x ∧
          (P.arrows.ι ≫ R.groupoid.target.hom).app T a =
            (Restriction.objectsCompHom E R R').hom.app T y } ≃
      { a : (P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).toFunctor.obj T //
        ((P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).ι ≫
            R'.groupoid.source.hom).app T a = x ∧
          ((P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).ι ≫
            R'.groupoid.target.hom).app T a = y } :=
  Equiv.subtypeEquiv (OpenFiniteSubgroupoid.compIsoArrows E R R' P T) fun a =>
    and_congr (OpenFiniteSubgroupoid.compIsoArrows_source_iff E R R' P T a x)
      (OpenFiniteSubgroupoid.compIsoArrows_target_iff E R R' P T a y)

/-! ### The composition of the preimage -/

/-- The composition of the preimage of an open finite subgroupoid: the composite, in the
restriction along `E.hom ≫ g`, of the two arrows of the pair. -/
def OpenFiniteSubgroupoid.compIsoComp (P : OpenFiniteSubgroupoid R.groupoid) :
    Deformation.composableArrows R'.groupoid.objects.obj
        (P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).toFunctor
        ((P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).ι ≫
          R'.groupoid.source.hom)
        ((P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).ι ≫
          R'.groupoid.target.hom) ⟶
      (P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).toFunctor :=
  Subfunctor.lift (OpenFiniteSubgroupoid.compIsoComposable E R R' P ≫
      R'.groupoid.toGroupoidInFunctors.comp)
    (OpenFiniteSubgroupoid.range_compIsoComposable_le E R R' P)

/-- The comparison of the arrow spaces carries the composite of the preimages of two composable
arrows to the composite of those arrows. -/
theorem Restriction.arrowsCompIso_hom_compose_inv (T : (BigFppfOver C S hS)ᵒᵖ)
    (a b : R.groupoid.arrows.obj.obj T)
    (h : R'.groupoid.source.hom.app T
          ((Restriction.arrowsCompIso E R R').inv.hom.app T a) =
        R'.groupoid.target.hom.app T
          ((Restriction.arrowsCompIso E R R').inv.hom.app T b))
    (h' : R.groupoid.source.hom.app T a = R.groupoid.target.hom.app T b) :
    (Restriction.arrowsCompIso E R R').hom.hom.app T
        (R'.groupoid.toGroupoidInFunctors.compose T
          ((Restriction.arrowsCompIso E R R').inv.hom.app T a)
          ((Restriction.arrowsCompIso E R R').inv.hom.app T b) h) =
      R.groupoid.toGroupoidInFunctors.compose T a b h' := by
  have h'' : R.groupoid.source.hom.app T ((Restriction.arrowsCompIso E R R').hom.hom.app T
        ((Restriction.arrowsCompIso E R R').inv.hom.app T a)) =
      R.groupoid.target.hom.app T ((Restriction.arrowsCompIso E R R').hom.hom.app T
        ((Restriction.arrowsCompIso E R R').inv.hom.app T b)) :=
    (congrArg (R.groupoid.source.hom.app T)
      (Restriction.arrowsCompIso_hom_inv_app E R R' T a)).trans
      (h'.trans (congrArg (R.groupoid.target.hom.app T)
        (Restriction.arrowsCompIso_hom_inv_app E R R' T b)).symm)
  refine (Restriction.arrowsCompIso_hom_compose E R R' T _ _ h h'').trans ?_
  exact Deformation.GroupoidInFunctors.compose_eq_of_arrows_eq
    R.groupoid.toGroupoidInFunctors T h'' h'
    (Restriction.arrowsCompIso_hom_inv_app E R R' T a)
    (Restriction.arrowsCompIso_hom_inv_app E R R' T b)

/-- The composition of the preimage of an open finite subgroupoid is the preimage of its
composition: composing the preimages of two composable arrows gives the preimage of their
composite. -/
theorem OpenFiniteSubgroupoid.compIsoComp_app (P : OpenFiniteSubgroupoid R.groupoid)
    (T : (BigFppfOver C S hS)ᵒᵖ) (a b : P.arrows.toFunctor.obj T)
    (h : (P.arrows.ι ≫ R.groupoid.source.hom).app T a =
      (P.arrows.ι ≫ R.groupoid.target.hom).app T b)
    (h₀ : ((P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).ι ≫
          R'.groupoid.source.hom).app T
        (OpenFiniteSubgroupoid.compIsoArrows E R R' P T a) =
      ((P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).ι ≫
          R'.groupoid.target.hom).app T
        (OpenFiniteSubgroupoid.compIsoArrows E R R' P T b)) :
    (OpenFiniteSubgroupoid.compIsoComp E R R' P).app T
        ⟨(OpenFiniteSubgroupoid.compIsoArrows E R R' P T a,
          OpenFiniteSubgroupoid.compIsoArrows E R R' P T b), h₀⟩ =
      OpenFiniteSubgroupoid.compIsoArrows E R R' P T (P.comp.app T ⟨(a, b), h⟩) := by
  refine Subtype.ext (Eq.symm ?_)
  refine (congrArg (fun w => (Restriction.arrowsCompIso E R R').inv.hom.app T w)
    ((P.comp_restricts T ⟨(a, b), h⟩).trans
      (Restriction.arrowsCompIso_hom_compose_inv E R R' T a.1 b.1 h₀ h).symm)).trans ?_
  exact Restriction.arrowsCompIso_inv_hom_app E R R' T _

/-- **Evaluating the preimage of an open finite subgroupoid gives a groupoid.**  It is the
groupoid induced, along the comparison of the object spaces, from the evaluation of the
subgroupoid. -/
theorem OpenFiniteSubgroupoid.nonempty_pointwiseGroupoid_compIso
    (P : OpenFiniteSubgroupoid R.groupoid) (T : (BigFppfOver C S hS)ᵒᵖ) :
    Nonempty (Deformation.PointwiseGroupoid
      (((P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).ι ≫
        R'.groupoid.source.hom).app T)
      (((P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).ι ≫
        R'.groupoid.target.hom).app T)
      (fun p => (OpenFiniteSubgroupoid.compIsoComp E R R' P).app T p)) := by
  refine ⟨Deformation.PointwiseGroupoid.ofIndexing
    (D := (OpenFiniteSubgroupoid.toGroupoidInFunctors P).Evaluation T)
    (fun x => (Restriction.objectsCompHom E R R').hom.app T x) _ _ _
    (fun x y => ((OpenFiniteSubgroupoid.toGroupoidInFunctors P).evaluationArrowEquiv T
        ((Restriction.objectsCompHom E R R').hom.app T x)
        ((Restriction.objectsCompHom E R R').hom.app T y)).trans
      (OpenFiniteSubgroupoid.compIsoArrowEquiv E R R' P T x y)) ?_⟩
  intro x y z gg ff
  refine Eq.trans
    (congrArg (OpenFiniteSubgroupoid.compIsoArrows E R R' P T)
      ((OpenFiniteSubgroupoid.toGroupoidInFunctors P).evaluationArrowEquiv_comp T gg ff)) ?_
  exact (OpenFiniteSubgroupoid.compIsoComp_app E R R' P T _ _ _ _).symm

/-! ### The transported open finite subgroupoid -/

/-- **The open subspace of arrows, pulled back along the comparison.**  The preimage, under the
comparison of the two arrow spaces, of an open finite subgroupoid of a realization of the
restriction along `g` is an open finite subgroupoid of a realization of the restriction along
`E.hom ≫ g`. -/
def OpenFiniteSubgroupoid.compIso (P : OpenFiniteSubgroupoid R.groupoid) :
    OpenFiniteSubgroupoid R'.groupoid where
  arrows := P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom
  arrows_open := Space.isOpenSubspace_preimage C S hS _ _ R.groupoid.arrows.2
    R'.groupoid.arrows.2 P.arrows_open
  source_finite := OpenFiniteSubgroupoid.isFinite_compIso_source E R R' P
  target_finite := OpenFiniteSubgroupoid.isFinite_compIso_target E R R' P
  comp := OpenFiniteSubgroupoid.compIsoComp E R R' P
  comp_restricts _ _ := rfl
  pointwiseGroupoid T :=
    OpenFiniteSubgroupoid.nonempty_pointwiseGroupoid_compIso E R R' P T

/-- The arrows of the transported open finite subgroupoid are the preimage of its arrows under
the comparison of the two arrow spaces. -/
theorem OpenFiniteSubgroupoid.compIso_arrows (P : OpenFiniteSubgroupoid R.groupoid) :
    (OpenFiniteSubgroupoid.compIso E R R' P).arrows =
      P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom := rfl

/-- Every point of the arrows of an open finite subgroupoid comes from a point of the preimage of
those arrows, the comparison of the arrow spaces being an isomorphism. -/
theorem OpenFiniteSubgroupoid.exists_pointsMap_compIso (P : OpenFiniteSubgroupoid R.groupoid)
    (q : Space.points C S hS P.arrows.toFunctor) :
    ∃ q' : Space.points C S hS
        (P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).toFunctor,
      Space.pointsMap C S hS
          (P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).toFunctor
          ((P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).ι ≫
            (Restriction.arrowsCompIso E R R').hom.hom) q' =
        Space.pointsMap C S hS P.arrows.toFunctor P.arrows.ι q := by
  have := OpenFiniteSubgroupoid.isIso_fromPreimage E R R' P
  refine ⟨Space.pointsMap C S hS P.arrows.toFunctor
    (inv (P.arrows.fromPreimage (Restriction.arrowsCompIso E R R').hom.hom)) q, ?_⟩
  refine (congrArg (fun m => Space.pointsMap C S hS
    (P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).toFunctor m
    (Space.pointsMap C S hS P.arrows.toFunctor
      (inv (P.arrows.fromPreimage (Restriction.arrowsCompIso E R R').hom.hom)) q))
    (Subfunctor.fromPreimage_ι P.arrows
      (Restriction.arrowsCompIso E R R').hom.hom).symm).trans ?_
  refine (congrFun (Space.pointsMap_comp C S hS
    (P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).toFunctor
    (P.arrows.fromPreimage (Restriction.arrowsCompIso E R R').hom.hom) P.arrows.ι) _).trans ?_
  refine congrArg (Space.pointsMap C S hS P.arrows.toFunctor P.arrows.ι) ?_
  exact pointsMap_pointsMap_of_comp_eq_id _ _ (IsIso.inv_hom_id _) q

/-! ### The transported strong splitting -/

/-- **A strong splitting, pulled back along the comparison.**  The preimage of a strong splitting
at a point of the object space of a realization of the restriction along `g` is a strong splitting
at any point of the object space of a realization of the restriction along `E.hom ≫ g` which the
comparison of the object spaces carries to it. -/
def StrongSplitting.compIso {u : Space.points C S hS R.groupoid.objects.obj}
    (P : StrongSplitting R.groupoid u)
    (u' : Space.points C S hS R'.groupoid.objects.obj)
    (hu : Space.pointsMap C S hS R'.groupoid.objects.obj
      (Restriction.objectsCompHom E R R').hom u' = u) :
    StrongSplitting R'.groupoid u' :=
  { OpenFiniteSubgroupoid.compIso E R R' P.toOpenFiniteSubgroupoid with
    contains_arrows := by
      intro r hr
      have hs : Space.pointsMap C S hS R.groupoid.arrows.obj R.groupoid.source.hom
          (Space.pointsMap C S hS R'.groupoid.arrows.obj
            (Restriction.arrowsCompIso E R R').hom.hom r) = u := by
        refine (congrFun (Space.pointsMap_comp C S hS R'.groupoid.arrows.obj
          (Restriction.arrowsCompIso E R R').hom.hom R.groupoid.source.hom) r).symm.trans ?_
        refine (congrArg (fun m => Space.pointsMap C S hS R'.groupoid.arrows.obj m r)
          (Restriction.arrowsCompIso_hom_hom_comp_source E R R')).trans ?_
        refine (congrFun (Space.pointsMap_comp C S hS R'.groupoid.arrows.obj
          R'.groupoid.source.hom (Restriction.objectsCompHom E R R').hom) r).trans ?_
        exact (congrArg (Space.pointsMap C S hS R'.groupoid.objects.obj
          (Restriction.objectsCompHom E R R').hom) hr.1).trans hu
      have ht : Space.pointsMap C S hS R.groupoid.arrows.obj R.groupoid.target.hom
          (Space.pointsMap C S hS R'.groupoid.arrows.obj
            (Restriction.arrowsCompIso E R R').hom.hom r) = u := by
        refine (congrFun (Space.pointsMap_comp C S hS R'.groupoid.arrows.obj
          (Restriction.arrowsCompIso E R R').hom.hom R.groupoid.target.hom) r).symm.trans ?_
        refine (congrArg (fun m => Space.pointsMap C S hS R'.groupoid.arrows.obj m r)
          (Restriction.arrowsCompIso_hom_hom_comp_target E R R')).trans ?_
        refine (congrFun (Space.pointsMap_comp C S hS R'.groupoid.arrows.obj
          R'.groupoid.target.hom (Restriction.objectsCompHom E R R').hom) r).trans ?_
        exact (congrArg (Space.pointsMap C S hS R'.groupoid.objects.obj
          (Restriction.objectsCompHom E R R').hom) hr.2).trans hu
      obtain ⟨p, hp⟩ := P.contains_arrows (Space.pointsMap C S hS R'.groupoid.arrows.obj
        (Restriction.arrowsCompIso E R R').hom.hom r) ⟨hs, ht⟩
      obtain ⟨q', hq'⟩ := OpenFiniteSubgroupoid.exists_pointsMap_compIso E R R'
        P.toOpenFiniteSubgroupoid p
      refine ⟨q', ?_⟩
      refine pointsMap_injective_of_isIso (Restriction.arrowsCompIso E R R').hom.hom ?_
      refine Eq.trans ?_ (hq'.trans hp)
      exact (congrFun (Space.pointsMap_comp C S hS
        (P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).toFunctor
        (P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).ι
        (Restriction.arrowsCompIso E R R').hom.hom) q').symm }

/-- The transported strong splitting has the transported open finite subgroupoid underlying
it. -/
theorem StrongSplitting.compIso_toOpenFiniteSubgroupoid
    {u : Space.points C S hS R.groupoid.objects.obj} (P : StrongSplitting R.groupoid u)
    (u' : Space.points C S hS R'.groupoid.objects.obj)
    (hu : Space.pointsMap C S hS R'.groupoid.objects.obj
      (Restriction.objectsCompHom E R R').hom u' = u) :
    (StrongSplitting.compIso E R R' P u' hu).toOpenFiniteSubgroupoid =
      OpenFiniteSubgroupoid.compIso E R R' P.toOpenFiniteSubgroupoid := rfl

/-- **A strong splitting across an equality of restricting morphisms.**  A strong splitting of a
realization of the restriction along `g` gives one of a realization of the restriction along any
morphism equal to `g` precomposed with an isomorphism. -/
theorem nonempty_strongSplitting_of_eq {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂)
    {g : U₂ ⟶ G.objects} (R : Restriction G g)
    {u : Space.points C S hS R.groupoid.objects.obj} (Q : StrongSplitting R.groupoid u)
    (m : U₁ ⟶ G.objects) (hm : E.hom ≫ g = m) (Rm : Restriction G m)
    (u' : Space.points C S hS Rm.groupoid.objects.obj)
    (hu' : Space.pointsMap C S hS Rm.groupoid.objects.obj
      (eqToHom Rm.objects_eq ≫ E.hom ≫ eqToHom R.objects_eq.symm).hom u' = u) :
    Nonempty (StrongSplitting Rm.groupoid u') := by
  subst hm
  exact ⟨StrongSplitting.compIso E R Rm Q u' hu'⟩

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end

end
