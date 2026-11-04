module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPointMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericStalkCriterion

/-!
# Birational schemes over a base and their generic residue fields

Let `X` and `Y` be integral schemes over a base `S`. If `X` and `Y` are birational over `S`,
then their generic points have the same image in `S` and their residue fields at the generic
points are isomorphic over the residue field of that common image. This is the implication
(1) ⇒ (3) of Stacks Tag 0552.

## Main results

* `AlgebraicGeometry.residueFieldIso_of_birationalOver`: a birational pair over `S` has
  isomorphic generic residue fields over `S`.
* `AlgebraicGeometry.exists_genericStalkIso_of_residueFieldIso`: such an isomorphism of generic
  residue fields comes from an isomorphism of the local rings at the generic points over `S`.

## References

* [Stacks Project, Tag 0552](https://stacks.math.columbia.edu/tag/0552)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The residue map of an integral scheme at its generic point, as an isomorphism from the local
ring there to the residue field. -/
public noncomputable def genericStalkResidueFieldIso (Z : Scheme.{u}) [IsIntegral Z] :
    Z.presheaf.stalk (genericPoint Z) ≅ Z.residueField (genericPoint Z) := by
  refine (RingEquiv.ofBijective (Z.residue (genericPoint Z)).hom ?_).toCommRingCatIso
  constructor
  · change Function.Injective (IsLocalRing.residue (Z.presheaf.stalk _))
    rw [RingHom.injective_iff_ker_eq_bot, IsLocalRing.ker_residue,
      IsLocalRing.maximalIdeal_eq_bot]
  · exact Z.residue_surjective _

/-- The isomorphism `genericStalkResidueFieldIso Z` is the residue map at the generic point. -/
public theorem genericStalkResidueFieldIso_hom (Z : Scheme.{u}) [IsIntegral Z] :
    (genericStalkResidueFieldIso Z).hom = Z.residue (genericPoint Z) := rfl

/-- Transporting a morphism out of the residue field at `a` along `h : a = b` is precomposition
with the identification of the residue fields at `b` and at `a` induced by `h`. -/
public theorem cast_residueField_hom {S : Scheme.{u}} {a b : S} (h : a = b)
    {T : CommRingCat} (f : S.residueField a ⟶ T) :
    h ▸ f = eqToHom (congrArg (fun z => S.residueField z) h.symm) ≫ f := by
  cases h
  simp

/-- The specialization map between the stalks at equal points is the identification of the
stalks induced by the equality. -/
public theorem stalkSpecializes_of_eq {S : Scheme.{u}} {a b : S} (h : a = b) :
    S.presheaf.stalkSpecializes (Inseparable.of_eq h).ge =
      eqToHom (congrArg (fun z => S.presheaf.stalk z) h) := by
  cases h
  simp

/-- Heterogeneously equal morphisms out of the stalks of `Y` at points `x = y` differ by the
identification of the stalks induced by `x = y`. -/
public theorem stalkMap_eq_of_heq {Y : Scheme.{u}} {x y : Y} {R : CommRingCat}
    {f : Y.presheaf.stalk x ⟶ R} {g : Y.presheaf.stalk y ⟶ R} (h : x = y)
    (H : HEq f g) : f = eqToHom (congrArg Y.presheaf.stalk h) ≫ g := by
  cases h
  exact eq_of_heq H

/-- Along `h : b = a`, the residue map at `b` followed by the identification of residue fields
is the identification of stalks followed by the residue map at `a`. -/
private theorem residue_comp_eqToHom {S : Scheme.{u}} {a b : S} (h : b = a) {T : CommRingCat}
    (f : S.residueField a ⟶ T) :
    S.residue b ≫ eqToHom (congrArg (fun z => S.residueField z) h) ≫ f =
      eqToHom (congrArg (fun z => S.presheaf.stalk z) h) ≫ S.residue a ≫ f := by
  cases h
  simp

/-- Let `e` be an isomorphism of the residue fields at the generic points of integral schemes over
`S`, compatible with the maps from the residue field of `S` at the common image. Then the inverse
of the induced isomorphism of the local rings at the generic points is compatible with the stalk
maps from `S`. -/
public theorem genericStalkMap_commutes_of_residueFieldIso
    {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsIntegral X] [IsIntegral Y]
    (h : sX (genericPoint X) = sY (genericPoint Y))
    (e : X.residueField (genericPoint X) ≅ Y.residueField (genericPoint Y))
    (he : h ▸ (sX.residueFieldMap (genericPoint X) ≫ e.hom) =
      sY.residueFieldMap (genericPoint Y)) :
    sY.stalkMap (genericPoint Y) ≫
        (genericStalkResidueFieldIso X ≪≫ e ≪≫ (genericStalkResidueFieldIso Y).symm).inv =
      eqToHom (congrArg (fun z => S.presheaf.stalk z) h.symm) ≫
        sX.stalkMap (genericPoint X) := by
  apply (cancel_mono (genericStalkResidueFieldIso X).hom).1
  simp only [Iso.trans_inv, Category.assoc]
  simp only [Iso.symm_inv, Iso.inv_hom_id]
  simp only [Category.comp_id, genericStalkResidueFieldIso_hom]
  rw [← Scheme.residue_residueFieldMap_assoc sY (genericPoint Y) e.inv,
    ← Scheme.residue_residueFieldMap sX (genericPoint X)]
  have he' : eqToHom (congrArg (fun z => S.residueField z) h.symm) ≫
      (sX.residueFieldMap (genericPoint X) ≫ e.hom) =
      sY.residueFieldMap (genericPoint Y) := by
    simpa [cast_residueField_hom] using he
  calc
    _ = S.residue (sY (genericPoint Y)) ≫
          (eqToHom (congrArg (fun z => S.residueField z) h.symm) ≫
            (sX.residueFieldMap (genericPoint X) ≫ e.hom)) ≫ e.inv := by rw [← he']
    _ = eqToHom (congrArg (fun z => S.presheaf.stalk z) h.symm) ≫
          S.residue (sX (genericPoint X)) ≫ sX.residueFieldMap (genericPoint X) := by
      simp only [Category.assoc]
      rw [residue_comp_eqToHom h.symm]
      simp

private theorem residueFieldIso_of_genericStalkMap
    {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsIntegral X] [IsIntegral Y]
    (h : sX (genericPoint X) = sY (genericPoint Y))
    (m : Y.presheaf.stalk (genericPoint Y) ⟶ X.presheaf.stalk (genericPoint X))
    (hm : IsIso m)
    (hm_comm : sY.stalkMap (genericPoint Y) ≫ m =
      eqToHom (congrArg (fun z => S.presheaf.stalk z) h.symm) ≫
        sX.stalkMap (genericPoint X)) :
    ∃ (e : X.residueField (genericPoint X) ≅ Y.residueField (genericPoint Y)),
      h ▸ (sX.residueFieldMap (genericPoint X) ≫ e.hom) =
        sY.residueFieldMap (genericPoint Y) := by
  let mIso : Y.presheaf.stalk (genericPoint Y) ≅ X.presheaf.stalk (genericPoint X) :=
    asIso m
  let e := (genericStalkResidueFieldIso X).symm ≪≫ mIso.symm ≪≫
    genericStalkResidueFieldIso Y
  refine ⟨e, ?_⟩
  rw [cast_residueField_hom]
  apply (cancel_epi (S.residue (sY (genericPoint Y)))).1
  rw [residue_comp_eqToHom h.symm, Scheme.residue_residueFieldMap_assoc sX (genericPoint X),
    Scheme.residue_residueFieldMap sY (genericPoint Y)]
  dsimp [e]
  rw [← genericStalkResidueFieldIso_hom X, ← genericStalkResidueFieldIso_hom Y]
  simp only [Iso.hom_inv_id_assoc]
  show ((eqToHom (congrArg (fun z => S.presheaf.stalk z) h.symm) ≫
    sX.stalkMap (genericPoint X)) ≫ mIso.inv) ≫
      (genericStalkResidueFieldIso Y).hom =
    sY.stalkMap (genericPoint Y) ≫ (genericStalkResidueFieldIso Y).hom
  rw [← hm_comm]
  simp [Category.assoc, mIso]

/-- The generic point of an irreducible scheme lies in every dense open. -/
public lemma genericPoint_mem_dense_open {Z : Scheme.{u}} [IrreducibleSpace Z]
    (U : Z.Opens) (hU : Dense (U : Set Z)) : genericPoint Z ∈ U := by
  apply (genericPoint_spec Z).mem_open_set_iff U.2 |>.2
  simpa using hU.nonempty

/-- The local map at the generic point for `genericPointContext sX sY` which sends the generic
point of `X` to that of `Y`, with the stalk map induced by an isomorphism `e` of the residue fields
at the generic points compatible with the maps from the residue field of `S`. -/
public noncomputable def genericPointLocalMapOfResidueFieldIso
    {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsIntegral X] [IsIntegral Y]
    (h : sX (genericPoint X) = sY (genericPoint Y))
    (e : X.residueField (genericPoint X) ≅ Y.residueField (genericPoint Y))
    (he : h ▸ (sX.residueFieldMap (genericPoint X) ≫ e.hom) =
      sY.residueFieldMap (genericPoint Y)) :
    (genericPointContext sX sY).GenericPointLocalMap
      ⟨0, by simp⟩ := by
  let c := genericPointContext sX sY
  let eStalk := genericStalkResidueFieldIso X ≪≫ e ≪≫
    (genericStalkResidueFieldIso Y).symm
  refine ⟨genericPoint Y, h.symm, eStalk.inv, ?_, ?_⟩
  · change IsLocalHom eStalk.inv.hom
    exact isLocalHom_of_leftInverse eStalk.hom.hom (by intro a; simp)
  · change sY.stalkMap (genericPoint Y) ≫ eStalk.inv =
        eqToHom (congrArg (fun z => S.presheaf.stalk z) h.symm) ≫
          sX.stalkMap (genericPoint X)
    simpa [c, genericPointContext, eStalk] using
      genericStalkMap_commutes_of_residueFieldIso sX sY h e he

/-- If integral schemes `X` and `Y` are birational over `S`, then their generic points have the
same image in `S`, and their residue fields at the generic points are isomorphic compatibly with
the maps from the residue field of `S` at that image. -/
public theorem residueFieldIso_of_birationalOver
    {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsIntegral X] [IsIntegral Y]
    (hXY : Scheme.BirationalOver sX sY) :
    ∃ (h : sX (genericPoint X) = sY (genericPoint Y))
      (e : X.residueField (genericPoint X) ≅ Y.residueField (genericPoint Y)),
      h ▸ (sX.residueFieldMap (genericPoint X) ≫ e.hom) =
        sY.residueFieldMap (genericPoint Y) := by
  classical
  let p := hXY.partialIso sX sY
  let C := genericPointContext sX sY
  let i : Fin C.numberOfComponents := ⟨0, by simp [C]⟩
  let g : X.PartialMap Y := p.toPartialMap
  let : X.Over S := ⟨sX⟩
  let : Y.Over S := ⟨sY⟩
  have hOver : g.hom ≫ sY = g.domain.ι ≫ sX := by
    show p.iso.hom ≫ p.target.ι ≫ sY = p.source.ι ≫ sX
    exact hXY.partialIso_isOver sX sY
  let : g.IsOver S := ⟨hOver⟩
  let : g.toRationalMap.IsOver S := inferInstance
  have hRatOver : g.toRationalMap.compHom sY = sX.toRationalMap :=
    (Scheme.RationalMap.isOver_iff).mp ‹g.toRationalMap.IsOver S›
  let f : C.RationalMapsOver := ⟨g.toRationalMap, hRatOver⟩
  let G := C.genericPointMapForRationalMaps f i
  let z : g.domain := ⟨genericPoint X, genericPoint_mem_dense_open g.domain g.dense_domain⟩
  let : Nonempty p.source := ⟨⟨genericPoint X,
    genericPoint_mem_dense_open p.source p.dense_source⟩⟩
  let : Nonempty p.target := ⟨⟨genericPoint Y,
    genericPoint_mem_dense_open p.target p.dense_target⟩⟩
  have hz : g.hom z = genericPoint Y := by
    show p.target.ι (p.iso.hom z) = genericPoint Y
    have hz' : z = genericPoint p.source.toScheme :=
      Subtype.ext (genericPoint_eq_of_isOpenImmersion p.source.ι).symm
    rw [hz', genericPoint_eq_of_isOpenImmersion p.iso.hom,
      genericPoint_eq_of_isOpenImmersion p.target.ι]
  have hpoint := C.genericPointMapForRationalMaps.map_point f g rfl hOver
    (fun _ => genericPoint_mem_dense_open g.domain g.dense_domain) i
  have hstalk := C.genericPointMapForRationalMaps.map_stalk f g rfl hOver
    (fun _ => genericPoint_mem_dense_open g.domain g.dense_domain) i
  change G.point = g.hom z at hpoint
  change HEq G.stalkMap (g.hom.stalkMap z ≫ (g.domain.stalkIso z).hom) at hstalk
  have : IsOpenImmersion g.hom := by
    show IsOpenImmersion (p.iso.hom ≫ p.target.ι)
    infer_instance
  cases hG : G with
  | mk dpoint dmapsTo dm dlocal dcomm =>
    rw [hG] at hpoint hstalk
    dsimp only at hstalk
    have hDpoint : dpoint = genericPoint Y := hpoint.trans hz
    cases hDpoint
    dsimp only at hpoint
    have hstalkEq := stalkMap_eq_of_heq hpoint hstalk
    have hcompIso : IsIso (g.hom.stalkMap z ≫ (g.domain.stalkIso z).hom) := by
      have : IsIso (g.hom.stalkMap z) :=
        (IsOpenImmersion.iff_isIso_stalkMap.mp ‹IsOpenImmersion g.hom›).2 z
      have : IsIso ((g.domain.stalkIso z).hom) := inferInstance
      infer_instance
    have : IsIso (eqToHom (congrArg Y.presheaf.stalk hpoint)) := inferInstance
    have : IsIso (g.hom.stalkMap z ≫ (g.domain.stalkIso z).hom) := hcompIso
    have hm : IsIso dm := hstalkEq ▸ (inferInstance : IsIso
      (eqToHom (congrArg Y.presheaf.stalk hpoint) ≫
        (g.hom.stalkMap z ≫ (g.domain.stalkIso z).hom)))
    have hmapsTo : sY (genericPoint Y) = sX (genericPoint X) := dmapsTo
    have hcomm : sY.stalkMap (genericPoint Y) ≫ dm =
        eqToHom (congrArg (fun z => S.presheaf.stalk z) hmapsTo) ≫
          sX.stalkMap (genericPoint X) := by
      simpa [C, genericPointContext, hmapsTo] using dcomm
    exact ⟨hmapsTo.symm, (residueFieldIso_of_genericStalkMap sX sY hmapsTo.symm
      dm hm hcomm)⟩

private alias transport_comp_hom_of_comp_inv := transport_comp_of_inv

/-- For integral schemes over a base, an isomorphism of the residue fields at the generic points
over the base is induced by an isomorphism of the local rings there over the base. -/
public theorem exists_genericStalkIso_of_residueFieldIso
    {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsIntegral X] [IsIntegral Y]
    (h : sX (genericPoint X) = sY (genericPoint Y))
    (e : X.residueField (genericPoint X) ≅ Y.residueField (genericPoint Y))
    (he : h ▸ (sX.residueFieldMap (genericPoint X) ≫ e.hom) =
      sY.residueFieldMap (genericPoint Y)) :
    ∃ e' : X.presheaf.stalk (genericPoint X) ≅ Y.presheaf.stalk (genericPoint Y),
      h ▸ (sX.stalkMap (genericPoint X) ≫ e'.hom) = sY.stalkMap (genericPoint Y) :=
  ⟨genericStalkResidueFieldIso X ≪≫ e ≪≫ (genericStalkResidueFieldIso Y).symm,
    transport_comp_hom_of_comp_inv (fun z ↦ S.presheaf.stalk z) h
      (sX.stalkMap (genericPoint X)) _ (sY.stalkMap (genericPoint Y))
      (genericStalkMap_commutes_of_residueFieldIso sX sY h e he)⟩

end AlgebraicGeometry

end
