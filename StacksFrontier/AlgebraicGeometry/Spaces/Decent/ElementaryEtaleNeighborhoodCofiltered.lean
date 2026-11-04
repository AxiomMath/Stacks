module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.FieldValued
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhoodFieldPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.MonomorphismPoints
public import StacksCore.Tactic.StacksAttribute

/-!
# Cofilteredness of the elementary étale neighborhoods of a point

Let `x` be a point of an algebraic space `X` over `S`. Any two elementary étale neighborhoods of
`x` are refined by a third, and any two parallel morphisms of such neighborhoods are equalized by
a refinement of their source: the category of elementary étale neighborhoods of `x` is cofiltered
as soon as it is nonempty.

Both constructions rest on the same refinement principle. An object `P` of the chosen big site
which is étale over the scheme of a neighborhood `V`, and through which the residue-field point of
`V` factors, is again an elementary étale neighborhood of `x`. Indeed the factorization produces a
point of `P` above the distinguished point of `V` at which the residue field is *unchanged*: the
factorization splits the homomorphism `κ(v) ⟶ κ(p)` which `P ⟶ V` induces there, and a
homomorphism of fields is injective, so a split homomorphism of residue fields is bijective. The
canonical morphism from the residue-field point of `P` into the space therefore agrees, up to that
isomorphism, with the one of `V`, and so is again a monomorphism.

A common refinement of two neighborhoods `V` and `W` is the fibre product of their schemes over
the space, which the representable diagonal of an algebraic space provides as an object of the
site. Its residue-field point comes from the comparison of the residue-field points of `V` and of
`W`, which are monic field-valued representatives of the same point `x` and hence canonically
isomorphic over the space. A refinement equalizing two morphisms `f, g : V ⟶ W` is the fibre
product of `(f, g) : V ⟶ W ×_X W` with the diagonal of `W` over the space; its residue-field
point comes from the rigidity of the residue-field point of `V`, namely that `f` and `g` agree
after composition with it.

## Main definitions

* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.ofResidueFieldLift` is the elementary étale
  neighborhood described above, and
  `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.ofResidueFieldLiftHom` its morphism to the
  neighborhood it refines.

## Main results

* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.isIso_liftedResidueFieldHom`: the residue
  field at the lifted point is the residue field of `V` at its distinguished point.
* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.exists_cone_objs` and
  `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.exists_cone_maps`: the two clauses of
  **Stacks 0BGV**, common refinements and equalizing refinements, assembled in
  `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.isCofilteredOrEmpty`.
* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.isCofiltered_of_nonempty`: **Stacks 0BGV**
  for a nonempty category of neighborhoods.
* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.residueFieldMap_comp_eq`: two morphisms of
  elementary étale neighborhoods agree after composition with the residue-field point of their
  source.

## Implementation notes

Neither clause of Stacks 0BGV uses decency of `X`, or indeed any hypothesis beyond `x` being a
point of an algebraic space: the monomorphism condition carried by an elementary étale
neighborhood is what makes the two residue-field points comparable, and that condition is part of
the data of Tag 0BGU. Decency is used by the source only for *nonemptiness* of the category, which
is Stacks 0BBP; nonemptiness is therefore carried here as the hypothesis of
`isCofiltered_of_nonempty` rather than derived from decency. Tag 0BBP is not available in this
library: its proof needs clause (1) of Tag 0BBN, which
`StacksFrontier/AlgebraicGeometry/Spaces/OpenFiltrationSeparatedNeighbourhoods.lean` records as
missing.

Representability of the fibre products is taken from étaleness rather than from the diagonal of
`X`: `AlgebraicGeometry.Space.IsEtale` of a chart is the relative morphism property of Tag 03FR,
whose first half is relative representability — by an object of the *chosen site*, so no size
estimate is needed — and whose second half gives étaleness of the projection. The diagonal of a
neighborhood over the space is recognized as étale through Tag 03FV, a morphism over the space
between algebraic spaces étale over it.

The data of each fibre product is packaged in an existential statement
(`exists_cone_data`, `exists_selfProduct_data`, `exists_equalizer_data`) before the neighborhood
is assembled from it. This is not cosmetic: the projections of a relatively representable morphism
are choice terms built from a proof of étaleness, and the elaborator unfolds them when it has to
check a definitional equality against one, so passing them as opaque local constants is what keeps
the assembly cheap.

## References

* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
* [Stacks Project, Tag 0BGV](https://stacks.math.columbia.edu/tag/0BGV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (x : points B S hS X)

namespace ElementaryEtaleNeighborhood

section ResidueFieldLift

/-- The point of `P` determined by a lift to `P` of the residue-field point of `V`. -/
def liftedPoint (V : ElementaryEtaleNeighborhood B S hS X hX x) (P : BigFppfOver B S hS)
    (m : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶ P) :
    P.left.1 :=
  m.left.1 (IsLocalRing.closedPoint (V.scheme.left.1.residueField V.point))

/-- The lifted point lies above the distinguished point of `V`. -/
theorem map_liftedPoint (V : ElementaryEtaleNeighborhood B S hS X hX x)
    (P : BigFppfOver B S hS) (q : P ⟶ V.scheme)
    (m : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶ P)
    (hm : m ≫ q = residueFieldMap B S hS V.scheme V.point V.residueField_contained) :
    q.left.1 (liftedPoint B S hS X hX x V P m) = V.point := by
  have h := congrArg
    (fun k : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶ V.scheme ↦
      k.left.1 (IsLocalRing.closedPoint (V.scheme.left.1.residueField V.point))) hm
  exact h.trans (Scheme.fromSpecResidueField_apply _ _)

/-- The homomorphism of residue fields which the étale morphism induces at the lifted point. -/
def liftedResidueFieldHom (V : ElementaryEtaleNeighborhood B S hS X hX x)
    (P : BigFppfOver B S hS) (q : P ⟶ V.scheme)
    (m : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶ P)
    (hm : m ≫ q = residueFieldMap B S hS V.scheme V.point V.residueField_contained) :
    CommRingCat.of (V.scheme.left.1.residueField V.point) ⟶
      CommRingCat.of (P.left.1.residueField (liftedPoint B S hS X hX x V P m)) :=
  (V.scheme.left.1.residueFieldCongr
      (map_liftedPoint B S hS X hX x V P q m hm)).inv ≫
    q.left.1.residueFieldMap (liftedPoint B S hS X hX x V P m)

/-- The residue-field homomorphism at the lifted point fits in the square of field spectra over
the scheme of `V`. -/
theorem specMap_liftedResidueFieldHom (V : ElementaryEtaleNeighborhood B S hS X hX x)
    (P : BigFppfOver B S hS) (q : P ⟶ V.scheme)
    (m : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶ P)
    (hm : m ≫ q = residueFieldMap B S hS V.scheme V.point V.residueField_contained) :
    Spec.map (liftedResidueFieldHom B S hS X hX x V P q m hm) ≫
        V.scheme.left.1.fromSpecResidueField V.point =
      P.left.1.fromSpecResidueField (liftedPoint B S hS X hX x V P m) ≫ q.left.1 := by
  have hqu := map_liftedPoint B S hS X hX x V P q m hm
  have hCongr : Spec.map (V.scheme.left.1.residueFieldCongr hqu).inv ≫
      V.scheme.left.1.fromSpecResidueField V.point =
      V.scheme.left.1.fromSpecResidueField (q.left.1 (liftedPoint B S hS X hX x V P m)) := by
    have h := Scheme.residueFieldCongr_fromSpecResidueField hqu
    calc
      Spec.map (V.scheme.left.1.residueFieldCongr hqu).inv ≫
          V.scheme.left.1.fromSpecResidueField V.point =
          Spec.map (V.scheme.left.1.residueFieldCongr hqu).inv ≫
            (Spec.map (V.scheme.left.1.residueFieldCongr hqu).hom ≫
              V.scheme.left.1.fromSpecResidueField
                (q.left.1 (liftedPoint B S hS X hX x V P m))) := by rw [← h]
      _ = (Spec.map (V.scheme.left.1.residueFieldCongr hqu).inv ≫
            Spec.map (V.scheme.left.1.residueFieldCongr hqu).hom) ≫
            V.scheme.left.1.fromSpecResidueField
              (q.left.1 (liftedPoint B S hS X hX x V P m)) := by rw [Category.assoc]
      _ = V.scheme.left.1.fromSpecResidueField
            (q.left.1 (liftedPoint B S hS X hX x V P m)) := by simp
  have hmap : Spec.map (liftedResidueFieldHom B S hS X hX x V P q m hm) =
      Spec.map (q.left.1.residueFieldMap (liftedPoint B S hS X hX x V P m)) ≫
        Spec.map (V.scheme.left.1.residueFieldCongr hqu).inv := by
    rw [liftedResidueFieldHom, ← Spec.map_comp]
  rw [hmap, Category.assoc, hCongr]
  exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (f := q.left.1)
    (liftedPoint B S hS X hX x V P m)

/-- The morphism of schemes underlying a lift of the residue-field point factors the canonical
morphism from the residue field of `V` at its distinguished point. -/
theorem left_comp_liftedPoint (V : ElementaryEtaleNeighborhood B S hS X hX x)
    (P : BigFppfOver B S hS) (q : P ⟶ V.scheme)
    (m : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶ P)
    (hm : m ≫ q = residueFieldMap B S hS V.scheme V.point V.residueField_contained) :
    m.left.1 ≫ q.left.1 = V.scheme.left.1.fromSpecResidueField V.point :=
  congrArg
    (fun k : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶ V.scheme ↦
      k.left.1) hm

/-- **The residue field is unchanged.** The homomorphism of residue fields at the lifted point is
an isomorphism: the lift splits it, and a homomorphism of fields is injective. -/
theorem isIso_liftedResidueFieldHom (V : ElementaryEtaleNeighborhood B S hS X hX x)
    (P : BigFppfOver B S hS) (q : P ⟶ V.scheme)
    (m : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶ P)
    (hm : m ≫ q = residueFieldMap B S hS V.scheme V.point V.residueField_contained) :
    IsIso (liftedResidueFieldHom B S hS X hX x V P q m hm) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Spec (.of (V.scheme.left.1.residueField V.point)) ⟶
      Spec (.of (P.left.1.residueField (liftedPoint B S hS X hX x V P m))),
      φ ≫ P.left.1.fromSpecResidueField (liftedPoint B S hS X hX x V P m) = m.left.1 := by
    obtain ⟨φ, hφ, -⟩ := _root_.AlgebraicGeometry.FieldValuedPoint.canonical_isSmallest
      (X := P.left.1) (liftedPoint B S hS X hX x V P m)
      ⟨V.scheme.left.1.residueField V.point, m.left.1⟩
      (Scheme.fromSpecResidueField_apply _ _).symm
    exact ⟨φ, hφ⟩
  have hsmall := _root_.AlgebraicGeometry.FieldValuedPoint.canonical_isSmallest
    (X := V.scheme.left.1) V.point
    (_root_.AlgebraicGeometry.FieldValuedPoint.canonical V.scheme.left.1 V.point) rfl
  have hone : φ ≫ Spec.map (liftedResidueFieldHom B S hS X hX x V P q m hm) = 𝟙 _ := by
    refine hsmall.unique ?_ (Category.id_comp _)
    show (φ ≫ Spec.map (liftedResidueFieldHom B S hS X hX x V P q m hm)) ≫
      V.scheme.left.1.fromSpecResidueField V.point =
      V.scheme.left.1.fromSpecResidueField V.point
    rw [Category.assoc, specMap_liftedResidueFieldHom B S hS X hX x V P q m hm,
      ← Category.assoc, hφ]
    exact left_comp_liftedPoint B S hS X hX x V P q m hm
  have hψα : liftedResidueFieldHom B S hS X hX x V P q m hm ≫ Spec.preimage φ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, Spec.map_preimage]
    exact hone
  have hinj : Function.Injective (Spec.preimage φ).hom := (Spec.preimage φ).hom.injective
  have hαψ : Spec.preimage φ ≫ liftedResidueFieldHom B S hS X hX x V P q m hm = 𝟙 _ := by
    ext z
    apply hinj
    exact congrArg (fun k : CommRingCat.of (V.scheme.left.1.residueField V.point) ⟶
      CommRingCat.of (V.scheme.left.1.residueField V.point) ↦
        k.hom ((Spec.preimage φ).hom z)) hψα
  exact ⟨Spec.preimage φ, hψα, hαψ⟩

/-- The residue-field spectrum at the lifted point belongs to the chosen big site. -/
theorem contains_liftedResidueField (V : ElementaryEtaleNeighborhood B S hS X hX x)
    (P : BigFppfOver B S hS) (q : P ⟶ V.scheme)
    (m : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶ P)
    (hm : m ≫ q = residueFieldMap B S hS V.scheme V.point V.residueField_contained) :
    B.Contains (Spec (.of (P.left.1.residueField (liftedPoint B S hS X hX x V P m)))) := by
  have := isIso_liftedResidueFieldHom B S hS X hX x V P q m hm
  have : IsIso (Spec.map (liftedResidueFieldHom B S hS X hX x V P q m hm)) := inferInstance
  show (Spec (.of (P.left.1.residueField (liftedPoint B S hS X hX x V P m)))).size < B.cutoff
  rw [Scheme.size_congr (asIso (Spec.map (liftedResidueFieldHom B S hS X hX x V P q m hm)))]
  exact V.residueField_contained

/-- The morphism of residue-field points of the site which the étale morphism induces at the
lifted point. -/
def liftedResidueFieldObjectMap (V : ElementaryEtaleNeighborhood B S hS X hX x)
    (P : BigFppfOver B S hS) (q : P ⟶ V.scheme)
    (m : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶ P)
    (hm : m ≫ q = residueFieldMap B S hS V.scheme V.point V.residueField_contained) :
    residueFieldObject B S hS P (liftedPoint B S hS X hX x V P m)
        (contains_liftedResidueField B S hS X hX x V P q m hm) ⟶
      residueFieldObject B S hS V.scheme V.point V.residueField_contained :=
  pointedResidueFieldMap B S hS q (liftedPoint B S hS X hX x V P m) V.point
    (map_liftedPoint B S hS X hX x V P q m hm)
    (contains_liftedResidueField B S hS X hX x V P q m hm) V.residueField_contained

/-- The induced morphism of residue-field points is an isomorphism. -/
theorem isIso_liftedResidueFieldObjectMap (V : ElementaryEtaleNeighborhood B S hS X hX x)
    (P : BigFppfOver B S hS) (q : P ⟶ V.scheme)
    (m : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶ P)
    (hm : m ≫ q = residueFieldMap B S hS V.scheme V.point V.residueField_contained) :
    IsIso (liftedResidueFieldObjectMap B S hS X hX x V P q m hm) := by
  have := isIso_liftedResidueFieldHom B S hS X hX x V P q m hm
  have : IsIso ((BigFppfOver.toScheme B S hS).map
      (liftedResidueFieldObjectMap B S hS X hX x V P q m hm)) := by
    show IsIso (Spec.map (liftedResidueFieldHom B S hS X hX x V P q m hm))
    infer_instance
  exact isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)

/-- The induced morphism of residue-field points lies over the étale morphism. -/
theorem liftedResidueFieldObjectMap_comp (V : ElementaryEtaleNeighborhood B S hS X hX x)
    (P : BigFppfOver B S hS) (q : P ⟶ V.scheme)
    (m : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶ P)
    (hm : m ≫ q = residueFieldMap B S hS V.scheme V.point V.residueField_contained) :
    liftedResidueFieldObjectMap B S hS X hX x V P q m hm ≫
        residueFieldMap B S hS V.scheme V.point V.residueField_contained =
      residueFieldMap B S hS P (liftedPoint B S hS X hX x V P m)
        (contains_liftedResidueField B S hS X hX x V P q m hm) ≫ q :=
  pointedResidueFieldMap_comp B S hS q (liftedPoint B S hS X hX x V P m) V.point
    (map_liftedPoint B S hS X hX x V P q m hm)
    (contains_liftedResidueField B S hS X hX x V P q m hm) V.residueField_contained

/-- **A refinement of an elementary étale neighborhood.** An object of the chosen big site which
is étale over the scheme of an elementary étale neighborhood `V` of `x`, and through which the
residue-field point of `V` factors, is again an elementary étale neighborhood of `x`: the lifted
point lies above `x`, and the residue field there is the residue field of `V` at its
distinguished point, so the canonical morphism into the space is again monic. -/
def ofResidueFieldLift (V : ElementaryEtaleNeighborhood B S hS X hX x)
    (P : BigFppfOver B S hS) (q : P ⟶ V.scheme)
    (hq : Etale ((BigFppfOver.toScheme B S hS).map q))
    (m : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶ P)
    (hm : m ≫ q = residueFieldMap B S hS V.scheme V.point V.residueField_contained) :
    ElementaryEtaleNeighborhood B S hS X hX x where
  scheme := P
  point := liftedPoint B S hS X hX x V P m
  residueField_contained := contains_liftedResidueField B S hS X hX x V P q m hm
  toSpace := yoneda.map q ≫ V.toSpace
  etale_toSpace := isEtale_comp B S hS
    ((isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map q)).mpr
      ((presheaf_yoneda_map_etale_iff B S hS q).mpr hq)) V.etale_toSpace
  map_point := by
    have hclass : pointsMap B S hS (yoneda.obj P) (yoneda.map q)
        (presheafPoint B S hS P (liftedPoint B S hS X hX x V P m)
          (contains_liftedResidueField B S hS X hX x V P q m hm)) =
        presheafPoint B S hS V.scheme V.point V.residueField_contained := by
      refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS (yoneda.obj V.scheme)
        ⟨_, FieldValuedPoint.dominates_refl B S hS (yoneda.obj V.scheme) _,
          liftedResidueFieldObjectMap B S hS X hX x V P q m hm, ?_⟩
      exact liftedResidueFieldObjectMap_comp B S hS X hX x V P q m hm
    change pointsMap B S hS (yoneda.obj P) (yoneda.map q ≫ V.toSpace)
      (presheafPoint B S hS P (liftedPoint B S hS X hX x V P m)
        (contains_liftedResidueField B S hS X hX x V P q m hm)) = x
    rw [pointsMap_comp]
    change pointsMap B S hS (yoneda.obj V.scheme) V.toSpace
      (pointsMap B S hS (yoneda.obj P) (yoneda.map q)
        (presheafPoint B S hS P (liftedPoint B S hS X hX x V P m)
          (contains_liftedResidueField B S hS X hX x V P q m hm))) = x
    rw [hclass]
    exact V.map_point
  mono_residueField := by
    have := isIso_liftedResidueFieldObjectMap B S hS X hX x V P q m hm
    have hmono : Mono (yoneda.map
        (residueFieldMap B S hS V.scheme V.point V.residueField_contained) ≫ V.toSpace) :=
      V.mono_residueField
    have hfactor : yoneda.map (residueFieldMap B S hS P (liftedPoint B S hS X hX x V P m)
            (contains_liftedResidueField B S hS X hX x V P q m hm)) ≫
          (yoneda.map q ≫ V.toSpace) =
        yoneda.map (liftedResidueFieldObjectMap B S hS X hX x V P q m hm) ≫
          (yoneda.map (residueFieldMap B S hS V.scheme V.point V.residueField_contained) ≫
            V.toSpace) := by
      rw [← Category.assoc, ← yoneda.map_comp,
        ← liftedResidueFieldObjectMap_comp B S hS X hX x V P q m hm, yoneda.map_comp,
        Category.assoc]
    change Mono (yoneda.map (residueFieldMap B S hS P (liftedPoint B S hS X hX x V P m)
      (contains_liftedResidueField B S hS X hX x V P q m hm)) ≫ (yoneda.map q ≫ V.toSpace))
    rw [hfactor]
    infer_instance

/-- A refinement maps to the elementary étale neighborhood it refines. -/
def ofResidueFieldLiftHom (V : ElementaryEtaleNeighborhood B S hS X hX x)
    (P : BigFppfOver B S hS) (q : P ⟶ V.scheme)
    (hq : Etale ((BigFppfOver.toScheme B S hS).map q))
    (m : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶ P)
    (hm : m ≫ q = residueFieldMap B S hS V.scheme V.point V.residueField_contained) :
    ofResidueFieldLift B S hS X hX x V P q hq m hm ⟶ V where
  hom := q
  over := rfl
  map_point := map_liftedPoint B S hS X hX x V P q m hm

/-- A lift of the residue-field point of `V` which factors over a second elementary étale
neighborhood `W` through the comparison of residue-field points carries the lifted point to the
distinguished point of `W`. -/
theorem map_liftedPoint_comp (V W : ElementaryEtaleNeighborhood B S hS X hX x)
    (P : BigFppfOver B S hS) (r : P ⟶ W.scheme)
    (m : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶ P)
    (g : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶
      residueFieldObject B S hS W.scheme W.point W.residueField_contained)
    (h : m ≫ r = g ≫ residueFieldMap B S hS W.scheme W.point W.residueField_contained) :
    r.left.1 (liftedPoint B S hS X hX x V P m) = W.point := by
  have h' := congrArg
    (fun k : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶ W.scheme ↦
      k.left.1 (IsLocalRing.closedPoint (V.scheme.left.1.residueField V.point))) h
  refine h'.trans ?_
  exact Scheme.fromSpecResidueField_apply W.point
    (g.left.1 (IsLocalRing.closedPoint (V.scheme.left.1.residueField V.point)))

end ResidueFieldLift

section Cofiltered

/-- The morphism to the space of an elementary étale neighborhood is relatively representable,
with étale represented base changes. -/
theorem presheaf_toSpace (V : ElementaryEtaleNeighborhood B S hS X hX x) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf V.toSpace :=
  (isEtale_iff_presheaf_of_yoneda B S hS V.toSpace).1 V.etale_toSpace

/-- The residue-field point of an elementary étale neighborhood, viewed as a field-valued point
of the space, is monic. -/
theorem mono_neighborhoodFieldPoint (V : ElementaryEtaleNeighborhood B S hS X hX x) :
    Mono (yonedaEquiv.symm (neighborhoodFieldPoint B S hS X hX x V).value) := by
  rw [neighborhoodFieldPoint_morphism]
  exact V.mono_residueField

/-- **The residue-field points of two neighborhoods agree.** The residue-field point of one
elementary étale neighborhood of `x` factors through that of any other, compatibly with the
morphisms to the space: both are monic field-valued representatives of `x`. -/
theorem exists_residueFieldObject_hom (V W : ElementaryEtaleNeighborhood B S hS X hX x) :
    ∃ g : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶
        residueFieldObject B S hS W.scheme W.point W.residueField_contained,
      yoneda.map (g ≫ residueFieldMap B S hS W.scheme W.point W.residueField_contained) ≫
          W.toSpace =
        yoneda.map (residueFieldMap B S hS V.scheme V.point V.residueField_contained) ≫
          V.toSpace := by
  have := mono_neighborhoodFieldPoint B S hS X hX x V
  have := mono_neighborhoodFieldPoint B S hS X hX x W
  obtain ⟨e, he⟩ := iso_of_mono_of_point_eq B S hS X hX
    (neighborhoodFieldPoint B S hS X hX x V) (neighborhoodFieldPoint B S hS X hX x W)
    ((neighborhoodFieldPoint_class B S hS X hX x V).trans
      (neighborhoodFieldPoint_class B S hS X hX x W).symm)
  have he' : yoneda.map e.hom ≫
      yonedaEquiv.symm (neighborhoodFieldPoint B S hS X hX x W).value =
      yonedaEquiv.symm (neighborhoodFieldPoint B S hS X hX x V).value := by
    apply yonedaEquiv.injective
    simpa only [← yonedaEquiv_naturality, Equiv.apply_symm_apply] using he
  obtain ⟨g, hg⟩ : ∃ g : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶
        residueFieldObject B S hS W.scheme W.point W.residueField_contained,
      yoneda.map g ≫ (yoneda.map
            (residueFieldMap B S hS W.scheme W.point W.residueField_contained) ≫ W.toSpace) =
        yoneda.map (residueFieldMap B S hS V.scheme V.point V.residueField_contained) ≫
          V.toSpace := by
    refine ⟨e.hom, ?_⟩
    rw [← neighborhoodFieldPoint_morphism B S hS X hX x W,
      ← neighborhoodFieldPoint_morphism B S hS X hX x V]
    exact he'
  refine ⟨g, ?_⟩
  rw [yoneda.map_comp, Category.assoc]
  exact hg

/-- **The data of a common refinement.** The fibre product of the schemes of two elementary
étale neighborhoods of `x` over the space, with the lift of the residue-field point of the first
determined by the comparison of the two residue-field points. -/
theorem exists_cone_data (V W : ElementaryEtaleNeighborhood B S hS X hX x) :
    ∃ (P : BigFppfOver B S hS) (qV : P ⟶ V.scheme) (qW : P ⟶ W.scheme)
      (_ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map qV))
      (m : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶ P),
      m ≫ qV = residueFieldMap B S hS V.scheme V.point V.residueField_contained ∧
        yoneda.map qW ≫ W.toSpace = yoneda.map qV ≫ V.toSpace ∧
        qW.left.1 (liftedPoint B S hS X hX x V P m) = W.point := by
  obtain ⟨g, hsq⟩ := exists_residueFieldObject_hom B S hS X hX x V W
  have hWp := presheaf_toSpace B S hS X hX x W
  refine ⟨hWp.1.pullback V.toSpace, hWp.1.snd V.toSpace, hWp.1.fst' V.toSpace,
    hWp.2 V.toSpace (hWp.1.fst V.toSpace) (hWp.1.snd V.toSpace) (hWp.1.isPullback V.toSpace),
    hWp.1.lift' (g ≫ residueFieldMap B S hS W.scheme W.point W.residueField_contained)
      (residueFieldMap B S hS V.scheme V.point V.residueField_contained) hsq,
    hWp.1.lift'_snd _ _ hsq, (hWp.1.isPullback' V.toSpace).w,
    map_liftedPoint_comp B S hS X hX x V W _ (hWp.1.fst' V.toSpace) _ g
      (hWp.1.lift'_fst (g ≫ residueFieldMap B S hS W.scheme W.point W.residueField_contained)
        (residueFieldMap B S hS V.scheme V.point V.residueField_contained) hsq)⟩

/-- **Stacks 0BGV, common refinements.** Two elementary étale neighborhoods of `x` admit a
common refinement. -/
@[stacks 0BGV "common refinements: any two elementary étale neighbourhoods admit a third \
  mapping to both"]
theorem exists_cone_objs (V W : ElementaryEtaleNeighborhood B S hS X hX x) :
    ∃ (E : ElementaryEtaleNeighborhood B S hS X hX x) (_ : E ⟶ V) (_ : E ⟶ W), True := by
  obtain ⟨P, qV, qW, hq, m, hm, hover, hpoint⟩ := exists_cone_data B S hS X hX x V W
  exact ⟨ofResidueFieldLift B S hS X hX x V P qV hq m hm,
    ofResidueFieldLiftHom B S hS X hX x V P qV hq m hm, ⟨qW, hover, hpoint⟩, trivial⟩

/-- **Rigidity of the residue-field point.** Two morphisms of elementary étale neighborhoods
agree after composition with the residue-field point of their source: both induce morphisms of
residue-field points over the space, and the canonical morphism of the target into the space is
monic. -/
theorem residueFieldMap_comp_eq {V W : ElementaryEtaleNeighborhood B S hS X hX x} (f g : V ⟶ W) :
    residueFieldMap B S hS V.scheme V.point V.residueField_contained ≫ f.hom =
      residueFieldMap B S hS V.scheme V.point V.residueField_contained ≫ g.hom := by
  have hf := neighborhoodResidueFieldMap_comp B S hS X hX x f
  have hg := neighborhoodResidueFieldMap_comp B S hS X hX x g
  have : Mono (yoneda.map
      (residueFieldMap B S hS W.scheme W.point W.residueField_contained) ≫ W.toSpace) :=
    W.mono_residueField
  have hfg : yoneda.map (neighborhoodResidueFieldMap B S hS X hX x f) =
      yoneda.map (neighborhoodResidueFieldMap B S hS X hX x g) := by
    apply (cancel_mono (yoneda.map
      (residueFieldMap B S hS W.scheme W.point W.residueField_contained) ≫ W.toSpace)).mp
    rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hf, hg,
      Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, f.over, g.over]
  rw [← hf, ← hg, yoneda.map_injective hfg]

/-- A morphism of the site is étale after Yoneda iff its underlying morphism of schemes is. -/
private theorem isEtale_yoneda_map_iff {U V : BigFppfOver B S hS} (q : U ⟶ V) :
    IsEtale B S hS (yoneda.map q) ↔ Etale ((BigFppfOver.toScheme B S hS).map q) :=
  (isEtale_iff_presheaf_of_yoneda B S hS _).trans (presheaf_yoneda_map_etale_iff B S hS q)

/-- **The self-product of a neighborhood over the space.** The fibre product of the scheme of an
elementary étale neighborhood with itself over the space, with its two projections and its
diagonal; the diagonal is étale, being a morphism over the space between algebraic spaces étale
over it. -/
theorem exists_selfProduct_data (W : ElementaryEtaleNeighborhood B S hS X hX x) :
    ∃ (R : BigFppfOver B S hS) (π₁ π₂ : R ⟶ W.scheme) (δ : W.scheme ⟶ R),
      IsPullback (yoneda.map π₁) (yoneda.map π₂) W.toSpace W.toSpace ∧
        δ ≫ π₁ = 𝟙 W.scheme ∧ δ ≫ π₂ = 𝟙 W.scheme ∧
        AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map δ) := by
  have hWp := presheaf_toSpace B S hS X hX x W
  have hR := hWp.1.isPullback' (f' := W.toSpace) W.toSpace
  have hπ₁ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map
      (hWp.1.fst' W.toSpace)) :=
    hWp.2 W.toSpace (yoneda.map (hWp.1.snd W.toSpace)) (hWp.1.fst' W.toSpace)
      (by simpa only [Functor.relativelyRepresentable.map_fst'] using hR.flip)
  refine ⟨hWp.1.pullback W.toSpace, hWp.1.fst' W.toSpace, hWp.1.snd W.toSpace,
    hWp.1.lift' (𝟙 W.scheme) (𝟙 W.scheme) rfl, hR,
    hWp.1.lift'_fst (𝟙 W.scheme) (𝟙 W.scheme) rfl,
    hWp.1.lift'_snd (𝟙 W.scheme) (𝟙 W.scheme) rfl, ?_⟩
  refine (isEtale_yoneda_map_iff B S hS _).1 ?_
  refine isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS W.scheme)
    (isAlgebraicSpace_yoneda B S hS (hWp.1.pullback W.toSpace)) hX _ W.toSpace
    (yoneda.map (hWp.1.fst' W.toSpace) ≫ W.toSpace) W.etale_toSpace
    (isEtale_comp B S hS ((isEtale_yoneda_map_iff B S hS _).2 hπ₁) W.etale_toSpace) ?_
  rw [← Category.assoc, ← Functor.map_comp,
    hWp.1.lift'_fst (𝟙 W.scheme) (𝟙 W.scheme) rfl]
  simp

/-- **The data of an equalizing refinement.** For two morphisms `f, g : V ⟶ W` of elementary
étale neighborhoods of `x`, the fibre product of `(f, g) : V ⟶ W ×_X W` with the diagonal of
`W` over the space, together with the lift of the residue-field point of `V` which the rigidity
of that point provides. -/
theorem exists_equalizer_data {V W : ElementaryEtaleNeighborhood B S hS X hX x} (f g : V ⟶ W) :
    ∃ (T : BigFppfOver B S hS) (t : T ⟶ V.scheme)
      (_ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map t))
      (m : residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶ T),
      m ≫ t = residueFieldMap B S hS V.scheme V.point V.residueField_contained ∧
        t ≫ f.hom = t ≫ g.hom := by
  obtain ⟨R, π₁, π₂, δ, hR, hδ₁, hδ₂, hδetale⟩ := exists_selfProduct_data B S hS X hX x W
  have hfg : yoneda.map f.hom ≫ W.toSpace = yoneda.map g.hom ≫ W.toSpace :=
    f.over.trans g.over.symm
  obtain ⟨a, ha₁, ha₂⟩ : ∃ a : V.scheme ⟶ R, a ≫ π₁ = f.hom ∧ a ≫ π₂ = g.hom := by
    refine ⟨yoneda.preimage (hR.lift (yoneda.map f.hom) (yoneda.map g.hom) hfg),
      yoneda.map_injective ?_, yoneda.map_injective ?_⟩ <;>
      rw [Functor.map_comp, yoneda.map_preimage]
    exacts [hR.lift_fst _ _ _, hR.lift_snd _ _ _]
  have key : (residueFieldMap B S hS V.scheme V.point V.residueField_contained ≫ f.hom) ≫ δ =
      residueFieldMap B S hS V.scheme V.point V.residueField_contained ≫ a := by
    apply yoneda.map_injective
    refine hR.hom_ext ?_ ?_
    · rw [← Functor.map_comp, ← Functor.map_comp]
      simp only [Category.assoc, hδ₁, ha₁, Category.comp_id]
    · rw [← Functor.map_comp, ← Functor.map_comp]
      simp only [Category.assoc, hδ₂, ha₂, Category.comp_id]
      exact congrArg yoneda.map (residueFieldMap_comp_eq B S hS X hX x f g)
  have hδp := (presheaf_yoneda_map_etale_iff B S hS δ).2 hδetale
  have hT := hδp.1.isPullback_of_map (F := yoneda) a
  refine ⟨hδp.1.pullback (yoneda.map a), hδp.1.snd (yoneda.map a),
    hδp.2 (yoneda.map a) (hδp.1.fst (yoneda.map a)) (hδp.1.snd (yoneda.map a))
      (hδp.1.isPullback (yoneda.map a)),
    hδp.1.lift' (residueFieldMap B S hS V.scheme V.point V.residueField_contained ≫ f.hom)
      (residueFieldMap B S hS V.scheme V.point V.residueField_contained)
      (by rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg yoneda.map key),
    hδp.1.lift'_snd _ _ _, ?_⟩
  rw [← ha₁, ← ha₂, ← Category.assoc, ← Category.assoc, ← hT.w, Category.assoc, Category.assoc,
    hδ₁, hδ₂]

/-- **Stacks 0BGV, equalizing refinements.** Two morphisms of elementary étale neighborhoods of
`x` are equalized by a refinement of their source. -/
@[stacks 0BGV "equalizing refinements: any two parallel morphisms are equalized by a \
  refinement"]
theorem exists_cone_maps {V W : ElementaryEtaleNeighborhood B S hS X hX x} (f g : V ⟶ W) :
    ∃ (E : ElementaryEtaleNeighborhood B S hS X hX x) (h : E ⟶ V), h ≫ f = h ≫ g := by
  obtain ⟨T, t, ht, m, hm, heq⟩ := exists_equalizer_data B S hS X hX x f g
  refine ⟨ofResidueFieldLift B S hS X hX x V T t ht m hm,
    ofResidueFieldLiftHom B S hS X hX x V T t ht m hm, ?_⟩
  apply Hom.ext
  exact heq

/-- **Stacks 0BGV.** The category of elementary étale neighborhoods of a point of an algebraic
space is cofiltered as soon as it is nonempty: any two neighborhoods are refined by a third,
and any two parallel morphisms are equalized by a refinement. -/
@[stacks 0BGV "the category is cofiltered or empty; unconditional"]
instance isCofilteredOrEmpty : IsCofilteredOrEmpty (ElementaryEtaleNeighborhood B S hS X hX x)
    where
  cone_objs V W := exists_cone_objs B S hS X hX x V W
  cone_maps {_V _W} f g := exists_cone_maps B S hS X hX x f g

/-- **Stacks 0BGV.** The category of elementary étale neighborhoods of a point of an algebraic
space, if nonempty, is cofiltered. -/
@[stacks 0BGV "cofilteredness, with nonemptiness -- which is Tag 0BBP, absent from this \
  library -- as an explicit hypothesis"]
theorem isCofiltered_of_nonempty
    (hne : Nonempty (ElementaryEtaleNeighborhood B S hS X hX x)) :
    IsCofiltered (ElementaryEtaleNeighborhood B S hS X hX x) :=
  { nonempty := hne }

end Cofiltered

end ElementaryEtaleNeighborhood

end AlgebraicGeometry.Space

end
