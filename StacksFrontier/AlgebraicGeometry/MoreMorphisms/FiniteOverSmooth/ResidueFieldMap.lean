module

public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Diagram
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapPullback

/-!
# Residue fields along a fibre product

Stacks 057K builds its étale neighbourhoods as fibre products, and has to know that the residue
field extension it produces agrees with the one Stacks 052E gave. That means knowing when a
projection of a fibre product induces an isomorphism on a residue field, and that the two
resulting residue-field squares commute. Both are collected here.

## Main results

* `AlgebraicGeometry.isIso_residueFieldMap_of_isPreimmersion`: a preimmersion induces
  isomorphisms on residue fields.
* `AlgebraicGeometry.isIso_residueFieldMap_pullback_fst_of_right`: if one projection of a fibre
  product induces an isomorphism on a residue field at a point, so does the other.
* `AlgebraicGeometry.pullback_point_ext_of_isIso_residueFieldMap`: a point of a fibre product is
  determined by its two images when the residue field of one of them is unchanged.
* `AlgebraicGeometry.residueFieldMap_square`: the residue-field square attached to a pointed
  commutative square of schemes commutes.
* `AlgebraicGeometry.algebraMap_residueField_comp_specResidueFieldIso_inv`: the algebra map of a
  residue field of `Spec κ(x)` is the residue field map of `Spec κ(x) ⟶ X`.

## Main definitions

* `AlgebraicGeometry.pullbackPointOfIsIsoResidueFieldMap` is the unique point of a fibre product
  over a given pair of points lying over a common point of the base whose residue field extension
  on the right is trivial, and
  `AlgebraicGeometry.isPullbackPointOfIsIsoResidueFieldMap` is the same point in an arbitrary
  cartesian square.

## Implementation notes

The criterion for a projection is proved for `pullback.snd` and transferred to `pullback.fst` by
`CategoryTheory.Limits.pullbackSymmetry`. For `pullback.snd` the point is written in the
classification of `AlgebraicGeometry.Scheme.Pullback.carrierEquiv`: the tensor product
`κ(x) ⊗_{κ(s)} κ(y)` becomes `κ(y)` when `κ(s) ⟶ κ(x)` is an isomorphism, so `Spec` of it is a
one-point scheme mapping isomorphically, and Tag 01JT identifies the residue field at the
classified prime.

## References

* [Stacks Project, Tag 01JT](https://stacks.math.columbia.edu/tag/01JT)
* [Stacks Project, Tag 02LE](https://stacks.math.columbia.edu/tag/02LE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A preimmersion induces an isomorphism on residue fields, its stalk maps being surjective. -/
theorem isIso_residueFieldMap_of_isPreimmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsPreimmersion f] (x : X) : IsIso (f.residueFieldMap x) :=
  Stacks.Thickenings.isIso_residueFieldMap_of_surjective_stalkMap f x
    (f.stalkMap_surjective x)

/-- The structure map of the residue field of a point `q` of `Spec κ(x)`, read through
`AlgebraicGeometry.Scheme.Spec.residueFieldIso`, is the residue field map of `Spec κ(x) ⟶ X`
transported along the image of `q`. -/
theorem algebraMap_residueField_comp_specResidueFieldIso_inv (X : Scheme.{u}) (x : X)
    (q : Spec (X.residueField x)) [q.asIdeal.IsPrime] (hq : X.fromSpecResidueField x q = x) :
    CommRingCat.ofHom (algebraMap (X.residueField x) q.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of (X.residueField x)) q).inv =
      (X.residueFieldCongr hq).inv ≫ (X.fromSpecResidueField x).residueFieldMap q := by
  set r := X.fromSpecResidueField x with hr
  have hspec : Spec.map ((X.residueFieldCongr hq).inv) ≫ r = X.fromSpecResidueField (r q) := by
    simp [hr]
  refine Spec.map_inj.1 ((cancel_mono r).1 ?_)
  calc
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) q.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of (X.residueField x)) q).inv) ≫ r =
        (Spec (.of (X.residueField x))).fromSpecResidueField q ≫ r := by
      rw [Spec.map_comp, Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    _ = Spec.map (r.residueFieldMap q) ≫ X.fromSpecResidueField (r q) := by
      rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    _ = Spec.map (r.residueFieldMap q) ≫ Spec.map ((X.residueFieldCongr hq).inv) ≫ r :=
      congrArg (fun j ↦ Spec.map (r.residueFieldMap q) ≫ j) hspec.symm
    _ = Spec.map ((X.residueFieldCongr hq).inv ≫ r.residueFieldMap q) ≫ r := by
      rw [Spec.map_comp, Category.assoc]

/-- If the second projection of a fibre product induces an isomorphism on the residue field at a
point, then so does the first. -/
theorem isIso_residueFieldMap_pullback_fst_of_right {X S Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (z : (pullback f g : Scheme.{u}).carrier)
    (hg : IsIso (g.residueFieldMap (pullback.snd f g z))) :
    IsIso ((pullback.fst f g).residueFieldMap z) := by
  set z' := (pullbackSymmetry f g).hom z with hz'
  have hpoint : pullback.fst g f z' = pullback.snd f g z := by
    rw [hz', ← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_fst]
  have hfx : IsIso (g.residueFieldMap (pullback.fst g f z')) :=
    (g.isIso_residueFieldMap_congr hpoint).mpr hg
  have hsecond := pullback_snd_residueFieldMap_isIso g f z' hfx
  have hcomp : IsIso (((pullbackSymmetry f g).hom ≫ pullback.snd g f).residueFieldMap z) := by
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' hsecond inferInstance
  rwa [pullbackSymmetry_hom_comp_snd] at hcomp

/-- The residue-field square attached to a commutative square of schemes with compatible chosen
points commutes. -/
theorem residueFieldMap_square {X X' S S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : X' ⟶ X) (e : S' ⟶ S) (hc : g ≫ f = f' ≫ e)
    (x' : X') (x : X) (s' : S') (s : S)
    (hx : g x' = x) (hs : e s' = s) (hf : f x = s) (hf' : f' x' = s') :
    (S.residueFieldCongr hf).inv ≫ f.residueFieldMap x ≫
        (X.residueFieldCongr hx).inv ≫ g.residueFieldMap x' =
      (S.residueFieldCongr hs).inv ≫ e.residueFieldMap s' ≫
        (S'.residueFieldCongr hf').inv ≫ f'.residueFieldMap x' := by
  subst x s' s
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_inv, Category.id_comp,
    ← Scheme.residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr hc x']
  simp

/-- The residue-field square of `AlgebraicGeometry.residueFieldMap_square` in the case where the
chosen point of `S'` is the image of the chosen point of `X'`, where the transport along that
equality disappears. -/
theorem residueFieldMap_square_of_eq {X X' S S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : X' ⟶ X) (e : S' ⟶ S) (hc : g ≫ f = f' ≫ e) (x' : X') (x : X) (s : S)
    (hx : g x' = x) (hs : e (f' x') = s) (hf : f x = s) :
    (S.residueFieldCongr hf).inv ≫ f.residueFieldMap x ≫
        (X.residueFieldCongr hx).inv ≫ g.residueFieldMap x' =
      (S.residueFieldCongr hs).inv ≫ e.residueFieldMap (f' x') ≫ f'.residueFieldMap x' := by
  have h := residueFieldMap_square f f' g e hc x' x (f' x') s hx hs hf rfl
  rw [Scheme.residueFieldCongr_refl, Iso.refl_inv, Category.id_comp] at h
  exact h

/-- The inclusion of the left residue field in the tensor product of a triplet is an isomorphism
when the transported residue field map on the right is. -/
private theorem isIso_tensorInl_of_isIso {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (T : Scheme.Pullback.Triplet f g)
    (h : IsIso ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)) : IsIso T.tensorInl := by
  change IsIso (pushout.inl _ _)
  infer_instance

/-- A point of a fibre product is determined by its two images as soon as the second projection
induces an isomorphism on the residue field there. -/
theorem pullback_point_ext_of_isIso_residueFieldMap {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (z z' : (pullback f g : Scheme.{u}))
    (hx : pullback.fst f g z = pullback.fst f g z')
    (hy : pullback.snd f g z = pullback.snd f g z')
    (hi : IsIso (g.residueFieldMap (pullback.snd f g z'))) : z = z' := by
  set T := Scheme.Pullback.Triplet.ofPoint z' with hT
  have : IsIso (g.residueFieldMap T.y) := hi
  have : IsIso T.tensorInl := isIso_tensorInl_of_isIso T inferInstance
  have : Subsingleton (Spec T.tensor) :=
    ⟨fun a b ↦ (Spec.map T.tensorInl).homeomorph.injective (Subsingleton.elim _ _)⟩
  refine Scheme.Pullback.carrierEquiv.injective (Scheme.Pullback.carrierEquiv_eq_iff.mpr
    ⟨Scheme.Pullback.Triplet.ext hx hy, ?_⟩)
  show @Eq (Spec T.tensor) _ _
  exact Subsingleton.elim _ _

/-- A point of a fibre product is determined by its two images, in the form in which the two
points are named together with the equality of their images in the base: the right-hand residue
field extension at the named point is the one required to be trivial. -/
theorem pullback_point_eq_of_isIso_residueFieldMap {A B S : Scheme.{u}} (f : A ⟶ S) (g : B ⟶ S)
    (x : A) (y : B) (hxy : f x = g y)
    (hfield : IsIso ((S.residueFieldCongr hxy.symm).inv ≫ g.residueFieldMap y))
    (p q : (pullback f g : Scheme.{u})) (hp : pullback.fst f g p = x)
    (hq : pullback.snd f g p = y) (hp' : pullback.fst f g q = x)
    (hq' : pullback.snd f g q = y) : p = q := by
  refine pullback_point_ext_of_isIso_residueFieldMap f g p q (hp.trans hp'.symm)
    (hq.trans hq'.symm) ?_
  rw [hq']
  exact IsIso.of_isIso_comp_left (S.residueFieldCongr hxy.symm).inv (g.residueFieldMap y)

/-! ### Transporting a residue field map along an equation on points -/

/-- The residue field map of `f` at `x` has source `κ(f x)`; composing it with
`AlgebraicGeometry.Scheme.residueFieldCongr` transports it to a map out of `κ(s)` for any point
`s` given with an equation `f x = s`. Those transported maps compose along a composition of
morphisms. -/
theorem residueFieldCongr_inv_residueFieldMap_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (x : A) (y : B) (z : C) (hf : f x = y) (hg : g y = z) (hfg : (f ≫ g) x = z) :
    (C.residueFieldCongr hfg).inv ≫ (f ≫ g).residueFieldMap x =
      (C.residueFieldCongr hg).inv ≫ g.residueFieldMap y ≫
        (B.residueFieldCongr hf).inv ≫ f.residueFieldMap x := by
  subst hf
  subst hg
  simp [Scheme.residueFieldMap_comp]

/-- The transported residue field map is unchanged when the morphism is replaced by an equal
one. -/
theorem residueFieldCongr_inv_residueFieldMap_eq_of_eq {X Y : Scheme.{u}} {g h : X ⟶ Y}
    (e : g = h) (x : X) (y : Y) (hg : g x = y) (hh : h x = y) :
    (Y.residueFieldCongr hg).inv ≫ g.residueFieldMap x =
      (Y.residueFieldCongr hh).inv ≫ h.residueFieldMap x := by
  subst h
  have hh' : hh = hg := Subsingleton.elim _ _
  subst hh'
  rfl

/-- A composition of morphisms induces an isomorphism of residue fields at a point at which both
factors do. -/
theorem isIso_residueFieldMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hf : IsIso (f.residueFieldMap x)) (hg : IsIso (g.residueFieldMap (f x))) :
    IsIso ((f ≫ g).residueFieldMap x) := by
  rw [Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' hg hf

/-- If the transported residue field maps of a composition and of its second factor are
isomorphisms, then so is that of its first factor. -/
theorem isIso_residueFieldCongr_inv_residueFieldMap_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (x : X) (y : Y) (z : Z) (hf : f x = y) (hg : g y = z) (hfg : (f ≫ g) x = z)
    (hcomp : IsIso ((Z.residueFieldCongr hfg).inv ≫ (f ≫ g).residueFieldMap x))
    (hgIso : IsIso ((Z.residueFieldCongr hg).inv ≫ g.residueFieldMap y)) :
    IsIso ((Y.residueFieldCongr hf).inv ≫ f.residueFieldMap x) := by
  rw [residueFieldCongr_inv_residueFieldMap_comp f g x y z hf hg hfg] at hcomp
  have : IsIso ((Z.residueFieldCongr hg).inv ≫ g.residueFieldMap y) := hgIso
  have : IsIso (((Z.residueFieldCongr hg).inv ≫ g.residueFieldMap y) ≫
      (Y.residueFieldCongr hf).inv ≫ f.residueFieldMap x) := by
    simpa only [Category.assoc] using hcomp
  exact IsIso.of_isIso_comp_left
    ((Z.residueFieldCongr hg).inv ≫ g.residueFieldMap y)
    ((Y.residueFieldCongr hf).inv ≫ f.residueFieldMap x)

/-- A morphism of a cartesian square induces an isomorphism of residue fields at a point at which
the morphism opposite to it does. -/
theorem isIso_residueFieldMap_of_isPullback {P X Y S : Scheme.{u}} {i : P ⟶ X} {j : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (H : IsPullback i j f g) (p : P)
    (hg : IsIso (g.residueFieldMap (j p))) : IsIso (i.residueFieldMap p) := by
  have hqj : pullback.snd f g (H.isoPullback.hom p) = j p := by
    rw [← Scheme.Hom.comp_apply, H.isoPullback_hom_snd]
  have hfst : IsIso ((pullback.fst f g).residueFieldMap (H.isoPullback.hom p)) :=
    isIso_residueFieldMap_pullback_fst_of_right f g _ (by rw [hqj]; exact hg)
  have hcomp : IsIso ((H.isoPullback.hom ≫ pullback.fst f g).residueFieldMap p) := by
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' hfst (by infer_instance)
  rw [H.isoPullback_hom_fst] at hcomp
  exact hcomp

/-! ### The unique point of a fibre product above a trivial residue field extension -/

/-- The point of `X ×_S Y` determined by points `x : X` and `y : Y` lying over a common point of
`S` whose residue field extension on the right is trivial. There is exactly one such point,
because the tensor product classifying them is then `κ(x)`, a field. -/
def pullbackPointOfIsIsoResidueFieldMap {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X)
    (y : Y) (s : S) (hx : f x = s) (hy : g y = s)
    (hiso : IsIso ((S.residueFieldCongr hy).inv ≫ g.residueFieldMap y)) :
    (pullback f g : Scheme.{u}) := by
  let T : Scheme.Pullback.Triplet f g := ⟨x, y, s, hx, hy⟩
  have : IsIso ((S.residueFieldCongr hy).inv ≫ g.residueFieldMap y) := hiso
  have : IsIso T.tensorInl := by
    change IsIso (pushout.inl _ _)
    infer_instance
  letI : Field T.tensor :=
    (MulEquiv.isField (Field.toIsField (X.residueField x))
      (asIso T.tensorInl).symm.commRingCatIsoToRingEquiv.toMulEquiv).toField
  exact T.SpecTensorTo (IsLocalRing.closedPoint T.tensor)

/-- The two projections of `AlgebraicGeometry.pullbackPointOfIsIsoResidueFieldMap` are the given
points. -/
private theorem pullbackPointOfIsIsoResidueFieldMap_fst_snd {X Y S : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) (x : X) (y : Y) (s : S) (hx : f x = s) (hy : g y = s)
    (hiso : IsIso ((S.residueFieldCongr hy).inv ≫ g.residueFieldMap y)) :
    pullback.fst f g (pullbackPointOfIsIsoResidueFieldMap f g x y s hx hy hiso) = x ∧
      pullback.snd f g (pullbackPointOfIsIsoResidueFieldMap f g x y s hx hy hiso) = y := by
  let T : Scheme.Pullback.Triplet f g := ⟨x, y, s, hx, hy⟩
  have : IsIso T.tensorInl := isIso_tensorInl_of_isIso T hiso
  let : Field T.tensor :=
    (MulEquiv.isField (Field.toIsField (X.residueField x))
      (asIso T.tensorInl).symm.commRingCatIsoToRingEquiv.toMulEquiv).toField
  let p : Spec T.tensor := IsLocalRing.closedPoint T.tensor
  have hspecl : Spec.map T.tensorInl p = IsLocalRing.closedPoint (X.residueField x) :=
    Subsingleton.elim _ _
  have hspecr : Spec.map T.tensorInr p = IsLocalRing.closedPoint (Y.residueField y) :=
    Subsingleton.elim _ _
  have hl := congrArg (fun q : Spec T.tensor ⟶ X => q p) T.specTensorTo_fst
  have hr := congrArg (fun q : Spec T.tensor ⟶ Y => q p) T.specTensorTo_snd
  change pullback.fst f g (T.SpecTensorTo p) =
    X.fromSpecResidueField x (Spec.map T.tensorInl p) at hl
  change pullback.snd f g (T.SpecTensorTo p) =
    Y.fromSpecResidueField y (Spec.map T.tensorInr p) at hr
  rw [hspecl] at hl
  rw [hspecr] at hr
  exact ⟨hl.trans (Scheme.fromSpecResidueField_apply x _),
    hr.trans (Scheme.fromSpecResidueField_apply y _)⟩

/-- The first projection of `AlgebraicGeometry.pullbackPointOfIsIsoResidueFieldMap` is the given
point of the left-hand scheme. -/
theorem pullbackPointOfIsIsoResidueFieldMap_fst {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (x : X) (y : Y) (s : S) (hx : f x = s) (hy : g y = s)
    (hiso : IsIso ((S.residueFieldCongr hy).inv ≫ g.residueFieldMap y)) :
    pullback.fst f g (pullbackPointOfIsIsoResidueFieldMap f g x y s hx hy hiso) = x :=
  (pullbackPointOfIsIsoResidueFieldMap_fst_snd f g x y s hx hy hiso).1

/-- The second projection of `AlgebraicGeometry.pullbackPointOfIsIsoResidueFieldMap` is the given
point of the right-hand scheme. -/
theorem pullbackPointOfIsIsoResidueFieldMap_snd {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (x : X) (y : Y) (s : S) (hx : f x = s) (hy : g y = s)
    (hiso : IsIso ((S.residueFieldCongr hy).inv ≫ g.residueFieldMap y)) :
    pullback.snd f g (pullbackPointOfIsIsoResidueFieldMap f g x y s hx hy hiso) = y :=
  (pullbackPointOfIsIsoResidueFieldMap_fst_snd f g x y s hx hy hiso).2

/-- The point of the vertex of a cartesian square determined by points of the two outer schemes
lying over a common point whose residue field extension on the right is trivial. -/
def isPullbackPointOfIsIsoResidueFieldMap {P X Y S : Scheme.{u}} {i : P ⟶ X} {j : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (H : IsPullback i j f g) (x : X) (y : Y) (s : S) (hx : f x = s)
    (hy : g y = s) (hiso : IsIso ((S.residueFieldCongr hy).inv ≫ g.residueFieldMap y)) : P :=
  H.isoPullback.inv (pullbackPointOfIsIsoResidueFieldMap f g x y s hx hy hiso)

/-- The left-hand projection of `AlgebraicGeometry.isPullbackPointOfIsIsoResidueFieldMap` is the
given point. -/
theorem isPullbackPointOfIsIsoResidueFieldMap_fst {P X Y S : Scheme.{u}} {i : P ⟶ X} {j : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (H : IsPullback i j f g) (x : X) (y : Y) (s : S) (hx : f x = s)
    (hy : g y = s) (hiso : IsIso ((S.residueFieldCongr hy).inv ≫ g.residueFieldMap y)) :
    i (isPullbackPointOfIsIsoResidueFieldMap H x y s hx hy hiso) = x := by
  set z := pullbackPointOfIsIsoResidueFieldMap f g x y s hx hy hiso
  have hcancel : H.isoPullback.hom (H.isoPullback.inv z) = z :=
    congr($(H.isoPullback.inv_hom_id).base z)
  calc
    i (H.isoPullback.inv z) =
        (H.isoPullback.hom ≫ pullback.fst f g) (H.isoPullback.inv z) := by
      rw [H.isoPullback_hom_fst]
    _ = pullback.fst f g z := by rw [Scheme.Hom.comp_apply, hcancel]
    _ = x := pullbackPointOfIsIsoResidueFieldMap_fst f g x y s hx hy hiso

/-- The right-hand projection of `AlgebraicGeometry.isPullbackPointOfIsIsoResidueFieldMap` is the
given point. -/
theorem isPullbackPointOfIsIsoResidueFieldMap_snd {P X Y S : Scheme.{u}} {i : P ⟶ X} {j : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (H : IsPullback i j f g) (x : X) (y : Y) (s : S) (hx : f x = s)
    (hy : g y = s) (hiso : IsIso ((S.residueFieldCongr hy).inv ≫ g.residueFieldMap y)) :
    j (isPullbackPointOfIsIsoResidueFieldMap H x y s hx hy hiso) = y := by
  set z := pullbackPointOfIsIsoResidueFieldMap f g x y s hx hy hiso
  have hcancel : H.isoPullback.hom (H.isoPullback.inv z) = z :=
    congr($(H.isoPullback.inv_hom_id).base z)
  calc
    j (H.isoPullback.inv z) =
        (H.isoPullback.hom ≫ pullback.snd f g) (H.isoPullback.inv z) := by
      rw [H.isoPullback_hom_snd]
    _ = pullback.snd f g z := by rw [Scheme.Hom.comp_apply, hcancel]
    _ = y := pullbackPointOfIsIsoResidueFieldMap_snd f g x y s hx hy hiso

end AlgebraicGeometry

end
