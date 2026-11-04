module

public import StacksFrontier.AlgebraicGeometry.Quot.CartesianFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.IsomorphismLocusInRelativeMorphisms
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesDiagonal
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso
public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf

/-!
# The fibres of the stack of proper flat families, as relative morphisms

The stack `Spaces'_{fp, flat, proper}` of **Stacks 0D1D** is fibred in groupoids over the big fppf
site of `S` by **Stacks 0D1E**, so for a scheme `U` of the site it has a fibre category over `U`,
and for two objects `x`, `y` of that fibre the presheaf `Isom(x, y)` of **Stacks 02ZB** on the
slice `(Sch/U)` is defined. This file identifies its sections with the *relative isomorphisms* of
**Stacks 05Y1** between the two families `Z = space x` and `X = space y` over
`h_U`: a section of `Isom(x, y)` over `b : V ⟶ U` is an isomorphism `b^* x ≅ b^* y` in the fibre
over `V`, and the chosen pullback `b^* x` is a fibre product `h_V ×_{h_U} Z`, so such an
isomorphism is exactly a relative morphism whose first component is `h_b` and whose morphism of
base changes is invertible.

That identification is the comparison the proof of **Stacks 0D1F** needs between the abstract
isomorphism presheaf of a fibre and the concrete isomorphism functor `Isom_U(Z, X)`.

## Main definitions

* `AlgebraicGeometry.ProperFlatFibre.underlying`: the functor taking a finitely presented, flat
  and proper family to the algebraic space carrying it, as a presheaf on the site.
* `AlgebraicGeometry.ProperFlatFibre.str`: the structure morphism `Z ⟶ h_U` of an object of the
  fibre over `U`.
* `AlgebraicGeometry.ProperFlatFibre.pullIso`: the chosen pullback of an object of the fibre along
  `b : V ⟶ U` is the fibre product `h_V ×_{h_U} Z`.
* `AlgebraicGeometry.ProperFlatFibre.relativeSection`: the relative morphism of Stacks 05Y1
  attached to a morphism `b^* x ⟶ b^* y` of the fibre over `V`.

## Main results

* `AlgebraicGeometry.ProperFlatFibre.isPullback_map`: a morphism of the fibred category over
  `g : U ⟶ V` is a cartesian square of structure morphisms. This is Stacks 04U9 read on the proper
  flat families, and it is what makes `AlgebraicGeometry.ProperFlatFibre.pullIso` exist.
* `AlgebraicGeometry.ProperFlatFibre.relativeSection_baseChangeMap`: the morphism of base changes
  of the relative morphism attached to `m` is `m` conjugated by the two comparisons of
  `AlgebraicGeometry.ProperFlatFibre.pullIso`. Everything else is read off this.
* `AlgebraicGeometry.ProperFlatFibre.relativeSection_comp` and
  `AlgebraicGeometry.ProperFlatFibre.relativeSection_id`: the attachment is compatible with
  composition and identities of the fibre.
* `AlgebraicGeometry.ProperFlatFibre.relativeSection_injective` and
  `AlgebraicGeometry.ProperFlatFibre.relativeSection_surjective`: the relative *isomorphisms*
  whose first component is `h_b` are exactly the ones attached to an isomorphism of the fibre, and
  no two morphisms of the fibre give the same relative morphism.

## References

* [Stacks Project, Tag 0D1D](https://stacks.math.columbia.edu/tag/0D1D)
* [Stacks Project, Tag 0D1E](https://stacks.math.columbia.edu/tag/0D1E)
* [Stacks Project, Tag 0D1F](https://stacks.math.columbia.edu/tag/0D1F)
* [Stacks Project, Tag 04U9](https://stacks.math.columbia.edu/tag/04U9)
* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
* [Stacks Project, Tag 05Y1](https://stacks.math.columbia.edu/tag/05Y1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w₁ w₂

namespace AlgebraicGeometry.ProperFlatFibre

/-- **The comparison isomorphism of two fibre products along identical data is the identity.**
This is the step `AlgebraicGeometry.Space.RelativeMorphism.ext_of_base_eq` leaves to its caller
when the two relative morphisms compared have literally the same first component. -/
theorem pullback_congrHom_hom_rfl {C : Type w₁} [Category.{w₂} C] {X Y Z : C} (f : X ⟶ Z)
    (g : Y ⟶ Z) [HasPullback f g] :
    (pullback.congrHom (rfl : f = f) (rfl : g = g)).hom = 𝟙 (pullback f g) := by
  refine pullback.hom_ext ?_ ?_ <;> simp [pullback.congrHom]

/-- **Reassociating a composite through an isomorphism inserted in the middle.** The two sides
are the second component of a composite of relative morphisms, read in the two ways
`AlgebraicGeometry.ProperFlatFibre.relativeSection_comp` compares: on the left the morphism of
the fibre is composed first, on the right each factor is conjugated by the identification of its
chosen pullback with a fibre product. -/
theorem comp_conj {C : Type w₁} [Category.{w₂} C] {X₀ X₁ X₂ X₂' X₃ X₄ : C} (i : X₀ ⟶ X₁)
    (f : X₁ ⟶ X₂) (e : X₂ ≅ X₂') (g : X₂ ⟶ X₃) (k : X₃ ⟶ X₄) :
    i ≫ (f ≫ g) ≫ k = (i ≫ f ≫ e.hom) ≫ e.inv ≫ g ≫ k := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The finitely presented, flat and proper families of Stacks 0D1E, read in the comma category
of Stacks 04U8: forget the cartesianness of the morphisms and the three conditions on the
objects. -/
abbrev comma (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :=
  wideSubcategoryInclusion
      ((stronglyCartesianOver (spacesProjection B S hS)).inverseImage
        (isProperFlatSpace B S hS).ι) ⋙
    (isProperFlatSpace B S hS).ι

/-- The algebraic space carrying a finitely presented, flat and proper family, as a presheaf on
the big fppf site of `S`. -/
abbrev underlying (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :=
  comma B S hS ⋙ Comma.fst _ _ ⋙
    ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The algebraic space carrying an object of the fibre of the proper flat families over `U`. -/
abbrev space {U : BigFppfOver B S hS}
    (x : (cartesianProperFlatProjection B S hS).Fiber U) :=
  (underlying B S hS).obj x.val

/-- The structure morphism `Z ⟶ h_U` of an object of the fibre of the proper flat families over
`U`: its structure morphism in the comma category, followed by the identification of its base
with `U`. -/
def str {U : BigFppfOver B S hS} (x : (cartesianProperFlatProjection B S hS).Fiber U) :
    space x ⟶ yoneda.obj U :=
  ((comma B S hS).obj x.val).hom ≫ yoneda.map (eqToHom x.property)

/-- The morphism of algebraic spaces carrying a morphism of the proper flat families. -/
abbrev map {U V : BigFppfOver B S hS}
    {x : (cartesianProperFlatProjection B S hS).Fiber U}
    {y : (cartesianProperFlatProjection B S hS).Fiber V} (f : x.val ⟶ y.val) :
    space x ⟶ space y :=
  (underlying B S hS).map f

/-- A morphism lying over `g : U ⟶ V` has the projection `g` up to the identifications of the
bases of its source and target with `U` and `V`. -/
private theorem projection_map_comp_eqToHom {U V : BigFppfOver B S hS}
    {x : (cartesianProperFlatProjection B S hS).Fiber U}
    {y : (cartesianProperFlatProjection B S hS).Fiber V} (f : x.val ⟶ y.val) (g : U ⟶ V)
    [(cartesianProperFlatProjection B S hS).IsHomLift g f] :
    (cartesianProperFlatProjection B S hS).map f ≫ eqToHom y.property =
      eqToHom x.property ≫ g := by
  rw [IsHomLift.fac' (cartesianProperFlatProjection B S hS) g f]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- A morphism of the proper flat families lying over `g : U ⟶ V` commutes with the structure
morphisms of the two fibres. -/
theorem map_str {U V : BigFppfOver B S hS}
    {x : (cartesianProperFlatProjection B S hS).Fiber U}
    {y : (cartesianProperFlatProjection B S hS).Fiber V} (f : x.val ⟶ y.val) (g : U ⟶ V)
    [(cartesianProperFlatProjection B S hS).IsHomLift g f] :
    map f ≫ str y = str x ≫ yoneda.map g := by
  have h := projection_map_comp_eqToHom f g
  change ((comma B S hS).map f).left.hom ≫
    ((comma B S hS).obj y.val).hom ≫ yoneda.map (eqToHom y.property) = _
  have hw : ((comma B S hS).map f).left.hom ≫
      ((comma B S hS).obj y.val).hom =
      ((comma B S hS).obj x.val).hom ≫
        yoneda.map ((cartesianProperFlatProjection B S hS).map f) :=
    ((comma B S hS).map f).w
  rw [← Category.assoc, hw, Category.assoc, ← yoneda.map_comp]
  change _ = ((comma B S hS).obj x.val).hom ≫
    yoneda.map (eqToHom x.property) ≫ yoneda.map g
  rw [h, yoneda.map_comp]

/-- A morphism of the fibre over `U` commutes with the structure morphisms. -/
private theorem map_val_str {U : BigFppfOver B S hS}
    {x y : (cartesianProperFlatProjection B S hS).Fiber U} (m : x ⟶ y) :
    map m.val ≫ str y = str x := by
  have _ := m.property
  rw [map_str m.val (𝟙 U), yoneda.map_id, Category.comp_id]

/-- A morphism of the fibre of the proper flat families is determined by the morphism of
algebraic spaces carrying it. -/
theorem map_injective {U : BigFppfOver B S hS}
    {x y : (cartesianProperFlatProjection B S hS).Fiber U} {f g : x ⟶ y}
    (h : map f.val = map g.val) : f = g := by
  apply Functor.Fiber.hom_ext
  apply (comma B S hS).map_injective
  apply Comma.hom_ext
  · exact ObjectProperty.hom_ext _ h
  · change (cartesianProperFlatProjection B S hS).map f.val =
      (cartesianProperFlatProjection B S hS).map g.val
    have _ := f.property
    have _ := g.property
    rw [IsHomLift.fac' (cartesianProperFlatProjection B S hS) (𝟙 U) f.val,
      IsHomLift.fac' (cartesianProperFlatProjection B S hS) (𝟙 U) g.val]

/-- **An isomorphism of the fibre from an isomorphism of the underlying algebraic spaces over
`h_U`.** An isomorphism of the two algebraic spaces commuting with the structure morphisms is an
isomorphism of the fibre: it is a cartesian square because both its horizontal edges are
isomorphisms, and it lies over the identity of `U`. -/
def isoOfUnderlying {U : BigFppfOver B S hS}
    (x y : (cartesianProperFlatProjection B S hS).Fiber U) (e : space x ≅ space y)
    (he : e.hom ≫ str y = str x) : x ≅ y := by
  let exy : (comma B S hS).obj x.val ≅ (comma B S hS).obj y.val :=
    Comma.isoMk (ObjectProperty.isoMk _ e) (eqToIso (x.property.trans y.property.symm)) (by
      change e.hom ≫ (((comma B S hS).obj y.val).hom ≫
        yoneda.map (eqToHom y.property)) =
        ((comma B S hS).obj x.val).hom ≫ yoneda.map (eqToHom x.property) at he
      apply (cancel_mono (yoneda.map (eqToHom y.property))).mp
      change (e.hom ≫ ((comma B S hS).obj y.val).hom) ≫
        yoneda.map (eqToHom y.property) =
        (((comma B S hS).obj x.val).hom ≫
          yoneda.map (eqToHom (x.property.trans y.property.symm))) ≫ _
      simpa only [Category.assoc, ← yoneda.map_comp, eqToHom_trans] using he)
  let ef : x.val ≅ y.val := WideSubcategory.isoMk
    (ObjectProperty.isoMk _ exy)
    (by
      change (spacesProjection B S hS).IsStronglyCartesian
        ((spacesProjection B S hS).map exy.hom) exy.hom
      infer_instance)
    (by
      change (spacesProjection B S hS).IsStronglyCartesian
        ((spacesProjection B S hS).map exy.inv) exy.inv
      infer_instance)
  exact Functor.Fiber.isoMk ef (by
    apply IsHomLift.of_fac' (cartesianProperFlatProjection B S hS) (𝟙 U) ef.hom
      x.property y.property
    change eqToHom (x.property.trans y.property.symm) = _
    simp only [Category.id_comp, eqToHom_trans])

/-- The morphism of algebraic spaces underlying `isoOfUnderlying x y e he` is `e.hom`. -/
@[simp]
theorem isoOfUnderlying_hom {U : BigFppfOver B S hS}
    (x y : (cartesianProperFlatProjection B S hS).Fiber U) (e : space x ≅ space y)
    (he : e.hom ≫ str y = str x) :
    map (isoOfUnderlying x y e he).hom.val = e.hom := rfl

/-- **A morphism of the proper flat families is a cartesian square of structure morphisms.**
This is Stacks 04U9: the morphisms of the fibred category are by definition the strongly
cartesian morphisms of the comma category of Stacks 04U8, and a morphism there is strongly
cartesian exactly when its comparison with the chosen fibre product is an isomorphism. -/
theorem isPullback_map {U V : BigFppfOver B S hS}
    {x : (cartesianProperFlatProjection B S hS).Fiber U}
    {y : (cartesianProperFlatProjection B S hS).Fiber V} (f : x.val ⟶ y.val) (g : U ⟶ V)
    [(cartesianProperFlatProjection B S hS).IsHomLift g f] :
    IsPullback (str x) (map f) (yoneda.map g) (str y) := by
  let m := (comma B S hS).map f
  let A := (comma B S hS).obj x.val
  let C := (comma B S hS).obj y.val
  let k := pullback.lift A.hom m.left.hom m.w.symm
  have hk : IsIso (ObjectProperty.homMk k : A.left ⟶
      AlgebraicSpaces.fiberProduct B S hS (schemeSpaceMap m.right)
        (ObjectProperty.homMk C.hom)) :=
    (spacesProjection_isStronglyCartesian_iff m).mp f.property
  have : IsIso k := (ObjectProperty.ι _).map_isIso (ObjectProperty.homMk k : A.left ⟶
    AlgebraicSpaces.fiberProduct B S hS (schemeSpaceMap m.right)
      (ObjectProperty.homMk C.hom))
  have hp : IsPullback A.hom m.left.hom (yoneda.map m.right) C.hom :=
    IsPullback.of_iso_pullback ⟨m.w.symm⟩ (asIso k)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  refine hp.of_iso (Iso.refl _) (yoneda.mapIso (eqToIso x.property))
    (Iso.refl _) (yoneda.mapIso (eqToIso y.property)) ?_ ?_ ?_ ?_
  · simp only [Functor.mapIso_hom, eqToIso.hom, Iso.refl_hom, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · change yoneda.map ((cartesianProperFlatProjection B S hS).map f) ≫
      yoneda.map (eqToHom y.property) = yoneda.map (eqToHom x.property) ≫ yoneda.map g
    rw [← yoneda.map_comp, ← yoneda.map_comp, projection_map_comp_eqToHom f g]
  · simp only [Functor.mapIso_hom, eqToIso.hom, Iso.refl_hom, Category.id_comp]
    rfl

/-- The projection of the proper flat families is a fibred category, by Stacks 0D1E. -/
theorem isFibered (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (cartesianProperFlatProjection B S hS).IsFibered :=
  (cartesianProperFlatProjection_isFiberedInGroupoids B S hS).isFibered

attribute [local instance] isFibered

/-- The chosen pullback of an object of the fibre over `U` along `b : V ⟶ U`. -/
abbrev pull {U : BigFppfOver B S hS}
    (x : (cartesianProperFlatProjection B S hS).Fiber U) (b : Over U) :=
  Functor.pullbackFiber (cartesianProperFlatProjection B S hS) x b.hom

/-- The chosen cartesian lift of `b : V ⟶ U` at an object of the fibre over `U`. -/
abbrev pullMap {U : BigFppfOver B S hS}
    (x : (cartesianProperFlatProjection B S hS).Fiber U) (b : Over U) :
    (pull x b).val ⟶ x.val :=
  Functor.IsPreFibered.pullbackMap x.property b.hom

/-- **The algebraic space of a chosen pullback is a fibre product.** The chosen cartesian lift of
`b : V ⟶ U` at `x` is a cartesian square by `AlgebraicGeometry.fiber_isPullback`, so the algebraic
space carrying it is the fibre product `h_V ×_{h_U} Z`. -/
def pullIso {U : BigFppfOver B S hS}
    (x : (cartesianProperFlatProjection B S hS).Fiber U) (b : Over U) :
    space (pull x b) ≅ pullback (yoneda.map b.hom) (str x) :=
  (isPullback_map (pullMap x b) b.hom).isoPullback

/-- `pullIso x b` followed by the first projection is the structure morphism of `pull x b`. -/
@[reassoc (attr := simp)]
theorem pullIso_hom_fst {U : BigFppfOver B S hS}
    (x : (cartesianProperFlatProjection B S hS).Fiber U) (b : Over U) :
    (pullIso x b).hom ≫ pullback.fst (yoneda.map b.hom) (str x) =
      str (pull x b) := IsPullback.isoPullback_hom_fst _

/-- `pullIso x b` followed by the second projection is the morphism of spaces of `pullMap x b`. -/
@[reassoc (attr := simp)]
theorem pullIso_hom_snd {U : BigFppfOver B S hS}
    (x : (cartesianProperFlatProjection B S hS).Fiber U) (b : Over U) :
    (pullIso x b).hom ≫ pullback.snd (yoneda.map b.hom) (str x) =
      map (pullMap x b) := IsPullback.isoPullback_hom_snd _

/-- The inverse of `pullIso x b` followed by the structure morphism of `pull x b` is the first
projection of the fibre product `h_V ×_{h_U} Z`. -/
@[reassoc (attr := simp)]
theorem pullIso_inv_fst {U : BigFppfOver B S hS}
    (x : (cartesianProperFlatProjection B S hS).Fiber U) (b : Over U) :
    (pullIso x b).inv ≫ str (pull x b) =
      pullback.fst (yoneda.map b.hom) (str x) := IsPullback.isoPullback_inv_fst _

/-- The inverse of `pullIso x b` followed by the morphism of spaces of `pullMap x b` is the second
projection of the fibre product `h_V ×_{h_U} Z`. -/
@[reassoc (attr := simp)]
theorem pullIso_inv_snd {U : BigFppfOver B S hS}
    (x : (cartesianProperFlatProjection B S hS).Fiber U) (b : Over U) :
    (pullIso x b).inv ≫ map (pullMap x b) =
      pullback.snd (yoneda.map b.hom) (str x) := IsPullback.isoPullback_inv_snd _

/-! ### The relative morphism attached to a morphism of the fibre -/

/-- **The relative morphism of Stacks 05Y1 attached to a morphism of the fibre.** A morphism
`b^* x ⟶ b^* y` of the fibre over `b.left` gives a relative morphism from `Z = space x` to
`X = space y` over `h_U` at the test presheaf `h_{b.left}`, with first component `h_b`: its
second component is the morphism of the chosen pullbacks, read through the identification of
`b^* x` with `h_{b.left} ×_{h_U} Z`. -/
def relativeSection {U : BigFppfOver B S hS}
    (x y : (cartesianProperFlatProjection B S hS).Fiber U) (b : Over U)
    (m : pull x b ⟶ pull y b) :
    Space.RelativeMorphism B S hS (space x) (space y) (yoneda.obj U)
      (str x) (str y) (yoneda.obj b.left) where
  base := yoneda.map b.hom
  morphism := (pullIso x b).inv ≫ map m.val ≫ map (pullMap y b)
  commutes := by
    have _ := m.property
    rw [Category.assoc, Category.assoc, map_str (pullMap y b) b.hom,
      ← Category.assoc (map m.val), map_str m.val (𝟙 b.left)]
    simp only [yoneda.map_id, Category.comp_id]
    rw [← Category.assoc, pullIso_inv_fst, pullback.condition]

attribute [local implicit_reducible] relativeSection

/-- The first component of the relative morphism `relativeSection x y b m` is `h_b`. -/
@[simp]
theorem relativeSection_base {U : BigFppfOver B S hS}
    (x y : (cartesianProperFlatProjection B S hS).Fiber U) (b : Over U)
    (m : pull x b ⟶ pull y b) :
    (relativeSection x y b m).base = yoneda.map b.hom := rfl

/-- **The second component of the relative morphism attached to `m`, lifted into the fibre
product, is `m` itself**, read through the two identifications of the chosen pullbacks with fibre
products. The condition of the lift is a hypothesis so that the statement applies to whichever
proof of it the ambient term carries; the lift itself is the morphism of base changes of
`AlgebraicGeometry.ProperFlatFibre.relativeSection`, and also the comparison map occurring in a
composite of relative morphisms. Everything below is read off this. -/
theorem relativeSection_lift_eq {U : BigFppfOver B S hS}
    (x y : (cartesianProperFlatProjection B S hS).Fiber U) (b : Over U)
    (m : pull x b ⟶ pull y b)
    (w : pullback.fst (yoneda.map b.hom) (str x) ≫ yoneda.map b.hom =
      ((pullIso x b).inv ≫ map m.val ≫ map (pullMap y b)) ≫ str y) :
    pullback.lift (pullback.fst (yoneda.map b.hom) (str x))
        ((pullIso x b).inv ≫ map m.val ≫ map (pullMap y b)) w =
      (pullIso x b).inv ≫ map m.val ≫ (pullIso y b).hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.lift_fst, Category.assoc, Category.assoc, pullIso_hom_fst, map_val_str m,
      pullIso_inv_fst]
  · rw [pullback.lift_snd, Category.assoc, Category.assoc, pullIso_hom_snd]

/-- **The morphism of base changes of the relative morphism attached to `m` is `m` itself**, read
through the two identifications of the chosen pullbacks with fibre products. -/
theorem relativeSection_baseChangeMap {U : BigFppfOver B S hS}
    (x y : (cartesianProperFlatProjection B S hS).Fiber U) (b : Over U)
    (m : pull x b ⟶ pull y b) :
    ((relativeSection x y b m).baseChangeMap :
        pullback (yoneda.map b.hom) (str x) ⟶ pullback (yoneda.map b.hom) (str y)) =
      (pullIso x b).inv ≫ map m.val ≫ (pullIso y b).hom :=
  relativeSection_lift_eq x y b m _

/-- The relative morphism attached to an isomorphism of the fibre is a relative isomorphism. -/
theorem relativeSection_isRelativeIso {U : BigFppfOver B S hS}
    (x y : (cartesianProperFlatProjection B S hS).Fiber U) (b : Over U)
    (m : pull x b ⟶ pull y b) [IsIso m] :
    (relativeSection x y b m).IsRelativeIso := by
  change IsIso ((relativeSection x y b m).baseChangeMap :
    pullback (yoneda.map b.hom) (str x) ⟶ pullback (yoneda.map b.hom) (str y))
  rw [relativeSection_baseChangeMap]
  have : IsIso m.val := Functor.map_isIso Functor.Fiber.fiberInclusion m
  infer_instance

/-- Attaching a relative morphism to a morphism of the fibre is injective: the two components of
the morphism of base changes recover the morphism of the fibre. -/
theorem relativeSection_injective {U : BigFppfOver B S hS}
    (x y : (cartesianProperFlatProjection B S hS).Fiber U) (b : Over U) :
    Function.Injective (relativeSection x y b) := by
  intro m n h
  dsimp only [relativeSection] at h
  injection h with _ h₂
  apply map_injective
  refine (cancel_mono (pullIso y b).hom).mp (pullback.hom_ext ?_ ?_)
  · rw [Category.assoc, Category.assoc, pullIso_hom_fst, map_val_str m,
      map_val_str n]
  · rw [Category.assoc, Category.assoc, pullIso_hom_snd]
    exact (cancel_epi (pullIso x b).inv).mp h₂

/-- Attaching a relative morphism to a morphism of the fibre carries composition in the fibre to
composition of relative morphisms. -/
theorem relativeSection_comp {U : BigFppfOver B S hS}
    (x y w : (cartesianProperFlatProjection B S hS).Fiber U) (b : Over U)
    (m : pull x b ⟶ pull y b) (n : pull y b ⟶ pull w b) :
    relativeSection x w b (m ≫ n) =
      Space.RelativeMorphism.comp (relativeSection x y b m) (relativeSection y w b n) rfl := by
  refine Space.RelativeMorphism.ext_of_base_eq rfl ?_
  dsimp only [relativeSection, Space.RelativeMorphism.comp]
  rw [pullback_congrHom_hom_rfl, Category.id_comp, relativeSection_lift_eq]
  change (pullIso x b).inv ≫ map (x := pull x b) (y := pull w b) (m.val ≫ n.val) ≫
    map (pullMap w b) = _
  rw [show map (x := pull x b) (y := pull w b) (m.val ≫ n.val) = map m.val ≫ map n.val from
    (underlying B S hS).map_comp _ _]
  exact comp_conj _ _ (pullIso y b) _ _

/-- Attaching a relative morphism to a morphism of the fibre carries the identity of the fibre to
the identity relative morphism. -/
theorem relativeSection_id {U : BigFppfOver B S hS}
    (x : (cartesianProperFlatProjection B S hS).Fiber U) (b : Over U) :
    relativeSection x x b (𝟙 (pull x b)) =
      Space.RelativeMorphism.identity (str x) (yoneda.map b.hom) := by
  refine Space.RelativeMorphism.ext_of_base_eq rfl ?_
  dsimp only [relativeSection, Space.RelativeMorphism.identity]
  rw [pullback_congrHom_hom_rfl, Category.id_comp]
  change (pullIso x b).inv ≫ map (x := pull x b) (y := pull x b) (𝟙 (pull x b).val) ≫
    map (pullMap x b) = _
  rw [show map (x := pull x b) (y := pull x b) (𝟙 (pull x b).val) = 𝟙 _ from
    (underlying B S hS).map_id _, Category.id_comp, pullIso_inv_snd]

/-- **Every relative isomorphism whose first component is `h_b` is attached to an isomorphism of
the fibre.** The morphisms of the fibred category of Stacks 0D1E are the cartesian ones, so a
morphism of a fibre is an isomorphism; accordingly it is the *relative isomorphisms* that the
attachment of `AlgebraicGeometry.ProperFlatFibre.relativeSection` hits, and the isomorphism of the
fibre is read off the morphism of base changes through the two comparisons of
`AlgebraicGeometry.ProperFlatFibre.pullIso`. -/
theorem relativeSection_surjective {U : BigFppfOver B S hS}
    (x y : (cartesianProperFlatProjection B S hS).Fiber U) (b : Over U)
    (q : Space.RelativeMorphism B S hS (space x) (space y) (yoneda.obj U)
      (str x) (str y) (yoneda.obj b.left))
    (hb : q.base = yoneda.map b.hom) (hq : q.IsRelativeIso) :
    ∃ m : pull x b ⟶ pull y b, IsIso m ∧ relativeSection x y b m = q := by
  obtain ⟨a, qm, hqcomm⟩ := q
  dsimp only at hb
  subst hb
  let q' : Space.RelativeMorphism B S hS (space x) (space y) (yoneda.obj U)
      (str x) (str y) (yoneda.obj b.left) := ⟨yoneda.map b.hom, qm, hqcomm⟩
  have : IsIso q'.baseChangeMap := hq
  let e : space (pull x b) ≅ space (pull y b) :=
    pullIso x b ≪≫ asIso q'.baseChangeMap ≪≫ (pullIso y b).symm
  have he : e.hom ≫ str (pull y b) = str (pull x b) := by
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, asIso_hom]
    simp only [Category.assoc, pullIso_inv_fst]
    change (pullIso x b).hom ≫ q'.baseChangeMap ≫ pullback.fst _ _ = _
    rw [Space.RelativeMorphism.baseChangeMap_comp_fst]
    exact pullIso_hom_fst x b
  let m := isoOfUnderlying (pull x b) (pull y b) e he
  refine ⟨m.hom, inferInstance, Space.RelativeMorphism.ext_of_base_eq rfl ?_⟩
  dsimp only [relativeSection]
  rw [pullback_congrHom_hom_rfl, Category.id_comp, isoOfUnderlying_hom]
  dsimp only [e, Iso.trans_hom, Iso.symm_hom, asIso_hom]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [Category.assoc, pullIso_inv_snd]
  exact Space.RelativeMorphism.baseChangeMap_comp_snd q'

/-! ### Compatibility with restriction along a morphism of the slice -/

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

/-- The comparison of two fibre products whose second legs agree does not move the first
projection. -/
@[reassoc]
theorem congrHom_hom_fst {C : Type w₁} [Category.{w₂} C] {X Y W : C} {f₁ f₂ : X ⟶ W} (hf : f₁ = f₂)
    (g : Y ⟶ W) [HasPullback f₁ g] [HasPullback f₂ g] :
    (pullback.congrHom hf (rfl : g = g)).hom ≫ pullback.fst f₂ g = pullback.fst f₁ g := by
  cases hf
  rw [pullback_congrHom_hom_rfl, Category.id_comp]

/-- The comparison of two fibre products whose second legs agree does not move the second
projection. -/
@[reassoc]
theorem congrHom_hom_snd {C : Type w₁} [Category.{w₂} C] {X Y W : C} {f₁ f₂ : X ⟶ W} (hf : f₁ = f₂)
    (g : Y ⟶ W) [HasPullback f₁ g] [HasPullback f₂ g] :
    (pullback.congrHom hf (rfl : g = g)).hom ≫ pullback.snd f₂ g = pullback.snd f₁ g := by
  cases hf
  rw [pullback_congrHom_hom_rfl, Category.id_comp]

/-- **The identification of a chosen pullback with a fibre product is compatible with composition
in the slice.** For `h : b ⟶ c` over `U`, the restriction map `b^* x ⟶ c^* x` of the chosen
pullbacks of `x` becomes, through
`AlgebraicGeometry.ProperFlatFibre.pullIso`, the base change map
`h_b ×_{h_U} Z ⟶ h_c ×_{h_U} Z` of fibre products. -/
theorem pullIso_restrict {U : BigFppfOver B S hS}
    (x : (cartesianProperFlatProjection B S hS).Fiber U) {b c : Over U} (h : b ⟶ c)
    (hb : yoneda.map b.hom = yoneda.map h.left ≫ yoneda.map c.hom) :
    (pullIso x b).inv ≫
        map (Functor.pullbackFiberMap (cartesianProperFlatProjection B S hS) x h) =
      (pullback.congrHom hb (rfl : str x = str x)).hom ≫
        pullback.mapFst (yoneda.map h.left) (yoneda.map c.hom) (str x) ≫ (pullIso x c).inv := by
  have hfac : map (Functor.pullbackFiberMap (cartesianProperFlatProjection B S hS) x h) ≫
      map (pullMap x c) = map (pullMap x b) := by
    simpa only [Functor.map_comp] using (underlying B S hS).congr_map
      (Functor.pullbackFiberMap_fac (cartesianProperFlatProjection B S hS) x h)
  refine (cancel_mono (pullIso x c).hom).mp ?_
  rw [Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullIso_hom_fst]
    rw [map_str (Functor.pullbackFiberMap (cartesianProperFlatProjection B S hS) x h) h.left,
      pullIso_inv_fst_assoc, pullback.mapFst_fst, congrHom_hom_fst_assoc]
  · simp only [Category.assoc, pullIso_hom_snd]
    rw [hfac, pullIso_inv_snd, pullback.mapFst_snd, congrHom_hom_snd]

/-- **Attaching a relative morphism to a morphism of the fibre is compatible with restriction
along a morphism of the slice.** This is what makes the attachment a morphism of presheaves on
`(Sch/U)`. -/
theorem relativeSection_restrict {U : BigFppfOver B S hS}
    (x y : (cartesianProperFlatProjection B S hS).Fiber U) {b c : Over U} (h : b ⟶ c)
    (m : pull x c ⟶ pull y c) :
    relativeSection x y b
        (Functor.morRestrict (cartesianProperFlatProjection B S hS) x y h m) =
      Space.RelativeMorphism.restrict (yoneda.map h.left) (relativeSection x y c m) := by
  have hb : yoneda.map b.hom = yoneda.map h.left ≫ yoneda.map c.hom := by
    rw [← yoneda.map_comp, Over.w h]
  have hm : map (Functor.morRestrict (cartesianProperFlatProjection B S hS) x y h m).val ≫
      map (pullMap y b) =
      map (Functor.pullbackFiberMap (cartesianProperFlatProjection B S hS) x h) ≫
        map m.val ≫ map (pullMap y c) := by
    have := (underlying B S hS).congr_map
      (Functor.morRestrict_fac (cartesianProperFlatProjection B S hS) x y h m)
    simp only [Functor.map_comp] at this
    exact this
  refine Space.RelativeMorphism.ext_of_base_eq hb ?_
  rw [Space.RelativeMorphism.restrict_morphism, pullback.map_id_eq_mapFst]
  change (pullIso x b).inv ≫
      map (Functor.morRestrict (cartesianProperFlatProjection B S hS) x y h m).val ≫
        map (pullMap y b) = _
  rw [hm, ← Category.assoc, pullIso_restrict x h hb]
  simp only [Category.assoc]
  rfl

end AlgebraicGeometry.ProperFlatFibre

end
