module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaSquare

/-!
# The second diagonal is the identity section of the inertia

Fix a base category `𝒞`, categories `p𝒮 : 𝒮 ⥤ 𝒞` and `p𝒮' : 𝒮' ⥤ 𝒞` over `𝒞` and a 1-morphism
`G : 𝒮 ⥤ 𝒮'` over `𝒞`. Write `Δ_G : 𝒮 ⥤ 𝒮 ×_{G, 𝒮', G} 𝒮` for the diagonal
(`CategoryTheory.TwoFibreProductOver.diagonal`). The *second diagonal* of `G` is the diagonal of
`Δ_G`,

`Δ_{Δ_G} : 𝒮 ⥤ 𝒮 ×_{Δ_G, 𝒮 ×_{𝒮'} 𝒮, Δ_G} 𝒮`.

This file identifies its target with the relative inertia `I_{𝒮/𝒮'}` of Stacks 034I
(`CategoryTheory.RelativeInertia`) and `Δ_{Δ_G}` itself with the neutral section `x ↦ (x, 𝟙 x)`
of the inertia, which is the identification the proof of Stacks 07WG opens with (Categories,
Section 4.34).

The comparison functor sends an object `(x, y, φ)` of the second 2-fibre product to the pair
`(x, φ₁ ∘ φ₂⁻¹)`, where `φ₁`, `φ₂ : x ⟶ y` are the two components of the comparison isomorphism
`φ : Δ_G x ≅ Δ_G y`; the comparison square of the 2-fibre product says exactly that `G φ₁` and
`G φ₂` agree, so that composite is an automorphism of `x` killed by `G`. Its quasi-inverse sends
`(x, α)` to `(x, x, (α, 𝟙 x))`, and the two composites are the identity up to the canonical
isomorphism; as for the inertia square of Stacks 04Z6, the comparison is an equivalence **over
`𝒞`**, which is what `CategoryTheory.IsEquivalenceOver` records.

Everything here is formal: no hypothesis beyond `G ⋙ p𝒮' = p𝒮` is used.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.DiagonalFibreProduct`: the target
  `𝒮 ×_{Δ_G, 𝒮 ×_{𝒮'} 𝒮, Δ_G} 𝒮` of the second diagonal.
* `CategoryTheory.TwoFibreProductOver.isoFst`, `CategoryTheory.TwoFibreProductOver.isoSnd`: the
  two components of the comparison isomorphism of one of its objects.
* `CategoryTheory.TwoFibreProductOver.diagonalAut`: the automorphism of `x` attached to an object
  of the second 2-fibre product.
* `CategoryTheory.TwoFibreProductOver.toRelativeInertia`,
  `CategoryTheory.TwoFibreProductOver.ofRelativeInertia`: the comparison functor and its
  quasi-inverse, and `CategoryTheory.TwoFibreProductOver.unitIso` the unit of the equivalence.

## Main results

* `CategoryTheory.TwoFibreProductOver.diagonal_comp_toRelativeInertia`: the second diagonal
  corresponds to the neutral section of the inertia.
* `CategoryTheory.TwoFibreProductOver.isEquivalenceOver_toRelativeInertia`: the comparison
  functor is an equivalence over `𝒞`, and
  `CategoryTheory.TwoFibreProductOver.isEquivalence_toRelativeInertia` the underlying equivalence
  of categories.
* `CategoryTheory.TwoFibreProductOver.isEquivalence_diagonal_diagonal_iff`: the second diagonal is
  an equivalence exactly when the neutral section of the inertia is.
-/

@[expose] public section

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒮 : Type u₂} [Category.{v₂} 𝒮]
variable {𝒮' : Type u₃} [Category.{v₃} 𝒮']
variable {p𝒮 : 𝒮 ⥤ 𝒞} {p𝒮' : 𝒮' ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'}

-- As in `StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal`: the two components of `Δ_G x`
-- are the same object `x` of `𝒮`, and the composites of components below need that at instance
-- transparency, which a plain `def` does not provide.
attribute [local instance_reducible] diagonal

/-- The diagonal is strictly over `𝒞`, so it is a 1-morphism of categories over `𝒞` and has
itself a diagonal. -/
lemma diagonal_comp_structureFunctor (hG : G ⋙ p𝒮' = p𝒮) :
    diagonal hG ⋙ structureFunctor p𝒮 p𝒮 p𝒮' G G = p𝒮 :=
  rfl

/-- The 2-fibre product `𝒮 ×_{Δ_G, 𝒮 ×_{𝒮'} 𝒮, Δ_G} 𝒮` of the diagonal of `G` with itself, the
target of the second diagonal of `G`. -/
abbrev DiagonalFibreProduct (hG : G ⋙ p𝒮' = p𝒮) : Type _ :=
  TwoFibreProductOver p𝒮 p𝒮 (structureFunctor p𝒮 p𝒮 p𝒮' G G) (diagonal hG) (diagonal hG)

section

variable (hG : G ⋙ p𝒮' = p𝒮) (T : DiagonalFibreProduct hG)

/-- The first components of the comparison isomorphism of an object `T = (x, y, φ)` of the
second 2-fibre product form an isomorphism `x ≅ y`. -/
@[simps]
def isoFst : T.x ≅ T.y where
  hom := T.iso.hom.a
  inv := T.iso.inv.a
  hom_inv_id := by
    simpa only [comp_a, id_a, diagonal_obj_x] using congrArg Hom.a T.iso.hom_inv_id
  inv_hom_id := by
    simpa only [comp_a, id_a, diagonal_obj_x] using congrArg Hom.a T.iso.inv_hom_id

/-- The second components of the comparison isomorphism of an object `T = (x, y, φ)` of the
second 2-fibre product form an isomorphism `x ≅ y`. -/
@[simps]
def isoSnd : T.x ≅ T.y where
  hom := T.iso.hom.b
  inv := T.iso.inv.b
  hom_inv_id := by
    simpa only [comp_b, id_b, diagonal_obj_y] using congrArg Hom.b T.iso.hom_inv_id
  inv_hom_id := by
    simpa only [comp_b, id_b, diagonal_obj_y] using congrArg Hom.b T.iso.inv_hom_id

/-- The automorphism of `T.x` attached to an object `T = (x, y, φ)` of the second 2-fibre
product: the composite `φ₁ ∘ φ₂⁻¹` of the first component of `φ` with the inverse of its second
component. -/
def diagonalAut : Aut T.x :=
  .of (isoFst hG T ≪≫ (isoSnd hG T).symm)

/-- The automorphism attached to `T` is `φ₁` followed by the inverse of `φ₂`. -/
@[simp] lemma diagonalAut_hom :
    (diagonalAut hG T).asIso.hom = (isoFst hG T).hom ≫ (isoSnd hG T).inv :=
  rfl

/-- Its inverse is `φ₂` followed by the inverse of `φ₁`. -/
@[simp] lemma diagonalAut_inv :
    (diagonalAut hG T).asIso.inv = (isoSnd hG T).hom ≫ (isoFst hG T).inv :=
  rfl

/-- The automorphism attached to an object of the second 2-fibre product is killed by `G`: the
comparison square of the 2-fibre product identifies the images of the two components of its
comparison isomorphism. -/
lemma map_diagonalAut_hom : G.map (diagonalAut hG T).asIso.hom = 𝟙 (G.obj T.x) := by
  rw [diagonalAut_hom, isoFst_hom, isoSnd_inv, G.map_comp,
    map_eq_of_hom_diagonal hG T.iso.hom, ← G.map_comp,
    show T.iso.hom.b ≫ T.iso.inv.b = 𝟙 T.x from (isoSnd hG T).hom_inv_id]
  exact G.map_id T.x

/-- The first components of a morphism of the second 2-fibre product commute with the comparison
isomorphisms of its source and target. -/
lemma comp_isoFst_hom {T₁ T₂ : DiagonalFibreProduct hG} (φ : T₁ ⟶ T₂) :
    φ.a ≫ (isoFst hG T₂).hom = (isoFst hG T₁).hom ≫ φ.b := by
  simpa only [isoFst_hom, comp_a, diagonal_map_a] using congrArg Hom.a φ.w

/-- The second components of a morphism of the second 2-fibre product commute with the
comparison isomorphisms of its source and target. -/
lemma comp_isoSnd_hom {T₁ T₂ : DiagonalFibreProduct hG} (φ : T₁ ⟶ T₂) :
    φ.a ≫ (isoSnd hG T₂).hom = (isoSnd hG T₁).hom ≫ φ.b := by
  simpa only [isoSnd_hom, comp_b, diagonal_map_b] using congrArg Hom.b φ.w

/-- The inverse form of `CategoryTheory.TwoFibreProductOver.comp_isoSnd_hom`. -/
lemma isoSnd_inv_comp {T₁ T₂ : DiagonalFibreProduct hG} (φ : T₁ ⟶ T₂) :
    (isoSnd hG T₁).inv ≫ φ.a = φ.b ≫ (isoSnd hG T₂).inv := by
  refine (cancel_epi (isoSnd hG T₁).hom).mp ?_
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Category.assoc,
    ← comp_isoSnd_hom hG φ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The automorphisms attached to the source and the target of a morphism of the second 2-fibre
product are conjugate by its first component. -/
lemma comp_diagonalAut_hom {T₁ T₂ : DiagonalFibreProduct hG} (φ : T₁ ⟶ T₂) :
    φ.a ≫ (diagonalAut hG T₂).asIso.hom = (diagonalAut hG T₁).asIso.hom ≫ φ.a := by
  rw [diagonalAut_hom, diagonalAut_hom, ← Category.assoc, comp_isoFst_hom, Category.assoc,
    ← isoSnd_inv_comp, Category.assoc]

end

/-- The comparison functor from the second 2-fibre product of `G` to the relative inertia
`I_{𝒮/𝒮'}`: it sends `(x, y, φ)` to `(x, φ₁ ∘ φ₂⁻¹)` and a morphism to its first component. -/
def toRelativeInertia (hG : G ⋙ p𝒮' = p𝒮) : DiagonalFibreProduct hG ⥤ RelativeInertia G where
  obj T := ⟨T.x, diagonalAut hG T, map_diagonalAut_hom hG T⟩
  map φ := ⟨φ.a, comp_diagonalAut_hom hG φ⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The comparison functor keeps the first component of an object. -/
@[simp] lemma toRelativeInertia_obj_obj (hG : G ⋙ p𝒮' = p𝒮) (T : DiagonalFibreProduct hG) :
    ((toRelativeInertia hG).obj T).obj = T.x :=
  rfl

/-- The automorphism it attaches to an object is
`CategoryTheory.TwoFibreProductOver.diagonalAut`. -/
@[simp] lemma toRelativeInertia_obj_auto (hG : G ⋙ p𝒮' = p𝒮) (T : DiagonalFibreProduct hG) :
    ((toRelativeInertia hG).obj T).auto = diagonalAut hG T :=
  rfl

/-- The comparison functor keeps the first component of a morphism. -/
@[simp] lemma toRelativeInertia_map_hom (hG : G ⋙ p𝒮' = p𝒮)
    {T T' : DiagonalFibreProduct hG} (φ : T ⟶ T') :
    ((toRelativeInertia hG).map φ).hom = φ.a :=
  rfl

/-- The comparison functor is the first projection followed by the forgetful functor of the
inertia. -/
lemma toRelativeInertia_comp_π (hG : G ⋙ p𝒮' = p𝒮) :
    toRelativeInertia hG ⋙ RelativeInertia.π G =
      fst p𝒮 p𝒮 (structureFunctor p𝒮 p𝒮 p𝒮' G G) (diagonal hG) (diagonal hG) :=
  rfl

/-- The comparison functor is a 1-morphism of categories over `𝒞`. -/
lemma toRelativeInertia_comp_relativeInertiaStruct (hG : G ⋙ p𝒮' = p𝒮) :
    toRelativeInertia hG ⋙ relativeInertiaStruct G p𝒮 =
      structureFunctor p𝒮 p𝒮 (structureFunctor p𝒮 p𝒮 p𝒮' G G) (diagonal hG) (diagonal hG) := by
  rw [relativeInertiaStruct_eq, ← Functor.assoc, toRelativeInertia_comp_π, fst_comp_eq]

/-- **The second diagonal is the identity section of the inertia.** Composing the second diagonal
of `G` with the comparison functor gives the neutral section `x ↦ (x, 𝟙 x)` of the relative
inertia `I_{𝒮/𝒮'}`. -/
lemma diagonal_comp_toRelativeInertia (hG : G ⋙ p𝒮' = p𝒮) :
    diagonal (diagonal_comp_structureFunctor hG) ⋙ toRelativeInertia hG =
      RelativeInertia.neutralSection G :=
  CategoryTheory.Functor.ext
    (fun x => RelativeInertia.obj_ext rfl
      (show (𝟙 x ≫ 𝟙 x : x ⟶ x) = 𝟙 x ≫ 𝟙 x ≫ 𝟙 x by simp))
    (fun x y f => RelativeInertiaHom.ext (by
      simp only [RelativeInertia.comp_hom, RelativeInertiaHom.eqToHom_hom]
      exact show f = 𝟙 x ≫ f ≫ 𝟙 y by simp))

/-! ### The quasi-inverse -/

section

variable (hG : G ⋙ p𝒮' = p𝒮)

include hG in
/-- A morphism of `𝒮` killed by `G` is vertical over `𝒞`: `p𝒮` factors through `G`. -/
lemma map_eq_id_of_map_eq_id {z : 𝒮} (α : z ⟶ z) (hα : G.map α = 𝟙 (G.obj z)) :
    p𝒮.map α = 𝟙 (p𝒮.obj z) := by
  have h := Functor.congr_hom hG.symm α
  have hid : (G ⋙ p𝒮').map α = 𝟙 ((G ⋙ p𝒮').obj z) := by simp [hα]
  rw [h, hid]
  simp

/-- The base morphism of the comparison isomorphism of an object of the second 2-fibre product is
the canonical identification of the bases of its two components. -/
lemma iso_hom_hbase (T : DiagonalFibreProduct hG) :
    T.iso.hom.hbase = eqToHom T.hx ≫ eqToHom T.hy.symm := by
  have := T.vertical
  have h := IsHomLift.fac' (structureFunctor p𝒮 p𝒮 p𝒮' G G) (𝟙 T.base) T.iso.hom
  rw [structureFunctor_map] at h
  rw [h]
  simp only [Category.id_comp, eqToHom_trans]
  rfl

/-- The second component of the comparison isomorphism lies over the canonical identification of
the bases. -/
lemma map_isoSnd_hom (T : DiagonalFibreProduct hG) :
    p𝒮.map (isoSnd hG T).hom = eqToHom T.hx ≫ eqToHom T.hy.symm := by
  have := T.iso.hom.hb
  have h := IsHomLift.fac' p𝒮 T.iso.hom.hbase T.iso.hom.b
  rw [isoSnd_hom, h]
  simp only [iso_hom_hbase hG T, eqToHom_trans]

/-- The inverse of the second component of the comparison isomorphism lies over the canonical
identification of the bases. -/
lemma map_isoSnd_inv (T : DiagonalFibreProduct hG) :
    p𝒮.map (isoSnd hG T).inv = eqToHom T.hy ≫ eqToHom T.hx.symm := by
  rw [← cancel_epi (p𝒮.map (isoSnd hG T).hom), ← p𝒮.map_comp, Iso.hom_inv_id, p𝒮.map_id,
    map_isoSnd_hom hG T]
  simp

/-- The vertical isomorphism of the 2-product `𝒮 ×_{𝒮'} 𝒮` attached to an automorphism of an
object of `𝒮` killed by `G`: the pair `(α, 𝟙)`. -/
def isoOfAut (A : RelativeInertia G) :
    (diagonal hG).obj A.obj ≅ (diagonal hG).obj A.obj where
  hom :=
    { hbase := 𝟙 (p𝒮.obj A.obj)
      a := A.auto.asIso.hom
      b := 𝟙 A.obj
      ha := IsHomLift.of_fac' p𝒮 _ A.auto.asIso.hom rfl rfl
        (by simp [map_eq_id_of_map_eq_id hG A.auto.asIso.hom A.cond])
      hb := IsHomLift.id rfl
      w := by simp [A.cond] }
  inv :=
    { hbase := 𝟙 (p𝒮.obj A.obj)
      a := A.auto.asIso.inv
      b := 𝟙 A.obj
      ha := IsHomLift.of_fac' p𝒮 _ A.auto.asIso.inv rfl rfl
        (by simp [map_eq_id_of_map_eq_id hG A.auto.asIso.inv A.cond_inv])
      hb := IsHomLift.id rfl
      w := by simp [A.cond_inv] }
  hom_inv_id := Hom.ext' A.auto.asIso.hom_inv_id (Category.id_comp (𝟙 A.obj))
  inv_hom_id := Hom.ext' A.auto.asIso.inv_hom_id (Category.id_comp (𝟙 A.obj))

/-- The isomorphism attached to an automorphism is vertical: its base morphism is an identity. -/
@[simp] lemma isoOfAut_hom_hbase (A : RelativeInertia G) :
    (isoOfAut hG A).hom.hbase = 𝟙 (p𝒮.obj A.obj) :=
  rfl

/-- Its inverse is vertical too. -/
@[simp] lemma isoOfAut_inv_hbase (A : RelativeInertia G) :
    (isoOfAut hG A).inv.hbase = 𝟙 (p𝒮.obj A.obj) :=
  rfl

/-- Its first component is the automorphism. -/
@[simp] lemma isoOfAut_hom_a (A : RelativeInertia G) :
    (isoOfAut hG A).hom.a = A.auto.asIso.hom :=
  rfl

/-- Its second component is the identity. -/
@[simp] lemma isoOfAut_hom_b (A : RelativeInertia G) :
    (isoOfAut hG A).hom.b = 𝟙 A.obj :=
  rfl

/-- The first component of its inverse is the inverse automorphism. -/
@[simp] lemma isoOfAut_inv_a (A : RelativeInertia G) :
    (isoOfAut hG A).inv.a = A.auto.asIso.inv :=
  rfl

/-- The second component of its inverse is the identity. -/
@[simp] lemma isoOfAut_inv_b (A : RelativeInertia G) :
    (isoOfAut hG A).inv.b = 𝟙 A.obj :=
  rfl

/-- The quasi-inverse of the comparison functor: an object `(x, α)` of the relative inertia goes
to the object `(x, x, (α, 𝟙 x))` of the second 2-fibre product. -/
def ofRelativeInertia : RelativeInertia G ⥤ DiagonalFibreProduct hG where
  obj A :=
    { base := p𝒮.obj A.obj
      x := A.obj
      y := A.obj
      hx := rfl
      hy := rfl
      iso := isoOfAut hG A
      vertical :=
        IsHomLift.map (p := structureFunctor p𝒮 p𝒮 p𝒮' G G) (isoOfAut hG A).hom }
  map f :=
    { hbase := p𝒮.map f.hom
      a := f.hom
      b := f.hom
      ha := IsHomLift.map (p := p𝒮) f.hom
      hb := IsHomLift.map (p := p𝒮) f.hom
      w := Hom.ext' f.comm
        ((Category.comp_id f.hom).trans (Category.id_comp f.hom).symm) }
  map_id _ := Hom.ext' rfl rfl
  map_comp _ _ := Hom.ext' rfl rfl

/-- The quasi-inverse is a 1-morphism of categories over `𝒞`. -/
lemma ofRelativeInertia_comp_structureFunctor :
    ofRelativeInertia hG ⋙
        structureFunctor p𝒮 p𝒮 (structureFunctor p𝒮 p𝒮 p𝒮' G G) (diagonal hG) (diagonal hG) =
      relativeInertiaStruct G p𝒮 :=
  rfl

/-! ### The comparison is an equivalence over the base -/

/-- The comparison morphism from an object `T = (x, y, φ)` of the second 2-fibre product to the
object `(x, x, (φ₁ ∘ φ₂⁻¹, 𝟙 x))` attached to its automorphism: the identity on the first
component, and `φ₂⁻¹` on the second. -/
def unitHom (T : DiagonalFibreProduct hG) :
    T ⟶ (ofRelativeInertia hG).obj ((toRelativeInertia hG).obj T) where
  hbase := eqToHom T.hx.symm
  a := 𝟙 T.x
  b := (isoSnd hG T).inv
  ha := IsHomLift.id_lift_eqToHom_domain T.hx.symm T.hx
  hb := by
    have h := IsHomLift.map (p := p𝒮) (isoSnd hG T).inv
    rw [map_isoSnd_inv hG T] at h
    exact (IsHomLift.lift_eqToHom_comp_iff p𝒮 _ _ T.hy).mp h
  w := Hom.ext'
    (Category.id_comp ((isoFst hG T).hom ≫ (isoSnd hG T).inv))
    ((Category.id_comp (𝟙 T.x)).trans ((isoSnd hG T).hom_inv_id).symm)

/-- The base morphism of the comparison morphism identifies the two bases. -/
@[simp] lemma unitHom_hbase (T : DiagonalFibreProduct hG) :
    (unitHom hG T).hbase = eqToHom T.hx.symm :=
  rfl

/-- Its first component is the identity. -/
@[simp] lemma unitHom_a (T : DiagonalFibreProduct hG) : (unitHom hG T).a = 𝟙 T.x :=
  rfl

/-- Its second component is the inverse of `φ₂`. -/
@[simp] lemma unitHom_b (T : DiagonalFibreProduct hG) :
    (unitHom hG T).b = (isoSnd hG T).inv :=
  rfl

/-- The automorphism attached to `T` composed with the second component of its comparison
isomorphism is the first component. -/
lemma diagonalAut_hom_comp_isoSnd_hom (T : DiagonalFibreProduct hG) :
    (diagonalAut hG T).asIso.hom ≫ (isoSnd hG T).hom = (isoFst hG T).hom := by
  rw [diagonalAut_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The inverse of `CategoryTheory.TwoFibreProductOver.unitHom`: the identity on the first
component and `φ₂` on the second. -/
def unitInv (T : DiagonalFibreProduct hG) :
    (ofRelativeInertia hG).obj ((toRelativeInertia hG).obj T) ⟶ T where
  hbase := eqToHom T.hx
  a := 𝟙 T.x
  b := (isoSnd hG T).hom
  ha := IsHomLift.id_lift_eqToHom_domain T.hx rfl
  hb := by
    have h := IsHomLift.map (p := p𝒮) (isoSnd hG T).hom
    rw [map_isoSnd_hom hG T] at h
    exact (IsHomLift.lift_comp_eqToHom_iff p𝒮 _ _ T.hy.symm).mp h
  w := Hom.ext'
    ((Category.id_comp (isoFst hG T).hom).trans
      (diagonalAut_hom_comp_isoSnd_hom hG T).symm)
    rfl

/-- The comparison isomorphism between an object of the second 2-fibre product and the object
attached to its automorphism. -/
def unitIsoApp (T : DiagonalFibreProduct hG) :
    T ≅ (ofRelativeInertia hG).obj ((toRelativeInertia hG).obj T) where
  hom := unitHom hG T
  inv := unitInv hG T
  hom_inv_id := Hom.ext' (Category.id_comp (𝟙 T.x)) (isoSnd hG T).inv_hom_id
  inv_hom_id := Hom.ext' (Category.id_comp (𝟙 T.x)) (isoSnd hG T).hom_inv_id

/-- The unit isomorphism of the equivalence: its component at `T` is
`CategoryTheory.TwoFibreProductOver.unitIsoApp`. -/
def unitIso :
    𝟭 (DiagonalFibreProduct hG) ≅ toRelativeInertia hG ⋙ ofRelativeInertia hG :=
  NatIso.ofComponents (unitIsoApp hG)
    (fun φ => Hom.ext'
      ((Category.comp_id φ.a).trans (Category.id_comp φ.a).symm)
      (isoSnd_inv_comp hG φ).symm)

/-- The component of the unit at `T` is `CategoryTheory.TwoFibreProductOver.unitHom`. -/
@[simp] lemma unitIso_hom_app (T : DiagonalFibreProduct hG) :
    (unitIso hG).hom.app T = unitHom hG T :=
  rfl

/-- Composing the quasi-inverse with the comparison functor gives the identity of the relative
inertia. -/
lemma ofRelativeInertia_comp_toRelativeInertia :
    ofRelativeInertia hG ⋙ toRelativeInertia hG = 𝟭 (RelativeInertia G) :=
  CategoryTheory.Functor.ext
    (fun A => RelativeInertia.obj_ext rfl
      (show A.auto.asIso.hom ≫ 𝟙 A.obj = 𝟙 A.obj ≫ A.auto.asIso.hom ≫ 𝟙 A.obj by simp))
    (fun A B f => RelativeInertiaHom.ext (by
      simp only [RelativeInertia.comp_hom, RelativeInertiaHom.eqToHom_hom]
      exact show f.hom = 𝟙 A.obj ≫ f.hom ≫ 𝟙 B.obj by simp))

/-- **The second 2-fibre product of the diagonal is the relative inertia.** The comparison
functor `(x, y, φ) ↦ (x, φ₁ ∘ φ₂⁻¹)` from `𝒮 ×_{Δ_G, 𝒮 ×_{𝒮'} 𝒮, Δ_G} 𝒮` to the relative
inertia `I_{𝒮/𝒮'}` is an equivalence **over `𝒞`**: its quasi-inverse, unit and counit are all
over `𝒞`. Together with
`CategoryTheory.TwoFibreProductOver.diagonal_comp_toRelativeInertia`, which identifies the second
diagonal of `G` with the neutral section of the inertia, this is the identification the proof of
Stacks 07WG opens with. -/
theorem isEquivalenceOver_toRelativeInertia :
    Nonempty (IsEquivalenceOver
      (structureFunctor p𝒮 p𝒮 (structureFunctor p𝒮 p𝒮 p𝒮' G G) (diagonal hG) (diagonal hG))
      (relativeInertiaStruct G p𝒮) (toRelativeInertia hG)) :=
  ⟨{ inverse := ofRelativeInertia hG
     unitIso := unitIso hG
     counitIso := eqToIso (ofRelativeInertia_comp_toRelativeInertia hG)
     functor_unitIso_comp := fun T => RelativeInertiaHom.ext (by
       simp only [unitIso_hom_app, toRelativeInertia_map_hom, unitHom_a, eqToIso.hom,
         RelativeInertia.comp_hom, RelativeInertiaHom.eqToHom_hom, eqToHom_app,
         RelativeInertia.id_hom]
       exact Category.id_comp (𝟙 T.x))
     functor_over := toRelativeInertia_comp_relativeInertiaStruct hG
     inverse_over := ofRelativeInertia_comp_structureFunctor hG
     unit_over := fun T => by
       simp only [unitIso_hom_app, structureFunctor_map, unitHom_hbase]
       rfl
     counit_over := fun A => by
       simp only [eqToIso.hom, eqToHom_app, eqToHom_map] }⟩

/-- The comparison functor is an equivalence of the underlying categories. -/
theorem isEquivalence_toRelativeInertia : (toRelativeInertia hG).IsEquivalence := by
  obtain ⟨E⟩ := isEquivalenceOver_toRelativeInertia hG
  exact E.isEquivalence

/-- The second diagonal of `G` is an equivalence exactly when the neutral section of the relative
inertia is: the comparison equivalence identifies the two. -/
theorem isEquivalence_diagonal_diagonal_iff :
    (diagonal (diagonal_comp_structureFunctor hG)).IsEquivalence ↔
      (RelativeInertia.neutralSection G).IsEquivalence := by
  have := isEquivalence_toRelativeInertia hG
  constructor <;> intro h
  · rw [← diagonal_comp_toRelativeInertia hG]
    infer_instance
  · have : (diagonal (diagonal_comp_structureFunctor hG) ⋙ toRelativeInertia hG).IsEquivalence := by
      rwa [diagonal_comp_toRelativeInertia hG]
    exact Functor.isEquivalence_of_comp_right _ (toRelativeInertia hG)

end

end CategoryTheory.TwoFibreProductOver

end
