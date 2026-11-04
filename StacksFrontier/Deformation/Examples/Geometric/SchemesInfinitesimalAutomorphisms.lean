module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationFiberAut
public import StacksFrontier.Deformation.Examples.Geometric.SchemesPredeformation
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Infinitesimal automorphisms of the deformation category of a scheme are self-maps

Let `k` be a field and `X` a scheme over `k`. This file connects the abstract infinitesimal
automorphism group `Inf(𝓓_X)` of [Stacks Project, Tag 06JS], formed from the deformation category
of [Stacks Project, Tag 0DY7], with honest self-maps of the total space of a deformation of `X`
over the dual numbers.

Two things are proved.

* **Every fibre automorphism is infinitesimal.** The condition defining
  `Deformation.infinitesimalAutomorphisms` is that an automorphism commute with the canonical
  retraction `r` back to the chosen point over the residue field. For the deformation category of
  a scheme this is automatic: the component of `r` on total spaces satisfies
  `x₀.specialMap ≫ r.map = xε.specialMap`, the component of the automorphism fixes
  `xε.specialMap`, and `x₀.specialMap` is invertible by
  `Deformation.Examples.isIso_specialMap_of_base_eq_residueFieldObject`, so cancelling it gives
  `r.map ≫ a.map = r.map`. Hence the subgroup is the whole automorphism group.

* **The automorphism group of a point of the fibre does not depend on how the fibre is
  indexed.** `Deformation.infinitesimalAutomorphismGroup` is formed at a point `xε` of the fibre
  over an object `Aε` of `𝒞_Λ`, whereas
  `Deformation.Examples.fiberAutEquivLiftsOverBaseTop` describes the automorphisms of a
  deformation `P` in the fibre over `P.base`. The two fibres are indexed by `Aε` and by
  `xε.1.base`, which are equal but not identical, and a morphism of either is an arrow of the
  deformation category whose base component is the identity.
  `Deformation.Examples.autFiberBaseMulEquiv` is the resulting isomorphism of groups, the identity
  on underlying arrows.

Composing the two with `Deformation.Examples.fiberAutEquivLiftsOverBaseTop` presents `Inf(𝓓_X)`
as the set of self-maps of the total space of `xε` over its base fixing the special-fibre
immersion — equivalently, as the global lifts of the identity of `X`. That is the passage from
the abstract group to geometry; the identification of the lift set with `Der_k(𝒪_X, 𝒪_X)` is the
simply-transitive action of [Stacks Project, Tag 04FJ] and is not in this file.

## Main definitions

* `Deformation.Examples.autFiberBaseMulEquiv`: re-indexing the fibre does not change the
  automorphism group of a deformation.
* `Deformation.Examples.infinitesimalAutomorphismGroupMulEquivFiberAut`: `Inf(𝓓_X)` is the full
  automorphism group of the point in its fibre.
* `Deformation.Examples.infinitesimalAutomorphismGroupEquivLiftsOverBaseTop`: `Inf(𝓓_X)` is the
  set of global lifts of the identity of `X` to the total space of the deformation.

## Main results

* `Deformation.Examples.schemeDeformationFiberAut_base_eq_id`: an automorphism of a point of a
  fibre acts as the identity on the base object of the deformation.
* `Deformation.Examples.infinitesimalAutomorphisms_schemeDeformation_eq_top`: every fibre
  automorphism of a deformation of a scheme is an infinitesimal automorphism.

## Implementation notes

`Deformation.Examples.schemeDeformationFiberAut_base_eq_id` repeats
`Deformation.Examples.deformationFiberHom_base` for a fibre indexed by an arbitrary `Aε` rather
than by `P.base`; the proof is the lifting condition read through
`CategoryTheory.Functor.IsHomLift.fac'`, whose right-hand side is a composite of two `eqToHom`s
that `simp` collapses. It is stated separately because that lemma is available only at the
`P.base` indexing, which is exactly the mismatch `autFiberBaseMulEquiv` exists to absorb.

Both proofs are written in term mode where they touch arrows of a fibre. The goals produced by
`CategoryTheory.Functor.Fiber.hom_ext` are spelled through
`CategoryTheory.Functor.Fiber.fiberInclusion`, which is definitionally but not reducibly the
first projection of the fibre subtype, so `rw` and `simp` refuse the motive while `exact` crosses
the identification.

No `@[stacks]` attribute is carried here: none of these declarations states a whole clause of a
source lemma. They are the geometric reading of `Inf(𝓓_X)` that the infinitesimal-automorphism
clause of [Stacks Project, Tag 0DY9] is assembled from.

## References

* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 06JQ](https://stacks.math.columbia.edu/tag/06JQ)
* [Stacks Project, Tag 06JS](https://stacks.math.columbia.edu/tag/06JS)
* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X : Over (Spec (CommRingCat.of k))}

/-! ### Automorphisms of a point of an arbitrarily indexed fibre -/

/-- The two identifications of an object `x` with `Aε` cancel. -/
private theorem eqToHom_id_comp_eqToHom_symm {C : Type*} [Category C] {x A : C} (h : x = A) :
    eqToHom h ≫ 𝟙 A ≫ eqToHom h.symm = 𝟙 x := by
  simp

/-- An arrow of the fibre over `Aε` between points of the deformation category acts as the
identity on the base object of the deformation: the lifting condition expresses its base
component as a composite of two identifications of that object with `Aε`. -/
theorem schemeDeformationFiberAut_base_eq_id
    {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber Aε}
    (f : xε ⟶ xε) : f.val.base = 𝟙 xε.1.base := by
  have := f.2
  have hfac := IsHomLift.fac' (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X)
    (𝟙 Aε) f.val
  exact hfac.trans (eqToHom_id_comp_eqToHom_symm xε.2)

/-- The lifting condition over the identity of `Aε`, in the form
`CategoryTheory.Functor.IsHomLift.of_fac'` consumes: an arrow of the deformation category whose
base component is the identity of `xε.1.base` lies over the identity of `Aε`, the two
identifications of `xε.1.base` with `Aε` cancelling. -/
theorem schemeDeformationFiberAut_fac
    {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber Aε)
    {f : xε.1 ⟶ xε.1} (hf : f.base = 𝟙 xε.1.base) :
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).map f
      = eqToHom xε.2 ≫ 𝟙 Aε ≫ eqToHom xε.2.symm := by
  exact hf.trans (eqToHom_id_comp_eqToHom_symm xε.2).symm

/-- **Re-indexing the fibre does not change the automorphism group of a deformation.** A point
`xε` of the fibre over `Aε` and the same deformation read in the fibre over its own base object
have the same automorphisms, because an arrow of either fibre is an arrow of the deformation
category whose base component is the identity of `xε.1.base`. The isomorphism is the identity on
underlying arrows. -/
def autFiberBaseMulEquiv {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber Aε) :
    Aut xε ≃* Aut (deformationFiberObj xε.1) where
  toFun a :=
    { hom := ⟨a.hom.val, deformationFiberHom_isHomLift a.hom.val
        (schemeDeformationFiberAut_base_eq_id a.hom)⟩
      inv := ⟨a.inv.val, deformationFiberHom_isHomLift a.inv.val
        (schemeDeformationFiberAut_base_eq_id a.inv)⟩
      hom_inv_id := Functor.Fiber.hom_ext
        (congrArg (fun b : xε ⟶ xε => b.val) a.hom_inv_id)
      inv_hom_id := Functor.Fiber.hom_ext
        (congrArg (fun b : xε ⟶ xε => b.val) a.inv_hom_id) }
  invFun a :=
    { hom := ⟨a.hom.val, IsHomLift.of_fac' _ (𝟙 Aε) a.hom.val xε.2 xε.2
        (schemeDeformationFiberAut_fac xε (deformationFiberHom_base a.hom))⟩
      inv := ⟨a.inv.val, IsHomLift.of_fac' _ (𝟙 Aε) a.inv.val xε.2 xε.2
        (schemeDeformationFiberAut_fac xε (deformationFiberHom_base a.inv))⟩
      hom_inv_id := Functor.Fiber.hom_ext
        (congrArg (fun b : deformationFiberObj xε.1 ⟶ deformationFiberObj xε.1 => b.val)
          a.hom_inv_id)
      inv_hom_id := Functor.Fiber.hom_ext
        (congrArg (fun b : deformationFiberObj xε.1 ⟶ deformationFiberObj xε.1 => b.val)
          a.inv_hom_id) }
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-! ### Every fibre automorphism is infinitesimal -/

/-- **Every automorphism of a point of the deformation category of a scheme in its fibre is an
infinitesimal automorphism.** Membership means commuting with the canonical retraction `r` to the
chosen point `x₀` over the residue field. On base objects both sides are the base component of
`r`, the automorphism acting as the identity there. On total spaces, `r` satisfies
`x₀.specialMap ≫ r.map = xε.specialMap` and the automorphism fixes `xε.specialMap`, so
`x₀.specialMap ≫ (r.map ≫ a.map) = x₀.specialMap ≫ r.map`; and `x₀.specialMap` is invertible,
because `x₀` lies over the residue field, so it may be cancelled.

Consequently `Inf(𝓓_X)` is the whole of `Aut xε`, which is what makes it a group of honest
self-maps of the total space. -/
theorem infinitesimalAutomorphisms_schemeDeformation_eq_top
    {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {x₀ : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber
      (residueFieldObject.{u, u, u} Λ k)}
    {xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber Aε}
    (g : residueFieldObject.{u, u, u} Λ k ⟶ Aε) (e : Aε ⟶ residueFieldObject.{u, u, u} Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1)
    (hi : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).IsHomLift g i) :
    infinitesimalAutomorphisms
        (schemeDeformationCategoryProjection_cofiberedInGroupoids X) g e hpair i hi = ⊤ := by
  have hx₀ : IsIso x₀.1.specialMap :=
    isIso_specialMap_of_base_eq_residueFieldObject x₀.1 x₀.2
  apply top_unique
  intro a _
  rw [mem_infinitesimalAutomorphisms_iff]
  set r := (canonicalRetraction
    (schemeDeformationCategoryProjection_cofiberedInGroupoids X) g e hpair.split i hi).1 with hr
  have hrs : x₀.1.specialMap ≫ r.map = xε.1.specialMap := r.special_compat
  apply SchemeDeformationCategory.Hom.ext
  · show a.hom.val.base ≫ r.base = r.base
    rw [schemeDeformationFiberAut_base_eq_id a.hom, Category.id_comp]
  · show r.map ≫ a.hom.val.map = r.map
    refine (cancel_epi x₀.1.specialMap).mp ?_
    calc x₀.1.specialMap ≫ r.map ≫ a.hom.val.map
        = xε.1.specialMap ≫ a.hom.val.map := by rw [← Category.assoc, hrs]
      _ = xε.1.specialMap := a.hom.val.special_compat
      _ = x₀.1.specialMap ≫ r.map := hrs.symm

/-! ### `Inf(𝓓_X)` as a group of self-maps -/

/-- **`Inf(𝓓_X)` is the full automorphism group of the point in its fibre**, by
`Deformation.Examples.infinitesimalAutomorphisms_schemeDeformation_eq_top`. -/
@[sga "3 VIIA 1.5" "special case"]
def infinitesimalAutomorphismGroupMulEquivFiberAut
    (hp : IsPredeformationCategory
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {x₀ : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber
      (residueFieldObject.{u, u, u} Λ k)}
    {xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber Aε}
    (g : residueFieldObject.{u, u, u} Λ k ⟶ Aε) (e : Aε ⟶ residueFieldObject.{u, u, u} Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1)
    (hi : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).IsHomLift g i) :
    infinitesimalAutomorphismGroup hp g e hpair i hi ≃* Aut (deformationFiberObj xε.1) :=
  (MulEquiv.subgroupCongr
      (Subgroup.ext fun a => by
        rw [Subsingleton.elim hp.cofibered
          (schemeDeformationCategoryProjection_cofiberedInGroupoids X),
          infinitesimalAutomorphisms_schemeDeformation_eq_top g e hpair i hi])).trans
    ((Subgroup.topEquiv (G := Aut xε)).trans (autFiberBaseMulEquiv xε))

/-- **`Inf(𝓓_X)` is the set of global lifts of the identity of `X` to the total space of the
deformation**: the composite of
`Deformation.Examples.infinitesimalAutomorphismGroupMulEquivFiberAut` with
`Deformation.Examples.fiberAutEquivLiftsOverBaseTop`. This is the passage from the abstract
infinitesimal automorphism group to self-maps of a scheme. -/
@[sga "3 VIIA 1.5" "special case"]
def infinitesimalAutomorphismGroupEquivLiftsOverBaseTop
    (hp : IsPredeformationCategory
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {x₀ : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber
      (residueFieldObject.{u, u, u} Λ k)}
    {xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber Aε}
    (g : residueFieldObject.{u, u, u} Λ k ⟶ Aε) (e : Aε ⟶ residueFieldObject.{u, u, u} Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1)
    (hi : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).IsHomLift g i) :
    infinitesimalAutomorphismGroup hp g e hpair i hi ≃
      Stacks.Thickenings.liftsOverBase xε.1.specialMap xε.1.specialMap xε.1.toBase
        xε.1.toBase (𝟙 X.left) ⊤ :=
  (infinitesimalAutomorphismGroupMulEquivFiberAut hp g e hpair i hi).toEquiv.trans
    (fiberAutEquivLiftsOverBaseTop xε.1)

end Deformation.Examples

end
