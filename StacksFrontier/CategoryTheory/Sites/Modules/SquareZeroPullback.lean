module

public import StacksFrontier.CategoryTheory.Sites.Modules.SquareZeroPushout

/-!
# The fibre product of sheaves of commutative rings, and the square-zero pullback

Let `(C, K)` be a site and let `p : 𝒜 ⟶ ℬ` and `q : 𝒟 ⟶ ℬ` be morphisms of sheaves of
commutative rings on it.  This file constructs the fibre product

`𝒜 ×_ℬ 𝒟`,

sectionwise: over an object `U` of the site its sections are the pairs `(a, d)` with
`p a = q d`.  Unlike the quotient of a sheaf of rings by a sheaf of ideals, this *is* a sheaf
already sectionwise, because the sheaf condition is a limit condition and the fibre product is
one too; so no sheafification appears anywhere in this file and every statement below is an
equality of sections, never a local one.

When `p` is the surjection of a square-zero extension `0 ⟶ 𝒢 ⟶ 𝒜 ⟶ ℬ ⟶ 0` this is the
*square-zero pullback* of that extension along `q`: the second projection
`𝒜 ×_ℬ 𝒟 ⟶ 𝒟` is locally surjective, its kernel on sections is exactly the kernel of `p`
embedded as `(·, 0)`, and that kernel has square zero.  It is the sheaf-level counterpart of
`Stacks.Deformation.pullbackSubalgebra`, the fibre product `C' ×_C B` of [Stacks 0GPW].

## Main definitions

* `Stacks.Sites.SqZeroPullback.fibreSubring`: the subring of pairs `(a, d)` with `p a = q d`.
* `Stacks.Sites.SqZeroPullback.fibrePresheaf` and
  `Stacks.Sites.SqZeroPullback.fibreSheaf`: the fibre product as a presheaf and, by
  `Stacks.Sites.SqZeroPullback.isSheaf_fibrePresheaf`, as a sheaf of commutative rings.
* `Stacks.Sites.SqZeroPullback.fibreFst` and `Stacks.Sites.SqZeroPullback.fibreSnd`: the two
  projections, and `Stacks.Sites.SqZeroPullback.fibreMk` the section attached to a pair.
* `Stacks.Sites.SqZeroPullback.fibrePresheafLift` and
  `Stacks.Sites.SqZeroPullback.fibreLift`: the universal property, for a presheaf and for a
  sheaf mapping compatibly to `𝒜` and `𝒟`, with
  `Stacks.Sites.SqZeroPullback.fibre_hom_ext` its uniqueness half.
* `Stacks.Sites.SqZeroPullback.fibreInr`: the inclusion into the fibre product of a sectionwise
  family realizing the kernel of `p`, with
  `Stacks.Sites.SqZeroPullback.fibreInrHom` its form as a map of additive groups.

## Main results

* `Stacks.Sites.SqZeroPullback.isSheaf_fibrePresheaf`: the sectionwise fibre product is a
  sheaf.
* `Stacks.Sites.SqZeroPullback.fibreSnd_app_eq_zero_iff`: **the kernel of the second
  projection, computed exactly on sections** — a section of the fibre product dies in `𝒟` if
  and only if its second component is `0`, if and only if it is `(a, 0)` with `p a = 0`.
* `Stacks.Sites.SqZeroPullback.isLocallySurjective_fibreSnd`: **right exactness** — the second
  projection is locally surjective whenever `p` is.
* `Stacks.Sites.SqZeroPullback.fibreInr_injective`,
  `Stacks.Sites.SqZeroPullback.fibreSnd_app_eq_zero_iff_exists_fibreInr` and
  `Stacks.Sites.SqZeroPullback.fibreInr_mul_fibreInr`: **left exactness, the kernel and the
  square-zero property** for the inclusion attached to a realization of `Ker p`.
* `Stacks.Sites.SqZeroPullback.fibreMk_mul_fibreInr`: the ideal `Ker p` of the fibre product is
  acted on through `𝒟`.

## Implementation notes

The fibre product is built by hand as the sectionwise subring of the product rather than as
`CategoryTheory.Limits.pullback` in `Sheaf K CommRingCat`.  The limit exists, and
`sheafToPresheaf` preserves it, but every statement in this file and in its consumers is about
*sections*, and reading sections off the limit would mean composing the identification of the
limit in sheaves with the one in presheaves with the one in `CommRingCat`.  Building the subring
directly makes `fibreMk` and the kernel computation definitional.

The inclusion of `Ker p` is not taken to be a sheaf of modules.  What the consumers have is a
sectionwise additive family `ι` realizing `Ker p` — for the square-zero extensions of
[Stacks 0GQ2] it is the inclusion of `𝒢` into `𝒪_{Y'}` — and the three fields
`FibreInrData.app`, `FibreInrData.app_map` and `FibreInrData.range` are exactly that.  No module
structure is needed for any statement here, so none is assumed; the multiplication rule
`fibreMk_mul_fibreInr` is stated as the transport of the rule in `𝒜`.

This module reuses `Stacks.Sites.SqZeroPushout.isSheaf_forgetCommRing` and
`Stacks.Sites.SqZeroPushout.eq_of_locally_eq` from the pushout file rather than restating them;
that is the only reason for the import, and nothing of the pushout construction is used.

## References

* [Stacks Project, Tag 0GPW](https://stacks.math.columbia.edu/tag/0GPW)
* [Stacks Project, Tag 0GQ2](https://stacks.math.columbia.edu/tag/0GQ2)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sites.SqZeroPushout (isSheaf_forgetCommRing eq_of_locally_eq)

universe u

namespace Stacks.Sites.SqZeroPullback

variable {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
  {A B D : Sheaf K CommRingCat.{u}} (p : A ⟶ B) (q : D ⟶ B)

/-! ### The fibre product as a sheaf of commutative rings -/

/-- The subring of `𝒜(U) × 𝒟(U)` of pairs whose two images in `ℬ(U)` agree. -/
def fibreSubring (X : Cᵒᵖ) : Subring (↥(A.obj.obj X) × ↥(D.obj.obj X)) where
  carrier := {z | p.hom.app X z.1 = q.hom.app X z.2}
  mul_mem' := by
    intro z w hz hw
    change p.hom.app X (z.1 * w.1) = q.hom.app X (z.2 * w.2)
    rw [map_mul, map_mul, hz, hw]
  one_mem' := by
    change p.hom.app X 1 = q.hom.app X 1
    rw [map_one, map_one]
  add_mem' := by
    intro z w hz hw
    change p.hom.app X (z.1 + w.1) = q.hom.app X (z.2 + w.2)
    rw [map_add, map_add, hz, hw]
  zero_mem' := by
    change p.hom.app X 0 = q.hom.app X 0
    rw [map_zero, map_zero]
  neg_mem' := by
    intro z hz
    change p.hom.app X (-z.1) = q.hom.app X (-z.2)
    rw [map_neg, map_neg, hz]

/-- A pair of local sections lies in the fibre product exactly when its two images agree. -/
theorem mem_fibreSubring_iff (X : Cᵒᵖ) (z : ↥(A.obj.obj X) × ↥(D.obj.obj X)) :
    z ∈ fibreSubring p q X ↔ p.hom.app X z.1 = q.hom.app X z.2 := Iff.rfl

/-- Restriction along an arrow of the site, on the fibre product: componentwise. -/
def fibreMap {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ↥(fibreSubring p q X) →+* ↥(fibreSubring p q Y) where
  toFun z := ⟨((A.obj.map f).hom (z : ↥(A.obj.obj X) × ↥(D.obj.obj X)).1,
      (D.obj.map f).hom (z : ↥(A.obj.obj X) × ↥(D.obj.obj X)).2), by
    have hz : p.hom.app X (z : ↥(A.obj.obj X) × ↥(D.obj.obj X)).1
        = q.hom.app X (z : ↥(A.obj.obj X) × ↥(D.obj.obj X)).2 := z.2
    change p.hom.app Y ((A.obj.map f).hom _) = q.hom.app Y ((D.obj.map f).hom _)
    rw [NatTrans.naturality_apply p.hom f, NatTrans.naturality_apply q.hom f, hz]⟩
  map_one' := Subtype.ext (Prod.ext (map_one (A.obj.map f).hom) (map_one (D.obj.map f).hom))
  map_mul' z w := Subtype.ext
    (Prod.ext (map_mul (A.obj.map f).hom _ _) (map_mul (D.obj.map f).hom _ _))
  map_zero' := Subtype.ext (Prod.ext (map_zero (A.obj.map f).hom) (map_zero (D.obj.map f).hom))
  map_add' z w := Subtype.ext
    (Prod.ext (map_add (A.obj.map f).hom _ _) (map_add (D.obj.map f).hom _ _))

/-- Restriction on the fibre product, read in the ambient product of sections. -/
@[simp] theorem fibreMap_val {X Y : Cᵒᵖ} (f : X ⟶ Y) (z : ↥(fibreSubring p q X)) :
    ((fibreMap p q f z : ↥(fibreSubring p q Y)) : ↥(A.obj.obj Y) × ↥(D.obj.obj Y)) =
      ((A.obj.map f).hom (z : ↥(A.obj.obj X) × ↥(D.obj.obj X)).1,
        (D.obj.map f).hom (z : ↥(A.obj.obj X) × ↥(D.obj.obj X)).2) := rfl

/-- **The fibre product `𝒜 ×_ℬ 𝒟`, as a presheaf of commutative rings.** -/
def fibrePresheaf : Cᵒᵖ ⥤ CommRingCat.{u} where
  obj X := CommRingCat.of ↥(fibreSubring p q X)
  map f := CommRingCat.ofHom (fibreMap p q f)
  map_id X := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun z => Subtype.ext (Prod.ext ?_ ?_)
    · change (A.obj.map (𝟙 X)).hom _ = _
      rw [A.obj.map_id]; rfl
    · change (D.obj.map (𝟙 X)).hom _ = _
      rw [D.obj.map_id]; rfl
  map_comp {X Y Z} f g := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun z => Subtype.ext (Prod.ext ?_ ?_)
    · change (A.obj.map (f ≫ g)).hom _ = _
      rw [A.obj.map_comp]; rfl
    · change (D.obj.map (f ≫ g)).hom _ = _
      rw [D.obj.map_comp]; rfl


/-! ### Sections of the fibre product -/

/-- The pair of components of a local section of the fibre product. -/
def fibreVal (X : Cᵒᵖ) (z : ↥((fibrePresheaf p q).obj X)) :
    ↥(A.obj.obj X) × ↥(D.obj.obj X) := (z : ↥(fibreSubring p q X)).val

/-- The two components of a local section of the fibre product have the same image in `ℬ`. -/
theorem fibreVal_mem (X : Cᵒᵖ) (z : ↥((fibrePresheaf p q).obj X)) :
    p.hom.app X (fibreVal p q X z).1 = q.hom.app X (fibreVal p q X z).2 :=
  (z : ↥(fibreSubring p q X)).2

/-- Two local sections of the fibre product with the same components are equal. -/
theorem fibreVal_injective (X : Cᵒᵖ) : Function.Injective (fibreVal p q X) :=
  fun _ _ h => by exact Subtype.ext h

/-- Restriction of a local section of the fibre product is componentwise. -/
theorem fibreVal_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (z : ↥((fibrePresheaf p q).obj X)) :
    fibreVal p q Y (((fibrePresheaf p q).map f).hom z) =
      ((A.obj.map f).hom (fibreVal p q X z).1, (D.obj.map f).hom (fibreVal p q X z).2) := rfl

/-- The local section of the fibre product attached to a pair of local sections with equal
images in `ℬ`. -/
def fibreMk (X : Cᵒᵖ) (a : ↥(A.obj.obj X)) (d : ↥(D.obj.obj X))
    (h : p.hom.app X a = q.hom.app X d) : ↥((fibrePresheaf p q).obj X) :=
  (⟨(a, d), h⟩ : ↥(fibreSubring p q X))

/-- The components of the section attached to a pair. -/
@[simp] theorem fibreVal_fibreMk (X : Cᵒᵖ) (a : ↥(A.obj.obj X)) (d : ↥(D.obj.obj X))
    (h : p.hom.app X a = q.hom.app X d) : fibreVal p q X (fibreMk p q X a d h) = (a, d) := rfl

/-- Addition of local sections of the fibre product is componentwise. -/
theorem fibreVal_add (X : Cᵒᵖ) (z w : ↥((fibrePresheaf p q).obj X)) :
    fibreVal p q X (z + w) = fibreVal p q X z + fibreVal p q X w := rfl

/-- Multiplication of local sections of the fibre product is componentwise. -/
theorem fibreVal_mul (X : Cᵒᵖ) (z w : ↥((fibrePresheaf p q).obj X)) :
    fibreVal p q X (z * w) = fibreVal p q X z * fibreVal p q X w := rfl

/-- The zero section of the fibre product. -/
theorem fibreVal_zero (X : Cᵒᵖ) : fibreVal p q X 0 = 0 := rfl

/-- Negation of local sections of the fibre product is componentwise. -/
theorem fibreVal_neg (X : Cᵒᵖ) (z : ↥((fibrePresheaf p q).obj X)) :
    fibreVal p q X (-z) = -fibreVal p q X z := rfl

/-- **The sectionwise fibre product is a sheaf.**  Its two component families amalgamate in `𝒜`
and in `𝒟`; the two images of the amalgamations in `ℬ` agree because they agree locally and `ℬ`
is a sheaf. -/
theorem isSheaf_fibrePresheaf : Presheaf.IsSheaf K (fibrePresheaf p q) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget K _ (forget CommRingCat.{u}),
    isSheaf_iff_isSheaf_of_type]
  intro X S hS x hx
  have amalg (E : Sheaf K CommRingCat.{u})
      (π : ∀ Y, ↥((fibrePresheaf p q).obj Y) → ↥(E.obj.obj Y))
      (hπ : ∀ ⦃Y Z⦄ (g : Y ⟶ Z) z,
        π Z (((fibrePresheaf p q).map g).hom z) = (E.obj.map g).hom (π Y z)) :=
    isSheaf_forgetCommRing E S hS (fun _ f h => π _ (x f h))
      (fun _ _ _ g₁ g₂ f₁ f₂ h₁ h₂ hg =>
        (hπ g₁.op _).symm.trans ((congrArg (π _) (hx g₁ g₂ h₁ h₂ hg)).trans (hπ g₂.op _)))
  obtain ⟨a, ha, ha'⟩ := amalg A (fun Y z => (fibreVal p q Y z).1) fun _ _ _ _ => rfl
  obtain ⟨d, hd, hd'⟩ := amalg D (fun Y z => (fibreVal p q Y z).2) fun _ _ _ _ => rfl
  have hmem : p.hom.app (op X) a = q.hom.app (op X) d := by
    refine eq_of_locally_eq (isSheaf_forgetCommRing B) hS _ _ fun Y f hf => ?_
    have h1 : (A.obj.map f.op).hom a = (fibreVal p q (op Y) (x f hf)).1 := ha f hf
    have h2 : (D.obj.map f.op).hom d = (fibreVal p q (op Y) (x f hf)).2 := hd f hf
    show (B.obj.map f.op).hom (p.hom.app (op X) a) = (B.obj.map f.op).hom (q.hom.app (op X) d)
    rw [← NatTrans.naturality_apply p.hom f.op a, ← NatTrans.naturality_apply q.hom f.op d, h1, h2]
    exact fibreVal_mem p q (op Y) (x f hf)
  refine ⟨fibreMk p q (op X) a d hmem, fun Y f hf => ?_, fun y hy => ?_⟩
  · exact fibreVal_injective p q _ (Prod.ext (ha f hf) (hd f hf))
  · refine fibreVal_injective p q _ (Prod.ext ?_ ?_)
    · exact ha' _ fun _ f hf => congrArg (fun z => (fibreVal p q _ z).1) (hy f hf)
    · exact hd' _ fun _ f hf => congrArg (fun z => (fibreVal p q _ z).2) (hy f hf)

/-- **The fibre product `𝒜 ×_ℬ 𝒟` of sheaves of commutative rings.** -/
def fibreSheaf : Sheaf K CommRingCat.{u} where
  obj := fibrePresheaf p q
  property := isSheaf_fibrePresheaf p q

/-! ### The projections and the universal property -/

/-- The first projection `𝒜 ×_ℬ 𝒟 ⟶ 𝒜`, on the underlying presheaves. -/
def fibreFstHom : fibrePresheaf p q ⟶ A.obj where
  app X := CommRingCat.ofHom
    ((RingHom.fst ↥(A.obj.obj X) ↥(D.obj.obj X)).comp (fibreSubring p q X).subtype)
  naturality _ _ _ := CommRingCat.hom_ext (RingHom.ext fun _ => rfl)

/-- The second projection `𝒜 ×_ℬ 𝒟 ⟶ 𝒟`, on the underlying presheaves. -/
def fibreSndHom : fibrePresheaf p q ⟶ D.obj where
  app X := CommRingCat.ofHom
    ((RingHom.snd ↥(A.obj.obj X) ↥(D.obj.obj X)).comp (fibreSubring p q X).subtype)
  naturality _ _ _ := CommRingCat.hom_ext (RingHom.ext fun _ => rfl)

/-- The first projection `𝒜 ×_ℬ 𝒟 ⟶ 𝒜`. -/
def fibreFst : fibreSheaf p q ⟶ A := ⟨fibreFstHom p q⟩

/-- The second projection `𝒜 ×_ℬ 𝒟 ⟶ 𝒟`. -/
def fibreSnd : fibreSheaf p q ⟶ D := ⟨fibreSndHom p q⟩

/-- The first projection on sections is the first component. -/
@[simp] theorem fibreFst_app (X : Cᵒᵖ) (z : ↥((fibrePresheaf p q).obj X)) :
    (fibreFst p q).hom.app X z = (fibreVal p q X z).1 := rfl

/-- The second projection on sections is the second component. -/
@[simp] theorem fibreSnd_app (X : Cᵒᵖ) (z : ↥((fibrePresheaf p q).obj X)) :
    (fibreSnd p q).hom.app X z = (fibreVal p q X z).2 := rfl

/-- **The fibre square commutes.** -/
theorem fibreFst_comp_eq : fibreFst p q ≫ p = fibreSnd p q ≫ q := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun X => CommRingCat.hom_ext (RingHom.ext fun z => ?_))
  exact fibreVal_mem p q X z

/-- **Two morphisms into the fibre product which agree after both projections are equal.** -/
theorem fibre_hom_ext {T : Sheaf K CommRingCat.{u}} {α β : T ⟶ fibreSheaf p q}
    (h₁ : α ≫ fibreFst p q = β ≫ fibreFst p q)
    (h₂ : α ≫ fibreSnd p q = β ≫ fibreSnd p q) : α = β := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun X => CommRingCat.hom_ext (RingHom.ext fun z => ?_))
  refine fibreVal_injective p q X (Prod.ext ?_ ?_)
  · exact congrArg (fun t : T ⟶ A => t.hom.app X z) h₁
  · exact congrArg (fun t : T ⟶ D => t.hom.app X z) h₂

/-- **The universal property of the fibre product, for a presheaf.**  A presheaf of commutative
rings mapping to `𝒜` and to `𝒟` so that the two composites to `ℬ` agree maps to the fibre
product. -/
def fibrePresheafLift {P : Cᵒᵖ ⥤ CommRingCat.{u}} (u : P ⟶ A.obj) (v : P ⟶ D.obj)
    (h : u ≫ p.hom = v ≫ q.hom) : P ⟶ fibrePresheaf p q where
  app X := CommRingCat.ofHom
    (((u.app X).hom.prod (v.app X).hom).codRestrict (fibreSubring p q X) fun z =>
      congrArg (fun α : P ⟶ B.obj => α.app X z) h)
  naturality X Y f := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun z => Subtype.ext (Prod.ext ?_ ?_)
    · exact NatTrans.naturality_apply u f z
    · exact NatTrans.naturality_apply v f z

/-- The lift out of a presheaf, on sections. -/
@[simp] theorem fibreVal_fibrePresheafLift {P : Cᵒᵖ ⥤ CommRingCat.{u}} (u : P ⟶ A.obj)
    (v : P ⟶ D.obj) (h : u ≫ p.hom = v ≫ q.hom) (X : Cᵒᵖ) (z : ↥(P.obj X)) :
    fibreVal p q X ((fibrePresheafLift p q u v h).app X z) = (u.app X z, v.app X z) := rfl

/-- The lift out of a presheaf followed by the first projection is the given map to `𝒜`. -/
theorem fibrePresheafLift_comp_fst {P : Cᵒᵖ ⥤ CommRingCat.{u}} (u : P ⟶ A.obj)
    (v : P ⟶ D.obj) (h : u ≫ p.hom = v ≫ q.hom) :
    fibrePresheafLift p q u v h ≫ fibreFstHom p q = u :=
  NatTrans.ext (funext fun _ => CommRingCat.hom_ext (RingHom.ext fun _ => rfl))

/-- The lift out of a presheaf followed by the second projection is the given map to `𝒟`. -/
theorem fibrePresheafLift_comp_snd {P : Cᵒᵖ ⥤ CommRingCat.{u}} (u : P ⟶ A.obj)
    (v : P ⟶ D.obj) (h : u ≫ p.hom = v ≫ q.hom) :
    fibrePresheafLift p q u v h ≫ fibreSndHom p q = v :=
  NatTrans.ext (funext fun _ => CommRingCat.hom_ext (RingHom.ext fun _ => rfl))

/-- **The universal property of the fibre product, for a sheaf.** -/
def fibreLift {T : Sheaf K CommRingCat.{u}} (u : T ⟶ A) (v : T ⟶ D)
    (h : u ≫ p = v ≫ q) : T ⟶ fibreSheaf p q :=
  ⟨fibrePresheafLift p q u.hom v.hom (congrArg (fun t : T ⟶ B => t.hom) h)⟩

/-- The lift out of a sheaf, on sections. -/
@[simp] theorem fibreVal_fibreLift {T : Sheaf K CommRingCat.{u}} (u : T ⟶ A) (v : T ⟶ D)
    (h : u ≫ p = v ≫ q) (X : Cᵒᵖ) (z : ↥(T.obj.obj X)) :
    fibreVal p q X ((fibreLift p q u v h).hom.app X z) = (u.hom.app X z, v.hom.app X z) := rfl

/-- The lift out of a sheaf followed by the first projection is the given map to `𝒜`. -/
theorem fibreLift_comp_fst {T : Sheaf K CommRingCat.{u}} (u : T ⟶ A) (v : T ⟶ D)
    (h : u ≫ p = v ≫ q) : fibreLift p q u v h ≫ fibreFst p q = u :=
  Sheaf.hom_ext (fibrePresheafLift_comp_fst p q u.hom v.hom
    (congrArg (fun t : T ⟶ B => t.hom) h))

/-- The lift out of a sheaf followed by the second projection is the given map to `𝒟`. -/
theorem fibreLift_comp_snd {T : Sheaf K CommRingCat.{u}} (u : T ⟶ A) (v : T ⟶ D)
    (h : u ≫ p = v ≫ q) : fibreLift p q u v h ≫ fibreSnd p q = v :=
  Sheaf.hom_ext (fibrePresheafLift_comp_snd p q u.hom v.hom
    (congrArg (fun t : T ⟶ B => t.hom) h))

/-! ### The square-zero pullback -/

/-- **The kernel of the second projection, on sections.**  A local section of the fibre product
dies in `𝒟` exactly when its second component vanishes, in which case its first component lies
in `Ker p`. -/
theorem fibreSnd_app_eq_zero_iff (X : Cᵒᵖ) (z : ↥((fibrePresheaf p q).obj X)) :
    (fibreSnd p q).hom.app X z = 0 ↔
      p.hom.app X (fibreVal p q X z).1 = 0 ∧ (fibreVal p q X z).2 = 0 := by
  refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
  rw [fibreVal_mem p q X z]
  show q.hom.app X ((fibreSnd p q).hom.app X z) = 0
  rw [h, map_zero]

/-- **Right exactness.**  The second projection of the fibre product is locally surjective
whenever `p` is: a local section `d` of `𝒟` whose image `q d` lifts to `a` in `𝒜` is the image
of the section `(a, d)`. -/
instance isLocallySurjective_fibreSnd [Presheaf.IsLocallySurjective K p.hom] :
    Presheaf.IsLocallySurjective K (fibreSnd p q).hom where
  imageSieve_mem {X} d := by
    refine K.superset_covering (fun Y f hf => ?_)
      (Presheaf.imageSieve_mem K p.hom (q.hom.app (op X) d))
    obtain ⟨a, ha⟩ := hf
    refine ⟨fibreMk p q (op Y) a ((D.obj.map f.op).hom d) ?_, rfl⟩
    exact ha.trans (NatTrans.naturality_apply q.hom f.op d).symm

/-- The data realizing `Ker p` as a presheaf of abelian groups `𝒢`: a natural family of
injective additive maps `𝒢(U) ⟶ 𝒜(U)` whose range is exactly the kernel of `p` on sections.
For a square-zero extension `0 ⟶ 𝒢 ⟶ 𝒜 ⟶ ℬ ⟶ 0` of sheaves of rings this is the inclusion of
its ideal. -/
structure FibreInrData (G : Cᵒᵖ ⥤ AddCommGrpCat.{u}) where
  /-- The inclusion `𝒢(U) ⟶ 𝒜(U)` on sections. -/
  app (X : Cᵒᵖ) : ↥(G.obj X) →+ ↥(A.obj.obj X)
  /-- The inclusions commute with the restriction maps. -/
  app_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ↥(G.obj X)) :
    app Y ((G.map f) n) = (A.obj.map f).hom (app X n)
  /-- The inclusions are injective. -/
  app_injective (X : Cᵒᵖ) : Function.Injective (app X)
  /-- The range of the inclusion is exactly the kernel of `p`. -/
  range (X : Cᵒᵖ) (a : ↥(A.obj.obj X)) : p.hom.app X a = 0 ↔ ∃ n : ↥(G.obj X), app X n = a

variable {G : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (ι : FibreInrData p G)

/-- **The inclusion of `𝒢` into the fibre product**, `n ↦ (ι n, 0)`. -/
def fibreInr (X : Cᵒᵖ) (n : ↥(G.obj X)) : ↥((fibrePresheaf p q).obj X) :=
  fibreMk p q X (ι.app X n) 0 (by rw [(ι.range X _).2 ⟨n, rfl⟩, map_zero])

/-- The components of the inclusion of `𝒢`. -/
@[simp] theorem fibreVal_fibreInr (X : Cᵒᵖ) (n : ↥(G.obj X)) :
    fibreVal p q X (fibreInr p q ι X n) = (ι.app X n, 0) := rfl

/-- The inclusion of `𝒢` into the fibre product is killed by the second projection. -/
@[simp] theorem fibreSnd_fibreInr (X : Cᵒᵖ) (n : ↥(G.obj X)) :
    (fibreSnd p q).hom.app X (fibreInr p q ι X n) = 0 := rfl

/-- The inclusion of `𝒢` into the fibre product is additive. -/
theorem fibreInr_add (X : Cᵒᵖ) (n m : ↥(G.obj X)) :
    fibreInr p q ι X (n + m) = fibreInr p q ι X n + fibreInr p q ι X m :=
  fibreVal_injective p q X (Prod.ext (map_add (ι.app X) n m)
    (add_zero (0 : ↥(D.obj.obj X))).symm)

/-- The inclusion of `𝒢` into the fibre product sends `0` to `0`. -/
theorem fibreInr_zero (X : Cᵒᵖ) : fibreInr p q ι X 0 = 0 :=
  fibreVal_injective p q X (Prod.ext (map_zero (ι.app X)) rfl)

/-- The inclusion of `𝒢` into the fibre product, as a homomorphism of the additive groups of
local sections. -/
def fibreInrHom (X : Cᵒᵖ) : ↥(G.obj X) →+ ↥((fibrePresheaf p q).obj X) where
  toFun := fibreInr p q ι X
  map_zero' := fibreInr_zero p q ι X
  map_add' := fibreInr_add p q ι X

/-- The inclusion of `𝒢` into the fibre product commutes with the restriction maps. -/
theorem fibreInr_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ↥(G.obj X)) :
    ((fibrePresheaf p q).map f).hom (fibreInr p q ι X n) = fibreInr p q ι Y ((G.map f) n) :=
  fibreVal_injective p q Y (Prod.ext (ι.app_map f n).symm (map_zero (D.obj.map f).hom))

/-- **Left exactness.**  The inclusion of `𝒢` into the fibre product is injective on
sections. -/
theorem fibreInr_injective (X : Cᵒᵖ) : Function.Injective (fibreInr p q ι X) :=
  fun _ _ h => ι.app_injective X (congrArg (fun z => (fibreVal p q X z).1) h)

/-- **Exactness in the middle, with the kernel computed exactly on sections.**  A local section
of the fibre product dies in `𝒟` if and only if it is `(ι n, 0)` for a local section `n` of
`𝒢`. -/
theorem fibreSnd_app_eq_zero_iff_exists_fibreInr (X : Cᵒᵖ)
    (z : ↥((fibrePresheaf p q).obj X)) :
    (fibreSnd p q).hom.app X z = 0 ↔ ∃ n : ↥(G.obj X), fibreInr p q ι X n = z := by
  refine ⟨fun h => ?_, fun ⟨n, hn⟩ => hn ▸ fibreSnd_fibreInr p q ι X n⟩
  obtain ⟨hker, hsnd⟩ := (fibreSnd_app_eq_zero_iff p q X z).1 h
  obtain ⟨n, hn⟩ := (ι.range X _).1 hker
  exact ⟨n, fibreVal_injective p q X (Prod.ext hn hsnd.symm)⟩

/-- **The ideal `𝒢` of the fibre product has square zero** as soon as its square vanishes in
`𝒜`, which for a square-zero extension `0 ⟶ 𝒢 ⟶ 𝒜 ⟶ ℬ ⟶ 0` it does. -/
theorem fibreInr_mul_fibreInr (X : Cᵒᵖ) (n m : ↥(G.obj X))
    (hsq : ι.app X n * ι.app X m = 0) :
    fibreInr p q ι X n * fibreInr p q ι X m = 0 :=
  fibreVal_injective p q X (Prod.ext hsq (mul_zero (0 : ↥(D.obj.obj X))))

/-- **The ideal `𝒢` of the fibre product is acted on through `𝒟`.**  Multiplying `(ι n, 0)` by
a local section `z` gives `(z₁ · ι n, 0)`; the second component is `0` because `z₂ · 0 = 0`, so
the action is that of `𝒜` on `Ker p`, which factors through `ℬ` and hence through `𝒟`. -/
theorem fibreMk_mul_fibreInr (X : Cᵒᵖ) (z : ↥((fibrePresheaf p q).obj X)) (n m : ↥(G.obj X))
    (hact : (fibreVal p q X z).1 * ι.app X n = ι.app X m) :
    z * fibreInr p q ι X n = fibreInr p q ι X m :=
  fibreVal_injective p q X (Prod.ext hact (mul_zero (fibreVal p q X z).2))

end Stacks.Sites.SqZeroPullback

end
