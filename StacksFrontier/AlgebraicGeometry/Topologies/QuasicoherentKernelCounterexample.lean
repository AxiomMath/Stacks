module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.QuasicoherentChaotic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Data.ZMod.Basic

/-!
# Quasi-coherent modules on a site are not closed under kernels

On a site, the kernel of a morphism of quasi-coherent sheaves of modules need not be
quasi-coherent.  This file proves that, by a counterexample on a two-object site with the
chaotic topology.

The reason is base change.  Tag 0GZN says that on the chaotic topology a module is
quasi-coherent exactly when every restriction map is a base change, `𝒪(U) ⊗_{𝒪(V)} F(V) = F(U)`
for `f : U ⟶ V`.  Tensoring is right exact but not left exact, so this condition survives
cokernels and fails for kernels.  The witness is multiplication by `2` on the structure sheaf of
the site with `𝒪(V) = ℤ` and `𝒪(U) = ℤ/2`: its kernel is `0` over `V` and all of `ℤ/2` over `U`,
and `ℤ/2 ⊗_ℤ 0 = 0` is not `ℤ/2`.  This is the counterexample of Stacks 06VE (6), where the
association functor `G ↦ Gᵃ` is recorded as exact into the *small étale* site but not into the
big one.

This bounds the site-level closure properties that Tag 03M1 and Tag 0GNB can ask for: the
cokernel clauses are not in conflict with anything here, and the coherent analogue is true and
already in the tree — `Stacks.SheafOfModules.isCoherentOnSite_kernel`, Tag 01BY (3) on an
arbitrary site — but no *unconditional* site-level quasi-coherent kernel statement can be
proved.

The qualifier matters, and the counterexample itself says why: its mechanism is the non-flat
map `ℤ → ℤ/2`. Add flatness of the restriction maps and the kernel statement becomes
provable — `AlgebraicGeometry.Space.isCartesianOnAffineCharts_kernel`
(`StacksFrontier/AlgebraicGeometry/Spaces/ChartSectionsKernel.lean`) does exactly that, and on
the small étale site of an algebraic space the flatness is automatic, since étale morphisms
are flat. So what is refuted here is the clause at this generality, not the clause.

## Main results

* `ChaoticQCoh.quasiCoherent_unit`: on any site with the chaotic topology, the structure sheaf
  is a quasi-coherent module over itself.
* `ChaoticQCoh.KernelCounterexample.not_quasiCoherent_kernel_two`: the kernel of multiplication
  by `2` on the structure sheaf of the two-object site below is not quasi-coherent.
* `ChaoticQCoh.KernelCounterexample.not_quasicoherent_closed_under_kernels`: consequently the
  quasi-coherent modules on that site are not closed under kernels.

## Main definitions

* `ChaoticQCoh.KernelCounterexample.Obj` and `ChaoticQCoh.KernelCounterexample.Hom` are the
  two-object category `U ⟶ V`, and `ChaoticQCoh.KernelCounterexample.ringPresheafZMod` is the
  presheaf of rings `V ↦ ℤ`, `U ↦ ℤ/2` on it, with reduction as its restriction map.
* `ChaoticQCoh.KernelCounterexample.two` is multiplication by `2` on the structure sheaf.

## Implementation notes

The quasi-coherence of the structure sheaf is proved by identifying the canonical map of
Tag 0GZN with the comparison morphism `η` of the monoidal functor
`CategoryTheory.ModuleCat.extendScalars`, which is an isomorphism because that functor is
monoidal (`CategoryTheory.Functor.Monoidal.εIso`).  The identification is made after applying
the extension/restriction adjunction, where both sides become the ring restriction map: this is
`CategoryTheory.ModuleCat.restrictScalars_η` on one side and
`CategoryTheory.PresheafOfModules.unit_map_one` on the other.  Doing it that way avoids
constructing any element of `𝒪(U) ⊗_{𝒪(V)} 𝒪(V)` by hand.

That matters, because the tensor products appearing in Tag 0GZN's `canonicalMap` carry their
module structures inside `CategoryTheory.ModuleCat.restrictScalars`, so a tensor written by hand
needs instances that are only definitionally the ambient ones.  Tag 0GZN's own file is elaborated
with `backward.isDefEq.respectTransparency` turned off and does not notice; downstream files
cannot do that.  Every step here that touches a tensor is therefore either a term-mode
application, where definitional unfolding is allowed, or a goal produced by
`TensorProduct.induction_on`, where the instances come from the goal.  `rw` on such a goal fails
with "the target expression is not type-correct under the `implicit` transparency level".

The evaluation of the kernel at an object of the site is obtained from
`CategoryTheory.Limits.PreservesKernel.iso` for
`CategoryTheory.PresheafOfModules.evaluation`, which preserves finite limits.  Over `V` the
kernel is identified with the kernel of an injective map and over `U` with the kernel of the zero
map, since `x + x = 0` in `ℤ/2`.

## References

* [Stacks Project, Tag 0GZN](https://stacks.math.columbia.edu/tag/0GZN)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct Functor.OplaxMonoidal

universe u

namespace ChaoticQCoh

variable {C : Type u} [Category.{0} C] (O : Cᵒᵖ ⥤ CommRingCat.{u})

/-! ### The structure sheaf is quasi-coherent -/

/-- The canonical map of Tag 0GZN for the structure sheaf is the comparison morphism `η` of the
monoidal functor `extendScalars`.  Both become the ring restriction map after applying the
extension/restriction of scalars adjunction, and a morphism out of an extension of scalars is
determined by its adjoint transpose. -/
public theorem unit_canonicalMap_eq_eta {U V : C} (f : U ⟶ V) :
    canonicalMap O (PresheafOfModules.unit (ringPresheaf O)) f =
      η (ModuleCat.extendScalars (ringRestriction O f)) := by
  refine ((ModuleCat.extendRestrictScalarsAdj (ringRestriction O f)).homEquiv _ _).injective ?_
  have h1 : (ModuleCat.extendRestrictScalarsAdj (ringRestriction O f)).homEquiv _ _
      (canonicalMap O (PresheafOfModules.unit (ringPresheaf O)) f) =
      (PresheafOfModules.unit (ringPresheaf O)).map f.op :=
    ((ModuleCat.extendRestrictScalarsAdj (ringRestriction O f)).homEquiv _ _).apply_symm_apply _
  rw [h1]
  ext
  exact (PresheafOfModules.unit_map_one (ringPresheaf O) f.op).trans
    (((ModuleCat.restrictScalars_η (ringRestriction O f) 1).trans
      (map_one (ringRestriction O f))).symm)

/-- **The structure sheaf of a chaotic site is quasi-coherent.**  Every canonical map of
Tag 0GZN for it is the comparison morphism of a monoidal functor, hence an isomorphism. -/
public theorem quasiCoherent_unit : QuasiCoherent O (PresheafOfModules.unit (ringPresheaf O)) :=
  (quasiCoherent_iff_canonicalMap_isIso O _).mpr fun {_ _} f => by
    rw [unit_canonicalMap_eq_eta]
    exact (Functor.Monoidal.εIso (ModuleCat.extendScalars (ringRestriction O f))).isIso_inv

/-! ### Base change of a zero module -/

/-- An extension of scalars of a module with one element has one element: every element of the
tensor product is a sum of simple tensors, each of which has a zero factor. -/
public theorem subsingleton_extendScalars {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S)
    (M : ModuleCat.{u} R) [Subsingleton M] :
    Subsingleton ((ModuleCat.extendScalars g).obj M : Type u) := by
  have h : ∀ z : ((ModuleCat.extendScalars g).obj M : Type u), z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul a m =>
        rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
        rfl
    | add p q hp hq =>
        rw [hp, hq]
        exact add_zero 0
  exact ⟨fun x y => (h x).trans (h y).symm⟩

/-! ### Transport of smallness along an isomorphism of modules -/

/-- A module isomorphic to one with a single element has a single element. -/
public theorem subsingleton_of_iso {R : Type u} [Ring R] {A B : ModuleCat.{u} R} (e : A ≅ B)
    [Subsingleton B] : Subsingleton (A : Type u) :=
  e.toLinearEquiv.toEquiv.subsingleton

/-- A module isomorphic to one with two distinct elements has two distinct elements. -/
public theorem nontrivial_of_iso {R : Type u} [Ring R] {A B : ModuleCat.{u} R} (e : A ≅ B)
    [Nontrivial B] : Nontrivial (A : Type u) :=
  e.toLinearEquiv.toEquiv.nontrivial

/-- The kernel of an injective morphism of modules has a single element. -/
public theorem subsingleton_kernel_of_injective {R : Type u} [Ring R] {A B : ModuleCat.{u} R}
    (g : A ⟶ B) (hg : Function.Injective g.hom) :
    Subsingleton ((kernel g : ModuleCat.{u} R) : Type u) :=
  have : Subsingleton (LinearMap.ker g.hom) :=
    ⟨fun a b => Subtype.ext
      (hg ((LinearMap.mem_ker.mp a.2).trans (LinearMap.mem_ker.mp b.2).symm))⟩
  subsingleton_of_iso (ModuleCat.kernelIsoKer g)

end ChaoticQCoh

namespace ChaoticQCoh.KernelCounterexample

/-! ### The two-object site -/

/-- The two objects of the site: `base`, which carries `ℤ`, and `cover`, which carries `ℤ/2`. -/
public inductive Obj where
  /-- The object carrying `ℤ`. -/
  | base : Obj
  /-- The object carrying `ℤ/2`. -/
  | cover : Obj

/-- The morphisms of the site: the identities and one morphism `cover ⟶ base`. -/
public inductive Hom : Obj → Obj → Type
  /-- The identity of an object. -/
  | id (X : Obj) : Hom X X
  /-- The one non-identity morphism. -/
  | down : Hom Obj.cover Obj.base

/-- Composition of morphisms of the site. -/
public def Hom.comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  | _, _, _, .id _, g => g
  | _, _, _, .down, .id _ => .down

/-- The two-object category. -/
public instance category : Category Obj where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := rfl
  comp_id f := by cases f <;> rfl
  assoc f g h := by cases f <;> cases g <;> cases h <;> rfl

/-- The ring attached to each object: `ℤ` over `base` and `ℤ/2` over `cover`. -/
public def ringObj : Obj → CommRingCat.{0}
  | .base => CommRingCat.of ℤ
  | .cover => CommRingCat.of (ZMod 2)

/-- The restriction map attached to each morphism: the identity on an identity, and reduction
modulo `2` on the one non-identity morphism. -/
public noncomputable def ringMap : {X Y : Obj} → Hom X Y → (ringObj Y ⟶ ringObj X)
  | _, _, .id _ => 𝟙 _
  | _, _, .down => CommRingCat.ofHom (Int.castRingHom (ZMod 2))

/-- `ringMap` is contravariantly functorial. -/
public theorem ringMap_comp {X Y Z : Obj} (f : Hom X Y) (g : Hom Y Z) :
    ringMap (f.comp g) = ringMap g ≫ ringMap f := by
  cases f <;> cases g <;> exact (Category.comp_id _).symm

/-- The presheaf of rings `base ↦ ℤ`, `cover ↦ ℤ/2` with reduction modulo `2` as its
restriction map. -/
public noncomputable def ringPresheafZMod : Objᵒᵖ ⥤ CommRingCat.{0} where
  obj X := ringObj X.unop
  map f := ringMap f.unop
  map_id _ := rfl
  map_comp f g := ringMap_comp g.unop f.unop

/-! ### Multiplication by two on the structure sheaf -/

/-- Multiplication by `2` on the structure sheaf of the site, as the sum of two copies of the
identity. -/
public noncomputable def two :
    PresheafOfModules.unit (ringPresheaf ringPresheafZMod) ⟶
      PresheafOfModules.unit (ringPresheaf ringPresheafZMod) :=
  𝟙 _ + 𝟙 _

/-- On sections, `two` doubles. -/
public theorem two_app_apply (X : Objᵒᵖ)
    (x : (PresheafOfModules.unit (ringPresheaf ringPresheafZMod)).obj X) :
    (two.app X) x = x + x := rfl

/-- Over `base` the ring is `ℤ`, on which doubling is injective. -/
public theorem two_app_base_injective :
    Function.Injective ((two.app (op Obj.base)).hom) := by
  have key : ∀ x y : ℤ, x + x = y + y → x = y := fun _ _ h => by omega
  intro x y h
  exact key x y h

/-- Over `cover` the ring is `ℤ/2`, on which doubling is zero. -/
public theorem two_app_cover_eq_zero : two.app (op Obj.cover) = 0 := by
  ext
  show (1 : ZMod 2) + 1 = 0
  decide

/-! ### The kernel of multiplication by two -/

/-- The kernel of `two` evaluated at `X` is the kernel of `two` on sections over `X`. -/
private noncomputable def kernelTwoObjIso (X : Objᵒᵖ) :
    (kernel two).obj X ≅ kernel (two.app X) :=
  PreservesKernel.iso (PresheafOfModules.evaluation (ringPresheaf ringPresheafZMod) X) two

/-- Over `base` the kernel of `two` has a single element: it is the kernel of doubling on
`ℤ`. -/
public theorem subsingleton_kernel_two_base :
    Subsingleton ((kernel two).obj (op Obj.base)) :=
  have := ChaoticQCoh.subsingleton_kernel_of_injective _ two_app_base_injective
  ChaoticQCoh.subsingleton_of_iso (kernelTwoObjIso _)

/-- Over `cover` the kernel of `two` has two distinct elements: `two` vanishes there, so the
kernel is all of `ℤ/2`. -/
public noncomputable def kernelTwoCoverIso :
    kernel (two.app (op Obj.cover)) ≅
      (PresheafOfModules.unit (ringPresheaf ringPresheafZMod)).obj (op Obj.cover) := by
  rw [two_app_cover_eq_zero]
  exact kernelZeroIsoSource

/-- Over `cover` the kernel of `two` has two distinct elements: `two` vanishes there, so the
kernel is all of `ℤ/2`. -/
public theorem nontrivial_kernel_two_cover :
    Nontrivial ((kernel two).obj (op Obj.cover)) :=
  have : Nontrivial ((kernel (two.app (op Obj.cover)) : ModuleCat.{0} _) : Type) :=
    have : Nontrivial
        (((PresheafOfModules.unit (ringPresheaf ringPresheafZMod)).obj (op Obj.cover) : Type)) :=
      inferInstanceAs (Nontrivial (ZMod 2))
    ChaoticQCoh.nontrivial_of_iso kernelTwoCoverIso
  ChaoticQCoh.nontrivial_of_iso (kernelTwoObjIso _)

/-- **The kernel of a morphism of quasi-coherent modules on a site need not be
quasi-coherent.**  If it were, the canonical map of Tag 0GZN along `down : cover ⟶ base` would
be an isomorphism; its source is a base change of a module with one element and so has one
element, while its target has two. -/
public theorem not_quasiCoherent_kernel_two :
    ¬ QuasiCoherent ringPresheafZMod (kernel two) := by
  intro hqc
  have hiso : IsIso (canonicalMap ringPresheafZMod (kernel two)
      (Hom.down : Obj.cover ⟶ Obj.base)) :=
    canonicalMap_isIso_of_quasiCoherent ringPresheafZMod (kernel two) hqc
      (Hom.down : Obj.cover ⟶ Obj.base)
  have hsrc : Subsingleton
      ((ModuleCat.extendScalars
        (ringRestriction ringPresheafZMod (Hom.down : Obj.cover ⟶ Obj.base))).obj
          ((kernel two).obj (op Obj.base)) : Type) :=
    have := subsingleton_kernel_two_base
    ChaoticQCoh.subsingleton_extendScalars _ _
  have hsurj := (ConcreteCategory.bijective_of_isIso
    (canonicalMap ringPresheafZMod (kernel two)
      (Hom.down : Obj.cover ⟶ Obj.base))).2
  obtain ⟨a, b, hab⟩ := nontrivial_kernel_two_cover
  obtain ⟨a', ha⟩ := hsurj a
  obtain ⟨b', hb⟩ := hsurj b
  exact hab (ha.symm.trans (by rw [Subsingleton.elim a' b', hb]))

/-- **Quasi-coherent modules on a site are not closed under kernels.**  The site is the
two-object site with the chaotic topology, the morphism is multiplication by `2` on its
structure sheaf, and the structure sheaf is quasi-coherent by
`ChaoticQCoh.quasiCoherent_unit`. -/
public theorem not_quasicoherent_closed_under_kernels :
    ¬ ∀ (F G : PresheafOfModules.{0} (ringPresheaf ringPresheafZMod)) (φ : F ⟶ G),
        QuasiCoherent ringPresheafZMod F → QuasiCoherent ringPresheafZMod G →
          QuasiCoherent ringPresheafZMod (kernel φ) := by
  intro h
  exact not_quasiCoherent_kernel_two
    (h _ _ two (quasiCoherent_unit ringPresheafZMod) (quasiCoherent_unit ringPresheafZMod))

end ChaoticQCoh.KernelCounterexample

end
