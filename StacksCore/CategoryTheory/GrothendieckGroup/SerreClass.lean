module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
import StacksCore.CategoryTheory.Abelian.SerreClass.Localization
import StacksCore.CategoryTheory.GrothendieckGroup.Abelian
public import StacksCore.CategoryTheory.GrothendieckGroup.Basic

/-! # The Grothendieck group of a Serre quotient: Stacks 02MX (1)

Stacks 02MX (1): let `𝒜` be an abelian category, `𝒞 ⊂ 𝒜` a Serre subcategory and `ℬ = 𝒜/𝒞`.
The exact functors `𝒞 → 𝒜` and `𝒜 → ℬ` induce an exact sequence `K₀(𝒞) → K₀(𝒜) → K₀(ℬ) → 0`.

In Lean, `𝒜` is an abelian category `A` and `𝒞` is a Serre class `P : ObjectProperty A`, with
inclusion `P.ι : P.FullSubcategory ⥤ A`. As in Mathlib's `ObjectProperty.SerreClassLocalization`,
`ℬ` is any category `D` with a localization functor `L : A ⥤ D` for `P.isoModSerre`, a
preadditive structure and `[L.Additive]`; the abelian structure of `D` (Stacks 02MS) is not an
assumption. The two maps of K-groups are `GrothendieckGroup.map P.ι hι` and
`GrothendieckGroup.map L hL`, where `hι` and `hL` say that `P.ι` and `L` send short exact
sequences to short exact sequences. The maps do not depend on these proofs; the canonical ones
are `P.shortExact_map_ι` (in `StacksCore.CategoryTheory.Abelian.Subcategory`) and
`SerreClassLocalization.shortExact_map L P` (in
`StacksCore.CategoryTheory.Abelian.SerreClass.Localization`). This file re-exports neither module.

## Main results

* `SerreClassLocalization.grothendieckGroupEquiv`: the map `K₀(A) → K₀(D)` induced by `L`
  identifies `K₀(D)` with the quotient of `K₀(A)` by the image of `K₀(P.FullSubcategory)`.
* `SerreClassLocalization.exact_grothendieckGroup_map`: the exactness at `K₀(A)`.
* `SerreClassLocalization.grothendieckGroup_map_surjective`: the surjectivity of
  `K₀(A) → K₀(D)`, which is `GrothendieckGroup.map_surjective` for the essentially surjective
  functor `L`.
* `SerreClassLocalization.existsUnique_comp_map_eq`: an additive map from `K₀(A)` to an additive
  monoid that vanishes on the image of `K₀(P.FullSubcategory)` factors uniquely through `K₀(D)`.

## Implementation notes

Exactness is read off an explicit inverse of the map `K₀(A) ⧸ im K₀(P.FullSubcategory) → K₀(D)`
induced by `L`: it sends the class of an object `Y` of `D` to the class of any object `X` of `A`
with `L X ≅ Y`. That this is well defined uses exactly the two ingredients of the Stacks proof.

* Every short exact sequence of `D` is isomorphic to the image under `L` of a short exact
  sequence of `A` (`SerreClassLocalization.exists_shortExact_map_iso`, from the proofs of Stacks
  02MS and 05QG), so the relations of `K₀(D)` hold for the proposed values.
* Two objects `M` and `N` of `A` with `L M ≅ L N` are joined by a roof `M ← M' → N` in `A` whose
  two arrows have kernel and cokernel in `P` (a right fraction for the calculus of fractions of
  `P.isoModSerre`), so `[M] - [N]` lies in the image of `K₀(P.FullSubcategory)`
  (`SerreClassLocalization.of_sub_of_mem_range_map_ι_of_iso`).

Stacks matches the objects on the two sides of an equation in a free abelian group through a
bijection `τ`; working with the inverse map makes this multiset bookkeeping unnecessary.
-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Limits

namespace GrothendieckGroup

/-- The class of an object `X` satisfying `P` lies in the image of the map
`K₀(P.FullSubcategory) → K₀(A)` induced by the inclusion `P.ι`: it is the image of the class of
`X` as an object of `P.FullSubcategory`. -/
lemma of_mem_range_map_ι {A : Type u} [Category.{v} A] [HasZeroMorphisms A]
    (P : ObjectProperty A)
    (hι : ∀ ⦃S : ShortComplex P.FullSubcategory⦄, S.ShortExact → (S.map P.ι).ShortExact)
    {X : A} (hX : P X) : of X ∈ (map P.ι hι).range :=
  AddMonoidHom.mem_range.2 ⟨of ⟨X, hX⟩, by rw [map_of, ObjectProperty.ι_obj]⟩

/-- If the kernel and the cokernel of `f : X ⟶ Y` satisfy `P`, then `[X] - [Y]` lies in the
image of the map `K₀(P.FullSubcategory) → K₀(A)`, since `[X] - [Y] = [Ker f] - [Coker f]`. -/
lemma of_sub_of_mem_range_map_ι {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A)
    (hι : ∀ ⦃S : ShortComplex P.FullSubcategory⦄, S.ShortExact → (S.map P.ι).ShortExact)
    {X Y : A} (f : X ⟶ Y) (hk : P (kernel f)) (hc : P (cokernel f)) :
    of X - of Y ∈ (map P.ι hι).range := by
  rw [of_sub_of_eq_of_kernel_sub_of_cokernel f]
  exact sub_mem (of_mem_range_map_ι P hι hk) (of_mem_range_map_ι P hι hc)

/-- If `f : X ⟶ Y` is an isomorphism modulo a Serre class `P`, that is, its kernel and its
cokernel satisfy `P`, then `[X] - [Y]` lies in the image of the map
`K₀(P.FullSubcategory) → K₀(A)`. -/
lemma of_sub_of_mem_range_map_ι_of_isoModSerre {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.IsSerreClass]
    (hι : ∀ ⦃S : ShortComplex P.FullSubcategory⦄, S.ShortExact → (S.map P.ι).ShortExact)
    {X Y : A} (f : X ⟶ Y) (hf : P.isoModSerre f) : of X - of Y ∈ (map P.ι hι).range := by
  obtain ⟨h₁, h₂⟩ := (P.isoModSerre_iff f).1 hf
  exact of_sub_of_mem_range_map_ι P hι f ((P.monoModSerre_iff f).1 h₁)
    ((P.epiModSerre_iff f).1 h₂)

end GrothendieckGroup

namespace ObjectProperty.SerreClassLocalization

open GrothendieckGroup

variable {A : Type u} [Category.{v} A] [Abelian A] {D : Type u'} [Category.{v'} D]
  (L : A ⥤ D) (P : ObjectProperty A) [P.IsSerreClass]
  [L.IsLocalization P.isoModSerre] [Preadditive D] [L.Additive]
  (hι : ∀ ⦃S : ShortComplex P.FullSubcategory⦄, S.ShortExact → (S.map P.ι).ShortExact)
  (hL : ∀ ⦃S : ShortComplex A⦄, S.ShortExact → (S.map L).ShortExact)

/-- Two objects `X` and `Y` of `A` whose images under `L` are isomorphic have classes that differ
by an element of the image of `K₀(P.FullSubcategory) → K₀(A)`. This is the roof `M ← M' → τ(M)`
of the proof of Stacks 02MX (1): the isomorphism `L X ≅ L Y` is a right fraction `X ← X' → Y`
whose two arrows are isomorphisms modulo `P`, and `[X] - [Y] = ([X'] - [Y]) - ([X'] - [X])`. -/
lemma of_sub_of_mem_range_map_ι_of_iso {X Y : A} (e : L.obj X ≅ L.obj Y) :
    of X - of Y ∈ (GrothendieckGroup.map P.ι hι).range := by
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L P.isoModSerre e.hom
  have : IsIso (L.map φ.f) := by
    rw [← φ.map_s_comp_map L (Localization.inverts L P.isoModSerre), ← hφ]
    infer_instance
  have h := sub_mem
    (of_sub_of_mem_range_map_ι_of_isoModSerre P hι φ.f ((isIso_map_iff L P φ.f).1 this))
    (of_sub_of_mem_range_map_ι_of_isoModSerre P hι φ.s φ.hs)
  rwa [sub_sub_sub_cancel_left] at h

/-- Two objects of `A` whose images under `L` are isomorphic to the same object of `D` have the
same class in the quotient of `K₀(A)` by the image of `K₀(P.FullSubcategory)`. -/
lemma mk_of_eq_mk_of_of_iso {Y : D} {X X' : A} (e : Y ≅ L.obj X) (e' : Y ≅ L.obj X') :
    (QuotientAddGroup.mk (of X) : GrothendieckGroup A ⧸ (GrothendieckGroup.map P.ι hι).range) =
      QuotientAddGroup.mk (of X') :=
  QuotientAddGroup.eq_iff_sub_mem.2 (of_sub_of_mem_range_map_ι_of_iso L P hι (e.symm ≪≫ e'))

/-- The composite `K₀(P.FullSubcategory) → K₀(A) → K₀(D)` is zero: `L` sends every object
satisfying `P` to a zero object. -/
theorem map_comp_map_ι :
    (GrothendieckGroup.map L hL).comp (GrothendieckGroup.map P.ι hι) = 0 := by
  ext X
  rw [AddMonoidHom.comp_apply, map_of, map_of, ι_obj, AddMonoidHom.zero_apply]
  exact of_eq_zero_of_isZero ((isZero_obj_iff L P X.obj).2 X.property)

/-- **Stacks 02MX (1)**, as an isomorphism: the map `K₀(A) → K₀(D)` induced by the localization
functor `L` identifies `K₀(D)` with the quotient of `K₀(A)` by the image of
`K₀(P.FullSubcategory)`.

The inverse sends `[Y]` to the class of `[L.objPreimage Y]`. It respects the relations of `K₀(D)`
because every short exact sequence of `D` is isomorphic to the image of a short exact sequence of
`A` (`exists_shortExact_map_iso`), and any two preimages of an object have the same class
(`mk_of_eq_mk_of_of_iso`). -/
@[stacks 02MX "(1) as `K₀(A)/im K₀(C) ≃ K₀(A/C)`, for any localization `L`"]
noncomputable def grothendieckGroupEquiv :
    GrothendieckGroup A ⧸ (GrothendieckGroup.map P.ι hι).range ≃+ GrothendieckGroup D :=
  have := Localization.essSurj L P.isoModSerre
  AddMonoidHom.toAddEquiv
    (QuotientAddGroup.lift _ (GrothendieckGroup.map L hL)
      ((AddMonoidHom.range_le_ker_iff _ _).2 (map_comp_map_ι L P hι hL)))
    (GrothendieckGroup.lift (fun Y ↦ QuotientAddGroup.mk (of (L.objPreimage Y))) fun S hS ↦ by
      obtain ⟨T, hT, ⟨e⟩⟩ := exists_shortExact_map_iso L P S hS
      rw [mk_of_eq_mk_of_of_iso L P hι (L.objObjPreimageIso _).symm (asIso e.hom.τ₁).symm,
        mk_of_eq_mk_of_of_iso L P hι (L.objObjPreimageIso _).symm (asIso e.hom.τ₂).symm,
        mk_of_eq_mk_of_of_iso L P hι (L.objObjPreimageIso _).symm (asIso e.hom.τ₃).symm,
        additivity hT, QuotientAddGroup.mk_add])
    (by
      ext X
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, QuotientAddGroup.mk'_apply,
        QuotientAddGroup.lift_mk, map_of, GrothendieckGroup.lift_of]
      exact mk_of_eq_mk_of_of_iso L P hι (L.objObjPreimageIso _).symm (Iso.refl _))
    (by
      have := hasZeroObject L P
      ext Y
      rw [AddMonoidHom.comp_apply, GrothendieckGroup.lift_of, QuotientAddGroup.lift_mk, map_of,
        AddMonoidHom.id_apply]
      exact of_eq_of_iso (L.objObjPreimageIso Y))

/-- `grothendieckGroupEquiv` sends the class of `x` to the image of `x` under the map
`K₀(A) → K₀(D)` induced by `L`. -/
@[simp]
lemma grothendieckGroupEquiv_mk (x : GrothendieckGroup A) :
    grothendieckGroupEquiv L P hι hL (QuotientAddGroup.mk x) = GrothendieckGroup.map L hL x := by
  rw [grothendieckGroupEquiv, AddMonoidHom.toAddEquiv_apply, QuotientAddGroup.lift_mk]

/-- `grothendieckGroupEquiv` sends the class of `[X]` to `[L X]`. -/
lemma grothendieckGroupEquiv_mk_of (X : A) :
    grothendieckGroupEquiv L P hι hL (QuotientAddGroup.mk (of X)) = of (L.obj X) := by
  rw [grothendieckGroupEquiv_mk, map_of]

/-- The inverse of `grothendieckGroupEquiv` sends the image of `x` under the map
`K₀(A) → K₀(D)` induced by `L` to the class of `x`. -/
@[simp]
lemma grothendieckGroupEquiv_symm_map (x : GrothendieckGroup A) :
    (grothendieckGroupEquiv L P hι hL).symm (GrothendieckGroup.map L hL x) =
      QuotientAddGroup.mk x := by
  rw [AddEquiv.symm_apply_eq, grothendieckGroupEquiv_mk]

/-- The inverse of `grothendieckGroupEquiv` sends `[Y]` to the class of `[X]`, for any object `X`
of `A` with `Y ≅ L X`. -/
lemma grothendieckGroupEquiv_symm_of {Y : D} {X : A} (e : Y ≅ L.obj X) :
    (grothendieckGroupEquiv L P hι hL).symm (of Y) = QuotientAddGroup.mk (of X) := by
  rw [AddEquiv.symm_apply_eq, grothendieckGroupEquiv_mk_of]
  have := hasZeroObject L P
  exact of_eq_of_iso e

/-- The inverse of `grothendieckGroupEquiv` sends `[L X]` to the class of `[X]`. -/
@[simp]
lemma grothendieckGroupEquiv_symm_of_obj (X : A) :
    (grothendieckGroupEquiv L P hι hL).symm (of (L.obj X)) = QuotientAddGroup.mk (of X) :=
  grothendieckGroupEquiv_symm_of L P hι hL (Iso.refl _)

/-- `grothendieckGroupEquiv` composed with the projection of `K₀(A)` onto its quotient by the
image of `K₀(P.FullSubcategory)` is the map `K₀(A) → K₀(D)` induced by `L`. -/
lemma grothendieckGroupEquiv_comp_mk' :
    AddMonoidHom.comp (grothendieckGroupEquiv L P hι hL)
      (QuotientAddGroup.mk' (GrothendieckGroup.map P.ι hι).range) =
      GrothendieckGroup.map L hL := by
  ext X
  rw [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, AddMonoidHom.coe_ofClass,
    grothendieckGroupEquiv_mk_of, map_of]

/-- **Stacks 02MX (1)**, exactness at `K₀(A)`: the kernel of the map `K₀(A) → K₀(D)` induced by
`L` is the image of the map `K₀(P.FullSubcategory) → K₀(A)` induced by the inclusion. It is read
off `grothendieckGroupEquiv_comp_mk'`. -/
@[stacks 02MX "(1), exactness at `K₀(A)`"]
theorem exact_grothendieckGroup_map :
    Function.Exact (GrothendieckGroup.map P.ι hι) (GrothendieckGroup.map L hL) := by
  rw [AddMonoidHom.exact_iff, ← grothendieckGroupEquiv_comp_mk' L P hι hL,
    AddMonoidHom.ker_addEquiv_comp, QuotientAddGroup.ker_mk']

include P in
/-- **Stacks 02MX (1)**, surjectivity: the map `K₀(A) → K₀(D)` induced by `L` is surjective. This
is `GrothendieckGroup.map_surjective`, since `L` is essentially surjective and `D` has a zero
object. -/
@[stacks 02MX "(1), surjectivity of `K₀(A) → K₀(A/C)`"]
theorem grothendieckGroup_map_surjective :
    Function.Surjective (GrothendieckGroup.map L hL) := by
  have := Localization.essSurj L P.isoModSerre
  have := hasZeroObject L P
  exact GrothendieckGroup.map_surjective L hL

/-- An additive map `φ` from `K₀(A)` to an additive monoid that vanishes on the image of
`K₀(P.FullSubcategory)` factors uniquely through the map `K₀(A) → K₀(D)` induced by `L`. -/
lemma existsUnique_comp_map_eq {G : Type w} [AddMonoid G] (φ : GrothendieckGroup A →+ G)
    (hφ : φ.comp (GrothendieckGroup.map P.ι hι) = 0) :
    ∃! ψ : GrothendieckGroup D →+ G, ψ.comp (GrothendieckGroup.map L hL) = φ := by
  have h : ((QuotientAddGroup.lift _ φ ((AddMonoidHom.range_le_ker_iff _ _).2 hφ)).comp
      ((grothendieckGroupEquiv L P hι hL).symm : GrothendieckGroup D →+ _)).comp
      (GrothendieckGroup.map L hL) = φ := by
    ext X
    simp
  exact ExistsUnique.intro _ h fun ψ hψ ↦
    (AddMonoidHom.cancel_right (grothendieckGroup_map_surjective L P hL)).1 (hψ.trans h.symm)

end ObjectProperty.SerreClassLocalization

end CategoryTheory
