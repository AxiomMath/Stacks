module

public import StacksFrontier.AlgebraicGeometry.MayerVietorisHgroup.RestrictCover

/-!
# Mayer--Vietoris over an ambient open, read on cohomology classes

Let `X` be a topological space, `O` a sheaf of rings on `X`, and `U ⊔ V = W` two opens covering
an ambient open. The long exact sequence of
`StacksFrontier/AlgebraicGeometry/MayerVietorisHgroup/AmbientOpen.lean` is a statement about
morphisms of abelian groups; a diagram chase uses it on elements. This file reads off the four
element-level statements such a chase needs.

## Main definitions

* `Stacks.Cohomology.AmbientMayerVietoris.pair`: the class in `Hⁿ(U,G) ⊞ Hⁿ(V,G)` determined by
  a class on `U` and a class on `V`.

## Main results

* `Stacks.Cohomology.AmbientMayerVietoris.exists_restrict_eq_of_restrict_inf_eq`: **glueing** --
  two classes on `U` and on `V` whose restrictions to `U ⊓ V` agree are the restrictions of a
  class on `W`.
* `Stacks.Cohomology.AmbientMayerVietoris.eq_zero_of_restrict_eq_zero`: in degree zero a class
  on `W` restricting to zero on `U` and on `V` is zero.
* `Stacks.Cohomology.AmbientMayerVietoris.exists_ambientDelta_eq`: in positive degree a class on
  `W` restricting to zero on `U` and on `V` is the connecting morphism of a class on `U ⊓ V`.
* `Stacks.Cohomology.AmbientMayerVietoris.exists_restrict_sub_eq_of_ambientDelta_eq_zero`: a
  class on `U ⊓ V` killed by the connecting morphism is a difference of restrictions from `U` and
  from `V`.
* `Stacks.Cohomology.AmbientMayerVietoris.ambientDelta_restrict_sub`: the connecting morphism
  kills a difference of restrictions from `U` and from `V`.
* `Stacks.Cohomology.AmbientMayerVietoris.hrestrict_map` and
  `Stacks.Cohomology.AmbientMayerVietoris.ambientDelta_map`: restriction and the connecting
  morphism commute with the map induced by a morphism of sheaves of modules.

## Implementation notes

The two non-connecting maps of the sequence are the pair of restrictions and the difference of
the restrictions to the intersection, by
`Stacks.Cohomology.AmbientMayerVietoris.ambientFirst_eq` and
`Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond_eq`, so every statement below is about
restriction maps and the connecting morphism only; the biproduct is crossed through `pair` and
the four `biprod` component identities of `AmbientOpen.lean`.

Exactness is taken from `Stacks.Cohomology.AmbientMayerVietoris.mayerVietorisAmbient_exact` at
the two relevant spots and passed to elements by
`CategoryTheory.ShortComplex.ab_exact_iff`.

## References

* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AbsoluteMayerVietoris

universe u

namespace Stacks.Cohomology.AmbientMayerVietoris

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts
attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} O)]

variable (U V : Opens X) (G : SheafOfModules.{u} O)

/-! ### Restriction and the connecting morphism are natural in the sheaf

Both are natural transformations between the cohomology functors, so both commute with the map
induced by a morphism of sheaves of modules. These are the two naturality statements read on
classes. -/

section Naturality

variable {A B : Opens X} (h : A ≤ B) (p : ℕ) {G G' : SheafOfModules.{u} O} (φ : G ⟶ G')

/-- **Restriction commutes with the map induced by a morphism of sheaves of modules.** -/
theorem hrestrict_map (ξ : (Hgroup O B p G : Type u)) :
    Hrestrict O h p G' ((Hfunctor O B p).map φ ξ) =
      (Hfunctor O A p).map φ (Hrestrict O h p G ξ) := by
  simp [Hrestrict]

end Naturality

/-! ### The biproduct, on classes -/

/-- **The class of `Hⁿ(U,G) ⊞ Hⁿ(V,G)` determined by a class on `U` and a class on `V`.** -/
def pair (n : ℕ) (a : (Hgroup O U n G : Type u)) (b : (Hgroup O V n G : Type u)) :
    (((Hfunctor O U n ⊞ Hfunctor O V n).obj G : AddCommGrpCat.{u}) : Type u) :=
  (biprod.inl : Hfunctor O U n ⟶ Hfunctor O U n ⊞ Hfunctor O V n).app G a +
    (biprod.inr : Hfunctor O V n ⟶ Hfunctor O U n ⊞ Hfunctor O V n).app G b

/-- The first component of `pair` is its first argument. -/
theorem fst_pair (n : ℕ) (a : (Hgroup O U n G : Type u)) (b : (Hgroup O V n G : Type u)) :
    (biprod.fst : Hfunctor O U n ⊞ Hfunctor O V n ⟶ Hfunctor O U n).app G
        (pair O U V G n a b) = a := by
  simp [pair, ← AddCommGrpCat.comp_apply, biprod_inl_fst_app, biprod_inr_fst_app]

/-- The second component of `pair` is its second argument. -/
theorem snd_pair (n : ℕ) (a : (Hgroup O U n G : Type u)) (b : (Hgroup O V n G : Type u)) :
    (biprod.snd : Hfunctor O U n ⊞ Hfunctor O V n ⟶ Hfunctor O V n).app G
        (pair O U V G n a b) = b := by
  simp [pair, ← AddCommGrpCat.comp_apply, biprod_inl_snd_app, biprod_inr_snd_app]

/-- The pair of two zero classes is zero. -/
@[simp]
theorem pair_zero (n : ℕ) : pair O U V G n 0 0 = 0 := by
  dsimp only [pair]
  rw [map_zero, map_zero, add_zero]

/-- A class of the biproduct is the pair of its two components. -/
theorem pair_fst_snd (n : ℕ)
    (z : (((Hfunctor O U n ⊞ Hfunctor O V n).obj G : AddCommGrpCat.{u}) : Type u)) :
    pair O U V G n
        ((biprod.fst : Hfunctor O U n ⊞ Hfunctor O V n ⟶ Hfunctor O U n).app G z)
        ((biprod.snd : Hfunctor O U n ⊞ Hfunctor O V n ⟶ Hfunctor O V n).app G z) = z :=
  app_biprod_total (Hfunctor O U n) (Hfunctor O V n) G z

/-- **The second map of the Mayer--Vietoris sequence, on a pair of classes**: the difference of
the two restrictions to the intersection. -/
theorem mvSecond_pair (n : ℕ) (a : (Hgroup O U n G : Type u)) (b : (Hgroup O V n G : Type u)) :
    (mvSecond O U V n).app G (pair O U V G n a b) =
      Hrestrict O (inf_le_left : U ⊓ V ≤ U) n G a -
        Hrestrict O (inf_le_right : U ⊓ V ≤ V) n G b := by
  dsimp only [pair]
  rw [map_add, ← AddCommGrpCat.comp_apply, ← AddCommGrpCat.comp_apply, ← NatTrans.comp_app,
    ← NatTrans.comp_app, inl_comp_mvSecond, inr_comp_mvSecond]
  simp [Hrestrict, sub_eq_add_neg]

section Cover

variable (W : Opens X) (hU : U ≤ W) (hV : V ≤ W) (hUV : U ⊔ V = W)

/-- **The first map of the Mayer--Vietoris sequence, on a class over `W`**: the pair of the two
restrictions. -/
theorem ambientFirst_app (n : ℕ) (x : (Hgroup O W n G : Type u)) :
    (ambientFirst O W U V hU hV n).app G x =
      pair O U V G n (Hrestrict O hU n G x) (Hrestrict O hV n G x) := by
  rw [← pair_fst_snd O U V G n ((ambientFirst O W U V hU hV n).app G x)]
  congr 1 <;> rw [← AddCommGrpCat.comp_apply, ← NatTrans.comp_app, ambientFirst_eq] <;>
    simp [Hrestrict]

include hUV

/-- **Glueing.** Two classes on `U` and on `V` whose restrictions to `U ⊓ V` agree are the
restrictions of a class on `W`.  This is exactness of the Mayer--Vietoris sequence at the
biproduct. -/
theorem exists_restrict_eq_of_restrict_inf_eq (n : ℕ)
    (a : (Hgroup O U n G : Type u)) (b : (Hgroup O V n G : Type u))
    (hab : Hrestrict O (inf_le_left : U ⊓ V ≤ U) n G a =
      Hrestrict O (inf_le_right : U ⊓ V ≤ V) n G b) :
    ∃ x : (Hgroup O W n G : Type u),
      Hrestrict O hU n G x = a ∧ Hrestrict O hV n G x = b := by
  have hex := mayerVietorisAmbient_exact O W U V hU hV hUV n G
  have h01 := hex.exact 0 (by omega)
  have hel := (ShortComplex.ab_exact_iff _).1 h01
  have hz : (mvSecond O U V n).app G (pair O U V G n a b) = 0 := by
    rw [mvSecond_pair, hab, sub_self]
  obtain ⟨x, hx⟩ := hel (pair O U V G n a b) hz
  have hx' : (ambientFirst O W U V hU hV n).app G x = pair O U V G n a b := hx
  refine ⟨x, ?_, ?_⟩
  · rw [← fst_pair O U V G n a b, ← hx', ambientFirst_app, fst_pair]
  · rw [← snd_pair O U V G n a b, ← hx', ambientFirst_app, snd_pair]

/-- **In degree zero a class on `W` restricting to zero on `U` and on `V` is zero.**  This is
the leading zero of the Mayer--Vietoris sequence. -/
theorem eq_zero_of_restrict_eq_zero (x : (Hgroup O W 0 G : Type u))
    (hxU : Hrestrict O hU 0 G x = 0) (hxV : Hrestrict O hV 0 G x = 0) : x = 0 := by
  have hmono : Mono ((ambientFirst O W U V hU hV 0).app G) :=
    mono_ambientFirst_zero O W U V hU hV hUV G
  have hinj := (AddCommGrpCat.mono_iff_injective _).1 hmono
  refine hinj ?_
  simp only [ambientFirst_app, hxU, hxV, map_zero, pair_zero]

/-- **In positive degree a class on `W` restricting to zero on `U` and on `V` is a connecting
image.**  This is exactness of the Mayer--Vietoris sequence at `Hⁿ⁺¹(W,G)`. -/
theorem exists_ambientDelta_eq (n : ℕ) (x : (Hgroup O W (n + 1) G : Type u))
    (hxU : Hrestrict O hU (n + 1) G x = 0) (hxV : Hrestrict O hV (n + 1) G x = 0) :
    ∃ θ : (Hgroup O (U ⊓ V) n G : Type u),
      (ambientDelta O W U V hU hV hUV n).app G θ = x := by
  have hex := mayerVietorisAmbient_exact O W U V hU hV hUV n G
  have h23 := hex.exact 2 (by omega)
  have hel := (ShortComplex.ab_exact_iff _).1 h23
  have hz : (ambientFirst O W U V hU hV (n + 1)).app G x = 0 := by
    rw [ambientFirst_app, hxU, hxV, pair_zero]
  exact hel x hz

/-- **A class on `U ⊓ V` killed by the connecting morphism is a difference of restrictions.**
This is exactness of the Mayer--Vietoris sequence at `Hⁿ(U ⊓ V,G)`. -/
theorem exists_restrict_sub_eq_of_ambientDelta_eq_zero (n : ℕ)
    (θ : (Hgroup O (U ⊓ V) n G : Type u))
    (hθ : (ambientDelta O W U V hU hV hUV n).app G θ = 0) :
    ∃ (a : (Hgroup O U n G : Type u)) (b : (Hgroup O V n G : Type u)),
      Hrestrict O (inf_le_left : U ⊓ V ≤ U) n G a -
        Hrestrict O (inf_le_right : U ⊓ V ≤ V) n G b = θ := by
  have hex := mayerVietorisAmbient_exact O W U V hU hV hUV n G
  have h12 := hex.exact 1 (by omega)
  have hel := (ShortComplex.ab_exact_iff _).1 h12
  obtain ⟨z, hz⟩ := hel θ hθ
  have hz' : (mvSecond O U V n).app G z = θ := hz
  refine ⟨(biprod.fst : Hfunctor O U n ⊞ Hfunctor O V n ⟶ Hfunctor O U n).app G z,
    (biprod.snd : Hfunctor O U n ⊞ Hfunctor O V n ⟶ Hfunctor O V n).app G z, ?_⟩
  rw [← mvSecond_pair, pair_fst_snd]
  exact hz'

/-- **The connecting morphism kills a difference of restrictions.**  The composite of the second
map of the Mayer--Vietoris sequence with the connecting morphism is zero. -/
theorem ambientDelta_restrict_sub (n : ℕ)
    (a : (Hgroup O U n G : Type u)) (b : (Hgroup O V n G : Type u)) :
    (ambientDelta O W U V hU hV hUV n).app G
        (Hrestrict O (inf_le_left : U ⊓ V ≤ U) n G a -
          Hrestrict O (inf_le_right : U ⊓ V ≤ V) n G b) = 0 := by
  have hex := mayerVietorisAmbient_exact O W U V hU hV hUV n G
  have h : ((mvSecond O U V n).app G ≫ (ambientDelta O W U V hU hV hUV n).app G) = 0 :=
    hex.toIsComplex.zero 1
  have h2 : (ambientDelta O W U V hU hV hUV n).app G
      ((mvSecond O U V n).app G (pair O U V G n a b)) = 0 := by
    rw [← AddCommGrpCat.comp_apply, h]
    simp
  rw [mvSecond_pair] at h2
  exact h2

/-- **The connecting morphism commutes with the map induced by a morphism of sheaves of
modules.** -/
theorem ambientDelta_map (n : ℕ) {G' : SheafOfModules.{u} O} (φ : G ⟶ G')
    (θ : (Hgroup O (U ⊓ V) n G : Type u)) :
    (ambientDelta O W U V hU hV hUV n).app G' ((Hfunctor O (U ⊓ V) n).map φ θ) =
      (Hfunctor O W (n + 1)).map φ ((ambientDelta O W U V hU hV hUV n).app G θ) := by
  simp

end Cover

end Stacks.Cohomology.AmbientMayerVietoris

end
