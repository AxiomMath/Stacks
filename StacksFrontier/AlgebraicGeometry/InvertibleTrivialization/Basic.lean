module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.RingTheory.Module.IdealSmulTop

/-!
# An invertible sheaf of modules is locally trivial

Let `(X, 𝒪_X)` be a ringed space all of whose stalks `𝒪_{X,x}` are local rings, and let `L` be
an invertible sheaf of `𝒪_X`-modules. This file proves that `L` is locally free of rank one:
every point of `X` has an open neighbourhood `W` and a section `a ∈ L(W)` such that, on every
open `V ≤ W`, the map `c ↦ c • a|_V` is a bijection `𝒪_X(V) → L(V)`. This is the converse half
of [Stacks, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M).

`exists_bijective_smul_of_isInvertible` below is the form consumers want: it produces exactly
the hypothesis that `nonempty_orderOfVanishingData_of_bijective_smul` and the other
trivialization consumers take as a parameter.

**Both `Stacks.SheafOfModules.IsInvertible` and the byte-identical
`AlgebraicGeometry.SheafOfModules.IsInvertible` carry this trivialization.**
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`
(`StacksFrontier/AlgebraicGeometry/InvertibleClasses/Basic.lean`) relates the two, and 0B8M's
clause-2 output reaches the `AlgebraicGeometry` class through it: an
`AlgebraicGeometry`-class invertible module obtains `IsFiniteLocallyFreeOfRank _ 1` by
`infer_instance`. **So a statement may use either class.**

## Main results

* `Stacks.SheafOfModules.Invertible.bijective_smul_of_notMem_maximalIdeal_smul_top`: the
  algebraic core. Over a local ring, a module that is invertible in the sense of
  `Module.Invertible` is free of rank one on any element outside `𝔪 M`.
* `Stacks.SheafOfModules.exists_tensorPairing_eq_unitSection`: given a trivialization
  `ψ : L ⊗_{𝒪_X} N ≅ 𝒪_X`, every point has a neighbourhood carrying sections `a` of `L` and
  `b` of `N` that pair to `1`.
* `Stacks.SheafOfModules.bijective_smul_of_tensorPairing_eq_unitSection`: such a pair
  trivializes `L` over *every* smaller open, not just over the one where it was found.
* `Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible` and
  `Stacks.SheafOfModules.exists_nonempty_linearEquiv_of_isInvertible`: the two packaged forms
  of the conclusion for an invertible `L`, the second as a linear equivalence
  `L(V) ≃ₗ[𝒪_X(V)] 𝒪_X(V)`.

## Implementation notes

The Stacks proof of Tag 0B8M argues that the germ of a trivializing section is a *basis* of
`L_x` by Nakayama's lemma, which presupposes that `L_x` is a finitely generated
`𝒪_{X,x}`-module. That finiteness is what
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FinitePresentationStalk.lean` records as
unavailable, and it is not used here. Instead the stalk pairing
`Stacks.SheafOfModules.stalkPairing` exhibits `L_x` as an *invertible* `𝒪_{X,x}`-module
directly, and an invertible module over a local ring is already free of rank one
(`Stacks.SheafOfModules.Invertible.nonempty_linearEquiv_of_module_invertible`), with no
finiteness input at all. So the only work left is to see that an element outside `𝔪 L_x`
generates, which is `bijective_smul_of_notMem_maximalIdeal_smul_top`.

Everything is then local-to-global in one step: bijectivity of `c ↦ c • a|_V` is checked on
stalks, where the two directions are the two halves of that algebraic core, and transported to
sections by `TopCat.Presheaf.section_ext`. Note that the trivializing pair is found at a single
point but works over every open contained in the neighbourhood where it lives, because
`Stacks.SheafOfModules.tensorPairing_res` restricts the pairing and the stalk argument is
repeated verbatim at every point of that open.

The invertibility predicate is `Stacks.SheafOfModules.IsInvertible`, the one whose API
(`Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit`,
`Stacks.SheafOfModules.stalkPairing`, `Stacks.SheafOfModules.exists_tmul_eq_one`) this file
consumes. It is *not* `AlgebraicGeometry.SheafOfModules.IsInvertible` of
`StacksFrontier/Topology/Sheaves/Modules/Invertible.lean`; the two classes have byte-identical
definitions but are distinct constants, and no bridge between them is written here.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public section

open CategoryTheory TensorProduct Opposite TopologicalSpace AlgebraicGeometry IsLocalRing
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules.Invertible

section LocalAlgebra

variable {R : Type u} [CommRing R] {M P : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P]

/-- Under an identification `M ≃ₗ R`, the submodule `𝔪 M` corresponds to the maximal ideal. -/
theorem mem_maximalIdeal_smul_top_iff [IsLocalRing R] (e : M ≃ₗ[R] R) (a : M) :
    a ∈ maximalIdeal R • (⊤ : Submodule R M) ↔ e a ∈ maximalIdeal R := by
  have hmap : Submodule.map (e.symm : R →ₗ[R] M) (maximalIdeal R • (⊤ : Submodule R R))
      = maximalIdeal R • (⊤ : Submodule R M) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  rw [← hmap, Ideal.smul_top_eq_self]
  refine ⟨?_, fun h => ⟨e a, h, e.symm_apply_apply a⟩⟩
  rintro ⟨r, hr, rfl⟩
  simpa using hr

/-- **The algebraic core of the converse half of Tag 0B8M.** Over a local ring, an invertible
module is free of rank one on any element that does not lie in `𝔪 M`: such an element has unit
image under any identification `M ≃ₗ R`, so multiplication by it is bijective. No finiteness
hypothesis on `M` is needed, because an invertible module over a local ring is already free of
rank one. -/
theorem bijective_smul_of_notMem_maximalIdeal_smul_top [IsLocalRing R] [Module.Invertible R M]
    (a : M) (ha : a ∉ maximalIdeal R • (⊤ : Submodule R M)) :
    Function.Bijective fun c : R => c • a := by
  obtain ⟨e⟩ := nonempty_linearEquiv_of_module_invertible R M
  obtain ⟨v, hv⟩ : ∃ v, e a * v = 1 :=
    (notMem_maximalIdeal.1 (fun h => ha ((mem_maximalIdeal_smul_top_iff e a).2 h))).exists_right_inv
  refine ⟨fun c c' h => ?_, fun m => ⟨e m * v, e.injective ?_⟩⟩
  · have h' : c * e a = c' * e a := by
      simpa only [map_smul, smul_eq_mul] using congrArg e h
    calc c = c * (e a * v) := by rw [hv, mul_one]
      _ = c' * e a * v := by rw [← mul_assoc, h']
      _ = c' * (e a * v) := by rw [mul_assoc]
      _ = c' := by rw [hv, mul_one]
  · rw [map_smul, smul_eq_mul, mul_assoc, mul_comm v (e a), hv, mul_one]

/-- A pairing `M ⊗ P ≃ R` is linear in the first factor. Stated separately from the sheaf-level
argument so that the scalar action is the one the tensor product was formed with. -/
theorem pairing_smul_tmul (Θ : M ⊗[R] P ≃ₗ[R] R) (c : R) (u : M) (v : P) :
    Θ ((c • u) ⊗ₜ[R] v) = c * Θ (u ⊗ₜ[R] v) := by
  rw [← TensorProduct.smul_tmul', map_smul, smul_eq_mul]

end LocalAlgebra

end Stacks.SheafOfModules.Invertible

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
  {L N : SheafOfModules.{u} (structureSheafRing X)}
  (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (L)).obj
    (N)) ≅ SheafOfModules.unit (structureSheafRing X))

/-- Given a trivialization `ψ : L ⊗_{𝒪_X} N ≅ 𝒪_X`, every point of `X` has an open
neighbourhood carrying sections of `L` and of `N` that pair to the unit section.

The germ of `L` at `x` is an invertible module over the local ring `𝒪_{X,x}`, hence free of
rank one; a generator is not in `𝔪_x L_x`, so it pairs to `1` with some germ of `N`, and the
two germs are represented by sections on a neighbourhood whose pairing has germ `1`. -/
theorem exists_tensorPairing_eq_unitSection (x : X.carrier) :
    ∃ (W : Opens X.carrier) (_ : x ∈ W) (a : L.val.obj (op W)) (b : N.val.obj (op W)),
      tensorPairing ψ W a b = unitSection X W := by
  have : Module.Invertible (ringStalk X x) (grpStalk X L.val x) := .left (stalkPairing ψ x)
  obtain ⟨e⟩ := Invertible.nonempty_linearEquiv_of_module_invertible
    (ringStalk X x) (grpStalk X L.val x)
  have hl : e.symm 1 ∉ maximalIdeal (ringStalk X x) •
      (⊤ : Submodule (ringStalk X x) (grpStalk X L.val x)) := by
    rw [Invertible.mem_maximalIdeal_smul_top_iff e, e.apply_symm_apply]
    exact fun h => (Ideal.ne_top_iff_one _).mp (maximalIdeal.isMaximal _).ne_top h
  obtain ⟨n, hn⟩ := exists_tmul_eq_one (stalkPairing ψ x) (e.symm 1) hl
  obtain ⟨U₁, hx₁, a₁, ha₁⟩ := exists_grpGerm_eq X L.val x (e.symm 1)
  obtain ⟨U₂, hx₂, b₂, hb₂⟩ := exists_grpGerm_eq X N.val x n
  set U : Opens X.carrier := U₁ ⊓ U₂ with hU
  have hxU : x ∈ U := ⟨hx₁, hx₂⟩
  obtain ⟨a, hga⟩ : ∃ a : L.val.obj (op U), grpGerm X L.val x U hxU a = e.symm 1 :=
    ⟨L.val.map (homOfLE (inf_le_left : U ≤ U₁)).op a₁,
      Eq.trans (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) L.val.presheaf
        (homOfLE (inf_le_left : U ≤ U₁)) x hxU a₁) ha₁⟩
  obtain ⟨b, hgb⟩ : ∃ b : N.val.obj (op U), grpGerm X N.val x U hxU b = n :=
    ⟨N.val.map (homOfLE (inf_le_right : U ≤ U₂)).op b₂,
      Eq.trans (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) N.val.presheaf
        (homOfLE (inf_le_right : U ≤ U₂)) x hxU b₂) hb₂⟩
  have hring : ringGerm X x U hxU (tensorPairing ψ U a b) = 1 := by
    rw [← stalkPairing_germ ψ x U hxU a b, hga, hgb, hn]
  have hgrp : grpGerm X (SheafOfModules.unit (structureSheafRing X)).val x U hxU
      (tensorPairing ψ U a b)
      = grpGerm X (SheafOfModules.unit (structureSheafRing X)).val x ⊤ (Opens.mem_top x)
        (unitSection X ⊤) := by
    rw [← ringGerm_smul_unitGerm X x U hxU (tensorPairing ψ U a b), hring, one_smul, unitGerm]
  obtain ⟨W, hxW, iW, jW, hW⟩ := TopCat.Presheaf.germ_eq (C := AddCommGrpCat.{u})
    (SheafOfModules.unit (structureSheafRing X)).val.presheaf x hxU (Opens.mem_top x)
    (tensorPairing ψ U a b) (unitSection X ⊤) hgrp
  refine ⟨W, hxW, L.val.map iW.op a, N.val.map iW.op b, ?_⟩
  rw [← tensorPairing_res]
  exact hW.trans (map_one ((structureSheafRing X).obj.map jW.op).hom)

/-- The stalk consequence of a pair of sections pairing to the unit section: at every point of
the open where they live, the pairing of their germs is `1`, and the germ of the section of `L`
is a basis of the stalk `L_y`. -/
theorem bijective_smul_germ_of_tensorPairing_eq_unitSection {V : Opens X.carrier}
    (a : L.val.obj (op V)) (b : N.val.obj (op V)) (hab : tensorPairing ψ V a b = unitSection X V)
    (y : X.carrier) (hy : y ∈ V) :
    stalkPairing ψ y (grpGerm X L.val y V hy a ⊗ₜ[ringStalk X y] grpGerm X N.val y V hy b) = 1 ∧
      Function.Bijective fun c : ringStalk X y => c • grpGerm X L.val y V hy a := by
  have h1 : stalkPairing ψ y
      (grpGerm X L.val y V hy a ⊗ₜ[ringStalk X y] grpGerm X N.val y V hy b) = 1 := by
    rw [stalkPairing_germ ψ y V hy a b, hab]
    exact map_one (ringGerm X y V hy)
  have : Module.Invertible (ringStalk X y) (grpStalk X L.val y) := .left (stalkPairing ψ y)
  exact ⟨h1, Invertible.bijective_smul_of_notMem_maximalIdeal_smul_top _
    (notMem_smul_of_tmul_eq_one (stalkPairing ψ y) _ _ h1)⟩

/-- **A pair of sections pairing to the unit section trivializes `L` over every smaller open.**
Both directions are checked on stalks and transported to sections by the sheaf condition:
injectivity because the germ of `a` is a basis, surjectivity because the explicit preimage of a
section `m` is its own pairing with `b`. -/
theorem bijective_smul_of_tensorPairing_eq_unitSection (W : Opens X.carrier)
    (a : L.val.obj (op W)) (b : N.val.obj (op W)) (hab : tensorPairing ψ W a b = unitSection X W)
    (V : Opens X.carrier) (hVW : V ≤ W) :
    Function.Bijective fun c : X.presheaf.obj (op V) =>
      c • (L.val.map (homOfLE hVW).op a) := by
  have hab' : tensorPairing ψ V (L.val.map (homOfLE hVW).op a) (N.val.map (homOfLE hVW).op b)
      = unitSection X V := by
    rw [← tensorPairing_res ψ (homOfLE hVW) a b, hab]
    exact map_one ((structureSheafRing X).obj.map (homOfLE hVW).op).hom
  set a' : L.val.obj (op V) := L.val.map (homOfLE hVW).op a with ha'
  set b' : N.val.obj (op V) := N.val.map (homOfLE hVW).op b with hb'
  constructor
  · intro c c' hc
    refine TopCat.Presheaf.section_ext (C := CommRingCat.{u}) ⟨X.presheaf, X.IsSheaf⟩ V c c'
      fun y hy => ?_
    obtain ⟨h1, hbij⟩ := bijective_smul_germ_of_tensorPairing_eq_unitSection ψ a' b' hab' y hy
    refine hbij.1 (show ringGerm X y V hy c • _ = ringGerm X y V hy c' • _ from ?_)
    rw [← stalkModule_germ_smul X L.val y V hy c a', ← stalkModule_germ_smul X L.val y V hy c' a']
    exact congrArg (grpGerm X L.val y V hy) hc
  · intro m
    set c : X.presheaf.obj (op V) := tensorPairing ψ V m b' with hcdef
    refine ⟨c, ?_⟩
    refine TopCat.Presheaf.section_ext (C := AddCommGrpCat.{u}) ⟨L.val.presheaf, L.isSheaf⟩ V _ m
      fun y hy => ?_
    obtain ⟨h1, hbij⟩ := bijective_smul_germ_of_tensorPairing_eq_unitSection ψ a' b' hab' y hy
    obtain ⟨c₀, hc₀⟩ := hbij.2 (grpGerm X L.val y V hy m)
    have hc₀' : c₀ • grpGerm X L.val y V hy a' = grpGerm X L.val y V hy m := hc₀
    change grpGerm X L.val y V hy (c • a') = _
    rw [stalkModule_germ_smul X L.val y V hy c a', hcdef,
      ← stalkPairing_germ ψ y V hy m b', ← hc₀',
      Invertible.pairing_smul_tmul (stalkPairing ψ y) c₀ _ _, h1, mul_one]
    exact hc₀'

variable (L) in
/-- **The converse half of Stacks Project, Tag 0B8M.** An invertible sheaf of modules on a
ringed space whose stalks are local rings is locally free of rank one: every point has an open
neighbourhood `W` and a section `a ∈ L(W)` such that `c ↦ c • a|_V` is a bijection
`𝒪_X(V) → L(V)` for every open `V ≤ W`. -/
theorem exists_bijective_smul_of_isInvertible
    [IsInvertible X.presheaf (structureSheafRing X).property L] (x : X.carrier) :
    ∃ (W : Opens X.carrier) (_ : x ∈ W) (a : L.val.obj (op W)),
      ∀ (V : Opens X.carrier) (hVW : V ≤ W),
        Function.Bijective fun c : X.presheaf.obj (op V) =>
          c • (L.val.map (homOfLE hVW).op a) := by
  obtain ⟨N, ⟨ψ⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf) (hO := (structureSheafRing X).property) L).mp ‹_›
  obtain ⟨W, hxW, a, b, hab⟩ := exists_tensorPairing_eq_unitSection ψ x
  exact ⟨W, hxW, a, fun V hVW =>
    bijective_smul_of_tensorPairing_eq_unitSection ψ W a b hab V hVW⟩

variable (L) in
/-- The converse half of Tag 0B8M, read as a linear equivalence on sections: an invertible
sheaf of modules on a ringed space with local stalks has `L(V) ≃ₗ[𝒪_X(V)] 𝒪_X(V)` for every
open `V` inside a suitable neighbourhood of any given point. -/
theorem exists_nonempty_linearEquiv_of_isInvertible
    [IsInvertible X.presheaf (structureSheafRing X).property L] (x : X.carrier) :
    ∃ (W : Opens X.carrier), x ∈ W ∧ ∀ V : Opens X.carrier, V ≤ W →
      Nonempty (L.val.obj (op V) ≃ₗ[X.presheaf.obj (op V)] X.presheaf.obj (op V)) := by
  obtain ⟨W, hxW, a, ha⟩ := exists_bijective_smul_of_isInvertible L x
  refine ⟨W, hxW, fun V hVW => ⟨(LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton (X.presheaf.obj (op V)) (L.val.obj (op V))
      (L.val.map (homOfLE hVW).op a)) (ha V hVW)).symm⟩⟩

/-- The converse half of Tag 0B8M for a scheme, where the stalks of the structure sheaf are
local rings automatically: an invertible `𝒪_Y`-module is trivialized on the sections over every
open inside a suitable neighbourhood of any given point. This is the form the zero-scheme and
regular-section arguments of Chapter 31 consume. -/
theorem Scheme.exists_nonempty_linearEquiv_of_isInvertible (Y : Scheme.{u}) (L : Y.Modules)
    [IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L] (x : Y) :
    ∃ W : Opens Y, x ∈ W ∧ ∀ V : Opens Y, V ≤ W →
      Nonempty (Γ(L, V) ≃ₗ[Γ(Y, V)] Γ(Y, V)) := by
  have : ∀ z : Y.toRingedSpace.carrier, IsLocalRing (ringStalk Y.toRingedSpace z) :=
    fun z => Y.isLocalRing z
  exact Stacks.SheafOfModules.exists_nonempty_linearEquiv_of_isInvertible
    (X := Y.toRingedSpace) L x

end Stacks.SheafOfModules

end
