module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.Algebra.Homology.InjectiveDimension.Criteria
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Basic
public import StacksFrontier.Homology.PseudoCoherent.HomFlat
public import StacksFrontier.RingTheory.Dualizing.Gorenstein

/-!
# Gorenstein schemes and flat morphisms

A scheme is *Gorenstein*, in the sense of `AlgebraicGeometry.IsGorenstein`, when it is locally
Noetherian and all of its local rings are Gorenstein. This file proves that the property descends
along a flat morphism: if `f : X ⟶ Y` is a flat morphism of locally Noetherian schemes with `X`
Gorenstein, then every local ring of `Y` at a point of the image of `f` is Gorenstein.

The descent statement is local on both schemes and rests on a purely algebraic fact about a flat
local homomorphism `A → B` of Noetherian local rings: if `B` is Gorenstein then so is `A`. That
is proved here as `Stacks.Duality.isGorensteinLocalRing_of_flat`. Since `B` is Gorenstein it has
finite injective dimension, so `Ext^i_B(N, B)` vanishes for every `B`-module `N` once `i` is
large. Applying this to `N = B ⊗_A κ_A` and comparing with `Ext^i_A(κ_A, A) ⊗_A B` through flat
base change for `Ext` shows that `Ext^i_A(κ_A, A) ⊗_A B` vanishes for large `i`; as a flat local
homomorphism is faithfully flat, `Ext^i_A(κ_A, A)` itself vanishes for large `i`, which is the
criterion for `A` to be Gorenstein.

## Main results

* `Stacks.Duality.isGorensteinLocalRing_of_flat` — a Noetherian local ring with a flat local
  homomorphism to a Gorenstein Noetherian local ring is Gorenstein. This is one half of
  Stacks 0BJL.
* `Stacks.Duality.isGorensteinLocalRing_stalk_of_flat` — the local ring of the base of a flat
  morphism at a point of the image is Gorenstein when the source is Gorenstein.

## Implementation notes

Flat base change for `Ext` is only available in the universe-lifted form of
`StacksDraft.PseudoCoherence.baseChange_ext_bijective_of_pseudoCoherent`, whose modules are
`ULift`s, while the Gorenstein criterion
`Dualizing.isGorensteinLocalRing_iff_residueField_ext_vanishing` is stated with `Shrink` of the
residue field. The two are matched by transporting along
`ULift.moduleEquiv` and `CategoryTheory.Abelian.Ext.homEquiv`, which identifies `Ext` in the
sense of Mathlib with a morphism group of the derived category.

## References

* [Stacks Project, Tag 0BJL](https://stacks.math.columbia.edu/tag/0BJL)
* [Stacks Project, Tag 0C12](https://stacks.math.columbia.edu/tag/0C12)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry StacksDraft.InjectiveDimension
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

/-- `Ext^n` between modules vanishes iff the derived-category `Ext` between isomorphic modules
does. -/
private theorem subsingleton_ext_iff_of_iso {R : Type u} [CommRing R] {M M' N N' : ModuleCat.{u} R}
    (e : M ≅ M') (e' : N ≅ N') (n : ℕ) :
    Subsingleton (CategoryTheory.Abelian.Ext.{u} M N n) ↔
      Subsingleton (DerivedCategory.Ext ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M')
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N') (n : ℤ)) :=
  (Equiv.subsingleton_congr (CategoryTheory.Abelian.Ext.homEquiv.trans
    (Iso.homCongr ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso e)
      ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (n : ℤ)).mapIso
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso e')))))

/-- Half of **Stacks Project, Tag 0BJL**: if `A → B` is a flat local homomorphism of Noetherian
local rings and `B` is Gorenstein, then `A` is Gorenstein.

Finite injective dimension of `B` kills `Ext^i_B(B ⊗_A κ_A, B)` for large `i`; flat base change
for `Ext` turns that into the vanishing of `Ext^i_A(κ_A, A) ⊗_A B`, and faithful flatness of a
flat local homomorphism removes the tensor factor. -/
theorem isGorensteinLocalRing_of_flat (A B : Type u) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [Module.Flat A B] [IsLocalHom (algebraMap A B)]
    (hB : Dualizing.IsGorensteinLocalRing B) :
    Dualizing.IsGorensteinLocalRing A := by
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hfin : Module.Finite A (Shrink.{u} (A ⧸ IsLocalRing.maximalIdeal A)) :=
    Module.Finite.equiv (Shrink.linearEquiv A (A ⧸ IsLocalRing.maximalIdeal A)).symm
  obtain ⟨a, bnd, hamp⟩ := hB.finiteInjectiveDimension
  have hvanish : ∀ (N : ModuleCat.{u} B) (i : ℤ), bnd < i →
      Subsingleton (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj N)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) i) :=
    fun N i hi =>
      ((hasInjectiveAmplitude_iff_ext_vanishing_iff_quotient_vanishing
        _ a bnd).1.mp hamp) N i (Or.inr hi)
  rw [Dualizing.isGorensteinLocalRing_iff_residueField_ext_vanishing]
  refine ⟨max bnd 0, fun i hi => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) :=
    ⟨i.toNat, (Int.toNat_of_nonneg (le_of_lt (lt_of_le_of_lt (le_max_right bnd 0) hi))).symm⟩
  have hn : bnd < (n : ℤ) := lt_of_le_of_lt (le_max_left bnd 0) hi
  obtain ⟨η, t, hη, ht, htu, hmain⟩ :=
    StacksDraft.PseudoCoherence.baseChange_ext_bijective_of_pseudoCoherent A B
      (Shrink.{u} (A ⧸ IsLocalRing.maximalIdeal A)) A
  obtain ⟨β, hcβ, huβ, hsmul, hzero, hfp, hpc, hnoeth⟩ := hmain n
  have hbij := hnoeth ‹_› hfin
  have hSN : Subsingleton (CategoryTheory.Abelian.Ext.{u}
      (ModuleCat.of B (ULift.{u} (B ⊗[A] Shrink.{u} (A ⧸ IsLocalRing.maximalIdeal A))))
      (ModuleCat.of B (ULift.{u} (B ⊗[A] A))) n) :=
    (subsingleton_ext_iff_of_iso (Iso.refl _)
      (ULift.moduleEquiv.trans (TensorProduct.AlgebraTensorModule.rid A B B)).toModuleIso n).2
      (hvanish _ n hn)
  have hTens : Subsingleton (CategoryTheory.Abelian.Ext.{u}
      (ModuleCat.of A (ULift.{u} (Shrink.{u} (A ⧸ IsLocalRing.maximalIdeal A))))
      (ModuleCat.of A (ULift.{u} A)) n ⊗[A] B) :=
    @Equiv.subsingleton _ _ (Equiv.ofBijective _ hbij) hSN
  have hExtA : Subsingleton (CategoryTheory.Abelian.Ext.{u}
      (ModuleCat.of A (ULift.{u} (Shrink.{u} (A ⧸ IsLocalRing.maximalIdeal A))))
      (ModuleCat.of A (ULift.{u} A)) n) :=
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_left A _).mp hTens
  exact (subsingleton_ext_iff_of_iso (ULift.moduleEquiv.toModuleIso (R := A))
    (ULift.moduleEquiv.toModuleIso (R := A)) n).1 hExtA

/-- **Stacks Project, Tag 0C12.** The local ring of the base at any point in the image of a flat
morphism of locally Noetherian schemes with Gorenstein source is Gorenstein.

The map of local rings `𝒪_{Y, f x} → 𝒪_{X, x}` induced by a flat morphism is a flat local
homomorphism of Noetherian local rings, so `isGorensteinLocalRing_of_flat` applies. -/
-- Tag 0C12 is covered by more than one declaration. This one is the clause
-- about the base: for a flat morphism of locally Noetherian schemes with
-- Gorenstein source, the local ring of the base at the image of any point
-- is Gorenstein; the attribute below records it with this clause as its
-- note.
@[stacks 0C12 "Gorenstein local rings of the base"]
theorem isGorensteinLocalRing_stalk_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsGorenstein X] [IsLocallyNoetherian Y] [Flat f] (x : X) :
    Dualizing.IsGorensteinLocalRing (Y.presheaf.stalk (f x)) := by
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (AlgebraicGeometry.Flat.iff_flat_stalkMap f).mp ‹_› x
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  exact isGorensteinLocalRing_of_flat _ _
    (AlgebraicGeometry.IsGorenstein.isGorensteinLocalRing x)

end Stacks.Duality
