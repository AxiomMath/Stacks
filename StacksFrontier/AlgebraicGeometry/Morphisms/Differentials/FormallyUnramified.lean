module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import StacksFrontier.AlgebraicGeometry.AffineDifferentials.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sheaf of relative differentials of a formally unramified morphism vanishes

A morphism of schemes is formally unramified exactly when it is so on every pair of affine
charts, and a formally unramified ring map has no nonzero derivations at all. Since the sheaf of
relative differentials of a morphism of schemes represents relative derivations of its structure
sheaf, and a section of the structure sheaf is locally a section over an affine open lying over
an affine open, the universal relative derivation of a formally unramified morphism is zero and
the sheaf representing it is a zero object.

## Main results

* `AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation_d_eq_zero`: the universal relative
  derivation of a formally unramified morphism annihilates every local section of the structure
  sheaf of its source.
* `AlgebraicGeometry.Scheme.Hom.isZero_relativeDifferentials_of_formallyUnramified`: the sheaf
  of relative differentials of a formally unramified morphism is a zero object.

## Implementation notes

The vanishing on an affine chart is read off from
`Stacks.AlgebraicGeometry.AffineDifferentials.sectionsDerivation`, which presents the universal
relative derivation on an open `U ≤ f ⁻¹ᵁ V` as a derivation of `Γ(X, U)` relative to the ring
map `Γ(S, V) ⟶ Γ(X, U)` induced by `f`; for affine `U` and `V` that ring map is formally
unramified, so the derivation is zero. Passing from affine charts to an arbitrary open uses only
separatedness of the sheaf of relative differentials, in the form
`CategoryTheory.Presheaf.IsSheaf.section_ext`.

Vanishing of a derivation is stated for `CategoryTheory.ModuleCat.Derivation`, the shape
`sectionsDerivation` has, rather than for `Derivation` over a pair of types: the scalar
multiplication of the base ring on the target is `Module.compHom` there, so the scalar tower is
supplied along with it instead of being assumed.

## References

* [Stacks Project, Tag 02G4](https://stacks.math.columbia.edu/tag/02G4)
* [Stacks Project, Tag 01US](https://stacks.math.columbia.edu/tag/01US)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.AffineDifferentials

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- A derivation with values in a module over a formally unramified ring map is zero: it factors
through the module of Kähler differentials, which is trivial. -/
private theorem moduleCatDerivation_d_eq_zero_of_formallyUnramified {A B : CommRingCat.{u}}
    (g : A ⟶ B) (hg : g.hom.FormallyUnramified) {M : ModuleCat.{u} B} (D : M.Derivation g)
    (b : B) : D.d b = 0 := by
  let := g.hom.toAlgebra
  let := Module.compHom M g.hom
  have hfu : Algebra.FormallyUnramified A B := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact hg
  let : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Subsingleton (KaehlerDifferential A B) := (Algebra.formallyUnramified_iff A B).mp hfu
  let D' : Derivation A B M := D
  have h := congrArg
    (fun L : KaehlerDifferential A B →ₗ[B] M => L (KaehlerDifferential.D A B b))
    (Subsingleton.elim D'.liftKaehlerDifferential (0 : KaehlerDifferential A B →ₗ[B] M))
  exact (by simpa using h : D' b = 0)

/-- The universal relative derivation of a formally unramified morphism annihilates the sections
over an affine open lying over an affine open. -/
private theorem universalRelativeDerivation_d_eq_zero_of_isAffineOpen (f : X ⟶ S)
    [FormallyUnramified f] {V : S.Opens} (hV : IsAffineOpen V) {U : X.Opens}
    (hU : IsAffineOpen U) (hUV : U ≤ f ⁻¹ᵁ V) (a : Γ(X, U)) :
    (universalRelativeDerivation f).d a = 0 :=
  moduleCatDerivation_d_eq_zero_of_formallyUnramified (f.appLE V U hUV)
    (f.formallyUnramified_appLE hV hU hUV) (sectionsDerivation f V U hUV) a

/-- **The universal relative derivation of a formally unramified morphism is zero.** -/
theorem universalRelativeDerivation_d_eq_zero (f : X ⟶ S) [FormallyUnramified f]
    (W : X.Opens) (s : Γ(X, W)) : (universalRelativeDerivation f).d s = 0 := by
  refine (relativeDifferentials f).isSheaf.section_ext (U := .op W) ?_
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ W ⊓ f ⁻¹ᵁ V from ⟨hx, hxV⟩) (W.2.inter (V.2.preimage f.base.hom.continuous))
  have hUW' : U ≤ W ⊓ f ⁻¹ᵁ V := hUW
  have hUW'' : U ≤ W := hUW'.trans inf_le_left
  refine ⟨U, hUW'', hxU, ?_⟩
  show (relativeDifferentials f).val.map (homOfLE hUW'').op
      ((universalRelativeDerivation f).d s) =
    (relativeDifferentials f).val.map (homOfLE hUW'').op 0
  rw [map_zero]
  exact ((universalRelativeDerivation f).d_map (homOfLE hUW'').op s).symm.trans
    (universalRelativeDerivation_d_eq_zero_of_isAffineOpen f hV hU (hUW'.trans inf_le_right) _)

/-- **The sheaf of relative differentials of a formally unramified morphism of schemes is a zero
object**: its universal derivation is zero, so the identity and the zero endomorphism both
factor the universal derivation through itself and are therefore equal. -/
@[ega "IV 17.4.2" "a) ⇒ c)"]
theorem isZero_relativeDifferentials_of_formallyUnramified (f : X ⟶ S) [FormallyUnramified f] :
    IsZero (relativeDifferentials f) := by
  obtain ⟨c, -, hu⟩ := SheafOfModules.universalDerivation_isUniversal (inverseImageStructureMap f)
    (relativeDifferentials f) (universalRelativeDerivation f)
  have hid : (𝟙 (relativeDifferentials f)) = c := by
    refine hu _ ?_
    ext U x
    rfl
  have hzero : (0 : relativeDifferentials f ⟶ relativeDifferentials f) = c := by
    refine hu _ ?_
    ext U x
    show ((0 : relativeDifferentials f ⟶ relativeDifferentials f).val.app U).hom
      ((universalRelativeDerivation f).d x) = (universalRelativeDerivation f).d x
    rw [universalRelativeDerivation_d_eq_zero f U.unop x, map_zero]
  exact (IsZero.iff_id_eq_zero _).mpr (hid.trans hzero.symm)

end AlgebraicGeometry.Scheme.Hom

end
