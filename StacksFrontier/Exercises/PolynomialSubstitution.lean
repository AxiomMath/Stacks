module

public import Mathlib.Data.ZMod.Basic
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# Substitution by a monic polynomial is finite locally free

Substitution of a monic polynomial of positive degree for the variable gives a finite locally
free map of polynomial rings, both over the integers and after reduction modulo a prime.

The map sending the variable to `h` is `Polynomial.aeval h`, and its underlying ring
homomorphism supplies the module structure on the target. The target is in fact free: writing
`S = R[X]`, the polynomial `q = h - Y` over `S` is monic of degree `deg h`, and `S[Y]/(q)` is
identified with `S` acting on `R[X]` through `aeval h`, by sending the root of `q` to `X`. The
power basis of `AdjoinRoot q` transports along that identification to a basis of `deg h`
elements, and a module with a finite basis is finite locally free of that rank, on the cover of
the spectrum by the single basic open of `1`. In the second statement the polynomial is reduced
coefficientwise to `ZMod p` before substitution; its degree is unchanged because its leading
coefficient is `1`. The rank is the natural degree of `h` in each case.

## Main results

* `Polynomial.monic_aeval_isFiniteLocallyFreeOfRank_int`: the integral statement.
* `Polynomial.monic_aeval_isFiniteLocallyFreeOfRank_zmod`: the statement modulo a prime.

## Implementation notes

The identification passes through a `ULift` of `R[X]`, so that the two `Algebra (R[X]) ·`
structures in play -- the identity one and the one through `aeval h` -- live on different types
and do not collide during elaboration. The two mutually inverse algebra maps between
`AdjoinRoot q` and that `ULift` are written out and then shown to be mutually inverse.

## References

* [Stacks Project, Tag 02ER](https://stacks.math.columbia.edu/tag/02ER)
-/

@[expose] public section

open Polynomial



namespace Polynomial

private theorem aeval_monic_basis (R : Type) [CommRing R] [Nontrivial R]
    (h : Polynomial R) (hh : h.Monic) (hd : 0 < h.natDegree) :
    letI : Algebra (Polynomial R) (Polynomial R) :=
      (Polynomial.aeval h).toRingHom.toAlgebra
    letI : Module (Polynomial R) (Polynomial R) :=
      ((Polynomial.aeval h).toRingHom.toAlgebra).toModule
    Nonempty (Module.Basis (Fin h.natDegree) (Polynomial R) (Polynomial R)) := by
  let q : R[X][X] := h.map (algebraMap R R[X]) - C (X : R[X])
  have hqdeg : q.natDegree = h.natDegree := by
    simp only [q, natDegree_sub_C]
    exact natDegree_map_eq_of_injective C_injective h
  have hqmonic : q.Monic := by
    have hm : (h.map (algebraMap R R[X])).Monic := hh.map _
    refine hm.sub_of_left (degree_C_le.trans_lt ?_)
    rw [degree_eq_natDegree hm.ne_zero,
      natDegree_map_eq_of_injective (f := algebraMap R R[X]) C_injective]
    exact_mod_cast hd
  let φ : R[X] →+* ULift.{0} R[X] := ULift.ringEquiv.symm.toRingHom.comp (aeval h).toRingHom
  have hroot : eval₂ φ (ULift.up X) q = 0 := by
    have : φ.comp (algebraMap R R[X]) = ULift.ringEquiv.symm.toRingHom.comp C := by
      ext
      simp [φ]
    simp only [q]
    rw [eval₂_sub, eval₂_map, eval₂_C, this,
      show (ULift.up X : ULift.{0} R[X]) = ULift.ringEquiv.symm.toRingHom X from rfl,
      ← hom_eval₂, eval₂_C_X, sub_eq_zero]
    simp [φ]
  let ψ : ULift.{0} R[X] →+* AdjoinRoot q :=
    (eval₂RingHom (algebraMap R _) (AdjoinRoot.root _)).comp ULift.ringEquiv.toRingHom
  have hψφ : ψ.comp φ = algebraMap R[X] (AdjoinRoot q) := by
    refine ringHom_ext (fun r => ?_) ?_
    · change eval₂ (algebraMap R _) (AdjoinRoot.root _) (aeval h (C r)) = _
      rw [aeval_C, algebraMap_eq, eval₂_C, IsScalarTower.algebraMap_apply R R[X], algebraMap_eq]
    · change eval₂ (algebraMap R _) (AdjoinRoot.root _) (aeval h X) = _
      rw [aeval_X, IsScalarTower.algebraMap_eq R R[X] (AdjoinRoot _), AdjoinRoot.algebraMap_eq]
      simpa only [q, eval₂_sub, eval₂_map, eval₂_C, sub_eq_zero] using AdjoinRoot.eval₂_root q
  let : Algebra R[X] (ULift.{0} R[X]) := φ.toAlgebra
  let : Module R[X] (ULift.{0} R[X]) := φ.toAlgebra.toModule
  let toB := AdjoinRoot.liftAlgHom q (Algebra.ofId R[X] (ULift.{0} R[X])) (ULift.up X) hroot
  let fromB : ULift.{0} R[X] →ₐ[R[X]] AdjoinRoot q :=
    { toRingHom := ψ, commutes' := RingHom.congr_fun hψφ }
  have htoRoot : toB (AdjoinRoot.root _) = ULift.up X := AdjoinRoot.liftAlgHom_root ..
  have hfromRoot : fromB (ULift.up X) = AdjoinRoot.root _ := eval₂_X _ _
  have htofrom (x : ULift.{0} R[X]) : toB (fromB x) = x := by
    obtain ⟨p⟩ := x
    apply ULift.down_injective
    have : ULift.ringEquiv.toRingHom.comp (toB.toRingHom.comp (ψ.comp
        ULift.ringEquiv.symm.toRingHom)) = RingHom.id R[X] := by
      refine ringHom_ext (fun r => ?_) ?_
      · change (toB (eval₂ (algebraMap R _) (AdjoinRoot.root _) (C r))).down = C r
        rw [eval₂_C, IsScalarTower.algebraMap_apply R R[X], toB.commutes]
        change aeval h (algebraMap R R[X] r) = C r
        simp
      · change (toB (eval₂ (algebraMap R _) (AdjoinRoot.root _) X)).down = X
        rw [eval₂_X, htoRoot]
    exact DFunLike.congr_fun this p
  let e : AdjoinRoot q ≃ₐ[R[X]] ULift.{0} R[X] :=
    AlgEquiv.ofAlgHom toB fromB (AlgHom.ext htofrom)
      (AdjoinRoot.algHom_ext <| by simp [htoRoot, hfromRoot])
  let bU := ((AdjoinRoot.powerBasis' hqmonic).basis.map e.toLinearEquiv).reindex (finCongr hqdeg)
  let : Algebra R[X] R[X] := (aeval h).toRingHom.toAlgebra
  let : Module R[X] R[X] := ((aeval h).toRingHom.toAlgebra).toModule
  let downLin : ULift.{0} R[X] ≃ₗ[R[X]] R[X] :=
    { ULift.ringEquiv.toAddEquiv with map_smul' := fun _ _ => rfl }
  exact ⟨bU.map downLin⟩

private theorem isFiniteLocallyFreeOfRank_of_basis {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] {n : ℕ} (b : Module.Basis (Fin n) R M) :
    Module.IsFiniteLocallyFreeOfRank R M n := by
  classical
  refine ⟨Unit, fun _ => 1, by simp, fun _ => ?_⟩
  let : Algebra R (Localization.Away (1 : R)) :=
    @OreLocalization.instAlgebra R _ (Submonoid.powers (1 : R)) _ R _ (Algebra.id R)
  let : IsLocalization (Submonoid.powers (1 : R)) (Localization.Away (1 : R)) :=
    Localization.isLocalization (R := R) (M := Submonoid.powers 1)
  exact ⟨b.ofIsLocalizedModule (Localization.Away (1 : R))
    (Submonoid.powers (1 : R))
    (LocalizedModule.mkLinearMap (Submonoid.powers (1 : R)) M)⟩

/-- Substitution by a monic polynomial of positive degree `n` is finite locally free of rank `n`. -/
private theorem aeval_isFiniteLocallyFreeOfRank (R : Type) [CommRing R] [Nontrivial R]
    (h : Polynomial R) (hh : h.Monic) (hd : 0 < h.natDegree) {n : ℕ} (hn : h.natDegree = n) :
    letI : Algebra (Polynomial R) (Polynomial R) := (Polynomial.aeval h).toRingHom.toAlgebra
    letI : Module (Polynomial R) (Polynomial R) := Algebra.toModule
    Module.IsFiniteLocallyFreeOfRank (Polynomial R) (Polynomial R) n := by
  let : Algebra (Polynomial R) (Polynomial R) := (Polynomial.aeval h).toRingHom.toAlgebra
  let : Module (Polynomial R) (Polynomial R) :=
    ((Polynomial.aeval h).toRingHom.toAlgebra).toModule
  obtain ⟨b⟩ := aeval_monic_basis R h hh hd
  exact isFiniteLocallyFreeOfRank_of_basis (b.reindex (finCongr hn))

/-- Substitution by a monic integral polynomial of positive degree is finite locally free
of rank equal to its degree. -/
@[stacks 02ER "part (1)"]
theorem monic_aeval_isFiniteLocallyFreeOfRank_int (h : Polynomial ℤ)
    (hh : h.Monic) (hd : 0 < h.natDegree) :
    letI : Algebra (Polynomial ℤ) (Polynomial ℤ) := (Polynomial.aeval h).toRingHom.toAlgebra
    letI : Module (Polynomial ℤ) (Polynomial ℤ) := Algebra.toModule
    Module.IsFiniteLocallyFreeOfRank (Polynomial ℤ) (Polynomial ℤ) h.natDegree :=
  aeval_isFiniteLocallyFreeOfRank ℤ h hh hd rfl

/-- After reduction modulo a prime, substitution by the reduced monic polynomial is
finite locally free of the original degree. -/
@[stacks 02ER "part (2)"]
theorem monic_aeval_isFiniteLocallyFreeOfRank_zmod (h : Polynomial ℤ)
    (hh : h.Monic) (hd : 0 < h.natDegree) (p : ℕ) (hp : p.Prime) :
    let g : Polynomial (ZMod p) := h.map (Int.castRingHom (ZMod p))
    letI : Algebra (Polynomial (ZMod p)) (Polynomial (ZMod p)) :=
      (Polynomial.aeval g).toRingHom.toAlgebra
    letI : Module (Polynomial (ZMod p)) (Polynomial (ZMod p)) := Algebra.toModule
    Module.IsFiniteLocallyFreeOfRank (Polynomial (ZMod p))
      (Polynomial (ZMod p)) h.natDegree := by
  let g : Polynomial (ZMod p) := h.map (Int.castRingHom (ZMod p))
  let : Fact p.Prime := ⟨hp⟩
  have hgdeg : g.natDegree = h.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero _ (by simp [hh])
  exact aeval_isFiniteLocallyFreeOfRank (ZMod p) g (hh.map _) (by simpa [hgdeg] using hd) hgdeg

end Polynomial

end
