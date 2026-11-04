module

public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup

/-!
# The Chern character as a ring map on the Grothendieck ring of vector bundles

Let `X` be a scheme. A function on `𝒪_X`-modules with values in a ring `R` which vanishes off
the finite locally free modules, is additive on short exact sequences of finite locally free
modules, is multiplicative on tensor products and takes the value `1` on `𝒪_X` extends uniquely
to a ring homomorphism on `K₀(Vect(X))`. For the Chern character
`ch(ℰ) = ∑_{p ≥ 0} P_p(c_1(ℰ), …, c_p(ℰ))/p!` with values in `∏_{i ≥ 0} A^i(X) ⊗ 𝐐`, this is
the ring map `ch : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X) ⊗ 𝐐` sending the generator `[ℰ]` to `ch(ℰ)`.

## Main results

* `AlgebraicGeometry.VectorBundleKZero.existsUnique_ringHom_of_tensorMultiplicative`: the
  unique ring homomorphism `K₀(Vect(X)) ⟶ R` extending a given additive and multiplicative
  assignment of an element of `R` to each finite locally free module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.FiniteLocallyFree

universe u

namespace AlgebraicGeometry.VectorBundleKZero

variable {R : Type*} [Ring R] (X : Scheme.{u}) (ch : X.Modules → R)

/-- An assignment `ℰ ↦ ch(ℰ)` of an element of a ring `R` to each `𝒪_X`-module which vanishes off
the finite locally free modules, is additive along their short exact sequences and
multiplicative on tensor products, and takes the value `1` on `𝒪_X`, extends to a ring
homomorphism on `K₀(Vect(X))`, and to exactly one. For the Chern character with values in
`∏_{i ≥ 0} A^i(X) ⊗ 𝐐` this is the ring map `ch : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X) ⊗ 𝐐`. -/
@[stacks 0FEM "the canonical ring map on `K₀(Vect(X))` that the Chern character defines, and \
  its uniqueness; additivity along short exact sequences (Tag 0F9C), multiplicativity on \
  tensor products (Tag 0F9D) and the value on `𝒪_X` are properties of the Chern character of a \
  module and are hypotheses, and `∏_{i ≥ 0} A^i(X) ⊗ 𝐐` is read as an arbitrary ring, which it \
  has no construction as in this repository"]
theorem existsUnique_ringHom_of_tensorMultiplicative
    (hzero : ∀ M : X.Modules,
      ¬ IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M → ch M = 0)
    (hadd : ∀ {E F G : X.Modules} (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0),
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
        IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F →
          IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G →
            Mono f → Epi g → (ShortComplex.mk f g w).Exact → ch F = ch E + ch G)
    (hmul : ∀ M N : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) N →
        ch (Scheme.Modules.tensorObjRingedSpace X M N) = ch M * ch N)
    (hone : ch (SheafOfModules.unit X.ringCatSheaf) = 1) :
    ∃! φ : VectorBundleKZero X →+* R,
      ∀ M : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M →
        φ (classOf X M) = ch M := by
  have hclass : ∀ M : X.Modules, liftAddHom ch hzero hadd (classOf X M) = ch M :=
    liftAddHom_classOf ch hzero hadd
  have hstep : ∀ M : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M →
      ∀ c : VectorBundleKZero X, liftAddHom ch hzero hadd (classOf X M * c) =
        liftAddHom ch hzero hadd (classOf X M) * liftAddHom ch hzero hadd c := by
    intro M hM
    refine DFunLike.congr_fun (addHom_ext
      (φ := (liftAddHom ch hzero hadd).comp (AddMonoidHom.mulLeft (classOf X M)))
      (ψ := (AddMonoidHom.mulLeft (liftAddHom ch hzero hadd (classOf X M))).comp
        (liftAddHom ch hzero hadd)) fun N hN => ?_)
    show liftAddHom ch hzero hadd (classOf X M * classOf X N) =
      liftAddHom ch hzero hadd (classOf X M) * liftAddHom ch hzero hadd (classOf X N)
    rw [classOf_mul M N hM hN, hclass, hclass, hclass, hmul M N hM hN]
  refine ⟨{ liftAddHom ch hzero hadd with
      map_one' := ?_
      map_mul' := ?_ }, fun M _ => hclass M, ?_⟩
  · rw [← classOf_unit X]
    exact (hclass _).trans hone
  · intro a b
    exact DFunLike.congr_fun (addHom_ext
      (φ := (liftAddHom ch hzero hadd).comp (AddMonoidHom.mulRight b))
      (ψ := (AddMonoidHom.mulRight (liftAddHom ch hzero hadd b)).comp
        (liftAddHom ch hzero hadd)) fun M hM => hstep M hM b) a
  · intro g hg
    refine RingHom.coe_addMonoidHom_injective (addHom_ext fun M hM => ?_)
    exact (hg M hM).trans (hclass M).symm

end AlgebraicGeometry.VectorBundleKZero

end
