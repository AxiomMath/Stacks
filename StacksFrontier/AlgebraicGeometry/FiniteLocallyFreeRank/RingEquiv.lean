module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Module
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteLocallyFreeOfRank

/-!
# Finite local freeness of a rank along an equivalence of base rings

Being finite locally free of rank `d` is carried along an equivalence of base rings by a
semilinear additive equivalence of modules.

## Main results

* `Module.IsFiniteLocallyFreeOfRank.of_ringEquiv`: the transport along `e : R ≃+* S`.

## Implementation notes

The hypothesis is phrased as an `AddEquiv` together with the scalar compatibility rather than as
a semilinear equivalence `M ≃ₛₗ[(e : R →+* S)] N`, because the latter's type mentions the
`RingHomInvPair` instances that `e` supplies: a caller would have to put them in scope before it
could even write the statement. This follows `Module.IsReflexive.of_ringEquiv`. The proof reads
the equivalence of base rings as an algebra structure, so that
`Module.IsFiniteLocallyFreeOfRank.baseChange` applies, and then identifies `S ⊗[R] M` with `N`.
-/

@[expose] public section

open TensorProduct

universe u v w

/-- **Being finite locally free of rank `d` is carried along an equivalence of base rings.**
Let `e : R ≃+* S` be an equivalence of rings, `M` an `R`-module and `N` an `S`-module, and let
`g : M ≃+ N` be an additive equivalence with `g (r • m) = e r • g m`. If `M` is finite locally
free of rank `d` over `R` then `N` is finite locally free of rank `d` over `S`.

`of_linearEquiv` is the special case of a single base ring. Applying the statement to `e.symm`
and `g.symm` gives the converse, so this is an equivalence.

The module is left in the base ring's universe because the finiteness of `M` needed to base
change along `e` is read off `Module.IsFiniteLocallyFreeOfRank.finite_and_projective`. -/
theorem Module.IsFiniteLocallyFreeOfRank.of_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    {M : Type u} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (e : R ≃+* S) (g : M ≃+ N) (hg : ∀ (r : R) (m : M), g (r • m) = e r • g m) {d : ℕ}
    (h : Module.IsFiniteLocallyFreeOfRank R M d) :
    Module.IsFiniteLocallyFreeOfRank S N d := by
  have : Module.Finite R M := h.finite_and_projective.1
  let : Algebra R S := e.toRingHom.toAlgebra
  have halg : ∀ r : R, algebraMap R S r = e r := fun _ => rfl
  let : Module R N := Module.compHom N e.toRingHom
  have hsmulN : ∀ (r : R) (n : N), r • n = e r • n := fun _ _ => rfl
  have : IsScalarTower R S N := by
    apply IsScalarTower.of_algebraMap_smul
    intro r n
    rw [halg, hsmulN]
  -- `g` is `R`-linear for the structure `e` transports to `N`.
  let gl : M ≃ₗ[R] N :=
    { g with map_smul' := fun r m => by rw [hsmulN]; exact hg r m }
  -- `e.symm` is `R`-linear from `S`, acting through `e`, to `R`.
  let es : S ≃ₗ[R] R :=
    { e.symm.toAddEquiv with
      map_smul' := fun r s => by
        show e.symm (r • s) = r • e.symm s
        rw [Algebra.smul_def, halg, map_mul, RingEquiv.symm_apply_apply, smul_eq_mul] }
  let chain : TensorProduct R S M ≃ₗ[R] N :=
    (TensorProduct.congr es (LinearEquiv.refl R M)).trans
      ((TensorProduct.lid R M).trans gl)
  have hchain : ∀ (r : R) (x : TensorProduct R S M), chain (r • x) = e r • chain x := by
    intro r x
    rw [map_smul, hsmulN]
  -- An `R`-linear equivalence of `S`-modules is `S`-linear because `e` is surjective.
  let G : TensorProduct R S M ≃ₗ[S] N :=
    { chain.toAddEquiv with
      map_smul' := fun s x => by
        obtain ⟨r, rfl⟩ := e.surjective s
        show chain ((e r) • x) = (e r) • chain x
        rw [← halg]
        simp only [IsScalarTower.algebraMap_smul]
        rw [hsmulN]
        exact hchain r x }
  exact Module.IsFiniteLocallyFreeOfRank.of_linearEquiv G (h.baseChange S)

end
