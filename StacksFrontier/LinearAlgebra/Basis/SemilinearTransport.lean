module

public import Mathlib.Algebra.Module.RingHom
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Transport of a basis along a semilinear additive isomorphism

A basis is an `R`-linear notion, so transporting one along an isomorphism requires the
isomorphism to be linear.  The situation this file addresses is the next one up: an additive
isomorphism `e : M ≃+ N` between a module over `R` and a module over `S` which is *semilinear*
over a ring isomorphism `ε : R ≃+* S`, in the sense that `e (r • x) = ε r • e x`.  Such an `e`
carries a basis of `M` over `R` to a basis of `N` over `S`.

The intended source of such an `e` is a presentation of `N` as a quotient: an additive
surjection `g : M ↠ N` whose kernel is exactly a submodule `p` and which is semilinear over a
ring homomorphism `ψ : R →+* S` realizes `N` as `M ⧸ p`.  That is
`Stacks.SemilinearTransport.quotientAddEquivOfSurjective`.

## Main definitions

* `Stacks.SemilinearTransport.basisOfAddEquiv`: **a basis transports along an additive
  isomorphism which is semilinear over a ring isomorphism.**
* `Stacks.SemilinearTransport.quotientAddEquivOfSurjective`: an additive surjection with kernel
  exactly `p`, semilinear over a ring homomorphism, identifies its target with `M ⧸ p`.

## Implementation notes

Both constructions go through `Module.compHom`, which turns the `S`-module `N` into an
`R`-module with `r • y = ψ r • y`; semilinearity of the map is then plain `R`-linearity for that
structure, and `Module.Basis.mapCoeffs` crosses back from `R` to `S` because the two actions
agree by construction — the hypothesis of `mapCoeffs` is `rfl` here.
-/

@[expose] public section

namespace Stacks.SemilinearTransport

variable {R S M N : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module S N]

/-- **A basis transports along an additive isomorphism which is semilinear over a ring
isomorphism.**  If `ε : R ≃+* S` and `e : M ≃+ N` satisfy `e (r • x) = ε r • e x`, then the
image under `e` of a basis of `M` over `R` is a basis of `N` over `S`. -/
noncomputable def basisOfAddEquiv {ι : Type*} (ε : R ≃+* S) (e : M ≃+ N)
    (he : ∀ (r : R) (x : M), e (r • x) = ε r • e x) (b : Module.Basis ι R M) :
    Module.Basis ι S N :=
  letI : Module R N := Module.compHom N (ε : R →+* S)
  (b.map (e.toLinearEquiv he)).mapCoeffs ε fun _ _ => rfl

/-- The `j`-th vector of the transported basis `basisOfAddEquiv ε e he b` is `e (b j)`. -/
theorem basisOfAddEquiv_apply {ι : Type*} (ε : R ≃+* S) (e : M ≃+ N)
    (he : ∀ (r : R) (x : M), e (r • x) = ε r • e x) (b : Module.Basis ι R M) (j : ι) :
    basisOfAddEquiv ε e he b j = e (b j) := by
  let : Module R N := Module.compHom N (ε : R →+* S)
  exact (b.map (e.toLinearEquiv he)).mapCoeffs_apply ε (fun _ _ => rfl) j

/-- **An additive surjection with kernel exactly `p` identifies its target with `M ⧸ p`.**  The
map is only assumed semilinear over a ring homomorphism `ψ : R →+* S`, so the identification is
stated as an isomorphism of additive groups;
`Stacks.SemilinearTransport.quotientAddEquivOfSurjective_smul` records that it is semilinear
over `ψ`. -/
noncomputable def quotientAddEquivOfSurjective (p : Submodule R M) (ψ : R →+* S) (g : M →+ N)
    (hgsmul : ∀ (r : R) (x : M), g (r • x) = ψ r • g x) (hgsurj : Function.Surjective g)
    (hgker : ∀ x : M, g x = 0 ↔ x ∈ p) :
    (M ⧸ p) ≃+ N :=
  letI : Module R N := Module.compHom N ψ
  let gl : M →ₗ[R] N := { g with map_smul' := hgsmul }
  have hle : p ≤ LinearMap.ker gl := fun x => (hgker x).mpr
  (LinearEquiv.ofBijective (p.liftQ gl hle)
    ⟨LinearMap.ker_eq_bot.mp (p.ker_liftQ_eq_bot gl hle fun x => (hgker x).mp),
      fun y => (hgsurj y).elim fun x hx => ⟨Submodule.Quotient.mk x, hx⟩⟩).toAddEquiv

/-- The identification `quotientAddEquivOfSurjective` sends the class of `x` in `M ⧸ p` to
`g x`. -/
theorem quotientAddEquivOfSurjective_mk (p : Submodule R M) (ψ : R →+* S) (g : M →+ N)
    (hgsmul : ∀ (r : R) (x : M), g (r • x) = ψ r • g x) (hgsurj : Function.Surjective g)
    (hgker : ∀ x : M, g x = 0 ↔ x ∈ p) (x : M) :
    quotientAddEquivOfSurjective p ψ g hgsmul hgsurj hgker (Submodule.Quotient.mk x) = g x :=
  rfl

/-- The identification of `Stacks.SemilinearTransport.quotientAddEquivOfSurjective` is
semilinear over `ψ` for the `R`-action on the quotient `M ⧸ p`. -/
theorem quotientAddEquivOfSurjective_smul (p : Submodule R M) (ψ : R →+* S) (g : M →+ N)
    (hgsmul : ∀ (r : R) (x : M), g (r • x) = ψ r • g x) (hgsurj : Function.Surjective g)
    (hgker : ∀ x : M, g x = 0 ↔ x ∈ p) (r : R) (y : M ⧸ p) :
    quotientAddEquivOfSurjective p ψ g hgsmul hgsurj hgker (r • y) =
      ψ r • quotientAddEquivOfSurjective p ψ g hgsmul hgsurj hgker y := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective p y
  rw [← Submodule.Quotient.mk_smul, quotientAddEquivOfSurjective_mk,
    quotientAddEquivOfSurjective_mk, hgsmul]

end Stacks.SemilinearTransport

end
