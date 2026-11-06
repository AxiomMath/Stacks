module

public import StacksFrontier.Deformation.Completed.PowerSeriesPoints
public import StacksFrontier.Deformation.TangentSpace.FunctorMap

/-!
# The tangent space of a power series extension

If `f : R ⟶ S` exhibits `S` as a power series ring in `n` variables over `R`, the tangent space
of the functor prorepresented by `S` is the tangent space of the functor prorepresented by `R`
plus `n` dimensions: a `k[ε]`-point of `S` is a `k[ε]`-point of `R` together with the `n`
values of the variables in `ε k`.

## Main results

* `Deformation.finrank_tangentSpaceArtinian_of_isPowerSeriesOver`: there is `n` with
  `dim S = dim R + n` and `dim T(S) = dim T(R) + n`.

## Implementation notes

The comparison map sends a tangent vector `x : S ⟶ k[ε]` to its restriction along `f` and to the
derivation values `D_x(c_i)` at the coordinates `c_i` of
`Deformation.IsPowerSeriesOver.exists_coordinates`; it is `k`-linear because both components are,
the first by Stacks 06ST. A `k[ε]`-point sends each coordinate, which lies in the maximal ideal,
to an element with vanishing first component, so the point is recovered from the derivation
values, which gives injectivity through the uniqueness half of the universal property, and
surjectivity is the existence half.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A `k[ε]`-point takes an element of the maximal ideal to an element with vanishing first
component. -/
private theorem fst_eq_zero_of_mem_maximalIdeal {S : CompleteLocalAlgCat.{u, max v w, w} Λ k}
    (x : tangentSpaceArtinian Λ k (restrictedCoyoneda S)) {s : S} (hs : s ∈ maximalIdeal S) :
    (x.hom s).fst = 0 := by
  have h := x.residue_comm s
  rwa [(IsLocalRing.residue_eq_zero_iff s).mpr hs, map_zero] at h

/-- **The tangent space of a power series extension.** If `f : R ⟶ S` exhibits `S` as a power
series ring over `R`, there is `n` (the number of variables) with `dim S = dim R + n` for the Krull
dimensions and `dim T(S) = dim T(R) + n` for the tangent spaces. -/
public theorem finrank_tangentSpaceArtinian_of_isPowerSeriesOver [Module.Finite Λ k]
    {R S : CompleteLocalAlgCat.{u, max v w, w} Λ k} {f : R ⟶ S} (hf : IsPowerSeriesOver f) :
    ∃ n : ℕ, ringKrullDim S = ringKrullDim R + n ∧
      Module.finrank k (tangentSpaceArtinian Λ k (restrictedCoyoneda S)) =
        Module.finrank k (tangentSpaceArtinian Λ k (restrictedCoyoneda R)) + n := by
  classical
  obtain ⟨n, c, hc, hdim, huniq, hexist⟩ := hf.exists_coordinates
  refine ⟨n, hdim, ?_⟩
  let : Algebra S k := (residueHom S).toRingHom.toAlgebra
  let D := tangentSpaceDerivationsLinearEquiv S
  let ev : Fin n → (Derivation Λ S k →ₗ[k] k) := fun i =>
    { toFun := fun d => d (c i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let Φ : tangentSpaceArtinian Λ k (restrictedCoyoneda S) →ₗ[k]
      tangentSpaceArtinian Λ k (restrictedCoyoneda R) × (Fin n → k) :=
    LinearMap.prod (tangentSpaceMapArtinian f) (LinearMap.pi fun i => (ev i).comp D.toLinearMap)
  have hΦ : ∀ x, Φ x = (f ≫ x, fun i => (x.hom (c i)).snd.down) := fun x =>
    Prod.ext (tangentSpaceMapArtinian_apply f x)
      (funext fun i => tangentSpaceDerivationsLinearEquiv_apply S x (c i))
  have hbij : Function.Bijective Φ := by
    constructor
    · intro x y hxy
      rw [hΦ, hΦ] at hxy
      obtain ⟨h₁, h₂⟩ := Prod.ext_iff.mp hxy
      refine huniq x y h₁ fun i => ?_
      refine TrivSqZeroExt.ext ?_ (ULift.ext (congrFun h₂ i))
      rw [fst_eq_zero_of_mem_maximalIdeal x (hc i), fst_eq_zero_of_mem_maximalIdeal y (hc i)]
    · rintro ⟨z, v⟩
      let T := artinianToComplete.obj (artinianDualNumbers Λ k)
      let xs : Fin n → T := fun i => TrivSqZeroExt.inr (ULift.up (v i))
      have hxs : ∀ i, xs i ∈ maximalIdeal T := by
        intro i
        rw [← IsLocalRing.residue_eq_zero_iff]
        apply T.residueEquiv.injective
        rw [map_zero]
        rfl
      obtain ⟨b, hb, hbc⟩ := hexist z xs hxs
      refine ⟨b, ?_⟩
      rw [hΦ, hb]
      exact Prod.ext rfl (funext fun i => congrArg (fun t => t.snd.down) (hbc i))
  have : FiniteDimensional k (tangentSpaceArtinian Λ k (restrictedCoyoneda R)) :=
    tangentSpace_finiteDimensional R
  rw [(LinearEquiv.ofBijective Φ hbij).finrank_eq, Module.finrank_prod, Module.finrank_fin_fun]

end Deformation

end
