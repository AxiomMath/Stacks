module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# A base change of a residually trivial extension is residually trivial at a point

Let `E → E'` be a ring map, let `p'` be a prime of `E'` contracting to a prime `p` of `E`, and
suppose the residue field extension `κ(p) → κ(p')` is bijective. Let `E → F` be any ring map and
let `q` be a prime of `F` contracting to `p`. Then the tensor product `F ⊗[E] E'` carries a prime
`Q` lying over `q` and over `p'` whose residue field extension `κ(q) → κ(Q)` is again bijective.

Nothing is asked of `E → E'`. The statement is about the fibre: the fibre of
`Spec (F ⊗[E] E') ⟶ Spec F` over `q` is `(E' ⊗[E] κ(p)) ⊗_{κ(p)} κ(q)`, and the prime `p'` of
`E'` with `κ(p') = κ(p)` is a `κ(p)`-point of `Spec (E' ⊗[E] κ(p))`, which base-changes to a
`κ(q)`-point of the fibre. A `κ(q)`-point of the fibre is exactly a prime `Q` over `q` with
`κ(Q) = κ(q)`.

Read with `E → E'` étale this says that an **elementary** étale extension stays elementary
after an arbitrary base change, at the point the given one determines.

## Main results

* `Ideal.ResidueField.map_bijective_of_lift`: the residue field extension of a prime `Q` over a
  prime `q` is bijective as soon as the ambient ring admits a map to `κ(q)` with kernel exactly
  `Q` restricting to the canonical map on `F`.
* `Ideal.exists_isPrime_comap_eq_and_residueField_map_bijective_tensorProduct`: the statement
  above.

## Implementation notes

The `κ(q)`-point of the fibre is built directly, as a ring map `ψ : F ⊗[E] E' → κ(q)`, rather
than by forming the fibre ring: `ψ` is `Algebra.TensorProduct.lift` of the canonical
`F → κ(q)` and of `E' → κ(p') ≅ κ(p) → κ(q)`, the inverse of `κ(p) → κ(p')` being available
because that map is assumed bijective. Those two agree on `E` by
`Ideal.ResidueField.map_algebraMap` on each side, which is what makes the lift exist. The prime
is then `Q = ker ψ`, prime because `κ(q)` is a field, and its two contractions are computed by
`RingHom.comap_ker` from the two composites of `ψ` with the inclusions.

Bijectivity of `κ(q) → κ(Q)` is `Ideal.ResidueField.map_bijective_of_lift`, whose proof is the
only place the residue fields are manipulated. Since `ker ψ = Q`, `ψ` carries the complement of
`Q` to units, so Mathlib's `Ideal.ResidueField.lift` turns it into `θ : κ(Q) → κ(q)`; `θ`
composed with `κ(q) → κ(Q)` is the identity, because both sides agree on the image of `F` and a
map out of `κ(q)` is determined by that (`Ideal.ResidueField.ringHom_ext`). A retraction of a
field extension of fields makes both maps bijective, which is the conclusion. No surjectivity
of a ring map is needed anywhere, and in particular `F → F ⊗[E] E'` is not surjective on stalks,
so `RingHom.SurjectiveOnStalks.residueFieldMap_bijective` does not apply.

*What was already available, and why the prime is produced here anyway.* The existence of a
prime of the tensor product over `q` and over `p'` — the conclusion with the residue field
clause deleted — is Mathlib's `Ideal.fiberIsoOfBijectiveResidueField`, which under the same
hypothesis puts the fibre of `E' ⊗[E] F` over `p'` in bijection with the fibre of `F` over `p`.
The residue field clause is what neither it nor any of the repository's variants of the same
existence statement carries, and it is not recoverable from the prime alone: the proof below
needs to know that the prime *is* `ker ψ`. Importing the prime and identifying it with `ker ψ`
afterwards is possible, through the uniqueness clause
`Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap`, but it is longer than constructing
`ψ` and reading both clauses off it, and it would additionally have to cross the factor order,
Mathlib's statement being about `E' ⊗[E] F`.

At the level of schemes the residue field clause alone is
`AlgebraicGeometry.pullback_snd_residueFieldMap_isIso`: residual triviality is stable under base
change, at every point of the fibre product. That is the same mathematics. It is not used here
because the consumer is the ring-level statement, and transporting the scheme-level one back
would need the identification of `Spec (F ⊗[E] E')` with the fibre product of the two `Spec`s on
carriers, plus the two residue field bridges of
`StacksFrontier/AlgebraicGeometry/Morphisms/UniversalHomeomorphism/Affine/ResidueField.lean`, and
would still leave the existence of the point to be produced separately.
-/

@[expose] public section

open TensorProduct

namespace Ideal.ResidueField

/-- **A residue field extension is bijective once the extension ring maps to `κ(q)` with kernel
the prime.** Let `g : F → G` carry a prime `Q` of `G` back to a prime `q` of `F`, and suppose
there is a ring map `ψ : G → κ(q)` whose kernel is exactly `Q` and whose restriction along `g`
is the canonical map `F → κ(q)`. Then `κ(q) → κ(Q)` is bijective.

Since `ker ψ = Q`, the map `ψ` sends the complement of `Q` to units, so it descends to
`θ : κ(Q) → κ(q)`; and `θ` is a retraction of `κ(q) → κ(Q)` because the two composites agree on
the image of `F`. Both maps are then bijective, being maps of fields with a one-sided
inverse. -/
theorem map_bijective_of_lift {F G : Type*} [CommRing F] [CommRing G]
    (q : Ideal F) [q.IsPrime] (Q : Ideal G) [Q.IsPrime] (g : F →+* G) (hq : q = Q.comap g)
    (ψ : G →+* q.ResidueField) (hker : RingHom.ker ψ = Q)
    (hψ : ψ.comp g = algebraMap F q.ResidueField) :
    Function.Bijective (Ideal.ResidueField.map q Q g hq) := by
  have hunit : Q.primeCompl ≤ (IsUnit.submonoid q.ResidueField).comap ψ :=
    fun z hz => (show ψ z ≠ 0 from fun h => hz (hker ▸ h)).isUnit
  set θ : Q.ResidueField →+* q.ResidueField :=
    Ideal.ResidueField.lift Q ψ hker.ge hunit with hθdef
  have hθ : θ.comp (Ideal.ResidueField.map q Q g hq) = RingHom.id q.ResidueField := by
    refine Ideal.ResidueField.ringHom_ext (RingHom.ext fun r => ?_)
    rw [RingHom.comp_assoc]
    simp only [RingHom.coe_comp, Function.comp_apply, Ideal.ResidueField.map_algebraMap, hθdef,
      Ideal.ResidueField.lift_algebraMap, RingHom.id_apply]
    exact RingHom.congr_fun hψ r
  exact ⟨RingHom.injective _, fun y => ⟨θ y, θ.injective (RingHom.congr_fun hθ (θ y))⟩⟩

end Ideal.ResidueField

/-- **A residually trivial extension stays residually trivial after an arbitrary base change.**
Let `E → E'` be a ring map, let `p'` be a prime of `E'` contracting to a prime `p` of `E` with
bijective residue field extension `κ(p) → κ(p')`, and let `E → F` be a ring map with a prime `q`
contracting to `p`. Then `F ⊗[E] E'` has a prime `Q` contracting to `q` on the left and to `p'`
on the right, with `κ(q) → κ(Q)` bijective.

Read with `E → E'` étale, `Spec (F ⊗[E] E') ⟶ Spec F` is étale and elementary at the point `Q`:
an elementary étale neighbourhood base-changes to one. -/
theorem Ideal.exists_isPrime_comap_eq_and_residueField_map_bijective_tensorProduct
    {E E' F : Type*} [CommRing E] [CommRing E'] [CommRing F] [Algebra E E'] [Algebra E F]
    (p : Ideal E) [p.IsPrime] (p' : Ideal E') [p'.IsPrime]
    (hp' : p = p'.comap (algebraMap E E'))
    (hres : Function.Bijective (Ideal.ResidueField.map p p' (algebraMap E E') hp'))
    (q : Ideal F) [q.IsPrime] (hq : p = q.comap (algebraMap E F)) :
    ∃ (Q : Ideal (F ⊗[E] E')) (_ : Q.IsPrime)
      (hQ : q = Q.comap (algebraMap F (F ⊗[E] E'))),
      p' = Q.comap (Algebra.TensorProduct.includeRight : E' →ₐ[E] F ⊗[E] E').toRingHom ∧
        Function.Bijective (Ideal.ResidueField.map q Q (algebraMap F (F ⊗[E] E')) hQ) := by
  let : Algebra E q.ResidueField :=
    ((algebraMap F q.ResidueField).comp (algebraMap E F)).toAlgebra
  let : IsScalarTower E E q.ResidueField :=
    ⟨fun x y z => by simp [smul_eq_mul, Algebra.smul_def, map_mul, mul_assoc]⟩
  -- `κ(p) ≅ κ(p')`, and the composite `E' → κ(p') ≅ κ(p) → κ(q)`.
  let e : p.ResidueField ≃+* p'.ResidueField := RingEquiv.ofBijective _ hres
  let φ : p'.ResidueField →+* q.ResidueField :=
    (Ideal.ResidueField.map p q (algebraMap E F) hq).comp
      (e.symm : p'.ResidueField →+* p.ResidueField)
  let ψ' : E' →+* q.ResidueField := φ.comp (algebraMap E' p'.ResidueField)
  have hψ'base : ∀ x : E, ψ' (algebraMap E E' x) = algebraMap E q.ResidueField x := by
    intro x
    have h1 : e (algebraMap E p.ResidueField x) =
        algebraMap E' p'.ResidueField (algebraMap E E' x) :=
      Ideal.ResidueField.map_algebraMap p p' (algebraMap E E') hp' x
    simp only [ψ', φ, RingHom.coe_comp, Function.comp_apply, ← h1, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply]
    exact Ideal.ResidueField.map_algebraMap p q (algebraMap E F) hq x
  -- The `κ(q)`-point of the fibre, as a map out of the tensor product.
  let ψ : (F ⊗[E] E') →ₐ[E] q.ResidueField :=
    Algebra.TensorProduct.lift
      ({ toRingHom := algebraMap F q.ResidueField, commutes' := fun _ => rfl } : F →ₐ[E] _)
      ({ toRingHom := ψ', commutes' := hψ'base } : E' →ₐ[E] _)
      fun _ _ => Commute.all _ _
  have hψleft : ψ.toRingHom.comp (algebraMap F (F ⊗[E] E')) = algebraMap F q.ResidueField :=
    RingHom.ext fun z => AlgHom.congr_fun
      (Algebra.TensorProduct.lift_comp_includeLeft _ _ fun _ _ => Commute.all _ _) z
  have hψright : ψ.toRingHom.comp
      (Algebra.TensorProduct.includeRight : E' →ₐ[E] F ⊗[E] E').toRingHom = ψ' :=
    RingHom.ext fun y => AlgHom.congr_fun
      (Algebra.TensorProduct.lift_comp_includeRight _ _ fun _ _ => Commute.all _ _) y
  -- The kernel of `ψ'` is `p'`, the two maps it is composed with being injective.
  have hψ'ker : RingHom.ker ψ' = p' :=
    (RingHom.ker_comp_of_injective (algebraMap E' p'.ResidueField)
      ((Ideal.ResidueField.map p q (algebraMap E F) hq).injective.comp e.symm.injective)).trans
      p'.ker_algebraMap_residueField
  have hQprime : (RingHom.ker ψ.toRingHom).IsPrime := RingHom.ker_isPrime _
  refine ⟨RingHom.ker ψ.toRingHom, hQprime, ?_, ?_, ?_⟩
  · rw [RingHom.comap_ker, hψleft, Ideal.ker_algebraMap_residueField]
  · rw [RingHom.comap_ker, hψright, hψ'ker]
  · exact Ideal.ResidueField.map_bijective_of_lift q _ _ _ ψ.toRingHom rfl hψleft

end
