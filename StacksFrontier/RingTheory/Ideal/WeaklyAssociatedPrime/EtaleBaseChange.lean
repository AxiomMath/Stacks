module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.EtalePullback
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffinePullbackSections
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.RingEquiv
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreFiniteType

/-!
# Weakly associated primes and étale base change

Let `A → B` be an étale ring map and let `X` be an `A`-module. A prime `q` of `B` is weakly
associated to `B ⊗[A] X` exactly when its contraction to `A` is weakly associated to `X`. This
is the ring-theoretic form of Stacks tag 05FP, whose scheme-theoretic form
`AlgebraicGeometry.isWeaklyAssociatedPoint_pullback_iff_of_etale` is proved elsewhere.

The passage between the two forms is the affine dictionary. The prime `q` is a point of
`Spec B`, the étale morphism is `Spec` of `A → B`, and `B ⊗[A] X` is the module of global
sections of the pullback of the quasi-coherent module `X̃` along it. Weak association of a
point of an affine scheme to a quasi-coherent module is weak association of the corresponding
prime to the module of global sections (Stacks tag 056M), so the scheme statement specializes
to the ring statement.

## Main results

* `AlgebraicGeometry.isWeaklyAssociatedPoint_tilde_iff`: on `Spec R`, weak association of a
  point to the quasi-coherent module `M̃` of an `R`-module `M` is weak association of the
  corresponding prime to `M`.
* `Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_tensorProduct_iff_of_etale`: the
  ring-theoretic form of Stacks tag 05FP.

## Implementation notes

The affine comparison of Stacks tag 056M is stated for an affine open of an arbitrary scheme.
Applying it on `Spec A` at the affine open `⊤` leaves the prime expressed as
`IsAffineOpen.primeIdealOf`, that is as the image of the point under `(Spec A).isoSpec`; the
identification with the point itself is the transport of weak association along the ring
isomorphism `A ≃+* Γ(Spec A, ⊤)`.

The global sections of the pullback are identified with the plain tensor product by
`AlgebraicGeometry.pullbackTildeΓTensorEquiv`, so no extension-of-scalars bookkeeping is
needed at the ring level.

## References

* [Stacks Project, Tag 05FP](https://stacks.math.columbia.edu/tag/05FP)
* [Stacks Project, Tag 056M](https://stacks.math.columbia.edu/tag/056M)
-/

@[expose] public section

open CategoryTheory

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- On an affine scheme, weak association of a point to a quasi-coherent module is weak
association of the corresponding prime to the module of global sections. -/
private theorem isWeaklyAssociatedPoint_spec_iff {A : CommRingCat.{u}} (F : (Spec A).Modules)
    [F.IsQuasicoherent] (x : PrimeSpectrum A) :
    Stacks.Divisors.IsWeaklyAssociatedPoint F x ↔
      IsWeaklyAssociatedPrime A ((moduleSpecΓFunctor (R := A)).obj F) x.asIdeal := by
  let : Module A Γ(F, ⊤) := ((moduleSpecΓFunctor (R := A)).obj F).isModule
  let ρ : A ≃+* Γ(Spec A, ⊤) := (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv
  let hU := isAffineOpen_top (Spec A)
  have hp : (hU.primeIdealOf ⟨x, Set.mem_univ _⟩).asIdeal = x.asIdeal.map ρ.toRingHom := by
    rw [IsAffineOpen.primeIdealOf, hU.isoSpec_hom, Scheme.Opens.toSpecΓ_top]
    change ((Spec A).isoSpec.hom x).asIdeal = x.asIdeal.map ρ.toRingHom
    rw [Scheme.isoSpec_Spec_hom]
    exact Ideal.comap_symm (f := ρ)
  rw [← isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint F ⊤ hU x (Set.mem_univ _), hp]
  exact (isWeaklyAssociatedPrime_iff_of_semilinearEquiv
    ρ (AddEquiv.refl _) (fun _ _ => rfl) x.asIdeal).symm

/-- On `Spec R`, weak association of a point to the quasi-coherent module of an `R`-module `M`
is weak association of the corresponding prime to `M`. -/
public theorem isWeaklyAssociatedPoint_tilde_iff {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (x : PrimeSpectrum R) :
    Stacks.Divisors.IsWeaklyAssociatedPoint (tilde M) x ↔
      IsWeaklyAssociatedPrime R M x.asIdeal := by
  rw [isWeaklyAssociatedPoint_spec_iff]
  exact (LinearEquiv.isWeaklyAssociatedPrime_iff
    ((tilde.toTildeΓNatIso (R := R)).app M).toLinearEquiv x.asIdeal).symm

end AlgebraicGeometry

namespace Stacks.WeaklyAssociatedPrimes

open _root_.AlgebraicGeometry

/-- **Stacks Project, Tag 05FP, ring-theoretic form.** For an étale ring map `A → B` and an
`A`-module `X`, a prime of `B` is weakly associated to `B ⊗[A] X` if and only if its
contraction to `A` is weakly associated to `X`. -/
public theorem isWeaklyAssociatedPrime_tensorProduct_iff_of_etale
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    {X : Type u} [AddCommGroup X] [Module A X] (q : Ideal B) [q.IsPrime] :
    IsWeaklyAssociatedPrime B (B ⊗[A] X) q ↔
      IsWeaklyAssociatedPrime A X (q.comap (algebraMap A B)) := by
  let f : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  have : Etale (Spec.map f) := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  let M : ModuleCat.{u} (CommRingCat.of A) := ModuleCat.of A X
  let G : (Spec (CommRingCat.of B)).Modules :=
    (Scheme.Modules.pullback (Spec.map f)).obj (tilde M)
  have : G.IsQuasicoherent := by
    have h : ((tilde.functor (CommRingCat.of B)).obj
        ((ModuleCat.extendScalars f.hom).obj M)).IsQuasicoherent := inferInstance
    exact (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of B)).ringCatSheaf).prop_of_iso
      ((pullbackTildeIso (CommRingCat.of A) (CommRingCat.of B) f).app M).symm h
  let qp : PrimeSpectrum B := ⟨q, inferInstance⟩
  calc IsWeaklyAssociatedPrime B (B ⊗[A] X) q
      ↔ IsWeaklyAssociatedPrime B ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj G) q :=
        (LinearEquiv.isWeaklyAssociatedPrime_iff (pullbackTildeΓTensorEquiv (S := B) M) q).symm
    _ ↔ Stacks.Divisors.IsWeaklyAssociatedPoint G qp :=
        (isWeaklyAssociatedPoint_spec_iff G qp).symm
    _ ↔ Stacks.Divisors.IsWeaklyAssociatedPoint (tilde M) ((Spec.map f).base qp) :=
        isWeaklyAssociatedPoint_pullback_iff_of_etale (Spec.map f) (tilde M) qp
    _ ↔ IsWeaklyAssociatedPrime A X (q.comap (algebraMap A B)) :=
        isWeaklyAssociatedPoint_tilde_iff M ((Spec.map f).base qp)

end Stacks.WeaklyAssociatedPrimes

end
