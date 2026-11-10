module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import StacksFrontier.AlgebraicGeometry.Flatness.FinitelyPresented.FreeMapGenericFibreInjectivity

/-!
# A surjection onto a module free of rank `p` at every generic fibre point is an isomorphism

Let `R → S` be a flat ring map of finite presentation with geometrically integral fibres, let `N`
be a finite `S`-module and let `alpha : S^{⊕ p} → N` be **surjective**. For a prime `r` of `R`
write `𝔭_r = rS` for the generic point of the fibre over `r`. If the localization `N_{𝔭_r}` is
free of rank `p` over `S_{𝔭_r}` for *every* prime `r` of `R`, then `alpha` is bijective, so `N`
is free of rank `p`.

This is the engine of the source's proof of the first assertion of [Stacks, Tag 05MS]: there a
surjection `𝒪_U^{⊕ p} → ℱ_U` on an affine open `U` of a base change is produced from a free stalk
at one generic fibre point, and the freeness of the stalk at *all* of them forces it to be an
isomorphism. The two hypotheses that
`Module.bijective_of_forall_flat_localizedModule_genericFibre` — Stacks 05IA run at every prime
of the base — asks for are exactly what a free localization of rank `p` supplies: the map becomes
bijective over the residue field `κ(𝔭_r)` because both sides then have dimension `p` there, and
`N_{𝔭_r}` is flat over `R` because it is free over `S_{𝔭_r}`, which is flat over `R`.

## Main results

* `Module.finrank_fiber_of_basis_localizedModule`: the fibre of `N` at a prime whose localization
  is free of rank `p` has dimension `p` over the residue field of that prime.
* `Module.bijective_rTensor_residueField_of_basis_localizedModule`: a surjection from `S^{⊕ p}`
  onto such an `N` becomes bijective over that residue field.
* `Module.flat_localizedModule_of_basis_localizedModule`: such a localization of `N` is flat over
  the base.
* `Module.bijective_of_forall_basis_localizedModule_genericFibre`: the engine — the surjection is
  bijective.
* `Module.nonempty_basis_of_forall_basis_localizedModule_genericFibre`: the same
  conclusion read as a basis of `N` over `S` indexed by `Fin p`.

## Implementation notes

The dimension count over `κ(𝔭)` is `Module.rankAtStalk_eq` with its flatness hypothesis replaced
by a basis of the localization: the chain
`κ(𝔭) ⊗_{S_𝔭} (S_𝔭 ⊗_S N) ≅ κ(𝔭) ⊗_S N` of
`TensorProduct.AlgebraTensorModule.cancelBaseChange` transports the base change of a basis of
`N_𝔭` to a basis of the fibre, so no `StrongRankCondition` beyond that of a field is needed, and
`N` itself is never assumed flat over `S` — which matters, since the module of Situation
[Stacks, Tag 05MP] is of finite type only.

Bijectivity over the residue field is Orzech's theorem
(`OrzechProperty.bijective_of_surjective_of_finrank_le`) applied over the field `κ(𝔭)`: the
surjection has source and target of the same finite dimension there. It is proved for
`LinearMap.lTensor`, the orientation in which `Ideal.Fiber` is stated, and carried to
`LinearMap.rTensor`, the orientation Stacks 05IA is stated in, by
`LinearMap.lTensor_inj_iff_rTensor_inj` and `LinearMap.lTensor_surj_iff_rTensor_surj`.

Flatness of `N_𝔭` over `R` factors through `S` rather than through `S_𝔭`: there is no `Algebra R
S_𝔭` instance, while `Module.Flat.trans S (Localization.AtPrime 𝔭) _` and
`Module.Flat.trans R S _` compose without one.

## References

* [Stacks Project, Tag 05MS](https://stacks.math.columbia.edu/tag/05MS)
* [Stacks Project, Tag 05IA](https://stacks.math.columbia.edu/tag/05IA)
-/

@[expose] public section

open AlgebraicGeometry CommRingCat
open scoped TensorProduct

universe u w

namespace Module

/-- **The fibre of a module at a prime where it is free of rank `p` has dimension `p`.** If the
localization of `N` at a prime `𝔭` of `S` has a basis indexed by `Fin p` over `S_𝔭`, then the
fibre `κ(𝔭) ⊗_S N` is a `κ(𝔭)`-vector space of dimension `p`.

This is `Module.rankAtStalk_eq` with its hypothesis that `N` be flat and finite over `S`
replaced by the basis, which is all that the proof uses. -/
theorem finrank_fiber_of_basis_localizedModule {S : Type u} [CommRing S] (q : Ideal S)
    [q.IsPrime] (N : Type w) [AddCommGroup N] [Module S N] (p : ℕ)
    (b : Module.Basis (Fin p) (Localization.AtPrime q) (LocalizedModule q.primeCompl N)) :
    Module.finrank q.ResidueField (q.Fiber N) = p := by
  classical
  have e : q.ResidueField ⊗[Localization.AtPrime q]
      (Localization.AtPrime q ⊗[S] N) ≃ₗ[q.ResidueField] q.ResidueField ⊗[S] N :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange _ _ _ _ _
  have hb : Module.Basis (Fin p) q.ResidueField (q.Fiber N) :=
    ((b.map (LocalizedModule.equivTensorProduct q.primeCompl N)).baseChange
      q.ResidueField).map e
  simpa using Module.finrank_eq_card_basis hb

/-- **A surjection from `S^{⊕ p}` onto a module free of rank `p` at a prime becomes bijective
over the residue field of that prime.** Both sides of `alpha ⊗ κ(𝔭)` are `κ(𝔭)`-vector spaces of
dimension `p`, and a surjection between finite modules whose source has dimension at most that
of its target is bijective by Orzech's theorem. -/
theorem bijective_rTensor_residueField_of_basis_localizedModule {S : Type u} [CommRing S]
    (q : Ideal S) [q.IsPrime] (N : Type w) [AddCommGroup N] [Module S N] [Module.Finite S N]
    (p : ℕ) (alpha : (Fin p → S) →ₗ[S] N) (hsurj : Function.Surjective alpha)
    (b : Module.Basis (Fin p) (Localization.AtPrime q) (LocalizedModule q.primeCompl N)) :
    Function.Bijective (alpha.rTensor q.ResidueField) := by
  classical
  have hsurjb : Function.Surjective (alpha.baseChange q.ResidueField) := by
    have h := alpha.lTensor_surjective q.ResidueField hsurj
    rwa [← LinearMap.baseChange_eq_lTensor] at h
  have hbsrc : Module.Basis (Fin p) q.ResidueField (q.ResidueField ⊗[S] (Fin p → S)) :=
    (Pi.basisFun S (Fin p)).baseChange q.ResidueField
  have : Module.Finite q.ResidueField (q.ResidueField ⊗[S] (Fin p → S)) :=
    Module.Finite.of_basis hbsrc
  have : Module.Finite q.ResidueField (q.ResidueField ⊗[S] N) :=
    Module.Finite.of_surjective (alpha.baseChange q.ResidueField) hsurjb
  have hsrc : Module.finrank q.ResidueField (q.ResidueField ⊗[S] (Fin p → S)) = p := by
    simpa using Module.finrank_eq_card_basis hbsrc
  have htgt : Module.finrank q.ResidueField (q.ResidueField ⊗[S] N) = p :=
    finrank_fiber_of_basis_localizedModule q N p b
  have hbij : Function.Bijective (alpha.baseChange q.ResidueField) :=
    OrzechProperty.bijective_of_surjective_of_finrank_le _ hsurjb (by rw [hsrc, htgt])
  rw [LinearMap.baseChange_eq_lTensor] at hbij
  exact ⟨(LinearMap.lTensor_inj_iff_rTensor_inj _ _).mp hbij.1,
    (LinearMap.lTensor_surj_iff_rTensor_surj _ _).mp hbij.2⟩

/-- **A localization which is free over the localized ring is flat over the base.** If `N_𝔭` has
a basis over `S_𝔭` and `S` is flat over `R`, then `N_𝔭` is flat over `R`: it is flat over `S`
because `S_𝔭` is, and `S` is flat over `R`. -/
theorem flat_localizedModule_of_basis_localizedModule (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (q : Ideal S) [q.IsPrime] (N : Type w) [AddCommGroup N]
    [Module S N] [Module R N] [IsScalarTower R S N] (p : ℕ)
    (b : Module.Basis (Fin p) (Localization.AtPrime q) (LocalizedModule q.primeCompl N)) :
    Module.Flat R (LocalizedModule q.primeCompl N) := by
  have : Module.Free (Localization.AtPrime q) (LocalizedModule q.primeCompl N) :=
    Module.Free.of_basis b
  have : Module.Flat S (LocalizedModule q.primeCompl N) :=
    Module.Flat.trans S (Localization.AtPrime q) _
  exact Module.Flat.trans R S _

/-- **The engine of the first assertion of [Stacks, Tag 05MS].** Let `R → S` be flat of finite
presentation with geometrically integral fibres, let `N` be a finite `S`-module and let
`alpha : S^{⊕ p} → N` be surjective. If for every prime `r` of `R` the localization of `N` at the
generic point `rS` of the fibre over `r` is free of rank `p`, then `alpha` is bijective.

The two hypotheses of `Module.bijective_of_forall_flat_localizedModule_genericFibre` — Stacks
05IA at every prime of `R` — are supplied by
`Module.bijective_rTensor_residueField_of_basis_localizedModule` and
`Module.flat_localizedModule_of_basis_localizedModule`. -/
theorem bijective_of_forall_basis_localizedModule_genericFibre (R S : Type u) [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N] (p : ℕ) (alpha : (Fin p → S) →ₗ[S] N)
    (hbasis : ∀ (r : Ideal R) (_ : r.IsPrime),
      letI := Ideal.isPrime_map_of_geometricallyIntegral R S r
      Nonempty (Module.Basis (Fin p) (Localization.AtPrime (Ideal.map (algebraMap R S) r))
        (LocalizedModule (Ideal.map (algebraMap R S) r).primeCompl N)))
    (hsurj : Function.Surjective alpha) :
    Function.Bijective alpha := by
  refine Module.bijective_of_forall_flat_localizedModule_genericFibre R S N p alpha
    (fun r hr => ?_) (fun r hr => ?_) hsurj
  all_goals
    have := hr
    have := Ideal.isPrime_map_of_geometricallyIntegral R S r
  · exact (bijective_rTensor_residueField_of_basis_localizedModule _ N p alpha hsurj
      (hbasis r hr).some).1
  · exact flat_localizedModule_of_basis_localizedModule R S _ N p (hbasis r hr).some

/-- **The engine of the first assertion of [Stacks, Tag 05MS], read as freeness.** Under the
hypotheses of `Module.bijective_of_forall_basis_localizedModule_genericFibre` the module `N` is
free of rank `p` over `S`, the surjection being an isomorphism. -/
theorem nonempty_basis_of_forall_basis_localizedModule_genericFibre (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N] (p : ℕ) (alpha : (Fin p → S) →ₗ[S] N)
    (hbasis : ∀ (r : Ideal R) (_ : r.IsPrime),
      letI := Ideal.isPrime_map_of_geometricallyIntegral R S r
      Nonempty (Module.Basis (Fin p) (Localization.AtPrime (Ideal.map (algebraMap R S) r))
        (LocalizedModule (Ideal.map (algebraMap R S) r).primeCompl N)))
    (hsurj : Function.Surjective alpha) :
    Nonempty (Module.Basis (Fin p) S N) :=
  ⟨(Pi.basisFun S (Fin p)).map (LinearEquiv.ofBijective alpha
    (bijective_of_forall_basis_localizedModule_genericFibre R S N p alpha hbasis hsurj))⟩

end Module

end
