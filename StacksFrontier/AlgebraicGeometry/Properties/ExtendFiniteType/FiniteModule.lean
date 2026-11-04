module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.Basic

/-!
# Coherent modules on the complement of a vanishing locus come from a finite module

Let `A` be a ring, let `U ⊆ Spec A` be a quasi-compact open and let `F` be a quasi-coherent
`𝒪_U`-module of finite type. Then `F` is the restriction to `U` of the quasi-coherent module
`M̃` attached to a finite `A`-module `M`. When `A` is Noetherian and `U` is the complement of
the vanishing locus `V(I)` of an ideal `I ⊆ A`, the quasi-compactness hypothesis is automatic
and a coherent module on `U` satisfies the hypotheses; this is part (1) of Stacks 0BK0.

Three results of the library compose to give this. Stacks 0G41 (1)
(`AlgebraicGeometry.exists_finiteTypeQuasicoherent_extension`) extends `F` to a quasi-coherent
module of finite type on the whole of `Spec A`, which is quasi-compact and quasi-separated
because it is affine. A quasi-coherent module on an affine scheme is the associated sheaf of its
own global sections, by the counit `Scheme.Modules.fromTildeΓ` being an isomorphism, and those
global sections form a finite module exactly because the sheaf is of finite type
(`AlgebraicGeometry.moduleFinite_of_isFiniteType_qc`). Restricting that isomorphism back to `U`
identifies `M̃|_U` with `F`.

The quasi-compactness of the complement of `V(I)` is `PrimeSpectrum.isCompact_isOpen_iff_ideal`:
an open complement of a vanishing locus is quasi-compact as soon as the ideal is finitely
generated, which over a Noetherian ring every ideal is.

## Main results

* `AlgebraicGeometry.zeroLocusCompl`: the open complement of `V(I)` in `Spec A`.
* `AlgebraicGeometry.mem_zeroLocusCompl`: a point of that open is a prime not containing `I`.
* `AlgebraicGeometry.forall_zeroLocusCompl_toScheme`: quantifying over the points of the open
  subscheme is quantifying over the primes not containing `I`.
* `AlgebraicGeometry.isCompact_zeroLocusCompl`: over a Noetherian ring that open is
  quasi-compact.
* `AlgebraicGeometry.exists_finiteModule_tilde_restrict`: on a quasi-compact open of an affine
  scheme, a quasi-coherent module of finite type is the restriction of `M̃` for a finite `M`.
* `AlgebraicGeometry.exists_finiteModule_tilde_restrict_zeroLocusCompl`: part (1) of
  Stacks 0BK0.

## Implementation notes

`Scheme.Modules.restrictFunctor` transports the isomorphism `M̃ ≅ G` on `Spec A` to the
isomorphism of restrictions; the existential is stated with `Nonempty` because the isomorphism
is data and the statement is a proposition.

`Scheme.Modules` carries a `Category` instance of its own whose `Hom` is only definitionally the
`SheafOfModules` one, so `IsIso G.fromTildeΓ` for `G : (Spec A).Modules` is not found by
instance resolution, which works at reducible transparency. The witness is therefore supplied to
`CategoryTheory.asIso` as an explicit argument.

## References

* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Scheme.Modules

universe u

namespace AlgebraicGeometry

/-- The complement in `Spec A` of the vanishing locus `V(I)` of an ideal `I ⊆ A`, as an open
subset. -/
def zeroLocusCompl {A : CommRingCat.{u}} (I : Ideal A) : (Spec A).Opens where
  carrier := (PrimeSpectrum.zeroLocus (I : Set A))ᶜ
  is_open' := (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

/-- **A point of `Spec A` lies outside the vanishing locus of `I` exactly when it does not
contain `I`.** Both sides unfold to `¬ (I : Set A) ⊆ 𝔭`, by `PrimeSpectrum.mem_zeroLocus` and
`SetLike.le_def`. -/
@[ega "I 1.1.1" "special case"]
theorem mem_zeroLocusCompl {A : CommRingCat.{u}} (I : Ideal A) (p : Spec A) :
    p ∈ zeroLocusCompl I ↔ ¬ I ≤ p.asIdeal :=
  Iff.rfl

/-- **The points of the open subscheme `Spec A ∖ V(I)` are the primes of `A` not containing
`I`.** This is `AlgebraicGeometry.Scheme.Opens.forall_toScheme` at the open `zeroLocusCompl I`,
with membership read by `mem_zeroLocusCompl`. -/
theorem forall_zeroLocusCompl_toScheme {A : CommRingCat.{u}} (I : Ideal A)
    {P : Spec A → Prop} :
    (∀ x : (zeroLocusCompl I).toScheme, P ((zeroLocusCompl I).ι.base x)) ↔
      ∀ p : PrimeSpectrum (ToType A), ¬ I ≤ p.asIdeal → P p := by
  rw [Scheme.Opens.forall_toScheme]
  exact ⟨fun h p hp => h p ((mem_zeroLocusCompl I p).mpr hp),
    fun h p hp => h p ((mem_zeroLocusCompl I p).mp hp)⟩

/-- Over a Noetherian ring every ideal is finitely generated, so the complement of a vanishing
locus in the spectrum is quasi-compact. -/
theorem isCompact_zeroLocusCompl {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) :
    IsCompact (zeroLocusCompl I).1 :=
  (PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr ⟨I, IsNoetherian.noetherian I, rfl⟩).1

/-- On a quasi-compact open `U` of an affine scheme `Spec A`, a quasi-coherent `𝒪_U`-module of
finite type is the restriction to `U` of the sheaf `M̃` attached to a finite `A`-module `M`. -/
theorem exists_finiteModule_tilde_restrict {A : CommRingCat.{u}} (U : (Spec A).Opens)
    (hU : IsCompact U.1) (F : U.toScheme.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ M : ModuleCat.{u} A, Module.Finite A M ∧ Nonempty ((tilde M).restrict U.ι ≅ F) := by
  obtain ⟨G, hGqc, hGft, ⟨e⟩⟩ := exists_finiteTypeQuasicoherent_extension U hU F
  have := hGqc
  have := hGft
  have hiso : IsIso G.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G
  refine ⟨moduleSpecΓFunctor.obj G, moduleFinite_of_isFiniteType_qc A G, ?_⟩
  exact ⟨(Scheme.Modules.restrictFunctor U.ι).mapIso (@asIso _ _ _ _ G.fromTildeΓ hiso) ≪≫ e⟩

/-- **Stacks Project, Tag 0BK0 (1).** Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal and
let `U = Spec A \ V(I)`. A coherent `𝒪_U`-module is the restriction to `U` of the sheaf `M̃`
attached to a finite `A`-module `M`. -/
@[stacks 0BK0 "(1)", ega "I 1.5.1" "(a) => (c)"]
theorem exists_finiteModule_tilde_restrict_zeroLocusCompl {A : CommRingCat.{u}}
    [IsNoetherianRing A] (I : Ideal A) (F : (zeroLocusCompl I).toScheme.Modules)
    [F.IsCoherent] :
    ∃ M : ModuleCat.{u} A, Module.Finite A M ∧
      Nonempty ((tilde M).restrict (zeroLocusCompl I).ι ≅ F) := by
  obtain ⟨hqc, hft⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have := hqc
  have := hft
  exact exists_finiteModule_tilde_restrict (zeroLocusCompl I) (isCompact_zeroLocusCompl I) F

end AlgebraicGeometry

end
