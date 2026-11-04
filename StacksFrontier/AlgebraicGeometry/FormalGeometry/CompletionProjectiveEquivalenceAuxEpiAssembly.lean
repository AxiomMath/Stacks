module

public import StacksFrontier.AlgebraicGeometry.AmpleFiniteSurjective.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxDirectSumPiece
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxEpiPresentation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxPolyPresentation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxVanishing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition

/-!
# The degreewise epimorphic presentation over the polynomial algebra

This file supplies the hypothesis `hepi` of
`Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_forall_epi_over_polyAlgebra`, and with it
part (2) of [Stacks, Tag 0897] for the associated graded algebra of `ℐ = I · 𝒪_X` — the single
input [Stacks, Tag 0884] and hence [Stacks, Tag 0885] were waiting for.

## The middle term is the tautological one

For a quasi-coherent graded `𝒪_X[x_i : i ∈ ι]`-module `N` of finite type on affine opens, the
presenting module is

  `Q = ⨁_{j ∈ J} N_j ⊗_{𝒪_X} 𝒪_X[x_i](-j)`,

`Stacks.Coherent.degreePresentation`, for a single finite set of degrees `J` produced by the
global degree bound `Stacks.Coherent.exists_finset_degrees_generating_cover`. The homogeneous
pieces of `N` themselves are the summands: **no sum of twists of an ample invertible module is
needed.** The source's `⨁_j (L^{⊗(-k_j)})^{⊕ I_j} ⊗ 𝓟(-j)` is one admissible choice, but what
the dévissage asks of `Q` is only that its twists be uniformly acyclic, and that the pieces of
`N` already have: they are coherent, so Serre vanishing applies to each of the finitely many
degrees of `J` at once (`Stacks.Coherent.exists_isZero_Hgroup_piece_tensorPowModule_on_finset`),
and the degree-`n` piece of a summand is `N_j ⊗ 𝒪_X[x_i]_{n-j}` with `𝒪_X[x_i]_{n-j}` free of
finite rank, so its twists are acyclic in *every* homogeneous degree with the same bound
(`Stacks.Coherent.isZero_Hgroup_freeGradedModuleOn_piece_tensorPowModule`).

## The four clauses

* **degreewise epimorphism** — `Stacks.Coherent.exists_finset_epi_degreePresentationHom`, whose
  quasi-compactness hypothesis comes from `AlgebraicGeometry.compactSpace_of_isProper`;
* **quasi-coherent pieces** — `Stacks.Coherent.isQuasicoherent_directSum_piece` over the
  summands, each piece being a tensor product of quasi-coherent modules
  (`Stacks.AmpleFiniteSurjective.isQuasicoherent_tensorModules` and
  `Stacks.SymmetricFree.isQuasicoherent_symmetricAlgebraPiece`);
* **finite type on affine opens** — `Stacks.Coherent.isFiniteTypeOnAffine_directSum` over
  `Stacks.Coherent.isFiniteTypeOnAffine_freeGradedModuleOn`, whose finiteness hypothesis on the
  pieces of `N` is `Stacks.Coherent.moduleFinite_piece`;
* **uniformly acyclic twists** — `Stacks.Coherent.isZero_Hgroup_directSum_piece_tensorModules`
  over `Stacks.Coherent.isZero_Hgroup_freeGradedModuleOn_piece_tensorPowModule`, fed by
  `Stacks.Coherent.exists_free_polyAlgebra_piece` and by Serre vanishing on `J`.

## Main results

* `Stacks.Coherent.exists_epi_degreePresentation_polyAlgebra` — **the presentation**, i.e. the
  hypothesis `hepi` discharged.
* `Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_isProper` — **part (2) of
  [Stacks, Tag 0897] for the associated graded algebra of `I · 𝒪_X`**, unconditionally for a
  proper morphism to the spectrum of a Noetherian ring and an ample invertible module.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0884](https://stacks.math.columbia.edu/tag/0884)
* [Stacks Project, Tag 087Z](https://stacks.math.columbia.edu/tag/087Z)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Ample Stacks.RelativeVeryAmple

universe u

namespace Stacks.Coherent

/-- **The degreewise epimorphic presentation of a quasi-coherent graded `𝒪_X[x_i]`-module of
finite type on affine opens**, with the tautological middle term
`Stacks.Coherent.degreePresentation`. This is the hypothesis `hepi` of
`Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_epi_over_polyAlgebra`; see the module
documentation for the four clauses and where each comes from. -/
public theorem exists_epi_degreePresentation_polyAlgebra (A : Type u) [CommRing A]
    [IsNoetherianRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) (ι : Type u) [Finite ι]
    (N : SheafOfModules.GradedModule (polyAlgebra X ι))
    (hqc : ∀ n : ℤ, (N.piece n).IsQuasicoherent) (hft : IsFiniteTypeOnAffine N) :
    ∃ (Q : SheafOfModules.GradedModule (polyAlgebra X ι)) (π : Q ⟶ N),
      (∀ n : ℤ, Epi (gradedAppMod π n)) ∧
      (∀ n : ℤ, (Q.piece n).IsQuasicoherent) ∧
      IsFiniteTypeOnAffine Q ∧
      ∃ d₁ : ℤ, ∀ d : ℤ, d₁ ≤ d → ∀ m : ℕ, 0 < m → ∀ n : ℤ,
        IsZero (Hgroup X.ringCatSheaf ⊤ m
          (tensorModules X (Q.piece n) (tensorPowModule X L d))) := by
  have : CompactSpace X := AlgebraicGeometry.compactSpace_of_isProper f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨J, hJ⟩ := exists_finset_epi_degreePresentationHom N hqc hft
  refine ⟨degreePresentation N J, degreePresentationHom N J, hJ, fun n => ?_, ?_, ?_⟩
  · refine isQuasicoherent_directSum_piece (degreeSummand N J) (fun k m => ?_) n
    have := hqc k.down.1
    have := Stacks.SymmetricFree.isQuasicoherent_symmetricAlgebraPiece (X := X) (I := ι)
      (m + -k.down.1)
    exact Stacks.AmpleFiniteSurjective.isQuasicoherent_tensorModules (N.piece k.down.1)
      ((polyAlgebra X ι).piece (m + -k.down.1))
  · refine isFiniteTypeOnAffine_directSum (degreeSummand N J) fun k => ?_
    have := hqc k.down.1
    exact isFiniteTypeOnAffine_freeGradedModuleOn (modPiece N k.down.1)
      (fun m => Stacks.SymmetricFree.isQuasicoherent_symmetricAlgebraPiece (X := X) (I := ι) m)
      (fun U => moduleFinite_piece
        (Stacks.SymmetricFree.forall_moduleFinite_symmetricAlgebraPiece X ι) N hft U k.down.1)
      k.down.1
  · obtain ⟨d₁, hd₁⟩ := exists_isZero_Hgroup_piece_tensorPowModule_on_finset A f
      (Stacks.SymmetricFree.forall_moduleFinite_symmetricAlgebraPiece X ι) N hqc hft L hL J
    refine ⟨(d₁ : ℤ), fun d hd m hm n => ?_⟩
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = (e : ℤ) := ⟨d.toNat, by omega⟩
    refine isZero_Hgroup_directSum_piece_tensorModules (degreeSummand N J)
      (tensorPowModule X L (e : ℤ)) m n fun k => ?_
    exact isZero_Hgroup_freeGradedModuleOn_piece_tensorPowModule X (N.piece k.down.1) L
      k.down.1 (fun m' => exists_free_polyAlgebra_piece X ι m') m (e : ℤ)
      (hd₁ e (by omega) m hm k.down.1 k.down.2) n

/-- **Part (2) of [Stacks, Tag 0897] for the associated graded algebra of `I · 𝒪_X`**, for a
proper morphism to the spectrum of a Noetherian ring and an invertible `𝒪_X`-module — with no
hypothesis beyond those.

This is `Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_forall_epi_over_polyAlgebra` with
its one hypothesis discharged by
`Stacks.Coherent.exists_epi_degreePresentation_polyAlgebra`. It is the input of [Stacks, Tag
0884] (`Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule`), and therefore
the input of [Stacks, Tag 0885]. -/
public theorem hasAssociatedGradedTwistVanishing_of_isProper (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (L : X.Modules) [IsInvertibleModule X L] :
    HasAssociatedGradedTwistVanishing A I f L :=
  hasAssociatedGradedTwistVanishing_of_forall_epi_over_polyAlgebra A I f L
    fun ι _ hL N hqc hft _ _ =>
      exists_epi_degreePresentation_polyAlgebra A f L hL ι N hqc hft

end Stacks.Coherent

end
