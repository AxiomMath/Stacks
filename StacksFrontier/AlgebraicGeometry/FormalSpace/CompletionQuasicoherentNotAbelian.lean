module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionQuasicoherentModules
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceLocalTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpaceNonAbelianQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# The quasi-coherent modules on a Noetherian affine formal algebraic space need not be abelian

Stacks, Examples, Section 0ALF considers `X = Spf(ℤ_p)`, the completion of `Spec ℤ_p` along `(p)`,
identifies the quasi-coherent modules on (the category fibred in groupoids of) `X` with the
`p`-adically complete abelian groups, and concludes from Stacks 07JR that they do not form an
abelian category (Stacks 0ALG). Formal Spaces, Remark 0DEM, records the moral: even for a
Noetherian affine formal algebraic space, whose structure sheaf is well behaved, the natural
category of quasi-coherent modules is in general not abelian.

The identification holds for the completion of any affine scheme `Spec A` along a finitely
generated ideal `I` (`AlgebraicGeometry.FormalSpace.quasicoherentModulesCompletionEquiv`), and the
argument of Stacks 07JR applies to every Noetherian domain `A` complete for a principal ideal
`(π)` with `π` neither zero nor a unit. So the conclusion holds for every such `Spf(A)`, which
is the generality behind the source's "almost any Noetherian affine formal algebraic space".

## Main results

* `AlgebraicGeometry.FormalSpace.not_nonempty_abelian_quasicoherentModules_completionAlongIdeal`:
  **Stacks 0DEM.** For a Noetherian domain `A`, complete for `(π)` with `π ≠ 0` not a unit, the
  completion of `Spec A` along `(π)` — that is, `Spf(A)` — is a Noetherian affine formal
  algebraic space whose quasi-coherent modules do not form an abelian category.
* `AlgebraicGeometry.FormalSpace.not_nonempty_abelian_quasicoherentModules_padicCompletion`:
  the source's example, `Spf(ℤ_p)` over `Spec ℤ`, for every prime `p`.
* `AlgebraicGeometry.FormalSpace.exists_isNoetherian_not_nonempty_abelian_quasicoherentModules`:
  **Stacks 0ALG.** There is a Noetherian affine formal algebraic space whose quasi-coherent
  modules do not form an abelian category.

## Implementation notes

Non-abelianness is `¬ Nonempty (Abelian _)`: no abelian structure on the category exists at all,
whatever preadditive structure it is given. It is carried from the complete modules
(`Stacks.Examples.not_abelian_iAdicallyCompleteModuleCat_of_principal`, Stacks 07JR) along the
equivalence by `CategoryTheory.not_nonempty_abelian_of_equivalence`.

The category of quasi-coherent modules is `AlgebraicGeometry.FibredSite.quasicoherentModules`,
the category of Stacks 06WG, on the category fibred in groupoids of the sheaf of sets
`colim Spec(A ⧸ πⁿ⁺¹)` (Stacks 0049, as in Stacks 0430), with modules in the universe of the
schemes of the site.

## References

* [Stacks Project, Tag 0DEM](https://stacks.math.columbia.edu/tag/0DEM)
* [Stacks Project, Tag 0ALF](https://stacks.math.columbia.edu/tag/0ALF)
* [Stacks Project, Tag 0ALG](https://stacks.math.columbia.edu/tag/0ALG)
* [Stacks Project, Tag 07JR](https://stacks.math.columbia.edu/tag/07JR)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormalSpace

/-- **Stacks 0DEM.** Let `A` be a Noetherian domain which is complete for a principal ideal
`I = (π)` with `π` neither zero nor a unit, and let `X = Spf(A)` be the completion of `Spec A`
along `V(I)`, over any base scheme `S` of any big fppf site. Then `X` is a Noetherian affine
formal algebraic space, and the category of quasi-coherent modules on `X` (Stacks 06WG) is not
abelian: it admits no abelian structure at all.

Formal Spaces, Remark 0DEM, says that for almost any Noetherian affine formal algebraic space the
natural category of quasi-coherent modules is not abelian, referring to Examples, Section 0ALF;
the content of that section is the identification of these modules with the complete
`A`-modules (`AlgebraicGeometry.FormalSpace.quasicoherentModulesCompletionEquiv`) together with
the non-abelianness of the latter (Stacks 07JR), and this statement is that content for every
such `A`, of which the section's `ℤ_p` is one. -/
@[stacks 0DEM "the content of Examples, Section 0ALF: for every Noetherian domain `A` complete \
for a principal ideal `(π)` with `π ≠ 0` not a unit, `Spf(A)` is a Noetherian affine formal \
algebraic space whose quasi-coherent modules do not form an abelian category"]
theorem not_nonempty_abelian_quasicoherentModules_completionAlongIdeal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {A : Type u} [CommRing A]
    [IsNoetherianRing A] [NoZeroDivisors A] (f : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (I : Ideal A) (hAc : IsAdicComplete I A) (π : A)
    (hIπ : I = Ideal.span {π}) (hπ : π ≠ 0) (hπu : ¬ IsUnit π) :
    IsAffineFormalAlgebraicSpace B S hS (completionAlongIdeal B S hS f hA I) ∧
      IsNoetherian B S hS (completionAlongIdeal B S hS f hA I) ∧
      ¬ Nonempty (Abelian (FibredSite.quasicoherentModules.{u, u + 1, u + 1, u} B S hS
        (completionFibred B S hS f hA I).p
        (isFiberedInGroupoids_completionFibred B S hS f hA I))) :=
  ⟨isAffineFormalAlgebraicSpace_completionAlongIdeal B S hS f hA I,
    isNoetherian_completionAlongIdeal B S hS f hA I,
    not_nonempty_abelian_of_equivalence
      (quasicoherentModulesCompletionEquiv B S hS f hA I (IsNoetherian.noetherian I))
      (Stacks.Examples.not_abelian_iAdicallyCompleteModuleCat_of_principal A I hAc π hIπ hπ hπu
        A (LinearEquiv.refl A A))⟩

/-! ### The example of the source: `Spf(ℤ_p)` -/

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- `ℤ_p` is a Noetherian ring, in any universe. -/
theorem isNoetherianRing_uliftPadicInt : IsNoetherianRing (ULift.{u} ℤ_[p]) :=
  isNoetherianRing_of_surjective ℤ_[p] (ULift.{u} ℤ_[p])
    (ULift.ringEquiv.{0, u}.symm : ℤ_[p] ≃+* ULift.{u} ℤ_[p]).toRingHom
    (ULift.ringEquiv.symm).surjective

/-- `ℤ_p` is `p`-adically complete, in any universe. -/
theorem isAdicComplete_uliftPadicInt :
    IsAdicComplete (Ideal.span {(p : ULift.{u} ℤ_[p])}) (ULift.{u} ℤ_[p]) := by
  let e : ℤ_[p] ≃+* ULift.{u} ℤ_[p] := ULift.ringEquiv.symm
  have hP : IsAdicComplete (Ideal.span {(p : ℤ_[p])}) ℤ_[p] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  have hmap : (Ideal.span {(p : ℤ_[p])}).map e = Ideal.span {(p : ULift.{u} ℤ_[p])} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [← hmap]
  exact (IsAdicComplete.congr_ringEquiv _ e).mpr hP

/-- `p` is a non-zero non-unit of `ℤ_p`, in any universe. -/
theorem natCast_ne_zero_and_not_isUnit_uliftPadicInt :
    (p : ULift.{u} ℤ_[p]) ≠ 0 ∧ ¬ IsUnit (p : ULift.{u} ℤ_[p]) := by
  let e : ULift.{u} ℤ_[p] ≃+* ℤ_[p] := ULift.ringEquiv
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : ((p : ℕ) : ℤ_[p]) = 0 := by rw [← map_natCast e, h, map_zero]
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h')
  · exact PadicInt.p_nonunit (by simpa using h.map e)

/-- **`Spf(ℤ_p)`**: the completion of `Spec ℤ_p` along `(p)`, over `Spec ℤ`, in a big fppf site
containing both. -/
abbrev padicCompletion (B : BigFppfSite.{u}) (hZ : B.Contains (Spec (.of (ULift.{u} ℤ))))
    (hZp : B.Contains (Spec (.of (ULift.{u} ℤ_[p])))) :
    FppfSheaf B (Spec (.of (ULift.{u} ℤ))) hZ :=
  completionAlongIdeal B (Spec (.of (ULift.{u} ℤ))) hZ (specULiftZIsTerminal.from _) hZp
    (Ideal.span {(p : ULift.{u} ℤ_[p])})

/-- **Stacks 0ALG, the source's example.** For a prime `p`, the formal spectrum
`X = Spf(ℤ_p)` over `Spec ℤ` is a Noetherian affine formal algebraic space whose category of
quasi-coherent modules (Stacks 06WG) admits no abelian structure: by Examples, Section 0ALF, it
is the category of `p`-adically complete abelian groups, which is not abelian (Stacks 07JR). -/
@[stacks 0ALG "the source's example `Spf(ℤ_p)`, for every prime `p`"]
theorem not_nonempty_abelian_quasicoherentModules_padicCompletion (B : BigFppfSite.{u})
    (hZ : B.Contains (Spec (.of (ULift.{u} ℤ)))) (hZp : B.Contains (Spec (.of (ULift.{u} ℤ_[p])))) :
    IsAffineFormalAlgebraicSpace B _ hZ (padicCompletion p B hZ hZp) ∧
      IsNoetherian B _ hZ (padicCompletion p B hZ hZp) ∧
      ¬ Nonempty (Abelian (FibredSite.quasicoherentModules.{u, u + 1, u + 1, u} B _ hZ
        (completionFibred B _ hZ (specULiftZIsTerminal.from _) hZp
          (Ideal.span {(p : ULift.{u} ℤ_[p])})).p
        (isFiberedInGroupoids_completionFibred B _ hZ _ hZp _))) :=
  let := isNoetherianRing_uliftPadicInt.{u} p
  not_nonempty_abelian_quasicoherentModules_completionAlongIdeal B _ hZ _ hZp _
    (isAdicComplete_uliftPadicInt.{u} p) _ rfl
    (natCast_ne_zero_and_not_isUnit_uliftPadicInt.{u} p).1
    (natCast_ne_zero_and_not_isUnit_uliftPadicInt.{u} p).2

end Padic

/-- **Stacks 0ALG.** The category of quasi-coherent modules on a formal algebraic space is not
abelian in general, even for a Noetherian affine formal algebraic space: there is a big fppf
site with a base scheme and a Noetherian affine formal algebraic space `X` over it — `Spf(ℤ_2)`
over `Spec ℤ` — whose category of quasi-coherent modules (Stacks 06WG, on the category fibred in
groupoids of `X`) admits no abelian structure. -/
@[stacks 0ALG]
theorem exists_isNoetherian_not_nonempty_abelian_quasicoherentModules :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS),
      IsAffineFormalAlgebraicSpace B S hS X ∧ IsNoetherian B S hS X ∧
      ¬ Nonempty (Abelian (FibredSite.quasicoherentModules.{u, u + 1, u + 1, u} B S hS
        (presheafOfGroupoids (X.obj ⋙ typeToGrpd)).p
        (isFiberedInGroupoids_presheafOfGroupoids _))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing
    ({Spec (.of (ULift.{u} ℤ)), Spec (.of (ULift.{u} ℤ_[2]))} : Set Scheme.{u})
  have hZ : B.Contains (Spec (.of (ULift.{u} ℤ))) := hB _ (Set.mem_insert _ _)
  have hZp : B.Contains (Spec (.of (ULift.{u} ℤ_[2]))) :=
    hB _ (Set.mem_insert_of_mem _ rfl)
  exact ⟨B, _, hZ, padicCompletion 2 B hZ hZp,
    not_nonempty_abelian_quasicoherentModules_padicCompletion 2 B hZ hZp⟩

end AlgebraicGeometry.FormalSpace

end
