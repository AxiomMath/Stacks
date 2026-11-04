module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CanonicalExtensionUniqueness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CanonicalExtensionCdOneDepthThree
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SequentialProIsomorphismSymm

/-!
# Algebraization in cohomological dimension one

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`. [Stacks, Tag 0EJJ] asserts that an object `(ℱₙ)` of
`Coh(U, I𝒪_U)` satisfying the `(2, 3)`-inequalities extends to `X` when `A` has a dualizing complex
and `cd(A, I) = 1`. The source's proof replaces `(ℱₙ)` by the object `(ℋₙ)` of [Stacks, Tag 0EJG],
to which it maps with kernel and cokernel annihilated by a power of `I` and which is
pro-isomorphic to a system `(ℱ''ₙ)` of depth at least three along `δ^Y_Z`; then `(ℋₙ)` extends
canonically by [Stacks, Tag 0EJI], hence extends by [Stacks, Tag 0EIR], and `(ℱₙ)` extends by
[Stacks, Tag 0EIU].

This file performs the last three steps.

## Main results

* `Stacks.Algebraization.extendsToX_of_annihilated_of_canonicallyExtends` — Tags 0EIR and 0EIU
  combined: a morphism with annihilated kernel and cokernel to a canonically extending object.
* `Stacks.Algebraization.extendsToX_of_annihilated_of_proIso_depthThree` — the same with the
  canonical extension supplied by [Stacks, Tag 0EJI].

## Implementation notes

`Stacks.Algebraization.ExtendsToX` is stated along the kernel ideal sheaf of `Y ⟶ X` pulled back to
`U`, which equals `Stacks.Algebraization.idealOnOpen` but not definitionally. The transport of 0EIU
across that equation is done with the ideal sheaf a variable, by eliminating the equation, as in
`ExtensionCohomologicalDimensionOne.lean`: on the concrete ideal sheaves the kernel would unfold
`Scheme.ΓSpecIso`.

## References

* [Stacks Project, Tag 0EJJ](https://stacks.math.columbia.edu/tag/0EJJ)
* [Stacks Project, Tag 0EJG](https://stacks.math.columbia.edu/tag/0EJG)
* [Stacks Project, Tag 0EJI](https://stacks.math.columbia.edu/tag/0EJI)
* [Stacks Project, Tag 0EIR](https://stacks.math.columbia.edu/tag/0EIR)
* [Stacks Project, Tag 0EIU](https://stacks.math.columbia.edu/tag/0EIU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})

/-- An object of `Coh(U, I𝒪_U)` extends to `X` as soon as it admits a morphism, with kernel and
cokernel annihilated by a power of `I`, to an object which canonically extends to `X`. -/
theorem extendsToX_of_annihilated_of_canonicallyExtends
    (F H : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (α : F.obj ⟶ H.obj)
    (hα : IsKernelCokernelAnnihilatedByPower (idealOnOpen S) α)
    (hH : CanonicallyExtends S H) :
    ExtendsToX S (toKerSystem S F) := by
  have key : ∀ (J : S.U.toScheme.IdealSheafData) (_ : S.Yι.ker.comap S.U.ι = J)
      (F H : Stacks.Coherent.CoherentAdicSystems J) (α : F.obj ⟶ H.obj),
      IsKernelCokernelAnnihilatedByPower J α →
      (∃ G : Stacks.Coherent.CoherentAdicSystems S.Yι.ker,
        Nonempty (G.obj ⋙ Scheme.Modules.restrictFunctor S.U.ι ≅ H.obj)) →
      ∃ G : Stacks.Coherent.CoherentAdicSystems S.Yι.ker,
        Nonempty (G.obj ⋙ Scheme.Modules.restrictFunctor S.U.ι ≅ F.obj) := by
    intro J hJ F H α hα hH
    subst hJ
    exact (extendsToX_iff_extendsToX_of_isKernelCokernelAnnihilatedByPower S
      (ObjectProperty.homMk α) hα).2 hH
  have hextH : ExtendsToX S (toKerSystem S H) :=
    extendsToX_of_canonicallyExtends S H (tildeGlobalSectionsPullbackIso S H) hH
  exact exists_restrictionIso_congr S (toKerSystem_obj S F).symm
    (key _ (ker_Yι_comap_eq_idealOnOpen S) F H α hα
      (exists_restrictionIso_congr S (toKerSystem_obj S H) hextH))

/-- **The extension step of [Stacks, Tag 0EJJ].** In Situation 0EHC with `A` having a dualizing
complex and `cd(A, I) = 1`, an object `(ℱₙ)` of `Coh(U, I𝒪_U)` extends to `X` as soon as it maps,
with kernel and cokernel annihilated by a power of `I`, to an object `(ℋₙ)` pro-isomorphic to an
inverse system `(ℱ''ₙ)` of coherent `𝒪_U`-modules with `depth(ℱ''_{n,y}) + δ^Y_Z(y) ≥ 3` on
`U ∩ Y`: by [Stacks, Tag 0EJI] `(ℋₙ)` canonically extends, by [Stacks, Tag 0EIR] it extends, and
by [Stacks, Tag 0EIU] so does `(ℱₙ)`. -/
theorem extendsToX_of_annihilated_of_proIso_depthThree
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) = 1)
    (F H : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (α : F.obj ⟶ H.obj)
    (hα : IsKernelCokernelAnnihilatedByPower (idealOnOpen S) α)
    (G : ℕᵒᵖ ⥤ S.U.toScheme.Modules) [∀ n : ℕᵒᵖ, (G.obj n).IsCoherent]
    (e : InverseSequence.ProIso G H.obj)
    (hdepth : ∀ n : ℕ, ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
      3 ≤ depthOfStalkOnOpen S (G.obj (op n)) y + S.distanceToZ z) :
    ExtendsToX S (toKerSystem S F) :=
  extendsToX_of_annihilated_of_canonicallyExtends S F H α hα
    (canonicallyExtends_of_cd_one_of_proIso_depthThree S H hdual hcd G e.symm hdepth)

end Stacks.Algebraization

end
