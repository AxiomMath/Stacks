module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.AffineChartAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.GlobalProperOverCompleteLocal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GrothendieckExistenceProper
public import StacksCore.Tactic.StacksAttribute

/-!
# Algebraization of formal modules on a proper scheme over a complete local ring

Let `(R, 𝔪)` be a complete Noetherian local ring, let `p : X → Spec R` be proper, let `Z` be a
closed subset of the special fibre `X_1`, let `U = X ∖ Z` and let `j : U → X` be the inclusion.
Stacks 0EJV states that an object `(F_n)` of `Coh(U, 𝔪𝒪_U)` which is flat over `R` — `F_n` is flat
over `R/𝔪ⁿ` — and for which `j_*F_1` and `R¹j_*F_1` are coherent is algebraizable: it is the
completion of a coherent `𝒪_U`-module. This file proves that statement.

The proof is the one the remark sketches.

1. On every affine open `V` of `X` the hypotheses of Stacks 0EJU hold for the chart situation of
   `V` (`Stacks.Algebraization.isStableAdicSystem_sections_of_flat`): flatness of the formal stalks
   comes from flatness of the `F_n` by Stacks 0912, and finiteness of `H⁰(U ∩ V, F_1)` and
   `H¹(U ∩ V, F_1)` from the coherence of `j_*F_1` and `R¹j_*F_1`.
2. The canonical extensions of 0EJU on the members of a finite affine open cover are assembled into
   a single object `(G_n)` of `Coh(X, 𝔪𝒪_X)` whose restriction to `U` is `(F_n)`
   (`Stacks.Coherent.exists_coherentAdicSystem_restrict_iso`). It is cut out of the direct images
   `j_*F_n` by images and ideal-power quotients, with indices chosen uniformly over the cover, so
   no glueing is needed and the compatibility with localization that the remark attributes to
   Stacks 0DXW is built in.
3. Grothendieck's existence theorem, Stacks 088C
   (`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProper`), gives a coherent
   `𝒪_X`-module `𝒢` whose completion is `(G_n)`.
4. The restriction of the completion of `𝒢` to `U` is the completion of `𝒢|_U`
   (`Stacks.Algebraization.completionRestrictOpenIso`).

## Main results

* `Stacks.Algebraization.isCompletionOfCoherent_of_flat_of_isCoherent` — **Stacks 0EJV**, the
  algebraization statement.

## The hypotheses

The thickening `X_1` is the closed subscheme cut out by `𝔪𝒪_X`, which is
`Stacks.Cohomology.FormalFunctions.baseIdealSheaf R 𝔪 p`; `Z ⊆ X_1` is
`Z ≤ (baseIdealSheaf R 𝔪 p).support`, and the ideal sheaf `𝔪𝒪_U` is its restriction to `U`. The
system is zero-indexed, as everywhere in this library: the term `F.obj.obj (op n)` is the source's
`F_{n+1}`, annihilated by `𝔪ⁿ⁺¹`, so the flatness hypothesis is that it is flat over `R/𝔪ⁿ⁺¹`, and
the source's `F_1` is `F.obj.obj (op 0)`. Flatness of `F_n` over `R/𝔪ⁿ` is flatness of its stalks,
where `R` acts on the stalk at `x` through `R → Γ(X, 𝒪_X) → 𝒪_{U,x}`
(`Stacks.Algebraization.baseToStalk`); it is stated in the form
`Stacks.Algebraization.StalksFlatOverQuotient`, see the discussion there. The higher direct image
`R¹j_*` is the first right derived functor of `Scheme.Modules.pushforward j`, as in the library's
statements of Stacks 01XJ and 0BLT.

`X` is locally Noetherian, being of finite type over the Noetherian ring `R`; the statement
records this with `letI` rather than assuming it.

## References

* [Stacks Project, Tag 0EJV](https://stacks.math.columbia.edu/tag/0EJV)
* [Stacks Project, Tag 0EJU](https://stacks.math.columbia.edu/tag/0EJU)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 0912](https://stacks.math.columbia.edu/tag/0912)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.FormalFunctions
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-- **Stacks 0EJV, algebraization over a complete local base.** Let `(R, 𝔪)` be a complete
Noetherian local ring, let `p : X ⟶ Spec R` be proper, let `Z` be a closed subset of the special
fibre `X_1`, let `U = X ∖ Z` with inclusion `j = U.ι`, and let `(F_n)` be an object of
`Coh(U, 𝔪𝒪_U)`. Assume that `F_n` is flat over `R/𝔪ⁿ` for all `n`, and that `j_*F_1` and
`R¹j_*F_1` are coherent. Then `(F_n)` is the completion of a coherent `𝒪_U`-module. -/
@[stacks 0EJV "algebraization: a flat object of Coh(U, 𝔪𝒪_U) with j_*F₁ and R¹j_*F₁ coherent is \
the completion of a coherent 𝒪_U-module"]
theorem isCompletionOfCoherent_of_flat_of_isCoherent
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsProper p]
    (Z : Closeds X) (hZ : Z ≤ (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p).support)
    (U : X.Opens) (hU : (U : Set X) = (Z : Set X)ᶜ)
    (F : Stacks.Coherent.CoherentAdicSystems
      ((baseIdealSheaf R (IsLocalRing.maximalIdeal R) p).comap U.ι))
    (hflat : ∀ n : ℕ, StalksFlatOverQuotient R (baseToStalk R (U.ι ≫ p))
      (IsLocalRing.maximalIdeal R ^ (n + 1)) (F.obj.obj (op n)))
    (h0 : ((Scheme.Modules.pushforward U.ι).obj (F.obj.obj (op 0))).IsCoherent)
    (h1 : (((Scheme.Modules.pushforward U.ι).rightDerived 1).obj (F.obj.obj (op 0))).IsCoherent) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    IsCompletionOfCoherent ((baseIdealSheaf R (IsLocalRing.maximalIdeal R) p).comap U.ι) F := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := {}
  have hU' : ((U : Set X))ᶜ ⊆ (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p).support := by
    rw [hU, compl_compl]
    exact hZ
  let P := F.obj ⋙ Scheme.Modules.pushforward U.ι
  have : ∀ n, (P.obj n).IsQuasicoherent := fun n => by
    have : (F.obj.obj n).IsQuasicoherent := F.property.isQuasicoherent n.unop
    exact AlgebraicGeometry.pushforward_isQuasicoherent U.ι _
  obtain ⟨G, hG⟩ := Stacks.Coherent.exists_coherentAdicSystem_restrict_iso
    (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p) P fun V =>
    isStableAdicSystem_sections_of_flat R p U V F hU' hflat h0 h1
  obtain ⟨eH⟩ := hG U.ι F.obj F.property
    (Functor.isoWhiskerLeft F.obj (Scheme.Modules.restrictFunctorAdjCounitIso U.ι) ≪≫
      Functor.rightUnitor _)
  have := isEquivalence_completionFunctor_of_isProper R (IsLocalRing.maximalIdeal R) p
  let 𝒢 := (completionFunctor X (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p)).objPreimage G
  let eG : ((completionFunctor X (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p)).obj 𝒢).obj ≅
      G.obj :=
    (ObjectProperty.ι _).mapIso
      ((completionFunctor X (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p)).objObjPreimageIso G)
  exact ⟨restrictCoherentModules U.ι 𝒢,
    ⟨(completionRestrictOpenIso U.ι _ 𝒢).symm ≪≫
      Functor.isoWhiskerRight eG (Scheme.Modules.restrictFunctor U.ι) ≪≫ eH⟩⟩

end Stacks.Algebraization

end
