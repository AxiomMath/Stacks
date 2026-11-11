module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentKernelStabilization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.FormalCompletionCohomologySequence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalAdicTowerComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalQuotientTowerDerivedCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalQuotientTowerProducts
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology and completion of a coherent module at a principal ideal

Let `A` be a Noetherian ring, `a ∈ A`, `f : X ⟶ Spec A` a Noetherian scheme over `A` and `ℱ` a
coherent `𝒪_X`-module all of whose cohomology modules `H^p(X, ℱ)` are finite over `A`. Write
`I = (a)` and `𝓘 = I · 𝒪_X`. Then for every `p` there is a short exact sequence of `A`-modules

`0 ⟶ R¹lim H^{p-1}(X, ℱ/𝓘ⁿℱ) ⟶ H^p(X, ℱ)^∧ ⟶ lim H^p(X, ℱ/𝓘ⁿℱ) ⟶ 0`,

the conclusion of [Stacks, Tag 0A0M] with the `I`-adic completion of the `A`-module `H^p(X, ℱ)`
in the middle. This is the source's statement for a principal `I`, and nothing beyond the
source's own hypotheses on `A`, `X` and `ℱ` enters.

`Stacks.Algebraization.exists_shortExact_cohomology_limit_adicQuotients` of
`Completion/CohomologyAdicCompletion.lean` proves, for an arbitrary ideal `I` of `A`, the same
sequence with `H^p(X, lim ℱ/𝓘ⁿℱ)` in the middle, together with the identification
`H^p(RΓ(X, ℱ)^∧) = H^p(X, ℱ)^∧` of [Stacks, Tag 0A06]. What separates the two is a single
isomorphism of `D(A)`, namely `RΓ(X, lim ℱ/𝓘ⁿℱ) ≅ RΓ(X, ℱ)^∧`, which is [Stacks, Tag 0BLX];
`Stacks.Algebraization.exists_shortExact_adicCompletion_cohomology` there is the transport along
it. This file supplies that isomorphism when `I` is principal, which is what makes the transport
unconditional and gives the source's conclusion.

Two ingredients supply it.

* [Stacks, Tag 0BLD], in the form
  `Stacks.Algebraization.PrincipalQuotientTowerCompletion`
  `.nonempty_iso_derivedSections_limit_quotientTower_derivedCompletion`, is the isomorphism
  `RΓ(X, lim ℱ/aⁿ⁺¹ℱ) ≅ RΓ(X, ℱ)^∧` along the tower of cokernels of the iterates of
  multiplication by `a`. Its hypothesis on the `a`-power torsion of `ℱ` is supplied by
  `Stacks.Algebraization.stabilizes_mulF_of_isCoherent`, which proves it for a coherent sheaf on
  a Noetherian scheme out of the ascending chain condition of [Stacks, Tag 01Y8]; and its three
  countable-product side conditions are supplied by
  `Stacks.Algebraization.hasProductsOfShape_nat_derivedCategory_modules` and
  `Stacks.DerivedProducts.hasProductsOfShape_derivedCategory`. So nothing of the forbidden
  "exists stabilizing data" kind survives.
* The tower `n ↦ ℱ/aⁿ⁺¹ℱ` of that result and the tower `n ↦ ℱ/𝓘ⁿℱ` of this one are different
  constructions — a quotient by the cokernel of an endomorphism against a quotient by the
  subsheaf cut out by a power of an ideal sheaf, indexed one step apart. They are identified, for
  `𝓘 = (a)𝒪_X`, in `FormalGeometry/PrincipalAdicTowerComparison.lean`, whose
  `Stacks.Algebraization.PrincipalAdicTower.limitTowerIso` is the isomorphism of their inverse
  limits used here.

## What this file is for, now that the general case is proved

The source's whole statement — the sequence at an **arbitrary** ideal `I`, with the properness
clause — is `Stacks.Algebraization.exists_shortExact_adicCompletion_cohomology_whole` of
`Completion/GeneralCohomologyAdicCompletion.lean`, which discharges `hBLX` from the Koszul
identity of [Stacks, Tag 0BLX] and part (3) of [Stacks, Tag 0A0K]. This file keeps the principal
case because its route is different and independent: it goes through [Stacks, Tag 0BLD] and the
comparison of the two adic towers of `ℱ` at a principal ideal, and so neither needs the
quasi-compactness that part (3) of [Stacks, Tag 0A0K] carries nor the Koszul machinery of the
ringed site.

The properness clause is not proved here; it is
`Stacks.Algebraization.isZero_firstDerivedLimit_cohomology_adicQuotients_of_isProper` of
`Completion/CohomologyAdicCompletionWhole.lean`, out of [Stacks, Tag 02OB] and [Stacks,
Tag 02O8].

## Main results

* `Stacks.Algebraization.exists_shortExact_adicCompletion_cohomology_principal` — the short exact
  sequence with `H^p(X, ℱ)^∧` in the middle, for a principal ideal.

## Implementation notes

Derived `I`-adic completion is never introduced as data: `A` is Noetherian, so a left adjoint to
the inclusion of the derived-complete objects of `D(A)` exists by [Stacks, Tag 0920], and the
reflector is produced inside the proof of
`Stacks.Algebraization.exists_shortExact_adicCompletion_cohomology`. The isomorphism of
[Stacks, Tag 0BLX] proved here is stated for every reflector, which by uniqueness of left
adjoints is equivalent to its instance at any one of them.

`Stacks.Algebraization.modulesHasDerivedCategory` is reinstated as a local instance of high
priority, as in `Completion/CohomologyAdicCompletion.lean`, so that `D(𝒪_X)` is the standard
model. The countable products of `D(𝒪_X)` cannot be stated in this import closure, which is why
they live in `FormalGeometry/PrincipalQuotientTowerProducts.lean` and are consumed here as a
term.

## References

* [Stacks Project, Tag 0A0M](https://stacks.math.columbia.edu/tag/0A0M)
* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
* [Stacks Project, Tag 0BLD](https://stacks.math.columbia.edu/tag/0BLD)
* [Stacks Project, Tag 0A06](https://stacks.math.columbia.edu/tag/0A06)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0920](https://stacks.math.columbia.edu/tag/0920)
* [Stacks Project, Tag 01Y8](https://stacks.math.columbia.edu/tag/01Y8)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open scoped AlgebraicGeometry
open Stacks.Cohomology.DerivedSectionsOverBase (baseSmul derivedSectionsOver)
open Stacks.Algebraization.PrincipalQuotientTower (mulF quotientTower quotientTowerModules)
open Stacks.Algebraization.PrincipalQuotientTowerCompletion
  (nonempty_iso_derivedSections_limit_quotientTower_derivedCompletion)

universe u

namespace Stacks.Algebraization

attribute [local instance 10000] Stacks.Algebraization.modulesHasDerivedCategory

/-- **The short exact sequence of [Stacks, Tag 0A0M] for a principal ideal.**

Let `A` be a Noetherian ring, `a ∈ A`, `f : X ⟶ Spec A` a Noetherian scheme over `A` and `ℱ` a
coherent `𝒪_X`-module whose cohomology modules `H^p(X, ℱ)` are finite over `A` — the hypotheses
of the source, and nothing else. Write `I = (a)` and `𝓘 = I · 𝒪_X`. Then for every `p` the
`I`-adic completion of the `A`-module `H^p(X, ℱ)` sits in a short exact sequence of `A`-modules

`0 ⟶ R¹lim H^{p-1}(X, ℱ/𝓘ⁿℱ) ⟶ H^p(X, ℱ)^∧ ⟶ lim H^p(X, ℱ/𝓘ⁿℱ) ⟶ 0`,

whose left term is the cokernel of `1 - shift` on the product of the degree-`(p-1)` cohomology
tower and whose right term is the inverse limit of the degree-`p` cohomology tower. This is the
source's conclusion.

Derived `I`-adic completion is not data here: `A` is Noetherian, so a reflector onto the
derived-complete objects of `D(A)` exists by [Stacks, Tag 0920] and is produced inside the proof.
The isomorphism `RΓ(X, ℱ)^∧ ≅ RΓ(X, lim ℱ/𝓘ⁿℱ)` of [Stacks, Tag 0BLX], which the source's proof
derives, is proved for this `I` from [Stacks, Tag 0BLD] and the comparison of the two adic towers
of `ℱ` at a principal ideal, `Stacks.Algebraization.PrincipalAdicTower.limitTowerIso`.

This is the source's sequence at a principal ideal, by a route that goes through [Stacks,
Tag 0BLD]. At an arbitrary ideal the same sequence, together with the properness clause, is
`Stacks.Algebraization.exists_shortExact_adicCompletion_cohomology_whole` of
`Completion/GeneralCohomologyAdicCompletion.lean`, which discharges `hBLX` from the Koszul
identity of [Stacks, Tag 0BLX] and part (3) of [Stacks, Tag 0A0K] instead, and carries the tag. -/
public theorem exists_shortExact_adicCompletion_cohomology_principal
    (A : Type u) [CommRing A] [IsNoetherianRing A] (a : A)
    {X : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Spec (.of A))
    (F : X.Modules) [F.IsCoherent]
    (hfinite : ∀ p : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
        ((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F))))
    (p : ℤ) :
    let T : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
      adicQuotientSystem
          (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A (Ideal.span {a}) f) F ⋙
        DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f
    let H : ℤ → DerivedCategory (ModuleCat.{u} A) ⥤ ModuleCat.{u} A := fun q ↦
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) q
    ∃ (i : CompletionSequences.firstDerivedLimit A (T ⋙ H (p - 1)) ⟶
        ModuleCat.of A (AdicCompletion (Ideal.span {a})
          ((H p).obj ((derivedGlobalSectionsOver f).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj F)))))
      (q : ModuleCat.of A (AdicCompletion (Ideal.span {a})
          ((H p).obj ((derivedGlobalSectionsOver f).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj F)))) ⟶
        limit (T ⋙ H p))
      (w : i ≫ q = 0),
      (ShortComplex.mk i q w).ShortExact := by
  intro T H
  have hcoh : F.IsCoherent := inferInstance
  set ρ : A →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom with hρ
  -- The comparison of the two towers at the principal ideal `(a)`.
  have hIdeal : Stacks.Cohomology.FormalFunctions.baseIdealSheaf A (Ideal.span {a}) f =
      PrincipalAdicTower.spanIdealSheaf (ρ a) :=
    PrincipalAdicTower.baseIdealSheaf_span_singleton A f a
  have elim : limit (quotientTowerModules X ρ a F) ≅
      limit (adicQuotientSystem
        (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A (Ideal.span {a}) f) F) :=
    (PrincipalAdicTower.limitTowerIso X ρ a F).symm ≪≫
      eqToIso (congrArg (fun I : X.IdealSheafData ↦ limit (adicQuotientSystem I F)) hIdeal.symm)
  -- [Stacks, Tag 0BLX] for this `I`, out of [Stacks, Tag 0BLD]: the stabilization of the
  -- `a`-power torsion is proved for a coherent sheaf on a Noetherian scheme, and the countable
  -- products of `D(𝒪_X)` and of `D(A)` exist, so no side condition survives.
  have hBLX : ∀ (C : DerivedCategory (ModuleCat.{u} A) ⥤
      (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
        fun L ↦ IsDerivedComplete (Ideal.span {a}) L).FullSubcategory)
      (_ : C ⊣ (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
        fun L ↦ IsDerivedComplete (Ideal.span {a}) L).ι),
      Nonempty
        ((C.obj ((derivedGlobalSectionsOver f).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj F))).obj ≅
          (derivedGlobalSectionsOver f).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj
              (limit (adicQuotientSystem
                (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A (Ideal.span {a}) f) F)))) := by
    intro C adj
    have : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    have := hasProductsOfShape_nat_derivedCategory_modules X
    obtain ⟨⟨e⟩, -, -⟩ :=
      @nonempty_iso_derivedSections_limit_quotientTower_derivedCompletion
        X A _ ρ a F (isQuasicoherent_of_isCoherent F)
        (stabilizes_mulF_of_isCoherent ρ a F hcoh) _ _ _ _ C adj
    exact ⟨e.symm ≪≫ (derivedGlobalSectionsOver f).mapIso
      ((DerivedCategory.singleFunctor X.Modules 0).mapIso elim)⟩
  exact exists_shortExact_adicCompletion_cohomology_of_forall_reflector A (Ideal.span {a}) f F
    hfinite hBLX p

end Stacks.Algebraization

end
