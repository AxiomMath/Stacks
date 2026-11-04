module

public import StacksFrontier.CategoryTheory.Sites.CechToCohomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
import StacksCore.Tactic.StacksAttribute

/-!
# The Čech-to-cohomology spectral sequence abutting to `H^{p+q}(U, F)`: Stacks 03OW

Let `C` be a site, let `𝒰 = {U_i → U}_{i ∈ I}` be a covering of an object `U` and let `F` be an
abelian sheaf on `C`.  [Stacks, Tag 03OW] asserts that there is a spectral sequence

```
E₂^{p,q} = Ȟ^p(𝒰, H^q(F))  ⟹  H^{p+q}(U, F),
```

where `H^q(F)` is the abelian presheaf `V ↦ H^q(V, F)`.

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/CechComparison/Basic.lean` builds this spectral
sequence as the Grothendieck spectral sequence of the composite
`Ab(C) --i--> PAb(C) --Ȟ⁰(𝒰,-)--> Ab`, with its second page, but abutting to the right derived
functors `R^{p+q}(Ȟ⁰(𝒰, -) ∘ i)(F)` of the composite.  This file supplies the step of the source's
proof that identifies that abutment with `H^{p+q}(U, F)`, and states the theorem in full.

## Main results

* `Stacks.CechComparison.exists_cechToCohomology_spectralSequence_abutsTo_sheafCohomology`:
  **[Stacks, Tag 03OW]**.  For a family `𝒰 = E` generating a covering sieve of `U` and an abelian
  sheaf `F` there is a cohomological spectral sequence, zero outside the first quadrant, with
  `E₂^{p,q} ≅ Ȟ^p(𝒰, H^q(F))` and abutting to `H^n(U, F)` (and to `0` in negative degrees).

## Implementation notes

**The abutment.**  The identification `R^n(Ȟ⁰(𝒰, -) ∘ i)(F) ≅ H^n(U, F)` is the composite of
three steps, all of `StacksFrontier/CategoryTheory/Sites/CechToCohomology.lean`, packaged as
`Stacks.CechSite.rightDerivedPlus_cechZero_obj_iso_cohomologyPresheaf`:

* the Čech augmentation `Γ(U, -) ⟶ Ȟ⁰(𝒰, -)` is a *natural* isomorphism on abelian sheaves when
  `𝒰` is a covering (`Stacks.CechSite.cechCohomologyZeroFunctorIso`, the naturality that the
  implementation notes of `CechComparison/Basic.lean` record as missing there), so
  `Ȟ⁰(𝒰, -) ∘ i ≅ Γ(U, -) ∘ i` and the two have the same right derived functors;
* evaluation at `U` is exact on abelian presheaves, so `R^n(Γ(U, -) ∘ i) ≅ Γ(U, -) ∘ R^n i`;
* `R^n i(F) ≅ H^n(F)` objectwise, [Stacks, Tag 03AY], so its value at `U` is `H^n(U, F)`.

Together with the acyclicity input of `CechComparison/Basic.lean` (`i` sends injective sheaves to
`Ȟ⁰(𝒰, -)`-acyclic presheaves, [Stacks, Tag 03AW] and [Stacks, Tag 03AU]) this is the
composition `R(Ȟ⁰(𝒰, -) ∘ i) = RΓ(U, -)` that the source's proof uses.

**Indexing.**  `CategoryTheory.SpectralSequence.AbutsTo` takes a `ℤ`-indexed abutment.  In negative
degrees the abutment of a first-quadrant spectral sequence is necessarily zero, so the family
abutted to is `n ↦ H^n(U, F)` for `n ≥ 0` and the initial object for `n < 0`.  The groups
`H^q(V, F)` are `(F.cohomologyPresheaf q).obj (op V)`, Mathlib's `CategoryTheory.Sheaf.H'`, in
the abutment exactly as in the second page.

**Hypotheses.**  The site is small with covering families indexed in its universe, as in
`CechComparison/Basic.lean`; sheafification of abelian presheaves is then found by instance
search and is not assumed.  The existence of the iterated fibre products
`U_{i₀} ×_U ⋯ ×_U U_{iₙ}`, which a covering of a site in the sense of the source has and which
the Čech complex is built from, is the one typeclass hypothesis on `E`.

## References

* [Stacks Project, Tag 03OW](https://stacks.math.columbia.edu/tag/03OW)
* [Stacks Project, Tag 03AY](https://stacks.math.columbia.edu/tag/03AY)
* [Stacks Project, Tag 03AZ](https://stacks.math.columbia.edu/tag/03AZ)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.CechComparison

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  {U : C}
  (E : PreZeroHypercover.{u} U)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun b ↦ Over.mk (E.f (i b)))]

/-- **Stacks Project, Tag 03OW.**  Let `C` be a site, `𝒰 = E = {U_i → U}_{i ∈ I}` a covering of
`U ∈ Ob(C)` (the family generates a covering sieve of `U`) and `F` an abelian sheaf on `C`.  There
is a cohomological spectral sequence, zero outside the first quadrant, with second page

```
E₂^{p,q} ≅ Ȟ^p(𝒰, H^q(F)),
```

the Čech cohomology of the covering with coefficients in the abelian presheaf
`H^q(F) : V ↦ H^q(V, F)`, and abutting to `H^{p+q}(U, F)`: the graded family abutted to is
`n ↦ H^n(U, F)` in degrees `n ≥ 0` and is zero in negative degrees, where no term of the
spectral sequence contributes.

The spectral sequence is the Grothendieck spectral sequence of `Ȟ⁰(𝒰, -) ∘ i` of
`exists_cechToCohomology_spectralSequence`; its abutment `R^n(Ȟ⁰(𝒰, -) ∘ i)(F)` is identified with
`H^n(U, F)` by `Stacks.CechSite.rightDerivedPlus_cechZero_obj_iso_cohomologyPresheaf`. -/
@[stacks 03OW, sga "4 V 3.2" "special case"]
theorem exists_cechToCohomology_spectralSequence_abutsTo_sheafCohomology
    (hE : E.sieve₀ ∈ J U) (F : Sheaf J AddCommGrpCat.{u}) :
    ∃ S : CohomologicalSpectralSequence AddCommGrpCat.{u} 0,
      (∀ p q : ℕ, Nonempty ((S.page 2 zero_le_two).X ((p : ℤ), (q : ℤ)) ≅
        Stacks.CechSite.cechCohomology E (F.cohomologyPresheaf q) p)) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((S.page 2 zero_le_two).X (p, q))) ∧
      SpectralSequence.AbutsTo S (fun n : ℤ ↦
        if n < 0 then ⊥_ AddCommGrpCat.{u} else (F.cohomologyPresheaf n.toNat).obj (op U)) := by
  obtain ⟨S, hE₂, habuts⟩ := exists_cechToCohomology_spectralSequence J E F
  refine ⟨S, fun p q => ?_, fun p q hpq => ?_, habuts.of_iso fun n => ?_⟩
  · obtain ⟨e⟩ := hE₂ (p : ℤ) (q : ℤ)
    refine ⟨e ≪≫ ?_⟩
    refine ((Stacks.CechSite.cechCohomologyIsoRightDerivedPlus.{u, u, u, u} E p).app
      (((sheafIncl J).rightDerivedPlus (q : ℤ)).obj F)).symm ≪≫ ?_
    exact (Stacks.CechSite.cechComplexFunctor E ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).mapIso
      (rightDerivedPlus_sheafToPresheaf_obj_iso_cohomologyPresheaf J F q)
  · refine IsZero.of_iso ?_ (hE₂ p q).some
    rcases hpq with hp | hq
    · exact Functor.isZero_rightDerivedPlus_of_neg (cechZeroFunctor E) _ p hp
    · have : ((cechZeroFunctor E).rightDerivedPlus p).Additive := by
        show (DerivedCategory.Plus.singleFunctor _ 0 ⋙
          (cechZeroFunctor E).rightDerivedFunctorPlus ⋙
            DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p).Additive
        infer_instance
      exact ((cechZeroFunctor E).rightDerivedPlus p).map_isZero
        (Functor.isZero_rightDerivedPlus_of_neg (sheafIncl J) F q hq)
  · split_ifs with hn
    · exact (Functor.isZero_rightDerivedPlus_of_neg _ F n hn).isoIsInitial initialIsInitial
    · have e :=
        Stacks.CechSite.rightDerivedPlus_cechZero_obj_iso_cohomologyPresheaf J U E hE n.toNat F
      rwa [Int.toNat_of_nonneg (by omega)] at e

end Stacks.CechComparison

end
