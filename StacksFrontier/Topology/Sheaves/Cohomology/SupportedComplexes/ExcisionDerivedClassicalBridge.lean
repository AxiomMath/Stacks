module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorPostcomposeExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorPrecomposeExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerivedNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.Homology.DerivedIndexing.PostCompositionCoherence
public import StacksFrontier.Homology.DerivedIndexing.PreCompositionCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.RightDerivedCompIsoTargetCongr

/-!
# The classical and the derived excision agree

An *excision* datum is: two abelian categories `𝒜` and `𝒜'`, an additive endofunctor `S : 𝒜 ⥤ 𝒜`,
an additive endofunctor `Ṡ : 𝒜' ⥤ 𝒜'`, an additive functor `L : 𝒜 ⥤ 𝒜'` which is exact, preserves
injective objects and has an exact left adjoint `V ⊣ L`, and a degree-zero comparison
`e : S ⋙ L ≅ L ⋙ Ṡ`. The motivating instance is `S = H_T(-)` the sections supported on a subset,
`L = (-)|_U` restriction to an open subset and `V` extension by zero, where `e` is excision in
degree zero.

Such a datum produces **two** comparisons in each degree:

* the **classical** one, between Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`,
  `S.rightDerived n ⋙ L ≅ L ⋙ Ṡ.rightDerived n`, built by moving `L` out of the derived functor
  with `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` and back in with
  `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` ([Stacks, Tag 015Z]) — this is
  the shape of `Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologyRestrictNatIso` and of
  `Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso`; and
* the **derived** one, on the unbounded derived category, `RS ⋙ L.mapDerivedCategory ≅
  L.mapDerivedCategory ⋙ RṠ`, built by the universal property of right derivation from `e` read
  degreewise, which is the shape of
  `Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSectionsRestrictNatIso`.

They agree, under the bridge `Hⁿ(Rw(X[0])) ≅ Rⁿw(X)` of
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` taken for `S` on one side
and for `Ṡ` on the other. That is `Stacks.DerivedIndexing.classicalExcision_eq_derivedExcision`,
the main result, and its componentwise form.

## Main definitions

* `Stacks.DerivedIndexing.excisionHomotopyIso`: `e` read on the homotopy category and then on the
  derived category — the degreewise datum the universal property of right derivation consumes.
  This is `Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsRestrictHomotopyIso`
  generically.
* `Stacks.DerivedIndexing.derivedExcisionNatIso`: **the derived excision**,
  `RS ⋙ L.mapDerivedCategory ≅ L.mapDerivedCategory ⋙ RṠ`, by Mathlib's
  `CategoryTheory.Functor.rightDerivedNatIso` for the two right derived functors of `S ⋙ L` and of
  `L ⋙ Ṡ`.
* `Stacks.DerivedIndexing.derivedExcisionSingleHomologyNatTrans`: that comparison read on the
  degree-`n` cohomology of the derived functor at an object placed in degree `0`, which is the
  left-hand side of the main result.
* `Stacks.DerivedIndexing.postCompSingleHomologyNatTrans`: the comparison pulling `L` out of the
  cohomology of `D(𝒜')`, read at `RS` of an object placed in degree `0`. It is written out rather
  than whiskered, for the reason recorded on
  `Stacks.DerivedIndexing.preCompSingleHomologyNatTrans`.

## Main results

* `Stacks.DerivedIndexing.isRightDerivedFunctor_rightDerivedCompMapDerivedCategory` and
  `Stacks.DerivedIndexing.isRightDerivedFunctor_mapDerivedCategoryCompRightDerived`: the two
  presuppositions of the derived excision, that `RS ⋙ L.mapDerivedCategory` is a right derived
  functor of `S ⋙ L` and that `L.mapDerivedCategory ⋙ RṠ` is one of `L ⋙ Ṡ`.
* `Stacks.DerivedIndexing.derivedExcisionNatIso_fac`: the factorization that pins the derived
  excision down.
* `Stacks.DerivedIndexing.classicalExcision_eq_derivedExcision_app`,
  `Stacks.DerivedIndexing.classicalExcision_eq_derivedExcision`: **the classical excision is
  `Hⁿ` of the derived excision**, componentwise and as an equality of natural transformations.

## Implementation notes

**The three coherences, pasted.** The proof of the main result is four facts composed, in this
order:

1. `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_naturality_app`, the
   coherence of the bridge *in the functor variable*, at `τ = e.hom`, `Rw₁ = RS ⋙
   L.mapDerivedCategory` and `Rw₂ = L.mapDerivedCategory ⋙ RṠ`. It turns `Hⁿ` of the derived
   excision followed by the bridge for `L ⋙ Ṡ` into the bridge for `S ⋙ L` followed by Mathlib's
   `CategoryTheory.NatTrans.rightDerived e.hom n`. The hypothesis it needs — that the derived
   excision *is* the morphism the universal property produces from `e` — is
   `Stacks.DerivedIndexing.derivedExcisionNatIso_hom`, which holds because
   `Stacks.DerivedIndexing.excisionHomotopyIso` is, on the nose,
   `Stacks.DerivedFunctor.mapHomotopyCategoryCompQhNatTrans` of `e.hom`.
2. `Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_postComp_app`, the
   coherence for *post-composition with an exact functor*, which computes the bridge for `S ⋙ L`
   at `RS ⋙ L.mapDerivedCategory` as `L` pulled out of the cohomology of `D(𝒜')`, the bridge for
   `S` under `L`, and Mathlib's `CategoryTheory.Functor.rightDerivedCompIso` inverted. Its
   presupposition is `Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose`, with unit
   `Stacks.DerivedFunctor.postcomposeUnit`.
3. `Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_preComp_app`, the
   coherence for *pre-composition with an exact functor preserving injectives*, which computes
   the bridge for `L ⋙ Ṡ` at `L.mapDerivedCategory ⋙ RṠ`, followed by
   `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`, as the single-functor
   comparison of `L.mapDerivedCategory` followed by the bridge for `Ṡ` at `L X`. Its
   presupposition is
   `Stacks.DerivedFunctor.isRightDerivedFunctor_precompose_of_exact_leftAdjoint`, with unit
   `Stacks.DerivedFunctor.precomposeUnit`, whose pinning hypothesis `hα'` is discharged verbatim
   by `Stacks.DerivedFunctor.precomposeUnit_app`.
4. `Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso_hom_app`, which is where the
   congruence of
   `StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.RightDerivedCompIsoTargetCongr`
   enters. **It is needed because the two coherences speak different dialects**: step 2 produces
   Mathlib's `CategoryTheory.Functor.rightDerivedCompIso S L n`, which is the comparison only in
   the case `H = S ⋙ L`, whereas the classical excision is
   `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso S L (L ⋙ Ṡ) e n`, at the general target
   `H = L ⋙ Ṡ`. The congruence says exactly that the second is the first inverted followed by the
   right derived functor of `e` — which is the factor step 1 leaves over. Without it the two sides
   do not even have matching types.

Each of the four is a single equation between morphisms of `𝒜'`; the remaining content is one
associativity chase, `bridge_chase`.

**No transport of units is needed.** `Stacks.DerivedFunctor.rightDerivedNatTrans_unit_iso` exists
to make the naturality coherence applicable when a unit is presented at a functor isomorphic to,
but not spelled as, `w(-) ∘ Qh`. It is not used here: `Stacks.DerivedFunctor.postcomposeUnit` and
`Stacks.DerivedFunctor.precomposeUnit` are already stated at the spellings
`(S ⋙ L).mapHomotopyCategory _ ⋙ Qh` and `(L ⋙ Ṡ).mapHomotopyCategory _ ⋙ Qh` that the bridge and
the naturality coherence are defined for.

**The two composite `IsRightDerivedFunctor` statements are instance hypotheses** of the results
below, exactly as in `StacksFrontier.Homology.DerivedIndexing.PostCompositionCoherence`: they occur in
the *statements*, through the bridge, so they must be available when a statement is elaborated,
and they cannot be synthesized from the K-injective-resolution hypotheses, which are not classes.
`isRightDerivedFunctor_rightDerivedCompMapDerivedCategory` and
`isRightDerivedFunctor_mapDerivedCategoryCompRightDerived` of this file supply them from the
excision datum, so nothing beyond that datum is ever asked for. The class is a `Prop`, so no
coherence between two such instances has to be checked.

**Transparency.** Every chase is a `private` helper at a variable category with the objects
implicit and the morphisms explicit, applied with `exact`, as in
`StacksFrontier.Homology.DerivedIndexing.PreCompositionCoherence`: on `DerivedCategory` the
reassociations of `Functor.comp` and the two spellings of a composite's homotopy-category functor
are definitionally but not syntactically equal, and `rw` and `simp only` fail on them.

## References

* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category

namespace Stacks.DerivedIndexing

universe wA vA uA wA' vA' uA'

section Excision

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wA} A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [EnoughInjectives A']
  [HasDerivedCategory.{wA'} A']
  (S : A ⥤ A) [S.Additive] (S' : A' ⥤ A') [S'.Additive]
  (L : A ⥤ A') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [L.PreservesInjectiveObjects]
  (e : S ⋙ L ≅ L ⋙ S')
  (RS : DerivedCategory A ⥤ DerivedCategory A)
  (αS : S.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RS)
  [RS.IsRightDerivedFunctor αS (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (RS' : DerivedCategory A' ⥤ DerivedCategory A')
  (αS' : S'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RS')
  [RS'.IsRightDerivedFunctor αS' (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
  (V : A' ⥤ A) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V] (adj : V ⊣ L)
  (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  (hres' : ∀ K : CochainComplex A' ℤ, ∃ (I : CochainComplex A' ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)

/-- The chase behind `classicalExcision_eq_derivedExcision_app`: the pre-composition coherence
`hQ` replaces the right-hand pair, the naturality coherence `hStar` crosses the square, the
post-composition coherence `hP` splits the left edge into three and the target congruence `hDag`
assembles the last two factors. Stated at an arbitrary category with the objects implicit and the
morphisms explicit. -/
private theorem bridge_chase {E : Type*} [Category* E] {x y z u v p r w : E}
    (a : x ⟶ y) (b : y ⟶ z) (cc : z ⟶ u) (q₁ : y ⟶ v) (q₂ : v ⟶ u)
    (d : x ⟶ w) (f : w ⟶ z) (g₁ : x ⟶ p) (g₂ : p ⟶ r) (g₃ : r ⟶ w) (m : r ⟶ z)
    (hQ : b ≫ cc = q₁ ≫ q₂) (hStar : a ≫ b = d ≫ f) (hP : d = g₁ ≫ g₂ ≫ g₃)
    (hDag : m = g₃ ≫ f) :
    a ≫ q₁ ≫ q₂ = g₁ ≫ g₂ ≫ m ≫ cc := by
  subst hP hDag
  simp [← hQ, reassoc_of% hStar]

/-! ### The degreewise datum -/

/-- **The degree-zero excision, read on the homotopy category and then on the derived category.**
The comparison of the homotopy-category functor of `S ⋙ L` with the composite of the
homotopy-category functors, inverted, then `e` applied degreewise, then `DerivedCategory.Qh`.

This is the generic form of
`Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsRestrictHomotopyIso`, and it is the
datum the universal property of right derivation consumes. -/
def excisionHomotopyIso :
    (S ⋙ L).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      (L ⋙ S').mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.isoWhiskerRight
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (S ⋙ L)) (ComplexShape.up ℤ)).symm ≪≫
      Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)) DerivedCategory.Qh

/-- The components of `excisionHomotopyIso`: the comparison at `CategoryTheory.Iso.refl`
contributes an identity morphism, so what is left is `e` applied degreewise, under
`DerivedCategory.Qh`. -/
theorem excisionHomotopyIso_hom_app (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (excisionHomotopyIso S S' L e).hom.app K =
      (Stacks.DerivedFunctor.mapHomotopyCategoryCompQhNatTrans (S ⋙ L) (L ⋙ S') e.hom).app K :=
  have h0 : (Functor.mapHomotopyCategoryCompIso (Iso.refl (S ⋙ L))
      (ComplexShape.up ℤ)).inv.app K = CategoryStruct.id
        ((S.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          L.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) := rfl
  have h1 : (excisionHomotopyIso S S' L e).hom.app K =
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (S ⋙ L))
            (ComplexShape.up ℤ)).inv.app K ≫
          (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app K) := rfl
  have h2 : (Functor.mapHomotopyCategoryCompIso (Iso.refl (S ⋙ L))
          (ComplexShape.up ℤ)).inv.app K ≫
        (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app K =
      (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K :=
    (congrArg
      (fun z => z ≫ (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app K)
      h0).trans (Category.id_comp _)
  h1.trans (congrArg DerivedCategory.Qh.map h2)

/-- **`excisionHomotopyIso` is the datum the universal property of right derivation consumes.**
Its `hom` is `Stacks.DerivedFunctor.mapHomotopyCategoryCompQhNatTrans` of `e.hom`, which is what
makes `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_naturality` applicable
to the derived excision. -/
theorem excisionHomotopyIso_hom :
    (excisionHomotopyIso S S' L e).hom =
      Stacks.DerivedFunctor.mapHomotopyCategoryCompQhNatTrans (S ⋙ L) (L ⋙ S') e.hom :=
  NatTrans.ext (funext fun K => excisionHomotopyIso_hom_app S S' L e K)

/-! ### The two presuppositions -/

include hres in
/-- **`RS ⋙ L.mapDerivedCategory` is a right derived functor of `S ⋙ L`.** `L` is exact, so this
is absoluteness of a right derived functor computed by K-injective resolutions,
`Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose`. -/
theorem isRightDerivedFunctor_rightDerivedCompMapDerivedCategory :
    (RS ⋙ L.mapDerivedCategory).IsRightDerivedFunctor
      (Stacks.DerivedFunctor.postcomposeUnit S L RS αS)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose S L RS αS hres

include V adj hres hres' in
/-- **`L.mapDerivedCategory ⋙ RṠ` is a right derived functor of `L ⋙ Ṡ`.** Unlike the
post-composition statement this is not formal: it needs that `L` carries K-injective complexes to
K-injective ones, which holds by [Stacks, Tag 08BJ] because `L` has the exact left adjoint `V`.
That is `Stacks.DerivedFunctor.isRightDerivedFunctor_precompose_of_exact_leftAdjoint`. -/
theorem isRightDerivedFunctor_mapDerivedCategoryCompRightDerived :
    (L.mapDerivedCategory ⋙ RS').IsRightDerivedFunctor
      (Stacks.DerivedFunctor.precomposeUnit L S' RS' αS')
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.isRightDerivedFunctor_precompose_of_exact_leftAdjoint L S' RS' αS' V adj
    hres' hres

/-! ### The derived excision -/

variable [(RS ⋙ L.mapDerivedCategory).IsRightDerivedFunctor
    (Stacks.DerivedFunctor.postcomposeUnit S L RS αS)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [(L.mapDerivedCategory ⋙ RS').IsRightDerivedFunctor
    (Stacks.DerivedFunctor.precomposeUnit L S' RS' αS')
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- **The derived excision.** For an excision datum with total right derived functors `RS` of `S`
and `RṠ` of `Ṡ`,

`RS(K)|_L ≅ RṠ(K|_L)`,

naturally in `K` in the unbounded derived category of `𝒜`. Both composites are right derived
functors of the degreewise-isomorphic functors `S ⋙ L` and `L ⋙ Ṡ` — the two presuppositions
above — so the uniqueness of right derived functors,
`CategoryTheory.Functor.rightDerivedNatIso`, supplies the comparison from `excisionHomotopyIso`.
What pins it down is `derivedExcisionNatIso_fac`.

`Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSectionsRestrictNatIso` is this
comparison for the local cohomology of sheaves of abelian groups. -/
def derivedExcisionNatIso : RS ⋙ L.mapDerivedCategory ≅ L.mapDerivedCategory ⋙ RS' :=
  Functor.rightDerivedNatIso (RS ⋙ L.mapDerivedCategory) (L.mapDerivedCategory ⋙ RS')
    (Stacks.DerivedFunctor.postcomposeUnit S L RS αS)
    (Stacks.DerivedFunctor.precomposeUnit L S' RS' αS')
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (excisionHomotopyIso S S' L e)

/-- **The factorization that pins the derived excision down.** The unit exhibiting
`RS ⋙ L.mapDerivedCategory` as a right derived functor, followed by the comparison, is the
degreewise excision followed by the unit exhibiting `L.mapDerivedCategory ⋙ RṠ` as one. -/
theorem derivedExcisionNatIso_fac :
    Stacks.DerivedFunctor.postcomposeUnit S L RS αS ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (derivedExcisionNatIso S S' L e RS αS RS' αS').hom =
      (excisionHomotopyIso S S' L e).hom ≫
        Stacks.DerivedFunctor.precomposeUnit L S' RS' αS' :=
  Functor.rightDerivedNatTrans_fac (RS ⋙ L.mapDerivedCategory) (L.mapDerivedCategory ⋙ RS')
    (Stacks.DerivedFunctor.postcomposeUnit S L RS αS)
    (Stacks.DerivedFunctor.precomposeUnit L S' RS' αS')
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (excisionHomotopyIso S S' L e).hom

/-- **The derived excision is the morphism the universal property produces from `e`.** Both are
`CategoryTheory.Functor.rightDerivedNatTrans` at the same two units, and the degreewise data agree
by `excisionHomotopyIso_hom`. This is what makes the naturality coherence of the bridge applicable
to the derived excision. -/
theorem derivedExcisionNatIso_hom :
    (derivedExcisionNatIso S S' L e RS αS RS' αS').hom =
      Stacks.DerivedFunctor.derivedNatTrans (S ⋙ L) (L ⋙ S') (RS ⋙ L.mapDerivedCategory)
        (L.mapDerivedCategory ⋙ RS') (Stacks.DerivedFunctor.postcomposeUnit S L RS αS)
        (Stacks.DerivedFunctor.precomposeUnit L S' RS' αS') e.hom :=
  congrArg
    (fun σ => Functor.rightDerivedNatTrans (RS ⋙ L.mapDerivedCategory)
      (L.mapDerivedCategory ⋙ RS') (Stacks.DerivedFunctor.postcomposeUnit S L RS αS)
      (Stacks.DerivedFunctor.precomposeUnit L S' RS' αS')
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) σ)
    (excisionHomotopyIso_hom S S' L e)

/-! ### The two sides of the comparison -/

/-- **`Hⁿ` of the derived excision**, at an object placed in degree `0`: the left-hand side of the
main result. The components are written out rather than assembled by whiskering, for the reason
recorded on `Stacks.DerivedIndexing.preCompSingleHomologyNatTrans`. -/
def derivedExcisionSingleHomologyNatTrans (n : ℤ) :
    DerivedCategory.singleFunctor A 0 ⋙ (RS ⋙ L.mapDerivedCategory) ⋙
        DerivedCategory.homologyFunctor A' n ⟶
      DerivedCategory.singleFunctor A 0 ⋙ (L.mapDerivedCategory ⋙ RS') ⋙
        DerivedCategory.homologyFunctor A' n :=
  Functor.whiskerLeft (DerivedCategory.singleFunctor A 0)
    (Functor.whiskerRight (derivedExcisionNatIso S S' L e RS αS RS' αS').hom
      (DerivedCategory.homologyFunctor A' n))

/-- **`Hⁿ` of the derived excision is the morphism the naturality coherence of the bridge is
stated for.** -/
theorem derivedExcisionSingleHomologyNatTrans_eq (n : ℤ) :
    derivedExcisionSingleHomologyNatTrans S S' L e RS αS RS' αS' n =
      Stacks.DerivedFunctor.singleCompDerivedCompHomologyNatTrans (S ⋙ L) (L ⋙ S')
        (RS ⋙ L.mapDerivedCategory) (L.mapDerivedCategory ⋙ RS')
        (Stacks.DerivedFunctor.postcomposeUnit S L RS αS)
        (Stacks.DerivedFunctor.precomposeUnit L S' RS' αS') e.hom n :=
  congrArg
    (fun τ => Functor.whiskerLeft (DerivedCategory.singleFunctor A 0)
      (Functor.whiskerRight τ (DerivedCategory.homologyFunctor A' n)))
    (derivedExcisionNatIso_hom S S' L e RS αS RS' αS')

end Excision

section Sides

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [HasDerivedCategory.{wA'} A']
  (L : A ⥤ A') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (RS : DerivedCategory A ⥤ DerivedCategory A)

/-- **`L` pulled out of the cohomology of `D(𝒜')`**, read at `RS` of an object placed in degree
`0`: the first factor of the right-hand side of the main result. The components are written out
rather than assembled by whiskering, which would produce bracketings definitionally but not
unifiably equal to the ones the bridge is stated at — exactly as for
`Stacks.DerivedIndexing.preCompSingleHomologyNatTrans`. -/
def postCompSingleHomologyNatTrans (n : ℤ) :
    DerivedCategory.singleFunctor A 0 ⋙ (RS ⋙ L.mapDerivedCategory) ⋙
        DerivedCategory.homologyFunctor A' n ⟶
      (DerivedCategory.singleFunctor A 0 ⋙ RS ⋙ DerivedCategory.homologyFunctor A n) ⋙ L where
  app X := (L.mapDerivedCategoryHomologyIso n).hom.app
    (RS.obj ((DerivedCategory.singleFunctor A 0).obj X))
  naturality _ _ f := (L.mapDerivedCategoryHomologyIso n).hom.naturality
    (RS.map ((DerivedCategory.singleFunctor A 0).map f))

end Sides

/-! ### The comparison -/

section Bridge

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wA} A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [EnoughInjectives A']
  [HasDerivedCategory.{wA'} A']
  (S : A ⥤ A) [S.Additive] (S' : A' ⥤ A') [S'.Additive]
  (L : A ⥤ A') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [L.PreservesInjectiveObjects]
  (e : S ⋙ L ≅ L ⋙ S')
  (RS : DerivedCategory A ⥤ DerivedCategory A)
  (αS : S.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RS)
  [RS.IsRightDerivedFunctor αS (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (RS' : DerivedCategory A' ⥤ DerivedCategory A')
  (αS' : S'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RS')
  [RS'.IsRightDerivedFunctor αS' (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
  [(RS ⋙ L.mapDerivedCategory).IsRightDerivedFunctor
    (Stacks.DerivedFunctor.postcomposeUnit S L RS αS)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [(L.mapDerivedCategory ⋙ RS').IsRightDerivedFunctor
    (Stacks.DerivedFunctor.precomposeUnit L S' RS' αS')
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  (hres' : ∀ K : CochainComplex A' ℤ, ∃ (I : CochainComplex A' ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)

/-- **The classical excision is `Hⁿ` of the derived excision, componentwise.** At `X : 𝒜`:
`Hⁿ` of the derived excision, followed by the two factors of the bridge for `Ṡ` at `L X`, is `L`
pulled out of the cohomology of `D(𝒜')`, then `L` applied to the bridge for `S` at `X`, then the
classical excision at `X`. -/
theorem classicalExcision_eq_derivedExcision_app (n : ℕ) (X : A) :
    (derivedExcisionSingleHomologyNatTrans S S' L e RS αS RS' αS' (n : ℤ)).app X ≫
        (preCompSingleHomologyNatTrans L RS' (n : ℤ)).app X ≫
          (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived S' RS' αS'
            hres' n).hom.app (L.obj X) =
      (postCompSingleHomologyNatTrans L RS (n : ℤ)).app X ≫
        L.map ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived S RS αS
            hres n).hom.app X) ≫
          (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso S L (L ⋙ S') e n ≪≫
            Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L S' n).hom.app X := by
  have hcl : (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso S L (L ⋙ S') e n ≪≫
        Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L S' n).hom.app X =
      (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso S L (L ⋙ S') e n).hom.app X ≫
        (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L S' n).hom.app X := rfl
  have hQ := singleCompDerivedCompHomologyIsoRightDerived_preComp_app L S' RS' αS'
    (Stacks.DerivedFunctor.precomposeUnit L S' RS' αS')
    (Stacks.DerivedFunctor.precomposeUnit_app L S' RS' αS') hres hres' n X
  have hStar := Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_naturality_app
    (S ⋙ L) (L ⋙ S') (RS ⋙ L.mapDerivedCategory) (L.mapDerivedCategory ⋙ RS')
    (Stacks.DerivedFunctor.postcomposeUnit S L RS αS)
    (Stacks.DerivedFunctor.precomposeUnit L S' RS' αS') hres e.hom n X
  have hP := singleCompDerivedCompHomologyIsoRightDerived_postComp_app S L RS αS hres n X
  have hDag := moduleComparison_rightDerivedCompIso_hom_app S L (L ⋙ S') e n X
  rw [hcl, derivedExcisionSingleHomologyNatTrans_eq,
    Stacks.DerivedFunctor.singleCompDerivedCompHomologyNatTrans_app]
  exact bridge_chase _ _ _ _ _ _ _ _ _ _ _ hQ hStar hP hDag

/-- **The classical excision is `Hⁿ` of the derived excision.**

Let `S : 𝒜 ⥤ 𝒜` and `Ṡ : 𝒜' ⥤ 𝒜'` be additive, let `L : 𝒜 ⥤ 𝒜'` be additive, exact, preserving
injective objects, and let `e : S ⋙ L ≅ L ⋙ Ṡ`. Let `RS` and `RṠ` be total right derived functors
of `S` and `Ṡ` on the unbounded derived categories, with units `αS` and `αṠ`.

Then the **classical** degree-`n` excision

`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso S L (L ⋙ Ṡ) e n ≪≫
Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L Ṡ n :
S.rightDerived n ⋙ L ≅ L ⋙ Ṡ.rightDerived n`

agrees, under the two bridges `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`
for `S` and for `Ṡ`, with the degree-`n` cohomology of the **derived** excision
`derivedExcisionNatIso` produced from `e` by the universal property of right derivation.

The three coherences of the bridge and the target congruence of
`Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso_hom_app` are pasted in the order
recorded in the implementation notes. -/
theorem classicalExcision_eq_derivedExcision (n : ℕ) :
    derivedExcisionSingleHomologyNatTrans S S' L e RS αS RS' αS' (n : ℤ) ≫
        preCompSingleHomologyNatTrans L RS' (n : ℤ) ≫
          Functor.whiskerLeft L
            (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived S' RS' αS'
              hres' n).hom =
      postCompSingleHomologyNatTrans L RS (n : ℤ) ≫
        Functor.whiskerRight
            (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived S RS αS
              hres n).hom L ≫
          (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso S L (L ⋙ S') e n ≪≫
            Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L S' n).hom :=
  NatTrans.ext (funext fun X =>
    classicalExcision_eq_derivedExcision_app S S' L e RS αS RS' αS' hres hres' n X)

end Bridge

end Stacks.DerivedIndexing

end
