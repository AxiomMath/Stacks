module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceSectionMultiplication
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialNumerical
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRegularity
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.Regularity

/-!
# Multiplication of sections by linear forms on a regular sheaf

Let `k` be a field, `n ≥ 0` and `ℱ` a coherent sheaf on `ℙⁿ_k`. [Stacks, Tag 08A7] says that if
`ℱ` is `m`-regular then the multiplication map

`H⁰(ℙⁿ_k, ℱ(m)) ⊗_k H⁰(ℙⁿ_k, 𝒪(1)) ⟶ H⁰(ℙⁿ_k, ℱ(m+1))`

is surjective. This file proves that, by the induction on `n` of the source, from the hyperplane
restriction data of [Stacks, Tag 08A0] carried as a hypothesis.

## Main definitions

* `AlgebraicGeometry.HyperplaneRestrictionPackage` bundles the hyperplane restriction data of
  [Stacks, Tag 08A0] in the twisted form of [Stacks, Tag 0EGK], together with the degree-zero
  cohomology comparison of [Stacks, Tag 089W] and the lifting of degree-one forms of
  [Stacks, Tag 089Z].

## Main results

* `AlgebraicGeometry.surjective_cohomologyOverFieldMap_zero_of_isMRegular`: the step at which
  `m`-regularity is used — a section on the hyperplane lifts to `ℙⁿ_k`, because
  `H¹(ℙⁿ_k, ℱ(m-1)) = 0`.
* `AlgebraicGeometry.span_mulSections_eq_top_of_isMRegular_zero`: the base case `n = 0`, where
  `𝒪(1)` is trivial and multiplication by a generator is an isomorphism.
* `AlgebraicGeometry.span_mulSections_eq_top_of_isMRegular`: **[Stacks, Tag 08A7].**

## How the multiplication map is rendered

`H⁰(ℙⁿ_k, -)` is `AlgebraicGeometry.cohomologyOverField`, the right derived global sections with
scalars restricted along the structure morphism, so it is a genuine `k`-vector space; in degree
zero it is the module of global sections by
`AlgebraicGeometry.cohomologyOverFieldZeroEquivSections`. The multiplication map is the one
induced on `H⁰` by `Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.twistSectionMul`,
multiplication of a twisted module by a global section of `𝒪(1)`; `H⁰(ℙⁿ_k, 𝒪(1))` is the type
`(twistOver n (Spec k) 1).sections` of those global sections.

Surjectivity of a linear map out of `A ⊗_k B` is stated as the statement that the `k`-span of the
products is everything: the image of `TensorProduct.lift` of a bilinear map is the span of the
range of that map, so the two are the same assertion, and the span form needs neither the tensor
product nor the bilinearity of multiplication to be constructed. This matters because the
`k`-vector space structure on `H⁰` comes from a restriction of scalars whose comparison with
global sections is only available as an `Equiv`.

## What is carried and what is proved

`AlgebraicGeometry.HyperplaneRestrictionPackage` is carried here, as the hypothesis `pkg`. Over
an **infinite** field every clause of it except `liftSection` is now proved elsewhere in this
repository, and `AlgebraicGeometry.exists_hyperplaneRestrictionData` in
`StacksFrontier/AlgebraicGeometry/Variety/Projective/HyperplaneRestrictionPackageConstruction.lean`
produces the data carrying them: `G`, `isCoherent`, `j`, `isAffineHom` and `s` come from
`AlgebraicGeometry.exists_restrictionSequences`, whose
`AlgebraicGeometry.HasMulRestrictionSequences` clause gives `res`, `comp_res` and `shortExact`
— the sequences of [Stacks, Tag 08A0] twisted as in [Stacks, Tag 0EGK], with multiplication by
`s` as their first arrow — and whose 0EGK-shaped clause gives `shortExact'`; `compare` is
`AlgebraicGeometry.projectiveHPushforwardIso`, the comparison of [Stacks, Tag 089W] along a
closed immersion over `Spec k`, which the over-`Spec k` clause of [Stacks, Tag 089Z] unblocks.
`AlgebraicGeometry.nonempty_hyperplaneRestrictionPackage_of_liftSection` then says that that
data together with `liftSection` for it **is** a package.

`liftSection` — that every degree-one form on the hyperplane is the restriction of one upstairs,
compatibly with multiplication on `H⁰`, the source's "see the proof of Lemma 33.35.2" — is now
proved too over an infinite field, from one hypothesis that has no cohomology and no
multiplication in it: `AlgebraicGeometry.nonempty_hyperplaneRestrictionPackage_of_liftSectionHom`
and `AlgebraicGeometry.nonempty_hyperplaneRestrictionPackage_of_surjective_restriction` produce a
whole package from the surjectivity of restriction on global sections of `𝒪(1)` alone. What makes
that possible is that the restriction arrows are no longer chosen out of the sequences but given
by a formula, `AlgebraicGeometry.pullbackTwistUnitRes`, so that naturality of the unit of
`j^* ⊣ j_*` reduces the intertwining to a square of sheaves upstairs of the hyperplane; see
`StacksFrontier/AlgebraicGeometry/Variety/Projective/HyperplaneRestrictionPackageConstruction.lean`,
whose "What remains" section states the surviving obligation exactly. The clause is deliberately
**not** offered as a hypothesis quantified over all restriction arrows: `res` is pinned down by
the sequences only up to an automorphism of each target, and such a change leaves exactness intact
while breaking the intertwining, so the quantified form would be false and a reduction to it
vacuous.

Discharging `pkg` for an arbitrary field needs, on top of `liftSection`, the descent of the
conclusion from an infinite extension back to `k`. [Stacks, Tag 08A4] is not the obstruction —
`AlgebraicGeometry.isMRegular_iff_fieldExtension` is proved and
`AlgebraicGeometry.isMRegular_add_one` already passes through `RatFunc k` with it — but it
descends a vanishing statement, whereas the conclusion here is a surjectivity on `H⁰`, which
needs base change of `H⁰` along `k ⟶ RatFunc k` compatible with multiplication by a section.

Everything else is proved here: the induction on `n`, the base case, the lifting of a section
from the hyperplane out of the vanishing of `H¹` that `m`-regularity provides, and the final
exactness step. Because the restriction data is a hypothesis, no hypothesis on `k` beyond being
a field is present in this file.

## References

* [Stacks Project, Tag 08A7](https://stacks.math.columbia.edu/tag/08A7)
* [Stacks Project, Tag 08A3](https://stacks.math.columbia.edu/tag/08A3)
* [Stacks Project, Tag 08A5](https://stacks.math.columbia.edu/tag/08A5)
* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
* [Stacks Project, Tag 0EGK](https://stacks.math.columbia.edu/tag/0EGK)
* [Stacks Project, Tag 089Z](https://stacks.math.columbia.edu/tag/089Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication
open Stacks.RelativeVeryAmple

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The structure morphism `ℙⁿ_k ⟶ Spec k`. -/
abbrev projectiveSpaceToBase (k : Type u) [Field k] (n : ℕ) :
    projectiveSpaceOverRing n (.of k) ⟶ Spec (.of k) :=
  projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)

/-- `Hⁱ(ℙⁿ_k, ℱ)` as a `k`-vector space. -/
abbrev projectiveH (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) (i : ℕ) : ModuleCat.{u} k :=
  cohomologyOverField k (projectiveSpaceToBase k n) F i

/-- The map on `H⁰(ℙⁿ_k, -)` induced by a morphism of modules. -/
abbrev projectiveHZeroMap (k : Type u) [Field k] (n : ℕ)
    {F G : (projectiveSpaceOverRing n (.of k)).Modules} (φ : F ⟶ G) :
    projectiveH k n F 0 ⟶ projectiveH k n G 0 :=
  cohomologyOverFieldMap k (projectiveSpaceToBase k n) φ 0

/-- **Multiplication of a class in `H⁰(ℙⁿ_k, ℱ(d))` by a global section of `𝒪(1)`**, the map of
[Stacks, Tag 08A7], as the map on `H⁰` induced by
`Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.twistSectionMul`. -/
abbrev mulSection (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules)
    (s : (twistOver n (Spec (.of k)) 1).sections) (d : ℤ) :
    projectiveH k n (projectiveTwist n F d) 0 ⟶
      projectiveH k n (projectiveTwist n F (d + 1)) 0 :=
  projectiveHZeroMap k n (twistSectionMul n (Spec (.of k)) F s d)

/-- The `k`-subspace of `H⁰(ℙⁿ_k, ℱ(d+1))` spanned by the products `s · a` of a global section
`s` of `𝒪(1)` with a class `a ∈ H⁰(ℙⁿ_k, ℱ(d))`. Tag 08A7 asserts that this is everything, which
is surjectivity of the multiplication map out of `H⁰(ℱ(d)) ⊗_k H⁰(𝒪(1))`. -/
def mulSectionsSpan (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) (d : ℤ) :
    Submodule k ↑(projectiveH k n (projectiveTwist n F (d + 1)) 0) :=
  Submodule.span k
    {t | ∃ (s : (twistOver n (Spec (.of k)) 1).sections)
        (a : ↑(projectiveH k n (projectiveTwist n F d) 0)),
      t = ConcreteCategory.hom (mulSection k n F s d) a}

/-- The product `s · a` of a global section `s` of `𝒪(1)` with a class `a ∈ H⁰(ℙⁿ_k, ℱ(d))` lies
in `mulSectionsSpan k n F d`. -/
theorem mem_mulSectionsSpan (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) (d : ℤ)
    (s : (twistOver n (Spec (.of k)) 1).sections)
    (a : ↑(projectiveH k n (projectiveTwist n F d) 0)) :
    ConcreteCategory.hom (mulSection k n F s d) a ∈ mulSectionsSpan k n F d :=
  Submodule.subset_span ⟨s, a, rfl⟩

/-! ### The step at which `m`-regularity is used -/

/-- **The one place `m`-regularity enters the proof of [Stacks, Tag 08A7].** If `ℱ` is
`m`-regular on `ℙⁿ_k` with `n ≥ 1`, and `0 ⟶ ℱ(m-1) ⟶ ℱ(m) ⟶ 𝒬 ⟶ 0` is short exact, then
`H⁰(ℙⁿ_k, ℱ(m)) ⟶ H⁰(ℙⁿ_k, 𝒬)` is surjective.

`m`-regularity gives `H¹(ℙⁿ_k, ℱ(m-1)) = 0`, so the connecting map out of `H⁰(ℙⁿ_k, 𝒬)` in the
long exact sequence is zero and exactness there forces surjectivity. In [Stacks, Tag 08A7] the
sequence is the twisted hyperplane restriction sequence and `𝒬 = i_*𝒢(m)`, so this is the step
that lifts a section of `𝒢(m)` on the hyperplane to a section of `ℱ(m)`. -/
theorem surjective_cohomologyOverFieldMap_zero_of_isMRegular
    (k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] (m : ℤ)
    (hF : IsMRegular k n F m)
    (S : ShortComplex (projectiveSpaceOverRing n (.of k)).Modules)
    (hS : S.ShortExact) (hX₁ : S.X₁ = projectiveTwist n F (m - 1)) :
    Function.Surjective
      (ConcreteCategory.hom (cohomologyOverFieldMap k (projectiveSpaceToBase k n) S.g 0)) := by
  obtain ⟨d, _, _, hex, _⟩ :=
    exists_cohomologyOverField_longExactSequence k (projectiveSpaceToBase k n) hS
  have hvan : IsZero (projectiveH k n S.X₁ 1) := by
    rw [hX₁]
    refine (isZero_cohomologyOverField_iff_isZero_hgroup k (projectiveSpaceToBase k n)
      (projectiveTwist n F (m - 1)) 1).mpr ?_
    have h := hF 1 le_rfl hn
    have he : m - ((1 : ℕ) : ℤ) = m - 1 := by push_cast; ring
    rwa [he] at h
  intro t
  have hzero : ConcreteCategory.hom (d 0) t = 0 := by
    have hd : d 0 = 0 := hvan.eq_zero_of_tgt _
    rw [hd]; rfl
  exact (hex 0 t).mp hzero

/-! ### The base case `n = 0` -/

/-- Tensoring on the right by a morphism of modules is the library's functorial tensor
isomorphism when that morphism is an isomorphism; both are
`Stacks.RingedSpace.tensorSheaf` applied to the pair `(𝟙, e.hom)`. -/
theorem hom_tensorModulesMapIso_refl (n : ℕ) (S : Scheme.{u})
    (A : (projectiveSpaceOver n S).Modules) {B C : (projectiveSpaceOver n S).Modules}
    (e : B ≅ C) :
    (tensorModulesMapIso (projectiveSpaceOver n S) (Iso.refl A) e).hom
      = tensorRightOfHom n S A e.hom := rfl

/-- Tensoring on the right by an isomorphism of modules is an isomorphism. -/
theorem isIso_tensorRightOfHom (n : ℕ) (S : Scheme.{u})
    (A : (projectiveSpaceOver n S).Modules) {B C : (projectiveSpaceOver n S).Modules}
    (e : B ≅ C) : IsIso (tensorRightOfHom n S A e.hom) :=
  hom_tensorModulesMapIso_refl n S A e ▸
    (tensorModulesMapIso (projectiveSpaceOver n S) (Iso.refl A) e).isIso_hom

/-- The same identification for a morphism out of the structure sheaf. -/
theorem hom_tensorModulesMapIso_unit (n : ℕ) (S : Scheme.{u})
    (A : (projectiveSpaceOver n S).Modules) {B : (projectiveSpaceOver n S).Modules}
    (e : SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf ≅ B) :
    (tensorModulesMapIso (projectiveSpaceOver n S) (Iso.refl A) e).hom
      = tensorRightOfUnitHom n S A e.hom := rfl

/-- Tensoring on the right by an isomorphism out of the structure sheaf is an isomorphism. -/
theorem isIso_tensorRightOfUnitHom (n : ℕ) (S : Scheme.{u})
    (A : (projectiveSpaceOver n S).Modules) {B : (projectiveSpaceOver n S).Modules}
    (e : SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf ≅ B) :
    IsIso (tensorRightOfUnitHom n S A e.hom) :=
  hom_tensorModulesMapIso_unit n S A e ▸
    (tensorModulesMapIso (projectiveSpaceOver n S) (Iso.refl A) e).isIso_hom

/-- The global section of `𝒪(1)` on `ℙ⁰_S` corresponding to the identity of the structure sheaf
under the trivialisation `AlgebraicGeometry.projectiveTwistingSheafZeroIsoUnit`. On `ℙ⁰` this is
the section the source calls `T₀`: it generates `𝒪(1)`. -/
def generatingSectionZero (S : Scheme.{u}) : (twistOver 0 S 1).sections :=
  (twistOver 0 S 1).unitHomEquiv (projectiveTwistingSheafZeroIsoUnit S 1).inv

/-- **Multiplication by the generating section of `𝒪(1)` on `ℙ⁰_S` is an isomorphism.** On `ℙ⁰`
the sheaf `𝒪(1)` is trivial (`AlgebraicGeometry.projectiveTwistingSheafZeroIsoUnit`), so the
section corresponding to the identity of the structure sheaf makes every factor of
`twistSectionMul` an isomorphism. -/
theorem isIso_twistSectionMul_zero (S : Scheme.{u})
    (F : (projectiveSpaceOver 0 S).Modules) (d : ℤ) :
    IsIso (twistSectionMul 0 S F (generatingSectionZero S) d) := by
  have hsec : sectionHom (twistOver 0 S 1) (generatingSectionZero S)
      = (projectiveTwistingSheafZeroIsoUnit S 1).symm.hom :=
    (twistOver 0 S 1).unitHomEquiv.symm_apply_apply _
  -- the four factors of `twistSectionMul` are the four components of this composite isomorphism
  let e :=
    (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor
        (projectiveSpaceOver 0 S).presheaf (projectiveSpaceOver 0 S).ringCatSheaf.property
        (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver 0 S) F
          (twistOver 0 S d))).symm ≪≫
      (tensorModulesMapIso (projectiveSpaceOver 0 S) (Iso.refl _)
          (projectiveTwistingSheafZeroIsoUnit S 1).symm ≪≫
        (Stacks.SheafOfModules.Invertible.tensorProductAssociator
            (projectiveSpaceOver 0 S).presheaf (projectiveSpaceOver 0 S).ringCatSheaf.property
            F (twistOver 0 S d) (twistOver 0 S 1) ≪≫
          tensorModulesMapIso (projectiveSpaceOver 0 S) (Iso.refl F)
            (twistOverMulIso 0 S d 1)))
  have hcomp : twistSectionMul 0 S F (generatingSectionZero S) d = e.hom := by
    rw [twistSectionMul, hsec]
    rfl
  exact hcomp ▸ e.isIso_hom

/-- **[Stacks, Tag 08A7] in the base case `n = 0`.** On `ℙ⁰_k` the sheaf `𝒪(1)` is trivial, so
multiplication by a generating section is already an isomorphism `ℱ(d) ≅ ℱ(d+1)` on `H⁰`; no
regularity hypothesis is needed. This is the source's remark that for `n = 0` the claim is
immediate because `𝒪(1) ≅ 𝒪` and `T₀` generates it. -/
theorem span_mulSections_eq_top_of_isMRegular_zero (k : Type u) [Field k]
    (F : (projectiveSpaceOverRing 0 (.of k)).Modules) (d : ℤ) :
    mulSectionsSpan k 0 F d = ⊤ := by
  set s := generatingSectionZero (Spec (.of k)) with hs
  have hiso : IsIso (twistSectionMul 0 (Spec (.of k)) F s d) :=
    isIso_twistSectionMul_zero (Spec (.of k)) F d
  refine eq_top_iff.2 fun t _ => ?_
  have hsurj : ConcreteCategory.hom (mulSection k 0 F s d)
      (ConcreteCategory.hom (projectiveHZeroMap k 0
        (inv (twistSectionMul 0 (Spec (.of k)) F s d))) t) = t := by
    have hcomp : projectiveHZeroMap k 0 (inv (twistSectionMul 0 (Spec (.of k)) F s d)) ≫
        mulSection k 0 F s d = 𝟙 _ := by
      rw [mulSection, projectiveHZeroMap, projectiveHZeroMap,
        ← cohomologyOverFieldMap_comp, IsIso.inv_hom_id, cohomologyOverFieldMap_id]
    exact ConcreteCategory.congr_hom hcomp t
  rw [← hsurj]
  exact mem_mulSectionsSpan k 0 F d s _

/-! ### The hyperplane restriction data, carried -/

/-- **The hyperplane restriction data of [Stacks, Tag 08A0], twisted as in [Stacks, Tag 0EGK]
and read on degree-zero cohomology through [Stacks, Tag 089Z].**

For a coherent `ℱ` on `ℙ^{n+1}_k` this bundles: a coherent `𝒢` on `ℙⁿ_k`, an affine morphism
`j : ℙⁿ_k ⟶ ℙ^{n+1}_k` presenting the hyperplane and identifying it with `ℙⁿ_k`, a global
section `s` of `𝒪(1)` cutting it out, the twisted restriction sequences
`0 ⟶ ℱ(d) ⟶ ℱ(d+1) ⟶ j_*(𝒢(d+1)) ⟶ 0` whose first arrow is multiplication by `s`, the
comparison of `H⁰(ℙ^{n+1}_k, j_*(𝒢(d)))` with `H⁰(ℙⁿ_k, 𝒢(d))`, and the fact that every
degree-one form on the hyperplane is the restriction of one upstairs, compatibly with
multiplication.

Over an infinite field every clause but `liftSection` is proved elsewhere in this repository and
assembled by `AlgebraicGeometry.nonempty_hyperplaneRestrictionPackage_of_liftSection`; see the
module documentation for where each comes from. The index is written `n + 1` rather than `n` with
`1 ≤ n` so that the hyperplane is `ℙⁿ_k` with no truncated subtraction. -/
structure HyperplaneRestrictionPackage (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing (n + 1) (.of k)).Modules) where
  /-- The restriction of `ℱ` to the hyperplane, transported to `ℙⁿ_k`. -/
  G : (projectiveSpaceOverRing n (.of k)).Modules
  /-- `𝒢` is coherent. -/
  isCoherent : G.IsCoherent
  /-- The hyperplane inclusion, composed with the identification of [Stacks, Tag 089Z]. -/
  j : projectiveSpaceOverRing n (.of k) ⟶ projectiveSpaceOverRing (n + 1) (.of k)
  /-- A closed immersion is affine, which is what the cohomology comparison needs. -/
  isAffineHom : IsAffineHom j
  /-- The global section of `𝒪(1)` cutting out the hyperplane. -/
  s : (twistOver (n + 1) (Spec (.of k)) 1).sections
  /-- The restriction arrow `ℱ(d) ⟶ j_*(𝒢(d))`. -/
  res : ∀ d : ℤ, projectiveTwist (n + 1) F d ⟶
    (Scheme.Modules.pushforward j).obj (projectiveTwist n G d)
  /-- Multiplication by `s` followed by restriction vanishes. -/
  comp_res : ∀ d : ℤ,
    twistSectionMul (n + 1) (Spec (.of k)) F s d ≫ res (d + 1) = 0
  /-- The twisted restriction sequence is short exact. -/
  shortExact : ∀ d : ℤ, (ShortComplex.mk
    (twistSectionMul (n + 1) (Spec (.of k)) F s d) (res (d + 1)) (comp_res d)).ShortExact
  /-- The same sequences indexed by their middle term, `0 ⟶ ℱ(d-1) ⟶ ℱ(d) ⟶ j_*(𝒢(d)) ⟶ 0`.
  This is the same carried data as `shortExact`, reindexed; only exactness is used from it, so
  the first arrow is not named. -/
  shortExact' : ∀ d : ℤ,
    ∃ (a : projectiveTwist (n + 1) F (d - 1) ⟶ projectiveTwist (n + 1) F d)
      (w : a ≫ res d = 0), (ShortComplex.mk a (res d) w).ShortExact
  /-- `H⁰` of the direct image is `H⁰` on the hyperplane, a closed immersion being affine. -/
  compare : ∀ d : ℤ, projectiveH k n (projectiveTwist n G d) 0 ≅
    projectiveH k (n + 1) ((Scheme.Modules.pushforward j).obj (projectiveTwist n G d)) 0
  /-- Every degree-one form on the hyperplane is the restriction of one upstairs, and
  restriction intertwines the two multiplications. -/
  liftSection : ∀ σ : (twistOver n (Spec (.of k)) 1).sections,
    ∃ σ' : (twistOver (n + 1) (Spec (.of k)) 1).sections, ∀ d : ℤ,
      mulSection k (n + 1) F σ' d ≫ projectiveHZeroMap k (n + 1) (res (d + 1))
        = projectiveHZeroMap k (n + 1) (res d) ≫ (compare d).inv ≫
            mulSection k n G σ d ≫ (compare (d + 1)).hom

/-- The restriction sequences of a `AlgebraicGeometry.HyperplaneRestrictionPackage` are exactly
the sequences that [Stacks, Tag 08A5] consumes. -/
theorem hasHyperplaneRestrictionSequences_of_package (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing (n + 1) (.of k)).Modules)
    (P : HyperplaneRestrictionPackage k n F) :
    HasHyperplaneRestrictionSequences (n + 1) F P.G P.j := by
  intro d
  obtain ⟨a, w, hse⟩ := P.shortExact' d
  exact ⟨a, P.res d, w, hse⟩

/-- The restriction map `H⁰(ℙ^{n+1}_k, ℱ(d)) ⟶ H⁰(ℙⁿ_k, 𝒢(d))` of a package: restriction to the
hyperplane followed by the comparison with cohomology on `ℙⁿ_k`. -/
abbrev HyperplaneRestrictionPackage.resH {k : Type u} [Field k] {n : ℕ}
    {F : (projectiveSpaceOverRing (n + 1) (.of k)).Modules}
    (P : HyperplaneRestrictionPackage k n F) (d : ℤ) :
    projectiveH k (n + 1) (projectiveTwist (n + 1) F d) 0 ⟶
      projectiveH k n (projectiveTwist n P.G d) 0 :=
  projectiveHZeroMap k (n + 1) (P.res d) ≫ (P.compare d).inv

/-! ### Tag 08A7 -/

/-- **[Stacks, Tag 08A7].** Let `k` be a field, `n ≥ 0` and `ℱ` a coherent sheaf on `ℙⁿ_k`. If
`ℱ` is `m`-regular then the multiplication map

`H⁰(ℙⁿ_k, ℱ(m)) ⊗_k H⁰(ℙⁿ_k, 𝒪(1)) ⟶ H⁰(ℙⁿ_k, ℱ(m+1))`

is surjective — equivalently, the `k`-span of the products is everything.

The proof is the source's induction on `n`. For `n = 0` multiplication by a generator of the
trivial sheaf `𝒪(1)` is already an isomorphism. For the step, the inductive hypothesis writes the
restriction of a class `t ∈ H⁰(ℱ(m+1))` to the hyperplane as a combination of products
`σ · g`; each `g` lifts to `ℙ^{n+1}_k` because `m`-regularity makes `H¹(ℱ(m-1))` vanish, each `σ`
lifts by [Stacks, Tag 089Z], and subtracting the lifted combination leaves a class restricting to
zero, which by exactness of the restriction sequence is `s` times a class in `H⁰(ℱ(m))`. -/
@[stacks 08A7 "for an arbitrary field, with the hyperplane restriction data of Tags 08A0, 0EGK \
and 089Z carried in `HyperplaneRestrictionPackage`; the induction on `n`, the base case and the \
use of `m`-regularity to lift a section off the hyperplane are proved. Over an infinite field \
every clause of that package but `liftSection` is proved too -- see \
`AlgebraicGeometry.exists_hyperplaneRestrictionData`. Surjectivity out of the tensor product is \
stated as the `k`-span of the products being `⊤`."]
theorem span_mulSections_eq_top_of_isMRegular (k : Type u) [Field k]
    (pkg : ∀ (n : ℕ) (F : (projectiveSpaceOverRing (n + 1) (.of k)).Modules),
      F.IsCoherent → Nonempty (HyperplaneRestrictionPackage k n F)) :
    ∀ (n : ℕ) (F : (projectiveSpaceOverRing n (.of k)).Modules) (hFc : F.IsCoherent) (m : ℤ),
      @IsMRegular k _ n F hFc m → mulSectionsSpan k n F m = ⊤ := by
  intro n
  induction n with
  | zero => exact fun F _ m _ => span_mulSections_eq_top_of_isMRegular_zero k F m
  | succ n ih =>
    intro F hFc m hF
    have := hFc
    obtain ⟨P⟩ := pkg n F hFc
    have := P.isCoherent
    have := P.isAffineHom
    -- [Stacks, Tag 08A5]: the restriction to the hyperplane is `m`-regular.
    have hG : @IsMRegular k _ n P.G P.isCoherent m :=
      isMRegular_of_hyperplaneRestriction k (n + 1) (Nat.le_add_left 1 n) F m P.G P.j
        (hasHyperplaneRestrictionSequences_of_package k n F P) hF
    -- the inductive hypothesis on the hyperplane
    have hspanG : mulSectionsSpan k n P.G m = ⊤ := ih P.G P.isCoherent m hG
    set T := mulSectionsSpan k (n + 1) F m with hT
    set ψ := ConcreteCategory.hom (P.resH (m + 1)) with hψ
    -- `m`-regularity lifts a class off the hyperplane in degree `m`.
    have hsurjm : Function.Surjective (ConcreteCategory.hom (P.resH m)) := by
      obtain ⟨a, w, hse⟩ := P.shortExact' m
      have hX₁ : (ShortComplex.mk a (P.res m) w).X₁
          = projectiveTwist (n + 1) F (m - 1) := rfl
      have h := surjective_cohomologyOverFieldMap_zero_of_isMRegular k (n + 1)
        (Nat.le_add_left 1 n) F m hF _ hse hX₁
      exact fun g => by
        obtain ⟨a, ha⟩ := h (ConcreteCategory.hom (P.compare m).hom g)
        refine ⟨a, ?_⟩
        have : ConcreteCategory.hom (P.resH m) a
            = ConcreteCategory.hom (P.compare m).inv
              (ConcreteCategory.hom (projectiveHZeroMap k (n + 1) (P.res m)) a) := rfl
        rw [this, ha]
        exact (P.compare m).hom_inv_id_apply g
    -- Claim A: every product on the hyperplane is `ψ` of a product upstairs.
    have hA : mulSectionsSpan k n P.G m ≤ T.map ψ := by
      rw [mulSectionsSpan, Submodule.span_le]
      rintro x ⟨σ, g, rfl⟩
      obtain ⟨σ', hσ'⟩ := P.liftSection σ
      obtain ⟨f, hf⟩ := hsurjm g
      refine ⟨ConcreteCategory.hom (mulSection k (n + 1) F σ' m) f,
        mem_mulSectionsSpan k (n + 1) F m σ' f, ?_⟩
      -- restriction intertwines multiplication by `σ'` upstairs with multiplication by `σ`
      have hmor : mulSection k (n + 1) F σ' m ≫ P.resH (m + 1)
          = P.resH m ≫ mulSection k n P.G σ m := by
        change mulSection k (n + 1) F σ' m ≫
            projectiveHZeroMap k (n + 1) (P.res (m + 1)) ≫ (P.compare (m + 1)).inv
          = (projectiveHZeroMap k (n + 1) (P.res m) ≫ (P.compare m).inv) ≫
              mulSection k n P.G σ m
        rw [← Category.assoc, hσ' m]
        simp
      have happ : ConcreteCategory.hom (P.resH (m + 1))
            (ConcreteCategory.hom (mulSection k (n + 1) F σ' m) f)
          = ConcreteCategory.hom (mulSection k n P.G σ m)
            (ConcreteCategory.hom (P.resH m) f) :=
        ConcreteCategory.congr_hom hmor f
      rw [hψ, happ, hf]
    -- Claim B: `ψ` maps `T` onto everything.
    have hB : T.map ψ = ⊤ := by
      refine eq_top_iff.2 ?_
      rw [← hspanG]
      exact hA
    -- Claim C: the kernel of `ψ` is already in `T`, by exactness of the restriction sequence.
    have hC : LinearMap.ker ψ ≤ T := by
      intro x hx
      obtain ⟨_, _, hex, _, _⟩ :=
        exists_cohomologyOverField_longExactSequence k (projectiveSpaceToBase k (n + 1))
          (P.shortExact m)
      have hx0 : ConcreteCategory.hom
          (projectiveHZeroMap k (n + 1) (P.res (m + 1))) x = 0 := by
        have h1 : ConcreteCategory.hom (P.compare (m + 1)).inv
            (ConcreteCategory.hom (projectiveHZeroMap k (n + 1) (P.res (m + 1))) x) = 0 :=
          LinearMap.mem_ker.1 hx
        rw [← (P.compare (m + 1)).inv_hom_id_apply
          (ConcreteCategory.hom (projectiveHZeroMap k (n + 1) (P.res (m + 1))) x), h1, map_zero]
      obtain ⟨f, hf⟩ := (hex 0 x).mp hx0
      exact hf ▸ mem_mulSectionsSpan k (n + 1) F m P.s f
    -- Claims B and C give everything.
    refine eq_top_iff.2 fun t _ => ?_
    obtain ⟨t', ht', hψt'⟩ : ∃ t' ∈ T, ψ t' = ψ t := by
      have : ψ t ∈ T.map ψ := hB ▸ Submodule.mem_top
      obtain ⟨t', ht', h⟩ := this
      exact ⟨t', ht', h⟩
    have hker : t - t' ∈ LinearMap.ker ψ := by
      rw [LinearMap.mem_ker, map_sub, hψt', sub_self]
    have := T.add_mem (hC hker) ht'
    simpa using this

end AlgebraicGeometry

end
