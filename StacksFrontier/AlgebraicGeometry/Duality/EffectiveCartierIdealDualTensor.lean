module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDerivedSheafHomIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjects
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatFinitelyPresentedSummands
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocallyFiniteFreeSummandSource

/-!
# Invertible modules are perfect, and the tensor-dual formula at `i_* 𝒪_D`

Let `(C, O)` be a ringed site. An invertible sheaf of `O`-modules placed in a single degree is a
perfect object of `D(O)`: it is only *locally* a direct summand of a finite free module, never
globally, so the complex it generates is only locally strictly perfect, which is exactly what
perfectness asks for. More generally the third term of a short exact sequence whose first two
terms are invertible is a perfect object when placed in degree zero, the cone of the first map
being a two-term complex which is strictly perfect on a covering.

The consequence drawn here is the clause `M ⊗^L_O E^∨ ≅ R ℰom_O(E, M)` of
[Stacks, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ) — the same assertion as clause (3)
of [Stacks, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ), which
`AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso` proves for every perfect `E` — read
first at `E = ℐ_D`, the ideal sheaf of an effective Cartier divisor `D ⊆ X` on a scheme, and
then at `E = i_* 𝒪_D`, whose class in `D(𝒪_X)` is that of the two-term complex `(ℐ_D ⟶ 𝒪_X)`.
The second reading is the whole content of the source's proof of
[Stacks, Tag 0AA4](https://stacks.math.columbia.edu/tag/0AA4) on `X`: it gives

`R ℰom_{𝒪_X}(i_* 𝒪_D, K) ≅ K ⊗^L_{𝒪_X} (i_* 𝒩)[-1]`

for every `K`, the derived dual of `i_* 𝒪_D` being `(i_* 𝒩)[-1]` by
`Stacks.Divisors.idealDerivedSheafHomIso`.

## Main results

* `AlgebraicGeometry.RingedSite.isStrictlyPerfect_single`: a module which is a direct summand of
  a finite free module, placed in a single degree, is a strictly perfect complex.
* `AlgebraicGeometry.RingedSite.isPerfectComplex_single_of_isInvertible` and
  `AlgebraicGeometry.RingedSite.isPerfect_singleFunctor_of_isInvertible`: an invertible sheaf of
  modules placed in a single degree is a perfect complex, hence a perfect object of `D(O)`.
* `AlgebraicGeometry.RingedSite.isPerfectComplex_mappingCone_single` and
  `AlgebraicGeometry.RingedSite.isPerfect_singleFunctor_of_shortExact_isInvertible`: the cone of
  a morphism of single complexes on locally finite free summands is a perfect complex, so the
  third term of a short exact sequence of invertible modules is a perfect object of `D(O)`.
* `Stacks.Divisors.isPerfect_singleFunctor_idealShortComplex_X₃`: **`(i_* 𝒪_D)[0]` is a perfect
  object of `D(𝒪_X)`** for `D ⊆ X` an effective Cartier divisor.
* `Stacks.Divisors.idealDualTensorIso`: `K ⊗^L_{𝒪_X} R ℰom(ℐ_D, 𝒪_X) ≅ R ℰom(ℐ_D, K)`, for every
  `K` in `D(𝒪_X)`.
* `Stacks.Divisors.divisorQuotientDualTensorIso`:
  `R ℰom_{𝒪_X}(i_* 𝒪_D, K) ≅ K ⊗^L_{𝒪_X} (i_* 𝒩)[-1]`, for every `K` in `D(𝒪_X)`.

## Implementation notes

The covering on which the single complex is strictly perfect is the canonical family
`Stacks.SheafOfModules.invertibleSummandObj` of objects carrying a finite free splitting of the
invertible module, which covers the final object by
`Stacks.SheafOfModules.coversTop_invertibleSummandObj`; the sieve of arrows factoring through a
member is covering for *every* object, which is what Mathlib's
`CategoryTheory.GrothendieckTopology.CoversTop` says, and strict perfectness of a restriction
passes down an arrow by
`AlgebraicGeometry.RingedSite.InvertibleDerived.isStrictlyPerfect_restrictComplex`. The passage
from the complex to the module in the single degree is
`AlgebraicGeometry.RingedSite.restrictSingleIso`.

For the two-term complex the same covering argument is run on the *intersection* of the two
sieves `AlgebraicGeometry.RingedSite.summandSieve` trivializing the two terms — a Grothendieck
topology is closed under intersections — and the cone is formed before restricting: restriction
to a slice is additive, so it commutes with the cone by
`HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso`, and the restricted cone is
strictly perfect by [Stacks, Tag 08FM] (`mappingCone_isStrictlyPerfect`). That the cone
represents the third term is Mathlib's `CochainComplex.mappingCone.descShortComplex`, a
quasi-isomorphism exactly because the sequence is short exact, so no comparison of
distinguished triangles is needed either.

`Stacks.Divisors.idealShortComplex` is a plain definition, so instance search does not reach
through its projections; the invertibility of its first two terms is therefore supplied as
`local instance`s at the spellings `(idealShortComplex D).X₁` and `(idealShortComplex D).X₂`.

The universes are the diagonal `RingedSite.{u, u, u}`, which is the pin of
`AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso` and of
`AlgebraicGeometry.RingedSite.InvertibleDerived`; the perfectness cluster built on local
*models* — `AlgebraicGeometry.RingedSite.isPerfect_of_locally`,
`AlgebraicGeometry.RingedSite.isPerfectComplex_of_isPerfect_representation` and
`AlgebraicGeometry.RingedSite.isPerfect_obj₃_of_distinguished` — is pinned at module universe
`0` instead and is therefore unavailable here, which is why the covering argument is run
directly rather than through the closure of perfectness under distinguished triangles.

No `@[stacks]` attribute is carried below. The isomorphisms of
`Stacks.Divisors.idealDualTensorIso` and `Stacks.Divisors.divisorQuotientDualTensorIso` are
instantiations of `derivedDualTensorSheafHomIso`, which already carries the attribute for the
general perfect source, and the perfectness statements are the single-degree invertible case of
the general statement of [Stacks, Tag 0FPY] that
`AlgebraicGeometry.RingedSite.InvertibleDerived.isPerfect_of_hasInvertibleModuleDecomposition`
carries. In particular `divisorQuotientDualTensorIso` is **not** the isomorphism assertion of
[Stacks, Tag 0AA4], which is about `R ℰom(𝒪_D, K)` on `D` and not about `R ℰom_{𝒪_X}(i_* 𝒪_D, K)`
on `X`; it is the step of that tag's proof which the two sides are compared through.

## References

* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08FM](https://stacks.math.columbia.edu/tag/08FM)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
* [Stacks Project, Tag 0AA4](https://stacks.math.columbia.edu/tag/0AA4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

universe u d

namespace AlgebraicGeometry.RingedSite

section Single

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A module placed in a single degree is a strictly perfect complex as soon as the module is a
direct summand of a finite free module. -/
theorem isStrictlyPerfect_single (k : ℤ) {M : SheafOfModules.{u} R}
    (hM : IsDirectSummandOfFiniteFree R M) :
    IsStrictlyPerfect R ((HomologicalComplex.single (SheafOfModules.{u} R)
      (ComplexShape.up ℤ) k).obj M) where
  bounded := (Set.finite_singleton k).subset (fun i hi => by
    by_contra hik
    exact hi (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) k M i hik))
  termDirectSummand i := by
    by_cases hik : i = k
    · subst hik
      exact IsDirectSummandOfFiniteFree.of_iso R
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i M) hM
    · refine Stacks.SheafOfModules.isDirectSummandOfFiniteFree_of_retract_free R _
        PEmpty.{u + 1} 0 0 ?_
      rw [zero_comp]
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) k M i hik).eq_of_src _ _

end Single

section Perfect

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **An invertible sheaf of modules placed in a single degree is a perfect complex.** -/
theorem isPerfectComplex_single_of_isInvertible (k : ℤ)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L] :
    X.IsPerfectComplex ((HomologicalComplex.single (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) k).obj L) := by
  refine InvertibleDerived.isPerfectComplex_of_strictlyPerfectSieve _ (fun U => ?_)
  refine X.J.superset_covering ?_
    (Stacks.SheafOfModules.coversTop_invertibleSummandObj X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L U)
  rintro W f ⟨j, ⟨g⟩⟩
  refine InvertibleDerived.isStrictlyPerfect_restrictComplex g ?_
  refine InvertibleDerived.isStrictlyPerfect_of_iso _ (restrictSingleIso X L _ k).symm
    (isStrictlyPerfect_single _ k ?_)
  exact Stacks.SheafOfModules.isDirectSummandOfFiniteFree_of_retract_free _ _ _
    (Stacks.SheafOfModules.invertibleSummandRetract j).i
    (Stacks.SheafOfModules.invertibleSummandRetract j).r
    (Stacks.SheafOfModules.invertibleSummandRetract j).retract

/-- The sieve of arrows over whose source a sheaf of modules restricts to a direct summand of a
finite free module. It is a sieve because that property passes along an arrow of the site, by
`AlgebraicGeometry.RingedSite.InvertibleDerived.isDirectSummandOfFiniteFree_over`. -/
def summandSieve (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) : Sieve U where
  arrows W _ := IsDirectSummandOfFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)
    (M.over W)
  downward_closed hf g := InvertibleDerived.isDirectSummandOfFiniteFree_over g hf

/-- **An invertible sheaf of modules is, on a covering of every object, a direct summand of a
finite free module.** This is [Stacks, Tag 0B8N] in the form of a covering sieve: the objects
carrying a finite free splitting cover the final object, so the sieve of arrows factoring
through one of them is covering above every object, and it is contained in the sieve above. -/
theorem summandSieve_mem_of_isInvertible
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property M] (U : X.C) :
    summandSieve X M U ∈ X.J U := by
  refine X.J.superset_covering ?_
    (Stacks.SheafOfModules.coversTop_invertibleSummandObj X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property M U)
  rintro W f ⟨j, ⟨g⟩⟩
  exact InvertibleDerived.isDirectSummandOfFiniteFree_over g
    (Stacks.SheafOfModules.isDirectSummandOfFiniteFree_of_retract_free _ _ _
      (Stacks.SheafOfModules.invertibleSummandRetract j).i
      (Stacks.SheafOfModules.invertibleSummandRetract j).r
      (Stacks.SheafOfModules.invertibleSummandRetract j).retract)

/-- Sheaves of modules on a site have binary biproducts: they form an abelian category, hence
have binary products, and a preadditive category with binary products has binary biproducts.
This is what makes the mapping cone of a morphism of complexes of `O`-modules exist. -/
local instance hasBinaryBiproducts_sheafOfModules
    {C' : Type u} [Category.{u} C'] {J' : GrothendieckTopology C'} (R : Sheaf J' RingCat.{u})
    [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    HasBinaryBiproducts (SheafOfModules.{u} R) :=
  ⟨fun P Q => HasBinaryBiproduct.of_hasBinaryProduct P Q⟩

/-- **The cone of a morphism of two single-degree complexes which are locally direct summands
of finite free modules is a perfect complex.**

Above an object of the site over which both modules are direct summands of finite free modules
the two single complexes are strictly perfect (`isStrictlyPerfect_single`), hence so is the cone
of the restricted morphism by [Stacks, Tag 08FM] (`mappingCone_isStrictlyPerfect`); restriction
to a slice commutes with the cone, by
`HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso`, so the restriction of the cone
is strictly perfect there. Those objects form a covering sieve above every object, being the
intersection of the two covering sieves `summandSieve`. -/
theorem isPerfectComplex_mappingCone_single (k : ℤ)
    {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : A ⟶ B)
    (hA : ∀ U : X.C, summandSieve X A U ∈ X.J U)
    (hB : ∀ U : X.C, summandSieve X B U ∈ X.J U) :
    X.IsPerfectComplex (CochainComplex.mappingCone
      ((HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) k).map f)) := by
  refine InvertibleDerived.isPerfectComplex_of_strictlyPerfectSieve _ fun U => ?_
  refine X.J.superset_covering ?_ (X.J.intersection_covering (hA U) (hB U))
  intro W g hg
  have hA' : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)
      (X.restrictComplex ((HomologicalComplex.single (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) k).obj A) W) :=
    InvertibleDerived.isStrictlyPerfect_of_iso _ (restrictSingleIso X A W k).symm
      (isStrictlyPerfect_single _ k hg.1)
  have hB' : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)
      (X.restrictComplex ((HomologicalComplex.single (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) k).obj B) W) :=
    InvertibleDerived.isStrictlyPerfect_of_iso _ (restrictSingleIso X B W k).symm
      (isStrictlyPerfect_single _ k hg.2)
  exact InvertibleDerived.isStrictlyPerfect_of_iso _
    (HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso _
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W)).symm
    (mappingCone_isStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) _ hA' hB')

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **An invertible sheaf of modules placed in a single degree is a perfect object of `D(O)`.** -/
theorem isPerfect_singleFunctor_of_isInvertible (k : ℤ)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L] :
    X.IsPerfect ((DerivedCategory.singleFunctor (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k).obj L) :=
  ⟨_, isPerfectComplex_single_of_isInvertible X k L, ⟨Iso.refl _⟩⟩

/-- **The third term of a short exact sequence whose first two terms are invertible sheaves of
modules is a perfect object of `D(O)` when placed in degree zero.**

The two-term complex formed by the first map represents that third term: the cone of the
morphism of single complexes maps to the single complex on the third term by
`CochainComplex.mappingCone.descShortComplex`, which is a quasi-isomorphism because the sequence
is short exact. The cone is a perfect complex by
`AlgebraicGeometry.RingedSite.isPerfectComplex_mappingCone_single`, the two covering sieves being
supplied by `AlgebraicGeometry.RingedSite.summandSieve_mem_of_isInvertible`. -/
theorem isPerfect_singleFunctor_of_shortExact_isInvertible
    (S : ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hS : S.ShortExact)
    [Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property S.X₁]
    [Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property S.X₂] :
    X.IsPerfect
      ((DerivedCategory.singleFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj S.X₃) := by
  have hS' := hS.map_of_exact (HomologicalComplex.single (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ComplexShape.up ℤ) 0)
  have := CochainComplex.mappingCone.quasiIso_descShortComplex (S := _) hS'
  have hiso : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex
      (S.map (HomologicalComplex.single (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) 0)))) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  exact ⟨_, isPerfectComplex_mappingCone_single X 0 S.f
      (summandSieve_mem_of_isInvertible X S.X₁) (summandSieve_mem_of_isInvertible X S.X₂),
    ⟨@asIso _ _ _ _ _ hiso⟩⟩

end Perfect

end AlgebraicGeometry.RingedSite

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-- **[Stacks, Tag 08DQ], the clause `M ⊗ᴸ E^∨ ≅ R ℰom(E, M)`, at the ideal sheaf of an
effective Cartier divisor.** -/
def idealDualTensorIso (K : DerivedCategory X.Modules) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor
          (Stacks.SheafOfModules.ringedSite X.sheaf)).obj K).obj
        (AlgebraicGeometry.RingedSite.derivedDual (Stacks.SheafOfModules.ringedSite X.sheaf)
          ((DerivedCategory.singleFunctor X.Modules 0).obj (negativeTwist' D))) ≅
      ((AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor
          (Stacks.SheafOfModules.ringedSite X.sheaf)).obj
        (op ((DerivedCategory.singleFunctor X.Modules 0).obj (negativeTwist' D)))).obj K :=
  AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso
    (Stacks.SheafOfModules.ringedSite X.sheaf)
    ((DerivedCategory.singleFunctor X.Modules 0).obj (negativeTwist' D)) K
    (AlgebraicGeometry.RingedSite.isPerfect_singleFunctor_of_isInvertible
      (Stacks.SheafOfModules.ringedSite X.sheaf) 0 (negativeTwist' D))

/-- The ideal sheaf of an effective Cartier divisor is invertible, at the spelling in which the
first term of the ideal short complex presents it. `Stacks.Divisors.idealShortComplex` is a
plain definition, so instance search does not reach through its first projection. -/
local instance isInvertible_idealShortComplex_X₁ :
    Stacks.SheafOfModules.IsInvertible (Stacks.SheafOfModules.ringedSite X.sheaf).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O).property
      (idealShortComplex D).X₁ :=
  isTensorInvertible_negativeTwist D

/-- The structure sheaf of `X`, as a module over itself, is invertible; at the spelling in which
the second term of the ideal short complex presents it. -/
local instance isInvertible_idealShortComplex_X₂ :
    Stacks.SheafOfModules.IsInvertible (Stacks.SheafOfModules.ringedSite X.sheaf).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O).property
      (idealShortComplex D).X₂ :=
  Stacks.SheafOfModules.isInvertible_unit _ _

/-- **`(i_* 𝒪_D)[0]` is a perfect object of `D(𝒪_X)`**, for `D ⊆ X` an effective Cartier
divisor.

Its class in `D(𝒪_X)` is that of the two-term complex `(ℐ_D ⟶ 𝒪_X)` of the ideal sequence
`0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0` ([Stacks, Tag 0C6K]), whose two terms are invertible, so this is
`AlgebraicGeometry.RingedSite.isPerfect_singleFunctor_of_shortExact_isInvertible` at that
sequence. It is the perfectness the proof of [Stacks, Tag 0AA4] invokes in order to apply the
tensor-dual clause of [Stacks, Tag 08DQ] to the source `i_* 𝒪_D`. -/
theorem isPerfect_singleFunctor_idealShortComplex_X₃ :
    (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect
      ((DerivedCategory.singleFunctor X.Modules 0).obj (idealShortComplex D).X₃) :=
  AlgebraicGeometry.RingedSite.isPerfect_singleFunctor_of_shortExact_isInvertible
    (Stacks.SheafOfModules.ringedSite X.sheaf) (idealShortComplex D)
    (idealShortComplex_shortExact D)

/-- **[Stacks, Tag 0AA4], the whole content of the source's proof of it on `X`:**

`R ℰom_{𝒪_X}(i_* 𝒪_D, K) ≅ K ⊗^L_{𝒪_X} (i_* 𝒩)[-1]`,

for every `K` in `D(𝒪_X)`, with `𝒩 = i^* 𝒪_X(D)` the normal sheaf of the effective Cartier
divisor `D ⊆ X`.

`i_* 𝒪_D` placed in degree zero is perfect
(`Stacks.Divisors.isPerfect_singleFunctor_idealShortComplex_X₃`), so the clause
`M ⊗^L E^∨ ≅ R ℰom(E, M)` of [Stacks, Tag 08DQ] — that is, clause (3) of [Stacks, Tag 08JJ],
`AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso` — applies at `E = i_* 𝒪_D`, and its
derived dual `R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X)` is `(i_* 𝒩)[-1]` by
`Stacks.Divisors.idealDerivedSheafHomIso`. -/
def divisorQuotientDualTensorIso (K : DerivedCategory X.Modules) :
    ((AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor
          (Stacks.SheafOfModules.ringedSite X.sheaf)).obj
        (op ((DerivedCategory.singleFunctor X.Modules 0).obj (idealShortComplex D).X₃))).obj K ≅
      ((Stacks.SheafOfModules.derivedTensorProductFunctor
          (Stacks.SheafOfModules.ringedSite X.sheaf)).obj K).obj
        ((DerivedCategory.singleFunctor X.Modules 1).obj (normalShortComplex D).X₃) := by
  let G : DerivedCategory X.Modules ⥤ DerivedCategory X.Modules :=
    (Stacks.SheafOfModules.derivedTensorProductFunctor
      (Stacks.SheafOfModules.ringedSite X.sheaf)).obj K
  exact (AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso
      (Stacks.SheafOfModules.ringedSite X.sheaf)
      ((DerivedCategory.singleFunctor X.Modules 0).obj (idealShortComplex D).X₃) K
      (isPerfect_singleFunctor_idealShortComplex_X₃ D)).symm ≪≫
    G.mapIso (idealDerivedSheafHomIso D)

end Stacks.Divisors

end
