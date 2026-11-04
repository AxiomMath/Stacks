module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceFiniteFamilies
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayModuleOverDerived
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CechGlobalSliceAway
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.DerivedHomComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingCriterionTelescope
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingIdealSheafRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
public import StacksFrontier.Homology.DerivedCategory.IsZero
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
import StacksCore.Tactic.StacksAttribute

/-!
# Descent along the slice restrictions of a ringed site

Let `(𝒞, 𝒪)` be a ringed site. For every object `U` of `𝒞` restriction to the slice site is
`SheafOfModules.overFunctor 𝒪 U`, it is exact, and it therefore induces a functor
`(-)|_U : D(𝒪) ⟶ D(𝒪_U)`. This file proves that the whole family `{(-)|_U}_{U ∈ 𝒞}` **descends
information**: an object of `D(𝒪)` all of whose restrictions vanish is zero, and a morphism all
of whose restrictions are invertible is invertible. It also proves that each `(-)|_U` commutes
with the countable products of the derived categories.

Those are the two properties that [Stacks, Tag 0999] forces on anyone who wants to read its
derived-completeness predicate back on the site itself: the predicate asserts `T(K|_U, f) = 0`
slice by slice, and `T(-, f) = 0` is the invertibility of an endomorphism of a *countable
product* in the derived category of the slice.

Those two properties are then combined into the **descent of derived completeness**: if
`T(K|_V, f|_V) = 0` for every object `V` of `𝒞` — which is what [Stacks, Tag 0999] asserts of a
derived-complete `K` at a section of the ideal sheaf — then `T(K, f) = 0` on the site itself,
and so, by [Stacks, Tag 0997], `R𝑆heafHom_𝒪(𝒪_f, K) = 0`.

Finally, the restriction stability of the vanishing locus of [Stacks, Tag 0998] is proved, which
is part of the sheaf condition of that lemma.

## Main results

* `AlgebraicGeometry.RingedSite.isZero_of_forall_isZero_over` — a sheaf of modules whose
  restriction to every slice site is zero is zero.
* `AlgebraicGeometry.RingedSite.isIso_of_forall_isIso_over` — a morphism of sheaves of modules
  whose restriction to every slice site is invertible is invertible.
* `AlgebraicGeometry.RingedSite.isZero_of_forall_isZero_overFunctor_mapDerivedCategory` and
  `AlgebraicGeometry.RingedSite.isIso_of_forall_isIso_overFunctor_mapDerivedCategory` — the
  same two statements in `D(𝒪)`: **the slice restrictions jointly reflect isomorphisms.**
* `AlgebraicGeometry.RingedSite.preservesProductsOfShape_nat_overFunctor_mapDerivedCategory` —
  **restriction to a slice site commutes with the countable products of the derived
  categories.**
* `AlgebraicGeometry.RingedSite.memVanishingIdeal_over_of_memVanishingIdeal` — **[Stacks, Tag
  0998], restriction stability**: a global section in the vanishing locus of `K` restricts to a
  global section of `𝒪_U` in the vanishing locus of `K|_U`.
* `AlgebraicGeometry.RingedSite.overFunctor_map_awaySmul_app`,
  `mapHomologicalComplex_map_awaySmul_smul_id` and `mapDerivedCategory_map_awaySmul_smul_id` —
  restriction to the slice over `U` carries multiplication by a global section `f` to
  multiplication by its value over `U`, on sheaves of modules, on cochain complexes, and in the
  derived category.
* `AlgebraicGeometry.RingedSite.isDerivedCompleteAt_of_forall_isDerivedCompleteAt_over` —
  **the descent**: `T(K|_V, f|_V) = 0` for every `V` gives `T(K, f) = 0`.
* `AlgebraicGeometry.RingedSite.memVanishingIdeal_of_forall_isDerivedCompleteAt_over` — the
  descent followed by [Stacks, Tag 0997] (1) ⇔ (3): the same hypothesis gives
  `R𝑆heafHom_𝒪(𝒪_f, K) = 0`.

## Implementation notes

The sheaf-level reflection is the sheaf condition in disguise, and needs no covering: the
restriction of `M` to the slice over `U` has, among its sections, the sections of `M` over `U`
itself, read over the terminal object `U ⟶ U` of `𝒞/U`. So a single slice already sees all
sections of `M` over its own object, and ranging over all `U` sees all of `M`. The morphism
statement is then the kernel–cokernel criterion: restriction is exact, so it takes the kernel
and the cokernel of a morphism to those of its restriction, and in an abelian category a
morphism with zero kernel and zero cokernel is invertible.

In the derived category both statements are read off degreewise. An object of an unbounded
derived category is zero exactly when all its cohomology vanishes
(`DerivedCategory.isZero_iff_forall_isZero_homology`) and a morphism is invertible exactly when
it is so on all cohomology (`DerivedCategory.isIso_iff`); restriction being exact, cohomology
commutes with it by `StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso`.

The countable products are obtained by **adjunction**, not from the construction of the products
themselves: extension by zero is left adjoint to restriction already on the derived categories,
which is `Stacks.Cohomology.Localization.derivedExtensionByZeroRestrictionAdjunction` ([Stacks,
Tag 08FJ]), and a right adjoint preserves every limit. Exactness of countable products of sheaves
of modules, Grothendieck's axiom AB4*, is *false*, so a product in `D(𝒪)` is not computed
termwise.

For restriction stability of the vanishing locus: the locus of [Stacks, Tag 0998] is
`AlgebraicGeometry.RingedSite.MemVanishingIdeal`, the vanishing of `R𝑆heafHom_𝒪(𝒪_f, K)`; the
base change `(𝒪_f)|_U ≅ (𝒪_U)_{f|_U}` is
`AlgebraicGeometry.RingedSite.derivedAwayModuleOverIso` and reduces membership of `f|_U` in the
locus of `K|_U` to the vanishing of `R𝑆heafHom_{𝒪_U}((𝒪_f)|_U, K|_U)`
(`AlgebraicGeometry.RingedSite.memVanishingIdeal_over_iff_isZero_derivedSheafHom_overFunctor`);
and that object is the restriction of `R𝑆heafHom_𝒪(𝒪_f, K)` by [Stacks, Tag 08JB],
`AlgebraicGeometry.RingedSite.derivedHomRestriction`. An additive functor carries a zero object
to a zero object, so the vanishing upstairs gives the vanishing downstairs.

What that does not give is the converse, and a single slice cannot give it: the converse needs
the locus to be tested on a covering family rather than on one object, which is
`AlgebraicGeometry.RingedSite.memVanishingIdeal_of_coversTop` of `VanishingIdealLocal.lean`.

The scalar at which [Stacks, Tag 0999] tests a restriction is
`Stacks.SheafOfModules.terminalSectionToEnd` at the terminal object `U ⟶ U` of `𝒞/U`, and it is
that spelling, `overTerminalSmul`, which the descent below uses — not
`AlgebraicGeometry.RingedSite.awaySmul` of the slice ringed site. The two are the same
endomorphism, but `((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U` and
`(Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)` are different *spellings* of one sheaf of
rings, and instance search does not pass between them: a statement mixing a scalar in one spelling
with a category in the other has no `Linear` instance. Keeping to the spelling of the predicate is
what makes the result directly usable by it.

**The descent carries no information about the ideal sheaf.** Its hypothesis is the family of
slice conditions, which the predicate of [Stacks, Tag 0999] supplies only at sections *belonging*
to the ideal sheaf; so applying it to a global section `f` requires separately that `f` be a
section of that ideal sheaf. That holds for the sheaf of ideals generated by a finite family of
global sections, and it is not assumed here.

## References

* [Stacks Project, Tag 0998](https://stacks.math.columbia.edu/tag/0998)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 08FJ](https://stacks.math.columbia.edu/tag/08FJ)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

section Sheaves

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- **A sheaf of modules whose restriction to every slice site vanishes is zero.** The
restriction to the slice over `V` has the sections of `M` over `V` among its own, read over the
terminal object `V ⟶ V` of `𝒞/V`, so the family of restrictions sees every section of `M`. -/
theorem isZero_of_forall_isZero_over (M : SheafOfModules.{u} R)
    (h : ∀ V : C, IsZero ((SheafOfModules.overFunctor.{u} R V).obj M)) :
    IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  ext V x
  exact Stacks.SheafOfModules.eq_zero_of_isZero (h V.unop) (op (Over.mk (𝟙 V.unop))) x

end Sheaves

section Reflection

variable (X : RingedSite.{u, u, u})

/-- **A morphism of sheaves of modules whose restriction to every slice site is invertible is
invertible.** Restriction is exact, so it carries the kernel and the cokernel of the morphism to
the kernel and the cokernel of its restriction; both vanish on every slice, hence vanish, and a
morphism of an abelian category with zero kernel and zero cokernel is invertible. -/
theorem isIso_of_forall_isIso_over
    {M N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (g : M ⟶ N)
    (h : ∀ V : X.C, IsIso
      ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V).map g)) :
    IsIso g := by
  have hker : IsZero (kernel g) := isZero_of_forall_isZero_over _ fun V => by
    have := h V
    exact IsZero.of_iso (isZero_kernel_of_mono ((SheafOfModules.overFunctor.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V).map g))
      (PreservesKernel.iso
        (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V) g)
  have hcoker : IsZero (cokernel g) := isZero_of_forall_isZero_over _ fun V => by
    have := h V
    exact IsZero.of_iso (isZero_cokernel_of_epi ((SheafOfModules.overFunctor.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V).map g))
      (PreservesCokernel.iso
        (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V) g)
  have : Mono g := Preadditive.mono_of_isZero_kernel g hker
  have : Epi g := Preadditive.epi_of_isZero_cokernel g hcoker
  exact isIso_of_mono_of_epi g

/-- **An object of `D(𝒪)` whose restriction to every slice site vanishes is zero.** An object of
an unbounded derived category is zero exactly when all its cohomology vanishes, and restriction
being exact, the cohomology of the restriction is the restriction of the cohomology. -/
theorem isZero_of_forall_isZero_overFunctor_mapDerivedCategory
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (h : ∀ V : X.C, IsZero
      ((SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V).mapDerivedCategory.obj K)) :
    IsZero K := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro n
  refine isZero_of_forall_isZero_over _ fun V => ?_
  refine IsZero.of_iso ?_
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V)
        n).app K).symm
  exact (DerivedCategory.homologyFunctor _ n).map_isZero (h V)

/-- **The slice restrictions jointly reflect isomorphisms in `D(𝒪)`.** A morphism of `D(𝒪)` is
invertible exactly when it is invertible on all cohomology; cohomology commutes with the exact
restriction, and the restrictions of a sheaf of modules jointly reflect isomorphisms. -/
theorem isIso_of_forall_isIso_overFunctor_mapDerivedCategory
    {K L : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (φ : K ⟶ L)
    (h : ∀ V : X.C,
      IsIso ((SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V).mapDerivedCategory.map φ)) :
    IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_forall_isIso_over X _ fun V => ?_
  have := h V
  have hmap : IsIso (((SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V).mapDerivedCategory ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over V)) n).map φ) := by
    dsimp only [Functor.comp_map]
    infer_instance
  exact (NatIso.isIso_map_iff
    (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V) n) φ).1 hmap

end Reflection

section Products

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-- **Restriction to a slice site commutes with the countable products of the derived
categories.** Extension by zero is left adjoint to restriction already on the unbounded derived
categories, which is [Stacks, Tag 08FJ], and a right adjoint preserves every limit.

No exactness of the countable products of sheaves of modules is used, and none is available:
Grothendieck's axiom AB4* fails there, which is why the countable products of `D(𝒪)` are built
from K-injective resolutions in the first place. -/
alias preservesProductsOfShape_nat_overFunctor_mapDerivedCategory :=
  preservesProducts_mapDerivedCategory_overFunctor

end Products

section VanishingLocus

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] (U : X.C)
  (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **[Stacks, Tag 0998], restriction stability of the vanishing locus.** If the global section
`f` of `𝒪` lies in the vanishing locus of `K`, then its restriction `f|_U` lies in the vanishing
locus of `K|_U` over the slice site `𝒞/U`.

Membership of `f|_U` in the locus of `K|_U` is the vanishing of `R𝑆heafHom_{𝒪_U}((𝒪_f)|_U, K|_U)`
by `AlgebraicGeometry.RingedSite.memVanishingIdeal_over_iff_isZero_derivedSheafHom_overFunctor`,
whose input is the base change `(𝒪_f)|_U ≅ (𝒪_U)_{f|_U}`; and that object is the restriction of
`R𝑆heafHom_𝒪(𝒪_f, K)` by [Stacks, Tag 08JB]. Restriction is additive, so it carries the
vanishing upstairs to the vanishing downstairs. -/
@[stacks 0998 "the vanishing locus is stable under restriction to a slice site"]
theorem memVanishingIdeal_over_of_memVanishingIdeal
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : MemVanishingIdeal X K h) :
    MemVanishingIdeal (X.over U)
      ((SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj K)
      (globalSectionOver X U h) := by
  rw [memVanishingIdeal_over_iff_isZero_derivedSheafHom_overFunctor]
  exact IsZero.of_iso
    ((SheafOfModules.overFunctor.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.map_isZero hK)
    ((derivedHomRestriction X U).iso (derivedAwayModule X h) K).symm

end VanishingLocus

section Descent

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}]
  (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

attribute [local instance] linearCatCenterRingSheaf
  isMulCommutative_ringSheaf_over linearCatCenterOver

/-- The value over `U` of a global section of `𝒪`, read as a scalar acting on sheaves of
modules on the slice site over `U`. This is the scalar at which the derived-completeness
predicate of [Stacks, Tag 0999] tests `K|_U`. -/
abbrev overTerminalSmul (U : X.C) :
    End (𝟭 (SheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U))) :=
  Stacks.SheafOfModules.terminalSectionToEnd (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U)
    (Over.mk (𝟙 U)) Over.mkIdTerminal (globalSectionVal h (op U))

omit [HasWeakSheafify X.J CommRingCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}] in
/-- **Multiplication by a global section restricts to multiplication by its value over `U`**, on
every sheaf of modules. Both sides act on a section over `V/U` by multiplication by the value of
`f` over `V`, which is the restriction along `V ⟶ U` of its value over `U`. -/
theorem overFunctor_map_awaySmul_app (U : X.C)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).map
        ((awaySmul X h).app M) =
      (overTerminalSmul X h U).app
        ((SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).obj M) := by
  ext V x
  refine (awaySmul_app_apply X h M (op V.unop.left) x).trans ?_
  rw [← globalSectionVal_map h ((Over.mkIdTerminal.from V.unop).left.op)]
  rfl

omit [HasWeakSheafify X.J CommRingCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}] in
/-- The degreewise form of `overFunctor_map_awaySmul_app` on cochain complexes, which is the
hypothesis `Stacks.SheafOfModules.DerivedRestrictScalars.mapDerivedCategory_map_smul_id`
consumes. -/
theorem mapHomologicalComplex_map_awaySmul_smul_id (U : X.C)
    (Z : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ) :
    ((SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (awaySmul X h • 𝟙 Z) =
      overTerminalSmul X h U •
        𝟙 (((SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Z) := by
  ext n : 1
  rw [Functor.mapHomologicalComplex_map_f,
    show (awaySmul X h • 𝟙 Z).f n = (awaySmul X h).app (Z.X n) from rfl,
    show (overTerminalSmul X h U •
        𝟙 (((SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Z)).f n =
      (overTerminalSmul X h U).app
        ((SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).obj (Z.X n)) from rfl]
  exact overFunctor_map_awaySmul_app X h U (Z.X n)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The derived form of `overFunctor_map_awaySmul_app`: restriction to the slice site over `U`
carries multiplication by `f` on an object of `D(𝒪)` to multiplication by the value of `f` over
`U`. -/
theorem mapDerivedCategory_map_awaySmul_smul_id (U : X.C)
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    (SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.map
        (awaySmul X h • 𝟙 K) =
      overTerminalSmul X h U •
        𝟙 ((SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj K) :=
  Stacks.SheafOfModules.DerivedRestrictScalars.mapDerivedCategory_map_smul_id
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U) _ _
    (mapHomologicalComplex_map_awaySmul_smul_id X h U) K

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The descent of derived completeness from the slice sites to the site.** If `T(K|_V, f|_V)`
vanishes for every object `V` of `𝒞`, then `T(K, f)` vanishes on the site itself.

The hypothesis is verbatim what the derived-completeness predicate of [Stacks, Tag 0999]
supplies at a section of the ideal sheaf; it says nothing about `f` unless `f` is a section of
that ideal sheaf, and nothing here assumes that it is.

The two inputs are these. Restriction commutes with the countable product of the derived category
(`preservesProductsOfShape_nat_overFunctor_mapDerivedCategory`), so, matching the scalars by
`mapDerivedCategory_map_awaySmul_smul_id`, it intertwines the two Milnor difference maps
`1 - f·shift` and `1 - f|_V·shift` through the product comparison; and the restrictions jointly
reflect isomorphisms (`isIso_of_forall_isIso_overFunctor_mapDerivedCategory`), so invertibility
of every restriction of `1 - f·shift` is invertibility of `1 - f·shift`. -/
theorem isDerivedCompleteAt_of_forall_isDerivedCompleteAt_over
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hc : ∀ V : X.C, IsDerivedCompleteAt
      ((SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V).mapDerivedCategory.obj K)
      (overTerminalSmul X h V)) :
    IsDerivedCompleteAt K (awaySmul X h) := by
  rw [isDerivedCompleteAt_iff_isIso]
  refine isIso_of_forall_isIso_overFunctor_mapDerivedCategory X _ fun V => ?_
  have hprod := preservesProductsOfShape_nat_overFunctor_mapDerivedCategory X V
  have h1 : IsIso (piComparison
        (SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V).mapDerivedCategory (fun _ : ℕ ↦ K) ≫
      oneSubSmulShift
        ((SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V).mapDerivedCategory.obj K)
        (overTerminalSmul X h V)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (hc V)
  rw [← oneSubSmulShift_map_comp_piComparison
    (SheafOfModules.overFunctor.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V).mapDerivedCategory
    (mapDerivedCategory_map_awaySmul_smul_id X h V K)] at h1
  exact IsIso.of_isIso_comp_right _ (piComparison (SheafOfModules.overFunctor.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V).mapDerivedCategory (fun _ : ℕ ↦ K))

/-- **Membership in the vanishing locus of [Stacks, Tag 0998], from derived completeness along
the slice sites.** If `K|_V` is derived complete at the value of `f` over `V` for every object
`V` of `𝒞`, then `R𝑆heafHom_𝒪(𝒪_f, K) = 0`.

This is the descent above followed by the equivalence (1) ⇔ (3) of [Stacks, Tag 0997]. The
hypothesis is what `AlgebraicGeometry.RingedSite.IsDerivedComplete` of [Stacks, Tag 0999]
supplies at a *section of the ideal sheaf*; applying this to a global section `f` therefore still
requires that `f` belong to the ideal sheaf, which is a separate input and is not assumed
here. -/
theorem memVanishingIdeal_of_forall_isDerivedCompleteAt_over
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hc : ∀ V : X.C, IsDerivedCompleteAt
      ((SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V).mapDerivedCategory.obj K)
      (overTerminalSmul X h V)) :
    MemVanishingIdeal X K h :=
  (isZero_derivedSheafHom_derivedAwayModule_iff_isDerivedCompleteAt X h K).2
    (isDerivedCompleteAt_of_forall_isDerivedCompleteAt_over X h K hc)

end Descent

end AlgebraicGeometry.RingedSite

end
