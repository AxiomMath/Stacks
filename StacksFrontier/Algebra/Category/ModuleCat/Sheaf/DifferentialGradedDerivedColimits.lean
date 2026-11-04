module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDeltaFunctorTriangle
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedFilteredColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategoryTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedKInjectiveExistence
public import StacksFrontier.CategoryTheory.Abelian.GrothendieckAxioms.CountableCoproducts
public import StacksFrontier.CategoryTheory.Triangulated.Functor
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimit

/-!
# The derived colimit of a system of sheaf differential graded modules

Let `(C, O)` be a ringed site and let `(A, d)` be a sheaf of differential graded `O`-algebras.
Let `M₀ → M₁ → M₂ → ⋯` be a system of right differential graded `A`-modules. Its derived
colimit `hocolim Mₙ` in `D(A, d)` — the third vertex of a distinguished triangle on the map
`1 - f : ⊕ₙ Mₙ ⟶ ⊕ₙ Mₙ` — is represented by the ordinary colimit `colim Mₙ` of sheaf
differential graded modules.

The proof is the one of the source, one level up from the non-sheaf case
`DifferentialGradedModule.isHomotopyColimit_toDerivedCategory_obj_colimit` (Tag 0CRL). Lemma
093W presents the colimit of a system over `ℕ` as the cokernel of `1 - f`, so that
`0 → ⊕ₙ Mₙ → ⊕ₙ Mₙ → colim Mₙ → 0` is a short exact sequence of right differential graded
`A`-modules; a `δ`-functor structure on the localization `Mod(A, d) ⥤ D(A, d)` turns that
sequence into a distinguished triangle of `D(A, d)`; and the image of a direct sum of modules
is a direct sum in `D(A, d)`, so that triangle is the one Definition 090Z asks for.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.hasZeroObject_derivedCategory`: `D(A, d)` has a zero
  object, the quasi-isomorphisms admitting a left calculus of fractions. This is needed only to
  *state* the `δ`-functor of Tag 0FTB, which lands in a pre-triangulated category.

## Main results

* `SheafOfModules.DifferentialGradedModule.preservesFiniteLimits_colim_nat`: colimits over `ℕ`
  of right differential graded `A`-modules are exact, in the form Lemma 093W consumes.
* `SheafOfModules.DifferentialGradedModule.shortExact_oneSubShift_piMap`: **Lemma 093W for
  sheaf differential graded modules** — `0 → ⊕ₙ Mₙ --(1 - f)--> ⊕ₙ Mₙ --π--> colim Mₙ → 0` is
  short exact. This carries no hypothesis beyond the standing ones on the site.
* `SheafOfModules.DifferentialGradedModule.isHomotopyColimit_moduleToDerivedCategory_obj_colimit`:
  **Stacks 0FTC**, `colim Mₙ = hocolim Mₙ` in `D(A, d)`.

## Where the three inputs of Tag 0FTC come from

Beyond the standing conditions on the site, which are the ones that make `SheafOfModules O`
abelian and its differential graded modules sheafifiable, Tag 0FTC needs three things, and all
three are proved in this development:

* **Tag 0FT4**, that the quasi-isomorphisms are a multiplicative system compatible with the
  triangulation of `K(Mod(A, d))` of Tag 0FS7. It is
  `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_hasLeftCalculusOfFractions` and
  `….quasiIsomorphisms_isCompatibleWithTriangulation`, both instances, and through them
  Mathlib's `CategoryTheory.Localization.Triangulated` supplies the additive, shifted,
  pre-triangulated structure on `D(A, d)` in which the statement is read. Instance search finds
  them; nothing has to be passed.
* **Tag 0FTB**, the `δ`-functor structure (Tag 0150) on the localization functor
  `Mod(A, d) ⥤ D(A, d)` with connecting morphism `δ = - p ∘ q⁻¹`. It is
  `SheafOfModules.DifferentialGradedModule.deltaFunctorStructure`. Only its `distinguished`
  field is used below; the naturality field is not.
* **Tag 0FT9**, parts (1) and (2): that `D(A, d)` has countable direct sums and that they are
  computed by direct sums of modules. Those are
  `SheafOfModules.DifferentialGradedModule.derivedCategory_sumsAndProducts`, read here as the
  two instances `hasColimitsOfShape_discrete_nat_derivedCategory` and
  `preservesColimitsOfShape_discrete_nat_moduleToDerivedCategory`; `ℕ` is replaced by an
  index type of the module universe along `Equiv.ulift`, which is where Tag 0FT9 states them.

The short exact sequence `0 → ⊕ₙ Mₙ → ⊕ₙ Mₙ → colim Mₙ → 0` of right differential graded
`A`-modules, i.e. Lemma 093W in `Mod(A, d)`, needs none of those. Its monomorphy half is the
only place exactness of colimits over `ℕ` is used, and that exactness is Tag 0FRJ,
`filteredColimits_exact`.

## Implementation notes

*Why Lemma 093W can be cited rather than redone.* In the non-sheaf case
(`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedColimits.lean`) the monomorphy of `1 - f`
had to be proved by hand on a concrete direct sum, because the colimits of differential graded
modules there are produced abstractly from coproducts and cokernels and nothing is known about
their elements. Here the general Lemma 093W applies: exactness of colimits over `ℕ` in
`Mod(A, d)` is Tag 0FRJ (`filteredColimits_exact`), AB5 at the size of the shape `ℕ`, which is
`Type 0`. So `Stacks.CountableCoproducts.shortExact_oneSubShift_piMap` is instantiated directly
and the hand-written telescope argument is not repeated.

*The shape of the first map.* `CategoryTheory.Pretriangulated.IsHomotopyColimit` pins the first
map of the triangle as a `Sigma.desc` over the family `(F ⋙ G).obj`, while the short exact
sequence produces `Stacks.CountableCoproducts.oneSubShift F` in `Mod(A, d)`. The comparison map
`⊕ₙ G Mₙ ⟶ G (⊕ₙ Mₙ)` of the additive functor `G` intertwines the two
(`Stacks.CountableCoproducts.oneSubShift_comp_sigmaComparison`), and it is an isomorphism exactly
by Tag 0FT9, part (2); transporting the distinguished triangle along it is the last step.

*The base and the universes.* The base is a ringed site, as in Tag 0FTC itself and as the
pre-triangulated structure on `K(Mod(A, d))` of Tag 0FS7 requires. The module universe is
`max u v w` with `u` the universe of the site and `v` the universe of the pieces of the algebra:
that is the shape at which Tag 0FRJ's exactness of filtered colimits is available, and it is
also where Tag 0FT0 produces its K-injective resolutions and therefore where Tag 0FT9 has its
direct sums.

## References

* [Stacks Project, Tag 0FTC](https://stacks.math.columbia.edu/tag/0FTC)
* [Stacks Project, Tag 093W](https://stacks.math.columbia.edu/tag/093W)
* [Stacks Project, Tag 090Z](https://stacks.math.columbia.edu/tag/090Z)
* [Stacks Project, Tag 0CRL](https://stacks.math.columbia.edu/tag/0CRL)
* [Stacks Project, Tag 0FTB](https://stacks.math.columbia.edu/tag/0FTB)
* [Stacks Project, Tag 0FT4](https://stacks.math.columbia.edu/tag/0FT4)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
* [Stacks Project, Tag 0FT9](https://stacks.math.columbia.edu/tag/0FT9)
* [Stacks Project, Tag 0FS7](https://stacks.math.columbia.edu/tag/0FS7)
* [Stacks Project, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ)
* [Stacks Project, Tag 0150](https://stacks.math.columbia.edu/tag/0150)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.CountableCoproducts

universe w v u

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  [HasWeakSheafify X.J (Type max u v w)]
  [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-! ### Lemma 093W for sheaf differential graded modules -/

omit [HasWeakSheafify X.J (Type (max u v w))] in
/-- Colimits over `ℕ` of right differential graded `A`-modules are exact, in the form Lemma 093W
consumes: `colim : (ℕ ⥤ Mod(A, d)) ⥤ Mod(A, d)` preserves finite limits.

This is Tag 0FRJ, `SheafOfModules.DifferentialGradedModule.filteredColimits_exact`, at the size
of the shape `ℕ`, which is a filtered category in `Type 0`. -/
theorem preservesFiniteLimits_colim_nat :
    PreservesFiniteLimits
      (colim : (ℕ ⥤ DifferentialGradedModule.{u, v, max u v w} A) ⥤
        DifferentialGradedModule.{u, v, max u v w} A) :=
  have := filteredColimits_exact.{0, 0, max v w, v, u, u, u} A
  HasExactColimitsOfShape.preservesFiniteLimits

omit [HasWeakSheafify X.J (Type (max u v w))] in
/-- **Lemma 093W for sheaf differential graded modules.** For a system `M₀ → M₁ → ⋯` of right
differential graded `A`-modules over a sheaf of differential graded algebras, the sequence

`0 → ⊕ₙ Mₙ --(1 - f)--> ⊕ₙ Mₙ --π--> colim Mₙ → 0`

is short exact, where `1 - f` is the morphism with `σₙ ≫ (1 - f) = σₙ - fₙ ≫ σₙ₊₁` on the `n`-th
coprojection and `π` is the morphism with `σₙ ≫ π = ιₙ`.

The general Lemma 093W applies verbatim: `Mod(A, d)` is abelian, it has colimits over `ℕ` and
countable direct sums, and those colimits over `ℕ` are exact by Tag 0FRJ. -/
@[stacks 093W "sheaf differential graded modules"]
theorem shortExact_oneSubShift_piMap (F : ℕ ⥤ DifferentialGradedModule.{u, v, max u v w} A) :
    ∃ hw : oneSubShift F ≫ piMap F = 0,
      (ShortComplex.mk (oneSubShift F) (piMap F) hw).ShortExact :=
  Stacks.CountableCoproducts.shortExact_oneSubShift_piMap
    (preservesFiniteLimits_colim_nat.{w} A) F

/-! ### The derived colimit -/

section DerivedColimit

/-- `D(A, d)` has a zero object: it is the image of the zero object of `K(Mod(A, d))` under the
localization functor, which is additive because the quasi-isomorphisms admit a left calculus of
fractions, Tag 0FT4. Instance search does not find this through the `abbrev` for the derived
category, and it is one of the structures a `δ`-functor's target is asked for. -/
instance hasZeroObject_derivedCategory : HasZeroObject (derivedCategory.{u, v, max u v w} A) :=
  (toDerivedCategory.{u, v, max u v w} A).hasZeroObject_of_additive

/-! ### Countable direct sums in the derived category -/

/-- `D(A, d)` has countable direct sums: it has all the ones indexed by a type of the module
universe, which is Tag 0FT9, part (1), and `ℕ` is in bijection with such a type. -/
instance hasColimitsOfShape_discrete_nat_derivedCategory :
    HasColimitsOfShape (Discrete ℕ) (derivedCategory.{u, v, max u v w} A) :=
  haveI : HasColimitsOfShape (Discrete (ULift.{max u v w} ℕ))
      (derivedCategory.{u, v, max u v w} A) :=
    (derivedCategory_hasProducts_and_hasCoproducts.{u, v, w} A).2 (ULift.{max u v w} ℕ)
  hasColimitsOfShape_of_equivalence (Discrete.equivalence (Equiv.ulift.{max u v w, 0}))

/-- **Tag 0FT9, part (2)** in the form a derived colimit consumes: the localization functor
`Mod(A, d) ⥤ D(A, d)` carries a direct sum of right differential graded modules to a direct sum,
for a countable family. Preservation of colimits of discrete diagrams records both that the
image of the direct sum is a direct sum and that its coproduct injections are the images of the
canonical ones. -/
instance preservesColimitsOfShape_discrete_nat_moduleToDerivedCategory :
    PreservesColimitsOfShape (Discrete ℕ) (moduleToDerivedCategory.{u, v, max u v w} A) := by
  have key : ∀ M : ULift.{max u v w} ℕ → DifferentialGradedModule.{u, v, max u v w} A,
      PreservesColimit (Discrete.functor M)
        (moduleToDerivedCategory.{u, v, max u v w} A) := fun M =>
    preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct M)
      ((isColimitMapCoconeCofanMkEquiv _ _ _).symm
        (isColimit_derivedCofanOfModules_dg.{u, v, w} A M))
  have : PreservesColimitsOfShape (Discrete (ULift.{max u v w} ℕ))
      (moduleToDerivedCategory.{u, v, max u v w} A) :=
    ⟨fun {K} => preservesColimit_of_iso_diagram _ (Discrete.natIsoFunctor (F := K)).symm⟩
  exact preservesColimitsOfShape_of_equiv
    (Discrete.equivalence (Equiv.ulift.{max u v w, 0})) _

/-- **Stacks 0FTC.** *"Let `(C, O)` be a ringed site. Let `(A, d)` be a sheaf of differential
graded algebras on `(C, O)`. Let `Mₙ` be a system of differential graded `A`-modules. Then the
derived colimit `hocolim Mₙ` in `D(A, d)` is represented by the differential graded module
`colim Mₙ`."*

The conclusion is `CategoryTheory.Pretriangulated.IsHomotopyColimit` of Definition 090Z for the
image system in `D(A, d)`: the image of `colim Mₙ` sits in a distinguished triangle
`⊕ₙ Mₙ --(1 - f)--> ⊕ₙ Mₙ ⟶ colim Mₙ ⟶ (⊕ₙ Mₙ)⟦1⟧` of `D(A, d)`.

The three inputs are all proved in this development: the pre-triangulated structure on `D(A, d)`
in which the statement is read is the one Tag 0FT4 produces, found by instance search from
`quasiIsomorphisms_hasLeftCalculusOfFractions` and
`quasiIsomorphisms_isCompatibleWithTriangulation`; the `δ`-functor structure `d` is Tag 0FTB,
`deltaFunctorStructure`; and the two colimit instances on `D(A, d)` are Tag 0FT9, parts (1) and
(2), `hasColimitsOfShape_discrete_nat_derivedCategory` and
`preservesColimitsOfShape_discrete_nat_moduleToDerivedCategory`. -/
@[stacks 0FTC]
theorem isHomotopyColimit_moduleToDerivedCategory_obj_colimit
    (F : ℕ ⥤ DifferentialGradedModule.{u, v, max u v w} A) :
    IsHomotopyColimit (F ⋙ moduleToDerivedCategory.{u, v, max u v w} A)
      ((moduleToDerivedCategory.{u, v, max u v w} A).obj (colimit F)) := by
  have d : (moduleToDerivedCategory.{u, v, max u v w} A).DeltaFunctorStructure
      (DifferentialGradedModule.{u, v, max u v w} A) (derivedCategory.{u, v, max u v w} A) :=
    deltaFunctorStructure
  have : HasCoproduct fun n =>
    (moduleToDerivedCategory.{u, v, max u v w} A).obj (F.obj n) := inferInstance
  obtain ⟨hw, hSE⟩ := shortExact_oneSubShift_piMap A F
  set e := asIso (sigmaComparison (moduleToDerivedCategory.{u, v, max u v w} A) F.obj)
  refine ⟨e.hom ≫ (moduleToDerivedCategory A).map (piMap F),
    d.δ hSE ≫ (CategoryTheory.shiftFunctor (derivedCategory A) (1 : ℤ)).map e.inv, ?_⟩
  refine isomorphic_distinguished _ (d.distinguished hSE) _
    (Triangle.isoMk _ _ e e (Iso.refl _)
      (oneSubShift_comp_sigmaComparison (moduleToDerivedCategory A) F) (Category.comp_id _) ?_)
  simp

end DerivedColimit

end SheafOfModules.DifferentialGradedModule

end
