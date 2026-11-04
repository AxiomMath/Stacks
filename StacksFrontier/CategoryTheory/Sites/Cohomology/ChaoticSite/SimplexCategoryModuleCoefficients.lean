module

public import Mathlib.CategoryTheory.Category.ULift
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Equivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolutionLargeSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekOfInverseImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.FlatEilenbergZilber
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SymmetricPowerVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# Simplicial modules as modules on the chaotic site `Δ`

Let `Δ = SimplexCategory` carry the chaotic topology and let `B` be a ring. Remark 08QD observes
that this is an instance of Example 08PF to which Lemma 08Q9 applies, with the cosimplicial
object `U_• = 𝟭 Δ`, and draws three consequences:

* the category `Mod(B̲)` of modules over the constant sheaf of rings `B̲` *is* the category of
  simplicial `B`-modules;
* the derived lower shriek `Lπ_! : D(B̲) ⥤ D(B)` sends a simplicial `B`-module `M_•` to its
  associated complex `s(M_•)`, the alternating-face-map complex;
* for two (flat) simplicial `B`-modules the complex `s(M_• ⊗_B M'_•)` is quasi-isomorphic to the
  total complex of the double complex `s(M_•) ⊗_B s(M'_•)`, which is a case of the
  Eilenberg–Zilber theorem.

The verification that `U_• = 𝟭 Δ` satisfies the hypothesis of Lemma 08Q9 is
`Stacks.ChaoticSite.isPointResolution_id_simplexCategory`, and the Eilenberg–Zilber theorem is
`Stacks.ChaoticSite.quasiIso_alexanderWhitney`. This file supplies the two statements about
`Mod(B̲)` and `Lπ_!`, for a ring `B` in an arbitrary universe.

## Main definitions

* `Stacks.ChaoticSite.simplexCategoryConstantRingSheaf`: the constant sheaf of rings `B̲` on the
  chaotic site `Δ`.
* `Stacks.ChaoticSite.simplexCategoryModuleEquivalence`: **`Mod(B̲)` is the category of simplicial
  `B`-modules.**
* `Stacks.ChaoticSite.simplexCategoryMooreNatIsoDerivedLowerShriek`: **`Lπ_!` sends a simplicial
  `B`-module to its associated complex**: `Q(s(M_•)) ≅ Lπ_!(M_•)` in `D(B)`, naturally in `M_•`.

## Main results

* `Stacks.ChaoticSite.isPointResolution_asSmallUp_simplexCategory`: the cosimplicial object
  `U_• = 𝟭 Δ`, read in the small model `AsSmall Δ` of `Δ` at an arbitrary universe, is again a
  point resolution.
* `Stacks.ChaoticSite.flatEilenbergZilber`: the Eilenberg–Zilber comparison holds for every
  commutative ring, so the predicate `Stacks.ChaoticSite.FlatEilenbergZilber` is always satisfied.

## Implementation notes

**The universe of `B`.** The module form of Lemma 08Q9,
`Stacks.ChaoticSite.ModuleValued.mooreCochainNatIsoDerivedColimit`, asks for the site, the ring
and the modules to share one universe. `Δ` is a small category in universe `0`, so applied to
`Δ` directly it only reaches rings `B : Type`. To reach a ring `B : Type w`, the criterion is
applied instead at `AsSmall.{w} Δ`, a small category in universe `w` equivalent to `Δ`, with the
cosimplicial object `AsSmall.up`, and the result is carried back to `Δ` along the equivalence by
`Stacks.ChaoticSite.derivedColimitSingleEquivalenceIso`, as in
`Stacks.ChaoticSite.ModuleValued.mooreCochainNatIsoDerivedColimitOfLarge`. The Moore-complex
side needs no comparison: restricting a presheaf on `AsSmall Δ` along `AsSmall.up` and taking
its alternating-face-map complex is, by definition, the Moore complex of its evaluation on
`AsSmall.up`.

**The representation of `Mod(B̲)` and `Lπ_!`.** As everywhere in this development
(see `StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriek`), a
`B̲`-module on a chaotic site is read as a diagram of `B`-modules, through
`Stacks.ChaoticSite.constantModuleSheafEquivalence`, and `Lπ_!` is the total left derived
functor `Stacks.CategoryHomology.totalDerivedColimit` of the colimit, which is `π_!` on the
chaotic site by Example 08PF. At `C = Δ` a diagram `Δᵒᵖ ⥤ ModuleCat B` is by definition a
simplicial `B`-module.

## References

* [Stacks Project, Tag 08QD](https://stacks.math.columbia.edu/tag/08QD)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08Q3](https://stacks.math.columbia.edu/tag/08Q3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.CategoryHomology

open scoped Simplicial

universe w

namespace Stacks.ChaoticSite

attribute [local instance] HasDerivedCategory.standard

/-! ### `Mod(B̲)` on `Δ` -/

section Modules

variable (B : Type w) [Ring B]

/-- The constant sheaf of rings `B̲` on `Δ` with the chaotic topology: every presheaf is a sheaf
for the chaotic topology, and the constant presheaf with value `B` is the structure sheaf of
Example 08PF. -/
def simplexCategoryConstantRingSheaf :
    Sheaf (GrothendieckTopology.trivial SimplexCategory) RingCat.{w} :=
  ⟨(Functor.const SimplexCategoryᵒᵖ).obj (RingCat.of B), by
    simpa only [GrothendieckTopology.trivial_eq_bot] using Presheaf.isSheaf_bot _⟩

/-- **Stacks 08QD, `Mod(B̲)` on `Δ`.** For the chaotic site `Δ` and a ring `B`, the category
`Mod(B̲)` of modules over the constant sheaf of rings `B̲` is the category of simplicial
`B`-modules. -/
@[stacks 08QD "`Mod(B̲)` is the category of simplicial `B`-modules"]
def simplexCategoryModuleEquivalence :
    SheafOfModules.{w} (simplexCategoryConstantRingSheaf B) ≌
      SimplicialObject (ModuleCat.{w} B) :=
  constantModuleSheafEquivalence (RingCat.of B) (simplexCategoryConstantRingSheaf B) rfl

end Modules

/-! ### The point resolution of `Δ` at an arbitrary universe -/

section PointResolution

/-- The simplicial set `Mor(AsSmall.up ⦋•⦌, W)` of the small model of `Δ` in universe `w` is the
standard simplex on `W`, read in `SSet.{w}`. -/
@[sga "4 V 7.3.1.6"]
def asSmallUpYonedaIsoStdSimplex (W : AsSmall.{w} SimplexCategory) :
    (AsSmall.up.{0, 0, w} : SimplexCategory ⥤ AsSmall.{w} SimplexCategory).op ⋙ yoneda.obj W ≅
      SSet.stdSimplex.{w}.obj (AsSmall.down.obj W) :=
  NatIso.ofComponents (fun _ => Equiv.toIso (Equiv.ulift.trans Equiv.ulift.symm))
    (by intros; rfl)

/-- The standard simplex on `⦋0⦌`, read in `SSet.{w}`, is the constant simplicial set on a
singleton. -/
def stdSimplexZeroIsoConst :
    SSet.stdSimplex.{w}.obj ⦋0⦌ ≅ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{w + 1} :=
  NatIso.ofComponents (fun x => Equiv.toIso
    (Equiv.ulift.trans (Equiv.equivPUnit (unop x ⟶ ⦋0⦌)))) (by intros; rfl)

/-- **The tautological cosimplicial object of `Δ` is a point resolution in every universe.** The
cosimplicial object `AsSmall.up` of the small model `AsSmall.{w} Δ` is a point resolution: its
simplicial sets of morphisms are the standard simplices, read in `SSet.{w}`, which are
homotopy equivalent to a point (Stacks 08Q3). This is
`Stacks.ChaoticSite.isPointResolution_id_simplexCategory` at the universe `w`. -/
theorem isPointResolution_asSmallUp_simplexCategory :
    IsPointResolution
      (AsSmall.up.{0, 0, w} : CosimplicialObject (AsSmall.{w} SimplexCategory)) := by
  intro W
  refine ⟨(asSmallUpYonedaIsoStdSimplex W).hom ≫
      SSet.stdSimplex.{w}.map (default : AsSmall.down.obj W ⟶ ⦋0⦌) ≫
      stdSimplexZeroIsoConst.hom, ?_⟩
  exact SimplicialObject.homotopyEquivalences_iso_comp_iso (asSmallUpYonedaIsoStdSimplex W)
    (SSet.stdSimplex.{w}.map (default : AsSmall.down.obj W ⟶ ⦋0⦌)) stdSimplexZeroIsoConst
    ((SSet.stdSimplex.homotopyEquivalences_hom_obj₀ (AsSmall.down.obj W).len).1 _)

end PointResolution

/-! ### `Lπ_!` of a simplicial module -/

section DerivedLowerShriek

variable (B : Type w) [Ring B]

/-- **Stacks 08QD, `Lπ_!` of a simplicial module is its associated complex.** For the chaotic
site `Δ` and a ring `B`, the derived lower shriek `Lπ_! : D(B̲) ⥤ D(B)` sends a simplicial
`B`-module `M_•`, placed in degree zero, to its associated complex `s(M_•)`, the
alternating-face-map complex, read as a cochain complex in nonpositive degrees:

`Q(s(M_•)) ≅ Lπ_!(M_•)` in `D(B)`, naturally in `M_•`.

Here `Lπ_!` is the total left derived functor of the colimit over `Δᵒᵖ`, which is `π_!` on the
chaotic site by Example 08PF, and a `B̲`-module is a simplicial `B`-module by
`Stacks.ChaoticSite.simplexCategoryModuleEquivalence`. The proof is Lemma 08Q9 for the point
resolution `U_• = 𝟭 Δ`, at which the evaluation `M(U_•)` is `M_•` itself. -/
@[stacks 08QD "`Lπ_!` sends a simplicial `B`-module `M_•` to its associated complex `s(M_•)`, \
  as an isomorphism in `D(B)` natural in `M_•`"]
def simplexCategoryMooreNatIsoDerivedLowerShriek :
    alternatingFaceMapComplex (ModuleCat.{w} B) ⋙
        (ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor (ModuleCat.{w} B) ⋙
          DerivedCategory.Q ≅
      HomologicalComplex.single (SimplicialObject (ModuleCat.{w} B)) (ComplexShape.up ℤ) 0 ⋙
        DerivedCategory.Q ⋙ totalDerivedColimit SimplexCategory (ModuleCat.{w} B) :=
  cancelLeftNatIsoOfEquivalence
    (presheafEquivalenceOfEquivalence AsSmall.equiv.{0, 0, w} (ModuleCat.{w} B)) _ _
    (ModuleValued.mooreCochainNatIsoDerivedColimit (B := B) AsSmall.up.{0, 0, w}
        isPointResolution_asSmallUp_simplexCategory ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
        (totalDerivedColimitIsoTotalDerivedColimit' _ (ModuleCat.{w} B))) ≪≫
      derivedColimitSingleEquivalenceIso AsSmall.equiv.{0, 0, w} (ModuleCat.{w} B) ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
        (totalDerivedColimitIsoTotalDerivedColimit' SimplexCategory (ModuleCat.{w} B)).symm)))

end DerivedLowerShriek

/-! ### The Eilenberg–Zilber comparison -/

/-- **The Eilenberg–Zilber comparison holds for every commutative ring.** For two degreewise flat
simplicial `B`-modules the Moore complex of the degreewise tensor product is quasi-isomorphic to
the total tensor product of the Moore complexes, the quasi-isomorphism being the
Alexander–Whitney map `AlgebraicTopology.alexanderWhitney` (Stacks 08QD,
`Stacks.ChaoticSite.quasiIso_alexanderWhitney`, which needs no flatness). -/
@[stacks 08QD "flat_eilenberg_zilber: for flat simplicial `B`-modules `M_•`, `M'_•`, the complex \
  `s(M_• ⊗_B M'_•)` is quasi-isomorphic to the total complex of `s(M_•) ⊗_B s(M'_•)`"]
theorem flatEilenbergZilber.{t, s} (B : Type s) [CommRing B] :
    FlatEilenbergZilber.{t, s} B :=
  fun M N _ _ => ⟨alexanderWhitney M N, inferInstance⟩

end Stacks.ChaoticSite

end
