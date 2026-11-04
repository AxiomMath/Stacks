module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.SiteIsomorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Topological invariance of the étale site, in one statement

The conjunction of the three parts of [Stacks, Tag 03SI] for a universal homeomorphism `f`: the
étale sites are isomorphic, the étale topoi are equivalent, and étale cohomology agrees.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f]

/-- **Topological invariance of the étale site.** Let `f : X ⟶ Y` be a universal homeomorphism
of schemes (for example the closed immersion defined by a nilpotent sheaf of ideals). Then

1. the étale sites of `Y` and `X` are isomorphic: base change along `f` is an equivalence of the
   small étale categories, and a sieve on a scheme étale over `Y` is covering exactly when its
   image under base change is covering;
2. the étale topoi of `Y` and `X` are equivalent; and
3. `H^q` of every abelian sheaf on the small étale site of `Y` agrees with `H^q` of its
   restriction along `f`, for every `q`,

the étale topoi being compared through `Stacks.EtaleCohomology.smallEtaleInverseImage` and the
comparison on cohomology being `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap`.

The `CategoryTheory.HasSheafify` and `CategoryTheory.HasExt.{w}` instances on the two categories
of abelian sheaves are the ones needed to state part (3). -/
@[ega "IV 18.1.2" "more general",
  sga "1 IX 1.7" "more general",
  sga "1 IX 4.10",
  sga "4 XIV 1.11" "more general",
  sga "4½ Th_finitude 2.7" "more general"]
theorem
    smallEtaleSite_iso_and_topoi_equivalent_and_etaleCohomology_bijective_of_universalHomeomorphism
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    ((smallEtaleBaseChange f).IsEquivalence ∧
        ∀ (V : Y.Etale) (S : Sieve V),
          S.functorPushforward (smallEtaleBaseChange f) ∈
              smallEtaleTopology X ((smallEtaleBaseChange f).obj V) ↔
            S ∈ smallEtaleTopology Y V) ∧
      (smallEtaleInverseImage.{u, v} f).IsEquivalence ∧
      ∀ (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ),
        Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f F q) :=
  ⟨smallEtaleSite_iso_of_universalHomeomorphism f,
    smallEtaleInverseImage_isEquivalence_of_universalHomeomorphism.{u, v} f,
    fun F q ↦ etaleCohomologyRestrictionMap_bijective_of_universalHomeomorphism.{u, v, w} f F q⟩

end Stacks.EtaleCohomology

end
