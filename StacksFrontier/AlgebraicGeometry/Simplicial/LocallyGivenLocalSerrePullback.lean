module

public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenLocalSerre
public import StacksFrontier.AlgebraicGeometry.Simplicial.TotalRestrictionSummand
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.StructureAugmentationPullback
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.RingedAugmentationStructureSheafChange

/-!
# Pulled-back modules among the cohomology modules of a glued object

In Situation 0DC9 let `A_U` be a local family of weak Serre subcategories (0DC2, 0DC3, 0DC4) with
every `E_U` in `D_{A_U}(O_{u(U)})`, let `L` be a simplicial object of `SR(B)`, `K = u(L)`, and let
`E` on `(C/K)_total` restrict to `E_{U_{n,i}}` on every summand `C/u(U_{n,i})`. If a cohomology
module `H^q(E)` is `a^*N` for an `O_C`-module `N`, `a` the ringed augmentation of Remark 0D9W
with the restricted structure sheaf, then `N|_{u(U_{n,i})}` lies in `A_{u(U_{n,i})}` for every
summand: it is the restriction of `a^*N = H^q(E)` to the summand.

This is the step of the proof of Stacks 0DCC which places the cohomology of the glued object in
`A_total`.

Consequently (`exists_derivedPullback_iso_of_cartesian_homology`), for a hypercovering `K` and
any ringed augmentation with invertible structure map, an object `E` of `D(O)` whose cohomology
modules are cartesian, and are `a^*N` only for `N` whose restrictions to the members of `K_0` lie
in the family, is `La^*F` for some `F` in `D_A(O_C)`: each `H^q(E)` is `a^*N` (Stacks 0D9Z), `N`
lies in `A` by the covering argument of Stacks 0DC7, and the essential surjectivity half of
Stacks 0DC7 applies.

## Main results

* `AlgebraicGeometry.RingedSite.LocallyGiven.overFunctor_mem_of_homology_iso_pullback`.
* `CategoryTheory.SimplicialSemiRepresentable.exists_derivedPullback_iso_of_cartesian_homology`.

## References

* [Stacks Project, Tag 0DCC](https://stacks.math.columbia.edu/tag/0DCC)
* [Stacks Project, Tag 0DC7](https://stacks.math.columbia.edu/tag/0DC7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.SimplicialSemiRepresentable

universe u uB vB

namespace AlgebraicGeometry.RingedSite.LocallyGiven

attribute [local instance] LocallyGiven.category HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

variable {X : RingedSite.{u, u, u}} [X.J.toCoverage.HasPullbacks]
  (G : LocallyGiven.{0, u, u, u, uB, vB} X) (L : SimplicialObject (FormalCoproduct.{u} G.B))
  (T : Stacks.Cohomology.CohomologicalDescent.LocalSerreFamily.{u} X)

/-- **A module pulled back to a cohomology module of the glued object has its restrictions to
the summands in the family.** If `H^q(E) ≅ a^*N`, then `N|_{u(U_{n,i})}`, which is the
restriction of `a^*N` to the summand `C/u(U_{n,i})` (`a^*` being restriction along `j_total`),
is the restriction of `H^q(E)` to that summand, and so lies in `A_{u(U_{n,i})}`. -/
theorem overFunctor_mem_of_homology_iso_pullback
    (hA : ∀ (U : G.B) (q : ℤ), T.A (G.u.obj U)
      ((DerivedCategory.homologyFunctor _ q).obj (G.obj U)))
    (E : DerivedCategory ((situation X.J (G.image L)).totalRingedTopos
      (structureSheaf X (G.image L))).Modules)
    (σ : G.SummandIdentification L E) (q : ℤ)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (e : (DerivedCategory.homologyFunctor _ q).obj E ≅
      (structureAugmentation X (G.image L)).totalRingedHom.toModulesHom.pullbackModules.obj N)
    (n : SimplexCategory) (i : (L.obj (op n)).I) :
    T.A (G.u.obj ((L.obj (op n)).obj i))
      ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (G.u.obj ((L.obj (op n)).obj i))).obj N) := by
  have := T.weakSerre (G.u.obj ((L.obj (op n)).obj i))
  refine (T.A _).prop_of_iso ?_ (G.summandRestriction_homology_mem L T hA E σ n i q)
  exact (G.summandRestrictionB L n i).mapIso
      (((situation X.J (G.image L)).componentModulesRestriction (structureSheaf X (G.image L))
        n).mapIso (e ≪≫ (structurePullbackModulesRestrictionIso X (G.image L)).app N)) ≪≫
    (totalRestrictionSummandIso X (G.image L) n i).app N

end AlgebraicGeometry.RingedSite.LocallyGiven

namespace CategoryTheory.SimplicialSemiRepresentable

open Stacks.CategoryTheory.Hypercovering Stacks.Cohomology.CohomologicalDescent

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyTotalModuleDescent
  CategoryTheory.SimplicialSiteSituation.wEqualsLocallyBijectiveTotalModuleDescent
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (P : Pretopology C)
  (O : Sheaf P.toGrothendieck CommRingCat.{u}) (Y : HypercoveringOfTerminal.{u} P)
  (T : LocalSerreFamily.{u} (pretopologyRingedSite P O))


/-- **The essential surjectivity half of Stacks 0DC7, for a ringed augmentation of a hypercovering
with invertible structure map, in terms of cartesian cohomology.** Let `E` be an object of `D(O)`
whose cohomology modules are cartesian, such that whenever `H^q(E) ≅ a^*N` the restrictions of `N`
to the members `U_{0,j}` of `K_0` lie in the family. Then `E = La^*F` for an `F` in `D_A(O_C)`:
each `H^q(E)` is `a^*N` (Stacks 0D9Z), `N` lies in `A` by the covering argument of Stacks 0DC7,
and `Stacks.CategoryTheory.Hypercovering.exists_derivedPullback_iso_of_localSerreFamily`
applies. -/
theorem exists_derivedPullback_iso_of_cartesian_homology
    (B : SimplicialSiteSituation.RingedAugmentation
      (situation P.toGrothendieck Y.toSimplicialObject)
      (Cat.of C) P.toGrothendieck (situationAugmentation P.toGrothendieck Y.toSimplicialObject))
    [hB : IsIso B.totalRingedHom.fSharpInverseImage]
    (T : LocalSerreFamily.{u} (pretopologyRingedSite P B.OD))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((situation P.toGrothendieck Y.toSimplicialObject).totalRingedTopos B.O).O)))
    (hcart : ∀ q : ℤ, (situation P.toGrothendieck Y.toSimplicialObject).IsModuleFiberTransitionIso
      B.O ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((situation P.toGrothendieck Y.toSimplicialObject).totalRingedTopos B.O).O)) q).obj E))
    (hN : ∀ (q : ℤ) (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B.OD)),
      (B.totalRingedHom.toModulesHom.pullbackModules.obj N ≅
        (DerivedCategory.homologyFunctor (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((situation P.toGrothendieck Y.toSimplicialObject).totalRingedTopos B.O).O)) q).obj E) →
      ∀ j : (Y.toSimplicialObject.obj (op (SimplexCategory.mk 0))).I,
        T.A _ ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf B.OD)
          ((Y.toSimplicialObject.obj (op (SimplexCategory.mk 0))).obj j)).obj N)) :
    ∃ F : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B.OD)),
      DerivedCategoryB.derivedCategoryB (LocalSerreFamily.globalProperty _ T) F ∧
        Nonempty ((RingedToposHom.leftDerivedPullbackOfIsIsoFSharp B.totalRingedHom).functor.obj F
          ≅ E) := by
  refine @exists_derivedPullback_iso_of_localSerreFamily _ _ _ _ P Y B hB T E fun q ↦ ?_
  obtain ⟨N, ⟨e⟩⟩ :=
    SimplicialSiteSituation.RingedAugmentation.essImage_pullbackModules Y B (hcart q)
  exact ⟨N, LocalSerreFamily.globalProperty_of_degreeZero P Y B.OD T N (hN q N e), ⟨e.symm⟩⟩

/-- **The essential surjectivity half of Stacks 0DC7 for the augmentation with the restricted
structure sheaf of a hypercovering**, at the spelling of Stacks 0DCA: an object `E` of `D(O)` whose
cohomology modules are cartesian, and are `a^*N` only for `N` whose restrictions to the members of
`K_0` lie in the family, is `La^*F` for some `F` in `D_A(O_C)`. -/
theorem exists_structurePullback_iso_of_cartesian_homology
    (E : DerivedCategory ((situation P.toGrothendieck Y.toSimplicialObject).totalRingedTopos
        (structureSheaf (pretopologyRingedSite P O) Y.toSimplicialObject)).Modules)
    (hcart : ∀ q : ℤ, (situation P.toGrothendieck Y.toSimplicialObject).IsModuleFiberTransitionIso
      (structureSheaf (pretopologyRingedSite P O) Y.toSimplicialObject)
      ((DerivedCategory.homologyFunctor
        ((situation P.toGrothendieck Y.toSimplicialObject).totalRingedTopos
        (structureSheaf (pretopologyRingedSite P O) Y.toSimplicialObject)).Modules q).obj E))
    (hN : ∀ (q : ℤ) (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)),
      ((structureAugmentation (pretopologyRingedSite P O)
        Y.toSimplicialObject).totalRingedHom.toModulesHom.pullbackModules.obj N ≅
          (DerivedCategory.homologyFunctor
            ((situation P.toGrothendieck Y.toSimplicialObject).totalRingedTopos
        (structureSheaf (pretopologyRingedSite P O) Y.toSimplicialObject)).Modules q).obj E) →
      ∀ j : (Y.toSimplicialObject.obj (op (SimplexCategory.mk 0))).I,
        T.A _ ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf O)
          ((Y.toSimplicialObject.obj (op (SimplexCategory.mk 0))).obj j)).obj N)) :
    ∃ F : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)),
      DerivedCategoryB.derivedCategoryB (LocalSerreFamily.globalProperty _ T) F ∧
        Nonempty ((RingedToposHom.leftDerivedPullbackOfIsIsoFSharp
          (structureAugmentation (pretopologyRingedSite P O)
            Y.toSimplicialObject).totalRingedHom).functor.obj F ≅ E) := by
  refine exists_derivedPullback_iso_of_cartesian_homology P Y
    (structureAugmentation (pretopologyRingedSite P O) Y.toSimplicialObject) T E (fun q ↦ ?_)
    (fun q N e j ↦ hN q N ?_ j)
  · convert hcart q using 3
    dsimp only [structureAugmentation_O]
    exact Iff.rfl
  · refine e ≪≫ eqToIso ?_
    dsimp only [structureAugmentation_O]
    rfl

end CategoryTheory.SimplicialSemiRepresentable

end
