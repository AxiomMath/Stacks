module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogResidueSequenceBase
public import StacksFrontier.AlgebraicGeometry.DeRham.Functoriality
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsGeneratorCalculus
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Basic

/-!
# The de Rham complex of a divisor as a direct image of abelian sheaves

For a closed subscheme `i : Y ⟶ X` given by an ideal sheaf, the complex
`Scheme.Hom.divisorDeRhamBase f I` of sheaves of `f^{-1}𝒪_S`-modules is `i_*Ω^•_{Y/S}`, and the
restriction of forms `Ω^•_{X/S} ⟶ i_*Ω^•_{Y/S}` of the proof of Stacks Tag 0FUQ is the canonical
map of de Rham complexes of Tag 07HX. This file records both, after forgetting the module
structures: the underlying complex of abelian sheaves is the direct image of abelian sheaves of the
de Rham complex of `Y`, and the underlying map of the restriction is
`AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMap`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.divisorDeRhamAbIso`: the identification of the underlying complex
  of abelian sheaves of `i_*Ω^•_{Y/S}` with the direct image of that of `Ω^•_{Y/S}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.toSheaf_divisorRestrictionBase_comp_divisorDeRhamAbIso`: the
  restriction of forms is the canonical map of Tag 07HX.

## References

* [Stacks Project, Tag 0FUQ](https://stacks.math.columbia.edu/tag/0FUQ)
* [Stacks Project, Tag 07HX](https://stacks.math.columbia.edu/tag/07HX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)

/-- **The underlying complex of abelian sheaves of `i_*Ω^•_{Y/S}` is the direct image of that of
`Ω^•_{Y/S}`**: the identity in every degree. -/
def divisorDeRhamAbIso :
    ((_root_.SheafOfModules.toSheaf (baseRingSheaf f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (divisorDeRhamBase f I) ≅
      ((Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u}
          I.subschemeι.base).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplex (deRhamAlgebras (I.subschemeι ≫ f))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (deRhamAlgebras (I.subschemeι ≫ f)))) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) fun i j hij => by
    obtain rfl : i + 1 = j := hij
    simp only [Iso.refl_hom, Functor.mapHomologicalComplex_obj_d, divisorDeRhamBase_d]
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U =>
      AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)))
    rfl

/-- **The restriction of forms `Ω^•_{X/S} ⟶ i_*Ω^•_{Y/S}`, read in abelian sheaves, is the
canonical map of de Rham complexes of Stacks Tag 07HX.** -/
theorem toSheaf_divisorRestrictionBase_comp_divisorDeRhamAbIso :
    ((_root_.SheafOfModules.toSheaf (baseRingSheaf f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (divisorRestrictionBase f I) ≫ (divisorDeRhamAbIso f I).hom =
      deRhamAbelianPushforwardMap I.subschemeι f (I.subschemeι ≫ f) (𝟙 S) (by simp) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U =>
    AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)))
  exact congrArg (fun φ : relativeDifferentialForms f (n : ℤ) ⟶
      (Scheme.Modules.pushforward I.subschemeι).obj
        (relativeDifferentialForms (I.subschemeι ≫ f) (n : ℤ)) => φ.app U.unop x)
    (Stacks.DeRham.FormsGenerators.formsDirectImageComparison_eq f I.subschemeι (n : ℤ))

end AlgebraicGeometry.Scheme.Hom
