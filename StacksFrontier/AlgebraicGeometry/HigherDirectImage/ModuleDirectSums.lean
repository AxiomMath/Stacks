module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToSheafColimits
public import StacksFrontier.AlgebraicGeometry.Cohomology.ColimitsHigherDirect.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.ModuleAbelianComparison
public import StacksFrontier.CategoryTheory.Triangulated.CoproductComparison

/-!
# Higher direct images of sheaves of modules commute with direct sums

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes. For every `p` the
`p`-th higher direct image of sheaves of modules `R^p f_* : Mod(𝒪_X) ⥤ Mod(𝒪_S)` commutes with
direct sums indexed by an arbitrary type of the scheme universe:

`R^p f_* (⨁ᵢ ℱᵢ) = ⨁ᵢ R^p f_* ℱᵢ`.

The same statement for sheaves of abelian groups is
`Stacks.Cohomology.SchemeColimits.higherDirectImage_preservesColimitsOfShape_discrete`, and the
two higher direct images agree after forgetting the module structure, by
`Stacks.AlgebraicGeometry.HigherDirectImage.rightDerivedPushforwardToSheafIso`. Forgetting the
module structure preserves direct sums and reflects isomorphisms, so the abelian statement
implies the module one.

## Main results

* `Stacks.AlgebraicGeometry.HigherDirectImage.preservesColimitsOfShape_discrete_rightDerived`:
  **`R^p f_*` on sheaves of modules preserves direct sums indexed by an arbitrary type of the
  scheme universe.**

## Implementation notes

The reduction is run on comparison morphisms rather than on colimit cocones, through
`CategoryTheory.Limits.isIso_sigmaComparison_of_isIso_comp`: what the abelian statement and the
comparison of the two higher direct images give is that the comparison morphism of
`R^p f_* ⋙ forget` is invertible, and what is wanted is invertibility of the comparison morphism
of `R^p f_*` alone. The two differ by the comparison morphism of `forget`, invertible because
forgetting preserves direct sums; since `forget` reflects isomorphisms, the remaining factor is
invertible too. Translating back into `PreservesColimitsOfShape` is
`CategoryTheory.Limits.preservesColimitsOfShape_discrete_of_isIso_sigmaComparison`.

`AlgebraicGeometry.Scheme.Modules X` is a definition reducing to
`SheafOfModules X.ringCatSheaf`, but the two carry separately declared `Category` instances and
instance search does not pass between them. Every fact about `SheafOfModules.toSheaf` is
therefore handed to the comparison lemmas as an explicit argument, where it is checked up to
definitional equality, rather than being left to synthesis; this is why
`CategoryTheory.Limits.isIso_sigmaComparison_of_preservesColimit` exists and why the reflection
of isomorphisms is passed by hand.

The abelian direct image is spelled as the direct image along the continuous functor
`Opens.map f.base` between the Grothendieck topologies of open covers, which is the spelling of
the comparison; `TopCat.Sheaf.pushforward AddCommGrpCat f.base`, the spelling of the abelian
direct-sum statement, is the same functor on the nose.

No `@[stacks]` attribute is attached. [Stacks, Tag 07TB] is the statement about *filtered*
colimits, carried by
`Stacks.Cohomology.SchemeColimits.higherDirectImage_preservesFilteredColimits`; a direct sum is
not a filtered colimit, and what is below is the direct-sum companion of that tag in the module
spelling, which is the form needed by an argument citing Tag 07TB for a direct sum of
quasi-coherent modules.

## References

* [Stacks Project, Tag 07TB](https://stacks.math.columbia.edu/tag/07TB)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.HigherDirectImage

universe u

/-- Direct sums of abelian sheaves on the small Zariski site of a scheme, indexed by a type of
the scheme universe. The instance is `CategoryTheory.Sheaf.instHasColimitsOfShape`, recorded
here because instance search does not reach it at that index size within its budget: the
colimits of abelian groups it asks for are themselves found only near the end of the search. -/
local instance hasColimitsOfShape_discrete_sheafAb (Z : Scheme.{u}) (ι : Type u) :
    HasColimitsOfShape (Discrete ι)
      (Sheaf (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}) :=
  haveI : HasColimitsOfShape (Discrete ι) AddCommGrpCat.{u} := inferInstance
  CategoryTheory.Sheaf.instHasColimitsOfShape

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The direct image of abelian sheaves along the continuous functor between the Grothendieck
topologies of open covers of the target and of the source. This is the spelling in which
`Stacks.AlgebraicGeometry.HigherDirectImage.rightDerivedPushforwardToSheafIso` compares the
module and abelian higher direct images. -/
abbrev abelianPushforward :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u} :=
  (Opens.map f.base).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology S.carrier) (Opens.grothendieckTopology X.carrier)

/-- The direct image of abelian sheaves along the continuous functor between the Grothendieck
topologies of open covers is the direct image of abelian sheaves along the continuous map of
underlying spaces. -/
theorem abelianPushforward_eq :
    abelianPushforward f = TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base :=
  rfl

variable [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f] (p : ℕ)
  (α : Type u)

/-- **`R^p f_*` on sheaves of modules preserves direct sums.** For a quasi-compact and
quasi-separated morphism of schemes `f : X ⟶ S`, the `p`-th higher direct image
`R^p f_* : Mod(𝒪_X) ⥤ Mod(𝒪_S)` commutes with direct sums indexed by an arbitrary type of the
scheme universe. -/
theorem preservesColimitsOfShape_discrete_rightDerived :
    PreservesColimitsOfShape (Discrete α)
      ((Scheme.Modules.pushforward f).rightDerived p) := by
  have htoX : PreservesColimitsOfShape (Discrete α)
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf) :=
    SheafOfModules.preservesColimitsOfShape_toSheaf X.ringCatSheaf
  have htoS : PreservesColimitsOfShape (Discrete α)
      (SheafOfModules.toSheaf.{u} S.ringCatSheaf : S.Modules ⥤ _) :=
    SheafOfModules.preservesColimitsOfShape_toSheaf S.ringCatSheaf
  have hab : PreservesColimitsOfShape (Discrete α) ((abelianPushforward f).rightDerived p) :=
    Stacks.Cohomology.SchemeColimits.higherDirectImage_preservesColimitsOfShape_discrete f p α
  have habforget : PreservesColimitsOfShape (Discrete α)
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙ (abelianPushforward f).rightDerived p) :=
    comp_preservesColimitsOfShape _ _
  have hforgetab : PreservesColimitsOfShape (Discrete α)
      ((Scheme.Modules.pushforward f).rightDerived p ⋙
        SheafOfModules.toSheaf.{u} S.ringCatSheaf) :=
    (preservesColimitsOfShape_iff_of_natIso
      (rightDerivedPushforwardToSheafIso f p).symm).mp habforget
  refine preservesColimitsOfShape_discrete_of_isIso_sigmaComparison _ fun M ↦ ?_
  have hcomp : IsIso (sigmaComparison
      ((Scheme.Modules.pushforward f).rightDerived p ⋙
        SheafOfModules.toSheaf.{u} S.ringCatSheaf) M) :=
    isIso_sigmaComparison_of_preservesColimit _ M hforgetab.preservesColimit
  have hforget := isIso_sigmaComparison_of_preservesColimit
    (SheafOfModules.toSheaf.{u} S.ringCatSheaf)
    (fun j ↦ ((Scheme.Modules.pushforward f).rightDerived p).obj (M j))
    htoS.preservesColimit
  exact isIso_sigmaComparison_of_isIso_comp ((Scheme.Modules.pushforward f).rightDerived p)
    (SheafOfModules.toSheaf.{u} S.ringCatSheaf) M
    (inferInstance : Functor.ReflectsIsomorphisms (SheafOfModules.toSheaf.{u} S.ringCatSheaf))
    hcomp hforget

end Stacks.AlgebraicGeometry.HigherDirectImage

end
