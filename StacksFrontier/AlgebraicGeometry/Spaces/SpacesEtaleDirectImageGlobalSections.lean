module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleGlobalSectionsFork

/-!
# Global sections of a direct image along a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B` and let `H` be a sheaf of sets on the spaces-étale site of `X`.  The direct image of
`H` along `f`, read on the étale scheme charts of `Y` — the functor
`AlgebraicGeometry.Space.spacesDirectImageRestriction` through which the small étale direct
image of Stacks 03G2, part (3) is computed — has the same global sections as `H` itself read on
the étale scheme charts of `X`:

`Γ(Y, f_* H) ≃ Γ(X, H)`.

Global sections are the sections of the presheaf on the small étale site, that is the limit of
its values over all étale scheme charts, which is how
`AlgebraicGeometry.Space.restrictSectionsToCharts` and
`AlgebraicGeometry.Space.equivSectionsComparison` compute them.  The identification is the
composite of three: the global sections of the direct image are its value at the terminal object
`Y` of the spaces-étale site of `Y`, by Stacks 03M8 on global sections; that value is the value
of `H` at the cartesian base change of `Y`, by definition of the direct image; and that base
change is again terminal, by `AlgebraicGeometry.Space.isTerminal_spacesBaseChange_idObj`, so the
value is the value of `H` at the terminal object `X`, which is the global sections of `H`.

## Main definitions

* `AlgebraicGeometry.Space.spacesBaseChangeIdObjIso` identifies the cartesian base change of the
  terminal object of the spaces-étale site of `Y` with the terminal object of that of `X`.
* `AlgebraicGeometry.Space.equivSectionsSpacesDirectImage` is the identification
  `Γ(Y, f_* H) ≃ Γ(X, H)`.

## Implementation notes

`AlgebraicGeometry.Space.bijective_restrictSectionsToCharts` is used once on each side, and each
use needs an étale scheme chart whose structure morphism is surjective on points.  Those charts
are produced rather than assumed: `AlgebraicGeometry.Space.exists_isSurjective_chart` supplies
one for any algebraic space, an atlas being such a chart, so the statement carries no
hypotheses.

The sheaves are valued in `Type (u + 1)`, the universe of the objects of the two étale sites,
because that is the universe at which Stacks 03G1 and Stacks 03G2, part (3) are instantiated in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleToposMorphism.lean`, hence the universe of
`AlgebraicGeometry.Space.spacesDirectImageRestriction`.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **The cartesian base change of the terminal object is terminal.**  The base change along `f`
of the terminal object of the spaces-étale site of `Y` is canonically the terminal object of the
spaces-étale site of `X`: both are terminal, by
`AlgebraicGeometry.Space.isTerminal_spacesBaseChange_idObj` and
`AlgebraicGeometry.Space.SpacesEtale.isTerminal_idObj`. -/
noncomputable def spacesBaseChangeIdObjIso :
    (spacesBaseChange B S hS f).functor.obj (SpacesEtale.idObj B S hS Y) ≅
      SpacesEtale.idObj B S hS X :=
  (isTerminal_spacesBaseChange_idObj B S hS f).uniqueUpToIso
    (SpacesEtale.isTerminal_idObj B S hS X)

/-- **The direct image of a spaces-étale sheaf has the same global sections as the sheaf.**  Let
`H` be a sheaf of sets on the spaces-étale site of `X`.  If `X` and `Y` admit étale scheme
charts whose structure morphisms are surjective on points — which every algebraic space does,
`AlgebraicGeometry.Space.exists_isSurjective_chart` — then the global sections of the direct
image of `H` along `f`, computed over the small étale site of `Y`, are the global sections of `H`
computed over the small étale site of `X`.

The direct image over an étale scheme chart `V` of `Y` is the sections of `H` over the cartesian
base change `X ×_Y V`, so this says that the compatible families of such sections, indexed by
the charts of `Y`, are the compatible families of sections of `H` over the charts of `X`.  Both
are computed by Stacks 03M8 on global sections,
`AlgebraicGeometry.Space.equivSectionsComparison`, as the value at the terminal object of the
respective spaces-étale site, and the two terminal objects correspond under base change by
`AlgebraicGeometry.Space.spacesBaseChangeIdObjIso`. -/
noncomputable def equivSectionsSpacesDirectImage
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1))) :
    ((spacesDirectImageRestriction B S hS f).obj H).obj.sections ≃
      ((comparisonRestriction B S hS X).obj H).obj.sections :=
  (equivSectionsComparison B S hS
        (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).obj H).obj
        (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).obj H).property
        (exists_isSurjective_chart B S hS Y).choose_spec).symm.trans
    ((H.obj.mapIso (spacesBaseChangeIdObjIso B S hS f).symm.op).toEquiv.trans
      (equivSectionsComparison B S hS H.obj H.property
        (exists_isSurjective_chart B S hS X).choose_spec))

/-- **The identification `Γ(Y, f_* H) ≃ Γ(X, H)` is restriction along any arrow into a cartesian
base change.**  Let `τ` be a global section of the direct image of `H`, that is a compatible
family of sections of `H` over the algebraic spaces `X ×_Y V` indexed by the étale scheme charts
`V` of `Y`.  Then the member at an étale scheme chart `U` of `X` of the global section of `H` it
corresponds to is the restriction, along any arrow `U ⟶ X ×_Y V`, of the member of the family
at `V`.

Both sides are the restriction of the section of `H` over the terminal object that `τ` comes
from, along a morphism `U ⟶ X ×_Y Y`; and `X ×_Y Y` is again terminal, by
`AlgebraicGeometry.Space.isTerminal_spacesBaseChange_idObj`, so the two morphisms agree. -/
theorem equivSectionsSpacesDirectImage_val
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)))
    (τ : ((spacesDirectImageRestriction B S hS f).obj H).obj.sections)
    (U : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (k : (comparisonFunctor B S hS X).obj U ⟶ chartBaseChange B S hS f V) :
    (equivSectionsSpacesDirectImage B S hS f H τ).val (op U) =
      H.obj.map k.op (τ.val (op V)) := by
  set D := ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).obj H with hD
  set x := (equivSectionsComparison B S hS D.obj D.property
    (exists_isSurjective_chart B S hS Y).choose_spec).symm τ with hx
  have hτ : τ.val (op V) =
      H.obj.map ((spacesBaseChange B S hS f).functor.map
        ((SpacesEtale.isTerminal_idObj B S hS Y).from
          ((comparisonFunctor B S hS Y).obj V))).op x := by
    conv_lhs => rw [← (equivSectionsComparison B S hS D.obj D.property
      (exists_isSurjective_chart B S hS Y).choose_spec).apply_symm_apply τ]
    rfl
  have hL : (equivSectionsSpacesDirectImage B S hS f H τ).val (op U) =
      H.obj.map ((SpacesEtale.isTerminal_idObj B S hS X).from
          ((comparisonFunctor B S hS X).obj U)).op
        (H.obj.map (spacesBaseChangeIdObjIso B S hS f).inv.op x) := rfl
  have hc {A C E : (SpacesEtale B S hS X)ᵒᵖ} (a : C ⟶ E) (b : A ⟶ C) (y) :
      H.obj.map a (H.obj.map b y) = H.obj.map (b ≫ a) y := by
    rw [Functor.map_comp]; rfl
  rw [hL, hτ]
  refine (hc _ _ _).trans (Eq.trans ?_ (hc _ _ _).symm)
  exact congrArg (fun g ↦ H.obj.map (Quiver.Hom.op g) x)
    ((isTerminal_spacesBaseChange_idObj B S hS f).hom_ext _ _)

end AlgebraicGeometry.Space

end
