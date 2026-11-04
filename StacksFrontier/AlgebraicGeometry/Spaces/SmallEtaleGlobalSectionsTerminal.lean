module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSheafConditionOneElement
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleGlobalSectionsFork

/-!
# Global sections over the small étale site are the sections at the terminal spaces-étale object

Let `X` be an algebraic space over a scheme `S`.  The small étale site of `X` has no terminal
object — its objects are étale *scheme* charts — so global sections of a sheaf on it is not
evaluation anywhere; `CategoryTheory.Sheaf.Γ` is the limit of the underlying presheaf over the
whole site.  The spaces-étale site of Stacks 03G0, by contrast, has `X` itself as a terminal
object, and the two sites have the same topos by Stacks 03G1.

This file identifies the two readings of global sections: for a sheaf `P` on the spaces-étale
site of `X`, with values in an arbitrary category, the cone over the étale scheme charts whose
vertex is `P(X)` and whose legs are the restrictions along the unique morphisms `U ⟶ X` of the
site is a *limit* cone.  Consequently global sections over the small étale site of the
restriction of `P` to the charts is `P(X)`, naturally in `P`.

For a sheaf of sets this is `AlgebraicGeometry.Space.bijective_restrictSectionsToCharts`.

## Main definitions

* `AlgebraicGeometry.Space.coneCharts`: the cone over the étale scheme charts with vertex the
  sections of `P` at the terminal object of the spaces-étale site.
* `AlgebraicGeometry.Space.spacesEtaleChartRestriction`: restriction of sheaves along the
  comparison functor of Stacks 03G1, at an arbitrary coefficient category.

## Main results

* `AlgebraicGeometry.Space.isLimitConeCharts`: `coneCharts` is a limit cone for a sheaf `P`.
* `AlgebraicGeometry.Space.ΓTerminalNatIso`: **global sections over the small étale site of the
  restriction of a spaces-étale sheaf are its sections at the terminal object**, as a natural
  isomorphism of functors `Sheaf(X_{spaces,étale}) ⥤ A`.
* `AlgebraicGeometry.Space.isZero_obj_of_isZero_chart`: a spaces-étale sheaf vanishing on a
  chart which covers an object vanishes on that object.

## References

* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03H7](https://stacks.math.columbia.edu/tag/03H7)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

variable {A : Type w} [Category.{w'} A]

/-! ### The cone over the charts -/

/-- **The sections at the terminal object, restricted to the étale scheme charts.**  For a
presheaf `P` on the spaces-étale site of `X`, the cone over the restriction of `P` to the étale
scheme charts whose vertex is `P(X)` and whose leg at a chart `U` is restriction along the
unique morphism `U ⟶ X` of the spaces-étale site. -/
def coneCharts (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A) :
    Cone ((comparisonFunctor B S hS X).op ⋙ P) where
  pt := P.obj (op (SpacesEtale.idObj B S hS X))
  π :=
    { app := fun V => P.map ((SpacesEtale.isTerminal_idObj B S hS X).from
        ((comparisonFunctor B S hS X).obj V.unop)).op
      naturality := fun V₁ V₂ g => by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_map,
          Functor.op_map]
        rw [Category.id_comp, ← P.map_comp, ← op_comp,
          (SpacesEtale.isTerminal_idObj B S hS X).hom_ext
            ((comparisonFunctor B S hS X).map g.unop ≫
              (SpacesEtale.isTerminal_idObj B S hS X).from
                ((comparisonFunctor B S hS X).obj V₁.unop))
            ((SpacesEtale.isTerminal_idObj B S hS X).from
              ((comparisonFunctor B S hS X).obj V₂.unop))] }

section IsLimit

variable (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A)

/-- For a sheaf `P` on the spaces-étale site with values in `A` and an object `a` of `A`, the
presheaf of sets `P ⋙ coyoneda.obj (op a)` of maps out of `a` into `P` is a sheaf. -/
theorem isSheaf_comp_coyoneda
    (hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) P) (a : A) :
    Presheaf.IsSheaf (SpacesEtale.topology B S hS X) (P ⋙ coyoneda.obj (op a)) :=
  (isSheaf_iff_isSheaf_of_type _ _).2 (hP a)

/-- The legs of a cone over the restriction of `P` to the charts, read as a compatible family of
maps out of its vertex — a section of the restriction of the sheaf of sets
`P ⋙ coyoneda.obj (op s.pt)`. -/
def coneSections (s : Cone ((comparisonFunctor B S hS X).op ⋙ P)) :
    ((comparisonFunctor B S hS X).op ⋙ (P ⋙ coyoneda.obj (op s.pt))).sections :=
  ⟨fun V => s.π.app V, fun {_ _} g => s.w g⟩

/-- **The cone over the charts is a limit cone.**  For a sheaf `P` on the spaces-étale site of
`X` with values in an arbitrary category, the sections of `P` at the terminal object are the
limit of its sections over the étale scheme charts. -/
def isLimitConeCharts (hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) P) :
    IsLimit (coneCharts B S hS X P) :=
  let e : ∀ s : Cone ((comparisonFunctor B S hS X).op ⋙ P),
      (P ⋙ coyoneda.obj (op s.pt)).obj (op (SpacesEtale.idObj B S hS X)) ≃
        ((comparisonFunctor B S hS X).op ⋙ (P ⋙ coyoneda.obj (op s.pt))).sections :=
    fun s => equivSectionsComparison B S hS (P ⋙ coyoneda.obj (op s.pt))
      (isSheaf_comp_coyoneda B S hS X P hP s.pt)
      (exists_isSurjective_chart B S hS X).choose_spec
  { lift := fun s => (e s).symm (coneSections B S hS X P s)
    fac := fun s W =>
      congrArg (fun σ : ((comparisonFunctor B S hS X).op ⋙
          (P ⋙ coyoneda.obj (op s.pt))).sections => σ.1 W)
        ((e s).apply_symm_apply (coneSections B S hS X P s))
    uniq := fun s _ hm => (e s).eq_symm_apply.2 (Subtype.ext (funext hm)) }

end IsLimit

/-! ### Vanishing on an object from vanishing on a chart covering it -/

section Vanishing

variable [Limits.HasZeroMorphisms A]

/-- **A sheaf on the spaces-étale site which vanishes on a chart covering an object vanishes on
that object.**  If `g : U ⟶ V` is a morphism of the spaces-étale site from an étale scheme
chart `U`, surjective on points, and the sections of `P` at `U` are a zero object, then so are
the sections of `P` at `V`. -/
theorem isZero_obj_of_isZero_chart (P : Sheaf (SpacesEtale.topology B S hS X) A)
    {V : SpacesEtale B S hS X} {U : SmallEtale B S hS X.1}
    (g : (comparisonFunctor B S hS X).obj U ⟶ V)
    (hg : IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map g).hom)
    (hU : Limits.IsZero (P.obj.obj (op ((comparisonFunctor B S hS X).obj U)))) :
    Limits.IsZero (P.obj.obj (op V)) :=
  have hpb := IsPullback.of_hasPullback g g
  (IsZero.iff_id_eq_zero _).2 <| Fork.IsLimit.hom_ext
    (isLimitForkOfSurjectiveSingleton B S hS P.obj P.cond hg hpb
      (Presheaf.fork_condition_of_isPullback P.obj hpb)) (hU.eq_of_tgt _ _)

end Vanishing

/-! ### Global sections of the restriction to the charts -/

/-- Restriction of sheaves along the comparison functor of Stacks 03G1, at an arbitrary
coefficient category: a sheaf on the spaces-étale site of `X` read on the étale scheme charts.
For sheaves of sets this is the equivalence
`AlgebraicGeometry.Space.smallEtaleToposEquiv`. -/
abbrev spacesEtaleChartRestriction :
    Sheaf (SpacesEtale.topology B S hS X) A ⥤ Sheaf (SmallEtale.topology B S hS X.1) A :=
  (comparisonFunctor B S hS X).sheafPushforwardContinuous A
    (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)

variable [HasWeakSheafify (SmallEtale.topology B S hS X.1) A]
    [HasGlobalSectionsFunctor (SmallEtale.topology B S hS X.1) A]

/-- `AlgebraicGeometry.Space.coneCharts` at a sheaf, with its vertex written as the value of the
sections functor at the terminal object of the spaces-étale site. -/
abbrev coneChartsSheaf (G : Sheaf (SpacesEtale.topology B S hS X) A) :
    Cone ((comparisonFunctor B S hS X).op ⋙ G.obj) where
  pt := ((sheafSections (SpacesEtale.topology B S hS X) A).obj
    (op (SpacesEtale.idObj B S hS X))).obj G
  π := (coneCharts B S hS X G.obj).π

/-- `AlgebraicGeometry.Space.coneChartsSheaf` is a limit cone. -/
abbrev isLimitConeChartsSheaf (G : Sheaf (SpacesEtale.topology B S hS X) A) :
    IsLimit (coneChartsSheaf B S hS X G) :=
  isLimitConeCharts B S hS X G.obj G.cond

/-- The global-sections cone of the restriction of `G` to the charts, as a cone over the
composite of `G` with the opposite of the comparison functor, with its vertex written as the
value of the composite functor. -/
abbrev coneΓSheaf (G : Sheaf (SpacesEtale.topology B S hS X) A) :
    Cone ((comparisonFunctor B S hS X).op ⋙ G.obj) where
  pt := (spacesEtaleChartRestriction B S hS X ⋙ Sheaf.Γ (SmallEtale.topology B S hS X.1) A).obj G
  π := ((spacesEtaleChartRestriction B S hS X (A := A)).obj G).coneΓ.π

/-- `AlgebraicGeometry.Space.coneΓSheaf` is a limit cone. -/
abbrev isLimitConeΓSheaf (G : Sheaf (SpacesEtale.topology B S hS X) A) :
    IsLimit (coneΓSheaf B S hS X G) :=
  Sheaf.isLimitConeΓ _

/-- **Global sections over the small étale site are the sections at the terminal spaces-étale
object.**  For a sheaf `P` on the spaces-étale site of `X`, the global sections — over the small
étale site — of the restriction of `P` to the étale scheme charts are the sections of `P` at the
terminal object `X` of the spaces-étale site, naturally in `P`. -/
def ΓTerminalNatIso :
    (sheafSections (SpacesEtale.topology B S hS X) A).obj (op (SpacesEtale.idObj B S hS X)) ≅
      spacesEtaleChartRestriction B S hS X ⋙ Sheaf.Γ (SmallEtale.topology B S hS X.1) A :=
  NatIso.ofComponents
    (fun G => (isLimitConeChartsSheaf B S hS X G).conePointUniqueUpToIso
      (isLimitConeΓSheaf B S hS X G))
    (fun {G₁ G₂} φ => (isLimitConeΓSheaf B S hS X G₂).hom_ext fun V => by
      have f₂ := IsLimit.conePointUniqueUpToIso_hom_comp
        (isLimitConeChartsSheaf B S hS X G₂) (isLimitConeΓSheaf B S hS X G₂) V
      have f₁ := IsLimit.conePointUniqueUpToIso_hom_comp
        (isLimitConeChartsSheaf B S hS X G₁) (isLimitConeΓSheaf B S hS X G₁) V
      have f₃ : ((sheafSections (SpacesEtale.topology B S hS X) A).obj
              (op (SpacesEtale.idObj B S hS X))).map φ ≫
            (coneChartsSheaf B S hS X G₂).π.app V =
          (coneChartsSheaf B S hS X G₁).π.app V ≫
            φ.hom.app (op ((comparisonFunctor B S hS X).obj V.unop)) :=
        (φ.hom.naturality ((SpacesEtale.isTerminal_idObj B S hS X).from
          ((comparisonFunctor B S hS X).obj V.unop)).op).symm
      rw [Category.assoc, f₂, f₃, ← f₁, Category.assoc, Category.assoc]
      exact whisker_eq _
        (Sheaf.ΓRes_naturality ((spacesEtaleChartRestriction B S hS X (A := A)).map φ) V).symm)

end AlgebraicGeometry.Space

end
