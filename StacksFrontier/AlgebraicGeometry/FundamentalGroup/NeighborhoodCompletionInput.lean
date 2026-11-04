module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.NeighbourhoodCompletion
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction

/-!
# The neighbourhoods of a closed subscheme as inputs to the completion conditions

The fundamental-group chapter indexes the open neighbourhoods of the closed subscheme cut out by
an ideal sheaf `Y` by `Stacks.FundamentalGroup.Neighborhood X Y`, whose membership condition is
the existence of a factorization of `Y.subschemeι` through the open. The completion conditions of
[Stacks, Tag 0EK2] are stated for a closed immersion `i : Y ⟶ X` and quantify over opens `V`
subject to `Set.range i.base ⊆ V`. The two conditions say the same thing, and this file provides
the translation in both directions together with the one consequence it is wanted for: condition
(4) of the tag, applied at a neighbourhood in the chapter's sense.

Nothing here is new mathematics. It exists because the private bridge
`Stacks.FundamentalGroup.exists_lift_subschemeι_iff` in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction` is not exported, and
because the translation has to be available on both sides at once: the opens produced by the
completion conditions are opens of a neighbourhood, and have to be turned back into
neighbourhoods of the chapter.

## Main definitions

* `Stacks.FundamentalGroup.Neighborhood.ofRangeSubset` — an open containing the image of
  `Y.subschemeι` is a neighbourhood.

## Main results

* `Stacks.FundamentalGroup.Neighborhood.range_subschemeι_subset` — the converse: a neighbourhood
  contains the image of `Y.subschemeι`. This is the hypothesis the completion conditions ask for.
* `Stacks.FundamentalGroup.Neighborhood.homOfLE_ofRangeSubset` — an open of a neighbourhood which
  still contains the closed subscheme is a smaller neighbourhood, with the transition morphism.
* `Stacks.FundamentalGroup.isHomsComplete_of_completionFullyFaithfulComplete` — condition (4) of
  [Stacks, Tag 0EK2] read at a neighbourhood: for finite locally free modules `G`, `F` on a
  neighbourhood `V`, the colimit over the opens of `V` containing the closed subscheme of the
  morphisms `G|_W ⟶ F|_W` is the inverse limit of the morphisms on the infinitesimal
  neighbourhoods.

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.FundamentalGroup

variable (X : Scheme.{u}) (Y : X.IdealSheafData)

/-- **A neighbourhood contains the image of the closed immersion.** This is the form of the
containment condition that the completion conditions of [Stacks, Tag 0EK2] ask for. -/
public theorem Neighborhood.range_subschemeι_subset (V : Neighborhood X Y) :
    Set.range (Y.subschemeι).base ⊆ (Neighborhood.open X Y V : Set X) :=
  le_trans (le_of_eq Y.range_subschemeι) (Neighborhood.support_subset_open X Y V)

/-- **An open containing the image of the closed immersion is a neighbourhood.** -/
public def Neighborhood.ofRangeSubset (W : X.Opens)
    (hW : Set.range (Y.subschemeι).base ⊆ (W : Set X)) : Neighborhood X Y :=
  OrderDual.toDual
    ⟨W, IsOpenImmersion.lift W.ι Y.subschemeι
        (by rw [Scheme.Opens.range_ι]; exact hW),
      IsOpenImmersion.lift_fac _ _ _⟩

/-- The open underlying the neighbourhood attached to an open is that open. -/
public theorem Neighborhood.open_ofRangeSubset (W : X.Opens)
    (hW : Set.range (Y.subschemeι).base ⊆ (W : Set X)) :
    Neighborhood.open X Y (Neighborhood.ofRangeSubset X Y W hW) = W :=
  rfl

/-- **Shrinking a neighbourhood.** An open contained in a neighbourhood and still containing the
image of the closed immersion is a smaller neighbourhood, and the transition morphism of the
index category is the one attached to the inclusion. -/
public def Neighborhood.homOfLE_ofRangeSubset (V : Neighborhood X Y) (W : X.Opens)
    (hW : Set.range (Y.subschemeι).base ⊆ (W : Set X)) (hle : W ≤ Neighborhood.open X Y V) :
    V ⟶ Neighborhood.ofRangeSubset X Y W hW :=
  homOfLE (show (OrderDual.ofDual (Neighborhood.ofRangeSubset X Y W hW)).val ≤
    (OrderDual.ofDual V).val from hle)

/-- **Condition (4) of [Stacks, Tag 0EK2], read at a neighbourhood of the chapter.** For two
finite locally free modules on an open neighbourhood `V` of the closed subscheme cut out by `Y`,
the colimit over the opens of `V` containing the closed subscheme of the morphisms between their
restrictions is the inverse limit of the morphisms between their restrictions to the
infinitesimal neighbourhoods. -/
public theorem isHomsComplete_of_completionFullyFaithfulComplete
    (h : Stacks.Algebraization.NeighbourhoodCompletion.CompletionFullyFaithfulComplete
      Y.subschemeι)
    (V : Neighborhood X Y)
    (G F : (Neighborhood.open X Y V).toScheme.Modules)
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F) :
    (Stacks.Algebraization.nbhdTower Y.subschemeι (Neighborhood.open X Y V)
      (Neighborhood.range_subschemeι_subset X Y V)).IsHomsComplete G F :=
  h (Neighborhood.open X Y V) (Neighborhood.range_subschemeι_subset X Y V) G F hG hF

/-! ### Opens of a neighbourhood as smaller neighbourhoods

The completion conditions produce an open of the neighbourhood `V` they were applied at, whereas
the chapter's index category is made of opens of `X`. The two are matched by the image of the
open under the inclusion `V ⊆ X`, which is the same scheme. -/

/-- An open of a neighbourhood, read as an open of `X`. -/
public def Neighborhood.imageOpen (V : Neighborhood X Y)
    (W : (Neighborhood.open X Y V).toScheme.Opens) : X.Opens :=
  (Neighborhood.open X Y V).ι ''ᵁ W

/-- The image of an open of a neighbourhood is contained in the neighbourhood. -/
public theorem Neighborhood.imageOpen_le (V : Neighborhood X Y)
    (W : (Neighborhood.open X Y V).toScheme.Opens) :
    Neighborhood.imageOpen X Y V W ≤ Neighborhood.open X Y V :=
  Scheme.Opens.ι_image_le _ W

/-- An open of a neighbourhood and its image in `X` are the same scheme. -/
public def Neighborhood.imageOpenIso (V : Neighborhood X Y)
    (W : (Neighborhood.open X Y V).toScheme.Opens) :
    W.toScheme ≅ (Neighborhood.imageOpen X Y V W).toScheme :=
  (Neighborhood.open X Y V).ι.isoImage W

/-- The identification of an open of a neighbourhood with its image is compatible with the two
inclusions into `X`. -/
public theorem Neighborhood.imageOpenIso_hom_ι (V : Neighborhood X Y)
    (W : (Neighborhood.open X Y V).toScheme.Opens) :
    (Neighborhood.imageOpenIso X Y V W).hom ≫ (Neighborhood.imageOpen X Y V W).ι =
      W.ι ≫ (Neighborhood.open X Y V).ι :=
  Scheme.Hom.isoImage_hom_ι _ W

/-- An open of a neighbourhood containing the support of the lifted tower has an image containing
the closed subscheme. -/
public theorem Neighborhood.range_subschemeι_subset_imageOpen (V : Neighborhood X Y)
    (W : (Neighborhood.open X Y V).toScheme.Opens)
    (hW : (Stacks.Algebraization.nbhdTower Y.subschemeι (Neighborhood.open X Y V)
      (Neighborhood.range_subschemeι_subset X Y V)).support ⊆ W) :
    Set.range (Y.subschemeι).base ⊆ (Neighborhood.imageOpen X Y V W : Set X) :=
  Stacks.Algebraization.range_subset_image_of_support_subset Y.subschemeι
    (Neighborhood.open X Y V) (Neighborhood.range_subschemeι_subset X Y V) W hW

/-- **An open of a neighbourhood containing the closed subscheme is a smaller neighbourhood.** -/
public def Neighborhood.shrink (V : Neighborhood X Y)
    (W : (Neighborhood.open X Y V).toScheme.Opens)
    (hW : (Stacks.Algebraization.nbhdTower Y.subschemeι (Neighborhood.open X Y V)
      (Neighborhood.range_subschemeι_subset X Y V)).support ⊆ W) : Neighborhood X Y :=
  Neighborhood.ofRangeSubset X Y (Neighborhood.imageOpen X Y V W)
    (Neighborhood.range_subschemeι_subset_imageOpen X Y V W hW)

/-- The transition morphism of the index category onto a smaller neighbourhood. -/
public def Neighborhood.shrinkHom (V : Neighborhood X Y)
    (W : (Neighborhood.open X Y V).toScheme.Opens)
    (hW : (Stacks.Algebraization.nbhdTower Y.subschemeι (Neighborhood.open X Y V)
      (Neighborhood.range_subschemeι_subset X Y V)).support ⊆ W) :
    V ⟶ Neighborhood.shrink X Y V W hW :=
  Neighborhood.homOfLE_ofRangeSubset X Y V (Neighborhood.imageOpen X Y V W)
    (Neighborhood.range_subschemeι_subset_imageOpen X Y V W hW)
    (Neighborhood.imageOpen_le X Y V W)

/-- The open underlying the smaller neighbourhood is the image of the open. -/
public theorem Neighborhood.open_shrink (V : Neighborhood X Y)
    (W : (Neighborhood.open X Y V).toScheme.Opens)
    (hW : (Stacks.Algebraization.nbhdTower Y.subschemeι (Neighborhood.open X Y V)
      (Neighborhood.range_subschemeι_subset X Y V)).support ⊆ W) :
    Neighborhood.open X Y (Neighborhood.shrink X Y V W hW) =
      Neighborhood.imageOpen X Y V W :=
  rfl

/-- **The identification of an open of a neighbourhood with the smaller neighbourhood it gives is
compatible with the inclusions into the neighbourhood.** Both composites with the inclusion of the
neighbourhood into `X` are the inclusion of the open, and that inclusion is a monomorphism. -/
public theorem Neighborhood.imageOpenIso_hom_homOfLE (V : Neighborhood X Y)
    (W : (Neighborhood.open X Y V).toScheme.Opens)
    (hW : (Stacks.Algebraization.nbhdTower Y.subschemeι (Neighborhood.open X Y V)
      (Neighborhood.range_subschemeι_subset X Y V)).support ⊆ W) :
    (Neighborhood.imageOpenIso X Y V W).hom ≫
        X.homOfLE (Neighborhood.shrinkHom X Y V W hW).le = W.ι := by
  refine (cancel_mono (Neighborhood.open X Y V).ι).1 ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun k => (Neighborhood.imageOpenIso X Y V W).hom ≫ k)
    (Scheme.homOfLE_ι X (Neighborhood.shrinkHom X Y V W hW).le)).trans ?_
  exact Neighborhood.imageOpenIso_hom_ι X Y V W

/-- **The chapter's chosen factorization is the completion side's induced immersion.** Both
compose with the inclusion of the neighbourhood to `Y.subschemeι`, and that inclusion is a
monomorphism, so no ambiguity is introduced by the two independent choices. -/
public theorem Neighborhood.toSchemeHom_eq_nbhdImmersion (V : Neighborhood X Y) :
    Neighborhood.toSchemeHom X Y V =
      Stacks.Algebraization.nbhdImmersion Y.subschemeι (Neighborhood.open X Y V)
        (Neighborhood.range_subschemeι_subset X Y V) :=
  (cancel_mono (Neighborhood.open X Y V).ι).1
    ((Neighborhood.toSchemeHom_fac X Y V).trans
      (Stacks.Algebraization.nbhdImmersion_ι Y.subschemeι (Neighborhood.open X Y V)
        (Neighborhood.range_subschemeι_subset X Y V)).symm)

/-- The support of the tower of infinitesimal neighbourhoods read over a neighbourhood is the
image of the chapter's chosen factorization. -/
public theorem nbhdTower_support_eq (V : Neighborhood X Y) :
    (Stacks.Algebraization.nbhdTower Y.subschemeι (Neighborhood.open X Y V)
        (Neighborhood.range_subschemeι_subset X Y V)).support =
      Set.range (Neighborhood.toSchemeHom X Y V).base :=
  congrArg (fun k : Y.subscheme ⟶ (Neighborhood.open X Y V).toScheme => Set.range k.base)
    (Neighborhood.toSchemeHom_eq_nbhdImmersion X Y V).symm

/-- **The factorization of the closed subscheme through an open of a neighbourhood.** -/
public def Neighborhood.toOpenHom (V : Neighborhood X Y)
    (W : (Neighborhood.open X Y V).toScheme.Opens)
    (hW : (Stacks.Algebraization.nbhdTower Y.subschemeι (Neighborhood.open X Y V)
      (Neighborhood.range_subschemeι_subset X Y V)).support ⊆ W) :
    Y.subscheme ⟶ W.toScheme :=
  Neighborhood.toSchemeHom X Y (Neighborhood.shrink X Y V W hW) ≫
    (Neighborhood.imageOpenIso X Y V W).inv

/-- **A section over an open of a neighbourhood is a section over the smaller neighbourhood it
gives.** The identification of the open with the smaller neighbourhood carries a section of a
scheme over the neighbourhood to a section over the smaller neighbourhood. -/
public theorem Neighborhood.shrink_sectionHom (V : Neighborhood X Y)
    (W : (Neighborhood.open X Y V).toScheme.Opens)
    (hW : (Stacks.Algebraization.nbhdTower Y.subschemeι (Neighborhood.open X Y V)
      (Neighborhood.range_subschemeι_subset X Y V)).support ⊆ W)
    {T : Scheme.{u}} (p : T ⟶ (Neighborhood.open X Y V).toScheme) (s : W.toScheme ⟶ T)
    (hs : s ≫ p = W.ι) :
    ((Neighborhood.imageOpenIso X Y V W).inv ≫ s) ≫ p =
      X.homOfLE (Neighborhood.shrinkHom X Y V W hW).le := by
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun k => (Neighborhood.imageOpenIso X Y V W).inv ≫ k) hs).trans ?_
  refine Eq.trans (congrArg (fun k => (Neighborhood.imageOpenIso X Y V W).inv ≫ k)
    (Neighborhood.imageOpenIso_hom_homOfLE X Y V W hW).symm) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ X.homOfLE (Neighborhood.shrinkHom X Y V W hW).le)
    (Neighborhood.imageOpenIso X Y V W).inv_hom_id).trans ?_
  exact Category.id_comp _

/-- **Restriction of a transported section to the closed subscheme.** Restricting the section
over the smaller neighbourhood to the closed subscheme is restricting the original section along
the factorization through the open. -/
public theorem Neighborhood.toSchemeHom_shrink_comp (V : Neighborhood X Y)
    (W : (Neighborhood.open X Y V).toScheme.Opens)
    (hW : (Stacks.Algebraization.nbhdTower Y.subschemeι (Neighborhood.open X Y V)
      (Neighborhood.range_subschemeι_subset X Y V)).support ⊆ W)
    {T : Scheme.{u}} (s : W.toScheme ⟶ T) :
    Neighborhood.toSchemeHom X Y (Neighborhood.shrink X Y V W hW) ≫
        ((Neighborhood.imageOpenIso X Y V W).inv ≫ s) =
      Neighborhood.toOpenHom X Y V W hW ≫ s :=
  (Category.assoc _ _ _).symm

/-- The factorization through an open of a neighbourhood does factor the closed immersion into
the neighbourhood. -/
public theorem Neighborhood.toOpenHom_ι (V : Neighborhood X Y)
    (W : (Neighborhood.open X Y V).toScheme.Opens)
    (hW : (Stacks.Algebraization.nbhdTower Y.subschemeι (Neighborhood.open X Y V)
      (Neighborhood.range_subschemeι_subset X Y V)).support ⊆ W) :
    Neighborhood.toOpenHom X Y V W hW ≫ W.ι = Neighborhood.toSchemeHom X Y V := by
  refine (cancel_mono (Neighborhood.open X Y V).ι).1 ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun k => Neighborhood.toOpenHom X Y V W hW ≫ k)
    (show W.ι ≫ (Neighborhood.open X Y V).ι =
        (Neighborhood.imageOpenIso X Y V W).hom ≫ (Neighborhood.imageOpen X Y V W).ι from
      (Neighborhood.imageOpenIso_hom_ι X Y V W).symm)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun k => k ≫ (Neighborhood.imageOpen X Y V W).ι)
    (show Neighborhood.toOpenHom X Y V W hW ≫ (Neighborhood.imageOpenIso X Y V W).hom =
        Neighborhood.toSchemeHom X Y (Neighborhood.shrink X Y V W hW) from
      (Category.assoc _ _ _).trans
        ((congrArg (fun k => Neighborhood.toSchemeHom X Y
            (Neighborhood.shrink X Y V W hW) ≫ k)
          (Neighborhood.imageOpenIso X Y V W).inv_hom_id).trans (Category.comp_id _)))) ?_
  exact (Neighborhood.toSchemeHom_fac X Y (Neighborhood.shrink X Y V W hW)).trans
    (Neighborhood.toSchemeHom_fac X Y V).symm

end Stacks.FundamentalGroup

end
