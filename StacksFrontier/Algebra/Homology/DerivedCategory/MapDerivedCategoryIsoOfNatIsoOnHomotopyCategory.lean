module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionQhComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons

/-!
# The comparison of the degreewise actions of isomorphic exact functors, on homotopy categories

For isomorphic exact functors `F ≅ G` of abelian categories with derived categories,
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso` identifies their degreewise
actions on unbounded derived categories. It is constructed as a lift along the localization
`DerivedCategory.Q` of the category of *complexes*, so nothing computes it on the image of the
localization `DerivedCategory.Qh` of the *homotopy* category, which is where the units of right
derived descents live. This file computes it on the image of `DerivedCategory.Qh`.

## Main results

* `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q`, of
  `StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons`, is the value of
  the comparison at the image of a cochain complex; it is the input here, not a result of this
  file.
* `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Qh`: **the comparison
  read on the image of `DerivedCategory.Qh`**, against
  `CategoryTheory.Functor.mapDerivedCategoryFactorsh`.
* `Stacks.DerivedCategoryComparisons.mapDerivedCategoryFactorsh_inv_app_comp_isoOfNatIso`: the
  same read against the *inverses* of those factorizations, which is the side a right derived
  descent presents.

## Implementation notes

The `Q`-to-`Qh` telescoping is the one that
`Stacks.DerivedFunctor.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso` performs, and
it is used here verbatim: the two localizations are compared by
`DerivedCategory.quotientCompQhIso`, whose components are not identities, and that lemma says
that composing a factorization over `DerivedCategory.Qh` with it leaves only the factorization
over `DerivedCategory.Q`. Both sides of the statement over `DerivedCategory.Qh` are therefore
composed with a component of `DerivedCategory.quotientCompQhIso`, which is invertible, and
cancelled.

Every object of the homotopy category of cochain complexes is definitionally the quotient of the
complex representing it, so the statement at an arbitrary object `J` is the statement at
`(HomotopyCategory.quotient _ _).obj J.as`.

One object of a derived category has several definitionally equal but syntactically distinct
spellings — `(F.mapHomotopyCategory c).obj ((HomotopyCategory.quotient _ c).obj K)` against
`(HomotopyCategory.quotient _ c).obj ((F.mapHomologicalComplex c).obj K)`, for instance — and a
composite whose consecutive factors use different ones is well typed and yet invisible to the
keyed matching of `rw` and `simp`. The algebra below is therefore written in term mode, by
`Eq.trans`, `congrArg` and the associativity of composition, all of which are checked up to
definitional equality.

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace Stacks.DerivedCategoryComparisons

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F G : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)

/-- The comparison at the image of a cochain complex, with the factorization of the action of `G`
cancelled: the form in which it is conjugated by `DerivedCategory.quotientCompQhIso`. -/
private theorem mapDerivedCategoryIsoOfNatIso_hom_app_Q_comp (K : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryIsoOfNatIso F G e).hom.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K) :=
  (congrArg (fun t => t ≫ G.mapDerivedCategoryFactors.hom.app K)
      (mapDerivedCategoryIsoOfNatIso_hom_app_Q F G e K)).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun t => F.mapDerivedCategoryFactors.hom.app K ≫ t)
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t => DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K) ≫ t)
              (Iso.inv_hom_id_app G.mapDerivedCategoryFactors K)).trans
            (Category.comp_id _)))))

/-- The two sides of `mapDerivedCategoryIsoOfNatIso_hom_app_Qh_quotient_obj`, before the
comparison of the two localizations is cancelled, are the same composite. Both reduce, through
`Stacks.DerivedFunctor.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso` and naturality,
to the factorization of the action of `F` over `DerivedCategory.Q` followed by the localization
of the degreewise action of `e`. -/
private theorem mapDerivedCategoryIsoOfNatIso_hom_app_Qh_cancel (K : CochainComplex C₁ ℤ) :
    ((mapDerivedCategoryIsoOfNatIso F G e).hom.app
            (DerivedCategory.Qh.obj
              ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K)) ≫
          G.mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K)) ≫
        (DerivedCategory.quotientCompQhIso C₂).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (F.mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map
            ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app
              ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K))) ≫
        (DerivedCategory.quotientCompQhIso C₂).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  have hnat := (mapDerivedCategoryIsoOfNatIso F G e).hom.naturality
    ((DerivedCategory.quotientCompQhIso C₁).hom.app K)
  have hleft : ((mapDerivedCategoryIsoOfNatIso F G e).hom.app
          (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K)) ≫
        G.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K)) ≫
          (DerivedCategory.quotientCompQhIso C₂).hom.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₁).hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun t => (mapDerivedCategoryIsoOfNatIso F G e).hom.app
              (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K)) ≫ t)
            (Stacks.DerivedFunctor.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso
              G K)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ G.mapDerivedCategoryFactors.hom.app K) hnat.symm).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun t => F.mapDerivedCategory.map
                  ((DerivedCategory.quotientCompQhIso C₁).hom.app K) ≫ t)
                (mapDerivedCategoryIsoOfNatIso_hom_app_Q_comp F G e K))))))
  have hqh : DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app
          ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K)) ≫
          (DerivedCategory.quotientCompQhIso C₂).hom.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (DerivedCategory.quotientCompQhIso C₂).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K) :=
    (DerivedCategory.quotientCompQhIso C₂).hom.naturality
      ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K)
  have hright : (F.mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map
            ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app
              ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K))) ≫
          (DerivedCategory.quotientCompQhIso C₂).hom.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₁).hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun t => F.mapDerivedCategoryFactorsh.hom.app
              ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) ≫ t) hqh).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K))
              (Stacks.DerivedFunctor.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso
                F K)).trans
            (Category.assoc _ _ _))))
  exact hleft.trans hright.symm

/-- The comparison at the image under `DerivedCategory.Qh` of the quotient of a cochain complex:
`mapDerivedCategoryIsoOfNatIso_hom_app_Q_comp` conjugated by
`DerivedCategory.quotientCompQhIso` and cancelled. -/
private theorem mapDerivedCategoryIsoOfNatIso_hom_app_Qh_quotient_obj
    (K : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryIsoOfNatIso F G e).hom.app
          (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K)) ≫
        G.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) =
      F.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app
            ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K)) :=
  have : IsIso ((DerivedCategory.quotientCompQhIso C₂).hom.app
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    (Iso.app (DerivedCategory.quotientCompQhIso C₂) _).isIso_hom
  (cancel_mono ((DerivedCategory.quotientCompQhIso C₂).hom.app
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))).1
      (mapDerivedCategoryIsoOfNatIso_hom_app_Qh_cancel F G e K)

/-- **The comparison of the degreewise actions of two isomorphic exact functors, on the image of
the localization of the homotopy category.** At an object `J` of the unbounded homotopy category,
the comparison composed with the factorization of the action of `G` through the homotopy category
is the factorization of the action of `F` followed by the localization of the degreewise action
of `e` on homotopy categories.

This is the form in which the comparison meets a right derived descent, whose defining
factorization — `Stacks.DerivedFunctor.exactDerivedDesc_fac_app`, for instance — is stated at an
object `DerivedCategory.Qh.obj J` and through
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`. -/
public theorem mapDerivedCategoryIsoOfNatIso_hom_app_Qh
    (J : HomotopyCategory C₁ (ComplexShape.up ℤ)) :
    (mapDerivedCategoryIsoOfNatIso F G e).hom.app (DerivedCategory.Qh.obj J) ≫
        G.mapDerivedCategoryFactorsh.hom.app J =
      F.mapDerivedCategoryFactorsh.hom.app J ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app J) :=
  mapDerivedCategoryIsoOfNatIso_hom_app_Qh_quotient_obj F G e J.as

/-- **The comparison of the degreewise actions of two isomorphic exact functors, read against the
inverses of the factorizations through the homotopy category.** The form the descent units of
Stacks 0GIX meet: the inverse factorization for `F` followed by the comparison is the
localization of the degreewise action of `e` followed by the inverse factorization for `G`. -/
public theorem mapDerivedCategoryFactorsh_inv_app_comp_isoOfNatIso
    (J : HomotopyCategory C₁ (ComplexShape.up ℤ)) :
    F.mapDerivedCategoryFactorsh.inv.app J ≫
        (mapDerivedCategoryIsoOfNatIso F G e).hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app J) ≫
        G.mapDerivedCategoryFactorsh.inv.app J :=
  (Iso.inv_comp_eq (F.mapDerivedCategoryFactorsh.app J)).2
    (((Iso.eq_comp_inv (G.mapDerivedCategoryFactorsh.app J)).2
      (mapDerivedCategoryIsoOfNatIso_hom_app_Qh F G e J)).trans (Category.assoc _ _ _))

end Stacks.DerivedCategoryComparisons

end
