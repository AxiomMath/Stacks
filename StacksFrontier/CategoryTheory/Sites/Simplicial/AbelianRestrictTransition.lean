module

public import StacksFrontier.CategoryTheory.Sites.AbelianSheafification
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedSheaves
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TransitionAdjunctionAb

/-!
# Restriction across fibres of a simplicial site, on abelian sheaves

Let `S` be a simplicial-site situation and `φ : [m] ⟶ [n]` a simplex map.  Restricting an abelian
sheaf on the total site to the components of degrees `m` and `n` gives two abelian sheaves,
compared by a canonical transition map: on sections over an object `V` of degree `m` it is
restriction of the sheaf along the total-category arrow `(φ, 𝟙)` out of the degree-`n` object
lying over `V`.  This is the transition of Stacks 09WF with abelian coefficients.

Read as a map of abelian sheaves on the degree-`m` component it is the direct-image transition
`restrictTransitionAb`, landing in the direct image along `f_φ`.  Its mate under the adjunction
`CategoryTheory.SimplicialSiteSituation.transitionAdjunctionAb` is the inverse-image transition
`fiberTransitionAb`, a map out of
`CategoryTheory.SimplicialSiteSituation.transitionInverseImageAb`.

`transitionInverseImageAbIso` identifies that chosen inverse image with the inverse image of
abelian sheaves of Stacks 04JC, in both cases of Stacks 09WE.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.restrictTransitionAb`: the direct-image transition.
* `CategoryTheory.SimplicialSiteSituation.fiberTransitionAb`: the inverse-image transition.
* `CategoryTheory.SimplicialSiteSituation.transitionInverseImageAbIso`: the comparison of the
  chosen inverse image of abelian sheaves along a simplicial transition with the inverse image of
  Stacks 04JC.

## Main results

* `CategoryTheory.SimplicialSiteSituation.restrictTransitionAb_inl_arrow` and
  `.restrictTransitionAb_inr_arrow`: restriction along an arbitrary cross-fibre arrow of the total
  category factors through the transition, in each of the two cases.
* `CategoryTheory.SimplicialSiteSituation.fiberTransitionAb_adj`: the mate of the inverse-image
  transition is the direct-image transition.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Pseudofunctor Opposite

universe u

namespace CategoryTheory

namespace SimplicialSiteSituation

/-- The direct-image transition comparing the restrictions of a total-site abelian sheaf to the
components of degrees `m` and `n`.  In case (B) it is obtained from the family of total-category
arrows through the universal property of the right Kan extension. -/
noncomputable def restrictTransitionAb (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    S.abelianComponent m ⟶ S.abelianComponent n ⋙ S.transitionDirectImageAb φ := by
  rcases S with ⟨C | C⟩
  · exact
      { app := fun A => ⟨whiskerRight (NatTrans.op (continuousInclusionTransition C φ)) A.obj⟩
        naturality := fun A B f => (sheafToPresheaf _ _).map_injective <|
          NatTrans.ext (funext fun _ => (f.hom.naturality _).symm) }
  · exact
      { app := fun A => ⟨((C.underlying.map φ.op).toFunctor.op.ranAdjunction Ab.{u}).homEquiv
          _ _ (whiskerRight (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op))
            A.obj)⟩
        naturality := fun A B f => by
          apply (sheafToPresheaf _ _).map_injective
          change whiskerLeft (Grothendieck.ι C.underlying (op m)).op f.hom ≫
              _ = _ ≫ (C.underlying.map φ.op).toFunctor.op.ran.map
                (whiskerLeft (Grothendieck.ι C.underlying (op n)).op f.hom)
          apply Adjunction.homEquiv_naturality_left_square
          exact NatTrans.ext (funext fun _ => (f.hom.naturality _).symm) }

/-- The direct-image transition comparing the restrictions of a total-site abelian sheaf to the
components of degrees `m` and `n`.  In case (B) it is obtained from the family of total-category
arrows through the universal property of the right Kan extension. -/
noncomputable def restrictTransitionAb' (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    S.restrictAb m ⟶ S.restrictAb n ⋙ S.transitionDirectImageAb φ := by
  rcases S with ⟨C | C⟩
  · exact
      { app := fun A => ⟨whiskerRight (NatTrans.op (continuousInclusionTransition C φ)) A.obj⟩
        naturality := fun A B f => (sheafToPresheaf _ _).map_injective <|
          NatTrans.ext (funext fun _ => (f.hom.naturality _).symm) }
  · exact
      { app := fun A => ⟨((C.underlying.map φ.op).toFunctor.op.ranAdjunction Ab.{u}).homEquiv
          _ _ (whiskerRight (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op))
            A.obj)⟩
        naturality := fun A B f => by
          apply (sheafToPresheaf _ _).map_injective
          change whiskerLeft (Grothendieck.ι C.underlying (op m)).op f.hom ≫
              _ = _ ≫ (C.underlying.map φ.op).toFunctor.op.ran.map
                (whiskerLeft (Grothendieck.ι C.underlying (op n)).op f.hom)
          apply Adjunction.homEquiv_naturality_left_square
          exact NatTrans.ext (funext fun _ => (f.hom.naturality _).symm) }

/-- In case (A), the abelian transition on sections is restriction along `(φ, 𝟙)`. -/
@[simp] theorem restrictTransitionAb_inl_app (C : SimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (A : Sheaf (totalTopology ⟨Sum.inl C⟩) Ab.{u}) (V : C.underlying.obj m) :
    ((restrictTransitionAb ⟨Sum.inl C⟩ φ).app A).hom.app (op V) =
      A.obj.map ((continuousInclusionTransition C φ).app V).op := rfl

/-- In case (B), the Kan-extension mate of the abelian transition on sections is restriction
along `(φ, 𝟙)`. -/
@[simp] theorem restrictTransitionAb_inr_app (C : CocontinuousSimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (A : Sheaf (totalTopology ⟨Sum.inr C⟩) Ab.{u})
    (U : C.underlying.obj (op n)) :
    ((((C.underlying.map φ.op).toFunctor.op.ranAdjunction Ab.{u}).homEquiv _ _).symm
      ((restrictTransitionAb ⟨Sum.inr C⟩ φ).app A).hom).app (op U) =
      A.obj.map ((Grothendieck.ιNatTrans φ.op).app U).op := by
  exact congrArg (fun t => t.app (op U))
    ((((C.underlying.map φ.op).toFunctor.op.ranAdjunction Ab.{u}).homEquiv _ _).symm_apply_apply _)

/-- In case (B), the Kan-extension mate of the abelian transition on sections is restriction
along `(φ, 𝟙)`. -/
@[simp] theorem restrictTransitionAb_inr_app' (C : CocontinuousSimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (A : Sheaf (totalTopology ⟨Sum.inr C⟩) Ab.{u})
    (U : C.underlying.obj (op n)) :
    ((((C.underlying.map φ.op).toFunctor.op.ranAdjunction Ab.{u}).homEquiv _ _).symm
      ((restrictTransitionAb' ⟨Sum.inr C⟩ φ).app A).hom).app (op U) =
      A.obj.map ((Grothendieck.ιNatTrans φ.op).app U).op :=
  restrictTransitionAb_inr_app C φ A U

/-- In case (A), restriction of an abelian sheaf along an arbitrary cross-fibre arrow of the
total category is recovered from the transition. -/
theorem restrictTransitionAb_inl_arrow (C : SimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (A : Sheaf (totalTopology ⟨Sum.inl C⟩) Ab.{u}) {U : C.underlying.obj n}
    {V : C.underlying.obj m} (f : U ⟶ (C.underlying.map φ).toFunctor.obj V) :
    ((restrictTransitionAb ⟨Sum.inl C⟩ φ).app A).hom.app (op V) ≫
        A.obj.map ((CoGrothendieck.ι C.totalPseudofunctor (op n)).map f).op =
      A.obj.map (Quiver.Hom.op
        (⟨φ.op, f⟩ : (CoGrothendieck.ι C.totalPseudofunctor (op n)).obj U ⟶
          (CoGrothendieck.ι C.totalPseudofunctor (op m)).obj V)) :=
  (A.obj.map_comp ((continuousInclusionTransition C φ).app V).op
      ((CoGrothendieck.ι C.totalPseudofunctor (op n)).map f).op).symm.trans
    (congrArg (fun k => A.obj.map (Quiver.Hom.op k))
      (CoGrothendieck.ι_map_comp_ιNatTrans_app C.totalPseudofunctor φ.op f))

/-- In case (B), restriction of an abelian sheaf along an arbitrary cross-fibre arrow of the
total category is recovered from the Kan-extension mate. -/
theorem restrictTransitionAb_inr_arrow (C : CocontinuousSimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (A : Sheaf (totalTopology ⟨Sum.inr C⟩) Ab.{u})
    {U : C.underlying.obj (op n)} {V : C.underlying.obj (op m)}
    (f : (C.underlying.map φ.op).toFunctor.obj U ⟶ V) :
    A.obj.map ((Grothendieck.ι C.underlying (op m)).map f).op ≫
        ((((C.underlying.map φ.op).toFunctor.op.ranAdjunction Ab.{u}).homEquiv _ _).symm
          ((restrictTransitionAb ⟨Sum.inr C⟩ φ).app A).hom).app (op U) =
      A.obj.map (Quiver.Hom.op (⟨φ.op, f⟩ : (Grothendieck.ι C.underlying (op n)).obj U ⟶
        (Grothendieck.ι C.underlying (op m)).obj V)) := by
  rw [restrictTransitionAb_inr_app]
  exact (A.obj.map_comp ((Grothendieck.ι C.underlying (op m)).map f).op
        ((Grothendieck.ιNatTrans (F := C.underlying) φ.op).app U).op).symm.trans
      (congrArg (fun k => A.obj.map (Quiver.Hom.op k))
        (Grothendieck.ιNatTrans_app_comp_ι_map φ.op f))

/-- In case (A) the abelian transition has the transition of Tag 09WF as its underlying map of
sheaves of sets. -/
theorem restrictTransitionAb_inl_forget (C : SimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (A : Sheaf (totalTopology ⟨Sum.inl C⟩) Ab.{u}) :
    (sheafCompose ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
          (forget Ab.{u})).map ((restrictTransitionAb ⟨Sum.inl C⟩ φ).app A) =
      (restrictTransition ⟨Sum.inl C⟩ φ).app
        ((sheafCompose (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology
          (forget Ab.{u})).obj A) := rfl

/-- In case (A) the abelian transition has the transition of Tag 09WF as its underlying map of
sheaves of sets. -/
theorem restrictTransitionAb_inl_forget' (C : SimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (A : Sheaf (totalTopology ⟨Sum.inl C⟩) Ab.{u}) :
    (sheafCompose ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
          (forget Ab.{u})).map ((restrictTransitionAb' ⟨Sum.inl C⟩ φ).app A) =
      (restrictTransition ⟨Sum.inl C⟩ φ).app
        ((sheafCompose (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology
          (forget Ab.{u})).obj A) := rfl

/-- The inverse-image transition on the restrictions of a total-site abelian sheaf: the mate of
`restrictTransitionAb` under the adjunction of the simplicial transition. -/
noncomputable def fiberTransitionAb (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    S.abelianComponent m ⋙ S.transitionInverseImageAb φ ⟶ S.abelianComponent n where
  app A := ((S.transitionAdjunctionAb φ).homEquiv _ _).symm ((S.restrictTransitionAb φ).app A)
  naturality A B α := by
    simpa only [Functor.comp_map] using
      (S.transitionAdjunctionAb φ).homEquiv_naturality_right_square
        ((S.abelianComponent m).map α)
        ((S.restrictTransitionAb φ).app B)
        ((S.restrictTransitionAb φ).app A)
        ((S.abelianComponent n).map α)
        (by simpa only [Functor.comp_map] using (S.restrictTransitionAb φ).naturality α)

/-- The inverse-image transition on the restrictions of a total-site abelian sheaf: the mate of
`restrictTransitionAb'` under the adjunction of the simplicial transition. -/
noncomputable def fiberTransitionAb' (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    S.restrictAb m ⋙ S.transitionInverseImageAb φ ⟶ S.restrictAb n where
  app A := ((S.transitionAdjunctionAb φ).homEquiv _ _).symm ((S.restrictTransitionAb' φ).app A)
  naturality A B α := by
    simpa only [Functor.comp_map] using
      (S.transitionAdjunctionAb φ).homEquiv_naturality_right_square
        ((S.restrictAb m).map α)
        ((S.restrictTransitionAb' φ).app B)
        ((S.restrictTransitionAb' φ).app A)
        ((S.restrictAb n).map α)
        (by simpa only [Functor.comp_map] using (S.restrictTransitionAb' φ).naturality α)

/-- The mate of the inverse-image transition is the direct-image transition. -/
@[simp] theorem fiberTransitionAb_adj (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) (A : Sheaf S.totalTopology Ab.{u}) :
    ((S.transitionAdjunctionAb φ).homEquiv _ _) ((S.fiberTransitionAb φ).app A) =
      (S.restrictTransitionAb φ).app A :=
  ((S.transitionAdjunctionAb φ).homEquiv _ _).apply_symm_apply _

/-- The mate of the inverse-image transition is the direct-image transition. -/
@[simp] theorem fiberTransitionAb_adj' (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) (A : Sheaf S.totalTopology Ab.{u}) :
    ((S.transitionAdjunctionAb φ).homEquiv _ _) ((S.fiberTransitionAb' φ).app A) =
      (S.restrictTransitionAb' φ).app A :=
  fiberTransitionAb_adj S φ A

end SimplicialSiteSituation

namespace SimplicialSite

open CategoryTheory.SimplicialSiteSituation in
/-- In case (A), the chosen inverse image of abelian sheaves along a simplicial transition is the
inverse image of Stacks 04JC. -/
noncomputable def transitionInverseImageAbIso (C : SimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    transitionInverseImageAb (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ ≅
      abelianTransition (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ := by
  haveI : ((C.underlying.map φ).toFunctor).IsContinuous
      (C.coverage m).toGrothendieck (C.coverage n).toGrothendieck :=
    (C.isMorphismOfSites φ).isContinuous
  exact (Functor.sheafPullbackConstruction.sheafPullbackIso
      ((C.underlying.map φ).toFunctor) Ab.{u}
      (C.coverage m).toGrothendieck (C.coverage n).toGrothendieck).symm ≪≫
    Stacks.Sites.AbelianPullback.sheafPullbackAbIsoAbelianInverseImage (C.isMorphismOfSites φ)

end SimplicialSite

namespace CocontinuousSimplicialSite

open CategoryTheory.SimplicialSiteSituation Stacks.Sites.AbelianPullback in
/-- In case (B), the chosen inverse image of abelian sheaves along a simplicial transition is the
inverse image of Stacks 04JC. -/
noncomputable def transitionInverseImageAbIso (C : CocontinuousSimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    transitionInverseImageAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ ≅
      abelianTransition (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ :=
  (cocontinuousAbelianInverseImageIso ((C.underlying.map φ.op).toFunctor)
    (topologyOfCoverings (C.coverage (op n)))
    (topologyOfCoverings (C.coverage (op m)))).symm

end CocontinuousSimplicialSite

namespace SimplicialSiteSituation

/-- The chosen inverse image of abelian sheaves along a simplicial transition is the inverse image
of abelian sheaves of Stacks 04JC. -/
noncomputable def transitionInverseImageAbIso (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    S.transitionInverseImageAb φ ≅ abelianTransition S φ := by
  obtain ⟨c⟩ := S
  cases c with
  | inl C => exact SimplicialSite.transitionInverseImageAbIso C φ
  | inr C => exact CocontinuousSimplicialSite.transitionInverseImageAbIso C φ

end SimplicialSiteSituation

end CategoryTheory

add_to_stacks 09WF "cross-fibre restriction in case (A), abelian coefficients"
  CategoryTheory.SimplicialSiteSituation.restrictTransitionAb_inl_arrow
add_to_stacks 09WF "cross-fibre restriction in case (B), abelian coefficients"
  CategoryTheory.SimplicialSiteSituation.restrictTransitionAb_inr_arrow

end
