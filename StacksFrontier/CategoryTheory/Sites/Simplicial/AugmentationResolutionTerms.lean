module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumFormulaLeg
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentLowerShriekAdjunction
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.Sigma.LocallyZero
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianTransitionBridge
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianTransitionBridgeCocontinuous
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationComponentInverseImageAb
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedRealization

/-!
# Degreewise comparison of the simplex-coefficient resolution with the lower shriek images

Let `S` be a simplicial-site situation and `F` an abelian sheaf on its total site. The degree-`n`
term of the simplex-coefficient resolution of `F` is the sheafification of the presheaf sending an
object of the total category to the direct sum of the sections of `F` over that object indexed by
the simplex maps out of `⦋n⦌`; the terms of the resolution of Stacks 0D78 are instead the lower
shriek images `g_{n!}(F_n)`. This file collects the comparison data between the two.

Over an object of degree `n` the summands of the degree-`n` term are indexed by the simplex maps
`⦋n⦌ ⟶ ⦋n⦌`, so the identity map labels a distinguished summand and
`componentPresheafInclusion` includes `F` into the resolution over that component.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentPresheafInclusion`: over the component of
  simplicial degree `n`, the inclusion of `F` as the summand of the degree-`n` term of the
  simplex-coefficient presheaf labelled by the identity simplex map.
* `CategoryTheory.SimplicialSiteSituation.componentSheafInclusion`: the same inclusion read on
  abelian sheaves over that component, after sheafification.
* `CategoryTheory.SimplicialSiteSituation.componentLowerShriekMap`: the canonical map
  `g_{n!}(F_n) ⟶` the degree-`n` term, the transpose of that inclusion under `g_{n!} ⊣ g_n^{-1}`.
  For a cartesian `F` this is the comparison that Stacks 09WG makes an isomorphism.
* `CategoryTheory.SimplicialSiteSituation.copowerRestrict` and `.copowerRestrictIso`: the copower
  of a functor by the simplex maps `⦋n⦌ ⟶ ⦋m⦌`, and its identification with the coproduct of
  copies of that functor.
* `CategoryTheory.SimplicialSiteSituation.restrictSimplexCoefficientIsoCoproduct`: restricted to
  the component of degree `m`, the degree-`n` term of the simplex-coefficient presheaf is the
  coproduct over the simplex maps `⦋n⦌ ⟶ ⦋m⦌` of the restriction of `F`.
* `CategoryTheory.SimplicialSiteSituation.abelianComponentBarIsoCoproduct`: the same
  decomposition for the degree-`n` term of the resolution itself, after sheafification.
* `CategoryTheory.SimplicialSiteSituation.componentPresheafSummand` and `.componentSheafSummand`:
  over the component of degree `m`, the summand of the degree-`n` term labelled by a simplex map
  `φ : ⦋n⦌ ⟶ ⦋m⦌`, before and after sheafification.
* `CategoryTheory.SimplicialSiteSituation.sigma_ι_comp_abelianComponentBarIsoCoproduct_inv`: the
  `φ`-labelled leg of that decomposition is the `φ`-labelled summand.
* `CategoryTheory.SimplicialSiteSituation`
  `.transitionInverseImageAb_map_componentSheafInclusion_comp_fiberTransitionAb`: the
  identity-labelled summand inclusion, transported along a simplex map `φ`, is the `φ`-labelled
  leg of the degree-`m` decomposition.
* `CategoryTheory.SimplicialSiteSituation.componentSheafInclusion_comp_restrictTransitionAb`: the
  same statement for the direct-image transition; the two are exchanged by
  `fiberTransitionAb_square`.
* `CategoryTheory.SimplicialSiteSituation.presheafInclusion_comp_map`: the identity-labelled
  summand over the component of degree `n`, restricted along an arrow of the total category whose
  degree map is `φ`, is the `φ`-labelled summand over the component of degree `m`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.isIso_of_forall_isIso_abelianComponent_map`: a morphism
  of abelian sheaves on the total site whose restriction to every simplicial degree is an
  isomorphism is an isomorphism.
* `CategoryTheory.SimplicialSiteSituation.degreeFunctor_obj_componentFunctor_obj` and
  `.degreeFunctor_leftOp_obj_op_componentFunctor_obj`: an object of the component of simplicial
  degree `n` has simplicial degree `n`.
* `CategoryTheory.SimplicialSiteSituation.isIso_abelianTransitionOfFiber_app_of_isCartesianAbSheaf`
  and `.isIso_fiberTransitionAb_app_of_isCartesianAbSheaf`: for a cartesian abelian sheaf the
  abelian inverse-image transitions are invertible, in two spellings, the second being the one
  the summands of the formula of Stacks 09WG are stated in.

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

section Copowers

/-- The copower of a functor by the simplex maps `⦋n⦌ ⟶ ⦋m⦌`, written so that its structure map
is the copower map of the reindexing by precomposition with the identity of `⦋m⦌`: that is what
the degree-`n` term of the simplex-coefficient diagram restricts to over the component of
degree `m`. -/
def copowerRestrict {D : Type u} [Category.{u} D] (n m : SimplexCategory) (K : D ⥤ Ab.{u}) :
    D ⥤ Ab.{u} where
  obj Y := ∐ fun _ : n ⟶ m => K.obj Y
  map f := copowerMap (fun φ => φ ≫ 𝟙 m) (K.map f)
  map_id Y := by
    apply Sigma.hom_ext
    intro φ
    simp [ι_copowerMap]
  map_comp f g := by
    apply Sigma.hom_ext
    intro φ
    simp [ι_copowerMap, ι_copowerMap_assoc]

/-- The copower of a functor by a type is the coproduct of copies of that functor. -/
def copowerRestrictIso {D : Type u} [Category.{u} D] (n m : SimplexCategory) (K : D ⥤ Ab.{u}) :
    copowerRestrict n m K ≅ ∐ fun _ : n ⟶ m => K :=
  NatIso.ofComponents (fun Y => (sigmaObjIso (fun _ : n ⟶ m => K) Y).symm) (by
    intro Y Z f
    apply Sigma.hom_ext
    intro φ
    simp [copowerRestrict, ι_copowerMap_assoc])

end Copowers


variable (S : SimplicialSiteSituation.{u})

/-- A morphism of abelian sheaves on the total site whose restriction to every simplicial degree
is an isomorphism is an isomorphism. -/
theorem isIso_of_forall_isIso_abelianComponent_map {F G : Sheaf S.totalTopology Ab.{u}}
    (f : F ⟶ G) (h : ∀ n : SimplexCategory, IsIso ((S.abelianComponent n).map f)) :
    IsIso f := by
  have happ : ∀ X : S.totalCategoryᵒᵖ,
      IsIso (((sheafToPresheaf S.totalTopology Ab.{u}).map f).app X) := by
    intro X
    obtain ⟨Xu⟩ := X
    obtain ⟨n, Y, hY⟩ := CategoryTheory.SimplicialSiteSituation.exists_componentFunctor_obj S Xu
    subst hY
    have := h n
    exact inferInstanceAs
      (IsIso (((sheafToPresheaf (S.componentTopology n) Ab.{u}).map
        ((S.abelianComponent n).map f)).app (Opposite.op Y)))
  have : IsIso ((sheafToPresheaf S.totalTopology Ab.{u}).map f) :=
    NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso f (sheafToPresheaf S.totalTopology Ab.{u})

/-- An object of the component of simplicial degree `n` has simplicial degree `n`. -/
@[simp] theorem degreeFunctor_obj_componentFunctor_obj (n : SimplexCategory)
    (Y : S.component n) :
    (degreeFunctor S).obj ((S.componentFunctor n).obj Y) = Opposite.op n := by
  obtain ⟨c⟩ := S
  cases c with
  | inl C => rfl
  | inr C => rfl

/-- The simplicial degree of an object of the component of degree `n`, read through the functor
the simplex-coefficient diagram is built from. -/
@[simp] theorem degreeFunctor_leftOp_obj_op_componentFunctor_obj (n : SimplexCategory)
    (Y : S.component n) :
    ((degreeFunctor S).leftOp).obj (Opposite.op ((S.componentFunctor n).obj Y)) = n := by
  obtain ⟨c⟩ := S
  cases c with
  | inl C => rfl
  | inr C => rfl

/-- A morphism of abelian sheaves on the total site whose restriction to every simplicial degree
is an isomorphism is an isomorphism. -/
theorem isIso_of_forall_isIso_restrictAb_map {F G : Sheaf S.totalTopology Ab.{u}}
    (f : F ⟶ G) (h : ∀ n : SimplexCategory, IsIso ((S.restrictAb n).map f)) :
    IsIso f :=
  isIso_of_forall_isIso_abelianComponent_map S f h

/-- An object of the component of simplicial degree `n` has simplicial degree `n`. -/
@[simp] theorem totalSimplexDegree_obj_componentFunctor_obj (n : SimplexCategory)
    (Y : S.component n) :
    (totalSimplexDegree S).obj ((S.componentFunctor n).obj Y) = Opposite.op n := by
  obtain ⟨c⟩ := S
  cases c with
  | inl C => rfl
  | inr C => rfl

/-- The simplicial degree of an object of the component of degree `n`, read through the functor
the simplex-coefficient diagram is built from. -/
@[simp] theorem totalSimplexDegree_leftOp_obj_op_componentFunctor_obj (n : SimplexCategory)
    (Y : S.component n) :
    (totalSimplexDegree S).leftOp.obj (Opposite.op ((S.componentFunctor n).obj Y)) = n := by
  obtain ⟨c⟩ := S
  cases c with
  | inl C => rfl
  | inr C => rfl

variable (F : Sheaf S.totalTopology Ab.{u})

/-- Over an object of simplicial degree `n`, the summand of the degree-`n` term of the
simplex-coefficient presheaf labelled by the identity simplex map. -/
def componentPresheafInclusion (n : SimplexCategory) :
    (S.componentFunctor n).op ⋙ F.obj ⟶
      (S.componentFunctor n).op ⋙
        (simplexCoefficientDiagram ((degreeFunctor S).leftOp) F.obj).obj (Opposite.op n) where
  app Y :=
    Sigma.ι (fun _ : n ⟶ ((degreeFunctor S).leftOp).obj
        (Opposite.op ((S.componentFunctor n).obj Y.unop)) =>
      F.obj.obj (Opposite.op ((S.componentFunctor n).obj Y.unop)))
      (eqToHom (degreeFunctor_leftOp_obj_op_componentFunctor_obj S n Y.unop).symm)
  naturality Y Z f := by
    obtain ⟨c⟩ := S
    cases c with
    | inl C =>
      simp [simplexCoefficientDiagram, ι_copowerMap]
      congr 1
    | inr C =>
      simp [simplexCoefficientDiagram, ι_copowerMap]
      congr 1

/-- Over an object of simplicial degree `n`, the summand of the degree-`n` term of the
simplex-coefficient presheaf labelled by the identity simplex map. -/
def componentPresheafInclusion' (n : SimplexCategory) :
    (S.componentFunctor n).op ⋙ F.obj ⟶
      (S.componentFunctor n).op ⋙
        ((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj F.obj).obj
        (Opposite.op n) where
  app Y :=
    Sigma.ι (fun _ : n ⟶ (totalSimplexDegree S).leftOp.obj
        (Opposite.op ((S.componentFunctor n).obj Y.unop)) =>
      F.obj.obj (Opposite.op ((S.componentFunctor n).obj Y.unop)))
      (eqToHom (totalSimplexDegree_leftOp_obj_op_componentFunctor_obj S n Y.unop).symm)
  naturality Y Z f := by
    obtain ⟨c⟩ := S
    cases c with
    | inl C =>
      simp [simplexCoefficientDiagram', ι_copowerMap]
      congr 1
    | inr C =>
      simp [simplexCoefficientDiagram', ι_copowerMap]
      congr 1

/-- The degree-`n` term of the simplex-coefficient resolution is the sheafification of the
degree-`n` term of the simplex-coefficient presheaf. -/
theorem barSimplicial_obj_op (n : SimplexCategory) :
    (barSimplicial S F).obj (Opposite.op n) =
      (presheafToSheaf S.totalTopology Ab.{u}).obj
        ((simplexCoefficientDiagram ((degreeFunctor S).leftOp) F.obj).obj (Opposite.op n)) :=
  rfl

/-- The degree-`n` term of the simplex-coefficient resolution is the sheafification of the
degree-`n` term of the simplex-coefficient presheaf. -/
theorem barSimplicial_obj_op' (n : SimplexCategory) :
    ((barSimplicial' S).obj F).obj (Opposite.op n) =
      (presheafToSheaf S.totalTopology Ab.{u}).obj
        (((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj F.obj).obj
        (Opposite.op n)) :=
  rfl

/-- The identity-labelled summand inclusion is natural in `F`. -/
theorem componentPresheafInclusion_naturality (n : SimplexCategory)
    {F G : Sheaf S.totalTopology Ab.{u}} (α : F ⟶ G) :
    Functor.whiskerLeft (S.componentFunctor n).op α.hom ≫ componentPresheafInclusion' S G n =
      componentPresheafInclusion' S F n ≫
        Functor.whiskerLeft (S.componentFunctor n).op
          (((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).map α.hom).app
            (Opposite.op n)) :=
  NatTrans.ext <| funext fun _ => (ι_copowerMap id (α.hom.app _) _).symm

/-- Over the component of simplicial degree `n`, the inclusion of `F` into the degree-`n` term of
the simplex-coefficient resolution. -/
def componentSheafInclusion (n : SimplexCategory) :
    (S.abelianComponent n).obj F ⟶
      (S.abelianComponent n).obj ((barSimplicial S F).obj (Opposite.op n)) :=
  ObjectProperty.homMk
    (componentPresheafInclusion S F n ≫
      Functor.whiskerLeft (S.componentFunctor n).op
        (toSheafify S.totalTopology
          ((simplexCoefficientDiagram ((degreeFunctor S).leftOp) F.obj).obj (Opposite.op n))))

/-- Over the component of simplicial degree `n`, the inclusion of `F` into the degree-`n` term of
the simplex-coefficient resolution, natural in `F`. -/
def componentSheafInclusion' (n : SimplexCategory) :
    S.restrictAb n ⟶ barTerm S n ⋙ S.restrictAb n where
  app F := ObjectProperty.homMk
    (componentPresheafInclusion' S F n ≫
      Functor.whiskerLeft (S.componentFunctor n).op
        (toSheafify S.totalTopology
          (((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj F.obj).obj
            (Opposite.op n))))
  naturality F G α := by
    apply (sheafToPresheaf (S.componentTopology n) Ab.{u}).map_injective
    change Functor.whiskerLeft (S.componentFunctor n).op α.hom ≫
        (componentPresheafInclusion' S G n ≫ Functor.whiskerLeft (S.componentFunctor n).op
          (toSheafify S.totalTopology
            (((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj G.obj).obj
              (Opposite.op n)))) =
      (componentPresheafInclusion' S F n ≫ Functor.whiskerLeft (S.componentFunctor n).op
          (toSheafify S.totalTopology
            (((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj F.obj).obj
              (Opposite.op n)))) ≫
        Functor.whiskerLeft (S.componentFunctor n).op
          (sheafifyMap S.totalTopology
            (((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).map α.hom).app
              (Opposite.op n)))
    rw [← Category.assoc, componentPresheafInclusion_naturality, Category.assoc, Category.assoc,
      ← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp, toSheafify_naturality]

/-- The canonical map from the lower shriek image of the restriction of `F` to the degree-`n` term
of the simplex-coefficient resolution: the transpose of `componentSheafInclusion` under the
adjunction `g_{n!} ⊣ g_n^{-1}`. -/
def componentLowerShriekMap (n : SimplexCategory) :
    (Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
        (S.componentTopology n) S.totalTopology).obj ((S.abelianComponent n).obj F) ⟶
      (barSimplicial S F).obj (Opposite.op n) :=
  ((S.componentLowerShriekAbAdjunction n).homEquiv _ _).symm (componentSheafInclusion S F n)

/-- The canonical map from the lower shriek image of the restriction of `F` to the degree-`n` term
of the simplex-coefficient resolution, natural in `F`: the transpose of
`componentSheafInclusion'` under the adjunction `g_{n!} ⊣ g_n^{-1}`. -/
def componentLowerShriekMap' (n : SimplexCategory) :
    S.restrictAb n ⋙ componentLowerShriekAb S n ⟶ barTerm S n where
  app F := ((S.componentLowerShriekAbAdjunction' n).homEquiv _ _).symm
    ((componentSheafInclusion' S n).app F)
  naturality F G α := by
    rw [Functor.comp_map, ← Adjunction.homEquiv_naturality_left_symm,
      ← Adjunction.homEquiv_naturality_right_symm]
    exact congrArg _ ((componentSheafInclusion' S n).naturality α)

/-- For a cartesian abelian sheaf on the total site, the abelian transition of Stacks 07TF is
invertible. -/
theorem isIso_abelianTransitionOfFiber_app_of_isCartesianAbSheaf
    (hF : IsCartesianAbSheaf S F) {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso ((abelianTransitionOfFiber S φ).app F) := by
  have : IsIso ((sheafCompose (S.componentTopology n) (forget Ab.{u})).map
      ((abelianTransitionOfFiber S φ).app F)) := by
    rw [abelianTransitionOfFiber_forget]
    exact hF φ
  exact isIso_of_reflects_iso ((abelianTransitionOfFiber S φ).app F)
    (sheafCompose (S.componentTopology n) (forget Ab.{u}))

/-- For a cartesian abelian sheaf on the total site, the abelian transition of Stacks 07TF is
invertible. -/
theorem isIso_abelianTransitionOfFiber_app_of_isCartesianAbSheaf'
    (hF : IsCartesianAbSheaf S F) {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso ((abelianTransitionOfFiber' S φ).app F) := by
  obtain ⟨c⟩ := S
  cases c <;> exact isIso_abelianTransitionOfFiber_app_of_isCartesianAbSheaf _ F hF φ

/-- For a cartesian abelian sheaf on the total site, the inverse-image transition in the spelling
the sum formula of Stacks 09WG uses is invertible. -/
theorem isIso_fiberTransitionAb_app_of_isCartesianAbSheaf (hF : IsCartesianAbSheaf S F)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso ((S.fiberTransitionAb φ).app F) := by
  have := isIso_abelianTransitionOfFiber_app_of_isCartesianAbSheaf S F hF φ
  rw [congr_app (S.fiberTransitionAb_eq φ) F, NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

/-- For a cartesian abelian sheaf on the total site, the inverse-image transition in the spelling
the sum formula of Stacks 09WG uses is invertible. -/
theorem isIso_fiberTransitionAb_app_of_isCartesianAbSheaf' (hF : IsCartesianAbSheaf S F)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso ((S.fiberTransitionAb' φ).app F) := by
  obtain ⟨c⟩ := S
  cases c <;> exact isIso_fiberTransitionAb_app_of_isCartesianAbSheaf _ F hF φ

/-- Restricted to the component of simplicial degree `m`, the degree-`n` term of the
simplex-coefficient presheaf of `F` is the coproduct, indexed by the simplex maps `⦋n⦌ ⟶ ⦋m⦌`, of
the restriction of `F`. -/
def restrictSimplexCoefficientIsoCoproduct (n m : SimplexCategory) :
    (S.componentFunctor m).op ⋙
        (simplexCoefficientDiagram ((degreeFunctor S).leftOp) F.obj).obj (Opposite.op n) ≅
      ∐ fun _ : n ⟶ m => (S.componentFunctor m).op ⋙ F.obj := by
  obtain ⟨c⟩ := S
  cases c with
  | inl C => exact copowerRestrictIso n m ((componentFunctor ⟨Sum.inl C⟩ m).op ⋙ F.obj)
  | inr C => exact copowerRestrictIso n m ((componentFunctor ⟨Sum.inr C⟩ m).op ⋙ F.obj)

/-- Restricted to the component of simplicial degree `m`, the degree-`n` term of the
simplex-coefficient presheaf of `F` is the coproduct, indexed by the simplex maps `⦋n⦌ ⟶ ⦋m⦌`, of
the restriction of `F`. -/
def restrictSimplexCoefficientIsoCoproduct' (n m : SimplexCategory) :
    (S.componentFunctor m).op ⋙
        ((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj F.obj).obj
        (Opposite.op n) ≅
      ∐ fun _ : n ⟶ m => (S.componentFunctor m).op ⋙ F.obj := by
  obtain ⟨c⟩ := S
  cases c with
  | inl C => exact copowerRestrictIso n m ((componentFunctor ⟨Sum.inl C⟩ m).op ⋙ F.obj)
  | inr C => exact copowerRestrictIso n m ((componentFunctor ⟨Sum.inr C⟩ m).op ⋙ F.obj)

/-- Discrete colimits of abelian sheaves on a component, found through the size-indexed
instance. -/
local instance hasColimitsOfShapeDiscreteSheafComponent {I : Type}
    (m : SimplexCategory) :
    HasColimitsOfShape (Discrete I) (Sheaf (S.componentTopology m) Ab.{u}) :=
  haveI : HasColimitsOfSize.{0, 0} Ab.{u} := inferInstance
  haveI : HasColimitsOfSize.{0, 0} (Sheaf (S.componentTopology m) Ab.{u}) := inferInstance
  HasColimitsOfSize.has_colimits_of_shape _

/-- Restricted to the component of simplicial degree `m`, the degree-`n` term of the
simplex-coefficient resolution of `F` is the coproduct, indexed by the simplex maps `⦋n⦌ ⟶ ⦋m⦌`,
of the restriction of `F`. -/
def abelianComponentBarIsoCoproduct (n m : SimplexCategory) :
    (S.abelianComponent m).obj ((barSimplicial S F).obj (Opposite.op n)) ≅
      ∐ fun _ : n ⟶ m => (S.abelianComponent m).obj F :=
  (((S.componentFunctor m).pushforwardContinuousSheafificationCompatibility
        Ab.{u} (S.componentTopology m) S.totalTopology).app
      ((simplexCoefficientDiagram ((degreeFunctor S).leftOp) F.obj).obj (Opposite.op n))).symm ≪≫
    (presheafToSheaf (S.componentTopology m) Ab.{u}).mapIso
      (restrictSimplexCoefficientIsoCoproduct S F n m) ≪≫
    PreservesCoproduct.iso _ _ ≪≫
    Sigma.mapIso fun _ => (sheafificationIso ((S.abelianComponent m).obj F)).symm

/-- Restricted to the component of simplicial degree `m`, the degree-`n` term of the
simplex-coefficient resolution of `F` is the coproduct, indexed by the simplex maps `⦋n⦌ ⟶ ⦋m⦌`,
of the restriction of `F`. -/
def abelianComponentBarIsoCoproduct' (n m : SimplexCategory) :
    (S.restrictAb m).obj (((barSimplicial' S).obj F).obj (Opposite.op n)) ≅
      ∐ fun _ : n ⟶ m => (S.restrictAb m).obj F :=
  (((S.componentFunctor m).pushforwardContinuousSheafificationCompatibility
        Ab.{u} (S.componentTopology m) S.totalTopology).app
      (((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj F.obj).obj
        (Opposite.op n))).symm ≪≫
    (presheafToSheaf (S.componentTopology m) Ab.{u}).mapIso
      (restrictSimplexCoefficientIsoCoproduct' S F n m) ≪≫
    PreservesCoproduct.iso _ _ ≪≫
    Sigma.mapIso fun _ => (sheafificationIso ((S.restrictAb m).obj F)).symm

/-- Over the component of degree `m`, the `φ`-labelled summand of the degree-`n` term of the
simplex-coefficient presheaf. -/
def componentPresheafSummand {n m : SimplexCategory} (φ : n ⟶ m) :
    (S.componentFunctor m).op ⋙ F.obj ⟶
      (S.componentFunctor m).op ⋙
        (simplexCoefficientDiagram ((degreeFunctor S).leftOp) F.obj).obj (Opposite.op n) :=
  Sigma.ι (fun _ : n ⟶ m => (S.componentFunctor m).op ⋙ F.obj) φ ≫
    (restrictSimplexCoefficientIsoCoproduct S F n m).inv

/-- Over the component of degree `m`, the `φ`-labelled summand of the degree-`n` term of the
simplex-coefficient presheaf. -/
def componentPresheafSummand' {n m : SimplexCategory} (φ : n ⟶ m) :
    (S.componentFunctor m).op ⋙ F.obj ⟶
      (S.componentFunctor m).op ⋙
        ((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj F.obj).obj
        (Opposite.op n) :=
  Sigma.ι (fun _ : n ⟶ m => (S.componentFunctor m).op ⋙ F.obj) φ ≫
    (restrictSimplexCoefficientIsoCoproduct' S F n m).inv

/-- The `φ`-labelled summand is the `φ`-th coproduct inclusion read through the degree-`m`
decomposition. -/
theorem componentPresheafSummand_eq {n m : SimplexCategory} (φ : n ⟶ m) :
    componentPresheafSummand S F φ =
      Sigma.ι (fun _ : n ⟶ m => (S.componentFunctor m).op ⋙ F.obj) φ ≫
        (restrictSimplexCoefficientIsoCoproduct S F n m).inv :=
  rfl

/-- The `φ`-labelled summand is the `φ`-th coproduct inclusion read through the degree-`m`
decomposition. -/
theorem componentPresheafSummand_eq' {n m : SimplexCategory} (φ : n ⟶ m) :
    componentPresheafSummand' S F φ =
      Sigma.ι (fun _ : n ⟶ m => (S.componentFunctor m).op ⋙ F.obj) φ ≫
        (restrictSimplexCoefficientIsoCoproduct' S F n m).inv :=
  rfl

/-- The restriction of `F` to the component of degree `m` is the sheafification of its own
underlying presheaf, written with that presheaf spelled as a restriction of `F`. -/
def abelianComponentSheafificationIso (m : SimplexCategory) :
    (S.abelianComponent m).obj F ≅
      (presheafToSheaf (S.componentTopology m) Ab.{u}).obj ((S.componentFunctor m).op ⋙ F.obj) :=
  sheafificationIso ((S.abelianComponent m).obj F)

/-- The restriction of `F` to the component of degree `m` is the sheafification of its own
underlying presheaf, written with that presheaf spelled as a restriction of `F`. -/
def abelianComponentSheafificationIso' (m : SimplexCategory) :
    (S.restrictAb m).obj F ≅
      (presheafToSheaf (S.componentTopology m) Ab.{u}).obj ((S.componentFunctor m).op ⋙ F.obj) :=
  sheafificationIso ((S.restrictAb m).obj F)

/-- Over the component of degree `m`, the `φ`-labelled summand of the degree-`n` term of the
simplex-coefficient resolution. -/
def componentSheafSummand {n m : SimplexCategory} (φ : n ⟶ m) :
    (S.abelianComponent m).obj F ⟶
      (S.abelianComponent m).obj ((barSimplicial S F).obj (Opposite.op n)) :=
  ObjectProperty.homMk
    (componentPresheafSummand S F φ ≫
      Functor.whiskerLeft (S.componentFunctor m).op
        (toSheafify S.totalTopology
          ((simplexCoefficientDiagram ((degreeFunctor S).leftOp) F.obj).obj (Opposite.op n))))

/-- Over the component of degree `m`, the `φ`-labelled summand of the degree-`n` term of the
simplex-coefficient resolution. -/
def componentSheafSummand' {n m : SimplexCategory} (φ : n ⟶ m) :
    (S.restrictAb m).obj F ⟶
      (S.restrictAb m).obj (((barSimplicial' S).obj F).obj (Opposite.op n)) :=
  ObjectProperty.homMk
    (componentPresheafSummand' S F φ ≫
      Functor.whiskerLeft (S.componentFunctor m).op
        (toSheafify S.totalTopology
          (((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj F.obj).obj
        (Opposite.op n))))

/-- Restricting the degree-`n` term of the resolution to the component of degree `m` is the
sheafification of the restricted simplex-coefficient presheaf: the compatibility of pushforward
with sheafification, written with its target spelled as a restriction of the resolution. -/
def abelianComponentBarSheafificationIso (n m : SimplexCategory) :
    (presheafToSheaf (S.componentTopology m) Ab.{u}).obj
        ((S.componentFunctor m).op ⋙
          (simplexCoefficientDiagram ((degreeFunctor S).leftOp) F.obj).obj (Opposite.op n)) ≅
      (S.abelianComponent m).obj ((barSimplicial S F).obj (Opposite.op n)) :=
  ((S.componentFunctor m).pushforwardContinuousSheafificationCompatibility
      Ab.{u} (S.componentTopology m) S.totalTopology).app
    ((simplexCoefficientDiagram ((degreeFunctor S).leftOp) F.obj).obj (Opposite.op n))

/-- Restricting the degree-`n` term of the resolution to the component of degree `m` is the
sheafification of the restricted simplex-coefficient presheaf: the compatibility of pushforward
with sheafification, written with its target spelled as a restriction of the resolution. -/
def abelianComponentBarSheafificationIso' (n m : SimplexCategory) :
    (presheafToSheaf (S.componentTopology m) Ab.{u}).obj
        ((S.componentFunctor m).op ⋙
          ((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj F.obj).obj
        (Opposite.op n)) ≅
      (S.restrictAb m).obj (((barSimplicial' S).obj F).obj (Opposite.op n)) :=
  ((S.componentFunctor m).pushforwardContinuousSheafificationCompatibility
      Ab.{u} (S.componentTopology m) S.totalTopology).app
    (((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj F.obj).obj
        (Opposite.op n))

/-- The sheafified `φ`-summand is the sheafification of the presheaf `φ`-summand, read through
the compatibility of pushforward with sheafification. -/
theorem map_componentPresheafSummand_comp_compatibility {n m : SimplexCategory} (φ : n ⟶ m) :
    (abelianComponentSheafificationIso S F m).hom ≫
        (presheafToSheaf (S.componentTopology m) Ab.{u}).map (componentPresheafSummand S F φ) ≫
          (abelianComponentBarSheafificationIso S F n m).hom =
      componentSheafSummand S F φ := by
  apply (sheafToPresheaf (S.componentTopology m) Ab.{u}).map_injective
  show toSheafify (S.componentTopology m) ((S.componentFunctor m).op ⋙ F.obj) ≫
      sheafifyMap (S.componentTopology m) (componentPresheafSummand S F φ) ≫
        (((S.componentFunctor m).pushforwardContinuousSheafificationCompatibility
            Ab.{u} (S.componentTopology m) S.totalTopology).hom.app
          ((simplexCoefficientDiagram ((degreeFunctor S).leftOp) F.obj).obj
            (Opposite.op n))).hom = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    Functor.toSheafify_pullbackSheafificationCompatibility]
  rfl

/-- The sheafified `φ`-summand is the sheafification of the presheaf `φ`-summand, read through
the compatibility of pushforward with sheafification. -/
theorem map_componentPresheafSummand_comp_compatibility' {n m : SimplexCategory} (φ : n ⟶ m) :
    (abelianComponentSheafificationIso' S F m).hom ≫
        (presheafToSheaf (S.componentTopology m) Ab.{u}).map (componentPresheafSummand' S F φ) ≫
          (abelianComponentBarSheafificationIso' S F n m).hom =
      componentSheafSummand' S F φ := by
  obtain ⟨c⟩ := S
  cases c <;> exact map_componentPresheafSummand_comp_compatibility _ F φ

/-- The `φ`-labelled summand inclusion of the degree-`m` decomposition is the sheafified
`φ`-summand. -/
theorem sigma_ι_comp_abelianComponentBarIsoCoproduct_inv {n m : SimplexCategory} (φ : n ⟶ m) :
    Sigma.ι (fun _ : n ⟶ m => (S.abelianComponent m).obj F) φ ≫
        (abelianComponentBarIsoCoproduct S F n m).inv =
      componentSheafSummand S F φ := by
  have h : (abelianComponentBarIsoCoproduct S F n m).inv =
      (((Sigma.mapIso fun _ : n ⟶ m =>
              (abelianComponentSheafificationIso S F m).symm).inv ≫
            (PreservesCoproduct.iso (presheafToSheaf (S.componentTopology m) Ab.{u})
              (fun _ : n ⟶ m => (S.componentFunctor m).op ⋙ F.obj)).inv) ≫
          (presheafToSheaf (S.componentTopology m) Ab.{u}).map
            (restrictSimplexCoefficientIsoCoproduct S F n m).inv) ≫
        (abelianComponentBarSheafificationIso S F n m).hom :=
    rfl
  rw [h]
  simp only [Iso.symm_inv, Category.assoc, Sigma.ι_mapIso_inv_assoc,
    PreservesCoproduct.inv_hom, ι_comp_sigmaComparison_assoc, ← Functor.map_comp_assoc]
  rw [← componentPresheafSummand_eq, map_componentPresheafSummand_comp_compatibility]

/-- The `φ`-labelled summand inclusion of the degree-`m` decomposition is the sheafified
`φ`-summand. -/
theorem sigma_ι_comp_abelianComponentBarIsoCoproduct_inv' {n m : SimplexCategory} (φ : n ⟶ m) :
    Sigma.ι (fun _ : n ⟶ m => (S.restrictAb m).obj F) φ ≫
        (abelianComponentBarIsoCoproduct' S F n m).inv =
      componentSheafSummand' S F φ := by
  obtain ⟨c⟩ := S
  cases c <;> exact sigma_ι_comp_abelianComponentBarIsoCoproduct_inv _ F φ

/-- On sections over an object of the component of degree `m`, the `φ`-labelled summand is the
summand inclusion labelled by `φ`. -/
theorem componentPresheafSummand_app {n m : SimplexCategory} (φ : n ⟶ m) (U : S.component m) :
    (componentPresheafSummand S F φ).app (Opposite.op U) =
      Sigma.ι (fun _ : n ⟶ ((degreeFunctor S).leftOp).obj
          (Opposite.op ((S.componentFunctor m).obj U)) =>
        F.obj.obj (Opposite.op ((S.componentFunctor m).obj U)))
        (φ ≫ eqToHom (degreeFunctor_leftOp_obj_op_componentFunctor_obj S m U).symm) := by
  obtain ⟨c⟩ := S
  cases c <;>
  · change (Sigma.ι (fun _ : n ⟶ m => (componentFunctor _ m).op ⋙ F.obj) φ).app _ ≫
        (sigmaObjIso (fun _ : n ⟶ m => (componentFunctor _ m).op ⋙ F.obj) _).hom = _
    rw [ι_comp_sigmaObjIso_hom]
    congr 1
    exact (Category.comp_id φ).symm

/-- On sections over an object of the component of degree `m`, the `φ`-labelled summand is the
summand inclusion labelled by `φ`. -/
theorem componentPresheafSummand_app' {n m : SimplexCategory} (φ : n ⟶ m) (U : S.component m) :
    (componentPresheafSummand' S F φ).app (Opposite.op U) =
      Sigma.ι (fun _ : n ⟶ (totalSimplexDegree S).leftOp.obj
          (Opposite.op ((S.componentFunctor m).obj U)) =>
        F.obj.obj (Opposite.op ((S.componentFunctor m).obj U)))
        (φ ≫ eqToHom (totalSimplexDegree_leftOp_obj_op_componentFunctor_obj S m U).symm) := by
  obtain ⟨c⟩ := S
  cases c <;> exact componentPresheafSummand_app _ F φ U

/-- The core presheaf computation: the identity-labelled summand over degree `n`, restricted
along a total-category arrow of degree `φ`, is the `φ`-labelled summand over degree `m`. -/
theorem presheafInclusion_comp_map {n m : SimplexCategory} (φ : n ⟶ m)
    (V : S.component n) (U : S.component m)
    (w : (S.componentFunctor m).obj U ⟶ (S.componentFunctor n).obj V)
    (hw : eqToHom (degreeFunctor_leftOp_obj_op_componentFunctor_obj S n V).symm ≫
        ((degreeFunctor S).leftOp).map w.op =
      φ ≫ eqToHom (degreeFunctor_leftOp_obj_op_componentFunctor_obj S m U).symm) :
    (componentPresheafInclusion S F n).app (Opposite.op V) ≫
        ((simplexCoefficientDiagram ((degreeFunctor S).leftOp) F.obj).obj
          (Opposite.op n)).map w.op =
      F.obj.map w.op ≫ (componentPresheafSummand S F φ).app (Opposite.op U) := by
  rw [componentPresheafSummand_app]
  show Sigma.ι _ (eqToHom (degreeFunctor_leftOp_obj_op_componentFunctor_obj S n V).symm) ≫
      copowerMap (fun α => α ≫ ((degreeFunctor S).leftOp).map w.op) (F.obj.map w.op) = _
  rw [ι_copowerMap, hw]
  rfl

/-- The core presheaf computation: the identity-labelled summand over degree `n`, restricted
along a total-category arrow of degree `φ`, is the `φ`-labelled summand over degree `m`. -/
theorem presheafInclusion_comp_map' {n m : SimplexCategory} (φ : n ⟶ m)
    (V : S.component n) (U : S.component m)
    (w : (S.componentFunctor m).obj U ⟶ (S.componentFunctor n).obj V)
    (hw : eqToHom (totalSimplexDegree_leftOp_obj_op_componentFunctor_obj S n V).symm ≫
        (totalSimplexDegree S).leftOp.map w.op =
      φ ≫ eqToHom (totalSimplexDegree_leftOp_obj_op_componentFunctor_obj S m U).symm) :
    (componentPresheafInclusion' S F n).app (Opposite.op V) ≫
        (((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj F.obj).obj
          (Opposite.op n)).map w.op =
      F.obj.map w.op ≫ (componentPresheafSummand' S F φ).app (Opposite.op U) := by
  obtain ⟨c⟩ := S
  cases c <;> exact presheafInclusion_comp_map _ F φ V U w hw

/-- The sections of the identity-labelled inclusion. -/
theorem componentSheafInclusion_hom_app (n : SimplexCategory) (V : S.component n) :
    (componentSheafInclusion S F n).hom.app (Opposite.op V) =
      (componentPresheafInclusion S F n).app (Opposite.op V) ≫
        (toSheafify S.totalTopology
          ((simplexCoefficientDiagram ((degreeFunctor S).leftOp) F.obj).obj
            (Opposite.op n))).app (Opposite.op ((S.componentFunctor n).obj V)) :=
  rfl

/-- The sections of the identity-labelled inclusion. -/
theorem componentSheafInclusion_hom_app' (n : SimplexCategory) (V : S.component n) :
    ((componentSheafInclusion' S n).app F).hom.app (Opposite.op V) =
      (componentPresheafInclusion' S F n).app (Opposite.op V) ≫
        (toSheafify S.totalTopology
          (((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj F.obj).obj
            (Opposite.op n))).app (Opposite.op ((S.componentFunctor n).obj V)) :=
  rfl

/-- The sections of the `φ`-labelled summand. -/
theorem componentSheafSummand_hom_app {n m : SimplexCategory} (φ : n ⟶ m)
    (U : S.component m) :
    (componentSheafSummand S F φ).hom.app (Opposite.op U) =
      (componentPresheafSummand S F φ).app (Opposite.op U) ≫
        (toSheafify S.totalTopology
          ((simplexCoefficientDiagram ((degreeFunctor S).leftOp) F.obj).obj
            (Opposite.op n))).app (Opposite.op ((S.componentFunctor m).obj U)) :=
  rfl

/-- The sections of the `φ`-labelled summand. -/
theorem componentSheafSummand_hom_app' {n m : SimplexCategory} (φ : n ⟶ m)
    (U : S.component m) :
    (componentSheafSummand' S F φ).hom.app (Opposite.op U) =
      (componentPresheafSummand' S F φ).app (Opposite.op U) ≫
        (toSheafify S.totalTopology
          (((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj F.obj).obj
            (Opposite.op n))).app (Opposite.op ((S.componentFunctor m).obj U)) :=
  rfl

/-- In case (A) the direct image along a transition is restriction of sections. -/
theorem transitionDirectImageAb_inl_map_hom_app (C : SimplicialSite.{u})
    {n m : SimplexCategory} (φ : n ⟶ m)
    {A B : Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m) Ab.{u}}
    (k : A ⟶ B) (V : (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).component n) :
    (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionDirectImageAb φ).map k).hom.app
        (Opposite.op V) =
      k.hom.app (Opposite.op ((C.underlying.map φ).toFunctor.obj V)) :=
  rfl

/-- On sections, the identity-labelled summand over degree `n`, restricted along a total-category
arrow whose simplicial degree is `φ`, is the `φ`-labelled summand over degree `m`. -/
theorem componentSheafInclusion_app_comp_map {n m : SimplexCategory} (φ : n ⟶ m)
    (V : S.component n) (U : S.component m)
    (w : (S.componentFunctor m).obj U ⟶ (S.componentFunctor n).obj V)
    (hw : eqToHom (degreeFunctor_leftOp_obj_op_componentFunctor_obj S n V).symm ≫
        ((degreeFunctor S).leftOp).map w.op =
      φ ≫ eqToHom (degreeFunctor_leftOp_obj_op_componentFunctor_obj S m U).symm) :
    (componentSheafInclusion S F n).hom.app (Opposite.op V) ≫
        ((barSimplicial S F).obj (Opposite.op n)).obj.map w.op =
      F.obj.map w.op ≫ (componentSheafSummand S F φ).hom.app (Opposite.op U) := by
  have hnat := (toSheafify S.totalTopology
    ((simplexCoefficientDiagram ((degreeFunctor S).leftOp) F.obj).obj
      (Opposite.op n))).naturality w.op
  refine Eq.trans (congrArg (fun g => g ≫ _) (componentSheafInclusion_hom_app S F n V)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun g => _ ≫ g) hnat.symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun g => g ≫ _) (presheafInclusion_comp_map S F φ V U w hw)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (fun g => _ ≫ g) (componentSheafSummand_hom_app S F φ U).symm

/-- On sections, the identity-labelled summand over degree `n`, restricted along a total-category
arrow whose simplicial degree is `φ`, is the `φ`-labelled summand over degree `m`. -/
theorem componentSheafInclusion_app_comp_map' {n m : SimplexCategory} (φ : n ⟶ m)
    (V : S.component n) (U : S.component m)
    (w : (S.componentFunctor m).obj U ⟶ (S.componentFunctor n).obj V)
    (hw : eqToHom (totalSimplexDegree_leftOp_obj_op_componentFunctor_obj S n V).symm ≫
        (totalSimplexDegree S).leftOp.map w.op =
      φ ≫ eqToHom (totalSimplexDegree_leftOp_obj_op_componentFunctor_obj S m U).symm) :
    ((componentSheafInclusion' S n).app F).hom.app (Opposite.op V) ≫
        (((barSimplicial' S).obj F).obj (Opposite.op n)).obj.map w.op =
      F.obj.map w.op ≫ (componentSheafSummand' S F φ).hom.app (Opposite.op U) := by
  obtain ⟨c⟩ := S
  cases c <;> exact componentSheafInclusion_app_comp_map _ F φ V U w hw

/-- The identity-labelled summand over degree `n`, transported along the direct-image transition
at `φ`, is the `φ`-labelled summand over degree `m`. -/
theorem componentSheafInclusion_comp_restrictTransitionAb {n m : SimplexCategory} (φ : n ⟶ m) :
    componentSheafInclusion S F n ≫
        (S.restrictTransitionAb φ).app ((barSimplicial S F).obj (Opposite.op n)) =
      (S.restrictTransitionAb φ).app F ≫
        (S.transitionDirectImageAb φ).map (componentSheafSummand S F φ) := by
  obtain ⟨c⟩ := S
  cases c with
  | inl C =>
    apply (sheafToPresheaf _ _).map_injective
    apply NatTrans.ext
    funext Y
    obtain ⟨V⟩ := Y
    exact componentSheafInclusion_app_comp_map (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) F φ
      V ((C.underlying.map φ).toFunctor.obj V) ((continuousInclusionTransition C φ).app V) rfl
  | inr C =>
    apply Sheaf.hom_ext
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom]
    refine ((((C.underlying.map φ.op).toFunctor).op.ranAdjunction Ab.{u}).homEquiv
      _ _).symm.injective ?_
    refine Eq.trans (Adjunction.homEquiv_naturality_left_symm _ _ _) ?_
    refine Eq.trans ?_ (Adjunction.homEquiv_naturality_right_symm _ _ _).symm
    apply NatTrans.ext
    funext Y
    obtain ⟨U⟩ := Y
    rw [NatTrans.comp_app, NatTrans.comp_app, restrictTransitionAb_inr_app,
      restrictTransitionAb_inr_app]
    exact componentSheafInclusion_app_comp_map (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) F φ
      ((C.underlying.map φ.op).toFunctor.obj U) U
      ((Grothendieck.ιNatTrans (F := C.underlying) φ.op).app U) rfl

/-- The identity-labelled summand over degree `n`, transported along the direct-image transition
at `φ`, is the `φ`-labelled summand over degree `m`. -/
theorem componentSheafInclusion_comp_restrictTransitionAb' {n m : SimplexCategory} (φ : n ⟶ m) :
    (componentSheafInclusion' S n).app F ≫
        (S.restrictTransitionAb' φ).app (((barSimplicial' S).obj F).obj (Opposite.op n)) =
      (S.restrictTransitionAb' φ).app F ≫
        (S.transitionDirectImageAb φ).map (componentSheafSummand' S F φ) := by
  obtain ⟨c⟩ := S
  cases c <;> exact componentSheafInclusion_comp_restrictTransitionAb _ F φ

/-- Transposition: a square for the direct-image transition gives the corresponding square for
its mate, the inverse-image transition. -/
theorem fiberTransitionAb_square {n m : SimplexCategory} (φ : n ⟶ m)
    {G H : Sheaf S.totalTopology Ab.{u}}
    (f : (S.abelianComponent n).obj G ⟶ (S.abelianComponent n).obj H)
    (g : (S.abelianComponent m).obj G ⟶ (S.abelianComponent m).obj H)
    (h : f ≫ (S.restrictTransitionAb φ).app H =
      (S.restrictTransitionAb φ).app G ≫ (S.transitionDirectImageAb φ).map g) :
    (S.transitionInverseImageAb φ).map f ≫ (S.fiberTransitionAb φ).app H =
      (S.fiberTransitionAb φ).app G ≫ g := by
  refine ((S.transitionAdjunctionAb φ).homEquiv _ _).injective ?_
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    S.fiberTransitionAb_adj, S.fiberTransitionAb_adj]
  exact h

/-- Transposition: a square for the direct-image transition gives the corresponding square for
its mate, the inverse-image transition. -/
theorem fiberTransitionAb_square' {n m : SimplexCategory} (φ : n ⟶ m)
    {G H : Sheaf S.totalTopology Ab.{u}}
    (f : (S.restrictAb n).obj G ⟶ (S.restrictAb n).obj H)
    (g : (S.restrictAb m).obj G ⟶ (S.restrictAb m).obj H)
    (h : f ≫ (S.restrictTransitionAb' φ).app H =
      (S.restrictTransitionAb' φ).app G ≫ (S.transitionDirectImageAb φ).map g) :
    (S.transitionInverseImageAb φ).map f ≫ (S.fiberTransitionAb' φ).app H =
      (S.fiberTransitionAb' φ).app G ≫ g := by
  obtain ⟨c⟩ := S
  cases c <;> exact fiberTransitionAb_square _ φ f g h

/-- The identity-labelled summand inclusion of `F` into the degree-`n` term of the
simplex-coefficient resolution, transported along the inverse-image transition at
`φ : ⦋n⦌ ⟶ ⦋m⦌`, is the `φ`-labelled summand of the degree-`m` decomposition of that term. -/
theorem transitionInverseImageAb_map_componentSheafInclusion_comp_fiberTransitionAb
    {n m : SimplexCategory} (φ : n ⟶ m) :
    (S.transitionInverseImageAb φ).map (componentSheafInclusion S F n) ≫
        (S.fiberTransitionAb φ).app ((barSimplicial S F).obj (Opposite.op n)) =
      (S.fiberTransitionAb φ).app F ≫
        Limits.Sigma.ι (fun _ : n ⟶ m => (S.abelianComponent m).obj F) φ ≫
          (abelianComponentBarIsoCoproduct S F n m).inv := by
  rw [sigma_ι_comp_abelianComponentBarIsoCoproduct_inv]
  exact fiberTransitionAb_square S φ _ _
    (componentSheafInclusion_comp_restrictTransitionAb S F φ)

/-- The identity-labelled summand inclusion of `F` into the degree-`n` term of the
simplex-coefficient resolution, transported along the inverse-image transition at
`φ : ⦋n⦌ ⟶ ⦋m⦌`, is the `φ`-labelled summand of the degree-`m` decomposition of that term. -/
theorem transitionInverseImageAb_map_componentSheafInclusion_comp_fiberTransitionAb'
    {n m : SimplexCategory} (φ : n ⟶ m) :
    (S.transitionInverseImageAb φ).map ((componentSheafInclusion' S n).app F) ≫
        (S.fiberTransitionAb' φ).app (((barSimplicial' S).obj F).obj (Opposite.op n)) =
      (S.fiberTransitionAb' φ).app F ≫
        Limits.Sigma.ι (fun _ : n ⟶ m => (S.restrictAb m).obj F) φ ≫
          (abelianComponentBarIsoCoproduct' S F n m).inv := by
  obtain ⟨c⟩ := S
  cases c <;>
    exact transitionInverseImageAb_map_componentSheafInclusion_comp_fiberTransitionAb _ F φ

attribute [local instance] componentFunctorHasCoproductsOfShape


variable (S : SimplicialSiteSituation.{u}) (F : Sheaf S.totalTopology Ab.{u})

/-- Restricted to the component of simplicial degree `m`, the canonical comparison map of
`componentLowerShriekMap` is the direct sum, over the simplex maps `φ : ⦋n⦌ ⟶ ⦋m⦌`, of the
inverse-image transitions at `φ`: the sum formula of Stacks 09WG identifies its source, and the
degree-`m` decomposition of the resolution term identifies its target. -/
theorem abelianComponent_map_componentLowerShriekMap_eq (n m : SimplexCategory) :
    (S.abelianComponent m).map (componentLowerShriekMap S F n) =
      ((S.componentLowerShriekRestrictionIsoCoproduct n m).app
          ((S.abelianComponent n).obj F)).hom ≫
        (Limits.sigmaObjIso (fun φ : n ⟶ m => S.transitionInverseImageAb φ)
          ((S.abelianComponent n).obj F)).hom ≫
        (Limits.Sigma.map fun φ : n ⟶ m => (S.fiberTransitionAb φ).app F) ≫
        (abelianComponentBarIsoCoproduct S F n m).inv := by
  have hu : (S.componentLowerShriekAbAdjunction n).unit.app ((S.abelianComponent n).obj F) ≫
        (S.abelianComponent n).map (componentLowerShriekMap S F n) =
      componentSheafInclusion S F n :=
    ((S.componentLowerShriekAbAdjunction n).homEquiv_unit _ _
        (componentLowerShriekMap S F n)).symm.trans
      (((S.componentLowerShriekAbAdjunction n).homEquiv _ _).apply_symm_apply _)
  have hM : (Limits.sigmaObjIso (fun φ : n ⟶ m => S.transitionInverseImageAb φ)
          ((S.abelianComponent n).obj F)).inv ≫
        ((S.componentLowerShriekRestrictionIsoCoproduct n m).app
            ((S.abelianComponent n).obj F)).inv ≫
          (S.abelianComponent m).map (componentLowerShriekMap S F n) =
      (Limits.Sigma.map fun φ : n ⟶ m => (S.fiberTransitionAb φ).app F) ≫
        (abelianComponentBarIsoCoproduct S F n m).inv := by
    refine Limits.Sigma.hom_ext _ _ (fun φ => ?_)
    have hleft : Limits.Sigma.ι (fun ψ : n ⟶ m =>
          (S.transitionInverseImageAb ψ).obj ((S.abelianComponent n).obj F)) φ ≫
        (Limits.sigmaObjIso (fun ψ : n ⟶ m => S.transitionInverseImageAb ψ)
          ((S.abelianComponent n).obj F)).inv =
        (Limits.Sigma.ι (fun ψ : n ⟶ m => S.transitionInverseImageAb ψ) φ).app
          ((S.abelianComponent n).obj F) :=
      Limits.ι_comp_sigmaObjIso_inv _ _ φ
    have hleg : (Limits.Sigma.ι (fun ψ : n ⟶ m => S.transitionInverseImageAb ψ) φ).app
            ((S.abelianComponent n).obj F) ≫
          ((S.componentLowerShriekRestrictionIsoCoproduct n m).app
            ((S.abelianComponent n).obj F)).inv =
        (S.componentSumFormulaLeg φ).app ((S.abelianComponent n).obj F) :=
      congr_app (S.sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg n m φ)
        ((S.abelianComponent n).obj F)
    have hnat := (S.fiberTransitionAb φ).naturality (componentLowerShriekMap S F n)
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k => k ≫
      (((S.componentLowerShriekRestrictionIsoCoproduct n m).app
          ((S.abelianComponent n).obj F)).inv ≫
        (S.abelianComponent m).map (componentLowerShriekMap S F n))) hleft) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k => k ≫
      (S.abelianComponent m).map (componentLowerShriekMap S F n))
      (hleg.trans (S.componentSumFormulaLeg_app φ ((S.abelianComponent n).obj F)))) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun k =>
      (S.transitionInverseImageAb φ).map
        ((S.componentLowerShriekAbAdjunction n).unit.app ((S.abelianComponent n).obj F)) ≫ k)
      hnat.symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k => k ≫
      (S.fiberTransitionAb φ).app ((barSimplicial S F).obj (Opposite.op n)))
      (((S.transitionInverseImageAb φ).map_comp _ _).symm.trans
        (congrArg (S.transitionInverseImageAb φ).map hu))) ?_
    refine Eq.trans
      (transitionInverseImageAb_map_componentSheafInclusion_comp_fiberTransitionAb S F φ) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k => k ≫ (abelianComponentBarIsoCoproduct S F n m).inv)
      (Limits.Sigma.ι_map (fun ψ : n ⟶ m => (S.fiberTransitionAb ψ).app F) φ).symm) ?_
    exact Category.assoc _ _ _
  exact (Iso.inv_comp_eq _).mp ((Iso.inv_comp_eq _).mp hM)

/-- Restricted to the component of simplicial degree `m`, the canonical comparison map of
`componentLowerShriekMap'` is the direct sum, over the simplex maps `φ : ⦋n⦌ ⟶ ⦋m⦌`, of the
inverse-image transitions at `φ`: the sum formula of Stacks 09WG identifies its source, and the
degree-`m` decomposition of the resolution term identifies its target. -/
theorem restrictAb_map_componentLowerShriekMap_eq (n m : SimplexCategory) :
    (S.restrictAb m).map ((componentLowerShriekMap' S n).app F) =
      ((S.componentLowerShriekRestrictionIsoCoproduct n m).app
          ((S.restrictAb n).obj F)).hom ≫
        (Limits.sigmaObjIso (fun φ : n ⟶ m => S.transitionInverseImageAb φ)
          ((S.restrictAb n).obj F)).hom ≫
        (Limits.Sigma.map fun φ : n ⟶ m => (S.fiberTransitionAb' φ).app F) ≫
        (abelianComponentBarIsoCoproduct' S F n m).inv := by
  obtain ⟨c⟩ := S
  cases c <;> exact abelianComponent_map_componentLowerShriekMap_eq _ F n m

/-- **Stacks 0D78, the degreewise comparison.** For a cartesian abelian sheaf on the total site
the canonical map from the lower shriek image of the restriction of `F` to the degree-`n` term of
the simplex-coefficient resolution is an isomorphism. -/
theorem isIso_componentLowerShriekMap (hF : IsCartesianAbSheaf S F) (n : SimplexCategory) :
    IsIso (componentLowerShriekMap S F n) := by
  refine isIso_of_forall_isIso_abelianComponent_map S (componentLowerShriekMap S F n)
    (fun m => ?_)
  have h (φ : n ⟶ m) : IsIso ((S.fiberTransitionAb φ).app F) :=
    isIso_fiberTransitionAb_app_of_isCartesianAbSheaf S F hF φ
  rw [abelianComponent_map_componentLowerShriekMap_eq S F n m]
  exact inferInstanceAs (IsIso
    (((S.componentLowerShriekRestrictionIsoCoproduct n m).app
          ((S.abelianComponent n).obj F) ≪≫
        Limits.sigmaObjIso (fun φ : n ⟶ m => S.transitionInverseImageAb φ)
          ((S.abelianComponent n).obj F) ≪≫
        Limits.Sigma.mapIso (fun φ : n ⟶ m => asIso ((S.fiberTransitionAb φ).app F)) ≪≫
        (abelianComponentBarIsoCoproduct S F n m).symm).hom))

/-- **Stacks 0D78, the degreewise comparison.** For a cartesian abelian sheaf on the total site
the canonical map from the lower shriek image of the restriction of `F` to the degree-`n` term of
the simplex-coefficient resolution is an isomorphism. -/
theorem isIso_componentLowerShriekMap' (hF : IsCartesianAbSheaf S F) (n : SimplexCategory) :
    IsIso ((componentLowerShriekMap' S n).app F) := by
  obtain ⟨c⟩ := S
  cases c <;> exact isIso_componentLowerShriekMap _ F hF n

namespace Augmentation

variable (D : Cat.{u, u}) (K : GrothendieckTopology D) (a : Augmentation S D K)
  (G : Sheaf K Ab.{u})

/-- **Stacks 0D78.** The exact complex
`… ⟶ g_{1!}(a_1⁻¹𝒢) ⟶ g_{0!}(a_0⁻¹𝒢) ⟶ a⁻¹𝒢 ⟶ 0`
of abelian sheaves on the total site: the alternating-face complex of the simplex-coefficient
resolution of `a⁻¹𝒢`, whose degree-`n` term is the extension by zero `g_{n!}(a_n⁻¹𝒢)`. -/
@[stacks 0D78]
def resolution : Resolution S D K a G where
  simplicial := barSimplicial S ((totalInverseImageAb S D K a).obj G)
  degreeIso n :=
    letI := isIso_componentLowerShriekMap S ((totalInverseImageAb S D K a).obj G)
      (isCartesianAbSheaf_totalInverseImageAb S D K a G) ⦋n⦌
    (asIso (componentLowerShriekMap S ((totalInverseImageAb S D K a).obj G) ⦋n⦌)).symm ≪≫
      (componentLowerShriekAb S ⦋n⦌).mapIso
        (componentRestrictionAbInverseImageIso S D K a G ⦋n⦌)
  augmentation := barAugmentation S ((totalInverseImageAb S D K a).obj G)
  augmentation_comp := barAugmentation_comp S ((totalInverseImageAb S D K a).obj G)
  exact_positive := barSimplicial_exactAt S ((totalInverseImageAb S D K a).obj G)
  exact_zero := barAugmentation_exact S ((totalInverseImageAb S D K a).obj G)
  augmentation_epi := barAugmentation_epi S ((totalInverseImageAb S D K a).obj G)

end Augmentation

end CategoryTheory.SimplicialSiteSituation


end
