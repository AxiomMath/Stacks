module

public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Basic
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Map
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Presheaf
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs

/-!
# Hypercoverings and morphisms of sites

A morphism of sites whose underlying functor preserves equalizers and fibre products carries a
hypercovering of the final presheaf to a hypercovering of the final presheaf: applying the
functor degreewise to the simplicial semi-representable object underlying a hypercovering of the
source site again underlies a hypercovering of the target site.

## Main results

* `exists_hypercovering_of_map` is Tag 0DAY: the degreewise image of a hypercovering under the
  underlying functor of such a morphism of sites underlies a hypercovering.

## Implementation notes

The image of a semi-representable object retains its indexing type and applies the functor to
each represented object; this is `mapFormalCoproduct` of
`StacksFrontier.CategoryTheory.Sites.Hypercovering.Basic`. Since a hypercovering of a presheaf is
bundled together with its augmentation, the conclusion is stated as the existence of a
hypercovering whose underlying simplicial object is the degreewise image of the given one,
rather than as a construction.

The three conditions are transported separately. Condition (1) goes through
`GrothendieckTopology.CoversTop`: the degree-zero augmentation of the associated simplicial
presheaf is locally surjective exactly when the family of objects of degree zero covers the
final object (`coversTop_of_locallySurjective` and `locallySurjective_of_coversTop`), and that
property is preserved by a morphism of sites because the sheaf pullback is a left adjoint
(`coversTop_map`). Conditions (2) and (3) are transported by the sheaf pullback as well; what is
needed of it is that it preserves binary products and finite connected limits, so that it
commutes with the fibre product in degree one and with the matching limits of the positive
coskeleta. The matching categories of a positive coskeleton are finite
(`finCategoryStructuredArrowInclusionOp`), and `unit_comp_matchingCone_π` records that the
coskeleton unit followed by a projection of the matching cone is the corresponding structure map,
which is what identifies the image of a matching object with the matching object of the image.

## References

* [Stacks Project, Tag 0DAY](https://stacks.math.columbia.edu/tag/0DAY)
-/

@[expose] public section

universe w r q vC vD uC uD vA uA vB uB

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- Coproducts of presheaves of types indexed by `Type w`, stated directly: instance search for
it times out on Lean v4.35.0 (through `UnivLE`). -/
private instance hasCoproducts_functor_type (K : Type uA) [Category.{vA} K] :
    HasCoproducts.{w} (K ⥤ Type (max w r)) :=
  fun _ => functorCategoryHasColimitsOfShape

/-- Local surjectivity is unchanged when all values are lifted to a larger universe. -/
private lemma locallySurjective_ulift
    (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type r} (f : P ⟶ Q)
    [Presheaf.IsLocallySurjective J f] :
    Presheaf.IsLocallySurjective J
      ((Functor.whiskeringRight Cᵒᵖ (Type r) (Type (max r q))).obj
        uliftFunctor.{max r q, r} |>.map f) := by
  refine ⟨?_⟩
  intro U s
  change ULift.{max r q, r} (Q.obj (op U)) at s
  apply J.superset_covering ?_ (Presheaf.imageSieve_mem J f (ULift.down s))
  rintro V g ⟨t, ht⟩
  refine ⟨ULift.up t, ?_⟩
  show ULift.up (f.app _ t) = ULift.up (Q.map g.op (ULift.down s))
  exact congrArg ULift.up ht

/-- Pullback of sheaves sends the sheafification of a locally surjective map of presheaves to a
locally surjective map of sheaves. -/
private lemma sheafPullback_preservesLocallySurjective
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : D ⥤ C) [u.IsContinuous K J]
    [(u.sheafPushforwardContinuous (Type (max q vD vC)) K J).IsRightAdjoint]
    [HasWeakSheafify K (Type (max q vD vC))]
    [K.WEqualsLocallyBijective (Type (max q vD vC))]
    [HasSheafify K (Type (max q vD vC))]
    [HasSheafify J (Type (max q vD vC))]
    {P₁ P₂ : Dᵒᵖ ⥤ Type (max q vD vC)} (f : P₁ ⟶ P₂)
    [Presheaf.IsLocallySurjective K f] :
    Sheaf.IsLocallySurjective
      ((u.sheafPullback (Type (max q vD vC)) K J).map
        ((presheafToSheaf K (Type (max q vD vC))).map f)) := by
  rw [Sheaf.isLocallySurjective_iff_epi]
  have : Epi ((presheafToSheaf K (Type (max q vD vC))).map f) := by
    apply (Sheaf.isLocallySurjective_iff_epi _).1
    exact (Presheaf.isLocallySurjective_presheafToSheaf_map_iff K f).2 inferInstance
  have : Functor.PreservesEpimorphisms
      (u.sheafPullback (Type (max q vD vC)) K J) := by
    constructor
    intro X Y g hg
    have := (u.sheafAdjunctionContinuous (Type (max q vD vC)) K J).leftAdjoint_preservesColimits
    exact preserves_epi_of_preservesColimit
      (u.sheafPullback (Type (max q vD vC)) K J) g
  infer_instance

private def familySupport {I : Type w} (Y : I → C) :
    Subfunctor ((Functor.const Cᵒᵖ).obj PUnit.{q + 1}) where
  obj V := {_x | ∃ i, Nonempty (V.unop ⟶ Y i)}
  map := by
    rintro V W f s ⟨i, ⟨g⟩⟩
    exact ⟨i, ⟨f.unop ≫ g⟩⟩

private lemma coversTop_map (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : D ⥤ C) [IsMorphismOfSites.{q} u K J]
    {I : Type w} (Y : I → D) (hY : K.CoversTop Y) : J.CoversTop (u.obj ∘ Y) := by
  let T := Sheaf.terminal J (Types.isTerminalPUnit.{q})
  let S := familySupport.{w, q} (u.obj ∘ Y)
  let G : Sheaf J (Type q) := ⟨(S.sheafify J).toFunctor,
    (isSheaf_iff_isSheaf_of_type _ _).2
      (S.sheafify_isSheaf ((isSheaf_iff_isSheaf_of_type _ _).1 T.property))⟩
  let R := u.sheafPushforwardContinuous (Type q) K J
  let x : Presheaf.FamilyOfElementsOnObjects (R.obj G).obj Y := fun i =>
    ⟨PUnit.unit, S.le_sheafify J _ ⟨i, ⟨𝟙 _⟩⟩⟩
  have hx : x.IsCompatible := fun _ _ _ _ _ => Subtype.ext (PUnit.ext _ _)
  let s := hx.section_ hY (R.obj G).property
  let a : Sheaf.terminal K Types.isTerminalPUnit ⟶ R.obj G :=
    ⟨{ app V := ↾fun _ => s.val V
       naturality V W f := by ext; exact (s.property f).symm }⟩
  obtain ⟨L, ⟨adj⟩, hL⟩ := (‹IsMorphismOfSites.{q} u K J›).hasExactLeftAdjoint
  let := hL
  let hT := (Sheaf.isTerminalTerminal K Types.isTerminalPUnit).isTerminalObj L
  let b : T ⟶ G := hT.from T ≫ (adj.homEquiv _ _).symm a
  exact fun V => (b.hom.app (op V) PUnit.unit).property

private lemma associated_exists_rep (X : FormalCoproduct.{w} C) (V : C)
    (s : (associatedPresheafFunctor.{q}.obj X).obj (op V)) :
    ∃ i, Nonempty (V ⟶ X.obj i) := by
  let E := (evaluation Cᵒᵖ (Type (max w vC))).obj (op V)
  have h := isColimitOfPreserves E (colimit.isColimit
    (Discrete.functor (fun i : X.I => uliftYoneda.{w}.obj (X.obj i))))
  obtain ⟨i, t, ht⟩ := Types.jointly_surjective_of_isColimit h s.down
  exact ⟨i.as, ⟨t.down⟩⟩

private lemma coversTop_of_locallySurjective (J : GrothendieckTopology C)
    (X : FormalCoproduct.{w} C) {T : Cᵒᵖ ⥤ Type (max q w vC)}
    (hT : IsTerminal T) (a : associatedPresheafFunctor.{q}.obj X ⟶ T)
    [Presheaf.IsLocallySurjective J a] : J.CoversTop X.obj := by
  intro V
  let s := (hT.from ((Functor.const _).obj PUnit)).app (op V) PUnit.unit
  apply J.superset_covering ?_ (Presheaf.imageSieve_mem J a s)
  rintro W f ⟨t, ht⟩
  exact associated_exists_rep X W t

private lemma locallySurjective_of_coversTop (J : GrothendieckTopology C)
    (X : FormalCoproduct.{w} C) {T : Cᵒᵖ ⥤ Type (max q w vC)}
    (hT : IsTerminal T) (a : associatedPresheafFunctor.{q}.obj X ⟶ T)
    (hX : J.CoversTop X.obj) : Presheaf.IsLocallySurjective J a := by
  constructor
  intro V s
  apply J.superset_covering ?_ (hX V)
  rintro W f ⟨i, ⟨g⟩⟩
  refine ⟨ULift.up ((Sigma.ι (fun i : X.I => uliftYoneda.{w}.obj (X.obj i)) i).app
    (op W) (ULift.up g)), ?_⟩
  have ht := hT.isTerminalObj ((evaluation _ _).obj (op W))
  let : Unique (T.obj (op W)) := Types.isTerminalEquivUnique _ ht
  exact Subsingleton.elim _ _

private noncomputable def evalCompIso {A : Type uA} [Category.{vA} A]
    {B : Type uB} [Category.{vB} B] [HasCoproducts.{w} A] [HasCoproducts.{w} B]
    (F : C ⥤ A) (G : A ⥤ B) [∀ I : Type w, PreservesColimitsOfShape (Discrete I) G] :
    (FormalCoproduct.eval.{w} C A).obj F ⋙ G ≅
      (FormalCoproduct.eval.{w} C B).obj (F ⋙ G) := by
  refine (NatIso.ofComponents (F := (FormalCoproduct.eval.{w} C B).obj (F ⋙ G))
    (G := (FormalCoproduct.eval.{w} C A).obj F ⋙ G)
    (fun X => (PreservesCoproduct.iso G (fun i : X.I => F.obj (X.obj i))).symm) ?_).symm
  intro X Y f
  change (Sigma.desc (fun i : X.I => G.map (F.map (f.φ i)) ≫
      Sigma.ι (fun j : Y.I => G.obj (F.obj (Y.obj j))) (f.f i))) ≫
      sigmaComparison G (fun j : Y.I => F.obj (Y.obj j)) =
    sigmaComparison G (fun i : X.I => F.obj (X.obj i)) ≫
      G.map (Sigma.desc (fun i : X.I => F.map (f.φ i) ≫
        Sigma.ι (fun j : Y.I => F.obj (Y.obj j)) (f.f i)))
  apply Sigma.hom_ext
  intro i
  simp only [Category.assoc, Sigma.ι_desc_assoc, ι_comp_sigmaComparison,
    ι_comp_sigmaComparison_assoc, ← G.map_comp, Sigma.ι_desc]

private noncomputable def associatedEvalIso :
    associatedPresheafFunctor.{q, w} (C := C) ≅
      (FormalCoproduct.eval.{w} C (Cᵒᵖ ⥤ Type (max q w vC))).obj
        uliftYoneda.{max q w} := by
  let G := (Functor.whiskeringRight Cᵒᵖ (Type (max w vC))
    (Type (max q w vC))).obj uliftFunctor.{q}
  let e : associatedPresheafFunctor.{q, w} (C := C) ≅
      (FormalCoproduct.eval.{w} C _).obj (uliftYoneda.{w} ⋙ G) := evalCompIso _ _
  refine e ≪≫ (FormalCoproduct.eval C _).mapIso ?_
  refine NatIso.ofComponents (fun X => NatIso.ofComponents (fun V => ?_) ?_) ?_
  · exact (Equiv.ulift.trans Equiv.ulift |>.trans Equiv.ulift.symm).toIso
  · intros; rfl
  · intros; rfl

private noncomputable def associatedHomIso (V : C) :
    coyoneda.obj (op ((FormalCoproduct.incl.{w} C).obj V)) ⋙ uliftFunctor.{q} ≅
      associatedPresheafFunctor.{q, w} (C := C) ⋙
        (evaluation Cᵒᵖ (Type (max q w vC))).obj (op V) := by
  let e (X : FormalCoproduct.{w} C) :=
    PreservesCoproduct.iso ((evaluation Cᵒᵖ (Type (max w vC))).obj (op V))
      (fun i : X.I => uliftYoneda.{w}.obj (X.obj i)) ≪≫
      Types.coproductIso (fun i : X.I => ULift.{w} (V ⟶ X.obj i))
  let d (X : FormalCoproduct.{w} C) :=
    ((Equiv.ulift.trans (e X).toEquiv).trans
      ((Equiv.sigmaCongrRight fun _ => Equiv.ulift).trans
        ((FormalCoproduct.inclHomEquiv V X).symm.trans Equiv.ulift.symm))).symm.toIso
  have hd (X : FormalCoproduct.{w} C)
      (f : (FormalCoproduct.incl.{w} C).obj V ⟶ X) :
      (d X).hom (ULift.up f) = ULift.up
        ((Sigma.ι (fun i : X.I => uliftYoneda.{w}.obj (X.obj i)) (f.f PUnit.unit)).app
          (op V) (ULift.up (f.φ PUnit.unit))) := by
    change ULift.up ((e X).inv ⟨f.f PUnit.unit, ULift.up (f.φ PUnit.unit)⟩) = _
    simp [e, PreservesCoproduct.inv_hom, sigmaComparison, -types_comp_apply]
  refine NatIso.ofComponents d ?_
  intro X Y f
  ext s
  obtain ⟨s⟩ := s
  change (d Y).hom (ULift.up (s ≫ f)) =
    (associatedPresheafFunctor.{q}.map f).app (op V) ((d X).hom (ULift.up s))
  rw [hd, hd]
  apply ULift.ext
  change _ = ((Sigma.ι _ (s.f PUnit.unit) ≫
    (FormalCoproduct.uliftYoneda.map f)).app (op V)) (ULift.up (s.φ PUnit.unit))
  change _ = ((Sigma.ι _ (s.f PUnit.unit) ≫
    Sigma.desc (fun i : X.I => uliftYoneda.{w}.map (f.φ i) ≫
      Sigma.ι (fun j : Y.I => uliftYoneda.{w}.obj (Y.obj j)) (f.f i))).app (op V))
        (ULift.up (s.φ PUnit.unit))
  rw [Sigma.ι_desc]
  rfl

private lemma preservesLimits_associated (I : Type*) [Category I] :
    PreservesLimitsOfShape I (associatedPresheafFunctor.{q, w} (C := C)) := by
  apply preservesLimitsOfShape_of_evaluation
  intro V
  exact preservesLimitsOfShape_of_natIso (associatedHomIso V.unop)

private noncomputable def mapAssociatedLanIso (u : D ⥤ C) :
    mapFormalCoproduct.{w} u ⋙
        associatedPresheafFunctor.{max q w vC vD uC uD} ≅
      associatedPresheafFunctor.{max q w vC vD uC uD} ⋙ u.op.lan := by
  let E := Type (max q w vC vD uC uD)
  let A : D ⥤ Dᵒᵖ ⥤ E := uliftYoneda.{max q w vC vD uC uD}
  let B : C ⥤ Cᵒᵖ ⥤ E := uliftYoneda.{max q w vC vD uC uD}
  let e₁ : mapFormalCoproduct.{w} u ⋙ (FormalCoproduct.eval C _).obj B ≅
      (FormalCoproduct.eval D _).obj (u ⋙ B) := Iso.refl _
  let e₂ : u ⋙ B ≅ A ⋙ u.op.lan :=
    Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{max q w vC vD uC uD} u
  have : PreservesColimitsOfSize.{w, w} (u.op.lan : (Dᵒᵖ ⥤ E) ⥤ Cᵒᵖ ⥤ E) :=
    (u.op.lanAdjunction E).leftAdjoint_preservesColimits
  let e₃ : (FormalCoproduct.eval.{w} D _).obj A ⋙ u.op.lan ≅
      (FormalCoproduct.eval.{w} D _).obj (A ⋙ u.op.lan) := evalCompIso _ _
  exact Functor.isoWhiskerLeft _ associatedEvalIso ≪≫ e₁ ≪≫
    (FormalCoproduct.eval D _).mapIso e₂ ≪≫ e₃.symm ≪≫
      Functor.isoWhiskerRight associatedEvalIso.symm _

private noncomputable def sheafifyLanIso (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (u : D ⥤ C) [u.IsContinuous K J] :
    u.op.lan ⋙ presheafToSheaf J (Type (max q vC vD uC uD)) ≅
      presheafToSheaf K (Type (max q vC vD uC uD)) ⋙
        u.sheafPullback (Type (max q vC vD uC uD)) K J := by
  let E := Type (max q vC vD uC uD)
  exact Adjunction.leftAdjointUniq
    ((u.op.lanAdjunction E).comp (sheafificationAdjunction J E))
    (((sheafificationAdjunction K E).comp (u.sheafAdjunctionContinuous E K J)).ofNatIsoRight
      (u.sheafPushforwardContinuousCompSheafToPresheafIso E K J))

private noncomputable def mapAssociatedSheafIso (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (u : D ⥤ C) [u.IsContinuous K J] :
    mapFormalCoproduct.{w} u ⋙
        associatedPresheafFunctor.{max q w vC vD uC uD} ⋙
          presheafToSheaf J (Type (max q w vC vD uC uD)) ≅
      associatedPresheafFunctor.{max q w vC vD uC uD} ⋙
        presheafToSheaf K (Type (max q w vC vD uC uD)) ⋙
          u.sheafPullback (Type (max q w vC vD uC uD)) K J :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (mapAssociatedLanIso.{w, q} u) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (sheafifyLanIso.{max q w} J K u)

/-- Local surjectivity of the image of a map under `associatedPresheafFunctor` does not depend on
the universe parameter. -/
private lemma locallySurjective_associated_of {X Y : FormalCoproduct.{w} C}
    (J : GrothendieckTopology C) (f : X ⟶ Y)
    (h : Presheaf.IsLocallySurjective J (associatedPresheafFunctor.{q}.map f)) :
    Presheaf.IsLocallySurjective J (associatedPresheafFunctor.{r}.map f) := by
  constructor
  intro V s
  let t : (associatedPresheafFunctor.{q}.obj Y).obj (op V) := ULift.up s.down
  apply J.superset_covering ?_
    (Presheaf.imageSieve_mem J (associatedPresheafFunctor.{q}.map f) t)
  rintro W g ⟨t, ht⟩
  exact ⟨ULift.up t.down, congrArg ULift.up (congrArg ULift.down ht)⟩

private lemma locallySurjective_associated_iff (J : GrothendieckTopology C)
    {X Y : FormalCoproduct.{w} C} (f : X ⟶ Y) :
    Presheaf.IsLocallySurjective J (associatedPresheafFunctor.{q}.map f) ↔
      Presheaf.IsLocallySurjective J (associatedPresheafFunctor.{r}.map f) :=
  ⟨locallySurjective_associated_of J f, locallySurjective_associated_of J f⟩

private lemma epi_of_limit_cone_comparison
    {I : Type*} [Category I] {F F' : I ⥤ C}
    {c : Cone F} {c' : Cone F'} (hc : IsLimit c) (hc' : IsLimit c')
    (e : F ≅ F') {Z Z' : C} (eZ : Z ≅ Z') (f : Z ⟶ c.pt) (f' : Z' ⟶ c'.pt)
    (hf : Epi f) (h : ∀ i, f ≫ c.π.app i ≫ e.hom.app i = eZ.hom ≫ f' ≫ c'.π.app i) :
    Epi f' := by
  let d := (Cone.postcompose e.hom).obj c
  let hd := (IsLimit.postcomposeHomEquiv e c).symm hc
  let a := hd.conePointUniqueUpToIso hc'
  have ha : eZ.hom ≫ f' = f ≫ a.hom := by
    apply hc'.hom_ext
    intro i
    simpa [a, d] using (h i).symm
  exact epi_of_epi_fac ha

private noncomputable def matchingCone
    (X : SimplicialObject C) (n : ℕ) (m : SimplexCategoryᵒᵖ)
    [∀ F : SimplicialObject.Truncated C n,
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    Cone (StructuredArrow.proj m (SimplexCategory.Truncated.inclusion n).op ⋙
      (SimplicialObject.truncation n).obj X) :=
  (Functor.RightExtension.mk ((SimplicialObject.cosk n).obj X)
    ((SimplicialObject.coskAdj n).counit.app _)).coneAt m

private noncomputable def matchingConeIsLimit
    (X : SimplicialObject C) (n : ℕ) (m : SimplexCategoryᵒᵖ)
    [∀ F : SimplicialObject.Truncated C n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F] :
    IsLimit (matchingCone X n m) :=
  Functor.isPointwiseRightKanExtensionOfIsRightKanExtension _ _ m

private lemma unit_comp_matchingCone_π
    (X : SimplicialObject C) (n : ℕ) (m : SimplexCategoryᵒᵖ)
    [∀ F : SimplicialObject.Truncated C n,
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]
    (i : StructuredArrow m (SimplexCategory.Truncated.inclusion n).op) :
    ((SimplicialObject.coskAdj n).unit.app X).app m ≫
      (matchingCone X n m).π.app i = X.map i.hom := by
  let η := (SimplicialObject.coskAdj n).unit.app X
  let ε := (SimplicialObject.coskAdj n).counit.app ((SimplicialObject.truncation n).obj X)
  have h : η.app ((SimplexCategory.Truncated.inclusion n).op.obj i.right) ≫
      ε.app i.right = 𝟙 _ :=
    NatTrans.congr_app ((SimplicialObject.coskAdj n).left_triangle_components X) i.right
  have hnat : X.map i.hom ≫
      η.app ((SimplexCategory.Truncated.inclusion n).op.obj i.right) =
      η.app m ≫ ((SimplicialObject.cosk n).obj X).map i.hom := η.naturality i.hom
  show η.app m ≫
    (((SimplicialObject.cosk n).obj X).map i.hom ≫ ε.app i.right) = X.map i.hom
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun f ↦ f ≫ ε.app i.right) hnat.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun f ↦ X.map i.hom ≫ f) h).trans ?_
  exact Category.comp_id _

private lemma wEqualsLocallyBijective_types (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective (Type (max q uC vC)) :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{vC,
    max q uC vC, uC, (max q uC vC) + 1, max q uC vC} J

private lemma locallySurjective_higher_map
    [HasEqualizers C] [HasPullbacks C] [HasEqualizers D] [HasPullbacks D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : D ⥤ C)
    [u.IsContinuous K J]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [PreservesLimitsOfShape WalkingCospan u]
    (X : SimplicialObject (FormalCoproduct.{w} D)) (n : ℕ) (hn : 1 ≤ n)
    [Presheaf.IsLocallySurjective K (higherMatchingMap.{vD} X n hn)] :
    Presheaf.IsLocallySurjective J
      (higherMatchingMap.{vC} (X ⋙ mapFormalCoproduct u) n hn) := by
  let := hasPositiveCoskeleta (C := C) n hn
  let := hasPositiveCoskeleta (C := D) n hn
  let m := op (SimplexCategory.mk (n + 1))
  let I := StructuredArrow m (SimplexCategory.Truncated.inclusion n).op
  let := finCategoryStructuredArrowInclusionOp n m
  let : NeZero n := ⟨by omega⟩
  let : IsConnected I := Functor.Final.out m
  let E := Type (max w vC vD uC uD)
  let : J.WEqualsLocallyBijective E :=
    wEqualsLocallyBijective_types.{max w vC vD uC uD} J
  let : K.WEqualsLocallyBijective E :=
    wEqualsLocallyBijective_types.{max w vC vD uC uD} K
  let AD := associatedPresheafFunctor.{max w vC vD uC uD, w} (C := D)
  let AC := associatedPresheafFunctor.{max w vC vD uC uD, w} (C := C)
  let SD := AD ⋙ presheafToSheaf K E
  let SC := AC ⋙ presheafToSheaf J E
  let L : Sheaf K E ⥤ Sheaf J E := u.sheafPullback E K J
  let R := SD ⋙ L
  let : PreservesLimitsOfShape I AD := preservesLimits_associated I
  let : PreservesLimitsOfShape I AC := preservesLimits_associated I
  let : PreservesLimitsOfShape I L :=
    show PreservesLimitsOfShape I (u.sheafPullback E K J) from
      Functor.preservesLimitsOfShape_sheafPullback.{max w vC vD uC uD} u K J I
  let f := ((SimplicialObject.coskAdj n).unit.app X).app m
  let f' := ((SimplicialObject.coskAdj n).unit.app (X ⋙ mapFormalCoproduct u)).app m
  have hsmall : Presheaf.IsLocallySurjective K
      (associatedPresheafFunctor.{vD, w}.map f) :=
    ‹Presheaf.IsLocallySurjective K (higherMatchingMap.{vD} X n hn)›
  let : Presheaf.IsLocallySurjective K (AD.map f) :=
    (locallySurjective_associated_iff K f).1 hsmall
  have : Epi (R.map f) := (Sheaf.isLocallySurjective_iff_epi _).1
    (sheafPullback_preservesLocallySurjective.{max w vC vD uC uD} J K u (AD.map f))
  have hepi : Epi (SC.map f') := by
    let c := R.mapCone (matchingCone X n m)
    let c' := SC.mapCone (matchingCone (X ⋙ mapFormalCoproduct u) n m)
    let e := (mapAssociatedSheafIso.{w, 0} J K u).symm
    apply epi_of_limit_cone_comparison
      (isLimitOfPreserves R (matchingConeIsLimit X n m))
      (isLimitOfPreserves SC (matchingConeIsLimit (X ⋙ mapFormalCoproduct u) n m))
      (Functor.isoWhiskerLeft _ e) (e.app (X.obj m)) (R.map f) (SC.map f')
      (show Epi (R.map f) from ‹Epi (R.map f)›)
    intro i
    calc
      _ = R.map (f ≫ (matchingCone X n m).π.app i) ≫
          e.hom.app (X.obj ((SimplexCategory.Truncated.inclusion n).op.obj i.right)) :=
        (R.map_comp_assoc _ _ _).symm
      _ = R.map (X.map i.hom) ≫ e.hom.app _ := by
        rw [unit_comp_matchingCone_π]
      _ = (e.app (X.obj m)).hom ≫ SC.map ((X ⋙ mapFormalCoproduct u).map i.hom) :=
        e.hom.naturality (X.map i.hom)
      _ = _ := by
        rw [← unit_comp_matchingCone_π (X ⋙ mapFormalCoproduct u) n m i]
        exact congrArg ((e.app (X.obj m)).hom ≫ ·) (SC.map_comp _ _)
  exact (locallySurjective_associated_iff J f').2
    ((Presheaf.isLocallySurjective_presheafToSheaf_map_iff J (AC.map f')).1
      ((Sheaf.isLocallySurjective_iff_epi _).2 hepi))

private lemma locallySurjective_of_ulift
    (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type r} (f : P ⟶ Q)
    (hf : Presheaf.IsLocallySurjective J (Functor.whiskerRight f uliftFunctor.{q})) :
    Presheaf.IsLocallySurjective J f := by
  constructor
  intro V s
  let t : (Q ⋙ uliftFunctor.{q}).obj (op V) := ULift.up s
  apply J.superset_covering ?_
    (Presheaf.imageSieve_mem J (Functor.whiskerRight f uliftFunctor.{q}) t)
  rintro W g ⟨t, ht⟩
  exact ⟨t.down, congrArg ULift.down ht⟩

private noncomputable def associatedLiftIso :
    associatedPresheafFunctor.{q, w} (C := C) ⋙
      (Functor.whiskeringRight _ _ _).obj uliftFunctor.{r} ≅
      associatedPresheafFunctor.{max q r, w} (C := C) := by
  refine NatIso.ofComponents (fun X => NatIso.ofComponents (fun V => ?_) ?_) ?_
  · exact ((Equiv.ulift.trans Equiv.ulift).trans Equiv.ulift.symm).toIso
  · intros; rfl
  · intros; rfl

private noncomputable def oneMatchingCone
    (X : SimplicialObject (Cᵒᵖ ⥤ Type q)) (T : Cᵒᵖ ⥤ Type q)
    (a : X ⟶ (SimplicialObject.const _).obj T) :
    BinaryFan (X.obj (op ⦋0⦌)) (X.obj (op ⦋0⦌)) :=
  BinaryFan.mk (pullback.fst (a.app (op ⦋0⦌)) (a.app (op ⦋0⦌)))
    (pullback.snd (a.app (op ⦋0⦌)) (a.app (op ⦋0⦌)))

private noncomputable def oneMatchingConeIsLimit
    (X : SimplicialObject (Cᵒᵖ ⥤ Type q)) (T : Cᵒᵖ ⥤ Type q)
    (a : X ⟶ (SimplicialObject.const _).obj T) (hT : IsTerminal T) :
    IsLimit (oneMatchingCone X T a) :=
  isProductOfIsTerminalIsPullback _ _ _ _ hT (pullbackIsPullback _ _)

private lemma locallySurjective_one_map
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : D ⥤ C)
    [u.IsContinuous K J]
    [PreservesLimitsOfShape (Discrete WalkingPair)
      (u.sheafPullback (Type (max w vC vD uC uD)) K J)]
    (X : SimplicialObject (FormalCoproduct.{w} D))
    (TD : Dᵒᵖ ⥤ Type (max w vD)) (TC : Cᵒᵖ ⥤ Type (max w vC))
    (a : associatedSimplicialPresheaf.{vD} X ⟶
      (SimplicialObject.const _).obj TD)
    (b : associatedSimplicialPresheaf.{vC} (X ⋙ mapFormalCoproduct u) ⟶
      (SimplicialObject.const _).obj TC)
    (hTD : IsTerminal TD) (hTC : IsTerminal TC)
    [Presheaf.IsLocallySurjective K (oneMatchingMap _ TD a)] :
    Presheaf.IsLocallySurjective J (oneMatchingMap _ TC b) := by
  let E := Type (max w vC vD uC uD)
  let UD : (Dᵒᵖ ⥤ Type (max w vD)) ⥤ (Dᵒᵖ ⥤ E) :=
    (Functor.whiskeringRight _ _ _).obj uliftFunctor.{max w vC vD uC uD}
  let UC : (Cᵒᵖ ⥤ Type (max w vC)) ⥤ (Cᵒᵖ ⥤ E) :=
    (Functor.whiskeringRight _ _ _).obj uliftFunctor.{max w vC vD uC uD}
  let HD := UD ⋙ presheafToSheaf K E
  let HC := UC ⋙ presheafToSheaf J E
  let L : Sheaf K E ⥤ Sheaf J E := u.sheafPullback E K J
  let R := HD ⋙ L
  let AD := associatedPresheafFunctor.{vD, w} (C := D)
  let AC := associatedPresheafFunctor.{vC, w} (C := C)
  let eD : AD ⋙ HD ≅ associatedPresheafFunctor.{max w vC vD uC uD, w} ⋙
      presheafToSheaf K E :=
    Functor.isoWhiskerRight (associatedLiftIso.{w, max w vC vD uC uD, vD}) _
  let eC : AC ⋙ HC ≅ associatedPresheafFunctor.{max w vC vD uC uD, w} ⋙
      presheafToSheaf J E :=
    Functor.isoWhiskerRight (associatedLiftIso.{w, max w vC vD uC uD, vC}) _
  let e : AD ⋙ R ≅ mapFormalCoproduct u ⋙ AC ⋙ HC :=
    Functor.isoWhiskerRight eD L ≪≫ (mapAssociatedSheafIso.{w, 0} J K u).symm ≪≫
      Functor.isoWhiskerLeft (mapFormalCoproduct u) eC.symm
  let f := oneMatchingMap _ TD a
  let g := oneMatchingMap _ TC b
  let : J.WEqualsLocallyBijective E :=
    wEqualsLocallyBijective_types.{max w vC vD uC uD} J
  let : K.WEqualsLocallyBijective E :=
    wEqualsLocallyBijective_types.{max w vC vD uC uD} K
  let : Presheaf.IsLocallySurjective K (UD.map f) :=
    locallySurjective_ulift.{max w vD, max w vC vD uC uD} K f
  have : Epi (R.map f) := (Sheaf.isLocallySurjective_iff_epi _).1
    (sheafPullback_preservesLocallySurjective.{max w vC vD uC uD} J K u (UD.map f))
  have hg : Epi (HC.map g) := by
    let e₀ := e.app (X.obj (op ⦋0⦌))
    let ei : (pair (AD.obj (X.obj (op ⦋0⦌))) (AD.obj (X.obj (op ⦋0⦌))) ⋙ R) ≅
        (pair (AC.obj ((mapFormalCoproduct u).obj (X.obj (op ⦋0⦌))))
          (AC.obj ((mapFormalCoproduct u).obj (X.obj (op ⦋0⦌)))) ⋙ HC) :=
      NatIso.ofComponents (fun i => by rcases i with ⟨i⟩; cases i <;> exact e₀)
        (by rintro ⟨i⟩ ⟨j⟩ ⟨f⟩; cases f; cases i <;> simp)
    apply epi_of_limit_cone_comparison
      (isLimitOfPreserves R (oneMatchingConeIsLimit _ TD a hTD))
      (isLimitOfPreserves HC (oneMatchingConeIsLimit _ TC b hTC))
      ei (e.app (X.obj (op ⦋1⦌))) (R.map f) (HC.map g)
      (show Epi (R.map f) from ‹Epi (R.map f)›)
    have key : ∀ (k : Fin 2)
        (pD : pullback (a.app (op ⦋0⦌)) (a.app (op ⦋0⦌)) ⟶
          (associatedSimplicialPresheaf.{vD} X).obj (op ⦋0⦌))
        (pC : pullback (b.app (op ⦋0⦌)) (b.app (op ⦋0⦌)) ⟶
          (associatedSimplicialPresheaf.{vC} (X ⋙ mapFormalCoproduct u)).obj (op ⦋0⦌)),
        f ≫ pD = (associatedSimplicialPresheaf.{vD} X).δ k →
        g ≫ pC = (associatedSimplicialPresheaf.{vC} (X ⋙ mapFormalCoproduct u)).δ k →
        R.map f ≫ R.map pD ≫ e₀.hom = (e.app (X.obj (op ⦋1⦌))).hom ≫ HC.map g ≫ HC.map pC := by
      intro k pD pC hD hC
      rw [← R.map_comp_assoc, hD, ← HC.map_comp, hC]
      exact e.hom.naturality (X.δ k)
    rintro ⟨i⟩
    cases i
    · exact key 0 _ _ (oneMatchingMap_fst _ _ _) (oneMatchingMap_fst _ _ _)
    · exact key 1 _ _ (oneMatchingMap_snd _ _ _) (oneMatchingMap_snd _ _ _)
  have : Presheaf.IsLocallySurjective J (UC.map g) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff J (UC.map g)).1
      ((Sheaf.isLocallySurjective_iff_epi _).2 hg)
  exact locallySurjective_of_ulift.{max w vC, max w vC vD uC uD} J g this

private lemma preservesBinaryProducts_sheafPullback
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : D ⥤ C)
    [IsMorphismOfSites.{q} u K J]
    [(u.sheafPushforwardContinuous (Type q) K J).IsRightAdjoint] :
    PreservesLimitsOfShape (Discrete WalkingPair) (u.sheafPullback (Type q) K J) := by
  obtain ⟨L, ⟨adj⟩, hL⟩ := (‹IsMorphismOfSites.{q} u K J›).hasExactLeftAdjoint
  let := hL
  exact preservesLimitsOfShape_of_natIso
    (Adjunction.leftAdjointUniq adj (u.sheafAdjunctionContinuous (Type q) K J))

/-- The canonical augmentation of the image of a simplicial formal coproduct: its target is
the terminal lifted presheaf, so the augmentation is unique. -/
private noncomputable def mappedAugmentation
    (K : SimplicialObject (FormalCoproduct.{w} C)) :
    associatedSimplicialPresheaf.{vC, w} K ⟶
      (SimplicialObject.const _).obj
        (liftedPresheaf.{vC, w} (⊤_ (Cᵒᵖ ⥤ Type vC))) := by
  let e : (Cᵒᵖ ⥤ Type vC) ⥤ (Cᵒᵖ ⥤ Type (max vC w vC)) :=
    (Functor.whiskeringRight Cᵒᵖ (Type vC) (Type (max vC w vC))).obj
      uliftFunctor.{max w vC, vC}
  have ht : IsTerminal (⊤_ (Cᵒᵖ ⥤ Type vC)) := terminalIsTerminal
  have ht' : IsTerminal (liftedPresheaf.{vC, w}
      (⊤_ (Cᵒᵖ ⥤ Type vC))) := by
    change IsTerminal (e.obj (⊤_ (Cᵒᵖ ⥤ Type vC)))
    exact ht.isTerminalObj e
  exact (Functor.isTerminalConst SimplexCategoryᵒᵖ ht').from _

/-- The underlying functor of a morphism of sites which preserves equalizers and pullbacks
carries a hypercovering to a hypercovering. -/
@[stacks 0DAY]
lemma exists_hypercovering_of_map
    [HasEqualizers C] [HasPullbacks C] [HasEqualizers D] [HasPullbacks D]
    (J : Pretopology C) (K : Pretopology D) (u : D ⥤ C)
    [IsMorphismOfSites.{max w vC vD uC uD} u K.toGrothendieck J.toGrothendieck]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [PreservesLimitsOfShape WalkingCospan u]
    (X : HypercoveringOfTerminal.{w} K) :
    ∃ Y : HypercoveringOfTerminal.{w} J,
      Y.toSimplicialObject = X.toSimplicialObject ⋙ mapFormalCoproduct u := by
  let K' := X.toSimplicialObject ⋙ mapFormalCoproduct u
  refine ⟨{
    toSimplicialObject := K'
    augmentation := mappedAugmentation K'
    locallySurjective_zero := by
      apply locallySurjective_of_coversTop J.toGrothendieck
        ((mapFormalCoproduct u).obj (X.toSimplicialObject.obj (op ⦋0⦌)))
        (terminalIsTerminal.isTerminalObj
          ((Functor.whiskeringRight _ _ _).obj uliftFunctor.{max w vC, vC}))
      apply coversTop_map J.toGrothendieck K.toGrothendieck u
      let := X.locallySurjective_zero
      exact coversTop_of_locallySurjective K.toGrothendieck
        (X.toSimplicialObject.obj (op ⦋0⦌))
        (terminalIsTerminal.isTerminalObj
          ((Functor.whiskeringRight _ _ _).obj uliftFunctor.{max w vD, vD}))
        (X.augmentation.app (op ⦋0⦌))
    locallySurjective_one := by
      let : PreservesLimitsOfShape (Discrete WalkingPair)
          (u.sheafPullback (Type (max w vC vD uC uD)) K.toGrothendieck J.toGrothendieck) :=
        preservesBinaryProducts_sheafPullback.{max w vC vD uC uD}
          J.toGrothendieck K.toGrothendieck u
      let := X.locallySurjective_one
      exact locallySurjective_one_map J.toGrothendieck K.toGrothendieck u
        X.toSimplicialObject _ _ X.augmentation (mappedAugmentation K')
        (terminalIsTerminal.isTerminalObj
          ((Functor.whiskeringRight _ _ _).obj uliftFunctor.{max w vD, vD}))
        (terminalIsTerminal.isTerminalObj
          ((Functor.whiskeringRight _ _ _).obj uliftFunctor.{max w vC, vC}))
    locallySurjective_succ := by
      intro n hn
      let := X.locallySurjective_succ n hn
      exact locallySurjective_higher_map J.toGrothendieck K.toGrothendieck u
        X.toSimplicialObject n hn
  }, ?_⟩
  rfl

end Stacks.CategoryTheory.Hypercovering

end
