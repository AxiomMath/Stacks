module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Coherence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Fullness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.StageRealization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageConstructibleSetSheafDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageFaithfulness
public import StacksFrontier.CategoryTheory.Sites.Continuous.PullbackCompSheafifiedYoneda
public import StacksCore.Tactic.StacksAttribute

/-!
# Maps of constructible sheaves of sets on a limit of schemes come from a finite stage

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms inside a big étale site. This file proves the fullness
assertion of Tag 09YU, clause (1) — every map between the inverse images to `X_étale` of two
constructible sheaves of sets at a stage comes from a map at a later stage — and with the
faithfulness and essential surjectivity assertions already in the library, the whole of
clause (1): the category of constructible sheaves of sets on `X_étale` is the colimit of the
categories of constructible sheaves of sets on the `(X_i)_étale`, in the elementwise form
`AlgebraicGeometry.SmallEtaleStagesColimit` in which the library states such colimits of
categories.

## The argument

The source reduces fullness, through Tag 09Y9, to sheaves represented by quasi-compact
quasi-separated étale objects. The reduction is carried out here for an arbitrary coefficient
category and an arbitrary class `P` of sheaves, as
`AlgebraicGeometry.SmallEtaleVertexHomLifts.of_generators`, from faithfulness, essential
surjectivity, closure of `P` under kernel pairs, cokernel pairs and inverse image, presentations
of `P`-sheaves as quotients of generators, and fullness for maps between generators:

* *descent along an epimorphism* (`AlgebraicGeometry.SmallEtaleVertexHomLifts.of_comp_epi`): a map
  out of the inverse image of `F` comes from a stage as soon as its composite with the inverse
  image of an epimorphism `E ⟶ F` does — at the stage of the witness the witness agrees on the
  kernel pair after inverse image to `X`, hence at a later stage by faithfulness, and there it
  descends along the regular epimorphism;
* *epimorphisms descend* (`AlgebraicGeometry.exists_epi_smallEtaleStageTransition_map`): the two
  legs of the cokernel pair agree on `X`, hence at a later stage;
* a map `a` from a generator into a `P`-sheaf `G` is pulled back along the inverse image of a
  presentation of `G`; the pullback is the inverse image of a `P`-sheaf at a stage by essential
  surjectivity, its projections come from a stage, the first is an epimorphism, and `a` descends
  along it.

For sheaves of sets the generators are the representables of quasi-compact quasi-separated étale
objects. Maps between them are morphisms of the small étale site, which come from a stage by
Tag 01ZC (`AlgebraicGeometry.exists_stage_smallEtaleBaseChange_hom`), and the comparison of
inverse images through two stages is, on representables, the representable of the comparison of
base changes (`CategoryTheory.Sheaf.sheafPullbackComp'_hom_app_sheafifiedYoneda`).

## Main results

* `AlgebraicGeometry.SmallEtaleVertexHomLifts` — a map between the inverse images to the vertex of
  sheaves at two stages comes from a common later stage; closed under composition, containing the
  inverse images of maps at a stage and the canonical comparisons.
* `AlgebraicGeometry.SmallEtaleVertexHomLifts.of_generators` — fullness from generators.
* `AlgebraicGeometry.exists_stage_smallEtaleBaseChange_hom` — morphisms between base changes to the
  limit of étale objects of a stage come from a stage.
* `AlgebraicGeometry.smallEtaleStagesFull_isConstructibleSetSheaf` — **Tag 09YU, clause (1), the
  fullness assertion.**
* `AlgebraicGeometry.smallEtaleStagesColimit_isConstructibleSetSheaf` — **Tag 09YU, clause (1).**

## References

* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
* [Stacks Project, Tag 09Y9](https://stacks.math.columbia.edu/tag/09Y9)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v iu u uw

namespace AlgebraicGeometry

section Calculus

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  {I : Type iu} [Preorder I] (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))
  (hX : B.Contains c.pt)

/-- The comparison of two successive transitions with the transition along the composite. -/
public abbrev smallEtaleStageTransitionComp {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    (F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A) :
    (smallEtaleStageTransition B A Dg hjk).obj ((smallEtaleStageTransition B A Dg hij).obj F) ≅
      (smallEtaleStageTransition B A Dg (hij.trans hjk)).obj F :=
  (smallEtaleSheafPullbackCompIso' B A (systemStageHom B Dg hjk) (systemStageHom B Dg hij)
    (systemStageHom B Dg (hij.trans hjk)) (systemStageHom_comp B Dg hij hjk)).app F

/-- **The cocycle law of the comparisons.** For `i ≤ j ≤ k`, comparing through `j` and then
from `j` to `i` is comparing along the composite transition. -/
@[reassoc]
public theorem smallEtaleStageComparison_trans {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    (F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A) :
    (smallEtaleStageComparison B A Dg c hX hjk
          ((smallEtaleStageTransition B A Dg hij).obj F)).hom ≫
        (smallEtaleStageComparison B A Dg c hX hij F).hom =
      (smallEtaleStageProjection B A Dg c hX k).map
          (smallEtaleStageTransitionComp B A Dg hij hjk F).hom ≫
        (smallEtaleStageComparison B A Dg c hX (hij.trans hjk) F).hom := by
  rw [smallEtaleStageComparison_eq, smallEtaleStageComparison_eq, smallEtaleStageComparison_eq]
  exact (smallEtaleSheafPullbackCompIso'_assoc B A (coneStageHom B Dg c hX k)
    (systemStageHom B Dg hjk) (systemStageHom B Dg hij) (coneStageHom B Dg c hX j)
    (systemStageHom B Dg (hij.trans hjk)) (coneStageHom B Dg c hX i)
    (coneStageHom_comp B Dg c hX hjk) (systemStageHom_comp B Dg hij hjk)
    (coneStageHom_comp B Dg c hX hij)
    (coneStageHom_comp B Dg c hX (hij.trans hjk)) F).symm

/-- The cocycle law, for the inverse comparisons. -/
@[reassoc]
public theorem smallEtaleStageComparison_trans_inv {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    (F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A) :
    (smallEtaleStageComparison B A Dg c hX (hij.trans hjk) F).inv ≫
        (smallEtaleStageProjection B A Dg c hX k).map
          (smallEtaleStageTransitionComp B A Dg hij hjk F).inv =
      (smallEtaleStageComparison B A Dg c hX hij F).inv ≫
        (smallEtaleStageComparison B A Dg c hX hjk
          ((smallEtaleStageTransition B A Dg hij).obj F)).inv := by
  have h := congrArg Iso.inv (Iso.ext (smallEtaleStageComparison_trans B A Dg c hX hij hjk F) :
    smallEtaleStageComparison B A Dg c hX hjk ((smallEtaleStageTransition B A Dg hij).obj F) ≪≫
        smallEtaleStageComparison B A Dg c hX hij F =
      (smallEtaleStageProjection B A Dg c hX k).mapIso
          (smallEtaleStageTransitionComp B A Dg hij hjk F) ≪≫
        smallEtaleStageComparison B A Dg c hX (hij.trans hjk) F)
  simpa using h.symm

/-- **A map between inverse images to the vertex comes from a stage.** For sheaves `F` at the
stage `i` and `G` at the stage `j`, a map `a` between their inverse images to the vertex comes
from a map `b` between their inverse images to a common later stage `k`, read through the
canonical comparisons. -/
public def SmallEtaleVertexHomLifts {i j : I}
    {F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    {G : Sheaf (SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property) A}
    (a : (smallEtaleStageProjection B A Dg c hX i).obj F ⟶
      (smallEtaleStageProjection B A Dg c hX j).obj G) : Prop :=
  ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k)
    (b : (smallEtaleStageTransition B A Dg hik).obj F ⟶
      (smallEtaleStageTransition B A Dg hjk).obj G),
    (smallEtaleStageComparison B A Dg c hX hik F).inv ≫
        (smallEtaleStageProjection B A Dg c hX k).map b ≫
        (smallEtaleStageComparison B A Dg c hX hjk G).hom = a

variable {B A Dg c hX}

/-- A witness read through the comparisons determines the inverse image of the witness. -/
private theorem smallEtaleStageProjection_map_eq_of_witness {i j k : I}
    {F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    {G : Sheaf (SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property) A}
    {a : (smallEtaleStageProjection B A Dg c hX i).obj F ⟶
      (smallEtaleStageProjection B A Dg c hX j).obj G}
    (hik : i ≤ k) (hjk : j ≤ k)
    {b : (smallEtaleStageTransition B A Dg hik).obj F ⟶
      (smallEtaleStageTransition B A Dg hjk).obj G}
    (hb : (smallEtaleStageComparison B A Dg c hX hik F).inv ≫
        (smallEtaleStageProjection B A Dg c hX k).map b ≫
        (smallEtaleStageComparison B A Dg c hX hjk G).hom = a) :
    (smallEtaleStageProjection B A Dg c hX k).map b =
      (smallEtaleStageComparison B A Dg c hX hik F).hom ≫ a ≫
        (smallEtaleStageComparison B A Dg c hX hjk G).inv := by
  rw [← hb]
  simp

/-- **Moving a witness to a later stage.** A witness `b` at the stage `k` gives the witness
`c⁻¹ ≫ b|_{k'} ≫ c` at every later stage `k'`, with `c` the comparison of two successive
transitions with the transition along the composite. -/
public theorem SmallEtaleVertexHomLifts.of_le_eq {i j k : I}
    {F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    {G : Sheaf (SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property) A}
    {a : (smallEtaleStageProjection B A Dg c hX i).obj F ⟶
      (smallEtaleStageProjection B A Dg c hX j).obj G}
    (hik : i ≤ k) (hjk : j ≤ k)
    (b : (smallEtaleStageTransition B A Dg hik).obj F ⟶
      (smallEtaleStageTransition B A Dg hjk).obj G)
    (hb : (smallEtaleStageComparison B A Dg c hX hik F).inv ≫
        (smallEtaleStageProjection B A Dg c hX k).map b ≫
        (smallEtaleStageComparison B A Dg c hX hjk G).hom = a)
    {k' : I} (hkk' : k ≤ k') :
    (smallEtaleStageComparison B A Dg c hX (hik.trans hkk') F).inv ≫
        (smallEtaleStageProjection B A Dg c hX k').map
          ((smallEtaleStageTransitionComp B A Dg hik hkk' F).inv ≫
            (smallEtaleStageTransition B A Dg hkk').map b ≫
            (smallEtaleStageTransitionComp B A Dg hjk hkk' G).hom) ≫
        (smallEtaleStageComparison B A Dg c hX (hjk.trans hkk') G).hom = a := by
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [smallEtaleStageComparison_trans_inv_assoc,
    ← smallEtaleStageComparison_trans B A Dg c hX hjk hkk' G,
    smallEtaleStageComparison_hom_naturality_assoc, Iso.inv_hom_id_assoc, hb]

/-- A witness at a stage gives a witness at every later stage. -/
public theorem SmallEtaleVertexHomLifts.of_le {i j k : I}
    {F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    {G : Sheaf (SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property) A}
    {a : (smallEtaleStageProjection B A Dg c hX i).obj F ⟶
      (smallEtaleStageProjection B A Dg c hX j).obj G}
    (hik : i ≤ k) (hjk : j ≤ k)
    (b : (smallEtaleStageTransition B A Dg hik).obj F ⟶
      (smallEtaleStageTransition B A Dg hjk).obj G)
    (hb : (smallEtaleStageComparison B A Dg c hX hik F).inv ≫
        (smallEtaleStageProjection B A Dg c hX k).map b ≫
        (smallEtaleStageComparison B A Dg c hX hjk G).hom = a)
    {k' : I} (hkk' : k ≤ k') :
    ∃ b' : (smallEtaleStageTransition B A Dg (hik.trans hkk')).obj F ⟶
        (smallEtaleStageTransition B A Dg (hjk.trans hkk')).obj G,
      (smallEtaleStageComparison B A Dg c hX (hik.trans hkk') F).inv ≫
        (smallEtaleStageProjection B A Dg c hX k').map b' ≫
        (smallEtaleStageComparison B A Dg c hX (hjk.trans hkk') G).hom = a :=
  ⟨_, SmallEtaleVertexHomLifts.of_le_eq hik hjk b hb hkk'⟩

/-- The inverse image to the vertex of a map at a stage comes from a stage. -/
public theorem smallEtaleVertexHomLifts_map {i : I}
    {F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    (x : F ⟶ G) :
    SmallEtaleVertexHomLifts B A Dg c hX ((smallEtaleStageProjection B A Dg c hX i).map x) :=
  ⟨i, le_rfl, le_rfl, (smallEtaleStageTransition B A Dg le_rfl).map x, by
    rw [smallEtaleStageComparison_hom_naturality, Iso.inv_hom_id_assoc]⟩

/-- The comparison from the inverse image of a transition comes from a stage. -/
public theorem smallEtaleVertexHomLifts_comparison_hom {i j : I} (h : i ≤ j)
    (F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A) :
    SmallEtaleVertexHomLifts B A Dg c hX (smallEtaleStageComparison B A Dg c hX h F).hom :=
  ⟨j, le_rfl, h, (smallEtaleStageTransitionComp B A Dg h le_rfl F).hom, by
    rw [Iso.inv_comp_eq, smallEtaleStageComparison_trans]⟩

/-- The comparison to the inverse image of a transition comes from a stage. -/
public theorem smallEtaleVertexHomLifts_comparison_inv {i j : I} (h : i ≤ j)
    (F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A) :
    SmallEtaleVertexHomLifts B A Dg c hX (smallEtaleStageComparison B A Dg c hX h F).inv :=
  ⟨j, h, le_rfl, (smallEtaleStageTransitionComp B A Dg h le_rfl F).inv, by
    rw [← Category.assoc, smallEtaleStageComparison_trans_inv, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]⟩

/-- **Maps coming from a stage are closed under composition**, over a directed index. -/
public theorem SmallEtaleVertexHomLifts.comp [IsDirected I (· ≤ ·)] {i j l : I}
    {F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    {G : Sheaf (SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property) A}
    {H : Sheaf (SmallEtale.topology B (Dg.obj (op l)).obj (Dg.obj (op l)).property) A}
    {a : (smallEtaleStageProjection B A Dg c hX i).obj F ⟶
      (smallEtaleStageProjection B A Dg c hX j).obj G}
    {a' : (smallEtaleStageProjection B A Dg c hX j).obj G ⟶
      (smallEtaleStageProjection B A Dg c hX l).obj H}
    (ha : SmallEtaleVertexHomLifts B A Dg c hX a) (ha' : SmallEtaleVertexHomLifts B A Dg c hX a') :
    SmallEtaleVertexHomLifts B A Dg c hX (a ≫ a') := by
  obtain ⟨k, hik, hjk, b, hb⟩ := ha
  obtain ⟨k', hjk', hlk', b', hb'⟩ := ha'
  obtain ⟨m, hkm, hk'm⟩ := directed_of (· ≤ ·) k k'
  obtain ⟨b₁, hb₁⟩ := SmallEtaleVertexHomLifts.of_le hik hjk b hb hkm
  obtain ⟨b₂, hb₂⟩ := SmallEtaleVertexHomLifts.of_le hjk' hlk' b' hb' hk'm
  refine ⟨m, hik.trans hkm, hlk'.trans hk'm, b₁ ≫ b₂, ?_⟩
  rw [← hb₁, ← hb₂, Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Maps coming from a stage are invariant under conjugation by isomorphisms at the stages. -/
public theorem SmallEtaleVertexHomLifts.of_conj_map [IsDirected I (· ≤ ·)] {i l : I}
    {E E' : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    {F F' : Sheaf (SmallEtale.topology B (Dg.obj (op l)).obj (Dg.obj (op l)).property) A}
    (α : E ≅ E') (β : F ≅ F')
    {a : (smallEtaleStageProjection B A Dg c hX i).obj E ⟶
      (smallEtaleStageProjection B A Dg c hX l).obj F}
    (h : SmallEtaleVertexHomLifts B A Dg c hX ((smallEtaleStageProjection B A Dg c hX i).map α.inv ≫
      a ≫ (smallEtaleStageProjection B A Dg c hX l).map β.hom)) :
    SmallEtaleVertexHomLifts B A Dg c hX a := by
  have ha : a = (smallEtaleStageProjection B A Dg c hX i).map α.hom ≫
      ((smallEtaleStageProjection B A Dg c hX i).map α.inv ≫ a ≫
        (smallEtaleStageProjection B A Dg c hX l).map β.hom) ≫
      (smallEtaleStageProjection B A Dg c hX l).map β.inv := by simp
  rw [ha]
  exact (smallEtaleVertexHomLifts_map α.hom).comp (h.comp (smallEtaleVertexHomLifts_map β.inv))

/-- Maps coming from a stage are invariant under conjugation by the comparisons. -/
public theorem SmallEtaleVertexHomLifts.of_conj_comparison [IsDirected I (· ≤ ·)] {i l m : I}
    (him : i ≤ m) (hlm : l ≤ m)
    {E : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    {F : Sheaf (SmallEtale.topology B (Dg.obj (op l)).obj (Dg.obj (op l)).property) A}
    {a : (smallEtaleStageProjection B A Dg c hX i).obj E ⟶
      (smallEtaleStageProjection B A Dg c hX l).obj F}
    (h : SmallEtaleVertexHomLifts B A Dg c hX ((smallEtaleStageComparison B A Dg c hX him E).hom ≫
      a ≫ (smallEtaleStageComparison B A Dg c hX hlm F).inv)) :
    SmallEtaleVertexHomLifts B A Dg c hX a := by
  have ha : a = (smallEtaleStageComparison B A Dg c hX him E).inv ≫
      ((smallEtaleStageComparison B A Dg c hX him E).hom ≫ a ≫
        (smallEtaleStageComparison B A Dg c hX hlm F).inv) ≫
      (smallEtaleStageComparison B A Dg c hX hlm F).hom := by simp
  rw [ha]
  exact (smallEtaleVertexHomLifts_comparison_inv him E).comp
    (h.comp (smallEtaleVertexHomLifts_comparison_hom hlm F))

end Calculus

/-- A morphism whose cokernel pair has equal legs is an epimorphism. -/
public theorem epi_of_isPushout_self {C : Type*} [Category* C] {X Y Z : C} {f : X ⟶ Y}
    {g : Y ⟶ Z} (h : IsPushout f f g g) : Epi f :=
  ⟨fun x y hxy => (h.inl_desc x y hxy).symm.trans (h.inr_desc x y hxy)⟩

section Descent

variable {B : BigEtaleSite.{u}} {A : Type t} [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  {I : Type iu} [Preorder I] [IsDirected I (· ≤ ·)] {Dg : Iᵒᵖ ⥤ B.Scheme}
  {c : Cone (Dg ⋙ B.inclusion)} {hX : B.Contains c.pt} {P : SmallEtaleSheafProperty B A}

/-- Inverse image along a transition preserves colimits, being a left adjoint. -/
public instance smallEtaleStageTransition_preservesColimitsOfSize {i j : I} (h : i ≤ j) :
    PreservesColimitsOfSize.{0, 0} (smallEtaleStageTransition B A Dg h) :=
  ((smallEtaleBaseChange B (Dg.map (homOfLE h).op)).sheafAdjunctionContinuous A
    (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    (SmallEtale.topology B (Dg.obj (op j)).obj
      (Dg.obj (op j)).property)).leftAdjoint_preservesColimits

/-- Inverse image to the vertex preserves epimorphisms, being a left adjoint. -/
public instance smallEtaleStageProjection_preservesEpimorphisms (i : I) :
    (smallEtaleStageProjection B A Dg c hX i).PreservesEpimorphisms :=
  haveI := ((smallEtaleBaseChange B (coneStageHom B Dg c hX i)).sheafAdjunctionContinuous A
    (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    (SmallEtale.topology B c.pt hX)).isLeftAdjoint
  inferInstance

/-- Inverse image along a transition preserves epimorphisms, being a left adjoint. -/
public instance smallEtaleStageTransition_preservesEpimorphisms {i j : I} (h : i ≤ j) :
    (smallEtaleStageTransition B A Dg h).PreservesEpimorphisms :=
  haveI := ((smallEtaleBaseChange B (Dg.map (homOfLE h).op)).sheafAdjunctionContinuous A
    (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    (SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property)).isLeftAdjoint
  inferInstance

omit [IsDirected I (· ≤ ·)] in
/-- **Epimorphisms descend to a stage.** For a property `P` of sheaves closed under cokernel
pairs and for which the comparison is faithful, a map of `P`-sheaves at a stage whose inverse
image to the vertex is an epimorphism becomes an epimorphism at a later stage: the two legs of
its cokernel pair agree after inverse image to the vertex, hence at a later stage, where they
are the legs of the cokernel pair of the inverse image. -/
public theorem exists_epi_smallEtaleStageTransition_map
    (hfaith : SmallEtaleStagesFaithful B A Dg c hX P)
    [∀ X : B.Scheme, HasPushouts (Sheaf (SmallEtale.topology B X.obj X.property) A)]
    (hPpo : ∀ (i : I) {E F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj
      (Dg.obj (op i)).property) A} (f : E ⟶ F), P _ E → P _ F → P _ (pushout f f))
    {i : I} {E F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    (f : E ⟶ F) (hE : P _ E) (hF : P _ F)
    [Epi ((smallEtaleStageProjection B A Dg c hX i).map f)] :
    ∃ (j : I) (h : i ≤ j), Epi ((smallEtaleStageTransition B A Dg h).map f) := by
  have hw : (smallEtaleStageProjection B A Dg c hX i).map (pushout.inl f f) =
      (smallEtaleStageProjection B A Dg c hX i).map (pushout.inr f f) := by
    rw [← cancel_epi ((smallEtaleStageProjection B A Dg c hX i).map f), ← Functor.map_comp,
      ← Functor.map_comp, pushout.condition]
  obtain ⟨j, h, hj⟩ := hfaith i F (pushout f f) hF (hPpo i f hE hF) _ _ hw
  refine ⟨j, h, epi_of_isPushout_self
    (g := (smallEtaleStageTransition B A Dg h).map (pushout.inr f f)) ?_⟩
  have hpo := (IsPushout.of_hasPushout f f).map (smallEtaleStageTransition B A Dg h)
  rw [hj] at hpo
  exact hpo

omit [IsDirected I (· ≤ ·)] in
/-- **Maps descend along an epimorphism.** Let `p : E ⟶ F` be an epimorphism of `P`-sheaves at a
stage, `P` closed under kernel pairs, inverse image and with faithful comparison. A map `a` out
of the inverse image of `F` to the vertex comes from a stage as soon as its composite with the
inverse image of `p` does.

At the stage of the witness `b` of that composite, `b` agrees on the two legs of the kernel pair
of `p` after inverse image to the vertex, hence at a later stage by faithfulness; there `p` is
still a regular epimorphism, inverse image preserving its coequalizer presentation, and `b`
descends along it. -/
public theorem SmallEtaleVertexHomLifts.of_comp_epi
    (hfaith : SmallEtaleStagesFaithful B A Dg c hX P)
    [∀ X : B.Scheme, HasPullbacks (Sheaf (SmallEtale.topology B X.obj X.property) A)]
    [∀ X : B.Scheme, IsRegularEpiCategory (Sheaf (SmallEtale.topology B X.obj X.property) A)]
    (hPpb : ∀ (i : I) {E F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj
      (Dg.obj (op i)).property) A} (f : E ⟶ F), P _ E → P _ F → P _ (pullback f f))
    (hPtr : ∀ {i j : I} (h : i ≤ j) (F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj
      (Dg.obj (op i)).property) A), P _ F → P _ ((smallEtaleStageTransition B A Dg h).obj F))
    {n l : I} {E F : Sheaf (SmallEtale.topology B (Dg.obj (op n)).obj (Dg.obj (op n)).property) A}
    {G : Sheaf (SmallEtale.topology B (Dg.obj (op l)).obj (Dg.obj (op l)).property) A}
    (p : E ⟶ F) [Epi p] (hE : P _ E) (hF : P _ F) (hG : P _ G)
    (a : (smallEtaleStageProjection B A Dg c hX n).obj F ⟶
      (smallEtaleStageProjection B A Dg c hX l).obj G)
    (ha : SmallEtaleVertexHomLifts B A Dg c hX
      ((smallEtaleStageProjection B A Dg c hX n).map p ≫ a)) :
    SmallEtaleVertexHomLifts B A Dg c hX a := by
  obtain ⟨m, hnm, hlm, b, hb⟩ := ha
  set pm := (smallEtaleStageTransition B A Dg hnm).map p with hpm
  have hK : P _ (pullback pm pm) := hPpb m pm (hPtr hnm E hE) (hPtr hnm F hF)
  have hb' := smallEtaleStageProjection_map_eq_of_witness hnm hlm hb
  have heq : (smallEtaleStageProjection B A Dg c hX m).map (pullback.fst pm pm ≫ b) =
      (smallEtaleStageProjection B A Dg c hX m).map (pullback.snd pm pm ≫ b) := by
    rw [Functor.map_comp, Functor.map_comp, hb', Category.assoc,
      ← smallEtaleStageComparison_hom_naturality_assoc, ← hpm,
      ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, pullback.condition]
  obtain ⟨m', hmm', hj⟩ := hfaith m (pullback pm pm) _ hK (hPtr hlm G hG) _ _ heq
  obtain ⟨⟨R⟩⟩ := IsRegularEpiCategory.regularEpiOfEpi pm
  set T := smallEtaleStageTransition B A Dg hmm'
  have hcol := isColimitCoforkMapOfIsColimit T R.w R.isColimit
  have hdesc : T.map R.left ≫ T.map b = T.map R.right ≫ T.map b := by
    calc T.map R.left ≫ T.map b =
          T.map (pullback.lift R.left R.right R.w) ≫ T.map (pullback.fst pm pm ≫ b) := by
            rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc,
              pullback.lift_fst R.left R.right R.w]
      _ = T.map (pullback.lift R.left R.right R.w) ≫ T.map (pullback.snd pm pm ≫ b) := by
            rw [hj]
      _ = T.map R.right ≫ T.map b := by
            rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc,
              pullback.lift_snd R.left R.right R.w]
  set b' := Cofork.IsColimit.desc hcol (T.map b) hdesc
  have hb'fac : T.map pm ≫ b' = T.map b := Cofork.IsColimit.π_desc hcol
  refine ⟨m', hnm.trans hmm', hlm.trans hmm',
    (smallEtaleStageTransitionComp B A Dg hnm hmm' F).inv ≫ b' ≫
      (smallEtaleStageTransitionComp B A Dg hlm hmm' G).hom, ?_⟩
  rw [← cancel_epi ((smallEtaleStageProjection B A Dg c hX n).map p), ← hb,
    smallEtaleStageComparison_inv_naturality_assoc]
  have hnat : (smallEtaleStageTransition B A Dg (hnm.trans hmm')).map p ≫
      (smallEtaleStageTransitionComp B A Dg hnm hmm' F).inv =
      (smallEtaleStageTransitionComp B A Dg hnm hmm' E).inv ≫
        T.map ((smallEtaleStageTransition B A Dg hnm).map p) :=
    (smallEtaleSheafPullbackCompIso' B A (systemStageHom B Dg hmm')
      (systemStageHom B Dg hnm) (systemStageHom B Dg (hnm.trans hmm'))
      (systemStageHom_comp B Dg hnm hmm')).inv.naturality p
  rw [← Functor.map_comp_assoc, reassoc_of% hnat, ← hpm, reassoc_of% hb'fac]
  simp only [Functor.map_comp, Category.assoc]
  rw [smallEtaleStageComparison_trans_inv_assoc,
    ← smallEtaleStageComparison_trans B A Dg c hX hlm hmm' G,
    smallEtaleStageComparison_hom_naturality_assoc, Iso.inv_hom_id_assoc]

/-- **Fullness from generators.** Let `P` be a property of sheaves for which the comparison is
faithful and essentially surjective, closed under kernel pairs, cokernel pairs and inverse image,
and let `Gen` be a class of `P`-sheaves — the generators — such that every `P`-sheaf at a stage is
a quotient of a generator and every map between the inverse images to the vertex of two
generators comes from a stage. Suppose further that the `P`-sheaves on the vertex are closed under
pullbacks and that epimorphisms of sheaves on the vertex are stable under pullback. Then every map
between the inverse images to the vertex of two `P`-sheaves comes from a stage.

This is the source's argument for the fullness assertion of Tag 09YU, with the generators the
representable sheaves of quasi-compact quasi-separated objects. A map `a` out of the inverse image
of a generator into that of a `P`-sheaf `G` is pulled back along the inverse image of a
presentation `q` of `G`; the pullback is a `P`-sheaf on the vertex, hence the inverse image of a
`P`-sheaf at a stage, and its two projections, maps into inverse images of generators, come from a
stage, through presentations of their source by generators and descent along those
presentations. The first projection is an epimorphism on the vertex, so it becomes one at a
stage, and `a` descends along it. The general case is then descent along a presentation of the
source. -/
public theorem SmallEtaleVertexHomLifts.of_generators
    [∀ X : B.Scheme, HasPullbacks (Sheaf (SmallEtale.topology B X.obj X.property) A)]
    [∀ X : B.Scheme, HasPushouts (Sheaf (SmallEtale.topology B X.obj X.property) A)]
    [∀ X : B.Scheme, IsRegularEpiCategory (Sheaf (SmallEtale.topology B X.obj X.property) A)]
    [HasPullbacks (Sheaf (SmallEtale.topology B c.pt hX) A)]
    {Gen : SmallEtaleSheafProperty B A}
    (hfaith : SmallEtaleStagesFaithful B A Dg c hX P)
    (hes : SmallEtaleStagesEssSurj B A Dg c hX P)
    (hGenP : ∀ (i : I) (F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj
      (Dg.obj (op i)).property) A), Gen _ F → P _ F)
    (hpres : ∀ (i : I) (F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj
      (Dg.obj (op i)).property) A), P _ F → ∃ (E : Sheaf (SmallEtale.topology B
        (Dg.obj (op i)).obj (Dg.obj (op i)).property) A) (p : E ⟶ F), Gen _ E ∧ Epi p)
    (hgen : ∀ {i l : I}
      (E : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A)
      (F : Sheaf (SmallEtale.topology B (Dg.obj (op l)).obj (Dg.obj (op l)).property) A),
      Gen _ E → Gen _ F → ∀ a : (smallEtaleStageProjection B A Dg c hX i).obj E ⟶
        (smallEtaleStageProjection B A Dg c hX l).obj F, SmallEtaleVertexHomLifts B A Dg c hX a)
    (hPtr : ∀ {i j : I} (h : i ≤ j) (F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj
      (Dg.obj (op i)).property) A), P _ F → P _ ((smallEtaleStageTransition B A Dg h).obj F))
    (hPproj : ∀ (i : I) (F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj
      (Dg.obj (op i)).property) A), P _ F →
        P (B.obj c.pt hX) ((smallEtaleStageProjection B A Dg c hX i).obj F))
    (hPpb : ∀ (i : I) {E F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj
      (Dg.obj (op i)).property) A} (f : E ⟶ F), P _ E → P _ F → P _ (pullback f f))
    (hPpo : ∀ (i : I) {E F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj
      (Dg.obj (op i)).property) A} (f : E ⟶ F), P _ E → P _ F → P _ (pushout f f))
    (hPvpb : ∀ {E F G : Sheaf (SmallEtale.topology B c.pt hX) A} (f : E ⟶ G) (g : F ⟶ G),
      P (B.obj c.pt hX) E → P (B.obj c.pt hX) F → P (B.obj c.pt hX) G →
        P (B.obj c.pt hX) (pullback f g))
    (hepi : ∀ {E F G : Sheaf (SmallEtale.topology B c.pt hX) A} (f : E ⟶ G) (g : F ⟶ G),
      Epi g → Epi (pullback.fst f g))
    {i l : I} (F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A)
    (G : Sheaf (SmallEtale.topology B (Dg.obj (op l)).obj (Dg.obj (op l)).property) A)
    (hF : P _ F) (hG : P _ G)
    (a : (smallEtaleStageProjection B A Dg c hX i).obj F ⟶
      (smallEtaleStageProjection B A Dg c hX l).obj G) :
    SmallEtaleVertexHomLifts B A Dg c hX a := by
  -- maps from a `P`-sheaf into a generator
  have hPG : ∀ {n l : I}
      (Q : Sheaf (SmallEtale.topology B (Dg.obj (op n)).obj (Dg.obj (op n)).property) A)
      (F : Sheaf (SmallEtale.topology B (Dg.obj (op l)).obj (Dg.obj (op l)).property) A),
      P _ Q → Gen _ F → ∀ a : (smallEtaleStageProjection B A Dg c hX n).obj Q ⟶
        (smallEtaleStageProjection B A Dg c hX l).obj F,
      SmallEtaleVertexHomLifts B A Dg c hX a := by
    intro n l Q F hQ hF a
    obtain ⟨E, p, hE, hp⟩ := hpres n Q hQ
    have := hp
    exact SmallEtaleVertexHomLifts.of_comp_epi hfaith hPpb hPtr p (hGenP _ E hE) hQ (hGenP _ F hF)
      a (hgen E F hE hF _)
  -- maps from a generator into a `P`-sheaf
  have hRS : ∀ {i l : I}
      (F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A)
      (G : Sheaf (SmallEtale.topology B (Dg.obj (op l)).obj (Dg.obj (op l)).property) A),
      Gen _ F → P _ G → ∀ a : (smallEtaleStageProjection B A Dg c hX i).obj F ⟶
        (smallEtaleStageProjection B A Dg c hX l).obj G,
      SmallEtaleVertexHomLifts B A Dg c hX a := by
    intro i l F G hF hG a
    obtain ⟨W, q, hW, hq⟩ := hpres l G hG
    have := hq
    have hQ : P _ (pullback a ((smallEtaleStageProjection B A Dg c hX l).map q)) :=
      hPvpb _ _ (hPproj i F (hGenP i F hF)) (hPproj l W (hGenP l W hW)) (hPproj l G hG)
    have : Epi (pullback.fst a ((smallEtaleStageProjection B A Dg c hX l).map q)) :=
      hepi _ _ inferInstance
    obtain ⟨k, Qk, hQk, ⟨e⟩⟩ := hes _ hQ
    have hβ := hPG Qk W hQk hW
      (e.hom ≫ pullback.snd a ((smallEtaleStageProjection B A Dg c hX l).map q))
    have hαa : SmallEtaleVertexHomLifts B A Dg c hX
        ((e.hom ≫ pullback.fst a ((smallEtaleStageProjection B A Dg c hX l).map q)) ≫ a) := by
      have hsq : (e.hom ≫ pullback.fst a ((smallEtaleStageProjection B A Dg c hX l).map q)) ≫ a =
          (e.hom ≫ pullback.snd a ((smallEtaleStageProjection B A Dg c hX l).map q)) ≫
            (smallEtaleStageProjection B A Dg c hX l).map q := by
        simp [pullback.condition]
      rw [hsq]
      exact hβ.comp (smallEtaleVertexHomLifts_map q)
    obtain ⟨n, hkn, hin, bα, hbα⟩ := hPG Qk F hQk hF
      (e.hom ≫ pullback.fst a ((smallEtaleStageProjection B A Dg c hX l).map q))
    have : Epi ((smallEtaleStageProjection B A Dg c hX n).map bα) := by
      rw [smallEtaleStageProjection_map_eq_of_witness hkn hin hbα]
      infer_instance
    obtain ⟨n', hnn', hepi'⟩ := exists_epi_smallEtaleStageTransition_map hfaith hPpo bα
      (hPtr hkn Qk hQk) (hPtr hin F (hGenP i F hF))
    have := hepi'
    have hp' := SmallEtaleVertexHomLifts.of_le_eq hkn hin bα hbα hnn'
    have key : SmallEtaleVertexHomLifts B A Dg c hX
        ((smallEtaleStageComparison B A Dg c hX (hin.trans hnn') F).hom ≫ a) := by
      refine SmallEtaleVertexHomLifts.of_comp_epi hfaith hPpb hPtr
        ((smallEtaleStageTransitionComp B A Dg hkn hnn' Qk).inv ≫
          (smallEtaleStageTransition B A Dg hnn').map bα ≫
          (smallEtaleStageTransitionComp B A Dg hin hnn' F).hom)
        (hPtr _ Qk hQk) (hPtr _ F (hGenP i F hF)) hG _ ?_
      have hcomp : (smallEtaleStageProjection B A Dg c hX n').map
            ((smallEtaleStageTransitionComp B A Dg hkn hnn' Qk).inv ≫
              (smallEtaleStageTransition B A Dg hnn').map bα ≫
              (smallEtaleStageTransitionComp B A Dg hin hnn' F).hom) ≫
            (smallEtaleStageComparison B A Dg c hX (hin.trans hnn') F).hom ≫ a =
          (smallEtaleStageComparison B A Dg c hX (hkn.trans hnn') Qk).hom ≫
            ((e.hom ≫ pullback.fst a ((smallEtaleStageProjection B A Dg c hX l).map q)) ≫ a) := by
        rw [← hp']
        simp
      rw [hcomp]
      exact (smallEtaleVertexHomLifts_comparison_hom _ Qk).comp hαa
    have ha : a = (smallEtaleStageComparison B A Dg c hX (hin.trans hnn') F).inv ≫
        ((smallEtaleStageComparison B A Dg c hX (hin.trans hnn') F).hom ≫ a) := by simp
    rw [ha]
    exact (smallEtaleVertexHomLifts_comparison_inv _ F).comp key
  obtain ⟨E, p, hE, hp⟩ := hpres i F hF
  have := hp
  exact SmallEtaleVertexHomLifts.of_comp_epi hfaith hPpb hPtr p (hGenP _ E hE) hF hG a
    (hRS E G hE hG _)

end Descent

/-- The base change square of an étale object along a morphism, on underlying schemes. -/
private theorem isPullback_inclusion_map_pullback (B : BigEtaleSite.{u}) {S T : B.Scheme}
    (f : T ⟶ S) (U : SmallEtale B S.obj S.property) :
    IsPullback (B.inclusion.map (pullback.fst U.obj.hom f))
      (B.inclusion.map (pullback.snd U.obj.hom f)) (B.inclusion.map U.obj.hom)
      (B.inclusion.map f) :=
  (IsPullback.of_hasPullback U.obj.hom f).map B.inclusion

section Representables

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

open Stacks.EtaleCohomology in
/-- **A morphism between base changes to the limit of two étale objects of a stage comes from a
later stage** (Tag 01ZC). Let `U` and `W` be objects of `(X_i)_étale` with `U` quasi-compact and
quasi-separated, and let `w : U_X ⟶ W_X` be a morphism between their base changes to the limit.
Then for some `j ≥ i` there is a morphism `ψ : U_j ⟶ W_j` between their base changes to `X_j`
whose base change to `X` is `w`, read through the comparison of the base change to `X` through
`X_j` with the base change to `X` directly. -/
public theorem exists_stage_smallEtaleBaseChange_hom (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) (i : I)
    (U W : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    (hUc : CompactSpace ((SmallEtale.toScheme B _ _).obj U))
    (hUq : QuasiSeparatedSpace ((SmallEtale.toScheme B _ _).obj U))
    (w₀ : (smallEtaleBaseChange B (coneStageHom B Dg c hX i)).obj U ⟶
      (smallEtaleBaseChange B (coneStageHom B Dg c hX i)).obj W) :
    ∃ (j : I) (h : i ≤ j) (ψ : (smallEtaleBaseChange B (systemStageHom B Dg h)).obj U ⟶
        (smallEtaleBaseChange B (systemStageHom B Dg h)).obj W),
      (smallEtaleBaseChange B (coneStageHom B Dg c hX j)).map ψ ≫
          (smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j)) (Dg.obj (op i))
            (coneStageHom B Dg c hX j) (systemStageHom B Dg h) (coneStageHom B Dg c hX i)
            (coneStageHom_comp B Dg c hX h)).hom.app W =
        (smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j)) (Dg.obj (op i))
            (coneStageHom B Dg c hX j) (systemStageHom B Dg h) (coneStageHom B Dg c hX i)
            (coneStageHom_comp B Dg c hX h)).hom.app U ≫ w₀ := by
  classical
  have : IsCofiltered Iᵒᵖ := inferInstance
  have haff' : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom ((Dg ⋙ B.inclusion).map e) :=
    fun e => haff e
  have hqc' : ∀ p : Iᵒᵖ, CompactSpace ((Dg ⋙ B.inclusion).obj p) := fun p => hqc p.unop
  have hqs' : ∀ p : Iᵒᵖ, QuasiSeparatedSpace ((Dg ⋙ B.inclusion).obj p) :=
    fun p => hqs p.unop
  have : Etale (B.inclusion.map W.obj.hom) := W.property
  have : CompactSpace (B.inclusion.obj U.obj.left) := hUc
  have : QuasiSeparatedSpace (B.inclusion.obj U.obj.left) := hUq
  set u := B.inclusion.map U.obj.hom with hu
  -- the base-change squares at the vertex
  have hsqU := isPullback_inclusion_map_pullback B (coneStageHom B Dg c hX i) U
  have hsqW := isPullback_inclusion_map_pullback B (coneStageHom B Dg c hX i) W
  set eU := hsqU.flip.isoPullback with heU
  -- the morphism to descend
  set w' : B.inclusion.obj (pullback U.obj.hom (coneStageHom B Dg c hX i)) ⟶
      B.inclusion.obj (pullback W.obj.hom (coneStageHom B Dg c hX i)) :=
    B.inclusion.map w₀.hom.left with hw'def
  have hw : w' ≫ B.inclusion.map (pullback.snd W.obj.hom (coneStageHom B Dg c hX i)) =
      B.inclusion.map (pullback.snd U.obj.hom (coneStageHom B Dg c hX i)) :=
    (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w w₀.hom))
  set φ : pullback (c.π.app (op i)) u ⟶ B.inclusion.obj W.obj.left :=
    eU.inv ≫ w' ≫ B.inclusion.map (pullback.fst W.obj.hom (coneStageHom B Dg c hX i)) with hφdef
  have hφ' : φ ≫ B.inclusion.map W.obj.hom = pullback.snd (c.π.app (op i)) u ≫ u := by
    rw [hφdef, Category.assoc, Category.assoc, hsqW.w, reassoc_of% hw, ← hsqU.w,
      ← Category.assoc]
    congr 1
    exact hsqU.flip.isoPullback_inv_snd
  have hφ : φ ≫ B.inclusion.map W.obj.hom =
      pullback.snd (c.π.app (op i)) u ≫ u ≫ 𝟙 ((Dg ⋙ B.inclusion).obj (op i)) :=
    hφ'.trans (congrArg (pullback.snd (c.π.app (op i)) u ≫ ·) (Category.comp_id u).symm)
  obtain ⟨k, e, ψs, hψw, hψc⟩ := exists_stage_hom_of_hom (Dg ⋙ B.inclusion) c hc (op i) u
    (𝟙 _) (B.inclusion.map W.obj.hom) φ hφ
  have hψw' : ψs ≫ B.inclusion.map W.obj.hom = pullback.snd _ u ≫ u :=
    hψw.trans (congrArg (pullback.snd _ u ≫ ·) (Category.comp_id u))
  set j : I := k.unop with hj
  have h : i ≤ j := leOfHom e.unop
  have he : e = (homOfLE h).op := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  subst he
  set t := systemStageHom B Dg h with ht
  set pj := coneStageHom B Dg c hX j with hpj
  -- the base-change squares at the stage
  have hsqUj := isPullback_inclusion_map_pullback B t U
  have hsqWj := isPullback_inclusion_map_pullback B t W
  set eUj := hsqUj.flip.isoPullback with heUj
  have hm : (eUj.hom ≫ ψs) ≫ B.inclusion.map W.obj.hom =
      B.inclusion.map (pullback.snd U.obj.hom t) ≫ B.inclusion.map t := by
    rw [Category.assoc, hψw', ← pullback.condition, ← Category.assoc]
    congr 1
    exact hsqUj.flip.isoPullback_hom_fst
  set m := hsqWj.lift (eUj.hom ≫ ψs) (B.inclusion.map (pullback.snd U.obj.hom t)) hm with hmdef
  have hmsnd : m ≫ B.inclusion.map (pullback.snd W.obj.hom t) =
      B.inclusion.map (pullback.snd U.obj.hom t) := hsqWj.lift_snd _ _ _
  have hmfst : m ≫ B.inclusion.map (pullback.fst W.obj.hom t) = eUj.hom ≫ ψs :=
    hsqWj.lift_fst _ _ _
  have hcone := coneStageHom_comp B Dg c hX h
  -- the comparison of the two base changes, on underlying schemes
  have hθ : ∀ V : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property,
      (SmallEtale.toScheme B c.pt hX).map
          ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j)) (Dg.obj (op i))
            pj t (coneStageHom B Dg c hX i) hcone).hom.app V) ≫
          B.inclusion.map (pullback.fst V.obj.hom (coneStageHom B Dg c hX i)) =
        B.inclusion.map (pullback.fst ((smallEtaleBaseChange B t).obj V).obj.hom pj) ≫
          B.inclusion.map (pullback.fst V.obj.hom t) := fun V =>
    (B.inclusion.map_comp _ _).symm.trans ((congrArg B.inclusion.map
      (smallEtaleBaseChange_factoredCompIso_hom_app_fst B _ _ _ pj t
        (coneStageHom B Dg c hX i) hcone V)).trans
        (B.inclusion.map_comp _ _))
  -- base change of a morphism, on underlying schemes
  have hbc : ∀ (V V' : SmallEtale B (Dg.obj (op j)).obj (Dg.obj (op j)).property) (g : V ⟶ V'),
      (SmallEtale.toScheme B c.pt hX).map ((smallEtaleBaseChange B pj).map g) ≫
          B.inclusion.map (pullback.fst V'.obj.hom pj) =
        B.inclusion.map (pullback.fst V.obj.hom pj) ≫
          (SmallEtale.toScheme B (Dg.obj (op j)).obj (Dg.obj (op j)).property).map g := by
    intro V V' g
    change B.inclusion.map (((Over.pullback pj).map g.hom).left) ≫
        B.inclusion.map (pullback.fst V'.obj.hom pj) =
      B.inclusion.map (pullback.fst V.obj.hom pj) ≫ B.inclusion.map g.hom.left
    rw [← B.inclusion.map_comp, ← B.inclusion.map_comp]
    refine congrArg B.inclusion.map ?_
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have hwφ : w' ≫ B.inclusion.map (pullback.fst W.obj.hom (coneStageHom B Dg c hX i)) =
      eU.hom ≫ stageBaseChangeComparison (Dg ⋙ B.inclusion) c (homOfLE h).op u ≫ ψs := by
    rw [hψc, hφdef, Iso.hom_inv_id_assoc]
  -- the key identity of the two comparisons into the descended fibre product
  have hkey : B.inclusion.map (pullback.fst ((smallEtaleBaseChange B t).obj U).obj.hom pj) ≫
        eUj.hom =
      (SmallEtale.toScheme B c.pt hX).map
          ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j)) (Dg.obj (op i))
            pj t (coneStageHom B Dg c hX i) hcone).hom.app U) ≫ eU.hom ≫
        stageBaseChangeComparison (Dg ⋙ B.inclusion) c (homOfLE h).op u := by
    set θU : B.inclusion.obj (pullback ((smallEtaleBaseChange B t).obj U).obj.hom pj) ⟶
        B.inclusion.obj (pullback U.obj.hom (coneStageHom B Dg c hX i)) :=
      (SmallEtale.toScheme B c.pt hX).map
        ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j))
          (Dg.obj (op i)) pj t (coneStageHom B Dg c hX i) hcone).hom.app U) with hθUdef
    have e3 : eU.hom ≫ pullback.fst (B.inclusion.map (coneStageHom B Dg c hX i)) u =
        B.inclusion.map (pullback.snd U.obj.hom (coneStageHom B Dg c hX i)) :=
      hsqU.flip.isoPullback_hom_fst
    have e3' : eU.hom ≫ pullback.snd (B.inclusion.map (coneStageHom B Dg c hX i)) u =
        B.inclusion.map (pullback.fst U.obj.hom (coneStageHom B Dg c hX i)) :=
      hsqU.flip.isoPullback_hom_snd
    apply pullback.hom_ext
    · have e4 : θU ≫ B.inclusion.map (pullback.snd U.obj.hom (coneStageHom B Dg c hX i)) =
          B.inclusion.map (pullback.snd ((smallEtaleBaseChange B t).obj U).obj.hom pj) :=
        toScheme_map_comp_hom B hX _
      have e5 : B.inclusion.map (pullback.snd ((smallEtaleBaseChange B t).obj U).obj.hom pj) ≫
          c.π.app (op j) =
          B.inclusion.map (pullback.fst ((smallEtaleBaseChange B t).obj U).obj.hom pj) ≫
            B.inclusion.map (pullback.snd U.obj.hom t) :=
        ((B.inclusion.map_comp _ _).symm.trans
          (congrArg B.inclusion.map pullback.condition.symm)).trans (B.inclusion.map_comp _ _)
      calc (B.inclusion.map (pullback.fst ((smallEtaleBaseChange B t).obj U).obj.hom pj) ≫
            eUj.hom) ≫ pullback.fst ((Dg ⋙ B.inclusion).map (homOfLE h).op) u
          = B.inclusion.map (pullback.fst ((smallEtaleBaseChange B t).obj U).obj.hom pj) ≫
            (eUj.hom ≫ pullback.fst ((Dg ⋙ B.inclusion).map (homOfLE h).op) u) :=
              Category.assoc _ _ _
        _ = B.inclusion.map (pullback.fst ((smallEtaleBaseChange B t).obj U).obj.hom pj) ≫
            B.inclusion.map (pullback.snd U.obj.hom t) :=
              congrArg _ hsqUj.flip.isoPullback_hom_fst
        _ = (θU ≫ B.inclusion.map (pullback.snd U.obj.hom (coneStageHom B Dg c hX i))) ≫
            c.π.app (op j) := by rw [e4, e5]
        _ = (θU ≫ eU.hom ≫ pullback.fst (B.inclusion.map (coneStageHom B Dg c hX i)) u) ≫
            c.π.app (op j) := by rw [e3]
        _ = (θU ≫ eU.hom ≫ stageBaseChangeComparison (Dg ⋙ B.inclusion) c (homOfLE h).op u) ≫
            pullback.fst ((Dg ⋙ B.inclusion).map (homOfLE h).op) u := by
              simp only [Category.assoc]
              rw [pullback.lift_fst]
              rfl
    · calc (B.inclusion.map (pullback.fst ((smallEtaleBaseChange B t).obj U).obj.hom pj) ≫
            eUj.hom) ≫ pullback.snd ((Dg ⋙ B.inclusion).map (homOfLE h).op) u
          = B.inclusion.map (pullback.fst ((smallEtaleBaseChange B t).obj U).obj.hom pj) ≫
            (eUj.hom ≫ pullback.snd ((Dg ⋙ B.inclusion).map (homOfLE h).op) u) :=
              Category.assoc _ _ _
        _ = B.inclusion.map (pullback.fst ((smallEtaleBaseChange B t).obj U).obj.hom pj) ≫
            B.inclusion.map (pullback.fst U.obj.hom t) :=
              congrArg _ hsqUj.flip.isoPullback_hom_snd
        _ = θU ≫ B.inclusion.map (pullback.fst U.obj.hom (coneStageHom B Dg c hX i)) :=
              (hθ U).symm
        _ = θU ≫ eU.hom ≫ pullback.snd (B.inclusion.map (coneStageHom B Dg c hX i)) u := by
              rw [e3']
        _ = (θU ≫ eU.hom ≫ stageBaseChangeComparison (Dg ⋙ B.inclusion) c (homOfLE h).op u) ≫
            pullback.snd ((Dg ⋙ B.inclusion).map (homOfLE h).op) u := by
              simp only [Category.assoc]
              rw [pullback.lift_snd]
              rfl
  refine ⟨j, h, mkHom B (Dg.obj (op j)).property
    (V := (smallEtaleBaseChange B t).obj U) (W := (smallEtaleBaseChange B t).obj W) m hmsnd, ?_⟩
  refine Stacks.EtaleCohomology.hom_ext B hX (hsqW.hom_ext ?_ ?_)
  · rw [Functor.map_comp, Functor.map_comp]
    set θU' : B.inclusion.obj (pullback ((smallEtaleBaseChange B t).obj U).obj.hom pj) ⟶
        B.inclusion.obj (pullback U.obj.hom (coneStageHom B Dg c hX i)) :=
      (SmallEtale.toScheme B c.pt hX).map
          ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j))
            (Dg.obj (op i)) pj t (coneStageHom B Dg c hX i) hcone).hom.app U) with hθU'
    set θW' : B.inclusion.obj (pullback ((smallEtaleBaseChange B t).obj W).obj.hom pj) ⟶
        B.inclusion.obj (pullback W.obj.hom (coneStageHom B Dg c hX i)) :=
      (SmallEtale.toScheme B c.pt hX).map
          ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j))
            (Dg.obj (op i)) pj t (coneStageHom B Dg c hX i) hcone).hom.app W) with hθW'
    set ψ' : B.inclusion.obj (pullback ((smallEtaleBaseChange B t).obj U).obj.hom pj) ⟶
        B.inclusion.obj (pullback ((smallEtaleBaseChange B t).obj W).obj.hom pj) :=
      (SmallEtale.toScheme B c.pt hX).map ((smallEtaleBaseChange B pj).map
        (mkHom B (Dg.obj (op j)).property (V := (smallEtaleBaseChange B t).obj U)
          (W := (smallEtaleBaseChange B t).obj W) m hmsnd)) with hψ'
    have hψfst : ψ' ≫ B.inclusion.map (pullback.fst ((smallEtaleBaseChange B t).obj W).obj.hom pj) =
        B.inclusion.map (pullback.fst ((smallEtaleBaseChange B t).obj U).obj.hom pj) ≫ m :=
      hbc _ _ _
    have hθW : θW' ≫ B.inclusion.map (pullback.fst W.obj.hom (coneStageHom B Dg c hX i)) =
        B.inclusion.map (pullback.fst ((smallEtaleBaseChange B t).obj W).obj.hom pj) ≫
          B.inclusion.map (pullback.fst W.obj.hom t) := hθ W
    change (ψ' ≫ θW') ≫ B.inclusion.map (pullback.fst W.obj.hom (coneStageHom B Dg c hX i)) =
      (θU' ≫ w') ≫ B.inclusion.map (pullback.fst W.obj.hom (coneStageHom B Dg c hX i))
    rw [Category.assoc, Category.assoc, hθW, reassoc_of% hψfst]
    calc (B.inclusion.map (pullback.fst ((smallEtaleBaseChange B t).obj U).obj.hom pj) ≫ m) ≫
          B.inclusion.map (pullback.fst W.obj.hom t)
        = B.inclusion.map (pullback.fst ((smallEtaleBaseChange B t).obj U).obj.hom pj) ≫
            (m ≫ B.inclusion.map (pullback.fst W.obj.hom t)) := Category.assoc _ _ _
      _ = B.inclusion.map (pullback.fst ((smallEtaleBaseChange B t).obj U).obj.hom pj) ≫
            (eUj.hom ≫ ψs) := congrArg _ hmfst
      _ = (B.inclusion.map (pullback.fst ((smallEtaleBaseChange B t).obj U).obj.hom pj) ≫
            eUj.hom) ≫ ψs := (Category.assoc _ _ _).symm
      _ = (θU' ≫ eU.hom ≫ stageBaseChangeComparison (Dg ⋙ B.inclusion) c (homOfLE h).op u) ≫
            ψs := congrArg (· ≫ ψs) hkey
      _ = θU' ≫ (eU.hom ≫ stageBaseChangeComparison (Dg ⋙ B.inclusion) c (homOfLE h).op u ≫
            ψs) := by simp only [Category.assoc]
      _ = θU' ≫ w' ≫ B.inclusion.map (pullback.fst W.obj.hom (coneStageHom B Dg c hX i)) :=
            congrArg _ hwφ.symm
  · exact (toScheme_map_comp_hom B hX _).trans (toScheme_map_comp_hom B hX _).symm

end Representables

/-- **Epimorphisms of sheaves of sets are stable under pullback.** An epimorphism of sheaves of
sets is locally surjective, and a local lift of the image of a section gives, together with the
restriction of the section, a local section of the pullback. -/
public theorem epi_pullback_fst_sheaf_of_epi {C : Type*} [Category* C]
    {J : GrothendieckTopology C} [HasSheafify J (Type uw)]
    {E F G : Sheaf J (Type uw)} (f : E ⟶ G) (g : F ⟶ G) [HasPullback f g] [Epi g] :
    Epi (pullback.fst f g) := by
  have hg : Sheaf.IsLocallySurjective g := (Sheaf.isLocallySurjective_iff_epi g).2 inferInstance
  refine (Sheaf.isLocallySurjective_iff_epi (pullback.fst f g)).1 ⟨fun {U} x => ?_⟩
  refine J.superset_covering ?_ (Presheaf.imageSieve_mem J g.hom (f.hom.app (op U) x))
  rintro V h ⟨y, hy⟩
  have hsq := (IsPullback.of_hasPullback f g).map
    (sheafToPresheaf J (Type uw) ⋙ (evaluation Cᵒᵖ (Type uw)).obj (op V))
  obtain ⟨z, hz, -⟩ := Types.exists_of_isPullback hsq (E.obj.map h.op x) y (by
    change f.hom.app (op V) (E.obj.map h.op x) = g.hom.app (op V) y
    rw [hy]
    exact NatTrans.naturality_apply f.hom h.op x)
  exact ⟨z, hz⟩

section Sets

variable (B : BigEtaleSite.{u})

/-- The base change of a quasi-compact quasi-separated étale object along a morphism to a
quasi-compact quasi-separated scheme is again quasi-compact and quasi-separated. -/
public theorem isQCQSEtaleObject_smallEtaleBaseChange {S T : B.Scheme} (f : T ⟶ S)
    [QuasiSeparatedSpace S.obj] [CompactSpace T.obj] [QuasiSeparatedSpace T.obj]
    (U : SmallEtale B S.obj S.property) (hU : IsQCQSEtaleObject B S U) :
    IsQCQSEtaleObject B T ((smallEtaleBaseChange B f).obj U) := by
  obtain ⟨hUc, hUq⟩ := hU
  have : CompactSpace (B.inclusion.obj U.obj.left) := hUc
  have : QuasiSeparatedSpace (B.inclusion.obj U.obj.left) := hUq
  have : QuasiSeparatedSpace (B.inclusion.obj S) := ‹QuasiSeparatedSpace S.obj›
  have hsq := isPullback_inclusion_map_pullback B f U
  have : QuasiCompact (B.inclusion.map U.obj.hom) := quasiCompact_of_compactSpace _
  have : QuasiSeparated (B.inclusion.map U.obj.hom) := QuasiSeparated.of_quasiSeparatedSpace _
  have : QuasiCompact (B.inclusion.map (pullback.snd U.obj.hom f)) :=
    MorphismProperty.of_isPullback hsq ‹_›
  have : QuasiSeparated (B.inclusion.map (pullback.snd U.obj.hom f)) :=
    MorphismProperty.of_isPullback hsq ‹_›
  have : CompactSpace (B.inclusion.obj T) := ‹CompactSpace T.obj›
  have : QuasiSeparatedSpace (B.inclusion.obj T) := ‹QuasiSeparatedSpace T.obj›
  have hC : CompactSpace (B.inclusion.obj (pullback U.obj.hom f)) :=
    QuasiCompact.compactSpace_of_compactSpace (B.inclusion.map (pullback.snd U.obj.hom f))
  have hQ : QuasiSeparatedSpace (B.inclusion.obj (pullback U.obj.hom f)) :=
    quasiSeparatedSpace_of_quasiSeparated (B.inclusion.map (pullback.snd U.obj.hom f))
  exact ⟨hC, hQ⟩

/-- A pullback of constructible sheaves of sets is constructible (Tag 03RZ (1)). -/
public theorem isConstructibleSetSheaf_pullback_of_cospan (X : B.Scheme)
    {E F G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))} (f : E ⟶ G)
    (g : F ⟶ G) (hE : IsConstructibleSetSheaf B X E) (hF : IsConstructibleSetSheaf B X F)
    (hG : IsConstructibleSetSheaf B X G) : IsConstructibleSetSheaf B X (pullback f g) :=
  isConstructibleSetSheaf_congr B _
    (limit.isoLimitCone ⟨PullbackCone.mk (pullback.fst f g) (pullback.snd f g)
      pullback.condition, pullbackIsPullback f g⟩)
    (isConstructibleSetSheaf_limit B _ (cospan f g) (by rintro (_ | _ | _) <;> assumption))

/-- A pushout of constructible sheaves of sets is constructible (Tag 03RZ (1)). -/
public theorem isConstructibleSetSheaf_pushout_of_span (X : B.Scheme)
    {E F G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))} (f : E ⟶ F)
    (g : E ⟶ G) (hE : IsConstructibleSetSheaf B X E) (hF : IsConstructibleSetSheaf B X F)
    (hG : IsConstructibleSetSheaf B X G) : IsConstructibleSetSheaf B X (pushout f g) :=
  let : HasFiniteColimits (Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :=
    CategoryTheory.Sheaf.instHasFiniteColimits
  isConstructibleSetSheaf_congr B _
    (colimit.isoColimitCocone ⟨PushoutCocone.mk (pushout.inl f g) (pushout.inr f g)
      pushout.condition, pushoutIsPushout f g⟩)
    (isConstructibleSetSheaf_colimit B _ (span f g) (by rintro (_ | _ | _) <;> assumption))

/-- A sheaf of sets isomorphic to the sheaf represented by a quasi-compact and quasi-separated
object of the small étale site. These are the generators of the constructible sheaves of sets
(Tag 09Y9). -/
public def IsQCQSRepresentableSetSheaf : SmallEtaleSheafProperty B (Type (u + 1)) :=
  fun X F => ∃ U : SmallEtale B X.obj X.property, IsQCQSEtaleObject B X U ∧
    Nonempty (F ≅ (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj U)

variable [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- Inverse image of the sheaf represented by an étale object is the sheaf represented by its
base change (Stacks 04D3), as an isomorphism of sheaves of sets on small étale sites. -/
public abbrev smallEtaleSheafifiedYonedaPullbackIso {S T : B.Scheme} (f : T ⟶ S)
    (V : SmallEtale B S.obj S.property) :
    (smallEtaleSheafPullback B (Type (u + 1)) f).obj
        ((Sheaf.sheafifiedYoneda (SmallEtale.topology B S.obj S.property)).obj V) ≅
      (Sheaf.sheafifiedYoneda (SmallEtale.topology B T.obj T.property)).obj
        ((smallEtaleBaseChange B f).obj V) :=
  Sheaf.sheafPullbackSheafifiedYonedaIso (smallEtaleBaseChange B f)
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property) V

/-- Naturality of `AlgebraicGeometry.smallEtaleSheafifiedYonedaPullbackIso` in the object. -/
@[reassoc]
public theorem smallEtaleSheafifiedYonedaPullbackIso_hom_naturality {S T : B.Scheme}
    (f : T ⟶ S) {V V' : SmallEtale B S.obj S.property} (g : V ⟶ V') :
    (smallEtaleSheafPullback B (Type (u + 1)) f).map
        ((Sheaf.sheafifiedYoneda (SmallEtale.topology B S.obj S.property)).map g) ≫
      (smallEtaleSheafifiedYonedaPullbackIso B f V').hom =
    (smallEtaleSheafifiedYonedaPullbackIso B f V).hom ≫
      (Sheaf.sheafifiedYoneda (SmallEtale.topology B T.obj T.property)).map
        ((smallEtaleBaseChange B f).map g) :=
  (Sheaf.sheafPullbackCompSheafifiedYonedaIso (smallEtaleBaseChange B f) _ _).hom.naturality g

/-- **Maps between representable sheaves come from a stage.** For quasi-compact and
quasi-separated objects `U` and `W` of `(X_i)_étale`, every map between the inverse images to the
vertex of the sheaves they represent comes from a stage. The map is a morphism `U_X ⟶ W_X` of the
small étale site of the vertex, which comes from a stage by
`AlgebraicGeometry.exists_stage_smallEtaleBaseChange_hom`, and the comparisons of inverse images
are, on representable sheaves, the representables of the comparisons of base changes by
`CategoryTheory.Sheaf.sheafPullbackComp'_hom_app_sheafifiedYoneda`. -/
public theorem smallEtaleVertexHomLifts_sheafifiedYoneda (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) (i : I)
    (U W : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    (hU : IsQCQSEtaleObject B (Dg.obj (op i)) U)
    (a : (smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj
        ((Sheaf.sheafifiedYoneda (SmallEtale.topology B (Dg.obj (op i)).obj
          (Dg.obj (op i)).property)).obj U) ⟶
      (smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj
        ((Sheaf.sheafifiedYoneda (SmallEtale.topology B (Dg.obj (op i)).obj
          (Dg.obj (op i)).property)).obj W)) :
    SmallEtaleVertexHomLifts B (Type (u + 1)) Dg c hX a := by
  have : (SmallEtale.topology B c.pt hX).Subcanonical :=
    AlgebraicGeometry.smallEtaleTopology_subcanonical' B (B.obj c.pt hX)
  have hff := Sheaf.fullyFaithfulSheafifiedYoneda (SmallEtale.topology B c.pt hX)
  set a' := (smallEtaleSheafifiedYonedaPullbackIso B (coneStageHom B Dg c hX i) U).inv ≫ a ≫
    (smallEtaleSheafifiedYonedaPullbackIso B (coneStageHom B Dg c hX i) W).hom with ha'
  have hw := hff.map_preimage a'
  obtain ⟨j, h, ψ, hψ⟩ := exists_stage_smallEtaleBaseChange_hom B Dg c hX hc haff hqc hqs i U W
    hU.1 hU.2 (hff.preimage a')
  have hK : ∀ V : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property,
      (smallEtaleStageComparison B (Type (u + 1)) Dg c hX h
          ((Sheaf.sheafifiedYoneda (SmallEtale.topology B (Dg.obj (op i)).obj
            (Dg.obj (op i)).property)).obj V)).hom =
        (smallEtaleStageProjection B (Type (u + 1)) Dg c hX j).map
            (smallEtaleSheafifiedYonedaPullbackIso B (systemStageHom B Dg h) V).hom ≫
          (smallEtaleSheafifiedYonedaPullbackIso B (coneStageHom B Dg c hX j)
            ((smallEtaleBaseChange B (systemStageHom B Dg h)).obj V)).hom ≫
          (Sheaf.sheafifiedYoneda (SmallEtale.topology B c.pt hX)).map
            ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j))
              (Dg.obj (op i)) (coneStageHom B Dg c hX j) (systemStageHom B Dg h)
              (coneStageHom B Dg c hX i)
              (coneStageHom_comp B Dg c hX h)).hom.app V) ≫
          (smallEtaleSheafifiedYonedaPullbackIso B (coneStageHom B Dg c hX i) V).inv := by
    intro V
    rw [smallEtaleStageComparison_eq, smallEtaleSheafPullbackCompIso'_eq]
    exact Sheaf.sheafPullbackComp'_hom_app_sheafifiedYoneda _ _ _ _ V
  refine ⟨j, h, h, (smallEtaleSheafifiedYonedaPullbackIso B (systemStageHom B Dg h) U).hom ≫
    (Sheaf.sheafifiedYoneda (SmallEtale.topology B (Dg.obj (op j)).obj
      (Dg.obj (op j)).property)).map ψ ≫
      (smallEtaleSheafifiedYonedaPullbackIso B (systemStageHom B Dg h) W).inv, ?_⟩
  rw [Iso.inv_comp_eq, hK U, hK W, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_map_assoc]
  congr 1
  have hn := smallEtaleSheafifiedYonedaPullbackIso_hom_naturality B (coneStageHom B Dg c hX j) ψ
  have h2 : (Sheaf.sheafifiedYoneda (SmallEtale.topology B c.pt hX)).map
        ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).map ψ) ≫
      (Sheaf.sheafifiedYoneda (SmallEtale.topology B c.pt hX)).map
        ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j))
          (Dg.obj (op i)) (coneStageHom B Dg c hX j) (systemStageHom B Dg h)
          (coneStageHom B Dg c hX i) (coneStageHom_comp B Dg c hX h)).hom.app W) =
      (Sheaf.sheafifiedYoneda (SmallEtale.topology B c.pt hX)).map
        ((smallEtaleBaseChange_factoredCompIso B (B.obj c.pt hX) (Dg.obj (op j))
          (Dg.obj (op i)) (coneStageHom B Dg c hX j) (systemStageHom B Dg h)
          (coneStageHom B Dg c hX i) (coneStageHom_comp B Dg c hX h)).hom.app U) ≫ a' := by
    rw [← Functor.map_comp, hψ, Functor.map_comp, hw]
  rw [reassoc_of% hn, reassoc_of% h2, ha']
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **Maps between generators come from a stage.** Maps between the inverse images to the vertex
of two sheaves isomorphic to representables of quasi-compact quasi-separated étale objects, at
two possibly different stages, come from a stage: after moving both to a common later stage,
where they are again such representables, this is
`AlgebraicGeometry.smallEtaleVertexHomLifts_sheafifiedYoneda`. -/
public theorem smallEtaleVertexHomLifts_isQCQSRepresentableSetSheaf (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) {i l : I}
    (E : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) (Type (u + 1)))
    (F : Sheaf (SmallEtale.topology B (Dg.obj (op l)).obj (Dg.obj (op l)).property) (Type (u + 1)))
    (hE : IsQCQSRepresentableSetSheaf B _ E) (hF : IsQCQSRepresentableSetSheaf B _ F)
    (a : (smallEtaleStageProjection B (Type (u + 1)) Dg c hX i).obj E ⟶
      (smallEtaleStageProjection B (Type (u + 1)) Dg c hX l).obj F) :
    SmallEtaleVertexHomLifts B (Type (u + 1)) Dg c hX a := by
  obtain ⟨U, hU, ⟨eE⟩⟩ := hE
  obtain ⟨W, hW, ⟨eF⟩⟩ := hF
  obtain ⟨m, him, hlm⟩ := directed_of (· ≤ ·) i l
  have : CompactSpace (Dg.obj (op m)).obj := hqc m
  have : QuasiSeparatedSpace (Dg.obj (op m)).obj := hqs m
  have : QuasiSeparatedSpace (Dg.obj (op i)).obj := hqs i
  refine SmallEtaleVertexHomLifts.of_conj_map eE eF
    (SmallEtaleVertexHomLifts.of_conj_comparison him hlm
      (SmallEtaleVertexHomLifts.of_conj_map
        (smallEtaleSheafifiedYonedaPullbackIso B (systemStageHom B Dg him) U)
        (smallEtaleSheafifiedYonedaPullbackIso B (systemStageHom B Dg hlm) W) ?_))
  exact smallEtaleVertexHomLifts_sheafifiedYoneda B Dg c hX hc haff hqc hqs m _ _
    (isQCQSEtaleObject_smallEtaleBaseChange B _ U hU) _

/-- **Stacks 09YU, clause (1), the fullness assertion.** Let `X = lim X_i` be the limit of a
directed inverse system of quasi-compact and quasi-separated schemes with affine transition
morphisms inside a big étale site. Every map between the inverse images to `X_étale` of two
constructible sheaves of sets on `(X_i)_étale` is the inverse image of a map between their
inverse images to some later stage, read through the canonical comparisons. -/
public theorem smallEtaleStagesFull_isConstructibleSetSheaf (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesFull B (Type (u + 1)) Dg c hX (fun X => IsConstructibleSetSheaf B X) := by
  have : ∀ X : B.Scheme,
      HasPushouts (Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) := fun X => by
    let : HasFiniteColimits (Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :=
      CategoryTheory.Sheaf.instHasFiniteColimits
    infer_instance
  have : ∀ X : B.Scheme,
      HasPullbacks (Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :=
    fun X => inferInstance
  have : ∀ X : B.Scheme,
      IsRegularEpiCategory (Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :=
    fun X => inferInstance
  intro i F G hF hG a
  obtain ⟨k, hik, hik', b, hb⟩ := SmallEtaleVertexHomLifts.of_generators
    (Gen := IsQCQSRepresentableSetSheaf B)
    (smallEtaleStagesFaithful_isConstructibleSetSheaf B Dg c hX hc haff hqc hqs)
    (smallEtaleStagesEssSurj_isConstructibleSetSheaf B Dg c hX hc haff hqc hqs)
    (fun i F ⟨U, hU, ⟨e⟩⟩ => by
      have : CompactSpace (Dg.obj (op i)).obj := hqc i
      have : QuasiSeparatedSpace (Dg.obj (op i)).obj := hqs i
      have : CompactSpace U.obj.left.obj := hU.1
      have : QuasiSeparatedSpace U.obj.left.obj := hU.2
      exact isConstructibleSetSheaf_congr B _ e.symm
        (isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs B _ U))
    (fun i F hF => by
      have : CompactSpace (Dg.obj (op i)).obj := hqc i
      have : QuasiSeparatedSpace (Dg.obj (op i)).obj := hqs i
      let : HasFiniteColimits (Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj
          (Dg.obj (op i)).property) (Type (u + 1))) :=
        CategoryTheory.Sheaf.instHasFiniteColimits
      obtain ⟨n, m, Ufam, Vfam, hUfam, hVfam, f, g, ⟨co⟩⟩ :=
        (isConstructibleSetSheaf_iff_hasFiniteQCSRepresentableCoequalizerPresentation_unconditional
          B (Dg.obj (op i)) F).mp hF
      have : ∀ p : ℕ, HasColimitsOfShape (Discrete (Fin p)) (Sheaf (SmallEtale.topology B
          (Dg.obj (op i)).obj (Dg.obj (op i)).property) (Type (u + 1))) :=
        fun _ => HasFiniteColimits.out _
      have : HasColimitsOfShape WalkingParallelPair (Sheaf (SmallEtale.topology B
          (Dg.obj (op i)).obj (Dg.obj (op i)).property) (Type (u + 1))) := HasFiniteColimits.out _
      have : ∀ k, CompactSpace ((SmallEtale.toScheme B _ _).obj (Ufam k)) := fun k => (hUfam k).1
      have : ∀ k, QuasiSeparatedSpace ((SmallEtale.toScheme B _ _).obj (Ufam k)) :=
        fun k => (hUfam k).2
      refine ⟨_, (Stacks.EtaleCohomology.sigmaSheafifiedYonedaIsoDisjointUnion B _ Ufam).inv ≫
        coequalizer.π f g ≫ co.hom,
        ⟨Stacks.EtaleCohomology.disjointUnionObj B _ Ufam,
          ⟨compactSpace_sigmaObj _, quasiSeparatedSpace_sigmaObj _⟩, ⟨Iso.refl _⟩⟩, ?_⟩
      infer_instance)
    (fun E F hE hF a =>
      smallEtaleVertexHomLifts_isQCQSRepresentableSetSheaf B Dg c hX hc haff hqc hqs E F hE hF a)
    (fun h F hF => isConstructibleFiniteSheaf_pullback B _ F hF)
    (fun i F hF => isConstructibleFiniteSheaf_pullback B _ F hF)
    (fun i E F f hE hF => isConstructibleSetSheaf_pullback_of_cospan B _ f f hE hE hF)
    (fun i E F f hE hF => isConstructibleSetSheaf_pushout_of_span B _ f f hE hF hF)
    (fun f g hE hF hG => isConstructibleSetSheaf_pullback_of_cospan B (B.obj c.pt hX) f g hE hF hG)
    (fun f g hg => by have := hg; exact epi_pullback_fst_sheaf_of_epi f g)
    F G hF hG a
  exact ⟨k, hik, b, hb⟩

/-- **Stacks 09YU, clause (1).** Let `X = lim X_i` be the limit of a directed inverse system of
quasi-compact and quasi-separated schemes with affine transition morphisms inside a big étale
site. The category of constructible sheaves of sets on `X_étale` is the colimit of the categories
of constructible sheaves of sets on the `(X_i)_étale`, along étale inverse image: the comparison
is faithful (`AlgebraicGeometry.smallEtaleStagesFaithful_isConstructibleSetSheaf`), full
(`AlgebraicGeometry.smallEtaleStagesFull_isConstructibleSetSheaf`) and essentially surjective
(`AlgebraicGeometry.smallEtaleStagesEssSurj_isConstructibleSetSheaf`), which over a directed index
is the assertion that the category on the limit is the filtered colimit of the categories at the
stages. -/
@[stacks 09YU "clause (1)"]
public theorem smallEtaleStagesColimit_isConstructibleSetSheaf (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesColimit B (Type (u + 1)) Dg c hX (fun X => IsConstructibleSetSheaf B X) where
  faithful := smallEtaleStagesFaithful_isConstructibleSetSheaf B Dg c hX hc haff hqc hqs
  full := smallEtaleStagesFull_isConstructibleSetSheaf B Dg c hX hc haff hqc hqs
  essSurj := smallEtaleStagesEssSurj_isConstructibleSetSheaf B Dg c hX hc haff hqc hqs

end Sets

end AlgebraicGeometry

end
