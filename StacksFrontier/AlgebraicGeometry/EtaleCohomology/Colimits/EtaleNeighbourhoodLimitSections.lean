module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitPostcompGerms
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PostcompInverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.ColimitSite
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitInverseImageSystem
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitPostcompGerms

/-!
# Sections of the inverse image of an étale sheaf to a limit of étale neighbourhoods

Let `X` be a scheme, `F` a sheaf of sets on its small étale site, `I` a directed set with a least
element and `(W_i)` an inverse system of étale `X`-schemes over `I` with affine transition
morphisms, with limit `T` and structure morphism `q : T ⟶ X`. Restricting a section of `F` over
`W_i` to `T` gives a map `F(W_i) ⟶ Γ(T, q⁻¹F)`. This file proves, for `W_⊥` affine, that these maps
exhibit `Γ(T, q⁻¹F)` as the filtered colimit of the `F(W_i)`: every global section of `q⁻¹F` comes
from some `W_i`, and two sections over `W_i` with the same image agree on some `W_j`, `j ≥ i`.

This is Stacks 09YQ in degree zero, for sheaves of sets and a quasi-compact quasi-separated
`W_⊥`.

## Implementation notes

The result is `Stacks.EtaleCohomology.LimitSiteBridge.wholeSections_colimit_of_qcqs` for the
restriction of `F` to `W_⊥`, read back on `X` through
`Stacks.EtaleCohomology.postcompInverseImageIso`.

## Main definitions

* `limitBase`: the structure morphism `q : T ⟶ X`.
* `limitSections`: the restriction maps `F(W_i) ⟶ Γ(T, q⁻¹F)`.

## Main results

* `limitSections_colimit`: every global section of `q⁻¹F` is the restriction of a section over
  some `W_i`, and two sections over `W_i` with the same restriction agree on some `W_j`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.EtaleLimitSections

open Stacks.EtaleCohomology.AffineLimitCohomology Stacks.EtaleCohomology.LimitSiteBridge

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [OrderBot I]
  {X : Scheme.{u}} (W : Iᵒᵖ ⥤ X.Etale)
  (c : Cone (W ⋙ Scheme.Etale.forget X ⋙ Over.forget X))

/-- The structure morphism `T ⟶ X` of the limit. -/
def limitBase : c.pt ⟶ X := c.π.app (op ⊥) ≫ (W.obj (op ⊥)).hom

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- Every leg `T ⟶ W_i` of the cone, composed with the structure morphism `W_i ⟶ X`, is the
structure morphism `limitBase W c : T ⟶ X`. -/
theorem π_comp_hom (i : Iᵒᵖ) : c.π.app i ≫ (W.obj i).hom = limitBase W c := by
  have h1 := c.w ((homOfLE (bot_le : ⊥ ≤ i.unop)).op)
  have h2 : (W.map (homOfLE (bot_le : ⊥ ≤ i.unop)).op).left ≫ (W.obj (op ⊥)).hom = (W.obj i).hom :=
    MorphismProperty.Over.w _
  exact (congrArg (c.π.app i ≫ ·) h2.symm).trans ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (W.obj (op ⊥)).hom) h1))

/-- **Restriction of a section over `W_i` to the limit**: the unit of the inverse image along
`q : T ⟶ X` over `W_i`, restricted along the morphism from `T` to `W_i ×_X T` given by the
projection `T ⟶ W_i`. -/
def limitSections {q : c.pt ⟶ X} (hq : ∀ i, c.π.app i ≫ (W.obj i).hom = q)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (i : Iᵒᵖ) :
    F.obj.obj (op (W.obj i)) ⟶
      ((smallEtaleInverseImage.{u, 0} q).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt))) :=
  ((smallEtaleInverseImageAdjunction.{u, 0} q).unit.app F).hom.app (op (W.obj i)) ≫
    ((smallEtaleInverseImage.{u, 0} q).obj F).obj.map
      (smallEtaleBaseChangeLift q (W.obj i) (c.π.app i) (hq i)).op

omit [Nonempty I] [IsDirected I (· ≤ ·)] [OrderBot I] in
/-- The restriction maps `limitSections` are compatible with the transition maps: for `i ≤ j`,
restricting a section over `W_i` to `W_j` and then to `T` is restricting it to `T`. -/
theorem limitSections_transition {q : c.pt ⟶ X} (hq : ∀ i, c.π.app i ≫ (W.obj i).hom = q)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) {i j : I} (d : i ≤ j) :
    F.obj.map (W.map (homOfLE d).op).op ≫ limitSections W c hq F (op j) =
      limitSections W c hq F (op i) := by
  have hn := ((smallEtaleInverseImageAdjunction.{u, 0} q).unit.app F).hom.naturality
      (W.map (homOfLE d).op).op
  have hl : smallEtaleBaseChangeLift q (W.obj (op j)) (c.π.app (op j)) (hq _) ≫
      (smallEtaleBaseChange q).map (W.map (homOfLE d).op) =
      smallEtaleBaseChangeLift q (W.obj (op i)) (c.π.app (op i)) (hq _) := by
    apply smallEtaleBaseChange_hom_ext
    refine (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (smallEtaleBaseChange_map_left_fst _ _)).trans ?_)
    refine (Category.assoc _ _ _).symm.trans ?_
    refine ((congrArg (· ≫ _) (pullback.lift_fst _ _ _)).trans ?_).trans
      (pullback.lift_fst _ _ _).symm
    exact c.w (homOfLE d).op
  have hm := congrArg (fun m => ((smallEtaleInverseImage.{u, 0} q).obj F).obj.map
    (Quiver.Hom.op m)) hl
  simp only [op_comp, Functor.map_comp] at hm
  rw [limitSections, limitSections]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hn).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hm)))

/-- **Stacks 09YQ in degree zero, for sheaves of sets and étale neighbourhoods.** Let `(W_i)` be an
inverse system of étale `X`-schemes over a directed set with a least element `⊥`, with affine
transition morphisms and `W_⊥` quasi-compact and quasi-separated, and let `T = lim W_i` with
`q : T ⟶ X`. For a sheaf of sets `F` on the small étale site of `X`, every global section of
`q⁻¹F` is the restriction of a section of `F` over some `W_i`, and two sections over `W_i` with the
same restriction agree on some `W_j`, `j ≥ i`. Here `q` is any morphism through which all the
legs of the cone lie over `X`. -/
theorem limitSections_colimit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (W.map a).left]
    (hc : IsLimit c)
    {q : c.pt ⟶ X} (hq : ∀ i, c.π.app i ≫ (W.obj i).hom = q)
    [CompactSpace (W.obj (op ⊥)).left] [QuasiSeparatedSpace (W.obj (op ⊥)).left]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    (∀ s : ((smallEtaleInverseImage.{u, 0} q).obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 c.pt))), ∃ (i : I) (x : F.obj.obj (op (W.obj (op i)))),
          limitSections W c hq F (op i) x = s) ∧
      ∀ (i : I) (x x' : F.obj.obj (op (W.obj (op i)))),
        limitSections W c hq F (op i) x = limitSections W c hq F (op i) x' →
          ∃ (j : I) (d : i ≤ j), F.obj.map (W.map (homOfLE d).op).op x =
            F.obj.map (W.map (homOfLE d).op).op x' := by
  let D := W ⋙ Scheme.Etale.forget X ⋙ Over.forget X
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a) := fun a =>
    inferInstanceAs (IsAffineHom (W.map a).left)
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a) := fun a => etale_left (W.map a)
  obtain ⟨B, hB⟩ := BigEtaleSite.exists_contains_of_small (Set.range D.obj ∪ {c.pt})
  have hD : ∀ i, B.Contains (D.obj i) := fun i => hB _ (Or.inl ⟨i, rfl⟩)
  have hX : B.Contains c.pt := hB _ (Or.inr rfl)
  -- the bottom level, its structure morphism to `X`, and the restriction of `F` to it
  let w : lvl D c B hD hX hc (bottom D c B hD hX hc) ⟶ X := (W.obj (op ⊥)).hom
  have : Etale w := (W.obj (op ⊥)).prop
  have : CompactSpace (lvl D c B hD hX hc (bottom D c B hD hX hc)) :=
    ‹CompactSpace (W.obj (op ⊥)).left›
  have : QuasiSeparatedSpace (lvl D c B hD hX hc (bottom D c B hD hX hc)) :=
    ‹QuasiSeparatedSpace (W.obj (op ⊥)).left›
  let F₀ := ((smallEtalePostcomp w).sheafPushforwardContinuous (Type (u + 1))
    (lvl D c B hD hX hc (bottom D c B hD hX hc)).smallEtaleTopology X.smallEtaleTopology).obj F
  obtain ⟨hsurj, hinj⟩ := wholeSections_colimit_of_qcqs F₀
  -- the levels read back in the original system
  have hw : ∀ i : I, 𝟙 (W.obj (op i)).left ≫ (W.obj (op i)).hom =
      (𝟙 (W.obj (op i)).left ≫ (W.map (homOfLE (bot_le : ⊥ ≤ i)).op).left) ≫
        (W.obj (op ⊥)).hom := by
    intro i
    rw [Category.id_comp, Category.id_comp]
    exact (MorphismProperty.Over.w (W.map (homOfLE (bot_le : ⊥ ≤ i)).op)).symm
  let eW : ∀ i : I, (smallEtalePostcomp w).obj (wh D c B hD hX hc i) ⟶ W.obj (op i) := fun i =>
    MorphismProperty.Over.homMk (𝟙 (W.obj (op i)).left) (hw i) trivial
  let eW' : ∀ i : I, W.obj (op i) ⟶ (smallEtalePostcomp w).obj (wh D c B hD hX hc i) := fun i =>
    MorphismProperty.Over.homMk (𝟙 (W.obj (op i)).left) (hw i).symm trivial
  have heW : ∀ i : I, Function.Bijective (F.obj.map (eW i).op) := fun i => by
    have : IsIso (eW i) := ⟨eW' i, MorphismProperty.Over.Hom.ext (Category.id_comp _),
      MorphismProperty.Over.Hom.ext (Category.id_comp _)⟩
    exact ConcreteCategory.bijective_of_isIso (F.obj.map (eW i).op)
  have htr : ∀ {i j : I} (d : i ≤ j), (smallEtalePostcomp w).map (whMap D c B hD hX hc d) ≫ eW i =
      eW j ≫ W.map (homOfLE d).op := fun d =>
    MorphismProperty.Over.Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm)
  -- the inverse image of the restriction to the limit is the inverse image of `F`
  have hq' : q = lvlπ D c B hD hX hc (bottom D c B hD hX hc) ≫ w := (hq (op ⊥)).symm
  let e := postcompInverseImageIso w (lvlπ D c B hD hX hc (bottom D c B hD hX hc)) q hq'
  let θ := (e.hom.app F).hom.app (op (unitT D c))
  have hθ : Function.Bijective θ := ConcreteCategory.bijective_of_isIso θ
  have key : ∀ (i : I) (x : F.obj.obj (op (W.obj (op i)))),
      θ (wholeSections D c B hD hX hc F₀ i (F.obj.map (eW i).op x)) =
        limitSections W c hq F (op i) x := by
    intro i x
    let Q := (smallEtaleInverseImage.{u, 0} q).obj F
    have hlift : sig D c B hD hX hc i ≫ baseChangePostcompMap w
        (lvlπ D c B hD hX hc (bottom D c B hD hX hc)) q hq' (wh D c B hD hX hc i) ≫
          (smallEtaleBaseChange q).map (eW i) =
        smallEtaleBaseChangeLift q (W.obj (op i)) (c.π.app (op i)) (hq _) := by
      apply smallEtaleBaseChange_hom_ext
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
        (smallEtaleBaseChange_map_left_fst _ (eW i))))).trans ?_
      refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
        (baseChangePostcompMap_left_fst w _ _ hq' _)).trans (Category.comp_id _)))).trans ?_
      exact (sig_left_fst i).trans (pullback.lift_fst _ _ _).symm
    have n1 := ConcreteCategory.congr_hom ((e.hom.app F).hom.naturality (sig D c B hD hX hc i).op)
      (unitAt D c B hD hX hc F₀ (wh D c B hD hX hc i) (F.obj.map (eW i).op x))
    have n2 := unit_comp_postcompInverseImageIso w (lvlπ D c B hD hX hc (bottom D c B hD hX hc))
      q hq' F (wh D c B hD hX hc i) (F.obj.map (eW i).op x)
    have n3 := ConcreteCategory.congr_hom
      (((smallEtaleInverseImageAdjunction.{u, 0} q).unit.app F).hom.naturality
        (eW i).op) x
    have n4 := ConcreteCategory.congr_hom (congrArg (fun m => Q.obj.map (Quiver.Hom.op m)) hlift)
      (((smallEtaleInverseImageAdjunction.{u, 0} q).unit.app F).hom.app
        (op (W.obj (op i))) x)
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] at n1 n3 n4
    refine n1.trans ((congrArg (Q.obj.map (sig D c B hD hX hc i).op) n2).trans ?_)
    exact (congrArg (fun y => Q.obj.map (sig D c B hD hX hc i).op (Q.obj.map
      (baseChangePostcompMap w (lvlπ D c B hD hX hc (bottom D c B hD hX hc)) q hq'
        (wh D c B hD hX hc i)).op y)) n3).trans n4
  refine ⟨fun s => ?_, fun i x x' hxx' => ?_⟩
  · obtain ⟨s', rfl⟩ := hθ.2 s
    obtain ⟨i, y, rfl⟩ := hsurj s'
    obtain ⟨x, rfl⟩ := (heW i).2 y
    exact ⟨i, x, (key i x).symm⟩
  · rw [← key, ← key] at hxx'
    obtain ⟨j, d, hd⟩ := hinj i _ _ (hθ.1 hxx')
    refine ⟨j, d, (heW j).1 ?_⟩
    have h1 := congrArg (fun m => F.obj.map m.op x) (htr d)
    have h2 := congrArg (fun m => F.obj.map m.op x') (htr d)
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] at h1 h2
    rw [← h1, ← h2]
    exact hd

end Stacks.EtaleCohomology.EtaleLimitSections
