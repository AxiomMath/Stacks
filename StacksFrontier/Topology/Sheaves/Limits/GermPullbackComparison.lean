module

public import StacksFrontier.Topology.Sheaves.Functors.Pullback.SheafStalk
public import StacksFrontier.Topology.Sheaves.Limits.GermPullback

/-!
# Comparison of the two models of the inverse-image sheaf of types

The inverse image of a sheaf of types along a continuous map is built in two ways: as
`TopCat.Sheaf.pullback`, the left adjoint of pushforward, and as `GermPullback.sheaf`, the sheaf
of compatible germs.  This file constructs the canonical morphism from the first to the second and
shows that it is an isomorphism.

## Main definitions

* `Stacks.GermPullbackComparison.pullbackToGerm`: the canonical morphism from the inverse-image
  sheaf to the sheaf of compatible germs.
* `Stacks.GermPullbackComparison.germPullback_stalkEval`: the induced map on stalks, shown
  bijective in `germPullback_stalkEval_bijective`.

## Main results

* `Stacks.GermPullbackComparison.pullbackToGerm_isIso`: `pullbackToGerm` is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite

universe u

noncomputable section

namespace Stacks.GermPullbackComparison

/-- The map carrying a section of a sheaf to the family of its germs along a continuous map. -/
noncomputable def germPullbackUnit {Y Z : TopCat.{u}} (g : Z ⟶ Y)
    (F : Y.Sheaf (Type u)) :
    F.obj ⟶ (TopCat.Presheaf.pushforward (Type u) g).obj
      (GermPullback.sheaf (ConcreteCategory.hom g) F.obj).obj where
  app V := ↾fun s ↦ GermPullback.ofSection (fun z ↦ z.2) s
  naturality := by
    intro V W f
    ext s
    refine GermPullback.ext fun z ↦ ?_
    change (⟨(ConcreteCategory.hom g) z.1,
      F.presheaf.germ (unop W) ((ConcreteCategory.hom g) z.1) z.2 (F.obj.map f s)⟩ :
        GermPullback.Germs F.presheaf) =
      ⟨(ConcreteCategory.hom g) z.1,
        F.presheaf.germ (unop V) ((ConcreteCategory.hom g) z.1) (f.unop.le z.2) s⟩
    exact congrArg (fun ξ ↦ (⟨(ConcreteCategory.hom g) z.1, ξ⟩ :
      GermPullback.Germs F.presheaf)) (F.presheaf.germ_res_apply' f _ z.2 s)

/-- The canonical morphism from the inverse-image sheaf to the sheaf of compatible germs along a
continuous map. -/
@[no_expose] noncomputable def pullbackToGerm {Y Z : TopCat.{u}} (g : Z ⟶ Y)
    (F : Y.Sheaf (Type u)) :
    (TopCat.Sheaf.pullback (Type u) g).obj F ⟶
      GermPullback.sheaf (ConcreteCategory.hom g) F.presheaf := by
  let G := GermPullback.sheaf (ConcreteCategory.hom g) F.presheaf
  exact ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).homEquiv F G).symm
    ⟨germPullbackUnit g F⟩

/-- `pullbackToGerm` carries the image of a section under the adjunction unit to the family of
its germs. -/
lemma pullbackToGerm_unit {Y Z : TopCat.{u}} (g : Z ⟶ Y)
    (F : Y.Sheaf (Type u)) (V : Opens Y) (s : F.obj.obj (op V)) :
    (pullbackToGerm g F).hom.app (op ((Opens.map g).obj V))
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app F).hom.app
        (op V) s) =
      GermPullback.ofSection (g := ConcreteCategory.hom g) (fun z ↦ z.2) s := by
  let G := GermPullback.sheaf (ConcreteCategory.hom g) F.presheaf
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g
  have h : adj.homEquiv F G (pullbackToGerm g F) =
      (⟨germPullbackUnit g F⟩ : F ⟶ (TopCat.Sheaf.pushforward (Type u) g).obj G) :=
    (adj.homEquiv F G).apply_symm_apply _
  rw [adj.homEquiv_unit] at h
  exact congrArg (fun m : F ⟶ (TopCat.Sheaf.pushforward (Type u) g).obj G ↦
    m.hom.app (op V) s) h

/-- A section of the sheaf of compatible germs takes, at a point, a value in the stalk above the
image of that point. -/
lemma germPullback_first {Y Z : TopCat.{u}} (g : Z → Y)
    (F : Y.Presheaf (Type u)) {W : Opens Z}
    (σ : (GermPullback.sheaf g F).presheaf.obj (op W)) (z : W) :
    (σ.1 z).1 = g z.1 := by
  obtain ⟨W₀, hz₀, i, V, hV, s, hs⟩ := GermPullback.exists_repr σ z.2
  exact congrArg Sigma.fst (hs ⟨z.1, hz₀⟩)

/-- The germ, in the stalk above the image point, determined by a section of the sheaf of
compatible germs. -/
noncomputable def germPullback_eval {Y Z : TopCat.{u}} (g : Z → Y)
    (F : Y.Presheaf (Type u)) {W : Opens Z}
    (σ : (GermPullback.sheaf g F).presheaf.obj (op W)) (z : W) :
    F.stalk (g z.1) :=
  (germPullback_first g F σ z) ▸ (σ.1 z).2

/-- Evaluating the family of germs of a section recovers the germ of that section. -/
lemma germPullback_eval_ofSection {Y Z : TopCat.{u}} (g : Z → Y)
    (F : Y.Presheaf (Type u)) {W : Opens Z} {V : Opens Y}
    (hV : ∀ z : W, g z.1 ∈ V) (s : F.obj (op V)) (z : W) :
    germPullback_eval g F (GermPullback.ofSection hV s) z =
      F.germOfSize V (g z.1) (hV z) s := by
  simp only [germPullback_eval, GermPullback.ofSection_val]
  rfl

/-- Evaluation of a section of the sheaf of compatible germs commutes with restriction. -/
lemma germPullback_eval_restrict {Y Z : TopCat.{u}} (g : Z → Y)
    (F : Y.Presheaf (Type u)) {W W' : Opens Z} (i : W' ⟶ W)
    (σ : (GermPullback.sheaf g F).presheaf.obj (op W)) (z : W') :
    germPullback_eval g F ((GermPullback.sheaf g F).presheaf.map i.op σ) z =
      germPullback_eval g F σ (i z) := by
  simp [germPullback_eval, GermPullback.val_map_apply]

/-- The map from the stalk of the sheaf of compatible germs to the stalk of the original sheaf
above the image point. -/
noncomputable def germPullback_stalkEval {Y Z : TopCat.{u}} (g : Z → Y)
    (F : Y.Presheaf (Type u)) (z : Z) :
    (GermPullback.sheaf g F).presheaf.stalk z ⟶ F.stalk (g z) :=
  colimit.desc ((OpenNhds.inclusion z).op ⋙ (GermPullback.sheaf g F).presheaf)
    { pt := F.stalk (g z)
      ι :=
        { app := fun U ↦ ↾fun σ ↦ germPullback_eval g F σ
            ⟨z, (unop U).2⟩
          naturality := by
            intro U V f
            ext σ
            exact germPullback_eval_restrict g F f.unop σ
              ⟨z, (unop V).2⟩ } }

/-- `germPullback_stalkEval` carries the germ of a section to the value of that section. -/
lemma germPullback_stalkEval_germ {Y Z : TopCat.{u}} (g : Z → Y)
    (F : Y.Presheaf (Type u)) {W : Opens Z} (z : Z) (hz : z ∈ W)
    (σ : (GermPullback.sheaf g F).presheaf.obj (op W)) :
    germPullback_stalkEval g F z
      ((GermPullback.sheaf g F).presheaf.germ W z hz σ) =
      germPullback_eval g F σ ⟨z, hz⟩ := by
  dsimp [germPullback_stalkEval, TopCat.Presheaf.germ]
  exact colimit.ι_desc_apply _ _ _

/-- `germPullback_stalkEval` is surjective. -/
lemma germPullback_stalkEval_surjective {Y Z : TopCat.{u}} (g : Z → Y)
    (hg : Continuous g) (F : Y.Presheaf (Type u)) (z : Z) :
    Function.Surjective (germPullback_stalkEval g F z) := by
  intro ξ
  obtain ⟨V, hzV, s, hs⟩ := F.exists_germ_eq ξ
  let W : Opens Z := ⟨g ⁻¹' (V : Set Y), V.isOpen.preimage hg⟩
  have hzW : z ∈ W := hzV
  let σ := GermPullback.ofSection (g := g) (𝒢 := F)
    (W := W) (V := V) (fun w : W ↦ w.2) s
  refine ⟨(GermPullback.sheaf g F).presheaf.germ W z hzW σ, ?_⟩
  rw [germPullback_stalkEval_germ, germPullback_eval_ofSection]
  exact hs

/-- Two sections of the sheaf of compatible germs with equal evaluations at a point take the same
value at that point. -/
lemma germPullback_value_eq_of_eval_eq {Y Z : TopCat.{u}} (g : Z → Y)
    (F : Y.Presheaf (Type u)) {W W' : Opens Z}
    (σ : (GermPullback.sheaf g F).presheaf.obj (op W))
    (τ : (GermPullback.sheaf g F).presheaf.obj (op W'))
    (z : Z) (hz : z ∈ W) (hz' : z ∈ W')
    (he : germPullback_eval g F σ ⟨z, hz⟩ =
      germPullback_eval g F τ ⟨z, hz'⟩) :
    σ.1 ⟨z, hz⟩ = τ.1 ⟨z, hz'⟩ := by
  let hσ := germPullback_first g F σ ⟨z, hz⟩
  let hτ := germPullback_first g F τ ⟨z, hz'⟩
  refine Sigma.ext (hσ.trans hτ.symm) ?_
  exact (eqRec_heq hσ _).symm.trans ((heq_of_eq he).trans (eqRec_heq hτ _))

/-- `germPullback_stalkEval` is injective. -/
lemma germPullback_stalkEval_injective {Y Z : TopCat.{u}} (g : Z → Y)
    (hg : Continuous g) (F : Y.Presheaf (Type u)) (z : Z) :
    Function.Injective (germPullback_stalkEval g F z) := by
  let G := GermPullback.sheaf g F
  intro a b h
  obtain ⟨U, hzU, σ, rfl⟩ := G.presheaf.exists_germ_eq a
  obtain ⟨V, hzV, τ, rfl⟩ := G.presheaf.exists_germ_eq b
  rw [germPullback_stalkEval_germ, germPullback_stalkEval_germ] at h
  have he := germPullback_value_eq_of_eval_eq g F σ τ z hzU hzV h
  obtain ⟨W, hzW, iU, iV, hw⟩ :=
    GermPullback.eventually_eq_of_apply_eq hg σ.2 τ.2 hzU hzV he
  have hrestr : G.presheaf.map iU.op σ = G.presheaf.map iV.op τ := GermPullback.ext hw
  exact (G.presheaf.germ_res_apply iU z hzW σ).symm.trans
    ((congrArg (G.presheaf.germ W z hzW) hrestr).trans (G.presheaf.germ_res_apply iV z hzW τ))

/-- `germPullback_stalkEval` is bijective. -/
lemma germPullback_stalkEval_bijective {Y Z : TopCat.{u}} (g : Z → Y)
    (hg : Continuous g) (F : Y.Presheaf (Type u)) (z : Z) :
    Function.Bijective (germPullback_stalkEval g F z) :=
  ⟨germPullback_stalkEval_injective g hg F z,
    germPullback_stalkEval_surjective g hg F z⟩

/-- On the germ of the image of a section under the adjunction unit, the stalk map of
`pullbackToGerm` followed by evaluation is the germ of that section. -/
lemma pullbackToGerm_stalkEval_unit {Y Z : TopCat.{u}} (g : Z ⟶ Y)
    (F : Y.Sheaf (Type u)) (z : Z) (V : Opens Y) (hz : g z ∈ V)
    (s : F.obj.obj (op V)) :
    germPullback_stalkEval (ConcreteCategory.hom g) F.presheaf z
      ((TopCat.Presheaf.stalkFunctor (Type u) z).map (pullbackToGerm g F).hom
        (((TopCat.Sheaf.pullback (Type u) g).obj F).presheaf.germ
          ((Opens.map g).obj V) z hz
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app F).hom.app
            (op V) s))) = F.presheaf.germ V (g z) hz s := by
  let t := ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app F).hom.app
    (op V) s
  have hmap := TopCat.Presheaf.stalkFunctor_map_germ_apply
    ((Opens.map g).obj V) z hz (pullbackToGerm g F).hom t
  calc
    _ = germPullback_stalkEval (ConcreteCategory.hom g) F.presheaf z
          (((GermPullback.sheaf (ConcreteCategory.hom g) F.presheaf).presheaf.germ
            ((Opens.map g).obj V) z hz)
            ((pullbackToGerm g F).hom.app (op ((Opens.map g).obj V)) t)) :=
      congrArg (germPullback_stalkEval (ConcreteCategory.hom g) F.presheaf z) hmap
    _ = F.presheaf.germ V (g z) hz s := by
      rw [show (pullbackToGerm g F).hom.app (op ((Opens.map g).obj V)) t =
        GermPullback.ofSection (g := ConcreteCategory.hom g) (fun w ↦ w.2) s from
        pullbackToGerm_unit g F V s]
      have hzW : z ∈ (Opens.map g).obj V := hz
      exact (germPullback_stalkEval_germ (ConcreteCategory.hom g) F.presheaf
        z hzW (GermPullback.ofSection (g := ConcreteCategory.hom g)
          (fun w : (Opens.map g).obj V ↦ w.2) s)).trans
        (germPullback_eval_ofSection (ConcreteCategory.hom g) F.presheaf
          (fun w : (Opens.map g).obj V ↦ w.2) s ⟨z, hzW⟩)

/-- The stalk map of `pullbackToGerm`, followed by evaluation, is the stalk comparison of the
inverse-image sheaf. -/
lemma pullbackToGerm_stalkEval {Y Z : TopCat.{u}} (g : Z ⟶ Y)
    (F : Y.Sheaf (Type u)) (z : Z)
    (a : ((TopCat.Sheaf.pullback (Type u) g).obj F).presheaf.stalk z) :
    germPullback_stalkEval (ConcreteCategory.hom g) F.presheaf z
      ((TopCat.Presheaf.stalkFunctor (Type u) z).map (pullbackToGerm g F).hom a) =
      (stalkPullbackSheafIso g F z).hom a := by
  let e := stalkPullbackSheafIso g F z
  obtain ⟨V, hz, s, hs⟩ := F.presheaf.exists_germ_eq (e.hom a)
  have ha : e.inv (F.presheaf.germ V (g z) hz s) = a := by
    rw [hs, Iso.hom_inv_id_apply]
  calc
    _ = germPullback_stalkEval (ConcreteCategory.hom g) F.presheaf z
        ((TopCat.Presheaf.stalkFunctor (Type u) z).map (pullbackToGerm g F).hom
          (e.inv (F.presheaf.germ V (g z) hz s))) :=
      congrArg _ (congrArg _ ha.symm)
    _ = germPullback_stalkEval (ConcreteCategory.hom g) F.presheaf z
        ((TopCat.Presheaf.stalkFunctor (Type u) z).map (pullbackToGerm g F).hom
          (((TopCat.Sheaf.pullback (Type u) g).obj F).presheaf.germ
            ((Opens.map g).obj V) z hz
            (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app F).hom.app
              (op V) s))) :=
      congrArg _ (congrArg _ (stalkPullbackSheafIso_inv_germ g F z V hz s))
    _ = F.presheaf.germ V (g z) hz s := pullbackToGerm_stalkEval_unit g F z V hz s
    _ = (stalkPullbackSheafIso g F z).hom a := hs

/-- **The inverse image of a sheaf of sets is the sheaf of compatible germs.** The canonical
map `pullbackToGerm` from the inverse image `g^{-1}F` to the germ model `GermPullback.sheaf` is
an isomorphism. This is what makes statements phrased with the germ model — for instance the
degree-zero case of Stacks 09V3 and proper base change for sheaves of sets, Stacks 0D90 — be
statements about the genuine inverse image. -/
theorem pullbackToGerm_isIso {Y Z : TopCat.{u}} (g : Z ⟶ Y)
    (F : Y.Sheaf (Type u)) : IsIso (pullbackToGerm g F) := by
  let : ∀ z : Z, IsIso ((TopCat.Presheaf.stalkFunctor (Type u) z).map
      (pullbackToGerm g F).hom) := by
    intro z
    apply (bijective_iff_isIso_ofHom _).mp
    have h := germPullback_stalkEval_bijective (ConcreteCategory.hom g)
      g.hom.continuous F.presheaf z
    have h₀ : Function.Bijective (stalkPullbackSheafIso g F z).hom :=
      (stalkPullbackSheafIso g F z).toEquiv.bijective
    apply (Function.Bijective.of_comp_iff' h _).mp
    change Function.Bijective
      (fun a : ((TopCat.Sheaf.pullback (Type u) g).obj F).presheaf.stalk z =>
        germPullback_stalkEval (ConcreteCategory.hom g) F.presheaf z
          ((TopCat.Presheaf.stalkFunctor (Type u) z).map (pullbackToGerm g F).hom a))
    convert h₀ using 1
    funext a
    exact pullbackToGerm_stalkEval g F z a
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _

end Stacks.GermPullbackComparison

end

end
