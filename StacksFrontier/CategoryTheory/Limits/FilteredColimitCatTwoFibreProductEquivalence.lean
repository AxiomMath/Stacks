module

public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatTwoFibreProductComparison

/-!
# Filtered colimits of categories commute with 2-fibre products

Let `α : 𝒳 ⟶ 𝒴` and `γ : 𝒵 ⟶ 𝒴` be morphisms of diagrams of categories indexed by a filtered
category `J`. This file proves that the comparison functor
`CategoryTheory.Cat.colimitTwoFibreProductComparison`

`colim (𝒳ⱼ ×_{𝒴ⱼ} 𝒵ⱼ) ⥤ (colim 𝒳ⱼ) ×_{colim 𝒴ⱼ} (colim 𝒵ⱼ)`

is an equivalence, which is the statement "filtered colimits of categories commute with
2-fibre products" used with the details omitted in the proofs of Stacks 0CMT and Stacks 0CMW.

## Main results

* `CategoryTheory.Cat.isEquivalence_colimitTwoFibreProductComparison`: the comparison is an
  equivalence.
* `CategoryTheory.Cat.faithful_colimitTwoFibreProductComparison`
* `CategoryTheory.Cat.full_colimitTwoFibreProductComparison`
* `CategoryTheory.Cat.essSurj_colimitTwoFibreProductComparison`
* `CategoryTheory.Cat.exists_stage_hom_of_twoFibreProductStage`: a morphism between the
  stagewise comparison images of two objects of one stage comes from a morphism of a later
  stage.
* `CategoryTheory.Cat.exists_stage_iso_of_colimit`: an isomorphism of a filtered colimit in
  `Cat` between the images of two objects of one stage comes from an isomorphism of a later
  stage.
* `CategoryTheory.Cat.exists_stage_obj_of_twoFibreProductStage`: an object of the 2-fibre
  product of the colimits is the stagewise comparison of an object of a stage.

## Implementation notes

All three properties are checked by representing the data at a stage of the diagram and using
that the comparison restricted to a stage is the stagewise comparison
(`CategoryTheory.Cat.colimitTwoFibreProductComparison_ι`). The representations are the toolkit
of `StacksFrontier.CategoryTheory.Limits.FilteredColimitCatStages`, and filteredness enters twice:
once to bring the two components of a datum to one common stage, and once more to force an
identity that holds in the colimit to hold already at a stage, which is
`CategoryTheory.Cat.exists_common_stage_eq_of_colimit_ι_map_eq`.

Essential surjectivity is the only one of the three that needs an *isomorphism* at a stage
rather than a morphism: the structural isomorphism of an object of the 2-fibre product of the
colimits must be realised at a stage for the three data to assemble into an object of the
stagewise 2-fibre product, and `CategoryTheory.Cat.exists_stage_iso_of_colimit` does that by
representing the inverse after the isomorphism and then forcing the two composites to be
identities already at a stage. The resulting object is sent by the stagewise comparison to the
given object *on the nose*, not merely up to isomorphism, so the witnessing isomorphism is a
transport.

The compatibility condition carried by a morphism of 2-fibre products is what makes this more
than a statement about the two components separately, and it is handled once and for all by
`CategoryTheory.Cat.categoricalPullback_mapEq_hom_w_iff`: both the transitions of the stagewise
2-fibre product and the stagewise comparison are instances of the functoriality of the 2-fibre
product along two *strictly* commuting squares, and for those the condition transports in both
directions. Its ingredients are stated with
`CategoryTheory.Cat.strictSquare_obj` rather than `CategoryTheory.Functor.congr_obj`, so that
the transports they produce mention no composite functors and therefore cancel syntactically;
`CategoryTheory.eqToHom_trans_assoc` is the simp lemma that collapses the resulting
right-associated chains, and where even that does not fire — the endpoints being equal only
definitionally, or the category instance being reached by two different paths — the chain is
collapsed by `exact` with `CategoryTheory.Cat.eqToHom_conj_assoc` and its variants.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 0CMT](https://stacks.math.columbia.edu/tag/0CMT)
* [Stacks Project, Tag 0CMS](https://stacks.math.columbia.edu/tag/0CMS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Cat

universe t u v w

section TransportW

variable {𝒳 𝒴 𝒵 𝒜 ℬ 𝒞 : Type*} [Category 𝒳] [Category 𝒴] [Category 𝒵]
  [Category 𝒜] [Category ℬ] [Category 𝒞]

/-- Going along a strictly commuting square of functors one way, with the two transports of
`CategoryTheory.Cat.strictSquare_obj` written out. -/
lemma strictSquare_map (H : 𝒳 ⥤ 𝒵) (L : 𝒳 ⥤ 𝒜) (M : 𝒵 ⥤ 𝒞) (F : 𝒜 ⥤ 𝒞)
    (hHM : H ⋙ M = L ⋙ F) {x y : 𝒳} (c : x ⟶ y) :
    M.map (H.map c) = eqToHom (Functor.congr_obj hHM x) ≫ F.map (L.map c) ≫
      eqToHom (Functor.congr_obj hHM y).symm := by
  simpa only [Functor.comp_map] using Functor.congr_hom hHM c

/-- Going along a strictly commuting square of functors the other way. -/
lemma strictSquare_map' (H : 𝒳 ⥤ 𝒵) (L : 𝒳 ⥤ 𝒜) (M : 𝒵 ⥤ 𝒞) (F : 𝒜 ⥤ 𝒞)
    (hHM : H ⋙ M = L ⋙ F) {x y : 𝒳} (c : x ⟶ y) :
    F.map (L.map c) = eqToHom (Functor.congr_obj hHM x).symm ≫ M.map (H.map c) ≫
      eqToHom (Functor.congr_obj hHM y) := by
  rw [strictSquare_map H L M F hHM c]; simp

variable (H : 𝒳 ⥤ 𝒵) (I : 𝒴 ⥤ 𝒵) (L : 𝒳 ⥤ 𝒜) (K : 𝒴 ⥤ ℬ) (M : 𝒵 ⥤ 𝒞) (F : 𝒜 ⥤ 𝒞)
  (G : ℬ ⥤ 𝒞) (hKG : K ⋙ G = I ⋙ M) (hHM : H ⋙ M = L ⋙ F)

/-- The first component of the image of an object under the functoriality of the 2-fibre
product. -/
@[simp]
lemma categoricalPullback_mapEq_obj_fst (R : CategoricalPullback H I) :
    ((CategoricalPullback.map H I L K M F G (eqToIso hKG) (eqToIso hHM)).obj R).fst =
      L.obj R.fst := rfl

/-- The second component of the image of an object under the functoriality of the 2-fibre
product. -/
@[simp]
lemma categoricalPullback_mapEq_obj_snd (R : CategoricalPullback H I) :
    ((CategoricalPullback.map H I L K M F G (eqToIso hKG) (eqToIso hHM)).obj R).snd =
      K.obj R.snd := rfl

/-- The structural isomorphism of the image of an object under the functoriality of the 2-fibre
product built from two strictly commuting squares, with its two 2-cells written as
transports. -/
lemma categoricalPullback_mapEq_obj_iso_hom (R : CategoricalPullback H I) :
    ((CategoricalPullback.map H I L K M F G (eqToIso hKG) (eqToIso hHM)).obj R).iso.hom =
      eqToHom (Functor.congr_obj hHM R.fst).symm ≫ M.map R.iso.hom ≫
        eqToHom (Functor.congr_obj hKG R.snd).symm := by
  change (eqToIso hHM).inv.app R.fst ≫ M.map R.iso.hom ≫ (eqToIso hKG).inv.app R.snd = _
  simp only [CategoryTheory.eqToIso.inv]
  rw [CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_app]

/-- **The compatibility condition of a morphism of 2-fibre products transports along the
functoriality built from two strictly commuting squares.** A pair of component morphisms
satisfies the condition for the image objects exactly when the two sides of the condition at the
source have the same image under the functor filling the squares. -/
lemma categoricalPullback_mapEq_hom_w_iff
    {P Q : CategoricalPullback H I} (cX : P.fst ⟶ Q.fst) (cZ : P.snd ⟶ Q.snd) :
    (F.map (L.map cX) : F.obj (L.obj P.fst) ⟶ F.obj (L.obj Q.fst)) ≫
          ((CategoricalPullback.map H I L K M F G (eqToIso hKG) (eqToIso hHM)).obj Q).iso.hom =
        ((CategoricalPullback.map H I L K M F G (eqToIso hKG) (eqToIso hHM)).obj P).iso.hom ≫
          (G.map (K.map cZ) : G.obj (K.obj P.snd) ⟶ G.obj (K.obj Q.snd)) ↔
      M.map (H.map cX ≫ Q.iso.hom) = M.map (P.iso.hom ≫ I.map cZ) := by
  dsimp only [categoricalPullback_mapEq_obj_fst, categoricalPullback_mapEq_obj_snd,
    CategoricalPullback.π₁_obj, CategoricalPullback.π₂_obj]
  rw [categoricalPullback_mapEq_obj_iso_hom, categoricalPullback_mapEq_obj_iso_hom,
    strictSquare_map' H L M F hHM cX, strictSquare_map K I G M hKG cZ,
    Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [← Category.assoc (M.map (H.map cX)), ← Category.assoc (M.map P.iso.hom)]
  refine ⟨fun hh => (cancel_mono (eqToHom _)).mp ((cancel_epi (eqToHom _)).mp hh), fun hh => ?_⟩
  rw [hh]

end TransportW

section Equivalence

variable {J : Type v} [Category.{w} J] [IsFiltered J]
  {X Y Z : J ⥤ Cat.{max u v w, max u v w}} (α : X ⟶ Y) (γ : Z ⟶ Y)
  [HasColimit X] [HasColimit Y] [HasColimit Z]
  [HasColimit (X ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
  [HasColimit (Y ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
  [HasColimit (Z ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
  [HasColimit (twoFibreProductDiagram α γ)]
  [HasColimit (twoFibreProductDiagram α γ ⋙
    CategoryTheory.nerveFunctor.{max u v w, max u v w})]

/-- A morphism conjugated by two transports on either side, the inner pair grouped with the
morphism, is the single conjugate: the target transports are taken as arguments, so that this
applies by `exact` wherever the endpoints agree only definitionally. -/
lemma eqToHom_conj_assoc {C : Type*} [Category C] {a₁ a₂ a₃ b₁ b₂ b₃ : C}
    (p₁ : a₁ = a₂) (p₂ : a₂ = a₃) (f : a₃ ⟶ b₁) (q₁ : b₁ = b₂) (q₂ : b₂ = b₃)
    (p : a₁ = a₃) (q : b₁ = b₃) :
    eqToHom p₁ ≫ (eqToHom p₂ ≫ f ≫ eqToHom q₁) ≫ eqToHom q₂ = eqToHom p ≫ f ≫ eqToHom q := by
  cases p₁; cases p₂; cases q₁; cases q₂; simp

/-- A morphism conjugated by three nested pairs of transports is the single conjugate. -/
lemma eqToHom_conj_assoc₃ {C : Type*} [Category C] {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : C}
    (p₁ : a₁ = a₂) (p₂ : a₂ = a₃) (p₃ : a₃ = a₄) (f : a₄ ⟶ b₁)
    (q₁ : b₁ = b₂) (q₂ : b₂ = b₃) (q₃ : b₃ = b₄) (p : a₁ = a₄) (q : b₁ = b₄) :
    eqToHom p₁ ≫ (eqToHom p₂ ≫ (eqToHom p₃ ≫ f ≫ eqToHom q₁) ≫ eqToHom q₂) ≫ eqToHom q₃ =
      eqToHom p ≫ f ≫ eqToHom q := by
  cases p₁; cases p₂; cases p₃; cases q₁; cases q₂; cases q₃; simp

/-- Conjugating a morphism by a pair of transports and then by the inverse pair does
nothing. -/
lemma eqToHom_conj_cancel {C : Type*} [Category C] {x y x' y' : C} (p : x = x') (q : y' = y)
    (f : x ⟶ y) (p' : x' = x) (q' : y = y') :
    eqToHom p ≫ (eqToHom p' ≫ f ≫ eqToHom q') ≫ eqToHom q = f := by
  cases p'; cases q'; simp

/-- A functor applied to a morphism conjugated by a pair of transports. -/
lemma map_eqToHom_conj {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x y x' y' : C} (p : x' = x) (f : x ⟶ y) (q : y = y') :
    F.map (eqToHom p ≫ f ≫ eqToHom q) =
      eqToHom (congrArg F.obj p) ≫ F.map f ≫ eqToHom (congrArg F.obj q) := by
  cases p; cases q; simp

/-- Conjugating two mutually inverse morphisms by a pair of transports and composing gives the
identity. -/
lemma eqToHom_conj_comp_self {C : Type*} [Category C] {x y x' y' : C}
    (p : x' = x) (q : y = y') (f : x ⟶ y) (g : y ⟶ x) (h : f ≫ g = 𝟙 x) :
    (eqToHom p ≫ f ≫ eqToHom q) ≫ eqToHom q.symm ≫ g ≫ eqToHom p.symm = 𝟙 x' := by
  cases p; cases q; simp [h]

omit [IsFiltered J] in
/-- An identity between the images of two parallel morphisms under a transition persists along
any further transition. -/
lemma map_comp_eq_of_map_eq {W : J ⥤ Cat.{t, t}} {j k l : J}
    (r : j ⟶ k) (s : k ⟶ l) {a b : W.obj j} {p q : a ⟶ b}
    (h : (W.map r).toFunctor.map p = (W.map r).toFunctor.map q) :
    (W.map (r ≫ s)).toFunctor.map p = (W.map (r ≫ s)).toFunctor.map q := by
  have e : (W.map (r ≫ s)).toFunctor = (W.map r).toFunctor ⋙ (W.map s).toFunctor :=
    (congrArg Cat.Hom.toFunctor (W.map_comp r s)).trans (Cat.Hom.comp_toFunctor _ _)
  rw [Functor.congr_hom e p, Functor.congr_hom e q, Functor.comp_map, Functor.comp_map, h]

/-- Two transitions out of one stage of a filtered category factor through a single transition
out of that stage. -/
lemma exists_common_stage_of_two {j k₁ k₂ : J} (u₁ : j ⟶ k₁) (u₂ : j ⟶ k₂) :
    ∃ (k : J) (u : j ⟶ k) (v₁ : k₁ ⟶ k) (v₂ : k₂ ⟶ k), u = u₁ ≫ v₁ ∧ u = u₂ ≫ v₂ := by
  refine ⟨IsFiltered.coeq (u₁ ≫ IsFiltered.leftToMax k₁ k₂) (u₂ ≫ IsFiltered.rightToMax k₁ k₂),
    (u₁ ≫ IsFiltered.leftToMax k₁ k₂) ≫ IsFiltered.coeqHom _ _,
    IsFiltered.leftToMax k₁ k₂ ≫ IsFiltered.coeqHom _ _,
    IsFiltered.rightToMax k₁ k₂ ≫ IsFiltered.coeqHom _ _, Category.assoc _ _ _, ?_⟩
  rw [← Category.assoc]
  exact IsFiltered.coeq_condition _ _

omit [IsFiltered J] in
/-- The transition square of a colimit inclusion, read on objects. -/
lemma colimit_ι_map_obj (W : J ⥤ Cat.{t, t}) [HasColimit W] {j k : J} (s : j ⟶ k)
    (a : W.obj j) :
    (colimit.ι W k).toFunctor.obj ((W.map s).toFunctor.obj a) =
      (colimit.ι W j).toFunctor.obj a :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor (colimit.w W s)) a

/-- A morphism of a stage, whose image in the colimit is a conjugate of `f`, has a transition
image with the same property. -/
private lemma colimit_ι_map_map_eq_conj {K : Type v} [Category.{w} K]
    {W : K ⥤ Cat.{t, t}} [HasColimit W] {j k : K}
    (s : j ⟶ k) {a b : W.obj j} (g : a ⟶ b) {x y : ↑(colimit W)} (f : x ⟶ y)
    {p : (colimit.ι W j).toFunctor.obj a = x} {q : y = (colimit.ι W j).toFunctor.obj b}
    (hg : (colimit.ι W j).toFunctor.map g = eqToHom p ≫ f ≫ eqToHom q)
    (P : (colimit.ι W k).toFunctor.obj ((W.map s).toFunctor.obj a) = x)
    (Q : y = (colimit.ι W k).toFunctor.obj ((W.map s).toFunctor.obj b)) :
    (colimit.ι W k).toFunctor.map ((W.map s).toFunctor.map g) = eqToHom P ≫ f ≫ eqToHom Q := by
  rw [colimit_ι_map_map, hg]
  exact eqToHom_conj_assoc _ _ _ _ _ _ _

/-- **A morphism of a filtered colimit in `Cat` between the images of two objects of one stage
is the image of a morphism of a later stage**, with the two transports written out. -/
lemma exists_stage_hom_of_colimit (W : J ⥤ Cat.{max u v w, max u v w}) [HasColimit W]
    [HasColimit (W ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    (j : J) (a b : W.obj j)
    (f : (colimit.ι W j).toFunctor.obj a ⟶ (colimit.ι W j).toFunctor.obj b) :
    ∃ (k : J) (r : j ⟶ k) (g : (W.map r).toFunctor.obj a ⟶ (W.map r).toFunctor.obj b),
      (colimit.ι W k).toFunctor.map g =
        eqToHom (colimit_ι_map_obj W r a) ≫ f ≫ eqToHom (colimit_ι_map_obj W r b).symm := by
  obtain ⟨k, r, g, hg⟩ := exists_stage_map_of_colimit_of_eq.{u, v, w} W j a b f
  refine ⟨k, r, g, ?_⟩
  rw [(comp_eqToHom_iff _ _ _).mp
    (transport_hom_of_heq (colimit_ι_map_obj W r a) (colimit_ι_map_obj W r b) hg),
    Category.assoc]

/-- The first component of a morphism of 2-fibre products conjugated by two transports. -/
lemma categoricalPullback_eqToHom_conj_fst {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ]
    [Category 𝒞] {F : 𝒜 ⥤ 𝒞} {G : ℬ ⥤ 𝒞} {P Q P' Q' : CategoricalPullback F G}
    (eP : P' = P) (eQ : Q = Q') (f : P ⟶ Q) :
    (eqToHom eP ≫ f ≫ eqToHom eQ).fst =
      eqToHom (congrArg CategoricalPullback.fst eP) ≫ f.fst ≫
        eqToHom (congrArg CategoricalPullback.fst eQ) := by
  cases eP; cases eQ; simp

/-- The second component of a morphism of 2-fibre products conjugated by two transports. -/
lemma categoricalPullback_eqToHom_conj_snd {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ]
    [Category 𝒞] {F : 𝒜 ⥤ 𝒞} {G : ℬ ⥤ 𝒞} {P Q P' Q' : CategoricalPullback F G}
    (eP : P' = P) (eQ : Q = Q') (f : P ⟶ Q) :
    (eqToHom eP ≫ f ≫ eqToHom eQ).snd =
      eqToHom (congrArg CategoricalPullback.snd eP) ≫ f.snd ≫
        eqToHom (congrArg CategoricalPullback.snd eQ) := by
  cases eP; cases eQ; simp

/-- **The compatibility condition of a morphism of 2-fibre products transports to any pair of
objects equal to its endpoints.** -/
lemma categoricalPullback_transport_w {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]
    {F : 𝒜 ⥤ 𝒞} {G : ℬ ⥤ 𝒞} {P Q P' Q' : CategoricalPullback F G}
    (eP : P' = P) (eQ : Q' = Q) (f : P ⟶ Q) :
    F.map (eqToHom (congrArg CategoricalPullback.fst eP) ≫ f.fst ≫
        eqToHom (congrArg CategoricalPullback.fst eQ).symm) ≫ Q'.iso.hom =
      P'.iso.hom ≫ G.map (eqToHom (congrArg CategoricalPullback.snd eP) ≫ f.snd ≫
        eqToHom (congrArg CategoricalPullback.snd eQ).symm) := by
  cases eP; cases eQ; simp

omit [IsFiltered J]
    [HasColimit (X ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    [HasColimit (Y ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    [HasColimit (Z ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    [HasColimit (twoFibreProductDiagram α γ)] [HasColimit (twoFibreProductDiagram α γ ⋙
    CategoryTheory.nerveFunctor.{max u v w, max u v w})] in
/-- The compatibility condition for the stagewise comparison, read back at the stage. -/
lemma twoFibreProductStage_hom_w_iff (k : J)
    {A B : CategoricalPullback (α.app k).toFunctor (γ.app k).toFunctor}
    (cX : A.fst ⟶ B.fst) (cZ : A.snd ⟶ B.snd) :
    ((colimMap α).toFunctor.map ((colimit.ι X k).toFunctor.map cX) :
            (colimMap α).toFunctor.obj ((colimit.ι X k).toFunctor.obj A.fst) ⟶
              (colimMap α).toFunctor.obj ((colimit.ι X k).toFunctor.obj B.fst)) ≫
          ((twoFibreProductStage α γ k).obj B).iso.hom =
        ((twoFibreProductStage α γ k).obj A).iso.hom ≫
          ((colimMap γ).toFunctor.map ((colimit.ι Z k).toFunctor.map cZ) :
            (colimMap γ).toFunctor.obj ((colimit.ι Z k).toFunctor.obj A.snd) ⟶
              (colimMap γ).toFunctor.obj ((colimit.ι Z k).toFunctor.obj B.snd)) ↔
      (colimit.ι Y k).toFunctor.map ((α.app k).toFunctor.map cX ≫ B.iso.hom) =
        (colimit.ι Y k).toFunctor.map (A.iso.hom ≫ (γ.app k).toFunctor.map cZ) :=
  categoricalPullback_mapEq_hom_w_iff (α.app k).toFunctor (γ.app k).toFunctor
    (colimit.ι X k).toFunctor (colimit.ι Z k).toFunctor (colimit.ι Y k).toFunctor
    (colimMap α).toFunctor (colimMap γ).toFunctor
    (ι_colimMap_toFunctor γ k) (ι_colimMap_toFunctor α k).symm cX cZ

omit [IsFiltered J] [HasColimit X] [HasColimit Y] [HasColimit Z]
    [HasColimit (X ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    [HasColimit (Y ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    [HasColimit (Z ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    [HasColimit (twoFibreProductDiagram α γ)] [HasColimit (twoFibreProductDiagram α γ ⋙
    CategoryTheory.nerveFunctor.{max u v w, max u v w})] in
/-- The compatibility condition for a transition of the stagewise 2-fibre product, read back at
the earlier stage. -/
lemma twoFibreProductMap_hom_w_iff {k m : J} (v : k ⟶ m)
    {A B : CategoricalPullback (α.app k).toFunctor (γ.app k).toFunctor}
    (cX : A.fst ⟶ B.fst) (cZ : A.snd ⟶ B.snd) :
    ((α.app m).toFunctor.map ((X.map v).toFunctor.map cX) :
            (α.app m).toFunctor.obj ((X.map v).toFunctor.obj A.fst) ⟶
              (α.app m).toFunctor.obj ((X.map v).toFunctor.obj B.fst)) ≫
          ((twoFibreProductMap α γ v).obj B).iso.hom =
        ((twoFibreProductMap α γ v).obj A).iso.hom ≫
          ((γ.app m).toFunctor.map ((Z.map v).toFunctor.map cZ) :
            (γ.app m).toFunctor.obj ((Z.map v).toFunctor.obj A.snd) ⟶
              (γ.app m).toFunctor.obj ((Z.map v).toFunctor.obj B.snd)) ↔
      (Y.map v).toFunctor.map ((α.app k).toFunctor.map cX ≫ B.iso.hom) =
        (Y.map v).toFunctor.map (A.iso.hom ≫ (γ.app k).toFunctor.map cZ) :=
  categoricalPullback_mapEq_hom_w_iff (α.app k).toFunctor (γ.app k).toFunctor
    (X.map v).toFunctor (Z.map v).toFunctor (Y.map v).toFunctor
    (α.app m).toFunctor (γ.app m).toFunctor
    (naturality_toFunctor γ v) (naturality_toFunctor α v).symm cX cZ

omit [IsFiltered J]
    [HasColimit (X ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    [HasColimit (Y ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    [HasColimit (Z ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    [HasColimit (twoFibreProductDiagram α γ)] [HasColimit (twoFibreProductDiagram α γ ⋙
    CategoryTheory.nerveFunctor.{max u v w, max u v w})] in
/-- The cocone condition on objects: the stagewise comparison of a transported object is the
stagewise comparison of the object itself. -/
lemma twoFibreProductStage_obj_map {j k : J} (u : j ⟶ k)
    (a : (twoFibreProductDiagram α γ).obj j) :
    (twoFibreProductStage α γ k).obj ((twoFibreProductMap α γ u).obj a) =
      (twoFibreProductStage α γ j).obj a :=
  Functor.congr_obj (twoFibreProductMap_comp_twoFibreProductStage α γ u) a

omit [HasColimit (Y ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    [HasColimit (twoFibreProductDiagram α γ ⋙
    CategoryTheory.nerveFunctor.{max u v w, max u v w})] in
/-- **A morphism between the stagewise comparison images of two objects of one stage is, at a
later stage, the stagewise comparison of a morphism of that stage.** -/
lemma exists_stage_hom_of_twoFibreProductStage (j : J)
    (a b : (twoFibreProductDiagram α γ).obj j)
    (h' : (twoFibreProductStage α γ j).obj a ⟶ (twoFibreProductStage α γ j).obj b) :
    ∃ (k : J) (A B : (twoFibreProductDiagram α γ).obj k) (φ : A ⟶ B),
      (colimit.ι (twoFibreProductDiagram α γ) k).toFunctor.obj A =
        (colimit.ι (twoFibreProductDiagram α γ) j).toFunctor.obj a ∧
      (colimit.ι (twoFibreProductDiagram α γ) k).toFunctor.obj B =
        (colimit.ι (twoFibreProductDiagram α γ) j).toFunctor.obj b ∧
      ∃ (fA : (twoFibreProductStage α γ k).obj A = (twoFibreProductStage α γ j).obj a)
        (fB : (twoFibreProductStage α γ k).obj B = (twoFibreProductStage α γ j).obj b),
        (twoFibreProductStage α γ k).map φ = eqToHom fA ≫ h' ≫ eqToHom fB.symm := by
  obtain ⟨k₁, r₁, gX, hgX⟩ := exists_stage_hom_of_colimit.{u, v, w} X j a.fst b.fst
    (h'.fst : (colimit.ι X j).toFunctor.obj a.fst ⟶ (colimit.ι X j).toFunctor.obj b.fst)
  obtain ⟨k₂, r₂, gZ, hgZ⟩ := exists_stage_hom_of_colimit.{u, v, w} Z k₁
    ((Z.map r₁).toFunctor.obj a.snd) ((Z.map r₁).toFunctor.obj b.snd)
    (eqToHom (colimit_ι_map_obj Z r₁ a.snd) ≫
      (h'.snd : (colimit.ι Z j).toFunctor.obj a.snd ⟶ (colimit.ι Z j).toFunctor.obj b.snd) ≫
      eqToHom (colimit_ι_map_obj Z r₁ b.snd).symm)
  set A₂ := (twoFibreProductMap α γ r₂).obj ((twoFibreProductMap α γ r₁).obj a) with hA₂
  set B₂ := (twoFibreProductMap α γ r₂).obj ((twoFibreProductMap α γ r₁).obj b) with hB₂
  have fA₂ : (twoFibreProductStage α γ k₂).obj A₂ = (twoFibreProductStage α γ j).obj a :=
    (twoFibreProductStage_obj_map.{u, v, w} α γ r₂ _).trans
      (twoFibreProductStage_obj_map.{u, v, w} α γ r₁ a)
  have fB₂ : (twoFibreProductStage α γ k₂).obj B₂ = (twoFibreProductStage α γ j).obj b :=
    (twoFibreProductStage_obj_map.{u, v, w} α γ r₂ _).trans
      (twoFibreProductStage_obj_map.{u, v, w} α γ r₁ b)
  have hcX : (colimit.ι X k₂).toFunctor.map ((X.map r₂).toFunctor.map gX) =
      eqToHom (congrArg CategoricalPullback.fst fA₂) ≫ h'.fst ≫
        eqToHom (congrArg CategoricalPullback.fst fB₂).symm := by
    exact colimit_ι_map_map_eq_conj r₂ gX _ hgX _ _
  have hcZ : (colimit.ι Z k₂).toFunctor.map gZ =
      eqToHom (congrArg CategoricalPullback.snd fA₂) ≫ h'.snd ≫
        eqToHom (congrArg CategoricalPullback.snd fB₂).symm := by
    rw [hgZ]
    exact eqToHom_conj_assoc _ _ _ _ _ _ _
  -- the compatibility condition, read in the colimit and then at the stage
  have hwcolim := categoricalPullback_transport_w fA₂ fB₂ h'
  rw [← hcX, ← hcZ] at hwcolim
  have hwstage := (twoFibreProductStage_hom_w_iff.{u, v, w} α γ k₂ (A := A₂) (B := B₂)
    ((X.map r₂).toFunctor.map gX) gZ).mp hwcolim
  -- filteredness forces the compatibility condition at a stage
  obtain ⟨m, v, hv⟩ := exists_common_stage_eq_of_colimit_ι_map_eq Y k₂
    ((α.app k₂).toFunctor.map ((X.map r₂).toFunctor.map gX) ≫ B₂.iso.hom)
    (A₂.iso.hom ≫ (γ.app k₂).toFunctor.map gZ) hwstage
  have fA : (twoFibreProductStage α γ m).obj ((twoFibreProductMap α γ v).obj A₂) =
      (twoFibreProductStage α γ j).obj a :=
    (twoFibreProductStage_obj_map.{u, v, w} α γ v A₂).trans fA₂
  have fB : (twoFibreProductStage α γ m).obj ((twoFibreProductMap α γ v).obj B₂) =
      (twoFibreProductStage α γ j).obj b :=
    (twoFibreProductStage_obj_map.{u, v, w} α γ v B₂).trans fB₂
  refine ⟨m, (twoFibreProductMap α γ v).obj A₂, (twoFibreProductMap α γ v).obj B₂,
    ⟨(X.map v).toFunctor.map ((X.map r₂).toFunctor.map gX), (Z.map v).toFunctor.map gZ,
      (twoFibreProductMap_hom_w_iff.{u, v, w} α γ v (A := A₂) (B := B₂)
        ((X.map r₂).toFunctor.map gX) gZ).mpr hv⟩,
    ((colimit_ι_map_obj (twoFibreProductDiagram α γ) v A₂).trans
      ((colimit_ι_map_obj (twoFibreProductDiagram α γ) r₂ _).trans
        (colimit_ι_map_obj (twoFibreProductDiagram α γ) r₁ a))),
    ((colimit_ι_map_obj (twoFibreProductDiagram α γ) v B₂).trans
      ((colimit_ι_map_obj (twoFibreProductDiagram α γ) r₂ _).trans
        (colimit_ι_map_obj (twoFibreProductDiagram α γ) r₁ b))),
    fA, fB, ?_⟩
  refine CategoricalPullback.hom_ext ?_ ?_
  · exact (colimit_ι_map_map_eq_conj v _ _ hcX _ _).trans
      (categoricalPullback_eqToHom_conj_fst fA fB.symm h').symm
  · exact (colimit_ι_map_map_eq_conj v gZ _ hcZ _ _).trans
      (categoricalPullback_eqToHom_conj_snd fA fB.symm h').symm

omit [IsFiltered J] in
/-- A composite transition on objects, factored. -/
lemma map_comp_obj {W : J ⥤ Cat.{t, t}} {j k l : J} (r : j ⟶ k) (s : k ⟶ l) (a : W.obj j) :
    (W.map (r ≫ s)).toFunctor.obj a = (W.map s).toFunctor.obj ((W.map r).toFunctor.obj a) :=
  Functor.congr_obj ((congrArg Cat.Hom.toFunctor (W.map_comp r s)).trans
    (Cat.Hom.comp_toFunctor _ _)) a

/-- Two pairs of parallel morphisms of one stage of two filtered diagrams, each pair identified
in the colimit, are identified by one common transition. -/
private lemma exists_common_stage_map_eq₂ (W W' : J ⥤ Cat.{max u v w, max u v w})
    [HasColimit W] [HasColimit W']
    {j : J} {a b : W.obj j} {c d : W'.obj j} (f g : a ⟶ b) (f' g' : c ⟶ d)
    (h : (colimit.ι W j).toFunctor.map f = (colimit.ι W j).toFunctor.map g)
    (h' : (colimit.ι W' j).toFunctor.map f' = (colimit.ι W' j).toFunctor.map g') :
    ∃ (k : J) (u : j ⟶ k), (W.map u).toFunctor.map f = (W.map u).toFunctor.map g ∧
      (W'.map u).toFunctor.map f' = (W'.map u).toFunctor.map g' := by
  obtain ⟨k₁, u₁, h₁⟩ := exists_common_stage_eq_of_colimit_ι_map_eq W j f g h
  obtain ⟨k₂, u₂, h₂⟩ := exists_common_stage_eq_of_colimit_ι_map_eq W' j f' g' h'
  obtain ⟨k, u, v₁, v₂, e₁, e₂⟩ := exists_common_stage_of_two u₁ u₂
  exact ⟨k, u, by rw [e₁]; exact map_comp_eq_of_map_eq u₁ v₁ h₁,
    by rw [e₂]; exact map_comp_eq_of_map_eq u₂ v₂ h₂⟩

/-- **An isomorphism of a filtered colimit in `Cat` between the images of two objects of one
stage is, at a later stage, the image of an isomorphism of that stage.** The inverse is
represented after the isomorphism, and filteredness then forces the two composites to be
identities already at a stage. -/
lemma exists_stage_iso_of_colimit (W : J ⥤ Cat.{max u v w, max u v w}) [HasColimit W]
    [HasColimit (W ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    (j : J) (p q : W.obj j)
    (n : (colimit.ι W j).toFunctor.obj p ≅ (colimit.ι W j).toFunctor.obj q) :
    ∃ (k : J) (r : j ⟶ k) (e : (W.map r).toFunctor.obj p ≅ (W.map r).toFunctor.obj q),
      (colimit.ι W k).toFunctor.map e.hom =
        eqToHom (colimit_ι_map_obj W r p) ≫ n.hom ≫
          eqToHom (colimit_ι_map_obj W r q).symm := by
  obtain ⟨k₁, r₁, g, hg⟩ := exists_stage_hom_of_colimit.{u, v, w} W j p q n.hom
  obtain ⟨k₂, r₂, g', hg'⟩ := exists_stage_hom_of_colimit.{u, v, w} W k₁
    ((W.map r₁).toFunctor.obj q) ((W.map r₁).toFunctor.obj p)
    (eqToHom (colimit_ι_map_obj W r₁ q) ≫ n.inv ≫ eqToHom (colimit_ι_map_obj W r₁ p).symm)
  have A (x : W.obj j) : (colimit.ι W k₂).toFunctor.obj
        ((W.map r₂).toFunctor.obj ((W.map r₁).toFunctor.obj x)) =
      (colimit.ι W j).toFunctor.obj x :=
    (colimit_ι_map_obj W r₂ _).trans (colimit_ι_map_obj W r₁ x)
  have hG : (colimit.ι W k₂).toFunctor.map ((W.map r₂).toFunctor.map g) =
      eqToHom (A p) ≫ n.hom ≫ eqToHom (A q).symm :=
    colimit_ι_map_map_eq_conj r₂ g _ hg _ _
  have hG' : (colimit.ι W k₂).toFunctor.map g' = eqToHom (A q) ≫ n.inv ≫ eqToHom (A p).symm :=
    hg'.trans (eqToHom_conj_assoc _ _ _ _ _ _ _)
  have h₁ : (colimit.ι W k₂).toFunctor.map ((W.map r₂).toFunctor.map g ≫ g') =
      (colimit.ι W k₂).toFunctor.map (𝟙 _) := by
    rw [Functor.map_comp, hG, hG', Functor.map_id]
    exact eqToHom_conj_comp_self (A p) (A q).symm n.hom n.inv n.hom_inv_id
  have h₂ : (colimit.ι W k₂).toFunctor.map (g' ≫ (W.map r₂).toFunctor.map g) =
      (colimit.ι W k₂).toFunctor.map (𝟙 _) := by
    rw [Functor.map_comp, hG, hG', Functor.map_id]
    exact eqToHom_conj_comp_self (A q) (A p).symm n.inv n.hom n.inv_hom_id
  obtain ⟨k, t, H₁, H₂⟩ := exists_common_stage_map_eq₂.{u, v, w} W W _ _ _ _ h₁ h₂
  have E (x : W.obj j) : (W.map (r₁ ≫ r₂ ≫ t)).toFunctor.obj x =
      (W.map t).toFunctor.obj ((W.map r₂).toFunctor.obj ((W.map r₁).toFunctor.obj x)) :=
    (map_comp_obj r₁ (r₂ ≫ t) x).trans (map_comp_obj r₂ t _)
  have B (x : W.obj j) : (colimit.ι W k).toFunctor.obj
        ((W.map t).toFunctor.obj ((W.map r₂).toFunctor.obj ((W.map r₁).toFunctor.obj x))) =
      (colimit.ι W j).toFunctor.obj x :=
    (colimit_ι_map_obj W t _).trans (A x)
  have hE : (colimit.ι W k).toFunctor.map
        ((W.map t).toFunctor.map ((W.map r₂).toFunctor.map g)) =
      eqToHom (B p) ≫ n.hom ≫ eqToHom (B q).symm :=
    colimit_ι_map_map_eq_conj t _ _ hG _ _
  refine ⟨k, r₁ ≫ r₂ ≫ t, eqToIso (E p) ≪≫
    { hom := (W.map t).toFunctor.map ((W.map r₂).toFunctor.map g)
      inv := (W.map t).toFunctor.map g'
      hom_inv_id := by rw [← Functor.map_comp, H₁, Functor.map_id]
      inv_hom_id := by rw [← Functor.map_comp, H₂, Functor.map_id] } ≪≫
    eqToIso (E q).symm, ?_⟩
  change (colimit.ι W k).toFunctor.map (eqToHom (E p) ≫
    (W.map t).toFunctor.map ((W.map r₂).toFunctor.map g) ≫ eqToHom (E q).symm) = _
  refine (map_eqToHom_conj _ _ _ _).trans ?_
  rw [hE]
  exact eqToHom_conj_assoc _ _ _ _ _ _ _

omit [HasColimit (X ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    [HasColimit (Y ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    [HasColimit (Z ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    [HasColimit (twoFibreProductDiagram α γ ⋙
    CategoryTheory.nerveFunctor.{max u v w, max u v w})] in
/-- Two parallel morphisms at a stage of the 2-fibre product diagram whose images under the
stagewise comparison `twoFibreProductStage` into the 2-fibre product of the colimits agree already
have the same image in the colimit of the 2-fibre product diagram. -/
lemma colimit_ι_map_eq_of_twoFibreProductStage_map_eq {j : J}
    {a b : (twoFibreProductDiagram α γ).obj j} {f' g' : a ⟶ b}
    (key : (twoFibreProductStage α γ j).map f' = (twoFibreProductStage α γ j).map g') :
    (colimit.ι (twoFibreProductDiagram α γ) j).toFunctor.map f' =
      (colimit.ι (twoFibreProductDiagram α γ) j).toFunctor.map g' := by
  obtain ⟨k, u, H₁, H₂⟩ := exists_common_stage_map_eq₂.{u, v, w} X Z f'.fst g'.fst f'.snd g'.snd
    (congrArg CategoricalPullback.Hom.fst key) (congrArg CategoricalPullback.Hom.snd key)
  have hD : ((twoFibreProductDiagram α γ).map u).toFunctor.map f' =
      ((twoFibreProductDiagram α γ).map u).toFunctor.map g' :=
    CategoricalPullback.hom_ext H₁ H₂
  have h' := congrArg (colimit.ι (twoFibreProductDiagram α γ) k).toFunctor.map hD
  rw [colimit_ι_map_map u f', colimit_ι_map_map u g'] at h'
  exact (cancel_mono _).mp ((cancel_epi _).mp h')

omit [HasColimit (X ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    [HasColimit (Y ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    [HasColimit (Z ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})] in
/-- **The comparison out of the colimit of a stagewise 2-fibre product is faithful.** -/
theorem faithful_colimitTwoFibreProductComparison :
    (colimitTwoFibreProductComparison α γ).Faithful where
  map_injective {P Q} f g h := by
    obtain ⟨j, a, b, f', g', hx, hy, hf', hg'⟩ :=
      exists_stage_hom_pair_of_colimit.{u, v, w} (twoFibreProductDiagram α γ) f g
    have hcc : ((colimit.ι (twoFibreProductDiagram α γ) j).toFunctor ⋙
          colimitTwoFibreProductComparison α γ).map f' =
        ((colimit.ι (twoFibreProductDiagram α γ) j).toFunctor ⋙
          colimitTwoFibreProductComparison α γ).map g' := by
      rw [Functor.comp_map, Functor.comp_map, hf', hg', Functor.map_comp, Functor.map_comp,
        Functor.map_comp, Functor.map_comp, h]
    have h' := (Functor.congr_hom (colimitTwoFibreProductComparison_ι α γ j) f').symm.trans
      (hcc.trans (Functor.congr_hom (colimitTwoFibreProductComparison_ι α γ j) g'))
    have hι := colimit_ι_map_eq_of_twoFibreProductStage_map_eq.{u, v, w} α γ
      ((cancel_mono _).mp ((cancel_epi _).mp h'))
    rw [hf', hg'] at hι
    exact (cancel_mono (eqToHom hy.symm)).mp ((cancel_epi (eqToHom hx)).mp hι)


omit [HasColimit (Y ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})] in
/-- **The comparison out of the colimit of a stagewise 2-fibre product is full.** -/
theorem full_colimitTwoFibreProductComparison :
    (colimitTwoFibreProductComparison α γ).Full where
  map_surjective {P Q} h := by
    obtain ⟨j, a, b, hx, hy⟩ := exists_common_stage_obj_of_colimit.{u, v, w}
      (twoFibreProductDiagram α γ) P Q
    have ea : (colimitTwoFibreProductComparison α γ).obj
        ((colimit.ι (twoFibreProductDiagram α γ) j).toFunctor.obj a) =
        (twoFibreProductStage α γ j).obj a :=
      Functor.congr_obj (colimitTwoFibreProductComparison_ι α γ j) a
    have eb : (colimitTwoFibreProductComparison α γ).obj
        ((colimit.ι (twoFibreProductDiagram α γ) j).toFunctor.obj b) =
        (twoFibreProductStage α γ j).obj b :=
      Functor.congr_obj (colimitTwoFibreProductComparison_ι α γ j) b
    have pa : (twoFibreProductStage α γ j).obj a =
        (colimitTwoFibreProductComparison α γ).obj P :=
      ea.symm.trans (congrArg (colimitTwoFibreProductComparison α γ).obj hx)
    have pb : (twoFibreProductStage α γ j).obj b =
        (colimitTwoFibreProductComparison α γ).obj Q :=
      eb.symm.trans (congrArg (colimitTwoFibreProductComparison α γ).obj hy)
    obtain ⟨k, A, B, φ, e₁, e₂, f₁, f₂, hφ⟩ :=
      exists_stage_hom_of_twoFibreProductStage.{u, v, w} α γ j a b
        (eqToHom pa ≫ h ≫ eqToHom pb.symm)
    have key : (colimitTwoFibreProductComparison α γ).map
          ((colimit.ι (twoFibreProductDiagram α γ) k).toFunctor.map φ) =
        eqToHom (congrArg (colimitTwoFibreProductComparison α γ).obj (e₁.trans hx)) ≫ h ≫
          eqToHom (congrArg (colimitTwoFibreProductComparison α γ).obj (e₂.trans hy)).symm := by
      refine (Functor.congr_hom (colimitTwoFibreProductComparison_ι α γ k) φ).trans ?_
      rw [hφ]
      exact eqToHom_conj_assoc₃ _ _ _ _ _ _ _ _ _
    refine ⟨eqToHom (e₁.trans hx).symm ≫
      (colimit.ι (twoFibreProductDiagram α γ) k).toFunctor.map φ ≫ eqToHom (e₂.trans hy), ?_⟩
    rw [Functor.map_comp, Functor.map_comp, key, eqToHom_map, eqToHom_map]
    exact eqToHom_conj_cancel _ _ _ _ _

/-- **An object of each of two filtered colimits in `Cat` comes from one common stage.** The two
diagrams are unrelated, so this is not `CategoryTheory.Cat.exists_common_stage_obj_of_colimit`:
the common stage is produced by hand from `CategoryTheory.IsFiltered.max`. -/
lemma exists_common_stage_obj_of_colimit₂ (W W' : J ⥤ Cat.{max u v w, max u v w})
    [HasColimit W] [HasColimit W']
    [HasColimit (W ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    [HasColimit (W' ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    (p : ↑(colimit W)) (q : ↑(colimit W')) :
    ∃ (j : J) (a : W.obj j) (b : W'.obj j),
      (colimit.ι W j).toFunctor.obj a = p ∧ (colimit.ι W' j).toFunctor.obj b = q := by
  obtain ⟨j₁, a, ha⟩ := exists_stage_obj_of_colimit.{u, v, w} W p
  obtain ⟨j₂, b, hb⟩ := exists_stage_obj_of_colimit.{u, v, w} W' q
  exact ⟨IsFiltered.max j₁ j₂, (W.map (IsFiltered.leftToMax j₁ j₂)).toFunctor.obj a,
    (W'.map (IsFiltered.rightToMax j₁ j₂)).toFunctor.obj b,
    (colimit_ι_map_obj W _ a).trans ha, (colimit_ι_map_obj W' _ b).trans hb⟩

omit [HasColimit (twoFibreProductDiagram α γ)] [HasColimit (twoFibreProductDiagram α γ ⋙
    CategoryTheory.nerveFunctor.{max u v w, max u v w})] in
/-- **Every object of the 2-fibre product of the colimits is already the stagewise comparison of
an object of a stage.** The two components are represented at a common stage; the structural
isomorphism of the object is then an isomorphism of the colimit of `𝒴` between the images of two
objects of that stage, so `CategoryTheory.Cat.exists_stage_iso_of_colimit` realises it at a
later stage, and the three data assemble into an object of the 2-fibre product there. -/
lemma exists_stage_obj_of_twoFibreProductStage
    (R : CategoricalPullback (colimMap α).toFunctor (colimMap γ).toFunctor) :
    ∃ (k : J) (A : CategoricalPullback (α.app k).toFunctor (γ.app k).toFunctor),
      (twoFibreProductStage α γ k).obj A = R := by
  obtain ⟨j, x, z, hx, hz⟩ := exists_common_stage_obj_of_colimit₂.{u, v, w} X Z R.fst R.snd
  -- the structural isomorphism of `R`, transported to the stage `j`
  have Aα : (colimit.ι Y j).toFunctor.obj ((α.app j).toFunctor.obj x) =
      (colimMap α).toFunctor.obj R.fst :=
    (Functor.congr_obj ((ι_colimMap_toFunctor α j).symm) x).trans
      (congrArg (colimMap α).toFunctor.obj hx)
  have Aγ : (colimMap γ).toFunctor.obj R.snd =
      (colimit.ι Y j).toFunctor.obj ((γ.app j).toFunctor.obj z) :=
    (congrArg (colimMap γ).toFunctor.obj hz).symm.trans
      (Functor.congr_obj (ι_colimMap_toFunctor γ j) z)
  obtain ⟨k, r, e, he⟩ := exists_stage_iso_of_colimit.{u, v, w} Y j
    ((α.app j).toFunctor.obj x) ((γ.app j).toFunctor.obj z)
    (eqToIso Aα ≪≫ R.iso ≪≫ eqToIso Aγ)
  -- the stage isomorphism, transported across the naturality squares of `α` and `γ`
  have Eα : (Y.map r).toFunctor.obj ((α.app j).toFunctor.obj x) =
      (α.app k).toFunctor.obj ((X.map r).toFunctor.obj x) :=
    Functor.congr_obj ((naturality_toFunctor α r).symm) x
  have Eγ : (γ.app k).toFunctor.obj ((Z.map r).toFunctor.obj z) =
      (Y.map r).toFunctor.obj ((γ.app j).toFunctor.obj z) :=
    Functor.congr_obj (naturality_toFunctor γ r) z
  refine ⟨k, ⟨(X.map r).toFunctor.obj x, (Z.map r).toFunctor.obj z,
    eqToIso Eα.symm ≪≫ e ≪≫ eqToIso Eγ.symm⟩, ?_⟩
  refine categoricalPullback_obj_ext ((colimit_ι_map_obj X r x).trans hx)
    ((colimit_ι_map_obj Z r z).trans hz) ?_
  refine (categoricalPullback_mapEq_obj_iso_hom (α.app k).toFunctor (γ.app k).toFunctor
    (colimit.ι X k).toFunctor (colimit.ι Z k).toFunctor (colimit.ι Y k).toFunctor
    (colimMap α).toFunctor (colimMap γ).toFunctor
    (ι_colimMap_toFunctor γ k) (ι_colimMap_toFunctor α k).symm _).trans ?_
  rw [show (eqToIso Eα.symm ≪≫ e ≪≫ eqToIso Eγ.symm).hom =
    eqToHom Eα.symm ≫ e.hom ≫ eqToHom Eγ.symm from rfl, map_eqToHom_conj, he,
    show (eqToIso Aα ≪≫ R.iso ≪≫ eqToIso Aγ).hom = eqToHom Aα ≫ R.iso.hom ≫ eqToHom Aγ from rfl]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  rfl

omit [HasColimit (twoFibreProductDiagram α γ ⋙
    CategoryTheory.nerveFunctor.{max u v w, max u v w})] in
/-- **The comparison out of the colimit of a stagewise 2-fibre product is essentially
surjective.** -/
theorem essSurj_colimitTwoFibreProductComparison :
    (colimitTwoFibreProductComparison α γ).EssSurj where
  mem_essImage R := by
    obtain ⟨k, A, hA⟩ := exists_stage_obj_of_twoFibreProductStage.{u, v, w} α γ R
    exact ⟨(colimit.ι (twoFibreProductDiagram α γ) k).toFunctor.obj A,
      ⟨eqToIso ((Functor.congr_obj (colimitTwoFibreProductComparison_ι α γ k) A).trans hA)⟩⟩

/-- **Filtered colimits of categories commute with 2-fibre products:** the comparison
`colim (𝒳ⱼ ×_{𝒴ⱼ} 𝒵ⱼ) ⥤ (colim 𝒳ⱼ) ×_{colim 𝒴ⱼ} (colim 𝒵ⱼ)` is an equivalence. -/
theorem isEquivalence_colimitTwoFibreProductComparison :
    (colimitTwoFibreProductComparison α γ).IsEquivalence where
  faithful := faithful_colimitTwoFibreProductComparison.{u, v, w} α γ
  full := full_colimitTwoFibreProductComparison.{u, v, w} α γ
  essSurj := essSurj_colimitTwoFibreProductComparison.{u, v, w} α γ

end Equivalence

end CategoryTheory.Cat

end
