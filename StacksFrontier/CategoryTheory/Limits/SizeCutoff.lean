module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import StacksFrontier.CategoryTheory.CountableCategoryCode

/-!
# Cutting off a category by a size function

Let `C` be a category with hom types in `Type u` and `s : C → Cardinal.{u}` an isomorphism
invariant such that for every `μ` the objects `X` with `s X < μ` form an essentially small
property. This file shows that there is a function `ν` on cardinals such that, for every cardinal
`κ` closed under `ν` and under successors and of uncountable cofinality, the full subcategory
`{X | s X < κ}` computes countable limits and colimits as `C` does:

* a limit in `C` of a countable diagram with values in `{s < κ}` has `s < κ`;
* a cone over such a diagram, with apex in `{s < κ}`, which is terminal among the cones with apex
  in `{s < κ}` is a limit cone in `C`;

and dually for colimits. This is the construction in the proof of Stacks 000J, carried out for an
abstract size function. Countable categories form a set up to equivalence
(`CategoryTheory.CountableCategoryCode`), and so do diagrams in a small model of `{s < μ}` and
cones over them; `ν μ` bounds the sizes of their limits and of witnesses to the failure of a cone
to be a limit cone. The second point is the direction of the comparison which Stacks comment
#608 notes the proof of 000J does not address; closing `κ` under these witnesses settles it.

## Main results

* `CategoryTheory.Limits.exists_sizeCutoff_bound`: the function `ν` and the four properties.
-/

@[expose] public section

open CategoryTheory Limits Cardinal Opposite Order

universe w v u' u

namespace CategoryTheory.Limits

section Transfer

variable {D : Type*} [Category* D] {D' : Type*} [Category* D']

/-- An object is terminal exactly when every object has a unique morphism to it. -/
theorem nonempty_isTerminal_iff_forall_unique (d : D) :
    Nonempty (IsTerminal d) ↔ ∀ t : D, Nonempty (Unique (t ⟶ d)) :=
  ⟨fun ⟨h⟩ t => ⟨⟨⟨h.from t⟩, fun _ => h.hom_ext _ _⟩⟩, fun h =>
    ⟨IsTerminal.ofUniqueHom (fun t => (h t).some.default) fun t m => (h t).some.uniq m⟩⟩

/-- An object is initial exactly when it has a unique morphism to every object. -/
theorem nonempty_isInitial_iff_forall_unique (d : D) :
    Nonempty (IsInitial d) ↔ ∀ t : D, Nonempty (Unique (d ⟶ t)) :=
  ⟨fun ⟨h⟩ t => ⟨⟨⟨h.to t⟩, fun _ => h.hom_ext _ _⟩⟩, fun h =>
    ⟨IsInitial.ofUniqueHom (fun t => (h t).some.default) fun t m => (h t).some.uniq m⟩⟩

/-- The property "every object satisfying `p` has a unique morphism to `d`" is carried along an
equivalence of categories, for an isomorphism-invariant `p`. -/
theorem forall_unique_hom_iff_of_equivalence (K : D ≌ D') (p : D → Prop) (p' : D' → Prop)
    (hp : ∀ t, p' (K.functor.obj t) ↔ p t) (hp' : ∀ {t t' : D'}, (t ≅ t') → p' t → p' t')
    {d : D} {d' : D'} (e : K.functor.obj d ≅ d') :
    (∀ t, p t → Nonempty (Unique (t ⟶ d))) ↔ ∀ t', p' t' → Nonempty (Unique (t' ⟶ d')) := by
  constructor
  · intro h t' ht'
    have ht : p (K.inverse.obj t') := (hp _).1 (hp' (K.counitIso.app t').symm ht')
    obtain ⟨u⟩ := h _ ht
    exact ⟨((Iso.homCongr (K.counitIso.app t') e).symm.trans
      K.fullyFaithfulFunctor.homEquiv.symm).unique⟩
  · intro h t ht
    obtain ⟨u⟩ := h _ ((hp t).2 ht)
    exact ⟨(K.fullyFaithfulFunctor.homEquiv.trans (Iso.homCongr (Iso.refl _) e)).unique⟩

end Transfer

variable {C : Type u'} [Category.{u} C] (s : C → Cardinal.{u})

/-- The objects `X` with `s X < μ`. -/
abbrev sizeLT (μ : Cardinal.{u}) : ObjectProperty C := fun X => s X < μ

section Bound

variable [∀ μ : Cardinal.{u}, ObjectProperty.EssentiallySmall.{u} (sizeLT s μ)]

theorem essentiallySmall_sizeLT_fullSubcategory (μ : Cardinal.{u}) :
    EssentiallySmall.{u} (sizeLT s μ).FullSubcategory :=
  inferInstance

/-- A small model of the full subcategory of objects `X` with `s X < μ`. -/
def SizeLTModel (μ : Cardinal.{u}) : Type u :=
  @SmallModel _ _ (essentiallySmall_sizeLT_fullSubcategory s μ)

noncomputable instance (μ : Cardinal.{u}) : SmallCategory (SizeLTModel s μ) :=
  @smallCategorySmallModel _ _ (essentiallySmall_sizeLT_fullSubcategory s μ)

/-- The equivalence of `{s < μ}` with its small model. -/
noncomputable abbrev sizeLTEquiv (μ : Cardinal.{u}) :
    (sizeLT s μ).FullSubcategory ≌ SizeLTModel s μ :=
  @equivSmallModel _ _ (essentiallySmall_sizeLT_fullSubcategory s μ)

/-- The fully faithful functor from the small model of `{s < μ}` to `C`. -/
noncomputable abbrev sizeLTModelι (μ : Cardinal.{u}) : SizeLTModel s μ ⥤ C :=
  (sizeLTEquiv s μ).inverse ⋙ (sizeLT s μ).ι

open scoped Classical in
/-- A bound for `s` of the limits in `C` of diagrams indexed by codes of countable categories
with values in the small model of `{s < μ}`. -/
noncomputable def limitSizeBound (μ : Cardinal.{u}) : Cardinal.{u} :=
  ⨆ x : Σ c : CountableCategoryCode, c.Obj ⥤ SizeLTModel s μ,
    if _ : HasLimit (x.2 ⋙ sizeLTModelι s μ) then s (limit (x.2 ⋙ sizeLTModelι s μ)) else 0

open scoped Classical in
/-- A bound for `s` of witnesses that a cone over a diagram indexed by the code of a countable
category, in the small model of `{s < μ}`, is not a limit cone in `C`. -/
noncomputable def coneWitnessSizeBound (μ : Cardinal.{u}) : Cardinal.{u} :=
  ⨆ x : Σ c : CountableCategoryCode, Σ G : c.Obj ⥤ SizeLTModel s μ, Cone G,
    if h : ∃ t : Cone (x.2.1 ⋙ sizeLTModelι s μ),
        ¬ Nonempty (Unique (t ⟶ (sizeLTModelι s μ).mapCone x.2.2)) then
      s h.choose.pt else 0

variable {s}

/-- A diagram with values in `{s < μ}` factors through the small model up to isomorphism. -/
theorem exists_iso_sizeLTModelι {J : Type*} [Category* J] {μ : Cardinal.{u}} (F : J ⥤ C)
    (hF : ∀ j, s (F.obj j) < μ) : ∃ G : J ⥤ SizeLTModel s μ, Nonempty (G ⋙ sizeLTModelι s μ ≅ F) :=
  ⟨(sizeLT s μ).lift F hF ⋙ (sizeLTEquiv s μ).functor,
    ⟨Functor.associator ((sizeLT s μ).lift F hF) (sizeLTEquiv s μ).functor (sizeLTModelι s μ) ≪≫
      Functor.isoWhiskerLeft ((sizeLT s μ).lift F hF)
        ((Functor.associator (sizeLTEquiv s μ).functor (sizeLTEquiv s μ).inverse
          (sizeLT s μ).ι).symm ≪≫
        Functor.isoWhiskerRight (sizeLTEquiv s μ).unitIso.symm (sizeLT s μ).ι ≪≫
          Functor.leftUnitor (sizeLT s μ).ι) ≪≫
      (sizeLT s μ).liftCompιIso F hF⟩⟩

/-- An object in `{s < μ}` is isomorphic to an object of the small model. -/
theorem exists_iso_sizeLTModelι_obj {μ : Cardinal.{u}} (X : C) (hX : s X < μ) :
    ∃ Y : SizeLTModel s μ, Nonempty ((sizeLTModelι s μ).obj Y ≅ X) :=
  ⟨(sizeLTEquiv s μ).functor.obj ⟨X, hX⟩,
    ⟨(sizeLT s μ).ι.mapIso ((sizeLTEquiv s μ).unitIso.app ⟨X, hX⟩).symm⟩⟩

/-- A countable family of cardinals below `κ` and one more cardinal below `κ` are all below some
`μ < κ`. -/
theorem exists_lt_forall_lt_of_countable {κ : Cardinal.{u}} (hsucc : ∀ μ < κ, succ μ < κ)
    (hcof : ℵ₀ < κ.ord.cof) {ι : Type} [Countable ι] (f : ι → Cardinal.{u}) (hf : ∀ i, f i < κ)
    {b : Cardinal.{u}} (hb : b < κ) : ∃ μ < κ, b < μ ∧ ∀ i, f i < μ := by
  have hbdd : BddAbove (Set.range f) := bddAbove_of_small
  have hsup : ⨆ i, f i < κ := by
    rw [← (Equiv.ulift.{u} (α := ι)).iSup_comp]
    exact iSup_lt_of_lt_cof_ord (mk_le_aleph0.trans_lt hcof) fun i => hf _
  refine ⟨succ (max b (⨆ i, f i)), hsucc _ (max_lt hb hsup), lt_succ_of_le (le_max_left _ _),
    fun i => lt_succ_of_le ((le_ciSup hbdd i).trans (le_max_right _ _))⟩

private theorem pos_of_aleph0_lt_cof {κ : Cardinal.{u}} (hcof : ℵ₀ < κ.ord.cof) :
    (0 : Cardinal.{u}) < κ :=
  aleph0_pos.trans (hcof.trans_le ((Ordinal.cof_le_card _).trans_eq (card_ord κ)))

variable (hs : ∀ {X Y : C}, (X ≅ Y) → s X = s Y) {κ : Cardinal.{u}}
  (hsucc : ∀ μ < κ, succ μ < κ) (hcof : ℵ₀ < κ.ord.cof)
include hs hsucc hcof

/-- The limit of a diagram indexed by the code of a countable category with values in `{s < κ}`
lies in `{s < κ}`, if `κ` is closed under `limitSizeBound s`. -/
theorem size_limit_lt_of_code (hκ : ∀ μ < κ, limitSizeBound s μ < κ) (c : CountableCategoryCode)
    (F : c.Obj ⥤ C) (hF : ∀ j, s (F.obj j) < κ) [HasLimit F] : s (limit F) < κ := by
  obtain ⟨μ, hμ, -, hFμ⟩ :=
    exists_lt_forall_lt_of_countable hsucc hcof _ hF (pos_of_aleph0_lt_cof hcof)
  obtain ⟨G, ⟨α⟩⟩ := exists_iso_sizeLTModelι F hFμ
  have : HasLimit (G ⋙ sizeLTModelι s μ) := hasLimit_of_iso α.symm
  refine lt_of_eq_of_lt (hs (HasLimit.isoOfNatIso α.symm)) (lt_of_le_of_lt ?_ (hκ μ hμ))
  refine le_ciSup_of_le bddAbove_of_small ⟨c, G⟩ ?_
  dsimp only
  split_ifs with h'
  · exact le_rfl
  · exact absurd ‹HasLimit (G ⋙ sizeLTModelι s μ)› h'

/-- Let `F` be a diagram indexed by the code of a countable category with values in `{s < κ}`, and
`d` a cone over `F` with apex in `{s < κ}` such that every cone over `F` with apex in `{s < κ}`
has a unique morphism to `d`. If `κ` is closed under `coneWitnessSizeBound s`, then every cone over
`F` has a unique morphism to `d`. -/
theorem forall_unique_of_code (hκ : ∀ μ < κ, coneWitnessSizeBound s μ < κ)
    (c : CountableCategoryCode) (F : c.Obj ⥤ C) (hF : ∀ j, s (F.obj j) < κ) (d : Cone F)
    (hd : s d.pt < κ) (h : ∀ t : Cone F, s t.pt < κ → Nonempty (Unique (t ⟶ d))) :
    ∀ t : Cone F, Nonempty (Unique (t ⟶ d)) := by
  obtain ⟨μ, hμ, hdμ, hFμ⟩ := exists_lt_forall_lt_of_countable hsucc hcof _ hF hd
  obtain ⟨G, ⟨α⟩⟩ := exists_iso_sizeLTModelι F hFμ
  obtain ⟨Y, ⟨β⟩⟩ := exists_iso_sizeLTModelι_obj d.pt hdμ
  let d₀ : Cone G :=
    { pt := Y
      π :=
        { app := fun j => (sizeLTModelι s μ).preimage (β.hom ≫ d.π.app j ≫ α.inv.app j)
          naturality := fun j k f => (sizeLTModelι s μ).map_injective (by
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Functor.map_comp, Functor.map_preimage, Category.assoc]
            rw [show (sizeLTModelι s μ).map (G.map f) = (G ⋙ sizeLTModelι s μ).map f from rfl,
              ← α.inv.naturality, ← Category.assoc (d.π.app j), d.w f]) } }
  let K := Cone.postcomposeEquivalence α
  have e : K.functor.obj ((sizeLTModelι s μ).mapCone d₀) ≅ d :=
    Cone.ext β fun j => by
      change (sizeLTModelι s μ).map ((sizeLTModelι s μ).preimage
        (β.hom ≫ d.π.app j ≫ α.inv.app j)) ≫ α.hom.app j = β.hom ≫ d.π.app j
      rw [Functor.map_preimage]
      simp
  have hiso : ∀ {t t' : Cone F}, (t ≅ t') → s t.pt < κ → s t'.pt < κ := fun i ht =>
    lt_of_eq_of_lt (hs ((Cone.forget F).mapIso i)).symm ht
  have hd₀ : ∀ t : Cone (G ⋙ sizeLTModelι s μ), s t.pt < κ →
      Nonempty (Unique (t ⟶ (sizeLTModelι s μ).mapCone d₀)) :=
    (forall_unique_hom_iff_of_equivalence K (fun t => s t.pt < κ) (fun t => s t.pt < κ)
      (fun _ => Iff.rfl) hiso e).2 h
  have hall : ∀ t : Cone (G ⋙ sizeLTModelι s μ),
      Nonempty (Unique (t ⟶ (sizeLTModelι s μ).mapCone d₀)) := by
    by_contra hne
    have hx : ∃ t : Cone (G ⋙ sizeLTModelι s μ),
        ¬ Nonempty (Unique (t ⟶ (sizeLTModelι s μ).mapCone d₀)) := not_forall.1 hne
    have hw : s hx.choose.pt < κ := by
      refine lt_of_le_of_lt ?_ (hκ μ hμ)
      refine le_ciSup_of_le bddAbove_of_small ⟨c, G, d₀⟩ ?_
      dsimp only
      split_ifs with h'
      · exact le_rfl
      · exact absurd hx h'
    exact hx.choose_spec (hd₀ _ hw)
  intro t
  exact (forall_unique_hom_iff_of_equivalence K (fun _ => True) (fun _ => True)
    (fun _ => Iff.rfl) (fun _ h => h) e).1 (fun t _ => hall t) t trivial

/-- The limit of a countable diagram with values in `{s < κ}` lies in `{s < κ}`, if `κ` is closed
under `limitSizeBound s`. -/
theorem size_limit_lt (hκ : ∀ μ < κ, limitSizeBound s μ < κ) {J : Type v} [Category.{w} J]
    [CountableCategory J] (F : J ⥤ C) (hF : ∀ j, s (F.obj j) < κ) [HasLimit F] :
    s (limit F) < κ := by
  let E := CountableCategoryCode.equivOfCountable J
  have hl : IsLimit ((limit.cone F).whisker E.functor) := (limit.isLimit F).whiskerEquivalence E
  have : HasLimit (E.functor ⋙ F) := HasLimit.mk ⟨_, hl⟩
  exact lt_of_eq_of_lt (hs (hl.conePointUniqueUpToIso (limit.isLimit _)))
    (size_limit_lt_of_code hs hsucc hcof hκ _ _ fun j => hF _)

/-- Let `F` be a countable diagram with values in `{s < κ}`, and `d` a cone over `F` with apex in
`{s < κ}` such that every cone over `F` with apex in `{s < κ}` has a unique morphism to `d`. If `κ`
is closed under `coneWitnessSizeBound s`, then every cone over `F` has a unique morphism
to `d`. -/
theorem forall_unique_of_forall_unique_lt (hκ : ∀ μ < κ, coneWitnessSizeBound s μ < κ)
    {J : Type v} [Category.{w} J] [CountableCategory J] (F : J ⥤ C) (hF : ∀ j, s (F.obj j) < κ)
    (d : Cone F) (hd : s d.pt < κ) (h : ∀ t : Cone F, s t.pt < κ → Nonempty (Unique (t ⟶ d))) :
    ∀ t : Cone F, Nonempty (Unique (t ⟶ d)) := by
  let E := CountableCategoryCode.equivOfCountable J
  let K := Cone.whiskeringEquivalence (F := F) E
  have hiso : ∀ {t t' : Cone (E.functor ⋙ F)}, (t ≅ t') → s t.pt < κ → s t'.pt < κ :=
    fun i ht => lt_of_eq_of_lt (hs ((Cone.forget _).mapIso i)).symm ht
  have h' := (forall_unique_hom_iff_of_equivalence K (fun t => s t.pt < κ)
    (fun t => s t.pt < κ) (fun _ => Iff.rfl) hiso (Iso.refl _)).1 h
  have hall := forall_unique_of_code hs hsucc hcof hκ _ (E.functor ⋙ F) (fun j => hF _)
    (K.functor.obj d) hd h'
  intro t
  exact (forall_unique_hom_iff_of_equivalence K (fun _ => True) (fun _ => True)
    (fun _ => Iff.rfl) (fun _ h => h) (Iso.refl _)).2 (fun t _ => hall t) t trivial

omit hs hsucc hcof in
/-- If every `{s < μ}` is essentially small, so is every `{s ∘ unop < μ}` in `Cᵒᵖ`. -/
instance essentiallySmall_sizeLT_unop (μ : Cardinal.{u}) :
    ObjectProperty.EssentiallySmall.{u} (sizeLT (fun X : Cᵒᵖ => s X.unop) μ) :=
  (ObjectProperty.essentiallySmall_op_iff (sizeLT s μ)).2 inferInstance

/-- The colimit of a countable diagram with values in `{s < κ}` lies in `{s < κ}`, if `κ` is
closed under `limitSizeBound` of the opposite size function. -/
theorem size_colimit_lt (hκ : ∀ μ < κ, limitSizeBound (fun X : Cᵒᵖ => s X.unop) μ < κ)
    {J : Type v} [Category.{w} J] [CountableCategory J] (F : J ⥤ C) (hF : ∀ j, s (F.obj j) < κ)
    [HasColimit F] : s (colimit F) < κ :=
  lt_of_eq_of_lt (hs (limitOpIsoOpColimit F).unop)
    (size_limit_lt (s := fun X : Cᵒᵖ => s X.unop) (fun e => (hs e.unop).symm) hsucc hcof hκ
      F.op fun j => hF j.unop)

/-- Let `F` be a countable diagram with values in `{s < κ}`, and `d` a cocone under `F` with apex
in `{s < κ}` with a unique morphism to every cocone under `F` with apex in `{s < κ}`. If `κ` is
closed under `coneWitnessSizeBound` of the opposite size function, then `d` has a unique morphism
to every cocone under `F`. -/
theorem forall_unique_of_forall_unique_lt_cocone
    (hκ : ∀ μ < κ, coneWitnessSizeBound (fun X : Cᵒᵖ => s X.unop) μ < κ)
    {J : Type v} [Category.{w} J] [CountableCategory J] (F : J ⥤ C) (hF : ∀ j, s (F.obj j) < κ)
    (d : Cocone F) (hd : s d.pt < κ)
    (h : ∀ t : Cocone F, s t.pt < κ → Nonempty (Unique (d ⟶ t))) :
    ∀ t : Cocone F, Nonempty (Unique (d ⟶ t)) := by
  let K : (Cocone F)ᵒᵖ ≌ Cone F.op :=
    (coconeEquivalenceOpConeOp F).op.trans (opOpEquivalence _)
  have hop : ∀ t : (Cocone F)ᵒᵖ, s t.unop.pt < κ → Nonempty (Unique (t ⟶ op d)) :=
    fun t ht => (h t.unop ht).map fun u => @Equiv.unique _ _ u (opEquiv t (op d))
  have hiso : ∀ {t t' : Cone F.op}, (t ≅ t') → s t.pt.unop < κ → s t'.pt.unop < κ :=
    fun i ht => lt_of_eq_of_lt (hs ((Cone.forget _).mapIso i).unop) ht
  have h' := (forall_unique_hom_iff_of_equivalence K (fun t => s t.unop.pt < κ)
    (fun t => s t.pt.unop < κ) (fun _ => Iff.rfl) hiso (Iso.refl _)).1 hop
  have hall := forall_unique_of_forall_unique_lt (s := fun X : Cᵒᵖ => s X.unop)
    (fun e => (hs e.unop).symm) hsucc hcof hκ F.op (fun j => hF j.unop) d.op hd h'
  have hall' := (forall_unique_hom_iff_of_equivalence K (fun _ => True) (fun _ => True)
    (fun _ => Iff.rfl) (fun _ h => h) (Iso.refl _)).2 (fun t _ => hall t)
  intro t
  exact (hall' (op t) trivial).map fun u => @Equiv.unique _ _ u (opEquiv (op t) (op d)).symm

end Bound

section Main

variable {s}

/-- **The size cutoff of a category.** Let `s` be an isomorphism-invariant size function on `C`
such that each `{s < μ}` is essentially small. There is a function `ν` on cardinals such that for
every cardinal `κ` closed under `ν` and under successors and of uncountable cofinality, and every
countable diagram `F` with values in `{s < κ}`:
* a limit of `F` lies in `{s < κ}`;
* a cone over `F` with apex in `{s < κ}` to which every cone with apex in `{s < κ}` has a unique
  morphism is a limit cone;
* a colimit of `F` lies in `{s < κ}`;
* a cocone under `F` with apex in `{s < κ}` which has a unique morphism to every cocone with apex
  in `{s < κ}` is a colimit cocone. -/
theorem exists_sizeCutoff_bound (hs : ∀ {X Y : C}, (X ≅ Y) → s X = s Y)
    [∀ μ : Cardinal.{u}, ObjectProperty.EssentiallySmall.{u} (sizeLT s μ)] :
    ∃ ν : Cardinal.{u} → Cardinal.{u}, ∀ κ : Cardinal.{u}, (∀ μ < κ, succ μ < κ) →
      ℵ₀ < κ.ord.cof → (∀ μ < κ, ν μ < κ) →
      ∀ (J : Type v) [Category.{w} J] [CountableCategory J] (F : J ⥤ C),
        (∀ j, s (F.obj j) < κ) →
        (∀ [HasLimit F], s (limit F) < κ) ∧
        (∀ d : Cone F, s d.pt < κ → (∀ t : Cone F, s t.pt < κ → Nonempty (Unique (t ⟶ d))) →
          Nonempty (IsLimit d)) ∧
        (∀ [HasColimit F], s (colimit F) < κ) ∧
        (∀ d : Cocone F, s d.pt < κ →
          (∀ t : Cocone F, s t.pt < κ → Nonempty (Unique (d ⟶ t))) →
          Nonempty (IsColimit d)) := by
  refine ⟨fun μ => max (max (limitSizeBound s μ) (coneWitnessSizeBound s μ))
    (max (limitSizeBound (fun X : Cᵒᵖ => s X.unop) μ)
      (coneWitnessSizeBound (fun X : Cᵒᵖ => s X.unop) μ)), fun κ hsucc hcof hν J _ _ F hF => ?_⟩
  have h1 : ∀ μ < κ, limitSizeBound s μ < κ := fun μ hμ =>
    (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt (hν μ hμ))
  have h2 : ∀ μ < κ, coneWitnessSizeBound s μ < κ := fun μ hμ =>
    (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt (hν μ hμ))
  have h3 : ∀ μ < κ, limitSizeBound (fun X : Cᵒᵖ => s X.unop) μ < κ := fun μ hμ =>
    (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt (hν μ hμ))
  have h4 : ∀ μ < κ, coneWitnessSizeBound (fun X : Cᵒᵖ => s X.unop) μ < κ := fun μ hμ =>
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt (hν μ hμ))
  refine ⟨size_limit_lt hs hsucc hcof h1 F hF, fun d hd h => ?_,
    size_colimit_lt hs hsucc hcof h3 F hF, fun d hd h => ?_⟩
  · exact ⟨(Cone.isLimitEquivIsTerminal d).symm
      ((nonempty_isTerminal_iff_forall_unique d).2
        (forall_unique_of_forall_unique_lt hs hsucc hcof h2 F hF d hd h)).some⟩
  · exact ⟨(Cocone.isColimitEquivIsInitial d).symm
      ((nonempty_isInitial_iff_forall_unique d).2
        (forall_unique_of_forall_unique_lt_cocone hs hsucc hcof h4 F hF d hd h)).some⟩

end Main

end CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

section FullSubcategory

variable {C : Type u'} [Category.{u} C] {J : Type v} [Category.{w} J] (P : ObjectProperty C)

/-- A cone over `F ⋙ P.ι` with apex satisfying `P`, viewed as a cone over `F` in the full
subcategory. -/
@[simps]
def liftConeι {F : J ⥤ P.FullSubcategory} (t : Cone (F ⋙ P.ι)) (ht : P t.pt) :
    Cone F where
  pt := ⟨t.pt, ht⟩
  π :=
    { app := fun j => ObjectProperty.homMk (t.π.app j)
      naturality := fun j k f => by
        ext
        simpa using (t.w f).symm }

/-- A cocone under `F ⋙ P.ι` with apex satisfying `P`, viewed as a cocone under `F` in the full
subcategory. -/
@[simps]
def liftCoconeι {F : J ⥤ P.FullSubcategory} (t : Cocone (F ⋙ P.ι))
    (ht : P t.pt) : Cocone F where
  pt := ⟨t.pt, ht⟩
  ι :=
    { app := fun j => ObjectProperty.homMk (t.ι.app j)
      naturality := fun j k f => by
        ext
        simpa using t.w f }

/-- If every cone over `F ⋙ P.ι` with apex in `P` that is terminal among such cones is a limit
cone, then `P.ι` preserves the limit of `F`. -/
theorem preservesLimit_ι_of_forall_unique (F : J ⥤ P.FullSubcategory) [HasLimit F]
    (h : ∀ d : Cone (F ⋙ P.ι), P d.pt →
      (∀ t : Cone (F ⋙ P.ι), P t.pt → Nonempty (Unique (t ⟶ d))) → Nonempty (IsLimit d)) :
    PreservesLimit F P.ι := by
  have hu : ∀ t : Cone (F ⋙ P.ι), P t.pt →
      Nonempty (Unique (t ⟶ P.ι.mapCone (limit.cone F))) := by
    intro t ht
    have e : P.ι.mapCone (liftConeι P t ht) ≅ t := Cone.ext (Iso.refl _) fun j =>
      (Category.id_comp (t.π.app j)).symm
    obtain ⟨u⟩ := (nonempty_isTerminal_iff_forall_unique _).1
      ⟨Cone.isLimitEquivIsTerminal _ (limit.isLimit F)⟩ (liftConeι P t ht)
    exact ⟨@Equiv.unique _ _ u ((Iso.homCongr e (Iso.refl _)).symm.trans
      (Functor.FullyFaithful.ofFullyFaithful (Cone.functoriality F P.ι)).homEquiv.symm)⟩
  obtain ⟨hl⟩ := h _ (limit F).property hu
  exact preservesLimit_of_preserves_limit_cone (limit.isLimit F) hl

/-- If every cocone under `F ⋙ P.ι` with apex in `P` that is initial among such cocones is a
colimit cocone, then `P.ι` preserves the colimit of `F`. -/
theorem preservesColimit_ι_of_forall_unique (F : J ⥤ P.FullSubcategory)
    [HasColimit F]
    (h : ∀ d : Cocone (F ⋙ P.ι), P d.pt →
      (∀ t : Cocone (F ⋙ P.ι), P t.pt → Nonempty (Unique (d ⟶ t))) → Nonempty (IsColimit d)) :
    PreservesColimit F P.ι := by
  have hu : ∀ t : Cocone (F ⋙ P.ι), P t.pt →
      Nonempty (Unique (P.ι.mapCocone (colimit.cocone F) ⟶ t)) := by
    intro t ht
    have e : P.ι.mapCocone (liftCoconeι P t ht) ≅ t := Cocone.ext (Iso.refl _) fun j =>
      Category.comp_id (t.ι.app j)
    obtain ⟨u⟩ := (nonempty_isInitial_iff_forall_unique _).1
      ⟨Cocone.isColimitEquivIsInitial _ (colimit.isColimit F)⟩ (liftCoconeι P t ht)
    exact ⟨@Equiv.unique _ _ u ((Iso.homCongr (Iso.refl _) e).symm.trans
      (Functor.FullyFaithful.ofFullyFaithful (Cocone.functoriality F P.ι)).homEquiv.symm)⟩
  obtain ⟨hl⟩ := h _ (colimit F).property hu
  exact preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F) hl

/-- Let `F` be a diagram in the full subcategory `P`. Suppose a limit of `F ⋙ P.ι` lies in `P`,
and a cone over `F ⋙ P.ι` with apex in `P` that is terminal among such cones is a limit cone. Then
`F` has a limit if and only if `F ⋙ P.ι` has one, and then the comparison morphism
`P.ι.obj (limit F) ⟶ limit (F ⋙ P.ι)` is an isomorphism. -/
theorem hasLimit_iff_and_isIso_limit_post (F : J ⥤ P.FullSubcategory)
    (hl : ∀ [HasLimit (F ⋙ P.ι)], P (limit (F ⋙ P.ι)))
    (h : ∀ d : Cone (F ⋙ P.ι), P d.pt →
      (∀ t : Cone (F ⋙ P.ι), P t.pt → Nonempty (Unique (t ⟶ d))) → Nonempty (IsLimit d)) :
    (HasLimit F ↔ HasLimit (F ⋙ P.ι)) ∧
      ∀ [HasLimit F] [HasLimit (F ⋙ P.ι)], IsIso (limit.post F P.ι) := by
  refine ⟨⟨fun _ => ?_, fun _ => ?_⟩, ?_⟩
  · have := P.preservesLimit_ι_of_forall_unique F h
    exact HasLimit.mk ⟨_, isLimitOfPreserves P.ι (limit.isLimit F)⟩
  · have := createsLimitFullSubcategoryInclusion F hl
    exact hasLimit_of_created F P.ι
  · intro _ _
    have := P.preservesLimit_ι_of_forall_unique F h
    infer_instance

/-- Let `F` be a diagram in the full subcategory `P`. Suppose a colimit of `F ⋙ P.ι` lies in `P`,
and a cocone under `F ⋙ P.ι` with apex in `P` that is initial among such cocones is a colimit
cocone. Then `F` has a colimit if and only if `F ⋙ P.ι` has one, and then the comparison morphism
`colimit (F ⋙ P.ι) ⟶ P.ι.obj (colimit F)` is an isomorphism. -/
theorem hasColimit_iff_and_isIso_colimit_post (F : J ⥤ P.FullSubcategory)
    (hl : ∀ [HasColimit (F ⋙ P.ι)], P (colimit (F ⋙ P.ι)))
    (h : ∀ d : Cocone (F ⋙ P.ι), P d.pt →
      (∀ t : Cocone (F ⋙ P.ι), P t.pt → Nonempty (Unique (d ⟶ t))) → Nonempty (IsColimit d)) :
    (HasColimit F ↔ HasColimit (F ⋙ P.ι)) ∧
      ∀ [HasColimit F] [HasColimit (F ⋙ P.ι)], IsIso (colimit.post F P.ι) := by
  refine ⟨⟨fun _ => ?_, fun _ => ?_⟩, ?_⟩
  · have := P.preservesColimit_ι_of_forall_unique F h
    exact HasColimit.mk ⟨_, isColimitOfPreserves P.ι (colimit.isColimit F)⟩
  · have := createsColimitFullSubcategoryInclusion F hl
    exact hasColimit_of_created F P.ι
  · intro _ _
    have := P.preservesColimit_ι_of_forall_unique F h
    infer_instance

end FullSubcategory

end CategoryTheory.ObjectProperty
