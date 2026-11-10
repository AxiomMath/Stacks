module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward.OverSiteDisjointCover
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward.OverSiteDisjointCover

/-!
# Splittings of finite étale morphisms and the split direct image

Auxiliary material for Stacks 095B: splittings of a morphism `f : X ⟶ Y` over an object `V` of
the small étale site of `Y` (a decomposition of the base change into sheets mapping
isomorphically to `V`), the identification of the restricted direct image over a split object
with the finite product of the restrictions along the sheets, and the existence of an étale
covering by split objects for a finite étale morphism (Tag 04HN).

## References

* [Stacks Project, Tag 095B](https://stacks.math.columbia.edu/tag/095B)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.ConstantSheaf

section Splittings

open CategoryTheory.Limits

/-- The section of the base change of `f` along `V.hom` determined by a morphism
`σ : V.left ⟶ X` over `Y`. -/
private def pullbackSection {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale)
    (σ : V.left ⟶ X) (hσ : σ ≫ f = V.hom) : V.left ⟶ pullback V.hom f :=
  pullback.lift (𝟙 V.left) σ (by simp [hσ])

@[simp, reassoc (attr := simp)]
private lemma pullbackSection_fst {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale)
    (σ : V.left ⟶ X) (hσ : σ ≫ f = V.hom) :
    pullbackSection f V σ hσ ≫ pullback.fst V.hom f = 𝟙 _ :=
  pullback.lift_fst _ _ _

@[simp, reassoc (attr := simp)]
private lemma pullbackSection_snd {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale)
    (σ : V.left ⟶ X) (hσ : σ ≫ f = V.hom) :
    pullbackSection f V σ hσ ≫ pullback.snd V.hom f = σ :=
  pullback.lift_snd _ _ _

/-- Sections determined by equal morphisms agree. -/
private lemma pullbackSection_congr {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale)
    {σ σ' : V.left ⟶ X} (hσ : σ ≫ f = V.hom) (hσ' : σ' ≫ f = V.hom) (hσσ' : σ = σ') :
    pullbackSection f V σ hσ = pullbackSection f V σ' hσ' := by
  subst hσσ'
  rfl

/-- The comparison morphism between the base changes of `f` to `V'` and to `V`, for a
morphism `V' ⟶ V` of the small étale site of `Y`. -/
private def pullbackComap {X Y : Scheme.{u}} (f : X ⟶ Y) {V V' : Y.Etale} (h : V' ⟶ V) :
    pullback V'.hom f ⟶ pullback V.hom f :=
  pullback.lift (pullback.fst V'.hom f ≫ h.left) (pullback.snd V'.hom f) (by
    rw [Category.assoc, MorphismProperty.Over.w h, pullback.condition])

@[simp, reassoc (attr := simp)]
private lemma pullbackComap_fst {X Y : Scheme.{u}} (f : X ⟶ Y) {V V' : Y.Etale} (h : V' ⟶ V) :
    pullbackComap f h ≫ pullback.fst V.hom f = pullback.fst V'.hom f ≫ h.left :=
  pullback.lift_fst _ _ _

@[simp, reassoc (attr := simp)]
private lemma pullbackComap_snd {X Y : Scheme.{u}} (f : X ⟶ Y) {V V' : Y.Etale} (h : V' ⟶ V) :
    pullbackComap f h ≫ pullback.snd V.hom f = pullback.snd V'.hom f :=
  pullback.lift_snd _ _ _

/-- The section determined by `σ` base-changes to the section determined by `h.left ≫ σ`. -/
private lemma pullbackSection_comap {X Y : Scheme.{u}} (f : X ⟶ Y) {V V' : Y.Etale}
    (h : V' ⟶ V) (σ : V.left ⟶ X) (hσ : σ ≫ f = V.hom)
    (hσ' : (h.left ≫ σ) ≫ f = V'.hom) :
    pullbackSection f V' (h.left ≫ σ) hσ' ≫ pullbackComap f h =
      h.left ≫ pullbackSection f V σ hσ := by
  apply pullback.hom_ext <;> simp

/-- The image of a base-changed section is contained in the preimage of the image of the
original section. -/
private lemma range_pullbackSection_comap_subset {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V V' : Y.Etale} (h : V' ⟶ V) (σ : V.left ⟶ X) (hσ : σ ≫ f = V.hom)
    (hσ' : (h.left ≫ σ) ≫ f = V'.hom) :
    Set.range (pullbackSection f V' (h.left ≫ σ) hσ') ⊆
      (pullbackComap f h) ⁻¹' Set.range (pullbackSection f V σ hσ) := by
  rintro x ⟨a, rfl⟩
  refine ⟨h.left a, ?_⟩
  have hc : (pullbackSection f V' (h.left ≫ σ) hσ' ≫ pullbackComap f h) a =
      (h.left ≫ pullbackSection f V σ hσ) a := by
    rw [pullbackSection_comap f h σ hσ hσ']
  simpa [Scheme.Hom.comp_apply] using hc.symm

/-- The square comparing a section over `V'` with the corresponding section over `V` is a
pullback square. -/
private lemma isPullback_pullbackSection_comap {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V V' : Y.Etale} (h : V' ⟶ V) (σ : V.left ⟶ X) (hσ : σ ≫ f = V.hom)
    (hσ' : (h.left ≫ σ) ≫ f = V'.hom) :
    IsPullback (pullbackSection f V' (h.left ≫ σ) hσ') h.left
      (pullbackComap f h) (pullbackSection f V σ hσ) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (pullbackSection_comap f h σ hσ hσ') (fun s ↦ s.fst ≫ pullback.fst V'.hom f)
    (fun s ↦ ?_) (fun s ↦ ?_) (fun s m hm _ ↦ ?_))
  · have h₁ : s.fst ≫ pullback.fst V'.hom f ≫ h.left = s.snd := by
      simpa using s.condition =≫ pullback.fst V.hom f
    have h₂ : s.fst ≫ pullback.snd V'.hom f = s.snd ≫ σ := by
      simpa using s.condition =≫ pullback.snd V.hom f
    refine pullback.hom_ext (by simp) ?_
    rw [Category.assoc, pullbackSection_snd, h₂, ← h₁]
    simp only [Category.assoc]
  · simpa using s.condition =≫ pullback.fst V.hom f
  · rw [← hm, Category.assoc, pullbackSection_fst, Category.comp_id]

/-- A point of the base change to `V'` whose image lies on a sheet over `V` lies on the
corresponding sheet over `V'`. -/
private lemma mem_range_pullbackSection_comap {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V V' : Y.Etale} (h : V' ⟶ V) (σ : V.left ⟶ X) (hσ : σ ≫ f = V.hom)
    (hσ' : (h.left ≫ σ) ≫ f = V'.hom) {p : ↥(pullback V'.hom f)}
    (hp : pullbackComap f h p ∈ Set.range (pullbackSection f V σ hσ)) :
    p ∈ Set.range (pullbackSection f V' (h.left ≫ σ) hσ') := by
  obtain ⟨v, hv⟩ := hp
  have hsq := isPullback_pullbackSection_comap f h σ hσ hσ'
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullbackComap f h) (g := pullbackSection f V σ hσ) p v hv.symm
  refine ⟨hsq.isoPullback.inv z, ?_⟩
  have hfac : hsq.isoPullback.inv ≫ pullbackSection f V' (h.left ≫ σ) hσ' =
      pullback.fst (pullbackComap f h) (pullbackSection f V σ hσ) := by
    rw [Iso.inv_comp_eq]
    exact hsq.isoPullback_hom_fst.symm
  rw [← hz, ← hfac, Scheme.Hom.comp_apply]

/-- A trivialization of a finite étale morphism `f` over an object `V` of the small étale
site of `Y`: a finite family of sections of the base change of `f` to `V` whose images are
pairwise disjoint and cover the base change. -/
private structure Splitting {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale) where
  /-- The number of sheets. -/
  sheets : ℕ
  /-- The sheets, as morphisms to `X` over `Y`. -/
  sheet : Fin sheets → (V.left ⟶ X)
  /-- Every sheet is étale. -/
  etale_sheet : ∀ j, Etale (sheet j)
  /-- Every sheet is a morphism over `Y`. -/
  sheet_over : ∀ j, sheet j ≫ f = V.hom
  /-- Distinct sheets have disjoint images in the base change. -/
  disjoint_sheet : Pairwise fun j j' ↦ Disjoint
    (Set.range (pullbackSection f V (sheet j) (sheet_over j)))
    (Set.range (pullbackSection f V (sheet j') (sheet_over j')))
  /-- The sheets cover the base change. -/
  iUnion_sheet :
    (⋃ j, Set.range (pullbackSection f V (sheet j) (sheet_over j))) = Set.univ

/-- Splittings base-change along morphisms of the small étale site. -/
private def Splitting.comap {X Y : Scheme.{u}} {f : X ⟶ Y} {V V' : Y.Etale} (h : V' ⟶ V)
    (s : Splitting f V) : Splitting f V' where
  sheets := s.sheets
  sheet j := h.left ≫ s.sheet j
  etale_sheet j := by
    have := s.etale_sheet j
    infer_instance
  sheet_over j := by
    rw [Category.assoc, s.sheet_over j, MorphismProperty.Over.w h]
  disjoint_sheet j j' hjj' :=
    Set.disjoint_of_subset
      (range_pullbackSection_comap_subset f h (s.sheet j) (s.sheet_over j) _)
      (range_pullbackSection_comap_subset f h (s.sheet j') (s.sheet_over j') _)
      (Disjoint.preimage _ (s.disjoint_sheet hjj'))
  iUnion_sheet := Set.iUnion_eq_univ_iff.2 fun p ↦ by
    obtain ⟨j, hj⟩ := Set.iUnion_eq_univ_iff.1 s.iUnion_sheet (pullbackComap f h p)
    exact ⟨j, mem_range_pullbackSection_comap f h (s.sheet j) (s.sheet_over j) _ hj⟩

end Splittings

section SplitPushforward

open CategoryTheory.Limits Opposite

@[simp]
private lemma smallEtaleBaseChange_obj_hom {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale) :
    ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V).hom = pullback.snd V.hom f := rfl

@[simp]
private lemma smallEtaleBaseChange_map_left {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V V' : Y.Etale} (h : V' ⟶ V) :
    ((Stacks.EtaleCohomology.smallEtaleBaseChange f).map h).left = pullbackComap f h := rfl

@[simp]
private lemma smallEtaleComposition_obj_hom {X : Scheme.{u}} (U : X.Etale)
    (W : U.left.Etale) : ((smallEtaleComposition U).obj W).hom = W.hom ≫ U.hom := rfl

@[simp]
private lemma smallEtaleComposition_map_left {X : Scheme.{u}} (U : X.Etale)
    {W W' : U.left.Etale} (g : W ⟶ W') :
    ((smallEtaleComposition U).map g).left = g.left := rfl

@[simp]
private lemma smallEtaleRestriction_obj_obj {X : Scheme.{u}} (U : X.Etale)
    (A : Type*) [Category* A] (F : Sheaf (smallEtaleTopology X) A) :
    ((smallEtaleRestriction U A).obj F).obj = (smallEtaleComposition U).op ⋙ F.obj := rfl

@[simp]
private lemma Splitting.comap_sheet {X Y : Scheme.{u}} {f : X ⟶ Y} {V V' : Y.Etale}
    (h : V' ⟶ V) (s : Splitting f V) (j : Fin s.sheets) :
    (s.comap h).sheet j = h.left ≫ s.sheet j := rfl

/-- Composition with an étale morphism, as a functor between small étale sites. -/
private def etaleComp {Z' Z : Scheme.{u}} (p : Z' ⟶ Z) (hp : Etale p) : Z'.Etale ⥤ Z.Etale where
  obj W := MorphismProperty.Over.mk ⊤ (W.hom ≫ p) (by have := hp; infer_instance)
  map g := MorphismProperty.Over.homMk g.left (MorphismProperty.Over.w_assoc g p)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
private lemma etaleComp_obj_hom {Z' Z : Scheme.{u}} (p : Z' ⟶ Z) (hp : Etale p)
    (W : Z'.Etale) : ((etaleComp p hp).obj W).hom = W.hom ≫ p := rfl

@[simp]
private lemma etaleComp_obj_left {Z' Z : Scheme.{u}} (p : Z' ⟶ Z) (hp : Etale p)
    (W : Z'.Etale) : ((etaleComp p hp).obj W).left = W.left := rfl

@[simp]
private lemma etaleComp_map_left {Z' Z : Scheme.{u}} (p : Z' ⟶ Z) (hp : Etale p)
    {W W' : Z'.Etale} (g : W ⟶ W') : ((etaleComp p hp).map g).left = g.left := rfl

/-- Composition with an étale morphism is continuous for the small étale topologies. -/
private lemma etaleComp_isContinuous {Z' Z : Scheme.{u}} (p : Z' ⟶ Z) (hp : Etale p) :
    (etaleComp p hp).IsContinuous (smallEtaleTopology Z') (smallEtaleTopology Z) :=
  smallEtaleComposition_isContinuous (MorphismProperty.Over.mk ⊤ p hp)

/-- Restriction of sheaves along an étale morphism. -/
private def etaleRestrict {Z' Z : Scheme.{u}} (p : Z' ⟶ Z) (hp : Etale p)
    (A : Type*) [Category* A] :
    Sheaf (smallEtaleTopology Z) A ⥤ Sheaf (smallEtaleTopology Z') A :=
  letI := etaleComp_isContinuous p hp
  (etaleComp p hp).sheafPushforwardContinuous A (smallEtaleTopology Z') (smallEtaleTopology Z)

@[simp]
private lemma etaleRestrict_obj_obj {Z' Z : Scheme.{u}} (p : Z' ⟶ Z) (hp : Etale p)
    (A : Type*) [Category* A] (F : Sheaf (smallEtaleTopology Z) A) :
    ((etaleRestrict p hp A).obj F).obj = (etaleComp p hp).op ⋙ F.obj := rfl

/-- The object of the small étale site of `X` carved out by a sheet of a splitting. -/
private def splitObj {X Y : Scheme.{u}} {f : X ⟶ Y} {V : Y.Etale} (s : Splitting f V)
    (j : Fin s.sheets) : X.Etale :=
  MorphismProperty.Over.mk ⊤ (s.sheet j) (s.etale_sheet j)

@[simp]
private lemma splitObj_hom {X Y : Scheme.{u}} {f : X ⟶ Y} {V : Y.Etale} (s : Splitting f V)
    (j : Fin s.sheets) : (splitObj s j).hom = s.sheet j := rfl

@[simp]
private lemma splitObj_left {X Y : Scheme.{u}} {f : X ⟶ Y} {V : Y.Etale} (s : Splitting f V)
    (j : Fin s.sheets) : (splitObj s j).left = V.left := rfl

/-- The inclusion of a sheet of a splitting into the base change. -/
private def splitInj {X Y : Scheme.{u}} {f : X ⟶ Y} {V : Y.Etale} (s : Splitting f V)
    (j : Fin s.sheets) : splitObj s j ⟶ (Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V :=
  MorphismProperty.Over.homMk (pullbackSection f V (s.sheet j) (s.sheet_over j))
    (pullbackSection_snd f V (s.sheet j) (s.sheet_over j))

@[simp]
private lemma splitInj_left {X Y : Scheme.{u}} {f : X ⟶ Y} {V : Y.Etale} (s : Splitting f V)
    (j : Fin s.sheets) :
    (splitInj s j).left = pullbackSection f V (s.sheet j) (s.sheet_over j) := rfl

/-- A morphism of the small étale site whose underlying morphism of schemes is a
monomorphism is a monomorphism. -/
private lemma mono_of_mono_left {X : Scheme.{u}} {A B : X.Etale} (a : A ⟶ B)
    (ha : Mono a.left) : Mono a :=
  ⟨fun _ _ heq ↦ MorphismProperty.Over.Hom.ext
    (ha.right_cancellation _ _ (congrArg (fun k ↦ k.left) heq))⟩

private lemma mono_splitInj {X Y : Scheme.{u}} {f : X ⟶ Y} {V : Y.Etale} (s : Splitting f V)
    (j : Fin s.sheets) : Mono (splitInj s j) :=
  mono_of_mono_left _ (by
    change Mono (pullbackSection f V (s.sheet j) (s.sheet_over j))
    have : IsSplitMono (pullbackSection f V (s.sheet j) (s.sheet_over j)) :=
      IsSplitMono.mk' ⟨pullback.fst V.hom f,
        pullbackSection_fst f V (s.sheet j) (s.sheet_over j)⟩
    infer_instance)

private lemma isPullback_initial_splitInj {X Y : Scheme.{u}} {f : X ⟶ Y} {V : Y.Etale}
    (s : Splitting f V) {j j' : Fin s.sheets} (hjj' : j ≠ j') :
    IsPullback (initial.to (splitObj s j)) (initial.to (splitObj s j'))
      (splitInj s j) (splitInj s j') :=
  isPullback_initial_of_disjoint_range _ _ (s.disjoint_sheet hjj')

private lemma splitInj_mem_smallEtaleTopology {X Y : Scheme.{u}} {f : X ⟶ Y} {V : Y.Etale}
    (s : Splitting f V) :
    Sieve.ofArrows (splitObj s) (splitInj s) ∈
      smallEtaleTopology X ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V) :=
  (ofArrows_mem_smallEtaleTopology_iff _).mpr s.iUnion_sheet

/-- The sections of a sheaf over the base change of `f` to `V` are the product of its
sections over the sheets of a splitting. -/
private lemma nonempty_isLimit_splitFan {X Y : Scheme.{u}} {f : X ⟶ Y} {V : Y.Etale}
    (s : Splitting f V) {A : Type*} [Category* A] (F : Sheaf (smallEtaleTopology X) A) :
    Nonempty (IsLimit (Fan.mk
      (F.obj.obj (op ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V)))
      (fun j ↦ F.obj.map (splitInj s j).op))) := by
  classical
  have factor : ∀ {T : X.Etale}
      (p : T ⟶ (Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V),
      (Sieve.ofArrows (splitObj s) (splitInj s)).arrows p →
        Σ j, {q : T ⟶ splitObj s j // p = q ≫ splitInj s j} := by
    intro T p hp
    have hmem := (Sieve.mem_ofArrows_iff (splitObj s) (splitInj s) p).1 hp
    exact ⟨hmem.choose, hmem.choose_spec.choose, hmem.choose_spec.choose_spec⟩
  exact ⟨isLimit_fan_sections_of_disjoint_cover (smallEtaleTopology X) F.obj F.property
    (Cofan.mk ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V) (splitInj s)) factor
    (mono_splitInj s) (fun _ _ h ↦ isPullback_initial_splitInj s h)
    (empty_mem_smallEtaleTopology X) (splitInj_mem_smallEtaleTopology s)⟩

/-- The structure morphism of an object of the small étale site of `V.left`, viewed in the
small étale site of `Y`. -/
private def overHom {Y : Scheme.{u}} (V : Y.Etale) (W : V.left.Etale) :
    (etaleComp V.hom V.prop).obj W ⟶ V :=
  MorphismProperty.Over.homMk W.hom rfl

@[simp]
private lemma overHom_left {Y : Scheme.{u}} (V : Y.Etale) (W : V.left.Etale) :
    (overHom V W).left = W.hom := rfl

/-- The inclusions of the sheets of a splitting, naturally over the small étale site of
`V.left`. -/
private def splitInjNat {X Y : Scheme.{u}} {f : X ⟶ Y} {V : Y.Etale} (s : Splitting f V)
    (j : Fin s.sheets) :
    etaleComp (s.sheet j) (s.etale_sheet j) ⟶
      etaleComp V.hom V.prop ⋙ Stacks.EtaleCohomology.smallEtaleBaseChange f where
  app W := splitInj (s.comap (overHom V W)) j
  naturality W W' g := by
    apply MorphismProperty.Over.Hom.ext
    change g.left ≫ pullbackSection f ((etaleComp V.hom V.prop).obj W')
        ((s.comap (overHom V W')).sheet j) ((s.comap (overHom V W')).sheet_over j) =
      pullbackSection f ((etaleComp V.hom V.prop).obj W)
          ((s.comap (overHom V W)).sheet j) ((s.comap (overHom V W)).sheet_over j) ≫
        pullbackComap f ((etaleComp V.hom V.prop).map g)
    have hw : (s.comap (overHom V W)).sheet j =
        ((etaleComp V.hom V.prop).map g).left ≫ (s.comap (overHom V W')).sheet j :=
      (MorphismProperty.Over.w_assoc g (s.sheet j)).symm
    have hover : (((etaleComp V.hom V.prop).map g).left ≫
        (s.comap (overHom V W')).sheet j) ≫ f = ((etaleComp V.hom V.prop).obj W).hom := by
      rw [← hw]
      exact (s.comap (overHom V W)).sheet_over j
    rw [pullbackSection_congr f ((etaleComp V.hom V.prop).obj W)
      ((s.comap (overHom V W)).sheet_over j) hover hw]
    exact (pullbackSection_comap f ((etaleComp V.hom V.prop).map g)
      ((s.comap (overHom V W')).sheet j) ((s.comap (overHom V W')).sheet_over j) hover).symm

/-- Direct image of sheaves along `f`, on the small étale sites. -/
private def smallEtalePushforward {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type*) [Category* A] :
    Sheaf (smallEtaleTopology X) A ⥤ Sheaf (smallEtaleTopology Y) A :=
  (Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPushforwardContinuous A
    (smallEtaleTopology Y) (smallEtaleTopology X)

/-- Comparison of the restriction of the direct image to a split object with the restriction
of the sheaf along a sheet. -/
private def splitRestrictionMap {X Y : Scheme.{u}} {f : X ⟶ Y} {V : Y.Etale}
    (s : Splitting f V) {A : Type*} [Category* A] (F : Sheaf (smallEtaleTopology X) A)
    (j : Fin s.sheets) :
    (etaleRestrict V.hom V.prop A).obj ((smallEtalePushforward f A).obj F) ⟶
      (etaleRestrict (s.sheet j) (s.etale_sheet j) A).obj F :=
  ⟨Functor.whiskerRight (NatTrans.op (splitInjNat s j)) F.obj⟩

/-- Over a split object, the restriction of the direct image is the product of the
restrictions along the sheets. -/
private lemma nonempty_isLimit_splitFanSheaf {X Y : Scheme.{u}} {f : X ⟶ Y} {V : Y.Etale}
    (s : Splitting f V) {A : Type*} [Category* A] (F : Sheaf (smallEtaleTopology X) A) :
    Nonempty (IsLimit (Fan.mk
      ((etaleRestrict V.hom V.prop A).obj ((smallEtalePushforward f A).obj F))
      (splitRestrictionMap s F))) := by
  classical
  refine ⟨isLimitOfReflects (sheafToPresheaf (smallEtaleTopology V.left) A) ?_⟩
  refine (Fan.isLimitMapConeEquiv _ _ _).symm ?_
  refine evaluationJointlyReflectsLimits _ (fun W ↦ ?_)
  refine (Fan.isLimitMapConeEquiv _ _ _).symm ?_
  change IsLimit (Fan.mk (F.obj.obj (op ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj
      ((etaleComp V.hom V.prop).obj W.unop))))
    (fun j ↦ F.obj.map (splitInj (s.comap (overHom V W.unop)) j).op))
  exact (nonempty_isLimit_splitFan (s.comap (overHom V W.unop)) F).some

/-- Over a split object, the restriction of the direct image is the product of the
restrictions along the sheets. -/
private lemma nonempty_splitRestrictionIso {X Y : Scheme.{u}} {f : X ⟶ Y} {V : Y.Etale}
    (s : Splitting f V) {A : Type*} [Category* A] [HasFiniteProducts A]
    (F : Sheaf (smallEtaleTopology X) A) :
    Nonempty ((etaleRestrict V.hom V.prop A).obj ((smallEtalePushforward f A).obj F) ≅
      ∏ᶜ fun j ↦ (etaleRestrict (s.sheet j) (s.etale_sheet j) A).obj F) :=
  ⟨(nonempty_isLimit_splitFanSheaf s F).some.conePointUniqueUpToIso (productIsProduct _)⟩

end SplitPushforward


section SplittingExistence

open CategoryTheory.Limits

/-- An étale morphism, as an object of the small étale site of its target. -/
private def etaleObj {Y N : Scheme.{u}} (q : N ⟶ Y) (hq : Etale q) : Y.Etale :=
  MorphismProperty.Over.mk ⊤ q hq

@[simp]
private lemma etaleObj_hom {Y N : Scheme.{u}} (q : N ⟶ Y) (hq : Etale q) :
    (etaleObj q hq).hom = q := rfl

@[simp]
private lemma etaleObj_left {Y N : Scheme.{u}} (q : N ⟶ Y) (hq : Etale q) :
    (etaleObj q hq).left = N := rfl

/-- The section of the base change cut out by a sheet of a trivialization
`X ×_Y N ≅ ∐_{i : ι} N` is the corresponding component of the coproduct. -/
private lemma pullbackSection_sheetOfIso {X Y : Scheme.{u}} (f : X ⟶ Y) {N : Scheme.{u}}
    (q : N ⟶ Y) (hq : Etale q) {index : Type u} (e : pullback f q ≅ ∐ fun _ : index ↦ N)
    (he : e.hom ≫ Sigma.desc (fun _ ↦ 𝟙 N) = pullback.snd f q) (j : index)
    (hover : _root_.Stacks.Etale.sheetOfIso f q e j ≫ f = (etaleObj q hq).hom) :
    pullbackSection f (etaleObj q hq) (_root_.Stacks.Etale.sheetOfIso f q e j) hover =
      Sigma.ι (fun _ : index ↦ N) j ≫ e.inv ≫ (pullbackSymmetry f q).hom := by
  have h1 : (Sigma.ι (fun _ : index ↦ N) j ≫ e.inv ≫ (pullbackSymmetry f q).hom) ≫
      pullback.fst (etaleObj q hq).hom f = 𝟙 (etaleObj q hq).left := by
    change (Sigma.ι (fun _ : index ↦ N) j ≫ e.inv ≫ (pullbackSymmetry f q).hom) ≫
      pullback.fst q f = 𝟙 N
    rw [Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact _root_.Stacks.Etale.ι_inv_comp_snd f q e he j
  have h2 : (Sigma.ι (fun _ : index ↦ N) j ≫ e.inv ≫ (pullbackSymmetry f q).hom) ≫
      pullback.snd (etaleObj q hq).hom f = _root_.Stacks.Etale.sheetOfIso f q e j := by
    change (Sigma.ι (fun _ : index ↦ N) j ≫ e.inv ≫ (pullbackSymmetry f q).hom) ≫
      pullback.snd q f = _
    rw [Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_snd]
    rfl
  refine pullback.hom_ext ?_ ?_
  · exact (pullbackSection_fst f (etaleObj q hq) _ hover).trans h1.symm
  · exact (pullbackSection_snd f (etaleObj q hq) _ hover).trans h2.symm

/-- The image of the section of `X ×_Y N → N` cut out by a sheet of a trivialization is the
image of the corresponding component of the coproduct. -/
private lemma range_pullbackSection_sheetOfIso {X Y : Scheme.{u}} (f : X ⟶ Y) {N : Scheme.{u}}
    (q : N ⟶ Y) (hq : Etale q) {index : Type u} (e : pullback f q ≅ ∐ fun _ : index ↦ N)
    (he : e.hom ≫ Sigma.desc (fun _ ↦ 𝟙 N) = pullback.snd f q) (j : index)
    (hover : _root_.Stacks.Etale.sheetOfIso f q e j ≫ f = (etaleObj q hq).hom) :
    Set.range (pullbackSection f (etaleObj q hq) (_root_.Stacks.Etale.sheetOfIso f q e j) hover) =
      (e.inv ≫ (pullbackSymmetry f q).hom) '' Set.range (Sigma.ι (fun _ : index ↦ N) j) := by
  rw [pullbackSection_sheetOfIso f q hq e he j hover]
  ext p
  simp only [Set.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Sigma.ι (fun _ : index ↦ N) j x, ⟨x, rfl⟩, (Scheme.Hom.comp_apply _ _ x).symm⟩
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, Scheme.Hom.comp_apply _ _ x⟩

/-- Distinct components of a coproduct of schemes have disjoint images. -/
lemma disjoint_range_sigmaι {index : Type u} (Z : index → Scheme.{u})
    {j j' : index} (hjj' : j ≠ j') :
    Disjoint (Set.range (Sigma.ι Z j)) (Set.range (Sigma.ι Z j')) := by
  rw [Set.disjoint_left]
  rintro p ⟨x, rfl⟩ ⟨y, hy⟩
  exact hjj' (congrArg Sigma.fst ((sigmaι_eq_iff Z j' j y x).mp hy)).symm

/-- The components of a coproduct of schemes cover it. -/
lemma iUnion_range_sigmaι {index : Type u} (Z : index → Scheme.{u}) :
    (⋃ j, Set.range (Sigma.ι Z j)) = Set.univ := by
  refine Set.iUnion_eq_univ_iff.2 fun p ↦ ?_
  obtain ⟨j, y, hy⟩ := (sigmaOpenCover Z).exists_eq p
  exact ⟨j, y, hy⟩

/-- **Étale-local triviality.** A trivialization `X ×_Y N ≅ ∐_{i : ι} N` of a finite étale
morphism `f` over an étale `Y`-scheme `N` is a splitting of `f` over `N`. -/
private lemma nonempty_splitting_of_iso {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Etale f)
    {N : Scheme.{u}} (q : N ⟶ Y) (hq : Etale q) {index : Type u} [Finite index]
    (e : pullback f q ≅ ∐ fun _ : index ↦ N)
    (he : e.hom ≫ Sigma.desc (fun _ ↦ 𝟙 N) = pullback.snd f q) :
    Nonempty (Splitting f (etaleObj q hq)) := by
  classical
  obtain ⟨n, ⟨φ⟩⟩ : ∃ n : ℕ, Nonempty (Fin n ≃ index) :=
    ⟨Nat.card index, ⟨(Finite.equivFin index).symm⟩⟩
  have hover : ∀ j : index,
      _root_.Stacks.Etale.sheetOfIso f q e j ≫ f = (etaleObj q hq).hom :=
    fun j ↦ _root_.Stacks.Etale.sheetOfIso_comp f q e he j
  have hetale : ∀ j : index, Etale (_root_.Stacks.Etale.sheetOfIso f q e j) := by
    intro j
    have hcomp : Etale (_root_.Stacks.Etale.sheetOfIso f q e j ≫ f) := by
      rw [hover j]
      exact hq
    have := hf
    exact Etale.of_comp _ f
  set g : (∐ fun _ : index ↦ N) ⟶ pullback q f :=
    e.inv ≫ (pullbackSymmetry f q).hom with hg
  have hgiso : IsIso g := by
    rw [hg]
    infer_instance
  have hginj : Function.Injective (⇑g) := (@Scheme.Hom.homeomorph _ _ g hgiso).injective
  have hgsurj : Function.Surjective (⇑g) := (@Scheme.Hom.homeomorph _ _ g hgiso).surjective
  have hrange : ∀ j : index,
      Set.range (pullbackSection f (etaleObj q hq)
          (_root_.Stacks.Etale.sheetOfIso f q e j) (hover j)) =
        g '' Set.range (Sigma.ι (fun _ : index ↦ N) j) :=
    fun j ↦ range_pullbackSection_sheetOfIso f q hq e he j (hover j)
  refine ⟨{ sheets := n
            sheet := fun k ↦ _root_.Stacks.Etale.sheetOfIso f q e (φ k)
            etale_sheet := fun k ↦ hetale (φ k)
            sheet_over := fun k ↦ hover (φ k)
            disjoint_sheet := ?_
            iUnion_sheet := ?_ }⟩
  · intro k k' hkk'
    rw [hrange (φ k), hrange (φ k')]
    exact Set.disjoint_image_of_injective hginj
      (disjoint_range_sigmaι (fun _ : index ↦ N) (fun h ↦ hkk' (φ.injective h)))
  · refine Set.iUnion_eq_univ_iff.2 fun p ↦ ?_
    obtain ⟨z, rfl⟩ := hgsurj p
    obtain ⟨j, hj⟩ := Set.iUnion_eq_univ_iff.1 (iUnion_range_sigmaι fun _ : index ↦ N) z
    refine ⟨φ.symm j, ?_⟩
    rw [hrange (φ (φ.symm j)), Equiv.apply_symm_apply]
    exact ⟨z, hj, rfl⟩

/-- **Étale-local triviality.** Every object of the small étale site of `Y` is covered by
objects over which the finite étale morphism `f` splits. -/
@[sga "4 IX 5.1" "partial"]
private lemma exists_splitting_cover {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    (U : Y.Etale) : ∃ (I : Type (u + 1)) (V : I → Y.Etale) (g : ∀ i, V i ⟶ U),
      Sieve.ofArrows V g ∈ smallEtaleTopology Y U ∧ ∀ i, Nonempty (Splitting f (V i)) := by
  classical
  choose N q hq pt hpt index hindex e he using fun x : ↥U.left ↦
    _root_.Stacks.Etale.exists_etale_pullback_iso_sigma f (U.hom x)
  have hUe : Etale U.hom := U.prop
  have hsnd : ∀ x : ↥U.left, Etale (pullback.snd (q x) U.hom) := fun x ↦ by
    have := hq x
    infer_instance
  have hVe : ∀ x : ↥U.left, Etale (pullback.snd (q x) U.hom ≫ U.hom) := fun x ↦
    @Etale.etale_comp _ _ _ _ U.hom (hsnd x) hUe
  refine ⟨ULift.{u + 1} ↥U.left,
    fun i ↦ etaleObj (pullback.snd (q i.down) U.hom ≫ U.hom) (hVe i.down),
    fun i ↦ MorphismProperty.Over.homMk (pullback.snd (q i.down) U.hom) rfl, ?_, ?_⟩
  · refine (ofArrows_mem_smallEtaleTopology_iff _).mpr (Set.eq_univ_of_forall fun x ↦ ?_)
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := q x) (g := U.hom) (pt x) x (hpt x)
    exact Set.mem_iUnion.2 ⟨⟨x⟩, z, hz⟩
  · intro i
    have := hindex i.down
    obtain ⟨hs⟩ := nonempty_splitting_of_iso f inferInstance (q i.down) (hq i.down)
      (e i.down) (he i.down)
    have hmor : etaleObj (pullback.snd (q i.down) U.hom ≫ U.hom) (hVe i.down) ⟶
        etaleObj (q i.down) (hq i.down) :=
      MorphismProperty.Over.homMk (pullback.fst (q i.down) U.hom) (by
        simp only [etaleObj_hom]
        exact pullback.condition)
    exact ⟨Splitting.comap hmor hs⟩

end SplittingExistence

end Stacks.ConstantSheaf
