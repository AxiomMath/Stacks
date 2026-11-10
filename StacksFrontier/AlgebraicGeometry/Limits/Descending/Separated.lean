module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Perfect.Limits
public import StacksCore.Tactic.StacksAttribute

/-!
# Separatedness at a finite stage of a limit

In the descent situation for a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms, separatedness of the limit descends to all
sufficiently large stages.

"For all sufficiently large indices" is expressed by an index `i₀` together with the assertion
for every `i` satisfying `i₀ ≤ i`. The index preorder is assumed essentially small relative to
the scheme universe, which expresses the source's common ambient universe while keeping the
index and scheme universes independent: a limit computed only in a smaller category of schemes
need not be preserved upon enlarging that universe, and the affine-limit descent and
filtered-colimit arguments used below require this size condition.

## Main results

* `AlgebraicGeometry.eventually_isSeparated`: the schemes in the system are separated beyond some
  index when their limit is separated.
* `AlgebraicGeometry.exists_isSeparated_stage`: the same statement for a cofiltered thin index
  category in the universe of the schemes, from which the above is deduced.

## Implementation notes

Separatedness of a scheme `X` is reduced to the condition that for every pair `U`, `V` of members
of an open cover the canonical morphism `U ∩ V ⟶ U × V` is a closed immersion. At a stage of the
system that morphism is obtained by descending the corresponding closed immersion over the limit;
the descent is the affine statement that a closed immersion of limits of diagrams of affine
schemes comes from a closed immersion at a finite stage, which in turn comes from the finitely
many algebra generators supplied by a cartesian projection.

The descent step compares morphisms built from `CategoryTheory.Limits.pullback`, from the diagram
of inverse images of an open, and from the open covers assembled out of them. Each identification
between two such descriptions is recorded as a named equation that the proofs rewrite with
explicitly, rather than left to the elaborator to find by unfolding the definitions.

## References

* [Stacks Project, Tag 086Q](https://stacks.math.columbia.edu/tag/086Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

/-- Separatedness of one stage of the inverse system propagates to all later stages, because the
transition morphisms are affine and hence separated. -/
private theorem isSeparated_of_later_of_stage_isSeparated
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (d : DescentSituation.{v, u} I) {i₀ : I}
    (hi₀ : (d.system.obj (Opposite.op i₀)).IsSeparated) :
    ∀ i : I, i₀ ≤ i → (d.system.obj (Opposite.op i)).IsSeparated := by
  intro i h
  let f : d.system.obj (Opposite.op i) ⟶ d.system.obj (Opposite.op i₀) :=
    d.system.map (homOfLE h).op
  have hf : IsAffineHom f := d.transition_affine (homOfLE h).op
  have hsep : IsSeparated f := IsSeparated.of_isAffineHom f
  have hstage : IsSeparated (terminal.from (d.system.obj (Opposite.op i))) := by
    rw [← terminal.comp_from f]
    infer_instance
  exact ⟨hstage⟩

private theorem eventually_isSeparated_of_exists_stage
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (d : DescentSituation.{v, u} I)
    (h : ∃ i₀ : I, (d.system.obj (Opposite.op i₀)).IsSeparated) :
    ∃ i₀ : I, ∀ i : I, i₀ ≤ i → (d.system.obj (Opposite.op i)).IsSeparated := by
  obtain ⟨i₀, hi₀⟩ := h
  exact ⟨i₀, isSeparated_of_later_of_stage_isSeparated d hi₀⟩

/-- A ring map of finite type has a finite set of elements generating the target over the image
of the source. -/
private lemma finiteType_exists_generators {R S : CommRingCat.{u}} (f : R ⟶ S)
    (hf : f.hom.FiniteType) :
    ∃ s : Finset S, Subring.closure (Set.range f ∪ (s : Set S)) = ⊤ := by
  let _ := f.hom.toAlgebra
  obtain ⟨s, hs⟩ := hf.out
  refine ⟨s, ?_⟩
  change Subring.closure (Set.range (algebraMap R S) ∪ (s : Set S)) = ⊤
  rw [← Algebra.adjoin_eq_ring_closure, hs]
  rfl

/-- Finitely many persistent generators turn surjectivity on a filtered colimit into surjectivity
at every sufficiently late stage. -/
private lemma exists_surjective_of_generators
    {J : Type u} [Category.{u} J] [IsFiltered J] [Quiver.IsThin J]
    (A B : J ⥤ CommRingCat.{u}) (f : A ⟶ B)
    (a : Cocone A) (b : Cocone B) (ha : IsColimit a) (hb : IsColimit b)
    (g : a.pt ⟶ b.pt) (hg : ∀ i, a.ι.app i ≫ g = f.app i ≫ b.ι.app i)
    (hgs : Function.Surjective g) (i₀ : J) (s : Finset (B.obj i₀))
    (hs : ∀ (j : J) (e : i₀ ⟶ j),
      Subring.closure (Set.range (f.app j) ∪ (B.map e) '' (s : Set (B.obj i₀))) = ⊤) :
    ∃ (j : J) (_ : i₀ ⟶ j), ∀ (k : J) (_ : j ⟶ k), Function.Surjective (f.app k) := by
  classical
  have h (x : s) : ∃ (j : J) (e : i₀ ⟶ j), B.map e x.1 ∈ Set.range (f.app j) := by
    obtain ⟨y, hy⟩ := hgs (b.ι.app i₀ x.1)
    obtain ⟨k, z, hz⟩ := Concrete.isColimit_exists_rep A ha y
    have he : b.ι.app i₀ x.1 = b.ι.app k (f.app k z) := by
      rw [← hy, ← hz]
      exact congrArg (fun q : A.obj k ⟶ b.pt => q z) (hg k)
    obtain ⟨j, e, q, hq⟩ := Concrete.isColimit_exists_of_rep_eq B hb x.1 (f.app k z) he
    refine ⟨j, e, A.map q z, ?_⟩
    rw [hq, NatTrans.naturality_apply]
  choose j e hj using h
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (insert i₀ (Finset.univ.image j))
  let e₀ : i₀ ⟶ k := (hk (Finset.mem_insert_self _ _)).some
  let q (x : s) : j x ⟶ k := (hk (by simp)).some
  have hmem : ∀ x ∈ s, B.map e₀ x ∈ Set.range (f.app k) := by
    intro x hx
    obtain ⟨y, hy⟩ := hj ⟨x, hx⟩
    refine ⟨A.map (q ⟨x, hx⟩) y, ?_⟩
    have eqe : e₀ = e ⟨x, hx⟩ ≫ q ⟨x, hx⟩ := Subsingleton.elim _ _
    rw [NatTrans.naturality_apply, hy, eqe, B.map_comp]
    rfl
  refine ⟨k, e₀, fun l q => ?_⟩
  have htop : (f.app l).hom.range = ⊤ := by
    apply top_unique
    rw [← hs l (e₀ ≫ q)]
    apply Subring.closure_le.mpr
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact hx
    · obtain ⟨z, hz⟩ := hmem y hy
      refine ⟨A.map q z, ?_⟩
      rw [NatTrans.naturality_apply, hz, B.map_comp]
      rfl
  intro x
  exact (show x ∈ (f.app l).hom.range by rw [htop]; trivial)

/-- Generators of a ring over a subring are carried by a pushout square to generators of the
pushout over the image of the remaining corner. -/
private lemma generators_of_isPushout
    {R S R' S' P : CommRingCat.{u}} (a : R ⟶ S) (b : R ⟶ R')
    (c : S ⟶ S') (d : R' ⟶ S') (f : P ⟶ S') (r : R' ⟶ P)
    (h : IsPushout a b c d) (hr : r ≫ f = d)
    (s : Finset S) (hs : Subring.closure (Set.range a ∪ (s : Set S)) = ⊤) :
    Subring.closure (Set.range f ∪ c '' (s : Set S)) = ⊤ := by
  let T := Subring.closure (Set.range f ∪ c '' (s : Set S))
  have hd : Set.range d ⊆ T := by
    rintro _ ⟨x, rfl⟩
    exact Subring.subset_closure (Or.inl ⟨r x, congrArg (fun q : R' ⟶ S' => q x) hr⟩)
  have hc : Set.range c ⊆ T := by
    rintro _ ⟨x, rfl⟩
    have hle : Subring.closure (Set.range a ∪ (s : Set S)) ≤ T.comap c.hom := by
      apply Subring.closure_le.mpr
      rintro x (⟨y, rfl⟩ | hx)
      · change c (a y) ∈ T
        rw [show c (a y) = d (b y) from congrArg (fun q : R ⟶ S' => q y) h.w]
        exact hd ⟨b y, rfl⟩
      · exact Subring.subset_closure (Or.inr ⟨x, hx, rfl⟩)
    exact hle (by rw [hs]; trivial)
  apply top_unique
  rw [← CommRingCat.closure_range_union_range_eq_top_of_isPushout h]
  exact Subring.closure_le.mpr (Set.union_subset hc hd)

/-- A cartesian projection supplies uniform generators for the source algebras. A closed
immersion of the limits therefore descends to the affine stages. -/
private lemma exists_closedImmersion_of_affine_diagrams
    {J : Type u} [Category.{u} J] [IsCofiltered J] [Quiver.IsThin J]
    (W U P : J ⥤ Scheme.{u})
    [∀ i, IsAffine (W.obj i)] [∀ i, IsAffine (U.obj i)] [∀ i, IsAffine (P.obj i)]
    (a : W ⟶ U) (f : W ⟶ P) (r : P ⟶ U) (hfr : f ≫ r = a)
    (cW : Cone W) (cP : Cone P) (hcW : IsLimit cW) (hcP : IsLimit cP)
    (g : cW.pt ⟶ cP.pt) (hg : ∀ i, g ≫ cP.π.app i = cW.π.app i ≫ f.app i)
    [IsClosedImmersion g] (i₀ : J) [LocallyOfFiniteType (a.app i₀)]
    (hcart : ∀ (j : J) (e : j ⟶ i₀),
      IsPullback (W.map e) (a.app j) (a.app i₀) (U.map e)) :
    ∃ (j : J) (_ : j ⟶ i₀), ∀ (k : J) (_ : k ⟶ j), IsClosedImmersion (f.app k) := by
  have : IsAffine cP.pt := Scheme.isAffine_of_isLimit cP hcP
  let A := P.op ⋙ Scheme.Γ
  let B := W.op ⋙ Scheme.Γ
  let φ : A ⟶ B := Functor.whiskerRight (NatTrans.op f) Scheme.Γ
  let ca := Scheme.Γ.mapCocone cP.op
  let cb := Scheme.Γ.mapCocone cW.op
  have (i : Jᵒᵖ) : IsAffine (P.op.obj i).unop := inferInstanceAs (IsAffine (P.obj i.unop))
  have (i : Jᵒᵖ) : IsAffine (W.op.obj i).unop := inferInstanceAs (IsAffine (W.obj i.unop))
  have hca : IsColimit ca := isColimitOfPreserves Scheme.Γ hcP.op
  have hcb : IsColimit cb := isColimitOfPreserves Scheme.Γ hcW.op
  obtain ⟨s, hs⟩ := finiteType_exists_generators (a.app i₀).appTop
    (HasRingHomProperty.appTop @LocallyOfFiniteType (a.app i₀) inferInstance)
  have hgen (j : Jᵒᵖ) (e : op i₀ ⟶ j) :
      Subring.closure (Set.range (φ.app j) ∪ B.map e '' (s : Set Γ(W.obj i₀, ⊤))) = ⊤ :=
    generators_of_isPushout (a.app i₀).appTop (U.map e.unop).appTop
      (W.map e.unop).appTop (a.app j.unop).appTop
      (f.app j.unop).appTop (r.app j.unop).appTop
      (isPushout_appTop_of_isPullback (hcart j.unop e.unop))
      (by
        rw [← Scheme.Hom.comp_appTop]
        exact congrArg Scheme.Hom.appTop (congrArg (fun t => t.app j.unop) hfr))
      s hs
  obtain ⟨j, e, hj⟩ := exists_surjective_of_generators A B φ ca cb hca hcb g.appTop
    (fun i => by
      change (cP.π.app i.unop).appTop ≫ g.appTop =
        (f.app i.unop).appTop ≫ (cW.π.app i.unop).appTop
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hg])
    (IsClosedImmersion.isAffine_surjective_of_isAffine g).2 (op i₀) s hgen
  exact ⟨j.unop, e.unop, fun k q =>
    IsClosedImmersion.of_surjective_of_isAffine (f.app k) (hj (op k) q.op)⟩

/-- The diagram of the pairwise products of two diagrams of schemes. -/
@[reducible]
private noncomputable def pairDiagram {J : Type u} [Category.{u} J]
    (A B : J ⥤ Scheme.{u}) : J ⥤ Scheme.{u} where
  obj i := A.obj i ⨯ B.obj i
  map f := prod.map (A.map f) (B.map f)
  map_id i := by simp
  map_comp f g := by simp [prod.map_map]

/-- The transition morphisms of `AlgebraicGeometry.pairDiagram` are the pairwise products of the
transition morphisms of the two diagrams. -/
private lemma pairDiagram_map {J : Type u} [Category.{u} J] (A B : J ⥤ Scheme.{u}) {j k : J}
    (f : j ⟶ k) : (pairDiagram A B).map f = prod.map (A.map f) (B.map f) := rfl

/-- The product of two cones, as a cone on the diagram of pairwise products. -/
@[reducible]
private noncomputable def pairCone {J : Type u} [Category.{u} J]
    {A B : J ⥤ Scheme.{u}} (a : Cone A) (b : Cone B) : Cone (pairDiagram A B) where
  pt := a.pt ⨯ b.pt
  π.app i := prod.map (a.π.app i) (b.π.app i)
  π.naturality i j f := by
    dsimp [pairDiagram]
    simp [prod.map_map]

private noncomputable def pairConeIsLimit {J : Type u} [Category.{u} J]
    {A B : J ⥤ Scheme.{u}} (a : Cone A) (b : Cone B)
    (ha : IsLimit a) (hb : IsLimit b) : IsLimit (pairCone a b) := by
  let fstCone (s : Cone (pairDiagram A B)) : Cone A :=
    { pt := s.pt
      π.app i := s.π.app i ≫ prod.fst
      π.naturality i j f := by
        simpa [pairDiagram, Category.assoc] using (congrArg (fun k => k ≫ prod.fst) (s.w f)).symm }
  let sndCone (s : Cone (pairDiagram A B)) : Cone B :=
    { pt := s.pt
      π.app i := s.π.app i ≫ prod.snd
      π.naturality i j f := by
        simpa [pairDiagram, Category.assoc] using (congrArg (fun k => k ≫ prod.snd) (s.w f)).symm }
  refine
    { lift := fun s => prod.lift (ha.lift (fstCone s)) (hb.lift (sndCone s))
      fac := ?_
      uniq := ?_ }
  · intro s j
    apply prod.hom_ext <;> simp [pairCone, fstCone, sndCone]
  · intro s m hm
    apply prod.hom_ext
    · refine ha.hom_ext fun j => ?_
      simpa [pairCone, fstCone, Category.assoc] using congrArg (fun k => k ≫ prod.fst) (hm j)
    · refine hb.hom_ext fun j => ?_
      simpa [pairCone, sndCone, Category.assoc] using congrArg (fun k => k ≫ prod.snd) (hm j)

/-- The canonical morphism from the intersection of two opens of a scheme to their product. -/
private noncomputable abbrev intersectionToProduct {X : Scheme.{u}} (U V : X.Opens) :
    (U ⊓ V).toScheme ⟶ U.toScheme ⨯ V.toScheme :=
  prod.lift (X.homOfLE inf_le_left) (X.homOfLE inf_le_right)

/-- Restricting a morphism to smaller opens on source and target commutes with the inclusions
of the smaller opens into the larger ones. -/
private lemma homOfLE_comp_resLE {X Y : Scheme.{u}} (f : X ⟶ Y) {S S' : Y.Opens}
    (hSS' : S ≤ S') {T T' : X.Opens} (hT : T ≤ f ⁻¹ᵁ S) (hT' : T' ≤ f ⁻¹ᵁ S')
    (hTT' : T ≤ T') :
    X.homOfLE hTT' ≫ f.resLE S' T' hT' = f.resLE S T hT ≫ Y.homOfLE hSS' := by
  rw [← cancel_mono S'.ι]
  simp

/-- The canonical morphism from an intersection to a product is compatible with restricting a
morphism to the two opens and to their intersection. -/
private lemma intersectionToProduct_comp_prodMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    {S S' : Y.Opens} {T T' : X.Opens} (hT : T ≤ f ⁻¹ᵁ S) (hT' : T' ≤ f ⁻¹ᵁ S')
    (hTT' : T ⊓ T' ≤ f ⁻¹ᵁ (S ⊓ S')) :
    intersectionToProduct T T' ≫ prod.map (f.resLE S T hT) (f.resLE S' T' hT') =
      f.resLE (S ⊓ S') (T ⊓ T') hTT' ≫ intersectionToProduct S S' := by
  apply prod.hom_ext
  · simp only [intersectionToProduct, Category.assoc, prod.map_fst, prod.lift_fst_assoc,
      prod.lift_fst]
    exact homOfLE_comp_resLE f inf_le_left hTT' hT inf_le_left
  · simp only [intersectionToProduct, Category.assoc, prod.map_snd, prod.lift_snd_assoc,
      prod.lift_snd]
    exact homOfLE_comp_resLE f inf_le_right hTT' hT' inf_le_right

private lemma intersectionToProduct_isPullback {X : Scheme.{u}} (U V : X.Opens) :
    IsPullback (U ⊓ V).ι (intersectionToProduct U V)
      (prod.lift (𝟙 X) (𝟙 X)) (prod.map U.ι V.ι) := by
  apply IsPullback.mk'
  · apply prod.hom_ext <;> simp [intersectionToProduct]
  · intro T φ ψ h _
    exact (cancel_mono (U ⊓ V).ι).mp h
  · intro T a b h
    have hu : b ≫ prod.fst ≫ U.ι = a := by
      simpa using congrArg (fun k => k ≫ prod.fst) h.symm
    have hv : b ≫ prod.snd ≫ V.ι = a := by
      simpa using congrArg (fun k => k ≫ prod.snd) h.symm
    have hfst := (isPullback_opens_inf U V).lift_fst (b ≫ prod.fst) (b ≫ prod.snd)
      (hu.trans hv.symm)
    have hsnd := (isPullback_opens_inf U V).lift_snd (b ≫ prod.fst) (b ≫ prod.snd)
      (hu.trans hv.symm)
    refine ⟨(isPullback_opens_inf U V).lift (b ≫ prod.fst) (b ≫ prod.snd) (hu.trans hv.symm),
      ?_, ?_⟩
    · rw [← Scheme.homOfLE_ι X inf_le_left, ← Category.assoc, hfst, Category.assoc]
      exact hu
    · apply prod.hom_ext
      · rw [Category.assoc]
        simp only [intersectionToProduct, prod.lift_fst]
        exact hfst
      · rw [Category.assoc]
        simp only [intersectionToProduct, prod.lift_snd]
        exact hsnd

private lemma intersectionToProduct_closed {X : Scheme.{u}} [X.IsSeparated]
    (U V : X.Opens) : IsClosedImmersion (intersectionToProduct U V) :=
  MorphismProperty.of_isPullback (intersectionToProduct_isPullback U V)
    (inferInstance : IsClosedImmersion (prod.lift (𝟙 X) (𝟙 X)))

section Descend

/-- The canonical morphism from the pullback of two opens to their pullback over the terminal
scheme is a closed immersion when the intersection embeds as a closed subscheme of the product. -/
private lemma isClosedImmersion_pullbackMap_of_intersectionToProduct {X : Scheme.{u}}
    (U V : X.Opens) (h : IsClosedImmersion (intersectionToProduct U V)) :
    IsClosedImmersion (pullback.map U.ι V.ι (U.ι ≫ terminal.from X) (V.ι ≫ terminal.from X)
      (𝟙 _) (𝟙 _) (terminal.from X) (by simp) (by simp)) := by
  let f : pullback U.ι V.ι ⟶ pullback (U.ι ≫ terminal.from X) (V.ι ≫ terminal.from X) :=
    pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (terminal.from X) (by simp) (by simp)
  change IsClosedImmersion f
  let eP := prodIsoPullback U.toScheme V.toScheme
  let eC := pullback.congrHom (terminal.comp_from U.ι).symm
    (terminal.comp_from V.ι).symm
  have hffst : f ≫ pullback.fst (U.ι ≫ terminal.from X)
        (V.ι ≫ terminal.from X) = pullback.fst U.ι V.ι ≫ 𝟙 _ :=
    pullback.lift_fst _ _ _
  have hfsnd : f ≫ pullback.snd (U.ι ≫ terminal.from X)
        (V.ι ≫ terminal.from X) = pullback.snd U.ι V.ι ≫ 𝟙 _ :=
    pullback.lift_snd _ _ _
  have hcfst : eC.hom ≫ pullback.fst (U.ι ≫ terminal.from X)
        (V.ι ≫ terminal.from X) =
      pullback.fst (terminal.from U.toScheme) (terminal.from V.toScheme) ≫ 𝟙 _ :=
    pullback.lift_fst _ _ _
  have hcsnd : eC.hom ≫ pullback.snd (U.ι ≫ terminal.from X)
        (V.ι ≫ terminal.from X) =
      pullback.snd (terminal.from U.toScheme) (terminal.from V.toScheme) ≫ 𝟙 _ :=
    pullback.lift_snd _ _ _
  have hpfst : eP.hom ≫ pullback.fst (terminal.from U.toScheme)
      (terminal.from V.toScheme) = prod.fst := prodIsoPullback_hom_fst _ _
  have hpsnd : eP.hom ≫ pullback.snd (terminal.from U.toScheme)
      (terminal.from V.toScheme) = prod.snd := prodIsoPullback_hom_snd _ _
  have he : (isPullback_opens_inf U V).isoPullback.hom ≫ f =
      intersectionToProduct U V ≫ eP.hom ≫ eC.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, hffst, Category.comp_id,
        (isPullback_opens_inf U V).isoPullback_hom_fst, Category.assoc,
        Category.assoc, hcfst, Category.comp_id, hpfst]
      exact (prod.lift_fst _ _).symm
    · rw [Category.assoc, hfsnd, Category.comp_id,
        (isPullback_opens_inf U V).isoPullback_hom_snd, Category.assoc,
        Category.assoc, hcsnd, Category.comp_id, hpsnd]
      exact (prod.lift_snd _ _).symm
  have hcl : IsClosedImmersion (intersectionToProduct U V ≫ eP.hom ≫ eC.hom) := inferInstance
  rw [← he] at hcl
  exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion _ _).mp hcl

/-- A scheme covered by opens whose pairwise intersections embed as closed subschemes of the
corresponding products is separated. -/
private lemma isSeparated_of_intersectionToProduct
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (hU : TopologicalSpace.IsOpenCover U)
    (h : ∀ i j, IsClosedImmersion (intersectionToProduct (U i) (U j))) :
    X.IsSeparated := by
  let 𝒰 := X.openCoverOfIsOpenCover U hU
  let cover := Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒰 (terminal.from X) (terminal.from X)
  constructor
  constructor
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) cover
  intro ij
  let i := ij.1
  let j := ij.2
  let f : pullback (U i).ι (U j).ι ⟶
      pullback ((U i).ι ≫ terminal.from X) ((U j).ι ≫ terminal.from X) :=
    pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (terminal.from X) (by simp) (by simp)
  have hf : IsClosedImmersion f :=
    isClosedImmersion_pullbackMap_of_intersectionToProduct (U i) (U j) (h i j)
  let hp := pullback_map_diagonal_isPullback (U i).ι (U j).ι (terminal.from X)
  let e : Arrow.mk f ≅ Arrow.mk (cover.pullbackHom (pullback.diagonal (terminal.from X)) ij) :=
    Arrow.isoMk hp.isoPullback (Iso.refl _)
      (by
        change hp.isoPullback.hom ≫
          pullback.snd (pullback.diagonal (terminal.from X)) (cover.f ij) = f ≫ 𝟙 _
        rw [Category.comp_id]
        exact hp.isoPullback_hom_snd)
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) e).mp hf

/-- The morphism of diagrams of preimages induced by an inclusion of opens of one stage. -/
@[reducible]
private noncomputable def opensDiagramMap
    {J : Type u} [Category.{u} J] (D : J ⥤ Scheme.{u})
    (i : J) (U V : (D.obj i).Opens) (h : U ≤ V) :
    opensDiagram D i U ⟶ opensDiagram D i V where
  app j := (D.obj j.left).homOfLE ((D.map j.hom).preimage_mono h)
  naturality j k f := by
    apply (cancel_mono (D.map k.hom ⁻¹ᵁ V).ι).mp
    simp [opensDiagram, Scheme.Hom.resLE_comp_ι]

private lemma opensDiagramMap_isPullback
    {J : Type u} [Category.{u} J] (D : J ⥤ Scheme.{u})
    (i : J) (U V : (D.obj i).Opens) (h : U ≤ V)
    {j k : Over i} (e : j ⟶ k) :
    IsPullback ((opensDiagram D i U).map e) ((opensDiagramMap D i U V h).app j)
      ((opensDiagramMap D i U V h).app k) ((opensDiagram D i V).map e) := by
  have (j : Over i) : IsOpenImmersion ((opensDiagramMap D i U V h).app j) := by
    change IsOpenImmersion ((D.obj j.left).homOfLE ((D.map j.hom).preimage_mono h))
    infer_instance
  refine IsOpenImmersion.isPullback _ _ _ _
    ((opensDiagramMap D i U V h).naturality e).symm ?_
  change (D.map e.left).resLE (D.map k.hom ⁻¹ᵁ V) (D.map j.hom ⁻¹ᵁ V) _ ⁻¹ᵁ
      ((D.obj k.left).homOfLE ((D.map k.hom).preimage_mono h)).opensRange =
    ((D.obj j.left).homOfLE ((D.map j.hom).preimage_mono h)).opensRange
  rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE, ← Scheme.Hom.comp_preimage,
    Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage,
    ← Scheme.Hom.comp_preimage (D.map e.left), ← D.map_comp, Over.w e]

/-- The morphism from the diagram of preimages of an intersection to the diagram of pairwise
products of the diagrams of preimages. -/
@[reducible]
private noncomputable def intersectionDiagramToProduct
    {J : Type u} [Category.{u} J] (D : J ⥤ Scheme.{u})
    (i : J) (U V : (D.obj i).Opens) :
    opensDiagram D i (U ⊓ V) ⟶ pairDiagram (opensDiagram D i U) (opensDiagram D i V) where
  app j := prod.lift ((opensDiagramMap D i (U ⊓ V) U inf_le_left).app j)
    ((opensDiagramMap D i (U ⊓ V) V inf_le_right).app j)
  naturality j k f := by
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, Category.assoc, pairDiagram_map, prod.map_fst,
        ← Category.assoc, prod.lift_fst]
      exact (opensDiagramMap D i (U ⊓ V) U inf_le_left).naturality f
    · rw [Category.assoc, prod.lift_snd, Category.assoc, pairDiagram_map, prod.map_snd,
        ← Category.assoc, prod.lift_snd]
      exact (opensDiagramMap D i (U ⊓ V) V inf_le_right).naturality f

private lemma exists_intersectionToProduct_closed_of_affine_intersection
    {J : Type u} [Category.{u} J] [IsCofiltered J] [Quiver.IsThin J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)]
    [c.pt.IsSeparated] (i : J) (U V : (D.obj i).Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V)) :
    ∃ (j : J) (e : j ⟶ i), ∀ (k : J) (q : k ⟶ j),
      IsClosedImmersion (intersectionToProduct (D.map (q ≫ e) ⁻¹ᵁ U)
        (D.map (q ≫ e) ⁻¹ᵁ V)) := by
  let W := opensDiagram D i (U ⊓ V)
  let A := opensDiagram D i U
  let B := opensDiagram D i V
  let P := pairDiagram A B
  have hW (j : Over i) : IsAffine (W.obj j) := hUV.preimage (D.map j.hom)
  have hA (j : Over i) : IsAffine (A.obj j) := hU.preimage (D.map j.hom)
  have hB (j : Over i) : IsAffine (B.obj j) := hV.preimage (D.map j.hom)
  have hP (j : Over i) : IsAffine (P.obj j) :=
    IsAffine.of_isIso (prodIsoPullback (A.obj j) (B.obj j)).hom
  let cw := opensCone D c i (U ⊓ V)
  let ca := opensCone D c i U
  let cb := opensCone D c i V
  let cp := pairCone ca cb
  have hcw := isLimitOpensCone D c hc i (U ⊓ V)
  have hcp := pairConeIsLimit ca cb (isLimitOpensCone D c hc i U) (isLimitOpensCone D c hc i V)
  let a : W ⟶ A := opensDiagramMap D i (U ⊓ V) U inf_le_left
  let f : W ⟶ P := intersectionDiagramToProduct D i U V
  let r : P ⟶ A :=
    { app := fun _ => prod.fst
      naturality := fun j k e => by
        dsimp [P, pairDiagram]
        simp }
  have hfr : f ≫ r = a := by
    ext j
    exact prod.lift_fst _ _
  let g : cw.pt ⟶ cp.pt := intersectionToProduct (c.π.app i ⁻¹ᵁ U) (c.π.app i ⁻¹ᵁ V)
  have hpre (T : (D.obj i).Opens) (j : Over i) :
      c.π.app i ⁻¹ᵁ T = c.π.app j.left ⁻¹ᵁ (D.map j.hom ⁻¹ᵁ T) := by
    rw [← Scheme.Hom.comp_preimage, c.w]
  have hg (j : Over i) : g ≫ cp.π.app j = cw.π.app j ≫ f.app j :=
    intersectionToProduct_comp_prodMap (c.π.app j.left)
      (S := D.map j.hom ⁻¹ᵁ U) (S' := D.map j.hom ⁻¹ᵁ V)
      (T := c.π.app i ⁻¹ᵁ U) (T' := c.π.app i ⁻¹ᵁ V) (hpre U j).le (hpre V j).le
      (by rw [hpre U j, hpre V j]; exact le_rfl)
  have : IsClosedImmersion g := intersectionToProduct_closed (X := c.pt) _ _
  have : Quiver.IsThin (Over i) := fun j k => ⟨fun f g => by
    ext
    exact Subsingleton.elim _ _⟩
  have : LocallyOfFiniteType (a.app (Over.mk (𝟙 i))) := by
    change LocallyOfFiniteType ((D.obj i).homOfLE
      ((D.map (Over.mk (𝟙 i)).hom).preimage_mono (inf_le_left : U ⊓ V ≤ U)))
    infer_instance
  obtain ⟨j, _, hj⟩ := exists_closedImmersion_of_affine_diagrams W A P a f r hfr cw cp
    hcw hcp g hg (Over.mk (𝟙 i)) (fun j e =>
      opensDiagramMap_isPullback D i (U ⊓ V) U inf_le_left e)
  exact ⟨j.left, j.hom, fun k q => hj (Over.mk (q ≫ j.hom)) (Over.homMk q)⟩

end Descend

/-- First descend affineness of the intersection, then descend the closed immersion into the
product of the two affine charts. -/
private lemma exists_intersectionToProduct_closed
    {J : Type u} [Category.{u} J] [IsCofiltered J] [Quiver.IsThin J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, QuasiSeparatedSpace (D.obj i)]
    [c.pt.IsSeparated] (i : J) (U V : (D.obj i).Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    ∃ (j : J) (e : j ⟶ i), ∀ (k : J) (q : k ⟶ j),
      IsClosedImmersion (intersectionToProduct (D.map (q ≫ e) ⁻¹ᵁ U)
        (D.map (q ≫ e) ⁻¹ᵁ V)) := by
  have := isAffineHom_π_app D c hc
  have hcompact : IsCompact (U ⊓ V : (D.obj i).Opens).carrier :=
    (quasiSeparatedSpace_iff_forall_affineOpens.mp inferInstance) ⟨U, hU⟩ ⟨V, hV⟩
  have (j : Over i) : CompactSpace ((opensDiagram D i (U ⊓ V)).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ (U ⊓ V).2 hcompact)
  have (j : Over i) : QuasiSeparatedSpace ((opensDiagram D i (U ⊓ V)).obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map j.hom ⁻¹ᵁ (U ⊓ V)).2).mp
      (.of_quasiSeparatedSpace _)
  have : IsAffine (opensCone D c i (U ⊓ V)).pt :=
    IsAffineOpen.inf (X := c.pt) (hU.preimage (c.π.app i)) (hV.preimage (c.π.app i))
  obtain ⟨j, hj⟩ := Scheme.exists_isAffine_of_isLimit (opensDiagram D i (U ⊓ V))
    (opensCone D c i (U ⊓ V)) (isLimitOpensCone D c hc i (U ⊓ V))
  obtain ⟨k, e, hk⟩ := exists_intersectionToProduct_closed_of_affine_intersection D c hc
    j.left (D.map j.hom ⁻¹ᵁ U) (D.map j.hom ⁻¹ᵁ V)
    (hU.preimage _) (hV.preimage _) hj
  refine ⟨k, e ≫ j.hom, fun l q => ?_⟩
  have hpre (T : (D.obj i).Opens) :
      D.map (q ≫ (e ≫ j.hom)) ⁻¹ᵁ T = D.map (q ≫ e) ⁻¹ᵁ (D.map j.hom ⁻¹ᵁ T) := by
    rw [← Category.assoc, D.map_comp, Scheme.Hom.comp_preimage]
  exact (congrArg₂ (fun A B : (D.obj l).Opens =>
    IsClosedImmersion (intersectionToProduct A B)) (hpre U) (hpre V)).mpr (hk l q)

/-- The cofiltered form of Tag 086Q: for a cofiltered thin diagram of quasi-compact and
quasi-separated schemes with affine transition morphisms, a separated limit forces some stage of
the diagram to be a separated scheme.

This is the geometric core of `AlgebraicGeometry.eventually_isSeparated`, which adds the passage
from a directed preorder to its small model and the propagation of separatedness to all later
stages. It is stated separately because the relative statement over a fixed base (Tag 01ZH)
applies it to the diagram of inverse images of an open, whose index category is an `Over`
category rather than the opposite of a preorder. -/
lemma exists_isSeparated_stage
    {J : Type u} [Category.{u} J] [IsCofiltered J] [Quiver.IsThin J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [c.pt.IsSeparated] : ∃ i : J, (D.obj i).IsSeparated := by
  classical
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := J)
  let cover := (D.obj i).affineCover.finiteSubcover
  let U (x : cover.I₀) := (cover.f x).opensRange
  have hU (x) : IsAffineOpen (U x) := isAffineOpen_opensRange (cover.f x)
  have hpair (p : cover.I₀ × cover.I₀) :=
    exists_intersectionToProduct_closed D c hc i (U p.1) (U p.2) (hU _) (hU _)
  choose j e hj using hpair
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (insert i (Finset.univ.image j))
  let q : k ⟶ i := (hk (Finset.mem_insert_self _ _)).some
  let r (p : cover.I₀ × cover.I₀) : k ⟶ j p := (hk (by simp)).some
  refine ⟨k, isSeparated_of_intersectionToProduct (fun x => D.map q ⁻¹ᵁ U x) ?_ ?_⟩
  · change ⨆ x, D.map q ⁻¹ᵁ U x = ⊤
    rw [← Scheme.Hom.preimage_iSup]
    change D.map q ⁻¹ᵁ (⨆ x, (cover.f x).opensRange) = ⊤
    rw [cover.iSup_opensRange, Scheme.Hom.preimage_top]
  · intro x y
    have he : r (x, y) ≫ e (x, y) = q := Subsingleton.elim _ _
    exact (congrArg (fun f : k ⟶ i =>
      IsClosedImmersion (intersectionToProduct (D.map f ⁻¹ᵁ U x) (D.map f ⁻¹ᵁ U y))) he).mp
      (hj (x, y) k (r (x, y)))

/-- **Stacks Project, Tag 086Q.** In a directed inverse system of quasi-compact and
quasi-separated schemes with affine transition morphisms, if the limit is separated then every
sufficiently late stage is separated. -/
@[stacks 086Q]
theorem eventually_isSeparated
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    [EssentiallySmall.{u} I]
    (d : DescentSituation.{v, u} I)
    [d.limitCone.pt.IsSeparated] :
    ∃ i₀ : I, ∀ i : I, i₀ ≤ i → (d.system.obj (Opposite.op i)).IsSeparated := by
  classical
  have : Nonempty I := ⟨d.base⟩
  let e := equivSmallModel.{u} Iᵒᵖ
  have : IsCofiltered (SmallModel.{u} Iᵒᵖ) := IsCofiltered.of_equivalence e
  have : Quiver.IsThin (SmallModel.{u} Iᵒᵖ) := fun j k =>
    ⟨fun f g => e.inverse.map_injective (Subsingleton.elim _ _)⟩
  let D := e.inverse ⋙ d.system
  let c := d.limitCone.whisker e.inverse
  have hc : IsLimit c :=
    (Functor.Initial.isLimitWhiskerEquiv e.inverse d.limitCone).symm d.isLimit
  have : c.pt.IsSeparated := ‹d.limitCone.pt.IsSeparated›
  have (j : SmallModel.{u} Iᵒᵖ) : CompactSpace (D.obj j) :=
    d.quasiCompact (e.inverse.obj j).unop
  have (j : SmallModel.{u} Iᵒᵖ) : QuasiSeparatedSpace (D.obj j) :=
    d.quasiSeparated (e.inverse.obj j).unop
  have {j k : SmallModel.{u} Iᵒᵖ} (f : j ⟶ k) : IsAffineHom (D.map f) :=
    d.transition_affine (e.inverse.map f)
  obtain ⟨j, hj⟩ := exists_isSeparated_stage D c hc
  exact eventually_isSeparated_of_exists_stage d ⟨(e.inverse.obj j).unop, hj⟩

end AlgebraicGeometry

end
