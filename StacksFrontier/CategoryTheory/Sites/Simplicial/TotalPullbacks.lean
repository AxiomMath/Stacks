module

public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalSite

/-!
# Pullbacks of covering families in the total site

The two remaining site axioms for the fibrewise covering families of the total site of a
simplicial site: pullbacks along members of a covering family exist, and covering families are
stable under base change. Both rest on one geometric fact: a pullback square in a single fibre,
transported along a simplex map, is a pullback square in the total category as soon as every
further transition functor out of that fibre preserves it.

## Main results

* `CategoryTheory.SimplicialSite.isPullback_totalVertical`: a pullback square in one fibre,
  transported along a simplex map, is a pullback square in the total category when every
  further transition functor out of that fibre preserves it.
* `CategoryTheory.SimplicialSite.totalCoverage_hasPullbacks`: pullbacks of fibrewise covering
  families along arbitrary morphisms of the total category exist.
* `CategoryTheory.SimplicialSite.totalCoverage_isStableUnderBaseChange`: the fibrewise covering
  families are stable under base change in the total category.

## Implementation notes

The transported pullback square is produced by a helper stated in `CoGrothendieck.mk` normal
form, so that no object of the total category enters a goal as
`((CoGrothendieck.ι F b).obj P).base`; the passage between that form and the one phrased with
the fibre inclusion `CoGrothendieck.ι` is definitional and is made once, in
`isPullback_totalVertical`.

The remaining clauses of Stacks 09WC — the total category, its morphisms and their composition,
the fibrewise covering families, the identity-covering axiom and the composition axiom — are the
Mathlib declarations `CoGrothendieck`, `CoGrothendieck.Hom`, `CoGrothendieck.category` and the
declarations of `StacksFrontier.CategoryTheory.Sites.Simplicial.TotalSite`. The `add_to_stacks`
commands at the end of this file record the tag against them, which is what completes the tag's
covering set.

## References

* [Stacks Project, Tag 09WC](https://stacks.math.columbia.edu/tag/09WC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor

universe u

namespace CategoryTheory

attribute [local implicit_reducible] CategoryTheory.Pseudofunctor.CoGrothendieck.ι
  Quiver.Hom.toLoc

namespace SimplicialSite

attribute [local simp] PrelaxFunctor.map₂_eqToHom

/-- A pullback square in one fibre, with one pair of parallel arrows transported along a simplex
map, is a pullback square in the total category, provided the transported square is preserved by
every further transition functor out of that fibre. The vertical arrows are written out in
`CoGrothendieck.mk` normal form. -/
private lemma isPullback_totalVertical_mk {C : SimplicialSite.{u}}
    {b0 b1 : SimplexCategoryᵒᵖ} (δ : b1 ⟶ b0)
    {U V : C.totalPseudofunctor.obj ⟨Opposite.op b0⟩} (q : U ⟶ V)
    {W : C.totalPseudofunctor.obj ⟨Opposite.op b1⟩}
    (g : W ⟶ (C.totalPseudofunctor.map δ.op.toLoc).toFunctor.obj V)
    {P : C.totalPseudofunctor.obj ⟨Opposite.op b1⟩} {fst : P ⟶ W}
    {snd : P ⟶ (C.totalPseudofunctor.map δ.op.toLoc).toFunctor.obj U}
    (hpb : IsPullback fst snd g ((C.totalPseudofunctor.map δ.op.toLoc).toFunctor.map q))
    (hpres : ∀ {b2 : SimplexCategoryᵒᵖ} (η : b1.unop ⟶ b2.unop),
      PreservesLimit (cospan g ((C.totalPseudofunctor.map δ.op.toLoc).toFunctor.map q))
        ((C.underlying.map η).toFunctor)) :
    IsPullback (C := CoGrothendieck C.totalPseudofunctor)
      (⟨𝟙 b1, fst ≫ (C.totalPseudofunctor.mapId ⟨Opposite.op b1⟩).inv.toNatTrans.app W⟩ :
        (⟨b1, P⟩ : CoGrothendieck C.totalPseudofunctor) ⟶ ⟨b1, W⟩)
      (⟨δ, snd⟩ : (⟨b1, P⟩ : CoGrothendieck C.totalPseudofunctor) ⟶ ⟨b0, U⟩)
      (⟨δ, g⟩ : (⟨b1, W⟩ : CoGrothendieck C.totalPseudofunctor) ⟶ ⟨b0, V⟩)
      (⟨𝟙 b0, q ≫ (C.totalPseudofunctor.mapId ⟨Opposite.op b0⟩).inv.toNatTrans.app V⟩ :
        (⟨b0, U⟩ : CoGrothendieck C.totalPseudofunctor) ⟶ ⟨b0, V⟩) := by
  have hmap {T : SimplexCategoryᵒᵖ} (e : T ⟶ b1) := by
    have : PreservesLimit (cospan g ((C.totalPseudofunctor.map δ.op.toLoc).toFunctor.map q))
      (C.totalPseudofunctor.map e.op.toLoc).toFunctor := hpres e.unop
    exact Functor.map_isPullback (C.totalPseudofunctor.map e.op.toLoc).toFunctor hpb
  apply IsPullback.mk'
  · refine CoGrothendieck.Hom.ext _ _ (by simp) ?_
    have hw := hpb.w
    simp only [CoGrothendieck.categoryStruct_comp_fiber]
    simp only [op_id, Quiver.Hom.id_toLoc, Cat.Hom.id_toFunctor,
      CoGrothendieck.categoryStruct_comp_base, op_comp, Quiver.Hom.comp_toLoc,
      mapComp_id_right_inv_app, Functor.id_obj, Bicategory.Strict.rightUnitor_eqToIso,
      eqToIso.inv, PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
      Category.comp_id, eqToHom_naturality, Category.assoc, ← NatTrans.naturality_assoc,
      Functor.id_map, eqToHom_naturality_assoc, ← Cat.Hom₂.comp_app, Iso.inv_hom_id,
      Cat.Hom.toNatTrans_id, NatTrans.id_app, Functor.map_comp, mapComp_id_left_inv_app,
      Bicategory.Strict.leftUnitor_eqToIso, ← Functor.map_comp_assoc, Functor.map_id,
      Category.id_comp, eqToHom_trans] at hw ⊢
    rw [← Category.assoc, hw, Category.assoc]
  · intro T φ φ' hφ hψ
    have hb : φ.base = φ'.base := by
      simpa using congrArg CoGrothendieck.Hom.base hφ
    obtain ⟨b', f'⟩ := φ'
    dsimp only at hb f' hφ hψ ⊢
    cases hb
    have hp := hmap φ.base
    refine CoGrothendieck.Hom.ext _ _ rfl ?_
    simp only [eqToHom_refl, Category.comp_id]
    apply hp.hom_ext
    · have hh := CoGrothendieck.Hom.congr hφ
      simp only [CoGrothendieck.categoryStruct_comp_fiber, eqToHom_refl, Category.comp_id,
        Functor.map_comp, Category.assoc] at hh
      simp only [← Category.assoc] at hh
      exact (cancel_mono ((C.totalPseudofunctor.map φ.base.op.toLoc).toFunctor.map
        ((C.totalPseudofunctor.mapId ⟨Opposite.op b1⟩).inv.toNatTrans.app W))).mp
        ((cancel_mono ((C.totalPseudofunctor.mapComp (𝟙 b1).op.toLoc
          φ.base.op.toLoc).inv.toNatTrans.app W)).mp hh)
    · have hh := CoGrothendieck.Hom.congr hψ
      simp only [CoGrothendieck.categoryStruct_comp_fiber, eqToHom_refl, Category.comp_id] at hh
      simp only [← Category.assoc] at hh
      exact (cancel_mono ((C.totalPseudofunctor.mapComp δ.op.toLoc
        φ.base.op.toLoc).inv.toNatTrans.app U)).mp hh
  · intro T φ ψ h
    have hb : φ.base ≫ δ = ψ.base := by
      simpa using congrArg CoGrothendieck.Hom.base h
    obtain ⟨b', bFiber⟩ := ψ
    dsimp only at hb bFiber h ⊢
    cases hb
    have hp := hmap φ.base
    have hh := CoGrothendieck.Hom.congr h
    simp only [CoGrothendieck.categoryStruct_comp_fiber] at hh
    simp only [CoGrothendieck.categoryStruct_comp_base, op_comp, Quiver.Hom.comp_toLoc, op_id,
      Quiver.Hom.id_toLoc, Cat.Hom.id_toFunctor, Functor.map_comp, mapComp_id_left_inv_app,
      Functor.id_obj, Bicategory.Strict.leftUnitor_eqToIso, eqToIso.inv,
      PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, Category.assoc,
      ← Functor.map_comp_assoc, ← Cat.Hom₂.comp_app, Iso.inv_hom_id, Cat.Hom.toNatTrans_id,
      NatTrans.id_app, Functor.map_id, Category.id_comp, eqToHom_naturality, Category.comp_id,
      eqToHom_trans, eqToHom_refl] at hh
    have hfiber : φ.fiber ≫ (C.totalPseudofunctor.map φ.base.op.toLoc).toFunctor.map g =
        (bFiber ≫ (C.totalPseudofunctor.mapComp δ.op.toLoc
            φ.base.op.toLoc).hom.toNatTrans.app U) ≫
          (C.totalPseudofunctor.map φ.base.op.toLoc).toFunctor.map
            ((C.totalPseudofunctor.map δ.op.toLoc).toFunctor.map q) := by
      have h2 := congrArg (fun k => k ≫ (C.totalPseudofunctor.mapComp δ.op.toLoc
        φ.base.op.toLoc).hom.toNatTrans.app V) hh
      simp only [Category.assoc] at h2
      rw [(C.totalPseudofunctor.mapComp δ.op.toLoc
        φ.base.op.toLoc).hom.toNatTrans.naturality q] at h2
      simpa [Category.assoc, Functor.comp_map] using h2
    obtain ⟨l, hl₁, hl₂⟩ := hp.exists_lift φ.fiber _ hfiber
    refine ⟨⟨φ.base, l⟩, ?_, ?_⟩
    · refine CoGrothendieck.Hom.ext _ _ (by simp) ?_
      simp only [CoGrothendieck.categoryStruct_comp_fiber]
      simp only [op_id, Quiver.Hom.id_toLoc, Cat.Hom.id_toFunctor,
        CoGrothendieck.categoryStruct_comp_base, op_comp, Quiver.Hom.comp_toLoc,
        Functor.map_comp, mapComp_id_left_inv_app, Functor.id_obj,
        Bicategory.Strict.leftUnitor_eqToIso, eqToIso.inv, PrelaxFunctor.map₂_eqToHom,
        Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, Category.assoc, ← Functor.map_comp_assoc,
        ← Cat.Hom₂.comp_app, Iso.inv_hom_id, Cat.Hom.toNatTrans_id, NatTrans.id_app,
        Functor.map_id, Category.id_comp, eqToHom_naturality, Category.comp_id]
      rw [← Category.assoc, hl₁]
    · refine CoGrothendieck.Hom.ext _ _ rfl ?_
      simp only [CoGrothendieck.categoryStruct_comp_fiber, eqToHom_refl, Category.comp_id]
      rw [← Category.assoc, hl₂]
      simp

/-- A pullback square in one fibre, with one pair of parallel arrows transported along a simplex
map, is a pullback square in the total category, provided the transported square is preserved by
every further transition functor out of that fibre. -/
lemma isPullback_totalVertical {C : SimplicialSite.{u}}
    {b0 b1 : SimplexCategoryᵒᵖ} (δ : b1 ⟶ b0)
    {U V : C.totalPseudofunctor.obj ⟨Opposite.op b0⟩} (q : U ⟶ V)
    {W : C.totalPseudofunctor.obj ⟨Opposite.op b1⟩}
    (g : W ⟶ (C.totalPseudofunctor.map δ.op.toLoc).toFunctor.obj V)
    {P : C.totalPseudofunctor.obj ⟨Opposite.op b1⟩} {fst : P ⟶ W}
    {snd : P ⟶ (C.totalPseudofunctor.map δ.op.toLoc).toFunctor.obj U}
    (hpb : IsPullback fst snd g ((C.totalPseudofunctor.map δ.op.toLoc).toFunctor.map q))
    (hpres : ∀ {b2 : SimplexCategoryᵒᵖ} (η : b1.unop ⟶ b2.unop),
      PreservesLimit (cospan g ((C.totalPseudofunctor.map δ.op.toLoc).toFunctor.map q))
        ((C.underlying.map η).toFunctor)) :
    IsPullback
      ((CoGrothendieck.ι C.totalPseudofunctor b1).map fst)
      (⟨δ, snd⟩ : (CoGrothendieck.ι C.totalPseudofunctor b1).obj P ⟶
        (CoGrothendieck.ι C.totalPseudofunctor b0).obj U)
      (⟨δ, g⟩ : (CoGrothendieck.ι C.totalPseudofunctor b1).obj W ⟶
        (CoGrothendieck.ι C.totalPseudofunctor b0).obj V)
      ((CoGrothendieck.ι C.totalPseudofunctor b0).map q) :=
  isPullback_totalVertical_mk δ q g hpb hpres

section FibreInclusion

attribute [local implicit_reducible] CategoryTheory.SimplicialSite.totalPseudofunctor
  CategoryTheory.Functor.toPseudofunctor' CategoryTheory.pseudofunctorOfIsLocallyDiscrete

/-- The inclusion of the fibre in simplicial degree `n` preserves the pairwise pullbacks of
a covering family of that fibre. Those pullbacks are computed in the fibre, and the square
they form stays a pullback in the total category because every transition functor out of that
fibre preserves it. -/
theorem coverage_pullbacksPreservedBy_ι (C : SimplicialSite.{u}) (n : SimplexCategory) :
    (C.coverage n).PullbacksPreservedBy
      (CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)) := by
  let F : C.underlying.obj n ⥤ CoGrothendieck C.totalPseudofunctor :=
    CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)
  change (C.coverage n).PullbacksPreservedBy F
  have : (C.coverage n).HasIsos := C.coverage_hasIsos n
  have : (C.coverage n).HasPullbacks := C.coverage_hasPullbacks n
  have : (C.coverage n).IsStableUnderBaseChange := C.coverage_isStableUnderBaseChange n
  refine ⟨fun X R hR => ⟨fun Y Z f g hf hg => ?_⟩⟩
  have : R.HasPairwisePullbacks := (C.coverage n).hasPairwisePullbacks_of_mem hR
  have : HasPullback f g := Presieve.HasPairwisePullbacks.has_pullbacks hf hg
  have hpb := IsPullback.of_hasPullback f g
  let Fδ := (C.totalPseudofunctor.map (𝟙 (Opposite.op n)).op.toLoc).toFunctor
  have hFδ : Fδ = 𝟭 (C.underlying.obj n) := by
    change (C.underlying.map (𝟙 n)).toFunctor = 𝟭 (C.underlying.obj n)
    exact congrArg Cat.Hom.toFunctor (C.underlying.map_id n)
  let hX : Fδ.obj X = X := congrArg (fun G => G.obj X) hFδ
  let hZ : Fδ.obj Z = Z := congrArg (fun G => G.obj Z) hFδ
  let eX : X ≅ Fδ.obj X := eqToIso hX.symm
  let eZ : Z ≅ Fδ.obj Z := eqToIso hZ.symm
  have hgNat : Fδ.map g = eZ.inv ≫ g ≫ eX.hom := by
    simpa [eX, eZ, hX, hZ, Category.assoc] using (Functor.congr_hom hFδ g)
  have heX : eX.hom =
      (C.totalPseudofunctor.mapId ⟨Opposite.op (Opposite.op n)⟩).inv.toNatTrans.app X := by
    simp [eX, Fδ, SimplicialSite.totalPseudofunctor, Functor.toPseudofunctor'_mapId]
  have heZ : eZ.hom =
      (C.totalPseudofunctor.mapId ⟨Opposite.op (Opposite.op n)⟩).inv.toNatTrans.app Z := by
    simp [eZ, Fδ, SimplicialSite.totalPseudofunctor, Functor.toPseudofunctor'_mapId]
  have hpb' : IsPullback (pullback.fst f g) (pullback.snd f g ≫ eZ.hom) (f ≫ eX.hom)
      (Fδ.map g) := by
    refine hpb.of_iso (Iso.refl _) (Iso.refl _) eZ eX (by simp) (by simp) (by simp) ?_
    rw [hgNat]
    simp [eX, eZ]
  have htotal := SimplicialSite.isPullback_totalVertical (C := C)
    (δ := 𝟙 (Opposite.op n)) (q := g) (g := f ≫ eX.hom) hpb' fun η => by
      have : PreservesLimit (cospan f g) (C.underlying.map η).toFunctor :=
        C.preservesPullbacks (φ := η) hR hg f
      exact preservesLimit_of_iso_diagram (K₁ := cospan f g) _
        (cospanExt (Iso.refl Y) eZ eX (by simp) (by rw [hgNat]; simp))
  have hmap {A B : C.underlying.obj n} (k : A ⟶ B) :
      (⟨𝟙 (Opposite.op n),
          k ≫ (C.totalPseudofunctor.mapId ⟨Opposite.op (Opposite.op n)⟩).inv.toNatTrans.app B⟩ :
        (CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).obj A ⟶
          (CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).obj B) = F.map k := by
    refine CoGrothendieck.Hom.ext _ _ rfl ?_
    simp only [F, CoGrothendieck.ι_map_fiber]
    exact (Category.comp_id _).symm
  rw [heX, heZ, hmap, hmap] at htotal
  exact preservesLimit_of_preserves_limit_cone hpb.isLimit
    ((isLimitMapConePullbackConeEquiv F hpb.w).symm htotal.isLimit)

end FibreInclusion

/-- Pullbacks of fibrewise covering families along arbitrary total morphisms exist. -/
@[stacks 09WC "existence of pullbacks of coverings", instance]
theorem totalCoverage_hasPullbacks (C : SimplicialSite.{u}) :
    C.totalCoverage.HasPullbacks := by
  classical
  refine ⟨?_⟩
  rintro ⟨b1, V⟩ ⟨b0, U⟩ R ⟨δ, g⟩ ⟨R0, hR0, hR0eq⟩
  constructor
  intro Z r hr
  let ι0 := CoGrothendieck.ι C.totalPseudofunctor b0
  have hmem : R0.map ι0 r := by rwa [hR0eq]
  rcases Presieve.map_iff.mp hmem with ⟨Z0, hZ0, q, hq, hrEq⟩
  cases hZ0
  obtain rfl : r = ι0.map q := by simpa [ι0] using hrEq.symm
  let Fδ := (C.underlying.map δ.unop).toFunctor
  have hRδ : R0.map Fδ ∈ C.coverage b1.unop (Fδ.obj U) := C.coverPreserving (φ := δ.unop) U hR0
  have hqδ : (R0.map Fδ) (Fδ.map q) := Presieve.map_iff.mpr ⟨Z0, rfl, q, hq, by simp⟩
  have : (R0.map Fδ).HasPullbacks g :=
    (C.coverage_hasPullbacks b1.unop).hasPullbacks_of_mem g hRδ
  have : HasPullback (Fδ.map q) g := (R0.map Fδ).hasPullback g hqδ
  exact (isPullback_totalVertical (C := C) δ q g (IsPullback.of_hasPullback (Fδ.map q) g).flip
    fun η => C.preservesPullbacks η hRδ hqδ g).flip.hasPullback

/-- The inclusion of a fibre into the total category is faithful. -/
private theorem coGrothendieck_ι_faithful (C : SimplicialSite.{u}) (b : SimplexCategoryᵒᵖ) :
    (CoGrothendieck.ι C.totalPseudofunctor b).Faithful where
  map_injective {a₁ a₂} φ ψ hh := by
    have h2 := CoGrothendieck.Hom.congr hh
    simp only [CoGrothendieck.ι_map_fiber, eqToHom_refl, Category.comp_id] at h2
    exact (cancel_mono
      ((C.totalPseudofunctor.mapId ⟨Opposite.op b⟩).inv.toNatTrans.app a₂)).mp h2

/-- The fibrewise covering families are stable under base change in the total category. -/
@[stacks 09WC "the base-change axiom", instance]
theorem totalCoverage_isStableUnderBaseChange (C : SimplicialSite.{u}) :
    C.totalCoverage.IsStableUnderBaseChange := by
  constructor
  rintro ι ⟨b0, U⟩ X f ⟨R0, hR0, hR0eq⟩ ⟨b1, V⟩ ⟨δ, gFiber⟩ P p₁ p₂ h
  classical
  let ι0 := CoGrothendieck.ι C.totalPseudofunctor b0
  have : ι0.Faithful := C.coGrothendieck_ι_faithful b0
  have hobj : Function.Injective ι0.obj := by
    intro U₁ U₂ hh
    change ({ base := b0, fiber := U₁ } : C.totalPseudofunctor.CoGrothendieck) =
      { base := b0, fiber := U₂ } at hh
    exact eq_of_heq (CoGrothendieck.mk.inj hh).2
  have houter (i : ι) :
      ∃ (x : C.totalPseudofunctor.obj ⟨Opposite.op b0⟩)
        (hx : ι0.obj x = X i) (a : x ⟶ U), R0 a ∧
          f i = eqToHom hx.symm ≫ ι0.map a := by
    have hm : R0.map ι0 (f i) := hR0eq ▸ ⟨i⟩
    obtain ⟨x, hx, a, ha, heq⟩ := Presieve.map_iff.mp hm
    exact ⟨x, hx, a, ha, by simp [heq]⟩
  choose x hx a ha hfa using houter
  obtain rfl : X = fun i => ι0.obj (x i) := funext fun i => (hx i).symm
  have hfa' (i : ι) : f i = ι0.map (a i) := by simpa using hfa i
  have hR0family : R0 = Presieve.ofArrows x a := by
    apply presieve_map_injective_of_faithful ι0 hobj
    rw [hR0eq, funext hfa']
    simp [Presieve.map_ofArrows]
  have hAfamily : Presieve.ofArrows x a ∈ C.coverage b0.unop U := hR0family ▸ hR0
  let Fδ := (C.underlying.map δ.unop).toFunctor
  let xδ := fun i => Fδ.obj (x i)
  let aδ := fun i => Fδ.map (a i)
  have hAδ : Presieve.ofArrows xδ aδ ∈ C.coverage b1.unop (Fδ.obj U) := by
    have hc : (Presieve.ofArrows x a).map Fδ ∈ C.coverage b1.unop (Fδ.obj U) :=
      C.coverPreserving (φ := δ.unop) U hAfamily
    rwa [show (Presieve.ofArrows x a).map Fδ = Presieve.ofArrows xδ aδ from
      Presieve.map_ofArrows a] at hc
  have hmemδ (i : ι) : Presieve.ofArrows xδ aδ (aδ i) := ⟨i⟩
  have hPB (i : ι) : ∃ (Q : C.underlying.obj b1.unop) (fst : Q ⟶ V) (snd : Q ⟶ xδ i),
      IsPullback fst snd gFiber (aδ i) := by
    have : HasPullback (aδ i) gFiber :=
      ((C.coverage_hasPullbacks b1.unop).hasPullbacks_of_mem gFiber hAδ).hasPullback (hmemδ i)
    exact ⟨_, _, _, (IsPullback.of_hasPullback (aδ i) gFiber).flip⟩
  choose Q fst snd hpb using hPB
  let ι1 := CoGrothendieck.ι C.totalPseudofunctor b1
  let totalG : ι1.obj V ⟶ ι0.obj U := ⟨δ, gFiber⟩
  let Qₜ := fun i => ι1.obj (Q i)
  let q₁ := fun i => ι1.map (fst i)
  let q₂ := fun i => (⟨δ, snd i⟩ : Qₜ i ⟶ ι0.obj (x i))
  have hbar (i : ι) : IsPullback (q₁ i) (q₂ i) totalG (f i) := by
    have ht := isPullback_totalVertical (C := C) δ (a i) gFiber (hpb i)
      (fun η => C.preservesPullbacks η hAδ (hmemδ i) gFiber)
    simpa [Fδ, xδ, aδ, totalG, Qₜ, q₁, q₂, hfa' i] using ht
  have := C.coverage_isStableUnderBaseChange b1.unop
  have hQtotal : Presieve.ofArrows Qₜ q₁ ∈ C.totalCoverage (ι1.obj V) :=
    ⟨Presieve.ofArrows Q fst,
      Precoverage.mem_coverings_of_isPullback aδ hAδ gFiber fst snd hpb, Presieve.map_ofArrows fst⟩
  let e := fun i => (h i).isoIsPullback _ _ (hbar i)
  have hinner (i : ι) :
      Presieve.ofArrows (fun _ : Unit => P i) (fun _ => (e i).hom) ∈
        C.totalCoverage (Qₜ i) := by
    rw [Presieve.ofArrows_of_unique]
    exact Precoverage.HasIsos.mem_coverings_of_isIso (e i).hom
  have hcomp := Precoverage.comp_mem_coverings q₁ hQtotal
    (g := fun i _ => (e i).hom) hinner
  have hcompEq :
      Presieve.ofArrows (fun p : Σ _ : ι, Unit => P p.1)
          (fun p => (e p.1).hom ≫ q₁ p.1) = Presieve.ofArrows P p₁ := by
    calc
      _ = Presieve.ofArrows (fun p : Σ _ : ι, Unit => P p.1) (fun p => p₁ p.1) := by
        congr 1
        exact funext fun p => (h p.1).isoIsPullback_hom_fst _ _ (hbar p.1)
      _ = Presieve.ofArrows P p₁ :=
        Presieve.ofArrows_comp_eq_of_surjective p₁ fun i => ⟨⟨i, ()⟩, rfl⟩
  rwa [← hcompEq]

end SimplicialSite

end CategoryTheory

add_to_stacks 09WC "the objects of the total category"
  CategoryTheory.Pseudofunctor.CoGrothendieck
add_to_stacks 09WC "the morphisms of the total category"
  CategoryTheory.Pseudofunctor.CoGrothendieck.Hom
add_to_sga "4 XVII 2.2.12" CategoryTheory.Pseudofunctor.CoGrothendieck.Hom
add_to_stacks 09WC "composition in the total category"
  CategoryTheory.Pseudofunctor.CoGrothendieck.category
add_to_stacks 09WC "the covering families"
  CategoryTheory.SimplicialSite.totalCoverage
add_to_stacks 09WC "the identity-covering axiom"
  CategoryTheory.SimplicialSite.totalCoverage_hasIsos
add_to_stacks 09WC "the composition axiom"
  CategoryTheory.SimplicialSite.totalCoverage_isStableUnderComposition

end
