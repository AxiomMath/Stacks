module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.AmbientSizeBound
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.AmbientSizeBound

/-!
# Universal thickening existence: lifting the chart relation

Lifting the étale equivalence relation presenting the source to the universal first order
thickening of a chart, the induced relation on the target chart (diagonal, symmetry and
composition), formal unramifiedness of the chart maps, and descent of maps along an atlas.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Spaces.UniversalThickening

open AlgebraicGeometry.Space

private lemma exists_chartThickening
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicGeometry.AlgebraicSpaces B S hS} (h : Z ⟶ X)
    (hh : AlgebraicGeometry.Space.FormallyUnramified h.hom) :
    Nonempty (ChartThickening B S hS h) := by
  obtain ⟨V, U, a, b, ψ, hae, hbe, has, hbs, hcomm, hψ⟩ :=
    exists_formallyUnramified_surjectiveEtale_chart B S hS h hh
  let : FormallyUnramified
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map ψ) := hψ
  exact ⟨⟨V, U, a, b, ψ, hae, hbe, has, hbs, hcomm, hψ,
    Stacks.Thickenings.universalFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map ψ)⟩⟩

lemma universalThickening_lift_map
    {R R' V V' U : Scheme.{u}} (j : R ⟶ R')
    (hj : Stacks.Thickenings.IsFirstOrderThickening j) (s : R ⟶ V) (b : R' ⟶ U)
    (q : V ⟶ U) (i : V ⟶ V') (p : V' ⟶ U)
    (hu : Stacks.Thickenings.IsUniversalFirstOrderThickening q i p)
    (hcomm : j ≫ b = s ≫ q) :
    ∃! k : R' ⟶ V', (j ≫ k = s ≫ i) ∧ (k ≫ p = b) :=
  hu.existsUnique_lift j hj s b hcomm

lemma universalThickening_lift_pair_distinct_base
    {R R' V V' U : Scheme.{u}} (j : R ⟶ R')
    (hj : Stacks.Thickenings.IsFirstOrderThickening j)
    (s t : R ⟶ V) (b₁ b₂ : R' ⟶ U) (q : V ⟶ U)
    (i : V ⟶ V') (p : V' ⟶ U)
    (hu : Stacks.Thickenings.IsUniversalFirstOrderThickening q i p)
    (hs : j ≫ b₁ = s ≫ q) (ht : j ≫ b₂ = t ≫ q) :
    ∃! k : R' ⟶ V' ⨯ V',
      (j ≫ k ≫ (Limits.prod.fst : V' ⨯ V' ⟶ V') = s ≫ i) ∧
      (j ≫ k ≫ (Limits.prod.snd : V' ⨯ V' ⟶ V') = t ≫ i) ∧
      (k ≫ (Limits.prod.fst : V' ⨯ V' ⟶ V') ≫ p = b₁) ∧
      (k ≫ (Limits.prod.snd : V' ⨯ V' ⟶ V') ≫ p = b₂) := by
  obtain ⟨ks, hks, uks⟩ := universalThickening_lift_map j hj s b₁ q i p hu hs
  obtain ⟨kt, hkt, ukt⟩ := universalThickening_lift_map j hj t b₂ q i p hu ht
  refine ⟨Limits.prod.lift ks kt, ?_, ?_⟩
  · constructor
    · calc
        j ≫ Limits.prod.lift ks kt ≫ Limits.prod.fst = j ≫ ks := by
          rw [Limits.prod.lift_fst]
        _ = s ≫ i := hks.1
    · constructor
      · calc
          j ≫ Limits.prod.lift ks kt ≫ Limits.prod.snd = j ≫ kt := by
            rw [Limits.prod.lift_snd]
          _ = t ≫ i := hkt.1
      · constructor
        · rw [← Category.assoc, Limits.prod.lift_fst]
          exact hks.2
        · rw [← Category.assoc, Limits.prod.lift_snd]
          exact hkt.2
  · intro k hk
    apply Limits.prod.hom_ext
    · have hfst := uks (k ≫ Limits.prod.fst)
        ⟨hk.1, hk.2.2.1⟩
      rw [hfst, Limits.prod.lift_fst]
    · have hsnd := ukt (k ≫ Limits.prod.snd)
        ⟨hk.2.1, hk.2.2.2⟩
      rw [hsnd, Limits.prod.lift_snd]

lemma universalThickening_lift_pair
    {R R' V V' U : Scheme.{u}} (j : R ⟶ R')
    (hj : Stacks.Thickenings.IsFirstOrderThickening j)
    (s t : R ⟶ V) (b : R' ⟶ U) (q : V ⟶ U)
    (i : V ⟶ V') (p : V' ⟶ U)
    (hu : Stacks.Thickenings.IsUniversalFirstOrderThickening q i p)
    (hs : j ≫ b = s ≫ q) (ht : j ≫ b = t ≫ q) :
    ∃! k : R' ⟶ V' ⨯ V',
      (j ≫ k ≫ (Limits.prod.fst : V' ⨯ V' ⟶ V') = s ≫ i) ∧
      (j ≫ k ≫ (Limits.prod.snd : V' ⨯ V' ⟶ V') = t ≫ i) ∧
      (k ≫ (Limits.prod.fst : V' ⨯ V' ⟶ V') ≫ p = b) ∧
      (k ≫ (Limits.prod.snd : V' ⨯ V' ⟶ V') ≫ p = b) :=
  universalThickening_lift_pair_distinct_base j hj s t b b q i p hu hs ht

lemma universalThickening_lift_to_pullback
    {R R' V V' U : Scheme.{u}} (j : R ⟶ R')
    (hj : Stacks.Thickenings.IsFirstOrderThickening j)
    (s t : R ⟶ V) (b : R' ⟶ U) (q : V ⟶ U)
    (i : V ⟶ V') (p : V' ⟶ U)
    (hu : Stacks.Thickenings.IsUniversalFirstOrderThickening q i p)
    (hs : j ≫ b = s ≫ q) (ht : j ≫ b = t ≫ q) :
    ∃! k : R' ⟶ Limits.pullback p p,
      j ≫ k ≫ (Limits.pullback.fst p p) = s ≫ i ∧
      j ≫ k ≫ (Limits.pullback.snd p p) = t ≫ i ∧
      k ≫ Limits.pullback.fst p p ≫ p = b ∧
      k ≫ Limits.pullback.snd p p ≫ p = b := by
  obtain ⟨ks, hks, uks⟩ := universalThickening_lift_map j hj s b q i p hu hs
  obtain ⟨kt, hkt, ukt⟩ := universalThickening_lift_map j hj t b q i p hu ht
  have hbase : ks ≫ p = kt ≫ p := hks.2.trans hkt.2.symm
  let k := Limits.pullback.lift ks kt hbase
  refine ⟨k, ?_, ?_⟩
  · constructor
    · calc
        j ≫ k ≫ Limits.pullback.fst p p = j ≫ ks := by
          simp only [k, Limits.pullback.lift_fst]
        _ = s ≫ i := hks.1
    · constructor
      · calc
        j ≫ k ≫ Limits.pullback.snd p p = j ≫ kt := by
            simp only [k, Limits.pullback.lift_snd]
          _ = t ≫ i := hkt.1
      · constructor
        · calc
            k ≫ Limits.pullback.fst p p ≫ p = ks ≫ p := by
              rw [← Category.assoc, show k ≫ Limits.pullback.fst p p = ks from by
                dsimp [k]
                exact Limits.pullback.lift_fst ks kt hbase]
            _ = b := hks.2
        · calc
            k ≫ Limits.pullback.snd p p ≫ p = kt ≫ p := by
              rw [← Category.assoc, show k ≫ Limits.pullback.snd p p = kt from by
                dsimp [k]
                exact Limits.pullback.lift_snd ks kt hbase]
            _ = b := hkt.2
  · intro k' hk'
    apply Limits.pullback.hom_ext
    · have hfst := uks (k' ≫ Limits.pullback.fst p p)
        ⟨by simpa [Category.assoc] using hk'.1,
          by simpa [Category.assoc] using hk'.2.2.1⟩
      have hKfst : k ≫ Limits.pullback.fst p p = ks := by
        dsimp [k]
        exact Limits.pullback.lift_fst ks kt hbase
      exact hfst.trans hKfst.symm
    · have hsnd := ukt (k' ≫ Limits.pullback.snd p p)
        ⟨by simpa [Category.assoc] using hk'.2.1,
          by simpa [Category.assoc] using hk'.2.2.2⟩
      have hKsnd : k ≫ Limits.pullback.snd p p = kt := by
        dsimp [k]
        exact Limits.pullback.lift_snd ks kt hbase
      exact hsnd.trans hKsnd.symm

lemma exists_universalThickening_of_relation_pair
    {R V U V' : Scheme.{u}} (s t : R ⟶ V) (q : V ⟶ U)
    (i : V ⟶ V') (p : V' ⟶ U)
    (hu : Stacks.Thickenings.IsUniversalFirstOrderThickening q i p)
    (hfu : FormallyUnramified (s ≫ q))
    (hbase : t ≫ q = s ≫ q) :
    ∃ (H : Stacks.Thickenings.UniversalFirstOrderThickening (s ≫ q))
      (k : H.ambient ⟶ Limits.pullback p p),
      (H.inclusion ≫ k ≫ Limits.pullback.fst p p = s ≫ i) ∧
      (H.inclusion ≫ k ≫ Limits.pullback.snd p p = t ≫ i) ∧
      (k ≫ Limits.pullback.fst p p ≫ p = H.toBase) ∧
      (k ≫ Limits.pullback.snd p p ≫ p = H.toBase) := by
  let : FormallyUnramified (s ≫ q) := hfu
  let H := Stacks.Thickenings.universalFirstOrderThickening (s ≫ q)
  have hs : H.inclusion ≫ H.toBase = s ≫ q :=
    H.isUniversal.inclusion_toBase
  have ht : H.inclusion ≫ H.toBase = t ≫ q := by
    rw [hbase]
    exact hs
  obtain ⟨k, hk, _⟩ := universalThickening_lift_to_pullback
    H.inclusion H.isUniversal.isFirstOrderThickening s t H.toBase q i p hu hs ht
  exact ⟨H, k, hk.1, hk.2.1, hk.2.2.1, hk.2.2.2⟩

lemma exists_universalThickening_of_etale_relation_pair
    {R V U V' : Scheme.{u}} (s t : R ⟶ V) (q : V ⟶ U)
    (i : V ⟶ V') (p : V' ⟶ U)
    (hu : Stacks.Thickenings.IsUniversalFirstOrderThickening q i p)
    (hs : Etale s) (hq : FormallyUnramified q)
    (hbase : t ≫ q = s ≫ q) :
    ∃ (H : Stacks.Thickenings.UniversalFirstOrderThickening (s ≫ q))
      (k : H.ambient ⟶ Limits.pullback p p),
      (H.inclusion ≫ k ≫ Limits.pullback.fst p p = s ≫ i) ∧
      (H.inclusion ≫ k ≫ Limits.pullback.snd p p = t ≫ i) ∧
      (k ≫ Limits.pullback.fst p p ≫ p = H.toBase) ∧
      (k ≫ Limits.pullback.snd p p ≫ p = H.toBase) := by
  let : Etale s := hs
  let : FormallyUnramified s := inferInstance
  exact exists_universalThickening_of_relation_pair s t q i p hu
    (MorphismProperty.comp_mem @FormallyUnramified s q inferInstance hq) hbase

lemma exists_universal_relation_pair_lift
    {R W V U V' : Scheme.{u}} (r : R ⟶ W) (f g : W ⟶ U)
    (s t : R ⟶ V) (q : V ⟶ U) (i : V ⟶ V') (p : V' ⟶ U)
    (hu : Stacks.Thickenings.IsUniversalFirstOrderThickening q i p)
    (hr : FormallyUnramified r)
    (hf : Etale f) (hg : Etale g)
    (hsource : r ≫ f = s ≫ q) (htarget : r ≫ g = t ≫ q) :
    let H := Stacks.Thickenings.universalFirstOrderThickening r
    ∃ (k : H.ambient ⟶ V' ⨯ V'),
      (H.inclusion ≫ k ≫ Limits.prod.fst = s ≫ i) ∧
      (H.inclusion ≫ k ≫ Limits.prod.snd = t ≫ i) ∧
      (k ≫ Limits.prod.fst ≫ p = H.toBase ≫ f) ∧
      (k ≫ Limits.prod.snd ≫ p = H.toBase ≫ g) ∧
      FormallyUnramified (k ≫ Limits.prod.fst) ∧
      FormallyUnramified (k ≫ Limits.prod.snd) := by
  let : FormallyUnramified r := hr
  let H := Stacks.Thickenings.universalFirstOrderThickening r
  have hlift : ∀ (c : R ⟶ V) (e : W ⟶ U), r ≫ e = c ≫ q →
      H.inclusion ≫ (H.toBase ≫ e) = c ≫ q := fun c e he => by
    rw [← Category.assoc, H.isUniversal.inclusion_toBase, he]
  have hs := hlift s f hsource
  have ht := hlift t g htarget
  obtain ⟨k, hk, _⟩ := universalThickening_lift_pair_distinct_base
    H.inclusion H.isUniversal.isFirstOrderThickening s t (H.toBase ≫ f) (H.toBase ≫ g)
    q i p hu hs ht
  let : FormallyUnramified H.toBase :=
    Stacks.Thickenings.UniversalFirstOrderThickening.formallyUnramified_toBase H
  have hproj : ∀ (e : W ⟶ U) (π : V' ⨯ V' ⟶ V'), Etale e →
      k ≫ π ≫ p = H.toBase ≫ e → FormallyUnramified (k ≫ π) := by
    intro e π he hke
    let : Etale e := he
    let : FormallyUnramified ((k ≫ π) ≫ p) := by
      rw [Category.assoc, hke]
      exact MorphismProperty.comp_mem @FormallyUnramified H.toBase e inferInstance inferInstance
    exact FormallyUnramified.of_comp (k ≫ π) p
  exact ⟨k, hk.1, hk.2.1, hk.2.2.1, hk.2.2.2, hproj f _ hf hk.2.2.1, hproj g _ hg hk.2.2.2⟩

private lemma exists_targetRelation_map_of_chartKernelPair
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicGeometry.AlgebraicSpaces B S hS} {h : Z ⟶ X}
    (D : ChartThickening B S hS h)
    (K : ChartKernelPair B S hS D.sourceChart) :
    ∃ (W : AlgebraicGeometry.BigFppfOver B S hS)
      (α β : W ⟶ D.U) (r : K.R ⟶ W),
      r ≫ α = K.source ≫ D.chartMap ∧
      r ≫ β = K.target ≫ D.chartMap ∧
      Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map α) ∧
      Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map β) ∧
      IsPullback (yoneda.map α) (yoneda.map β)
        D.targetChart D.targetChart := by
  classical
  let : Limits.HasBinaryProducts (AlgebraicGeometry.BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let hd := X.property.diagonal_representable.of_diag D.targetChart
  let W := hd.pullback D.targetChart
  let α : W ⟶ D.U := yoneda.preimage (hd.fst D.targetChart)
  let β : W ⟶ D.U := hd.snd D.targetChart
  have hpb : IsPullback (yoneda.map α) (yoneda.map β)
      D.targetChart D.targetChart := by
    simpa [α, β] using hd.isPullback D.targetChart
  let f := K.source ≫ D.chartMap
  let g := K.target ≫ D.chartMap
  have hfg : yoneda.map f ≫ D.targetChart = yoneda.map g ≫ D.targetChart := by
    have hmap : ∀ c : K.R ⟶ D.V, yoneda.map (c ≫ D.chartMap) ≫ D.targetChart =
        (yoneda.map c ≫ D.sourceChart) ≫ h.hom := fun c => by
      rw [Functor.map_comp, Category.assoc, D.comm, Category.assoc]
    change yoneda.map (K.source ≫ D.chartMap) ≫ D.targetChart =
      yoneda.map (K.target ≫ D.chartMap) ≫ D.targetChart
    rw [hmap, hmap, K.kernelPair.w]
  let r' := hpb.lift (yoneda.map f) (yoneda.map g) hfg
  let r : K.R ⟶ W := yoneda.preimage r'
  have hrα : r ≫ α = f := by
    apply Functor.map_injective yoneda
    rw [Functor.map_comp, yoneda.map_preimage, hpb.lift_fst]
  have hrβ : r ≫ β = g := by
    apply Functor.map_injective yoneda
    rw [Functor.map_comp, yoneda.map_preimage, hpb.lift_snd]
  have hα : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map α) :=
    D.targetEtale.property D.targetChart (yoneda.map β) α hpb.flip
  have hβ : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map β) :=
    D.targetEtale.property D.targetChart (yoneda.map α) β hpb
  exact ⟨W, α, β, r, hrα, hrβ, hα, hβ, hpb⟩

/-- Maps with equal composites to `a` lift through a pullback of `yoneda.map α`, `yoneda.map β`. -/
theorem exists_lift_of_isPullback_yoneda {C : Type*} [Category.{u} C] {U W T : C}
    {F : Cᵒᵖ ⥤ Type u} {a : yoneda.obj U ⟶ F} {α β : W ⟶ U}
    (hW : IsPullback (yoneda.map α) (yoneda.map β) a a) (f g : T ⟶ U)
    (h : yoneda.map f ≫ a = yoneda.map g ≫ a) :
    ∃ l : T ⟶ W, l ≫ α = f ∧ l ≫ β = g := by
  refine ⟨yoneda.preimage (hW.lift _ _ h), ?_, ?_⟩
  · apply Functor.map_injective yoneda
    rw [Functor.map_comp, yoneda.map_preimage]
    exact hW.lift_fst _ _ _
  · apply Functor.map_injective yoneda
    rw [Functor.map_comp, yoneda.map_preimage]
    exact hW.lift_snd _ _ _

lemma bridge_targetRelation_diagonal
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U W : AlgebraicGeometry.BigFppfOver B S hS}
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : yoneda.obj U ⟶ F) (α β : W ⟶ U)
    (hW : IsPullback (yoneda.map α) (yoneda.map β) a a) :
    ∃ d : U ⟶ W, d ≫ α = 𝟙 U ∧ d ≫ β = 𝟙 U :=
  exists_lift_of_isPullback_yoneda hW _ _ rfl

lemma bridge_targetRelation_swap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U W : AlgebraicGeometry.BigFppfOver B S hS}
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : yoneda.obj U ⟶ F) (α β : W ⟶ U)
    (hW : IsPullback (yoneda.map α) (yoneda.map β) a a) :
    ∃ e : W ⟶ W, e ≫ α = β ∧ e ≫ β = α :=
  exists_lift_of_isPullback_yoneda hW _ _ hW.w.symm

lemma bridge_targetRelation_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U W : AlgebraicGeometry.BigFppfOver B S hS}
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : yoneda.obj U ⟶ F) (α β : W ⟶ U)
    (hW : IsPullback (yoneda.map α) (yoneda.map β) a a) :
    ∃ c : Limits.pullback β α ⟶ W,
      c ≫ α = Limits.pullback.fst β α ≫ α ∧
      c ≫ β = Limits.pullback.snd β α ≫ β := by
  refine exists_lift_of_isPullback_yoneda hW _ _ ?_
  have hpb : Limits.pullback.fst β α ≫ β = Limits.pullback.snd β α ≫ α :=
    Limits.pullback.condition
  calc
    _ = yoneda.map (Limits.pullback.fst β α ≫ β) ≫ a := by
      simp only [Functor.map_comp, Category.assoc, hW.w]
    _ = yoneda.map (Limits.pullback.snd β α ≫ α) ≫ a := by rw [hpb]
    _ = _ := by simp only [Functor.map_comp, Category.assoc, hW.w]

lemma formallyUnramified_yoneda_map_of_formallyUnramified_chart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R W V U : AlgebraicGeometry.BigFppfOver B S hS}
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (r : R ⟶ W) (α β : W ⟶ U) (s t : R ⟶ V) (q : V ⟶ U)
    (a : yoneda.obj V ⟶ F)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) a a)
    (hrα : r ≫ α = s ≫ q) (hrβ : r ≫ β = t ≫ q)
    (hq : FormallyUnramified
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)) :
    AlgebraicGeometry.Space.FormallyUnramified (yoneda.map r) := by
  let Tscheme := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let : FormallyUnramified (Tscheme.map q) := hq
  intro T T' hT hT' j hj x y hxy z₁ z₂ hz₁ hz₂
  rcases hz₁ with ⟨hz₁r, hz₁b⟩
  rcases hz₂ with ⟨hz₂r, hz₂b⟩
  change j ≫ z₁ = x at hz₁r
  change z₁ ≫ r = y at hz₁b
  change j ≫ z₂ = x at hz₂r
  change z₂ ≫ r = y at hz₂b
  change Stacks.Thickenings.IsFirstOrderThickening (Tscheme.map j) at hj
  let : IsClosedImmersion (Tscheme.map j) := hj.1
  have key : ∀ (c : R ⟶ V) (γ : W ⟶ U), r ≫ γ = c ≫ q → z₁ ≫ c = z₂ ≫ c := by
    intro c γ hrγ
    have hRestr : j ≫ (z₁ ≫ c) = j ≫ (z₂ ≫ c) := by
      rw [← Category.assoc, hz₁r, ← Category.assoc, hz₂r]
    have hBase : (z₁ ≫ c) ≫ q = (z₂ ≫ c) ≫ q := by
      rw [Category.assoc, Category.assoc, ← hrγ, ← Category.assoc, ← Category.assoc, hz₁b, hz₂b]
    apply Tscheme.map_injective
    simp only [Functor.map_comp]
    apply FormallyUnramified.hom_ext (Tscheme.map j)
      ⟨2, by simpa using hj.2⟩ (Tscheme.map q)
    · simpa only [Functor.map_comp, Category.assoc] using congrArg Tscheme.map hRestr
    · simpa only [Functor.map_comp, Category.assoc] using congrArg Tscheme.map hBase
  apply Functor.map_injective yoneda
  apply hR.hom_ext
  · simpa only [Functor.map_comp] using congrArg yoneda.map (key s α hrα)
  · simpa only [Functor.map_comp] using congrArg yoneda.map (key t β hrβ)

lemma formallyUnramified_scheme_map_of_yoneda
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R W : AlgebraicGeometry.BigFppfOver B S hS} (r : R ⟶ W)
    (hr : AlgebraicGeometry.Space.FormallyUnramified (yoneda.map r)) :
    FormallyUnramified ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map r) := by
  let hR := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS R
  let hW := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W
  have hchart :=
    (AlgebraicGeometry.Space.formallyUnramified_iff_etaleCharts B S hS hR hW (yoneda.map r)).mp hr
  have hEtale : ∀ X : AlgebraicGeometry.BigFppfOver B S hS,
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj X)) :=
    AlgebraicGeometry.presheaf_id_of_iso B S hS _ (fun _ _ f hf => by
      have : IsIso f := hf
      change Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f)
      infer_instance)
  have hcomm : yoneda.map r ≫ 𝟙 (yoneda.obj W) =
      𝟙 (yoneda.obj R) ≫ yoneda.map r := by simp
  exact hchart R W (𝟙 (yoneda.obj R)) (𝟙 (yoneda.obj W)) r
    (hEtale R) (hEtale W) hcomm

private lemma exists_lifted_chartKernelPair_over_targetRelation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicGeometry.AlgebraicSpaces B S hS} {h : Z ⟶ X}
    (D : ChartThickening B S hS h)
    (K : ChartKernelPair B S hS D.sourceChart) :
    ∃ (W : AlgebraicGeometry.BigFppfOver B S hS)
      (α β : W ⟶ D.U) (r : K.R ⟶ W)
      (H : Stacks.Thickenings.UniversalFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map r))
      (k : H.ambient ⟶ D.thickening.ambient ⨯ D.thickening.ambient),
      r ≫ α = K.source ≫ D.chartMap ∧
      r ≫ β = K.target ≫ D.chartMap ∧
      Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map α) ∧
      Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map β) ∧
      IsPullback (yoneda.map α) (yoneda.map β)
        D.targetChart D.targetChart ∧
      Stacks.Thickenings.IsUniversalFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map r ≫
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map α)
        H.inclusion (H.toBase ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map α) ∧
      Stacks.Thickenings.IsUniversalFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map r ≫
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map β)
        H.inclusion (H.toBase ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map β) ∧
        (H.inclusion ≫ k ≫ Limits.prod.fst =
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map K.source ≫
            D.thickening.inclusion) ∧
        (H.inclusion ≫ k ≫ Limits.prod.snd =
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map K.target ≫
            D.thickening.inclusion) ∧
        (k ≫ Limits.prod.fst ≫ D.thickening.toBase =
          H.toBase ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map α) ∧
        (k ≫ Limits.prod.snd ≫ D.thickening.toBase =
          H.toBase ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map β) ∧
        FormallyUnramified (k ≫ Limits.prod.fst) ∧
        FormallyUnramified (k ≫ Limits.prod.snd) := by
  obtain ⟨W, α, β, r, hrα, hrβ, hα, hβ, hWpb⟩ :=
    exists_targetRelation_map_of_chartKernelPair B S hS D K
  have hrSite := formallyUnramified_yoneda_map_of_formallyUnramified_chart
    B S hS r α β K.source K.target D.chartMap D.sourceChart K.kernelPair
    hrα hrβ D.formallyUnramified
  have hrScheme := formallyUnramified_scheme_map_of_yoneda B S hS r hrSite
  have hsource : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map r ≫
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map α =
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map K.source ≫
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map D.chartMap := by
    simpa only [Functor.map_comp] using congrArg
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map hrα
  have htarget : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map r ≫
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map β =
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map K.target ≫
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map D.chartMap := by
    simpa only [Functor.map_comp] using congrArg
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map hrβ
  obtain ⟨k, hk1, hk2, hk3, hk4, hk5, hk6⟩ :=
    exists_universal_relation_pair_lift
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map r)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map α)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map β)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map K.source)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map K.target)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map D.chartMap)
      D.thickening.inclusion D.thickening.toBase D.thickening.isUniversal
      hrScheme hα hβ hsource htarget
  let H := Stacks.Thickenings.universalFirstOrderThickening
    ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map r)
  exact ⟨W, α, β, r, H, k, hrα, hrβ, hα, hβ, hWpb,
    bridge_universalThickening_comp_etale _ _ _ _ H.isUniversal hα,
    bridge_universalThickening_comp_etale _ _ _ _ H.isUniversal hβ,
    hk1, hk2, hk3, hk4, hk5, hk6⟩

lemma bridge_descend_map_from_atlas
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y T : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hT : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) T)
    {V R : AlgebraicGeometry.BigFppfOver B S hS} (s t : R ⟶ V)
    (q : yoneda.obj V ⟶ Y)
    (hK : IsPullback (yoneda.map s) (yoneda.map t) q q)
    (hsurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (hetale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (f : yoneda.obj V ⟶ T)
    (hf : yoneda.map s ≫ f = yoneda.map t ≫ f) :
    ∃ g : Y ⟶ T, q ≫ g = f := by
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  obtain ⟨hRsh, hVsh, ⟨hc⟩⟩ :=
    AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale
      B S hS q s t hK hY hsurj hetale
  let sf : (⟨yoneda.obj R, hRsh⟩ : Sheaf J (Type u)) ⟶
      ⟨yoneda.obj V, hVsh⟩ := ⟨yoneda.map s⟩
  let tf : (⟨yoneda.obj R, hRsh⟩ : Sheaf J (Type u)) ⟶
      ⟨yoneda.obj V, hVsh⟩ := ⟨yoneda.map t⟩
  let ff : (⟨yoneda.obj V, hVsh⟩ : Sheaf J (Type u)) ⟶
      ⟨T, hT⟩ := ⟨f⟩
  let c : Cofork sf tf := Cofork.ofπ ff
    (show sf ≫ ff = tf ≫ ff from Sheaf.hom_ext hf)
  exact ⟨(hc.desc c).hom,
    congrArg (fun k => k.hom) (hc.fac c WalkingParallelPair.one)⟩

lemma bridge_maps_equal_of_atlas
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y T : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hT : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) T)
    {V R : AlgebraicGeometry.BigFppfOver B S hS} (s t : R ⟶ V)
    (q : yoneda.obj V ⟶ Y)
    (hK : IsPullback (yoneda.map s) (yoneda.map t) q q)
    (hsurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (hetale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (f g : Y ⟶ T) (hfg : q ≫ f = q ≫ g) : f = g := by
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  obtain ⟨hRsh, hVsh, ⟨hc⟩⟩ :=
    AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale
      B S hS q s t hK hY hsurj hetale
  let ff : (⟨Y, hY.isSheaf⟩ : Sheaf J (Type u)) ⟶
      ⟨T, hT⟩ := ⟨f⟩
  let gg : (⟨Y, hY.isSheaf⟩ : Sheaf J (Type u)) ⟶
      ⟨T, hT⟩ := ⟨g⟩
  have heq : ff = gg := by
    apply Cofork.IsColimit.hom_ext hc
    exact Sheaf.hom_ext hfg
  exact congrArg (fun k => k.hom) heq

lemma bridge_subschemePoints_mk
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V U : AlgebraicGeometry.BigFppfOver B S hS} (f : V ⟶ U)
    [Mono ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f)] :
    AlgebraicGeometry.Space.subschemePoints B S hS
      (Subobject.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f)) =
        Subfunctor.range (yoneda.map f) := by
  ext T x
  change (∃ g, g ≫ _ = _) ↔ ∃ y, y ≫ f = x
  apply (Subobject.factors_iff _ _).symm.trans
  rw [Subobject.mk_factors_iff]
  change (∃ g, g ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f =
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map x) ↔ ∃ y, y ≫ f = x
  constructor
  · rintro ⟨g, hg⟩
    let g' : T.unop.left ⟶ V.left := B.inclusion.preimage g
    have hmapg : B.inclusion.map g' = g := B.inclusion.map_preimage g
    have hg' : g ≫ B.inclusion.map f.left = B.inclusion.map x.left := hg
    have hw : g' ≫ V.hom = T.unop.hom := by
      apply B.inclusion.map_injective
      rw [Functor.map_comp, hmapg]
      calc
        g ≫ B.inclusion.map V.hom =
            g ≫ B.inclusion.map (f.left ≫ U.hom) := by rw [Over.w]
        _ = B.inclusion.map x.left ≫ B.inclusion.map U.hom := by
          rw [Functor.map_comp, ← Category.assoc, hg']
        _ = B.inclusion.map T.unop.hom := by rw [← Functor.map_comp, Over.w]
    refine ⟨Over.homMk g' hw, ?_⟩
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change B.inclusion.map (g' ≫ f.left) = B.inclusion.map x.left
    rw [Functor.map_comp, hmapg, hg']
  · rintro ⟨g, rfl⟩
    exact ⟨(AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g,
      (Functor.map_comp _ _ _).symm⟩

lemma bridge_isPullback_fromPreimage
    {C : Type*} [Category C] {F G : C ⥤ Type u}
    (Z : Subfunctor F) (f : G ⟶ F) :
    IsPullback (Z.fromPreimage f) (Z.preimage f).ι Z.ι f := by
  let c := PullbackCone.mk (Z.fromPreimage f) (Z.preimage f).ι
    (Z.fromPreimage_ι f)
  have hmem (s : PullbackCone Z.ι f) : Subfunctor.range s.snd ≤ Z.preimage f := by
    rintro U z ⟨x, rfl⟩
    have hx := congrArg (fun q => q.app U x) s.condition
    change (s.fst.app U x).val = f.app U (s.snd.app U x) at hx
    change f.app U (s.snd.app U x) ∈ Z.obj U
    exact hx ▸ (s.fst.app U x).property
  apply IsPullback.of_isLimit (c := c)
  refine PullbackCone.IsLimit.mk (Z.fromPreimage_ι f)
    (fun s => Subfunctor.lift s.snd (hmem s)) ?_ ?_ ?_
  · intro s
    apply (cancel_mono Z.ι).mp
    change (Subfunctor.lift s.snd (hmem s) ≫ Z.fromPreimage f) ≫ Z.ι =
      s.fst ≫ Z.ι
    rw [Category.assoc, Z.fromPreimage_ι, ← Category.assoc, Subfunctor.lift_ι]
    exact s.condition.symm
  · intro s
    exact Subfunctor.lift_ι _ _
  · intro s m hm₁ hm₂
    apply (cancel_mono (Z.preimage f).ι).mp
    exact hm₂.trans (Subfunctor.lift_ι _ _).symm

lemma bridge_isPullback_of_preimage_eq_range
    {C : Type*} [Category C] {F G H : C ⥤ Type u}
    (Z : Subfunctor F) (f : G ⟶ F) (i : H ⟶ G) [Mono i]
    (hi : Z.preimage f = Subfunctor.range i) :
    ∃ a : H ⟶ Z.toFunctor, IsPullback a i Z.ι f := by
  let e : H ≅ (Z.preimage f).toFunctor :=
    asIso (Subfunctor.toRange i) ≪≫ eqToIso (congrArg Subfunctor.toFunctor hi.symm)
  refine ⟨e.hom ≫ Z.fromPreimage f, ?_⟩
  apply (bridge_isPullback_fromPreimage Z f).of_iso' e
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp
  · change Subfunctor.toRange i ≫
      eqToHom (congrArg Subfunctor.toFunctor hi.symm) ≫ (Z.preimage f).ι = i ≫ 𝟙 _
    rw [subfunctor_eqToHom_ι hi.symm,
      Subfunctor.toRange_ι, Category.comp_id]
  · simp
  · simp

lemma bridge_restricted_kernelPair
    {C : Type*} [Category C]
    {R V R' V' Q : C} (s t : R ⟶ V) (s' t' : R' ⟶ V')
    (iV : V ⟶ V') (iR : R ⟶ R') (q : V' ⟶ Q)
    [Mono iV]
    (hs : IsPullback s iR iV s')
    (ht : iR ≫ t' = t ≫ iV)
    (hR' : IsPullback s' t' q q) :
    IsPullback s t (iV ≫ q) (iV ≫ q) := by
  apply IsPullback.mk' (by
    calc
      s ≫ (iV ≫ q) = (s ≫ iV) ≫ q := (Category.assoc _ _ _).symm
      _ = (iR ≫ s') ≫ q := by rw [hs.w]
      _ = (iR ≫ t') ≫ q := by simp only [Category.assoc, hR'.w]
      _ = (t ≫ iV) ≫ q := by rw [ht]
      _ = t ≫ (iV ≫ q) := Category.assoc _ _ _)
  · intro T a b ha hb
    apply hs.hom_ext ha
    apply hR'.hom_ext
    · simpa only [Category.assoc, ← hs.w] using
        congrArg (fun f => f ≫ iV) ha
    · simpa only [Category.assoc, ht] using
        congrArg (fun f => f ≫ iV) hb
  · intro T a b hab
    have heq : (a ≫ iV) ≫ q = (b ≫ iV) ≫ q := by
      simpa only [Category.assoc] using hab
    let z : T ⟶ R' := hR'.lift (a ≫ iV) (b ≫ iV) heq
    have hz : a ≫ iV = z ≫ s' := (hR'.lift_fst _ _ _).symm
    let l : T ⟶ R := hs.lift a z hz
    refine ⟨l, hs.lift_fst _ _ _, ?_⟩
    apply (cancel_mono iV).mp
    calc
      (l ≫ t) ≫ iV = l ≫ (iR ≫ t') := by rw [Category.assoc, ht]
      _ = (l ≫ iR) ≫ t' := (Category.assoc _ _ _).symm
      _ = z ≫ t' := by rw [hs.lift_snd]
      _ = b ≫ iV := hR'.lift_snd _ _ _

end Stacks.Spaces.UniversalThickening

end
