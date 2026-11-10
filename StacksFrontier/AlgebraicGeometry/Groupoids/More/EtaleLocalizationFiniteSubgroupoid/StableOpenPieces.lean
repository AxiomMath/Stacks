module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.CardForm
public import StacksFrontier.AlgebraicGeometry.Descent.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidBaseChange
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.CommonField
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.Decomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapPullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.EtaleLocalizationFiniteSubgroupoid.OrbitFiniteness

/-!
# Stable open-and-closed pieces of a groupoid

Preliminaries for `AlgebraicGeometry.GroupoidScheme.exists_finite_openClosed_subgroupoid`
(Stacks Project, Tag 03FL): finite coproduct decompositions of schemes and their base
changes, the subgroupoid cut out by compatible open immersions, rebasing a groupoid along a
base change, and the restriction of a groupoid to open pieces stable under its source and
target maps.

## Main definitions

No new public definitions are introduced.

## References

* [Stacks Project, Tag 03FL](https://stacks.math.columbia.edu/tag/03FL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidScheme

lemma finite_union_of_components {B S : Scheme.{u}} (f : B ⟶ S)
    (n : ℕ) (X : Option (Fin n) → Scheme.{u}) (j : ∀ i, X i ⟶ B)
    (ho : ∀ i, IsOpenImmersion (j i)) (hc : ∀ i, IsClosedImmersion (j i))
    [IsIso (Sigma.desc j)] (hf : ∀ i, IsFinite (j (some i) ≫ f)) :
    ∃ (Y : Scheme.{u}) (k : Y ⟶ B), IsOpenImmersion k ∧ IsClosedImmersion k ∧
      IsFinite (k ≫ f) ∧ IsIso (coprod.desc k (j none)) ∧
      Set.range k = ⋃ i, Set.range (j (some i)) := by
  let X' := fun i : Fin n => X (some i)
  let k : ∐ X' ⟶ B := Sigma.desc fun i => j (some i)
  have : ∀ i, IsOpenImmersion (j i) := ho
  have : IsOpenImmersion k := isOpenImmersion_sigmaDesc X' _
    (fun i l hil => disjoint_ranges_of_sigma_desc_iso j (by simpa using hil))
  have hr : Set.range k = ⋃ i, Set.range (j (some i)) := range_sigma_desc _
  have : IsClosedImmersion k := by
    apply IsClosedImmersion.of_isPreimmersion
    rw [hr]
    apply isClosed_iUnion_of_finite
    intro i
    have : IsClosedImmersion (j (some i)) := hc (some i)
    exact (j (some i)).isClosedEmbedding.isClosed_range
  have : IsFinite (k ≫ f) := by
    have he : k ≫ f = Sigma.desc (fun i => j (some i) ≫ f) := by
      apply Sigma.hom_ext
      intro i
      simp [k, X']
    rw [he]
    exact finite_sigma_desc n X' _ hf
  exact ⟨∐ X', k, inferInstance, inferInstance, inferInstance,
    isIso_coprod_desc_sigma_option j, hr⟩

lemma selected_components_fiber {B S Z : Scheme.{u}}
    (f : B ⟶ S) (g : B ⟶ Z) (p : S) {n : ℕ}
    (X : Option (Fin n) → Scheme.{u}) (j : ∀ i, X i ⟶ B)
    [IsIso (Sigma.desc j)] (v : ∀ i, X (some i)) (x : Fin n → Z)
    (hv : ∀ i, (j (some i) ≫ g) (v i) = x i)
    (hf : ∀ i, {a : X (some i) | (j (some i) ≫ f) a = p} = {v i})
    (hc : ∀ a : X none, (j none ≫ f) a = p →
      ∀ i, (j none ≫ g) a ≠ x i)
    (z : B) (hz : f z = p) :
    z ∈ (⋃ i, Set.range (j (some i))) ↔ g z ∈ Set.range x := by
  constructor
  · intro h
    obtain ⟨i, a, rfl⟩ := Set.mem_iUnion.mp h
    have ha : a = v i := by
      apply Set.mem_singleton_iff.mp
      rw [← hf i]
      exact hz
    exact ⟨i, (hv i).symm.trans (by rw [ha]; rfl)⟩
  · rintro ⟨i, hi⟩
    have hcover : z ∈ Set.range (Sigma.desc j) := (Sigma.desc j).surjective z
    rw [range_sigma_desc] at hcover
    obtain ⟨a, b, rfl⟩ := Set.mem_iUnion.mp hcover
    cases a with
    | none => exact ((hc b hz i) hi.symm).elim
    | some a => exact Set.mem_iUnion.mpr ⟨a, b, rfl⟩

lemma finite_pullback_piece {B B' S S' Y : Scheme.{u}}
    {a : B' ⟶ B} {b : B' ⟶ S'} {f : B ⟶ S} {q : S' ⟶ S}
    (h : IsPullback a b f q) (j : Y ⟶ B) [IsFinite (j ≫ f)] :
    IsFinite (pullback.snd j a ≫ b) := by
  have hc := ((IsPullback.of_hasPullback j a).flip.paste_horiz h.flip).flip
  rw [← hc.isoPullback_hom_snd]
  infer_instance

lemma pullback_map_base_isPullback {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (h : T' ⟶ S) (q : T' ⟶ T) (hq : q ≫ g = h) :
    IsPullback (pullback.map f h f g (𝟙 X) q (𝟙 S) (by simp) (by simpa using hq.symm))
      (pullback.snd f h) (pullback.snd f g) q := by
  let m := pullback.map f h f g (𝟙 X) q (𝟙 S) (by simp) (by simpa using hq.symm)
  have ht : IsPullback (m ≫ pullback.fst f g) (pullback.snd f h) f (q ≫ g) := by
    simpa [m, pullbackMap_fst, hq] using IsPullback.of_hasPullback f h
  exact ht.of_right (by simp [m]) (IsPullback.of_hasPullback f g)

lemma isCompl_ranges_coprod_desc {X Y B : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) [IsIso (coprod.desc f g)] :
    IsCompl (Set.range f) (Set.range g) := by
  constructor
  · apply Set.disjoint_left.mpr
    rintro z ⟨x, rfl⟩ ⟨y, hy⟩
    have he : (coprod.inl : X ⟶ X ⨿ Y) x = (coprod.inr : Y ⟶ X ⨿ Y) y := by
      apply (coprod.desc f g).isOpenEmbedding.injective
      simpa only [← Scheme.Hom.comp_apply, coprod.inl_desc, coprod.inr_desc] using hy.symm
    exact Set.disjoint_iff_forall_ne.mp (isCompl_range_inl_inr X Y).1
      ⟨x, rfl⟩ ⟨y, rfl⟩ he
  · rw [codisjoint_iff]
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨w, rfl⟩ := (coprod.desc f g).surjective z
    obtain ⟨x | y, rfl⟩ := (coprodMk X Y).surjective w
    · exact Or.inl ⟨x, by simp only [coprodMk_inl, ← Scheme.Hom.comp_apply,
        coprod.inl_desc]⟩
    · exact Or.inr ⟨y, by simp only [coprodMk_inr, ← Scheme.Hom.comp_apply,
        coprod.inr_desc]⟩

lemma isIso_coprod_desc_pullback {X Y B B' : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (a : B' ⟶ B)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsIso (coprod.desc f g)] :
    IsIso (coprod.desc (pullback.snd f a) (pullback.snd g a)) := by
  have h : IsCompl (pullback.snd f a).opensRange (pullback.snd g a).opensRange := by
    rw [Scheme.Hom.opensRange_pullbackSnd, Scheme.Hom.opensRange_pullbackSnd]
    convert (isCompl_ranges_coprod_desc f g).map (CompleteLatticeHom.setPreimage a) using 1
    simp [isCompl_iff, disjoint_iff, codisjoint_iff, ← TopologicalSpace.Opens.coe_inj]
  obtain ⟨hc⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl _ _ h
  change IsIso ((coprodIsCoprod _ _).coconePointUniqueUpToIso hc).hom
  infer_instance

/-- On generalized points, composing two arrows of a subgroupoid given by compatible maps and
then including the result agrees with composing the two included arrows. -/
lemma lift_comp_compatible
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) {U R : Over S}
    (jU : U ⟶ G.objects) (jR : R ⟶ G.arrows) (s t : R ⟶ U) (c : pullback s t ⟶ R)
    (hs : s ≫ jU = jR ≫ G.source) (ht : t ≫ jU = jR ≫ G.target)
    (hc : c ≫ jR = pullback.map s t G.source G.target jR jR jU hs ht ≫ G.comp)
    {T : Over S} (a b : T ⟶ R) (w : a ≫ s = b ≫ t)
    (w' : (a ≫ jR) ≫ G.source = (b ≫ jR) ≫ G.target) :
    (pullback.lift a b w ≫ c) ≫ jR =
      pullback.lift (a ≫ jR) (b ≫ jR) w' ≫ G.comp := by
  rw [Category.assoc, hc]
  show pullback.lift a b w ≫ pullback.map s t G.source G.target jR jR jU hs ht ≫ G.comp = _
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

def subgroupoidOfCompatibleMaps
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) (U R : Over S)
    (jU : U ⟶ G.objects) (jR : R ⟶ G.arrows) [Mono jU] [Mono jR]
    (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R)
    (hs : s ≫ jU = jR ≫ G.source) (ht : t ≫ jU = jR ≫ G.target)
    (he : e ≫ jR = jU ≫ G.identity) (hi : i ≫ jR = jR ≫ G.inverse)
    (hc : c ≫ jR = pullback.map s t G.source G.target jR jR jU hs ht ≫ G.comp) :
    Stacks.Groupoids.GroupoidScheme S := by
  let k := pullback.map s t G.source G.target jR jR jU hs ht
  have hkf : k ≫ pullback.fst G.source G.target = pullback.fst s t ≫ jR := by
    simp [k]
  have hks : k ≫ pullback.snd G.source G.target = pullback.snd s t ≫ jR := by
    simp [k]
  have map_rel {T : Over S} (a b : T ⟶ R) (w : a ≫ s = b ≫ t) :
      (a ≫ jR) ≫ G.source = (b ≫ jR) ≫ G.target := by
    simpa only [Category.assoc, hs, ht] using congrArg (· ≫ jU) w
  have map_comp {T : Over S} (a b : T ⟶ R) (w : a ≫ s = b ≫ t)
      (w' : (a ≫ jR) ≫ G.source = (b ≫ jR) ≫ G.target) :
      (pullback.lift a b w ≫ c) ≫ jR =
        pullback.lift (a ≫ jR) (b ≫ jR) w' ≫ G.comp :=
    lift_comp_compatible G jU jR s t c hs ht hc a b w w'
  have hcs : c ≫ s = pullback.snd s t ≫ s := by
    apply (cancel_mono jU).mp
    simp only [Category.assoc, hs, reassoc_of% hc, G.source_comp]
    change k ≫ pullback.snd G.source G.target ≫ G.source = _
    rw [reassoc_of% hks]
  have hct : c ≫ t = pullback.fst s t ≫ t := by
    apply (cancel_mono jU).mp
    simp only [Category.assoc, ht, reassoc_of% hc, G.target_comp]
    change k ≫ pullback.fst G.source G.target ≫ G.target = _
    rw [reassoc_of% hkf]
  refine
    { objects := U
      arrows := R
      source := s
      target := t
      comp := c
      identity := e
      inverse := i
      source_identity := ?_
      target_identity := ?_
      source_inverse := ?_
      target_inverse := ?_
      source_comp := hcs
      target_comp := hct
      left_identity := ?_
      right_identity := ?_
      left_inverse := ?_
      right_inverse := ?_
      assoc := ?_ }
  · apply (cancel_mono jU).mp
    simp only [Category.assoc, hs, reassoc_of% he, G.source_identity,
      Category.comp_id, Category.id_comp]
  · apply (cancel_mono jU).mp
    simp only [Category.assoc, ht, reassoc_of% he, G.target_identity,
      Category.comp_id, Category.id_comp]
  · apply (cancel_mono jU).mp
    simp only [Category.assoc, hs, ht, reassoc_of% hi, G.source_inverse]
  · apply (cancel_mono jU).mp
    simp only [Category.assoc, hs, ht, reassoc_of% hi, G.target_inverse]
  · intro T a w
    apply (cancel_mono jR).mp
    rw [map_comp _ _ w (map_rel _ _ w)]
    simpa only [Category.assoc, he, reassoc_of% ht] using
      G.left_identity T (a ≫ jR)
        (by simp only [Category.assoc, G.source_identity, Category.comp_id])
  · intro T a w
    apply (cancel_mono jR).mp
    rw [map_comp _ _ w (map_rel _ _ w)]
    simpa only [Category.assoc, he, reassoc_of% hs] using
      G.right_identity T (a ≫ jR)
        (by simp only [Category.assoc, G.target_identity, Category.comp_id])
  · intro T a w
    apply (cancel_mono jR).mp
    rw [map_comp _ _ w (map_rel _ _ w)]
    simpa only [Category.assoc, hi, he, reassoc_of% hs] using
      G.left_inverse T (a ≫ jR) (by simp only [Category.assoc, G.source_inverse])
  · intro T a w
    apply (cancel_mono jR).mp
    rw [map_comp _ _ w (map_rel _ _ w)]
    simpa only [Category.assoc, hi, he, reassoc_of% ht] using
      G.right_inverse T (a ≫ jR) (by simp only [Category.assoc, G.target_inverse])
  · intro T a b d wab wbd w₁ w₂
    apply (cancel_mono jR).mp
    rw [map_comp _ _ w₁ (map_rel _ _ w₁), map_comp _ _ w₂ (map_rel _ _ w₂)]
    simp only [map_comp _ _ wab (map_rel _ _ wab), map_comp _ _ wbd (map_rel _ _ wbd)]
    exact G.assoc T (a ≫ jR) (b ≫ jR) (d ≫ jR) _ _ _ _

attribute [local implicit_reducible] subgroupoidOfCompatibleMaps

def subgroupoidOfCompatibleMapsHom
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) (U R : Over S)
    (jU : U ⟶ G.objects) (jR : R ⟶ G.arrows) [Mono jU] [Mono jR]
    (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R)
    (hs : s ≫ jU = jR ≫ G.source) (ht : t ≫ jU = jR ≫ G.target)
    (he : e ≫ jR = jU ≫ G.identity) (hi : i ≫ jR = jR ≫ G.inverse)
    (hc : c ≫ jR = pullback.map s t G.source G.target jR jR jU hs ht ≫ G.comp) :
    Stacks.Groupoids.GroupoidScheme.Hom
      (subgroupoidOfCompatibleMaps G U R jU jR s t e i c hs ht he hi hc) G := by
  refine
    { mapObjects := jU
      mapArrows := jR
      map_source := hs.symm
      map_target := ht.symm
      map_identity := he.symm
      map_comp := ?_ }
  intro T a b w w'
  change T ⟶ R at a b
  change a ≫ s = b ≫ t at w
  change (pullback.lift a b w ≫ c) ≫ jR =
    pullback.lift (a ≫ jR) (b ≫ jR) w' ≫ G.comp
  exact lift_comp_compatible G jU jR s t c hs ht hc a b w w'

attribute [local implicit_reducible] subgroupoidOfCompatibleMapsHom

def subgroupoidOfCompatibleMapsAlong
    {S T : Scheme.{u}} (F : Over T ⥤ Over S) [F.Faithful]
    (G : Stacks.Groupoids.GroupoidScheme S) (U R : Over T)
    (jU : F.obj U ⟶ G.objects) (jR : F.obj R ⟶ G.arrows) [Mono jU] [Mono jR]
    (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R)
    (hs : F.map s ≫ jU = jR ≫ G.source) (ht : F.map t ≫ jU = jR ≫ G.target)
    (he : F.map e ≫ jR = jU ≫ G.identity) (hi : F.map i ≫ jR = jR ≫ G.inverse)
    (hc : F.map c ≫ jR = pullbackComparison F s t ≫
      pullback.map (F.map s) (F.map t) G.source G.target jR jR jU hs ht ≫ G.comp) :
    Stacks.Groupoids.GroupoidScheme T := by
  let k := pullbackComparison F s t ≫
      pullback.map (F.map s) (F.map t) G.source G.target jR jR jU hs ht
  have hkf : k ≫ pullback.fst G.source G.target = F.map (pullback.fst s t) ≫ jR := by
    simp [k]
  have hks : k ≫ pullback.snd G.source G.target = F.map (pullback.snd s t) ≫ jR := by
    simp [k]
  have map_rel {Z : Over T} (a b : Z ⟶ R) (w : a ≫ s = b ≫ t) :
      (F.map a ≫ jR) ≫ G.source = (F.map b ≫ jR) ≫ G.target := by
    simpa only [Functor.map_comp, Category.assoc, hs, ht] using congrArg (fun z => F.map z ≫ jU) w
  have map_comp {Z : Over T} (a b : Z ⟶ R) (w : a ≫ s = b ≫ t)
      (w' : (F.map a ≫ jR) ≫ G.source = (F.map b ≫ jR) ≫ G.target) :
      F.map (pullback.lift a b w ≫ c) ≫ jR =
        pullback.lift (F.map a ≫ jR) (F.map b ≫ jR) w' ≫ G.comp := by
    rw [Functor.map_comp, Category.assoc, hc]
    change F.map (pullback.lift a b w) ≫ k ≫ G.comp = _
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, hkf, ← Category.assoc, ← F.map_comp, pullback.lift_fst,
        pullback.lift_fst]
    · rw [Category.assoc, hks, ← Category.assoc, ← F.map_comp, pullback.lift_snd,
        pullback.lift_snd]
  have hcs : c ≫ s = pullback.snd s t ≫ s := by
    apply F.map_injective
    apply (cancel_mono jU).mp
    simp only [Functor.map_comp]
    simp only [Category.assoc, hs, reassoc_of% hc, G.source_comp]
    change k ≫ pullback.snd G.source G.target ≫ G.source = _
    rw [reassoc_of% hks]
  have hct : c ≫ t = pullback.fst s t ≫ t := by
    apply F.map_injective
    apply (cancel_mono jU).mp
    simp only [Functor.map_comp]
    simp only [Category.assoc, ht, reassoc_of% hc, G.target_comp]
    change k ≫ pullback.fst G.source G.target ≫ G.target = _
    rw [reassoc_of% hkf]
  refine
    { objects := U
      arrows := R
      source := s
      target := t
      comp := c
      identity := e
      inverse := i
      source_identity := ?_
      target_identity := ?_
      source_inverse := ?_
      target_inverse := ?_
      source_comp := hcs
      target_comp := hct
      left_identity := ?_
      right_identity := ?_
      left_inverse := ?_
      right_inverse := ?_
      assoc := ?_ }
  · apply F.map_injective
    apply (cancel_mono jU).mp
    simp only [Functor.map_comp]
    simp only [Category.assoc, hs, reassoc_of% he, G.source_identity,
      Category.comp_id]
    rw [F.map_id, Category.id_comp]
  · apply F.map_injective
    apply (cancel_mono jU).mp
    simp only [Functor.map_comp]
    simp only [Category.assoc, ht, reassoc_of% he, G.target_identity,
      Category.comp_id]
    rw [F.map_id, Category.id_comp]
  · apply F.map_injective
    apply (cancel_mono jU).mp
    simp only [Functor.map_comp]
    simp only [Category.assoc, hs, ht, reassoc_of% hi, G.source_inverse]
  · apply F.map_injective
    apply (cancel_mono jU).mp
    simp only [Functor.map_comp]
    simp only [Category.assoc, hs, ht, reassoc_of% hi, G.target_inverse]
  · intro Z a w
    apply F.map_injective
    apply (cancel_mono jR).mp
    rw [map_comp _ _ w (map_rel _ _ w)]
    simpa only [Functor.map_comp, Category.assoc, he, reassoc_of% ht] using
      G.left_identity (F.obj Z) (F.map a ≫ jR)
        (by simp only [Category.assoc, G.source_identity, Category.comp_id])
  · intro Z a w
    apply F.map_injective
    apply (cancel_mono jR).mp
    rw [map_comp _ _ w (map_rel _ _ w)]
    simpa only [Functor.map_comp, Category.assoc, he, reassoc_of% hs] using
      G.right_identity (F.obj Z) (F.map a ≫ jR)
        (by simp only [Category.assoc, G.target_identity, Category.comp_id])
  · intro Z a w
    apply F.map_injective
    apply (cancel_mono jR).mp
    rw [map_comp _ _ w (map_rel _ _ w)]
    simpa only [Functor.map_comp, Category.assoc, hi, he, reassoc_of% hs] using
      G.left_inverse (F.obj Z) (F.map a ≫ jR) (by simp only [Category.assoc, G.source_inverse])
  · intro Z a w
    apply F.map_injective
    apply (cancel_mono jR).mp
    rw [map_comp _ _ w (map_rel _ _ w)]
    simpa only [Functor.map_comp, Category.assoc, hi, he, reassoc_of% ht] using
      G.right_inverse (F.obj Z) (F.map a ≫ jR) (by simp only [Category.assoc, G.target_inverse])
  · intro Z a b d wab wbd w₁ w₂
    apply F.map_injective
    apply (cancel_mono jR).mp
    rw [map_comp _ _ w₁ (map_rel _ _ w₁), map_comp _ _ w₂ (map_rel _ _ w₂)]
    simp only [map_comp _ _ wab (map_rel _ _ wab), map_comp _ _ wbd (map_rel _ _ wbd)]
    exact G.assoc (F.obj Z) (F.map a ≫ jR) (F.map b ≫ jR) (F.map d ≫ jR) _ _ _ _

attribute [local implicit_reducible] subgroupoidOfCompatibleMapsAlong

def subgroupoidOfCompatibleMapsAlongHomOver
    {S T : Scheme.{u}} (q : T ⟶ S) [(Over.map q).Faithful]
    (G : Stacks.Groupoids.GroupoidScheme S) (U R : Over T)
    (jU : (Over.map q).obj U ⟶ G.objects) (jR : (Over.map q).obj R ⟶ G.arrows) [Mono jU] [Mono jR]
    (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R)
    (hs : (Over.map q).map s ≫ jU = jR ≫ G.source) (ht : (Over.map q).map t ≫ jU = jR ≫ G.target)
    (he : (Over.map q).map e ≫ jR = jU ≫ G.identity) (hi : (Over.map q).map i ≫ jR = jR ≫ G.inverse)
    (hc : (Over.map q).map c ≫ jR = pullbackComparison (Over.map q) s t ≫
      pullback.map ((Over.map q).map s) ((Over.map q).map t) G.source G.target jR jR jU hs ht ≫
        G.comp) :
    HomOver q
      (subgroupoidOfCompatibleMapsAlong (Over.map q) G U R jU jR s t e i c hs ht he hi hc) G := by
  let F := Over.map q
  refine
    { mapObjects := jU
      mapArrows := jR
      map_source := hs.symm
      map_target := ht.symm
      map_identity := he.symm
      map_comp := ?_ }
  intro Z a b w w'
  change Z ⟶ R at a b
  change a ≫ s = b ≫ t at w
  change F.map (pullback.lift a b w ≫ c) ≫ jR =
    pullback.lift (F.map a ≫ jR) (F.map b ≫ jR) w' ≫ G.comp
  rw [Functor.map_comp, Category.assoc, hc]
  let k := pullbackComparison F s t ≫
    pullback.map (F.map s) (F.map t) G.source G.target jR jR jU hs ht
  change F.map (pullback.lift a b w) ≫ k ≫ G.comp = _
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · have hk : k ≫ pullback.fst G.source G.target = F.map (pullback.fst s t) ≫ jR := by
      simp [k]
    rw [Category.assoc, hk, ← Category.assoc, ← F.map_comp, pullback.lift_fst,
      pullback.lift_fst]
  · have hk : k ≫ pullback.snd G.source G.target = F.map (pullback.snd s t) ≫ jR := by
      simp [k]
    rw [Category.assoc, hk, ← Category.assoc, ← F.map_comp, pullback.lift_snd,
      pullback.lift_snd]

attribute [local implicit_reducible] subgroupoidOfCompatibleMapsAlongHomOver

def rebaseGroupoid {S T : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    (q : T ⟶ S) [Mono q] (f : G.objects.left ⟶ T) (hf : f ≫ q = G.objects.hom) :
    Stacks.Groupoids.GroupoidScheme T := by
  let F := Over.map q
  let : F.Faithful :=
    { map_injective := by
        intro X Y a b h
        apply Over.OverMorphism.ext
        exact congrArg (fun z : F.obj X ⟶ F.obj Y => z.left) h }
  let U : Over T := Over.mk f
  let R : Over T := Over.mk (G.source.left ≫ f)
  let jU : F.obj U ⟶ G.objects := Over.homMk (𝟙 _) (by simpa [F, U] using hf.symm)
  let jR : F.obj R ⟶ G.arrows := Over.homMk (𝟙 _) (by simp [F, R, hf])
  have : Mono jU := by dsimp [jU]; infer_instance
  have : Mono jR := by dsimp [jR]; infer_instance
  let s : R ⟶ U := Over.homMk G.source.left rfl
  let t : R ⟶ U := Over.homMk G.target.left (by
    apply (cancel_mono q).mp
    simp [U, R, Category.assoc, hf])
  let e : U ⟶ R := Over.homMk G.identity.left (by
    have h := congrArg Over.Hom.left G.source_identity
    simpa [U, R, ← Category.assoc] using congrArg (· ≫ f) h)
  let i : R ⟶ R := Over.homMk G.inverse.left (by
    apply (cancel_mono q).mp
    simp [R, Category.assoc, hf])
  have hs : F.map s ≫ jU = jR ≫ G.source := by ext; simp [F, s, jU, jR]
  have ht : F.map t ≫ jU = jR ≫ G.target := by ext; simp [F, t, jU, jR]
  have he : F.map e ≫ jR = jU ≫ G.identity := by ext; simp [F, e, jU, jR]
  have hi : F.map i ≫ jR = jR ≫ G.inverse := by ext; simp [F, i, jR]
  let k := pullbackComparison F s t ≫
    pullback.map (F.map s) (F.map t) G.source G.target jR jR jU hs ht
  let c : pullback s t ⟶ R := Over.homMk (k ≫ G.comp).left (by
    apply (cancel_mono q).mp
    change (k ≫ G.comp).left ≫ (G.source.left ≫ f) ≫ q = _
    simp only [Category.assoc, hf, G.source.w]
    exact (k ≫ G.comp).w)
  exact subgroupoidOfCompatibleMapsAlong F G U R jU jR s t e i c hs ht he hi
    (by ext; simp [F, c, jR, k])

attribute [local implicit_reducible] rebaseGroupoid

def rebaseGroupoidProjection {S T : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    (q : T ⟶ S) [Mono q] (f : G.objects.left ⟶ T) (hf : f ≫ q = G.objects.hom) :
    HomOver q (rebaseGroupoid G q f hf) G := by
  let : (Over.map q).Faithful :=
    { map_injective := by
        intro X Y a b h
        apply Over.OverMorphism.ext
        exact congrArg (fun z : (Over.map q).obj X ⟶ (Over.map q).obj Y => z.left) h }
  unfold rebaseGroupoid
  exact subgroupoidOfCompatibleMapsAlongHomOver ..

attribute [local implicit_reducible] rebaseGroupoidProjection

def liftOverOpenImmersion {S : Scheme.{u}} {U X Y : Over S}
    (j : U ⟶ Y) [IsOpenImmersion j.left] (f : X ⟶ Y)
    (h : Set.range f.left ⊆ Set.range j.left) : X ⟶ U :=
  Over.homMk (IsOpenImmersion.lift j.left f.left h) (by
    rw [← j.w, IsOpenImmersion.lift_fac_assoc, f.w])

attribute [local implicit_reducible] liftOverOpenImmersion

lemma liftOverOpenImmersion_fac {S : Scheme.{u}} {U X Y : Over S}
    (j : U ⟶ Y) [IsOpenImmersion j.left] (f : X ⟶ Y)
    (h : Set.range f.left ⊆ Set.range j.left) :
    liftOverOpenImmersion j f h ≫ j = f :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)

/-- A morphism over `S` commutes with the structure maps on points. -/
private theorem over_hom_left_apply {S : Scheme.{u}} {X Y : Over S} (j : X ⟶ Y) (x : X.left) :
    Y.hom (j.left x) = X.hom x := by
  rw [← Scheme.Hom.comp_apply, Over.w]

lemma range_restrict_over {S : Scheme.{u}} {X Y : Over S}
    (j : X ⟶ Y) (V : S.Opens) :
    Set.range ((X.hom ⁻¹ᵁ V).ι ≫ j.left) =
      Set.range j.left ∩ Y.hom ⁻¹' (V : Set S) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x.1, rfl⟩, by change Y.hom (j.left x.1) ∈ V; rw [over_hom_left_apply]; exact x.2⟩
  · rintro ⟨⟨x, rfl⟩, hx⟩
    exact ⟨⟨x, by simpa [over_hom_left_apply] using hx⟩, rfl⟩

lemma maps_restrictions {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Z) (j : Y ⟶ Z) (V : S.Opens)
    (h : ∀ x : X.left, X.hom x ∈ V → f.left x ∈ Set.range j.left) :
    Set.range ((X.hom ⁻¹ᵁ V).ι ≫ f.left) ⊆
      Set.range ((Y.hom ⁻¹ᵁ V).ι ≫ j.left) := by
  rw [range_restrict_over f V, range_restrict_over j V]
  rintro z ⟨⟨x, rfl⟩, hx⟩
  exact ⟨h x (by simpa [over_hom_left_apply] using hx), hx⟩

def groupoidOfStableOpenPieces
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    (U R : Over S) (jU : U ⟶ G.objects) (jR : R ⟶ G.arrows)
    [IsOpenImmersion jU.left] [IsOpenImmersion jR.left]
    (hs : Set.range (jR ≫ G.source).left ⊆ Set.range jU.left)
    (ht : Set.range (jR ≫ G.target).left ⊆ Set.range jU.left)
    (he : Set.range (jU ≫ G.identity).left ⊆ Set.range jR.left)
    (hi : Set.range (jR ≫ G.inverse).left ⊆ Set.range jR.left)
    (hc : Set.range (pullback.map (jR ≫ G.source) (jR ≫ G.target)
      G.source G.target jR jR (𝟙 _) (by simp) (by simp) ≫ G.comp).left ⊆
      Set.range jR.left) : Stacks.Groupoids.GroupoidScheme S := by
  have : Mono jU := Over.mono_of_mono_left jU
  have : Mono jR := Over.mono_of_mono_left jR
  let s := liftOverOpenImmersion jU (jR ≫ G.source) hs
  let t := liftOverOpenImmersion jU (jR ≫ G.target) ht
  let e := liftOverOpenImmersion jR (jU ≫ G.identity) he
  let i := liftOverOpenImmersion jR (jR ≫ G.inverse) hi
  have hs' : s ≫ jU = jR ≫ G.source := liftOverOpenImmersion_fac _ _ _
  have ht' : t ≫ jU = jR ≫ G.target := liftOverOpenImmersion_fac _ _ _
  let k := pullback.map s t G.source G.target jR jR jU hs' ht'
  let k₀ := pullback.map (jR ≫ G.source) (jR ≫ G.target)
    G.source G.target jR jR (𝟙 _) (by simp) (by simp)
  let a : pullback s t ⟶ pullback (jR ≫ G.source) (jR ≫ G.target) :=
    pullback.map s t (jR ≫ G.source) (jR ≫ G.target) (𝟙 _) (𝟙 _) jU
      (by simpa using hs') (by simpa using ht')
  have hak : a ≫ k₀ = k := by
    apply pullback.hom_ext <;>
      simp [a, k₀, k]
  have hck : Set.range (k ≫ G.comp).left ⊆ Set.range jR.left := by
    rintro z ⟨w, rfl⟩
    apply hc
    refine ⟨a.left w, ?_⟩
    change (a ≫ k₀ ≫ G.comp).left w = (k ≫ G.comp).left w
    rw [← Category.assoc, hak]
  let c := liftOverOpenImmersion jR (k ≫ G.comp) hck
  exact subgroupoidOfCompatibleMaps G U R jU jR s t e i c hs' ht'
    (liftOverOpenImmersion_fac _ _ _) (liftOverOpenImmersion_fac _ _ _)
    (liftOverOpenImmersion_fac _ _ _)

attribute [local implicit_reducible] groupoidOfStableOpenPieces

def groupoidOfStableOpenPiecesHom
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    (U R : Over S) (jU : U ⟶ G.objects) (jR : R ⟶ G.arrows)
    [IsOpenImmersion jU.left] [IsOpenImmersion jR.left]
    (hs : Set.range (jR ≫ G.source).left ⊆ Set.range jU.left)
    (ht : Set.range (jR ≫ G.target).left ⊆ Set.range jU.left)
    (he : Set.range (jU ≫ G.identity).left ⊆ Set.range jR.left)
    (hi : Set.range (jR ≫ G.inverse).left ⊆ Set.range jR.left)
    (hc : Set.range (pullback.map (jR ≫ G.source) (jR ≫ G.target)
      G.source G.target jR jR (𝟙 _) (by simp) (by simp) ≫ G.comp).left ⊆
      Set.range jR.left) : Stacks.Groupoids.GroupoidScheme.Hom
      (groupoidOfStableOpenPieces G U R jU jR hs ht he hi hc) G := by
  have : Mono jU := Over.mono_of_mono_left jU
  have : Mono jR := Over.mono_of_mono_left jR
  unfold groupoidOfStableOpenPieces
  exact subgroupoidOfCompatibleMapsHom ..

attribute [local implicit_reducible] groupoidOfStableOpenPiecesHom

lemma target_mem_orbit_of_source_mem
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) (u : G.objects.left)
    (r : G.arrows.left)
    (hr : G.source.left r ∈ G.target.left '' (G.source.left ⁻¹' {u})) :
    G.target.left r ∈ G.target.left '' (G.source.left ⁻¹' {u}) := by
  obtain ⟨a, ha, har⟩ := hr
  have hp := (IsPullback.of_hasPullback G.source G.target).map (Over.forget S)
  obtain ⟨z, hzr, hza⟩ := Scheme.exists_preimage_of_isPullback hp r a har.symm
  change (pullback.fst G.source G.target).left z = r at hzr
  change (pullback.snd G.source G.target).left z = a at hza
  refine ⟨G.comp.left z, ?_, ?_⟩
  · change G.source.left (G.comp.left z) = u
    have h := congrArg (fun f : pullback G.source G.target ⟶ G.objects => f.left z) G.source_comp
    have hu' : G.source.left ((pullback.snd G.source G.target).left z) = u := by
      rwa [hza]
    simpa only [Over.comp_left, Scheme.Hom.comp_apply, hza] using h.trans hu'
  · have h := congrArg (fun f : pullback G.source G.target ⟶ G.objects => f.left z) G.target_comp
    simpa only [Over.comp_left, Scheme.Hom.comp_apply, hzr] using h

lemma exists_open_stable_pieces
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) (p : S)
    (U R : Over S) (jU : U ⟶ G.objects) (jR : R ⟶ G.arrows)
    [IsOpenImmersion jU.left] [IsOpenImmersion jR.left]
    [IsFinite U.hom] [IsFinite R.hom] [IsSeparated G.objects.hom]
    (hR : ∀ r, G.arrows.hom r = p →
      (r ∈ Set.range jR.left ↔ G.source.left r ∈ Set.range jU.left))
    (hstable : ∀ r, G.arrows.hom r = p →
      G.source.left r ∈ Set.range jU.left → G.target.left r ∈ Set.range jU.left) :
    ∃ V : S.Opens, p ∈ V ∧
      (∀ r : R.left, R.hom r ∈ V →
        G.source.left (jR.left r) ∈ Set.range jU.left ∧
        G.target.left (jR.left r) ∈ Set.range jU.left ∧
        G.inverse.left (jR.left r) ∈ Set.range jR.left) ∧
      (∀ x : U.left, U.hom x ∈ V →
        G.identity.left (jU.left x) ∈ Set.range jR.left) ∧
      (∀ z : (pullback (jR ≫ G.source) (jR ≫ G.target)).left,
        (pullback (jR ≫ G.source) (jR ≫ G.target)).hom z ∈ V →
        (pullback.map (jR ≫ G.source) (jR ≫ G.target) G.source G.target
          jR jR (𝟙 _) (by simp) (by simp) ≫ G.comp).left z ∈ Set.range jR.left) := by
  let D := pullback (jR ≫ G.source) (jR ≫ G.target)
  let k : D ⟶ pullback G.source G.target :=
    pullback.map (jR ≫ G.source) (jR ≫ G.target) G.source G.target
      jR jR (𝟙 _) (by simp) (by simp)
  have hf : IsFinite ((jR ≫ G.target).left ≫ G.objects.hom) := by
    rw [(jR ≫ G.target).w]; infer_instance
  have : IsFinite (jR ≫ G.target).left := IsFinite.of_comp _ G.objects.hom
  have hd := (IsPullback.of_hasPullback (jR ≫ G.source) (jR ≫ G.target)).map (Over.forget S)
  have : IsFinite (pullback.fst (jR ≫ G.source) (jR ≫ G.target)).left := by
    have he : hd.isoPullback.hom ≫ pullback.fst (jR ≫ G.source).left
        (jR ≫ G.target).left = (pullback.fst (jR ≫ G.source) (jR ≫ G.target)).left :=
      hd.isoPullback_hom_fst
    rw [← he]
    infer_instance
  have : IsFinite D.hom := by
    rw [← (pullback.fst (jR ≫ G.source) (jR ≫ G.target)).w]
    infer_instance
  let A : R.left.Opens := (jR ≫ G.source).left ⁻¹ᵁ jU.left.opensRange ⊓
    (jR ≫ G.target).left ⁻¹ᵁ jU.left.opensRange ⊓
    (jR ≫ G.inverse).left ⁻¹ᵁ jR.left.opensRange
  let B : U.left.Opens := (jU ≫ G.identity).left ⁻¹ᵁ jR.left.opensRange
  let C : D.left.Opens := (k ≫ G.comp).left ⁻¹ᵁ jR.left.opensRange
  have ha (r : R.left) (hr : R.hom r = p) : r ∈ A := by
    have hp : G.arrows.hom (jR.left r) = p := by
      rwa [over_hom_left_apply]
    have hs := (hR (jR.left r) hp).mp ⟨r, rfl⟩
    have ht := hstable (jR.left r) hp hs
    change (G.source.left (jR.left r) ∈ Set.range jU.left ∧
      G.target.left (jR.left r) ∈ Set.range jU.left) ∧
      G.inverse.left (jR.left r) ∈ Set.range jR.left
    refine ⟨⟨hs, ht⟩, (hR _ ?_).mpr ?_⟩
    · rwa [over_hom_left_apply]
    · simpa only [← Scheme.Hom.comp_apply, Category.assoc, ← Over.comp_left,
        G.source_inverse] using ht
  have hb (x : U.left) (hx : U.hom x = p) : x ∈ B := by
    change G.identity.left (jU.left x) ∈ Set.range jR.left
    apply (hR _ ?_).mpr
    · have h := congrArg Over.Hom.left G.source_identity
      simpa only [← Scheme.Hom.comp_apply, Category.assoc, ← Over.comp_left,
        G.source_identity, Category.comp_id] using
        (show jU.left x ∈ Set.range jU.left from ⟨x, rfl⟩)
    · rwa [over_hom_left_apply, over_hom_left_apply]
  have hc (z : D.left) (hz : D.hom z = p) : z ∈ C := by
    have hp : G.arrows.hom ((k ≫ G.comp).left z) = p := by
      rwa [over_hom_left_apply]
    apply (hR _ hp).mpr
    have hsource : k ≫ G.comp ≫ G.source =
        pullback.snd (jR ≫ G.source) (jR ≫ G.target) ≫ jR ≫ G.source := by
      simp [k, G.source_comp]
    have h := congrArg (fun f => f.left z) hsource
    change G.source.left ((k ≫ G.comp).left z) ∈ Set.range jU.left
    rw [show G.source.left ((k ≫ G.comp).left z) =
      G.source.left (jR.left ((pullback.snd (jR ≫ G.source) (jR ≫ G.target)).left z)) from h]
    apply (hR _ ?_).mp ⟨_, rfl⟩
    rwa [over_hom_left_apply, over_hom_left_apply]
  obtain ⟨V₁, hp₁, h₁⟩ := exists_open_neighborhood_preimage_le_of_isFinite R.hom p A ha
  obtain ⟨V₂, hp₂, h₂⟩ := exists_open_neighborhood_preimage_le_of_isFinite U.hom p B hb
  obtain ⟨V₃, hp₃, h₃⟩ := exists_open_neighborhood_preimage_le_of_isFinite D.hom p C hc
  refine ⟨V₁ ⊓ V₂ ⊓ V₃, ⟨⟨hp₁, hp₂⟩, hp₃⟩, ?_, ?_, ?_⟩
  · intro r hr
    have h := h₁ hr.1.1
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro x hx
    exact h₂ hx.1.2
  · intro z hz
    exact h₃ hz.2

def restrictStablePieces
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    (U R : Over S) (jU : U ⟶ G.objects) (jR : R ⟶ G.arrows)
    [IsOpenImmersion jU.left] [IsOpenImmersion jR.left]
    (V : S.Opens)
    (hR : ∀ r : R.left, R.hom r ∈ V →
      G.source.left (jR.left r) ∈ Set.range jU.left ∧
      G.target.left (jR.left r) ∈ Set.range jU.left ∧
      G.inverse.left (jR.left r) ∈ Set.range jR.left)
    (hU : ∀ x : U.left, U.hom x ∈ V →
      G.identity.left (jU.left x) ∈ Set.range jR.left)
    (hC : ∀ z : (pullback (jR ≫ G.source) (jR ≫ G.target)).left,
      (pullback (jR ≫ G.source) (jR ≫ G.target)).hom z ∈ V →
      (pullback.map (jR ≫ G.source) (jR ≫ G.target) G.source G.target
        jR jR (𝟙 _) (by simp) (by simp) ≫ G.comp).left z ∈ Set.range jR.left) :
    Stacks.Groupoids.GroupoidScheme S := by
  let U' : Over S := Over.mk ((U.hom ⁻¹ᵁ V).ι ≫ U.hom)
  let R' : Over S := Over.mk ((R.hom ⁻¹ᵁ V).ι ≫ R.hom)
  let aU : U' ⟶ U := Over.homMk (U.hom ⁻¹ᵁ V).ι rfl
  let aR : R' ⟶ R := Over.homMk (R.hom ⁻¹ᵁ V).ι rfl
  let jU' := aU ≫ jU
  let jR' := aR ≫ jR
  have : IsOpenImmersion jU'.left := by
    change IsOpenImmersion ((U.hom ⁻¹ᵁ V).ι ≫ jU.left)
    infer_instance
  have : IsOpenImmersion jR'.left := by
    change IsOpenImmersion ((R.hom ⁻¹ᵁ V).ι ≫ jR.left)
    infer_instance
  have hs : Set.range (jR' ≫ G.source).left ⊆ Set.range jU'.left :=
    maps_restrictions (jR ≫ G.source) jU V (fun r hr => (hR r hr).1)
  have ht : Set.range (jR' ≫ G.target).left ⊆ Set.range jU'.left :=
    maps_restrictions (jR ≫ G.target) jU V (fun r hr => (hR r hr).2.1)
  have he : Set.range (jU' ≫ G.identity).left ⊆ Set.range jR'.left :=
    maps_restrictions (jU ≫ G.identity) jR V hU
  have hi : Set.range (jR' ≫ G.inverse).left ⊆ Set.range jR'.left :=
    maps_restrictions (jR ≫ G.inverse) jR V (fun r hr => (hR r hr).2.2)
  let D' := pullback (jR' ≫ G.source) (jR' ≫ G.target)
  let D := pullback (jR ≫ G.source) (jR ≫ G.target)
  let a : D' ⟶ D := pullback.map (jR' ≫ G.source) (jR' ≫ G.target)
    (jR ≫ G.source) (jR ≫ G.target) aR aR (𝟙 _) (by simp [jR']) (by simp [jR'])
  let k' := pullback.map (jR' ≫ G.source) (jR' ≫ G.target) G.source G.target
    jR' jR' (𝟙 _) (by simp) (by simp)
  let k := pullback.map (jR ≫ G.source) (jR ≫ G.target) G.source G.target
    jR jR (𝟙 _) (by simp) (by simp)
  have hak : a ≫ k = k' := by
    apply pullback.hom_ext <;>
      simp [a, k, k', jR']
  have hc : Set.range (k' ≫ G.comp).left ⊆ Set.range jR'.left := by
    rintro z ⟨w, rfl⟩
    change (k' ≫ G.comp).left w ∈ Set.range ((R.hom ⁻¹ᵁ V).ι ≫ jR.left)
    rw [range_restrict_over]
    have hw : D'.hom w ∈ V := by
      rw [← (pullback.fst (jR' ≫ G.source) (jR' ≫ G.target)).w,
        Scheme.Hom.comp_apply]
      exact ((pullback.fst (jR' ≫ G.source) (jR' ≫ G.target)).left w).2
    have haw : D.hom (a.left w) ∈ V := by
      simpa only [← Scheme.Hom.comp_apply, a.w] using hw
    refine ⟨?_, ?_⟩
    · have h := hC (a.left w) haw
      change (a ≫ k ≫ G.comp).left w ∈ Set.range jR.left at h
      rwa [← Category.assoc, hak] at h
    · change G.arrows.hom ((k' ≫ G.comp).left w) ∈ V
      simpa only [← Scheme.Hom.comp_apply, (k' ≫ G.comp).w] using hw
  exact groupoidOfStableOpenPieces G U' R' jU' jR' hs ht he hi hc

attribute [local implicit_reducible] restrictStablePieces

def restrictStablePiecesHom
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    (U R : Over S) (jU : U ⟶ G.objects) (jR : R ⟶ G.arrows)
    [IsOpenImmersion jU.left] [IsOpenImmersion jR.left]
    (V : S.Opens)
    (hR : ∀ r : R.left, R.hom r ∈ V →
      G.source.left (jR.left r) ∈ Set.range jU.left ∧
      G.target.left (jR.left r) ∈ Set.range jU.left ∧
      G.inverse.left (jR.left r) ∈ Set.range jR.left)
    (hU : ∀ x : U.left, U.hom x ∈ V →
      G.identity.left (jU.left x) ∈ Set.range jR.left)
    (hC : ∀ z : (pullback (jR ≫ G.source) (jR ≫ G.target)).left,
      (pullback (jR ≫ G.source) (jR ≫ G.target)).hom z ∈ V →
      (pullback.map (jR ≫ G.source) (jR ≫ G.target) G.source G.target
        jR jR (𝟙 _) (by simp) (by simp) ≫ G.comp).left z ∈ Set.range jR.left) :
    Stacks.Groupoids.GroupoidScheme.Hom
      (restrictStablePieces G U R jU jR V hR hU hC) G := by
  have : IsOpenImmersion
      ((Over.homMk (U.hom ⁻¹ᵁ V).ι rfl : Over.mk ((U.hom ⁻¹ᵁ V).ι ≫ U.hom) ⟶ U) ≫ jU).left := by
    change IsOpenImmersion ((U.hom ⁻¹ᵁ V).ι ≫ jU.left)
    infer_instance
  have : IsOpenImmersion
      ((Over.homMk (R.hom ⁻¹ᵁ V).ι rfl : Over.mk ((R.hom ⁻¹ᵁ V).ι ≫ R.hom) ⟶ R) ≫ jR).left := by
    change IsOpenImmersion ((R.hom ⁻¹ᵁ V).ι ≫ jR.left)
    infer_instance
  unfold restrictStablePieces
  exact groupoidOfStableOpenPiecesHom ..

attribute [local implicit_reducible] restrictStablePiecesHom

end AlgebraicGeometry.GroupoidScheme
