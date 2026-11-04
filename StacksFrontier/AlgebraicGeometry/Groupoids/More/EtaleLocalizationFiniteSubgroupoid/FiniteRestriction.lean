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
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.EtaleLocalizationFiniteSubgroupoid.FiniteSubgroupoid

/-!
# The finite subgroupoid as a full restriction

When the relation morphism of the groupoid is universally closed, the elementary étale
neighbourhood of `AlgebraicGeometry.GroupoidScheme.exists_finite_openClosed_subgroupoid`
can be shrunk so that the finite open-and-closed subgroupoid is moreover the restriction
of the base-changed groupoid to its object scheme.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_finite_openClosed_restriction`: when the
  relation morphism is universally closed, the neighbourhood can be shrunk so that the
  finite subgroupoid is moreover the restriction of the base-changed groupoid to it.

## Implementation notes

Part (h) of Tag 03X5 is expressed by the universal property of the restricted arrow
scheme: every arrow of the base-changed groupoid whose source and target factor through
the chosen object scheme factors uniquely through its arrow scheme.  Quantifying over
arbitrary test schemes records the full scheme-theoretic restriction, not merely an
equality of underlying point sets.

## References

* [Stacks Project, Tag 03FL](https://stacks.math.columbia.edu/tag/03FL)
* [Stacks Project, Tag 03X5](https://stacks.math.columbia.edu/tag/03X5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidScheme

private lemma existsUnique_openImmersion_lift {X Y Z : Scheme.{u}}
    (i : X ⟶ Y) [IsOpenImmersion i] (f : Z ⟶ Y)
    (h : Set.range f ⊆ Set.range i) :
    ∃! g : Z ⟶ X, g ≫ i = f :=
  ⟨IsOpenImmersion.lift i f h, IsOpenImmersion.lift_fac i f h,
    fun g hg => IsOpenImmersion.lift_uniq i f h g hg⟩

private lemma disjoint_ranges_of_coprod_iso {X Y Z : Scheme.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso (coprod.desc f g)] :
    Disjoint (Set.range f) (Set.range g) := by
  rw [Set.disjoint_left]
  intro z hzf hzg
  rcases hzf with ⟨x, rfl⟩
  rcases hzg with ⟨y, h⟩
  have hh : (coprod.desc f g) ((coprod.inl : X ⟶ X ⨿ Y) x) =
      (coprod.desc f g) ((coprod.inr : Y ⟶ X ⨿ Y) y) := by
    simpa only [← Scheme.Hom.comp_apply, coprod.inl_desc, coprod.inr_desc] using h.symm
  have hxy := (asIso (coprod.desc f g)).hom.homeomorph.injective hh
  exact (AlgebraicGeometry.inl_ne_inr (X := X) (Y := Y) x y) hxy

private lemma no_extra_arrows_over_special_fiber
    {S : Scheme.{u}} (U R A B : Over S) (s t : R ⟶ U) (p : S)
    {W' : Over S} (jU : A ⟶ U)
    (jR : B ⟶ R) (jW' : W' ⟶ R)
    [IsIso (coprod.desc jR.left jW'.left)]
    (hfiber : jR.left '' {r : B.left | B.hom r = p} =
      s.left ⁻¹' (jU.left '' {x : A.left | A.hom x = p}))
    (z : (A ⨯ A).left) (r : R.left)
    (hz : (A ⨯ A).hom z = p)
    (hrel : (prod.lift t s).left r = (prod.map jU jU).left z) :
    r ∉ Set.range jW'.left := by
  have hsrcPt : A.hom ((prod.snd : A ⨯ A ⟶ A).left z) = p :=
    (congrArg (fun f : (A ⨯ A).left ⟶ S => f z) (prod.snd : A ⨯ A ⟶ A).w).trans hz
  have hsrc : s.left r =
      jU.left ((prod.snd : A ⨯ A ⟶ A).left z) := by
    have h := congrArg (fun x => (prod.snd : U ⨯ U ⟶ U).left x) hrel
    change ((prod.lift t s ≫ prod.snd).left) r =
      ((prod.map jU jU ≫ prod.snd).left) z at h
    rw [prod.lift_snd, prod.map_snd] at h
    exact h
  have hpre : s.left r ∈ jU.left '' {x : A.left | A.hom x = p} :=
    ⟨(prod.snd : A ⨯ A ⟶ A).left z, hsrcPt, hsrc.symm⟩
  have hrR : r ∈ jR.left '' {a : B.left | B.hom a = p} := by
    rwa [hfiber]
  rcases hrR with ⟨a, ha, har⟩
  intro hrW
  rcases hrW with ⟨b, hb⟩
  have hdisj := disjoint_ranges_of_coprod_iso jR.left jW'.left
  exact (Set.disjoint_left.mp hdisj ⟨a, har⟩ ⟨b, hb⟩)

private lemma point_mem_range_coprod_desc {A B X : Scheme.{u}}
    (f : A ⟶ X) (g : B ⟶ X) [IsIso (coprod.desc f g)] (x : X) :
    x ∈ Set.range f ∨ x ∈ Set.range g := by
  obtain ⟨z, rfl⟩ := (coprod.desc f g).homeomorph.surjective x
  obtain ⟨a | b, rfl⟩ := (AlgebraicGeometry.coprodMk A B).surjective z
  · left
    refine ⟨a, ?_⟩
    simp only [Scheme.Hom.homeomorph_apply, AlgebraicGeometry.coprodMk_inl]
    exact (congrArg (fun k : A ⟶ X => k a) (coprod.inl_desc f g)).symm
  · right
    refine ⟨b, ?_⟩
    simp only [Scheme.Hom.homeomorph_apply, AlgebraicGeometry.coprodMk_inr]
    exact (congrArg (fun k : B ⟶ X => k b) (coprod.inr_desc f g)).symm

private lemma exists_open_neighborhood_avoiding_extra_relation_arrows
    {S : Scheme.{u}} (U R A : Over S) (s t : R ⟶ U) (p : S)
    {W' : Over S} (jU : A ⟶ U) (jW' : W' ⟶ R)
    [IsFinite A.hom]
    [UniversallyClosed (prod.lift t s).left]
    [IsClosedImmersion jW'.left]
    (hspecial : ∀ (z : (A ⨯ A).left) (r : R.left),
      (A ⨯ A).hom z = p →
      (prod.lift t s).left r =
        (prod.map jU jU).left z → r ∉ Set.range jW'.left) :
    ∃ Q : S.Opens, p ∈ Q.1 ∧
      ∀ (z : (A ⨯ A).left) (r : R.left),
        (A ⨯ A).hom z ∈ Q.1 →
        (prod.lift t s).left r = (prod.map jU jU).left z →
        r ∉ Set.range jW'.left := by
  let ρ := (prod.lift t s).left
  let ι := (prod.map jU jU).left
  let π := (A ⨯ A).hom
  let C : Set (A ⨯ A).left :=
    ι ⁻¹' (ρ '' Set.range jW'.left)
  have hclosedC : IsClosed C :=
    (ρ.isClosedMap _ (IsClosedImmersion.isClosedEmbedding jW'.left).isClosed_range).preimage
      ι.continuous
  have hproj : IsFinite (prod.fst : A ⨯ A ⟶ A).left := by
    let e := Over.prodLeftIsoPullback A A
    have h : IsFinite (e.hom ≫
        pullback.fst A.hom A.hom) := by
      infer_instance
    rw [Over.prodLeftIsoPullback_hom_fst] at h
    exact h
  let : IsFinite (prod.fst : A ⨯ A ⟶ A).left := hproj
  have hπ : IsFinite π := by
    show IsFinite (A ⨯ A).hom
    rw [← (prod.fst : A ⨯ A ⟶ A).w]
    infer_instance
  let : IsFinite π := hπ
  have hp : p ∉ π '' C := by
    rintro ⟨z, hzC, hz⟩
    rcases (Set.mem_preimage.mp hzC) with hrelmem
    rcases (Set.mem_image ρ (Set.range jW'.left) (ι z)).mp hrelmem with
      ⟨r, hr, hrel⟩
    exact (hspecial z r hz (by simpa [ρ, ι] using hrel)) hr
  refine ⟨⟨(π '' C)ᶜ, isOpen_compl_iff.mpr (π.isClosedMap _ hclosedC)⟩, hp, ?_⟩
  intro z r hzQ hrel hr
  exact hzQ ⟨z, ⟨r, hr, by simpa [ρ, ι] using hrel⟩, rfl⟩

private lemma avoids_complement_of_relation
    {S : Scheme.{u}} (U R A W : Over S) (s t : R ⟶ U)
    (i : A ⟶ U) (j : W ⟶ R) (Q : S.Opens)
    (h : ∀ (z : (A ⨯ A).left) (r : R.left),
      (A ⨯ A).hom z ∈ Q.1 →
      (prod.lift t s).left r = (prod.map i i).left z →
      r ∉ Set.range j.left)
    {T : Scheme.{u}} (f : T ⟶ R.left) (x y : T ⟶ A.left)
    (hs : f ≫ s.left = x ≫ i.left) (ht : f ≫ t.left = y ≫ i.left)
    (hQ : ∀ z : T, (f ≫ R.hom) z ∈ Q.1) :
    ∀ z : T, f z ∉ Set.range j.left := by
  let V : Over S := Over.mk (f ≫ R.hom)
  let fO : V ⟶ R := Over.homMk f
  let xO : V ⟶ A := Over.homMk x (by
    rw [← i.w, ← Category.assoc, ← hs, Category.assoc, s.w]; rfl)
  let yO : V ⟶ A := Over.homMk y (by
    rw [← i.w, ← Category.assoc, ← ht, Category.assoc, t.w]; rfl)
  let zO : V ⟶ A ⨯ A := prod.lift yO xO
  have hrel : fO ≫ prod.lift t s = zO ≫ prod.map i i := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, prod.map_fst,
        zO, prod.lift_fst_assoc]
      apply (Over.forget S).map_injective
      exact ht
    · simp only [Category.assoc, prod.lift_snd, prod.map_snd,
        zO, prod.lift_snd_assoc]
      apply (Over.forget S).map_injective
      exact hs
  intro z
  apply h (zO.left z) (f z)
  · have hz := congrArg (fun k => k z) zO.w
    change (A ⨯ A).hom (zO.left z) = (f ≫ R.hom) z at hz
    rw [hz]
    exact hQ z
  · exact congrArg (fun k => k.left z) hrel

/-- The étale neighbourhood `N` restricted to an open subscheme containing its
distinguished point, in a reducible form whose structure morphism is `Q.ι ≫ N.toBase`. -/
private abbrev restrictNeighborhood {S : Scheme.{u}} {s : S}
    (N : AlgebraicGeometry.EtaleNeighborhood S s) (Q : N.scheme.Opens)
    (hQ : N.point ∈ Q.1) : AlgebraicGeometry.EtaleNeighborhood S s where
  scheme := (↑Q : Scheme)
  point := ⟨N.point, hQ⟩
  toBase := Q.ι ≫ N.toBase
  etale_toBase := by infer_instance
  map_point := by
    change N.toBase N.point = s
    exact N.map_point

private lemma range_fst_of_isPullback {P X Y Z : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) : Set.range a = f ⁻¹' Set.range g := by
  rw [← h.isoPullback_hom_fst]
  show Set.range ((pullback.fst f g) ∘ h.isoPullback.hom) = _
  have hs : Function.Surjective h.isoPullback.hom :=
    h.isoPullback.hom.homeomorph.surjective
  rw [Set.range_comp, hs.range_eq, Set.image_univ, Scheme.Pullback.range_fst]

private def baseChangeProjection {X S T V : Scheme.{u}}
    (x : X ⟶ S) (f : T ⟶ S) (q : V ⟶ T) :
    pullback x (q ≫ f) ⟶ pullback x f :=
  pullback.lift (pullback.fst x (q ≫ f)) (pullback.snd x (q ≫ f) ≫ q)
    (by simpa only [Category.assoc] using pullback.condition (f := x) (g := q ≫ f))

private lemma baseChangeProjection_isPullback {X S T V : Scheme.{u}}
    (x : X ⟶ S) (f : T ⟶ S) (q : V ⟶ T) :
    IsPullback (baseChangeProjection x f q) (pullback.snd x (q ≫ f))
      (pullback.snd x f) q := by
  apply IsPullback.mk' (by simp [baseChangeProjection, pullback.lift_snd])
  · intro Z a b h₁ h₂
    apply pullback.hom_ext
    · have hh := congrArg (fun k => k ≫ pullback.fst x f) h₁
      simpa only [Category.assoc, baseChangeProjection, pullback.lift_fst] using hh
    · exact h₂
  · intro Z a b h
    let l := pullback.lift (a ≫ pullback.fst x f) b (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, h, Category.assoc])
    refine ⟨l, ?_, pullback.lift_snd _ _ _⟩
    apply pullback.hom_ext
    · simp [l, baseChangeProjection, Category.assoc, pullback.lift_fst]
    · simp [l, baseChangeProjection, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, h]

private def baseChangeInclusion {A A' X X' S T : Scheme.{u}}
    {a : A ⟶ S} {a' : A' ⟶ T} {q : A' ⟶ A} {f : T ⟶ S}
    (hq : IsPullback q a' a f) {x : X ⟶ S} {x' : X' ⟶ T} {qX : X' ⟶ X}
    (hX : IsPullback qX x' x f) (i : A ⟶ X) (hi : i ≫ x = a) : A' ⟶ X' :=
  hX.lift (q ≫ i) a' (by rw [Category.assoc, hi, hq.w])

private lemma baseChangeInclusion_isPullback {A A' X X' S T : Scheme.{u}}
    {a : A ⟶ S} {a' : A' ⟶ T} {q : A' ⟶ A} {f : T ⟶ S}
    (hq : IsPullback q a' a f) {x : X ⟶ S} {x' : X' ⟶ T} {qX : X' ⟶ X}
    (hX : IsPullback qX x' x f) (i : A ⟶ X) (hi : i ≫ x = a) :
    IsPullback q (baseChangeInclusion hq hX i hi) i qX := by
  let j := baseChangeInclusion hq hX i hi
  have hj : j ≫ x' = a' := hX.lift_snd _ _ _
  have houter : IsPullback q (j ≫ x') (i ≫ x) f := by
    rw [hi, hj]
    exact hq
  exact houter.of_bot (hX.lift_fst _ _ _).symm hX

private lemma coprod_isIso_of_isPullbacks
    {A B X A' B' X' : Scheme.{u}}
    (i : A ⟶ X) (j : B ⟶ X) [IsIso (coprod.desc i j)]
    (i' : A' ⟶ X') (j' : B' ⟶ X') (a : A' ⟶ A) (b : B' ⟶ B) (q : X' ⟶ X)
    (ha : IsPullback a i' i q) (hb : IsPullback b j' j q) :
    IsIso (coprod.desc i' j') := by
  let F := pair A B
  let F' := pair A' B'
  let α : F' ⟶ F := Discrete.natTrans fun k => by
    cases k with | mk k => cases k with
    | left => exact a
    | right => exact b
  let c : BinaryCofan A B := BinaryCofan.mk i j
  let c' : BinaryCofan A' B' := BinaryCofan.mk i' j'
  have hc : IsColimit c := by
    have : IsIso ((coprodIsCoprod A B).desc c) :=
      (inferInstance : IsIso (coprod.desc i j))
    exact (IsColimit.ofPointIso (coprodIsCoprod A B))
  have h : α ≫ c.ι = c'.ι ≫ (Functor.const (Discrete WalkingPair)).map q := by
    ext k
    cases k with | mk k => cases k with
    | left => exact ha.w
    | right => exact hb.w
  have hc' : IsColimit c' := Classical.choice
    ((FinitaryExtensive.vanKampen c hc).isUniversal c' α q h
      (NatTrans.Equifibered.of_discrete α) fun k => by
        cases k with | mk k => cases k with
        | left => exact ha.flip
        | right => exact hb.flip)
  exact (IsColimit.coconePointUniqueUpToIso (coprodIsCoprod A' B') hc').isIso_hom

private lemma homOver_composition {S T : Scheme.{u}} {f : T ⟶ S}
    {G : Stacks.Groupoids.GroupoidScheme S} {H : Stacks.Groupoids.GroupoidScheme T}
    (F : HomOver f H G) :
    ∃ k : (pullback H.source H.target).left ⟶ (pullback G.source G.target).left,
      k ≫ (pullback.fst G.source G.target).left =
        (pullback.fst H.source H.target).left ≫ F.mapArrows.left ∧
      k ≫ (pullback.snd G.source G.target).left =
        (pullback.snd H.source H.target).left ≫ F.mapArrows.left ∧
      H.comp.left ≫ F.mapArrows.left = k ≫ G.comp.left := by
  let a := (Over.map f).map (pullback.fst H.source H.target) ≫ F.mapArrows
  let b := (Over.map f).map (pullback.snd H.source H.target) ≫ F.mapArrows
  have w : a ≫ G.source = b ≫ G.target := by
    dsimp [a, b]
    simp only [Category.assoc, F.map_source, F.map_target]
    simp only [← Category.assoc, ← Functor.map_comp, pullback.condition]
  let k := pullback.lift a b w
  refine ⟨k.left, ?_, ?_, ?_⟩
  · exact congrArg (fun g => g.left) (pullback.lift_fst a b w)
  · exact congrArg (fun g => g.left) (pullback.lift_snd a b w)
  · have hc := F.map_comp (pullback H.source H.target)
      (pullback.fst H.source H.target) (pullback.snd H.source H.target)
      pullback.condition w
    have hid : pullback.lift (pullback.fst H.source H.target)
        (pullback.snd H.source H.target) pullback.condition = 𝟙 _ := by
      ext <;> simp
    simp only [Stacks.Groupoids.GroupoidScheme.compose, hid, Category.id_comp] at hc
    exact congrArg (fun g => g.left) hc

private lemma universallyClosed_baseChange_relation {S T : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (f : T ⟶ S)
    [UniversallyClosed (prod.lift G.target G.source).left] :
    UniversallyClosed (prod.lift ((Over.pullback f).map G.target)
      ((Over.pullback f).map G.source)).left := by
  let F := Over.pullback f
  have h : UniversallyClosed (F.map (prod.lift G.target G.source)).left :=
    MorphismProperty.overPullbackMap f (prod.lift G.target G.source) inferInstance
  have heq : prod.lift (F.map G.target) (F.map G.source) =
      F.map (prod.lift G.target G.source) ≫ prodComparison F G.objects G.objects := by
    apply prod.hom_ext <;> simp [Category.assoc, prodComparison_fst,
      prodComparison_snd, ← F.map_comp]
  let : UniversallyClosed (F.map (prod.lift G.target G.source)).left := h
  rw [heq]
  show UniversallyClosed ((F.map (prod.lift G.target G.source)).left ≫
    (prodComparison F G.objects G.objects).left)
  have : IsIso (prodComparison F G.objects G.objects).left :=
    (inferInstance : IsIso ((Over.forget T).map (prodComparison F G.objects G.objects)))
  exact inferInstance

private lemma image_fiber_baseChange {A A' X X' S T : Scheme.{u}}
    (i : A ⟶ X) (i' : A' ⟶ X') (a : A' ⟶ A) (q : X' ⟶ X)
    (h : IsPullback a i' i q) (x : X ⟶ S) (x' : X' ⟶ T) (f : T ⟶ S)
    (hbase : q ≫ x = x' ≫ f) (hf : Function.Injective f) (p : T) :
    i' '' {z | (i' ≫ x') z = p} = q ⁻¹' (i '' {z | (i ≫ x) z = f p}) := by
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    change x' (i' v) = p at hv
    refine ⟨a v, ?_, ?_⟩
    · have hw := congrArg (fun k : A' ⟶ S => k v)
        (show a ≫ i ≫ x = i' ≫ x' ≫ f by rw [← hbase, ← Category.assoc, h.w, Category.assoc])
      show x (i (a v)) = f p
      simpa only [Scheme.Hom.comp_apply, hv] using hw
    · exact congrArg (fun k : A' ⟶ X => k v) h.w
  · rintro ⟨v, hv, hvi⟩
    have hz : z ∈ Set.range i' := by
      rw [range_fst_of_isPullback h.flip]
      exact ⟨v, hvi⟩
    obtain ⟨v', rfl⟩ := hz
    refine ⟨v', ?_, rfl⟩
    apply hf
    have hb := congrArg (fun k : X' ⟶ S => k (i' v')) hbase
    show f (x' (i' v')) = f p
    change x (q (i' v')) = f (x' (i' v')) at hb
    rw [← hb, ← hvi]
    exact hv

private lemma lift_point_of_open_baseChange {A A' S T : Scheme.{u}}
    (a : A' ⟶ A) (b : A' ⟶ T) (c : A ⟶ S) (f : T ⟶ S)
    (h : IsPullback a b c f) [IsOpenImmersion f]
    (x : A) (p : T) (hx : c x = f p) :
    ∃ x' : A', a x' = x ∧ b x' = p := by
  have hx' : x ∈ Set.range a := by
    rw [range_fst_of_isPullback h]
    exact ⟨p, hx.symm⟩
  obtain ⟨x', rfl⟩ := hx'
  refine ⟨x', rfl, f.isOpenEmbedding.injective ?_⟩
  exact (congrArg (fun k : A' ⟶ S => k x') h.w).symm.trans hx

private lemma preimage_orbit_of_lift {R R' U U' : Type*}
    (s t : R → U) (s' t' : R' → U') (r : R' → R) (q : U' → U)
    (hs : ∀ z, s (r z) = q (s' z)) (ht : ∀ z, t (r z) = q (t' z))
    (hq : Function.Injective q) (u : U')
    (hlift : ∀ z, s z = q u → z ∈ Set.range r) :
    q ⁻¹' (t '' (s ⁻¹' {q u})) = t' '' (s' ⁻¹' {u}) := by
  ext x
  constructor
  · rintro ⟨z, hz, hx⟩
    obtain ⟨z', rfl⟩ := hlift z hz
    refine ⟨z', hq ?_, hq ?_⟩
    · exact (hs z').symm.trans hz
    · exact (ht z').symm.trans hx
  · rintro ⟨z, hz, rfl⟩
    exact ⟨r z, (hs z).trans (congrArg q hz), ht z⟩

/-- The finite open-and-closed subgroupoid around a quasi-finite point can be chosen as the
full restriction when the relation morphism is universally closed. -/
@[stacks 03X5]
public theorem exists_finite_openClosed_restriction
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) (p : S)
    (u : G.objects.left) (hu : G.objects.hom u = p)
    [LocallyOfFiniteType G.objects.hom]
    (hqu : AlgebraicGeometry.quasiFiniteAt G.objects.hom u)
    [IsSeparated G.objects.hom] [IsSeparated G.arrows.hom]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
    [Flat G.target.left] [LocallyOfFinitePresentation G.target.left]
    (hfinite : Set.Finite (G.source.left ⁻¹' {u}))
    [UniversallyClosed (prod.lift G.target G.source).left] :
    ∃ (N : AlgebraicGeometry.EtaleNeighborhood S p), N.IsElementary ∧
      ∃ (H : Stacks.Groupoids.GroupoidScheme N.scheme) (W W' : Scheme.{u})
        (jU : H.objects.left ⟶ pullback G.objects.hom N.toBase)
        (jW : W ⟶ pullback G.objects.hom N.toBase)
        (jR : H.arrows.left ⟶ pullback G.arrows.hom N.toBase)
        (jW' : W' ⟶ pullback G.arrows.hom N.toBase),
        IsOpenImmersion jU ∧ IsClosedImmersion jU ∧
        IsOpenImmersion jW ∧ IsClosedImmersion jW ∧
        IsIso (coprod.desc jU jW) ∧
        IsOpenImmersion jR ∧ IsClosedImmersion jR ∧
        IsOpenImmersion jW' ∧ IsClosedImmersion jW' ∧
        IsIso (coprod.desc jR jW') ∧
        H.objects.hom = jU ≫ pullback.snd G.objects.hom N.toBase ∧
        H.arrows.hom = jR ≫ pullback.snd G.arrows.hom N.toBase ∧
        (∃ u' : H.objects.left,
          (jU ≫ pullback.fst G.objects.hom N.toBase) u' = u ∧
          jU '' {x : H.objects.left | H.objects.hom x = N.point} =
            (pullback.map G.arrows.hom N.toBase G.objects.hom N.toBase
              G.target.left (𝟙 _) (𝟙 _) (by simp) (by simp)) ''
              ((pullback.map G.arrows.hom N.toBase G.objects.hom N.toBase
                G.source.left (𝟙 _) (𝟙 _) (by simp) (by simp)) ⁻¹' {jU u'}) ∧
          jR '' {r : H.arrows.left | H.arrows.hom r = N.point} =
            (pullback.map G.arrows.hom N.toBase G.objects.hom N.toBase
              G.source.left (𝟙 _) (𝟙 _) (by simp) (by simp)) ⁻¹'
                (jU '' {x : H.objects.left | H.objects.hom x = N.point})) ∧
        IsFinite H.objects.hom ∧ IsFinite H.arrows.hom ∧
        H.source.left ≫ jU ≫ pullback.fst G.objects.hom N.toBase =
          jR ≫ pullback.fst G.arrows.hom N.toBase ≫ G.source.left ∧
        H.target.left ≫ jU ≫ pullback.fst G.objects.hom N.toBase =
          jR ≫ pullback.fst G.arrows.hom N.toBase ≫ G.target.left ∧
        (∃ k : (pullback H.source H.target).left ⟶
            (pullback G.source G.target).left,
          k ≫ (pullback.fst G.source G.target).left =
              (pullback.fst H.source H.target).left ≫ jR ≫
                pullback.fst G.arrows.hom N.toBase ∧
          k ≫ (pullback.snd G.source G.target).left =
              (pullback.snd H.source H.target).left ≫ jR ≫
                pullback.fst G.arrows.hom N.toBase ∧
          H.comp.left ≫ jR ≫ pullback.fst G.arrows.hom N.toBase =
            k ≫ G.comp.left) ∧
        (∀ (T : Scheme.{u})
          (f : T ⟶ pullback G.arrows.hom N.toBase)
          (x y : T ⟶ H.objects.left),
          (f ≫ pullback.map G.arrows.hom N.toBase G.objects.hom N.toBase
              G.source.left (𝟙 _) (𝟙 _) (by simp) (by simp) = x ≫ jU) →
          (f ≫ pullback.map G.arrows.hom N.toBase G.objects.hom N.toBase
              G.target.left (𝟙 _) (𝟙 _) (by simp) (by simp) = y ≫ jU) →
          (∃! g : T ⟶ H.arrows.left,
            g ≫ jR = f ∧ g ≫ H.source.left = x ∧ g ≫ H.target.left = y)) := by
  obtain ⟨N, hN, H, W, W', jU, jW, jR, jW', h1, h2, h3, h4, h5, h6, h7,
      h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ :=
    exists_finite_openClosed_subgroupoid G p u hu hqu hfinite
  let := h1
  let := h2
  let := h3
  let := h4
  let := h5
  let := h6
  let := h7
  let := h8
  let := h9
  let := h10
  let := h14
  let := h15
  let F := Over.pullback N.toBase
  let U := F.obj G.objects
  let R := F.obj G.arrows
  let s := F.map G.source
  let t := F.map G.target
  let i : H.objects ⟶ U := Over.homMk jU h11.symm
  let j : H.arrows ⟶ R := Over.homMk jR h12.symm
  let w : Over N.scheme := Over.mk (jW' ≫ pullback.snd G.arrows.hom N.toBase)
  let iw : w ⟶ R := Over.homMk jW'
  let : IsClosedImmersion iw.left := h9
  let : IsIso (coprod.desc j.left iw.left) := h10
  have huc : UniversallyClosed (prod.lift t s).left :=
    universallyClosed_baseChange_relation G N.toBase
  let := huc
  obtain ⟨u', hu', huf, hrf⟩ := h13
  have hrf' : j.left '' {r | H.arrows.hom r = N.point} =
      s.left ⁻¹' (i.left '' {x | H.objects.hom x = N.point}) := hrf
  obtain ⟨Q, hpQ, havoid⟩ := exists_open_neighborhood_avoiding_extra_relation_arrows
    U R H.objects s t N.point i iw
    (no_extra_arrows_over_special_fiber U R H.objects H.arrows s t N.point
      i j iw hrf')
  have h11b : H.objects.hom = jU ≫ U.hom := h11
  have h12b : H.arrows.hom = jR ≫ R.hom := h12
  have hcomm : ∀ (e : H.arrows ⟶ H.objects) (g : G.arrows ⟶ G.objects),
      e.left ≫ jU ≫ pullback.fst G.objects.hom N.toBase =
        jR ≫ pullback.fst G.arrows.hom N.toBase ≫ g.left →
      e.left ≫ jU = jR ≫ (F.map g).left := by
    intro e g h
    apply pullback.hom_ext
    · simpa only [Category.assoc, F, Over.pullback_map_left, pullback.lift_fst] using h
    · change (e.left ≫ jU) ≫ U.hom = (jR ≫ (F.map g).left) ≫ U.hom
      rw [Category.assoc, ← h11b, Category.assoc, (F.map g).w, ← h12b, e.w]
  have hsrc : H.source.left ≫ jU = jR ≫ s.left := hcomm H.source G.source h16
  have htgt : H.target.left ≫ jU = jR ≫ t.left := hcomm H.target G.target h17
  have hu'p : H.objects.hom u' = N.point := by
    have hid : ∀ (e : H.arrows ⟶ H.objects) (e' : R ⟶ U), H.identity ≫ e = 𝟙 _ →
        e.left ≫ jU = jR ≫ e'.left → e'.left (jR (H.identity.left u')) = jU u' := by
      intro e e' he h
      have hh := congrArg (fun k : H.objects.left ⟶ U.left => k u')
        (show H.identity.left ≫ jR ≫ e'.left = jU by
          rw [← h, ← Category.assoc]
          change (H.identity ≫ e).left ≫ jU = jU
          rw [he]; exact Category.id_comp jU)
      exact hh
    have hz : jU u' ∈ jU '' {x | H.objects.hom x = N.point} := by
      rw [huf]
      exact ⟨jR (H.identity.left u'), hid _ _ H.source_identity hsrc,
        hid _ _ H.target_identity htgt⟩
    obtain ⟨v, hv, he⟩ := hz
    exact (jU.isOpenEmbedding.injective he) ▸ hv
  let N' := restrictNeighborhood N Q hpQ
  let q : N'.scheme ⟶ N.scheme := Q.ι
  let B := Classical.choice (AlgebraicGeometry.GroupoidScheme.exists_baseChange q H)
  let H' := B.groupoid
  let a : H'.objects.left ⟶ H.objects.left := B.projection.mapObjects.left
  let b : H'.arrows.left ⟶ H.arrows.left := B.projection.mapArrows.left
  let pU : pullback G.objects.hom N'.toBase ⟶ U.left :=
    baseChangeProjection G.objects.hom N.toBase q
  let pR : pullback G.arrows.hom N'.toBase ⟶ R.left :=
    baseChangeProjection G.arrows.hom N.toBase q
  have hpU : IsPullback pU (pullback.snd G.objects.hom N'.toBase) U.hom q :=
    baseChangeProjection_isPullback G.objects.hom N.toBase q
  have hpR : IsPullback pR (pullback.snd G.arrows.hom N'.toBase) R.hom q :=
    baseChangeProjection_isPullback G.arrows.hom N.toBase q
  let iU : H'.objects.left ⟶ pullback G.objects.hom N'.toBase :=
    baseChangeInclusion B.isPullback_objects hpU jU h11.symm
  let iR : H'.arrows.left ⟶ pullback G.arrows.hom N'.toBase :=
    baseChangeInclusion B.isPullback_arrows hpR jR h12.symm
  let Wn := pullback (jW ≫ U.hom) q
  let Wn' := pullback (jW' ≫ R.hom) q
  let iW := baseChangeInclusion (IsPullback.of_hasPullback (jW ≫ U.hom) q)
    hpU jW rfl
  let iW' := baseChangeInclusion (IsPullback.of_hasPullback (jW' ≫ R.hom) q)
    hpR jW' rfl
  have hiU : IsPullback a iU jU pU :=
    baseChangeInclusion_isPullback B.isPullback_objects hpU jU h11.symm
  have hiR : IsPullback b iR jR pR :=
    baseChangeInclusion_isPullback B.isPullback_arrows hpR jR h12.symm
  have hiW := baseChangeInclusion_isPullback
    (IsPullback.of_hasPullback (jW ≫ U.hom) q) hpU jW rfl
  have hiW' := baseChangeInclusion_isPullback
    (IsPullback.of_hasPullback (jW' ≫ R.hom) q) hpR jW' rfl
  have hiUbase : iU ≫ pullback.snd G.objects.hom N'.toBase = H'.objects.hom :=
    hpU.lift_snd _ _ _
  have hiRbase : iR ≫ pullback.snd G.arrows.hom N'.toBase = H'.arrows.hom :=
    hpR.lift_snd _ _ _
  let : IsOpenImmersion q := inferInstanceAs (IsOpenImmersion Q.ι)
  let : IsOpenImmersion pU := MorphismProperty.of_isPullback hpU.flip inferInstance
  let : IsOpenImmersion pR := MorphismProperty.of_isPullback hpR.flip inferInstance
  let : IsOpenImmersion iU := MorphismProperty.of_isPullback hiU h1
  let : IsClosedImmersion iU := MorphismProperty.of_isPullback hiU h2
  let : IsOpenImmersion iR := MorphismProperty.of_isPullback hiR h6
  let : IsClosedImmersion iR := MorphismProperty.of_isPullback hiR h7
  let : IsOpenImmersion iW := MorphismProperty.of_isPullback hiW h3
  let : IsClosedImmersion iW := MorphismProperty.of_isPullback hiW h4
  let : IsOpenImmersion iW' := MorphismProperty.of_isPullback hiW' h8
  let : IsClosedImmersion iW' := MorphismProperty.of_isPullback hiW' h9
  have hcopU : IsIso (coprod.desc iU iW) :=
    coprod_isIso_of_isPullbacks jU jW iU iW _ _ pU hiU hiW
  have hcopR : IsIso (coprod.desc iR iW') :=
    coprod_isIso_of_isPullbacks jR jW' iR iW' _ _ pR hiR hiW'
  have hfinU : IsFinite H'.objects.hom :=
    MorphismProperty.of_isPullback B.isPullback_objects h14
  have hfinR : IsFinite H'.arrows.hom :=
    MorphismProperty.of_isPullback B.isPullback_arrows h15
  have hqp : q N'.point = N.point := rfl
  obtain ⟨un, hun, hunp⟩ := lift_point_of_open_baseChange a H'.objects.hom
    H.objects.hom q B.isPullback_objects u' N'.point hu'p
  have hiUf : iU ≫ pullback.fst G.objects.hom N'.toBase =
      a ≫ jU ≫ pullback.fst G.objects.hom N.toBase := by
    have hh := congrArg (fun k => k ≫ pullback.fst G.objects.hom N.toBase) hiU.w
    simpa only [Category.assoc, pU, baseChangeProjection, pullback.lift_fst] using hh.symm
  have hiRf : iR ≫ pullback.fst G.arrows.hom N'.toBase =
      b ≫ jR ≫ pullback.fst G.arrows.hom N.toBase := by
    have hh := congrArg (fun k => k ≫ pullback.fst G.arrows.hom N.toBase) hiR.w
    simpa only [Category.assoc, pR, baseChangeProjection, pullback.lift_fst] using hh.symm
  have hbs : b ≫ H.source.left = H'.source.left ≫ a :=
    congrArg (fun k => k.left) B.projection.map_source
  have hbt : b ≫ H.target.left = H'.target.left ≫ a :=
    congrArg (fun k => k.left) B.projection.map_target
  have hlift_comm : ∀ (e : H.arrows ⟶ H.objects) (e' : H'.arrows ⟶ H'.objects)
      (g : G.arrows ⟶ G.objects), b ≫ e.left = e'.left ≫ a →
      e.left ≫ jU ≫ pullback.fst G.objects.hom N.toBase =
        jR ≫ pullback.fst G.arrows.hom N.toBase ≫ g.left →
      e'.left ≫ iU ≫ pullback.fst G.objects.hom N'.toBase =
        iR ≫ pullback.fst G.arrows.hom N'.toBase ≫ g.left := by
    intro e e' g hb h
    rw [hiUf, ← Category.assoc e'.left a, ← hb, Category.assoc, h,
      ← Category.assoc iR, hiRf, Category.assoc, Category.assoc]
  have hsrcf := hlift_comm H.source H'.source G.source hbs h16
  have htgtf := hlift_comm H.target H'.target G.target hbt h17
  let sn := (Over.pullback N'.toBase).map G.source
  let tn := (Over.pullback N'.toBase).map G.target
  have hpmap : ∀ g : G.arrows ⟶ G.objects,
      pR ≫ (F.map g).left = ((Over.pullback N'.toBase).map g).left ≫ pU := by
    intro g
    dsimp only [F, pR, pU, N', restrictNeighborhood, q]
    apply pullback.hom_ext <;>
      simp [baseChangeProjection, Over.pullback_map_left,
        Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  have hsnp : pR ≫ s.left = sn.left ≫ pU := hpmap G.source
  have htnp : pR ≫ t.left = tn.left ≫ pU := hpmap G.target
  have hcommn : ∀ (e' : H'.arrows ⟶ H'.objects) (g : G.arrows ⟶ G.objects),
      e'.left ≫ iU ≫ pullback.fst G.objects.hom N'.toBase =
        iR ≫ pullback.fst G.arrows.hom N'.toBase ≫ g.left →
      e'.left ≫ iU = iR ≫ ((Over.pullback N'.toBase).map g).left := by
    intro e' g h
    apply pullback.hom_ext
    · simpa only [Category.assoc, Over.pullback_map_left, pullback.lift_fst] using h
    · simp only [Category.assoc, hiUbase, Over.pullback_map_left, pullback.lift_snd,
        hiRbase, e'.w]
  have hsrcn : H'.source.left ≫ iU = iR ≫ sn.left := hcommn H'.source G.source hsrcf
  have htgtn : H'.target.left ≫ iU = iR ≫ tn.left := hcommn H'.target G.target htgtf
  have hiUpoint : pU (iU un) = jU u' := by
    have hh := congrArg (fun k => k un) hiU.w
    change jU (a un) = pU (iU un) at hh
    simpa only [hun] using hh.symm
  have hfu : iU '' {x | H'.objects.hom x = N'.point} =
      pU ⁻¹' (jU '' {x | H.objects.hom x = N.point}) := by
    have hf := image_fiber_baseChange jU iU a pU hiU U.hom
      (pullback.snd G.objects.hom N'.toBase) q hpU.w
      q.isOpenEmbedding.injective N'.point
    simpa only [hiUbase, ← h11b, hqp] using hf
  have hfr : iR '' {r | H'.arrows.hom r = N'.point} =
      pR ⁻¹' (jR '' {r | H.arrows.hom r = N.point}) := by
    have hf := image_fiber_baseChange jR iR b pR hiR R.hom
      (pullback.snd G.arrows.hom N'.toBase) q hpR.w
      q.isOpenEmbedding.injective N'.point
    simpa only [hiRbase, ← h12b, hqp] using hf
  have horbit : iU '' {x | H'.objects.hom x = N'.point} =
      tn.left '' (sn.left ⁻¹' {iU un}) := by
    rw [hfu, huf, ← hiUpoint]
    apply preimage_orbit_of_lift s.left t.left sn.left tn.left pR pU
      (fun z => congrArg (fun k => k z) hsnp)
      (fun z => congrArg (fun k => k z) htnp) pU.isOpenEmbedding.injective
    intro r hr
    rw [range_fst_of_isPullback hpR]
    refine ⟨N'.point, ?_⟩
    show N.point = R.hom r
    have hh := congrArg (fun k => k r) s.w
    change U.hom (s.left r) = R.hom r at hh
    rw [hr, hiUpoint, ← Scheme.Hom.comp_apply, ← h11b, hu'p] at hh
    exact hh
  have hrfb : jR '' {r | H.arrows.hom r = N.point} =
      s.left ⁻¹' (jU '' {x | H.objects.hom x = N.point}) := hrf
  have harrows : iR '' {r | H'.arrows.hom r = N'.point} =
      sn.left ⁻¹' (iU '' {x | H'.objects.hom x = N'.point}) := by
    rw [hfr, hfu, hrfb]
    ext r
    simp only [Set.mem_preimage]
    exact Iff.of_eq (congrArg (fun z => z ∈ jU '' {x | H.objects.hom x = N.point})
      (congrArg (fun k => k r) hsnp))
  obtain ⟨k, hk1, hk2, hk3⟩ := h18
  obtain ⟨l, hl1, hl2, hl3⟩ := homOver_composition B.projection
  refine ⟨N', shrinkEtaleNeighborhood_elementary N hN Q hpQ, H', Wn, Wn', iU, iW,
    iR, iW', inferInstance, inferInstance, inferInstance, inferInstance, hcopU,
    inferInstance, inferInstance, inferInstance, inferInstance, hcopR,
    hiUbase.symm, hiRbase.symm, ⟨un, ?_, horbit, harrows⟩, hfinU, hfinR,
    hsrcf, htgtf, ⟨l ≫ k, ?_, ?_, ?_⟩, ?_⟩
  · rw [hiUf]
    show (jU ≫ pullback.fst G.objects.hom N.toBase) (a un) = u
    rw [hun, hu']
  · rw [Category.assoc, hk1, ← Category.assoc l, hl1]
    simp only [Category.assoc, hiRf, H', b]
  · rw [Category.assoc, hk2, ← Category.assoc l, hl2]
    simp only [Category.assoc, hiRf, H', b]
  · simp only [Category.assoc, hiRf]
    rw [← Category.assoc H'.comp.left b, hl3, Category.assoc, hk3]
  · intro T f x y hfs hft
    change f ≫ sn.left = x ≫ iU at hfs
    change f ≫ tn.left = y ≫ iU at hft
    have hold : ∀ (x : T ⟶ H'.objects.left) (g : G.arrows ⟶ G.objects),
        f ≫ ((Over.pullback N'.toBase).map g).left = x ≫ iU →
        (f ≫ pR) ≫ (F.map g).left = (x ≫ a) ≫ jU := by
      intro x g h
      rw [Category.assoc, hpmap, ← Category.assoc, h]
      simpa only [Category.assoc] using congrArg (fun k => x ≫ k) hiU.w.symm
    have hfsold : (f ≫ pR) ≫ s.left = (x ≫ a) ≫ jU := hold x G.source hfs
    have hftold : (f ≫ pR) ≫ t.left = (y ≫ a) ≫ jU := hold y G.target hft
    have hfavoid := avoids_complement_of_relation U R H.objects w s t i iw Q havoid
      (f ≫ pR) (x ≫ a) (y ≫ a) hfsold hftold (by
        intro z
        rw [Category.assoc, hpR.w]
        exact ((pullback.snd G.arrows.hom N'.toBase) (f z)).property)
    have hfrange : Set.range f ⊆ Set.range iR := by
      rintro z ⟨v, rfl⟩
      rw [range_fst_of_isPullback hiR.flip]
      rcases point_mem_range_coprod_desc jR jW' (pR (f v)) with hr | hr
      · exact hr
      · exact (hfavoid v hr).elim
    obtain ⟨g, hg, huniq⟩ := existsUnique_openImmersion_lift iR f hfrange
    refine ⟨g, ⟨hg, ?_, ?_⟩, fun g' hg' => huniq g' hg'.1⟩
    · apply (cancel_mono iU).mp
      rw [Category.assoc, hsrcn, ← Category.assoc, hg, hfs]
    · apply (cancel_mono iU).mp
      rw [Category.assoc, htgtn, ← Category.assoc, hg, hft]

end AlgebraicGeometry.GroupoidScheme
