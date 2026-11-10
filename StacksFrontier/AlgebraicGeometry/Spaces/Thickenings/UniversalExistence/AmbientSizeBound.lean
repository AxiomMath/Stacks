module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.SiteThickening
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.FirstOrderClauseAndAffineSize
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.SiteThickening

/-!
# Universal thickening existence: the ambient of a universal thickening lies in the site

The chart data of the construction, the invariance of the underlying space under a first order
thickening, first order thickenings along pullbacks of relations, joint monicity of the lifted
relation, and the size bound showing that the ambient scheme of a universal first order
thickening of a morphism of the site lies in the site.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Spaces.UniversalThickening

open AlgebraicGeometry.Space

private lemma exists_formallyUnramified_surjectiveEtale_chart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicGeometry.AlgebraicSpaces B S hS} (h : Z ⟶ X)
    (hh : AlgebraicGeometry.Space.FormallyUnramified h.hom) :
    ∃ (V U : AlgebraicGeometry.BigFppfOver B S hS)
      (a : yoneda.obj V ⟶ Z.1) (b : yoneda.obj U ⟶ X.1) (ψ : V ⟶ U),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf b ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf b ∧
      yoneda.map ψ ≫ b = a ≫ h.hom ∧
      FormallyUnramified ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map ψ) :=
  (AlgebraicGeometry.Space.formallyUnramified_iff_surjectiveEtaleChart B S hS
    Z.property X.property h.hom).mp hh

private structure ChartThickening
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicGeometry.AlgebraicSpaces B S hS} (h : Z ⟶ X) where
  V : AlgebraicGeometry.BigFppfOver B S hS
  U : AlgebraicGeometry.BigFppfOver B S hS
  sourceChart : yoneda.obj V ⟶ Z.1
  targetChart : yoneda.obj U ⟶ X.1
  chartMap : V ⟶ U
  sourceEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf sourceChart
  targetEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf targetChart
  sourceSurjective : (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf sourceChart
  targetSurjective : (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf targetChart
  comm : yoneda.map chartMap ≫ targetChart = sourceChart ≫ h.hom
  formallyUnramified : FormallyUnramified
    ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map chartMap)
  thickening : Stacks.Thickenings.UniversalFirstOrderThickening
    ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map chartMap)

private structure ChartKernelPair
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z : AlgebraicGeometry.AlgebraicSpaces B S hS}
    {V : AlgebraicGeometry.BigFppfOver B S hS} (a : yoneda.obj V ⟶ Z.1) where
  R : AlgebraicGeometry.BigFppfOver B S hS
  source : R ⟶ V
  target : R ⟶ V
  toSpace : yoneda.obj R ⟶ Z.1
  kernelPair : IsPullback (yoneda.map source) (yoneda.map target) a a
  etaleRelation : Stacks.Groupoids.IsEtaleEquivalenceRelation
    (AlgebraicGeometry.Space.sitePreRelation B S hS source target)

/-! A first-order thickening does not change the underlying space.  This lets
us extend open pieces of the relation chart to its thickened ambient scheme. -/

private noncomputable def bridge_thickeningHomeomorph
    {Z Z' : Scheme.{u}} (i : Z ⟶ Z')
    (hi : Stacks.Thickenings.IsThickening i) : Z ≃ₜ Z' := by
  letI : IsClosedImmersion i := hi.1
  exact (Equiv.ofBijective i.base ⟨i.isClosedEmbedding.injective, hi.2⟩)
    |>.toHomeomorphOfContinuousClosed i.continuous i.isClosedEmbedding.isClosedMap

private noncomputable def bridge_thickeningOpenImage
    {Z Z' : Scheme.{u}} (i : Z ⟶ Z')
    (hi : Stacks.Thickenings.IsThickening i) (V : Z.Opens) : Z'.Opens := by
  let e := bridge_thickeningHomeomorph i hi
  exact ⟨e '' V, e.isOpenMap _ V.2⟩

private lemma bridge_preimage_thickeningOpenImage
    {Z Z' : Scheme.{u}} (i : Z ⟶ Z')
    (hi : Stacks.Thickenings.IsThickening i) (V : Z.Opens) :
    i ⁻¹ᵁ bridge_thickeningOpenImage i hi V = V := by
  let e := bridge_thickeningHomeomorph i hi
  ext x
  change e x ∈ e '' V ↔ x ∈ V
  simp

private lemma bridge_firstOrder_pullback
    {T T' V : Scheme.{u}} (j : T ⟶ T')
    (hj : Stacks.Thickenings.IsFirstOrderThickening j) (v : V ⟶ T') [IsOpenImmersion v] :
    Stacks.Thickenings.IsFirstOrderThickening (Limits.pullback.fst v j) := by
  have : IsClosedImmersion j := hj.1
  refine ⟨inferInstance, ?_⟩
  rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  exact Stacks.IdealSheaf.comap_pow_eq_bot j.ker v hj.2

private lemma bridge_firstOrder_of_isPullback
    {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback a b f g) (hf : Stacks.Thickenings.IsFirstOrderThickening f) :
    Stacks.Thickenings.IsFirstOrderThickening b := by
  have : IsClosedImmersion f := hf.1
  have : IsClosedImmersion b :=
    MorphismProperty.of_isPullback sq hf.1
  refine ⟨inferInstance, ?_⟩
  rw [← sq.flip.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  exact Stacks.IdealSheaf.comap_pow_eq_bot f.ker _ hf.2

private lemma bridge_relationPullback_square
    {C : Type*} [Category C] [Limits.HasPullbacks C]
    {V R V' R' : C}
    (s t : R ⟶ V) (s' t' : R' ⟶ V')
    (iV : V ⟶ V') (iR : R ⟶ R')
    (hs : IsPullback s iR iV s')
    (ht : iR ≫ t' = t ≫ iV)
    [Mono iR] :
    ∃ iP : Limits.pullback t s ⟶ Limits.pullback t' s',
      IsPullback (Limits.pullback.fst t s) iP iR
        (Limits.pullback.fst t' s') ∧
      iP ≫ Limits.pullback.snd t' s' =
        Limits.pullback.snd t s ≫ iR := by
  let iP : Limits.pullback t s ⟶ Limits.pullback t' s' :=
    Limits.pullback.lift
      (Limits.pullback.fst t s ≫ iR)
      (Limits.pullback.snd t s ≫ iR) (by
        calc
          (Limits.pullback.fst t s ≫ iR) ≫ t' =
              Limits.pullback.fst t s ≫ (iR ≫ t') := Category.assoc _ _ _
          _ = Limits.pullback.fst t s ≫ (t ≫ iV) := by rw [ht]
          _ = (Limits.pullback.fst t s ≫ t) ≫ iV :=
            (Category.assoc _ _ _).symm
          _ = (Limits.pullback.snd t s ≫ s) ≫ iV := by
            rw [Limits.pullback.condition]
          _ = Limits.pullback.snd t s ≫ (s ≫ iV) := Category.assoc _ _ _
          _ = Limits.pullback.snd t s ≫ (iR ≫ s') := by rw [hs.w]
          _ = (Limits.pullback.snd t s ≫ iR) ≫ s' :=
            (Category.assoc _ _ _).symm)
  have hfst : iP ≫ Limits.pullback.fst t' s' =
      Limits.pullback.fst t s ≫ iR := Limits.pullback.lift_fst _ _ _
  have hsnd : iP ≫ Limits.pullback.snd t' s' =
      Limits.pullback.snd t s ≫ iR := Limits.pullback.lift_snd _ _ _
  have hpb : IsPullback (Limits.pullback.fst t s) iP iR
      (Limits.pullback.fst t' s') := by
    apply IsPullback.mk' (by rw [hfst])
    · intro T a b ha hb
      apply Limits.pullback.hom_ext
      · exact ha
      · apply (cancel_mono iR).mp
        calc
          (a ≫ Limits.pullback.snd t s) ≫ iR =
              a ≫ (iP ≫ Limits.pullback.snd t' s') := by rw [hsnd, Category.assoc]
          _ = (a ≫ iP) ≫ Limits.pullback.snd t' s' :=
            (Category.assoc _ _ _).symm
          _ = (b ≫ iP) ≫ Limits.pullback.snd t' s' := by rw [hb]
          _ = b ≫ (iP ≫ Limits.pullback.snd t' s') := Category.assoc _ _ _
          _ = (b ≫ Limits.pullback.snd t s) ≫ iR := by rw [hsnd, Category.assoc]
    · intro T a b hab
      have hcomm : (a ≫ t) ≫ iV =
          (b ≫ Limits.pullback.snd t' s') ≫ s' := by
        calc
          (a ≫ t) ≫ iV = a ≫ (t ≫ iV) := Category.assoc _ _ _
          _ = a ≫ (iR ≫ t') := by rw [ht]
          _ = (a ≫ iR) ≫ t' := (Category.assoc _ _ _).symm
          _ = (b ≫ Limits.pullback.fst t' s') ≫ t' := by rw [hab]
          _ = b ≫ (Limits.pullback.fst t' s' ≫ t') := Category.assoc _ _ _
          _ = b ≫ (Limits.pullback.snd t' s' ≫ s') := by
            rw [Limits.pullback.condition]
          _ = (b ≫ Limits.pullback.snd t' s') ≫ s' :=
            (Category.assoc _ _ _).symm
      let a₂ : T ⟶ R := hs.lift (a ≫ t)
        (b ≫ Limits.pullback.snd t' s') hcomm
      let l : T ⟶ Limits.pullback t s :=
        Limits.pullback.lift a a₂ (hs.lift_fst _ _ _).symm
      refine ⟨l, Limits.pullback.lift_fst _ _ _, ?_⟩
      apply Limits.pullback.hom_ext
      · calc
          (l ≫ iP) ≫ Limits.pullback.fst t' s' =
              l ≫ (iP ≫ Limits.pullback.fst t' s') := Category.assoc _ _ _
          _ = l ≫ (Limits.pullback.fst t s ≫ iR) := by rw [hfst]
          _ = (l ≫ Limits.pullback.fst t s) ≫ iR :=
            (Category.assoc _ _ _).symm
          _ = a ≫ iR := by rw [Limits.pullback.lift_fst]
          _ = b ≫ Limits.pullback.fst t' s' := hab
      · calc
          (l ≫ iP) ≫ Limits.pullback.snd t' s' =
              l ≫ (iP ≫ Limits.pullback.snd t' s') := Category.assoc _ _ _
          _ = l ≫ (Limits.pullback.snd t s ≫ iR) := by rw [hsnd]
          _ = (l ≫ Limits.pullback.snd t s) ≫ iR :=
            (Category.assoc _ _ _).symm
          _ = a₂ ≫ iR := by rw [Limits.pullback.lift_snd]
          _ = b ≫ Limits.pullback.snd t' s' := hs.lift_snd _ _ _
  exact ⟨iP, hpb, hsnd⟩

private lemma bridge_relationPullback_firstOrder
    {V R V' R' : Scheme.{u}}
    (s t : R ⟶ V) (s' t' : R' ⟶ V')
    (iV : V ⟶ V') (iR : R ⟶ R')
    (hs : IsPullback s iR iV s')
    (ht : iR ≫ t' = t ≫ iV)
    (hiR : Stacks.Thickenings.IsFirstOrderThickening iR) :
    ∃ iP : Limits.pullback t s ⟶ Limits.pullback t' s',
      IsPullback (Limits.pullback.fst t s) iP iR
        (Limits.pullback.fst t' s') ∧
      iP ≫ Limits.pullback.snd t' s' =
        Limits.pullback.snd t s ≫ iR ∧
      Stacks.Thickenings.IsFirstOrderThickening iP := by
  have : IsClosedImmersion iR := hiR.1
  have : Mono iR := inferInstance
  obtain ⟨iP, hpb, hsnd⟩ :=
    bridge_relationPullback_square s t s' t' iV iR hs ht
  exact ⟨iP, hpb, hsnd, bridge_firstOrder_of_isPullback hpb hiR⟩

private lemma bridge_jointlyMono_of_universalRelation
    {V R V' R' U W : Scheme.{u}}
    (s t : R ⟶ V) (s' t' : R' ⟶ V')
    (r : R ⟶ W) (α β : W ⟶ U)
    (iV : V ⟶ V') (iR : R ⟶ R')
    (pV : V' ⟶ U) (pR : R' ⟶ W)
    (hK : JointlyMono₂ s t) (hW : JointlyMono₂ α β)
    [Mono iV]
    (hR : Stacks.Thickenings.IsUniversalFirstOrderThickening r iR pR)
    (hs : IsPullback s iR iV s')
    (ht : iR ≫ t' = t ≫ iV)
    (hp : s' ≫ pV = pR ≫ α)
    (hq : t' ≫ pV = pR ≫ β) :
    JointlyMono₂ s' t' := by
  refine ⟨?_⟩
  intro T x y hxs hxt
  have hcancel (f : R' ⟶ V') (g : W ⟶ U) (hf : f ≫ pV = pR ≫ g) (hxf : x ≫ f = y ≫ f) :
      (x ≫ pR) ≫ g = (y ≫ pR) ≫ g := by
    rw [Category.assoc, Category.assoc, ← hf, ← Category.assoc, ← Category.assoc, hxf]
  have hbase : x ≫ pR = y ≫ pR :=
    hW.right_cancellation _ _ (hcancel _ _ hp hxs) (hcancel _ _ hq hxt)
  let T₀ := Limits.pullback x iR
  let j : T₀ ⟶ T := Limits.pullback.fst x iR
  let e : T₀ ⟶ R := Limits.pullback.snd x iR
  have hje : j ≫ x = e ≫ iR := Limits.pullback.condition
  have hj : Stacks.Thickenings.IsFirstOrderThickening j :=
    bridge_firstOrder_of_isPullback
      (IsPullback.of_hasPullback x iR).flip hR.isFirstOrderThickening
  have hcomm : (e ≫ s) ≫ iV = (j ≫ y) ≫ s' := by
    calc
      (e ≫ s) ≫ iV = e ≫ (s ≫ iV) := Category.assoc _ _ _
      _ = e ≫ (iR ≫ s') := by rw [hs.w]
      _ = (e ≫ iR) ≫ s' := (Category.assoc _ _ _).symm
      _ = (j ≫ x) ≫ s' := by rw [hje]
      _ = j ≫ (x ≫ s') := Category.assoc _ _ _
      _ = j ≫ (y ≫ s') := by rw [hxs]
      _ = (j ≫ y) ≫ s' := (Category.assoc _ _ _).symm
  let e₂ : T₀ ⟶ R := hs.lift (e ≫ s) (j ≫ y) hcomm
  have he₂s : e₂ ≫ s = e ≫ s := hs.lift_fst _ _ _
  have he₂i : e₂ ≫ iR = j ≫ y := hs.lift_snd _ _ _
  have he₂t : e₂ ≫ t = e ≫ t := by
    apply (cancel_mono iV).mp
    calc
      (e₂ ≫ t) ≫ iV = e₂ ≫ (t ≫ iV) := Category.assoc _ _ _
      _ = e₂ ≫ (iR ≫ t') := by rw [ht]
      _ = (e₂ ≫ iR) ≫ t' := (Category.assoc _ _ _).symm
      _ = (j ≫ y) ≫ t' := by rw [he₂i]
      _ = j ≫ (y ≫ t') := Category.assoc _ _ _
      _ = j ≫ (x ≫ t') := by rw [hxt]
      _ = (j ≫ x) ≫ t' := (Category.assoc _ _ _).symm
      _ = (e ≫ iR) ≫ t' := by rw [hje]
      _ = e ≫ (iR ≫ t') := Category.assoc _ _ _
      _ = e ≫ (t ≫ iV) := by rw [ht]
      _ = (e ≫ t) ≫ iV := (Category.assoc _ _ _).symm
  have he₂ : e₂ = e := hK.right_cancellation _ _ he₂s he₂t
  have hjy : j ≫ y = e ≫ iR := by rw [← he₂i, he₂]
  have hcompat : j ≫ (x ≫ pR) = e ≫ r := by
    calc
      j ≫ (x ≫ pR) = (j ≫ x) ≫ pR := (Category.assoc _ _ _).symm
      _ = (e ≫ iR) ≫ pR := by rw [hje]
      _ = e ≫ (iR ≫ pR) := Category.assoc _ _ _
      _ = e ≫ r := by rw [hR.inclusion_toBase]
  obtain ⟨z, _, uniq⟩ := hR.existsUnique_lift j hj e (x ≫ pR) hcompat
  have hx : x = z := uniq x ⟨hje, rfl⟩
  have hy : y = z := uniq y ⟨hjy, hbase.symm⟩
  exact hx.trans hy.symm

private lemma bridge_jointlyMono_scheme_of_over
    {S : Scheme.{u}} {R V : Over S} (s t : R ⟶ V)
    (h : JointlyMono₂ s t) : JointlyMono₂ s.left t.left := by
  refine ⟨?_⟩
  intro T x y hs ht
  let T₀ : Over S := Over.mk (x ≫ R.hom)
  have hy : y ≫ R.hom = x ≫ R.hom := by
    calc
      y ≫ R.hom = y ≫ (s.left ≫ V.hom) := by rw [s.w]
      _ = (y ≫ s.left) ≫ V.hom := (Category.assoc _ _ _).symm
      _ = (x ≫ s.left) ≫ V.hom := by rw [hs]
      _ = x ≫ (s.left ≫ V.hom) := Category.assoc _ _ _
      _ = x ≫ R.hom := by rw [s.w]
  let x₀ : T₀ ⟶ R := Over.homMk x rfl
  let y₀ : T₀ ⟶ R := Over.homMk y hy
  have hs₀ : x₀ ≫ s = y₀ ≫ s := by
    apply CostructuredArrow.hom_ext
    exact hs
  have ht₀ : x₀ ≫ t = y₀ ≫ t := by
    apply CostructuredArrow.hom_ext
    exact ht
  exact congrArg (fun f : T₀ ⟶ R => f.left)
    (h.right_cancellation x₀ y₀ hs₀ ht₀)

private lemma bridge_jointlyMono_over_of_scheme
    {S : Scheme.{u}} {R V : Over S} (s t : R ⟶ V)
    (h : JointlyMono₂ s.left t.left) : JointlyMono₂ s t := by
  refine ⟨?_⟩
  intro T x y hs ht
  apply CostructuredArrow.hom_ext
  exact h.right_cancellation x.left y.left
    (congrArg (fun f : T ⟶ V => f.left) hs)
    (congrArg (fun f : T ⟶ V => f.left) ht)

private lemma bridge_firstOrder_restrict
    {Z Z' : Scheme.{u}} (i : Z ⟶ Z')
    (hi : Stacks.Thickenings.IsFirstOrderThickening i) (U : Z'.Opens) :
    Stacks.Thickenings.IsFirstOrderThickening (i ∣_ U) := by
  let : IsClosedImmersion (i ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict i U).flip hi.1
  refine ⟨inferInstance, ?_⟩
  let : IsClosedImmersion i := hi.1
  apply Scheme.IdealSheafData.ext
  funext W
  let A : Z'.affineOpens := ⟨U.ι ''ᵁ W, W.2.image_of_isOpenImmersion U.ι⟩
  have hker := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion i (i ∣_ U)
    (i ⁻¹ᵁ U).ι U.ι (isPullback_morphismRestrict i U) W
  have hJ : (i.ker.ideal A) ^ 2 = ⊥ := by
    have h := congrArg (fun K : Scheme.IdealSheafData Z' => K.ideal A) hi.2
    simpa [Scheme.IdealSheafData.ideal_pow] using h
  change ((i ∣_ U).ker.ideal W) ^ 2 = ⊥
  rw [hker]
  let φ := CommRingCat.Hom.hom (U.ι.appIso W).inv
  let J := i.ker.ideal A
  change (Ideal.comap φ J) ^ 2 = ⊥
  have hle := Ideal.le_comap_pow (K := J) φ 2
  rw [hJ] at hle
  have hφ : Function.Injective φ :=
    (ConcreteCategory.bijective_of_isIso (U.ι.appIso W).inv).1
  have hbot : Ideal.comap φ ⊥ = ⊥ := Ideal.comap_bot_of_injective φ hφ
  have hle' : (Ideal.comap φ J) ^ 2 ≤ ⊥ := by simpa [hbot] using hle
  exact le_antisymm hle' bot_le

private lemma bridge_universalThickening_comp_formallyEtale
    {Z X Y Z' : Scheme.{u}} (h : Z ⟶ Y) (i : Z ⟶ Z')
    (p : Z' ⟶ Y) (e : Y ⟶ X)
    (hi : Stacks.Thickenings.IsUniversalFirstOrderThickening h i p)
    (he : AlgebraicGeometry.FormallyEtale e) :
    Stacks.Thickenings.IsUniversalFirstOrderThickening (h ≫ e) i (p ≫ e) := by
  refine ⟨hi.isFirstOrderThickening, ?_, ?_⟩
  · simpa only [Category.assoc] using
      congrArg (fun f => f ≫ e) hi.inclusion_toBase
  · intro T T' j hj a b hab
    obtain ⟨c, hc, hcu⟩ := AlgebraicGeometry.FormallyEtale.existsUnique_lift
      e he j hj b (a ≫ h) (by simpa only [Category.assoc] using hab.symm)
    obtain ⟨d, hd, hdu⟩ := hi.existsUnique_lift j hj a c hc.1
    refine ⟨d, ⟨hd.1, by rw [← Category.assoc, hd.2, hc.2]⟩, ?_⟩
    intro d' hd'
    have hc' : d' ≫ p = c := by
      apply hcu (d' ≫ p)
      constructor
      · calc
          j ≫ (d' ≫ p) = (j ≫ d') ≫ p := (Category.assoc _ _ _).symm
          _ = (a ≫ i) ≫ p := by rw [hd'.1]
          _ = a ≫ h := by rw [Category.assoc, hi.inclusion_toBase]
      · simpa only [Category.assoc] using hd'.2
    apply hdu d'
    exact ⟨hd'.1, hc'⟩

private lemma bridge_universalThickening_comp_etale
    {Z X Y Z' : Scheme.{u}} (h : Z ⟶ Y) (i : Z ⟶ Z')
    (p : Z' ⟶ Y) (e : Y ⟶ X)
    (hi : Stacks.Thickenings.IsUniversalFirstOrderThickening h i p)
    (he : Etale e) :
    Stacks.Thickenings.IsUniversalFirstOrderThickening (h ≫ e) i (p ≫ e) :=
  bridge_universalThickening_comp_formallyEtale h i p e hi
    ((AlgebraicGeometry.etale_iff_locallyOfFinitePresentation_and_formallyEtale e).mp he).2

private lemma bridge_universalThickening_cancel_mono_base
    {Z X Y Z' : Scheme.{u}} (h : Z ⟶ Y) (i : Z ⟶ Z')
    (p : Z' ⟶ Y) (e : Y ⟶ X) [Mono e]
    (hi : Stacks.Thickenings.IsUniversalFirstOrderThickening (h ≫ e) i (p ≫ e)) :
    Stacks.Thickenings.IsUniversalFirstOrderThickening h i p := by
  refine ⟨hi.isFirstOrderThickening, (cancel_mono e).mp (by
    simpa only [Category.assoc] using hi.inclusion_toBase), ?_⟩
  intro T T' j hj a b hab
  obtain ⟨c, hc, hcu⟩ := hi.existsUnique_lift j hj a (b ≫ e) (by
    simpa only [Category.assoc] using congrArg (fun f => f ≫ e) hab)
  have hcb : c ≫ p = b := (cancel_mono e).mp (by
    simpa only [Category.assoc] using hc.2)
  refine ⟨c, ⟨hc.1, hcb⟩, ?_⟩
  intro d hd
  apply hcu d
  refine ⟨hd.1, ?_⟩
  simpa only [Category.assoc] using congrArg (fun f => f ≫ e) hd.2

private lemma bridge_universalThickening_factor_targetOpen
    {Z X Z' : Scheme.{u}} (h : Z ⟶ X) (i : Z ⟶ Z')
    (p : Z' ⟶ X) (hi : Stacks.Thickenings.IsUniversalFirstOrderThickening h i p)
    (U : X.Opens) (hrange : Set.range h.base ⊆ Set.range U.ι.base) :
    ∃ (h' : Z ⟶ U) (p' : Z' ⟶ U),
      h' ≫ U.ι = h ∧ p' ≫ U.ι = p ∧
        Stacks.Thickenings.IsUniversalFirstOrderThickening h' i p' := by
  have hprange : Set.range p.base ⊆ Set.range U.ι.base := by
    rintro y ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hi.isFirstOrderThickening.isThickening.2 x
    have heq := congrArg (fun f : Z ⟶ X => f.base z) hi.inclusion_toBase
    have hp : p.base (i.base z) = h.base z := by
      simpa [Scheme.Hom.comp_base] using heq
    rw [← hz, hp]
    exact hrange ⟨z, rfl⟩
  let p' := IsOpenImmersion.lift U.ι p hprange
  have hp' : p' ≫ U.ι = p := IsOpenImmersion.lift_fac U.ι p hprange
  let h' := i ≫ p'
  have hh' : h' ≫ U.ι = h := by
    dsimp [h']
    rw [Category.assoc, hp']
    exact hi.inclusion_toBase
  have hu : Stacks.Thickenings.IsUniversalFirstOrderThickening h' i p' := by
    apply bridge_universalThickening_cancel_mono_base h' i p' U.ι
    simpa only [hh', hp'] using hi
  exact ⟨h', p', hh', hp', hu⟩

private lemma bridge_universalThickening_restrictSource
    {Z X Z' : Scheme.{u}} (h : Z ⟶ X) (i : Z ⟶ Z') (p : Z' ⟶ X)
    (hi : Stacks.Thickenings.IsUniversalFirstOrderThickening h i p) (V : Z.Opens) :
    Stacks.Thickenings.IsUniversalFirstOrderThickening (V.ι ≫ h)
      (i.resLE (bridge_thickeningOpenImage i hi.isFirstOrderThickening.isThickening V) V
        (by rw [bridge_preimage_thickeningOpenImage]))
      ((bridge_thickeningOpenImage i hi.isFirstOrderThickening.isThickening V).ι ≫ p) := by
  let V' := bridge_thickeningOpenImage i hi.isFirstOrderThickening.isThickening V
  have hpre : i ⁻¹ᵁ V' = V :=
    bridge_preimage_thickeningOpenImage i hi.isFirstOrderThickening.isThickening V
  have hle : V ≤ i ⁻¹ᵁ V' := by rw [hpre]
  let i' := i.resLE V' V hle
  have hi'_comp : i' ≫ V'.ι = V.ι ≫ i := by
    dsimp [i']
    exact Scheme.Hom.resLE_comp_ι i hle
  have hi' : Stacks.Thickenings.IsFirstOrderThickening i' := by
    have hbase : Stacks.Thickenings.IsFirstOrderThickening
        (i.resLE V' (i ⁻¹ᵁ V') le_rfl) := by
      rw [Scheme.Hom.resLE_eq_morphismRestrict]
      exact bridge_firstOrder_restrict i hi.isFirstOrderThickening V'
    let P : MorphismProperty Scheme := fun _ _ f => Stacks.Thickenings.IsFirstOrderThickening f
    exact (Scheme.Hom.resLE_congr i hle rfl hpre.symm P).2 hbase
  refine ⟨hi', ?_, ?_⟩
  · change i' ≫ V'.ι ≫ p = V.ι ≫ h
    calc
      i' ≫ V'.ι ≫ p = (V.ι ≫ i) ≫ p := by
        rw [← Category.assoc, hi'_comp]
      _ = V.ι ≫ h := by simp only [Category.assoc, hi.inclusion_toBase]
  · intro T T' j hj a b hab
    obtain ⟨f, hf, hu⟩ := hi.existsUnique_lift j hj (a ≫ V.ι) b (by
      simpa [Category.assoc] using hab)
    have hrange : Set.range f.base ⊆ Set.range V'.ι.base := by
      rintro y ⟨x, rfl⟩
      obtain ⟨t, ht⟩ := hj.isThickening.2 x
      have heq := congrArg (fun g : T ⟶ Z' => g.base t) hf.1
      have heq' : f.base (j.base t) = i.base (V.ι.base (a.base t)) := by
        simpa [Scheme.Hom.comp_base] using heq
      have hmem : i.base (V.ι.base (a.base t)) ∈ V' := by
        change i.base (V.ι.base (a.base t)) ∈
          bridge_thickeningHomeomorph i hi.isFirstOrderThickening.isThickening '' V
        exact ⟨V.ι.base (a.base t), (a.base t).property, rfl⟩
      refine ⟨⟨i.base (V.ι.base (a.base t)), hmem⟩, ?_⟩
      change i.base (V.ι.base (a.base t)) = f.base x
      rw [← ht]
      exact heq'.symm
    let f' := IsOpenImmersion.lift V'.ι f hrange
    have hf'_fac : f' ≫ V'.ι = f := IsOpenImmersion.lift_fac V'.ι f hrange
    have hsource_comp : (a ≫ i') ≫ V'.ι = (a ≫ V.ι) ≫ i := by
      calc
        (a ≫ i') ≫ V'.ι = a ≫ (i' ≫ V'.ι) := by simp [Category.assoc]
        _ = a ≫ (V.ι ≫ i) := by rw [hi'_comp]
        _ = (a ≫ V.ι) ≫ i := by simp [Category.assoc]
    have hrestr : j ≫ f' = a ≫ i' := by
      apply (cancel_mono V'.ι).mp
      calc
        (j ≫ f') ≫ V'.ι = j ≫ f := by simp [Category.assoc, hf'_fac]
        _ = (a ≫ V.ι) ≫ i := hf.1
        _ = a ≫ i' ≫ V'.ι := hsource_comp.symm
    have hbase : f' ≫ (V'.ι ≫ p) = b := by
      calc
        f' ≫ (V'.ι ≫ p) = (f' ≫ V'.ι) ≫ p := by simp [Category.assoc]
        _ = f ≫ p := by rw [hf'_fac]
        _ = b := hf.2
    refine ⟨f', ⟨hrestr, hbase⟩, ?_⟩
    intro g hg
    apply (cancel_mono V'.ι).mp
    calc
      g ≫ V'.ι = f := hu (g ≫ V'.ι) ⟨by
        calc
          j ≫ (g ≫ V'.ι) = (j ≫ g) ≫ V'.ι := by simp [Category.assoc]
          _ = (a ≫ i') ≫ V'.ι := congrArg (fun z => z ≫ V'.ι) hg.1
          _ = (a ≫ V.ι) ≫ i := hsource_comp, by
        calc
          (g ≫ V'.ι) ≫ p = g ≫ (V'.ι ≫ p) := by simp [Category.assoc]
          _ = b := hg.2⟩
      _ = f' ≫ V'.ι := hf'_fac.symm

private lemma bridge_size_le_universalThickening
    {Z X H : Scheme.{u}} (h : Z ⟶ X) (i : Z ⟶ H) (p : H ⟶ X)
    (hi : Stacks.Thickenings.IsUniversalFirstOrderThickening h i p) :
    H.size ≤ max Z.size X.size := by
  classical
  let I := {ab : Z.affineOpens × X.affineOpens //
    ab.1.1 ≤ h ⁻¹ᵁ ab.2.1}
  let W : Option I → H.Opens
    | none => ⊥
    | some ab => bridge_thickeningOpenImage i hi.isFirstOrderThickening.isThickening ab.1.1.1
  have hW (ab : I) : ((W (some ab) : H.Opens) : Scheme).size ≤
      max Z.size X.size := by
    let A := ab.1.1.1
    let B := ab.1.2.1
    let A' := bridge_thickeningOpenImage i hi.isFirstOrderThickening.isThickening A
    have hA : A ≤ h ⁻¹ᵁ B := ab.2
    have hrange : Set.range (A.ι ≫ h).base ⊆ Set.range B.ι.base := by
      rintro y ⟨a, rfl⟩
      have hm : h.base (A.ι.base a) ∈ B := hA a.property
      exact ⟨⟨h.base (A.ι.base a), hm⟩, rfl⟩
    have hlocal := bridge_universalThickening_restrictSource h i p hi A
    obtain ⟨h', p', _, _, hup⟩ :=
      bridge_universalThickening_factor_targetOpen (A.ι ≫ h)
        (i.resLE A' A (by rw [bridge_preimage_thickeningOpenImage]))
        (A'.ι ≫ p) hlocal B hrange
    let : IsAffine (A : Scheme) := ab.1.1.2
    let : IsAffine (B : Scheme) := ab.1.2.2
    have hbound := bridge_size_le_universalThickening_affine h'
      (i.resLE A' A (by rw [bridge_preimage_thickeningOpenImage])) p' hup
    change (A' : Scheme).size ≤ max Z.size X.size
    exact hbound.trans (max_le_max (Scheme.size_coe_opens_le Z A)
      (Scheme.size_coe_opens_le X B))
  have hcov : ⨆ t, W t = ⊤ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨z, hz⟩ := hi.isFirstOrderThickening.isThickening.2 x
      have hx : h.base z ∈ (⊤ : X.Opens) := trivial
      obtain ⟨B, hB, hXB, _⟩ := exists_isAffineOpen_mem_and_subset hx
      have hzpre : z ∈ h ⁻¹ᵁ B := hXB
      obtain ⟨A, hA, hzA, hAB⟩ := exists_isAffineOpen_mem_and_subset hzpre
      let ab : I := ⟨(⟨A, hA⟩, ⟨B, hB⟩), hAB⟩
      have hmem : x ∈ W (some ab) := by
        change x ∈ bridge_thickeningHomeomorph i hi.isFirstOrderThickening.isThickening '' A
        exact ⟨z, hzA, hz⟩
      exact (le_iSup W (some ab)) hmem
  have hℵ : Cardinal.aleph0 ≤ max Z.size X.size := Z.aleph0_le_size.trans (le_max_left _ _)
  have hI : Cardinal.mk (Option I) ≤ max Z.size X.size := by
    have hsub : Cardinal.mk I ≤
        Cardinal.mk (Z.affineOpens × X.affineOpens) :=
      Cardinal.mk_le_of_injective Subtype.val_injective
    have hprod : Cardinal.mk (Z.affineOpens × X.affineOpens) ≤
        max (max (Cardinal.mk Z.affineOpens) (Cardinal.mk X.affineOpens))
          Cardinal.aleph0 := by
      simpa only [Cardinal.mk_prod, Cardinal.lift_id] using
        Cardinal.mul_le_max (Cardinal.mk Z.affineOpens)
          (Cardinal.mk X.affineOpens)
    have hbase : max (max (Cardinal.mk Z.affineOpens)
        (Cardinal.mk X.affineOpens)) Cardinal.aleph0 ≤ max Z.size X.size := by
      apply max_le
      · exact max_le
          ((Scheme.mk_affineOpens_le_size Z).trans (le_max_left _ _))
          ((Scheme.mk_affineOpens_le_size X).trans (le_max_right _ _))
      · exact hℵ
    have hle : Cardinal.mk I ≤ max Z.size X.size :=
      hsub.trans (hprod.trans hbase)
    rw [Cardinal.mk_option]
    exact (Cardinal.add_le_max _ _).trans
      (max_le (max_le hle ((by norm_num : (1 : Cardinal) ≤ Cardinal.aleph0).trans hℵ)) hℵ)
  have hsize : H.size ≤ max (Cardinal.mk (Option I))
      (⨆ t : Option I, ((W t : H.Opens) : Scheme).size) :=
    Scheme.size_le_of_iSup_eq_top W hcov
  exact hsize.trans (max_le hI (ciSup_le' fun t => by
    cases t with
    | none =>
        have : IsEmpty (W none : Scheme) := by
          change IsEmpty ((⊥ : H.Opens) : Scheme)
          exact ⟨fun x => x.2⟩
        exact (AlgebraicGeometry.size_le_aleph0_of_isEmpty _ inferInstance).trans hℵ
    | some ab => exact hW ab))

/-- **The ambient scheme of a universal first order thickening of a morphism of schemes of a big
fppf site lies in the site.**  If `Z` and `X` are contained in `B` and `Z ⊂ H` is a universal
first order thickening of `h : Z ⟶ X` in the sense of Stacks 04EX, then `H` is contained in
`B`: its size is bounded by the sizes of `Z` and `X`. -/
theorem _root_.AlgebraicGeometry.Space.contains_ambient_of_isUniversalFirstOrderThickening
    (B : AlgebraicGeometry.BigFppfSite.{u}) {Z X H : Scheme.{u}} (hZ : B.Contains Z)
    (hX : B.Contains X) (h : Z ⟶ X) (i : Z ⟶ H) (p : H ⟶ X)
    (hi : Stacks.Thickenings.IsUniversalFirstOrderThickening h i p) :
    B.Contains H :=
  (bridge_size_le_universalThickening h i p hi).trans_lt (max_lt hZ hX)

/-- **The universal first-order thickening of a morphism of the site is presented by the site.**
Let `q : V ⟶ U` be a morphism of the big fppf category over `S` and `t` a universal first-order
thickening of the underlying morphism of schemes.  Then `q` factors as `i ≫ p` through an object
`V'` of the site whose underlying scheme is the ambient scheme of `t`, the underlying morphisms
of `i` and `p` being the inclusion and the structure morphism of `t`; the underlying morphism of
`i` is a first-order thickening, the range of `yoneda.map i` is a universal first-order
thickening of algebraic spaces over the algebraic space represented by `U`, and the underlying
morphisms of `i` and `p` are a universal first-order thickening of the underlying morphism of
`i ≫ p`.

No size hypothesis on the ambient scheme is needed: the big site contains it by the cardinality
bound behind `AlgebraicGeometry.Space.contains_ambient_of_isUniversalFirstOrderThickening`. -/
lemma exists_site_isUniversalFirstOrderThickening
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V U : AlgebraicGeometry.BigFppfOver B S hS} (q : V ⟶ U)
    (t : Stacks.Thickenings.UniversalFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)) :
    ∃ (V' : AlgebraicGeometry.BigFppfOver B S hS) (i : V ⟶ V') (p : V' ⟶ U),
      i ≫ p = q ∧
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V' = t.ambient ∧
      HEq ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i) t.inclusion ∧
      HEq ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p) t.toBase ∧
      Stacks.Thickenings.IsFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i) ∧
      AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS
        (Subfunctor.range (yoneda.map i)) (AlgebraicGeometry.schemeSpaceMap p) ∧
      Stacks.Thickenings.IsUniversalFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (i ≫ p))
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i)
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p) := by
  have ht : B.Contains t.ambient :=
    contains_ambient_of_isUniversalFirstOrderThickening B V.left.property U.left.property _ _ _
      t.isUniversal
  let F := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let V' : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (t.toBase ≫ U.hom.hom) : B.obj ht ⟶ B.obj hS)
  have hiS : t.inclusion ≫ (t.toBase ≫ U.hom.hom) = V.hom.hom := by
    rw [← Category.assoc, t.isUniversal.inclusion_toBase]
    exact congrArg (fun f => f.hom) q.w
  let i : V ⟶ V' := Over.homMk (ObjectProperty.homMk t.inclusion)
    (by apply ObjectProperty.hom_ext; exact hiS)
  let p : V' ⟶ U := Over.homMk (ObjectProperty.homMk t.toBase) rfl
  have hcomp : i ≫ p = q := F.map_injective t.isUniversal.inclusion_toBase
  have hu : Stacks.Thickenings.IsUniversalFirstOrderThickening
      (F.map (i ≫ p)) (F.map i) (F.map p) := by
    rw [hcomp]
    exact t.isUniversal
  exact ⟨V', i, p, hcomp, rfl, HEq.rfl, HEq.rfl, t.isUniversal.isFirstOrderThickening,
    universalThickening_yoneda_range B S hS i p hu, hu⟩

private noncomputable def chartKernelPair
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z : AlgebraicGeometry.AlgebraicSpaces B S hS}
    {V : AlgebraicGeometry.BigFppfOver B S hS} (a : yoneda.obj V ⟶ Z.1)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a) :
    ChartKernelPair B S hS a := by
  classical
  letI : Limits.HasBinaryProducts (AlgebraicGeometry.BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let hdiag := Z.property.diagonal_representable.of_diag a
  let R := hdiag.pullback a
  let s : R ⟶ V := yoneda.preimage (hdiag.fst a)
  let t : R ⟶ V := hdiag.snd a
  have hK : IsPullback (yoneda.map s) (yoneda.map t) a a := by
    simpa [s, t] using hdiag.isPullback a
  have hRel : IsEquivalenceRelation
      ((Over.post B.inclusion).map s) ((Over.post B.inclusion).map t) :=
    AlgebraicGeometry.Space.isEquivalenceRelation_of_isPullback B S hS a s t hK
  have htEtale : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map t) :=
    ha.property a (yoneda.map s) t hK
  have hsEtale : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s) :=
    ha.property a (yoneda.map t) s hK.flip
  have hTarget : (AlgebraicGeometry.Space.sitePreRelation B S hS s t).target =
      (Over.post B.inclusion).map s := by
    dsimp [AlgebraicGeometry.Space.sitePreRelation, Stacks.Groupoids.PreRelation.target]
    rw [Limits.prod.lift_fst]
  have hSource : (AlgebraicGeometry.Space.sitePreRelation B S hS s t).source =
      (Over.post B.inclusion).map t := by
    dsimp [AlgebraicGeometry.Space.sitePreRelation, Stacks.Groupoids.PreRelation.source]
    rw [Limits.prod.lift_snd]
  have hEtaleRel : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (AlgebraicGeometry.Space.sitePreRelation B S hS s t) := by
    let : IsEquivalenceRelation
        (AlgebraicGeometry.Space.sitePreRelation B S hS s t).target
        (AlgebraicGeometry.Space.sitePreRelation B S hS s t).source := by
      rw [hTarget, hSource]
      exact hRel
    let : Etale (AlgebraicGeometry.Space.sitePreRelation B S hS s t).source.left := by
      rw [hSource]
      simpa [AlgebraicGeometry.BigFppfOver.toScheme, AlgebraicGeometry.BigFppfOver.forget,
        Over.post] using htEtale
    let : Etale (AlgebraicGeometry.Space.sitePreRelation B S hS s t).target.left := by
      rw [hTarget]
      simpa [AlgebraicGeometry.BigFppfOver.toScheme, AlgebraicGeometry.BigFppfOver.forget,
        Over.post] using hsEtale
    exact {}
  exact ⟨R, s, t, hdiag.fst a ≫ a, hK, hEtaleRel⟩

end Stacks.Spaces.UniversalThickening

end
