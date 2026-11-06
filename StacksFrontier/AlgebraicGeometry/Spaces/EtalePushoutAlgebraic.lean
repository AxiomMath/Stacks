module

public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquareGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothMonomorphismOpenImmersion
import all StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquareGluing

/-!
# Pushouts of algebraic spaces along an open immersion and an étale morphism

Let `S` be a scheme contained in a big fppf site `B`. Let `a : A ⟶ F` be an open immersion and
`b : A ⟶ V` an étale morphism of algebraic spaces over `S`. The pushout `Q = F ⨿_A V`, formed in
the fppf sheaves of sets, is an algebraic space, and the map `F ⨿ V ⟶ Q` is étale and surjective.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_of_isPullback_of_isEtale`: a sheaf receiving an
  epimorphism from an algebraic space whose kernel pair is an algebraic space with étale
  projections is an algebraic space, and the epimorphism is étale and surjective.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_isPushout_of_isOpenImmersion`: the pushout of two
  algebraic spaces along a common open subspace is an algebraic space.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_isPushout_of_isOpenImmersion_of_isEtale`: the
  pushout along an open immersion and an étale morphism is an algebraic space.
* `CategoryTheory.Adhesive.isPushout_of_isPushout_of_isKernelPair`: in an adhesive category the
  kernel pair of the first leg of a pushout along a monomorphism `a : A ⟶ F` is glued from `F`
  and the kernel pair of the second leg of the span, along `A`.

## References

* [Stacks Project, Tag 0AR9](https://stacks.math.columbia.edu/tag/0AR9)
* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Adhesive

variable {C : Type*} [Category* C] [Adhesive C]

/-- In an adhesive category, let `F` be the pushout of `d : D ⟶ K` (a monomorphism) and
`p : D ⟶ A`. If `p` has a section `e` and the leg `s : K ⟶ F` has a section `r` with
`e ≫ d = a ≫ r`, then `K` is the pushout of `a` and `e`. -/
theorem isPushout_of_isPushout_of_sections {D K A F : C} {d : D ⟶ K} {p : D ⟶ A}
    {s : K ⟶ F} {a : A ⟶ F} [Mono d] [Mono a] (h : IsPushout d p s a) (e : A ⟶ D) (r : F ⟶ K)
    (hep : e ≫ p = 𝟙 A) (hrs : r ≫ s = 𝟙 F) (hed : e ≫ d = a ≫ r) :
    IsPushout a e r d := by
  have hr : Mono r := mono_of_mono_fac hrs
  have hlift (c : PullbackCone r d) : (c.snd ≫ p) ≫ a = c.fst := by
    rw [Category.assoc, ← h.w, ← Category.assoc, ← c.condition, Category.assoc, hrs,
      Category.comp_id]
  have hpb : IsPullback a e r d := by
    refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hed.symm (fun c ↦ c.snd ≫ p)
      hlift (fun c ↦ ?_) (fun c m hm₁ hm₂ ↦ ?_))
    · rw [← cancel_mono d, Category.assoc, hed, ← Category.assoc, hlift, c.condition]
    · rw [← hm₂, Category.assoc, hep, Category.comp_id]
  have hpo : IsPushout a e (pushout.inl a e) (pushout.inr a e) := IsPushout.of_hasPushout a e
  have hk : Mono (hpo.desc r d hpb.w) := hpo.desc_mono_of_isPullback hpb
  obtain ⟨k, hk, hik, hjk⟩ : ∃ k : pushout a e ⟶ K, Mono k ∧ pushout.inl a e ≫ k = r ∧
      pushout.inr a e ≫ k = d :=
    ⟨_, hk, hpo.inl_desc _ _ _, hpo.inr_desc _ _ _⟩
  obtain ⟨t, hit, hjt⟩ : ∃ t : pushout a e ⟶ F, pushout.inl a e ≫ t = 𝟙 F ∧
      pushout.inr a e ≫ t = p ≫ a :=
    ⟨hpo.desc (𝟙 F) (p ≫ a) (by rw [← Category.assoc, hep, Category.id_comp,
      Category.comp_id]), hpo.inl_desc _ _ _, hpo.inr_desc _ _ _⟩
  have hks : k ≫ s = t := hpo.hom_ext (by rw [← Category.assoc, hik, hrs, hit])
    (by rw [← Category.assoc, hjk, h.w, hjt])
  have htop : IsPushout (pushout.inr a e) p t a := by
    refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk hjt
      (fun c ↦ pushout.inl a e ≫ c.inl) (fun c ↦ ?_) (fun c ↦ ?_) (fun c m hm₁ _ ↦ ?_))
    · refine hpo.hom_ext ?_ ?_
      · rw [← Category.assoc, hit, Category.id_comp]
      · rw [← Category.assoc, hjt, Category.assoc, ← Category.assoc a, pushout.condition,
          Category.assoc, c.condition, ← Category.assoc e, hep, Category.id_comp]
    · rw [← Category.assoc, pushout.condition, Category.assoc, c.condition, ← Category.assoc,
        hep, Category.id_comp]
    · rw [← hm₁, ← Category.assoc, hit, Category.id_comp]
  have hback : IsPullback (pushout.inr a e) (𝟙 D) k d :=
    IsPullback.of_vert_isIso_mono ⟨by rw [hjk, Category.id_comp]⟩
  have hleft : IsPullback p (𝟙 D) (𝟙 A) p := IsPullback.of_vert_isIso ⟨by simp⟩
  have hcube := ((Adhesive.van_kampen h) (pushout.inr a e) p t a (𝟙 D) k (𝟙 A) (𝟙 F)
    hback hleft ⟨by rw [Category.comp_id, hks]⟩ ⟨by simp⟩ ⟨hjt⟩).mp htop
  have : IsIso k := hcube.1.isIso_snd_of_isIso
  exact hpo.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso k) (by simp) (by simp)
    (by simp [hik]) (by simp [hjk])

/-- **The kernel pair of the first leg of a pushout along a monomorphism.** In an adhesive
category let `Q` be the pushout of a monomorphism `a : A ⟶ F` and a morphism `b : A ⟶ V`, with
first leg `g : F ⟶ Q`. Let `D = A ×_V A` and `K = F ×_Q F` be the two kernel pairs, `δ` and `ε`
their diagonals and `d : D ⟶ K` the map induced by `a`. Then `K` is the pushout of `a` and
`δ`: the kernel pair of `g` is glued from `F` and `A ×_V A` along `A`. -/
theorem isPushout_of_isPushout_of_isKernelPair {A F V Q D K : C} {a : A ⟶ F} {b : A ⟶ V}
    {g : F ⟶ Q} {i : V ⟶ Q} [Mono a] (h : IsPushout a b g i) {p₁ p₂ : D ⟶ A}
    (hD : IsPullback p₁ p₂ b b) {k₁ k₂ : K ⟶ F} (hK : IsPullback k₁ k₂ g g)
    (δ : A ⟶ D) (hδ₁ : δ ≫ p₁ = 𝟙 A) (hδ₂ : δ ≫ p₂ = 𝟙 A)
    (ε : F ⟶ K) (hε₁ : ε ≫ k₁ = 𝟙 F) (hε₂ : ε ≫ k₂ = 𝟙 F)
    (d : D ⟶ K) (hd₁ : d ≫ k₁ = p₁ ≫ a) (hd₂ : d ≫ k₂ = p₂ ≫ a) :
    IsPushout a δ ε d := by
  have hp : IsPullback a b g i := Adhesive.isPullback_of_isPushout_of_mono_left h
  have hw (c : PullbackCone k₁ a) : (c.fst ≫ k₂) ≫ g = (c.snd ≫ b) ≫ i := by
    rw [Category.assoc, ← hK.w, ← Category.assoc, c.condition, Category.assoc, h.w,
      Category.assoc]
  let l (c : PullbackCone k₁ a) : c.pt ⟶ D :=
    hD.lift c.snd (hp.lift (c.fst ≫ k₂) (c.snd ≫ b) (hw c)) (by rw [IsPullback.lift_snd])
  have hback : IsPullback d p₁ k₁ a := by
    refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by rw [hd₁]) l (fun c ↦ ?_)
      (fun c ↦ hD.lift_fst _ _ _) (fun c m hm₁ hm₂ ↦ ?_))
    · refine hK.hom_ext ?_ ?_
      · rw [Category.assoc, hd₁, ← Category.assoc, hD.lift_fst, c.condition]
      · rw [Category.assoc, hd₂, ← Category.assoc, hD.lift_snd, hp.lift_fst]
    · refine hD.hom_ext (by rw [hm₂, hD.lift_fst]) ?_
      rw [hD.lift_snd]
      refine hp.hom_ext ?_ ?_
      · rw [hp.lift_fst, Category.assoc, ← hd₂, ← Category.assoc, hm₁]
      · rw [hp.lift_snd, Category.assoc, ← hD.w, ← Category.assoc, hm₂]
  have hdm : Mono d := hback.mono_fst_of_mono
  have htop : IsPushout d p₂ k₂ a :=
    ((Adhesive.van_kampen h) d p₂ k₂ a p₁ k₁ b g hback hD.flip ⟨hK.w.symm⟩ h.toCommSq
      ⟨hd₂⟩).mpr ⟨hK.flip, hp⟩
  refine isPushout_of_isPushout_of_sections htop δ ε hδ₂ hε₂ ?_
  refine hK.hom_ext ?_ ?_
  · rw [Category.assoc, hd₁, ← Category.assoc, hδ₁, Category.id_comp, Category.assoc, hε₁,
      Category.comp_id]
  · rw [Category.assoc, hd₂, ← Category.assoc, hδ₂, Category.id_comp, Category.assoc, hε₂,
      Category.comp_id]

omit [Adhesive C] in
/-- The two legs of a pushout square are jointly epimorphic. -/
theorem epi_coprodDesc_of_isPushout [HasBinaryCoproducts C] {A F V Q : C} {a : A ⟶ F}
    {b : A ⟶ V} {g : F ⟶ Q} {i : V ⟶ Q} (h : IsPushout a b g i) : Epi (coprod.desc g i) :=
  ⟨fun u v huv ↦ h.hom_ext
    (by simpa only [coprod.inl_desc_assoc] using congrArg (coprod.inl ≫ ·) huv)
    (by simpa only [coprod.inr_desc_assoc] using congrArg (coprod.inr ≫ ·) huv)⟩

/-- In an adhesive category let `Q` be the pushout of a monomorphism `a : A ⟶ F` and
`b : A ⟶ V`, mapping to `H` by `p`, and suppose `A` is the fibre product of `F` and `V` over `H`
with `V ⟶ H` a monomorphism. Then `V` is the fibre product of `Q` and `V` over `H`. -/
theorem isPullback_inr_of_isPushout [HasPullbacks C] {A F V Q H : C} {a : A ⟶ F} {b : A ⟶ V}
    {g : F ⟶ Q} {i : V ⟶ Q} [Mono a] (h : IsPushout a b g i) {f : F ⟶ H} {j : V ⟶ H} [Mono j]
    (hA : IsPullback a b f j) (p : Q ⟶ H) (hgp : g ≫ p = f) (hip : i ≫ p = j) :
    IsPullback i (𝟙 V) p j := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by rw [hip, Category.id_comp])
    (fun c ↦ c.snd) (fun c ↦ ?_) (fun c ↦ Category.comp_id _)
    (fun c m _ hm ↦ by rwa [Category.comp_id] at hm))
  obtain ⟨_, _, _, _, -, -, htop⟩ := (Adhesive.van_kampen h).exists_cube_filling
    (IsPullback.of_hasPullback c.fst g) (IsPullback.of_hasPullback c.fst i)
  refine htop.hom_ext ?_ ?_
  · have hw : pullback.snd c.fst g ≫ f = (pullback.fst c.fst g ≫ c.snd) ≫ j := by
      rw [← hgp, ← Category.assoc, ← pullback.condition, Category.assoc, c.condition,
        Category.assoc]
    have hm₁ := hA.lift_fst _ _ hw
    have hm₂ := hA.lift_snd _ _ hw
    rw [← Category.assoc, ← hm₂, Category.assoc, ← h.w, ← Category.assoc, hm₁,
      ← pullback.condition]
  · have hs : pullback.fst c.fst i ≫ c.snd = pullback.snd c.fst i := by
      rw [← cancel_mono j, Category.assoc, ← c.condition, ← Category.assoc, pullback.condition,
        Category.assoc, hip]
    rw [← Category.assoc, hs, ← pullback.condition]

end CategoryTheory.Adhesive

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Limits of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasLimits_presheaf_etalePushoutAlgebraic :
    HasLimitsOfSize.{u, u} ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_etalePushoutAlgebraic
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Limits of sheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasLimits_sheaf_etalePushoutAlgebraic :
    HasLimitsOfSize.{u, u} (Sheaf (BigFppfOver.topology B S hS) (Type u)) := inferInstance

/-- Pullbacks of sheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_sheaf_etalePushoutAlgebraic
    {X Y Z : Sheaf (BigFppfOver.topology B S hS) (Type u)} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks in slices of sheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_overSheaf_etalePushoutAlgebraic
    {T : Sheaf (BigFppfOver.topology B S hS) (Type u)} {X Y Z : Over T} (f : X ⟶ Z)
    (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Locality on the source along one étale surjection -/

/-- A morphism of algebraic spaces is étale as soon as its composite with an étale surjective
morphism is. -/
theorem isEtale_of_isEtale_comp_of_isSurjective {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) {q : X ⟶ Y} (hq : IsEtale B S hS q)
    (hqs : IsSurjective B S hS q) {f : Y ⟶ Z} (hf : IsEtale B S hS (q ≫ f)) :
    IsEtale B S hS f := by
  let Xs : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Ys : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let Zs : AlgebraicSpaces B S hS := ⟨Z, hZ⟩
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃_ _ : AlgebraicSpaces B S hS⦄ k ↦ IsEtale B S hS k.hom
  let _ : P.IsLocalAtSource (Topology.precoverage.{u, 0} .etale B S hS) :=
    isEtale_isLocalAtSource_etale.{u, 0} B S hS
  have hR : Presieve.ofArrows (fun _ : PUnit.{1} ↦ Xs) (fun _ ↦ (ObjectProperty.homMk q :
      Xs ⟶ Ys)) ∈ Topology.precoverage.{u, 0} .etale B S hS Ys :=
    ⟨PUnit.{1}, _, _, rfl, hY, fun _ ↦ hX, ⟨hY, fun _ ↦ hX, fun _ ↦ hq,
      Set.eq_univ_iff_forall.mpr fun y ↦ Set.mem_iUnion.mpr ⟨⟨⟩, hqs y⟩⟩⟩
  show P (ObjectProperty.homMk f : Ys ⟶ Zs)
  refine MorphismProperty.IsLocalAtSource.of_forall_comp (P := P) hR ?_
  rintro T k ⟨⟩
  exact hf

/-- A morphism of algebraic spaces is locally of finite type as soon as its composite with an
étale surjective morphism is. -/
theorem isLocallyOfFiniteType_of_comp_of_isEtale_of_isSurjective
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) {q : X ⟶ Y} (hq : IsEtale B S hS q)
    (hqs : IsSurjective B S hS q) {f : Y ⟶ Z} (hf : IsLocallyOfFiniteType B S hS (q ≫ f)) :
    IsLocallyOfFiniteType B S hS f := by
  let Xs : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Ys : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let Zs : AlgebraicSpaces B S hS := ⟨Z, hZ⟩
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃_ _ : AlgebraicSpaces B S hS⦄ k ↦ IsLocallyOfFiniteType B S hS k.hom
  let _ : P.IsLocalAtSource (Topology.precoverage.{u, 0} .fppf B S hS) :=
    isLocallyOfFiniteType_isLocalAtSource_fppf.{u, 0} B S hS
  have hR : Presieve.ofArrows (fun _ : PUnit.{1} ↦ Xs) (fun _ ↦ (ObjectProperty.homMk q :
      Xs ⟶ Ys)) ∈ Topology.precoverage.{u, 0} .fppf B S hS Ys :=
    ⟨PUnit.{1}, _, _, rfl, hY, fun _ ↦ hX, isFppfCovering_of_isEtaleCovering B S hS
      ⟨hY, fun _ ↦ hX, fun _ ↦ hq,
        Set.eq_univ_iff_forall.mpr fun y ↦ Set.mem_iUnion.mpr ⟨⟨⟩, hqs y⟩⟩⟩
  show P (ObjectProperty.homMk f : Ys ⟶ Zs)
  refine MorphismProperty.IsLocalAtSource.of_forall_comp (P := P) hR ?_
  rintro T k ⟨⟩
  exact hf

/-- Every point of a binary coproduct of algebraic spaces, formed in the fppf sheaves of sets,
comes from one of the two summands. -/
theorem mem_range_pointsMap_or_of_isColimit_binaryCofan
    {F G H : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hF : IsAlgebraicSpace B S hS F.obj) (hG : IsAlgebraicSpace B S hS G.obj)
    (hH : IsAlgebraicSpace B S hS H.obj) (i : F ⟶ H) (j : G ⟶ H)
    (hc : IsColimit (BinaryCofan.mk i j)) (x : points B S hS H.obj) :
    x ∈ Set.range (pointsMap B S hS F.obj i.hom) ∨
      x ∈ Set.range (pointsMap B S hS G.obj j.hom) := by
  classical
  let J := BigFppfOver.topology B S hS
  let A : ULift.{u} WalkingPair → Sheaf J (Type u) := fun z ↦ pairFunction F G z.down
  let ι : ∀ z, A z ⟶ H := fun z ↦ (BinaryCofan.mk i j).ι.app ⟨z.down⟩
  have hc' : IsColimit (Cofan.mk H ι) :=
    (Cofan.isColimitEquivOfEquiv Equiv.ulift
      (Cofan.mk H fun k ↦ (BinaryCofan.mk i j).ι.app ⟨k⟩)).toFun hc
  have hA : ∀ z, IsAlgebraicSpace B S hS (A z).obj := by
    rintro ⟨z⟩
    cases z
    exacts [hF, hG]
  have hι : ∀ z, IsOpenImmersion B S hS (ι z).hom := fun z ↦
    coproductIncl_isOpenImmersion B S hS A H ι hc' z
  let O : ULift.{u} WalkingPair → Subfunctor H.obj := fun z ↦ Subfunctor.range (ι z).hom
  have ho : ∀ z, IsOpenSubspace B S hS (O z) := fun z ↦
    isOpenSubspace_range_of_isAlgebraicSpace B S hS (hA z) (ι z).hom (hι z)
  have hloc := coproduct_locallySurjective J A ι hc'
  let k : (∐ fun z ↦ (A z).obj) ⟶ (∐ fun z ↦ (O z).toFunctor) :=
    Sigma.desc fun z ↦ Subfunctor.toRange (ι z).hom ≫ Sigma.ι (fun z ↦ (O z).toFunctor) z
  have hfac : k ≫ Sigma.desc (fun z ↦ (O z).ι) = Sigma.desc (fun z ↦ (ι z).hom) := by
    apply Sigma.hom_ext
    intro z
    simp [k, O, Subfunctor.toRange_ι]
  have hcov : IsZariskiCover B S hS (ULift.{u} WalkingPair) O :=
    ⟨ho, Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac⟩
  have hp := (isZariskiCover_iff_iUnion_points B S hS H.obj hH _ O ho).mp hcov
  have hx : x ∈ ⋃ z, Set.range (pointsMap B S hS (O z).toFunctor (O z).ι) :=
    hp ▸ Set.mem_univ x
  obtain ⟨z, y, rfl⟩ := Set.mem_iUnion.mp hx
  have hmono : Mono (ι z).hom := mono_of_isOpenImmersion B S hS _ (hι z)
  obtain ⟨w, rfl⟩ := pointsMap_surjective_of_isIso B S hS (Subfunctor.toRange (ι z).hom) y
  have hw : pointsMap B S hS (O z).toFunctor (O z).ι
      (pointsMap B S hS (A z).obj (Subfunctor.toRange (ι z).hom) w) =
        pointsMap B S hS (A z).obj (ι z).hom w := by
    rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]
  rw [hw]
  rcases z with ⟨z⟩
  cases z
  exacts [Or.inl ⟨w, rfl⟩, Or.inr ⟨w, rfl⟩]

/-- A morphism out of a binary coproduct of algebraic spaces, formed in the fppf sheaves of
sets, is locally of finite type as soon as both of its restrictions are. -/
theorem isLocallyOfFiniteType_of_isColimit_binaryCofan
    {F G H : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F.obj) (hG : IsAlgebraicSpace B S hS G.obj)
    (hH : IsAlgebraicSpace B S hS H.obj) (hZ : IsAlgebraicSpace B S hS Z)
    (i : F ⟶ H) (j : G ⟶ H) (hc : IsColimit (BinaryCofan.mk i j)) (f : H.obj ⟶ Z)
    (hi : IsLocallyOfFiniteType B S hS (i.hom ≫ f))
    (hj : IsLocallyOfFiniteType B S hS (j.hom ≫ f)) :
    IsLocallyOfFiniteType B S hS f := by
  let Hs : AlgebraicSpaces B S hS := ⟨H.obj, hH⟩
  let Zs : AlgebraicSpaces B S hS := ⟨Z, hZ⟩
  let Yi : WalkingPair → AlgebraicSpaces B S hS := fun c ↦
    ⟨(pairFunction F G c).obj, by cases c; exacts [hF, hG]⟩
  let gi : ∀ c, Yi c ⟶ Hs := fun c ↦
    ObjectProperty.homMk ((BinaryCofan.mk i j).ι.app ⟨c⟩).hom
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃_ _ : AlgebraicSpaces B S hS⦄ k ↦ IsLocallyOfFiniteType B S hS k.hom
  let _ : P.IsLocalAtSource (Topology.precoverage.{u, 0} .fppf B S hS) :=
    isLocallyOfFiniteType_isLocalAtSource_fppf.{u, 0} B S hS
  have hopen : ∀ c, IsOpenImmersion B S hS (gi c).hom := fun c ↦
    coproductIncl_isOpenImmersion B S hS (pairFunction F G) H
      (fun c ↦ (BinaryCofan.mk i j).ι.app ⟨c⟩) hc c
  have hR : Presieve.ofArrows Yi gi ∈ Topology.precoverage.{u, 0} .fppf B S hS Hs := by
    refine ⟨WalkingPair, Yi, gi, rfl, hH, fun c ↦ (Yi c).property,
      isFppfCovering_of_isEtaleCovering B S hS ⟨hH, fun c ↦ (Yi c).property,
        fun c ↦ isEtale_of_isOpenImmersion B S hS (hopen c), ?_⟩⟩
    refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
    rcases mem_range_pointsMap_or_of_isColimit_binaryCofan B S hS hF hG hH i j hc x with hx | hx
    · exact Set.mem_iUnion.mpr ⟨.left, hx⟩
    · exact Set.mem_iUnion.mpr ⟨.right, hx⟩
  show P (ObjectProperty.homMk f : Hs ⟶ Zs)
  refine MorphismProperty.IsLocalAtSource.of_forall_comp (P := P) hR ?_
  rintro T k ⟨c⟩
  cases c
  exacts [hi, hj]

/-! ### The quotient of an algebraic space by an étale kernel pair -/

/-- Let `q : Y ⟶ Q` be an epimorphism of fppf sheaves of sets whose source is an algebraic space
and whose kernel pair `R = Y ×_Q Y` is an algebraic space with étale projections. Then `Q` is an
algebraic space, and `q` is étale and surjective. -/
theorem isAlgebraicSpace_of_isPullback_of_isEtale
    {Y Q R : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hY : IsAlgebraicSpace B S hS Y.obj) (hR : IsAlgebraicSpace B S hS R.obj)
    {s t : R ⟶ Y} {q : Y ⟶ Q} [Epi q] (hk : IsPullback s t q q)
    (hs : IsEtale B S hS s.hom) (ht : IsEtale B S hS t.hom) :
    IsAlgebraicSpace B S hS Q.obj ∧ IsEtale B S hS q.hom ∧ IsSurjective B S hS q.hom := by
  classical
  let J := BigFppfOver.topology B S hS
  let E := algebraicSpacesToSheaf B S hS
  obtain ⟨base, hbase, hbaseP⟩ := terminalAlgebraicSpace B S hS
  let Xsp : AlgebraicSpaces B S hS := ⟨Y.obj, hY⟩
  let Rsp : AlgebraicSpaces B S hS := ⟨R.obj, hR⟩
  let qX : Xsp ⟶ base := hbase.from Xsp
  let qR : Rsp ⟶ base := hbase.from Rsp
  let sb : Over.mk qR.hom ⟶ Over.mk qX.hom :=
    Over.homMk s.hom (congrArg (fun m : Rsp ⟶ base ↦ m.hom) (hbase.hom_ext _ _))
  let tb : Over.mk qR.hom ⟶ Over.mk qX.hom :=
    Over.homMk t.hom (congrArg (fun m : Rsp ⟶ base ↦ m.hom) (hbase.hom_ext _ _))
  let _ : (Over.forget base.obj).Full :=
    (Over.equivalenceOfIsTerminal hbaseP).fullyFaithfulFunctor.full
  let rel : PreRelation (Over.mk qR.hom) (Over.mk qX.hom) := prod.lift sb tb
  have htr : rel.target = sb := prod.lift_fst _ _
  have hsr : rel.source = tb := prod.lift_snd _ _
  have hkernelP : IsKernelPair q.hom ((Over.forget base.obj).map sb)
      ((Over.forget base.obj).map tb) := hk.map (sheafToPresheaf J (Type u))
  haveI : HasLimitsOfShape WalkingCospan (Over base) :=
    Over.hasLimitsOfShape_of_isConnected (B := base)
  haveI : HasPullback tb sb := HasLimitsOfShape.has_limit _
  have hrel : IsEquivalenceRelation rel.target rel.source := by
    rw [htr, hsr]
    exact (equivalenceRelation_of_isKernelPair_map (Over.forget base.obj) sb tb q.hom
      hkernelP).isEquivalenceRelation
  have hquotRes := isAlgebraicSpace_quotient_of_etale B S hS rel
    (show IsEtale B S hS rel.source.left by rwa [hsr])
    (show IsEtale B S hS rel.target.left by rwa [htr])
  have hkr : IsKernelPair q (E.map (ObjectProperty.homMk rel.target.left : Rsp ⟶ Xsp))
      (E.map (ObjectProperty.homMk rel.source.left : Rsp ⟶ Xsp)) := by
    rw [htr, hsr]
    exact hk
  let hc := hkr.toCoequalizer (regularEpiOfEpi q)
  let hquotc := quotientSheafIsColimit B S hS rel
  let eqQ : quotientSheaf rel ≅ Q := hquotc.coconePointUniqueUpToIso hc
  have heqQ : (⟨toQuotientSheaf rel⟩ : E.obj Xsp ⟶ _) ≫ eqQ.hom = q :=
    hquotc.comp_coconePointUniqueUpToIso_hom hc WalkingParallelPair.one
  have hQalg : IsAlgebraicSpace B S hS Q.obj :=
    isAlgebraicSpace_of_iso B S hS ((sheafToPresheaf J (Type u)).mapIso eqQ) hquotRes.1
  let W : AlgebraicSpaces B S hS := ⟨Q.obj, hQalg⟩
  let Wquot : AlgebraicSpaces B S hS := ⟨(quotientSheaf rel).obj, hquotRes.1⟩
  let eqW : Wquot ≅ W := ObjectProperty.isoMk _ ((sheafToPresheaf J (Type u)).mapIso eqQ)
  let qW : Xsp ⟶ W := ObjectProperty.homMk q.hom
  let qquot : Xsp ⟶ Wquot := ObjectProperty.homMk (toQuotientSheaf rel)
  have hqq : qquot ≫ eqW.hom = qW := ObjectProperty.hom_ext _ (congrArg (fun k ↦ k.hom) heqQ)
  have hqflat : IsFlat B S hS q.hom := by
    have h := @property_postcomp_iso B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) ↦ IsFlat B S hS k.hom)
      (isFlat_isLocalAtTarget_fpqc.{u, 0} B S hS) _ _ _ qquot eqW hquotRes.2.1
    rwa [hqq] at h
  have hqlfp : IsLocallyOfFinitePresentation B S hS q.hom := by
    have h := @property_postcomp_iso B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) ↦
        IsLocallyOfFinitePresentation B S hS k.hom)
      (isLocallyOfFinitePresentation_isLocalAtTarget_fpqc.{u, 0} B S hS) _ _ _
      qquot eqW hquotRes.2.2
    rwa [hqq] at h
  have hqsurj : IsSurjective B S hS q.hom := by
    intro x
    obtain ⟨y, hy⟩ := ((pointsMap_surjective_of_isIso B S hS eqQ.hom.hom).comp
      (isSurjective_toQuotientSheaf rel)) x
    rw [Function.comp_apply, ← pointsMap_comp_apply,
      show toQuotientSheaf rel ≫ eqQ.hom.hom = q.hom from congrArg (fun k ↦ k.hom) heqQ] at hy
    exact ⟨y, hy⟩
  exact ⟨hQalg, @property_of_fppf_pullback B S hS
    (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) ↦ IsEtale B S hS k.hom)
    (isEtale_isLocalAtTarget_fpqc.{u, 0} B S hS) Rsp Xsp Xsp W
    (ObjectProperty.homMk s.hom) (ObjectProperty.homMk t.hom) qW qW
    (IsPullback.of_map_of_faithful E hk) hqsurj hqflat hqlfp ht, hqsurj⟩

/-! ### The kernel pair of the map out of the coproduct of the two legs -/

/-- Let `Q` be the pushout of a monomorphism `a : A ⟶ F` and a morphism `b : A ⟶ V` of fppf
sheaves of sets, with legs `g` and `i`, and let `K = F ×_Q F` be an algebraic space with étale
projections. If `A`, `F` and `V` are algebraic spaces and `a` and `b` are étale, then the
kernel pair of `F ⨿ V ⟶ Q` is an algebraic space with étale projections. -/
theorem exists_isPullback_coprodDesc_of_isPushout
    {A F V Q K : Sheaf (BigFppfOver.topology B S hS) (Type u)} {a : A ⟶ F} {b : A ⟶ V}
    {g : F ⟶ Q} {i : V ⟶ Q} [Mono a] (h : IsPushout a b g i) {k₁ k₂ : K ⟶ F}
    (hK : IsPullback k₁ k₂ g g) (hA : IsAlgebraicSpace B S hS A.obj)
    (hF : IsAlgebraicSpace B S hS F.obj) (hV : IsAlgebraicSpace B S hS V.obj)
    (hKa : IsAlgebraicSpace B S hS K.obj) (ha : IsEtale B S hS a.hom)
    (hb : IsEtale B S hS b.hom) (hk₁ : IsEtale B S hS k₁.hom) (hk₂ : IsEtale B S hS k₂.hom) :
    ∃ (R : Sheaf (BigFppfOver.topology B S hS) (Type u)) (s t : R ⟶ F ⨿ V),
      IsAlgebraicSpace B S hS R.obj ∧ IsPullback s t (coprod.desc g i) (coprod.desc g i) ∧
        IsEtale B S hS s.hom ∧ IsEtale B S hS t.hom := by
  classical
  let J := BigFppfOver.topology B S hS
  have hi : Mono i := Adhesive.mono_of_isPushout_of_mono_left h
  have hp : IsPullback a b g i := Adhesive.isPullback_of_isPushout_of_mono_left h
  let X := F ⨿ V
  have hX : IsAlgebraicSpace B S hS X.obj :=
    isAlgebraicSpace_binaryCoproduct B S hS hF hV coprod.inl coprod.inr (coprodIsCoprod _ _)
  let q : X ⟶ Q := coprod.desc g i
  let XParts := pairFunction F V
  let mapsQ : ∀ k, XParts k ⟶ Q := fun k ↦ WalkingPair.casesOn k g i
  let RParts : WalkingPair × WalkingPair → Sheaf J (Type u) := fun k ↦
    match k with
    | (.left, .left) => K
    | (.left, .right) => A
    | (.right, .left) => A
    | (.right, .right) => V
  let r₁ : ∀ c d, RParts (c, d) ⟶ XParts c := fun c d ↦
    match c, d with
    | .left, .left => k₁
    | .left, .right => a
    | .right, .left => b
    | .right, .right => 𝟙 _
  let r₂ : ∀ c d, RParts (c, d) ⟶ XParts d := fun c d ↦
    match c, d with
    | .left, .left => k₂
    | .left, .right => b
    | .right, .left => a
    | .right, .right => 𝟙 _
  have hr : ∀ c d, IsPullback (r₁ c d) (r₂ c d) (mapsQ c) (mapsQ d) := by
    intro c d
    cases c <;> cases d
    exacts [hK, hp, hp.flip, IsKernelPair.id_of_mono i]
  let R : Sheaf J (Type u) := ∐ RParts
  have hRParts : ∀ k, IsAlgebraicSpace B S hS (RParts k).obj := by
    rintro ⟨c, d⟩
    cases c <;> cases d
    exacts [hKa, hA, hA, hV]
  have hR : IsAlgebraicSpace B S hS R.obj :=
    isAlgebraicSpace_finiteCoproduct B S hS (fun k ↦ (RParts k).obj) hRParts
      R (Sigma.ι RParts) (coproductIsCoproduct RParts)
  let xs : ∀ c, XParts c ⟶ X := fun c ↦ WalkingPair.casesOn c coprod.inl coprod.inr
  let s : R ⟶ X := Sigma.desc (fun k ↦ r₁ k.1 k.2 ≫ xs k.1)
  let t : R ⟶ X := Sigma.desc (fun k ↦ r₂ k.1 k.2 ≫ xs k.2)
  have hXc : IsColimit (Cofan.mk X xs) := by
    refine (coprodIsCoprod F V).ofIsoColimit (Cocone.ext (Iso.refl _) ?_)
    rintro ⟨c⟩
    cases c <;> simp [xs, Cofan.mk] <;> rfl
  let hpbs : ∀ c : WalkingPair, HasPullback (mapsQ c) q :=
    fun c ↦ HasLimitsOfShape.has_limit (cospan (mapsQ c) q)
  have hkernel : IsPullback s t q q :=
    @IsUniversalColimit.isPullback_prod_of_isColimit
      (Sheaf J (Type u)) _ WalkingPair WalkingPair Q XParts (Cofan.mk X xs)
      (FinitaryExtensive.isVanKampen_finiteCoproducts hXc).isUniversal
      XParts (Cofan.mk X xs)
      (FinitaryExtensive.isVanKampen_finiteCoproducts hXc).isUniversal
      mapsQ mapsQ q q hpbs inferInstance RParts r₁ r₂
      hr (Cofan.mk R (Sigma.ι RParts)) (coproductIsCoproduct RParts)
      (by intro c; cases c
          exacts [coprod.inl_desc g i, coprod.inr_desc g i])
      (by intro c; cases c
          exacts [coprod.inl_desc g i, coprod.inr_desc g i])
  have hxs : ∀ c, IsEtale B S hS (xs c).hom := fun c ↦
    isEtale_of_isOpenImmersion B S hS (coproductIncl_isOpenImmersion B S hS XParts X xs hXc c)
  have hsEt : IsEtale B S hS s.hom := by
    refine isEtale_of_finite_coproduct B S hS hRParts hR hX
      (Sigma.ι RParts) (coproductIsCoproduct RParts) s ?_
    rintro ⟨c, d⟩
    show IsEtale B S hS ((Sigma.ι RParts (c, d) ≫ s).hom)
    simp only [s, Sigma.ι_desc]
    refine isEtale_comp B S hS ?_ (hxs c)
    cases c <;> cases d
    exacts [hk₁, ha, hb, isEtale_of_isIso B S hS (𝟙 V.obj)]
  have htEt : IsEtale B S hS t.hom := by
    refine isEtale_of_finite_coproduct B S hS hRParts hR hX
      (Sigma.ι RParts) (coproductIsCoproduct RParts) t ?_
    rintro ⟨c, d⟩
    show IsEtale B S hS ((Sigma.ι RParts (c, d) ≫ t).hom)
    simp only [t, Sigma.ι_desc]
    refine isEtale_comp B S hS ?_ (hxs d)
    cases c <;> cases d
    exacts [hk₂, hb, ha, isEtale_of_isIso B S hS (𝟙 V.obj)]
  exact ⟨R, s, t, hR, hkernel, hsEt, htEt⟩

/-- An open immersion of fppf sheaves of sets is a monomorphism of sheaves. -/
private theorem mono_of_isOpenImmersion_sheaf
    {A F : Sheaf (BigFppfOver.topology B S hS) (Type u)} {a : A ⟶ F}
    (ha : IsOpenImmersion B S hS a.hom) : Mono a :=
  Functor.mono_of_mono_map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u))
    (mono_of_isOpenImmersion B S hS _ ha)

/-- Let `Q` be the pushout of a monomorphism `a : A ⟶ F` and `b : A ⟶ V` of algebraic spaces
with étale `a` and `b`, and let `K = F ×_Q F` be an algebraic space with étale projections. Then
`Q` is an algebraic space, and `F ⨿ V ⟶ Q` is étale and surjective. -/
private theorem isAlgebraicSpace_of_isPushout_of_isEtale_kernelPair
    {A F V Q K : Sheaf (BigFppfOver.topology B S hS) (Type u)} {a : A ⟶ F} {b : A ⟶ V}
    {g : F ⟶ Q} {i : V ⟶ Q} [Mono a] (h : IsPushout a b g i) {k₁ k₂ : K ⟶ F}
    (hK : IsPullback k₁ k₂ g g) (hA : IsAlgebraicSpace B S hS A.obj)
    (hF : IsAlgebraicSpace B S hS F.obj) (hV : IsAlgebraicSpace B S hS V.obj)
    (hKa : IsAlgebraicSpace B S hS K.obj) (ha : IsEtale B S hS a.hom)
    (hb : IsEtale B S hS b.hom) (hk₁ : IsEtale B S hS k₁.hom) (hk₂ : IsEtale B S hS k₂.hom) :
    IsAlgebraicSpace B S hS Q.obj ∧ IsEtale B S hS (coprod.desc g i).hom ∧
      IsSurjective B S hS (coprod.desc g i).hom := by
  obtain ⟨R, s, t, hR, hker, hs, ht⟩ :=
    exists_isPullback_coprodDesc_of_isPushout B S hS h hK hA hF hV hKa ha hb hk₁ hk₂
  have : Epi (coprod.desc g i) := Adhesive.epi_coprodDesc_of_isPushout h
  exact isAlgebraicSpace_of_isPullback_of_isEtale B S hS
    (isAlgebraicSpace_binaryCoproduct B S hS hF hV coprod.inl coprod.inr (coprodIsCoprod _ _))
    hR hker hs ht

/-! ### Glueing along open subspaces -/

/-- **Glueing two algebraic spaces along a common open subspace.** Let `a : A ⟶ F` and
`e : A ⟶ D` be open immersions of algebraic spaces over `S`, and let `P` be their pushout in the
fppf sheaves of sets. Then `P` is an algebraic space, and `F ⨿ D ⟶ P` is étale and surjective. -/
theorem isAlgebraicSpace_of_isPushout_of_isOpenImmersion
    {A F D P : Sheaf (BigFppfOver.topology B S hS) (Type u)} {a : A ⟶ F} {e : A ⟶ D}
    {g : F ⟶ P} {j : D ⟶ P} (h : IsPushout a e g j) (hA : IsAlgebraicSpace B S hS A.obj)
    (hF : IsAlgebraicSpace B S hS F.obj) (hD : IsAlgebraicSpace B S hS D.obj)
    (ha : IsOpenImmersion B S hS a.hom) (he : IsOpenImmersion B S hS e.hom) :
    IsAlgebraicSpace B S hS P.obj ∧ IsEtale B S hS (coprod.desc g j).hom ∧
      IsSurjective B S hS (coprod.desc g j).hom := by
  have : Mono a := mono_of_isOpenImmersion_sheaf B S hS ha
  have : Mono e := mono_of_isOpenImmersion_sheaf B S hS he
  have : Mono g := Adhesive.mono_of_isPushout_of_mono_left h.flip
  have hetid := isEtale_of_isIso B S hS (𝟙 F.obj)
  exact isAlgebraicSpace_of_isPushout_of_isEtale_kernelPair B S hS h (IsKernelPair.id_of_mono g)
    hA hF hD hF (isEtale_of_isOpenImmersion B S hS ha) (isEtale_of_isOpenImmersion B S hS he)
    hetid hetid

/-! ### Pushouts along an open immersion and an étale morphism -/

/-- **The pushout of an open immersion and an étale morphism is an algebraic space.** Let
`a : A ⟶ F` be an open immersion and `b : A ⟶ V` an étale morphism of algebraic spaces over
`S`, and let `Q` be their pushout in the fppf sheaves of sets, with legs `g : F ⟶ Q` and
`i : V ⟶ Q`. Then `Q` is an algebraic space, and `F ⨿ V ⟶ Q` is étale and surjective. -/
theorem isAlgebraicSpace_of_isPushout_of_isOpenImmersion_of_isEtale
    {A F V Q : Sheaf (BigFppfOver.topology B S hS) (Type u)} {a : A ⟶ F} {b : A ⟶ V}
    {g : F ⟶ Q} {i : V ⟶ Q} (h : IsPushout a b g i) (hA : IsAlgebraicSpace B S hS A.obj)
    (hF : IsAlgebraicSpace B S hS F.obj) (hV : IsAlgebraicSpace B S hS V.obj)
    (ha : IsOpenImmersion B S hS a.hom) (hb : IsEtale B S hS b.hom) :
    IsAlgebraicSpace B S hS Q.obj ∧ IsEtale B S hS (coprod.desc g i).hom ∧
      IsSurjective B S hS (coprod.desc g i).hom := by
  let J := BigFppfOver.topology B S hS
  have : Mono a := mono_of_isOpenImmersion_sheaf B S hS ha
  have haEt : IsEtale B S hS a.hom := isEtale_of_isOpenImmersion B S hS ha
  have hDalg : IsAlgebraicSpace B S hS (pullback b.hom b.hom) :=
    isAlgebraicSpace_pullback B S hS b.hom b.hom hA hA hV
  let D : Sheaf J (Type u) := ⟨pullback b.hom b.hom, hDalg.isSheaf⟩
  let p₁ : D ⟶ A := ObjectProperty.homMk (pullback.fst b.hom b.hom)
  let p₂ : D ⟶ A := ObjectProperty.homMk (pullback.snd b.hom b.hom)
  have hD : IsPullback p₁ p₂ b b :=
    IsPullback.of_map_of_faithful (sheafToPresheaf J (Type u))
      (IsPullback.of_hasPullback b.hom b.hom)
  let δ : A ⟶ D := ObjectProperty.homMk (pullback.diagonal b.hom)
  have hδ₁ : δ ≫ p₁ = 𝟙 A := ObjectProperty.hom_ext _ (pullback.diagonal_fst b.hom)
  have hδ₂ : δ ≫ p₂ = 𝟙 A := ObjectProperty.hom_ext _ (pullback.diagonal_snd b.hom)
  have hδ : IsOpenImmersion B S hS δ.hom :=
    isOpenImmersion_diagonal_of_isUnramified B S hS hA hV b.hom
      (isUnramified_of_isEtale B S hS hb)
  have hp₁ : IsEtale B S hS p₁.hom := isEtale_sheafPullback B S hS hDalg hA hA hV _ _ _ _
    hD.flip hb
  have hp₂ : IsEtale B S hS p₂.hom := isEtale_sheafPullback B S hS hDalg hA hA hV _ _ _ _
    hD hb
  let K := pullback g g
  let d : D ⟶ K := pullback.lift (p₁ ≫ a) (p₂ ≫ a) (by
    rw [Category.assoc, h.w, ← Category.assoc, hD.w, Category.assoc, ← h.w, Category.assoc])
  have hglue : IsPushout a δ (pullback.diagonal g) d :=
    Adhesive.isPushout_of_isPushout_of_isKernelPair h hD (IsPullback.of_hasPullback g g) δ hδ₁
      hδ₂ (pullback.diagonal g) (pullback.diagonal_fst g) (pullback.diagonal_snd g) d
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  obtain ⟨hKalg, hqK, hqKs⟩ := isAlgebraicSpace_of_isPushout_of_isOpenImmersion B S hS hglue
    hA hF hDalg ha hδ
  have hFD : IsAlgebraicSpace B S hS (F ⨿ D).obj :=
    isAlgebraicSpace_binaryCoproduct B S hS hF hDalg coprod.inl coprod.inr (coprodIsCoprod _ _)
  have hk (k : K ⟶ F) (hεk : pullback.diagonal g ≫ k = 𝟙 F) (p : D ⟶ A)
      (hdk : d ≫ k = p ≫ a) (hp : IsEtale B S hS p.hom) : IsEtale B S hS k.hom := by
    refine isEtale_of_isEtale_comp_of_isSurjective B S hS hFD hKalg hF hqK hqKs ?_
    refine isEtale_binaryCoproduct_desc B S hS hF hDalg hFD hF coprod.inl coprod.inr
      (coprodIsCoprod _ _) (coprod.desc (pullback.diagonal g) d ≫ k) ?_ ?_
    · show IsEtale B S hS ((coprod.inl ≫ coprod.desc (pullback.diagonal g) d ≫ k).hom)
      rw [coprod.inl_desc_assoc, hεk]
      exact isEtale_of_isIso B S hS (𝟙 F.obj)
    · show IsEtale B S hS ((coprod.inr ≫ coprod.desc (pullback.diagonal g) d ≫ k).hom)
      rw [coprod.inr_desc_assoc, hdk]
      exact isEtale_comp B S hS hp haEt
  have hk₁ := hk (pullback.fst g g) (pullback.diagonal_fst g) p₁ (pullback.lift_fst _ _ _) hp₁
  have hk₂ := hk (pullback.snd g g) (pullback.diagonal_snd g) p₂ (pullback.lift_snd _ _ _) hp₂
  exact isAlgebraicSpace_of_isPushout_of_isEtale_kernelPair B S hS h
    (IsPullback.of_hasPullback g g) hA hF hV hKalg haEt hb hk₁ hk₂

end AlgebraicGeometry.Space

end
