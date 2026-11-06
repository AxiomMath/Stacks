module

public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependenceComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceSchemeConverse
public import StacksFrontier.RingTheory.Koszul.TorIndependence

/-!
# Tor independence of algebraic spaces along a composition

Let `U ⟶ V ⟶ W` and `W' ⟶ W` be morphisms of algebraic spaces and let `V' = V ×_W W'`. If `V`
and `W'` are Tor independent over `W`, and `U` and `V'` are Tor independent over `V`, then `U`
and `W'` are Tor independent over `W`. This is the statement whose details are omitted in the
proofs of Stacks 0E5E and 0E5F.

## Main results

* `AlgebraicGeometry.Space.torIndependent_comp_of_isPullback`: Tor independence along a
  composition, for algebraic spaces.
* `AlgebraicGeometry.Space.torIndependent_comp_right_of_isPullback`: the same along a
  horizontal composition of cartesian squares.
* `AlgebraicGeometry.Space.TorIndependent.symm`: Tor independence is symmetric.

## Implementation notes

Tor independence of algebraic spaces is checked on a diagram of étale scheme charts (Stacks
08IQ): a chart `W₀` of `W`, charts `V₀`, `X₀` of `V ×_W W₀` and `W' ×_W W₀`, and a chart `U₀` of
`U ×_V V₀`. Over the scheme `V₀ ×_{W₀} X₀`, which is étale over `V'`, the statement is the one
for schemes, `AlgebraicGeometry.TorIndependent.comp_of_isPullback`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_TorIndependenceComp :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_TorIndependenceComp
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- A base change of a surjective morphism of algebraic spaces is surjective, for a cartesian
square of presheaves whose four corners are algebraic spaces. -/
theorem isSurjective_of_isPullback_of_isAlgebraicSpace
    {X' X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hZ : IsAlgebraicSpace B S hS Z) (hY : IsAlgebraicSpace B S hS Y)
    {p : X' ⟶ X} {f' : X' ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y} (h : IsPullback p f' f g)
    (hf : IsSurjective B S hS f) : IsSurjective B S hS f' :=
  isSurjective_of_isPullback B S hS (W := ⟨X', hX'⟩) (Z := ⟨X, hX⟩) (X := ⟨Z, hZ⟩) (Y := ⟨Y, hY⟩)
    (p := ObjectProperty.homMk p) (q := ObjectProperty.homMk f') (g := ObjectProperty.homMk f)
    (f := ObjectProperty.homMk g) (IsPullback.of_map_of_faithful (ObjectProperty.ι _) h) hf

/-- Tor independence of two algebraic spaces over a base is symmetric. -/
theorem TorIndependent.symm {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} {hG : IsAlgebraicSpace B S hS G}
    {hH : IsAlgebraicSpace B S hS H} {f : F ⟶ H} {g : G ⟶ H}
    (h : TorIndependent hF hG hH f g) : TorIndependent hG hF hH g f := by
  intro y x hyx
  obtain ⟨φ, ψ, hφ, hψ, htor⟩ := h x y hyx.symm
  refine ⟨ψ, φ, hψ, hφ, ?_⟩
  let e₁ := eqToHom (congrArg (etaleLocalRing B S hS H) hyx.symm)
  let e₂ := eqToHom (congrArg (etaleLocalRing B S hS H) hyx)
  have he : ∀ r, e₂.hom (e₁.hom r) = r := fun r => by
    change (e₁ ≫ e₂).hom r = r
    simp [e₁, e₂]
  letI : Algebra (etaleLocalRing B S hS H (geometricPointMap f x))
      (etaleLocalRing B S hS F x) := φ.toAlgebra
  letI : Algebra (etaleLocalRing B S hS H (geometricPointMap f x))
      (etaleLocalRing B S hS G y) := ((e₁ ≫ CommRingCat.ofHom ψ).hom).toAlgebra
  letI : Algebra (etaleLocalRing B S hS H (geometricPointMap g y))
      (etaleLocalRing B S hS G y) := ψ.toAlgebra
  letI : Algebra (etaleLocalRing B S hS H (geometricPointMap g y))
      (etaleLocalRing B S hS F x) := ((e₂ ≫ CommRingCat.ofHom φ).hom).toAlgebra
  exact (torIndependent_congr _ _ _ _ _ _ (eqToIso (congrArg (etaleLocalRing B S hS H) hyx.symm)).commRingCatIsoToRingEquiv (RingEquiv.refl _)
    (RingEquiv.refl _) (fun _ => rfl) (fun r => congrArg φ (he r).symm)).mp
    (RingTheory.TorIndependence.TorIndependent.symm htor)

/-- Every algebraic space has an étale surjective chart by a scheme. -/
theorem exists_isEtale_isSurjective_chart {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) :
    ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F), IsEtale B S hS f ∧ IsSurjective B S hS f := by
  obtain ⟨U, f, hfS, hfE⟩ := hF.exists_atlas
  exact ⟨U, f, (isEtale_iff_presheaf_of_yoneda B S hS f).2 hfE,
    isSurjective_of_presheafSurjective B S hS f hfS⟩

/-- For `a : A ⟶ C` and an étale `c : W₀ ⟶ C` of algebraic spaces with `W₀` a scheme chart, the
pullback `A ×_C W₀` is an algebraic space with étale first projection, and has an étale
surjective scheme chart `V₀` whose composite to `A` is étale. -/
private theorem exists_chart_pullback {A C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B S hS A) (hC : IsAlgebraicSpace B S hS C) {W₀ : BigFppfOver B S hS}
    (a : A ⟶ C) (c : yoneda.obj W₀ ⟶ C) (hc : IsEtale B S hS c) :
    IsAlgebraicSpace B S hS (pullback a c) ∧ IsEtale B S hS (pullback.fst a c) ∧
      ∃ (V₀ : BigFppfOver B S hS) (v : yoneda.obj V₀ ⟶ pullback a c) (b : yoneda.obj V₀ ⟶ A)
        (w : V₀ ⟶ W₀), b = v ≫ pullback.fst a c ∧ IsEtale B S hS v ∧ IsSurjective B S hS v ∧
          IsEtale B S hS b ∧ yoneda.map w = v ≫ pullback.snd a c ∧ yoneda.map w ≫ c = b ≫ a := by
  have hP := isAlgebraicSpace_pullback B S hS a c hA (isAlgebraicSpace_yoneda B S hS W₀) hC
  have sq : IsPullback (pullback.fst a c) (pullback.snd a c) a c := IsPullback.of_hasPullback _ _
  have hfst := isEtale_of_isPullback_of_isAlgebraicSpace B S hS sq hP hA
    (isAlgebraicSpace_yoneda B S hS W₀) hC hc
  obtain ⟨V₀, v, hvE, hvS⟩ := exists_isEtale_isSurjective_chart B S hS hP
  refine ⟨hP, hfst, V₀, v, _, yoneda.preimage (v ≫ pullback.snd a c), rfl, hvE, hvS,
    isEtale_comp B S hS hvE hfst, yoneda.map_preimage _, ?_⟩
  rw [yoneda.map_preimage, Category.assoc, ← sq.w, Category.assoc]

/-- **Tor independence along a composition.** Let `U ⟶ V ⟶ W` and `W' ⟶ W` be morphisms of
algebraic spaces and `V' = V ×_W W'`. If `V` and `W'` are Tor independent over `W`, and `U` and
`V'` are Tor independent over `V`, then `U` and `W'` are Tor independent over `W`. -/
theorem torIndependent_comp_of_isPullback {U V W W' V' : AlgebraicSpaces B S hS}
    (p : U ⟶ V) (q : V ⟶ W) (s : W' ⟶ W) (π₁ : V' ⟶ V) (π₂ : V' ⟶ W')
    (sq : IsPullback π₁.hom π₂.hom q.hom s.hom)
    (hqs : TorIndependent V.2 W'.2 W.2 q.hom s.hom)
    (hp : TorIndependent U.2 V'.2 V.2 p.hom π₁.hom) :
    TorIndependent U.2 W'.2 W.2 (p.hom ≫ q.hom) s.hom := by
  have hy := isAlgebraicSpace_yoneda B S hS
  -- a chart of the base
  obtain ⟨W₀, c, hcE, hcS⟩ := exists_isEtale_isSurjective_chart B S hS W.2
  -- a chart of `V ×_W W₀`
  have sqPV : IsPullback (pullback.fst q.hom c) (pullback.snd q.hom c) q.hom c :=
    IsPullback.of_hasPullback _ _
  obtain ⟨hPV, hfstV, V₀, v₁, bV, vw, hbVd, hv₁E, hv₁S, hbV, hvw, hcV⟩ :=
    exists_chart_pullback B S hS V.2 W.2 q.hom c hcE
  -- a chart of `W' ×_W W₀`
  have sqPX : IsPullback (pullback.fst s.hom c) (pullback.snd s.hom c) s.hom c :=
    IsPullback.of_hasPullback _ _
  obtain ⟨hPX, -, X₀, x₁, bX, xw, hbXd, hx₁E, hx₁S, hbX, hxw, hcX⟩ :=
    exists_chart_pullback B S hS W'.2 W.2 s.hom c hcE
  -- a chart of `U ×_V V₀`
  have sqPU : IsPullback (pullback.fst p.hom bV) (pullback.snd p.hom bV) p.hom bV :=
    IsPullback.of_hasPullback _ _
  obtain ⟨hPU, -, U₀, u₁, bU, uv, hbUd, hu₁E, hu₁S, hbU, huv, hcU⟩ :=
    exists_chart_pullback B S hS U.2 V.2 p.hom bV hbV
  -- the scheme `Y₀ = V₀ ×_{W₀} X₀`
  let π₁₀ := pullback.fst vw xw
  let π₂₀ := pullback.snd vw xw
  have sqY₀ : IsPullback (yoneda.map π₁₀) (yoneda.map π₂₀) (yoneda.map vw) (yoneda.map xw) :=
    (IsPullback.of_hasPullback vw xw).map yoneda
  have sqY₀s : IsPullback ((BigFppfOver.toScheme B S hS).map π₁₀)
      ((BigFppfOver.toScheme B S hS).map π₂₀) ((BigFppfOver.toScheme B S hS).map vw)
      ((BigFppfOver.toScheme B S hS).map xw) :=
    (IsPullback.of_hasPullback vw xw).map (BigFppfOver.toScheme B S hS)
  -- its map to `V'`
  have hyw : (yoneda.map π₁₀ ≫ bV) ≫ q.hom = (yoneda.map π₂₀ ≫ bX) ≫ s.hom := by
    rw [Category.assoc, Category.assoc, ← hcV, ← hcX, ← Category.assoc, ← Category.assoc,
      sqY₀.w]
  obtain ⟨y, hy₁, hy₂⟩ : ∃ y : yoneda.obj (pullback vw xw) ⟶ V'.1,
      y ≫ π₁.hom = yoneda.map π₁₀ ≫ bV ∧ y ≫ π₂.hom = yoneda.map π₂₀ ≫ bX :=
    ⟨sq.lift _ _ hyw, sq.lift_fst _ _ _, sq.lift_snd _ _ _⟩
  -- `y` is étale: it is a composite of base changes of `v₁`, `x₁` and `pullback.fst q c`
  have hT := isAlgebraicSpace_pullback B S hS π₁.hom (pullback.fst q.hom c) V'.2 hPV V.2
  have sqT : IsPullback (pullback.fst π₁.hom (pullback.fst q.hom c))
      (pullback.snd π₁.hom (pullback.fst q.hom c)) π₁.hom (pullback.fst q.hom c) :=
    IsPullback.of_hasPullback _ _
  set tf := pullback.fst π₁.hom (pullback.fst q.hom c)
  set ts := pullback.snd π₁.hom (pullback.fst q.hom c)
  have htf : IsEtale B S hS tf :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS sqT hT V'.2 hPV V.2 hfstV
  have hjw : (tf ≫ π₂.hom) ≫ s.hom = (ts ≫ pullback.snd q.hom c) ≫ c := by
    rw [Category.assoc, ← sq.w, ← Category.assoc, sqT.w, Category.assoc, sqPV.w,
      Category.assoc]
  obtain ⟨j, hj₁, hj₂⟩ : ∃ j : pullback π₁.hom (pullback.fst q.hom c) ⟶ pullback s.hom c,
      j ≫ pullback.fst s.hom c = tf ≫ π₂.hom ∧
        j ≫ pullback.snd s.hom c = ts ≫ pullback.snd q.hom c :=
    ⟨pullback.lift _ _ hjw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have sqTj : IsPullback j ts (pullback.snd s.hom c) (pullback.snd q.hom c) := by
    refine IsPullback.of_right ?_ hj₂ sqPX
    rw [hj₁, ← sqPV.w]
    exact sqT.paste_horiz sq.flip
  have hQ := isAlgebraicSpace_pullback B S hS ts v₁ hT (hy V₀) hPV
  have sqQ : IsPullback (pullback.fst ts v₁) (pullback.snd ts v₁) ts v₁ :=
    IsPullback.of_hasPullback _ _
  have hqf : IsEtale B S hS (pullback.fst ts v₁) :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS sqQ hQ hT (hy V₀) hPV hv₁E
  have hew : y ≫ π₁.hom = (yoneda.map π₁₀ ≫ v₁) ≫ pullback.fst q.hom c := by
    rw [hy₁, hbVd, Category.assoc]
  obtain ⟨e, he₁, he₂⟩ : ∃ e : yoneda.obj (pullback vw xw) ⟶ pullback π₁.hom
      (pullback.fst q.hom c), e ≫ tf = y ∧ e ≫ ts = yoneda.map π₁₀ ≫ v₁ :=
    ⟨pullback.lift _ _ hew, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨e₁, he₁₁, he₁₂⟩ : ∃ e₁ : yoneda.obj (pullback vw xw) ⟶ pullback ts v₁,
      e₁ ≫ pullback.fst ts v₁ = e ∧ e₁ ≫ pullback.snd ts v₁ = yoneda.map π₁₀ :=
    ⟨pullback.lift e (yoneda.map π₁₀) he₂, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hej : e ≫ j = yoneda.map π₂₀ ≫ x₁ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hj₁, ← Category.assoc, he₁, hy₂, hbXd, Category.assoc]
    · rw [Category.assoc, hj₂, ← Category.assoc, he₂, Category.assoc, ← hvw,
        sqY₀.w, hxw, Category.assoc]
  have sqe₁ : IsPullback e₁ (yoneda.map π₂₀) (pullback.fst ts v₁ ≫ j) x₁ := by
    refine IsPullback.of_right ?_ (by rw [← Category.assoc, he₁₁, hej])
      (sqQ.paste_horiz sqTj).flip
    rw [he₁₂, ← hvw, ← hxw]
    exact sqY₀
  have he₁E : IsEtale B S hS e₁ :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS sqe₁ (hy _) hQ (hy X₀) hPX hx₁E
  have hyE : IsEtale B S hS y := by
    rw [← he₁, ← he₁₁, Category.assoc]
    exact isEtale_comp B S hS he₁E (isEtale_comp B S hS hqf htf)
  -- Tor independence of the scheme charts
  let spV : AlgebraicSpaces B S hS := ⟨yoneda.obj V₀, hy V₀⟩
  let spX : AlgebraicSpaces B S hS := ⟨yoneda.obj X₀, hy X₀⟩
  let spW : AlgebraicSpaces B S hS := ⟨yoneda.obj W₀, hy W₀⟩
  let spU : AlgebraicSpaces B S hS := ⟨yoneda.obj U₀, hy U₀⟩
  let spY : AlgebraicSpaces B S hS := ⟨yoneda.obj (pullback vw xw), hy _⟩
  have h₁ := (torIndependent_iff_forall_etale_diagram B S hS q s).mp hqs spV spX spW
    (ObjectProperty.homMk bV) (ObjectProperty.homMk bX) (ObjectProperty.homMk c)
    (ObjectProperty.homMk (yoneda.map vw)) (ObjectProperty.homMk (yoneda.map xw))
    hbV hbX hcE hcV hcX
  have h₂ := (torIndependent_iff_forall_etale_diagram B S hS p π₁).mp hp spU spY spV
    (ObjectProperty.homMk bU) (ObjectProperty.homMk y) (ObjectProperty.homMk bV)
    (ObjectProperty.homMk (yoneda.map uv)) (ObjectProperty.homMk (yoneda.map π₁₀))
    hbU hyE hbV hcU hy₁.symm
  have hsch := AlgebraicGeometry.TorIndependent.comp_of_isPullback sqY₀s
    (torIndependent_scheme_of_torIndependent_yoneda B S hS vw xw h₁)
    (torIndependent_scheme_of_torIndependent_yoneda B S hS uv π₁₀ h₂)
  rw [← Functor.map_comp] at hsch
  -- the chart of `U ×_W W₀`
  have hPU' := isAlgebraicSpace_pullback B S hS (p.hom ≫ q.hom) c U.2 (hy W₀) W.2
  have sqPU' : IsPullback (pullback.fst (p.hom ≫ q.hom) c) (pullback.snd (p.hom ≫ q.hom) c)
      (p.hom ≫ q.hom) c := IsPullback.of_hasPullback _ _
  have hmw : (pullback.fst (p.hom ≫ q.hom) c ≫ p.hom) ≫ q.hom =
      pullback.snd (p.hom ≫ q.hom) c ≫ c := by rw [Category.assoc, sqPU'.w]
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m : pullback (p.hom ≫ q.hom) c ⟶ pullback q.hom c,
      m ≫ pullback.fst q.hom c = pullback.fst (p.hom ≫ q.hom) c ≫ p.hom ∧
        m ≫ pullback.snd q.hom c = pullback.snd (p.hom ≫ q.hom) c :=
    ⟨pullback.lift _ _ hmw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have sqm : IsPullback m (pullback.fst (p.hom ≫ q.hom) c) (pullback.fst q.hom c) p.hom := by
    refine IsPullback.of_right ?_ hm₁ sqPV.flip
    rw [hm₂]
    exact sqPU'.flip
  have hkw : pullback.fst p.hom bV ≫ p.hom ≫ q.hom =
      (pullback.snd p.hom bV ≫ yoneda.map vw) ≫ c := by
    rw [← Category.assoc, sqPU.w, Category.assoc, Category.assoc, hcV]
  obtain ⟨k, hk₁, hk₂⟩ : ∃ k : pullback p.hom bV ⟶ pullback (p.hom ≫ q.hom) c,
      k ≫ pullback.fst (p.hom ≫ q.hom) c = pullback.fst p.hom bV ∧
        k ≫ pullback.snd (p.hom ≫ q.hom) c = pullback.snd p.hom bV ≫ yoneda.map vw :=
    ⟨pullback.lift _ _ hkw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hkm : k ≫ m = pullback.snd p.hom bV ≫ v₁ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hm₁, ← Category.assoc, hk₁, sqPU.w, hbVd, Category.assoc]
    · rw [Category.assoc, hm₂, hk₂, hvw, Category.assoc]
  have sqk : IsPullback k (pullback.snd p.hom bV) m v₁ := by
    refine IsPullback.of_right ?_ hkm sqm.flip
    rw [hk₁, ← hbVd]
    exact sqPU
  have hkE : IsEtale B S hS k :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS sqk hPU hPU' (hy V₀) hPV hv₁E
  have hkS : IsSurjective B S hS k :=
    isSurjective_of_isPullback_of_isAlgebraicSpace B S hS hPU (hy V₀) hPU' hPV sqk.flip hv₁S
  -- condition (4) of Stacks 08IQ for the composite
  exact torIndependent_of_torIndependent_scheme_diagram B S hS
    (X := U) (Y := W') (Bs := W) (PX := ⟨_, hPU'⟩) (PY := ⟨_, hPX⟩)
    (ObjectProperty.homMk (p.hom ≫ q.hom)) s c bU (uv ≫ vw) bX xw
    (ObjectProperty.homMk (pullback.fst (p.hom ≫ q.hom) c)) (pullback.snd (p.hom ≫ q.hom) c)
    (ObjectProperty.homMk (pullback.fst s.hom c)) (pullback.snd s.hom c) (u₁ ≫ k) x₁
    sqPU' sqPX (by rw [Category.assoc]; exact (congrArg (u₁ ≫ ·) hk₁).trans hbUd.symm)
    (by rw [Category.assoc, hk₂, ← Category.assoc, ← huv, Functor.map_comp])
    hbXd.symm hxw.symm hcE hcS hbU hbX (isEtale_comp B S hS hu₁E hkE)
    (isSurjective_comp B S hS hu₁S hkS) hx₁E hx₁S hsch

/-- **Tor independence along a horizontal composition.** For a cartesian square
`X' = X ×_Y Y'` with `f : X ⟶ Y` and `h : Y' ⟶ Y` Tor independent, and with the base change
`f' : X' ⟶ Y'` Tor independent of `h' : Y'' ⟶ Y'`, the morphisms `f` and `h ∘ h'` are Tor
independent. -/
theorem torIndependent_comp_right_of_isPullback {X Y Y' Y'' X' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (h : Y' ⟶ Y) (h' : Y'' ⟶ Y') (g : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g.hom f'.hom f.hom h.hom)
    (hfh : TorIndependent X.2 Y'.2 Y.2 f.hom h.hom)
    (hf'h' : TorIndependent X'.2 Y''.2 Y'.2 f'.hom h'.hom) :
    TorIndependent X.2 Y''.2 Y.2 f.hom (h'.hom ≫ h.hom) :=
  (torIndependent_comp_of_isPullback B S hS h' h f f' g sq.flip hfh.symm hf'h'.symm).symm

end AlgebraicGeometry.Space

end
