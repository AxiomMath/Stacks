module

public import StacksFrontier.AlgebraicGeometry.Stacks.ParasiticLisseEtaleVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePrimedFactorizations

/-!
# Arrows between flat objects factor étale-locally through flat arrows

Let `𝒳` be an algebraic stack and let `φ : y ⟶ x` be an arrow between two *flat* objects of `𝒳`
(**Stacks 0787**), lying over a morphism of schemes `V ⟶ U` which need not be flat.  This file
proves that étale-locally on `V` the arrow `φ` factors through arrows lying over *flat* morphisms
of schemes: for every arrow `k : V' ⟶ V` of an étale covering sieve of `V` there are a lift
`κ : y' ⟶ y` of `k`, an object `w` with arrows `π₁ : w ⟶ y` and `π₂ : w ⟶ x` lying over flat
morphisms, and an arrow `χ : y' ⟶ w` with `χ ≫ π₁ = κ` and `χ ≫ π₂ = κ ≫ φ`.

This is the geometric input of **Stacks 07B1** (1)(b) and (2)(b), that the restriction of a module
in `LQCoh^fbc(𝒪_𝒳)` to the flat-fppf site is quasi-coherent: the flat base change property is
only asked along flat arrows, and the factorization reduces an arbitrary arrow between flat objects
to those.

## The construction

Form the 2-fibre product `W = V ×_{y, 𝒳} U` of the 1-morphisms `y : V ⟶ 𝒳` and `x : U ⟶ 𝒳`.  The
arrow `φ` is an object `s` of `W` lying over `V`, namely `(𝟙_V, V ⟶ U, y ≅ x|_V)`.  `W` has a
smooth surjective atlas `U₀ ⟶ W` whose distinguished object `d` has flat `U`-component
(`AlgebraicGeometry.Stack.FlatFppf.exists_primed_atlas`), and its `V`-component is flat too, since
`W ⟶ V` is the base change of the flat `x`.  Along the smooth surjective atlas `s` lifts étale
locally on `V` (**Stacks 06XH**, `AlgebraicGeometry.Stack.exists_etaleCovering_fibre_lift`), and
the two components of the lift followed by the arrow to `d` give `χ`; `π₁` and `π₂` are the two
components of `d` read in `𝒳`.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.exists_flat_factorization`: the factorization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06XH** (2) in the family form: along a surjective smooth 1-morphism of algebraic
stacks, an object of the base lifts over every member of some étale jointly surjective family of
morphisms of schemes into the scheme it lies over.  This is the family underlying the covering
sieve of `AlgebraicGeometry.Stack.exists_etaleCovering_fibre_lift`. -/
theorem exists_etaleFamily_fibre_lift {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hsurj : IsSurjective B S hS f)
    (hsmooth : AlgebraicStacks.IsSmooth B S hS f)
    (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U) :
    ∃ (I : Type (u + 1)) (W : I → B.Schemes) (e : ∀ i, W i ⟶ U.left),
      (∀ i, Etale (B.inclusion.map (e i))) ∧
      (∀ t : B.inclusion.obj U.left, ∃ i, t ∈ Set.range (B.inclusion.map (e i))) ∧
      ∀ i, ∃ (x : 𝒳.val.val.obj) (α : (CatFiberedInGroupoids.homFunctor f.hom).obj x ⟶ y.1),
        𝒴.val.val.p.IsHomLift
          (Over.homMk (e i) : (Over.mk (e i ≫ U.hom) : BigFppfOver B S hS) ⟶ U) α := by
  obtain ⟨T, m, hmsm, hmsurj, z, φ, hφ⟩ :=
    exists_scheme_lift_of_isSurjective_isSmooth B S hS f hsurj hsmooth U y
  obtain ⟨I, W, e, hetale, hjs, hfacs⟩ :=
    exists_etaleRefinement_of_smooth_surjective B m hmsm hmsurj
  refine ⟨I, W, e, hetale, hjs, fun i => ?_⟩
  obtain ⟨c, hc⟩ := hfacs i
  set b : (Over.mk (e i ≫ U.hom) : BigFppfOver B S hS) ⟶ (Over.mk (m ≫ U.hom) :
      BigFppfOver B S hS) := Over.homMk c (by simp [← hc]) with hbdef
  set hm : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U := Over.homMk m rfl with hmdef
  have hb : b ≫ hm = (Over.homMk (e i) : (Over.mk (e i ≫ U.hom) : BigFppfOver B S hS) ⟶ U) :=
    Over.OverMorphism.ext (by simp [hbdef, hmdef, hc])
  have hw : CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p = 𝒳.val.val.p := f.hom.hom.w
  have hzbase : 𝒳.val.val.p.obj z = Over.mk (m ≫ U.hom) := by
    rw [← hw]
    exact IsHomLift.domain_eq 𝒴.val.val.p hm φ
  obtain ⟨z', ρ, hρ⟩ := 𝒳.val.isFiberedInGroupoids.exists_lift b z hzbase
  refine ⟨z', (CatFiberedInGroupoids.homFunctor f.hom).map ρ ≫ φ, ?_⟩
  rw [← hb]
  have h₁ : 𝒴.val.val.p.IsHomLift b ((CatFiberedInGroupoids.homFunctor f.hom).map ρ) :=
    PresheafOfCategories.isHomLift_map_of_comp hw b ρ hρ
  exact IsHomLift.comp 𝒴.val.val.p b hm ((CatFiberedInGroupoids.homFunctor f.hom).map ρ) φ

/-- **Arrows between flat objects factor étale-locally through flat arrows.**  For flat objects
`y`, `x` of an algebraic stack `𝒳` and an arbitrary arrow `φ : y ⟶ x`, there is an étale jointly
surjective family `e i : W i ⟶ V` of morphisms of schemes into the scheme `V` below `y` such that
for every `i` some lift `κ : y' ⟶ y` of `e i` admits a factorization `χ : y' ⟶ w` through an object
`w` carrying arrows `π₁ : w ⟶ y` and `π₂ : w ⟶ x` over flat morphisms of schemes, with
`χ ≫ π₁ = κ` and `χ ≫ π₂ = κ ≫ φ`. -/
theorem exists_flat_factorization (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {y x : 𝒳.val.val.obj} (hy : flatObject B S hS 𝒳.val y) (hx : flatObject B S hS 𝒳.val x)
    (φ : y ⟶ x) :
    ∃ (I : Type (u + 1)) (W : I → B.Schemes) (e : ∀ i, W i ⟶ (𝒳.val.val.p.obj y).left),
      (∀ i, Etale (B.inclusion.map (e i))) ∧
      (∀ t : B.inclusion.obj (𝒳.val.val.p.obj y).left,
        ∃ i, t ∈ Set.range (B.inclusion.map (e i))) ∧
      ∀ i, ∃ (y' w : 𝒳.val.val.obj) (κ : y' ⟶ y) (χ : y' ⟶ w) (π₁ : w ⟶ y) (π₂ : w ⟶ x),
          𝒳.val.val.p.IsHomLift (Over.homMk (e i) : (Over.mk (e i ≫ (𝒳.val.val.p.obj y).hom) :
            BigFppfOver B S hS) ⟶ 𝒳.val.val.p.obj y) κ ∧
          Flat (B.inclusion.map (𝒳.val.val.p.map π₁).left) ∧
          Flat (B.inclusion.map (𝒳.val.val.p.map π₂).left) ∧
          χ ≫ π₁ = κ ∧ χ ≫ π₂ = κ ≫ φ := by
  set p := 𝒳.val.val.p with hp
  have hfib := 𝒳.val.isFiberedInGroupoids
  set V := p.obj y with hV
  set U := p.obj x with hU
  let xF : p.Fiber U := Functor.Fiber.mk (a := x) rfl
  let f₁ : schemeStack.{u, w} B S hS U ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom (objectMorphism B S hS 𝒳.val xF)
  have hf₁ : AlgebraicStacks.IsFlat B S hS f₁ := hx
  let yF : FlatFppf B S hS 𝒳 := ⟨y, hy⟩
  let c := ambientChoiceOfPullbacks B S hS 𝒳
  let yF₀ : p.Fiber V := Functor.Fiber.mk (a := y) rfl
  let F := c.sliceFunctor yF₀
  let G := f₁.hom.hom.toFunctor
  have hG : G = Functor.TwoYoneda.liftFunctor p hfib U xF := rfl
  -- the lift of `x` along an object `a` of `Over U`, and its strongly cartesian arrow to `x`
  let φL : ∀ a : Over U, G.obj a ⟶ x := fun a =>
    (Functor.TwoYoneda.chosenLift p hfib U xF a).φ
  have hφL : ∀ a : Over U, p.IsStronglyCartesian a.hom (φL a) := fun a =>
    (Functor.TwoYoneda.chosenLift p hfib U xF a).isStronglyCartesian
  have hGφ : ∀ {a a' : Over U} (g : a ⟶ a'), G.map g ≫ φL a' = φL a := fun {a a'} g =>
    Functor.IsStronglyCartesian.fac p a'.hom (φL a') (Over.w g).symm (φL a)
  -- the 2-fibre product and its primed atlas
  set T := ambientSquare B S hS f₁ yF with hT
  obtain ⟨U₀, a₀, ha₀sm, ha₀surj, hP⟩ := exists_primed_atlas B S hS f₁ yF
  let d := (CatFiberedInGroupoids.homFunctor a₀.hom).obj (Over.mk (𝟙 U₀))
  -- the object `s` of the 2-fibre product named by `φ`
  let g : V ⟶ U := p.map φ
  have hφg : p.IsHomLift g φ := inferInstance
  have hφLg : p.IsStronglyCartesian g (φL (Over.mk g)) := hφL (Over.mk g)
  obtain ⟨θ, hθ⟩ : ∃ θ : F.obj (Over.mk (𝟙 V)) ⟶ y,
      θ = c.map (𝟙 V) yF₀ := ⟨_, rfl⟩
  have hcV : p.IsHomLift (𝟙 V) θ := hθ ▸
    (c.isStronglyCartesian (𝟙 V) yF₀).toIsHomLift
  have hcφ : p.IsHomLift g (θ ≫ φ) := inferInstance
  obtain ⟨σ, hσ, hσfac⟩ : ∃ σ : F.obj (Over.mk (𝟙 V)) ⟶ G.obj (Over.mk g),
      p.IsHomLift (𝟙 V) σ ∧ σ ≫ φL (Over.mk g) = θ ≫ φ :=
    ⟨Functor.IsStronglyCartesian.map p g (φL (Over.mk g)) (Category.id_comp g).symm (θ ≫ φ),
      Functor.IsStronglyCartesian.map_isHomLift p g (φL (Over.mk g))
        (Category.id_comp g).symm _,
      Functor.IsStronglyCartesian.fac p g (φL (Over.mk g)) (Category.id_comp g).symm _⟩
  have hσiso : IsIso σ := by
    have : p.IsStronglyCartesian (𝟙 V) σ := hfib.isStronglyCartesian_homLift (𝟙 V) σ
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (𝟙 V) σ
  let s : T.pt.val.val.obj :=
    { base := V
      x := Over.mk (𝟙 V)
      y := Over.mk g
      hx := rfl
      hy := rfl
      iso := @asIso _ _ _ _ σ hσiso
      vertical := hσ }
  obtain ⟨I, W, e, he, hjs, hlift⟩ := exists_etaleFamily_fibre_lift B S hS a₀ ha₀surj ha₀sm V
    (Functor.Fiber.mk (a := s) rfl)
  refine ⟨I, W, e, he, hjs, fun i => ?_⟩
  obtain ⟨x₀, α, hα⟩ := hlift i
  set k : (Over.mk (e i ≫ V.hom) : BigFppfOver B S hS) ⟶ V := Over.homMk (e i) with hk
  -- the flatness of the two components of the atlas object `d`
  have hdflat : flatObject B S hS T.pt.val d :=
    flatObject_map B S hS a₀ (AlgebraicStacks.isFlat_of_isSmooth B S hS a₀ ha₀sm)
      ⟨_, AlgebraicStacks.isFlat_of_isSmooth.{u, w} B S hS _
        (smoothObject_schemeStack_id.{u, w} B S hS U₀)⟩
  have hfst : AlgebraicStacks.IsFlat B S hS T.fst :=
    AlgebraicStacks.isFlat_baseChange B S hS f₁ (ambientSliceMorphism B S hS yF) T
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
        (ambientSliceMorphism B S hS yF) f₁) hf₁
  have hdx : Flat ((BigFppfOver.toScheme B S hS).map d.x.hom) :=
    (flatObject_schemeStack_iff.{u, w} B S hS V d.x).1
      (flatObject_map B S hS T.fst hfst ⟨d, hdflat⟩)
  have hdy : Flat ((BigFppfOver.toScheme B S hS).map d.y.hom) :=
    (flatObject_schemeStack_iff.{u, w} B S hS U d.y).1 hP
  -- an arrow lying over a flat morphism of schemes is flat
  have hflat : ∀ {a b : 𝒳.val.val.obj} {A A' : BigFppfOver B S hS} (h : A ⟶ A') (π : a ⟶ b),
      p.IsHomLift h π → Flat ((BigFppfOver.toScheme B S hS).map h) →
        Flat (B.inclusion.map (p.map π).left) := fun h π _ hh => by
    change Flat ((BigFppfOver.toScheme B S hS).map _)
    rw [IsHomLift.fac' p h π]
    simp only [Functor.map_comp]
    infer_instance
  -- the lifted object `s'` and its arrow `e` to the atlas object
  let s' := (CatFiberedInGroupoids.homFunctor a₀.hom).obj x₀
  let eA : s' ⟶ d := (CatFiberedInGroupoids.homFunctor a₀.hom).map
    (Over.homMk x₀.hom (Category.comp_id _) : x₀ ⟶ Over.mk (𝟙 U₀))
  obtain ⟨π₁, hπ₁⟩ : ∃ π₁ : F.obj d.x ⟶ y, π₁ = c.map d.x.hom yF₀ :=
    ⟨_, rfl⟩
  obtain ⟨π₂, hπ₂⟩ : ∃ π₂ : F.obj d.x ⟶ x, π₂ = d.iso.hom ≫ φL d.y := ⟨_, rfl⟩
  refine ⟨F.obj s'.x, F.obj d.x, F.map α.a ≫ θ, F.map eA.a, π₁, π₂, ?_, ?_, ?_, ?_, ?_⟩
  · have h₁ : (Over.forget V).IsHomLift k α.a := TwoFibreProductOver.isHomLift_a α k hα
    have : p.IsHomLift k (F.map α.a) :=
      Functor.isHomLift_map_of_comp_eq (Functor.ChoiceOfPullbacks.sliceFunctor_comp c _) k α.a
    exact @CategoryTheory.IsHomLift.comp_lift_id_right _ _ _ _ p _ _ _ _ _ k (F.map α.a) this θ
      hcV
  · have : p.IsHomLift d.x.hom π₁ := hπ₁ ▸
      (c.isStronglyCartesian d.x.hom yF₀).toIsHomLift
    exact hflat _ π₁ this hdx
  · have hv : p.IsHomLift (𝟙 d.y.left) d.iso.hom := by
      have h := d.vertical
      rw [← d.hy] at h
      exact h
    have : p.IsHomLift d.y.hom (φL d.y) := (hφL d.y).toIsHomLift
    have : p.IsHomLift d.y.hom π₂ := hπ₂ ▸
      @CategoryTheory.IsHomLift.comp_lift_id_left _ _ _ _ p _ _ _ _ _ d.y.hom (φL d.y) this
        d.iso.hom hv
    exact hflat _ π₂ this hdy
  · rw [hπ₁, hθ]
    have h₁ := Functor.ChoiceOfPullbacks.sliceFunctor_map_fac c
      yF₀ α.a
    have h₂ := Functor.ChoiceOfPullbacks.sliceFunctor_map_fac c
      yF₀ eA.a
    simp only at h₁
    exact h₂.trans h₁.symm
  · have hw : F.map eA.a ≫ d.iso.hom = s'.iso.hom ≫ G.map eA.b := eA.w
    have hαw : F.map α.a ≫ σ = s'.iso.hom ≫ G.map α.b := α.w
    have e₁ : F.map eA.a ≫ d.iso.hom ≫ φL d.y = s'.iso.hom ≫ φL s'.y :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φL d.y) hw).trans
        ((Category.assoc _ _ _).trans (congrArg (s'.iso.hom ≫ ·) (hGφ eA.b))))
    have e₂ : (F.map α.a ≫ θ) ≫ φ = s'.iso.hom ≫ φL s'.y :=
      (Category.assoc _ _ _).trans ((congrArg (F.map α.a ≫ ·) hσfac.symm).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φL (Over.mk g)) hαw).trans
          ((Category.assoc _ _ _).trans (congrArg (s'.iso.hom ≫ ·) (hGφ α.b))))))
    rw [hπ₂]
    exact e₁.trans e₂.symm

end AlgebraicGeometry.Stack.FlatFppf
