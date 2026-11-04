module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.LiftCover
public import StacksFrontier.Deformation.Artin.Infinitesimal.ChartCoverPlumbing

/-!
# Classes of lifts along a faithfully flat finitely presented cover

The sheaf condition of Stacks 0DNS for one covering, on isomorphism classes of lifts: for an
algebraic stack `𝒳` locally of finite presentation over `S`, a deformation situation of affines
`i : T ⟶ T'`, an object `x` over `T` and a flat, surjective, locally finitely presented
`k : c' ⟶ T'` with `c = T ×_{T'} c'`, the pullback of classes of lifts of `x` along `i` to
classes of lifts of `x|_c` along `c ⟶ c'` is injective
(`Deformation.Artin.injective_underFiberClassPullback_of_cover`), and its image is the
equalizer of the two pullbacks to `c' ×_{T'} c'`
(`Deformation.Artin.underFiberClassPullback_eq_iff_of_cover`).

These are the class-level forms of `AlgebraicGeometry.Stack.GroupoidLift.exists_hom_of_cover`
and `AlgebraicGeometry.Stack.GroupoidLift.exists_lift_of_cover`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor Limits
open AlgebraicGeometry AlgebraicGeometry.Stack AlgebraicGeometry.Stack.GroupoidLift

namespace Deformation.Artin

universe w u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- A morphism of lifts over the identity gives equal classes. -/
theorem underFiberClass_eq_of_hom {U V : BigFppfOver B S hS} {x : 𝒳.val.obj}
    (hx : 𝒳.val.p.obj x = U) (aa : U ⟶ V)
    (s t : (Under.post 𝒳.val.p).Fiber (Under.mk (eqToHom hx ≫ aa))) (θ : s.1.right ⟶ t.1.right)
    (hθ : 𝒳.val.p.IsHomLift (𝟙 V) θ) (hw : s.1.hom ≫ θ = t.1.hom) :
    (Quotient.mk (isIsomorphicSetoid _) s) = Quotient.mk _ t := by
  have : IsIso θ := 𝒳.isFiberedInGroupoids.isIso_of_isHomLift_id θ hθ
  have hinv : 𝒳.val.p.IsHomLift (𝟙 V) (CategoryTheory.inv θ) := by
    have := IsHomLift.inv 𝒳.val.p (𝟙 V) θ
    simpa using this
  have hw' : t.1.hom ≫ CategoryTheory.inv θ = s.1.hom := by
    rw [IsIso.comp_inv_eq]
    exact hw.symm
  let φ : s ⟶ t := underFiberHomMk 𝒳.val.p hx aa θ hθ hw
  let ψ : t ⟶ s := underFiberHomMk 𝒳.val.p hx aa _ hinv hw'
  exact Quotient.sound ⟨⟨φ, ψ, Functor.Fiber.hom_ext (Under.UnderMorphism.ext (IsIso.hom_inv_id θ)),
    Functor.Fiber.hom_ext (Under.UnderMorphism.ext (IsIso.inv_hom_id θ))⟩⟩

/-- **The pullback of classes of lifts to an fppf cover is injective**, as soon as the spaces of
arrows of the charts of `𝒳` with isomorphic chart objects are locally of finite presentation
(`harr`; this holds when `𝒳 ⟶ S` or the inertia of `𝒳` is locally of finite presentation). -/
theorem injective_underFiberClassPullback_of_cover (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (harr : ArrowSpacesLocallyOfFinitePresentation B S hS 𝒳)
    {T c c' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c')]
    (i : T ⟶ T') (hi : IsDeformationSituation ((BigFppfOver.toScheme B S hS).map i).appTop.hom)
    (j : c ⟶ T) (l : c ⟶ c') (k : c' ⟶ T') (hpb : IsPullback j l i k)
    (hkf : Flat ((BigFppfOver.toScheme B S hS).map k))
    (hks : Surjective ((BigFppfOver.toScheme B S hS).map k))
    (hkp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map k))
    {x y : 𝒳.val.obj} (hx : 𝒳.val.p.obj x = T) (hy : 𝒳.val.p.obj y = c) (α : y ⟶ x)
    (hα : 𝒳.val.p.IsHomLift j α) :
    Function.Injective (underFiberClassPullback 𝒳.val.p 𝒳.isFiberedInGroupoids k hpb.w α hα
      (hx := hx) (hy := hy)) := by
  intro t₁ t₂ h
  obtain ⟨u₁, v₁, hu₁, hv₁, ρ₁, hρ₁, hw₁⟩ :=
    exists_cartesian_underFiberClassPullback 𝒳.val.p 𝒳.isFiberedInGroupoids k hpb.w α hα t₁
  obtain ⟨u₂, v₂, hu₂, hv₂, ρ₂, hρ₂, hw₂⟩ :=
    exists_cartesian_underFiberClassPullback 𝒳.val.p 𝒳.isFiberedInGroupoids k hpb.w α hα t₂
  obtain ⟨e⟩ := Quotient.exact (hv₁.trans (h.trans hv₂.symm))
  have hθv : v₁.1.hom ≫ e.hom.1.right = v₂.1.hom := Under.w e.hom.1
  have hθvl : 𝒳.val.p.IsHomLift (𝟙 c') e.hom.1.right :=
    underPost_isHomLift_right 𝒳.val.p _ e.hom.1 e.hom.2
  have := hρ₁.toIsHomLift
  have := hρ₂.toIsHomLift
  obtain ⟨θ, hθ, hφθ⟩ := exists_hom_of_cover_of_arrSpace h𝒳 harr i hi j l k hpb hkf hks hkp hx α
    hα
    v₁.1.hom (underFiber_isHomLift 𝒳.val.p hy l v₁) u₁.1.hom (underFiber_isHomLift 𝒳.val.p hx i u₁)
    u₂.1.hom (underFiber_isHomLift 𝒳.val.p hx i u₂) ρ₁ inferInstance (e.hom.1.right ≫ ρ₂)
    (GroupoidLift.StackChart.isHomLift_of_eq (Category.id_comp k) inferInstance) hw₁
    (by rw [← Category.assoc, hθv, hw₂])
  rw [← hu₁, ← hu₂]
  exact underFiberClass_eq_of_hom hx i u₁ u₂ θ hθ hφθ

/-- The pullback of classes of lifts only depends on the base square and the arrow. -/
theorem underFiberClassPullback_congr_arrow {U U' V V' : BigFppfOver B S hS} {aa : U ⟶ U'}
    {cc : V ⟶ V'} {bb bb' : V ⟶ U} {D D' : V' ⟶ U'} (hb : bb = bb') (hD : D = D')
    (hsq : bb ≫ aa = cc ≫ D) (hsq' : bb' ≫ aa = cc ≫ D') {x y : 𝒳.val.obj}
    {hx : 𝒳.val.p.obj x = U} {hy : 𝒳.val.p.obj y = V} {φ φ' : y ⟶ x} (hφeq : φ = φ')
    (hφ : 𝒳.val.p.IsHomLift bb φ) (hφ' : 𝒳.val.p.IsHomLift bb' φ')
    (a : Quotient (isIsomorphicSetoid ((Under.post 𝒳.val.p).Fiber (Under.mk (eqToHom hx ≫ aa))))) :
    underFiberClassPullback 𝒳.val.p 𝒳.isFiberedInGroupoids D hsq φ hφ (hy := hy) a =
      underFiberClassPullback 𝒳.val.p 𝒳.isFiberedInGroupoids D' hsq' φ' hφ' (hy := hy) a := by
  subst hb hD hφeq
  rfl

/-- **The classes of lifts over an fppf cover which come from the base are the equalizer of the
two pullbacks to the double overlap**, under the finiteness `harr` of the spaces of arrows of
charts. -/
theorem underFiberClassPullback_eq_iff_of_cover (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (harr : ArrowSpacesLocallyOfFinitePresentation B S hS 𝒳)
    {T c c' c'' c₂ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c')]
    (i : T ⟶ T') (hi : IsDeformationSituation ((BigFppfOver.toScheme B S hS).map i).appTop.hom)
    (j : c ⟶ T) (l : c ⟶ c') (k : c' ⟶ T') (hpb : IsPullback j l i k)
    (hl : IsDeformationSituation ((BigFppfOver.toScheme B S hS).map l).appTop.hom)
    (hkf : Flat ((BigFppfOver.toScheme B S hS).map k))
    (hks : Surjective ((BigFppfOver.toScheme B S hS).map k))
    (hkp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map k))
    (k₁ k₂ : c'' ⟶ c') (hpb₂ : IsPullback k₁ k₂ k k) (j₂ : c₂ ⟶ T) (l₂ : c₂ ⟶ c'')
    (hpb₃ : IsPullback j₂ l₂ i (k₁ ≫ k)) (h₁ h₂ : c₂ ⟶ c) (hh₁ : h₁ ≫ l = l₂ ≫ k₁)
    (hh₂ : h₂ ≫ l = l₂ ≫ k₂) (hh₁j : h₁ ≫ j = j₂) (hh₂j : h₂ ≫ j = j₂)
    {x y y₂ : 𝒳.val.obj} (hx : 𝒳.val.p.obj x = T) (hy : 𝒳.val.p.obj y = c)
    (hy₂ : 𝒳.val.p.obj y₂ = c₂) (α : y ⟶ x) (hα : 𝒳.val.p.IsHomLift j α)
    (γ₁ γ₂ : y₂ ⟶ y) (hγ₁ : 𝒳.val.p.IsHomLift h₁ γ₁) (hγ₂ : 𝒳.val.p.IsHomLift h₂ γ₂)
    (hγ : γ₁ ≫ α = γ₂ ≫ α)
    (t : Quotient (isIsomorphicSetoid ((Under.post 𝒳.val.p).Fiber (Under.mk (eqToHom hy ≫ l))))) :
    underFiberClassPullback 𝒳.val.p 𝒳.isFiberedInGroupoids k₁ hh₁ γ₁ hγ₁ (hy := hy₂) t =
        underFiberClassPullback 𝒳.val.p 𝒳.isFiberedInGroupoids k₂ hh₂ γ₂ hγ₂ (hy := hy₂) t ↔
      ∃ s, underFiberClassPullback 𝒳.val.p 𝒳.isFiberedInGroupoids k hpb.w α hα
        (hx := hx) (hy := hy) s = t := by
  have hp := 𝒳.isFiberedInGroupoids
  constructor
  · induction t using Quotient.ind with
    | _ v =>
    intro heq
    obtain ⟨va', va, hva', hva, ρa, hρa, hwa⟩ :=
      exists_cartesian_underFiberClassPullback 𝒳.val.p hp k₁ hh₁ γ₁ hγ₁ (hy := hy₂)
        (Quotient.mk _ v)
    obtain ⟨vb', vb, hvb', hvb, ρb, hρb, hwb⟩ :=
      exists_cartesian_underFiberClassPullback 𝒳.val.p hp k₂ hh₂ γ₂ hγ₂ (hy := hy₂)
        (Quotient.mk _ v)
    obtain ⟨ea⟩ := Quotient.exact hva'
    obtain ⟨eb⟩ := Quotient.exact hvb'
    obtain ⟨θ⟩ := Quotient.exact (hva.trans (heq.trans hvb.symm))
    have : 𝒳.val.p.IsHomLift (𝟙 c') ea.hom.1.right :=
      underPost_isHomLift_right 𝒳.val.p _ ea.hom.1 ea.hom.2
    have : 𝒳.val.p.IsHomLift (𝟙 c') eb.hom.1.right :=
      underPost_isHomLift_right 𝒳.val.p _ eb.hom.1 eb.hom.2
    have : 𝒳.val.p.IsHomLift (𝟙 c'') θ.hom.1.right :=
      underPost_isHomLift_right 𝒳.val.p _ θ.hom.1 θ.hom.2
    have := hρa.toIsHomLift
    have := hρb.toIsHomLift
    obtain ⟨z, hz, φ, ρ, hφ, hρ, hw⟩ := exists_lift_of_cover_of_arrSpace h𝒳 harr i hi j l k hpb
      hl hkf hks hkp
      k₁ k₂ hpb₂ j₂ l₂ hpb₃ h₁ h₂ hh₁ hh₂ hh₁j hh₂j hx α hα v.1.hom
      (underFiber_isHomLift 𝒳.val.p hy l v) γ₁ γ₂ hγ₁ hγ₂ hγ (ρa ≫ ea.hom.1.right)
      (θ.hom.1.right ≫ ρb ≫ eb.hom.1.right)
      (GroupoidLift.StackChart.isHomLift_of_eq (Category.comp_id k₁) inferInstance)
      (GroupoidLift.StackChart.isHomLift_of_eq (by rw [Category.id_comp, Category.comp_id])
        (inferInstance : 𝒳.val.p.IsHomLift (𝟙 c'' ≫ k₂ ≫ 𝟙 c') _)) va.1.hom
      (underFiber_isHomLift 𝒳.val.p hy₂ l₂ va)
      (by rw [← Category.assoc, hwa, Category.assoc, Under.w ea.hom.1])
      (by rw [← Category.assoc, Under.w θ.hom.1, ← Category.assoc, hwb, Category.assoc,
        Under.w eb.hom.1])
    exact ⟨_, (eq_underFiberClassPullback_of_cartesian 𝒳.val.p hp k hpb.w α hα
      (underFiberObjMk 𝒳.val.p hx i φ hφ) v rfl rfl ρ (hp.isStronglyCartesian_homLift k ρ) hw).symm⟩
  · rintro ⟨s, rfl⟩
    have hsq : ∀ (k' : c'' ⟶ c') (h : c₂ ⟶ c), h ≫ l = l₂ ≫ k' → (h ≫ j) ≫ i = l₂ ≫ k' ≫ k :=
      fun k' h hh ↦ by rw [Category.assoc, hpb.w, ← Category.assoc, hh, Category.assoc]
    rw [← underFiberClassPullback_comp 𝒳.val.p hp k k₁ hpb.w hh₁ α hα γ₁ hγ₁ (hsq k₁ h₁ hh₁)
      inferInstance, ← underFiberClassPullback_comp 𝒳.val.p hp k k₂ hpb.w hh₂ α hα γ₂ hγ₂
      (hsq k₂ h₂ hh₂) inferInstance]
    exact underFiberClassPullback_congr_arrow (hh₁j.trans hh₂j.symm) hpb₂.w _ _ hγ
      inferInstance inferInstance s

section Rows

variable {A A₁ A₂ : Type u} [CommRing A] [CommRing A₁] [CommRing A₂]
  {f₀₁ : A →+* A₁} {a b : A₁ →+* A₂}
  {toS : Spec (.of A) ⟶ S} {toS₁ : Spec (.of A₁) ⟶ S} {toS₂ : Spec (.of A₂) ⟶ S}
  {hA : B.Contains (Spec (.of A))} {hA₁ : B.Contains (Spec (.of A₁))}
  {hA₂ : B.Contains (Spec (.of A₂))}
  {hf₀₁ : Spec.map (CommRingCat.ofHom f₀₁) ≫ toS = toS₁}
  {hfa : Spec.map (CommRingCat.ofHom a) ≫ toS₁ = toS₂}
  {hfb : Spec.map (CommRingCat.ofHom b) ≫ toS₁ = toS₂}
  {x x₁ x₂ : 𝒳.val.obj}
  {hx : 𝒳.val.p.obj x = algebraOver A B S hS toS hA}
  {hx₁ : 𝒳.val.p.obj x₁ = algebraOver A₁ B S hS toS₁ hA₁}
  {hx₂ : 𝒳.val.p.obj x₂ = algebraOver A₂ B S hS toS₂ hA₂}
  {φ₀₁ : x₁ ⟶ x}
  {hφ₀₁ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom f₀₁ B S hS toS toS₁ hA hA₁ hf₀₁) φ₀₁}
  {α β : x₂ ⟶ x₁}
  {hα : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom a B S hS toS₁ toS₂ hA₁ hA₂ hfa) α}
  {hβ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom b B S hS toS₁ toS₂ hA₁ hA₂ hfb) β}
  {M : SiteModule A B} {M₁ : SiteModule A₁ B} {M₂ : SiteModule A₂ B}
  {ψ₀₁ : M.obj ⟶ (ModuleCat.restrictScalars f₀₁).obj M₁.obj}
  {ψa : M₁.obj ⟶ (ModuleCat.restrictScalars a).obj M₂.obj}
  {ψb : M₁.obj ⟶ (ModuleCat.restrictScalars b).obj M₂.obj}

/-- **The rows of lift classes are exact along an fppf cover.** For an algebraic stack locally
of finite presentation over `S`, the row `F(A[M]) → F(A₁[M₁]) ⇉ F(A₂[M₂])` of classes of lifts
is exact as soon as `Spec A₁[M₁] → Spec A[M]` is flat, surjective and locally of finite
presentation, `Spec A₁ = Spec A ×_{Spec A[M]} Spec A₁[M₁]`, `Spec A₂[M₂]` is the double overlap
with reduction `Spec A₂ = Spec A ×_{Spec A[M]} Spec A₂[M₂]`, and `x₂ ⇉ x₁ ⟶ x` commutes. This is
the sheaf condition of Stacks 0DNS for the covering `A[M] → A₁[M₁]`. -/
theorem liftClassRowExact_of_cover (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (f : 𝒳 ⟶ Stack.schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS))))
    (hf : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj (squareZeroOver A B S hS toS M))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj (squareZeroOver A₁ B S hS toS₁ M₁))]
    (hi : IsDeformationSituation ((BigFppfOver.toScheme B S hS).map
      (squareZeroArrow A B S hS toS hA M)).appTop.hom)
    (hl : IsDeformationSituation ((BigFppfOver.toScheme B S hS).map
      (squareZeroArrow A₁ B S hS toS₁ hA₁ M₁)).appTop.hom)
    (hpb : IsPullback (algebraOverMapOfRingHom f₀₁ B S hS toS toS₁ hA hA₁ hf₀₁)
      (squareZeroArrow A₁ B S hS toS₁ hA₁ M₁) (squareZeroArrow A B S hS toS hA M)
      (tangentPullbackBase f₀₁ hf₀₁ ψ₀₁))
    (hkf : Flat ((BigFppfOver.toScheme B S hS).map (tangentPullbackBase f₀₁ hf₀₁ ψ₀₁)))
    (hks : Surjective ((BigFppfOver.toScheme B S hS).map (tangentPullbackBase f₀₁ hf₀₁ ψ₀₁)))
    (hkp : LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (tangentPullbackBase f₀₁ hf₀₁ ψ₀₁)))
    (hpb₂ : IsPullback (P := squareZeroOver A₂ B S hS toS₂ M₂)
      (X := squareZeroOver A₁ B S hS toS₁ M₁) (Y := squareZeroOver A₁ B S hS toS₁ M₁)
      (Z := squareZeroOver A B S hS toS M) (tangentPullbackBase a hfa ψa)
      (tangentPullbackBase b hfb ψb) (tangentPullbackBase f₀₁ hf₀₁ ψ₀₁)
      (tangentPullbackBase f₀₁ hf₀₁ ψ₀₁))
    (hpb₃ : IsPullback (algebraOverMapOfRingHom a B S hS toS₁ toS₂ hA₁ hA₂ hfa ≫
        algebraOverMapOfRingHom f₀₁ B S hS toS toS₁ hA hA₁ hf₀₁)
      (squareZeroArrow A₂ B S hS toS₂ hA₂ M₂) (squareZeroArrow A B S hS toS hA M)
      (tangentPullbackBase a hfa ψa ≫
        tangentPullbackBase f₀₁ hf₀₁ ψ₀₁))
    (hab : algebraOverMapOfRingHom b B S hS toS₁ toS₂ hA₁ hA₂ hfb ≫
        algebraOverMapOfRingHom f₀₁ B S hS toS toS₁ hA hA₁ hf₀₁ =
      algebraOverMapOfRingHom a B S hS toS₁ toS₂ hA₁ hA₂ hfa ≫
        algebraOverMapOfRingHom f₀₁ B S hS toS toS₁ hA hA₁ hf₀₁)
    (hγ : α ≫ φ₀₁ = β ≫ φ₀₁) :
    LiftClassRowExact 𝒳.isFiberedInGroupoids hφ₀₁ hα hβ ψ₀₁ ψa ψb (hx := hx) (hx₁ := hx₁)
      (hx₂ := hx₂) := by
  have harr : ArrowSpacesLocallyOfFinitePresentation B S hS 𝒳 :=
    arrowSpacesLocallyOfFinitePresentation_of_structureMorphism h𝒳 f hf
  refine ⟨injective_underFiberClassPullback_of_cover h𝒳 harr _ hi _ _ _ hpb hkf hks hkp hx hx₁
    φ₀₁ hφ₀₁, fun c₁ ↦ ?_⟩
  exact underFiberClassPullback_eq_iff_of_cover h𝒳 harr _ hi _ _ _ hpb hl hkf hks
    hkp _ _ hpb₂
    _ _ hpb₃ _ _ (tangentPullbackBase_square a hfa ψa) (tangentPullbackBase_square b hfb ψb) rfl
    hab hx hx₁ hx₂ φ₀₁ hφ₀₁ α β hα hβ hγ c₁

end Rows

end Deformation.Artin

end
