module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackLiftPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.LiftArrowUniqueness

/-!
# Descent of lifts along a covering at a chart point

Let `𝒳` be a stack in groupoids with a chart `(a, ι)` over the affine object `T'`,
`A' = Γ(T', ⊤)`, `I ⊆ A'` a square-zero ideal, `C'` a faithfully flat finitely presented
`A'`-algebra, and `x̄` an object over `Spec (A' ⧸ I)` which, over `Spec (C' ⧸ I C')`, comes from
a chart point `ū` (`c : ξ ū ⟶ x̄`) at which the arrows have a formally étale chart.

* **Effectivity.** A lift `ξ u` of `ξ ū` over `C'` whose two pullbacks to `C' ⊗ C'` are
  identified by an arrow lifting the descent arrow of `x̄` comes from a lift of `x̄` over `A'`
  (`AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_lift_of_chartLift`). This is the
  exactness in the middle of the sheaf condition of Stacks 0DNS for the covering
  `A' → C'`: the arrow is the isomorphism of the two pullbacks of a lift class, and it is
  corrected to an exact cocycle by the second-order step before it descends.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory Opposite Limits
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe w u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} {a : schemeFibredCategory B S hS U₀ ⟶ 𝒳}
  {P : SmallAlg (ringOf B S hS T') B.cutoff} {ι : specOver P ⟶ U₀}

namespace StackChart

variable (hA : Cardinal.mk (ringOf B S hS T') < B.cutoff) {C' : Type u} [CommRing C']
  [Algebra (ringOf B S hS T') C'] (hC : Cardinal.mk C' < B.cutoff) (I : Ideal (ringOf B S hS T'))
  (hI : I ^ 2 = ⊥)

/-- **Effective descent of a lift at a chart point.** A point `u : P → C'` lifting `ū` and an
arrow `ξ (v₀ ∘ u) ⟶ ξ (vₗ ∘ u)` over `Spec (C' ⊗ C')` lifting the descent arrow of `x̄` give an
object `x'` over `Spec A'` with a morphism `φ : x̄ ⟶ x'` over `Spec (A' ⧸ I) ⟶ Spec A'` (a lift of
`x̄`) and a morphism `ζ : ξ u ⟶ x'` over `Spec C' ⟶ Spec A'` through which `c ≫ φ` factors: the
pullback of the lift `x'` to `C'` is the lift `ξ u`. -/
theorem exists_lift_of_chartLift
    (h𝒳 : 𝒳.val.p.IsStackInGroupoids.{w} (BigFppfOver.topology B S hS))
    [Module.FaithfullyFlat (ringOf B S hS T') C'] [Algebra.FinitePresentation (ringOf B S hS T') C']
    [Module.FinitePresentation P.obj Ω[P.obj⁄ringOf B S hS T']]
    {Q : Type u} [CommRing Q] [Algebra (ringOf B S hS T') Q]
    [Module.FinitePresentation Q Ω[Q⁄ringOf B S hS T']]
    (b : Chart (stackArr a ι) Q) (hb : b.IsFormallyEtale) (sV tV : P.obj →ₐ[ringOf B S hS T'] Q)
    (hsV : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q →ₐ[ringOf B S hS T'] D.obj),
      (b.app D v).src = v.comp sV)
    (htV : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q →ₐ[ringOf B S hS T'] D.obj),
      (b.app D v).tgt = v.comp tV)
    {xb : 𝒳.val.obj} (hxb : 𝒳.val.p.obj xb = specOver (red I (baseAlg (κ := B.cutoff) hA)))
    (u : P.obj →ₐ[ringOf B S hS T'] (descNerve T' hC 0).obj)
    (c : ξ a ι ((qC hC I hI).hom.hom.comp u) ⟶ xb)
    (hc : 𝒳.val.p.IsHomLift (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot) c)
    (εbar : Q →ₐ[ringOf B S hS T'] (red I (descNerve T' hC 0)).obj)
    (hε : b.app _ εbar = Arr.idt ((qC hC I hI).hom.hom.comp u))
    (hom : ξ a ι ((descV₀ T' hC).hom.hom.comp u) ⟶ ξ a ι ((descVₗ T' hC).hom.hom.comp u))
    [hl : 𝒳.val.p.IsHomLift (𝟙 (specOver (descNerve T' hC 1))) hom]
    (hrq : haveI := hc
      Arr.map a ι (qC₁ hC I hI) (descArr u hom) = chartRbar (hA := hA) hC I _ c) :
    ∃ (x' : 𝒳.val.obj) (ζ : ξ a ι u ⟶ x') (φ : xb ⟶ x'),
      𝒳.val.p.IsHomLift (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ ∧
        𝒳.val.p.IsHomLift (specOverMap (thk I hI (baseAlg (κ := B.cutoff) hA)).q) φ ∧
          c ≫ φ = trans a ι (qC hC I hI) u ≫ ζ := by
  have := hc
  let D := chartNerveDatumOfLift hA hC I hI _ c u rfl
  have hcoc : D.IsCocycle := chartRbar_cocycle hC I _ c
  obtain ⟨ε₀, ⟨hε₀, -⟩, -⟩ := hb _ _ (thk I hI (descNerve T' hC 0)).q
    (thk I hI (descNerve T' hC 0)).surj (thk I hI (descNerve T' hC 0)).sq εbar (Arr.idt D.u₀)
    ((Arr.map_idt _ _).trans ((congrArg Arr.idt D.u₀_lift).trans hε.symm))
  obtain ⟨r', hs', ht', hq', hd⟩ := NerveDatum.exists_cocycle_of_lift (D := D) sV tV εbar hsV htV
    hε hb (u := u) rfl ε₀ hε₀ (r := descArr u hom) rfl rfl hrq hcoc
  obtain ⟨_, hcocy⟩ := NerveDatum.cocycle_of_defectH r' hs' ht' hd
  obtain ⟨src, tgt, hom', lift'⟩ := r'
  change src = _ at hs'
  change tgt = _ at ht'
  subst hs' ht'
  obtain ⟨x', ζ, hζl, hζ⟩ := exists_descent_of_hom hA u hom' h𝒳 hcocy
  have hx' : 𝒳.val.p.obj x' = specOver (baseAlg (κ := B.cutoff) hA) :=
    @IsHomLift.codomain_eq _ _ _ _ 𝒳.val.p _ _ _ _ (specOverMap (baseMap B.aleph0_lt_cutoff hC hA))
      ζ hζl
  have := hζl
  have hζ' : 𝒳.val.p.IsHomLift (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫
      specOverMap (thk I hI (baseAlg (κ := B.cutoff) hA)).q) (trans a ι (qC hC I hI) u ≫ ζ) :=
    isHomLift_of_eq (spec_baseMap_q hA hC I hI) inferInstance
  have hρ := Arr.hom_eq_of_eq hq'.symm
  obtain ⟨φ, hφ, hcφ⟩ := exists_hom_of_chart (baseThk B.aleph0_lt_cutoff hC hI hA).bot (rV₀ hC I)
    (rVₗ hC I) h𝒳 (isPullback_specOverMap_of_isPushout _ _ _ _
      (isPushout_red_nerve_one B.aleph0_lt_cutoff C' hC I hI hA)) (ofArrows_red_mem hA hC I hI)
    (specOverMap (thk I hI (baseAlg (κ := B.cutoff) hA)).q) hxb hx' _ c hc
    (trans a ι (qC hC I hI) u ≫ ζ) hζ' (chartRbar hC I _ c).hom (chartRbar hC I _ c).lift
    (chartRbar_fac hC I _ c) (red_descArr_fac u hom' ζ hζ _ _ _ hρ)
  exact ⟨x', ζ, φ, hζl, hφ, hcφ⟩

section Canonical

variable {hA} {hC} (u : P.obj →ₐ[ringOf B S hS T'] (descNerve T' hC 0).obj) {x' : 𝒳.val.obj}
  (ζ : ξ a ι u ⟶ x') [hζ : 𝒳.val.p.IsHomLift (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ]

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- Any two morphisms from the base algebra `A'` to an `A'`-algebra `N` are equal. -/
theorem baseAlg_hom_ext {N : SmallAlg (ringOf B S hS T') B.cutoff}
    (k k' : baseAlg (κ := B.cutoff) hA ⟶ N) : k = k' :=
  ObjectProperty.hom_ext _ (CommAlgCat.hom_ext (AlgHom.ext fun x ↦
    (k.hom.hom.commutes x).trans (k'.hom.hom.commutes x).symm))

variable (hA) in
/-- The two projections `Spec (C' ⊗ C') ⟶ Spec C'` agree after composition with
`Spec C' ⟶ Spec A'`. -/
theorem spec_descV_base :
    specOverMap (descVₗ T' hC) ≫ specOverMap (baseMap B.aleph0_lt_cutoff hC hA) =
      specOverMap (descV₀ T' hC) ≫ specOverMap (baseMap B.aleph0_lt_cutoff hC hA) :=
  (isPullback_descV hC hA).w.symm

/-- **The descent arrow of a lift** `ζ : ξ u ⟶ x'` over `Spec C' ⟶ Spec A'`: the canonical arrow
between its two pullbacks to `Spec (C' ⊗ C')`. -/
noncomputable def liftArr : Arr a ι (descNerve T' hC 1) :=
  canArr (specOverMap (descV₀ T' hC) ≫ specOverMap (baseMap B.aleph0_lt_cutoff hC hA))
    ((descV₀ T' hC).hom.hom.comp u) ((descVₗ T' hC).hom.hom.comp u)
    (trans a ι (descV₀ T' hC) u ≫ ζ) (trans a ι (descVₗ T' hC) u ≫ ζ) inferInstance
    (isHomLift_of_eq (spec_descV_base hA) inferInstance)

/-- The descent arrow of `ζ`, followed by the second pullback of `ζ` to `Spec (C' ⊗ C')`, is the
first pullback of `ζ`. -/
theorem liftArr_fac : (liftArr u ζ).hom ≫ trans a ι (descVₗ T' hC) u ≫ ζ =
    trans a ι (descV₀ T' hC) u ≫ ζ :=
  canArr_fac _ _ _ _ _

variable (hA) in
/-- For every face map `Spec (C' ⊗ C' ⊗ C') ⟶ Spec (C' ⊗ C')`, its composite with the first
projection to `Spec C'` and with `Spec C' ⟶ Spec A'` is the same morphism to `Spec A'`. -/
theorem liftArr_face_base (i : Fin 3) :
    specOverMap (descFace T' hC i) ≫ specOverMap (descV₀ T' hC) ≫
        specOverMap (baseMap B.aleph0_lt_cutoff hC hA) =
      specOverMap (descFace T' hC 1) ≫ specOverMap (descV₀ T' hC) ≫
        specOverMap (baseMap B.aleph0_lt_cutoff hC hA) :=
  (congrArg (specOverMap (descFace T' hC i) ≫ ·) (specOverMap_comp _ _).symm).trans
    ((specOverMap_comp _ _).symm.trans ((congrArg specOverMap (baseAlg_hom_ext _ _)).trans
      ((specOverMap_comp _ _).trans (congrArg (specOverMap (descFace T' hC 1) ≫ ·)
        (specOverMap_comp _ _)))))

/-- The pullback of the descent arrow of `ζ` along the `i`-th face map to
`Spec (C' ⊗ C' ⊗ C')` is the canonical arrow between the corresponding pullbacks of `ζ`. -/
theorem liftArr_map (i : Fin 3) :
    Arr.map a ι (descFace T' hC i) (liftArr u ζ) =
      canArr (specOverMap (descFace T' hC 1) ≫ specOverMap (descV₀ T' hC) ≫
          specOverMap (baseMap B.aleph0_lt_cutoff hC hA))
        ((descFace T' hC i).hom.hom.comp ((descV₀ T' hC).hom.hom.comp u))
        ((descFace T' hC i).hom.hom.comp ((descVₗ T' hC).hom.hom.comp u))
        (trans a ι (descFace T' hC i) _ ≫ trans a ι (descV₀ T' hC) u ≫ ζ)
        (trans a ι (descFace T' hC i) _ ≫ trans a ι (descVₗ T' hC) u ≫ ζ)
        (isHomLift_of_eq (liftArr_face_base hA i) inferInstance)
        (isHomLift_of_eq ((congrArg (specOverMap (descFace T' hC i) ≫ ·)
          (spec_descV_base hA)).trans (liftArr_face_base hA i)) inferInstance) := by
  have h₂ := isHomLift_of_eq (spec_descV_base hA) (inferInstance :
    𝒳.val.p.IsHomLift (specOverMap (descVₗ T' hC) ≫
      specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) (trans a ι (descVₗ T' hC) u ≫ ζ))
  exact (map_canArr _ _ _ _ _ _ inferInstance inferInstance).trans
    (canArr_base_congr (liftArr_face_base hA i) _ _ _ _)

/-- `trans_square`, post-composed with a morphism `c`. -/
private theorem trans_square_comp_assoc {C D D' E : SmallAlg (ringOf B S hS T') B.cutoff}
    (h : C ⟶ D) (g : D ⟶ E) (h' : C ⟶ D') (g' : D' ⟶ E) (e : h ≫ g = h' ≫ g')
    (w : P.obj →ₐ[ringOf B S hS T'] C.obj)
    (hX : ξ a ι (g.hom.hom.comp (h.hom.hom.comp w)) = ξ a ι (g'.hom.hom.comp (h'.hom.hom.comp w)))
    {Z : 𝒳.val.obj} (c : ξ a ι w ⟶ Z) :
    trans a ι g (h.hom.hom.comp w) ≫ trans a ι h w ≫ c =
      eqToHom hX ≫ trans a ι g' (h'.hom.hom.comp w) ≫ trans a ι h' w ≫ c :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ c) (trans_square h g h' g' e w hX)).trans
    ((Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _))))

/-- **The descent arrow of a lift satisfies the cocycle condition exactly.** -/
theorem liftArr_cocycle :
    ∃ h : (Arr.map a ι (descFace T' hC 0) (liftArr u ζ)).src =
        (Arr.map a ι (descFace T' hC 2) (liftArr u ζ)).tgt,
      Arr.comp (Arr.map a ι (descFace T' hC 0) (liftArr u ζ))
        (Arr.map a ι (descFace T' hC 2) (liftArr u ζ)) h =
        Arr.map a ι (descFace T' hC 1) (liftArr u ζ) := by
  have h : (Arr.map a ι (descFace T' hC 0) (liftArr u ζ)).src =
      (Arr.map a ι (descFace T' hC 2) (liftArr u ζ)).tgt :=
    congrArg (fun m : descNerve T' hC 0 ⟶ descNerve T' hC 2 ↦ m.hom.hom.comp u)
      (descV₀_face_zero T' hC)
  refine ⟨h, ?_⟩
  refine (Arr.comp_congr (liftArr_map u ζ 0) (liftArr_map u ζ 2) h).trans
    ((comp_canArr _ _ _ _ _ _ _ _ _ h ?_).trans
      ((canArr_congr _ _ _ _ _ _ _ _ _
        (congrArg (fun m : descNerve T' hC 0 ⟶ descNerve T' hC 2 ↦ m.hom.hom.comp u)
          (descV₀_face_one T' hC).symm)
        (congrArg (fun m : descNerve T' hC 0 ⟶ descNerve T' hC 2 ↦ m.hom.hom.comp u)
          (descVₗ_face_one T' hC).symm) ?_ ?_).trans (liftArr_map u ζ 1).symm))
  · exact trans_square_comp_assoc _ _ _ _ (descV₀_face_zero T' hC) u _ _
  · exact trans_square_comp_assoc _ _ _ _ (descV₀_face_one T' hC).symm u _ _
  · exact trans_square_comp_assoc _ _ _ _ (descVₗ_face_one T' hC).symm u _ _

end Canonical

section Reduction

variable {hA} {hC} {I hI} (u : P.obj →ₐ[ringOf B S hS T'] (descNerve T' hC 0).obj) {x' : 𝒳.val.obj}
  (ζ : ξ a ι u ⟶ x') [hζ : 𝒳.val.p.IsHomLift (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ]

/-- **The descent arrow of a lift reduces to the descent arrow of `x̄`.** If `φ : x̄ ⟶ x'`
exhibits `x'` as a lift of `x̄` and `c ≫ φ` factors through `ζ`, the reduction of the descent
arrow of `ζ` is the descent arrow of `x̄` relative to `c`. -/
theorem map_liftArr_eq_chartRbar {xb : 𝒳.val.obj} (c : ξ a ι ((qC hC I hI).hom.hom.comp u) ⟶ xb)
    [hc : 𝒳.val.p.IsHomLift (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot) c]
    (φ : xb ⟶ x') (hφ : 𝒳.val.p.IsHomLift (specOverMap (thk I hI (baseAlg (κ := B.cutoff) hA)).q) φ)
    (hcφ : c ≫ φ = trans a ι (qC hC I hI) u ≫ ζ) :
    Arr.map a ι (qC₁ hC I hI) (liftArr u ζ) = chartRbar (hA := hA) hC I _ c := by
  have hp := 𝒳.isFiberedInGroupoids
  have := hφ
  have := hp.isStronglyCartesian_homLift
    (specOverMap (thk I hI (baseAlg (κ := B.cutoff) hA)).q) φ
  have hs : (Arr.map a ι (qC₁ hC I hI) (liftArr u ζ)).src =
      (rV₀ hC I).hom.hom.comp ((qC hC I hI).hom.hom.comp u) :=
    (congrArg (fun m : descNerve T' hC 0 ⟶ red I (descNerve T' hC 1) ↦ m.hom.hom.comp u)
      (qC_rV₀ hC I hI)).symm
  have ht : (Arr.map a ι (qC₁ hC I hI) (liftArr u ζ)).tgt =
      (rVₗ hC I).hom.hom.comp ((qC hC I hI).hom.hom.comp u) :=
    (congrArg (fun m : descNerve T' hC 0 ⟶ red I (descNerve T' hC 1) ↦ m.hom.hom.comp u)
      (qC_rVₗ hC I hI)).symm
  unfold chartRbar
  refine eq_canArr _ _ _ _ _ _ hs ht ?_
  have key := red_descArr_fac (lift := (liftArr u ζ).lift) u (liftArr u ζ).hom ζ
    (liftArr_fac u ζ) (eqToHom (congrArg (ξ a ι) hs.symm) ≫
      (Arr.map a ι (qC₁ hC I hI) (liftArr u ζ)).hom ≫ eqToHom (congrArg (ξ a ι) ht))
    (congrArg (ξ a ι) hs.symm) (congrArg (ξ a ι) ht) rfl
  rw [← hcφ] at key
  have h₁ : 𝒳.val.p.IsHomLift (specOverMap (rV₀ hC I) ≫
      specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot)
      (eqToHom (congrArg (ξ a ι) hs.symm) ≫ (Arr.map a ι (qC₁ hC I hI) (liftArr u ζ)).hom ≫
        eqToHom (congrArg (ξ a ι) ht) ≫ trans a ι (rVₗ hC I) _ ≫ c) := by
    have := (Arr.map a ι (qC₁ hC I hI) (liftArr u ζ)).lift
    rw [← spec_rV_base hA hC I hI]
    infer_instance
  refine Functor.IsStronglyCartesian.ext 𝒳.val.p
    (specOverMap (thk I hI (baseAlg (κ := B.cutoff) hA)).q) φ
    (specOverMap (rV₀ hC I) ≫ specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot) ?_
  refine Eq.trans ?_ (key.trans (Category.assoc _ _ _).symm)
  simp only [Category.assoc]

end Reduction

section HomExt

variable {N N' N₂ : SmallAlg (ringOf B S hS T') B.cutoff} (f : N ⟶ N') (i₁ i₂ : N' ⟶ N₂)

/-- **Morphisms out of an object glued from a chart point are determined over the covering.**
Over an fppf covering `Spec N' ⟶ Spec N` with double overlap `Spec N₂`, if `c : ξ w ⟶ xb` over
`Spec f` has its two pullbacks intertwined by an arrow `ρ`, two morphisms `xb ⟶ x'` over the
same `k` that agree after `c` are equal. This is the uniqueness half of
`AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_hom_of_chart`. -/
theorem hom_ext_of_chart (h𝒳 : 𝒳.val.p.IsStackInGroupoids.{w} (BigFppfOver.topology B S hS))
    (hpb : IsPullback (specOverMap i₁) (specOverMap i₂) (specOverMap f) (specOverMap f))
    (hcov : Sieve.ofArrows (fun _ : PUnit.{w + 1} ↦ specOver N') (fun _ ↦ specOverMap f) ∈
      BigFppfOver.topology B S hS (specOver N))
    {Z : BigFppfOver B S hS} (k : specOver N ⟶ Z) {xb x' : 𝒳.val.obj}
    (hxb : 𝒳.val.p.obj xb = specOver N) (hx' : 𝒳.val.p.obj x' = Z)
    (w : P.obj →ₐ[ringOf B S hS T'] N'.obj) (c : ξ a ι w ⟶ xb)
    (hc : 𝒳.val.p.IsHomLift (specOverMap f) c)
    (ρ : ξ a ι (i₁.hom.hom.comp w) ⟶ ξ a ι (i₂.hom.hom.comp w))
    (hρ : 𝒳.val.p.IsHomLift (𝟙 (specOver N₂)) ρ)
    (hρc : ρ ≫ trans a ι i₂ w ≫ c = trans a ι i₁ w ≫ c) (φ₁ φ₂ : xb ⟶ x')
    (hφ₁ : 𝒳.val.p.IsHomLift k φ₁) (hφ₂ : 𝒳.val.p.IsHomLift k φ₂) (h : c ≫ φ₁ = c ≫ φ₂) :
    φ₁ = φ₂ := by
  have hp := 𝒳.isFiberedInGroupoids
  let y := Functor.Restriction.ofIsFiberedInGroupoids 𝒳.val.p hp k x' hx'
  have hy : 𝒳.val.p.IsHomLift k y.hom := Functor.isHomLift_of_restriction _ y
  have : 𝒳.val.p.IsStronglyCartesian k y.hom := hp.isStronglyCartesian_homLift _ _
  have := hρ
  have := hc
  have := hφ₁
  have := hφ₂
  let ζ := c ≫ φ₁
  let βy : ξ a ι w ⟶ y.pt := Functor.IsStronglyCartesian.map 𝒳.val.p k y.hom
    (g := specOverMap f) rfl ζ
  have hβl : 𝒳.val.p.IsHomLift (specOverMap f) βy :=
    Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _
  have hβ : βy ≫ y.hom = ζ := Functor.IsStronglyCartesian.fac _ _ _ _ _
  have := hβl
  have h₁ : 𝒳.val.p.IsHomLift (specOverMap i₁ ≫ specOverMap f) (trans a ι i₁ w ≫ c) :=
    inferInstance
  have h₂ : 𝒳.val.p.IsHomLift (specOverMap i₁ ≫ specOverMap f) (trans a ι i₁ w ≫ βy) :=
    inferInstance
  have hρ₂ : 𝒳.val.p.IsHomLift (specOverMap i₂) (ρ ≫ trans a ι i₂ w) := inferInstance
  have hρζ : ρ ≫ trans a ι i₂ w ≫ ζ = trans a ι i₁ w ≫ ζ := by
    simp only [ζ, ← Category.assoc] at hρc ⊢
    rw [hρc]
  have hmy : (ρ ≫ trans a ι i₂ w) ≫ βy = trans a ι i₁ w ≫ βy := by
    have hl : 𝒳.val.p.IsHomLift (specOverMap i₁ ≫ specOverMap f) ((ρ ≫ trans a ι i₂ w) ≫ βy) := by
      rw [hpb.w]
      infer_instance
    refine Functor.IsStronglyCartesian.ext 𝒳.val.p k y.hom (specOverMap i₁ ≫ specOverMap f) ?_
    exact ((Category.assoc _ _ _).trans ((congrArg _ hβ).trans ((Category.assoc _ _ _).trans
      hρζ))).trans ((congrArg _ hβ).symm.trans (Category.assoc _ _ _).symm)
  have : 𝒳.val.p.IsHomLift (𝟙 (specOver N')) (𝟙 (ξ a ι w)) := IsHomLift.id (ξ_obj a ι w)
  have : 𝒳.val.p.IsHomLift (𝟙 (specOver N₂)) (𝟙 (ξ a ι (i₁.hom.hom.comp w))) :=
    IsHomLift.id (ξ_obj a ι _)
  have hiso := h𝒳.isom_isSheaf xb y.pt hxb y.hpt (fun _ : PUnit.{w + 1} ↦ specOver N')
    (fun _ ↦ specOverMap f) hcov (fun _ _ ↦ specOver N₂) (fun _ _ ↦ specOverMap i₁)
    (fun _ _ ↦ specOverMap i₂) (fun _ _ ↦ hpb)
    (fun _ ↦ Functor.Restriction.ofHomLift _ hp _ hxb (ξ_obj a ι w) c hc)
    (fun _ ↦ Functor.Restriction.ofHomLift _ hp _ y.hpt (ξ_obj a ι w) βy hβl)
    (fun _ _ ↦ Functor.Restriction.ofHomLift _ hp _ hxb (ξ_obj a ι _) _ h₁)
    (fun _ _ ↦ Functor.Restriction.ofHomLift _ hp _ y.hpt (ξ_obj a ι _) _ h₂)
  obtain ⟨g, -, huniq⟩ := hiso (fun _ ↦ 𝟙 _)
    (fun _ ↦ fibreHom_of_isHomLift (W := specOver N') _ _ (𝟙 (ξ a ι w)))
    (fun _ ↦ inferInstance) (fun _ _ ↦ ⟨𝟙 _,
      fibreHom_of_isHomLift (W := specOver N₂) _ _ (𝟙 (ξ a ι (i₁.hom.hom.comp w))),
      Functor.isRestrictionOf_of_fac _ _ _ _ _ _ _ _ _ _ (trans a ι i₁ w)
        (trans_isHomLift a ι i₁ w) rfl (trans a ι i₁ w) (trans_isHomLift a ι i₁ w) rfl
        ((Category.id_comp _).trans (Category.comp_id _).symm),
      Functor.isRestrictionOf_of_fac _ _ _ _ _ _ _ _ _ _ (ρ ≫ trans a ι i₂ w) hρ₂
        ((Category.assoc _ _ _).trans hρc) (ρ ≫ trans a ι i₂ w) hρ₂ hmy
        ((Category.id_comp _).trans (Category.comp_id _).symm)⟩)
  have key : ∀ φ : xb ⟶ x', 𝒳.val.p.IsHomLift k φ → c ≫ φ = ζ →
      ∃ g' : xb ⟶ y.pt, g' ≫ y.hom = φ ∧ g' = g := by
    intro φ hφ hcφ
    have := hφ
    let g' : xb ⟶ y.pt := Functor.IsStronglyCartesian.map 𝒳.val.p k y.hom
      (g := 𝟙 (specOver N)) (Category.id_comp k).symm φ
    have hg'l : 𝒳.val.p.IsHomLift (𝟙 (specOver N)) g' :=
      Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _
    have hg' : g' ≫ y.hom = φ := Functor.IsStronglyCartesian.fac _ _ _ _ _
    have := hg'l
    refine ⟨g', hg', huniq g' ⟨fibreHom_of_isHomLift _ _ g', ?_, fun _ ↦ ?_⟩⟩
    · have := hp.isStronglyCartesian_homLift (𝟙 (specOver N)) g'
      exact Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p (𝟙 (specOver N)) g'
    · change c ≫ g' = 𝟙 _ ≫ βy
      rw [Category.id_comp]
      refine Functor.IsStronglyCartesian.ext 𝒳.val.p k y.hom (specOverMap f) ?_
      exact ((Category.assoc _ _ _).trans ((congrArg _ hg').trans hcφ)).trans hβ.symm
  obtain ⟨g₁, hg₁, e₁⟩ := key φ₁ hφ₁ rfl
  obtain ⟨g₂, hg₂, e₂⟩ := key φ₂ hφ₂ h.symm
  rw [← hg₁, ← hg₂, e₁, e₂]

end HomExt

end StackChart

end AlgebraicGeometry.Stack.GroupoidLift

end
