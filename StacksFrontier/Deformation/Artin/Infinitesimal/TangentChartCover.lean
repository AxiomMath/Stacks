module

public import StacksFrontier.Deformation.Artin.Infinitesimal.SquareZeroCover
public import StacksFrontier.Deformation.Artin.Infinitesimal.ChartTangentBaseChange

/-!
# A chart point over a faithfully flat finitely presented cover

For an algebraic stack `𝒳` locally of finite presentation over `S` and an object `x` over an
affine `T' = Spec A'`, there are a smooth chart `a : (Sch/U₀) ⟶ 𝒳` formally smooth on objects, a
finitely presented `A'`-algebra `P` with `ι : Spec P ⟶ U₀` formally smooth for square-zero
extensions, a faithfully flat finitely presented `A'`-algebra `X` with a point `w : P → X`, and a
formally étale chart of the arrows by a finitely presented algebra `Q` passing through the identity
of `w`, together with a morphism `a(ι ∘ Spec w) ⟶ x` over `Spec X ⟶ T'`. This is the cover on
which the first paragraph of the proof of Stacks 0DNT tests flat base change: over it `x` becomes
the object of a chart point, where flat base change is
`Deformation.Artin.ChartLift.isTangentBaseChangeIso_chart_of_algebraMap`.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.exists_chartPoint_cover`.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory Opposite Limits
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack

universe w u

namespace GroupoidLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

open StackChart in
/-- **A chart point over a faithfully flat finitely presented cover.** An object `x` over the
affine `T'` of an algebraic stack locally of finite presentation over `S` becomes, over a
faithfully flat finitely presented `Γ(T')`-algebra `X`, the object `a(ι ∘ Spec w)` of a point `w`
of a chart through which a formally étale chart of the arrows passes at the identity. -/
theorem exists_chartPoint_cover (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (f : 𝒳 ⟶ schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS))))
    (hf : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f)
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = T') :
    ∃ (U₀ : BigFppfOver B S hS) (a : schemeFibredCategory B S hS U₀ ⟶ 𝒳)
      (P : SmallAlg (ringOf B S hS T') B.cutoff) (ι : specOver P ⟶ U₀)
      (_ : Algebra.FinitePresentation (ringOf B S hS T') P.obj)
      (_ : IsFormallySmoothOnObjects B S hS (schemeFibredCategory B S hS U₀) 𝒳 a)
      (_ : ∀ {C' C : SmallAlg (ringOf B S hS T') B.cutoff} (e : SqZero C' C)
        (m' : specOver C' ⟶ U₀) (u : P.obj →ₐ[ringOf B S hS T'] C.obj),
        specOverMap e.q ≫ m' = specOverMap (SmallAlg.homMk u) ≫ ι →
        ∃ u' : P.obj →ₐ[ringOf B S hS T'] C'.obj, e.q.hom.hom.comp u' = u ∧
          specOverMap (SmallAlg.homMk u') ≫ ι = m')
      (X : SmallAlg (ringOf B S hS T') B.cutoff)
      (_ : Module.FaithfullyFlat (ringOf B S hS T') X.obj)
      (_ : Algebra.FinitePresentation (ringOf B S hS T') X.obj)
      (w : P.obj →ₐ[ringOf B S hS T'] X.obj)
      (Q : SmallAlg (ringOf B S hS T') B.cutoff)
      (_ : Module.FinitePresentation Q.obj Ω[Q.obj⁄ringOf B S hS T'])
      (b : Chart (stackArr a ι) Q.obj) (_ : b.IsFormallyEtale)
      (sV tV : P.obj →ₐ[ringOf B S hS T'] Q.obj)
      (_ : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q.obj →ₐ[ringOf B S hS T'] D.obj),
        (b.app D v).src = v.comp sV)
      (_ : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q.obj →ₐ[ringOf B S hS T'] D.obj),
        (b.app D v).tgt = v.comp tV)
      (ε : Q.obj →ₐ[ringOf B S hS T'] X.obj) (_ : b.app X ε = Arr.idt w)
      (φ : ξ a ι w ⟶ x), 𝒳.val.p.IsHomLift (specOverToBase X) φ := by
  classical
  obtain ⟨hXfib, -, -, U₀, atlas, hrep, hprop⟩ := id h𝒳
  let a : schemeFibredCategory B S hS U₀ ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom atlas
  have hUstack := isDeligneMumfordStack_schemeFibredCategory.{u, w} B S hS U₀
  -- the chart is smooth and formally smooth on objects
  let Psm : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun {_ _} q => Space.IsSmooth B S hS q
  have hPsm := Space.isSmoothLocalOnSourceAndTarget_smooth B S hS
  let _ : (spaceProperty B S hS Psm).IsStableUnderBaseChange := by
    simpa [Psm, spaceProperty] using Space.isSmooth_isStableUnderBaseChange B S hS
  let _ : (spaceProperty B S hS Psm).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) := by
    change (Space.smoothMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS)
    exact Space.smooth_isLocalAtTarget_fppf B S hS
  have ha : HasPropertyOnSomeSmoothDiagram B S hS Psm a :=
    (hasPropertyOnSomeSmoothDiagram_iff_relative B S hS Psm hPsm hUstack.1 h𝒳 a hrep).2
      (fun V y hy F hF hEquiv => (hprop V y hy F hF hEquiv).2)
  have hafs := isFormallySmoothOnObjects_of_isSmooth_unconditional B S hS hUstack.1 h𝒳 a hrep ha
  -- the underlying morphism of the composite chart is locally of finite presentation
  let 𝒳' : AlgebraicStacks.{u, w} B S hS := ⟨𝒳, h𝒳⟩
  let a' : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳' := Bicategory.InducedBicategory.mkHom a
  let f' : 𝒳' ⟶ schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS))) :=
    Bicategory.InducedBicategory.mkHom f
  have hZl : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map
      (schemeMapOfFunctor B S hS (a ≫ f).hom)) :=
    locallyOfFinitePresentation_siteMap_of_isLocallyOfFinitePresentation B S hS (a' ≫ f')
      (AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS a' f'
        (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS a' ha) hf)
  -- the affine étale cover of `T'` on which `x` comes from the chart
  obtain ⟨c, W, g, s, m, θ, hc, hW, hgs, hge, hse, hθ⟩ :=
    exists_affine_etale_chart_cover a hrep hprop (inferInstance : IsAffine _) x hx
  have hterm : ∀ {X : BigFppfOver B S hS} (u v : X ⟶ Over.mk (𝟙 (B.obj hS))), u = v :=
    fun u v => Over.mkIdTerminal.hom_ext u v
  let τ : T' ⟶ Over.mk (𝟙 (B.obj hS)) := Over.mkIdTerminal.from T'
  let k₁ : c ⟶ pullback (s ≫ schemeMapOfFunctor B S hS (a ≫ f).hom) τ :=
    pullback.lift m g (hterm _ _)
  obtain ⟨c', W'', r, s'', m'', hc', hW'', hrs, hre, hs''e, hm''⟩ :=
    BigFppfOver.exists_affine_surjective_etale_refinement_factor (inferInstance : IsAffine _) g
      hgs hge k₁
  have := hc'
  have := hW''
  have hm''s : m'' ≫ s'' ≫ pullback.snd _ _ = r ≫ g := by
    rw [← Category.assoc, hm'', Category.assoc, pullback.lift_snd]
  have hm''f : m'' ≫ s'' ≫ pullback.fst _ _ = r ≫ m := by
    rw [← Category.assoc, hm'', Category.assoc, pullback.lift_fst]
  -- the chart algebra is finitely presented
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  have hpbS := (IsPullback.of_hasPullback (s ≫ schemeMapOfFunctor B S hS (a ≫ f).hom) τ).map
    (BigFppfOver.toScheme B S hS)
  have hsnd : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map
      (pullback.snd (s ≫ schemeMapOfFunctor B S hS (a ≫ f).hom) τ)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpbS
      (by rw [Functor.map_comp]; infer_instance)
  have hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map
      (s'' ≫ pullback.snd _ _)) := by
    rw [Functor.map_comp]; infer_instance
  have hP : Algebra.FinitePresentation (ringOf B S hS T')
      (sectionsAlg W'' (s'' ≫ pullback.snd _ _)).obj :=
    RingHom.finitePresentation_algebraMap.mp (HasRingHomProperty.iff_of_isAffine.mp hlfp)
  -- the chart
  have hιZ : (sectionsHom W'' (s'' ≫ pullback.snd _ _) ≫ s'' ≫ pullback.fst _ _ ≫ s) ≫
      schemeMapOfFunctor B S hS (a ≫ f).hom =
        specOverToBase (sectionsAlg W'' (s'' ≫ pullback.snd _ _)) ≫ τ := hterm _ _
  let ι : specOver (sectionsAlg W'' (s'' ≫ pullback.snd _ _)) ⟶ U₀ :=
    sectionsHom W'' (s'' ≫ pullback.snd _ _) ≫ s'' ≫ pullback.fst _ _ ≫ s
  have hα' := sameImage_pairObj f τ hιZ
  have := hP
  obtain ⟨C₁, f₁, hf₁s, hf₁e, Q, _, hΩ, b, hb, sV, tV, hsV, htV, ε, hε⟩ :=
    exists_arrowChart_finitePresentation a ι h𝒳 f hf hα' (sectionsMap m'' hm''s).hom.hom
  have htoB : specOverToBase C₁ =
      specOverMap f₁ ≫ sectionsHom c' (r ≫ g) ≫ (r ≫ g) := by
    rw [← specOverMap_comp_toBase f₁, ← sectionsHom_comp c' (r ≫ g)]
  have hFF : Module.FaithfullyFlat (ringOf B S hS T') C₁.obj := by
    refine faithfullyFlat_of_specOverToBase C₁ ?_ ?_ <;>
      rw [htoB, Functor.map_comp, Functor.map_comp] <;> infer_instance
  have hFP : Algebra.FinitePresentation (ringOf B S hS T') C₁.obj := by
    refine finitePresentation_of_specOverToBase C₁ ?_
    rw [htoB, Functor.map_comp, Functor.map_comp]; infer_instance
  -- the morphism from the object of the chart point
  let u := f₁.hom.hom.comp (sectionsMap m'' hm''s).hom.hom
  let ν := specOverMap f₁ ≫ sectionsHom c' (r ≫ g) ≫ r
  have hν : specOverMap (SmallAlg.homMk u) ≫ ι = ν ≫ m ≫ s := by
    have e1 : SmallAlg.homMk u = sectionsMap m'' hm''s ≫ f₁ := rfl
    change specOverMap (SmallAlg.homMk u) ≫ sectionsHom W'' (s'' ≫ pullback.snd _ _) ≫ s'' ≫
      pullback.fst _ _ ≫ s = (specOverMap f₁ ≫ sectionsHom c' (r ≫ g) ≫ r) ≫ m ≫ s
    rw [e1, specOverMap_comp]
    simp only [Category.assoc]
    rw [reassoc_of% (specOverMap_sectionsMap m'' hm''s), reassoc_of% hm''f]
  let e₁ : pt ι u ⟶ (Over.mk (m ≫ s) : Over U₀) := Over.homMk ν hν.symm
  have he₁ : (schemeFibredCategory B S hS U₀).val.p.IsHomLift ν e₁ :=
    IsHomLift.map (Over.forget U₀) e₁
  have he₁' : 𝒳.val.p.IsHomLift ν ((CatFiberedInGroupoids.homFunctor a).map e₁) :=
    BasedFunctor.preserves_isHomLift a.hom _ e₁
  have hφ : 𝒳.val.p.IsHomLift (ν ≫ g) ((CatFiberedInGroupoids.homFunctor a).map e₁ ≫ θ) :=
    IsHomLift.comp 𝒳.val.p ν g _ θ
  have hνg : ν ≫ g = specOverToBase C₁ := by rw [htoB]; simp only [ν, Category.assoc]
  exact ⟨U₀, a, _, ι, hP, hafs,
    fun {_ _} e m' u hm' => exists_lift_sectionsHom_of_etale_pullback s hse _ τ s'' hs''e
      e m' u (hterm _ _) hm',
    C₁, hFF, hFP, u, Q, hΩ, b, hb, sV, tV, hsV, htV, ε, hε, _, hνg ▸ hφ⟩

end GroupoidLift

end AlgebraicGeometry.Stack

namespace Deformation.Artin

open TensorProduct

/-! ### Tensor products over isomorphic rings -/

section RingChange

variable {R R' : Type*} [CommRing R] [CommRing R'] (e : R' →+* R) (he : Function.Bijective e)
  {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module R' M]
  [Module R' N] (hM : ∀ (r : R') (m : M), r • m = e r • m)
  (hN : ∀ (r : R') (n : N), r • n = e r • n)

include hM hN in
/-- The additive map `M ⊗_{R'} N → M ⊗_R N` along a ring map `e : R' → R` through which `R'`
acts. -/
def tensorRingChange : M ⊗[R'] N →+ M ⊗[R] N :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun m ↦ AddMonoidHom.mk' (fun n ↦ m ⊗ₜ[R] n) (fun n n' ↦ tmul_add m n n'))
      (fun m m' ↦ by ext n; exact add_tmul m m' n))
    (fun r m n ↦ by
      change (r • m) ⊗ₜ[R] n = m ⊗ₜ[R] (r • n)
      rw [hM, hN, TensorProduct.smul_tmul])

include he hM hN in
/-- The additive map `M ⊗_R N → M ⊗_{R'} N` inverse to `tensorRingChange`, for a bijective
`e : R' → R`. -/
def tensorRingChangeInv : M ⊗[R] N →+ M ⊗[R'] N :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun m ↦ AddMonoidHom.mk' (fun n ↦ m ⊗ₜ[R'] n) (fun n n' ↦ tmul_add m n n'))
      (fun m m' ↦ by ext n; exact add_tmul m m' n))
    (fun r m n ↦ by
      change (r • m) ⊗ₜ[R'] n = m ⊗ₜ[R'] (r • n)
      obtain ⟨r', rfl⟩ := he.2 r
      rw [← hM, ← hN, TensorProduct.smul_tmul])

/-- `tensorRingChange` sends `m ⊗ n` to `m ⊗ n`. -/
theorem tensorRingChange_tmul (m : M) (n : N) :
    tensorRingChange e hM hN (m ⊗ₜ n) = m ⊗ₜ n := rfl

/-- `tensorRingChangeInv` sends `m ⊗ n` to `m ⊗ n`. -/
theorem tensorRingChangeInv_tmul (m : M) (n : N) :
    tensorRingChangeInv e he hM hN (m ⊗ₜ n) = m ⊗ₜ n := rfl

/-- **Tensor products over isomorphic rings agree**: `M ⊗_{R'} N ≅ M ⊗_R N` for an isomorphism
`e : R' → R` through which `R'` acts on `M` and `N`. -/
def tensorRingChangeEquiv : M ⊗[R'] N ≃+ M ⊗[R] N where
  toFun := tensorRingChange e hM hN
  invFun := tensorRingChangeInv e he hM hN
  left_inv t := by
    induction t using TensorProduct.inductionOn with
    | tmul m n => rfl
    | add t t' h h' => rw [map_add, map_add, h, h']
  right_inv t := by
    induction t using TensorProduct.inductionOn with
    | tmul m n => rfl
    | add t t' h h' => rw [map_add, map_add, h, h']
  map_add' := map_add _

/-- `tensorRingChangeEquiv` sends `m ⊗ n` to `m ⊗ n`. -/
theorem tensorRingChangeEquiv_tmul (m : M) (n : N) :
    tensorRingChangeEquiv e he hM hN (m ⊗ₜ n) = m ⊗ₜ n := rfl

end RingChange

end Deformation.Artin


/-! ### Flat base change at a chart point, by a tensor product -/

namespace Deformation.Artin.ChartLift

universe u

open AlgebraicGeometry CategoryTheory TensorProduct AlgebraicGeometry.Stack
open AlgebraicGeometry.Stack.GroupoidLift
open AlgebraicGeometry.Stack.GroupoidLift.StackChart AlgebraicGeometry.Space.ChartDescent

section ChartTensor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {A : Type u} [CommRing A] (e : ringOf B S hS T' →+* A) (he : Function.Bijective e)

/-- `X ⊗_A C` as a small algebra over `Γ(T')`, through `X`. -/
noncomputable abbrev tensorAlg (X : SmallAlg (ringOf B S hS T') B.cutoff) [Algebra A X.obj]
    (C : Type u) [CommRing C] [Algebra A C] (h : Cardinal.mk (X.obj ⊗[A] C) < B.cutoff) :
    SmallAlg (ringOf B S hS T') B.cutoff :=
  SmallAlg.mk (X.obj ⊗[A] C) h

/-- The inclusion `X → X ⊗_A C` of small algebras over `Γ(T')`. -/
noncomputable abbrev tensorAlgHom (X : SmallAlg (ringOf B S hS T') B.cutoff) [Algebra A X.obj]
    (C : Type u) [CommRing C] [Algebra A C] (h : Cardinal.mk (X.obj ⊗[A] C) < B.cutoff) :
    X ⟶ tensorAlg X C h :=
  SmallAlg.homMk (R := X) (R' := tensorAlg X C h) Algebra.TensorProduct.includeLeft

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- `tensorAlgHom` sends `x` to `x ⊗ 1`. -/
theorem tensorAlgHom_apply (X : SmallAlg (ringOf B S hS T') B.cutoff) [Algebra A X.obj]
    (C : Type u) [CommRing C] [Algebra A C] (h : Cardinal.mk (X.obj ⊗[A] C) < B.cutoff)
    (x : X.obj) : (tensorAlgHom X C h).hom.hom x = (x ⊗ₜ[A] (1 : C) : X.obj ⊗[A] C) := rfl

variable {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} {a : Stack.schemeFibredCategory B S hS U₀ ⟶ 𝒳}
  {P : SmallAlg (ringOf B S hS T') B.cutoff} {ι : specOver P ⟶ U₀}
  {Q : SmallAlg (ringOf B S hS T') B.cutoff} {b : Chart (stackArr a ι) Q.obj}
  {sV tV : P.obj →ₐ[ringOf B S hS T'] Q.obj}
  (hb : b.IsFormallyEtale)
  (hsV : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q.obj →ₐ[ringOf B S hS T'] D.obj),
    (b.app D v).src = v.comp sV)
  (htV : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q.obj →ₐ[ringOf B S hS T'] D.obj),
    (b.app D v).tgt = v.comp tV)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- `(x ⊗ m) ⊗ c ↦ (x ⊗ c) ⊗ m` is `c • (x ⊗ 1) ⊗ m`. -/
theorem rightComm_tmul_eq_smul {X : Type u} [CommRing X] [Algebra A X] {C : Type u} [CommRing C]
    [Algebra A C] {M : Type u} [AddCommGroup M] [Module A M] (t : X ⊗[A] M) (c : C) :
    TensorProduct.rightComm A X M C (t ⊗ₜ[A] c) = ((1 : X) ⊗ₜ[A] c : X ⊗[A] C) •
      TensorProduct.map (Algebra.TensorProduct.includeLeft : X →ₐ[A] X ⊗[A] C).toLinearMap
        LinearMap.id t := by
  induction t using TensorProduct.inductionOn with
  | tmul x m =>
    rw [TensorProduct.rightComm_tmul, TensorProduct.map_tmul, TensorProduct.smul_tmul', smul_eq_mul,
      AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, LinearMap.id_apply]
  | add t t' h₁ h₂ => rw [TensorProduct.add_tmul, map_add, h₁, h₂, map_add, smul_add]

/-- The map `C → X ⊗_A C` as a map of `Γ(T')`-algebras, for `Γ(T')` acting on `C` through
`e : Γ(T') ≅ A`. -/
noncomputable def tensorRight {X : SmallAlg (ringOf B S hS T') B.cutoff} [Algebra A X.obj]
    (hAX : ∀ r, algebraMap A X.obj (e r) = algebraMap (ringOf B S hS T') X.obj r)
    (C : Type u) [CommRing C] [Algebra A C] [Algebra (ringOf B S hS T') C]
    (hC : ∀ r, algebraMap (ringOf B S hS T') C r = algebraMap A C (e r))
    (h : Cardinal.mk (X.obj ⊗[A] C) < B.cutoff) :
    C →ₐ[ringOf B S hS T'] (tensorAlg X C h).obj :=
  { toRingHom := (Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).toRingHom
    commutes' := fun r ↦ by
      change (1 : X.obj) ⊗ₜ[A] (algebraMap (ringOf B S hS T') C r) =
        (algebraMap (ringOf B S hS T') X.obj r) ⊗ₜ[A] (1 : C)
      rw [hC, ← hAX, Algebra.algebraMap_eq_smul_one (A := C) (e r),
        Algebra.algebraMap_eq_smul_one (A := X.obj) (e r)]
      exact (TensorProduct.smul_tmul _ _ _).symm }

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
include he in
/-- **`X[X ⊗_A M] ⊗_{Γ(T')} C ≅ (X ⊗_A C)[(X ⊗_A C) ⊗_A M]`**, the hypothesis of
`isTangentBaseChangeIso_chart_of_algebraMap` for the base change by a tensor product. -/
theorem bijective_sqzTensorLift_tensor {X : SmallAlg (ringOf B S hS T') B.cutoff}
    [Algebra A X.obj] (hAX : ∀ r, algebraMap A X.obj (e r) = algebraMap (ringOf B S hS T') X.obj r)
    (C : Type u) [CommRing C] [Algebra A C] [Algebra (ringOf B S hS T') C]
    (hC : ∀ r, algebraMap (ringOf B S hS T') C r = algebraMap A C (e r))
    (h : Cardinal.mk (X.obj ⊗[A] C) < B.cutoff) (M : SiteModule A B) :
    Function.Bijective (sqzTensorLift (tensorAlgHom X C h)
      (M := (⟨_, isSiteModule_tensor (contains_spec X) M⟩ : SiteModule X.obj B).obj)
      (N := (⟨_, isSiteModule_tensor (A₁ := X.obj ⊗[A] C) (contains_spec (tensorAlg X C h)) M⟩ :
        SiteModule (tensorAlg X C h).obj B).obj)
      (tensorCoeffMap (Algebra.TensorProduct.includeLeft : X.obj →ₐ[A] X.obj ⊗[A] C) M.obj)
      (card_sqz_lt _) (card_sqz_lt _) (tensorRight e hAX C hC h)) := by
  classical
  have hMX : ∀ (r : ringOf B S hS T') (x : X.obj), r • x = e r • x := fun r x ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, hAX]
  have hNC : ∀ (r : ringOf B S hS T') (c : C), r • c = e r • c := fun r c ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, hC]
  have hX : Function.Bijective (Algebra.TensorProduct.lift (tensorAlgHom X C h).hom.hom
      (tensorRight e hAX C hC h) (fun _ _ ↦ Commute.all _ _) :
        X.obj ⊗[ringOf B S hS T'] C →ₐ[ringOf B S hS T'] (tensorAlg X C h).obj) := by
    have heq : ⇑(Algebra.TensorProduct.lift (tensorAlgHom X C h).hom.hom
        (tensorRight e hAX C hC h) (fun _ _ ↦ Commute.all _ _) :
          X.obj ⊗[ringOf B S hS T'] C →ₐ[ringOf B S hS T'] (tensorAlg X C h).obj) =
        ⇑(tensorRingChangeEquiv e he hMX hNC) := by
      funext t
      induction t using TensorProduct.inductionOn with
      | tmul x c =>
        rw [Algebra.TensorProduct.lift_tmul, tensorRingChangeEquiv_tmul]
        change (x ⊗ₜ[A] (1 : C)) * ((1 : X.obj) ⊗ₜ[A] c) = x ⊗ₜ[A] c
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      | add t t' h₁ h₂ => rw [map_add, map_add, h₁, h₂]
    rw [heq]
    exact (tensorRingChangeEquiv e he hMX hNC).bijective
  let : Module (ringOf B S hS T') (X.obj ⊗[A] M.obj) :=
    Module.compHom (X.obj ⊗[A] M.obj) (algebraMap (ringOf B S hS T') X.obj)
  have hM₁ : ∀ (r : ringOf B S hS T') (t : X.obj ⊗[A] M.obj),
      algebraMap (ringOf B S hS T') X.obj r • t = (e r • t : X.obj ⊗[A] M.obj) := fun r t ↦ by
    rw [← hAX, algebraMap_smul]
  let β₀ : (X.obj ⊗[A] M.obj) ⊗[ringOf B S hS T'] C ≃+ (X.obj ⊗[A] C) ⊗[A] M.obj :=
    (tensorRingChangeEquiv e he hM₁ hNC).trans
      (TensorProduct.rightComm A X.obj M.obj C).toAddEquiv
  exact bijective_sqzTensorLift _ _ _ _ _ hX β₀.toAddMonoidHom β₀.bijective
    (fun t c ↦ rightComm_tmul_eq_smul t c)

include he hb hsV htV in
/-- **Stacks 0DNT at a chart point, for the base change `X → X ⊗_A C` by a flat `A`-algebra
`C`**, where `Γ(T') ≅ A` and the coefficients are `X ⊗_A M → (X ⊗_A C) ⊗_A M`. -/
theorem isTangentBaseChangeIso_chart_tensor {X : SmallAlg (ringOf B S hS T') B.cutoff}
    [Algebra A X.obj] (hAX : ∀ r, algebraMap A X.obj (e r) = algebraMap (ringOf B S hS T') X.obj r)
    (C : Type u) [CommRing C] [Algebra A C] [Module.Flat A C]
    (h : Cardinal.mk (X.obj ⊗[A] C) < B.cutoff) (M : SiteModule A B)
    {w : P.obj →ₐ[ringOf B S hS T'] X.obj}
    (hf : Spec.map (CommRingCat.ofHom (algebraMap X.obj (X.obj ⊗[A] C))) ≫ toSOf X =
      toSOf (tensorAlg X C h))
    (hφ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom (algebraMap X.obj (X.obj ⊗[A] C)) B S hS
      (toSOf X) (toSOf (tensorAlg X C h)) (contains_spec X) (contains_spec (tensorAlg X C h)) hf)
      (trans a ι (tensorAlgHom X C h) w))
    [Module.FinitePresentation P.obj Ω[P.obj⁄ringOf B S hS T']]
    [Module.FinitePresentation Q.obj Ω[Q.obj⁄ringOf B S hS T']]
    {v : Q.obj →ₐ[ringOf B S hS T'] X.obj} (hv : b.app X v = Arr.idt w)
    (ha : Stack.IsFormallySmoothOnObjects B S hS (Stack.schemeFibredCategory B S hS U₀) 𝒳 a)
    (hι : ∀ {C' C : SmallAlg (ringOf B S hS T') B.cutoff} (e : SqZero C' C)
      (m' : specOver C' ⟶ U₀) (u : P.obj →ₐ[ringOf B S hS T'] C.obj),
      specOverMap e.q ≫ m' = specOverMap (SmallAlg.homMk u) ≫ ι →
      ∃ u' : P.obj →ₐ[ringOf B S hS T'] C'.obj, e.q.hom.hom.comp u' = u ∧
        specOverMap (SmallAlg.homMk u') ≫ ι = m')
    (Fx : TangentFunctorData X.obj B S hS (toSOf X) (contains_spec X) 𝒳.val.p (ξ a ι w)
      (ξ_obj a ι w))
    (Gy : TangentFunctorData (X.obj ⊗[A] C) B S hS (toSOf (tensorAlg X C h))
      (contains_spec (tensorAlg X C h)) 𝒳.val.p
      (ξ a ι ((tensorAlgHom X C h).hom.hom.comp w)) (ξ_obj a ι _)) :
    IsTangentBaseChangeIso 𝒳.property hf (trans a ι (tensorAlgHom X C h) w) hφ Fx Gy
      (M := ⟨_, isSiteModule_tensor (contains_spec X) M⟩)
      (N := ⟨_, isSiteModule_tensor (A₁ := X.obj ⊗[A] C) (contains_spec (tensorAlg X C h)) M⟩)
      (tensorCoeffMap (Algebra.TensorProduct.includeLeft : X.obj →ₐ[A] X.obj ⊗[A] C) M.obj) := by
  classical
  let : Algebra (ringOf B S hS T') C := ((algebraMap A C).comp e).toAlgebra
  let : Algebra (ringOf B S hS T') A := e.toAlgebra
  have : IsScalarTower (ringOf B S hS T') A C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Flat (ringOf B S hS T') A :=
    Module.Flat.of_linearEquiv (LinearEquiv.ofBijective
      (Algebra.linearMap (ringOf B S hS T') A) he).symm
  have : Module.Flat (ringOf B S hS T') C := Module.Flat.trans (ringOf B S hS T') A C
  have hL := bijective_sqzTensorLift_tensor e he hAX C (fun _ ↦ rfl) h M
  exact isTangentBaseChangeIso_chart_of_algebraMap hb hsV htV (tensorAlgHom X C h) rfl _ _
    (fun _ ↦ rfl) hf hφ _ hL hv ha hι Fx Gy

end ChartTensor

end Deformation.Artin.ChartLift

end
