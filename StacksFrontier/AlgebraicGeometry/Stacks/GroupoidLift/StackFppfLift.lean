module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackLiftPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackLiftAffine
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackFppfLiftAux
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackChartCover
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Pushout.QuasiFiniteFunctoriality
public import StacksFrontier.Deformation.Artin.Infinitesimal

/-!
# Descent of infinitesimal lifts from a faithfully flat finitely presented algebra

Let `𝒳` be an algebraic stack over `S` whose structure morphism is locally of finite
presentation, `(A' → A, x)` a deformation situation, `B'` a faithfully flat finitely presented
`A'`-algebra and `y'` an object of `𝒳` over `B'` lifting `x|_{B' ⊗_{A'} A}`. Then `x` lifts to an
object over `A'` (Stacks 0DNU,
`AlgebraicGeometry.Stack.exists_lift_of_fppf_lift_of_isDeformationSituation`).

## Main results

* `AlgebraicGeometry.Stack.exists_lift_of_fppf_lift_of_isDeformationSituation`: an infinitesimal
  deformation of an object of an algebraic stack locally of finite presentation lifts as soon as
  it lifts after a faithfully flat finitely presented base change.

## References

* [Stacks Project, Tag 0DNU](https://stacks.math.columbia.edu/tag/0DNU)
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

open StackChart

/-- The projection of a category fibered in groupoids is a fibered functor. -/
local instance : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered

/-- Given a chart `a` whose groupoid is formally smooth on sources, a formally étale arrow chart
`b`, a point `ubar` of the chart over the reduction of `descNerve T' hC 0` together with a lift
`u₀` of it, and a morphism from the object of `ubar` to an object `xb` over the reduction of
`T'` which is a pullback of `x` along `φT`, the object `x` over `T` lifts along `i : T ⟶ T'`. -/
theorem exists_lift_of_chartPoint_of_lift_transport
    (hst : 𝒳.val.p.IsStackInGroupoids.{w} (BigFppfOver.topology B S hS))
    {U₀ : BigFppfOver B S hS} {a : schemeFibredCategory B S hS U₀ ⟶ 𝒳}
    {P : SmallAlg (ringOf B S hS T') B.cutoff} {ι : specOver P ⟶ U₀}
    (hA : Cardinal.mk (ringOf B S hS T') < B.cutoff) {C' : Type u}
    [CommRing C'] [Algebra (ringOf B S hS T') C'] (hC : Cardinal.mk C' < B.cutoff)
    [Module.FaithfullyFlat (ringOf B S hS T') C'] [Algebra.FinitePresentation (ringOf B S hS T') C']
    [Module.FinitePresentation P.obj Ω[P.obj⁄ringOf B S hS T']]
    (hG : (stackGroupoid a ι).SrcFormallySmooth)
    {Q : Type u} [CommRing Q] [Algebra (ringOf B S hS T') Q]
    [Module.FinitePresentation Q Ω[Q⁄ringOf B S hS T']]
    (b : Chart (stackArr a ι) Q) (hb : b.IsFormallyEtale) (sV tV : P.obj →ₐ[ringOf B S hS T'] Q)
    (hsV : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q →ₐ[ringOf B S hS T'] D.obj),
      (b.app D v).src = v.comp sV)
    (htV : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q →ₐ[ringOf B S hS T'] D.obj),
      (b.app D v).tgt = v.comp tV)
    {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (i : T ⟶ T')
    (hI : kerIdeal i ^ 2 = ⊥) (φT : specOver (red (kerIdeal i) (baseAlg (κ := B.cutoff) hA)) ⟶ T)
    [IsIso φT] (hφT : φT ≫ i = specOverToBase (red (kerIdeal i) (baseAlg (κ := B.cutoff) hA)))
    {x xb : 𝒳.val.obj} (c₀ : xb ⟶ x) [𝒳.val.p.IsHomLift φT c₀]
    (hxb : 𝒳.val.p.obj xb = specOver (red (kerIdeal i) (baseAlg (κ := B.cutoff) hA)))
    (ubar : P.obj →ₐ[ringOf B S hS T'] (red (kerIdeal i) (descNerve T' hC 0)).obj)
    (cm : ξ a ι ubar ⟶ xb)
    (hc : 𝒳.val.p.IsHomLift (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot) cm)
    (εbar : Q →ₐ[ringOf B S hS T'] (red (kerIdeal i) (descNerve T' hC 0)).obj)
    (hε : b.app _ εbar = Arr.idt ubar) (u₀ : P.obj →ₐ[ringOf B S hS T'] (descNerve T' hC 0).obj)
    (hu₀ : (thk (kerIdeal i) hI (descNerve T' hC 0)).q.hom.hom.comp u₀ = ubar) :
    ∃ (z : 𝒳.val.obj) (_ : 𝒳.val.p.obj z = T') (φ : x ⟶ z), 𝒳.val.p.IsHomLift i φ := by
  have : 𝒳.val.p.IsStronglyCartesian φT c₀ :=
    𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift φT c₀
  obtain ⟨u, x', ζ, φ, hζ, hφ⟩ := exists_lift_of_chartPoint_of_lift hA hC (kerIdeal i) hI hst hG b
    hb sV tV hsV htV hxb ubar cm hc εbar hε u₀ hu₀
  have hx' : 𝒳.val.p.obj x' = specOver (baseAlg (κ := B.cutoff) hA) :=
    @IsHomLift.codomain_eq _ _ _ _ 𝒳.val.p _ _ _ _
      (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ hζ
  have := isIso_specOverToBase_baseAlg (T' := T') hA
  set toB := specOverToBase (T' := T') (baseAlg (κ := B.cutoff) hA)
  set z := Functor.IsPreFibered.pullbackObj hx' (inv toB)
  have hz : 𝒳.val.p.obj z = T' := Functor.IsPreFibered.pullbackObj_proj hx' (inv toB)
  set d : z ⟶ x' := Functor.IsPreFibered.pullbackMap hx' (inv toB)
  have : IsIso c₀ := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p φT c₀
  have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift (inv toB) d
  have : IsIso d := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p (inv toB) d
  have hφ' : 𝒳.val.p.IsHomLift (inv φT ≫
      specOverMap (thk (kerIdeal i) hI (baseAlg (κ := B.cutoff) hA)).q ≫ inv (inv toB))
      (inv c₀ ≫ φ ≫ inv d) := inferInstance
  have hi' : inv φT ≫ specOverMap (thk (kerIdeal i) hI (baseAlg (κ := B.cutoff) hA)).q ≫
      inv (inv toB) = i := by
    rw [IsIso.inv_inv, specOverMap_comp_toBase, ← hφT, IsIso.inv_hom_id_assoc]
  exact ⟨z, hz, inv c₀ ≫ φ ≫ inv d, isHomLift_of_eq hi' hφ'⟩

/-- If `Spec C → T'` factors as `Spec C → Spec Γ(c') → c' → V' → T'` with the first map surjective
étale (`f₁`), `c' → V'` surjective étale and `k : V' → T'` flat, surjective and locally of finite
presentation, then `C` is faithfully flat and finitely presented over `Γ(T')`. -/
private theorem faithfullyFlat_finitePresentation_of_etale_cover {c' V' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c')] {j₁ : c' ⟶ T'}
    {C : SmallAlg (ringOf B S hS T') B.cutoff} (f₁ : sectionsAlg c' j₁ ⟶ C) (e : c' ⟶ V')
    (k : V' ⟶ T') (he : e ≫ k = j₁) [Etale ((BigFppfOver.toScheme B S hS).map (specOverMap f₁))]
    [Surjective ((BigFppfOver.toScheme B S hS).map (specOverMap f₁))]
    [Etale ((BigFppfOver.toScheme B S hS).map e)] [Surjective ((BigFppfOver.toScheme B S hS).map e)]
    [Flat ((BigFppfOver.toScheme B S hS).map k)] [Surjective ((BigFppfOver.toScheme B S hS).map k)]
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map k)] :
    Module.FaithfullyFlat (ringOf B S hS T') C.obj ∧
      Algebra.FinitePresentation (ringOf B S hS T') C.obj := by
  subst he
  have h : (BigFppfOver.toScheme B S hS).map (specOverToBase C) =
      (BigFppfOver.toScheme B S hS).map (specOverMap f₁) ≫
        (BigFppfOver.toScheme B S hS).map (sectionsHom c' (e ≫ k)) ≫
          (BigFppfOver.toScheme B S hS).map e ≫ (BigFppfOver.toScheme B S hS).map k := by
    simp only [← Functor.map_comp, ← specOverMap_comp_toBase f₁, ← sectionsHom_comp c' (e ≫ k)]
  refine ⟨faithfullyFlat_of_specOverToBase C ?_ ?_, finitePresentation_of_specOverToBase C ?_⟩ <;>
    rw [h] <;> infer_instance

/-- Over a cartesian square `Y = X ×_{X'} Y'` with maps `j, l, i, k`, objects `α : y ⟶ x` over `j`
and `β : y ⟶ y'` over `l`, a morphism `c₀ : xb ⟶ x` over `φ` and `θ : w ⟶ y'` over `ν` with
`(ψ ≫ φ) ≫ i = ν ≫ k` give a morphism `w ⟶ xb` over `ψ`. -/
private theorem exists_isHomLift_of_isPullback {X Y Y' X' R E : BigFppfOver B S hS}
    {j : Y ⟶ X} {l : Y ⟶ Y'} {i : X ⟶ X'} {k : Y' ⟶ X'} (hpb : IsPullback j l i k)
    {x y y' xb w : 𝒳.val.obj} (α : y ⟶ x) [𝒳.val.p.IsHomLift j α] (β : y ⟶ y')
    [𝒳.val.p.IsHomLift l β] {φ : R ⟶ X} (c₀ : xb ⟶ x) [𝒳.val.p.IsHomLift φ c₀] {ψ : E ⟶ R}
    {ν : E ⟶ Y'} (θ : w ⟶ y') [𝒳.val.p.IsHomLift ν θ] (h : (ψ ≫ φ) ≫ i = ν ≫ k) :
    ∃ cm : w ⟶ xb, 𝒳.val.p.IsHomLift ψ cm := by
  have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift l β
  have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift φ c₀
  exact ⟨Functor.IsStronglyCartesian.map 𝒳.val.p φ c₀ (hpb.lift_fst _ _ h)
    (Functor.IsStronglyCartesian.map 𝒳.val.p l β (hpb.lift_snd _ _ h).symm θ ≫ α), inferInstance⟩

/-- If `h : W ⟶ Z` is locally of finite presentation and `s'' : W'' ⟶ W ×_Z T'` is étale with
`W''` affine, then `Γ(W'')` is finitely presented over `Γ(T')`. -/
private theorem finitePresentation_sectionsAlg_of_etale_pullback {Z W W'' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W'')] (h : W ⟶ Z) (τ : T' ⟶ Z)
    (s'' : W'' ⟶ pullback h τ)
    [hh : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map h)]
    [Etale ((BigFppfOver.toScheme B S hS).map s'')] :
    Algebra.FinitePresentation (ringOf B S hS T')
      (sectionsAlg W'' (s'' ≫ pullback.snd _ _)).obj := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (pullback.snd h τ)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((IsPullback.of_hasPullback h τ).map (BigFppfOver.toScheme B S hS)) hh
  have hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map
      (s'' ≫ pullback.snd _ _)) := by
    rw [Functor.map_comp]
    infer_instance
  exact RingHom.finitePresentation_algebraMap.mp (HasRingHomProperty.iff_of_isAffine.mp hlfp)

/-- **Descent of an infinitesimal lift, from chart data.** The data: a chart `a` formally smooth
on objects, `s : W ⟶ U₀` étale, `s'' : W'' ⟶ W ×_Z T'` étale with `W''` affine and `Γ(W'')`
finitely presented over `Γ(T')`; the deformation situation `i : T ⟶ T'` and the cartesian square
`V = T ×_{T'} V'` with `k : V' ⟶ T'` flat, surjective and locally of finite presentation; a
surjective étale `r ≫ g : c' ⟶ V'` with `m'' : c' ⟶ W''` over `W` and `T'`; objects `x` over
`T`, `y` over `V`, `y'` over `V'` with `α : y ⟶ x`, `β : y ⟶ y'`, and `θ : a(s ∘ m) ⟶ y'` over
`g`. -/
theorem exists_lift_of_fppf_chart
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) {Z : BigFppfOver B S hS}
    (f : 𝒳 ⟶ schemeFibredCategory B S hS Z)
    (hf : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f)
    {U₀ W W'' c c' T V V' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W'')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (a : schemeFibredCategory B S hS U₀ ⟶ 𝒳)
    (ha : IsFormallySmoothOnObjects B S hS (schemeFibredCategory B S hS U₀) 𝒳 a)
    (s : W ⟶ U₀) (hse : Etale ((BigFppfOver.toScheme B S hS).map s)) (τ : T' ⟶ Z)
    (s'' : W'' ⟶ pullback (s ≫ schemeMapOfFunctor B S hS (a ≫ f).hom) τ)
    (hs''e : Etale ((BigFppfOver.toScheme B S hS).map s''))
    (hP : Algebra.FinitePresentation (ringOf B S hS T')
      (sectionsAlg W'' (s'' ≫ pullback.snd _ _)).obj)
    (hιZ : (sectionsHom W'' (s'' ≫ pullback.snd _ _) ≫ s'' ≫ pullback.fst _ _ ≫ s) ≫
      schemeMapOfFunctor B S hS (a ≫ f).hom =
        specOverToBase (sectionsAlg W'' (s'' ≫ pullback.snd _ _)) ≫ τ)
    (i : T ⟶ T') (hi : Deformation.Artin.IsDeformationSituation
      ((BigFppfOver.toScheme B S hS).map i).appTop.hom)
    (j : V ⟶ T) (l : V ⟶ V') (k : V' ⟶ T') (hpb : IsPullback j l i k)
    (hkf : Flat ((BigFppfOver.toScheme B S hS).map k))
    (hks : Surjective ((BigFppfOver.toScheme B S hS).map k))
    (hkp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map k))
    (g : c ⟶ V') (m : c ⟶ W) (r : c' ⟶ c)
    (hrs : Surjective ((BigFppfOver.toScheme B S hS).map (r ≫ g)))
    (hre : Etale ((BigFppfOver.toScheme B S hS).map (r ≫ g))) (m'' : c' ⟶ W'')
    (hm''s : m'' ≫ s'' ≫ pullback.snd _ _ = r ≫ g ≫ k)
    (hm''f : m'' ≫ s'' ≫ pullback.fst _ _ = r ≫ m)
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = T) (y : 𝒳.val.obj) (α : y ⟶ x)
    (hα : 𝒳.val.p.IsHomLift j α) (y' : 𝒳.val.obj) (β : y ⟶ y') (hβ : 𝒳.val.p.IsHomLift l β)
    (θ : (CatFiberedInGroupoids.homFunctor a).obj (Over.mk (m ≫ s)) ⟶ y')
    (hθ : 𝒳.val.p.IsHomLift g θ) :
    ∃ (x' : 𝒳.val.obj) (_ : 𝒳.val.p.obj x' = T') (φ : x ⟶ x'), 𝒳.val.p.IsHomLift i φ := by
  classical
  obtain ⟨_, ⟨_, hst⟩, _⟩ := id h𝒳
  set A' := ringOf B S hS T'
  have hA : Cardinal.mk A' < B.cutoff := card_sections_lt T'
  have hsurjI : Function.Surjective (algebraMap A' (sectionsAlg T i).obj) := hi.1
  have hI : kerIdeal i ^ 2 = ⊥ := hi.2
  let ι : specOver (sectionsAlg W'' (s'' ≫ pullback.snd _ _)) ⟶ U₀ :=
    sectionsHom W'' (s'' ≫ pullback.snd _ _) ≫ s'' ≫ pullback.fst _ _ ≫ s
  have hG : (stackGroupoid (a := a) (ι := ι)).SrcFormallySmooth :=
    stackGroupoid_srcFormallySmooth_of_over f τ hιZ ha
      (exists_lift_sectionsHom_of_etale_pullback s hse _ τ s'' hs''e)
  obtain ⟨C₁, f₁, hf₁s, hf₁e, Q, _, _, b, hb, sV, tV, hsV, htV, ε, hε⟩ :=
    exists_arrowChart_finitePresentation a ι h𝒳 f hf (sameImage_pairObj f τ hιZ)
      (sectionsMap m'' hm''s).hom.hom
  have hC : Cardinal.mk C₁.obj < B.cutoff := C₁.2
  obtain ⟨_, _⟩ :=
    faithfullyFlat_finitePresentation_of_etale_cover f₁ (r ≫ g) k (Category.assoc _ _ _)
  let q := (thk (kerIdeal i) hI (descNerve T' hC 0)).q
  let u₀ : (sectionsAlg W'' (s'' ≫ pullback.snd _ _)).obj →ₐ[A'] (descNerve T' hC 0).obj :=
    f₁.hom.hom.comp (sectionsMap m'' hm''s).hom.hom
  let ubar := q.hom.hom.comp u₀
  let εbar := q.hom.hom.comp ε
  let φT := redToBase i hsurjI hA
  let xb := Functor.IsPreFibered.pullbackObj hx φT
  let c₀ : xb ⟶ x := Functor.IsPreFibered.pullbackMap hx φT
  let ν := specOverMap q ≫ specOverMap f₁ ≫ sectionsHom c' (r ≫ g ≫ k) ≫ r
  have hν : specOverMap (SmallAlg.homMk ubar) ≫ ι = ν ≫ m ≫ s := by
    change specOverMap (SmallAlg.homMk ubar) ≫ sectionsHom W'' (s'' ≫ pullback.snd _ _) ≫ s'' ≫
      pullback.fst _ _ ≫ s = (specOverMap q ≫ specOverMap f₁ ≫ sectionsHom c' (r ≫ g ≫ k) ≫ r) ≫
        m ≫ s
    rw [show SmallAlg.homMk ubar = sectionsMap m'' hm''s ≫ f₁ ≫ q from rfl, specOverMap_comp,
      specOverMap_comp]
    simp only [Category.assoc]
    rw [reassoc_of% (specOverMap_sectionsMap m'' hm''s), reassoc_of% hm''f]
  let e₁ : pt ι ubar ⟶ (Over.mk (m ≫ s) : Over U₀) := Over.homMk ν hν.symm
  have he₁ : (schemeFibredCategory B S hS U₀).val.p.IsHomLift ν e₁ :=
    IsHomLift.map (Over.forget U₀) e₁
  have he₁' : 𝒳.val.p.IsHomLift ν ((CatFiberedInGroupoids.homFunctor a).map e₁) :=
    BasedFunctor.preserves_isHomLift a.hom _ e₁
  have hk : (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫ φT) ≫ i = (ν ≫ g) ≫ k := by
    change _ = (specOverMap q ≫ specOverMap f₁ ≫ sectionsHom c' (r ≫ g ≫ k) ≫ r) ≫ g ≫ k
    simp only [Category.assoc]
    rw [redToBase_comp, specOverMap_comp_toBase, sectionsHom_comp, specOverMap_comp_toBase,
      specOverMap_comp_toBase]
  obtain ⟨cm, hc⟩ := exists_isHomLift_of_isPullback hpb α β c₀ (ν := ν ≫ g)
    ((CatFiberedInGroupoids.homFunctor a).map e₁ ≫ θ) hk
  exact exists_lift_of_chartPoint_of_lift_transport hst hA hC hG b hb sV tV hsV htV i hI φT
    (redToBase_comp i hsurjI hA) c₀ (Functor.IsPreFibered.pullbackObj_proj hx φT) ubar cm hc εbar
    ((b.natural q ε).symm.trans ((congrArg _ hε).trans (Arr.map_idt _ _))) u₀ rfl

/-- **Descent of an infinitesimal lift along a faithfully flat finitely presented cover**, for an
algebraic stack locally of finite presentation over `S`, with the deformation and its base change
as a cartesian square `V = T ×_{T'} V'` of affines of the site. -/
theorem exists_lift_of_fppf_lift_core (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (f : 𝒳 ⟶ schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS))))
    (hf : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f)
    {T V V' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
    (i : T ⟶ T') (hi : Deformation.Artin.IsDeformationSituation
      ((BigFppfOver.toScheme B S hS).map i).appTop.hom)
    (j : V ⟶ T) (l : V ⟶ V') (k : V' ⟶ T') (hpb : IsPullback j l i k)
    (hkf : Flat ((BigFppfOver.toScheme B S hS).map k))
    (hks : Surjective ((BigFppfOver.toScheme B S hS).map k))
    (hkp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map k))
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = T) (y : 𝒳.val.obj) (α : y ⟶ x)
    (hα : 𝒳.val.p.IsHomLift j α) (y' : 𝒳.val.obj) (hy' : 𝒳.val.p.obj y' = V') (β : y ⟶ y')
    (hβ : 𝒳.val.p.IsHomLift l β) :
    ∃ (x' : 𝒳.val.obj) (_ : 𝒳.val.p.obj x' = T') (φ : x ⟶ x'), 𝒳.val.p.IsHomLift i φ := by
  obtain ⟨_, -, -, U₀, atlas, hrep, hprop⟩ := id h𝒳
  let a : schemeFibredCategory B S hS U₀ ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom atlas
  have hUstack := isDeligneMumfordStack_schemeFibredCategory.{u, w} B S hS U₀
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
  let 𝒳' : AlgebraicStacks.{u, w} B S hS := ⟨𝒳, h𝒳⟩
  let a' : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳' := Bicategory.InducedBicategory.mkHom a
  let f' : 𝒳' ⟶ schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS))) :=
    Bicategory.InducedBicategory.mkHom f
  have hZl : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map
      (schemeMapOfFunctor B S hS (a ≫ f).hom)) :=
    locallyOfFinitePresentation_siteMap_of_isLocallyOfFinitePresentation B S hS (a' ≫ f')
      (AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS a' f'
        (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS a' ha) hf)
  obtain ⟨c, W, g, s, m, θ, hc, hW, hgs, hge, hse, hθ⟩ :=
    exists_affine_etale_chart_cover a hrep hprop (inferInstance : IsAffine _) y' hy'
  have hterm : ∀ {X : BigFppfOver B S hS} (u v : X ⟶ Over.mk (𝟙 (B.obj hS))), u = v :=
    Over.mkIdTerminal.hom_ext
  let τ : T' ⟶ Over.mk (𝟙 (B.obj hS)) := Over.mkIdTerminal.from T'
  let k₁ : c ⟶ pullback (s ≫ schemeMapOfFunctor B S hS (a ≫ f).hom) τ :=
    pullback.lift m (g ≫ k) (hterm _ _)
  obtain ⟨c', W'', r, s'', m'', hc', hW'', hrs, hre, hs''e, hm''⟩ :=
    BigFppfOver.exists_affine_surjective_etale_refinement_factor (inferInstance : IsAffine _) g
      hgs hge k₁
  have hm''s : m'' ≫ s'' ≫ pullback.snd _ _ = r ≫ g ≫ k := by
    rw [← Category.assoc, hm'', Category.assoc, pullback.lift_snd]
  have hm''f : m'' ≫ s'' ≫ pullback.fst _ _ = r ≫ m := by
    rw [← Category.assoc, hm'', Category.assoc, pullback.lift_fst]
  have hl : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map
      (s ≫ schemeMapOfFunctor B S hS (a ≫ f).hom)) := by
    rw [Functor.map_comp]
    infer_instance
  exact exists_lift_of_fppf_chart h𝒳 f hf a hafs s hse τ s'' hs''e
    (finitePresentation_sectionsAlg_of_etale_pullback _ τ s'') (hterm _ _) i hi j l k hpb
    hkf hks hkp g m r hrs hre m'' hm''s hm''f x hx y α hα y' β hβ θ hθ

end GroupoidLift

/-- **Stacks 0DNU.** Let `𝒳` be an algebraic stack over `S` whose structure morphism is locally of
finite presentation, and let `(A' → A, x)` be a deformation situation, `A' → A` being
`Γ(U') → Γ(U)` for the closed immersion `i : U ⟶ U'` of affines and `x` an object over `U`. If
there are a faithfully flat finitely presented `A'`-algebra `B' = Γ(V')` and an object `y'` of `𝒳`
over `B'` lifting the restriction `y` of `x` to `B' ⊗_{A'} A = Γ(V)`, then there is an object `x'`
over `A'` lifting `x`. -/
@[stacks 0DNU]
theorem exists_lift_of_fppf_lift_of_isDeformationSituation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (f : 𝒳 ⟶ schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS))))
    (hf : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f)
    (U U' V V' : BigAffineFppf B S hS)
    (i : U ⟶ U') (j : V ⟶ U) (l : V ⟶ V') (k : V' ⟶ U')
    (hsq : j ≫ i = l ≫ k)
    (hpb : IsPushout
      ((BigAffineFppf.toScheme B S hS).map i).appTop
      ((BigAffineFppf.toScheme B S hS).map k).appTop
      ((BigAffineFppf.toScheme B S hS).map j).appTop
      ((BigAffineFppf.toScheme B S hS).map l).appTop)
    (hi : Deformation.Artin.IsDeformationSituation
      ((BigAffineFppf.toScheme B S hS).map i).appTop.hom)
    (hff : ((BigAffineFppf.toScheme B S hS).map k).appTop.hom.FaithfullyFlat)
    (hfp : ((BigAffineFppf.toScheme B S hS).map k).appTop.hom.FinitePresentation)
    (x : 𝒳.val.obj)
    (hx : 𝒳.val.p.obj x = (BigAffineFppf.inclusion B S hS).obj U)
    (y : 𝒳.val.obj)
    (_hy : 𝒳.val.p.obj y = (BigAffineFppf.inclusion B S hS).obj V)
    (α : y ⟶ x)
    (hα : 𝒳.val.p.IsStronglyCartesian ((BigAffineFppf.inclusion B S hS).map j) α)
    (hlift : ∃ (y' : 𝒳.val.obj)
      (_hy' : 𝒳.val.p.obj y' = (BigAffineFppf.inclusion B S hS).obj V')
      (β : y ⟶ y'), 𝒳.val.p.IsStronglyCartesian ((BigAffineFppf.inclusion B S hS).map l) β) :
    ∃ (x' : 𝒳.val.obj)
      (_hx' : 𝒳.val.p.obj x' = (BigAffineFppf.inclusion B S hS).obj U')
      (β : x ⟶ x'), 𝒳.val.p.IsStronglyCartesian ((BigAffineFppf.inclusion B S hS).map i) β := by
  obtain ⟨y', hy', β, hβ⟩ := hlift
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj U')) :=
    U'.property
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj U)) :=
    U.property
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj V')) :=
    V'.property
  have hpbS := isPullback_of_isPushout_appTop hpb
  have hpbO : IsPullback ((BigAffineFppf.inclusion B S hS).map j)
      ((BigAffineFppf.inclusion B S hS).map l) ((BigAffineFppf.inclusion B S hS).map i)
      ((BigAffineFppf.inclusion B S hS).map k) :=
    IsPullback.of_map (BigFppfOver.toScheme B S hS)
      (by rw [← Functor.map_comp, ← Functor.map_comp, hsq]) hpbS
  have hk := (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine
    ((BigAffineFppf.toScheme B S hS).map k)).mpr hff
  have hkp : LocallyOfFinitePresentation ((BigAffineFppf.toScheme B S hS).map k) :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mpr hfp
  obtain ⟨x', hx', φ, hφ⟩ := GroupoidLift.exists_lift_of_fppf_lift_core h𝒳 f hf
    ((BigAffineFppf.inclusion B S hS).map i) hi ((BigAffineFppf.inclusion B S hS).map j)
    ((BigAffineFppf.inclusion B S hS).map l) ((BigAffineFppf.inclusion B S hS).map k) hpbO
    hk.1 hk.2 hkp x hx y α hα.toIsHomLift y' hy' β hβ.toIsHomLift
  exact ⟨x', hx', φ, 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift _ φ⟩

end AlgebraicGeometry.Stack

end
