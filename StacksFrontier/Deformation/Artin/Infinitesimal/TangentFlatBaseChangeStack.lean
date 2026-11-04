module

public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentBaseChangeStack

/-!
# Flat base change of tangent modules of an algebraic stack: the assembly

For an algebraic stack `𝒳` locally of finite presentation over `S`, an object `x` over `Spec A`,
a flat `A`-algebra `C` and `y = x|_{Spec C}`, the map of Stacks 07YA induces
`C ⊗_A T_x(M) ≅ T_y(C ⊗_A M)` (Stacks 0DNT).

The proof follows the source. Over a faithfully flat finitely presented chart cover `A → A₁`
(`AlgebraicGeometry.Stack.GroupoidLift.exists_chartPoint_cover`) the object `x` becomes the
object of a chart point `w : P → A₁`, and so do its pullbacks to `A₂ = A₁ ⊗_A A₁`,
`C₁ = A₁ ⊗_A C` and `C₂ = A₂ ⊗_A C`; at chart points flat base change holds
(`Deformation.Artin.ChartLift.isTangentBaseChangeIso_chart_tensor`), and it descends along the
cover (`Deformation.Artin.isTangentBaseChangeIso_of_tensorCover`). The arrows between these
objects that the descent needs are produced from the universal property of strongly cartesian
arrows, all arrows of a category fibred in groupoids being strongly cartesian.

## Main results

* `Deformation.Artin.isTangentBaseChangeIso_of_isAlgebraicStack`: the base change map is an
  isomorphism `C ⊗_A T_x(M) ≅ T_y(C ⊗_A M)`.
* `Deformation.Artin.exists_tangentFlatBaseChange`: **Stacks 0DNT**, with the isomorphism
  described on pure tensors by cartesian pullback of lifts along `Spec C[C ⊗_A M] → Spec A[M]`.

## References

* [Stacks Project, Tag 0DNT](https://stacks.math.columbia.edu/tag/0DNT)
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory Opposite Limits AlgebraicGeometry CategoryTheory.Functor
open AlgebraicGeometry.Stack AlgebraicGeometry.Stack.GroupoidLift
open AlgebraicGeometry.Stack.GroupoidLift.StackChart AlgebraicGeometry.Space.ChartDescent
open Deformation.Artin.ChartLift

namespace Deformation.Artin

universe w u

/-- Two factorizations of one ring map give the same composite of morphisms of spectra. -/
theorem algebraOverMapOfRingHom_comp_eq {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {A₁ A₂ A₃ A₄ : Type u} [CommRing A₁] [CommRing A₂] [CommRing A₃]
    [CommRing A₄] {f₁ : A₁ →+* A₂} {f₂ : A₂ →+* A₄} {g₁ : A₁ →+* A₃} {g₂ : A₃ →+* A₄}
    (h : f₂.comp f₁ = g₂.comp g₁)
    {t₁ : Spec (.of A₁) ⟶ S} {t₂ : Spec (.of A₂) ⟶ S} {t₃ : Spec (.of A₃) ⟶ S}
    {t₄ : Spec (.of A₄) ⟶ S} {h₁ : B.Contains (Spec (.of A₁))} {h₂ : B.Contains (Spec (.of A₂))}
    {h₃ : B.Contains (Spec (.of A₃))} {h₄ : B.Contains (Spec (.of A₄))}
    (hf₁ : Spec.map (CommRingCat.ofHom f₁) ≫ t₁ = t₂)
    (hf₂ : Spec.map (CommRingCat.ofHom f₂) ≫ t₂ = t₄)
    (hg₁ : Spec.map (CommRingCat.ofHom g₁) ≫ t₁ = t₃)
    (hg₂ : Spec.map (CommRingCat.ofHom g₂) ≫ t₃ = t₄) :
    algebraOverMapOfRingHom f₂ B S hS t₂ t₄ h₂ h₄ hf₂ ≫
        algebraOverMapOfRingHom f₁ B S hS t₁ t₂ h₁ h₂ hf₁ =
      algebraOverMapOfRingHom g₂ B S hS t₃ t₄ h₃ h₄ hg₂ ≫
        algebraOverMapOfRingHom g₁ B S hS t₁ t₃ h₁ h₃ hg₁ := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom f₂) ≫ Spec.map (CommRingCat.ofHom f₁) =
    Spec.map (CommRingCat.ofHom g₂) ≫ Spec.map (CommRingCat.ofHom g₁)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, h]

section ChartCover

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
  {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {toSC : Spec (.of C) ⟶ S} {hC : B.Contains (Spec (.of C))}
  {T' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  (e : ringOf B S hS T' →+* A) (he : Function.Bijective e)

variable {U₀ : BigFppfOver B S hS} {a : Stack.schemeFibredCategory B S hS U₀ ⟶ 𝒳}
  {P : SmallAlg (ringOf B S hS T') B.cutoff} {ι : specOver P ⟶ U₀}
  {Q : SmallAlg (ringOf B S hS T') B.cutoff} {b : Chart (stackArr a ι) Q.obj}
  {sV tV : P.obj →ₐ[(ringOf B S hS T')] Q.obj}
  (hb : b.IsFormallyEtale)
  (hsV : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q.obj →ₐ[(ringOf B S hS T')] D.obj),
      (b.app D v).src = v.comp sV)
  (htV : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q.obj →ₐ[(ringOf B S hS T')] D.obj),
      (b.app D v).tgt = v.comp tV)
  (ha : Stack.IsFormallySmoothOnObjects B S hS (Stack.schemeFibredCategory B S hS U₀) 𝒳 a)
  (hι : ∀ {C' C : SmallAlg (ringOf B S hS T') B.cutoff} (e : SqZero C' C) (m' : specOver C' ⟶ U₀)
    (u : P.obj →ₐ[(ringOf B S hS T')] C.obj), specOverMap e.q ≫ m' = specOverMap (SmallAlg.homMk u)
        ≫ ι →
      ∃ u' : P.obj →ₐ[(ringOf B S hS T')] C'.obj, e.q.hom.hom.comp u' = u ∧
        specOverMap (SmallAlg.homMk u') ≫ ι = m')
  {X : SmallAlg (ringOf B S hS T') B.cutoff} [Algebra A X.obj]
  (hAX : ∀ r, algebraMap A X.obj (e r) = algebraMap (ringOf B S hS T') X.obj r)
  (hXX : Cardinal.mk (X.obj ⊗[A] X.obj) < B.cutoff)
  (hXC : Cardinal.mk (X.obj ⊗[A] C) < B.cutoff)
  (hXXC : Cardinal.mk ((X.obj ⊗[A] X.obj) ⊗[A] C) < B.cutoff)
  {w : P.obj →ₐ[(ringOf B S hS T')] X.obj} {ε : Q.obj →ₐ[(ringOf B S hS T')] X.obj}
  (hε : b.app X ε = Arr.idt w)

include he hb hsV htV ha hι hAX hε in
/-- **Flat base change descends along a chart cover.** With `A₁ = X` the ring of a chart point
`w` over `Spec A`, `A₂ = X ⊗_A X`, `C₁ = X ⊗_A C` and `C₂ = A₂ ⊗_A C`, the objects `x₁`, `x₂`,
`y₁`, `y₂` of `isTangentBaseChangeIso_of_tensorCover` taken to be the chart points over these
rings and `x₁ ← y₁`, `x₂ ← y₂` the arrows of the chart, the hypotheses of that lemma on the
chart points hold, so flat base change for `x` follows from the compatibilities of the arrows. -/
theorem isTangentBaseChangeIso_of_chartTensorCover [Module.Flat A C]
    [Module.FinitePresentation P.obj Ω[P.obj⁄(ringOf B S hS T')]]
    [Module.FinitePresentation Q.obj Ω[Q.obj⁄(ringOf B S hS T')]]
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (f : 𝒳 ⟶ Stack.schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS))))
    (hfS : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f)
    (hFl : Flat (Spec.map (CommRingCat.ofHom (algebraMap A X.obj))))
    (hSu : Surjective (Spec.map (CommRingCat.ofHom (algebraMap A X.obj))))
    (hLp : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap A X.obj))))
    {x y : 𝒳.val.obj} {hx : 𝒳.val.p.obj x = algebraOver A B S hS toS hA}
    {hy : 𝒳.val.p.obj y = algebraOver C B S hS toSC hC}
    {hf₀₁ : Spec.map (CommRingCat.ofHom (algebraMap A X.obj)) ≫ toS = toSOf X}
    {hfa : Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : X.obj →ₐ[A] X.obj ⊗[A] X.obj).toRingHom) ≫
        toSOf X = toSOf (tensorAlg X X.obj hXX)}
    {hfb : Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : X.obj →ₐ[A] X.obj ⊗[A] X.obj).toRingHom) ≫
        toSOf X = toSOf (tensorAlg X X.obj hXX)}
    {hf : Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ toS = toSC}
    {hfc₀₁ : Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).toRingHom) ≫ toSC = toSOf
          (tensorAlg X C hXC)}
    {hfa' : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
      (Algebra.TensorProduct.includeLeft : X.obj →ₐ[A] X.obj ⊗[A] X.obj)
        (AlgHom.id A C)).toRingHom) ≫ toSOf (tensorAlg X C hXC) = toSOf (tensorAlg (tensorAlg X
            X.obj hXX) C hXXC)}
    {hfb' : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
      (Algebra.TensorProduct.includeRight : X.obj →ₐ[A] X.obj ⊗[A] X.obj)
        (AlgHom.id A C)).toRingHom) ≫ toSOf (tensorAlg X C hXC) = toSOf (tensorAlg (tensorAlg X
            X.obj hXX) C hXXC)}
    {φ₀₁ : ξ a ι w ⟶ x}
    (hφ₀₁ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom (algebraMap A X.obj) B S hS toS
      (toSOf X) hA (contains_spec X) hf₀₁) φ₀₁)
    {α β : ξ a ι ((tensorAlgHom X X.obj hXX).hom.hom.comp w) ⟶ ξ a ι w}
    (hα : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom
      (Algebra.TensorProduct.includeLeft : X.obj →ₐ[A] X.obj ⊗[A] X.obj).toRingHom
        B S hS (toSOf X) (toSOf (tensorAlg X X.obj hXX)) (contains_spec X) (contains_spec
            (tensorAlg X X.obj hXX)) hfa) α)
    (hβ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom
      (Algebra.TensorProduct.includeRight : X.obj →ₐ[A] X.obj ⊗[A] X.obj).toRingHom
        B S hS (toSOf X) (toSOf (tensorAlg X X.obj hXX)) (contains_spec X) (contains_spec
            (tensorAlg X X.obj hXX)) hfb) β)
    {φ : y ⟶ x}
    (hφ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom (algebraMap A C) B S hS toS toSC hA hC hf) φ)
    {φ₀₁' : ξ a ι ((tensorAlgHom X C hXC).hom.hom.comp w) ⟶ y}
    (hφ₀₁' : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom
      (Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).toRingHom
        B S hS toSC (toSOf (tensorAlg X C hXC)) hC (contains_spec (tensorAlg X C hXC)) hfc₀₁) φ₀₁')
    {α' β' : ξ a ι ((tensorAlgHom (tensorAlg X X.obj hXX) C hXXC).hom.hom.comp ((tensorAlgHom X
        X.obj hXX).hom.hom.comp w)) ⟶
      ξ a ι ((tensorAlgHom X C hXC).hom.hom.comp w)}
    (hα' : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom (Algebra.TensorProduct.map
      (Algebra.TensorProduct.includeLeft : X.obj →ₐ[A] X.obj ⊗[A] X.obj) (AlgHom.id A C)).toRingHom
        B S hS (toSOf (tensorAlg X C hXC)) (toSOf (tensorAlg (tensorAlg X X.obj hXX) C hXXC))
            (contains_spec (tensorAlg X C hXC)) (contains_spec (tensorAlg (tensorAlg X X.obj hXX) C
            hXXC)) hfa') α')
    (hβ' : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom (Algebra.TensorProduct.map
      (Algebra.TensorProduct.includeRight : X.obj →ₐ[A] X.obj ⊗[A] X.obj)
        (AlgHom.id A C)).toRingHom
        B S hS (toSOf (tensorAlg X C hXC)) (toSOf (tensorAlg (tensorAlg X X.obj hXX) C hXXC))
            (contains_spec (tensorAlg X C hXC)) (contains_spec (tensorAlg (tensorAlg X X.obj hXX) C
            hXXC)) hfb') β')
    (hγ : α ≫ φ₀₁ = β ≫ φ₀₁) (hγ' : α' ≫ φ₀₁' = β' ≫ φ₀₁')
    (hsq₀₁ : φ₀₁' ≫ φ = trans a ι (tensorAlgHom X C hXC) w ≫ φ₀₁)
    (hsqa : α' ≫ trans a ι (tensorAlgHom X C hXC) w = trans a ι (tensorAlgHom (tensorAlg X X.obj
        hXX) C hXXC) ((tensorAlgHom X X.obj hXX).hom.hom.comp w) ≫ α)
    (hsqb : β' ≫ trans a ι (tensorAlgHom X C hXC) w = trans a ι (tensorAlgHom (tensorAlg X X.obj
        hXX) C hXXC) ((tensorAlgHom X X.obj hXX).hom.hom.comp w) ≫ β)
    (M : SiteModule A B) (hN : IsSiteModule C B (ModuleCat.of C (C ⊗[A] M.obj)))
    (F : TangentFunctorData A B S hS toS hA 𝒳.val.p x hx)
    (G : TangentFunctorData C B S hS toSC hC 𝒳.val.p y hy) :
    IsTangentBaseChangeIso 𝒳.isFiberedInGroupoids hf φ hφ F G (M := M) (N := ⟨_, hN⟩)
      (tensorCoeff M.obj) := by
  have hAX₂ : ∀ r, algebraMap A ((tensorAlg X X.obj hXX)).obj (e r) = algebraMap (ringOf B S hS T')
      ((tensorAlg X X.obj hXX)).obj r :=
    fun r ↦ congrArg (· ⊗ₜ[A] (1 : X.obj)) (hAX r)
  have hv₂ : b.app (tensorAlg X X.obj hXX) ((tensorAlgHom X X.obj hXX).hom.hom.comp ε) = Arr.idt
      ((tensorAlgHom X X.obj hXX).hom.hom.comp w) :=
    chart_app_comp _ hε
  let F₁ := chartTangentData (a := a) (ι := ι) (w := w)
    (fun M _ _ h₁ h₂ ↦ rel_iff_of_chart hb hsV htV hε M h₁ h₂) ha hι
  let F₂ := chartTangentData (a := a) (ι := ι) (w := ((tensorAlgHom X X.obj hXX).hom.hom.comp w))
    (fun M _ _ h₁ h₂ ↦ rel_iff_of_chart hb hsV htV hv₂ M h₁ h₂) ha hι
  let G₁ := chartTangentData (a := a) (ι := ι) (w := (tensorAlgHom X C hXC).hom.hom.comp w)
    (fun M _ _ h₁ h₂ ↦ rel_iff_of_chart hb hsV htV (chart_app_comp _ hε) M h₁ h₂) ha hι
  let G₂ := chartTangentData (a := a) (ι := ι) (w := (tensorAlgHom (tensorAlg X X.obj hXX) C
      hXXC).hom.hom.comp ((tensorAlgHom X X.obj hXX).hom.hom.comp w))
    (fun M _ _ h₁ h₂ ↦ rel_iff_of_chart hb hsV htV (chart_app_comp _ hv₂) M h₁ h₂) ha hι
  have h₁ := isTangentBaseChangeIso_chart_tensor e he hb hsV htV
    hAX C hXC M (toSOf_comp (tensorAlgHom X C hXC))
    (trans_isHomLift a ι (tensorAlgHom X C hXC) w) hε ha hι F₁ G₁
  have h₂ := isTangentBaseChangeIso_chart_tensor e he hb hsV htV
    hAX₂ C hXXC M (toSOf_comp (tensorAlgHom (tensorAlg X X.obj hXX) C hXXC))
    (trans_isHomLift a ι (tensorAlgHom (tensorAlg X X.obj hXX) C hXXC) ((tensorAlgHom X X.obj
        hXX).hom.hom.comp w)) hv₂ ha hι F₂ G₂
  exact isTangentBaseChangeIso_of_tensorCover (A := A) (A₁ := X.obj) (C := C) (M := M)
    (hf₀₁ := hf₀₁) (hfa := hfa) (hfb := hfb) (hf := hf) (hfc₀₁ := hfc₀₁) (hfa' := hfa')
    (hfb' := hfb') (hφ₀₁ := hφ₀₁) (hα := hα) (hβ := hβ) (hφ := hφ) (hφ₀₁' := hφ₀₁')
    (hα' := hα') (hβ' := hβ') (F := F) (G := G) (F₁ := F₁) (F₂ := F₂) (G₁ := G₁) (G₂ := G₂)
    (hN := hN) h𝒳 f hfS hFl hSu hLp hγ hγ' hsq₀₁ hsqa hsqb h₁ h₂

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
include hAX in
/-- `x ↦ 1 ⊗ x` is a map of `Γ(T')`-algebras `X → X ⊗_A X`. -/
theorem includeRight_commutes (r : (ringOf B S hS T')) :
    (Algebra.TensorProduct.includeRight : X.obj →ₐ[A] X.obj ⊗[A] X.obj) (algebraMap (ringOf B S hS
        T') X.obj r) =
      algebraMap (ringOf B S hS T') (tensorAlg X X.obj hXX).obj r :=
  (tensorRight e hAX X.obj (fun r ↦ (hAX r).symm) hXX).commutes r

/-- `x ↦ 1 ⊗ x`, the second inclusion `X → X ⊗_A X` of small `Γ(T')`-algebras. -/
noncomputable abbrev tensorAlgHomRight : X ⟶ (tensorAlg X X.obj hXX) :=
  SmallAlg.homMk (tensorRight e hAX X.obj (fun r ↦ (hAX r).symm) hXX)

/-- `x ⊗ c ↦ (x ⊗ 1) ⊗ c`, as a map of small `Γ(T')`-algebras `X ⊗_A C → (X ⊗_A X) ⊗_A C`. -/
noncomputable abbrev tensorAlgMapLeft : (tensorAlg X C hXC) ⟶ (tensorAlg (tensorAlg X X.obj hXX) C
    hXXC) :=
  SmallAlg.homMk
    { toRingHom := (Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeLeft : X.obj →ₐ[A] X.obj ⊗[A] X.obj) (AlgHom.id A
            C)).toRingHom
      commutes' := fun r ↦ by
        change Algebra.TensorProduct.map _ _ (algebraMap (ringOf B S hS T') (X.obj ⊗[A] C) r) =
          algebraMap (ringOf B S hS T') ((X.obj ⊗[A] X.obj) ⊗[A] C) r
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
          Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.algebraMap_apply]
        rfl }

/-- `x ⊗ c ↦ (1 ⊗ x) ⊗ c`, as a map of small `Γ(T')`-algebras `X ⊗_A C → (X ⊗_A X) ⊗_A C`. -/
noncomputable abbrev tensorAlgMapRight : (tensorAlg X C hXC) ⟶ (tensorAlg (tensorAlg X X.obj hXX) C
    hXXC) :=
  SmallAlg.homMk
    { toRingHom := (Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeRight : X.obj →ₐ[A] X.obj ⊗[A] X.obj)
          (AlgHom.id A C)).toRingHom
      commutes' := fun r ↦ by
        change Algebra.TensorProduct.map _ _ (algebraMap (ringOf B S hS T') (X.obj ⊗[A] C) r) =
          algebraMap (ringOf B S hS T') ((X.obj ⊗[A] X.obj) ⊗[A] C) r
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
          Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
        exact congrArg (· ⊗ₜ[A] (1 : C)) (includeRight_commutes e hAX hXX r) }

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- `tensorAlgMapLeft` sends `z ⊗ 1` to `(z ⊗ 1) ⊗ 1`. -/
theorem tensorAlgMapLeft_tmul (z : X.obj) :
    (tensorAlgMapLeft hXX hXC hXXC).hom.hom (z ⊗ₜ[A] (1 : C)) =
      (tensorAlgHom X X.obj hXX).hom.hom z ⊗ₜ[A] (1 : C) := by
  change Algebra.TensorProduct.map
    (Algebra.TensorProduct.includeLeft : X.obj →ₐ[A] X.obj ⊗[A] X.obj) (AlgHom.id A C)
      (z ⊗ₜ[A] (1 : C)) = (z ⊗ₜ[A] (1 : X.obj)) ⊗ₜ[A] (1 : C)
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rfl

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- `tensorAlgMapRight` sends `z ⊗ 1` to `(1 ⊗ z) ⊗ 1`. -/
theorem tensorAlgMapRight_tmul (z : X.obj) :
    (tensorAlgMapRight e hAX hXX hXC hXXC).hom.hom (z ⊗ₜ[A] (1 : C)) =
      (tensorAlgHomRight e hAX hXX).hom.hom z ⊗ₜ[A] (1 : C) := by
  change Algebra.TensorProduct.map
    (Algebra.TensorProduct.includeRight : X.obj →ₐ[A] X.obj ⊗[A] X.obj) (AlgHom.id A C)
      (z ⊗ₜ[A] (1 : C)) = ((1 : X.obj) ⊗ₜ[A] z) ⊗ₜ[A] (1 : C)
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rfl

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The two maps `X ⊗_A C ⇉ (X ⊗_A X) ⊗_A C` agree on `C`. -/
theorem tensorAlgMapLeft_comp_includeRight :
    ((tensorAlgMapLeft hXX hXC hXXC).hom.hom : (tensorAlg X C hXC).obj →+* (tensorAlg (tensorAlg X
        X.obj hXX) C hXXC).obj).comp (Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A]
        C).toRingHom =
      ((tensorAlgMapRight e hAX hXX hXC hXXC).hom.hom : (tensorAlg X C hXC).obj →+* (tensorAlg
          (tensorAlg X X.obj hXX) C hXXC).obj).comp (Algebra.TensorProduct.includeRight : C →ₐ[A]
          X.obj ⊗[A] C).toRingHom := by
  refine RingHom.ext fun c ↦ ?_
  change Algebra.TensorProduct.map _ _ ((1 : X.obj) ⊗ₜ[A] c) =
    Algebra.TensorProduct.map _ _ ((1 : X.obj) ⊗ₜ[A] c)
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_one, map_one]

include hAX in
/-- **The second arrow `x₂ ⟶ x₁` of the cover.** The chart point over `X ⊗_A X` maps to the
chart point over `X` along the first inclusion; the arrow along the second inclusion is the
factorization of `x₂ ⟶ x₁ ⟶ x` through the strongly cartesian `x₁ ⟶ x`. -/
theorem exists_isHomLift_includeRight {x : 𝒳.val.obj}
    {hf₀₁ : Spec.map (CommRingCat.ofHom (algebraMap A X.obj)) ≫ toS = toSOf X}
    {φ₀₁ : ξ a ι w ⟶ x}
    (hφ₀₁ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom (algebraMap A X.obj) B S hS toS
      (toSOf X) hA (contains_spec X) hf₀₁) φ₀₁) :
    ∃ β : ξ a ι ((tensorAlgHom X X.obj hXX).hom.hom.comp w) ⟶ ξ a ι w, 𝒳.val.p.IsHomLift
        (algebraOverMapOfRingHom
      (Algebra.TensorProduct.includeRight : X.obj →ₐ[A] X.obj ⊗[A] X.obj).toRingHom
        B S hS (toSOf X) (toSOf (tensorAlg X X.obj hXX)) (contains_spec X) (contains_spec
            (tensorAlg X X.obj hXX))
        (toSOf_comp (tensorAlgHomRight e hAX hXX))) β ∧
      trans a ι (tensorAlgHom X X.obj hXX) w ≫ φ₀₁ = β ≫ φ₀₁ := by
  have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift (algebraOverMapOfRingHom
    (algebraMap A X.obj) B S hS toS (toSOf X) hA (contains_spec X) hf₀₁) φ₀₁
  have : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom
      (Algebra.TensorProduct.includeLeft : X.obj →ₐ[A] X.obj ⊗[A] X.obj).toRingHom
        B S hS (toSOf X) (toSOf (tensorAlg X X.obj hXX)) (contains_spec X) (contains_spec
            (tensorAlg X X.obj hXX))
        (toSOf_comp (tensorAlgHom X X.obj hXX))) (trans a ι (tensorAlgHom X X.obj hXX) w) :=
    trans_isHomLift a ι (tensorAlgHom X X.obj hXX) w
  have hbase := algebraOverMapOfRingHom_comp_eq (B := B) (S := S) (hS := hS)
    (h₁ := hA) (h₂ := contains_spec X) (h₃ := contains_spec X) (h₄ := contains_spec (tensorAlg X
        X.obj hXX))
    (f₁ := algebraMap A X.obj) (g₁ := algebraMap A X.obj)
    (f₂ := (Algebra.TensorProduct.includeLeft : X.obj →ₐ[A] X.obj ⊗[A] X.obj).toRingHom)
    (g₂ := (Algebra.TensorProduct.includeRight : X.obj →ₐ[A] X.obj ⊗[A] X.obj).toRingHom)
    (RingHom.ext fun r ↦
      ((Algebra.TensorProduct.includeLeft : X.obj →ₐ[A] X.obj ⊗[A] X.obj).commutes r).trans
        ((Algebra.TensorProduct.includeRight : X.obj →ₐ[A] X.obj ⊗[A] X.obj).commutes r).symm)
    hf₀₁ (toSOf_comp (tensorAlgHom X X.obj hXX)) hf₀₁ (toSOf_comp (tensorAlgHomRight e hAX hXX))
  obtain ⟨β, hβ, hfac⟩ := (IsStronglyCartesian.universal_property 𝒳.val.p _ φ₀₁ _ _ hbase
    (trans a ι (tensorAlgHom X X.obj hXX) w ≫ φ₀₁)).exists
  exact ⟨β, hβ, hfac.symm⟩

/-- **The arrow `y₁ ⟶ y` of the cover of `y`.** The composite `y₁ ⟶ x₁ ⟶ x` factors through
the strongly cartesian `y ⟶ x` over `C → X ⊗_A C`. -/
theorem exists_isHomLift_tensorIncludeRight {x y : 𝒳.val.obj}
    {hf₀₁ : Spec.map (CommRingCat.ofHom (algebraMap A X.obj)) ≫ toS = toSOf X}
    {φ₀₁ : ξ a ι w ⟶ x}
    (hφ₀₁ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom (algebraMap A X.obj) B S hS toS
      (toSOf X) hA (contains_spec X) hf₀₁) φ₀₁)
    {hf : Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ toS = toSC} {φ : y ⟶ x}
    (hφ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom (algebraMap A C) B S hS toS toSC hA hC hf) φ)
    (hfc₀₁ : Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).toRingHom) ≫ toSC = toSOf
          (tensorAlg X C hXC)) :
    ∃ φ₀₁' : ξ a ι ((tensorAlgHom X C hXC).hom.hom.comp w) ⟶ y,
      𝒳.val.p.IsHomLift (algebraOverMapOfRingHom
        (Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).toRingHom
          B S hS toSC (toSOf (tensorAlg X C hXC)) hC (contains_spec (tensorAlg X C hXC)) hfc₀₁)
              φ₀₁' ∧
      φ₀₁' ≫ φ = trans a ι (tensorAlgHom X C hXC) w ≫ φ₀₁ := by
  have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift
    (algebraOverMapOfRingHom (algebraMap A C) B S hS toS toSC hA hC hf) φ
  have : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom (algebraMap X.obj (X.obj ⊗[A] C))
      B S hS (toSOf X) (toSOf (tensorAlg X C hXC)) (contains_spec X) (contains_spec (tensorAlg X C
          hXC))
      (toSOf_comp (tensorAlgHom X C hXC))) (trans a ι (tensorAlgHom X C hXC) w) :=
    trans_isHomLift a ι (tensorAlgHom X C hXC) w
  have hbase := algebraOverMapOfRingHom_comp_eq (B := B) (S := S) (hS := hS)
    (h₁ := hA) (h₂ := contains_spec X) (h₃ := hC) (h₄ := contains_spec (tensorAlg X C hXC))
    (f₁ := algebraMap A X.obj) (g₁ := algebraMap A C)
    (f₂ := algebraMap X.obj (X.obj ⊗[A] C))
    (g₂ := (Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).toRingHom)
    (RingHom.ext fun r ↦
      ((Algebra.TensorProduct.includeLeft : X.obj →ₐ[A] X.obj ⊗[A] C).commutes r).trans
        ((Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).commutes r).symm)
    hf₀₁ (toSOf_comp (tensorAlgHom X C hXC)) hf hfc₀₁
  exact (IsStronglyCartesian.universal_property 𝒳.val.p _ φ _ _ hbase _).exists

/-- **An arrow `y₂ ⟶ y₁` over an arrow `x₂ ⟶ x₁`.** For `g : X → X ⊗_A X` and an arrow
`x₂ ⟶ x₁` over it, the composite `y₂ ⟶ x₂ ⟶ x₁` factors through the strongly cartesian
`y₁ ⟶ x₁` over `X ⊗_A C → (X ⊗_A X) ⊗_A C`. -/
theorem exists_isHomLift_tensorMap (g : X ⟶ (tensorAlg X X.obj hXX)) (g' : (tensorAlg X C hXC) ⟶
    (tensorAlg (tensorAlg X X.obj hXX) C hXXC))
    (hg : ∀ z : X.obj, g'.hom.hom (z ⊗ₜ[A] (1 : C)) = g.hom.hom z ⊗ₜ[A] (1 : C))
    {α : ξ a ι ((tensorAlgHom X X.obj hXX).hom.hom.comp w) ⟶ ξ a ι w}
    (hα : 𝒳.val.p.IsHomLift (specOverMap g) α) :
    ∃ α' : ξ a ι ((tensorAlgHom (tensorAlg X X.obj hXX) C hXXC).hom.hom.comp ((tensorAlgHom X X.obj
        hXX).hom.hom.comp w)) ⟶
        ξ a ι ((tensorAlgHom X C hXC).hom.hom.comp w),
      𝒳.val.p.IsHomLift (specOverMap g') α' ∧
      α' ≫ trans a ι (tensorAlgHom X C hXC) w = trans a ι (tensorAlgHom (tensorAlg X X.obj hXX) C
          hXXC) ((tensorAlgHom X X.obj hXX).hom.hom.comp w) ≫ α := by
  have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift
    (specOverMap (tensorAlgHom X C hXC)) (trans a ι (tensorAlgHom X C hXC) w)
  have hbase : specOverMap (tensorAlgHom (tensorAlg X X.obj hXX) C hXXC) ≫ specOverMap g =
      specOverMap g' ≫ specOverMap (tensorAlgHom X C hXC) := by
    rw [← specOverMap_comp, ← specOverMap_comp]
    congr 1
    exact ObjectProperty.hom_ext _ (CommAlgCat.hom_ext (AlgHom.ext fun z ↦ (hg z).symm))
  exact (IsStronglyCartesian.universal_property 𝒳.val.p _ _ _ _ hbase _).exists

/-- **The two arrows `y₂ ⇉ y₁` agree after `y₁ ⟶ y`**, since they do after `y ⟶ x`, which is
strongly cartesian. -/
theorem comp_tensorIncludeRight_eq_of_tensorAlgMap {x y : 𝒳.val.obj}
    {hf₀₁ : Spec.map (CommRingCat.ofHom (algebraMap A X.obj)) ≫ toS = toSOf X}
    {φ₀₁ : ξ a ι w ⟶ x} {α β : ξ a ι ((tensorAlgHom X X.obj hXX).hom.hom.comp w) ⟶ ξ a ι w}
    (hγ : α ≫ φ₀₁ = β ≫ φ₀₁)
    {hf : Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ toS = toSC} {φ : y ⟶ x}
    (hφ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom (algebraMap A C) B S hS toS toSC hA hC hf) φ)
    {hfc₀₁ : Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).toRingHom) ≫ toSC = toSOf
          (tensorAlg X C hXC)}
    {φ₀₁' : ξ a ι ((tensorAlgHom X C hXC).hom.hom.comp w) ⟶ y}
    (hφ₀₁' : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom
      (Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).toRingHom
        B S hS toSC (toSOf (tensorAlg X C hXC)) hC (contains_spec (tensorAlg X C hXC)) hfc₀₁) φ₀₁')
    (hsq₀₁ : φ₀₁' ≫ φ = trans a ι (tensorAlgHom X C hXC) w ≫ φ₀₁)
    (g₁ g₂ : (tensorAlg X C hXC) ⟶ (tensorAlg (tensorAlg X X.obj hXX) C hXXC))
    (hg : (g₁.hom.hom : (tensorAlg X C hXC).obj →+* (tensorAlg (tensorAlg X X.obj hXX) C
        hXXC).obj).comp (Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).toRingHom =
      (g₂.hom.hom : (tensorAlg X C hXC).obj →+* (tensorAlg (tensorAlg X X.obj hXX) C
          hXXC).obj).comp (Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).toRingHom)
    {α' β' : ξ a ι ((tensorAlgHom (tensorAlg X X.obj hXX) C hXXC).hom.hom.comp ((tensorAlgHom X
        X.obj hXX).hom.hom.comp w)) ⟶
      ξ a ι ((tensorAlgHom X C hXC).hom.hom.comp w)}
    (hα' : 𝒳.val.p.IsHomLift (specOverMap g₁) α') (hβ' : 𝒳.val.p.IsHomLift (specOverMap g₂) β')
    (hsqa : α' ≫ trans a ι (tensorAlgHom X C hXC) w = trans a ι (tensorAlgHom (tensorAlg X X.obj
        hXX) C hXXC) ((tensorAlgHom X X.obj hXX).hom.hom.comp w) ≫ α)
    (hsqb : β' ≫ trans a ι (tensorAlgHom X C hXC) w = trans a ι (tensorAlgHom (tensorAlg X X.obj
        hXX) C hXXC) ((tensorAlgHom X X.obj hXX).hom.hom.comp w) ≫ β) :
    α' ≫ φ₀₁' = β' ≫ φ₀₁' := by
  have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift
    (algebraOverMapOfRingHom (algebraMap A C) B S hS toS toSC hA hC hf) φ
  have hbase : specOverMap g₁ ≫ algebraOverMapOfRingHom
      (Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).toRingHom
        B S hS toSC (toSOf (tensorAlg X C hXC)) hC (contains_spec (tensorAlg X C hXC)) hfc₀₁ =
      specOverMap g₂ ≫ algebraOverMapOfRingHom
      (Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).toRingHom
        B S hS toSC (toSOf (tensorAlg X C hXC)) hC (contains_spec (tensorAlg X C hXC)) hfc₀₁ := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom
        (g₁.hom.hom : (tensorAlg X C hXC).obj →+* (tensorAlg (tensorAlg X X.obj hXX) C hXXC).obj))
            ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (g₂.hom.hom : (tensorAlg X C hXC).obj →+* (tensorAlg (tensorAlg X X.obj hXX) C hXXC).obj))
            ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hg]
  have : 𝒳.val.p.IsHomLift (specOverMap g₁ ≫ algebraOverMapOfRingHom
      (Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).toRingHom
        B S hS toSC (toSOf (tensorAlg X C hXC)) hC (contains_spec (tensorAlg X C hXC)) hfc₀₁) (β' ≫
            φ₀₁') := by
    rw [hbase]
    exact @IsHomLift.comp _ _ _ _ 𝒳.val.p _ _ _ _ _ _ _ _ β' φ₀₁' hβ' hφ₀₁'
  have : 𝒳.val.p.IsHomLift (specOverMap g₁ ≫ algebraOverMapOfRingHom
      (Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).toRingHom
        B S hS toSC (toSOf (tensorAlg X C hXC)) hC (contains_spec (tensorAlg X C hXC)) hfc₀₁) (α' ≫
            φ₀₁') :=
    @IsHomLift.comp _ _ _ _ 𝒳.val.p _ _ _ _ _ _ _ _ α' φ₀₁' hα' hφ₀₁'
  refine IsStronglyCartesian.ext 𝒳.val.p
    (algebraOverMapOfRingHom (algebraMap A C) B S hS toS toSC hA hC hf) φ (specOverMap g₁ ≫
        algebraOverMapOfRingHom
      (Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).toRingHom
        B S hS toSC (toSOf (tensorAlg X C hXC)) hC (contains_spec (tensorAlg X C hXC)) hfc₀₁) ?_
  simp only [Category.assoc, hsq₀₁, reassoc_of% hsqa, reassoc_of% hsqb, hγ]

end ChartCover

section Assembly

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- A tensor product of two modules below the cutoff is below the cutoff. -/
theorem card_tensorProduct_lt_cutoff {R M N : Type u} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] (hM : Cardinal.mk M < B.cutoff)
    (hN : Cardinal.mk N < B.cutoff) : Cardinal.mk (M ⊗[R] N) < B.cutoff := by
  refine (card_tensorProduct_le R M N).trans_lt (max_lt B.aleph0_lt_cutoff ?_)
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  exact Cardinal.mul_lt_of_lt B.aleph0_lt_cutoff.le hM hN

/-- **Flat base change for the tangent modules of an algebraic stack.** Let `𝒳` be an algebraic
stack over `S` with `𝒳 → S` locally of finite presentation, `A → C` a flat homomorphism of
`S`-algebras, `x` an object over `Spec A` and `φ : y ⟶ x` an arrow over `Spec C ⟶ Spec A`. Then
the map of Stacks 07YA induces `C ⊗_A T_x(M) ≅ T_y(C ⊗_A M)`. -/
theorem isTangentBaseChangeIso_of_isAlgebraicStack {A C : Type u} [CommRing A] [CommRing C]
    [Algebra A C] [Module.Flat A C]
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (f : 𝒳 ⟶ Stack.schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS))))
    (hfS : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f)
    {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
    {toSC : Spec (.of C) ⟶ S} {hC : B.Contains (Spec (.of C))}
    (hf : Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ toS = toSC)
    {x y : 𝒳.val.obj} {hx : 𝒳.val.p.obj x = algebraOver A B S hS toS hA}
    {hy : 𝒳.val.p.obj y = algebraOver C B S hS toSC hC} (φ : y ⟶ x)
    (hφ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom (algebraMap A C) B S hS toS toSC hA hC hf) φ)
    (M : SiteModule A B) (hN : IsSiteModule C B (ModuleCat.of C (C ⊗[A] M.obj)))
    (F : TangentFunctorData A B S hS toS hA 𝒳.val.p x hx)
    (G : TangentFunctorData C B S hS toSC hC 𝒳.val.p y hy) :
    IsTangentBaseChangeIso 𝒳.isFiberedInGroupoids hf φ hφ F G (M := M) (N := ⟨_, hN⟩)
      (tensorCoeff M.obj) := by
  classical
  obtain ⟨U₀, a, P, ι, hP, ha, hι, X, hFF, hFP, w, Q, hΩ, b, hb, sV, tV, hsV, htV, ε, hε, φ₀₁,
    hφ₀₁⟩ := exists_chartPoint_cover h𝒳 f hfS x hx
  let : Algebra A X.obj := baseAlgebra X
  have hAX : ∀ r, algebraMap A X.obj (fromRingOf r) =
      algebraMap (ringOf B S hS (algebraOver A B S hS toS hA)) X.obj r := fun r ↦
    congrArg (algebraMap (ringOf B S hS (algebraOver A B S hS toS hA)) X.obj)
      (congrArg (fun g ↦ g.hom r) (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id)
  obtain ⟨hFl, hSu, hLp⟩ := specMap_algebraMap_fppf hAX
  have hCκ : Cardinal.mk C < B.cutoff := by
    have h : (Spec (.of C)).size < B.cutoff := hC
    rw [Scheme.size_Spec] at h
    exact (le_max_right _ _).trans_lt h
  have hXX : Cardinal.mk (X.obj ⊗[A] X.obj) < B.cutoff :=
    card_tensorProduct_lt_cutoff X.property X.property
  have hXC : Cardinal.mk (X.obj ⊗[A] C) < B.cutoff := card_tensorProduct_lt_cutoff X.property hCκ
  have hXXC : Cardinal.mk ((X.obj ⊗[A] X.obj) ⊗[A] C) < B.cutoff :=
    card_tensorProduct_lt_cutoff hXX hCκ
  have hf₀₁ : Spec.map (CommRingCat.ofHom (algebraMap A X.obj)) ≫ toS = toSOf X :=
    specMap_comp_toS_eq_toSOf' hAX
  have hfc₀₁ : Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).toRingHom) ≫ toSC =
        toSOf (tensorAlg X C hXC) := by
    rw [← hf, ← toSOf_comp (tensorAlgHom X C hXC), ← hf₀₁, ← Category.assoc, ← Category.assoc,
      ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun c ↦
      ((Algebra.TensorProduct.includeRight : C →ₐ[A] X.obj ⊗[A] C).commutes c).trans
        ((Algebra.TensorProduct.includeLeft : X.obj →ₐ[A] X.obj ⊗[A] C).commutes c).symm
  have hφ₀₁' : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom (algebraMap A X.obj) B S hS toS
      (toSOf X) hA (contains_spec X) hf₀₁) φ₀₁ := by
    rwa [algebraOverMapOfRingHom_eq_specOverToBase hAX]
  obtain ⟨β, hβ, hγ⟩ := exists_isHomLift_includeRight fromRingOf hAX hXX hφ₀₁'
  obtain ⟨φ₀₁'', hφ₀₁'', hsq₀₁⟩ := exists_isHomLift_tensorIncludeRight hXC hφ₀₁' hφ hfc₀₁
  obtain ⟨α', hα', hsqa⟩ := exists_isHomLift_tensorMap hXX hXC hXXC (tensorAlgHom X X.obj hXX)
    (tensorAlgMapLeft hXX hXC hXXC) (tensorAlgMapLeft_tmul hXX hXC hXXC)
    (trans_isHomLift a ι _ w)
  obtain ⟨β', hβ', hsqb⟩ := exists_isHomLift_tensorMap hXX hXC hXXC
    (tensorAlgHomRight fromRingOf hAX hXX) (tensorAlgMapRight fromRingOf hAX hXX hXC hXXC)
    (tensorAlgMapRight_tmul fromRingOf hAX hXX hXC hXXC) hβ
  have hγ' := comp_tensorIncludeRight_eq_of_tensorAlgMap hXX hXC hXXC (hf₀₁ := hf₀₁) hγ hφ
    hφ₀₁'' hsq₀₁ _ _
    (tensorAlgMapLeft_comp_includeRight fromRingOf hAX hXX hXC hXXC) hα' hβ' hsqa hsqb
  exact isTangentBaseChangeIso_of_chartTensorCover (hfa := toSOf_comp (tensorAlgHom X X.obj hXX))
    (hfa' := toSOf_comp (tensorAlgMapLeft hXX hXC hXXC))
    (hfb' := toSOf_comp (tensorAlgMapRight fromRingOf hAX hXX hXC hXXC))
    fromRingOf fromRingOf_bijective hb hsV htV ha hι hAX hXX hXC hXXC hε h𝒳 f hfS hFl hSu hLp
    hφ₀₁' (trans_isHomLift a ι (tensorAlgHom X X.obj hXX) w) hβ hφ hφ₀₁'' hα' hβ' hγ hγ' hsq₀₁
    hsqa hsqb M hN F G

/-- The morphism `Spec C[N] ⟶ Spec A[M]` of Stacks 07YA is the spectrum of the ring map
`A[M] → C[N]` which is `f` on `A` and the coefficient map on `M`. -/
theorem exists_squareZeroRing_hom_tangentPullbackBase {A C : Type u} [CommRing A] [CommRing C]
    (f' : A →+* C) {toS : Spec (.of A) ⟶ S} {toSC : Spec (.of C) ⟶ S}
    (hf : Spec.map (CommRingCat.ofHom f') ≫ toS = toSC) {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f').obj N.obj) :
    ∃ r : squareZeroRing A M.obj ⟶ squareZeroRing C N.obj,
      (BigFppfOver.toScheme B S hS).map (tangentPullbackBase (hS := hS) f' hf ψ) = Spec.map r ∧
      ∀ z : TrivSqZeroExt A M.obj,
        (r.hom z).fst = f' z.fst ∧ (r.hom z).snd = restrictScalarsAddHom f' ψ z.snd :=
  ⟨CommRingCat.ofHom (squareZeroRingBaseMap f' (restrictScalarsAddHom f' ψ)
    (restrictScalarsAddHom_smul f' ψ)), rfl, fun _ ↦ ⟨rfl, rfl⟩⟩

/-- **The map of Stacks 07YA on representatives.** Every element `t` of `T_x(M)` is the class of
a lift `a` of `x` whose cartesian pullback `c` along `Spec C[N] ⟶ Spec A[M]` represents the image
of `t`. -/
theorem exists_rep_tangentPullbackHom {A C : Type u} [CommRing A] [CommRing C] (f' : A →+* C)
    {toS : Spec (.of A) ⟶ S} {toSC : Spec (.of C) ⟶ S}
    {hA : B.Contains (Spec (.of A))} {hC : B.Contains (Spec (.of C))}
    (hf : Spec.map (CommRingCat.ofHom f') ≫ toS = toSC)
    {x y : 𝒳.val.obj} {hx : 𝒳.val.p.obj x = algebraOver A B S hS toS hA}
    {hy : 𝒳.val.p.obj y = algebraOver C B S hS toSC hC} (φ : y ⟶ x)
    (hφ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom f' B S hS toS toSC hA hC hf) φ)
    (F : TangentFunctorData A B S hS toS hA 𝒳.val.p x hx)
    (G : TangentFunctorData C B S hS toSC hC 𝒳.val.p y hy)
    {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f').obj N.obj) (t : F.functor.obj M) :
    ∃ (a : (Under.post 𝒳.val.p).Fiber
        (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M)))
      (c : (Under.post 𝒳.val.p).Fiber
        (Under.mk (eqToHom hy ≫ squareZeroArrow C B S hS toSC hC N))),
      Quotient.mk _ a = F.liftEquiv M t ∧
      Quotient.mk _ c =
        G.liftEquiv N (tangentPullbackHom f' hf 𝒳.isFiberedInGroupoids φ hφ F G ψ t) ∧
      ∃ ρ : c.1.right ⟶ a.1.right,
        𝒳.val.p.IsStronglyCartesian (tangentPullbackBase f' hf ψ) ρ ∧
          c.1.hom ≫ ρ = φ ≫ a.1.hom := by
  obtain ⟨u, hu⟩ := Quotient.exists_rep (F.liftEquiv M t)
  exact ⟨u, _, hu, (liftEquiv_tangentPullbackFun_of_rep f' hf 𝒳.isFiberedInGroupoids φ hφ F G ψ t
    u hu).symm, (underFiberPullback 𝒳.val.p 𝒳.isFiberedInGroupoids
    (tangentPullbackBase f' hf ψ) (tangentPullbackBase_square f' hf ψ) φ hφ (hy := hy) u).2⟩

/-- **Stacks 0DNT: tangent modules of an algebraic stack commute with flat base change.** Let `𝒳`
be an algebraic stack over `S` with `𝒳 → S` locally of finite presentation, `A → C` a flat
homomorphism of `S`-algebras, `x` an object of `𝒳` over `Spec A` and `y = x|_{Spec C}`, exhibited
by a strongly cartesian arrow `β : y ⟶ x` over `Spec C ⟶ Spec A`. Then for every `A`-module `M`
there is a `C`-linear isomorphism `C ⊗_A T_x(M) ≅ T_y(C ⊗_A M)`, the one induced by pulling lifts
back along `Spec C[C ⊗_A M] ⟶ Spec A[M]`: the ring map `r : A[M] → C[C ⊗_A M]` is `A → C` on
`A` and `m ↦ 1 ⊗ m` on `M`, and `1 ⊗ t` is sent to the class of the cartesian pullback along
`Spec r` of a lift representing `t`. The tangent modules are arbitrary realizations of the
tangent functors of Stacks 07Y9. -/
@[stacks 0DNT]
theorem exists_tangentFlatBaseChange
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (f : 𝒳 ⟶ Stack.schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS))))
    (hf : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f)
    (A C : Type u) [CommRing A] [CommRing C] [Algebra A C] [Module.Flat A C]
    (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    (toS' : Spec (.of C) ⟶ S) (hC : B.Contains (Spec (.of C)))
    (x y : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = algebraOver A B S hS toS hA)
    (hy : 𝒳.val.p.obj y = algebraOver C B S hS toS' hC)
    (b : algebraOver C B S hS toS' hC ⟶ algebraOver A B S hS toS hA)
    (hb : (BigFppfOver.toScheme B S hS).map b = Spec.map (CommRingCat.ofHom (algebraMap A C)))
    (β : y ⟶ x) (hβ : 𝒳.val.p.IsStronglyCartesian b β)
    (M : SiteModule A B) (hMC : IsSiteModule C B (ModuleCat.of C (C ⊗[A] M.obj)))
    (Tx : TangentFunctorData A B S hS toS hA 𝒳.val.p x hx)
    (Ty : TangentFunctorData C B S hS toS' hC 𝒳.val.p y hy) :
    let N : SiteModule C B := ⟨ModuleCat.of C (C ⊗[A] M.obj), hMC⟩
    ∃ (r : squareZeroRing A M.obj ⟶ squareZeroRing C N.obj)
      (g : squareZeroOver C B S hS toS' N ⟶ squareZeroOver A B S hS toS M)
      (e : (C ⊗[A] (Tx.functor.obj M : Type _)) ≃ₗ[C] (Ty.functor.obj N : Type _)),
      ((BigFppfOver.toScheme B S hS).map g = Spec.map r) ∧
      (∀ z : TrivSqZeroExt A M.obj,
        (r.hom z).fst = algebraMap A C z.fst ∧ (r.hom z).snd = (1 : C) ⊗ₜ[A] z.snd) ∧
      (∀ t : (Tx.functor.obj M : Type _),
        ∃ (a : (Under.post 𝒳.val.p).Fiber
            (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M)))
          (c : (Under.post 𝒳.val.p).Fiber
            (Under.mk (eqToHom hy ≫ squareZeroArrow C B S hS toS' hC N))),
          Quotient.mk _ a = Tx.liftEquiv M t ∧
          Quotient.mk _ c = Ty.liftEquiv N (e ((1 : C) ⊗ₜ[A] t)) ∧
          ∃ φ : c.1.right ⟶ a.1.right,
            𝒳.val.p.IsStronglyCartesian g φ ∧ c.1.hom ≫ φ = β ≫ a.1.hom) := by
  intro N
  have hfC : Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ toS = toS' := by
    rw [← hb]
    exact (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w b))
  have hb' : b = algebraOverMapOfRingHom (algebraMap A C) B S hS toS toS' hA hC hfC :=
    (BigFppfOver.toScheme B S hS).map_injective hb
  have hφ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom (algebraMap A C) B S hS toS toS' hA hC hfC)
      β := by
    rw [← hb']
    infer_instance
  obtain ⟨e, he⟩ := isTangentBaseChangeIso_of_isAlgebraicStack h𝒳 f hf hfC β hφ M hMC Tx Ty
  obtain ⟨r, hr, hrz⟩ := exists_squareZeroRing_hom_tangentPullbackBase (algebraMap A C) hfC
    (M := M) (N := N) (tensorCoeff (A₁ := C) M.obj)
  refine ⟨r, tangentPullbackBase (algebraMap A C) hfC (tensorCoeff (A₁ := C) M.obj), e, hr,
    hrz, fun t ↦ ?_⟩
  obtain ⟨u, c, hu, hc, ρ, hρ, hfac⟩ := exists_rep_tangentPullbackHom (algebraMap A C) hfC β hφ
    Tx Ty (M := M) (N := N) (tensorCoeff (A₁ := C) M.obj) t
  exact ⟨u, c, hu, hc.trans (congrArg (Ty.liftEquiv N) (he t).symm), ρ, hρ, hfac⟩

end Assembly

end Deformation.Artin

end
