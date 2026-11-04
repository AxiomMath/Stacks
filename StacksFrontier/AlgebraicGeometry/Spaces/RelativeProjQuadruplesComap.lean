module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesAlgebraicSpace

/-!
# Base change of the functor of quadruples along a comparison of restriction data

Let `g : X' ⟶ X` be a morphism of presheaves on the big fppf site, `ρ` a restriction datum of
Stacks 084A over `X` (the restrictions `f^*𝒜` of a graded algebra to the scheme points of `X`
together with the comparisons along morphisms of test objects) and `ρ'` one over `X'`.  A
*comparison along `g`* identifies the algebra of `ρ'` at a scheme point `f` of `X'` with the
algebra of `ρ` at `g ∘ f`, compatibly with the comparisons of the two data.  This is what Stacks
085C produces for `ρ'` the datum of `g^*𝒜`: the identification `(g ∘ f')^*𝒜 = (f')^*(g^*𝒜)`.

Given such a comparison, this file constructs the morphism `F' ⟶ F` of the functors of quadruples
sending the class of `(d, f', ℒ, ψ)` to the class of `(d, g ∘ f', ℒ, ψ)`, and proves that the
square it forms with `g` and the two projections is cartesian: `F' = X' ×_X F`.  This is the proof
of Stacks 085C: a bijection `F'(T) ≅ X'(T) ×_{X(T)} F(T)` on quasi-compact test objects, natural in
`T`, and extended through the limit over the quasi-compact opens.

## Main definitions

* `AlgebraicGeometry.Space.GradedAlgebraRestriction.ComapHom`: a comparison of restriction data
  along `g`.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.ComapHom.fibreMap`: the induced bijection of
  the fibres of `F(T)` over `g ∘ f` and of `F'(T)` over `f`.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.ComapHom.quadrupleSpaceMap`: the morphism
  `F' ⟶ F` of the functors of quadruples.

## Main results

* `AlgebraicGeometry.Space.GradedAlgebraRestriction.ComapHom.fibreRestrict_fibreMap`: the
  bijection of the fibres commutes with the restriction maps of `F` and `F'`.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.ComapHom.isPullback_quadrupleSpaceMap`:
  **the square `F' ⟶ F`, `F' ⟶ X'`, `F ⟶ X`, `g : X' ⟶ X` is cartesian.**

## References

* [Stacks Project, Tag 085C](https://stacks.math.columbia.edu/tag/085C)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S S' T : Scheme.{u}} (g : S' ⟶ S)
  {A B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}

/-- **Base change down commutes with transport**, on the union: reading the transport along `Φ`
of a class over `f' ≫ g` as a class for `g^*𝒜` over `f'` is transporting along `g^*Φ` the class
read for `g^*ℬ`. -/
theorem F.baseChangeDownQ_algebraTransport (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (h : ∀ n : ℤ, IsIso (Φ.app n)) (f' : T ⟶ S') (q : Quot (UnionRel (f := f' ≫ g) (A := B))) :
    F.baseChangeDownQ g A f' (F.algebraTransport Φ h (⟨f' ≫ g, q⟩ : F B T)).2 =
      F.algebraTransport (baseAlgebraMapHom g Φ) (fun n => haveI := h n; inferInstance)
        (F.baseChangeDownQ g B f' q) := by
  have hup : F.baseChangeUp g A
      (F.baseChangeDownQ g A f' (F.algebraTransport Φ h (⟨f' ≫ g, q⟩ : F B T)).2) =
      F.baseChangeUp g A (F.algebraTransport (baseAlgebraMapHom g Φ)
        (fun n => have := h n; inferInstance) (F.baseChangeDownQ g B f' q)) :=
    (F.baseChangeUp_baseChangeDownQ g A f' _).trans
      ((congrArg (F.algebraTransport Φ h) (F.baseChangeUp_baseChangeDownQ g B f' q).symm).trans
        (F.baseChangeUp_algebraTransport g Φ h _).symm)
  have key := F.baseChangeUp_injective g hup
  exact Sigma.ext rfl (heq_of_eq key)

/-- `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.baseChangeDownQ_algebraTransport` for the
pullback of a class over the identity. -/
theorem F.baseChangeDownQ_algebraTransport_pullback (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (h : ∀ n : ℤ, IsIso (Φ.app n)) (q : Quot (UnionRel (f := 𝟙 S) (A := B))) :
    F.baseChangeDownQ g A (𝟙 S') (F.algebraTransport Φ h (F.pullback g (⟨𝟙 S, q⟩ : F B S))).2 =
      F.algebraTransport (baseAlgebraMapHom g Φ) (fun n => haveI := h n; inferInstance)
        (F.baseChangeDownQ g B (𝟙 S') (F.pullback g (⟨𝟙 S, q⟩ : F B S)).2) :=
  F.baseChangeDownQ_algebraTransport g Φ h (𝟙 S') (F.pullback g (⟨𝟙 S, q⟩ : F B S)).2

/-- Transport along equal unital homomorphisms agrees. -/
theorem F.algebraTransport_congr {Φ Ψ : SheafOfModules.GradedAlgebra.UnitalHom A B} (e : Φ = Ψ)
    (hΦ : ∀ n : ℤ, IsIso (Φ.app n)) (hΨ : ∀ n : ℤ, IsIso (Ψ.app n)) (ξ : F B T) :
    F.algebraTransport Φ hΦ ξ = F.algebraTransport Ψ hΨ ξ := by
  subst e
  rfl

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

namespace AlgebraicGeometry.Space

namespace GradedAlgebraRestriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {r : GradedAlgebraPoints B S hS X} {r' : GradedAlgebraPoints B S hS X'}

/-- **A comparison of restriction data along `g : X' ⟶ X`.**  For every scheme point `f` of `X'`
a degreewise invertible unital homomorphism from the algebra of `ρ'` at `f` to the algebra of `ρ`
at `g ∘ f`, compatible with the restriction maps of the two data along every morphism of test
objects.  For the restriction datum of `g^*𝒜` and that of `𝒜` this is the identification
`(f')^*(g^*𝒜) = (g ∘ f')^*𝒜` of the proof of Stacks 085C. -/
structure ComapHom (ρ' : GradedAlgebraRestriction r') (ρ : GradedAlgebraRestriction r)
    (g : X' ⟶ X) where
  /-- The comparison at a scheme point of `X'`. -/
  hom {T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X') :
    SheafOfModules.GradedAlgebra.UnitalHom (r'.algebra T f) (r.algebra T (f ≫ g))
  /-- The comparison is invertible in every degree. -/
  isIso_hom_app {T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X') (n : ℤ) : IsIso ((hom f).app n)
  /-- The comparison commutes with the restriction maps of the two data. -/
  restrict_comp_hom {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X')
      (f₂ : yoneda.obj T' ⟶ X') (hf : yoneda.map τ ≫ f = f₂)
      (h : yoneda.map τ ≫ f ≫ g = f₂ ≫ g) :
    (ρ'.restrict τ f f₂ hf).comp
        (baseAlgebraMapHom ((BigFppfOver.toScheme B S hS).map τ) (hom f)) =
      (hom f₂).comp (ρ.restrict τ (f ≫ g) (f₂ ≫ g) h)

attribute [instance] ComapHom.isIso_hom_app

namespace ComapHom

variable {ρ' : GradedAlgebraRestriction r'} {ρ : GradedAlgebraRestriction r} {g : X' ⟶ X}
  (e : ComapHom ρ' ρ g)

/-- **The bijection of the fibres**: a class of quadruples `(d, g ∘ f, ℒ, ψ)` for `ρ` over
`g ∘ f` gives the class of `(d, f, ℒ, ψ)` for `ρ'` over `f`, `ψ` read through the comparison. -/
def fibreMap {T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X')
    (q : Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T))
      (A := r.algebra T (f ≫ g)))) :
    Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T)) (A := r'.algebra T f)) :=
  (F.algebraTransport (e.hom f) (e.isIso_hom_app f)
    (⟨𝟙 _, q⟩ : F (r.algebra T (f ≫ g)) ((BigFppfOver.toScheme B S hS).obj T))).2

/-- The inverse of the bijection of the fibres. -/
def fibreInv {T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X')
    (q : Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T)) (A := r'.algebra T f))) :
    Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T)) (A := r.algebra T (f ≫ g))) :=
  (F.algebraTransport (unitalHomInverse (e.hom f) (e.isIso_hom_app f))
    (isIso_unitalHomInverse_app _ _)
    (⟨𝟙 _, q⟩ : F (r'.algebra T f) ((BigFppfOver.toScheme B S hS).obj T))).2

/-- `fibreInv` is a left inverse of `fibreMap`. -/
theorem fibreInv_fibreMap {T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X')
    (q : Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T))
      (A := r.algebra T (f ≫ g)))) :
    e.fibreInv f (e.fibreMap f q) = q :=
  eq_of_heq (Sigma.mk.inj
    ((F.algebraTransportEquiv (e.hom f) (e.isIso_hom_app f) _).symm_apply_apply
      (⟨𝟙 _, q⟩ : F (r.algebra T (f ≫ g)) ((BigFppfOver.toScheme B S hS).obj T)))).2

/-- `fibreInv` is a right inverse of `fibreMap`. -/
theorem fibreMap_fibreInv {T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X')
    (q : Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T)) (A := r'.algebra T f))) :
    e.fibreMap f (e.fibreInv f q) = q :=
  eq_of_heq (Sigma.mk.inj
    ((F.algebraTransportEquiv (e.hom f) (e.isIso_hom_app f) _).apply_symm_apply
      (⟨𝟙 _, q⟩ : F (r'.algebra T f) ((BigFppfOver.toScheme B S hS).obj T)))).2

/-- The bijection of the fibres is injective. -/
theorem fibreMap_injective {T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X') :
    Function.Injective (e.fibreMap f) :=
  Function.LeftInverse.injective (e.fibreInv_fibreMap f)

/-- The inverse of the bijection of the fibres is injective. -/
theorem fibreInv_injective {T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X') :
    Function.Injective (e.fibreInv f) :=
  Function.LeftInverse.injective (e.fibreMap_fibreInv f)

/-- **The bijection of the fibres commutes with the restriction maps of `F` and `F'`.** -/
theorem fibreRestrict_fibreMap {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X')
    (f₂ : yoneda.obj T' ⟶ X') (hf : yoneda.map τ ≫ f = f₂) (h : yoneda.map τ ≫ f ≫ g = f₂ ≫ g)
    (q : Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T))
      (A := r.algebra T (f ≫ g)))) :
    ρ'.fibreRestrict τ f f₂ hf (e.fibreMap f q) =
      e.fibreMap f₂ (ρ.fibreRestrict τ (f ≫ g) (f₂ ≫ g) h q) := by
  have h1 := ρ'.sigma_fibreRestrict τ f f₂ hf (e.fibreMap f q)
  have h2 := ρ.sigma_fibreRestrict τ (f ≫ g) (f₂ ≫ g) h q
  have h3' : (F.pullback ((BigFppfOver.toScheme B S hS).map τ)
      (⟨𝟙 _, e.fibreMap f q⟩ : F (r'.algebra T f) ((BigFppfOver.toScheme B S hS).obj T))).2 =
      (F.algebraTransport (e.hom f) (e.isIso_hom_app f)
        (F.pullback ((BigFppfOver.toScheme B S hS).map τ)
          (⟨𝟙 _, q⟩ : F (r.algebra T (f ≫ g)) ((BigFppfOver.toScheme B S hS).obj T)))).2 :=
    eq_of_heq (Sigma.mk.inj (F.algebraTransport_pullback (e.hom f) (e.isIso_hom_app f)
      ((BigFppfOver.toScheme B S hS).map τ)
      (⟨𝟙 _, q⟩ : F (r.algebra T (f ≫ g)) ((BigFppfOver.toScheme B S hS).obj T))).symm).2
  have h4 := F.baseChangeDownQ_algebraTransport_pullback ((BigFppfOver.toScheme B S hS).map τ)
    (e.hom f) (e.isIso_hom_app f) q
  have key : (⟨𝟙 _, ρ'.fibreRestrict τ f f₂ hf (e.fibreMap f q)⟩ :
        F (r'.algebra T' f₂) ((BigFppfOver.toScheme B S hS).obj T')) =
      ⟨𝟙 _, e.fibreMap f₂ (ρ.fibreRestrict τ (f ≫ g) (f₂ ≫ g) h q)⟩ := by
    refine h1.trans ?_
    refine (congrArg (fun x : Quot (UnionRel
        (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T') ≫ (BigFppfOver.toScheme B S hS).map τ)
        (A := r'.algebra T f)) => F.algebraTransport (ρ'.restrict τ f f₂ hf)
          (ρ'.isIso_restrict_app τ f f₂ hf) (F.baseChangeDownQ ((BigFppfOver.toScheme B S hS).map τ)
            (r'.algebra T f) (𝟙 _) x)) h3').trans ?_
    rw [h4, F.algebraTransport_algebraTransport _ _ _ _ (fun n => inferInstance),
      F.algebraTransport_congr (e.restrict_comp_hom τ f f₂ hf h) _ (fun n => inferInstance),
      ← F.algebraTransport_algebraTransport (e.hom f₂) (ρ.restrict τ (f ≫ g) (f₂ ≫ g) h)
        (e.isIso_hom_app f₂) (fun n => inferInstance), ← h2]
    rfl
  exact eq_of_heq (Sigma.mk.inj key).2

/-- The inverse bijection of the fibres commutes with the restriction maps. -/
theorem fibreRestrict_fibreInv {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X')
    (f₂ : yoneda.obj T' ⟶ X') (hf : yoneda.map τ ≫ f = f₂) (h : yoneda.map τ ≫ f ≫ g = f₂ ≫ g)
    (q : Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T)) (A := r'.algebra T f))) :
    ρ.fibreRestrict τ (f ≫ g) (f₂ ≫ g) h (e.fibreInv f q) =
      e.fibreInv f₂ (ρ'.fibreRestrict τ f f₂ hf q) := by
  apply e.fibreMap_injective f₂
  rw [← e.fibreRestrict_fibreMap τ f f₂ hf h, e.fibreMap_fibreInv, e.fibreMap_fibreInv]

/-! ### The morphism of functors of quadruples -/

/-- **The map `F'(T) ⟶ F(T)` on the limits over the quasi-compact test objects**: a point of `X'`
with a compatible family of classes of quadruples `(d, f', ℒ, ψ)` goes to its image in `X` with the
family of classes of `(d, g ∘ f', ℒ, ψ)`. -/
def limPointMap {T : BigFppfOver B S hS} (ξ : LimPoint ρ' T) : LimPoint ρ T where
  point := ξ.point ≫ g
  val W hW w := e.fibreInv (yoneda.map w ≫ ξ.point) (ξ.val W hW w)
  compat W W' hW hW' k w := by
    rw [← ξ.compat W W' hW hW' k w]
    exact e.fibreRestrict_fibreInv k (yoneda.map w ≫ ξ.point) (yoneda.map (k ≫ w) ≫ ξ.point) rfl
      rfl (ξ.val W hW w)

/-- The image of a point under `limPointMap` lies over its composite with `g`. -/
theorem limPointMap_point {T : BigFppfOver B S hS} (ξ : LimPoint ρ' T) :
    (e.limPointMap ξ).point = ξ.point ≫ g :=
  rfl

/-- `limPointMap` commutes with restriction along a morphism of test objects. -/
theorem limPointMap_restrict {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (ξ : LimPoint ρ' T) :
    e.limPointMap (ξ.restrict τ) = (e.limPointMap ξ).restrict τ :=
  rfl

/-- **Injectivity on the fibres of the projection to `X'`.** -/
theorem limPointMap_injective {T : BigFppfOver B S hS} {ξ η : LimPoint ρ' T}
    (hp : ξ.point = η.point) (h : e.limPointMap ξ = e.limPointMap η) : ξ = η := by
  obtain ⟨p, v, c⟩ := ξ
  obtain ⟨p', v', c'⟩ := η
  obtain rfl : p = p' := hp
  exact LimPoint.ext' rfl fun W hW w => heq_of_eq (e.fibreInv_injective _
    (eq_of_heq (congr_arg_heq (fun ζ : LimPoint ρ T => ζ.val W hW w) h)))

/-- **Surjectivity onto the fibre product**: a point of `F(T)` over `g ∘ f` comes from a point of
`F'(T)` over `f`. -/
theorem exists_limPointMap {T : BigFppfOver B S hS} (ζ : LimPoint ρ T) (f : yoneda.obj T ⟶ X')
    (hf : ζ.point = f ≫ g) : ∃ ξ : LimPoint ρ' T, ξ.point = f ∧ e.limPointMap ξ = ζ := by
  obtain ⟨p, v, c⟩ := ζ
  subst hf
  refine ⟨⟨f, fun W hW w => e.fibreMap (yoneda.map w ≫ f) (v W hW w), fun W W' hW hW' k w => ?_⟩,
    rfl, LimPoint.ext' rfl fun W hW w => heq_of_eq (e.fibreInv_fibreMap _ _)⟩
  rw [← c W W' hW hW' k w]
  exact e.fibreRestrict_fibreMap k (yoneda.map w ≫ f) (yoneda.map (k ≫ w) ≫ f) rfl rfl (v W hW w)

variable {Â : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X) →
      SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T)}
    {Â' : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X') →
      SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T)}
    {ρ₁ : GradedAlgebraRestriction (GradedAlgebraPoints.ofQuasicoherentFamily Â)}
    {ρ₁' : GradedAlgebraRestriction (GradedAlgebraPoints.ofQuasicoherentFamily Â')}
    (e₁ : ComapHom ρ₁' ρ₁ g)
    (hc : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      B.Contains (relativeProj (Â T f)).scheme)
    (hc' : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X'),
      B.Contains (relativeProj (Â' T f)).scheme)

/-- **The morphism `F' ⟶ F`** on the presheaves of `u`-small sets of the limits. -/
def relativeProjMap : ρ₁'.relativeProjFunctor hc' ⟶ ρ₁.relativeProjFunctor hc where
  app T := TypeCat.ofHom fun x => (ρ₁.relativeProjFunctorEquiv hc T.unop).symm
    (e₁.limPointMap (ρ₁'.relativeProjFunctorEquiv hc' T.unop x))
  naturality T T' τ := by
    ext x
    apply (ρ₁.relativeProjFunctorEquiv hc T'.unop).injective
    change ρ₁.relativeProjFunctorEquiv hc T'.unop ((ρ₁.relativeProjFunctorEquiv hc T'.unop).symm
      (e₁.limPointMap (ρ₁'.relativeProjFunctorEquiv hc' T'.unop
        ((ρ₁'.relativeProjFunctor hc').map τ.unop.op x)))) =
      ρ₁.relativeProjFunctorEquiv hc T'.unop ((ρ₁.relativeProjFunctor hc).map τ.unop.op
        ((ρ₁.relativeProjFunctorEquiv hc T.unop).symm
          (e₁.limPointMap (ρ₁'.relativeProjFunctorEquiv hc' T.unop x))))
    rw [relativeProjFunctorEquiv_map, relativeProjFunctorEquiv_map, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, limPointMap_restrict]

/-- The morphism `F' ⟶ F` read on the limits is `limPointMap`. -/
theorem relativeProjFunctorEquiv_relativeProjMap {T : BigFppfOver B S hS}
    (x : (ρ₁'.relativeProjFunctor hc').obj (op T)) :
    ρ₁.relativeProjFunctorEquiv hc T ((e₁.relativeProjMap hc hc').app (op T) x) =
      e₁.limPointMap (ρ₁'.relativeProjFunctorEquiv hc' T x) :=
  Equiv.apply_symm_apply _ _

/-- **Stacks 085C on the functors of quadruples: `F' = X' ×_X F`.**  The square formed by the
morphism `F' ⟶ F`, the projections `F' ⟶ X'` and `F ⟶ X`, and `g : X' ⟶ X` is cartesian. -/
theorem isPullback_relativeProjMap :
    IsPullback (e₁.relativeProjMap hc hc') (ρ₁'.relativeProjπ hc') (ρ₁.relativeProjπ hc) g := by
  apply IsPullback.of_forall_isPullback_app
  intro T
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    show yonedaEquiv (ρ₁.relativeProjFunctorEquiv hc T.unop
      ((e₁.relativeProjMap hc hc').app T x)).point = g.app T (yonedaEquiv
        (ρ₁'.relativeProjFunctorEquiv hc' T.unop x).point)
    rw [relativeProjFunctorEquiv_relativeProjMap, limPointMap_point, yonedaEquiv_comp]
  · rintro x y ⟨h1, h2⟩
    apply (ρ₁'.relativeProjFunctorEquiv hc' T.unop).injective
    refine e₁.limPointMap_injective (yonedaEquiv.injective h2) ?_
    rw [← e₁.relativeProjFunctorEquiv_relativeProjMap hc hc' x,
      ← e₁.relativeProjFunctorEquiv_relativeProjMap hc hc' y]
    exact congrArg _ h1
  · intro y x hxy
    obtain ⟨ξ, hξ, hξ'⟩ := e₁.exists_limPointMap (ρ₁.relativeProjFunctorEquiv hc T.unop y)
      (yonedaEquiv.symm x)
      (yonedaEquiv.injective (by rwa [yonedaEquiv_comp, Equiv.apply_symm_apply]))
    refine ⟨(ρ₁'.relativeProjFunctorEquiv hc' T.unop).symm ξ, ?_, ?_⟩
    · apply (ρ₁.relativeProjFunctorEquiv hc T.unop).injective
      rw [relativeProjFunctorEquiv_relativeProjMap, Equiv.apply_symm_apply, hξ']
    · show yonedaEquiv (ρ₁'.relativeProjFunctorEquiv hc' T.unop
        ((ρ₁'.relativeProjFunctorEquiv hc' T.unop).symm ξ)).point = x
      rw [Equiv.apply_symm_apply, hξ, Equiv.apply_symm_apply]

variable (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
  (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')

/-- **The morphism `F' ⟶ F` of the functors of quadruples of Stacks 084A**, sending the class of
`(d, f', ℒ, ψ)` to the class of `(d, g ∘ f', ℒ, ψ)`. -/
def quadrupleSpaceMap : ρ₁'.quadrupleSpace hc' hX' ⟶ ρ₁.quadrupleSpace hc hX :=
  (ρ₁'.quadrupleSpaceIso hc' hX').inv ≫ e₁.relativeProjMap hc hc' ≫ (ρ₁.quadrupleSpaceIso hc hX).hom

/-- **Stacks 085C on the functors of quadruples of Stacks 084A: `F' = X' ×_X F`.** -/
theorem isPullback_quadrupleSpaceMap :
    IsPullback (e₁.quadrupleSpaceMap hc hc' hX hX') (ρ₁'.quadrupleSpaceπ hc' hX')
      (ρ₁.quadrupleSpaceπ hc hX) g :=
  (e₁.isPullback_relativeProjMap hc hc').of_iso (ρ₁'.quadrupleSpaceIso hc' hX')
    (ρ₁.quadrupleSpaceIso hc hX) (Iso.refl _) (Iso.refl _) (by simp [quadrupleSpaceMap])
    (by simp [quadrupleSpaceπ]) (by simp [quadrupleSpaceπ]) (by simp)

end ComapHom

end GradedAlgebraRestriction

end AlgebraicGeometry.Space

end
