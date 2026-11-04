module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionBaseChangeTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesRestrict

/-!
# The functor of quadruples of Stacks 084A is a functor

In Situation 0849 let `X` be an algebraic space over a scheme `S` and `𝒜` a quasi-coherent graded
`𝒪_X`-algebra.  Over a restriction datum `ρ` (`AlgebraicGeometry.Space.GradedAlgebraRestriction`)
the value `F(T)` of the functor of quadruples of Stacks 084A carries the restriction maps
`AlgebraicGeometry.Space.GradedAlgebraRestriction.FRestrict`.  This file proves the two functor
laws for them, and so assembles `F` into a presheaf on the big fppf site.

The laws are deduced from the corresponding laws of the scheme-level functor of quadruples of the
display 01NX, through a comparison which is the first half of the proof of Stacks 084B: for a
scheme point `g : Z ⟶ X` and a morphism `t : T ⟶ Z` of test objects, a quadruple over the
restricted point `t^*g` of `X` — that is, a quadruple over the identity of `T` for the algebra
`(g ∘ t)^*𝒜` — is the same thing as a quadruple over `t` for the algebra `g^*𝒜` on `Z`.  The
source's words are "sending a quadruple `(d, f : T → Z, ℒ, ψ)` for `F'` to `(d, g ∘ f, ℒ, ψ)`";
read in the other direction this is the map
`AlgebraicGeometry.Space.GradedAlgebraRestriction.fibreToF`, from the fibre of `F(T)` over `t^*g`
to the scheme-level union `F'(T)` of the algebra `g^*𝒜`: transport along the comparison
`(g ∘ t)^*𝒜 ≅ t^*(g^*𝒜)` of the restriction datum, then base change along `t` by Tag 01NT.

## Main results

* `AlgebraicGeometry.Space.GradedAlgebraRestriction.fibreToF_injective`: the comparison is
  injective.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.fibreToF_fibreRestrict`: the comparison
  carries the restriction map of `F` along `τ : T' ⟶ T` to the pullback of the scheme-level
  functor along the scheme morphism of `τ`.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.FRestrict_id` and
  `AlgebraicGeometry.Space.GradedAlgebraRestriction.FRestrict_comp`: the two functor laws.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.functor`: the functor of quadruples on the
  big fppf site, on every test object the union over the degrees.

## Implementation notes

The naturality `fibreToF_fibreRestrict` is where the two coherences of the restriction datum are
spent: the cocycle condition
`AlgebraicGeometry.Space.GradedAlgebraRestriction.restrict_comp` turns the transport along the
comparison at a composite into the transports at the two factors, and the remaining comparison
is the associativity of base change,
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.baseChangeUp_baseChangeUp`.  With the
naturality available, both functor laws follow from the laws `F.pullback_id` and
`F.pullback_comp` of the scheme-level functor by injectivity, so the identity coherence of the
restriction datum is not needed for them.

## References

* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace AlgebraicGeometry.Space

namespace GradedAlgebraRestriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {r : GradedAlgebraPoints B S hS X} (ρ : GradedAlgebraRestriction r)

/-! ### The comparison with the scheme-level functor of quadruples -/

/-- **A point of the fibre of `F(T)` over a restricted point, as a point of the scheme-level
functor of quadruples of `g^*𝒜`.**

For a scheme point `g : Z ⟶ X`, a morphism `t : T ⟶ Z` of test objects and the restricted point
`f = t^*g`, a class of quadruples over the identity of `T` for the algebra `f^*𝒜` is transported
along the comparison `f^*𝒜 ≅ t^*(g^*𝒜)` of the restriction datum and then read, by the base
change of Tag 01NT, as a class of quadruples over `t` for the algebra `g^*𝒜` on `Z`. -/
def fibreToF {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) (t : T ⟶ Z)
    (f : yoneda.obj T ⟶ X) (hf : yoneda.map t ≫ g = f)
    (q : Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T)) (A := r.algebra T f))) :
    F (r.algebra Z g) ((BigFppfOver.toScheme B S hS).obj T) :=
  F.baseChangeUp ((BigFppfOver.toScheme B S hS).map t) (r.algebra Z g)
    ((F.algebraTransportEquiv (ρ.restrict t g f hf) (ρ.isIso_restrict_app t g f hf) _).symm
      ⟨𝟙 _, q⟩)

/-- The comparison lands over the scheme morphism of `t`. -/
@[simp] theorem fibreToF_fst {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) (t : T ⟶ Z)
    (f : yoneda.obj T ⟶ X) (hf : yoneda.map t ≫ g = f)
    (q : Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T)) (A := r.algebra T f))) :
    (ρ.fibreToF g t f hf q).1 = (BigFppfOver.toScheme B S hS).map t :=
  rfl

/-- **The comparison is injective**: the transport along the comparison of the restriction datum
is a bijection, and the base change of Tag 01NT is injective over the fixed morphism `𝟙`. -/
theorem fibreToF_injective {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) (t : T ⟶ Z)
    (f : yoneda.obj T ⟶ X) (hf : yoneda.map t ≫ g = f) :
    Function.Injective (ρ.fibreToF g t f hf) := by
  intro a b h
  have h1 := F.baseChangeUp_injective ((BigFppfOver.toScheme B S hS).map t) h
  have h2 : (⟨𝟙 _, a⟩ : F (r.algebra T f) ((BigFppfOver.toScheme B S hS).obj T)) = ⟨𝟙 _, b⟩ :=
    (F.algebraTransportEquiv (ρ.restrict t g f hf) (ρ.isIso_restrict_app t g f hf) _).symm.injective
      (Sigma.ext rfl (heq_of_eq h1))
  exact eq_of_heq (Sigma.mk.inj h2).2

/-- The comparison depends on the morphism `t` only through its value: equal morphisms give the
same comparison. -/
theorem fibreToF_congr {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) {t t' : T ⟶ Z}
    (ht : t = t') (f : yoneda.obj T ⟶ X) (hf : yoneda.map t ≫ g = f)
    (hf' : yoneda.map t' ≫ g = f)
    (q : Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T)) (A := r.algebra T f))) :
    ρ.fibreToF g t f hf q = ρ.fibreToF g t' f hf' q := by
  subst ht
  rfl

/-- **The restriction map of `F`, read in the scheme-level functor of quadruples.** The class of
the restriction of a quadruple along `τ` is the transport along the comparison of the restriction
datum of the base change down, along the scheme morphism of `τ`, of the class of its pullback. -/
theorem sigma_fibreRestrict {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X)
    (f' : yoneda.obj T' ⟶ X) (hf : yoneda.map τ ≫ f = f')
    (q : Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T)) (A := r.algebra T f))) :
    (⟨𝟙 _, ρ.fibreRestrict τ f f' hf q⟩ :
        F (r.algebra T' f') ((BigFppfOver.toScheme B S hS).obj T')) =
      F.algebraTransport (ρ.restrict τ f f' hf) (ρ.isIso_restrict_app τ f f' hf)
        (F.baseChangeDownQ ((BigFppfOver.toScheme B S hS).map τ) (r.algebra T f) (𝟙 _)
          (F.pullback ((BigFppfOver.toScheme B S hS).map τ)
            (⟨𝟙 _, q⟩ : F (r.algebra T f) ((BigFppfOver.toScheme B S hS).obj T))).2) := by
  induction q using Quot.ind with
  | _ P => rfl

/-- **The comparison is natural.** Restricting a point of the fibre of `F(T)` along a morphism
`τ : T' ⟶ T` of test objects and then comparing it, over `τ ≫ t`, with the scheme-level functor
of quadruples of `g^*𝒜`, is comparing it over `t` and then pulling back along the scheme morphism
of `τ`.

This is where the cocycle condition of the restriction datum is used; the rest is the
compatibility of base change with transport and its associativity. -/
theorem fibreToF_fibreRestrict {Z T T' : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X)
    (t : T ⟶ Z) (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X) (f' : yoneda.obj T' ⟶ X)
    (hf : yoneda.map t ≫ g = f) (hf' : yoneda.map τ ≫ f = f')
    (hf'' : yoneda.map (τ ≫ t) ≫ g = f')
    (q : Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T)) (A := r.algebra T f))) :
    ρ.fibreToF g (τ ≫ t) f' hf'' (ρ.fibreRestrict τ f f' hf' q) =
      F.pullback ((BigFppfOver.toScheme B S hS).map τ) (ρ.fibreToF g t f hf q) := by
  set φ := BigFppfOver.toScheme B S hS
  set Θ := baseAlgebraCompHomOf (r.algebra Z g) (φ.map τ) (φ.map t) (φ.map (τ ≫ t))
    (φ.map_comp τ t).symm with hΘ
  -- the transport along the composite comparison `τ^*(f^*𝒜) ⟶ (τ ≫ t)^*(g^*𝒜)`
  set Ψ := (baseAlgebraMapHom (φ.map τ) (ρ.restrict t g f hf)).comp Θ with hΨ
  have hΨiso : ∀ n : ℤ, IsIso (Ψ.app n) := fun n => inferInstance
  set p : F (r.algebra T f) (φ.obj T') := F.pullback (φ.map τ) ⟨𝟙 _, q⟩ with hp
  set w := F.baseChangeDownQ (φ.map τ) (r.algebra T f) (𝟙 _) p.2 with hw
  set v := (F.algebraTransportEquiv Ψ hΨiso _).symm w with hv
  have hwv : F.algebraTransport Ψ hΨiso v = w :=
    (F.algebraTransportEquiv Ψ hΨiso _).apply_symm_apply w
  have hpw : F.baseChangeUp (φ.map τ) (r.algebra T f) w = p :=
    F.baseChangeUp_baseChangeDownQ (φ.map τ) (r.algebra T f) (𝟙 _) p.2
  -- the restricted point is the transport, along the comparison at the composite, of `v`
  have hx' : (⟨𝟙 _, ρ.fibreRestrict τ f f' hf' q⟩ : F (r.algebra T' f') (φ.obj T')) =
      F.algebraTransport (ρ.restrict (τ ≫ t) g f' hf'') (ρ.isIso_restrict_app _ g f' hf'') v := by
    rw [ρ.sigma_fibreRestrict τ f f' hf' q, ← hw, ← hwv,
      F.algebraTransport_algebraTransport _ _ _ _ (fun n => inferInstance)]
    congr 1
    exact (ρ.restrict_comp t τ g f f' hf hf' hf'').symm
  have hLHS : ρ.fibreToF g (τ ≫ t) f' hf'' (ρ.fibreRestrict τ f f' hf' q) =
      F.baseChangeUp (φ.map (τ ≫ t)) (r.algebra Z g) v := by
    rw [fibreToF, hx']
    exact congrArg _ ((F.algebraTransportEquiv _ _ _).symm_apply_apply v)
  -- the pulled-back point is the transport, along the comparison at `t`, of the base change of `v`
  set y := F.baseChangeUp (φ.map τ) (baseAlgebra (φ.map t) (r.algebra Z g))
    (F.algebraTransport Θ (fun n => inferInstance) v) with hy
  have hpv : p = F.algebraTransport (ρ.restrict t g f hf) (ρ.isIso_restrict_app t g f hf) y :=
    hpw.symm.trans ((congrArg (F.baseChangeUp (φ.map τ) (r.algebra T f)) (hwv.symm.trans
      (F.algebraTransport_algebraTransport _ _ (fun n => inferInstance)
        (fun n => inferInstance) hΨiso v).symm)).trans
      (F.baseChangeUp_algebraTransport (φ.map τ) (ρ.restrict t g f hf)
        (ρ.isIso_restrict_app t g f hf) _))
  have hRHS : F.pullback (φ.map τ) (ρ.fibreToF g t f hf q) =
      F.baseChangeUp (φ.map t) (r.algebra Z g) y := by
    rw [fibreToF, ← F.baseChangeUp_pullback]
    congr 1
    exact (F.algebraTransport_pullback _ _ (φ.map τ) _).symm.trans
      ((congrArg (F.algebraTransport (unitalHomInverse (ρ.restrict t g f hf)
        (ρ.isIso_restrict_app t g f hf)) (isIso_unitalHomInverse_app _ _)) hpv).trans
        ((F.algebraTransportEquiv _ _ _).symm_apply_apply _))
  rw [hLHS, hRHS, F.baseChangeUp_baseChangeUp]

/-! ### The functor laws -/

/-- **The restriction along the identity of a test object is the identity**, on the fibres. -/
theorem fibreRestrict_id {T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X)
    (q : Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T)) (A := r.algebra T f))) :
    ρ.fibreRestrict (𝟙 T) f f rfl q = q := by
  apply ρ.fibreToF_injective f (𝟙 T) f rfl
  exact (ρ.fibreToF_congr f (Category.id_comp (𝟙 T)).symm f rfl (by simp) _).trans
    ((ρ.fibreToF_fibreRestrict f (𝟙 T) (𝟙 T) f f rfl rfl (by simp) q).trans (F.pullback_id _))

/-- **The first functor law**: restricting a point of `F(T)` along the identity of `T` returns
it. -/
theorem FRestrict_id {T : BigFppfOver B S hS} (ξ : r.F T) : ρ.FRestrict (𝟙 T) ξ = ξ := by
  obtain ⟨f, q⟩ := ξ
  exact Sigma.ext rfl (heq_of_eq (ρ.fibreRestrict_id f q))

/-- **The restriction along a composite is the composite of the restrictions**, on the fibres. -/
theorem fibreRestrict_comp {T T' T'' : BigFppfOver B S hS} (τ : T' ⟶ T) (τ' : T'' ⟶ T')
    (f : yoneda.obj T ⟶ X)
    (q : Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T)) (A := r.algebra T f))) :
    ρ.fibreRestrict (τ' ≫ τ) f (yoneda.map (τ' ≫ τ) ≫ f) rfl q =
      ρ.fibreRestrict τ' (yoneda.map τ ≫ f) (yoneda.map (τ' ≫ τ) ≫ f) rfl
        (ρ.fibreRestrict τ f (yoneda.map τ ≫ f) rfl q) := by
  apply ρ.fibreToF_injective f ((τ' ≫ τ) ≫ 𝟙 T) (yoneda.map (τ' ≫ τ) ≫ f) (by simp)
  have e1 := ρ.fibreToF_fibreRestrict f (𝟙 T) (τ' ≫ τ) f (yoneda.map (τ' ≫ τ) ≫ f) rfl rfl
    (by simp) q
  have e2 := ρ.fibreToF_fibreRestrict f (τ ≫ 𝟙 T) τ' (yoneda.map τ ≫ f)
    (yoneda.map (τ' ≫ τ) ≫ f) (by simp) rfl (by simp) (ρ.fibreRestrict τ f (yoneda.map τ ≫ f) rfl q)
  have e3 := ρ.fibreToF_fibreRestrict f (𝟙 T) τ f (yoneda.map τ ≫ f) rfl rfl (by simp) q
  exact e1.trans ((F.pullback_comp _ _ _).trans ((congrArg (F.pullback _) e3.symm).trans
    (e2.symm.trans (ρ.fibreToF_congr f (Category.assoc τ' τ (𝟙 T)).symm _ _ _ _))))

/-- **The second functor law**: restricting a point of `F(T)` along a composite `τ' ≫ τ` is
restricting along `τ` and then along `τ'`. -/
theorem FRestrict_comp {T T' T'' : BigFppfOver B S hS} (τ : T' ⟶ T) (τ' : T'' ⟶ T')
    (ξ : r.F T) : ρ.FRestrict (τ' ≫ τ) ξ = ρ.FRestrict τ' (ρ.FRestrict τ ξ) := by
  obtain ⟨f, q⟩ := ξ
  exact Sigma.ext rfl (heq_of_eq (ρ.fibreRestrict_comp τ τ' f q))

/-- **Stacks 084A: the functor of quadruples on the big fppf site**, its value on a test object
`T` being the union over `d ≥ 1` of the quadruples `(d, f : T → X, ℒ, ψ)` modulo strict
equivalence and the equivalence of Tag 01NW, and its restriction maps being
`AlgebraicGeometry.Space.GradedAlgebraRestriction.FRestrict`. -/
def functor : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) where
  obj T := r.F T.unop
  map τ := TypeCat.ofHom (ρ.FRestrict τ.unop)
  map_id _T := TypeCat.homEquiv.injective (funext fun ξ => ρ.FRestrict_id ξ)
  map_comp τ τ' := TypeCat.homEquiv.injective (funext fun ξ => ρ.FRestrict_comp τ.unop τ'.unop ξ)

/-- The value of `functor` on a test object `T` is the set `F(T)` of classes of quadruples. -/
@[simp] theorem functor_obj (T : (BigFppfOver B S hS)ᵒᵖ) : ρ.functor.obj T = r.F T.unop := rfl

/-- The map of `functor` along `τ : T ⟶ T'` sends `ξ` to its restriction along `τ.unop`. -/
@[simp] theorem functor_map {T T' : (BigFppfOver B S hS)ᵒᵖ} (τ : T ⟶ T') (ξ : r.F T.unop) :
    ρ.functor.map τ ξ = ρ.FRestrict τ.unop ξ := rfl

end GradedAlgebraRestriction

end AlgebraicGeometry.Space

end
