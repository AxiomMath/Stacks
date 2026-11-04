module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteCoefficientLFunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StratificationLFunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DerivedStalkPerfection

/-!
# The L-function is multiplicative along short exact sequences

Let `X` be locally of finite type and quasi-compact over a finite field and
`0 → F' → F → F'' → 0` a sequence of sheaves of modules over a commutative ring `Λ` on
`X_étale`, exact on the stalks at every geometric point, with finite projective stalks. Then

`L(X, F) = L(X, F') · L(X, F'')`.

## Main results

All names are in the namespace `Stacks.EtaleCohomology`.

* `EulerSystem.eulerProduct_eq_mul`: Euler products multiply when the local factors do.
* `finiteProjectiveLocalFactor_X₂_eq_mul`: the local Euler factor is multiplicative along a
  stalkwise short exact sequence.
* `lFunctionOfFiniteProjectiveStalks_X₂_eq_mul`: the L-function is multiplicative along a
  stalkwise short exact sequence.
* `lFunctionOfFiniteProjectiveStalks_X₂_eq_mul_of_shortExact`: the same for a short exact sequence
  of sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

/-- **Euler products multiply** when the local factors do. -/
public theorem EulerSystem.eulerProduct_eq_mul {Λ : Type*} [CommRing Λ] {ι : Type*}
    (E E' E'' : EulerSystem Λ ι) (hdeg' : ∀ i, E'.deg i = E.deg i)
    (hdeg'' : ∀ i, E''.deg i = E.deg i) (hfac : ∀ i, E.factor i = E'.factor i * E''.factor i) :
    E.eulerProduct = E'.eulerProduct * E''.eulerProduct := by
  classical
  ext n
  have hsupp' : E'.support n = E.support n := by
    ext i
    rw [E'.mem_support, E.mem_support, hdeg']
  have hsupp'' : E''.support n = E.support n := by
    ext i
    rw [E''.mem_support, E.mem_support, hdeg'']
  let J := Ideal.span {(PowerSeries.X : PowerSeries Λ) ^ (n + 1)}
  have hq : Ideal.Quotient.mk J (E'.eulerProduct * E''.eulerProduct) =
      Ideal.Quotient.mk J (E'.partialProduct n * E''.partialProduct n) := by
    rw [map_mul, map_mul,
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2
        (E'.X_pow_dvd_eulerProduct_sub_partialProduct n)),
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2
        (E''.X_pow_dvd_eulerProduct_sub_partialProduct n))]
  have hd := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hq)
  have h := PowerSeries.X_pow_dvd_iff.1 hd n (Nat.lt_succ_self n)
  rw [map_sub, sub_eq_zero] at h
  rw [h, E.coeff_eulerProduct, EulerSystem.partialProduct, EulerSystem.partialProduct,
    EulerSystem.partialProduct, hsupp', hsupp'', ← Finset.prod_mul_distrib]
  exact congrArg _ (Finset.prod_congr rfl fun i _ => hfac i)

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]
  (S : ShortComplex (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)))
  (hS : ∀ s : GeometricPoint X.obj,
    (S.map (etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s)).ShortExact)
  (hfin₁ : ∀ s : GeometricPoint X.obj,
    Module.Finite Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s).obj S.X₁))
  (hproj₁ : ∀ s : GeometricPoint X.obj,
    Module.Projective Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s).obj S.X₁))
  (hfin₂ : ∀ s : GeometricPoint X.obj,
    Module.Finite Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s).obj S.X₂))
  (hproj₂ : ∀ s : GeometricPoint X.obj,
    Module.Projective Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s).obj S.X₂))
  (hfin₃ : ∀ s : GeometricPoint X.obj,
    Module.Finite Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s).obj S.X₃))
  (hproj₃ : ∀ s : GeometricPoint X.obj,
    Module.Projective Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s).obj S.X₃))
  {k : Type u} [Field k] [Finite k] (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f]

include hS in
/-- The sequence of stalks on Mathlib's site is short exact. -/
public theorem shortExact_map_sheafEquiv_sheafFiber (s : GeometricPoint X.obj) :
    (S.map ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{max (u + 1) r} Λ)).functor ⋙
      (Scheme.pointSmallEtale s.hom).sheafFiber)).ShortExact :=
  ShortComplex.shortExact_of_iso
    (S.mapNatIso (sheafEquivCompSheafFiberIso.{u, max (u + 1) r, r} B X Λ s)).symm (hS s)

include hS in
/-- **The local factor is multiplicative along a stalkwise short exact sequence.** -/
public theorem finiteProjectiveLocalCharSeries_X₂_eq_mul (x : closedPoints X.obj) :
    finiteProjectiveLocalCharSeries.{u, max (u + 1) r, r} B X Λ S.X₂ f hfin₂ hproj₂ x =
      finiteProjectiveLocalCharSeries.{u, max (u + 1) r, r} B X Λ S.X₁ f hfin₁ hproj₁ x *
        finiteProjectiveLocalCharSeries.{u, max (u + 1) r, r} B X Λ S.X₃ f hfin₃ hproj₃ x := by
  have := finite_residueField f x.1 x.2
  have hE := shortExact_map_sheafEquiv_sheafFiber B X Λ S hS (geometricPointAt X.obj x.1)
  have := finite_sheafFiber_sheafEquiv B X Λ (geometricPointAt X.obj x.1) S.X₁ (hfin₁ _)
  have := projective_sheafFiber_sheafEquiv B X Λ S.X₁ (geometricPointAt X.obj x.1) (hproj₁ _)
  have := finite_sheafFiber_sheafEquiv B X Λ (geometricPointAt X.obj x.1) S.X₂ (hfin₂ _)
  have := projective_sheafFiber_sheafEquiv B X Λ S.X₂ (geometricPointAt X.obj x.1) (hproj₂ _)
  have := finite_sheafFiber_sheafEquiv B X Λ (geometricPointAt X.obj x.1) S.X₃ (hfin₃ _)
  have := projective_sheafFiber_sheafEquiv B X Λ S.X₃ (geometricPointAt X.obj x.1) (hproj₃ _)
  have h₁ := frobeniusStalk_naturality (ModuleCat.{max (u + 1) r} Λ) X.obj x.1
    ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{max (u + 1) r} Λ)).functor.map S.f)
  have h₂ := frobeniusStalk_naturality (ModuleCat.{max (u + 1) r} Λ) X.obj x.1
    ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{max (u + 1) r} Λ)).functor.map S.g)
  let L := (SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{max (u + 1) r} Λ)).functor
  let Φ := (Scheme.pointSmallEtale (geometricPointAt X.obj x.1).hom).sheafFiber
    (A := ModuleCat.{max (u + 1) r} Λ)
  let i : Φ.obj (L.obj S.X₁) →ₗ[Λ] Φ.obj (L.obj S.X₂) := (Φ.map (L.map S.f)).hom
  let q : Φ.obj (L.obj S.X₂) →ₗ[Λ] Φ.obj (L.obj S.X₃) := (Φ.map (L.map S.g)).hom
  have hi : Function.Injective i := hE.moduleCat_injective_f
  have hex : Function.Exact i q :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hE.exact
  have hq : Function.Surjective q := hE.moduleCat_surjective_g
  have hα : (frobeniusStalk (ModuleCat.{max (u + 1) r} Λ) X.obj x.1 (L.obj S.X₂)).hom.comp i =
      i.comp (frobeniusStalk (ModuleCat.{max (u + 1) r} Λ) X.obj x.1 (L.obj S.X₁)).hom := by
    simpa only [ModuleCat.hom_comp] using congrArg ModuleCat.Hom.hom h₁
  have hβ : q.comp (frobeniusStalk (ModuleCat.{max (u + 1) r} Λ) X.obj x.1 (L.obj S.X₂)).hom =
      (frobeniusStalk (ModuleCat.{max (u + 1) r} Λ) X.obj x.1 (L.obj S.X₃)).hom.comp q := by
    simpa only [ModuleCat.hom_comp] using congrArg ModuleCat.Hom.hom h₂.symm
  exact ProjectiveDeterminant.charSeries_of_exact hi hex hq _ _ _ hα hβ _

include hS in
/-- The local Euler factor is multiplicative along a stalkwise short exact sequence. -/
public theorem finiteProjectiveLocalFactor_X₂_eq_mul (x : closedPoints X.obj) :
    finiteProjectiveLocalFactor.{u, max (u + 1) r, r} B X Λ S.X₂ f hfin₂ hproj₂ x =
      finiteProjectiveLocalFactor.{u, max (u + 1) r, r} B X Λ S.X₁ f hfin₁ hproj₁ x *
        finiteProjectiveLocalFactor.{u, max (u + 1) r, r} B X Λ S.X₃ f hfin₃ hproj₃ x := by
  have h₁ := finiteProjectiveLocalCharSeries_mul_localFactor.{u, max (u + 1) r, r} B X Λ S.X₁ f
    hfin₁ hproj₁ x
  have h₂ := finiteProjectiveLocalCharSeries_mul_localFactor.{u, max (u + 1) r, r} B X Λ S.X₂ f
    hfin₂ hproj₂ x
  have h₃ := finiteProjectiveLocalCharSeries_mul_localFactor.{u, max (u + 1) r, r} B X Λ S.X₃ f
    hfin₃ hproj₃ x
  rw [finiteProjectiveLocalCharSeries_X₂_eq_mul B X Λ S hS hfin₁ hproj₁ hfin₂ hproj₂ hfin₃ hproj₃
    f x] at h₂
  set a₁ := finiteProjectiveLocalCharSeries.{u, max (u + 1) r, r} B X Λ S.X₁ f hfin₁ hproj₁ x
  set a₃ := finiteProjectiveLocalCharSeries.{u, max (u + 1) r, r} B X Λ S.X₃ f hfin₃ hproj₃ x
  set b₁ := finiteProjectiveLocalFactor.{u, max (u + 1) r, r} B X Λ S.X₁ f hfin₁ hproj₁ x
  set b₂ := finiteProjectiveLocalFactor.{u, max (u + 1) r, r} B X Λ S.X₂ f hfin₂ hproj₂ x
  set b₃ := finiteProjectiveLocalFactor.{u, max (u + 1) r, r} B X Λ S.X₃ f hfin₃ hproj₃ x
  calc b₂ = b₂ * ((a₁ * b₁) * (a₃ * b₃)) := by rw [h₁, h₃, mul_one, mul_one]
    _ = (a₁ * a₃ * b₂) * (b₁ * b₃) := by ring
    _ = b₁ * b₃ := by rw [h₂, one_mul]

variable [QuasiCompact f]

include hS in
/-- **The L-function is multiplicative along a stalkwise short exact sequence**: for
`0 → F' → F → F'' → 0` exact on stalks, with finite projective stalks,
`L(X, F) = L(X, F') · L(X, F'')`. -/
public theorem lFunctionOfFiniteProjectiveStalks_X₂_eq_mul :
    lFunctionOfFiniteProjectiveStalks.{u, max (u + 1) r, r} B X Λ S.X₂ f hfin₂ hproj₂ =
      lFunctionOfFiniteProjectiveStalks.{u, max (u + 1) r, r} B X Λ S.X₁ f hfin₁ hproj₁ *
        lFunctionOfFiniteProjectiveStalks.{u, max (u + 1) r, r} B X Λ S.X₃ f hfin₃ hproj₃ :=
  EulerSystem.eulerProduct_eq_mul _ _ _ (fun _ => rfl) (fun _ => rfl)
    (finiteProjectiveLocalFactor_X₂_eq_mul B X Λ S hS hfin₁ hproj₁ hfin₂ hproj₂ hfin₃ hproj₃ f)

omit hS in
/-- **The L-function is multiplicative along a short exact sequence of sheaves.** -/
public theorem lFunctionOfFiniteProjectiveStalks_X₂_eq_mul_of_shortExact (hS : S.ShortExact) :
    lFunctionOfFiniteProjectiveStalks.{u, max (u + 1) r, r} B X Λ S.X₂ f hfin₂ hproj₂ =
      lFunctionOfFiniteProjectiveStalks.{u, max (u + 1) r, r} B X Λ S.X₁ f hfin₁ hproj₁ *
        lFunctionOfFiniteProjectiveStalks.{u, max (u + 1) r, r} B X Λ S.X₃ f hfin₃ hproj₃ :=
  lFunctionOfFiniteProjectiveStalks_X₂_eq_mul B X Λ S (fun s => by
    have : AB5OfSize.{u, u} (ModuleCat.{max (u + 1) r} Λ) :=
      AB5OfSize_shrink.{u, u, max (u + 1) r, max (u + 1) r} (C := ModuleCat.{max (u + 1) r} Λ)
    have := preservesFiniteLimits_etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s
    have := preservesFiniteColimits_etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s
    exact hS.map_of_exact _) hfin₁ hproj₁ hfin₂ hproj₂ hfin₃ hproj₃ f

end Stacks.EtaleCohomology

end
