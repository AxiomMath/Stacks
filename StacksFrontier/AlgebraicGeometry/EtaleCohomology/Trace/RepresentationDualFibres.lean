module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationDualCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportExtFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.InverseImageAlongMorphism

/-!
# The geometric fibres of the dual coefficients of `ℱ_ρ`

For an open immersion `j`, the inverse images `g⁻¹ j_! K` of pow-exact étale sheaves `K` of
`ℤ/pᵐ`-modules have flat fibres at all points with separably closed residue field. For a proper `X`
over a field `k` with identity compactification `j` and a field extension `k̄` of `k`,
`(j_! K)|_{X_k̄}` is lisse for every lisse `K`. The levels of the ℓ-adic sheaf of a continuous
`ℤ_ℓ`-representation are lisse.

All names are in the namespace `Stacks.EtaleCohomology`.

## Main results

* `isPowExact_of_powExact_moduleCat`: an object of `ModuleCat (ℤ/pᵐ)` which is pow-exact is
  pow-exact as a module.
* `flat_sheafFiber_of_powExact`: pow-exact étale sheaves have flat fibres.
* `flat_sheafFiber_inverseImage_extensionByZero_of_powExact`: so do inverse images of their
  extensions by zero.
* `isFiniteTypeLocallyConstant_inverseImage_extensionByZero_ofProper`: `(j_! K)|_{X_k̄}` is lisse.
* `isFiniteTypeLocallyConstant_etaleLevel_representationLAdicSheaf`: the levels of the sheaf of a
  continuous `ℤ_ℓ`-representation are lisse.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u v

namespace Stacks.EtaleCohomology

open Stacks.ZModPrimePower Stacks.Frobenius

/-! ### Pow-exactness of fibres -/

section PowExact

variable {p m : ℕ}

/-- **A pow-exact object of `ModuleCat (ℤ/pᵐ)` is a pow-exact module.** -/
theorem isPowExact_of_powExact_moduleCat {M : ModuleCat.{v} (ZMod (p ^ m))}
    (hM : PowExact p m M) : IsPowExact p m M := by
  intro a ha x hx
  let S := Submodule.span (ZMod (p ^ m)) {x}
  let g : ModuleCat.of (ZMod (p ^ m)) S ⟶ M := ModuleCat.ofHom S.subtype
  have hg : g ≫ ((p ^ a) • 𝟙 _) = 0 := by
    ext z
    obtain ⟨y, hy⟩ := z
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    change p ^ a • (c • x) = 0
    rw [smul_comm, hx, smul_zero]
  obtain ⟨T, π, hπ, y, hy⟩ := hM a ha g hg
  obtain ⟨t, ht⟩ := (ModuleCat.epi_iff_surjective π).1 hπ
    ⟨x, Submodule.mem_span_singleton_self x⟩
  refine ⟨y.hom t, ?_⟩
  have := congrArg (fun φ => φ.hom t) hy
  change (g.hom (π.hom t)) = p ^ (m - a) • y.hom t at this
  rw [ht] at this
  exact this.symm

/-- **Pow-exact étale sheaves have flat fibres**: the fibre of a pow-exact étale sheaf of
`ℤ/pᵐ`-modules at a point with separably closed residue field is a flat `ℤ/pᵐ`-module. -/
theorem flat_sheafFiber_of_powExact [Fact p.Prime] {S : Scheme.{u}}
    (K : EtaleModules.{u, 0} (ZMod (p ^ m)) S) (hK : PowExact p m K) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ S) :
    Module.Flat (ZMod (p ^ m)) ((Scheme.pointSmallEtale t).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (p ^ m))) |>.obj K) := by
  have : AB5OfSize.{u, u} (ModuleCat.{u + 1} (ZMod (p ^ m))) :=
    AlgebraicGeometry.aB5OfSize_moduleCat_of_univLE.{u, u + 1, 0} (ZMod (p ^ m))
  have : PreservesFiniteLimits ((Scheme.pointSmallEtale t).sheafFiber
    (A := ModuleCat.{u + 1} (ZMod (p ^ m)))) := inferInstance
  have : ((Scheme.pointSmallEtale t).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (p ^ m)))).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact flat_of_isPowExact (isPowExact_of_powExact_moduleCat
    (hK.map _ (zmodSheaf_nsmul_id S.smallEtaleTopology (p ^ m) K)))

/-- **Flat fibres of `g⁻¹ j_! K` for a pow-exact `K`**: for an open immersion `j : U ⟶ X̄`, a
morphism `g : Y ⟶ X̄` and a pow-exact sheaf `K` of `ℤ/pᵐ`-modules on `U`, the fibres of
`g⁻¹ j_! K` at all points of `Y` with separably closed residue field are flat. -/
theorem flat_sheafFiber_inverseImage_extensionByZero_of_powExact [Fact p.Prime]
    {U Xbar Y : Scheme.{u}} (j : U ⟶ Xbar) [IsOpenImmersion j] (g : Y ⟶ Xbar)
    (K : EtaleModules.{u, 0} (ZMod (p ^ m)) U) (hK : PowExact p m K) (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    Module.Flat (ZMod (p ^ m))
      ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} (ZMod (p ^ m)))).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod (p ^ m)) g).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (p ^ m)) j).obj K))) :=
  flat_sheafFiber_ulift_inverseImage (ZMod (p ^ m)) g s _
    (flat_sheafFiber_extensionByZero (ZMod (p ^ m)) j (s ≫ g) K
      fun t _ => flat_sheafFiber_of_powExact K hK t)

end PowExact

/-! ### Lisse sheaves on the identity compactification -/

section Lisse

attribute [local instance] moduleCat_hasLimitsOfSize

/-- **`(j_! K)|_{X_k̄}` is lisse for `K` lisse and `j` the identity compactification** of a proper
`X` over `k`. -/
theorem isFiniteTypeLocallyConstant_inverseImage_extensionByZero_ofProper (N : ℕ)
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (kbar : Type u) [Field kbar] [Algebra k kbar] (K : EtaleModules.{u, 0} (ZMod N) X)
    (hK : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod N) X.smallEtaleTopology K) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod N)
      (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} (ZMod N) (fieldBaseChangeProj (Over.mk f) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod N)
          (CompactificationOf.ofProper f).immersion).obj K)) :=
  lccModules_etaleModuleInverseImage N (fieldBaseChangeProj (Over.mk f) kbar) _
    (Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ (ZMod N)
      ((etaleModuleExtensionByZeroIdIso (ZMod N) X).app K).symm hK)

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]
  (ρ₀ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ₀ : Continuous ρ₀)

/-- **The levels of the sheaf of a continuous `ℤ_ℓ`-representation are lisse on Mathlib's small
étale site.** -/
theorem isFiniteTypeLocallyConstant_etaleLevel_representationLAdicSheaf (n : ℕ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1))) X.1.smallEtaleTopology
      (LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀) n) := by
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  exact (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_functor_iff B X (ZMod (ℓ ^ (n + 1)))
    _).2 (isFiniteTypeLocallyConstant_representationLevelSheaf B X x _ ρ₀ hρ₀ (n + 1))

end Lisse

end Stacks.EtaleCohomology

end
