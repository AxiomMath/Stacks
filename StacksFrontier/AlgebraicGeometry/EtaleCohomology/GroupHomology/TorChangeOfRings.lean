module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.FiniteGroupTor

/-!
# Change of rings for `Tor` over the group algebras of finite groups

Let `Λ` be a finite ring and `π : Q' → Q` a homomorphism of finite discrete groups, inducing the
ring map `Λ[Q'] → Λ[Q]`. For a finite `Λ`-module `M` with an action of `Q`, the change-of-rings
map

`Tor_i^{Λ[Q']}(res_π M, Λ) ⟶ Tor_i^{Λ[Q]}(M, Λ)`

is a morphism of homological δ-functors in `M`: natural in `M` and compatible with the connecting
maps (`Stacks.GroupHomology.torChangeOfRings`). In degree zero it is the projection of
coinvariants `M_{Q'} → M_Q`, `[m] ↦ [m]` (`Stacks.GroupHomology.torChangeOfRings_app_zero`).

It is defined by this property: the target `Tor_•^{Λ[Q]}(-, Λ)` is a universal homological
δ-functor on finite modules (`Stacks.GroupHomology.isUniversal_torDelta`, since the free modules
`Λ[Q]^k` cover every finite module and have no higher `Tor`), so a morphism into it is determined
by its degree-zero part (`Stacks.GroupHomology.torChangeOfRings_eq`). Any other construction with
these two properties, such as the classical one by a comparison of projective resolutions, gives
the same map; that construction is not formalized here.

Coinflation `H_i(Q', res_π M) ⟶ H_i(Q, M)`, the character dual of inflation
`Hⁱ(Q, M^∨) ⟶ Hⁱ(Q', res_π M^∨)`, is a morphism of homological δ-functors
(`Stacks.GroupHomology.coinflation`), since inflation is one and character duality is exact; in
degree zero it is the projection of coinvariants (`Stacks.GroupHomology.coinflation_app_zero_comp`).
Hence, through `H_i(Q, -) ≅ Tor_i^{Λ[Q]}(-, Λ)` (`Stacks.GroupHomology.homologyTorIso`), coinflation
is the change-of-rings map (`Stacks.GroupHomology.coinflation_comp_homologyTorIso`,
`Stacks.GroupHomology.torChangeOfRings_app_app`).

## Main definitions

* `Stacks.GroupHomology.coinvariantsProjection`: `M_{Q'} → M_Q`, naturally in `M`.
* `Stacks.GroupHomology.torChangeOfRings`: the change-of-rings morphism of δ-functors.
* `Stacks.GroupHomology.coinflation`: coinflation, as a morphism of δ-functors.

## Main results

* `Stacks.GroupHomology.torChangeOfRings_app_zero`, `Stacks.GroupHomology.torChangeOfRings_eq`.
* `Stacks.GroupHomology.coinflation_comp_homologyTorIso`: coinflation is the change-of-rings map.

## References

* [Stacks Project, Section 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.ContinuousCohomology
  Stacks.CategoryHomology

universe w

namespace Stacks.GroupHomology

variable (Λ : Type) [Ring Λ] [Finite Λ]
  {Q Q' : Type w} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]
  [DiscreteTopology Q] [Group Q'] [TopologicalSpace Q'] [IsTopologicalGroup Q'] [CompactSpace Q']
  [DiscreteTopology Q'] (π : Q' →ₜ* Q)

/-- Restriction along `π` preserves finite limits (instance form). -/
local instance : PreservesFiniteLimits (finiteTypeContinuousModuleRes.{0, w, w} Λ π) :=
  preservesFiniteLimits_finiteTypeContinuousModuleRes π

/-- Restriction along `π` preserves finite colimits (instance form). -/
local instance : PreservesFiniteColimits (finiteTypeContinuousModuleRes.{0, w, w} Λ π) :=
  preservesFiniteColimits_finiteTypeContinuousModuleRes π

omit [Finite Λ] [IsTopologicalGroup Q] [CompactSpace Q] [DiscreteTopology Q]
  [IsTopologicalGroup Q'] [CompactSpace Q'] [DiscreteTopology Q'] in
/-- The differences `π(q') m - m` are differences `q m - m`. -/
theorem coinvariantsKer_res_le (N : FiniteTypeContinuousModule.{0, w, w} Λ Q) :
    Stacks.Trace.coinvariantsKer (finiteTypeContinuousModuleRepresentation Λ Q'
        ((finiteTypeContinuousModuleRes Λ (ContinuousMonoidHom.id Q')).obj
          ((finiteTypeContinuousModuleRes Λ π).obj N))) ≤
      Stacks.Trace.coinvariantsKer (finiteTypeContinuousModuleRepresentation Λ Q
        ((finiteTypeContinuousModuleRes Λ (ContinuousMonoidHom.id Q)).obj N)) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨⟨g, x⟩, rfl⟩
  exact ⟨(π g, x), rfl⟩

/-- **The projection of coinvariants `M_{Q'} → M_Q`**, `[m] ↦ [m]`, for `Q'` acting on `M`
through `π`, naturally in `M`. -/
def coinvariantsProjection :
    finiteTypeContinuousModuleRes.{0, w, w} Λ π ⋙
        restrictedCoinvariantsFunctor Λ (ContinuousMonoidHom.id Q') ⟶
      restrictedCoinvariantsFunctor Λ (ContinuousMonoidHom.id Q) where
  app N := ModuleCat.ofHom (Submodule.mapQ _ _ LinearMap.id (coinvariantsKer_res_le Λ π N))
  naturality _ _ _ := by
    apply ModuleCat.hom_ext
    apply Submodule.linearMap_qext
    rfl

omit [Finite Λ] [IsTopologicalGroup Q] [CompactSpace Q] [DiscreteTopology Q]
  [IsTopologicalGroup Q'] [CompactSpace Q'] [DiscreteTopology Q'] in
/-- The projection of coinvariants sends the class of `m` to the class of `m`. -/
@[simp]
theorem coinvariantsProjection_app_mk (N : FiniteTypeContinuousModule.{0, w, w} Λ Q)
    (x : N.obj.obj.obj.V) :
    ((coinvariantsProjection Λ π).app N).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x :=
  rfl

/-- The source of the change-of-rings map: `M ↦ Tor_i^{Λ[Q']}(res_π M, Λ)`. -/
abbrev torChangeOfRingsSource :
    HomologicalDeltaFunctor (FiniteTypeContinuousModule.{0, w, w} Λ Q) (ModuleCat.{w} Λ) :=
  (torDelta Λ Q').precomp (finiteTypeContinuousModuleRes.{0, w, w} Λ π)

/-- The degree-zero part of the change-of-rings map: the projection of coinvariants, read on
`Tor_0^{Λ[Q']}(res_π M, Λ) = M_{Q'}` and `Tor_0^{Λ[Q]}(M, Λ) = M_Q`. -/
def torChangeOfRingsZero :
    (torChangeOfRingsSource Λ π).functor 0 ⟶ (torDelta Λ Q).functor 0 :=
  Functor.whiskerLeft (finiteTypeContinuousModuleRes.{0, w, w} Λ π)
      ((torDeltaZeroIso Λ Q').hom ≫ (coinvariantsComparison (Λ := Λ) (Q := Q')).inv) ≫
    coinvariantsProjection Λ π ≫ (coinvariantsComparison (Λ := Λ) (Q := Q)).hom ≫
      (torDeltaZeroIso Λ Q).inv

/-- **The change-of-rings map `Tor_i^{Λ[Q']}(res_π M, Λ) ⟶ Tor_i^{Λ[Q]}(M, Λ)`** along the ring
map `Λ[Q'] → Λ[Q]` induced by `π`, as a morphism of homological δ-functors in `M`: the unique one
which in degree zero is the projection of coinvariants `M_{Q'} → M_Q`. -/
def torChangeOfRings : torChangeOfRingsSource Λ π ⟶ torDelta Λ Q :=
  haveI := isUniversal_torDelta Λ Q
  HomologicalDeltaFunctor.IsUniversal.lift (H := torDelta Λ Q) (torChangeOfRingsZero Λ π)

/-- In degree zero the change-of-rings map is the projection of coinvariants. -/
theorem torChangeOfRings_app_zero :
    (torChangeOfRings Λ π).app 0 = torChangeOfRingsZero Λ π :=
  haveI := isUniversal_torDelta Λ Q
  HomologicalDeltaFunctor.IsUniversal.lift_app_zero (H := torDelta Λ Q) _

/-- **The change-of-rings map is determined by degree zero**: a morphism of δ-functors
`Tor_•^{Λ[Q']}(res_π -, Λ) ⟶ Tor_•^{Λ[Q]}(-, Λ)` which in degree zero is the projection of
coinvariants is the change-of-rings map. -/
theorem torChangeOfRings_eq (η : torChangeOfRingsSource Λ π ⟶ torDelta Λ Q)
    (h : η.app 0 = torChangeOfRingsZero Λ π) : η = torChangeOfRings Λ π :=
  haveI := isUniversal_torDelta Λ Q
  HomologicalDeltaFunctor.IsUniversal.hom_ext_zero (H := torDelta Λ Q)
    (h.trans (torChangeOfRings_app_zero Λ π).symm)

section Coinflation

variable {Λ} in
/-- The restriction of the dual is the dual of the restriction: the identity of the characters of
`M`, equivariant because `π (g⁻¹) = (π g)⁻¹`. -/
def resDualHom (N : FiniteTypeContinuousModule.{0, w, w} Λ Q) :
    (finiteTypeContinuousModuleRes.{0, w, w} Λᵐᵒᵖ π).obj
        ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q).obj (Opposite.op N)) ⟶
      (finiteTypeContinuousModuleDual.{0, w, w} Λ Q').obj
        (Opposite.op ((finiteTypeContinuousModuleRes.{0, w, w} Λ π).obj N)) :=
  ObjectProperty.homMk ((Stacks.GroupCohomology.homEquiv Λᵐᵒᵖ Q' _ _).symm
    ⟨LinearMap.id, fun g c ↦ (characterRepresentation_apply_of_eq _
      (finiteTypeContinuousModuleRepresentation Λ Q N) π.toMonoidHom (fun _ ↦ rfl) g c).symm⟩)

omit [CompactSpace Q] [DiscreteTopology Q] [CompactSpace Q'] [DiscreteTopology Q'] in
/-- The identification of the restriction of the dual with the dual of the restriction is
natural. -/
theorem resDualHom_naturality {N N' : FiniteTypeContinuousModule.{0, w, w} Λ Q} (f : N ⟶ N') :
    (finiteTypeContinuousModuleRes.{0, w, w} Λᵐᵒᵖ π).map
        ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q).map f.op) ≫ resDualHom π N =
      resDualHom π N' ≫ (finiteTypeContinuousModuleDual.{0, w, w} Λ Q').map
        ((finiteTypeContinuousModuleRes.{0, w, w} Λ π).map f).op := by
  apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext
  apply Action.hom_ext; apply ModuleCat.hom_ext; rfl

/-- The dual of the component of coinflation: inflation `Hⁱ(Q, M^∨) ⟶ Hⁱ(Q', res_π M^∨)`, followed
by `res_π (M^∨) = (res_π M)^∨`. -/
def coinflationDual (n : ℕ) (N : FiniteTypeContinuousModule.{0, w, w} Λ Q) :
    ((cohomologyDelta Λᵐᵒᵖ Q).functor n).obj
        ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q).obj (Opposite.op N)) ⟶
      ((cohomologyDelta Λᵐᵒᵖ Q').functor n).obj
        ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q').obj
          (Opposite.op ((finiteTypeContinuousModuleRes.{0, w, w} Λ π).obj N))) :=
  ((inflation Λᵐᵒᵖ π).app n).app
      ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q).obj (Opposite.op N)) ≫
    ((cohomologyDelta Λᵐᵒᵖ Q').functor n).map (resDualHom π N)

omit [DiscreteTopology Q'] in
/-- The dual of coinflation is natural. -/
theorem coinflationDual_naturality (n : ℕ) {N N' : FiniteTypeContinuousModule.{0, w, w} Λ Q}
    (f : N ⟶ N') :
    coinflationDual Λ π n N' ≫ ((cohomologyDelta Λᵐᵒᵖ Q').functor n).map
        ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q').map
          ((finiteTypeContinuousModuleRes.{0, w, w} Λ π).map f).op) =
      ((cohomologyDelta Λᵐᵒᵖ Q).functor n).map
          ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q).map f.op) ≫ coinflationDual Λ π n N := by
  have h₁ := ((inflation Λᵐᵒᵖ π).app n).naturality
    ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q).map f.op)
  calc coinflationDual Λ π n N' ≫ ((cohomologyDelta Λᵐᵒᵖ Q').functor n).map
        ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q').map
          ((finiteTypeContinuousModuleRes.{0, w, w} Λ π).map f).op)
      = ((inflation Λᵐᵒᵖ π).app n).app
          ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q).obj (Opposite.op N')) ≫
        ((cohomologyDelta Λᵐᵒᵖ Q').functor n).map (resDualHom π N' ≫
          (finiteTypeContinuousModuleDual.{0, w, w} Λ Q').map
            ((finiteTypeContinuousModuleRes.{0, w, w} Λ π).map f).op) := by
        rw [coinflationDual, Functor.map_comp]
        exact Category.assoc _ _ _
    _ = ((inflation Λᵐᵒᵖ π).app n).app
          ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q).obj (Opposite.op N')) ≫
        ((cohomologyDelta Λᵐᵒᵖ Q').functor n).map
          ((finiteTypeContinuousModuleRes.{0, w, w} Λᵐᵒᵖ π).map
            ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q).map f.op) ≫ resDualHom π N) := by
        rw [resDualHom_naturality]
    _ = (((inflation Λᵐᵒᵖ π).app n).app
          ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q).obj (Opposite.op N')) ≫
        ((inflationTarget Λᵐᵒᵖ π).functor n).map
          ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q).map f.op)) ≫
        ((cohomologyDelta Λᵐᵒᵖ Q').functor n).map (resDualHom π N) := by
        rw [Functor.map_comp]
        exact (Category.assoc _ _ _).symm
    _ = (((cohomologyDelta Λᵐᵒᵖ Q).functor n).map
          ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q).map f.op) ≫
        ((inflation Λᵐᵒᵖ π).app n).app
          ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q).obj (Opposite.op N))) ≫
        ((cohomologyDelta Λᵐᵒᵖ Q').functor n).map (resDualHom π N) := by
        rw [h₁]
    _ = _ := Category.assoc _ _ _

/-- `res_π (M^∨) = (res_π M)^∨` on the dual of a short exact sequence. -/
def resDualShortComplexHom (S : ShortComplex (FiniteTypeContinuousModule.{0, w, w} Λ Q)) :
    (HomologicalDeltaFunctor.dualShortComplex
        (finiteTypeContinuousModuleDual.{0, w, w} Λ Q) S).map
        (finiteTypeContinuousModuleRes.{0, w, w} Λᵐᵒᵖ π) ⟶
      HomologicalDeltaFunctor.dualShortComplex (finiteTypeContinuousModuleDual.{0, w, w} Λ Q')
        (S.map (finiteTypeContinuousModuleRes.{0, w, w} Λ π)) where
  τ₁ := resDualHom π S.X₃
  τ₂ := resDualHom π S.X₂
  τ₃ := resDualHom π S.X₁
  comm₁₂ := resDualHom_naturality Λ π S.g
  comm₂₃ := resDualHom_naturality Λ π S.f

omit [DiscreteTopology Q'] in
/-- The dual of coinflation commutes with the connecting maps: inflation is a morphism of
δ-functors and `res_π (M^∨) = (res_π M)^∨` is natural. -/
theorem coinflationDual_comm {S : ShortComplex (FiniteTypeContinuousModule.{0, w, w} Λ Q)}
    (hS : S.ShortExact) (n : ℕ) :
    coinflationDual Λ π n S.X₁ ≫ (cohomologyDelta Λᵐᵒᵖ Q').δ
        (HomologicalDeltaFunctor.shortExact_dualShortComplex
          (finiteTypeContinuousModuleDual.{0, w, w} Λ Q')
          (hS.map_of_exact (finiteTypeContinuousModuleRes.{0, w, w} Λ π))) n =
      (cohomologyDelta Λᵐᵒᵖ Q).δ (HomologicalDeltaFunctor.shortExact_dualShortComplex
          (finiteTypeContinuousModuleDual.{0, w, w} Λ Q) hS) n ≫
        coinflationDual Λ π (n + 1) S.X₃ := by
  have hS₂ := HomologicalDeltaFunctor.shortExact_dualShortComplex
    (finiteTypeContinuousModuleDual.{0, w, w} Λ Q) hS
  have h₁ := (cohomologyDelta Λᵐᵒᵖ Q').δ_naturality
    (hS₂.map_of_exact (finiteTypeContinuousModuleRes.{0, w, w} Λᵐᵒᵖ π))
    (HomologicalDeltaFunctor.shortExact_dualShortComplex
      (finiteTypeContinuousModuleDual.{0, w, w} Λ Q')
      (hS.map_of_exact (finiteTypeContinuousModuleRes.{0, w, w} Λ π)))
    (resDualShortComplexHom Λ π S) n
  have h₂ := (inflation Λᵐᵒᵖ π).comm hS₂ n
  rw [coinflationDual, coinflationDual]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₁).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₂).trans (Category.assoc _ _ _))))

/-- **Coinflation** `H_i(Q', res_π M) ⟶ H_i(Q, M)`, as a morphism of homological δ-functors in
`M`: the character dual of inflation `Hⁱ(Q, M^∨) ⟶ Hⁱ(Q', res_π M^∨)`. -/
def coinflation :
    (restrictedHomologyDelta Λ (ContinuousMonoidHom.id Q')).precomp
        (finiteTypeContinuousModuleRes.{0, w, w} Λ π) ⟶
      restrictedHomologyDelta Λ (ContinuousMonoidHom.id Q) where
  app n :=
    { app N := (CharacterModule.moduleCatDualOfMulOppositeFunctor Λ).map
        (coinflationDual Λ π n N).op
      naturality _ _ f := HomologicalDeltaFunctor.map_op_comp_map_op_eq
        (CharacterModule.moduleCatDualOfMulOppositeFunctor Λ) _ _ _ _
        (coinflationDual_naturality Λ π n f) }
  comm {S} hS n := HomologicalDeltaFunctor.map_op_comp_map_op_eq
    (CharacterModule.moduleCatDualOfMulOppositeFunctor Λ) _ _ _ _ (coinflationDual_comm Λ π hS n)

omit [DiscreteTopology Q'] in
/-- The components of coinflation are the duals of inflation. -/
theorem coinflation_app_app (n : ℕ) (N : FiniteTypeContinuousModule.{0, w, w} Λ Q) :
    ((coinflation Λ π).app n).app N = (CharacterModule.moduleCatDualOfMulOppositeFunctor Λ).map
        (coinflationDual Λ π n N).op :=
  rfl

end Coinflation

section DegreeZero

/-- Cancelling `κ⁻¹ ≫ κ` and commuting `κ'⁻¹` past `m`, in any category. -/
private theorem comp_cancel_naturality {C : Type*} [Category C] {A A' B C₀ D D' E F : C}
    {r : A ⟶ B} {ki : B ⟶ C₀} {kh : C₀ ⟶ B} {ii : B ⟶ D} {k'i : D ⟶ E} {m : E ⟶ F}
    {im : D ⟶ D'} {k'i'' : D' ⟶ F} {d : A ⟶ A'} {r' : A' ⟶ D'} (h₁ : ki ≫ kh = 𝟙 B)
    (h₂ : im ≫ k'i'' = k'i ≫ m) (h₃ : r ≫ ii ≫ im = d ≫ r') :
    (r ≫ ki) ≫ (kh ≫ ii ≫ k'i) ≫ m = d ≫ r' ≫ k'i'' := by
  simp only [Category.assoc, reassoc_of% h₁, ← h₂, reassoc_of% h₃]

/-- Cancelling `b ≫ c ≫ c' ≫ b' = 𝟙`, in any category. -/
private theorem comp_cancel_cancel {C : Type*} [Category C] {W X Y Z T U : C}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (c' : Z ⟶ Y) (b' : Y ⟶ X) (p : X ⟶ T) (q : T ⟶ U)
    (h₁ : c ≫ c' = 𝟙 Y) (h₂ : b ≫ b' = 𝟙 X) :
    (a ≫ p) ≫ q = (a ≫ b ≫ c) ≫ (c' ≫ b') ≫ p ≫ q := by
  simp only [Category.assoc, reassoc_of% h₁, reassoc_of% h₂]

omit [Finite Λ] in
/-- A character `c` takes the value `w c` on the element of a finite module with double dual `w`. -/
private theorem apply_evalEquiv_symm {A : Type w} [AddCommGroup A] [Module Λ A] [Finite A]
    (w : CharacterModule (CharacterModule A)) (c : CharacterModule A) :
    c ((CharacterModule.evalEquiv A Λ).symm w) = w c := by
  conv_rhs => rw [← (CharacterModule.evalEquiv A Λ).apply_symm_apply w]
  rfl

omit [CompactSpace Q] [DiscreteTopology Q] in
variable {Λ} in
/-- `H_0(Q, M) ≅ M_Q`, tested against a character `c` of `M_Q`: the class `z`, a character of
`H⁰(Q, M^∨) = (M_Q)^∨`, goes to the element of `M_Q` on which `c` takes the value `z c`. -/
theorem restrictedHomologyZeroIso_hom_apply (N : FiniteTypeContinuousModule.{0, w, w} Λ Q)
    (z : CharacterModule
      (((restrictedCohomologyDelta Λᵐᵒᵖ (ContinuousMonoidHom.id Q)).functor 0).obj
        ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q).obj (Opposite.op N))))
    (c : CharacterModule ((restrictedCoinvariantsFunctor Λ (ContinuousMonoidHom.id Q)).obj N)) :
    c (((restrictedHomologyZeroIso Λ (ContinuousMonoidHom.id Q)).hom.app N).hom z) =
      z (((restrictedCohomologyZeroDualIso Λ (ContinuousMonoidHom.id Q)).app
        (Opposite.op N)).inv.hom c) := by
  have : Finite ((restrictedCoinvariantsFunctor Λ (ContinuousMonoidHom.id Q)).obj N) :=
    finite_coinvariants_finiteTypeContinuousModuleRepresentation Λ _
  change c ((CharacterModule.evalEquiv _ Λ).symm _) = _
  exact apply_evalEquiv_symm Λ _ c

omit [DiscreteTopology Q'] in
/-- **Inflation in degree zero is the dual of the projection of coinvariants**, read on
`H⁰(Q, M^∨) = (M_Q)^∨` and `H⁰(Q', (res_π M)^∨) = (M_{Q'})^∨`. -/
theorem coinflationDual_zero (N : FiniteTypeContinuousModule.{0, w, w} Λ Q) :
    ((restrictedCohomologyZeroDualIso Λ (ContinuousMonoidHom.id Q)).app (Opposite.op N)).inv ≫
        coinflationDual Λ π 0 N =
      (CharacterModule.moduleCatDualFunctor Λ).map ((coinvariantsProjection Λ π).app N).op ≫
        ((restrictedCohomologyZeroDualIso Λ (ContinuousMonoidHom.id Q')).app
          (Opposite.op ((finiteTypeContinuousModuleRes.{0, w, w} Λ π).obj N))).inv := by
  rw [coinflationDual, inflation, DeltaFunctor.IsUniversal.lift_app_zero]
  have h₁ := (cohomologyDeltaZeroIso Λᵐᵒᵖ Q).inv_hom_id_app
    ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q).obj (Opposite.op N))
  have h₂ := (cohomologyDeltaZeroIso Λᵐᵒᵖ Q').inv.naturality (resDualHom π N)
  have h₃ : (restrictedInvariantsDualIso Λ (ContinuousMonoidHom.id Q)).inv.app (Opposite.op N) ≫
      (invariantsInclusion Λᵐᵒᵖ π).app
        ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q).obj (Opposite.op N)) ≫
      (finiteTypeContinuousModuleToRes Λᵐᵒᵖ (ContinuousMonoidHom.id Q') ⋙
        continuousModuleRingInvariants.{0, w, w} Λᵐᵒᵖ Q').map (resDualHom π N) =
      (CharacterModule.moduleCatDualFunctor Λ).map ((coinvariantsProjection Λ π).app N).op ≫
        (restrictedInvariantsDualIso Λ (ContinuousMonoidHom.id Q')).inv.app
          (Opposite.op ((finiteTypeContinuousModuleRes.{0, w, w} Λ π).obj N)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    rfl
  exact comp_cancel_naturality h₁ h₂ h₃

omit [DiscreteTopology Q'] in
/-- **Coinflation in degree zero is the projection of coinvariants**, read on
`H_0(Q', res_π M) = M_{Q'}` and `H_0(Q, M) = M_Q`. -/
theorem coinflation_app_zero_comp :
    (coinflation Λ π).app 0 ≫ (restrictedHomologyZeroIso Λ (ContinuousMonoidHom.id Q)).hom =
      Functor.whiskerLeft (finiteTypeContinuousModuleRes.{0, w, w} Λ π)
          (restrictedHomologyZeroIso Λ (ContinuousMonoidHom.id Q')).hom ≫
        coinvariantsProjection Λ π := by
  ext N : 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine sub_eq_zero.1 (CharacterModule.eq_zero_of_character_apply fun c ↦ ?_)
  have e₁ := restrictedHomologyZeroIso_hom_apply N (((coinflation Λ π).app 0).app N z) c
  have e₂ := restrictedHomologyZeroIso_hom_apply
    ((finiteTypeContinuousModuleRes.{0, w, w} Λ π).obj N) z
    (c.comp ((coinvariantsProjection Λ π).app N).hom.toAddMonoidHom)
  let z' : CharacterModule (((cohomologyDelta Λᵐᵒᵖ Q').functor 0).obj
      ((finiteTypeContinuousModuleDual.{0, w, w} Λ Q').obj
        (Opposite.op ((finiteTypeContinuousModuleRes.{0, w, w} Λ π).obj N)))) := z
  have e₃ := congrArg z' (ConcreteCategory.congr_hom (coinflationDual_zero Λ π N) c)
  rw [map_sub, sub_eq_zero]
  exact e₁.trans (e₃.trans e₂.symm)

/-- **Coinflation is the change-of-rings map**: under `H_i(Q', -) ≅ Tor_i^{Λ[Q']}(-, Λ)` and
`H_i(Q, -) ≅ Tor_i^{Λ[Q]}(-, Λ)` (`Stacks.GroupHomology.homologyTorIso`), the coinflation
`H_i(Q', res_π M) ⟶ H_i(Q, M)` is `Tor_i^{Λ[Q']}(res_π M, Λ) ⟶ Tor_i^{Λ[Q]}(M, Λ)`, as morphisms
of δ-functors: both are morphisms into the universal `Tor_•^{Λ[Q]}(-, Λ)` with the projection of
coinvariants in degree zero. -/
theorem coinflation_comp_homologyTorIso :
    coinflation Λ π ≫ (homologyTorIso Λ Q).hom =
      HomologicalDeltaFunctor.Hom.precomp (finiteTypeContinuousModuleRes.{0, w, w} Λ π)
          (homologyTorIso Λ Q').hom ≫ torChangeOfRings Λ π := by
  have := isUniversal_torDelta Λ Q
  have := isUniversal_torDelta Λ Q'
  have := isUniversal_restrictedHomologyDelta_id Λ Q
  have := isUniversal_restrictedHomologyDelta_id Λ Q'
  apply HomologicalDeltaFunctor.IsUniversal.hom_ext_zero (H := torDelta Λ Q)
  rw [HomologicalDeltaFunctor.comp_app, HomologicalDeltaFunctor.comp_app,
    HomologicalDeltaFunctor.Hom.precomp_app, torChangeOfRings_app_zero, homologyTorIso,
    homologyTorIso, HomologicalDeltaFunctor.IsUniversal.isoOfIso_hom_app_zero,
    HomologicalDeltaFunctor.IsUniversal.isoOfIso_hom_app_zero]
  ext N : 2
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    (NatTrans.congr_app (coinflation_app_zero_comp Λ π) N)).trans ?_)
  exact comp_cancel_cancel _ _ _ _ _ _ _
    ((torDeltaZeroIso Λ Q').inv_hom_id_app ((finiteTypeContinuousModuleRes.{0, w, w} Λ π).obj N))
    ((coinvariantsComparison (Λ := Λ) (Q := Q')).hom_inv_id_app
      ((finiteTypeContinuousModuleRes.{0, w, w} Λ π).obj N))

/-- The change-of-rings map is coinflation, read through `H_i ≅ Tor_i`. -/
theorem torChangeOfRings_app_app (n : ℕ) (N : FiniteTypeContinuousModule.{0, w, w} Λ Q) :
    ((torChangeOfRings Λ π).app n).app N =
      ((homologyTorIso Λ Q').inv.app n).app ((finiteTypeContinuousModuleRes.{0, w, w} Λ π).obj N) ≫
        ((coinflation Λ π).app n).app N ≫ ((homologyTorIso Λ Q).hom.app n).app N :=
  (Iso.eq_inv_comp ((HomologicalDeltaFunctor.isoApp (homologyTorIso Λ Q') n).app
    ((finiteTypeContinuousModuleRes.{0, w, w} Λ π).obj N))).2
    (NatTrans.congr_app (congrArg (fun η ↦ η.app n) (coinflation_comp_homologyTorIso Λ π)) N).symm

end DegreeZero

end Stacks.GroupHomology

end
