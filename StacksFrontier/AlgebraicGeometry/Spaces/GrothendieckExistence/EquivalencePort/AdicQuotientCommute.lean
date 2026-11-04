module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.IdealPowerAnnihilationAffine

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Quotients by powers of two sheaves of ideals commute

For sheaves of ideals `𝓘`, `𝓚` of `𝒪_F` and an `𝒪_F`-module `M`,
`(M / 𝓚^e M) / 𝓘^m (M / 𝓚^e M) ≅ (M / 𝓘^m M) / 𝓚^e (M / 𝓘^m M)`
(`AlgebraicGeometry.Space.C1573.adicQuotientCommIso`), both being the universal quotient of `M`
killed by `𝓘^m` and by `𝓚^e`.

## Main definitions

* `AlgebraicGeometry.Space.C1573.smallEtaleAdicQuotientLift`: The factorisation through
  `M / 𝓘^k M` of a morphism into a module annihilated by `𝓘^k`.
* `AlgebraicGeometry.Space.C1573.adicQuotientCommIso`: The isomorphism
  `(M / 𝓚^e M) / 𝓘^m ≅ (M / 𝓘^m M) / 𝓚^e`.
* `AlgebraicGeometry.Space.C1573.adicQuotientQuotientIso`: The isomorphism
  `(M / 𝓚^(e+1) M) / 𝓚^e ≅ M / 𝓚^e M`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

section Lift

variable (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- A morphism into a module annihilated by `𝓘 ^ k` factors through `M / 𝓘 ^ k M`. -/
def C1573.smallEtaleAdicQuotientLift (k : ℕ) {M T : Modules.{u, u} B S hS F hF} (g : M ⟶ T)
    (hT : IsPowAnnihilated B S hS F hF 𝓘 k T) :
    smallEtaleAdicQuotient B S hS F hF 𝓘 k M ⟶ T :=
  cokernel.desc _ g ((idealPowerSubsheaf_ι_comp_zero_iff B S hS F hF 𝓘 k _).2 fun U r hr x =>
    ((g.val.app (op U)).hom.map_smul r x).trans (hT U r hr _))

/-- The lift `M / 𝓘^k M ⟶ T` of `g` composed with the projection `M ⟶ M / 𝓘^k M` is `g`. -/
@[reassoc (attr := simp)]
theorem C1573.smallEtaleAdicQuotientProjection_lift (k : ℕ) {M T : Modules.{u, u} B S hS F hF}
    (g : M ⟶ T) (hT : IsPowAnnihilated B S hS F hF 𝓘 k T) :
    smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k M ≫
        smallEtaleAdicQuotientLift B S hS F hF 𝓘 k g hT = g :=
  cokernel.π_desc _ _ _

end Lift

variable (𝓘 𝓚 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (e m : ℕ) (M : Modules.{u, u} B S hS F hF)

/-- `(M / 𝓘^m M) / 𝓚^e` is annihilated by `𝓘^m`. -/
theorem C1573.isPowAnnihilated_quotient_quotient :
    IsPowAnnihilated B S hS F hF 𝓘 m
      (smallEtaleAdicQuotient B S hS F hF 𝓚 e (smallEtaleAdicQuotient B S hS F hF 𝓘 m M)) :=
  isPowAnnihilated_of_epi B S hS F hF 𝓘 m
    (smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e _)
    (isPowAnnihilated_smallEtaleAdicQuotient B S hS F hF 𝓘 m M)

/-- The comparison `(M / 𝓚^e) / 𝓘^m ⟶ (M / 𝓘^m) / 𝓚^e`. -/
def C1573.adicQuotientCommHom :
    smallEtaleAdicQuotient B S hS F hF 𝓘 m (smallEtaleAdicQuotient B S hS F hF 𝓚 e M) ⟶
      smallEtaleAdicQuotient B S hS F hF 𝓚 e (smallEtaleAdicQuotient B S hS F hF 𝓘 m M) :=
  smallEtaleAdicQuotientLift B S hS F hF 𝓘 m
    (smallEtaleAdicQuotientLift B S hS F hF 𝓚 e
      (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 m M ≫
        smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e _)
      (isPowAnnihilated_smallEtaleAdicQuotient B S hS F hF 𝓚 e _))
    (isPowAnnihilated_quotient_quotient B S hS F hF 𝓘 𝓚 e m M)

/-- The comparison `(M / 𝓚^e) / 𝓘^m ⟶ (M / 𝓘^m) / 𝓚^e` composed with the projection
`M ⟶ (M / 𝓚^e) / 𝓘^m` is the projection `M ⟶ (M / 𝓘^m) / 𝓚^e`. -/
@[reassoc (attr := simp)]
theorem C1573.adicQuotientCommHom_spec :
    smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e M ≫
        smallEtaleAdicQuotientProjection B S hS F hF 𝓘 m _ ≫
          adicQuotientCommHom B S hS F hF 𝓘 𝓚 e m M =
      smallEtaleAdicQuotientProjection B S hS F hF 𝓘 m M ≫
        smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e _ := by
  simp [adicQuotientCommHom]

/-- **`(M / 𝓚^e M) / 𝓘^m ≅ (M / 𝓘^m M) / 𝓚^e`.** -/
def C1573.adicQuotientCommIso :
    smallEtaleAdicQuotient B S hS F hF 𝓘 m (smallEtaleAdicQuotient B S hS F hF 𝓚 e M) ≅
      smallEtaleAdicQuotient B S hS F hF 𝓚 e (smallEtaleAdicQuotient B S hS F hF 𝓘 m M) where
  hom := adicQuotientCommHom B S hS F hF 𝓘 𝓚 e m M
  inv := adicQuotientCommHom B S hS F hF 𝓚 𝓘 m e M
  hom_inv_id := by
    refine (cancel_epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e M ≫
      smallEtaleAdicQuotientProjection B S hS F hF 𝓘 m _)).1 ?_
    simp
  inv_hom_id := by
    refine (cancel_epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 m M ≫
      smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e _)).1 ?_
    simp

/-- **`(M / 𝓚^(e+1) M) / 𝓚^e ≅ M / 𝓚^e M`**, induced by the transition map
`M / 𝓚^(e+1) M ⟶ M / 𝓚^e M`. -/
def C1573.adicQuotientQuotientIso (e : ℕ) (M : Modules.{u, u} B S hS F hF) :
    smallEtaleAdicQuotient B S hS F hF 𝓚 e (smallEtaleAdicQuotient B S hS F hF 𝓚 (e + 1) M) ≅
      smallEtaleAdicQuotient B S hS F hF 𝓚 e M where
  hom := smallEtaleAdicQuotientLift B S hS F hF 𝓚 e
    (smallEtaleAdicQuotientTransition B S hS F hF 𝓚 e M)
    (isPowAnnihilated_smallEtaleAdicQuotient B S hS F hF 𝓚 e M)
  inv := smallEtaleAdicQuotientLift B S hS F hF 𝓚 e
    (smallEtaleAdicQuotientProjection B S hS F hF 𝓚 (e + 1) M ≫
      smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e _)
    (isPowAnnihilated_smallEtaleAdicQuotient B S hS F hF 𝓚 e _)
  hom_inv_id := by
    refine (cancel_epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓚 (e + 1) M ≫
      smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e _)).1 ?_
    simp only [Category.assoc, smallEtaleAdicQuotientProjection_lift_assoc, Category.comp_id]
    rw [← Category.assoc, smallEtaleAdicQuotientProjection_comp_transition,
      smallEtaleAdicQuotientProjection_lift]
  inv_hom_id := by
    refine (cancel_epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e M)).1 ?_
    simp only [Category.assoc, smallEtaleAdicQuotientProjection_lift_assoc, Category.comp_id,
      smallEtaleAdicQuotientProjection_lift]
    exact smallEtaleAdicQuotientProjection_comp_transition B S hS F hF 𝓚 e M

/-- The projection `M / 𝓚^(e+1) M ⟶ (M / 𝓚^(e+1) M) / 𝓚^e` followed by
`(M / 𝓚^(e+1) M) / 𝓚^e ≅ M / 𝓚^e M` is the transition map `M / 𝓚^(e+1) M ⟶ M / 𝓚^e M`. -/
@[reassoc (attr := simp)]
theorem C1573.smallEtaleAdicQuotientProjection_adicQuotientQuotientIso_hom (e : ℕ)
    (M : Modules.{u, u} B S hS F hF) :
    smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e _ ≫
        (adicQuotientQuotientIso B S hS F hF 𝓚 e M).hom =
      smallEtaleAdicQuotientTransition B S hS F hF 𝓚 e M :=
  smallEtaleAdicQuotientProjection_lift B S hS F hF 𝓚 e
    (smallEtaleAdicQuotientTransition B S hS F hF 𝓚 e M)
    (isPowAnnihilated_smallEtaleAdicQuotient B S hS F hF 𝓚 e M)

end AlgebraicGeometry.Space

end
