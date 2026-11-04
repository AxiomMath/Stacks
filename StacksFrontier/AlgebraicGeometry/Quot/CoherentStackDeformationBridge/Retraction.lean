module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.Difference
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsIdComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardAssoc
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardRightExact

/-!
# The direct image along a retraction of a thickening of base changes

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB) and `h : T ⟶ T'` a first order
thickening of schemes over `Y` with a retraction `r : T' ⟶ T` over `Y`, `h ≫ r = 𝟙`. Write
`i : X_T ⟶ X_{T'}` and `ρ : X_{T'} ⟶ X_T` for the induced morphisms of small étale ringed topoi.
Since `X_h ≫ X_r = 𝟙`, the direct image `i_* ⋙ ρ_*` of sheaves of sets is the identity; as `i_*`
is an equivalence (the small étale topoi of a thickening agree, Stacks 04DY), so is `ρ_*`. Hence
the direct image of modules along `ρ` is exact, and `ρ_* ∘ i_*` is the identity on modules. This
is how classes of extensions of `𝒪_{X_{T'}}`-modules are read on `X_T` in the proofs of
Stacks 08W8 and Stacks 08WA.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.retractionDirectImageIso`: `i_* ⋙ ρ_* ≅ 𝟭` on
  sheaves of sets.
* `AlgebraicGeometry.Space.CoherentSituation.retractionModulePushforwardIso`:
  `i_* ⋙ ρ_* ≅ 𝟭` on modules.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isEquivalence_retraction_pushforward`: `ρ_*` is an
  equivalence of topoi.
* `AlgebraicGeometry.Space.CoherentSituation.preservesFiniteColimits_retraction_modulePushforward`:
  the direct image of modules along `ρ` is right exact.
* `AlgebraicGeometry.Space.CoherentSituation.preservesFiniteLimits_retraction_modulePushforward`:
  the direct image of modules along `ρ` is left exact.

## References

* [Stacks Project, Tag 04DY](https://stacks.math.columbia.edu/tag/04DY)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {T T' : SchemesOver D.Y} (h : T ⟶ T') (r : T' ⟶ T) (hr : h ≫ r = 𝟙 T)

include hr in
/-- The morphisms of base changes of a thickening and of a retraction of it compose to the
identity. -/
theorem relativeMap_comp_relativeMap_retraction :
    D.relativeSquareSituation.relativeMap h ≫ D.relativeSquareSituation.relativeMap r =
      𝟙 (D.space T) := by
  rw [← baseChangeMap_comp, hr, baseChangeMap_id]

/-- **`i_* ⋙ ρ_* ≅ 𝟭` on sheaves of sets**, for `i = X_h` and `ρ = X_r` with `h ≫ r = 𝟙`: the
comparison of Stacks 03G2, part (3), for the composite, which is the identity, followed by the
identification of the direct image along an identity with the identity functor. -/
def retractionDirectImageIso :
    (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).toToposHom.pushforward ⋙
      (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap r)).toToposHom.pushforward ≅
      𝟭 _ :=
  smallToposMorphismTypeU_comp B S hS _ _ ≪≫
    eqToIso (congrArg
      (fun k : D.space T ⟶ D.space T => (smallToposMorphismTypeU B S hS k).pushforward)
      (relativeMap_comp_relativeMap_retraction h r hr)) ≪≫
    smallEtaleDirectImageIdIso B S hS (D.space T)

include hr in
/-- **`ρ_*` is an equivalence of topoi**: `i_*` is one, the topoi of a first order thickening
being equivalent (Stacks 04DY), and `i_* ⋙ ρ_*` is the identity. -/
theorem isEquivalence_retraction_pushforward
    (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left)) :
    (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap r)).toToposHom.pushforward.IsEquivalence := by
  have := (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh).equiv
  have : ((smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).toToposHom.pushforward ⋙
      (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap r)).toToposHom.pushforward).IsEquivalence :=
    Functor.isEquivalence_of_iso (retractionDirectImageIso h r hr).symm
  exact Functor.isEquivalence_of_comp_left
    (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom.pushforward
    _

include hr in
/-- **The direct image of modules along `ρ` is right exact**: the direct image of sheaves of sets
along `ρ` is an equivalence, so it preserves epimorphisms. -/
theorem preservesFiniteColimits_retraction_modulePushforward
    (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left)) :
    PreservesFiniteColimits
      (modulePushforward B S hS (D.relativeSquareSituation.relativeMap r)) := by
  have := isEquivalence_retraction_pushforward h r hr hh
  have h₀ := RingedToposHom.preservesFiniteColimits_pushforwardModules
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap r))
  rw [pushforwardModules_eq_modulePushforward] at h₀
  exact h₀

/-- **The direct image of modules along `ρ` is left exact**, being a right adjoint. -/
theorem preservesFiniteLimits_retraction_modulePushforward :
    PreservesFiniteLimits (modulePushforward B S hS (D.relativeSquareSituation.relativeMap r)) := by
  have : PreservesLimitsOfSize.{0, 0}
      (modulePushforward B S hS (D.relativeSquareSituation.relativeMap r)) :=
    (modulePullbackAdjunction B S hS
      (D.relativeSquareSituation.relativeMap r)).rightAdjoint_preservesLimits
  exact PreservesLimitsOfSize0.preservesFiniteLimits _

/-- **`i_* ⋙ ρ_* ≅ 𝟭` on modules**: the comparison of the direct images of modules of a composite
(Stacks 03LU) followed by the unit law for the identity. -/
def retractionModulePushforwardIso :
    modulePushforward B S hS (D.relativeSquareSituation.relativeMap h) ⋙
      modulePushforward B S hS (D.relativeSquareSituation.relativeMap r) ≅ 𝟭 _ :=
  modulePushforwardCompIso B S hS _ _ ≪≫
    eqToIso (congrArg (modulePushforward B S hS)
      (relativeMap_comp_relativeMap_retraction h r hr)) ≪≫
    modulePushforwardIdIso B S hS (D.space T)

include hr in
/-- **The direct image of modules along `ρ` is right exact**, in the spelling of the morphism of
small étale ringed topoi. -/
theorem preservesFiniteColimits_retraction_pushforwardModules
    (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left)) :
    PreservesFiniteColimits
      (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap r)).pushforwardModules := by
  rw [pushforwardModules_eq_modulePushforward]
  exact preservesFiniteColimits_retraction_modulePushforward h r hr hh

/-- **The direct image of modules along `ρ` is left exact**, being a right adjoint, in the
spelling of the morphism of small étale ringed topoi. -/
theorem preservesFiniteLimits_retraction_pushforwardModules :
    PreservesFiniteLimits
      (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap r)).pushforwardModules := by
  rw [pushforwardModules_eq_modulePushforward]
  exact preservesFiniteLimits_retraction_modulePushforward r

/-- **`(𝟙 X)_* ≅ 𝟭` on modules over the small étale ringed topos of `X`**: the unit law of
Stacks 03LU, `AlgebraicGeometry.Space.pushforwardModulesIsoIdSmallEtale` with its functors read on
the small étale ringed topos rather than on the small étale ringed site. -/
def pushforwardModulesIsoIdSmallEtaleTopos (X : AlgebraicSpaces B S hS) :=
  RingedToposHom.pushforwardModulesIsoId (smallEtaleRingedToposHom B S hS (𝟙 X))
    (smallEtaleDirectImageIdIso B S hS X).symm
    ((forgetRing_map_fSharp B S hS (𝟙 X)).trans (structureSharpSet_id B S hS X))

/-- **`a_* ⋙ c_* ≅ 𝟭` on modules for `a ≫ c = 𝟙`**, in the spelling of the morphisms of small étale
ringed topoi: the comparison of Stacks 03LU followed by the unit law. -/
def pushforwardModulesRetractionIso {X₀ X₁ : AlgebraicSpaces B S hS} (a : X₀ ⟶ X₁) (c : X₁ ⟶ X₀)
    (hac : a ≫ c = 𝟙 X₀) :
    (smallEtaleRingedToposHom B S hS a).pushforwardModules ⋙
      (smallEtaleRingedToposHom B S hS c).pushforwardModules ≅ 𝟭 _ :=
  pushforwardModulesCompAt B S hS a c ≪≫
    eqToIso (congrArg (fun k : X₀ ⟶ X₀ => (smallEtaleRingedToposHom B S hS k).pushforwardModules)
      hac) ≪≫
    (pushforwardModulesIsoIdSmallEtaleTopos X₀).symm

/-- **`i_* ⋙ ρ_* ≅ 𝟭` on modules**, in the spelling of the morphisms of small étale ringed topoi:
the comparison of the direct images of modules of a composite followed by the unit law for the
identity. -/
def retractionPushforwardModulesIso :
    (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).pushforwardModules ⋙
      (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap r)).pushforwardModules ≅
      𝟭 _ :=
  pushforwardModulesRetractionIso _ _ (relativeMap_comp_relativeMap_retraction h r hr)


section Coherence

variable {X₀ X₁ X₂ : AlgebraicSpaces B S hS}

/-- `y_*x_*M ≅ M` for `x ≫ y = 𝟙` (the comparison of Stacks 03LU and the unit law), in the
spelling of the morphisms of small étale ringed topoi. -/
def pushforwardModulesRetractionIsoApp (x : X₀ ⟶ X₁) (y : X₁ ⟶ X₀) (hxy : x ≫ y = 𝟙 X₀)
    (M : Modules.{u, u} B S hS X₀.1 X₀.2) :
    (smallEtaleRingedToposHom B S hS y).pushforwardModules.obj
        ((smallEtaleRingedToposHom B S hS x).pushforwardModules.obj M) ≅ M :=
  (pushforwardModulesCompAt B S hS x y).app M ≪≫
    eqToIso (congrArg (fun k : X₀ ⟶ X₀ =>
      (smallEtaleRingedToposHom B S hS k).pushforwardModules.obj M) hxy) ≪≫
    ((pushforwardModulesIsoIdSmallEtale B S hS X₀).app M).symm

/-- **The comparisons `c_* k_* M ≅ M` and `c₂_* a_* M ≅ M` along `k_* ≅ b_* a_*` and
`c_* b_* ≅ c₂_*` agree** as soon as the four comparisons satisfy the associativity coherence at
`M`; a statement about isomorphisms of objects only. -/
theorem retractionIso_inv_comp_of_assoc {C D E : Type*} [Category C] [Category D] [Category E]
    (Pa : C ⥤ D) (Pb : D ⥤ E) (Pc : E ⥤ C) {M : C} {Y : E} {Z : C}
    (μab : Pb.obj (Pa.obj M) ≅ Y) (μbc : Pc.obj (Pb.obj (Pa.obj M)) ≅ Z)
    (μkc : Pc.obj Y ≅ M) (μac : Z ≅ M)
    (hass : Pc.map μab.hom ≫ μkc.hom = μbc.hom ≫ μac.hom) :
    μkc.inv ≫ Pc.map μab.inv ≫ μbc.hom = μac.inv := by
  rw [← cancel_mono μac.hom, Category.assoc, Category.assoc, ← hass, ← Category.assoc
    (Pc.map μab.inv), ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id, Iso.inv_hom_id]

/-- The associativity coherence of Stacks 03LU, for `a ≫ b = k` and `b ≫ c = c₂`. -/
theorem pushforwardModulesCompAt_assoc_of_eq (a : X₀ ⟶ X₂) (b : X₂ ⟶ X₁) (c : X₁ ⟶ X₀)
    {k : X₀ ⟶ X₁} {c₂ : X₂ ⟶ X₀} (e₁ : a ≫ b = k) (e₂ : b ≫ c = c₂)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)) :
    (smallEtaleRingedToposHom B S hS c).pushforwardModules.map
          ((pushforwardModulesCompAt B S hS a b).hom.app M ≫
            eqToHom (congrArg (fun x : X₀ ⟶ X₁ =>
              (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj M) e₁)) ≫
        (pushforwardModulesCompAt B S hS k c).hom.app M =
      (pushforwardModulesCompAt B S hS b c).hom.app
          ((smallEtaleRingedToposHom B S hS a).pushforwardModules.obj M) ≫
        eqToHom (congrArg (fun x : X₂ ⟶ X₀ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj
            ((smallEtaleRingedToposHom B S hS a).pushforwardModules.obj M)) e₂) ≫
        (pushforwardModulesCompAt B S hS a c₂).hom.app M ≫
        eqToHom (congrArg (fun x : X₀ ⟶ X₀ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj M)
          (by rw [← e₁, ← e₂, Category.assoc])) := by
  subst e₁ e₂
  simpa using pushforwardModulesCompAt_assoc B S hS a b c M

/-- **The comparisons `c_* k_* M ⟶ (𝟙)_* M` and `c₂_* a_* M ⟶ (𝟙)_* M` along a morphism of
thickenings are compatible** (the associativity coherence of Stacks 03LU): for `a ≫ b = k`,
`b ≫ c = c₂`, `k ≫ c = 𝟙` and `a ≫ c₂ = 𝟙`. -/
theorem pushforwardModulesCompAt_retraction_coherence (a : X₀ ⟶ X₂) (b : X₂ ⟶ X₁)
    (c : X₁ ⟶ X₀) {k : X₀ ⟶ X₁} {c₂ : X₂ ⟶ X₀} (e₁ : a ≫ b = k) (e₂ : b ≫ c = c₂)
    (h₁ : k ≫ c = 𝟙 X₀) (h₂ : a ≫ c₂ = 𝟙 X₀)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)) :
    (smallEtaleRingedToposHom B S hS c).pushforwardModules.map
        ((pushforwardModulesCompAt B S hS a b).hom.app M ≫ eqToHom (congrArg (fun x : X₀ ⟶ X₁ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj M) e₁)) ≫
      (pushforwardModulesCompAt B S hS k c).hom.app M ≫ eqToHom (congrArg (fun x : X₀ ⟶ X₀ =>
        (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj M) h₁) =
    (pushforwardModulesCompAt B S hS b c).hom.app
        ((smallEtaleRingedToposHom B S hS a).pushforwardModules.obj M) ≫
      eqToHom (congrArg (fun x : X₂ ⟶ X₀ =>
        (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj
          ((smallEtaleRingedToposHom B S hS a).pushforwardModules.obj M)) e₂) ≫
      (pushforwardModulesCompAt B S hS a c₂).hom.app M ≫ eqToHom (congrArg (fun x : X₀ ⟶ X₀ =>
        (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj M) h₂) := by
  rw [← Category.assoc, pushforwardModulesCompAt_assoc_of_eq a b c e₁ e₂ M]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (eqToHom_trans _ _))))))

end Coherence

end AlgebraicGeometry.Space.CoherentSituation

end
