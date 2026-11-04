module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismDerivationTangentLinear
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftBaseNaturality
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsRimSchlessingerUnconditional

/-!
# The arrow `Der_k(𝒪_Y, f_*𝒪_X) → T Def_{X → Y}` of Stacks 0E3V as a `k`-linear map

The source's proof interprets a derivation `D` as a morphism `f_ε : X' → Y'` deforming `f`, the
translate `D ⬝ f'` of the trivial lift, and sends it to the class of `(f_ε : X' → Y')` in
`T Def_{X → Y}`. This file proves that this arrow is `k`-linear and bundles it.

## Main definitions

* `Deformation.Examples.schemeMorphismTrivialPushforward`,
  `Deformation.Examples.schemeMorphismTrivialTransport`: the pushforward of lifts and the
  transport of the acting group of [Stacks Project, Tag 0CK2] between the trivial deformations,
  along a map of coordinate modules.
* `Deformation.Examples.schemeMorphismDerivationTangentLinearMap`: **the arrow
  `Der_k(𝒪_Y, f_*𝒪_X) → T Def_{X → Y}` as a `k`-linear map**, at the canonical data.

## Main results

* `Deformation.Examples.schemeMorphismTrivialTransport_comp`,
  `Deformation.Examples.schemeMorphismTrivialTransport_id`,
  `Deformation.Examples.schemeMorphismTrivialTransport_smul`: functoriality of the transport, and
  its value along a scaling of the coordinate.
* `Deformation.Examples.liftClass_trivialVAdd_add_of_transport_zero`: additivity, through the
  doubled coordinate module `k ⊕ k`.
* `Deformation.Examples.liftClass_trivialVAdd_smul_of_transport_smul`: homogeneity.

## References

* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

attribute [local instance] deformationSpecialMap_isClosedImmersion
  residueSpecMap_isClosedImmersion

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

section Transport

/-- The square-zero condition for the trivial deformation of `X` over `k[N]`. -/
theorem schemeMorphismSourceTrivialAt_maximalIdeal_pow_two (N : FGModuleCat.{u} k) :
    IsLocalRing.maximalIdeal (schemeMorphismSourceTrivialAt f pX pY hf N).base ^ 2 = ⊥ := by
  rw [schemeMorphismSourceTrivialAt_base]
  exact maximalIdeal_squareZeroExtensionArtinian_pow_two N

/-- The pushforward of lifts between the trivial deformations along a map of coordinate
modules. -/
abbrev schemeMorphismTrivialPushforward {M N : FGModuleCat.{u} k} (g : M ⟶ N) :
    globalLiftsOverBase f (schemeMorphismSourceTrivialAt f pX pY hf M)
        (schemeMorphismTargetTrivialAt f pX pY hf M)
        (eqToHom ((schemeMorphismTargetTrivialAt_base f pX pY hf M).trans
          (schemeMorphismSourceTrivialAt_base f pX pY hf M).symm)) →
      globalLiftsOverBase f (schemeMorphismSourceTrivialAt f pX pY hf N)
        (schemeMorphismTargetTrivialAt f pX pY hf N)
        (eqToHom ((schemeMorphismTargetTrivialAt_base f pX pY hf N).trans
          (schemeMorphismSourceTrivialAt_base f pX pY hf N).symm)) :=
  globalLiftsOverBasePushforward f pX pY hf (schemeMorphismSourceTrivialMap f pX pY hf g)
    (schemeMorphismTargetTrivialMap f pX pY hf g) (schemeMorphismTrivialMap_base_comm f pX pY hf g)

/-- The transport of the acting group of Tag 0CK2 between the trivial deformations along a map of
coordinate modules. -/
abbrev schemeMorphismTrivialTransport {M N : FGModuleCat.{u} k} (g : M ⟶ N) :
    (Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
        Stacks.Thickenings.conormalModules (schemeMorphismSourceTrivialAt f pX pY hf M).specialMap)
      →+ (Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
        Stacks.Thickenings.conormalModules (schemeMorphismSourceTrivialAt f pX pY hf
            N).specialMap) :=
  liftActionTransport f pX pY hf (schemeMorphismSourceTrivialMap f pX pY hf g)
    (schemeMorphismTargetTrivialMap f pX pY hf g) (schemeMorphismTrivialMap_base_comm f pX pY hf g)
    (schemeMorphismSourceTrivialAt_maximalIdeal_pow_two f pX pY hf M)
    (schemeMorphismSourceTrivialAt_maximalIdeal_pow_two f pX pY hf N)
    (schemeMorphismTrivialLiftAt f pX pY hf M)

/-- The pushforward of the trivial lift is the trivial lift. -/
theorem schemeMorphismTrivialPushforward_trivialLiftAt {M N : FGModuleCat.{u} k} (g : M ⟶ N) :
    schemeMorphismTrivialPushforward f pX pY hf g (schemeMorphismTrivialLiftAt f pX pY hf M) =
      schemeMorphismTrivialLiftAt f pX pY hf N :=
  (eq_globalLiftsOverBasePushforward f pX pY hf _ _ _ _ _
    (schemeMorphismTrivialLiftAt_comp_map f pX pY hf N g)).symm

/-- **Naturality of the action at the trivial lifts.** -/
theorem schemeMorphismTrivialPushforward_vadd {M N : FGModuleCat.{u} k} (g : M ⟶ N)
    (θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules (schemeMorphismSourceTrivialAt f pX pY hf M).specialMap) :
    schemeMorphismTrivialPushforward f pX pY hf g
        (globalLiftsOverBaseVAdd f pX pY hf
          (schemeMorphismSourceTrivialAt_maximalIdeal_pow_two f pX pY hf M)
          (schemeMorphismTrivialLiftAt f pX pY hf M) θ (schemeMorphismTrivialLiftAt f pX pY hf M)) =
      globalLiftsOverBaseVAdd f pX pY hf
          (schemeMorphismSourceTrivialAt_maximalIdeal_pow_two f pX pY hf N)
          (schemeMorphismTrivialLiftAt f pX pY hf N) (schemeMorphismTrivialTransport f pX pY hf g θ)
          (schemeMorphismTrivialLiftAt f pX pY hf N) :=
  (globalLiftsOverBasePushforward_vadd f pX pY hf _ _ _ _ _
    (schemeMorphismTrivialLiftAt f pX pY hf M) θ _ _ (schemeMorphismTrivialLiftAt f pX pY hf
        N)).trans
    (congrArg _ (schemeMorphismTrivialPushforward_trivialLiftAt f pX pY hf g))

/-- The class of the pushforward of a lift is the image of its class. -/
theorem liftClass_schemeMorphismTrivialPushforward
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    {M N : FGModuleCat.{u} k} (g : M ⟶ N)
    (ℓ : globalLiftsOverBase f (schemeMorphismSourceTrivialAt f pX pY hf M)
        (schemeMorphismTargetTrivialAt f pX pY hf M)
        (eqToHom ((schemeMorphismTargetTrivialAt_base f pX pY hf M).trans
          (schemeMorphismSourceTrivialAt_base f pX pY hf M).symm))) :
    liftClass f pX pY hf hM N (schemeMorphismTargetTrivialAt_base f pX pY hf N)
        (schemeMorphismTrivialPushforward f pX pY hf g ℓ) =
      tangentModuleMapAt.{u, u, u} (BasedCategory.ofFunctor
          (schemeMorphismDeformationCategoryProjection f pX pY hf)) hM g
        (liftClass f pX pY hf hM M (schemeMorphismTargetTrivialAt_base f pX pY hf M) ℓ) :=
  liftClass_eq_tangentModuleMapAt_of_trivialMap f pX pY hf hM g ℓ _
    (globalLiftsOverBasePushforward_fac f pX pY hf _ _ _ ℓ)

/-- The transport depends only on the map of coordinate modules through its two arrows. -/
theorem liftActionTransport_congr
    {P₁ P₂ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q₁ Q₂ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {e₁ : Q₁.base ⟶ P₁.base} {e₂ : Q₂.base ⟶ P₂.base}
    {φ φ' : P₁ ⟶ P₂} {ψ ψ' : Q₁ ⟶ Q₂} (hφ : φ = φ') (hψ : ψ = ψ')
    (hb : ψ.base ≫ e₂ = e₁ ≫ φ.base) (hb' : ψ'.base ≫ e₂ = e₁ ≫ φ'.base)
    (hm₁ : IsLocalRing.maximalIdeal P₁.base ^ 2 = ⊥)
    (hm₂ : IsLocalRing.maximalIdeal P₂.base ^ 2 = ⊥) (ℓ₁ : globalLiftsOverBase f P₁ Q₁ e₁) :
    liftActionTransport f pX pY hf φ ψ hb hm₁ hm₂ ℓ₁ =
      liftActionTransport f pX pY hf φ' ψ' hb' hm₁ hm₂ ℓ₁ := by
  subst hφ hψ
  rfl

/-- **The transport along a composite of coordinate maps is the composite of the transports.** -/
theorem schemeMorphismTrivialTransport_comp {M N O : FGModuleCat.{u} k} (g : M ⟶ N) (h : N ⟶ O)
    (θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules (schemeMorphismSourceTrivialAt f pX pY hf M).specialMap) :
    schemeMorphismTrivialTransport f pX pY hf (g ≫ h) θ =
      schemeMorphismTrivialTransport f pX pY hf h (schemeMorphismTrivialTransport f pX pY hf g
          θ) := by
  have ⟨hX, hY⟩ : schemeMorphismSourceTrivialMap f pX pY hf (g ≫ h) =
      schemeMorphismSourceTrivialMap f pX pY hf g ≫ schemeMorphismSourceTrivialMap f pX pY hf h ∧
      schemeMorphismTargetTrivialMap f pX pY hf (g ≫ h) =
      schemeMorphismTargetTrivialMap f pX pY hf g ≫
        schemeMorphismTargetTrivialMap f pX pY hf h := by
    constructor <;>
      (dsimp only [schemeMorphismSourceTrivialMap, schemeMorphismTargetTrivialMap]
       rw [squareZeroCrossUnderMap_comp, ChosenPushforwardsAt.map_comp])
  have hb'' := hX ▸ hY ▸ schemeMorphismTrivialMap_base_comm f pX pY hf (g ≫ h)
  dsimp only [schemeMorphismTrivialTransport]
  rw [liftActionTransport_congr f pX pY hf hX hY _ hb'', liftActionTransport_comp]
  exact DFunLike.congr_fun (liftActionTransport_eq f pX pY hf
    (schemeMorphismSourceTrivialMap f pX pY hf h) (schemeMorphismTargetTrivialMap f pX pY hf h)
    (schemeMorphismTrivialMap_base_comm f pX pY hf h)
    (schemeMorphismSourceTrivialAt_maximalIdeal_pow_two f pX pY hf N)
    (schemeMorphismSourceTrivialAt_maximalIdeal_pow_two f pX pY hf O) _
    (schemeMorphismTrivialLiftAt f pX pY hf N)) _

/-- **The transport along the identity coordinate map is the identity.** -/
theorem schemeMorphismTrivialTransport_id (M : FGModuleCat.{u} k)
    (θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶
      Stacks.Thickenings.conormalModules (schemeMorphismSourceTrivialAt f pX pY hf M).specialMap) :
    schemeMorphismTrivialTransport f pX pY hf (𝟙 M) θ = θ := by
  have ⟨hX, hY⟩ : schemeMorphismSourceTrivialMap f pX pY hf (𝟙 M) = 𝟙 _ ∧
      schemeMorphismTargetTrivialMap f pX pY hf (𝟙 M) = 𝟙 _ := by
    constructor <;>
      (dsimp only [schemeMorphismSourceTrivialMap, schemeMorphismTargetTrivialMap]
       rw [squareZeroCrossUnderMap_id, ChosenPushforwardsAt.map_id])
  have hb' := hX ▸ hY ▸ schemeMorphismTrivialMap_base_comm f pX pY hf (𝟙 M)
  dsimp only [schemeMorphismTrivialTransport]
  rw [liftActionTransport_congr f pX pY hf hX hY _ hb', liftActionTransport_id]

end Transport

/-! ### Additivity -/

section Additivity

/-- The rank-one coordinate module, at which the tangent space is read. -/
abbrev rankOneCoordinate : FGModuleCat.{u} k := FGModuleCat.of k (ULift.{u} k)

/-- The rank-two coordinate module `k ⊕ k`. -/
abbrev rankTwoCoordinate : FGModuleCat.{u} k := FGModuleCat.of k (ULift.{u} k × ULift.{u} k)

/-- The first inclusion `k → k ⊕ k`. -/
abbrev rankTwoInl : rankOneCoordinate (k := k) ⟶ rankTwoCoordinate (k := k) :=
  FGModuleCat.ofHom (LinearMap.inl k (ULift.{u} k) (ULift.{u} k))

/-- The second inclusion `k → k ⊕ k`. -/
abbrev rankTwoInr : rankOneCoordinate (k := k) ⟶ rankTwoCoordinate (k := k) :=
  FGModuleCat.ofHom (LinearMap.inr k (ULift.{u} k) (ULift.{u} k))

/-- The first projection `k ⊕ k → k`. -/
abbrev rankTwoFst : rankTwoCoordinate (k := k) ⟶ rankOneCoordinate (k := k) :=
  FGModuleCat.ofHom (LinearMap.fst k (ULift.{u} k) (ULift.{u} k))

/-- The second projection `k ⊕ k → k`. -/
abbrev rankTwoSnd : rankTwoCoordinate (k := k) ⟶ rankOneCoordinate (k := k) :=
  FGModuleCat.ofHom (LinearMap.snd k (ULift.{u} k) (ULift.{u} k))

/-- **Additivity of the class of the translate of the trivial lift**, granted that the transport
along the zero coordinate map vanishes. The argument is the doubled coordinate module of
`Deformation.map_add_of_doubling`: the pair `(θ, η)` is transported to `k ⊕ k`, the translate of
the trivial lift there is pushed forward along the two projections and their sum, and the class
of a pushforward is the image of the class
(`Deformation.Examples.liftClass_schemeMorphismTrivialPushforward`). -/
theorem liftClass_trivialVAdd_add_of_transport_zero
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (h0 : ∀ θ, schemeMorphismTrivialTransport f pX pY hf
      (0 : rankOneCoordinate (k := k) ⟶ rankOneCoordinate (k := k)) θ = 0)
    (θ η : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶ Stacks.Thickenings.conormalModules
      (schemeMorphismSourceTrivialAt f pX pY hf (rankOneCoordinate (k := k))).specialMap) :
    liftClass f pX pY hf hM _ (schemeMorphismTargetTrivialAt_base f pX pY hf _)
        (globalLiftsOverBaseVAdd f pX pY hf
          (schemeMorphismSourceTrivialAt_maximalIdeal_pow_two f pX pY hf _)
          (schemeMorphismTrivialLiftAt f pX pY hf _) (θ + η)
          (schemeMorphismTrivialLiftAt f pX pY hf _)) =
      liftClass f pX pY hf hM _ (schemeMorphismTargetTrivialAt_base f pX pY hf _)
          (globalLiftsOverBaseVAdd f pX pY hf
            (schemeMorphismSourceTrivialAt_maximalIdeal_pow_two f pX pY hf _)
            (schemeMorphismTrivialLiftAt f pX pY hf _) θ
            (schemeMorphismTrivialLiftAt f pX pY hf _)) +
        liftClass f pX pY hf hM _ (schemeMorphismTargetTrivialAt_base f pX pY hf _)
          (globalLiftsOverBaseVAdd f pX pY hf
            (schemeMorphismSourceTrivialAt_maximalIdeal_pow_two f pX pY hf _)
            (schemeMorphismTrivialLiftAt f pX pY hf _) η
            (schemeMorphismTrivialLiftAt f pX pY hf _)) := by
  have e₁₁ : rankTwoInl (k := k) ≫ rankTwoFst = 𝟙 _ := by apply FGModuleCat.hom_ext; rfl
  have e₂₁ : rankTwoInr (k := k) ≫ rankTwoFst = 0 := by apply FGModuleCat.hom_ext; rfl
  have e₁₂ : rankTwoInl (k := k) ≫ rankTwoSnd = 0 := by apply FGModuleCat.hom_ext; rfl
  have e₂₂ : rankTwoInr (k := k) ≫ rankTwoSnd = 𝟙 _ := by apply FGModuleCat.hom_ext; rfl
  refine Deformation.map_add_of_doubling
    (globalLiftsOverBaseVAdd f pX pY hf
      (schemeMorphismSourceTrivialAt_maximalIdeal_pow_two f pX pY hf _)
      (schemeMorphismTrivialLiftAt f pX pY hf _))
    (globalLiftsOverBaseVAdd f pX pY hf
      (schemeMorphismSourceTrivialAt_maximalIdeal_pow_two f pX pY hf rankTwoCoordinate)
      (schemeMorphismTrivialLiftAt f pX pY hf rankTwoCoordinate))
    (schemeMorphismTrivialLiftAt f pX pY hf _) (schemeMorphismTrivialLiftAt f pX pY hf _)
    (liftClass f pX pY hf hM _ (schemeMorphismTargetTrivialAt_base f pX pY hf _))
    (liftClass f pX pY hf hM _ (schemeMorphismTargetTrivialAt_base f pX pY hf _))
    (schemeMorphismTrivialPushforward f pX pY hf rankTwoFst)
    (schemeMorphismTrivialPushforward f pX pY hf rankTwoSnd)
    (schemeMorphismTrivialPushforward f pX pY hf (rankTwoFst + rankTwoSnd))
    (schemeMorphismTrivialTransport f pX pY hf rankTwoFst)
    (schemeMorphismTrivialTransport f pX pY hf rankTwoSnd)
    (schemeMorphismTrivialTransport f pX pY hf (rankTwoFst + rankTwoSnd))
    (schemeMorphismTrivialTransport f pX pY hf rankTwoInl)
    (schemeMorphismTrivialTransport f pX pY hf rankTwoInr)
    (tangentModuleMapAt.{u, u, u} _ hM rankTwoFst) (tangentModuleMapAt.{u, u, u} _ hM rankTwoSnd)
    (schemeMorphismTrivialPushforward_vadd f pX pY hf _)
    (schemeMorphismTrivialPushforward_vadd f pX pY hf _)
    (schemeMorphismTrivialPushforward_vadd f pX pY hf _)
    (liftClass_schemeMorphismTrivialPushforward f pX pY hf hM _)
    (liftClass_schemeMorphismTrivialPushforward f pX pY hf hM _)
    (fun x => (liftClass_schemeMorphismTrivialPushforward f pX pY hf hM _ x).trans
      (tangentModuleMapAt_add.{u, u, u} _ hM _ _ _))
    ?_ ?_ ?_ ?_ ?_ ?_ θ η
  all_goals
    intro θ
    simp [← schemeMorphismTrivialTransport_comp, Preadditive.comp_add, e₁₁, e₂₁, e₁₂, e₂₂, h0,
      schemeMorphismTrivialTransport_id]

end Additivity

/-! ### Homogeneity -/

section Homogeneity

/-- **Homogeneity of the class of the translate of the trivial lift**, granted that the transport
along the scaling `c • 𝟙` of the rank-one coordinate module is multiplication by `c`. The
translate by `c • θ` is the pushforward along `k[c • 𝟙]` of the translate by `θ`, and the class
of that pushforward is `c` times the class (`Deformation.tangentModuleMapAt_smul`). -/
theorem liftClass_trivialVAdd_smul_of_transport_smul
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (smul : k → (Stacks.Smooth.pullbackCotangentSheaf pY f ⟶ Stacks.Thickenings.conormalModules
      (schemeMorphismSourceTrivialAt f pX pY hf (rankOneCoordinate (k := k))).specialMap) →
      (Stacks.Smooth.pullbackCotangentSheaf pY f ⟶ Stacks.Thickenings.conormalModules
      (schemeMorphismSourceTrivialAt f pX pY hf (rankOneCoordinate (k := k))).specialMap))
    (hsmul : ∀ (c : k) θ, schemeMorphismTrivialTransport f pX pY hf
      (c • 𝟙 (rankOneCoordinate (k := k))) θ = smul c θ)
    (c : k)
    (θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶ Stacks.Thickenings.conormalModules
      (schemeMorphismSourceTrivialAt f pX pY hf (rankOneCoordinate (k := k))).specialMap) :
    liftClass f pX pY hf hM _ (schemeMorphismTargetTrivialAt_base f pX pY hf _)
        (globalLiftsOverBaseVAdd f pX pY hf
            (schemeMorphismSourceTrivialAt_maximalIdeal_pow_two f pX pY hf _)
            (schemeMorphismTrivialLiftAt f pX pY hf _) (smul c θ)
            (schemeMorphismTrivialLiftAt f pX pY hf _)) =
      c • liftClass f pX pY hf hM _ (schemeMorphismTargetTrivialAt_base f pX pY hf _)
        (globalLiftsOverBaseVAdd f pX pY hf
            (schemeMorphismSourceTrivialAt_maximalIdeal_pow_two f pX pY hf _)
            (schemeMorphismTrivialLiftAt f pX pY hf _) θ
            (schemeMorphismTrivialLiftAt f pX pY hf _)) := by
  rw [← hsmul, ← schemeMorphismTrivialPushforward_vadd, liftClass_schemeMorphismTrivialPushforward]
  exact tangentModuleMapAt_smul.{u, u, u} _ hM c _

end Homogeneity

/-! ### The arrow `Der_k(𝒪_Y, f_*𝒪_X) → T Def_{X → Y}` as a `k`-linear map -/

section LinearMap

/-- The transport along the scaling `c • 𝟙` of the rank-one coordinate module is multiplication
by `c`, for the `k`-linear structure of
`Deformation.Examples.schemeMorphismDerivationsLinearEquivHom`.
This is `Deformation.Examples.liftActionTransport_crossScaling` at the trivial deformations. -/
theorem schemeMorphismTrivialTransport_smul (c : k)
    (θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶ Stacks.Thickenings.conormalModules
      (schemeMorphismSourceTrivialAt f pX pY hf (rankOneCoordinate (k := k))).specialMap) :
    letI : Linear k X.Modules := modulesLinear k (Over.mk (f ≫ pY))
    schemeMorphismTrivialTransport f pX pY hf (c • 𝟙 (rankOneCoordinate (k := k))) θ = c • θ :=
  liftActionTransport_crossScaling f pX pY hf (schemeMorphismSourcePushforwards f pX pY
      hf) (schemeMorphismTargetPushforwards f pX pY hf) c
          (firstOrderPushforwardCross_maximalIdeal_pow_two (schemeMorphismSourcePushforwards f pX pY
          hf)) (schemeMorphismTrivialLift f pX pY hf) θ

/-- The transport along the zero coordinate map vanishes. -/
theorem schemeMorphismTrivialTransport_zero
    (θ : Stacks.Smooth.pullbackCotangentSheaf pY f ⟶ Stacks.Thickenings.conormalModules
      (schemeMorphismSourceTrivialAt f pX pY hf (rankOneCoordinate (k := k))).specialMap) :
    schemeMorphismTrivialTransport f pX pY hf
      (0 : rankOneCoordinate (k := k) ⟶ rankOneCoordinate (k := k)) θ = 0 := by
  let : Linear k X.Modules := modulesLinear k (Over.mk (f ≫ pY))
  rw [← zero_smul k (𝟙 (rankOneCoordinate (k := k))), schemeMorphismTrivialTransport_smul,
    zero_smul]

/-- The arrow `Der_k(𝒪_Y, f_*𝒪_X) → T Def_{X → Y}` at the canonical data, as a bare function:
`Deformation.Examples.schemeMorphismDerivationTangentMap` at the trivial lift. -/
abbrev schemeMorphismDerivationTangentFun :
    schemeMorphismDerivations f pY →
      ↥(tangentModuleAt.{u, u, u}
        (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY
            hf)) (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf)
        (FGModuleCat.of k (ULift.{u} k))) :=
  schemeMorphismDerivationTangentMap f pX pY hf
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf) (FGModuleCat.of
      k (ULift.{u} k))
    (firstOrderPushforwardCross_base (schemeMorphismTargetPushforwards f pX pY hf))
    (globalLiftsOverBaseDerivationVAdd f pX pY hf (firstOrderPushforwardCrossConormalIsoUnit
        (schemeMorphismSourcePushforwards f pX pY
        hf)) (firstOrderPushforwardCross_maximalIdeal_pow_two
            (schemeMorphismSourcePushforwards f pX pY hf)) (schemeMorphismTrivialLift f pX pY hf))
            (schemeMorphismTrivialLift f pX pY hf)

/-- **Stacks 0E3V, the arrow `Der_k(𝒪_Y, f_*𝒪_X) → T Def_{X → Y}` as a `k`-linear map.** A
derivation `D` is sent to the class of the translate `D ⬝ f'` of the trivial lift. -/
def schemeMorphismDerivationTangentLinearMap :
    letI := schemeMorphismDerivationsModule f pY
      (SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    schemeMorphismDerivations f pY →ₗ[k]
      ↥(tangentModuleAt.{u, u, u}
        (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY
            hf)) (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf)
        (FGModuleCat.of k (ULift.{u} k))) :=
  letI := schemeMorphismDerivationsModule f pY
    (SheafOfModules.unit (structureSheafRing X.toRingedSpace))
  { toFun := schemeMorphismDerivationTangentFun f pX pY hf
    map_add' := fun D D' => by
      change liftClass f pX pY hf _ _ _ (globalLiftsOverBaseVAdd f pX pY hf _ _
          (schemeMorphismDerivationsEquivHom f pY _ (firstOrderPushforwardCrossConormalIsoUnit
              (schemeMorphismSourcePushforwards f pX pY hf)) (D + D')) _) = _
      rw [map_add]
      exact liftClass_trivialVAdd_add_of_transport_zero f pX pY hf
          (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf)
        (schemeMorphismTrivialTransport_zero f pX pY hf) _ _
    map_smul' := fun c D => by
      let : Linear k X.Modules := modulesLinear k (Over.mk (f ≫ pY))
      change liftClass f pX pY hf _ _ _ (globalLiftsOverBaseVAdd f pX pY hf _ _
          (schemeMorphismDerivationsEquivHom f pY _ (firstOrderPushforwardCrossConormalIsoUnit
              (schemeMorphismSourcePushforwards f pX pY hf)) (c • D)) _) = _
      have hD : schemeMorphismDerivationsEquivHom f pY _ (firstOrderPushforwardCrossConormalIsoUnit
          (schemeMorphismSourcePushforwards f pX pY hf)) (c • D) =
          c • schemeMorphismDerivationsEquivHom f pY _ (firstOrderPushforwardCrossConormalIsoUnit
              (schemeMorphismSourcePushforwards f pX pY hf)) D :=
        (schemeMorphismDerivationsLinearEquivHom f pY _ (firstOrderPushforwardCrossConormalIsoUnit
            (schemeMorphismSourcePushforwards f pX pY hf))).map_smul c D
      rw [hD]
      exact liftClass_trivialVAdd_smul_of_transport_smul f pX pY hf
          (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf) (fun c θ =>
          c • θ)
        (schemeMorphismTrivialTransport_smul f pX pY hf) c _ }

/-- The `k`-linear map `schemeMorphismDerivationTangentLinearMap` sends a derivation `D` to
`schemeMorphismDerivationTangentFun f pX pY hf D`. -/
@[simp]
theorem schemeMorphismDerivationTangentLinearMap_apply (D : schemeMorphismDerivations f pY) :
    letI := schemeMorphismDerivationsModule f pY
      (SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    schemeMorphismDerivationTangentLinearMap f pX pY hf D =
      schemeMorphismDerivationTangentFun f pX pY hf D := rfl

end LinearMap

end Deformation.Examples
