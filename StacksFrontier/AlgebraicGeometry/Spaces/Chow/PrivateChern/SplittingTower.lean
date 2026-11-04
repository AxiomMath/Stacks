module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowLocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackIdentity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria

/-!
# Towers of morphisms with injective flat pullback on Chow groups

In Situation 0EDT let `π : P → X` be a morphism of good algebraic spaces over `B` which is flat
of relative dimension `d`. The splitting principle (Stacks 0ESC) asks for such a `π` for which
the flat pullback `π_Y^* : CH_k(Y) → CH_{k+d}(Y ×_X P)` is injective for every morphism
`f : Y → X` of good algebraic spaces over `B`, and its proof builds `π` as a tower of projective
bundles. This file records the formal part of that argument: the property is enjoyed by the
identity and is stable under composition.

Injectivity of `π_Y^*` on Chow groups is the statement that a `k`-cycle on `Y` whose flat
pullback is rationally equivalent to zero is itself rationally equivalent to zero; this is the
form used here,
`AlgebraicGeometry.Space.PrivateChern.FlatPullbackReflectsRationalEquivalence`, since it is
stated on cycles and does not need the flat pullback to be descended to Chow groups first.

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.FlatPullbackReflectsRationalEquivalence`: the flat
  pullback along a flat morphism `q : Q → Y` of relative dimension `d` is injective on Chow
  groups.
* `AlgebraicGeometry.Space.PrivateChern.HasInjectiveChowPullbacks`: along every morphism
  `f : Y → X` of good algebraic spaces over `B` and every cartesian square with good corner
  `Q = Y ×_X P`, the flat pullback `CH_k(Y) → CH_{k+d}(Q)` is injective. This is clause (1) of
  Stacks 0ESC.
* `AlgebraicGeometry.Space.PrivateChern.HasInjectiveChowBaseChange`: the same for *some*
  cartesian square along every `f`; it is the form in which towers are assembled.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.flatPullbackMap_id`: the flat pullback along the
  identity is the identity.
* `AlgebraicGeometry.Space.PrivateChern.flatPullbackMap_eq_cycleGroupRestrict_of_isIso` and
  `AlgebraicGeometry.Space.PrivateChern.isRationallyEquivalentToZero_flatPullbackMap_of_isIso`:
  the flat pullback along an isomorphism is the restriction of cycles, so it preserves
  rational equivalence.
* `AlgebraicGeometry.Space.PrivateChern.FlatPullbackReflectsRationalEquivalence.of_iso`:
  injectivity does not depend on the choice of fibre product.
* `AlgebraicGeometry.Space.PrivateChern.hasInjectiveChowBaseChange_id` and
  `AlgebraicGeometry.Space.PrivateChern.HasInjectiveChowBaseChange.comp`: the identity has the
  property, and a composite `P₂ → P₁ → X` of two morphisms with the property has it at the sum
  of the relative dimensions.
* `AlgebraicGeometry.Space.PrivateChern.HasInjectiveChowBaseChange.hasInjectiveChowPullbacks`:
  one fibre product along every `f` suffices.

## Implementation notes

The flat pullback of cycles is not descended to Chow groups here. Injectivity of
`q^* : CH_k(Y) → CH_{k+d}(Q)` is equivalent to the statement that a cycle whose flat pullback is
rationally equivalent to zero is rationally equivalent to zero, and that is the statement used.

## References

* [Stacks Project, Tag 0ESC](https://stacks.math.columbia.edu/tag/0ESC)
* [Stacks Project, Tag 0EPA](https://stacks.math.columbia.edu/tag/0EPA)
* [Stacks Project, Tag 0EPY](https://stacks.math.columbia.edu/tag/0EPY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] pointTopology

/-! ### The flat pullback along the identity -/

section Identity

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space) (hX : D.IsGood sX)

/-- The coefficient of the flat pullback along an étale `j` of relative dimension `0` at `T` is the
coefficient of `α` at `c`, provided `c` is the only integral closed subspace of which `T` is
a component of the inverse image. -/
private theorem flatPullbackMap_apply_eq_of_isEtale
    {V W : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sV : V ⟶ D.space) (hV : D.IsGood sV) (sW : W ⟶ D.space) (hW : D.IsGood sW) (j : V ⟶ W)
    (hjc : j ≫ sW = sV) (het : IsEtale D.site D.base D.base_mem j)
    (hflat : IsFlat D.site D.base D.base_mem j)
    (hr : HasRelativeDimension 0 D.site D.base D.base_mem j) (k n : ℤ)
    (hkn : k + ((0 : ℕ) : ℤ) = n) (α : CycleGroup D sW k)
    (T : IntegralClosedSubspace D.site D.base D.base_mem V)
    (c : IntegralClosedSubspace D.site D.base D.base_mem W)
    (hc : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem W,
      (∃ C, Z.preimageComponent D.site D.base D.base_mem j hV.1
        (D.isDecentSpace_of_isGood sV hV) hW.1 C = T) ↔ c = Z) :
    (flatPullbackMap D sV hV sW hW j hjc 0 hflat hr k n hkn α).1 T = α.1 c := by
  classical
  rw [flatPullbackMap_apply]
  have hmult : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem W,
      flatPullbackMult D sV hV sW hW j hjc 0 hflat hr Z T = if c = Z then 1 else 0 := by
    intro Z
    rw [show flatPullbackMult D sV hV sW hW j hjc 0 hflat hr Z T =
        Z.preimageComponentsCycle D sV hV sW hW j T from
      congrFun (Z.flatPullbackMult_eq_preimageComponentsCycle D sV hV sW hW het hjc) T]
    rw [IntegralClosedSubspace.preimageComponentsCycle, Set.indicator_apply]
    exact if_congr (hc Z) rfl rfl
  simp_rw [hmult, mul_ite, mul_one, mul_zero]
  rw [finsum_eq_single _ c (fun Z hZ => by simp [Ne.symm hZ])]
  simp

/-- The inverse image of an integral closed subspace `Z` along the identity has a single
irreducible component, and the integral closed subspace it carries is `Z`. -/
theorem exists_preimageComponent_id_eq_iff
    (Z W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (∃ C, Z.preimageComponent D.site D.base D.base_mem (𝟙 X) hX.1
        (D.isDecentSpace_of_isGood sX hX) hX.1 C = W) ↔ W = Z := by
  have hpre : Z.preimagePointSet D.site D.base D.base_mem (𝟙 X) =
      subspacePointSet D.site D.base D.base_mem X Z.subspace := by
    ext x
    simp only [IntegralClosedSubspace.preimagePointSet, Set.mem_preimage, pointsMap_id, id_eq]
  have hirr : IsIrreducible (Z.preimagePointSet D.site D.base D.base_mem (𝟙 X)) := by
    rw [hpre]
    exact isIrreducible_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem Z
  have : IrreducibleSpace (Z.preimagePointSet D.site D.base D.base_mem (𝟙 X)) :=
    isIrreducible_iff_irreducibleSpace.mp hirr
  have hcomp : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem (𝟙 X)) =
      {Set.univ} := irreducibleComponents_eq_singleton
  have hsupp : ∀ C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem (𝟙 X)),
      Z.preimageComponent D.site D.base D.base_mem (𝟙 X) hX.1
        (D.isDecentSpace_of_isGood sX hX) hX.1 C = Z := by
    intro C
    have hC : (C : Set (Z.preimagePointSet D.site D.base D.base_mem (𝟙 X))) = Set.univ := by
      simpa only [hcomp, Set.mem_singleton_iff] using C.2
    refine injective_integralClosedSubspaceSupport D.site D.base D.base_mem hX.1
      (TopologicalSpace.IrreducibleCloseds.ext ?_)
    show subspacePointSet D.site D.base D.base_mem X
        (Z.preimageComponent D.site D.base D.base_mem (𝟙 X) hX.1
          (D.isDecentSpace_of_isGood sX hX) hX.1 C).subspace =
      subspacePointSet D.site D.base D.base_mem X Z.subspace
    rw [IntegralClosedSubspace.subspacePointSet_preimageComponent, hC, Set.image_univ,
      Subtype.range_coe, hpre]
  constructor
  · rintro ⟨C, rfl⟩
    exact hsupp C
  · rintro rfl
    exact ⟨⟨Set.univ, hcomp ▸ Set.mem_singleton _⟩, hsupp _⟩

/-- **The flat pullback along the identity is the identity**: for a `k`-cycle `α` on a good
algebraic space `X/B`, `(id_X)^* α = α`, the identity being flat of relative dimension `0`. -/
theorem flatPullbackMap_id (hflat : IsFlat D.site D.base D.base_mem (𝟙 X))
    (hr : HasRelativeDimension 0 D.site D.base D.base_mem (𝟙 X)) (k n : ℤ)
    (hkn : k + ((0 : ℕ) : ℤ) = n) (α : CycleGroup D sX k) :
    (flatPullbackMap D sX hX sX hX (𝟙 X) (Category.id_comp sX) 0 hflat hr k n hkn α).1 =
      α.1 := by
  funext T
  exact flatPullbackMap_apply_eq_of_isEtale D sX hX sX hX (𝟙 X) (Category.id_comp sX)
    (isEtale_of_isIso D.site D.base D.base_mem (𝟙 X)) hflat hr k n hkn α _ _
    (exists_preimageComponent_id_eq_iff D sX hX · T)

end Identity

/-! ### The flat pullback along an isomorphism -/

section Iso

variable (D : BaseSpaceDimensionSituation.{u})
    {X U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sU : U ⟶ D.space) (hU : D.IsGood sU)

/-- **The flat pullback depends only on the morphism and the relative dimension.** Two flat
pullbacks along equal morphisms, at equal relative dimensions, have the same coefficients. -/
theorem flatPullbackMap_congr_of_eq {f f' : U ⟶ X} (hff' : f = f') (hfc : f ≫ sX = sU)
    (hfc' : f' ≫ sX = sU) {r r' : ℕ} (hrr' : r = r') (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (hflat' : IsFlat D.site D.base D.base_mem f')
    (hr' : HasRelativeDimension r' D.site D.base D.base_mem f') (k n : ℤ) (hkn : k + (r : ℤ) = n)
    (hkn' : k + (r' : ℤ) = n) (α : CycleGroup D sX k) :
    flatPullbackMap D sU hU sX hX f hfc r hflat hr k n hkn α =
      flatPullbackMap D sU hU sX hX f' hfc' r' hflat' hr' k n hkn' α := by
  subst hff' hrr'
  rfl

/-- Along an isomorphism `j : U → X`, an integral closed subspace `T ⊆ U` is a component of the
inverse image of an integral closed subspace `Z ⊆ X` exactly when `Z` is the closure of the image
of `T`: the map on points is a homeomorphism, so the inverse image of `|Z|` is irreducible and
closed, and it is `|T|` exactly when `|Z|` is the image of `|T|`. -/
theorem exists_preimageComponent_eq_iff_of_isIso (j : U ⟶ X) [IsIso j]
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (T : IntegralClosedSubspace D.site D.base D.base_mem U) :
    (∃ C, Z.preimageComponent D.site D.base D.base_mem j hU.1
        (D.isDecentSpace_of_isGood sU hU) hX.1 C = T) ↔
      IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
        (D.isDecentSpace_of_isGood sX hX) j T = Z := by
  let φ := pointsHomeomorphOfIso D.site D.base D.base_mem (asIso j)
  have hpre : Z.preimagePointSet D.site D.base D.base_mem j =
      φ ⁻¹' subspacePointSet D.site D.base D.base_mem X Z.subspace := rfl
  have hirr : IsIrreducible (Z.preimagePointSet D.site D.base D.base_mem j) := by
    rw [hpre, ← φ.image_symm]
    exact (isIrreducible_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem Z).image
      φ.symm φ.symm.continuous.continuousOn
  have : IrreducibleSpace (Z.preimagePointSet D.site D.base D.base_mem j) :=
    isIrreducible_iff_irreducibleSpace.mp hirr
  have hcomp : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem j) =
      {Set.univ} := irreducibleComponents_eq_singleton
  have hsupp : ∀ C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem j),
      subspacePointSet D.site D.base D.base_mem U
        (Z.preimageComponent D.site D.base D.base_mem j hU.1
          (D.isDecentSpace_of_isGood sU hU) hX.1 C).subspace =
        φ ⁻¹' subspacePointSet D.site D.base D.base_mem X Z.subspace := by
    intro C
    have hC : (C : Set (Z.preimagePointSet D.site D.base D.base_mem j)) = Set.univ := by
      simpa only [hcomp, Set.mem_singleton_iff] using C.2
    rw [IntegralClosedSubspace.subspacePointSet_preimageComponent, hC, Set.image_univ,
      Subtype.range_coe, hpre]
  have hcl : subspacePointSet D.site D.base D.base_mem X
      (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
        (D.isDecentSpace_of_isGood sX hX) j T).subspace =
      φ '' subspacePointSet D.site D.base D.base_mem U T.subspace := by
    rw [IntegralClosedSubspace.subspacePointSet_closureImage]
    exact (φ.isClosed_image.mpr
      (isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hU.1 T)).closure_eq
  constructor
  · rintro ⟨C, rfl⟩
    refine injective_integralClosedSubspaceSupport D.site D.base D.base_mem hX.1
      (TopologicalSpace.IrreducibleCloseds.ext ?_)
    show subspacePointSet D.site D.base D.base_mem X _ =
      subspacePointSet D.site D.base D.base_mem X Z.subspace
    rw [hcl, hsupp C, Set.image_preimage_eq _ φ.surjective]
  · intro h
    refine ⟨⟨Set.univ, hcomp ▸ Set.mem_singleton _⟩, ?_⟩
    refine injective_integralClosedSubspaceSupport D.site D.base D.base_mem hU.1
      (TopologicalSpace.IrreducibleCloseds.ext ?_)
    show subspacePointSet D.site D.base D.base_mem U _ =
      subspacePointSet D.site D.base D.base_mem U T.subspace
    rw [hsupp, ← h, hcl, Set.preimage_image_eq _ φ.injective]

/-- **The flat pullback along an isomorphism is the restriction of cycles**: for an isomorphism
`j : U → X` of good algebraic spaces over `B`, flat of relative dimension `0`, the coefficient of
`j^*α` at an integral closed subspace `T ⊆ U` is the coefficient of `α` at the closure of the
image of `T`, by Stacks 0EPY. -/
theorem flatPullbackMap_eq_cycleGroupRestrict_of_isIso (j : U ⟶ X) [IsIso j]
    (hjc : j ≫ sX = sU) (hflat : IsFlat D.site D.base D.base_mem j)
    (hr : HasRelativeDimension 0 D.site D.base D.base_mem j) (k : ℤ)
    (hkk : k + ((0 : ℕ) : ℤ) = k) (α : CycleGroup D sX k) :
    flatPullbackMap D sU hU sX hX j hjc 0 hflat hr k k hkk α =
      cycleGroupRestrict D sX hX sU hU (isOpenImmersion_of_isIso D.site D.base D.base_mem j) hjc
        k α := by
  refine Subtype.ext (funext fun T => ?_)
  rw [cycleGroupRestrict_apply]
  exact flatPullbackMap_apply_eq_of_isEtale D sU hU sX hX j hjc
    (isEtale_of_isIso D.site D.base D.base_mem j) hflat hr k k hkk α T _
    (exists_preimageComponent_eq_iff_of_isIso D sX hX sU hU j · T)

/-- **Flat pullback along an isomorphism preserves rational equivalence to zero.** It is the
restriction of cycles along an open immersion, which preserves rational equivalence
(Stacks 0EQ7). -/
theorem isRationallyEquivalentToZero_flatPullbackMap_of_isIso (j : U ⟶ X) [IsIso j]
    (hjc : j ≫ sX = sU) (hflat : IsFlat D.site D.base D.base_mem j)
    (hr : HasRelativeDimension 0 D.site D.base D.base_mem j) (k n : ℤ)
    (hkn : k + ((0 : ℕ) : ℤ) = n) {α : CycleGroup D sX k}
    (hα : IsRationallyEquivalentToZero.{v} D sX hX k α) :
    IsRationallyEquivalentToZero.{v} D sU hU n
      (flatPullbackMap D sU hU sX hX j hjc 0 hflat hr k n hkn α) := by
  obtain rfl : k = n := by simpa using hkn
  rw [flatPullbackMap_eq_cycleGroupRestrict_of_isIso D sX hX sU hU j hjc hflat hr k hkn α]
  exact isRationallyEquivalentToZero_cycleGroupRestrict D sX hX sU hU
    (isOpenImmersion_of_isIso D.site D.base D.base_mem j) hjc k hα

end Iso

/-! ### Injectivity of a flat pullback on Chow groups -/

section Injective

variable (D : BaseSpaceDimensionSituation.{u})

/-- **The flat pullback along `q` is injective on Chow groups.** For a morphism `q : Q → Y` of good
algebraic spaces over `B`, flat of relative dimension `d`, a `k`-cycle on `Y` whose flat pullback
`q^*α ∈ Z_{k+d}(Q)` is rationally equivalent to zero is itself rationally equivalent to zero.

This is the injectivity of `q^* : CH_k(Y) → CH_{k+d}(Q)`: the kernel of the class of `q^*` consists
of the cycles whose pullback is rationally equivalent to zero. -/
def FlatPullbackReflectsRationalEquivalence
    {Q Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sQ : Q ⟶ D.space) (hQ : D.IsGood sQ) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (q : Q ⟶ Y)
    (hq : q ≫ sY = sQ) (d : ℕ) (hflat : IsFlat D.site D.base D.base_mem q)
    (hd : HasRelativeDimension d D.site D.base D.base_mem q) : Prop :=
  ∀ (k n : ℤ) (hkn : k + (d : ℤ) = n) (α : CycleGroup D sY k),
    IsRationallyEquivalentToZero.{v} D sQ hQ n
        (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn α) →
      IsRationallyEquivalentToZero.{v} D sY hY k α

/-- **The identity has injective flat pullback on Chow groups.** -/
theorem flatPullbackReflectsRationalEquivalence_id
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (hflat : IsFlat D.site D.base D.base_mem (𝟙 Y))
    (hd : HasRelativeDimension 0 D.site D.base D.base_mem (𝟙 Y)) :
    FlatPullbackReflectsRationalEquivalence.{v} D sY hY sY hY (𝟙 Y) (Category.id_comp sY) 0
      hflat hd := by
  intro k n hkn α h
  obtain rfl : k = n := by simpa using hkn
  have heq : flatPullbackMap D sY hY sY hY (𝟙 Y) (Category.id_comp sY) 0 hflat hd k k hkn α =
      α := Subtype.ext (flatPullbackMap_id D sY hY hflat hd k k hkn α)
  rwa [heq] at h

/-- **A composite of flat pullbacks injective on Chow groups is injective on Chow groups.** If
`q₂ : Q₂ → Q₁` and `q₁ : Q₁ → Y` are flat of relative dimensions `d₂` and `d₁` and both flat
pullbacks are injective on Chow groups, so is the flat pullback along `q₂ ≫ q₁`, which is flat
of relative dimension `d₂ + d₁` (Stacks 0EPA). -/
theorem FlatPullbackReflectsRationalEquivalence.comp
    {Q₂ Q₁ Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sQ₂ : Q₂ ⟶ D.space} {hQ₂ : D.IsGood sQ₂} {sQ₁ : Q₁ ⟶ D.space} {hQ₁ : D.IsGood sQ₁}
    {sY : Y ⟶ D.space} {hY : D.IsGood sY} {q₂ : Q₂ ⟶ Q₁} {q₁ : Q₁ ⟶ Y}
    {hq₂ : q₂ ≫ sQ₁ = sQ₂} {hq₁ : q₁ ≫ sY = sQ₁} {d₂ d₁ : ℕ}
    {hf₂ : IsFlat D.site D.base D.base_mem q₂}
    {hd₂ : HasRelativeDimension d₂ D.site D.base D.base_mem q₂}
    {hf₁ : IsFlat D.site D.base D.base_mem q₁}
    {hd₁ : HasRelativeDimension d₁ D.site D.base D.base_mem q₁}
    (h₂ : FlatPullbackReflectsRationalEquivalence.{v} D sQ₂ hQ₂ sQ₁ hQ₁ q₂ hq₂ d₂ hf₂ hd₂)
    (h₁ : FlatPullbackReflectsRationalEquivalence.{v} D sQ₁ hQ₁ sY hY q₁ hq₁ d₁ hf₁ hd₁)
    (hf : IsFlat D.site D.base D.base_mem (q₂ ≫ q₁))
    (hd : HasRelativeDimension (d₂ + d₁) D.site D.base D.base_mem (q₂ ≫ q₁)) :
    FlatPullbackReflectsRationalEquivalence.{v} D sQ₂ hQ₂ sY hY (q₂ ≫ q₁)
      (comp_structureMorphism_eq D sQ₂ sQ₁ sY q₂ q₁ hq₂ hq₁) (d₂ + d₁) hf hd := by
  intro k n hkn α h
  have hcomp := flatPullbackMap_comp D sQ₂ hQ₂ sQ₁ hQ₁ sY hY q₂ q₁ hq₂ hq₁ d₂ d₁ hf₂ hd₂ hf₁
    hd₁ k n hkn
  rw [hcomp, AddMonoidHom.comp_apply] at h
  exact h₁ k (k + (d₁ : ℤ)) rfl α (h₂ (k + (d₁ : ℤ)) n (by push_cast at hkn; omega) _ h)

/-- An isomorphism onto an algebraic space is flat of relative dimension `0`. -/
private theorem isFlat_and_hasRelativeDimension_zero_of_isIso_target
    {V W : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (j : V ⟶ W) [IsIso j]
    (hW : IsAlgebraicSpace D.site D.base D.base_mem W) :
    IsFlat D.site D.base D.base_mem j ∧ HasRelativeDimension 0 D.site D.base D.base_mem j :=
  have het := isEtale_of_isIso D.site D.base D.base_mem j
  ⟨isFlat_of_isEtale D.site D.base D.base_mem het,
    hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem j hW het⟩

/-- For an isomorphism `e : Q' ≅ Q` of good algebraic spaces over `B`, the flat pullback along
`e⁻¹` undoes the flat pullback along `e`: `(e⁻¹)^* (e^* β) = β`. -/
private theorem flatPullbackMap_inv_flatPullbackMap_hom
    {Q Q' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sQ : Q ⟶ D.space) (hQ : D.IsGood sQ) (sQ' : Q' ⟶ D.space) (hQ' : D.IsGood sQ') (e : Q' ≅ Q)
    (hebase : e.hom ≫ sQ = sQ') (heibase : e.inv ≫ sQ' = sQ)
    (hef : IsFlat D.site D.base D.base_mem e.hom)
    (hed : HasRelativeDimension 0 D.site D.base D.base_mem e.hom)
    (heif : IsFlat D.site D.base D.base_mem e.inv)
    (heid : HasRelativeDimension 0 D.site D.base D.base_mem e.inv) (m m' : ℤ)
    (h1 : m + ((0 : ℕ) : ℤ) = m') (h2 : m' + ((0 : ℕ) : ℤ) = m) (β : CycleGroup D sQ m) :
    flatPullbackMap D sQ hQ sQ' hQ' e.inv heibase 0 heif heid m' m h2
        (flatPullbackMap D sQ' hQ' sQ hQ e.hom hebase 0 hef hed m m' h1 β) = β := by
  subst h1
  have hid := isFlat_and_hasRelativeDimension_zero_of_isIso_target D (𝟙 Q) hQ.1
  have hc := isFlat_and_hasRelativeDimension_comp D sQ hQ sQ' hQ' sQ hQ e.inv e.hom heibase
    hebase 0 0 heif heid hef hed
  have := congrArg (fun φ => φ β) (flatPullbackMap_comp D sQ hQ sQ' hQ' sQ hQ e.inv e.hom heibase
    hebase 0 0 heif heid hef hed m m (by simp))
  simp only [AddMonoidHom.comp_apply] at this
  rw [← this, flatPullbackMap_congr_of_eq D sQ hQ sQ hQ e.inv_hom_id
    (comp_structureMorphism_eq D sQ sQ' sQ e.inv e.hom heibase hebase) (Category.id_comp sQ)
    (Nat.zero_add 0) hc.2.1 hc.2.2 hid.1 hid.2 m m (by simp) (by simp) β]
  exact Subtype.ext (flatPullbackMap_id D sQ hQ hid.1 hid.2 _ _ _ β)

/-- **Injectivity on Chow groups does not depend on the choice of fibre product.** Let
`q : Q → Y` and `q' : Q' → Y` be flat of relative dimension `d`, and let `e : Q' ≅ Q` be an
isomorphism with `e ≫ q = q'`. If the flat pullback along `q` is injective on Chow groups, so is
the flat pullback along `q'`: it is `q^*` followed by `e^*`, and `e^*` is invertible with inverse
`(e⁻¹)^*`, which preserves rational equivalence. -/
theorem FlatPullbackReflectsRationalEquivalence.of_iso
    {Q Q' Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sQ : Q ⟶ D.space} {hQ : D.IsGood sQ} {sQ' : Q' ⟶ D.space} (hQ' : D.IsGood sQ')
    {sY : Y ⟶ D.space} {hY : D.IsGood sY} {q : Q ⟶ Y} {q' : Q' ⟶ Y} (e : Q' ≅ Q)
    (he : e.hom ≫ q = q') {hq : q ≫ sY = sQ} (hq' : q' ≫ sY = sQ') {d : ℕ}
    {hflat : IsFlat D.site D.base D.base_mem q}
    {hd : HasRelativeDimension d D.site D.base D.base_mem q}
    (hflat' : IsFlat D.site D.base D.base_mem q')
    (hd' : HasRelativeDimension d D.site D.base D.base_mem q')
    (h : FlatPullbackReflectsRationalEquivalence.{v} D sQ hQ sY hY q hq d hflat hd) :
    FlatPullbackReflectsRationalEquivalence.{v} D sQ' hQ' sY hY q' hq' d hflat' hd' := by
  intro k n hkn α hα
  subst hkn
  have hebase : e.hom ≫ sQ = sQ' := by rw [← hq, ← Category.assoc, he, hq']
  have heibase : e.inv ≫ sQ' = sQ := by
    rw [← hebase, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hfe := isFlat_and_hasRelativeDimension_zero_of_isIso_target D e.hom hQ.1
  have hfei := isFlat_and_hasRelativeDimension_zero_of_isIso_target D e.inv hQ'.1
  have hc := isFlat_and_hasRelativeDimension_comp D sQ' hQ' sQ hQ sY hY e.hom q hebase hq 0 d
    hfe.1 hfe.2 hflat hd
  have h₁ : flatPullbackMap D sQ' hQ' sY hY q' hq' d hflat' hd' k (k + (d : ℤ)) rfl α =
      flatPullbackMap D sQ' hQ' sQ hQ e.hom hebase 0 hfe.1 hfe.2 (k + (d : ℤ)) (k + (d : ℤ))
        (by simp) (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k (k + (d : ℤ)) rfl α) := by
    rw [flatPullbackMap_congr_of_eq D sY hY sQ' hQ' he.symm hq'
      (comp_structureMorphism_eq D sQ' sQ sY e.hom q hebase hq) (Nat.zero_add d).symm hflat' hd'
      hc.2.1 hc.2.2 k (k + (d : ℤ)) rfl (by simp) α,
      flatPullbackMap_comp D sQ' hQ' sQ hQ sY hY e.hom q hebase hq 0 d hfe.1 hfe.2 hflat hd k
        (k + (d : ℤ)) (by simp), AddMonoidHom.comp_apply]
  refine h k (k + (d : ℤ)) rfl α ?_
  rw [← flatPullbackMap_inv_flatPullbackMap_hom D sQ hQ sQ' hQ' e hebase heibase hfe.1 hfe.2
    hfei.1 hfei.2
    (k + (d : ℤ)) (k + (d : ℤ)) (by simp) (by simp)
    (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k (k + (d : ℤ)) rfl α)]
  refine isRationallyEquivalentToZero_flatPullbackMap_of_isIso D sQ' hQ' sQ hQ e.inv heibase hfei.1
    hfei.2 _ _ _ ?_
  rwa [← h₁]

end Injective

/-! ### Injectivity after every base change -/

section BaseChange

variable (D : BaseSpaceDimensionSituation.{u})

/-- **Injectivity of flat pullback on Chow groups after every base change.** A morphism
`π : P → X` of good algebraic spaces over `B` has this property at relative dimension `d` when
for every morphism `f : Y → X` of good algebraic spaces over `B` there is a cartesian square

```
Q --p--> P
|q       |π
v        v
Y --f--> X
```

with `Q` good over `B`, in which `q` is flat of relative dimension `d` and the flat pullback
`q^* : CH_k(Y) → CH_{k+d}(Q)` is injective. -/
def HasInjectiveChowBaseChange {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (π : P ⟶ X) (d : ℕ) : Prop :=
  ∀ ⦃Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u⦄ (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : Y ⟶ X), f ≫ sX = sY →
    ∃ (Q : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u) (sQ : Q ⟶ D.space)
      (hQ : D.IsGood sQ) (p : Q ⟶ P) (q : Q ⟶ Y) (_ : IsPullback p q π f) (hq : q ≫ sY = sQ)
      (hflat : IsFlat D.site D.base D.base_mem q)
      (hd : HasRelativeDimension d D.site D.base D.base_mem q),
      FlatPullbackReflectsRationalEquivalence.{v} D sQ hQ sY hY q hq d hflat hd

/-- **The identity has injective flat pullback after every base change**, at relative
dimension `0`: along `f : Y → X` the square with `Q = Y` and `q = id_Y` is cartesian. -/
theorem hasInjectiveChowBaseChange_id {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) : HasInjectiveChowBaseChange.{v} D sX (𝟙 X) 0 := by
  intro Y sY hY f hf
  have hid := isFlat_and_hasRelativeDimension_zero_of_isIso_target D (𝟙 Y) hY.1
  exact ⟨Y, sY, hY, f, 𝟙 Y, IsPullback.of_id_snd, Category.id_comp sY, hid.1, hid.2,
    flatPullbackReflectsRationalEquivalence_id.{v} D sY hY _ _⟩

/-- **Composites of towers.** If `π₁ : P₁ → X` has injective flat pullback after every base
change at relative dimension `d₁`, and `π₂ : P₂ → P₁` does at relative dimension `d₂` (for the
structure morphism `π₁ ≫ s_X` of `P₁`), then so does `π₂ ≫ π₁ : P₂ → X` at relative dimension
`d₂ + d₁`.

Along `f : Y → X` the square of `π₁` has a good corner `Q₁`, the square of `π₂` along
`Q₁ → P₁` has a good corner `Q₂`, and the two squares paste to a cartesian square for
`π₂ ≫ π₁`, along which the flat pullback is the composite of the two flat pullbacks
(Stacks 0EPA). -/
theorem HasInjectiveChowBaseChange.comp
    {X P₁ P₂ : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sX : X ⟶ D.space}
    {π₁ : P₁ ⟶ X} {π₂ : P₂ ⟶ P₁} {d₁ d₂ : ℕ}
    (h₁ : HasInjectiveChowBaseChange.{v} D sX π₁ d₁)
    (h₂ : HasInjectiveChowBaseChange.{v} D (π₁ ≫ sX) π₂ d₂) :
    HasInjectiveChowBaseChange.{v} D sX (π₂ ≫ π₁) (d₂ + d₁) := by
  intro Y sY hY f hf
  obtain ⟨Q₁, sQ₁, hQ₁, p₁, q₁, sq₁, hq₁, hf₁, hd₁, hinj₁⟩ := h₁ sY hY f hf
  have hp₁ : p₁ ≫ π₁ ≫ sX = sQ₁ := by
    rw [← Category.assoc, sq₁.w, Category.assoc, hf, hq₁]
  obtain ⟨Q₂, sQ₂, hQ₂, p₂, q₂, sq₂, hq₂, hf₂, hd₂, hinj₂⟩ := h₂ sQ₁ hQ₁ p₁ hp₁
  have hcomp := isFlat_and_hasRelativeDimension_comp D sQ₂ hQ₂ sQ₁ hQ₁ sY hY q₂ q₁ hq₂ hq₁ d₂
    d₁ hf₂ hd₂ hf₁ hd₁
  exact ⟨Q₂, sQ₂, hQ₂, p₂, q₂ ≫ q₁, sq₂.paste_vert sq₁,
    comp_structureMorphism_eq D sQ₂ sQ₁ sY q₂ q₁ hq₂ hq₁, hcomp.2.1, hcomp.2.2,
    hinj₂.comp D hinj₁ hcomp.2.1 hcomp.2.2⟩

/-- **Injectivity of flat pullback on Chow groups along every fibre product.** For a morphism
`π : P → X` of good algebraic spaces over `B`, flat of relative dimension `d`: for every morphism
`f : Y → X` of good algebraic spaces over `B` and every cartesian square

```
Q --p--> P
|q       |π
v        v
Y --f--> X
```

with `Q` good over `B`, the flat pullback `q^* : CH_k(Y) → CH_{k+d}(Q)` is injective. The base
change `q` is flat of relative dimension `d` by Stacks 0EPD. -/
def HasInjectiveChowPullbacks {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP) (π : P ⟶ X)
    (hπ : π ≫ sX = sP) (d : ℕ) (hflat : IsFlat D.site D.base D.base_mem π)
    (hd : HasRelativeDimension d D.site D.base D.base_mem π) : Prop :=
  ∀ ⦃Y Q : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u⦄ (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : Y ⟶ X), f ≫ sX = sY →
    ∀ (sQ : Q ⟶ D.space) (hQ : D.IsGood sQ) (p : Q ⟶ P) (q : Q ⟶ Y) (sq : IsPullback p q π f)
      (hq : q ≫ sY = sQ),
      FlatPullbackReflectsRationalEquivalence.{v} D sQ hQ sY hY q hq d
        (isFlat_and_hasRelativeDimension_of_isPullback D sQ hQ sY hY sP hP sX hX hq hπ sq.flip d
          hflat hd).2.1
        (isFlat_and_hasRelativeDimension_of_isPullback D sQ hQ sY hY sP hP sX hX hq hπ sq.flip d
          hflat hd).2.2

/-- **One fibre product suffices.** If along every `f : Y → X` some cartesian square with good
corner has injective flat pullback on Chow groups, then every such square does: two fibre
products are isomorphic over `Y`. -/
theorem HasInjectiveChowBaseChange.hasInjectiveChowPullbacks
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} (hX : D.IsGood sX) {sP : P ⟶ D.space} (hP : D.IsGood sP) {π : P ⟶ X}
    (hπ : π ≫ sX = sP) {d : ℕ} (hflat : IsFlat D.site D.base D.base_mem π)
    (hd : HasRelativeDimension d D.site D.base D.base_mem π)
    (h : HasInjectiveChowBaseChange.{v} D sX π d) :
    HasInjectiveChowPullbacks.{v} D sX hX sP hP π hπ d hflat hd := by
  intro Y Q sY hY f hf sQ hQ p q sq hq
  obtain ⟨Q₀, sQ₀, hQ₀, p₀, q₀, sq₀, hq₀, hf₀, hd₀, hinj₀⟩ := h sY hY f hf
  exact hinj₀.of_iso D hQ (sq.isoIsPullback _ _ sq₀) (sq.isoIsPullback_hom_snd _ _ sq₀) hq _ _

end BaseChange

end AlgebraicGeometry.Space.PrivateChern

end
