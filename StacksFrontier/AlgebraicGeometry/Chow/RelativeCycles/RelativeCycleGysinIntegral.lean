module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapClosedImmersionInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.IsoComponentEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponentClassModuleIso
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionDescentCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.GysinGysinCommute
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.ClosedCoverExactSequence
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackRationallyCompatible
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardUncontained
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapChernDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.RelativeCycleBivariant

/-!
# The Gysin identity for a relative cycle on an integral test scheme

Let `(S, δ)` be as in Section 0H65, let `p : X ⟶ Y` be a morphism of schemes locally of finite
type over `S`, let `r ≥ 0` and let `α ∈ z(X/Y, r)`. For an integral test scheme `w : W ⟶ Y` of
`δ`-dimension `k + 1`, an invertible `𝒪_W`-module `M` and `σ ∈ Γ(W, M)`, with zero schemes
`i : D ⟶ W` and `j : E ⟶ W ×_Y X` of `σ` and of its pullback, this file proves

  `w^*α ∩ i_* i^* [W] ≡ j_* j^*(w^*α ∩ [W])`   modulo rational equivalence inside `E`,

where `i^*` and `j^*` are the Gysin maps of Stacks 02T8 for the first Chern class. It is the case
of a single integral component of the Gysin compatibility of the operation of Stacks 0H6F, and it
rests on `Stacks.Chow.cap_chernComponentCycle_apply`: if `σ ≠ 0` then `i^*[W]` is the divisor of
`σ`, and otherwise `D = W` and `i^*[W]` is the first Chern class of `M` capped with `[W]`; in both
cases it is the divisor of a meromorphic section of `M`, and so is every component of the right
hand side.

## Main results

* `Stacks.Chow.relativeCycleCap_gysin_fundamentalCycle` — the displayed identity.
* `Stacks.Chow.relativeCycleCap_isRationallyEquivalentToZeroWithin` — the operation carries a
  cycle rationally equivalent to zero inside a closed subscheme of the test scheme to a cycle
  rationally equivalent to zero inside its inverse image.
* `Stacks.Chow.properPushforward_gysinRule_extendCycleGroup_congr` — the pushforward to the
  ambient scheme of the Gysin cycle of Stacks 02T8 depends on the invertible module and its
  section only through the zero scheme and the isomorphism class of the module.

## References

* [Stacks Project, Tag 0H6F](https://stacks.math.columbia.edu/tag/0H6F)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- Rational equivalence to zero within a subset does not see how the degree is written. -/
theorem isRationallyEquivalentToZeroWithin_congr_degree (C : ChowSituation.{u}) {X : Scheme.{u}}
    (q : X ⟶ C.S) [LocallyOfFiniteType q] {k k' : ℤ} (hk : k = k') (a : CycleGroup C q k)
    (a' : CycleGroup C q k') (h : a.1 = a'.1) (T : Set X)
    (ha : IsRationallyEquivalentToZeroWithin C q k a T) :
    IsRationallyEquivalentToZeroWithin C q k' a' T := by
  subst hk
  rwa [← Subtype.ext h]

/-- The coefficient of a pushforward along a closed immersion off its image vanishes. -/
theorem properPushforward_apply_eq_zero_of_notMem_range_of_isClosedImmersion
    (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ sX = sZ) (k : ℤ) (c : CycleGroup C sZ k) {y : X} (hy : y ∉ Set.range i.base) :
    (properPushforward C sZ sX i hi k c).1 y = 0 := by
  rw [properPushforward_apply_of_isClosedImmersion]
  have he : i.base ⁻¹' {y} = ∅ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    exact fun h ↦ hy ⟨z, h⟩
  rw [he, finsum_mem_empty]

/-- A point where the pushforward of a cycle along a closed immersion is nonzero is the image of
a point where the cycle is nonzero. -/
theorem exists_apply_ne_zero_of_properPushforward_apply_ne_zero (C : ChowSituation.{u})
    {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ) (k : ℤ)
    (c : CycleGroup C sZ k) {y : X} (hy : (properPushforward C sZ sX i hi k c).1 y ≠ 0) :
    ∃ z, i.base z = y ∧ c.1 z ≠ 0 := by
  by_cases h : y ∈ Set.range i.base
  · obtain ⟨z, rfl⟩ := h
    rw [properPushforward_apply_image_of_isClosedImmersion] at hy
    exact ⟨z, rfl, hy⟩
  · exact absurd (properPushforward_apply_eq_zero_of_notMem_range_of_isClosedImmersion C _ _ _ _ _
      _ h) hy

/-- A cycle for one structure morphism is a cycle for an equal one. -/
def cycleGroupOfMorphismEq (C : ChowSituation.{u}) {X : Scheme.{u}} {q q' : X ⟶ C.S}
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (h : q = q') {k : ℤ}
    (c : CycleGroup C q k) : CycleGroup C q' k :=
  ⟨c.1, (mem_cyclesOfDimension_congr C h rfl _).1 c.2⟩

/-- Transporting a cycle along an equality of structure morphisms leaves its coefficients
unchanged. -/
@[simp]
theorem cycleGroupOfMorphismEq_val (C : ChowSituation.{u}) {X : Scheme.{u}} {q q' : X ⟶ C.S}
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (h : q = q') {k : ℤ}
    (c : CycleGroup C q k) : (cycleGroupOfMorphismEq C h c).1 = c.1 :=
  rfl

/-- The cycle of a closed subscheme depends on the structure morphism and the degree only through
their values. -/
theorem cycleAssociatedToClosedSubscheme_val_congr (C : ChowSituation.{u}) {X Z : Scheme.{u}}
    {q q' : X ⟶ C.S} [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (hq : q = q')
    (i : Z ⟶ X) [IsClosedImmersion i] {j j' : ℤ} (hj : j = j') :
    (cycleAssociatedToClosedSubscheme C q i j).1 =
      (cycleAssociatedToClosedSubscheme C q' i j').1 := by
  subst hq hj
  rfl

/-- The cycle of a closed subscheme of a closed subscheme depends only on the inner ideal sheaf. -/
theorem cycleAssociatedToClosedSubscheme_subschemeι_comp_congr (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (q : X ⟶ C.S) [LocallyOfFiniteType q] (f : Z ⟶ X) [IsClosedImmersion f]
    {I J : Z.IdealSheafData} (h : I = J) (k : ℤ) :
    cycleAssociatedToClosedSubscheme C q (I.subschemeι ≫ f) k =
      cycleAssociatedToClosedSubscheme C q (J.subschemeι ≫ f) k := by
  subst h
  rfl

/-- The component cycle of a meromorphic section depends on the structure morphism and the degree
only through the underlying Weil divisor. -/
theorem chernComponentCycle_val_congr (C : ChowSituation.{u}) {A : Scheme.{u}} (sA sA' : A ⟶ C.S)
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] [IsIntegral A] [IsLocallyNoetherian A]
    {j j' : ℤ} (hj : schemeDeltaDimension C sA = ((j + 1 : ℤ) : EInt))
    (hj' : schemeDeltaDimension C sA' = ((j' + 1 : ℤ) : EInt)) {L : A.Modules}
    (hL : ∀ x : A, Stacks.Divisors.IsTrivializedNear L x)
    (s : L.presheaf.stalk (genericPoint A)) :
    (chernComponentCycle C sA hj hL s).1 = (chernComponentCycle C sA' hj' hL s).1 := by
  refine Function.locallyFinsuppWithin.ext fun x => ?_
  by_cases hx : ∃ Z : Stacks.Divisors.PrimeDivisor A, Z.genericPoint = x
  · obtain ⟨Z, rfl⟩ := hx
    rw [chernComponentCycle_genericPoint, chernComponentCycle_genericPoint]
  · have hne : ∀ Z : Stacks.Divisors.PrimeDivisor A, Z.genericPoint ≠ x := fun Z hZ => hx ⟨Z, hZ⟩
    rw [chernComponentCycle_eq_zero C sA hj hL s x hne,
      chernComponentCycle_eq_zero C sA' hj' hL s x hne]

/-- Proper pushforward of cycles depends on the structure morphisms and the degree only through
their values and the underlying cycle. -/
theorem properPushforward_val_congr (C : ChowSituation.{u}) {A B : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] {sB sB' : B ⟶ C.S}
    [LocallyOfFiniteType sB] [LocallyOfFiniteType sB'] (hA : sA = sA') (hB : sB = sB')
    (f : A ⟶ B) [IsProper f] (hf : f ≫ sB = sA) (hf' : f ≫ sB' = sA') {j j' : ℤ}
    (c : CycleGroup C sA j) (c' : CycleGroup C sA' j') (hc : c.1 = c'.1) :
    (properPushforward C sA sB f hf j c).1 = (properPushforward C sA' sB' f hf' j' c').1 := by
  subst hA hB
  exact val_properPushforward_eq_of_val_eq C sA sB f hf c c' hc

/-- A sum of products with a function `m` may be taken over the points where `m` is nonzero. -/
theorem finsum_mul_eq_finsum_subtype_ne_zero {ι : Type*} (m G : ι → ℤ) :
    ∑ᶠ x, m x * G x = ∑ᶠ x : {x // m x ≠ 0}, m x.1 * G x.1 := by
  symm
  refine (finsum_subtype_eq_finsum_cond (f := fun x ↦ m x * G x) (fun x ↦ m x ≠ 0)).trans ?_
  exact (finsum_mem_inter_support_eq' (fun x ↦ m x * G x) {x | m x ≠ 0} Set.univ
    fun x hx ↦ ⟨fun _ ↦ trivial, fun _ ↦ left_ne_zero_of_mul hx⟩).trans (finsum_mem_univ _)

/-- On an integral scheme of delta-dimension `k + 1` the generic point has relative dimension
`k + 1`. -/
theorem relativeDimension_genericPoint_of_schemeDeltaDimension (C : ChowSituation.{u})
    {W : Scheme.{u}} [IsIntegral W] (sW : W ⟶ C.S) [LocallyOfFiniteType sW] {k : ℤ}
    (hW : schemeDeltaDimension C sW = (k : EInt)) :
    relativeDimension C.dimensionFunction sW (genericPoint W) = k := by
  rw [schemeDeltaDimension_eq_genericPoint] at hW
  exact WithBotTop.coe_injective hW

/-- The Gysin cycle of Stacks 02T8 of the fundamental cycle of an integral scheme is the Gysin
component cycle of the scheme itself. -/
theorem gysinRule_extendCycleGroup_fundamentalCycle (C : ChowSituation.{u}) {W : Scheme.{u}}
    [IsIntegral W] (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (k : ℤ)
    (hW : schemeDeltaDimension C sW = ((k + 1 : ℤ) : EInt)) (M : W.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property M]
    (σ : Γ(M, ⊤)) (chern : FirstChernComponentClassRule C sW k) :
    (gysinRule C sW k M σ chern).extendCycleGroup (fundamentalCycle C sW (k + 1)) =
      gysinComponentCycle C sW k M σ chern (integralComponentAt (genericPoint W))
        (isIntegral_integralComponentAt _)
        (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C sW _
          (relativeDimension_genericPoint_of_schemeDeltaDimension C sW hW)) := by
  have : IsIso (integralComponentAt (genericPoint W)).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).2
      (integralComponentAt_genericPoint_eq_bot W)
  rw [fundamentalCycle, cycleAssociatedToClosedSubscheme_eq_of_iso C sW (𝟙 W)
    (integralComponentAt (genericPoint W)).subschemeι
    (asIso (integralComponentAt (genericPoint W)).subschemeι).symm (by simp) (k + 1)]
  exact IntegralComponentRule.extendCycleGroup_cycleAssociatedToClosedSubscheme _ _ _ _

/-! ### The pushed-forward Gysin cycle -/

/-- For an integral component `W` contained in the zero scheme `E`, the pushforward to `X` of
its Gysin component cycle is the pushforward along `W ↪ X` of the first Chern class
representative. -/
private theorem properPushforward_zeroScheme_gysinComponentCycle_of_le (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (chern : FirstChernComponentClassRule C p k) (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hle : Stacks.Divisors.zeroScheme X L s ≤ W) :
    properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
        (gysinComponentCycle C p k L s chern W hW hDim) =
      properPushforward C (W.subschemeι ≫ p) p W.subschemeι rfl k
        (Quotient.out (chern W hW hDim)) := by
  rw [gysinComponentCycle_of_le C p k L s chern W hW hDim hle, properPushforward_properPushforward,
    properPushforward_congr C _ _ _ _ (Scheme.IdealSheafData.inclusion_subschemeι hle) _
      (by simp)]

section GysinCongr

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S) [LocallyOfFiniteType q] (d : ℤ)

/-- The pushforward to the ambient scheme of the Gysin cycle of Stacks 02T8 is the locally finite
sum of the pushforwards of the Gysin component cycles. -/
theorem properPushforward_gysinRule_extendCycleGroup_apply (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (b : Γ(N, ⊤)) (c : CycleGroup C q (d + 1)) (y : X) :
    (properPushforward C ((Stacks.Divisors.zeroScheme X N b).subschemeι ≫ q) q
        (Stacks.Divisors.zeroScheme X N b).subschemeι rfl d
        ((gysinRule C q d N b (firstChernComponentClass C q d N)).extendCycleGroup c)).1 y =
      ∑ᶠ x, c.1 x * (properPushforward C ((Stacks.Divisors.zeroScheme X N b).subschemeι ≫ q) q
        (Stacks.Divisors.zeroScheme X N b).subschemeι rfl d
        (gysinComponentCycleAt C q d N b (firstChernComponentClass C q d N) x)).1 y := by
  by_cases hy : y ∈ Set.range (Stacks.Divisors.zeroScheme X N b).subschemeι.base
  · obtain ⟨e, rfl⟩ := hy
    rw [properPushforward_apply_image_of_isClosedImmersion]
    simp_rw [properPushforward_apply_image_of_isClosedImmersion]
    rfl
  · rw [properPushforward_apply_eq_zero_of_notMem_range_of_isClosedImmersion C _ _ _ _ _ _ hy]
    refine (finsum_eq_zero_of_forall_eq_zero fun x ↦ ?_).symm
    rw [properPushforward_apply_eq_zero_of_notMem_range_of_isClosedImmersion C _ _ _ _ _ _ hy,
      mul_zero]

/-- **The pushed-forward Gysin component cycle depends only on the zero scheme and the
isomorphism class of the module.** For an integral component not contained in the zero scheme it
is the cycle of the intersection, a closed subscheme of `X` determined by the zero scheme; for one
contained in it, the pushforward of a representative of the first Chern class of the restricted
module, which depends on the module only up to isomorphism. -/
theorem properPushforward_gysinComponentCycleAt_congr (N N' : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N']
    (b : Γ(N, ⊤)) (b' : Γ(N', ⊤))
    (hZ : Stacks.Divisors.zeroScheme X N b = Stacks.Divisors.zeroScheme X N' b') (φ : N ≅ N')
    (x : X) :
    (properPushforward C ((Stacks.Divisors.zeroScheme X N b).subschemeι ≫ q) q
        (Stacks.Divisors.zeroScheme X N b).subschemeι rfl d
        (gysinComponentCycleAt C q d N b (firstChernComponentClass C q d N) x)).1 =
      (properPushforward C ((Stacks.Divisors.zeroScheme X N' b').subschemeι ≫ q) q
        (Stacks.Divisors.zeroScheme X N' b').subschemeι rfl d
        (gysinComponentCycleAt C q d N' b' (firstChernComponentClass C q d N') x)).1 := by
  classical
  by_cases hx : relativeDimension C.dimensionFunction q x = d + 1
  · rw [gysinComponentCycleAt_eq C q d N b _ hx, gysinComponentCycleAt_eq C q d N' b' _ hx]
    have hW := isIntegral_integralComponentAt x
    have hDim := schemeDeltaDimension_integralComponentAt_of_eq C q hx
    by_cases hle : Stacks.Divisors.zeroScheme X N b ≤ integralComponentAt x
    · have hle' : Stacks.Divisors.zeroScheme X N' b' ≤ integralComponentAt x := hZ ▸ hle
      rw [properPushforward_zeroScheme_gysinComponentCycle_of_le C q d N b _ _ hW hDim hle,
        properPushforward_zeroScheme_gysinComponentCycle_of_le C q d N' b' _ _ hW hDim hle']
      let := hW
      rw [firstChernComponentClass_eq_of_iso C q d φ (integralComponentAt x) hDim]
    · have hle' : ¬ Stacks.Divisors.zeroScheme X N' b' ≤ integralComponentAt x := hZ ▸ hle
      rw [gysinComponentCycle_of_not_le C q d N b _ _ hW hDim hle,
        gysinComponentCycle_of_not_le C q d N' b' _ _ hW hDim hle',
        properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp,
        properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
      rw [hZ]
  · have h0 : ∀ (N₀ : X.Modules)
        [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N₀]
        (b₀ : Γ(N₀, ⊤)), gysinComponentCycleAt C q d N₀ b₀ (firstChernComponentClass C q d N₀) x
          = 0 := by
      intro N₀ _ b₀
      apply Subtype.ext
      change (gysinRule C q d N₀ b₀ _).totalize (integralComponentAt x) = 0
      rw [IntegralComponentRule.totalize, dite_eq_right]
      rintro ⟨-, hdim⟩
      apply hx
      have h := relativeDimension_genericPointOf C q (integralComponentAt x)
        (isIntegral_integralComponentAt x) hdim
      rwa [genericPointOf_integralComponentAt] at h
    rw [h0 N b, h0 N' b', properPushforward_zero, properPushforward_zero]

/-- **The pushed-forward Gysin cycle depends only on the zero scheme and the isomorphism class
of the module.** -/
theorem properPushforward_gysinRule_extendCycleGroup_congr (N N' : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N']
    (b : Γ(N, ⊤)) (b' : Γ(N', ⊤))
    (hZ : Stacks.Divisors.zeroScheme X N b = Stacks.Divisors.zeroScheme X N' b') (φ : N ≅ N')
    (c : CycleGroup C q (d + 1)) :
    (properPushforward C ((Stacks.Divisors.zeroScheme X N b).subschemeι ≫ q) q
        (Stacks.Divisors.zeroScheme X N b).subschemeι rfl d
        ((gysinRule C q d N b (firstChernComponentClass C q d N)).extendCycleGroup c)).1 =
      (properPushforward C ((Stacks.Divisors.zeroScheme X N' b').subschemeι ≫ q) q
        (Stacks.Divisors.zeroScheme X N' b').subschemeι rfl d
        ((gysinRule C q d N' b' (firstChernComponentClass C q d N')).extendCycleGroup c)).1 := by
  refine Function.locallyFinsuppWithin.ext fun y ↦ ?_
  rw [properPushforward_gysinRule_extendCycleGroup_apply,
    properPushforward_gysinRule_extendCycleGroup_apply]
  refine finsum_congr fun x ↦ ?_
  rw [properPushforward_gysinComponentCycleAt_congr C q d N N' b b' hZ φ x]

end GysinCongr

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (p : X ⟶ Y) [LocallyOfFiniteType p] (r : ℕ) (α : FamilyOfCycles p r)
  (hα : letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    IsRelativeCycle p r α)

include hα in
/-- **The operation of a relative cycle carries a rational equivalence inside a closed
subscheme to one inside its inverse image.** If a cycle `c` on the test scheme `T` is rationally
equivalent to zero within the support of an ideal sheaf `I`, then `g^*α ∩ c` is rationally
equivalent to zero within the inverse image of that support in `T ×_Y X`.

The cycle is the pushforward of its inverse image on `V(I)`, which is rationally equivalent to
zero there; the operation commutes with that pushforward (Stacks 0H6B), kills rational
equivalences on `V(I)` (Stacks 0B7A with 0H6E), and the pushforward of a rational equivalence
along a closed immersion is carried by its image. -/
theorem relativeCycleCap_isRationallyEquivalentToZeroWithin {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k d : ℤ) (hd : d = (r : ℤ) + k) (I : T.IdealSheafData)
    (c : CycleGroup C (g ≫ sY) k)
    (hc : IsRationallyEquivalentToZeroWithin C (g ≫ sY) k c (I.support : Set T)) :
    IsRationallyEquivalentToZeroWithin C (pullback.fst p g ≫ p ≫ sY) d
      (cycleGroupCongr C _ hd.symm (relativeCycleCap C sY p r α g k c))
      ((pullback.snd p g).base ⁻¹' (I.support : Set T)) := by
  obtain ⟨K, W, hW, hDim, hLocal, hsub, f, hf⟩ := hc
  set c' := cyclePullbackAlongClosedImmersion C (I.subschemeι ≫ g ≫ sY) (g ≫ sY) I.subschemeι rfl
    k c with hc'
  have hc'0 : IsRationallyEquivalentToZero C (I.subschemeι ≫ g ≫ sY) k c' :=
    isRationallyEquivalentToZero_cyclePullbackAlongClosedImmersion C (g ≫ sY) I k W hW hDim hLocal
      f hsub c hf
  have hcc' : properPushforward C (I.subschemeι ≫ g ≫ sY) (g ≫ sY) I.subschemeι rfl k c' = c := by
    refine properPushforward_cyclePullbackAlongClosedImmersion_eq C _ _ I.subschemeι rfl k c
      fun y hy ↦ ?_
    rw [hf y]
    refine finsum_eq_zero_of_forall_eq_zero fun j ↦ ?_
    by_contra hne
    refine hy ?_
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hsub j (support_principalDivisorPushforward_subset C (g ≫ sY) (W j) (hW j) (f j) hne)
  -- the operation on `V(I)` kills `c'`
  have hzero := VeryWeakCapRule.cap_eq_zero_of_isCycleGysinNatural C (p ≫ sY) sY p rfl (-(r : ℤ))
    (relativeCycleCapRule C sY p r α) (isCycleGysinNatural_relativeCycleCapRule C sY p r α hα)
    (I.subschemeι ≫ g) k c' hc'0
  have hmem : cycleGroupCongr C (pullback.fst p (I.subschemeι ≫ g) ≫ p ≫ sY)
      (by ring : (r : ℤ) + k = k - -(r : ℤ)) (relativeCycleCap C sY p r α (I.subschemeι ≫ g) k c')
      ∈ rationalEquivalences C (pullback.fst p (I.subschemeι ≫ g) ≫ p ≫ sY) (k - -(r : ℤ)) :=
    (QuotientAddGroup.eq_zero_iff _).1 hzero
  -- push it forward along the base change of `V(I) ⟶ T`
  let : IsClosedImmersion (bivariantBaseChangeMap p g I.subschemeι) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap p g I.subschemeι)
      (P := @IsClosedImmersion) inferInstance
  have hpush := properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion C
    (pullback.fst p (I.subschemeι ≫ g) ≫ p ≫ sY) (pullback.fst p g ≫ p ≫ sY)
    (bivariantBaseChangeMap p g I.subschemeι) (by simp) (k - -(r : ℤ)) hmem
  have hprop := properPushforward_relativeCycleCap C sY p r α g I.subschemeι
    (bivariantBaseChangeMap p g I.subschemeι) (isPullback_bivariantBaseChangeMap p g I.subschemeι)
    (by simp) k c'
  rw [show properPushforward C ((I.subschemeι ≫ g) ≫ sY) (g ≫ sY) I.subschemeι
    (by simp [Category.assoc]) k c' = c from hcc'] at hprop
  refine (isRationallyEquivalentToZeroWithin_congr_degree C _ (by rw [hd]; ring) _ _ ?_ _
    hpush).mono ?_
  · rw [← hprop]
    rfl
  · rintro x ⟨x', rfl⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, bivariantBaseChangeMap, pullback.lift_snd,
      Scheme.Hom.comp_apply, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨_, rfl⟩

/-! ### The integral case -/

section IntegralCase

variable {W : Scheme.{u}} [IsIntegral W] (w : W ⟶ Y) [LocallyOfFiniteType w] (k d : ℤ)
  (hd : d = (r : ℤ) + k) (hW : schemeDeltaDimension C (w ≫ sY) = ((k + 1 : ℤ) : EInt))
  (M : W.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property M]
  (σ : Γ(M, ⊤))

attribute [local instance] isIntegral_integralComponentAt

include hα in
/-- **The divisor side and the Gysin side of the integral case, componentwise.** For a nonzero
meromorphic section `t` of `M`, the difference of `w^*α ∩ div_M(t)` and `j_* j^*(w^*α ∩ [W])` is,
at each point, the sum over the components `Z_x` of `w^*α ∩ [W]` of their multiplicities times the
difference of the pushforward of `div(t|_{Z_x})` and the pushed-forward Gysin component cycle of
`Z_x`. This is `Stacks.Chow.cap_chernComponentCycle_apply`. -/
theorem relativeCycleCap_chernComponentCycle_sub_gysin_apply
    (t : M.presheaf.stalk (genericPoint W)) (ht : t ≠ 0) (y : ↥(pullback p w)) :
    haveI : AlgebraicGeometry.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M :=
      Stacks.Divisors.isInvertible_presheaf M
    letI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sY)
    (cycleGroupCongr C _ hd.symm (relativeCycleCap C sY p r α w k
        (chernComponentCycle C (w ≫ sY) hW
          (Stacks.Divisors.isTrivializedNear_of_isInvertible M) t))).1 y -
      (properPushforward C
          ((bivariantPullbackZeroScheme p w M σ).subschemeι ≫ pullback.fst p w ≫ p ≫ sY)
          (pullback.fst p w ≫ p ≫ sY) (bivariantPullbackZeroScheme p w M σ).subschemeι rfl d
          ((gysinRule C (pullback.fst p w ≫ p ≫ sY) d (bivariantPullbackModule p w M)
              (bivariantPullbackSection p w M σ)
              (firstChernComponentClass C (pullback.fst p w ≫ p ≫ sY) d
                (bivariantPullbackModule p w M))).extendCycleGroup
            (cycleGroupCongr C _ (by rw [hd]; ring) (relativeCycleCap C sY p r α w (k + 1)
              (fundamentalCycle C (w ≫ sY) (k + 1)))))).1 y =
      ∑ᶠ x : capSupport C (w ≫ sY) (pullback.snd p w) r (baseChangeFamily p w r α) k,
        (cap C (w ≫ sY) (pullback.snd p w) (baseChangeFamily p w r α)
            (fundamentalCycle C (w ≫ sY) (k + 1))).1 x.1 *
          ((capComponentDivisor C (w ≫ sY) (pullback.snd p w) r (baseChangeFamily p w r α) M t
              x).1 y -
            (properPushforward C
              ((bivariantPullbackZeroScheme p w M σ).subschemeι ≫ pullback.fst p w ≫ p ≫ sY)
              (pullback.fst p w ≫ p ≫ sY) (bivariantPullbackZeroScheme p w M σ).subschemeι rfl d
              (gysinComponentCycleAt C (pullback.fst p w ≫ p ≫ sY) d (bivariantPullbackModule p w M)
                (bivariantPullbackSection p w M σ)
                (firstChernComponentClass C (pullback.fst p w ≫ p ≫ sY) d
                  (bivariantPullbackModule p w M)) x.1)).1 y) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M :=
    Stacks.Divisors.isInvertible_presheaf M
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sY)
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hαW := isRelativeCycle_baseChangeFamily p w r hα
  set m := (cap C (w ≫ sY) (pullback.snd p w) (baseChangeFamily p w r α)
    (fundamentalCycle C (w ≫ sY) (k + 1))).1 with hm
  have hfin := finite_support_inter_generalizations m.locallyFiniteSupport
    (isCompact_singleton (x := y))
  have hsubfin : ∀ F : capSupport C (w ≫ sY) (pullback.snd p w) r (baseChangeFamily p w r α) k → ℤ,
      (∀ x, F x ≠ 0 → y ∈ closure {x.1}) → (Function.support F).Finite := by
    intro F hF
    refine (hfin.preimage Subtype.val_injective.injOn).subset fun x hx ↦ ?_
    exact ⟨⟨y, rfl, hF x hx⟩, x.2⟩
  change (cap C (w ≫ sY) (pullback.snd p w) (baseChangeFamily p w r α)
    (chernComponentCycle C (w ≫ sY) hW
      (Stacks.Divisors.isTrivializedNear_of_isInvertible M) t)).1 y - _ = _
  rw [cap_chernComponentCycle_apply C (w ≫ sY) (pullback.snd p w) r _ hW M hαW t ht y,
    properPushforward_gysinRule_extendCycleGroup_apply]
  rw [show (∑ᶠ x, (cycleGroupCongr C (pullback.fst p w ≫ p ≫ sY) (by rw [hd]; ring)
      (relativeCycleCap C sY p r α w (k + 1) (fundamentalCycle C (w ≫ sY) (k + 1)))).1 x *
      (properPushforward C
        ((bivariantPullbackZeroScheme p w M σ).subschemeι ≫ pullback.fst p w ≫ p ≫ sY)
        (pullback.fst p w ≫ p ≫ sY) (bivariantPullbackZeroScheme p w M σ).subschemeι rfl d
        (gysinComponentCycleAt C (pullback.fst p w ≫ p ≫ sY) d (bivariantPullbackModule p w M)
          (bivariantPullbackSection p w M σ)
          (firstChernComponentClass C (pullback.fst p w ≫ p ≫ sY) d
            (bivariantPullbackModule p w M)) x)).1 y) =
      ∑ᶠ x : capSupport C (w ≫ sY) (pullback.snd p w) r (baseChangeFamily p w r α) k, m x.1 *
        (properPushforward C
          ((bivariantPullbackZeroScheme p w M σ).subschemeι ≫ pullback.fst p w ≫ p ≫ sY)
          (pullback.fst p w ≫ p ≫ sY) (bivariantPullbackZeroScheme p w M σ).subschemeι rfl d
          (gysinComponentCycleAt C (pullback.fst p w ≫ p ≫ sY) d (bivariantPullbackModule p w M)
            (bivariantPullbackSection p w M σ)
            (firstChernComponentClass C (pullback.fst p w ≫ p ≫ sY) d
              (bivariantPullbackModule p w M)) x.1)).1 y from by
    exact finsum_mul_eq_finsum_subtype_ne_zero _ _]
  rw [← finsum_sub_distrib]
  · exact finsum_congr fun x ↦ by rw [mul_sub]
  · refine hsubfin _ fun x hx ↦ ?_
    obtain ⟨z, hz, -⟩ := exists_apply_ne_zero_of_properPushforward_apply_ne_zero C _ _ _ _ _ _
      (right_ne_zero_of_mul hx)
    rw [← hz, ← coe_support_integralComponentAt, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  · refine hsubfin _ fun x hx ↦ ?_
    obtain ⟨z, hz, hz0⟩ := exists_apply_ne_zero_of_properPushforward_apply_ne_zero C _ _ _ _ _ _
      (right_ne_zero_of_mul hx)
    rw [← hz]
    exact support_gysinComponentCycleAt_subset C _ d _ _ _ x.1 hz0

include hd in
/-- **One component, the section nonzero.** If `σ ≠ 0`, then for every component `Z_x` of
`w^*α ∩ [W]` the pushforward of the divisor of `σ|_{Z_x}` is the pushed-forward Gysin component
cycle of `Z_x`: both are the cycle of the zero scheme of the pullback of `σ` to `Z_x`. -/
theorem capComponentDivisor_eq_gysinComponentCycleAt (hσ : σ ≠ 0)
    (x : capSupport C (w ≫ sY) (pullback.snd p w) r (baseChangeFamily p w r α) k) :
    haveI : AlgebraicGeometry.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M :=
      Stacks.Divisors.isInvertible_presheaf M
    (capComponentDivisor C (w ≫ sY) (pullback.snd p w) r (baseChangeFamily p w r α) M
        (M.presheaf.germ ⊤ (genericPoint W) trivial σ) x).1 =
      (properPushforward C
        ((bivariantPullbackZeroScheme p w M σ).subschemeι ≫ pullback.fst p w ≫ p ≫ sY)
        (pullback.fst p w ≫ p ≫ sY) (bivariantPullbackZeroScheme p w M σ).subschemeι rfl d
        (gysinComponentCycleAt C (pullback.fst p w ≫ p ≫ sY) d (bivariantPullbackModule p w M)
          (bivariantPullbackSection p w M σ)
          (firstChernComponentClass C (pullback.fst p w ≫ p ≫ sY) d
            (bivariantPullbackModule p w M)) x.1)).1 := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M :=
    Stacks.Divisors.isInvertible_presheaf M
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sY)
  set q := pullback.snd p w with hq
  set Z := integralComponentAt x.1 with hZ
  let : IsLocallyNoetherian Z.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (Z.subschemeι ≫ q ≫ w ≫ sY)
  have : IsDominant (Z.subschemeι ≫ q) := x.isDominant
  set b' := AlgebraicGeometry.pullbackGlobalSections (Z.subschemeι ≫ q) M σ with hb'
  have hgerm := Stacks.Chow.germ_genericPoint_pullbackGlobalSections (Z.subschemeι ≫ q) M σ
  have hb'0 : b' ≠ 0 := by
    intro h0
    have h1 := Stacks.Divisors.genericStalkPullback_ne_zero (Z.subschemeι ≫ q)
      (Stacks.Divisors.isTrivializedNear_of_isInvertible M)
      (Stacks.ChernCap42.germ_ne_zero_of_ne_zero M σ hσ (genericPoint W))
    rw [← hgerm, ← hb', h0, map_zero] at h1
    exact h1 rfl
  -- the divisor of the pulled-back section is the cycle of its zero scheme (Stacks 02SK)
  have hdiv := Stacks.Chow.cycleAssociatedToZeroScheme_eq_meromorphicDivisorCycle C
    (Z.subschemeι ≫ q ≫ w ≫ sY) ((r : ℤ) + k + 1) x.schemeDeltaDimension_eq
    ((Scheme.Modules.pullback (Z.subschemeι ≫ q)).obj M) b' hb'0
    (fun z ↦ (Stacks.Divisors.isTrivializedNear_of_isInvertible M
      ((Z.subschemeι ≫ q).base z)).pullback)
  replace hdiv := congrArg Subtype.val hdiv
  rw [val_meromorphicDivisorCycle_eq_chernComponentCycle] at hdiv
  -- the Gysin side
  have hx' : relativeDimension C.dimensionFunction (pullback.fst p w ≫ p ≫ sY) x.1 = d + 1 := by
    rw [pullbackFst_comp_eq w rfl, x.relativeDimension_eq, hd]
  have hEσ : bivariantPullbackZeroScheme p w M σ = (Stacks.Divisors.zeroScheme W M σ).comap q :=
    Stacks.Divisors.zeroScheme_pullback q M σ
  have hle : ¬ bivariantPullbackZeroScheme p w M σ ≤ Z := by
    rw [hZ, le_integralComponentAt_iff_mem_support, hEσ, Scheme.IdealSheafData.support_comap]
    change q.base x.1 ∉ ((Stacks.Divisors.zeroScheme W M σ).support : Set W)
    rw [x.base_eq, ← Scheme.IdealSheafData.range_subschemeι]
    exact Stacks.ChernCap42.genericPoint_notMem_range_subschemeι_zeroScheme M σ hσ
  rw [gysinComponentCycleAt_eq C _ d _ _ _ hx', gysinComponentCycle_of_not_le C _ d _ _ _ _ _ _ hle,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
  change _ = (cycleAssociatedToClosedSubscheme C (pullback.fst p w ≫ p ≫ sY)
    ((Z.comap (bivariantPullbackZeroScheme p w M σ).subschemeι).subschemeι ≫
      (bivariantPullbackZeroScheme p w M σ).subschemeι) d).1
  rw [cycleAssociatedToClosedSubscheme_comap_zeroScheme C _ (bivariantPullbackModule p w M)
    (bivariantPullbackSection p w M σ) Z d]
  -- the two zero schemes on `Z` are one closed subscheme
  have hZZ : Stacks.Divisors.zeroScheme Z.subscheme
      ((Scheme.Modules.pullback Z.subschemeι).obj (bivariantPullbackModule p w M))
      (AlgebraicGeometry.pullbackGlobalSections Z.subschemeι (bivariantPullbackModule p w M)
        (bivariantPullbackSection p w M σ)) =
      Stacks.Divisors.zeroScheme Z.subscheme ((Scheme.Modules.pullback (Z.subschemeι ≫ q)).obj M)
        b' := by
    rw [Stacks.Divisors.zeroScheme_pullback, hb', Stacks.Divisors.zeroScheme_pullback]
    rw [Stacks.Divisors.zeroScheme_pullback, ← Scheme.IdealSheafData.comap_comp]
  rw [cycleAssociatedToClosedSubscheme_subschemeι_comp_congr C _ Z.subschemeι hZZ d]
  unfold capComponentDivisor
  rw [← hgerm]
  refine (val_properPushforward_eq_of_val_eq C _ _ _ _ _ _ hdiv.symm).trans ?_
  rw [properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
  exact cycleAssociatedToClosedSubscheme_val_congr C (pullbackFst_comp_eq w rfl).symm _ (by
    rw [hd]; ring)

/-- **One component, the section zero.** If `σ = 0`, then for every component `Z_x` of
`w^*α ∩ [W]` and every nonzero meromorphic section `t` of `M`, the pushforward of the divisor of
`t|_{Z_x}` and the pushed-forward Gysin component cycle of `Z_x` are rationally equivalent inside
`Z_x`: both are first Chern classes of the restriction of `M` to `Z_x` capped with `[Z_x]`. -/
theorem capComponentDivisor_sub_gysinComponentCycleAt (hσ : σ = 0)
    (t : M.presheaf.stalk (genericPoint W)) (ht : t ≠ 0)
    (x : capSupport C (w ≫ sY) (pullback.snd p w) r (baseChangeFamily p w r α) k) :
    haveI : AlgebraicGeometry.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M :=
      Stacks.Divisors.isInvertible_presheaf M
    IsRationallyEquivalentToZeroWithin C (pullback.fst p w ≫ p ≫ sY) d
      (cycleGroupCongr C _ hd.symm (cycleGroupOfMorphismEq C
          (pullbackFst_comp_eq w rfl).symm (capComponentDivisor C (w ≫ sY) (pullback.snd p w) r
            (baseChangeFamily p w r α) M t x)) -
        properPushforward C
          ((bivariantPullbackZeroScheme p w M σ).subschemeι ≫ pullback.fst p w ≫ p ≫ sY)
          (pullback.fst p w ≫ p ≫ sY) (bivariantPullbackZeroScheme p w M σ).subschemeι rfl d
          (gysinComponentCycleAt C (pullback.fst p w ≫ p ≫ sY) d (bivariantPullbackModule p w M)
            (bivariantPullbackSection p w M σ)
            (firstChernComponentClass C (pullback.fst p w ≫ p ≫ sY) d
              (bivariantPullbackModule p w M)) x.1))
      (closure {x.1}) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M :=
    Stacks.Divisors.isInvertible_presheaf M
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sY)
  subst hσ
  set q := pullback.snd p w with hq
  set Z := integralComponentAt x.1 with hZ
  let : IsLocallyNoetherian Z.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (Z.subschemeι ≫ q ≫ w ≫ sY)
  have : IsDominant (Z.subschemeι ≫ q) := x.isDominant
  have hx' : relativeDimension C.dimensionFunction (pullback.fst p w ≫ p ≫ sY) x.1 = d + 1 := by
    rw [pullbackFst_comp_eq w rfl, x.relativeDimension_eq, hd]
  have hdZ := schemeDeltaDimension_integralComponentAt_of_eq C (pullback.fst p w ≫ p ≫ sY) hx'
  have hle : bivariantPullbackZeroScheme p w M 0 ≤ Z := by
    rw [bivariantPullbackZeroScheme, bivariantPullbackSection, map_zero,
      Stacks.Divisors.zeroScheme_zero_eq_bot]
    exact bot_le
  rw [gysinComponentCycleAt_eq C _ d _ _ _ hx', 
    properPushforward_zeroScheme_gysinComponentCycle_of_le C _ d _ _ _ _ _ _ hle]
  -- the first Chern class of the restriction, through the pulled-back section
  set tx := Stacks.Divisors.genericStalkPullback (Z.subschemeι ≫ q) M t with htx
  have htx0 : tx ≠ 0 := Stacks.Divisors.genericStalkPullback_ne_zero (Z.subschemeι ≫ q)
    (Stacks.Divisors.isTrivializedNear_of_isInvertible M) ht
  have : AlgebraicGeometry.SheafOfModules.IsInvertible Z.subscheme.presheaf
      Z.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback Z.subschemeι).obj (bivariantPullbackModule p w M)) :=
    isInvertible_presheaf_modulePullback _ Z.subschemeι
  obtain ⟨s₀, hs₀⟩ := Stacks.Divisors.exists_ne_zero_genericStalk_of_isInvertible
    ((Scheme.Modules.pullback Z.subschemeι).obj (bivariantPullbackModule p w M))
  have hcls : (QuotientAddGroup.mk (Quotient.out (firstChernComponentClass C
        (pullback.fst p w ≫ p ≫ sY) d (bivariantPullbackModule p w M) Z inferInstance hdZ)) :
        chowGroup C (Z.subschemeι ≫ pullback.fst p w ≫ p ≫ sY) d) =
      QuotientAddGroup.mk (chernComponentCycle C (Z.subschemeι ≫ pullback.fst p w ≫ p ≫ sY) hdZ
        (fun z ↦ (Stacks.Divisors.isTrivializedNear_of_isInvertible M
          ((Z.subschemeι ≫ q).base z)).pullback) tx) :=
    (Quotient.out_eq _).trans ((firstChernComponentClass_eq_mk_of_ne_zero C _ d _ Z hdZ hs₀).trans
      (mk_chernComponentCycle_eq_of_moduleIso C _ hdZ
        ((Scheme.Modules.pullbackComp Z.subschemeι q).app M) _ _ hs₀ htx0))
  have hre := properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion C
    (Z.subschemeι ≫ pullback.fst p w ≫ p ≫ sY) (pullback.fst p w ≫ p ≫ sY) Z.subschemeι rfl d
    (QuotientAddGroup.eq_iff_sub_mem.1 hcls)
  rw [properPushforward_sub] at hre
  have hneg := isRationallyEquivalentToZeroWithin_neg C _ d (hre.mono (by
    rw [Scheme.IdealSheafData.range_subschemeι, hZ, coe_support_integralComponentAt]))
  rw [neg_sub] at hneg
  convert hneg using 2
  apply Subtype.ext
  unfold capComponentDivisor
  exact properPushforward_val_congr C (by rw [pullbackFst_comp_eq w rfl])
    (pullbackFst_comp_eq w rfl).symm Z.subschemeι rfl rfl _ _
    (chernComponentCycle_val_congr C _ _ _ _ _ _)

/-- **The divisor side, the section nonzero.** If `σ ≠ 0`, the pushforward to `W` of the Gysin
cycle of `[W]` is the divisor of `σ` (Stacks 02SK). -/
theorem properPushforward_gysinRule_fundamentalCycle_of_ne_zero (hσ : σ ≠ 0) :
    haveI : AlgebraicGeometry.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M :=
      Stacks.Divisors.isInvertible_presheaf M
    letI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sY)
    properPushforward C ((Stacks.Divisors.zeroScheme W M σ).subschemeι ≫ w ≫ sY) (w ≫ sY)
        (Stacks.Divisors.zeroScheme W M σ).subschemeι rfl k
        ((gysinRule C (w ≫ sY) k M σ (firstChernComponentClass C (w ≫ sY) k M)).extendCycleGroup
          (fundamentalCycle C (w ≫ sY) (k + 1))) =
      chernComponentCycle C (w ≫ sY) hW (Stacks.Divisors.isTrivializedNear_of_isInvertible M)
        (M.presheaf.germ ⊤ (genericPoint W) trivial σ) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M :=
    Stacks.Divisors.isInvertible_presheaf M
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sY)
  have hle : ¬ Stacks.Divisors.zeroScheme W M σ ≤ integralComponentAt (genericPoint W) := by
    rw [le_integralComponentAt_iff_mem_support, ← Scheme.IdealSheafData.range_subschemeι]
    exact Stacks.ChernCap42.genericPoint_notMem_range_subschemeι_zeroScheme M σ hσ
  rw [gysinRule_extendCycleGroup_fundamentalCycle C (w ≫ sY) k hW M σ,
    gysinComponentCycle_of_not_le C (w ≫ sY) k M σ _ _ _ _ hle,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
  apply Subtype.ext
  rw [show (cycleAssociatedToClosedSubscheme C (w ≫ sY)
      (((integralComponentAt (genericPoint W)).comap
        (Stacks.Divisors.zeroScheme W M σ).subschemeι).subschemeι ≫
        (Stacks.Divisors.zeroScheme W M σ).subschemeι) k) =
      cycleAssociatedToClosedSubscheme C (w ≫ sY) (Stacks.Divisors.zeroScheme W M σ).subschemeι k
      from by
    rw [cycleAssociatedToClosedSubscheme_subschemeι_comp_congr C (w ≫ sY)
      (Stacks.Divisors.zeroScheme W M σ).subschemeι (by
        rw [integralComponentAt_genericPoint_eq_bot W, Scheme.IdealSheafData.comap_bot]) k]
    exact cycleAssociatedToClosedSubscheme_eq_of_iso C (w ≫ sY)
      ((⊥ : (Stacks.Divisors.zeroScheme W M σ).subscheme.IdealSheafData).subschemeι ≫
        (Stacks.Divisors.zeroScheme W M σ).subschemeι) (Stacks.Divisors.zeroScheme W M σ).subschemeι
      (asIso (⊥ : (Stacks.Divisors.zeroScheme W M σ).subscheme.IdealSheafData).subschemeι) rfl k]
  rw [cycleAssociatedToClosedSubscheme_val_congr C rfl _ (by ring : k = k + 1 - 1),
    Stacks.Chow.cycleAssociatedToZeroScheme_eq_meromorphicDivisorCycle C (w ≫ sY) (k + 1) hW M σ hσ
      (Stacks.Divisors.isTrivializedNear_of_isInvertible M)]
  exact val_meromorphicDivisorCycle_eq_chernComponentCycle C (w ≫ sY) hW _ _

/-- **The divisor side, the section zero.** If `σ = 0`, the pushforward to `W` of the Gysin cycle
of `[W]` is rationally equivalent to the divisor of every nonzero meromorphic section of `M`: it is
a representative of `c₁(M) ∩ [W]`. -/
theorem properPushforward_gysinRule_fundamentalCycle_of_eq_zero (hσ : σ = 0)
    (t : M.presheaf.stalk (genericPoint W)) (ht : t ≠ 0) :
    haveI : AlgebraicGeometry.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M :=
      Stacks.Divisors.isInvertible_presheaf M
    letI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sY)
    IsRationallyEquivalentToZero C (w ≫ sY) k
      (properPushforward C ((Stacks.Divisors.zeroScheme W M σ).subschemeι ≫ w ≫ sY) (w ≫ sY)
          (Stacks.Divisors.zeroScheme W M σ).subschemeι rfl k
          ((gysinRule C (w ≫ sY) k M σ (firstChernComponentClass C (w ≫ sY) k M)).extendCycleGroup
            (fundamentalCycle C (w ≫ sY) (k + 1))) -
        chernComponentCycle C (w ≫ sY) hW
          (Stacks.Divisors.isTrivializedNear_of_isInvertible M) t) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M :=
    Stacks.Divisors.isInvertible_presheaf M
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sY)
  subst hσ
  set W₀ := integralComponentAt (genericPoint W) with hW₀
  have hdim₀ := schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C (w ≫ sY)
    (genericPoint W) (relativeDimension_genericPoint_of_schemeDeltaDimension C (w ≫ sY) hW)
  have hle : Stacks.Divisors.zeroScheme W M 0 ≤ W₀ := by
    rw [Stacks.Divisors.zeroScheme_zero_eq_bot]; exact bot_le
  have : IsIso W₀.subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).2 (integralComponentAt_genericPoint_eq_bot W)
  rw [gysinRule_extendCycleGroup_fundamentalCycle C (w ≫ sY) k hW M 0,
    properPushforward_zeroScheme_gysinComponentCycle_of_le C (w ≫ sY) k M 0 _ _ _ _ hle]
  have : AlgebraicGeometry.SheafOfModules.IsInvertible W₀.subscheme.presheaf
      W₀.subscheme.ringCatSheaf.2 ((Scheme.Modules.pullback W₀.subschemeι).obj M) :=
    isInvertible_presheaf_modulePullback M W₀.subschemeι
  let : IsLocallyNoetherian W₀.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W₀.subschemeι ≫ w ≫ sY)
  set ε : W ≅ W₀.subscheme := (asIso W₀.subschemeι).symm with hε
  have hει : ε.hom ≫ W₀.subschemeι = 𝟙 W := by simp [hε]
  have h := rationallyEquivalentToZero_properPushforward_sub_chernComponentCycle C (w ≫ sY)
    (W₀.subschemeι ≫ w ≫ sY) ε (by rw [← Category.assoc, hει, Category.id_comp]) k hW hdim₀
    ((Scheme.Modules.pullback W₀.subschemeι).obj M) M
    ((Scheme.Modules.pullbackComp ε.hom W₀.subschemeι).app M ≪≫
      (Scheme.Modules.pullbackCongr hει).app M ≪≫ (Scheme.Modules.pullbackId W).app M) ht
    (Quotient.out (firstChernComponentClass C (w ≫ sY) k M W₀ inferInstance hdim₀))
    (fun t' ht' ↦ (Quotient.out_eq _).trans
      (firstChernComponentClass_eq_mk_of_ne_zero C (w ≫ sY) k M W₀ hdim₀ ht'))
  rwa [properPushforward_congr C _ _ _ _ (show ε.inv = W₀.subschemeι by simp [hε]) _
    (by simp)] at h

end IntegralCase

include hα in
/-- **Stacks 0H6F on one integral test scheme.** For an integral test scheme `w : W ⟶ Y` of
delta-dimension `k + 1`, an invertible module `M` on `W` and `σ ∈ Γ(W, M)`,
`w^*α ∩ i_* i^* [W] - j_* j^*(w^*α ∩ [W])` is rationally equivalent to zero inside the zero
scheme `E` of the pullback of `σ` to `W ×_Y X`. -/
theorem relativeCycleCap_gysin_fundamentalCycle {W : Scheme.{u}} [IsIntegral W] (w : W ⟶ Y)
    [LocallyOfFiniteType w] (k d : ℤ) (hd : d = (r : ℤ) + k)
    (hW : schemeDeltaDimension C (w ≫ sY) = ((k + 1 : ℤ) : EInt)) (M : W.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property M]
    (σ : Γ(M, ⊤)) :
    IsRationallyEquivalentToZeroWithin C (pullback.fst p w ≫ p ≫ sY) d
      (cycleGroupCongr C _ hd.symm (relativeCycleCap C sY p r α w k
          (properPushforward C ((Stacks.Divisors.zeroScheme W M σ).subschemeι ≫ w ≫ sY) (w ≫ sY)
            (Stacks.Divisors.zeroScheme W M σ).subschemeι rfl k
            ((gysinRule C (w ≫ sY) k M σ (firstChernComponentClass C (w ≫ sY) k M)).extendCycleGroup
              (fundamentalCycle C (w ≫ sY) (k + 1))))) -
        properPushforward C
          ((bivariantPullbackZeroScheme p w M σ).subschemeι ≫ pullback.fst p w ≫ p ≫ sY)
          (pullback.fst p w ≫ p ≫ sY) (bivariantPullbackZeroScheme p w M σ).subschemeι rfl d
          ((gysinRule C (pullback.fst p w ≫ p ≫ sY) d (bivariantPullbackModule p w M)
              (bivariantPullbackSection p w M σ)
              (firstChernComponentClass C (pullback.fst p w ≫ p ≫ sY) d
                (bivariantPullbackModule p w M))).extendCycleGroup
            (cycleGroupCongr C _ (by rw [hd]; ring) (relativeCycleCap C sY p r α w (k + 1)
              (fundamentalCycle C (w ≫ sY) (k + 1))))))
      ((bivariantPullbackZeroScheme p w M σ).support : Set ↥(pullback p w)) := by
  classical
  have : AlgebraicGeometry.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M :=
    Stacks.Divisors.isInvertible_presheaf M
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sY)
  set m := (cap C (w ≫ sY) (pullback.snd p w) (baseChangeFamily p w r α)
    (fundamentalCycle C (w ≫ sY) (k + 1))).1 with hm
  by_cases hσ : σ = 0
  · -- the section vanishes: everything is a first Chern class
    obtain ⟨t, ht⟩ := Stacks.Divisors.exists_ne_zero_genericStalk_of_isInvertible M
    have hEσ :
        ((bivariantPullbackZeroScheme p w M σ).support : Set ↥(pullback p w)) = Set.univ := by
      have h0 : bivariantPullbackSection p w M σ = 0 := by
        rw [bivariantPullbackSection, hσ, map_zero]
      rw [bivariantPullbackZeroScheme, h0, Stacks.Divisors.zeroScheme_zero_eq_bot,
        Scheme.IdealSheafData.support_bot]
      rfl
    rw [hEσ]
    set ch := chernComponentCycle C (w ≫ sY) hW
      (Stacks.Divisors.isTrivializedNear_of_isInvertible M) t with hch
    set Dc := properPushforward C ((Stacks.Divisors.zeroScheme W M σ).subschemeι ≫ w ≫ sY)
      (w ≫ sY) (Stacks.Divisors.zeroScheme W M σ).subschemeι rfl k
      ((gysinRule C (w ≫ sY) k M σ (firstChernComponentClass C (w ≫ sY) k M)).extendCycleGroup
        (fundamentalCycle C (w ≫ sY) (k + 1))) with hDc
    have hX₁ := relativeCycleCap_isRationallyEquivalentToZeroWithin C sY p r α hα w k d hd ⊥
      (Dc - ch) ((isRationallyEquivalentToZeroWithin_univ_iff C _ k _).2
        (properPushforward_gysinRule_fundamentalCycle_of_eq_zero C sY w k hW M σ hσ t ht))
    rw [map_sub, map_sub] at hX₁
    have hX₂ := rationallyEquivalentToZeroWithin_finsum C (pullback.fst p w ≫ p ≫ sY) d
      (fun x : capSupport C (w ≫ sY) (pullback.snd p w) r (baseChangeFamily p w r α) k ↦
        m x.1 • (cycleGroupCongr C _ hd.symm (cycleGroupOfMorphismEq C
          (pullbackFst_comp_eq w rfl).symm (capComponentDivisor C (w ≫ sY) (pullback.snd p w) r
            (baseChangeFamily p w r α) M t x)) -
        properPushforward C
          ((bivariantPullbackZeroScheme p w M σ).subschemeι ≫ pullback.fst p w ≫ p ≫ sY)
          (pullback.fst p w ≫ p ≫ sY) (bivariantPullbackZeroScheme p w M σ).subschemeι rfl d
          (gysinComponentCycleAt C (pullback.fst p w ≫ p ≫ sY) d (bivariantPullbackModule p w M)
            (bivariantPullbackSection p w M σ)
            (firstChernComponentClass C (pullback.fst p w ≫ p ≫ sY) d
              (bivariantPullbackModule p w M)) x.1)))
      (fun x ↦ closure {x.1}) (locallyFinite_closure_support m.locallyFiniteSupport)
      (fun x ↦ isRationallyEquivalentToZeroWithin_zsmul C _ d
        (capComponentDivisor_sub_gysinComponentCycleAt C sY p r α w k d hd M σ hσ t ht x) (m x.1)
        fun y ↦ rfl)
      (α := cycleGroupCongr C _ hd.symm (relativeCycleCap C sY p r α w k ch) -
        properPushforward C
          ((bivariantPullbackZeroScheme p w M σ).subschemeι ≫ pullback.fst p w ≫ p ≫ sY)
          (pullback.fst p w ≫ p ≫ sY) (bivariantPullbackZeroScheme p w M σ).subschemeι rfl d
          ((gysinRule C (pullback.fst p w ≫ p ≫ sY) d (bivariantPullbackModule p w M)
              (bivariantPullbackSection p w M σ)
              (firstChernComponentClass C (pullback.fst p w ≫ p ≫ sY) d
                (bivariantPullbackModule p w M))).extendCycleGroup
            (cycleGroupCongr C _ (by rw [hd]; ring) (relativeCycleCap C sY p r α w (k + 1)
              (fundamentalCycle C (w ≫ sY) (k + 1))))))
      (fun y ↦ by
        rw [AddSubgroupClass.coe_sub, Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply,
          relativeCycleCap_chernComponentCycle_sub_gysin_apply C sY p r α hα w k d hd hW M σ t ht y]
        rfl)
    have := isRationallyEquivalentToZeroWithin_add C _ d (hX₁.mono (Set.subset_univ _))
      (hX₂.mono (Set.subset_univ _))
    rwa [sub_add_sub_cancel] at this
  · -- the section does not vanish: the two sides agree on the nose
    have ht := Stacks.ChernCap42.germ_ne_zero_of_ne_zero M σ hσ (genericPoint W)
    rw [properPushforward_gysinRule_fundamentalCycle_of_ne_zero C sY w k hW M σ hσ]
    have hzero : cycleGroupCongr C _ hd.symm (relativeCycleCap C sY p r α w k
          (chernComponentCycle C (w ≫ sY) hW (Stacks.Divisors.isTrivializedNear_of_isInvertible M)
            (M.presheaf.germ ⊤ (genericPoint W) trivial σ))) -
        properPushforward C
          ((bivariantPullbackZeroScheme p w M σ).subschemeι ≫ pullback.fst p w ≫ p ≫ sY)
          (pullback.fst p w ≫ p ≫ sY) (bivariantPullbackZeroScheme p w M σ).subschemeι rfl d
          ((gysinRule C (pullback.fst p w ≫ p ≫ sY) d (bivariantPullbackModule p w M)
              (bivariantPullbackSection p w M σ)
              (firstChernComponentClass C (pullback.fst p w ≫ p ≫ sY) d
                (bivariantPullbackModule p w M))).extendCycleGroup
            (cycleGroupCongr C _ (by rw [hd]; ring) (relativeCycleCap C sY p r α w (k + 1)
              (fundamentalCycle C (w ≫ sY) (k + 1))))) = 0 := by
      refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
      rw [AddSubgroupClass.coe_sub, Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply,
        relativeCycleCap_chernComponentCycle_sub_gysin_apply C sY p r α hα w k d hd hW M σ _ ht y]
      refine (finsum_eq_zero_of_forall_eq_zero fun x ↦ ?_).trans rfl
      rw [capComponentDivisor_eq_gysinComponentCycleAt C sY p r α w k d hd M σ hσ x, sub_self,
        mul_zero]
    rw [hzero]
    exact isRationallyEquivalentToZeroWithin_zero C _ d _

end Stacks.Chow

end
