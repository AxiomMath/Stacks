module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Relative
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Specialization
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.ZeroIdeal
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Relative cycles and closed immersions

Let `S` be a locally Noetherian scheme, let `i : X ⟶ Y` be a closed immersion of schemes locally
of finite type over `S`, let `r ≥ 0` and let `α` be a family of `r`-cycles on the fibres of
`X/S`. Pushing each member of `α` forward along the morphism `i_s : X_s ⟶ Y_s` induced on the
fibres gives a family `i_*α` of `r`-cycles on the fibres of `Y/S`, and the first content of this
file is that `α` is a relative `r`-cycle exactly when `i_*α` is one.

When `i` is moreover a thickening, so that it is surjective on points, each `i_s` is a thickening
too and `i_*` is a bijection on the cycles of every fibre, hence on families of cycles. Combined
with the equivalence just described this identifies the groups `z(X/S, r)` and `z(Y/S, r)` of
relative `r`-cycles, which is the second content of the file.

## Main definitions

* `Stacks.Chow.fiberProperPushforward` — proper pushforward on the cycle group of a single
  fibre, along the morphism of fibres induced by a proper morphism over the base.
* `Stacks.Chow.properPushforwardFamily` — the family `f_*α`, the fibrewise proper pushforward of
  a family of cycles along a proper morphism over the base.
* `Stacks.Chow.fiberProperPushforwardHom`, `Stacks.Chow.fiberProperPushforwardAddEquiv`,
  `Stacks.Chow.properPushforwardFamilyAddEquiv` — pushforward along a closed immersion over the
  base as a homomorphism on the cycles of a fibre, and, for a thickening, as an additive
  equivalence on the cycles of a fibre and on families of such cycles.
* `Stacks.Chow.relativeCyclesAddEquivOfIsThickening` — the additive equivalence
  `z(X/S, r) ≃ z(Y/S, r)` induced by proper pushforward along a thickening.

## Main results

* `Stacks.Chow.isRelativeCycle_iff_isRelativeCycle_properPushforwardFamily` — `α` is a relative
  `r`-cycle on `X/S` if and only if `i_*α` is a relative `r`-cycle on `Y/S`.
* `Stacks.Chow.relativeCyclesAddEquivOfIsThickening_coe` — that equivalence is proper pushforward,
  read on the underlying families of fibrewise cycles.
* `Stacks.Chow.baseChangeFamily_properPushforwardFamily` — for a closed immersion, the pushforward
  of a family of cycles commutes with base change of the base.
* `Stacks.Chow.specializationCycle_properPushforwardFamily` — for a closed immersion,
  specialization of cycles over a discrete valuation ring commutes with pushforward.
* `Stacks.Chow.fiberProperPushforward_injective` — pushforward along a closed immersion is
  injective on each fibrewise cycle group.
* `Stacks.Chow.properPushforward_injective_of_isClosedImmersion`,
  `Stacks.Chow.properPushforward_bijective_of_surjective` — for an arbitrary base situation,
  pushforward of `k`-cycles along a closed immersion is injective, and bijective as soon as the
  immersion is surjective on points.
* `AlgebraicGeometry.Scheme.IdealSheafData.comap_map_of_isPullback` — pushing an ideal sheaf
  forward along a closed immersion commutes with pulling it back along a base change of that
  immersion.

## References

* [Stacks Project, Tag 0H54](https://stacks.math.columbia.edu/tag/0H54)
* [Stacks Project, Tag 0H5E](https://stacks.math.columbia.edu/tag/0H5E)
* [Stacks Project, Tag 0H4P](https://stacks.math.columbia.edu/tag/0H4P)
* [Stacks Project, Tag 0H4M](https://stacks.math.columbia.edu/tag/0H4M)
* [Stacks Project, Tag 0H50](https://stacks.math.columbia.edu/tag/0H50)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-! ### Pushforward and pullback of an ideal sheaf across a base change square -/

/-- **Pushforward along a closed immersion commutes with base change.** Let `i : X ⟶ Y` be a closed
immersion and let the square formed by `j' : X₀ ⟶ X`, `i₀ : X₀ ⟶ Y₀`, `i` and `j : Y₀ ⟶ Y` be a
pullback square, so that `i₀` is the base change of `i` along `j`. Then for every quasi-coherent
ideal sheaf `I` on `X` the closed subscheme of `Y₀` obtained by reading `I` in `Y` and pulling back
along `j` is the one obtained by pulling `I` back along `j'` and reading the result in `Y₀`. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.comap_map_of_isPullback
    {X Y X₀ Y₀ : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] {j' : X₀ ⟶ X} {i₀ : X₀ ⟶ Y₀}
    {j : Y₀ ⟶ Y} (h : IsPullback j' i₀ i j) (I : X.IdealSheafData) :
    (I.map i).comap j = (I.comap j').map i₀ := by
  have hsq : IsPullback (pullback.fst j' I.subschemeι) (pullback.snd j' I.subschemeι) j'
      I.subschemeι := IsPullback.of_hasPullback _ _
  have hpaste : IsPullback (pullback.fst j' I.subschemeι ≫ i₀)
      (pullback.snd j' I.subschemeι) j (I.subschemeι ≫ i) := (hsq.flip.paste_vert h).flip
  rw [Scheme.IdealSheafData.map, ← AlgebraicGeometry.ker_eq_comap_ker_of_isPullback hpaste,
    Scheme.Hom.ker_comp, AlgebraicGeometry.ker_eq_comap_ker_of_isPullback hsq,
    Scheme.IdealSheafData.ker_subschemeι]

namespace Stacks.Chow

/-- The cycle of the closed subscheme cut out by the pushforward of an ideal sheaf along a closed
immersion is the cycle of the composite closed immersion. -/
theorem cycleAssociatedToClosedSubscheme_map (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (i : X ⟶ Y) [IsClosedImmersion i]
    (I : X.IdealSheafData) (k : ℤ) :
    cycleAssociatedToClosedSubscheme C sY (I.subschemeι ≫ i) k =
      cycleAssociatedToClosedSubscheme C sY (I.map i).subschemeι k :=
  Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦
    closedSubschemeCycleCoeff_eq_of_iso C sY (I.subschemeι ≫ i) (I.map i).subschemeι
      (imageIsoOfIsClosedImmersion i I) (imageIsoOfIsClosedImmersion_hom_subschemeι i I) k y)

/-! ### The fibrewise proper pushforward of a family of cycles -/

section ProperPushforwardFamily

variable {X Y S : Scheme.{u}} (sX : X ⟶ S) [LocallyOfFiniteType sX] (sY : Y ⟶ S)
  [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX)

/-- Proper pushforward on the cycle group of the fibre over `s`, along the morphism `f_s` induced
on the fibres by a proper morphism `f` over the base. -/
def fiberProperPushforward (s : S) (r : ℕ) :
    FiberCycleGroup sX s r → FiberCycleGroup sY s r :=
  properPushforward (fieldChowSituation (S.residueField s)) (sX.fiberToSpecResidueField s)
    (sY.fiberToSpecResidueField s) (inducedFiberMap sX sY f hf s)
    (inducedFiberMap_fiberToSpecResidueField sX sY f hf s) (r : ℤ)

/-- **The pushforward `f_*α` of a family of cycles on fibres.** The member over `s` is the proper
pushforward of the member of `α` over `s` along the morphism `f_s : X_s ⟶ Y_s` induced on the
fibres. -/
def properPushforwardFamily (r : ℕ) (α : FamilyOfCycles sX r) : FamilyOfCycles sY r :=
  fun s ↦ fiberProperPushforward sX sY f hf s r (α s)

/-- The member over `s` of `f_*α` is the proper pushforward of the member of `α` over `s`. -/
@[simp]
theorem properPushforwardFamily_apply (r : ℕ) (α : FamilyOfCycles sX r) (s : S) :
    properPushforwardFamily sX sY f hf r α s = fiberProperPushforward sX sY f hf s r (α s) :=
  rfl

end ProperPushforwardFamily

/-! ### Pushforward along a closed immersion -/

section ClosedImmersion

variable {X Y S : Scheme.{u}} (sX : X ⟶ S) [LocallyOfFiniteType sX] (sY : Y ⟶ S)
  [LocallyOfFiniteType sY] (i : X ⟶ Y) [IsClosedImmersion i] (hi : i ≫ sY = sX)

/-- The morphism induced on fibres by a closed immersion over the base is a closed immersion. -/
instance isClosedImmersion_inducedFiberMap (s : S) :
    IsClosedImmersion (inducedFiberMap sX sY i hi s) :=
  MorphismProperty.of_isPullback (isPullback_inducedFiberMap sX sY i hi s) inferInstance

/-- Along a closed immersion the pushforward of a cycle on a fibre has, at the image of a point
of that fibre, the coefficient of the original cycle at that point. -/
theorem fiberProperPushforward_apply_image (s : S) (r : ℕ) (c : FiberCycleGroup sX s r)
    (x : sX.fiber s) :
    (fiberProperPushforward sX sY i hi s r c :
        AlgebraicCycle (sY.fiber s) ℤ) ((inducedFiberMap sX sY i hi s).base x) =
      (c : AlgebraicCycle (sX.fiber s) ℤ) x :=
  properPushforward_apply_image_of_isClosedImmersion _ _ _ _ _ _ c x

/-- Along a closed immersion the pushforward of a cycle on a fibre vanishes away from the image
of that fibre. -/
theorem fiberProperPushforward_apply_of_notMem_range (s : S) (r : ℕ)
    (c : FiberCycleGroup sX s r) {z : sY.fiber s}
    (hz : z ∉ Set.range (inducedFiberMap sX sY i hi s).base) :
    (fiberProperPushforward sX sY i hi s r c : AlgebraicCycle (sY.fiber s) ℤ) z = 0 :=
  properPushforward_apply_of_notMem_range _ _ _ _ _ _ c hz

/-- Proper pushforward along a closed immersion is injective on `k`-cycles. -/
private theorem properPushforward_injective_aux (C : ChowSituation.{u}) {Z X : Scheme.{u}}
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ) (k : ℤ) :
    Function.Injective (properPushforward C sZ sX i hi k) := by
  intro c d hcd
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro z
  rw [← properPushforward_apply_image_of_isClosedImmersion C sZ sX i hi k c z,
    ← properPushforward_apply_image_of_isClosedImmersion C sZ sX i hi k d z, hcd]

/-- Pushforward along a closed immersion over the base is injective on the cycles of a fibre. -/
theorem fiberProperPushforward_injective (s : S) (r : ℕ) :
    Function.Injective (fiberProperPushforward sX sY i hi s r) :=
  properPushforward_injective_aux _ _ _ _ _ _

/-- **The cycle of a closed subscheme of a fibre pushes forward to the cycle of its image.**
Along a closed immersion over the base, the pushforward of the `r`-cycle of a closed subscheme
`W` of `X_s` is the `r`-cycle of the closed subscheme of `Y_s` cut out by the pushforward of the
ideal sheaf of `W`. -/
theorem fiberProperPushforward_fiberSubschemeCycle (s : S) (r : ℕ)
    (W : (sX.fiber s).IdealSheafData) :
    fiberProperPushforward sX sY i hi s r (fiberSubschemeCycle sX s r W) =
      fiberSubschemeCycle sY s r (W.map (inducedFiberMap sX sY i hi s)) := by
  unfold fiberProperPushforward fiberSubschemeCycle
  rw [properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp,
    cycleAssociatedToClosedSubscheme_map]

end ClosedImmersion

/-! ### A reindexing of locally finite sums -/

/-- A locally finite sum of a family supported on the range of an injection is the locally finite
sum of the family read along that injection. -/
private theorem finsum_comp_of_support_subset_range {A B M : Type*} [AddCommMonoid M]
    {φ : A → B} (hφ : Function.Injective φ) (F : B → M)
    (hsupp : Function.support F ⊆ Set.range φ) : (∑ᶠ b, F b) = ∑ᶠ a, F (φ a) := by
  rw [← finsum_mem_range hφ, finsum_mem_def, Set.indicator_eq_self.2 hsupp]

/-! ### Specialization commutes with pushforward along a closed immersion -/

section Specialization

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {X Y : Scheme.{u}}
  (sX : X ⟶ Spec (.of R)) [LocallyOfFiniteType sX] (sY : Y ⟶ Spec (.of R))
  [LocallyOfFiniteType sY] (i : X ⟶ Y) [IsClosedImmersion i] (hi : i ≫ sY = sX) (r : ℕ)

omit [IsDiscreteValuationRing R] [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
  [IsClosedImmersion i] in
/-- The scheme-theoretic image in `Y` of the reduced closure of the image of a point of the
generic fibre of `X` is the image in `Y` of the scheme-theoretic image in `X`. -/
theorem specializationClosure_inducedFiberMap
    (ξ : sX.fiber (genericPoint (Spec (.of R)))) :
    specializationClosure sY
        ((inducedFiberMap sX sY i hi (genericPoint (Spec (.of R)))).base ξ) =
      (specializationClosure sX ξ).map i := by
  rw [specializationClosure, specializationClosure, ← map_integralComponentAt,
    ← Scheme.IdealSheafData.map_comp, ← Scheme.IdealSheafData.map_comp,
    inducedFiberMap_fiberι]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] in
/-- The special fibre of the scheme-theoretic image of the reduced closure of the image of a
point of the generic fibre is the image, under the morphism induced on closed fibres, of the
special fibre on the `X` side. -/
theorem specializationSpecialFibre_inducedFiberMap
    (ξ : sX.fiber (genericPoint (Spec (.of R)))) :
    specializationSpecialFibre sY
        ((inducedFiberMap sX sY i hi (genericPoint (Spec (.of R)))).base ξ) =
      (specializationSpecialFibre sX ξ).map
        (inducedFiberMap sX sY i hi (IsLocalRing.closedPoint R)) := by
  rw [specializationSpecialFibre, specializationSpecialFibre,
    specializationClosure_inducedFiberMap sX sY i hi ξ,
    Scheme.IdealSheafData.comap_map_of_isPullback i
      (isPullback_inducedFiberMap sX sY i hi (IsLocalRing.closedPoint R))]

/-- **The specialization of a fundamental cycle commutes with pushforward along a closed
immersion.** The specialization of the fundamental cycle of the reduced closure of the image of
`ξ` is the pushforward of the specialization of the fundamental cycle of the reduced closure
of `ξ`. -/
theorem specializationIntegralCycle_inducedFiberMap
    (ξ : sX.fiber (genericPoint (Spec (.of R)))) :
    specializationIntegralCycle sY r
        ((inducedFiberMap sX sY i hi (genericPoint (Spec (.of R)))).base ξ) =
      fiberProperPushforward sX sY i hi (IsLocalRing.closedPoint R) r
        (specializationIntegralCycle sX r ξ) := by
  change fiberSubschemeCycle sY (IsLocalRing.closedPoint R) r
      (specializationSpecialFibre sY
        ((inducedFiberMap sX sY i hi (genericPoint (Spec (.of R)))).base ξ)) =
    fiberProperPushforward sX sY i hi (IsLocalRing.closedPoint R) r
      (fiberSubschemeCycle sX (IsLocalRing.closedPoint R) r (specializationSpecialFibre sX ξ))
  rw [fiberProperPushforward_fiberSubschemeCycle sX sY i hi (IsLocalRing.closedPoint R) r
    (specializationSpecialFibre sX ξ), specializationSpecialFibre_inducedFiberMap sX sY i hi ξ]

/-- Specialization of cycles over a discrete valuation ring commutes with pushforward along a
closed immersion over that ring: pushing the specialization of a cycle on the generic fibre forward
along the morphism of closed fibres gives the specialization of its pushforward along the morphism
of generic fibres. -/
@[stacks 0H4M "specialization commutes with pushforward along a closed immersion"]
theorem specializationCycle_properPushforwardFamily
    (c : FiberCycleGroup sX (genericPoint (Spec (.of R))) r) :
    fiberProperPushforward sX sY i hi (IsLocalRing.closedPoint R) r (specializationCycle sX r c) =
      specializationCycle sY r
        (fiberProperPushforward sX sY i hi (genericPoint (Spec (.of R))) r c) := by
  classical
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro z
  have hsupp : (Function.support fun ζ : sY.fiber (genericPoint (Spec (.of R))) ↦
      (fiberProperPushforward sX sY i hi (genericPoint (Spec (.of R))) r c :
          AlgebraicCycle (sY.fiber (genericPoint (Spec (.of R)))) ℤ) ζ *
        (specializationIntegralCycle sY r ζ).1 z) ⊆
      Set.range (inducedFiberMap sX sY i hi (genericPoint (Spec (.of R)))).base := by
    intro ζ hζ
    by_contra hmem
    refine hζ ?_
    have h0 := fiberProperPushforward_apply_of_notMem_range sX sY i hi
      (genericPoint (Spec (.of R))) r c hmem
    simp only [h0, zero_mul]
  have hre := finsum_comp_of_support_subset_range
    (inducedFiberMap sX sY i hi (genericPoint (Spec (.of R)))).isClosedEmbedding.injective
    (fun ζ : sY.fiber (genericPoint (Spec (.of R))) ↦
      (fiberProperPushforward sX sY i hi (genericPoint (Spec (.of R))) r c :
          AlgebraicCycle (sY.fiber (genericPoint (Spec (.of R)))) ℤ) ζ *
        (specializationIntegralCycle sY r ζ).1 z) hsupp
  have hval : ∀ ξ : sX.fiber (genericPoint (Spec (.of R))),
      (fiberProperPushforward sX sY i hi (genericPoint (Spec (.of R))) r c :
            AlgebraicCycle (sY.fiber (genericPoint (Spec (.of R)))) ℤ)
            ((inducedFiberMap sX sY i hi (genericPoint (Spec (.of R)))).base ξ) *
          (specializationIntegralCycle sY r
            ((inducedFiberMap sX sY i hi (genericPoint (Spec (.of R)))).base ξ)).1 z =
        (c : AlgebraicCycle (sX.fiber (genericPoint (Spec (.of R)))) ℤ) ξ *
          (fiberProperPushforward sX sY i hi (IsLocalRing.closedPoint R) r
            (specializationIntegralCycle sX r ξ)).1 z := fun ξ ↦ by
    rw [fiberProperPushforward_apply_image sX sY i hi _ r c ξ,
      specializationIntegralCycle_inducedFiberMap sX sY i hi r ξ]
  rw [specializationCycle_apply, hre, finsum_congr hval]
  by_cases hz : z ∈ Set.range (inducedFiberMap sX sY i hi (IsLocalRing.closedPoint R)).base
  · obtain ⟨x, rfl⟩ := hz
    rw [fiberProperPushforward_apply_image sX sY i hi _ r _ x, specializationCycle_apply]
    exact finsum_congr fun ξ ↦ by
      rw [fiberProperPushforward_apply_image sX sY i hi _ r _ x]
  · rw [fiberProperPushforward_apply_of_notMem_range sX sY i hi _ r _ hz]
    refine ((finsum_congr fun ξ ↦ ?_).trans finsum_zero).symm
    rw [fiberProperPushforward_apply_of_notMem_range sX sY i hi _ r _ hz, mul_zero]

end Specialization

/-! ### Pushforward along a closed immersion commutes with base change -/

section BaseChange

variable {X Y S S' : Scheme.{u}} (sX : X ⟶ S) [LocallyOfFiniteType sX] (sY : Y ⟶ S)
  [LocallyOfFiniteType sY] (i : X ⟶ Y) [IsClosedImmersion i] (hi : i ≫ sY = sX) (g : S' ⟶ S)

/-- The base change along `g : S' ⟶ S` of a morphism `i : X ⟶ Y` over `S`. -/
def baseChangeMap : pullback sX g ⟶ pullback sY g :=
  pullback.map sX g sY g i (𝟙 S') (𝟙 S) (by simp [← hi]) (by simp)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [IsClosedImmersion i] in
/-- The base change of `i` followed by the first projection to `Y` is the first projection to `X`
followed by `i`. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_fst :
    baseChangeMap sX sY i hi g ≫ pullback.fst sY g = pullback.fst sX g ≫ i :=
  pullback.lift_fst _ _ _

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [IsClosedImmersion i] in
/-- The base change of `i` commutes with the second projections to `S'`. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_snd :
    baseChangeMap sX sY i hi g ≫ pullback.snd sY g = pullback.snd sX g := by
  rw [baseChangeMap, pullback.lift_snd, Category.comp_id]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [IsClosedImmersion i] in
/-- The base change of `i` along `g` sits in a pullback square with `i` and the two projections
to `X` and `Y`. -/
theorem isPullback_baseChangeMap :
    IsPullback (pullback.fst sX g) (baseChangeMap sX sY i hi g) i (pullback.fst sY g) :=
  (IsPullback.paste_vert_iff (IsPullback.of_hasPullback sY g)
      (baseChangeMap_fst sX sY i hi g).symm).mp
    (by
      rw [baseChangeMap_snd, hi]
      exact IsPullback.of_hasPullback sX g)

/-- The base change of a closed immersion is a closed immersion. -/
instance isClosedImmersion_baseChangeMap :
    IsClosedImmersion (baseChangeMap sX sY i hi g) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeMap sX sY i hi g) inferInstance

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [IsClosedImmersion i] in
/-- The morphism induced on fibres by the base change of `i` is compatible with the canonical
morphisms from the fibres of a base change to the fibres over the image point. -/
theorem restrictedFiberMap_comp_inducedFiberMap (t : S') :
    restrictedFiberMap sX (pullback.snd sX g) (pullback.fst sX g) g pullback.condition t ≫
        inducedFiberMap sX sY i hi (g t) =
      inducedFiberMap (pullback.snd sX g) (pullback.snd sY g) (baseChangeMap sX sY i hi g)
          (baseChangeMap_snd sX sY i hi g) t ≫
        restrictedFiberMap sY (pullback.snd sY g) (pullback.fst sY g) g pullback.condition t := by
  have hX : restrictedFiberMap sX (pullback.snd sX g) (pullback.fst sX g) g
        pullback.condition t ≫ sX.fiberι (g t) =
      (pullback.snd sX g).fiberι t ≫ pullback.fst sX g :=
    restrictedFiberMap_fiberι sX (pullback.snd sX g) (pullback.fst sX g) g pullback.condition t
  have hY : restrictedFiberMap sY (pullback.snd sY g) (pullback.fst sY g) g
        pullback.condition t ≫ sY.fiberι (g t) =
      (pullback.snd sY g).fiberι t ≫ pullback.fst sY g :=
    restrictedFiberMap_fiberι sY (pullback.snd sY g) (pullback.fst sY g) g pullback.condition t
  refine (IsPullback.of_hasPullback sY (S.fromSpecResidueField (g t))).hom_ext ?_ ?_
  · change _ ≫ sY.fiberι (g t) = _ ≫ sY.fiberι (g t)
    conv_lhs => rw [Category.assoc, inducedFiberMap_fiberι, ← Category.assoc, hX]
    conv_rhs => rw [Category.assoc, hY, ← Category.assoc, inducedFiberMap_fiberι,
      Category.assoc, baseChangeMap_fst]
    rw [Category.assoc]
  · change _ ≫ sY.fiberToSpecResidueField (g t) = _ ≫ sY.fiberToSpecResidueField (g t)
    conv_lhs => rw [Category.assoc, inducedFiberMap_fiberToSpecResidueField,
      restrictedFiberMap_comp_fiberToSpecResidueField]
    conv_rhs => rw [Category.assoc, restrictedFiberMap_comp_fiberToSpecResidueField,
      ← Category.assoc, inducedFiberMap_fiberToSpecResidueField]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [IsClosedImmersion i] in
/-- The fibre over `t` of the base change of `i` is the base change of the fibre of `i` over
`g t`: the square of the two morphisms of fibres and the two canonical morphisms to the fibres
over `g t` is a pullback square. -/
theorem isPullback_inducedFiberMap_baseChangeMap (t : S') :
    IsPullback
      (restrictedFiberMap sX (pullback.snd sX g) (pullback.fst sX g) g pullback.condition t)
      (inducedFiberMap (pullback.snd sX g) (pullback.snd sY g) (baseChangeMap sX sY i hi g)
        (baseChangeMap_snd sX sY i hi g) t)
      (inducedFiberMap sX sY i hi (g t))
      (restrictedFiberMap sY (pullback.snd sY g) (pullback.fst sY g) g pullback.condition t) :=
  (IsPullback.paste_vert_iff (isPullback_restrictedFiberMap_baseChange sY g t)
      (restrictedFiberMap_comp_inducedFiberMap sX sY i hi g t)).mp
    (by
      rw [inducedFiberMap_fiberToSpecResidueField, inducedFiberMap_fiberToSpecResidueField]
      exact isPullback_restrictedFiberMap_baseChange sX g t)

/-- The coefficient of a base-changed family, with the multiplicity written as a coefficient of
the cycle of a closed subscheme. -/
private theorem baseChangeFamily_apply_cycleAssociated {Z : Scheme.{u}} (sZ : Z ⟶ S)
    [LocallyOfFiniteType sZ] (r : ℕ) (α : FamilyOfCycles sZ r) (t : S')
    (x : (pullback.snd sZ g).fiber t) :
    (baseChangeFamily sZ g r α t : AlgebraicCycle ((pullback.snd sZ g).fiber t) ℤ) x =
      (α (g t) : AlgebraicCycle (sZ.fiber (g t)) ℤ)
          (restrictedFiberMap sZ (pullback.snd sZ g) (pullback.fst sZ g) g
            pullback.condition t x) *
        (cycleAssociatedToClosedSubscheme (fieldChowSituation (S'.residueField t))
          ((pullback.snd sZ g).fiberToSpecResidueField t)
          ((integralComponentAt (restrictedFiberMap sZ (pullback.snd sZ g) (pullback.fst sZ g) g
            pullback.condition t x)).comap
            (restrictedFiberMap sZ (pullback.snd sZ g) (pullback.fst sZ g) g
              pullback.condition t)).subschemeι (r : ℤ)).1 x :=
  rfl

/-- The cycle of the inverse image of the reduced closure of the image of a point of the fibre
of `X` over `g t` is the pushforward, along the morphism of fibres over `t`, of the cycle of the
inverse image of the reduced closure of that point. -/
private theorem cycleAssociated_comap_integralComponentAt_inducedFiberMap (r : ℕ) (t : S')
    (w : sX.fiber (g t)) :
    cycleAssociatedToClosedSubscheme (fieldChowSituation (S'.residueField t))
        ((pullback.snd sY g).fiberToSpecResidueField t)
        ((integralComponentAt ((inducedFiberMap sX sY i hi (g t)).base w)).comap
          (restrictedFiberMap sY (pullback.snd sY g) (pullback.fst sY g) g
            pullback.condition t)).subschemeι (r : ℤ) =
      properPushforward (fieldChowSituation (S'.residueField t))
        ((pullback.snd sX g).fiberToSpecResidueField t)
        ((pullback.snd sY g).fiberToSpecResidueField t)
        (inducedFiberMap (pullback.snd sX g) (pullback.snd sY g) (baseChangeMap sX sY i hi g)
          (baseChangeMap_snd sX sY i hi g) t)
        (inducedFiberMap_fiberToSpecResidueField (pullback.snd sX g) (pullback.snd sY g)
          (baseChangeMap sX sY i hi g) (baseChangeMap_snd sX sY i hi g) t) (r : ℤ)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation (S'.residueField t))
          ((pullback.snd sX g).fiberToSpecResidueField t)
          ((integralComponentAt w).comap
            (restrictedFiberMap sX (pullback.snd sX g) (pullback.fst sX g) g
              pullback.condition t)).subschemeι (r : ℤ)) := by
  rw [← map_integralComponentAt, Scheme.IdealSheafData.comap_map_of_isPullback
      (inducedFiberMap sX sY i hi (g t)) (isPullback_inducedFiberMap_baseChangeMap sX sY i hi g t),
    ← cycleAssociatedToClosedSubscheme_map,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]

/-- Pushing a family of cycles forward along a closed immersion over the base commutes with base
change of the base: the base change of `i_*α` is the pushforward of the base change of `α` along
the base change of `i`. -/
theorem baseChangeFamily_properPushforwardFamily (r : ℕ) (α : FamilyOfCycles sX r) :
    baseChangeFamily sY g r (properPushforwardFamily sX sY i hi r α) =
      properPushforwardFamily (pullback.snd sX g) (pullback.snd sY g)
        (baseChangeMap sX sY i hi g) (baseChangeMap_snd sX sY i hi g) r
        (baseChangeFamily sX g r α) := by
  classical
  funext t
  have hcomm : ∀ x : (pullback.snd sX g).fiber t,
      (restrictedFiberMap sY (pullback.snd sY g) (pullback.fst sY g) g
            pullback.condition t).base
          ((inducedFiberMap (pullback.snd sX g) (pullback.snd sY g)
            (baseChangeMap sX sY i hi g) (baseChangeMap_snd sX sY i hi g) t).base x) =
        (inducedFiberMap sX sY i hi (g t)).base
          ((restrictedFiberMap sX (pullback.snd sX g) (pullback.fst sX g) g
            pullback.condition t).base x) := by
    intro x
    have h := congrArg (fun m : (pullback.snd sX g).fiber t ⟶ sY.fiber (g t) ↦ m x)
      (restrictedFiberMap_comp_inducedFiberMap sX sY i hi g t)
    simp only [Scheme.Hom.comp_apply] at h
    exact h.symm
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  rw [baseChangeFamily_apply_cycleAssociated, properPushforwardFamily_apply,
    fiberProperPushforward]
  by_cases hy : y ∈ Set.range (inducedFiberMap (pullback.snd sX g) (pullback.snd sY g)
      (baseChangeMap sX sY i hi g) (baseChangeMap_snd sX sY i hi g) t).base
  · obtain ⟨x, rfl⟩ := hy
    rw [hcomm x, properPushforward_apply_image_of_isClosedImmersion,
      cycleAssociated_comap_integralComponentAt_inducedFiberMap sX sY i hi g r t _,
      properPushforward_apply_image_of_isClosedImmersion, properPushforwardFamily_apply,
      fiberProperPushforward, properPushforward_apply_image_of_isClosedImmersion,
      baseChangeFamily_apply_cycleAssociated]
  · rw [properPushforwardFamily_apply, fiberProperPushforward,
      properPushforward_apply_of_notMem_range _ _ _ _ _ _ _ hy]
    by_cases hw : (restrictedFiberMap sY (pullback.snd sY g) (pullback.fst sY g) g
        pullback.condition t).base y ∈ Set.range (inducedFiberMap sX sY i hi (g t)).base
    · obtain ⟨w, hw⟩ := hw
      rw [← hw, cycleAssociated_comap_integralComponentAt_inducedFiberMap sX sY i hi g r t w,
        properPushforward_apply_of_notMem_range _ _ _ _ _ _ _ hy, mul_zero]
    · rw [properPushforward_apply_of_notMem_range _ _ _ _ _ _ _ hw, zero_mul]

end BaseChange

/-! ### Stacks 0H54 -/

section Main

variable {X Y S : Scheme.{u}} (sX : X ⟶ S) [LocallyOfFiniteType sX] (sY : Y ⟶ S)
  [LocallyOfFiniteType sY] (i : X ⟶ Y) [IsClosedImmersion i] (hi : i ≫ sY = sX) (r : ℕ)

/-- **The valuative condition transfers across pushforward along a closed immersion.** For a single
discrete valuation ring `R` and a single morphism `g : Spec R ⟶ S`, the condition `sp(α_η) = α_0`
on the base change of `α` holds if and only if it holds for the base change of `i_*α`. -/
theorem specializationCycle_baseChangeFamily_properPushforwardFamily_iff
    (α : FamilyOfCycles sX r) (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (g : AlgebraicGeometry.Spec (CommRingCat.of R) ⟶ S) :
    specializationCycle (pullback.snd sX g) r
        (baseChangeFamily sX g r α (genericPoint (AlgebraicGeometry.Spec (CommRingCat.of R)))) =
      baseChangeFamily sX g r α (IsLocalRing.closedPoint R) ↔
    specializationCycle (pullback.snd sY g) r
        (baseChangeFamily sY g r (properPushforwardFamily sX sY i hi r α)
          (genericPoint (AlgebraicGeometry.Spec (CommRingCat.of R)))) =
      baseChangeFamily sY g r (properPushforwardFamily sX sY i hi r α)
        (IsLocalRing.closedPoint R) := by
  rw [baseChangeFamily_properPushforwardFamily sX sY i hi g r α]
  simp only [properPushforwardFamily]
  rw [← specializationCycle_properPushforwardFamily (pullback.snd sX g) (pullback.snd sY g)
      (baseChangeMap sX sY i hi g) (baseChangeMap_snd sX sY i hi g) r _]
  exact (Function.Injective.eq_iff
    (fiberProperPushforward_injective (pullback.snd sX g) (pullback.snd sY g)
      (baseChangeMap sX sY i hi g) (baseChangeMap_snd sX sY i hi g)
      (IsLocalRing.closedPoint R) r)).symm

/-- Let `S` be a locally Noetherian scheme, let `i : X ⟶ Y` be a closed immersion of schemes
locally of finite type over `S`, let `r ≥ 0` and let `α` be a family of `r`-cycles on the fibres of
`X/S`. Then `α` is a relative `r`-cycle on `X/S` if and only if `i_*α` is a relative `r`-cycle on
`Y/S`. -/
@[stacks 0H54]
theorem isRelativeCycle_iff_isRelativeCycle_properPushforwardFamily [IsLocallyNoetherian S]
    (α : FamilyOfCycles sX r) :
    IsRelativeCycle sX r α ↔
      IsRelativeCycle sY r (properPushforwardFamily sX sY i hi r α) :=
  ⟨fun hα R _ _ _ g ↦ (specializationCycle_baseChangeFamily_properPushforwardFamily_iff
      sX sY i hi r α R g).mp (hα R g),
    fun hβ R _ _ _ g ↦ (specializationCycle_baseChangeFamily_properPushforwardFamily_iff
      sX sY i hi r α R g).mpr (hβ R g)⟩

end Main

/-! ### Pushforward along a surjective closed immersion -/

section SurjectiveClosedImmersion

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ) (k : ℤ)

/-- Proper pushforward along a closed immersion is injective on `k`-cycles. -/
theorem properPushforward_injective_of_isClosedImmersion :
    Function.Injective (properPushforward C sZ sX i hi k) :=
  properPushforward_injective_aux C sZ sX i hi k

/-- Proper pushforward along a closed immersion which is surjective on points is a bijection on
`k`-cycles. -/
theorem properPushforward_bijective_of_surjective (hsurj : Function.Surjective i.base) :
    Function.Bijective (properPushforward C sZ sX i hi k) := by
  refine ⟨properPushforward_injective_of_isClosedImmersion C sZ sX i hi k, fun c ↦
    ⟨cyclePullbackAlongClosedImmersion C sZ sX i hi k c, ?_⟩⟩
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  rw [properPushforward_cyclePullbackAlongClosedImmersion_apply,
    Set.indicator_of_mem (Set.mem_range.mpr (hsurj y))]

end SurjectiveClosedImmersion

/-! ### Stacks 0H5E -/

section Thickening

variable {X Y S : Scheme.{u}} (sX : X ⟶ S) [LocallyOfFiniteType sX] (sY : Y ⟶ S)
  [LocallyOfFiniteType sY] (i : X ⟶ Y) [IsClosedImmersion i] (hi : i ≫ sY = sX)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] in
/-- The morphism induced on the fibre over `s` by a closed immersion which is surjective on points
is again surjective on points. -/
theorem surjective_inducedFiberMap_of_surjective (hsurj : Function.Surjective i.base) (s : S) :
    Function.Surjective (inducedFiberMap sX sY i hi s).base :=
  (Stacks.Thickenings.isThickening_of_isPullback
    (isPullback_inducedFiberMap sX sY i hi s).flip ⟨inferInstance, hsurj⟩).2

/-- Along a thickening over the base, pushforward of the cycles of a single fibre is surjective. -/
theorem fiberProperPushforward_surjective_of_surjective
    (hsurj : Function.Surjective i.base) (s : S) (r : ℕ) :
    Function.Surjective (fiberProperPushforward sX sY i hi s r) :=
  (properPushforward_bijective_of_surjective (fieldChowSituation (S.residueField s))
    (sX.fiberToSpecResidueField s) (sY.fiberToSpecResidueField s) (inducedFiberMap sX sY i hi s)
    (inducedFiberMap_fiberToSpecResidueField sX sY i hi s) (r : ℤ)
    (surjective_inducedFiberMap_of_surjective sX sY i hi hsurj s)).2

/-- Along a thickening over the base, pushforward of the cycles of a single fibre is a
bijection. -/
theorem fiberProperPushforward_bijective_of_surjective
    (hsurj : Function.Surjective i.base) (s : S) (r : ℕ) :
    Function.Bijective (fiberProperPushforward sX sY i hi s r) :=
  ⟨fiberProperPushforward_injective sX sY i hi s r,
    fiberProperPushforward_surjective_of_surjective sX sY i hi hsurj s r⟩

/-- Proper pushforward on the cycles of the fibre over `s`, along the morphism of fibres induced
by a closed immersion over the base, as a homomorphism of abelian groups. -/
def fiberProperPushforwardHom (s : S) (r : ℕ) :
    FiberCycleGroup sX s r →+ FiberCycleGroup sY s r :=
  properPushforwardHom (fieldChowSituation (S.residueField s)) (sX.fiberToSpecResidueField s)
    (sY.fiberToSpecResidueField s) (inducedFiberMap sX sY i hi s)
    (inducedFiberMap_fiberToSpecResidueField sX sY i hi s) (r : ℤ)

/-- `fiberProperPushforwardHom` is `fiberProperPushforward`. -/
@[simp]
theorem fiberProperPushforwardHom_apply (s : S) (r : ℕ) (c : FiberCycleGroup sX s r) :
    fiberProperPushforwardHom sX sY i hi s r c = fiberProperPushforward sX sY i hi s r c :=
  rfl

/-- Proper pushforward along a thickening over the base is an additive equivalence on the cycles
of each fibre. -/
def fiberProperPushforwardAddEquiv (hsurj : Function.Surjective i.base) (s : S) (r : ℕ) :
    FiberCycleGroup sX s r ≃+ FiberCycleGroup sY s r :=
  AddEquiv.ofBijective (fiberProperPushforwardHom sX sY i hi s r)
    (fiberProperPushforward_bijective_of_surjective sX sY i hi hsurj s r)

/-- `fiberProperPushforwardAddEquiv` is `fiberProperPushforward`. -/
@[simp]
theorem fiberProperPushforwardAddEquiv_apply (hsurj : Function.Surjective i.base) (s : S)
    (r : ℕ) (c : FiberCycleGroup sX s r) :
    fiberProperPushforwardAddEquiv sX sY i hi hsurj s r c =
      fiberProperPushforward sX sY i hi s r c :=
  rfl

/-- Proper pushforward along a thickening over the base is an additive equivalence on families of
cycles on the fibres. -/
def properPushforwardFamilyAddEquiv (hsurj : Function.Surjective i.base) (r : ℕ) :
    FamilyOfCycles sX r ≃+ FamilyOfCycles sY r where
  toFun α s := fiberProperPushforwardAddEquiv sX sY i hi hsurj s r (α s)
  invFun β s := (fiberProperPushforwardAddEquiv sX sY i hi hsurj s r).symm (β s)
  left_inv α :=
    funext fun s ↦ (fiberProperPushforwardAddEquiv sX sY i hi hsurj s r).symm_apply_apply (α s)
  right_inv β :=
    funext fun s ↦ (fiberProperPushforwardAddEquiv sX sY i hi hsurj s r).apply_symm_apply (β s)
  map_add' α β :=
    funext fun s ↦ map_add (fiberProperPushforwardAddEquiv sX sY i hi hsurj s r) (α s) (β s)

/-- `properPushforwardFamilyAddEquiv` is the fibrewise pushforward `properPushforwardFamily`. -/
@[simp]
theorem properPushforwardFamilyAddEquiv_apply (hsurj : Function.Surjective i.base) (r : ℕ)
    (α : FamilyOfCycles sX r) :
    properPushforwardFamilyAddEquiv sX sY i hi hsurj r α =
      properPushforwardFamily sX sY i hi r α :=
  rfl

variable [IsLocallyNoetherian S]

/-- Let `S` be a locally Noetherian scheme and let `i : X ⟶ Y` be a thickening of schemes locally
of finite type over `S`. For `r ≥ 0` proper pushforward along `i` is an additive equivalence
`z(X/S, r) ≃ z(Y/S, r)` of groups of relative `r`-cycles. -/
@[stacks 0H5E "the bijection i_* : z(X/S, r) → z(X'/S, r) of relative r-cycles"]
def relativeCyclesAddEquivOfIsThickening (hthick : Stacks.Thickenings.IsThickening i) (r : ℕ) :
    ↥(relativeCycles sX r) ≃+ ↥(relativeCycles sY r) where
  toFun α := ⟨properPushforwardFamilyAddEquiv sX sY i hi hthick.2 r α.1, by
    exact (isRelativeCycle_iff_isRelativeCycle_properPushforwardFamily sX sY i hi r α.1).mp α.2⟩
  invFun β := ⟨(properPushforwardFamilyAddEquiv sX sY i hi hthick.2 r).symm β.1, by
    refine (isRelativeCycle_iff_isRelativeCycle_properPushforwardFamily sX sY i hi r _).mpr ?_
    rw [← properPushforwardFamilyAddEquiv_apply sX sY i hi hthick.2 r,
      (properPushforwardFamilyAddEquiv sX sY i hi hthick.2 r).apply_symm_apply]
    exact β.2⟩
  left_inv α :=
    Subtype.ext ((properPushforwardFamilyAddEquiv sX sY i hi hthick.2 r).symm_apply_apply α.1)
  right_inv β :=
    Subtype.ext ((properPushforwardFamilyAddEquiv sX sY i hi hthick.2 r).apply_symm_apply β.1)
  map_add' α β :=
    Subtype.ext (map_add (properPushforwardFamilyAddEquiv sX sY i hi hthick.2 r) α.1 β.1)

/-- The additive equivalence of relative `r`-cycles attached to a thickening is proper pushforward:
the family of fibrewise cycles underlying the image of `α` is the fibrewise proper pushforward of
the family underlying `α`. -/
@[simp, stacks 0H5E "the equivalence is the fibrewise proper pushforward of families of cycles"]
theorem relativeCyclesAddEquivOfIsThickening_coe
    (hthick : Stacks.Thickenings.IsThickening i) (r : ℕ) (α : ↥(relativeCycles sX r)) :
    (relativeCyclesAddEquivOfIsThickening sX sY i hi hthick r α).1 =
      properPushforwardFamily sX sY i hi r α.1 :=
  rfl

end Thickening

end Stacks.Chow

end
