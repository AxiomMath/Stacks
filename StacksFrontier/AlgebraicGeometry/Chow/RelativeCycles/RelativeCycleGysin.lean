module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackRationallyCompatible
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapChernDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.RelativeCycleBivariant
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.RelativeCycleGysinIntegral

/-!
# The operation of a relative cycle commutes with the Gysin map of every invertible module

Let `(S, δ)` be as in Section 0H65, let `p : X ⟶ Y` be a morphism of schemes locally of finite
type over `S`, let `r ≥ 0` and let `α ∈ z(X/Y, r)`. For a test scheme `g : T ⟶ Y`, an invertible
`𝒪_T`-module `L` and a global section `s` of `L`, with zero schemes `i : D ⟶ T` and
`j : E ⟶ X' = T ×_Y X` of `s` and of its pullback, this file proves

  `g^*α ∩ i_* i^* β ≡ j_* j^*(g^*α ∩ β)`   modulo rational equivalence inside `E`,

for every cycle `β` on `T`, where `i^*` and `j^*` are the Gysin maps of Stacks 02T8 for the first
Chern class of the invertible modules. On Chow groups this is condition (3) of Stacks 0B76 for the
operation `g ↦ g^*α ∩ -` of Stacks 0H6F, for every invertible module rather than only those of
Stacks 0H6E that are trivial on the divisor.

## Main results

* `Stacks.Chow.relativeCycleCap_gysin_rationallyEquivalent` — the displayed identity.
* `Stacks.Chow.relativeCycleCapChow_gysin` — condition (3) of Stacks 0B76 for the operation on
  Chow groups, at the Gysin system of the first Chern class.

## References

* [Stacks Project, Tag 0H6F](https://stacks.math.columbia.edu/tag/0H6F)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (p : X ⟶ Y) [LocallyOfFiniteType p] (r : ℕ) (α : FamilyOfCycles p r)
  (hα : letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    IsRelativeCycle p r α)

/-! ### The identity on cycles -/

include hα in
/-- **The identity on one integral component.** For a point `w` of the test scheme `T` of
relative dimension `k + 1`, with `W` the integral closed subscheme it is the generic point of,
`g^*α ∩ i_* i^* [W] - j_* j^*(g^*α ∩ [W])` is rationally equivalent to zero inside the part of `E`
lying over `W`. Here `i^*[W]` is the Gysin component cycle of `W`. -/
theorem relativeCycleCap_gysin_component {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k d : ℤ) (hd : d = (r : ℤ) + k) (w : T)
    (hw : relativeDimension C.dimensionFunction (g ≫ sY) w = k + 1) :
    IsRationallyEquivalentToZeroWithin C (pullback.fst p g ≫ p ≫ sY) d
      (cycleGroupCongr C _ hd.symm (relativeCycleCap C sY p r α g k
          (properPushforward C ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g ≫ sY) (g ≫ sY)
            (Stacks.Divisors.zeroScheme T L s).subschemeι rfl k
            (gysinComponentCycleAt C (g ≫ sY) k L s (firstChernComponentClass C (g ≫ sY) k L)
              w))) -
        properPushforward C
          ((bivariantPullbackZeroScheme p g L s).subschemeι ≫ pullback.fst p g ≫ p ≫ sY)
          (pullback.fst p g ≫ p ≫ sY) (bivariantPullbackZeroScheme p g L s).subschemeι rfl d
          ((gysinRule C (pullback.fst p g ≫ p ≫ sY) d (bivariantPullbackModule p g L)
              (bivariantPullbackSection p g L s)
              (firstChernComponentClass C (pullback.fst p g ≫ p ≫ sY) d
                (bivariantPullbackModule p g L))).extendCycleGroup
            (cycleGroupCongr C _ (by rw [hd]; ring) (relativeCycleCap C sY p r α g (k + 1)
              (cycleAssociatedToClosedSubscheme C (g ≫ sY) (integralComponentAt w).subschemeι
                (k + 1))))))
      (((bivariantPullbackZeroScheme p g L s).support : Set ↥(pullback p g)) ∩
        (pullback.snd p g).base ⁻¹' closure {w}) := by
  classical
  set W := integralComponentAt w with hWdef
  have : IsIntegral W.subscheme := isIntegral_integralComponentAt w
  set ιW := W.subschemeι with hιW
  set D := Stacks.Divisors.zeroScheme T L s with hD
  set E := bivariantPullbackZeroScheme p g L s with hE
  set π := pullback.snd p g with hπ
  set h' := bivariantBaseChangeMap p g ιW with hh'
  have : IsClosedImmersion h' := MorphismProperty.of_isPullback
    (isPullback_bivariantBaseChangeMap p g ιW) (P := @IsClosedImmersion) inferInstance
  have hWd : schemeDeltaDimension C ((ιW ≫ g) ≫ sY) = ((k + 1 : ℤ) : EInt) :=
    schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C (g ≫ sY) w hw
  set fc := fundamentalCycle C ((ιW ≫ g) ≫ sY) (k + 1) with hfc
  set M := (Scheme.Modules.pullback ιW).obj L with hM
  set σ := AlgebraicGeometry.pullbackGlobalSections ιW L s with hσ
  -- the identity on the integral test scheme `W`
  have hGW := relativeCycleCap_gysin_fundamentalCycle C sY p r α hα (ιW ≫ g) k d hd hWd M σ
  -- Stacks 02TA along `ιW` on `T` and along `h'` on `T ×_Y X`
  have h2TA := isRationallyEquivalentToZeroWithin_gysinRule_extendCycleGroup_properPushforward C
    (g ≫ sY) ((ιW ≫ g) ≫ sY) ιW (by simp [Category.assoc]) L s k fc
  set a := cycleGroupCongr C (pullback.fst p (ιW ≫ g) ≫ p ≫ sY)
    (by rw [hd]; ring : (r : ℤ) + (k + 1) = d + 1) (relativeCycleCap C sY p r α (ιW ≫ g) (k + 1) fc)
    with ha
  have hh'base : h' ≫ pullback.fst p g ≫ p ≫ sY = pullback.fst p (ιW ≫ g) ≫ p ≫ sY := by
    rw [← Category.assoc, hh']; simp
  have h2TA' := isRationallyEquivalentToZeroWithin_gysinRule_extendCycleGroup_properPushforward C
    (pullback.fst p g ≫ p ≫ sY) (pullback.fst p (ιW ≫ g) ≫ p ≫ sY) h' hh'base
    (bivariantPullbackModule p g L) (bivariantPullbackSection p g L s) d a
  -- the three pieces and their carriers
  set K : Set ↥(pullback p g) := (E.support : Set ↥(pullback p g)) ∩ π.base ⁻¹' closure {w}
    with hK
  have hWsupp : (W.support : Set T) = closure {w} := coe_support_integralComponentAt w
  have hEsupp : (E.support : Set ↥(pullback p g)) = π.base ⁻¹' (D.support : Set T) := by
    rw [hE, bivariantPullbackZeroScheme, Stacks.Divisors.zeroScheme_pullback,
      Scheme.IdealSheafData.support_comap]
    rfl
  have hrangeh' : Set.range h'.base ⊆ π.base ⁻¹' closure {w} := by
    rintro x ⟨x', rfl⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hh', bivariantBaseChangeMap, pullback.lift_snd,
      Scheme.Hom.comp_apply, ← hWsupp, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨_, rfl⟩
  have hclosedK : IsClosed (π.base ⁻¹' closure {w}) := isClosed_closure.preimage π.continuous
  -- (i) the identity on `W`, pushed forward
  have hI := properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion_of_within C
    _ (pullback.fst p g ≫ p ≫ sY) h' hh'base d
    (bivariantPullbackZeroScheme p (ιW ≫ g) M σ).support.isClosed hGW
  -- (ii) the defect of Stacks 02TA on `T`
  have hII := properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion_of_within C
    _ (g ≫ sY) D.subschemeι rfl k
    ((isClosed_closure).preimage D.subschemeι.continuous) h2TA
  have hII' := relativeCycleCap_isRationallyEquivalentToZeroWithin C sY p r α hα g k d hd (D ⊔ W) _
    (hII.mono (by
      rintro t ⟨e, he, rfl⟩
      rw [Scheme.IdealSheafData.support_sup]
      refine ⟨by rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨e, rfl⟩, ?_⟩
      have h := he
      rw [Set.mem_preimage, closure_range_subschemeι] at h
      exact h))
  -- (iii) the defect of Stacks 02TA on `T ×_Y X`
  have hIII := properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion_of_within C
    _ (pullback.fst p g ≫ p ≫ sY) E.subschemeι rfl d
    ((isClosed_closure).preimage E.subschemeι.continuous) h2TA'
  -- the square of the base change of `ιW`
  have hsq : h' ≫ π = pullback.snd p (ιW ≫ g) ≫ ιW := by
    rw [hh', hπ, bivariantBaseChangeMap, pullback.lift_snd]
  have hDσ : Stacks.Divisors.zeroScheme W.subscheme M σ = D.comap ιW :=
    Stacks.Divisors.zeroScheme_pullback ιW L s
  -- the identity of cycles
  have r1 : gysinComponentCycleAt C (g ≫ sY) k L s (firstChernComponentClass C (g ≫ sY) k L) w =
      (gysinRule C (g ≫ sY) k L s (firstChernComponentClass C (g ≫ sY) k L)).extendCycleGroup
        (properPushforward C ((ιW ≫ g) ≫ sY) (g ≫ sY) ιW (by simp [Category.assoc]) (k + 1)
          fc) := by
    rw [hfc, properPushforward_fundamentalCycle_of_isClosedImmersion,
      IntegralComponentRule.extendCycleGroup_cycleAssociatedToClosedSubscheme _ W inferInstance
        (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C (g ≫ sY) w hw)]
    exact gysinComponentCycleAt_eq C (g ≫ sY) k L s _ hw
  have r3 : ∀ (j : ℤ) (c : CycleGroup C ((ιW ≫ g) ≫ sY) j),
      relativeCycleCap C sY p r α g j
          (properPushforward C ((ιW ≫ g) ≫ sY) (g ≫ sY) ιW (by simp [Category.assoc]) j c) =
        properPushforward C (pullback.fst p (ιW ≫ g) ≫ p ≫ sY) (pullback.fst p g ≫ p ≫ sY) h'
          hh'base ((r : ℤ) + j) (relativeCycleCap C sY p r α (ιW ≫ g) j c) := fun j c ↦
    (properPushforward_relativeCycleCap C sY p r α g ιW h'
      (isPullback_bivariantBaseChangeMap p g ιW) (by simp [hh']) j c).symm
  have key : ∀ (x y z v : CycleGroup C (pullback.fst p g ≫ p ≫ sY) d), x.1 = y.1 + z.1 - v.1 →
      IsRationallyEquivalentToZeroWithin C _ d y K → IsRationallyEquivalentToZeroWithin C _ d z K →
      IsRationallyEquivalentToZeroWithin C _ d v K →
        IsRationallyEquivalentToZeroWithin C _ d x K := by
    intro x y z v hx hy hz hv
    have hxe : x = y + z - v := Subtype.ext (by rw [hx]; rfl)
    rw [hxe, sub_eq_add_neg]
    exact isRationallyEquivalentToZeroWithin_add C _ d (isRationallyEquivalentToZeroWithin_add C _ d
      hy hz) (isRationallyEquivalentToZeroWithin_neg C _ d hv)
  rw [properPushforward_sub] at hI
  rw [properPushforward_sub, map_sub, map_sub] at hII'
  rw [properPushforward_sub] at hIII
  refine key _ _ _ _ ?_ (hI.mono ?_) (hII'.mono ?_) (hIII.mono ?_)
  · -- the pieces, read on cycles
    have e5 : cycleGroupCongr C (pullback.fst p g ≫ p ≫ sY) (by rw [hd]; ring)
        (relativeCycleCap C sY p r α g (k + 1)
          (cycleAssociatedToClosedSubscheme C (g ≫ sY) W.subschemeι (k + 1))) =
        properPushforward C (pullback.fst p (ιW ≫ g) ≫ p ≫ sY) (pullback.fst p g ≫ p ≫ sY) h'
          hh'base (d + 1) a := by
      apply Subtype.ext
      rw [← properPushforward_fundamentalCycle_of_isClosedImmersion C ((ιW ≫ g) ≫ sY) (g ≫ sY) ιW
        (by simp [Category.assoc]) (k + 1), r3]
      rfl
    rw [e5, r1]
    -- the pushforward of the descended Gysin cycle of `W`
    have e3 : properPushforward C (D.subschemeι ≫ g ≫ sY) (g ≫ sY) D.subschemeι rfl k
        (properPushforward C ((pullbackZeroScheme ιW L s).subschemeι ≫ (ιW ≫ g) ≫ sY)
          (D.subschemeι ≫ g ≫ sY) (Stacks.Divisors.zeroSchemePullbackMap ιW L s)
          (Stacks.Divisors.zeroSchemePullbackMap_comp_structureMorphism ιW L s (g ≫ sY)
            ((ιW ≫ g) ≫ sY) (by simp [Category.assoc])) k
          ((gysinRule C ((ιW ≫ g) ≫ sY) k ((Scheme.Modules.pullback ιW).obj L)
            (AlgebraicGeometry.pullbackGlobalSections ιW L s)
            (firstChernComponentClass C ((ιW ≫ g) ≫ sY) k
              ((Scheme.Modules.pullback ιW).obj L))).extendCycleGroup fc)) =
        properPushforward C ((ιW ≫ g) ≫ sY) (g ≫ sY) ιW (by simp [Category.assoc]) k
          (properPushforward C ((Stacks.Divisors.zeroScheme W.subscheme M σ).subschemeι ≫
              (ιW ≫ g) ≫ sY) ((ιW ≫ g) ≫ sY) (Stacks.Divisors.zeroScheme W.subscheme M σ).subschemeι
            rfl k ((gysinRule C ((ιW ≫ g) ≫ sY) k M σ
              (firstChernComponentClass C ((ιW ≫ g) ≫ sY) k M)).extendCycleGroup fc)) := by
      rw [properPushforward_properPushforward, properPushforward_properPushforward]
      exact congrFun (properPushforward_congr C _ _ _ _
        (Stacks.Divisors.zeroSchemePullbackMap_comp_subschemeι ιW L s) _ _ k) _
    -- the descended Gysin cycle of the base change, for the two spellings of the module
    have hZ : Stacks.Divisors.zeroScheme (pullback p (ιW ≫ g))
        ((Scheme.Modules.pullback h').obj (bivariantPullbackModule p g L))
        (AlgebraicGeometry.pullbackGlobalSections h' (bivariantPullbackModule p g L)
          (bivariantPullbackSection p g L s)) =
        Stacks.Divisors.zeroScheme (pullback p (ιW ≫ g)) (bivariantPullbackModule p (ιW ≫ g) M)
          (bivariantPullbackSection p (ιW ≫ g) M σ) := by
      have hE2 : Stacks.Divisors.zeroScheme (pullback p g) (bivariantPullbackModule p g L)
          (bivariantPullbackSection p g L s) = D.comap π :=
        Stacks.Divisors.zeroScheme_pullback π L s
      have hEσ2 : Stacks.Divisors.zeroScheme (pullback p (ιW ≫ g))
          (bivariantPullbackModule p (ιW ≫ g) M) (bivariantPullbackSection p (ιW ≫ g) M σ) =
          (Stacks.Divisors.zeroScheme W.subscheme M σ).comap (pullback.snd p (ιW ≫ g)) :=
        Stacks.Divisors.zeroScheme_pullback _ M σ
      rw [Stacks.Divisors.zeroScheme_pullback h', hE2, hEσ2, hDσ,
        ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hsq]
    have φ : (Scheme.Modules.pullback h').obj (bivariantPullbackModule p g L) ≅
        bivariantPullbackModule p (ιW ≫ g) M :=
      (Scheme.Modules.pullbackComp h' π).app L ≪≫ (Scheme.Modules.pullbackCongr hsq).app L ≪≫
        ((Scheme.Modules.pullbackComp (pullback.snd p (ιW ≫ g)) ιW).app L).symm
    have e6 := properPushforward_gysinRule_extendCycleGroup_congr C
      (pullback.fst p (ιW ≫ g) ≫ p ≫ sY) d _ _ _ _ hZ φ a
    have e7 : properPushforward C (E.subschemeι ≫ pullback.fst p g ≫ p ≫ sY)
        (pullback.fst p g ≫ p ≫ sY) E.subschemeι rfl d
        (properPushforward C ((pullbackZeroScheme h' (bivariantPullbackModule p g L)
            (bivariantPullbackSection p g L s)).subschemeι ≫ pullback.fst p (ιW ≫ g) ≫ p ≫ sY)
          (E.subschemeι ≫ pullback.fst p g ≫ p ≫ sY)
          (Stacks.Divisors.zeroSchemePullbackMap h' (bivariantPullbackModule p g L)
            (bivariantPullbackSection p g L s))
          (Stacks.Divisors.zeroSchemePullbackMap_comp_structureMorphism h' _ _ _ _ hh'base) d
          ((gysinRule C (pullback.fst p (ιW ≫ g) ≫ p ≫ sY) d
            ((Scheme.Modules.pullback h').obj (bivariantPullbackModule p g L))
            (AlgebraicGeometry.pullbackGlobalSections h' (bivariantPullbackModule p g L)
              (bivariantPullbackSection p g L s))
            (firstChernComponentClass C (pullback.fst p (ιW ≫ g) ≫ p ≫ sY) d
              ((Scheme.Modules.pullback h').obj (bivariantPullbackModule p g L)))).extendCycleGroup
            a)) =
        properPushforward C (pullback.fst p (ιW ≫ g) ≫ p ≫ sY) (pullback.fst p g ≫ p ≫ sY) h'
          hh'base d
          (properPushforward C ((bivariantPullbackZeroScheme p (ιW ≫ g) M σ).subschemeι ≫
              pullback.fst p (ιW ≫ g) ≫ p ≫ sY) (pullback.fst p (ιW ≫ g) ≫ p ≫ sY)
            (bivariantPullbackZeroScheme p (ιW ≫ g) M σ).subschemeι rfl d
            ((gysinRule C (pullback.fst p (ιW ≫ g) ≫ p ≫ sY) d
              (bivariantPullbackModule p (ιW ≫ g) M) (bivariantPullbackSection p (ιW ≫ g) M σ)
              (firstChernComponentClass C (pullback.fst p (ιW ≫ g) ≫ p ≫ sY) d
                (bivariantPullbackModule p (ιW ≫ g) M))).extendCycleGroup a)) := by
      rw [properPushforward_properPushforward]
      rw [properPushforward_congr C _ _ _ _
        (Stacks.Divisors.zeroSchemePullbackMap_comp_subschemeι h' _ _) _
        (by simp only [Category.assoc, hh'base])]
      rw [← properPushforward_properPushforward C _ (pullback.fst p (ιW ≫ g) ≫ p ≫ sY) _
        (pullbackZeroScheme h' (bivariantPullbackModule p g L)
          (bivariantPullbackSection p g L s)).subschemeι h' rfl hh'base d]
      congr 1
      exact Subtype.ext e6
    have hV2 := congrArg Subtype.val e7
    have hZ2 := congrArg Subtype.val ((congrArg (cycleGroupCongr C (pullback.fst p g ≫ p ≫ sY)
      hd.symm) ((congrArg (relativeCycleCap C sY p r α g k) e3).trans (r3 k _))).trans
      (properPushforward_cycleGroupCongr C _ _ h' hh'base hd.symm _).symm)
    have key2 : ∀ {G : Type u} [AddCommGroup G] {S : AddSubgroup G} (A B Y₁ Y₂ Z₂ V₂ A' B' : S),
        A.1 = A'.1 → B.1 = B'.1 → Z₂.1 = Y₁.1 → V₂.1 = Y₂.1 →
          (A - B).1 = (Y₁ - Y₂).1 + (A' - Z₂).1 - (B' - V₂).1 := by
      intro G _ S A B Y₁ Y₂ Z₂ V₂ A' B' hA hB hZ hV
      simp only [AddSubgroup.coe_sub]
      rw [hA, hB, hZ, hV]
      abel
    exact key2 _ _ _ _ _ _ _ _ rfl rfl hZ2 hV2
  · rintro x ⟨x', hx', rfl⟩
    refine ⟨?_, hrangeh' ⟨x', rfl⟩⟩
    have hEσ : bivariantPullbackZeroScheme p (ιW ≫ g) M σ =
        (D.comap ιW).comap (pullback.snd p (ιW ≫ g)) := by
      rw [bivariantPullbackZeroScheme, Stacks.Divisors.zeroScheme_pullback, hDσ]
    rw [hEσ, Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap] at hx'
    rw [hEsupp, Set.mem_preimage, ← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]
    exact hx'
  · intro x hx
    rw [Set.mem_preimage, Scheme.IdealSheafData.support_sup] at hx
    refine ⟨?_, ?_⟩
    · rw [hEsupp]
      exact hx.1
    · rw [Set.mem_preimage, ← hWsupp]
      exact hx.2
  · rintro x ⟨e, he, rfl⟩
    refine ⟨?_, closure_minimal hrangeh' hclosedK he⟩
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨e, rfl⟩

include hα in
/-- **The operation of a relative cycle commutes with the Gysin map of an invertible module, on
cycles modulo rational equivalence.** For a test scheme `g : T ⟶ Y`, an invertible module `L` on
`T` and `s ∈ Γ(T, L)`, with zero schemes `i : D ⟶ T` of `s` and `j : E ⟶ T ×_Y X` of its
pullback, `g^*α ∩ i_* i^* β - j_* j^*(g^*α ∩ β)` is rationally equivalent to zero inside `E`. -/
theorem relativeCycleCap_gysin_rationallyEquivalent {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k d : ℤ) (hd : d = (r : ℤ) + k) (β : CycleGroup C (g ≫ sY) (k + 1)) :
    IsRationallyEquivalentToZeroWithin C (pullback.fst p g ≫ p ≫ sY) d
      (cycleGroupCongr C _ hd.symm (relativeCycleCap C sY p r α g k
          (properPushforward C ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g ≫ sY) (g ≫ sY)
            (Stacks.Divisors.zeroScheme T L s).subschemeι rfl k
            ((gysinRule C (g ≫ sY) k L s (firstChernComponentClass C (g ≫ sY) k L)).extendCycleGroup
              β))) -
        properPushforward C
          ((bivariantPullbackZeroScheme p g L s).subschemeι ≫ pullback.fst p g ≫ p ≫ sY)
          (pullback.fst p g ≫ p ≫ sY) (bivariantPullbackZeroScheme p g L s).subschemeι rfl d
          ((gysinRule C (pullback.fst p g ≫ p ≫ sY) d (bivariantPullbackModule p g L)
              (bivariantPullbackSection p g L s)
              (firstChernComponentClass C (pullback.fst p g ≫ p ≫ sY) d
                (bivariantPullbackModule p g L))).extendCycleGroup
            (cycleGroupCongr C _ (by rw [hd]; ring) (relativeCycleCap C sY p r α g (k + 1) β))))
      ((bivariantPullbackZeroScheme p g L s).support : Set ↥(pullback p g)) := by
  classical
  set D := Stacks.Divisors.zeroScheme T L s with hD
  set E := bivariantPullbackZeroScheme p g L s with hE
  set π := pullback.snd p g with hπ
  set chT := firstChernComponentClass C (g ≫ sY) k L with hchT
  set chE := firstChernComponentClass C (pullback.fst p g ≫ p ≫ sY) d
    (bivariantPullbackModule p g L) with hchE
  set RE := gysinRule C (pullback.fst p g ≫ p ≫ sY) d (bivariantPullbackModule p g L)
    (bivariantPullbackSection p g L s) chE with hRE
  -- the weight of the base-changed family at a point of `X'`
  set a : ↥(pullback p g) → ℤ := fun x ↦
    ((baseChangeFamily p g r α (π.base x)) : AlgebraicCycle _ ℤ) (π.asFiber x) with ha
  have hcap : ∀ (j : ℤ) (c : CycleGroup C (g ≫ sY) j) (x : ↥(pullback p g)),
      (relativeCycleCap C sY p r α g j c).1 x = c.1 (π.base x) * a x := fun _ _ _ ↦ rfl
  set J := ↥(Function.support (β.1 : T → ℤ))
  have hdim : ∀ j : J, relativeDimension C.dimensionFunction (g ≫ sY) (j : T) = k + 1 :=
    fun j ↦ (mem_cyclesOfDimension_iff_forall_point C (g ≫ sY) (k + 1) β.1).1 β.2 j j.2
  -- the cycle of one component
  set Δ : J → CycleGroup C (pullback.fst p g ≫ p ≫ sY) d := fun j ↦
    cycleGroupCongr C _ hd.symm (relativeCycleCap C sY p r α g k
          (properPushforward C (D.subschemeι ≫ g ≫ sY) (g ≫ sY) D.subschemeι rfl k
            (gysinComponentCycleAt C (g ≫ sY) k L s chT j))) -
        properPushforward C (E.subschemeι ≫ pullback.fst p g ≫ p ≫ sY)
          (pullback.fst p g ≫ p ≫ sY) E.subschemeι rfl d
          (RE.extendCycleGroup
            (cycleGroupCongr C _ (by rw [hd]; ring) (relativeCycleCap C sY p r α g (k + 1)
              (cycleAssociatedToClosedSubscheme C (g ≫ sY) (integralComponentAt (j : T)).subschemeι
                (k + 1))))) with hΔ
  have hcomp : ∀ j : J, IsRationallyEquivalentToZeroWithin C (pullback.fst p g ≫ p ≫ sY) d (Δ j)
      ((E.support : Set ↥(pullback p g)) ∩ π.base ⁻¹' closure {(j : T)}) := fun j ↦
    relativeCycleCap_gysin_component C sY p r α hα g L s k d hd j (hdim j)
  have hlf : LocallyFinite fun j : J ↦
      ((E.support : Set ↥(pullback p g)) ∩ π.base ⁻¹' closure {(j : T)}) :=
    ((locallyFinite_closure_support β.1.locallyFiniteSupport).preimage_continuous
      π.continuous).subset fun j ↦ Set.inter_subset_right
  refine (rationallyEquivalentToZeroWithin_finsum C (pullback.fst p g ≫ p ≫ sY) d
    (fun j : J ↦ (β.1 (j : T)) • Δ j) _ hlf
    (fun j ↦ isRationallyEquivalentToZeroWithin_zsmul C _ d (hcomp j) (β.1 (j : T))
      fun x ↦ by simp) ?_).mono (Set.iUnion_subset fun j ↦ Set.inter_subset_left)
  intro y
  -- restricting a sum over the points of `T` to the support of `β`
  have hsum : ∀ F : T → ℤ, (∀ t, β.1 t = 0 → F t = 0) → ∑ᶠ t, F t = ∑ᶠ j : J, F j := by
    intro F hF
    rw [finsum_set_coe_eq_finsum_mem, ← finsum_mem_univ]
    refine (finsum_mem_inter_support_eq' F _ _ fun t ht ↦ ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩).symm
    by_contra h
    exact ht (hF t (by simpa using h))
  -- the left hand side, componentwise on `T`
  have hL : ∀ t : T,
      (properPushforward C (D.subschemeι ≫ g ≫ sY) (g ≫ sY) D.subschemeι rfl k
        ((gysinRule C (g ≫ sY) k L s chT).extendCycleGroup β)).1 t =
        ∑ᶠ j : J, β.1 j * (properPushforward C (D.subschemeι ≫ g ≫ sY) (g ≫ sY) D.subschemeι rfl
          k (gysinComponentCycleAt C (g ≫ sY) k L s chT j)).1 t := by
    intro t
    by_cases ht : t ∈ Set.range D.subschemeι.base
    · obtain ⟨e, rfl⟩ := ht
      rw [properPushforward_apply_image_of_isClosedImmersion]
      simp_rw [properPushforward_apply_image_of_isClosedImmersion]
      change ∑ᶠ x : T, β.1 x * (gysinComponentCycleAt C (g ≫ sY) k L s chT x).1 e = _
      exact hsum _ fun t ht ↦ by rw [ht, zero_mul]
    · rw [properPushforward_apply_eq_zero_of_notMem_range_of_isClosedImmersion C _ _ _ _ _ _ ht]
      refine (finsum_eq_zero_of_forall_eq_zero fun j ↦ ?_).symm
      rw [properPushforward_apply_eq_zero_of_notMem_range_of_isClosedImmersion C _ _ _ _ _ _ ht,
        mul_zero]
  -- the Gysin component cycles on `X'`
  set ρ : ↥(pullback p g) → CycleGroup C (E.subschemeι ≫ pullback.fst p g ≫ p ≫ sY) d := fun x ↦
    gysinComponentCycleAt C (pullback.fst p g ≫ p ≫ sY) d (bivariantPullbackModule p g L)
      (bivariantPullbackSection p g L s) chE x with hρ
  have hρsupp : ∀ x, Function.support (ρ x).1 ⊆ E.subschemeι.base ⁻¹' closure {x} := fun x ↦
    support_gysinComponentCycleAt_subset C (pullback.fst p g ≫ p ≫ sY) d
      (bivariantPullbackModule p g L) (bivariantPullbackSection p g L s) chE x
  have hext : ∀ (c : CycleGroup C (pullback.fst p g ≫ p ≫ sY) (d + 1)) (e : E.subscheme),
      (RE.extendCycleGroup c).1 e = ∑ᶠ x, c.1 x * (ρ x).1 e := fun _ _ ↦ rfl
  -- the prime cycle of a point of the support of `β`
  have hprime : ∀ (j : J) (t : T),
      (cycleAssociatedToClosedSubscheme C (g ≫ sY) (integralComponentAt (j : T)).subschemeι
        (k + 1)).1 t = if t = (j : T) then 1 else 0 := by
    intro j t
    split_ifs with h
    · subst h
      exact cycleAssociatedToClosedSubscheme_integralComponentAt_self C (g ≫ sY) (j : T)
        (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C (g ≫ sY) _ (hdim j))
    · exact cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C (g ≫ sY) (k + 1) _ h
  -- the right hand side, componentwise
  have hR : ∀ e : E.subscheme,
      ∑ᶠ x, (β.1 (π.base x) * a x) * (ρ x).1 e =
        ∑ᶠ j : J, β.1 j * ∑ᶠ x, (if π.base x = (j : T) then (1 : ℤ) else 0) * a x * (ρ x).1 e := by
    intro e
    have hF : (Function.support fun x ↦ (β.1 (π.base x) * a x) * (ρ x).1 e).Finite := by
      refine (finite_support_inter_generalizations
        (relativeCycleCap C sY p r α g (k + 1) β).1.locallyFiniteSupport
        (isCompact_singleton (x := E.subschemeι.base e))).subset ?_
      intro x hx
      replace hx : (β.1 (π.base x) * a x) * (ρ x).1 e ≠ 0 := hx
      refine ⟨⟨_, rfl, ?_⟩, left_ne_zero_of_mul hx⟩
      exact hρsupp x (right_ne_zero_of_mul hx)
    rw [← finsum_finsum_mem_fiber π.base _ hF]
    refine (hsum _ fun t ht ↦ ?_).trans (finsum_congr fun j ↦ ?_)
    · exact finsum_mem_eq_zero_of_forall_eq_zero fun x hx ↦ by
        rw [show π.base x = t from hx, ht, zero_mul, zero_mul]
    · rw [finsum_mem_def, mul_finsum]
      refine finsum_congr fun x ↦ ?_
      by_cases hx : π.base x = (j : T)
      · rw [Set.indicator_of_mem (by exact hx), ite_eq_left hx, hx]
        ring
      · rw [Set.indicator_of_notMem (by exact hx), ite_eq_right hx]
        ring
  -- the support facts
  have hclosD : ∀ (j : J) (t : T), (properPushforward C (D.subschemeι ≫ g ≫ sY) (g ≫ sY)
      D.subschemeι rfl k (gysinComponentCycleAt C (g ≫ sY) k L s chT j)).1 t ≠ 0 →
      t ∈ closure {(j : T)} := by
    intro j t ht
    by_cases hmem : t ∈ Set.range D.subschemeι.base
    · obtain ⟨e, rfl⟩ := hmem
      rw [properPushforward_apply_image_of_isClosedImmersion] at ht
      exact support_gysinComponentCycleAt_subset C (g ≫ sY) k L s chT j ht
    · exact absurd (properPushforward_apply_eq_zero_of_notMem_range_of_isClosedImmersion C _ _ _ _
        _ _ hmem) ht
  have hpoint : ∀ t : T, {j : J | t ∈ closure {(j : T)}}.Finite := fun t ↦
    (locallyFinite_closure_support β.1.locallyFiniteSupport).point_finite t
  set A : J → ℤ := fun j ↦ (properPushforward C (D.subschemeι ≫ g ≫ sY) (g ≫ sY)
      D.subschemeι rfl k (gysinComponentCycleAt C (g ≫ sY) k L s chT j)).1 (π.base y) * a y
    with hA
  set B : J → ℤ := fun j ↦ (properPushforward C (E.subschemeι ≫ pullback.fst p g ≫ p ≫ sY)
      (pullback.fst p g ≫ p ≫ sY) E.subschemeι rfl d
      (RE.extendCycleGroup
        (cycleGroupCongr C _ (by rw [hd]; ring) (relativeCycleCap C sY p r α g (k + 1)
          (cycleAssociatedToClosedSubscheme C (g ≫ sY) (integralComponentAt (j : T)).subschemeι
            (k + 1)))))).1 y with hB
  have hΔy : ∀ j : J, ((β.1 (j : T)) • Δ j).1 y = β.1 j * (A j - B j) := by
    intro j
    simp only [AddSubgroupClass.coe_zsmul, Function.locallyFinsuppWithin.coe_zsmul,
      Pi.smul_apply, smul_eq_mul, hΔ, AddSubgroupClass.coe_sub,
      Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply]
    rfl
  have hfinA : (Function.support fun j : J ↦ β.1 j * A j).Finite := by
    refine (hpoint (π.base y)).subset fun j hj ↦ ?_
    exact hclosD j _ (left_ne_zero_of_mul (right_ne_zero_of_mul hj))
  have hLy : (properPushforward C (D.subschemeι ≫ g ≫ sY) (g ≫ sY) D.subschemeι rfl k
      ((gysinRule C (g ≫ sY) k L s chT).extendCycleGroup β)).1 (π.base y) * a y =
        ∑ᶠ j : J, β.1 j * A j := by
    rw [hL, finsum_mul]
    exact finsum_congr fun j ↦ by rw [hA]; ring
  have hRy : (properPushforward C (E.subschemeι ≫ pullback.fst p g ≫ p ≫ sY)
      (pullback.fst p g ≫ p ≫ sY) E.subschemeι rfl d (RE.extendCycleGroup
        (cycleGroupCongr C _ (by rw [hd]; ring) (relativeCycleCap C sY p r α g (k + 1) β)))).1 y =
        ∑ᶠ j : J, β.1 j * B j := by
    by_cases hy : y ∈ Set.range E.subschemeι.base
    · obtain ⟨e, rfl⟩ := hy
      rw [properPushforward_apply_image_of_isClosedImmersion, hext]
      refine (hR e).trans (finsum_congr fun j ↦ ?_)
      simp only [hB]
      rw [properPushforward_apply_image_of_isClosedImmersion, hext]
      congr 1
      refine finsum_congr fun x ↦ ?_
      change _ = ((cycleAssociatedToClosedSubscheme C (g ≫ sY)
        (integralComponentAt (j : T)).subschemeι (k + 1)).1 (π.base x) * a x) * _
      rw [hprime]
    · rw [properPushforward_apply_eq_zero_of_notMem_range_of_isClosedImmersion C _ _ _ _ _ _ hy]
      refine (finsum_eq_zero_of_forall_eq_zero fun j ↦ ?_).symm
      simp only [hB]
      rw [properPushforward_apply_eq_zero_of_notMem_range_of_isClosedImmersion C _ _ _ _ _ _ hy,
        mul_zero]
  have hfinB : (Function.support fun j : J ↦ β.1 j * B j).Finite := by
    by_cases hy : y ∈ Set.range E.subschemeι.base
    · obtain ⟨e, rfl⟩ := hy
      have hfin := finite_support_inter_generalizations
        (relativeCycleCap C sY p r α g (k + 1) β).1.locallyFiniteSupport
        (isCompact_singleton (x := E.subschemeι.base e))
      refine ((hfin.image π.base).preimage Subtype.val_injective.injOn).subset fun j hj ↦ ?_
      replace hj : β.1 j * B j ≠ 0 := hj
      have hBj := right_ne_zero_of_mul hj
      simp only [hB] at hBj
      rw [properPushforward_apply_image_of_isClosedImmersion, hext] at hBj
      obtain ⟨x, hx⟩ := Function.support_nonempty_iff.2 (fun h ↦ hBj (by
        rw [finsum_eq_zero_of_forall_eq_zero fun x ↦ congrFun h x]))
      replace hx : (cycleGroupCongr C _ _ (relativeCycleCap C sY p r α g (k + 1)
          (cycleAssociatedToClosedSubscheme C (g ≫ sY) (integralComponentAt (j : T)).subschemeι
            (k + 1)))).1 x * (ρ x).1 e ≠ 0 := hx
      change ((cycleAssociatedToClosedSubscheme C (g ≫ sY) (integralComponentAt (j : T)).subschemeι
        (k + 1)).1 (π.base x) * a x) * (ρ x).1 e ≠ 0 at hx
      rw [hprime] at hx
      have hxj : π.base x = (j : T) := by
        by_contra hne
        rw [ite_eq_right hne, zero_mul, zero_mul] at hx
        exact hx rfl
      rw [ite_eq_left hxj, one_mul] at hx
      refine ⟨x, ⟨⟨_, rfl, hρsupp x (right_ne_zero_of_mul hx)⟩, ?_⟩, hxj⟩
      change (β.1 (π.base x) * a x) ≠ 0
      rw [hxj]
      exact mul_ne_zero j.2 (left_ne_zero_of_mul hx)
    · refine Set.finite_empty.subset fun j hj ↦ hj ?_
      change β.1 j * B j = 0
      simp only [hB]
      rw [properPushforward_apply_eq_zero_of_notMem_range_of_isClosedImmersion C _ _ _ _ _ _ hy,
        mul_zero]
  simp only [AddSubgroupClass.coe_sub, Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply]
  change (properPushforward C (D.subschemeι ≫ g ≫ sY) (g ≫ sY) D.subschemeι rfl k
      ((gysinRule C (g ≫ sY) k L s chT).extendCycleGroup β)).1 (π.base y) * a y - _ = _
  rw [hLy, hRy, ← finsum_sub_distrib hfinA hfinB]
  exact finsum_congr fun j ↦ by rw [hΔy, mul_sub]

/-! ### Condition (3) of Stacks 0B76 -/

/-- **Condition (3) of Stacks 0B76** for the operation `g ↦ g^*α ∩ -` of a relative cycle on Chow
groups, at the Gysin system of the first Chern class of an invertible module: it commutes with the
Gysin map of the zero scheme of every global section of every invertible module on every test
scheme. -/
theorem relativeCycleCapChow_gysin {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ) :
    let D := Stacks.Divisors.zeroScheme T L s
    let L' := (Scheme.Modules.pullback (pullback.snd p g)).obj L
    let s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd p g) L s
    let E := Stacks.Divisors.zeroScheme (pullback p g) L' s'
    ∀ (e : pullback p (D.subschemeι ≫ g) ≅ E.subscheme)
      (_he : e.hom ≫ E.subschemeι = bivariantBaseChangeMap p g D.subschemeι)
      (hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst p g ≫ p ≫ sY) =
        pullback.fst p (D.subschemeι ≫ g) ≫ p ≫ sY)
      (β : chowGroup C (g ≫ sY) (k + 1)),
      properChowPushforward C (pullback.fst p (D.subschemeι ≫ g) ≫ p ≫ sY)
          (E.subschemeι ≫ pullback.fst p g ≫ p ≫ sY) e.hom hbase (k - -(r : ℤ))
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C
            (pullback.fst p (D.subschemeι ≫ g) ≫ p ≫ sY) (E.subschemeι ≫ pullback.fst p g ≫ p ≫ sY)
            e.hom hbase (k - -(r : ℤ)))
          (relativeCycleCapChow C sY p r α hα (D.subschemeι ≫ g) k
            ((gysinSystemOfInvertible C).onChow (g ≫ sY) L s k β)) =
        (gysinSystemOfInvertible C).onChow (pullback.fst p g ≫ p ≫ sY) L' s' (k - -(r : ℤ))
          (Eq.mp (congrArg (chowGroup C (pullback.fst p g ≫ p ≫ sY))
            (by omega : (k + 1) - -(r : ℤ) = (k - -(r : ℤ)) + 1))
            (relativeCycleCapChow C sY p r α hα g (k + 1) β)) := by
  intro D L' s' E e he hbase β
  induction β using QuotientAddGroup.induction_on with
  | H b =>
    set γD :=
      (gysinRule C (g ≫ sY) k L s (firstChernComponentClass C (g ≫ sY) k L)).extendCycleGroup b
      with hγD
    set c := cycleGroupCongr C (pullback.fst p g ≫ p ≫ sY)
      (by ring : (r : ℤ) + (k + 1) = k - -(r : ℤ) + 1) (relativeCycleCap C sY p r α g (k + 1) b)
      with hc
    have hL : properChowPushforward C (pullback.fst p (D.subschemeι ≫ g) ≫ p ≫ sY)
          (E.subschemeι ≫ pullback.fst p g ≫ p ≫ sY) e.hom hbase (k - -(r : ℤ))
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C
            (pullback.fst p (D.subschemeι ≫ g) ≫ p ≫ sY) (E.subschemeι ≫ pullback.fst p g ≫ p ≫ sY)
            e.hom hbase (k - -(r : ℤ)))
          (relativeCycleCapChow C sY p r α hα (D.subschemeι ≫ g) k
            ((gysinSystemOfInvertible C).onChow (g ≫ sY) L s k b)) =
        QuotientAddGroup.mk' (rationalEquivalences C _ (k - -(r : ℤ)))
          (properPushforward C (pullback.fst p (D.subschemeι ≫ g) ≫ p ≫ sY)
            (E.subschemeι ≫ pullback.fst p g ≫ p ≫ sY) e.hom hbase (k - -(r : ℤ))
            (cycleGroupCongr C _ (by ring)
              (relativeCycleCap C sY p r α (D.subschemeι ≫ g) k γD))) := rfl
    have hR : (gysinSystemOfInvertible C).onChow (pullback.fst p g ≫ p ≫ sY) L' s' (k - -(r : ℤ))
          (Eq.mp (congrArg (chowGroup C (pullback.fst p g ≫ p ≫ sY))
            (by omega : (k + 1) - -(r : ℤ) = (k - -(r : ℤ)) + 1))
            (relativeCycleCapChow C sY p r α hα g (k + 1) b)) =
        QuotientAddGroup.mk' (rationalEquivalences C _ (k - -(r : ℤ)))
          ((gysinRule C (pullback.fst p g ≫ p ≫ sY) (k - -(r : ℤ)) L' s'
            (firstChernComponentClass C (pullback.fst p g ≫ p ≫ sY) (k - -(r : ℤ))
              L')).extendCycleGroup c) := by
      have h1 : relativeCycleCapChow C sY p r α hα g (k + 1) b =
          QuotientAddGroup.mk' (rationalEquivalences C _ ((k + 1) - -(r : ℤ)))
            (cycleGroupCongr C _ (by ring) (relativeCycleCap C sY p r α g (k + 1) b)) := rfl
      rw [h1, eqMp_chowGroup_mk C _ (by omega)]
      rfl
    rw [hL, hR]
    refine (QuotientAddGroup.eq_iff_sub_mem).2 ?_
    refine isRationallyEquivalentToZero_of_properPushforward_isRationallyEquivalentToZeroWithin C
      _ (pullback.fst p g ≫ p ≫ sY) E.subschemeι rfl (k - -(r : ℤ)) _ ?_
    rw [Scheme.IdealSheafData.range_subschemeι]
    refine isRationallyEquivalentToZeroWithin_congr_degree C _ rfl _ _ ?_ _
      (relativeCycleCap_gysin_rationallyEquivalent C sY p r α hα g L s k (k - -(r : ℤ)) (by ring) b)
    rw [properPushforward_sub]
    congr 2
    apply Subtype.ext
    have hcomp := congrFun (properPushforward_comp C (pullback.fst p (D.subschemeι ≫ g) ≫ p ≫ sY)
      (E.subschemeι ≫ pullback.fst p g ≫ p ≫ sY) (pullback.fst p g ≫ p ≫ sY) e.hom E.subschemeι
      hbase rfl (k - -(r : ℤ)))
      (cycleGroupCongr C _ (by ring) (relativeCycleCap C sY p r α (D.subschemeι ≫ g) k γD))
    simp only [Function.comp_apply] at hcomp
    rw [hcomp, properPushforward_congr C _ _ _ _ he _ (by rw [← he]; exact hbase)]
    have hprop := properPushforward_relativeCycleCap C sY p r α g D.subschemeι
      (bivariantBaseChangeMap p g D.subschemeι) (isPullback_bivariantBaseChangeMap p g D.subschemeι)
      (by simp) k γD
    exact (congrArg Subtype.val hprop).symm

/-! ### The bivariant class -/

/-- **Stacks 0H6F, the bivariant class `c(α) ∈ A^{-r}(X ⟶ Y)`** of a relative `r`-cycle `α` on
`X/Y`: on a test scheme `g : Y' ⟶ Y` locally of finite type it caps by the operation
`g^*α ∩ - : A_k(Y') ⟶ A_{k+r}(Y' ×_Y X)` induced by the operation on cycles, which factors through
rational equivalence (`Stacks.Chow.relativeCycleCapChow`). The three conditions of Stacks 0B76 are
`Stacks.Chow.relativeCycleCapChow_properPushforward` (Stacks 0H6B),
`Stacks.Chow.relativeCycleCapChow_flatPullbackChow` (Stacks 0H68) and
`Stacks.Chow.relativeCycleCapChow_gysin`, the Gysin condition for every invertible module. -/
def relativeCycleBivariantClass :
    BivariantClass C (gysinSystemOfInvertible C) (p ≫ sY) sY p rfl (-(r : ℤ)) where
  cap g _ k := relativeCycleCapChow C sY p r α hα g k
  cap_properPushforward g _ h _ h' sq hfst k := by
    let : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    exact relativeCycleCapChow_properPushforward C sY p r α hα g h h' sq hfst k _ _
  cap_flatPullbackChow g _ h _ _ d hd h' sq hfst k := by
    let : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    let : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    exact relativeCycleCapChow_flatPullbackChow C sY p r α hα g h d hd h'
      (AlgebraicGeometry.RelativeDimension.of_isPullback sq hd) sq hfst k _ _
  cap_gysin g _ L _ s k := relativeCycleCapChow_gysin C sY p r α hα g L s k

/-- The bivariant class of a relative cycle caps the class of a cycle `β` on a test scheme
`g : Y' ⟶ Y` to the class of `g^*α ∩ β`. -/
theorem relativeCycleBivariantClass_cap_mk {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (k : ℤ) (β : CycleGroup C (g ≫ sY) k) :
    (relativeCycleBivariantClass C sY p r α hα).cap g k
        (QuotientAddGroup.mk' (rationalEquivalences C (g ≫ sY) k) β) =
      QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst p g ≫ p ≫ sY) (k - -(r : ℤ)))
        (cycleGroupCongr C _ (by ring) (relativeCycleCap C sY p r α g k β)) :=
  rfl

include hα in
/-- **Stacks Project, Proposition 0H6F.** Let `(S, δ)` be as in Section 0H65, let `p : X ⟶ Y` be
a morphism of schemes locally of finite type over `S`, let `r ≥ 0` and let `α ∈ z(X/Y, r)` be a
relative `r`-cycle on `X/Y`. The rule that to every morphism `g : Y' ⟶ Y` locally of finite type
and every `k ∈ ℤ` associates the operation `g^*α ∩ - : Z_k(Y') ⟶ Z_{r + k}(X')`,
`X' = Y' ×_Y X` (`Stacks.Chow.relativeCycleCap`), factors through rational equivalence to define
a bivariant class `c(α) ∈ A^{-r}(X ⟶ Y)`: there is a bivariant class of degree `-r` for `p`
whose cap operation on every test scheme sends the class of a cycle `β` to the class of
`g^*α ∩ β`. The class is `Stacks.Chow.relativeCycleBivariantClass`. -/
@[stacks 0H6F]
theorem exists_bivariantClass_cap_mk_eq_relativeCycleCap :
    ∃ c : BivariantClass C (gysinSystemOfInvertible C) (p ≫ sY) sY p rfl (-(r : ℤ)),
      ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
        (β : CycleGroup C (g ≫ sY) k),
        c.cap g k (QuotientAddGroup.mk' (rationalEquivalences C (g ≫ sY) k) β) =
          QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst p g ≫ p ≫ sY) (k - -(r : ℤ)))
            (cycleGroupCongr C _ (by ring) (relativeCycleCap C sY p r α g k β)) :=
  ⟨relativeCycleBivariantClass C sY p r α hα, fun g _ k β ↦
    relativeCycleBivariantClass_cap_mk C sY p r α hα g k β⟩

end Stacks.Chow

end
