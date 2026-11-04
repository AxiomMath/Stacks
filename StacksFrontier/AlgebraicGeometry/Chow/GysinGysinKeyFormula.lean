module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinGysinAmbientDivisor

/-!
# Two Gysin maps commute

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `(L, s, i : D → X)` and `(L', s', i' : D' → X)` be two triples as in
Definition 02T8. Stacks 0B73 asserts that the square of four Gysin maps

```
  CH_k(X) ⟶ CH_{k-1}(D) ⟶ CH_{k-2}(D ∩ D')   and   CH_k(X) ⟶ CH_{k-1}(D') ⟶ CH_{k-2}(D ∩ D')
```

commutes.

## Main definitions

* `Stacks.Chow.componentSituation`: on an integral closed subscheme `Z_ξ` of `X`, the
  `KeyFormulaSituation` of the restrictions of the generators of `L` and `L'` prescribed at `ξ`
  (`Stacks.Chow.componentGeneratorAt`).
* `Stacks.Chow.KeyFormulaSituation.swap`: a situation with its two pairs exchanged.

## Main results

* `isRationallyEquivalentToZeroWithin_properPushforward_gysinGysinComponentCycle_sub_sum`: one
  iterated Gysin cycle of `Z_ξ`, pushed forward to `X`, is rationally equivalent within
  `Z_ξ ∩ D ∩ D'` to the sum the family of the key formula attaches to it.
* `Stacks.Chow.gysinGysinCommutesOnComponents_componentSituation`: the two iterated Gysin maps
  agree on every integral closed subscheme of delta-dimension `k + 2`.
* `Stacks.Chow.gysinChowOfInvertible_comm`: the square of four Gysin maps commutes.

## References

* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

section Member

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L L' : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']
  (s : Γ(L, ⊤)) (s' : Γ(L', ⊤)) (ξ : X)

/-- The integral closed subscheme through a point of a closed set lies in that closed set. -/
private theorem coe_support_integralComponentAt_subset_of_mem {Y : Scheme.{u}}
    (I : Y.IdealSheafData) {y : Y} (hy : y ∈ (I.support : Set Y)) :
    ((integralComponentAt y).support : Set Y) ⊆ I.support := by
  rw [coe_support_integralComponentAt]
  exact I.support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hy)

/-- A point of the integral closed subscheme through `y`, mapped to the ambient scheme, lies in
its support. -/
private theorem subschemeι_base_mem_support_integralComponentAt {Y : Scheme.{u}} (y : Y)
    (w : (integralComponentAt y).subscheme) :
    (integralComponentAt y).subschemeι.base w ∈ ((integralComponentAt y).support : Set Y) := by
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨w, rfl⟩

/-- Let `Z` be the integral closed subscheme of `X` through `x`, presented both as a component
`Z ⊆ D` of the zero scheme of `s` and as a component `Z ⊆ W` of the integral closed subscheme
through `ξ`, and let `m'` be the generator of `L'` prescribed at `x`. Then the outer Gysin cycle
of the first presentation and the divisor `div_{L'|_Z}(m'|_Z)` of the second have, after being
pushed forward to `X`, a difference rationally equivalent to zero with witnesses inside
`Z ∩ D ∩ D'`. -/
theorem isRationallyEquivalentToZeroWithin_gysinRuleInter_cycle_sub_restricted
    {x : X} (hxD : Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt x)
    (zD : (Stacks.Divisors.zeroScheme X L s).subscheme)
    (hzD : (Stacks.Divisors.zeroScheme X L s).subschemeι.base zD = x)
    (wW : (integralComponentAt ξ).subscheme)
    (hwW : (integralComponentAt ξ).subschemeι.base wW = x)
    (hDimZ : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ p) =
      ((k + 1 : ℤ) : EInt))
    (hDimzD : schemeDeltaDimension C ((integralComponentAt zD).subschemeι ≫
      (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hDimwW : schemeDeltaDimension C ((integralComponentAt wW).subschemeι ≫
      (integralComponentAt ξ).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    IsRationallyEquivalentToZeroWithin C p k
      (properPushforward C ((zeroSchemeInter L L' s s').subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          ((zeroSchemeInter L L' s s').subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι) (Category.assoc _ _ _) k
          ((gysinRuleInter C p k L L' s s').cycle (integralComponentAt zD)
            (isIntegral_integralComponentAt zD) hDimzD) -
        properPushforward C ((integralComponentAt wW).subschemeι ≫
            (integralComponentAt ξ).subschemeι ≫ p) p
          ((integralComponentAt wW).subschemeι ≫ (integralComponentAt ξ).subschemeι)
          (Category.assoc _ _ _) k
          (chernCycleOfRestrictedStalk C ((integralComponentAt ξ).subschemeι ≫ p) k
            ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L')
            (integralComponentAt wW) (isIntegral_integralComponentAt wW) hDimwW
            (genericPointOf_integralComponentAt wW)
            (Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L' wW hwW
              (componentGeneratorAt L' s' x))))
      (((integralComponentAt x).support : Set X) ∩
        (((Stacks.Divisors.zeroScheme X L s).support : Set X) ∩
          ((Stacks.Divisors.zeroScheme X L' s').support : Set X))) := by
  have : IsIntegral (integralComponentAt ξ).subscheme := isIntegral_integralComponentAt ξ
  have : IsLocallyNoetherian (integralComponentAt ξ).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt ξ).subschemeι ≫ p)
  have hiff : zeroSchemeInter L L' s s' ≤ integralComponentAt zD ↔
      Stacks.Divisors.zeroScheme X L' s' ≤ integralComponentAt x := by
    rw [le_integralComponentAt_iff_mem_support, le_integralComponentAt_iff_mem_support,
      zeroSchemeInter_eq_comap, Scheme.IdealSheafData.support_comap]
    exact ⟨fun h ↦ by rwa [← hzD], fun h ↦ by rwa [← hzD] at h⟩
  have hsubD : ((integralComponentAt x).support : Set X) ⊆
      ((Stacks.Divisors.zeroScheme X L s).support : Set X) := by
    exact coe_support_integralComponentAt_subset_of_mem _
      ((le_integralComponentAt_iff_mem_support _ _).1 hxD)
  have hmono : ((integralComponentAt x).support : Set X) ∩
      ((Stacks.Divisors.zeroScheme X L' s').support : Set X) ⊆
        ((integralComponentAt x).support : Set X) ∩
          (((Stacks.Divisors.zeroScheme X L s).support : Set X) ∩
            ((Stacks.Divisors.zeroScheme X L' s').support : Set X)) :=
    fun y hy ↦ ⟨hy.1, hsubD hy.1, hy.2⟩
  have ha := isRationallyEquivalentToZeroWithin_properPushforward_gysinRuleInter_cycle_sub_of_le
    C p k L L' s s' zD hDimzD
    (m' := Stacks.Divisors.pullbackStalkAt (Stacks.Divisors.zeroScheme X L s).subschemeι L' zD
      hzD (componentGeneratorAt L' s' x))
    (fun hle ↦ Stacks.Divisors.IsStalkBasis.pullbackStalkAt
      (Stacks.Divisors.zeroScheme X L s).subschemeι L' zD hzD
      (isStalkBasis_componentGeneratorAt_of_le L' s' (hiff.1 hle)))
    (fun hnle ↦ by
      rw [componentGeneratorAt_of_not_le L' s' fun hle ↦ hnle (hiff.2 hle),
        pullbackStalkAt_germ_top L' s' (Stacks.Divisors.zeroScheme X L s).subschemeι zD hzD])
  have hcarr : ((integralComponentAt
        ((Stacks.Divisors.zeroScheme X L s).subschemeι.base zD)).support : Set X) ∩
      (((Stacks.Divisors.zeroScheme X L s).support : Set X) ∩
        ((Stacks.Divisors.zeroScheme X L' s').support : Set X)) ⊆
      ((integralComponentAt x).support : Set X) ∩
        (((Stacks.Divisors.zeroScheme X L s).support : Set X) ∩
          ((Stacks.Divisors.zeroScheme X L' s').support : Set X)) :=
    fun y hy ↦ ⟨hzD ▸ hy.1, hy.2⟩
  have hb :=
    isRationallyEquivalentToZeroWithin_properPushforward_chernCycleOfRestrictedStalk_ambient
    C p k L' s' ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
    (Stacks.Divisors.zeroScheme X L s).subschemeι rfl zD hzD hDimzD hDimZ
    (isStalkBasis_componentGeneratorAt_of_le L' s') (componentGeneratorAt_of_not_le L' s')
  have hc :=
    isRationallyEquivalentToZeroWithin_properPushforward_chernCycleOfRestrictedStalk_ambient
    C p k L' s' ((integralComponentAt ξ).subschemeι ≫ p)
    (integralComponentAt ξ).subschemeι rfl wW hwW hDimwW hDimZ
    (isStalkBasis_componentGeneratorAt_of_le L' s') (componentGeneratorAt_of_not_le L' s')
  have hb2 : IsRationallyEquivalentToZeroWithin C p k
      (properPushforward C ((integralComponentAt zD).subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          ((integralComponentAt zD).subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι) (Category.assoc _ _ _) k
          (chernCycleOfRestrictedStalk C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
            (zeroSchemeRestrictModule L L' s) (integralComponentAt zD)
            (isIntegral_integralComponentAt zD) hDimzD
            (genericPointOf_integralComponentAt zD)
            (Stacks.Divisors.pullbackStalkAt (Stacks.Divisors.zeroScheme X L s).subschemeι L' zD
              hzD (componentGeneratorAt L' s' x))) -
        properPushforward C ((integralComponentAt x).subschemeι ≫ p) p
          (integralComponentAt x).subschemeι rfl k
          (chernCycleOfRestrictedStalk C p k L' (integralComponentAt x)
            (isIntegral_integralComponentAt x) hDimZ (genericPointOf_integralComponentAt x)
            (componentGeneratorAt L' s' x)))
      (((integralComponentAt x).support : Set X) ∩
        ((Stacks.Divisors.zeroScheme X L' s').support : Set X)) := hb
  have hc2 : IsRationallyEquivalentToZeroWithin C p k
      (properPushforward C ((integralComponentAt wW).subschemeι ≫
            (integralComponentAt ξ).subschemeι ≫ p) p
          ((integralComponentAt wW).subschemeι ≫ (integralComponentAt ξ).subschemeι)
          (Category.assoc _ _ _) k
          (chernCycleOfRestrictedStalk C ((integralComponentAt ξ).subschemeι ≫ p) k
            ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L')
            (integralComponentAt wW) (isIntegral_integralComponentAt wW) hDimwW
            (genericPointOf_integralComponentAt wW)
            (Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L' wW hwW
              (componentGeneratorAt L' s' x))) -
        properPushforward C ((integralComponentAt x).subschemeι ≫ p) p
          (integralComponentAt x).subschemeι rfl k
          (chernCycleOfRestrictedStalk C p k L' (integralComponentAt x)
            (isIntegral_integralComponentAt x) hDimZ (genericPointOf_integralComponentAt x)
            (componentGeneratorAt L' s' x)))
      (((integralComponentAt x).support : Set X) ∩
        ((Stacks.Divisors.zeroScheme X L' s').support : Set X)) := hc
  refine isRationallyEquivalentToZeroWithin_sub C p k
    (isRationallyEquivalentToZeroWithin_add C p k (ha.mono hcarr) (hb2.mono hmono))
    (hc2.mono hmono)
    fun y ↦ ?_
  show (_ : ℤ) - _ = ((_ - _) + (_ - _)) - (_ - _)
  ring

end Member

/-! ### Local finiteness of a family of images -/

/-- The images of a locally finite family under a closed embedding form a locally finite
family. -/
theorem locallyFinite_image_of_isClosedEmbedding {A B I : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {f : A → B} (hf : Topology.IsClosedEmbedding f) {F : I → Set A}
    (hF : LocallyFinite F) : LocallyFinite fun i ↦ f '' F i := by
  intro b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    obtain ⟨t, ht, hfin⟩ := hF a
    obtain ⟨V, hVt, hV, haV⟩ := mem_nhds_iff.mp ht
    obtain ⟨O, hO, hOV⟩ := hf.isEmbedding.isInducing.isOpen_iff.mp hV
    refine ⟨O, hO.mem_nhds (by rw [← hOV] at haV; exact haV), hfin.subset ?_⟩
    rintro i ⟨-, ⟨x, hx, rfl⟩, hxO⟩
    exact ⟨x, hx, hVt (by rw [← hOV]; exact hxO)⟩
  · refine ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl.mem_nhds hb, ?_⟩
    have hzero : {i : I | ((fun i ↦ f '' F i) i ∩ (Set.range f)ᶜ).Nonempty} = ∅ := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, ⟨x, -, rfl⟩, h⟩
      exact h ⟨x, rfl⟩
    rw [hzero]
    exact Set.finite_empty

/-- For a closed immersion `j : V ⟶ X` and points `v, w` of `V`, the fundamental cycle of the
integral closed subscheme of `X` through `j v` has at `j w` the coefficient that the fundamental
cycle of the integral closed subscheme of `V` through `v` has at `w`. -/
theorem cycleAssociatedToClosedSubscheme_integralComponentAt_base (C : ChowSituation.{u})
    {X V : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (sV : V ⟶ C.S)
    [LocallyOfFiniteType sV] (j : V ⟶ X) [IsClosedImmersion j] (v : V)
    {k : ℤ} (hDimV : schemeDeltaDimension C ((integralComponentAt v).subschemeι ≫ sV) =
      (k : EInt))
    (hDimX : schemeDeltaDimension C ((integralComponentAt (j.base v)).subschemeι ≫ p) =
      (k : EInt)) (w : V) :
    (cycleAssociatedToClosedSubscheme C p (integralComponentAt (j.base v)).subschemeι k).1
        (j.base w) =
      (cycleAssociatedToClosedSubscheme C sV (integralComponentAt v).subschemeι k).1 w := by
  by_cases hw : w = v
  · subst hw
    have h1 := cycleAssociatedToClosedSubscheme_integral_apply C p
      (integralComponentAt (j.base w)) (isIntegral_integralComponentAt _) hDimX
    have h2 := cycleAssociatedToClosedSubscheme_integral_apply C sV (integralComponentAt w)
      (isIntegral_integralComponentAt _) hDimV
    rw [genericPointOf_integralComponentAt] at h1 h2
    rw [h1, h2]
  · rw [cycleAssociatedToClosedSubscheme_integral_apply_of_ne C p
      (integralComponentAt (j.base v)) (isIntegral_integralComponentAt _) k
      (by rw [genericPointOf_integralComponentAt]; exact fun he ↦
        hw (j.isClosedEmbedding.injective he)),
    cycleAssociatedToClosedSubscheme_integral_apply_of_ne C sV (integralComponentAt v)
      (isIntegral_integralComponentAt _) k
      (by rw [genericPointOf_integralComponentAt]; exact hw)]

/-! ### The key formula situation on the component through a point -/

section Situation

attribute [local instance] isIntegral_integralComponentAt

variable {X : Scheme.{u}} (L L' : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']
  (s : Γ(L, ⊤)) (s' : Γ(L', ⊤)) (ξ : X)
  [IsLocallyNoetherian (integralComponentAt ξ).subscheme]

/-- The restriction to the integral closed subscheme `Z_ξ` of the generator of `L` prescribed at
`ξ`, read as a meromorphic section of `L|_{Z_ξ}`. -/
abbrev restrictedComponentSection :
    ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L).presheaf.stalk
      (genericPoint (integralComponentAt ξ).subscheme) :=
  Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L
    (genericPoint (integralComponentAt ξ).subscheme) (genericPointOf_integralComponentAt ξ)
    (componentGeneratorAt L s ξ)

/-- The restricted generator generates the generic stalk of `L|_{Z_ξ}`. -/
theorem isStalkBasis_restrictedComponentSection :
    IsStalkBasis ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L)
      (genericPoint (integralComponentAt ξ).subscheme) (restrictedComponentSection L s ξ) :=
  isStalkBasis_pullbackStalkAt_componentGeneratorAt L s (integralComponentAt ξ)
    (genericPoint (integralComponentAt ξ).subscheme) (genericPointOf_integralComponentAt ξ)

/-- The restricted generator is a nonzero meromorphic section. -/
theorem restrictedComponentSection_ne_zero : restrictedComponentSection L s ξ ≠ 0 := by
  intro h
  have h01 : (0 : (integralComponentAt ξ).subscheme.presheaf.stalk
      (genericPoint (integralComponentAt ξ).subscheme)) = 1 :=
    (isStalkBasis_restrictedComponentSection L s ξ).injective (by simp only [h, smul_zero])
  exact zero_ne_one (α := (integralComponentAt ξ).subscheme.functionField) h01

/-- The `KeyFormulaSituation` on `Z_ξ` whose two meromorphic sections are the restrictions of the
generators of `L` and `L'` prescribed at `ξ`, and whose chosen generators at each member of the
family are the restrictions of the generators prescribed at the image of its generic point. -/
def componentSituation : KeyFormulaSituation
    ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L)
    ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L') :=
  let ℱ₀ := keyFormulaSituationOf
    ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L)
    ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L')
    (restrictedComponentSection L s ξ) (restrictedComponentSection L' s' ξ)
    (restrictedComponentSection_ne_zero L s ξ) (restrictedComponentSection_ne_zero L' s' ξ)
  { ℱ₀ with
    localGeneratorL := fun i ↦
      Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L
        (ℱ₀.componentPoint i) rfl (componentGeneratorAt L s
          ((integralComponentAt ξ).subschemeι.base (ℱ₀.componentPoint i)))
    localGeneratorN := fun i ↦
      Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L'
        (ℱ₀.componentPoint i) rfl (componentGeneratorAt L' s'
          ((integralComponentAt ξ).subschemeι.base (ℱ₀.componentPoint i)))
    isStalkBasis_localGeneratorL := fun i ↦
      isStalkBasis_pullbackStalkAt_componentGeneratorAt L s (integralComponentAt ξ)
        (ℱ₀.componentPoint i) rfl
    isStalkBasis_localGeneratorN := fun i ↦
      isStalkBasis_pullbackStalkAt_componentGeneratorAt L' s' (integralComponentAt ξ)
        (ℱ₀.componentPoint i) rfl }

/-- The first meromorphic section of `componentSituation` is the restricted generator of `L`. -/
@[simp]
theorem componentSituation_sectionL :
    (componentSituation L L' s s' ξ).sectionL = restrictedComponentSection L s ξ := rfl

/-- The second meromorphic section of `componentSituation` is the restricted generator of
`L'`. -/
@[simp]
theorem componentSituation_sectionN :
    (componentSituation L L' s s' ξ).sectionN = restrictedComponentSection L' s' ξ := rfl

/-- The chosen generator of `L` at a member of `componentSituation` is the restriction of the
generator of `L` prescribed at the image of its generic point. -/
@[simp]
theorem componentSituation_localGeneratorL (i : (componentSituation L L' s s' ξ).Index) :
    (componentSituation L L' s s' ξ).localGeneratorL i =
      Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L
        ((componentSituation L L' s s' ξ).componentPoint i) rfl
        (componentGeneratorAt L s ((integralComponentAt ξ).subschemeι.base
          ((componentSituation L L' s s' ξ).componentPoint i))) := rfl

/-- The chosen generator of `L'` at a member of `componentSituation` is the restriction of the
generator of `L'` prescribed at the image of its generic point. -/
@[simp]
theorem componentSituation_localGeneratorN (i : (componentSituation L L' s s' ξ).Index) :
    (componentSituation L L' s s' ξ).localGeneratorN i =
      Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L'
        ((componentSituation L L' s s' ξ).componentPoint i) rfl
        (componentGeneratorAt L' s' ((integralComponentAt ξ).subschemeι.base
          ((componentSituation L L' s s' ξ).componentPoint i))) := rfl

end Situation

/-! ### Swapping the two pairs of a situation -/

section Swap

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] {M M' : Y.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M']

/-- A `KeyFormulaSituation` with its two pairs exchanged: the family and its chosen generators are
the same, and the roles of the two invertible modules are swapped. -/
def KeyFormulaSituation.swap (ℱ : KeyFormulaSituation M M') : KeyFormulaSituation M' M where
  sectionL := ℱ.sectionN
  sectionL_ne_zero := ℱ.sectionN_ne_zero
  sectionN := ℱ.sectionL
  sectionN_ne_zero := ℱ.sectionL_ne_zero
  Index := ℱ.Index
  component := ℱ.component
  component_injective := ℱ.component_injective
  locallyFinite_component := ℱ.locallyFinite_component
  isCoordinateAt_one_of_notMem Z hZ := ⟨(ℱ.isCoordinateAt_one_of_notMem Z hZ).2,
    (ℱ.isCoordinateAt_one_of_notMem Z hZ).1⟩
  localGeneratorL := ℱ.localGeneratorN
  localGeneratorN := ℱ.localGeneratorL
  isStalkBasis_localGeneratorL := ℱ.isStalkBasis_localGeneratorN
  isStalkBasis_localGeneratorN := ℱ.isStalkBasis_localGeneratorL

omit [IsLocallyNoetherian Y] in
/-- The first section of the swapped situation is the second section of the original. -/
@[simp]
theorem KeyFormulaSituation.swap_sectionL (ℱ : KeyFormulaSituation M M') :
    ℱ.swap.sectionL = ℱ.sectionN := rfl

omit [IsLocallyNoetherian Y] in
/-- The second chosen generators of the swapped situation are the first ones of the original. -/
@[simp]
theorem KeyFormulaSituation.swap_localGeneratorN (ℱ : KeyFormulaSituation M M') (i : ℱ.Index) :
    ℱ.swap.localGeneratorN i = ℱ.localGeneratorL i := rfl

omit [IsLocallyNoetherian Y] in
/-- The swapped situation has the same members as the original. -/
@[simp]
theorem KeyFormulaSituation.swap_componentPoint (ℱ : KeyFormulaSituation M M') (i : ℱ.Index) :
    ℱ.swap.componentPoint i = ℱ.componentPoint i := rfl

/-- The first orders of vanishing of the swapped situation are the second ones of the original. -/
@[simp]
theorem KeyFormulaSituation.swap_orderL (ℱ : KeyFormulaSituation M M') (i : ℱ.Index) :
    ℱ.swap.orderL i = ℱ.orderN i := rfl

end Swap

/-! ### Adding two carried rational equivalences -/

section Generic

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)

/-- Let `A = ∑ᶠ j, u j` and `B = ∑ᶠ j, v j` coefficientwise, where `u j` and `v j` are supported
in `F j` for a locally finite family `F`. If each `u j - v j` is rationally equivalent to zero
within `E j`, for a locally finite family `E`, then `A - B` is rationally equivalent to zero
within `⋃ j, E j`. -/
theorem isRationallyEquivalentToZeroWithin_sub_of_finsum_of_subset {J : Type u}
    (E F : J → Set X) (hE : LocallyFinite E) (hF : LocallyFinite F)
    (A B : CycleGroup C p k) (u v : J → CycleGroup C p k)
    (hu : ∀ j, Function.support (u j).1 ⊆ F j) (hv : ∀ j, Function.support (v j).1 ⊆ F j)
    (hA : ∀ x : X, A.1 x = ∑ᶠ j : J, (u j).1 x)
    (hB : ∀ x : X, B.1 x = ∑ᶠ j : J, (v j).1 x)
    (hD : ∀ j, IsRationallyEquivalentToZeroWithin C p k (u j - v j) (E j)) :
    IsRationallyEquivalentToZeroWithin C p k (A - B) (⋃ j, E j) := by
  refine rationallyEquivalentToZeroWithin_finsum C p k (fun j ↦ u j - v j) E hE hD fun x ↦ ?_
  have hfu : Function.HasFiniteSupport fun j : J ↦ (u j).1 x :=
    (hF.point_finite x).subset fun j hj ↦ hu j (by exact hj)
  have hfv : Function.HasFiniteSupport fun j : J ↦ (v j).1 x :=
    (hF.point_finite x).subset fun j hj ↦ hv j (by exact hj)
  have hpt : (A - B).1 x = A.1 x - B.1 x := by simp
  rw [hpt, hA x, hB x, ← finsum_sub_distrib hfu hfv]
  exact finsum_congr fun j ↦ by simp

/-- Proper pushforward commutes with an integer multiple. -/
theorem properPushforward_zsmul {Z : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (f : Z ⟶ X) [IsProper f] (hf : f ≫ p = sZ) (m : ℤ) (c : CycleGroup C sZ k) :
    properPushforward C sZ p f hf k (m • c) = m • properPushforward C sZ p f hf k c :=
  map_zsmul (properPushforwardHom C sZ p f hf k) m c

/-- If `a`, `b` and `c` are rationally equivalent to zero within `T` and `d = a - b + c`
coefficientwise, then `d` is rationally equivalent to zero within `T`. -/
theorem isRationallyEquivalentToZeroWithin_sub_add {a b c d : CycleGroup C p k} {T : Set X}
    (ha : IsRationallyEquivalentToZeroWithin C p k a T)
    (hb : IsRationallyEquivalentToZeroWithin C p k b T)
    (hc : IsRationallyEquivalentToZeroWithin C p k c T)
    (hd : ∀ y : X, d.1 y = a.1 y - b.1 y + c.1 y) :
    IsRationallyEquivalentToZeroWithin C p k d T := by
  have hnb : IsRationallyEquivalentToZeroWithin C p k (-b) T :=
    isRationallyEquivalentToZeroWithin_of_eq_neg C p k hb fun y ↦ rfl
  refine isRationallyEquivalentToZeroWithin_zsmul C p k
    (isRationallyEquivalentToZeroWithin_add C p k
      (isRationallyEquivalentToZeroWithin_add C p k ha hnb) hc) 1 fun y ↦ ?_
  rw [hd y, one_mul]
  show a.1 y - b.1 y + c.1 y = a.1 y + -b.1 y + c.1 y
  ring

/-- If `α` and `β` are rationally equivalent to zero within `T` and `γ = α + β`
coefficientwise, then `γ` is rationally equivalent to zero within `T`. -/
theorem isRationallyEquivalentToZeroWithin_add_of {α β γ : CycleGroup C p k} {T : Set X}
    (hα : IsRationallyEquivalentToZeroWithin C p k α T)
    (hβ : IsRationallyEquivalentToZeroWithin C p k β T)
    (hγ : ∀ y : X, γ.1 y = α.1 y + β.1 y) :
    IsRationallyEquivalentToZeroWithin C p k γ T := by
  refine isRationallyEquivalentToZeroWithin_zsmul C p k
    (isRationallyEquivalentToZeroWithin_add C p k hα hβ) 1 fun y ↦ ?_
  rw [hγ y, one_mul]
  show _ = α.1 y + β.1 y
  rfl

end Generic

/-! ### One iterated Gysin cycle, presented by the family of the key formula -/

section Assembly

attribute [local instance] isIntegral_integralComponentAt

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L L' : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']
  (s : Γ(L, ⊤)) (s' : Γ(L', ⊤)) (ξ : X)
  [IsLocallyNoetherian (integralComponentAt ξ).subscheme]
  (ℱ : KeyFormulaSituation
    ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L)
    ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L'))

omit [IsLocallyNoetherian (integralComponentAt ξ).subscheme] in
/-- If `Z_ξ` has delta-dimension `k + 2`, each member of the family of a situation on `Z_ξ` has
delta-dimension `k + 1`. -/
theorem schemeDeltaDimension_componentPoint
    (hDimW : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt)) (i : ℱ.Index) :
    schemeDeltaDimension C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫
      (integralComponentAt ξ).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt) :=
  ℱ.schemeDeltaDimension_integralComponentAt_componentPoint C
    ((integralComponentAt ξ).subschemeι ≫ p) k
    (by rw [hDimW, show (k + 1 + 1 : ℤ) = k + 2 from by ring]) i

omit [IsLocallyNoetherian (integralComponentAt ξ).subscheme] in
/-- The member of the family, read as an integral closed subscheme of the ambient scheme, has
delta-dimension `k + 1`. -/
theorem schemeDeltaDimension_base_componentPoint
    (hDimW : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt)) (i : ℱ.Index) :
    schemeDeltaDimension C ((integralComponentAt
        ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i))).subschemeι ≫ p) =
      ((k + 1 : ℤ) : EInt) := by
  obtain ⟨ε, hε⟩ := exists_iso_integralComponentAt_comp (integralComponentAt ξ).subschemeι
    (ℱ.componentPoint i)
  refine (schemeDeltaDimension_of_iso C
    ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫
      (integralComponentAt ξ).subschemeι ≫ p)
    ((integralComponentAt ((integralComponentAt ξ).subschemeι.base
      (ℱ.componentPoint i))).subschemeι ≫ p) ε
    (by rw [← Category.assoc, hε, Category.assoc])).trans
    (schemeDeltaDimension_componentPoint C p k L L' ξ ℱ hDimW i)

omit [IsLocallyNoetherian (integralComponentAt ξ).subscheme] in
/-- `f_i = 1` at every member of the family lying off the zero scheme of `s`. -/
theorem ratioL_eq_one_of_not_le
    (hsectionL : ℱ.sectionL = restrictedComponentSection L s ξ)
    (hgenL : ∀ i, ℱ.localGeneratorL i =
      Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L
        (ℱ.componentPoint i) rfl (componentGeneratorAt L s
          ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i))))
    (i : ℱ.Index) (hP : ¬ Stacks.Divisors.zeroScheme X L s ≤
      integralComponentAt ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i))) :
    ℱ.ratioL i = 1 := by
  have hPξ : ¬ Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt ξ := fun hle ↦
    hP (hle.trans ((le_integralComponentAt_iff_mem_support (integralComponentAt ξ) _).2
      (subschemeι_base_mem_support_integralComponentAt ξ (ℱ.componentPoint i))))
  refine (ℱ.ratioL_eq_one_iff i).mpr ?_
  have h1 : ℱ.localGeneratorL i = ((Scheme.Modules.pullback
      (integralComponentAt ξ).subschemeι).obj L).presheaf.germ ⊤ (ℱ.componentPoint i) trivial
      (AlgebraicGeometry.pullbackGlobalSections (integralComponentAt ξ).subschemeι L s) := by
    rw [hgenL i, componentGeneratorAt_of_not_le L s hP,
      pullbackStalkAt_germ_top L s (integralComponentAt ξ).subschemeι (ℱ.componentPoint i) rfl]
  have h2 : ℱ.sectionL = ((Scheme.Modules.pullback
      (integralComponentAt ξ).subschemeι).obj L).presheaf.germ ⊤
      (genericPoint (integralComponentAt ξ).subscheme) trivial
      (AlgebraicGeometry.pullbackGlobalSections (integralComponentAt ξ).subschemeι L s) := by
    rw [hsectionL]
    show Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L
      (genericPoint (integralComponentAt ξ).subscheme) (genericPointOf_integralComponentAt ξ)
      (componentGeneratorAt L s ξ) = _
    rw [componentGeneratorAt_of_not_le L s hPξ,
      pullbackStalkAt_germ_top L s (integralComponentAt ξ).subschemeι
        (genericPoint (integralComponentAt ξ).subscheme) (genericPointOf_integralComponentAt ξ)]
  rw [h1, h2]
  exact Stacks.Divisors.toGenericStalk_germ
    (L := (Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L) (W := ⊤)
    (x := ℱ.componentPoint i) trivial trivial _

/-- `ord_{Z_i}(s) = 0` at every member of the family lying off the zero scheme of `s`. -/
theorem orderL_eq_zero_of_not_le
    (hsectionL : ℱ.sectionL = restrictedComponentSection L s ξ)
    (hgenL : ∀ i, ℱ.localGeneratorL i =
      Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L
        (ℱ.componentPoint i) rfl (componentGeneratorAt L s
          ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i))))
    (i : ℱ.Index) (hP : ¬ Stacks.Divisors.zeroScheme X L s ≤
      integralComponentAt ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i))) :
    ℱ.orderL i = 0 := by
  rw [ℱ.orderL_eq_ord_ratioL i, ratioL_eq_one_of_not_le L L' s ξ ℱ hsectionL hgenL i hP,
    ← map_one (algebraMap ((integralComponentAt ξ).subscheme.presheaf.stalk
      (ℱ.componentPoint i)) (integralComponentAt ξ).subscheme.functionField)]
  exact Scheme.ord_algebraMap_of_isUnit (ℱ.coheight_componentPoint i) isUnit_one

omit [IsLocallyNoetherian (integralComponentAt ξ).subscheme] in
/-- The family of members of the situation, read as integral closed subschemes of the ambient
scheme, is locally finite. -/
theorem locallyFinite_support_base_componentPoint :
    LocallyFinite fun i : ℱ.Index ↦ ((integralComponentAt
      ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i))).support : Set X) := by
  have heq : (fun i : ℱ.Index ↦ ((integralComponentAt
        ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i))).support : Set X)) =
      fun i : ℱ.Index ↦ (integralComponentAt ξ).subschemeι.base ''
        (((integralComponentAt (ℱ.componentPoint i)).support :
          Set (integralComponentAt ξ).subscheme)) := by
    funext i
    rw [coe_support_integralComponentAt, coe_support_integralComponentAt, ← Set.image_singleton,
      ((integralComponentAt ξ).subschemeι.isClosedEmbedding).closure_image_eq]
  rw [heq]
  exact locallyFinite_image_of_isClosedEmbedding
    ((integralComponentAt ξ).subschemeι.isClosedEmbedding)
    ℱ.locallyFinite_support_integralComponentAt

/-- If the first meromorphic section of the situation is the restriction of the generator of `L`
prescribed at `ξ`, then the divisor of that generator on `Z_ξ`, pushed forward to `X`, is
`∑ᶠ i, ord_{Z_i}(s) [Z_i]`, each member `Z_i` read as an integral closed subscheme of `X`. -/
theorem componentDivisorPushforward_apply_finsum
    (hDimW : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt))
    (hsectionL : ℱ.sectionL = restrictedComponentSection L s ξ) (y : X) :
    (componentDivisorPushforward C p k L ξ hDimW (componentGeneratorAt L s ξ)).1 y =
      ∑ᶠ i : ℱ.Index, ℱ.orderL i *
        (cycleAssociatedToClosedSubscheme C p (integralComponentAt
          ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i))).subschemeι
          (k + 1)).1 y := by
  have hdimX := schemeDeltaDimension_base_componentPoint C p k L L' ξ ℱ hDimW
  have hsec : Stacks.Chow.restrictStalk (integralComponentAt ξ) L
      (genericPointOf_integralComponentAt ξ) (componentGeneratorAt L s ξ) = ℱ.sectionL :=
    hsectionL.symm
  have hval : (chernCycleOfRestrictedStalk C p (k + 1) L (integralComponentAt ξ)
        (isIntegral_integralComponentAt ξ) hDimW (genericPointOf_integralComponentAt ξ)
        (componentGeneratorAt L s ξ)).1 = weilDivisorAlgebraicCycle ℱ.weilDivisorL := by
    show weilDivisorAlgebraicCycle (Stacks.Divisors.weilDivisorOfMeromorphicSection
      (isTrivializedNear_restrictModule (integralComponentAt ξ) L)
      (Stacks.Chow.restrictStalk (integralComponentAt ξ) L
        (genericPointOf_integralComponentAt ξ) (componentGeneratorAt L s ξ))) = _
    rw [hsec]
  have hdef : componentDivisorPushforward C p k L ξ hDimW (componentGeneratorAt L s ξ) =
      properPushforward C ((integralComponentAt ξ).subschemeι ≫ p) p
        (integralComponentAt ξ).subschemeι rfl (k + 1)
        (chernCycleOfRestrictedStalk C p (k + 1) L (integralComponentAt ξ)
          (isIntegral_integralComponentAt ξ) hDimW
          (genericPointOf_integralComponentAt ξ) (componentGeneratorAt L s ξ)) := rfl
  by_cases hr : y ∈ Set.range (integralComponentAt ξ).subschemeι.base
  · obtain ⟨w, rfl⟩ := hr
    rw [hdef, properPushforward_apply_image_of_isClosedImmersion,
      show (chernCycleOfRestrictedStalk C p (k + 1) L (integralComponentAt ξ)
            (isIntegral_integralComponentAt ξ) hDimW (genericPointOf_integralComponentAt ξ)
            (componentGeneratorAt L s ξ)).1 w =
          weilDivisorAlgebraicCycle ℱ.weilDivisorL w from by rw [hval],
      ℱ.weilDivisorAlgebraicCycle_weilDivisorL_apply C
        ((integralComponentAt ξ).subschemeι ≫ p) k
        (by rw [hDimW, show (k + 1 + 1 : ℤ) = k + 2 from by ring]) w]
    exact finsum_congr fun i ↦ congrArg (ℱ.orderL i * ·)
      (cycleAssociatedToClosedSubscheme_integralComponentAt_base C p
        ((integralComponentAt ξ).subschemeι ≫ p) (integralComponentAt ξ).subschemeι
        (ℱ.componentPoint i)
        (schemeDeltaDimension_componentPoint C p k L L' ξ ℱ hDimW i) (hdimX i) w).symm
  · rw [hdef, properPushforward_apply_of_notMem_range C
      ((integralComponentAt ξ).subschemeι ≫ p) p
      (integralComponentAt ξ).subschemeι rfl (k + 1) _ hr]
    refine ((finsum_congr fun i ↦ ?_).trans finsum_zero).symm
    rw [cycleAssociatedToClosedSubscheme_integral_apply_of_ne C p
      (integralComponentAt ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i)))
      (isIntegral_integralComponentAt _) (k + 1)
      (by rw [genericPointOf_integralComponentAt]
          exact fun he ↦ hr ⟨ℱ.componentPoint i, he.symm⟩), mul_zero]

/-- The same sum, taken only over the members of the family lying in the zero scheme of `s`. -/
theorem componentDivisorPushforward_apply_finsum_subtype
    (hDimW : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt))
    (hsectionL : ℱ.sectionL = restrictedComponentSection L s ξ)
    (hgenL : ∀ i, ℱ.localGeneratorL i =
      Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L
        (ℱ.componentPoint i) rfl (componentGeneratorAt L s
          ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i)))) (y : X) :
    (componentDivisorPushforward C p k L ξ hDimW (componentGeneratorAt L s ξ)).1 y =
      ∑ᶠ j : {i : ℱ.Index // Stacks.Divisors.zeroScheme X L s ≤
          integralComponentAt ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i))},
        ℱ.orderL j.1 * (cycleAssociatedToClosedSubscheme C p (integralComponentAt
          ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint j.1))).subschemeι
          (k + 1)).1 y := by
  rw [componentDivisorPushforward_apply_finsum C p k L L' s ξ ℱ hDimW hsectionL y]
  exact finsum_eq_finsum_subtype _ fun i hi ↦ by
    rw [orderL_eq_zero_of_not_le L L' s ξ ℱ hsectionL hgenL i hi, zero_mul]

omit [IsLocallyNoetherian (integralComponentAt ξ).subscheme] in
/-- The generic point of a member lying in the zero scheme is in the image of the zero scheme. -/
theorem mem_range_subschemeι_componentPoint
    (j : {i : ℱ.Index // Stacks.Divisors.zeroScheme X L s ≤
      integralComponentAt ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i))}) :
    genericPointOf (integralComponentAt ((integralComponentAt ξ).subschemeι.base
        (ℱ.componentPoint j.1))) (isIntegral_integralComponentAt _) ∈
      Set.range (Stacks.Divisors.zeroScheme X L s).subschemeι.base := by
  rw [genericPointOf_integralComponentAt, Scheme.IdealSheafData.range_subschemeι]
  exact (le_integralComponentAt_iff_mem_support _ _).1 j.2

omit [IsLocallyNoetherian (integralComponentAt ξ).subscheme] in
/-- The selected members form a locally finite family. -/
theorem locallyFinite_support_subtype_componentPoint :
    LocallyFinite fun j : {i : ℱ.Index // Stacks.Divisors.zeroScheme X L s ≤
        integralComponentAt ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i))} ↦
      ((integralComponentAt ((integralComponentAt ξ).subschemeι.base
        (ℱ.componentPoint j.1))).support : Set X) :=
  (locallyFinite_support_base_componentPoint L L' ξ ℱ).comp_injective Subtype.val_injective

omit [IsLocallyNoetherian (integralComponentAt ξ).subscheme] in
/-- If the divisor of an element `m` of the stalk of `L` at `ξ`, pushed forward to `X`, is the
locally finite combination `∑_j n_j [Z_j]` of the fundamental cycles of integral closed
subschemes lying in the zero scheme, then a rule on the integral components of the zero scheme
takes the corresponding combination of its values on the components above the `Z_j`. -/
theorem extendCycleGroup_descendedComponentDivisorCycle_apply_finsum
    {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    {g : Y ⟶ (Stacks.Divisors.zeroScheme X L s).subscheme}
    (R : IntegralComponentRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) sY g k)
    (hDimW : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt)) (m : L.presheaf.stalk ξ)
    {J : Type u} (V : J → X)
    (hmemV : ∀ j, genericPointOf (integralComponentAt (V j))
      (isIntegral_integralComponentAt (V j)) ∈
      Set.range (Stacks.Divisors.zeroScheme X L s).subschemeι.base)
    (hDimV : ∀ j, schemeDeltaDimension C ((integralComponentAt (V j)).subschemeι ≫ p) =
      ((k + 1 : ℤ) : EInt))
    (hLocalV : LocallyFinite fun j ↦ ((integralComponentAt (V j)).support : Set X))
    (n : J → ℤ)
    (hpres : ∀ y : X, (componentDivisorPushforward C p k L ξ hDimW m).1 y =
      ∑ᶠ j : J, n j * (cycleAssociatedToClosedSubscheme C p
        (integralComponentAt (V j)).subschemeι (k + 1)).1 y) (y : Y) :
    (R.extendCycleGroup
        (descendedComponentDivisorCycle C p k L s ξ hDimW m)).1 y =
      ∑ᶠ j : J, n j * (R.cycle
        (integralComponentAbove (Stacks.Divisors.zeroScheme X L s).subschemeι
          (integralComponentAt (V j)) (isIntegral_integralComponentAt (V j)) (hmemV j))
        (isIntegral_integralComponentAbove _ _ _ _)
        (schemeDeltaDimension_integralComponentAbove C p
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (integralComponentAt (V j))
          (isIntegral_integralComponentAt (V j)) (hmemV j) (hDimV j))).1 y :=
  extendCycleGroup_cyclePullbackAlongClosedImmersion_apply_of_presentation C p
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
    (Stacks.Divisors.zeroScheme X L s).subschemeι rfl R
    (fun j ↦ integralComponentAt (V j)) (fun j ↦ isIntegral_integralComponentAt (V j)) hDimV
    hmemV hLocalV n (componentDivisorPushforward C p k L ξ hDimW m) hpres y

omit [IsLocallyNoetherian (integralComponentAt ξ).subscheme] in
/-- The image in `X` of the `i`-th member of the family is the integral closed subscheme through
the image of its generic point. -/
theorem range_subschemeι_comp_componentPoint (i : ℱ.Index) :
    Set.range ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫
        (integralComponentAt ξ).subschemeι).base =
      ((integralComponentAt ((integralComponentAt ξ).subschemeι.base
        (ℱ.componentPoint i))).support : Set X) := by
  obtain ⟨ε, hε⟩ := exists_iso_integralComponentAt_comp (integralComponentAt ξ).subschemeι
    (ℱ.componentPoint i)
  rw [← hε, ← Scheme.IdealSheafData.range_subschemeι]
  refine Set.ext fun y ↦ ⟨?_, ?_⟩
  · rintro ⟨w, rfl⟩
    exact ⟨ε.hom.base w, rfl⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨v, rfl⟩ := surjective_base_hom_of_iso ε w
    exact ⟨v, rfl⟩

/-- The members of the family whose image in `X` lies in the zero scheme of `s`. -/
abbrev SelectedIndex : Type u :=
  {i : ℱ.Index // Stacks.Divisors.zeroScheme X L s ≤
    integralComponentAt ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i))}

variable (hDimW : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
  ((k + 1 + 1 : ℤ) : EInt))

/-- The outer Gysin cycle of a selected member of the family. -/
def memberGysinCycle (j : SelectedIndex L L' s ξ ℱ) :
    CycleGroup C ((zeroSchemeInter L L' s s').subschemeι ≫
      (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k :=
  (gysinRuleInter C p k L L' s s').cycle
    (integralComponentAbove (Stacks.Divisors.zeroScheme X L s).subschemeι
      (integralComponentAt ((integralComponentAt ξ).subschemeι.base
        (ℱ.componentPoint j.1))) (isIntegral_integralComponentAt _)
      (mem_range_subschemeι_componentPoint L L' s ξ ℱ j))
    (isIntegral_integralComponentAbove _ _ _ _)
    (schemeDeltaDimension_integralComponentAbove C p
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
      (Stacks.Divisors.zeroScheme X L s).subschemeι rfl _
      (isIntegral_integralComponentAt _)
      (mem_range_subschemeι_componentPoint L L' s ξ ℱ j)
      (schemeDeltaDimension_base_componentPoint C p k L L' ξ ℱ hDimW j.1))

/-- The outer Gysin cycle of a selected member, pushed forward to the ambient scheme. -/
def memberGysinPushforward (j : SelectedIndex L L' s ξ ℱ) : CycleGroup C p k :=
  properPushforward C ((zeroSchemeInter L L' s s').subschemeι ≫
      (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
    ((zeroSchemeInter L L' s s').subschemeι ≫
      (Stacks.Divisors.zeroScheme X L s).subschemeι) (Category.assoc _ _ _) k
    (memberGysinCycle C p k L L' s s' ξ ℱ hDimW j)

/-- The divisor `div_{L'|Z_i}(t_i|Z_i)` the key formula reads at the `i`-th member, pushed
forward to the ambient scheme. -/
def memberKeyFormulaDivisor (i : ℱ.Index) : CycleGroup C p k :=
  properPushforward C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫
      (integralComponentAt ξ).subschemeι ≫ p) p
    ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫
      (integralComponentAt ξ).subschemeι) (Category.assoc _ _ _) k
    (chernCycleOfRestrictedStalk C ((integralComponentAt ξ).subschemeι ≫ p) k
      ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L')
      (integralComponentAt (ℱ.componentPoint i))
      (isIntegral_integralComponentAt (ℱ.componentPoint i))
      (schemeDeltaDimension_componentPoint C p k L L' ξ ℱ hDimW i)
      (genericPointOf_integralComponentAt (ℱ.componentPoint i))
      (Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L'
        (ℱ.componentPoint i) rfl (componentGeneratorAt L' s'
          ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i)))))

/-- The outer Gysin cycle of a selected member is supported on that member. -/
theorem support_memberGysinPushforward_subset (j : SelectedIndex L L' s ξ ℱ) :
    Function.support (ℱ.orderL j.1 • memberGysinPushforward C p k L L' s s' ξ ℱ hDimW j).1 ⊆
      ((integralComponentAt ((integralComponentAt ξ).subschemeι.base
        (ℱ.componentPoint j.1))).support : Set X) := by
  intro y hy
  have hy' : (memberGysinPushforward C p k L L' s s' ξ ℱ hDimW j).1 y ≠ 0 :=
    right_ne_zero_of_mul (by exact hy)
  by_cases hr : y ∈ Set.range ((zeroSchemeInter L L' s s').subschemeι ≫
      (Stacks.Divisors.zeroScheme X L s).subschemeι).base
  · obtain ⟨z, rfl⟩ := hr
    rw [memberGysinPushforward, properPushforward_apply_image_of_isClosedImmersion] at hy'
    exact coe_support_integralComponentAbove_subset
      (Stacks.Divisors.zeroScheme X L s).subschemeι
      (integralComponentAt ((integralComponentAt ξ).subschemeι.base
        (ℱ.componentPoint j.1))) (isIntegral_integralComponentAt _)
      (mem_range_subschemeι_componentPoint L L' s ξ ℱ j)
      ((gysinRuleInter C p k L L' s s').support_subset _ _ _ (by exact hy'))
  · rw [memberGysinPushforward] at hy'
    exact absurd (properPushforward_apply_of_notMem_range C
      ((zeroSchemeInter L L' s s').subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
      ((zeroSchemeInter L L' s s').subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι) (Category.assoc _ _ _) k _ hr) hy'

/-- The divisor the key formula reads at a member is supported on that member. -/
theorem support_memberKeyFormulaDivisor_subset (i : ℱ.Index) :
    Function.support (ℱ.orderL i • memberKeyFormulaDivisor C p k L L' s' ξ ℱ hDimW i).1 ⊆
      ((integralComponentAt ((integralComponentAt ξ).subschemeι.base
        (ℱ.componentPoint i))).support : Set X) := by
  intro y hy
  have hy' : (memberKeyFormulaDivisor C p k L L' s' ξ ℱ hDimW i).1 y ≠ 0 :=
    right_ne_zero_of_mul (by exact hy)
  rw [memberKeyFormulaDivisor] at hy'
  rw [← range_subschemeι_comp_componentPoint L L' ξ ℱ i]
  exact support_properPushforward_subset C
    ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫
      (integralComponentAt ξ).subschemeι ≫ p) p
    ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫
      (integralComponentAt ξ).subschemeι) (Category.assoc _ _ _) k _ (by exact hy')

/-- For a selected member `Z_j`, `ord_{Z_j}(s)` times the difference of its outer Gysin cycle and
of the divisor the key formula reads there is rationally equivalent to zero within
`Z_j ∩ D ∩ D'`. -/
theorem isRationallyEquivalentToZeroWithin_memberGysinPushforward_sub
    (j : SelectedIndex L L' s ξ ℱ) :
    IsRationallyEquivalentToZeroWithin C p k
      (ℱ.orderL j.1 • memberGysinPushforward C p k L L' s s' ξ ℱ hDimW j -
        ℱ.orderL j.1 • memberKeyFormulaDivisor C p k L L' s' ξ ℱ hDimW j.1)
      (((integralComponentAt ((integralComponentAt ξ).subschemeι.base
          (ℱ.componentPoint j.1))).support : Set X) ∩
        (((Stacks.Divisors.zeroScheme X L s).support : Set X) ∩
          ((Stacks.Divisors.zeroScheme X L' s').support : Set X))) := by
  have hC : IsRationallyEquivalentToZeroWithin C p k
      (memberGysinPushforward C p k L L' s s' ξ ℱ hDimW j -
        memberKeyFormulaDivisor C p k L L' s' ξ ℱ hDimW j.1)
      (((integralComponentAt ((integralComponentAt ξ).subschemeι.base
          (ℱ.componentPoint j.1))).support : Set X) ∩
        (((Stacks.Divisors.zeroScheme X L s).support : Set X) ∩
          ((Stacks.Divisors.zeroScheme X L' s').support : Set X))) :=
    isRationallyEquivalentToZeroWithin_gysinRuleInter_cycle_sub_restricted C p k L L' s s' ξ
      j.2 (genericPointAbove (Stacks.Divisors.zeroScheme X L s).subschemeι
        (integralComponentAt ((integralComponentAt ξ).subschemeι.base
          (ℱ.componentPoint j.1))) (isIntegral_integralComponentAt _)
        (mem_range_subschemeι_componentPoint L L' s ξ ℱ j))
      ((base_genericPointAbove (Stacks.Divisors.zeroScheme X L s).subschemeι _ _ _).trans
        (genericPointOf_integralComponentAt _))
      (ℱ.componentPoint j.1) rfl
      (schemeDeltaDimension_base_componentPoint C p k L L' ξ ℱ hDimW j.1)
      (schemeDeltaDimension_integralComponentAbove C p
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl _
        (isIntegral_integralComponentAt _)
        (mem_range_subschemeι_componentPoint L L' s ξ ℱ j)
        (schemeDeltaDimension_base_componentPoint C p k L L' ξ ℱ hDimW j.1))
      (schemeDeltaDimension_componentPoint C p k L L' ξ ℱ hDimW j.1)
  refine isRationallyEquivalentToZeroWithin_zsmul C p k hC (ℱ.orderL j.1) fun y ↦ ?_
  show ℱ.orderL j.1 * _ - ℱ.orderL j.1 * _ = ℱ.orderL j.1 * (_ - _)
  ring

/-- The iterated Gysin cycle of `Z_ξ` taken through `D = Z(s)`, pushed forward to `X`, is the sum
over the selected members `Z_j` of `ord_{Z_j}(s)` times their outer Gysin cycles, pushed forward
to `X`. -/
theorem properPushforward_extendCycleGroup_descended_apply_finsum
    (hsectionL : ℱ.sectionL = restrictedComponentSection L s ξ)
    (hgenL : ∀ i, ℱ.localGeneratorL i =
      Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L
        (ℱ.componentPoint i) rfl (componentGeneratorAt L s
          ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i)))) (y : X) :
    (properPushforward C ((zeroSchemeInter L L' s s').subschemeι ≫
          (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        ((zeroSchemeInter L L' s s').subschemeι ≫
          (Stacks.Divisors.zeroScheme X L s).subschemeι) (Category.assoc _ _ _) k
        ((gysinRuleInter C p k L L' s s').extendCycleGroup
          (descendedComponentDivisorCycle C p k L s ξ hDimW
            (componentGeneratorAt L s ξ)))).1 y =
      ∑ᶠ j : SelectedIndex L L' s ξ ℱ,
        (ℱ.orderL j.1 • memberGysinPushforward C p k L L' s s' ξ ℱ hDimW j).1 y := by
  have hpresG : ∀ z : (zeroSchemeInter L L' s s').subscheme,
      ((gysinRuleInter C p k L L' s s').extendCycleGroup
          (descendedComponentDivisorCycle C p k L s ξ hDimW (componentGeneratorAt L s ξ))).1 z =
        ∑ᶠ j : SelectedIndex L L' s ξ ℱ,
          (ℱ.orderL j.1 • memberGysinCycle C p k L L' s s' ξ ℱ hDimW j).1 z := by
    intro z
    rw [extendCycleGroup_descendedComponentDivisorCycle_apply_finsum C p k L s ξ
      (gysinRuleInter C p k L L' s s') hDimW (componentGeneratorAt L s ξ)
      (fun j : SelectedIndex L L' s ξ ℱ ↦
        (integralComponentAt ξ).subschemeι.base (ℱ.componentPoint j.1))
      (mem_range_subschemeι_componentPoint L L' s ξ ℱ)
      (fun j ↦ schemeDeltaDimension_base_componentPoint C p k L L' ξ ℱ hDimW j.1)
      (locallyFinite_support_subtype_componentPoint L L' s ξ ℱ) (fun j ↦ ℱ.orderL j.1)
      (componentDivisorPushforward_apply_finsum_subtype C p k L L' s ξ ℱ hDimW hsectionL hgenL) z]
    refine finsum_congr fun j ↦ ?_
    rw [memberGysinCycle]
    rfl
  rw [properPushforward_apply_finsum_of_isClosedImmersion C
    ((zeroSchemeInter L L' s s').subschemeι ≫
      (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
    ((zeroSchemeInter L L' s s').subschemeι ≫
      (Stacks.Divisors.zeroScheme X L s).subschemeι) (Category.assoc _ _ _) k _
    (fun j : SelectedIndex L L' s ξ ℱ ↦
      ℱ.orderL j.1 • memberGysinCycle C p k L L' s s' ξ ℱ hDimW j) hpresG y]
  refine finsum_congr fun j ↦ ?_
  rw [memberGysinPushforward, properPushforward_zsmul]

/-- The iterated Gysin cycle of `W = Z_ξ` taken through `D = Z(s)`, pushed forward to `X`, differs
from `∑_i ord_{Z_i}(s) · (Z_i → X)_* div_{L'|Z_i}(t_i|Z_i)` by a cycle rationally equivalent to
zero with witnesses inside `W ∩ D ∩ D'`. -/
theorem isRationallyEquivalentToZeroWithin_properPushforward_gysinGysinComponentCycle_sub_sum
    (hsectionL : ℱ.sectionL = restrictedComponentSection L s ξ)
    (hgenL : ∀ i, ℱ.localGeneratorL i =
      Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L
        (ℱ.componentPoint i) rfl (componentGeneratorAt L s
          ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i))))
    (β : CycleGroup C p k)
    (hβ : ∀ y : X, β.1 y = ∑ᶠ i : ℱ.Index,
      (ℱ.orderL i • memberKeyFormulaDivisor C p k L L' s' ξ ℱ hDimW i).1 y) :
    IsRationallyEquivalentToZeroWithin C p k
      (properPushforward C ((zeroSchemeInter L L' s s').subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          ((zeroSchemeInter L L' s s').subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι) (Category.assoc _ _ _) k
          (gysinGysinComponentCycle C p k L L' s s' (integralComponentAt ξ)
            (isIntegral_integralComponentAt ξ) hDimW) - β)
      (((integralComponentAt ξ).support : Set X) ∩
        (((Stacks.Divisors.zeroScheme X L s).support : Set X) ∩
          ((Stacks.Divisors.zeroScheme X L' s').support : Set X))) := by
  have hBpres : ∀ y : X, β.1 y = ∑ᶠ j : SelectedIndex L L' s ξ ℱ,
      (ℱ.orderL j.1 • memberKeyFormulaDivisor C p k L L' s' ξ ℱ hDimW j.1).1 y := by
    intro y
    rw [hβ y]
    exact finsum_eq_finsum_subtype _ fun i hi ↦ by
      rw [orderL_eq_zero_of_not_le L L' s ξ ℱ hsectionL hgenL i hi, zero_smul]
      rfl
  have hsum := isRationallyEquivalentToZeroWithin_sub_of_finsum_of_subset C p k
    (fun j : SelectedIndex L L' s ξ ℱ ↦ ((integralComponentAt
        ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint j.1))).support : Set X) ∩
      (((Stacks.Divisors.zeroScheme X L s).support : Set X) ∩
        ((Stacks.Divisors.zeroScheme X L' s').support : Set X)))
    (fun j : SelectedIndex L L' s ξ ℱ ↦ ((integralComponentAt
        ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint j.1))).support : Set X))
    ((locallyFinite_support_subtype_componentPoint L L' s ξ ℱ).subset
      fun j ↦ Set.inter_subset_left)
    (locallyFinite_support_subtype_componentPoint L L' s ξ ℱ) _ β
    (fun j ↦ ℱ.orderL j.1 • memberGysinPushforward C p k L L' s s' ξ ℱ hDimW j)
    (fun j ↦ ℱ.orderL j.1 • memberKeyFormulaDivisor C p k L L' s' ξ ℱ hDimW j.1)
    (support_memberGysinPushforward_subset C p k L L' s s' ξ ℱ hDimW)
    (fun j ↦ support_memberKeyFormulaDivisor_subset C p k L L' s' ξ ℱ hDimW j.1)
    (properPushforward_extendCycleGroup_descended_apply_finsum C p k L L' s s' ξ ℱ hDimW
      hsectionL hgenL)
    hBpres (isRationallyEquivalentToZeroWithin_memberGysinPushforward_sub C p k L L' s s' ξ ℱ
      hDimW)
  refine isRationallyEquivalentToZeroWithin_add_of C p k
    (isRationallyEquivalentToZeroWithin_properPushforward_gysinGysinComponentCycle_sub_of_le
      C p k L L' s s' ξ hDimW (isStalkBasis_componentGeneratorAt_of_le L s)
      (componentGeneratorAt_of_not_le L s))
    (hsum.mono (Set.iUnion_subset fun j ↦ ?_)) fun y ↦ ?_
  · exact fun z hz ↦ ⟨coe_support_integralComponentAt_subset_of_mem _
      (subschemeι_base_mem_support_integralComponentAt ξ (ℱ.componentPoint j.1)) hz.1, hz.2⟩
  · show (_ : ℤ) - _ = (_ - _) + (_ - _)
    ring

/-! ### The left hand side of the key formula as a cycle -/

/-- The left hand side of the key formula of a datum, as a `k`-cycle on an integral scheme of
delta-dimension `k + 2`. -/
def leftCycleGroup {Y : Scheme.{u}} [IsIntegral Y] (D : KeyFormulaData Y) (q : Y ⟶ C.S)
    [LocallyOfFiniteType q] (hn : schemeDeltaDimension C q = ((k + 2 : ℤ) : EInt)) :
    CycleGroup C q k :=
  ⟨D.leftCycle C q, by
    have h := D.leftCycle_mem_cyclesOfDimension C q hn (deltaDimensionFunction_apply C q)
    rwa [show (k + 2 - 2 : ℤ) = k from by ring] at h⟩

/-- The coefficients of `leftCycleGroup` are those of the left hand side of the key formula. -/
@[simp]
theorem leftCycleGroup_apply {Y : Scheme.{u}} [IsIntegral Y] (D : KeyFormulaData Y) (q : Y ⟶ C.S)
    [LocallyOfFiniteType q] (hn : schemeDeltaDimension C q = ((k + 2 : ℤ) : EInt)) (w : Y) :
    (leftCycleGroup C k D q hn).1 w = D.leftCoeff C q w := rfl

/-- The data of the key formula of a situation with the divisors of the generators of `L` set to
zero. Its left hand side is the first half `∑_i ord_{Z_i}(s) div_{L'|Z_i}(t_i|Z_i)` of the left
hand side of the key formula. -/
def keyFormulaDataZeroL : KeyFormulaData (integralComponentAt ξ).subscheme :=
  { ℱ.toKeyFormulaData C ((integralComponentAt ξ).subschemeι ≫ p) with
    restrictedDivisorL := fun _ ↦ 0
    coheight_of_restrictedDivisorL := fun _ _ hz ↦ absurd rfl hz }

/-- The zeroed datum has the same members as the situation. -/
@[simp]
theorem keyFormulaDataZeroL_componentPoint (i : ℱ.Index) :
    (keyFormulaDataZeroL C p L L' ξ ℱ).componentPoint i = ℱ.componentPoint i := rfl

/-- The `i`-th summand of the left hand side of the zeroed datum is the divisor the key formula
reads at the `i`-th member, weighted by the order of vanishing of `s`. -/
theorem componentDifference_keyFormulaDataZeroL (hDimW : schemeDeltaDimension C
    ((integralComponentAt ξ).subschemeι ≫ p) = ((k + 1 + 1 : ℤ) : EInt)) (i : ℱ.Index) :
    (keyFormulaDataZeroL C p L L' ξ ℱ).componentDifference i =
      (ℱ.orderL i • chernCycleOfRestrictedStalk C ((integralComponentAt ξ).subschemeι ≫ p) k
        ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L')
        (integralComponentAt (ℱ.componentPoint i))
        (isIntegral_integralComponentAt (ℱ.componentPoint i))
        (schemeDeltaDimension_componentPoint C p k L L' ξ ℱ hDimW i)
        (genericPointOf_integralComponentAt (ℱ.componentPoint i)) (ℱ.localGeneratorN i)).1 := by
  show (keyFormulaDataZeroL C p L L' ξ ℱ).orderL i •
      (keyFormulaDataZeroL C p L L' ξ ℱ).restrictedDivisorN i -
    (keyFormulaDataZeroL C p L L' ξ ℱ).orderN i • (0 : AlgebraicCycle _ ℤ) = _
  rw [smul_zero, sub_zero]
  rfl

/-- The left hand side of the zeroed datum, pushed forward to `X`, is
`∑ᶠ i, ord_{Z_i}(s)` times the divisor the key formula reads at the `i`-th member. -/
theorem properPushforward_leftCycleGroup_zeroL_apply
    (hDimW : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt))
    (hn2 : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 2 : ℤ) : EInt))
    (hgenN : ∀ i, ℱ.localGeneratorN i =
      Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L'
        (ℱ.componentPoint i) rfl (componentGeneratorAt L' s'
          ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i)))) (y : X) :
    (properPushforward C ((integralComponentAt ξ).subschemeι ≫ p) p
        (integralComponentAt ξ).subschemeι rfl k
        (leftCycleGroup C k (keyFormulaDataZeroL C p L L' ξ ℱ)
          ((integralComponentAt ξ).subschemeι ≫ p) hn2)).1 y =
      ∑ᶠ i : ℱ.Index,
        (ℱ.orderL i • memberKeyFormulaDivisor C p k L L' s' ξ ℱ hDimW i).1 y := by
  rw [properPushforward_apply_finsum_of_isClosedImmersion C
    ((integralComponentAt ξ).subschemeι ≫ p) p (integralComponentAt ξ).subschemeι rfl k _
    (fun i : ℱ.Index ↦ properPushforward C
      ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫
        (integralComponentAt ξ).subschemeι ≫ p) ((integralComponentAt ξ).subschemeι ≫ p)
      (integralComponentAt (ℱ.componentPoint i)).subschemeι rfl k
      (ℱ.orderL i • chernCycleOfRestrictedStalk C ((integralComponentAt ξ).subschemeι ≫ p) k
        ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L')
        (integralComponentAt (ℱ.componentPoint i))
        (isIntegral_integralComponentAt (ℱ.componentPoint i))
        (schemeDeltaDimension_componentPoint C p k L L' ξ ℱ hDimW i)
        (genericPointOf_integralComponentAt (ℱ.componentPoint i)) (ℱ.localGeneratorN i))) ?_ y]
  · refine finsum_congr fun i ↦ ?_
    rw [properPushforward_properPushforward C
      ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫
        (integralComponentAt ξ).subschemeι ≫ p) ((integralComponentAt ξ).subschemeι ≫ p) p
      (integralComponentAt (ℱ.componentPoint i)).subschemeι (integralComponentAt ξ).subschemeι
      rfl rfl k, memberKeyFormulaDivisor, hgenN i]
    rw [properPushforward_zsmul]
  · intro w
    show ∑ᶠ i : ℱ.Index, closedSubschemeCyclePushforward C
      ((integralComponentAt ξ).subschemeι ≫ p) (integralComponentAt (ℱ.componentPoint i))
      ((keyFormulaDataZeroL C p L L' ξ ℱ).componentDifference i) w = _
    refine finsum_congr fun i ↦ ?_
    rw [componentDifference_keyFormulaDataZeroL C p k L L' ξ ℱ hDimW i]
    rfl

/-- The left hand side of the key formula of the situation, pushed forward to `X`, is the sum
over the members of `ord_{Z_i}(s)` times the divisor the key formula reads there, minus
`ord_{Z_i}(s')` times the divisor the swapped situation reads there. -/
theorem properPushforward_leftCycleGroup_apply
    (hDimW : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt))
    (hn2 : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 2 : ℤ) : EInt))
    (hgenL : ∀ i, ℱ.localGeneratorL i =
      Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L
        (ℱ.componentPoint i) rfl (componentGeneratorAt L s
          ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i))))
    (hgenN : ∀ i, ℱ.localGeneratorN i =
      Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L'
        (ℱ.componentPoint i) rfl (componentGeneratorAt L' s'
          ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i)))) (y : X) :
    (properPushforward C ((integralComponentAt ξ).subschemeι ≫ p) p
        (integralComponentAt ξ).subschemeι rfl k
        (leftCycleGroup C k (ℱ.toKeyFormulaData C ((integralComponentAt ξ).subschemeι ≫ p))
          ((integralComponentAt ξ).subschemeι ≫ p) hn2)).1 y =
      ∑ᶠ i : ℱ.Index, ((ℱ.orderL i • memberKeyFormulaDivisor C p k L L' s' ξ ℱ hDimW i) -
        (ℱ.orderN i • memberKeyFormulaDivisor C p k L' L s ξ ℱ.swap hDimW i)).1 y := by
  rw [properPushforward_apply_finsum_of_isClosedImmersion C
    ((integralComponentAt ξ).subschemeι ≫ p) p (integralComponentAt ξ).subschemeι rfl k _
    (fun i : ℱ.Index ↦ properPushforward C
      ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫
        (integralComponentAt ξ).subschemeι ≫ p) ((integralComponentAt ξ).subschemeι ≫ p)
      (integralComponentAt (ℱ.componentPoint i)).subschemeι rfl k
      ((ℱ.orderL i • chernCycleOfRestrictedStalk C ((integralComponentAt ξ).subschemeι ≫ p) k
          ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L')
          (integralComponentAt (ℱ.componentPoint i))
          (isIntegral_integralComponentAt (ℱ.componentPoint i))
          (schemeDeltaDimension_componentPoint C p k L L' ξ ℱ hDimW i)
          (genericPointOf_integralComponentAt (ℱ.componentPoint i)) (ℱ.localGeneratorN i)) -
        (ℱ.orderN i • chernCycleOfRestrictedStalk C ((integralComponentAt ξ).subschemeι ≫ p) k
          ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L)
          (integralComponentAt (ℱ.componentPoint i))
          (isIntegral_integralComponentAt (ℱ.componentPoint i))
          (schemeDeltaDimension_componentPoint C p k L' L ξ ℱ.swap hDimW i)
          (genericPointOf_integralComponentAt (ℱ.componentPoint i)) (ℱ.localGeneratorL i)))) ?_ y]
  · refine finsum_congr fun i ↦ ?_
    rw [properPushforward_properPushforward C
      ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫
        (integralComponentAt ξ).subschemeι ≫ p) ((integralComponentAt ξ).subschemeι ≫ p) p
      (integralComponentAt (ℱ.componentPoint i)).subschemeι (integralComponentAt ξ).subschemeι
      rfl rfl k, properPushforward_sub, properPushforward_zsmul, properPushforward_zsmul]
    simp only [memberKeyFormulaDivisor, KeyFormulaSituation.swap_componentPoint, hgenN i,
      hgenL i]
  · intro w
    show ∑ᶠ i : ℱ.Index, closedSubschemeCyclePushforward C
      ((integralComponentAt ξ).subschemeι ≫ p) (integralComponentAt (ℱ.componentPoint i))
      ((ℱ.toKeyFormulaData C ((integralComponentAt ξ).subschemeι ≫ p)).componentDifference i)
      w = _
    rfl

omit [IsLocallyNoetherian (integralComponentAt ξ).subscheme] in
/-- A member of the family lies in the zero scheme of the restriction of `s` to `Z_ξ` exactly
when its image lies in the zero scheme of `s`. -/
theorem le_integralComponentAt_componentPoint_iff (i : ℱ.Index) :
    Stacks.Divisors.zeroScheme (integralComponentAt ξ).subscheme
        ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (integralComponentAt ξ).subschemeι L s) ≤
          integralComponentAt (ℱ.componentPoint i) ↔
      Stacks.Divisors.zeroScheme X L s ≤
        integralComponentAt ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i)) := by
  rw [Stacks.Divisors.zeroScheme_pullback, le_integralComponentAt_iff_mem_support,
    le_integralComponentAt_iff_mem_support, Scheme.IdealSheafData.support_comap]
  exact Iff.rfl

omit [IsLocallyNoetherian (integralComponentAt ξ).subscheme] in
/-- `f_i = 1` at every member of the family off the zero scheme of the restricted section. -/
theorem ratioL_eq_one_of_not_le_restricted
    (hsectionL : ℱ.sectionL = restrictedComponentSection L s ξ)
    (hgenL : ∀ i, ℱ.localGeneratorL i =
      Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L
        (ℱ.componentPoint i) rfl (componentGeneratorAt L s
          ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i))))
    (i : ℱ.Index)
    (h : ¬ Stacks.Divisors.zeroScheme (integralComponentAt ξ).subscheme
      ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (integralComponentAt ξ).subschemeι L s) ≤
        integralComponentAt (ℱ.componentPoint i)) :
    ℱ.ratioL i = 1 :=
  ratioL_eq_one_of_not_le L L' s ξ ℱ hsectionL hgenL i fun hle ↦
    h ((le_integralComponentAt_componentPoint_iff L L' s ξ ℱ i).2 hle)

/-- The left hand side of the key formula, pushed forward to `X`, is rationally equivalent to
zero with witnesses inside `W ∩ D ∩ D'`. -/
theorem isRationallyEquivalentToZeroWithin_properPushforward_leftCycleGroup
    (hDimW : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt))
    (hn2 : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 2 : ℤ) : EInt))
    (hsectionL : ℱ.sectionL = restrictedComponentSection L s ξ)
    (hsectionN : ℱ.sectionN = restrictedComponentSection L' s' ξ)
    (hgenL : ∀ i, ℱ.localGeneratorL i =
      Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L
        (ℱ.componentPoint i) rfl (componentGeneratorAt L s
          ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i))))
    (hgenN : ∀ i, ℱ.localGeneratorN i =
      Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L'
        (ℱ.componentPoint i) rfl (componentGeneratorAt L' s'
          ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i)))) :
    IsRationallyEquivalentToZeroWithin C p k
      (properPushforward C ((integralComponentAt ξ).subschemeι ≫ p) p
        (integralComponentAt ξ).subschemeι rfl k
        (leftCycleGroup C k (ℱ.toKeyFormulaData C ((integralComponentAt ξ).subschemeι ≫ p))
          ((integralComponentAt ξ).subschemeι ≫ p) hn2))
      (((integralComponentAt ξ).support : Set X) ∩
        (((Stacks.Divisors.zeroScheme X L s).support : Set X) ∩
          ((Stacks.Divisors.zeroScheme X L' s').support : Set X))) := by
  have hkeyW := isRationallyEquivalentToZeroWithin_leftCoeff_of_zeroScheme_pair
    ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L)
    ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L')
    (AlgebraicGeometry.pullbackGlobalSections (integralComponentAt ξ).subschemeι L s)
    (AlgebraicGeometry.pullbackGlobalSections (integralComponentAt ξ).subschemeι L' s') ℱ C
    ((integralComponentAt ξ).subschemeι ≫ p)
    (ratioL_eq_one_of_not_le_restricted L L' s ξ ℱ hsectionL hgenL)
    (fun i hi ↦ ratioL_eq_one_of_not_le_restricted L' L s' ξ ℱ.swap hsectionN hgenN i hi)
    (schemeDeltaDimension_componentPoint C p k L L' ξ ℱ hDimW)
    (leftCycleGroup C k (ℱ.toKeyFormulaData C ((integralComponentAt ξ).subschemeι ≫ p))
      ((integralComponentAt ξ).subschemeι ≫ p) hn2) (fun w ↦ rfl)
  have hclosed : IsClosed ((((Stacks.Divisors.zeroScheme (integralComponentAt ξ).subscheme
        ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L)
        (AlgebraicGeometry.pullbackGlobalSections
          (integralComponentAt ξ).subschemeι L s)).support :
      Set (integralComponentAt ξ).subscheme)) ∩
      ((Stacks.Divisors.zeroScheme (integralComponentAt ξ).subscheme
        ((Scheme.Modules.pullback (integralComponentAt ξ).subschemeι).obj L')
        (AlgebraicGeometry.pullbackGlobalSections
          (integralComponentAt ξ).subschemeι L' s')).support :
        Set (integralComponentAt ξ).subscheme)) :=
    (Stacks.Divisors.zeroScheme _ _ _).support.isClosed.inter
      (Stacks.Divisors.zeroScheme _ _ _).support.isClosed
  refine (properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion_of_within C
    ((integralComponentAt ξ).subschemeι ≫ p) p (integralComponentAt ξ).subschemeι rfl k hclosed
    hkeyW).mono ?_
  rintro y ⟨w, ⟨hw1, hw2⟩, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · exact subschemeι_base_mem_support_integralComponentAt ξ w
  · rwa [Stacks.Divisors.zeroScheme_pullback, Scheme.IdealSheafData.support_comap] at hw1
  · rwa [Stacks.Divisors.zeroScheme_pullback, Scheme.IdealSheafData.support_comap] at hw2

/-- For a situation on `W = Z_ξ` with the prescribed generators, the two iterated Gysin cycles of
`W`, pushed forward to `X`, differ by a cycle rationally equivalent to zero with witnesses inside
`W ∩ D ∩ D'`. -/
theorem isRationallyEquivalentToZeroWithin_gysinGysinComponentCycle_sub_of_situation
    (hDimW : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt))
    (hn2 : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 2 : ℤ) : EInt))
    (hsectionL : ℱ.sectionL = restrictedComponentSection L s ξ)
    (hsectionN : ℱ.sectionN = restrictedComponentSection L' s' ξ)
    (hgenL : ∀ i, ℱ.localGeneratorL i =
      Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L
        (ℱ.componentPoint i) rfl (componentGeneratorAt L s
          ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i))))
    (hgenN : ∀ i, ℱ.localGeneratorN i =
      Stacks.Divisors.pullbackStalkAt (integralComponentAt ξ).subschemeι L'
        (ℱ.componentPoint i) rfl (componentGeneratorAt L' s'
          ((integralComponentAt ξ).subschemeι.base (ℱ.componentPoint i)))) :
    IsRationallyEquivalentToZeroWithin C p k
      (properPushforward C ((zeroSchemeInter L L' s s').subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          ((zeroSchemeInter L L' s s').subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι) (Category.assoc _ _ _) k
          (gysinGysinComponentCycle C p k L L' s s' (integralComponentAt ξ)
            (isIntegral_integralComponentAt ξ) hDimW) -
        properPushforward C ((zeroSchemeInter L' L s' s).subschemeι ≫
            (Stacks.Divisors.zeroScheme X L' s').subschemeι ≫ p) p
          ((zeroSchemeInter L' L s' s).subschemeι ≫
            (Stacks.Divisors.zeroScheme X L' s').subschemeι) (Category.assoc _ _ _) k
          (gysinGysinComponentCycle C p k L' L s' s (integralComponentAt ξ)
            (isIntegral_integralComponentAt ξ) hDimW))
      (((integralComponentAt ξ).support : Set X) ∩
        (((Stacks.Divisors.zeroScheme X L s).support : Set X) ∩
          ((Stacks.Divisors.zeroScheme X L' s').support : Set X))) := by
  have hfinA : ∀ y : X, (Function.support fun i : ℱ.Index ↦
      (ℱ.orderL i • memberKeyFormulaDivisor C p k L L' s' ξ ℱ hDimW i).1 y).Finite := fun y ↦
    finite_support_of_locallyFinite _ (locallyFinite_support_base_componentPoint L L' ξ ℱ)
      (fun i z ↦ (ℱ.orderL i • memberKeyFormulaDivisor C p k L L' s' ξ ℱ hDimW i).1 z)
      (fun i ↦ support_memberKeyFormulaDivisor_subset C p k L L' s' ξ ℱ hDimW i) y
  have hfinB : ∀ y : X, (Function.support fun i : ℱ.Index ↦
      (ℱ.orderN i • memberKeyFormulaDivisor C p k L' L s ξ ℱ.swap hDimW i).1 y).Finite :=
    fun y ↦ finite_support_of_locallyFinite _
      (locallyFinite_support_base_componentPoint L L' ξ ℱ)
      (fun i z ↦ (ℱ.orderN i • memberKeyFormulaDivisor C p k L' L s ξ ℱ.swap hDimW i).1 z)
      (fun i ↦ support_memberKeyFormulaDivisor_subset C p k L' L s ξ ℱ.swap hDimW i) y
  have hβ₂ : ∀ y : X,
      (properPushforward C ((integralComponentAt ξ).subschemeι ≫ p) p
          (integralComponentAt ξ).subschemeι rfl k
          (leftCycleGroup C k (keyFormulaDataZeroL C p L L' ξ ℱ)
            ((integralComponentAt ξ).subschemeι ≫ p) hn2) -
        properPushforward C ((integralComponentAt ξ).subschemeι ≫ p) p
          (integralComponentAt ξ).subschemeι rfl k
          (leftCycleGroup C k (ℱ.toKeyFormulaData C ((integralComponentAt ξ).subschemeι ≫ p))
            ((integralComponentAt ξ).subschemeι ≫ p) hn2)).1 y =
      ∑ᶠ i : ℱ.Index,
        (ℱ.orderN i • memberKeyFormulaDivisor C p k L' L s ξ ℱ.swap hDimW i).1 y := by
    intro y
    have hsplit : ∀ i : ℱ.Index,
        ((ℱ.orderL i • memberKeyFormulaDivisor C p k L L' s' ξ ℱ hDimW i) -
            (ℱ.orderN i • memberKeyFormulaDivisor C p k L' L s ξ ℱ.swap hDimW i)).1 y =
          (ℱ.orderL i • memberKeyFormulaDivisor C p k L L' s' ξ ℱ hDimW i).1 y -
            (ℱ.orderN i • memberKeyFormulaDivisor C p k L' L s ξ ℱ.swap hDimW i).1 y :=
      fun _ ↦ rfl
    show (properPushforward C ((integralComponentAt ξ).subschemeι ≫ p) p
        (integralComponentAt ξ).subschemeι rfl k
        (leftCycleGroup C k (keyFormulaDataZeroL C p L L' ξ ℱ)
          ((integralComponentAt ξ).subschemeι ≫ p) hn2)).1 y -
      (properPushforward C ((integralComponentAt ξ).subschemeι ≫ p) p
        (integralComponentAt ξ).subschemeι rfl k
        (leftCycleGroup C k (ℱ.toKeyFormulaData C ((integralComponentAt ξ).subschemeι ≫ p))
          ((integralComponentAt ξ).subschemeι ≫ p) hn2)).1 y = _
    rw [properPushforward_leftCycleGroup_zeroL_apply C p k L L' s' ξ ℱ hDimW hn2 hgenN y,
      properPushforward_leftCycleGroup_apply C p k L L' s s' ξ ℱ hDimW hn2 hgenL hgenN y,
      finsum_congr hsplit, finsum_sub_distrib (hfinA y) (hfinB y)]
    ring
  refine isRationallyEquivalentToZeroWithin_sub_add C p k
    (isRationallyEquivalentToZeroWithin_properPushforward_gysinGysinComponentCycle_sub_sum
      C p k L L' s s' ξ ℱ hDimW hsectionL hgenL _
      (properPushforward_leftCycleGroup_zeroL_apply C p k L L' s' ξ ℱ hDimW hn2 hgenN))
    ((isRationallyEquivalentToZeroWithin_properPushforward_gysinGysinComponentCycle_sub_sum
      C p k L' L s' s ξ ℱ.swap hDimW hsectionN hgenN _ hβ₂).mono
      fun z hz ↦ ⟨hz.1, hz.2.2, hz.2.1⟩)
    (isRationallyEquivalentToZeroWithin_properPushforward_leftCycleGroup C p k L L' s s' ξ ℱ
      hDimW hn2 hsectionL hsectionN hgenL hgenN) fun y ↦ ?_
  show (_ : ℤ) - _ = (_ - _) - (_ - (_ - _)) + _
  ring

end Assembly

/-! ### Commutation of the two Gysin maps -/

section Tag

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L L' : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']
  (s : Γ(L, ⊤)) (s' : Γ(L', ⊤))

/-- For every integral closed subscheme `W ⊆ X` of delta-dimension `k + 2` the two iterated Gysin
cycles of `W`, pushed forward to `X`, differ by a cycle rationally equivalent to zero with
witnesses inside `W ∩ D ∩ D'`. -/
theorem isRationallyEquivalentToZeroWithin_gysinGysinComponentCycle_sub_component (ξ : X)
    (W : X.IdealSheafData) (hW : IsIntegral W.subscheme) (hWξ : integralComponentAt ξ = W)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 + 1 : ℤ) : EInt)) :
    IsRationallyEquivalentToZeroWithin C p k
      (properPushforward C ((zeroSchemeInter L L' s s').subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          ((zeroSchemeInter L L' s s').subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι) (Category.assoc _ _ _) k
          (gysinGysinComponentCycle C p k L L' s s' W hW hDim) -
        properPushforward C ((zeroSchemeInter L' L s' s).subschemeι ≫
            (Stacks.Divisors.zeroScheme X L' s').subschemeι ≫ p) p
          ((zeroSchemeInter L' L s' s).subschemeι ≫
            (Stacks.Divisors.zeroScheme X L' s').subschemeι) (Category.assoc _ _ _) k
          (gysinGysinComponentCycle C p k L' L s' s W hW hDim))
      ((W.support : Set X) ∩
        (((Stacks.Divisors.zeroScheme X L s).support : Set X) ∩
          ((Stacks.Divisors.zeroScheme X L' s').support : Set X))) := by
  subst hWξ
  have : IsLocallyNoetherian (integralComponentAt ξ).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt ξ).subschemeι ≫ p)
  exact isRationallyEquivalentToZeroWithin_gysinGysinComponentCycle_sub_of_situation C p k L L'
    s s' ξ (componentSituation L L' s s' ξ) hDim
    (by rw [hDim, show (k + 1 + 1 : ℤ) = k + 2 from by ring]) rfl rfl (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- The two iterated Gysin maps agree on every integral closed subscheme of delta-dimension
`k + 2`, in the sense of `GysinGysinCommutesOnComponents`. -/
theorem gysinGysinCommutesOnComponents_componentSituation
    (e : (zeroSchemeInter L L' s s').subscheme ≅ (zeroSchemeInter L' L s' s).subscheme)
    (he : e.hom ≫ (zeroSchemeInter L' L s' s).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L' s').subschemeι =
      (zeroSchemeInter L L' s s').subschemeι ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι) :
    GysinGysinCommutesOnComponents C p k L L' s s' e he :=
  gysinGysinCommutesOnComponents_of_properPushforward C p k L L' s s' e he
    fun W hW hDim ↦ isRationallyEquivalentToZeroWithin_gysinGysinComponentCycle_sub_component
      C p k L L' s s' (genericPointOf W hW) W hW (integralComponentAt_genericPointOf W hW) hDim

/-- Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let
`X` be locally of finite type over `S`, and let `(L, s, i : D → X)` and `(L', s', i' : D' → X)`
be two triples as in Definition 02T8, so that `D = Z(s)` and `D' = Z(s')` are the zero schemes of
the two sections. Write `j : D ∩ D' → D` and `j' : D ∩ D' → D'` for the two presentations of the
scheme-theoretic intersection as a zero scheme — of the restriction of `s'` to `D`, and of the
restriction of `s` to `D'` — and let `e` be an isomorphism between them over `X`. Then the
diagram

```
  CH_k(X)  --i^*-->  CH_{k-1}(D)
     |                  |
  (i')^*               j^*
     v                  v
  CH_{k-1}(D') --(j')^*--> CH_{k-2}(D ∩ D')
```

commutes, each of the four maps being a Gysin map. The input degree is written `(k + 1) + 1`. -/
@[stacks 0B73]
theorem gysinChowOfInvertible_comm
    (e : (zeroSchemeInter L L' s s').subscheme ≅ (zeroSchemeInter L' L s' s).subscheme)
    (he : e.hom ≫ (zeroSchemeInter L' L s' s).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L' s').subschemeι =
      (zeroSchemeInter L L' s s').subschemeι ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι)
    (α : chowGroup C p (k + 1 + 1)) :
    chowPushforwardOfIso C ((zeroSchemeInter L L' s s').subschemeι ≫
          (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
        ((zeroSchemeInter L' L s' s).subschemeι ≫
          (Stacks.Divisors.zeroScheme X L' s').subschemeι ≫ p)
        e.hom (iso_zeroSchemeInter_comp_structureMorphism C p L L' s s' e he) k
        (gysinChowOfInvertible C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
          (zeroSchemeRestrictModule L L' s) (restrictSectionToZeroScheme L L' s s')
          (gysinChowOfInvertible C p (k + 1) L s α)) =
      gysinChowOfInvertible C ((Stacks.Divisors.zeroScheme X L' s').subschemeι ≫ p) k
        (zeroSchemeRestrictModule L' L s') (restrictSectionToZeroScheme L' L s' s)
        (gysinChowOfInvertible C p (k + 1) L' s' α) :=
  gysinChowOfInvertible_comm_of_components C p k L L' s s' e he
    (gysinGysinCommutesOnComponents_componentSituation C p k L L' s s' e he) α

end Tag

end Stacks.Chow

end
