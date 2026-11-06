module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IteratedFirstChernCapCommutativity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CycleMapsOfKernels
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RegularSectionFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinOfSection

/-!
# The refined Gysin map and the restriction to a closed subspace

In Situation 0EDT let `X/B` be good, let `(ℒ, s)` be a pair as in Stacks 0ER1 with vanishing
locus `E = Z(s)`, and let `Y ⊆ X` be a closed subspace. The pair `(ℒ|_Y, s|_Y)` on `Y` has
vanishing locus `Y' = Z(s|_Y) = Y ×_X E` (Stacks 0846, part (2)). For a `(k+1)`-cycle `β` on `Y`
the two `k`-cycles on `X`

`(E → X)_* i^*((Y → X)_* β)`  and  `(Y → X)_* (Y' → Y)_* (i_Y)^* β`

are rationally equivalent, with the rational equivalence carried by `|Y'|`. On an integral
closed subspace `V ⊆ Y` with image `V' ⊆ X`, if `V ⊄ Y'` both Gysin components are the cycle of
the scheme-theoretic intersection `V' ∩ E`, read on `E` and on `Y'`; if `V ⊆ Y'` both are Weil
divisors of regular meromorphic sections of `ℒ|_{V'}`, after transport along `V ≅ V'`, which
differ by a principal divisor (Stacks 0EPT). The case of a closed immersion of Stacks 0ER5 is the
cycle-level form of this.

## Main results

* `AlgebraicGeometry.Space.cycleGroupClosedPushforward_closedSubspaceCycle_eq_of_range_eq`: the
  cycles of two closed subspaces of spaces embedded in `X` with the same image have the same
  pushforward to `X`.
* `AlgebraicGeometry.Space.isCanonicallyRationallyEquivalentToZeroWithin_gysinCycleMap_closedSubspaceCyclePushforward_sub`:
  the comparison above.

## References

* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER5](https://stacks.math.columbia.edu/tag/0ER5)
* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace CategoryTheory.Subfunctor

variable {C : Type*} [Category C] {F A : C ⥤ Type v}

/-- The image of the inverse image of a subfunctor `G ⊆ F` along `f : A ⟶ F`, mapped back to `F`,
is the intersection of the image of `f` with `G`. -/
theorem range_preimage_ι_comp (G : Subfunctor F) (f : A ⟶ F) :
    range ((G.preimage f).ι ≫ f) = range f ⊓ G := by
  ext U x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a.1, rfl⟩, a.2⟩
  · rintro ⟨⟨a, rfl⟩, ha⟩
    exact ⟨⟨a, ha⟩, rfl⟩

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Closed subspaces with the same image -/

section RangeComparison

variable (D : BaseSpaceDimensionSituation.{u})
    {X T₁ T₂ : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Two closed subspaces with the same image in `X` have the same pushed-forward cycle.** In
Situation 0EDT let `X/B` be good, let `j₁ : T₁ → X`, `j₂ : T₂ → X` be closed immersions over the
base and let `Y₁ ⊆ T₁`, `Y₂ ⊆ T₂` be closed subspaces of δ-dimension at most `k` whose images in
`X` agree as subfunctors. Then `(j₁)_*[Y₁]_k = (j₂)_*[Y₂]_k`: the composites `Y_i → X` are
monomorphisms, so each `Y_i` is isomorphic to the common image, compatibly with the maps to `X`. -/
theorem cycleGroupClosedPushforward_closedSubspaceCycle_eq_of_range_eq (sX : X ⟶ D.space)
    (hX : D.IsGood sX) {j₁ : T₁ ⟶ X} (hj₁ : IsClosedImmersion D.site D.base D.base_mem j₁)
    {j₂ : T₂ ⟶ X} (hj₂ : IsClosedImmersion D.site D.base D.base_mem j₂) (s₁ : T₁ ⟶ D.space)
    (hT₁ : D.IsGood s₁) (s₂ : T₂ ⟶ D.space) (hT₂ : D.IsGood s₂) (hs₁ : j₁ ≫ sX = s₁)
    (hs₂ : j₂ ≫ sX = s₂) (Y₁ : Subfunctor T₁) (hY₁ : IsClosedSubspace D.site D.base D.base_mem Y₁)
    (Y₂ : Subfunctor T₂) (hY₂ : IsClosedSubspace D.site D.base D.base_mem Y₂)
    (hrange : Subfunctor.range (Y₁.ι ≫ j₁) = Subfunctor.range (Y₂.ι ≫ j₂)) (k : ℤ)
    (hd₁ : deltaDimensionSubspace D s₁ hT₁ Y₁ hY₁ ≤ (k : EInt))
    (hd₂ : deltaDimensionSubspace D s₂ hT₂ Y₂ hY₂ ≤ (k : EInt)) :
    cycleGroupClosedPushforward D hX.1 hT₁.1 (D.isDecentSpace_of_isGood sX hX) hj₁ sX hX.2.2 s₁
        hs₁ k (closedSubspaceCycle D s₁ hT₁ Y₁ hY₁ k hd₁) =
      cycleGroupClosedPushforward D hX.1 hT₂.1 (D.isDecentSpace_of_isGood sX hX) hj₂ sX hX.2.2
        s₂ hs₂ k (closedSubspaceCycle D s₂ hT₂ Y₂ hY₂ k hd₂) := by
  have : Mono (Y₁.ι ≫ j₁) := mono_of_isClosedImmersion D.site D.base D.base_mem _
    (isClosedImmersion_comp D.site D.base D.base_mem _ _ hY₁.2 hj₁)
  have : Mono (Y₂.ι ≫ j₂) := mono_of_isClosedImmersion D.site D.base D.base_mem _
    (isClosedImmersion_comp D.site D.base D.base_mem _ _ hY₂.2 hj₂)
  let e : (Subfunctor.range (Y₁.ι ≫ j₁)).toFunctor ≅ (Subfunctor.range (Y₂.ι ≫ j₂)).toFunctor :=
    { hom := Subfunctor.homOfLe hrange.le
      inv := Subfunctor.homOfLe hrange.ge
      hom_inv_id := by ext; rfl
      inv_hom_id := by ext; rfl }
  let φ : Y₁.toFunctor ≅ Y₂.toFunctor :=
    asIso (Subfunctor.toRange (Y₁.ι ≫ j₁)) ≪≫ e ≪≫ (asIso (Subfunctor.toRange (Y₂.ι ≫ j₂))).symm
  have hφ : φ.hom ≫ Y₂.ι ≫ j₂ = Y₁.ι ≫ j₁ := by
    have hinv : inv (Subfunctor.toRange (Y₂.ι ≫ j₂)) ≫ Y₂.ι ≫ j₂ =
        (Subfunctor.range (Y₂.ι ≫ j₂)).ι := by
      rw [IsIso.inv_comp_eq, Subfunctor.toRange_ι]
    show (Subfunctor.toRange (Y₁.ι ≫ j₁) ≫ Subfunctor.homOfLe hrange.le ≫
      inv (Subfunctor.toRange (Y₂.ι ≫ j₂))) ≫ Y₂.ι ≫ j₂ = Y₁.ι ≫ j₁
    simp only [Category.assoc, hinv, Subfunctor.homOfLe_ι, Subfunctor.toRange_ι]
  exact cycleGroupClosedPushforward_closedSubspaceCycle_eq_of_iso D sX hX hj₁ hj₂ s₁ hT₁ s₂ hT₂
    hs₁ hs₂ Y₁ hY₁ Y₂ hY₂ φ hφ k hd₁ hd₂

end RangeComparison

/-! ### Integral closed subspaces of a closed subspace -/

section ComponentImage

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (Y : ClosedSubspaces D.site D.base D.base_mem X)

/-- An integral closed subspace `V` of a closed subspace `Y ⊆ X` is the inverse image in `Y` of
its image `V' ⊆ X`: the inclusion `V → Y → X` is `V ≅ V' → X`, and `Y → X` is a monomorphism. -/
theorem preimage_closedSubspaceComponentImage
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor) :
    (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace.preimage Y.1.ι = V.subspace := by
  set φ := IntegralClosedSubspace.isoPushforward hX.1 Y.2.1 (D.isDecentSpace_of_isGood sX hX)
    Y.2.2 V
  have hφ : φ.hom ≫ (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace.ι =
      V.subspace.ι ≫ Y.1.ι :=
    IntegralClosedSubspace.isoPushforward_hom_comp_ι hX.1 Y.2.1
      (D.isDecentSpace_of_isGood sX hX) Y.2.2 V
  ext U y
  constructor
  · intro hy
    let z : (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace.toFunctor.obj U :=
      ⟨Y.1.ι.app U y, hy⟩
    have h1 : Y.1.ι.app U (V.subspace.ι.app U (φ.inv.app U z)) = Y.1.ι.app U y := by
      have h := congrArg (fun f => f.app U (φ.inv.app U z)) hφ
      simp only [NatTrans.comp_app_apply] at h
      have hid : φ.hom.app U (φ.inv.app U z) = z := by
        simp
      rw [← h, hid]
      rfl
    have h3 : V.subspace.ι.app U (φ.inv.app U z) = y := Subtype.ext h1
    rw [← h3]
    exact (φ.inv.app U z).2
  · intro hy
    have h1 := congrArg (fun f => f.app U (⟨y, hy⟩ : V.subspace.toFunctor.obj U)) hφ
    simp only at h1
    show Y.1.ι.app U y ∈ (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace.obj U
    have h2 : Y.1.ι.app U y = (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace.ι.app U
        (φ.hom.app U ⟨y, hy⟩) := h1.symm
    rw [h2]
    exact (φ.hom.app U ⟨y, hy⟩).2

/-- The image `V' ⊆ X` of an integral closed subspace of `Y` lies in `Y`. -/
theorem closedSubspaceComponentImage_le
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor) :
    (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace ≤ Y.1 := by
  set φ := IntegralClosedSubspace.isoPushforward hX.1 Y.2.1 (D.isDecentSpace_of_isGood sX hX)
    Y.2.2 V
  have hφ : φ.hom ≫ (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace.ι =
      V.subspace.ι ≫ Y.1.ι :=
    IntegralClosedSubspace.isoPushforward_hom_comp_ι hX.1 Y.2.1
      (D.isDecentSpace_of_isGood sX hX) Y.2.2 V
  intro U x hx
  let z : (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace.toFunctor.obj U := ⟨x, hx⟩
  have h1 : (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace.ι.app U z =
      Y.1.ι.app U (V.subspace.ι.app U (φ.inv.app U z)) := by
    have h := congrArg (fun f => f.app U (φ.inv.app U z)) hφ
    simp only [NatTrans.comp_app_apply] at h
    have hid : φ.hom.app U (φ.inv.app U z) = z := by
      simp
    rw [← h, hid]
  show (closedSubspaceComponentImage D sX hX Y.1 Y.2 V).subspace.ι.app U z ∈ Y.1.obj U
  rw [h1]
  exact (V.subspace.ι.app U (φ.inv.app U z)).2

end ComponentImage

/-! ### Invertible modules on a closed subspace -/

section Transport

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (Y : ClosedSubspaces D.site D.base D.base_mem X)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

include hN in
/-- The restriction `𝒩|_Y` of an invertible module to a closed subspace is invertible
(Stacks 0B8P). -/
theorem isInvertibleModule_closedSubspaceModuleRestrict :
    IsInvertibleModule (⟨Y.1.toFunctor, (isGood_closedSubspace D sX hX Y).1⟩ :
      AlgebraicSpaces D.site D.base D.base_mem) (closedSubspaceModuleRestrict D sX hX N Y) :=
  modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hX.1 Y.1 Y.2) N hN

end Transport

/-! ### The restriction of a pair to a closed subspace -/

section Restriction

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (Y : ClosedSubspaces D.site D.base D.base_mem X)

/-- The restriction `s|_Y ∈ Γ(Y, ℒ|_Y)` of a global section to a closed subspace `Y ⊆ X`: its
inverse image along the closed immersion `Y → X`. -/
abbrev closedSubspaceModuleRestrictSection : (closedSubspaceModuleRestrict D p hp L Y).sections :=
  modulePullbackSections D.site D.base D.base_mem
    (closedSubspaceHom D.site D.base D.base_mem hp.1 Y.1 Y.2) L s

/-- The vanishing locus `Z(s|_Y) ⊆ Y` of the restriction of a global section to a closed
subspace. -/
abbrev closedSubspaceVanishingLocus : ClosedSubspaces D.site D.base D.base_mem Y.1.toFunctor :=
  vanishingLocus D (Y.1.ι ≫ p) (isGood_closedSubspace D p hp Y)
    (closedSubspaceModuleRestrict D p hp L Y) (closedSubspaceModuleRestrictSection D p hp L s Y)

variable {L} in
/-- The restriction `ℒ|_Y` of an invertible sheaf to a closed subspace is invertible
(Stacks 0B8P). -/
theorem isInvertibleSheaf_closedSubspaceModuleRestrict (hL : IsInvertibleSheaf D p hp L) :
    IsInvertibleSheaf D (Y.1.ι ≫ p) (isGood_closedSubspace D p hp Y)
      (closedSubspaceModuleRestrict D p hp L Y) :=
  isInvertible_modulePullback_obj D.site D.base D.base_mem
    (closedSubspaceHom D.site D.base D.base_mem hp.1 Y.1 Y.2) L hL

variable {L} in
/-- **Stacks 0846, part (2), for a closed subspace.** `Z(s|_Y) = Y ×_X Z(s)`, the inverse image of
`Z(s)` in `Y`. -/
theorem closedSubspaceVanishingLocus_eq_preimage (hL : IsInvertibleSheaf D p hp L) :
    (closedSubspaceVanishingLocus D p hp L s Y).1 =
      (vanishingLocus D p hp L s).1.preimage Y.1.ι :=
  congrArg Subtype.val (zeroScheme_modulePullbackSections D.site D.base D.base_mem ⟨X, hp.1⟩
    ⟨Y.1.toFunctor, Y.2.1⟩ L hL s (closedSubspaceHom D.site D.base D.base_mem hp.1 Y.1 Y.2))

variable {L} (hL : IsInvertibleSheaf D p hp L) (k : ℤ)

include hL in
/-- An integral closed subspace `V ⊆ Y` lies in `Z(s|_Y)` exactly when its image `V' ⊆ X` lies in
`Z(s)`. -/
theorem le_closedSubspaceVanishingLocus_iff
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor) :
    V.subspace ≤ (closedSubspaceVanishingLocus D p hp L s Y).1 ↔
      (closedSubspaceComponentImage D p hp Y.1 Y.2 V).subspace ≤ (vanishingLocus D p hp L s).1 := by
  rw [closedSubspaceVanishingLocus_eq_preimage D p hp s Y hL]
  constructor
  · intro h U x hx
    have hxY := closedSubspaceComponentImage_le D p hp Y V U hx
    have hxV : (⟨x, hxY⟩ : Y.1.toFunctor.obj U) ∈ V.subspace.obj U := by
      rwa [← preimage_closedSubspaceComponentImage D p hp Y V]
    exact h U hxV
  · intro h U y hy
    have hy' : Y.1.ι.app U y ∈ (closedSubspaceComponentImage D p hp Y.1 Y.2 V).subspace.obj U := by
      rwa [← preimage_closedSubspaceComponentImage D p hp Y V] at hy
    exact h U hy'

/-- **The comparison on one integral closed subspace.** For an integral closed subspace `V ⊆ Y`
with image `V' ⊆ X`, the pushforwards to `X` of the Gysin component cycle of `(ℒ, s)` at `V'` and
of the Gysin component cycle of `(ℒ|_Y, s|_Y)` at `V` differ by a sum of canonical principal
divisors on subspaces of `|V'| ∩ |Z(s|_Y)|`. If `V ⊄ Z(s|_Y)` the two are the cycle of
`V' ∩ Z(s)`, read on `Z(s)` and on `Z(s|_Y)`; if `V ⊆ Z(s|_Y)` both are pushforwards of Weil
divisors of regular meromorphic sections of `ℒ|_{V'}` (Stacks 0EPT). -/
theorem isCanonicallyRationallyEquivalentToZeroWithin_gysinComponentCycle_sub
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D p hp k
      (closedSubspaceCyclePushforward D p hp (vanishingLocus D p hp L s) k
          (gysinComponentCycle D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s)
            k (sectionGysinRule D p hp L s k hL)
            (closedSubspaceComponentImage D p hp Y.1 Y.2 V)) -
        closedSubspaceCyclePushforward D p hp Y k
          (closedSubspaceCyclePushforward D (Y.1.ι ≫ p) (isGood_closedSubspace D p hp Y)
            (closedSubspaceVanishingLocus D p hp L s Y) k
            (gysinComponentCycle D (Y.1.ι ≫ p) (closedSubspaceVanishingLocus D p hp L s Y)
              (isGood_vanishingLocus D _ (isGood_closedSubspace D p hp Y) _ _) k
              (sectionGysinRule D _ (isGood_closedSubspace D p hp Y) _
                (closedSubspaceModuleRestrictSection D p hp L s Y) k
                (isInvertibleSheaf_closedSubspaceModuleRestrict D p hp Y hL)) V)))
      (Set.range (pointsMap D.site D.base D.base_mem _
          ((closedSubspaceVanishingLocus D p hp L s Y).1.ι ≫ Y.1.ι)) ∩
        subspacePointSet D.site D.base D.base_mem X
          (closedSubspaceComponentImage D p hp Y.1 Y.2 V).subspace) := by
  have hdec := D.isDecentSpace_of_isGood p hp
  have hYg := isGood_closedSubspace D p hp Y
  have hYdec := D.isDecentSpace_of_isGood _ hYg
  set E := vanishingLocus D p hp L s
  have hE := isGood_vanishingLocus D p hp L s
  set Y' := closedSubspaceVanishingLocus D p hp L s Y
  have hY' : D.IsGood (Y'.1.ι ≫ Y.1.ι ≫ p) := isGood_vanishingLocus D _ hYg _ _
  have hY'eq : Y'.1 = E.1.preimage Y.1.ι := closedSubspaceVanishingLocus_eq_preimage D p hp s Y hL
  set V' := closedSubspaceComponentImage D p hp Y.1 Y.2 V with hV'def
  have hdimV : deltaDimension D p V' = deltaDimension D (Y.1.ι ≫ p) V :=
    deltaDimension_closedSubspaceComponentImage D p hp Y.1 Y.2 V
  have hcomp : ∀ γ : CycleGroup D (Y'.1.ι ≫ Y.1.ι ≫ p) k,
      closedSubspaceCyclePushforward D p hp Y k
          (closedSubspaceCyclePushforward D (Y.1.ι ≫ p) hYg Y' k γ) =
        cycleGroupClosedPushforward D hp.1 Y'.2.1 hdec
          (isClosedImmersion_comp D.site D.base D.base_mem _ _ Y'.2.2 Y.2.2) p hp.2.2
          (Y'.1.ι ≫ Y.1.ι ≫ p) (Category.assoc _ _ _) k γ := fun γ =>
    cycleGroupClosedPushforward_cycleGroupClosedPushforward D hp.1 Y.2.1 Y'.2.1 hdec hYdec rfl
      Y'.2.2 Y.2.2 (isClosedImmersion_comp D.site D.base D.base_mem _ _ Y'.2.2 Y.2.2) p hp.2.2
      (Y.1.ι ≫ p) hYg.2.2 (Y'.1.ι ≫ Y.1.ι ≫ p) rfl rfl (Category.assoc _ _ _) k γ
  by_cases hV : deltaDimension D (Y.1.ι ≫ p) V = k + 1
  · have hV'k : deltaDimension D p V' = k + 1 := hdimV.trans hV
    by_cases hVY' : V.subspace ≤ Y'.1
    · -- `V ⊆ Z(s|_Y)`: two Weil divisors on `V'`
      have hV'E : V'.subspace ≤ E.1 :=
        (le_closedSubspaceVanishingLocus_iff D p hp s Y hL V).1 hVY'
      rw [gysinComponentCycle_of_le D p E hE k _ hV'k hV'E,
        gysinComponentCycle_of_le D (Y.1.ι ≫ p) Y' hY' k _ hV hVY',
        closedSubspaceCyclePushforward_containedPushforward D p hp E k hE hV'E,
        closedSubspaceCyclePushforward_containedPushforward D (Y.1.ι ≫ p) hYg Y' k hY' hVY']
      have hk : deltaDimensionClosed D (V.subspace.ι ≫ Y.1.ι ≫ p)
          (isGood_integralClosedSubspace D (Y.1.ι ≫ p) hYg V) Set.univ isClosed_univ =
            ((k + 1 : ℤ) : EInt) := by
        rw [deltaDimensionClosed_univ_integralClosedSubspace D (Y.1.ι ≫ p) hYg V, hV]
      have hk' : deltaDimensionClosed D (V'.subspace.ι ≫ p)
          (isGood_integralClosedSubspace D p hp V') Set.univ isClosed_univ =
            ((k + 1 : ℤ) : EInt) := by
        rw [deltaDimensionClosed_univ_integralClosedSubspace D p hp V', hV'k]
      obtain ⟨σ, hσ, hσeq⟩ :=
        exists_closedSubspaceCyclePushforward_canonicalDivisorCycleAt_eq
          D p hp Y.1 Y.2 L (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL)
          (closedSubspaceModuleRestrict D p hp L Y) rfl V
          (restrictedSectionOfIntegralClosedSubspace D (Y.1.ι ≫ p) hYg _
            (isInvertibleSheaf_closedSubspaceModuleRestrict D p hp Y hL) V)
          (isRegularMeromorphicSection_regularMeromorphicSection D.site D.base D.base_mem
            (isGood_integralClosedSubspace D (Y.1.ι ≫ p) hYg V).1 V.isIntegralSpace
            (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D (V.subspace.ι ≫ Y.1.ι ≫ p)
              (isGood_integralClosedSubspace D (Y.1.ι ≫ p) hYg V))
            _ (isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D
              (Y.1.ι ≫ p) hYg _ (isInvertibleSheaf_closedSubspaceModuleRestrict D p hp Y hL) V))
          hk hk'
      have hsec : closedSubspaceCyclePushforward D p hp Y k
          (integralClosedSubspacePushforward D (Y.1.ι ≫ p) hYg V k
            ((sectionGysinRule D _ hYg _ (closedSubspaceModuleRestrictSection D p hp L s Y) k
              (isInvertibleSheaf_closedSubspaceModuleRestrict D p hp Y hL)).chernCycle V hV
                hVY')) =
          integralClosedSubspacePushforward D p hp V' k
            (canonicalDivisorCycleAt D _ (isGood_integralClosedSubspace D p hp V')
              V'.isIntegralSpace _ (isInvertibleModule_integralClosedSubspaceRestrict D p hp L
                (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) _) σ hσ hk') :=
        hσeq
      have hchern : (sectionGysinRule D p hp L s k hL).chernCycle V' hV'k hV'E =
          canonicalDivisorCycleAt D _ (isGood_integralClosedSubspace D p hp V')
            V'.isIntegralSpace _ (isInvertibleModule_integralClosedSubspaceRestrict D p hp L
              (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) _)
            (restrictedSectionOfIntegralClosedSubspace D p hp L hL V')
            (isRegularMeromorphicSection_regularMeromorphicSection D.site D.base D.base_mem
              (isGood_integralClosedSubspace D p hp V').1 V'.isIntegralSpace
              (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D (V'.subspace.ι ≫ p)
                (isGood_integralClosedSubspace D p hp V'))
              _ (isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D p hp L hL
                V')) hk' :=
        rfl
      rw [hchern]
      rw [hsec, ← map_sub, ← one_smul ℤ (_ - _)]
      refine (isCycleFamilySumWithin_integralClosedSubspacePushforward D p hp k V'
        (P := canonicalPrincipalDivisors D p hp k)
        ((exists_zsmul_sub_canonicalDivisorCycleAt_eq D _ (isGood_integralClosedSubspace D p hp V')
          V'.isIntegralSpace _ _ _ σ _ hσ hk' 1).elim fun g hg => ⟨hk', g, hg⟩)).mono ?_
      refine Set.subset_inter ?_ subset_rfl
      rw [hV'def, IntegralClosedSubspace.subspacePointSet_pushforward]
      rintro _ ⟨y, ⟨v, rfl⟩, rfl⟩
      refine ⟨pointsMap D.site D.base D.base_mem _ (Subfunctor.homOfLe hVY') v, ?_⟩
      rw [← pointsMap_comp_apply, ← Category.assoc, Subfunctor.homOfLe_ι, pointsMap_comp_apply]
    · -- `V ⊄ Z(s|_Y)`: the cycle of `V' ∩ Z(s)`, read on `Z(s)` and on `Z(s|_Y)`
      have hV'E : ¬ V'.subspace ≤ E.1 := fun h =>
        hVY' ((le_closedSubspaceVanishingLocus_iff D p hp s Y hL V).2 h)
      rw [gysinComponentCycle_of_not_le D p E hE k _ hV'k hV'E,
        gysinComponentCycle_of_not_le D (Y.1.ι ≫ p) Y' hY' k _ hV hVY', hcomp]
      have hrange : Subfunctor.range ((V'.subspace.preimage E.1.ι).ι ≫ E.1.ι) =
          Subfunctor.range ((V.subspace.preimage Y'.1.ι).ι ≫ Y'.1.ι ≫ Y.1.ι) := by
        rw [Subfunctor.range_preimage_ι_comp, Subfunctor.range_ι]
        ext U x
        constructor
        · rintro ⟨hxE, hxV⟩
          have hxY := closedSubspaceComponentImage_le D p hp Y V U hxV
          have hyY' : (⟨x, hxY⟩ : Y.1.toFunctor.obj U) ∈ Y'.1.obj U := by
            rwa [hY'eq]
          have haV : (⟨x, hxY⟩ : Y.1.toFunctor.obj U) ∈ V.subspace.obj U := by
            rwa [← preimage_closedSubspaceComponentImage D p hp Y V]
          exact ⟨⟨⟨⟨x, hxY⟩, hyY'⟩, haV⟩, rfl⟩
        · rintro ⟨⟨⟨y, hy⟩, hyV⟩, rfl⟩
          refine ⟨?_, ?_⟩
          · rwa [hY'eq] at hy
          · change y ∈ V.subspace.obj U at hyV
            rwa [← preimage_closedSubspaceComponentImage D p hp Y V] at hyV
      have h := cycleGroupClosedPushforward_closedSubspaceCycle_eq_of_range_eq D p hp E.2.2
        (isClosedImmersion_comp D.site D.base D.base_mem _ _ Y'.2.2 Y.2.2) (E.1.ι ≫ p) hE
        (Y'.1.ι ≫ Y.1.ι ≫ p) hY' rfl (Category.assoc _ _ _) _ _ _ _ hrange k
        (deltaDimensionSubspace_gysinIntersectionSubspace_le_of_not_le D p hp E hE k V' hV'k hV'E)
        (deltaDimensionSubspace_gysinIntersectionSubspace_le_of_not_le D (Y.1.ι ≫ p) hYg Y' hY' k
          V hV hVY')
      have h' : closedSubspaceCyclePushforward D p hp E k
            ((sectionGysinRule D p hp L s k hL).intersectionCycle V' hV'k hV'E) =
          cycleGroupClosedPushforward D hp.1 Y'.2.1 hdec
            (isClosedImmersion_comp D.site D.base D.base_mem _ _ Y'.2.2 Y.2.2) p hp.2.2
            (Y'.1.ι ≫ Y.1.ι ≫ p) (Category.assoc _ _ _) k
            ((sectionGysinRule D _ hYg _ (closedSubspaceModuleRestrictSection D p hp L s Y) k
              (isInvertibleSheaf_closedSubspaceModuleRestrict D p hp Y hL)).intersectionCycle V
                hV hVY') :=
        h
      rw [h', sub_self]
      exact isCycleFamilySumWithin_zero D p hp k _
  · rw [gysinComponentCycle_of_deltaDimension_ne D p E hE k _ (by rwa [hdimV]),
      gysinComponentCycle_of_deltaDimension_ne D (Y.1.ι ≫ p) Y' hY' k _ hV, map_zero, map_zero,
      map_zero, sub_zero]
    exact isCycleFamilySumWithin_zero D p hp k _

/-- **The refined Gysin map and the restriction to a closed subspace.** In Situation 0EDT let
`X/B` be good, `(ℒ, s)` a pair as in Stacks 0ER1 with `E = Z(s)`, `Y ⊆ X` a closed subspace and
`Y' = Z(s|_Y) ⊆ Y`. For every `(k+1)`-cycle `β` on `Y`,

`(E → X)_* i^*((Y → X)_* β) - (Y → X)_* (Y' → Y)_* (i_Y)^* β`

is a sum of canonical principal divisors on integral closed subspaces of `X` lying in the image
of `|Y'|` and in the images of the subspaces occurring in `β`. Both sides are computed one
integral closed subspace `V ⊆ Y` at a time
(`AlgebraicGeometry.Space.isCanonicallyRationallyEquivalentToZeroWithin_gysinComponentCycle_sub`),
and the images of the `V` occurring in `β` form a locally finite family (Stacks 0EQ8). This is
Stacks 0ER5 for the closed immersion `Y → X`, at the level of cycles. -/
theorem
    isCanonicallyRationallyEquivalentToZeroWithin_gysinCycleMap_closedSubspaceCyclePushforward_sub
    (β : CycleGroup D (Y.1.ι ≫ p) (k + 1)) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, max (u + 1) v} D p hp k
      (closedSubspaceCyclePushforward D p hp (vanishingLocus D p hp L s) k
          (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k
            (sectionGysinRule D p hp L s k hL)
            (closedSubspaceCyclePushforward D p hp Y (k + 1) β)) -
        closedSubspaceCyclePushforward D p hp Y k
          (closedSubspaceCyclePushforward D (Y.1.ι ≫ p) (isGood_closedSubspace D p hp Y)
            (closedSubspaceVanishingLocus D p hp L s Y) k
            (gysinCycleMap D (Y.1.ι ≫ p) (closedSubspaceVanishingLocus D p hp L s Y)
              (isGood_vanishingLocus D _ (isGood_closedSubspace D p hp Y) _ _) k
              (sectionGysinRule D _ (isGood_closedSubspace D p hp Y) _
                (closedSubspaceModuleRestrictSection D p hp L s Y) k
                (isInvertibleSheaf_closedSubspaceModuleRestrict D p hp Y hL)) β)))
      (Set.range (pointsMap D.site D.base D.base_mem _
          ((closedSubspaceVanishingLocus D p hp L s Y).1.ι ≫ Y.1.ι)) ∩
        ⋃ V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor,
          if β.1 V = 0 then ∅ else subspacePointSet D.site D.base D.base_mem X
            (closedSubspaceComponentImage D p hp Y.1 Y.2 V).subspace) := by
  classical
  have hdec := D.isDecentSpace_of_isGood p hp
  have hYg := isGood_closedSubspace D p hp Y
  set E := vanishingLocus D p hp L s
  have hE := isGood_vanishingLocus D p hp L s
  set Y' := closedSubspaceVanishingLocus D p hp L s Y
  have hY' : D.IsGood (Y'.1.ι ≫ Y.1.ι ≫ p) := isGood_vanishingLocus D _ hYg _ _
  let rule := sectionGysinRule D p hp L s k hL
  let ruleY := sectionGysinRule D _ hYg _ (closedSubspaceModuleRestrictSection D p hp L s Y) k
    (isInvertibleSheaf_closedSubspaceModuleRestrict D p hp Y hL)
  let img := closedSubspaceComponentImage D p hp Y.1 Y.2
  have himg : Function.Injective img := IntegralClosedSubspace.injective_pushforward D.site
    D.base D.base_mem hp.1 Y.2.1 hdec Y.2.2
  let pushY := fun j : ℤ => closedSubspaceCyclePushforward D p hp Y j
  have hpush : ∀ (j : ℤ) (γ : CycleGroup D (Y.1.ι ≫ p) j) V, (pushY j γ).1 (img V) = γ.1 V :=
    fun j γ V => cycleClosedPushforward_apply_pushforward D hp.1 Y.2.1 hdec Y.2.2 γ.1 V
  have hpush0 : ∀ (j : ℤ) (γ : CycleGroup D (Y.1.ι ≫ p) j) Z,
      (∀ V, img V ≠ Z) → (pushY j γ).1 Z = 0 := fun j γ Z hZ =>
    cycleClosedPushforward_apply_of_forall_ne D hp.1 Y.2.1 hdec Y.2.2 γ.1 Z hZ
  have hΦ := (isCycleMapOfKernel_gysinCycleMap D p E hE k rule).closedPushforward hp.1 E.2.1
    hdec E.2.2 hp.2.2 rfl (π' := id) rfl
  have hΨ := (isCycleMapOfKernel_gysinCycleMap D (Y.1.ι ≫ p) Y' hY' k ruleY).closedPushforward
    hYg.1 Y'.2.1 (D.isDecentSpace_of_isGood _ hYg) Y'.2.2 hYg.2.2 rfl (π' := id) rfl
  let K := fun W : IntegralClosedSubspace D.site D.base D.base_mem X =>
    closedSubspaceCyclePushforward D p hp E k (gysinComponentCycle D p E hE k rule W)
  let KY := fun V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor =>
    closedSubspaceCyclePushforward D (Y.1.ι ≫ p) hYg Y' k
      (gysinComponentCycle D (Y.1.ι ≫ p) Y' hY' k ruleY V)
  let R := Set.range (pointsMap D.site D.base D.base_mem _ (Y'.1.ι ≫ Y.1.ι))
  have hT₀ : LocallyFinite fun V : IntegralClosedSubspace D.site D.base D.base_mem
      Y.1.toFunctor => if β.1 V = 0 then (∅ : Set (points D.site D.base D.base_mem X))
        else subspacePointSet D.site D.base D.base_mem X (img V).subspace := by
    refine ((pushY (k + 1) β).2.1.comp_injective himg).subset fun V => ?_
    simp only [Function.comp_apply, hpush]
    exact subset_rfl
  have hT : LocallyFinite fun V : IntegralClosedSubspace D.site D.base D.base_mem
      Y.1.toFunctor => if β.1 V = 0 then (∅ : Set (points D.site D.base D.base_mem X))
        else R ∩ subspacePointSet D.site D.base D.base_mem X (img V).subspace := by
    refine hT₀.subset fun V => ?_
    split_ifs
    · exact subset_rfl
    · exact Set.inter_subset_right
  have h := isCycleFamilySumWithin_finsum.{u, v, u + 1} D p hp k _ hT
    (P := canonicalPrincipalDivisors D p hp k)
    (fun V => β.1 V • (K (img V) - pushY k (KY V)))
    (fun V => by
      by_cases hV : β.1 V = 0
      · simp only [hV, if_true, zero_smul]
        exact isCycleFamilySumWithin_zero D p hp k _
      · simp only [hV, if_false]
        exact (isCanonicallyRationallyEquivalentToZeroWithin_gysinComponentCycle_sub.{v} D p hp s
          Y hL k V).zsmul neg_mem_canonicalPrincipalDivisors _)
    (α := closedSubspaceCyclePushforward D p hp E k
        (gysinCycleMap D p E hE k rule (pushY (k + 1) β)) -
      pushY k (closedSubspaceCyclePushforward D (Y.1.ι ≫ p) hYg Y' k
        (gysinCycleMap D (Y.1.ι ≫ p) Y' hY' k ruleY β)))
    (fun Z => ?_)
  · refine h.mono (Set.iUnion_subset fun V => ?_)
    split_ifs with hV
    · exact Set.empty_subset _
    · exact Set.inter_subset_inter subset_rfl (Set.subset_iUnion_of_subset V (by rw [if_neg hV]))
  -- the coefficients
  have hreindex : ∑ᶠ Z' : IntegralClosedSubspace D.site D.base D.base_mem X,
      (pushY (k + 1) β).1 Z' * (K Z').1 Z = ∑ᶠ V, β.1 V * (K (img V)).1 Z := by
    rw [finsum_eq_finsum_comp_of_support_subset_range himg]
    · simp only [hpush]
    · intro Z' hZ'
      by_contra hne
      refine hZ' ?_
      show (pushY (k + 1) β).1 Z' * _ = 0
      rw [hpush0 _ _ Z' fun V hV => hne ⟨V, hV⟩, zero_mul]
  have hfinX : Function.HasFiniteSupport fun V => β.1 V * (K (img V)).1 Z := by
    refine ((hΦ.finite_support (pushY (k + 1) β) Z).preimage himg.injOn).subset fun V hV => ?_
    simpa only [Function.mem_support, Set.mem_preimage, hpush] using hV
  show (closedSubspaceCyclePushforward D p hp E k
      (gysinCycleMap D p E hE k rule (pushY (k + 1) β))).1 Z -
    (pushY k (closedSubspaceCyclePushforward D (Y.1.ι ≫ p) hYg Y' k
      (gysinCycleMap D (Y.1.ι ≫ p) Y' hY' k ruleY β))).1 Z = _
  have hA : (closedSubspaceCyclePushforward D p hp E k
      (gysinCycleMap D p E hE k rule (pushY (k + 1) β))).1 Z =
        ∑ᶠ W, (pushY (k + 1) β).1 W * (K W).1 Z := hΦ.apply _ Z
  rw [hA, hreindex]
  by_cases hZ : ∃ V₀, img V₀ = Z
  · obtain ⟨V₀, rfl⟩ := hZ
    have hB : (closedSubspaceCyclePushforward D (Y.1.ι ≫ p) hYg Y' k
        (gysinCycleMap D (Y.1.ι ≫ p) Y' hY' k ruleY β)).1 V₀ =
          ∑ᶠ V, β.1 V * (KY V).1 V₀ := hΨ.apply β V₀
    rw [hpush, hB, ← finsum_sub_distrib hfinX (hΨ.finite_support β V₀)]
    refine finsum_congr fun V => ?_
    show _ = β.1 V * ((K (img V)).1 (img V₀) - (pushY k (KY V)).1 (img V₀))
    rw [hpush, mul_sub]
  · rw [hpush0 _ _ Z fun V hV => hZ ⟨V, hV⟩, sub_zero]
    refine finsum_congr fun V => ?_
    show _ = β.1 V * ((K (img V)).1 Z - (pushY k (KY V)).1 Z)
    rw [hpush0 _ _ Z fun V hV => hZ ⟨V, hV⟩, sub_zero]

end Restriction

end AlgebraicGeometry.Space

end
