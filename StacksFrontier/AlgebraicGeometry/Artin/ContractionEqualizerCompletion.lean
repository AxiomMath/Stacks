module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism

/-!
# The completed equalizer square of Artin's contraction functor

In the situation of Stacks 0GH8 let `(Z₁, u'₁, x̂₁)` and `(Z₂, u'₂, x̂₂)` be two elements of
`F(V)` with chosen compatibility witnesses, and let `V' = V'₁ ×_V V'₂`, `E' ⟶ V'`,
`Z = Z₁ ∩ Z₂` and `E_W ⟶ V_{/Z}` be as in `AlgebraicGeometry.Artin.ContractionEqualizer`.
**Stacks 0GHD**, assertion (3), says that the morphism `E'_{/Z} ⟶ V_{/Z}` factors through `E_W`
and that the square

```
E'_{/Z} ⟶ X'_{/T'}
   ↓          ↓ g
  E_W   ⟶    W
```

is cartesian. This file proves both, at the level of fppf sheaves of `Type (u + 1)`.

## Main definitions

* `AlgebraicGeometry.Artin.ContractionEqualizer.centerEqz`: the closed set `(E' ⟶ V)⁻¹ Z`.
* `AlgebraicGeometry.Artin.ContractionEqualizer.completedToBase`: the morphism
  `E'_{/Z} ⟶ V_{/Z}`, the completion of `E' ⟶ V`.
* `AlgebraicGeometry.Artin.ContractionEqualizer.completedToSituation`: the morphism
  `E'_{/Z} ⟶ X'_{/T'}`, the completion of the common morphism `E' ⟶ X'`.
* `AlgebraicGeometry.Artin.ContractionEqualizer.completedToEW`: the factorization
  `E'_{/Z} ⟶ E_W`.

## Main results

* `AlgebraicGeometry.Artin.ContractionEqualizer.completedToBase_comp_xhat₁_eq`: the morphism
  `E'_{/Z} ⟶ V_{/Z}` equalizes the two morphisms `V_{/Z} ⟶ W`, so factors through `E_W`.
* `AlgebraicGeometry.Artin.ContractionEqualizer.isPullback_completedToSituation_completedToEW`:
  **Stacks 0GHD**, assertion (3), the factorization and the cartesian square.
* `AlgebraicGeometry.Artin.ContractionEqualizer.isSeparatedMorphism_EW`: **Stacks 0GHD**, the
  separatedness half of the sentence "`E_W` is a locally Noetherian formal algebraic space
  separated over `V`": `E_W ⟶ V_{/Z} ⟶ V` is a monomorphism, so its diagonal is an
  isomorphism and hence a closed immersion.

## Implementation notes

The proof is the one the remark leaves to the reader, written out with the completion square
of Stacks 0APV (`AlgebraicGeometry.Space.isPullback_completionSheafMap`). Shrinking the closed
set from `Zᵢ` to `Z ⊆ Zᵢ` is a base change of completions
(`AlgebraicGeometry.Space.isPullback_completionSheafRestrict_id_of_subset`), so pasting it with
the cartesian square of the compatibility witness exhibits `V'_{i,/Z}` as
`V_{/Z} ×_W X'_{/T'}`; completion commutes with the fibre product `V' = V'₁ ×_V V'₂`
(`AlgebraicGeometry.Space.isPullback_completionSheafRestrict`); and `E'_{/Z}` is the equalizer
of the two morphisms `V'_{/Z} ⟶ X'_{/T'}`, because `E'_{/Z} = E' ×_{V'} V'_{/Z}` by Stacks 0APV,
the sheafified universe lift preserves the equalizer `E' ⟶ V'`, and `X'_{/T'} ⟶ X'` is a
monomorphism.

## What is not proved here

The last sentence of assertion (3), that `E'_{/Z} ⟶ E_W` is a formal modification as the base
change of `g`, is Stacks 0GDN applied to this square, which needs `E_W` to be a locally
Noetherian formal algebraic space — the second half of the remark's "observe" sentence — and
`E_W ⟶ W` to be adic. Neither is proved here; see the module documentation of
`StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizer`.

The other half of that sentence, that `E_W` is a locally Noetherian formal algebraic space, is
not proved here either: `E_W ⟶ V_{/Z}` is a base change of the diagonal of `W`, representable
by schemes by Stacks 0AIP, so it would follow from Stacks 0AIZ for `V_{/Z}` together with
Stacks 0AJI and Stacks 0AQ8, none of which this library has without hypotheses.

## References

* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
* [Stacks Project, Tag 0GDN](https://stacks.math.columbia.edu/tag/0GDN)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHD](https://stacks.math.columbia.edu/tag/0GHD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section CompletionSquares

variable {F'' F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Composing two restriction morphisms of completions gives the restriction morphism along any
morphism equal to the composite. -/
@[reassoc]
theorem completionSheafRestrict_comp_eq (f : F'' ⟶ F') (g : F' ⟶ F) (k : F'' ⟶ F)
    (hk : f ≫ g = k) (T'' : Set (points B S hS F'')) (T' : Set (points B S hS F'))
    (T : Set (points B S hS F)) (h₁ : T'' ⊆ pointsMap B S hS F'' f ⁻¹' T')
    (h₂ : T' ⊆ pointsMap B S hS F' g ⁻¹' T) (h : T'' ⊆ pointsMap B S hS F'' k ⁻¹' T) :
    completionSheafRestrict B S hS f T'' T' h₁ ≫ completionSheafRestrict B S hS g T' T h₂ =
      completionSheafRestrict B S hS k T'' T h := by
  subst hk
  exact (completionSheafRestrict_comp B S hS f g T'' T' T h₁ h₂ h).symm

/-- A containment in an iterated inverse image is a containment in the inverse image under the
composite. -/
theorem subset_preimage_pointsMap_comp (f : F'' ⟶ F') (g : F' ⟶ F)
    {T'' : Set (points B S hS F'')} {T : Set (points B S hS F)}
    (h : T'' ⊆ pointsMap B S hS F'' f ⁻¹' (pointsMap B S hS F' g ⁻¹' T)) :
    T'' ⊆ pointsMap B S hS F'' (f ≫ g) ⁻¹' T := by
  rwa [pointsMap_comp, Set.preimage_comp]

/-- **Stacks 0APV** for the restriction morphisms: if `T'` is the inverse image of `T` under
`f`, the completion square of `f` is cartesian. -/
theorem isPullback_completionSheafInclusion_restrict (f : F' ⟶ F)
    (T' : Set (points B S hS F')) (T : Set (points B S hS F))
    (hT' : T' = pointsMap B S hS F' f ⁻¹' T) (h : T' ⊆ pointsMap B S hS F' f ⁻¹' T) :
    IsPullback (completionSheafInclusion B S hS F' T') (completionSheafRestrict B S hS f T' T h)
      (sheafifiedULiftMap B S hS f) (completionSheafInclusion B S hS F T) := by
  subst hT'
  rw [completionSheafRestrict_self]
  exact isPullback_completionSheafMap B S hS f T

/-- **Shrinking the closed set is a base change of completions.** For `p : F' ⟶ F` and
`T ⊆ T₁`, the completion of `F'` along `p⁻¹ T` is the fibre product of the completion of `F'`
along `p⁻¹ T₁` and of the completion of `F` along `T` over the completion of `F` along `T₁`. -/
theorem isPullback_completionSheafRestrict_id_of_subset (p : F' ⟶ F)
    {T T₁ : Set (points B S hS F)} (hT : T ⊆ T₁) :
    IsPullback (completionSheafRestrict B S hS p (pointsMap B S hS F' p ⁻¹' T) T subset_rfl)
      (completionSheafRestrict B S hS (𝟙 F') (pointsMap B S hS F' p ⁻¹' T)
        (pointsMap B S hS F' p ⁻¹' T₁)
        (subset_preimage_pointsMap_id B S hS (Set.preimage_mono hT)))
      (completionSheafRestrict B S hS (𝟙 F) T T₁ (subset_preimage_pointsMap_id B S hS hT))
      (completionSheafRestrict B S hS p (pointsMap B S hS F' p ⁻¹' T₁) T₁ subset_rfl) := by
  have hb := (isPullback_completionSheafInclusion_restrict B S hS p _ T₁ rfl subset_rfl).flip
  have ho := (isPullback_completionSheafInclusion_restrict B S hS p _ T rfl subset_rfl).flip
  refine IsPullback.of_bot ?_ ?_ hb
  · rw [completionSheafRestrict_comp_inclusion, completionSheafRestrict_comp_inclusion,
      sheafifiedULiftMap_id, sheafifiedULiftMap_id, Category.comp_id, Category.comp_id]
    exact ho
  · rw [completionSheafRestrict_comp_id, completionSheafRestrict_id_comp]

/-- The sheafified universe lift of an equalizer of presheaves is an equalizer: the universe
lift and the fppf sheafification both preserve finite limits. -/
def isLimitForkSheafifiedULiftMapEqualizer (f g : F' ⟶ F) :
    IsLimit (Fork.ofι (sheafifiedULiftMap B S hS (equalizer.ι f g))
      (by rw [← sheafifiedULiftMap_comp, ← sheafifiedULiftMap_comp, equalizer.condition]) :
        Fork (sheafifiedULiftMap B S hS f) (sheafifiedULiftMap B S hS g)) :=
  isLimitForkMapOfIsLimit (fppfSheafification B S hS) _
    (isLimitForkMapOfIsLimit ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u)
      (Type (u + 1))).obj uliftFunctor.{u + 1}) _ (equalizerIsEqualizer f g))

end CompletionSquares

end Space

namespace Artin

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ContractionSituation

variable {c : ContractionSituation B S hS} {V : BigFppfOver B S hS}
    {Z : Set (Space.points B S hS (yoneda.obj V))}
    {u : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor}
    {xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W}

/-- The cartesian square of a compatibility witness, with the containment of sets of points
recorded by `subset_rfl`. -/
theorem CompatibilityWitness.isPullback_xhat'_subset_rfl (w : CompatibilityWitness c V Z u xhat) :
    IsPullback
      (Space.completionSheafRestrict B S hS w.p (Space.pointsMap B S hS w.V' w.p ⁻¹' Z) Z
        subset_rfl) w.xhat' xhat c.g :=
  w.isPullback_xhat'

/-- Composing a restriction morphism into `V'_{/Z}` with `x̂' : V'_{/Z} ⟶ X'_{/T'}` and the
inclusion `X'_{/T'} ⟶ X'` is the inclusion followed by `x'`. -/
theorem CompatibilityWitness.completionSheafRestrict_comp_xhat'_comp_inclusion
    (w : CompatibilityWitness c V Z u xhat) {E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : E ⟶ w.V') (T : Set (Space.points B S hS E))
    (h : T ⊆ Space.pointsMap B S hS E q ⁻¹' (Space.pointsMap B S hS w.V' w.p ⁻¹' Z)) :
    Space.completionSheafRestrict B S hS q T _ h ≫ w.xhat' ≫
        Space.completionSheafInclusion B S hS c.X' c.T' =
      Space.completionSheafInclusion B S hS E T ≫ Space.sheafifiedULiftMap B S hS (q ≫ w.x') := by
  rw [← w.completion_x', ← Category.assoc, Space.completionSheafRestrict_comp_inclusion,
    Category.assoc, Space.sheafifiedULiftMap_comp]

/-- Composing a restriction morphism into `V'_{/Z}` with `x̂'` and `g` is the restriction
morphism along `V'' ⟶ V' ⟶ V` followed by `x̂`, by the cartesian square of the witness. -/
theorem CompatibilityWitness.completionSheafRestrict_comp_xhat'_comp_g
    (w : CompatibilityWitness c V Z u xhat) {E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : E ⟶ w.V') (T : Set (Space.points B S hS E))
    (h : T ⊆ Space.pointsMap B S hS E q ⁻¹' (Space.pointsMap B S hS w.V' w.p ⁻¹' Z))
    (h' : T ⊆ Space.pointsMap B S hS E (q ≫ w.p) ⁻¹' Z) :
    Space.completionSheafRestrict B S hS q T _ h ≫ w.xhat' ≫ c.g =
      Space.completionSheafRestrict B S hS (q ≫ w.p) T Z h' ≫ xhat := by
  rw [← w.isPullback_xhat'_subset_rfl.w,
    Space.completionSheafRestrict_comp_eq_assoc B S hS q w.p (q ≫ w.p) rfl (h := h')]

/-- The identity of `completionSheafRestrict_comp_xhat'_comp_g`, for a restriction to a smaller
closed set `Z₀ ⊆ Z` of the base, along a morphism `k` equal to `q ≫ p`. -/
private theorem CompatibilityWitness.completionSheafRestrict_comp_xhat'_comp_g_of_subset
    (w : CompatibilityWitness c V Z u xhat) {Z₀ : Set (Space.points B S hS (yoneda.obj V))}
    (hZ₀ : Z₀ ⊆ Z) {E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : E ⟶ w.V')
    (k : E ⟶ yoneda.obj V) (hk : q ≫ w.p = k) (T : Set (Space.points B S hS E))
    (h : T ⊆ Space.pointsMap B S hS E q ⁻¹' (Space.pointsMap B S hS w.V' w.p ⁻¹' Z))
    (hk' : T ⊆ Space.pointsMap B S hS E k ⁻¹' Z₀) :
    Space.completionSheafRestrict B S hS q T _ h ≫ w.xhat' ≫ c.g =
      Space.completionSheafRestrict B S hS k T Z₀ hk' ≫
        Space.completionSheafRestrict B S hS (𝟙 _) Z₀ Z
          (Space.subset_preimage_pointsMap_id B S hS hZ₀) ≫ xhat := by
  subst hk
  rw [w.completionSheafRestrict_comp_xhat'_comp_g q T h
    (Space.subset_preimage_pointsMap_comp B S hS _ _ h),
    Space.completionSheafRestrict_comp_id_assoc]

/-- **The witness restricted to a smaller closed set.** For `Z₀ ⊆ Z`, the completion of `V'`
along `p⁻¹ Z₀` is the fibre product of `V_{/Z₀}` and `X'_{/T'}` over `W`, the morphism
`V_{/Z₀} ⟶ W` being `x̂` restricted to `V_{/Z₀}`. -/
theorem CompatibilityWitness.isPullback_restrict (w : CompatibilityWitness c V Z u xhat)
    {Z₀ : Set (Space.points B S hS (yoneda.obj V))} (hZ₀ : Z₀ ⊆ Z) :
    IsPullback
      (Space.completionSheafRestrict B S hS w.p (Space.pointsMap B S hS w.V' w.p ⁻¹' Z₀) Z₀
        subset_rfl)
      (Space.completionSheafRestrict B S hS (𝟙 w.V') (Space.pointsMap B S hS w.V' w.p ⁻¹' Z₀)
          (Space.pointsMap B S hS w.V' w.p ⁻¹' Z)
          (Space.subset_preimage_pointsMap_id B S hS (Set.preimage_mono hZ₀)) ≫ w.xhat')
      (Space.completionSheafRestrict B S hS (𝟙 _) Z₀ Z
          (Space.subset_preimage_pointsMap_id B S hS hZ₀) ≫ xhat)
      c.g :=
  (Space.isPullback_completionSheafRestrict_id_of_subset B S hS w.p hZ₀).paste_vert
    w.isPullback_xhat'_subset_rfl

end ContractionSituation

namespace ContractionEqualizer

variable {c : ContractionSituation B S hS} {V : BigFppfOver B S hS}
    (d : ContractionEqualizer c V)

/-! ### The objects and morphisms of the square -/

/-- The closed set `(E' ⟶ V)⁻¹ Z` of `E'` along which `E'` is completed. -/
abbrev centerEqz : Set (Space.points B S hS d.eqz) :=
  Space.pointsMap B S hS d.eqz d.toBase ⁻¹' d.Z

/-- The set of points of `V'` lying over `Z`, through the first projection. -/
abbrev centerFibProd : Set (Space.points B S hS d.fibProd) :=
  Space.pointsMap B S hS d.fibProd (pullback.fst d.w₁.p d.w₂.p) ⁻¹'
    (Space.pointsMap B S hS d.w₁.V' d.w₁.p ⁻¹' d.Z)

/-- A point of `V'` lying over `Z` through the first projection lies over `Z` through the
second. -/
theorem centerFibProd_subset_snd :
    d.centerFibProd ⊆ Space.pointsMap B S hS d.fibProd (pullback.snd d.w₁.p d.w₂.p) ⁻¹'
      (Space.pointsMap B S hS d.w₂.V' d.w₂.p ⁻¹' d.Z) :=
  (Space.preimage_pointsMap_eq_of_comm B S hS pullback.condition d.Z).subset

/-- A point of `V'` lying over `Z` maps under the first projection to a point of `V'₁` lying
over `Z₁`. -/
theorem centerFibProd_subset_fst₁ :
    d.centerFibProd ⊆ Space.pointsMap B S hS d.fibProd (pullback.fst d.w₁.p d.w₂.p) ⁻¹'
      (Space.pointsMap B S hS d.w₁.V' d.w₁.p ⁻¹' d.t₁.Z) :=
  fun _ hx => d.Z_subset_t₁ hx

/-- A point of `V'` lying over `Z` maps under the second projection to a point of `V'₂` lying
over `Z₂`. -/
theorem centerFibProd_subset_snd₂ :
    d.centerFibProd ⊆ Space.pointsMap B S hS d.fibProd (pullback.snd d.w₁.p d.w₂.p) ⁻¹'
      (Space.pointsMap B S hS d.w₂.V' d.w₂.p ⁻¹' d.t₂.Z) :=
  fun _ hx => d.Z_subset_t₂ (d.centerFibProd_subset_snd hx)

/-- The closed set `(E' ⟶ V)⁻¹ Z` of `E'` is the preimage under `E' ⟶ V'` of the set of
points of `V'` lying over `Z`. -/
theorem centerEqz_eq_preimage_centerFibProd :
    d.centerEqz = Space.pointsMap B S hS d.eqz (equalizer.ι d.x₁ d.x₂) ⁻¹' d.centerFibProd := by
  simp only [centerEqz, centerFibProd, toBase, Space.pointsMap_comp, Set.preimage_comp]

/-- A point of `E'` lying over `Z` maps under `E' ⟶ V'₁` to a point lying over `Z₁`. -/
theorem centerEqz_subset_toFst : d.centerEqz ⊆ Space.pointsMap B S hS d.eqz d.toFst ⁻¹'
    (Space.pointsMap B S hS d.w₁.V' d.w₁.p ⁻¹' d.t₁.Z) := by
  intro x hx
  have : Space.pointsMap B S hS d.eqz (d.toFst ≫ d.w₁.p) x ∈ d.Z := by
    rw [d.toFst_comp_p]
    exact hx
  rw [Space.pointsMap_comp] at this
  exact d.Z_subset_t₁ this

/-- A point of `E'` lying over `Z` maps under `E' ⟶ V'₂` to a point lying over `Z₂`. -/
theorem centerEqz_subset_toSnd : d.centerEqz ⊆ Space.pointsMap B S hS d.eqz d.toSnd ⁻¹'
    (Space.pointsMap B S hS d.w₂.V' d.w₂.p ⁻¹' d.t₂.Z) := by
  intro x hx
  have : Space.pointsMap B S hS d.eqz (d.toSnd ≫ d.w₂.p) x ∈ d.Z := by
    rw [d.toSnd_comp_p]
    exact hx
  rw [Space.pointsMap_comp] at this
  exact d.Z_subset_t₂ this

/-- A point of `E'` lying over `Z` is carried into `T'` by the morphism `E' ⟶ V'₁ ⟶ X'`. -/
theorem centerEqz_subset_preimage_closedSubset :
    d.centerEqz ⊆ Space.pointsMap B S hS d.eqz (d.toFst ≫ d.w₁.x') ⁻¹' c.T' := by
  intro y hy
  induction y using Quot.ind with | _ q => ?_
  have hq := d.centerEqz_subset_toFst hy
  rw [Set.mem_preimage, Space.pointsMap_class] at hq
  rw [Set.mem_preimage, Space.pointsMap_class, Space.FieldValuedPoint.map_comp]
  exact d.w₁.class_map_witnessMap_mem_closedSubset _ hq

/-- The morphism `E'_{/Z} ⟶ V_{/Z}`, the completion of `E' ⟶ V` along `Z`. -/
def completedToBase :
    Space.completionSheaf B S hS d.eqz d.centerEqz ⟶
      Space.completionSheaf B S hS (yoneda.obj V) d.Z :=
  Space.completionSheafRestrict B S hS d.toBase d.centerEqz d.Z subset_rfl

/-- The morphism `E'_{/Z} ⟶ X'_{/T'}`, the completion of the morphism `E' ⟶ X'` along which the
two morphisms `E' ⟶ V'ᵢ ⟶ X'` agree. -/
def completedToSituation : Space.completionSheaf B S hS d.eqz d.centerEqz ⟶
    Space.completionSheaf B S hS c.X' c.T' :=
  Space.completionSheafRestrict B S hS (d.toFst ≫ d.w₁.x') d.centerEqz c.T'
    d.centerEqz_subset_preimage_closedSubset

/-- `E'_{/Z} ⟶ X'_{/T'}` is the composite of `E'_{/Z} ⟶ V'_{1,/Z₁}` and `x̂'₁`. -/
theorem completedToSituation_eq_fst : d.completedToSituation =
    Space.completionSheafRestrict B S hS d.toFst d.centerEqz _ d.centerEqz_subset_toFst ≫
      d.w₁.xhat' := by
  have := Space.mono_completionSheafInclusion B S hS c.X' c.T'
  rw [← cancel_mono (Space.completionSheafInclusion B S hS c.X' c.T'), completedToSituation,
    Space.completionSheafRestrict_comp_inclusion, Category.assoc,
    d.w₁.completionSheafRestrict_comp_xhat'_comp_inclusion]

/-- `E'_{/Z} ⟶ X'_{/T'}` is the composite of `E'_{/Z} ⟶ V'_{2,/Z₂}` and `x̂'₂`. -/
theorem completedToSituation_eq_snd : d.completedToSituation =
    Space.completionSheafRestrict B S hS d.toSnd d.centerEqz _ d.centerEqz_subset_toSnd ≫
      d.w₂.xhat' := by
  have := Space.mono_completionSheafInclusion B S hS c.X' c.T'
  rw [← cancel_mono (Space.completionSheafInclusion B S hS c.X' c.T'), completedToSituation,
    Space.completionSheafRestrict_comp_inclusion, Category.assoc,
    d.w₂.completionSheafRestrict_comp_xhat'_comp_inclusion, d.toFst_comp_witnessMap_eq]

/-- The composite `E'_{/Z} ⟶ X'_{/T'} ⟶ W` equals `E'_{/Z} ⟶ V_{/Z} ⟶ V_{/Z₁} ⟶ W`. -/
theorem completedToSituation_comp_g_eq_xhat₁ :
    d.completedToSituation ≫ c.g = d.completedToBase ≫ d.xhat₁ := by
  rw [d.completedToSituation_eq_fst, Category.assoc]
  exact d.w₁.completionSheafRestrict_comp_xhat'_comp_g_of_subset d.Z_subset_t₁ d.toFst d.toBase
    d.toFst_comp_p _ d.centerEqz_subset_toFst subset_rfl

/-- The composite `E'_{/Z} ⟶ X'_{/T'} ⟶ W` equals `E'_{/Z} ⟶ V_{/Z} ⟶ V_{/Z₂} ⟶ W`. -/
theorem completedToSituation_comp_g_eq_xhat₂ :
    d.completedToSituation ≫ c.g = d.completedToBase ≫ d.xhat₂ := by
  rw [d.completedToSituation_eq_snd, Category.assoc]
  exact d.w₂.completionSheafRestrict_comp_xhat'_comp_g_of_subset d.Z_subset_t₂ d.toSnd d.toBase
    d.toSnd_comp_p _ d.centerEqz_subset_toSnd subset_rfl

/-- **Stacks 0GHD**, assertion (3), first half: `E'_{/Z} ⟶ V_{/Z}` equalizes the two morphisms
`V_{/Z} ⟶ V_{/Zᵢ} ⟶ W`, that is, it factors through their equalizer `E_W`. -/
theorem completedToBase_comp_xhat₁_eq : d.completedToBase ≫ d.xhat₁ = d.completedToBase ≫ d.xhat₂ :=
  d.completedToSituation_comp_g_eq_xhat₁.symm.trans d.completedToSituation_comp_g_eq_xhat₂

/-- The factorization `E'_{/Z} ⟶ E_W` of `E'_{/Z} ⟶ V_{/Z}`. -/
def completedToEW : Space.completionSheaf B S hS d.eqz d.centerEqz ⟶ d.EW :=
  equalizer.lift d.completedToBase d.completedToBase_comp_xhat₁_eq

/-- The factorization `E'_{/Z} ⟶ E_W` composed with `E_W ⟶ V_{/Z}` is `E'_{/Z} ⟶ V_{/Z}`. -/
@[simp]
theorem completedToEW_comp_ι : d.completedToEW ≫ equalizer.ι d.xhat₁ d.xhat₂ = d.completedToBase :=
  equalizer.lift_ι _ _

/-! ### The completion of `V'` and of `E'` -/

/-- The morphism `V'_{/Z} ⟶ V'_{1,/Z}`. -/
abbrev completedFst : Space.completionSheaf B S hS d.fibProd d.centerFibProd ⟶
    Space.completionSheaf B S hS d.w₁.V' (Space.pointsMap B S hS d.w₁.V' d.w₁.p ⁻¹' d.Z) :=
  Space.completionSheafRestrict B S hS (pullback.fst d.w₁.p d.w₂.p) _ _ subset_rfl

/-- The morphism `V'_{/Z} ⟶ V'_{2,/Z}`. -/
abbrev completedSnd : Space.completionSheaf B S hS d.fibProd d.centerFibProd ⟶
    Space.completionSheaf B S hS d.w₂.V' (Space.pointsMap B S hS d.w₂.V' d.w₂.p ⁻¹' d.Z) :=
  Space.completionSheafRestrict B S hS (pullback.snd d.w₁.p d.w₂.p) _ _ d.centerFibProd_subset_snd

/-- Completion commutes with the fibre product `V' = V'₁ ×_V V'₂`. -/
theorem isPullback_completedFst_completedSnd :
    IsPullback d.completedFst d.completedSnd
      (Space.completionSheafRestrict B S hS d.w₁.p _ d.Z subset_rfl)
      (Space.completionSheafRestrict B S hS d.w₂.p _ d.Z subset_rfl) :=
  Space.isPullback_completionSheafRestrict B S hS _ _ _ _ (IsPullback.of_hasPullback _ _) d.Z
    _ _ _ rfl rfl rfl subset_rfl d.centerFibProd_subset_snd subset_rfl subset_rfl

/-- The morphism `E'_{/Z} ⟶ V'_{/Z}`. -/
abbrev completedι : Space.completionSheaf B S hS d.eqz d.centerEqz ⟶
    Space.completionSheaf B S hS d.fibProd d.centerFibProd :=
  Space.completionSheafRestrict B S hS (equalizer.ι d.x₁ d.x₂) _ _
    d.centerEqz_eq_preimage_centerFibProd.subset

/-- The square formed by `E'_{/Z} ⟶ E'`, `E'_{/Z} ⟶ V'_{/Z}`, `E' ⟶ V'` and `V'_{/Z} ⟶ V'`
is cartesian, after sheafified universe lift: `E'_{/Z} = E' ×_{V'} V'_{/Z}`. -/
theorem isPullback_completedι :
    IsPullback (Space.completionSheafInclusion B S hS d.eqz d.centerEqz) d.completedι
      (Space.sheafifiedULiftMap B S hS (equalizer.ι d.x₁ d.x₂))
      (Space.completionSheafInclusion B S hS d.fibProd d.centerFibProd) :=
  Space.isPullback_completionSheafInclusion_restrict B S hS _ _ _
    d.centerEqz_eq_preimage_centerFibProd d.centerEqz_eq_preimage_centerFibProd.subset

/-- The morphism `E'_{/Z} ⟶ V'_{/Z}` is a monomorphism. -/
theorem mono_completedι : Mono d.completedι := by
  have hm : Mono (Space.sheafifiedULiftMap B S hS (equalizer.ι d.x₁ d.x₂)) :=
    mono_of_isLimit_fork (Space.isLimitForkSheafifiedULiftMapEqualizer B S hS d.x₁ d.x₂)
  constructor
  intro Y a b hab
  refine d.isPullback_completedι.hom_ext ?_ hab
  refine (cancel_mono (Space.sheafifiedULiftMap B S hS (equalizer.ι d.x₁ d.x₂))).1 ?_
  rw [Category.assoc, Category.assoc, d.isPullback_completedι.w, ← Category.assoc,
    ← Category.assoc, hab]

/-- The two morphisms `V'_{/Z} ⟶ V'_{i,/Zᵢ} ⟶ X'_{/T'}`; `E'_{/Z}` is their equalizer. -/
def completedX₁ : Space.completionSheaf B S hS d.fibProd d.centerFibProd ⟶
    Space.completionSheaf B S hS c.X' c.T' :=
  Space.completionSheafRestrict B S hS (pullback.fst d.w₁.p d.w₂.p) d.centerFibProd
    (Space.pointsMap B S hS d.w₁.V' d.w₁.p ⁻¹' d.t₁.Z) d.centerFibProd_subset_fst₁ ≫
      d.w₁.xhat'

/-- The second of the two morphisms `V'_{/Z} ⟶ X'_{/T'}`. -/
def completedX₂ : Space.completionSheaf B S hS d.fibProd d.centerFibProd ⟶
    Space.completionSheaf B S hS c.X' c.T' :=
  Space.completionSheafRestrict B S hS (pullback.snd d.w₁.p d.w₂.p) d.centerFibProd
    (Space.pointsMap B S hS d.w₂.V' d.w₂.p ⁻¹' d.t₂.Z)
    d.centerFibProd_subset_snd₂ ≫ d.w₂.xhat'

/-- The composite `E'_{/Z} ⟶ V'_{/Z} ⟶ X'_{/T'}` through the first factor is
`E'_{/Z} ⟶ X'_{/T'}`. -/
theorem completedι_comp_completedX₁ : d.completedι ≫ d.completedX₁ = d.completedToSituation := by
  rw [completedX₁, Space.completionSheafRestrict_comp_eq_assoc B S hS (equalizer.ι d.x₁ d.x₂)
    (pullback.fst d.w₁.p d.w₂.p) d.toFst rfl (h := d.centerEqz_subset_toFst),
    d.completedToSituation_eq_fst]

/-- The composite `E'_{/Z} ⟶ V'_{/Z} ⟶ X'_{/T'}` through the second factor is
`E'_{/Z} ⟶ X'_{/T'}`. -/
theorem completedι_comp_completedX₂ : d.completedι ≫ d.completedX₂ = d.completedToSituation := by
  rw [completedX₂, Space.completionSheafRestrict_comp_eq_assoc B S hS (equalizer.ι d.x₁ d.x₂)
    (pullback.snd d.w₁.p d.w₂.p) d.toSnd rfl (h := d.centerEqz_subset_toSnd),
    d.completedToSituation_eq_snd]

/-- A morphism into `V'_{/Z}` equalizing the two morphisms to `X'_{/T'}` lifts to `E'_{/Z}`. -/
theorem exists_lift_completedι {Y : FormalSpace.FppfSheaf B S hS}
    (t : Y ⟶ Space.completionSheaf B S hS d.fibProd d.centerFibProd)
    (ht : t ≫ d.completedX₁ = t ≫ d.completedX₂) :
    ∃ l : Y ⟶ Space.completionSheaf B S hS d.eqz d.centerEqz, l ≫ d.completedι = t := by
  have h₁ : d.completedX₁ ≫ Space.completionSheafInclusion B S hS c.X' c.T' =
      Space.completionSheafInclusion B S hS d.fibProd d.centerFibProd ≫
        Space.sheafifiedULiftMap B S hS d.x₁ := by
    rw [completedX₁, Category.assoc, d.w₁.completionSheafRestrict_comp_xhat'_comp_inclusion]
    rfl
  have h₂ : d.completedX₂ ≫ Space.completionSheafInclusion B S hS c.X' c.T' =
      Space.completionSheafInclusion B S hS d.fibProd d.centerFibProd ≫
        Space.sheafifiedULiftMap B S hS d.x₂ := by
    rw [completedX₂, Category.assoc, d.w₂.completionSheafRestrict_comp_xhat'_comp_inclusion]
    rfl
  have hfork : (t ≫ Space.completionSheafInclusion B S hS d.fibProd d.centerFibProd) ≫
        Space.sheafifiedULiftMap B S hS d.x₁ =
      (t ≫ Space.completionSheafInclusion B S hS d.fibProd d.centerFibProd) ≫
        Space.sheafifiedULiftMap B S hS d.x₂ := by
    rw [Category.assoc, Category.assoc, ← h₁, ← h₂, ← Category.assoc, ← Category.assoc, ht]
  obtain ⟨k, hk⟩ := Fork.IsLimit.lift' (Space.isLimitForkSheafifiedULiftMapEqualizer B S hS
    d.x₁ d.x₂) _ hfork
  exact ⟨d.isPullback_completedι.lift k t hk, d.isPullback_completedι.lift_snd _ _ _⟩

/-! ### Assertion (3) -/

/-- The cartesian square exhibiting `V'_{1,/Z}` as `V_{/Z} ×_W X'_{/T'}`. -/
theorem isPullback_restrict₁ :
    IsPullback
      (Space.completionSheafRestrict B S hS d.w₁.p
        (Space.pointsMap B S hS d.w₁.V' d.w₁.p ⁻¹' d.Z) d.Z subset_rfl)
      (Space.completionSheafRestrict B S hS (𝟙 d.w₁.V')
          (Space.pointsMap B S hS d.w₁.V' d.w₁.p ⁻¹' d.Z)
          (Space.pointsMap B S hS d.w₁.V' d.w₁.p ⁻¹' d.t₁.Z)
          (Space.subset_preimage_pointsMap_id B S hS (Set.preimage_mono d.Z_subset_t₁)) ≫
        d.w₁.xhat')
      d.xhat₁ c.g :=
  d.w₁.isPullback_restrict d.Z_subset_t₁

/-- The cartesian square exhibiting `V'_{2,/Z}` as `V_{/Z} ×_W X'_{/T'}`. -/
theorem isPullback_restrict₂ :
    IsPullback
      (Space.completionSheafRestrict B S hS d.w₂.p
        (Space.pointsMap B S hS d.w₂.V' d.w₂.p ⁻¹' d.Z) d.Z subset_rfl)
      (Space.completionSheafRestrict B S hS (𝟙 d.w₂.V')
          (Space.pointsMap B S hS d.w₂.V' d.w₂.p ⁻¹' d.Z)
          (Space.pointsMap B S hS d.w₂.V' d.w₂.p ⁻¹' d.t₂.Z)
          (Space.subset_preimage_pointsMap_id B S hS (Set.preimage_mono d.Z_subset_t₂)) ≫
        d.w₂.xhat')
      d.xhat₂ c.g :=
  d.w₂.isPullback_restrict d.Z_subset_t₂

/-- The composite `V'_{/Z} ⟶ V'_{1,/Z} ⟶ V'_{1,/Z₁} ⟶ X'_{/T'}` is the first of the two
morphisms `V'_{/Z} ⟶ X'_{/T'}`. -/
theorem completedFst_comp_restrict :
    d.completedFst ≫ Space.completionSheafRestrict B S hS (𝟙 d.w₁.V')
        (Space.pointsMap B S hS d.w₁.V' d.w₁.p ⁻¹' d.Z)
        (Space.pointsMap B S hS d.w₁.V' d.w₁.p ⁻¹' d.t₁.Z)
        (Space.subset_preimage_pointsMap_id B S hS (Set.preimage_mono d.Z_subset_t₁)) ≫
        d.w₁.xhat' = d.completedX₁ := by
  rw [Space.completionSheafRestrict_comp_id_assoc]
  rfl

/-- The composite `V'_{/Z} ⟶ V'_{2,/Z} ⟶ V'_{2,/Z₂} ⟶ X'_{/T'}` is the second of the two
morphisms `V'_{/Z} ⟶ X'_{/T'}`. -/
theorem completedSnd_comp_restrict :
    d.completedSnd ≫ Space.completionSheafRestrict B S hS (𝟙 d.w₂.V')
        (Space.pointsMap B S hS d.w₂.V' d.w₂.p ⁻¹' d.Z)
        (Space.pointsMap B S hS d.w₂.V' d.w₂.p ⁻¹' d.t₂.Z)
        (Space.subset_preimage_pointsMap_id B S hS (Set.preimage_mono d.Z_subset_t₂)) ≫
        d.w₂.xhat' = d.completedX₂ := by
  rw [Space.completionSheafRestrict_comp_id_assoc]
  rfl

/-- The composite `E'_{/Z} ⟶ V'_{/Z} ⟶ V'_{1,/Z} ⟶ V_{/Z}` is `E'_{/Z} ⟶ V_{/Z}`. -/
theorem completedι_comp_completedFst_comp_p :
    d.completedι ≫ d.completedFst ≫ Space.completionSheafRestrict B S hS d.w₁.p _ d.Z subset_rfl =
      d.completedToBase := by
  rw [Space.completionSheafRestrict_comp_eq B S hS (pullback.fst d.w₁.p d.w₂.p) d.w₁.p
      (pullback.fst d.w₁.p d.w₂.p ≫ d.w₁.p) rfl
      (h := Space.subset_preimage_pointsMap_comp B S hS _ _ (subset_rfl : d.centerFibProd ⊆ _)),
    Space.completionSheafRestrict_comp_eq B S hS (equalizer.ι d.x₁ d.x₂)
      (pullback.fst d.w₁.p d.w₂.p ≫ d.w₁.p) d.toBase rfl (h := subset_rfl)]
  rfl

/-- The composite `E'_{/Z} ⟶ V'_{/Z} ⟶ V'_{2,/Z} ⟶ V_{/Z}` is `E'_{/Z} ⟶ V_{/Z}`. -/
theorem completedι_comp_completedSnd_comp_p :
    d.completedι ≫ d.completedSnd ≫ Space.completionSheafRestrict B S hS d.w₂.p _ d.Z subset_rfl =
      d.completedToBase := by
  rw [Space.completionSheafRestrict_comp_eq B S hS (pullback.snd d.w₁.p d.w₂.p) d.w₂.p
      (pullback.snd d.w₁.p d.w₂.p ≫ d.w₂.p) rfl
      (h := Space.subset_preimage_pointsMap_comp B S hS _ _ d.centerFibProd_subset_snd),
    Space.completionSheafRestrict_comp_eq B S hS (equalizer.ι d.x₁ d.x₂)
      (pullback.snd d.w₁.p d.w₂.p ≫ d.w₂.p) d.toBase
      (by rw [← d.toSnd_comp_p, toSnd, Category.assoc]) (h := subset_rfl)]
  rfl

/-- Existence half of the universal property of the square of assertion (3). -/
theorem exists_lift_isPullback {Y : FormalSpace.FppfSheaf B S hS}
    (a : Y ⟶ Space.completionSheaf B S hS c.X' c.T') (e : Y ⟶ d.EW)
    (hae : a ≫ c.g = e ≫ equalizer.ι d.xhat₁ d.xhat₂ ≫ d.xhat₁) :
    ∃ l : Y ⟶ Space.completionSheaf B S hS d.eqz d.centerEqz,
      l ≫ d.completedToSituation = a ∧ l ≫ d.completedToEW = e := by
  set y := e ≫ equalizer.ι d.xhat₁ d.xhat₂ with hy
  have hy₁ : y ≫ d.xhat₁ = a ≫ c.g := by rw [hy, Category.assoc, hae]
  have hy₂ : y ≫ d.xhat₂ = a ≫ c.g := by
    rw [hy, Category.assoc, ← equalizer.condition, hae]
  set r₁ := d.isPullback_restrict₁.lift y a hy₁ with hr₁
  set r₂ := d.isPullback_restrict₂.lift y a hy₂ with hr₂
  have hr : r₁ ≫ Space.completionSheafRestrict B S hS d.w₁.p _ d.Z subset_rfl =
      r₂ ≫ Space.completionSheafRestrict B S hS d.w₂.p _ d.Z subset_rfl := by
    rw [hr₁, hr₂, IsPullback.lift_fst, IsPullback.lift_fst]
  set v := d.isPullback_completedFst_completedSnd.lift r₁ r₂ hr with hv
  have hv₁ : v ≫ d.completedX₁ = a := by
    rw [← d.completedFst_comp_restrict, ← Category.assoc, hv, IsPullback.lift_fst, hr₁,
      IsPullback.lift_snd]
  have hv₂ : v ≫ d.completedX₂ = a := by
    rw [← d.completedSnd_comp_restrict, ← Category.assoc, hv, IsPullback.lift_snd, hr₂,
      IsPullback.lift_snd]
  obtain ⟨l, hl⟩ := d.exists_lift_completedι v (hv₁.trans hv₂.symm)
  refine ⟨l, ?_, ?_⟩
  · rw [← d.completedι_comp_completedX₁, ← Category.assoc, hl, hv₁]
  · refine (cancel_mono (equalizer.ι d.xhat₁ d.xhat₂)).1 ?_
    rw [Category.assoc, completedToEW_comp_ι, ← d.completedι_comp_completedFst_comp_p,
      ← Category.assoc, hl, ← Category.assoc, hv, IsPullback.lift_fst, hr₁, IsPullback.lift_fst]

/-- Uniqueness half of the universal property of the square of assertion (3). -/
theorem lift_unique {Y : FormalSpace.FppfSheaf B S hS}
    (l l' : Y ⟶ Space.completionSheaf B S hS d.eqz d.centerEqz)
    (h₁ : l ≫ d.completedToSituation = l' ≫ d.completedToSituation)
    (h₂ : l ≫ d.completedToEW = l' ≫ d.completedToEW) : l = l' := by
  have := d.mono_completedι
  have hb : l ≫ d.completedToBase = l' ≫ d.completedToBase := by
    rw [← completedToEW_comp_ι, ← Category.assoc, h₂, Category.assoc]
  refine (cancel_mono d.completedι).1 (d.isPullback_completedFst_completedSnd.hom_ext ?_ ?_)
  · refine d.isPullback_restrict₁.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [d.completedι_comp_completedFst_comp_p, hb]
    · simp only [Category.assoc]
      rw [d.completedFst_comp_restrict, d.completedι_comp_completedX₁, h₁]
  · refine d.isPullback_restrict₂.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [d.completedι_comp_completedSnd_comp_p, hb]
    · simp only [Category.assoc]
      rw [d.completedSnd_comp_restrict, d.completedι_comp_completedX₂, h₁]

/-- **Stacks 0GHD**, assertion (3): the morphism `E'_{/Z} ⟶ V_{/Z}` factors through `E_W`, by
`AlgebraicGeometry.Artin.ContractionEqualizer.completedToEW`, and the square formed by
`E'_{/Z} ⟶ X'_{/T'}`, `E'_{/Z} ⟶ E_W`, the formal modification `g : X'_{/T'} ⟶ W` and the
morphism `E_W ⟶ V_{/Z} ⟶ W` is cartesian. -/
@[stacks 0GHD "assertion (3), the factorization and the cartesian square in full: that \
E'_{/Z} → V_{/Z} factors through E_W and that the square E'_{/Z} → X'_{/T'}, E_W → W over \
g is cartesian, in the category of fppf sheaves where formal algebraic spaces over S live. \
The closing sentence of (3), that E'_{/Z} → E_W is then a formal modification as a base \
change of g, is Stacks 0GDN applied to this square and is not claimed here. Proved for an \
arbitrary object V of the big fppf site over S, so the tag's own hypothesis that V be a \
locally Noetherian scheme over S is a special case"]
theorem isPullback_completedToSituation_completedToEW :
    d.completedToEW ≫ equalizer.ι d.xhat₁ d.xhat₂ = d.completedToBase ∧
      IsPullback d.completedToSituation d.completedToEW c.g
        (equalizer.ι d.xhat₁ d.xhat₂ ≫ d.xhat₁) := by
  refine ⟨d.completedToEW_comp_ι, ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => Classical.choose (d.exists_lift_isPullback s.fst s.snd s.condition))
    (fun s => (Classical.choose_spec (d.exists_lift_isPullback s.fst s.snd s.condition)).1)
    (fun s => (Classical.choose_spec (d.exists_lift_isPullback s.fst s.snd s.condition)).2)
    (fun s m h₁ h₂ => d.lift_unique _ _
      (h₁.trans (Classical.choose_spec
        (d.exists_lift_isPullback s.fst s.snd s.condition)).1.symm)
      (h₂.trans (Classical.choose_spec
        (d.exists_lift_isPullback s.fst s.snd s.condition)).2.symm))⟩⟩⟩
  rw [d.completedToSituation_comp_g_eq_xhat₁, ← Category.assoc, completedToEW_comp_ι]

/-! ### `E_W` is separated over `V` -/

/-- The morphism `E_W ⟶ V_{/Z} ⟶ V` into (the sheafified universe lift of) `V`. -/
def EWToBase : d.EW ⟶ Space.sheafifiedULift B S hS (yoneda.obj V) :=
  equalizer.ι d.xhat₁ d.xhat₂ ≫ Space.completionSheafInclusion B S hS (yoneda.obj V) d.Z

/-- The morphism `E_W ⟶ V` is a monomorphism. -/
instance mono_EWToBase : Mono d.EWToBase := by
  have := Space.mono_completionSheafInclusion B S hS (yoneda.obj V) d.Z
  unfold EWToBase
  infer_instance

/-- **Stacks 0GHD**, the separatedness half of the sentence "`E_W` is a locally Noetherian
formal algebraic space separated over `V`": the morphism `E_W ⟶ V` is separated, its relative
diagonal being an isomorphism because `E_W ⟶ V_{/Z}` and `V_{/Z} ⟶ V` are monomorphisms. -/
@[stacks 0GHD "the sentence `E_W is a locally Noetherian formal algebraic space separated over \
V', the separatedness half in full: that E_W ⟶ V is separated, i.e. that its relative \
diagonal is a closed immersion. The other half, that E_W is a locally Noetherian formal \
algebraic space, is not claimed here. Proved for an arbitrary object V of the big fppf site \
over S, so the tag's own hypothesis that V be a locally Noetherian scheme over S is a special \
case"]
theorem isSeparatedMorphism_EW : FormalSpace.IsSeparatedMorphism B S hS d.EWToBase :=
  FormalSpace.isClosedImmersion_of_isIso B S hS _

end ContractionEqualizer

end Artin

end AlgebraicGeometry

end
