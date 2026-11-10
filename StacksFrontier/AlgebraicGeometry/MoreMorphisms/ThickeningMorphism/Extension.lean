module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Cartesian
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Separated
public import StacksFrontier.AlgebraicGeometry.Morphisms.DifferentialsAndValuative.ClosedImmersionInfinitesimal

/-!
# Immersions, properness and finiteness extend over a thickening

Let

```
X --f--→ Y
|        |
i        j
↓        ↓
X' -f'-→ Y'
```

be a cartesian morphism of thickenings in which both `f` and `f'` are locally of finite type.
Then `f` is a closed immersion, an immersion, proper, or finite exactly when `f'` is.

In each case the implication from `f'` to `f` is base change. In the other direction, a closed
immersion is detected after the point-bijective closed base change along `j`; an immersion is
reduced to the closed-immersion case by restricting to the coborder of the range of `f`, which
is an open subscheme of `Y` whose image in `Y'` is open because `j` is a homeomorphism; and
properness is the conjunction of separatedness, universal closedness and local finite type, the
first two of which hold for any morphism of thickenings. Finiteness is properness together with
local quasi-finiteness, by Zariski's main theorem, and local quasi-finiteness is invariant
because the two thickenings are homeomorphisms on points.

## Main definitions

* `Stacks.Thickenings.CartesianFiniteTypeMorphism`: a cartesian morphism of thickenings whose
  two component morphisms are locally of finite type.

## Main results

* `Stacks.Thickenings.CartesianFiniteTypeMorphism.isClosedImmersion_iff`
* `Stacks.Thickenings.CartesianFiniteTypeMorphism.isImmersion_iff`
* `Stacks.Thickenings.CartesianFiniteTypeMorphism.isProper_iff`
* `Stacks.Thickenings.CartesianFiniteTypeMorphism.isFinite_iff`

## Implementation notes

The commutative square is a morphism in the arrow category of schemes, so its commutativity is
the field `w` of `CategoryTheory.Arrow.Hom`; the identification of `X` with `Y ×_{Y'} X'` is
recorded by `CategoryTheory.IsPullback`, which avoids choosing a fibre product. No finiteness
condition is imposed on the thickenings themselves.

## References

* [Stacks Project, Tag 0BPG](https://stacks.math.columbia.edu/tag/0BPG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Thickenings

universe u

/-- A cartesian morphism of thickenings of schemes whose two component morphisms are locally
of finite type. -/
structure CartesianFiniteTypeMorphism where
  /-- The closed subscheme of the source thickening. -/
  X : Scheme.{u}
  /-- The ambient scheme of the source thickening. -/
  X' : Scheme.{u}
  /-- The closed subscheme of the target thickening. -/
  Y : Scheme.{u}
  /-- The ambient scheme of the target thickening. -/
  Y' : Scheme.{u}
  /-- The source thickening. -/
  i : X ⟶ X'
  /-- The target thickening. -/
  j : Y ⟶ Y'
  /-- The commutative square between the two thickenings. -/
  morphism : Arrow.mk i ⟶ Arrow.mk j
  /-- The source inclusion is a thickening. -/
  sourceThickening : IsThickening i
  /-- The target inclusion is a thickening. -/
  targetThickening : IsThickening j
  /-- The map between the closed subschemes is locally of finite type. -/
  [locallyOfFiniteType_left : LocallyOfFiniteType morphism.left]
  /-- The map between the ambient schemes is locally of finite type. -/
  [locallyOfFiniteType_right : LocallyOfFiniteType morphism.right]
  /-- The square identifies `X` with `Y ×_{Y'} X'`. -/
  cartesian : IsPullback morphism.left i j morphism.right

attribute [instance]
  CartesianFiniteTypeMorphism.locallyOfFiniteType_left
  CartesianFiniteTypeMorphism.locallyOfFiniteType_right

namespace CartesianFiniteTypeMorphism

/-- The morphism `f : X ⟶ Y` between the closed subschemes. -/
abbrev f (S : CartesianFiniteTypeMorphism.{u}) : S.X ⟶ S.Y := S.morphism.left

/-- The morphism `f' : X' ⟶ Y'` between the ambient schemes. -/
abbrev f' (S : CartesianFiniteTypeMorphism.{u}) : S.X' ⟶ S.Y' := S.morphism.right

/-- The thickenings are homeomorphisms on points, compatibly with the maps `f` and `f'`. -/
private theorem exists_homeomorph_comm (S : CartesianFiniteTypeMorphism.{u}) :
    ∃ (hi : S.X ≃ₜ S.X') (hj : S.Y ≃ₜ S.Y'), (∀ x, hi x = S.i x) ∧ (∀ y, hj y = S.j y) ∧
      ∀ x, S.f' (hi x) = hj (S.f x) := by
  have _ : IsClosedImmersion S.i := S.sourceThickening.1
  have _ : IsClosedImmersion S.j := S.targetThickening.1
  refine ⟨S.i.isClosedEmbedding.toIsEmbedding.toHomeomorphOfSurjective S.sourceThickening.2,
    S.j.isClosedEmbedding.toIsEmbedding.toHomeomorphOfSurjective S.targetThickening.2,
    fun x ↦ by simp, fun y ↦ by simp, fun x ↦ ?_⟩
  exact congrArg (fun k : S.X ⟶ S.Y' => k x) S.morphism.w.symm

/-- Being a closed immersion is invariant under a cartesian, locally finite type morphism of
thickenings. -/
@[stacks 0BPG "closed_immersion"]
theorem isClosedImmersion_iff (S : CartesianFiniteTypeMorphism.{u}) :
    IsClosedImmersion S.f ↔ IsClosedImmersion S.f' := by
  refine ⟨fun hf ↦ ?_, fun hf' ↦ ?_⟩
  · have _ : IsClosedImmersion S.i := S.sourceThickening.1
    have _ : IsClosedImmersion S.j := S.targetThickening.1
    obtain ⟨hi, hj, -, hj_apply, hcomm⟩ := exists_homeomorph_comm S
    have hqc_f' : QuasiCompact S.f' := by
      refine ⟨fun U hU hUc ↦ ?_⟩
      convert hi.isCompact_image.mpr
        ((inferInstance : QuasiCompact S.f).isCompact_preimage _
          (hj.isOpen_preimage.mpr hU) (hj.isCompact_preimage.mpr hUc)) using 1
      symm
      rw [hi.image_eq_preimage_symm]
      ext x'
      change hj (S.f (hi.symm x')) ∈ U ↔ S.f' x' ∈ U
      rw [← hcomm (hi.symm x'), hi.apply_symm_apply]
    have _ : IsClosedImmersion (pullback.snd S.f' S.j) :=
      (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion (f := S.f)
        (g := pullback.snd S.f' S.j) (Arrow.isoMk S.cartesian.flip.isoPullback (Iso.refl _)
          S.cartesian.flip.isoPullback_hom_snd)).mp hf
    exact isClosedImmersion_of_infinitesimal_baseChange S.f' S.j
      ⟨S.j.isClosedEmbedding.toIsEmbedding.injective, S.targetThickening.2⟩
      (Or.inl ⟨inferInstance, hqc_f'⟩)
  · exact IsClosedImmersion.isStableUnderBaseChange.of_isPullback S.cartesian.flip hf'

/-- Being an immersion is invariant under a cartesian, locally finite type morphism of
thickenings. -/
@[stacks 0BPG "immersion"]
theorem isImmersion_iff (S : CartesianFiniteTypeMorphism.{u}) :
    IsImmersion S.f ↔ IsImmersion S.f' := by
  refine ⟨fun hf ↦ ?_, fun hf' ↦ ?_⟩
  · have _ : IsClosedImmersion S.i := S.sourceThickening.1
    have _ : IsClosedImmersion S.j := S.targetThickening.1
    let V : S.Y.Opens := S.f.coborderRange
    obtain ⟨hi, hj, -, hj_apply, hcomm⟩ := exists_homeomorph_comm S
    let V' : S.Y'.Opens := ⟨hj '' (V : Set S.Y), hj.isOpenMap _ V.2⟩
    have hV : V ≤ S.j ⁻¹ᵁ V' := fun y hy ↦ ⟨y, hy, hj_apply y⟩
    have hfV (x : S.X) : S.f x ∈ V := by
      rw [← S.f.liftCoborder_ι]
      exact (S.f.liftCoborder x).property
    have hVsrc : S.f ⁻¹ᵁ V = ⊤ := top_unique fun x _ ↦ hfV x
    have hf_range : Set.range S.f'.base ⊆ (V' : Set S.Y') := by
      rintro y' ⟨x', rfl⟩
      obtain ⟨x, rfl⟩ := hi.surjective x'
      change S.f' (hi x) ∈ V'
      rw [hcomm x]
      exact ⟨S.f x, hfV x, rfl⟩
    have hf'pre : S.f' ⁻¹ᵁ V' = ⊤ := top_unique fun x _ ↦ hf_range ⟨x, rfl⟩
    let hsrc := hVsrc.symm.le
    let htgt := hf'pre.symm.le
    let c₀ : (⊤ : S.X.Opens).toScheme ⟶ V.toScheme := S.f.resLE V ⊤ hsrc
    let c'₀ : (⊤ : S.X'.Opens).toScheme ⟶ V'.toScheme := S.f'.resLE V' ⊤ htgt
    let i₀ : (⊤ : S.X.Opens).toScheme ⟶ (⊤ : S.X'.Opens).toScheme :=
      S.i.resLE ⊤ ⊤ (by simp)
    let k : V.toScheme ⟶ V'.toScheme := S.j.resLE V' V hV
    have hc₀_eq : c₀ = S.X.topIso.hom ≫ S.f.liftCoborder := by
      apply (cancel_mono V.ι).mp
      rw [Category.assoc, S.f.liftCoborder_ι]
      simp [c₀, Scheme.Hom.resLE_comp_ι]
    have hc₀ : IsClosedImmersion c₀ := by
      rw [hc₀_eq]
      infer_instance
    have hi₀_eq : i₀ = S.X.topIso.hom ≫ S.i ≫ S.X'.topIso.inv := by
      apply (cancel_mono ((⊤ : S.X'.Opens).ι)).mp
      calc
        i₀ ≫ (⊤ : S.X'.Opens).ι = (⊤ : S.X.Opens).ι ≫ S.i :=
          Scheme.Hom.resLE_comp_ι (f := S.i)
            (e := (show (⊤ : S.X.Opens) ≤ S.i ⁻¹ᵁ (⊤ : S.X'.Opens) by simp))
        _ = S.X.topIso.hom ≫ S.i ≫ S.X'.topIso.inv ≫ (⊤ : S.X'.Opens).ι := by simp
    have hcart : IsPullback c₀ i₀ k c'₀ := by
      simpa [c₀, c'₀, i₀, k, V, V', hsrc, htgt] using
        (Scheme.Hom.isPullback_resLE S.cartesian
          (US := V') (UT := ⊤) (UX := V) (UY := ⊤)
          (hUST := htgt) (hUSX := hV) (hUY := by simp [hVsrc]))
    have _ : LocallyOfFiniteType c'₀ := inferInstance
    let R : CartesianFiniteTypeMorphism.{u} :=
      { X := (⊤ : S.X.Opens).toScheme
        X' := (⊤ : S.X'.Opens).toScheme
        Y := V.toScheme
        Y' := V'.toScheme
        i := i₀
        j := k
        morphism := ⟨c₀, c'₀, hcart.w⟩
        sourceThickening := by
          constructor
          · rw [hi₀_eq]
            infer_instance
          · intro y'
            obtain ⟨x, hx⟩ := S.sourceThickening.2 (S.X'.topIso.hom y')
            have hleft : Function.LeftInverse
                (fun z : S.X' => S.X'.topIso.inv z)
                (fun z : (⊤ : S.X'.Opens).toScheme => S.X'.topIso.hom z) := by
              intro z
              change S.X'.topIso.inv (S.X'.topIso.hom z) = z
              exact congrArg
                (fun f : (⊤ : S.X'.Opens).toScheme ⟶ (⊤ : S.X'.Opens).toScheme => f z)
                S.X'.topIso.hom_inv_id
            have hinj : Function.Injective S.X'.topIso.hom := hleft.injective
            refine ⟨S.X.topIso.inv x, ?_⟩
            apply hinj
            rw [hi₀_eq]
            change S.X'.topIso.hom (S.X'.topIso.inv
              (S.i (S.X.topIso.hom (S.X.topIso.inv x)))) = S.X'.topIso.hom y'
            have hX (z : S.X) : S.X.topIso.hom (S.X.topIso.inv z) = z :=
              congrArg (fun f : S.X ⟶ S.X => f z) S.X.topIso.inv_hom_id
            have hX' (z : S.X') : S.X'.topIso.hom (S.X'.topIso.inv z) = z :=
              congrArg (fun f : S.X' ⟶ S.X' => f z) S.X'.topIso.inv_hom_id
            calc
              _ = S.i (S.X.topIso.hom (S.X.topIso.inv x)) := hX' _
              _ = S.i x := by rw [hX]
              _ = S.X'.topIso.hom y' := hx
        targetThickening := by
          constructor
          · have hrange : Set.range V.ι.base = Set.range (pullback.snd V'.ι S.j).base := by
              rw [Scheme.Opens.range_ι, IsOpenImmersion.range_pullbackSnd,
                Scheme.Opens.opensRange_ι]
              ext y
              change y ∈ V ↔ S.j y ∈ V'
              refine ⟨fun hy ↦ ⟨y, hy, hj_apply y⟩, fun hy ↦ ?_⟩
              change S.j y ∈ hj '' (V : Set S.Y) at hy
              obtain ⟨z, hz, hzy⟩ := hy
              simpa [hj.injective (hzy.trans (hj_apply y).symm)] using hz
            let e : V.toScheme ≅ pullback V'.ι S.j :=
              IsOpenImmersion.isoOfRangeEq V.ι (pullback.snd V'.ι S.j) hrange
            have he : e.hom ≫ pullback.snd V'.ι S.j = V.ι :=
              IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
            have hk_eq : k = e.hom ≫ pullback.fst V'.ι S.j := by
              apply (cancel_mono V'.ι).mp
              calc
                k ≫ V'.ι = V.ι ≫ S.j := by simp [k, Scheme.Hom.resLE_comp_ι]
                _ = e.hom ≫ pullback.fst V'.ι S.j ≫ V'.ι := by
                  rw [← he]
                  simp [Category.assoc, pullback.condition]
            have _ : IsClosedImmersion (pullback.fst V'.ι S.j) :=
              (IsClosedImmersion.isStableUnderBaseChange).of_isPullback
                (IsPullback.of_hasPullback V'.ι S.j).flip S.targetThickening.1
            rw [hk_eq]
            infer_instance
          · intro y'
            obtain ⟨y, hy, hEq⟩ := y'.property
            refine ⟨⟨y, hy⟩, ?_⟩
            apply Subtype.ext
            simpa [k, Scheme.Hom.coe_resLE_apply, hj_apply] using hEq
        cartesian := hcart }
    have hc'₀ : IsClosedImmersion c'₀ := (isClosedImmersion_iff R).mp hc₀
    rw [← show S.X'.topIso.inv ≫ c'₀ ≫ V'.ι = S.f' by simp [c'₀, Scheme.Hom.resLE_comp_ι]]
    infer_instance
  · exact IsImmersion.isStableUnderBaseChange.of_isPullback S.cartesian.flip hf'

/-- Properness is invariant under a cartesian, locally finite type morphism of
thickenings. -/
@[stacks 0BPG "proper"]
theorem isProper_iff (S : CartesianFiniteTypeMorphism.{u}) :
    IsProper S.f ↔ IsProper S.f' := by
  simp [AlgebraicGeometry.isProper_iff,
    isSeparated_left_iff_right S.sourceThickening S.targetThickening S.morphism,
    universallyClosed_left_iff_right S.morphism S.sourceThickening S.targetThickening,
    show LocallyOfFiniteType S.f from inferInstance,
    show LocallyOfFiniteType S.f' from inferInstance]

/-- Finiteness is invariant under a cartesian, locally finite type morphism of thickenings: a
morphism of schemes is finite exactly when it is proper and locally quasi-finite, and both of
those are invariant. -/
@[stacks 0BPG "finite"]
theorem isFinite_iff (S : CartesianFiniteTypeMorphism.{u}) :
    IsFinite S.f ↔ IsFinite S.f' := by
  rw [IsFinite.iff_isProper_and_locallyQuasiFinite,
    IsFinite.iff_isProper_and_locallyQuasiFinite, S.isProper_iff,
    locallyQuasiFinite_iff_of_isThickening S.sourceThickening S.targetThickening S.cartesian.flip]

end CartesianFiniteTypeMorphism

end Stacks.Thickenings

end
