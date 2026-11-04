module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDeltaDimension

/-!
# The flat pullback of an integral closed subscheme, coefficientwise

Stacks 02RB has two halves. The first is the construction of flat pullback of cycles; it is
`Stacks.Chow.flatPullback` in `StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback`, where
the coefficient at `x' : X'` is the coefficient of the given cycle at `f x'` times the weight
`Stacks.Chow.flatPullbackWeight`, the multiplicity of `x'` in the scheme-theoretic inverse image
of the reduced closure of `f x'`. The second half is the agreement of that pointwise rule with
the componentwise description: the pullback of the cycle `[Z]_k` of an integral closed subscheme
`i : Z ⟶ X` is the cycle `[X' ×_X Z]_{k+r}` of its scheme-theoretic inverse image.

This file supplies the second half, as three statements about coefficients only. They mention
neither `flatPullback` nor its weight, so they apply to any packaging of the pullback rule, and
they compose to the agreement in a few lines: the cycle of an integral subscheme is the
indicator of the image of its generic point (`cycleAssociatedToClosedSubscheme_isIntegral_apply`);
over that point the weight is the coefficient of the categorical pullback
(`closedSubschemeCycleCoeff_comap_eq_pullbackFst`); and away from it the coefficient of the
categorical pullback vanishes (`closedSubschemeCycleCoeff_pullbackFst_eq_zero`).

The mathematics is in the middle statement. For integral `Z` the ideal sheaf cutting out the
reduced closure of the image of the generic point is the kernel of `i`, so its inverse image
along `f` is the kernel of `pullback.fst f i`; the two closed subschemes of `X'` that these cut
out are therefore isomorphic over `X'`, and multiplicity is invariant under such an isomorphism.
The last statement is where flatness is used: a flat morphism of schemes lifts generalizations,
so every generic point of `X' ×_X Z` lies over the generic point of `Z`, and a point of `X'`
whose image misses that generic point cannot be the image of one.

## Main results

* `Stacks.Chow.cycleAssociatedToClosedSubscheme_isIntegral_apply_genericPoint`,
  `Stacks.Chow.cycleAssociatedToClosedSubscheme_isIntegral_apply_of_ne` — the cycle of an
  integral closed subscheme of delta-dimension `k` is the indicator of the image of its generic
  point.
* `Stacks.Chow.closedSubschemeCycleCoeff_comap_eq_pullbackFst` — over the generic point, the
  inverse-image subscheme and the categorical pullback have the same coefficient.
* `Stacks.Chow.closedSubschemeCycleCoeff_pullbackFst_eq_zero` — off the fibre of the generic
  point, the categorical pullback has coefficient zero.
* `Stacks.Chow.closure_range_eq_closure_generic_image` — the closure of the image of a generic
  point of the source is the closure of the whole image of a continuous map.
* `Stacks.Chow.genericPointsIso`, `Stacks.Chow.componentMultiplicity_eq_of_iso`,
  `Stacks.Chow.closedSubschemeCycleCoeff_eq_of_iso` and
  `Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_of_iso` — an isomorphism of schemes matches
  up generic points, multiplicity is unchanged by precomposing a closed immersion with an
  isomorphism, and the coefficient function and the cycle of a closed subscheme therefore
  depend only on the subscheme and not on the presentation of its closed immersion.

## References

* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Multiplicities of an integral closed subscheme -/

/-- The kernel ideal sheaf of a closed immersion with integral source is radical. -/
private theorem integral_closedImmersion_ker_radical {Y Z : Scheme.{u}}
    (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z] :
    i.ker.radical = i.ker := by
  ext U a
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  refine ⟨fun ha => ?_, fun ha => Ideal.mem_radical_iff.mpr ⟨1, by simp [ha]⟩⟩
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp ha
  have hred : IsReduced Γ(Z, i ⁻¹ᵁ U) := IsReduced.component_reduced (i ⁻¹ᵁ U)
  exact RingHom.mem_ker.mpr ((isReduced_iff _).mp hred _
    ⟨n, by simpa only [map_pow] using RingHom.mem_ker.mp hn⟩)

/-- The closure of the image of a generic point is the closure of the whole image. -/
theorem closure_range_eq_closure_generic_image {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (hf : Continuous f)
    (ξ : X) (hξ : closure ({ξ} : Set X) = Set.univ) :
    closure ({f ξ} : Set Y) = closure (Set.range f) := by
  refine le_antisymm (closure_mono (Set.singleton_subset_iff.mpr ⟨ξ, rfl⟩))
    (closure_minimal ?_ isClosed_closure)
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ closure ({ξ} : Set X) := by simp [hξ]
  simpa only [Set.image_singleton] using image_closure_subset_closure_image hf ⟨z, hz, rfl⟩

/-- For an integral closed subscheme, the ideal sheaf cutting out the reduced closure of the
image of the generic point is the kernel of the closed immersion. -/
private theorem vanishingIdeal_closure_image_generic_eq_ker {Y Z : Scheme.{u}}
    (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z] (ξ : genericPoints Z) :
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({i ξ.1} : Set Y)) = i.ker := by
  have hξeq : ξ.1 = genericPoint Z := by
    simpa [genericPoints_eq_singleton] using ξ.2
  have hξ : closure ({ξ.1} : Set Z) = Set.univ := by
    rw [hξeq]
    exact genericPoint_spec Z
  have hset : (Closeds.closure ({i ξ.1} : Set Y) : Set Y) = (i.ker).support := by
    rw [Scheme.Hom.support_ker]
    exact closure_range_eq_closure_generic_image i i.continuous ξ.1 hξ
  calc
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({i ξ.1} : Set Y)) =
        Scheme.IdealSheafData.vanishingIdeal (i.ker).support := by
          congr 1
          exact SetLike.coe_injective hset
    _ = i.ker.radical := Scheme.IdealSheafData.vanishingIdeal_support
    _ = i.ker := integral_closedImmersion_ker_radical i

/-- An isomorphism of schemes matches up their generic points. -/
noncomputable def genericPointsIso {A B : Scheme.{u}} (e : A ≅ B) :
    genericPoints A ≃ genericPoints B := by
  let h : A ≃ₜ B := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)
  refine ⟨fun x => ⟨e.hom x.1, ?_⟩, fun y => ⟨e.inv y.1, ?_⟩, ?_, ?_⟩
  · change closure ({e.hom x.1} : Set B) ∈ irreducibleComponents B
    have hx : h x.1 = e.hom x.1 := rfl
    rw [← hx, ← Set.image_singleton, ← h.image_closure]
    let W := genericPoints.component x
    have hW : Maximal IsIrreducible (W : Set A) := W.2
    have hW' : Maximal IsIrreducible (h '' (W : Set A)) := by
      rw [maximal_iff]
      refine ⟨?_, ?_⟩
      · exact hW.prop.image h h.continuous.continuousOn
      · intro T hT hsub
        have hpre : IsIrreducible (h.symm '' T) :=
          hT.image h.symm h.symm.continuous.continuousOn
        have hWpre : (W : Set A) ⊆ h.symm '' T := by
          intro z hz
          have hzT : h z ∈ T := hsub ⟨z, hz, rfl⟩
          exact ⟨h z, hzT, h.symm_apply_apply z⟩
        have heq : (W : Set A) = h.symm '' T := (maximal_iff.mp hW).2 hpre hWpre
        calc
          h '' (W : Set A) = h '' (h.symm '' T) := congrArg (fun s => h '' s) heq
          _ = T := by ext z; simp
    exact hW'
  · change closure ({e.inv y.1} : Set A) ∈ irreducibleComponents A
    have hy : h.symm y.1 = e.inv y.1 := rfl
    rw [← hy, ← Set.image_singleton, ← h.symm.image_closure]
    let W := genericPoints.component y
    have hW : Maximal IsIrreducible (W : Set B) := W.2
    have hW' : Maximal IsIrreducible (h.symm '' (W : Set B)) := by
      rw [maximal_iff]
      refine ⟨?_, ?_⟩
      · exact hW.prop.image h.symm h.symm.continuous.continuousOn
      · intro T hT hsub
        have hpre : IsIrreducible (h '' T) := hT.image h h.continuous.continuousOn
        have hWpre : (W : Set B) ⊆ h '' T := by
          intro z hz
          have hzT : h.symm z ∈ T := hsub ⟨z, hz, rfl⟩
          exact ⟨h.symm z, hzT, h.apply_symm_apply z⟩
        have heq : (W : Set B) = h '' T := (maximal_iff.mp hW).2 hpre hWpre
        calc
          h.symm '' (W : Set B) = h.symm '' (h '' T) := congrArg (fun s => h.symm '' s) heq
          _ = T := by ext z; simp
    exact hW'
  · exact fun x => Subtype.ext (by simp)
  · exact fun y => Subtype.ext (by simp)

/-- Multiplicity is unchanged by precomposing a closed immersion with an isomorphism. -/
theorem componentMultiplicity_eq_of_iso {X A B : Scheme.{u}}
    (j : B ⟶ X) [IsClosedImmersion j] (e : A ≅ B) (ξ : genericPoints A) :
    componentMultiplicity (e.hom ≫ j) ξ =
      componentMultiplicity j (genericPointsIso e ξ) := by
  classical
  let η : genericPoints B := ⟨e.hom ξ.1, (genericPointsIso e ξ).2⟩
  let eStalk := (asIso (e.hom.stalkMap ξ.1)).commRingCatIsoToRingEquiv
  let R : Type u := X.presheaf.stalk ((e.hom ≫ j) ξ.1)
  let S : Type u := X.presheaf.stalk (j (e.hom ξ.1))
  let M : Type u := A.presheaf.stalk ξ.1
  let N : Type u := B.presheaf.stalk (e.hom ξ.1)
  let ρM : R →+* M := ((e.hom ≫ j).stalkMap ξ.1).hom
  let ρNj : S →+* N := (j.stalkMap (e.hom ξ.1)).hom
  let eBase : R ≃+* S := RingEquiv.refl R
  let ρN : R →+* N := ρNj.comp eBase.toRingHom
  let _ : Algebra R S := eBase.toRingHom.toAlgebra
  let _ : Module S N := Module.compHom N ρNj
  let _ : Module R N := Module.compHom N ρN
  let _ : IsScalarTower R S N := by
    constructor
    intro a b n
    show ρNj (eBase.toRingHom a * b) * n =
      ρNj (eBase.toRingHom a) * (ρNj b * n)
    rw [map_mul]
    simp [mul_assoc]
  have hmap (a : R) : ρM a = eStalk.toRingHom (ρN a) := by
    dsimp [ρM, ρN, ρNj, eBase, eStalk]
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  let _ : Module R M := Module.compHom M ρM
  let eM : M ≃ₗ[R] N :=
    { toFun := eStalk.symm
      invFun := eStalk
      left_inv := eStalk.apply_symm_apply
      right_inv := eStalk.symm_apply_apply
      map_add' := eStalk.symm.map_add
      map_smul' := by
        intro r n
        show eStalk.symm (ρM r * n) = ρN r * eStalk.symm n
        rw [hmap r]
        show eStalk.symm (eStalk.toRingHom (ρN r) * n) =
          ρN r * eStalk.symm n
        simp }
  have hlen : Module.length R M = Module.length R N := eM.length_eq
  have hlenBase : Module.length R N = Module.length S N :=
    Module.length_eq_of_surjective (S := R) (R := S) (M := N) eBase.surjective
  show componentMultiplicity (e.hom ≫ j) ξ = componentMultiplicity j η
  unfold componentMultiplicity
  dsimp only [η]
  simpa [R, S, M, N, ρM, ρNj, eBase, ρN] using
    congrArg ENat.toNat (hlen.trans hlenBase)

/-- The coefficient function of a closed subscheme depends only on the subscheme, not on the
presentation of the closed immersion. -/
theorem closedSubschemeCycleCoeff_eq_of_iso
    (C : ChowSituation.{u}) {X A B : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (jA : A ⟶ X) [IsClosedImmersion jA]
    (jB : B ⟶ X) [IsClosedImmersion jB]
    (e : A ≅ B) (hcomp : e.hom ≫ jB = jA) (k : ℤ) (x : X) :
    closedSubschemeCycleCoeff C sX jA k x = closedSubschemeCycleCoeff C sX jB k x := by
  classical
  unfold closedSubschemeCycleCoeff
  by_cases hA : ∃ ξ : genericPoints A,
      jA ξ.1 = x ∧ relativeDimension C.dimensionFunction sX x = k
  · let ξA : genericPoints A := Classical.choose hA
    have hspecA := Classical.choose_spec hA
    let ξB : genericPoints B := genericPointsIso e ξA
    have heval : jB (e.hom ξA.1) = jA ξA.1 := by
      simpa only [Scheme.Hom.comp_apply] using congrArg (fun q : A ⟶ X => q ξA.1) hcomp
    have hpt : jB ξB.1 = x := heval.trans hspecA.1
    have hB : ∃ ξ : genericPoints B,
        jB ξ.1 = x ∧ relativeDimension C.dimensionFunction sX x = k :=
      ⟨ξB, hpt, hspecA.2⟩
    have hchooseA : Classical.choose hA = ξA := rfl
    have hchooseB : Classical.choose hB = ξB :=
      Subtype.ext (jB.isClosedEmbedding.injective ((Classical.choose_spec hB).1.trans hpt.symm))
    rw [dite_eq_left hA, dite_eq_left hB, hchooseA, hchooseB]
    simpa [ξB, ← hcomp] using componentMultiplicity_eq_of_iso jB e ξA
  · have hB : ¬ ∃ ξ : genericPoints B,
        jB ξ.1 = x ∧ relativeDimension C.dimensionFunction sX x = k := by
      rintro ⟨ξB, hξB, hdim⟩
      have hmap : e.hom (e.inv ξB.1) = ξB.1 :=
        congrArg (fun q : B ⟶ B => q ξB.1) e.inv_hom_id
      have heval : jB (e.hom (e.inv ξB.1)) = jA (e.inv ξB.1) := by
        simpa only [Scheme.Hom.comp_apply] using
          congrArg (fun q : A ⟶ X => q (e.inv ξB.1)) hcomp
      exact hA ⟨⟨e.inv ξB.1, (genericPointsIso e.symm ξB).2⟩,
        heval.symm.trans (by rwa [hmap]), hdim⟩
    rw [dite_eq_right hA, dite_eq_right hB]

/-- The cycle of a closed subscheme depends only on the closed subscheme, not on the
presentation of its closed immersion: this is the cycle-level form of
`Stacks.Chow.closedSubschemeCycleCoeff_eq_of_iso`. -/
theorem cycleAssociatedToClosedSubscheme_eq_of_iso (C : ChowSituation.{u}) {X A B : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (jA : A ⟶ X) [IsClosedImmersion jA]
    (jB : B ⟶ X) [IsClosedImmersion jB] (e : A ≅ B) (hcomp : e.hom ≫ jB = jA) (k : ℤ) :
    cycleAssociatedToClosedSubscheme C sX jA k = cycleAssociatedToClosedSubscheme C sX jB k :=
  Subtype.ext (Function.locallyFinsuppWithin.ext
    (closedSubschemeCycleCoeff_eq_of_iso C sX jA jB e hcomp k))

/-! ### Generic points under a flat morphism -/

/-- A flat morphism of schemes lifts generalizations: flatness gives going down on each affine
piece, and going down is exactly the lifting of generalizations on prime spectra. -/
private lemma flat_generalizingMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    GeneralizingMap f := by
  have := HasRingHomProperty.of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget.{u}
    (topologically GeneralizingMap)
  show topologically GeneralizingMap f
  rw [HasRingHomProperty.iff_appLE (P := topologically GeneralizingMap)]
  intro U V e
  algebraize [(f.appLE U V e).hom]
  apply Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp
  convert! Algebra.HasGoingDown.of_flat
  exact HasRingHomProperty.appLE @Flat f ‹_› U V e

/-- Every generic point of the pullback of a flat morphism along a morphism with irreducible
source lies over the generic point of that source. -/
private lemma snd_genericPoint_pullback_eq
    {X Y Z : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
    (i : Z ⟶ Y) [IrreducibleSpace Z]
    (ξ : genericPoints (pullback f i : Scheme.{u})) :
    (pullback.snd f i) ξ.1 = genericPoint Z := by
  let P := pullback f i
  let p : P ⟶ Z := pullback.snd f i
  let W := genericPoints.component ξ
  have hξ : ξ.1 = W.2.1.genericPoint := (genericPoints.isGenericPoint ξ).eq
    (W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents (W : Set P) W.2))
  have : Flat p :=
    (Flat.isStableUnderBaseChange).of_isPullback
      (IsPullback.of_hasPullback f i) inferInstance
  obtain ⟨V, hV⟩ := component_genericPoint_maps_to_component_genericPoint p W
  have hVU : (V : Set Z) = Set.univ :=
    Set.eq_univ_of_univ_subset (V.2.2 (IrreducibleSpace.isIrreducible_univ Z) (Set.subset_univ _))
  have hη : IsGenericPoint (genericPoints.ofComponent V : Z) (Set.univ : Set Z) := by
    simpa only [hVU] using (genericPoints.isGenericPoint_ofComponent V)
  rw [hξ, hV]
  exact hη.eq (genericPoint_spec Z)

/-! ### The three coefficient statements -/

/-- The cycle of an integral closed subscheme `i : Z ⟶ Y` of delta-dimension `k` has
coefficient one at the image of the generic point of `Z`. -/
theorem cycleAssociatedToClosedSubscheme_isIntegral_apply_genericPoint (C : ChowSituation.{u})
    {Y Z : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z] (k : ℤ)
    (hdim : relativeDimension C.dimensionFunction sY (i (genericPoint Z)) = k) :
    (cycleAssociatedToClosedSubscheme C sY i k).1 (i (genericPoint Z)) = 1 := by
  let η : genericPoints Z := ⟨genericPoint Z, by simp [genericPoints_eq_singleton]⟩
  rw [cycleAssociatedToClosedSubscheme_apply C sY i k η hdim,
    componentMultiplicity_eq_one_of_reduced i η]

/-- The cycle of an integral closed subscheme `i : Z ⟶ Y` has coefficient zero at every point
other than the image of the generic point of `Z`: that image is the only generic point. -/
theorem cycleAssociatedToClosedSubscheme_isIntegral_apply_of_ne (C : ChowSituation.{u})
    {Y Z : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z] (k : ℤ) {y : Y}
    (hy : y ≠ i (genericPoint Z)) :
    (cycleAssociatedToClosedSubscheme C sY i k).1 y = 0 := by
  refine cycleAssociatedToClosedSubscheme_apply_eq_zero C sY i k y ?_
  rintro ⟨ξ, hξ, _⟩
  have hξη : ξ.1 = genericPoint Z := by simpa [genericPoints_eq_singleton] using ξ.2
  exact hy (by simpa [hξη] using hξ.symm)

/-- Over the generic point of an integral closed subscheme `i : Z ⟶ X`, the scheme-theoretic
inverse image along `f` of the reduced closure of that point has the same coefficient as the
categorical pullback `X' ×_X Z`: the two cut out isomorphic closed subschemes of `X'`. -/
theorem closedSubschemeCycleCoeff_comap_eq_pullbackFst (C : ChowSituation.{u})
    {X' X Z : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX']
    (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (j : ℤ) (x : X') (hx : f x = i (genericPoint Z)) :
    closedSubschemeCycleCoeff C sX'
        (((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({f x} : Set X))).comap f).subschemeι) j x =
      closedSubschemeCycleCoeff C sX' (pullback.fst f i) j x := by
  classical
  let η : genericPoints Z := ⟨genericPoint Z, by simp [genericPoints_eq_singleton]⟩
  let p := pullback.fst f i
  let I : Scheme.IdealSheafData X :=
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({f x} : Set X))
  have hI : I = i.ker := by
    dsimp [I]
    rw [hx]
    exact vanishingIdeal_closure_image_generic_eq_ker i η
  have hJ : I.comap f = p.ker := by
    rw [hI]
    exact (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i f).symm
  have hker : p.ker = (I.comap f).subschemeι.ker := by
    rw [← hJ, Scheme.IdealSheafData.ker_subschemeι]
  let eHom := IsClosedImmersion.lift p (I.comap f).subschemeι hker.le
  have : IsIso eHom := IsClosedImmersion.isIso_lift p _ hker
  exact closedSubschemeCycleCoeff_eq_of_iso C sX' (I.comap f).subschemeι p (asIso eHom)
    (by simp [eHom]) j x

/-- Away from the fibre over the generic point of an integral closed subscheme `i : Z ⟶ X`, the
categorical pullback `X' ×_X Z` contributes no coefficient. Flatness of `f` is what forces every
generic point of the pullback to lie over the generic point of `Z`. -/
theorem closedSubschemeCycleCoeff_pullbackFst_eq_zero (C : ChowSituation.{u})
    {X' X Z : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX']
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (j : ℤ) (x : X') (hx : f x ≠ i (genericPoint Z)) :
    closedSubschemeCycleCoeff C sX' (pullback.fst f i) j x = 0 := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  unfold closedSubschemeCycleCoeff
  apply dite_eq_right
  rintro ⟨ξ, rfl, _⟩
  apply hx
  rw [← snd_genericPoint_pullback_eq f i ξ]
  simpa only [Scheme.Hom.comp_apply] using
    congrArg (fun q : (pullback f i : Scheme) ⟶ X => q ξ.1) pullback.condition

end Stacks.Chow

end
