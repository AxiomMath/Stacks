module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import StacksFrontier.Homology.KFlat.BifunctorLocalization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatRepresentative

/-!
# The lowest cokernel of a bounded above flat complex of Tor amplitude in `[a, b]`

Let `E` be a bounded above complex of flat `O_X`-modules on a ringed space whose
derived-category image has Tor amplitude in `[a, b]`. Then the cokernel of the differential
`E^{a-1} ⟶ E^a` is a flat `O_X`-module. This is the step which, applied to a flat
resolution, produces the *bounded* flat representative of an object of Tor amplitude in
`[a, b]`.

## Main results

* `Stacks.Cohomology.TorAmplitude.FlatCokernel.isFlat_cokernel_of_hasTorAmplitude`: the
  cokernel of `d^{a-1}` is flat.
* `Stacks.Cohomology.TorAmplitude.FlatCokernel.exactAt_rowComplex_of_hasTorAmplitude`: below
  `a` the termwise tensor complex `p ↦ E^p ⊗_{O_X} F` is exact, for every `O_X`-module `F`.
* `Stacks.Cohomology.TorAmplitude.FlatCokernel.preservesMonomorphisms_tensor_cokernel`: in any
  abelian category, if `S ⊗ M` is exact for every `M` then `Coker(S.g) ⊗ -` preserves
  monomorphisms. Stated for an arbitrary abelian category and bifunctor, so that the same
  argument serves the ringed-site analogue.
* `Stacks.Cohomology.TorAmplitude.FlatCokernel.mono_cokernel_map_of_exact`: the diagram chase
  behind it, likewise for an arbitrary abelian category.

## Implementation notes

The identification of `Tot(E ⊗_{O_X} F[0])` with the termwise complex `p ↦ E^p ⊗_{O_X} F` is
`CochainComplex.KFlatBifunctor.totalSingleIso`, and the termwise complex itself is
`CochainComplex.KFlatBifunctor.rowComplex`.

Flatness is exactness of tensoring on the *right*, while the functors above tensor on the
left; the two are exchanged by the braiding `Stacks.SheafOfModules.Tensor.sheafTensorBraiding`.

The universes of the space, its structure sheaf and its modules coincide, as they already
must for `Stacks.Cohomology.TorAmplitude.HasTorAmplitude`; the derived category's own hom
universe stays independent.

## References

* [Stacks Project, Tag 08CH](https://stacks.math.columbia.edu/tag/08CH)
* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

namespace Stacks.Cohomology.TorAmplitude.FlatCokernel

universe u d

section Abstract

variable {C : Type*} [Category C] [Abelian C]

/-- **A diagram chase for the induced map on the right-hand cokernels of a three-row
diagram.** Given short complexes `S₁ ⟶ S₂ ⟶ S₃` whose composite is zero, with the middle
column exact, `S₃` exact, `g.τ₁` epi and `f.τ₃` mono, a map `φ` between cokernels of the
second differentials compatible with `f.τ₃` is a monomorphism. -/
lemma mono_cokernel_map_of_exact
    {S₁ S₂ S₃ : ShortComplex C} (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃)
    (hfg : f ≫ g = 0)
    (h₂ : (ShortComplex.mk f.τ₂ g.τ₂
      (by simpa using congrArg ShortComplex.Hom.τ₂ hfg)).Exact)
    (h₃ : S₃.Exact) [Epi g.τ₁] [Mono f.τ₃]
    {Q₁ Q₂ : C} (q₁ : S₁.X₃ ⟶ Q₁) (q₂ : S₂.X₃ ⟶ Q₂)
    (w₁ : S₁.g ≫ q₁ = 0) (w₂ : S₂.g ≫ q₂ = 0)
    [Epi q₁] (hq₂ : (ShortComplex.mk S₂.g q₂ w₂).Exact)
    (φ : Q₁ ⟶ Q₂) (hφ : q₁ ≫ φ = f.τ₃ ≫ q₂) : Mono φ := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro A z hz
  obtain ⟨A₁, π₁, hπ₁, x, hx⟩ := surjective_up_to_refinements_of_epi q₁ z
  have hxf : (x ≫ f.τ₃) ≫ q₂ = 0 := by
    rw [Category.assoc, ← hφ, ← Category.assoc, ← hx, Category.assoc, hz,
      Limits.comp_zero]
  obtain ⟨A₂, π₂, hπ₂, y, hy⟩ := hq₂.exact_up_to_refinements (x ≫ f.τ₃) hxf
  have hyg : (y ≫ g.τ₂) ≫ S₃.g = 0 := by
    rw [Category.assoc, g.comm₂₃, ← Category.assoc, ← hy]
    have hf₃ : f.τ₃ ≫ g.τ₃ = 0 := by
      simpa using congrArg ShortComplex.Hom.τ₃ hfg
    simp only [Category.assoc, hf₃, Limits.comp_zero]
  obtain ⟨A₃, π₃, hπ₃, t, ht⟩ := h₃.exact_up_to_refinements (y ≫ g.τ₂) hyg
  obtain ⟨A₄, π₄, hπ₄, s, hs⟩ := surjective_up_to_refinements_of_epi g.τ₁ t
  have hv : (π₄ ≫ π₃ ≫ y - s ≫ S₂.f) ≫ g.τ₂ = 0 := by
    rw [Preadditive.sub_comp]
    have hh : (π₄ ≫ π₃ ≫ y) ≫ g.τ₂ = (s ≫ S₂.f) ≫ g.τ₂ := by
      calc
        _ = π₄ ≫ (π₃ ≫ (y ≫ g.τ₂)) := by simp only [Category.assoc]
        _ = π₄ ≫ (t ≫ S₃.f) := by rw [ht]
        _ = (s ≫ S₂.f) ≫ g.τ₂ := by
          rw [← Category.assoc, hs]
          simp only [Category.assoc, g.comm₁₂]
    rw [hh, sub_self]
  obtain ⟨A₅, π₅, hπ₅, v, hv⟩ := h₂.exact_up_to_refinements _ hv
  have heq : π₅ ≫ π₄ ≫ π₃ ≫ π₂ ≫ x = v ≫ S₁.g := by
    apply (cancel_mono f.τ₃).1
    calc
      _ = π₅ ≫ π₄ ≫ π₃ ≫ y ≫ S₂.g := by
        simp only [Category.assoc]
        rw [← hy]
      _ = (π₅ ≫ (π₄ ≫ π₃ ≫ y - s ≫ S₂.f)) ≫ S₂.g := by
        simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
          S₂.zero, Limits.comp_zero, sub_zero]
      _ = (v ≫ f.τ₂) ≫ S₂.g := by rw [hv]
      _ = _ := by simp only [Category.assoc, f.comm₂₃]
  apply (cancel_epi (π₅ ≫ π₄ ≫ π₃ ≫ π₂ ≫ π₁)).1
  simp only [Limits.comp_zero, Category.assoc, hx]
  simpa only [Category.assoc, w₁, Limits.comp_zero] using
    congrArg (fun k => k ≫ q₁) heq

/-- **Tensoring with the cokernel of a universally exact three-term complex preserves
monomorphisms.** If `S` is a short complex such that `S ⊗ M` is exact for every `M`, then
`Coker(S.g) ⊗ -` preserves monomorphisms. -/
lemma preservesMonomorphisms_tensor_cokernel
    (T : C ⥤ C ⥤ C) [T.Additive] [∀ M, (T.obj M).Additive]
    [∀ M, (T.flip.obj M).Additive]
    [∀ M, PreservesFiniteColimits (T.obj M)]
    [∀ M, PreservesFiniteColimits (T.flip.obj M)]
    (S : ShortComplex C)
    [PreservesFiniteLimits (T.obj S.X₂)]
    [PreservesFiniteLimits (T.obj S.X₃)]
    (hS : ∀ M, (S.map (T.flip.obj M)).Exact) :
    (T.obj (cokernel S.g)).PreservesMonomorphisms where
  preserves {M N} f hf := by
    let _ := hf
    have hP := ShortComplex.exact_cokernel f
    let α := S.mapNatTrans (T.flip.map f)
    let β := S.mapNatTrans (T.flip.map (cokernel.π f))
    have hαβ : α ≫ β = 0 := by
      ext <;> simp [α, β, ← Functor.map_comp]
    have h₂ : (ShortComplex.mk α.τ₂ β.τ₂
        (by simpa using congrArg ShortComplex.Hom.τ₂ hαβ)).Exact :=
      hP.map (T.obj S.X₂)
    have hβ : Epi β.τ₁ := inferInstanceAs (Epi ((T.obj S.X₁).map (cokernel.π f)))
    have hα : Mono α.τ₃ := inferInstanceAs (Mono ((T.obj S.X₃).map f))
    have hQ := ShortComplex.exact_cokernel S.g
    exact mono_cokernel_map_of_exact α β hαβ h₂ (hS (cokernel f))
      ((T.flip.obj M).map (cokernel.π S.g))
      ((T.flip.obj N).map (cokernel.π S.g))
      (by simp [← NatTrans.comp_app, ← Functor.map_comp])
      (by simp [← NatTrans.comp_app, ← Functor.map_comp])
      (hQ.map_of_epi_of_preservesCokernel (T.flip.obj N) inferInstance inferInstance)
      ((T.obj (cokernel S.g)).map f)
      ((T.map (cokernel.π S.g)).naturality f).symm

end Abstract

section RingedSpace

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u} X)]

-- `HasDerivedCategory` at the spelling of Stacks 06YU: the type is `OXMod X` by `rfl`, but
-- `structureSheafOfRings` is not reducible, so an instance proved at one spelling does not fire
-- at the other.
attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-- **A complex of Tor amplitude in `[a, b]` with K-flat underlying complex has exact
termwise tensor products below `a`.** For every `O_X`-module `F` the termwise complex
`p ↦ K^p ⊗_{O_X} F` is exact in degrees `i < a`. -/
theorem exactAt_rowComplex_of_hasTorAmplitude
    (K : CochainComplex (Modules X) ℤ) (a b i : ℤ)
    (hKflat : KFlat X K)
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X (DerivedCategory.Q.obj K) a b)
    (F : Modules X) (hi : i < a) :
    (CochainComplex.KFlatBifunctor.rowComplex
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) K F).ExactAt i := by
  let F₀ := (HomologicalComplex.single (Modules X) (ComplexShape.up ℤ) 0).obj F
  let L := ((Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} X.sheaf).obj K).obj F₀
  have hExact : L.ExactAt i := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have hzero := hamp F i (by rw [Set.mem_Icc]; omega)
    have e : L.homology i ≅
        (DerivedCategory.homologyFunctor (Modules X) i).obj
          (((Stacks.Cohomology.TorAmplitude.derTensor X).tensor.obj
            (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj F₀)) :=
      ((DerivedCategory.homologyFunctorFactors
          (Modules X) i).app L).symm ≪≫
        (DerivedCategory.homologyFunctor
            (Modules X) i).mapIso
          ((Stacks.Cohomology.TorAmplitude.derTensor X).comparisonLeft K F₀ hKflat).symm
    exact hzero.of_iso e
  exact hExact.of_iso
    (CochainComplex.KFlatBifunctor.totalSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) K F)

/-- **Tag 08CH.** The cokernel of the differential into the lowest degree of the Tor-amplitude
interval of a bounded above complex of flat `O_X`-modules is a flat `O_X`-module.

The complex is K-flat by Tag 06YQ, so the Tor-amplitude hypothesis makes the three-term
complex `K^{a-2} ⊗ F ⟶ K^{a-1} ⊗ F ⟶ K^a ⊗ F` exact for every `O_X`-module `F`. Hence
`Coker(d^{a-1}) ⊗ -` preserves monomorphisms, and being right exact as well it is exact. -/
@[stacks 08CH]
theorem isFlat_cokernel_of_hasTorAmplitude
    (K : CochainComplex (Modules X) ℤ) (a b : ℤ)
    (hbound : ∃ n : ℤ, K.IsStrictlyLE n)
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (K.X i))
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X (DerivedCategory.Q.obj K) a b) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      (cokernel (K.d (a - 1) a)) := by
  have hKflat := kFlat_of_boundedAbove_of_flat X K hbound hflat
  let T : Modules X ⥤ Modules X ⥤ Modules X :=
    Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf
  let S := K.sc' (a - 2) (a - 1) a
  let _ : ∀ M, PreservesFiniteColimits (T.obj M) :=
    Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj X.sheaf
  let _ : ∀ M, PreservesFiniteColimits (T.flip.obj M) :=
    Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorFlipObj X.sheaf
  let _ : PreservesFiniteLimits (T.obj S.X₂) :=
    (Stacks.SheafOfModules.exact_sheafTensorObj_of_isFlat X.sheaf (hflat (a - 1))).1
  let _ : PreservesFiniteLimits (T.obj S.X₃) :=
    (Stacks.SheafOfModules.exact_sheafTensorObj_of_isFlat X.sheaf (hflat a)).1
  have hS (M : Modules X) : (S.map (T.flip.obj M)).Exact :=
    (HomologicalComplex.exactAt_iff' _ (a - 2) (a - 1) a
      ((ComplexShape.up ℤ).prev_eq' (show a - 2 + 1 = a - 1 by omega))
      ((ComplexShape.up ℤ).next_eq' (show a - 1 + 1 = a by omega))).1
      (exactAt_rowComplex_of_hasTorAmplitude K a b (a - 1) hKflat hamp M (by omega))
  let _ := preservesMonomorphisms_tensor_cokernel T S hS
  let _ := Functor.preservesHomology_of_preservesMonos_and_cokernels (T.obj (cokernel S.g))
  let _ : ∀ {M N : Modules X} (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) (T.obj (cokernel S.g)) :=
    fun f => Functor.PreservesHomology.preservesKernel _ f
  have h : exactFunctor _ _ (T.obj (cokernel S.g)) := by
    rw [exactFunctor_iff]
    exact ⟨Functor.preservesFiniteLimits_of_preservesKernels _, inferInstance⟩
  exact Stacks.SheafOfModules.isFlat_of_exactFunctor_sheafTensorFlip X.sheaf _
    ((exactFunctor _ _).prop_of_iso
      ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.sheaf).app (cokernel S.g)) h)

end RingedSpace

end Stacks.Cohomology.TorAmplitude.FlatCokernel

end
