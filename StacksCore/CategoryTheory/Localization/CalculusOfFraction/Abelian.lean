module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Fractions
public import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Localizations of abelian categories are abelian

If `L : C ⥤ D` is a localization functor for a morphism property `W` which has a left calculus
of fractions, then `L` preserves epimorphisms and cokernels, and `D` has cokernels as soon as
`C` does. Dually, if `W` has a right calculus of fractions, then `L` preserves monomorphisms
and kernels, and `D` has kernels; these are deduced from the left-handed statements applied to
the opposite categories. Finally, if `C` is abelian and `W` has both calculi of fractions,
then `D` is abelian and `L` is exact. This is
[Stacks, Tag 05QG](https://stacks.math.columbia.edu/tag/05QG), following the strategy of the
Stacks project: the abelian structure is obtained from the coimage-image comparison, which `L`
transports from `C` since it preserves kernels and cokernels.
-/

@[expose] public section

namespace CategoryTheory.Localization

open Limits MorphismProperty ZeroObject

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (W : MorphismProperty C)
  [L.IsLocalization W]

section Left

variable [W.HasLeftCalculusOfFractions]

include W in
/-- A localization functor for a morphism property with left calculus of fractions preserves
epimorphisms: writing two morphisms out of `L.obj Y` as left fractions with a common
denominator, an equalizing epimorphism can be cancelled in `C` after clearing denominators. -/
theorem preservesEpimorphisms : L.PreservesEpimorphisms where
  preserves {X Y} p hp := ⟨fun {T} u₁ u₂ h ↦ by
    have := Localization.essSurj L W
    rw [← cancel_mono (L.objObjPreimageIso T).inv]
    obtain ⟨φ, hφ₁, hφ₂⟩ := Localization.exists_leftFraction₂ L W
      (u₁ ≫ (L.objObjPreimageIso T).inv) (u₂ ≫ (L.objObjPreimageIso T).inv)
    have h' : L.map (p ≫ φ.fst.f) = L.map (p ≫ φ.snd.f) := by
      convert congrFun (congrArg CategoryStruct.comp h) (L.objObjPreimageIso T).inv =≫ L.map φ.s
      <;> simp [LeftFraction.map_comp_map_s φ.fst L (Localization.inverts L W), hφ₁,
        LeftFraction.map_comp_map_s φ.snd L (Localization.inverts L W), hφ₂]
    obtain ⟨Z', t, ht, fac⟩ := (MorphismProperty.map_eq_iff_postcomp L W _ _).1 h'
    rw [hφ₁, hφ₂, LeftFraction.map_eq, LeftFraction.map_eq]
    congr 1
    refine W.map_eq_iff_postcomp L _ _|>.2 ⟨Z', t, ht, ?_⟩
    rwa [Category.assoc, Category.assoc, cancel_epi] at fac⟩

section

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [L.PreservesZeroMorphisms]

include W in
/-- Any morphism out of `L.obj Y` annihilating `L.map f` factors through `L` of the cokernel
of `f`, when `W` has a left calculus of fractions. -/
lemma exists_desc_of_map_comp_eq_zero {X Y : C} (f : X ⟶ Y) [HasCokernel f] :
    ∀ (T : D) (z : L.obj Y ⟶ T), L.map f ≫ z = 0 →
      ∃ l : L.obj (cokernel f) ⟶ T, L.map (cokernel.π f) ≫ l = z := by
  have := Localization.essSurj L W
  intro T w hw
  wlog hw' : ∃ (Z : C) (hZ : L.obj Z = T) (z : Y ⟶ Z), w = L.map z ≫ eqToHom hZ generalizing T
  · obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L W (w ≫ (L.objObjPreimageIso T).inv)
    rw [← cancel_mono (L.map φ.s), Category.assoc,
      MorphismProperty.LeftFraction.map_comp_map_s] at hφ
    obtain ⟨l, hl⟩ := this _ (L.map φ.f) (by rw [← hφ, reassoc_of% hw, zero_comp]) ⟨_, rfl, by simp⟩
    exact ⟨l ≫ inv (L.map φ.s) ≫ (L.objObjPreimageIso T).hom, by simp [reassoc_of% hl, ← hφ]⟩
  obtain ⟨Z, rfl, z, rfl⟩ := hw'
  simp only [eqToHom_refl, Category.comp_id, ← L.map_comp] at hw
  obtain ⟨Z', t, ht, fac⟩ := (MorphismProperty.map_eq_iff_postcomp L W (f ≫ z) 0).1
    (by rw [hw, L.map_zero])
  rw [Category.assoc, zero_comp] at fac
  have := Localization.inverts L W t ht
  exact ⟨L.map (cokernel.desc _ _ fac) ≫ inv (L.map t), by simp [← L.map_comp_assoc]⟩

include W in
/-- A zero-morphism-preserving localization functor for a morphism property with left calculus
of fractions preserves cokernels. -/
@[stacks 05QG "part (1) for a morphism of `C`"]
theorem preservesCokernel {X Y : C} (f : X ⟶ Y) [HasCokernel f] :
    PreservesColimit (parallelPair f 0) L :=
  have := preservesEpimorphisms L W
  have : Epi (L.map (cokernel.π f)) := L.map_epi _
  preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
    ((CokernelCofork.isColimitMapCoconeEquiv _ L).2
      (Cofork.IsColimit.ofExistsUnique
        (fun s ↦ existsUnique_of_exists_of_unique
          (exists_desc_of_map_comp_eq_zero L W f _ _ (CokernelCofork.condition s))
          (fun _ _ h₁ h₂ ↦ (cancel_epi (L.map (cokernel.π f))).1 (h₁.trans h₂.symm)))))

include L W in
/-- If `C` has cokernels and `L : C ⥤ D` is a zero-morphism-preserving localization functor
for a morphism property with left calculus of fractions, then `D` has cokernels. -/
@[stacks 05QG "part (1)"]
theorem hasCokernels [HasCokernels C] : HasCokernels D where
  has_colimit f := by
    obtain ⟨g, ⟨e⟩⟩ := (Localization.essSurj_mapArrow L W).mem_essImage (Arrow.mk f)
    have := preservesCokernel L W g.hom
    have : HasColimit (parallelPair (L.map g.hom) 0) :=
      ⟨_, (CokernelCofork.isColimitMapCoconeEquiv _ L).1
        (isColimitOfPreserves L (cokernelIsCokernel g.hom))⟩
    exact hasColimit_of_iso
      ((parallelPair.ext (Arrow.leftFunc.mapIso e.symm) (Arrow.rightFunc.mapIso e.symm)
        (show f ≫ e.inv.right = e.inv.left ≫ L.map g.hom from (Arrow.w_mk e.inv).symm)
        (show (0 : _ ⟶ _) ≫ e.inv.right = e.inv.left ≫ 0 by simp) :
          parallelPair f 0 ≅ parallelPair (L.map g.hom) 0))

end

end Left

section Right

variable [W.HasRightCalculusOfFractions]

include W in
/-- A localization functor for a morphism property with right calculus of fractions preserves
monomorphisms. This is deduced from `Localization.preservesEpimorphisms` by passing to the
opposite categories. -/
theorem preservesMonomorphisms : L.PreservesMonomorphisms where
  preserves {_ _} f hf :=
    have := preservesEpimorphisms L.op W.op
    have : Epi f.op := (op_epi_iff f).2 hf
    (op_epi_iff (L.map f)).1 (by
      rw [← f.unop_op, ← L.op_map]
      exact Functor.PreservesEpimorphisms.preserves f.op)

section

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [L.PreservesZeroMorphisms]

include W in
/-- Any morphism into `L.obj X` annihilated by `L.map f` factors through `L` of the kernel of
`f`, when `W` has a right calculus of fractions. This is deduced from
`Localization.exists_desc_of_map_comp_eq_zero` by passing to the opposite categories. -/
lemma exists_lift_of_comp_map_eq_zero {X Y : C} (f : X ⟶ Y) [HasKernel f] :
    ∀ (T : D) (z : T ⟶ L.obj X), z ≫ L.map f = 0 →
      ∃ l : T ⟶ L.obj (kernel f), l ≫ L.map (kernel.ι f) = z := by
  intro T z hz
  let t : ColimitCocone (parallelPair f.op 0) :=
    ⟨_, KernelFork.IsLimit.ofιOp (kernel.ι f) (kernel.condition f) (kernelIsKernel f)⟩
  have : HasCokernel f.op := HasColimit.mk t
  have : L.op.PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by rw [Functor.op_map, unop_zero, L.map_zero, op_zero]⟩
  obtain ⟨l', hl'⟩ := exists_desc_of_map_comp_eq_zero L.op W.op f.op (Opposite.op T) z.op
    (Quiver.Hom.unop_inj (by simpa using hz))
  let e : cokernel f.op ≅ Opposite.op (kernel f) := colimit.isoColimitCocone t
  have he : cokernel.π f.op ≫ e.hom = (kernel.ι f).op :=
    colimit.isoColimitCocone_ι_hom t WalkingParallelPair.one
  have h₂ : L.op.map ((kernel.ι f).op) ≫ L.op.map e.inv ≫ l' = z.op := by
    rw [← he, L.op.map_comp, Category.assoc, ← L.op.map_comp_assoc e.hom e.inv,
      e.hom_inv_id, L.op.map_id, Category.id_comp, hl']
  refine ⟨(L.op.map e.inv ≫ l').unop, ?_⟩
  simpa using congrArg Quiver.Hom.unop h₂

include W in
/-- A zero-morphism-preserving localization functor for a morphism property with right
calculus of fractions preserves kernels. -/
@[stacks 05QG "part (2) for a morphism of `C`"]
lemma preservesKernel {X Y : C} (f : X ⟶ Y) [HasKernel f] :
    PreservesLimit (parallelPair f 0) L :=
  have := preservesMonomorphisms L W
  have : Mono (L.map (kernel.ι f)) := L.map_mono _
  preservesLimit_of_preserves_limit_cone (kernelIsKernel f) ((KernelFork.isLimitMapConeEquiv _ L).2
    (Fork.IsLimit.ofExistsUnique (fun s ↦ existsUnique_of_exists_of_unique
      (exists_lift_of_comp_map_eq_zero L W f _ _ (KernelFork.condition s))
      (fun _ _ h₁ h₂ ↦ (cancel_mono (L.map (kernel.ι f))).1 (h₁.trans h₂.symm)))))

include L W in
/-- If `C` has kernels and `L : C ⥤ D` is a zero-morphism-preserving localization functor for
a morphism property with right calculus of fractions, then `D` has kernels. -/
@[stacks 05QG "part (2)"]
theorem hasKernels [HasKernels C] : HasKernels D where
  has_limit f :=
    have ⟨g, ⟨e⟩⟩ := (essSurj_mapArrow_of_hasRightCalculusOfFractions L W).mem_essImage f
    have := preservesKernel L W g.hom
    have : HasLimit (parallelPair (L.map g.hom) 0) :=
      ⟨_, (KernelFork.isLimitMapConeEquiv _ L).1
        (isLimitOfPreserves L (kernelIsKernel g.hom))⟩
    hasLimit_of_iso ((parallelPair.ext (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e)
        (show L.map g.hom ≫ e.hom.right = e.hom.left ≫ f from (Arrow.w_mk e.hom).symm)
        (show (0 : _ ⟶ _) ≫ e.hom.right = e.hom.left ≫ 0 by simp) :
          parallelPair (L.map g.hom) 0 ≅ parallelPair f 0))

end

end Right

section

variable [Abelian C] [Preadditive D] [L.Additive]

include L in
/-- The localization of a category with a zero object by an additive localization functor has
a zero object. -/
theorem hasZeroObject : HasZeroObject D :=
  ⟨L.obj 0, by rw [IsZero.iff_id_eq_zero, ← L.map_id, id_zero, L.map_zero]⟩

include L W in
/-- The localization of an abelian category has binary products, as the additive localization
functor preserves biproducts and is essentially surjective. -/
theorem hasBinaryProducts : HasBinaryProducts D :=
  haveI := Localization.essSurj L W
  @hasBinaryProducts_of_hasLimit_pair D _ fun {X Y} ↦ hasLimit_of_iso
   (mapPairIso (L.objObjPreimageIso X) (L.objObjPreimageIso Y) : pair _ _ ≅ pair X Y)

include L W in
/-- The localization of an abelian category has finite products. -/
theorem hasFiniteProducts' : HasFiniteProducts D :=
  haveI := hasZeroObject L
  haveI := hasBinaryProducts L W
  hasFiniteProducts_of_has_binary_and_terminal

section

variable [W.HasLeftCalculusOfFractions] [W.HasRightCalculusOfFractions]

include W in
/-- `L` maps the coimage-image comparison of `g` to the coimage-image comparison of
`L.map g`, up to the canonical isomorphisms induced by preservation of kernels and
cokernels; in particular the latter is an isomorphism. -/
lemma isIso_coimageImageComparison_map [HasKernels D] [HasCokernels D] {X Y : C} (g : X ⟶ Y) :
    IsIso (Abelian.coimageImageComparison (L.map g)) := by
  have := preservesMonomorphisms L W
  have := preservesKernel L W g
  have := preservesKernel L W (cokernel.π g)
  have := preservesCokernel L W g
  have := preservesCokernel L W (kernel.ι g)
  let e₁ : Abelian.coimage (L.map g) ≅ L.obj (Abelian.coimage g) := cokernel.mapIso _ _
    (PreservesKernel.iso L g).symm (Iso.refl _) (by simp) ≪≫
    (PreservesCokernel.iso L (kernel.ι g)).symm
  let e₂ : Abelian.image (L.map g) ≅ L.obj (Abelian.image g) := kernel.mapIso _ _ (Iso.refl _)
    (PreservesCokernel.iso L g).symm (by simp) ≪≫
    (PreservesKernel.iso L (cokernel.π g)).symm
  have sq : e₁.hom ≫ L.map (Abelian.coimageImageComparison g) =
      Abelian.coimageImageComparison (L.map g) ≫ e₂.hom := by
    rw [← cancel_epi (Abelian.coimage.π (L.map g)), ← cancel_mono (L.map (Abelian.image.ι g))]
    simp [-Functor.map_comp, e₁, e₂, ← L.map_comp]
  convert_to IsIso (e₁.hom ≫ L.map (Abelian.coimageImageComparison g) ≫ e₂.inv) using 1
  · rw [← Category.assoc, eq_comm, Iso.comp_inv_eq, sq]
  infer_instance

include L W in
/-- The coimage-image comparison of any morphism of the localized category is an isomorphism,
since any morphism is isomorphic to the image of a morphism of `C` in the arrow category. -/
lemma isIso_coimageImageComparison [HasKernels D] [HasCokernels D] {A B : D} (φ : A ⟶ B) :
    IsIso (Abelian.coimageImageComparison φ) := by
  obtain ⟨g, ⟨e⟩⟩ := (Localization.essSurj_mapArrow L W).mem_essImage (Arrow.mk φ)
  have h₁ := isIso_coimageImageComparison_map L W g.hom
  rw [← MorphismProperty.isomorphisms.iff] at h₁ ⊢
  exact ((MorphismProperty.isomorphisms D).arrow_mk_iso_iff
    (Abelian.coimageImageComparisonFunctor.mapIso e)).1 h₁

include L W in
/-- The localization of an abelian category at a morphism property with left and right
calculi of fractions is abelian, provided it has been endowed with a preadditive structure
making the localization functor additive (see
`Mathlib/CategoryTheory/Localization/CalculusOfFractions/Preadditive.lean`). -/
@[stacks 05QG "part (3)", instance_reducible]
def abelian : Abelian D :=
  have := hasFiniteProducts' L W
  have := hasKernels L W
  have := hasCokernels L W
  @Abelian.ofCoimageImageComparisonIsIso D _ _ _ _ (isIso_coimageImageComparison L W) _

end

end

section

variable [Abelian C] [Abelian D] [L.Additive] [W.HasRightCalculusOfFractions]

include W in
/-- A localization functor between abelian categories for a morphism property with right
calculus of fractions preserves finite limits. The abelian structure on the localized
category can be obtained from `CategoryTheory.Localization.abelian`. -/
@[stacks 05QG "part (3)"]
theorem preservesFiniteLimits : PreservesFiniteLimits L :=
  @L.preservesFiniteLimits_of_preservesKernels _ _ _ _ _ _ _ _ _ _ _ _ fun f ↦ preservesKernel L W f

end

section

variable [Abelian C] [Abelian D] [L.Additive] [W.HasLeftCalculusOfFractions]

include W in
/-- A localization functor between abelian categories for a morphism property with left
calculus of fractions preserves finite colimits. The abelian structure on the localized
category can be obtained from `CategoryTheory.Localization.abelian`. -/
@[stacks 05QG "part (3)"]
lemma preservesFiniteColimits : PreservesFiniteColimits L :=
  @L.preservesFiniteColimits_of_preservesCokernels _ _ _ _ _ _ _ _ _ _ _ _
    fun f ↦ preservesCokernel L W f

end

end CategoryTheory.Localization
