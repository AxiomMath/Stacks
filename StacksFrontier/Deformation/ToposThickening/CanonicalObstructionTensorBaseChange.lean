module

public import StacksFrontier.Deformation.ToposThickening.KernelComplexFlatBaseChange
public import StacksFrontier.Homology.ExtendScalars.DerivedMonoidal

/-!
# Base change of the derived tensor comparison of a lifted differential

Let `fR : R' → R` and `fS : S' → S` be surjections of commutative rings in a commuting square
with `a : R' → S'` and `b : R → S`, write `I = ker fR` and `J = ker fS`, let `L` be a free
differential lift of a complex `P` of `R`-modules along `fR`, and let `c` and `cS` be curvature
data for `L` and for its base change.

The curvature chain maps already agree after base change
(`LiftedDifferentialCurvature.hom_baseChange`). What is proved here is the matching statement
for the second half of the construction of the canonical obstruction map: the comparison of the
ordinary kernel tensor complex with the derived tensor product. Derived base change
`β = - ⊗ᴸ_R S` carries `c.tensorComparison` to `cS.tensorComparison`, read through the
monoidality of derived base change on K-flat representatives and through the comparison of the
two kernel objects.

## Main definitions

* `Deformation.Obstruction.kernelObjectResolutionBaseChange`: the comparison
  `β(Q T) ⟶ J/J²` attached to a resolution `q : T ⟶ I/I²`, namely the K-flat comparison for
  derived base change followed by the base change of `q`.
* `Deformation.Obstruction.kernelObjectBaseChange`: the comparison
  `β(I/I²) ⟶ J/J²` in `D(S)`, computed through such a resolution.
* `Deformation.Obstruction.tensorComparisonBaseChangeMap`: the canonical comparison
  `β(Q P ⊗ᴸ_R I/I²) ⟶ (Q (S ⊗_R P)) ⊗ᴸ_S J/J²`.

## Main results

* `Deformation.Obstruction.isKProjective_mapCochainComplex`: extension of scalars carries a
  bounded-above complex of projectives to a K-projective complex.
* `Deformation.Obstruction.LiftedDifferentialCurvature.tensorComparison_baseChange`: the base
  change of the tensor comparison of `c` is the tensor comparison of `cS`, read through the
  comparison of total tensor complexes and the canonical comparison on derived tensor products.
* `Deformation.Obstruction.isIso_kernelObjectBaseChange` and
  `Deformation.Obstruction.isIso_tensorComparisonBaseChangeMap`: those comparisons are
  isomorphisms when `a` and `b` are flat and `J = I · S'`.

## Implementation notes

The square itself needs no flatness and no cartesian hypothesis on kernels: it holds for any
commuting square of four rings whose two vertical maps are surjective. Flatness of
`a : R' → S'` and of `b : R → S` together with `J = I · S'` enter only to make the comparisons
isomorphisms, through `quasiIso_kernelComplexBaseChange`. In particular the square is available
at a localization square `R' → (R')_g`.

The resolution `q : T ⟶ I/I²` is required to be K-projective, not merely K-flat, because
`LiftedDifferentialCurvature.tensorComparison_after_resolution` lifts a map through a
quasi-isomorphism. On the base-changed side K-projectivity is not transported abstractly:
`T` is taken bounded above with projective terms, and extension of scalars — a left adjoint
whose right adjoint is exact — preserves both properties, so the base change is again a
bounded-above complex of projectives.

## References

* [Stacks Project, Tag 0DYR](https://stacks.math.columbia.edu/tag/0DYR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.ExtendScalars CochainComplex.DerivedExtensionScalars
  CochainComplex.DerivedTensor
open StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Deformation.Obstruction

variable {R' R S' S : Type u} [CommRing R'] [CommRing R] [CommRing S'] [CommRing S]

/-! ### K-projectivity of a base-changed resolution -/

/-- Extension of scalars carries a bounded-above complex of projective modules to a
bounded-above complex of projective modules, hence to a K-projective complex: it is a left
adjoint whose right adjoint, restriction of scalars, is exact. -/
lemma isKProjective_mapCochainComplex (b : R →+* S)
    (T : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ) [T.IsStrictlyLE m]
    (hTproj : ∀ i, Projective (T.X i)) :
    ((mapCochainComplex b).obj T).IsKProjective := by
  have hLE : ((mapCochainComplex b).obj T).IsStrictlyLE m := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact Functor.map_isZero (ModuleCat.extendScalars.{u, u, u} b)
      (T.isZero_of_isStrictlyLE m i hi)
  have hproj : ∀ i, Projective (((mapCochainComplex b).obj T).X i) := fun i =>
    (ModuleCat.extendRestrictScalarsAdj.{u} b).map_projective _ (hTproj i)
  exact CochainComplex.isKProjective_of_projective _ m

/-- The kernel complex of a surjection receives a quasi-isomorphism from a bounded-above
complex of projective modules. -/
lemma exists_projective_kernelComplex_resolution (f : R' →+* R) (hf : Function.Surjective f) :
    ∃ (T : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ) (q : T ⟶ kernelComplex f hf),
      T.IsStrictlyLE m ∧ (∀ i, Projective (T.X i)) ∧ QuasiIso q := by
  have : (kernelComplex f hf).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (squareZeroKernelModule.{u, u} f hf) i (by omega)
  obtain ⟨T, m, q, hm, hproj, hq⟩ := exists_projective_resolution (kernelComplex f hf) 0
  exact ⟨T, m, q, hm, hproj, hq⟩

/-! ### Comparison of the two kernel objects -/

variable (fR : R' →+* R) (hfR : Function.Surjective fR)
  (fS : S' →+* S) (hfS : Function.Surjective fS)
  (a : R' →+* S') (b : R →+* S) (hcomm : b.comp fR = fS.comp a)

/-- The base change along `b` of a resolution `q : T ⟶ I/I²`, as a map `S ⊗_R T ⟶ J/J²` of
complexes of `S`-modules. -/
noncomputable def kernelComplexResolutionBaseChange
    {T : CochainComplex (ModuleCat.{u} R) ℤ} (q : T ⟶ kernelComplex fR hfR) :
    (mapCochainComplex b).obj T ⟶ kernelComplex fS hfS :=
  (mapCochainComplex b).map q ≫ kernelComplexBaseChangeMap fR hfR fS hfS a b hcomm

/-- The comparison `β(Q T) ⟶ J/J²` attached to a resolution `q : T ⟶ I/I²` by a K-flat
complex: the K-flat comparison for derived base change followed by the base change of `q`. -/
noncomputable def kernelObjectResolutionBaseChange
    (T : CochainComplex (ModuleCat.{u} R) ℤ) (hT : T.KFlat)
    (q : T ⟶ kernelComplex fR hfR) :
    (derivedExtensionScalarsGeneral.{u, u, u} b).functor.obj (DerivedCategory.Q.obj T) ⟶
      squareZeroKernelObject fS hfS :=
  (kFlatComparisonIso b T hT).hom ≫
    DerivedCategory.Q.map (kernelComplexResolutionBaseChange fR hfR fS hfS a b hcomm q)

/-- The comparison `β(I/I²) ⟶ J/J²` of the two kernel objects in `D(S)`, computed through a
K-flat resolution `q : T ⟶ I/I²`. -/
noncomputable def kernelObjectBaseChange
    (T : CochainComplex (ModuleCat.{u} R) ℤ) (hT : T.KFlat)
    (q : T ⟶ kernelComplex fR hfR) (hq : IsIso (DerivedCategory.Q.map q)) :
    (derivedExtensionScalarsGeneral.{u, u, u} b).functor.obj (squareZeroKernelObject fR hfR) ⟶
      squareZeroKernelObject fS hfS :=
  letI := hq
  (derivedExtensionScalarsGeneral.{u, u, u} b).functor.map (inv (DerivedCategory.Q.map q)) ≫
    kernelObjectResolutionBaseChange fR hfR fS hfS a b hcomm T hT q

/-! ### Base change of the tensor comparison -/

/-- The comparison from derived to termwise extension of scalars is natural in the complex.
This is the naturality of `kFlatComparisonIso` without the K-flatness hypotheses, which the
isomorphism needs but the naturality does not. -/
private lemma derivedExtensionScalars_comparison_naturality (b : R →+* S)
    {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (h : X ⟶ Y) :
    (derivedExtensionScalarsGeneral.{u, u, u} b).functor.map (DerivedCategory.Q.map h) ≫
        (derivedExtensionScalarsGeneral.{u, u, u} b).comparison.app Y =
      (derivedExtensionScalarsGeneral.{u, u, u} b).comparison.app X ≫
        DerivedCategory.Q.map ((mapCochainComplex b).map h) :=
  (derivedExtensionScalarsGeneral.{u, u, u} b).comparison.naturality h

private lemma kFlatComparisonIso_hom_eq (b : R →+* S)
    (X : CochainComplex (ModuleCat.{u} R) ℤ) (hX : X.KFlat) :
    (kFlatComparisonIso b X hX).hom =
      (derivedExtensionScalarsGeneral.{u, u, u} b).comparison.app X := rfl

/-- The canonical comparison `β(Q P ⊗ᴸ_R I/I²) ⟶ Q(S ⊗_R P) ⊗ᴸ_S J/J²`, computed through a
K-flat resolution `q : T ⟶ I/I²`: the monoidality of derived base change on the K-flat
representatives `P` and `T`, with the first factor carried to its base change by the K-flat
comparison and the second by the comparison of kernel objects. -/
noncomputable def tensorComparisonBaseChangeMap
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
    (T : CochainComplex (ModuleCat.{u} R) ℤ) (hT : T.KFlat)
    (q : T ⟶ kernelComplex fR hfR) (hq : IsIso (DerivedCategory.Q.map q)) :
    (derivedExtensionScalarsGeneral.{u, u, u} b).functor.obj
        (((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj P)).obj
          (squareZeroKernelObject fR hfR)) ⟶
      ((canonicalDerivedTensorProductFunctor S).obj
          (DerivedCategory.Q.obj ((mapCochainComplex b).obj P))).obj
        (squareZeroKernelObject fS hfS) :=
  letI := hq
  (derivedExtensionScalarsGeneral.{u, u, u} b).functor.map
      (((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj P)).map
        (inv (DerivedCategory.Q.map q))) ≫
    (derivedMonoidalIso b P T hP hT).hom ≫
    ((canonicalDerivedTensorProductFunctor S).map (kFlatComparisonIso b P hP).hom).app
      ((derivedExtensionScalarsGeneral.{u, u, u} b).functor.obj (DerivedCategory.Q.obj T)) ≫
    ((canonicalDerivedTensorProductFunctor S).obj
        (DerivedCategory.Q.obj ((mapCochainComplex b).obj P))).map
      (kernelObjectResolutionBaseChange fR hfR fS hfS a b hcomm T hT q)

/-- The base change of the comparison of total tensor complexes is the comparison of the
base-changed total tensor complexes, read through the monoidality of degreewise extension of
scalars. -/
private lemma monoidalIso_inv_tensor_resolution
    {P T : CochainComplex (ModuleCat.{u} R) ℤ} (q : T ⟶ kernelComplex fR hfR) :
    (extendScalarsMonoidalIso b P T).inv ≫
        (𝟙 ((mapCochainComplex b).obj P) ⊗ₘ
          kernelComplexResolutionBaseChange fR hfR fS hfS a b hcomm q) =
      (mapCochainComplex b).map (𝟙 P ⊗ₘ q) ≫
        kernelTensorBaseChangeMap fR hfR fS hfS a b hcomm P := by
  have h := extendScalarsMonoidalIso_naturality b (𝟙 P) q
  rw [CategoryTheory.Functor.map_id] at h
  have h3 : (mapCochainComplex b).map (𝟙 P ⊗ₘ q) ≫
      (extendScalarsMonoidalIso b P (kernelComplex fR hfR)).inv =
      (extendScalarsMonoidalIso b P T).inv ≫
        (𝟙 ((mapCochainComplex b).obj P) ⊗ₘ (mapCochainComplex b).map q) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hsplit : (𝟙 ((mapCochainComplex b).obj P) ⊗ₘ
        kernelComplexResolutionBaseChange fR hfR fS hfS a b hcomm q) =
      (𝟙 ((mapCochainComplex b).obj P) ⊗ₘ (mapCochainComplex b).map q) ≫
        (𝟙 ((mapCochainComplex b).obj P) ⊗ₘ
          kernelComplexBaseChangeMap fR hfR fS hfS a b hcomm) := by
    rw [kernelComplexResolutionBaseChange]
    simp only [tensorHom_comp_tensorHom, Category.id_comp]
  rw [hsplit, kernelTensorBaseChangeMap,
    ← Category.assoc ((mapCochainComplex b).map (𝟙 P ⊗ₘ q)), h3, Category.assoc]

/-- **Base change of the derived tensor comparison of a lifted differential.** For a commuting
square of ring maps whose two vertical maps `fR : R' → R` and `fS : S' → S` are surjective,
derived base change carries the comparison of the kernel tensor complex with the derived tensor
product to the corresponding comparison for the base-changed lift, through the comparison of
total tensor complexes and the canonical comparison of derived tensor products. -/
theorem LiftedDifferentialCurvature.tensorComparison_baseChange
    {P : CochainComplex (ModuleCat.{u} R) ℤ} {L : FreeDifferentialLift fR P}
    (c : LiftedDifferentialCurvature fR hfR P L)
    (cS : LiftedDifferentialCurvature fS hfS ((mapCochainComplex b).obj P)
      (L.baseChange hfR hfS a b hcomm))
    (T : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ) (hTLE : T.IsStrictlyLE m)
    (hTproj : ∀ i, Projective (T.X i)) (hT : T.KFlat)
    (q : T ⟶ kernelComplex fR hfR) (hq : QuasiIso q)
    (hQq : IsIso (DerivedCategory.Q.map q)) :
    (derivedExtensionScalarsGeneral.{u, u, u} b).functor.map c.tensorComparison ≫
        tensorComparisonBaseChangeMap fR hfR fS hfS a b hcomm P c.isKFlat T hT q hQq =
      (derivedExtensionScalarsGeneral.{u, u, u} b).comparison.app
          (P ⊗ kernelComplex fR hfR) ≫
        DerivedCategory.Q.map (kernelTensorBaseChangeMap fR hfR fS hfS a b hcomm P) ≫
        cS.tensorComparison := by
  have := hq
  have := hQq
  have := hTLE
  have hTp : ∀ n, Projective (T.X n) := hTproj
  have := hTp
  have hTK : T.IsKProjective := CochainComplex.isKProjective_of_projective T m
  have hTSK : ((mapCochainComplex b).obj T).IsKProjective :=
    isKProjective_mapCochainComplex b T m hTproj
  have hTS : ((mapCochainComplex b).obj T).KFlat :=
    CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} b T hT
  have htq : QuasiIso (𝟙 P ⊗ₘ q) := quasiIso_tensorLeft_map P c.isKFlat q
  have htqiso : IsIso (DerivedCategory.Q.map (𝟙 P ⊗ₘ q)) := inferInstance
  apply (cancel_epi ((derivedExtensionScalarsGeneral.{u, u, u} b).functor.map
    (DerivedCategory.Q.map (𝟙 P ⊗ₘ q)))).mp
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    c.tensorComparison_after_resolution T hT q]
  have hcancel : (derivedExtensionScalarsGeneral.{u, u, u} b).functor.map
        (((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj P)).map
          (DerivedCategory.Q.map q)) ≫
      (derivedExtensionScalarsGeneral.{u, u, u} b).functor.map
        (((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj P)).map
          (inv (DerivedCategory.Q.map q))) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      IsIso.hom_inv_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [tensorComparisonBaseChangeMap, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hcancel]
  dsimp only [derivedMonoidalIso, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_inv, Iso.app_hom]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [NatTrans.naturality_assoc
      ((canonicalDerivedTensorProductFunctor S).map (kFlatComparisonIso b P c.isKFlat).hom)
      (kFlatComparisonIso b T hT).inv,
    ← NatTrans.comp_app_assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    kernelObjectResolutionBaseChange, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_assoc]
  have htail : DerivedCategory.Q.map (extendScalarsMonoidalIso b P T).inv ≫
        ((canonicalDerivedTensorProduct S).comparison ((mapCochainComplex b).obj P)
          ((mapCochainComplex b).obj T) cS.isKFlat hTS).inv ≫
        ((canonicalDerivedTensorProductFunctor S).obj
            (DerivedCategory.Q.obj ((mapCochainComplex b).obj P))).map
          (DerivedCategory.Q.map
            (kernelComplexResolutionBaseChange fR hfR fS hfS a b hcomm q)) =
      DerivedCategory.Q.map ((mapCochainComplex b).map (𝟙 P ⊗ₘ q)) ≫
        DerivedCategory.Q.map (kernelTensorBaseChangeMap fR hfR fS hfS a b hcomm P) ≫
        cS.tensorComparison := by
    rw [← cS.tensorComparison_after_resolution ((mapCochainComplex b).obj T) hTS
        (kernelComplexResolutionBaseChange fR hfR fS hfS a b hcomm q),
      ← CategoryTheory.Functor.map_comp_assoc,
      monoidalIso_inv_tensor_resolution fR hfR fS hfS a b hcomm q,
      CategoryTheory.Functor.map_comp_assoc]
  rw [kFlatComparisonIso_hom_eq, htail]
  rw [reassoc_of% (derivedExtensionScalars_comparison_naturality b (𝟙 P ⊗ₘ q))]
  exact (Category.assoc _ _ _).symm

/-! ### The comparisons are isomorphisms -/

/-- Under flatness and `J = I · S'`, the base change of a resolution of `I/I²` becomes an
isomorphism in the derived category. -/
private lemma isIso_Q_map_kernelComplexResolutionBaseChange
    (hJ : RingHom.ker fS = Ideal.map a (RingHom.ker fR)) (ha : a.Flat) (hb : b.Flat)
    (T : CochainComplex (ModuleCat.{u} R) ℤ) (q : T ⟶ kernelComplex fR hfR) (hq : QuasiIso q) :
    IsIso (DerivedCategory.Q.map
      (kernelComplexResolutionBaseChange fR hfR fS hfS a b hcomm q)) := by
  have : QuasiIso (kernelComplexResolutionBaseChange fR hfR fS hfS a b hcomm q) :=
    quasiIso_kernelComplexBaseChange fR hfR fS hfS a b hcomm hJ ha hb T q hq
  infer_instance

/-- For flat `a` and `b` and a cartesian square on kernels, the comparison of the two kernel
objects is an isomorphism of `D(S)`: the base change of a resolution of `I/I²` is a resolution
of `J/J²`. -/
theorem isIso_kernelObjectBaseChange
    (hJ : RingHom.ker fS = Ideal.map a (RingHom.ker fR)) (ha : a.Flat) (hb : b.Flat)
    (T : CochainComplex (ModuleCat.{u} R) ℤ) (hT : T.KFlat)
    (q : T ⟶ kernelComplex fR hfR) (hq : QuasiIso q)
    (hQq : IsIso (DerivedCategory.Q.map q)) :
    IsIso (kernelObjectBaseChange fR hfR fS hfS a b hcomm T hT q hQq) := by
  have := hQq
  have := isIso_Q_map_kernelComplexResolutionBaseChange fR hfR fS hfS a b hcomm hJ ha hb T q hq
  rw [kernelObjectBaseChange, kernelObjectResolutionBaseChange]
  infer_instance

/-- Under the same hypotheses the comparison of the derived tensor products is an
isomorphism. -/
theorem isIso_tensorComparisonBaseChangeMap
    (hJ : RingHom.ker fS = Ideal.map a (RingHom.ker fR)) (ha : a.Flat) (hb : b.Flat)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
    (T : CochainComplex (ModuleCat.{u} R) ℤ) (hT : T.KFlat)
    (q : T ⟶ kernelComplex fR hfR) (hq : QuasiIso q)
    (hQq : IsIso (DerivedCategory.Q.map q)) :
    IsIso (tensorComparisonBaseChangeMap fR hfR fS hfS a b hcomm P hP T hT q hQq) := by
  have := hQq
  have := isIso_Q_map_kernelComplexResolutionBaseChange fR hfR fS hfS a b hcomm hJ ha hb T q hq
  rw [tensorComparisonBaseChangeMap, kernelObjectResolutionBaseChange]
  infer_instance

end Deformation.Obstruction

end
