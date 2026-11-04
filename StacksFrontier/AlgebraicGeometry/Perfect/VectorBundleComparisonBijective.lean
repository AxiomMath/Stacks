module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.EulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparisonSurjective
public import StacksCore.Tactic.StacksAttribute

/-!
# The comparison homomorphism `K₀(Vect(X)) ⟶ K₀(X)` is a bijection

Let `X` be a scheme. The comparison homomorphism `AlgebraicGeometry.comparisonAddHom`, which
sends the class of a finite locally free `𝒪_X`-module to the class of that module placed in
degree zero, is an isomorphism from the Grothendieck group of finite locally free modules onto
the Grothendieck group of perfect objects of `D(𝒪_X)`. Surjectivity is
`Stacks.Perfect.BoundedLocallyFreeComplexes.surjective_comparisonAddHom`; this file supplies the
inverse homomorphism and hence injectivity, and puts the two halves together.

## Main definitions

* `Stacks.Perfect.BoundedLocallyFreeComplexes.eulerCharPerfect`: the Euler characteristic in
  `K₀(Vect(X))` of a perfect object of `D(𝒪_X)`, computed on a bounded complex of finite locally
  free modules representing it.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.inverseAddHom`: the homomorphism
  `K₀(D_perf(𝒪_X)) ⟶ K₀(Vect(X))` that Euler characteristic defines.

## Main results

* `Stacks.Perfect.BoundedLocallyFreeComplexes.eulerCharPerfect_triangle`: the Euler
  characteristic is additive on distinguished triangles of perfect objects.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.inverseAddHom_comparisonAddHom`: the inverse
  homomorphism is a left inverse of the comparison homomorphism.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.injective_comparisonAddHom`.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.bijective_comparisonAddHom`.

## Implementation notes

The source's inverse is the Euler characteristic `Σᵢ (-1)ⁱ [ℰⁱ]`, taken on a bounded complex of
finite locally free modules representing the perfect object. Three inputs make that well defined
and additive, and the statements below take each as an argument:

* `hrep`: every perfect object of `D(𝒪_X)` is isomorphic to the image of a bounded complex of
  finite locally free modules. This is [Stacks, Tag 0F8F]; on a quasi-compact quasi-separated
  scheme with the resolution property and affine diagonal it is
  `BoundedLocallyFreeComplexes.exists_boundedFiniteLocallyFree_iso_of_affineDiagonal`.
* `hroof`: a morphism of `D(𝒪_X)` between two such complexes is represented by a roof
  `ℰ^• ← 𝒢^• → ℱ^•` of such complexes whose left leg is a quasi-isomorphism. This is
  [Stacks, Tag 0F8G]; under the same hypotheses it is
  `BoundedLocallyFreeComplexes.exists_boundedFiniteLocallyFree_roof_of_affineDiagonal`.
  It makes the Euler characteristic independent of the representative, the two legs of the roof
  being quasi-isomorphisms to which
  `Stacks.Perfect.BoundedLocallyFreeComplexes.eulerCharComplex_eq_of_quasiIso` applies.
* `hcyc`: the modules of cycles of a bounded acyclic complex of finite locally free modules are
  finite locally free. This is step (2) of the proof of [Stacks, Tag 0FDJ] itself — the descending
  induction over the short exact sequences `0 → Z^i → ℰ^i → Z^{i+1} → 0` — and not a separate
  tag; it is the input of
  `Stacks.Perfect.BoundedLocallyFreeComplexes.eulerCharComplex_eq_zero_of_acyclic`.

Additivity on a distinguished triangle `T` is the source's argument: the first two vertices are
replaced by bounded complexes of finite locally free modules, `hroof` represents the map between
them by a roof, and `T` is then isomorphic to the mapping cone triangle of the roof's right leg,
on which the Euler characteristic is additive by
`Stacks.Perfect.BoundedLocallyFreeComplexes.eulerCharComplex_mappingCone`.

Two instance priorities are set at the top of the namespace and both are load-bearing.
`HasDerivedCategory.standard` is given priority 10000 because
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` of
`StacksFrontier.Homology.DerivedCategory.LocallySmall` is a `HasDerivedCategory.{u}` instance for
`X.Modules` while the standard one is at level `u + 1`: at equal priority the locally small one
wins, and then `Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory`, which is
elaborated against the standard one, no longer agrees with the statements here — the symptom is
`IsPerfect.{u, u, u}` against `IsPerfect.{u, u, u + 1}`.
`Stacks.Perfect.BoundedLocallyFreeComplexes.hasDerivedCategoryStandardRingedSiteModules` is given
priority 20000 for the reason recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparisonSurjective`: without it, identifying
the two spellings of the derived category of the `𝒪_X`-modules exhausts the elaborator, and the
statements mentioning `AlgebraicGeometry.comparisonAddHom` time out.

The morphism `T.mor₁` of the triangle is taken through `ObjectProperty.ι` to an explicitly typed
morphism `m` of `D(𝒪_X)` before being handed to `hroof`: at the spelling
`(ObjectProperty.ι.mapTriangle.obj T).mor₁` its target is a projection of the mapped triangle
rather than `T.obj₂.obj`, and composites formed there are not the ones `Category.assoc` and the
cancellation lemmas for isomorphisms rewrite.

## References

* [Stacks Project, Tag 0FDJ](https://stacks.math.columbia.edu/tag/0FDJ)
* [Stacks Project, Tag 0F8F](https://stacks.math.columbia.edu/tag/0F8F)
* [Stacks Project, Tag 0F8G](https://stacks.math.columbia.edu/tag/0F8G)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry TopologicalSpace
open Stacks.Cohomology.PerfectComplexes
open Stacks.FiniteLocallyFree

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] hasDerivedCategoryStandardRingedSiteModules

variable (X : Scheme.{u})

/-- A module in degree zero is a complex that is strictly `≥ 0` and strictly `≤ 0`. -/
private theorem isStrictlyGE_and_isStrictlyLE_single (M : X.Modules) :
    ((CochainComplex.singleFunctor X.Modules 0).obj M).IsStrictlyGE 0 ∧
      ((CochainComplex.singleFunctor X.Modules 0).obj M).IsStrictlyLE 0 :=
  ⟨(CochainComplex.isStrictlyGE_iff _ 0).2 fun i hi =>
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i (by omega),
    (CochainComplex.isStrictlyLE_iff _ 0).2 fun i hi =>
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i (by omega)⟩

/-- If `p` is a quasi-isomorphism, a roof `inv (Q p) ≫ Q q = α` gives `Q q = Q p ≫ α`. -/
private theorem map_eq_comp_of_inv_comp_eq {E F G : CochainComplex X.Modules ℤ} (p : G ⟶ E)
    [QuasiIso p] (q : G ⟶ F) (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F)
    (he : inv (DerivedCategory.Q.map p) ≫ DerivedCategory.Q.map q = α) :
    DerivedCategory.Q.map q = DerivedCategory.Q.map p ≫ α := by
  rw [← he]
  simp

/-- A finite locally free module in degree zero is a bounded complex of finite locally free
modules. -/
theorem boundedFiniteLocallyFreeComplex_single (M : X.Modules)
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    boundedFiniteLocallyFreeComplex X ((CochainComplex.singleFunctor X.Modules 0).obj M) := by
  obtain ⟨hge, hle⟩ := isStrictlyGE_and_isStrictlyLE_single X M
  refine ⟨⟨(CochainComplex.plus_iff X.Modules _).2 ⟨0, hge⟩,
    (CochainComplex.minus_iff _).2 ⟨0, hle⟩⟩, ?_⟩
  intro i
  by_cases hi : i = 0
  · subst i
    exact @IsFiniteLocallyFree.of_iso.{u, u, u} _ _ _ _ _ _ _ _
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).symm hM
  · exact finiteLocallyFree_of_isZero X _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi)

/-- The Euler characteristic of a module in degree zero is the class of that module. -/
theorem eulerCharComplex_single (M : X.Modules) :
    eulerCharComplex X ((CochainComplex.singleFunctor X.Modules 0).obj M) =
      VectorBundleKZero.classOf X M := by
  obtain ⟨hge, hle⟩ := isStrictlyGE_and_isStrictlyLE_single X M
  rw [eulerCharComplex_eq_sum X _ 0 0 hge hle]
  simp only [Finset.Icc_self, Finset.sum_singleton, Int.negOnePow_zero, Units.val_one, one_smul]
  exact classOf_eq_of_iso' X (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M)

/-- **Bounded complexes of finite locally free modules isomorphic in `D(𝒪_X)` have the same
Euler characteristic.** -/
theorem eulerCharComplex_eq_of_derivedIso
    (hroof : ∀ E F : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E →
      boundedFiniteLocallyFreeComplex X F →
      ∀ α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F,
        ∃ (G : CochainComplex X.Modules ℤ) (p : G ⟶ E) (_ : QuasiIso p) (q : G ⟶ F),
          boundedFiniteLocallyFreeComplex X G ∧
            inv (DerivedCategory.Q.map p) ≫ DerivedCategory.Q.map q = α)
    (hcyc : ∀ C : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X C →
      C.Acyclic → ∀ i : ℤ, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (C.cycles i))
    {E F : CochainComplex X.Modules ℤ} (hE : boundedFiniteLocallyFreeComplex X E)
    (hF : boundedFiniteLocallyFreeComplex X F)
    (e : DerivedCategory.Q.obj E ≅ DerivedCategory.Q.obj F) :
    eulerCharComplex X E = eulerCharComplex X F := by
  obtain ⟨G, p, hp, q, hG, he⟩ := hroof E F hE hF e.hom
  have := hp
  have hq : IsIso (DerivedCategory.Q.map q) := by
    rw [map_eq_comp_of_inv_comp_eq X p q _ he]
    infer_instance
  have : QuasiIso q := (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules q).mp hq
  exact (eulerCharComplex_eq_of_quasiIso X p hG hE hcyc).symm.trans
    (eulerCharComplex_eq_of_quasiIso X q hG hF hcyc)

/-! ### The Euler characteristic of a perfect object -/

section Inverse

variable
  (hrep : ∀ K : DerivedCategory X.Modules, IsPerfect (X := X.toRingedSpace) K →
    ∃ E : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E ∧
      Nonempty (DerivedCategory.Q.obj E ≅ K))
  (hroof : ∀ E F : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E →
    boundedFiniteLocallyFreeComplex X F →
    ∀ α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F,
      ∃ (G : CochainComplex X.Modules ℤ) (p : G ⟶ E) (_ : QuasiIso p) (q : G ⟶ F),
        boundedFiniteLocallyFreeComplex X G ∧
          inv (DerivedCategory.Q.map p) ≫ DerivedCategory.Q.map q = α)
  (hcyc : ∀ C : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X C →
    C.Acyclic → ∀ i : ℤ, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (C.cycles i))

/-- The **Euler characteristic of a perfect object** of `D(𝒪_X)`: the Euler characteristic of a
bounded complex of finite locally free modules representing it. -/
def eulerCharPerfect (K : PerfectDerivedCategory X) : VectorBundleKZero X :=
  eulerCharComplex X (hrep K.obj K.property).choose

include hroof hcyc in
/-- The Euler characteristic of a perfect object is computed by any bounded complex of finite
locally free modules representing it. -/
theorem eulerCharPerfect_eq (K : PerfectDerivedCategory X) (E : CochainComplex X.Modules ℤ)
    (hE : boundedFiniteLocallyFreeComplex X E)
    (e : DerivedCategory.Q.obj E ≅ K.obj) :
    eulerCharPerfect X hrep K = eulerCharComplex X E :=
  eulerCharComplex_eq_of_derivedIso X hroof hcyc
    (hrep K.obj K.property).choose_spec.1 hE
    ((hrep K.obj K.property).choose_spec.2.some ≪≫ e.symm)

include hroof hcyc in
/-- **The Euler characteristic is additive on distinguished triangles of perfect objects.**  Two
of the three vertices are replaced by bounded complexes of finite locally free modules, the map
between them is represented by a roof, and the triangle is then isomorphic to the mapping cone
triangle of the roof's right leg. -/
theorem eulerCharPerfect_triangle (T : Triangle (PerfectDerivedCategory X))
    (hT : T ∈ distTriang (PerfectDerivedCategory X)) :
    eulerCharPerfect X hrep T.obj₂ =
      eulerCharPerfect X hrep T.obj₁ + eulerCharPerfect X hrep T.obj₃ := by
  let P : ObjectProperty (DerivedCategory X.Modules) :=
    fun K => IsPerfect (X := X.toRingedSpace) K
  let U := P.ι.mapTriangle.obj T
  obtain ⟨E, hEb, ⟨eE⟩⟩ := hrep T.obj₁.obj T.obj₁.property
  obtain ⟨F, hFb, ⟨eF⟩⟩ := hrep T.obj₂.obj T.obj₂.property
  let m : T.obj₁.obj ⟶ T.obj₂.obj := P.ι.map T.mor₁
  obtain ⟨G, p, hp, q, hGb, he⟩ := hroof E F hEb hFb (eE.hom ≫ m ≫ eF.inv)
  have := hp
  have hpIso : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules p).2 hp
  have h1 : DerivedCategory.Q.map q =
      DerivedCategory.Q.map p ≫ (eE.hom ≫ m ≫ eF.inv) :=
    map_eq_comp_of_inv_comp_eq X p q _ he
  let eG : DerivedCategory.Q.obj G ≅ U.obj₁ := asIso (DerivedCategory.Q.map p) ≪≫ eE
  have hcomm : DerivedCategory.Q.map q ≫ eF.hom = eG.hom ≫ m := by
    simp only [h1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (Category.assoc _ _ _).symm
  let eT := isoTriangleOfIso₁₂ _ U
    (DerivedCategory.mappingCone_triangle_distinguished q) hT eG eF hcomm
  let eC : DerivedCategory.Q.obj (CochainComplex.mappingCone q) ≅ T.obj₃.obj :=
    Triangle.π₃.mapIso eT
  rw [eulerCharPerfect_eq X hrep hroof hcyc T.obj₁ G hGb eG,
    eulerCharPerfect_eq X hrep hroof hcyc T.obj₂ F hFb eF,
    eulerCharPerfect_eq X hrep hroof hcyc T.obj₃ _ (mappingCone_mem X q hGb hFb) eC,
    eulerCharComplex_mappingCone X q hGb hFb]
  abel

/-! ### The inverse homomorphism and injectivity -/

include hrep hroof hcyc in
/-- **The inverse of the comparison homomorphism.**  The Euler characteristic of a perfect
object is additive on distinguished triangles, so it descends to a homomorphism
`K₀(D_perf(𝒪_X)) ⟶ K₀(Vect(X))`. -/
def inverseAddHom : K0 (PerfectDerivedCategory X) →+ VectorBundleKZero X :=
  QuotientAddGroup.lift _ (FreeAbelianGroup.lift (eulerCharPerfect X hrep)) (by
    refine (AddSubgroup.closure_le
      (K := (FreeAbelianGroup.lift (eulerCharPerfect X hrep)).ker)).2 ?_
    rintro _ ⟨T, hT, rfl⟩
    rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, map_sub,
      FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of, eulerCharPerfect_triangle X hrep hroof hcyc T hT]
    abel)

include hrep hroof hcyc in
/-- The inverse homomorphism sends the class of a perfect object to its Euler characteristic. -/
theorem inverseAddHom_cls (K : PerfectDerivedCategory X) :
    inverseAddHom X hrep hroof hcyc (K0.cls K) = eulerCharPerfect X hrep K :=
  FreeAbelianGroup.lift_apply_of _ _

include hrep hroof hcyc in
/-- On the class of a finite locally free module the inverse homomorphism undoes the comparison
homomorphism: the module in degree zero is its own bounded finite locally free representative,
and its Euler characteristic is the class of the module. -/
theorem inverseAddHom_comparisonAddHom_classOf (M : X.Modules)
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    inverseAddHom X hrep hroof hcyc (comparisonAddHom X (VectorBundleKZero.classOf X M)) =
      VectorBundleKZero.classOf X M := by
  have hP := isPerfect_singleFunctor_of_isFiniteLocallyFree X M hM
  let K : PerfectDerivedCategory X := ⟨(DerivedCategory.singleFunctor X.Modules 0).obj M, hP⟩
  calc inverseAddHom X hrep hroof hcyc (comparisonAddHom X (VectorBundleKZero.classOf X M))
      = inverseAddHom X hrep hroof hcyc (K0.cls K) :=
        congrArg _ (comparisonAddHom_classOf X M hM hP)
    _ = eulerCharPerfect X hrep K := inverseAddHom_cls X hrep hroof hcyc K
    _ = eulerCharComplex X ((CochainComplex.singleFunctor X.Modules 0).obj M) :=
        eulerCharPerfect_eq X hrep hroof hcyc K _
          (boundedFiniteLocallyFreeComplex_single X M hM)
          ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app M).symm
    _ = VectorBundleKZero.classOf X M := eulerCharComplex_single X M

include hrep hroof hcyc in
/-- **The inverse homomorphism is a left inverse of the comparison homomorphism.** -/
theorem inverseAddHom_comp_comparisonAddHom :
    (inverseAddHom X hrep hroof hcyc).comp (comparisonAddHom X) = AddMonoidHom.id _ :=
  VectorBundleKZero.addHom_ext fun M hM =>
    inverseAddHom_comparisonAddHom_classOf X hrep hroof hcyc M hM

include hrep hroof hcyc in
/-- The inverse homomorphism is a left inverse of the comparison homomorphism, pointwise. -/
theorem inverseAddHom_comparisonAddHom (c : VectorBundleKZero X) :
    inverseAddHom X hrep hroof hcyc (comparisonAddHom X c) = c :=
  DFunLike.congr_fun (inverseAddHom_comp_comparisonAddHom X hrep hroof hcyc) c

include hrep hroof hcyc in
/-- **Injectivity of the comparison homomorphism `K₀(Vect(X)) ⟶ K₀(X)`.** -/
theorem injective_comparisonAddHom : Function.Injective (comparisonAddHom X) :=
  Function.LeftInverse.injective
    (g := inverseAddHom X hrep hroof hcyc) (inverseAddHom_comparisonAddHom X hrep hroof hcyc)

include hrep hroof hcyc in
/-- **The comparison homomorphism `K₀(Vect(X)) ⟶ K₀(X)` is a bijection.**  It is injective
because the Euler characteristic of a bounded complex of finite locally free modules gives an
inverse on the other side, and surjective by
`Stacks.Perfect.BoundedLocallyFreeComplexes.surjective_comparisonAddHom`. -/
theorem bijective_comparisonAddHom : Function.Bijective (comparisonAddHom X) :=
  ⟨injective_comparisonAddHom X hrep hroof hcyc, surjective_comparisonAddHom X hrep⟩

end Inverse

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
