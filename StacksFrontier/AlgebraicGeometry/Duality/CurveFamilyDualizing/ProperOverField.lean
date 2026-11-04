module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.StandardModelTwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexModel
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GorensteinDualizingInvertible
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibres
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Syntomic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalRelativeDimensionOne

/-!
# Relative dualizing complexes of a proper scheme over a field

Let `k` be a field and `v : V ⟶ Spec k` a proper morphism; it is flat and locally of finite
presentation, so relative dualizing complexes for `v` in the sense of [Stacks, Tag 0E2T] are
defined. This file identifies every relative dualizing complex `(K, ξ)` for `v`, relative to any
diagonal open `W`, with the dualizing complex `ω_V^• = v^×(𝒪_{Spec k})` of [Stacks, Tag 0BS2]
on cohomology sheaves; in particular `H^{-1}(K) ≅ ω_V`, the dualizing sheaf. When `V` is
moreover Gorenstein, equidimensional and of dimension one — for instance when `v` is syntomic of
relative dimension one and `V` is nonempty — `K` has no other cohomology, so `K ≅ ω_V[1]`.

## Main results

All in the namespace `Stacks.Duality.CurveFamilyDualizing`:

* `nonempty_iso_relativeDualizingComplex_of_isRelativeDualizingComplex`:
  `K ≅ a(𝒪_{Spec k})` at the standard model.
* `nonempty_homology_iso_dualizingComplexOverField_of_isRelativeDualizingComplex`:
  `H^j(K) ≅ H^j(ω_V^•)` for every `j`.
* `nonempty_homology_neg_one_iso_dualizingSheafOverField_of_isRelativeDualizingComplex`:
  `H^{-1}(K) ≅ ω_V`.
* `isZero_homology_dualizingComplexOverField_of_isGorenstein`
  and `isZero_homology_of_isRelativeDualizingComplex_of_isGorenstein`:
  for `V` Gorenstein, equidimensional of dimension one, `H^j(ω_V^•) = 0 = H^j(K)` for `j ≠ -1`.
* `nonempty_iso_singleFunctor_dualizingSheafOverField_of_isGorenstein`:
  then `K ≅ ω_V[1]`.
* `isGorenstein_equidimensional_dim_one_of_syntomicOfRelativeDimension`:
  a nonempty `V` syntomic of relative dimension one over `k` satisfies those hypotheses; the
  `..._of_syntomicOfRelativeDimension` and `..._of_isAtWorstNodalOfRelativeDimensionOne`
  corollaries package the conclusions.

## The argument

By [Stacks, Tag 0E2Z] (`Stacks.Duality.isRelativeDualizingComplex_relativeDualizingComplex`)
`a(𝒪_{Spec k})` with the map of Equation 0E2Q is a relative dualizing complex on `V ×_k V`; its
restriction to `W` and the uniqueness of [Stacks, Tag 0E2W] give `K ≅ a(𝒪_{Spec k})`, which is
`AlgebraicGeometry.Scheme.Hom.existsUnique_relativeDualizingComplex_iso_baseChange` along the
identity square. The complex `a(𝒪_{Spec k})` is `ω_V^•` read at the other model of the derived
category (`Stacks.Duality.StandardModel.relativeDualizingComplexModelIso`), and the cohomology
sheaves do not depend on the model (`StacksDraft.DerivedModel.modelHomologyFunctorIso`).

For the vanishing, at every point `x` the stalks of the cohomology sheaves of the dualizing
complex `ω_V^•` are concentrated in one degree, because `𝒪_{V,x}` is Gorenstein
(`Stacks.Duality.exists_stalk_homology_concentrated_free_of_isGorensteinLocalRing`), and that
degree is `-1` because the stalk of `ω_V = H^{-1}(ω_V^•)` is nonzero (`V` being Cohen–Macaulay,
equidimensional of dimension one). A module whose stalks all vanish is zero.

## Implementation notes

Relative dualizing complexes live at `CategoryTheory.HasDerivedCategory.standard`, while `ω_V^•`
and `ω_V` live at the locally small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`.
The statements name the standard model explicitly (with `@`) wherever an object of `D(𝒪_V)` at
that model occurs, so that instance search cannot silently pick the other model.

## References

* [Stacks Project, Tag 0E2T](https://stacks.math.columbia.edu/tag/0E2T)
* [Stacks Project, Tag 0E2W](https://stacks.math.columbia.edu/tag/0E2W)
* [Stacks Project, Tag 0E2Z](https://stacks.math.columbia.edu/tag/0E2Z)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS6](https://stacks.math.columbia.edu/tag/0BS6)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry StrictlyPerfect

universe u

namespace Stacks.Duality.CurveFamilyDualizing

variable {k : Type u} [Field k] {V : Scheme.{u}} (v : V ⟶ Spec (CommRingCat.of k)) [IsProper v]

/-! ### Gorenstein, equidimensional, dimension one -/

omit [IsProper v] in
/-- **A scheme syntomic over a field is Gorenstein.** A syntomic morphism is a local complete
intersection morphism, and `Spec k` is regular, hence Gorenstein, so its source is Gorenstein
([Stacks, Tag 0C15]). -/
theorem isGorenstein_of_syntomic_overField (hs : Syntomic v) : AlgebraicGeometry.IsGorenstein V :=
  isGorenstein_of_isLocalCompleteIntersectionMorphism v
    ((syntomic_iff_flat_and_isLocalCompleteIntersectionMorphism v).mp hs).2
    (isGorenstein_of_isRegular _ fun _ => ⟨⟨⊤, isAffineOpen_top _⟩, trivial,
      IsRegularRing.of_ringEquiv
        (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv⟩)

omit [IsProper v] in
/-- **Over a field, relative dimension one is local dimension one.** If `v : V ⟶ Spec k` is
syntomic of relative dimension one, then `V` has local dimension one at every point: `Spec k` has
a single point, so the fibre through any point is homeomorphic to `V` itself. -/
theorem topologicalKrullDimAt_eq_one_of_syntomicOfRelativeDimension
    (hv : SyntomicOfRelativeDimension 1 v) (x : V) : topologicalKrullDimAt V x = 1 := by
  have : Subsingleton (Spec (CommRingCat.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hpre : v ⁻¹' {v x} = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim (v y) (v x)
  let e : v.fiber (v x) ≃ₜ V :=
    (v.fiberHomeo (v x)).trans ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ V))
  have he : e (v.asFiber x) = x := v.fiberι_asFiber x
  rw [← he, ← topologicalKrullDimAt_eq_of_homeomorph e]
  exact (hv.2 x).trans Nat.cast_one

/-- **A nonempty scheme syntomic of relative dimension one over a field is a Gorenstein curve**:
it is Gorenstein, equidimensional, and of dimension one — the hypotheses of
`Stacks.Duality.isInvertible_dualizingSheafOverField_of_isGorenstein`. Equidimensionality
follows from the constancy of the local dimension (`equidimensional_of_topologicalKrullDimAt_eq`)
and the dimension is the supremum of the local dimensions ([Stacks, Tag 0B7I]). -/
theorem isGorenstein_equidimensional_dim_one_of_syntomicOfRelativeDimension
    (hv : SyntomicOfRelativeDimension 1 v) [Nonempty V] :
    AlgebraicGeometry.IsGorenstein V ∧ TopologicalSpace.Equidimensional V ∧
      topologicalKrullDim V = 1 := by
  have h := topologicalKrullDimAt_eq_one_of_syntomicOfRelativeDimension v hv
  refine ⟨isGorenstein_of_syntomic_overField v hv.1,
    equidimensional_of_topologicalKrullDimAt_eq k V v (d := 1)
      fun x => (h x).trans Nat.cast_one.symm, ?_⟩
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  simp_rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim, h]
  exact ciSup_const

/-! ### The dualizing complex over the field -/

/-- **The dualizing complex of a proper Gorenstein curve has cohomology only in degree `-1`.**
Let `V` be proper over a field `k`, Gorenstein, equidimensional and of dimension one. Then
`H^j(ω_V^•) = 0` for `j ≠ -1`, where `ω_V^• = v^×(𝒪_{Spec k})`
(`Stacks.Duality.dualizingComplexOverField`). At every point the stalks of the cohomology sheaves
are concentrated in one degree (the local ring being Gorenstein), and that degree is `-1` because
the stalk of `ω_V = H^{-1}(ω_V^•)` is nonzero. -/
theorem isZero_homology_dualizingComplexOverField_of_isGorenstein
    (hG : AlgebraicGeometry.IsGorenstein V) (hequi : TopologicalSpace.Equidimensional V)
    (hdim : topologicalKrullDim V = 1) {j : ℤ} (hj : j ≠ -1) :
    IsZero ((DerivedCategory.homologyFunctor V.Modules j).obj
      (dualizingComplexOverField v).obj) := by
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian v
  have hK := isDualizingComplex_dualizingComplexOverField_of_topologicalKrullDim_le_one v hdim.le
  refine isZero_of_forall_modulesStalk _ fun x => ?_
  obtain ⟨n, hz, -⟩ :=
    exists_stalk_homology_concentrated_free_of_isGorensteinLocalRing hK x
      (hG.isGorensteinLocalRing x)
  have hn : n = -1 := by
    by_contra hne
    exact not_nontrivial_iff_subsingleton.mpr
      (ModuleCat.isZero_iff_subsingleton.mp (hz (-1) (Ne.symm hne)))
      (nontrivial_stalk_dualizingSheafOverField_of_isCohenMacaulay v
        (AlgebraicGeometry.isCohenMacaulay_of_isGorenstein V) hequi hdim x)
  exact hz j (hn ▸ hj)

section Standard

/-- **A relative dualizing complex of a proper scheme over a field is `a(𝒪_{Spec k})`.** Let
`(K, ξ)` be a relative dualizing complex for `v : V ⟶ Spec k` proper ([Stacks, Tag 0E2T]),
relative to any diagonal open `W`, at the standard model of `D(𝒪_V)`. Then `K` is isomorphic to
the relative dualizing complex `a(𝒪_{Spec k})` of [Stacks, Remark 0B6S]
(`Stacks.Duality.StandardModel.relativeDualizingComplex`): by [Stacks, Tag 0E2Z] the latter is a
relative dualizing complex as well, and relative dualizing complexes on the same `W` are unique
up to unique isomorphism ([Stacks, Tag 0E2W]); this is
`AlgebraicGeometry.Scheme.Hom.existsUnique_relativeDualizingComplex_iso_baseChange` for the
identity square. -/
theorem nonempty_iso_relativeDualizingComplex_of_isRelativeDualizingComplex
    {D : v.DiagonalOpen}
    {K : @DerivedCategory (OXMod.{u, u} V.toRingedSpace) _ _ (HasDerivedCategory.standard _)}
    {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    (hK : @Scheme.Hom.IsRelativeDualizingComplex V (Spec (CommRingCat.of k)) v
      (HasDerivedCategory.standard _) (fun _ => HasDerivedCategory.standard _) _ _
      (@RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage (Spec (CommRingCat.of k)).toRingedSpace v.base)
        (fun _ => HasDerivedCategory.standard _)) D K ξ) :
    haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace v
    haveI : QuasiSeparatedSpace V := quasiSeparatedSpace_of_quasiSeparated v
    Nonempty (K ≅ (StandardModel.relativeDualizingComplex v).obj) := by
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace v
  have : QuasiSeparatedSpace V := quasiSeparatedSpace_of_quasiSeparated v
  obtain ⟨φ, -, -⟩ := Scheme.Hom.existsUnique_relativeDualizingComplex_iso_baseChange v hK
    (Scheme.Hom.isPullback_id v) D (𝟙 D.W)
    (by rw [Scheme.Hom.pullbackMapOfIsPullback_isPullback_id, Category.id_comp, Category.comp_id])
  exact ⟨((Scheme.Hom.DiagonalOpen.derivedPullbackIdIso V).app K).symm ≪≫ φ.symm⟩

/-- **The cohomology sheaves of a relative dualizing complex over a field are those of
`ω_V^•`.** For `(K, ξ)` a relative dualizing complex for `v : V ⟶ Spec k` proper, relative to
any diagonal open, and every `j`, the `j`-th cohomology sheaf of `K` (at the standard model) is
isomorphic to the `j`-th cohomology sheaf of the dualizing complex `ω_V^• = v^×(𝒪_{Spec k})` of
[Stacks, Tag 0BS2] (at the locally small model). -/
theorem nonempty_homology_iso_dualizingComplexOverField_of_isRelativeDualizingComplex
    {D : v.DiagonalOpen}
    {K : @DerivedCategory (OXMod.{u, u} V.toRingedSpace) _ _ (HasDerivedCategory.standard _)}
    {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    (hK : @Scheme.Hom.IsRelativeDualizingComplex V (Spec (CommRingCat.of k)) v
      (HasDerivedCategory.standard _) (fun _ => HasDerivedCategory.standard _) _ _
      (@RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage (Spec (CommRingCat.of k)).toRingedSpace v.base)
        (fun _ => HasDerivedCategory.standard _)) D K ξ) (j : ℤ) :
    Nonempty ((@DerivedCategory.homologyFunctor (OXMod.{u, u} V.toRingedSpace) _ _
      (HasDerivedCategory.standard _) j).obj K ≅
      (@DerivedCategory.homologyFunctor V.Modules _ _ (Scheme.Modules.hasDerivedCategory V) j).obj
        (dualizingComplexOverField v).obj) := by
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace v
  have : QuasiSeparatedSpace V := quasiSeparatedSpace_of_quasiSeparated v
  obtain ⟨e⟩ := nonempty_iso_relativeDualizingComplex_of_isRelativeDualizingComplex v hK
  exact ⟨(@DerivedCategory.homologyFunctor (OXMod.{u, u} V.toRingedSpace) _ _
      (HasDerivedCategory.standard _) j).mapIso e ≪≫
    ((StacksDraft.DerivedModel.modelHomologyFunctorIso (HasDerivedCategory.standard V.Modules)
      (Scheme.Modules.hasDerivedCategory V) j).app
        (StandardModel.relativeDualizingComplex v).obj).symm ≪≫
    (@DerivedCategory.homologyFunctor V.Modules _ _ (Scheme.Modules.hasDerivedCategory V) j).mapIso
      ((ObjectProperty.ι _).mapIso (StandardModel.relativeDualizingComplexModelIso v))⟩

/-- **`H^{-1}` of a relative dualizing complex over a field is the dualizing sheaf.** For
`(K, ξ)` a relative dualizing complex for `v : V ⟶ Spec k` proper ([Stacks, Tag 0E2T]), relative
to any diagonal open, `H^{-1}(K) ≅ ω_V`, the dualizing sheaf
`Stacks.Duality.dualizingSheafOverField` of [Stacks, Tag 0BS2]. -/
theorem nonempty_homology_neg_one_iso_dualizingSheafOverField_of_isRelativeDualizingComplex
    {D : v.DiagonalOpen}
    {K : @DerivedCategory (OXMod.{u, u} V.toRingedSpace) _ _ (HasDerivedCategory.standard _)}
    {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    (hK : @Scheme.Hom.IsRelativeDualizingComplex V (Spec (CommRingCat.of k)) v
      (HasDerivedCategory.standard _) (fun _ => HasDerivedCategory.standard _) _ _
      (@RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage (Spec (CommRingCat.of k)).toRingedSpace v.base)
        (fun _ => HasDerivedCategory.standard _)) D K ξ) :
    Nonempty ((@DerivedCategory.homologyFunctor (OXMod.{u, u} V.toRingedSpace) _ _
      (HasDerivedCategory.standard _) (-1)).obj K ≅
      dualizingSheafOverField v) :=
  nonempty_homology_iso_dualizingComplexOverField_of_isRelativeDualizingComplex v hK (-1)

/-- **A relative dualizing complex of a proper Gorenstein curve has cohomology only in degree
`-1`.** For `(K, ξ)` a relative dualizing complex for `v : V ⟶ Spec k` proper, relative to any
diagonal open, with `V` Gorenstein, equidimensional and of dimension one, `H^j(K) = 0` for
`j ≠ -1`. -/
theorem isZero_homology_of_isRelativeDualizingComplex_of_isGorenstein
    {D : v.DiagonalOpen}
    {K : @DerivedCategory (OXMod.{u, u} V.toRingedSpace) _ _ (HasDerivedCategory.standard _)}
    {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    (hK : @Scheme.Hom.IsRelativeDualizingComplex V (Spec (CommRingCat.of k)) v
      (HasDerivedCategory.standard _) (fun _ => HasDerivedCategory.standard _) _ _
      (@RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage (Spec (CommRingCat.of k)).toRingedSpace v.base)
        (fun _ => HasDerivedCategory.standard _)) D K ξ)
    (hG : AlgebraicGeometry.IsGorenstein V) (hequi : TopologicalSpace.Equidimensional V)
    (hdim : topologicalKrullDim V = 1) {j : ℤ} (hj : j ≠ -1) :
    IsZero ((@DerivedCategory.homologyFunctor (OXMod.{u, u} V.toRingedSpace) _ _
      (HasDerivedCategory.standard _) j).obj K) :=
  (isZero_homology_dualizingComplexOverField_of_isGorenstein v hG hequi hdim hj).of_iso
    (nonempty_homology_iso_dualizingComplexOverField_of_isRelativeDualizingComplex v hK j).some

/-- **A relative dualizing complex of a proper Gorenstein curve is `ω_V[1]`.** For `(K, ξ)` a
relative dualizing complex for `v : V ⟶ Spec k` proper, relative to any diagonal open, with `V`
Gorenstein, equidimensional and of dimension one, `K` is the dualizing sheaf `ω_V` placed in
degree `-1`: its cohomology is concentrated in that degree, where it is `ω_V`. -/
theorem nonempty_iso_singleFunctor_dualizingSheafOverField_of_isGorenstein
    {D : v.DiagonalOpen}
    {K : @DerivedCategory (OXMod.{u, u} V.toRingedSpace) _ _ (HasDerivedCategory.standard _)}
    {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    (hK : @Scheme.Hom.IsRelativeDualizingComplex V (Spec (CommRingCat.of k)) v
      (HasDerivedCategory.standard _) (fun _ => HasDerivedCategory.standard _) _ _
      (@RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage (Spec (CommRingCat.of k)).toRingedSpace v.base)
        (fun _ => HasDerivedCategory.standard _)) D K ξ)
    (hG : AlgebraicGeometry.IsGorenstein V) (hequi : TopologicalSpace.Equidimensional V)
    (hdim : topologicalKrullDim V = 1) :
    Nonempty (K ≅ (@DerivedCategory.singleFunctor (OXMod.{u, u} V.toRingedSpace) _ _
      (HasDerivedCategory.standard _) (-1)).obj (dualizingSheafOverField v)) := by
  let := HasDerivedCategory.standard (OXMod.{u, u} V.toRingedSpace)
  have hz := fun j (hj : j ≠ -1) =>
    isZero_homology_of_isRelativeDualizingComplex_of_isGorenstein v hK hG hequi hdim hj
  have : K.IsGE (-1) := (DerivedCategory.isGE_iff K (-1)).2 fun i hi => hz i (by omega)
  have : K.IsLE (-1) := (DerivedCategory.isLE_iff K (-1)).2 fun i hi => hz i (by omega)
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K (-1)
  have e' : Y ≅ dualizingSheafOverField v :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (OXMod.{u, u} V.toRingedSpace)
      (-1)).app Y).symm ≪≫
      (DerivedCategory.homologyFunctor (OXMod.{u, u} V.toRingedSpace) (-1)).mapIso e.symm ≪≫
      (nonempty_homology_neg_one_iso_dualizingSheafOverField_of_isRelativeDualizingComplex v
        hK).some
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor (OXMod.{u, u} V.toRingedSpace) (-1)).mapIso e'⟩

/-- **Syntomic of relative dimension one: the relative dualizing complex has cohomology only in
degree `-1`.** For `v : V ⟶ Spec k` proper and syntomic of relative dimension one with `V`
nonempty, and `(K, ξ)` a relative dualizing complex for `v` relative to any diagonal open,
`H^j(K) = 0` for `j ≠ -1`. -/
theorem isZero_homology_of_isRelativeDualizingComplex_of_syntomicOfRelativeDimension
    {D : v.DiagonalOpen}
    {K : @DerivedCategory (OXMod.{u, u} V.toRingedSpace) _ _ (HasDerivedCategory.standard _)}
    {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    (hK : @Scheme.Hom.IsRelativeDualizingComplex V (Spec (CommRingCat.of k)) v
      (HasDerivedCategory.standard _) (fun _ => HasDerivedCategory.standard _) _ _
      (@RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage (Spec (CommRingCat.of k)).toRingedSpace v.base)
        (fun _ => HasDerivedCategory.standard _)) D K ξ)
    (hv : SyntomicOfRelativeDimension 1 v) [Nonempty V] {j : ℤ} (hj : j ≠ -1) :
    IsZero ((@DerivedCategory.homologyFunctor (OXMod.{u, u} V.toRingedSpace) _ _
      (HasDerivedCategory.standard _) j).obj K) :=
  have h := isGorenstein_equidimensional_dim_one_of_syntomicOfRelativeDimension v hv
  isZero_homology_of_isRelativeDualizingComplex_of_isGorenstein v hK h.1 h.2.1 h.2.2 hj

/-- **Syntomic of relative dimension one: the relative dualizing complex is `ω_V[1]`.** For
`v : V ⟶ Spec k` proper and syntomic of relative dimension one with `V` nonempty, every relative
dualizing complex `(K, ξ)` for `v`, relative to any diagonal open, is isomorphic to `ω_V[1]`. -/
theorem nonempty_iso_singleFunctor_dualizingSheafOverField_of_syntomicOfRelativeDimension
    {D : v.DiagonalOpen}
    {K : @DerivedCategory (OXMod.{u, u} V.toRingedSpace) _ _ (HasDerivedCategory.standard _)}
    {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    (hK : @Scheme.Hom.IsRelativeDualizingComplex V (Spec (CommRingCat.of k)) v
      (HasDerivedCategory.standard _) (fun _ => HasDerivedCategory.standard _) _ _
      (@RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage (Spec (CommRingCat.of k)).toRingedSpace v.base)
        (fun _ => HasDerivedCategory.standard _)) D K ξ)
    (hv : SyntomicOfRelativeDimension 1 v) [Nonempty V] :
    Nonempty (K ≅ (@DerivedCategory.singleFunctor (OXMod.{u, u} V.toRingedSpace) _ _
      (HasDerivedCategory.standard _) (-1)).obj (dualizingSheafOverField v)) :=
  have h := isGorenstein_equidimensional_dim_one_of_syntomicOfRelativeDimension v hv
  nonempty_iso_singleFunctor_dualizingSheafOverField_of_isGorenstein v hK h.1 h.2.1 h.2.2

/-- **At-worst-nodal of relative dimension one: the relative dualizing complex has cohomology
only in degree `-1`.** The case of `AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne` of
`isZero_homology_of_isRelativeDualizingComplex_of_syntomicOfRelativeDimension`. -/
theorem isZero_homology_of_isRelativeDualizingComplex_of_isAtWorstNodalOfRelativeDimensionOne
    {D : v.DiagonalOpen}
    {K : @DerivedCategory (OXMod.{u, u} V.toRingedSpace) _ _ (HasDerivedCategory.standard _)}
    {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    (hK : @Scheme.Hom.IsRelativeDualizingComplex V (Spec (CommRingCat.of k)) v
      (HasDerivedCategory.standard _) (fun _ => HasDerivedCategory.standard _) _ _
      (@RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage (Spec (CommRingCat.of k)).toRingedSpace v.base)
        (fun _ => HasDerivedCategory.standard _)) D K ξ)
    (hv : IsAtWorstNodalOfRelativeDimensionOne v) [Nonempty V] {j : ℤ} (hj : j ≠ -1) :
    IsZero ((@DerivedCategory.homologyFunctor (OXMod.{u, u} V.toRingedSpace) _ _
      (HasDerivedCategory.standard _) j).obj K) :=
  isZero_homology_of_isRelativeDualizingComplex_of_syntomicOfRelativeDimension v hK
    hv.syntomicOfRelativeDimension hj

/-- **At-worst-nodal of relative dimension one: the relative dualizing complex is `ω_V[1]`.**
The case of `AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne` of
`nonempty_iso_singleFunctor_dualizingSheafOverField_of_syntomicOfRelativeDimension`. -/
theorem nonempty_iso_singleFunctor_dualizingSheafOverField_of_isAtWorstNodalOfRelativeDimensionOne
    {D : v.DiagonalOpen}
    {K : @DerivedCategory (OXMod.{u, u} V.toRingedSpace) _ _ (HasDerivedCategory.standard _)}
    {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    (hK : @Scheme.Hom.IsRelativeDualizingComplex V (Spec (CommRingCat.of k)) v
      (HasDerivedCategory.standard _) (fun _ => HasDerivedCategory.standard _) _ _
      (@RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage (Spec (CommRingCat.of k)).toRingedSpace v.base)
        (fun _ => HasDerivedCategory.standard _)) D K ξ)
    (hv : IsAtWorstNodalOfRelativeDimensionOne v) [Nonempty V] :
    Nonempty (K ≅ (@DerivedCategory.singleFunctor (OXMod.{u, u} V.toRingedSpace) _ _
      (HasDerivedCategory.standard _) (-1)).obj (dualizingSheafOverField v)) :=
  nonempty_iso_singleFunctor_dualizingSheafOverField_of_syntomicOfRelativeDimension v hK
    hv.syntomicOfRelativeDimension

end Standard

end Stacks.Duality.CurveFamilyDualizing

end
