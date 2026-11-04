module

public import Mathlib.RingTheory.KrullDimension.Zero
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionGeometricLength
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedMinimalSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionSupportDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators

/-!
# Codimension-zero points in the support are weakly associated

Let `X` be an algebraic space over `S` and `F` an `𝒪_X`-module. A point of `X` of codimension
zero which lies in the support of `F` is weakly associated to `F`: the étale local ring there
has a single prime, so every non-unit is nilpotent and the annihilator of any nonzero element
of the geometric stalk has the maximal ideal as its only prime.

## Main results

* `isWeaklyAssociatedPoint_of_mem_supportOfSheaf_of_localRingDimension_eq_zero`, in the
  namespace `AlgebraicGeometry.Space`, is **Stacks 0CUL**, the first assertion.
* `isWeaklyAssociatedPoint_chartDirectImage_of_localRingDimension_eq_zero` — a codimension-zero
  point of the support of a module on a closed subspace is weakly associated to its direct image.
* `isWeaklyAssociatedPoint_of_localRingDimension_schemeTheoreticSupport_eq_zero` is
  **Stacks 0CUL**, the second assertion, for a quasi-coherent module of finite type.

## Implementation notes

Codimension zero is the vanishing of `AlgebraicGeometry.Space.localRingDimension` of
Stacks 04NA, read on the étale local ring at a geometric point through Stacks 04N9, and the
support is `AlgebraicGeometry.Space.supportOfSheaf` of Stacks 04KA, read on the geometric
stalks through `AlgebraicGeometry.Space.mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk`.
The two are joined by the criterion
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_of_forall_exists_pow_smul_eq_zero`, whose
nilpotency hypothesis is supplied by `Ring.KrullDimLE.isNilpotent_iff_mem_nonunits`; this
replaces the appeal to Stacks 0588 in the source, which produces some weakly associated prime
of a nonzero module and then identifies it with the maximal ideal.

The first assertion is stated for an arbitrary `𝒪_X`-module, whereas the source states it for a
quasi-coherent one; quasi-coherence enters neither the definition of weak association nor the
argument.

The second assertion is reduced to the closed subspace `Z`: the scheme theoretic support is a
closed subspace by `AlgebraicGeometry.Space.exists_isClosedSubspace_schemeTheoreticSupport`,
`F` is the direct image of a quasi-coherent `𝒪_Z`-module `G` by
`AlgebraicGeometry.Space.exists_module_on_schemeTheoreticSupport` (Stacks 07U0), and
`AlgebraicGeometry.Space.modulePushforwardIsoChartDirectImage` identifies that direct image
with `AlgebraicGeometry.Space.chartDirectImage`, for which the stalks are compared. The point
lies in the support of `G` because the support of `F` is the set of points of `Z`
(`AlgebraicGeometry.Space.supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport`) and the
stalks of `F` and `G` correspond.

## References

* [Stacks Project, Tag 0CUL](https://stacks.math.columbia.edu/tag/0CUL)
* [Stacks Project, Tag 0588](https://stacks.math.columbia.edu/tag/0588)
* [Stacks Project, Tag 07U0](https://stacks.math.columbia.edu/tag/07U0)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-- In a local ring of Krull dimension zero, every non-unit is nilpotent. -/
private theorem isNilpotent_of_mem_nonunits_of_ringKrullDim_eq_zero {R : Type*} [CommRing R]
    [IsLocalRing R] (h : ringKrullDim R = 0) {a : R} (ha : a ∈ nonunits R) : IsNilpotent a :=
  have := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr h
  Ring.KrullDimLE.isNilpotent_iff_mem_nonunits.mpr ha

/-- **Stacks 0CUL, the first assertion.** A point of an algebraic space which lies in the
support of an `𝒪_X`-module and has codimension zero, in the sense that the local ring of the
space there has Krull dimension zero, is weakly associated to that module. -/
@[stacks 0CUL "the first assertion, that a codimension-zero point of the support is weakly \
associated, stated for every module in place of a quasi-coherent one"]
theorem isWeaklyAssociatedPoint_of_mem_supportOfSheaf_of_localRingDimension_eq_zero
    (F : Modules.{u, m} B S hS X.1 X.2) (x : points B S hS X.1)
    (hsupp : x ∈ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F))
    (codim : localRingDimension B S hS x = 0) :
    IsWeaklyAssociatedPoint B S hS X F x := by
  obtain ⟨xbar, hxbar, hnt⟩ :=
    (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X F x).mp hsupp
  have := isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
  have hkrull : ∀ y : GeometricPoint B S hS X.1, y.LiesOver x →
      ringKrullDim (etaleLocalRing B S hS X.1 y) = ((0 : ℕ∞) : WithBot ℕ∞) :=
    ((localRingDimension_eq_tfae X.2 x 0).out 1 3).mp codim
  obtain ⟨t, ht⟩ := exists_ne (0 : geometricModuleStalk B S hS X xbar F)
  refine isWeaklyAssociatedPoint_of_forall_exists_pow_smul_eq_zero B S hS X F x xbar hxbar t ht
    fun a ha => (isNilpotent_of_mem_nonunits_of_ringKrullDim_eq_zero
      (by simpa using hkrull xbar hxbar) ha).imp
      fun n hn => by rw [hn, zero_smul]

/-- A point of a closed subspace `Z` of an algebraic space `X` which lies in the support of an
`𝒪_Z`-module `G` and has codimension zero in `Z` has an image in `X` weakly associated to the
direct image of `G`: the germ map `𝒪_{X, x̄} → 𝒪_{Z, z̄}` is surjective, so every non-unit of
`𝒪_{X, x̄}` acts on the stalk `(i_*G)_{x̄} = G_{z̄}` through a nilpotent element. -/
theorem isWeaklyAssociatedPoint_chartDirectImage_of_localRingDimension_eq_zero
    {Z : AlgebraicSpaces B S hS} (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (G : Modules.{u, m} B S hS Z.1 Z.2) (x : points B S hS Z.1)
    (hsupp : x ∈ supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj G))
    (codim : localRingDimension B S hS x = 0) :
    IsWeaklyAssociatedPoint B S hS X (chartDirectImage B S hS i hi G)
      (pointsMap B S hS Z.1 i.hom x) := by
  obtain ⟨zbar, hzbar, hnt⟩ :=
    (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS Z G x).mp hsupp
  have := isLocalRing_etaleLocalRing B S hS Z.1 Z.2 zbar
  have := isLocalRing_etaleLocalRing B S hS X.1 X.2 (geometricPointMap i.hom zbar)
  have hkrull : ∀ y : GeometricPoint B S hS Z.1, y.LiesOver x →
      ringKrullDim (etaleLocalRing B S hS Z.1 y) = ((0 : ℕ∞) : WithBot ℕ∞) :=
    ((localRingDimension_eq_tfae Z.2 x 0).out 1 3).mp codim
  have hlh : IsLocalHom (etaleLocalRingMap Z.2 i.hom zbar) :=
    IsLocalHom.of_surjective _
      (surjective_etaleLocalRingMap_of_isClosedImmersion B S hS i hi zbar)
  obtain ⟨t, ht⟩ := exists_ne (0 : geometricModuleStalk B S hS Z zbar G)
  obtain ⟨t₀, ht₀⟩ := surjective_geometricStalkPushforwardMap B S hS i hi zbar G t
  refine isWeaklyAssociatedPoint_of_forall_exists_pow_smul_eq_zero B S hS X
    (chartDirectImage B S hS i hi G) (pointsMap B S hS Z.1 i.hom x)
    (geometricPointMap i.hom zbar) (congrArg (pointsMap B S hS Z.1 i.hom) hzbar) t₀
    (fun h => ht (by rw [← ht₀, h, map_zero])) fun a ha => ?_
  obtain ⟨n, hn⟩ := isNilpotent_of_mem_nonunits_of_ringKrullDim_eq_zero
    (by simpa using hkrull zbar hzbar)
    (a := etaleLocalRingMap Z.2 i.hom zbar a) fun hu => ha (hlh.map_nonunit a hu)
  refine ⟨n, injective_geometricStalkPushforwardMap B S hS i hi zbar G ?_⟩
  rw [map_zero, geometricStalkPushforwardMap_smul, map_pow, hn, zero_smul]

/-- **Stacks 0CUL, the second assertion.** Let `F` be a quasi-coherent `𝒪_X`-module of finite
type with scheme theoretic support `Z`. A point of `Z` of codimension zero in `Z`, in the sense
that the local ring of `Z` there has Krull dimension zero, has an image in `X` weakly associated
to `F`.

The scheme theoretic support is a closed subspace and `F` is the direct image of a
quasi-coherent module `G` on it, by Stacks 07U0; the direct image of Stacks 03LU along the
closed immersion is the direct image along base change of étale charts. The image of the point
lies in the support of `F`, which is the set of points of `Z`, so the stalk of `G` at a
geometric point above it is nonzero, and the first assertion's argument applies on `Z`. -/
@[stacks 0CUL "the second assertion, for a codimension-zero point of the scheme theoretic \
support of a quasi-coherent module of finite type"]
theorem isWeaklyAssociatedPoint_of_localRingDimension_schemeTheoreticSupport_eq_zero
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    [SheafOfModules.IsFiniteTypeOnSite F]
    (x : points B S hS (schemeTheoreticSupport B S hS X F).toFunctor)
    (codim : localRingDimension B S hS x = 0) :
    IsWeaklyAssociatedPoint B S hS X F
      (pointsMap B S hS (schemeTheoreticSupport B S hS X F).toFunctor
        (schemeTheoreticSupport B S hS X F).ι x) := by
  have hft := Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite F inferInstance
  obtain ⟨hZ, hid⟩ := exists_isClosedSubspace_schemeTheoreticSupport B S hS X F inferInstance hft
  obtain ⟨hZ', G, hGqc, ⟨e⟩⟩ :=
    exists_module_on_schemeTheoreticSupport B S hS X F inferInstance hft
  let i := closedSubspaceInclusion B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩
  let e' : chartDirectImage B S hS i hZ.2 G ≅ F :=
    (modulePushforwardIsoChartDirectImage B S hS i hZ.2 G).symm ≪≫ e
  have : G.IsQuasicoherentOnSite := hGqc
  have : (chartDirectImage B S hS i hZ.2 G).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso e'.symm inferInstance
  obtain ⟨zbar, rfl⟩ := exists_geometricRepresentative B S hS _ x
  have hx : (geometricPointMap i.hom zbar).image ∈ supportOfSheaf B S hS X.1
      ((SheafOfModules.toSheaf _).obj (chartDirectImage B S hS i hZ.2 G)) := by
    rw [supportOfSheaf_eq_of_iso B S hS X e',
      supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B S hS X F inferInstance
        inferInstance]
    exact ⟨zbar.image, rfl⟩
  exact (isWeaklyAssociatedPoint_congr B S hS e' _).mp
    (isWeaklyAssociatedPoint_chartDirectImage_of_localRingDimension_eq_zero B S hS X i hZ.2 G
      zbar.image ((mem_supportOfSheaf_chartDirectImage_iff B S hS i hZ.2 G zbar).1 hx) codim)

end AlgebraicGeometry.Space

end
