module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObject
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Noetherian.CoherentHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Perfect.TorDimensionCertificate
public import StacksFrontier.AlgebraicGeometry.Perfect.TorDimensionCanonicalCertificate
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk
public import StacksFrontier.Topology.Sheaves.Stalk.Restrict
public import Mathlib.RingTheory.DualNumber
public import StacksFrontier.Homology.Perfect.Module
public import StacksFrontier.RingTheory.RegularLocalRing.GlobalDimension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GeneratedByGlobalSections

/-!
# Relative perfectness over a field

Let `k` be a field and let `X` be a scheme of finite presentation over `k`, so that `X` is
Noetherian. This file identifies the objects of `D(𝒪_X)` which are perfect relative to `Spec k`,
in the sense of Stacks 0DI0, with the bounded pseudo-coherent objects, and then — for an object
with quasi-coherent cohomology — with the objects of `D^b_Coh(𝒪_X)`. This is Stacks 0DI1.

The base being a point, the only fibre of `X ⟶ Spec k` is `X` itself; so the example is also the
warning that relative perfectness is *not* perfectness on the fibres, since a bounded complex
with coherent cohomology on a singular `X` need not be perfect. The algebraic form of that
failure is recorded here for the dual numbers; the witness itself is in
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectNotFibrewise`.

Relative perfectness is pseudo-coherence together with locally finite Tor dimension over
`f⁻¹𝒪_{Spec k}`, so the content of the first equivalence is that the second clause is exactly
cohomological boundedness. The mechanism is that every stalk of `f⁻¹𝒪_{Spec k}` is `k`, so every
module on the inverse-image ringed space `(X, f⁻¹𝒪_{Spec k})` is flat and the derived tensor
product is computed degreewise; Tor amplitude is then the cohomological amplitude, uniformly in
the tensor factor, and the structure sheaf being a tensor unit gives the converse. The second
equivalence is Stacks 08E8, the identification of the pseudo-coherent objects of `D_QCoh(𝒪_X)`
with `D⁻_Coh(𝒪_X)` on a Noetherian scheme.

## Main results

* `AlgebraicGeometry.isNoetherian_of_finitePresentation_over_field`: a scheme of finite
  presentation over a field is Noetherian.
* `AlgebraicGeometry.isPerfectRelativeTo_iff_isBounded_and_isPseudoCoherent`: for every family of
  certificates whose underived tensor product is `- ⊗_{f⁻¹𝒪_{Spec k}} -`, an object of `D(𝒪_X)`
  is perfect relative to `Spec k` if and only if it is bounded and pseudo-coherent.
* `AlgebraicGeometry.isBounded_and_isPseudoCoherent_iff_boundedCoherent`: on a Noetherian scheme
  an object of `D(𝒪_X)` is bounded and pseudo-coherent if and only if it lies in
  `D^b_Coh(𝒪_X)`.
* `AlgebraicGeometry.isPerfectRelativeTo_canonical_iff_isBounded_and_isPseudoCoherent`: the first
  equivalence of Stacks 0DI1 — relative perfectness at the derived tensor product of Stacks 06YU
  is boundedness and pseudo-coherence.
* `AlgebraicGeometry.isPerfectRelativeTo_canonical_iff_boundedCoherent`: the example itself, in
  one statement — an object of `D(𝒪_X)` is `Spec k`-perfect
  at the derived tensor product of Stacks 06YU if and only if it lies in `D^b_Coh(𝒪_X)`.
* `AlgebraicGeometry.finitePresentation_dualNumber` and
  `AlgebraicGeometry.not_isPerfectModule_residueField_dualNumber`: the dual numbers `k[ε]` are a
  finitely presented `k`-algebra whose residue field is a finite module which is not perfect.
  This is the singularity that makes the example a warning rather than a tautology: `Spec k[ε]`
  is of finite presentation over `k`, and a finite module on it need not be perfect. The warning
  itself — a `Spec k`-perfect object of `D(𝒪_X)` which is not perfect — is
  `AlgebraicGeometry.isPerfectRelativeTo_dualNumberResidueComplex_and_not_isPerfect`, in
  `StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectNotFibrewise`.

## Implementation notes

As everywhere in `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring`, the derived
tensor product on the inverse-image ringed space enters as a family of certificates indexed by
the opens of that space, since part (3) of Stacks 08CG restricts to an open covering. The first
equivalence is false for an arbitrary family — at
`AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection` the Tor clause
sees only the cohomology of the object, and for a certificate whose underived operation has
unbounded left derived functors a bounded object need not satisfy it — so the quantified form is
stated for families whose underived tensor product is the genuine `- ⊗_{f⁻¹𝒪_{Spec k}} -` of
Stacks 06YU. By `AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_congr` that condition
determines the predicate, since a total left derived functor is unique up to canonical
isomorphism. At `AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily`,
whose underived operation is that tensor product on the nose, the condition holds by `rfl`, and
`AlgebraicGeometry.isPerfectRelativeTo_canonical_iff_boundedCoherent` is the example for an
arbitrary scheme of finite presentation over `k`.

Neither equivalence requires quasi-coherence of the cohomology sheaves, although Stacks 08E8 does:
a pseudo-coherent object has it by Stacks 08E5 and a bounded coherent one by Stacks 01BW.

## References

* [Stacks Project, Example 36.35.2 (Tag 0DI1)](https://stacks.math.columbia.edu/tag/0DI1)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 36.10.3 (Tag 08E8)](https://stacks.math.columbia.edu/tag/08E8)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Lemma 36.10.1 (Tag 08E5)](https://stacks.math.columbia.edu/tag/08E5)
* [Stacks Project, Lemma 17.12.2 (Tag 01BW)](https://stacks.math.columbia.edu/tag/01BW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe d d' u

namespace AlgebraicGeometry

/-! ### Exact functors and cohomological boundedness -/

section Exact

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- Boundedness transfers along any implication between the vanishing of the cohomology of two
objects, with the same bounds. -/
private theorem isBounded_of_isZero_homology {E : DerivedCategory A} {F : DerivedCategory B}
    (h : ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor A i).obj E) →
      IsZero ((DerivedCategory.homologyFunctor B i).obj F))
    (hE : DerivedCategoryB.IsBounded E) : DerivedCategoryB.IsBounded F := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hE
  exact ⟨⟨a, fun i hi => h i (ha i hi)⟩, ⟨b, fun i hi => h i (hb i hi)⟩⟩

/-- An exact additive functor preserves cohomological boundedness, with the same bounds: it
commutes with the cohomology of the derived category. -/
private theorem isBounded_mapDerivedCategory (G : A ⥤ B) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (E : DerivedCategory A)
    (hE : DerivedCategoryB.IsBounded E) :
    DerivedCategoryB.IsBounded (G.mapDerivedCategory.obj E) :=
  isBounded_of_isZero_homology
    (fun i h => (isZero_homology_mapDerivedCategory_iff G E i).2 (Functor.map_isZero G h)) hE

/-- An exact additive functor which reflects zero objects neither creates nor destroys
cohomological boundedness. -/
private theorem isBounded_mapDerivedCategory_iff (G : A ⥤ B) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (hG : ∀ M : A, IsZero (G.obj M) → IsZero M) (E : DerivedCategory A) :
    DerivedCategoryB.IsBounded (G.mapDerivedCategory.obj E) ↔ DerivedCategoryB.IsBounded E := by
  exact ⟨isBounded_of_isZero_homology fun i h =>
    hG _ ((isZero_homology_mapDerivedCategory_iff G E i).1 h), isBounded_mapDerivedCategory G E⟩

end Exact


/-- Restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X` reflects zero objects: it does not change the
underlying sheaf of abelian groups. -/
private theorem isZero_of_isZero_scalarRestriction {X S : Scheme.{u}} (f : X ⟶ S)
    (M : OXMod.{u, u} X.toRingedSpace)
    (hM : IsZero ((Scheme.Hom.scalarRestriction f).obj M)) : IsZero M := by
  refine isZero_of_faithful (SheafOfModules.toSheaf (structureSheafOfRings X.toRingedSpace)) ?_
  exact Functor.map_isZero (SheafOfModules.toSheaf
    (structureSheafOfRings (RingedSpace.inverseImage S.toRingedSpace f.base))) hM

/-- Every point lies in a member of a family of opens whose supremum is the whole space. -/
private theorem exists_mem_of_iSup_eq_top {Z : Type*} [TopologicalSpace Z] {ι : Type*}
    {U : ι → Opens Z} (hU : iSup U = ⊤) (x : Z) : ∃ j, x ∈ U j :=
  Opens.mem_iSup.mp (by rw [hU]; trivial)

/-- A module on a ringed space whose restrictions to the members of an open covering all vanish
is zero: a sheaf vanishes exactly when all of its stalks do, and every point lies in a member of
the covering. -/
private theorem isZero_of_isZero_restrictModules (Z : RingedSpace.{u, u}) {ι : Type u}
    (U : ι → Opens Z.carrier) (hU : iSup U = ⊤) (M : OXMod.{u, u} Z)
    (hM : ∀ j : ι, IsZero ((RingedSpace.restrictModules Z (U j)).obj M)) : IsZero M := by
  refine isZero_of_faithful (SheafOfModules.toSheaf (structureSheafOfRings Z)) ?_
  refine (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).2 fun x => ?_
  obtain ⟨j, hj⟩ := exists_mem_of_iSup_eq_top hU x
  have hz := Functor.map_isZero
    (SheafOfModules.toSheaf (structureSheafOfRings (Z.restrict (U j).isOpenEmbedding))) (hM j)
  have hs := (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).1 hz ⟨x, hj⟩
  exact hs.of_iso (TopCat.Presheaf.stalkRestrictIso (U j) M.val.presheaf ⟨x, hj⟩).symm

/-! ### Ringed spaces whose structure-sheaf stalks are fields -/

section FieldStalks

/-- Every module over a commutative ring which is a field is flat: it is free.

The module structure is an explicit argument, so that the lemma applies to a goal whose module
structure is not the one instance resolution would find. -/
private theorem module_flat_of_isField {R : Type*} [CommRing R] (hR : IsField R)
    (M : Type*) [AddCommGroup M] (inst : Module R M) : Module.Flat R M := by
  let _ := inst
  let _ : Field R := hR.toField
  let _ : Module.Free R M := Module.Free.of_divisionRing R M
  exact Module.Flat.of_free

/-- Every module on a ringed space whose structure-sheaf stalks are fields is flat: flatness is
a stalkwise condition, and every module over a field is free. -/
private theorem isFlat_of_isField_stalks (Z : RingedSpace.{u, u})
    (hZ : ∀ x : Z.carrier, IsField (Z.presheaf.stalk x)) (M : OXMod.{u, u} Z) :
    SheafOfModules.IsFlat.{u, u, u, u} (O := Z.sheaf) M := by
  refine (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat Z.sheaf M).2 fun x => ?_
  exact module_flat_of_isField (hZ x) _ _

/-- The structure sheaf of an open subspace has field stalks as soon as the structure sheaf of
the ambient space does: a stalk of a restricted sheaf is a stalk of the sheaf. -/
private theorem isField_stalk_restrict (Z : RingedSpace.{u, u})
    (hZ : ∀ x : Z.carrier, IsField (Z.presheaf.stalk x)) (U : Opens Z.carrier) (x : U) :
    IsField ((Z.restrict U.isOpenEmbedding).presheaf.stalk x) :=
  (TopCat.Presheaf.stalkRestrictIso U Z.presheaf x).commRingCatIsoToRingEquiv.isField
    (hZ (U.inclusion' x))

/-- The stalk of the inverse image of a sheaf of commutative rings along a continuous map is the
stalk of the sheaf at the image point: the inverse image is the sheafification of the pullback
presheaf, sheafification does not change stalks, and the stalk of the pullback presheaf is the
stalk at the image point. -/
private def stalkPullbackSheafIso {Z W : TopCat.{u}} (g : Z ⟶ W)
    (G : TopCat.Sheaf CommRingCat.{u} W) (x : Z) :
    ((TopCat.Sheaf.pullback CommRingCat.{u} g).obj G).presheaf.stalk x ≅
      G.presheaf.stalk (g x) := by
  let iso1 := (TopCat.Sheaf.forget CommRingCat.{u} Z).mapIso
    ((TopCat.Sheaf.pullbackIso CommRingCat.{u} g).app G)
  refine (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).mapIso iso1 ≪≫ ?_
  have hIso : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology Z)
        ((TopCat.Presheaf.pullback CommRingCat.{u} g).obj G.presheaf))) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x CommRingCat _
  refine (@asIso _ _ _ _ _ hIso).symm ≪≫ ?_
  exact (TopCat.Presheaf.stalkPullbackIso CommRingCat.{u} g G.presheaf x).symm

/-- The structure sheaf of the inverse-image ringed space `(X, f⁻¹𝒪_{Spec k})` of a scheme over
a field has field stalks: the spectrum of a field is a single point whose local ring is the field
itself, and taking inverse images does not change stalks. -/
private theorem isField_stalk_inverseImage (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    IsField
      ((RingedSpace.inverseImage (Spec (.of k)).toRingedSpace f.base).presheaf.stalk x) := by
  let _ : Subsingleton (Spec (.of k)) := inferInstance
  have hp : f.base x = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  have hfield : IsField ((Spec (.of k)).presheaf.stalk (f.base x)) := by
    rw [hp]
    exact (stalkClosedPointIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)
  exact (stalkPullbackSheafIso f.base (Spec (.of k)).toRingedSpace.sheaf
    x).commRingCatIsoToRingEquiv.isField hfield

end FieldStalks

/-! ### Tor amplitude over a ringed space with field stalks -/

section TorAmplitude

/-- **Tor amplitude in `[a, b]` is the vanishing of cohomology outside `[a, b]` when tensoring
is exact and has a unit.**

If every functor `- ⊗_{𝒪_Z} ℱ` is exact then it is its own total left derived functor, so the
derived tensor product is computed degreewise and the vanishing degrees of `E ⊗^{L} ℱ` are those
of `E`, uniformly in `ℱ`. Tensoring with the unit is the identity functor, which gives the
converse. -/
private theorem hasTorAmplitudeIn_iff_isZero_homology (Z : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (OXMod.{u, u} Z)]
    (D : RingedSpace.CertifiedDerivedSheafTensoring.{d, u} Z)
    (hex : ∀ F : OXMod.{u, u} Z, PreservesFiniteLimits (D.tensor.flip.obj F) ∧
      PreservesFiniteColimits (D.tensor.flip.obj F))
    (unit : OXMod.{u, u} Z) (hunit : D.tensor.flip.obj unit ≅ 𝟭 (OXMod.{u, u} Z))
    (E : DerivedCategory (OXMod.{u, u} Z)) (a b : ℤ) :
    D.HasTorAmplitudeIn E a b ↔
      ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Z) i).obj E) := by
  have key : ∀ (F : OXMod.{u, u} Z) (i : ℤ),
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Z) i).obj
          ((D.derivedTensor.obj E).obj
            ((DerivedCategory.singleFunctor (OXMod.{u, u} Z) 0).obj F))) ↔
        IsZero ((D.tensor.flip.obj F).obj
          ((DerivedCategory.homologyFunctor (OXMod.{u, u} Z) i).obj E)) := by
    intro F i
    let _ := D.additive F
    let _ := (hex F).1
    let _ := (hex F).2
    let _ := D.isLeftDerived F
    let _ : ((D.tensor.flip.obj F).mapDerivedCategory).IsLeftDerivedFunctor
        (D.tensor.flip.obj F).mapDerivedCategoryFactors.hom
        (HomologicalComplex.quasiIso (OXMod.{u, u} Z) (ComplexShape.up ℤ)) :=
      Functor.isLeftDerivedFunctor_of_inverts _ _ _
    exact Iff.trans
      (RingedSpace.CertifiedDerivedSheafTensoring.isZero_homology_iff_of_isLeftDerived
        _ _ (D.comparison F) (D.tensor.flip.obj F).mapDerivedCategoryFactors.hom E i)
      (isZero_homology_mapDerivedCategory_iff (D.tensor.flip.obj F) E i)
  constructor
  · intro h i hi
    exact ((key unit i).1 (h _ i hi)).of_iso (hunit.app _).symm
  · intro h F i hi
    let _ := D.additive F
    exact (key F i).2 (Functor.map_isZero _ (h i hi))

/-- **Over a ringed space whose structure-sheaf stalks are fields, finite Tor dimension for the
genuine tensor product is cohomological boundedness.**

Every module is flat, so `- ⊗_{𝒪_Z} ℱ` is exact for every `ℱ`, and the structure sheaf is the
unit of the tensor product. The certificate is pinned by its underived tensor product; by
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.hasFiniteTorDimension_congr` that is
all the pinning finite Tor dimension admits. -/
private theorem hasFiniteTorDimension_iff_isBounded (Z : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (OXMod.{u, u} Z)]
    (hZ : ∀ x : Z.carrier, IsField (Z.presheaf.stalk x))
    (D : RingedSpace.CertifiedDerivedSheafTensoring.{d, u} Z)
    (hD : D.tensor = Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf)
    (E : DerivedCategory (OXMod.{u, u} Z)) :
    D.HasFiniteTorDimension E ↔ DerivedCategoryB.IsBounded E := by
  have hex : ∀ F : OXMod.{u, u} Z, PreservesFiniteLimits (D.tensor.flip.obj F) ∧
      PreservesFiniteColimits (D.tensor.flip.obj F) := by
    intro F
    rw [← exactFunctor_iff, hD]
    exact Stacks.SheafOfModules.exactFunctor_sheafTensorFlip_of_isFlat Z.sheaf F
      (isFlat_of_isField_stalks Z hZ F)
  have hunit : D.tensor.flip.obj
      (Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.structureSheafModule Z) ≅
      𝟭 (OXMod.{u, u} Z) := by
    rw [hD]
    exact Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.tensorStructureSheafIso Z
  constructor
  · rintro ⟨a, b, hab⟩
    rw [hasTorAmplitudeIn_iff_isZero_homology Z D hex _ hunit E a b] at hab
    exact ⟨⟨a, fun i hi => hab i (by simp only [Set.mem_Icc]; omega)⟩,
      ⟨b, fun i hi => hab i (by simp only [Set.mem_Icc]; omega)⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨a, b, (hasTorAmplitudeIn_iff_isZero_homology Z D hex _ hunit E a b).2 fun i hi => ?_⟩
    simp only [Set.mem_Icc, not_and_or, not_le] at hi
    rcases hi with hi | hi
    · exact ha i hi
    · exact hb i hi

/-- **On a quasi-compact ringed space whose structure-sheaf stalks are fields, locally finite Tor
dimension is cohomological boundedness.**

Over each member of a covering, finite Tor dimension of the restriction is boundedness of the
restriction, by `AlgebraicGeometry.hasFiniteTorDimension_iff_isBounded`. Quasi-compactness
extracts a finite subcovering, over which the finitely many pairs of bounds have a minimum and a
maximum, and a module whose restrictions to a covering vanish is zero. Conversely the covering by
all the opens works, since restriction to an open subspace is exact. -/
private theorem locallyHasFiniteTorDimension_iff_isBounded (Z : RingedSpace.{u, u})
    [CompactSpace Z.carrier] [HasDerivedCategory.{d} (OXMod.{u, u} Z)]
    [∀ U : Opens Z.carrier, HasDerivedCategory.{d'} (OXMod.{u, u} (Z.restrict U.isOpenEmbedding))]
    (hZ : ∀ x : Z.carrier, IsField (Z.presheaf.stalk x))
    (D : ∀ U : Opens Z.carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d', u} (Z.restrict U.isOpenEmbedding))
    (hD : ∀ U : Opens Z.carrier, (D U).tensor =
      Stacks.SheafOfModules.Tensor.sheafTensor (Z.restrict U.isOpenEmbedding).sheaf)
    (E : DerivedCategory (OXMod.{u, u} Z)) :
    RingedSpace.LocallyHasFiniteTorDimension Z D E ↔ DerivedCategoryB.IsBounded E := by
  classical
  have hloc : ∀ U : Opens Z.carrier,
      (D U).HasFiniteTorDimension ((RingedSpace.derivedRestrictModules Z U).obj E) ↔
        DerivedCategoryB.IsBounded ((RingedSpace.derivedRestrictModules Z U).obj E) := fun U =>
    hasFiniteTorDimension_iff_isBounded _ (isField_stalk_restrict Z hZ U) (D U) (hD U) _
  constructor
  · rintro ⟨I, U, hU, hTor⟩
    have hb : ∀ j : I, ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((RingedSpace.restrictModules Z (U j)).obj
          ((DerivedCategory.homologyFunctor (OXMod.{u, u} Z) i).obj E)) := by
      intro j
      obtain ⟨⟨a, ha⟩, ⟨b, hbb⟩⟩ := (hloc (U j)).1 (hTor j)
      refine ⟨a, b, fun i hi => ?_⟩
      refine (isZero_homology_mapDerivedCategory_iff
        (RingedSpace.restrictModules Z (U j)) E i).1 ?_
      rcases hi with hi | hi
      · exact ha i hi
      · exact hbb i hi
    choose a b hab using hb
    have hcov : (Set.univ : Set Z.carrier) ⊆ ⋃ j : I, (U j : Set Z.carrier) := by
      intro x _
      obtain ⟨j, hj⟩ := exists_mem_of_iSup_eq_top hU x
      exact Set.mem_iUnion.2 ⟨j, hj⟩
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
      (fun j : I => (U j : Set Z.carrier)) (fun j => (U j).isOpen) hcov
    have hsub : (iSup fun j : { j : I // j ∈ s } => U j.1) = ⊤ := by
      refine eq_top_iff.mpr fun x _ => ?_
      obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
      exact Opens.mem_iSup.mpr ⟨⟨j, hj⟩, hx⟩
    obtain ⟨lo, hlo⟩ := (Set.finite_range fun j : { j : I // j ∈ s } => a j.1).bddBelow
    obtain ⟨up, hup⟩ := (Set.finite_range fun j : { j : I // j ∈ s } => b j.1).bddAbove
    refine ⟨⟨lo, fun i hi => ?_⟩, ⟨up, fun i hi => ?_⟩⟩
    · exact isZero_of_isZero_restrictModules Z (fun j : { j : I // j ∈ s } => U j.1) hsub _
        fun j => hab j.1 i (Or.inl (lt_of_lt_of_le hi (hlo (Set.mem_range_self j))))
    · exact isZero_of_isZero_restrictModules Z (fun j : { j : I // j ∈ s } => U j.1) hsub _
        fun j => hab j.1 i (Or.inr (lt_of_le_of_lt (hup (Set.mem_range_self j)) hi))
  · intro hE
    exact ⟨Opens Z.carrier, id, le_antisymm le_top (le_iSup (fun U : Opens Z.carrier => U) ⊤),
      fun U => (hloc U).2 (isBounded_mapDerivedCategory _ E hE)⟩

end TorAmplitude

/-! ### Relative perfectness over a field -/

/-- A scheme of finite presentation over a field is Noetherian: it is of finite type over a
Noetherian scheme, hence locally Noetherian, and quasi-compact over a quasi-compact base, hence
quasi-compact. -/
public theorem isNoetherian_of_finitePresentation_over_field (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFinitePresentation f] [QuasiCompact f] :
    IsNoetherian X := by
  let _ : LocallyOfFiniteType f := inferInstance
  let _ : IsLocallyNoetherian (Spec (.of k)) := inferInstance
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : CompactSpace (Spec (.of k)) := inferInstance
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact {}

section Objective

attribute [local instance] HasDerivedCategory.standard

/-- Let `k` be a field and let `X` be a scheme of finite presentation over `k`. For every family
`D` of Stacks 08CG certificates on the open subspaces of `(X, f⁻¹𝒪_{Spec k})` whose underived
tensor product is `- ⊗_{f⁻¹𝒪_{Spec k}} -`, an object `E` of `D(𝒪_X)` is perfect relative to
`Spec k` at `D` if and only if it is bounded and pseudo-coherent.

Pseudo-coherence is the first clause of relative perfectness on both sides, so the content is
that the second clause — locally finite Tor dimension of `E` over `f⁻¹𝒪_{Spec k}` — is exactly
cohomological boundedness. Over a field every stalk of `f⁻¹𝒪_{Spec k}` is a field, so every
module on the inverse-image ringed space is flat, tensoring is exact, and the Tor amplitude of an
object collapses to its cohomological amplitude; the structure sheaf is a tensor unit, which
gives the other direction. Quasi-compactness of `X` turns the bounds supplied on the members of a
covering into one pair of bounds, and restriction of scalars along `f⁻¹𝒪_{Spec k} ⟶ 𝒪_X` is exact
and reflects zero objects, which transports boundedness in both directions.

By `AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_congr` the underived tensor
product determines the predicate. At the derived tensor product of Stacks 06YU this is
`AlgebraicGeometry.isPerfectRelativeTo_canonical_iff_isBounded_and_isPseudoCoherent`. -/
public theorem isPerfectRelativeTo_iff_isBounded_and_isPseudoCoherent (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFinitePresentation f] [QuasiCompact f]
    (D : ∀ U : Opens (RingedSpace.inverseImage (Spec (.of k)).toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (.of k)).toRingedSpace f.base).restrict
          U.isOpenEmbedding))
    (hD : ∀ U : Opens (RingedSpace.inverseImage (Spec (.of k)).toRingedSpace f.base).carrier,
      (D U).tensor = Stacks.SheafOfModules.Tensor.sheafTensor
        ((RingedSpace.inverseImage (Spec (.of k)).toRingedSpace f.base).restrict
          U.isOpenEmbedding).sheaf)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    f.IsPerfectRelativeTo D E ↔
      (DerivedCategoryB.IsBounded E ∧ RingedSpace.IsPseudoCoherent E) := by
  let _ : CompactSpace (Spec (.of k)) := inferInstance
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let _ : CompactSpace
      (RingedSpace.inverseImage (Spec (.of k)).toRingedSpace f.base).carrier :=
    inferInstanceAs (CompactSpace X)
  have key : RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage (Spec (.of k)).toRingedSpace f.base) D
      ((Scheme.Hom.derivedScalarRestriction f).obj E) ↔ DerivedCategoryB.IsBounded E :=
    (locallyHasFiniteTorDimension_iff_isBounded _ (isField_stalk_inverseImage k f) D hD _).trans
      (isBounded_mapDerivedCategory_iff (Scheme.Hom.scalarRestriction f)
        (fun M hM => isZero_of_isZero_scalarRestriction f M hM) E)
  exact ⟨fun h => ⟨key.1 h.2, h.1⟩, fun h => ⟨h.2, key.2 h.1⟩⟩

/-- **Stacks 0DI1, second equivalence, via Stacks 08E8.** On a Noetherian scheme an object of
`D(𝒪_X)` is bounded and pseudo-coherent if and only if it lies in `D^b_Coh(𝒪_X)`, that is,
if and only if it is bounded and all of its cohomology sheaves are coherent.

Together with
`AlgebraicGeometry.isPerfectRelativeTo_canonical_iff_isBounded_and_isPseudoCoherent` and
`AlgebraicGeometry.isNoetherian_of_finitePresentation_over_field` this identifies the objects of
`D(𝒪_X)` perfect relative to a field with `D^b_Coh(𝒪_X)`; see
`AlgebraicGeometry.isPerfectRelativeTo_canonical_iff_boundedCoherent`.

Stacks 08E8 cuts `D^b_Coh(𝒪_X)` out inside `D_QCoh(𝒪_X)`, and both sides here
imply quasi-coherence of the cohomology sheaves: on the left it is Stacks 08E5 for a pseudo-coherent
object,
`AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent`, and on the right it is Stacks
01BW, `isQuasicoherent_of_isCoherent`, applied degreewise. -/
@[stacks 0DI1 "bounded pseudo-coherent objects are the bounded coherent ones"]
public theorem isBounded_and_isPseudoCoherent_iff_boundedCoherent (X : Scheme.{u})
    [IsNoetherian X] (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    (DerivedCategoryB.IsBounded E ∧ RingedSpace.IsPseudoCoherent E) ↔
      DerivedCategoryB.derivedCategoryBBounded
        (fun M : OXMod.{u, u} X.toRingedSpace => M.IsCoherent) E := by
  have main : ∀ hqc : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent,
      (DerivedCategoryB.IsBounded E ∧ RingedSpace.IsPseudoCoherent E) ↔
        DerivedCategoryB.derivedCategoryBBounded
          (fun M : OXMod.{u, u} X.toRingedSpace => M.IsCoherent) E := by
    intro hqc
    let E' : (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory := ⟨E, hqc⟩
    constructor
    · rintro ⟨hb, hpc⟩
      exact ⟨hb, fun i =>
        ((isPseudoCoherent_iff_boundedAbove_coherent_homology X E').1 hpc).2 i⟩
    · rintro ⟨hb, hcoh⟩
      exact ⟨hb, (isPseudoCoherent_iff_boundedAbove_coherent_homology X E').2 ⟨hb.2, hcoh⟩⟩
  constructor
  · rintro ⟨hb, hpc⟩
    exact (main (isQuasicoherentDerived_of_isPseudoCoherent X E hpc)).1 ⟨hb, hpc⟩
  · rintro ⟨hb, hcoh⟩
    refine (main fun i => ?_).2 ⟨hb, hcoh⟩
    have hci : SheafOfModules.IsCoherent
        ((DerivedCategory.homologyFunctor X.Modules i).obj E) := hcoh i
    exact isQuasicoherent_of_isCoherent _

/-! ### The example at the genuine derived tensor product -/

/-- **Stacks 0DI1, first equivalence, at the genuine derived tensor product.** Let `k` be a field
and let `X` be a scheme of finite presentation over `k`. An object `E` of `D(𝒪_X)` is perfect
relative to `Spec k` — read at the derived tensor product of Stacks 06YU on each open subspace of
`(X, f⁻¹𝒪_{Spec k})`, which is
`AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily` — if and only if it
is bounded and pseudo-coherent.

This is `AlgebraicGeometry.isPerfectRelativeTo_iff_isBounded_and_isPseudoCoherent` at the
canonical family, whose underived operation *is* `- ⊗_{f⁻¹𝒪_{Spec k}} -` by `rfl`. -/
@[stacks 0DI1
  "first equivalence: at the 06YU derived tensor product, relative perfectness over a field is
  boundedness and pseudo-coherence"]
public theorem isPerfectRelativeTo_canonical_iff_isBounded_and_isPseudoCoherent (k : Type u)
    [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFinitePresentation f]
    [QuasiCompact f] (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    f.IsPerfectRelativeTo
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage (Spec (.of k)).toRingedSpace f.base)) E ↔
      (DerivedCategoryB.IsBounded E ∧ RingedSpace.IsPseudoCoherent E) :=
  isPerfectRelativeTo_iff_isBounded_and_isPseudoCoherent k f _ (fun _ => rfl) E

/-- **Stacks 0DI1.** Let `k` be a field and let `X` be a scheme of finite presentation over `k`.
An object `E` of `D(𝒪_X)` is `Spec k`-perfect if and only if it lies in `D^b_Coh(𝒪_X)`, that is,
if and only if it is bounded with coherent cohomology sheaves.

This is the example in one statement: relative perfectness is read at the derived tensor product
of Stacks 06YU, and the cohomology sheaves are quasi-coherent by Stacks 08E5 and 01BW. It is the
composite of
`AlgebraicGeometry.isPerfectRelativeTo_canonical_iff_isBounded_and_isPseudoCoherent` with
`AlgebraicGeometry.isBounded_and_isPseudoCoherent_iff_boundedCoherent`, the scheme being
Noetherian by `AlgebraicGeometry.isNoetherian_of_finitePresentation_over_field`. -/
@[stacks 0DI1 "the `Spec k`-perfect objects are exactly `D^b_Coh(𝒪_X)`"]
public theorem isPerfectRelativeTo_canonical_iff_boundedCoherent (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFinitePresentation f] [QuasiCompact f]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    f.IsPerfectRelativeTo
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage (Spec (.of k)).toRingedSpace f.base)) E ↔
      DerivedCategoryB.derivedCategoryBBounded
        (fun M : OXMod.{u, u} X.toRingedSpace => M.IsCoherent) E :=
  have : IsNoetherian X := isNoetherian_of_finitePresentation_over_field k f
  (isPerfectRelativeTo_canonical_iff_isBounded_and_isPseudoCoherent k f E).trans
    (isBounded_and_isPseudoCoherent_iff_boundedCoherent X E)

end Objective

/-! ### The singularity behind the example -/

section Singular

attribute [local instance] HasDerivedCategory.standard

/-- A perfect finite module over a Noetherian ring has finite projective dimension: a finite
projective resolution of finite length is a resolution by finite projectives. -/
private theorem projectiveDimension_ne_top_of_isPerfectModule {R : Type u} [CommRing R]
    [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : StacksDraft.Perfect.IsPerfectModule (R := R) M) :
    projectiveDimension (ModuleCat.of R M) ≠ ⊤ := by
  obtain ⟨d, F, hF, hzero⟩ :=
    (StacksDraft.Perfect.isPerfectModule_iff_exists_finite_projective_resolution M).mp hM
  rw [projectiveDimension_ne_top_iff]
  let G : ObjectProperty.LeftResolution
      (fun N : ModuleCat.{u} R => Projective N ∧ Module.Finite R N)
      (ModuleCat.of R M) :=
    { complex := F.complex
      property := fun i => ⟨(IsProjective.iff_projective _).mp (hF i).2, (hF i).1⟩
      π := F.π
      quasiIso := F.quasiIso }
  refine ⟨d, (ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_projective_finite
    (ModuleCat.of R M) d).mpr ⟨G, ?_⟩⟩
  simpa [G] using hzero

/-- The dual numbers over a field are a finitely presented algebra: they are free of rank two,
hence of finite type, and a finite algebra of finite type over a field is finitely presented. -/
public theorem finitePresentation_dualNumber (k : Type u) [Field k] :
    Algebra.FinitePresentation k (DualNumber k) := by
  let e : (k × k) ≃ₗ[k] DualNumber k :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => (x.fst, x.snd)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let _ : Module.Finite k (DualNumber k) := Module.Finite.equiv e
  exact Algebra.FinitePresentation.of_finiteType.mp inferInstance

/-- **The residue field of the dual numbers is not a perfect module.**

The dual numbers `k[ε]` are a local ring with nilpotent maximal ideal `(ε)`, and the residue
field is a finite module over them. Were it perfect it would have finite projective dimension,
so `k[ε]` would be a regular local ring and hence a domain, contradicting `ε² = 0` and `ε ≠ 0`.

This is the singularity underlying Stacks 0DI1: `Spec k[ε]` is a scheme of finite presentation
over `k` carrying a finite module which is not perfect, so bounded coherent complexes on a
singular scheme need not be perfect. -/
public theorem not_isPerfectModule_residueField_dualNumber (k : Type u) [Field k] :
    ¬ StacksDraft.Perfect.IsPerfectModule (R := DualNumber k)
      (IsLocalRing.ResidueField (DualNumber k)) := by
  intro h
  have hp := projectiveDimension_ne_top_of_isPerfectModule _ h
  have hreg : IsRegularLocalRing (DualNumber k) :=
    ((isRegularLocalRing_tfae (R := DualNumber k)).out 1 3).mp hp
  let _ := hreg
  let _ : IsDomain (DualNumber k) := IsRegularLocalRing.isDomain _
  have hnil : IsNilpotent (DualNumber.eps : DualNumber k) := ⟨2, by simp⟩
  exact one_ne_zero (congrArg TrivSqZeroExt.snd hnil.eq_zero)

end Singular

end AlgebraicGeometry

end
