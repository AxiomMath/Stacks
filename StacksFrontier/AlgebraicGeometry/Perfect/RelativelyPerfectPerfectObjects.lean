module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectTriangulated
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.TensorProduct
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension

/-!
# Perfect objects are perfect relative to the base, and tensoring preserves relative perfectness

Let `f : X ⟶ S` be a morphism of schemes which is flat and locally of finite presentation. Then
every perfect object of `D(𝒪_X)` is `S`-perfect in the sense of Stacks 0DI0, and the derived
tensor product of a perfect object with an `S`-perfect object is `S`-perfect. This is
Stacks 0DI4.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.inverseImageRingToStructureOpen` is the map of sheaves of rings
  `f⁻¹𝒪_S|_V ⟶ 𝒪_X|_V` on an open subspace.
* `AlgebraicGeometry.Scheme.Hom.scalarRestrictionOpen` is restriction of scalars along it.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_isPerfect` (Stacks 0DI4, first
  assertion): a perfect object of `D(𝒪_X)` is perfect relative to `S`.
* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_derivedTensor` (Stacks 0DI4, second
  assertion): the derived tensor product of Stacks 06YU of a perfect object with an `S`-perfect
  object is perfect relative to `S`.

## Implementation notes

The derived tensor product on the inverse-image ringed space is a family `D` of certificates
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring` indexed by the opens of that
space, as part (3) of Stacks 08CG restricts to an open covering. The properties of the genuine
derived tensor product that the two assertions use are hypotheses:

* `hamp`, the easy direction of Tag 08CI for the family: a complex of flat modules concentrated
  in `[a, b]` represents an object of Tor amplitude in `[a, b]`;
* `commShift` and `triangulated`, exactness of each `- ⊗^{L} ℱ[0]`, and
  `AlgebraicGeometry.RingedSpace.FiniteTorDimensionRestricts`, locality of finite Tor dimension.

Flatness of `f` enters through `hflat`: the restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X` of a
direct summand of a finite free `𝒪_X`-module is a flat `f⁻¹𝒪_S`-module.

The derived tensor product in the second assertion is
`Stacks.Cohomology.PseudoCoherentTensor.derivedTensorProduct` of Stacks 06YU. Its
pseudo-coherence clause is Tag 09J3, granted the complex level of that tag as the hypothesis
`hcl`. Its interaction with restriction to open subspaces is the datum `Θ`: for `V ⊆ W` a
triangulated functor computing `(E|_W ⊗^{L} M)|_V` over `f⁻¹𝒪_S`, with `Θunit` saying that the
structure sheaf is the unit and `Θtensor` that the construction is the restriction of
`- ⊗^{L} M`. The triangulated induction over a strictly perfect complex,
`AlgebraicGeometry.Scheme.Hom.StrictlyPerfectInduction`, is the hypothesis `hind`.

## References

* [Stacks Project, Lemma 36.35.5 (Tag 0DI4)](https://stacks.math.columbia.edu/tag/0DI4)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 36.35.4 (Tag 0DI3)](https://stacks.math.columbia.edu/tag/0DI3)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Lemma 20.48.5 (Tag 08CI)](https://stacks.math.columbia.edu/tag/08CI)
* [Stacks Project, Lemma 20.47.5 (Tag 09J3)](https://stacks.math.columbia.edu/tag/09J3)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
  StrictlyPerfect

universe d d' u

namespace AlgebraicGeometry

/-! ### Finite Tor dimension at a single certificate -/

namespace RingedSpace.CertifiedDerivedSheafTensoring

variable {Z : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u, u} Z)]
  (C : CertifiedDerivedSheafTensoring.{d, u} Z)

/-- Widening the interval weakens Tor amplitude. -/
private theorem hasTorAmplitudeIn_mono' (E : DerivedCategory (OXMod.{u, u} Z)) {a b a' b' : ℤ}
    (ha : a' ≤ a) (hb : b ≤ b') (h : C.HasTorAmplitudeIn E a b) :
    C.HasTorAmplitudeIn E a' b' := by
  intro F i hi
  refine h F i ?_
  simp only [Set.mem_Icc, not_and, not_le] at hi ⊢
  omega

/-- Finite Tor dimension only depends on the isomorphism class of the object. -/
private theorem hasFiniteTorDimension_of_iso' {E E' : DerivedCategory (OXMod.{u, u} Z)}
    (e : E ≅ E') (h : C.HasFiniteTorDimension E) : C.HasFiniteTorDimension E' := by
  obtain ⟨a, b, h⟩ := h
  exact ⟨a, b, fun F i hi => (h F i hi).of_iso
    ((DerivedCategory.homologyFunctor (OXMod.{u, u} Z) i).mapIso
      ((C.derivedTensor.mapIso e).app
        ((DerivedCategory.singleFunctor (OXMod.{u, u} Z) 0).obj F))).symm⟩

/-- **Stacks 08CK for a retract.** A retract of an object of finite Tor dimension has finite Tor
dimension, with the same interval. -/
private theorem hasFiniteTorDimension_of_retract' {A B : DerivedCategory (OXMod.{u, u} Z)}
    (i : A ⟶ B) (r : B ⟶ A) (hir : i ≫ r = 𝟙 A) (h : C.HasFiniteTorDimension B) :
    C.HasFiniteTorDimension A := by
  obtain ⟨a, b, h⟩ := h
  exact ⟨a, b, fun F j hj => Stacks.Cohomology.TorAmplitude.isZero_obj_of_retract
    (C.derivedTensor.flip.obj ((DerivedCategory.singleFunctor (OXMod.{u, u} Z) 0).obj F) ⋙
      DerivedCategory.homologyFunctor (OXMod.{u, u} Z) j) i r hir (h F j hj)⟩

variable
  (commShift : ∀ F : OXMod.{u, u} Z,
    (C.derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Z) 0).obj F)).CommShift ℤ)
  (triangulated : ∀ F : OXMod.{u, u} Z, letI := commShift F;
    (C.derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Z) 0).obj F)).IsTriangulated)

include commShift triangulated in
/-- **Stacks 08CJ.** Tor amplitude propagates in a distinguished triangle. -/
private theorem hasTorAmplitudeIn_of_distinguished'
    (T : Triangle (DerivedCategory (OXMod.{u, u} Z))) (hT : T ∈ distinguishedTriangles)
    (a b : ℤ) :
    (C.HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1) → C.HasTorAmplitudeIn T.obj₂ a b →
        C.HasTorAmplitudeIn T.obj₃ a b) ∧
      (C.HasTorAmplitudeIn T.obj₂ (a + 1) (b + 1) → C.HasTorAmplitudeIn T.obj₃ a b →
        C.HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1)) := by
  have key (F : OXMod.{u, u} Z) :
      (C.derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (OXMod.{u, u} Z) 0).obj F)).mapTriangle.obj T ∈
          distinguishedTriangles := by
    let _ := commShift F
    let _ := triangulated F
    exact Functor.map_distinguished _ T hT
  refine ⟨fun h₁ h₂ F i hi => ?_, fun h₂ h₃ F i hi => ?_⟩
  · have hex := DerivedCategory.HomologySequence.exact₃ _ (key F) i (i + 1) rfl
    refine hex.isZero_of_both_zeros ((h₂ F i hi).eq_zero_of_src _)
      ((h₁ F (i + 1) ?_).eq_zero_of_tgt _)
    simp only [Set.mem_Icc, not_and, not_le] at hi ⊢
    omega
  · have hex := DerivedCategory.HomologySequence.exact₁ _ (key F) (i - 1) i (by omega)
    refine hex.isZero_of_both_zeros ((h₃ F (i - 1) ?_).eq_zero_of_src _)
      ((h₂ F i hi).eq_zero_of_tgt _)
    simp only [Set.mem_Icc, not_and, not_le] at hi ⊢
    omega

include commShift triangulated in
/-- **Stacks 08CJ** for finite Tor dimension: the first and third two-out-of-three rules in a
distinguished triangle, with the intervals widened to a common one. -/
private theorem hasFiniteTorDimension_of_distinguished'
    (T : Triangle (DerivedCategory (OXMod.{u, u} Z))) (hT : T ∈ distinguishedTriangles) :
    (C.HasFiniteTorDimension T.obj₁ → C.HasFiniteTorDimension T.obj₂ →
        C.HasFiniteTorDimension T.obj₃) ∧
      (C.HasFiniteTorDimension T.obj₂ → C.HasFiniteTorDimension T.obj₃ →
        C.HasFiniteTorDimension T.obj₁) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨a₁, b₁, h₁⟩ ⟨a₂, b₂, h₂⟩
    exact ⟨min (a₁ - 1) a₂, max (b₁ - 1) b₂,
      (hasTorAmplitudeIn_of_distinguished' C commShift triangulated T hT _ _).1
        (hasTorAmplitudeIn_mono' C _ (by omega) (by omega) h₁)
        (hasTorAmplitudeIn_mono' C _ (min_le_right ..) (le_max_right ..) h₂)⟩
  · rintro ⟨a₂, b₂, h₂⟩ ⟨a₃, b₃, h₃⟩
    exact ⟨min (a₂ - 1) a₃ + 1, max (b₂ - 1) b₃ + 1,
      (hasTorAmplitudeIn_of_distinguished' C commShift triangulated T hT _ _).2
        (hasTorAmplitudeIn_mono' C _ (by omega) (by omega) h₂)
        (hasTorAmplitudeIn_mono' C _ (min_le_right ..) (le_max_right ..) h₃)⟩

include commShift triangulated in
/-- A zero object has finite Tor dimension. -/
private theorem hasFiniteTorDimension_of_isZero' {E : DerivedCategory (OXMod.{u, u} Z)}
    (hE : IsZero E) : C.HasFiniteTorDimension E := by
  refine ⟨0, 0, fun F i _ => ?_⟩
  let _ := commShift F
  let _ := triangulated F
  exact (DerivedCategory.homologyFunctor (OXMod.{u, u} Z) i).map_isZero
    ((C.derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Z) 0).obj F)).map_isZero hE)

end RingedSpace.CertifiedDerivedSheafTensoring

/-! ### Restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X` over an open subspace -/

namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The map of sheaves of rings `f⁻¹𝒪_S|_V ⟶ 𝒪_X|_V` over an open subspace `V`: the map
`AlgebraicGeometry.Scheme.Hom.inverseImageRingToStructure` of `f⁻¹𝒪_S ⟶ 𝒪_X`, read on the opens
contained in `V`. -/
public def inverseImageRingToStructureOpen (V : TopologicalSpace.Opens
    (RingedSpace.inverseImage S.toRingedSpace f.base).carrier) :
    structureSheafOfRings.{u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict V.isOpenEmbedding) ⟶
      structureSheafOfRings.{u} (X.toRingedSpace.restrict V.isOpenEmbedding) :=
  ObjectProperty.homMk
    (Functor.whiskerLeft V.isOpenEmbedding.functor.op (inverseImageRingToStructure f).hom)

/-- **Restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X` over an open subspace `V`**,
`Mod(𝒪_X|_V) ⥤ Mod(f⁻¹𝒪_S|_V)`: an `𝒪_X|_V`-module regarded as a module over the inverse image
of the structure sheaf of the base. The underlying sheaf of abelian groups is unchanged. -/
public def scalarRestrictionOpen (V : TopologicalSpace.Opens
    (RingedSpace.inverseImage S.toRingedSpace f.base).carrier) :
    OXMod.{u, u} (X.toRingedSpace.restrict V.isOpenEmbedding) ⥤
      OXMod.{u, u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict V.isOpenEmbedding) :=
  SheafOfModules.restrictScalars (inverseImageRingToStructureOpen f V)

/-- Restriction of scalars over an open subspace is additive. -/
public instance additive_scalarRestrictionOpen (V : TopologicalSpace.Opens
    (RingedSpace.inverseImage S.toRingedSpace f.base).carrier) :
    (scalarRestrictionOpen f V).Additive :=
  RingedSpace.additive_restrictScalars (X.toRingedSpace.restrict V.isOpenEmbedding)
    (inverseImageRingToStructureOpen f V)

/-- **Restriction of scalars over an open subspace is exact.** -/
public theorem exactFunctor_scalarRestrictionOpen (V : TopologicalSpace.Opens
    (RingedSpace.inverseImage S.toRingedSpace f.base).carrier) :
    PreservesFiniteLimits (scalarRestrictionOpen f V) ∧
      PreservesFiniteColimits (scalarRestrictionOpen f V) :=
  RingedSpace.exactFunctor_restrictScalars (X.toRingedSpace.restrict V.isOpenEmbedding)
    (inverseImageRingToStructureOpen f V)
    (RingedSpace.preservesFiniteColimits_toSheaf
      ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict V.isOpenEmbedding))

/-- Restriction of scalars over an open subspace is left exact. -/
public instance preservesFiniteLimits_scalarRestrictionOpen (V : TopologicalSpace.Opens
    (RingedSpace.inverseImage S.toRingedSpace f.base).carrier) :
    PreservesFiniteLimits (scalarRestrictionOpen f V) :=
  (exactFunctor_scalarRestrictionOpen f V).1

/-- Restriction of scalars over an open subspace is right exact. -/
public instance preservesFiniteColimits_scalarRestrictionOpen (V : TopologicalSpace.Opens
    (RingedSpace.inverseImage S.toRingedSpace f.base).carrier) :
    PreservesFiniteColimits (scalarRestrictionOpen f V) :=
  (exactFunctor_scalarRestrictionOpen f V).2

/-! ### Stacks 0DI4 -/

section Objective

variable
  [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]
  [HasDerivedCategory.{d'} (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base))]
  [hdc : ∀ U : TopologicalSpace.Opens
      (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    HasDerivedCategory.{d'}
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        U.isOpenEmbedding))]
  [hdcX : ∀ U : TopologicalSpace.Opens X.toRingedSpace.carrier,
    HasDerivedCategory.{d'} (OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding))]
  [Flat f] [LocallyOfFinitePresentation f]
  (D : ∀ U : TopologicalSpace.Opens
      (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
      ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))

/-- Tag 08CI's easy direction for the family `D`: a complex of flat modules concentrated in
`[a, b]` represents an object of Tor amplitude in `[a, b]`. -/
public def FlatRepresentativeBounds : Prop :=
  ∀ (V : TopologicalSpace.Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier)
      (K : CochainComplex (OXMod.{u, u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict V.isOpenEmbedding)) ℤ)
      (a b : ℤ),
    (∀ j : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        V.isOpenEmbedding).sheaf) (K.X j)) →
    (∀ j : ℤ, j ∉ Set.Icc a b → IsZero (K.X j)) →
    ∀ E : DerivedCategory (OXMod.{u, u}
      ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict V.isOpenEmbedding)),
      (DerivedCategory.Q.obj K ≅ E) → (D V).HasTorAmplitudeIn E a b

/-- The sheaf-level content of flatness of `f`: the restriction of scalars along
`f⁻¹𝒪_S ⟶ 𝒪_X` of a direct summand of a finite free `𝒪_X`-module is a flat `f⁻¹𝒪_S`-module,
over every open subspace. -/
public def ScalarRestrictionFlat : Prop :=
  ∀ (V : TopologicalSpace.Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier)
      (N : OXMod.{u, u} (X.toRingedSpace.restrict V.isOpenEmbedding)),
    IsDirectSummandOfFiniteFree N →
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict V.isOpenEmbedding).sheaf)
      ((scalarRestrictionOpen f V).obj N)

omit hdcX [Flat f] [LocallyOfFinitePresentation f] in
/-- The local half of the first assertion of Stacks 0DI4: over an open subspace on which a
strictly perfect complex `P` represents `E`, the restriction of scalars of `E` to `f⁻¹𝒪_S` has
finite Tor dimension. -/
private theorem hasFiniteTorDimension_scalarRestriction_of_isStrictlyPerfect
    (hamp : FlatRepresentativeBounds f D) (hflat : ScalarRestrictionFlat f)
    (V : TopologicalSpace.Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier)
    (Fc : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (eE : DerivedCategory.Q.obj Fc ≅ E)
    (P : CochainComplex (OXMod.{u, u} (X.toRingedSpace.restrict V.isOpenEmbedding)) ℤ)
    (hP : IsStrictlyPerfect P)
    (α : P ⟶ RingedSpace.restrictComplex Fc V) (hα : QuasiIso α) :
    (D V).HasFiniteTorDimension
      ((RingedSpace.derivedRestrictModules
        (RingedSpace.inverseImage S.toRingedSpace f.base) V).obj
          ((derivedScalarRestriction f).obj E)) := by
  obtain ⟨a, b, -, hz⟩ :=
    Stacks.Cohomology.TorAmplitude.exists_bounds_of_isStrictlyPerfect P hP
  let _ : (scalarRestrictionOpen f V).PreservesHomology :=
    Functor.preservesHomologyOfExact (scalarRestrictionOpen f V)
  have hαqi : QuasiIso (((scalarRestrictionOpen f V).mapHomologicalComplex
      (ComplexShape.up ℤ)).map α) := by
    have _ := hα
    exact HomologicalComplex.quasiIso_map_of_preservesHomology α (scalarRestrictionOpen f V)
  have hiso : IsIso (DerivedCategory.Q.map
      (((scalarRestrictionOpen f V).mapHomologicalComplex (ComplexShape.up ℤ)).map α)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hαqi
  let eloc : DerivedCategory.Q.obj
        (((scalarRestrictionOpen f V).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      (RingedSpace.derivedRestrictModules
        (RingedSpace.inverseImage S.toRingedSpace f.base) V).obj
          ((derivedScalarRestriction f).obj E) :=
    (@asIso _ _ _ _ _ hiso) ≪≫
      Iso.refl _ ≪≫
      (RingedSpace.derivedRestrictModulesObjQIso
        (RingedSpace.inverseImage S.toRingedSpace f.base) V
        (((scalarRestriction f).mapHomologicalComplex (ComplexShape.up ℤ)).obj Fc)).symm ≪≫
      (RingedSpace.derivedRestrictModules
        (RingedSpace.inverseImage S.toRingedSpace f.base) V).mapIso
          (((scalarRestriction f).mapDerivedCategoryFactors.app Fc).symm ≪≫
            (derivedScalarRestriction f).mapIso eE)
  exact ⟨a, b, hamp V (((scalarRestrictionOpen f V).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P) a b
    (fun j => hflat V (P.X j) (hP.directSummand j))
    (fun j hj => Functor.map_isZero (scalarRestrictionOpen f V) (hz j hj)) _ eloc⟩

omit hdcX in
/-- For a flat, locally finitely presented morphism of schemes `f : X ⟶ S`, every perfect object
of `D(𝒪_X)` is perfect relative to `S`. -/
@[stacks 0DI4 "a perfect object is perfect relative to the base"]
public theorem isPerfectRelativeTo_of_isPerfect
    (hamp : FlatRepresentativeBounds f D) (hflat : ScalarRestrictionFlat f)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (hE : RingedSpace.IsPerfect E) :
    f.IsPerfectRelativeTo D E := by
  refine ⟨hE.isPseudoCoherent, ?_⟩
  obtain ⟨Fc, ⟨I, U, hsup, hmod⟩, ⟨eE⟩⟩ := hE
  refine ⟨I, U, hsup, fun i => ?_⟩
  obtain ⟨P, hP, α, hα⟩ := hmod i
  exact hasFiniteTorDimension_scalarRestriction_of_isStrictlyPerfect f D hamp hflat (U i) Fc E
    eE P hP α hα

/-- A strictly perfect complex lies in every property of the objects of a derived category of
modules which is closed under isomorphisms and retracts, contains the zero objects, satisfies the
first and third two-out-of-three rules in a distinguished triangle, and contains the structure
sheaf in degree zero. -/
public def StrictlyPerfectInduction : Prop :=
  ∀ (Z : RingedSpace.{u, u}) [HasDerivedCategory.{d'} (OXMod.{u, u} Z)]
      (Pr : DerivedCategory (OXMod.{u, u} Z) → Prop),
    (∀ A B : DerivedCategory (OXMod.{u, u} Z), (A ≅ B) → Pr A → Pr B) →
    (∀ (A B : DerivedCategory (OXMod.{u, u} Z)) (i : A ⟶ B) (r : B ⟶ A),
      i ≫ r = 𝟙 A → Pr B → Pr A) →
    (∀ T : Triangle (DerivedCategory (OXMod.{u, u} Z)), T ∈ distinguishedTriangles →
      Pr T.obj₁ → Pr T.obj₂ → Pr T.obj₃) →
    (∀ T : Triangle (DerivedCategory (OXMod.{u, u} Z)), T ∈ distinguishedTriangles →
      Pr T.obj₂ → Pr T.obj₃ → Pr T.obj₁) →
    (∀ A : DerivedCategory (OXMod.{u, u} Z), IsZero A → Pr A) →
    Pr ((DerivedCategory.singleFunctor (OXMod.{u, u} Z) 0).obj (structureModule Z)) →
    ∀ L : CochainComplex (OXMod.{u, u} Z) ℤ, IsStrictlyPerfect L →
      Pr (DerivedCategory.Q.obj L)

section Tensor

variable
  (commShift : ∀ (V : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier)
      (F : OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        V.isOpenEmbedding)),
    ((D V).derivedTensor.flip.obj ((DerivedCategory.singleFunctor
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        V.isOpenEmbedding)) 0).obj F)).CommShift ℤ)
  (triangulated : ∀ (V : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier)
      (F : OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        V.isOpenEmbedding)),
    letI := commShift V F;
    ((D V).derivedTensor.flip.obj ((DerivedCategory.singleFunctor
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        V.isOpenEmbedding)) 0).obj F)).IsTriangulated)

omit [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]
  [HasDerivedCategory.{d'} (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base))]
  [Flat f] [LocallyOfFinitePresentation f] in
include commShift triangulated in
/-- Finite Tor dimension of the image under a triangulated functor `Θ` propagates to the third
vertex of a distinguished triangle. -/
private theorem hasFiniteTorDimension_Θ_obj₃
    (V : TopologicalSpace.Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier)
    (W : TopologicalSpace.Opens X.toRingedSpace.carrier)
    (Θ : DerivedCategory (OXMod.{u, u} (X.toRingedSpace.restrict W.isOpenEmbedding)) ⥤
      DerivedCategory (OXMod.{u, u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict V.isOpenEmbedding)))
    [Θ.CommShift ℤ] [Θ.IsTriangulated]
    (T : Triangle (DerivedCategory (OXMod.{u, u}
      (X.toRingedSpace.restrict W.isOpenEmbedding))))
    (hT : T ∈ distinguishedTriangles)
    (h₁ : (D V).HasFiniteTorDimension (Θ.obj T.obj₁))
    (h₂ : (D V).HasFiniteTorDimension (Θ.obj T.obj₂)) :
    (D V).HasFiniteTorDimension (Θ.obj T.obj₃) := by
  exact (RingedSpace.CertifiedDerivedSheafTensoring.hasFiniteTorDimension_of_distinguished'
    (D V) (commShift V) (triangulated V) (Θ.mapTriangle.obj T)
    (Functor.map_distinguished _ T hT)).1 h₁ h₂

omit [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]
  [HasDerivedCategory.{d'} (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base))]
  [Flat f] [LocallyOfFinitePresentation f] in
include commShift triangulated in
/-- Finite Tor dimension of the image under a triangulated functor `Θ` propagates to the first
vertex of a distinguished triangle. -/
private theorem hasFiniteTorDimension_Θ_obj₁
    (V : TopologicalSpace.Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier)
    (W : TopologicalSpace.Opens X.toRingedSpace.carrier)
    (Θ : DerivedCategory (OXMod.{u, u} (X.toRingedSpace.restrict W.isOpenEmbedding)) ⥤
      DerivedCategory (OXMod.{u, u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict V.isOpenEmbedding)))
    [Θ.CommShift ℤ] [Θ.IsTriangulated]
    (T : Triangle (DerivedCategory (OXMod.{u, u}
      (X.toRingedSpace.restrict W.isOpenEmbedding))))
    (hT : T ∈ distinguishedTriangles)
    (h₂ : (D V).HasFiniteTorDimension (Θ.obj T.obj₂))
    (h₃ : (D V).HasFiniteTorDimension (Θ.obj T.obj₃)) :
    (D V).HasFiniteTorDimension (Θ.obj T.obj₁) := by
  exact (RingedSpace.CertifiedDerivedSheafTensoring.hasFiniteTorDimension_of_distinguished'
    (D V) (commShift V) (triangulated V) (Θ.mapTriangle.obj T)
    (Functor.map_distinguished _ T hT)).2 h₂ h₃

omit [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]
  [HasDerivedCategory.{d'} (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base))]
  [Flat f] [LocallyOfFinitePresentation f] in
include commShift triangulated in
/-- Given the triangulated induction `hind`, the image under a triangulated functor `Θ` of a
strictly perfect complex has finite Tor dimension as soon as the image of the structure sheaf
does. -/
private theorem hasFiniteTorDimension_of_isStrictlyPerfect
    (V : TopologicalSpace.Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier)
    (W : TopologicalSpace.Opens X.toRingedSpace.carrier)
    (Θ : DerivedCategory (OXMod.{u, u} (X.toRingedSpace.restrict W.isOpenEmbedding)) ⥤
      DerivedCategory (OXMod.{u, u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict V.isOpenEmbedding)))
    [Θ.CommShift ℤ] [Θ.IsTriangulated]
    (hind : StrictlyPerfectInduction.{d', u})
    (hbase : (D V).HasFiniteTorDimension (Θ.obj ((DerivedCategory.singleFunctor
      (OXMod.{u, u} (X.toRingedSpace.restrict W.isOpenEmbedding)) 0).obj
        (structureModule (X.toRingedSpace.restrict W.isOpenEmbedding)))))
    (P : CochainComplex (OXMod.{u, u} (X.toRingedSpace.restrict W.isOpenEmbedding)) ℤ)
    (hP : IsStrictlyPerfect P) :
    (D V).HasFiniteTorDimension (Θ.obj (DerivedCategory.Q.obj P)) :=
  hind (X.toRingedSpace.restrict W.isOpenEmbedding)
    (fun B => (D V).HasFiniteTorDimension (Θ.obj B))
    (fun _ _ e h => RingedSpace.CertifiedDerivedSheafTensoring.hasFiniteTorDimension_of_iso'
      (D V) (Θ.mapIso e) h)
    (fun A _ i r hir h =>
      RingedSpace.CertifiedDerivedSheafTensoring.hasFiniteTorDimension_of_retract' (D V)
        (Θ.map i) (Θ.map r)
        (((Θ.map_comp i r).symm.trans (congrArg (fun φ => Θ.map φ) hir)).trans
          (Θ.map_id A)) h)
    (hasFiniteTorDimension_Θ_obj₃ f D commShift triangulated V W Θ)
    (hasFiniteTorDimension_Θ_obj₁ f D commShift triangulated V W Θ)
    (fun _ hA => RingedSpace.CertifiedDerivedSheafTensoring.hasFiniteTorDimension_of_isZero'
      (D V) (commShift V) (triangulated V) (Θ.map_isZero hA))
    hbase P hP

end Tensor

end Objective

/-! ### The second assertion of Stacks 0DI4

The derived tensor product is `Stacks.Cohomology.PseudoCoherentTensor.derivedTensorProduct` of
Stacks 06YU, on the standard derived category. -/

section TensorObjective

attribute [local instance] HasDerivedCategory.standard

variable [Flat f] [LocallyOfFinitePresentation f]
  (D : ∀ U : TopologicalSpace.Opens
      (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
      ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
  (commShift : ∀ (V : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier)
      (F : OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        V.isOpenEmbedding)),
    ((D V).derivedTensor.flip.obj ((DerivedCategory.singleFunctor
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        V.isOpenEmbedding)) 0).obj F)).CommShift ℤ)
  (triangulated : ∀ (V : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier)
      (F : OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        V.isOpenEmbedding)),
    letI := commShift V F;
    ((D V).derivedTensor.flip.obj ((DerivedCategory.singleFunctor
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        V.isOpenEmbedding)) 0).obj F)).IsTriangulated)

include commShift triangulated in
/-- For a flat, locally finitely presented morphism of schemes `f : X ⟶ S`, the derived tensor
product of a perfect object `K` of `D(𝒪_X)` with an `S`-perfect object `M` is perfect relative
to `S`. -/
@[stacks 0DI4 "tensoring an S-perfect object with a perfect object"]
public theorem isPerfectRelativeTo_derivedTensor
    (hrestricts : RingedSpace.FiniteTorDimensionRestricts
      (RingedSpace.inverseImage S.toRingedSpace f.base) D)
    (hind : StrictlyPerfectInduction.{u + 1, u})
    (hcl : Stacks.Cohomology.PseudoCoherentTensor.ComplexLevel.{u})
    (K M : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (Θ : ∀ (V : TopologicalSpace.Opens
          (RingedSpace.inverseImage S.toRingedSpace f.base).carrier)
        (W : TopologicalSpace.Opens X.toRingedSpace.carrier), (∀ x, x ∈ V → x ∈ W) →
      DerivedCategory (OXMod.{u, u} (X.toRingedSpace.restrict W.isOpenEmbedding)) ⥤
        DerivedCategory (OXMod.{u, u}
          ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict V.isOpenEmbedding)))
    (ΘcommShift : ∀ V W h, (Θ V W h).CommShift ℤ)
    (Θtriangulated : ∀ V W h, letI := ΘcommShift V W h; (Θ V W h).IsTriangulated)
    (Θunit : ∀ V W h, (Θ V W h).obj ((DerivedCategory.singleFunctor
        (OXMod.{u, u} (X.toRingedSpace.restrict W.isOpenEmbedding)) 0).obj
          (structureModule (X.toRingedSpace.restrict W.isOpenEmbedding))) ≅
      (RingedSpace.derivedRestrictModules
        (RingedSpace.inverseImage S.toRingedSpace f.base) V).obj
          ((derivedScalarRestriction f).obj M))
    (Θtensor : ∀ (V W h) (A : DerivedCategory (OXMod.{u, u} X.toRingedSpace)),
      (Θ V W h).obj ((RingedSpace.derivedRestrictModules X.toRingedSpace W).obj A) ≅
        (RingedSpace.derivedRestrictModules
          (RingedSpace.inverseImage S.toRingedSpace f.base) V).obj
            ((derivedScalarRestriction f).obj
          (((Stacks.Cohomology.PseudoCoherentTensor.derivedTensorProduct
            X.toRingedSpace).tensor.obj A).obj M)))
    (hK : RingedSpace.IsPerfect.{u, u + 1} K)
    (hM : f.IsPerfectRelativeTo D M) :
    f.IsPerfectRelativeTo D
      (((Stacks.Cohomology.PseudoCoherentTensor.derivedTensorProduct
        X.toRingedSpace).tensor.obj K).obj M) := by
  refine ⟨Stacks.Cohomology.PseudoCoherentTensor.isPseudoCoherent_canonicalDerivedTensorProduct
    X.toRingedSpace hcl K M hK.isPseudoCoherent hM.1, ?_⟩
  obtain ⟨Fc, ⟨I, U, hsupU, hmod⟩, ⟨eK⟩⟩ := hK
  obtain ⟨J, V, hsupV, htorM⟩ := hM.2
  refine ⟨I × J, fun ij => U ij.1 ⊓ V ij.2, ?_, fun ij => ?_⟩
  · refine top_unique fun x _ => ?_
    have hxU : x ∈ iSup U := by rw [hsupU]; trivial
    have hxV : x ∈ iSup V := by rw [hsupV]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxU
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxV
    exact Opens.mem_iSup.mpr ⟨(i, j), hi, hj⟩
  · obtain ⟨P, hP, α, hα⟩ := hmod ij.1
    have hsub : ∀ x, x ∈ U ij.1 ⊓ V ij.2 → x ∈ U ij.1 := fun _ hx => hx.1
    let _ := ΘcommShift (U ij.1 ⊓ V ij.2) (U ij.1) hsub
    let _ := Θtriangulated (U ij.1 ⊓ V ij.2) (U ij.1) hsub
    have hbase := RingedSpace.CertifiedDerivedSheafTensoring.hasFiniteTorDimension_of_iso'
      (D (U ij.1 ⊓ V ij.2)) (Θunit (U ij.1 ⊓ V ij.2) (U ij.1) hsub).symm
      (hrestricts inf_le_right _ (htorM ij.2))
    have hPr := hasFiniteTorDimension_of_isStrictlyPerfect f D commShift triangulated
      (U ij.1 ⊓ V ij.2) (U ij.1) (Θ (U ij.1 ⊓ V ij.2) (U ij.1) hsub) hind hbase P hP
    have hiso : IsIso (DerivedCategory.Q.map α) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hα
    let eP : DerivedCategory.Q.obj P ≅
        (RingedSpace.derivedRestrictModules X.toRingedSpace (U ij.1)).obj K :=
      (@asIso _ _ _ _ _ hiso) ≪≫
        (RingedSpace.derivedRestrictModulesObjQIso X.toRingedSpace (U ij.1) Fc).symm ≪≫
        (RingedSpace.derivedRestrictModules X.toRingedSpace (U ij.1)).mapIso eK
    exact RingedSpace.CertifiedDerivedSheafTensoring.hasFiniteTorDimension_of_iso'
      (D (U ij.1 ⊓ V ij.2))
      ((Θ (U ij.1 ⊓ V ij.2) (U ij.1) hsub).mapIso eP ≪≫ Θtensor (U ij.1 ⊓ V ij.2) (U ij.1) hsub K)
      hPr

end TensorObjective

end Scheme.Hom

end AlgebraicGeometry

end
