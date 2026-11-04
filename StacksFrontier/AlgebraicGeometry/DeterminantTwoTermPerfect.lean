module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrict
public import StacksFrontier.Homology.TwoTermComplex.DeterminantFunctor
public import StacksFrontier.Homology.TwoTermComplex.DeterminantLine
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.TransportAlongAnIsomorphism
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksCore.Tactic.EgaSgaAttribute
/-!
# The groupoids carrying the determinant of a two-term perfect complex on a scheme

Let `X` be a scheme. The determinant of Stacks 0FJX is a functor from the groupoid whose objects
are the perfect objects of `D(𝒪_X)` of Tor amplitude in `[-1, 0]` and whose morphisms are the
isomorphisms, to the groupoid of invertible `𝒪_X`-modules and their isomorphisms; a rank-zero
object `L` carries in addition a canonical global section `δ(L)` of `det(L)`, preserved by the
determinant of every isomorphism; and affine locally both are the construction over a ring of
More on Algebra, Section 0FJI.

This file fixes the two groupoids and shows that the first two of those three assertions hold for
formal reasons: the constant functor at `𝒪_X` is a functor between exactly these two groupoids,
and the zero section of any module satisfies the compatibility `det(a)(δ(L)) = δ(K)`. The
affine-local identification excludes the zero section.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.IsPerfectTwoTermAmplitude`: the object property cutting
  out the source groupoid, perfectness together with Tor amplitude in `[-1, 0]`.
* `AlgebraicGeometry.DeterminantTwoTerm.PerfectTwoTermAmplitude` and
  `AlgebraicGeometry.DeterminantTwoTerm.InvertibleModuleCat`: the two full subcategories whose
  `CategoryTheory.Core` are the source and target groupoids of the determinant.
* `AlgebraicGeometry.DeterminantTwoTerm.unitInvertible`: the structure sheaf as an object of the
  target groupoid.
* `AlgebraicGeometry.DeterminantTwoTerm.constUnitFunctor` and
  `AlgebraicGeometry.DeterminantTwoTerm.zeroSection`: the constant functor at `𝒪_X` and the zero
  global section.
* `AlgebraicGeometry.DeterminantTwoTerm.IsRankZeroScheme`: rank zero for an object of `D(𝒪_X)`,
  read on affine opens as rank zero of a corresponding object of `D(Γ(X, V))` in the sense of
  More on Algebra, Section 0FJI.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.zeroSection_natural`: the zero section is preserved by
  the image under the constant functor of every isomorphism.
* `AlgebraicGeometry.DeterminantTwoTerm.exists_functor_and_natural_section`: for *every* notion
  of rank zero, there is a functor from the source groupoid to the target groupoid together with
  a global section of its value at every rank-zero object, compatible with all isomorphisms.
* `AlgebraicGeometry.DeterminantTwoTerm.delta_id_ne_zero`: the canonical element of the
  determinant line of More on Algebra, Section 0FJI is not identically zero, so the zero section
  above is excluded by the affine-local assertion.
* `AlgebraicGeometry.DeterminantTwoTerm.isPerfectTwoTermAmplitude_derivedPullback`: the derived
  pullback of a perfect object of Tor amplitude in `[-1, 0]` is again one.

## Implementation notes

"Morphisms are the isomorphisms" is `CategoryTheory.Core` of a full subcategory.

Perfectness is `Stacks.Cohomology.PerfectComplexes.IsPerfect`, the predicate of Stacks 08CM on a
ringed space, and Tor amplitude is `Stacks.Cohomology.TorAmplitude.HasTorAmplitude`, the predicate
of Stacks 08CG stated against `Stacks.Cohomology.TorAmplitude.derTensor` — the derived tensor
product of Stacks 06YU read at the opens of `X`, not an abstract bifunctor. The alternative
spelling `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.HasTorAmplitudeIn` is
parameterised by a certificate, and
`AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_firstProjection_iff` exhibits a certificate for
which it degenerates to the vanishing of cohomology, so a source category stated against an
arbitrary certificate would not be the source category of Stacks 0FJX. Both predicates are read on
`DerivedCategory X.Modules`, which is `DerivedCategory (StrictlyPerfect.OXMod X.toRingedSpace)`.

Invertibility is `Stacks.Ample.IsInvertibleModule`, which is Stacks 01CS's class with the sheaf
condition on the structure presheaf of rings supplied; the structure sheaf satisfies it by
`Stacks.Ample.isInvertibleModule_unit`.

The derived category is the standard one, `HasDerivedCategory.standard`.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Remark 36.39.2 (Tag 0FJY)](https://stacks.math.columbia.edu/tag/0FJY)
* [Stacks Project, Section 15.87 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Lemma 15.87.4 (Tag 0FJM)](https://stacks.math.columbia.edu/tag/0FJM)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Definition 20.49.1 (Tag 08CM)](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Definition 17.23.1 (Tag 01CS)](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory StrictlyPerfect

universe u

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance] HasDerivedCategory.standard

/-- The property cutting out the source groupoid of the determinant of Stacks 0FJX: an object of
`D(𝒪_X)` which is perfect (Stacks 08CM) and has Tor amplitude in `[-1, 0]` (Stacks 08CG, against
the derived tensor product of Stacks 06YU). -/
def IsPerfectTwoTermAmplitude (X : Scheme.{u}) : ObjectProperty (DerivedCategory X.Modules) :=
  fun K => Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K ∧
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace K (-1) 0

/-- The category of perfect objects of `D(𝒪_X)` of Tor amplitude in `[-1, 0]`. Its
`CategoryTheory.Core` is the source groupoid of the determinant, in which the morphisms are the
isomorphisms. -/
abbrev PerfectTwoTermAmplitude (X : Scheme.{u}) := (IsPerfectTwoTermAmplitude X).FullSubcategory

/-- The property cutting out the target groupoid of the determinant of Stacks 0FJX: an invertible
`𝒪_X`-module, in the sense of Stacks 01CS. -/
def IsInvertibleProperty (X : Scheme.{u}) : ObjectProperty X.Modules :=
  fun L => Stacks.Ample.IsInvertibleModule X L

/-- The category of invertible `𝒪_X`-modules. Its `CategoryTheory.Core` is the target groupoid of
the determinant, in which the morphisms are the isomorphisms. -/
abbrev InvertibleModuleCat (X : Scheme.{u}) := (IsInvertibleProperty X).FullSubcategory

/-- The structure sheaf `𝒪_X`, as an object of the target groupoid of the determinant: it is an
invertible `𝒪_X`-module by `Stacks.Ample.isInvertibleModule_unit`. -/
def unitInvertible (X : Scheme.{u}) : InvertibleModuleCat X :=
  ⟨Stacks.Ample.unitModule X, Stacks.Ample.isInvertibleModule_unit X⟩

/-- The constant functor at the structure sheaf, from the source groupoid of the determinant of
Stacks 0FJX to its target groupoid. -/
def constUnitFunctor (X : Scheme.{u}) :
    Core (PerfectTwoTermAmplitude X) ⥤ Core (InvertibleModuleCat X) :=
  (Functor.const _).obj ⟨unitInvertible X⟩

/-- The zero global section of an `𝒪_X`-module. -/
def zeroSection {X : Scheme.{u}} (M : X.Modules) : Γ(M, ⊤) := 0

/-- Every map of `𝒪_X`-modules carries the zero global section to the zero global section. -/
theorem zeroSection_natural {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) :
    Scheme.Modules.Hom.app f ⊤ (zeroSection M) = zeroSection N :=
  map_zero _

/-- **The first two assertions of Stacks 0FJX are empty.** For every scheme `X` and every
property `rankZero` of objects of `D(𝒪_X)`, there is a functor `det` from the groupoid of perfect
objects of `D(𝒪_X)` of Tor amplitude in `[-1, 0]` and isomorphisms to the groupoid of invertible
`𝒪_X`-modules and isomorphisms, together with a global section `δ(L)` of `det(L)` for every
`rankZero` object `L`, such that `det(a)(δ(L)) = δ(K)` for every isomorphism `a : L ⟶ K`. -/
theorem exists_functor_and_natural_section (X : Scheme.{u})
    (rankZero : ObjectProperty (DerivedCategory X.Modules)) :
    ∃ (det : Core (PerfectTwoTermAmplitude X) ⥤ Core (InvertibleModuleCat X))
      (δ : ∀ L : PerfectTwoTermAmplitude X, rankZero L.obj → Γ((det.obj ⟨L⟩).of.obj, ⊤)),
      ∀ (L K : PerfectTwoTermAmplitude X) (a : (⟨L⟩ : Core (PerfectTwoTermAmplitude X)) ⟶ ⟨K⟩)
        (hL : rankZero L.obj) (hK : rankZero K.obj),
        Scheme.Modules.Hom.app ((IsInvertibleProperty X).ι.map (det.map a).iso.hom) ⊤ (δ L hL) =
          δ K hK :=
  ⟨constUnitFunctor X, fun _ _ => zeroSection _, fun _ _ _ _ _ => zeroSection_natural _⟩

/-- **The canonical element of More on Algebra, Section 0FJI is not identically zero**: it is
nonzero for the rank-zero two-term complex `ℚ --id--> ℚ`. -/
theorem delta_id_ne_zero :
    TwoTermComplex.delta (LinearMap.id : ℚ →ₗ[ℚ] ℚ) (fun _ => rfl) ≠ 0 := by
  have h : TwoTermComplex.delta (LinearMap.id : ℚ →ₗ[ℚ] ℚ) (fun _ => rfl) = LinearMap.id :=
    ProjectiveDeterminant.map_id
  have hinv := ProjectiveDeterminant.invertible (R := ℚ) (M := ℚ)
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free ℚ (ProjectiveDeterminant.module (R := ℚ) (M := ℚ)))
  obtain ⟨a, b, hab⟩ := e.toEquiv.nontrivial
  rw [h]
  exact fun hc => hab ((LinearMap.congr_fun hc a).trans (LinearMap.congr_fun hc b).symm)

/-- **The source category is preserved by derived pullback.** For a morphism of schemes
`f : X ⟶ Y`, the derived pullback `Lf^*K` of a perfect object `K` of `D(𝒪_Y)` of Tor amplitude in
`[-1, 0]` is again perfect of Tor amplitude in `[-1, 0]`. -/
@[stacks 0FJY "the derived pullback lands in the source category", sga "6 I 4.19.2" "special case"]
theorem isPerfectTwoTermAmplitude_derivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory Y.Modules) (hK : IsPerfectTwoTermAmplitude Y K) :
    IsPerfectTwoTermAmplitude X
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        f.toLRSHom.toShHom).obj K) :=
  ⟨RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ K hK.1,
    Stacks.Cohomology.TorAmplitude.Pullback.hasTorAmplitude_derivedPullback _ K (-1) 0 hK.2⟩

/-- The derived pullback along `f : X ⟶ Y` of an object of the source groupoid of the
determinant over `Y`, as an object of the source groupoid of the determinant over `X`. -/
def derivedPullbackObj {X Y : Scheme.{u}} (f : X ⟶ Y) (L : PerfectTwoTermAmplitude Y) :
    PerfectTwoTermAmplitude X :=
  ⟨_, isPerfectTwoTermAmplitude_derivedPullback f L.obj L.property⟩

/-- **Rank zero for an object of `D(𝒪_X)`.** Every point of `X` has an affine open neighbourhood
`V` such that `K|_V` is, along `V ≅ Spec Γ(X, V)`, the derived sheafification of an object of
`D(Γ(X, V))` admitting a two-term presentation `L⁻¹ → L⁰` by finite projective modules with
`L⁻¹_𝔭` and `L⁰_𝔭` of the same rank at every prime `𝔭`, as in More on Algebra, Section 0FJI. -/
def IsRankZeroScheme {X : Scheme.{u}} (K : DerivedCategory (OXMod.{u} X.toRingedSpace)) : Prop :=
  ∀ x : X, ∃ (V : X.Opens) (hV : IsAffineOpen V), x ∈ V ∧
    ∃ M : DerivedCategory (ModuleCat.{u} Γ(X, V)), TwoTermDeterminant.IsRankZero M ∧
      Nonempty ((RingedSpace.derivedRestrictModules X.toRingedSpace V).obj K ≅
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            (Stacks.Cohomology.TransportAlongIso.ringedSpaceIsoOfSchemeIso hV.isoSpec).hom).obj
          ((tilde.functor Γ(X, V)).mapDerivedCategory.obj M))

end AlgebraicGeometry.DeterminantTwoTerm

end
