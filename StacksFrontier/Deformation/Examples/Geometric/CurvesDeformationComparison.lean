module

public import StacksFrontier.Deformation.Examples.Geometric.SchemesDeformationCategory
public import StacksFrontier.AlgebraicGeometry.Quot.CurveDeformationsSchemes
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationFiberAut
public import StacksFrontier.Deformation.Examples.Geometric.OpenSubschemes
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.Properties
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverField
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Smooth.FullVertical
public import StacksFrontier.Deformation.Smooth.Unobstructed
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.GroupSpaceTranslation
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhEtaleSchemeSlices

/-!
# Flat deformations of a curve as deformations of a point of the stack of curves

Let `k` be a field, `Λ → k` a ring map, and `X` a proper scheme over `k` of dimension at most
one. The structure morphism `X → Spec k` is a family of curves (Stacks 0D4Z), that is a point
`x₀ : Spec k → Curves` of the stack of curves over `Spec ℤ`; through any morphism
`Spec Λ → Spec ℤ` it gives the predeformation category `𝓕_{Curves, k, x₀}` over `𝒞_Λ`
(Stacks 07T4). On the other side there is the deformation category `Def_X` of flat deformations
of `X` over the objects of `𝒞_Λ` (Stacks 0DY7, 0DY8).

The proof of Stacks 0DZU rests on the equality `Def_X = 𝓕_{Curves, k, x₀}`. This file constructs
the comparison functor `Def_X ⥤ 𝓕_{Curves, k, x₀}` over `𝒞_Λ` and proves that it is full and
faithful. A flat deformation `Y → Spec A` of `X` is proper and of finite presentation because
`X → Spec k` is (Stacks 06AG), and of dimension at most one because `X → Y` is a homeomorphism,
so it is a family of curves; the identification of its special fibre with `X` is a cartesian
square of schemes, which stays cartesian among algebraic spaces. Conversely a morphism of
families of curves between such deformations is a cartesian square of the algebraic spaces they
represent, which comes from a unique cartesian square of schemes because reading a scheme as an
algebraic space is fully faithful.

The file also shows that a deformation of `x₀` whose total space is represented by a scheme is
isomorphic over `𝒞_Λ` to the image of a deformation of `X`. That every deformation of `x₀` has
this property, and hence that the comparison functor is an equivalence, is proved in
`StacksFrontier.Deformation.Examples.Geometric.CurvesDeformationThickening`.

## Main definitions

* `Deformation.Examples.SchemeDeformationCategory.toCurveDeformation`: a deformation of `X` as a
  deformation of `x₀`.
* `Deformation.Examples.curvesPredeformation`: the predeformation category
  `𝓕_{Curves, k, x₀}`.
* `Deformation.Examples.schemeDeformationToCurves`: the comparison functor, and
  `Deformation.Examples.schemeDeformationToCurvesBased` the same functor over `𝒞_Λ`.

## Main results

* `Deformation.Examples.SchemeDeformationCategory.isProper_toBase` and
  `Deformation.Examples.SchemeDeformationCategory.locallyOfFinitePresentation_toBase`: a
  deformation of a proper scheme over `k` is proper and of finite presentation (Stacks 06AG).
* `Deformation.Examples.contains_baseSpec`: the spectrum of every object of `𝒞_Λ` lies in every
  big fppf site containing the spectrum of `k`.
* `Deformation.Examples.schemeDeformationToCurves_full` and
  `Deformation.Examples.schemeDeformationToCurves_faithful`: the comparison functor is full and
  faithful.
* `Deformation.Examples.exists_iso_schemeDeformationToCurves_obj_of_iso_schemeSpace`: a
  deformation of `x₀` with a scheme as total space comes from a deformation of `X`.

## Implementation notes

The stack of curves is presented by the category `AlgebraicGeometry.CurveFamily` of families of
curves over the big fppf site of `Spec ℤ`, read over the slice of schemes over `Spec ℤ` through
`Deformation.Examples.curvesToSchemesOver`; this is the functor `𝒳 ⥤ (Sch/S)` from which the
predeformation category of Stacks 07T4 is built. Since `Spec ℤ` is terminal, the morphism
`Spec Λ → Spec ℤ` is unique, and it is left arbitrary.

The big fppf site is size-bounded, so the point `x₀` exists only when `Spec k` is an object of the
site; that is the hypothesis `hk`, and it is the only size condition: the spectrum of an Artinian
local ring with residue field `k` has cardinality at most `max ℵ₀ #k`, and a scheme of finite type
over an object of the site lies in the site, so every scheme the comparison needs is an object of
the site.

## References

* [Stacks Project, Tag 0DZU](https://stacks.math.columbia.edu/tag/0DZU)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 0DY8](https://stacks.math.columbia.edu/tag/0DY8)
* [Stacks Project, Tag 07T4](https://stacks.math.columbia.edu/tag/07T4)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 06AG](https://stacks.math.columbia.edu/tag/06AG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- A module of finite length over a local ring has at most `max ℵ₀ #κ` elements. -/
theorem Cardinal.mk_le_max_residueField_of_isFiniteLength {R : Type u} [CommRing R]
    [IsLocalRing R] {M : Type u} [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Cardinal.mk M ≤ max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField R)) := by
  induction hM with
  | of_subsingleton =>
    exact (Cardinal.le_one_iff_subsingleton.mpr inferInstance).trans
      (Cardinal.one_le_aleph0.trans (le_max_left _ _))
  | @of_simple_quotient M _ _ N hs _ ih =>
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    obtain rfl : I = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hI
    calc Cardinal.mk M = Cardinal.mk (M ⧸ N) * Cardinal.mk N := by
          rw [← Cardinal.lift_id (Cardinal.mk (M ⧸ N)), ← Cardinal.lift_id (Cardinal.mk N),
            ← Cardinal.mk_prod]
          exact Cardinal.mk_congr
            (AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := N.toAddSubgroup))
      _ ≤ max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField R)) *
            max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField R)) :=
          mul_le_mul' ((Cardinal.mk_congr e.toEquiv).trans_le (le_max_right _ _)) ih
      _ = _ := Cardinal.mul_eq_self (le_max_left _ _)

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **The spectrum of an object of `𝒞_Λ` lies in every big fppf site containing the spectrum of
`k`.** An Artinian local ring with residue field `k` has finite length, so it has at most
`max ℵ₀ #k` elements. -/
theorem contains_baseSpec (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k) : B.Contains (baseSpec A) := by
  have hlen : IsFiniteLength A A := (isArtinianRing_iff_isFiniteLength A).mp inferInstance
  have h := Cardinal.mk_le_max_residueField_of_isFiniteLength hlen
  rw [Cardinal.mk_congr A.residueEquiv.toEquiv] at h
  exact BigFppfSite.contains_spec_of_mk_lt_cutoff B (h.trans_lt
    (max_lt B.aleph0_lt_cutoff (BigFppfSite.mk_lt_cutoff_of_contains_spec B hk)))

end Deformation.Examples

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Reading a scheme of a big fppf site containing `S` as an algebraic space is full. -/
instance schemeSpaceFunctor_full_of_contains : (schemeSpaceFunctor B S hS).Full :=
  (schemeSpaceFunctorFullyFaithful B hS).full

/-- Reading a scheme of a big fppf site containing `S` as an algebraic space is faithful. -/
instance schemeSpaceFunctor_faithful_of_contains : (schemeSpaceFunctor B S hS).Faithful :=
  (schemeSpaceFunctorFullyFaithful B hS).faithful

/-- The morphism of algebraic spaces induced by a morphism of the site determines it. -/
theorem schemeSpaceMap_injective {U V : BigFppfOver B S hS} {g g' : U ⟶ V}
    (h : schemeSpaceMap g = schemeSpaceMap g') : g = g' :=
  (schemeSpaceFunctor B S hS).map_injective h

/-- **A square of the site which is cartesian among algebraic spaces is cartesian**: reading a
scheme as an algebraic space is fully faithful, hence reflects fibre products. -/
theorem isPullback_of_isPullback_schemeSpaceMap {P Q R W : BigFppfOver B S hS} {a : P ⟶ Q}
    {b : P ⟶ R} {c : Q ⟶ W} {d : R ⟶ W}
    (h : IsPullback (schemeSpaceMap a) (schemeSpaceMap b) (schemeSpaceMap c) (schemeSpaceMap d)) :
    IsPullback a b c d :=
  IsPullback.of_map_of_faithful (schemeSpaceFunctor B S hS) h

end AlgebraicGeometry

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

variable {B hZ}

/-- Reading morphisms of schemes of the site over the integers preserves composition. -/
theorem integerSiteMap_comp {T T' T'' : Scheme.{u}} {hT : B.Contains T} {hT' : B.Contains T'}
    {hT'' : B.Contains T''} (f : T ⟶ T') (g : T' ⟶ T'') :
    integerSiteMap B hZ hT hT' f ≫ integerSiteMap B hZ hT' hT'' g =
      integerSiteMap B hZ hT hT'' (f ≫ g) :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ rfl)

/-- Reading morphisms of schemes of the site over the integers preserves identities. -/
theorem integerSiteMap_id {T : Scheme.{u}} {hT : B.Contains T} :
    integerSiteMap B hZ hT hT (𝟙 T) = 𝟙 _ :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ rfl)

/-- Every morphism between schemes of the site over the integers is the morphism of its
underlying schemes. -/
theorem integerSiteMap_toScheme_map {T T' : Scheme.{u}} {hT : B.Contains T}
    {hT' : B.Contains T'} (g : integerSiteObject B hZ hT ⟶ integerSiteObject B hZ hT') :
    integerSiteMap B hZ hT hT' ((BigFppfOver.toScheme B integerBase hZ).map g) = g :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ rfl)

/-- A scheme of the site over the integers, read in the slice over the integers, is its
structure morphism, whichever that is: the integers are terminal. -/
theorem post_integerSiteObject {T : Scheme.{u}} (hT : B.Contains T) (φ : T ⟶ integerBase) :
    (Over.post B.inclusion).obj (integerSiteObject B hZ hT) = Over.mk φ :=
  congrArg Over.mk (specULiftZIsTerminal.hom_ext _ _)

/-- A cartesian square of schemes of the site gives a cartesian square of the algebraic spaces
they represent. -/
theorem isPullback_schemeSpaceMap_integerSiteMap {P Q R W : Scheme.{u}} {hP : B.Contains P}
    {hQ : B.Contains Q} {hR : B.Contains R} {hW : B.Contains W} {a : P ⟶ Q} {b : P ⟶ R}
    {c : Q ⟶ W} {d : R ⟶ W} (h : IsPullback a b c d) :
    IsPullback (schemeSpaceMap (integerSiteMap B hZ hP hQ a))
      (schemeSpaceMap (integerSiteMap B hZ hP hR b))
      (schemeSpaceMap (integerSiteMap B hZ hQ hW c))
      (schemeSpaceMap (integerSiteMap B hZ hR hW d)) :=
  isPullback_schemeSpaceMap (IsPullback.of_map_of_faithful
    (BigFppfOver.toScheme B integerBase hZ) h)

/-- A square of schemes of the site whose square of algebraic spaces is cartesian is
cartesian. -/
theorem isPullback_of_isPullback_schemeSpaceMap_integerSiteMap {P Q R W : Scheme.{u}}
    {hP : B.Contains P} {hQ : B.Contains Q} {hR : B.Contains R} {hW : B.Contains W}
    {a : P ⟶ Q} {b : P ⟶ R} {c : Q ⟶ W} {d : R ⟶ W}
    (h : IsPullback (schemeSpaceMap (integerSiteMap B hZ hP hQ a))
      (schemeSpaceMap (integerSiteMap B hZ hP hR b))
      (schemeSpaceMap (integerSiteMap B hZ hQ hW c))
      (schemeSpaceMap (integerSiteMap B hZ hR hW d))) :
    IsPullback a b c d := by
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  exact (isPullback_of_isPullback_schemeSpaceMap h).map (BigFppfOver.toScheme B integerBase hZ)

/-- A morphism of algebraic spaces between schemes of the site over the integers is induced by a
morphism of schemes. -/
private theorem exists_schemeSpaceMap_integerSiteMap_eq {T T' : Scheme.{u}} {hT : B.Contains T}
    {hT' : B.Contains T'}
    (x : schemeSpace (integerSiteObject B hZ hT) ⟶ schemeSpace (integerSiteObject B hZ hT')) :
    ∃ g : T ⟶ T', schemeSpaceMap (integerSiteMap B hZ hT hT' g) = x :=
  ⟨(BigFppfOver.toScheme B integerBase hZ).map
      ((schemeSpaceFunctorFullyFaithful _ _).preimage x), by
    rw [integerSiteMap_toScheme_map]
    exact (schemeSpaceFunctorFullyFaithful _ _).map_preimage _⟩

/-- A morphism of the site over the integers whose underlying morphism of schemes is `r` is the
morphism induced by `r`. -/
private theorem eq_integerSiteMap_of_map_eq {T T' : Scheme.{u}} {hT : B.Contains T}
    {hT' : B.Contains T'} {f : integerSiteObject B hZ hT ⟶ integerSiteObject B hZ hT'}
    {r : T ⟶ T'} (h : 𝟙 _ ≫ (BigFppfOver.toScheme B integerBase hZ).map f ≫ 𝟙 _ = r) :
    f = integerSiteMap B hZ hT hT' r := by
  rw [Category.id_comp, Category.comp_id] at h
  exact (integerSiteMap_toScheme_map f).symm.trans (congrArg _ h)

end AlgebraicGeometry

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {X : Over (Spec (.of k))}

namespace SchemeDeformationCategory

/-- The structure morphism of a deformation of `X`, as a cartesian finite-order deformation of
the structure morphism of `X` over the closed point of the spectrum of the base. -/
def structureDeformationDiagram (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.{u} where
  S := Spec (CommRingCat.of k)
  S' := baseSpec P.base
  iS := residueSpecMap P.base
  iS_finiteOrder := residueSpecMap_isFiniteOrderThickening P.base
  X := X.left
  X' := P.scheme
  iX := P.specialMap
  iX_thickening := deformationSpecialMap_isThickening P
  Y := Spec (CommRingCat.of k)
  Y' := baseSpec P.base
  iY := residueSpecMap P.base
  iY_thickening := (residueSpecMap_isFiniteOrderThickening P.base).isThickening
  pX := X.hom
  pX' := P.toBase
  pY := 𝟙 _
  pY' := 𝟙 _
  f := X.hom
  f' := P.toBase
  f_over_S := Category.comp_id _
  f'_over_S' := Category.comp_id _
  f_thickening_comm := P.specialCartesian.w.symm
  X_cartesian := P.specialCartesian
  Y_cartesian := IsPullback.id_vert _
  X'_flat := P.flat

/-- **A deformation of a proper scheme is proper** over its base (Stacks 06AG). -/
theorem isProper_toBase [IsProper X.hom] (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    IsProper P.toBase :=
  (Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.isProper_iff
    P.structureDeformationDiagram).mp ‹_›

/-- **A deformation of a scheme locally of finite presentation is locally of finite
presentation** over its base (Stacks 06AG). -/
theorem locallyOfFinitePresentation_toBase [LocallyOfFinitePresentation X.hom]
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    LocallyOfFinitePresentation P.toBase :=
  (Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.locallyOfFinitePresentation_iff
    P.structureDeformationDiagram).mp ‹_›

/-- A deformation of `X` has the dimension of `X`: the special fibre is a homeomorphism. -/
theorem topologicalKrullDim_scheme (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    topologicalKrullDim P.scheme = topologicalKrullDim X.left :=
  (IsHomeomorph.topologicalKrullDim_eq _ (deformationSpecialMap_isHomeomorph P)).symm

/-- The total space of a deformation of a proper scheme over `k` lies in every big fppf site
containing the spectrum of `k`. -/
theorem contains_scheme [IsProper X.hom] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) : B.Contains P.scheme := by
  have := P.isProper_toBase
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact P.toBase
    (contains_baseSpec B hk P.base)

end SchemeDeformationCategory

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- A proper scheme over `k` lies in every big fppf site containing the spectrum of `k`. -/
theorem contains_left_of_isProper [IsProper X.hom] (hk : B.Contains (Spec (.of k))) :
    B.Contains X.left :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk

variable (X) [IsProper X.hom] (hk : B.Contains (Spec (.of k)))
  (hdim : topologicalKrullDim X.left ≤ 1)

/-- The functor from families of curves to schemes over the integers taking a family to its base:
the structure functor of the stack of curves, read in the slice over `Spec ℤ`. -/
abbrev curvesToSchemesOver : CurveFamily B hZ ⥤ Over integerBase :=
  curvesProjectionOver B hZ ⋙ Over.post B.inclusion

/-- The family of curves of `X` lies over the spectrum of `k`, whatever morphism `Spec Λ ⟶ Spec ℤ`
is chosen. -/
theorem curvesToSchemesOver_obj_curveFamilyOfScheme (iΛ : Spec (.of Λ) ⟶ integerBase) :
    (curvesToSchemesOver B hZ).obj (curveFamilyOfScheme X B hZ hk hdim) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
  post_integerSiteObject hk _

end Deformation.Examples

namespace Deformation.Examples

open Deformation.Artin

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
variable {X : Over (Spec (.of k))} [IsProper X.hom] (hk : B.Contains (Spec (.of k)))
  (hdim : topologicalKrullDim X.left ≤ 1)

namespace SchemeDeformationCategory

/-- **The family of curves of a deformation of `X`**: the total space of the deformation over the
spectrum of its base, which is proper, flat and of finite presentation by Stacks 06AG and has the
dimension of `X`. -/
def curveFamily (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) : CurveFamily B hZ :=
  curveFamilyOfProperFlatMorphism B hZ
    (integerSiteMap B hZ (P.contains_scheme B hk) (contains_baseSpec B hk P.base) P.toBase)
    P.flat P.isProper_toBase P.locallyOfFinitePresentation_toBase
    ((P.topologicalKrullDim_scheme).trans_le hdim)

variable (iΛ : Spec (.of Λ) ⟶ integerBase)

/-- **A deformation of `X` as a deformation of the point `x₀` of the stack of curves**: its family
of curves, with the cartesian square identifying the fibre over the closed point with `X`. -/
def toCurveDeformation (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    DeformationObject iΛ (curvesToSchemesOver B hZ) (curveFamilyOfScheme X B hZ hk hdim)
      (curvesToSchemesOver_obj_curveFamilyOfScheme X B hZ hk hdim iΛ) where
  algebra := P.base
  point := P.curveFamily B hZ hk hdim
  arrow :=
    { baseMap := integerSiteMap B hZ hk (contains_baseSpec B hk P.base) (residueSpecMap P.base)
      totalMap := schemeSpaceMap (integerSiteMap B hZ (contains_left_of_isProper B hk)
        (P.contains_scheme B hk) P.specialMap)
      cartesian := isPullback_schemeSpaceMap_integerSiteMap P.specialCartesian }
  base := post_integerSiteObject _ _
  arrow_base := by
    change 𝟙 _ ≫ residueSpecMap P.base ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id]

/-- **A morphism of deformations of `X` as a morphism of deformations of `x₀`**: the reversed
arrow is the cartesian square of total spaces over the map of spectra of the bases. -/
def toCurveDeformationMorphism {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (f : P ⟶ Q) :
    DeformationMorphism iΛ (curvesToSchemesOver B hZ) (curveFamilyOfScheme X B hZ hk hdim)
      (curvesToSchemesOver_obj_curveFamilyOfScheme X B hZ hk hdim iΛ)
      (P.toCurveDeformation B hZ hk hdim iΛ) (Q.toCurveDeformation B hZ hk hdim iΛ) where
  ringHom := f.base
  arrow :=
    { baseMap := integerSiteMap B hZ (contains_baseSpec B hk Q.base)
        (contains_baseSpec B hk P.base) (baseSpecMap f.base)
      totalMap := schemeSpaceMap (integerSiteMap B hZ (Q.contains_scheme B hk)
        (P.contains_scheme B hk) f.map)
      cartesian := isPullback_schemeSpaceMap_integerSiteMap f.cartesian }
  triangle := by
    apply CurveFamily.Hom.ext
    · change integerSiteMap B hZ _ _ (residueSpecMap Q.base) ≫
        integerSiteMap B hZ _ _ (baseSpecMap f.base) = integerSiteMap B hZ _ _ _
      rw [integerSiteMap_comp, residueSpecMap_naturality]
    · change schemeSpaceMap (integerSiteMap B hZ _ _ Q.specialMap) ≫
        schemeSpaceMap (integerSiteMap B hZ _ _ f.map) = schemeSpaceMap (integerSiteMap B hZ _ _ _)
      rw [← schemeSpaceMap_comp, integerSiteMap_comp, f.special_compat]
  arrow_base := by
    change 𝟙 _ ≫ baseSpecMap f.base ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id]
    rfl

end SchemeDeformationCategory

variable (iΛ : Spec (.of Λ) ⟶ integerBase) (X)

/-- The predeformation category `𝓕_{Curves, k, x₀}` of the point `x₀` of the stack of curves
classifying `X`, presented on the category `AlgebraicGeometry.CurveFamily` of families of curves
over the slice over `Spec ℤ`. -/
abbrev curvesPredeformation :
    PredeformationConstruction iΛ (curvesToSchemesOver B hZ) (curveFamilyOfScheme X B hZ hk hdim)
      (curvesToSchemesOver_obj_curveFamilyOfScheme X B hZ hk hdim iΛ) :=
  predeformationCategory iΛ (curvesToSchemesOver B hZ) (curveFamilyOfScheme X B hZ hk hdim)
    (curvesToSchemesOver_obj_curveFamilyOfScheme X B hZ hk hdim iΛ)

/-- The category structure of `𝓕_{Curves, k, x₀}`. -/
instance curvesPredeformation_category :
    Category (curvesPredeformation B hZ X hk hdim iΛ).carrier :=
  (curvesPredeformation B hZ X hk hdim iΛ).category

/-- The comparison of morphisms preserves identities. -/
theorem toCurveDeformationMorphism_id (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    SchemeDeformationCategory.toCurveDeformationMorphism B hZ hk hdim iΛ (𝟙 P) =
      (@CategoryStruct.id (curvesPredeformation B hZ X hk hdim iΛ).carrier _
        (P.toCurveDeformation B hZ hk hdim iΛ)) := by
  refine DeformationMorphism.ext_of_components _ _ _ _ rfl (CurveFamily.Hom.ext ?_ ?_)
  · show integerSiteMap B hZ _ _ (baseSpecMap (𝟙 P.base)) = 𝟙 _
    rw [baseSpecMap_id, integerSiteMap_id]
  · show schemeSpaceMap (integerSiteMap B hZ _ _ (𝟙 P.scheme)) = 𝟙 _
    rw [integerSiteMap_id]
    exact (schemeSpaceFunctor B integerBase hZ).map_id _

/-- The comparison of morphisms preserves composition. -/
theorem toCurveDeformationMorphism_comp {P Q R : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (f : P ⟶ Q) (g : Q ⟶ R) :
    SchemeDeformationCategory.toCurveDeformationMorphism B hZ hk hdim iΛ (f ≫ g) =
      @CategoryStruct.comp (curvesPredeformation B hZ X hk hdim iΛ).carrier _ _ _ _
        (SchemeDeformationCategory.toCurveDeformationMorphism B hZ hk hdim iΛ f)
        (SchemeDeformationCategory.toCurveDeformationMorphism B hZ hk hdim iΛ g) := by
  refine DeformationMorphism.ext_of_components _ _ _ _ rfl (CurveFamily.Hom.ext ?_ ?_)
  · show integerSiteMap B hZ _ _ (baseSpecMap (f.base ≫ g.base)) =
      integerSiteMap B hZ _ _ (baseSpecMap g.base) ≫ integerSiteMap B hZ _ _ (baseSpecMap f.base)
    rw [baseSpecMap_comp, integerSiteMap_comp]
  · show schemeSpaceMap (integerSiteMap B hZ _ _ (g.map ≫ f.map)) =
      schemeSpaceMap (integerSiteMap B hZ _ _ g.map) ≫
        schemeSpaceMap (integerSiteMap B hZ _ _ f.map)
    rw [← schemeSpaceMap_comp, integerSiteMap_comp]

/-- **The comparison functor `Def_X ⟶ 𝓕_{Curves, k, x₀}`**: a flat deformation of `X` over an
object of `𝒞_Λ` is a deformation of the point `x₀` of the stack of curves classifying `X`. -/
def schemeDeformationToCurves :
    SchemeDeformationCategory (Λ := Λ) (k := k) X ⥤ (curvesPredeformation B hZ X hk hdim iΛ).carrier
    where
  obj P := P.toCurveDeformation B hZ hk hdim iΛ
  map f := SchemeDeformationCategory.toCurveDeformationMorphism B hZ hk hdim iΛ f
  map_id P := toCurveDeformationMorphism_id B hZ X hk hdim iΛ P
  map_comp f g := toCurveDeformationMorphism_comp B hZ X hk hdim iΛ f g

end Deformation.Examples

namespace Deformation.Examples

open Deformation.Artin

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
variable (X : Over (Spec (.of k))) [IsProper X.hom] (hk : B.Contains (Spec (.of k)))
  (hdim : topologicalKrullDim X.left ≤ 1) (iΛ : Spec (.of Λ) ⟶ integerBase)

/-- The base component of a morphism of `𝓕_{Curves, k, x₀}` between two deformations coming
from deformations of `X` is the map of spectra of its arrow of `𝒞_Λ`. -/
theorem baseMap_eq_integerSiteMap_baseSpecMap {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (m : DeformationMorphism iΛ (curvesToSchemesOver B hZ) (curveFamilyOfScheme X B hZ hk hdim)
      (curvesToSchemesOver_obj_curveFamilyOfScheme X B hZ hk hdim iΛ)
      (P.toCurveDeformation B hZ hk hdim iΛ) (Q.toCurveDeformation B hZ hk hdim iΛ)) :
    m.arrow.baseMap = integerSiteMap B hZ (contains_baseSpec B hk Q.base)
      (contains_baseSpec B hk P.base) (baseSpecMap m.ringHom) := by
  exact eq_integerSiteMap_of_map_eq m.arrow_base

/-- **The comparison functor is faithful**: a morphism of deformations of `X` is determined by
its arrow of `𝒞_Λ` and its morphism of total spaces, and the latter is determined by the
morphism of algebraic spaces it induces. -/
instance schemeDeformationToCurves_faithful :
    (schemeDeformationToCurves B hZ X hk hdim iΛ).Faithful where
  map_injective {P Q} f g h := by
    have h' : SchemeDeformationCategory.toCurveDeformationMorphism B hZ hk hdim iΛ f =
        SchemeDeformationCategory.toCurveDeformationMorphism B hZ hk hdim iΛ g := h
    have hr : f.base = g.base := congrArg DeformationMorphism.ringHom h'
    have ht := congrArg (fun m => m.arrow.totalMap) h'
    change schemeSpaceMap (integerSiteMap B hZ _ _ f.map) =
      schemeSpaceMap (integerSiteMap B hZ _ _ g.map) at ht
    exact SchemeDeformationCategory.Hom.ext hr
      (congrArg (BigFppfOver.toScheme B integerBase hZ).map (schemeSpaceMap_injective ht))

/-- **The comparison functor is full**: a morphism of families of curves between two
deformations of `X` is a cartesian square of the algebraic spaces they represent, whose
morphism of total spaces comes from a morphism of schemes because reading a scheme as an
algebraic space is fully faithful; the square of schemes is then cartesian, and the compatibility
with the arrows from `x₀` is the compatibility with the identifications of the special fibres. -/
instance schemeDeformationToCurves_full :
    (schemeDeformationToCurves B hZ X hk hdim iΛ).Full where
  map_surjective {P Q} m₀ := by
    let m : DeformationMorphism iΛ (curvesToSchemesOver B hZ)
        (curveFamilyOfScheme X B hZ hk hdim)
        (curvesToSchemesOver_obj_curveFamilyOfScheme X B hZ hk hdim iΛ)
        (P.toCurveDeformation B hZ hk hdim iΛ) (Q.toCurveDeformation B hZ hk hdim iΛ) := m₀
    have hb := baseMap_eq_integerSiteMap_baseSpecMap B hZ X hk hdim iΛ m
    obtain ⟨g, hg⟩ : ∃ g : integerSiteObject B hZ (Q.contains_scheme B hk) ⟶
        integerSiteObject B hZ (P.contains_scheme B hk), schemeSpaceMap g = m.arrow.totalMap :=
      ⟨(schemeSpaceFunctorFullyFaithful _ _).preimage m.arrow.totalMap,
        (schemeSpaceFunctorFullyFaithful _ _).map_preimage _⟩
    refine ⟨{ base := m.ringHom
              map := (BigFppfOver.toScheme B integerBase hZ).map g
              cartesian := ?_
              special_compat := ?_ }, ?_⟩
    · have hc := m.arrow.cartesian
      rw [← hg, hb, ← integerSiteMap_toScheme_map g] at hc
      exact isPullback_of_isPullback_schemeSpaceMap_integerSiteMap hc
    · have htri := congrArg CurveFamily.Hom.totalMap m.triangle
      change schemeSpaceMap (integerSiteMap B hZ _ _ Q.specialMap) ≫ m.arrow.totalMap =
        schemeSpaceMap (integerSiteMap B hZ _ _ P.specialMap) at htri
      rw [← hg] at htri
      have htri' : schemeSpaceMap (integerSiteMap B hZ (contains_left_of_isProper B hk)
          (Q.contains_scheme B hk) Q.specialMap ≫ g) =
          schemeSpaceMap (integerSiteMap B hZ _ _ P.specialMap) := by
        rw [schemeSpaceMap_comp]
        exact htri
      have := congrArg (BigFppfOver.toScheme B integerBase hZ).map (schemeSpaceMap_injective htri')
      rwa [Functor.map_comp] at this
    · refine DeformationMorphism.ext_of_components _ _ _ _ rfl (CurveFamily.Hom.ext hb.symm ?_)
      exact (congrArg schemeSpaceMap (integerSiteMap_toScheme_map g)).trans hg

/-- **A deformation of `x₀` whose total space is a scheme comes from a deformation of `X`.** If
the total space of the family of curves of a deformation `y` of `x₀` over an object `A` of `𝒞_Λ`
is represented by a scheme `T` of the site, then `T` is flat over `Spec A` with special fibre `X`,
and `y` is isomorphic over `A` to the image of that deformation of `X`. -/
theorem exists_iso_schemeDeformationToCurves_obj_of_iso_schemeSpace
    (y : DeformationObject iΛ (curvesToSchemesOver B hZ) (curveFamilyOfScheme X B hZ hk hdim)
      (curvesToSchemesOver_obj_curveFamilyOfScheme X B hZ hk hdim iΛ))
    (T : BigFppfOver B integerBase hZ) (e : y.point.total ≅ schemeSpace T) :
    ∃ (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
      (φ : (schemeDeformationToCurves B hZ X hk hdim iΛ).obj P ≅ y),
      (curvesPredeformation B hZ X hk hdim iΛ).projection.IsHomLift
        (𝟙 ((curvesPredeformation B hZ X hk hdim iΛ).projection.obj y)) φ.hom := by
  obtain ⟨A, ⟨⟨⟨S, hS⟩, ⟨⟨⟩⟩, sHom⟩, total, toBase, hflat, hproper, hfp, hrd⟩, arrow, hbase,
    harrow⟩ := y
  obtain rfl : S = Spec (.of A) := congrArg Over.left hbase
  obtain rfl : sHom = ObjectProperty.homMk (specULiftZIsTerminal.from _) :=
    ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _)
  obtain ⟨⟨T, hT⟩, ⟨⟨⟩⟩, tHom⟩ := T
  obtain rfl : tHom = ObjectProperty.homMk (specULiftZIsTerminal.from _) :=
    ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _)
  have hA : B.Contains (baseSpec A) := hS
  -- the structure morphism and the special fibre, as morphisms of schemes
  obtain ⟨g, hg⟩ : ∃ g : T ⟶ baseSpec A,
      schemeSpaceMap (integerSiteMap B hZ hT hA g) = e.inv ≫ toBase :=
    exists_schemeSpaceMap_integerSiteMap_eq _
  obtain ⟨sp, hsp⟩ : ∃ sp : X.left ⟶ T,
      schemeSpaceMap (integerSiteMap B hZ (contains_left_of_isProper B hk) hT sp) =
        arrow.totalMap ≫ e.hom :=
    exists_schemeSpaceMap_integerSiteMap_eq _
  have hb : arrow.baseMap = integerSiteMap B hZ hk hA (residueSpecMap A) := by
    exact eq_integerSiteMap_of_map_eq harrow
  have flat : Flat g := by
    refine (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      Flat.isEtaleLocalOnSourceAndTarget (integerSiteMap B hZ hT hA g)).1 ?_
    have h₁ := (Space.holdsOnEveryEtaleChart_precomp_iso B integerBase hZ
      (@Flat.{u}) ((ObjectProperty.ι _).mapIso e.symm) toBase.hom).1 hflat
    have h₂ : yoneda.map (integerSiteMap B hZ hT hA g) =
        ((ObjectProperty.ι _).mapIso e.symm).hom ≫ toBase.hom :=
      congrArg (fun φ => φ.hom) hg
    rw [h₂]
    exact h₁
  have cart : IsPullback sp X.hom g (residueSpecMap A) := by
    have hc := IsPullback.of_iso arrow.cartesian (Iso.refl _) e (Iso.refl _) (Iso.refl _)
      (fst' := arrow.totalMap ≫ e.hom) (f' := e.inv ≫ toBase)
      (snd' := (curveFamilyOfScheme X B hZ hk hdim).toBase) (g' := schemeSpaceMap arrow.baseMap)
      (by simp) (by simp) (by simp)
      (by simp)
    rw [← hsp, ← hg, hb] at hc
    exact isPullback_of_isPullback_schemeSpaceMap_integerSiteMap hc
  let P : SchemeDeformationCategory (Λ := Λ) (k := k) X :=
    { base := A
      scheme := T
      toBase := g
      flat := flat
      specialMap := sp
      specialCartesian := cart }
  have hid' : schemeSpaceMap (𝟙 (integerSiteObject B hZ hA)) = 𝟙 _ :=
    (schemeSpaceFunctor B integerBase hZ).map_id _
  -- the comparison isomorphism, with identity base components
  let hom : DeformationMorphism iΛ (curvesToSchemesOver B hZ) (curveFamilyOfScheme X B hZ hk hdim)
      (curvesToSchemesOver_obj_curveFamilyOfScheme X B hZ hk hdim iΛ)
      (P.toCurveDeformation B hZ hk hdim iΛ)
      ⟨A, ⟨integerSiteObject B hZ hA, total, toBase, hflat, hproper, hfp, hrd⟩, arrow, hbase,
        harrow⟩ :=
    { ringHom := 𝟙 A
      arrow :=
        { baseMap := 𝟙 _
          totalMap := e.hom
          cartesian := by
            show IsPullback e.hom toBase (schemeSpaceMap (integerSiteMap B hZ hT hA g))
                (schemeSpaceMap (𝟙 (integerSiteObject B hZ hA)))
            have h : IsPullback e.hom toBase (e.inv ≫ toBase) (𝟙 _) :=
              IsPullback.of_iso (IsPullback.id_horiz toBase) (Iso.refl _) e (Iso.refl _)
                (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
            exact (congrArg (fun a => IsPullback e.hom toBase a
              (schemeSpaceMap (𝟙 (integerSiteObject B hZ hA)))) hg).mpr
                ((congrArg (fun b => IsPullback e.hom toBase (e.inv ≫ toBase) b) hid').mpr h) }
      triangle := CurveFamily.Hom.ext ((Category.comp_id _).trans hb) hsp.symm
      arrow_base := by
        show 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = baseSpecMap (𝟙 A)
        rw [baseSpecMap_id]
        simp }
  let inv : DeformationMorphism iΛ (curvesToSchemesOver B hZ) (curveFamilyOfScheme X B hZ hk hdim)
      (curvesToSchemesOver_obj_curveFamilyOfScheme X B hZ hk hdim iΛ)
      ⟨A, ⟨integerSiteObject B hZ hA, total, toBase, hflat, hproper, hfp, hrd⟩, arrow, hbase,
        harrow⟩
      (P.toCurveDeformation B hZ hk hdim iΛ) :=
    { ringHom := 𝟙 A
      arrow :=
        { baseMap := 𝟙 _
          totalMap := e.inv
          cartesian := by
            show IsPullback e.inv (schemeSpaceMap (integerSiteMap B hZ hT hA g)) toBase
                (schemeSpaceMap (𝟙 (integerSiteObject B hZ hA)))
            have h : IsPullback e.inv (e.inv ≫ toBase) toBase (𝟙 _) :=
              IsPullback.of_iso (IsPullback.id_horiz (e.inv ≫ toBase)) (Iso.refl _) e.symm
                (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
            exact (congrArg (fun a => IsPullback e.inv a toBase
              (schemeSpaceMap (𝟙 (integerSiteObject B hZ hA)))) hg).mpr
                ((congrArg (fun b => IsPullback e.inv (e.inv ≫ toBase) toBase b) hid').mpr h) }
      triangle := CurveFamily.Hom.ext ((Category.comp_id _).trans hb.symm)
        ((congrArg (fun φ => φ ≫ e.inv) hsp).trans ((Category.assoc _ _ _).trans
          ((congrArg (arrow.totalMap ≫ ·) e.hom_inv_id).trans (Category.comp_id _))))
      arrow_base := by
        show 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = baseSpecMap (𝟙 A)
        rw [baseSpecMap_id]
        simp }
  refine ⟨P, ⟨hom, inv, ?_, ?_⟩, ?_⟩
  · exact DeformationMorphism.ext_of_components _ _ _ _ (Category.comp_id _)
      (CurveFamily.Hom.ext (Category.comp_id _) e.inv_hom_id)
  · exact DeformationMorphism.ext_of_components _ _ _ _ (Category.comp_id _)
      (CurveFamily.Hom.ext (Category.comp_id _) e.hom_inv_id)
  · let φ : (schemeDeformationToCurves B hZ X hk hdim iΛ).obj P ⟶
        (show (curvesPredeformation B hZ X hk hdim iΛ).carrier from
          ⟨A, ⟨integerSiteObject B hZ hA, total, toBase, hflat, hproper, hfp, hrd⟩, arrow, hbase,
            harrow⟩) := hom
    exact IsHomLift.map (p := (curvesPredeformation B hZ X hk hdim iΛ).projection) φ

/-- The comparison functor as a morphism of categories over `𝒞_Λ`: it preserves the object of
`𝒞_Λ` a deformation lives over. -/
def schemeDeformationToCurvesBased :
    BasedFunctor (BasedCategory.ofFunctor (schemeDeformationCategoryProjection (Λ := Λ) X))
      (BasedCategory.ofFunctor (curvesPredeformation B hZ X hk hdim iΛ).projection) where
  toFunctor := schemeDeformationToCurves B hZ X hk hdim iΛ
  w := rfl

/-- The comparison functor followed by the structure functor of `𝓕_{Curves, k, x₀}` is the
structure functor of `Def_X`. -/
theorem schemeDeformationToCurvesBased_comp_baseProjection :
    BasedFunctor.comp (schemeDeformationToCurvesBased B hZ X hk hdim iΛ)
        (baseProjection (curvesPredeformation B hZ X hk hdim iΛ).projection) =
      baseProjection (schemeDeformationCategoryProjection (Λ := Λ) X) :=
  rfl

end Deformation.Examples
