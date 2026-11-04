module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DirectSumsOfEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.DerivedGlobalSectionsAdditive
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.LocallyConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.StrictHenselizationDependence
import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.StrictHenselizationLocallyConstant

/-!
# Local acyclicity relative to a locally constant torsion sheaf

Let `f : X ⟶ S` be a locally acyclic morphism of schemes and `F` a locally constant abelian sheaf
on `X_étale` whose stalk at every geometric point `x` is torsion with element orders prime to the
characteristic of the residue field at `x`. [Stacks, Tag 0GJR] says that `f` is locally acyclic
relative to `F`.

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/LocalAcyclicity/LocallyConstantCoefficients.lean`
proves the dévissage of the coefficient group, `Stacks.TorsionDevissage.isIso_app_of_torsion`, and
the statement of the tag granted four inputs. This file proves those inputs and so the tag:

* the filtered colimit step, Tag 03Q5 for the affine variety of vanishing cycles, is proved here;
* that the canonical map `α_{K,x,t}` has the same iso-status at two objects of `D(X_étale)` whose
  inverse images on `Spec 𝒪^{sh}_{X,x}` agree is
  `AlgebraicGeometry.isIso_vanishingCyclesFibreMap_app_iff_of_derivedPullbackIso`;
* that the inverse image of a locally constant sheaf on `Spec 𝒪^{sh}_{X,x}` is the constant sheaf
  with value its stalk at `x` is
  `AlgebraicGeometry.strictHenselizationDerivedPullbackConstantComplexIso`;
* additivity of unbounded derived global sections on each variety of vanishing cycles is the
  instance `Stacks.EtaleCohomology.smallEtaleDerivedGlobalSections_additive`.

## Main results

* `Stacks.SingleDegreeColimits.preservesColimitsOfShape_singleFunctorCompHomologyFunctor` —
  degree-`n` cohomology of an object placed in degree zero preserves all colimits.
* `AlgebraicGeometry.isIso_vanishingCyclesFibreMap_app_constantComplex_of_isColimit` —
  **[Stacks, Tag 03Q5]** for the canonical map at a variety of vanishing cycles: the locus where
  `α` is an isomorphism on constant coefficients is closed under filtered colimits of the
  coefficient group.
* `AlgebraicGeometry.isLocallyAcyclicRelative_of_isLocallyConstant_unconditional` —
  **[Stacks, Tag 0GJR]**, with no hypotheses beyond the source's.

## Closure of the iso-locus under filtered colimits

Tag 03Q5 is not phrased here as "`α` preserves filtered colimits": `D(X_étale)` has no filtered
colimits of the relevant diagrams, and the source uses none. What is used is that the locus where
`α` is invertible on *constant* coefficients is closed under filtered colimits of the coefficient
group. A map of `D(Ab)` is invertible as soon as it is so on cohomology in every degree
(`CategoryTheory.DerivedCategory.isIso_iff`), so it suffices to see that in each degree both sides
are functors of the coefficient group commuting with filtered colimits:

* below degree zero both sides vanish, the stalk side because it is an object placed in degree
  zero and the sections side by left t-exactness,
  `Stacks.DerivedFunctor.isGE_totalRightDerived_obj`;
* in degree `p ≥ 0` the stalk side is `M ↦ (constant sheaf M)_x` placed in degree zero, a
  composite of left adjoints with a functor that in each degree is either the identity or zero;
  and the sections side is `M ↦ H^p_étale(F_{x,t}, (constant sheaf M)|_{F_{x,t}})`, the inverse
  image being a left adjoint and `H^p_étale` of the affine `F_{x,t}` commuting with filtered
  colimits by Tag 03Q5 on the small étale site.

The comparison of the two descriptions with the two sides of `α` is
`Stacks.EtaleCohomology.constantStalkHomologyIso` and
`Stacks.EtaleCohomology.constantSectionsHomologyIso`; the second is where
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` is used.

## References

* [Stacks Project, Tag 0GJR](https://stacks.math.columbia.edu/tag/0GJR)
* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace Stacks.SingleDegreeColimits

/-! ### Degree-`n` cohomology of an object placed in degree zero

Both sides of the canonical map, evaluated on constant coefficients and read in a single degree,
are composites of functors out of abelian groups ending in
`DerivedCategory.singleFunctor _ 0 ⋙ DerivedCategory.homologyFunctor _ n` or in a right derived
functor. The two lemmas here say that the first of those preserves colimits: in degree zero it is
the identity, and in every other degree it vanishes. -/

/-- **A functor all of whose values are zero preserves every colimit.** The image of a cocone is
a cocone of zero objects with zero point, and a map out of a zero object is unique, so there is
exactly one map from the image point to any other cocone and the two conditions on it are
automatic. -/
theorem preservesColimit_of_isZero {J : Type*} [Category J] {C : Type*} [Category C]
    {D : Type*} [Category D] [HasZeroMorphisms D] (K : J ⥤ C) (F : C ⥤ D)
    (hF : ∀ Y, IsZero (F.obj Y)) : PreservesColimit K F where
  preserves {c} _ :=
    ⟨{ desc := fun _ => 0
       fac := fun _ j => (hF (K.obj j)).eq_of_src _ _
       uniq := fun _ _ _ => (hF c.pt).eq_of_src _ _ }⟩

/-- Degree-`n` cohomology of an object placed in degree zero vanishes for `n ≠ 0`. -/
private theorem isZero_singleFunctor_comp_homologyFunctor_obj {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {n : ℤ} (hn : n ≠ 0) (Y : C) :
    IsZero ((DerivedCategory.singleFunctor C 0 ⋙ DerivedCategory.homologyFunctor C n).obj Y) := by
  rcases lt_or_gt_of_ne hn with h | h
  · exact DerivedCategory.isZero_of_isGE _ 0 n h
  · exact DerivedCategory.isZero_of_isLE _ 0 n h

/-- **Degree-`n` cohomology of an object placed in degree zero preserves all colimits.** For
`n = 0` it is the identity functor, by
`CategoryTheory.DerivedCategory.singleFunctorCompHomologyFunctorIso`; for every other `n` an
object placed in degree zero has no cohomology in degree `n`, so the functor is zero. -/
theorem preservesColimitsOfShape_singleFunctorCompHomologyFunctor {C : Type*} [Category C]
    [Abelian C] [HasDerivedCategory C] (J : Type*) [Category J] (n : ℤ) :
    PreservesColimitsOfShape J
      (DerivedCategory.singleFunctor C 0 ⋙ DerivedCategory.homologyFunctor C n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact preservesColimitsOfShape_of_natIso
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).symm
  · exact ⟨fun {K} => preservesColimit_of_isZero K _
      (isZero_singleFunctor_comp_homologyFunctor_obj hn)⟩

end Stacks.SingleDegreeColimits

namespace Stacks.EtaleCohomology

-- `_root_` is load-bearing: the import closure contains declarations in the namespace
-- `Stacks.AlgebraicGeometry`, and inside `namespace Stacks.EtaleCohomology` a bare
-- `open AlgebraicGeometry` resolves to that one rather than to `_root_.AlgebraicGeometry`.
open _root_.AlgebraicGeometry Stacks.SingleDegreeColimits

attribute [local instance] HasDerivedCategory.standard

/-! ### The stalk side of the canonical map on constant coefficients -/

section Stalk

variable {X : Scheme.{u}} (x : GeometricPoint X) (n : ℤ)

/-- **The stalk side of the canonical map, on constant coefficients and in a single degree.**
The stalk functor is exact, so it carries a sheaf placed in degree zero to its stalk placed in
degree zero; the degree-`n` cohomology of the derived stalk of the constant complex is therefore
the composite of the constant sheaf functor, the stalk, and degree-`n` cohomology of an object
placed in degree zero.

The reassociations are written out because `(E ⋙ G) ⋙ H` and `E ⋙ G ⋙ H`, though definitionally
equal, are not unifiable as applications of `CategoryTheory.Functor.comp`. -/
def constantStalkHomologyIso :
    ((constantSheaf X.smallEtaleTopology Ab.{u + 1} ⋙
          DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0) ⋙
        smallEtaleDerivedStalkAb x.hom) ⋙ DerivedCategory.homologyFunctor Ab.{u + 1} n ≅
      constantSheaf X.smallEtaleTopology Ab.{u + 1} ⋙ smallEtaleStalkAb x.hom ⋙
        DerivedCategory.singleFunctor Ab.{u + 1} 0 ⋙
          DerivedCategory.homologyFunctor Ab.{u + 1} n :=
  Functor.associator
      (constantSheaf X.smallEtaleTopology Ab.{u + 1} ⋙
        DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0)
      (smallEtaleDerivedStalkAb x.hom) (DerivedCategory.homologyFunctor Ab.{u + 1} n) ≪≫
    Functor.associator (constantSheaf X.smallEtaleTopology Ab.{u + 1})
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0)
      (smallEtaleDerivedStalkAb x.hom ⋙ DerivedCategory.homologyFunctor Ab.{u + 1} n) ≪≫
    Functor.isoWhiskerLeft (constantSheaf X.smallEtaleTopology Ab.{u + 1})
      ((Functor.associator
            (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0)
            (smallEtaleDerivedStalkAb x.hom)
            (DerivedCategory.homologyFunctor Ab.{u + 1} n)).symm ≪≫
        Functor.isoWhiskerRight ((smallEtaleStalkAb x.hom).mapDerivedCategorySingleFunctor 0)
            (DerivedCategory.homologyFunctor Ab.{u + 1} n) ≪≫
          Functor.associator (smallEtaleStalkAb x.hom)
            (DerivedCategory.singleFunctor Ab.{u + 1} 0)
            (DerivedCategory.homologyFunctor Ab.{u + 1} n))

/-- **The stalk side commutes with filtered colimits of the coefficient group**, in every degree.
The constant sheaf functor and the stalk are left adjoints, and degree-`n` cohomology of an
object placed in degree zero preserves all colimits. -/
theorem preservesColimitsOfShape_constantStalkHomology (I : Type (u + 1)) [SmallCategory I] :
    PreservesColimitsOfShape I
      (((constantSheaf X.smallEtaleTopology Ab.{u + 1} ⋙
            DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0) ⋙
          smallEtaleDerivedStalkAb x.hom) ⋙ DerivedCategory.homologyFunctor Ab.{u + 1} n) :=
  let : PreservesColimitsOfShape I
      (DerivedCategory.singleFunctor Ab.{u + 1} 0 ⋙
        DerivedCategory.homologyFunctor Ab.{u + 1} n) :=
    preservesColimitsOfShape_singleFunctorCompHomologyFunctor I n
  preservesColimitsOfShape_of_natIso (constantStalkHomologyIso x n).symm

/-- **The stalk side vanishes outside degree zero**: it is an object placed in degree zero. -/
theorem isZero_constantStalkHomology (hn : n ≠ 0) (M : Ab.{u + 1}) :
    IsZero ((((constantSheaf X.smallEtaleTopology Ab.{u + 1} ⋙
          DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0) ⋙
        smallEtaleDerivedStalkAb x.hom) ⋙
        DerivedCategory.homologyFunctor Ab.{u + 1} n).obj M) := by
  exact IsZero.of_iso (isZero_singleFunctor_comp_homologyFunctor_obj hn _)
    ((constantStalkHomologyIso x n).app M)

end Stalk

/-! ### The sections side of the canonical map on constant coefficients -/

section Sections

variable {X T : Scheme.{u}} (π : T ⟶ X)

/-- **The sections side of the canonical map, on constant coefficients and in a non-negative
degree.** Inverse image is exact, so it carries a sheaf placed in degree zero to its inverse
image placed in degree zero; and the degree-`p` cohomology of unbounded derived global sections
of an object placed in degree zero is the classical `H^p_étale`, by
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`. So this side is the
composite of the constant sheaf functor, inverse image along `π`, and `H^p_étale(T, -)`.

The reassociations are written out because `(E ⋙ G) ⋙ H` and `E ⋙ G ⋙ H`, though definitionally
equal, are not unifiable as applications of `CategoryTheory.Functor.comp`. -/
def constantSectionsHomologyIso (p : ℕ) :
    ((constantSheaf X.smallEtaleTopology Ab.{u + 1} ⋙
          DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0) ⋙
        (smallEtaleDerivedPullbackAb π ⋙ smallEtaleDerivedGlobalSections T)) ⋙
        DerivedCategory.homologyFunctor Ab.{u + 1} (p : ℤ) ≅
      constantSheaf X.smallEtaleTopology Ab.{u + 1} ⋙ smallEtalePullbackAb π ⋙
        (Sheaf.Γ T.smallEtaleTopology Ab.{u + 1}).rightDerived p :=
  haveI := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse T
  Functor.associator
      (constantSheaf X.smallEtaleTopology Ab.{u + 1} ⋙
        DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0)
      (smallEtaleDerivedPullbackAb π ⋙ smallEtaleDerivedGlobalSections T)
      (DerivedCategory.homologyFunctor Ab.{u + 1} (p : ℤ)) ≪≫
    Functor.associator (constantSheaf X.smallEtaleTopology Ab.{u + 1})
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0)
      ((smallEtaleDerivedPullbackAb π ⋙ smallEtaleDerivedGlobalSections T) ⋙
        DerivedCategory.homologyFunctor Ab.{u + 1} (p : ℤ)) ≪≫
    Functor.isoWhiskerLeft (constantSheaf X.smallEtaleTopology Ab.{u + 1})
      (Functor.isoWhiskerLeft
          (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0)
          (Functor.associator (smallEtaleDerivedPullbackAb π)
            (smallEtaleDerivedGlobalSections T)
            (DerivedCategory.homologyFunctor Ab.{u + 1} (p : ℤ))) ≪≫
        (Functor.associator
            (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0)
            (smallEtaleDerivedPullbackAb π)
            (smallEtaleDerivedGlobalSections T ⋙
              DerivedCategory.homologyFunctor Ab.{u + 1} (p : ℤ))).symm ≪≫
          Functor.isoWhiskerRight
              ((smallEtalePullbackAb π).mapDerivedCategorySingleFunctor 0)
              (smallEtaleDerivedGlobalSections T ⋙
                DerivedCategory.homologyFunctor Ab.{u + 1} (p : ℤ)) ≪≫
            Functor.associator (smallEtalePullbackAb π)
                (DerivedCategory.singleFunctor (Sheaf T.smallEtaleTopology Ab.{u + 1}) 0)
                (smallEtaleDerivedGlobalSections T ⋙
                  DerivedCategory.homologyFunctor Ab.{u + 1} (p : ℤ)) ≪≫
              Functor.isoWhiskerLeft (smallEtalePullbackAb π)
                (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
                  (Sheaf.Γ T.smallEtaleTopology Ab.{u + 1})
                  (smallEtaleDerivedGlobalSections T)
                  (smallEtaleDerivedGlobalSectionsUnit T)
                  (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _) p))

/-- **The sections side commutes with filtered colimits of the coefficient group**, in every
non-negative degree, when `T` is quasi-compact and quasi-separated. The constant sheaf functor
and inverse image are left adjoints, and `H^p_étale(T, -)` commutes with filtered colimits by
[Stacks, Tag 03Q5]. -/
theorem preservesColimitsOfShape_constantSectionsHomology [CompactSpace T]
    [QuasiSeparatedSpace T] (p : ℕ) (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I
      (((constantSheaf X.smallEtaleTopology Ab.{u + 1} ⋙
            DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0) ⋙
          (smallEtaleDerivedPullbackAb π ⋙ smallEtaleDerivedGlobalSections T)) ⋙
          DerivedCategory.homologyFunctor Ab.{u + 1} (p : ℤ)) :=
  let : PreservesColimitsOfShape I (smallEtalePullbackAb π) :=
    ((smallEtaleAdjunctionAb π).leftAdjoint_preservesColimits).preservesColimitsOfShape
  let : PreservesColimitsOfShape I
      ((Sheaf.Γ T.smallEtaleTopology Ab.{u + 1}).rightDerived p) :=
    preservesColimitsOfShape_rightDerived_Γ_smallEtale.{u + 1} T p I
  preservesColimitsOfShape_of_natIso (constantSectionsHomologyIso π p).symm

/-- **The sections side vanishes below degree zero.** The inverse image of the constant complex
is again an object placed in degree zero, and unbounded derived global sections are left
t-exact. -/
theorem isZero_constantSectionsHomology (n : ℤ) (hn : n < 0) (M : Ab.{u + 1}) :
    IsZero ((((constantSheaf X.smallEtaleTopology Ab.{u + 1} ⋙
          DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0) ⋙
        (smallEtaleDerivedPullbackAb π ⋙ smallEtaleDerivedGlobalSections T)) ⋙
        DerivedCategory.homologyFunctor Ab.{u + 1} n).obj M) := by
  have := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse T
  have e : (DerivedCategory.singleFunctor (Sheaf T.smallEtaleTopology Ab.{u + 1}) 0).obj
        ((smallEtalePullbackAb π).obj
          ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj M)) ≅
      (smallEtaleDerivedPullbackAb π).obj
        ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj
          ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj M)) :=
    (((smallEtalePullbackAb π).mapDerivedCategorySingleFunctor 0).app
      ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj M)).symm
  have : ((smallEtaleDerivedPullbackAb π).obj
      ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj
        ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj M))).IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso e 0
  have := Stacks.DerivedFunctor.isGE_totalRightDerived_obj
    (Sheaf.Γ T.smallEtaleTopology Ab.{u + 1})
    ((smallEtaleDerivedPullbackAb π).obj
      ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj
        ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj M))) 0
  exact DerivedCategory.isZero_of_isGE
    ((smallEtaleDerivedGlobalSections T).obj ((smallEtaleDerivedPullbackAb π).obj
      ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj
        ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj M)))) 0 n hn

end Sections

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology Stacks.TorsionDevissage

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 03Q5 for the canonical map of Tag 0GJN on constant coefficients.** The locus where
the canonical map `α_{K,x,t}` is an isomorphism on constant coefficients is closed under filtered
colimits of the coefficient group: if `M` is the colimit of a filtered system `N` of abelian
groups and `α` is invertible on the constant complex with value `N i` for every `i`, then it is
invertible on the constant complex with value `M`.

A map of `D(Ab)` is invertible as soon as it is so on cohomology in every degree, and in each
degree both sides are functors of the coefficient group commuting with filtered colimits: below
degree zero both vanish, and in degree `p ≥ 0` the stalk side is `M ↦ (constant sheaf M)_x` placed
in degree zero while the sections side is `H^p_étale(F_{x,t}, -)` of the inverse image of the
constant sheaf. The variety of vanishing cycles is affine, hence quasi-compact and
quasi-separated, so [Stacks, Tag 03Q5] on its small étale site applies.

See the module docstring for why this is not phrased as preservation of filtered colimits by
`α`. -/
@[stacks 03Q5 "for the canonical map of Tag 0GJN at a variety of vanishing cycles, in the \
unbounded derived category: the locus where the map is invertible on constant coefficients is \
closed under filtered colimits of the coefficient group"]
theorem isIso_vanishingCyclesFibreMap_app_constantComplex_of_isColimit
    (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
    (f : X ⟶ S) (x : GeometricPoint X)
    (t : GeometricPoint (strictHenselization B S hS (x.map f)))
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I] (N : I ⥤ Ab.{u + 1})
    (c : Cocone N) (hc : IsColimit c)
    (hi : ∀ i, IsIso ((vanishingCyclesFibreMap B hX hS f x t).app
      (smallEtaleConstantComplexAb X (N.obj i)))) :
    IsIso ((vanishingCyclesFibreMap B hX hS f x t).app
      (smallEtaleConstantComplexAb X c.pt)) := by
  rw [DerivedCategory.isIso_iff]
  intro n
  set η := Functor.whiskerRight
    (Functor.whiskerLeft (smallEtaleConstantComplexFunctor X)
      (vanishingCyclesFibreMap B hX hS f x t))
    (DerivedCategory.homologyFunctor Ab.{u + 1} n)
  have hiη : ∀ i, IsIso (η.app (N.obj i)) := fun i => by
    have := hi i
    exact inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor Ab.{u + 1} n).map
      ((vanishingCyclesFibreMap B hX hS f x t).app
        (smallEtaleConstantComplexAb X (N.obj i)))))
  have : PreservesColimitsOfShape I
      ((smallEtaleConstantComplexFunctor X ⋙ smallEtaleDerivedStalkAb x.hom) ⋙
        DerivedCategory.homologyFunctor Ab.{u + 1} n) :=
    preservesColimitsOfShape_constantStalkHomology x n I
  rcases lt_or_ge n 0 with hn | hn
  · exact IsZero.isIso (isZero_constantStalkHomology x n (by omega) c.pt)
      (isZero_constantSectionsHomology (vanishingCyclesFibreToSource B hX hS f x t) n hn c.pt) _
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have : PreservesColimitsOfShape I
        ((smallEtaleConstantComplexFunctor X ⋙
            (smallEtaleDerivedPullbackAb (vanishingCyclesFibreToSource B hX hS f x t) ⋙
              smallEtaleDerivedGlobalSections (vanishingCyclesFibre B hX hS f x t))) ⋙
          DerivedCategory.homologyFunctor Ab.{u + 1} (p : ℤ)) :=
      preservesColimitsOfShape_constantSectionsHomology
        (vanishingCyclesFibreToSource B hX hS f x t) p I
    have : ∀ i, IsIso ((Functor.whiskerLeft N η).app i) := hiη
    have : IsIso (Functor.whiskerLeft N η) := NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit N η c hc

/-- **Stacks 0GJR.** Let `f : X ⟶ S` be a morphism of schemes and let `F` be a locally constant
abelian sheaf on `X_étale` whose stalk at every geometric point `x` is torsion with every element
order prime to the characteristic of the residue field at `x`. If `f` is locally acyclic, then
`f` is locally acyclic relative to `F`.

What is proved here is the dévissage: the reduction of the locally constant torsion coefficient
sheaf `F` to the constant sheaves `ℤ/nℤ` that local acyclicity speaks about. The stalk is written
as the filtered colimit of its finite subgroups, each of those splits as a finite direct sum of
cyclic groups of prime-to-`p` order, and local acyclicity is applied to each summand.

No hypothesis is supplied rather than derived. The two facts about the strict henselization that
the source's proof rests on are both proved: that the canonical map only sees the inverse image of
`K` on `Spec 𝒪^{sh}_{X,x}` is
`AlgebraicGeometry.isIso_vanishingCyclesFibreMap_app_iff_of_derivedPullbackIso`, and that a
locally constant sheaf has constant inverse image there, with value its stalk, is
`AlgebraicGeometry.strictHenselizationDerivedPullbackConstantComplexIso`. Nor is the filtered
colimit step a hypothesis: it is
`AlgebraicGeometry.isIso_vanishingCyclesFibreMap_app_constantComplex_of_isColimit`, Tag 03Q5 for
the variety of vanishing cycles, and neither is additivity of `RΓ` there, which is
`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSections_additive`.

`AlgebraicGeometry.isLocallyAcyclicRelative_of_isLocallyConstant` is the same statement with
those four facts taken as hypotheses. -/
@[stacks 0GJR]
theorem isLocallyAcyclicRelative_of_isLocallyConstant_unconditional
    (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
    (f : X ⟶ S)
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hFlc : Stacks.ConstantSheaf.IsLocallyConstant X.smallEtaleTopology F)
    (hFtors : ∀ (x : GeometricPoint X) (a : (smallEtaleStalkAb x.hom).obj F),
      ∃ n : ℕ, 0 < n ∧
        (ringChar x.residueField = 0 ∨ Nat.Coprime n (ringChar x.residueField)) ∧ n • a = 0)
    (hf : IsLocallyAcyclic B hX hS f) :
    IsLocallyAcyclicRelative B hX hS f
      ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F) := by
  intro x t
  rw [isIso_vanishingCyclesFibreMap_app_iff_of_derivedPullbackIso B hX hS f x t _ _
    (strictHenselizationDerivedPullbackConstantComplexIso B hX x F hFlc)]
  exact isIso_app_of_torsion
    (Functor.whiskerLeft (smallEtaleConstantComplexFunctor X)
      (vanishingCyclesFibreMap B hX hS f x t))
    (fun N c hc hi =>
      isIso_vanishingCyclesFibreMap_app_constantComplex_of_isColimit B hX hS f x t N c hc hi)
    (fun n hn hcop => hf x n hn hcop t)
    ((smallEtaleStalkAb x.hom).obj F) (hFtors x)

end AlgebraicGeometry

end
