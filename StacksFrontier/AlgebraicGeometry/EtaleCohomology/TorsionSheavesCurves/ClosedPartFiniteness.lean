module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DenseOpenReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DenseOpenReductionSupplement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SpecializationFiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Coefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointDomination
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap

/-!
# Finiteness of the sections of a constructible sheaf on a finite scheme

The proof of Stacks Tag 0GJA uses that for a constructible abelian sheaf `F` on `X_étale` and the
inclusion `i : Z ⟶ X` of a finite set of closed points, `H⁰(X, i_* i⁻¹ F) = H⁰(Z, i⁻¹ F)` is
finite, being the sum of the stalks of `F` at the points of `Z`, which are finite as `F` is
constructible. This file proves it.

The three steps are general. A constructible sheaf of sets has finite stalks at every geometric
point: the point lies in a stratum, on which the sheaf is finite locally constant, and the stalk
is that of the restriction to the stratum (Tag 03Q1). An abelian sheaf on Mathlib's small étale
site whose corresponding sheaf on the small étale site of Tag 021B is constructible therefore has
finite stalks at every geometric point, the stalk of the underlying sheaf of sets being the
underlying set of the stalk. And the global sections of an abelian sheaf on the small étale site
of any scheme inject into the product of its stalks at the geometric points over the points of
the scheme, a section with vanishing germs vanishing on an étale covering.

## Main results

* `AlgebraicGeometry.finite_etaleStalk_of_isConstructibleSetSheaf`: the geometric stalks of a
  constructible sheaf of sets are finite.
* `Stacks.EtaleCohomology.finite_sheafFiber_of_isConstructibleEtaleSheaf`: the geometric stalks
  of a constructible abelian sheaf on Mathlib's small étale site are finite.
* `Stacks.EtaleCohomology.injective_globalSections_toPresheafFiber`: global sections inject into
  the product of the stalks at the points of the scheme.
* `Stacks.EtaleCohomology.finite_sheafH_zero_of_isConstructibleEtaleSheaf`: on a scheme with
  finitely many points, `H⁰` of a constructible abelian sheaf is finite.
* `Stacks.EtaleCohomology.finite_sheafH_zero_directImage_inverseImage`: `H⁰(X, i_* i⁻¹ F)` is
  finite for `F` constructible and `i` a closed immersion of a scheme with finitely many points.
* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_extensionByZero_of_constructible`: Tag 0GJA
  towards the middle term, with the finiteness input discharged.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

/-- **The geometric stalks of a constructible sheaf of sets are finite.** The image of the
geometric point lies in an affine open of `X`, and in one stratum of the constructible
stratification of that open which the sheaf admits; the restriction of the sheaf to that stratum
is finite locally constant, so its stalks are finite by Tag 0GJ7, and the stalk of the sheaf at
the given point is the stalk of the restriction at a geometric point of the stratum above the same
point of `X` (Tag 03Q1). -/
theorem finite_etaleStalk_of_isConstructibleSetSheaf (B : BigEtaleSite.{u}) (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B X F) (t : GeometricPoint X.obj) :
    Finite (etaleStalk B X.obj X.property t F.obj) := by
  obtain ⟨U, hU⟩ : ∃ U : X.obj.affineOpens, t.hom default ∈ (U.1 : Set X.obj) := by
    have h : t.hom default ∈ (⊤ : X.obj.Opens) := trivial
    rw [← iSup_affineOpens_eq_top X.obj] at h
    exact TopologicalSpace.Opens.mem_iSup.mp h
  obtain ⟨s, hs⟩ := hF U
  obtain ⟨i, z, hz⟩ : ∃ (i : Fin s.n) (z : (s.piece i).obj),
      (B.inclusion.map (s.inclusion i)).base z = t.hom default := by
    have hx : t.hom default ∈ ⋃ i, Set.range (B.inclusion.map (s.inclusion i)).base := by
      rwa [← s.covers]
    exact Set.mem_iUnion.mp hx
  set t' := GeometricPoint.ofPoint (s.piece i).obj z
  have hbase : (t'.map (B.inclusion.map (s.inclusion i))).hom default = t.hom default := by
    show (B.inclusion.map (s.inclusion i)).base (t'.hom default) = t.hom default
    rwa [show t'.hom default = z from GeometricPoint.ofPoint_liesOver (s.piece i).obj z]
  have hfin :=
    (@finite_etaleStalk_and_bijective_specializationMapOnStalks_of_isFiniteLocallyConstant B
      (s.piece i).obj (s.piece i).property _ (hs i)).1 t'
  exact @Finite.of_equiv _ _ hfin ((smallEtalePullbackSheafFiberIso B (s.inclusion i) t'
      (Type (u + 1))).app F ≪≫
    (etaleStalkPresheafFunctorIsoOfEqBase B X.obj X.property hbase (Type (u + 1))).app
      F.obj).toEquiv

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

section Stalks

variable {X : Scheme.{u}}

/-- The forgetful functor from abelian groups in universe `u + 1` to types preserves filtered
colimits indexed by categories in universe `u`. -/
instance : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
  preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _

/-- The stalk of the underlying sheaf of sets of an abelian sheaf on Mathlib's small étale site,
at a geometric point, is the stalk on the small étale site of Tag 021B of the corresponding sheaf
of sets. -/
def sheafFiberSheafComposeForgetIso (B : BigEtaleSite.{u}) (hX : B.Contains X)
    (s : GeometricPoint X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Scheme.pointSmallEtale s.hom).sheafFiber.obj
        ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj F) ≅
      (geometricSitePoint B (B.obj X hX) s).sheafFiber.obj
        ((sheafCompose (SmallEtale.topology B X hX) (forget AddCommGrpCat.{u + 1})).obj
          ((toBoundedSiteAb B hX).obj F)) :=
  (Scheme.pointSmallEtale s.hom).sheafFiber.mapIso
      ((SmallEtale.sheafEquiv B X hX (Type (u + 1))).counitIso.app _).symm ≪≫
    (sheafFiberIsoOfAdjOfFiberIso (geometricSitePoint B (B.obj X hX) s)
      (Scheme.pointSmallEtale s.hom) (SmallEtale.toEtaleSite B X hX)
      (toEtaleSiteFiberIso B X hX s)
      (SmallEtale.sheafEquiv B X hX (Type (u + 1))).toAdjunction).app _

/-- **The geometric stalks of a constructible abelian sheaf are finite**, on Mathlib's small étale
site: the underlying sheaf of sets of the corresponding sheaf on the small étale site of Tag 021B
is constructible, its stalks are finite, and the underlying set of a stalk is the stalk of the
underlying sheaf of sets. -/
theorem finite_sheafFiber_of_isConstructibleEtaleSheafIn (B : BigEtaleSite.{u})
    (hX : B.Contains X) {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hF : IsConstructibleEtaleSheafIn B hX F) (s : GeometricPoint X) :
    Finite ((smallEtaleStalkAb s.hom).obj F) := by
  have hset := isConstructibleSetSheaf_underlying B (B.obj X hX)
    (smallEtaleUnderlyingSetCommutes B (B.obj X hX)) hF
  have hfin := finite_etaleStalk_of_isConstructibleSetSheaf B (B.obj X hX) _ hset s
  have e := (((Scheme.pointSmallEtale s.hom).sheafFiberCompIso
      (forget AddCommGrpCat.{u + 1})).app F).symm ≪≫ sheafFiberSheafComposeForgetIso B hX s F
  exact @Finite.of_equiv _ _ hfin e.symm.toEquiv

/-- **The geometric stalks of a constructible abelian sheaf are finite**, on Mathlib's small étale
site. -/
theorem finite_sheafFiber_of_isConstructibleEtaleSheaf
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hF : IsConstructibleSmallEtaleSheaf F)
    (s : GeometricPoint X) :
    Finite ((smallEtaleStalkAb s.hom).obj F) := by
  obtain ⟨B, hX, hB⟩ := hF
  exact finite_sheafFiber_of_isConstructibleEtaleSheafIn B hX hB s

/-- The geometric point at a point `x`, viewed as a lift of itself through the final object of
the small étale site. -/
def pointSmallEtaleFinalElement (x : X) :
    (Scheme.pointSmallEtale (GeometricPoint.ofPoint X x).hom).fiber.obj (Scheme.Etale.mk (𝟙 X)) :=
  Over.homMk (GeometricPoint.ofPoint X x).hom (by simp)

/-- **Global sections inject into the product of the geometric stalks.** On the small étale site
of a scheme `X`, a global section of an abelian sheaf whose germs at the geometric points over all
points of `X` vanish is zero: each germ vanishes on an étale neighbourhood, and these
neighbourhoods cover `X`. -/
theorem injective_globalSections_toPresheafFiber
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Injective (fun (a : ToType (F.obj.obj (op (Scheme.Etale.mk (𝟙 X))))) (x : X) =>
      (Scheme.pointSmallEtale (GeometricPoint.ofPoint X x).hom).toPresheafFiber
        (Scheme.Etale.mk (𝟙 X)) (pointSmallEtaleFinalElement x) F.obj a) := by
  intro a b hab
  have h : ∀ x : X, ∃ (Y : X.Etale) (f : Y ⟶ Scheme.Etale.mk (𝟙 X))
      (y : (Scheme.pointSmallEtale (GeometricPoint.ofPoint X x).hom).fiber.obj Y),
      (Scheme.pointSmallEtale (GeometricPoint.ofPoint X x).hom).fiber.map f y =
        pointSmallEtaleFinalElement x ∧ F.obj.map f.op a = F.obj.map f.op b := fun x =>
    (GrothendieckTopology.Point.toPresheafFiber_eq_iff' _ _ _ a b).1 (congrFun hab x)
  choose Y f y hy hf using h
  have hcov : Sieve.ofArrows Y f ∈ X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, ?_⟩
    let p : Spec (.of (GeometricPoint.ofPoint X x).residueField) := default
    have h1 : (y x).left ≫ (f x).left = (GeometricPoint.ofPoint X x).hom :=
      congrArg CommaMorphism.left (hy x)
    refine ⟨(y x).left p, ?_⟩
    show ((y x).left ≫ (f x).left) p = x
    rw [h1]
    exact GeometricPoint.ofPoint_liesOver X x
  have hsh := ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj F).property
  rw [isSheaf_iff_isSheaf_of_type] at hsh
  refine (hsh _ hcov).isSeparatedFor.ext fun Z g hg => ?_
  obtain ⟨x, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  show F.obj.map (h ≫ f x).op a = F.obj.map (h ≫ f x).op b
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hf x]

/-- **`H⁰` of a constructible abelian sheaf on a scheme with finitely many points is finite.** -/
theorem finite_sheafH_zero_of_isConstructibleEtaleSheaf [Finite X]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hF : IsConstructibleSmallEtaleSheaf F) :
    Finite (Sheaf.H.{u + 1} F 0) := by
  have : ∀ x : X, Finite (((Scheme.pointSmallEtale (GeometricPoint.ofPoint X x).hom).presheafFiber
      (A := AddCommGrpCat.{u + 1})).obj F.obj) := fun x =>
    finite_sheafFiber_of_isConstructibleEtaleSheaf hF _
  have : Finite (ToType (F.obj.obj (op (Scheme.Etale.mk (𝟙 X))))) :=
    Finite.of_injective _ (injective_globalSections_toPresheafFiber F)
  exact Finite.of_equiv _ (Sheaf.H.equiv₀ F (isTerminalEtaleMkId X)).toEquiv.symm

end Stalks

section ClosedPart

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- **`H⁰(X, i_* i⁻¹ F)` is finite** for a constructible abelian sheaf `F` and a closed immersion
`i : Z ⟶ X` of a scheme with finitely many points: it is `H⁰(Z, i⁻¹ F)`, the direct image along
a closed immersion not changing cohomology, and `i⁻¹ F` is constructible (Tag 095G). -/
theorem finite_sheafH_zero_directImage_inverseImage [Finite Z]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hF : IsConstructibleSmallEtaleSheaf F) :
    Finite (Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, u + 1} i).obj
      ((etaleAbelianInverseImage.{u, u + 1} i).obj F)) 0) := by
  let : HasExt.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    hasExt_of_enoughInjectives.{u + 1} _
  have := finite_sheafH_zero_of_isConstructibleEtaleSheaf
    (IsConstructibleSmallEtaleSheaf.inverseImage_of_mono i hF)
  exact Finite.of_equiv _ (sheafHSmallEtalePushforwardAddEquiv i
    ((etaleAbelianInverseImage.{u, u + 1} i).obj F) 0).toEquiv

end ClosedPart

/-- A scheme finite over an algebraically closed field has finitely many points. -/
theorem finite_of_isFinite_over_field {k : Type u} [Field k] [IsAlgClosed k] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) [IsFinite g] : Finite Z := by
  have : DiscreteTopology Z := discreteTopology_of_isFinite_over_field k g
  have : IsAffine Z := (isAffine_isClosed_isSepClosed_of_isFinite g).1
  exact finite_of_compact_of_discrete

namespace TorsionCurveAssertions

variable {k : Type u} [Field k] [IsAlgClosed k] {X Z U : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ) [IsFinite (i ≫ f)]

include hij in
/-- **Stacks Tag 0GJA, towards the middle term**, for a constructible sheaf: on a Noetherian
scheme over an algebraically closed field, with `Z` finite over `k` and `U` its open complement,
the eight assertions for `j_! j⁻¹ F` give them for a constructible `F`. -/
theorem of_extensionByZero_of_constructible [AlgebraicGeometry.IsNoetherian X]
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hF : IsConstructibleSmallEtaleSheaf F)
    (h : TorsionCurveAssertions f ((extensionByZero.{u, u + 1} j).obj
      ((etaleRestriction.{u, u + 1} j).obj F))) :
    TorsionCurveAssertions f F :=
  have := finite_of_isFinite_over_field (i ≫ f)
  of_extensionByZero f i j hij F (fun _ => finite_sheafH_zero_directImage_inverseImage i hF) h

end TorsionCurveAssertions

end Stacks.EtaleCohomology

end
