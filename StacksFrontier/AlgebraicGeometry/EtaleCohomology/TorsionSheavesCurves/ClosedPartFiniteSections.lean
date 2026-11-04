module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StalkLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionOfConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ProperFinitenessStatement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite stalks of constructible sheaves, and the sections of `i_* i⁻¹ F` over a finite scheme

The geometric stalks of a constructible abelian sheaf on the small étale site of a scheme are
finite groups. Consequently, if `i : Z ⟶ X` is a morphism from a scheme with finitely many
points and `F` is a constructible abelian sheaf on `X_étale`, then `H⁰(X, i_* i⁻¹ F)` is finite.
This is the step "`H⁰(Z, i⁻¹F) = ⊕ F_{x̄_i}`, finite as the stalks of a constructible sheaf are
finite" in the proof of Stacks Tag 0GJA, where `i` is the inclusion of a finite set of closed
points of a curve.

## Main results

* `AlgebraicGeometry.finite_etaleStalk_of_isFiniteLocallyConstant`: the geometric stalks of a
  finite locally constant abelian sheaf on the small étale site of Tag 021B are finite.
* `AlgebraicGeometry.finite_etaleStalk_of_isConstructibleAbelianSheaf`: the geometric stalks of
  a constructible abelian sheaf on that site are finite.
* `AlgebraicGeometry.finite_pointSmallEtale_sheafFiber_of_isConstructibleEtaleAbelianSheaf` and
  `AlgebraicGeometry.finite_pointSmallEtale_ulift_sheafFiber_of_isConstructibleEtaleAbelianSheaf`:
  the same on Mathlib's small étale site, at the point of a geometric point and at its universe
  lift.
* `Stacks.EtaleCohomology.finite_H_zero_etaleAbelianDirectImage_inverseImage`: for a morphism
  `i : Z ⟶ X` from a scheme with finitely many points and a constructible abelian sheaf `F`,
  the group `H⁰(X, i_* i⁻¹ F)` is finite.

## Implementation notes

The coefficient universe is `AddCommGrpCat.{max (u + 1) v}`, the one in which étale cohomology
of `X : Scheme.{u}` is computed in this chapter; the existing constructibility results in
`Constructible/TorsionOfConstructible.lean` are stated at `AddCommGrpCat.{u + 1}` only, so the
stratum argument proving finiteness of stalks is carried out here at the general universe. It is
that of `AlgebraicGeometry.exists_nsmul_eq_zero_etaleStalk_of_isConstructibleAbelianSheaf`, with
"finite" in place of "torsion": the image of the geometric point lies in a stratum of the
stratification of an affine open, the stalk there is the stalk of the restriction to the stratum
(Stacks 03Q1, 04FN), and that restriction is finite locally constant.

The stalk on Mathlib's site is identified with the stalk on the site of Tag 021B through
`AlgebraicGeometry.sheafFiberIsoOfAdjOfFiberIso` applied to the equivalence
`AlgebraicGeometry.SmallEtale.sheafEquiv`, and the universe lift of a point is removed by
`CategoryTheory.GrothendieckTopology.Point.uliftPresheafFiberIso`.

For the cohomology group, `H⁰` is `Hom(ℤ, i_* i⁻¹ F) = Hom(i⁻¹ ℤ, i⁻¹ F)` by the adjunction
`i⁻¹ ⊣ i_*`. The universe lifts of the geometric points `x̄`, one over each point `x` of `Z`, are
a conservative family of points of `Z_étale`, so the stalk functors at them are jointly faithful
and a morphism `i⁻¹ ℤ ⟶ i⁻¹ F` is determined by its stalks; those are morphisms from
`(i⁻¹ ℤ)_{x̄} = ℤ` to the finite group `(i⁻¹ F)_{x̄} = F_{i(x̄)}`, of which there are finitely
many, and there are finitely many `x`. No hypothesis on `i` is needed beyond finiteness of `Z`.

## References

* [Stacks Project, Tag 0GJA](https://stacks.math.columbia.edu/tag/0GJA)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w u v

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- A group isomorphic to a finite group is finite. -/
private theorem finite_of_addCommGrpCat_iso {A A' : AddCommGrpCat.{w}} [Finite A] (e : A ≅ A') :
    Finite A' :=
  Finite.of_equiv _ e.addCommGroupIsoToAddEquiv.toEquiv

/-- **The geometric stalks of a finite locally constant abelian sheaf are finite.** On the small
étale site of Tag 021B, the geometric point lifts to a member of a covering of the final object
on which the sheaf is constant with finite value, and the stalk is that value. -/
@[sga "4 IX 2.3.1" "partial"]
public theorem finite_etaleStalk_of_isFiniteLocallyConstant (S : Scheme.{u})
    (hS : B.Contains S)
    [∀ V : SmallEtale B S hS,
      HasWeakSheafify ((SmallEtale.topology B S hS).over V) AddCommGrpCat.{max (u + 1) v}]
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B S hS) F)
    (t : GeometricPoint S) : Finite ↑(etaleStalk B S hS t F.obj) := by
  have : ∀ V : SmallEtale B S hS, ((SmallEtale.topology B S hS).over V).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) v} := fun V ↦
    wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall.{max (u + 1) v, u + 1, u} _
  obtain ⟨I, V, f, hcov, hconst⟩ := hF.exists_finite_cover (SmallEtale.final B S hS)
  obtain ⟨i, y, -⟩ := exists_geometricPointFiber_of_coverFinal B S hS V f hcov t
  obtain ⟨E, hE, ⟨e⟩⟩ := hconst i
  exact finite_of_addCommGrpCat_iso (Stacks.ConstantSheaf.sheafFiberIsoOfConstantOver
    (geometricPointSitePoint B S hS t) y F E e).symm

section Constructible

variable
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      AddCommGrpCat.{max (u + 1) v}]

/-- **The geometric stalks of a constructible abelian étale sheaf are finite.** The image of the
geometric point lies in an affine open, one stratum of whose constructible stratification
contains it; the stalk of the sheaf there agrees with the stalk of its restriction to that
stratum at a geometric point of the stratum above the same point, and that restriction is finite
locally constant. -/
@[sga "4 IX 2.3.1" "partial"]
public theorem finite_etaleStalk_of_isConstructibleAbelianSheaf (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (hF : IsConstructibleAbelianSheaf B X F) (t : GeometricPoint X.obj) :
    Finite ↑(etaleStalk B X.obj X.property t F.obj) := by
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
    rw [show t'.hom default = z from GeometricPoint.ofPoint_liesOver (s.piece i).obj z]
    exact hz
  have := finite_etaleStalk_of_isFiniteLocallyConstant.{u, v} B (s.piece i).obj
    (s.piece i).property _ (hs i) t'
  exact finite_of_addCommGrpCat_iso ((etaleStalkSmallEtalePullObjIso B (s.inclusion i) t'
      AddCommGrpCat.{max (u + 1) v} F) ≪≫
    (etaleStalkPresheafFunctorIsoOfEqBase B X.obj X.property hbase
      AddCommGrpCat.{max (u + 1) v}).app F.obj)

/-- **The geometric stalks of a constructible abelian sheaf on Mathlib's small étale site are
finite.** The stalk functor of Mathlib's point at a geometric point, read through the
identification `AlgebraicGeometry.SmallEtale.sheafEquiv` of the two sheaf categories, is the
stalk functor of the site of Tag 021B, on which constructibility is defined. -/
public theorem finite_pointSmallEtale_sheafFiber_of_isConstructibleEtaleAbelianSheaf
    {X : Scheme.{u}} (hX : B.Contains X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.EtaleCohomology.IsConstructibleEtaleAbelianSheaf.{u, v} B X hX F)
    (t : GeometricPoint X) :
    Finite ↑((pointSmallEtale t.hom).sheafFiber.obj F) := by
  let E := SmallEtale.sheafEquiv B X hX AddCommGrpCat.{max (u + 1) v}
  let e₁ : E.functor ⋙ (pointSmallEtale t.hom).sheafFiber ≅
      (geometricSitePoint B (B.obj X hX) t).sheafFiber :=
    sheafFiberIsoOfAdjOfFiberIso (geometricSitePoint B (B.obj X hX) t)
      (pointSmallEtale t.hom) (SmallEtale.toEtaleSite B X hX)
      (toEtaleSiteFiberIso B X hX t) E.toAdjunction
  have := finite_etaleStalk_of_isConstructibleAbelianSheaf.{u, v} B (B.obj X hX)
    (E.inverse.obj F) hF t
  exact finite_of_addCommGrpCat_iso (A := etaleStalk B X hX t (E.inverse.obj F).obj)
    ((pointSmallEtale t.hom).sheafFiber.mapIso (E.counitIso.app F).symm ≪≫
      e₁.app (E.inverse.obj F)).symm

/-- The geometric stalks of a constructible abelian sheaf on Mathlib's small étale site are
finite, at the universe lift of the point of a geometric point: raising the universe of a point
does not change the stalk. -/
public theorem finite_pointSmallEtale_ulift_sheafFiber_of_isConstructibleEtaleAbelianSheaf
    {X : Scheme.{u}} (hX : B.Contains X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.EtaleCohomology.IsConstructibleEtaleAbelianSheaf.{u, v} B X hX F)
    (t : GeometricPoint X) :
    Finite ↑(((pointSmallEtale t.hom).ulift.{max (u + 1) v}).sheafFiber.obj F) := by
  have : Finite ↑((pointSmallEtale t.hom).presheafFiber.obj F.obj) :=
    finite_pointSmallEtale_sheafFiber_of_isConstructibleEtaleAbelianSheaf.{u, v} B hX F hF t
  exact finite_of_addCommGrpCat_iso (((pointSmallEtale t.hom).uliftPresheafFiberIso
    (A := AddCommGrpCat.{max (u + 1) v})).app F.obj).symm

end Constructible

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  [∀ (T T' : B.Scheme) (f : T' ⟶ T),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v}
      (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)
      (AlgebraicGeometry.SmallEtale.topology B T'.obj T'.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
    HasWeakSheafify
      ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
      AddCommGrpCat.{max (u + 1) v}]

/-- **The global sections of `i_* i⁻¹ F` are finite when `Z` is finite and `F` constructible.**
Let `i : Z ⟶ X` be a morphism of schemes, `Z` having finitely many points, and let `F` be a
constructible abelian sheaf on the small étale site of `X`. Then `H⁰(X, i_* i⁻¹ F)` is finite.

This is the step "`H⁰(Z, i⁻¹F) = ⊕ F_{x̄_i}` is finite, the stalks of a constructible sheaf being
finite" of the proof of Stacks Tag 0GJA, where `i` is the inclusion of finitely many closed
points; no hypothesis on `i` or on `X` is needed. By `i⁻¹ ⊣ i_*`, `H⁰(X, i_* i⁻¹ F)` is
`Hom(i⁻¹ ℤ, i⁻¹ F)`; a morphism there is determined by its stalks at the geometric points of `Z`,
which are morphisms from `ℤ` to the finite groups `F_{i(x̄)}`. -/
public theorem finite_H_zero_etaleAbelianDirectImage_inverseImage {Z : Scheme.{u}}
    (i : Z ⟶ X) [Finite Z]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : IsConstructibleEtaleAbelianSheaf.{u, v} B X hX F)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    Finite (Sheaf.H.{w} ((etaleAbelianDirectImage.{u, v} i).obj
      ((etaleAbelianInverseImage.{u, v} i).obj F)) 0) := by
  let C := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
    (AddCommGrpCat.of (ULift ℤ))
  let G := (etaleAbelianInverseImage.{u, v} i).obj F
  let s : ∀ z : Z, Spec (.of (GeometricPoint.ofPoint Z z).residueField) ⟶ Z :=
    fun z ↦ (GeometricPoint.ofPoint Z z).hom
  let Φ : Z → (smallEtaleTopology Z).Point.{max (u + 1) v} :=
    fun z ↦ (pointSmallEtale (s z)).ulift.{max (u + 1) v}
  have hs : ⋃ z, Set.range (s z) = Set.univ :=
    Set.eq_univ_of_forall fun z ↦ Set.mem_iUnion.2
      ⟨z, default, GeometricPoint.ofPoint_liesOver Z z⟩
  have hP : (ObjectProperty.ofObj Φ).IsConservativeFamilyOfPoints :=
    Scheme.isConservative_pointSmallEtale_ulift s hs
  let ψ : ((etaleAbelianInverseImage.{u, v} i).obj C ⟶ G) →
      ∀ z, (Φ z).sheafFiber.obj ((etaleAbelianInverseImage.{u, v} i).obj C) ⟶
        (Φ z).sheafFiber.obj G := fun φ z ↦ (Φ z).sheafFiber.map φ
  have hψ : Function.Injective ψ := by
    intro φ φ' h
    refine (hP.jointlyFaithful AddCommGrpCat.{max (u + 1) v}).map_injective fun p ↦ ?_
    obtain ⟨_, ⟨z⟩⟩ := p
    exact congrFun h z
  have hfin : ∀ z, Finite ((Φ z).sheafFiber.obj ((etaleAbelianInverseImage.{u, v} i).obj C) ⟶
      (Φ z).sheafFiber.obj G) := by
    intro z
    let Ψ := (pointSmallEtale (s z ≫ i)).ulift.{max (u + 1) v}
    have : X.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) v} :=
      Scheme.wEqualsLocallyBijective_smallEtaleTopology.{u, v} X
    have eC : (Φ z).sheafFiber.obj ((etaleAbelianInverseImage.{u, v} i).obj C) ≅
        AddCommGrpCat.of (ULift ℤ) :=
      (etaleAbelianInverseImageSheafFiberIso.{u, v} i (s z)).app C ≪≫
        Sites.constantSheafFiberIso Ψ (AddCommGrpCat.of (ULift ℤ))
    have hG : Finite ↑((Φ z).sheafFiber.obj G) := by
      have : Finite ↑(Ψ.sheafFiber.obj F) :=
        finite_pointSmallEtale_ulift_sheafFiber_of_isConstructibleEtaleAbelianSheaf.{u, v}
          B hX F hF ((GeometricPoint.ofPoint Z z).map i)
      exact finite_of_addCommGrpCat_iso
        ((etaleAbelianInverseImageSheafFiberIso.{u, v} i (s z)).app F).symm
    exact Finite.of_equiv _ ((eC.homCongr (Iso.refl _)).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv).symm
  have : Finite ((etaleAbelianInverseImage.{u, v} i).obj C ⟶ G) := Finite.of_injective ψ hψ
  exact Finite.of_equiv _ (((etaleAbelianInverseImageDirectImageAdj.{u, v} i).homEquiv C
    G).trans Abelian.Ext.homEquiv₀.symm)

end Stacks.EtaleCohomology

end
