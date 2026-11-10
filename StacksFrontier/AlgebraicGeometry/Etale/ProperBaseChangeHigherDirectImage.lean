module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.HigherDirectImageBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteDerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteTorsionDirectImage
public import StacksFrontier.AlgebraicGeometry.Etale.UpperShriekBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionInverseImage
public import StacksFrontier.AlgebraicGeometry.Etale.DerivedLowerShriekQuasiFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionsPushforward.AbelianSheafEssentialImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageDirectSums
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Proper base change for higher direct images on the small étale sites of a big étale site

Let `B` be a big étale site and
```
X₁ --a--> X
|f₁       |f
v         v
Y₁ --b--> Y
```
a cartesian square of its underlying category with `f` proper. For a torsion abelian sheaf `G`
on `X_étale`,

`b⁻¹ (R^q f_* G) ≅ R^q f₁_* (a⁻¹ G)`,

on the size-bounded small étale sites of Stacks 021B. This is
`Stacks.EtaleCohomology.etaleAbelianInverseImageRightDerivedDirectImageIsoOfIsProper`
([Stacks, Tag 095T] on Mathlib's small étale sites) carried along the equivalence
`AlgebraicGeometry.SmallEtale.sheafEquiv` of the sheaves of the two presentations, which
identifies the higher direct images
(`AlgebraicGeometry.SmallEtale.rightDerivedSheafEquivPushforwardBaseChangeIso`) and the inverse
images (`AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso`).

## Main definitions

* `AlgebraicGeometry.SmallEtale.abPullbackRightDerivedEtalePushforwardIsoOfIsProper`: the
  isomorphism above.

## References

* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

attribute [local instance] SmallEtale.isGrothendieckAbelian_sheaf_succ

variable (B : BigEtaleSite.{u})

/-- The equivalence of the abelian sheaves of the bounded small étale site of an object of `B`
with those of Mathlib's small étale site, at the coefficients `AddCommGrpCat.{u + 1}`. -/
abbrev abSheafEquiv (S : B.Scheme) :
    Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1} ≌
      Sheaf S.obj.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  SmallEtale.sheafEquiv B S.obj S.property AddCommGrpCat.{u + 1}

/-- **The comparison of sites commutes with inverse image**: transporting to Mathlib's small
étale site and then taking `b⁻¹` there is taking `b⁻¹` on the bounded site and then
transporting. -/
def abSheafEquivInverseImageIso {S T : B.Scheme} (b : T ⟶ S) :
    (abSheafEquiv B S).functor ⋙ Stacks.EtaleCohomology.etaleAbelianInverseImage.{u, 0}
        (B.inclusion.map b) ≅
      abPullback.{u, 0} B b ⋙ (abSheafEquiv B T).functor :=
  sheafEquivPullbackBaseChangeIso B b AddCommGrpCat.{u + 1}
    (Stacks.EtaleCohomology.etaleAbelianInverseImageDirectImageAdj.{u, 0} (B.inclusion.map b))
    (abPullbackAdjunction.{u, 0} B b)

/-- **The comparison of sites commutes with higher direct images**: Mathlib's `R^q f_*` of the
transport of `G` is the transport of the bounded site's `R^q f_* G`. -/
def abSheafEquivRightDerivedIso {T S : B.Scheme} (f : T ⟶ S) (q : ℕ)
    (G : Sheaf (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{u + 1}) :
    ((Stacks.EtaleCohomology.etaleAbelianDirectImage.{u, 0} (B.inclusion.map f)).rightDerived
        q).obj ((abSheafEquiv B T).functor.obj G) ≅
      (abSheafEquiv B S).functor.obj
        (((etalePushforward.{u, u + 1} B f).rightDerived q).obj G) :=
  (rightDerivedSheafEquivPushforwardBaseChangeIso.{0, u} B f q).app _ ≪≫
    (abSheafEquiv B S).functor.mapIso
      (((etalePushforward.{u, u + 1} B f).rightDerived q).mapIso
        ((abSheafEquiv B T).unitIso.app G).symm)

/-- **Inverse image of abelian sheaves on the bounded small étale sites preserves torsion**:
`Stacks.EtaleCohomology.torsionSheafProperty_etaleAbelianInverseImage` carried along the
comparison of sites. -/
@[sga "4 IX 1.2" "(iv)"]
theorem torsionSheafProperty_abPullback_obj {S T : B.Scheme} (b : T ⟶ S)
    (G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B S.obj S.property) G) :
    Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B T.obj T.property)
      ((abPullback.{u, 0} B b).obj G) :=
  (Stacks.Torsion.torsionSheafProperty _).prop_of_iso
    ((abSheafEquiv B T).unitIso.app _).symm
    (torsionSheafProperty_sheafEquiv_inverse_obj B T _
      ((Stacks.Torsion.torsionSheafProperty _).prop_of_iso ((abSheafEquivInverseImageIso B b).app G)
        (Stacks.EtaleCohomology.torsionSheafProperty_etaleAbelianInverseImage.{u, 0}
          (B.inclusion.map b) _ (torsionSheafProperty_sheafEquiv_functor_obj B S G hG))))

variable {X Y X₁ Y₁ : B.Scheme} (a : X₁ ⟶ X) (f₁ : X₁ ⟶ Y₁) (f : X ⟶ Y) (b : Y₁ ⟶ Y)
  (sq : IsPullback a f₁ f b) [IsProper (B.inclusion.map f)]

/-- **Proper base change for higher direct images on the bounded small étale sites.** For a
cartesian square `a ≫ f = f₁ ≫ b` of a big étale site with `f` proper and a torsion abelian
sheaf `G` on `X_étale`, `b⁻¹ (R^q f_* G) ≅ R^q f₁_* (a⁻¹ G)`: [Stacks, Tag 095T]
(`Stacks.EtaleCohomology.etaleAbelianInverseImageRightDerivedDirectImageIsoOfIsProper`) carried
along `AlgebraicGeometry.SmallEtale.sheafEquiv`. -/
def abPullbackRightDerivedEtalePushforwardIsoOfIsProper
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B X.obj X.property) G)
    (q : ℕ) :
    (abPullback.{u, 0} B b).obj (((etalePushforward.{u, u + 1} B f).rightDerived q).obj G) ≅
      ((etalePushforward.{u, u + 1} B f₁).rightDerived q).obj ((abPullback.{u, 0} B a).obj G) :=
  (abSheafEquiv B Y₁).fullyFaithfulFunctor.preimageIso <|
    ((abSheafEquivInverseImageIso B b).app _).symm ≪≫
    (Stacks.EtaleCohomology.etaleAbelianInverseImage.{u, 0} (B.inclusion.map b)).mapIso
      (abSheafEquivRightDerivedIso B f q G).symm ≪≫
    Stacks.EtaleCohomology.etaleAbelianInverseImageRightDerivedDirectImageIsoOfIsProper
      (B.inclusion.map f) (B.inclusion.map b) (B.inclusion.map a) (B.inclusion.map f₁)
      (sq.map B.inclusion) _ (torsionSheafProperty_sheafEquiv_functor_obj B X G hG) q ≪≫
    ((Stacks.EtaleCohomology.etaleAbelianDirectImage.{u, 0} (B.inclusion.map f₁)).rightDerived
      q).mapIso ((abSheafEquivInverseImageIso B a).app G) ≪≫
    abSheafEquivRightDerivedIso B f₁ q _

/-! ### Detection at the residue fields -/

section Residue

variable {S : B.Scheme} (s : S.obj)

/-- The spectrum of the residue field at a point of an object of a big étale site lies in the
site: the morphism from it is a quasi-compact monomorphism, which does not increase size. -/
theorem contains_spec_residueField : B.Contains (Spec (S.obj.residueField s)) :=
  (Scheme.size_le_of_mono_quasiCompact (S.obj.fromSpecResidueField s)).trans_lt S.property

/-- The spectrum of the residue field at a point `s`, as an object of the big étale site. -/
abbrev residueFieldObj : B.Scheme := B.obj _ (contains_spec_residueField B s)

/-- The canonical morphism `Spec κ(s) ⟶ S`, as a morphism of the big étale site. -/
abbrev residueFieldHom : residueFieldObj B s ⟶ S :=
  ObjectProperty.homMk (S.obj.fromSpecResidueField s)

/-- The étale stalk functor at a geometric point, on abelian sheaves, preserves zero
morphisms: it is the fibre functor of the point of the small étale site attached to the
geometric point. -/
private instance preservesZeroMorphisms_etaleStalkFunctorAbelian' (Y : Scheme.{u})
    (hY : B.Contains Y) (t : GeometricPoint Y) :
    (etaleStalkFunctorAbelian B Y hY t).PreservesZeroMorphisms := by
  change ((geometricPointSitePoint B Y hY t).sheafFiber
    (A := AddCommGrpCat.{u + 1})).PreservesZeroMorphisms
  infer_instance

/-- **An abelian étale sheaf whose inverse images to all residue fields vanish is zero.** A
geometric point `s̄` of `S` factors through `Spec κ(s) ⟶ S` at its image `s`, and the stalk at `s̄`
is the stalk at the lift of `s̄` of the inverse image to `Spec κ(s)` (Stacks 03Q1). -/
theorem isZero_of_forall_isZero_abPullback_residueFieldHom
    (M : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1})
    (h : ∀ s : S.obj, IsZero ((abPullback.{u, 0} B (residueFieldHom B s)).obj M)) :
    IsZero M := by
  refine isZero_of_forall_isZero_etaleStalk B S.obj S.property M fun x => ?_
  let s := x.hom (IsLocalRing.closedPoint x.residueField)
  let t : GeometricPoint (residueFieldObj B s).obj :=
    { residueField := x.residueField
      hom := Spec.map (S.obj.descResidueField (Scheme.stalkClosedPointTo x.hom)) }
  have hx : t.map (B.inclusion.map (residueFieldHom B s)) = x := by
    change GeometricPoint.mk x.residueField
      (Spec.map (S.obj.descResidueField (Scheme.stalkClosedPointTo x.hom)) ≫
        S.obj.fromSpecResidueField s) = x
    rw [Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField]
  have e := (smallEtalePullbackStalkIsoAbelian B (residueFieldHom B s) t).app M
  rw [hx] at e
  exact ((etaleStalkFunctorAbelian B _ _ t).map_isZero (h s)).of_iso e.symm

end Residue

/-! ### Higher direct images commute with filtered colimits -/

/-- The bounded site's higher direct image is Mathlib's, conjugated by the comparison of sites. -/
def rightDerivedEtalePushforwardIsoSheafEquiv {T S : B.Scheme} (f : T ⟶ S) (q : ℕ) :
    (abSheafEquiv B T).functor ⋙
        (Stacks.EtaleCohomology.etaleAbelianDirectImage.{u, 0} (B.inclusion.map f)).rightDerived
          q ⋙ (abSheafEquiv B S).inverse ≅
      (etalePushforward.{u, u + 1} B f).rightDerived q :=
  Functor.isoWhiskerLeft (abSheafEquiv B T).functor
      (Functor.isoWhiskerRight (rightDerivedSheafEquivPushforwardBaseChangeIso.{0, u} B f q)
        (abSheafEquiv B S).inverse) ≪≫
    Functor.isoWhiskerLeft ((abSheafEquiv B T).functor ⋙ (abSheafEquiv B T).inverse ⋙
      (etalePushforward.{u, u + 1} B f).rightDerived q) (abSheafEquiv B S).unitIso.symm ≪≫
    Functor.isoWhiskerRight (abSheafEquiv B T).unitIso.symm
      ((etalePushforward.{u, u + 1} B f).rightDerived q)

/-- **Higher direct images along a quasi-compact and quasi-separated morphism commute with
filtered colimits**, on the bounded small étale sites: Mathlib's
(`Stacks.EtaleCohomology.preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage`, which
is the source's proof of [Stacks, Tag 09Z1]) conjugated by the comparison of sites. -/
@[sga "4 VI 5.1" "Scheme case of VI 5.1"]
theorem preservesColimitsOfShape_rightDerived_etalePushforward {T S : B.Scheme} (f : T ⟶ S)
    [QuasiCompact (B.inclusion.map f)] [QuasiSeparated (B.inclusion.map f)] (q : ℕ)
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I ((etalePushforward.{u, u + 1} B f).rightDerived q) := by
  have :=
    Stacks.EtaleCohomology.preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage.{0, u}
      (B.inclusion.map f) q I
  exact preservesColimitsOfShape_of_natIso (rightDerivedEtalePushforwardIsoSheafEquiv B f q)

/-! ### Higher direct images along composites with finite morphisms -/

section Finite

attribute [local instance] HasDerivedCategory.standard

/-- The right derived functors of isomorphic additive functors are isomorphic. -/
def rightDerivedIsoOfIso {C D : Type*} [Category* C] [Category* D] [Abelian C]
    [HasInjectiveResolutions C] [Abelian D] {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

variable {X Y Z : B.Scheme}

/-- **`R^n (a ≫ b)_* = R^n b_* ∘ a_*` for `a` finite**: `a_*` is exact (Stacks 03QP) and carries
injective sheaves to injective sheaves, having the exact left adjoint `a⁻¹`. -/
def rightDerivedEtalePushforwardCompIsoOfIsFinite (a : X ⟶ Y) (b : Y ⟶ Z)
    [IsFinite (B.inclusion.map a)] (n : ℕ) :
    (etalePushforward.{u, u + 1} B (a ≫ b)).rightDerived n ≅
      etalePushforward.{u, u + 1} B a ⋙ (etalePushforward.{u, u + 1} B b).rightDerived n :=
  haveI hex := (exactFunctor_iff _).mp (etalePushforward_exact_of_isFinite B a)
  haveI := hex.1
  haveI := hex.2
  haveI := preservesFiniteLimits_abPullback.{u, 0} B a
  haveI : (etalePushforward.{u, u + 1} B a).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (abPullbackAdjunction.{u, 0} B a)
  rightDerivedIsoOfIso (smallEtaleSheafPushforwardCompIso B X Y Z a b AddCommGrpCat.{u + 1}).symm
      n ≪≫
    Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic _ _
      (fun I _ => (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).2
        fun p hp => by
          obtain ⟨p, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
          exact Functor.isZero_rightDerived_obj_injective_succ _ _ _) n

/-- **`R^n (a ≫ b)_* = b_* ∘ R^n a_*` for `b` finite**: `b_*` is exact (Stacks 03QP). -/
def rightDerivedEtalePushforwardCompIsoOfIsFinite' (a : X ⟶ Y) (b : Y ⟶ Z)
    [IsFinite (B.inclusion.map b)] (n : ℕ) :
    (etalePushforward.{u, u + 1} B a).rightDerived n ⋙ etalePushforward.{u, u + 1} B b ≅
      (etalePushforward.{u, u + 1} B (a ≫ b)).rightDerived n :=
  haveI hex := (exactFunctor_iff _).mp (etalePushforward_exact_of_isFinite B b)
  haveI := hex.1
  haveI := hex.2
  haveI : (etalePushforward.{u, u + 1} B b).PreservesHomology := Functor.preservesHomologyOfExact _
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso _ _ _
    (smallEtaleSheafPushforwardCompIso B X Y Z a b AddCommGrpCat.{u + 1}) n

end Finite

end AlgebraicGeometry.SmallEtale

end
