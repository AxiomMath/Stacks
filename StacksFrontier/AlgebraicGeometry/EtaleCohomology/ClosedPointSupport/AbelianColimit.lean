module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.Noetherian.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SpecializationClosedSupportColimit
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianWeakSerre
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Abelian étale sheaves supported in a specialization-closed set

Let `X` be a Noetherian scheme and let `E ⊆ X` be stable under specialization. An abelian sheaf
on the small étale site of `X` whose support is contained in `E` is a filtered colimit of abelian
sheaves each of whose supports is contained in a *closed* subset of `E`. This is the abelian
half of [Stacks, Tag 0F0N] part (2), with the constructibility of the terms of the colimit
dropped.

The statement is obtained from the sheaves-of-modules form
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleModuleSheaf_isClosed_support` by
transport along the equivalence `AddCommGrpCat ≌ ModuleCat (ULift ℤ)`, taken at the coefficient
universe `u + 1` of that result.

## Main results

* `AlgebraicGeometry.addCommGrpCatEquivULiftIntModuleCat` — abelian groups are the same thing as
  modules over `ULift ℤ`.
* `AlgebraicGeometry.sheafAddCommGrpCatEquivULiftIntModuleCat` — the induced equivalence between
  abelian sheaves and sheaves of `ULift ℤ`-modules on the small étale site.
* `AlgebraicGeometry.supportModuleSheaf_sheafAddCommGrpCatEquivULiftIntModuleCat` — that
  equivalence matches the support of an abelian sheaf with the support of the corresponding sheaf
  of `ULift ℤ`-modules.
* `AlgebraicGeometry.exists_isFilteredColimit_isClosed_support_abelian` — the abelian form of
  [Stacks, Tag 0F0N] part (2).

## Implementation notes

The coefficient equivalence is the composite of the forgetful equivalence
`ModuleCat ℤ ≌ AddCommGrpCat` of `ModuleCat.forget₂AddCommGroupIsEquivalence` with restriction of
scalars along `ULift.ringEquiv`. The detour through `ULift ℤ` is forced by the shape of the
sheaves-of-modules statement, whose ring lives in the coefficient universe `u + 1` while `ℤ` lives
in `Type 0`.

Matching the two supports is the only mathematical content of the transport. Both are defined by
nonvanishing of the geometric stalks, so it is enough to know that an equivalence of coefficient
categories neither changes a geometric stalk — it preserves the defining filtered colimit — nor
the vanishing of one, since being a zero object is a property of hom-sets alone. The abelian
support is spelled with a universe lift of the coefficients, which
`AlgebraicGeometry.isZero_etaleStalk_ulift_iff` removes.

Pushing the resulting diagram back along the inverse equivalence uses that an equivalence
preserves colimits; the vertex is moved onto the given sheaf by the unit isomorphism.

## References

* [Stacks Project, Tag 0F0N](https://stacks.math.columbia.edu/tag/0F0N)
* [Stacks Project, Tag 04FS](https://stacks.math.columbia.edu/tag/04FS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- `ULift ℤ` is a Noetherian ring, being isomorphic to `ℤ`. -/
private instance isNoetherianRing_uliftInt : IsNoetherianRing (ULift.{v} ℤ) :=
  isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv.{0, v}).symm

/-- The functor half of an equivalence of categories carries a zero object to a zero object:
being a zero object is a property of the hom-sets alone, and the adjunction underlying the
equivalence identifies the hom-sets in question. -/
private theorem isZero_equivalence_functor_obj {A : Type*} [Category* A] {A' : Type*}
    [Category* A'] (e : A ≌ A') {M : A} (h : IsZero M) : IsZero (e.functor.obj M) := by
  refine ⟨fun Y => ⟨?_⟩, fun Y => ⟨?_⟩⟩
  · let := (h.unique_to (e.inverse.obj Y)).some
    exact Equiv.unique (e.toAdjunction.homEquiv M Y)
  · let := (h.unique_from (e.symm.functor.obj Y)).some
    exact Equiv.unique (e.symm.toAdjunction.homEquiv Y M).symm

/-- An equivalence of categories detects zero objects. -/
private theorem isZero_equivalence_functor_obj_iff {A : Type*} [Category* A] {A' : Type*}
    [Category* A'] (e : A ≌ A') (M : A) : IsZero (e.functor.obj M) ↔ IsZero M :=
  ⟨fun h => (isZero_equivalence_functor_obj e.symm h).of_iso (e.unitIso.app M),
    isZero_equivalence_functor_obj e⟩

/-- Postcomposing the values of a presheaf on the small étale site with an equivalence of
coefficient categories changes neither the geometric stalk, which is a colimit the equivalence
preserves, nor the vanishing of it. -/
private theorem isZero_etaleStalk_comp_equivalence_iff (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (p : GeometricPoint S) {A : Type*} [Category* A]
    [HasColimitsOfSize.{u, u} A] {A' : Type*} [Category* A'] [HasColimitsOfSize.{u, u} A']
    (e : A ≌ A') (F : (SmallEtale B S hS)ᵒᵖ ⥤ A) :
    IsZero (etaleStalk B S hS p (F ⋙ e.functor)) ↔ IsZero (etaleStalk B S hS p F) := by
  let iso := preservesColimitIso e.functor
      ((CategoryOfElements.π (geometricPointFiber B S hS p)).op ⋙ F) ≪≫
    HasColimit.isoOfNatIso (Functor.associator _ _ _)
  show IsZero (colimit _) ↔ IsZero (colimit _)
  rw [← iso.isZero_iff]
  exact isZero_equivalence_functor_obj_iff e _

/-- **Abelian groups are the same thing as modules over `ULift ℤ`.** The forgetful functor from
`ℤ`-modules is an equivalence, and restriction of scalars along the ring isomorphism
`ULift ℤ ≃+* ℤ` is another. -/
public def addCommGrpCatEquivULiftIntModuleCat :
    AddCommGrpCat.{v} ≌ ModuleCat.{v} (ULift.{v} ℤ) :=
  (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).asEquivalence.symm.trans
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (ULift.ringEquiv.{0, v} (R := ℤ)))

/-- **Abelian sheaves on the small étale site are the same thing as sheaves of
`ULift ℤ`-modules**, by postcomposition with
`AlgebraicGeometry.addCommGrpCatEquivULiftIntModuleCat`. -/
@[sga "4 IV 11.1.5" "small étale topos"]
public def sheafAddCommGrpCatEquivULiftIntModuleCat (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1} ≌
      Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) := by
  letI := Stacks.ConstantSheaf.sheafCompose_isEquivalence (SmallEtale.topology B S hS)
    (addCommGrpCatEquivULiftIntModuleCat.{u + 1}).functor
  exact (sheafCompose (SmallEtale.topology B S hS)
    (addCommGrpCatEquivULiftIntModuleCat.{u + 1}).functor).asEquivalence

/-- The support of a sheaf of modules only depends on the isomorphism class of the sheaf. -/
private theorem supportModuleSheaf_congr (B : BigEtaleSite.{u}) (X : B.Scheme)
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    {M N : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)} (α : M ≅ N) :
    supportModuleSheaf B X Λ M = supportModuleSheaf B X Λ N := by
  ext x
  exact exists_congr fun t => and_congr_right fun _ => not_congr (Iso.isZero_iff
    ((etaleStalkPresheafFunctor B X.obj X.property t (ModuleCat.{u + 1} Λ)).mapIso
      ((sheafToPresheaf _ _).mapIso α)))

/-- **The equivalence of `AlgebraicGeometry.sheafAddCommGrpCatEquivULiftIntModuleCat` matches the
two supports.** Both are the set of points carrying a nonvanishing geometric stalk, and the
equivalence changes neither the stalk nor its vanishing. -/
public theorem supportModuleSheaf_sheafAddCommGrpCatEquivULiftIntModuleCat
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    supportModuleSheaf B X (ULift.{u + 1} ℤ)
        ((sheafAddCommGrpCatEquivULiftIntModuleCat B X.obj X.property).functor.obj G) =
      supportSheaf B X.obj X.property G := by
  ext x
  refine exists_congr fun t => and_congr_right fun _ => not_congr ?_
  rw [isZero_etaleStalk_ulift_iff B X.obj X.property G t]
  exact isZero_etaleStalk_comp_equivalence_iff B X.obj X.property t
    addCommGrpCatEquivULiftIntModuleCat.{u + 1} G.obj

/-- **The abelian form of [Stacks, Tag 0F0N] part (2).** Let `X` be a Noetherian scheme and let
`E ⊆ X` be stable under specialization. An abelian sheaf `F` on the small étale site of `X` whose
support is contained in `E` is a filtered colimit of abelian sheaves, each of whose supports is
contained in a closed subset of `E`.

This is the sheaves-of-modules statement
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleModuleSheaf_isClosed_support`
at `Λ = ULift ℤ`, transported along the equivalence
`AlgebraicGeometry.sheafAddCommGrpCatEquivULiftIntModuleCat`. Constructibility of the terms is
not transported: it is a property of the sheaf of modules, and asserting it of the abelian sheaf
would be a different statement. -/
public theorem exists_isFilteredColimit_isClosed_support_abelian
    (B : BigEtaleSite.{u}) (X : B.Scheme) [IsNoetherian X.obj]
    (E : Set X.obj) (hE : StableUnderSpecialization E)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hsupp : supportSheaf B X.obj X.property F ⊆ E) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, ∃ Z : Set X.obj, IsClosed Z ∧ Z ⊆ E ∧
          supportSheaf B X.obj X.property (D.obj i) ⊆ Z := by
  let eS := sheafAddCommGrpCatEquivULiftIntModuleCat B X.obj X.property
  obtain ⟨I, hI, hfilt, D, ι, ⟨hcolim⟩, hD⟩ :=
    exists_isFilteredColimit_isConstructibleModuleSheaf_isClosed_support B X
      (ULift.{u + 1} ℤ) E hE (eS.functor.obj F)
      ((supportModuleSheaf_sheafAddCommGrpCatEquivULiftIntModuleCat B X F).trans_subset hsupp)
  refine ⟨I, hI, hfilt, D ⋙ eS.inverse,
    ((eS.inverse.mapCocone (Cocone.mk _ ι)).extend (eS.unitIso.app F).inv).ι,
    ⟨IsColimit.ofIsoColimit (isColimitOfPreserves eS.inverse hcolim)
      (Cocone.ext (eS.unitIso.app F).symm)⟩, fun i => ?_⟩
  obtain ⟨Z, hZ, hZE, hZsupp⟩ := (hD i).2
  exact ⟨Z, hZ, hZE, ((supportModuleSheaf_sheafAddCommGrpCatEquivULiftIntModuleCat B X
    (eS.inverse.obj (D.obj i))).symm.trans (supportModuleSheaf_congr B X _
      (eS.counitIso.app (D.obj i)))).trans_subset hZsupp⟩

end AlgebraicGeometry

end
