module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.PerfectSourceLift
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.ShiftedBundleSummand
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrict
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.CategoryTheory.Triangulated.ConeOfBiprodProjection
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
import StacksCore.Tactic.StacksAttribute

/-!
# `F ⊕ F[1]` as the restriction of a perfect complex

Let `A` be a commutative ring, `X = Spec A` and `U ⊆ X` a quasi-compact open.  For every perfect
object `F` of `D(𝒪_U)` the object `F ⊕ F[1]` is the restriction to `U` of a perfect object of
`D(𝒪_X)`.  This is [Stacks, Tag 08EI].

The argument is the source's.  By [Stacks, Tag 08EG] there are an integer `r`, a finite locally
free `𝒪_U`-module `𝓕` and a perfect complex `P` on `X` with `𝓕[r] ⊕ F ≅ P|_U`.  By
[Stacks, Tag 08EH] applied to the endomorphism `α` of `P|_U` that is the identity on `𝓕[r]` and
zero on `F`, there are a perfect object `E₁` and maps `β, γ : E₁ ⟶ P` with `β|_U` invertible and
`β|_U ≫ α = γ|_U`.  The cone of `γ` is then perfect, and restricted to `U` it is the cone of `α`
-- because `β|_U` is invertible -- which is `F ⊕ F[1]`.

## Main results

* `Stacks.DerivedQCoh.OpenLift.derivedRestrictModulesIsoDerivedRestriction`: the two spellings of
  derived restriction to an open subspace of `Spec A` agree.
* `Stacks.DerivedQCoh.OpenLift.exists_isPerfect_biprod_shift_of_lift`: the triangle step, for an
  arbitrary triangulated functor out of `D(𝒪_X)` and a lift of `diag(1, 0)` along it.
* `Stacks.DerivedQCoh.OpenLift.isDQCoh_of_isPerfect`: a perfect object of `D(𝒪_{Spec A})` has
  quasi-coherent cohomology.
* `Stacks.DerivedQCoh.OpenLift.exists_lift_biprod_diag`: **[Stacks, Tag 08EH]** applied to
  `diag(1, 0)`, for any functor isomorphic to `derivedRestriction`.
* `Stacks.DerivedQCoh.OpenLift.exists_isPerfect_biprod_shift_iso_restrict_toScheme`:
  **[Stacks, Tag 08EI]**.

## Implementation notes

**The two spellings of derived restriction.**  [Stacks, Tag 08EG] computes the restriction of a
perfect complex degreewise, as `DerivedCategory.Q` of
`((AlgebraicGeometry.RingedSpace.restrictModules X U).mapHomologicalComplex _).obj P`, while
[Stacks, Tag 08EH] is stated for `Stacks.Cohomology.OpenSubspace.derivedRestriction`, the total
right derived functor of restriction passed to homotopy categories.  The first is
`AlgebraicGeometry.RingedSpace.derivedRestrictModules`, the functor induced on derived categories
by the exact functor `restrictModules`, read off by
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso`; and the second is the chosen total
right derived functor of the *same* functor, since
`AlgebraicGeometry.RingedSpace.restrictModules X.toRingedSpace U` is
`ExtensionByZeroModules.jStar U X.ringCatSheaf`.  So the two are identified by the uniqueness of
right derived functors, which is
`Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived`; that identification is
`derivedRestrictModulesIsoDerivedRestriction` below, and it is what lets the two tags meet.

**The affine scheme is `Spec A`**, as it is in [Stacks, Tag 08EH] and in the Koszul machinery
behind it, rather than a scheme assumed affine; the source's proof opens with "say `X = Spec A`".

The computation of the cone of the endomorphism `diag(1, 0)` of a biproduct is
`Stacks.Triangulated.exists_iso_biprod_shift_of_distTriang_of_conj`, a statement about an
arbitrary triangulated category.

**Why the argument is split, and into these pieces.**  The triangle step is stated for an
*arbitrary* triangulated functor out of `D(𝒪_X)`, so that the biproducts, the shift and the cone
are formed in a category that is a variable.  This is not generality for its own sake: each
written occurrence of `derivedRestriction` re-synthesizes the right-derived-functor instances
behind it, and each written occurrence of a biproduct in a *named* category of `𝒪_U`-modules
re-synthesizes the Grothendieck-abelian instances behind that; a declaration carrying several of
either exhausts the heartbeat budget while elaborating its own statement.  With the functor a
variable, the tag statement is the only place where restriction and the biproduct meet.

The isomorphisms are written with the biproduct on the left, as `S ⊞ F ≅ E|_U` rather than
`E|_U ≅ S ⊞ F`.  The category of `𝒪_U`-modules has two spellings -- `U.toScheme.Modules` and the
modules over `ExtensionByZeroModules.resRing U (Spec A).ringCatSheaf` -- which are the same type
with separately declared instances; with the restriction written first, the binary biproduct is
elaborated against the second spelling, and its instance is then not found.

`diag(1, 0)` is written `biprod.fst ≫ biprod.inl` rather than `biprod.map (𝟙 S) 0`, which would
ask for the zero morphism of that category as well; the two are equal by
`Stacks.Triangulated.biprod_map_id_zero_eq_fst_comp_inl`.

The category of `𝒪_X`-modules is written `StrictlyPerfect.OXMod (Spec A).toRingedSpace`, which is
the spelling `AlgebraicGeometry.RingedSpace.derivedRestrictModules`,
`Stacks.Cohomology.PerfectComplexes.IsPerfect` and [Stacks, Tag 08CR] are all stated in, rather
than `Koszul.DerivedSystem.derivedCat A`, which is the spelling [Stacks, Tag 08EH] is stated in.
The two are the same type, and an object or a morphism of one is accepted where the other is
expected; but a `CategoryTheory.Pretriangulated.Triangle` of one is not, because its category
instance is then synthesized from scratch rather than unified, and that synthesis does not fit in
the budget.  [Stacks, Tag 08EH] is applied to objects and morphisms, so the crossing happens
there and nowhere else.

`isDQCoh_of_isPerfect` is the one statement written in a third spelling, `(Spec A).Modules`: the
quasi-coherence of the cohomology of a pseudo-coherent object is stated with the `OXMod` of the
ringed space, and reading it as `Stacks.DerivedQCoh.IsDQCoh` fits the budget from
`(Spec A).Modules` and not from `OXMod`.

## References

* [Stacks Project, Tag 08EI](https://stacks.math.columbia.edu/tag/08EI)
* [Stacks Project, Tag 08EG](https://stacks.math.columbia.edu/tag/08EG)
* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.OpenSubspace
open Stacks.Cohomology.PerfectComplexes
open StrictlyPerfect

namespace Stacks.DerivedQCoh.OpenLift

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : CommRingCat.{u}}

/-- **Restriction to an open subspace of `Spec A`, in the two spellings of the derived
category.**  The functor induced on derived categories by the exact functor
`AlgebraicGeometry.RingedSpace.restrictModules` -- which is
`AlgebraicGeometry.RingedSpace.derivedRestrictModules`, the spelling [Stacks, Tag 08EG] computes
in -- is the total right derived functor `Stacks.Cohomology.OpenSubspace.derivedRestriction` that
[Stacks, Tag 08EH] is stated for.

`restrictModules` and `ExtensionByZeroModules.jStar` are the same functor, so the two are right
derived functors of one functor on the homotopy category, and
`Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived` -- [Stacks, Tag 0E2K] -- is the
resulting comparison. -/
def derivedRestrictModulesIsoDerivedRestriction (U : (Spec A).Opens) :
    AlgebraicGeometry.RingedSpace.derivedRestrictModules.{u + 1, u + 1, u}
        (Spec A).toRingedSpace U ≅
      derivedRestriction (Spec A).ringCatSheaf U :=
  Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived
    (AlgebraicGeometry.RingedSpace.restrictModules.{u, u} (Spec A).toRingedSpace U)

/-- **The triangle step of [Stacks, Tag 08EI].**  Let `R` be a triangulated functor out of
`D(𝒪_X)`, `X = Spec A`, let `E₀` and `E₁` be perfect objects of `D(𝒪_X)`, let
`ε : S ⊞ F ≅ R.obj E₀` identify the image of `E₀` with a biproduct, and let `β, γ : E₁ ⟶ E₀` be
maps with `R.map β` invertible and `R.map β` followed by `diag(1, 0)` conjugated along `ε` equal
to `R.map γ`.  Then the cone `E` of `γ` is perfect and `F ⊕ F[1] ≅ R.obj E`.

`R` carries the distinguished triangle on `γ` to a distinguished triangle, whose third object is
therefore the cone of `R.map γ`; since `R.map β` is invertible that is the cone of `diag(1, 0)`,
which `Stacks.Triangulated.exists_iso_biprod_shift_of_distTriang_of_conj` computes.  That the
cone of `γ` is perfect is [Stacks, Tag 08CR].

Nothing about restriction to an open is used, which is the point: the data `R`, `ε`, `β`, `γ` is
what [Stacks, Tag 08EG] and [Stacks, Tag 08EH] produce, and keeping the category of
`𝒪_U`-modules a variable here keeps its instances out of this declaration. -/
theorem exists_isPerfect_biprod_shift_of_lift {D : Type (u + 1)} [Category.{u + 1} D]
    [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    (R : DerivedCategory (OXMod.{u, u, u} (Spec A).toRingedSpace) ⥤ D) [R.CommShift ℤ]
    [R.IsTriangulated] {E₀ E₁ : DerivedCategory (OXMod.{u, u, u} (Spec A).toRingedSpace)}
    (hE₀ : IsPerfect (X := (Spec A).toRingedSpace) E₀)
    (hE₁ : IsPerfect (X := (Spec A).toRingedSpace) E₁)
    (S F : D) (ε : S ⊞ F ≅ R.obj E₀) (β γ : E₁ ⟶ E₀) (hβ : IsIso (R.map β))
    (hβγ : R.map β ≫
        (ε.inv ≫ ((biprod.fst : S ⊞ F ⟶ S) ≫ (biprod.inl : S ⟶ S ⊞ F)) ≫ ε.hom) = R.map γ) :
    ∃ E : DerivedCategory (OXMod.{u, u, u} (Spec A).toRingedSpace),
      IsPerfect (X := (Spec A).toRingedSpace) E ∧ Nonempty (F ⊞ F⟦(1 : ℤ)⟧ ≅ R.obj E) := by
  classical
  obtain ⟨E, v, w, hTri⟩ := distinguished_cocone_triangle γ
  refine ⟨E, Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished
    (X := (Spec A).toRingedSpace) (Triangle.mk γ v w) hTri hE₁ hE₀, ?_⟩
  obtain ⟨eFF⟩ := Stacks.Triangulated.exists_iso_biprod_shift_of_distTriang_of_conj S F ε _ _ hβ
    _ _ (R.map_distinguished (Triangle.mk γ v w) hTri) hβγ
  exact ⟨eFF.symm⟩

/-- **A perfect object of `D(𝒪_{Spec A})` lies in `D_QCoh(𝒪_{Spec A})`.**  A perfect object is
pseudo-coherent, and the cohomology sheaves of a pseudo-coherent object of the derived category
of a scheme are quasi-coherent.

The intermediate step is written out because reading the conclusion of
`AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent` directly as
`Stacks.DerivedQCoh.IsDQCoh` does not fit in the heartbeat budget. -/
theorem isDQCoh_of_isPerfect (E : DerivedCategory ((Spec A).Modules))
    (hE : IsPerfect (X := (Spec A).toRingedSpace) E) :
    Stacks.DerivedQCoh.IsDQCoh (R := (Spec A).ringCatSheaf) E :=
  have h : ∀ n : ℤ, SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf
      ((DerivedCategory.homologyFunctor (Spec A).Modules n).obj E) :=
    AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent (Spec A) E
      (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect E hE)
  fun n => h n

/-- **[Stacks, Tag 08EH] applied to `diag(1, 0)`, read along an isomorphism of restriction
functors.**  Let `R` be a functor out of `D(𝒪_X)`, `X = Spec A`, isomorphic to restriction to a
quasi-compact open `U`, let `E₀` be a perfect object of `D(𝒪_X)` and let
`ε : S ⊞ F ≅ R.obj E₀`.  Then there are a perfect `E₁` and maps `β, γ : E₁ ⟶ E₀` with `R.map β`
invertible and `R.map β` followed by `diag(1, 0)` conjugated along `ε` equal to `R.map γ`.

The endomorphism `ε.inv ≫ diag(1, 0) ≫ ε.hom` of `R.obj E₀` is carried to one of `E₀|_U` by the
isomorphism, [Stacks, Tag 08EH] lifts it, and the two conclusions are carried back by
`CategoryTheory.NatIso.isIso_map_iff` and `CategoryTheory.NatIso.naturality_2`.  The tag
identifies `E₁` as `I ⊗^L_{𝒪_X} E₀` for a perfect `I`, which is not recorded here because the
cone argument does not use it. -/
theorem exists_lift_biprod_diag (U : (Spec A).Opens) (hU : IsCompact (U : Set (Spec A)))
    (R : DerivedCategory (OXMod.{u, u, u} (Spec A).toRingedSpace) ⥤
      DerivedCategory (SheafOfModules.{u}
        (ExtensionByZeroModules.resRing U (Spec A).ringCatSheaf)))
    (φ : R ≅ derivedRestriction (Spec A).ringCatSheaf U)
    (E₀ : DerivedCategory (OXMod.{u, u, u} (Spec A).toRingedSpace))
    (hE₀ : IsPerfect (X := (Spec A).toRingedSpace) E₀)
    (S F : DerivedCategory (SheafOfModules.{u}
      (ExtensionByZeroModules.resRing U (Spec A).ringCatSheaf)))
    (ε : S ⊞ F ≅ R.obj E₀) :
    ∃ (E₁ : DerivedCategory (OXMod.{u, u, u} (Spec A).toRingedSpace)) (β γ : E₁ ⟶ E₀),
      IsPerfect (X := (Spec A).toRingedSpace) E₁ ∧ IsIso (R.map β) ∧
        R.map β ≫
            (ε.inv ≫ ((biprod.fst : S ⊞ F ⟶ S) ≫ (biprod.inl : S ⟶ S ⊞ F)) ≫ ε.hom) =
          R.map γ := by
  obtain ⟨I, -, hIE, β, γ, hβ, hβγ⟩ :=
    exists_isPerfect_lift_of_isPerfect_of_isDQCoh U hU E₀ E₀ hE₀ (isDQCoh_of_isPerfect E₀ hE₀)
      (φ.inv.app E₀ ≫ (ε.inv ≫ (biprod.fst ≫ biprod.inl) ≫ ε.hom) ≫ φ.hom.app E₀)
  refine ⟨_, β, γ, hIE, (NatIso.isIso_map_iff φ β).mpr hβ, ?_⟩
  have hid : φ.hom.app E₀ ≫ φ.inv.app E₀ = 𝟙 (R.obj E₀) := Iso.hom_inv_id_app φ E₀
  rw [← NatIso.naturality_2 φ β, ← NatIso.naturality_2 φ γ, ← hβγ]
  simp only [Category.assoc]
  rw [hid, Category.comp_id]

/-- **[Stacks, Tag 08EI].**  Let `A` be a commutative ring, `X = Spec A`, and `U ⊆ X` a
quasi-compact open.  For every perfect object `F` of `D(𝒪_U)` there is a perfect object `E` of
`D(𝒪_X)` with `F ⊕ F[1] ≅ E|_U`.

[Stacks, Tag 08EG] gives an integer `r`, a finite locally free `𝒪_U`-module `𝓕` and a perfect
complex `P` on `X` with `𝓕[r] ⊕ F ≅ P|_U`.  `exists_lift_biprod_diag`, which is
[Stacks, Tag 08EH], lifts the endomorphism `diag(1, 0)` of that biproduct to maps
`β, γ : E₁ ⟶ P` with `E₁` perfect and `β|_U` invertible, and the cone of `γ` is then a solution
by `Stacks.DerivedQCoh.OpenLift.exists_isPerfect_biprod_shift_of_lift`.
The tag is registered on
`Stacks.DerivedQCoh.OpenLift.exists_isPerfectComplex_restrict_iso_biprod_shift_of_isAffine` of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/OpenLift/AffineLift.lean`. -/
theorem exists_isPerfect_biprod_shift_iso_restrict_toScheme (U : (Spec A).Opens)
    (hU : IsCompact (U : Set (Spec A)))
    (F : DerivedCategory U.toScheme.Modules)
    (hF : IsPerfect (X := U.toScheme.toRingedSpace) F) :
    ∃ E : DerivedCategory (OXMod.{u, u, u} (Spec A).toRingedSpace),
      IsPerfect (X := (Spec A).toRingedSpace) E ∧
      Nonempty (F ⊞ F⟦(1 : ℤ)⟧ ≅
        (AlgebraicGeometry.RingedSpace.derivedRestrictModules.{u + 1, u + 1, u}
          (Spec A).toRingedSpace U).obj E) := by
  classical
  obtain ⟨r, G, P, -, hP, ⟨e⟩⟩ :=
    exists_finiteLocallyFree_biprod_iso_restrict_of_isPerfect (Spec A) U hU F hF
  have hE₀ : IsPerfect (X := (Spec A).toRingedSpace) (DerivedCategory.Q.obj P) :=
    ⟨P, hP, ⟨Iso.refl _⟩⟩
  obtain ⟨E₁, β, γ, hE₁, hβ, hβγ⟩ :=
    exists_lift_biprod_diag U hU _ (derivedRestrictModulesIsoDerivedRestriction U)
      (DerivedCategory.Q.obj P) hE₀ _ F
      (e ≪≫ (AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso
        (Spec A).toRingedSpace U P).symm)
  exact exists_isPerfect_biprod_shift_of_lift
    (AlgebraicGeometry.RingedSpace.derivedRestrictModules.{u + 1, u + 1, u}
      (Spec A).toRingedSpace U) hE₀ hE₁ _ F _ β γ hβ hβγ

end Stacks.DerivedQCoh.OpenLift

end
