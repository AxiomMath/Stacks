module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.PerfectSourceLift
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.SupportedIteratedCone
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.TensorSupport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# `F ⊕ F[1]` as the restriction of a perfect complex supported on a closed set

Let `A` be a commutative ring, `X = Spec A`, let `T ⊆ X` be a closed set with quasi-compact
complement and let `U ⊆ X` be a quasi-compact open.  For every perfect object `F` of `D(𝒪_U)`
whose cohomology is supported on `T ∩ U`, the object `F ⊕ F[1]` is the restriction to `U` of a
perfect object of `D(𝒪_X)` whose cohomology is supported on `T`.  This is [Stacks, Tag 08EK].

Steps 1 to 4 of the source are
`Stacks.DerivedQCoh.OpenLift.exists_isPerfect_cohomologySupportedOn_biprod_summand`: they produce
a perfect `C` supported on `T` with `C|_U ≅ S ⊞ F`.  What is left is steps 5 and 6.
[Stacks, Tag 08EH] lifts the endomorphism `diag(1, 0)` of `S ⊞ F` to maps
`β, γ : I ⊗^L_{𝒪_X} C ⟶ C` with `I` perfect and `β|_U` invertible; the cone of `γ` is then
perfect, its restriction to `U` is the cone of `diag(1, 0)`, which is `F ⊕ F[1]`, and it is
supported on `T` because both `I ⊗^L C` and `C` are.

## Main results

* `Stacks.DerivedQCoh.OpenLift.ringedSiteDerivedTensorProduct`: a derived tensor product of
  sheaves of modules on a ringed site, read as one on its sheaf of rings.
* `Stacks.DerivedQCoh.OpenLift.cohomologySupportedOn_derivedTensorProduct`: the derived tensor
  product preserves a closed cohomological support, at the canonical derived tensor product that
  [Stacks, Tag 08EH] is stated with.
* `Stacks.DerivedQCoh.OpenLift.cohomologySupportedOn_obj₃_of_distinguished`: the objects of
  `D(𝒪_X)` supported on a closed set are closed under cones.
* `Stacks.DerivedQCoh.OpenLift.exists_isPerfect_cohomologySupportedOn_biprod_shift_iso_restrict`:
  **[Stacks, Tag 08EK]**.

## Implementation notes

**Two structures for one derived tensor product.**  [Stacks, Tag 08EH] produces its lift as
`I ⊗^L_{𝒪_X} E` for the bifunctor
`Stacks.SheafOfModules.derivedTensorProductFunctor (Stacks.SheafOfModules.ringedSite X.sheaf)`,
whose datum is a `Stacks.SheafOfModules.DerivedTensorProduct` of a *ringed site*, while the
restriction compatibility of the derived tensor product -- and so
`Stacks.DerivedQCoh.OpenLift.cohomologySupportedOn_compl_derivedTensor` -- is stated for a
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` of a *sheaf of rings*.  The two structures
have the same fields, so `ringedSiteDerivedTensorProduct` reads one as the other without
changing the bifunctor; that is what lets the support statement be applied to the object
[Stacks, Tag 08EH] hands over.

**Restriction spellings.**  [Stacks, Tag 08EH] is stated for
`Stacks.Cohomology.OpenSubspace.derivedRestriction` and everything here for
`Stacks.Duality.OpenImmersion.derivedRestrict`, the spelling the support condition uses; the two
are identified by `Stacks.DerivedQCoh.OpenLift.schemeDerivedRestrictIsoOpenSubspace`, along which
the endomorphism being lifted is transported and the two conclusions are carried back by
`CategoryTheory.NatIso.isIso_map_iff` and `CategoryTheory.NatIso.naturality_2`.  This is the same
transport as in `Stacks.DerivedQCoh.OpenLift.exists_lift_biprod_diag`, done here inline because the
perfect object `I` -- which that statement does not record -- is needed for the support.

**The affine scheme is `Spec A`**, as in [Stacks, Tag 08EH] and [Stacks, Tag 08EI]; the source's
proof opens with "say `X = Spec A`".

## References

* [Stacks Project, Lemma 36.13.10 (Tag 08EK)](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Lemma 36.13.7 (Tag 08EH)](https://stacks.math.columbia.edu/tag/08EH)
* [Stacks Project, Tag 08DA](https://stacks.math.columbia.edu/tag/08DA)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Duality.OpenImmersion (derivedRestrict)
open Stacks.Cohomology.PerfectComplexes
open Stacks.SheafOfModules (ringedSite)

namespace Stacks.DerivedQCoh.OpenLift

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The derived tensor product preserves the support -/

/-- **A derived tensor product of modules on a ringed site, read as one on its sheaf of
rings.**  `Stacks.SheafOfModules.DerivedTensorProduct` and
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` have the same fields; this copies them
across, leaving the bifunctor unchanged. -/
def ringedSiteDerivedTensorProduct (X : Scheme.{u})
    (T : Stacks.SheafOfModules.DerivedTensorProduct (ringedSite X.sheaf)) :
    Stacks.DerivedTensor.RingedSite.DerivedTensorProduct (ringedSite X.sheaf).O where
  tensor := T.tensor
  comparison := T.comparison
  comparison_naturality := T.comparison_naturality
  comparisonRight := T.comparisonRight
  comparisonRight_naturality := T.comparisonRight_naturality
  comparisonRight_eq_comparison := T.comparisonRight_eq_comparison
  comparisonLeft := T.comparisonLeft
  comparisonLeft_naturality := T.comparisonLeft_naturality
  comparisonLeft_eq_comparison := T.comparisonLeft_eq_comparison
  toTensor := T.toTensor
  toTensor_naturality := T.toTensor_naturality
  toTensor_eq_comparisonRight := T.toTensor_eq_comparisonRight
  toTensor_eq_comparisonLeft := T.toTensor_eq_comparisonLeft
  commShift₂ := T.commShift₂
  exact_left := T.exact_left
  exact_right := T.exact_right

/-- **The canonical derived tensor product preserves a closed cohomological support.**  If the
cohomology of `E` is supported on a closed set `T`, so is that of `I ⊗^L_{𝒪_X} E`.

This is `Stacks.DerivedQCoh.OpenLift.cohomologySupportedOn_compl_derivedTensor` at the open
`X ∖ T`, with the derived tensor product the canonical one of
[Stacks, Tag 06YU] read through `ringedSiteDerivedTensorProduct`, which is the bifunctor
[Stacks, Tag 08EH] states its conclusion with. -/
theorem cohomologySupportedOn_derivedTensorProduct (X : Scheme.{u}) (T : Set X) (hT : IsClosed T)
    (I E : DerivedCategory X.Modules)
    (hE : CohomologySupportedOn X.ringCatSheaf T E) :
    CohomologySupportedOn X.ringCatSheaf T
      (((Stacks.SheafOfModules.derivedTensorProductFunctor (ringedSite X.sheaf)).obj I).obj E) := by
  have hV : ((⟨Tᶜ, hT.isOpen_compl⟩ : X.Opens) : Set X)ᶜ = T := compl_compl T
  have h := cohomologySupportedOn_compl_derivedTensor X ⟨Tᶜ, hT.isOpen_compl⟩
    (ringedSiteDerivedTensorProduct X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct (ringedSite X.sheaf)))
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _) I E (by rwa [hV])
  rwa [hV] at h

/-! ### The supported objects are closed under cones -/

/-- **The objects of `D(𝒪_X)` whose cohomology is supported on a closed set are closed under
cones.**  Support on a closed set is vanishing of the restriction to its complement, restriction
is a triangulated functor, and the third object of a distinguished triangle whose first two
objects vanish vanishes. -/
theorem cohomologySupportedOn_obj₃_of_distinguished (X : Scheme.{u}) (T : Set X)
    (hT : IsClosed T) (Tri : Triangle (DerivedCategory X.Modules))
    (hTri : Tri ∈ distTriang (DerivedCategory X.Modules))
    (h₁ : CohomologySupportedOn X.ringCatSheaf T Tri.obj₁)
    (h₂ : CohomologySupportedOn X.ringCatSheaf T Tri.obj₂) :
    CohomologySupportedOn X.ringCatSheaf T Tri.obj₃ := by
  let V : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  let : (derivedRestrict V.ι).IsTriangulated := isTriangulated_derivedRestrict V.ι
  have hV : ((V : X.Opens) : Set X)ᶜ = T := compl_compl T
  have h := cohomologySupportedOn_compl_opens_of_isZero_derivedRestrict V Tri.obj₃
    (Triangle.isZero₃_of_isZero₁₂ ((derivedRestrict V.ι).mapTriangle.obj Tri)
      ((derivedRestrict V.ι).map_distinguished Tri hTri)
      (isZero_derivedRestrict_of_cohomologySupportedOn_of_subset_compl T V subset_rfl Tri.obj₁ h₁)
      (isZero_derivedRestrict_of_cohomologySupportedOn_of_subset_compl T V subset_rfl Tri.obj₂ h₂))
  rwa [hV] at h

/-! ### The cone of the lift -/

variable {A : CommRingCat.{u}}

/-- **Steps 5 and 6 of [Stacks, Tag 08EK], with the lift given.**  Let `C` be a perfect object of
`D(𝒪_{Spec A})` supported on a closed set `T`, identified over a quasi-compact open `U` with a
biproduct `S ⊞ F`, and let `β, γ : E₁ ⟶ C` be maps out of a perfect object supported on `T` such
that `β|_U` is invertible and `β|_U` followed by `diag(1, 0)` conjugated along the
identification is `γ|_U` -- the data [Stacks, Tag 08EH] produces.  Then the cone of `γ` is
perfect, supported on `T`, and restricts to `F ⊕ F[1]` over `U`.

Perfectness of the cone is [Stacks, Tag 08CR], its support is
`cohomologySupportedOn_obj₃_of_distinguished`, and its restriction is computed by
`Stacks.Triangulated.exists_iso_biprod_shift_of_distTriang_of_conj` -- the restricted triangle is
a triangle on `diag(1, 0)`, because `β|_U` is invertible.

`E₁` is a variable, rather than the tensor product [Stacks, Tag 08EH] exhibits: the two spellings
of `D(𝒪_{Spec A})` meet in that tensor product, and keeping it out of this statement keeps the
rewriting below in one spelling. -/
theorem exists_isPerfect_cohomologySupportedOn_cone_of_lift (T : Set (Spec A)) (hT : IsClosed T)
    (U : (Spec A).Opens) (C E₁ : DerivedCategory (Spec A).Modules)
    (hCperf : IsPerfect (X := (Spec A).toRingedSpace) C)
    (hCsupp : CohomologySupportedOn (Spec A).ringCatSheaf T C)
    (hE₁perf : IsPerfect (X := (Spec A).toRingedSpace) E₁)
    (hE₁supp : CohomologySupportedOn (Spec A).ringCatSheaf T E₁)
    (S F : DerivedCategory U.toScheme.Modules)
    (ε : S ⊞ F ≅ (derivedRestrict U.ι).obj C) (β γ : E₁ ⟶ C)
    (hβ : IsIso ((derivedRestrict U.ι).map β))
    (hβγ : (derivedRestrict U.ι).map β ≫
        (ε.inv ≫ ((biprod.fst : S ⊞ F ⟶ S) ≫ (biprod.inl : S ⟶ S ⊞ F)) ≫ ε.hom) =
      (derivedRestrict U.ι).map γ) :
    ∃ E : DerivedCategory (Spec A).Modules,
      IsPerfect (X := (Spec A).toRingedSpace) E ∧
      CohomologySupportedOn (Spec A).ringCatSheaf T E ∧
      Nonempty (F ⊞ F⟦(1 : ℤ)⟧ ≅ (derivedRestrict U.ι).obj E) := by
  let : (derivedRestrict U.ι).CommShift ℤ := inferInstance
  let : (derivedRestrict U.ι).IsTriangulated := isTriangulated_derivedRestrict U.ι
  obtain ⟨E, v, w, hTri⟩ := distinguished_cocone_triangle γ
  have hTri' : (Triangle.mk γ v w : Triangle (DerivedCategory (Spec A).Modules)) ∈
      distTriang (DerivedCategory (Spec A).Modules) := hTri
  refine ⟨E, ?_, ?_, ?_⟩
  · have H := Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished
      (X := (Spec A).toRingedSpace)
    exact H (Triangle.mk γ v w) hTri' hE₁perf hCperf
  · exact cohomologySupportedOn_obj₃_of_distinguished (Spec A) T hT (Triangle.mk γ v w) hTri'
      hE₁supp hCsupp
  · obtain ⟨eFF⟩ := Stacks.Triangulated.exists_iso_biprod_shift_of_distTriang_of_conj S F ε _ _
      hβ _ _ ((derivedRestrict U.ι).map_distinguished (Triangle.mk γ v w) hTri') hβγ
    exact ⟨eFF.symm⟩

/-- **Transporting the conclusion of a lifting statement along an isomorphism of functors.**
If `R'` is isomorphic to `R` by `φ` and `R'.map β` followed by the conjugate of `a` along `φ` is
`R'.map γ`, then `R.map β` followed by `a` is `R.map γ`.  Both sides are
`CategoryTheory.NatIso.naturality_2` away from each other.

Everything is a variable, which is what makes the rewriting go through: the statement it is used
for has a derived tensor product for the source of `β` and `γ`, and `CategoryTheory.Category.assoc`
does not rewrite under it. -/
theorem map_comp_conj_eq_map {C : Type*} [Category* C] {D : Type*} [Category* D] {R R' : C ⥤ D}
    (φ : R ≅ R') {E₁ E₀ E₂ : C} (β : E₁ ⟶ E₀) (γ : E₁ ⟶ E₂) (a : R.obj E₀ ⟶ R.obj E₂)
    (hβγ : R'.map β ≫ φ.inv.app E₀ ≫ a ≫ φ.hom.app E₂ = R'.map γ) :
    R.map β ≫ a = R.map γ := by
  rw [← NatIso.naturality_2 φ β, ← NatIso.naturality_2 φ γ, ← hβγ]
  simp

/-- **[Stacks, Tag 08EH] applied to `diag(1, 0)`, with the perfect tensor factor recorded.**
Let `R` be a functor out of `D(𝒪_{Spec A})` isomorphic to restriction to a quasi-compact open
`U`, let `E₀` be perfect and let `ε : S ⊞ F ≅ R.obj E₀`.  Then there are a perfect object `I` and
maps `β, γ : I ⊗^L_{𝒪_X} E₀ ⟶ E₀` with `R.map β` invertible and `R.map β` followed by
`diag(1, 0)` conjugated along `ε` equal to `R.map γ`.

This is `Stacks.DerivedQCoh.OpenLift.exists_lift_biprod_diag` with the identification of the
source as a derived tensor product kept, which is what the support of the cone needs; the tensor
product is left out of that statement, and of the file it lives in, because that file is written
in the `StrictlyPerfect.OXMod` spelling of `D(𝒪_{Spec A})`.  `R` is a variable here for the same
reason it is there: the transport along `φ` is an equation between composites, and it rewrites
only while the functor is opaque. -/
theorem exists_lift_biprod_diag_tensor (U : (Spec A).Opens)
    (hU : IsCompact (U : Set (Spec A)))
    (R : DerivedCategory (Spec A).Modules ⥤ DerivedCategory U.toScheme.Modules)
    (φ : R ≅ Stacks.Cohomology.OpenSubspace.derivedRestriction (Spec A).ringCatSheaf U)
    (E₀ : DerivedCategory (Spec A).Modules)
    (hE₀ : IsPerfect (X := (Spec A).toRingedSpace) E₀)
    (S F : DerivedCategory U.toScheme.Modules) (ε : S ⊞ F ≅ R.obj E₀) :
    ∃ (I : DerivedCategory (Spec A).Modules)
      (β γ : ((Stacks.SheafOfModules.derivedTensorProductFunctor
        (ringedSite (Spec A).sheaf)).obj I).obj E₀ ⟶ E₀),
      IsPerfect (X := (Spec A).toRingedSpace)
        (((Stacks.SheafOfModules.derivedTensorProductFunctor
          (ringedSite (Spec A).sheaf)).obj I).obj E₀) ∧
      IsIso (R.map β) ∧
      R.map β ≫ (ε.inv ≫ ((biprod.fst : S ⊞ F ⟶ S) ≫ (biprod.inl : S ⟶ S ⊞ F)) ≫ ε.hom) =
        R.map γ := by
  obtain ⟨I, -, hIE, β, γ, hβ, hβγ⟩ :=
    exists_isPerfect_lift_of_isPerfect_of_isDQCoh U hU E₀ E₀ hE₀ (isDQCoh_of_isPerfect E₀ hE₀)
      (φ.inv.app E₀ ≫ (ε.inv ≫
        ((biprod.fst : S ⊞ F ⟶ S) ≫ (biprod.inl : S ⟶ S ⊞ F)) ≫ ε.hom) ≫ φ.hom.app E₀)
  exact ⟨I, β, γ, hIE, (NatIso.isIso_map_iff φ β).mpr hβ,
    map_comp_conj_eq_map φ β γ _ hβγ⟩

/-! ### Tag 08EK -/

/-- **[Stacks, Tag 08EK].**  Let `A` be a commutative ring, `X = Spec A`, let `T ⊆ X` be a closed
set whose complement is quasi-compact and let `U ⊆ X` be a quasi-compact open.  For every perfect
object `F` of `D(𝒪_U)` whose cohomology is supported on `T ∩ U` there is a perfect object `E` of
`D(𝒪_X)` whose cohomology is supported on `T` and with `F ⊕ F[1] ≅ E|_U`.

Steps 1 to 4 of the source are
`Stacks.DerivedQCoh.OpenLift.exists_isPerfect_cohomologySupportedOn_biprod_summand`, giving a
perfect `C` supported on `T` with `S ⊞ F ≅ C|_U`.  [Stacks, Tag 08EH] lifts the endomorphism
`diag(1, 0)` of that biproduct to `β, γ : I ⊗^L C ⟶ C` with `β|_U` invertible; the lifted
endomorphism is the one transported along
`Stacks.DerivedQCoh.OpenLift.schemeDerivedRestrictIsoOpenSubspace`, and its two conclusions are
carried back along the same isomorphism.  `I ⊗^L C` is supported on `T` because `C` is, so
`exists_isPerfect_cohomologySupportedOn_cone_of_lift` finishes.
The tag is registered on
`…OpenLift.exists_isPerfectComplex_supported_restrict_iso_biprod_shift_of_isAffine`
of `StacksFrontier/AlgebraicGeometry/DerivedQCoh/OpenLift/AffineSupportedLift.lean`. -/
theorem exists_isPerfect_cohomologySupportedOn_biprod_shift_iso_restrict (T : Set (Spec A))
    (hT : IsClosed T) (hTc : IsCompact (Tᶜ : Set (Spec A))) (U : (Spec A).Opens)
    (hU : IsCompact (U : Set (Spec A))) (F : DerivedCategory U.toScheme.Modules)
    (hF : IsPerfect (X := U.toScheme.toRingedSpace) F)
    (hFT : CohomologySupportedOn U.toScheme.ringCatSheaf (Subtype.val ⁻¹' T) F) :
    ∃ E : DerivedCategory (Spec A).Modules,
      IsPerfect (X := (Spec A).toRingedSpace) E ∧
      CohomologySupportedOn (Spec A).ringCatSheaf T E ∧
      Nonempty (F ⊞ F⟦(1 : ℤ)⟧ ≅ (derivedRestrict U.ι).obj E) := by
  classical
  obtain ⟨C, S, hCperf, hCsupp, ⟨ε⟩⟩ :=
    exists_isPerfect_cohomologySupportedOn_biprod_summand T hT hTc U hU F hF hFT
  obtain ⟨I, β, γ, hIC, hβ', hβγ'⟩ :=
    exists_lift_biprod_diag_tensor U hU (derivedRestrict U.ι)
      (schemeDerivedRestrictIsoOpenSubspace (Spec A) U) C hCperf S F ε
  exact exists_isPerfect_cohomologySupportedOn_cone_of_lift T hT U C _ hCperf hCsupp hIC
    (cohomologySupportedOn_derivedTensorProduct (Spec A) T hT I C hCsupp) S F ε β γ hβ' hβγ'

end Stacks.DerivedQCoh.OpenLift

end
