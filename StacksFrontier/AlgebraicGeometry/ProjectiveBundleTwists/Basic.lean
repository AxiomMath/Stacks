module

public import StacksFrontier.AlgebraicGeometry.GluedTwistAlgebra.Assemble
public import StacksFrontier.AlgebraicGeometry.SymGenDegreeOne.Consumers
public import StacksFrontier.AlgebraicGeometry.SymGenDegreeOne.ProjectiveBundleTwists
public import StacksFrontier.AlgebraicGeometry.SymmetricSituation.Quasicoherence
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Sections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twists `𝒪(n)` of the projective bundle of a quasi-coherent module

Let `X` be a scheme and `E` a quasi-coherent `𝒪_X`-module.
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra X E` is the symmetric algebra `Sym(E)`, as a
sheaf of graded `𝒪_X`-algebras, and `Stacks.SymGraded.schemeProjectiveBundle` is its relative
homogeneous spectrum, the projective bundle `𝐏(E) = Proj_X(Sym(E))` with its projection `π`.

This file constructs the **twists** `𝒪_{𝐏(E)}(n)` of that bundle, proves they are invertible, and
produces the **universal degree-one map** `π^*E ⟶ 𝒪_{𝐏(E)}(1)`. All of this is unconditional
beyond quasi-coherence of `E`; in particular nothing is assumed about the rank of `E`.

The twists are the glued twists of the twist datum
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` of `Sym(E)` (Tag 01NR).
Since `Sym(E)` is generated in degree one over every affine open of the base
(`Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra`), they are invertible by
`Stacks.AlgebraicGeometry.TwistMapsInvertible.twistData_isInvertible` (Tag 01O4). The degree-one
map is the homogeneous-section map `ψ 1` of the twist datum, read through the identification of
`Sym¹(E)` with `E`.

## Main definitions

* `Stacks.SymGraded.siteGenIso`: the isomorphism `F ≅ Sym¹ F`, sectionwise, for a presheaf of
  modules `F`.
* `Stacks.SymGraded.symmetricAlgebraGenIso` and `Stacks.SymGraded.symmetricAlgebraPieceOneIso`: the
  isomorphism `E ≅ Sym(E)₁` and its inverse, for a module sheaf `E` on a scheme.
* `Stacks.SymGraded.projectiveBundleTwist`: the twist `𝒪_{𝐏(E)}(n)`, the degree-`n` piece of the
  glued algebra of `Stacks.SymGraded.projectiveBundleTwistData`.
* `Stacks.SymGraded.projectiveBundleTwistGen`: the universal degree-one map `E ⟶ π_*𝒪(1)`, and
  `Stacks.SymGraded.projectiveBundleTwistUniv`: its adjoint `π^*E ⟶ 𝒪(1)`.
* `Stacks.SymGraded.bundleComparison`, `Stacks.SymGraded.bundleTwist` and
  `Stacks.SymGraded.bundleTwistUniv`: the same twist and the same universal map carried across
  `AlgebraicGeometry.projectiveBundlePresentationsAgree` onto
  `Stacks.RelativeProj.projectiveBundle`.

## Main results

* `Stacks.SymGraded.isIso_siteGen` and `Stacks.SymGraded.isIso_symmetricAlgebraGen`: the two
  degree-one generators are isomorphisms.
* `Stacks.SymGraded.isInvertible_projectiveBundleTwistOfQuasicoherent`: every twist `𝒪_{𝐏(E)}(n)`
  is invertible, with no hypothesis beyond quasi-coherence of `E`.
* `Stacks.SymGraded.projectiveBundleTwistUniv_adjoint`: the degree-one map and its adjoint
  correspond under `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`.
* `Stacks.SymGraded.isInvertible_bundleTwist`: the transported twist is invertible.
* `Stacks.SymGraded.exists_tautologicalDatum_of_epi`: if `Stacks.SymGraded.bundleTwistUniv` is an
  epimorphism, then `Stacks.RelativeProj.TautologicalDatum X E` is inhabited.

## Implementation notes

`Stacks.SymGraded.schemeSheafGradedAlgebra` takes `Stacks.SymGraded.IsQuasicoherentPieces E` as
data, and a different witness gives a syntactically different graded algebra, so the declarations
here quantify over the witness `hqc`. `Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent`
is the canonical one, and the `…OfQuasicoherent` declarations are the specialisations at it.

`AlgebraicGeometry.projectiveBundlePresentationsAgree` states existentially that the two glueings
of `Proj_X(Sym E)` are isomorphic over `X`, so `Stacks.SymGraded.bundleComparison` is a chosen
witness. Nothing depends on which witness is chosen, only on
`Stacks.SymGraded.bundleComparison_hom_comp_toBase`.

The twist is `D.algebra.piece n` with no transport: the glued graded algebra of a twist datum
lives over the sheaf of rings of the ringed site of the relative `Proj`, and
`Stacks.CategoryTheory.RingedSite.ringSheaf_ofScheme` makes that `Scheme.ringCatSheaf` on the
nose, so a homogeneous piece is already an object of the scheme's category of modules.

`TwistData.ψ` is indexed by `n : ℕ` and lands in degree `((n : ℕ) : ℤ)`, which at `n = 1` is the
integer `1` definitionally, so the composite with the degree-one generator needs no transport.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)

## Not done here

**No `@[stacks]` attribute is attached.** Tag 01OB asks for the projective bundle *together with*
its twists, and the clause about the bundle and its projection is already carried by
`Stacks.RelativeProj.projectiveBundle`. What Tag 01OB asks of the twists is that they be the
twists of Tag 01O4, i.e. of the universal invertible quotient, and that is a statement about a
universal property which is not available: `Stacks.RelativeProj.TautologicalDatum.IsUniversal`
is uninhabited at rank at least two. The twists built here are the glued twists of Tag 01NR with
Tag 01O4's invertibility, which is strictly less than the tag's clause, so placing the label is
left to the pass that can close that gap.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open PresheafOfModules
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.GluedTwistAlgebra
open Stacks.AlgebraicGeometry.TwistMapsInvertible

namespace Stacks.SymGraded

universe v u w

/-! ### Degree one of the sectionwise symmetric algebra -/

section Sectionwise

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat))

/-- The degree-one inclusion of the sectionwise symmetric algebra is injective on sections,
`SymmetricAlgebra.ι` being injective. -/
theorem siteGen_injective (Y : Cᵒᵖ) :
    Function.Injective (Hom.app (siteGen F) Y) := fun _ _ h =>
  SymmetricAlgebra.ι_injective _ _ (congrArg Subtype.val h)

/-- The degree-one inclusion of the sectionwise symmetric algebra is surjective on sections:
`Sym¹` is the range of `SymmetricAlgebra.ι`. -/
theorem siteGen_surjective (Y : Cᵒᵖ) :
    Function.Surjective (Hom.app (siteGen F) Y) := by
  rintro ⟨x, hx⟩
  replace hx : x ∈ SymPow.symmetricPower 1 ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y) := hx
  rw [SymPow.symmetricPower, pow_one] at hx
  obtain ⟨m, rfl⟩ := hx
  exact ⟨m, Subtype.ext rfl⟩

/-- **The degree-one inclusion of the sectionwise symmetric algebra is an isomorphism**: the
degree-one piece of `Sym_{O(Y)}(F(Y))` is `F(Y)`, naturally in `Y`. -/
def siteGenIso : F ≅ siteGradedPiece F 1 := by
  have hiso : ∀ Y : Cᵒᵖ, IsIso ((siteGen F).app Y) := fun Y =>
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨siteGen_injective F Y, siteGen_surjective F Y⟩
  refine isoMk (fun Y => asIso ((siteGen F).app Y)) ?_
  intro Y Z f
  exact (siteGen F).naturality f

/-- The forward map of `Stacks.SymGraded.siteGenIso` is the degree-one inclusion. -/
@[simp]
theorem siteGenIso_hom : (siteGenIso F).hom = siteGen F := rfl

/-- The degree-one inclusion `F ⟶ Sym¹ F` of the sectionwise symmetric algebra is an isomorphism.
-/
theorem isIso_siteGen : IsIso (siteGen F) := by
  rw [← siteGenIso_hom]
  infer_instance

end Sectionwise

/-! ### Degree one of `Sym(E)` on a scheme -/

section DegreeOne

variable {X : Scheme.{u}} (E : X.Modules)

/-- **`E ≅ Sym(E)₁`**, the degree-one generator of the symmetric algebra of a module sheaf on a
scheme: the identification of `E` with the sheafification of `E`, followed by the sheafification
of the sectionwise degree-one inclusion. -/
def symmetricAlgebraGenIso : E ≅ (Scheme.Modules.symmetricAlgebra X E).piece 1 :=
  (Scheme.Modules.sheafificationIso X E).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (siteGenIso E.val)

/-- The forward map of `Stacks.SymGraded.symmetricAlgebraGenIso` is the degree-one generator
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebraGen`. -/
@[simp]
theorem symmetricAlgebraGenIso_hom :
    (symmetricAlgebraGenIso E).hom = Scheme.Modules.symmetricAlgebraGen X E := rfl

/-- **The degree-one generator `E ⟶ Sym(E)₁` is an isomorphism.** -/
theorem isIso_symmetricAlgebraGen : IsIso (Scheme.Modules.symmetricAlgebraGen X E) :=
  ⟨⟨(symmetricAlgebraGenIso E).inv, (symmetricAlgebraGenIso E).hom_inv_id,
    (symmetricAlgebraGenIso E).inv_hom_id⟩⟩

/-- **Degree one of `Sym(E)` is `E`.** -/
def symmetricAlgebraPieceOneIso : (Scheme.Modules.symmetricAlgebra X E).piece 1 ≅ E :=
  (symmetricAlgebraGenIso E).symm

end DegreeOne

/-! ### The twists of the projective bundle -/

section Twists

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (hqc : IsQuasicoherentPieces E)

/-- **The twist `𝒪_{𝐏(E)}(n)` of the projective bundle of a quasi-coherent module**, the
degree-`n` piece of the glued graded algebra of twists on `𝐏(E) = Proj_X(Sym(E))`. -/
@[ega "II 4.1.1"]
def projectiveBundleTwist (n : ℤ) : (schemeProjectiveBundle E hqc).scheme.Modules :=
  (projectiveBundleTwistData E hqc).algebra.piece n

/-! ### The universal degree-one map -/

/-- **The universal degree-one map `E ⟶ π_*𝒪_{𝐏(E)}(1)`**: the homogeneous-section map of the
twist datum in degree one, read out of `E` through the identification of `E` with `Sym(E)₁`. -/
def projectiveBundleTwistGen :
    E ⟶ (Scheme.Modules.pushforward (schemeProjectiveBundle E hqc).toBase).obj
      (projectiveBundleTwist E hqc 1) :=
  Scheme.Modules.symmetricAlgebraGen X E ≫ (projectiveBundleTwistData E hqc).ψ 1

/-- **The universal map `π^*E ⟶ 𝒪_{𝐏(E)}(1)`** of the projective bundle of a quasi-coherent
module: the adjoint of `Stacks.SymGraded.projectiveBundleTwistGen`. -/
def projectiveBundleTwistUniv :
    (Scheme.Modules.pullback (schemeProjectiveBundle E hqc).toBase).obj E ⟶
      projectiveBundleTwist E hqc 1 :=
  ((Scheme.Modules.pullbackPushforwardAdjunction
    (schemeProjectiveBundle E hqc).toBase).homEquiv E (projectiveBundleTwist E hqc 1)).symm
      (projectiveBundleTwistGen E hqc)

omit [SheafOfModules.IsQuasicoherent E] in
/-- The two forms of the universal map correspond under the adjunction
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`. -/
theorem projectiveBundleTwistUniv_adjoint :
    (Scheme.Modules.pullbackPushforwardAdjunction
        (schemeProjectiveBundle E hqc).toBase).homEquiv E (projectiveBundleTwist E hqc 1)
      (projectiveBundleTwistUniv E hqc) = projectiveBundleTwistGen E hqc :=
  Equiv.apply_symm_apply _ _

end Twists

/-! ### The specialisations at the canonical quasi-coherence witness -/

section Canonical

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]

/-- Tag 01NR's twist datum of `Sym(E)` at the canonical quasi-coherence witness. -/
def projectiveBundleTwistDataOfQuasicoherent :
    TwistData (schemeSheafGradedAlgebra E (isQuasicoherentPieces_of_isQuasicoherent E)) :=
  projectiveBundleTwistData E (isQuasicoherentPieces_of_isQuasicoherent E)

/-- **The twists of `𝐏(E)` are invertible**, at the canonical quasi-coherence witness. -/
theorem isInvertible_projectiveBundleTwistOfQuasicoherent (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (schemeProjectiveBundle E (isQuasicoherentPieces_of_isQuasicoherent E)).scheme.presheaf
      (schemeProjectiveBundle E (isQuasicoherentPieces_of_isQuasicoherent E)).scheme.ringCatSheaf.2
      (projectiveBundleTwist E (isQuasicoherentPieces_of_isQuasicoherent E) n) :=
  isInvertible_projectiveBundleTwist E (isQuasicoherentPieces_of_isQuasicoherent E) n

/-- **The universal map `π^*E ⟶ 𝒪_{𝐏(E)}(1)`** at the canonical quasi-coherence witness. -/
def projectiveBundleTwistUnivOfQuasicoherent :
    (Scheme.Modules.pullback
        (schemeProjectiveBundle E (isQuasicoherentPieces_of_isQuasicoherent E)).toBase).obj E ⟶
      projectiveBundleTwist E (isQuasicoherentPieces_of_isQuasicoherent E) 1 :=
  projectiveBundleTwistUniv E (isQuasicoherentPieces_of_isQuasicoherent E)

end Canonical

/-! ### The twists on the other presentation of the bundle -/

section Transport

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (hqc : IsQuasicoherentPieces E)

/-- **The chosen isomorphism over the base between the two presentations of `𝐏(E)`**: the
`SheafGradedAlgebra` glueing `Stacks.SymGraded.schemeProjectiveBundle` and the `Situation`
glueing `Stacks.RelativeProj.projectiveBundle`, chosen from
`AlgebraicGeometry.projectiveBundlePresentationsAgree`. -/
def bundleComparison :
    (schemeProjectiveBundle E hqc).scheme ≅ Stacks.RelativeProj.projectiveBundle X E :=
  (AlgebraicGeometry.projectiveBundlePresentationsAgree E hqc).choose

/-- The comparison is a morphism over the base. -/
theorem bundleComparison_hom_comp_toBase :
    (bundleComparison E hqc).hom ≫ Stacks.RelativeProj.projectiveBundleToBase X E =
      (schemeProjectiveBundle E hqc).toBase :=
  (AlgebraicGeometry.projectiveBundlePresentationsAgree E hqc).choose_spec

/-- The inverse comparison is a morphism over the base. -/
theorem bundleComparison_inv_comp_toBase :
    (bundleComparison E hqc).inv ≫ (schemeProjectiveBundle E hqc).toBase =
      Stacks.RelativeProj.projectiveBundleToBase X E := by
  rw [← bundleComparison_hom_comp_toBase E hqc, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- **The twist `𝒪_{𝐏(E)}(n)` on `Stacks.RelativeProj.projectiveBundle`**: the twist
`Stacks.SymGraded.projectiveBundleTwist`, pulled back along the comparison
`Stacks.SymGraded.bundleComparison`. -/
def bundleTwist (n : ℤ) : (Stacks.RelativeProj.projectiveBundle X E).Modules :=
  (Scheme.Modules.pullback (bundleComparison E hqc).inv).obj (projectiveBundleTwist E hqc n)

/-- **The twist `𝒪_{𝐏(E)}(n)` on `Stacks.RelativeProj.projectiveBundle` is invertible.** -/
theorem isInvertible_bundleTwist (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.RelativeProj.projectiveBundle X E).presheaf
      (Stacks.RelativeProj.projectiveBundle X E).ringCatSheaf.2 (bundleTwist E hqc n) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
    (@Stacks.Modules.isInvertible_pullback _ _ (bundleComparison E hqc).inv
      (projectiveBundleTwist E hqc n) (stacksIsInvertible_projectiveBundleTwist E hqc n))

/-- **The universal map `π^*E ⟶ 𝒪_{𝐏(E)}(1)` on `Stacks.RelativeProj.projectiveBundle`**, for
`π` the projection of that presentation of the bundle. -/
def bundleTwistUniv :
    (Scheme.Modules.pullback (Stacks.RelativeProj.projectiveBundleToBase X E)).obj E ⟶
      bundleTwist E hqc 1 :=
  (Scheme.Modules.pullbackCongr (bundleComparison_inv_comp_toBase E hqc)).inv.app E ≫
    (Scheme.Modules.pullbackComp (bundleComparison E hqc).inv
      (schemeProjectiveBundle E hqc).toBase).inv.app E ≫
    (Scheme.Modules.pullback (bundleComparison E hqc).inv).map (projectiveBundleTwistUniv E hqc)

/-- If the universal map `Stacks.SymGraded.bundleTwistUniv` is an epimorphism, then there is a
tautological datum `Stacks.RelativeProj.TautologicalDatum X E` on `𝐏(E)`. -/
theorem exists_tautologicalDatum_of_epi
    (h : Epi (bundleTwistUniv E hqc)) : Nonempty (Stacks.RelativeProj.TautologicalDatum X E) :=
  ⟨{ twist := bundleTwist E hqc 1
     invertible := isInvertible_bundleTwist E hqc 1
     univ := bundleTwistUniv E hqc
     epi_univ := h }⟩

end Transport

end Stacks.SymGraded

end
