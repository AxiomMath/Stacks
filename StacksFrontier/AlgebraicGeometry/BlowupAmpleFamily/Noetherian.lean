module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformModule
public import StacksFrontier.AlgebraicGeometry.BlowupAmpleFamily.Basic
public import StacksFrontier.AlgebraicGeometry.BlowupAmpleFamily.Coproduct
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CompletelyDecomposedCover
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DenseOpenAdmissibleBlowup.AmpleFamily
public import StacksCore.Tactic.StacksAttribute

/-!
# Blowing up and ample families of invertible modules over a Noetherian base

Let `X` be a quasi-compact and quasi-separated scheme. There is a morphism `f : Y ⟶ X` which is
of finite presentation, proper and completely decomposed ([Stacks, Tag 0GTI]) such that `Y` has
an ample family of invertible modules. This is [Stacks, Tag 0GTU]. The first paragraph of the
source's proof, the reduction to a base of finite type over `ℤ`, is
`StacksFrontier/AlgebraicGeometry/BlowupAmpleFamily/Basic.lean`; this file proves the second
paragraph, the case of such a base, and assembles the two.

## Main results

* `Stacks.BlowupAmpleFamily.exists_isProper_isCompletelyDecomposed_isAmpleFamily_of_isNoetherian`:
  a Noetherian scheme is the target of a proper completely decomposed morphism whose source is
  reduced and has an ample family of invertible modules.
* `Stacks.BlowupAmpleFamily.isNoetherian_of_finiteType`: a scheme of finite type over `ℤ` is
  Noetherian.
* `Stacks.BlowupAmpleFamily.exists_finitePresentation_proper_completelyDecomposed_isAmpleFamily`:
  [Stacks, Tag 0GTU].

## Implementation notes

The source argues by induction on the dimension of the base `S`: [Stacks, Tag 0GTT] gives a dense
open `U ⊆ S` and a `U`-admissible blowing up `S' ⟶ S` whose source has an ample family, the
reduced complement `Z = S ∖ U` has smaller dimension, and `S' ⨿ W ⟶ S` is the desired morphism
for a morphism `W ⟶ Z` given by induction.

Here the induction is Noetherian induction over the closed subsets of `S`, in the form of
`AlgebraicGeometry.exists_isProper_isCompletelyDecomposed_of_integral_case`: it assembles a proper
completely decomposed morphism out of binary coproducts of proper morphisms, one for each
*integral* closed subscheme `Z ⊆ S`, each an isomorphism over a dense open of `Z`. This avoids
dimension theory: the complement of a dense open of an integral closed subset is a strictly
smaller closed subset, and a reducible closed subset is split into two strictly smaller ones. The
property carried through the induction is that the source is reduced and has an ample family of
invertible modules.

* Over an integral `Z`, which is Noetherian, Tag 0GTT
  (`Stacks.DenseOpenAdmissibleBlowup.exists_isCompact_dense_admissibleBlowup_isAmpleFamily`)
  gives `U` and the blowing up `Z' ⟶ Z`, which is proper and an isomorphism over `U`. Its
  source is replaced by the reduced induced structure `Z'_red`: the closed immersion
  `Z'_red ⟶ Z'` is affine, so `Z'_red` inherits the ample family
  (`Stacks.BlowupAmpleFamily.exists_isAmpleFamily_of_isAffineHom`), and over `U` it is a
  surjective closed immersion onto a reduced scheme, hence an isomorphism.
* The source of a binary coproduct of the morphisms built so far is the disjoint union of two
  reduced schemes with ample families, which is reduced and has an ample family
  (`Stacks.BlowupAmpleFamily.exists_isAmpleFamily_coprod`).

Finally a proper morphism to a locally Noetherian scheme is of finite presentation, being locally
of finite type, quasi-compact and quasi-separated.

**Why the sources are kept reduced.** The ample family on a disjoint union is built by glueing
invertible modules and sections along the two summands, which are closed immersions with empty
pairwise intersection; the glueing result available for this, [Stacks, Tag 09NE], is stated for a
reduced scheme. Passing to the reduced induced structure costs nothing here, since it changes
neither points nor residue fields, and the induction only ever sees the source through those.

## References

* [Stacks Project, Tag 0GTU](https://stacks.math.columbia.edu/tag/0GTU)
* [Stacks Project, Tag 0GTT](https://stacks.math.columbia.edu/tag/0GTT)
* [Stacks Project, Tag 0GTI](https://stacks.math.columbia.edu/tag/0GTI)
* [Stacks Project, Tag 09NE](https://stacks.math.columbia.edu/tag/09NE)
* [Stacks Project, Tag 0H59](https://stacks.math.columbia.edu/tag/0H59)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.BlowupAmpleFamily

/-- **An admissible blowup is an isomorphism over the open it is admissible for.** The centre of
a `V`-admissible blowup is supported away from `V`, and a blowup is an isomorphism over the
complement of the support of its centre. -/
theorem isIso_morphismRestrict_of_isAdmissibleBlowup {Y Y' : Scheme.{u}} {V : Y.Opens}
    {g : Y' ⟶ Y} (hg : Stacks.Blowup.IsAdmissibleBlowup V g) : IsIso (g ∣_ V) := by
  obtain ⟨I, -, hdisj, e, he⟩ := hg
  have h : IsIso (Stacks.Blowup.blowUpToBase I ∣_ V) :=
    Stacks.Blowup.isIso_blowUpToBase_restrict_of_subset_compl_support_reesData I V
      fun _ hz ↦ Set.disjoint_left.mp hdisj hz
  have h' : IsIso (e.hom ∣_ Stacks.Blowup.blowUpToBase I ⁻¹ᵁ V) := inferInstance
  rw [← he, morphismRestrict_comp]
  exact IsIso.comp_isIso' h' h

/-- An empty scheme is reduced: its only ring of sections is the zero ring. -/
theorem isReduced_of_isEmpty (T : Scheme.{u}) [IsEmpty T] : IsReduced T := by
  refine ⟨fun U => ?_⟩
  obtain rfl : U = ⊥ := Opens.ext (Set.eq_empty_of_isEmpty _)
  have : Subsingleton Γ(T, ⊥) :=
    CommRingCat.subsingleton_of_isTerminal T.sheaf.isTerminalOfEmpty
  infer_instance

/-- A disjoint union of two reduced schemes is reduced, being covered by them. -/
theorem isReduced_coprod (A B : Scheme.{u}) [IsReduced A] [IsReduced B] :
    IsReduced (A ⨿ B : Scheme.{u}) := by
  have : ∀ i, IsReduced ((coprodOpenCover.{u, 0} A B).X i) := by
    rintro (_ | _)
    · exact ‹IsReduced A›
    · exact ‹IsReduced B›
  exact IsReduced.of_openCover (𝒰 := coprodOpenCover.{u, 0} A B)

/-- **The second paragraph of the proof of [Stacks, Tag 0GTU], over a Noetherian base.** A
Noetherian scheme `S` is the target of a proper completely decomposed morphism `g : T ⟶ S` whose
source is reduced and has an ample family of invertible modules. -/
theorem exists_isProper_isCompletelyDecomposed_isAmpleFamily_of_isNoetherian (S : Scheme.{u})
    [IsNoetherian S] :
    ∃ (T : Scheme.{u}) (g : T ⟶ S), IsProper g ∧ IsCompletelyDecomposed g ∧ IsReduced T ∧
      ∃ (J : Type u) (N : J → T.Modules), T.IsAmpleFamily N := by
  obtain ⟨T, g, hp, ⟨hred, hamp⟩, hcd⟩ := exists_isProper_isCompletelyDecomposed_of_integral_case
    (S := S) (fun {T} _ => IsReduced T ∧ ∃ (J : Type u) (N : J → T.Modules), T.IsAmpleFamily N)
    (fun {T} _ hT => ⟨isReduced_of_isEmpty T, _, _, isAmpleFamily_of_isEmpty T⟩)
    (fun {T₁ T₂} _ _ ⟨h₁, J₁, N₁, hN₁⟩ ⟨h₂, J₂, N₂, hN₂⟩ => by
      have := isReduced_coprod T₁ T₂
      exact ⟨this, exists_isAmpleFamily_coprod T₁ T₂ hN₁ hN₂⟩)
    (fun I hI => by
      let Z := I.subscheme
      have : IsNoetherian Z := isNoetherian_source_of_isProper I.subschemeι
      have : Finite (irreducibleComponents Z) := finite_irreducibleComponents_of_isNoetherian
      obtain ⟨U, -, hUd, X', f, hadm, J, N, hN⟩ :=
        Stacks.DenseOpenAdmissibleBlowup.exists_isCompact_dense_admissibleBlowup_isAmpleFamily Z
      have hfp : IsProper f := Stacks.Blowup.IsAdmissibleBlowup.isProper hadm
      have hfU : IsIso (f ∣_ U) := isIso_morphismRestrict_of_isAdmissibleBlowup hadm
      let R := (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X')).subscheme
      let ρ : R ⟶ X' := (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X')).subschemeι
      have hρ : Surjective ρ := ⟨fun x => show x ∈ Set.range ρ by
        rw [Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]; trivial⟩
      have hρU : IsIso ((ρ ≫ f) ∣_ U) := by
        rw [morphismRestrict_comp]
        have : IsReduced (f ⁻¹ᵁ U).toScheme :=
          isReduced_of_isOpenImmersion (f ∣_ U ≫ U.ι)
        have : Surjective (ρ ∣_ f ⁻¹ᵁ U) := IsZariskiLocalAtTarget.restrict hρ (f ⁻¹ᵁ U)
        have : IsIso (ρ ∣_ f ⁻¹ᵁ U) := isIso_of_isClosedImmersion_of_surjective _
        exact IsIso.comp_isIso' this hfU
      obtain ⟨K, M, hM⟩ := exists_isAmpleFamily_of_isAffineHom ρ N hN
      exact ⟨R, ρ ≫ f, inferInstance, ⟨inferInstance, K, M, hM⟩, U, hUd, hρU⟩)
  exact ⟨T, g, hp, hcd, hred, hamp⟩

/-- **[Stacks, Tag 0GTU] over a Noetherian base.** A Noetherian scheme is the target of a morphism
which is of finite presentation, proper and completely decomposed and whose source has an ample
family of invertible modules. Over a locally Noetherian base a proper morphism is of finite
presentation. -/
theorem exists_finitePresentation_proper_completelyDecomposed_isAmpleFamily_of_isNoetherian
    (S : Scheme.{u}) [IsNoetherian S] :
    ∃ (T : Scheme.{u}) (g : T ⟶ S), FinitePresentation g ∧ IsProper g ∧
      IsCompletelyDecomposed g ∧ ∃ (J : Type u) (N : J → T.Modules), T.IsAmpleFamily N := by
  obtain ⟨T, g, hp, hcd, -, hamp⟩ :=
    exists_isProper_isCompletelyDecomposed_isAmpleFamily_of_isNoetherian S
  exact ⟨T, g, ⟨LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance,
    inferInstance, inferInstance⟩, hp, hcd, hamp⟩

/-- **A scheme of finite type over `ℤ` is Noetherian.** Finite type over `ℤ` is spelled, as in
the reduction of `StacksFrontier/AlgebraicGeometry/BlowupAmpleFamily/Basic.lean`, through the
morphism to the terminal scheme, which is `Spec ℤ`. -/
theorem isNoetherian_of_finiteType (X₀ : Scheme.{u}) (h₁ : LocallyOfFiniteType (terminal.from X₀))
    (h₂ : QuasiCompact (terminal.from X₀)) : IsNoetherian X₀ := by
  let e : (⊤_ Scheme.{u}) ≅ Spec (.of (ULift.{u} ℤ)) :=
    terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : LocallyOfFiniteType (terminal.from X₀ ≫ e.hom) := inferInstance
  have : QuasiCompact (terminal.from X₀ ≫ e.hom) := inferInstance
  have : IsLocallyNoetherian X₀ :=
    LocallyOfFiniteType.isLocallyNoetherian (terminal.from X₀ ≫ e.hom)
  have : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace (terminal.from X₀ ≫ e.hom)
  exact ⟨⟩

/-- **[Stacks, Tag 0GTU].** Let `X` be a quasi-compact and quasi-separated scheme. There is a
morphism of schemes `f : Y ⟶ X` which is of finite presentation, proper and completely
decomposed ([Stacks, Tag 0GTI]) and such that `Y` has an ample family of invertible modules.

The reduction to a base of finite type over `ℤ` is
`exists_finitePresentation_proper_completelyDecomposed_isAmpleFamily_of_finiteTypeCase`, and the
case of such a base, which is Noetherian, is
`exists_finitePresentation_proper_completelyDecomposed_isAmpleFamily_of_isNoetherian`. -/
@[stacks 0GTU]
theorem exists_finitePresentation_proper_completelyDecomposed_isAmpleFamily
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), FinitePresentation f ∧ IsProper f ∧
      IsCompletelyDecomposed f ∧ ∃ (J : Type u) (N : J → Y.Modules), Y.IsAmpleFamily N :=
  exists_finitePresentation_proper_completelyDecomposed_isAmpleFamily_of_finiteTypeCase X
    fun X₀ h₁ h₂ => by
      have := isNoetherian_of_finiteType X₀ h₁ h₂
      exact exists_finitePresentation_proper_completelyDecomposed_isAmpleFamily_of_isNoetherian X₀

end Stacks.BlowupAmpleFamily

end
