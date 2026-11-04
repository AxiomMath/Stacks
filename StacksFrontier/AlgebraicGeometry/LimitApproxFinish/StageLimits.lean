module

public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.CompatibleOpens
public import StacksFrontier.AlgebraicGeometry.NoetherianApproximation.GluePair

/-!
# Assembling the limit of the glued stages

Three tools for the gluing half of the one-affine-open step of Tag 07RN.

The step glues, at each finite stage, the model `V_i` of the already approximated part to an
affine scheme `Spec A_{i,p}` along their common open `W_i`, and must then recognize the ambient
scheme `S` as the inverse limit of the glued stages.  Both halves of that recognition are here.

## What is built, and the route

* `AlgebraicGeometry.isLimitSpecMapCone` says that the spectrum of a filtered colimit of rings
  is the inverse limit of the spectra of the stages.  It is one line: `AlgebraicGeometry.Scheme`
  `.Spec` is a right adjoint, so it preserves limits, and a colimit cocone of rings is a limit
  cone in the opposite category.  This is what identifies the affine open being added, which is
  the spectrum of the colimit of the finite-type subalgebras produced by Tag 01Z7, as the limit
  of their spectra.

* `AlgebraicGeometry.isLimitOfCompatibleOpensPair` is the two-open form of
  `AlgebraicGeometry.isLimitOfCompatibleOpensCover`: a cone over a cofiltered diagram of schemes
  is limiting as soon as there are *two* compatible families of opens which cover one stage and
  for which the restricted cones — the two families and their intersection — are limiting.  The
  general result asks for a family of compatible families closed under intersection; the content
  added here is the three-element index type `AlgebraicGeometry.CompatibleOpensPairIndex` which
  realizes a pair together with its intersection as such a family, and the nine-case
  verification that it is closed under intersection.

  In the application the first family is the system of models of the part already approximated,
  the second is the system of models of the affine open being added, and the third — the
  intersection — is the system of models of the overlap; the three restricted cones are limiting
  by hypothesis, by `AlgebraicGeometry.isLimitSpecMapCone` and by
  `AlgebraicGeometry.isLimitLaterCompatibleOpensCone` respectively.  This is the step which
  finally discharges the `CategoryTheory.Limits.IsLimit` hypothesis that every result in
  `FiniteTypeApproximation.CompatibleOpens` consumes; the producer of those hypotheses is
  `AlgebraicGeometry.isLimitCompatibleOpensCone`.

* `AlgebraicGeometry.Scheme.quasiCompact_terminal_from_gluePair` completes the finite-type
  bookkeeping for a glued stage.  `AlgebraicGeometry.Scheme.compactSpace_gluePair` gives
  compactness of the space and
  `AlgebraicGeometry.Scheme.locallyOfFiniteType_terminal_from_gluePair` gives local finite type,
  but the structure which records the conclusion of Tag 07RN asks for quasi-compactness of the
  structural morphism, which is Mathlib's `AlgebraicGeometry.compactSpace_iff_quasiCompact`
  applied to the former.  There is no gap here: with these three facts every glued stage meets
  the finite-type requirements on the stages.

## Implementation notes

The index universes are tied to the scheme universe for the spectrum statement: `Scheme.Spec`
preserves limits of shape `K` with `K` and its homs in the universe of the schemes, which is the
same restriction that Mathlib's file on affine-transition limits lives under, and freeing it
costs the synthesis of the colimits of `CommRingCat` that the preservation statement rests on.
The cover statement leaves the index universes of the diagram free, since nothing in it needs
rings.

Transparency gotchas:

* The hypotheses of `AlgebraicGeometry.isLimitOfCompatibleOpensPair` mention
  `AlgebraicGeometry.compatibleOpensCone` applied to proofs built here
  (`AlgebraicGeometry.preimage_inf_compatible` and
  `AlgebraicGeometry.preimage_inf_eq_of_preimage_eq`).  Supplying a different proof of the same
  two propositions is harmless: they are propositions, so the cones agree.

* `AlgebraicGeometry.compatibleOpensFamilyOfPair` is defined by cases on the index, so each of
  its three values is reduced by `rfl`; that is what lets the three limit hypotheses be passed
  straight through to `AlgebraicGeometry.isLimitOfCompatibleOpensCover`.

## What is NOT done here

Neither file in this directory constructs an inhabitant of
`AlgebraicGeometry.Scheme.FiniteTypeApproximation`, and Tag 07RN is not proved.  What is still
missing between here and that: the eventual open immersion of a stage of the overlap into the
spectrum of the fibre product ring (Tags 01P7, 01Z5, 01Z0 and 01Z9), the functor on the
disjoint union of the stage indices whose values are the glued schemes, and the induction over
the finitely many affine opens.  No tag attribute is attached to anything in this file.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01YT](https://stacks.math.columbia.edu/tag/01YT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v w u

namespace AlgebraicGeometry

/-! ### Spectra of a filtered colimit of rings -/

/-- **The spectrum of a colimit of rings is the inverse limit of the spectra.**  Mathlib's
`AlgebraicGeometry.Scheme.Spec` is a right adjoint, hence preserves limits, and a colimit cocone
of rings is a limit cone in the opposite category. -/
noncomputable def isLimitSpecMapCone {K : Type u} [Category.{u} K] {F : K ⥤ CommRingCat.{u}}
    {c : Cocone F} (hc : IsColimit c) : IsLimit (Scheme.Spec.mapCone c.op) :=
  isLimitOfPreserves Scheme.Spec hc.op

/-! ### Detecting a limit on a two-element compatible cover -/

/-- The index of a pair of compatible families of opens together with their intersection.  This
is the smallest family closed under intersection containing a given pair, and it is what turns
`AlgebraicGeometry.isLimitOfCompatibleOpensCover` into a statement about two opens. -/
inductive CompatibleOpensPairIndex
  /-- The first family of the pair. -/
  | first
  /-- The second family of the pair. -/
  | second
  /-- The intersection of the two families. -/
  | inter

namespace CompatibleOpensPair

variable {J : Type w} [Category.{v} J] {D : J ⥤ Scheme.{u}} {c : Cone D}

/-- The intersection of two compatible families of opens is compatible. -/
lemma preimage_inf_compatible {V₁ V₂ : ∀ j, (D.obj j).Opens}
    (hV₁ : ∀ ⦃j k : J⦄ (f : j ⟶ k), D.map f ⁻¹ᵁ V₁ k = V₁ j)
    (hV₂ : ∀ ⦃j k : J⦄ (f : j ⟶ k), D.map f ⁻¹ᵁ V₂ k = V₂ j)
    ⦃j k : J⦄ (f : j ⟶ k) : D.map f ⁻¹ᵁ (V₁ k ⊓ V₂ k) = V₁ j ⊓ V₂ j := by
  rw [Scheme.Hom.preimage_inf, hV₁ f, hV₂ f]

/-- The legs of a cone cut the intersection of two compatible families of opens out of the
intersection of the two opens they cut out individually. -/
lemma preimage_inf_eq_of_preimage_eq {V₁ V₂ : ∀ j, (D.obj j).Opens} {U₁ U₂ : c.pt.Opens}
    (hU₁ : ∀ j, c.π.app j ⁻¹ᵁ V₁ j = U₁) (hU₂ : ∀ j, c.π.app j ⁻¹ᵁ V₂ j = U₂) (j : J) :
    c.π.app j ⁻¹ᵁ (V₁ j ⊓ V₂ j) = U₁ ⊓ U₂ := by
  rw [Scheme.Hom.preimage_inf, hU₁ j, hU₂ j]

/-- The three-member family of compatible families of opens generated by a pair. -/
def family (V₁ V₂ : ∀ j, (D.obj j).Opens) :
    CompatibleOpensPairIndex → ∀ j, (D.obj j).Opens
  | .first => V₁
  | .second => V₂
  | .inter => fun j ↦ V₁ j ⊓ V₂ j

/-- The three opens of the vertex cut out by `AlgebraicGeometry.CompatibleOpensPair.family`. -/
def vertexFamily (U₁ U₂ : c.pt.Opens) : CompatibleOpensPairIndex → c.pt.Opens
  | .first => U₁
  | .second => U₂
  | .inter => U₁ ⊓ U₂

end CompatibleOpensPair

open CompatibleOpensPair in
/-- **Limits of schemes are detected on a two-element compatible open cover.**  Let `c` be a cone
over a cofiltered diagram of schemes, let `V₁` and `V₂` be compatible families of opens cutting
`U₁` and `U₂` out of the vertex, and suppose `V₁` and `V₂` cover one stage.  If the restricted
cones over `V₁`, over `V₂` and over their intersection are limiting, then `c` is limiting.

This is `AlgebraicGeometry.isLimitOfCompatibleOpensCover` applied to the family generated by the
pair, which is closed under intersection. -/
noncomputable def isLimitOfCompatibleOpensPair {J : Type w} [Category.{v} J] [IsCofiltered J]
    {D : J ⥤ Scheme.{u}} {c : Cone D} {V₁ V₂ : ∀ j, (D.obj j).Opens} {U₁ U₂ : c.pt.Opens}
    (hV₁ : ∀ ⦃j k : J⦄ (f : j ⟶ k), D.map f ⁻¹ᵁ V₁ k = V₁ j)
    (hV₂ : ∀ ⦃j k : J⦄ (f : j ⟶ k), D.map f ⁻¹ᵁ V₂ k = V₂ j)
    (hU₁ : ∀ j, c.π.app j ⁻¹ᵁ V₁ j = U₁) (hU₂ : ∀ j, c.π.app j ⁻¹ᵁ V₂ j = U₂)
    (j₀ : J) (hcover : V₁ j₀ ⊔ V₂ j₀ = ⊤)
    (h₁ : IsLimit (compatibleOpensCone D c V₁ hV₁ U₁ hU₁))
    (h₂ : IsLimit (compatibleOpensCone D c V₂ hV₂ U₂ hU₂))
    (h₃ : IsLimit (compatibleOpensCone D c (fun j ↦ V₁ j ⊓ V₂ j)
      (preimage_inf_compatible hV₁ hV₂) (U₁ ⊓ U₂) (preimage_inf_eq_of_preimage_eq hU₁ hU₂))) :
    IsLimit c := by
  refine isLimitOfCompatibleOpensCover (V := family V₁ V₂) (U := vertexFamily U₁ U₂)
    (hV := fun a ↦ ?_) (hU := fun a j ↦ ?_) (hinf := fun a b ↦ ?_) (j₀ := j₀)
    (hcover := IsOpenCover.mk ?_) (hlim := fun a ↦ ?_)
  · cases a with
    | first => exact hV₁
    | second => exact hV₂
    | inter => exact preimage_inf_compatible hV₁ hV₂
  · cases a with
    | first => exact hU₁ j
    | second => exact hU₂ j
    | inter => exact preimage_inf_eq_of_preimage_eq hU₁ hU₂ j
  · cases a with
    | first =>
      cases b with
      | first => exact ⟨.first, fun j ↦ show V₁ j = V₁ j ⊓ V₁ j from (inf_idem (V₁ j)).symm⟩
      | second => exact ⟨.inter, fun _ ↦ rfl⟩
      | inter => exact ⟨.inter, fun j ↦
          show V₁ j ⊓ V₂ j = V₁ j ⊓ (V₁ j ⊓ V₂ j) by rw [← inf_assoc, inf_idem]⟩
    | second =>
      cases b with
      | first => exact ⟨.inter, fun j ↦
          show V₁ j ⊓ V₂ j = V₂ j ⊓ V₁ j from inf_comm (V₁ j) (V₂ j)⟩
      | second => exact ⟨.second, fun j ↦ show V₂ j = V₂ j ⊓ V₂ j from (inf_idem (V₂ j)).symm⟩
      | inter => exact ⟨.inter, fun j ↦
          show V₁ j ⊓ V₂ j = V₂ j ⊓ (V₁ j ⊓ V₂ j) by rw [inf_left_comm, inf_idem]⟩
    | inter =>
      cases b with
      | first => exact ⟨.inter, fun j ↦
          show V₁ j ⊓ V₂ j = (V₁ j ⊓ V₂ j) ⊓ V₁ j by rw [inf_right_comm, inf_idem]⟩
      | second => exact ⟨.inter, fun j ↦
          show V₁ j ⊓ V₂ j = (V₁ j ⊓ V₂ j) ⊓ V₂ j by rw [inf_assoc, inf_idem]⟩
      | inter => exact ⟨.inter, fun j ↦
          show V₁ j ⊓ V₂ j = (V₁ j ⊓ V₂ j) ⊓ (V₁ j ⊓ V₂ j) from (inf_idem (V₁ j ⊓ V₂ j)).symm⟩
  · refine top_unique ?_
    rw [← hcover]
    exact sup_le (le_iSup (fun a ↦ family V₁ V₂ a j₀) CompatibleOpensPairIndex.first)
      (le_iSup (fun a ↦ family V₁ V₂ a j₀) CompatibleOpensPairIndex.second)
  · cases a with
    | first => exact h₁
    | second => exact h₂
    | inter => exact h₃

/-! ### Finiteness of a glued stage -/

/-- The glueing of two quasi-compact schemes is quasi-compact over the terminal scheme.  With
`AlgebraicGeometry.Scheme.locallyOfFiniteType_terminal_from_gluePair` this gives both finite-type
requirements that the conclusion of Tag 07RN places on the stages of the new system, for a stage
obtained by glueing a model of the part already approximated to an affine scheme. -/
lemma Scheme.quasiCompact_terminal_from_gluePair {W X Y : Scheme.{u}} (f : W ⟶ X) (g : W ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] [CompactSpace X] [CompactSpace Y] :
    QuasiCompact (terminal.from (Scheme.gluePair f g)) :=
  (compactSpace_iff_quasiCompact _).mp (Scheme.compactSpace_gluePair f g)

end AlgebraicGeometry
