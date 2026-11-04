module

public import Mathlib.CategoryTheory.Limits.Final
public import StacksCore.CategoryTheory.Category.Preorder
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Preorder vs. partial order: equivalence on (inverse) systems

For a preordered index `I`, let `Ī = Antisymmetrization I (· ≤ ·)` be its partial order quotient.
The quotient functor `I ⥤ Ī` is an equivalence of categories, so replacing `I` by `Ī` loses no
information about (inverse) systems indexed by `I` or their (co)limits.

Mathlib already provides the quotient itself (`Antisymmetrization`, `toAntisymmetrization`,
`instPartialOrderAntisymmetrization`, `toAntisymmetrization_le_toAntisymmetrization_iff`), and
the quotient functor is an equivalence of categories by
`StacksCore/CategoryTheory/Category/Preorder.lean`. This file records the residual content of
Stacks Tag 0CN1: directedness descends, the pullback functor on (inverse) systems is an
equivalence, and the equivalence is compatible with (co)limits.

## Main definitions

* `antisymmetrizationEquivalence`: The quotient functor `I ⥤ Ī` as an equivalence of categories.
* `pullbackSystemFunctor`: The functor from systems over `Ī` to systems over `I`, `N ↦ π ⋙ N`.
* `systemEquivalence`: The equivalence between systems over `Ī` and systems over `I`.
* `inverseSystemEquivalence`: The equivalence between inverse systems over `Ī` and over `I`.
* `colimitPullbackSystemIso`: The colimit of the pullback of `N` is isomorphic to that of `N`.
* `limitInverseSystemIso`: The limit of the pullback of `N` is isomorphic to that of `N`.

## Main results

* `isDirected_antisymmetrization`: If `I` is directed, so is `Ī`.
* `hasColimit_iff_hasColimit_of_systemEquivalence`: A system `N` over `Ī` has a colimit if and
  only if its pullback to `I` does.
* `hasLimit_iff_hasLimit_of_inverseSystemEquivalence`: An inverse system `N` over `Ī` has a limit
  if and only if its pullback to `I` does.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable (I : Type*) [Preorder I]

/-- If `I` is directed, so is its antisymmetrization. -/
@[stacks 0CN1 "If `I` is directed, so is its partial order quotient."]
theorem isDirected_antisymmetrization [IsDirected I (· ≤ ·)] :
    IsDirected (Antisymmetrization I (· ≤ ·)) (· ≤ ·) := by
  refine ⟨fun x y => ?_⟩
  induction x using Quotient.inductionOn with | _ a =>
  induction y using Quotient.inductionOn with | _ b =>
  obtain ⟨c, hac, hbc⟩ := IsDirected.directed (r := (· ≤ ·)) a b
  refine ⟨toAntisymmetrization (· ≤ ·) c, ?_, ?_⟩
  · exact toAntisymmetrization_le_toAntisymmetrization_iff.mpr hac
  · exact toAntisymmetrization_le_toAntisymmetrization_iff.mpr hbc

/-- The quotient map `π : I ⥤ Ī` onto the antisymmetrization, as an equivalence of categories. -/
noncomputable abbrev antisymmetrizationEquivalence : I ≌ Antisymmetrization I (· ≤ ·) :=
  (toAntisymmetrization_mono (α := I)).functor.asEquivalence

variable (C : Type*) [Category C]

/-- The pullback of systems over the antisymmetrization `Ī = Antisymmetrization I (· ≤ ·)` to
systems over `I`, along the quotient functor induced by `toAntisymmetrization`. -/
@[stacks 0CN1 "The functor from systems over `Ī` to systems over `I`, `N ↦ (N_{π(i)})`."]
def pullbackSystemFunctor :
    (Antisymmetrization I (· ≤ ·) ⥤ C) ⥤ (I ⥤ C) :=
  (Functor.whiskeringLeft _ _ C).obj (toAntisymmetrization_mono (α := I)).functor

/-- The pullback of a system `N` over `Ī` is the composite of the quotient functor with `N`. -/
@[simp]
lemma pullbackSystemFunctor_obj (N : Antisymmetrization I (· ≤ ·) ⥤ C) :
    (pullbackSystemFunctor I C).obj N = (toAntisymmetrization_mono (α := I)).functor ⋙ N :=
  rfl

/-- The equivalence between systems over the antisymmetrization of `I` and systems over `I`:
every system over `I` descends, uniquely up to canonical isomorphism, to a system over the
antisymmetrization. -/
@[stacks 0CN1 "The functor from systems over `Ī` to systems over `I` is an equivalence."]
noncomputable def systemEquivalence :
    (Antisymmetrization I (· ≤ ·) ⥤ C) ≌ (I ⥤ C) :=
  (antisymmetrizationEquivalence I).symm.congrLeft

/-- The functor of `systemEquivalence` is `pullbackSystemFunctor`. -/
lemma systemEquivalence_functor :
    (systemEquivalence I C).functor = pullbackSystemFunctor I C :=
  rfl

/-- The equivalence between inverse systems over the antisymmetrization of `I` and inverse
systems over `I`. -/
@[stacks 0CN1 "The analogous equivalence for inverse systems."]
noncomputable def inverseSystemEquivalence :
    ((Antisymmetrization I (· ≤ ·))ᵒᵖ ⥤ C) ≌ (Iᵒᵖ ⥤ C) :=
  (antisymmetrizationEquivalence I).symm.op.congrLeft

/-- The functor of `inverseSystemEquivalence` sends an inverse system `N` over `Ī` to the
composite of the opposite of the quotient functor with `N`. -/
@[simp]
lemma inverseSystemEquivalence_functor_obj (N : (Antisymmetrization I (· ≤ ·))ᵒᵖ ⥤ C) :
    (inverseSystemEquivalence I C).functor.obj N =
      (toAntisymmetrization_mono (α := I)).functor.op ⋙ N :=
  rfl

/-- A system `N` over `Ī` has a colimit if and only if its pullback to `I` has a colimit. -/
@[stacks 0CN1 "Compatibility of the equivalence with colimits of systems."]
theorem hasColimit_iff_hasColimit_of_systemEquivalence
    (N : Antisymmetrization I (· ≤ ·) ⥤ C) :
    HasColimit N ↔ HasColimit ((pullbackSystemFunctor I C).obj N) := by
  rw [pullbackSystemFunctor_obj, Functor.Final.hasColimit_comp_iff]

/-- The colimit of the pullback of a system `N` over `Ī` to `I` is the colimit of `N`. -/
@[stacks 0CN1 "The colimits of related systems agree."]
noncomputable def colimitPullbackSystemIso (N : Antisymmetrization I (· ≤ ·) ⥤ C)
    [HasColimit N] :
    colimit ((toAntisymmetrization_mono (α := I)).functor ⋙ N) ≅ colimit N :=
  Functor.Final.colimitIso (toAntisymmetrization_mono (α := I)).functor N

/-- An inverse system `N` over `Ī` has a limit if and only if its pullback to `I` has a limit. -/
@[stacks 0CN1 "Compatibility of the equivalence with limits of inverse systems.",
  sga "4 V 8.1.5" "special case"]
theorem hasLimit_iff_hasLimit_of_inverseSystemEquivalence
    (N : (Antisymmetrization I (· ≤ ·))ᵒᵖ ⥤ C) :
    HasLimit N ↔ HasLimit ((inverseSystemEquivalence I C).functor.obj N) := by
  rw [inverseSystemEquivalence_functor_obj, Functor.Initial.hasLimit_comp_iff]

/-- The limit of the pullback of an inverse system `N` over `Ī` to `I` is the limit of `N`. -/
@[stacks 0CN1 "The limits of related inverse systems agree."]
noncomputable def limitInverseSystemIso (N : (Antisymmetrization I (· ≤ ·))ᵒᵖ ⥤ C)
    [HasLimit N] :
    limit ((toAntisymmetrization_mono (α := I)).functor.op ⋙ N) ≅ limit N :=
  Functor.Initial.limitIso (toAntisymmetrization_mono (α := I)).functor.op N

end CategoryTheory
