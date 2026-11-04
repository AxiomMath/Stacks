module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.CoherentReflexive
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.HartogsExtension.Basic

/-!
# Restriction and direct image between full subcategories of modules on an open subscheme

Let `U` be an open subscheme of a scheme `X`.  Pullback along `U.ι` is left adjoint to direct
image, and the counit of that adjunction is *always* an isomorphism, because pullback along an
open immersion agrees with restriction and restriction is a retraction of direct image.  So if a
property `P` of `𝒪_X`-modules and a property `Q` of `𝒪_U`-modules are preserved by pullback and
by direct image respectively, the only thing that can fail is the unit: restriction and direct
image are inverse equivalences between the two full subcategories exactly when the canonical map
`F ⟶ j_*(F|_U)` is an isomorphism for every `F` satisfying `P`.

This is the categorical content of [Stacks, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ),
separated from its mathematical content.  For coherent reflexive modules over an integral locally
Noetherian `X` the unit is handled by Tag 0E9I, which is proved unconditionally, once the
depth of the *stalks of the module* along the complement of `U` is known; and that is Tag 0EBI
part (1).

## Main results

* `isIso_pullbackPushforwardAdjunction_counit`: the counit of the pullback--direct-image
  adjunction along an open immersion of schemes is an isomorphism.  Unconditional.
* `openRestrictEquivalenceOfProperties`: pullback and direct image are inverse equivalences
  between the full subcategories cut out by `P` and `Q`, given that they preserve the two
  properties and that the unit is invertible on `P`.
* `reflexiveCoherentEquivalenceOfPreservation`: the statement of Tag 0EBJ, from three named
  hypotheses.

## Implementation notes

The lift of the adjunction to the two full subcategories is Mathlib's
`CategoryTheory.Adjunction.restrictFullyFaithful`, whose two `simp` lemmas
`Adjunction.map_restrictFullyFaithful_unit_app` and
`Adjunction.map_restrictFullyFaithful_counit_app` express the lifted unit and counit through
`ObjectProperty.ι`, so invertibility transports both ways along the fully faithful inclusion.
No adjunction-lifting construction is introduced here: a `private` re-derivation of the Mathlib
lemma already exists in the tree at
`StacksFrontier/RingTheory/Dualizing/LocalCohomology.lean`, and the Mathlib statement is the one to
use.

`reflexiveCoherentEquivalenceOfPreservation` **carries hypotheses and therefore does not carry
the tag of Tag 0EBJ**.  Its three hypotheses are exactly, and only, the three statements the
source's proof needs that the library does not have:

* `hpullback` is Tag 0EBF clause (2), that pullback preserves reflexivity (clause (1), coherence,
  is `AlgebraicGeometry.isCoherent_pullback` and is proved, so it is *not* a hypothesis here);
* `hpushforward` is the extension step, the direct image across a depth-two complement of a
  coherent reflexive module being again coherent and reflexive;
* `hdepthStalk` is Tag 0EBI part (1), that a coherent reflexive module has stalk depth at least
  two wherever the local ring does.

## References

* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
* [Stacks Project, Tag 0EBI](https://stacks.math.columbia.edu/tag/0EBI)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

/-! ### The counit along an open immersion -/

/-- **The counit of the pullback--direct-image adjunction along an open immersion of schemes is
an isomorphism.**  Pullback along `U.ι` is isomorphic to restriction, and
`Scheme.Modules.restrictFunctorAdjCounitIso` says that restricting a direct image recovers the
module, so `j^* ∘ j_*` is isomorphic to the identity; a right adjoint whose composite with its
left adjoint is abstractly isomorphic to the identity has invertible counit.

No hypothesis on `U` or on `X` is used. -/
public theorem isIso_pullbackPushforwardAdjunction_counit (X : Scheme.{u}) (U : X.Opens) :
    IsIso (Scheme.Modules.pullbackPushforwardAdjunction U.ι).counit :=
  have j : Scheme.Modules.pushforward U.ι ⋙ Scheme.Modules.pullback U.ι ≅
      𝟭 U.toScheme.Modules :=
    (Functor.isoWhiskerLeft (Scheme.Modules.pushforward U.ι)
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm).trans
      (Scheme.Modules.restrictFunctorAdjCounitIso U.ι)
  (Scheme.Modules.pullbackPushforwardAdjunction U.ι).isIso_counit_of_iso j

/-! ### The equivalence between two full subcategories -/

/-- **Pullback and direct image along an open immersion are inverse equivalences between full
subcategories, as soon as they preserve the two properties and the unit is invertible.**

The equivalence is accompanied by the two natural isomorphisms identifying its functor and its
inverse, after inclusion into all modules, with pullback and direct image; so the statement
records the specified functors and not merely an abstract equivalence. -/
public noncomputable def openRestrictEquivalenceOfProperties {X : Scheme.{u}} (U : X.Opens)
    (P : ObjectProperty X.Modules) (Q : ObjectProperty U.toScheme.Modules)
    (hL : ∀ F : P.FullSubcategory, Q ((Scheme.Modules.pullback U.ι).obj F.obj))
    (hR : ∀ G : Q.FullSubcategory, P ((Scheme.Modules.pushforward U.ι).obj G.obj))
    (hunit : ∀ F : P.FullSubcategory,
      IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F.obj)) :
    Σ e : P.FullSubcategory ≌ Q.FullSubcategory,
      (e.functor ⋙ ObjectProperty.ι Q ≅
        ObjectProperty.ι P ⋙ Scheme.Modules.pullback U.ι) ×
      (e.inverse ⋙ ObjectProperty.ι P ≅
        ObjectProperty.ι Q ⋙ Scheme.Modules.pushforward U.ι) := by
  set adj := Scheme.Modules.pullbackPushforwardAdjunction U.ι with hadj
  set L := ObjectProperty.lift Q (ObjectProperty.ι P ⋙ Scheme.Modules.pullback U.ι) hL
    with hLdef
  set R := ObjectProperty.lift P (ObjectProperty.ι Q ⋙ Scheme.Modules.pushforward U.ι) hR
    with hRdef
  have c1 : ObjectProperty.ι P ⋙ Scheme.Modules.pullback U.ι ≅ L ⋙ ObjectProperty.ι Q :=
    (Q.liftCompιIso (ObjectProperty.ι P ⋙ Scheme.Modules.pullback U.ι) hL).symm
  have c2 : ObjectProperty.ι Q ⋙ Scheme.Modules.pushforward U.ι ≅ R ⋙ ObjectProperty.ι P :=
    (P.liftCompιIso (ObjectProperty.ι Q ⋙ Scheme.Modules.pushforward U.ι) hR).symm
  set adjP := adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι c1 c2 with hadjP
  have hrP : (ObjectProperty.ι P).ReflectsIsomorphisms := P.fullyFaithfulι.reflectsIsomorphisms
  have hrQ : (ObjectProperty.ι Q).ReflectsIsomorphisms := Q.fullyFaithfulι.reflectsIsomorphisms
  have hu : ∀ F : P.FullSubcategory, IsIso (adjP.unit.app F) := by
    intro F
    have h := Adjunction.map_restrictFullyFaithful_unit_app adj
      P.fullyFaithfulι Q.fullyFaithfulι c1 c2 F
    have : IsIso (adj.unit.app ((ObjectProperty.ι P).obj F)) := hunit F
    have h1 : IsIso ((Scheme.Modules.pushforward U.ι).map (c1.hom.app F)) := inferInstance
    have h2 : IsIso (c2.hom.app (L.obj F)) := inferInstance
    have : IsIso ((ObjectProperty.ι P).map (adjP.unit.app F)) := by
      rw [hadjP, h]
      exact IsIso.comp_isIso
    exact isIso_of_reflects_iso _ (ObjectProperty.ι P)
  have hc : ∀ G : Q.FullSubcategory, IsIso (adjP.counit.app G) := by
    intro G
    have h := Adjunction.map_restrictFullyFaithful_counit_app adj
      P.fullyFaithfulι Q.fullyFaithfulι c1 c2 G
    have : IsIso (adj.counit.app ((ObjectProperty.ι Q).obj G)) := by
      have := isIso_pullbackPushforwardAdjunction_counit X U
      infer_instance
    have h1 : IsIso (c1.inv.app (R.obj G)) := inferInstance
    have h2 : IsIso ((Scheme.Modules.pullback U.ι).map (c2.inv.app G)) := inferInstance
    have : IsIso ((ObjectProperty.ι Q).map (adjP.counit.app G)) := by
      rw [hadjP, h]
      exact IsIso.comp_isIso
    exact isIso_of_reflects_iso _ (ObjectProperty.ι Q)
  exact ⟨adjP.toEquivalence, c1.symm, c2.symm⟩

/-! ### Tag 0EBJ from three named hypotheses -/

/-- **The statement of Stacks, Tag 0EBJ, from three named hypotheses.**  On an integral locally
Noetherian scheme, restriction to an open subscheme whose complement has structure-sheaf depth at
least two is an equivalence on coherent reflexive modules, with direct image as its inverse, and
both identifications are natural.

The tag is **withheld**: the three hypotheses are the content the library still lacks, namely Tag
0EBF clause (2), the direct-image extension step, and Tag 0EBI part (1).  Coherence of a pullback
(Tag 0EBF clause (1)), invertibility of the unit (Tag 0E9I) and invertibility of the counit are
all discharged here. -/
public noncomputable def reflexiveCoherentEquivalenceOfPreservation (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (hpullback : ∀ F : X.Modules, F.IsCoherent → IsReflexive F →
      IsReflexive ((Scheme.Modules.pullback U.ι).obj F))
    (hpushforward : ∀ G : U.toScheme.Modules, G.IsCoherent → IsReflexive G →
      ((Scheme.Modules.pushforward U.ι).obj G).IsCoherent ∧
        IsReflexive ((Scheme.Modules.pushforward U.ι).obj G))
    (hdepthStalk : ∀ F : X.Modules, F.IsCoherent → IsReflexive F → ∀ x : X,
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) →
        letI : Module (X.presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) F.val x
        (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (↑(TopCat.Presheaf.stalk F.val.presheaf x))) :
    Σ e : ReflexiveCoherentModules X ≌ ReflexiveCoherentModules U.toScheme,
      (e.functor ⋙ ObjectProperty.ι
          (fun F : U.toScheme.Modules =>
            F.IsCoherent ∧ IsReflexive F) ≅
        ObjectProperty.ι
          (fun F : X.Modules => F.IsCoherent ∧ IsReflexive F) ⋙
          Scheme.Modules.pullback U.ι) ×
      (e.inverse ⋙ ObjectProperty.ι
          (fun F : X.Modules => F.IsCoherent ∧ IsReflexive F) ≅
        ObjectProperty.ι
          (fun F : U.toScheme.Modules =>
            F.IsCoherent ∧ IsReflexive F) ⋙
          Scheme.Modules.pushforward U.ι) := by
  have hLN : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  refine openRestrictEquivalenceOfProperties U
    (fun F : X.Modules => F.IsCoherent ∧ IsReflexive F)
    (fun F : U.toScheme.Modules => F.IsCoherent ∧ IsReflexive F) ?_ ?_ ?_
  · intro F
    have hcoh : F.obj.IsCoherent := F.property.1
    exact ⟨AlgebraicGeometry.isCoherent_pullback U.ι F.obj,
      hpullback F.obj F.property.1 F.property.2⟩
  · intro G
    exact hpushforward G.obj G.property.1 G.property.2
  · intro F
    have hcoh : F.obj.IsCoherent := F.property.1
    exact AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two X F.obj U
      (fun x hx => hdepthStalk F.obj F.property.1 F.property.2 x (hdepth x hx))

end Stacks.AlgebraicGeometry.ReflexiveModules

end
