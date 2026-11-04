module

public import StacksFrontier.AlgebraicGeometry.OpenImmersionAlgebraBridges.InverseImageStructureIso
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.Adjunction

/-!
# The direct image of algebra sheaves along an open immersion is fully faithful

Let `j : U ⟶ X` be an open immersion of schemes. This file assembles the two bridges of
`PushforwardFullyFaithful.lean` and `InverseImageStructureIso.lean` into the statement the
algebra-level fibre product of
`StacksFrontier/AlgebraicGeometry/AlgebraOpenExtension/Basic.lean` is waiting for:

  `Stacks.AffineAlgebraEquivalence.algebraPushforward j` is fully faithful,

hence the counit of `algebraPullbackPushforwardAdjunction j` is an isomorphism and

  `(algebraPullback j).obj ((algebraPushforward j).obj G) ≅ G`

for every sheaf of `𝒪_U`-algebras `G`.

## Main results

* `Stacks.OpenImmersionAlgebraBridges.fullyFaithful_algebraPushforward`: `j_*` on algebra
  sheaves is fully faithful.
* `Stacks.OpenImmersionAlgebraBridges.algebraCounitIso`: restriction to `U` of the direct image
  of `G` is `G` again.
* `Stacks.OpenImmersionAlgebraBridges.isIso_algebraPullbackMap`: `algebraPullback j` *is* the
  plain inverse image — the canonical map `j⁻¹A ⟶ j⁻¹A ⊗_{j⁻¹𝒪_X} 𝒪_U` is an isomorphism.

## What the two bridges each contribute

`algebraPushforward j` is `Under.post (j_*) ⋙ Under.map ⟨j.c⟩` on `AlgebraSheaf X = Under
X.sheaf`. Faithfulness and the construction of a preimage both come from full faithfulness of
`j_*` on sheaves of commutative rings (bridge 1). What does *not* come for free is that the
preimage respects the `𝒪_U`-algebra structure: `Under.map` is faithful but not full, so the
structure-map identity has to be deduced, and deducing it is exactly where
`IsIso (inverseImageStructureMap j)` (bridge 2) is spent — only its `Epi` half is used.

The mechanism is `structureSheafHom_comp_map`: composing the comorphism `𝒪_X ⟶ j_*𝒪_U` with
`j_*γ` is the adjunct of `inverseImageStructureMap j ≫ γ`. So an equality of composites with
the comorphism is, after the hom-equivalence, an equality of composites with the structural map,
and that map can be cancelled. In other words the content of this file is:

  **`j_*` on algebra sheaves is fully faithful because `j_*` on rings is, and because
  `j⁻¹𝒪_X ⟶ 𝒪_U` is epi.**

`isIso_algebraPullbackMap` is separate and cheaper: `algebraPullback j` pushes out along
`inverseImageStructureMap j`, and a pushout along an isomorphism has its opposite leg an
isomorphism (`CategoryTheory.Limits.pushout_inl_iso_of_right_iso`). This is the sentence
`AlgebraOpenExtension/Basic.lean` records as "the identification `j⁻¹𝒪_X ≅ 𝒪_U` that makes
`algebraPullback j` the plain inverse image rather than a pushout along it".

## No stacks attribute

Nothing here carries a `@[stacks]` attribute and none could. All three assertions of Tag 01PE
are about `AlgebraicGeometry.Scheme.Modules`, i.e. sheaves of modules; there is no algebra-level
assertion under that tag. This is infrastructure for Tags 05JT and 0817.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

universe u

namespace Stacks.OpenImmersionAlgebraBridges

variable {U X : Scheme.{u}} (j : U ⟶ X)

/-! ### Cancelling the comorphism against the structural map -/

/-- Composing the comorphism `𝒪_X ⟶ j_*𝒪_U` with the direct image of `γ : 𝒪_U ⟶ B` gives the
adjunct of `inverseImageStructureMap j ≫ γ`. True for every morphism of schemes; it is the
naturality statement behind
`Stacks.AffineAlgebraEquivalence.unit_comp_map_inverseImageStructureMap` read as a
hom-equivalence. -/
public theorem structureSheafHom_comp_map {B : TopCat.Sheaf CommRingCat.{u} U}
    (γ : U.sheaf ⟶ B) :
    structureSheafHom j ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} j.base).map γ =
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} j.base).homEquiv X.sheaf B
        (AlgebraicGeometry.inverseImageStructureMap j ≫ γ) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    unit_comp_map_inverseImageStructureMap]
  rfl

/-- If the structural map `j⁻¹𝒪_X ⟶ 𝒪_U` is epi, then two maps out of `𝒪_U` whose direct
images agree after composing with the comorphism are equal. -/
public theorem cancel_structureSheafHom {B : TopCat.Sheaf CommRingCat.{u} U} (γ δ : U.sheaf ⟶ B)
    [Epi (AlgebraicGeometry.inverseImageStructureMap j)]
    (h : structureSheafHom j ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} j.base).map γ =
      structureSheafHom j ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} j.base).map δ) :
    γ = δ := by
  rw [structureSheafHom_comp_map, structureSheafHom_comp_map] at h
  exact (cancel_epi _).mp
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} j.base).homEquiv
      X.sheaf B).injective h)

/-! ### Full faithfulness of the direct image of algebra sheaves -/

/-- The underlying map of sheaves of rings of a morphism between direct images of algebra
sheaves, at the spelling in which full faithfulness of `j_*` is stated. The two spellings are
definitionally equal; naming this avoids an application type mismatch at instance
transparency. -/
public def algebraPushforwardRight {A B : AlgebraSheaf U}
    (f : (algebraPushforward j).obj A ⟶ (algebraPushforward j).obj B) :
    (TopCat.Sheaf.pushforward CommRingCat.{u} j.base).obj A.right ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} j.base).obj B.right := f.right

/-- The structure-map identity carried by a morphism between direct images of algebra sheaves,
with the structure map of `(algebraPushforward j).obj A` written out as the comorphism followed
by the direct image of the structure map of `A`. -/
public theorem structureSheafHom_comp_right {A B : AlgebraSheaf U}
    (f : (algebraPushforward j).obj A ⟶ (algebraPushforward j).obj B) :
    structureSheafHom j ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} j.base).map A.hom ≫
        algebraPushforwardRight j f =
      structureSheafHom j ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} j.base).map B.hom :=
  (Category.assoc _ _ _).symm.trans (Under.w f)

variable [H : IsOpenImmersion j]

/-- **The direct image of algebra sheaves along an open immersion is fully faithful.** The
preimage of `f` is the preimage of its underlying map of sheaves of rings; that it respects the
`𝒪_U`-algebra structure is `cancel_structureSheafHom`, i.e. bridge 2. -/
public def fullyFaithful_algebraPushforward : (algebraPushforward j).FullyFaithful where
  preimage {A B} f :=
    Under.homMk
      ((fullyFaithful_pushforward_base j).preimage (algebraPushforwardRight j f)) (by
      refine cancel_structureSheafHom j _ _ ?_
      have h1 : (TopCat.Sheaf.pushforward CommRingCat.{u} j.base).map (A.hom ≫
          (fullyFaithful_pushforward_base j).preimage (algebraPushforwardRight j f)) =
          (TopCat.Sheaf.pushforward CommRingCat.{u} j.base).map A.hom ≫
            algebraPushforwardRight j f := by
        rw [Functor.map_comp, Functor.FullyFaithful.map_preimage]
      exact (congrArg (fun k ↦ structureSheafHom j ≫ k) h1).trans
        (structureSheafHom_comp_right j f))
  map_preimage {A B} f := by
    ext
    exact (fullyFaithful_pushforward_base j).map_preimage (algebraPushforwardRight j f)
  preimage_map {A B} f := by
    ext
    exact (fullyFaithful_pushforward_base j).preimage_map f.right

/-- `j_*` on algebra sheaves is full. -/
public instance full_algebraPushforward : (algebraPushforward j).Full :=
  (fullyFaithful_algebraPushforward j).full

/-- `j_*` on algebra sheaves is faithful. -/
public instance faithful_algebraPushforward : (algebraPushforward j).Faithful :=
  (fullyFaithful_algebraPushforward j).faithful

/-- The counit of `algebraPullback j ⊣ algebraPushforward j` is an isomorphism, the right
adjoint being fully faithful. -/
public instance isIso_counit_algebraPullbackPushforward :
    IsIso (algebraPullbackPushforwardAdjunction j).counit :=
  inferInstance

/-- **Restriction to `U` of the direct image of an algebra sheaf on `U` is that sheaf again:**
`j^*j_*G ≅ G`. This is the input the second assertion of the algebra-level extension
`A ×_{j_*(A|_U)} j_*G` needs. -/
public def algebraCounitIso (G : AlgebraSheaf U) :
    (algebraPullback j).obj ((algebraPushforward j).obj G) ≅ G :=
  asIso ((algebraPullbackPushforwardAdjunction j).counit.app G)

/-! ### Algebra pullback along an open immersion is the plain inverse image -/

/-- The canonical map `j⁻¹A ⟶ j⁻¹A ⊗_{j⁻¹𝒪_X} 𝒪_U` is an isomorphism at every algebra sheaf:
the extension of scalars is along the isomorphism `j⁻¹𝒪_X ≅ 𝒪_U`. -/
public instance isIso_algebraPullbackMap_app (A : AlgebraSheaf X) :
    IsIso ((algebraPullbackMap j).app A) := by
  change IsIso (Limits.pushout.inl
    ((TopCat.Sheaf.pullback CommRingCat.{u} j.base).map A.hom)
    (AlgebraicGeometry.inverseImageStructureMap j))
  infer_instance

/-- **`algebraPullback j` is the plain inverse image.** The natural transformation exhibiting
algebra pullback as extension of scalars from `j⁻¹𝒪_X` to `𝒪_U` is an isomorphism along an open
immersion. -/
public instance isIso_algebraPullbackMap : IsIso (algebraPullbackMap j) :=
  NatIso.isIso_of_isIso_app _

end Stacks.OpenImmersionAlgebraBridges
