module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsRelativized

/-!
# The glueing of morphisms at an open, from the glueing of morphisms of global objects

Let `(X, 𝒪_X)` be a ringed space and let `(ℬ, K_U, ρ^U_V)` be a system of locally given derived
objects on it, as in Situation 0D67.  The sheaf condition of [Stacks, Tag 0D66] part (2), as this
development carries it, speaks of objects of the derived category of the **whole** of `X`
restricted to opens; the predicate `Stacks.DerivedGlueing.HasGluingForHomsAt` that Tags 0D68 and
0D69 consume quantifies over objects `K L : OpenDerivedCategory X O` given **only over `O`**.

`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsRelativized` removes the
half of that mismatch which concerns the objects: every object over `O` is, up to isomorphism,
the restriction from `⊤` of an object over `⊤`,
`Stacks.DerivedGlueing.exists_restriction_top_iso`.  This file removes the other half, and so
completes the relativization.

Two steps.

First, the glueing condition at `O` for a **fixed** pair of objects,
`Stacks.DerivedGlueing.GluesHomsAt`, depends only on their isomorphism classes,
`Stacks.DerivedGlueing.GluesHomsAt.of_iso`.  Only the functoriality of the restriction map
`Stacks.DerivedGlueing.restrictHomBelow` is involved.  With the object half this already gives
`Stacks.DerivedGlueing.hasGluingForHomsAt_of_forall_restriction_top`: the condition at `O` need
only be checked at objects that are restrictions from `⊤`.

Second, for an object `K'` over `⊤` the restrictions to `W ≤ O` of `K'|_O` are identified with
the restrictions of `K'` itself, by
`Stacks.DerivedGlueing.restrictionIsoOfTopIso`, and that identification **carries
`restrictHomBelow` across**, `Stacks.DerivedGlueing.restrictHomBelow_restrictionIsoOfTopIso`.
This is the coherence of the identification with the comparison of restriction in one and in two
steps, `Stacks.DerivedGlueing.LocallyGiven.restrictionComp` — the field of which
`restrictHomBelow` is the conjugation.  Its proof is the associativity of that comparison,
`Stacks.DerivedGlueing.LocallyGiven.restrictionComp_pentagon`, followed by the comparison's own
naturality; no passage through the localization is needed, because the associativity has already
been proved there.

Together these give `Stacks.DerivedGlueing.hasGluingForHomsAt_of_global`: the glueing condition
at `O` follows from the glueing condition at `O` *for global objects*, which is
`Stacks.DerivedGlueing.HasGluingForHomsAtOfGlobal` and is stated entirely in terms of
restrictions from `⊤`.  That is the shape in which the development carries the sheaf condition of
[Stacks, Tag 0D66] part (2).

## Main definitions

* `Stacks.DerivedGlueing.GluesHomsAt`: the glueing condition at an open, for a fixed pair of
  objects over it.
* `Stacks.DerivedGlueing.restrictionIsoOfTopIso`: given an identification of an object over `O`
  with the restriction from `⊤` of an object over `⊤`, the induced identification of their
  restrictions to an open below `O`.
* `Stacks.DerivedGlueing.HasGluingForHomsAtOfGlobal`: the glueing condition at an open, for
  objects given over the whole space.

## Main results

* `Stacks.DerivedGlueing.restrictionComp_restrictionIsoOfTopIso`: the identification commutes
  with the comparison of restriction in one and in two steps.
* `Stacks.DerivedGlueing.restrictHomBelow_restrictionIsoOfTopIso`: the identification carries the
  restriction map of the rule `W ↦ Hom(K|_W, L|_W)` across.
* `Stacks.DerivedGlueing.GluesHomsAt.of_iso`: the glueing condition at a fixed pair of objects
  depends only on their isomorphism classes.
* `Stacks.DerivedGlueing.hasGluingForHomsAt_of_forall_restriction_top` and
  `Stacks.DerivedGlueing.hasGluingForHomsAt_of_global`: the relativization.

Tags covered: none.  Every declaration here is a step of a proof, not a clause of a tag
statement.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D69](https://stacks.math.columbia.edu/tag/0D69)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### Restricting a morphism conjugated by restrictions -/

/-- **The restriction map of `W ↦ Hom(K|_W, L|_W)` is compatible with composing on either side
with the restriction of a morphism over `O`.** Both legs are restrictions of morphisms over `O`,
so this is `Stacks.DerivedGlueing.restrictHomBelow_comp` followed by
`Stacks.DerivedGlueing.restrictHomBelow_map` on each of them. -/
theorem restrictHomBelow_map_comp_map (S : LocallyGiven X) {O : Opens X.carrier}
    {K₁ K₂ L₁ L₂ : OpenDerivedCategory X O} (a : K₁ ⟶ K₂) (b : L₂ ⟶ L₁)
    {T W : Opens X.carrier} (hTW : T ≤ W) (hWO : W ≤ O)
    (φ : (S.restriction W O hWO).obj K₂ ⟶ (S.restriction W O hWO).obj L₂) :
    restrictHomBelow S hTW hWO
        ((S.restriction W O hWO).map a ≫ φ ≫ (S.restriction W O hWO).map b) =
      (S.restriction T O (hTW.trans hWO)).map a ≫ restrictHomBelow S hTW hWO φ ≫
        (S.restriction T O (hTW.trans hWO)).map b := by
  rw [restrictHomBelow_comp, restrictHomBelow_comp, restrictHomBelow_map, restrictHomBelow_map]

/-! ### The identification of the restrictions of a restriction from the whole space -/

/-- **The restrictions below `O` of an object over `O` identified with the restriction from `⊤`
of an object over `⊤`.** If `e` identifies `K'|_O` with `K`, then for `W ≤ O` the comparison of
restriction from `⊤` in one and in two steps identifies `K'|_W` with `(K'|_O)|_W`, and `e`
identifies the latter with `K|_W`. -/
def restrictionIsoOfTopIso (S : LocallyGiven X) {O : Opens X.carrier}
    {K' : OpenDerivedCategory X ⊤} {K : OpenDerivedCategory X O}
    (e : (S.restriction O ⊤ le_top).obj K' ≅ K) (W : Opens X.carrier) (hWO : W ≤ O) :
    (S.restriction W ⊤ le_top).obj K' ≅ (S.restriction W O hWO).obj K :=
  (S.restrictionComp W O ⊤ hWO le_top).app K' ≪≫ (S.restriction W O hWO).mapIso e

/-- **The identification commutes with the comparison of restriction in one and in two steps.**
This is the coherence half of the relativization of the glueing condition for morphisms: the
comparison `Stacks.DerivedGlueing.LocallyGiven.restrictionComp` from `⊤` through `W`, followed by
the identification at `W`, is the identification at `T` followed by the comparison from `O`
through `W`.

The proof is the associativity of the comparisons,
`Stacks.DerivedGlueing.LocallyGiven.restrictionComp_pentagon`, for the chain `T ⊆ W ⊆ O ⊆ ⊤`,
followed by the naturality of the comparison from `O` through `W` at `e`. -/
theorem restrictionComp_restrictionIsoOfTopIso (S : LocallyGiven X) {O : Opens X.carrier}
    {K' : OpenDerivedCategory X ⊤} {K : OpenDerivedCategory X O}
    (e : (S.restriction O ⊤ le_top).obj K' ≅ K)
    {T W : Opens X.carrier} (hTW : T ≤ W) (hWO : W ≤ O) :
    (S.restrictionComp T W ⊤ hTW le_top).hom.app K' ≫
        (S.restriction T W hTW).map (restrictionIsoOfTopIso S e W hWO).hom =
      (restrictionIsoOfTopIso S e T (hTW.trans hWO)).hom ≫
        (S.restrictionComp T W O hTW hWO).hom.app K := by
  have hp := S.restrictionComp_pentagon T W O ⊤ hTW hWO le_top K'
  have hn := (S.restrictionComp T W O hTW hWO).hom.naturality e.hom
  simp only [Functor.comp_map] at hn
  simp only [restrictionIsoOfTopIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((S.restrictionComp T W ⊤ hTW le_top).hom.app K')
      ((S.restriction T W hTW).map ((S.restrictionComp W O ⊤ hWO le_top).hom.app K'))
      ((S.restriction T W hTW).map ((S.restriction W O hWO).map e.hom)), ← hp,
    Category.assoc, ← hn]

/-- `Stacks.DerivedGlueing.restrictionComp_restrictionIsoOfTopIso` read as an equality of
isomorphisms, so that the inverse square is available too. -/
theorem restrictionComp_restrictionIsoOfTopIso_iso (S : LocallyGiven X) {O : Opens X.carrier}
    {K' : OpenDerivedCategory X ⊤} {K : OpenDerivedCategory X O}
    (e : (S.restriction O ⊤ le_top).obj K' ≅ K)
    {T W : Opens X.carrier} (hTW : T ≤ W) (hWO : W ≤ O) :
    (S.restrictionComp T W ⊤ hTW le_top).app K' ≪≫
        (S.restriction T W hTW).mapIso (restrictionIsoOfTopIso S e W hWO) =
      restrictionIsoOfTopIso S e T (hTW.trans hWO) ≪≫
        (S.restrictionComp T W O hTW hWO).app K :=
  Iso.ext (restrictionComp_restrictionIsoOfTopIso S e hTW hWO)

/-- `Stacks.DerivedGlueing.restrictionComp_restrictionIsoOfTopIso` in the other direction. -/
theorem restrictionComp_restrictionIsoOfTopIso_inv (S : LocallyGiven X) {O : Opens X.carrier}
    {K' : OpenDerivedCategory X ⊤} {K : OpenDerivedCategory X O}
    (e : (S.restriction O ⊤ le_top).obj K' ≅ K)
    {T W : Opens X.carrier} (hTW : T ≤ W) (hWO : W ≤ O) :
    (S.restriction T W hTW).map (restrictionIsoOfTopIso S e W hWO).inv ≫
        (S.restrictionComp T W ⊤ hTW le_top).inv.app K' =
      (S.restrictionComp T W O hTW hWO).inv.app K ≫
        (restrictionIsoOfTopIso S e T (hTW.trans hWO)).inv := by
  simpa using congrArg Iso.inv (restrictionComp_restrictionIsoOfTopIso_iso S e hTW hWO)

/-- **The identification carries the restriction map of `W ↦ Hom(K|_W, L|_W)` across.** A
morphism between the restrictions to `W` of two objects over `O`, read through the
identifications as a morphism between the restrictions to `W` of the two objects over `⊤`,
restricts to `T` to the reading of its restriction.

This is `Stacks.DerivedGlueing.restrictionComp_restrictionIsoOfTopIso` for the source and its
inverse form for the target, since `Stacks.DerivedGlueing.restrictHomBelow` is by definition the
conjugation by the comparison of restriction in one and in two steps. -/
theorem restrictHomBelow_restrictionIsoOfTopIso (S : LocallyGiven X) {O : Opens X.carrier}
    {K' L' : OpenDerivedCategory X ⊤} {K L : OpenDerivedCategory X O}
    (eK : (S.restriction O ⊤ le_top).obj K' ≅ K)
    (eL : (S.restriction O ⊤ le_top).obj L' ≅ L)
    {T W : Opens X.carrier} (hTW : T ≤ W) (hWO : W ≤ O)
    (φ : (S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L) :
    restrictHomBelow S hTW le_top
        ((restrictionIsoOfTopIso S eK W hWO).hom ≫ φ ≫
          (restrictionIsoOfTopIso S eL W hWO).inv) =
      (restrictionIsoOfTopIso S eK T (hTW.trans hWO)).hom ≫ restrictHomBelow S hTW hWO φ ≫
        (restrictionIsoOfTopIso S eL T (hTW.trans hWO)).inv := by
  have htail := restrictionComp_restrictionIsoOfTopIso_inv S eL hTW hWO
  simp only [restrictHomBelow, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((S.restrictionComp T W ⊤ hTW le_top).hom.app K')
      ((S.restriction T W hTW).map (restrictionIsoOfTopIso S eK W hWO).hom) _,
    restrictionComp_restrictionIsoOfTopIso S eK hTW hWO]
  simp only [Category.assoc]
  rw [htail]

/-! ### The glueing condition at a fixed pair of objects -/

/-- **The glueing of morphisms at an open, for a fixed pair of objects over it.** This is the
body of `Stacks.DerivedGlueing.HasGluingForHomsAt` with the two objects fixed: a family of
morphisms between their restrictions to the members of the collection contained in `O`,
compatible with restriction between members, comes from a unique morphism over `O`. -/
def GluesHomsAt (S : LocallyGiven X) (O : Opens X.carrier)
    (K L : OpenDerivedCategory X O) : Prop :=
  (∀ (W : Opens X.carrier), W ∈ S.opens → ∀ hWO : W ≤ O, ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((S.restriction W O hWO).obj K)
        ((S.restriction W O hWO).obj L) i)) →
    ∀ φ : ∀ (W : Opens X.carrier), W ∈ S.opens → ∀ hWO : W ≤ O,
        (S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L,
      (∀ (W T : Opens X.carrier) (hW : W ∈ S.opens) (hT : T ∈ S.opens) (hTW : T ≤ W)
          (hWO : W ≤ O), restrictHomBelow S hTW hWO (φ W hW hWO) = φ T hT (hTW.trans hWO)) →
      ∃! ψ : K ⟶ L, ∀ (W : Opens X.carrier) (hW : W ∈ S.opens) (hWO : W ≤ O),
        (S.restriction W O hWO).map ψ = φ W hW hWO

/-- `Stacks.DerivedGlueing.HasGluingForHomsAt` is the glueing condition at every pair of
objects. -/
theorem hasGluingForHomsAt_iff_forall_gluesHomsAt (S : LocallyGiven X) (O : Opens X.carrier) :
    HasGluingForHomsAt S O ↔ ∀ K L : OpenDerivedCategory X O, GluesHomsAt S O K L :=
  Iff.rfl

/-- **The glueing condition at a pair of objects depends only on their isomorphism classes.**
Transporting a compatible family along the restrictions of the two isomorphisms is compatible,
by `Stacks.DerivedGlueing.restrictHomBelow_map_comp_map`, and conjugation is a bijection between
the two sets of solutions. -/
theorem GluesHomsAt.of_iso {S : LocallyGiven X} {O : Opens X.carrier}
    {K₁ K₂ L₁ L₂ : OpenDerivedCategory X O} (h : GluesHomsAt S O K₁ L₁)
    (eK : K₁ ≅ K₂) (eL : L₁ ≅ L₂) : GluesHomsAt S O K₂ L₂ := by
  intro hExt φ hφ
  obtain ⟨ψ, hψ, huniq⟩ := h
    (fun W hW hWO i hi => subsingleton_shiftedHom_of_iso
      ((S.restriction W O hWO).mapIso eK) ((S.restriction W O hWO).mapIso eL) i
      (hExt W hW hWO i hi))
    (fun W hW hWO => ((S.restriction W O hWO).mapIso eK).hom ≫ φ W hW hWO ≫
      ((S.restriction W O hWO).mapIso eL).inv)
    (fun W T hW hT hTW hWO => by
      simpa using (restrictHomBelow_map_comp_map S eK.hom eL.inv hTW hWO
        (φ W hW hWO)).trans (by rw [hφ W T hW hT hTW hWO]))
  refine ⟨eK.inv ≫ ψ ≫ eL.hom, fun W hW hWO => ?_, fun χ hχ => ?_⟩
  · simp [hψ W hW hWO]
  · have hχ' : eK.hom ≫ χ ≫ eL.inv = ψ := by
      refine huniq _ fun W hW hWO => ?_
      simp [hχ W hW hWO]
    rw [← hχ']
    simp

/-! ### The glueing condition for objects given over the whole space -/

/-- **The glueing of morphisms at an open, for objects given over the whole space.** This is the
glueing condition at `O` read at restrictions from `⊤`, and stated entirely in terms of
restrictions from `⊤`: it is the shape in which this development carries the sheaf condition of
[Stacks, Tag 0D66] part (2), whose objects are objects of the derived category of the whole of
`X`. -/
def HasGluingForHomsAtOfGlobal (S : LocallyGiven X) (O : Opens X.carrier) : Prop :=
  ∀ K' L' : OpenDerivedCategory X ⊤,
    (∀ (W : Opens X.carrier), W ∈ S.opens → W ≤ O → ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((S.restriction W ⊤ le_top).obj K')
        ((S.restriction W ⊤ le_top).obj L') i)) →
    ∀ φ : ∀ (W : Opens X.carrier), W ∈ S.opens → W ≤ O →
        ((S.restriction W ⊤ le_top).obj K' ⟶ (S.restriction W ⊤ le_top).obj L'),
      (∀ (W T : Opens X.carrier) (hW : W ∈ S.opens) (hT : T ∈ S.opens) (hTW : T ≤ W)
          (hWO : W ≤ O),
        restrictHomBelow S hTW le_top (φ W hW hWO) = φ T hT (hTW.trans hWO)) →
      ∃! ψ : (S.restriction O ⊤ le_top).obj K' ⟶ (S.restriction O ⊤ le_top).obj L',
        ∀ (W : Opens X.carrier) (hW : W ∈ S.opens) (hWO : W ≤ O),
          restrictHomBelow S hWO le_top ψ = φ W hW hWO

/-- **Restricting a morphism over `⊤` to an open below `O`, read through the identifications.**
At the identity identification the comparison of
`Stacks.DerivedGlueing.restrictionIsoOfTopIso` is the comparison of restriction in one and in
two steps, and `Stacks.DerivedGlueing.restrictHomBelow` is its conjugation by definition. -/
theorem restrictHomBelow_eq_conj_restrictionIsoOfTopIso (S : LocallyGiven X)
    {O : Opens X.carrier} {K' L' : OpenDerivedCategory X ⊤} {W : Opens X.carrier}
    (hWO : W ≤ O)
    (ψ : (S.restriction O ⊤ le_top).obj K' ⟶ (S.restriction O ⊤ le_top).obj L') :
    restrictHomBelow S hWO le_top ψ =
      (restrictionIsoOfTopIso S (Iso.refl ((S.restriction O ⊤ le_top).obj K')) W hWO).hom ≫
        (S.restriction W O hWO).map ψ ≫
          (restrictionIsoOfTopIso S (Iso.refl ((S.restriction O ⊤ le_top).obj L')) W hWO).inv := by
  simp [restrictHomBelow, restrictionIsoOfTopIso]

/-- **The glueing condition for global objects gives the glueing condition at the restrictions
from `⊤`.** The family is transported along
`Stacks.DerivedGlueing.restrictionIsoOfTopIso`, which carries the restriction map across by
`Stacks.DerivedGlueing.restrictHomBelow_restrictionIsoOfTopIso`. -/
theorem gluesHomsAt_restriction_top_of_global (S : LocallyGiven X) {O : Opens X.carrier}
    (hglue : HasGluingForHomsAtOfGlobal S O) (K' L' : OpenDerivedCategory X ⊤) :
    GluesHomsAt S O ((S.restriction O ⊤ le_top).obj K')
      ((S.restriction O ⊤ le_top).obj L') := by
  intro hExt φ hφ
  obtain ⟨ψ, hψ, huniq⟩ := hglue K' L'
    (fun W hW hWO i hi => subsingleton_shiftedHom_of_iso
      (restrictionIsoOfTopIso S (Iso.refl ((S.restriction O ⊤ le_top).obj K')) W hWO)
      (restrictionIsoOfTopIso S (Iso.refl ((S.restriction O ⊤ le_top).obj L')) W hWO) i
      (hExt W hW hWO i hi))
    (fun W hW hWO =>
      (restrictionIsoOfTopIso S (Iso.refl ((S.restriction O ⊤ le_top).obj K')) W hWO).hom ≫
        φ W hW hWO ≫
        (restrictionIsoOfTopIso S (Iso.refl ((S.restriction O ⊤ le_top).obj L')) W hWO).inv)
    (fun W T hW hT hTW hWO => by
      rw [restrictHomBelow_restrictionIsoOfTopIso, hφ W T hW hT hTW hWO])
  refine ⟨ψ, fun W hW hWO => ?_, fun χ hχ => ?_⟩
  · have h := hψ W hW hWO
    rw [restrictHomBelow_eq_conj_restrictionIsoOfTopIso] at h
    simpa using h
  · refine huniq _ fun W hW hWO => ?_
    rw [restrictHomBelow_eq_conj_restrictionIsoOfTopIso, hχ W hW hWO]

/-! ### The relativization -/

/-- **The glueing condition at an open need only be checked at restrictions from `⊤`.** Every
object over `O` is such a restriction up to isomorphism,
`Stacks.DerivedGlueing.exists_restriction_top_iso`, and the condition at a fixed pair of objects
depends only on their isomorphism classes. -/
theorem hasGluingForHomsAt_of_forall_restriction_top (S : LocallyGiven X)
    {O : Opens X.carrier}
    (h : ∀ K' L' : OpenDerivedCategory X ⊤,
      GluesHomsAt S O ((S.restriction O ⊤ le_top).obj K')
        ((S.restriction O ⊤ le_top).obj L')) :
    HasGluingForHomsAt S O := by
  intro K L
  obtain ⟨K', ⟨eK⟩⟩ := exists_restriction_top_iso S O K
  obtain ⟨L', ⟨eL⟩⟩ := exists_restriction_top_iso S O L
  exact (h K' L').of_iso eK eL

/-- **The relativization of the glueing of morphisms, complete.** The glueing condition at an
open `O` for objects given only over `O` — which is what Tags 0D68 and 0D69 consume — follows
from the glueing condition at `O` for objects given over the whole space, which is the shape in
which this development carries the sheaf condition of [Stacks, Tag 0D66] part (2).

Nothing is granted: the two halves are
`Stacks.DerivedGlueing.exists_restriction_top_iso`, that every object over `O` is a restriction
from `⊤` up to isomorphism, and
`Stacks.DerivedGlueing.restrictHomBelow_restrictionIsoOfTopIso`, that the identification carries
the restriction map of `W ↦ Hom(K|_W, L|_W)` across. -/
theorem hasGluingForHomsAt_of_global (S : LocallyGiven X) {O : Opens X.carrier}
    (hglue : HasGluingForHomsAtOfGlobal S O) : HasGluingForHomsAt S O :=
  hasGluingForHomsAt_of_forall_restriction_top S
    (gluesHomsAt_restriction_top_of_global S hglue)

end Stacks.DerivedGlueing

end
