module

public import StacksFrontier.Topology.Sheaves.Limits.GermPullback

/-!
# The stalks of the inverse image of a sheaf of sets

Let `g : Z → Y` be a continuous map and let `𝒢` be a presheaf of types on `Y`.  The inverse
image `g⁻¹𝒢`, realised as the sheaf of germs `GermPullback.sheaf g 𝒢`, has the same stalks as
`𝒢`: the canonical map

`𝒢_{g z} ⟶ (g⁻¹𝒢)_z`

sending the germ at `g z` of a section `s` of `𝒢` on `V` to the germ at `z` of the germwise
pullback `GermPullback.ofSection s` on `g⁻¹(V)` is bijective.  This is the basic property of
the inverse image of a sheaf of sets, and the one on which proper base change for sheaves of
sets, [Stacks, Tag 0D90](https://stacks.math.columbia.edu/tag/0D90), rests.

## Main definitions

* `GermPullback.preimageOpens`: the preimage of an open subset of `Y` under a continuous map,
  as an open subset of `Z`.
* `GermPullback.germOfSection`: the germ at `z` of the germwise pullback of a section of `𝒢`.
* `GermPullback.stalkCocone`: the cocone computing `stalkMap`.
* `GermPullback.stalkMap`: the canonical map `𝒢_{g z} ⟶ (g⁻¹𝒢)_z`.
* `GermPullback.stalkMapEquiv`: that map as a bijection.

## Main results

* `GermPullback.fst_val`: the value of a section of `g⁻¹𝒢` at `z` is a germ of `𝒢` at `g z`.
* `GermPullback.stalkMap_germ`: `stalkMap` sends the germ of `s` at `g z` to the germ at `z` of
  the germwise pullback of `s`, over *any* open on which the latter is defined.
* `GermPullback.exists_ofSection_germ_eq`: every germ of `g⁻¹𝒢` at `z` is the germ of a
  germwise pullback of a section of `𝒢`.
* `GermPullback.germ_ofSection_eq_iff`: two germwise pullbacks have the same germ at `z` exactly
  when the two sections have the same germ at `g z`.
* `GermPullback.bijective_stalkMap`: `stalkMap` is bijective.

## Implementation notes

The value of a section of `g⁻¹𝒢` at a point `z` *is* its germ at `z`, an element of the total
space `GermPullback.Germs 𝒢` whose first component is `g z` (`GermPullback.fst_val`).  Both
halves of the bijection are therefore immediate from the two basic facts about the germ model:
`GermPullback.exists_repr`, which says a section is locally a germwise pullback, and the fact
that a section of the germ model is determined by its values.  No colimit is manipulated beyond
the cocone defining `stalkMap`.

Because `GermPullback.Germs 𝒢` is a sigma type over the points of `Y` and the stalks of `𝒢`,
the value universe of `𝒢` is forced to be the universe of `Y`, and `Z` must live in the same
universe.

## References

* [Stacks, Tag 0D90](https://stacks.math.columbia.edu/tag/0D90)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite

universe u

noncomputable section

namespace GermPullback

variable {Y Z : TopCat.{u}} {g : Z → Y} {𝒢 : Y.Presheaf (Type u)}

/-! ### Elementary properties of the germ model -/

/-- The first component of the value of a section of `g⁻¹𝒢` at a point `z` is `g z`: the value
is a germ of `𝒢` at `g z` (Stacks 0D90). -/
lemma fst_val {W : Opens Z} (σ : (sheaf g 𝒢).presheaf.obj (op W)) (z : W) :
    (σ.1 z).1 = g z.1 := by
  obtain ⟨W₀, hz₀, i, V, hV, s, hs⟩ := exists_repr σ z.2
  have hz : i ⟨z.1, hz₀⟩ = z := Subtype.ext rfl
  have h := hs ⟨z.1, hz₀⟩
  rw [hz] at h
  rw [h]

/-- Restriction of a germwise pullback to a smaller open is the germwise pullback over that
smaller open (Stacks 0D90).

This is the form at an arbitrary continuous `g` and an arbitrary presheaf of types, of which
`GermPullback.map_ofSection` is the instance for the underlying presheaf of types of a presheaf
of abelian groups along a morphism of topological spaces. -/
lemma map_ofSection' {W W' : Opens Z} (i : W' ⟶ W) {V : Opens Y} (hV : ∀ z : W, g z.1 ∈ V)
    (s : 𝒢.obj (op V)) :
    (sheaf g 𝒢).presheaf.map i.op (ofSection hV s) = ofSection (fun z ↦ hV (i z)) s := rfl

/-- The germwise pullback of a restricted section is the germwise pullback of the section
(Stacks 0D90). -/
lemma ofSection_map {W : Opens Z} {V V' : Opens Y} (j : V ⟶ V') (hV : ∀ z : W, g z.1 ∈ V)
    (s : 𝒢.obj (op V')) :
    ofSection hV (𝒢.map j.op s) = ofSection (fun z ↦ j.le (hV z)) s := by
  refine ext fun z ↦ ?_
  rw [ofSection_val, ofSection_val, 𝒢.germOfSize_res_apply j (g z.1) (hV z) s]

/-- The preimage of an open subset of `Y` under a continuous map `g : Z → Y`, as an open subset
of `Z`.  It is the largest open on which the germwise pullback of a section of `𝒢` over `V` is
defined (Stacks 0D90). -/
def preimageOpens (hg : Continuous g) (V : Opens Y) : Opens Z :=
  ⟨g ⁻¹' (V : Set Y), V.isOpen.preimage hg⟩

/-- A point lies in `preimageOpens hg V` exactly when its image lies in `V` (Stacks 0D90). -/
lemma mem_preimageOpens {hg : Continuous g} {V : Opens Y} {z : Z} :
    z ∈ preimageOpens hg V ↔ g z ∈ V := Iff.rfl

/-! ### Local description of the germs of an inverse image -/

/-- Every germ of `g⁻¹𝒢` at `z` is the germ of the germwise pullback of a section of `𝒢`: this
is `GermPullback.exists_repr` read in the stalk (Stacks 0D90). -/
lemma exists_ofSection_germ_eq {z : Z} (a : (sheaf g 𝒢).presheaf.stalk z) :
    ∃ (V : Opens Y) (W : Opens Z) (hzW : z ∈ W) (hV : ∀ x : W, g x.1 ∈ V) (s : 𝒢.obj (op V)),
      (sheaf g 𝒢).presheaf.germ W z hzW (ofSection hV s) = a := by
  obtain ⟨W, hzW, σ, rfl⟩ := (sheaf g 𝒢).presheaf.exists_germ_eq a
  obtain ⟨W₀, hz₀, i, V, hV, s, hs⟩ := exists_repr σ hzW
  refine ⟨V, W₀, hz₀, hV, s, ?_⟩
  calc (sheaf g 𝒢).presheaf.germ W₀ z hz₀ (ofSection hV s)
      = (sheaf g 𝒢).presheaf.germ W₀ z hz₀ ((sheaf g 𝒢).presheaf.map i.op σ) :=
        congrArg (fun t ↦ (sheaf g 𝒢).presheaf.germ W₀ z hz₀ t) (ext fun x ↦ hs x).symm
    _ = (sheaf g 𝒢).presheaf.germ W z hzW σ :=
        (sheaf g 𝒢).presheaf.germ_res_apply i z hz₀ σ

/-- Two germwise pullbacks have the same germ at `z` exactly when the two sections of `𝒢` have
the same germ at `g z` (Stacks 0D90). -/
lemma germ_ofSection_eq_iff (hg : Continuous g) {z : Z} {V V' : Opens Y} {W W' : Opens Z}
    (hzW : z ∈ W) (hzW' : z ∈ W') (hV : ∀ x : W, g x.1 ∈ V) (hV' : ∀ x : W', g x.1 ∈ V')
    (s : 𝒢.obj (op V)) (s' : 𝒢.obj (op V')) :
    (sheaf g 𝒢).presheaf.germ W z hzW (ofSection hV s) =
        (sheaf g 𝒢).presheaf.germ W' z hzW' (ofSection hV' s') ↔
      𝒢.germOfSize V (g z) (hV ⟨z, hzW⟩) s = 𝒢.germOfSize V' (g z) (hV' ⟨z, hzW'⟩) s' := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨W₀, hz₀, i, i', he⟩ := (sheaf g 𝒢).presheaf.germ_eq z hzW hzW' _ _ h
    have hval := congrArg (fun σ ↦ σ.1 ⟨z, hz₀⟩) he
    simp only [val_map_apply, ofSection_val, Opens.val_apply] at hval
    exact eq_of_heq ((Sigma.mk.injEq _ _ _ _).mp hval).2
  · obtain ⟨V₀, hz₀, j, j', hj⟩ := 𝒢.germOfSize_eq (g z) (hV ⟨z, hzW⟩) (hV' ⟨z, hzW'⟩) s s' h
    set A : Opens Z := W ⊓ W' ⊓ preimageOpens hg V₀
    have hle : A ≤ W := inf_le_left.trans inf_le_left
    have hle' : A ≤ W' := inf_le_left.trans inf_le_right
    have hmem : z ∈ A := ⟨⟨hzW, hzW'⟩, hz₀⟩
    have h₀ : ∀ x : A, g x.1 ∈ V₀ := fun x ↦ x.2.2
    have key : ofSection (fun x : A ↦ hV (homOfLE hle x)) s
        = ofSection (fun x : A ↦ hV' (homOfLE hle' x)) s' :=
      (ofSection_map j h₀ s).symm.trans
        ((congrArg (ofSection h₀) hj).trans (ofSection_map j' h₀ s'))
    rw [← (sheaf g 𝒢).presheaf.germ_res_apply (homOfLE hle) z hmem,
      ← (sheaf g 𝒢).presheaf.germ_res_apply (homOfLE hle') z hmem]
    exact congrArg _ key

/-! ### The comparison map on stalks -/

/-- The germ at `z` of the germwise pullback, on `g⁻¹(A)`, of a section of `𝒢` on an open
neighbourhood `A` of `g z`.  These germs assemble into the cocone defining
`GermPullback.stalkMap` (Stacks 0D90). -/
def germOfSection (hg : Continuous g) (𝒢 : Y.Presheaf (Type u)) {z : Z} (A : Opens Y)
    (hA : g z ∈ A) (s : 𝒢.obj (op A)) : (sheaf g 𝒢).presheaf.stalk z :=
  (sheaf g 𝒢).presheaf.germ (preimageOpens hg A) z hA
    (ofSection (fun x ↦ mem_preimageOpens.mp x.2) s)

/-- The germ of the germwise pullback of a section does not change when the section is first
restricted to a smaller open neighbourhood of `g z` (Stacks 0D90). -/
lemma germOfSection_map (hg : Continuous g) (𝒢 : Y.Presheaf (Type u)) {z : Z} {A B : Opens Y}
    (hA : g z ∈ A) (hB : g z ∈ B) (j : B ⟶ A) (s : 𝒢.obj (op A)) :
    germOfSection hg 𝒢 B hB (𝒢.map j.op s) = germOfSection hg 𝒢 A hA s := by
  unfold germOfSection
  exact (germ_ofSection_eq_iff hg hB hA _ _ _ _).2 (𝒢.germOfSize_res_apply j (g z) hB s)

/-- The cocone on the diagram computing `𝒢_{g z}` whose vertex is `(g⁻¹𝒢)_z`: a section of `𝒢`
on an open neighbourhood `V` of `g z` goes to the germ at `z` of its germwise pullback on
`g⁻¹(V)` (Stacks 0D90). -/
def stalkCocone (hg : Continuous g) (𝒢 : Y.Presheaf (Type u)) (z : Z) :
    Cocone ((OpenNhds.inclusion (g z)).op ⋙ 𝒢) where
  pt := (sheaf g 𝒢).presheaf.stalk z
  ι :=
    { app := fun V ↦ TypeCat.ofHom (germOfSection hg 𝒢 (unop V).1 (unop V).2)
      naturality := by
        intro V V' i
        ext s
        exact germOfSection_map hg 𝒢 (unop V).2 (unop V').2
          ((OpenNhds.inclusion (g z)).map i.unop) s }

/-- The canonical map `𝒢_{g z} ⟶ (g⁻¹𝒢)_z` from the stalk of `𝒢` at `g z` to the stalk of the
inverse image `g⁻¹𝒢` at `z`.  It is bijective (`GermPullback.bijective_stalkMap`).  This is the
computation of the stalks of an inverse image used in Stacks 0D90. -/
def stalkMap (hg : Continuous g) (𝒢 : Y.Presheaf (Type u)) (z : Z) :
    𝒢.stalkOfSize (g z) ⟶ (sheaf g 𝒢).presheaf.stalk z :=
  colimit.desc _ (stalkCocone hg 𝒢 z)

/-- `stalkMap` sends the germ at `g z` of a section `s` of `𝒢` on `V` to the germ at `z` of the
germwise pullback of `s` on `g⁻¹(V)` (Stacks 0D90). -/
lemma stalkMap_germ_preimageOpens (hg : Continuous g) (𝒢 : Y.Presheaf (Type u)) (z : Z)
    {V : Opens Y} (hz : g z ∈ V) (s : 𝒢.obj (op V)) :
    stalkMap hg 𝒢 z (𝒢.germOfSize V (g z) hz s) = germOfSection hg 𝒢 V hz s := by
  have hι : 𝒢.germOfSize V (g z) hz ≫ stalkMap hg 𝒢 z =
      (stalkCocone hg 𝒢 z).ι.app (op (⟨V, hz⟩ : OpenNhds (g z))) :=
    colimit.ι_desc (stalkCocone hg 𝒢 z) (op (⟨V, hz⟩ : OpenNhds (g z)))
  exact ConcreteCategory.congr_hom hι s

/-- `stalkMap` sends the germ at `g z` of a section `s` of `𝒢` on `V` to the germ at `z` of the
germwise pullback of `s`, computed over any open `W` containing `z` which `g` maps into `V`
(Stacks 0D90). -/
lemma stalkMap_germ (hg : Continuous g) (𝒢 : Y.Presheaf (Type u)) (z : Z) {V : Opens Y}
    (hz : g z ∈ V) {W : Opens Z} (hzW : z ∈ W) (hV : ∀ x : W, g x.1 ∈ V) (s : 𝒢.obj (op V)) :
    stalkMap hg 𝒢 z (𝒢.germOfSize V (g z) hz s) =
      (sheaf g 𝒢).presheaf.germ W z hzW (ofSection hV s) := by
  rw [stalkMap_germ_preimageOpens hg 𝒢 z hz s]
  exact (germ_ofSection_eq_iff hg hz hzW _ hV s s).2 rfl

/-! ### The comparison map is bijective -/

/-- **The stalks of an inverse image.** The canonical map from the stalk of `𝒢` at `g z` to the
stalk of the inverse image `g⁻¹𝒢` at `z` is bijective.  This is the topological input to
Stacks 0D90. -/
theorem bijective_stalkMap (hg : Continuous g) (𝒢 : Y.Presheaf (Type u)) (z : Z) :
    Function.Bijective (stalkMap hg 𝒢 z) := by
  refine ⟨fun ξ ξ' h ↦ ?_, fun a ↦ ?_⟩
  · obtain ⟨V, hz, s, rfl⟩ := 𝒢.exists_germOfSize_eq ξ
    obtain ⟨V', hz', s', rfl⟩ := 𝒢.exists_germOfSize_eq ξ'
    rw [stalkMap_germ_preimageOpens hg 𝒢 z hz s,
      stalkMap_germ_preimageOpens hg 𝒢 z hz' s'] at h
    unfold germOfSection at h
    exact (germ_ofSection_eq_iff hg hz hz'
      (fun x : preimageOpens hg V ↦ mem_preimageOpens.mp x.2)
      (fun x : preimageOpens hg V' ↦ mem_preimageOpens.mp x.2) s s').1 h
  · obtain ⟨V, W, hzW, hV, s, h⟩ := exists_ofSection_germ_eq a
    exact ⟨𝒢.germOfSize V (g z) (hV ⟨z, hzW⟩) s,
      (stalkMap_germ hg 𝒢 z (hV ⟨z, hzW⟩) hzW hV s).trans h⟩

/-- **The stalks of an inverse image.** The stalk of the inverse image `g⁻¹𝒢` at `z` is the
stalk of `𝒢` at `g z`, via `GermPullback.stalkMap` (Stacks 0D90). -/
def stalkMapEquiv (hg : Continuous g) (𝒢 : Y.Presheaf (Type u)) (z : Z) :
    𝒢.stalkOfSize (g z) ≃ (sheaf g 𝒢).presheaf.stalk z :=
  Equiv.ofBijective _ (bijective_stalkMap hg 𝒢 z)

/-- `stalkMapEquiv` is `stalkMap` (Stacks 0D90). -/
@[simp]
lemma stalkMapEquiv_apply (hg : Continuous g) (𝒢 : Y.Presheaf (Type u)) (z : Z)
    (ξ : 𝒢.stalkOfSize (g z)) : stalkMapEquiv hg 𝒢 z ξ = stalkMap hg 𝒢 z ξ := rfl

end GermPullback

end
