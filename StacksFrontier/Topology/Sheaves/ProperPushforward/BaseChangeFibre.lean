module

public import StacksFrontier.Topology.Sheaves.ProperPushforward.SectionsOnQuasiCompactSubset

/-!
# The fibres of a base change, and the inverse image of a sheaf of sets along it

Let `f : X → Y` and `g : Z → Y` be continuous maps and form the cartesian square

```
X ×_Y Z --- g' ---> X
   |                |
   f'               f
   v                v
   Z  --- g ----->  Y
```

with `X ×_Y Z = Function.Pullback g f = {p : Z × X // g p.1 = f p.2}`, `f' = Function.Pullback.fst`
and `g' = Function.Pullback.snd`.  For a point `z : Z` the second projection restricts to a
homeomorphism from the fibre `f'⁻¹(z)` onto the fibre `f⁻¹(g z)`
(`Stacks.Topology.ProperBaseChange.fibreHomeomorph`), and under it the inverse image
`(g')⁻¹F` restricted to `f'⁻¹(z)` becomes `F` restricted to `f⁻¹(g z)`.

In the germ model of the inverse image this last statement is not an isomorphism to be built
but an equality of sheaves: sections of `(g')⁻¹F` on an open `W` of `X ×_Y Z` containing
`f'⁻¹(z)` restrict, by `GermPullback.comap` along the fibre inclusion, to sections of `F` on
`f⁻¹(g z)` in the sense of `Stacks.Topology.SectionsOnQuasiCompactSubset.sectionsOn`, and a
germwise pullback restricts to the corresponding family of germs of `F`
(`Stacks.Topology.ProperBaseChange.restrictToFibre_ofSection`).  This is the second ingredient
of proper base change for sheaves of sets,
[Stacks, Tag 0D90](https://stacks.math.columbia.edu/tag/0D90).

## Main definitions

* `Stacks.Topology.ProperBaseChange.pullbackSpace`: the fibre product `X ×_Y Z` as an object of
  `TopCat`.
* `Stacks.Topology.ProperBaseChange.fibreInclusion`: the map `f⁻¹(g z) → X ×_Y Z`,
  `x ↦ (z, x)`.
* `Stacks.Topology.ProperBaseChange.fibreHomeomorph`: the induced homeomorphism
  `f'⁻¹(z) ≃ₜ f⁻¹(g z)`.
* `Stacks.Topology.ProperBaseChange.restrictToFibre`: restriction of a section of `(g')⁻¹F`
  to the fibre `f'⁻¹(z)`, read as a section of `F` on `f⁻¹(g z)`.

## Main results

* `Stacks.Topology.ProperBaseChange.continuous_pullbackFst`,
  `Stacks.Topology.ProperBaseChange.continuous_pullbackSnd`: the two projections of the fibre
  product are continuous.
* `Stacks.Topology.ProperBaseChange.restrictToFibre_val`: `restrictToFibre` is evaluation along
  the fibre inclusion.
* `Stacks.Topology.ProperBaseChange.restrictToFibre_ofSection`: the restriction to the fibre of
  a germwise pullback of `s` is the family of germs of `s` along `f⁻¹(g z)`.

## Implementation notes

The fibre product is Mathlib's `Function.Pullback`, which is the subspace
`{p : Z × X // g p.1 = f p.2}` of `Z × X`; this is the shape in which Stacks 005O (4) states
universal closedness, so "`f'` is a closed map" needs no translation.

Only the statements about sheaves need all three spaces to live in one universe — a consequence
of `GermPullback.Germs` being a sigma type over the points of the space.  The statements about
the fibres themselves are universe-polymorphic.

## References

* [Stacks, Tag 005O](https://stacks.math.columbia.edu/tag/005O)
* [Stacks, Tag 0D90](https://stacks.math.columbia.edu/tag/0D90)
-/

@[expose] public section

open CategoryTheory TopologicalSpace TopCat Opposite

universe u v w

noncomputable section

namespace Stacks.Topology.ProperBaseChange

/-! ### The projections of a fibre product of topological spaces -/

section Topology

variable {X : Type u} {Y : Type v} {Z : Type w} {f : X → Y} {g : Z → Y}

/-- The inclusion of the fibre `f⁻¹(g z)` into the fibre product `X ×_Y Z`, sending `x` to the
point `(z, x)`.  Its image is the fibre of the first projection over `z` (Stacks 0D90). -/
def fibreInclusion (f : X → Y) (g : Z → Y) (z : Z) (x : (f ⁻¹' {g z} : Set X)) :
    Function.Pullback g f :=
  ⟨(z, x.1), x.2.symm⟩

/-- The first projection of `fibreInclusion f g z x` is `z` (Stacks 0D90). -/
@[simp]
lemma fst_fibreInclusion (f : X → Y) (g : Z → Y) (z : Z) (x : (f ⁻¹' {g z} : Set X)) :
    Function.Pullback.fst (fibreInclusion f g z x) = z := rfl

/-- The second projection of `fibreInclusion f g z x` is `x` (Stacks 0D90). -/
@[simp]
lemma snd_fibreInclusion (f : X → Y) (g : Z → Y) (z : Z) (x : (f ⁻¹' {g z} : Set X)) :
    Function.Pullback.snd (fibreInclusion f g z x) = x.1 := rfl

/-- A point of the fibre product lying over `z : Z` has its second projection in the fibre
`f⁻¹(g z)` (Stacks 0D90). -/
lemma snd_mem_preimage_of_fst_eq {z : Z} {p : Function.Pullback g f}
    (hp : Function.Pullback.fst p = z) : Function.Pullback.snd p ∈ f ⁻¹' {g z} := by
  subst hp
  exact p.2.symm

variable [TopologicalSpace X] [TopologicalSpace Z]

/-- The first projection `X ×_Y Z → Z` of a fibre product of topological spaces is continuous.
This is the map whose closedness is universal closedness of `f`, Stacks 005O (4). -/
lemma continuous_pullbackFst :
    Continuous (Function.Pullback.fst : Function.Pullback g f → Z) :=
  continuous_fst.comp continuous_subtype_val

/-- The second projection `X ×_Y Z → X` of a fibre product of topological spaces is
continuous (Stacks 005O (4)). -/
lemma continuous_pullbackSnd :
    Continuous (Function.Pullback.snd : Function.Pullback g f → X) :=
  continuous_snd.comp continuous_subtype_val

/-- The fibre inclusion is continuous (Stacks 0D90). -/
lemma continuous_fibreInclusion (f : X → Y) (g : Z → Y) (z : Z) :
    Continuous (fibreInclusion f g z) :=
  Continuous.subtype_mk (continuous_const.prodMk continuous_subtype_val) _

/-- **The fibres of a base change.** For `z : Z` the second projection of the fibre product
restricts to a homeomorphism from the fibre of `f' : X ×_Y Z → Z` over `z` onto the fibre of
`f : X → Y` over `g z`.  This is the homeomorphism of fibres used in Stacks 0D90. -/
def fibreHomeomorph (f : X → Y) (g : Z → Y) (z : Z) :
    ((Function.Pullback.fst : Function.Pullback g f → Z) ⁻¹' {z}) ≃ₜ (f ⁻¹' {g z} : Set X) where
  toFun p := ⟨Function.Pullback.snd p.1, snd_mem_preimage_of_fst_eq p.2⟩
  invFun x := ⟨fibreInclusion f g z x, rfl⟩
  left_inv p := by
    refine Subtype.ext (Subtype.ext (Prod.ext ?_ rfl))
    exact p.2.symm
  right_inv _ := rfl
  continuous_toFun :=
    Continuous.subtype_mk (continuous_pullbackSnd.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk (continuous_fibreInclusion f g z) _

/-- `fibreHomeomorph` is the second projection (Stacks 0D90). -/
@[simp]
lemma fibreHomeomorph_apply (f : X → Y) (g : Z → Y) (z : Z)
    (p : ((Function.Pullback.fst : Function.Pullback g f → Z) ⁻¹' {z})) :
    (fibreHomeomorph f g z p).1 = Function.Pullback.snd p.1 := rfl

/-- The inverse of `fibreHomeomorph` is the fibre inclusion (Stacks 0D90). -/
@[simp]
lemma fibreHomeomorph_symm_apply (f : X → Y) (g : Z → Y) (z : Z)
    (x : (f ⁻¹' {g z} : Set X)) :
    ((fibreHomeomorph f g z).symm x).1 = fibreInclusion f g z x := rfl

end Topology

/-! ### The inverse image of a sheaf of sets on a fibre of a base change -/

section Sheaves

open Stacks.Topology.SectionsOnQuasiCompactSubset

variable {X Y Z : TopCat.{u}} {f : ↥X → ↥Y} {g : ↥Z → ↥Y}

/-- The fibre product `X ×_Y Z` as an object of `TopCat`, so that the inverse image `(g')⁻¹F`
of a sheaf of sets on `X` along the second projection can be formed (Stacks 0D90). -/
abbrev pullbackSpace (g : ↥Z → ↥Y) (f : ↥X → ↥Y) : TopCat.{u} :=
  TopCat.of (Function.Pullback g f)

/-- The restriction of a section of the inverse image `(g')⁻¹F` on an open subset `W` of
`X ×_Y Z` containing the fibre `f'⁻¹(z)` to that fibre, read — via the homeomorphism
`f'⁻¹(z) ≃ f⁻¹(g z)` — as a section of `F` on `f⁻¹(g z)`.

In the germ model this is `GermPullback.comap` along the fibre inclusion: both the source and
the target are sheaves of germs of the *same* sheaf `F`, taken along the two maps
`g' : X ×_Y Z → X` and `f⁻¹(g z) ↪ X`, and these agree on the fibre (Stacks 0D90). -/
def restrictToFibre (F : X.Presheaf (Type u)) (z : ↥Z) {W : Opens (pullbackSpace g f)}
    (hW : ∀ x : (f ⁻¹' {g z} : Set X), fibreInclusion f g z x ∈ W)
    (σ : (GermPullback.sheaf (Function.Pullback.snd) F).presheaf.obj (op W)) :
    sectionsOn F (f ⁻¹' {g z}) :=
  GermPullback.comap (Y := X) (Z := pullbackSpace g f)
    (Z' := TopCat.of (f ⁻¹' {g z} : Set ↥X)) (𝒢 := F)
    (g := Function.Pullback.snd) (g' := subspaceInclusion (f ⁻¹' {g z}))
    (h := fibreInclusion f g z) (W := W) (W' := ⊤)
    (continuous_fibreInclusion f g z) (fun _ ↦ rfl) (fun w ↦ hW w.1) σ

/-- `restrictToFibre` evaluates a section along the fibre inclusion (Stacks 0D90). -/
@[simp]
lemma restrictToFibre_val (F : X.Presheaf (Type u)) (z : ↥Z) {W : Opens (pullbackSpace g f)}
    (hW : ∀ x : (f ⁻¹' {g z} : Set X), fibreInclusion f g z x ∈ W)
    (σ : (GermPullback.sheaf (Function.Pullback.snd) F).presheaf.obj (op W))
    (w : ↥(⊤ : Opens (TopCat.of (f ⁻¹' {g z} : Set X)))) :
    (restrictToFibre F z hW σ).1 w = σ.1 ⟨fibreInclusion f g z w.1, hW w.1⟩ := rfl

/-- **The inverse image of a sheaf of sets on a fibre of a base change.** The restriction to the
fibre `f'⁻¹(z)` of the germwise pullback along `g'` of a section `s` of `F` on `U` is the family
of germs of `s` along the fibre `f⁻¹(g z)`.  Together with
`Stacks.Topology.ProperBaseChange.fibreHomeomorph` this is the statement that `(g')⁻¹F`
restricted to `f'⁻¹(z)` is `F` restricted to `f⁻¹(g z)` (Stacks 0D90). -/
lemma restrictToFibre_ofSection (F : X.Presheaf (Type u)) (z : ↥Z)
    {W : Opens (pullbackSpace g f)}
    (hW : ∀ x : (f ⁻¹' {g z} : Set X), fibreInclusion f g z x ∈ W) {U : Opens X}
    (hU : ∀ p : W, Function.Pullback.snd p.1 ∈ U) (s : F.obj (op U))
    (hZU : (f ⁻¹' {g z} : Set X) ⊆ (U : Set X)) :
    restrictToFibre F z hW (GermPullback.ofSection hU s) = restrictToSubset F hZU s :=
  GermPullback.comap_ofSection (Y := X) (Z := pullbackSpace g f)
    (Z' := TopCat.of (f ⁻¹' {g z} : Set ↥X)) (𝒢 := F)
    (g := Function.Pullback.snd) (g' := subspaceInclusion (f ⁻¹' {g z}))
    (h := fibreInclusion f g z) (W := W) (W' := ⊤)
    (continuous_fibreInclusion f g z) (fun _ ↦ rfl) (fun w ↦ hW w.1) hU s

end Sheaves

end Stacks.Topology.ProperBaseChange

end
