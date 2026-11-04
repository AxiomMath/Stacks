module

public import Mathlib.Topology.Sheaves.SheafCondition.OpensLeCover

/-!
# Amalgamating a compatible family of maps into the sections of a sheaf

Let `F` be a sheaf of objects of a category `C` on a topological space `X`, let `P` be an open
subset of `X` covered by a family `K` of open subsets, and let `A` be an object of `C`. A family
of maps `A ⟶ F(V)`, one for each open `V` contained in some member of the cover, compatible with
restriction, amalgamates to a unique map `A ⟶ F(P)`.

This is the sheaf axiom in the form in which it is used to glue morphisms, phrased so that no
colimit or limit appears in the statement: `exists_amalgamation` is the existence half and
`amalgamation_unique` the uniqueness half. Both are read off from
`TopCat.Presheaf.IsSheaf.isSheafOpensLeCover`, which says that `F(P)` is the limit of the `F(V)`
over exactly the opens `V` contained in some `K i`; indexing the limit by *all* such `V` rather
than by the cover and its pairwise intersections is what makes the two statements above free of
case distinctions.

## Main results

* `TopCat.Presheaf.exists_amalgamation`: a compatible family of maps into the sections over the
  members of a cover amalgamates.
* `TopCat.Presheaf.amalgamation_unique`: a map into the sections over `P` is determined by its
  restrictions to the opens contained in some member of the cover.
* `TopCat.Presheaf.res_eq_of_res_eq`: two maps into sections over opens that are equal, but
  presented differently, agree as soon as their restrictions to a common open agree.

## References

* [Stacks Project, Tag 0072](https://stacks.math.columbia.edu/tag/0072)
-/

@[expose] public section

universe v u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TopCat.Presheaf.SheafCondition

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}}

section Map

variable (F : Presheaf C X)

/-- Two restriction maps of a presheaf on a space compose to a third one: the inclusions between
two fixed open subsets form a subsingleton, so there is nothing to choose. -/
theorem map_comp_map {A B D : (Opens X)ᵒᵖ} (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ D) :
    F.map a ≫ F.map b = F.map c := by
  rw [← F.map_comp]; rfl

/-- The restriction map of a presheaf along an inclusion of *equal* open subsets is an
isomorphism. -/
theorem isIso_map_of_eq {A B : Opens X} (i : A ⟶ B) (e : A = B) : IsIso (F.map i.op) := by
  subst e
  rw [show i = 𝟙 A from rfl, op_id, F.map_id]
  infer_instance

/-- Let `T` and `V` be open subsets with `V ≤ T` and `T ≤ V`, so that they are equal, and let
`φ : A ⟶ F(P)` and `ψ : A ⟶ F(T)` restrict to the same map on `V`. Then `ψ` is the restriction
of `φ` along any inclusion `T ≤ P`.

The two inclusions `hVT` and `hTV` replace an equality of open subsets, and so an `eqToHom`, by
inclusions in both directions; `m` is then an arbitrary restriction map, which is how this
lemma absorbs an `eqToHom` arising elsewhere. -/
theorem res_eq_of_res_eq {A : C} {P T V : Opens X} (φ : A ⟶ F.obj (op P)) (ψ : A ⟶ F.obj (op T))
    (hVT : V ≤ T) (hTV : T ≤ V) (hVP : V ≤ P)
    (hres : φ ≫ F.map (homOfLE hVP).op = ψ ≫ F.map (homOfLE hVT).op) (m : op P ⟶ op T) :
    φ ≫ F.map m = ψ := by
  rw [← map_comp_map F (homOfLE hVP).op (homOfLE hTV).op m, ← Category.assoc, hres,
    Category.assoc, map_comp_map F _ _ (𝟙 (op T)), F.map_id, Category.comp_id]

end Map

variable {F : Presheaf C X}

/-- A compatible family of maps `A ⟶ F(V)`, indexed by the open subsets `V` contained in some
member of a family `K`, as a cone over the opens-contained-in-a-member diagram. -/
def amalgCone {ι : Type*} (K : ι → Opens X) {A : C}
    (s : ∀ V : Opens X, (∃ i, V ≤ K i) → (A ⟶ F.obj (op V)))
    (hs : ∀ (V V' : Opens X) (hV : ∃ i, V ≤ K i) (hV' : ∃ i, V' ≤ K i) (h : V' ≤ V),
      s V hV ≫ F.map (homOfLE h).op = s V' hV') :
    Cone ((ObjectProperty.ι _ : OpensLeCover K ⥤ Opens X).op ⋙ F) where
  pt := A
  π :=
    { app := fun V => s V.unop.obj V.unop.property
      naturality := fun _ _ m => by
        dsimp
        rw [Category.id_comp]
        exact (hs _ _ _ _ (leOfHom m.unop.hom)).symm }

/-- **The sheaf axiom, existence half.** If `F` is a sheaf and the open subset `P` is the union of
a family `K` of open subsets, then a family of maps `A ⟶ F(V)`, one for each open `V` contained in
some `K i` and compatible with restriction, is the family of restrictions of a map `A ⟶ F(P)`. -/
theorem exists_amalgamation (hF : F.IsSheaf) {ι : Type*} (K : ι → Opens X) {P : Opens X}
    (hP : iSup K = P) {A : C} (s : ∀ V : Opens X, (∃ i, V ≤ K i) → (A ⟶ F.obj (op V)))
    (hs : ∀ (V V' : Opens X) (hV : ∃ i, V ≤ K i) (hV' : ∃ i, V' ≤ K i) (h : V' ≤ V),
      s V hV ≫ F.map (homOfLE h).op = s V' hV') :
    ∃ t : A ⟶ F.obj (op P), ∀ (V : Opens X) (hV : ∃ i, V ≤ K i) (hVP : V ≤ P),
      t ≫ F.map (homOfLE hVP).op = s V hV := by
  subst hP
  obtain ⟨hl⟩ := hF.isSheafOpensLeCover K
  exact ⟨hl.lift (amalgCone K s hs), fun V hV _ => hl.fac (amalgCone K s hs) (op ⟨V, hV⟩)⟩

/-- **The sheaf axiom, uniqueness half.** If `F` is a sheaf and the open subset `P` is the union
of a family `K` of open subsets, then a map `A ⟶ F(P)` is determined by its restrictions to the
open subsets contained in some `K i`. -/
theorem amalgamation_unique (hF : F.IsSheaf) {ι : Type*} (K : ι → Opens X) {P : Opens X}
    (hP : iSup K = P) {A : C} {t₁ t₂ : A ⟶ F.obj (op P)}
    (h : ∀ (V : Opens X) (_ : ∃ i, V ≤ K i) (hVP : V ≤ P),
      t₁ ≫ F.map (homOfLE hVP).op = t₂ ≫ F.map (homOfLE hVP).op) :
    t₁ = t₂ := by
  subst hP
  obtain ⟨hl⟩ := hF.isSheafOpensLeCover K
  refine hl.hom_ext fun V => ?_
  induction V with | op V => ?_
  exact h V.obj V.property (leOfHom ((opensLeCoverCocone K).ι.app V))

end TopCat.Presheaf

end
