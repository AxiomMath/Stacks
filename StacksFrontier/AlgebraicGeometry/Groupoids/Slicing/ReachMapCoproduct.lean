module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Basic
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors

/-!
# The reach map of a jointly covering family, and of a coproduct

Let `(U, R, s, t, c)` be a groupoid scheme over `S` and let `g : U' ⟶ U` be a morphism of
schemes.  Its *reach map* is `h = pullback.snd g t ≫ s : U' ×_{g, U, t} R ⟶ U`, the morphism
sending an arrow of `R` whose target lifts along `g` to its source.

Step 3 of the proof of [Stacks Project, Tag 0489] forms `U' = ∐_u U'_u`, the coproduct of the
affine slices produced by [Stacks Project, Tag 04N0] over the finite type points of `U`, and
needs the reach map of `∐_u g_u` to be flat, locally of finite presentation and locally
quasi-finite because each `h_u` is.  This file proves that, in the form it is needed: for a
family `k_i : V_i ⟶ U'` of open immersions covering `U'` and factorizations `k_i ≫ g = q_i`,
any property of morphisms of schemes which is Zariski-local at the source holds for the reach
map of `g` as soon as it holds for the reach map of each `q_i`.  The coproduct case is the
family of coproduct injections.

The point is that the reach map of `q_i` is the restriction of the reach map of `g` to an open
of its source: `V_i ×_{q_i, U, t} R` is the fibre product of `U' ×_{g, U, t} R` with `V_i` over
`U'`, by the pasting isomorphism
`CategoryTheory.Limits.pullbackRightPullbackFstIso`, and the projection to `U' ×_{g, U, t} R` is
a base change of `k_i`, hence an open immersion; the images of those projections cover because
the images of the `k_i` do.

## Main definitions

This file introduces no definitions.

## Main results

* `AlgebraicGeometry.reachMap_mem_of_jointly_covering`: the reach map of `g` has a property
  local at the source as soon as the reach maps of a jointly covering family of opens of `U'`
  over `U` do.
* `AlgebraicGeometry.exists_comp_reachMap_eq`: the reach map of `k ≫ g` factors through the
  reach map of `g`.
* `AlgebraicGeometry.exists_section_comp_reachMap_eq`: the image of the reach map of `g`
  contains the image of `g`.
* `AlgebraicGeometry.Scheme.Opens.eq_top_of_finiteTypePoints_subset`: an open containing every
  finite type point is everything.
* `AlgebraicGeometry.surjective_reachMap_of_jointly_covering`: the reach map of `g` is
  surjective when the reach maps of the members jointly cover the object scheme.
* `AlgebraicGeometry.reachMap_sigmaDesc_mem`: the reach map of `∐_i g_i` has such a property as
  soon as the reach maps of the `g_i` do.

## Implementation notes

The reach map is written out as `pullback.snd g G.target.left ≫ G.source.left`, with the fibre
product of schemes rather than the one of `Over S`; that is the form in which
`AlgebraicGeometry.exists_affine_slice_locallyQuasiFinite`, the library's
[Stacks Project, Tag 04N0], states the three properties of `h_u`, so the hypotheses of the
results here are literally its conclusions.  The transfer to the fibre product of `Over S`,
which `Stacks.Groupoids.GroupoidScheme.QuasiFiniteRefinement` asks for, is
`AlgebraicGeometry.overFibreProduct_isPullback` and is independent of this file.

The covering hypothesis is stated as surjectivity on points rather than as a supremum of opens,
because that is what `AlgebraicGeometry.Scheme.Cover.mkOfCovers` consumes and what the
coproduct supplies.

## References

* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
* [Stacks Project, Tag 04N0](https://stacks.math.columbia.edu/tag/04N0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- **The reach map of a jointly covering family.**  Let `G` be a groupoid scheme, let
`g : U' ⟶ U` be a morphism to its object scheme, and let `k i : V i ⟶ U'` be a family of open
immersions which is surjective on points, with `k i ≫ g = q i`.  Then any property of
morphisms of schemes which is Zariski-local at the source holds for the reach map of `g` as
soon as it holds for the reach map of every `q i`. -/
theorem reachMap_mem_of_jointly_covering {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtSource P] (G : GroupoidScheme S) {U' : Scheme.{u}}
    (g : U' ⟶ G.objects.left) {I : Type u} {V : I → Scheme.{u}}
    (k : ∀ i, V i ⟶ U') (q : ∀ i, V i ⟶ G.objects.left)
    (hk : ∀ i, IsOpenImmersion (k i)) (hcomp : ∀ i, k i ≫ g = q i)
    (hcov : ∀ x : U', ∃ (i : I) (y : V i), (k i) y = x)
    (hP : ∀ i, P (pullback.snd (q i) G.target.left ≫ G.source.left)) :
    P (pullback.snd g G.target.left ≫ G.source.left) := by
  have hoi : ∀ i, IsOpenImmersion
      (pullback.fst (pullback.fst g G.target.left) (k i)) := fun i =>
    have := hk i
    inferInstance
  have hcovers : ∀ x : ↥(pullback g G.target.left), ∃ (i : I)
      (y : ↥(pullback (pullback.fst g G.target.left) (k i))),
      (pullback.fst (pullback.fst g G.target.left) (k i)) y = x := by
    intro x
    obtain ⟨i, y, hy⟩ := hcov ((pullback.fst g G.target.left) x)
    have _ := hk i
    have hmem : x ∈ Set.range (pullback.fst (pullback.fst g G.target.left) (k i)) := by
      rw [IsOpenImmersion.range_pullbackFst (k i) (pullback.fst g G.target.left)]
      exact ⟨y, hy⟩
    obtain ⟨z, hz⟩ := hmem
    exact ⟨i, z, hz⟩
  refine IsZariskiLocalAtSource.of_openCover
    (Scheme.Cover.mkOfCovers I
      (fun i => pullback (pullback.fst g G.target.left) (k i))
      (fun i => pullback.fst (pullback.fst g G.target.left) (k i)) hcovers hoi) ?_
  have hP' : ∀ i, P (pullback.snd (k i ≫ g) G.target.left ≫ G.source.left) := by
    intro i
    rw [hcomp i]
    exact hP i
  intro i
  have _ := hk i
  show P (pullback.fst (pullback.fst g G.target.left) (k i) ≫
    pullback.snd g G.target.left ≫ G.source.left)
  have hsnd : (pullbackSymmetry (pullback.fst g G.target.left) (k i) ≪≫
        pullbackRightPullbackFstIso g G.target.left (k i)).hom ≫
        pullback.snd (k i ≫ g) G.target.left =
      pullback.fst (pullback.fst g G.target.left) (k i) ≫ pullback.snd g G.target.left := by
    rw [Iso.trans_hom, Category.assoc, pullbackRightPullbackFstIso_hom_snd, ← Category.assoc,
      pullbackSymmetry_hom_comp_snd]
  have hfac : pullback.fst (pullback.fst g G.target.left) (k i) ≫
      pullback.snd g G.target.left ≫ G.source.left =
        (pullbackSymmetry (pullback.fst g G.target.left) (k i) ≪≫
          pullbackRightPullbackFstIso g G.target.left (k i)).hom ≫
          pullback.snd (k i ≫ g) G.target.left ≫ G.source.left := by
    rw [← Category.assoc, ← hsnd, Category.assoc]
  rw [hfac, P.cancel_left_of_respectsIso]
  exact hP' i

/-- **The reach map of a factor.**  If `q = k ≫ g` then the reach map of `q` factors through
the reach map of `g`: an arrow of `R` whose target lifts along `q` has its target lifting along
`g`, with the same source.

This is the inclusion of the piece `V ×_{q, U, t} R` into `U' ×_{g, U, t} R` on which
`AlgebraicGeometry.reachMap_mem_of_jointly_covering` reads the reach map of `g`, written without
any comparison isomorphism. -/
theorem exists_comp_reachMap_eq (G : GroupoidScheme S) {U' V : Scheme.{u}}
    (g : U' ⟶ G.objects.left) (k : V ⟶ U') (q : V ⟶ G.objects.left) (hcomp : k ≫ g = q) :
    ∃ c : pullback q G.target.left ⟶ pullback g G.target.left,
      c ≫ pullback.snd g G.target.left ≫ G.source.left =
        pullback.snd q G.target.left ≫ G.source.left := by
  refine ⟨pullback.lift (pullback.fst q G.target.left ≫ k)
    (pullback.snd q G.target.left) ?_, ?_⟩
  · rw [Category.assoc, hcomp]
    exact pullback.condition
  · rw [← Category.assoc, pullback.lift_snd]

/-- **The reach map of `g` reaches everything `g` does.**  The identity section provides a
section `U' ⟶ U' ×_{g, U, t} R` of the reach map over `g`: an object of `U'` is the source of
the identity arrow at its image, whose target lifts along `g` tautologically.

So the image of the reach map of `g` contains the image of `g`, which is how Step 3 of the proof
of [Stacks Project, Tag 0489] knows that the image of `h_u` contains the point `u`. -/
theorem exists_section_comp_reachMap_eq (G : GroupoidScheme S) {U' : Scheme.{u}}
    (g : U' ⟶ G.objects.left) :
    ∃ e : U' ⟶ pullback g G.target.left,
      e ≫ pullback.snd g G.target.left ≫ G.source.left = g := by
  refine ⟨pullback.lift (𝟙 U') (g ≫ G.identity.left) ?_, ?_⟩
  · rw [Category.id_comp, Category.assoc, identity_left_comp_target_left G, Category.comp_id]
  · rw [← Category.assoc, pullback.lift_snd, Category.assoc,
      identity_left_comp_source_left G, Category.comp_id]

/-- An open of a scheme containing every finite type point is the whole scheme.

Its complement is closed, hence locally closed, so if it were nonempty it would contain a
finite type point by [Stacks Project, Tag 02J4]
(`AlgebraicGeometry.inter_finiteTypePoints_nonempty`).  This is the second half of the
surjectivity argument of Step 3 of the proof of [Stacks Project, Tag 0489]: the open union of
the images of the reach maps `h_u` contains every finite type point `u` of `U`, hence is `U`. -/
theorem Scheme.Opens.eq_top_of_finiteTypePoints_subset {X : Scheme.{u}} {W : X.Opens}
    (h : X.finiteTypePoints ⊆ (W : Set X)) : W = ⊤ := by
  by_contra hW
  have hne : ((W : Set X)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro htop
    exact hW (TopologicalSpace.Opens.ext (by simpa using htop))
  obtain ⟨x, hxc, hxft⟩ :=
    inter_finiteTypePoints_nonempty (W.2.isClosed_compl).isLocallyClosed hne
  exact hxc (h hxft)

/-- **The reach map of a family is surjective when the reach maps of its members jointly are.**
If `k i ≫ g = q i` and every point of the object scheme is in the image of the reach map of
some `q i`, then the reach map of `g` is surjective.

In Step 3 of the proof of [Stacks Project, Tag 0489] this is how the reach map of
`∐_u g_u` is seen to be an fppf covering: it is flat and locally of finite presentation by
`AlgebraicGeometry.reachMap_sigmaDesc_mem`, and surjective because the image of each `h_u` is
open and contains `u`, and the finite type points of `U` are dense. -/
theorem surjective_reachMap_of_jointly_covering (G : GroupoidScheme S) {U' : Scheme.{u}}
    (g : U' ⟶ G.objects.left) {I : Type u} {V : I → Scheme.{u}}
    (k : ∀ i, V i ⟶ U') (q : ∀ i, V i ⟶ G.objects.left) (hcomp : ∀ i, k i ≫ g = q i)
    (hcov : ∀ x : ↥G.objects.left, ∃ (i : I) (y : ↥(pullback (q i) G.target.left)),
      (pullback.snd (q i) G.target.left ≫ G.source.left) y = x) :
    Surjective (pullback.snd g G.target.left ≫ G.source.left) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨i, y, hy⟩ := hcov x
  obtain ⟨c, hc⟩ := exists_comp_reachMap_eq G g (k i) (q i) (hcomp i)
  refine ⟨c y, ?_⟩
  rw [← hy, ← hc]
  rfl

/-- **The reach map of a coproduct.**  Let `G` be a groupoid scheme and let
`q i : V i ⟶ U` be a family of morphisms to its object scheme.  Then any property of morphisms
of schemes which is Zariski-local at the source holds for the reach map of
`∐ q : ∐ V ⟶ U` as soon as it holds for the reach map of every `q i`.

This is Step 3 of the proof of [Stacks Project, Tag 0489] for the three properties it needs,
flatness, local finite presentation and local quasi-finiteness, each of which is Zariski-local
at the source. -/
theorem reachMap_sigmaDesc_mem {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtSource P] (G : GroupoidScheme S) {I : Type u} {V : I → Scheme.{u}}
    [Small.{u} I] (q : ∀ i, V i ⟶ G.objects.left)
    (hP : ∀ i, P (pullback.snd (q i) G.target.left ≫ G.source.left)) :
    P (pullback.snd (Sigma.desc q) G.target.left ≫ G.source.left) :=
  reachMap_mem_of_jointly_covering G (Sigma.desc q) (fun i => Sigma.ι V i) q
    (fun _ => inferInstance) (fun i => Sigma.ι_desc _ _) (fun x => by
      obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk V).surjective x
      exact ⟨i, y, (sigmaMk_mk V i y).symm.trans hy⟩) hP

end AlgebraicGeometry

end
