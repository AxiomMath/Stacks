module
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.EqualityLocus

/-!
# The open locus where two sections of an étale sheaf agree

Let `F` be a sheaf on the small étale site of a scheme `X`, let `W` be an object of that site and
let `a b` be two sections of `F` over `W`. The points of `W` near which `a` and `b` agree — in
the image of some morphism `V ⟶ W` of the site along which their restrictions coincide — form an
open subscheme of `W`, the **equality locus**
`Stacks.EtaleCohomology.smallEtaleEqLocusUnconditional F a b`. It is open because a morphism of
the small étale site is étale, hence open.

This is [Stacks, Tag 09XM](https://stacks.math.columbia.edu/tag/09XM)'s open equality locus for
sections over an arbitrary object of the site; `Stacks.EtaleCohomology.globalSectionEqOpen` is
the version for global sections, read in `X` rather than in the final object.

The equality locus behaves like an equality relation: it is everything for `a = a`, symmetric,
transitive, compatible with restriction along morphisms of the site, and it is everything only if
`a = b`. Transitivity and compatibility with restriction are where the fibre product over `W` of
two objects of the site is needed.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleOverPullback` — the fibre product over an object `W` of the
  small étale site of two morphisms into `W`, as an object of the site, with its projections.
* `Stacks.EtaleCohomology.smallEtaleEqLocusUnconditional` — the open of `W` over which two
  sections agree.

## Main results

* `Stacks.EtaleCohomology.range_subset_smallEtaleEqLocus_general` — the image of a morphism along
  which the sections agree lies in the equality locus.
* `Stacks.EtaleCohomology.preimage_smallEtaleEqLocus` — the equality locus of the restrictions
  along `h : V ⟶ W` is the preimage of the equality locus.
* `Stacks.EtaleCohomology.smallEtaleEqLocus_self`, `smallEtaleEqLocus_comm`,
  `smallEtaleEqLocus_trans` — reflexivity, symmetry and transitivity.
* `Stacks.EtaleCohomology.eq_of_smallEtaleEqLocus_eq_top` — sections whose equality locus is
  everything are equal.

## References

* [Stacks Project, Tag 09XM](https://stacks.math.columbia.edu/tag/09XM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace

universe w u

namespace Stacks.EtaleCohomology

variable {X : Scheme.{u}}

section OverPullback

variable {V V' W : X.Etale} (g : V ⟶ W) (h : V' ⟶ W)

/-- The fibre product `V ×_W V'` of two morphisms of the small étale site of `X` into `W`, as an
object of that site: its structure morphism is the second projection followed by that of `V'`. -/
public def smallEtaleOverPullback : X.Etale :=
  letI : Etale (V'.hom : V'.left ⟶ X) := V'.prop
  MorphismProperty.Over.mk ⊤ (pullback.snd g.left h.left ≫ (V'.hom : V'.left ⟶ X))
    inferInstance

/-- The first projection of `V ×_W V'`. -/
public def smallEtaleOverPullbackFst : smallEtaleOverPullback g h ⟶ V :=
  MorphismProperty.Over.homMk (pullback.fst g.left h.left)
    (by
      change pullback.fst g.left h.left ≫ (V.hom : V.left ⟶ X) =
        pullback.snd g.left h.left ≫ (V'.hom : V'.left ⟶ X)
      rw [← MorphismProperty.Over.w g, ← MorphismProperty.Over.w h, pullback.condition_assoc])
    trivial

/-- The second projection of `V ×_W V'`. -/
public def smallEtaleOverPullbackSnd : smallEtaleOverPullback g h ⟶ V' :=
  MorphismProperty.Over.homMk (pullback.snd g.left h.left) rfl trivial

/-- The underlying morphism of schemes of the first projection of `V ×_W V'` is `pullback.fst`. -/
@[simp]
public theorem smallEtaleOverPullbackFst_left :
    (smallEtaleOverPullbackFst g h).left = pullback.fst g.left h.left := rfl

/-- The underlying morphism of schemes of the second projection of `V ×_W V'` is
`pullback.snd`. -/
@[simp]
public theorem smallEtaleOverPullbackSnd_left :
    (smallEtaleOverPullbackSnd g h).left = pullback.snd g.left h.left := rfl

/-- The square formed by the two projections of `V ×_W V'` and `g`, `h` commutes. -/
public theorem smallEtaleOverPullback_condition :
    smallEtaleOverPullbackFst g h ≫ g = smallEtaleOverPullbackSnd g h ≫ h :=
  MorphismProperty.Over.Hom.ext pullback.condition

/-- The image of the second projection of `V ×_W V'` is the preimage of the image of `g`. -/
public theorem range_smallEtaleOverPullbackSnd :
    Set.range (smallEtaleOverPullbackSnd g h).left.base =
      h.left.base ⁻¹' Set.range g.left.base :=
  Scheme.Pullback.range_snd g.left h.left

end OverPullback

variable (F : Sheaf (Scheme.smallEtaleTopology X) (Type w))

/-- The **equality locus** of two sections of `F` over `W`: the union of the images of the
morphisms of the small étale site into `W` along which the two sections agree. It is an open of
`W`, a morphism of the site being étale and hence open. -/
public def smallEtaleEqLocusUnconditional {W : X.Etale} (a b : F.obj.obj (op W)) : W.left.Opens :=
  ⨆ p : {p : (V : X.Etale) × (V ⟶ W) // F.obj.map p.2.op a = F.obj.map p.2.op b},
    ⟨Set.range p.1.2.left.base, (Scheme.Hom.isOpenMap _).isOpen_range⟩

variable {F}

/-- A point lies in the equality locus exactly when it is in the image of a morphism of the site
along which the sections agree. -/
public theorem mem_smallEtaleEqLocus_iff {W : X.Etale} {a b : F.obj.obj (op W)} (x : W.left) :
    x ∈ smallEtaleEqLocusUnconditional F a b ↔
      ∃ (V : X.Etale) (g : V ⟶ W), F.obj.map g.op a = F.obj.map g.op b ∧
        x ∈ Set.range g.left.base := by
  refine ⟨fun hx ↦ ?_, fun ⟨V, g, hg, hx⟩ ↦ ?_⟩
  · obtain ⟨p, hp⟩ := Opens.mem_iSup.1 hx
    exact ⟨p.1.1, p.1.2, p.2, hp⟩
  · exact Opens.mem_iSup.2 ⟨⟨⟨V, g⟩, hg⟩, hx⟩

/-- The image of a morphism along which the sections agree lies in the equality locus. -/
public theorem range_subset_smallEtaleEqLocus_general {V W : X.Etale} {a b : F.obj.obj (op W)}
    (g : V ⟶ W) (hg : F.obj.map g.op a = F.obj.map g.op b) :
    Set.range g.left.base ⊆ smallEtaleEqLocusUnconditional F a b := fun _ hx ↦
  (mem_smallEtaleEqLocus_iff _).2 ⟨V, g, hg, hx⟩

/-- A section agrees with itself everywhere. -/
public theorem smallEtaleEqLocus_self {W : X.Etale} (a : F.obj.obj (op W)) :
    smallEtaleEqLocusUnconditional F a a = ⊤ :=
  top_le_iff.1 fun x _ ↦ range_subset_smallEtaleEqLocus_general (𝟙 W) rfl ⟨x, rfl⟩

/-- The equality locus is symmetric. -/
public theorem smallEtaleEqLocus_comm {W : X.Etale} (a b : F.obj.obj (op W)) :
    smallEtaleEqLocusUnconditional F a b = smallEtaleEqLocusUnconditional F b a := by
  ext x
  simp only [SetLike.mem_coe, mem_smallEtaleEqLocus_iff]
  exact ⟨fun ⟨V, g, hg, hx⟩ ↦ ⟨V, g, hg.symm, hx⟩, fun ⟨V, g, hg, hx⟩ ↦ ⟨V, g, hg.symm, hx⟩⟩

/-- Restriction along a composite is iterated restriction. -/
private theorem map_comp_op_apply {V V' W : X.Etale} (g' : V' ⟶ V) (g : V ⟶ W)
    (a : F.obj.obj (op W)) :
    F.obj.map (g' ≫ g).op a = F.obj.map g'.op (F.obj.map g.op a) :=
  F.obj.map_comp_apply g.op g'.op a

/-- **Restriction of the equality locus.** Along a morphism `h : V ⟶ W` of the site, the equality
locus of the restrictions is the preimage of the equality locus.

A point of `V` over a point of `W` hit by an agreeing `g : V' ⟶ W` is hit by the second
projection of `V' ×_W V`, along which the restrictions agree; conversely an agreeing morphism into
`V` composes with `h` to an agreeing morphism into `W`. -/
public theorem preimage_smallEtaleEqLocus {V W : X.Etale} (h : V ⟶ W) (a b : F.obj.obj (op W)) :
    h.left.base ⁻¹' (smallEtaleEqLocusUnconditional F a b : Set W.left) =
      smallEtaleEqLocusUnconditional F (F.obj.map h.op a) (F.obj.map h.op b) := by
  ext x
  simp only [Set.mem_preimage, SetLike.mem_coe, mem_smallEtaleEqLocus_iff]
  constructor
  · rintro ⟨V', g, hg, hx⟩
    refine ⟨smallEtaleOverPullback g h, smallEtaleOverPullbackSnd g h, ?_, ?_⟩
    · rw [← map_comp_op_apply, ← map_comp_op_apply, ← smallEtaleOverPullback_condition,
        map_comp_op_apply, map_comp_op_apply, hg]
    · rwa [range_smallEtaleOverPullbackSnd]
  · rintro ⟨V', g, hg, y, rfl⟩
    exact ⟨V', g ≫ h, by rw [map_comp_op_apply, map_comp_op_apply, hg],
      y, Scheme.Hom.comp_apply g.left h.left y⟩

/-- The equality locus is transitive. -/
public theorem smallEtaleEqLocus_trans {W : X.Etale} (a b c : F.obj.obj (op W)) :
    smallEtaleEqLocusUnconditional F a b ⊓ smallEtaleEqLocusUnconditional F b c ≤
      smallEtaleEqLocusUnconditional F a c := by
  rintro x ⟨hab, hbc⟩
  obtain ⟨V, g, hg, y, rfl⟩ := (mem_smallEtaleEqLocus_iff x).1 hab
  have hy : y ∈ smallEtaleEqLocusUnconditional F (F.obj.map g.op b) (F.obj.map g.op c) := by
    rwa [← SetLike.mem_coe, ← preimage_smallEtaleEqLocus]
  obtain ⟨V', g', hg', z, rfl⟩ := (mem_smallEtaleEqLocus_iff y).1 hy
  exact (mem_smallEtaleEqLocus_iff _).2 ⟨V', g' ≫ g,
    by rw [map_comp_op_apply, map_comp_op_apply, hg, hg'],
    z, Scheme.Hom.comp_apply g'.left g.left z⟩

/-- **The equality locus decides equality.** Two sections whose equality locus is all of `W` are
equal: the agreeing morphisms into `W` then form a covering family, and a sheaf is separated for
it. -/
public theorem eq_of_smallEtaleEqLocus_eq_top {W : X.Etale} {a b : F.obj.obj (op W)}
    (h : smallEtaleEqLocusUnconditional F a b = ⊤) : a = b := by
  let ι := {p : (V : X.Etale) × (V ⟶ W) // F.obj.map p.2.op a = F.obj.map p.2.op b}
  have hcov : Sieve.ofArrows (fun p : ι ↦ p.1.1) (fun p ↦ p.1.2) ∈
      Scheme.smallEtaleTopology X W := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun x ↦ ?_
    have hx : x ∈ smallEtaleEqLocusUnconditional F a b := h ▸ trivial
    obtain ⟨V, g, hg, hx⟩ := (mem_smallEtaleEqLocus_iff x).1 hx
    exact Set.mem_iUnion.2 ⟨⟨⟨V, g⟩, hg⟩, hx⟩
  refine (((isSheaf_iff_isSheaf_of_type _ _).1 F.property) _ hcov).isSeparatedFor.ext
    fun Y f hf ↦ ?_
  obtain ⟨p, k, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
  rw [map_comp_op_apply, map_comp_op_apply, p.2]

end Stacks.EtaleCohomology

end
