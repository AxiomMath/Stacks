module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute

/-!
# Characterizations of irreducible schemes

An irreducible scheme can be recognized either from a suitably intersecting affine open cover or
by checking all of its nonempty affine opens.

## Main results

* `AlgebraicGeometry.Scheme.irreducibleSpace_tfae` gives two affine-open criteria equivalent to
  irreducibility of a scheme.

## Implementation notes

An affine open covering is expressed as a family of open subsets satisfying `IsOpenCover`, with
affineness recorded separately. Irreducibility of an open subset means irreducibility of its
subtype topology.

## References

* [Stacks Project, Tag 01OM](https://stacks.math.columbia.edu/tag/01OM)
-/

@[expose] public section

open TopologicalSpace
open Set

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme all of whose nonempty affine opens are irreducible is preirreducible. -/
theorem preirreducibleSpace_of_forall_isAffineOpen (X : Scheme.{u})
    (hU : ∀ U : X.Opens, IsAffineOpen U → Nonempty U → IrreducibleSpace U) :
    PreirreducibleSpace X := by
  refine .of_forall_nonempty_inter fun U V hUo hVo ⟨x, hx⟩ ⟨y, hy⟩ ↦ ?_
  obtain ⟨R, f, hf, hx, hsub⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (U := ⟨U, hUo⟩) hx
  obtain ⟨S, g, hg, hy, hsub'⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (U := ⟨V, hVo⟩) hy
  let W : X.Opens := f.opensRange
  let Z : X.Opens := g.opensRange
  by_contra hdis
  have hd : Disjoint W Z := Opens.coe_disjoint.mp
    (Set.disjoint_left.mpr fun z hzW hzZ ↦ hdis ⟨z, hsub hzW, hsub' hzZ⟩)
  let T : X.Opens := W ⊔ Z
  have hTaff : IsAffineOpen T :=
    (isAffineOpen_opensRange f).sup_of_disjoint (isAffineOpen_opensRange g) hd
  have hxT : x ∈ T := Or.inl hx
  have hyT : y ∈ T := Or.inr hy
  have : IrreducibleSpace T := hU T hTaff ⟨⟨x, hxT⟩⟩
  let W' : Opens T := Opens.comap ⟨_, continuous_subtype_val⟩ W
  let Z' : Opens T := Opens.comap ⟨_, continuous_subtype_val⟩ Z
  obtain ⟨q, hqW, hqZ⟩ :=
    nonempty_preirreducible_inter W'.isOpen Z'.isOpen ⟨⟨x, hxT⟩, hx⟩ ⟨⟨y, hyT⟩, hy⟩
  exact hdis ⟨q.1, hsub hqW, hsub' hqZ⟩

/-- A nonempty scheme all of whose nonempty affine opens are irreducible is irreducible. -/
theorem irreducibleSpace_of_forall_isAffineOpen (X : Scheme.{u}) [Nonempty X]
    (hU : ∀ U : X.Opens, IsAffineOpen U → Nonempty U → IrreducibleSpace U) :
    IrreducibleSpace X :=
  { toPreirreducibleSpace := preirreducibleSpace_of_forall_isAffineOpen X hU
    toNonempty := ‹_› }

/-- A scheme is irreducible if and only if it is nonempty and every nonempty affine open is
irreducible. -/
theorem irreducibleSpace_iff_forall_isAffineOpen (X : Scheme.{u}) :
    IrreducibleSpace X ↔
      Nonempty X ∧ ∀ U : X.Opens, IsAffineOpen U → Nonempty U → IrreducibleSpace U := by
  refine ⟨fun h ↦ ⟨h.toNonempty, fun U _ hne ↦ ?_⟩, fun ⟨_, hU⟩ ↦
    irreducibleSpace_of_forall_isAffineOpen X hU⟩
  have : Nonempty {x // x ∈ (U : Set X)} := hne
  exact U.isOpen.isOpenEmbedding_subtypeVal.irreducibleSpace

/-- A scheme is irreducible if and only if it has a nonempty affine open cover by irreducible
opens whose members meet pairwise. -/
theorem irreducibleSpace_iff_exists_isAffineOpen_cover (X : Scheme.{u}) :
    IrreducibleSpace X ↔
      ∃ (ι : Type u) (U : ι → X.Opens), Nonempty ι ∧ IsOpenCover U ∧
        (∀ i, IsAffineOpen (U i)) ∧ (∀ i, IrreducibleSpace (U i)) ∧
        ∀ i j, Set.Nonempty ((U i : Set X) ∩ (U j : Set X)) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · let C := X.affineOpenCover
    let U (i : {j : C.I₀ // Nonempty ((C.f j).opensRange)}) : X.Opens := (C.f i.1).opensRange
    have hcov : IsOpenCover U := .mk <| eq_top_iff.mpr fun x _ ↦
      Opens.mem_iSup.mpr ⟨⟨C.idx x, ⟨⟨x, C.covers x⟩⟩⟩, C.covers x⟩
    have (k : C.I₀) : IsOpenImmersion (C.f k) := C.map_prop k
    refine ⟨_, U,
      ⟨⟨C.idx h.toNonempty.some, ⟨⟨h.toNonempty.some, C.covers h.toNonempty.some⟩⟩⟩⟩,
      hcov, fun i ↦ isAffineOpen_opensRange (C.f i.1), fun i ↦ ?_, fun i j ↦
        nonempty_preirreducible_inter (C.f i.1).opensRange.2 (C.f j.1).opensRange.2
          ⟨i.2.some.1, i.2.some.2⟩ ⟨j.2.some.1, j.2.some.2⟩⟩
    have : Nonempty {x // x ∈ ((C.f i.1).opensRange : Set X)} := i.2
    exact (C.f i.1).opensRange.isOpen.isOpenEmbedding_subtypeVal.irreducibleSpace
  · rintro ⟨ι, U, ⟨i⟩, hcov, -, hirr, hinter⟩
    exact
      { toPreirreducibleSpace := .of_isOpenCover
          (fun i j _ hd ↦ Set.not_disjoint_iff_nonempty_inter.mpr (hinter i j)
            (by simpa only [← Opens.coe_disjoint] using hd)) hcov
          (fun i ↦ (hirr i).toPreirreducibleSpace)
        toNonempty := ⟨(hirr i).toNonempty.some.val⟩ }

/-- **Stacks Project, Tag 01OM.** A scheme is irreducible if and only if it
has a nonempty affine open cover by irreducible opens whose members meet
pairwise, if and only if it is nonempty and every nonempty affine open is
irreducible. -/
@[stacks 01OM]
theorem irreducibleSpace_tfae (X : Scheme.{u}) :
    List.TFAE [
      IrreducibleSpace X,
      ∃ (ι : Type u) (U : ι → X.Opens),
        Nonempty ι ∧
          IsOpenCover U ∧
          (∀ i, IsAffineOpen (U i)) ∧
          (∀ i, IrreducibleSpace (U i)) ∧
          ∀ i j, Set.Nonempty ((U i : Set X) ∩ (U j : Set X)),
      Nonempty X ∧
        ∀ U : X.Opens, IsAffineOpen U → Nonempty U → IrreducibleSpace U] := by
  tfae_have 1 ↔ 2 := irreducibleSpace_iff_exists_isAffineOpen_cover X
  tfae_have 1 ↔ 3 := irreducibleSpace_iff_forall_isAffineOpen X
  tfae_finish

end AlgebraicGeometry.Scheme

end
