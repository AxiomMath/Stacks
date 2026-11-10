module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.LineThroughIdentityDomain
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyFibreRange
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyGerm
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyPoint
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyProportional
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySet

/-!
# The family `C'` of the Moving Lemma is irreducible

Clause (3) of Tag 0B1T compares the family `C'` with the constant family of `C`, and for that
comparison `C'` has to be an irreducible closed subset of `ℓ ×_k 𝐏(V)`. This file proves that it
is, for `C` an irreducible closed subvariety lying in the domain of definition of every
projective transformation the line names.

The argument runs on the part

`G = Γ ∩ pr_source⁻¹(C)`

of the graph of the family lying over `C`, of which `C'` is the image. Besides the projection
forgetting the source point there is a second projection of the triple product to `ℓ ×_k 𝐏(V)`,
the one keeping the line coordinate and the *source* point. It is proper, and its image on `G` is
the constant family `ℓ × C`, which is irreducible. Moreover a closed point of `G` is determined
by its image under that projection: the line coordinate and the source point determine the target
point, the target point of a point of the graph being the translate of the source point by the
endomorphism the line coordinate names. So `G` is irreducible by the criterion
`AlgebraicGeometry.isIrreducible_of_isClosedMap_of_unique_closedPoint`, and `C'`, its continuous
image under the projection forgetting the source point, is irreducible too.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.movingGraphOver`: the part `G` of the graph of the
  family lying over `C`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.srcLineMap`: the projection of the triple product to
  `ℓ ×_k 𝐏(V)` keeping the line coordinate and the source point.

## Main results

* `AlgebraicGeometry.eq_of_isClosed_singleton_of_proj_eq`: a closed point of a fibre product over
  `Spec k` is determined by its two projections.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isProper_srcLineMap`: the projection keeping the
  line coordinate and the source point is proper.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.image_movingGraphOver`: its image on `G` is the
  constant family.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isIrreducible_movingGraphOver`: `G` is irreducible.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isIrreducible_movingFamilySet`: **the family `C'` is
  irreducible.**

## Implementation notes

The uniqueness of a closed point of `G` over a point of the constant family is where the two
descriptions of a point of the graph meet. A closed point `t` of the triple product has all three
projections closed, hence cut out by nonzero functionals `f_x`, `μ` and `f_y`, and
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_movingGraph_iff_of_linearFunctionalPoint` turns
membership of the graph into the vanishing of the `2 × 2` minors of `f_y` against `f_x ∘ g`. So
`f_y` and `f_x ∘ g` cut out the same point by
`AlgebraicGeometry.ProjectiveSpaceOfModule.linearFunctionalPoint_eq_of_minors_eq`, which pins the
target point down once the source point and the line coordinate are given. That `f_x ∘ g` is
nonzero is exactly the hypothesis that `C` lies in the domain of definition `U(g)`, read through
`AlgebraicGeometry.ProjectiveSpaceOfModule.notMem_endDomain_linearFunctionalPoint_iff`.

Three agreeing projections are then turned into an equality of points of the triple product in
two steps. The ambient coordinates agree because both lie over the same point of the line, where
the section `σ_λ` undoes the projection to `𝐏(V)`
(`AlgebraicGeometry.ProjectiveSpaceOfModule.lineSection_ambPoint_of_ambLine_eq`); and a point of
a fibre product over `Spec k` which is closed is determined by its two projections, since it is a
`k`-point and a `k`-point of a fibre product is a pair of `k`-points
(`AlgebraicGeometry.eq_of_isClosed_singleton_of_proj_eq`).

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- **A closed point of a fibre product over `Spec k` is determined by its two projections.**
Over an algebraically closed field a closed point of a scheme locally of finite type is a
`k`-point, so each of the two points is a morphism `τ : Spec k ⟶ X ×_k Y` splitting the structure
morphism. The two composites with a projection are `k`-points of that factor agreeing at the
closed point of `Spec k`, hence equal; so `τ` and `τ'` have the same two projections and agree,
and evaluating at the closed point identifies the original points. -/
public theorem eq_of_isClosed_singleton_of_proj_eq {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    {z z' : ↥(pullback f g)} (hz : IsClosed ({z} : Set ↥(pullback f g)))
    (hz' : IsClosed ({z'} : Set ↥(pullback f g)))
    (h1 : (pullback.fst f g).base z = (pullback.fst f g).base z')
    (h2 : (pullback.snd f g).base z = (pullback.snd f g).base z') : z = z' := by
  have hlft : LocallyOfFiniteType (pullback.fst f g ≫ f) := inferInstance
  obtain ⟨τ, hτ, hτval⟩ : ∃ τ : Spec (.of k) ⟶ pullback f g,
      τ ≫ (pullback.fst f g ≫ f) = 𝟙 _ ∧ τ.base (IsLocalRing.closedPoint k) = z :=
    ⟨pointOfClosedPoint (pullback.fst f g ≫ f) z hz,
      pointOfClosedPoint_comp (pullback.fst f g ≫ f) z hz,
      pointOfClosedPoint_apply (pullback.fst f g ≫ f) z hz _⟩
  obtain ⟨τ', hτ', hτ'val⟩ : ∃ τ' : Spec (.of k) ⟶ pullback f g,
      τ' ≫ (pullback.fst f g ≫ f) = 𝟙 _ ∧ τ'.base (IsLocalRing.closedPoint k) = z' :=
    ⟨pointOfClosedPoint (pullback.fst f g ≫ f) z' hz',
      pointOfClosedPoint_comp (pullback.fst f g ≫ f) z' hz',
      pointOfClosedPoint_apply (pullback.fst f g ≫ f) z' hz' _⟩
  have hττ' : τ = τ' := by
    refine pullback.hom_ext ?_ ?_
    · refine ext_of_apply_closedPoint_eq f ?_ ?_ ?_
      · rw [Category.assoc]
        exact hτ
      · rw [Category.assoc]
        exact hτ'
      · change (pullback.fst f g).base (τ.base (IsLocalRing.closedPoint k)) =
          (pullback.fst f g).base (τ'.base (IsLocalRing.closedPoint k))
        rw [hτval, hτ'val]
        exact h1
    · refine ext_of_apply_closedPoint_eq g ?_ ?_ ?_
      · rw [Category.assoc, ← pullback.condition, ← Category.assoc]
        exact hτ
      · rw [Category.assoc, ← pullback.condition, ← Category.assoc]
        exact hτ'
      · change (pullback.snd f g).base (τ.base (IsLocalRing.closedPoint k)) =
          (pullback.snd f g).base (τ'.base (IsLocalRing.closedPoint k))
        rw [hτval, hτ'val]
        exact h2
  rw [← hτval, ← hτ'val, hττ']

namespace ProjectiveSpaceOfModule

variable (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
  (L : Submodule k (ParameterModule k V)) [FiniteDimensional k V]
  [Nontrivial (lineSpace k V L)] [Nontrivial V]

/-- The source point of a closed point of the triple product is a closed point of `𝐏(V)`. -/
private theorem isClosed_base_prSource (t : movingProd k V L)
    (ht : IsClosed ({t} : Set (movingProd k V L))) :
    IsClosed ({(prSource k V L).base t} : Set (projectiveSpaceOfModule k V)) :=
  isClosed_singleton_image_of_isClosed_singleton (prSource k V L) (movingProdToSpec k V L)
    (projectiveSpaceOfModuleToSpec k V) (prSource_comp_toSpec k V L) t ht

/-- The line coordinate of a closed point of the triple product is a closed point of the line. -/
private theorem isClosed_base_prLine (t : movingProd k V L)
    (ht : IsClosed ({t} : Set (movingProd k V L))) :
    IsClosed ({(prLine k V L).base t} : Set (movingLine k V L)) :=
  isClosed_singleton_image_of_isClosed_singleton (prLine k V L) (movingProdToSpec k V L)
    (movingLineToSpec k V L) (prLine_comp_toSpec k V L) t ht

/-- The target point of a closed point of the triple product is a closed point of `𝐏(V)`. -/
private theorem isClosed_base_prTarget (t : movingProd k V L)
    (ht : IsClosed ({t} : Set (movingProd k V L))) :
    IsClosed ({(prTarget k V L).base t} : Set (projectiveSpaceOfModule k V)) :=
  isClosed_singleton_image_of_isClosed_singleton (prTarget k V L) (movingProdToSpec k V L)
    (projectiveSpaceOfModuleToSpec k V) (prTarget_comp_toSpec k V L) t ht

/-- **The part of the graph of the family lying over `C`**, whose image under the projection
forgetting the source point is the family `C'`. -/
public def movingGraphOver {ι : Type*} [Fintype ι] (b : Module.Basis ι k (lineSpace k V L))
    (C : Set (projectiveSpaceOfModule k V)) : Set (movingProd k V L) :=
  movingGraph k V L b ∩ (prSource k V L).base ⁻¹' C

omit [IsAlgClosed k] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- A point of the triple product lies in that part of the graph exactly when it lies on the
graph and its source point lies in `C`. -/
public theorem mem_movingGraphOver_iff {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) (C : Set (projectiveSpaceOfModule k V))
    (t : movingProd k V L) :
    t ∈ movingGraphOver k V L b C ↔
      t ∈ movingGraph k V L b ∧ (prSource k V L).base t ∈ C :=
  Iff.rfl

omit [IsAlgClosed k] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- That part of the graph is closed: the graph is closed and the preimage of a closed `C` is
closed. -/
public theorem isClosed_movingGraphOver {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) {C : Set (projectiveSpaceOfModule k V)}
    (hC : IsClosed C) : IsClosed (movingGraphOver k V L b C) :=
  (isClosed_movingGraph k V L b).inter (hC.preimage (prSource k V L).continuous)

omit [IsAlgClosed k] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- The family `C'` is the image of that part of the graph under the projection forgetting the
source point. -/
public theorem movingFamilySet_eq_image {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) (C : Set (projectiveSpaceOfModule k V)) :
    movingFamilySet k V L b C = (prAmbient k V L).base '' movingGraphOver k V L b C :=
  rfl

/-- **The projection of the triple product to `ℓ ×_k 𝐏(V)` keeping the line coordinate and the
source point.** It is the second projection of the triple product to `ℓ ×_k 𝐏(V)`, the one not
forgetting the source point, and it is what carries the part of the graph over `C` onto the
constant family. -/
public def srcLineMap : movingProd k V L ⟶ movingAmbient k V L :=
  pullback.lift (prLine k V L) (prSource k V L) (by
    change (prAmbient k V L ≫ ambLine k V L) ≫ movingLineToSpec k V L =
      prSource k V L ≫ projectiveSpaceOfModuleToSpec k V
    rw [Category.assoc]
    exact (pullback.condition (f := projectiveSpaceOfModuleToSpec k V)
      (g := movingAmbientToSpec k V L)).symm)

omit [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- The line coordinate of that projection is the line coordinate of the triple product. -/
@[reassoc (attr := simp)]
public theorem srcLineMap_comp_ambLine :
    srcLineMap k V L ≫ ambLine k V L = prLine k V L :=
  pullback.lift_fst _ _ _

omit [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- The `𝐏(V)` coordinate of that projection is the source point of the triple product. -/
@[reassoc (attr := simp)]
public theorem srcLineMap_comp_ambPoint :
    srcLineMap k V L ≫ ambPoint k V L = prSource k V L :=
  pullback.lift_snd _ _ _

omit [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- That projection is a morphism over the ground field. -/
public theorem srcLineMap_comp_movingAmbientToSpec :
    srcLineMap k V L ≫ movingAmbientToSpec k V L = movingProdToSpec k V L :=
  calc srcLineMap k V L ≫ movingAmbientToSpec k V L
      = (srcLineMap k V L ≫ ambLine k V L) ≫ movingLineToSpec k V L :=
        (Category.assoc (srcLineMap k V L) (ambLine k V L) (movingLineToSpec k V L)).symm
    _ = prLine k V L ≫ movingLineToSpec k V L := by rw [srcLineMap_comp_ambLine]
    _ = movingProdToSpec k V L := prLine_comp_toSpec k V L

/-- **That projection is proper.** Its composite with the structure morphism of `ℓ ×_k 𝐏(V)` is
the structure morphism of the triple product, which is proper, and the structure morphism of
`ℓ ×_k 𝐏(V)` is separated. -/
public instance isProper_srcLineMap : IsProper (srcLineMap k V L) := by
  have h1 : IsProper (srcLineMap k V L ≫ movingAmbientToSpec k V L) := by
    rw [srcLineMap_comp_movingAmbientToSpec]
    exact isProper_movingProdToSpec k V L
  have h2 : IsSeparated (movingAmbientToSpec k V L) := by
    have := isProper_movingAmbientToSpec k V L
    infer_instance
  exact IsProper.of_comp _ (movingAmbientToSpec k V L)

omit [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- The line coordinate of the image of a point of the triple product. -/
public theorem ambLine_srcLineMap (t : movingProd k V L) :
    (ambLine k V L).base ((srcLineMap k V L).base t) = (prLine k V L).base t :=
  congrArg (fun m : movingProd k V L ⟶ movingLine k V L => m.base t)
    (srcLineMap_comp_ambLine k V L)

omit [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- The `𝐏(V)` coordinate of the image of a point of the triple product. -/
public theorem ambPoint_srcLineMap (t : movingProd k V L) :
    (ambPoint k V L).base ((srcLineMap k V L).base t) = (prSource k V L).base t :=
  congrArg (fun m : movingProd k V L ⟶ projectiveSpaceOfModule k V => m.base t)
    (srcLineMap_comp_ambPoint k V L)

/-- The image of a closed point of the triple product under that projection is a closed point of
`ℓ ×_k 𝐏(V)`. -/
private theorem isClosed_base_srcLineMap (t : movingProd k V L)
    (ht : IsClosed ({t} : Set (movingProd k V L))) :
    IsClosed ({(srcLineMap k V L).base t} : Set (movingAmbient k V L)) :=
  isClosed_singleton_image_of_isClosed_singleton (srcLineMap k V L) (movingProdToSpec k V L)
    (movingAmbientToSpec k V L) (srcLineMap_comp_movingAmbientToSpec k V L) t ht

/-- **Every closed point of the constant family is the image of a point of the graph over `C`.**
Write the line coordinate of the point as the point cut out by a functional `μ` on the
corank-two quotient and its `𝐏(V)` coordinate as the point cut out by `f_x`. The subvariety
lying in the domain of definition of the endomorphism `g = lineEnd μ` makes `f_x ∘ g` nonzero, so
it cuts out a point `y` of `𝐏(V)`; the point of the triple product over the triple
`(x, λ, y)` lies on the graph, since the minors of `f_x ∘ g` against itself vanish, and its
source point is `x`. Both it and the given point lie over `λ` with `𝐏(V)` coordinate `x`, so the
section at `λ` identifies them. -/
private theorem exists_mem_movingGraphOver {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) {C : Set (projectiveSpaceOfModule k V)}
    (hCg : ∀ mu : Module.Dual k (lineSpace k V L), mu ≠ 0 →
      C ⊆ (endDomain k V (lineEnd k V L mu) : Set (projectiveSpaceOfModule k V)))
    {z : movingAmbient k V L} (hz : z ∈ constantFamily k V L C)
    (hzc : IsClosed ({z} : Set (movingAmbient k V L))) :
    ∃ t ∈ movingGraphOver k V L b C, (srcLineMap k V L).base t = z := by
  have hxC : (ambPoint k V L).base z ∈ C := hz
  have hlamc : IsClosed ({(ambLine k V L).base z} : Set (movingLine k V L)) :=
    isClosed_singleton_image_of_isClosed_singleton (ambLine k V L) (movingAmbientToSpec k V L)
      (movingLineToSpec k V L) rfl z hzc
  have hxc : IsClosed ({(ambPoint k V L).base z} : Set (projectiveSpaceOfModule k V)) :=
    isClosed_singleton_image_of_isClosed_singleton (ambPoint k V L) (movingAmbientToSpec k V L)
      (projectiveSpaceOfModuleToSpec k V)
      (pullback.condition (f := movingLineToSpec k V L)
        (g := projectiveSpaceOfModuleToSpec k V)).symm z hzc
  obtain ⟨mu, hmu, hmudef⟩ :=
    exists_eq_linearFunctionalPoint k (lineSpace k V L) ((ambLine k V L).base z) hlamc
  obtain ⟨fx, hfx, hxdef⟩ :=
    exists_eq_linearFunctionalPoint k V ((ambPoint k V L).base z) hxc
  have hxg : (ambPoint k V L).base z ∈
      (endDomain k V (lineEnd k V L mu) : Set (projectiveSpaceOfModule k V)) := hCg mu hmu hxC
  have hfxg : fx ∘ₗ lineEnd k V L mu ≠ 0 := by
    intro h0
    refine (notMem_endDomain_linearFunctionalPoint_iff k V fx hfx (lineEnd k V L mu)).mpr h0 ?_
    rw [← hxdef]
    exact hxg
  have hyc : IsClosed ({linearFunctionalPoint k V (fx ∘ₗ lineEnd k V L mu) hfxg} :
      Set (projectiveSpaceOfModule k V)) :=
    linearFunctionalPoint_isClosed k V (fx ∘ₗ lineEnd k V L mu) hfxg
  refine ⟨(prodPoint k V L ((ambPoint k V L).base z) hxc ((ambLine k V L).base z) hlamc
    (linearFunctionalPoint k V (fx ∘ₗ lineEnd k V L mu) hfxg) hyc).base
      (IsLocalRing.closedPoint k), ⟨?_, ?_⟩, ?_⟩
  · refine (mem_movingGraph_iff_of_linearFunctionalPoint k V L b _ fx hfx ?_ mu hmu ?_
      (fx ∘ₗ lineEnd k V L mu) hfxg ?_).mpr fun u v => ?_
    · exact (prSource_prodPoint k V L ((ambPoint k V L).base z) hxc ((ambLine k V L).base z)
        hlamc _ hyc (IsLocalRing.closedPoint k)).trans hxdef
    · exact (prLine_prodPoint k V L ((ambPoint k V L).base z) hxc ((ambLine k V L).base z)
        hlamc _ hyc (IsLocalRing.closedPoint k)).trans hmudef
    · exact prTarget_prodPoint k V L ((ambPoint k V L).base z) hxc ((ambLine k V L).base z)
        hlamc _ hyc (IsLocalRing.closedPoint k)
    · change fx (lineEnd k V L mu u) * fx (lineEnd k V L mu v) =
        fx (lineEnd k V L mu v) * fx (lineEnd k V L mu u)
      ring
  · have h : (prSource k V L).base ((prodPoint k V L ((ambPoint k V L).base z) hxc
        ((ambLine k V L).base z) hlamc
        (linearFunctionalPoint k V (fx ∘ₗ lineEnd k V L mu) hfxg) hyc).base
          (IsLocalRing.closedPoint k)) = (ambPoint k V L).base z :=
      prSource_prodPoint k V L ((ambPoint k V L).base z) hxc ((ambLine k V L).base z) hlamc _
        hyc (IsLocalRing.closedPoint k)
    refine Set.mem_preimage.mpr ?_
    rw [h]
    exact hxC
  · have hamb : (ambLine k V L).base ((srcLineMap k V L).base ((prodPoint k V L
        ((ambPoint k V L).base z) hxc ((ambLine k V L).base z) hlamc
        (linearFunctionalPoint k V (fx ∘ₗ lineEnd k V L mu) hfxg) hyc).base
          (IsLocalRing.closedPoint k))) = (ambLine k V L).base z := by
      rw [ambLine_srcLineMap]
      exact prLine_prodPoint k V L ((ambPoint k V L).base z) hxc ((ambLine k V L).base z) hlamc
        _ hyc (IsLocalRing.closedPoint k)
    have hpt : (ambPoint k V L).base ((srcLineMap k V L).base ((prodPoint k V L
        ((ambPoint k V L).base z) hxc ((ambLine k V L).base z) hlamc
        (linearFunctionalPoint k V (fx ∘ₗ lineEnd k V L mu) hfxg) hyc).base
          (IsLocalRing.closedPoint k))) = (ambPoint k V L).base z := by
      rw [ambPoint_srcLineMap]
      exact prSource_prodPoint k V L ((ambPoint k V L).base z) hxc ((ambLine k V L).base z)
        hlamc _ hyc (IsLocalRing.closedPoint k)
    have h1 := lineSection_ambPoint_of_ambLine_eq k V L ((ambLine k V L).base z) hlamc hamb
    have h2 := lineSection_ambPoint_of_ambLine_eq k V L ((ambLine k V L).base z) hlamc
      (x := z) rfl
    rw [hpt] at h1
    exact h1.symm.trans h2

/-- **The image of the part of the graph over `C` is the constant family.** The inclusion `⊆` is
immediate, the `𝐏(V)` coordinate of the image of a point of the graph being its source point. The
reverse inclusion is checked on closed points, both sides being closed — the image because the
projection is proper — and there it is the construction of a point of the graph over a prescribed
line coordinate and source point. -/
public theorem image_movingGraphOver {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) {C : Set (projectiveSpaceOfModule k V)}
    (hC : IsClosed C) (_hCirr : IsIrreducible C)
    (hCg : ∀ mu : Module.Dual k (lineSpace k V L), mu ≠ 0 →
      C ⊆ (endDomain k V (lineEnd k V L mu) : Set (projectiveSpaceOfModule k V))) :
    (srcLineMap k V L).base '' movingGraphOver k V L b C = constantFamily k V L C := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨t, htN, rfl⟩
    change (ambPoint k V L).base ((srcLineMap k V L).base t) ∈ C
    rw [ambPoint_srcLineMap]
    exact ((mem_movingGraphOver_iff k V L b C t).mp htN).2
  · refine Set.subset_of_isClosed_of_closedPoints_subset
      (isClosed_constantFamily k V L C hC)
      ((srcLineMap k V L).isClosedMap _ (isClosed_movingGraphOver k V L b hC))
      fun z hz hzc => ?_
    obtain ⟨t, htN, hteq⟩ := exists_mem_movingGraphOver k V L b hCg hz hzc
    exact ⟨t, htN, hteq⟩

/-- **The part of the graph over `C` is irreducible.** Its image under the projection keeping the
line coordinate and the source point is the constant family, which is irreducible, that
projection is proper, hence a closed map, and two closed points of the part with the same image
agree: they have the same line coordinate and the same source point, hence the same target point
by the determinant characterisation of the graph, hence the same ambient coordinate by the
section at the common line coordinate, and a closed point of the triple product is determined by
its source point and its ambient coordinate. -/
public theorem isIrreducible_movingGraphOver {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) {C : Set (projectiveSpaceOfModule k V)}
    (hC : IsClosed C) (hCirr : IsIrreducible C) (hCne : C.Nonempty)
    (hCg : ∀ mu : Module.Dual k (lineSpace k V L), mu ≠ 0 →
      C ⊆ (endDomain k V (lineEnd k V L mu) : Set (projectiveSpaceOfModule k V))) :
    IsIrreducible (movingGraphOver k V L b C) := by
  -- a nonzero functional on the corank-two quotient, from the given basis
  obtain ⟨i⟩ := b.index_nonempty
  have hmu : b.coord i ≠ 0 := by
    intro h
    have h1 : b.coord i (b i) = 1 := by simp
    rw [h, LinearMap.zero_apply] at h1
    exact zero_ne_one h1
  -- the part of the graph is nonempty: over a closed point of `C` there is a closed point of the
  -- constant family, and over that a point of the graph
  have hNne : (movingGraphOver k V L b C).Nonempty := by
    obtain ⟨x, hxC, hxc⟩ := exists_isClosed_singleton_mem hCne hC
    have hzc : IsClosed ({(lineSection k V L
        (linearFunctionalPoint k (lineSpace k V L) (b.coord i) hmu)
        (linearFunctionalPoint_isClosed k (lineSpace k V L) (b.coord i) hmu)).base x} :
          Set (movingAmbient k V L)) :=
      isClosed_lineSection_base k V L _ _ hxc
    have hz : (lineSection k V L (linearFunctionalPoint k (lineSpace k V L) (b.coord i) hmu)
        (linearFunctionalPoint_isClosed k (lineSpace k V L) (b.coord i) hmu)).base x ∈
          constantFamily k V L C := by
      change (ambPoint k V L).base ((lineSection k V L _ _).base x) ∈ C
      rw [ambPoint_lineSection]
      exact hxC
    obtain ⟨t, htN, -⟩ := exists_mem_movingGraphOver k V L b hCg hz hzc
    exact ⟨t, htN⟩
  have himg : IsIrreducible ((srcLineMap k V L).base '' movingGraphOver k V L b C) := by
    rw [image_movingGraphOver k V L b hC hCirr hCg]
    exact isIrreducible_constantFamily k V L C hC hCirr
  refine isIrreducible_of_isClosedMap_of_unique_closedPoint (srcLineMap k V L).isClosedMap
    (isClosed_movingGraphOver k V L b hC) hNne himg
    (fun t _ htc => isClosed_base_srcLineMap k V L t htc) ?_ (srcLineMap k V L).continuous
  intro t htN t' ht'N htc ht'c hteq
  -- the line coordinates and the source points agree
  have hline : (prLine k V L).base t = (prLine k V L).base t' := by
    rw [← ambLine_srcLineMap, ← ambLine_srcLineMap, hteq]
  have hsrc : (prSource k V L).base t = (prSource k V L).base t' := by
    rw [← ambPoint_srcLineMap, ← ambPoint_srcLineMap, hteq]
  -- the functionals cutting out the common line coordinate and source point
  have hlinec := isClosed_base_prLine k V L t htc
  obtain ⟨mu, hmu', hmudef⟩ :=
    exists_eq_linearFunctionalPoint k (lineSpace k V L) ((prLine k V L).base t) hlinec
  obtain ⟨fx, hfx, hxdef⟩ :=
    exists_eq_linearFunctionalPoint k V ((prSource k V L).base t)
      (isClosed_base_prSource k V L t htc)
  have hxg : (prSource k V L).base t ∈
      (endDomain k V (lineEnd k V L mu) : Set (projectiveSpaceOfModule k V)) :=
    hCg mu hmu' ((mem_movingGraphOver_iff k V L b C t).mp htN).2
  have hfxg : fx ∘ₗ lineEnd k V L mu ≠ 0 := by
    intro h0
    refine (notMem_endDomain_linearFunctionalPoint_iff k V fx hfx (lineEnd k V L mu)).mpr h0 ?_
    rw [← hxdef]
    exact hxg
  -- the two target points are both the point cut out by `f_x ∘ g`
  obtain ⟨fy, hfy, hydef⟩ :=
    exists_eq_linearFunctionalPoint k V ((prTarget k V L).base t)
      (isClosed_base_prTarget k V L t htc)
  obtain ⟨fy', hfy', hy'def⟩ :=
    exists_eq_linearFunctionalPoint k V ((prTarget k V L).base t')
      (isClosed_base_prTarget k V L t' ht'c)
  have hdet := (mem_movingGraph_iff_of_linearFunctionalPoint k V L b t fx hfx hxdef mu hmu'
    hmudef fy hfy hydef).mp ((mem_movingGraphOver_iff k V L b C t).mp htN).1
  have hdet' := (mem_movingGraph_iff_of_linearFunctionalPoint k V L b t' fx hfx
    (hsrc.symm.trans hxdef) mu hmu' (hline.symm.trans hmudef) fy' hfy'
    hy'def).mp ((mem_movingGraphOver_iff k V L b C t').mp ht'N).1
  have htgt : (prTarget k V L).base t = (prTarget k V L).base t' :=
    (hydef.trans (linearFunctionalPoint_eq_of_minors_eq k V hfy hfxg fun u v => hdet u v)).trans
      (hy'def.trans
        (linearFunctionalPoint_eq_of_minors_eq k V hfy' hfxg fun u v => hdet' u v)).symm
  -- so the ambient coordinates agree, the section at the common line coordinate undoing the
  -- projection to `𝐏(V)` there
  have hamb : (prAmbient k V L).base t = (prAmbient k V L).base t' := by
    have h1 := lineSection_ambPoint_of_ambLine_eq k V L ((prLine k V L).base t) hlinec
      (x := (prAmbient k V L).base t) rfl
    have h2 := lineSection_ambPoint_of_ambLine_eq k V L ((prLine k V L).base t) hlinec
      (x := (prAmbient k V L).base t') hline.symm
    have h3 : (lineSection k V L ((prLine k V L).base t) hlinec).base
        ((ambPoint k V L).base ((prAmbient k V L).base t)) =
      (lineSection k V L ((prLine k V L).base t) hlinec).base
        ((ambPoint k V L).base ((prAmbient k V L).base t')) := congrArg _ htgt
    rw [h1, h2] at h3
    exact h3
  exact eq_of_isClosed_singleton_of_proj_eq (projectiveSpaceOfModuleToSpec k V)
    (movingAmbientToSpec k V L) htc ht'c hsrc hamb

/-- **The family `C'` of the Moving Lemma is irreducible**, being the continuous image of the
irreducible part of the graph lying over `C`. -/
public theorem isIrreducible_movingFamilySet {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) {C : Set (projectiveSpaceOfModule k V)}
    (hC : IsClosed C) (hCirr : IsIrreducible C) (hCne : C.Nonempty)
    (hCg : ∀ mu : Module.Dual k (lineSpace k V L), mu ≠ 0 →
      C ⊆ (endDomain k V (lineEnd k V L mu) : Set (projectiveSpaceOfModule k V))) :
    IsIrreducible (movingFamilySet k V L b C) := by
  rw [movingFamilySet_eq_image]
  exact (isIrreducible_movingGraphOver k V L b hC hCirr hCne hCg).image _
    (prAmbient k V L).continuous.continuousOn

end ProjectiveSpaceOfModule

end AlgebraicGeometry

end
