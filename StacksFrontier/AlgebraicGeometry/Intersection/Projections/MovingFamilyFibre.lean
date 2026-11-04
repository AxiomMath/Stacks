module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.LineThroughIdentityDomain
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyGerm
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyPoint
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyProportional
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySet
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyTranslate

/-!
# The fibre of the family `C'` over a closed point of the line is the translate

Clause (2) of Tag 0B1T says that the fibre of the family `C'` over the point `0` of the line is
`C` itself, and clause (4) is about the fibre over `∞`. Both are instances of one identity: for
every closed point `λ` of the line, cut out by a functional `μ` on the corank-two quotient and so
naming the endomorphism `g = lineEnd μ`, the fibre of `C'` over `λ` is the translate `r_g(C)`,

`σ_λ⁻¹(C') = r_g(C)`.

Both sides are closed subsets of `𝐏(V)` — the left because `C'` is closed, the right because `C`
is closed and contained in the domain `U(g)` — so the identity may be checked on closed points,
where the characterisation of the closed points of the graph turns it into the statement that the
functional cutting out a point of the fibre is proportional to `f_x ∘ g` for a closed point `x` of
`C`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.movingFibre_movingFamilySet`: **the fibre of `C'`
  over a closed point of the line is the translate of `C` by the endomorphism that point names.**
* `AlgebraicGeometry.ProjectiveSpaceOfModule.movingFibre_movingFamilySet_nonempty`: in
  particular the fibre is nonempty when `C` is, which is clause (1).

## Implementation notes

The two inclusions are proved on closed points and transported by
`Set.subset_of_isClosed_of_closedPoints_subset`, the triple product being a Jacobson space. In
the direction `C' ⊆ r_g(C)` a closed point of the fibre is lifted to a *closed* point of the
graph, which is possible because the relevant subset of the graph is closed and nonempty; its
three projections are then closed points, and
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_movingGraph_iff_of_linearFunctionalPoint` applies.
In the direction `r_g(C) ⊆ C'` the closed point of `C` whose translate is the given point is
produced by
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isClosed_mem_endProjection_eq`, and the point
of the graph above the resulting triple is
`AlgebraicGeometry.ProjectiveSpaceOfModule.prodPoint`.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
  (L : Submodule k (ParameterModule k V)) [FiniteDimensional k V]
  [Nontrivial (lineSpace k V L)] [Nontrivial V]

/-- A functional point in the domain of `g` has a functional whose composite with `g` is nonzero. -/
private theorem comp_ne_zero_of_mem_endDomain {K W : Type u} [Field K] [AddCommGroup W]
    [Module K W] {f : Module.Dual K W} (hf : f ≠ 0) (g : W →ₗ[K] W)
    {x : projectiveSpaceOfModule K W} (hx : x = linearFunctionalPoint K W f hf)
    (hxg : x ∈ (endDomain K W g : Set (projectiveSpaceOfModule K W))) : f ∘ₗ g ≠ 0 := by
  intro hz
  refine (notMem_endDomain_linearFunctionalPoint_iff K W f hf g).mpr hz ?_
  rw [← hx]
  exact hxg

/-- A closed point of the fibre of `C'` over a closed point of the line lies in the translate. -/
private theorem mem_endProjectionImage_of_mem_movingFibre {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) {C : Set (projectiveSpaceOfModule k V)}
    (hC : IsClosed C) {mu : Module.Dual k (lineSpace k V L)} (hmu : mu ≠ 0)
    (hCg : C ⊆ (endDomain k V (lineEnd k V L mu) : Set (projectiveSpaceOfModule k V)))
    {y : projectiveSpaceOfModule k V}
    (hy : IsClosed ({y} : Set (projectiveSpaceOfModule k V)))
    (hymem : y ∈ movingFibre k V L (linearFunctionalPoint k (lineSpace k V L) mu hmu)
      (linearFunctionalPoint_isClosed k (lineSpace k V L) mu hmu)
      (movingFamilySet k V L b C)) :
    y ∈ endProjectionImage k V (lineEnd k V L mu) C := by
  set lam := linearFunctionalPoint k (lineSpace k V L) mu hmu with hlamdef
  set hlam := linearFunctionalPoint_isClosed k (lineSpace k V L) mu hmu with hlamc
  set g := lineEnd k V L mu with hg
  -- the closed nonempty subset of the graph lying over `σ_λ(y)`
  have hclosedsec : IsClosed ({(lineSection k V L lam hlam).base y} :
      Set (movingAmbient k V L)) := isClosed_lineSection_base k V L lam hlam hy
  set W : Set (movingProd k V L) := movingGraph k V L b ∩ (prSource k V L).base ⁻¹' C ∩
    (prAmbient k V L).base ⁻¹' {(lineSection k V L lam hlam).base y} with hW
  have hWclosed : IsClosed W :=
    ((isClosed_movingGraph k V L b).inter (hC.preimage (prSource k V L).continuous)).inter
      (hclosedsec.preimage (prAmbient k V L).continuous)
  have hWne : W.Nonempty := by
    obtain ⟨t, ht, htC, hteq⟩ := (mem_movingFibre_movingFamilySet_iff k V L b C lam hlam y).mp hymem
    exact ⟨t, ⟨ht, htC⟩, hteq⟩
  obtain ⟨t, ⟨⟨htG, htC⟩, htamb⟩, htc⟩ := exists_isClosed_singleton_mem hWne hWclosed
  -- the three projections of `t` are closed points
  have hsrcc : IsClosed ({(prSource k V L).base t} : Set (projectiveSpaceOfModule k V)) :=
    isClosed_singleton_image_of_isClosed_singleton (prSource k V L) (movingProdToSpec k V L)
      (projectiveSpaceOfModuleToSpec k V)
      (pullback.condition (f := projectiveSpaceOfModuleToSpec k V)
        (g := movingAmbientToSpec k V L)) t htc
  have hlineeq : (prLine k V L).base t = lam := by
    change (ambLine k V L).base ((prAmbient k V L).base t) = lam
    rw [htamb]
    exact ambLine_lineSection k V L lam hlam y
  have htargeteq : (prTarget k V L).base t = y := by
    change (ambPoint k V L).base ((prAmbient k V L).base t) = y
    rw [htamb]
    exact ambPoint_lineSection k V L lam hlam y
  -- the three functionals
  obtain ⟨fx, hfx, hxdef⟩ := exists_eq_linearFunctionalPoint k V ((prSource k V L).base t) hsrcc
  obtain ⟨fy, hfy, hydef⟩ := exists_eq_linearFunctionalPoint k V y hy
  -- the source point lies in `U(g)`, so `fx ∘ g ≠ 0`
  have hxg : (prSource k V L).base t ∈
      (endDomain k V g : Set (projectiveSpaceOfModule k V)) := hCg htC
  have hfxg : fx ∘ₗ g ≠ 0 := comp_ne_zero_of_mem_endDomain hfx g hxdef hxg
  -- the determinant condition
  have hdet := (mem_movingGraph_iff_of_linearFunctionalPoint k V L b t fx hfx hxdef mu hmu
    (hlineeq.trans hlamdef) fy hfy (htargeteq.trans hydef)).mp htG
  -- so `y` is the translate of the source point
  have hprop : linearFunctionalPoint k V fy hfy = linearFunctionalPoint k V (fx ∘ₗ g) hfxg :=
    linearFunctionalPoint_eq_of_minors_eq k V hfy hfxg fun u v => hdet u v
  refine ⟨⟨(prSource k V L).base t, hxg⟩, ?_, ?_⟩
  · exact htC
  · rw [endProjection_eq_linearFunctionalPoint k V g ⟨(prSource k V L).base t, hxg⟩ fx hfx hfxg
      hxdef, ← hprop, ← hydef]

/-- A closed point of the translate lies in the fibre of `C'`. -/
private theorem mem_movingFibre_of_mem_endProjectionImage {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) {C : Set (projectiveSpaceOfModule k V)}
    (hC : IsClosed C) {mu : Module.Dual k (lineSpace k V L)} (hmu : mu ≠ 0)
    (hCg : C ⊆ (endDomain k V (lineEnd k V L mu) : Set (projectiveSpaceOfModule k V)))
    {y : projectiveSpaceOfModule k V}
    (hy : IsClosed ({y} : Set (projectiveSpaceOfModule k V)))
    (hymem : y ∈ endProjectionImage k V (lineEnd k V L mu) C) :
    y ∈ movingFibre k V L (linearFunctionalPoint k (lineSpace k V L) mu hmu)
      (linearFunctionalPoint_isClosed k (lineSpace k V L) mu hmu)
      (movingFamilySet k V L b C) := by
  obtain ⟨x, w, hxC, hxc, hwx, hwy⟩ :=
    exists_isClosed_mem_endProjection_eq k V (lineEnd k V L mu) hC hCg hy hymem
  obtain ⟨fx, hfx, hxdef⟩ := exists_eq_linearFunctionalPoint k V x hxc
  obtain ⟨fy, hfy, hydef⟩ := exists_eq_linearFunctionalPoint k V y hy
  have hxg : x ∈ (endDomain k V (lineEnd k V L mu) : Set (projectiveSpaceOfModule k V)) := hCg hxC
  have hfxg : fx ∘ₗ lineEnd k V L mu ≠ 0 :=
    comp_ne_zero_of_mem_endDomain hfx _ hxdef hxg
  have hyval : y = linearFunctionalPoint k V (fx ∘ₗ lineEnd k V L mu) hfxg := by
    rw [← hwy]
    exact endProjection_eq_linearFunctionalPoint k V (lineEnd k V L mu) w fx hfx hfxg
      (hwx.trans hxdef)
  have hdet : ∀ u v : V,
      fy u * fx (lineEnd k V L mu v) = fy v * fx (lineEnd k V L mu u) := by
    have hprop : linearFunctionalPoint k V fy hfy =
        linearFunctionalPoint k V (fx ∘ₗ lineEnd k V L mu) hfxg := by rw [← hydef, hyval]
    exact fun u v => minors_eq_of_linearFunctionalPoint_eq k V hfy hfxg hprop u v
  refine (mem_movingFibre_movingFamilySet_iff k V L b C
    (linearFunctionalPoint k (lineSpace k V L) mu hmu)
    (linearFunctionalPoint_isClosed k (lineSpace k V L) mu hmu) y).mpr
    ⟨(prodPoint k V L x hxc (linearFunctionalPoint k (lineSpace k V L) mu hmu)
      (linearFunctionalPoint_isClosed k (lineSpace k V L) mu hmu) y hy).base
        (IsLocalRing.closedPoint k), ?_, ?_, ?_⟩
  · refine (mem_movingGraph_iff_of_linearFunctionalPoint k V L b _ fx hfx ?_ mu hmu ?_ fy hfy
      ?_).mpr hdet
    · exact (prSource_prodPoint k V L x hxc (linearFunctionalPoint k (lineSpace k V L) mu hmu)
        (linearFunctionalPoint_isClosed k (lineSpace k V L) mu hmu) y hy
        (IsLocalRing.closedPoint k)).trans hxdef
    · exact prLine_prodPoint k V L x hxc (linearFunctionalPoint k (lineSpace k V L) mu hmu)
        (linearFunctionalPoint_isClosed k (lineSpace k V L) mu hmu) y hy
        (IsLocalRing.closedPoint k)
    · exact (prTarget_prodPoint k V L x hxc (linearFunctionalPoint k (lineSpace k V L) mu hmu)
        (linearFunctionalPoint_isClosed k (lineSpace k V L) mu hmu) y hy
        (IsLocalRing.closedPoint k)).trans hydef
  · have h : (prSource k V L).base ((prodPoint k V L x hxc
        (linearFunctionalPoint k (lineSpace k V L) mu hmu)
        (linearFunctionalPoint_isClosed k (lineSpace k V L) mu hmu) y hy).base
          (IsLocalRing.closedPoint k)) = x :=
      prSource_prodPoint k V L x hxc (linearFunctionalPoint k (lineSpace k V L) mu hmu)
        (linearFunctionalPoint_isClosed k (lineSpace k V L) mu hmu) y hy
        (IsLocalRing.closedPoint k)
    rw [h]
    exact hxC
  · exact prAmbient_prodPoint k V L x hxc (linearFunctionalPoint k (lineSpace k V L) mu hmu)
      (linearFunctionalPoint_isClosed k (lineSpace k V L) mu hmu) y hy
      (IsLocalRing.closedPoint k)

/-- **The fibre of `C'` over a closed point of the line is the translate of `C` by the
endomorphism that point names.** -/
public theorem movingFibre_movingFamilySet {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) {C : Set (projectiveSpaceOfModule k V)}
    (hC : IsClosed C) {mu : Module.Dual k (lineSpace k V L)} (hmu : mu ≠ 0)
    (hCg : C ⊆ (endDomain k V (lineEnd k V L mu) : Set (projectiveSpaceOfModule k V))) :
    movingFibre k V L (linearFunctionalPoint k (lineSpace k V L) mu hmu)
        (linearFunctionalPoint_isClosed k (lineSpace k V L) mu hmu)
        (movingFamilySet k V L b C) =
      endProjectionImage k V (lineEnd k V L mu) C := by
  refine Set.Subset.antisymm ?_ ?_
  · refine Set.subset_of_isClosed_of_closedPoints_subset
      (isClosed_movingFibre k V L _ _ (isClosed_movingFamilySet k V L b hC))
      (isClosed_endProjectionImage k V (lineEnd k V L mu) hC hCg) fun y hymem hyc => ?_
    exact mem_endProjectionImage_of_mem_movingFibre k V L b hC hmu hCg hyc hymem
  · refine Set.subset_of_isClosed_of_closedPoints_subset
      (isClosed_endProjectionImage k V (lineEnd k V L mu) hC hCg)
      (isClosed_movingFibre k V L _ _ (isClosed_movingFamilySet k V L b hC))
      fun y hymem hyc => ?_
    exact mem_movingFibre_of_mem_endProjectionImage k V L b hC hmu hCg hyc hymem

/-- **The fibre of `C'` over a closed point of the line is nonempty** when `C` is: the translate
of a nonempty subset of the domain of definition is nonempty. This is what clause (1) of Tag
0B1T consumes. -/
public theorem movingFibre_movingFamilySet_nonempty {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) {C : Set (projectiveSpaceOfModule k V)}
    (hC : IsClosed C) (hCne : C.Nonempty) {mu : Module.Dual k (lineSpace k V L)} (hmu : mu ≠ 0)
    (hCg : C ⊆ (endDomain k V (lineEnd k V L mu) : Set (projectiveSpaceOfModule k V))) :
    (movingFibre k V L (linearFunctionalPoint k (lineSpace k V L) mu hmu)
      (linearFunctionalPoint_isClosed k (lineSpace k V L) mu hmu)
      (movingFamilySet k V L b C)).Nonempty := by
  rw [movingFibre_movingFamilySet k V L b hC hmu hCg]
  exact endProjectionImage_nonempty k V hCne hCg

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
