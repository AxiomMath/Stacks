module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.LineThroughIdentityDomain
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyTranslate
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionClassifyingRange
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionFibreDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionLocus

/-!
# The fibre of the incidence correspondence over a class covers the translate's intersection

Let `C, T` be closed subsets of `𝐏(V)` and let `[g]` be a closed point of the parameter space
`𝐏 = 𝐏((End V)ᵛ)` with `C ⊆ U(g)`. The incidence correspondence over `C × T`,

`W = {(x, y, [h]) : x ∈ C, y ∈ T, r_h(x) = y}`,

has for fibre over `[g]` the graph of `r_g` above `C ∩ r_g⁻¹(T)`, so the image of that fibre
under the target projection is the translate's intersection `r_g(C) ∩ T`. This file proves the
containment that is needed — every *closed* point of `r_g(C) ∩ T` is in the image of the fibre —
which is what turns a bound on the dimension of a general fibre of `W ⟶ 𝐏` into a bound on
`dim (r_g(C) ∩ T)`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.prodTwoPoint`: the `k`-point of `𝐏(V) ×_k 𝐏(V)`
  attached to two closed points of `𝐏(V)`, and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.prodTwoPair` the point of the product it lands on.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.corrPoint`: the point of the ambient triple product
  `𝐏(V) ×_k 𝐏(V) ×_k 𝐏` with prescribed source point, target point and class, all three closed.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.tpSource_corrPoint`,
  `…tpTarget_corrPoint`, `…tpPar_corrPoint`: the three projections of that point.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_transitionLocus_corrPoint`: it lies on the
  incidence correspondence exactly when the transition condition holds of the representatives.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_image_fibre_transitionVarietyToPar`: **every
  closed point of `r_g(C) ∩ T` is the image under the target projection of a point of the fibre
  of `W ⟶ 𝐏` over `[g]`.**

## Implementation notes

**Why a point of the product has to be built at all.** The three projections do not determine a
point of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏` as a set-theoretic triple; what is used instead is that over an
algebraically closed field a closed point is a `k`-point, and that the `k`-points of a fibre
product over `Spec k` are pairs of `k`-points, so
`CategoryTheory.Limits.pullback.lift` of two `AlgebraicGeometry.pointOfClosedPoint`s produces
one. The same bookkeeping for the product `ℓ ×_k 𝐏(V)` of the moving family is
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyPoint`, and the third
coordinate is put on by
`AlgebraicGeometry.ProjectiveSpaceOfModule.parFibreSection`, the section of the projection to
the parameter space over a closed point, rather than by a third `pullback.lift`.

**Closed points only.** The statement is about the closed points of `r_g(C) ∩ T` and not about
all of it, for two reasons: the incidence condition `r_h(x) = y` is read off the minor sections
of `𝒪(1,1,1)`, which can be evaluated only at a triple of closed points
(`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_transitionLocus_iff_of_linearFunctionalPoint`),
and a closed point of the translate is the image of a *closed* point of `C` only by
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isClosed_mem_endProjection_eq`. The passage to
the whole of `r_g(C) ∩ T` is done by the consumer, against the *closure* of the image of the
fibre, both sets being closed in a Jacobson space.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V]
  [Nontrivial (ParameterModule k V)]

/-- **The `k`-point of `𝐏(V) ×_k 𝐏(V)` attached to two closed points of `𝐏(V)`.** -/
public def prodTwoPoint (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (y : projectiveSpaceOfModule k V)
    (hy : IsClosed ({y} : Set (projectiveSpaceOfModule k V))) :
    Spec (.of k) ⟶ prodTwo k V :=
  pullback.lift (pointOfClosedPoint (projectiveSpaceOfModuleToSpec k V) x hx)
    (pointOfClosedPoint (projectiveSpaceOfModuleToSpec k V) y hy)
    (by rw [pointOfClosedPoint_comp, pointOfClosedPoint_comp])

/-- **The point of `𝐏(V) ×_k 𝐏(V)` attached to two closed points of `𝐏(V)`**: the underlying
point of `AlgebraicGeometry.ProjectiveSpaceOfModule.prodTwoPoint`. -/
public def prodTwoPair (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (y : projectiveSpaceOfModule k V)
    (hy : IsClosed ({y} : Set (projectiveSpaceOfModule k V))) : prodTwo k V :=
  (prodTwoPoint k V x hx y hy).base (IsLocalRing.closedPoint k)

omit [Nontrivial (ParameterModule k V)] in
/-- The first projection of `prodTwoPoint` is the `k`-point at `x`. -/
@[reassoc]
public theorem prodTwoPoint_comp_fst (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (y : projectiveSpaceOfModule k V)
    (hy : IsClosed ({y} : Set (projectiveSpaceOfModule k V))) :
    prodTwoPoint k V x hx y hy ≫
        pullback.fst (projectiveSpaceOfModuleToSpec k V)
          (projectiveSpaceOfModuleToSpec k V) =
      pointOfClosedPoint (projectiveSpaceOfModuleToSpec k V) x hx :=
  pullback.lift_fst _ _ _

omit [Nontrivial (ParameterModule k V)] in
/-- The second projection of `prodTwoPoint` is the `k`-point at `y`. -/
@[reassoc]
public theorem prodTwoPoint_comp_snd (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (y : projectiveSpaceOfModule k V)
    (hy : IsClosed ({y} : Set (projectiveSpaceOfModule k V))) :
    prodTwoPoint k V x hx y hy ≫
        pullback.snd (projectiveSpaceOfModuleToSpec k V)
          (projectiveSpaceOfModuleToSpec k V) =
      pointOfClosedPoint (projectiveSpaceOfModuleToSpec k V) y hy :=
  pullback.lift_snd _ _ _

omit [Nontrivial (ParameterModule k V)] in
/-- The first coordinate of that point is `x`. -/
public theorem fst_prodTwoPair (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (y : projectiveSpaceOfModule k V)
    (hy : IsClosed ({y} : Set (projectiveSpaceOfModule k V))) :
    (pullback.fst (projectiveSpaceOfModuleToSpec k V)
        (projectiveSpaceOfModuleToSpec k V)).base (prodTwoPair k V x hx y hy) = x := by
  rw [prodTwoPair]
  exact (congrArg (fun m : Spec (.of k) ⟶ projectiveSpaceOfModule k V =>
    m.base (IsLocalRing.closedPoint k)) (prodTwoPoint_comp_fst k V x hx y hy)).trans
    (pointOfClosedPoint_apply (projectiveSpaceOfModuleToSpec k V) x hx _)

omit [Nontrivial (ParameterModule k V)] in
/-- The second coordinate of that point is `y`. -/
public theorem snd_prodTwoPair (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (y : projectiveSpaceOfModule k V)
    (hy : IsClosed ({y} : Set (projectiveSpaceOfModule k V))) :
    (pullback.snd (projectiveSpaceOfModuleToSpec k V)
        (projectiveSpaceOfModuleToSpec k V)).base (prodTwoPair k V x hx y hy) = y := by
  rw [prodTwoPair]
  exact (congrArg (fun m : Spec (.of k) ⟶ projectiveSpaceOfModule k V =>
    m.base (IsLocalRing.closedPoint k)) (prodTwoPoint_comp_snd k V x hx y hy)).trans
    (pointOfClosedPoint_apply (projectiveSpaceOfModuleToSpec k V) y hy _)

/-- **The point of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏` with prescribed source, target and class.** The pair of
the first two is `AlgebraicGeometry.ProjectiveSpaceOfModule.prodTwoPair` and the class is put on
by the section of the projection to the parameter space over the closed point `q`. -/
public def corrPoint {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))))
    (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (y : projectiveSpaceOfModule k V)
    (hy : IsClosed ({y} : Set (projectiveSpaceOfModule k V))) : transitionProd k V :=
  (parFibreSection k V hq).base (prodTwoPair k V x hx y hy)

/-- The class of that point is `q`. -/
public theorem tpPar_corrPoint {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))))
    (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (y : projectiveSpaceOfModule k V)
    (hy : IsClosed ({y} : Set (projectiveSpaceOfModule k V))) :
    (tpPar k V).base (corrPoint k V hq x hx y hy) = q := by
  have h : corrPoint k V hq x hx y hy ∈ (tpPar k V).base ⁻¹' {q} := by
    rw [← range_parFibreSection k V hq]
    exact ⟨_, rfl⟩
  exact h

/-- The pair of the first two coordinates of that point is `prodTwoPair`. -/
public theorem tpFst_corrPoint {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))))
    (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (y : projectiveSpaceOfModule k V)
    (hy : IsClosed ({y} : Set (projectiveSpaceOfModule k V))) :
    (tpFst k V).base (corrPoint k V hq x hx y hy) = prodTwoPair k V x hx y hy := by
  change (tpFst k V).base ((parFibreSection k V hq).base (prodTwoPair k V x hx y hy)) =
    prodTwoPair k V x hx y hy
  have h := congrArg (fun m : prodTwo k V ⟶ prodTwo k V => m.base (prodTwoPair k V x hx y hy))
    (parFibreSection_comp_tpFst k V hq)
  simpa only [Scheme.Hom.comp_apply, Scheme.Hom.id_base, TopCat.id_app] using h

/-- The source point of that point is `x`. -/
public theorem tpSource_corrPoint {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))))
    (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (y : projectiveSpaceOfModule k V)
    (hy : IsClosed ({y} : Set (projectiveSpaceOfModule k V))) :
    (tpSource k V).base (corrPoint k V hq x hx y hy) = x := by
  change (pullback.fst (projectiveSpaceOfModuleToSpec k V)
    (projectiveSpaceOfModuleToSpec k V)).base ((tpFst k V).base _) = x
  rw [tpFst_corrPoint, fst_prodTwoPair]

/-- The target point of that point is `y`. -/
public theorem tpTarget_corrPoint {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))))
    (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (y : projectiveSpaceOfModule k V)
    (hy : IsClosed ({y} : Set (projectiveSpaceOfModule k V))) :
    (tpTarget k V).base (corrPoint k V hq x hx y hy) = y := by
  change (pullback.snd (projectiveSpaceOfModuleToSpec k V)
    (projectiveSpaceOfModuleToSpec k V)).base ((tpFst k V).base _) = y
  rw [tpFst_corrPoint, snd_prodTwoPair]

/-- **The point lies on the incidence correspondence exactly when the transition condition holds
of the representatives.** This is
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_transitionLocus_iff_of_linearFunctionalPoint` read
at `corrPoint`, whose three projections are the three given closed points by construction. -/
public theorem mem_transitionLocus_corrPoint
    {p : ClosedPoints k (ParameterModule k V)} {g : V →ₗ[k] V}
    (hgrep : RepresentsParameterPoint k V p g)
    (hq : IsClosed ({(p : projectiveSpaceOfModule k (ParameterModule k V))} :
      Set (projectiveSpaceOfModule k (ParameterModule k V))))
    (f : Module.Dual k V) (hf : f ≠ 0) (f' : Module.Dual k V) (hf' : f' ≠ 0) :
    corrPoint k V hq (linearFunctionalPoint k V f hf)
        (linearFunctionalPoint_isClosed k V f hf) (linearFunctionalPoint k V f' hf')
        (linearFunctionalPoint_isClosed k V f' hf') ∈ transitionLocus k V ↔
      f ∘ₗ g ∈ Submodule.span k {f'} := by
  obtain ⟨hg0, hgeq⟩ := hgrep
  refine mem_transitionLocus_iff_of_linearFunctionalPoint k V _ f hf
    (tpSource_corrPoint k V hq _ _ _ _) f' hf' (tpTarget_corrPoint k V hq _ _ _ _)
    (Module.Dual.eval k (V →ₗ[k] V) g) (eval_ne_zero k V hg0) ?_ g fun ψ => rfl
  rw [tpPar_corrPoint k V hq]
  exact val_eq_linearFunctionalPoint k V p g hg0 hgeq

/-- **Every closed point of the translate's intersection is covered by the fibre.** Let `C, T` be
closed subsets of `𝐏(V)`, let `[g]` be a closed point of the parameter space with `C ⊆ U(g)` and
let `z` be a closed point of `r_g(C) ∩ T`. Then `z` is the image under the target projection of a
point of the incidence correspondence over `C × T` lying over `[g]`.

The source point is produced by
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isClosed_mem_endProjection_eq`: a closed point
of the translate is the image of a closed point of `C`. -/
public theorem mem_image_fibre_transitionVarietyToPar
    (C T : Set (projectiveSpaceOfModule k V)) (hCc : IsClosed C) (hTc : IsClosed T)
    {p : ClosedPoints k (ParameterModule k V)}
    (hq : IsClosed ({(p : projectiveSpaceOfModule k (ParameterModule k V))} :
      Set (projectiveSpaceOfModule k (ParameterModule k V))))
    {g : V →ₗ[k] V} (hgrep : RepresentsParameterPoint k V p g)
    (hCg : C ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V)))
    {z : projectiveSpaceOfModule k V}
    (hz : IsClosed ({z} : Set (projectiveSpaceOfModule k V)))
    (hzim : z ∈ endProjectionImage k V g C) (hzT : z ∈ T) :
    z ∈ (transitionVarietyι k V C T hCc hTc ≫ tpTarget k V).base ''
      ((transitionVarietyToPar k V (prodOfClosedToProdTwo k V C T hCc hTc)).base ⁻¹'
        {(p : projectiveSpaceOfModule k (ParameterModule k V))}) := by
  obtain ⟨x, w, hxC, hxc, hwx, hwz⟩ :=
    exists_isClosed_mem_endProjection_eq k V g hCc hCg hz hzim
  obtain ⟨f, hf, hxf⟩ := exists_eq_linearFunctionalPoint k V x hxc
  obtain ⟨f', hf', hzf⟩ := exists_eq_linearFunctionalPoint k V z hz
  -- the transition condition at the two functionals
  have hfg : f ∘ₗ g ≠ 0 := by
    intro h
    refine (notMem_endDomain_linearFunctionalPoint_iff k V f hf g).mpr h ?_
    rw [← hxf]
    exact hCg hxC
  have hwval : (w.val : projectiveSpaceOfModule k V) = linearFunctionalPoint k V f hf := by
    rw [← hxf]
    exact hwx
  have hspan : f ∘ₗ g ∈ Submodule.span k {f'} :=
    (endProjection_eq_linearFunctionalPoint_iff k V g w hf hf' hfg hwval).mp (by
      rw [hwz, hzf])
  -- the point of the ambient triple product, and that it is on the correspondence over `C × T`
  set t := corrPoint k V hq (linearFunctionalPoint k V f hf)
    (linearFunctionalPoint_isClosed k V f hf) (linearFunctionalPoint k V f' hf')
    (linearFunctionalPoint_isClosed k V f' hf') with ht
  have htloc : t ∈ transitionLocusOver k V C T := by
    refine ⟨⟨(mem_transitionLocus_corrPoint k V hgrep hq f hf f' hf').mpr hspan, ?_⟩, ?_⟩
    · change (tpSource k V).base t ∈ C
      rw [ht, tpSource_corrPoint, ← hxf]
      exact hxC
    · change (tpTarget k V).base t ∈ T
      rw [ht, tpTarget_corrPoint, ← hzf]
      exact hzT
  obtain ⟨s, hs⟩ : t ∈ Set.range (transitionVarietyι k V C T hCc hTc).base := by
    rw [range_transitionVarietyι k V C T hCc hTc]
    exact htloc
  refine ⟨s, ?_, ?_⟩
  · change (transitionVarietyToPar k V (prodOfClosedToProdTwo k V C T hCc hTc)).base s =
      (p : projectiveSpaceOfModule k (ParameterModule k V))
    have hcomp : transitionVarietyToPar k V (prodOfClosedToProdTwo k V C T hCc hTc) =
        transitionVarietyι k V C T hCc hTc ≫ tpPar k V := by
      rw [transitionVarietyToPar, transitionProjPar, Category.assoc]
    rw [hcomp, Scheme.Hom.comp_apply, hs, ht, tpPar_corrPoint]
  · rw [Scheme.Hom.comp_apply, hs, ht, tpTarget_corrPoint, hzf]

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
