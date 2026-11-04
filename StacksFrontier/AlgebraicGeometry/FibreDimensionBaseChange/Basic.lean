module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.KrullDimension.BaseChange
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# The dimension of a fibre is invariant under base change

Let `f : X ⟶ S` be locally of finite type and let

```
X' ---g'---> X
|            |
f'           f
v            v
S' ---g----> S
```

be a fibre product diagram. For a point `x'` of `X'` the fibre of `f'` through `x'` has the same
dimension at `x'` as the fibre of `f` through `g' x'` has at `g' x'`. This is part (1) of Stacks
Tag 02FY, and the consequence recorded here is the monotonicity used by an inverse system of
morphisms of schemes whose transition maps are closed immersions into the base change
(Stacks Tag 05M5): along such a transition the local dimension of the fibre can only drop.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_isPullback` is **Stacks Tag 02FY part
  (1)**: the local dimension of the fibre is invariant under base change.
* `AlgebraicGeometry.topologicalKrullDimAt_fiber_le_of_isClosedImmersion_lift`: if a morphism
  `f' : X' ⟶ S'` maps to `f : X ⟶ S` by `u : X' ⟶ X` and `g : S' ⟶ S` in such a way that the
  induced `X' ⟶ X ×_S S'` is a closed immersion, then the local dimension of the fibre of `f'`
  at `x'` is at most the local dimension of the fibre of `f` at `u x'`.
* `Topology.IsInducing.topologicalKrullDimAt_le`: the local Krull dimension of a topological
  space at a point is monotone along an inducing map.

## Implementation notes

The dimension of a scheme at a point is `topologicalKrullDimAt` (Stacks Tag 0055 (4)), and the
scheme-theoretic fibre through `x` is `f.fiber (f x)` with `f.asFiber x` the point itself, so the
quantity `dim_x X_{f(x)}` of the source is
`topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)`, as in
`AlgebraicGeometry.isOpen_setOf_fiberDimensionAt_le` (Tag 02FZ).

Base change is reduced to a base change along an *extension of residue fields* by
`AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback`, which identifies the fibre
of `f'` at `y'` with the fibre of `f` at `g y'` base changed along `κ(g y') ⟶ κ(y')`. That case
is in turn reduced to the
affine one by the open cover of `pullback π φ` by the `pullback (𝒰.f j ≫ π) φ` for an affine open
cover `𝒰` of the source, and the affine case is `Algebra.IsPushout.localKrullDim_comap_eq`
(Tag 00P4) applied to `A ⊗[k] K`. Since the base of the residue-field base change is already
affine, no compatible pair of affine charts on the two bases has to be constructed; this is why
the argument goes through the residue fields rather than applying Tag 00QI directly.

Dependent-type bookkeeping is avoided by moving the statements onto the *topological* fibre
`f ⁻¹' {y}` (`topologicalKrullDimAt_fiber_eq_preimage` and
`topologicalKrullDimAt_fiber_asFiber_eq_preimage`), where the base point of the fibre appears
only inside a set and not inside a type.

## References

* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 00P4](https://stacks.math.columbia.edu/tag/00P4)
* [Stacks Project, Tag 02FZ](https://stacks.math.columbia.edu/tag/02FZ)
* [Stacks Project, Tag 05M5](https://stacks.math.columbia.edu/tag/05M5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct

universe u

/-- The local Krull dimension at a point is monotone along an inducing map: a neighbourhood of
the image pulls back to a neighbourhood whose dimension is at most that of the original. -/
public theorem Topology.IsInducing.topologicalKrullDimAt_le {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {h : X → Y} (hh : Topology.IsInducing h) (x : X) :
    topologicalKrullDimAt X x ≤ topologicalKrullDimAt Y (h x) := by
  refine le_iInf fun V ↦ ?_
  refine iInf_le_of_le ⟨h ⁻¹' V.1, V.2.1, V.2.2.preimage hh.continuous⟩ ?_
  exact (hh.restrictPreimage V.1).topologicalKrullDim_le

namespace AlgebraicGeometry

/-- The local Krull dimension of a scheme at a point is unchanged along an isomorphism. -/
public theorem topologicalKrullDimAt_eq_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e]
    (x : X) : topologicalKrullDimAt ↥X x = topologicalKrullDimAt ↥Y (e x) :=
  topologicalKrullDimAt_eq_of_homeomorph (TopCat.homeoOfIso (asIso (Scheme.forgetToTop.map e))) x

/-- Pointwise form of an equation `a ≫ b = c` of morphisms of schemes. -/
private theorem apply_apply_eq_of_comp_eq {X Y Z : Scheme.{u}} {a : X ⟶ Y} {b : Y ⟶ Z}
    {c : X ⟶ Z} (h : a ≫ b = c) (x : X) : b (a x) = c x := by
  rw [← h, Scheme.Hom.comp_apply]

section FieldBaseChange

/-- The affine case of base change along a field extension: the local dimension of
`Spec (A ⊗[k] K)` at a prime is the local dimension of `Spec A` at the prime below it. This is
Tag 00P4. -/
private theorem localKrullDim_tensorProduct_comap_eq (k K A : Type u) [Field k] [Field K]
    [CommRing A] [Algebra k K] [Algebra k A] [Algebra.FiniteType k A]
    (w : PrimeSpectrum (A ⊗[k] K)) :
    letI := Algebra.TensorProduct.rightAlgebra (R := k) (A := A) (B := K)
    topologicalKrullDimAt (PrimeSpectrum (A ⊗[k] K)) w =
      topologicalKrullDimAt (PrimeSpectrum A)
        (PrimeSpectrum.comap (algebraMap A (A ⊗[k] K)) w) := by
  let _ := Algebra.TensorProduct.rightAlgebra (R := k) (A := A) (B := K)
  rw [topologicalKrullDimAt_eq_localKrullDim, topologicalKrullDimAt_eq_localKrullDim]
  exact (Algebra.IsPushout.localKrullDim_comap_eq k K A (A ⊗[k] K) w).symm

/-- Base change of `Spec A` along a field extension `K / k`, with `A` of finite type over `k`. -/
private theorem topologicalKrullDimAt_pullback_fst_eq_of_isAffine {k K A : Type u} [Field k]
    [Field K] [CommRing A] [Algebra k K] [Algebra k A] [Algebra.FiniteType k A]
    (w : ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    topologicalKrullDimAt ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))) w =
      topologicalKrullDimAt ↥(Spec (CommRingCat.of A))
        (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) w) := by
  let _ := Algebra.TensorProduct.rightAlgebra (R := k) (A := A) (B := K)
  rw [topologicalKrullDimAt_eq_of_isIso (pullbackSpecIso k A K).hom w]
  have h : Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[k] K)))
      ((pullbackSpecIso k A K).hom w) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) w :=
    apply_apply_eq_of_comp_eq (pullbackSpecIso_hom_fst' k A K) w
  rw [← h]
  exact localKrullDim_tensorProduct_comap_eq k K A ((pullbackSpecIso k A K).hom w)

/-- Base change of an affine scheme over a field along a field extension. -/
private theorem topologicalKrullDimAt_pullback_fst_eq_of_isAffine' {k K : Type u} [Field k]
    [Field K] [Algebra k K] {A : CommRingCat.{u}} (π : Spec A ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType π]
    (w : ↥(pullback π (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    topologicalKrullDimAt ↥(pullback π (Spec.map (CommRingCat.ofHom (algebraMap k K)))) w =
      topologicalKrullDimAt ↥(Spec A)
        (pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap k K))) w) := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective π
  have hft : RingHom.FiniteType ψ.hom :=
    HasRingHomProperty.Spec_iff.mp (show LocallyOfFiniteType (Spec.map ψ) from inferInstance)
  algebraize [ψ.hom]
  exact topologicalKrullDimAt_pullback_fst_eq_of_isAffine (k := k) (K := K) (A := ↥A) w

/-- Base change along a field extension does not change the local dimension, for the canonical
pullback. -/
private theorem topologicalKrullDimAt_pullback_fst_eq {k K : Type u} [Field k] [Field K]
    [Algebra k K] {F : Scheme.{u}} (π : F ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType π]
    (w : ↥(pullback π (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    topologicalKrullDimAt ↥(pullback π (Spec.map (CommRingCat.ofHom (algebraMap k K)))) w =
      topologicalKrullDimAt ↥F
        (pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap k K))) w) := by
  have key : ∃ (j : F.affineOpenCover.I₀)
      (v : ↥(pullback (F.affineOpenCover.f j ≫ π)
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))),
      (pullback.map (F.affineOpenCover.f j ≫ π)
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) π
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) (F.affineOpenCover.f j)
        (𝟙 _) (𝟙 _) (by simp) (by simp)) v = w := by
    obtain ⟨i, v, hv⟩ := (Scheme.Pullback.openCoverOfLeft F.affineOpenCover.openCover π
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).exists_eq w
    exact ⟨i, v, hv⟩
  obtain ⟨j, v, rfl⟩ := key
  have : IsOpenImmersion (F.affineOpenCover.f j) := F.affineOpenCover.openCover.map_prop j
  set m := pullback.map (F.affineOpenCover.f j ≫ π)
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) π
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) (F.affineOpenCover.f j)
    (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hsq : m ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.fst (F.affineOpenCover.f j ≫ π)
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ F.affineOpenCover.f j :=
    pullback.lift_fst _ _ _
  rw [show pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap k K))) (m v) =
      F.affineOpenCover.f j
        (pullback.fst (F.affineOpenCover.f j ≫ π)
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) v) from
      congrArg (fun r => r.base v) hsq,
    (F.affineOpenCover.f j).isOpenEmbedding.topologicalKrullDimAt_eq,
    m.isOpenEmbedding.topologicalKrullDimAt_eq]
  exact topologicalKrullDimAt_pullback_fst_eq_of_isAffine' (F.affineOpenCover.f j ≫ π) v

/-- Base change along a field extension does not change the local dimension, for an arbitrary
pullback square. -/
private theorem topologicalKrullDimAt_eq_of_isPullback_over_field {k K : Type u} [Field k]
    [Field K] [Algebra k K] {F P : Scheme.{u}} (π : F ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType π] {p₁ : P ⟶ F} {p₂ : P ⟶ Spec (CommRingCat.of K)}
    (hP : IsPullback p₁ p₂ π (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (w : P) :
    topologicalKrullDimAt ↥P w = topologicalKrullDimAt ↥F (p₁ w) := by
  have h : pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (hP.isoPullback.hom w) = p₁ w :=
    apply_apply_eq_of_comp_eq hP.isoPullback_hom_fst w
  rw [topologicalKrullDimAt_eq_of_isIso hP.isoPullback.hom w,
    topologicalKrullDimAt_pullback_fst_eq π, h]

end FieldBaseChange

section TopologicalFibre

/-- The local dimension of a scheme-theoretic fibre, read off on the topological fibre. -/
public theorem topologicalKrullDimAt_fiber_eq_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (w : f.fiber y) :
    topologicalKrullDimAt ↥(f.fiber y) w =
      topologicalKrullDimAt ((f : X → Y) ⁻¹' {y}) (f.fiberHomeo y w) :=
  topologicalKrullDimAt_eq_of_homeomorph (f.fiberHomeo y) w

/-- The local dimension at `x` of the fibre of `f` through `x`, read off on the topological
fibre. -/
public theorem topologicalKrullDimAt_fiber_asFiber_eq_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) :
    topologicalKrullDimAt ↥(f.fiber (f x)) (f.asFiber x) =
      topologicalKrullDimAt ((f : X → Y) ⁻¹' {f x}) ⟨x, rfl⟩ := by
  rw [topologicalKrullDimAt_fiber_eq_preimage f (f x) (f.asFiber x)]
  congr 1
  exact Subtype.ext (f.fiberι_asFiber x)

/-- Two descriptions of the same topological fibre give the same local dimension. -/
public theorem topologicalKrullDimAt_preimage_congr {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) {y y' : Y} (h : y = y') (x : X) (hx : f x = y) (hx' : f x = y') :
    topologicalKrullDimAt (f ⁻¹' {y}) ⟨x, hx⟩ =
      topologicalKrullDimAt (f ⁻¹' {y'}) ⟨x, hx'⟩ := by
  subst h
  rfl

end TopologicalFibre

section BaseChange

/-- **Stacks Project, Tag 02FY part (1).** In a fibre product diagram with `f` locally of finite
type, the fibre of the base change `f'` has the same dimension at `x'` as the fibre of `f` has
at the image of `x'`. -/
@[stacks 02FY "part (1)"]
public theorem topologicalKrullDimAt_fiber_eq_of_isPullback {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (hsq : IsPullback g' f' f g) [LocallyOfFiniteType f] (x' : X') :
    topologicalKrullDimAt ↥(f'.fiber (f' x')) (f'.asFiber x') =
      topologicalKrullDimAt ↥(f.fiber (f (g' x'))) (f.asFiber (g' x')) := by
  have hw : f (g' x') = g (f' x') :=
    apply_apply_eq_of_comp_eq hsq.w x'
  set y' := f' x'
  let : Algebra ↥(S.residueField (g y')) ↥(S'.residueField y') :=
    (g.residueFieldMap y').hom.toAlgebra
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (g y')) := by
    show LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField (g y')))
    infer_instance
  let q : f'.fiber y' ⟶ f.fiber (g y') :=
    pullback.map f' (S'.fromSpecResidueField y') f (S.fromSpecResidueField (g y'))
      g' (Spec.map (g.residueFieldMap y')) g hsq.w.symm (by simp)
  have hfib : IsPullback q (f'.fiberToSpecResidueField y')
      (f.fiberToSpecResidueField (g y')) (Spec.map (g.residueFieldMap y')) :=
    isPullback_fiberToSpecResidueField_of_isPullback hsq y'
  have hmap : CommRingCat.ofHom
      (algebraMap ↥(S.residueField (g y')) ↥(S'.residueField y')) =
      g.residueFieldMap y' := by
    rw [RingHom.algebraMap_toAlgebra]
    ext
    rfl
  rw [topologicalKrullDimAt_eq_of_isPullback_over_field (k := ↥(S.residueField (g y')))
    (K := ↥(S'.residueField y')) (f.fiberToSpecResidueField (g y'))
    (by rwa [hmap]) (f'.asFiber x')]
  have hqfst : q ≫ f.fiberι (g y') = f'.fiberι y' ≫ g' := pullback.lift_fst _ _ _
  have hpt : f.fiberι (g y') (q (f'.asFiber x')) = g' x' :=
    (apply_apply_eq_of_comp_eq hqfst _).trans (congrArg g' (f'.fiberι_asFiber x'))
  rw [topologicalKrullDimAt_fiber_eq_preimage f (g y') (q (f'.asFiber x')),
    topologicalKrullDimAt_fiber_asFiber_eq_preimage f (g' x'),
    show f.fiberHomeo (g y') (q (f'.asFiber x')) = ⟨g' x', hw⟩ from Subtype.ext hpt]
  exact topologicalKrullDimAt_preimage_congr (f : X → S) hw.symm (g' x') hw rfl

/-- If `f'` factors through `q` over the same base by a map which is an inducing map of
topological spaces, the local dimension of a fibre of `f'` is at most that of the corresponding
fibre of `q`. -/
public theorem topologicalKrullDimAt_fiber_le_of_isInducing {X' P S' : Scheme.{u}}
    (p : X' ⟶ P) (q : P ⟶ S') (f' : X' ⟶ S') (hfac : p ≫ q = f')
    (hp : Topology.IsInducing (p : X' → P)) (x' : X') :
    topologicalKrullDimAt ↥(f'.fiber (f' x')) (f'.asFiber x') ≤
      topologicalKrullDimAt ↥(q.fiber (q (p x'))) (q.asFiber (p x')) := by
  have hpt : ∀ z : X', f' z = q (p z) := fun z ↦
    (apply_apply_eq_of_comp_eq hfac z).symm
  have hset : (f' : X' → S') ⁻¹' {f' x'} =
      (p : X' → P) ⁻¹' ((q : P → S') ⁻¹' {q (p x')}) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hpt z, hpt x']
  rw [topologicalKrullDimAt_fiber_asFiber_eq_preimage f' x',
    topologicalKrullDimAt_fiber_asFiber_eq_preimage q (p x'),
    topologicalKrullDimAt_eq_of_homeomorph (Homeomorph.setCongr hset) ⟨x', rfl⟩]
  exact (hp.restrictPreimage ((q : P → S') ⁻¹' {q (p x')})).topologicalKrullDimAt_le ⟨x', rfl⟩

/-- The local dimension of a fibre drops along a closed immersion into a base change: if
`u : X' ⟶ X` and `g : S' ⟶ S` carry `f'` to `f` and the induced morphism
`X' ⟶ X ×_S S'` is a closed immersion, then the fibre of `f'` at `x'` has dimension at most that
of the fibre of `f` at `u x'`.

This is the transition step of Stacks Tag 05M5: for an inverse system of morphisms of schemes
`(f_i : X_i ⟶ S_i)` whose transitions `X_{i'} ⟶ X_i ×_{S_i} S_{i'}` are closed immersions, the
local dimension of the fibre is antitone in the index. -/
public theorem topologicalKrullDimAt_fiber_le_of_isClosedImmersion_lift
    {X' X S' S : Scheme.{u}} {f' : X' ⟶ S'} {f : X ⟶ S} [LocallyOfFiniteType f] {g : S' ⟶ S}
    {u : X' ⟶ X} (hcomm : u ≫ f = f' ≫ g)
    [IsClosedImmersion (pullback.lift u f' hcomm : X' ⟶ pullback f g)] (x' : X') :
    topologicalKrullDimAt ↥(f'.fiber (f' x')) (f'.asFiber x') ≤
      topologicalKrullDimAt ↥(f.fiber (f (u x'))) (f.asFiber (u x')) := by
  set p : X' ⟶ pullback f g := pullback.lift u f' hcomm
  have hfac : p ≫ pullback.snd f g = f' := pullback.lift_snd _ _ _
  have hu : pullback.fst f g (p x') = u x' :=
    apply_apply_eq_of_comp_eq (pullback.lift_fst u f' hcomm) x'
  refine le_trans (topologicalKrullDimAt_fiber_le_of_isInducing p (pullback.snd f g) f'
    hfac (IsClosedImmersion.isClosedEmbedding p).isEmbedding.isInducing x') ?_
  rw [topologicalKrullDimAt_fiber_eq_of_isPullback (IsPullback.of_hasPullback f g) (p x')]
  exact (congrArg (fun x : X ↦ topologicalKrullDimAt ↥(f.fiber (f x)) (f.asFiber x)) hu).le

end BaseChange

end AlgebraicGeometry

end
