module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalRingSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSliceFlatDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreRegularityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAtGeometricPoint

/-!
# Descending the fibre hypothesis of Stacks 06LW to the local ring of a chart of the fibre

Let `g : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` in a big fppf site, let
`ξ : F ⟶ X` be a morphism of algebraic spaces — in the application the projection of a fibre of
`g` — and let `z` be a geometric point of `F`.  The hypothesis of Stacks 06LW is that global
regular functions `f₁, …, f_r` on `X` have regular images in the étale local ring `𝒪_{F, z̄}`,
while the scheme-level slicing lemma Stacks 06LI consumes regularity in the *ordinary* local ring
of the scheme-theoretic fibre of a chart.  This file performs the passage between the two, which
is the third step of the source's proof.

## Main results

* `AlgebraicGeometry.Space.isRegular_chartFiber_of_isRegular_etaleLocalRing`: **the third step.**
  Given a small étale neighbourhood `U'` of `z` mapping to an étale chart `U` of `X` over `ξ`,
  and an isomorphism of the scheme of `U'` with the base change `U_v ×_{κ(v)} Spec k'` of the
  scheme-theoretic fibre of `U ⟶ V` compatible with that morphism, regularity of the images of
  the `f_i` in `𝒪_{F, z̄}` gives regularity of their germs in the local ring of `U_v` at the point
  under `z`.

## Implementation notes

Two identifications meet here.  On the étale side the image of a germ under the comparison
homomorphism of Stacks 04NG is the germ of the pulled-back function on a chart of the source,
which is `AlgebraicGeometry.Space.etaleLocalRingMap_chartLocalRingToEtaleLocalRing_germ`, the
square of local rings of Stacks 05VU read on germs of global sections; the neighbourhood of the
image point it is applied to is `AlgebraicGeometry.Space.targetNeighborhood`, whose point is the
image of the point of the source chart on the nose.  On the Zariski side the two flat comparisons
separating `𝒪_{U_v, u}` from `𝒪_{F, z̄}` are
`AlgebraicGeometry.Space.isRegular_map_etaleLocalRing_iff_fiber_extendResidueField`, into which
the isomorphism enters as the flat morphism it asks for.

The two meet because the morphism of schemes underlying the morphism of the site is, by the
compatibility hypothesis, the isomorphism followed by the two projections
`U_v ×_{κ(v)} Spec k' ⟶ U_v ⟶ U`; so the composite of the two stalk maps is the stalk map of the
morphism of the site, and a germ of a global function pulls back the same way along both.  That
is checked on germs of global sections rather than on the stalk maps themselves, where it would
be a rewrite under a type depending on the morphism being rewritten.

The point of the fibre is produced by `AlgebraicGeometry.Scheme.Hom.asFiber`, so the sequence
whose regularity is concluded is literally the one
`AlgebraicGeometry.Space.exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_chartFiber`
consumes, transport along `AlgebraicGeometry.Scheme.Hom.fiberι_asFiber` included.  Getting from
the point of the base change that the isomorphism produces to that one is the only place a
dependent rewrite is needed, and it is done by generalising the point and its defining equation
and substituting, which is what makes the transport disappear.

## References

* [Stacks Project, Tag 00LM](https://stacks.math.columbia.edu/tag/00LM)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 06LI](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Lemma 06LW](https://stacks.math.columbia.edu/tag/06LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The third step of the proof of the flatness half of Stacks 06LW: the fibre hypothesis
descends to the local ring of a chart of the fibre.**  Let `ξ : F ⟶ X` be a morphism of algebraic
spaces, let `z` be a geometric point of `F` and let `U'` be a small étale neighbourhood of `z`
whose chart maps to an étale chart `U` of `X` by a morphism `gNU` of the site commuting with `ξ`.
Let `U ⟶ V` be a morphism of the site and suppose the scheme of `U'` is isomorphic to the base
change `U_v ×_{Spec κ(v)} Spec k'` of the scheme-theoretic fibre of `U ⟶ V` at a point `v`, by an
isomorphism carrying the two projections to the morphism of schemes underlying `gNU`.

If global regular functions `f₁, …, f_r` on `X` have regular images in the étale local ring
`𝒪_{F, z̄}`, then their germs at the point `u` of `U` under `z` form a regular sequence in the
local ring of the scheme-theoretic fibre of `U ⟶ V` through `u`.

This is the shape in which
`AlgebraicGeometry.Space.exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_chartFiber`
consumes a regular sequence, so the two together are the last three steps of the source's
proof. -/
theorem isRegular_chartFiber_of_isRegular_etaleLocalRing
    {Xs Fs : AlgebraicSpaces B S hS} (ξ : Fs ⟶ Xs)
    {z : GeometricPoint B S hS Fs.1} (N : SmallEtaleNeighborhood z)
    (Uch : SmallEtale B S hS Xs.1) (gNU : N.chart.obj.left ⟶ Uch.obj.left)
    (hsq : N.chart.obj.hom ≫ ξ.hom = yoneda.map gNU ≫ Uch.obj.hom)
    {V : BigFppfOver B S hS} (gUV : Uch.obj.left ⟶ V)
    {k' : Type u} [Field k'] {v : (BigFppfOver.toScheme B S hS).obj V}
    (φ : ((BigFppfOver.toScheme B S hS).obj V).residueField v ⟶ CommRingCat.of k')
    (e : chartScheme N.chart ≅
      pullback (((BigFppfOver.toScheme B S hS).map gUV).fiberToSpecResidueField v) (Spec.map φ))
    (he : e.hom ≫ pullback.fst
            (((BigFppfOver.toScheme B S hS).map gUV).fiberToSpecResidueField v) (Spec.map φ) ≫
          ((BigFppfOver.toScheme B S hS).map gUV).fiberι v =
        (BigFppfOver.toScheme B S hS).map gNU)
    {r : ℕ} (fs : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS Xs)).sections)
    (hreg : RingTheory.Sequence.IsRegular (etaleLocalRing B S hS Fs.1 z)
      (List.ofFn fun i : Fin r => etaleLocalRingMap Fs.2 ξ.hom z
        (etaleLocalRingGerm B S hS Xs.1 (geometricPointMap ξ.hom z)
          (op (targetNeighborhood B S hS N Uch gNU hsq)) ((fs i).eval (op Uch))))) :
    RingTheory.Sequence.IsRegular
      ((((BigFppfOver.toScheme B S hS).map gUV).fiber
          ((BigFppfOver.toScheme B S hS).map gUV
            ((BigFppfOver.toScheme B S hS).map gNU
              (chartPoint B S hS Fs.1 N)))).presheaf.stalk
        (((BigFppfOver.toScheme B S hS).map gUV).asFiber
          ((BigFppfOver.toScheme B S hS).map gNU (chartPoint B S hS Fs.1 N))))
      (List.ofFn fun i : Fin r =>
        ((((BigFppfOver.toScheme B S hS).map gUV).fiberι
              ((BigFppfOver.toScheme B S hS).map gUV
                ((BigFppfOver.toScheme B S hS).map gNU
                  (chartPoint B S hS Fs.1 N)))).stalkMap
            (((BigFppfOver.toScheme B S hS).map gUV).asFiber
              ((BigFppfOver.toScheme B S hS).map gNU (chartPoint B S hS Fs.1 N)))).hom
          ((((BigFppfOver.toScheme B S hS).map gUV).fiberι_asFiber
                ((BigFppfOver.toScheme B S hS).map gNU
                  (chartPoint B S hS Fs.1 N))).symm ▸
            ((chartScheme Uch).presheaf.germ ⊤
              ((BigFppfOver.toScheme B S hS).map gNU (chartPoint B S hS Fs.1 N)) trivial
              ((fs i).eval (op Uch))))) := by
  have he2 : (e.hom ≫ pullback.fst
        (((BigFppfOver.toScheme B S hS).map gUV).fiberToSpecResidueField v) (Spec.map φ)) ≫
      ((BigFppfOver.toScheme B S hS).map gUV).fiberι v =
      (BigFppfOver.toScheme B S hS).map gNU := by
    rw [Category.assoc]; exact he
  -- the point of the chart of `X` under `z` lies in the fibre over `v`
  have hfib : ((BigFppfOver.toScheme B S hS).map gUV).fiberι v
      ((e.hom ≫ pullback.fst
        (((BigFppfOver.toScheme B S hS).map gUV).fiberToSpecResidueField v) (Spec.map φ))
          (chartPoint B S hS Fs.1 N)) =
      (BigFppfOver.toScheme B S hS).map gNU (chartPoint B S hS Fs.1 N) := by
    exact congrArg (· (chartPoint B S hS Fs.1 N)) he2
  have hcv : (BigFppfOver.toScheme B S hS).map gUV
      ((BigFppfOver.toScheme B S hS).map gNU (chartPoint B S hS Fs.1 N)) = v := by
    rw [← hfib]
    have hmem : ((BigFppfOver.toScheme B S hS).map gUV).fiberι v
        ((e.hom ≫ pullback.fst
          (((BigFppfOver.toScheme B S hS).map gUV).fiberToSpecResidueField v) (Spec.map φ))
            (chartPoint B S hS Fs.1 N)) ∈
        ((BigFppfOver.toScheme B S hS).map gUV) ⁻¹' {v} :=
      ((BigFppfOver.toScheme B S hS).map gUV).range_fiberι v ▸ Set.mem_range_self _
    simpa using hmem
  subst hcv
  have : IsIso e.hom := ⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩
  have : AlgebraicGeometry.Flat e.hom := inferInstance
  have hasF : (e.hom ≫ pullback.fst
        (((BigFppfOver.toScheme B S hS).map gUV).fiberToSpecResidueField
          ((BigFppfOver.toScheme B S hS).map gUV
            ((BigFppfOver.toScheme B S hS).map gNU (chartPoint B S hS Fs.1 N))))
        (Spec.map φ)) (chartPoint B S hS Fs.1 N) =
      ((BigFppfOver.toScheme B S hS).map gUV).asFiber
        ((BigFppfOver.toScheme B S hS).map gNU (chartPoint B S hS Fs.1 N)) := by
    refine (((BigFppfOver.toScheme B S hS).map gUV).fiberι _).isEmbedding.injective ?_
    rw [Scheme.Hom.fiberι_asFiber]
    exact hfib
  -- generalise the point of the fibre and the equation identifying it, so that the transport in
  -- the statement becomes a reflexivity
  suffices hgen : ∀ (y : ((BigFppfOver.toScheme B S hS).map gUV).fiber
        ((BigFppfOver.toScheme B S hS).map gUV
          ((BigFppfOver.toScheme B S hS).map gNU (chartPoint B S hS Fs.1 N))))
      (p : chartScheme Uch)
      (hp : ((BigFppfOver.toScheme B S hS).map gUV).fiberι
        ((BigFppfOver.toScheme B S hS).map gUV
          ((BigFppfOver.toScheme B S hS).map gNU (chartPoint B S hS Fs.1 N))) y = p)
      (_ : (e.hom ≫ pullback.fst
        (((BigFppfOver.toScheme B S hS).map gUV).fiberToSpecResidueField
          ((BigFppfOver.toScheme B S hS).map gUV
            ((BigFppfOver.toScheme B S hS).map gNU (chartPoint B S hS Fs.1 N))))
        (Spec.map φ)) (chartPoint B S hS Fs.1 N) = y)
      (_ : p = (BigFppfOver.toScheme B S hS).map gNU (chartPoint B S hS Fs.1 N)),
      RingTheory.Sequence.IsRegular
        ((((BigFppfOver.toScheme B S hS).map gUV).fiber
            ((BigFppfOver.toScheme B S hS).map gUV
              ((BigFppfOver.toScheme B S hS).map gNU
                (chartPoint B S hS Fs.1 N)))).presheaf.stalk y)
        (List.ofFn fun i : Fin r =>
          ((((BigFppfOver.toScheme B S hS).map gUV).fiberι
                ((BigFppfOver.toScheme B S hS).map gUV
                  ((BigFppfOver.toScheme B S hS).map gNU
                    (chartPoint B S hS Fs.1 N)))).stalkMap y).hom
            (hp.symm ▸ ((chartScheme Uch).presheaf.germ ⊤ p trivial ((fs i).eval (op Uch))))) by
    exact hgen _ _ (((BigFppfOver.toScheme B S hS).map gUV).fiberι_asFiber _) hasF rfl
  intro y p hp hy hpu
  subst hy
  subst hp
  refine (isRegular_map_etaleLocalRing_iff_fiber_extendResidueField B S hS Fs.1 Fs.2 N
    ((BigFppfOver.toScheme B S hS).map gUV) _ φ e.hom _).mp ?_
  rw [List.map_ofFn]
  refine (iff_of_eq (congrArg (fun l : List ↥(etaleLocalRing B S hS Fs.1 z) =>
    RingTheory.Sequence.IsRegular ↥(etaleLocalRing B S hS Fs.1 z) l)
    (congrArg List.ofFn (funext fun i => ?_)))).mpr hreg
  have hsec : (Scheme.Γ.map (e.hom ≫ pullback.fst
          (((BigFppfOver.toScheme B S hS).map gUV).fiberToSpecResidueField _)
          (Spec.map φ)).op).hom
        ((Scheme.Γ.map (((BigFppfOver.toScheme B S hS).map gUV).fiberι _).op).hom
          ((fs i).eval (op Uch))) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map gNU).op).hom
        ((fs i).eval (op Uch)) := by
    have h : (Scheme.Γ.map (((BigFppfOver.toScheme B S hS).map gUV).fiberι _).op ≫
        Scheme.Γ.map (e.hom ≫ pullback.fst
          (((BigFppfOver.toScheme B S hS).map gUV).fiberToSpecResidueField _) (Spec.map φ)).op) =
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map gNU).op := by
      rw [← Functor.map_comp, ← op_comp, he2]
    exact ConcreteCategory.congr_hom h ((fs i).eval (op Uch))
  simp only [RingHom.coe_comp, Function.comp_apply]
  refine Eq.trans (congrArg (chartLocalRingToEtaleLocalRing B S hS Fs.1 Fs.2 N)
    (Eq.trans (congrArg (fun y => ((e.hom ≫ pullback.fst
            (((BigFppfOver.toScheme B S hS).map gUV).fiberToSpecResidueField _)
            (Spec.map φ)).stalkMap (chartPoint B S hS Fs.1 N)).hom y)
        (Scheme.Hom.germ_stalkMap_apply (((BigFppfOver.toScheme B S hS).map gUV).fiberι _) ⊤ _
          trivial ((fs i).eval (op Uch))))
      (Eq.trans (Scheme.Hom.germ_stalkMap_apply (e.hom ≫ pullback.fst
            (((BigFppfOver.toScheme B S hS).map gUV).fiberToSpecResidueField _)
            (Spec.map φ)) ⊤ (chartPoint B S hS Fs.1 N) trivial _)
        (congrArg ((chartScheme N.chart).presheaf.germ ⊤ (chartPoint B S hS Fs.1 N) trivial)
          hsec)))) ?_
  refine Eq.trans (etaleLocalRingMap_chartLocalRingToEtaleLocalRing_germ B S hS ξ z N
    (targetNeighborhood B S hS N Uch gNU hsq) gNU hsq rfl ((fs i).eval (op Uch))).symm ?_
  exact congrArg (etaleLocalRingMap Fs.2 ξ.hom z)
    (chartLocalRingToEtaleLocalRing_germ B S hS Xs.1 Xs.2
      (targetNeighborhood B S hS N Uch gNU hsq) ((fs i).eval (op Uch)))

end AlgebraicGeometry.Space

end
