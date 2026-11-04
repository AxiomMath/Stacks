module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Basic
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberDimension
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Irreducible.GenericPoints

/-!
# Delta-dimension of the components of a flat base change

Let `(S, δ)` and `(S', δ')` be two base situations for Chow homology joined by a flat morphism
`g : S' ⟶ S` whose dimension functions differ by a constant `c` on the generic points of the
fibres of `g` — the situation of Stacks 0FVG. For `X` integral and locally of finite type over
`S` with `dim_δ(X) = k`, every irreducible component of `X' = X ×_S S'` has delta-dimension
`k + c`.

## Main results

* `Stacks.Chow.deltaDimension_component_baseChange` — Stacks 0FVH, the delta-dimension of every
  irreducible component of the base change.

## References

* [Stacks Project, Tag 0FVH](https://stacks.math.columbia.edu/tag/0FVH)
* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 02FX](https://stacks.math.columbia.edu/tag/02FX)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- A point of a scheme which is a generic point of an irreducible component is, as a point of
the fibre through it, a generic point of an irreducible component of that fibre. -/
@[ega "0 2.1.8" "partial, special case"]
private theorem mem_genericPoints_fiber_of_mem_genericPoints {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (hx : x ∈ genericPoints X) (s : S) (hs : f x = s) :
    (f.fiberHomeo s).symm ⟨x, by simp [hs]⟩ ∈ genericPoints (f.fiber s) := by
  refine (mem_genericPoints_iff_forall_specializes_eq _).2 fun y hy ↦ ?_
  have hxy : f.fiberι s y ⤳ x := by
    have := hy.map (f.fiberι s).continuous
    simpa only [Scheme.Hom.fiberι_fiberHomeo_symm] using this
  refine (f.fiberι s).isEmbedding.injective ?_
  simpa only [Scheme.Hom.fiberι_fiberHomeo_symm] using
    (mem_genericPoints_iff_forall_specializes_eq x).1 hx _ hxy

/-- In an irreducible space every irreducible component is the whole space. -/
private theorem coe_irreducibleComponents_eq_univ {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] (W : irreducibleComponents T) : (W : Set T) = Set.univ :=
  Set.eq_univ_of_forall fun y ↦
    W.2.2 (IrreducibleSpace.isIrreducible_univ T) (Set.subset_univ _) (Set.mem_univ y)

/-- A point of the fibre product `X ×_S S'` has the same image in `S` through both projections. -/
private theorem apply_fst_eq_apply_snd (B : FlatBaseChangeSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ B.base.S) (x' : (pullback f B.g : Scheme.{u})) :
    f (pullback.fst f B.g x') = B.g (pullback.snd f B.g x') := by
  simpa using congrArg (fun m : pullback f B.g ⟶ B.base.S => m x') pullback.condition

/-- In the situation of Stacks 0FVG, the image in `S'` of a generic point of an irreducible
component of `X' = X ×_S S'` lying over a generic point of `X` is a generic point of an
irreducible component of the fibre `g⁻¹(s)`, where `s` is the image in `S` of that generic
point of `X`. -/
private theorem mem_genericPoints_fiber_of_mem_genericPoints_pullback
    (B : FlatBaseChangeSituation.{u}) {X : Scheme.{u}} (f : X ⟶ B.base.S)
    (x' : (pullback f B.g : Scheme.{u}))
    (hx' : x' ∈ genericPoints (pullback f B.g : Scheme.{u})) :
    (⟨(pullback.snd f B.g) x', (apply_fst_eq_apply_snd B f x').symm⟩ :
      ↥(B.g ⁻¹' {f ((pullback.fst f B.g) x')})) ∈
      genericPoints (B.g ⁻¹' {f ((pullback.fst f B.g) x')}) := by
  let P : Scheme.{u} := pullback f B.g
  let p : P ⟶ X := pullback.fst f B.g
  let q : P ⟶ B.baseChange.S := pullback.snd f B.g
  let x : X := p x'
  let s : B.base.S := f x
  let s' : B.baseChange.S := q x'
  have hcomm : f x = B.g s' := apply_fst_eq_apply_snd B f x'
  let fiberSquare := AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f B.g).flip x
  let r : pullback (B.g.fiberToSpecResidueField (f x)) (Spec.map (f.residueFieldMap x)) ⟶
      pullback B.g (B.base.S.fromSpecResidueField (f x)) :=
    pullback.fst (B.g.fiberToSpecResidueField (f x)) (Spec.map (f.residueFieldMap x))
  have hrflat : Flat r := by
    have : Flat (Spec.map (f.residueFieldMap x)) :=
      Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField _) _)
    show Flat (pullback.fst (B.g.fiberToSpecResidueField (f x))
      (Spec.map (f.residueFieldMap x)))
    infer_instance
  let xFiber : p.fiber x := p.asFiber x'
  have hxFiber : xFiber ∈ genericPoints (p.fiber x) :=
    mem_genericPoints_fiber_of_mem_genericPoints p x' hx' (p x') rfl
  let xFiber' := fiberSquare.isoPullback.hom xFiber
  have hxFiber' : xFiber' ∈ genericPoints
      (pullback (B.g.fiberToSpecResidueField (f x)) (Spec.map (f.residueFieldMap x)) :
        Scheme.{u}) :=
    mem_genericPoints_of_generalizingMap
      fiberSquare.isoPullback.hom.isOpenEmbedding.generalizingMap hxFiber
  have hrfiber : r xFiber' ∈
      genericPoints (pullback B.g (B.base.S.fromSpecResidueField (f x)) : Scheme.{u}) :=
    mem_genericPoints_of_generalizingMap (Flat.generalizingMap r) hxFiber'
  have hrcomp : fiberSquare.isoPullback.hom ≫ r ≫ B.g.fiberι s = p.fiberι x ≫ q := by
    have hmap : fiberSquare.isoPullback.hom ≫ r =
        pullback.map p (X.fromSpecResidueField x) B.g
          (B.base.S.fromSpecResidueField (f x)) q (Spec.map (f.residueFieldMap x)) f
          pullback.condition (by simp) :=
      fiberSquare.isoPullback_hom_fst
    show (fiberSquare.isoPullback.hom ≫ r) ≫
        pullback.fst B.g (B.base.S.fromSpecResidueField (f x)) =
      pullback.fst p (X.fromSpecResidueField x) ≫ q
    rw [hmap, pullback.map, pullback.lift_fst]
  let sFiber : B.g.fiber s := (B.g.fiberHomeo s).symm ⟨s', hcomm.symm⟩
  have hpoint : r xFiber' = sFiber := by
    refine (B.g.fiberι s).isEmbedding.injective ?_
    have heval := congrArg (fun m : p.fiber x ⟶ B.baseChange.S => m xFiber) hrcomp
    change B.g.fiberι s (r xFiber') = q (p.fiberι x xFiber) at heval
    simpa [sFiber, xFiber, x, s', q, p, Scheme.Hom.fiberι_fiberHomeo_symm] using heval
  have hgeneric : sFiber ∈ genericPoints (B.g.fiber s) := hpoint ▸ hrfiber
  have : QuasiSober (B.g ⁻¹' {s}) := (B.g.fiberHomeo s).symm.isOpenEmbedding.quasiSober
  have hsub : (B.g.fiberHomeo s) sFiber ∈ genericPoints (B.g ⁻¹' {s}) :=
    mem_genericPoints_of_generalizingMap
      (B.g.fiberHomeo s).isOpenEmbedding.generalizingMap hgeneric
  simpa [sFiber, s', s, x, p, q, P, Scheme.Hom.fiberHomeo] using hsub

/-- At a generic point of an irreducible component, the dimension of the fibre at that point is the
transcendence degree of the residue-field extension. -/
private theorem topologicalKrullDimAt_fiber_eq_trdeg_of_mem_genericPoints {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) (hx : x ∈ genericPoints X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      (Cardinal.toENat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) :
        WithBot ℕ∞) := by
  have h := topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg f x
  rwa [ringKrullDim_stalk_eq_zero_of_mem_genericPoints (f.fiber (f x)) (f.asFiber x)
    (mem_genericPoints_fiber_of_mem_genericPoints f x hx (f x) rfl), zero_add] at h

/-- In the flat base-change situation of Stacks 0FVG, if `X` is integral and locally of finite
type over `S` with `dim_δ(X) = k`, then every irreducible component of the base change
`X ×_S S'` has delta-dimension `k + c`. -/
@[stacks 0FVH]
theorem deltaDimension_component_baseChange (B : FlatBaseChangeSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] [IsIntegral X]
    (k : ℤ) (hk : schemeDeltaDimension B.base f = (k : EInt))
    (Z : irreducibleComponents (pullback f B.g : Scheme.{u})) :
    deltaDimension B.baseChange (pullback.snd f B.g)
        ⟨Z, Z.2.1,
          isClosed_of_mem_irreducibleComponents
            (Z : Set (pullback f B.g : Scheme.{u})) Z.2⟩ =
      k + B.c := by
  let P : Scheme.{u} := pullback f B.g
  let p : P ⟶ X := pullback.fst f B.g
  let q : P ⟶ B.baseChange.S := pullback.snd f B.g
  let x' : P := (genericPoints.ofComponent Z).1
  have hx' : x' ∈ genericPoints P := (genericPoints.ofComponent Z).2
  have hxZ : IsGenericPoint x' (Z : Set P) := genericPoints.isGenericPoint_ofComponent Z
  have hx : p x' ∈ genericPoints X :=
    mem_genericPoints_of_generalizingMap (Flat.generalizingMap p) hx'
  let x : X := p x'
  let s : B.base.S := f x
  let s' : B.baseChange.S := q x'
  have hcomm : f x = B.g s' := apply_fst_eq_apply_snd B f x'
  have hsGeneric' : (⟨s', hcomm.symm⟩ : ↥(B.g ⁻¹' {s})) ∈ genericPoints (B.g ⁻¹' {s}) := by
    simpa [s, s', x, p, q, P] using
      mem_genericPoints_fiber_of_mem_genericPoints_pullback B f x' hx'
  have hδ : B.baseChange.dimensionFunction (q x') = B.base.dimensionFunction s + B.c :=
    B.dimensionFunction_eq_add s ⟨⟨s', hcomm.symm⟩, hsGeneric'⟩
  let W₀ : irreducibleComponents X :=
    ⟨Set.univ, ⟨IrreducibleSpace.isIrreducible_univ X, fun V _ _ ↦ Set.subset_univ V⟩⟩
  let Z₀ : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hxGeneric : IsGenericPoint x (Set.univ : Set X) := by
    simpa [coe_irreducibleComponents_eq_univ (genericPoints.component ⟨x, hx⟩)] using
      genericPoints.isGenericPoint ⟨x, hx⟩
  have hsup : schemeDeltaDimension B.base f = (deltaDimension B.base f Z₀ : EInt) := by
    rw [schemeDeltaDimension_eq_iSup]
    refine le_antisymm (iSup_le fun W ↦ ?_) (le_iSup_of_le W₀ le_rfl)
    have hWZ : IsGenericPoint x
        ((⟨W, W.2.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ :
          IrreducibleCloseds X) : Set X) := by
      simpa [coe_irreducibleComponents_eq_univ W] using hxGeneric
    rw [deltaDimension_eq_of_isGenericPoint B.base f _ x hWZ,
      deltaDimension_eq_of_isGenericPoint B.base f Z₀ x hxGeneric]
  have hwhole : deltaDimension B.base f Z₀ = k :=
    WithBotTop.coe_injective (hsup.symm.trans hk)
  have hrelSource : relativeDimension B.base.dimensionFunction f x = k :=
    (deltaDimension_eq_of_isGenericPoint B.base f Z₀ x hxGeneric).symm.trans hwhole
  have hxFormula := topologicalKrullDimAt_fiber_eq_trdeg_of_mem_genericPoints f x hx
  have hx'Formula := topologicalKrullDimAt_fiber_eq_trdeg_of_mem_genericPoints q x' hx'
  have hpointwise :=
    (topologicalKrullDimAt_fiber_eq_of_isPullback (IsPullback.of_hasPullback f B.g) x').symm
  have hpointwise' : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      topologicalKrullDimAt (q.fiber (q x')) (q.asFiber x') := by
    simpa [x, p, q, P] using hpointwise
  have htrdegNat := congrArg ENat.toNat
    (WithBot.coe_injective (hxFormula.symm.trans (hpointwise'.trans hx'Formula)))
  simp only [Cardinal.toNat_toENat] at htrdegNat
  rw [deltaDimension_eq_of_isGenericPoint B.baseChange q _ x' hxZ, relativeDimension,
    ← htrdegNat]
  simp only [relativeDimension, s] at hrelSource hδ
  omega

end Stacks.Chow

end
