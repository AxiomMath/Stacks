module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.FiberSequence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.FibreRegularSequence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.KrullDimension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmoothInputs.FibreDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.QuasiFiniteLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.CompositeFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
import all StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.QuasiFiniteSlice

/-!
# Quasi-finiteness of an immersed subscheme at a point of a maximal regular sequence

Let `f : X ⟶ S` be locally of finite type, let `x : X` be a point closed in its fibre, and let
`h₁, …, h_r` be elements of `𝒪_{X, x}` whose images in the local ring `𝒪_{X_{f x}, x}` of the
fibre form a **regular sequence of length the dimension of that local ring**.  Let `ι : Z ⟶ X`
be an immersion through `x` on which all the `h_i` vanish.  Then `Z ⟶ S` is **quasi-finite at
the point of `Z` above `x`**.

The local ring of the fibre of `Z ⟶ S` is a quotient of `𝒪_{X_{f x}, x}` in which the whole
regular sequence vanishes, so it is zero-dimensional
(`Stacks.AlgebraicGeometry.ringKrullDim_eq_zero_of_surjective_of_forall_eq_zero`); the point
being closed in its fibre makes the residue-field extension finite, hence of transcendence
degree zero; and the fibre-dimension formula of **Stacks 02FX** then gives a fibre of local
dimension zero, which is quasi-finiteness by **Stacks 0397**.

## Main results

* `Stacks.AlgebraicGeometry.isClosed_asFiber_comp_of_isPreimmersion`: a point closed in its
  fibre stays closed in the fibre of the composite with an immersion.
* `Stacks.AlgebraicGeometry.isClosed_asFiber_of_locallyQuasiFinite_fiberι_comp`: a point of a
  relation whose double fibre is quasi-finite, and whose image under the other leg is a closed
  point, is closed in its fibre.
* `Stacks.AlgebraicGeometry.quasiFiniteAt_comp_of_isRegular_fiberStalk`: the quasi-finiteness.

## Implementation notes

The two fibres are compared by `AlgebraicGeometry.fiberMapOfSourceHom`, which exhibits the fibre
of `ι ≫ f` as the base change of the fibre of `f` along `ι`; it is therefore a preimmersion, so
its map on stalks is surjective and its map on points is injective.  The point of the fibre of
`ι ≫ f` above `z` is compared with the canonical one by `TopCat.Presheaf.stalkCongr`, since
`(ι ≫ f) z` and `f (ι z)` are equal only propositionally in the shape in which the pullback
description produces them.

## References

* [Stacks Project, Tag 02FX](https://stacks.math.columbia.edu/tag/02FX)
* [Stacks Project, Tag 0397](https://stacks.math.columbia.edu/tag/0397)
* [Stacks Project, Lemma 37.24.6 (Tag 0570)](https://stacks.math.columbia.edu/tag/0570)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry

/-- The germ of a global section at a point, read at a propositionally equal point. -/
theorem germ_top_cast_eq {X : Scheme.{u}} {x y : X} (h : x = y) (s : Γ(X, ⊤)) :
    X.presheaf.germ ⊤ x trivial s = h.symm ▸ X.presheaf.germ ⊤ y trivial s := by
  subst h
  rfl

/-- **The stalk map of a composite on a transported germ.**  For `k : F ⟶ R`, `g : R ⟶ U`, a
point `v` of `F` and a point `q` of `R` with `k v = q`, the stalk map of `k ≫ g` at `v`, applied
to an element of `𝒪_{U, g q}` transported to `𝒪_{U, (k ≫ g) v}`, is the stalk map of `g` at `q`
followed by that of `k` at `v`. -/
theorem stalkMap_comp_cast {F R U : Scheme.{u}} (k : F ⟶ R) (g : R ⟶ U) (v : F) {q : R}
    (h : k v = q) (hq : (k ≫ g) v = g q) (x : U.presheaf.stalk (g q)) :
    ((k ≫ g).stalkMap v).hom (hq.symm ▸ x)
      = (k.stalkMap v).hom (h.symm ▸ (g.stalkMap q).hom x) := by
  subst h
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- **The stalk map of a composite, applied, with the point of the target transported.**  The two
factors are applied in turn; the transport is the same on both sides, `(p ≫ g) z` and `g (p z)`
being the same point. -/
theorem stalkMap_comp_apply_cast {Z X Y : Scheme.{u}} (p : Z ⟶ X) (g : X ⟶ Y) (z : Z) {y : Y}
    (hy : (p ≫ g) z = y) (x : Y.presheaf.stalk y) :
    ((p ≫ g).stalkMap z).hom (hy.symm ▸ x)
      = (p.stalkMap z).hom ((g.stalkMap (p z)).hom (hy.symm ▸ x)) := by
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- **A point of a relation whose double fibre is quasi-finite is closed in the fibre of one
leg.**  Let `a, b : R ⟶ U` and let `r₀ : R` be a point at which the fibre of `b` maps to `U`
along `a` by a locally quasi-finite morphism.  If `a r₀` is a closed point of `U`, then `r₀` is
closed in its fibre under `b`.

The locus in `b.fiber (b r₀)` where `a` takes the value `a r₀` is closed, `{a r₀}` being closed,
and discrete, `b.fiber (b r₀) ⟶ U` being locally quasi-finite; a singleton of a discrete closed
subspace is closed in the ambient space. -/
theorem isClosed_asFiber_of_locallyQuasiFinite_fiberι_comp {R U : Scheme.{u}} (a b : R ⟶ U)
    (r₀ : R) (hlqf : LocallyQuasiFinite (b.fiberι (b r₀) ≫ a))
    (hlft : LocallyOfFiniteType (b.fiberι (b r₀) ≫ a))
    (hclosed : IsClosed ({a r₀} : Set U)) :
    IsClosed ({b.asFiber r₀} : Set (b.fiber (b r₀))) := by
  have hpt : b.asFiber r₀ ∈ (b.fiberι (b r₀) ≫ a) ⁻¹' ({a r₀} : Set U) :=
    congrArg a (b.fiberι_asFiber r₀)
  have _ : DiscreteTopology ((b.fiberι (b r₀) ≫ a) ⁻¹' ({a r₀} : Set U)) :=
    _root_.isDiscrete_iff_discreteTopology.1
      (locallyQuasiFinite_iff_isDiscrete_preimage_singleton.1 hlqf (a r₀))
  have hcl : IsClosed ((b.fiberι (b r₀) ≫ a) ⁻¹' ({a r₀} : Set U)) :=
    hclosed.preimage (b.fiberι (b r₀) ≫ a).continuous
  have himg := hcl.isClosedEmbedding_subtypeVal.isClosedMap
    ({(⟨b.asFiber r₀, hpt⟩ : (b.fiberι (b r₀) ≫ a) ⁻¹' ({a r₀} : Set U))} :
      Set ((b.fiberι (b r₀) ≫ a) ⁻¹' ({a r₀} : Set U))) (isClosed_discrete _)
  simpa using himg

/-- The comparison `j` of the fibre of `ι ≫ f` with that of `f` is a preimmersion, and sends the
point `w` of the fibre of `ι ≫ f` over `f (ι z)` lying above `z` to the canonical point
of the fibre of `f`. -/
private theorem fiberMapOfSourceHom_point {Z X S : Scheme.{u}} (ι : Z ⟶ X) [IsPreimmersion ι]
    (f : X ⟶ S) (z : Z) (hbase : (ι ≫ f) z = f (ι z)) (w : (ι ≫ f).fiber (f (ι z)))
    (hwdef : w = hbase ▸ (ι ≫ f).asFiber z) :
    IsPreimmersion (AlgebraicGeometry.fiberMapOfSourceHom ι f (f (ι z))) ∧
      (ι ≫ f).fiberι (f (ι z)) w = z ∧
      AlgebraicGeometry.fiberMapOfSourceHom ι f (f (ι z)) w = f.asFiber (ι z) := by
  have hpb := (AlgebraicGeometry.fiberMapOfSourceHom_isPullback ι f (f (ι z))).flip
  have hw : (ι ≫ f).fiberι (f (ι z)) w = z := by
    subst hwdef
    cases hbase
    exact Scheme.Hom.fiberι_asFiber (ι ≫ f) z
  refine ⟨MorphismProperty.of_isPullback hpb inferInstance, hw, ?_⟩
  refine (f.fiberι (f (ι z))).isEmbedding.injective ?_
  have heval := congrArg (fun k => k w) hpb.w
  simpa only [Scheme.Hom.comp_apply, hw, Scheme.Hom.fiberι_asFiber] using heval.symm

variable {Z X S : Scheme.{u}}

/-- **A point closed in its fibre stays closed in the fibre of a composite with a
preimmersion.**  The fibre of `ι ≫ f` is the base change of the fibre of `f` along `ι`
(`AlgebraicGeometry.fiberMapOfSourceHom_isPullback`), so the comparison morphism is again a
preimmersion; the singleton is the preimage of a closed singleton under a continuous injection. -/
theorem isClosed_asFiber_comp_of_isPreimmersion (ι : Z ⟶ X) [IsPreimmersion ι] (f : X ⟶ S)
    (z : Z) (hclosed : IsClosed ({f.asFiber (ι z)} : Set (f.fiber (f (ι z))))) :
    IsClosed ({(ι ≫ f).asFiber z} : Set ((ι ≫ f).fiber ((ι ≫ f) z))) := by
  have hbase : (ι ≫ f) z = f (ι z) := by simp
  let w : (ι ≫ f).fiber (f (ι z)) := hbase ▸ (ι ≫ f).asFiber z
  obtain ⟨_, _, hjpoint⟩ := fiberMapOfSourceHom_point ι f z hbase w rfl
  let j : (ι ≫ f).fiber (f (ι z)) ⟶ f.fiber (f (ι z)) :=
    AlgebraicGeometry.fiberMapOfSourceHom ι f (f (ι z))
  have hpre : j ⁻¹' {f.asFiber (ι z)} = {w} := by
    ext w'
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun hw' => j.isEmbedding.injective (hw'.trans hjpoint.symm),
      by rintro rfl; exact hjpoint⟩
  have hc' : IsClosed ({w} : Set ((ι ≫ f).fiber (f (ι z)))) := by
    simpa [hpre] using hclosed.preimage j.continuous
  cases hbase
  exact hc'

/-- **Quasi-finiteness of an immersed subscheme cut by a maximal fibre-regular sequence.**  Let
`f : X ⟶ S` be locally of finite type, let `ι : Z ⟶ X` be a preimmersion with `ι z = x`, and let
`h₁, …, h_r` be elements of `𝒪_{X, x}` which vanish in `𝒪_{Z, z}` and whose images in the local
ring of the fibre `X_{f x}` at `x` form a regular sequence of length `dim 𝒪_{X_{f x}, x}`.  If
`x` is closed in its fibre, then `ι ≫ f` is quasi-finite at `z`. -/
theorem quasiFiniteAt_comp_of_isRegular_fiberStalk (ι : Z ⟶ X) [IsPreimmersion ι] (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyOfFiniteType (ι ≫ f)] (z : Z) (x : X) (hx : ι z = x)
    {r : ℕ} (h : Fin r → X.presheaf.stalk x)
    (hzero : ∀ k, (ι.stalkMap z).hom (hx.symm ▸ h k) = 0)
    (hreg : RingTheory.Sequence.IsRegular ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
      (List.ofFn fun k => ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
        ((f.fiberι_asFiber x).symm ▸ h k)))
    (hdim : ((r : ℕ) : WithBot ℕ∞) =
      ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)))
    (hclosed : IsClosed ({f.asFiber x} : Set (f.fiber (f x)))) :
    quasiFiniteAt (ι ≫ f) z := by
  subst hx
  let g := ι ≫ f
  have hbase : g z = f (ι z) := by simp [g]
  have hbaseComp : (ι ≫ f) z = f (ι z) := by simp
  let w : (ι ≫ f).fiber (f (ι z)) := hbaseComp ▸ (ι ≫ f).asFiber z
  obtain ⟨hjimm, hw, hjpoint⟩ := fiberMapOfSourceHom_point ι f z hbaseComp w rfl
  let j : (ι ≫ f).fiber (f (ι z)) ⟶ f.fiber (f (ι z)) :=
    AlgebraicGeometry.fiberMapOfSourceHom ι f (f (ι z))
  have hpb := (AlgebraicGeometry.fiberMapOfSourceHom_isPullback ι f (f (ι z))).flip
  let _ : Algebra (S.residueField (g z)) (Z.residueField z) :=
    (g.residueFieldMap z).hom.toAlgebra
  have _ : Module.Finite (S.residueField (g z)) (Z.residueField z) :=
    (isClosed_asFiber_iff_finite_residueField g z).mp
      (isClosed_asFiber_comp_of_isPreimmersion ι f z hclosed)
  have htrdeg : Algebra.trdeg (S.residueField (g z)) (Z.residueField z) = 0 :=
    trdeg_eq_zero
  let R : Type u := (f.fiber (f (ι z))).presheaf.stalk (f.asFiber (ι z))
  let Q : Type u := ((ι ≫ f).fiber (f (ι z))).presheaf.stalk w
  let ss := List.ofFn fun k : Fin r =>
    ((f.fiberι (f (ι z))).stalkMap (f.asFiber (ι z))).hom
      ((f.fiberι_asFiber (ι z)).symm ▸ h k)
  have hreg' : RingTheory.Sequence.IsRegular R ss := by simpa [R, ss] using hreg
  let e := (f.fiber (f (ι z))).presheaf.stalkCongr (.of_eq hjpoint.symm)
  let φ : R →+* Q := (e.hom ≫ j.stalkMap w).hom
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨q', hq'⟩ := j.stalkMap_surjective w q
    refine ⟨e.inv.hom q', ?_⟩
    change (j.stalkMap w).hom (e.hom.hom (e.inv.hom q')) = q
    rw [e.inv_hom_id_apply, hq']
  have heq : f.fiberι (f (ι z)) (f.asFiber (ι z)) = f.fiberι (f (ι z)) (j w) := by
    rw [hjpoint]
  have hpt : f.fiberι (f (ι z)) (j w) = ι ((ι ≫ f).fiberι (f (ι z)) w) := by
    have hp := congrArg (fun k => k w) hpb.w.symm
    simpa only [Scheme.Hom.comp_apply] using hp
  let eX1 := X.presheaf.stalkCongr (.of_eq heq)
  let eX2 := X.presheaf.stalkCongr (.of_eq hpt)
  have hcongr : (f.fiberι (f (ι z))).stalkMap (f.asFiber (ι z)) ≫ e.hom =
      eX1.hom ≫ (f.fiberι (f (ι z))).stalkMap (j w) := by
    simpa [e, eX1] using
      (Scheme.Hom.stalkMap_congr_point (f.fiberι (f (ι z))) (f.asFiber (ι z)) (j w) hjpoint.symm)
  have h2' : (f.fiberι (f (ι z))).stalkMap (j w) ≫ j.stalkMap w =
      eX2.hom ≫ ι.stalkMap ((ι ≫ f).fiberι (f (ι z)) w) ≫
        ((ι ≫ f).fiberι (f (ι z))).stalkMap w := by
    have h2 := Scheme.Hom.stalkMap_congr_hom (j ≫ f.fiberι (f (ι z)))
      (((ι ≫ f).fiberι (f (ι z))) ≫ ι) hpb.w.symm w
    have ee := Scheme.Hom.comp_apply j (f.fiberι (f (ι z))) w
    cases ee.symm
    convert h2 using 1 <;> simp [Scheme.Hom.stalkMap_comp, eX2, TopCat.Presheaf.stalkCongr]
  have hcomp : (f.fiberι (f (ι z))).stalkMap (f.asFiber (ι z)) ≫ e.hom ≫ j.stalkMap w =
      eX1.hom ≫ eX2.hom ≫ ι.stalkMap ((ι ≫ f).fiberι (f (ι z)) w) ≫
        ((ι ≫ f).fiberι (f (ι z))).stalkMap w := by
    rw [reassoc_of% hcongr, h2']
  let eX := X.presheaf.stalkCongr (.of_eq (congrArg ι hw))
  let eI := Z.presheaf.stalkCongr (.of_eq hw)
  have hzero' (k : Fin r) :
      (ι.stalkMap ((ι ≫ f).fiberι (f (ι z)) w)).hom (eX.inv.hom (h k)) = 0 := by
    have hcongI := Scheme.Hom.stalkMap_congr_point ι ((ι ≫ f).fiberι (f (ι z)) w) z hw
    have heval := congrArg (fun m => m.hom (eX.inv.hom (h k))) hcongI
    have hval : eI.hom.hom
        ((ι.stalkMap ((ι ≫ f).fiberι (f (ι z)) w)).hom (eX.inv.hom (h k))) =
        (ι.stalkMap z).hom (h k) := by
      have hh : eI.hom.hom
          ((ι.stalkMap ((ι ≫ f).fiberι (f (ι z)) w)).hom (eX.inv.hom (h k))) =
          (ι.stalkMap z).hom (eX.hom.hom (eX.inv.hom (h k))) := by
        simpa only [ConcreteCategory.comp_apply] using heval
      rw [hh, eX.inv_hom_id_apply (h k)]
    refine (ConcreteCategory.bijective_of_isIso eI.hom).1 ?_
    rw [hval, hzero k]
    simp
  have hcast (k : Fin r) :
      eX2.hom (eX1.hom ((f.fiberι_asFiber (ι z)).symm ▸ h k)) = eX.inv.hom (h k) := by
    have hpath : ((f.fiberι_asFiber (ι z)).symm.trans heq).trans hpt =
        (congrArg ι hw).symm := Subsingleton.elim _ _
    have h1 := stalkCongr_hom_eq_cast X.presheaf heq ((f.fiberι_asFiber (ι z)).symm ▸ h k)
    have h2 := stalkCongr_hom_eq_cast X.presheaf hpt
      (heq ▸ ((f.fiberι_asFiber (ι z)).symm ▸ h k))
    have h3 := stalkCongr_inv_eq_cast X.presheaf (congrArg ι hw) (h k)
    change eX2.hom.hom (eX1.hom.hom ((f.fiberι_asFiber (ι z)).symm ▸ h k)) = eX.inv.hom (h k)
    have hc1 : heq ▸ (f.fiberι_asFiber (ι z)).symm ▸ h k =
        ((f.fiberι_asFiber (ι z)).symm.trans heq) ▸ h k :=
      cast_cast_eq (β := fun p : X => X.presheaf.stalk p)
        (f.fiberι_asFiber (ι z)).symm heq (h k)
    have hc1' := congrArg
      (fun t : X.presheaf.stalk ((f.fiberι (f (ι z))) (j w)) => hpt ▸ t) hc1
    calc
      _ = hpt ▸ ((f.fiberι_asFiber (ι z)).symm.trans heq ▸ h k) := by
        rw [h1, h2]
        exact hc1'
      _ = ((f.fiberι_asFiber (ι z)).symm.trans heq).trans hpt ▸ h k :=
        cast_cast_eq (β := fun p : X => X.presheaf.stalk p)
          ((f.fiberι_asFiber (ι z)).symm.trans heq) hpt (h k)
      _ = (congrArg ι hw).symm ▸ h k := congrArg (fun p => p ▸ h k) hpath
      _ = _ := h3.symm
  have hkill : ∀ s ∈ ss, φ s = 0 := by
    intro s hs
    rcases List.mem_ofFn.mp hs with ⟨k, rfl⟩
    change ((e.hom ≫ j.stalkMap w).hom)
      (((f.fiberι (f (ι z))).stalkMap (f.asFiber (ι z))).hom
        ((f.fiberι_asFiber (ι z)).symm ▸ h k)) = 0
    have hval := congrArg (fun m :
        X.presheaf.stalk ((f.fiberι (f (ι z))) (f.asFiber (ι z))) ⟶
          ((ι ≫ f).fiber (f (ι z))).presheaf.stalk w =>
      m.hom ((f.fiberι_asFiber (ι z)).symm ▸ h k)) hcomp
    simp only [ConcreteCategory.comp_apply] at hval
    rwa [hcast k, hzero' k, map_zero] at hval
  have hlen' : (ss.length : WithBot ℕ∞) = ringKrullDim R := by simpa [R, ss] using hdim
  have _ : IsLocallyNoetherian (f.fiber (f (ι z))) := isLocallyNoetherian_fiber f (f (ι z))
  have _ : IsNoetherianRing R := inferInstance
  have hringdim : ringKrullDim Q = 0 :=
    ringKrullDim_eq_zero_of_surjective_of_forall_eq_zero φ hφ ss hreg' hlen' hkill
  have hringdim' : ringKrullDim ((g.fiber (g z)).presheaf.stalk (g.asFiber z)) = 0 := by
    dsimp [Q] at hringdim
    cases hbase
    exact hringdim
  have hdimfiber : topologicalKrullDimAt (g.fiber (g z)) (g.asFiber z) = 0 := by
    rw [topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk_add_trdeg g z, hringdim', htrdeg]
    simp
  exact (quasiFiniteAt_iff_fiberDimensionAt_eq_zero g z).2 hdimfiber

end Stacks.AlgebraicGeometry

end
