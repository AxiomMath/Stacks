module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Splitting off finitely many isolated fibre points after an étale base change

Let `f : X ⟶ S` be locally of finite type and let `x₁, …, xₙ` be points of one fibre of `f`,
each isolated in that fibre. After passing to a single elementary étale neighbourhood of the
base point, each `xᵢ` lies in an open subscheme of the base change which is finite over the new
base and meets the distinguished fibre in exactly one point, with unchanged residue field. If
`f` is in addition separated and the `xᵢ` are pairwise distinct, these opens can be shrunk to
pairwise disjoint *open and closed* pieces, and the base change decomposes as their disjoint
union together with one complementary piece whose distinguished fibre avoids the `xᵢ`.

## Main results

* `Stacks.Flatness.exists_etaleNeighborhood_finite_opens_of_isolated_fiber_points` is Tag 02LL:
  the common elementary étale neighbourhood and the finite opens.
* `Stacks.Flatness.exists_etaleNeighborhood_decomposition` is Tag 02LN: the decomposition into
  open and closed pieces.

## Implementation notes

The family of points is indexed by `Fin n`, so the empty family is allowed; in Tag 02LL
repetitions are allowed as well. For Tag 02LL an open subscheme is represented by a
`AlgebraicGeometry.Scheme.Opens` and its two structure morphisms are the restrictions of the
pullback projections along its inclusion; the unique point of the distinguished fibre is
specified by a singleton-set equality, and equality of residue fields by invertibility of the
canonical residue-field map.

Tag 02LL is proved by induction on `n`: the tail is handled by the inductive hypothesis, the
head by `Stacks.Flatness.exists_etaleNeighborhood_finiteAt` applied to the base change, and
the tail data is carried along the further neighbourhood by
`Stacks.Flatness.isFiniteNeighborhoodAt_baseChange`.

For Tag 02LN the pieces are indexed by `Option (Fin n)`, with `none` the complementary piece,
and the decomposition is expressed by asking the coproduct descender to be an isomorphism. The
disjointness is obtained by removing from the `i`-th open its intersection with the earlier
ones, which is legitimate because separatedness makes each open *closed* as well: it is finite,
hence proper, over the base. The final clause — no point of the complementary piece over the
distinguished point maps to any `xᵢ` — uses that a point of a fibre product over an elementary
étale neighbourhood is determined by its two projections, which is read off the classification
`AlgebraicGeometry.Scheme.Pullback.carrierEquiv` together with the fact that the relevant
residue-field tensor product has a one-point spectrum.

## References

* [Stacks Project, Tag 02LL](https://stacks.math.columbia.edu/tag/02LL)
* [Stacks Project, Tag 02LN](https://stacks.math.columbia.edu/tag/02LN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.Flatness

/-- A point isolated in its fibre has a preimage in the base change along an elementary étale
neighbourhood which lies over the distinguished point and is again isolated in its fibre. -/
lemma exists_isolated_point_pullback_of_elementary {X S : Scheme.{u}}
    (f : X ⟶ S) (s : S) (U : EtaleNeighborhood S s) (hU : U.IsElementary)
    (x : X) (hx : f x = s) (hxi : IsIsolatedPoint (f.asFiber x)) :
    ∃ y : ↑(pullback f U.toBase),
      pullback.fst f U.toBase y = x ∧ pullback.snd f U.toBase y = U.point ∧
      IsIsolatedPoint ((pullback.snd f U.toBase).asFiber y) := by
  classical
  subst s
  obtain ⟨y, hyx, hyu⟩ := Scheme.Pullback.exists_preimage_pullback x U.point U.map_point.symm
  let q := pullback.snd f U.toBase
  let e := fiberAfterElementaryEtaleIso f (f x) U hU
  let py : q.fiber U.point := hyu ▸ q.asFiber y
  have he : e.hom ≫ f.fiberι (f x) = q.fiberι U.point ≫ pullback.fst f U.toBase := by
    simpa [e, q] using fiberAfterElementaryEtaleIso_fiberι f (f x) U hU
  have hp : e.hom py = f.asFiber x := by
    apply (f.fiberι (f x)).isEmbedding.injective
    calc
      f.fiberι (f x) (e.hom py) = (e.hom ≫ f.fiberι (f x)) py := by simp
      _ = (q.fiberι U.point ≫ pullback.fst f U.toBase) py := by rw [he]
      _ = x := by
        show pullback.fst f U.toBase (q.fiberι U.point py) = x
        have hpyLift : q.fiberι U.point py = y := by
          simpa [py] using fiberι_cast_asFiber q y hyu
        rw [hpyLift, hyx]
      _ = f.fiberι (f x) (f.asFiber x) := by simp
  let H := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)
  refine ⟨y, hyx, hyu, ?_⟩
  change IsOpen ({f.asFiber x} : Set (f.fiber (f x))) at hxi
  have hpH : H py = f.asFiber x := hp
  have hset : H ⁻¹' ({f.asFiber x} : Set (f.fiber (f x))) = {py} := by
    ext z
    show H z = f.asFiber x ↔ z = py
    exact ⟨fun hz => H.injective (hz.trans hpH.symm), fun hz => hz ▸ hpH⟩
  have hpy : IsOpen ({py} : Set _) := hset ▸ hxi.preimage H.continuous
  exact (isIsolatedPoint_cast_asFiber q y hyu).1 hpy

/-- Unpacking `Stacks.Flatness.IsFiniteNeighborhoodAt` into the finiteness, singleton-fibre,
image and residue-field statements about its distinguished point. -/
lemma exists_of_isFiniteNeighborhoodAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (U : EtaleNeighborhood S (f x)) (V : (pullback f U.toBase).Opens)
    (h : IsFiniteNeighborhoodAt f x U V) :
    ∃ v : V,
      IsFinite (V.ι ≫ pullback.snd f U.toBase) ∧
      {y : V | (V.ι ≫ pullback.snd f U.toBase) y = U.point} = {v} ∧
      (V.ι ≫ pullback.fst f U.toBase) v = x ∧
      IsIso ((V.ι ≫ pullback.fst f U.toBase).residueFieldMap v) := by
  obtain ⟨hfin, ⟨v, hv, huv⟩, hrest⟩ := h
  refine ⟨v, hfin, ?_, (hrest v hv).1, (hrest v hv).2⟩
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact ⟨huv z, fun hz => hz ▸ hv⟩

/-- Packing the finiteness, singleton-fibre, image and residue-field statements about a chosen
point back into `Stacks.Flatness.IsFiniteNeighborhoodAt`. -/
lemma isFiniteNeighborhoodAt_of_exists {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (U : EtaleNeighborhood S (f x)) (V : (pullback f U.toBase).Opens)
    (v : V) (hfin : IsFinite (V.ι ≫ pullback.snd f U.toBase))
    (hsingle : {z : V | (V.ι ≫ pullback.snd f U.toBase) z = U.point} = {v})
    (hx : (V.ι ≫ pullback.fst f U.toBase) v = x)
    (hres : IsIso ((V.ι ≫ pullback.fst f U.toBase).residueFieldMap v)) :
    IsFiniteNeighborhoodAt f x U V := by
  have hv : (V.ι ≫ pullback.snd f U.toBase) v = U.point :=
    hsingle.symm.subset (Set.mem_singleton v)
  have huniq : ∀ z : V, (V.ι ≫ pullback.snd f U.toBase) z = U.point → z = v :=
    fun z hz => hsingle.subset hz
  refine ⟨hfin, ⟨v, hv, huniq⟩, fun z hz => ?_⟩
  obtain rfl := huniq z hz
  exact ⟨hx, hres⟩

/-- Along an open immersion `a`, the composite `a ≫ g` induces an isomorphism of residue fields at
`x` exactly when `g` does at `a x`. -/
private theorem isIso_residueFieldMap_comp_iff {X Y Z : Scheme.{u}} (a : X ⟶ Y)
    [IsOpenImmersion a] (g : Y ⟶ Z) (x : X) :
    IsIso ((a ≫ g).residueFieldMap x) ↔ IsIso (g.residueFieldMap (a x)) := by
  rw [Scheme.residueFieldMap_comp]
  exact isIso_comp_right_iff _ _

/-- **Stacks Project, Tag 02LL.** Several isolated points of one fibre can simultaneously be
made finite over a single elementary étale neighbourhood of the base point. -/
@[stacks 02LL]
theorem exists_etaleNeighborhood_finite_opens_of_isolated_fiber_points
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (s : S) (n : ℕ) (x : Fin n → X) (hx : ∀ i, f (x i) = s)
    (hx_isolated : ∀ i, IsIsolatedPoint (f.asFiber (x i))) :
    ∃ (U : EtaleNeighborhood S s) (_ : U.IsElementary)
      (V : Fin n → (pullback f U.toBase).Opens)
      (v : ∀ i, V i),
      (∀ i, IsFinite ((V i).ι ≫ pullback.snd f U.toBase)) ∧
      (∀ i, {y : V i | ((V i).ι ≫ pullback.snd f U.toBase) y = U.point} = {v i}) ∧
      (∀ i, ((V i).ι ≫ pullback.fst f U.toBase) (v i) = x i) ∧
      (∀ i, IsIso (((V i).ι ≫ pullback.fst f U.toBase).residueFieldMap (v i))) := by
  classical
  revert x hx hx_isolated
  induction n with
  | zero =>
      intro x hx hxi
      exact ⟨EtaleNeighborhood.self S s, EtaleNeighborhood.isElementary_self S s,
        Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0⟩
  | succ n ih =>
      intro x hx hxi
      let xtail : Fin n → X := fun i => x i.succ
      obtain ⟨U, hU, Vt, vt, htail⟩ :=
        ih xtail (fun i => hx i.succ) (fun i => hxi i.succ)
      let q := pullback.snd f U.toBase
      obtain ⟨y, hyx, hyu, hyisolated⟩ :=
        exists_isolated_point_pullback_of_elementary f s U hU (x 0) (hx 0) (hxi 0)
      obtain ⟨N⟩ := exists_etaleNeighborhood_finiteAt q y hyisolated
      let N' : EtaleNeighborhood U.scheme U.point :=
        { scheme := N.neighborhood.scheme
          point := N.neighborhood.point
          toBase := N.neighborhood.toBase
          map_point := N.neighborhood.map_point.trans hyu }
      have hN' : N'.IsElementary := by
        rw [EtaleNeighborhood.isElementary_iff]
        exact N.neighborhood.isElementary_iff.mp N.elementary
      let W : EtaleNeighborhood S s :=
        { scheme := N'.scheme
          point := N'.point
          toBase := N'.toBase ≫ U.toBase
          map_point := by
            show U.toBase (N'.toBase N'.point) = s
            exact (congrArg U.toBase N'.map_point).trans U.map_point }
      have hW : W.IsElementary := by
        rw [EtaleNeighborhood.isElementary_iff]
        show IsIso ((N'.toBase ≫ U.toBase).residueFieldMap N'.point)
        rw [Scheme.residueFieldMap_comp]
        have hUbase : IsIso (U.toBase.residueFieldMap (N'.toBase N'.point)) := by
          rw [N'.map_point]
          exact U.isElementary_iff.mp hU
        exact IsIso.comp_isIso' hUbase (N'.isElementary_iff.mp hN')
      let g : pullback f (N'.toBase ≫ U.toBase) ⟶ pullback f U.toBase :=
        pullback.map f (N'.toBase ≫ U.toBase) f U.toBase
          (𝟙 X) N'.toBase (𝟙 S) (by simp) (by simp)
      let Vtail : Fin n → (pullback f W.toBase).Opens := fun i => g ⁻¹ᵁ Vt i
      let Ui : ∀ i, EtaleNeighborhood S (f (xtail i)) := fun i =>
        { scheme := U.scheme
          point := U.point
          toBase := U.toBase
          map_point := U.map_point.trans (hx i.succ).symm }
      let Wi : ∀ i, EtaleNeighborhood S (f (xtail i)) := fun i =>
        { scheme := N'.scheme
          point := N'.point
          toBase := N'.toBase ≫ (Ui i).toBase
          map_point := by
            show (Ui i).toBase (N'.toBase N'.point) = f (xtail i)
            exact (congrArg (Ui i).toBase N'.map_point).trans (Ui i).map_point }
      have htailSpec : ∀ i, IsFiniteNeighborhoodAt f (xtail i) (Wi i) (Vtail i) := by
        intro i
        have hbase := isFiniteNeighborhoodAt_baseChange f (xtail i) (Ui i) (Vt i)
          (isFiniteNeighborhoodAt_of_exists f (xtail i) (Ui i) (Vt i) (vt i)
            (htail.1 i) (htail.2.1 i) (htail.2.2.1 i) (htail.2.2.2 i)) N' hN'
        simpa [W, Wi, Ui, Vtail, g] using hbase
      have hbase : N.neighborhood.toBase = N'.toBase := rfl
      let eCast := pullback.congrHom (f₁ := q) (f₂ := q)
        (g₁ := N.neighborhood.toBase) (g₂ := N'.toBase) rfl hbase
      let eAssoc := pullbackLeftPullbackSndIso f U.toBase N'.toBase
      let e := eCast ≪≫ eAssoc
      let j := N.openSubscheme.ι ≫ e.hom
      let Vzero : (pullback f W.toBase).Opens := j.opensRange
      let ezero := j.isoOpensRange
      obtain ⟨hBfinite, ⟨vB, hBpoint, hBunique⟩, hBrest⟩ := N.spec
      let vzero : Vzero := ezero.hom vB
      have hCastSnd : eCast.hom ≫ pullback.snd q N'.toBase =
          pullback.snd q N.neighborhood.toBase := by
        dsimp [eCast, pullback.congrHom, pullback.map]
        rw [pullback.lift_snd]
        simp
      have hCastFst : eCast.hom ≫ pullback.fst q N'.toBase =
          pullback.fst q N.neighborhood.toBase := by
        dsimp [eCast, pullback.congrHom, pullback.map]
        rw [pullback.lift_fst]
        simp
      have hAssocSnd : eAssoc.hom ≫ pullback.snd f W.toBase = pullback.snd q N'.toBase :=
        pullbackLeftPullbackSndIso_hom_snd f U.toBase N'.toBase
      have hAssocFst : eAssoc.hom ≫ pullback.fst f W.toBase =
          pullback.fst q N'.toBase ≫ pullback.fst f U.toBase :=
        pullbackLeftPullbackSndIso_hom_fst f U.toBase N'.toBase
      have hzj : ezero.hom ≫ Vzero.ι = j := Scheme.Hom.isoOpensRange_hom_ι j
      have hzeroProj : ezero.hom ≫ Vzero.ι ≫ pullback.snd f W.toBase =
          N.openSubscheme.ι ≫ pullback.snd q N.neighborhood.toBase := by
        rw [← Category.assoc, hzj]
        simp [j, e, hAssocSnd, hCastSnd]
      have hzeroFst : ezero.hom ≫ Vzero.ι ≫ pullback.fst f W.toBase =
          N.openSubscheme.ι ≫ pullback.fst q N.neighborhood.toBase ≫
            pullback.fst f U.toBase := by
        rw [← Category.assoc, hzj]
        simp [j, e, hAssocFst, ← hCastFst]
      have hzeroFinite : IsFinite (Vzero.ι ≫ pullback.snd f W.toBase) := by
        have hmap : Vzero.ι ≫ pullback.snd f W.toBase =
            ezero.inv ≫ N.openSubscheme.ι ≫ pullback.snd q N.neighborhood.toBase := by
          rw [← hzeroProj, ← Category.assoc, ezero.inv_hom_id, Category.id_comp]
        rw [hmap]
        have : IsFinite (N.openSubscheme.ι ≫ pullback.snd q N.neighborhood.toBase) := hBfinite
        infer_instance
      have hzeroPoint : (Vzero.ι ≫ pullback.snd f W.toBase) vzero = W.point := by
        calc
          (Vzero.ι ≫ pullback.snd f W.toBase) vzero =
              (ezero.hom ≫ Vzero.ι ≫ pullback.snd f W.toBase) vB := rfl
          _ = (N.openSubscheme.ι ≫ pullback.snd q N.neighborhood.toBase) vB := by
                rw [hzeroProj]
          _ = W.point := hBpoint
      have hzeroSingle :
          {z : Vzero | (Vzero.ι ≫ pullback.snd f W.toBase) z = W.point} = {vzero} := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        refine ⟨fun hz => ?_, fun hz => hz ▸ hzeroPoint⟩
        have hzinv : ezero.hom (ezero.inv z) = z := by
          show (ezero.inv ≫ ezero.hom) z = z
          rw [ezero.inv_hom_id]
          rfl
        have hzB : (N.openSubscheme.ι ≫ pullback.snd q N.neighborhood.toBase)
            (ezero.inv z) = N.neighborhood.point := by
          calc
            (N.openSubscheme.ι ≫ pullback.snd q N.neighborhood.toBase) (ezero.inv z) =
                (ezero.hom ≫ Vzero.ι ≫ pullback.snd f W.toBase) (ezero.inv z) := by
                  rw [hzeroProj]
            _ = (Vzero.ι ≫ pullback.snd f W.toBase) z := by
                  show pullback.snd f W.toBase (Vzero.ι (ezero.hom (ezero.inv z))) =
                    pullback.snd f W.toBase (Vzero.ι z)
                  rw [hzinv]
            _ = N.neighborhood.point := hz
        rw [← hzinv, hBunique (ezero.inv z) hzB]
      have hzeroX : (Vzero.ι ≫ pullback.fst f W.toBase) vzero = x 0 := by
        have hBy : (N.openSubscheme.ι ≫ pullback.fst q N.neighborhood.toBase) vB = y :=
          (hBrest vB hBpoint).1
        calc
          (Vzero.ι ≫ pullback.fst f W.toBase) vzero =
              (ezero.hom ≫ Vzero.ι ≫ pullback.fst f W.toBase) vB := rfl
          _ = (N.openSubscheme.ι ≫ pullback.fst q N.neighborhood.toBase ≫
                pullback.fst f U.toBase) vB := by rw [hzeroFst]
          _ = x 0 := by
                show pullback.fst f U.toBase
                  ((N.openSubscheme.ι ≫ pullback.fst q N.neighborhood.toBase) vB) = x 0
                rw [hBy, hyx]
      have hzeroResidue :
          IsIso ((Vzero.ι ≫ pullback.fst f W.toBase).residueFieldMap vzero) := by
        let gOld := N.openSubscheme.ι ≫ pullback.fst q N.neighborhood.toBase
        let xB : N.openSubscheme.toScheme := vB
        have hBres : IsIso (gOld.residueFieldMap xB) := (hBrest vB hBpoint).2
        have hBy : gOld xB = y := (hBrest vB hBpoint).1
        have holdResidue : IsIso ((gOld ≫ pullback.fst f U.toBase).residueFieldMap xB) := by
          rw [Scheme.residueFieldMap_comp (f := gOld) (g := pullback.fst f U.toBase) (x := xB)]
          have hfirst : IsIso ((pullback.fst f U.toBase).residueFieldMap (gOld xB)) := by
            rw [hBy]
            exact pullback_fst_residueFieldMap_isIso_of_elementary f s U hU y hyu
          exact IsIso.comp_isIso' hfirst hBres
        refine (isIso_residueFieldMap_comp_iff ezero.hom _ xB).mp ?_
        rw [hzeroFst, ← Category.assoc]
        exact holdResidue
      choose vt' hvt using fun i =>
        exists_of_isFiniteNeighborhoodAt f (xtail i) (Wi i) (Vtail i) (htailSpec i)
      exact ⟨W, hW, Fin.cases Vzero Vtail, Fin.cases vzero vt',
        fun i => Fin.cases hzeroFinite (fun j => (hvt j).1) i,
        fun i => Fin.cases hzeroSingle (fun j => (hvt j).2.1) i,
        fun i => Fin.cases hzeroX (fun j => (hvt j).2.2.1) i,
        fun i => Fin.cases hzeroResidue (fun j => (hvt j).2.2.2) i⟩

/-- **Stacks Project, Tag 02LN.** Finitely many distinct isolated points of a fibre of a
separated morphism locally of finite type split into separate finite open-and-closed pieces
after an elementary étale base change. -/
@[stacks 02LN, ega "IV 18.12.1" "separated case", ega "IV 18.12.3" "more general"]
theorem exists_etaleNeighborhood_decomposition
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsSeparated f]
    (s : S) (n : ℕ) (x : Fin n → X) (hx : ∀ i, f (x i) = s)
    (hx_injective : Function.Injective x)
    (hx_isolated : ∀ i, IsOpen {f.asFiber (x i)}) :
    ∃ (U : EtaleNeighborhood S s) (_ : U.IsElementary)
      (P : Option (Fin n) → Scheme.{u})
      (j : ∀ a, P a ⟶ pullback f U.toBase)
      (_ : ∀ a, IsOpenImmersion (j a))
      (_ : ∀ a, IsClosedImmersion (j a))
      (_ : IsIso (Sigma.desc j))
      (v : ∀ i, P (some i))
      (_ : ∀ i, IsFinite (j (some i) ≫ pullback.snd f U.toBase)),
      (∀ i, (j (some i) ≫ pullback.fst f U.toBase) (v i) = x i) ∧
      (∀ i, {y : P (some i) |
          (j (some i) ≫ pullback.snd f U.toBase) y = U.point} = {v i}) ∧
      (∀ i, IsIso ((j (some i) ≫ pullback.fst f U.toBase).residueFieldMap (v i))) ∧
      (∀ y : P none,
        (j none ≫ pullback.snd f U.toBase) y = U.point →
          ∀ i, (j none ≫ pullback.fst f U.toBase) y ≠ x i) := by
  classical
  obtain ⟨U, hU, V, v, hfinite, hfiber, hpoint, hres⟩ :=
    exists_etaleNeighborhood_finite_opens_of_isolated_fiber_points f s n x hx
      fun i => hx_isolated i
  let Y := pullback f U.toBase
  have hVclosed (i : Fin n) : IsClosed (V i : Set Y) := by
    have : IsFinite ((V i).ι ≫ pullback.snd f U.toBase) := hfinite i
    have : IsProper ((V i).ι) := IsProper.of_comp (V i).ι (pullback.snd f U.toBase)
    simpa [Scheme.Opens.range_ι] using (Scheme.Hom.isClosedMap (V i).ι).isClosed_range
  let Q (i : Fin n) : Y.Opens :=
    ⟨(V i : Set Y) \ ⋃ k : {k : Fin n // k.val < i.val}, (V k : Set Y), by
      have hclosedUnion : IsClosed (⋃ k : {k : Fin n // k.val < i.val}, (V k : Set Y)) :=
        isClosed_iUnion_of_finite fun k => hVclosed k.val
      simpa [Set.sdiff_eq] using (V i).2.inter hclosedUnion.isOpen_compl⟩
  have hQclosed (i : Fin n) : IsClosed (Q i : Set Y) := by
    have hopenUnion : IsOpen (⋃ k : {k : Fin n // k.val < i.val}, (V k : Set Y)) :=
      isOpen_iUnion fun k => (V k).2
    simpa [Q, Set.sdiff_eq] using (hVclosed i).inter hopenUnion.isClosed_compl
  have hQle (i : Fin n) : Q i ≤ V i := Set.sdiff_subset
  have hQdisj : Pairwise fun i k : Fin n => Disjoint (Q i : Set Y) (Q k : Set Y) := by
    intro i k hik
    rw [Set.disjoint_left]
    intro y hyi hyk
    by_cases hik' : i.val < k.val
    · exact hyk.2 (Set.mem_iUnion.mpr ⟨⟨i, hik'⟩, hyi.1⟩)
    · have hki : k.val < i.val :=
        lt_of_le_of_ne (le_of_not_gt hik') (by simpa [Fin.ext_iff] using hik.symm)
      exact hyi.2 (Set.mem_iUnion.mpr ⟨⟨k, hki⟩, hyk.1⟩)
  let T : Option (Fin n) → Y.Opens := fun a =>
    match a with
    | none => ⟨(⋃ i, (Q i : Set Y))ᶜ, (isClosed_iUnion_of_finite hQclosed).isOpen_compl⟩
    | some i => Q i
  let P : Option (Fin n) → Scheme.{u} := fun a => T a
  let j : ∀ a, P a ⟶ Y := fun a => (T a).ι
  have hopen : ∀ a, IsOpenImmersion (j a) := fun _ => inferInstance
  have hclosedP : ∀ a, IsClosedImmersion (j a) := by
    intro a
    apply IsClosedImmersion.of_isPreimmersion
    cases a with
    | none =>
        simpa [j, P, T, Scheme.Opens.range_ι] using
          (isOpen_iUnion fun i => (Q i).2).isClosed_compl
    | some i => simpa [j, P, T, Scheme.Opens.range_ι] using hQclosed i
  have hcover : ⨆ a : Option (Fin n), (j a).opensRange = ⊤ := by
    apply TopologicalSpace.Opens.ext
    ext y
    simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_univ,
      iff_true]
    show y ∈ ⋃ a : Option (Fin n), ((j a).opensRange : Set Y)
    by_cases hy : y ∈ ⋃ i, (Q i : Set Y)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨some i, by simpa [j, T, Scheme.Opens.opensRange_ι] using hi⟩
    · exact Set.mem_iUnion.mpr ⟨none, by simpa [j, T, Scheme.Opens.opensRange_ι] using hy⟩
  have hdisj : Pairwise fun a b : Option (Fin n) =>
      Disjoint (j a).opensRange (j b).opensRange := by
    intro a b hab
    simp only [j, Scheme.Opens.opensRange_ι]
    rw [← TopologicalSpace.Opens.coe_disjoint, Set.disjoint_left]
    intro y hya hyb
    cases a <;> cases b
    · exact hab rfl
    · exact hya (Set.mem_iUnion.mpr ⟨_, hyb⟩)
    · exact hyb (Set.mem_iUnion.mpr ⟨_, hya⟩)
    · exact Set.disjoint_left.mp (hQdisj (by simpa using hab)) hya hyb
  have hdesc : IsIso (Sigma.desc j) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk Y j)).mp
      (nonempty_isColimit_cofanMk_of j hcover hdisj)
  have hvfiber (i : Fin n) : ((V i).ι ≫ pullback.snd f U.toBase) (v i) = U.point := by
    have hm : v i ∈ {y : V i | ((V i).ι ≫ pullback.snd f U.toBase) y = U.point} := by
      rw [hfiber i]; simp
    exact hm
  have hvQ (i : Fin n) : (v i : Y) ∈ Q i := by
    refine ⟨(v i).property, ?_⟩
    intro hm
    obtain ⟨k, hmk⟩ := Set.mem_iUnion.mp hm
    let z : V k.val := ⟨(v i : Y), hmk⟩
    have hval : (V k.val).ι z = (V i).ι (v i) := rfl
    have hz : ((V k.val).ι ≫ pullback.snd f U.toBase) z = U.point := by
      show pullback.snd f U.toBase ((V k.val).ι z) = U.point
      rw [hval]
      exact hvfiber i
    have hzeq : z = v k.val := by
      have hmz : z ∈ {y : V k.val | ((V k.val).ι ≫ pullback.snd f U.toBase) y = U.point} := hz
      rw [hfiber k.val] at hmz
      exact hmz
    have hxx : x i = x k.val := by
      calc
        x i = ((V i).ι ≫ pullback.fst f U.toBase) (v i) := (hpoint i).symm
        _ = ((V k.val).ι ≫ pullback.fst f U.toBase) z := by
              show pullback.fst f U.toBase ((V i).ι (v i)) =
                pullback.fst f U.toBase ((V k.val).ι z)
              rw [hval]
        _ = x k.val := by rw [hzeq, hpoint k.val]
    have hv : i.val = (k.val : Fin n).val := congrArg Fin.val (hx_injective hxx)
    exact Nat.not_lt_of_ge (le_of_eq hv) k.property
  let v' : ∀ i, P (some i) := fun i => ⟨(v i : Y), hvQ i⟩
  have hkcomp (i : Fin n) : Y.homOfLE (hQle i) ≫ (V i).ι = (Q i).ι :=
    Y.homOfLE_ι (hQle i)
  have hkclosed (i : Fin n) : IsClosedImmersion (Y.homOfLE (hQle i)) := by
    have : IsOpenImmersion (Y.homOfLE (hQle i)) := inferInstance
    refine IsClosedImmersion.of_isPreimmersion _ ?_
    have hrange : IsClosed ((Y.homOfLE (hQle i)).opensRange : Set (V i)) := by
      rw [Scheme.opensRange_homOfLE]
      simpa only [TopologicalSpace.Opens.map_coe] using
        (hQclosed i).preimage (Scheme.Hom.continuous (V i).ι)
    exact hrange
  have hfinite' (i : Fin n) : IsFinite (j (some i) ≫ pullback.snd f U.toBase) := by
    have : IsOpenImmersion (Y.homOfLE (hQle i)) := inferInstance
    have : IsFinite ((V i).ι ≫ pullback.snd f U.toBase) := hfinite i
    have : IsClosedImmersion (Y.homOfLE (hQle i)) := hkclosed i
    show IsFinite ((Q i).ι ≫ pullback.snd f U.toBase)
    rw [← hkcomp i, Category.assoc]
    infer_instance
  have hUres : IsIso (U.toBase.residueFieldMap U.point) := U.isElementary_iff.mp hU
  have hsubtensor (R : Scheme.Pullback.Triplet f U.toBase)
      (hyR : R.y = U.point) (hsR : R.s = U.toBase U.point) :
      Subsingleton (Spec R.tensor) := by
    let R' : Scheme.Pullback.Triplet f U.toBase :=
      ⟨R.x, U.point, U.toBase U.point, R.hx.trans hsR, rfl⟩
    have hReq : R = R' := Scheme.Pullback.Triplet.ext rfl hyR
    have hR'sub : Subsingleton (Spec R'.tensor) := by
      have : IsIso ((S.residueFieldCongr (rfl : U.toBase U.point = U.toBase U.point)).inv ≫
          U.toBase.residueFieldMap U.point) := by simpa using hUres
      have hinl : IsIso R'.tensorInl := by
        dsimp [Scheme.Pullback.Triplet.tensorInl, Scheme.Pullback.Triplet.tensor]
        exact (IsPushout.of_hasPushout _ _).isIso_inl_of_isIso
      have : IsIso (Spec.map R'.tensorInl) := by infer_instance
      exact ⟨fun p q => (Spec.map R'.tensorInl).isEmbedding.injective (Subsingleton.elim _ _)⟩
    have : IsIso (Spec.map (Scheme.Pullback.Triplet.tensorCongr hReq).inv) := by infer_instance
    have hinj := (Spec.map (Scheme.Pullback.Triplet.tensorCongr hReq).inv).isEmbedding.injective
    exact ⟨fun p q => hinj (hR'sub.elim _ _)⟩
  have hunique (i : Fin n) (a b : Y)
      (haX : pullback.fst f U.toBase a = x i) (haU : pullback.snd f U.toBase a = U.point)
      (hbX : pullback.fst f U.toBase b = x i) (hbU : pullback.snd f U.toBase b = U.point) :
      a = b := by
    let ca := Scheme.Pullback.carrierEquiv (f := f) (g := U.toBase) a
    let cb := Scheme.Pullback.carrierEquiv (f := f) (g := U.toBase) b
    have hT : ca.1 = cb.1 := by
      refine Scheme.Pullback.Triplet.ext ?_ ?_
      · simpa [ca, cb, Scheme.Pullback.carrierEquiv] using haX.trans hbX.symm
      · simpa [ca, cb, Scheme.Pullback.carrierEquiv] using haU.trans hbU.symm
    have hcbY : cb.1.y = U.point := hbU
    have hcbS : cb.1.s = U.toBase U.point := by
      show f (pullback.fst f U.toBase b) = U.toBase U.point
      rw [hbX, hx i, U.map_point]
    refine (Scheme.Pullback.carrierEquiv (f := f) (g := U.toBase)).injective ?_
    rw [Scheme.Pullback.carrierEquiv_eq_iff]
    have : Subsingleton (Spec cb.1.tensor) := hsubtensor cb.1 hcbY hcbS
    exact ⟨hT, Subsingleton.elim _ _⟩
  refine ⟨U, hU, P, j, hopen, hclosedP, hdesc, v', hfinite', fun i => ?_, fun i => ?_,
    fun i => ?_, fun y hy i hyx => ?_⟩
  · show pullback.fst f U.toBase ((Q i).ι (v' i)) = x i
    exact hpoint i
  · ext y
    constructor
    · intro hy
      have hyQ : (j (some i)) y ∈ (Q i : Set Y) := y.property
      have hyVi : (j (some i)) y ∈ (V i : Set Y) := hQle i hyQ
      have hz : ((V i).ι ≫ pullback.snd f U.toBase)
          (⟨(j (some i)) y, hyVi⟩ : V i) = U.point := hy
      have hzeq : (⟨(j (some i)) y, hyVi⟩ : V i) = v i := (hfiber i).subset hz
      have hv'val : j (some i) (v' i) = (v i : Y) := rfl
      have hyval : (j (some i)).base y = (j (some i)).base (v' i) := by
        simpa [hv'val] using congrArg Subtype.val hzeq
      exact Set.mem_singleton_iff.mpr ((hopen (some i)).base_open.injective hyval)
    · intro hy
      obtain rfl : y = v' i := Set.mem_singleton_iff.mp hy
      exact hvfiber i
  · have hle : Q i ≤ V i := hQle i
    have hkv : Y.homOfLE hle (v' i) = v i := Scheme.homOfLE_apply' hle (v i : Y) (hvQ i)
    change IsIso (((Q i).ι ≫ pullback.fst f U.toBase).residueFieldMap (v' i))
    rw [← Y.homOfLE_ι hle, Category.assoc, isIso_residueFieldMap_comp_iff, hkv]
    exact hres i
  · have heq := hunique i (j none y) ((V i).ι (v i)) hyx hy (hpoint i) (hvfiber i)
    have hmem : (j none y : Y) ∈ Q i := by simpa [heq] using hvQ i
    exact y.property (Set.mem_iUnion.mpr ⟨i, hmem⟩)

end Stacks.Flatness

end
