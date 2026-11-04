module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Etale.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.Topology.Separation.IsolatedPoint
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapPullback
import StacksFrontier.AlgebraicGeometry.Flatness.IsolatedPointsDecomposition

/-!
# Separating finitely many isolated fibre points by one elementary étale base change

Let `f : X ⟶ S` be locally of finite type and let `x₁, …, xₙ` be points of one fibre of `f`,
each isolated in that fibre. After passing to a single elementary étale neighbourhood of the
base point, each `xᵢ` lies in an open subscheme of the base change which is finite over the new
base, meets the distinguished fibre in exactly one point, and has unchanged residue field there.

The single-point case, the property `Stacks.Flatness.IsFiniteNeighborhoodAt` recording such an
open, and its stability under a further elementary étale neighbourhood are
`Stacks.Flatness.exists_etaleNeighborhood_finiteAt` and
`Stacks.Flatness.isFiniteNeighborhoodAt_baseChange`; this file iterates them.

## Main results

* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_finite_opens_of_isolated_fiber_points`:
  finitely many isolated points of one fibre can be separated simultaneously.
* `AlgebraicGeometry.fiberIsoOfIsElementary`: base change along an elementary étale
  neighbourhood does not change the fibre over the distinguished point, and
  `AlgebraicGeometry.fiberIsoOfIsElementary_hom_fiberι` records the compatibility of this
  isomorphism with the two fibre inclusions.
* `AlgebraicGeometry.pullback_snd_residueFieldMap_isIso`: at a point of a fibre product where
  one projection is residually trivial, so is the other.

## Implementation notes

The canonical open after a further base change is the inverse image of the original open under
`CategoryTheory.Limits.pullback.map`. The unique point over the distinguished point is expressed
by a singleton-set equality, and the residue-field condition by invertibility of the canonical
map induced by the projection to `X`.

The family in the multi-point statement is indexed by `Fin n`, which allows the empty family and
repeated points; the induction on `n` adds one point at a time, composing the elementary étale
neighbourhood produced for the new point with the one produced for the earlier ones.

## References

* [Stacks Project, Tag 02LK](https://stacks.math.columbia.edu/tag/02LK)
* [Stacks Project, Tag 02LL](https://stacks.math.columbia.edu/tag/02LL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-! ### Residue fields of a base change -/

/-- Over the distinguished point of an elementary étale neighbourhood, the projection of the
base change to the original scheme induces an isomorphism of residue fields. -/
private alias isIso_residueFieldMap_pullback_fst_of_isElementary :=
  Stacks.Flatness.pullback_fst_residueFieldMap_isIso_of_elementary

/-! ### Fibres of a base change along an elementary étale neighbourhood -/

/-- Base change along an elementary étale neighbourhood does not change the fibre over the
distinguished point. -/
public noncomputable def fiberIsoOfIsElementary (f : X ⟶ S) (s : S)
    (U : EtaleNeighborhood S s) (hU : U.IsElementary) :
    (pullback.snd f U.toBase).fiber U.point ≅ f.fiber s := by
  let : IsIso U.residueFieldMap := hU
  let eSpec := Scheme.Spec.mapIso (asIso U.residueFieldMap).op
  have hbase : U.scheme.fromSpecResidueField U.point ≫ U.toBase =
      eSpec.hom ≫ S.fromSpecResidueField s := by
    dsimp [eSpec]
    simp [EtaleNeighborhood.residueFieldMap,
      Scheme.residueFieldCongr_fromSpecResidueField]
  let e₁ := pullbackLeftPullbackSndIso f U.toBase
    (U.scheme.fromSpecResidueField U.point)
  let h₂ := pullback.map f (S.fromSpecResidueField s) f
      (eSpec.hom ≫ S.fromSpecResidueField s)
      (𝟙 X) eSpec.inv (𝟙 S) (by simp) (by simp)
  let : IsIso h₂ := by
    dsimp [h₂]
    apply pullback.map_isIso
  exact e₁ ≪≫ pullback.congrHom rfl hbase ≪≫ (asIso h₂).symm

/-- The isomorphism `AlgebraicGeometry.fiberIsoOfIsElementary` is compatible with the inclusions
of the two fibres into the two total spaces. -/
public lemma fiberIsoOfIsElementary_hom_fiberι (f : X ⟶ S) (s : S)
    (U : EtaleNeighborhood S s) (hU : U.IsElementary) :
    (fiberIsoOfIsElementary f s U hU).hom ≫ f.fiberι s =
      (pullback.snd f U.toBase).fiberι U.point ≫ pullback.fst f U.toBase := by
  let : IsIso U.residueFieldMap := hU
  let eSpec := Scheme.Spec.mapIso (asIso U.residueFieldMap).op
  have hbase : U.scheme.fromSpecResidueField U.point ≫ U.toBase =
      eSpec.hom ≫ S.fromSpecResidueField s := by
    dsimp [eSpec]
    simp [EtaleNeighborhood.residueFieldMap,
      Scheme.residueFieldCongr_fromSpecResidueField]
  let e₁ := pullbackLeftPullbackSndIso f U.toBase
    (U.scheme.fromSpecResidueField U.point)
  let h₂ := pullback.map f (S.fromSpecResidueField s) f
      (eSpec.hom ≫ S.fromSpecResidueField s)
      (𝟙 X) eSpec.inv (𝟙 S) (by simp) (by simp)
  let : IsIso h₂ := by
    dsimp [h₂]
    apply pullback.map_isIso
  let eCongr : pullback f (U.scheme.fromSpecResidueField U.point ≫ U.toBase) ≅
      pullback f (eSpec.hom ≫ S.fromSpecResidueField s) :=
    pullback.congrHom rfl hbase
  have h₂fst : h₂ ≫ pullback.fst f (eSpec.hom ≫ S.fromSpecResidueField s) =
      pullback.fst f (S.fromSpecResidueField s) := by
    dsimp [h₂, pullback.map]
    rw [pullback.lift_fst]
    simp
  have hCongrfst : eCongr.hom ≫ pullback.fst f (eSpec.hom ≫ S.fromSpecResidueField s) =
      pullback.fst f (U.scheme.fromSpecResidueField U.point ≫ U.toBase) := by
    dsimp [eCongr, pullback.congrHom, pullback.map]
    rw [pullback.lift_fst]
    simp
  have htail : eCongr.hom ≫ (asIso h₂).symm.hom ≫
      pullback.fst f (S.fromSpecResidueField s) =
      pullback.fst f (U.scheme.fromSpecResidueField U.point ≫ U.toBase) := by
    rw [← h₂fst]
    simpa using hCongrfst
  show (e₁ ≪≫ eCongr ≪≫ (asIso h₂).symm).hom ≫
      pullback.fst f (S.fromSpecResidueField s) = _
  simp only [Iso.trans_hom, Category.assoc]
  rw [htail]
  exact pullbackLeftPullbackSndIso_hom_fst f U.toBase (U.scheme.fromSpecResidueField U.point)

/-- A point which is isolated in its fibre lifts to a point of the base change along an
elementary étale neighbourhood which is again isolated in its fibre. -/
private alias exists_isIsolatedPoint_pullback_of_isElementary :=
  Stacks.Flatness.exists_isolated_point_pullback_of_elementary

/-! ### Finite neighbourhoods over an elementary étale neighbourhood -/

/-- Unpacking `Stacks.Flatness.IsFiniteNeighborhoodAt` into a chosen point together with the
singleton description of the fibre over the distinguished point. -/
private lemma exists_point_of_isFiniteNeighborhoodAt (f : X ⟶ S) (x : X)
    (U : EtaleNeighborhood S (f x)) (V : (pullback f U.toBase).Opens)
    (h : Stacks.Flatness.IsFiniteNeighborhoodAt f x U V) :
    ∃ v : V,
      IsFinite (V.ι ≫ pullback.snd f U.toBase) ∧
      {y : V | (V.ι ≫ pullback.snd f U.toBase) y = U.point} = {v} ∧
      (V.ι ≫ pullback.fst f U.toBase) v = x ∧
      IsIso ((V.ι ≫ pullback.fst f U.toBase).residueFieldMap v) := by
  rcases h with ⟨hfin, ⟨v, hv, huv⟩, hrest⟩
  refine ⟨v, hfin, ?_, (hrest v hv).1, (hrest v hv).2⟩
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact ⟨huv z, by rintro rfl; exact hv⟩

/-- Repackaging a chosen point and the singleton description of the fibre over the distinguished
point into `Stacks.Flatness.IsFiniteNeighborhoodAt`. -/
private lemma isFiniteNeighborhoodAt_of_exists_point (f : X ⟶ S) (x : X)
    (U : EtaleNeighborhood S (f x)) (V : (pullback f U.toBase).Opens)
    (v : V) (hfin : IsFinite (V.ι ≫ pullback.snd f U.toBase))
    (hsingle : {z : V | (V.ι ≫ pullback.snd f U.toBase) z = U.point} = {v})
    (hx : (V.ι ≫ pullback.fst f U.toBase) v = x)
    (hres : IsIso ((V.ι ≫ pullback.fst f U.toBase).residueFieldMap v)) :
    Stacks.Flatness.IsFiniteNeighborhoodAt f x U V := by
  have hv : (V.ι ≫ pullback.snd f U.toBase) v = U.point :=
    hsingle.symm.subset (Set.mem_singleton v)
  have huniq : ∀ z : V, (V.ι ≫ pullback.snd f U.toBase) z = U.point → z = v :=
    fun z hz => hsingle.subset hz
  refine ⟨hfin, ⟨v, hv, huniq⟩, fun z hz => ?_⟩
  obtain rfl := huniq z hz
  exact ⟨hx, hres⟩

/-- Finiteness, a unique point over `t`, and an invertible residue field map at that point are
transported along an isomorphism of the sources. -/
public lemma finite_unique_isIso_residueFieldMap_of_iso {A B T Y : Scheme.{u}} (e : A ≅ B)
    {pA : A ⟶ T} {pB : B ⟶ T} (hp : e.hom ≫ pB = pA) {gA : A ⟶ Y} {gB : B ⟶ Y}
    (hg : e.hom ≫ gB = gA) {t : T} {a : A} (hfin : IsFinite pA) (hpa : pA a = t)
    (huniq : ∀ a', pA a' = t → a' = a) (hres : IsIso (gA.residueFieldMap a)) :
    IsFinite pB ∧ {b : B | pB b = t} = {e.hom a} ∧ IsIso (gB.residueFieldMap (e.hom a)) := by
  subst hp hg
  have hinv : ∀ b, e.hom (e.inv b) = b := fun b => by
    show (e.inv ≫ e.hom) b = b
    rw [e.inv_hom_id]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← Iso.inv_hom_id_assoc e pB]
    infer_instance
  · ext b
    refine ⟨fun hb => ?_, by rintro rfl; exact hpa⟩
    have hb' : (e.hom ≫ pB) (e.inv b) = t := by
      rw [Scheme.Hom.comp_apply, hinv]
      exact hb
    rw [Set.mem_singleton_iff, ← hinv b, huniq (e.inv b) hb']
  · rw [Scheme.residueFieldMap_comp] at hres
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (e.hom.residueFieldMap a) inferInstance hres

/-- Let `U` be an elementary étale neighbourhood of `s`, let `y` be a point of the base change
`pullback f U.toBase` over `x` and the distinguished point, and let `V` be a finite neighbourhood
of the base change at `y` over an étale neighbourhood `T` of the distinguished point. Then the
image of `V` is a finite open of the base change of `f` along the composite neighbourhood, with
a unique point over its distinguished point, lying over `x` with unchanged residue field. -/
public lemma exists_finite_open_of_isFiniteNeighborhoodAt_pullback_snd (f : X ⟶ S) (s : S)
    (U : EtaleNeighborhood S s) (hU : U.IsElementary) (x : X) (y : ↑(pullback f U.toBase))
    (hyx : pullback.fst f U.toBase y = x) (hyu : pullback.snd f U.toBase y = U.point)
    (T : EtaleNeighborhood U.scheme U.point)
    (V : (pullback (pullback.snd f U.toBase) T.toBase).Opens)
    (hV : Stacks.Flatness.IsFiniteNeighborhoodAt (pullback.snd f U.toBase) y
      { scheme := T.scheme
        point := T.point
        toBase := T.toBase
        map_point := T.map_point.trans hyu.symm } V) :
    ∃ (W : (pullback f (T.toBase ≫ U.toBase)).Opens) (w : W),
      IsFinite (W.ι ≫ pullback.snd f (T.toBase ≫ U.toBase)) ∧
      {z : W | (W.ι ≫ pullback.snd f (T.toBase ≫ U.toBase)) z = T.point} = {w} ∧
      (W.ι ≫ pullback.fst f (T.toBase ≫ U.toBase)) w = x ∧
      IsIso ((W.ι ≫ pullback.fst f (T.toBase ≫ U.toBase)).residueFieldMap w) := by
  let q := pullback.snd f U.toBase
  obtain ⟨hBfinite, ⟨vB, hBpoint, hBunique⟩, hBrest⟩ :
      IsFinite (V.ι ≫ pullback.snd q T.toBase) ∧
        (∃! v : V, (V.ι ≫ pullback.snd q T.toBase) v = T.point) ∧
        ∀ v : V, (V.ι ≫ pullback.snd q T.toBase) v = T.point →
          (V.ι ≫ pullback.fst q T.toBase) v = y ∧
            IsIso ((V.ι ≫ pullback.fst q T.toBase).residueFieldMap v) := hV
  let eAssoc := pullbackLeftPullbackSndIso f U.toBase T.toBase
  let j := V.ι ≫ eAssoc.hom
  have : IsOpenImmersion j := inferInstance
  let ezero := j.isoOpensRange
  have hAssocSnd : eAssoc.hom ≫ pullback.snd f (T.toBase ≫ U.toBase) =
      pullback.snd q T.toBase :=
    pullbackLeftPullbackSndIso_hom_snd f U.toBase T.toBase
  have hAssocFst : eAssoc.hom ≫ pullback.fst f (T.toBase ≫ U.toBase) =
      pullback.fst q T.toBase ≫ pullback.fst f U.toBase :=
    pullbackLeftPullbackSndIso_hom_fst f U.toBase T.toBase
  have hι : ezero.hom ≫ j.opensRange.ι = V.ι ≫ eAssoc.hom := Scheme.Hom.isoOpensRange_hom_ι j
  have hzeroProj : ezero.hom ≫ j.opensRange.ι ≫ pullback.snd f (T.toBase ≫ U.toBase) =
      V.ι ≫ pullback.snd q T.toBase := by
    rw [reassoc_of% hι, hAssocSnd]
  have hzeroFst : ezero.hom ≫ j.opensRange.ι ≫ pullback.fst f (T.toBase ≫ U.toBase) =
      (V.ι ≫ pullback.fst q T.toBase) ≫ pullback.fst f U.toBase := by
    rw [reassoc_of% hι, hAssocFst, Category.assoc]
  have hy : (V.ι ≫ pullback.fst q T.toBase) vB = y := (hBrest vB hBpoint).1
  let gOld := V.ι ≫ pullback.fst q T.toBase
  let xB : V.toScheme := vB
  have hfirst : IsIso ((pullback.fst f U.toBase).residueFieldMap (gOld xB)) := by
    have hxy : gOld xB = y := hy
    rw [hxy]
    exact isIso_residueFieldMap_pullback_fst_of_isElementary f s U hU y hyu
  have hold : IsIso ((gOld ≫ pullback.fst f U.toBase).residueFieldMap xB) := by
    rw [Scheme.residueFieldMap_comp (f := gOld) (g := pullback.fst f U.toBase) (x := xB)]
    exact IsIso.comp_isIso' hfirst (hBrest vB hBpoint).2
  obtain ⟨hfin, hsingle, hres⟩ := finite_unique_isIso_residueFieldMap_of_iso ezero hzeroProj
    hzeroFst hBfinite hBpoint hBunique hold
  refine ⟨j.opensRange, ezero.hom vB, hfin, hsingle, ?_, hres⟩
  show (ezero.hom ≫ j.opensRange.ι ≫ pullback.fst f (T.toBase ≫ U.toBase)) vB = x
  rw [hzeroFst]
  exact (congrArg (pullback.fst f U.toBase) hy).trans hyx

/-- A finite neighbourhood over an elementary étale neighbourhood `U`, with its chosen point,
persists after a further elementary étale neighbourhood `T` of the distinguished point. -/
public lemma exists_finite_open_comp_of_finite_open (f : X ⟶ S) (s : S) (x : X) (hx : f x = s)
    (U : EtaleNeighborhood S s) (V : (pullback f U.toBase).Opens) (v : V)
    (hfin : IsFinite (V.ι ≫ pullback.snd f U.toBase))
    (hsingle : {z : V | (V.ι ≫ pullback.snd f U.toBase) z = U.point} = {v})
    (hxv : (V.ι ≫ pullback.fst f U.toBase) v = x)
    (hres : IsIso ((V.ι ≫ pullback.fst f U.toBase).residueFieldMap v))
    (T : EtaleNeighborhood U.scheme U.point) (hT : T.IsElementary) :
    ∃ (W : (pullback f (T.toBase ≫ U.toBase)).Opens) (w : W),
      IsFinite (W.ι ≫ pullback.snd f (T.toBase ≫ U.toBase)) ∧
      {z : W | (W.ι ≫ pullback.snd f (T.toBase ≫ U.toBase)) z = T.point} = {w} ∧
      (W.ι ≫ pullback.fst f (T.toBase ≫ U.toBase)) w = x ∧
      IsIso ((W.ι ≫ pullback.fst f (T.toBase ≫ U.toBase)).residueFieldMap w) := by
  subst hx
  exact ⟨_, exists_point_of_isFiniteNeighborhoodAt f x _ _
    (Stacks.Flatness.isFiniteNeighborhoodAt_baseChange f x U V
      (isFiniteNeighborhoodAt_of_exists_point f x U V v hfin hsingle hxv hres) T hT)⟩

/-! ### Finitely many isolated points at once -/

/-- **Stacks Project, Tag 02LL.** Several isolated points in one fibre can
simultaneously be made finite over an elementary étale neighborhood. -/
@[stacks 02LL]
public theorem exists_elementaryEtaleNeighborhood_finite_opens_of_isolated_fiber_points
    (f : X ⟶ S) [LocallyOfFiniteType f] (s : S) (n : ℕ) (x : Fin n → X) (hx : ∀ i, f (x i) = s)
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
        obtain ⟨U, hU, Vt, vt, htail⟩ :=
          ih (fun i => x i.succ) (fun i => hx i.succ) fun i => hxi i.succ
        obtain ⟨y, hyx, hyu, hyisolated⟩ :=
          exists_isIsolatedPoint_pullback_of_isElementary f s U hU (x 0) (hx 0) (hxi 0)
        obtain ⟨N⟩ :=
          Stacks.Flatness.exists_etaleNeighborhood_finiteAt (pullback.snd f U.toBase) y
            hyisolated
        let N' : EtaleNeighborhood U.scheme U.point :=
          { scheme := N.neighborhood.scheme
            point := N.neighborhood.point
            toBase := N.neighborhood.toBase
            map_point := N.neighborhood.map_point.trans hyu }
        have hN' : N'.IsElementary := by
          rw [EtaleNeighborhood.isElementary_iff]
          simpa [N'] using (N.neighborhood.isElementary_iff).mp N.elementary
        obtain ⟨Vzero, vzero, hzero⟩ :=
          exists_finite_open_of_isFiniteNeighborhoodAt_pullback_snd f s U hU (x 0) y hyx hyu
            N' N.openSubscheme N.spec
        have hspec := fun i => exists_finite_open_comp_of_finite_open f s (x i.succ) (hx i.succ)
          U (Vt i) (vt i) (htail.1 i) (htail.2.1 i) (htail.2.2.1 i) (htail.2.2.2 i) N' hN'
        let V : Fin (n + 1) → (pullback f (U.comp N').toBase).Opens :=
          Fin.cases Vzero fun i => (hspec i).choose
        let v : ∀ i, V i := Fin.cases vzero fun i => (hspec i).choose_spec.choose
        refine ⟨U.comp N', hU.comp hN', V, v, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
        · exact Fin.cases hzero.1 (fun j => (hspec j).choose_spec.choose_spec.1) i
        · exact Fin.cases hzero.2.1 (fun j => (hspec j).choose_spec.choose_spec.2.1) i
        · exact Fin.cases hzero.2.2.1 (fun j => (hspec j).choose_spec.choose_spec.2.2.1) i
        · exact Fin.cases hzero.2.2.2 (fun j => (hspec j).choose_spec.choose_spec.2.2.2) i

end AlgebraicGeometry

end
