module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.QuasiFiniteEtaleLocalisation
public import StacksFrontier.Topology.Separation.IsolatedPoint

/-!
# Splitting off isolated fibre points by an etale base change

Let `f : X ⟶ S` be separated and locally of finite type, and let `x₁, …, xₙ` be pairwise
distinct isolated points of one fibre `X_s`. After passing to a single etale neighbourhood
`(U, u)` of `s`, the base change `X ×_S U` decomposes into open-and-closed pieces
`W ⊔ ⨿ᵢ ⨿ⱼ Vᵢⱼ` in which every `Vᵢⱼ` is finite over `U`, meets the distinguished fibre in one
point `vᵢⱼ` lying over `xᵢ` with `κ(u) ⊆ κ(vᵢⱼ)` purely inseparable, and the distinguished
fibre of `W` contains no point lying over any `xᵢ`.

This is the counterpart, for an arbitrary etale neighbourhood, of the decomposition over an
*elementary* etale neighbourhood: dropping the triviality of the residue extension costs only
that a single `xᵢ` may now be met by several pieces, and that the residue extensions are
purely inseparable instead of trivial.

## Main results

* `AlgebraicGeometry.exists_etaleNeighborhood_purelyInseparable_decomposition`

## Implementation notes

The base change is written `X ×_S U`, in Mathlib's order, and its pieces are indexed by
`Option (Σ i, Fin (m i))`: `none` is the residual piece `W` and `some ⟨i, j⟩` is `Vᵢⱼ`. The
decomposition is recorded as a family of opens which is pairwise disjoint, exhausts the space
and consists of open-and-closed subsets, rather than as an isomorphism from a coproduct.

The pieces come from the finite opens over a single etale neighbourhood, which may overlap:
each piece is cut down to the part of it that misses the finitely many other pieces. Those
pieces are closed, because a finite morphism is proper and a piece is finite over the
neighbourhood, so the cut-down piece is again open and closed and still contains its
distinguished point. The purely inseparable residue extension transports along the resulting
closed immersion of a piece into the original open, whose residue field map at the
distinguished point is an isomorphism.

## References

* [Stacks Project, Tag 02LO](https://stacks.math.columbia.edu/tag/02LO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 02LO.** Finitely many pairwise distinct isolated points of a fibre of
a separated morphism locally of finite type split into finite open-and-closed pieces after an
étale base change.  Each distinguished piece has singleton fibre and purely inseparable
residue-field extension, and the residual piece contains none of the specified points. -/
@[stacks 02LO, ega "IV 18.12.1" "separated case", ega "IV 18.12.3" "partial"]
public theorem exists_etaleNeighborhood_purelyInseparable_decomposition
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsSeparated f]
    (n : ℕ) (s : S) (x : Fin n → f.fiber s) (hx : Function.Injective x)
    (hxi : ∀ i, IsIsolatedPoint (x i)) :
    ∃ (U : EtaleNeighborhood S s)
      (m : Fin n → ℕ)
      (D : Option (Σ i, Fin (m i)) → (pullback f U.toBase).Opens)
      (v : ∀ i j, D (some ⟨i, j⟩)),
      Set.PairwiseDisjoint Set.univ (fun k ↦ (D k).1) ∧
      (⋃ k, (D k).1) = Set.univ ∧
      (∀ k, IsClopen (D k).1) ∧
      (∀ i j,
        let V := D (some ⟨i, j⟩)
        let g := V.ι ≫ pullback.snd f U.toBase
        IsFinite g ∧
          g ⁻¹' {U.point} = {v i j} ∧
          (V.ι ≫ pullback.fst f U.toBase) (v i j) = f.fiberι s (x i) ∧
          ∃ hvu : g (v i j) = U.point,
            ((U.scheme.residueFieldCongr hvu).inv ≫
              g.residueFieldMap (v i j)).hom.IsPurelyInseparable) ∧
      (∀ w : D none,
        ((D none).ι ≫ pullback.snd f U.toBase) w = U.point →
          ∀ i, ((D none).ι ≫ pullback.fst f U.toBase) w ≠ f.fiberι s (x i)) := by
  have of_bijective {E K : Type u} [Field E] [Field K] {φ : E →+* K}
      (hφ : Function.Bijective φ) : φ.IsPurelyInseparable := by
    algebraize [φ]
    exact (AlgEquiv.ofBijective (Algebra.ofId E K) hφ).isPurelyInseparable
  have hcomp_pure {X₁ Y₁ Z₁ : Scheme.{u}} (q : X₁ ⟶ Y₁) (g : Y₁ ⟶ Z₁) {f₁ : X₁ ⟶ Z₁}
      (hf : q ≫ g = f₁) {x₁ : X₁} [IsIso (q.residueFieldMap x₁)] {y₁ : Y₁} {z₁ : Z₁}
      (hy : q x₁ = y₁) (hz : g y₁ = z₁) (hfz : f₁ x₁ = z₁)
      (h : ((Z₁.residueFieldCongr hz).inv ≫ g.residueFieldMap y₁).hom.IsPurelyInseparable) :
      ((Z₁.residueFieldCongr hfz).inv ≫ f₁.residueFieldMap x₁).hom.IsPurelyInseparable := by
    subst hf hy hz
    rw [Scheme.residueFieldMap_comp]
    exact h.comp (of_bijective
      ((ConcreteCategory.isIso_iff_bijective (q.residueFieldMap x₁)).mp inferInstance))
  have hcut {P₁ U₁ : Scheme.{u}} (p : P₁ ⟶ U₁) {A T : P₁.Opens} (hTA : T ≤ A)
      (hT : IsClosed (T : Set P₁)) {u₁ : U₁} {v₁ : (A : Scheme)} {t : (T : Scheme)}
      (ht : T.ι t = A.ι v₁) [IsFinite (A.ι ≫ p)] (hfib : (A.ι ≫ p) ⁻¹' {u₁} = {v₁})
      (hvu : (A.ι ≫ p) v₁ = u₁)
      (hpure : ((U₁.residueFieldCongr hvu).inv ≫
        (A.ι ≫ p).residueFieldMap v₁).hom.IsPurelyInseparable) :
      IsFinite (T.ι ≫ p) ∧ (T.ι ≫ p) ⁻¹' {u₁} = {t} ∧
        ∃ hvu' : (T.ι ≫ p) t = u₁,
          ((U₁.residueFieldCongr hvu').inv ≫
            (T.ι ≫ p).residueFieldMap t).hom.IsPurelyInseparable := by
    let q := P₁.homOfLE hTA
    have hqι : q ≫ A.ι = T.ι := P₁.homOfLE_ι hTA
    have hq : q ≫ A.ι ≫ p = T.ι ≫ p := by rw [← Category.assoc, hqι]
    have hqpt (w : (T : Scheme)) : A.ι (q w) = T.ι w := by rw [← Scheme.Hom.comp_apply, hqι]
    have hqv : q t = v₁ := A.ι.isOpenEmbedding.injective ((hqpt t).trans ht)
    have : IsIso (q.residueFieldMap t) :=
      inferInstanceAs (IsIso ((P₁.homOfLE hTA).residueFieldMap t))
    have : IsClosedImmersion q := IsClosedImmersion.of_isPreimmersion q (by
      rw [← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE hTA]
      exact hT.preimage A.ι.continuous)
    have hvu' : (T.ι ≫ p) t = u₁ := by rwa [← hq, Scheme.Hom.comp_apply, hqv]
    refine ⟨by rw [← hq]; infer_instance, ?_, hvu',
      hcomp_pure q (A.ι ≫ p) hq hqv hvu hvu' hpure⟩
    ext w
    refine ⟨fun hw => T.ι.isOpenEmbedding.injective ?_, by rintro rfl; exact hvu'⟩
    have hqw : q w = v₁ := by
      rw [← Set.mem_singleton_iff, ← hfib]
      change (q ≫ A.ι ≫ p) w = u₁
      rwa [hq]
    rw [← hqpt, ← hqpt, hqw, hqv]
  have hisolated {p : f.fiber s} (hp : IsIsolatedPoint p) :
      IsIsolatedPoint (f.asFiber (f.fiberι s p)) := by
    have hsets : (f ⁻¹' ({s} : Set S) : Set X) = f ⁻¹' ({f (f.fiberι s p)} : Set S) := by
      rw [show f (f.fiberι s p) = s from (f.fiberHomeo s p).2]
    let e : f.fiber s ≃ₜ f.fiber (f (f.fiberι s p)) :=
      (f.fiberHomeo s).trans ((Homeomorph.setCongr hsets).trans (f.fiberHomeo _).symm)
    have he : e p = f.asFiber (f.fiberι s p) := by
      apply (f.fiberHomeo (f (f.fiberι s p))).injective
      change (f.fiberHomeo (f (f.fiberι s p)))
        ((f.fiberHomeo s).trans ((Homeomorph.setCongr hsets).trans (f.fiberHomeo _).symm) p) = _
      rw [Homeomorph.trans_apply, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
      apply Subtype.ext
      simp [Homeomorph.setCongr]
    change IsOpen ({f.asFiber (f.fiberι s p)} : Set (f.fiber (f (f.fiberι s p))))
    rw [← he, ← Set.image_singleton]
    exact e.isOpen_image.mpr (by simpa [IsIsolatedPoint] using hp)
  obtain ⟨U, m, V, v, hdata, hdistinct, hexhaust⟩ :=
    exists_etale_finite_opens_of_isolated_fiber_points f n s (fun i => f.fiberι s (x i))
      (fun i => (f.fiberHomeo s (x i)).2)
      (fun i j hij => hx ((f.fiberHomeo s).injective (Subtype.ext (by simpa using hij))))
      fun i => hisolated (hxi i)
  let P := pullback f U.toBase
  let I := Σ i, Fin (m i)
  let A (a : I) : P.Opens := V a.1 a.2
  let z (a : I) : P := (A a).ι (v a.1 a.2)
  have hAclopen (a : I) : IsClopen (A a : Set P) := by
    have : IsFinite ((A a).ι ≫ pullback.snd f U.toBase) := (hdata a.1 a.2).1
    have : IsFinite (A a).ι := IsFinite.of_comp (A a).ι (pullback.snd f U.toBase)
    exact ⟨by simpa [Scheme.Hom.opensRange, Scheme.Opens.opensRange_ι] using
      (A a).ι.isClosedMap.isClosed_range, (A a).isOpen⟩
  let T (a : I) : Set P := (A a : Set P) \ ⋃ b ∈ ({a}ᶜ : Set I), (A b : Set P)
  have hTclopen (a : I) : IsClopen (T a) := (hAclopen a).diff
    ⟨(Set.toFinite _).isClosed_biUnion fun b _ => (hAclopen b).isClosed,
      isOpen_biUnion fun b _ => (A b).isOpen⟩
  have hTdisj : Pairwise (Function.onFun Disjoint T) := fun a b hab => Set.disjoint_left.mpr
    fun y hya hyb => hya.2 (Set.mem_biUnion (Set.mem_compl_singleton_iff.mpr hab.symm) hyb.1)
  have hzT (a : I) : z a ∈ T a := by
    refine ⟨?_, fun hy => ?_⟩
    · rw [← Scheme.Opens.opensRange_ι (A a)]
      exact Scheme.Hom.mem_opensRange.mpr ⟨v a.1 a.2, rfl⟩
    obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.mp hy
    rw [← Scheme.Opens.opensRange_ι (A b)] at hzb
    obtain ⟨w, hw⟩ := Scheme.Hom.mem_opensRange.mp hzb
    have hwv : w = v b.1 b.2 := by
      have hwmem : w ∈ ((A b).ι ≫ pullback.snd f U.toBase) ⁻¹' {U.point} := by
        change pullback.snd f U.toBase ((A b).ι w) = U.point
        rw [hw]
        exact (hdata a.1 a.2).2.2.2.1
      rwa [(hdata b.1 b.2).2.1] at hwmem
    exact Set.mem_compl_singleton_iff.mp hb
      (hdistinct (hw.symm.trans (congrArg (A b).ι hwv))).symm
  obtain ⟨hDdisj, hDcover, hDclopen⟩ :
      Set.PairwiseDisjoint Set.univ (fun k : Option I ↦ k.elim (⋃ a, T a)ᶜ T) ∧
        (⋃ k : Option I, k.elim (⋃ a, T a)ᶜ T) = Set.univ ∧
        ∀ k : Option I, IsClopen (k.elim (⋃ a, T a)ᶜ T) := by
    refine ⟨?_, Set.eq_univ_of_forall fun y => ?_, ?_⟩
    · rintro (_ | a) - (_ | b) - hkl
      · exact (hkl rfl).elim
      · exact disjoint_compl_left.mono_right (Set.subset_iUnion T b)
      · exact (disjoint_compl_left.mono_right (Set.subset_iUnion T a)).symm
      · exact hTdisj fun h => hkl (congrArg some h)
    · by_cases hy : y ∈ ⋃ a, T a
      · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hy
        exact Set.mem_iUnion.mpr ⟨some a, ha⟩
      · exact Set.mem_iUnion.mpr ⟨none, hy⟩
    · rintro (_ | a)
      · exact (isClopen_iUnion_of_finite hTclopen).compl
      · exact hTclopen a
  let D (k : Option I) : P.Opens := ⟨k.elim (⋃ a, T a)ᶜ T, (hDclopen k).isOpen⟩
  refine ⟨U, m, D, fun i j => ⟨z ⟨i, j⟩, hzT ⟨i, j⟩⟩, hDdisj, hDcover, hDclopen, ?_, ?_⟩
  · intro i j
    have : IsFinite ((A ⟨i, j⟩).ι ≫ pullback.snd f U.toBase) := (hdata i j).1
    obtain ⟨-, hfib, hzX, hvu, -, hpure⟩ := hdata i j
    obtain ⟨h₁, h₂, h₃⟩ := hcut
      (pullback.snd f U.toBase) (A := A ⟨i, j⟩) (T := D (some ⟨i, j⟩)) (v₁ := v i j)
      (t := ⟨z ⟨i, j⟩, hzT ⟨i, j⟩⟩)
      (fun _ hy => hy.1) (hTclopen _).isClosed rfl hfib hvu hpure
    exact ⟨h₁, h₂, hzX, h₃⟩
  · intro w hwbase i hEq
    obtain ⟨j, hj⟩ := hexhaust i ((D none).ι w) hwbase hEq
    exact (show (D none).ι w ∉ ⋃ a, T a from w.2) (Set.mem_iUnion.mpr ⟨⟨i, j⟩, hj ▸ hzT ⟨i, j⟩⟩)

end AlgebraicGeometry

end
