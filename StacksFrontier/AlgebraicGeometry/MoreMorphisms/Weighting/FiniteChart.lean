module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FibreSumTerm
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.QuasiFiniteEtaleLocalisation
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite open charts of a locally quasi-finite morphism

A locally quasi-finite morphism locally of finite type becomes, near a chosen point of the
source and after an étale base change of the target, a finite morphism on an open piece of the
base change which meets the distinguished fibre in a single point with purely inseparable
residue-field extension. This file packages the chart produced that way together with the
comparison maps needed to transport such a chart along a further base change.

## Main definitions

* `AlgebraicGeometry.baseChangedChartMap` compares a chart of `f` base changed along `q` with a
  chart of `f` base changed along the composite.

## Main results

* `AlgebraicGeometry.exists_finite_opens_chart_at_point`: existence of a finite open chart
  through a point of the source, together with the fact that its distinguished points exhaust
  the fibre above that point.
* `AlgebraicGeometry.exists_isOpen_preimage_subset_of_isFinite`: a finite morphism sends a
  neighbourhood of a fibre to a neighbourhood of its image point.
* `AlgebraicGeometry.separableDegreeWeightedFiberSum_eventually_eq_zero`: the weighted fibre sum
  of a closed open piece with empty fibre vanishes near the corresponding point.
* `AlgebraicGeometry.fiber_eq_empty_of_forall_ne`: the residual piece of an open decomposition
  has empty distinguished fibre once it avoids every point of that fibre.
* `AlgebraicGeometry.exists_open_neighborhood_eq_of_isLocallyConstant_comp_of_isOpenMap` and
  `AlgebraicGeometry.eventually_eq_of_openMap_comp`: two general-topology lemmas transporting
  local constancy of an integer-valued function along an open map.

## Implementation notes

A chart of `f : X ⟶ Y` over an étale `g : V ⟶ Y` is a pair of morphisms `h : U ⟶ X`,
`π : U ⟶ V` whose induced map to `X ×_Y V` is an open immersion. Base changing the chart along
`q : S ⟶ V` produces a chart of `f` over `q ≫ g`, and the resulting open immersion into
`X ×_Y S` is `AlgebraicGeometry.baseChangedChartMap`.

## References

* [Stacks Project, Tag 02LM](https://stacks.math.columbia.edu/tag/02LM)
* [Stacks Project, Tag 0F3B](https://stacks.math.columbia.edu/tag/0F3B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped Topology

universe u

namespace AlgebraicGeometry

/-- The comparison map from a chart of `f` base changed along `q` to the base change of `f`
along the composite `q ≫ g`. -/
def baseChangedChartMap
    {X Y U V S : Scheme.{u}} (f : X ⟶ Y) (g : V ⟶ Y) (q : S ⟶ V)
    (h : U ⟶ X) (π : U ⟶ V) (comm : h ≫ f = π ≫ g) :
    pullback π q ⟶ pullback f (q ≫ g) :=
  pullback.map π q (pullback.snd f g) q
      (pullback.lift h π comm) (𝟙 S) (𝟙 V)
      (by simp only [Category.comp_id, pullback.lift_snd]) (by simp) ≫
    (pullbackLeftPullbackSndIso f g q).hom

/-- The base change of a chart is again a chart. -/
theorem baseChangedChartMap_isOpenImmersion
    {X Y U V S : Scheme.{u}} (f : X ⟶ Y) (g : V ⟶ Y) (q : S ⟶ V)
    (h : U ⟶ X) (π : U ⟶ V) (comm : h ≫ f = π ≫ g)
    [IsOpenImmersion (pullback.lift h π comm)] :
    IsOpenImmersion (baseChangedChartMap f g q h π comm) := by
  unfold baseChangedChartMap
  infer_instance

/-- The base-changed chart is compatible with the projections to the source. -/
theorem baseChangedChartMap_fst
    {X Y U V S : Scheme.{u}} (f : X ⟶ Y) (g : V ⟶ Y) (q : S ⟶ V)
    (h : U ⟶ X) (π : U ⟶ V) (comm : h ≫ f = π ≫ g) :
    baseChangedChartMap f g q h π comm ≫ pullback.fst f (q ≫ g) =
      pullback.fst π q ≫ h := by
  unfold baseChangedChartMap
  rw [Category.assoc, pullbackLeftPullbackSndIso_hom_fst]
  dsimp only [pullback.map]
  rw [← Category.assoc, pullback.lift_fst]
  simp only [Category.assoc, pullback.lift_fst]

/-- The base-changed chart is compatible with the projections to the base. -/
theorem baseChangedChartMap_snd
    {X Y U V S : Scheme.{u}} (f : X ⟶ Y) (g : V ⟶ Y) (q : S ⟶ V)
    (h : U ⟶ X) (π : U ⟶ V) (comm : h ≫ f = π ≫ g) :
    baseChangedChartMap f g q h π comm ≫ pullback.snd f (q ≫ g) =
      pullback.snd π q := by
  unfold baseChangedChartMap
  rw [Category.assoc, pullbackLeftPullbackSndIso_hom_snd]
  dsimp only [pullback.map]
  exact pullback.lift_snd _ _ _

/-- Through any point of the source of a locally quasi-finite morphism locally of finite type
there is a finite open chart over an étale neighbourhood of its image: finitely many opens of
the base change, each finite over the neighbourhood, each meeting the distinguished fibre in a
single point lying over the chosen point with purely inseparable residue-field extension, and
together exhausting that fibre. -/
theorem exists_finite_opens_chart_at_point
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (x : X) :
    ∃ (N : EtaleNeighborhood Y (f x)) (m : ℕ)
      (D : Fin m → (pullback f N.toBase).Opens)
      (a : ∀ j, D j),
      (∀ j,
        let π := (D j).ι ≫ pullback.snd f N.toBase
        IsFinite π ∧ π ⁻¹' {N.point} = {a j} ∧
          ((D j).ι ≫ pullback.fst f N.toBase) (a j) = x ∧
          ∃ ha : π (a j) = N.point,
            ((N.scheme.residueFieldCongr ha).inv ≫
              π.residueFieldMap (a j)).hom.IsPurelyInseparable) ∧
      ∀ z : ↥(pullback f N.toBase), pullback.snd f N.toBase z = N.point →
        pullback.fst f N.toBase z = x → ∃ j, (D j).ι (a j) = z := by
  have hxiso : IsIsolatedPoint (f.asFiber x) :=
    (quasiFiniteAt_tfae f x).out 1 2 rfl rfl (by decide) (by decide) |>.mp
      ((forall_quasiFiniteAt_iff f).mpr ⟨inferInstance, inferInstance⟩ x)
  obtain ⟨N, m, D, a, hspec, _, hcover⟩ :=
    exists_etale_finite_opens_of_isolated_fiber_points f 1 (f x) (fun _ ↦ x)
      (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _) (fun _ ↦ hxiso)
  refine ⟨N, m 0, D 0, a 0, fun j ↦ ?_, hcover 0⟩
  obtain ⟨hf, hfi, hxj, hres⟩ := hspec 0 j
  exact ⟨hf, hfi, hxj, hres.imp fun _ hh ↦ hh.2⟩

/-- A finite morphism `p : U ⟶ T` carries an open subset of `U` containing the whole fibre over
`t` to an open neighbourhood of `t`: there is an open `T'` containing `t` such that every point
of `U` above `T'` lands in the given open. -/
theorem exists_isOpen_preimage_subset_of_isFinite
    {U Y T : Scheme.{u}} (p : U ⟶ T) [IsFinite p]
    (k : U ⟶ Y) (t : T) (V : Y.Opens)
    (hfiber : ∀ u, p u = t → k u ∈ V) :
    ∃ T' : T.Opens, t ∈ T' ∧ ∀ u, p u ∈ T' → k u ∈ V := by
  obtain ⟨T', hsub, hopen, ht⟩ := mem_nhds_iff.mp <|
    p.isClosedMap.eventually_nhds_fiber t fun u hu ↦
      (V.2.preimage k.continuous).mem_nhds (hfiber u hu)
  exact ⟨⟨T', hopen⟩, ht, fun u hu ↦ hsub hu u rfl⟩

/-- The distinguished fibre of the residual piece of an open decomposition is empty once that
piece avoids every point of the fibre being split. -/
theorem fiber_eq_empty_of_forall_ne
    {P V : Scheme.{u}} (π : P ⟶ V) {n : ℕ} (v : V)
    (x : Fin n → π.fiber v) (hx : Function.Surjective x)
    (E : EtaleNeighborhood V v) (D₀ : (pullback π E.toBase).Opens)
    (hnone : ∀ w : D₀, (D₀.ι ≫ pullback.snd π E.toBase) w = E.point →
      ∀ i, (D₀.ι ≫ pullback.fst π E.toBase) w ≠ π.fiberι v (x i)) :
    ((D₀.ι ≫ pullback.snd π E.toBase) ⁻¹' {E.point}) = ∅ := by
  ext w
  refine ⟨fun hw ↦ ?_, fun hw ↦ by cases hw⟩
  have hw' : (D₀.ι ≫ pullback.snd π E.toBase) w = E.point := by simpa using hw
  let z : P := (D₀.ι ≫ pullback.fst π E.toBase) w
  have hz : π z = v := by
    have hc := congrArg (fun h : pullback π E.toBase ⟶ V ↦ h (D₀.ι w))
      (pullback.condition (f := π) (g := E.toBase))
    change (pullback.snd π E.toBase) (D₀.ι w) = E.point at hw'
    change π z = E.toBase ((pullback.snd π E.toBase) (D₀.ι w)) at hc
    rwa [hw', E.map_point] at hc
  obtain ⟨i, hi⟩ := hx ((π.fiberHomeo v).symm ⟨z, by simpa using hz⟩)
  have hzx : z = π.fiberι v (x i) := by
    rw [hi]
    exact (π.fiberι_fiberHomeo_symm v ⟨z, by simpa using hz⟩).symm
  exact (hnone w hw' i hzx).elim

/-- The weighted fibre sum of a closed open piece whose fibre over a point is empty vanishes in
a neighbourhood of that point. -/
theorem separableDegreeWeightedFiberSum_eventually_eq_zero
    {P V : Scheme.{u}} (π : P ⟶ V) [IsFinite π]
    (D : P.Opens) (hclosed : IsClosed (D : Set P)) (v : V)
    (hempty : ((D.ι ≫ π) ⁻¹' {v}) = ∅) (w : D → ℤ) :
    ∀ᶠ v' in nhds v, separableDegreeWeightedFiberSum (D.ι ≫ π) w v' = 0 := by
  classical
  filter_upwards [π.isClosedMap.eventually_nhds_fiber (p := (· ∉ (D : Set P))) v fun x hx ↦
    hclosed.isOpen_compl.mem_nhds fun hxD ↦
      Set.eq_empty_iff_forall_notMem.mp hempty ⟨x, hxD⟩ hx] with v' hv'
  unfold separableDegreeWeightedFiberSum
  exact finsum_eq_zero_of_forall_eq_zero fun d ↦ ite_eq_right fun hd ↦ hv' _ hd d.2

/-- If the composite `F ∘ q` is locally constant along an open map `q`, then `F` itself is
constant on an open neighbourhood of `q a`. -/
theorem exists_open_neighborhood_eq_of_isLocallyConstant_comp_of_isOpenMap
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (q : A → B) (hq : IsOpenMap q) (F : B → ℤ)
    (hF : IsLocallyConstant (F ∘ q)) (a : A) :
    ∃ N : Set B, IsOpen N ∧ q a ∈ N ∧ ∀ b ∈ N, F b = F (q a) := by
  refine ⟨q '' (F ∘ q) ⁻¹' {F (q a)}, hq _ (hF.isOpen_fiber _), ⟨a, rfl, rfl⟩, ?_⟩
  rintro b ⟨a', ha', rfl⟩
  exact ha'

/-- An open map pushes an eventual equality forward: if `F ∘ q` agrees with its value at `a`
near `a`, then `F` agrees with that value near `q a`. -/
theorem eventually_eq_of_openMap_comp
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (q : A → B) (hq : IsOpenMap q) (F : B → ℤ) (a : A)
    (h : ∀ᶠ a' in 𝓝 a, F (q a') = F (q a)) :
    ∀ᶠ b in 𝓝 (q a), F b = F (q a) := by
  obtain ⟨N, hNsub, hNopen, hNa⟩ := mem_nhds_iff.mp h
  filter_upwards [(hq N hNopen).mem_nhds ⟨a, hNa, rfl⟩] with b hb
  obtain ⟨a', ha'N, rfl⟩ := hb
  exact hNsub ha'N

end AlgebraicGeometry
