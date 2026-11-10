module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.InverseImageSectionsLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PropertyAPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImageSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.TorsionExponent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Direct and inverse images of `ℓ`-power torsion sheaves

Let `F` be an abelian sheaf on the small étale site of a scheme `X` which is `ℓ`-power torsion:
every local section is, locally, killed by a power of `ℓ`. Over an object `W` of the site whose
underlying scheme is quasi-compact, every section of `F` is then killed by a single power of
`ℓ`: the loci where it is killed by `ℓ^r` are open, increase with `r` and cover `W`.

Consequently the direct image `f_* F` along a quasi-compact morphism `f : X ⟶ Y` is again
`ℓ`-power torsion: a section of `f_* F` over an affine `V` étale over `Y` is a section of `F` over
the quasi-compact scheme `V ×_Y X`, and the affine objects cover. The inverse image `f⁻¹ G` of an
`ℓ`-power torsion sheaf `G` along any morphism is `ℓ`-power torsion, since its local sections
are locally pulled back from sections of `G`.

The same arguments, with the loci where a section is killed by `r!`, show that over a
quasi-compact object every section of a torsion sheaf is killed by a single positive integer, and
that the direct image of a torsion sheaf along a quasi-compact morphism is torsion.

## Main results

* `Stacks.EtaleCohomology.exists_pow_smul_eq_zero_of_isPrimePowerTorsion`: on a quasi-compact
  object a section of an `ℓ`-power torsion sheaf is killed by a power of `ℓ`.
* `Stacks.EtaleCohomology.isPrimePowerTorsion_smallEtalePushforwardAb`: direct image along a
  quasi-compact morphism preserves `ℓ`-power torsion.
* `Stacks.EtaleCohomology.isPrimePowerTorsion_smallEtalePullbackAb`: inverse image preserves
  `ℓ`-power torsion.
* `Stacks.EtaleCohomology.exists_nsmul_eq_zero_of_torsionSheafProperty`,
  `Stacks.EtaleCohomology.torsionSheafProperty_smallEtalePushforwardAb`: the same two statements
  for torsion sheaves, the second being [Stacks, Tag 0DDD], part (1), in degree zero.

## References

* [Stacks Project, Tag 0DV7](https://stacks.math.columbia.edu/tag/0DV7)
* [Stacks Project, Tag 0DDD](https://stacks.math.columbia.edu/tag/0DDD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ}

/-- **On a quasi-compact object a section of an `ℓ`-power torsion sheaf is killed by a power of
`ℓ`.** -/
@[sga "4 IX 1.2" "(ii)"]
theorem exists_pow_smul_eq_zero_of_isPrimePowerTorsion {X : Scheme.{u}}
    {F : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (hF : Stacks.Torsion.IsPrimePowerTorsion (smallEtaleTopology X) ℓ F) (W : X.Etale)
    [CompactSpace W.left] (x : ToType (F.obj.obj (op W))) : ∃ r : ℕ, ℓ ^ r • x = 0 := by
  let O : ℕ → W.left.Opens := fun r ↦ smallEtaleEqLocus F W (ℓ ^ r • x) 0
  have hmono : Monotone O := by
    intro r r' hrr' w hw
    obtain ⟨V, k, hk, hw⟩ := exists_of_mem_smallEtaleEqLocus F _ _ hw
    refine range_subset_smallEtaleEqLocus F k _ _ ?_ hw
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hrr'
    rw [map_zero] at hk ⊢
    rw [pow_add, mul_comm, mul_smul, map_nsmul, hk, smul_zero]
  have hcover : ∀ w : W.left, ∃ r, w ∈ O r := by
    intro w
    obtain ⟨R, hR, hann⟩ := hF W x
    obtain ⟨V, g, hg, hw⟩ := (mem_smallEtaleTopology_iff R).mp hR w
    obtain ⟨r, -, hr⟩ := hann V g hg
    refine ⟨r, range_subset_smallEtaleEqLocus F g _ _ ?_ hw⟩
    rw [map_nsmul, map_zero]
    exact hr
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun r ↦ (O r : Set W.left))
    (fun r ↦ (O r).isOpen) fun w _ ↦ Set.mem_iUnion.mpr (hcover w)
  refine ⟨t.sup id, ?_⟩
  have hall : Set.range (𝟙 W : W ⟶ W).left ⊆ O (t.sup id) := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨r, hr, hw⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ w))
    exact hmono (Finset.le_sup (f := id) hr) hw
  have h := (map_eq_map_iff_range_subset_smallEtaleEqLocus F (𝟙 W) _ _).mpr hall
  simpa only [op_id, CategoryTheory.Functor.map_id, AddCommGrpCat.hom_id, AddMonoidHom.id_apply]
    using h

/-- **Direct image along a quasi-compact morphism preserves `ℓ`-power torsion.** -/
theorem isPrimePowerTorsion_smallEtalePushforwardAb {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] {F : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (hF : Stacks.Torsion.IsPrimePowerTorsion (smallEtaleTopology X) ℓ F) :
    Stacks.Torsion.IsPrimePowerTorsion (smallEtaleTopology Y) ℓ
      ((smallEtalePushforwardAb f).obj F) := by
  intro U x
  let R : Sieve U := Sieve.generate fun V _ ↦ CompactSpace V.left
  refine ⟨R, ?_, ?_⟩
  · rw [mem_smallEtaleTopology_iff]
    intro y
    obtain ⟨z, hz⟩ := U.left.affineCover.covers y
    let V : Y.Etale := MorphismProperty.Over.mk ⊤
      (U.left.affineCover.f (U.left.affineCover.idx y) ≫ U.hom) (by infer_instance)
    have : CompactSpace V.left :=
      inferInstanceAs (CompactSpace (U.left.affineCover.X (U.left.affineCover.idx y)))
    exact ⟨V, MorphismProperty.Over.homMk (U.left.affineCover.f (U.left.affineCover.idx y)) rfl,
      ⟨V, 𝟙 V, _, this, Category.id_comp _⟩, z, hz⟩
  · rintro V a ⟨V₀, c, b, hV₀, rfl⟩
    have : CompactSpace ((𝟭 Scheme.{u}).obj V₀.left) := hV₀
    have hc : CompactSpace (pullback V₀.hom f : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst V₀.hom f)
    have : CompactSpace ((smallEtaleBaseChange f).obj V₀).left := hc
    obtain ⟨r, hr⟩ := exists_pow_smul_eq_zero_of_isPrimePowerTorsion hF
      ((smallEtaleBaseChange f).obj V₀) (((smallEtalePushforwardAb f).obj F).obj.map b.op x)
    have hr' : ℓ ^ (r + 1) • (((smallEtalePushforwardAb f).obj F).obj.map b.op x) = 0 := by
      rw [pow_succ', mul_smul]
      exact (congrArg (ℓ • ·) hr).trans (smul_zero ℓ)
    refine ⟨r + 1, Nat.succ_pos r, ?_⟩
    rw [op_comp, CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply, ← map_nsmul, hr',
      map_zero]

/-- **On a quasi-compact object a section of a torsion sheaf is killed by a single positive
integer.** The loci where the section is killed by `r!` are open, increase with `r` and cover the
object, so finitely many of them, hence one of them, cover it. -/
@[sga "4 IX 1.2" "(ii)"]
theorem exists_nsmul_eq_zero_of_torsionSheafProperty {X : Scheme.{u}}
    {F : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (hF : Stacks.Torsion.torsionSheafProperty (smallEtaleTopology X) F) (W : X.Etale)
    [CompactSpace W.left] (x : ToType (F.obj.obj (op W))) : ∃ n : ℕ, 0 < n ∧ n • x = 0 := by
  let O : ℕ → W.left.Opens := fun r ↦ smallEtaleEqLocus F W (r.factorial • x) 0
  have hmono : Monotone O := by
    intro r r' hrr' w hw
    obtain ⟨V, k, hk, hw⟩ := exists_of_mem_smallEtaleEqLocus F _ _ hw
    refine range_subset_smallEtaleEqLocus F k _ _ ?_ hw
    obtain ⟨e, he⟩ := Nat.factorial_dvd_factorial hrr'
    rw [map_zero] at hk ⊢
    rw [he, mul_comm, mul_smul, map_nsmul, hk, smul_zero]
  have hcover : ∀ w : W.left, ∃ r, w ∈ O r := by
    intro w
    obtain ⟨R, hR, hann⟩ := hF W x
    obtain ⟨V, g, hg, hw⟩ := (mem_smallEtaleTopology_iff R).mp hR w
    obtain ⟨n, hn, hr⟩ := hann V g hg
    refine ⟨n, range_subset_smallEtaleEqLocus F g _ _ ?_ hw⟩
    obtain ⟨e, he⟩ := Nat.dvd_factorial hn le_rfl
    rw [map_nsmul, map_zero, he, mul_comm, mul_smul]
    exact (congrArg (e • ·) hr).trans (smul_zero e)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun r ↦ (O r : Set W.left))
    (fun r ↦ (O r).isOpen) fun w _ ↦ Set.mem_iUnion.mpr (hcover w)
  refine ⟨(t.sup id).factorial, Nat.factorial_pos _, ?_⟩
  have hall : Set.range (𝟙 W : W ⟶ W).left ⊆ O (t.sup id) := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨r, hr, hw⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ w))
    exact hmono (Finset.le_sup (f := id) hr) hw
  have h := (map_eq_map_iff_range_subset_smallEtaleEqLocus F (𝟙 W) _ _).mpr hall
  simpa only [op_id, CategoryTheory.Functor.map_id, AddCommGrpCat.hom_id, AddMonoidHom.id_apply]
    using h

/-- **Direct image along a quasi-compact morphism preserves torsion sheaves**
([Stacks, Tag 0DDD], part (1) in degree zero). A section of `f_* F` over an object `V` étale over
`Y` with quasi-compact underlying scheme is a section of `F` over the quasi-compact scheme
`V ×_Y X`, hence is killed by one positive integer, and these objects cover. -/
@[sga "4 IX 1.2" "(v), degree q = 0"]
theorem torsionSheafProperty_smallEtalePushforwardAb {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] {F : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (hF : Stacks.Torsion.torsionSheafProperty (smallEtaleTopology X) F) :
    Stacks.Torsion.torsionSheafProperty (smallEtaleTopology Y)
      ((smallEtalePushforwardAb f).obj F) := by
  intro U x
  let R : Sieve U := Sieve.generate fun V _ ↦ CompactSpace V.left
  refine ⟨R, ?_, ?_⟩
  · rw [mem_smallEtaleTopology_iff]
    intro y
    obtain ⟨z, hz⟩ := U.left.affineCover.covers y
    let V : Y.Etale := MorphismProperty.Over.mk ⊤
      (U.left.affineCover.f (U.left.affineCover.idx y) ≫ U.hom) (by infer_instance)
    have : CompactSpace V.left :=
      inferInstanceAs (CompactSpace (U.left.affineCover.X (U.left.affineCover.idx y)))
    exact ⟨V, MorphismProperty.Over.homMk (U.left.affineCover.f (U.left.affineCover.idx y)) rfl,
      ⟨V, 𝟙 V, _, this, Category.id_comp _⟩, z, hz⟩
  · rintro V a ⟨V₀, c, b, hV₀, rfl⟩
    have : CompactSpace ((𝟭 Scheme.{u}).obj V₀.left) := hV₀
    have hc : CompactSpace (pullback V₀.hom f : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst V₀.hom f)
    have : CompactSpace ((smallEtaleBaseChange f).obj V₀).left := hc
    obtain ⟨n, hn, hr⟩ := exists_nsmul_eq_zero_of_torsionSheafProperty hF
      ((smallEtaleBaseChange f).obj V₀) (((smallEtalePushforwardAb f).obj F).obj.map b.op x)
    have hr' : n • (((smallEtalePushforwardAb f).obj F).obj.map b.op x) = 0 := hr
    refine ⟨n, hn, ?_⟩
    rw [op_comp, CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply, ← map_nsmul, hr',
      map_zero]

/-- **Inverse image preserves `ℓ`-power torsion.** -/
theorem isPrimePowerTorsion_smallEtalePullbackAb {X Y : Scheme.{u}} (f : X ⟶ Y)
    {G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}}
    (hG : Stacks.Torsion.IsPrimePowerTorsion (smallEtaleTopology Y) ℓ G) :
    Stacks.Torsion.IsPrimePowerTorsion (smallEtaleTopology X) ℓ
      ((smallEtalePullbackAb f).obj G) := by
  intro U x
  obtain ⟨R, hR, hloc⟩ := exists_covering_smallEtalePullbackAb_eq_unitApp f G U x
  let R' : Sieve U := Sieve.generate fun V a ↦ R a ∧ ∃ r : ℕ, 0 < r ∧
    ℓ ^ r • ((smallEtalePullbackAb f).obj G).obj.map a.op x = 0
  refine ⟨R', ?_, ?_⟩
  · refine (smallEtaleTopology X).transitive hR R' fun V a ha ↦ ?_
    obtain ⟨W, m, h, hh⟩ := hloc a ha
    obtain ⟨R₀, hR₀, hann⟩ := hG W h
    have hcov : (R₀.functorPushforward (smallEtaleBaseChange f)).pullback m ∈
        smallEtaleTopology X V :=
      (smallEtaleTopology X).pullback_stable m
        ((CoverPreserving.of_isContinuous (smallEtaleBaseChange f) (smallEtaleTopology Y)
          (smallEtaleTopology X)).cover_preserve hR₀)
    refine (smallEtaleTopology X).superset_covering (fun V' b hb ↦ ?_) hcov
    obtain ⟨W', w, c, hw, hbm⟩ := hb
    obtain ⟨r, hr, hr'⟩ := hann W' w hw
    refine ⟨V', 𝟙 V', b ≫ a, ⟨R.downward_closed ha b, r, hr, ?_⟩, Category.id_comp _⟩
    rw [op_comp, CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply, hh,
      ← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp, hbm, op_comp,
      CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply]
    change ℓ ^ r • ((smallEtalePullbackAb f).obj G).obj.map c.op
      (((smallEtalePullbackAb f).obj G).obj.map ((smallEtaleBaseChange f).map w).op
        (smallEtalePullbackAbUnitApp f G W h)) = 0
    rw [← ConcreteCategory.comp_apply ((smallEtalePullbackAbUnitApp f G W)),
      show smallEtalePullbackAbUnitApp f G W ≫
        ((smallEtalePullbackAb f).obj G).obj.map ((smallEtaleBaseChange f).map w).op =
        G.obj.map w.op ≫ smallEtalePullbackAbUnitApp f G W' from
        (((smallEtaleAdjunctionAb f).unit.app G).hom.naturality w.op).symm,
      ConcreteCategory.comp_apply, ← map_nsmul, ← map_nsmul, hr', map_zero, map_zero]
  · rintro V a ⟨V₀, c, b, ⟨-, r, hr, hr'⟩, rfl⟩
    refine ⟨r, hr, ?_⟩
    rw [op_comp, CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply, ← map_nsmul, hr',
      map_zero]

end Stacks.EtaleCohomology

end
