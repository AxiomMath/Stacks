module

public import StacksFrontier.Homology.Perfect.LocalRingFibreVanishing
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.Homology.Tor.FlatDerivedExtensionScalars
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat

/-!
# Spreading out the vanishing of high cohomology from a derived base change

Let `R → R'` be a ring map, `q' ⊂ R'` a prime and `q = q' ∩ R`. Let `K` be a pseudo-coherent
object of `D(R)` such that `Hⁱ(K ⊗_R^L R') = 0` for all `i > b`. Then there is `g ∈ R`, `g ∉ q`,
with `Hⁱ(K)_g = 0` for all `i > b`.

This is the local step of the proof of [Stacks, Tag 0CX9]: there `R = P` is a smooth algebra over
`A` presenting an affine étale chart `U = Spec B` of `X`, `K = Ri_*(K|_U)`, `R' = P ⊗_A A_n`, and
the vanishing comes from [Stacks, Tag 0CX8]. The source argues with a bounded-above complex of
finite free modules, replacing it on principal opens by shorter ones; here the same conclusion is
obtained degree by degree from [Stacks, Tag 068U], whose input is the vanishing of the derived
fibre at `q`.

## Main results

* `StacksDraft.Perfect.fibreCohomologyVanishes_of_isZero_homology_baseChange`: the derived fibre
  of `K` at `q` vanishes in degree `i > b` when `K ⊗_R^L R'` has no cohomology above `b`.
* `StacksDraft.Perfect.exists_away_forall_subsingleton_localizedModule_of_fibreCohomologyVanishes`:
  vanishing of the derived fibre at `q` in all degrees `> b` gives `g ∉ q` with
  `Hⁱ(K)_g = 0` for all `i > b`.
* `StacksDraft.Perfect.exists_away_forall_subsingleton_localizedModule_of_baseChange`: the
  statement above.

## Implementation notes

Derived categories of modules are at the standard model `HasDerivedCategory.standard`, the model
at which [Stacks, Tag 068U] (`StacksDraft.Perfect.exists_localization_iso_biprod_truncGE_truncLE`)
and the comparison `StacksDraft.Perfect.fibreCohomologyVanishes_iff_isZero_homology` are stated.
Derived base change is the chosen total left derived functor
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`. Modules are in the
universe of the rings.

## References

* [Stacks Project, Tag 068U](https://stacks.math.columbia.edu/tag/068U)
* [Stacks Project, Tag 0CX9](https://stacks.math.columbia.edu/tag/0CX9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars

universe u

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-- A module whose localization away from `f` vanishes also vanishes after localization away
from any multiple of `f`. -/
theorem subsingleton_localizedModule_powers_mul {R : Type u} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (f c : R)
    (h : Subsingleton (LocalizedModule (Submonoid.powers f) M)) :
    Subsingleton (LocalizedModule (Submonoid.powers (f * c)) M) := by
  rw [LocalizedModule.subsingleton_iff] at h ⊢
  intro m
  obtain ⟨r, ⟨k, rfl⟩, hr⟩ := h m
  refine ⟨(f * c) ^ k, ⟨k, rfl⟩, ?_⟩
  rw [mul_pow, mul_comm, mul_smul, hr, smul_zero]

/-- **The local case of [Stacks, Tag 068U] used degree by degree.** If the derived fibre of a
pseudo-coherent `K` at `p` has no cohomology in degree `i`, then `Hⁱ(K)_g = 0` for some `g ∉ p`. -/
theorem exists_away_subsingleton_localizedModule_of_fibreCohomologyVanishes {R : Type u}
    [CommRing R] (p : Ideal R) [p.IsPrime] (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ)
    (hfibre : FibreCohomologyVanishes.{u, u} p K i) :
    ∃ g : R, g ∉ p ∧ Subsingleton (LocalizedModule (Submonoid.powers g)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) := by
  obtain ⟨g, hg, hrest⟩ :=
    exists_localization_iso_biprod_truncGE_truncLE.{u, u} p K hK i hfibre
  dsimp only at hrest
  obtain ⟨-, -, e, -⟩ := hrest
  set Kf := (PseudoCoherence.localizationAwayFunctorAux.{u, u} g).obj K
  set upper := (DerivedCategory.TStructure.t.truncGE (i + 1)).obj Kf
  set lower := (DerivedCategory.TStructure.t.truncLE (i - 1)).obj Kf
  set H := DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization.Away g)) i
  have hzUpper : IsZero (H.obj upper) := DerivedCategory.isZero_of_isGE upper (i + 1) i (by omega)
  have hzLower : IsZero (H.obj lower) := DerivedCategory.isZero_of_isLE lower (i - 1) i (by omega)
  have hzSum : IsZero (H.obj (upper ⊞ lower)) :=
    have : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts H
    ((biprod_isZero_iff _ _).2 ⟨hzUpper, hzLower⟩).of_iso (H.mapBiprod upper lower)
  have hz : IsZero (H.obj Kf) := hzSum.of_iso (H.mapIso e)
  exact ⟨g, hg, ModuleCat.isZero_iff_subsingleton.1
    (hz.of_iso (PseudoCoherence.localizationAwayHomologyIso.{u, u} g K i).symm)⟩

/-- A pseudo-coherent object of `D(R)` has no cohomology above some degree. -/
theorem exists_isZero_homology_gt_of_isPseudoCoherent {R : Type u} [CommRing R]
    {K : DerivedCategory (ModuleCat.{u} R)}
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    ∃ t : ℤ, ∀ i : ℤ, t < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  obtain ⟨t, ht⟩ := hE.upperBound
  refine ⟨t, fun i hi => ?_⟩
  exact (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj E) t i hi).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso e.symm)

/-- **Vanishing of the derived fibre above `b` spreads out.** If the derived fibre of a
pseudo-coherent `K` at `p` has no cohomology in degrees `> b`, then for some `g ∉ p` all the
cohomology modules `Hⁱ(K)`, `i > b`, vanish after localization away from `g`. -/
theorem exists_away_forall_subsingleton_localizedModule_of_fibreCohomologyVanishes {R : Type u}
    [CommRing R] (p : Ideal R) [p.IsPrime] (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (b : ℤ)
    (hfibre : ∀ i : ℤ, b < i → FibreCohomologyVanishes.{u, u} p K i) :
    ∃ g : R, g ∉ p ∧ ∀ i : ℤ, b < i → Subsingleton (LocalizedModule (Submonoid.powers g)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) := by
  obtain ⟨t, ht⟩ := exists_isZero_homology_gt_of_isPseudoCoherent hK
  have key : ∀ n : ℕ, ∃ g : R, g ∉ p ∧ ∀ i : ℤ, b < i → i ≤ b + n →
      Subsingleton (LocalizedModule (Submonoid.powers g)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) := by
    intro n
    induction n with
    | zero => exact ⟨1, (Ideal.ne_top_iff_one p).1 ‹p.IsPrime›.ne_top, fun _ _ _ => by omega⟩
    | succ n ih =>
      obtain ⟨g, hg, hgi⟩ := ih
      obtain ⟨g', hg', hg'i⟩ :=
        exists_away_subsingleton_localizedModule_of_fibreCohomologyVanishes p K hK
          (b + (n + 1 : ℕ)) (hfibre _ (by omega))
      refine ⟨g * g', fun h => (‹p.IsPrime›.mem_or_mem h).elim hg hg',
        fun i hi hi' => ?_⟩
      by_cases hin : i ≤ b + n
      · exact subsingleton_localizedModule_powers_mul g g' (hgi i hi hin)
      · obtain rfl : i = b + (n + 1 : ℕ) := by omega
        rw [mul_comm]
        exact subsingleton_localizedModule_powers_mul g' g hg'i
  obtain ⟨g, hg, hgi⟩ := key (t - b).toNat
  refine ⟨g, hg, fun i hi => ?_⟩
  by_cases hit : i ≤ t
  · exact hgi i hi (by omega)
  · have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) :=
      ModuleCat.isZero_iff_subsingleton.1 (ht i (by omega))
    infer_instance

/-- **The derived fibre at `q' ∩ R` from a derived base change.** Let `f : R → R'` be a ring map,
`q'` a prime of `R'` and `K` a pseudo-coherent object of `D(R)` with `Hⁱ(K ⊗_R^L R') = 0` for all
`i > b`. Then the derived fibre `K ⊗_R^L κ(q' ∩ R)` has no cohomology in degrees `> b`.

`K ⊗_R^L κ(q')` is `(K ⊗_R^L R') ⊗_{R'}^L κ(q')`, which lies in degrees `≤ b` since derived
base change preserves the upper cutoffs; it is also `(K ⊗_R^L κ(q' ∩ R)) ⊗_{κ(q' ∩ R)} κ(q')`,
and the field extension `κ(q' ∩ R) → κ(q')` is faithfully flat. -/
theorem fibreCohomologyVanishes_of_isZero_homology_baseChange {R R' : Type u} [CommRing R]
    [CommRing R'] (f : R →+* R') (q' : Ideal R') [q'.IsPrime]
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (b : ℤ)
    (hb : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).obj
      ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj K)))
    (i : ℤ) (hi : b < i) :
    FibreCohomologyVanishes.{u, u} (q'.comap f) K i := by
  set p := q'.comap f
  set g' := algebraMap R' q'.ResidueField
  set e : p.ResidueField →+* q'.ResidueField := Ideal.ResidueField.map p q' f rfl
  have hcomp : (algebraMap R' q'.ResidueField).comp f = e.comp (algebraMap R p.ResidueField) :=
    RingHom.ext fun r => (Ideal.ResidueField.map_algebraMap p q' f rfl r).symm
  -- `K ⊗ᴸ κ(q')` lies in degrees `≤ b`.
  have h1 : ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj K).IsLE b :=
    (DerivedCategory.isLE_iff _ b).2 hb
  have h2 : ((totalDerivedExtensionScalars.{u, u, u} g').functor.obj
      ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj K)).IsLE b :=
    (totalDerivedExtensionScalars.{u, u, u} g').maps_t_le _ b
  have h3 : ((totalDerivedExtensionScalars.{u, u, u} (g'.comp f)).functor.obj K).IsLE b :=
    have : (((totalDerivedExtensionScalars.{u, u, u} f).functor ⋙
        (totalDerivedExtensionScalars.{u, u, u} g').functor).obj K).IsLE b := h2
    DerivedCategory.TStructure.t.isLE_of_iso
      ((totalDerivedExtensionScalarsComp.{u, u} f g').app K) b
  rw [hcomp] at h3
  have h4 : ((totalDerivedExtensionScalars.{u, u, u} e).functor.obj
      ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R p.ResidueField)).functor.obj
        K)).IsLE b :=
    DerivedCategory.TStructure.t.isLE_of_iso
      ((totalDerivedExtensionScalarsComp.{u, u} (algebraMap R p.ResidueField) e).app K).symm b
  -- The field extension `κ(q' ∩ R) → κ(q')` is faithfully flat.
  let : Algebra p.ResidueField q'.ResidueField := e.toAlgebra
  have hflat : e.Flat := by
    show Module.Flat p.ResidueField q'.ResidueField
    infer_instance
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  let F := ModuleCat.extendScalars.{u, u, u} e
  have : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} e).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  set X := (totalDerivedExtensionScalars.{u, u, u} (algebraMap R p.ResidueField)).functor.obj K
  have h5 : IsZero (F.obj ((DerivedCategory.homologyFunctor _ i).obj X)) :=
    (((DerivedCategory.isLE_iff _ b).1 h4 i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso
        ((RingTheory.TorIndependence.flatDerivedExtensionScalarsIso e hflat).app X).symm)).of_iso
      ((PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F i).app X).symm
  exact (fibreCohomologyVanishes_iff_isZero_homology.{u, u} p K hK i).2
    ((StacksDraft.TorAmplitude.FaithfullyFlat.isZero_extendScalars_iff _).1 h5)

/-- **Spreading out the vanishing of high cohomology from a derived base change.** Let
`f : R → R'` be a ring map, `q'` a prime of `R'` and `K` a pseudo-coherent object of `D(R)` with
`Hⁱ(K ⊗_R^L R') = 0` for all `i > b`. Then there is `g ∈ R` outside `q' ∩ R` with `Hⁱ(K)_g = 0`
for all `i > b`. -/
theorem exists_away_forall_subsingleton_localizedModule_of_baseChange {R R' : Type u}
    [CommRing R] [CommRing R'] (f : R →+* R') (q' : Ideal R') [q'.IsPrime]
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (b : ℤ)
    (hb : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).obj
      ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj K))) :
    ∃ g : R, g ∉ q'.comap f ∧ ∀ i : ℤ, b < i →
      Subsingleton (LocalizedModule (Submonoid.powers g)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) :=
  exists_away_forall_subsingleton_localizedModule_of_fibreCohomologyVanishes (q'.comap f) K hK b
    (fibreCohomologyVanishes_of_isZero_homology_baseChange f q' K hK b hb)

end StacksDraft.Perfect

end
