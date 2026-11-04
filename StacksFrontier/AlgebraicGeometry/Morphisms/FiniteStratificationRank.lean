module

public import StacksFrontier.AlgebraicGeometry.Groupoids.StratificationStratum
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteStratificationInvariant
public import StacksFrontier.RingTheory.Fitting.Rank

/-!
# The rank of a finite morphism on a stratum of its Fitting stratification

The strata of the Fitting stratification of a finite morphism `f` are the loci where the number
of generators of `f_* 𝒪_P` jumps. On the `r`-th stratum — inside the closed subscheme cut out by
the `(r-1)`st Fitting ideal sheaf and away from the support of the `r`th one — the base change
of `f` is finite locally free of rank `r`. This file proves that statement *affine-locally*: on
every affine open of the stratum lying over an affine open of the base, the sections of the
pushforward of the structure sheaf along the base change form a finite locally free module of
rank `r`.

## Main results

* `Stacks.Fitting.map_appLE_ideal_idealSheaf_of_isPullback`: base change of a Fitting ideal
  sheaf of a finite pushforward, on an affine open of the base and an affine open above it. The
  second leg of the cartesian square need not be affine, which is what the stratum needs.
* `Stacks.IdealSheaf.map_appLE_ideal_eq_bot_of_factorsThrough` and
  `Stacks.IdealSheaf.map_appLE_ideal_eq_top_of_notMem_support`: an ideal sheaf dies on anything
  mapping into its closed subscheme, and becomes the unit ideal on any affine open of anything
  mapping outside its support.
* `Stacks.Fitting.module_isFiniteLocallyFreeOfRank_pushforward_pullback`: the two conditions
  together give finite local freeness of rank `r` of the sections of the base change.
* `Stacks.Groupoids.module_isFiniteLocallyFreeOfRank_finiteStratification_stratum`: the
  specialization to a stratum of the Fitting stratification of the source map of a groupoid
  scheme, which is the affine-local form of the rank assertion of Stacks Tag 0AB9.

## Implementation notes

The base change statement is the affine-local counterpart of
`Stacks.Fitting.comap_idealSheaf_pushforward_of_isPullback`, whose inverse-image formula needs
the second leg of the square to be affine. The inclusion of a stratum is a locally closed
immersion, which is *not* affine, so that lemma does not apply; but the identification of the
sections of the fibre product as a tensor product only needs an affine open `V'` of the second
factor lying over an affine open `V` of the base, which is exactly
`Stacks.Morphisms.isPushout_appLE_of_isPullback`. Those pairs `(V, V')` cover the stratum by
`Stacks.Morphisms.exists_affineOpens_le_preimage`.

Passing from the two ideal-theoretic conditions to local freeness is the Fitting-ideal criterion
of Stacks Tag 07ZD, `finiteLocallyFreeOfRank_fittingIdeal_tfae`.

No `@[stacks 0AB9]` attribute is attached here. The rank assertion of that tag says that the
morphism `pullback.snd` is finite locally free of rank `r`, i.e. it is a statement about
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank`, which unfolds to the *sheaf*-level predicate
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` on the Zariski site. Deducing that
from the affine-local module statement proved here is
`Stacks.Groupoids.finiteStratification_rank` in
`StacksFrontier.AlgebraicGeometry.Morphisms.FiniteStratificationRankSheaf`, which carries the
attribute; it uses the sheaf-theoretic dictionary of Stacks Tags 01C6 and 05JM through
`Stacks.Modules.isFiniteLocallyFreeOfRank_of_module_affineOpens` and
`Stacks.Modules.isFiniteLocallyFreeOfRank_iff_localGenerators`, together with quasi-coherence
of a pushforward along an affine morphism,
`Stacks.Modules.isQuasicoherent_pushforwardStructureSheaf`.

## References

* [Stacks Project, Tag 0AB9](https://stacks.math.columbia.edu/tag/0AB9)
* [Stacks Project, Tag 05P8](https://stacks.math.columbia.edu/tag/05P8)
* [Stacks Project, Tag 07ZA](https://stacks.math.columbia.edu/tag/07ZA)
* [Stacks Project, Tag 07ZD](https://stacks.math.columbia.edu/tag/07ZD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.Morphisms

/-- Every point of a scheme has an affine open neighbourhood lying over an affine open of the
target of any given morphism: affine opens form a basis of both schemes, so an affine open of
the target containing the image of the point can be refined by an affine open of the source
inside its preimage. This is what makes an affine-local statement over such pairs of opens a
statement over a cover. -/
theorem exists_affineOpens_le_preimage {X Z : Scheme.{u}} (k : Z ⟶ X) (z : Z) :
    ∃ (V : X.affineOpens) (V' : Z.affineOpens), V'.1 ≤ k ⁻¹ᵁ V.1 ∧ z ∈ V'.1 := by
  obtain ⟨-, ⟨V, hV, rfl⟩, hzV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (k.base z)) isOpen_univ
  obtain ⟨-, ⟨V', hV', rfl⟩, hzV', hsub⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (a := z) hzV (k ⁻¹ᵁ V).2
  exact ⟨⟨V, hV⟩, ⟨V', hV'⟩, hsub, hzV'⟩

end Stacks.Morphisms

namespace Stacks.Fitting

open Stacks.Morphisms

/-- **Stacks Project, Tag 07ZA** for a finite pushforward, affine-locally: for a cartesian
square whose leg `f` out of the base is finite, an affine open `V` of the base and an affine
open `V'` of the other factor lying over `V`, the ideal of the `k`th Fitting ideal sheaf of
`f_* 𝒪_X` on `V` generates the ideal of the `k`th Fitting ideal sheaf of the pushforward of the
structure sheaf along the base change, on `V'`.

The second leg `g` is *not* assumed affine, which is what distinguishes this from
`Stacks.Fitting.comap_idealSheaf_pushforward_of_isPullback`: affineness of the fibre product
over `V'` comes from that of `f ⁻¹ᵁ V` over `V`. -/
theorem map_appLE_ideal_idealSheaf_of_isPullback {P X T U : Scheme.{u}} {p : P ⟶ X} {q : P ⟶ T}
    {f : X ⟶ U} {g : T ⟶ U} (hsq : IsPullback p q f g) [IsFinite f] (V : U.affineOpens)
    (V' : T.affineOpens) (hV' : V'.1 ≤ g ⁻¹ᵁ V.1) (k : ℤ) :
    Ideal.map (g.appLE V.1 V'.1 hV').hom ((idealSheaf (pushforwardStructureSheaf f) k).ideal V) =
      (idealSheaf (pushforwardStructureSheaf q) k).ideal V' := by
  have hq : IsFinite q := MorphismProperty.of_isPullback (P := @IsFinite) hsq ‹IsFinite f›
  rw [ideal_idealSheaf_pushforward, ideal_idealSheaf_pushforward]
  rcases lt_or_ge k 0 with hk | hk
  · rw [fittingIdeal, if_pos hk, Ideal.map_bot, fittingIdeal, if_pos hk]
  lift k to ℕ using hk
  have e : q ⁻¹ᵁ V'.1 ≤ p ⁻¹ᵁ (f ⁻¹ᵁ V.1) := by
    refine le_trans (q.preimage_mono hV') ?_
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hsq.w]
  have hpo := isPushout_appLE_of_isPullback hsq V V' hV' e
  let _ : Algebra Γ(U, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
  let _ : Algebra Γ(U, V.1) Γ(T, V'.1) := (g.appLE V.1 V'.1 hV').hom.toAlgebra
  let _ : Algebra Γ(T, V'.1) Γ(P, q ⁻¹ᵁ V'.1) := (q.app V'.1).hom.toAlgebra
  let _ : Algebra Γ(X, f ⁻¹ᵁ V.1) Γ(P, q ⁻¹ᵁ V'.1) :=
    (p.appLE (f ⁻¹ᵁ V.1) (q ⁻¹ᵁ V'.1) e).hom.toAlgebra
  let _ : Algebra Γ(U, V.1) Γ(P, q ⁻¹ᵁ V'.1) :=
    (g.appLE V.1 V'.1 hV' ≫ q.app V'.1).hom.toAlgebra
  have ht1 : IsScalarTower Γ(U, V.1) Γ(T, V'.1) Γ(P, q ⁻¹ᵁ V'.1) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have ht2 : IsScalarTower Γ(U, V.1) Γ(X, f ⁻¹ᵁ V.1) Γ(P, q ⁻¹ᵁ V'.1) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp]
    exact congrArg CommRingCat.Hom.hom hpo.w.symm
  have hpo' : IsPushout (CommRingCat.ofHom (algebraMap Γ(U, V.1) Γ(X, f ⁻¹ᵁ V.1)))
      (CommRingCat.ofHom (algebraMap Γ(U, V.1) Γ(T, V'.1)))
      (CommRingCat.ofHom (algebraMap Γ(X, f ⁻¹ᵁ V.1) Γ(P, q ⁻¹ᵁ V'.1)))
      (CommRingCat.ofHom (algebraMap Γ(T, V'.1) Γ(P, q ⁻¹ᵁ V'.1))) := by
    simpa [RingHom.algebraMap_toAlgebra] using hpo
  have hpush : Algebra.IsPushout Γ(U, V.1) Γ(X, f ⁻¹ᵁ V.1) Γ(T, V'.1) Γ(P, q ⁻¹ᵁ V'.1) :=
    CommRingCat.isPushout_iff_isPushout.mp hpo'
  rw [Algebra.IsPushout.comm] at hpush
  have hbc := hpush.out
  have hfinCD : Module.Finite Γ(T, V'.1) Γ(P, q ⁻¹ᵁ V'.1) :=
    module_finite_pushforwardStructureSheaf q V'
  have hfinBA : Module.Finite Γ(U, V.1) Γ(X, f ⁻¹ᵁ V.1) :=
    module_finite_pushforwardStructureSheaf f V
  have hfinT : Module.Finite Γ(T, V'.1) (TensorProduct Γ(U, V.1) Γ(T, V'.1) Γ(X, f ⁻¹ᵁ V.1)) :=
    Module.Finite.equiv hbc.equiv.symm
  exact ((fittingIdeal_basic_properties.{u, u, u, u}
    (R := Γ(U, V.1)) (M := Γ(X, f ⁻¹ᵁ V.1))).2.2.1 Γ(T, V'.1) k).symm.trans
    (fittingIdeal_eq_of_linearEquiv hbc.equiv k)

end Stacks.Fitting

namespace Stacks.IdealSheaf

/-- An ideal on an affine open whose zero locus misses that open is the unit ideal. -/
theorem eq_top_of_zeroLocus_inter_eq_empty {X : Scheme.{u}} (V : X.affineOpens)
    (K : Ideal Γ(X, V.1))
    (h : X.zeroLocus (U := V.1) (K : Set Γ(X, V.1)) ∩ (V.1 : Set X) = ∅) : K = ⊤ := by
  have himg := (V.2.fromSpec_image_zeroLocus (K : Set Γ(X, V.1))).trans h
  simpa using PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp (Set.image_eq_empty.mp himg)

/-- The ideal of an ideal sheaf on an affine open dies in the sections of its closed
subscheme: the ideal is exactly the kernel of the closed immersion on that open. -/
theorem map_app_subschemeι_ideal_eq_bot {X : Scheme.{u}} (I : X.IdealSheafData)
    (V : X.affineOpens) : Ideal.map (I.subschemeι.app V.1).hom (I.ideal V) = ⊥ := by
  rw [Ideal.map_eq_bot_iff_le_ker, Scheme.IdealSheafData.ker_subschemeι_app]

/-- The ideal of an ideal sheaf dies in the sections of anything mapping to its closed
subscheme: for `j : Z ⟶ I.subscheme`, an affine open `V` of `X` and an open `V'` of `Z` lying
over it, the image of `I.ideal V` in `Γ(Z, V')` is zero. -/
theorem map_appLE_ideal_eq_bot_of_factorsThrough {X Z : Scheme.{u}} (I : X.IdealSheafData)
    (j : Z ⟶ I.subscheme) (V : X.affineOpens) (V' : Z.Opens)
    (hV' : V' ≤ (j ≫ I.subschemeι) ⁻¹ᵁ V.1) :
    Ideal.map ((j ≫ I.subschemeι).appLE V.1 V' hV').hom (I.ideal V) = ⊥ := by
  rw [Scheme.Hom.comp_appLE, CommRingCat.hom_comp, ← Ideal.map_map,
    map_app_subschemeι_ideal_eq_bot, Ideal.map_bot]

/-- The ideal of an ideal sheaf generates the unit ideal on any affine open of a scheme mapping
entirely outside its support: for `k : Z ⟶ X` whose image misses `J.support`, an affine open
`V` of `X` and an affine open `V'` of `Z` lying over it, the image of `J.ideal V` in
`Γ(Z, V')` is everything. -/
theorem map_appLE_ideal_eq_top_of_notMem_support {X Z : Scheme.{u}} (J : X.IdealSheafData)
    (k : Z ⟶ X) (hk : ∀ z : Z, k.base z ∉ (J.support : Set X)) (V : X.affineOpens)
    (V' : Z.affineOpens) (hV' : V'.1 ≤ k ⁻¹ᵁ V.1) :
    Ideal.map (k.appLE V.1 V'.1 hV').hom (J.ideal V) = ⊤ := by
  refine eq_top_of_zeroLocus_inter_eq_empty V' _ ?_
  have hspan : Ideal.map (k.appLE V.1 V'.1 hV').hom (J.ideal V) =
      Ideal.span ((k.appLE V.1 V'.1 hV').hom '' (J.ideal V : Set Γ(X, V.1))) := rfl
  have himg : (k.appLE V.1 V'.1 hV').hom '' (J.ideal V : Set Γ(X, V.1)) =
      (Z.presheaf.map (homOfLE hV').op).hom ''
        ((k.app V.1).hom '' (J.ideal V : Set Γ(X, V.1))) := by
    rw [← Set.image_comp]
    rfl
  rw [hspan, Scheme.zeroLocus_span, himg, Scheme.zeroLocus_map, ← Scheme.preimage_zeroLocus]
  refine Set.eq_empty_of_forall_notMem fun z hz ↦ ?_
  have hzV' : z ∈ (V'.1 : Set Z) := hz.2
  rcases hz.1 with hz1 | hz1
  · exact hk z (((J.coe_support_inter V).ge ⟨hz1, hV' hzV'⟩).1)
  · exact hz1 hzV'

end Stacks.IdealSheaf

namespace Stacks.Fitting

open Stacks.Morphisms Stacks.IdealSheaf

/-- **Stacks Project, Tag 07ZD** transported to a base change of a finite morphism: if the
`(r-1)`st Fitting ideal sheaf of `f_* 𝒪_P` dies on an affine open `V'` of `Z` lying over an
affine open `V` of the base and the `r`th one becomes the unit ideal there, then the sections of
the pushforward of the structure sheaf along the base change of `f` by `k` form a finite locally
free module of rank `r` over `Γ(Z, V')`. -/
theorem module_isFiniteLocallyFreeOfRank_pushforward_pullback {X P Z : Scheme.{u}} (f : P ⟶ X)
    [IsFinite f] (k : Z ⟶ X) (r : ℕ) (hr : 0 < r) (V : X.affineOpens) (V' : Z.affineOpens)
    (hV' : V'.1 ≤ k ⁻¹ᵁ V.1)
    (hbot : Ideal.map (k.appLE V.1 V'.1 hV').hom
      ((idealSheaf (pushforwardStructureSheaf f) ((r - 1 : ℕ) : ℤ)).ideal V) = ⊥)
    (htop : Ideal.map (k.appLE V.1 V'.1 hV').hom
      ((idealSheaf (pushforwardStructureSheaf f) (r : ℤ)).ideal V) = ⊤) :
    Module.IsFiniteLocallyFreeOfRank Γ(Z, V'.1)
      Γ(pushforwardStructureSheaf (pullback.snd f k), V'.1) r := by
  have hsq : IsPullback (pullback.fst f k) (pullback.snd f k) f k := .of_hasPullback f k
  have hfin : Module.Finite Γ(Z, V'.1)
      Γ(pushforwardStructureSheaf (pullback.snd f k), V'.1) :=
    module_finite_pushforwardStructureSheaf _ V'
  have key (m : ℤ) :
      fittingIdeal (R := Γ(Z, V'.1))
          (M := Γ(pushforwardStructureSheaf (pullback.snd f k), V'.1)) m =
        Ideal.map (k.appLE V.1 V'.1 hV').hom
          ((idealSheaf (pushforwardStructureSheaf f) m).ideal V) := by
    rw [map_appLE_ideal_idealSheaf_of_isPullback hsq V V' hV' m,
      ideal_idealSheaf_pushforward]
  exact ((finiteLocallyFreeOfRank_fittingIdeal_tfae
    (R := Γ(Z, V'.1)) (M := Γ(pushforwardStructureSheaf (pullback.snd f k), V'.1)) r).out 2 1).mp
    (show fittingIdeal (R := Γ(Z, V'.1))
        (M := Γ(pushforwardStructureSheaf (pullback.snd f k), V'.1)) ((r : ℤ) - 1) = ⊥ ∧
      fittingIdeal (R := Γ(Z, V'.1))
        (M := Γ(pushforwardStructureSheaf (pullback.snd f k), V'.1)) (r : ℤ) = ⊤ from
      ⟨by rw [← show ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 by omega, key, hbot], (key _).trans htop⟩)

end Stacks.Fitting

namespace Stacks.Groupoids

open Stacks.Fitting Stacks.IdealSheaf Stacks.Morphisms

/-- On an affine open of the `r`-th stratum of the Fitting stratification lying over an affine
open of the object scheme, the sections of the pushforward of the structure sheaf along the base
change of source form a finite locally free module of rank `r`.

This is the affine-local form of the rank assertion of [Stacks Project, Tag 0AB9]: the stratum
lies inside the closed subscheme cut out by the `(r-1)`st Fitting ideal sheaf, where that ideal
sheaf dies, and misses the support of the `r`th one, where that one is the unit ideal; by base
change of Fitting ideals the same holds for the sections of the pullback, and Stacks Tag 07ZD
turns the pair of conditions into finite local freeness of rank `r`. -/
theorem module_isFiniteLocallyFreeOfRank_finiteStratification_stratum {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.source.left] (r : ℕ) (hr : 0 < r)
    (W : (finiteStratification G (r - 1)).subscheme.Opens)
    (hW : Set.range (W.ι ≫ (finiteStratification G (r - 1)).subschemeι) =
      ((finiteStratification G (r - 1)).support : Set G.objects.left) \
        ((finiteStratification G r).support : Set G.objects.left))
    (V : G.objects.left.affineOpens) (V' : W.toScheme.affineOpens)
    (hV' : V'.1 ≤ (W.ι ≫ (finiteStratification G (r - 1)).subschemeι) ⁻¹ᵁ V.1) :
    Module.IsFiniteLocallyFreeOfRank Γ(W.toScheme, V'.1)
      Γ(pushforwardStructureSheaf (pullback.snd G.source.left
        (W.ι ≫ (finiteStratification G (r - 1)).subschemeι)), V'.1) r :=
  module_isFiniteLocallyFreeOfRank_pushforward_pullback G.source.left _ r hr V V' hV'
    (map_appLE_ideal_eq_bot_of_factorsThrough _ W.ι V V'.1 hV')
    (map_appLE_ideal_eq_top_of_notMem_support _ _ (fun z ↦ (hW.subset ⟨z, rfl⟩).2) V V' hV')

end Stacks.Groupoids

end
