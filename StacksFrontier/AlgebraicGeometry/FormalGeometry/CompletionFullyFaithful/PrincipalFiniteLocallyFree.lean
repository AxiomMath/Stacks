module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonAdditive
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.AmpleEmbedding
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.PrincipalComplement
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.InternalHomLocallyFree
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.NeighbourhoodHomsComparison

/-!
# From the comparison for `𝒪_U` to the comparison for every finite locally free module

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` and let `U = Spec(A) ∖ V(𝔞)`. The comparison map
`Stacks.Algebraization.comparisonMap A I a F` of [Stacks, Tag 0EG2] goes from the colimit of the
sections of `F` over the open neighbourhoods of `U ∩ V(I)` to the limit of the sections of the
quotients `F / Iⁿ F` on `U`.

This file runs the implications (1) ⇒ (2) ⇒ (3) of [Stacks, Tag 0EK2] for that map: if the
comparison is an isomorphism for `𝒪_U`, it is an isomorphism for every finite locally free
`𝒪_U`-module, and hence — by the reduction of
`Stacks.Algebraization.NeighbourhoodHoms.nbhdHomComparison_bijective_of_isIso` — the completion
functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(U, I𝒪_U)` is fully faithful on finite locally free objects.

The argument is the one the source gives. `U` is quasi-affine, so `𝒪_U` is an ample invertible
module and all of its tensor powers are again `𝒪_U`; that is (1) ⇒ (2). For (2) ⇒ (3) a finite
locally free `ℰ` is embedded in a finite direct sum of high twists of the ample module by
`Stacks.Algebraization.exists_dual_embedding`, and the comparison map for a submodule of a module
for which it is an isomorphism is again an isomorphism
(`Stacks.Algebraization.isIso_comparisonMap_of_mono`, the sharpened [Stacks, Tag 0H48]).

## Main results

* `Stacks.Algebraization.isIso_comparisonMap_of_amplePowers` — **[Stacks, Tag 0EK2], (2) ⇒ (3)**
  for the comparison map: an ample invertible module whose high twists have invertible comparison
  makes the comparison invertible for every finite locally free module.
* `Stacks.Algebraization.isIso_comparisonMap_of_isFiniteLocallyFree` — **(1) ⇒ (3)**: the
  comparison for `𝒪_U` alone suffices.
* `Stacks.Algebraization.nbhdHomComparison_bijective_of_isIso_unit` — **(1) ⇒ (4)**: full
  faithfulness of the completion functor on finite locally free objects.

## Implementation notes

The source's sequence `0 → ℰ → (L^{⊗ p})^{⊕ r} → (L^{⊗ q})^{⊕ s}` is built in full by
`exists_dual_embedding`, but only its first map is used here: the sharpened form of
[Stacks, Tag 0H48] asks nothing of the third term of a short exact sequence, so a monomorphism
`ℰ ⟶ (L^{⊗ p})^{⊕ r}` into a module with invertible comparison is enough and the second map of
the sequence is discarded.

Three spellings of the tensor powers of an invertible module meet here, as they do in
`Stacks.Algebraization.sectionsCompleteFiniteLocallyFree_of_sectionsCompleteAmplePowers`:
`Stacks.SheafOfModules.Invertible.tensorPower`, over which
`AlgebraicGeometry.Scheme.Modules.IsAmple` and hence condition (2) are stated,
`Stacks.Ample.tensorPowModule`, over which `Stacks.Ample.IsAmple` and `exists_dual_embedding` are
stated, and `SheafOfModules.unit` for the zeroth power. They are identified by
`Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso` and
`Stacks.SheafOfModules.Invertible.tensorPowerUnitIso`, and the comparison map only sees a module
up to isomorphism, by `Stacks.Algebraization.isIso_comparisonMap_of_iso`.

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0H48](https://stacks.math.columbia.edu/tag/0H48)
* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Ample Stacks.AlgebraicGeometry.ReflexiveModules

noncomputable section

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I a : Ideal A)

/-- A finite locally free module on `U = Spec(A) ∖ V(𝔞)` is coherent, `U` being Noetherian. -/
public theorem isCoherent_of_isFiniteLocallyFree_complement
    (E : (complementZeroLocus A a : Scheme).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (complementZeroLocus A a : Scheme).ringCatSheaf) E) :
    E.IsCoherent :=
  have : IsLocallyNoetherian (complementZeroLocus A a : Scheme) :=
    AlgebraicGeometry.IsNoetherian.toIsLocallyNoetherian
  Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree _ E

/-- **[Stacks, Tag 0EK2], (2) implies (3), for the comparison map of [Stacks, Tag 0EG2].**
Let `L` be an ample invertible module on `U = Spec(A) ∖ V(𝔞)` whose tensor powers `L^{⊗ m}` have
invertible comparison map for all `m ≫ 0`. Then the comparison map is invertible for every finite
locally free `𝒪_U`-module.

A finite locally free `ℰ` is a submodule of a finite direct sum of copies of one high twist of
`L` (`Stacks.Algebraization.exists_dual_embedding`); the comparison for that direct sum is
invertible because it is invertible for the twist and both sides of the comparison are additive
(`Stacks.Algebraization.isIso_comparisonMap_bicone`), and the comparison for a submodule of a
module with invertible comparison is invertible
(`Stacks.Algebraization.isIso_comparisonMap_of_mono`). -/
public theorem isIso_comparisonMap_of_amplePowers
    (L : (complementZeroLocus A a : Scheme).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      (complementZeroLocus A a : Scheme).toRingedSpace.presheaf
      (structureSheafRing (complementZeroLocus A a : Scheme).toRingedSpace).property L)
    (hample : AlgebraicGeometry.Scheme.Modules.IsAmple (complementZeroLocus A a : Scheme) L)
    (N : ℕ)
    (hN : ∀ m : ℕ, N ≤ m → IsIso (comparisonMap A I a
      (Stacks.SheafOfModules.Invertible.tensorPower
        (complementZeroLocus A a : Scheme).toRingedSpace.presheaf
        (structureSheafRing (complementZeroLocus A a : Scheme).toRingedSpace).property L (m : ℤ))))
    (E : (complementZeroLocus A a : Scheme).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (complementZeroLocus A a : Scheme).ringCatSheaf) E) :
    IsIso (comparisonMap A I a E) := by
  classical
  have : IsLocallyNoetherian (complementZeroLocus A a : Scheme) :=
    AlgebraicGeometry.IsNoetherian.toIsLocallyNoetherian
  have := hL
  have hLinv : IsInvertibleModule (complementZeroLocus A a : Scheme) L :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  have hampleA : IsAmple (complementZeroLocus A a : Scheme) L :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ L).mp hample
  -- the comparison for every sufficiently high twist, in the `tensorPowModule` spelling
  have hpow : ∀ n : ℤ, (N : ℤ) ≤ n →
      IsIso (comparisonMap A I a (tensorPowModule (complementZeroLocus A a : Scheme) L n)) := by
    intro n hn
    have hn0 : (0 : ℤ) ≤ n := le_trans (Int.natCast_nonneg N) hn
    have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn0
    have hNn : N ≤ n.toNat := by omega
    have h1 := isIso_comparisonMap_of_iso A I a
      (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso
        (complementZeroLocus A a : Scheme) L ((n.toNat : ℕ) : ℤ)) (hN n.toNat hNn)
    rwa [hcast] at h1
  -- the embedding of `E` into a finite sum of high twists
  obtain ⟨p, q, ιp, ιq, hιp, hιq, hpN, hqN, bp, hbp, bq, hbq, q₀, hq₀, β, w, hrefl, hmono, hex,
    huniv⟩ := exists_dual_embedding L hampleA (N : ℤ) E hE
  have := hιp
  have := hmono
  have : Fintype ιp := Fintype.ofFinite ιp
  -- finite local freeness, hence coherence, of everything in sight
  have hEc : E.IsCoherent := isCoherent_of_isFiniteLocallyFree_complement A a E hE
  have hTwist : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (complementZeroLocus A a : Scheme).ringCatSheaf)
      (tensorPowModule (complementZeroLocus A a : Scheme) L (-p)) :=
    isFiniteLocallyFree_tensorPowModule L (-p)
  have hbpflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (complementZeroLocus A a : Scheme).ringCatSheaf) bp.pt :=
    AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isBilimit_const _ hbp
  have hdualTwist : (dualSheaf
      (tensorPowModule (complementZeroLocus A a : Scheme) L (-p))).IsCoherent :=
    isCoherent_of_isFiniteLocallyFree_complement A a _
      (isFiniteLocallyFree_dualSheaf _ hTwist)
  have hdualpt : (dualSheaf bp.pt).IsCoherent :=
    isCoherent_of_isFiniteLocallyFree_complement A a _ (isFiniteLocallyFree_dualSheaf _ hbpflf)
  have hdualbicone : (dualBicone bp).pt.IsCoherent := hdualpt
  -- the comparison for the dual of the finite sum of twists
  have hP : ∀ _i : ιp, IsIso (comparisonMap A I a
      (dualSheaf (tensorPowModule (complementZeroLocus A a : Scheme) L (-p)))) := fun _ =>
    isIso_comparisonMap_of_iso A I a
      (dualTensorPowIso (complementZeroLocus A a : Scheme) L p) (hpow p hpN)
  have hSum : IsIso (comparisonMap A I a (dualSheaf bp.pt)) :=
    isIso_comparisonMap_bicone A I a (dualBicone bp) (dualBicone_isBilimit bp hbp) hP
  exact isIso_comparisonMap_of_mono A I a _ hmono hSum

/-- **[Stacks, Tag 0EK2], (1) implies (3), for the comparison map of [Stacks, Tag 0EG2].** If the
comparison map for `𝒪_U` is invertible, it is invertible for every finite locally free
`𝒪_U`-module.

`U = Spec(A) ∖ V(𝔞)` is quasi-affine, so `𝒪_U` is an ample invertible module, and every tensor
power of `𝒪_U` is again `𝒪_U`; that is the implication (1) ⇒ (2). -/
public theorem isIso_comparisonMap_of_isFiniteLocallyFree
    (hunit : IsIso (comparisonMap A I a
      (SheafOfModules.unit (complementZeroLocus A a : Scheme).ringCatSheaf)))
    (E : (complementZeroLocus A a : Scheme).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (complementZeroLocus A a : Scheme).ringCatSheaf) E) :
    IsIso (comparisonMap A I a E) := by
  have hinv : AlgebraicGeometry.SheafOfModules.IsInvertible
      (complementZeroLocus A a : Scheme).toRingedSpace.presheaf
      (structureSheafRing (complementZeroLocus A a : Scheme).toRingedSpace).property
      (SheafOfModules.unit (complementZeroLocus A a : Scheme).ringCatSheaf) :=
    AlgebraicGeometry.Scheme.Modules.isInvertible_unit (complementZeroLocus A a : Scheme)
  have := hinv
  refine isIso_comparisonMap_of_amplePowers A I a _ hinv
    (AlgebraicGeometry.Scheme.Modules.isAmple_unit_of_isQuasiAffine
      (complementZeroLocus A a : Scheme)) 0 (fun m _ => ?_) E hE
  exact isIso_comparisonMap_of_iso A I a
    (Stacks.SheafOfModules.Invertible.tensorPowerUnitIso
      (complementZeroLocus A a : Scheme).toRingedSpace.presheaf
      (structureSheafRing (complementZeroLocus A a : Scheme).toRingedSpace).property m).symm
    hunit

/-- **[Stacks, Tag 0EK2], (1) implies (4).** If the comparison map of [Stacks, Tag 0EG2] is
invertible for `𝒪_U` on `U = Spec(A) ∖ V(𝔞)`, then the completion functor
`colim_𝒱 Coh(𝒪_V) ⟶ Coh(U, I𝒪_U)` is fully faithful on the full subcategory of finite locally
free objects: for finite locally free coherent `𝒢`, `ℱ` the canonical map
`Stacks.Algebraization.NeighbourhoodHoms.nbhdHomComparison` is bijective.

The internal hom of two finite locally free modules is finite locally free, so the comparison is
invertible for it by `Stacks.Algebraization.isIso_comparisonMap_of_isFiniteLocallyFree`, and
`Stacks.Algebraization.NeighbourhoodHoms.nbhdHomComparison_bijective_of_isIso` turns that into
bijectivity of the map on morphisms. -/
public theorem nbhdHomComparison_bijective_of_isIso_unit
    (hunit : IsIso (comparisonMap A I a
      (SheafOfModules.unit (complementZeroLocus A a : Scheme).ringCatSheaf)))
    (G F : AlgebraicGeometry.SheafOfModules.CoherentModules
      (complementZeroLocus A a : Scheme).ringCatSheaf)
    (hG : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree G.obj)
    (hF : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree F.obj) :
    Function.Bijective (NeighbourhoodHoms.nbhdHomComparison A I a G F) :=
  have : IsLocallyNoetherian (complementZeroLocus A a : Scheme) :=
    AlgebraicGeometry.IsNoetherian.toIsLocallyNoetherian
  NeighbourhoodHoms.nbhdHomComparison_bijective_of_isIso A I a G F
    (isIso_comparisonMap_of_isFiniteLocallyFree A I a hunit _
      ((AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff _).1
        (isFiniteLocallyFree_scheme_internalHomCoherent G F hG hF)))

end Stacks.Algebraization

end

end
