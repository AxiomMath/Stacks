module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyOfAPoint
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.AdditiveGroupVanishingAllDegrees
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.ConstantSheafGaloisModule
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.RootsOfUnityGaloisModuleIso
import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves on the small étale site of a point

Let `K` be a field, `Kˢᵉᵖ` a separable closure of it and `G = Gal(Kˢᵉᵖ/K)` the absolute Galois
group.  This file states the example [Stacks, Tag 03QV] in one declaration.

The example has two halves.  The first is a dictionary: under the equivalence of
[Stacks, Tag 04JQ] between abelian sheaves on `Spec(K)_étale` and discrete `G`-modules,

1. the constant sheaf `𝐙/n𝐙` corresponds to `𝐙/n𝐙` with the trivial `G`-action,
2. the sheaf `𝐆_m` corresponds to `(Kˢᵉᵖ)^*` with its `G`-action,
3. the sheaf `𝐆_a` corresponds to `(Kˢᵉᵖ, +)` with its `G`-action, and
4. the sheaf `μ_n` corresponds to `μ_n(Kˢᵉᵖ)` with its `G`-action.

The second half is two chains of equalities.  The multiplicative one,

  `0 = Pic(Spec K) = H¹_étale(Spec(K)_étale, 𝐆_m) = H¹(G, (Kˢᵉᵖ)^*)`,

is the one the source calls Hilbert's 90 theorem, and the additive one, for every `i ≥ 1`,

  `0 = H^i(Spec K, 𝒪) = H^i_étale(Spec(K)_étale, 𝐆_a) = H^i(G, Kˢᵉᵖ)`.

## Main definitions

* `AlgebraicGeometry.stacks03QV`: **the example, whole**.

## Implementation notes

**Why one declaration, and why it is a `def`.**  Clauses (1) to (4) are isomorphisms, that is
data, so the conjunction of the example's assertions is a product type and not a proposition; the
propositional half is collected under a single `PLift`.  The components are the declarations
listed below, each with its own docstring and proof; this declaration adds no mathematics and
exists to carry the tag on a statement of the whole example rather than on any one part of it.

**A chain of equalities between groups that all vanish is the vanishing of each.**  The source's
`0 = A = B = C` is therefore stated as `A = 0`, `B = 0` and `C = 0` together with the
identifications `B ≅ C` respectively `A ≅ B` and `B ≅ C` which the source's `=` signs assert.
Nothing is weakened: the identifications are the isomorphisms themselves, not merely the
assertion that both sides vanish.

**The displayed identifications the example recalls are not restated here.**  The source obtains
`H⁰_étale(S_étale, 𝐆_m) = Γ(S, 𝒪_S^*)`, `H¹_étale(S_étale, 𝐆_m) = H¹_Zar(S, 𝒪_S^*) = Pic(S)`,
`H^i_étale(S_étale, 𝐆_a) = H^i_Zar(S, 𝒪_S)` and `H^i(S_étale, ℱ) = H^i_Zar(S, ℱ)` for
quasi-coherent `ℱ` by citing Remark [Stacks, Tag 03P6], Theorem [Stacks, Tag 03P8] and Theorem
[Stacks, Tag 03P2]; they are the content of those tags and are registered there.  The two
identifications that the chains need are included below.

**The components.**

* clause (1): `AlgebraicGeometry.constantContinuousGModuleIso`, at the value `ULift (ZMod n)`;
* clause (2): `AlgebraicGeometry.multiplicativeContinuousGModuleIso`;
* clause (3): `AlgebraicGeometry.additiveContinuousGModuleIso`;
* clause (4): `AlgebraicGeometry.rootsOfUnityContinuousGModuleIso`;
* `0 = Pic(Spec K)`: `AlgebraicGeometry.subsingleton_picardGroup_spec_field`;
* `0 = H¹_étale(𝐆_m)`: `AlgebraicGeometry.subsingleton_multiplicativeSheafH_one`;
* `0 = H¹(G, (Kˢᵉᵖ)^*)`:
  `Stacks.GaloisCohomology.isZero_continuousGroupCohomology_unitsLift_one`;
* `H¹_étale(𝐆_m) ≅ H¹(G, (Kˢᵉᵖ)^*)`:
  `AlgebraicGeometry.multiplicativeSheafHAddEquivContinuousGroupCohomology`;
* `0 = H^i(Spec K, 𝒪)`: `AlgebraicGeometry.isZero_hgroup_structureSheaf_spec_field`;
* `H^i(Spec K, 𝒪) ≅ H^i_étale(𝐆_a)`:
  `AlgebraicGeometry.hgroupStructureSheafAddEquivSheafHAdditiveSheaf`;
* `0 = H^i_étale(𝐆_a)`: `AlgebraicGeometry.subsingleton_sheafH_additiveSheaf_of_isAffine`;
* `H^i_étale(𝐆_a) ≅ H^i(G, Kˢᵉᵖ)`:
  `AlgebraicGeometry.additiveSheafHAddEquivContinuousGroupCohomology`;
* `0 = H^i(G, Kˢᵉᵖ)`: `AlgebraicGeometry.isZero_continuousGroupCohomology_sepClosureAdd`.

**The big étale site and the geometric point are data, not hypotheses.**  The small étale site
of [Stacks, Tag 021B] is cut out of a big étale site containing `Spec K`, and the absolute Galois
group and the separable closure are presented by a geometric point; both exist for every field
(`AlgebraicGeometry.BigEtaleSite.containing` and
`AlgebraicGeometry.GeometricPoint.ofAlgebraicClosure`), and quantifying over them makes the
statement cover every choice.  Nothing is assumed of the field, of `n`, or of the characteristic.

## References

* [Stacks Project, Tag 03QV](https://stacks.math.columbia.edu/tag/03QV)
* [Stacks Project, Tag 04JQ](https://stacks.math.columbia.edu/tag/04JQ): the equivalence under
  which clauses (1) to (4) are read.
* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU): part (3), the
  identification of étale with Galois cohomology used by both chains.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] GeometricPoint.residueFieldAlgebra

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K))) (n : ℕ)

/-- Sheafification of abelian groups at the object universe of the small étale site. -/
local instance hasSheafify_objectUniverse_spec :
    HasSheafify (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u + 1} :=
  etaleSheaves_hasSheafify_of_univLE.{u, u + 1} _

/-- `Ext` of abelian sheaves at the object universe of the small étale site lives in that
universe. -/
local instance hasExt_objectUniverse_spec :
    HasExt.{u + 1} (Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  haveI : IsGrothendieckAbelian.{u + 1}
      (Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse _
  CategoryTheory.IsGrothendieckAbelian.hasExt _

/-- **Stacks Project, Tag 03QV, whole.**  Sheaves on `Spec(K)_étale` for `K` a field, with
`G = Gal(Kˢᵉᵖ/K)` the absolute Galois group.

Under the equivalence of Tag 04JQ between abelian sheaves on the small étale site of `Spec K` and
discrete `G`-modules: (1) the constant sheaf `𝐙/n𝐙` corresponds to `𝐙/n𝐙` with the trivial
`G`-action, (2) `𝐆_m` corresponds to `(Kˢᵉᵖ)^*`, (3) `𝐆_a` corresponds to `(Kˢᵉᵖ, +)`, and
(4) `μ_n` corresponds to `μ_n(Kˢᵉᵖ)`, each with its `G`-action.  Moreover

  `0 = Pic(Spec K) = H¹_étale(Spec(K)_étale, 𝐆_m) = H¹(G, (Kˢᵉᵖ)^*)`,

which is Hilbert's 90 theorem, and, for every `i ≥ 1`,

  `0 = H^i(Spec K, 𝒪) = H^i_étale(Spec(K)_étale, 𝐆_a) = H^i(G, Kˢᵉᵖ)`.

The module docstring lists the declaration proving each component. -/
@[stacks 03QV]
public def stacks03QV :
    ((etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj
        (constantEtaleSheaf B K hK (ULift.{u + 1} (ZMod n))) ≅
      constantGModule K sbar (ULift.{u + 1} (ZMod n))) ×
    ((etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj
        (multiplicativeSheafRestriction B K hK) ≅ sepClosureUnitsGModule K sbar) ×
    ((etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj
        (additiveSheafRestriction B K hK) ≅ sepClosureAddGModule K sbar) ×
    ((etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj
        (rootsOfUnitySheafRestriction B K hK n) ≅ sepClosureRootsOfUnityGModule K sbar n) ×
    (Sheaf.H.{u + 1, u + 1}
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of K))) 1 ≃+
      continuousGroupCohomology.{u, u + 1} (GeometricPoint.absoluteGaloisGroup sbar) 1
        (sepClosureUnitsGModule K sbar)) ×
    (∀ i : ℕ, Hgroup (Spec (CommRingCat.of K)).ringCatSheaf ⊤ (i + 1)
          (Scheme.unitModule (Spec (CommRingCat.of K))) ≃+
        Sheaf.H.{u + 1, u + 1}
          (Stacks.ArtinSchreier.additiveSheaf.{u, u + 1} (Spec (.of K))) (i + 1)) ×
    (∀ q : ℕ, Sheaf.H.{u + 1, u + 1}
          (Stacks.ArtinSchreier.additiveSheaf.{u, u + 1} (Spec (.of K))) q ≃+
        continuousGroupCohomology.{u, u + 1} (GeometricPoint.absoluteGaloisGroup sbar) q
          (sepClosureAddGModule K sbar)) ×
    PLift (Subsingleton (Spec (CommRingCat.of K)).picardGroup ∧
      Subsingleton (Sheaf.H.{u + 1, u + 1}
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of K))) 1) ∧
      IsZero (continuousGroupCohomology.{u, u + 1}
        (GeometricPoint.absoluteGaloisGroup sbar) 1 (sepClosureUnitsGModule K sbar)) ∧
      (∀ i : ℕ, 0 < i → IsZero (Hgroup (Spec (CommRingCat.of K)).ringCatSheaf ⊤ i
        (Scheme.unitModule (Spec (CommRingCat.of K))))) ∧
      (∀ i : ℕ, 0 < i → Subsingleton (Sheaf.H.{u + 1, u + 1}
        (Stacks.ArtinSchreier.additiveSheaf.{u, u + 1} (Spec (.of K))) i)) ∧
      (∀ i : ℕ, 0 < i → IsZero (continuousGroupCohomology.{u, u + 1}
        (GeometricPoint.absoluteGaloisGroup sbar) i (sepClosureAddGModule K sbar)))) :=
  ⟨constantContinuousGModuleIso B K hK sbar (ULift.{u + 1} (ZMod n)),
    multiplicativeContinuousGModuleIso B K hK sbar,
    additiveContinuousGModuleIso B K hK sbar,
    rootsOfUnityContinuousGModuleIso B K hK sbar n,
    multiplicativeSheafHAddEquivContinuousGroupCohomology B K hK sbar 1,
    fun i => hgroupStructureSheafAddEquivSheafHAdditiveSheaf (Spec (CommRingCat.of K)) i,
    fun q => additiveSheafHAddEquivContinuousGroupCohomology B K hK sbar q,
    PLift.up ⟨subsingleton_picardGroup_spec_field K,
      subsingleton_multiplicativeSheafH_one B K hK sbar,
      Stacks.GaloisCohomology.isZero_continuousGroupCohomology_unitsLift_one.{u, u + 1} _ _,
      fun i hi => isZero_hgroup_structureSheaf_spec_field K i hi,
      fun i hi => subsingleton_sheafH_additiveSheaf_of_isAffine (Spec (CommRingCat.of K)) i hi,
      fun i hi => isZero_continuousGroupCohomology_sepClosureAdd B K hK sbar i hi⟩⟩

end AlgebraicGeometry

end
