module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ComponentEnvelope
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.SigmaDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.CriteriaQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.SigmaLocallyBounded
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chern classes of a perfect object whose base has quasi-compact irreducible components

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `E` be a perfect object of `D(𝒪_X)`. Clause (3) of
[Stacks, Tag 0GUE] is that the irreducible components of `X` be quasi-compact. The envelope the
source builds for it is the disjoint union `∐ Wᵢ` over the irreducible components, each `Wᵢ`
Noetherian with the resolution property and affine diagonal; that envelope is
`Stacks.Chow.exists_isEnvelope_sigma_of_isCompact_irreducibleComponents`.

This file carries out the derived algebra over such a source. On each summand `Lf^*E` restricts
to a perfect object, hence is isomorphic to a bounded complex `𝓔ᵢ^•` of finite locally free
`𝒪_{Wᵢ}`-modules by [Stacks, Tag 0F8F]; the summands' complexes assemble into one complex on
`∐ Wᵢ` whose restriction to each summand is `𝓔ᵢ^•`, and the isomorphism in `D(𝒪_{∐ Wᵢ})` is
*built* out of the summands' isomorphisms rather than asserted.

## Main results

* `Stacks.Chow.exists_iso_Q_of_forall_iso_Q_sigmaι` — the gluing step: a family of isomorphisms
  between the classes of the summandwise restrictions of a complex on `∐ Wᵢ` and the classes of
  complexes on the summands produces one complex on `∐ Wᵢ` restricting to those and one
  isomorphism of classes over `∐ Wᵢ`.
* `Stacks.Chow.exists_isLocallyBoundedFiniteLocallyFree_iso_derivedPullback_sigma` — the derived
  algebra: over a coproduct of quasi-compact, quasi-separated, semi-separated schemes with the
  resolution property, the derived pullback of a perfect object is isomorphic to a locally
  bounded complex of finite locally free modules.
* `Stacks.Chow.hasDefinedChernClasses_of_isCompact_irreducibleComponents` —
  **[Stacks, Tag 0GUE] clause (3)**.

## Implementation notes

The derived category of `∐ Wᵢ` is *not* the product of the derived categories of the summands:
Mathlib's `CategoryTheory.Functor.IsLocalization.pi` carries a finiteness hypothesis on the
index, which the set of irreducible components does not satisfy. So the isomorphism cannot be
read off a product decomposition. It is built instead, in three steps, each of which is a
statement about complexes rather than about the derived category (the derived-category input,
the gluing of a family of isomorphisms over the summands, is
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/SigmaDerivedCategory.lean`):

* a K-flat complex `𝓚^•` representing `Lf^*E` ([Stacks, Tag 06YF]), which has the property that
  its degreewise restriction to a summand computes the derived pullback there
  (`Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat`);
* on each summand, the resulting isomorphism `Q(𝓚^•|ᵢ) ≅ Q(𝓔ᵢ^•)`;
* the family of those isomorphisms glued into one isomorphism over `∐ Wᵢ` by
  `AlgebraicGeometry.nonempty_iso_Q_of_forall_iso_Q_sigmaι`, which reads each of them as a roof
  of actual complexes and glues the two legs — possible because degreewise restriction to the
  summands is an equivalence (`AlgebraicGeometry.sigmaComplexEquivalence`) and quasi-isomorphy
  is detected summand by summand
  (`AlgebraicGeometry.quasiIso_of_quasiIso_pullback_sigmaι`).

Local boundedness with finite locally free terms of the glued complex is
`AlgebraicGeometry.isLocallyBoundedFiniteLocallyFree_of_pullback_sigmaι`, each summand's
restriction being isomorphic to a bounded complex of finite locally free modules.

## References

* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0F8F](https://stacks.math.columbia.edu/tag/0F8F)
* [Stacks Project, Tag 06YF](https://stacks.math.columbia.edu/tag/06YF)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.PseudoCoherence
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-- Local boundedness with finite locally free terms depends only on the isomorphism class of a
complex: finite local freeness of a term and vanishing of a restriction are both invariant under
isomorphism. -/
theorem IsLocallyBoundedFiniteLocallyFree.of_iso {X : Scheme.{u}}
    {P P' : CochainComplex X.Modules ℤ} (e : P ≅ P')
    (hP : IsLocallyBoundedFiniteLocallyFree P) :
    IsLocallyBoundedFiniteLocallyFree P' := by
  refine ⟨fun n => ?_, fun x => ?_⟩
  · have hn : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (P.X n) := hP.1 n
    exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
      (show P.X n ≅ P'.X n from
        (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).mapIso e)
  · obtain ⟨U, hxU, lo, hi, hvan⟩ := hP.2 x
    refine ⟨U, hxU, lo, hi, fun n hn => (hvan n hn).of_iso ?_⟩
    exact (restrictModules X.toRingedSpace U).mapIso
      ((HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).mapIso e).symm

/-- **A K-flat complex computes the derived pullback to a summand.** For a K-flat complex `K` on
`∐ W`, the restriction of its class to the summand `i` is the class of its degreewise
restriction. -/
def derivedPullbackSigmaιQIso {I : Type u} (W : I → Scheme.{u})
    (K : CochainComplex (∐ W : Scheme.{u}).Modules ℤ)
    (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex
      (∐ W : Scheme.{u}).toRingedSpace K) (i : I) :
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Sigma.ι W i).toLRSHom.toShHom).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (((Scheme.Modules.pullback (Sigma.ι W i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
  Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat _ K hK

/-- **Restriction to a summand of a derived pullback along the induced morphism out of a
coproduct** is the derived pullback along that summand's own morphism, the two composites being
equal by the universal property of the coproduct. -/
def derivedPullbackSigmaDescIso {I : Type u} {W : I → Scheme.{u}} {X : Scheme.{u}}
    (g : ∀ i, W i ⟶ X) (E : DerivedCategory X.Modules) (i : I) :
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Sigma.ι W i).toLRSHom.toShHom).obj
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Sigma.desc g).toLRSHom.toShHom).obj E) ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (g i).toLRSHom.toShHom).obj E :=
  (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (Sigma.ι W i).toLRSHom.toShHom (Sigma.desc g).toLRSHom.toShHom).app E ≪≫
    (eqToIso (Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq
      (congrArg (fun h : W i ⟶ X => h.toLRSHom.toShHom) (Sigma.ι_desc g i)))).app E

/-- **Gluing a family of isomorphisms of classes of complexes on the summands.** Let `K` be a
complex on `∐ W` and let `M i` be complexes on the summands with `Q(K|ᵢ) ≅ Q(M i)` for every
`i`. Then there is a complex `P` on `∐ W` whose restriction to each summand is isomorphic to
`M i` and with `Q(K) ≅ Q(P)`.

Degreewise restriction to the summands is an equivalence on complexes, so the `M i` assemble
into a complex `P` on `∐ W`; the isomorphism of classes is then
`AlgebraicGeometry.nonempty_iso_Q_of_forall_iso_Q_sigmaι` at `K` and `P`. -/
theorem exists_iso_Q_of_forall_iso_Q_sigmaι {I : Type u} (W : I → Scheme.{u})
    (K : CochainComplex (∐ W : Scheme.{u}).Modules ℤ)
    (M : ∀ i, CochainComplex (W i).Modules ℤ)
    (h : ∀ i, DerivedCategory.Q.obj ((AlgebraicGeometry.sigmaComplexFunctor W).obj K i) ≅
      DerivedCategory.Q.obj (M i)) :
    ∃ P : CochainComplex (∐ W : Scheme.{u}).Modules ℤ,
      (∀ i, Nonempty ((AlgebraicGeometry.sigmaComplexFunctor W).obj P i ≅ M i)) ∧
        Nonempty (DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj P) := by
  obtain ⟨P, ⟨v⟩⟩ : ∃ P : CochainComplex (∐ W : Scheme.{u}).Modules ℤ,
      Nonempty ((AlgebraicGeometry.sigmaComplexFunctor W).obj P ≅ M) :=
    ⟨(AlgebraicGeometry.sigmaComplexFunctor W).objPreimage M,
      ⟨(AlgebraicGeometry.sigmaComplexFunctor W).objObjPreimageIso M⟩⟩
  exact ⟨P, fun i => ⟨CategoryTheory.Pi.isoApp v i⟩,
    AlgebraicGeometry.nonempty_iso_Q_of_forall_iso_Q_sigmaι W K P fun i =>
      h i ≪≫ DerivedCategory.Q.mapIso (CategoryTheory.Pi.isoApp v i).symm⟩

/-- **The derived pullback of a perfect object to a coproduct of schemes with the resolution
property is a locally bounded complex of finite locally free modules.** Let `g i : W i ⟶ X` be a
family of morphisms with each `W i` quasi-compact, quasi-separated, semi-separated and carrying
the resolution property, let `f : ∐ W ⟶ X` be the induced morphism and let `E` be a perfect
object of `D(𝒪_X)`. Then `Lf^*E` is isomorphic in `D(𝒪_{∐ W})` to a locally bounded complex of
finite locally free `𝒪_{∐ W}`-modules.

On each summand `L(g i)^*E` is perfect by [Stacks, Tag 09UA], hence isomorphic to a bounded
complex `𝓔ᵢ^•` of finite locally free modules by [Stacks, Tag 0F8F]. A K-flat complex `𝓚^•`
representing `Lf^*E` has the property that its degreewise restriction to the summand `i`
represents the restriction of `Lf^*E` there, so there is an isomorphism `Q(𝓚^•|ᵢ) ≅ Q(𝓔ᵢ^•)`;
`Stacks.Chow.exists_iso_Q_of_forall_iso_Q_sigmaι` glues that family. -/
theorem exists_isLocallyBoundedFiniteLocallyFree_iso_derivedPullback_sigma
    {I : Type u} {W : I → Scheme.{u}} {X : Scheme.{u}} (g : ∀ i, W i ⟶ X)
    [∀ i, CompactSpace (W i)] [∀ i, QuasiSeparatedSpace (W i)]
    [∀ i, HasResolutionProperty (W i)]
    [∀ i, IsAffineHom (pullback.diagonal (terminal.from (W i)))]
    (E : DerivedCategory X.Modules) (hE : IsPerfect (X := X.toRingedSpace) E) :
    ∃ P : CochainComplex (∐ W : Scheme.{u}).Modules ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (Sigma.desc g).toLRSHom.toShHom).obj E ≅ DerivedCategory.Q.obj P) := by
  classical
  obtain ⟨K, k, hKflat, _, hk, _⟩ := Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution
    (∐ W : Scheme.{u}).toRingedSpace
    ((DerivedCategory.Q : CochainComplex (∐ W : Scheme.{u}).Modules ℤ ⥤ _).objPreimage
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Sigma.desc g).toLRSHom.toShHom).obj E))
  have hkIso : IsIso (DerivedCategory.Q.map k) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ k).2 hk
  have eK : DerivedCategory.Q.obj K ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Sigma.desc g).toLRSHom.toShHom).obj E :=
    asIso (DerivedCategory.Q.map k) ≪≫
      (DerivedCategory.Q : CochainComplex (∐ W : Scheme.{u}).Modules ℤ ⥤ _).objObjPreimageIso _
  have hperf : ∀ i, IsPerfect (X := (W i).toRingedSpace)
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (g i).toLRSHom.toShHom).obj E) := fun i =>
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
      (g i).toLRSHom.toShHom E hE
  choose Eb hEb hEbIso using fun i =>
    exists_boundedFiniteLocallyFree_iso_of_affineDiagonal (W i) _ (hperf i)
  obtain ⟨P, hPrestrict, ⟨eP⟩⟩ := exists_iso_Q_of_forall_iso_Q_sigmaι W K Eb fun i =>
    (derivedPullbackSigmaιQIso W K hKflat i).symm ≪≫
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Sigma.ι W i).toLRSHom.toShHom).mapIso eK ≪≫
      derivedPullbackSigmaDescIso g E i ≪≫ (hEbIso i).some.symm
  refine ⟨P, ?_, ⟨eK.symm ≪≫ eP⟩⟩
  refine AlgebraicGeometry.isLocallyBoundedFiniteLocallyFree_of_pullback_sigmaι W P fun i => ?_
  exact IsLocallyBoundedFiniteLocallyFree.of_iso ((hPrestrict i).some).symm
    (isLocallyBoundedFiniteLocallyFree_of_boundedFiniteLocallyFreeComplex (hEb i))

/-- **[Stacks, Tag 0GUE] clause (3).** Let `(S, δ)` be the base situation of chapter 42, let `X`
be locally of finite type over `S` with quasi-compact irreducible components, and let `E` be a
perfect object of `D(𝒪_X)`. Then the Chern classes of `E` are defined: there is an envelope
`f : Y ⟶ X` such that `Lf^*E` is isomorphic in `D(𝒪_Y)` to a locally bounded complex of finite
locally free `𝒪_Y`-modules.

`X` is locally Noetherian, the base being locally Noetherian and `X` locally of finite type over
it, so `Stacks.Chow.exists_isEnvelope_sigma_of_isCompact_irreducibleComponents` supplies an
envelope `∐ W ⟶ X` whose summands are Noetherian — hence quasi-compact and quasi-separated —
with the resolution property and affine diagonal. Then
`Stacks.Chow.exists_isLocallyBoundedFiniteLocallyFree_iso_derivedPullback_sigma` represents
`Lf^*E`, which is clause (1) of the source.

Every hypothesis is a hypothesis of the source: the Chow situation, `X` locally of finite type
over its base, `E` perfect, and quasi-compactness of the irreducible components of `X`. Local
Noetherianity, the envelope, the summands' resolution property and affine diagonal, and the
complex are all derived. -/
@[stacks 0GUE "clause (3): the irreducible components of X are quasi-compact.  The conclusion \
is the full one: the Chern classes of E are defined, i.e. there is an envelope f : Y -> X with \
Lf^*E isomorphic in D(O_Y) to a locally bounded complex of finite locally free O_Y-modules, \
which is Tag 0F9E (1).  The hypotheses are exactly the source's: the base situation of Tag \
02QL, X locally of finite type over its base, E perfect, and the irreducible components of X \
quasi-compact"]
theorem hasDefinedChernClasses_of_isCompact_irreducibleComponents
    (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (hqc : ∀ Z ∈ irreducibleComponents X, IsCompact Z)
    (E : DerivedCategory X.Modules) (hE : IsPerfect (X := X.toRingedSpace) E) :
    HasDefinedChernClasses E := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  obtain ⟨I, W, g, henv, hWdata⟩ :=
    exists_isEnvelope_sigma_of_isCompact_irreducibleComponents X hqc
  have hnoeth : ∀ i, IsNoetherian (W i) := fun i => (hWdata i).1
  have : ∀ i, CompactSpace (W i) := fun i => (hnoeth i).toCompactSpace
  have : ∀ i, QuasiSeparatedSpace (W i) := fun i => by
    have := hnoeth i
    infer_instance
  have : ∀ i, HasResolutionProperty (W i) := fun i => (hWdata i).2.1
  have : ∀ i, IsAffineHom (pullback.diagonal (terminal.from (W i))) :=
    fun i => (hWdata i).2.2
  obtain ⟨P, hP, hrep⟩ :=
    exists_isLocallyBoundedFiniteLocallyFree_iso_derivedPullback_sigma g E hE
  exact hasDefinedChernClasses_of_envelope (Sigma.desc g) henv E P hP hrep

end Stacks.Chow

end
