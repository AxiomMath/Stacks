module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.CriteriaComponents
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TriangleAdditivityResolution
public import StacksCore.Tactic.StacksAttribute

/-!
# Additivity across a triangle over a base with quasi-compact irreducible components

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` be a distinguished triangle in `D(𝒪_X)`
with `E₁` and `E₂` perfect. Condition (3) of [Stacks, Tag 0F9F] is that the irreducible
components of `X` be quasi-compact. The envelope the source builds for it is the disjoint union
`∐ Wᵢ` over those components, each `Wᵢ` Noetherian with the resolution property and affine
diagonal; that envelope is
`Stacks.Chow.exists_isEnvelope_sigma_of_isCompact_irreducibleComponents`.

This file carries out the derived algebra over such a source and **registers Stacks 0F9F under
condition (3)**, alongside its conditions (1) and (2) in
`StacksFrontier/AlgebraicGeometry/Chow/ChernClassDerived/TriangleAdditivity.lean` and its condition
(4) in
`StacksFrontier/AlgebraicGeometry/Chow/ChernClassDerived/TriangleAdditivityQuasiCompact.lean`.

## Main results

* `Stacks.Chow.nonempty_iso_Q_derivedPullback_sigmaDesc` — a family of isomorphisms presenting
  the derived pullbacks to the summands by the summandwise restrictions of one complex on
  `∐ W` produces an isomorphism over `∐ W`.
* `Stacks.Chow.exists_boundedFiniteLocallyFree_sigma_of_isPerfect` — [Stacks, Tag 0F8F] over
  such a coproduct, keeping the summands' bounded complexes.
* `Stacks.Chow.exists_isLocallyBoundedFiniteLocallyFree_roof_sigma` — [Stacks, Tag 0F8G] over
  such a coproduct: a morphism of `D(𝒪_{∐ W})` between the classes of two such complexes is a
  roof whose left leg is a quasi-isomorphism and whose apex is a locally bounded complex of
  finite locally free modules.
* `Stacks.Chow.exists_isLocallyBoundedFiniteLocallyFree_square_sigma` — the same with the
  objects of `D(𝒪_{∐ W})` presented only up to isomorphism, which is the shape condition (1) of
  the source asks for.
* `Stacks.Chow.triangleChernAdditive_of_isCompact_irreducibleComponents` —
  **[Stacks, Tag 0F9F] under condition (3) of the source**.

## Implementation notes

What condition (3) needs beyond clause (3) of [Stacks, Tag 0GUE] — which is
`Stacks.Chow.hasDefinedChernClasses_of_isCompact_irreducibleComponents` and asks only for an
isomorphism — is the *commuting square*: the map `α : 𝓔₁^• ⟶ 𝓔₂^•` glued from the summands' maps
has to represent `Lf^*E₁ ⟶ Lf^*E₂`, which is an equation in `D(𝒪_{∐ Wᵢ})`, and each summand's
own square gives that equation only after restriction to that summand.

The derived category of `∐ Wᵢ` is not the product of the derived categories of the summands, so
the equation cannot be read off a product decomposition. What replaces it is that the derived
pullbacks to the summands are jointly **faithful**:
`AlgebraicGeometry.eq_of_forall_derivedPullback_sigmaι_map_eq`, in
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/SigmaDerivedCategory.lean`. An equation
between two morphisms of `D(𝒪_{∐ Wᵢ})` may therefore be checked summand by summand, and that is
exactly how the square is obtained here, through
`AlgebraicGeometry.Q_map_eq_comp_of_forall_sigmaι`.

The three steps over the coproduct mirror the three steps of
`Stacks.Chow.triangleChernAdditive_of_resolutionProperty_envelope` over a single scheme with the
resolution property: [Stacks, Tag 0F8F] on each summand, then [Stacks, Tag 0F8G] on each
summand, then the assembly. The first two are glued by the equivalence
`AlgebraicGeometry.sigmaComplexEquivalence` on complexes, with quasi-isomorphy recognized
summandwise by `AlgebraicGeometry.quasiIso_of_quasiIso_pullback_sigmaι` and local boundedness
with finite locally free terms by
`AlgebraicGeometry.isLocallyBoundedFiniteLocallyFree_of_pullback_sigmaι`.

## References

* [Stacks Project, Tag 0F9F](https://stacks.math.columbia.edu/tag/0F9F)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
* [Stacks Project, Tag 0F8F](https://stacks.math.columbia.edu/tag/0F8F)
* [Stacks Project, Tag 0F8G](https://stacks.math.columbia.edu/tag/0F8G)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-- **An isomorphism over a coproduct from isomorphisms over the summands.** Let `g i : W i ⟶ X`
be a family of morphisms, `f : ∐ W ⟶ X` the induced morphism, `E` an object of `D(𝒪_X)` and `P` a
complex on `∐ W`. If on each summand `L(g i)^*E` is isomorphic to the class of the degreewise
restriction of `P`, then `Lf^*E` is isomorphic to the class of `P`.

Writing `Lf^*E` as the class of a complex `K`, the restriction of that class to the summand `i`
is the class of `K|ᵢ` (`AlgebraicGeometry.derivedPullbackSigmaιFactors`) and the restriction of
`Lf^*E` there is `L(g i)^*E`
(`Stacks.Chow.derivedPullbackSigmaDescIso`), so the hypothesis is a family of isomorphisms
`Q(K|ᵢ) ≅ Q(P|ᵢ)`, which
`AlgebraicGeometry.nonempty_iso_Q_of_forall_iso_Q_sigmaι` glues. -/
theorem nonempty_iso_Q_derivedPullback_sigmaDesc
    {I : Type u} {W : I → Scheme.{u}} {X : Scheme.{u}} (g : ∀ i, W i ⟶ X)
    (E : DerivedCategory X.Modules) (P : CochainComplex (∐ W : Scheme.{u}).Modules ℤ)
    (h : ∀ i, (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (g i).toLRSHom.toShHom).obj E ≅
      DerivedCategory.Q.obj ((AlgebraicGeometry.sigmaComplexFunctor W).obj P i)) :
    Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (Sigma.desc g).toLRSHom.toShHom).obj E ≅ DerivedCategory.Q.obj P) := by
  obtain ⟨K, ⟨eK⟩⟩ : ∃ K : CochainComplex (∐ W : Scheme.{u}).Modules ℤ,
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Sigma.desc g).toLRSHom.toShHom).obj E ≅ DerivedCategory.Q.obj K) :=
    ⟨_, ⟨(DerivedCategory.Q.objObjPreimageIso _).symm⟩⟩
  obtain ⟨c⟩ := AlgebraicGeometry.nonempty_iso_Q_of_forall_iso_Q_sigmaι W K P fun i =>
    ((AlgebraicGeometry.derivedPullbackSigmaιFactors W i).app K).symm ≪≫
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Sigma.ι W i).toLRSHom.toShHom).mapIso eK.symm ≪≫
      derivedPullbackSigmaDescIso g E i ≪≫ h i
  exact ⟨eK ≪≫ c⟩


/-- The roof identity read after the two identifications: if `ab` factors as `pb` followed by
`bi` conjugated by `ei` and `fj`, and `fj ≫ fi` is the identity, then `ab ≫ fi` factors as
`pb ≫ ei` followed by `bi`. -/
private theorem comp_roof_aux {C : Type*} [Category C] {g0 g1 e1 f1 pe pf : C}
    (w : g0 ⟶ g1) (pb : g1 ⟶ e1) (ab : g1 ⟶ f1) (ei : e1 ⟶ pe) (fi : f1 ⟶ pf) (fj : pf ⟶ f1)
    (bi : pe ⟶ pf) (hf : fj ≫ fi = 𝟙 pf) (hab : ab = pb ≫ (ei ≫ bi ≫ fj)) :
    w ≫ ab ≫ fi = (w ≫ pb ≫ ei) ≫ bi := by
  rw [hab]
  simp only [Category.assoc]
  rw [hf, Category.comp_id]

/-- **[Stacks, Tag 0F8F] over a coproduct of schemes with the resolution property.** Let
`g i : W i ⟶ X` be a family of morphisms with each `W i` quasi-compact, quasi-separated,
semi-separated and carrying the resolution property, let `f : ∐ W ⟶ X` be the induced morphism
and let `E` be a perfect object of `D(𝒪_X)`. Then there are bounded complexes `𝓔ᵢ^•` of finite
locally free `𝒪_{W i}`-modules and a complex `P` on `∐ W` whose degreewise restriction to each
summand is isomorphic to `𝓔ᵢ^•`, with `Lf^*E` isomorphic to the class of `P`.

On each summand `L(g i)^*E` is perfect by [Stacks, Tag 09UA], hence isomorphic to such a
bounded complex by [Stacks, Tag 0F8F]; those assemble into `P`, restriction to the summands
being an equivalence on complexes, and the isomorphism over `∐ W` is
`Stacks.Chow.nonempty_iso_Q_derivedPullback_sigmaDesc`.

Unlike `Stacks.Chow.exists_isLocallyBoundedFiniteLocallyFree_iso_derivedPullback_sigma`, which
reports only local boundedness of `P`, this keeps the summands' complexes: that is what
[Stacks, Tag 0F8G] asks for on each summand. -/
theorem exists_boundedFiniteLocallyFree_sigma_of_isPerfect
    {I : Type u} {W : I → Scheme.{u}} {X : Scheme.{u}} (g : ∀ i, W i ⟶ X)
    [∀ i, CompactSpace (W i)] [∀ i, QuasiSeparatedSpace (W i)]
    [∀ i, HasResolutionProperty (W i)]
    [∀ i, IsAffineHom (pullback.diagonal (terminal.from (W i)))]
    (E : DerivedCategory X.Modules) (hE : IsPerfect (X := X.toRingedSpace) E) :
    ∃ (Eb : ∀ i, CochainComplex (W i).Modules ℤ)
      (P : CochainComplex (∐ W : Scheme.{u}).Modules ℤ),
      (∀ i, boundedFiniteLocallyFreeComplex (W i) (Eb i)) ∧
        Nonempty ((AlgebraicGeometry.sigmaComplexFunctor W).obj P ≅ Eb) ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (Sigma.desc g).toLRSHom.toShHom).obj E ≅ DerivedCategory.Q.obj P) := by
  classical
  choose Eb hEb iEb using fun i =>
    exists_boundedFiniteLocallyFree_iso_of_affineDiagonal (W i) _
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
        (g i).toLRSHom.toShHom E hE)
  obtain ⟨P, ⟨v⟩⟩ : ∃ P : CochainComplex (∐ W : Scheme.{u}).Modules ℤ,
      Nonempty ((AlgebraicGeometry.sigmaComplexFunctor W).obj P ≅ Eb) :=
    ⟨_, ⟨(AlgebraicGeometry.sigmaComplexFunctor W).objObjPreimageIso Eb⟩⟩
  exact ⟨Eb, P, hEb, ⟨v⟩, nonempty_iso_Q_derivedPullback_sigmaDesc g E P fun i =>
    (iEb i).some.symm ≪≫ DerivedCategory.Q.mapIso (CategoryTheory.Pi.isoApp v i).symm⟩

/-- The summandwise half of `Stacks.Chow.exists_isLocallyBoundedFiniteLocallyFree_roof_sigma`:
given maps `p` and `a` over `∐ W` whose degreewise restrictions are the two legs of the
summands' roofs conjugated by the gluing isomorphisms, and the summands' roof identities, the
class of `a` is the class of `p` followed by `β`.

`AlgebraicGeometry.Q_map_eq_comp_of_forall_sigmaι` is what turns the summandwise identities into
the identity over `∐ W`. -/
private theorem Q_map_eq_comp_of_roof_sigma {I : Type u} (W : I → Scheme.{u})
    {Pe Pf Pg : CochainComplex (∐ W : Scheme.{u}).Modules ℤ}
    {Eb Fb Gb : ∀ i, CochainComplex (W i).Modules ℤ}
    (ve : ∀ i, ((Scheme.Modules.pullback (Sigma.ι W i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Pe ≅ Eb i)
    (vf : ∀ i, ((Scheme.Modules.pullback (Sigma.ι W i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Pf ≅ Fb i)
    (vg : ∀ i, ((Scheme.Modules.pullback (Sigma.ι W i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Pg ≅ Gb i)
    {pb : ∀ i, Gb i ⟶ Eb i} {ab : ∀ i, Gb i ⟶ Fb i} (p : Pg ⟶ Pe) (a : Pg ⟶ Pf)
    (hp : ∀ i, ((Scheme.Modules.pullback (Sigma.ι W i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map p = (vg i).hom ≫ pb i ≫ (ve i).inv)
    (ha : ∀ i, ((Scheme.Modules.pullback (Sigma.ι W i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map a = (vg i).hom ≫ ab i ≫ (vf i).inv)
    (β : DerivedCategory.Q.obj Pe ⟶ DerivedCategory.Q.obj Pf)
    (bi : ∀ i, DerivedCategory.Q.obj ((AlgebraicGeometry.sigmaComplexFunctor W).obj Pe i) ⟶
      DerivedCategory.Q.obj ((AlgebraicGeometry.sigmaComplexFunctor W).obj Pf i))
    (hbi : ∀ i, (AlgebraicGeometry.derivedPullbackSigmaιFactors W i).hom.app Pe ≫ bi i =
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Sigma.ι W i).toLRSHom.toShHom).map β ≫
        (AlgebraicGeometry.derivedPullbackSigmaιFactors W i).hom.app Pf)
    (hab : ∀ i, DerivedCategory.Q.map (ab i) = DerivedCategory.Q.map (pb i) ≫
      (DerivedCategory.Q.map (ve i).inv ≫ bi i ≫ DerivedCategory.Q.map (vf i).hom)) :
    DerivedCategory.Q.map a = DerivedCategory.Q.map p ≫ β := by
  refine AlgebraicGeometry.Q_map_eq_comp_of_forall_sigmaι W p a β bi hbi fun i => ?_
  rw [ha i, hp i, Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  exact comp_roof_aux _ _ _ _ _ _ _ (Iso.hom_inv_id_map _ _) (hab i)

/-- **[Stacks, Tag 0F8G] over a coproduct of schemes with the resolution property.** Let
`W i` be quasi-compact, quasi-separated, semi-separated schemes with the resolution property,
let `Pe` and `Pf` be complexes on `∐ W` whose degreewise restrictions to the summands are
isomorphic to bounded complexes `𝓔ᵢ^•`, `𝓕ᵢ^•` of finite locally free modules, and let
`β : Q(Pe) ⟶ Q(Pf)` be a morphism of `D(𝒪_{∐ W})`. Then `β` is represented by a roof: a locally
bounded complex `Pg` of finite locally free `𝒪_{∐ W}`-modules, a quasi-isomorphism
`p : Pg ⟶ Pe` and a map `a : Pg ⟶ Pf` with `Q(a) = Q(p) ≫ β`.

On each summand `β` reads as a morphism `Q(𝓔ᵢ^•) ⟶ Q(𝓕ᵢ^•)`
(`AlgebraicGeometry.exists_restrict_sigmaι`), which [Stacks, Tag 0F8G] represents by a roof
`𝓔ᵢ^• ⟵ 𝓖ᵢ^• ⟶ 𝓕ᵢ^•` with `𝓖ᵢ^•` again a bounded complex of finite locally free modules. The
`𝓖ᵢ^•` assemble into `Pg` and the two legs into `p` and `a`, restriction to the summands being
an equivalence on complexes; `p` is a quasi-isomorphism because it is one summand by summand
(`AlgebraicGeometry.quasiIso_of_quasiIso_pullback_sigmaι`), and the roof identity over `∐ W`
holds because it holds on every summand and the derived pullbacks to the summands are jointly
faithful (`AlgebraicGeometry.eq_of_forall_derivedPullback_sigmaι_map_eq`). -/
theorem exists_isLocallyBoundedFiniteLocallyFree_roof_sigma {I : Type u} (W : I → Scheme.{u})
    [∀ i, CompactSpace (W i)] [∀ i, QuasiSeparatedSpace (W i)]
    [∀ i, HasResolutionProperty (W i)]
    [∀ i, IsAffineHom (pullback.diagonal (terminal.from (W i)))]
    {Pe Pf : CochainComplex (∐ W : Scheme.{u}).Modules ℤ}
    {Eb Fb : ∀ i, CochainComplex (W i).Modules ℤ}
    (hEb : ∀ i, boundedFiniteLocallyFreeComplex (W i) (Eb i))
    (hFb : ∀ i, boundedFiniteLocallyFreeComplex (W i) (Fb i))
    (ve : ∀ i, ((Scheme.Modules.pullback (Sigma.ι W i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Pe ≅ Eb i)
    (vf : ∀ i, ((Scheme.Modules.pullback (Sigma.ι W i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Pf ≅ Fb i)
    (β : DerivedCategory.Q.obj Pe ⟶ DerivedCategory.Q.obj Pf) :
    ∃ (Pg : CochainComplex (∐ W : Scheme.{u}).Modules ℤ) (p : Pg ⟶ Pe) (a : Pg ⟶ Pf),
      IsLocallyBoundedFiniteLocallyFree Pg ∧ QuasiIso p ∧
        DerivedCategory.Q.map a = DerivedCategory.Q.map p ≫ β := by
  classical
  obtain ⟨bi, hbi⟩ := AlgebraicGeometry.exists_restrict_sigmaι W β
  choose Gb pb hpb ab hGb hroof using fun i =>
    exists_boundedFiniteLocallyFree_roof_of_affineDiagonal (W i) (Eb i) (Fb i) (hEb i) (hFb i)
      (DerivedCategory.Q.map (ve i).inv ≫ bi i ≫ DerivedCategory.Q.map (vf i).hom)
  obtain ⟨Pg, ⟨vgp⟩⟩ : ∃ P : CochainComplex (∐ W : Scheme.{u}).Modules ℤ,
      Nonempty ((AlgebraicGeometry.sigmaComplexFunctor W).obj P ≅ Gb) :=
    ⟨_, ⟨(AlgebraicGeometry.sigmaComplexFunctor W).objObjPreimageIso Gb⟩⟩
  have vg : ∀ i, ((Scheme.Modules.pullback (Sigma.ι W i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Pg ≅ Gb i := fun i => CategoryTheory.Pi.isoApp vgp i
  obtain ⟨p, hp⟩ : ∃ p : Pg ⟶ Pe, ∀ i,
      ((Scheme.Modules.pullback (Sigma.ι W i)).mapHomologicalComplex (ComplexShape.up ℤ)).map p =
        (vg i).hom ≫ pb i ≫ (ve i).inv :=
    ⟨(AlgebraicGeometry.sigmaComplexFunctor W).preimage
        (fun i => (vg i).hom ≫ pb i ≫ (ve i).inv),
      fun i => congrFun ((AlgebraicGeometry.sigmaComplexFunctor W).map_preimage _) i⟩
  obtain ⟨a, ha⟩ : ∃ a : Pg ⟶ Pf, ∀ i,
      ((Scheme.Modules.pullback (Sigma.ι W i)).mapHomologicalComplex (ComplexShape.up ℤ)).map a =
        (vg i).hom ≫ ab i ≫ (vf i).inv :=
    ⟨(AlgebraicGeometry.sigmaComplexFunctor W).preimage
        (fun i => (vg i).hom ≫ ab i ≫ (vf i).inv),
      fun i => congrFun ((AlgebraicGeometry.sigmaComplexFunctor W).map_preimage _) i⟩
  have hpq : QuasiIso p := by
    refine AlgebraicGeometry.quasiIso_of_quasiIso_pullback_sigmaι W p fun i => ?_
    rw [hp i]
    have := hpb i
    exact inferInstanceAs (QuasiIso ((vg i).hom ≫ pb i ≫ (ve i).inv))
  have hPg : IsLocallyBoundedFiniteLocallyFree Pg := by
    refine AlgebraicGeometry.isLocallyBoundedFiniteLocallyFree_of_pullback_sigmaι W Pg fun i => ?_
    exact IsLocallyBoundedFiniteLocallyFree.of_iso (vg i).symm
      (isLocallyBoundedFiniteLocallyFree_of_boundedFiniteLocallyFreeComplex (hGb i))
  refine ⟨Pg, p, a, hPg, hpq,
    Q_map_eq_comp_of_roof_sigma W ve vf vg p a hp ha β bi hbi fun i => ?_⟩
  have : IsIso (DerivedCategory.Q.map (pb i)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ (pb i)).2 (hpb i)
  rw [← hroof i, IsIso.hom_inv_id_assoc]

/-- **A morphism of `D(𝒪_{∐ W})` between objects presented by complexes with bounded finite
locally free restrictions is represented by a map of locally bounded complexes of finite
locally free modules.** Let `W i` be quasi-compact, quasi-separated, semi-separated schemes with
the resolution property, let `m : D₁ ⟶ D₂` be a morphism of `D(𝒪_{∐ W})`, and let `D₁`, `D₂` be
isomorphic to the classes of complexes `Pe`, `Pf` whose degreewise restrictions to the summands
are isomorphic to bounded complexes of finite locally free modules. Then there are locally
bounded complexes `P₁`, `P₂` of finite locally free `𝒪_{∐ W}`-modules, a map `α : P₁ ⟶ P₂` and
isomorphisms `f₁ : D₁ ≅ Q(P₁)`, `f₂ : D₂ ≅ Q(P₂)` with

  `f₁ ≫ Q(α) = m ≫ f₂`.

Transport `m` to a morphism `β : Q(Pe) ⟶ Q(Pf)` and represent it by a roof
`Pe ⟵ Pg ⟶ Pf` (`Stacks.Chow.exists_isLocallyBoundedFiniteLocallyFree_roof_sigma`); `Pg` with
the roof's left leg inverted presents `D₁`, and the right leg is the map of complexes
wanted. -/
theorem exists_isLocallyBoundedFiniteLocallyFree_square_sigma {I : Type u} (W : I → Scheme.{u})
    [∀ i, CompactSpace (W i)] [∀ i, QuasiSeparatedSpace (W i)]
    [∀ i, HasResolutionProperty (W i)]
    [∀ i, IsAffineHom (pullback.diagonal (terminal.from (W i)))]
    {D₁ D₂ : DerivedCategory (∐ W : Scheme.{u}).Modules} (m : D₁ ⟶ D₂)
    {Pe Pf : CochainComplex (∐ W : Scheme.{u}).Modules ℤ}
    {Eb Fb : ∀ i, CochainComplex (W i).Modules ℤ}
    (hEb : ∀ i, boundedFiniteLocallyFreeComplex (W i) (Eb i))
    (hFb : ∀ i, boundedFiniteLocallyFreeComplex (W i) (Fb i))
    (ve : ∀ i, ((Scheme.Modules.pullback (Sigma.ι W i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Pe ≅ Eb i)
    (vf : ∀ i, ((Scheme.Modules.pullback (Sigma.ι W i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Pf ≅ Fb i)
    (e₁ : D₁ ≅ DerivedCategory.Q.obj Pe) (e₂ : D₂ ≅ DerivedCategory.Q.obj Pf) :
    ∃ (P₁ P₂ : CochainComplex (∐ W : Scheme.{u}).Modules ℤ) (α : P₁ ⟶ P₂),
      IsLocallyBoundedFiniteLocallyFree P₁ ∧ IsLocallyBoundedFiniteLocallyFree P₂ ∧
      ∃ (f₁ : D₁ ≅ DerivedCategory.Q.obj P₁) (f₂ : D₂ ≅ DerivedCategory.Q.obj P₂),
        f₁.hom ≫ DerivedCategory.Q.map α = m ≫ f₂.hom := by
  classical
  have hPf : IsLocallyBoundedFiniteLocallyFree Pf := by
    refine AlgebraicGeometry.isLocallyBoundedFiniteLocallyFree_of_pullback_sigmaι W Pf fun i => ?_
    exact IsLocallyBoundedFiniteLocallyFree.of_iso (vf i).symm
      (isLocallyBoundedFiniteLocallyFree_of_boundedFiniteLocallyFreeComplex (hFb i))
  obtain ⟨Pg, p, a, hPg, hpq, key⟩ :=
    exists_isLocallyBoundedFiniteLocallyFree_roof_sigma W hEb hFb ve vf
      (e₁.inv ≫ m ≫ e₂.hom)
  have : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hpq
  refine ⟨Pg, Pf, a, hPg, hPf, e₁ ≪≫ (asIso (DerivedCategory.Q.map p)).symm, e₂, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, key, IsIso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc]

/-- **[Stacks, Tag 0F9F] under condition (3) of the source.** Let `T` be a distinguished triangle
of `D(𝒪_X)` whose first two objects are perfect and let the irreducible components of `X`, which
is locally of finite type over the base of the Chow situation, be quasi-compact. Then the Chern
classes of `E₁`, `E₂`, `E₃` are defined and

  `c(E₂) = c(E₁) c(E₃)`,  `ch_p(E₂) = ch_p(E₁) + ch_p(E₃)`,  `P_p(E₂) = P_p(E₁) + P_p(E₃)`.

`X` is locally Noetherian, the base being locally Noetherian and `X` locally of finite type over
it, so `Stacks.Chow.exists_isEnvelope_sigma_of_isCompact_irreducibleComponents` supplies an
envelope `∐ W ⟶ X` whose summands are Noetherian — hence quasi-compact and quasi-separated —
with the resolution property and affine diagonal. On such a source
`Stacks.Chow.exists_boundedFiniteLocallyFree_sigma_of_isPerfect` presents `Lf^*E₁` and `Lf^*E₂`
by complexes whose summandwise restrictions are bounded complexes of finite locally free
modules, and `Stacks.Chow.exists_isLocallyBoundedFiniteLocallyFree_square_sigma` represents
`Lf^*E₁ ⟶ Lf^*E₂` by a map of locally bounded complexes of finite locally free modules together
with the commuting square. That is condition (1) of the source, in the shape
`Stacks.Chow.hasDefinedChernClasses_and_additive_of_envelope` asks for.

Every hypothesis is a hypothesis of the source: the Chow situation, `X` locally of finite type
over its base, the distinguished triangle, perfectness of `E₁` and `E₂`, and quasi-compactness
of the irreducible components of `X`. Local Noetherianity, the envelope, the summands'
resolution property and affine diagonal, the two complexes and the map between them are all
derived. Perfectness of `E₃` is a standing hypothesis of the source that no step of this proof
uses, so it is omitted. -/
@[stacks 0F9F "condition (3): the irreducible components of X are quasi-compact.  The \
conclusion is the whole one: the Chern classes of E_1, E_2 and E_3 are defined, c(E_2) = \
c(E_1)c(E_3), ch(E_2) = ch(E_1) + ch(E_3) and P_p(E_2) = P_p(E_1) + P_p(E_3), the last two read \
componentwise in A^p(X) tensor Q and in A^p(X) as the source reads them.  The hypotheses are \
exactly the source's: the base situation of Tag 02QL, X locally of finite type over its base, \
the distinguished triangle, perfectness of E_1 and E_2, and the irreducible components of X \
quasi-compact.  Perfectness of E_3 is a standing hypothesis of the source that no step of this \
proof uses, so it is omitted, exactly as for conditions (1), (2) and (4)"]
theorem triangleChernAdditive_of_isCompact_irreducibleComponents
    (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (T : Triangle (DerivedCategory X.Modules)) (hT : T ∈ distTriang (DerivedCategory X.Modules))
    (h₁ : IsPerfect (X := X.toRingedSpace) T.obj₁)
    (h₂ : IsPerfect (X := X.toRingedSpace) T.obj₂)
    (hqc : ∀ Z ∈ irreducibleComponents X, IsCompact Z) :
    TriangleChernAdditive C sX T := by
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
  obtain ⟨Eb, Pe, hEb, ⟨vep⟩, ⟨e₁⟩⟩ :=
    exists_boundedFiniteLocallyFree_sigma_of_isPerfect g T.obj₁ h₁
  obtain ⟨Fb, Pf, hFb, ⟨vfp⟩, ⟨e₂⟩⟩ :=
    exists_boundedFiniteLocallyFree_sigma_of_isPerfect g T.obj₂ h₂
  obtain ⟨P₁, P₂, α, hP₁, hP₂, f₁, f₂, hα⟩ :=
    exists_isLocallyBoundedFiniteLocallyFree_square_sigma W
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Sigma.desc g).toLRSHom.toShHom).map T.mor₁) hEb hFb
      (fun i => CategoryTheory.Pi.isoApp vep i) (fun i => CategoryTheory.Pi.isoApp vfp i) e₁ e₂
  exact hasDefinedChernClasses_and_additive_of_envelope C sX T hT (Sigma.desc g) henv α
    hP₁ hP₂ f₁ f₂ hα

end Stacks.Chow

end
