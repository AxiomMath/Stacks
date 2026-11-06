module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Perfect.Approximation.OpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Approximation
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
import StacksCore.Tactic.StacksAttribute

/-!
# Approximation on an algebraic space representable by an affine scheme

Let `S` be a scheme and let `X` be an algebraic space over `S` which is representable by an
affine scheme `X₀`.  Stacks 08HM says that approximation holds for every triple `(T, E, m)` as
in Stacks 08HI for which there is an integer `r ≥ 0` with

1. `E` is `m`-pseudo-coherent,
2. `Hⁱ(E)` is supported on `T` for `i ≥ m - r + 1`,
3. `X ∖ T` is the union of `r` affine opens,

and that in particular approximation by perfect complexes holds in that situation.

The source's proof is five sentences and is **not** an induction on `r`; the induction lives
inside the affine-scheme statement it cites.  Writing `ε : X_étale ⟶ X₀,Zar` for the morphism of
Stacks 08H7, it says: `E = ε^*E₀` for an `E₀` of `D_QCoh(𝒪_{X₀})` by Stacks 071Q; `E₀` is
`m`-pseudo-coherent by Stacks 08HE; comparing stalks of cohomology sheaves — the computation in
the proof of Stacks 08H8 — the sheaves `Hⁱ(E₀)` are supported on the closed subset `T₀ ⊆ X₀`
corresponding to `T` for `i ≥ m - r + 1`; Derived Categories of Schemes, Stacks 08EQ gives an
approximation `P₀ ⟶ E₀` of `(T₀, E₀, m)`; `ε^*P₀` is perfect by Stacks 08HG; and pulling back
gives the approximation `ε^*P₀ ⟶ ε^*E₀ = E`.

That assembly is what is carried out here, from Stacks 08EQ and from named
hypotheses standing for the inputs this library does not have — see "What is carried" below,
which says what each one is and why it is missing.

## Main results

* `AlgebraicGeometry.Space.approximationHolds_of_affineCover`: **Stacks 08HM**, the statement
  for one triple, granted the inputs below.
* `AlgebraicGeometry.Space.approximationByPerfectComplexes_of_affine`: **the "in particular"
  of Stacks 08HM**, approximation by perfect complexes, deduced from the first statement.

## What is carried, and why

Everything below is a hypothesis of the two statements.  None of it is the conclusion of
Stacks 08HM, and none of it mentions approximation, a perfect object, or a triple.

*The bridge `ε` itself.*  Stacks 08HI is stated on `AlgebraicGeometry.Space.smallEtaleRingedSite`
of an algebraic space, which is built over a `AlgebraicGeometry.BigFppfSite`, whereas the
scheme-level statements of this chapter — Stacks 071Q
(`AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence`), Stacks 08HE clause
(1) ⇒ (2) (`AlgebraicGeometry.SmallEtale.pseudoCoherentToAssociatedModule_of_slice_exact`) and
Stacks 08HG (`AlgebraicGeometry.SmallEtale.perfectToAssociatedModule_of_slice_exact`) — are
stated on `AlgebraicGeometry.smallEtaleRingedSite` of a *scheme*, built over a
`AlgebraicGeometry.BigEtaleSite`.  The identification of the two for a representable space is
factored in this library as an equivalence of the underlying sites
(`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`, with the structure sheaves agreeing
by `AlgebraicGeometry.Space.reindexRing_representedSmallEtaleEquivalence`, which is `rfl`)
together with the module-level comparison
`AlgebraicGeometry.Space.representedSpaceModulesEquivalence`; what does *not* exist is a
transport of `AlgebraicGeometry.RingedSite.IsPerfect`, of
`AlgebraicGeometry.RingedSite.IsPseudoCoherentFrom` or of
`AlgebraicGeometry.Space.supportOfSheaf` along that equivalence, nor an identification of
`AlgebraicGeometry.Space.points` of the space with `PrimeSpectrum` of the ring.  So `ε^*` enters
as the functor `eps` of `𝒪`-modules together with its exactness, which is the exactness
assertion of Stacks 08H8; this is the same way extension by zero enters Stacks 08HL,
`AlgebraicGeometry.Space.approximationHolds_of_elementaryDistinguishedSquare`.  Pinning `ε^*` on
the derived category to `CategoryTheory.Functor.mapDerivedCategory` of an exact functor of
modules is not a restriction — it is the source's own reading of `ε^*`, `ε` being flat, and it is
what makes the `t`-exactness used below available rather than assumed.

*The stalk comparison, as one fact about modules.*  `hstalk` is the computation the source cites
as "comparing stalks of cohomology sheaves, see the proof of Lemma 75.4.1": for an
`𝒪_{X₀}`-module `G₀`, a point `p` of `|X|` lies outside the support of `ε^*G₀` exactly when the
Zariski stalk of `G₀` at the corresponding point `ρ p` of `X₀` vanishes.  It is stated for
*modules* only.  Both directions of the *derived* support transport are then **proved** here, in
both directions, from it: `Hⁱ(ε^*K) ≅ ε^*(Hⁱ K)` by
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`, and
`AlgebraicGeometry.Space.supportOfSheaf_subset_of_mono` (Stacks 04KB) moves the containment
across the resulting isomorphism of abelian sheaves.  The map `ρ` on points, with its
surjectivity, is the other half of what representability by `Spec R` provides.

*Stacks 071Q, as data.*  `E₀` together with `hE₀ : ε^*E₀ ≅ E` and the quasi-coherence of its
cohomology is essential surjectivity of the equivalence of Stacks 071Q.  The library's 071Q is
itself conditional on four inputs, and is in any case stated on the scheme's site, so it cannot
be read at `ε` here; it enters as the datum it would produce.  This is the device by which
Stacks 08HL carries the quasi-coherence of a restriction.

*Stacks 08HE clause (2) ⇒ (1).*  `hpcDescend` is pseudo-coherence *descending* along `ε^*`.  The
proved direction of Stacks 08HE is (1) ⇒ (2); clause (2) ⇒ (1) is the unproved
`AlgebraicGeometry.SmallEtale.AssociatedModuleToPseudoCoherent`, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtalePseudoCoherentForward.lean`
record.  It is stated as an implication *from* hypothesis (1) of the source, so hypothesis (1) is
really consumed.

*Stacks 08HG.*  `hperfAscend` is perfectness *ascending* along `ε^*`, which is the direction of
Stacks 08HG that is proved at the scheme level; only its transport across the site comparison is
missing.  It is universally quantified over the object it is applied to, because the
approximating `P₀` is produced by an existential inside the proof and is not available when the
statement is written — again as in Stacks 08HL.

*Hypothesis (3), in the form Stacks 08EQ consumes.*  The source states its third hypothesis as
"`X ∖ T` is the union of `r` affine opens" and its proof of the affine case then writes, without
argument, "write `T = V(f₁, …, f_r)`" with the *same* `r`.  Stacks 08EQ,
`AlgebraicGeometry.PerfectApproximation.approximationHolds_of_zeroLocus`, is stated for a closed
subset presented as the zero locus of `r` ring elements for exactly this reason.  That is not a
restriction waiting on a missing lemma: as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Perfect/PerfectApproximation/Affine.lean` record, a closed
subset of an affine scheme whose complement is a union of `r` affine opens need *not* be the
zero locus of `r` elements, and the source's proof in fact only matches the support hypothesis
against the number of affine opens covering `X ∖ T`.  Hypothesis (3) is taken here in the
zero-locus form, `T = ρ⁻¹ V(f₁, …, f_r)` for `f : Fin r → R`; the number matters, the Koszul
complex on `r` elements occupying the degrees `-r, …, 0`.

*The affine scheme is `Spec R`.*  `AlgebraicGeometry.Space.IsAffineSpace` gives a representing
object with *affine* underlying scheme, and the second assertion of Stacks 08EQ is proved
for `Spec R`.  The transport along `X₀ ≅ Spec Γ(X₀, 𝒪)` is
`AlgebraicGeometry.PerfectApproximation.approximationByPerfectComplexes_of_iso` of
`StacksFrontier/AlgebraicGeometry/Perfect/PerfectApproximation/AffineScheme.lean`, which is not used
here.  The
ring `R` is therefore a parameter here and `IsAffineSpace` is *not* a binder: it is not consumed
anywhere, the data `R`, `eps`, `ρ` and `hstalk` standing for precisely what it provides.

## What is proved here

Stacks 08EQ is genuinely applied, and around it:

* both directions of the derived support transport along `ε^*`, from the module-level `hstalk`,
  through the `t`-exactness of `ε^*` (`AlgebraicGeometry.Space.supportOfSheaf_eq_of_mapIso`
  below);
* the transport of the approximation itself: `ε^*` carries a map which is an isomorphism on `Hⁱ`
  above `m` and a surjection on `Hᵐ` to one that is, by
  `CategoryTheory.Functor.isIso_homologyFunctor_map_mapDerivedCategory_map` and
  `CategoryTheory.Functor.epi_homologyFunctor_map_mapDerivedCategory_map`, and the resulting map
  is composed with `hE₀` to land on `E` — this is the source's last sentence;
* monotonicity of `AlgebraicGeometry.RingedSite.IsPseudoCoherentFrom` in its degree, which the
  library records for modules and for ringed spaces but not for a ringed site, and which is what
  takes the `(m - r)`-pseudo-coherence that Stacks 08HJ supplies to the `m`-pseudo-coherence that
  hypothesis (1) asks for, in the second statement;
* the narrowing of the range of degrees from `i ≥ m - r` to `i ≥ m - r + 1` and the choice of the
  integer of Stacks 08HJ, also in the second statement.

## Implementation notes

`T` is an arbitrary subset of `|X|` rather than a closed one, which is the convention of
`AlgebraicGeometry.Space.ApproximationHolds` and of
`AlgebraicGeometry.Space.CohomologySupportedOn`; the source's closedness of `T` is part of its
notion of a triple and is used nowhere in its proof, so dropping it only strengthens the
statement.  In the second statement, where the quantifier is over closed subsets, `T` is closed.

The module sections are at the universe of the schemes, as in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ApproximationElementarySquare.lean`: at that
universe every sheafification and local-bijectivity hypothesis that
`AlgebraicGeometry.RingedSite.IsPerfect`, `AlgebraicGeometry.RingedSite.IsPseudoCoherentFrom`
and `AlgebraicGeometry.Space.ApproximationHolds` ask of the small étale site and of its slices
is an instance, by `AlgebraicGeometry.Space.RingedSite`, so none appears as a binder.  The
derived category of `(Spec R).Modules` is at `u + 1`, which is where Stacks 08EQ
lives; `CategoryTheory.Functor.mapDerivedCategory` and the two transport lemmas it is used with
leave the two derived-category universes independent, so no comparison of models is needed.

The standard model is selected at raised priority, as in
`StacksFrontier/AlgebraicGeometry/Perfect/PerfectApproximation/Affine.lean`: a plain
`attribute [local instance]` is not enough in a file with `AlgebraicGeometry.derivedTilde` in
its import closure.

## References

* [Stacks Project, Tag 08HM](https://stacks.math.columbia.edu/tag/08HM)
* [Stacks Project, Tag 08HI](https://stacks.math.columbia.edu/tag/08HI)
* [Stacks Project, Tag 08HJ](https://stacks.math.columbia.edu/tag/08HJ)
* [Stacks Project, Tag 08EQ](https://stacks.math.columbia.edu/tag/08EQ)
* [Stacks Project, Tag 08EM](https://stacks.math.columbia.edu/tag/08EM)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 08HG](https://stacks.math.columbia.edu/tag/08HG)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 04KB](https://stacks.math.columbia.edu/tag/04KB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space


attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-! ### Instances pinned by hand -/

/-- The abelian structure of the `𝒪_X`-modules with sections in the universe of the schemes,
written out instead of being found by instance search.

It is the term instance search returns, namely `SheafOfModules.instAbelian` fed the two
sheafification instances of `StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian`, so nothing is
changed by using it.  The search itself is unusable in a file importing
`StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine`, which Stacks
08EQ brings in: it declares sheafification instances for every universe of module sections
containing the objects of the site, whose universe parameter occurs only inside a `max`, so
matching them against a goal at the universe of the schemes leaves an unsolvable universe
constraint postponed rather than failing, and the postponed constraint is reported as an error.
This is the device of `AlgebraicGeometry.Space.smallEtaleModulesAbelian` in
`StacksFrontier/AlgebraicGeometry/Spaces/WeaklyAssociatedInjective.lean`, for the same reason. -/
@[instance_reducible] noncomputable def modulesAbelianAtSchemeUniverse :
    Abelian (Modules.{u, u} B S hS X hX) :=
  @SheafOfModules.instAbelian _ _ _ _ (smallEtaleRingedSite_hasSheafify B S hS X hX)
    (smallEtaleRingedSite_wEqualsLocallyBijective B S hS X hX)

attribute [local instance 10000] modulesAbelianAtSchemeUniverse in
/-- The standard model of `D(𝒪_X)` at the universe of the schemes, written out instead of being
found by instance search, for the reason recorded on
`AlgebraicGeometry.Space.modulesAbelianAtSchemeUniverse`.  Here the offending candidates are the
locally small models of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, which
Stacks 08EQ brings in through `AlgebraicGeometry.derivedTilde`: their universe of
morphisms is a `max` over the universe of the objects of the site, which for the small étale
site is `u + 1`, so matching them against the module universe `u` leaves the same unsolvable
constraint postponed.  This is `CategoryTheory.HasDerivedCategory.standard` fed the abelian
structure above, which is the term
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/Approximation.lean` selects, so the objects of
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory` live in this model. -/
@[instance_reducible] noncomputable def modulesHasDerivedCategory :
    HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS X hX) :=
  @HasDerivedCategory.standard (Modules.{u, u} B S hS X hX) _
    (modulesAbelianAtSchemeUniverse B S hS X hX)

/-! ### Support is an invariant of an abelian sheaf on the small étale site -/

attribute [local instance 10000] modulesAbelianAtSchemeUniverse modulesHasDerivedCategory in
include hX in
/-- Isomorphic abelian sheaves on the small étale site of an algebraic space have the same
support: an isomorphism is a monomorphism both ways, so Stacks 04KB applies twice. -/
theorem supportOfSheaf_eq_of_mapIso
    {F G : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{u}} (e : F ≅ G) :
    supportOfSheaf B S hS X F = supportOfSheaf B S hS X G :=
  Set.eq_of_subset_of_subset
    (@supportOfSheaf_subset_of_mono B S hS X hX F G e.hom (IsSplitMono.mono (f := e.hom)))
    (@supportOfSheaf_subset_of_mono B S hS X hX G F e.inv (IsSplitMono.mono (f := e.inv)))

/-! ### Pseudo-coherence from a degree is monotone in that degree -/

attribute [local instance 10000] modulesAbelianAtSchemeUniverse modulesHasDerivedCategory in
/-- **Monotonicity of Stacks 08FT part (1) in its degree.** A complex of `𝒪_X`-modules which is
`a`-pseudo-coherent is `b`-pseudo-coherent for every `b ≥ a`: the local approximations are the
same ones, their isomorphism range `> a` contains `> b`, and in degree `b` either `b = a`, where
the surjection is the given one, or `b > a`, where the given isomorphism is one. -/
theorem isPseudoCoherentComplexFrom_mono
    (K : CochainComplex (Modules.{u, u} B S hS X hX) ℤ) {a b : ℤ}
    (h : (smallEtaleRingedSite B S hS X hX).IsPseudoCoherentComplexFrom K a) (hab : a ≤ b) :
    (smallEtaleRingedSite B S hS X hX).IsPseudoCoherentComplexFrom K b := by
  intro U
  obtain ⟨T, hT, hmem⟩ := h U
  refine ⟨T, hT, fun {V} g hg => ?_⟩
  obtain ⟨P, hP, α, hiso, hepi⟩ := hmem g hg
  refine ⟨P, hP, α, fun j hj => hiso j (lt_of_le_of_lt hab hj), ?_⟩
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact hepi
  · have := hiso b hlt
    infer_instance

attribute [local instance 10000] modulesAbelianAtSchemeUniverse modulesHasDerivedCategory in
/-- **Monotonicity of Stacks 08FT part (3) in its degree**, for an object of `D(𝒪_X)`: the
representing complex of `AlgebraicGeometry.RingedSite.IsPseudoCoherentFrom` is monotone in the
degree by `AlgebraicGeometry.Space.isPseudoCoherentComplexFrom_mono`. -/
theorem isPseudoCoherentFrom_mono {E : DerivedCategory (Modules.{u, u} B S hS X hX)} {a b : ℤ}
    (h : (smallEtaleRingedSite B S hS X hX).IsPseudoCoherentFrom E a) (hab : a ≤ b) :
    (smallEtaleRingedSite B S hS X hX).IsPseudoCoherentFrom E b := by
  obtain ⟨K, hK, he⟩ := h
  exact ⟨K, isPseudoCoherentComplexFrom_mono B S hS X hX K hK hab, he⟩

/-! ### Stacks 08HM -/

attribute [local instance 10000] modulesAbelianAtSchemeUniverse modulesHasDerivedCategory in
/-- **Stacks 08HM.**  Let `S` be a scheme and let `X` be an algebraic space over `S` which is
representable by an affine scheme, say by `Spec R`.  Then approximation holds for a triple
`(T, E, m)` as in Stacks 08HI as soon as, for some `r ≥ 0`, `E` is `m`-pseudo-coherent, the
sheaves `Hⁱ(E)` are supported on `T` for `i ≥ m - r + 1`, and `T` is the preimage under the
comparison of points of a closed subset of `Spec R` cut out by `r` elements — which is the form
of hypothesis (3) that Stacks 08EQ consumes.

The approximation produced is `ε^*P₀ ⟶ ε^*E₀ ≅ E`, for `P₀ ⟶ E₀` the approximation of
`(V(f₁, …, f_r), E₀, m)` supplied by Stacks 08EQ; the "What is carried" section of this file
says what each hypothesis is and which of them the library does not prove. -/
@[stacks 08HM "approximation for a triple. CONDITIONAL. The assembly is the source's own and the
library's Tag 08EQ, approximationHolds_of_zeroLocus, is genuinely applied; see the module docstring
for every carried input and why it is missing"]
theorem approximationHolds_of_affineCover
    (R : CommRingCat.{u}) {r : ℕ} (f : Fin r → R)
    (eps : (Spec R).Modules ⥤ Modules.{u, u} B S hS X hX)
    [eps.Additive] [PreservesFiniteLimits eps] [PreservesFiniteColimits eps]
    (ρ : points B S hS X → PrimeSpectrum R) (hρ : Function.Surjective ρ)
    (hstalk : ∀ (G₀ : (Spec R).Modules) (p : points B S hS X),
      p ∉ supportOfSheaf B S hS X
          ((SheafOfModules.toSheaf
              ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))).obj (eps.obj G₀)) ↔
        IsZero (TopCat.Presheaf.stalk (X := Spec R) G₀.val.presheaf (ρ p)))
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) (m : ℤ)
    (E₀ : DerivedCategory.{u + 1} (Spec R).Modules)
    (hE₀ : eps.mapDerivedCategory.obj E₀ ≅ E.obj)
    (hqc₀ : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj E₀).IsQuasicoherent)
    (hpc : (smallEtaleRingedSite B S hS X hX).IsPseudoCoherentFrom E.obj m)
    (hpcDescend : (smallEtaleRingedSite B S hS X hX).IsPseudoCoherentFrom E.obj m →
      RingedSpace.IsPseudoCoherentFrom (X := (Spec R).toRingedSpace) E₀ m)
    (hperfAscend : ∀ P₀ : DerivedCategory.{u + 1} (Spec R).Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) P₀ →
        (smallEtaleRingedSite B S hS X hX).IsPerfect (eps.mapDerivedCategory.obj P₀))
    (hsupp : ∀ i : ℤ, m - (r : ℤ) + 1 ≤ i →
      supportOfSheaf B S hS X
        ((SheafOfModules.toSheaf
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).obj E.obj)) ⊆
        ρ ⁻¹' PrimeSpectrum.zeroLocus (Set.range f)) :
    ApproximationHolds B S hS X hX (ρ ⁻¹' PrimeSpectrum.zeroLocus (Set.range f)) E m := by
  -- Isomorphic `𝒪_X`-modules have the same support.
  have hsupp_iso : ∀ {M N : Modules.{u, u} B S hS X hX}, (M ≅ N) →
      supportOfSheaf B S hS X
          ((SheafOfModules.toSheaf
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS X hX).O))).obj M) =
        supportOfSheaf B S hS X
          ((SheafOfModules.toSheaf
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS X hX).O))).obj N) :=
    fun e => supportOfSheaf_eq_of_mapIso B S hS X hX
      ((SheafOfModules.toSheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))).mapIso e)
  -- `t`-exactness of `ε^*`: `Hⁱ(ε^*K)` is `ε^*(Hⁱ K)`, so the two have the same support.
  have hcomp := fun (K : DerivedCategory.{u + 1} (Spec R).Modules) (i : ℤ) =>
    hsupp_iso
      (M := (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).obj
        (eps.mapDerivedCategory.obj K))
      (N := eps.obj ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj K))
      ((eps.mapDerivedCategoryHomologyIso i).app K)
  -- `Hⁱ(ε^*E₀)` and `Hⁱ(E)` have the same support, by `hE₀`.
  have hEsupp := fun i : ℤ =>
    hsupp_iso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).mapIso hE₀)
  -- Hypothesis (2), descended to `X₀` through `hstalk`: this is the source's stalk comparison.
  have hsupp₀ : ∀ i : ℤ, m - (r : ℤ) + 1 ≤ i → ∀ x : PrimeSpectrum R,
      x ∉ PrimeSpectrum.zeroLocus (Set.range f) →
      IsZero (TopCat.Presheaf.stalk (X := Spec R)
        (((DerivedCategory.homologyFunctor (Spec R).Modules i).obj E₀).val.presheaf) x) := by
    intro i hi x hx
    obtain ⟨p, rfl⟩ := hρ x
    refine (hstalk ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj E₀) p).1 ?_
    rw [← hcomp E₀ i, hEsupp i]
    exact fun hmem => hx (hsupp i hi hmem)
  -- Stacks 08EQ on `Spec R`, with hypotheses (1) and (2) descended.
  obtain ⟨P₀, hP₀perf, hP₀supp, α₀, hαiso, hαepi⟩ :=
    PerfectApproximation.approximationHolds_of_zeroLocus R f E₀ m hqc₀ (hpcDescend hpc) hsupp₀
  refine ⟨eps.mapDerivedCategory.obj P₀, hperfAscend P₀ hP₀perf, ?_,
    eps.mapDerivedCategory.map α₀ ≫ hE₀.hom, ?_, ?_⟩
  · -- `ε^*P₀` is supported on `T`, again through `hstalk`.
    intro i
    rw [hcomp P₀ i]
    intro p hp
    by_contra hpT
    exact ((hstalk ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj P₀) p).2
      (hP₀supp i (ρ p) hpT)) hp
  · -- Isomorphism on `Hⁱ` for `i > m`.
    intro i hi
    have h₁ := eps.isIso_homologyFunctor_map_mapDerivedCategory_map α₀ i (hαiso i hi)
    have h₂ : IsIso ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X hX) i).map hE₀.hom) := inferInstance
    rw [Functor.map_comp]
    infer_instance
  · -- Surjection on `Hᵐ`.
    have h₁ := eps.epi_homologyFunctor_map_mapDerivedCategory_map α₀ m hαepi
    have h₂ : IsIso ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X hX) m).map hE₀.hom) :=
      (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) m).map_isIso hE₀.hom
    have h₃ : Epi ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X hX) m).map hE₀.hom) := IsIso.epi_of_iso _
    rw [Functor.map_comp]
    exact epi_comp _ _

attribute [local instance 10000] modulesAbelianAtSchemeUniverse modulesHasDerivedCategory in
/-- **The "in particular" of Stacks 08HM**: approximation by perfect complexes, in the sense of
Stacks 08HJ, holds on an algebraic space representable by an affine scheme.

Given, for each closed `T` whose open complement has quasi-compact inclusion, a presentation of
the corresponding closed subset of `Spec R` as the zero locus of `r` elements — which is what a
closed subset with retrocompact complement has, by Stacks 00E8, and the step Stacks
08EQ identifies as the only missing one in its own hypothesis (3) — the integer of Stacks 08HJ
is `r`, and the hypotheses of `AlgebraicGeometry.Space.approximationHolds_of_affineCover` follow
from those of Stacks 08HJ: `m`-pseudo-coherence from `(m - r)`-pseudo-coherence by
`AlgebraicGeometry.Space.isPseudoCoherentFrom_mono`, and support in the degrees `≥ m - r + 1`
from support in the degrees `≥ m - r`. -/
@[stacks 08HM "approximation by perfect complexes for an affine space. CONDITIONAL on the same
ε-bridge, plus the presentation of each closed subset with quasi-compact open complement as the
preimage of a zero locus of r elements; the deduction from the triple statement is proved"]
theorem approximationByPerfectComplexes_of_affine
    (R : CommRingCat.{u})
    (eps : (Spec R).Modules ⥤ Modules.{u, u} B S hS X hX)
    [eps.Additive] [PreservesFiniteLimits eps] [PreservesFiniteColimits eps]
    (ρ : points B S hS X → PrimeSpectrum R) (hρ : Function.Surjective ρ)
    (hstalk : ∀ (G₀ : (Spec R).Modules) (p : points B S hS X),
      p ∉ supportOfSheaf B S hS X
          ((SheafOfModules.toSheaf
              ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))).obj (eps.obj G₀)) ↔
        IsZero (TopCat.Presheaf.stalk (X := Spec R) G₀.val.presheaf (ρ p)))
    (hpres : letI : TopologicalSpace (points B S hS X) := pointTopology B S hS X
      ∀ (T : Set (points B S hS X)) (hT : IsClosed T),
        IsQuasiCompact B S hS
            ((openSubspacesOrderIso B S hS X hX).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι →
          ∃ (r : ℕ) (g : Fin r → R), T = ρ ⁻¹' PrimeSpectrum.zeroLocus (Set.range g))
    (E₀ : QuasicoherentDerivedCategory.{u, u} B S hS X hX →
      DerivedCategory.{u + 1} (Spec R).Modules)
    (hE₀ : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS X hX,
      eps.mapDerivedCategory.obj (E₀ E) ≅ E.obj)
    (hqc₀ : ∀ (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) (i : ℤ),
      ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj (E₀ E)).IsQuasicoherent)
    (hpcDescend : ∀ (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) (m : ℤ),
      (smallEtaleRingedSite B S hS X hX).IsPseudoCoherentFrom E.obj m →
        RingedSpace.IsPseudoCoherentFrom (X := (Spec R).toRingedSpace) (E₀ E) m)
    (hperfAscend : ∀ P₀ : DerivedCategory.{u + 1} (Spec R).Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) P₀ →
        (smallEtaleRingedSite B S hS X hX).IsPerfect (eps.mapDerivedCategory.obj P₀)) :
    ApproximationByPerfectComplexes.{u, u} B S hS X hX := by
  intro T hT hTc
  obtain ⟨r, g, hTg⟩ := hpres T hT hTc
  refine ⟨(r : ℤ), fun E m hpcE hsuppE => ?_⟩
  rw [hTg]
  refine approximationHolds_of_affineCover B S hS X hX R g eps ρ hρ hstalk E m (E₀ E) (hE₀ E)
    (hqc₀ E)
    (isPseudoCoherentFrom_mono B S hS X hX hpcE (by omega : m - (r : ℤ) ≤ m))
    (fun h => hpcDescend E m h) hperfAscend fun i hi => ?_
  rw [← hTg]
  exact hsuppE i (by omega)

end AlgebraicGeometry.Space

end
