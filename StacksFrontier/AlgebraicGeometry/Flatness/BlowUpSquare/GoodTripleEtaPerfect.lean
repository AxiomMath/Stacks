module

public import StacksFrontier.Algebra.Homology.QuasiIsoRoof
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestriction
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPrincipalityTransfer
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTriple
public import StacksFrontier.Homology.Eta.Perfect.LocallyFree
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeFiniteFree
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedApproximation
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalPerfectness
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.NestedRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.AffineFiniteProjective
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.MappingCone

/-!
# Perfectness of the derived décalage of a good triple

Let `(X, D, M)` be a triple as in Situation 0F8S and let `I ⊆ 𝒪_X` be the ideal sheaf of `D`.
Stacks tag 0GTW asserts that if `(X, D, M)` is a good triple then `Lη_I M` is a perfect object
of `D(𝒪_X)`.

The source proves this by translating More on Algebra, tag 0F7W along tag 0GTV: on an affine
chart `(U, A, f, M^•)` whose determinantal ideals `I_i(M^•, f)` are principal, every term of the
algebraic décalage `η_f M^•` is finite projective, so the complex of `𝒪_{Spec A}`-modules it
gives rise to is strictly perfect, and perfectness of `Lη_I M` is a local condition.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.etaComplex`: the algebraic décalage
  `η_f M^•` of the bounded complex of an affine chart, as a cochain complex of
  `Γ(X, U)`-modules.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.specEtaComplex`: the associated
  complex of `𝒪_U`-modules, obtained by applying `tilde` on `Spec Γ(X, U)` and pulling back
  along `U ≅ Spec Γ(X, U)`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage`: the affine-chart comparison
  carried as a hypothesis, a roof of quasi-isomorphisms; see "What is carried" below.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.isZero_etaComplex_X`: the décalage
  of a chart vanishes in every degree in which the chart's complex vanishes.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.isStrictlyPerfect_specEtaComplex`:
  **the translation of tag 0F7W to sheaves on a chart** — if the determinantal ideals of the
  chart are principal then `η_f M^•` gives a strictly perfect complex of `𝒪_U`-modules.
* `AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage.roof_of_iso` and
  `AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage.nonempty_iso`: in any model of
  `D(𝒪_U)`, the comparison is an isomorphism `(Lη_I M)|_U ≅ (η_f M^•)^~`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_derivedEta_obj`: **tag 0GTW**.

## What is carried

Two things are hypotheses rather than theorems here, and both are named in the statement of
tag 0GTW below.

1. The functor `Lη_I` itself, as `Stacks.Divisors.Eta.DerivedEta S.D`. That structure is
   [Stacks, Tag 0F8Q] and is already carried that way by
   `StacksFrontier/AlgebraicGeometry/Divisors/EtaDerivedQuasicoherent.lean`, which also records
   that `Stacks.IdealTorsion.Eta.derivedEta` discharges it.

2. `ChartDecalage`, the comparison identifying the restriction of `Lη_I M` to an affine chart
   with the complex of `𝒪_U`-modules coming from the algebraic décalage `η_f M^•` of the
   chart. This is **the second assertion of [Stacks, Tag 0GTV]**. It is stated as a roof of
   quasi-isomorphisms between that complex and the restriction of a representative of
   `Lη_I M`, so it mentions no derived category of `U`; in every model of `D(𝒪_U)` it is an
   isomorphism (`AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage.nonempty_iso`).
   Everything below the comparison — that the algebraic décalage of a chart with principal
   determinantal ideals is termwise finite projective, that the associated complex of sheaves is
   therefore strictly perfect, and that perfectness of `Lη_I M` follows because it is local — is
   proved.

Separately, `isPerfect_derivedEta_obj` asks for charts with principal determinantal ideals at
the points *off* `D` as well, as the hypothesis `hoff`. Good-triple-ness is a condition at the
points of `D` only; off `D` the equation `f` of a chart is a unit, so its determinantal ideals
are automatically the unit ideal, and a chart exists around every point because `M` is perfect.
The source uses both facts without comment — the second is the "details omitted" of the proof
of tag 0GTY, where the affine charts are asserted to form a basis for the topology of `X`.

## Implementation notes

The transport from `Spec Γ(X, U)` to `U` is `Stacks.AffineTilde.transportTildeComplex` along the
isomorphism of ringed spaces underlying `U.2.isoSpec`, so that
`Stacks.AffineTilde.isStrictlyPerfect_transportTildeComplex` applies to it directly.

Tag 0GTW is proved at the level of complexes, with no derived category of an open: a
representative of `Lη_I M` restricts on each chart to a perfect complex, joined by the roof of
`ChartDecalage` to a strictly perfect one, and perfectness of complexes is local
(`AlgebraicGeometry.RingedSpace.isPerfectComplex_of_forall_isPerfectComplex_restrict`). Two
representatives are joined by a roof, which restricts to the chart
(`CochainComplex.QuasiIsoRoof.restrict`). The derived category of `𝒪_X` is the one the triple
carries.

The read-outs `ChartDecalage.roof_of_iso` and `ChartDecalage.nonempty_iso` take a model of
`D(𝒪_U)`, at which the restriction
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules` is derived through its exactness
instances `AlgebraicGeometry.RingedSpace.PseudoCoherence.instPreservesFiniteLimitsRestrictModules`
and `AlgebraicGeometry.RingedSpace.PseudoCoherence.instPreservesFiniteColimitsRestrictModules`.

`Stacks.Cohomology.PerfectComplexes.IsPerfect` and
`AlgebraicGeometry.RingedSpace.IsPerfect` — the predicate `Situation 0F8S` is stated with — are
definitionally equal, so no bridge is needed between the local criterion and the conclusion.

## References

* [Stacks Project, Tag 0GTW](https://stacks.math.columbia.edu/tag/0GTW)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F7W](https://stacks.math.columbia.edu/tag/0F7W)
* [Stacks Project, Tag 0F8Q](https://stacks.math.columbia.edu/tag/0F8Q)
* [Stacks Project, Tag 0GTV](https://stacks.math.columbia.edu/tag/0GTV)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe u d w

attribute [local instance] AlgebraicGeometry.ComplexAndDivisorSituation.isEffectiveCartierDivisor

namespace AlgebraicGeometry.ComplexAndDivisorSituation

variable {S : ComplexAndDivisorSituation.{u, d}}

-- The situation's model of the derived category of `𝒪_X`-modules, in the
-- `AlgebraicGeometry.Scheme.Modules` spelling that `Stacks.Divisors.Eta.DerivedEta` is stated
-- in, is `modulesHasDerivedCategory` from
-- `StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPrincipalityTransfer`.  The two
-- spellings are the same category, but instance search does not see through the semireducible
-- definition, so the instance has to be pinned; it is registered locally there, so it has to be
-- registered again here.
attribute [local instance 100000] modulesHasDerivedCategory

/-- The standard model of the derived category of modules on an open subspace of a ringed
space, as a global instance. No declaration of this file uses it: the comparison on an affine
chart is a roof of quasi-isomorphisms, and its read-outs take a model of `D(𝒪_U)` as a
hypothesis. -/
instance restrictHasDerivedCategory (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    HasDerivedCategory.{u + 1} (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) :=
  HasDerivedCategory.standard _

namespace AffineChart

/-- The algebraic décalage `η_f M^•` of the bounded complex of an affine chart, as a cochain
complex of `Γ(X, U)`-modules. Its degree-`i` term is the submodule
`{x ∈ fⁱ(M^i)_f | dⁱ x ∈ fⁱ⁺¹(M^{i+1})_f}` of the localization of `M^i` at `f`. -/
def etaComplex (C : AffineChart S) : CochainComplex (ModuleCat.{u} Γ(S.X, C.U)) ℤ :=
  EtaComplex.etaObject C.f C.complex.toCochainComplex

/-- In a degree in which the chart's complex vanishes, so does its décalage: the décalage term
is a submodule of a localization of the zero module. -/
theorem isZero_etaComplex_X (C : AffineChart S) {i : ℤ} (h : C.complex.rank i = 0) :
    Limits.IsZero (C.etaComplex.X i) := by
  have hsub : Subsingleton (Fin (C.complex.rank i) → Γ(S.X, C.U)) := by
    rw [h]; infer_instance
  have hloc : Subsingleton (EtaPow.Loc C.f (C.complex.toCochainComplex.X i)) := by
    refine ⟨fun a b => ?_⟩
    induction a using LocalizedModule.induction_on with
    | _ m s =>
      induction b using LocalizedModule.induction_on with
      | _ n t =>
        have hmn : (t : Γ(S.X, C.U)) • m = (s : Γ(S.X, C.U)) • n := hsub.allEq _ _
        exact LocalizedModule.mk_eq.mpr ⟨1, by simp only [one_smul]; exact hmn⟩
  have hsing : Subsingleton (C.etaComplex.X i) :=
    ⟨fun a b => Subtype.ext (hloc.allEq _ _)⟩
  have := hsing
  exact ModuleCat.isZero_of_subsingleton _

/-- The degree-`i` term of the décalage of a chart is the décalage term of More on Algebra,
Section 15.98 for the matrix of `dⁱ`: the two differ only in the spelling of the
differential. -/
theorem etaComplex_X (C : AffineChart S) (i : ℤ) :
    C.etaComplex.X i =
      ModuleCat.of Γ(S.X, C.U) (EtaPow.fetaTerm C.f (C.complex.d i).mulVecLin i) := by
  have h : (C.complex.toCochainComplex.d i (i + 1)).hom = (C.complex.d i).mulVecLin := by
    rw [BoundedComplex.toCochainComplex_d]
    rfl
  exact congrArg (fun m => ModuleCat.of Γ(S.X, C.U) (EtaPow.fetaTerm C.f m i)) h

/-- The terms of the décalage of a chart with principal determinantal ideals are finite
projective: this is the module-level content of **[Stacks, Tag 0F7W]**. -/
theorem finite_projective_etaComplex_X (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) (i : ℤ) :
    Module.Finite Γ(S.X, C.U) (C.etaComplex.X i) ∧
      Module.Projective Γ(S.X, C.U) (C.etaComplex.X i) := by
  have H := EtaPow.LocallyFree.etaTerm_finite_projective_and_split_of_idealI_isPrincipal
    C.complex C.f C.regular i (hI i)
  obtain ⟨⟨hfin, hproj, -⟩, -⟩ := H
  rw [C.etaComplex_X i]
  exact ⟨hfin, hproj⟩

/-- The isomorphism of ringed spaces `Spec Γ(X, U) ≅ U` underlying an affine chart. -/
def specIso (C : AffineChart S) :
    (Spec Γ(S.X, C.U)).toRingedSpace ≅
      S.X.toRingedSpace.restrict C.U.1.isOpenEmbedding :=
  (Scheme.forgetToLocallyRingedSpace ⋙
    LocallyRingedSpace.forgetToSheafedSpace).mapIso C.U.2.isoSpec.symm

/-- The complex of `𝒪_U`-modules associated with the algebraic décalage of an affine chart:
sheafify `η_f M^•` on `Spec Γ(X, U)` and transport along `Spec Γ(X, U) ≅ U`. -/
def specEtaComplex (C : AffineChart S) :
    CochainComplex (OXMod.{u, u} (S.X.toRingedSpace.restrict C.U.1.isOpenEmbedding)) ℤ :=
  Stacks.AffineTilde.transportTildeComplex C.specIso C.etaComplex

/-- **The translation of [Stacks, Tag 0F7W] to sheaves on an affine chart.** If the
determinantal ideals `I_i(M^•, f)` of an affine chart are principal in every degree, then the
complex of `𝒪_U`-modules associated with the algebraic décalage `η_f M^•` is strictly perfect.

Each term of `η_f M^•` is finite projective by tag 0F7W, hence a direct summand of a finite free
module, so the sheaf it gives rise to on `Spec Γ(X, U)` is a direct summand of a finite free
`𝒪`-module; the complex is bounded because the chart's complex is. Transporting along
`Spec Γ(X, U) ≅ U` preserves strict perfection. -/
theorem isStrictlyPerfect_specEtaComplex (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) :
    StrictlyPerfect.IsStrictlyPerfect C.specEtaComplex :=
  Stacks.AffineTilde.isStrictlyPerfect_transportTildeComplex C.specIso C.etaComplex
    (C.complex.bounded.subset fun i hi => by
      simp only [Set.mem_ofPred_eq] at hi ⊢
      exact fun hr => hi (C.isZero_etaComplex_X hr))
    (C.finite_projective_etaComplex_X hI)

end AffineChart

/-- The affine-chart comparison for the derived décalage, carried as a hypothesis: on an affine
chart whose determinantal ideals are principal, some complex `K` representing `Lη_I M` restricts
to a complex joined by a roof of quasi-isomorphisms to the complex of `𝒪_U`-modules associated
with the algebraic décalage `η_f M^•` of the chart. It mentions no derived category of `U`; in
every model of `D(𝒪_U)` it is an isomorphism between the restriction of `Lη_I M` and that complex
(`AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage.nonempty_iso`,
`AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage.roof_of_iso`).

This is **the second assertion of [Stacks, Tag 0GTV]**, the statement that on `Spec(A)` with
`D = V(f)` the functor `Lη_f` on `D(A)` corresponds to `Lη_I` under the equivalence of tag
06Z0. -/
structure ChartDecalage (S : ComplexAndDivisorSituation.{u, d})
    (E : Stacks.Divisors.Eta.DerivedEta S.D) : Prop where
  /-- On a chart with principal determinantal ideals, a representative of `Lη_I M` restricts to
  a complex joined to the complex of the algebraic décalage by a roof of quasi-isomorphisms. -/
  roof : ∀ C : AffineChart S, (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) →
    ∃ K : CochainComplex (OXMod.{u, u} S.X.toRingedSpace) ℤ,
      Nonempty ((@DerivedCategory.Q _ _ _ S.hasDerivedCategory).obj K ≅ E.functor.obj S.M) ∧
        CochainComplex.QuasiIsoRoof C.specEtaComplex (RingedSpace.restrictComplex K C.U.1)

/-- Some complex of `𝒪_X`-modules represents `Lη_I M` in the derived category of the triple. -/
private theorem exists_obj_iso_derivedEta (S : ComplexAndDivisorSituation.{u, d})
    (E : Stacks.Divisors.Eta.DerivedEta S.D) :
    ∃ K : CochainComplex (OXMod.{u, u} S.X.toRingedSpace) ℤ,
      Nonempty ((@DerivedCategory.Q _ _ _ S.hasDerivedCategory).obj K ≅ E.functor.obj S.M) :=
  ⟨_, ⟨(@DerivedCategory.Q _ _ _ S.hasDerivedCategory).objObjPreimageIso _⟩⟩

namespace ChartDecalage

variable {E : Stacks.Divisors.Eta.DerivedEta S.D}

/-- **An isomorphism on a chart, in a model of `D(𝒪_U)`, gives the roof of the comparison.** If
the restriction of `Lη_I M` to the chart is isomorphic to the complex of the algebraic décalage
in some model of `D(𝒪_U)`, then any representative of `Lη_I M` restricts to a complex joined to
it by a roof of quasi-isomorphisms (`CochainComplex.quasiIsoRoof_iff_nonempty_iso`). -/
theorem roof_of_iso (C : AffineChart S)
    [HasDerivedCategory.{w} (OXMod.{u, u} (S.X.toRingedSpace.restrict C.U.1.isOpenEmbedding))]
    (e : (RingedSpace.PseudoCoherence.restrictModules S.X.toRingedSpace
        C.U.1).mapDerivedCategory.obj (E.functor.obj S.M) ≅
      DerivedCategory.Q.obj C.specEtaComplex) :
    ∃ K : CochainComplex (OXMod.{u, u} S.X.toRingedSpace) ℤ,
      Nonempty ((@DerivedCategory.Q _ _ _ S.hasDerivedCategory).obj K ≅ E.functor.obj S.M) ∧
        CochainComplex.QuasiIsoRoof C.specEtaComplex (RingedSpace.restrictComplex K C.U.1) := by
  let R := RingedSpace.PseudoCoherence.restrictModules S.X.toRingedSpace C.U.1
  obtain ⟨K, ⟨eK⟩⟩ := exists_obj_iso_derivedEta S E
  exact ⟨K, ⟨eK⟩, (CochainComplex.quasiIsoRoof_iff_nonempty_iso _ _).2
    ⟨e.symm ≪≫ R.mapDerivedCategory.mapIso eK.symm ≪≫ R.mapDerivedCategoryFactors.app K⟩⟩

/-- **The comparison on a chart is an isomorphism in every model of `D(𝒪_U)`**: the restriction
of `Lη_I M` to a chart with principal determinantal ideals is isomorphic to the complex of
`𝒪_U`-modules of the algebraic décalage of the chart. -/
theorem nonempty_iso (h : ChartDecalage S E) (C : AffineChart S)
    (hC : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal)
    [HasDerivedCategory.{w} (OXMod.{u, u} (S.X.toRingedSpace.restrict C.U.1.isOpenEmbedding))] :
    Nonempty ((RingedSpace.PseudoCoherence.restrictModules S.X.toRingedSpace
        C.U.1).mapDerivedCategory.obj (E.functor.obj S.M) ≅
      DerivedCategory.Q.obj C.specEtaComplex) := by
  obtain ⟨K, ⟨eK⟩, hr⟩ := h.roof C hC
  obtain ⟨e⟩ := (CochainComplex.quasiIsoRoof_iff_nonempty_iso _ _).1 hr
  let R := RingedSpace.PseudoCoherence.restrictModules S.X.toRingedSpace C.U.1
  exact ⟨R.mapDerivedCategory.mapIso eK.symm ≪≫ R.mapDerivedCategoryFactors.app K ≪≫ e.symm⟩

end ChartDecalage

/-- **[Stacks, Tag 0GTW].** Let `X`, `D`, `I`, `M` be as in Situation 0F8S. If `(X, D, M)` is a
good triple, then `Lη_I M` is a perfect object of `D(𝒪_X)`.

The functor `Lη_I` is the hypothesis `E` (tag 0F8Q) and the affine-chart comparison is the
hypothesis `hcomp` (the second assertion of tag 0GTV); `hoff` supplies at the points off `D`
the charts with principal determinantal ideals that good-triple-ness supplies at the points of
`D`. See the module documentation for why each is carried.

Perfectness of a complex is local, so it is enough that, around every point of `X`, a
representative of `Lη_I M` restricts to a perfect complex. A chart with principal determinantal
ideals is such an open: by `hcomp` another representative restricts to a complex joined by a
roof of quasi-isomorphisms to the complex coming from the algebraic décalage of the chart, which
is strictly perfect by the translation of tag 0F7W, and the two representatives are joined by a
roof which restricts to the chart. -/
@[stacks 0GTW "granted Stacks 0F8Q as the hypothesis E, bundled as \
Stacks.Divisors.Eta.DerivedEta, and the second assertion of Stacks 0GTV as the hypothesis \
hcomp; neither is proved in this library. The hypothesis hoff supplies the affine charts with \
principal determinantal ideals at the points off D, which the source leaves implicit"]
theorem isPerfect_derivedEta_obj (S : ComplexAndDivisorSituation.{u, d})
    (E : Stacks.Divisors.Eta.DerivedEta S.D)
    (hS : IsGoodTriple S)
    (hoff : ∀ x ∉ S.D.supportSet, ∃ C : AffineChart S,
      x ∈ (C.U : Set S.X) ∧ ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal)
    (hcomp : ChartDecalage S E) :
    RingedSpace.IsPerfect (X := S.X.toRingedSpace) (E.functor.obj S.M) := by
  obtain ⟨K₀, ⟨e₀⟩⟩ := exists_obj_iso_derivedEta S E
  refine ⟨K₀, RingedSpace.isPerfectComplex_of_forall_isPerfectComplex_restrict fun x => ?_, ⟨e₀⟩⟩
  obtain ⟨C, hxC, hI⟩ : ∃ C : AffineChart S,
      x ∈ (C.U : Set S.X) ∧ ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal := by
    by_cases hx : x ∈ S.D.supportSet
    · exact hS x hx
    · exact hoff x hx
  obtain ⟨K, ⟨eK⟩, hr⟩ := hcomp.roof C hI
  refine ⟨C.U.1, hxC, (RingedSpace.isPerfectComplex_iff_of_quasiIsoRoof
    (((CochainComplex.quasiIsoRoof_iff_nonempty_iso K K₀).2 ⟨eK ≪≫ e₀.symm⟩).restrict
      C.U.1)).1 ?_⟩
  exact (RingedSpace.isPerfectComplex_iff_of_quasiIsoRoof hr).1
    (RingedSpace.isPerfectComplex_of_isStrictlyPerfect (C.isStrictlyPerfect_specEtaComplex hI))

end AlgebraicGeometry.ComplexAndDivisorSituation

end
