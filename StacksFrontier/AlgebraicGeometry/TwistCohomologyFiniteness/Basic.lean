module

public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessTwists.Basic
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.CechVanishing

/-!
# Finite dimensionality of the cohomology of a module on projective space over a field

On projective `n`-space over a field, the cohomology of a quasi-coherent module is a
finite-dimensional vector space in *every* degree as soon as it is one in the finitely many
degrees `0, …, n`. Above degree `n` the group vanishes, by the clause of
[Stacks, Tag 01YS] that is already in the library, so there is nothing to assume there. This
file carries out that reduction, supplies the bridge from the explicit Čech complex of the
standard charts to the field-linear cohomology that consumes it, and runs the whole thing
through the dévissage of [Stacks, Tag 02O6].

**What this is for.** `AlgebraicGeometry.cohomologyOverField` is the sheaf cohomology of a module
on a scheme over `k`, with its `k`-module structure. The theorem
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_biprodPow` reduces
[Stacks, Tag 02O6] over a field to two inputs about projective space: the cohomology of each
twist is finite-dimensional *in every degree* — the Čech computation of [Stacks, Tag 01XT] — and
every coherent module is a quotient of a power of a twist, a clause of [Stacks, Tag 01YS].
This file weakens the first of those two inputs to *the degrees `≤ n`*, and simultaneously
removes the properness hypothesis, which projective space does not currently carry in this
development.

**The degree bound and properness are the same saving.** The general assembly reaches
[Stacks, Tag 02O6] in two ways: with the vanishing degree as a hypothesis, or with properness,
which supplies the vanishing degree. On projective space neither is needed: every quasi-coherent
module has vanishing cohomology above degree `n`, so `n + 1` *is* a vanishing degree for every
coherent module at once, and that is exactly what the hypothesis-form assembly asks for. So
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_projectiveSpace_of_epi_biprodPow`
below carries no properness hypothesis and no vanishing-degree hypothesis — only the two
genuinely projective inputs, one of them now only in degrees `≤ n`.

**Which model of projective space.** Everything projective below is stated on the library's
`AlgebraicGeometry.projectiveSpaceOverRing`, the base change of the integral model along
`Spec R ⟶ Spec ℤ`, because that is the model whose charts, cover and vanishing statement are in
the library and the model whose structure morphism goes to `Spec` of the *coefficient* ring,
which `AlgebraicGeometry.cohomologyOverField` needs. The other model,
`AlgebraicGeometry.Proj` of a polynomial ring, carries
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf` directly and is where the Čech terms
of [Stacks, Tag 01XT] have been described; the two models are identified only over the integers,
by `Stacks.ProjectiveCohomology.integralModelIso`. Nothing below needs the twists, so nothing
below needs that identification: the statements are about an arbitrary quasi-coherent module and
an arbitrary family of coherent modules on the library's model. The morphism to `Spec k` is also
left arbitrary rather than taken to be the structure morphism, since the vanishing clause does
not mention it.

## Main definitions

* `AlgebraicGeometry.cohomologyOverFieldSectionRingHom`: the ring homomorphism from `k` to the
  global sections of the structure sheaf along which `AlgebraicGeometry.cohomologyOverField`
  restricts scalars.
* `AlgebraicGeometry.rightDerivedEvaluationCechHomologyIso`: for a covering with affine finite
  intersections, the right-derived global sections of a quasi-coherent module *are* the homology
  of the explicit Čech complex — the isomorphism, not only the vanishing criterion.
* `AlgebraicGeometry.cohomologyOverFieldCechHomologyIso`: the same isomorphism read as an
  isomorphism of `k`-vector spaces.

## Main results

* `AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isZero_Hgroup`: a vanishing
  cohomology group is finite-dimensional.
* `AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_finiteDimensional_cechHomology`:
  **the Čech bridge** — finite dimensionality of the Čech homology gives finite dimensionality of
  the cohomology.
* `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_le_of_isZero_Hgroup_of_lt`:
  **the degree reduction** — finite dimensionality in degrees `≤ N` plus vanishing above `N`
  gives finite dimensionality in every degree.
* `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_projectiveSpace_of_le`:
  **on projective `n`-space over a field, degrees `≤ n` suffice.**
* `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_projectiveSpace_of_cechHomology`:
  the same from the explicit Čech complex of the `n + 1` standard charts.
* `forall_finiteDimensional_cohomologyOverField_projectiveSpace_of_epi_biprodPow`:
  **[Stacks, Tag 02O6] over a field on projective space, with no properness hypothesis**, from a
  family of coherent modules whose cohomology is finite-dimensional in degrees `≤ n` and which
  resolves every coherent module.

## Implementation notes

**No tag attribute is attached to anything here, and this file proves no tag.** The projective
statements carry the Čech computation of [Stacks, Tag 01XT] as an explicit hypothesis, in the
weakened form "degrees `≤ n`", and the assembly statements carry the quotient-of-twists clause of
[Stacks, Tag 01YS] as `hgen`; neither is in the library. The vanishing used below is
clause (2) of [Stacks, Tag 01YS], whose attribute sits on
`Stacks.ProjectiveCohomology.isZero_Hgroup_of_lt`; repeating it here would put one tag on two
constants, which is the defect no tag scan in this development can see. By the covering-set rule
the attributes for [Stacks, Tag 01XT], [Stacks, Tag 01YS] and [Stacks, Tag 02O6] therefore belong
on none of these declarations. The attribute token is deliberately not spelled out in this
comment: a comment-blind attribute grep reads a spelled token as coverage.

**Why `cohomologyOverField` is reached through `rfl` rather than through `Hgroup`.**
`AlgebraicGeometry.cohomologyOverField` is restriction of scalars applied to the right-derived
functor of `SheafOfModules.evaluation` at `⊤`, so it is the *module-valued* spelling of
cohomology, and `AlgebraicGeometry.cohomologyOverField_eq` records that identification as `rfl`.
The library's `Hgroup` is the abelian-group-valued spelling; the two are bridged by
`Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup`
for vanishing. That is why
the vanishing lemma below goes through that `iff` while the Čech bridge does not need it at all:
the Čech comparison of [Stacks, Tag 01EQ] is stated against the module-valued functor, which is
the one `cohomologyOverField` is built from.

**Finite dimensionality of a zero object has to be proved on the carrier.** `IsZero M` for
`M : ModuleCat S` and `IsZero ((ModuleCat.restrictScalars φ).obj M)` for the same `M` are
statements in two different categories and are not interchangeable by `exact`; the subsingleton
property of the *carrier*, which restriction of scalars does not change, is what crosses. Hence
`AlgebraicGeometry.finiteDimensional_restrictScalars_of_isZero` takes the zero-ness upstairs and
concludes downstairs, rather than being a corollary of a vanishing transfer.

**The vanishing degree used for the dévissage is `n + 1`, not `n`.** The hypothesis-form assembly
wants finite dimensionality of every coherent module's cohomology in all degrees `≥ N`, and on
projective space that is available exactly for `N = n + 1`; at `N = n` it would be the content of
[Stacks, Tag 01XT] at the top degree. The hypothesis on the resolving family is correspondingly
stated at `≤ n` and extended to `≤ n + 1` inside the proof, where the extra degree is again a
vanishing one.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf Stacks.Cohomology.CechDerived

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### A zero module is finite-dimensional -/

/-- **A zero module of `S`-modules is a finite-dimensional `k`-vector space after restriction of
scalars.** Restriction of scalars does not change the carrier, so the subsingleton property
crosses it; a subsingleton is finite and a finite module is a finite module. -/
theorem finiteDimensional_restrictScalars_of_isZero (k : Type u) [Field k] {S : Type u}
    [Ring S] (φ : k →+* S) (M : ModuleCat.{u} S) (h : IsZero M) :
    FiniteDimensional k ((ModuleCat.restrictScalars φ).obj M) := by
  have hs : Subsingleton ((ModuleCat.restrictScalars φ).obj M) :=
    (ModuleCat.isZero_iff_subsingleton (M := M)).mp h
  have : Finite ((ModuleCat.restrictScalars φ).obj M) := Finite.of_subsingleton
  exact Module.Finite.of_finite

/-! ### Cohomology over a field, as restriction of scalars -/

/-- The ring homomorphism from `k` to the global sections of the structure sheaf of a scheme over
`k`, along which `AlgebraicGeometry.cohomologyOverField` restricts scalars: the inverse of the
canonical isomorphism `Γ(Spec k) ≅ k` followed by the map on global sections. -/
def cohomologyOverFieldSectionRingHom (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : k →+* SectionRing X.ringCatSheaf (⊤ : X.Opens) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom

/-- `AlgebraicGeometry.cohomologyOverField` is restriction of scalars applied to the right
derived functor of evaluation at `⊤`. This is the identification that lets the Čech comparison of
[Stacks, Tag 01EQ], which is stated against the module-valued functor, be applied to it with no
bridge. -/
theorem cohomologyOverField_eq (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (F : X.Modules) (q : ℕ) :
    cohomologyOverField k f F q =
      (ModuleCat.restrictScalars (cohomologyOverFieldSectionRingHom k f)).obj
        (((SheafOfModules.evaluation.{u} X.ringCatSheaf
          (op (⊤ : X.Opens))).rightDerived q).obj F) :=
  rfl

/-- **A vanishing cohomology group is finite-dimensional.** The hypothesis is stated with the
library's abelian-group-valued `Hgroup`, which is the spelling every vanishing theorem in this
development uses, and
`Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup` converts it to the
module-valued one that `AlgebraicGeometry.cohomologyOverField` is built from. -/
theorem finiteDimensional_cohomologyOverField_of_isZero_Hgroup (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (F : X.Modules) (q : ℕ)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ q F)) :
    FiniteDimensional k (cohomologyOverField k f F q) :=
  finiteDimensional_restrictScalars_of_isZero k (cohomologyOverFieldSectionRingHom k f) _
    ((Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      X.ringCatSheaf ⊤ q F).mpr h)

/-! ### The Čech complex computes the cohomology, as an isomorphism -/

/-- **For a covering whose finite intersections are affine, the cohomology of a quasi-coherent
module is the homology of the explicit Čech complex** — as an isomorphism, not only as a vanishing
criterion. This is [Stacks, Tag 01XD] composed with the two translations of
`Stacks.Cohomology.CechVanishing`: the comparison of [Stacks, Tag 01EQ] is an isomorphism by
[Stacks, Tag 01ET], its source is the derived-category presentation of the Čech homology and its
target the derived global sections.

The lemma `Stacks.Cohomology.CechVanishing.isZero_Hgroup_iff_isZero_cechHomology` composes the
same four steps through `IsZero`; all three nontrivial steps are isomorphisms, so composing them
as isomorphisms costs nothing extra and is what a finiteness statement needs. -/
def rightDerivedEvaluationCechHomologyIso
    (Y : Scheme.{u}) {I : Type u} (U : Y.Opens) (Ui : I → Y.Opens) (hU : U = ⨆ i, Ui i)
    (haffine : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ j, Ui (s j)))
    (F : Y.Modules) [F.IsQuasicoherent] (p : ℕ) :
    ((SheafOfModules.evaluation.{u} Y.ringCatSheaf (op U)).rightDerived p).obj F ≅
      (cechComplex.{u, u, u, u} U Ui hU F).homology p :=
  have hiso : IsIso ((cechCohomologyToCohomology Y.ringCatSheaf U Ui hU (p : ℤ)).app F) :=
    Stacks.Cohomology.Affine.isIso_cechCohomologyToCohomology_of_isAffineOpen Y U Ui hU
      haffine F p
  -- The two `HasDerivedCategory` instances are passed explicitly. Synthesised from the
  -- ambient local instance they are built at a smaller morphism universe than the one
  -- `cechCohomologyToCohomology` carries, and the derived global sections of
  -- [Stacks, Tag 01EQ] are then no longer definitionally the right derived functor.
  (@Stacks.DerivedIndexing.rightDerivedIso _ _ _ _ _ _ _
      (SheafOfModules.evaluation.{u} Y.ringCatSheaf (op U)) _
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) p).app F ≪≫
    (@asIso _ _ _ _ _ hiso).symm ≪≫
      Stacks.Cohomology.CechVanishing.cechPlusHomologyIso Y.ringCatSheaf U Ui hU F p

/-- The same isomorphism for a scheme over a field, read through restriction of scalars, so that
both sides are `k`-vector spaces and the left-hand side is literally
`AlgebraicGeometry.cohomologyOverField`. -/
def cohomologyOverFieldCechHomologyIso (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {I : Type u} (Ui : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, Ui i)
    (haffine : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ j, Ui (s j)))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) :
    cohomologyOverField k f F p ≅
      (ModuleCat.restrictScalars (cohomologyOverFieldSectionRingHom k f)).obj
        ((cechComplex.{u, u, u, u} (⊤ : X.Opens) Ui hU F).homology p) :=
  (ModuleCat.restrictScalars (cohomologyOverFieldSectionRingHom k f)).mapIso
    (rightDerivedEvaluationCechHomologyIso X ⊤ Ui hU haffine F p)

/-- **The Čech bridge.** If the `p`-th homology of the Čech complex of a covering with affine
finite intersections is a finite-dimensional `k`-vector space, so is `Hᵖ(X, ℱ)`. This is the form
in which a computation with the explicit complex — the whole content of [Stacks, Tag 01XT] — pays
out as a statement about cohomology. -/
theorem finiteDimensional_cohomologyOverField_of_finiteDimensional_cechHomology
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {I : Type u} (Ui : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, Ui i)
    (haffine : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ j, Ui (s j)))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ)
    (hfd : FiniteDimensional k
      ((ModuleCat.restrictScalars (cohomologyOverFieldSectionRingHom k f)).obj
        ((cechComplex.{u, u, u, u} (⊤ : X.Opens) Ui hU F).homology p))) :
    FiniteDimensional k (cohomologyOverField k f F p) :=
  (cohomologyOverFieldCechHomologyIso k f Ui hU haffine F p).symm.toLinearEquiv.finiteDimensional

/-! ### The degree reduction -/

/-- **Finitely many degrees suffice, given vanishing above them.** If the cohomology of `ℱ` is a
finite-dimensional `k`-vector space in every degree `≤ N` and vanishes in every degree `> N`,
then it is finite-dimensional in every degree. Both hypotheses are load-bearing: dropping either
leaves the other range unprovable. -/
theorem forall_finiteDimensional_cohomologyOverField_of_le_of_isZero_Hgroup_of_lt
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (F : X.Modules) (N : ℕ)
    (hle : ∀ q ≤ N, FiniteDimensional k (cohomologyOverField k f F q))
    (hvan : ∀ q, N < q → IsZero (Hgroup X.ringCatSheaf ⊤ q F)) :
    ∀ q : ℕ, FiniteDimensional k (cohomologyOverField k f F q) := by
  intro q
  rcases le_or_gt q N with hq | hq
  · exact hle q hq
  · exact finiteDimensional_cohomologyOverField_of_isZero_Hgroup k f F q (hvan q hq)

/-! ### Projective space over a field -/

/-- **Above degree `n`, the cohomology of a quasi-coherent module on projective `n`-space over a
field is finite-dimensional unconditionally** — it is zero, by clause (2) of
[Stacks, Tag 01YS]. No properness, no Noetherian hypothesis and no coherence is needed, and the
morphism to `Spec k` is arbitrary. -/
theorem finiteDimensional_cohomologyOverField_projectiveSpace_of_lt (k : Type u) [Field k]
    (n : ℕ) (f : projectiveSpaceOverRing n (.of k) ⟶ Spec (.of k))
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsQuasicoherent] (q : ℕ) (hq : n < q) :
    FiniteDimensional k (cohomologyOverField k f F q) :=
  finiteDimensional_cohomologyOverField_of_isZero_Hgroup k f F q
    (Stacks.ProjectiveCohomology.isZero_Hgroup_of_lt n (.of k) F q hq)

/-- **On projective `n`-space over a field, the degrees `0, …, n` decide every degree.** For a
quasi-coherent module whose cohomology is a finite-dimensional `k`-vector space in each of the
`n + 1` lowest degrees, it is finite-dimensional in all of them.

This is what makes the first input of [Stacks, Tag 02O6] on projective space a statement about
finitely many groups rather than about infinitely many. -/
theorem forall_finiteDimensional_cohomologyOverField_projectiveSpace_of_le (k : Type u) [Field k]
    (n : ℕ) (f : projectiveSpaceOverRing n (.of k) ⟶ Spec (.of k))
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsQuasicoherent]
    (hle : ∀ q ≤ n, FiniteDimensional k (cohomologyOverField k f F q)) :
    ∀ q : ℕ, FiniteDimensional k (cohomologyOverField k f F q) :=
  forall_finiteDimensional_cohomologyOverField_of_le_of_isZero_Hgroup_of_lt k f F n hle
    fun q hq => Stacks.ProjectiveCohomology.isZero_Hgroup_of_lt n (.of k) F q hq

/-- **The same, read off the explicit Čech complex of the `n + 1` standard charts.** If the
homology of that complex is a finite-dimensional `k`-vector space in each degree `≤ n`, then the
cohomology of the module is finite-dimensional in every degree.

The hypothesis mentions no derived category, no higher direct image and no sheaf cohomology: it
is a statement about an explicit complex of modules of sections over intersections of the
standard charts. That is the shape in which the computation of [Stacks, Tag 01XT] discharges it.
Affineness of the finite intersections of the charts is
`Stacks.ProjectiveCohomology.isAffineOpen_iInf_chartAtUniverse`, so no hypothesis about the cover
appears. -/
theorem forall_finiteDimensional_cohomologyOverField_projectiveSpace_of_cechHomology
    (k : Type u) [Field k] (n : ℕ) (f : projectiveSpaceOverRing n (.of k) ⟶ Spec (.of k))
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsQuasicoherent]
    (hfd : ∀ q ≤ n, FiniteDimensional k
      ((ModuleCat.restrictScalars (cohomologyOverFieldSectionRingHom k f)).obj
        ((cechComplex.{u, u, u, u} (⊤ : (projectiveSpaceOverRing n (.of k)).Opens)
          (Stacks.ProjectiveCohomology.chartAtUniverse n (.of k))
          (Stacks.ProjectiveCohomology.iSup_chartAtUniverse_eq_top n (.of k)).symm
          F).homology q))) :
    ∀ q : ℕ, FiniteDimensional k (cohomologyOverField k f F q) :=
  forall_finiteDimensional_cohomologyOverField_projectiveSpace_of_le k n f F fun q hq =>
    finiteDimensional_cohomologyOverField_of_finiteDimensional_cechHomology k f
      (Stacks.ProjectiveCohomology.chartAtUniverse n (.of k))
      (Stacks.ProjectiveCohomology.iSup_chartAtUniverse_eq_top n (.of k)).symm
      (fun _ s => Stacks.ProjectiveCohomology.isAffineOpen_iInf_chartAtUniverse n (.of k) s)
      F q (hfd q hq)

/-! ### [Stacks, Tag 02O6] over a field from a family finite in low degrees -/

/-- **The dévissage of [Stacks, Tag 02O6] run on a family that is only known to be
finite-dimensional in low degrees.** This is
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_biprodPow_of_le` with its
hypothesis on the resolving family cut down to the degrees `≤ N`, the remaining degrees being
supplied by vanishing. There is no hypothesis on `f`. -/
theorem forall_finiteDimensional_cohomologyOverField_of_epi_biprodPow_of_le_of_isZero_Hgroup
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (T : ℕ → X.Modules) (N : ℕ)
    (hN : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ q : ℕ, N ≤ q → FiniteDimensional k (cohomologyOverField k f G q))
    (hTcoh : ∀ d : ℕ, SheafOfModules.IsCoherent (T d))
    (hTle : ∀ (d : ℕ), ∀ q ≤ N, FiniteDimensional k (cohomologyOverField k f (T d) q))
    (hTvan : ∀ d q : ℕ, N < q → IsZero (Hgroup X.ringCatSheaf ⊤ q (T d)))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ d r : ℕ, ∃ φ : (T d).biprodPow r ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ q : ℕ, FiniteDimensional k (cohomologyOverField k f G q) :=
  forall_finiteDimensional_cohomologyOverField_of_epi_biprodPow_of_le k f T N hN hTcoh
    (fun d q => forall_finiteDimensional_cohomologyOverField_of_le_of_isZero_Hgroup_of_lt
      k f (T d) N (hTle d) (hTvan d) q) hgen

/-- **[Stacks, Tag 02O6] over a field on projective space, with no properness hypothesis and no
vanishing-degree hypothesis.** Let `𝒯` be a family of coherent modules on projective `n`-space
over a field `k` such that the cohomology of each member is a finite-dimensional `k`-vector space
in each of the degrees `0, …, n`, and such that every coherent module is a quotient of a power of
a member. Then the cohomology of *every* coherent module is a finite-dimensional `k`-vector space
in every degree.

On `ℙⁿ` the family is the twists `𝒪(-d)`: the first hypothesis is the Čech computation of
[Stacks, Tag 01XT], restricted to the `n + 1` degrees in which it has content, and the second is
the quotient-of-twists clause of [Stacks, Tag 01YS].

Two hypotheses of the general assembly are discharged here rather than assumed. The
vanishing degree is `n + 1`, by clause (2) of [Stacks, Tag 01YS] applied to a coherent
— hence quasi-coherent, by [Stacks, Tag 01BW] — module; and properness of `f`, which the general
assembly uses only to produce that degree, is therefore not needed. The morphism `f` is an
arbitrary morphism to `Spec k`. -/
theorem forall_finiteDimensional_cohomologyOverField_projectiveSpace_of_epi_biprodPow
    (k : Type u) [Field k] (n : ℕ) (f : projectiveSpaceOverRing n (.of k) ⟶ Spec (.of k))
    (T : ℕ → (projectiveSpaceOverRing n (.of k)).Modules)
    (hTcoh : ∀ d : ℕ, SheafOfModules.IsCoherent (T d))
    (hTle : ∀ (d : ℕ), ∀ q ≤ n, FiniteDimensional k (cohomologyOverField k f (T d) q))
    (hgen : ∀ G : (projectiveSpaceOverRing n (.of k)).Modules, SheafOfModules.IsCoherent G →
      ∃ d r : ℕ, ∃ φ : (T d).biprodPow r ⟶ G, Epi φ) :
    ∀ G : (projectiveSpaceOverRing n (.of k)).Modules, SheafOfModules.IsCoherent G →
      ∀ q : ℕ, FiniteDimensional k (cohomologyOverField k f G q) := by
  have hTq : ∀ d : ℕ, (T d).IsQuasicoherent :=
    fun d => @_root_.isQuasicoherent_of_isCoherent _ _ _ (T d) (hTcoh d)
  refine forall_finiteDimensional_cohomologyOverField_of_epi_biprodPow_of_le_of_isZero_Hgroup
    k f T (n + 1) (fun G hG q hq => ?_) hTcoh (fun d q _ => ?_) (fun d q hq => ?_) hgen
  · have := @_root_.isQuasicoherent_of_isCoherent _ _ _ G hG
    exact finiteDimensional_cohomologyOverField_projectiveSpace_of_lt k n f G q (by omega)
  · exact forall_finiteDimensional_cohomologyOverField_projectiveSpace_of_le k n f (T d) (hTle d) q
  · exact Stacks.ProjectiveCohomology.isZero_Hgroup_of_lt n (.of k) (T d) q (by omega)

end AlgebraicGeometry

end
