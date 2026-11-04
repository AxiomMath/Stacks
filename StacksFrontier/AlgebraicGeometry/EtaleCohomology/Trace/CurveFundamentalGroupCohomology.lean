module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.Continuous
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.HomologicalConstructions
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.LeftDerived
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedEffaceability.EffaceabilityInput
import StacksCore.Tactic.StacksAttribute

/-!
# The (co)homology of a curve as a derived functor on its fundamental group

Let `k` be a field, `X` a geometrically connected smooth curve over `k` with
`X_{k̄} ≠ P¹_{k̄}`, let `Λ` be a finite ring with `#Λ ∈ k^*`, and for a finite `Λ`-module `M`
carrying a continuous `ρ : π₁(X, η̄) → Aut_Λ(M)` let `F_ρ` be the associated sheaf on
`X_étale`.  [Stacks, Tag 03VM] makes four assertions about how the (co)homology of `X_{k̄}`
depends on the pair `(M, ρ)`:

1. `(M, ρ) ↦ H_c^{2-i}(X_{k̄}, F_ρ)` is the **left derived functor** of
   `(M, ρ) ↦ H_c^2(X_{k̄}, F_ρ)`;
2. hence `H_c^{2-i}(X_{k̄}, F_ρ) = H_i(π₁(X_{k̄}, η̄), M)(-1)`;
3. a derived version, `RΓ_c(X_{k̄}, F_ρ) = LH_0(π₁(X_{k̄}, η̄), M(-1))` =
   `M(-1) ⊗^L_{Λ[[π₁(X_{k̄}, η̄)]]} Λ` in `D(Λ[[Ẑ]])`;
4. dually, `(M, ρ) ↦ H^i(X_{k̄}, F_ρ)` is the **right derived functor** of
   `(M, ρ) ↦ M^{π₁(X_{k̄}, η̄)}`, so `H^i(X_{k̄}, F_ρ) = H^i(π₁(X_{k̄}, η̄), M)`.

The source gives one line of proof: *"(Idea) Show both sides are universal δ-functors."*  That
argument — Grothendieck's, [Stacks, Tag 010T] and [Stacks, Tag 010U] — is what this file
formalizes, in both directions of degree, and that is what fixes the shape of everything below:
each statement takes a δ-functor and the input the source's proof actually uses (vanishing on
projectives, resp. on injectives, in positive degree, which is what "is a derived functor"
means), and concludes an identification in *every* degree from one in degree zero.

## Main results

The homological direction, for `H_c^{2-i}`, uses
`Stacks.CategoryHomology.HomologicalDeltaFunctor` — a family `Hᵢ` with connecting morphisms
`Hᵢ₊₁(X₃) ⟶ Hᵢ(X₁)` and the long exact sequence ending `H₀(X₃) ⟶ 0`, which is the shape of the
compactly supported cohomology of `X_{k̄}` reindexed by `i ↦ H_c^{2-i}`:

* `Stacks.EtaleCohomology.CurveFundamentalGroup.deltaFunctorIsoLeftDerived`: assertion 1, as an
  isomorphism of homological δ-functors onto `CategoryTheory.Functor.leftDerived`.
* `Stacks.EtaleCohomology.CurveFundamentalGroup.isoLeftDerived` and
  `isoLeftDerivedOfRightExact`: the same identification degree by degree.
* `Stacks.EtaleCohomology.CurveFundamentalGroup.compactSupportIsoGroupHomology`: assertion 2 —
  from the degree-zero identification of [Stacks, Tag 03VK] and the universality of both
  sides, an isomorphism in every degree.

The cohomological direction, for `H^i`, uses `CategoryTheory.DeltaFunctor`:

* `Stacks.EtaleCohomology.CurveFundamentalGroup.deltaFunctorIsoRightDerived`,
  `isoRightDerived`, `isoRightDerivedOfLeftExact`: assertion 4, against
  `CategoryTheory.Functor.rightDerived`.
* `Stacks.EtaleCohomology.CurveFundamentalGroup.isoContinuousGroupCohomologyRightDerived`,
  `isoContinuousGroupCohomology` and `isoContinuousGroupCohomologyOfInvariants`: assertion 4
  with the group-cohomology side **concrete** — the right derived functors of
  `Stacks.continuousGModuleInvariants` on discrete continuous `G`-modules, that is the
  `H^i(G, M)` of [Stacks, Tag 04JR].

### No unrestricted `@[stacks 03VM]`

Every `@[stacks 03VM]` attribute in this file carries a description of what it proves, because
three of the objects the proposition names do not exist in this repository.  Listed by tag:

* **[Stacks, Tag 03VI], homological half.**  Group *homology* of a profinite group — compact
  (equivalently profinite) `Λ[[G]]`-modules with continuous action, enough projectives there,
  and `H_i(G, M) = Tor_i^{Λ[[G]]}(M, Λ)` — is absent project wide; only the cohomological half
  is formalized (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/GroupCohomology/`).  So the
  `H_i(π₁(X_{k̄}, η̄), M)(-1)` side of assertion 2 is *not constructed here*: it enters
  `compactSupportIsoGroupHomology` as a second homological δ-functor `Hgp`, with the vanishing
  that makes it a left derived functor as a hypothesis.  No weak substitute is built.
* **Assertion 3 is not stated.**  The completed group algebra `Λ[[G]]`, the derived tensor
  product `- ⊗^L_{Λ[[G]]} Λ`, and `D(Λ[[Ẑ]])` are all part of the same missing half of
  [Stacks, Tag 03VI]; without them there is nothing to state.
* **[Stacks, Tag 03VK].**  The degree-zero base case `H_c^2(X_{k̄}, F_ρ) = M_{π₁(X_{k̄}, η̄)}(-1)`
  is taken as the explicit named hypothesis `base` of `compactSupportIsoGroupHomology`.  It is
  not reproved or redefined here.
* **The Tate twist `(-1)`.**  No cyclotomic character and no Tate twist are formalized in this
  repository, so the twist appears only inside the hypotheses `Hgp` and `base`, never as a
  construction of this file.
* **[Stacks, Tag 0GIY], [Stacks, Tag 03QW], [Stacks, Tag 0GK1], [Stacks, Tag 03VL].**  The
  étale side — the equivalence between finite locally constant sheaves on `X_{k̄}` and
  continuous `π₁`-representations, and the long exact sequence of compactly supported
  cohomology read as a δ-functor on the category of pairs `(M, ρ)` — is likewise a hypothesis:
  the δ-functors `Hc` and `Het` below.  The coefficient category is an arbitrary abelian
  category, so instantiating it at the finite `Λ`-modules with continuous `ρ` is exactly the
  statement of 03VM once those inputs exist.

* **Left exactness of `Stacks.continuousGModuleInvariants`.**  Not a Stacks gap but a Mathlib
  one: `CategoryTheory.ObjectProperty.ι` has `preservesMonomorphisms` and
  `preservesEpimorphisms` but no `PreservesFiniteLimits`, so the invariants functor on discrete
  continuous `G`-modules — a right adjoint composed with two exact inclusions — cannot be given
  that instance here.  It is therefore an instance hypothesis of
  `isoContinuousGroupCohomologyOfInvariants` only; the other two concrete statements phrase
  their degree-zero input against `R ⁰` of invariants and assume nothing.

What *is* proved, with no hypothesis beyond the stated ones, is the content of the source's
proof: both sides are universal δ-functors, so a degree-zero identification propagates to all
degrees, and the derived-functor description of the (co)homology follows.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
* [Stacks Project, Tag 010U](https://stacks.math.columbia.edu/tag/010U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.CategoryHomology

universe v v' u u'

namespace Stacks.EtaleCohomology.CurveFundamentalGroup

/-! ### The homological direction: `H_c^{2-i}` as a left derived functor -/

section Homological

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughProjectives A]
  {B : Type u'} [Category.{v'} B] [Abelian B]

/-- **The left derived functors of an additive functor are a universal homological δ-functor.**
This is the "one side" of the source's proof in the homological direction: the higher left
derived functors vanish on projective objects, so the dual of [Stacks, Tag 010T] applies. -/
theorem leftDerived_isUniversal (T : A ⥤ B) [T.Additive] :
    T.leftDerivedHomologicalDeltaFunctor.IsUniversal :=
  HomologicalDeltaFunctor.isUniversal_of_isZero_projective _ fun n P _ ↦ by
    rw [Functor.leftDerivedHomologicalDeltaFunctor_functor]
    exact T.isZero_leftDerived_obj_projective_succ n P

/-- **[Stacks, Tag 03VM], first assertion.**  A homological δ-functor `Hc` whose positive-degree
parts vanish on projective objects, and whose degree-zero part is identified with the
degree-zero left derived functor of an additive `T`, *is* the left derived functor of `T`: the
identification extends uniquely to an isomorphism of homological δ-functors.

In the source `Hc` is `i ↦ H_c^{2-i}(X_{k̄}, F_ρ)` on the category of pairs `(M, ρ)` and `T` is
`(M, ρ) ↦ H_c^2(X_{k̄}, F_ρ)`; the proof is the source's, that both sides are universal
δ-functors. -/
@[stacks 03VM "first assertion, by the source's own proof (both sides are universal δ-functors): \
a homological δ-functor whose positive degrees vanish on projectives IS the left derived \
functor of its degree-zero part. The compactly supported cohomology δ-functor \
`i ↦ H_c^{2-i}(X_k̄, F_ρ)` of the pair `(M, ρ)` is the hypothesis `Hc` and its vanishing on \
projectives the hypothesis `hvanish`, since the étale input (0GIY, 03QW, 0GK1, 03VL) is not \
available; no Tate twist is constructed"]
def deltaFunctorIsoLeftDerived (Hc : HomologicalDeltaFunctor A B) (T : A ⥤ B) [T.Additive]
    (hvanish : ∀ (n : ℕ) (P : A) [Projective P], IsZero ((Hc.functor (n + 1)).obj P))
    (base : Hc.functor 0 ≅ T.leftDerived 0) :
    Hc ≅ T.leftDerivedHomologicalDeltaFunctor :=
  haveI := HomologicalDeltaFunctor.isUniversal_of_isZero_projective Hc hvanish
  haveI := leftDerived_isUniversal (B := B) T
  HomologicalDeltaFunctor.IsUniversal.isoOfIso
    (base ≪≫ (eqToIso (Functor.leftDerivedHomologicalDeltaFunctor_functor T 0)).symm)

/-- **[Stacks, Tag 03VM], first assertion, degree by degree:** `Hcᵢ ≅ Lᵢ T`. -/
@[stacks 03VM "first assertion read degreewise: `H_c^{2-i} ≅ L_i(H_c^2)`, with the compactly \
supported cohomology δ-functor and its vanishing on projectives as hypotheses"]
def isoLeftDerived (Hc : HomologicalDeltaFunctor A B) (T : A ⥤ B) [T.Additive]
    (hvanish : ∀ (n : ℕ) (P : A) [Projective P], IsZero ((Hc.functor (n + 1)).obj P))
    (base : Hc.functor 0 ≅ T.leftDerived 0) (i : ℕ) :
    Hc.functor i ≅ T.leftDerived i :=
  HomologicalDeltaFunctor.isoApp (deltaFunctorIsoLeftDerived Hc T hvanish base) i ≪≫
    eqToIso (Functor.leftDerivedHomologicalDeltaFunctor_functor T i)

/-- **[Stacks, Tag 03VM], first assertion with the degree-zero hypothesis in its usable form.**
When `T` is right exact — as `(M, ρ) ↦ H_c^2(X_{k̄}, F_ρ)` is, being the final term of the long
exact sequence — the degree-zero input is an identification `Hc₀ ≅ T` itself, because
`L₀ T ≅ T`. -/
@[stacks 03VM "first assertion with a right exact degree-zero part: from `H_c^2 ≅ T` with `T` \
right exact, `H_c^{2-i} ≅ L_i T` for every `i`. The δ-functor and the vanishing on projectives \
are hypotheses"]
def isoLeftDerivedOfRightExact (Hc : HomologicalDeltaFunctor A B) (T : A ⥤ B) [T.Additive]
    [PreservesFiniteColimits T]
    (hvanish : ∀ (n : ℕ) (P : A) [Projective P], IsZero ((Hc.functor (n + 1)).obj P))
    (base : Hc.functor 0 ≅ T) (i : ℕ) :
    Hc.functor i ≅ T.leftDerived i :=
  isoLeftDerived Hc T hvanish (base ≪≫ T.leftDerivedZeroIsoSelf.symm) i

/-- **[Stacks, Tag 03VM], second assertion.**  Two homological δ-functors whose positive-degree
parts vanish on projective objects and whose degree-zero parts are identified are identified in
every degree.

This is the "so" of the proposition: with `Hc` the compactly supported cohomology
`i ↦ H_c^{2-i}(X_{k̄}, F_ρ)`, with `Hgp` the twisted group homology
`i ↦ H_i(π₁(X_{k̄}, η̄), M)(-1)`, and with `base` the isomorphism of [Stacks, Tag 03VK], both
sides are universal δ-functors and therefore agree in all degrees.  Neither side is constructed
here — see the module docstring. -/
@[stacks 03VM "second assertion: two homological δ-functors that both vanish on projectives in \
positive degree and agree in degree zero agree in every degree, which is the source's proof of \
`H_c^{2-i} = H_i(π₁(X_k̄, η̄), M)(-1)`. The twisted group homology side is the hypothesis `Hgp` \
(group homology of a profinite group is the absent homological half of 03VI, and no Tate twist \
is formalized) and the degree-zero base case is the hypothesis `base` (03VK)"]
def compactSupportIsoGroupHomology (Hc Hgp : HomologicalDeltaFunctor A B)
    (hHc : ∀ (n : ℕ) (P : A) [Projective P], IsZero ((Hc.functor (n + 1)).obj P))
    (hHgp : ∀ (n : ℕ) (P : A) [Projective P], IsZero ((Hgp.functor (n + 1)).obj P))
    (base : Hc.functor 0 ≅ Hgp.functor 0) (i : ℕ) :
    Hc.functor i ≅ Hgp.functor i :=
  haveI := HomologicalDeltaFunctor.isUniversal_of_isZero_projective Hc hHc
  haveI := HomologicalDeltaFunctor.isUniversal_of_isZero_projective Hgp hHgp
  HomologicalDeltaFunctor.isoApp (HomologicalDeltaFunctor.IsUniversal.isoOfIso base) i

end Homological

/-! ### The cohomological direction: `H^i` as a right derived functor -/

section Cohomological

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A] [HasDerivedCategory A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory B]

/-- **The right derived functors of an additive functor are a universal cohomological
δ-functor.**  This is the "one side" of the source's proof in the cohomological direction: the
higher right derived functors vanish on injective objects, so [Stacks, Tag 010T] applies. -/
theorem rightDerived_isUniversal (T : A ⥤ B) [T.Additive] :
    (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives T).IsUniversal :=
  DeltaFunctor.isUniversal_of_isZero_injective _ fun n I _ ↦ by
    rw [Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives_functor]
    exact T.isZero_rightDerived_obj_injective_succ n I

/-- **[Stacks, Tag 03VM], fourth assertion.**  A cohomological δ-functor `Het` whose
positive-degree parts vanish on injective objects, and whose degree-zero part is identified
with the degree-zero right derived functor of an additive `T`, *is* the right derived functor of
`T`.

In the source `Het` is `i ↦ H^i(X_{k̄}, F_ρ)` on the category of pairs `(M, ρ)` and `T` is
`(M, ρ) ↦ M^{π₁(X_{k̄}, η̄)}`. -/
@[stacks 03VM "fourth assertion, by the source's own proof: a cohomological δ-functor whose \
positive degrees vanish on injectives IS the right derived functor of its degree-zero part, so \
`H^i(X_k̄, F_ρ) = H^i(π₁(X_k̄, η̄), M)`. The étale δ-functor `Het` and its vanishing on \
injectives are hypotheses, since the étale input 0GIY is not available"]
def deltaFunctorIsoRightDerived (Het : DeltaFunctor A B) (T : A ⥤ B) [T.Additive]
    (hvanish : ∀ (n : ℕ) (I : A) [Injective I], IsZero ((Het.functor (n + 1)).obj I))
    (base : Het.functor 0 ≅ T.rightDerived 0) :
    Het ≅ Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives T :=
  haveI := DeltaFunctor.isUniversal_of_isZero_injective Het hvanish
  haveI := rightDerived_isUniversal (B := B) T
  DeltaFunctor.IsUniversal.isoOfIso
    (base ≪≫
      (eqToIso
        (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives_functor T 0)).symm)

/-- **[Stacks, Tag 03VM], fourth assertion, degree by degree:** `Hetⁱ ≅ R ⁱT`. -/
@[stacks 03VM "fourth assertion read degreewise: `H^i(X_k̄, F_ρ) ≅ R^i(M ↦ M^{π₁})`, with the \
étale δ-functor and its vanishing on injectives as hypotheses"]
def isoRightDerived (Het : DeltaFunctor A B) (T : A ⥤ B) [T.Additive]
    (hvanish : ∀ (n : ℕ) (I : A) [Injective I], IsZero ((Het.functor (n + 1)).obj I))
    (base : Het.functor 0 ≅ T.rightDerived 0) (i : ℕ) :
    Het.functor i ≅ T.rightDerived i :=
  CategoryTheory.DeltaFunctor.appIso
      (deltaFunctorIsoRightDerived Het T hvanish base) i ≪≫
    eqToIso (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives_functor T i)

/-- **[Stacks, Tag 03VM], fourth assertion with the degree-zero hypothesis in its usable form.**
When `T` is left exact — as `M ↦ M^{π₁(X_{k̄}, η̄)}` is — the degree-zero input is an
identification `Het₀ ≅ T` itself, because `R ⁰T ≅ T`. -/
@[stacks 03VM "fourth assertion with a left exact degree-zero part: from `H^0(X_k̄, F_ρ) ≅ T` \
with `T` left exact (invariants), `H^i(X_k̄, F_ρ) ≅ R^i T` for every `i`. The étale δ-functor \
and its vanishing on injectives are hypotheses"]
def isoRightDerivedOfLeftExact (Het : DeltaFunctor A B) (T : A ⥤ B) [T.Additive]
    [PreservesFiniteLimits T]
    (hvanish : ∀ (n : ℕ) (I : A) [Injective I], IsZero ((Het.functor (n + 1)).obj I))
    (base : Het.functor 0 ≅ T) (i : ℕ) :
    Het.functor i ≅ T.rightDerived i :=
  isoRightDerived Het T hvanish (base ≪≫ T.rightDerivedZeroIsoSelf.symm) i

end Cohomological

/-! ### The cohomological direction against continuous group cohomology

Here the group-cohomology side of the fourth assertion is the one this repository has: the
right derived functors of `continuousGModuleInvariants`, that is the `H^i(G, M)` of
[Stacks, Tag 04JR], on the category of discrete abelian groups with continuous `G`-action. -/

section ContinuousGroupCohomology

attribute [local instance] HasDerivedCategory.standard

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **[Stacks, Tag 03VM], fourth assertion with the group side concrete.**  A cohomological
δ-functor on discrete continuous `G`-modules whose positive degrees vanish on injectives and
whose degree-zero part is `H⁰` of the invariants functor agrees, in every degree, with the
higher right derived functors of invariants — the continuous group cohomology `H^i(G, M)` of
[Stacks, Tag 04JR].

Taking `G = π₁(X_{k̄}, η̄)` and the δ-functor `i ↦ H^i(X_{k̄}, F_ρ)`, this is the fourth
assertion of [Stacks, Tag 03VM]. -/
@[stacks 03VM "fourth assertion with the group-cohomology side CONCRETE: for a cohomological \
δ-functor on discrete continuous `G`-modules vanishing on injectives in positive degree and \
agreeing with `R^0` of invariants in degree zero, every degree agrees with the right derived \
functors of invariants, i.e. with the continuous group cohomology `H^i(G, M)` of 04JR. The \
étale δ-functor is still a hypothesis (0GIY is not available)", sga "3 I 5.2.1" "special case"]
def isoContinuousGroupCohomologyRightDerived
    (Het : DeltaFunctor (ContinuousGModule.{u, max u v} G) AddCommGrpCat.{max u v})
    (hvanish : ∀ (n : ℕ) (I : ContinuousGModule.{u, max u v} G) [Injective I],
      IsZero ((Het.functor (n + 1)).obj I))
    (base : Het.functor 0 ≅ (continuousGModuleInvariants.{u, max u v} G).rightDerived 0)
    (i : ℕ) :
    Het.functor i ≅ (continuousGModuleInvariants.{u, max u v} G).rightDerived i :=
  isoRightDerived Het _ hvanish base i

/-- **[Stacks, Tag 03VM], fourth assertion against `Stacks.continuousGroupCohomologyFunctor`.**
The same identification, with the right-hand side spelled as the cohomology functor of
[Stacks, Tag 04JR] (`CategoryTheory.Functor.rightDerivedPlus` of invariants) rather than as
Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`; the two agree by
`Stacks.DerivedIndexing.rightDerivedIso`. -/
@[stacks 03VM "fourth assertion with the right-hand side spelled as the continuous group \
cohomology functor of 04JR itself. The étale δ-functor and its vanishing on injectives are \
hypotheses", sga "3 I 5.2.1" "special case"]
def isoContinuousGroupCohomology
    (Het : DeltaFunctor (ContinuousGModule.{u, max u v} G) AddCommGrpCat.{max u v})
    (hvanish : ∀ (n : ℕ) (I : ContinuousGModule.{u, max u v} G) [Injective I],
      IsZero ((Het.functor (n + 1)).obj I))
    (base : Het.functor 0 ≅ (continuousGModuleInvariants.{u, max u v} G).rightDerived 0)
    (i : ℕ) :
    Het.functor i ≅ continuousGroupCohomologyFunctor.{u, v} G i :=
  isoContinuousGroupCohomologyRightDerived G Het hvanish base i ≪≫
    Stacks.DerivedIndexing.rightDerivedIso (continuousGModuleInvariants.{u, max u v} G) i

/-- **[Stacks, Tag 03VM], fourth assertion with both sides in the source's own form.**  From the
degree-zero identification `H^0(X_{k̄}, F_ρ) ≅ M^{π₁(X_{k̄}, η̄)}` — invariants themselves, not
`R ⁰` of invariants — the étale δ-functor agrees in every degree with the continuous group
cohomology `H^i(G, M)` of [Stacks, Tag 04JR].

Left exactness of `Stacks.continuousGModuleInvariants` is an instance *hypothesis*: it is true
(invariants are a right adjoint, and the two full-subcategory inclusions involved are exact),
but `CategoryTheory.ObjectProperty.ι` carries no `PreservesFiniteLimits` instance in Mathlib,
so there is nothing here to discharge it with.  The variant without it is
`isoContinuousGroupCohomology`, whose degree-zero input is phrased against `R ⁰`. -/
@[stacks 03VM "fourth assertion with BOTH sides in the source's own form: from \
`H^0(X_k̄, F_ρ) ≅ M^{π₁}` (the invariants functor itself) the étale δ-functor agrees in every \
degree with the continuous group cohomology `H^i(G, M)` of 04JR. Left exactness of the \
invariants functor is an instance hypothesis — true, but Mathlib gives no \
`PreservesFiniteLimits` instance for a full-subcategory inclusion — and the étale δ-functor \
with its vanishing on injectives is a hypothesis (0GIY is not available)"]
def isoContinuousGroupCohomologyOfInvariants
    [PreservesFiniteLimits (continuousGModuleInvariants.{u, max u v} G)]
    (Het : DeltaFunctor (ContinuousGModule.{u, max u v} G) AddCommGrpCat.{max u v})
    (hvanish : ∀ (n : ℕ) (I : ContinuousGModule.{u, max u v} G) [Injective I],
      IsZero ((Het.functor (n + 1)).obj I))
    (base : Het.functor 0 ≅ continuousGModuleInvariants.{u, max u v} G) (i : ℕ) :
    Het.functor i ≅ continuousGroupCohomologyFunctor.{u, v} G i :=
  isoRightDerivedOfLeftExact Het _ hvanish base i ≪≫
    Stacks.DerivedIndexing.rightDerivedIso (continuousGModuleInvariants.{u, max u v} G) i

end ContinuousGroupCohomology

end Stacks.EtaleCohomology.CurveFundamentalGroup
