module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentAbelian
import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcChartLocalization

/-!
# Quotients of a quasi-coherent module and an fpqc covering (Stacks 08IU)

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `F` be a
quasi-coherent `𝒪_X`-module.  Stacks 08IU records, for an fpqc covering `{f i : X i ⟶ X}` and
for each pair `i, j` an fpqc covering `{X ijk ⟶ X i ×_X X j}`, a bijection

`{quotients F ⟶ Q with Q quasi-coherent}`
`⟶ {families of quotients f i ^* F ⟶ Q i with Q i quasi-coherent and with Q i and Q j`
`restricting to the same quotient on X ijk}`

whose inverse is fpqc descent of quasi-coherent modules.

This file supplies the restriction of a quotient along a morphism of algebraic spaces, which is
the map the source writes down, and proves that it is injective on quotients whose kernel and
quotient module are quasi-coherent: such a quotient of `F` is determined by its restrictions
along the members of the covering.  The full bijection, with exactly the source's hypotheses, is
`AlgebraicGeometry.Space.bijOn_quotientRestrict_of_isFpqcCovering` of
`StacksFrontier/AlgebraicGeometry/Quot/QuotientDescentClauses.lean`, which uses the injectivity
proved here.

## Main definitions

* `AlgebraicGeometry.Space.quotientRestrict`: the restriction of a quotient of `F` along a
  morphism `g : W ⟶ X` of algebraic spaces, recorded by its kernel.  This is the map of the
  displayed bijection of Stacks 08IU at one member of the covering.
* `AlgebraicGeometry.Space.ReflectsZeroAlongFpqcCovering`: **the faithfulness clause of
  Stacks 04W8** as a named predicate — a homomorphism of quasi-coherent modules whose inverse
  images along the members of an fpqc covering all vanish is zero.

## Main results

* `AlgebraicGeometry.Space.modulePullback_reflectsZero_of_isFpqcCovering`: that predicate,
  **proved**, by the reduction of the faithfulness clause to the represented case.
* `AlgebraicGeometry.Space.quotientRestrictCokernelIso`: the quotient by the restriction of a
  quotient is the inverse image of the quotient, so `quotientRestrict` really does record the
  source's quotient `f i ^* F ⟶ f i ^* Q`.
* `AlgebraicGeometry.Space.quotientRestrict_comp`: restriction of a quotient is transitive,
  which is what makes the compatibility condition of the source hold for the restrictions of a
  single quotient.
* `AlgebraicGeometry.Space.le_of_quotientRestrict_le`: if along every member of an fpqc covering
  the restriction of one quotient is contained in the restriction of another, then the first
  quotient is contained in the second.
* `AlgebraicGeometry.Space.eq_of_quotientRestrict_eq` and
  `AlgebraicGeometry.Space.injOn_quotientRestrict`: a quotient with quasi-coherent kernel
  and quasi-coherent quotient module is determined by its restrictions along an fpqc covering;
  this is the injectivity step of Stacks 08IU.

## Implementation notes

**Quotients are recorded by their kernels.**  As in Situation 082M (Stacks 082M), two quotients
of `F` with the same kernel are the same quotient, so the left-hand set of the source is a set
of elements of `CategoryTheory.Subobject F`; the quotient attached to `K` is
`CategoryTheory.Limits.cokernel` of `K.arrow`, and the restriction of that quotient along
`g : W ⟶ X` is the kernel of the inverse image of the projection, which is
`AlgebraicGeometry.Space.quotientRestrict`.  The *quotient* is what restricts: the inverse image
of modules is a left adjoint, so it preserves epimorphisms but is not known to preserve
monomorphisms, and the inclusion of a submodule therefore has no inverse image that is again an
inclusion.  This is the same choice, and for the same reason, as
`AlgebraicGeometry.Space.QuotientSituation.quotientPullback` of
`StacksFrontier/AlgebraicGeometry/Quot/QuotientFunctorPullback.lean`; no base-change comparison
occurs here, because the module being restricted is `F` itself and not a base change of it.

**Where the clauses of Stacks 04W8 enter.**  The source's bijection is the fpqc descent of
quasi-coherent modules, Stacks 04W8.  Injectivity needs only the faithfulness clause, and only
for the covering `{X i ⟶ X}`.  That clause is
`AlgebraicGeometry.Space.ReflectsZeroAlongFpqcCovering`, the named predicate that
`AlgebraicGeometry.Space.modulePullback_reflectsZero_of_isFpqcCovering` proves below out of
`AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_map_injective_of_isFpqcCovering`
and the represented case `AlgebraicGeometry.Space.QuasiCoherentDescent.reprFpqcHomInjective`;
the predicate is kept because `AlgebraicGeometry.Space.ReflectsIsoAlongFpqcCovering` of
`StacksFrontier/AlgebraicGeometry/Quot/RelativeIsom.lean` and the statements of
`StacksFrontier/AlgebraicGeometry/Quot/QuotientFunctorSourceSheaf.lean` take it as an argument.
Surjectivity uses the fullness and effectivity clauses
(`AlgebraicGeometry.Space.QuasiCoherentDescent.full_canonicalDescentFunctor_of_isFpqcCovering'`
and `AlgebraicGeometry.Space.QuasiCoherentDescent.forall_isEffective_of_isFpqcCovering`) and is
proved, together with the bijection, in
`StacksFrontier/AlgebraicGeometry/Quot/QuotientDescentClauses.lean`.

**Why injectivity needs no exactness.**  One expects to compare two submodules by comparing
their inverse images, which would need the inverse image to preserve monomorphisms.  The proof
below avoids the issue: containment `K ≤ K'` of subobjects of `F` is the vanishing of the
composite `K ⟶ F ⟶ F/K'`, and that single homomorphism is killed by the inverse images of the
covering precisely because the restriction of the quotient by `K` is contained in the
restriction of the quotient by `K'`.  Only the faithfulness clause is then needed.

**The quasi-coherence of the kernel.**  The faithfulness clause applies to a homomorphism of
quasi-coherent modules, and its source here is the submodule `K`.  Its quasi-coherence is a
hypothesis of the results below, which sit before the kernel clause of Stacks 03M1 in the import
order; `AlgebraicGeometry.Space.kernelQuasicoherent` of
`StacksFrontier/AlgebraicGeometry/Quot/QuotientDescentClauses.lean` proves it from that of `F` and
`F/K`, and `AlgebraicGeometry.Space.bijOn_quotientRestrict_of_isFpqcCovering` discharges the
hypothesis with it.

## References

* [Stacks Project, Tag 08IU](https://stacks.math.columbia.edu/tag/08IU)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/- The ambient-universe abelian structure on sheaves of modules does not apply to the modules on
an algebraic space, whose sections live in the universe of the site's morphisms; it is switched
off so that instance search finds the structure of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulesAbelian.lean` directly. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/- Instance search reaches the abelian structure of sheaves of modules, and its kernels and
cokernels, at the universes of the ambient site before it reaches the ones of the modules on an
algebraic space; the latter are given priority so that it stops at the right ones. -/
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso

/-! ### Restriction of a quotient along a morphism of algebraic spaces -/

/-- **The restriction of a quotient along a morphism `g : W ⟶ X` of algebraic spaces.**  A
quotient of a module `F` on `X` is recorded by its kernel, a subobject `K` of `F`, the quotient
itself being `F/K`; its restriction along `g` is the quotient `g^*F ⟶ g^*(F/K)` of `g^*F`,
recorded in the same way by its kernel.

This is the map of the displayed bijection of Stacks 08IU, at one member of the covering. -/
def quotientRestrict {X W : AlgebraicSpaces B S hS} (g : W ⟶ X)
    {F : Modules.{u, u} B S hS X.1 X.2} (K : Subobject F) :
    Subobject ((modulePullback B S hS g).obj F) :=
  kernelSubobject ((modulePullback B S hS g).map (cokernel.π K.arrow))

/-- **The quotient by the restriction of a quotient is the inverse image of the quotient.**  The
restriction of `F ⟶ F/K` along `g` is `g^*F ⟶ g^*(F/K)`, which is what makes
`AlgebraicGeometry.Space.quotientRestrict` the restriction of the source.

A helper for Stacks 08IU: the displayed bijection of that Remark is read through this
comparison of a restricted quotient with the inverse image of the quotient. -/
def quotientRestrictCokernelIso {X W : AlgebraicSpaces B S hS} (g : W ⟶ X)
    {F : Modules.{u, u} B S hS X.1 X.2} (K : Subobject F) :
    cokernel (quotientRestrict g K).arrow ≅
      (modulePullback B S hS g).obj (cokernel K.arrow) :=
  Abelian.cokernelKernelSubobjectIso ((modulePullback B S hS g).map (cokernel.π K.arrow))

/-- The projection onto the quotient by the restriction of a quotient is the inverse image of
the projection, read through `AlgebraicGeometry.Space.quotientRestrictCokernelIso`. -/
theorem cokernel_π_comp_quotientRestrictCokernelIso_inv {X W : AlgebraicSpaces B S hS}
    (g : W ⟶ X) {F : Modules.{u, u} B S hS X.1 X.2} (K : Subobject F) :
    (modulePullback B S hS g).map (cokernel.π K.arrow) ≫
        (quotientRestrictCokernelIso g K).inv =
      cokernel.π (quotientRestrict g K).arrow :=
  Abelian.cokernelKernelSubobjectIso_inv_comp
    ((modulePullback B S hS g).map (cokernel.π K.arrow))

/-- **Restriction of a quotient is transitive.**  Restricting a quotient of `F` along `g` and
then along `k` is restricting it along the composite, up to the identification of the inverse
image along a composite with the iterated inverse image: both are the kernel of the iterated
inverse image of the projection `F ⟶ F/K`.

This is what makes the condition of the source — that two members of a family restrict to the
same quotient on a common refinement of their fibre product — hold for the family of
restrictions of a single quotient. -/
theorem quotientRestrict_comp {X W V : AlgebraicSpaces B S hS} (g : W ⟶ X) (k : V ⟶ W)
    {F : Modules.{u, u} B S hS X.1 X.2} (K : Subobject F) :
    quotientRestrict k (quotientRestrict g K) =
      kernelSubobject ((modulePullback B S hS k).map
        ((modulePullback B S hS g).map (cokernel.π K.arrow))) :=
  kernelSubobject_eq_of_comp_mono _ _
    ((modulePullback B S hS k).map (quotientRestrictCokernelIso g K).inv)
    (by rw [← Functor.map_comp, cokernel_π_comp_quotientRestrictCokernelIso_inv])

/-- The inclusion of the kernel of the restricted quotient is killed by the inverse image of the
projection: the restriction of a quotient is, by construction, a kernel. -/
theorem quotientRestrict_arrow_comp {X W : AlgebraicSpaces B S hS} (g : W ⟶ X)
    {F : Modules.{u, u} B S hS X.1 X.2} (K : Subobject F) :
    (quotientRestrict g K).arrow ≫
      (modulePullback B S hS g).map (cokernel.π K.arrow) = 0 :=
  kernelSubobject_arrow_comp _

/-! ### The faithfulness clause of Stacks 04W8 -/

/-- **The faithfulness clause of Stacks 04W8**, in the form the injectivity of the bijection of
Stacks 08IU consumes it: given an fpqc covering `(p i : Z i ⟶ W)` of algebraic spaces over `S`
and two quasi-coherent `𝒪_W`-modules, a homomorphism between them whose inverse images along the
members of the covering all vanish is itself zero.

This is the statement that the functor from quasi-coherent modules on `W` to descent data for
the covering is faithful, read on one homomorphism; it is the vanishing of a homomorphism rather
than the injectivity of a map of `Hom` sets because that functor is additive.  It is a named
predicate because the statements that consume it elsewhere take it as an argument;
`AlgebraicGeometry.Space.modulePullback_reflectsZero_of_isFpqcCovering` below proves it, so
nothing that uses it is conditional. -/
def ReflectsZeroAlongFpqcCovering (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Prop :=
  ∀ {I : Type v} {W : AlgebraicSpaces B S hS} {Z : I → AlgebraicSpaces B S hS}
    (p : ∀ i, Z i ⟶ W), IsFpqcCovering B S hS (fun i ↦ (p i).hom) →
    ∀ M N : Modules.{u, u} B S hS W.1 W.2, M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
    ∀ φ : M ⟶ N, (∀ i, (modulePullback B S hS (p i)).map φ = 0) → φ = 0

/-- **The faithfulness clause of Stacks 04W8, proved.**  A homomorphism of quasi-coherent
modules whose inverse images along the members of an fpqc covering all vanish is zero.

The inverse image of `𝒪`-modules is a left adjoint by the adjunction half of Stacks 03LU, so it
preserves the zero homomorphism; the hypothesis therefore says that the inverse images of `φ`
and of `0` agree along every member of the covering, and
`AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_map_injective_of_isFpqcCovering`
makes `φ = 0`.  That reduction takes the represented case as an argument and
`AlgebraicGeometry.Space.QuasiCoherentDescent.reprFpqcHomInjective` is a term of its type, so
nothing is assumed: no quasi-coherence is used either, the two hypotheses of
`AlgebraicGeometry.Space.ReflectsZeroAlongFpqcCovering` being ignored. -/
theorem modulePullback_reflectsZero_of_isFpqcCovering :
    ReflectsZeroAlongFpqcCovering.{u, v} B S hS := by
  intro I W Z p hp M N _ _ φ hφ
  refine QuasiCoherentDescent.modulePullback_map_injective_of_isFpqcCovering B S hS
    (QuasiCoherentDescent.reprFpqcHomInjective B S hS) Z p hp φ 0 fun i ↦ ?_
  have : (modulePullback B S hS (p i)).IsLeftAdjoint :=
    ⟨_, ⟨modulePullbackAdjunction B S hS (p i)⟩⟩
  rw [hφ i, Functor.map_zero]

/-! ### A quotient is determined by its restrictions along an fpqc covering -/

/-- **The one computation behind injectivity.**  If the restriction along `g` of the quotient by
`K` is contained in the restriction of the quotient by `K'`, then the inverse image along `g` of
the composite `K ⟶ F ⟶ F/K'` vanishes.

The inverse image of `K ⟶ F` is killed by the inverse image of `F ⟶ F/K`, so it factors through
the kernel of the latter, which is the restriction of the quotient by `K`; that kernel is
contained in the kernel of the inverse image of `F ⟶ F/K'`, which kills it. -/
theorem modulePullback_map_arrow_comp_cokernel_π_eq_zero {X W : AlgebraicSpaces B S hS}
    (g : W ⟶ X) {F : Modules.{u, u} B S hS X.1 X.2} {K K' : Subobject F}
    (h : quotientRestrict g K ≤ quotientRestrict g K') :
    (modulePullback B S hS g).map (K.arrow ≫ cokernel.π K'.arrow) = 0 := by
  have hzero : (modulePullback B S hS g).map K.arrow ≫
      (modulePullback B S hS g).map (cokernel.π K.arrow) = 0 := by
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
  have hfac : (quotientRestrict g K).Factors ((modulePullback B S hS g).map K.arrow) :=
    kernelSubobject_factors ((modulePullback B S hS g).map (cokernel.π K.arrow)) _ hzero
  have harrow : (quotientRestrict g K).arrow =
      Subobject.ofLE _ _ h ≫ (quotientRestrict g K').arrow := (Subobject.ofLE_arrow h).symm
  rw [Functor.map_comp, ← Subobject.factorThru_arrow _ _ hfac, Category.assoc, harrow,
    Category.assoc, quotientRestrict_arrow_comp, comp_zero, comp_zero]

/-- **Containment of quotients is fpqc local on the base.**  If along every member of an fpqc
covering of `X` the restriction of the quotient by `K` is contained in the restriction of the
quotient by `K'`, then `K ≤ K'`.

Containment `K ≤ K'` of subobjects of `F` says exactly that the composite `K ⟶ F ⟶ F/K'`
vanishes, and that homomorphism is killed by every inverse image of the covering, by
`AlgebraicGeometry.Space.modulePullback_map_arrow_comp_cokernel_π_eq_zero`; the faithfulness
clause of Stacks 04W8,
`AlgebraicGeometry.Space.modulePullback_reflectsZero_of_isFpqcCovering`, then makes it zero. -/
theorem le_of_quotientRestrict_le
    {I : Type v} {X : AlgebraicSpaces B S hS} {Z : I → AlgebraicSpaces B S hS}
    (p : ∀ i, Z i ⟶ X) (hp : IsFpqcCovering B S hS fun i ↦ (p i).hom)
    {F : Modules.{u, u} B S hS X.1 X.2} {K K' : Subobject F}
    (hK : (K : Modules.{u, u} B S hS X.1 X.2).IsQuasicoherentOnSite)
    (hQ' : (cokernel K'.arrow).IsQuasicoherentOnSite)
    (h : ∀ i, quotientRestrict (p i) K ≤ quotientRestrict (p i) K') : K ≤ K' := by
  have hzero : K.arrow ≫ cokernel.π K'.arrow = 0 :=
    modulePullback_reflectsZero_of_isFpqcCovering.{u, v} p hp _ _ hK hQ' _ fun i ↦
      modulePullback_map_arrow_comp_cokernel_π_eq_zero (p i) (h i)
  have hle := le_kernelSubobject (cokernel.π K'.arrow) K hzero
  rwa [kernelSubobject_cokernel_π] at hle

/-- **A quotient is determined by its restrictions along an fpqc covering.**  Let `X` be an
algebraic space over a scheme `S` of a big fppf site, let `F` be an `𝒪_X`-module and let
`{p i : Z i ⟶ X}` be an fpqc covering.  A quotient of `F` whose quotient module and whose kernel
are quasi-coherent is determined by its restrictions along the members of the covering: two such
quotients that restrict to the same quotient of `p i ^* F` for every `i` are the same quotient
of `F`.

This is the injectivity step of the bijection of Stacks 08IU, which is
`AlgebraicGeometry.Space.bijOn_quotientRestrict_of_isFpqcCovering`. -/
theorem eq_of_quotientRestrict_eq
    {I : Type v} {X : AlgebraicSpaces B S hS} {Z : I → AlgebraicSpaces B S hS}
    (p : ∀ i, Z i ⟶ X) (hp : IsFpqcCovering B S hS fun i ↦ (p i).hom)
    {F : Modules.{u, u} B S hS X.1 X.2} {K K' : Subobject F}
    (hK : (K : Modules.{u, u} B S hS X.1 X.2).IsQuasicoherentOnSite)
    (hK' : (K' : Modules.{u, u} B S hS X.1 X.2).IsQuasicoherentOnSite)
    (hQ : (cokernel K.arrow).IsQuasicoherentOnSite)
    (hQ' : (cokernel K'.arrow).IsQuasicoherentOnSite)
    (h : ∀ i, quotientRestrict (p i) K = quotientRestrict (p i) K') : K = K' :=
  le_antisymm (le_of_quotientRestrict_le p hp hK hQ' fun i ↦ (h i).le)
    (le_of_quotientRestrict_le p hp hK' hQ fun i ↦ (h i).ge)

/-- **Restriction along an fpqc covering is injective on quasi-coherent quotients.**  For an
fpqc covering `{p i : Z i ⟶ X}`, restriction along its members is injective on the set of
quotients of `F` whose quotient module and whose kernel are quasi-coherent.

This is a corollary of `AlgebraicGeometry.Space.eq_of_quotientRestrict_eq`.  The full bijection
of Stacks 08IU is `AlgebraicGeometry.Space.bijOn_quotientRestrict_of_isFpqcCovering`; the
quasi-coherence of the kernel, asked for here, follows from that of `F` and of the quotient
module by `AlgebraicGeometry.Space.kernelQuasicoherent`. -/
theorem injOn_quotientRestrict
    {I : Type v} {X : AlgebraicSpaces B S hS} {Z : I → AlgebraicSpaces B S hS}
    (p : ∀ i, Z i ⟶ X) (hp : IsFpqcCovering B S hS fun i ↦ (p i).hom)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    Set.InjOn (fun (K : Subobject F) i ↦ quotientRestrict (p i) K)
      {K | (K : Modules.{u, u} B S hS X.1 X.2).IsQuasicoherentOnSite ∧
        (cokernel K.arrow).IsQuasicoherentOnSite} :=
  fun _ hK _ hK' h ↦ eq_of_quotientRestrict_eq p hp hK.1 hK'.1 hK.2 hK'.2
    fun i ↦ congrFun h i

end AlgebraicGeometry.Space

end
