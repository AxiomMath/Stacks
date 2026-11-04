module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusBirational
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusNormalizationBound
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.ElementaryChainPropagation
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.ElementaryStepCokernelOne
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.NormalizationIsoRegularLocus
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.PicardTorsionChain
public import StacksFrontier.AlgebraicGeometry.Curves.IsNode
public import StacksFrontier.AlgebraicGeometry.Curves.MulticrossGlobal.GlueingChain
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.Picard.NormalizationComponents.SmoothCurveBridge
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.Unconditional

/-!
# The `ℓ`-torsion of the Picard group of a reduced proper curve

Let `k` be an algebraically closed field, let `X` be a proper scheme over `k` which is reduced,
connected and of dimension one, let `g` be its genus and let `g_geom` be the sum of the geometric
genera of its irreducible components.  [Stacks, Tag 0C20] states, for a prime `ℓ` different from
the characteristic of `k`,

`dim_{F_ℓ} Pic(X)[ℓ] ≤ g + g_geom`,

with equality if and only if every singularity of `X` is multicross.

This file carries out the source's argument.  The normalization `ν : X^ν ⟶ X` is factored by
[Stacks, Tag 0C1L] as a chain of glueings of two rational points and squishings of tangent
vectors (`AlgebraicGeometry.isElementaryChain_normalizationOverField`), and the two invariants
`dim_{F_ℓ} Pic(-)[ℓ]` and the genus are compared along that chain.  Each step is of one of the
three kinds of the source's table, and the comparison is the per-step arithmetic already in the
library:

* glueing two points on different connected components leaves both invariants unchanged;
* glueing two points on the same connected component raises `dim_{F_ℓ} Pic[ℓ]` by one and the
  genus by one;
* squishing a tangent vector leaves `dim_{F_ℓ} Pic[ℓ]` unchanged and raises the genus by one.

So along a chain the two invariants jump by `n` and by `m` with `n ≤ m`, and `n = m` exactly when
no squishing occurs; `Stacks.GlueSquishFactor.IsGlueingChain` is the predicate "no squishing
occurs".  Substituting the two values of the source at the far end of the chain,
`dim_{F_ℓ} Pic(X^ν)[ℓ] = 2 g_geom` and `h¹(X^ν) = g_geom`, turns `n ≤ m` into the stated bound
and `n = m` into the stated equality.

## The input from Tag 0C1Z

The source's proof quotes clause (1) of [Stacks, Tag 0C1Z] for smooth projective curves over `k`
at the prime `ℓ`, `Pic(C)[ℓ] ≅ (ℤ/ℓℤ)^{⊕2g(C)}`. It is the theorem
`Stacks.Picard.nonempty_torsionBy_addEquiv_pi_zmod_of_smoothProjectiveCurve`
(`Picard/TorsionSmoothProjectiveCurve/Unconditional.lean`). From it the source's value at the
normalization, `dim_{F_ℓ} Pic(X^ν)[ℓ] = 2 g_geom`, is
`AlgebraicGeometry.rank_picardTorsion_normalizationSchemeOverField_eq_two_mul_geometricGenus`:
the normalization is the disjoint union of its connected components, each of dimension one
being a smooth projective curve over `k`. Both halves of Tag 0C20 are registered below.

Everything else is proved: the chain induction; all three lines of the source's table,
including the genus invariance of a glueing across two connected components
(`Stacks.GlueSquishFactor.glueingGenusInvariance`); the equivalence between multicross
singularities and a factorization of the normalization with no squishing, which is
[Stacks, Tag 0C1X] made global over the singular points
(`Stacks.Curves.isGlueingChain_normalizationOver_iff_forall_isMulticrossSingularity`); the
propagation of properness, reducedness and the dimension bound along the chain; and the passage
from the two cardinal identities to the stated inequality and equality of `F_ℓ`-dimensions.

## Main results

* `Stacks.GlueSquishFactor.IsElementaryChain.isReduced_target`: reducedness travels from the
  source of a chain to its target.
* `Stacks.GlueSquishFactor.finrank_globalSections_eq_add_one_of_ne_connectedComponents`: `h⁰`
  rises by exactly one across a glueing of two points on different connected components.
* `Stacks.GlueSquishFactor.genus_eq_of_isGlueingTwoPoints_of_ne_connectedComponents` and its
  packaging `Stacks.GlueSquishFactor.glueingGenusInvariance`: the genus is therefore unchanged
  across such a glueing.  This was the binder `hgg` of both registrations below.
* `Stacks.GlueSquishFactor.exists_rank_torsionBy_picard_genus_of_isElementaryChain`: the
  bookkeeping along a chain — the two invariants jump by `n ≤ m`, with `n = m` only through a
  glueing chain.
* `Stacks.GlueSquishFactor.exists_rank_torsionBy_picard_genus_of_isGlueingChain`: along a
  glueing chain the two jumps are equal.
* `AlgebraicGeometry.finrank_picardTorsion_le_genus_add_geometricGenus_of_isReduced_dim_one`:
  the bound of [Stacks, Tag 0C20] (registered).
* `finrank_picardTorsion_eq_iff_forall_isMulticrossSingularity_of_isReduced_dim_one` (in
  `AlgebraicGeometry`): the equality criterion of [Stacks, Tag 0C20] (registered).

## References

* [Stacks Project, Proposition 53.17.3 (Tag 0C20)](https://stacks.math.columbia.edu/tag/0C20)
* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 0C1M](https://stacks.math.columbia.edu/tag/0C1M)
* [Stacks Project, Tag 0C1N](https://stacks.math.columbia.edu/tag/0C1N)
* [Stacks Project, Tag 0C1J](https://stacks.math.columbia.edu/tag/0C1J)
* [Stacks Project, Tag 0C1X](https://stacks.math.columbia.edu/tag/0C1X)
* [Stacks Project, Tag 0C1Z](https://stacks.math.columbia.edu/tag/0C1Z)
* [Stacks Project, Tag 0C0Y](https://stacks.math.columbia.edu/tag/0C0Y)
* [Stacks Project, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Picard (ofScheme)

universe u

namespace Stacks.GlueSquishFactor

attribute [local instance] AddSubgroup.torsionBy.zmodModule

/-! ### Injectivity on sections, and reducedness along a chain -/

/-- **A glueing of two rational points is injective on sections over every open.** The kernel of
`f^♯` is concentrated at the glued point by the descent clause of
`AlgebraicGeometry.IsGlueingTwoPoints`, and away from that point `f` is an isomorphism. -/
theorem injective_app_of_isGlueingTwoPoints {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b) (U : X.Opens) :
    Function.Injective (f.app U).hom := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hfin, ⟨W, hWset, hWiso⟩, hker, -, -⟩ := id h
  have := hfin
  have := hWiso
  have hkerloc : ∀ (Ω : X.Opens),
      (a ≫ f).base (IsLocalRing.closedPoint k) ∈ Ω → ∀ s : Γ(X, Ω), (f.app Ω).hom s = 0 →
      ∃ (V : X.Opens) (hVΩ : V ≤ Ω),
        (a ≫ f).base (IsLocalRing.closedPoint k) ∈ V ∧
          (X.presheaf.map (homOfLE hVΩ).op).hom s = 0 := by
    intro Ω hx s hs
    obtain ⟨V, hVΩ, hxV, hV0⟩ := hker Ω hx s ⟨Ω, le_rfl, hx, by rw [hs, map_zero]⟩
    exact ⟨V, hVΩ, hxV, hV0⟩
  exact injective_app_of_isIso_of_locally f hWset hkerloc U

/-- **A squishing of a tangent vector is injective on sections over every open.** The predicate
`AlgebraicGeometry.IsSquishingTangentVector` carries a short exact sequence of sheaves of abelian
groups whose first map is `f^♯`, and a monomorphism of sheaves of abelian groups is injective on
sections. -/
theorem injective_app_of_isSquishingTangentVector {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (θ : Spec (.of (DualNumber k)) ⟶ X')
    (h : AlgebraicGeometry.IsSquishingTangentVector f θ) (U : X.Opens) :
    Function.Injective (f.app U).hom := by
  obtain ⟨ψ, hzero, hshort, -⟩ :=
    Stacks.SquishSheafSequence.shortExact_of_isSquishingTangentVector f θ h
  have := hshort.mono_f
  have : Mono (Stacks.SquishSheafSequence.structureToPushforwardAddSheaf f).hom :=
    Functor.map_mono (TopCat.Sheaf.forget AddCommGrpCat.{u} X)
      (Stacks.SquishSheafSequence.structureToPushforwardAddSheaf f)
  exact (AddCommGrpCat.mono_iff_injective
    ((Stacks.SquishSheafSequence.structureToPushforwardAddSheaf f).hom.app (op U))).mp
    inferInstance

/-- **The target of an elementary modification is reduced when its source is.** Both kinds of
step are injective on sections over every open, and a scheme receiving an injection of sections
from a reduced scheme is reduced. -/
theorem IsElementaryStep.isReduced_target {k : Type u} [Field k] [IsAlgClosed k]
    {Y' Y : Over (Spec (.of k))} {f : Y' ⟶ Y} (hf : IsElementaryStep f)
    (hred : IsReduced Y'.left) : IsReduced Y.left := by
  have := hred
  rcases hf with ⟨a, b, hg⟩ | ⟨θ, hs⟩
  · exact isReduced_of_injective_app f.left (injective_app_of_isGlueingTwoPoints f.left a b hg)
  · exact isReduced_of_injective_app f.left
      (injective_app_of_isSquishingTangentVector f.left θ hs)

/-- **The target of a chain of elementary modifications is reduced when its source is.** Applied
to the initial segments of the factorization of [Stacks, Tag 0C1L] this gives the reducedness
which case (3) of the induction of [Stacks, Tag 0C20] asks of the source of every step. Unlike
`Stacks.GlueSquishFactor.IsAlmostIso.isReduced_target` this needs no hypothesis beyond the chain
itself: each individual step is injective on sections, which is all that reducedness uses. -/
theorem IsElementaryChain.isReduced_target {k : Type u} [Field k] [IsAlgClosed k]
    {Y' Y : Over (Spec (.of k))} {f : Y' ⟶ Y} (hf : IsElementaryChain k f)
    (hred : IsReduced Y'.left) : IsReduced Y.left := by
  induction hf with
  | @of_isIso A B g hg =>
    have := hg
    exact ObjectProperty.prop_of_iso (P := fun Z : Scheme.{u} => IsReduced Z)
      (show A.left ≅ B.left from (Over.forget (Spec (.of k))).mapIso (asIso g)) hred
  | of_step g hg => exact hg.isReduced_target hred
  | comp _ _ ihg ihf => exact ihf (ihg hred)

/-- **The source of a chain of elementary modifications has dimension at most that of its
target**: a chain is finite, hence integral, and an integral morphism does not raise the
dimension ([Stacks, Tag 0ECG]). -/
theorem IsElementaryChain.topologicalKrullDim_source_le {k : Type u} [Field k] [IsAlgClosed k]
    {Y' Y : Over (Spec (.of k))} {f : Y' ⟶ Y} (hf : IsElementaryChain k f) :
    topologicalKrullDim (Y'.left : Type u) ≤ topologicalKrullDim (Y.left : Type u) := by
  have := hf.isFinite
  exact topologicalKrullDim_le_of_isIntegralHom f.left

/-! ### The one per-step comparison across two connected components -/

/-- **The genus is unchanged by a glueing of two points lying on different connected components
of a proper source.** This is the line of the source's table for a glueing across two components:
the source reads it off the exact sequence of [Stacks, Tag 0C1J] on global sections, where `h⁰`
rises by one and `h¹` therefore stays put.

This is the packaging in which the chain induction below consumes that comparison; it is
discharged by `Stacks.GlueSquishFactor.glueingGenusInvariance`. -/
def GlueingGenusInvariance (k : Type u) [Field k] [IsAlgClosed k] : Prop :=
  ∀ {Y' Y : Over (Spec (.of k))} (f : Y' ⟶ Y) (a b : Spec (.of k) ⟶ Y'.left),
    AlgebraicGeometry.IsGlueingTwoPoints f.left a b →
    ConnectedComponents.mk (a.base (IsLocalRing.closedPoint k)) ≠
      ConnectedComponents.mk (b.base (IsLocalRing.closedPoint k)) →
    IsProper (Y.left ↘ Spec (.of k)) → IsProper (Y'.left ↘ Spec (.of k)) →
    topologicalKrullDim (Y.left : Type u) ≤ 1 →
    topologicalKrullDim (Y'.left : Type u) ≤ 1 →
    genus (Y.left ↘ Spec (.of k)) = genus (Y'.left ↘ Spec (.of k))

/-- **`h⁰` rises by exactly one when two rational points on different connected components of a
proper `X'` are glued.** This is the global-sections half of [Stacks, Tag 0C1J] as the source's
table uses it, and the one input the library was missing for the third line of that table.

Write `δ` for the functional `s ↦ s(a) - s(b)` on `Γ(X', 𝒪_{X'})`, the difference of the
evaluations at the two glued points.  It is `k`-linear, each evaluation being a ring homomorphism
which sends a constant section to its constant (`AlgebraicGeometry.sectionAt_constHom`).  Its
kernel is exactly the image of `Γ(X, 𝒪_X)`: a pullback from `X` has equal values at the two
points because they have the same image, and conversely a global function killed by `δ` descends
near the glued point by the descent clause of `AlgebraicGeometry.IsGlueingTwoPoints` and then
over all of `X` by `Stacks.GlueSquishFactor.exists_app_eq_of_le_sup`, the two opens `V` and
`{x}ᶜ` covering `X`.  It is surjective: by
`Stacks.GluePicard.exists_globalUnit_sectionAt_eq_of_ne_connectedComponents` — which is where the
two points lying on *different* components enters — each `c : kˣ` is the value at `a` of a global
unit whose value at `b` is `1`, so `c - 1` lies in the image, and `k` being infinite some such
`c - 1` is nonzero.
Rank-nullity for `δ` on the finite-dimensional `Γ(X', 𝒪_{X'})` ([Stacks, Tag 0BUG] (1)) then
reads `h⁰(X') = h⁰(X) + 1`, the image of `Γ(X, 𝒪_X)` having dimension `h⁰(X)` because `f` is
injective on sections (`Stacks.GlueSquishFactor.injective_app_of_isGlueingTwoPoints`). -/
theorem finrank_globalSections_eq_add_one_of_ne_connectedComponents {k : Type u} [Field k]
    [IsAlgClosed k] {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b) [IsProper (X' ↘ Spec (.of k))]
    (hab : ConnectedComponents.mk (a.base (IsLocalRing.closedPoint k)) ≠
      ConnectedComponents.mk (b.base (IsLocalRing.closedPoint k))) :
    letI : Algebra k Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop).hom.toAlgebra
    letI : Algebra k Γ(X', ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ X ↘ Spec (.of k)).appTop).hom.toAlgebra
    Module.finrank k Γ(X', ⊤) = Module.finrank k Γ(X, ⊤) + 1 := by
  classical
  obtain ⟨ha, hb, -, hfover, -, -, -, -, hab', hfin, ⟨U, hUset, hUiso⟩, -, hdesc, -⟩ := id h
  have := hfin
  have := hUiso
  let : Algebra k Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop).hom.toAlgebra
  let : Algebra k Γ(X', ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ X ↘ Spec (.of k)).appTop).hom.toAlgebra
  have hover : f ≫ (X ↘ Spec (.of k)) = X' ↘ Spec (.of k) := by
    simpa only [Scheme.Hom.isOver_iff] using hfover
  have hprop' : IsProper (f ≫ X ↘ Spec (.of k)) := by
    rw [hover]
    infer_instance
  have : Module.Finite k Γ(X', ⊤) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.moduleFinite_globalSections_of_isProper k
      (f ≫ X ↘ Spec (.of k))
  have hle : (⊤ : X'.Opens) ≤ (X' ↘ Spec (.of k)) ⁻¹ᵁ ⊤ := by simp
  have halg : ∀ c : k, algebraMap k Γ(X', ⊤) c = constHom X' ⊤ hle c := by
    intro c
    show ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ X ↘ Spec (.of k)).appTop).hom c = _
    rw [constHom_top X' hle c, hover]
  have hcomm : ∀ c : k, (f.appTop).hom (algebraMap k Γ(X, ⊤) c) = algebraMap k Γ(X', ⊤) c := by
    intro c
    show (f.appTop).hom (((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop).hom c) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫ f.appTop).hom c
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  -- evaluation at a rational point is additive and `k`-linear
  have hadd : ∀ (p : Spec (.of k) ⟶ X') (s t : Γ(X', ⊤)),
      AlgebraicGeometry.sectionAt p ⊤ (Opens.mem_top _) (s + t) =
        AlgebraicGeometry.sectionAt p ⊤ (Opens.mem_top _) s +
          AlgebraicGeometry.sectionAt p ⊤ (Opens.mem_top _) t :=
    fun p s t => map_add (AlgebraicGeometry.sectionAtHom p ⊤ (Opens.mem_top _)) s t
  have hsmul : ∀ (p : Spec (.of k) ⟶ X'),
      (∀ c : k, AlgebraicGeometry.sectionAt p ⊤ (Opens.mem_top _) (constHom X' ⊤ hle c) = c) →
      ∀ (c : k) (s : Γ(X', ⊤)),
      AlgebraicGeometry.sectionAt p ⊤ (Opens.mem_top _) (c • s) =
        c * AlgebraicGeometry.sectionAt p ⊤ (Opens.mem_top _) s := fun p hp c s => by
    have hmul : ∀ y z : Γ(X', ⊤), AlgebraicGeometry.sectionAt p ⊤ (Opens.mem_top _) (y * z) =
        AlgebraicGeometry.sectionAt p ⊤ (Opens.mem_top _) y *
          AlgebraicGeometry.sectionAt p ⊤ (Opens.mem_top _) z :=
      fun y z => map_mul (AlgebraicGeometry.sectionAtHom p ⊤ (Opens.mem_top _)) y z
    rw [Algebra.smul_def c s, hmul, halg c,
      hp c]
  -- the difference of the two evaluations, as a `k`-linear functional on global functions
  let δ : Γ(X', ⊤) →ₗ[k] k :=
    { toFun := fun s => AlgebraicGeometry.sectionAt a ⊤ (Opens.mem_top _) s -
        AlgebraicGeometry.sectionAt b ⊤ (Opens.mem_top _) s
      map_add' := fun s t => by
        show AlgebraicGeometry.sectionAt a ⊤ (Opens.mem_top _) (s + t) -
          AlgebraicGeometry.sectionAt b ⊤ (Opens.mem_top _) (s + t) = _
        rw [hadd a, hadd b]
        ring
      map_smul' := fun c s => by
        show AlgebraicGeometry.sectionAt a ⊤ (Opens.mem_top _) (c • s) -
            AlgebraicGeometry.sectionAt b ⊤ (Opens.mem_top _) (c • s) =
            c • (AlgebraicGeometry.sectionAt a ⊤ (Opens.mem_top _) s -
              AlgebraicGeometry.sectionAt b ⊤ (Opens.mem_top _) s)
        rw [hsmul a (AlgebraicGeometry.sectionAt_constHom a ha ⊤ (Opens.mem_top _) hle),
          hsmul b (AlgebraicGeometry.sectionAt_constHom b hb ⊤ (Opens.mem_top _) hle), smul_eq_mul]
        ring }
  -- pullback of global functions along `f`, as a `k`-linear map
  let ψ : Γ(X, ⊤) →ₗ[k] Γ(X', ⊤) :=
    { toFun := fun t => (f.appTop).hom t
      map_add' := fun s t => map_add (f.appTop).hom s t
      map_smul' := fun c t => by
        show (f.appTop).hom (c • t) = c • (f.appTop).hom t
        rw [Algebra.smul_def c t, Algebra.smul_def c ((f.appTop).hom t), map_mul, hcomm c] }
  have hinj : ∀ W : X.Opens, Function.Injective (f.app W).hom := fun W =>
    injective_app_of_isGlueingTwoPoints f a b h W
  have hψinj : Function.Injective ψ := fun s₁ s₂ hs => hinj ⊤ hs
  have hxtop : (a ≫ f).base (IsLocalRing.closedPoint k) ∈ (⊤ : X.Opens) := Opens.mem_top _
  have hxtopB : (b ≫ f).base (IsLocalRing.closedPoint k) ∈ (⊤ : X.Opens) := Opens.mem_top _
  have hker : LinearMap.ker δ = LinearMap.range ψ := by
    refine le_antisymm ?_ ?_
    · intro s hs
      have hs0 : AlgebraicGeometry.sectionAt a ⊤ (Opens.mem_top _) s -
          AlgebraicGeometry.sectionAt b ⊤ (Opens.mem_top _) s = 0 := LinearMap.mem_ker.mp hs
      obtain ⟨V, hVtop, hxV, t, hst⟩ := hdesc ⊤ hxtop s hs0
      have hcov : (⊤ : X.Opens) ≤ V ⊔ U := by
        intro y _
        by_cases hyx : y = (a ≫ f).base (IsLocalRing.closedPoint k)
        · exact Or.inl (hyx ▸ hxV)
        · refine Or.inr ?_
          show y ∈ (U : Set X)
          rw [hUset]
          exact hyx
      obtain ⟨r, hr⟩ :=
        exists_app_eq_of_le_sup f hinj hVtop (le_top (a := U)) hcov s t hst
      exact LinearMap.mem_range.mpr ⟨r, hr⟩
    · intro s hs
      obtain ⟨t, rfl⟩ := LinearMap.mem_range.mp hs
      refine LinearMap.mem_ker.mpr ?_
      have hval : AlgebraicGeometry.sectionAt a (f ⁻¹ᵁ (⊤ : X.Opens)) hxtop
            ((f.app (⊤ : X.Opens)).hom t) =
          AlgebraicGeometry.sectionAt b (f ⁻¹ᵁ (⊤ : X.Opens)) hxtopB
            ((f.app (⊤ : X.Opens)).hom t) :=
        (Stacks.GlueSquishUnits.sectionAt_pullback' f a ⊤ hxtop hxtop t).trans
          ((Stacks.GlueSquishUnits.sectionAt_congr' hab' ⊤ hxtop hxtopB t).trans
            (Stacks.GlueSquishUnits.sectionAt_pullback' f b ⊤ hxtopB hxtopB t).symm)
      show AlgebraicGeometry.sectionAt a (f ⁻¹ᵁ (⊤ : X.Opens)) hxtop
            ((f.app (⊤ : X.Opens)).hom t) -
          AlgebraicGeometry.sectionAt b (f ⁻¹ᵁ (⊤ : X.Opens)) hxtopB
            ((f.app (⊤ : X.Opens)).hom t) = 0
      rw [hval, sub_self]
  have hrange : LinearMap.range δ = ⊤ := by
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    obtain ⟨s₀, hs₀a, hs₀b⟩ :=
      Stacks.GluePicard.exists_globalUnit_sectionAt_eq_of_ne_connectedComponents f a b h hab
        (Units.mk0 c hc.1)
    have hδs₀ : δ (s₀ : Γ(X', ⊤)) = c - 1 := by
      show AlgebraicGeometry.sectionAt a ⊤ (Opens.mem_top _) (s₀ : Γ(X', ⊤)) -
        AlgebraicGeometry.sectionAt b ⊤ (Opens.mem_top _) (s₀ : Γ(X', ⊤)) = c - 1
      rw [hs₀a, hs₀b, Units.val_mk0]
    have hne : c - 1 ≠ 0 := sub_ne_zero_of_ne hc.2
    rw [LinearMap.range_eq_top]
    intro d
    refine ⟨(d / (c - 1)) • (s₀ : Γ(X', ⊤)), ?_⟩
    rw [map_smul, hδs₀, smul_eq_mul, div_mul_cancel₀ d hne]
  have hrk := LinearMap.finrank_range_add_finrank_ker δ
  rw [hrange, hker, finrank_top k k, Module.finrank_self,
    LinearMap.finrank_range_of_inj hψinj] at hrk
  omega

/-- **The genus is unchanged when two rational points on different connected components of a
proper `X'` are glued.** This is the third line of the source's table:
`Stacks.GlueSquishFactor.finrank_globalSections_eq_add_one_of_ne_connectedComponents` says that
`h⁰` rises by one,
`Stacks.GlueSquishFactor.finrank_cohomologyOverField_zero_cokernel_eq_one_of_isGlueingTwoPoints`
says that the cokernel `f_*𝒪_{X'}/𝒪_X` contributes one to the Euler characteristic, and the
Euler-characteristic bookkeeping of
`Stacks.GlueSquishFactor.finrank_globalSections_sub_genus_eq` turns the two into
`h¹(X) = h¹(X')`. -/
theorem genus_eq_of_isGlueingTwoPoints_of_ne_connectedComponents (k : Type u) [Field k]
    [IsAlgClosed k] {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b)
    [IsProper (X ↘ Spec (.of k))] [IsProper (X' ↘ Spec (.of k))]
    (hab : ConnectedComponents.mk (a.base (IsLocalRing.closedPoint k)) ≠
      ConnectedComponents.mk (b.base (IsLocalRing.closedPoint k)))
    (hdim : topologicalKrullDim X ≤ 1) (hdim' : topologicalKrullDim X' ≤ 1) :
    genus (X ↘ Spec (.of k)) = genus (f ≫ X ↘ Spec (.of k)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hfin, ⟨W, hWset, hWiso⟩, -, -, -⟩ := id h
  have := hfin
  have := hWiso
  have hinj : ∀ V : X.Opens, Function.Injective (f.app V).hom := fun V =>
    injective_app_of_isGlueingTwoPoints f a b h V
  have hmono := mono_hom_pushforwardAlgebra_of_injective_app f fun y => by
    obtain ⟨V, hV, hyV, -⟩ :=
      AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) (Opens.mem_top y)
    exact ⟨V, hV, hyV, hinj V⟩
  let : Algebra k Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop).hom.toAlgebra
  let : Algebra k Γ(X', ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ X ↘ Spec (.of k)).appTop).hom.toAlgebra
  have h1 : (Module.finrank k Γ(X', ⊤) : ℤ) - (genus (f ≫ X ↘ Spec (.of k)) : ℤ) =
      (Module.finrank k Γ(X, ⊤) : ℤ) - (genus (X ↘ Spec (.of k)) : ℤ) +
        (Module.finrank k (cohomologyOverField k (X ↘ Spec (.of k))
          (Limits.cokernel (structureUnitHom f)) 0) : ℤ) :=
    finrank_globalSections_sub_genus_eq k f (X ↘ Spec (.of k)) hmono hWset hdim hdim'
  have h2 : Module.finrank k (cohomologyOverField k (X ↘ Spec (.of k))
      (Limits.cokernel (structureUnitHom f)) 0) = 1 :=
    finrank_cohomologyOverField_zero_cokernel_eq_one_of_isGlueingTwoPoints f a b h
  have h3 : Module.finrank k Γ(X', ⊤) = Module.finrank k Γ(X, ⊤) + 1 :=
    finrank_globalSections_eq_add_one_of_ne_connectedComponents f a b h hab
  rw [h2, h3] at h1
  omega

/-- **`Stacks.GlueSquishFactor.GlueingGenusInvariance` holds**: a glueing of two rational points
lying on different connected components of a proper source leaves the genus unchanged. This is
`Stacks.GlueSquishFactor.genus_eq_of_isGlueingTwoPoints_of_ne_connectedComponents` read on a
morphism of objects over `Spec k`, where the structure morphism of the source is the composite of
the morphism with that of the target. -/
theorem glueingGenusInvariance (k : Type u) [Field k] [IsAlgClosed k] :
    GlueingGenusInvariance k := by
  intro Y' Y f a b hg hab hprop hpropsrc hdim hdim'
  have := hprop
  have := hpropsrc
  have hw : f.left ≫ (Y.left ↘ Spec (.of k)) = Y'.left ↘ Spec (.of k) := Over.w f
  have hres := genus_eq_of_isGlueingTwoPoints_of_ne_connectedComponents (X' := Y'.left)
    (X := Y.left) k f.left a b hg hab hdim hdim'
  rw [hw] at hres
  exact hres

/-! ### One elementary step -/

/-- A glueing of two points changes `dim_{F_ℓ} Pic[ℓ]` and the genus by the same amount: `1` on a
single connected component and `0` across two. -/
private theorem exists_rank_torsionBy_picard_genus_of_isGlueingTwoPoints {k : Type u} [Field k]
    [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    {Y' Y : Over (Spec (.of k))} (f : Y' ⟶ Y) (a b : Spec (.of k) ⟶ Y'.left)
    (hg : AlgebraicGeometry.IsGlueingTwoPoints f.left a b)
    (hprop : IsProper (Y.left ↘ Spec (.of k)))
    (hdim : topologicalKrullDim (Y.left : Type u) ≤ 1) :
    ∃ n : ℕ,
      Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y.left) (ℓ : ℤ)) =
        (n : Cardinal.{u + 1}) +
          Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y'.left) (ℓ : ℤ)) ∧
      genus (Y.left ↘ Spec (.of k)) = n + genus (Y'.left ↘ Spec (.of k)) := by
  have := hprop
  have hstep : IsElementaryStep f := Or.inl ⟨a, b, hg⟩
  have hfin : IsFinite f.left := hstep.isFinite
  have hpropsrc : IsProper (Y'.left ↘ Spec (.of k)) := hstep.isProper_source
  have hdim' : topologicalKrullDim (Y'.left : Type u) ≤ 1 :=
    (topologicalKrullDim_le_of_isIntegralHom f.left).trans hdim
  have hw : f.left ≫ (Y.left ↘ Spec (.of k)) = Y'.left ↘ Spec (.of k) := Over.w f
  by_cases hab : ConnectedComponents.mk (a.base (IsLocalRing.closedPoint k)) =
    ConnectedComponents.mk (b.base (IsLocalRing.closedPoint k))
  · refine ⟨1, ?_, ?_⟩
    · rw [Nat.cast_one]
      exact Stacks.PicardTorsionStep.rank_torsionBy_picard_eq_one_add_of_connectedComponents_eq
        (X' := Y'.left) (X := Y.left) ℓ hℓ f.left a b hg hab
    · have h := genus_eq_add_one_of_isGlueingTwoPoints (X' := Y'.left) (X := Y.left) k
        f.left a b hg hab hdim hdim'
      rw [hw] at h
      omega
  · refine ⟨0, ?_, ?_⟩
    · rw [Nat.cast_zero, zero_add]
      exact Stacks.PicardTorsionStep.rank_torsionBy_picard_eq_of_ne_connectedComponents
        (X' := Y'.left) (X := Y.left) ℓ f.left a b hg hab
    · have h := glueingGenusInvariance k f a b hg hab hprop hpropsrc hdim hdim'
      omega

/-- **The two invariants across one elementary modification.** For a step `f : Y' ⟶ Y` with `Y`
proper over `k` of dimension at most one and `Y'` reduced, there are `n ≤ m` with

`dim_{F_ℓ} Pic(Y)[ℓ] = n + dim_{F_ℓ} Pic(Y')[ℓ]` and `h¹(Y) = m + h¹(Y')`,

and `n = m` holds for a glueing while `n < m` holds for a squishing. These are the three lines of
the source's table: `(n, m) = (0, 0)` for a glueing of two points on different connected
components, `(1, 1)` for a glueing of two points on the same connected component, and `(0, 1)`
for a squishing of a tangent vector. -/
theorem exists_rank_torsionBy_picard_genus_of_isElementaryStep {k : Type u} [Field k]
    [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    {Y' Y : Over (Spec (.of k))} {f : Y' ⟶ Y} (hf : IsElementaryStep f)
    (hprop : IsProper (Y.left ↘ Spec (.of k))) (hred : IsReduced Y'.left)
    (hdim : topologicalKrullDim (Y.left : Type u) ≤ 1) :
    ∃ n m : ℕ, n ≤ m ∧
      Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y.left) (ℓ : ℤ)) =
        (n : Cardinal.{u + 1}) +
          Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y'.left) (ℓ : ℤ)) ∧
      genus (Y.left ↘ Spec (.of k)) = m + genus (Y'.left ↘ Spec (.of k)) ∧
      ((IsGlueingChain k f ∧ n = m) ∨ n < m) := by
  have := hprop
  have := hred
  have hfin := hf.isFinite
  have hpropsrc : IsProper (Y'.left ↘ Spec (.of k)) := hf.isProper_source
  have hdim' : topologicalKrullDim (Y'.left : Type u) ≤ 1 :=
    (topologicalKrullDim_le_of_isIntegralHom f.left).trans hdim
  have hw : f.left ≫ (Y.left ↘ Spec (.of k)) = Y'.left ↘ Spec (.of k) := Over.w f
  rcases hf with ⟨a, b, hg⟩ | ⟨θ, hs⟩
  · obtain ⟨n, hr, hgn⟩ :=
      exists_rank_torsionBy_picard_genus_of_isGlueingTwoPoints ℓ hℓ f a b hg hprop hdim
    exact ⟨n, n, le_rfl, hr, hgn, Or.inl ⟨.of_glueing f a b hg, rfl⟩⟩
  · refine ⟨0, 1, Nat.zero_le 1, ?_, ?_, Or.inr Nat.zero_lt_one⟩
    · rw [Nat.cast_zero, zero_add]
      exact Stacks.PicardTorsionStep.rank_torsionBy_picard_eq_of_isSquishingTangentVector
        (X' := Y'.left) (X := Y.left) ℓ hℓ f.left θ hs
    · have h := genus_eq_add_one_of_isSquishingTangentVector (X' := Y'.left) (X := Y.left) k
        f.left θ hs hdim hdim'
      rw [hw] at h
      omega

/-! ### Isomorphisms -/

/-- Pullback along an isomorphism `g : Y' ⟶ Y` shows that the `ℓ`-torsion of the Picard group of
`Y'` has dimension at most that of `Y`. -/
private theorem rank_torsionBy_picard_le_of_isIso {k : Type u} [Field k] [IsAlgClosed k] (ℓ : ℕ)
    [Fact ℓ.Prime] {Y' Y : Over (Spec (.of k))} (g : Y' ⟶ Y) [IsIso g] :
    Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y'.left) (ℓ : ℤ)) ≤
      Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y.left) (ℓ : ℤ)) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  refine LinearMap.rank_le_of_surjective
    (Stacks.EllTorsion.toZModLinearMap (ℓ := ℓ)
      (Stacks.EllTorsion.restrict ℓ
        (Stacks.Picard.schemePullbackClassHom ((Over.forget (Spec (.of k))).map g) :
          ofScheme Y.left →+ ofScheme Y'.left))) ?_
  simpa only [Stacks.EllTorsion.coe_toZModLinearMap] using
    Stacks.PicardTorsionStep.surjective_restrict_picardPullback_of_isIso ℓ g

/-- The dimension of the `ℓ`-torsion of the Picard group is unchanged by an isomorphism:
pullback along an isomorphism is surjective on `ℓ`-torsion in both directions. -/
theorem rank_torsionBy_picard_eq_of_isIso {k : Type u} [Field k] [IsAlgClosed k] (ℓ : ℕ)
    [Fact ℓ.Prime] {Y' Y : Over (Spec (.of k))} (g : Y' ⟶ Y) [IsIso g] :
    Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y.left) (ℓ : ℤ)) =
      Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y'.left) (ℓ : ℤ)) :=
  le_antisymm (rank_torsionBy_picard_le_of_isIso ℓ (inv g)) (rank_torsionBy_picard_le_of_isIso ℓ g)

/-- The genus is unchanged by an isomorphism of objects over `Spec k`. -/
theorem genus_eq_of_isIso {k : Type u} [Field k] {Y' Y : Over (Spec (.of k))} (g : Y' ⟶ Y)
    [IsIso g] (hprop : IsProper (Y.left ↘ Spec (.of k))) :
    genus (Y.left ↘ Spec (.of k)) = genus (Y'.left ↘ Spec (.of k)) := by
  have := hprop
  have hw : g.left ≫ (Y.left ↘ Spec (.of k)) = Y'.left ↘ Spec (.of k) := Over.w g
  have h := genus_comp_iso_eq k (Y.left ↘ Spec (.of k))
    (asIso ((Over.forget (Spec (.of k))).map g))
  rw [← hw]
  exact h.symm

/-! ### The whole chain -/

/-- **The bookkeeping of [Stacks, Tag 0C20] along a chain of elementary modifications.** For a
chain `f : Y' ⟶ Y` with `Y` proper over `k` of dimension at most one and `Y'` reduced there are
`n ≤ m` with

`dim_{F_ℓ} Pic(Y)[ℓ] = n + dim_{F_ℓ} Pic(Y')[ℓ]` and `h¹(Y) = m + h¹(Y')`,

and `n = m` only if the chain is a chain of glueings. The induction is the source's: each step
contributes one line of the table, properness travels from the target of a chain to its source,
reducedness from the source to the target, and the dimension bound from the target to the source
because an elementary modification is finite. -/
theorem exists_rank_torsionBy_picard_genus_of_isElementaryChain {k : Type u} [Field k]
    [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    {Y' Y : Over (Spec (.of k))} {f : Y' ⟶ Y} (hf : IsElementaryChain k f) :
    IsProper (Y.left ↘ Spec (.of k)) → IsReduced Y'.left →
      topologicalKrullDim (Y.left : Type u) ≤ 1 →
      ∃ n m : ℕ, n ≤ m ∧
        Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y.left) (ℓ : ℤ)) =
          (n : Cardinal.{u + 1}) +
            Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y'.left) (ℓ : ℤ)) ∧
        genus (Y.left ↘ Spec (.of k)) = m + genus (Y'.left ↘ Spec (.of k)) ∧
        ((IsGlueingChain k f ∧ n = m) ∨ n < m) := by
  induction hf with
  | @of_isIso A B g hg =>
    intro hprop _ _
    have := hg
    exact ⟨0, 0, le_rfl, by
      rw [Nat.cast_zero, zero_add]
      exact rank_torsionBy_picard_eq_of_isIso ℓ g, by
      rw [Nat.zero_add]
      exact genus_eq_of_isIso g hprop, Or.inl ⟨.of_isIso g hg, rfl⟩⟩
  | of_step g hg =>
    intro hprop hred hdim
    exact exists_rank_torsionBy_picard_genus_of_isElementaryStep ℓ hℓ hg hprop hred hdim
  | @comp C B A g p hg hp ihg ihp =>
    intro hprop hred hdim
    have hpropB : IsProper (B.left ↘ Spec (.of k)) := by
      have := hprop
      exact hp.isProper_source
    have hredB : IsReduced B.left := hg.isReduced_target hred
    have hdimB : topologicalKrullDim (B.left : Type u) ≤ 1 :=
      hp.topologicalKrullDim_source_le.trans hdim
    obtain ⟨n₂, m₂, hnm₂, hr₂, hg₂, hd₂⟩ := ihp hprop hredB hdim
    obtain ⟨n₁, m₁, hnm₁, hr₁, hg₁, hd₁⟩ := ihg hpropB hred hdimB
    refine ⟨n₂ + n₁, m₂ + m₁, by omega, ?_, ?_, ?_⟩
    · rw [hr₂, hr₁, Nat.cast_add]
      rw [add_assoc]
    · rw [hg₂, hg₁]
      omega
    · rcases hd₂ with ⟨hc₂, he₂⟩ | hlt₂
      · rcases hd₁ with ⟨hc₁, he₁⟩ | hlt₁
        · exact Or.inl ⟨.comp hc₁ hc₂, by omega⟩
        · exact Or.inr (by omega)
      · exact Or.inr (by omega)

/-- **Along a chain of glueings the two jumps are equal.** This is the equality case of the
bookkeeping: both kinds of glueing contribute the same amount to `dim_{F_ℓ} Pic[ℓ]` and to the
genus, so the two invariants move in step. -/
theorem exists_rank_torsionBy_picard_genus_of_isGlueingChain {k : Type u} [Field k]
    [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    {Y' Y : Over (Spec (.of k))} {f : Y' ⟶ Y} (hf : IsGlueingChain k f) :
    IsProper (Y.left ↘ Spec (.of k)) →
      topologicalKrullDim (Y.left : Type u) ≤ 1 →
      ∃ n : ℕ,
        Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y.left) (ℓ : ℤ)) =
          (n : Cardinal.{u + 1}) +
            Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y'.left) (ℓ : ℤ)) ∧
        genus (Y.left ↘ Spec (.of k)) = n + genus (Y'.left ↘ Spec (.of k)) := by
  induction hf with
  | @of_isIso A B g hg =>
    intro hprop _
    have := hg
    exact ⟨0, by
      rw [Nat.cast_zero, zero_add]
      exact rank_torsionBy_picard_eq_of_isIso ℓ g, by
      rw [Nat.zero_add]
      exact genus_eq_of_isIso g hprop⟩
  | @of_glueing A B g a b hgl =>
    intro hprop hdim
    exact exists_rank_torsionBy_picard_genus_of_isGlueingTwoPoints ℓ hℓ g a b hgl hprop hdim
  | @comp C B A g p hg hp ihg ihp =>
    intro hprop hdim
    have hpropB : IsProper (B.left ↘ Spec (.of k)) := by
      have := hprop
      exact hp.isElementaryChain.isProper_source
    have hdimB : topologicalKrullDim (B.left : Type u) ≤ 1 :=
      hp.isElementaryChain.topologicalKrullDim_source_le.trans hdim
    obtain ⟨n₂, hr₂, hg₂⟩ := ihp hprop hdim
    obtain ⟨n₁, hr₁, hg₁⟩ := ihg hpropB hdimB
    refine ⟨n₂ + n₁, ?_, ?_⟩
    · rw [hr₂, hr₁, Nat.cast_add, add_assoc]
    · rw [hg₂, hg₁]
      omega

end Stacks.GlueSquishFactor

namespace AlgebraicGeometry

attribute [local instance] AddSubgroup.torsionBy.zmodModule

open Stacks.GlueSquishFactor

/-! ### The genus of the normalization is the geometric genus -/

/-- In `WithBot ℕ∞` nothing lies strictly between `0` and `1`. -/
private theorem le_zero_of_lt_one {a : WithBot ℕ∞} (h : a < 1) : a ≤ 0 := by
  rw [← WithBot.coe_one] at h
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    rw [← WithBot.coe_zero]
    exact WithBot.coe_le_coe.mpr (Order.lt_one_iff.mp (WithBot.coe_lt_coe.mp h)).le

/-- **`h¹(X^ν) = g_geom`: the genus of the normalization is the geometric genus.** For a reduced
proper scheme of dimension at most one over an algebraically closed field the inequality
`AlgebraicGeometry.geometricGenus_le_genus_normalizationOverField` is an equality.

Both sides are sums over the irreducible components — the left by [Stacks, Tag 0CDV] and the
additivity of the genus over a disjoint union
(`AlgebraicGeometry.genus_normalizationOverField_eq_sum_components`), the right by the definition
of the geometric genus (`AlgebraicGeometry.geometricGenus_eq_sum_all_components`) — and the two
summands agree componentwise: on a component of dimension one by
`AlgebraicGeometry.geometricGenus_eq_ite_genus_normalizationOverField`, and on a component of
dimension zero because both are then zero, the normalization of such a component again having
dimension zero.  This upgrades the inequality to an equality. -/
theorem genus_normalizationOverField_eq_geometricGenus (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p] [IsReduced X]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    genus (normalizationOverField k p ≫ p) = geometricGenus k p := by
  classical
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian p
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace p }
  have : Finite (irreducibleComponents X) :=
    (finite_irreducibleComponents_of_isNoetherian (X := X)).to_subtype
  let : Fintype (irreducibleComponents X) := Fintype.ofFinite _
  rw [geometricGenus_eq_sum_all_components p, genus_normalizationOverField_eq_sum_components k p]
  refine Finset.sum_congr rfl fun W _ ↦ ?_
  have hirr : IrreducibleSpace (irreducibleComponentIdeal W).subscheme := by
    apply Scheme.IdealSheafData.irreducibleSpace_subscheme
    rw [Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
    exact W.2.1
  have hdimW : topologicalKrullDim ((irreducibleComponentIdeal W).subscheme : Type u) ≤ 1 :=
    le_trans (irreducibleComponentIdeal
      W).subschemeι.isClosedEmbedding.isInducing.topologicalKrullDim_le hdim
  rw [geometricGenus_eq_ite_genus_normalizationOverField k
    ((irreducibleComponentIdeal W).subschemeι ≫ p) hdimW]
  by_cases h1 : topologicalKrullDim ((irreducibleComponentIdeal W).subscheme : Type u) = 1
  · rw [ite_eq_left h1]
  · rw [ite_eq_right h1]
    have hfin := isFinite_normalizationOverField k ((irreducibleComponentIdeal W).subschemeι ≫ p)
    have hprop := isProper_normalizationOverField_comp k
      ((irreducibleComponentIdeal W).subschemeι ≫ p)
    exact genus_eq_zero_of_topologicalKrullDim_le_zero k _
      ((topologicalKrullDim_le_of_isIntegralHom
        (normalizationOverField k ((irreducibleComponentIdeal W).subschemeι ≫ p))).trans
        (le_zero_of_lt_one (lt_of_le_of_ne hdimW h1)))

/-- **The bookkeeping of [Stacks, Tag 0C20] read along the normalization.** The factorization of
[Stacks, Tag 0C1L] applied to `ν : X^ν ⟶ X` and
`Stacks.GlueSquishFactor.exists_rank_torsionBy_picard_genus_of_isElementaryChain`, with both ends
spelled in terms of `X` and its normalization: there are `n ≤ m` with

`dim_{F_ℓ} Pic(X)[ℓ] = n + dim_{F_ℓ} Pic(X^ν)[ℓ]` and `h¹(X) = m + h¹(X^ν)`,

and `n = m` only if `ν` factors with no squishing of a tangent vector. -/
theorem exists_rank_picardTorsion_genus_normalization (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] [IsReduced X]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : k) ≠ 0) :
    ∃ n m : ℕ, n ≤ m ∧
      Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) =
        (n : Cardinal.{u + 1}) + Module.rank (ZMod ℓ) (AddSubgroup.torsionBy
          (ofScheme (normalizationSchemeOverField k (X ↘ Spec (.of k)))) (ℓ : ℤ)) ∧
      genus (X ↘ Spec (.of k)) =
        m + genus (normalizationOverField k (X ↘ Spec (.of k)) ≫ (X ↘ Spec (.of k))) ∧
      ((IsGlueingChain k (normalizationOver k X) ∧ n = m) ∨ n < m) := by
  have hredν : IsReduced (normalizationSchemeOverField k (X ↘ Spec (.of k))) :=
    Scheme.isReduced_normalizationScheme X
      (finite_irreducibleComponents_of_locallyOfFiniteType k (X ↘ Spec (.of k)))
  exact exists_rank_torsionBy_picard_genus_of_isElementaryChain ℓ hℓ
    (isElementaryChain_normalizationOverField k (X ↘ Spec (.of k)) hdim)
    ‹IsProper (X ↘ Spec (.of k))› hredν hdim

/-- **The equality case of the bookkeeping read along the normalization**: if `ν` factors as a
chain of glueings with no squishing, the two jumps coincide. -/
theorem exists_rank_picardTorsion_genus_normalization_of_isGlueingChain (k : Type u) [Field k]
    [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [IsReduced X] (hdim : topologicalKrullDim (X : Type u) ≤ 1) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : k) ≠ 0)
    (hchain : IsGlueingChain k (normalizationOver k X)) :
    ∃ n : ℕ,
      Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) =
        (n : Cardinal.{u + 1}) + Module.rank (ZMod ℓ) (AddSubgroup.torsionBy
          (ofScheme (normalizationSchemeOverField k (X ↘ Spec (.of k)))) (ℓ : ℤ)) ∧
      genus (X ↘ Spec (.of k)) =
        n + genus (normalizationOverField k (X ↘ Spec (.of k)) ≫ (X ↘ Spec (.of k))) :=
  exists_rank_torsionBy_picard_genus_of_isGlueingChain ℓ hℓ hchain
    ‹IsProper (X ↘ Spec (.of k))› hdim

/-- A vector space whose rank is a sum of two natural numbers is finite-dimensional, of that
finrank. -/
private theorem finiteDimensional_and_finrank_eq_of_rank_eq_add {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] {n c : ℕ}
    (h : Module.rank K V = (n : Cardinal) + (c : Cardinal)) :
    FiniteDimensional K V ∧ Module.finrank K V = n + c := by
  have hrank : Module.rank K V = ((n + c : ℕ) : Cardinal) := by rw [h, Nat.cast_add]
  exact ⟨Module.rank_lt_aleph0_iff.mp (hrank ▸ Cardinal.natCast_lt_aleph0),
    Module.finrank_eq_of_rank_eq hrank⟩

/-- **Stacks Project, Tag 0C20, the bound.**

Let `k` be an algebraically closed field, let `X` be a proper scheme over `k` which is reduced and
of dimension one, let `g = h¹(X, 𝒪_X)` be its genus and let `g_geom` be the sum of the geometric
genera of its irreducible components, and let `ℓ` be a prime different from the characteristic of
`k`.  Then the `ℓ`-torsion of `Pic(X)` is finite-dimensional over `F_ℓ` and

`dim_{F_ℓ} Pic(X)[ℓ] ≤ g + g_geom`.

Connectedness, which the source assumes, is not needed; the source's statement is the special
case `[ConnectedSpace X]`.

The proof is the source's: the normalization is factored by [Stacks, Tag 0C1L], the two
invariants are compared along the factorization by the three lines of the source's table, and at
the far end `h¹(X^ν) = g_geom`
(`AlgebraicGeometry.genus_normalizationOverField_eq_geometricGenus`) and
`dim_{F_ℓ} Pic(X^ν)[ℓ] = 2 g_geom`, the latter from clause (1) of [Stacks, Tag 0C1Z]
(`Stacks.Picard.nonempty_torsionBy_addEquiv_pi_zmod_of_smoothProjectiveCurve`) by
`AlgebraicGeometry.rank_picardTorsion_normalizationSchemeOverField_eq_two_mul_geometricGenus`. -/
@[stacks 0C20 "the bound dim Pic(X)[l] ≤ g + g_geom (connectedness not needed)"]
theorem finrank_picardTorsion_le_genus_add_geometricGenus_of_isReduced_dim_one (k : Type u)
    [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] [IsReduced X]
    (hdim : topologicalKrullDim (X : Type u) = 1) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) :
    FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ∧
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ≤
        genus (X ↘ Spec (.of k)) + geometricGenus k (X ↘ Spec (.of k)) := by
  have hnorm := rank_picardTorsion_normalizationSchemeOverField_eq_two_mul_geometricGenus k
    (X ↘ Spec (.of k)) hdim.le ℓ (isUnit_iff_ne_zero.mpr hℓ)
    fun C c _ _ _ hu => Stacks.Picard.nonempty_torsionBy_addEquiv_pi_zmod_of_smoothProjectiveCurve
      k c ℓ (Fact.out : ℓ.Prime).one_lt.le hu
  obtain ⟨n, m, hnm, hr, hgen, -⟩ :=
    exists_rank_picardTorsion_genus_normalization k X hdim.le ℓ hℓ
  rw [hnorm] at hr
  obtain ⟨hfd, hfr⟩ := finiteDimensional_and_finrank_eq_of_rank_eq_add hr
  refine ⟨hfd, ?_⟩
  rw [genus_normalizationOverField_eq_geometricGenus k (X ↘ Spec (.of k)) hdim.le] at hgen
  omega

/-- **Stacks Project, Tag 0C20, the equality criterion.**

In the situation of the bound
`AlgebraicGeometry.finrank_picardTorsion_le_genus_add_geometricGenus_of_isReduced_dim_one`, the
`ℓ`-torsion of `Pic(X)` is finite-dimensional over `F_ℓ`, and equality
`dim_{F_ℓ} Pic(X)[ℓ] = g + g_geom` holds if and only if every singularity of `X` is multicross.

Equality holds exactly when the factorization of the normalization contains no squishing, in
both directions — the forward direction from the strict drop a squishing causes, the backward
direction from the equality case of the arithmetic along a glueing chain — and the
factorization contains no squishing exactly when every singularity of `X` is multicross
(`Stacks.Curves.isGlueingChain_normalizationOver_iff_forall_isMulticrossSingularity`, the step
the source leaves out: "just glue the local sequences for each point to find one that works for
all singular points"). -/
@[stacks 0C20 "the equality criterion: equality iff all singularities are multicross"]
theorem finrank_picardTorsion_eq_iff_forall_isMulticrossSingularity_of_isReduced_dim_one
    (k : Type u) [Field k]
    [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [IsReduced X] (hdim : topologicalKrullDim (X : Type u) = 1) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : k) ≠ 0) :
    FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ∧
      (Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) =
        genus (X ↘ Spec (.of k)) + geometricGenus k (X ↘ Spec (.of k)) ↔
      ∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) →
        Stacks.Curves.IsMulticrossSingularity k X x) := by
  refine ⟨(finrank_picardTorsion_le_genus_add_geometricGenus_of_isReduced_dim_one k X hdim ℓ
    hℓ).1, ?_⟩
  have hnorm := rank_picardTorsion_normalizationSchemeOverField_eq_two_mul_geometricGenus k
    (X ↘ Spec (.of k)) hdim.le ℓ (isUnit_iff_ne_zero.mpr hℓ)
    fun C c _ _ _ hu => Stacks.Picard.nonempty_torsionBy_addEquiv_pi_zmod_of_smoothProjectiveCurve
      k c ℓ (Fact.out : ℓ.Prime).one_lt.le hu
  obtain ⟨n, m, hnm, hr, hgen, hdisj⟩ :=
    exists_rank_picardTorsion_genus_normalization k X hdim.le ℓ hℓ
  rw [hnorm] at hr
  rw [genus_normalizationOverField_eq_geometricGenus k (X ↘ Spec (.of k)) hdim.le]
    at hgen
  have hfr := (finiteDimensional_and_finrank_eq_of_rank_eq_add hr).2
  rw [hfr, hgen]
  have hiff := Stacks.Curves.isGlueingChain_normalizationOver_iff_forall_isMulticrossSingularity
    k X hdim.le
  refine ⟨fun heq => hiff.mp ?_, fun hall => ?_⟩
  · rcases hdisj with ⟨hc, -⟩ | hlt
    · exact hc
    · omega
  · obtain ⟨n', hr', hgen'⟩ :=
      exists_rank_picardTorsion_genus_normalization_of_isGlueingChain k X hdim.le ℓ hℓ
        (hiff.mpr hall)
    rw [hnorm] at hr'
    rw [genus_normalizationOverField_eq_geometricGenus k (X ↘ Spec (.of k)) hdim.le]
      at hgen'
    have hfr' := (finiteDimensional_and_finrank_eq_of_rank_eq_add hr').2
    omega

end AlgebraicGeometry

end
