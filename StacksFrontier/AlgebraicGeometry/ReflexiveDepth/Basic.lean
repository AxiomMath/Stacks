module

public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.DualStalk
public import StacksFrontier.AlgebraicGeometry.ReflexiveExtend.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.Depth
public import StacksFrontier.AlgebraicGeometry.Properties.Serre
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.Depth

/-!
# The stalk of a reflexive module has depth at least two where the local ring does

Let `X` be a locally Noetherian scheme and let `F` be an `𝒪_X`-module which is reflexive, in the
sense that the canonical map `F ⟶ F^∨∨` is an isomorphism.  If the dual `F^∨` is of finite
presentation, then at every point `x` the stalk `F_x` is the `𝒪_{X,x}`-dual of the stalk of
`F^∨`, so Tag 0AV5 bounds its depth below by the depth of the local ring.  That is
[Stacks, Tag 0EBI](https://stacks.math.columbia.edu/tag/0EBI) part (1).

## Method, and why it does not go through Tag 0AY3

The Stacks Project's proof of Tag 0EBI part (1) obtains the
*module-theoretic* reflexivity of the stalk from [Stacks, Tag
0AY3](https://stacks.math.columbia.edu/tag/0AY3) and then moves the depth bound across
`Module.evalEquiv`.  That route needs the compatibility of the stalk of `toDoubleDual F` with
the algebraic evaluation map `M ⟶ M^**`, which is a genuinely expensive diagram.

It is not needed.  Tag 0AV5 (`one_le_depth_and_two_le_depth_linearMap`) bounds the depth of
*any* module of linear maps into the local ring, so it is enough to exhibit `F_x` as **some**
`𝒪_{X,x}`-dual, and reflexivity of `F` does that directly: the stalk of an isomorphism is a
linear equivalence, and Tag 01CP (`dualStalkEquiv`) identifies the stalk of `F^∨∨ = (F^∨)^∨`
with the dual of the stalk of `F^∨`.  No compatibility square intervenes, `Module.IsReflexive`
is never mentioned, and Tag 0AY3 is not used at all.

Consequently the hypotheses are also weaker than the source's: neither coherence of `F` nor
integrality of `X` is used, and the only input beyond reflexivity is finite presentation of the
dual.

## The one hypothesis, stated as an instance binder

`[(dualSheaf F).IsFinitePresentation]` **is** the whole residue, and it is Tag 01Y2 at
`𝒢 = 𝒪_X` — coherence of the dual of a coherent module — composed with Tag 01BW.  It is the
same single input that
`isReflexive_dualSheaf_of_isCoherent` and
`isCoherent_dualSheaf_of_hasLocalKernelPresentation` already isolate, and it is
itself gated on the first assertion of Tag 01CQ.  It is written as an instance binder so that
these statements become unconditional, with no edit to them or to their call sites, the moment
that input lands.

## Main definitions

* `stalkEquivOfIsIso f x`: the linear equivalence of stalks induced by an isomorphism of
  `𝒪_X`-modules.
* `modStalkEquivDualOfIsReflexive F hF x`: for `F` reflexive with `F^∨` of finite presentation,
  the identification of `F_x` with the `𝒪_{X,x}`-dual of the stalk of `F^∨`.

## Main results

* `two_le_depth_stalk_of_isReflexive` and `one_le_depth_stalk_of_isReflexive`: the depth bounds,
  in the form Tag 0EBI part (1) states.
* `sheafHasPropertySk_two_of_isReflexive_of_isFinitePresentation_dualSheaf`: Serre's condition
  `(S₂)` for the module, which is Tag 0EBI part (2), stated with the library's
  `AlgebraicGeometry.SheafHasPropertySk` and `AlgebraicGeometry.HasPropertySk`.  It drops the
  coherence of `F` that `sheafHasPropertySk_two_of_isReflexive` assumes, asking only that the
  dual be of finite presentation.
* `reflexiveCoherentEquivalenceOfCoherentDual`: the statement of Tag 0EBJ with the stalk-depth
  hypothesis of `reflexiveCoherentEquivalenceOfPreservation` discharged, so that only Tag 0EBF
  clause (2) and the direct-image extension step remain, together with the finite presentation
  of the dual.

## References

* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 0AV5](https://stacks.math.columbia.edu/tag/0AV5)
* [Stacks Project, Tag 0EBI](https://stacks.math.columbia.edu/tag/0EBI)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

open Stacks.SheafOfModules.SheafHomStalk

variable {X : Scheme.{u}}

/-! ### Stalks of an isomorphism -/

/-- The linear equivalence of stalks induced by an isomorphism of `𝒪_X`-modules.  Its two
components are the stalk maps of the morphism and of its inverse. -/
public noncomputable def stalkEquivOfIsIso {F G : X.Modules} (f : F ⟶ G) [IsIso f] (x : X) :
    modStalk F x ≃ₗ[ringStalk X.sheaf x] modStalk G x :=
  LinearEquiv.ofLinearMap (stalkHom f x) (stalkHom (inv f) x)
    (by rw [← stalkHom_comp, IsIso.inv_hom_id, stalkHom_id])
    (by rw [← stalkHom_comp, IsIso.hom_inv_id, stalkHom_id])

/-- The underlying map of `stalkEquivOfIsIso f x` is `stalkHom f x`. -/
@[simp]
public theorem stalkEquivOfIsIso_apply {F G : X.Modules} (f : F ⟶ G) [IsIso f] (x : X)
    (m : modStalk F x) : stalkEquivOfIsIso f x m = stalkHom f x m :=
  rfl

/-! ### The stalk of a reflexive module is a dual -/

/-- **For a reflexive module whose dual is of finite presentation, the stalk is the
`𝒪_{X,x}`-dual of the stalk of the dual.**

The canonical map `F ⟶ F^∨∨` is an isomorphism, so it induces a linear equivalence on stalks;
Tag 01CP applied to `F^∨` identifies the stalk of `F^∨∨` with the dual of the stalk of `F^∨`.

`dualStalkEquiv` is stated at the `X.presheaf.stalk x` spelling of the local ring, while
`stalkEquivOfIsIso` and the statement above use the `ringStalk X.sheaf x` spelling.  The two are
definitionally equal, but `LinearEquiv.trans` resolves `RingHomCompTriple` at reducible
transparency and so cannot mix them; ascribing the second equivalence at the `ringStalk` spelling
before composing keeps both sides on one `Semiring` instance. -/
public noncomputable def modStalkEquivDualOfIsReflexive (F : X.Modules)
    [(dualSheaf F).IsFinitePresentation] (hF : IsReflexive F) (x : X) :
    modStalk F x ≃ₗ[ringStalk X.sheaf x]
      (modStalk (dualSheaf F) x →ₗ[ringStalk X.sheaf x] ringStalk X.sheaf x) :=
  haveI : IsIso (toDoubleDual F) := hF
  let d : modStalk (dualSheaf (dualSheaf F)) x ≃ₗ[ringStalk X.sheaf x]
      (modStalk (dualSheaf F) x →ₗ[ringStalk X.sheaf x] ringStalk X.sheaf x) :=
    dualStalkEquiv (dualSheaf F) x
  (stalkEquivOfIsIso (toDoubleDual F) x).trans d

/-- Both halves of Tag 0AV5 for the stalk of a reflexive module, at the spelling of the stalk
that carries the module structure found by instance search.

The local-ring instance is taken as a *parameter* rather than synthesized: the statement does
not elaborate at this spelling of the local ring otherwise, and the two public forms below
supply the instance after rewriting the ring to `X.presheaf.stalk x`. -/
private theorem depth_stalk_bound_of_isReflexive (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F : X.Modules) [(dualSheaf F).IsFinitePresentation] (hF : IsReflexive F) (x : X)
    [IsLocalRing (ringStalk X.sheaf x)] :
    ((1 : ℕ∞) ≤ Module.depth (ringStalk X.sheaf x)
        (IsLocalRing.maximalIdeal (ringStalk X.sheaf x)) (ringStalk X.sheaf x) →
      (1 : ℕ∞) ≤ Module.depth (ringStalk X.sheaf x)
        (IsLocalRing.maximalIdeal (ringStalk X.sheaf x)) (modStalk F x)) ∧
    ((2 : ℕ∞) ≤ Module.depth (ringStalk X.sheaf x)
        (IsLocalRing.maximalIdeal (ringStalk X.sheaf x)) (ringStalk X.sheaf x) →
      (2 : ℕ∞) ≤ Module.depth (ringStalk X.sheaf x)
        (IsLocalRing.maximalIdeal (ringStalk X.sheaf x)) (modStalk F x)) := by
  have hnoe : IsNoetherianRing (ringStalk X.sheaf x) := by
    change IsNoetherianRing (X.presheaf.stalk x); infer_instance
  have : (dualSheaf F).IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (dualSheaf F)
  have hfin : Module.Finite (ringStalk X.sheaf x) (modStalk (dualSheaf F) x) :=
    SheafOfModules.finite_stalk X.sheaf (dualSheaf F) x
  rw [Module.depth_eq_depth_of_linearEquiv _ (modStalkEquivDualOfIsReflexive F hF x)]
  exact one_le_depth_and_two_le_depth_linearMap
    (M := modStalk (dualSheaf F) x) (N := ringStalk X.sheaf x)

/-- **Stacks, Tag 0EBI part (1), with the finite presentation of the dual as its one
hypothesis.**  On a locally Noetherian scheme, the stalk of a reflexive module whose dual is of
finite presentation has depth at least two at every point at which the local ring does.

Neither coherence of `F` nor integrality of `X` is used, so this is a generalization of the
source's statement in those two respects; `[(dualSheaf F).IsFinitePresentation]` is the one
hypothesis added, and the tag is withheld for exactly that reason. -/
-- stacks attribute for 0EBI part (1) withheld: the tag asserts the bound for every coherent
-- reflexive module unconditionally, and finite presentation of the dual is assumed here.
public theorem two_le_depth_stalk_of_isReflexive (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F : X.Modules) [(dualSheaf F).IsFinitePresentation] (hF : IsReflexive F) (x : X)
    (hx : (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (↑(TopCat.Presheaf.stalk F.val.presheaf x)) :=
  have : IsLocalRing (ringStalk X.sheaf x) := by
    change IsLocalRing (X.presheaf.stalk x); infer_instance
  (depth_stalk_bound_of_isReflexive X F hF x).2 hx

/-- **Stacks, Tag 0EBI part (1), the depth-one half**, with the finite presentation of the dual
as its one hypothesis.  This is the bound that the Serre-condition statement, part (2) of the
same tag, uses below the two-dimensional locus. -/
public theorem one_le_depth_stalk_of_isReflexive (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F : X.Modules) [(dualSheaf F).IsFinitePresentation] (hF : IsReflexive F) (x : X)
    (hx : (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (↑(TopCat.Presheaf.stalk F.val.presheaf x)) :=
  have : IsLocalRing (ringStalk X.sheaf x) := by
    change IsLocalRing (X.presheaf.stalk x); infer_instance
  (depth_stalk_bound_of_isReflexive X F hF x).1 hx

/-! ### Serre's condition for the module -/

/-- **Stacks, Tag 0EBI part (2), with the finite presentation of the dual as its one
hypothesis.**  On a locally Noetherian scheme satisfying Serre's condition `(S₂)`, a reflexive
module whose dual is of finite presentation satisfies `(S₂)`.

Above the two-dimensional locus the bound comes from part (1); below it, the dimension of the
support of the stalk is itself at most one, so the depth-one half of part (1) suffices, and on
the zero-dimensional locus nothing is needed.

Integrality of `X` and coherence of `F` are not used, so this is a generalization of the
source's statement in those two respects.  The tag is withheld for the same reason as for
part (1): finite presentation of the dual is assumed. -/
-- stacks attribute for 0EBI part (2) withheld: the tag asserts Serre's condition for every
-- coherent reflexive module unconditionally, and finite presentation of the dual is assumed here.
public theorem sheafHasPropertySk_two_of_isReflexive_of_isFinitePresentation_dualSheaf
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F : X.Modules) [(dualSheaf F).IsFinitePresentation] (hF : IsReflexive F)
    (hX : AlgebraicGeometry.HasPropertySk X 2) :
    AlgebraicGeometry.SheafHasPropertySk X (F : SheafOfModules.{u}
      (structureSheafRing X.toRingedSpace)) 2 := by
  intro x
  rw [Stacks.SheafOfModules.stalkModule_eq]
  have hxRing := hX x
  have hdepthR : ∀ n : ℕ∞, n ≤ 2 → (n : WithBot ℕ∞) ≤ Module.supportDim (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk F.val.presheaf x)) → n ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) := fun n hn h =>
    WithBot.coe_le_coe.mp
      ((le_min (WithBot.coe_le_coe.mpr hn)
        (h.trans (Module.supportDim_le_ringKrullDim _ _))).trans hxRing)
  by_cases htwo : (2 : WithBot ℕ∞) ≤ Module.supportDim (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk F.val.presheaf x))
  · exact (min_le_left _ _).trans (WithBot.coe_le_coe.mpr
      (two_le_depth_stalk_of_isReflexive X F hF x (hdepthR 2 le_rfl htwo)))
  · by_cases hone : (1 : WithBot ℕ∞) ≤ Module.supportDim (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk F.val.presheaf x))
    · refine (min_le_right _ _).trans ?_
      exact (withBot_lt_two_le_one (lt_of_not_ge htwo)).trans (WithBot.coe_le_coe.mpr
        (one_le_depth_stalk_of_isReflexive X F hF x (hdepthR 1 (by norm_num) hone)))
    · refine (min_le_right _ _).trans ?_
      exact (withBot_lt_one_le_zero (lt_of_not_ge hone)).trans (by simp)

/-! ### Tag 0EBJ with the stalk-depth hypothesis discharged -/

/-- **The statement of Stacks, Tag 0EBJ, from two named hypotheses and the finite presentation
of the dual of a coherent module.**

This is `reflexiveCoherentEquivalenceOfPreservation` with its third hypothesis — Tag 0EBI
part (1) — discharged by `two_le_depth_stalk_of_isReflexive`.  What replaces it, `hdualFP`, is
*not* a new assumption of the same kind: it is Tag 01Y2 at `𝒢 = 𝒪_X`, the single input that the
reflexive-hull adjunction of Tag 0EBH already waits on, so the two now wait on one thing
together.

The tag is **withheld**: two hypotheses remain, namely Tag 0EBF clause (2) and the direct-image
extension step. -/
public noncomputable def reflexiveCoherentEquivalenceOfCoherentDual (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (hpullback : ∀ F : X.Modules, F.IsCoherent → IsReflexive F →
      IsReflexive ((Scheme.Modules.pullback U.ι).obj F))
    (hpushforward : ∀ G : U.toScheme.Modules, G.IsCoherent → IsReflexive G →
      ((Scheme.Modules.pushforward U.ι).obj G).IsCoherent ∧
        IsReflexive ((Scheme.Modules.pushforward U.ι).obj G))
    (hdualFP : ∀ F : X.Modules, F.IsCoherent → (dualSheaf F).IsFinitePresentation) :
    Σ e : ReflexiveCoherentModules X ≌ ReflexiveCoherentModules U.toScheme,
      (e.functor ⋙ ObjectProperty.ι
          (fun F : U.toScheme.Modules =>
            F.IsCoherent ∧ IsReflexive F) ≅
        ObjectProperty.ι
          (fun F : X.Modules => F.IsCoherent ∧ IsReflexive F) ⋙
          Scheme.Modules.pullback U.ι) ×
      (e.inverse ⋙ ObjectProperty.ι
          (fun F : X.Modules => F.IsCoherent ∧ IsReflexive F) ≅
        ObjectProperty.ι
          (fun F : U.toScheme.Modules =>
            F.IsCoherent ∧ IsReflexive F) ⋙
          Scheme.Modules.pushforward U.ι) :=
  reflexiveCoherentEquivalenceOfPreservation X U hdepth hpullback hpushforward
    (fun F hcoh hrefl x hx =>
      haveI : (dualSheaf F).IsFinitePresentation := hdualFP F hcoh
      two_le_depth_stalk_of_isReflexive X F hrefl x hx)

end Stacks.AlgebraicGeometry.ReflexiveModules

end
