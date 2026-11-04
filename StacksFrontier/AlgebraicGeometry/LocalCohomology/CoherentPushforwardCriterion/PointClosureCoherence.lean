module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.AssociatedPointsCompat
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosedImmersionCoherence
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardAssociatedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# Coherence of the direct image of the structure sheaf of the closure of a point

Let `X` be a locally Noetherian scheme, `j : U ⟶ X` the inclusion of an open subscheme and `F` a
quasi-coherent `𝒪_U`-module. For `x ∈ U` write `i_x : W_x → U` for the integral closed subscheme
with generic point `x`. This file proves the implication (2) ⇒ (1) of [Stacks, Tag 0BJZ] from the
point where its comparison morphism is available: once `𝒪_U`-module map
`i_{x,*} 𝒪_{W_x} ⟶ F` is known to be a monomorphism, coherence of `j_* F` gives coherence of
`j_* i_{x,*} 𝒪_{W_x}`.

## Main results

* `AlgebraicGeometry.pointClosureStructureSheaf`: the `𝒪_U`-module `i_{x,*} 𝒪_{W_x}`.
* `AlgebraicGeometry.isCoherent_pushforward_of_injective_on_associatedPoints`: the general form
  of the argument. For a morphism of quasi-coherent `𝒪_U`-modules `φ : G ⟶ F` that is injective
  on the stalk at every associated point of `G`, coherence of `j_* F` gives coherence of
  `j_* G`.
* `AlgebraicGeometry.isCoherent_pushforward_pointClosure_of_mono`: the implication (2) ⇒ (1) of
  [Stacks, Tag 0BJZ] at the point `x`, granted a monomorphism `i_{x,*} 𝒪_{W_x} ⟶ F`.

## Implementation notes

`W_x` is taken as in `StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme`:
the closed subscheme cut out by the vanishing ideal of `closure {x}`. That file's
`Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure` and
`Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure` are what identify it as
*the* integral closed subscheme with generic point `x`, so a statement about this definite
construction reads as a statement about `W_x`.

The two steps of the source's last paragraph are already in the tree and are composed here.
Injectivity of the comparison morphism is [Stacks, Tag 0AVL], used through
`Stacks.Divisors.mono_of_stalk_injective_on_associatedPoints`, which is that tag restated
against the `Ass(F)` of [Stacks, Tag 02OJ]. The passage from a monomorphism to coherence of the
direct image is
`Stacks.AlgebraicGeometry.PushforwardAssociatedPoints.isCoherent_pushforward_of_mono`: direct
image along `j` is a right adjoint, hence preserves monomorphisms, and a quasi-coherent
submodule of a coherent module on a locally Noetherian scheme is coherent by
[Stacks, Tag 01Y1].

`U` is locally Noetherian because `X` is and `j` is an open immersion; this is supplied rather
than found by instance search, as is quasi-coherence of `i_{x,*} 𝒪_{W_x}`, which is
[Stacks, Tag 01LC] for the closed immersion `i_x`.

What is *not* proved here is the construction of the comparison morphism, which is the hypothesis
`Mono φ` below. In the source it is obtained by choosing a nonzero map
`φ_x : 𝒪_{W_x, x} = κ(x) → F_x` — which exists exactly because `x` is an associated point of `F`
— spreading it to a neighbourhood of `x` by [Stacks, Tag 01Y4] and extending it to all of `U` by
[Stacks, Tag 01YB]. The tree has both of those tags, but at incompatible levels of generality:
Tag 01Y4 is stated for sheaves of modules on a ringed space over an arbitrary neighbourhood,
while the Tag 01YB extension
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_homRestrict_eq` accepts only the open
`I.support.compl` of an ideal sheaf `I` and produces a map out of `I^k · G` rather than out of
`G`. Bridging them is a separate piece of work.

## References

* [Stacks Project, Tag 0BJZ](https://stacks.math.columbia.edu/tag/0BJZ)
* [Stacks Project, Tag 0AVL](https://stacks.math.columbia.edu/tag/0AVL)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The general form of the last paragraph of [Stacks, Tag 0BJZ].** Let `X` be locally
Noetherian, `j : U ⟶ X` an open immersion and `φ : G ⟶ F` a morphism of quasi-coherent
`𝒪_U`-modules which, at each point of `U`, is either injective on stalks or is at a point
outside `Ass(G)`. If `j_* F` is coherent then so is `j_* G`.

The hypothesis is the one of [Stacks, Tag 0AVL], so `φ` is a monomorphism; direct image
preserves monomorphisms and a quasi-coherent submodule of a coherent module is coherent by
[Stacks, Tag 01Y1]. -/
theorem isCoherent_pushforward_of_injective_on_associatedPoints
    {U X : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    {G F : U.Modules} [G.IsQuasicoherent] [F.IsQuasicoherent]
    (φ : G ⟶ F)
    (hφ : ∀ y : U, Function.Injective
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          ((PresheafOfModules.toPresheaf U.ringCatSheaf.obj).map φ.val)).hom ∨
        y ∉ Stacks.Divisors.associatedPoints G)
    (hF : ((Scheme.Modules.pushforward j).obj F).IsCoherent) :
    ((Scheme.Modules.pushforward j).obj G).IsCoherent := by
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  have : Mono φ := Stacks.Divisors.mono_of_stalk_injective_on_associatedPoints φ hφ
  exact Stacks.AlgebraicGeometry.PushforwardAssociatedPoints.isCoherent_pushforward_of_mono
    j φ hF

/-- The `𝒪_U`-module `i_{x,*} 𝒪_{W_x}` of [Stacks, Tag 0BJZ]: the direct image of the structure
sheaf of the integral closed subscheme of `U` with generic point `x` along its closed immersion
into `U`. -/
noncomputable abbrev pointClosureStructureSheaf {U : Scheme.{u}} (x : U) : U.Modules :=
  (Scheme.Modules.pushforward
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set U))).subschemeι).obj
    (SheafOfModules.unit
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subscheme.ringCatSheaf)

/-- `i_{x,*} 𝒪_{W_x}` is quasi-coherent: it is a direct image of a quasi-coherent module along a
closed immersion, which is quasi-compact and quasi-separated, so [Stacks, Tag 01LC] applies. -/
theorem isQuasicoherent_pointClosureStructureSheaf {U : Scheme.{u}} (x : U) :
    (pointClosureStructureSheaf x).IsQuasicoherent :=
  AlgebraicGeometry.pushforward_isQuasicoherent _ _

/-- **The implication (2) ⇒ (1) of [Stacks, Tag 0BJZ], granted the comparison morphism.** Let `X`
be a locally Noetherian scheme, `j : U ⟶ X` the inclusion of an open subscheme, `F` a
quasi-coherent `𝒪_U`-module and `x ∈ U`, and write `i_x : W_x → U` for the integral closed
subscheme with generic point `x`. If there is a monomorphism `i_{x,*} 𝒪_{W_x} ⟶ F` of
`𝒪_U`-modules, then coherence of `j_* F` implies coherence of `j_* i_{x,*} 𝒪_{W_x}`.

This is clause (1) of the source at the point `x`, deduced from clause (2). The monomorphism is
a hypothesis: in the source it is constructed from `x ∈ Ass(F)` by extending a nonzero map
`κ(x) → F_x` over `U`, which is the part of the argument this file does not carry out. That
construction is
`Stacks.AlgebraicGeometry.PointClosureComparison.exists_mono_of_isAssociatedPoint`, and the
unconditional clause is `isCoherent_pushforward_pointClosure_of_isAssociatedPoint'` in
`Stacks.AlgebraicGeometry.CoherenceFromPointClosures`; the tag for [Stacks, Tag 0BJZ] sits on the
full equivalence `isCoherent_pushforward_iff_forall_isAssociatedPoint` in the same namespace. -/
@[ega "IV 5.11.1" "a) => b)"]
theorem isCoherent_pushforward_pointClosure_of_mono
    {U X : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (x : U)
    {F : U.Modules} [F.IsQuasicoherent]
    (φ : pointClosureStructureSheaf x ⟶ F) [Mono φ]
    (hF : ((Scheme.Modules.pushforward j).obj F).IsCoherent) :
    ((Scheme.Modules.pushforward j).obj (pointClosureStructureSheaf x)).IsCoherent := by
  have := isQuasicoherent_pointClosureStructureSheaf x
  exact Stacks.AlgebraicGeometry.PushforwardAssociatedPoints.isCoherent_pushforward_of_mono
    j φ hF

/-- **The implication (2) ⇒ (1) of [Stacks, Tag 0BJZ], granted the comparison morphism.** The form
of `isCoherent_pushforward_pointClosure_of_mono` whose hypothesis is the one of
[Stacks, Tag 0AVL]: it is enough that the comparison morphism be injective on the stalk at each
associated point of `i_{x,*} 𝒪_{W_x}`. -/
theorem isCoherent_pushforward_pointClosure_of_injective_on_associatedPoints
    {U X : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (x : U)
    {F : U.Modules} [F.IsQuasicoherent]
    (φ : pointClosureStructureSheaf x ⟶ F)
    (hφ : ∀ y : U, Function.Injective
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          ((PresheafOfModules.toPresheaf U.ringCatSheaf.obj).map φ.val)).hom ∨
        y ∉ Stacks.Divisors.associatedPoints (pointClosureStructureSheaf x))
    (hF : ((Scheme.Modules.pushforward j).obj F).IsCoherent) :
    ((Scheme.Modules.pushforward j).obj (pointClosureStructureSheaf x)).IsCoherent := by
  have := isQuasicoherent_pointClosureStructureSheaf x
  exact isCoherent_pushforward_of_injective_on_associatedPoints j φ hφ hF

end AlgebraicGeometry

end
