module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DerivedSupportInvertsAugmentation
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.GlobalSectionsAffineCase

/-!
# The termwise Čech base change of Tag 0G7U is invertible on quasi-coherent modules

Let `g : X' ⟶ X` be a morphism of schemes, `f₁, …, f_c ∈ Γ(X, 𝒪_X)` and `f'ᵢ = g^♯(fᵢ)`. The
comparison `(ℱ')^• = g^*ℱ^•` of the two extended alternating Čech complexes that
[Stacks, Tag 0G7U] asserts is built in
`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/CechBaseChange.lean`:
`Stacks.Perfect.CechBaseChange.restrictedModuleBaseChange` termwise, `prodTermBaseChange` at the
product terms and `cplxBaseChange` as the map of complexes.

This file contributes the one thing that chain does not state: those comparisons are
**isomorphisms** when `ℱ` is quasi-coherent — termwise, at the product terms, and as a map of
complexes. That is the hypothesis under which the *first* diagram of [Stacks, Tag 0G7U] is
asserted — the second needs only the map — so it is an input to assertion (1). The complex-level
statement is the load-bearing one: it is what makes the remark's `(ℱ')^• = g^*ℱ^•` an
identification rather than a comparison, and so what lets the first diagram's top arrow be the
[Stacks, Tag 0G78] map in degree `c` rather than a Čech-level stand-in.

## Main results

* `Stacks.Perfect.CechBaseChange.isIso_restrictedModuleBaseChange` — termwise.
* `Stacks.Perfect.CechBaseChange.isIso_prodTermBaseChange` — at the product terms.
* `Stacks.Perfect.CechBaseChange.isIso_cplxBaseChange` — the comparison of complexes
  `g^*(ℱ^•) ⟶ (g^*ℱ)^•` is an isomorphism, which is the corrected form of the note
  `(ℱ')^• = g^*ℱ^•` of [Stacks, Tag 0G7U].  The note is stated there for an arbitrary
  `𝒪_X`-module and is false in that generality:
  `Stacks.Perfect.CechBaseChangeCounterexample.not_isIso_cplxBaseChange_f_one`
  (`CechBaseChangeCounterexample.lean`) gives a non-quasi-coherent `ℱ` for which the comparison
  is not an isomorphism in degree `1`, and for which the two complexes are not isomorphic at
  all (`isEmpty_iso_cplx`).

## Implementation notes

No flatness of `g` is needed, and that is the point: [Stacks, Tag 0G7U] assumes none, so every
`isIso_baseChangeNatTrans_of_flat` in the repository is unusable here, and the two unconditional
results — `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare` and
`Stacks.AlgebraicGeometry.PushforwardRegularity.OpenBaseChange.isIso_baseChangeNatTrans_pullback`
— are the transpose orientation, with the open immersion the morphism one pulls *back* along.

What applies instead is [Stacks, Tag 02KG] assertion 3 for an **affine** right-hand morphism,
which holds over an arbitrary base:
`Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_baseChangeNatTrans`. Its hypotheses are
all available here. The square is cartesian by `AlgebraicGeometry.isPullback_morphismRestrict`,
whose orientation matches `Stacks.Perfect.OpenPushRestrictBaseChange.restrictSquare` on the nose
— the two are proofs of the same equation, so they are the same term. The right-hand morphism is
affine because a principal-open intersection is the principal open of the product of the
equations, which is `Stacks.Perfect.CechDerivedSupport.isAffineHom_equationsOpen_ι`. And the
coefficient module stays quasi-coherent under restriction, by
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor`.

Everything else in `restrictedModuleBaseChange` is invertible for formal reasons and contributes
nothing: `toRPhom` and `toRPinv` are mutually inverse by `toRPhom_toRPinv` and `toRPinv_toRPhom`,
being `pushforward` of the two directions of `Scheme.Modules.restrictFunctorIsoPullback`; the
transport along `equationsOpen_pullback` is an `eqToHom`; and the second factor of
`openBaseChange` is a `pushforward` of a component of `pullbackRestrictIso`. So the theorem
unfolds the two definitions and lets instance search assemble the composite.

The statement is deliberately at `Stacks.Perfect.CechBaseChange.restrictedModuleBaseChange`
rather than at the underlying `baseChangeNatTrans`, because the library carries **two parallel
presentations** of the extended alternating Čech complex and a theorem about the wrong one does
not apply to this chain. `AlgebraicGeometry.ExtendedAlternatingCech.equationsOpen`
(`ExtendedAlternatingCech.lean:101`) and `Stacks.Perfect.ExtendedAlternatingCech.equationsOpen`
(`GlobalEquationsComplexData.lean:79`) are character-for-character identical definitions in
different namespaces, as are the two `restrictedModule`s, and both carry `@[stacks 0G7I]`. The
`isAffineHom_equationsOpen_ι` instance is stated for the `Stacks.Perfect` one, so instance search
silently fails on a goal phrased with the other. This is pre-existing and is not touched here.

`isIso_cplxBaseChange` is registered under Tag 0G7U as the corrected form of the note
`(ℱ')^• = g^*ℱ^•`; the other 0G7U registrations sit with the two diagrams.

## References

* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.OpenPushRestrictBaseChange
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.CechBaseChange

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ} (f : Fin c → Γ(X, ⊤))

/-- **The termwise Čech base change of [Stacks, Tag 0G7U] is invertible on quasi-coherent
modules.** For `ℱ` quasi-coherent, the comparison

`g^*((U_{i₀…i_p} → X)_*(ℱ|_{U_{i₀…i_p}})) ⟶ (U'_{i₀…i_p} → X')_*((g^*ℱ)|_{U'_{i₀…i_p}}))`

of `Stacks.Perfect.CechBaseChange.restrictedModuleBaseChange` is an isomorphism. This is the
hypothesis under which the first diagram of [Stacks, Tag 0G7U] is asserted.

There is no flatness hypothesis on `g`: the inclusion of a principal-open intersection is an
*affine* morphism, and base change for the direct image along an affine morphism holds over an
arbitrary base — [Stacks, Tag 02KG] assertion 3,
`Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_baseChangeNatTrans`. -/
public theorem isIso_restrictedModuleBaseChange (F : X.Modules) [F.IsQuasicoherent] (p : ℕ)
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    IsIso (restrictedModuleBaseChange g f F p s) := by
  have : IsAffineHom (equationsOpen f p s).ι :=
    Stacks.Perfect.CechDerivedSupport.isAffineHom_equationsOpen_ι f s
  have : ((Scheme.Modules.restrictFunctor (equationsOpen f p s).ι).obj F).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor _ F
  have : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      (restrictSquare g (equationsOpen f p s))).app
      ((Scheme.Modules.restrictFunctor (equationsOpen f p s).ι).obj F)) :=
    Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_baseChangeNatTrans
      (isPullback_morphismRestrict g (equationsOpen f p s)) _
  have : IsIso (toRPinv f F p s) :=
    ⟨_, toRPinv_toRPhom f F p s, toRPhom_toRPinv f F p s⟩
  have : IsIso (toRPhom (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) p s) :=
    ⟨_, toRPhom_toRPinv _ _ p s, toRPinv_toRPhom _ _ p s⟩
  dsimp only [restrictedModuleBaseChange, openBaseChange]
  infer_instance

/-- **The comparison at the product term is an isomorphism for quasi-coherent `ℱ`.** The
degree-`p + 1` term of the extended alternating Čech complex is a finite product of the terms
above, and `prodTermBaseChange` is the comparison on it.

That `Scheme.Modules.pullback g` commutes with this *limit* at all is not automatic — it is a
left adjoint — but it is pure Mathlib and needs nothing supplied: the pullback is additive, an
additive functor preserves finite products
(`CategoryTheory.Functor.preservesFiniteProductsOfAdditive`, a priority-100 instance), and
`CechCochains.OrdIndex p` is a `Fintype`. So the comparison factors as the Mathlib product
comparison followed by the product of the termwise comparisons, and both are isomorphisms. -/
public theorem isIso_prodTermBaseChange (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) :
    IsIso (prodTermBaseChange g f F p) := by
  have : ∀ s : CechCochains.OrdIndex (I := Fin c) p,
      IsIso (restrictedModuleBaseChange g f F p s) :=
    fun s => isIso_restrictedModuleBaseChange g f F p s
  have h : prodTermBaseChange g f F p =
      (Limits.PreservesProduct.iso (Scheme.Modules.pullback g)
          (fun s : CechCochains.OrdIndex (I := Fin c) p => restrictedModule f F p s) ≪≫
        Limits.Pi.mapIso fun s : CechCochains.OrdIndex (I := Fin c) p =>
          asIso (restrictedModuleBaseChange g f F p s)).hom := by
    refine Limits.Pi.hom_ext _ _ fun s => ?_
    rw [prodTermBaseChange_π, Iso.trans_hom, Category.assoc, Limits.Pi.mapIso_hom_π,
      Limits.PreservesProduct.iso_hom, Limits.piComparison_comp_π_assoc, asIso_hom]
  rw [h]
  infer_instance

/-- **The comparison of the two extended alternating Čech complexes is an isomorphism for
quasi-coherent `ℱ`.** This is the corrected form of the note `(ℱ')^• = g^*ℱ^•` of
[Stacks, Tag 0G7U], as an isomorphism of complexes rather than only a morphism — which is what
the remark's first diagram needs, and what lets its top arrow be identified with the
[Stacks, Tag 0G78] map in degree `c` rather than with a Čech-level comparison.

The remark states the note for an arbitrary `𝒪_X`-module `ℱ`, and in that generality it is
false: `Stacks.Perfect.CechBaseChangeCounterexample.not_isIso_cplxBaseChange_f_one` takes `k` a
field, `g : 𝔸¹_k ⟶ 𝔸²_k` the diagonal, the single equation `x`, and `ℱ` the extension by zero
of `𝒪` from `D(y)`, and shows that this comparison is not an isomorphism in degree `1`
(`Stacks.Perfect.CechBaseChangeCounterexample.isEmpty_iso_cplx`: the two complexes are not
isomorphic by any isomorphism).  The quasi-coherence hypothesis is therefore needed here; it is
the hypothesis under which the remark's first diagram is asserted.

A morphism of complexes is invertible as soon as every component is
(`HomologicalComplex.Hom.isIso_of_components`); here the degree-`0` component is the identity and
the rest is `isIso_prodTermBaseChange`. No flatness on `g`. -/
@[stacks 0G7U "the note `(F')^• = g^*F^•`, corrected to quasi-coherent `F` and read through the \
comparison map; for an arbitrary `F` it is false, see \
`CechBaseChangeCounterexample.not_isIso_cplxBaseChange_f_one`"]
public theorem isIso_cplxBaseChange (F : X.Modules) [F.IsQuasicoherent] :
    IsIso (cplxBaseChange g f F) := by
  have : ∀ n : ℕ, IsIso ((cplxBaseChange g f F).f n) := by
    intro n
    cases n with
    | zero =>
      change IsIso (cplxBaseChangeF g f F 0)
      dsimp only [cplxBaseChangeF]
      exact IsIso.id _
    | succ p =>
      change IsIso (cplxBaseChangeF g f F (p + 1))
      dsimp only [cplxBaseChangeF]
      exact isIso_prodTermBaseChange g f F p
  exact HomologicalComplex.Hom.isIso_of_components _

end Stacks.Perfect.CechBaseChange

end
