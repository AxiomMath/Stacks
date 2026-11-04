module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# Cokernels of quasi-coherent modules on an affine scheme

On an affine scheme the quasi-coherent modules are closed under cokernels.

On `Spec R` this is the cocontinuity of `M ↦ M̃`: a quasi-coherent module is the associated sheaf
of its global sections, and the tilde functor is a left adjoint, so it carries the cokernel of
the induced map of `R`-modules to the cokernel of the original map. A general affine scheme is
isomorphic to `Spec Γ(X, ⊤)`, and quasi-coherence transports across an isomorphism of schemes,
which reduces the general case to that one.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_cokernel`: the cokernel of a morphism between
  quasi-coherent modules on an affine scheme is quasi-coherent.

## Implementation notes

An affine scheme is represented by Mathlib's `AlgebraicGeometry.IsAffine` predicate rather than
by a chosen presentation as a spectrum, and the presentation used in the proof is
`AlgebraicGeometry.Scheme.isoSpec`. Modules are objects of `AlgebraicGeometry.Scheme.Modules` and
the cokernel is computed in that abelian category.

The transport along `X.isoSpec` is through the pullback functor, which preserves colimits as a
left adjoint; `Scheme.Modules.restrictFunctorIsoPullback` identifies pullback along an
isomorphism with restriction, which is how quasi-coherence is carried across. The statement is an
`instance`, so that quasi-coherence of an iterated cokernel is found by instance search.

## References

* [Stacks Project, Tag 01IC](https://stacks.math.columbia.edu/tag/01IC)
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry

universe u

/-- Quasi-coherence is invariant under isomorphism of modules. -/
private theorem isQuasicoherent_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    [M.IsQuasicoherent] : N.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e inferInstance

/-- On `Spec R` the cokernel of a map of quasi-coherent modules is quasi-coherent, because the
tilde functor is a left adjoint and so preserves cokernels. -/
private theorem isQuasicoherent_cokernel_onSpec {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (cokernel f).IsQuasicoherent := by
  let φ := (moduleSpecΓFunctor (R := R)).map f
  have := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  have := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  let eM := asIso (Scheme.Modules.fromTildeΓ M)
  let eN := asIso (Scheme.Modules.fromTildeΓ N)
  have hnat : (tilde.functor R).map φ ≫ eN.hom = eM.hom ≫ f := by
    change (moduleSpecΓFunctor (R := R) ⋙ tilde.functor R).map f ≫
        (Scheme.Modules.fromTildeΓNatTrans (R := R)).app N =
      (Scheme.Modules.fromTildeΓNatTrans (R := R)).app M ≫ f
    exact (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality f
  exact isQuasicoherent_of_iso (PreservesCokernel.iso (tilde.functor R) φ ≪≫
    cokernel.mapIso ((tilde.functor R).map φ) f eM eN hnat)

/-- Quasi-coherence is preserved by pullback along an isomorphism of schemes. -/
private theorem isQuasicoherent_pullback_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (M : Y.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback e.hom).obj M).IsQuasicoherent :=
  isQuasicoherent_of_iso ((Scheme.Modules.restrictFunctorIsoPullback e.hom).app M)

/-- **Stacks Project, Tag 01IC (cokernel).** The cokernel of a morphism between
quasi-coherent modules on an affine scheme is quasi-coherent. -/
@[stacks 01IC "cokernel", ega "I 4.1.1" "affine, cokernel"]
public instance isQuasicoherent_cokernel {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (cokernel f).IsQuasicoherent := by
  let e := X.isoSpec
  let R : CommRingCat := CommRingCat.of Γ(X, ⊤)
  let G := Scheme.Modules.pullback e.inv
  have hM : (G.obj M).IsQuasicoherent := isQuasicoherent_pullback_iso e.symm M
  have hN : (G.obj N).IsQuasicoherent := isQuasicoherent_pullback_iso e.symm N
  have hGC : (G.obj (cokernel f)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (PreservesCokernel.iso G f).symm (isQuasicoherent_cokernel_onSpec (R := R) (G.map f))
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (((Scheme.Modules.pullbackComp e.hom e.inv).app (cokernel f)) ≪≫
      ((Scheme.Modules.pullbackCongr e.hom_inv_id).app (cokernel f)) ≪≫
      (Scheme.Modules.pullbackId X).app (cokernel f))
    (isQuasicoherent_pullback_iso e (G.obj (cokernel f)))

end AlgebraicGeometry.Scheme.Modules
