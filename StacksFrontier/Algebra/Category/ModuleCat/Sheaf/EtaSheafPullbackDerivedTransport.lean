module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafIdealTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackDerived

/-!
# The derived décalage under a pullback, read at a second presentation of the pulled-back ideal

Let `f : X ⟶ Y` be a morphism of ringed spaces with exact pullback, let `I ⊆ 𝒪_Y` be an
invertible ideal sheaf, and let `J ⊆ 𝒪_X` be an invertible ideal sheaf together with an
isomorphism `e : f^*I ≅ J` compatible with the two inclusions into `𝒪_X`.  The canonical
comparison `Stacks.IdealTorsion.Eta.pullbackDerivedEtaMap` lands in `Lη_{f^*I}`; this file
carries it across `e` to land in `Lη_J`.

This is the situation of [Stacks, Tag 0F9X], which compares `Lh^*(Lη_{I_D} M)` with
`Lη_{I_E}(Lh^* M)` where `E = h^{-1}D`: `I_E` is not `h^*I_D` on the nose, but it is isomorphic
to it compatibly with the inclusions into the structure sheaf, which is exactly the datum `e`.

## Main definitions

* `Stacks.IdealTorsion.Eta.transportedPullbackDerivedEtaMap`: **the canonical comparison
  `Lf^*(Lη_I M) ⟶ Lη_J(Lf^* M)`**, for `M = [G^•]` represented by a complex of `I`-torsion-free
  modules.  It is the composite of four canonical maps: the comparison
  `Stacks.IdealTorsion.Eta.pullbackDerivedEtaMap` into `Lη_{f^*I}`, the identification of `Lf^*`
  with degreewise pullback, the transport
  `Stacks.IdealTorsion.Eta.IdealCongr.derivedEtaIso` along `e`, and that identification again,
  backwards.  No flatness is assumed.

## Main results

* `Stacks.IdealTorsion.Eta.isIso_transportedPullbackDerivedEtaMap`: **the comparison is an
  isomorphism when `f` is flat.**  Three of the four constituents are isomorphisms
  unconditionally — two are `Lη_J` applied to components of a natural isomorphism and one is the
  transport, which is an isomorphism outright — and the remaining one is
  `Stacks.IdealTorsion.Eta.isIso_pullbackDerivedEtaMap`, which is where flatness enters.
* `Stacks.IdealTorsion.Eta.isIdealTorsionFree_of_pullbackIdealIncl`: the torsion-freeness
  hypothesis for `J` follows from the one for `f^*I`.

## Implementation notes

The middle two maps are needed because the transport
`Stacks.IdealTorsion.Eta.IdealCongr.derivedEtaIso` is stated at an object of the form `Q F^•`
while the target of `Stacks.IdealTorsion.Eta.pullbackDerivedEtaMap` is `Lη` evaluated at
`Lf^*(Q G^•)`.  `CategoryTheory.Functor.mapDerivedCategoryFactors` identifies the second with
the first — `Lf^*(Q G^•) ≅ Q (f^* G^•)` for an exact `f^*` — so the transport is conjugated by
it.  Both conjugating maps are `Lη_{f^*I}`, respectively `Lη_J`, applied to a component of a
natural isomorphism, hence isomorphisms, and so they cost nothing in the invertibility argument.

Exactness of the pullback is taken as the two instance hypotheses
`CategoryTheory.Limits.PreservesFiniteLimits` and
`CategoryTheory.Limits.PreservesFiniteColimits`, as for
`Stacks.IdealTorsion.Eta.pullbackDerivedEtaMap`: they occur in the *statements*, through
`CategoryTheory.Functor.mapDerivedCategory`, so they have to be binders.  Flatness supplies both.

## References

* [Stacks Project, Tag 0F8Q](https://stacks.math.columbia.edu/tag/0F8Q)
* [Stacks Project, Tag 0F9X](https://stacks.math.columbia.edu/tag/0F9X)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.RingedSpace (pullbackFunctor)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.IdealTorsion.Eta

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
  [PreservesFiniteLimits (etaPullbackModules f)] [PreservesFiniteColimits (etaPullbackModules f)]
  (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
  (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) [Mono ι]
  [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
  [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    (pullbackIdealIncl f I ι)]
  (J : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
  (κ : J ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) [Mono κ]
  [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property J]
  (e : Iso (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    ((pullbackFunctor f).obj I) J)
  (he : e.hom ≫ κ = pullbackIdealIncl f I ι)

omit [PreservesFiniteLimits (etaPullbackModules f)]
  [PreservesFiniteColimits (etaPullbackModules f)] [Mono ι]
  [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
  [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    (pullbackIdealIncl f I ι)] [Mono κ]
  [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property J] in
include he in
/-- Torsion-freeness for the second presentation `J` of the pulled-back ideal follows from
torsion-freeness for `f^*I`: the two ideals are the same subsheaf of `𝒪_X`, by
`Stacks.IdealTorsion.Eta.IdealCongr.isIdealTorsionFree_congr`. -/
theorem isIdealTorsionFree_of_pullbackIdealIncl
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    (hG : IsIdealTorsionFree X (pullbackIdealIncl f I ι) G) :
    IsIdealTorsionFree X κ G :=
  (IdealCongr.isIdealTorsionFree_congr X (pullbackIdealIncl f I ι) κ e he G).mp hG

include he in
/-- **The canonical comparison `Lf^*(Lη_I M) ⟶ Lη_J(Lf^* M)`** at an object `M = [G^•]` of
`D(𝒪_Y)` represented by a complex `G^•` of `I`-torsion-free `𝒪_Y`-modules, where `J` is a second
presentation of the pulled-back ideal `f^*I`.

The composite of four canonical maps: the comparison
`Stacks.IdealTorsion.Eta.pullbackDerivedEtaMap` into `Lη_{f^*I}`, the identification of `Lf^*`
with degreewise pullback, the transport `Stacks.IdealTorsion.Eta.IdealCongr.derivedEtaIso` along
`e`, and that identification read backwards.

No flatness is assumed; see
`Stacks.IdealTorsion.Eta.isIso_transportedPullbackDerivedEtaMap`. -/
def transportedPullbackDerivedEtaMap
    (hres : HasTorsionFreeResolutions Y ι)
    (hresP : HasTorsionFreeResolutions X (pullbackIdealIncl f I ι))
    (hresJ : HasTorsionFreeResolutions X κ)
    (K : CochainComplex (TorsionFreeModule Y ι) ℤ)
    (hK : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι)
      ((pullbackComplex f ((torsionFreeComplex Y ι).obj K)).X n)) :
    (etaPullbackModules f).mapDerivedCategory.obj
        ((derivedEta Y I ι hres).obj
          (DerivedCategory.Q.obj ((torsionFreeComplex Y ι).obj K))) ⟶
      (derivedEta X J κ hresJ).obj
        ((etaPullbackModules f).mapDerivedCategory.obj
          (DerivedCategory.Q.obj ((torsionFreeComplex Y ι).obj K))) :=
  pullbackDerivedEtaMap f I ι hres hresP K hK ≫
    (derivedEta X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) hresP).map
      ((etaPullbackModules f).mapDerivedCategoryFactors.hom.app
        ((torsionFreeComplex Y ι).obj K)) ≫
    (IdealCongr.derivedEtaIso X ((pullbackFunctor f).obj I) J (pullbackIdealIncl f I ι) κ e he
      (pullbackComplex f ((torsionFreeComplex Y ι).obj K)) hK
      (fun n => isIdealTorsionFree_of_pullbackIdealIncl f I ι J κ e he _ (hK n))
      hresP hresJ).hom ≫
    (derivedEta X J κ hresJ).map
      ((etaPullbackModules f).mapDerivedCategoryFactors.inv.app
        ((torsionFreeComplex Y ι).obj K))

include he in
/-- **For a flat morphism the canonical comparison `Lf^*(Lη_I M) ⟶ Lη_J(Lf^* M)` is an
isomorphism.**

Of the four constituents, the transport along `e` is an isomorphism outright and the two
conjugating maps are `Lη` applied to components of the natural isomorphism
`CategoryTheory.Functor.mapDerivedCategoryFactors`, hence isomorphisms; the remaining one is
`Stacks.IdealTorsion.Eta.pullbackDerivedEtaMap`, which is an isomorphism for flat `f` by
`Stacks.IdealTorsion.Eta.isIso_pullbackDerivedEtaMap`. -/
theorem isIso_transportedPullbackDerivedEtaMap (hf : AlgebraicGeometry.IsFlat f)
    (hres : HasTorsionFreeResolutions Y ι)
    (hresP : HasTorsionFreeResolutions X (pullbackIdealIncl f I ι))
    (hresJ : HasTorsionFreeResolutions X κ)
    (K : CochainComplex (TorsionFreeModule Y ι) ℤ)
    (hK : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι)
      ((pullbackComplex f ((torsionFreeComplex Y ι).obj K)).X n)) :
    IsIso (transportedPullbackDerivedEtaMap f I ι J κ e he hres hresP hresJ K hK) := by
  have h1 := isIso_pullbackDerivedEtaMap f I ι hf hres hresP K hK
  have h2 : IsIso ((derivedEta X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) hresP).map
      ((etaPullbackModules f).mapDerivedCategoryFactors.hom.app
        ((torsionFreeComplex Y ι).obj K))) := inferInstance
  have h3 : IsIso ((IdealCongr.derivedEtaIso X ((pullbackFunctor f).obj I) J
      (pullbackIdealIncl f I ι) κ e he
      (pullbackComplex f ((torsionFreeComplex Y ι).obj K)) hK
      (fun n => isIdealTorsionFree_of_pullbackIdealIncl f I ι J κ e he _ (hK n))
      hresP hresJ).hom) := inferInstance
  have h4 : IsIso ((derivedEta X J κ hresJ).map
      ((etaPullbackModules f).mapDerivedCategoryFactors.inv.app
        ((torsionFreeComplex Y ι).obj K))) := inferInstance
  rw [transportedPullbackDerivedEtaMap]
  exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' h2 (IsIso.comp_isIso' h3 h4))

end Stacks.IdealTorsion.Eta

end
