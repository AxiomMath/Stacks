module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.Induction
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalAffine

/-!
# Flat base change ([Stacks, Tag 02KH])

Consider a cartesian square of schemes
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
with `g` flat and `f` quasi-compact and quasi-separated, and let `ℱ` be a quasi-coherent
`𝒪_X`-module with pullback `ℱ' = (g')^* ℱ`. Then:

1. the base change map of [Stacks, Tag 02N7] is an isomorphism
   `g^* R^i f_* ℱ ⟶ R^i f'_* ℱ'` for every `i`;
2. if `S` and `S'` are affine, then `H^i(X, ℱ) ⊗_{Γ(S, 𝒪_S)} Γ(S', 𝒪_{S'}) = H^i(X', ℱ')`.

## Main definitions

* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.higherBaseChangeMap`: the base change map
  `g^* R^i f_* ℱ ⟶ R^i f'_* ℱ'` in degree `i`, the degree-`i` cohomology of the base change map
  of [Stacks, Tag 02N7] read through the exactness of `g^*`.
* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.cohomologyBaseChangeIso`: the identification
  `H^i(X, ℱ) ⊗_{Γ(S, 𝒪_S)} Γ(S', 𝒪_{S'}) ≅ H^i(X', ℱ')` over affine bases.

## Main results

* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isIso_baseChangeMap_of_flat`: the base change map
  `g^* Rf_* ℱ ⟶ Rf'_* ℱ'` of [Stacks, Tag 02N7] is an isomorphism in `D⁺(𝒪_{S'})`.
* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isIso_higherBaseChangeMap`: part (1).
* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.cohomologyBaseChangeIso`: part (2).

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
  RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.FlatBaseChangeDerived

attribute [local instance] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}

/-- In a cartesian square with flat `g`, the base change `g'` of `g` is flat. -/
private theorem flat_snd_of_isPullback (H : IsPullback g' f' f g) [Flat g] : Flat g' :=
  MorphismProperty.of_isPullback H.flip inferInstance

/-- In a cartesian square with flat `g`, the base change `g'` of `g` is flat, as a morphism of
ringed spaces. -/
theorem isFlat_toShHom_of_isPullback (H : IsPullback g' f' f g) [Flat g] :
    AlgebraicGeometry.IsFlat g'.toLRSHom.toShHom :=
  have := flat_snd_of_isPullback H
  isFlat_toShHom g'

/-- **Flat base change in the derived category ([Stacks, Tag 02KH], part (1)).** For a cartesian
square of schemes with `g` flat and `f` quasi-compact and quasi-separated, and a quasi-coherent
`𝒪_X`-module `ℱ`, the base change map `g^* Rf_* ℱ ⟶ Rf'_* (g')^* ℱ` of [Stacks, Tag 02N7] is an
isomorphism in `D⁺(𝒪_{S'})`. Taking cohomology sheaves, the base change maps
`g^* R^i f_* ℱ ⟶ R^i f'_* (g')^* ℱ` are isomorphisms for every `i`
(`isIso_higherBaseChangeMap`). -/
@[stacks 02KH "part (1): the base change map of Tag 02N7 is an isomorphism in D⁺(𝒪_{S'}), hence \
in every degree i"]
theorem isIso_baseChangeMap_of_flat (H : IsPullback g' f' f g) [Flat g] [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] :
    IsIso ((Stacks.Cohomology.FlatBaseChange.baseChangeMap f.toLRSHom.toShHom
      f'.toLRSHom.toShHom g.toLRSHom.toShHom g'.toLRSHom.toShHom
      (congrArg (fun h => h.toLRSHom.toShHom) H.w) (isFlat_toShHom g)
      (isFlat_toShHom_of_isPullback H)).app ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
  have := flat_snd_of_isPullback H
  baseChangeIsIso f g f' g' H F

/-- Pullback along a flat morphism of schemes is exact. -/
theorem preservesFiniteColimits_modulePullback' {A B : Scheme.{u}} (h : A ⟶ B) :
    PreservesFiniteColimits (modulePullback h.toLRSHom.toShHom) :=
  preservesFiniteColimits_modulePullback _

/-- **The base change map in degree `i`.** For a cartesian square of schemes with `g` flat and a
module `ℱ` on `X`, the morphism `g^* R^i f_* ℱ ⟶ R^i f'_* (g')^* ℱ`: the degree-`i` cohomology of
the base change map of [Stacks, Tag 02N7] at `ℱ`, read through the identification of
`H^i(g^* K)` with `g^* H^i(K)` that exactness of `g^*` provides, and of `(g')^*` of `ℱ` placed
in degree zero with `(g')^* ℱ` placed in degree zero. -/
def higherBaseChangeMap (H : IsPullback g' f' f g) [Flat g]
    (F : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (i : ℤ) :
    (modulePullback g.toLRSHom.toShHom).obj
        (((modulePushforward f.toLRSHom.toShHom).rightDerivedPlus i).obj F) ⟶
      ((modulePushforward f'.toLRSHom.toShHom).rightDerivedPlus i).obj
        ((modulePullback g'.toLRSHom.toShHom).obj F) :=
  have : Flat g' := MorphismProperty.of_isPullback H.flip inferInstance
  have := preservesFiniteLimits_pullback g
  have := preservesFiniteColimits_modulePullback' g
  (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
      (modulePullback g.toLRSHom.toShHom) i).inv.app
      ((modulePushforward f.toLRSHom.toShHom).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
    (DerivedCategory.Plus.homologyFunctor _ i).map
      ((schemeBaseChange f f' g g' H.w).app ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
    (DerivedCategory.Plus.homologyFunctor _ i).map
      ((modulePushforward f'.toLRSHom.toShHom).rightDerivedFunctorPlus.map
        (pullbackSingleIso g' F).hom)

/-- **[Stacks, Tag 02KH], part (1).** For a cartesian square of schemes with `g` flat and `f`
quasi-compact and quasi-separated, and a quasi-coherent `𝒪_X`-module `ℱ`, the base change map
`g^* R^i f_* ℱ ⟶ R^i f'_* (g')^* ℱ` is an isomorphism for every `i`. -/
@[stacks 02KH "part (1), in each degree i"]
theorem isIso_higherBaseChangeMap (H : IsPullback g' f' f g) [Flat g] [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] (i : ℤ) :
    IsIso (higherBaseChangeMap H F i) := by
  have := flat_snd_of_isPullback H
  have := preservesFiniteLimits_pullback g
  have := preservesFiniteColimits_modulePullback' g
  have h₂ : IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map
      ((schemeBaseChange f f' g g' H.w).app ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :=
    have := baseChangeIsIso f g f' g' H F
    inferInstance
  exact IsIso.comp_isIso'
    (((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
      (modulePullback g.toLRSHom.toShHom) i).app _).isIso_inv)
    (IsIso.comp_isIso' h₂ ((DerivedCategory.Plus.homologyFunctor _ i).mapIso
      ((modulePushforward f'.toLRSHom.toShHom).rightDerivedFunctorPlus.mapIso
        (pullbackSingleIso g' F))).isIso_hom)

/-- The base change isomorphism `g^* R^i f_* ℱ ≅ R^i f'_* (g')^* ℱ` of part (1). -/
def higherBaseChangeIso (H : IsPullback g' f' f g) [Flat g] [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] (i : ℤ) :
    (modulePullback g.toLRSHom.toShHom).obj
        (((modulePushforward f.toLRSHom.toShHom).rightDerivedPlus i).obj F) ≅
      ((modulePushforward f'.toLRSHom.toShHom).rightDerivedPlus i).obj
        ((modulePullback g'.toLRSHom.toShHom).obj F) :=
  have := isIso_higherBaseChangeMap H F i
  asIso (higherBaseChangeMap H F i)

/-! ### Part (2): affine bases -/

section Affine

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The cohomology `H^i(X, ℱ)` of a module on a scheme over `S`, as a module over `Γ(S, 𝒪_S)`. -/
abbrev cohomologyOver (f : X ⟶ S) (F : X.Modules) (i : ℤ) : ModuleCat.{u} Γ(S, ⊤) :=
  (ModuleCat.restrictScalars f.appTop.hom).obj
    (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerivedPlus i).obj F)

/-- **[Stacks, Tag 02KH], part (2).** For a cartesian square of schemes with `S` and `S'`
affine, `g` flat and `f` quasi-compact and quasi-separated, and a quasi-coherent `𝒪_X`-module
`ℱ`,

`H^i(X, ℱ) ⊗_{Γ(S, 𝒪_S)} Γ(S', 𝒪_{S'}) ≅ H^i(X', (g')^* ℱ)`

as `Γ(S', 𝒪_{S'})`-modules, for every `i`. The isomorphism is the one given by the base change
map of [Stacks, Tag 02N7]: it is the global sections over `S'` of the isomorphism
`g^* R^i f_* ℱ ≅ R^i f'_* (g')^* ℱ` of part (1), read through the identifications
`H^i(X, ℱ) = Γ(S, R^i f_* ℱ)` of [Stacks, Tag 01XK] (for `f` and for `f'`) and
`Γ(S', g^* 𝒢) = Γ(S, 𝒢) ⊗_{Γ(S, 𝒪_S)} Γ(S', 𝒪_{S'})` for the quasi-coherent
`𝒢 = R^i f_* ℱ` ([Stacks, Tag 01XJ]). -/
@[stacks 02KH "part (2)"]
def cohomologyBaseChangeIso (H : IsPullback g' f' f g) [IsAffine S] [IsAffine S'] [Flat g]
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] (i : ℤ) :
    (ModuleCat.extendScalars g.appTop.hom).obj (cohomologyOver f F i) ≅
      cohomologyOver f' ((Scheme.Modules.pullback g').obj F) i :=
  have : QuasiCompact f' := MorphismProperty.of_isPullback H inferInstance
  have : QuasiSeparated f' := MorphismProperty.of_isPullback H inferInstance
  have : ((Scheme.Modules.pullback g').obj F).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback g' F
  (ModuleCat.extendScalars g.appTop.hom).mapIso
      ((Stacks.Cohomology.AffineBase.cohomologyIsoGlobalSectionsRightDerivedPushforward f i).app
        ⟨F, inferInstance⟩) ≪≫
    Stacks.AlgebraicGeometry.ModuleLimits.bcTop g
      (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F) ≪≫
    (Stacks.Cohomology.AffineBase.moduleGlobalSections S').mapIso (higherBaseChangeIso H F i) ≪≫
    ((Stacks.Cohomology.AffineBase.cohomologyIsoGlobalSectionsRightDerivedPushforward f' i).app
        ⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩).symm

end Affine

end Stacks.AlgebraicGeometry.FlatBaseChangeDerived

end
