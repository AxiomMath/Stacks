module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleEtaleBaseChangeHFace
public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleBaseChangeSpellings
public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleDerivedBaseChangeFromDegreeZero

/-!
# The base change map of Stacks 0736 on `D⁺` is invertible for an étale square

Let

```
  X' ———→ X
   | f'    | f
   v       v
  Y' ———→ Y
      g
```

be a cartesian square of algebraic spaces over a scheme `S` whose base `g` is **étale**.  This
file proves that the derived base change map `g^*Rf_* ⟶ Rf'_*(g')^*` of **Stacks 0736**, which
this development writes `AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap`, is invertible
at **every** object of `D⁺(𝒪_X)` — with no hypothesis beyond étaleness of `g`, and in particular
with no quasi-coherence of the coefficient and no affineness of either base.

Two existing statements meet here, and the file is the meeting and nothing else.

* `AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_of_isEtale` is the degree-zero base change
  map of an étale square, invertible as a **natural transformation** — at every `𝒪_X`-module, not
  only at the quasi-coherent ones.  It is stated at
  `AlgebraicGeometry.Space.moduleBaseChangeMap`, whose direct images are the modules
  development's.
* `Space.isIso_toposModuleDerivedBaseChangeMap_app_of_isIso_toposModuleBaseChangeMap_app_injective`
  carries invertibility of the degree-zero map at the *ringed-topoi* spelling
  `AlgebraicGeometry.Space.toposModuleBaseChangeMap`, asked at the injective coefficients only, to
  the derived map on `D⁺`, provided `(g')^*` preserves injective objects — which for an étale `g'`
  is `AlgebraicGeometry.Space.preservesInjectiveObjects_modulePullback_of_isEtale`.

What separated them was the identification of the two spellings of the degree-zero map, and that
identification is `AlgebraicGeometry.Space.toposModuleBaseChangeMap_app_eq`:  at an `𝒪_X`-module
the two differ by two components of the comparison
`AlgebraicGeometry.Space.modulePushforwardIso` of **Stacks 03LU**, so invertibility transfers with
no geometric input.  For a cartesian square with `g` étale the source leg `g'` is
étale too (`AlgebraicGeometry.Space.isEtale_of_isPullback`), so the hypothesis on the source leg
is discharged from the same étaleness.

## Main results

* `AlgebraicGeometry.Space.isIso_toposModuleBaseChangeMap_app_of_isEtale`: **the degree-zero base
  change map of an étale square is invertible at the ringed-topoi spelling of the direct image**,
  at every `𝒪_X`-module.
* `AlgebraicGeometry.Space.isIso_toposModuleDerivedBaseChangeMap_app_of_isEtale`: **the derived
  base change map of Stacks 0736 is invertible at every object of `D⁺(𝒪_X)` for a cartesian
  square with étale base.**

## Implementation notes

*Why the degree-zero étale case is available at every coefficient, and the flat case is not.*
`AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_of_isEtale` concludes invertibility of the
whole natural transformation, because its proof is the modules-over-sets cube:  the forgetful
functor to sheaves of sets reflects isomorphisms and carries the étale inverse image to
restriction on the nose, so no property of the coefficient is used.  The flat case
`AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_app_of_isFlat` is a statement about one
quasi-coherent coefficient at a time, and injective `𝒪_X`-modules are not quasi-coherent — which
is why the route taken here is available for an étale `g` and is *not* available for a merely flat
one.  See the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ToposModuleDerivedBaseChangeFromDegreeZero.lean`.

*This is not Stacks 073K, part (1).*  Part (1) asserts invertibility for `g` merely **flat** and
`f` quasi-compact and quasi-separated.  Étale is strictly stronger than flat, and nothing here is
evidence for the flat case:  the one step that makes the argument work — the degree-zero map
invertible at *injective* coefficients — is exactly the step a flat `g` does not supply.  So no
`@[stacks 073K]` attribute is carried here.  What this file is for is the reduction: the
chart-local reduction of part (1) over the affine charts factors each base leg through an étale
chart square and a square over an affine base, and this is the étale square's case, needed both
for the left-hand square of the pasting
`AlgebraicGeometry.Space.isIso_toposModuleDerivedBaseChangeMap_app_paste` and for the chart square
of the reduction's second conjunct.

*Neither `f` nor the coefficient is constrained.*  `f` is an arbitrary morphism of algebraic
spaces:  no quasi-compactness and no quasi-separatedness are asked, because the étale cube does
not use them.  The four exactness binders are the ones
`AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap` is itself defined against — the map
cannot be written without them — and for an étale, hence flat, `g` they are **Stacks 04JC**
through `AlgebraicGeometry.Space.exactFunctor_modulePullback_of_isFlat`.

## References

* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasDerivedCategory.standard enoughInjectives_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' Y Y' : AlgebraicSpaces B S hS}

/-- **The degree-zero base change map of an étale square, at the ringed-topoi spelling of the
direct image.**  For a cartesian square of algebraic spaces whose base `g` is étale, the
component at every `𝒪_X`-module of the map `g^*f_* ⟶ f'_*(g')^*` of
`AlgebraicGeometry.Space.toposModuleBaseChangeMap` is invertible.

This is `AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_of_isEtale` carried across
`AlgebraicGeometry.Space.toposModuleBaseChangeMap_app_eq`, which writes the component of the
ringed-topoi map as the component of the modules one between two components of the comparison
`AlgebraicGeometry.Space.modulePushforwardIso` of **Stacks 03LU** — one of them read through
`g^*`.  Both of those are isomorphisms, so the composite is invertible exactly when the middle
factor is.

No property of `F` is asked, because the modules spelling of the étale case is invertible as a
whole natural transformation. -/
theorem isIso_toposModuleBaseChangeMap_app_of_isEtale {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g) (hg : IsEtale B S hS g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    IsIso ((toposModuleBaseChangeMap f g f' g' sq.w).app F) := by
  have := isIso_moduleBaseChangeMap_of_isEtale B S hS g' f' f g sq hg
  have : IsIso ((moduleBaseChangeMap f g f' g' sq.w).app F) :=
    NatIso.isIso_app_of_isIso _ F
  rw [toposModuleBaseChangeMap_app_eq f g f' g' sq.w F]
  exact ((modulePullback B S hS g).mapIso ((modulePushforwardIso B S hS f).app F) ≪≫
    asIso ((moduleBaseChangeMap f g f' g' sq.w).app F) ≪≫
    ((modulePushforwardIso B S hS f').app
      ((modulePullback B S hS g').obj F)).symm).isIso_hom

/-- **The base change map of Stacks 0736 on `D⁺` is invertible for a cartesian square with étale
base.**  For a cartesian square of algebraic spaces whose base `g` is étale, the derived base
change map `g^*Rf_* ⟶ Rf'_*(g')^*` of
`AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap` is invertible at every object of
`D⁺(𝒪_X)`.

`AlgebraicGeometry.Space.isIso_toposModuleDerivedBaseChangeMap_app_of_isEtale_source` asks two
things of the square:  that the source leg `g'` be étale, which for a cartesian square follows
from étaleness of `g` by `AlgebraicGeometry.Space.isEtale_of_isPullback`, and that the degree-zero
base change map be invertible, which is
`AlgebraicGeometry.Space.isIso_toposModuleBaseChangeMap_app_of_isEtale` above.  Both are discharged
from `hg` alone, so the conclusion is unconditional.

**Étale, not flat:  this is not Stacks 073K, part (1)**, which asserts the same for `g` merely
flat and `f` quasi-compact and quasi-separated.  Étale is strictly stronger than flat and the
argument does not survive the weakening — see the implementation notes of this file.  It is the
étale square's case in the chart-local reduction of part (1). -/
theorem isIso_toposModuleDerivedBaseChangeMap_app_of_isEtale {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    [PreservesFiniteLimits (modulePullback B S hS g)]
    [PreservesFiniteColimits (modulePullback B S hS g)]
    [PreservesFiniteLimits (modulePullback B S hS g')]
    [PreservesFiniteColimits (modulePullback B S hS g')]
    (sq : IsPullback g' f' f g) (hg : IsEtale B S hS g.hom)
    (M : DerivedCategory.Plus (Modules.{u, u} B S hS X.1 X.2)) :
    IsIso ((toposModuleDerivedBaseChangeMap f g f' g' sq.w).app M) :=
  have := preservesInjectiveObjects_modulePullback_of_isEtale g'
    (isEtale_of_isPullback B S hS f' g' g f sq.flip hg)
  isIso_toposModuleDerivedBaseChangeMap_app_of_isIso_toposModuleBaseChangeMap_app_injective
    f g f' g' sq.w (fun N _ => isIso_toposModuleBaseChangeMap_app_of_isEtale sq hg N) M

end AlgebraicGeometry.Space

end
