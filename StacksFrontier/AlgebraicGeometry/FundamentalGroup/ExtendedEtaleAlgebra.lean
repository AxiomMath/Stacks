module

public import StacksFrontier.AlgebraicGeometry.PushforwardCoherent
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The extension algebra of a finite étale cover: coherence of the finite part, and flat base
change

Let `j : U ⟶ X` be an open immersion of locally Noetherian schemes whose complement consists of
points where `𝒪_X` has depth at least two, and let `π : V ⟶ U` be finite étale.
[Stacks, Tag 0EY6] asserts that the algebra `𝓑 = j_* π_* 𝒪_V` is a reflexive coherent
`𝒪_X`-algebra and that its formation commutes with flat base change.

This file lands the two parts of that assertion which do not need the theory of reflexive
extensions across a depth-two complement.

*The finite half of coherence.* The source's proof opens by observing that `π_* 𝒪_V` is a
coherent — indeed finite locally free — `𝒪_U`-module. That is proved here, for an arbitrary
finite morphism and in the algebra-sheaf form in which Tag 0EY6 states its conclusion: the
`𝒪_X`-module underlying `Stacks.AffineAlgebraEquivalence.pushforwardAlgebra f` is *equal* to
`(Scheme.Modules.pushforward f).obj 𝒪_V` (`underlyingModule_pushforwardAlgebra_eq`), so
coherence of the algebra follows from coherence of the direct image along a finite morphism
([Stacks, Tag 01Y6]).

*Flat base change, reduced to one isomorphism.* The base-change clause of Tag 0EY6 asks, at the
level of algebras, that `g⁻¹(f_* 𝒪_V) ⊗_{g⁻¹𝒪_X} 𝒪_{X'}` be `f'_* 𝒪_{V ×_X X'}`, i.e. that the
square exhibiting `f'_* 𝒪_{V ×_X X'}` as an extension of scalars be a pushout. Here that square
is shown to be a pushout as soon as the canonical comparison
`Stacks.AffineAlgebraEquivalence.baseChangeAlgebraHom` is an isomorphism
(`isPushout_pushforwardBaseChangeMap_of_isIso`): the corresponding square for the abstract
algebra pullback is a pushout by `algebraPullback_isPushout`, the comparison matches the two
left-hand legs by `algebraPullbackMap_comp_baseChangeAlgebraHom`, and it matches the two
structure morphisms because it is a morphism of algebras. So the whole of the base-change clause
rests on one isomorphism — which is flat base change for the direct image,
[Stacks, Tag 02KH], and is not proved here.

## Main results

* `Stacks.FundamentalGroup.underlyingModule_pushforwardAlgebra_eq` — the module underlying
  `f_* 𝒪_V` as an algebra is the direct image of the structure sheaf.
* `Stacks.FundamentalGroup.isCoherent_underlyingModule_pushforwardAlgebra` — for a finite
  morphism to a locally Noetherian scheme, `f_* 𝒪_V` is a coherent algebra.
* `Stacks.FundamentalGroup.isCoherent_underlyingModule_pushforwardAlgebra_of_isOpenImmersion` —
  the same for a finite cover of an open subscheme of a locally Noetherian scheme, which is the
  opening step of the proof of [Stacks, Tag 0EY6].
* `Stacks.FundamentalGroup.isPushout_pushforwardBaseChangeMap_of_isIso` — the extension-of-
  scalars square for the direct image is a pushout once the canonical base-change comparison of
  algebras is an isomorphism.

## Implementation notes

**No `@[stacks 0EY6 "algebra"]` or `@[stacks 0EY6 "flat_base_change"]` attribute is placed
here.** Neither covering set is complete: coherence and reflexivity of `j_* π_* 𝒪_V` itself both
need the extension of coherent reflexive modules across a depth-two complement
([Stacks, Tag 0EBJ], which no declaration on this branch carries), and the base-change clause
needs the isomorphism discussed above. A tag on a fraction of a covering set makes the whole tag
render as formalized.

The coherence predicate is written `_root_.SheafOfModules.IsCoherent`, and that is not
cosmetic: this branch carries two distinct coherence constants with identical fields, and inside
the `Stacks.` namespace both the unqualified name and dot notation resolve to the other one,
with no error anywhere. See the implementation notes of
`StacksFrontier/AlgebraicGeometry/PushforwardCoherent.lean`.

`underlyingModule_pushforwardAlgebra_eq` holds by `rfl`, by
`Stacks.AffineAlgebraEquivalence.underlyingModule_pushforwardAlgebra` together with
`Stacks.AlgebraicGeometry.AffineQcohPushforward.restrictScalars_pushforwardModules` and
`pushforwardModules_unit`; it is recorded because the two sides are stated over different
sheaves of rings and nothing makes the identification findable by `simp`.

The underlying isomorphism of sheaves of rings is built by hand in
`rightIsoOfBaseChangeAlgebraHom` rather than as `(Under.forget _).mapIso`, so that its `hom`
field is syntactically `Under.Hom.right (baseChangeAlgebraHom g W)`; with the functorial
spelling the two compatibility conditions of `CategoryTheory.IsPushout.of_iso` are no longer
closed by the existing lemmas without an extra conversion.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

universe u

namespace Stacks.FundamentalGroup

/-! ### Coherence of the direct image algebra along a finite morphism -/

/-- The `𝒪_X`-module underlying the algebra `f_* 𝒪_V` is the direct image of the structure
sheaf of `V`. The two sides are formed differently — the left by restricting scalars along
`f_* 𝒪_V` from the unit module over it, the right by the direct image functor on
`𝒪_V`-modules — and are equal. -/
public theorem underlyingModule_pushforwardAlgebra_eq {V X : Scheme.{u}} (f : V ⟶ X) :
    AlgebraSheaf.underlyingModule (pushforwardAlgebra f) =
      (Scheme.Modules.pushforward f).obj (SheafOfModules.unit V.ringCatSheaf) :=
  rfl

/-- **The direct image algebra along a finite morphism to a locally Noetherian scheme is
coherent.** This is [Stacks, Tag 01Y6] applied to the structure sheaf, read in the
algebra-sheaf form in which [Stacks, Tag 0EY6] states its conclusion. -/
@[ega "III 4.8.6" "special case"]
public theorem isCoherent_underlyingModule_pushforwardAlgebra {V X : Scheme.{u}}
    [IsLocallyNoetherian X] (f : V ⟶ X) [IsFinite f] :
    _root_.SheafOfModules.IsCoherent (AlgebraSheaf.underlyingModule (pushforwardAlgebra f)) :=
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian f
  have : _root_.SheafOfModules.IsCoherent (SheafOfModules.unit V.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  Stacks.AlgebraicGeometry.PushforwardCoherent.pushforward_isCoherent_of_isFinite f
    (SheafOfModules.unit V.ringCatSheaf)

/-- **The opening step of the proof of [Stacks, Tag 0EY6].** For a finite morphism
`π : V ⟶ U` onto an open subscheme of a locally Noetherian scheme `X`, the algebra `π_* 𝒪_V` is
a coherent `𝒪_U`-algebra. Étaleness of `π` is not needed for coherence; the source notes it to
get that `π_* 𝒪_V` is finite locally free, hence reflexive. -/
public theorem isCoherent_underlyingModule_pushforwardAlgebra_of_isOpenImmersion
    {U X V : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    (π : V ⟶ U) [IsFinite π] :
    _root_.SheafOfModules.IsCoherent (AlgebraSheaf.underlyingModule (pushforwardAlgebra π)) :=
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  isCoherent_underlyingModule_pushforwardAlgebra π

/-! ### Flat base change of the direct image algebra -/

/-- The isomorphism of sheaves of rings underlying an invertible base-change comparison of
algebras. -/
public def rightIsoOfBaseChangeAlgebraHom {X X' : Scheme.{u}} (g : X' ⟶ X) (W : Over X)
    (hiso : IsIso (baseChangeAlgebraHom g W)) :
    ((algebraPullback g).obj (pushforwardAlgebra W.hom)).right ≅
      (pushforwardAlgebra ((Over.pullback g).obj W).hom).right where
  hom := (baseChangeAlgebraHom g W).right
  inv := (@inv _ _ _ _ (baseChangeAlgebraHom g W) hiso).right
  hom_inv_id := congrArg Under.Hom.right (@IsIso.hom_inv_id _ _ _ _ _ hiso)
  inv_hom_id := congrArg Under.Hom.right (@IsIso.inv_hom_id _ _ _ _ _ hiso)

/-- **The base-change clause of [Stacks, Tag 0EY6], reduced to one isomorphism.** If the
canonical comparison `baseChangeAlgebraHom` from the extension of scalars of `f_* 𝒪_V` to the
direct image of the structure sheaf of `V ×_X X'` is an isomorphism, then the square
```
g⁻¹𝒪_X ⟶ g⁻¹(f_* 𝒪_V)
   ↓              ↓
 𝒪_{X'} ⟶  f'_* 𝒪_{V ×_X X'}
```
is a pushout, i.e. `f'_* 𝒪_{V ×_X X'} = g⁻¹(f_* 𝒪_V) ⊗_{g⁻¹𝒪_X} 𝒪_{X'}`. The hypothesis is flat
base change for the direct image, [Stacks, Tag 02KH]. -/
public theorem isPushout_pushforwardBaseChangeMap_of_isIso {X X' : Scheme.{u}} (g : X' ⟶ X)
    (W : Over X) (hiso : IsIso (baseChangeAlgebraHom g W)) :
    IsPushout
      ((TopCat.Sheaf.pullback CommRingCat g.base).map (pushforwardAlgebra W.hom).hom)
      (inverseImageStructureMap g)
      (pushforwardBaseChangeMap g W)
      (pushforwardAlgebra ((Over.pullback g).obj W).hom).hom :=
  (algebraPullback_isPushout g (pushforwardAlgebra W.hom)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (rightIsoOfBaseChangeAlgebraHom g W hiso)
    (by simp) (by simp)
    ((Category.id_comp _).trans (algebraPullbackMap_comp_baseChangeAlgebraHom g W))
    ((Category.id_comp _).trans (Under.w (baseChangeAlgebraHom g W)))

end Stacks.FundamentalGroup

end
