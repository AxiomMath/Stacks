module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisGlueingDescentBaseChange

/-!
# The elementary-distinguished-square step of the essential surjectivity half of Stacks 09RJ

Situation 09RH is a directed inverse system `i ↦ X_i` of quasi-compact quasi-separated algebraic
spaces over a scheme `S` with affine transition morphisms, together with a chosen limit `X` and a
chosen index `0`.  The essential surjectivity half of Stacks 09RJ — every perfect object of
`D(𝒪_X)` is the derived pullback of a perfect object of some `D(𝒪_{X_i})` — is proved in the
source by the induction principle of Stacks 08GP over the quasi-compact quasi-separated objects
of `(X_0)_{spaces, étale}`, and its step at an elementary distinguished square glues with
Stacks 08HB.

This file proves **that step**, for one stage and the limit, with nothing assumed beyond the data
the induction hands it.  Concretely: let `(U_0 ⊆ W_0, V_0 ⟶ W_0)` be an elementary distinguished
square, let `p : W ⟶ W_0` and `p' : W' ⟶ W_0` be morphisms with a morphism `q : W' ⟶ W` over
`W_0` — in the application `p` is the base change of `W_0` to a stage `X_i`, `p'` its base change
to the limit `X` and `q` the projection — and base change the square along `p` and along `p'` by
Stacks 08GN (`AlgebraicGeometry.Space.isElementaryDistinguishedSquare_preimage`).  Given an
object `E` of `D(𝒪_{W'})`, perfect objects `A` on the open subspace and `Bo` on the étale
algebraic space of the square over `W` whose derived pullbacks along `q` are the two restrictions
of `E`, and a comparison isomorphism `c` over the intersection compatible with them, there are a
**perfect** object `F` of `D(𝒪_W)` with `F|_{U} ≅ A`, `F|_{V} ≅ Bo` and `Lq^*F ≅ E`.

Perfectness of `E` is *not* a hypothesis: in the application `E` is perfect, being the
restriction of the perfect object of `D(𝒪_X)` being descended, but the step does not use it —
the perfectness of the glued object comes from the perfectness of `A` and of `Bo`.

That is the conclusion the induction's step needs: the objects descended over the two members of
the square are glued into an object descended over the ambient one, and the glued object is
perfect.

## The route taken, and what it does *not* need

Both assertions of Stacks 08HB are already available in this library in the
derived-pullback-pseudofunctor spelling, unconditionally
(`AlgebraicGeometry.Space.exists_glue_derivedPullback_eds` and `…exists_hom_derivedPullback_eds`),
with the compatibility over the intersection expressed as compatibility of the canonical square
isomorphisms of `AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`; the descent of an
object between two base changes of one square is assembled from them in
`AlgebraicGeometry.Space.exists_glue_derivedPullback_iso_of_edsPreimage`.  So the step below needs
**no identification of the composition comparison of the derived-pullback pseudofunctor with
`AlgebraicGeometry.Space.edsDerivedRestrictCompOpen` and `…edsDerivedRestrictCompEtale`**, which
is the comparison recorded as missing elsewhere in the library: every restriction here is a
derived pullback `Lj^*` and every identification of two iterated restrictions is a square
isomorphism of that one pseudofunctor.

What this file adds to those is the single missing ingredient, **perfectness of the glued
object**: perfectness of an object of `D(𝒪_W)` is tested on the two members of the square by
`AlgebraicGeometry.Space.isPerfect_of_isPerfect_edsRestrict`, which is stated for the étale
restriction functors, and
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackIsoOfIsEtale` reads it in the
pseudofunctor spelling.  This is the source's "one checks that `E_i` is perfect".

## Main results

* `AlgebraicGeometry.Space.isPerfect_of_isPerfect_derivedPullback_eds`: **perfectness is local
  for an elementary distinguished square**, read through derived pullbacks, and
  `…isPerfect_of_isPerfect_glueData_derivedPullback_eds` the same with the two restrictions
  prescribed only up to isomorphism.
* `AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_eds`: the first assertion of
  Stacks 08HB for perfect objects, in the pseudofunctor spelling — a perfect object of `D(𝒪_U)`
  and a perfect object of `D(𝒪_V)` identified over `P` are glued by a *perfect* object of
  `D(𝒪_W)`.
* `AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_eds`: the descent of a
  perfect object along a morphism of elementary distinguished squares.
* `AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_edsPreimage`: **the
  elementary-distinguished-square step**, for the two base changes of one square along
  `p : W ⟶ W_0` and `p' : W' ⟶ W_0` with `q : W' ⟶ W` over `W_0`.

## The hypotheses carried, and why each is an input rather than part of the conclusion

Every hypothesis below is either part of the elementary distinguished square and the cube of
Stacks 08GN, or one of the two things the induction of Stacks 08GP hands its step.  No `Prop`
binder stands in for missing mathematics, and no clause of Stacks 09RJ, of Stacks 09RI or of
Stacks 08HB is assumed.

*`A`, `Bo`, `hA`, `hBo`, `αU`, `αV`: the inductive hypotheses at the two members of the square.*
The induction principle of Stacks 08GP gives the step the property it is proving at the open
subspace `U`, at the étale algebraic space `V` and at the intersection `P`.  At `U` and at `V`
that property is exactly "the restriction of `E` is the derived pullback of a perfect object at
the stage", which is the perfect object `A` with the isomorphism `αU`, and the perfect object
`Bo` with `αV`.  They are the hypothesis of the step, not its conclusion; the step's conclusion
is the same statement at the ambient space `W`.

*`c` and `hc`: the comparison isomorphism over the intersection.*  In the source this is produced
from the inductive hypothesis at `P` by the full faithfulness half of Stacks 09RJ, which is
Stacks 09RI, after advancing the two stages carrying `A` and `Bo` to a common one; that
production is a statement about the inverse system and is not part of the square step.  Here `c`
is an argument, together with the compatibility `hc` saying that its derived pullback to the
intersection of the square over `W'` is the comparison of `αU` and `αV` read through the square
isomorphisms of the cube — which is precisely what the production delivers.  Nothing below
mentions an inverse system.

*`p`, `p'`, `q`, `hq`: the morphism of base changes.*  These are the geometry of Situation 09RH
at the square, not an assumption about it: `p` and `p'` are arbitrary morphisms to `W_0` and `q`
is an arbitrary morphism over `W_0`.

## What is not here

*The induction itself, and the production of `c`.*  Running the induction of Stacks 08GP needs
Situation 09RH base changed along an arbitrary quasi-compact quasi-separated algebraic space
étale over `X_0`, so that "the stages of `W_0`" and "the limit of `W_0`" are the stages and the
limit of a descent situation; the production of `c` then needs the identification of the
hom-level colimit maps of that base-changed situation with the derived pullbacks appearing in
`hc`.  Neither is in this library, and neither is assumed below: the statements here are about
one morphism `q : W' ⟶ W` over `W_0` and take `c` as given.

*The affine base case.*  The induction of Stacks 08GP starts from the affine objects of
`(X_0)_{spaces, étale}`; that case is not in this library and is not assumed below, no statement
here mentioning an affine object.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Lemma 75.10.8 (Tag 08HB)](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Lemma 75.9.1 (Tag 08GN)](https://stacks.math.columbia.edu/tag/08GN)
* [Stacks Project, Lemma 75.13.4 (Tag 08H6)](https://stacks.math.columbia.edu/tag/08H6)
* [Stacks Project, Definition 36.11.1 (Tag 0F8I)](https://stacks.math.columbia.edu/tag/0F8I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Perfectness is local for an elementary distinguished square, and the glued object -/

section Locality

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **Perfectness in `D(𝒪_W)` is local for an elementary distinguished square**, read through
derived pullbacks: an object whose derived pullbacks to the open subspace `U` and to the étale
algebraic space `V` are perfect is perfect.

This is `AlgebraicGeometry.Space.isPerfect_of_isPerfect_edsRestrict`, which is stated for the
étale restriction functors, read through
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackIsoOfIsEtale`; the two members of the
square cover it, so perfectness is tested on them. -/
theorem isPerfect_of_isPerfect_derivedPullback_eds
    (F : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W)))
    (hU : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1
        (edsOpen B S hS hsq).2).IsPerfect
      ((smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS hsq)).obj F))
    (hV : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2).IsPerfect
      ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).obj F)) :
    (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect F :=
  isPerfect_of_isPerfect_edsRestrict B S hS hsq F
    (RingedSite.IsPerfect.of_iso
      (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2) hU
      ((smallEtaleDerivedModulePullbackIsoOfIsEtale B S hS _
        (isEtale_edsOpenHom B S hS hsq)).app F))
    (RingedSite.IsPerfect.of_iso
      (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2) hV
      ((smallEtaleDerivedModulePullbackIsoOfIsEtale B S hS _
        (isEtale_edsEtaleHom B S hS hsq)).app F))

variable {A : DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (edsOpen B S hS hsq)))}
  {Bo : DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq)))}

/-- **An object of `D(𝒪_W)` restricting to perfect objects on the two members of an elementary
distinguished square is perfect**, the restrictions being prescribed up to isomorphism.  This is
`AlgebraicGeometry.Space.isPerfect_of_isPerfect_derivedPullback_eds` with the two perfectness
hypotheses transported along the given isomorphisms. -/
theorem isPerfect_of_isPerfect_glueData_derivedPullback_eds
    (F : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W)))
    (f : (smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS hsq)).obj F ≅ A)
    (g : (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).obj F ≅ Bo)
    (hA : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1
      (edsOpen B S hS hsq).2).IsPerfect A)
    (hBo : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2).IsPerfect Bo) :
    (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect F :=
  isPerfect_of_isPerfect_derivedPullback_eds hsq F
    (RingedSite.IsPerfect.of_iso
      (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2) hA f.symm)
    (RingedSite.IsPerfect.of_iso
      (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2) hBo g.symm)

/-- **The first assertion of Stacks 08HB for perfect objects**, in the derived-pullback
pseudofunctor spelling.  A perfect object `A` of `D(𝒪_U)` and a perfect object `Bo` of `D(𝒪_V)`
together with an isomorphism `c : A|_P ≅ Bo|_P` are glued by a **perfect** object `F` of
`D(𝒪_W)`, by isomorphisms `f : F|_U ≅ A` and `g : F|_V ≅ Bo` whose restrictions to `P` are
compatible with `c` through the square isomorphism of the cartesian square of the elementary
distinguished square.

The glueing is `AlgebraicGeometry.Space.exists_glue_derivedPullback_eds` and the perfectness of
the glued object is `AlgebraicGeometry.Space.isPerfect_of_isPerfect_glueData_derivedPullback_eds`;
nothing beyond the square and the perfectness of `A` and `Bo` is assumed. -/
theorem exists_glue_isPerfect_derivedPullback_eds
    (hA : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1
      (edsOpen B S hS hsq).2).IsPerfect A)
    (hBo : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2).IsPerfect Bo)
    (c : (smallEtaleDerivedModulePullback B S hS (edsFst B S hS hsq)).obj A ≅
      (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS hsq)).obj Bo) :
    ∃ (F : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W)))
      (f : (smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS hsq)).obj F ≅ A)
      (g : (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).obj F ≅ Bo),
      (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect F ∧
      (smallEtaleDerivedModulePullback B S hS (edsFst B S hS hsq)).map f.hom ≫ c.hom =
        ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq)
          (edsEtaleHom B S hS hsq) (edsFst B S hS hsq) (edsOpenHom B S hS hsq)
          (isPullback_edsInter B S hS hsq).flip.w).hom.app F ≫
        (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS hsq)).map g.hom := by
  obtain ⟨F, f, g, hfg⟩ := exists_glue_derivedPullback_eds hsq A Bo c
  exact ⟨F, f, g, isPerfect_of_isPerfect_glueData_derivedPullback_eds hsq F f g hA hBo, hfg⟩

end Locality

/-! ### The square step -/

section SquareStep

/-- **Descending a perfect object along a morphism of elementary distinguished squares.**  In the
situation of `AlgebraicGeometry.Space.exists_glue_derivedPullback_iso_of_eds` — two elementary
distinguished squares and a commutative cube between them — let `E` be an object of `D(𝒪_{W'})`,
let `A` on the open subspace and `Bo` on the étale algebraic space of the square over `W` be
**perfect**, let `αU : Lp_U^*A ≅ E|_{U'}` and `αV : Lp_V^*Bo ≅ E|_{V'}`, and let
`c : A|_P ≅ Bo|_P` be compatible with them over the intersection `P'` (`hc`).  Then there is a
**perfect** object `F` of `D(𝒪_W)` with `F|_U ≅ A`, `F|_V ≅ Bo` and `Lp^*F ≅ E`.

The object and the three isomorphisms are
`AlgebraicGeometry.Space.exists_glue_derivedPullback_iso_of_eds`; what is added is that `F` is
perfect, by `AlgebraicGeometry.Space.isPerfect_of_isPerfect_glueData_derivedPullback_eds`. -/
theorem exists_glue_isPerfect_derivedPullback_iso_of_eds
    {W W' : AlgebraicSpaces B S hS} {V V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Uo : Subfunctor W.1} {Uo' : Subfunctor W'.1} {fV : V ⟶ W.1} {fV' : V' ⟶ W'.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (hsq' : IsElementaryDistinguishedSquare B S hS W'.2 Uo' fV')
    (p : W' ⟶ W) (pU : edsOpen B S hS hsq' ⟶ edsOpen B S hS hsq)
    (pV : edsEtale B S hS hsq' ⟶ edsEtale B S hS hsq)
    (pP : edsInter B S hS hsq' ⟶ edsInter B S hS hsq)
    (hU : edsOpenHom B S hS hsq' ≫ p = pU ≫ edsOpenHom B S hS hsq)
    (hV : edsEtaleHom B S hS hsq' ≫ p = pV ≫ edsEtaleHom B S hS hsq)
    (hPU : edsFst B S hS hsq' ≫ pU = pP ≫ edsFst B S hS hsq)
    (hPV : edsSnd B S hS hsq' ≫ pV = pP ≫ edsSnd B S hS hsq)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W')))
    (A : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsOpen B S hS hsq))))
    (Bo : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq))))
    (hA : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1
      (edsOpen B S hS hsq).2).IsPerfect A)
    (hBo : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2).IsPerfect Bo)
    (αU : (smallEtaleDerivedModulePullback B S hS pU).obj A ≅
      (smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS hsq')).obj E)
    (αV : (smallEtaleDerivedModulePullback B S hS pV).obj Bo ≅
      (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq')).obj E)
    (c : (smallEtaleDerivedModulePullback B S hS (edsFst B S hS hsq)).obj A ≅
      (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS hsq)).obj Bo)
    (hc : (smallEtaleDerivedModulePullback B S hS pP).map c.hom =
      ((DerivedPullbackComposition.canonical B S hS).squareIso (edsFst B S hS hsq') pU pP
          (edsFst B S hS hsq) hPU).hom.app A ≫
        (smallEtaleDerivedModulePullback B S hS (edsFst B S hS hsq')).map αU.hom ≫
        ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq')
          (edsEtaleHom B S hS hsq') (edsFst B S hS hsq') (edsOpenHom B S hS hsq')
          (isPullback_edsInter B S hS hsq').flip.w).hom.app E ≫
        (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS hsq')).map αV.inv ≫
        ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq') pV pP
          (edsSnd B S hS hsq) hPV).inv.app Bo) :
    ∃ (F : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W)))
      (_ : (smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS hsq)).obj F ≅ A)
      (_ : (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).obj F ≅ Bo),
      (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect F ∧
        Nonempty ((smallEtaleDerivedModulePullback B S hS p).obj F ≅ E) := by
  obtain ⟨F, f, g, hFE⟩ := exists_glue_derivedPullback_iso_of_eds hsq hsq' p pU pV pP hU hV hPU
    hPV E A Bo αU αV c hc
  exact ⟨F, f, g, isPerfect_of_isPerfect_glueData_derivedPullback_eds hsq F f g hA hBo, hFE⟩

variable {W₀ : AlgebraicSpaces B S hS} {V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {U₀ : Subfunctor W₀.1} {f₀ : V₀ ⟶ W₀.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W₀.2 U₀ f₀)
  {W W' : AlgebraicSpaces B S hS} (p : W ⟶ W₀) (p' : W' ⟶ W₀) (q : W' ⟶ W)
  (hq : q ≫ p = p')

/-- **The elementary-distinguished-square step of the essential surjectivity half of
Stacks 09RJ.**  Let `(U_0 ⊆ W_0, V_0 ⟶ W_0)` be an elementary distinguished square, let
`p : W ⟶ W_0` and `p' : W' ⟶ W_0` be morphisms of algebraic spaces and let `q : W' ⟶ W` be a
morphism over `W_0`; by Stacks 08GN the square base changes to elementary distinguished squares
of `W` and of `W'` and `q` induces a morphism between them.  Let `E` be an object of
`D(𝒪_{W'})`, let `A` and `Bo` be **perfect** objects on the open subspace and on the étale
algebraic space of the square over `W` whose derived pullbacks along `q` are the two restrictions
of `E` (`αU`, `αV`), and let `c : A|_P ≅ Bo|_P` be a comparison isomorphism over the intersection
compatible with them (`hc`).  Then there is a **perfect** object `F` of `D(𝒪_W)` with `F|_U ≅ A`,
`F|_V ≅ Bo` and `Lq^*F ≅ E`.

In Situation 09RH `W_0` is an object of `(X_0)_{spaces, étale}`, `p` is the base change of `W_0`
to a stage `X_i`, `p'` its base change to the limit `X` and `q` the projection, `E` is the
restriction to `W'` of the perfect object of `D(𝒪_X)` being descended, and `A`, `Bo`, `αU`, `αV`
are the inductive hypotheses of Stacks 08GP at the two members of the square.  The conclusion is
the same statement at `W_0`, which is what the step of the induction has to produce.

This is `AlgebraicGeometry.Space.exists_glue_derivedPullback_iso_of_edsPreimage` with the
perfectness of the glued object added.  See "The hypotheses carried" in this file's module
documentation for each hypothesis and why it is an input of the source's proof; in particular the
comparison isomorphism `c` is an argument here, the source's production of it from Stacks 09RI
being a statement about the inverse system and not part of this step. -/
theorem exists_glue_isPerfect_derivedPullback_iso_of_edsPreimage
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W')))
    (A : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsOpen B S hS (edsPreimage hsq p)))))
    (Bo : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS (edsPreimage hsq p)))))
    (hA : (smallEtaleRingedSite B S hS (edsOpen B S hS (edsPreimage hsq p)).1
      (edsOpen B S hS (edsPreimage hsq p)).2).IsPerfect A)
    (hBo : (smallEtaleRingedSite B S hS (edsEtale B S hS (edsPreimage hsq p)).1
      (edsEtale B S hS (edsPreimage hsq p)).2).IsPerfect Bo)
    (αU : (smallEtaleDerivedModulePullback B S hS (edsPreimageOpenMap hsq p p' q hq)).obj A ≅
      (smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS (edsPreimage hsq p'))).obj E)
    (αV : (smallEtaleDerivedModulePullback B S hS (edsPreimageEtaleMap hsq p p' q hq)).obj Bo ≅
      (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS (edsPreimage hsq p'))).obj E)
    (c : (smallEtaleDerivedModulePullback B S hS (edsFst B S hS (edsPreimage hsq p))).obj A ≅
      (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS (edsPreimage hsq p))).obj Bo)
    (hc : (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq p p' q hq)).map c.hom =
      ((DerivedPullbackComposition.canonical B S hS).squareIso
          (edsFst B S hS (edsPreimage hsq p')) (edsPreimageOpenMap hsq p p' q hq)
          (edsPreimageInterMap hsq p p' q hq) (edsFst B S hS (edsPreimage hsq p))
          (edsFst_comp_edsPreimageOpenMap hsq p p' q hq)).hom.app A ≫
        (smallEtaleDerivedModulePullback B S hS (edsFst B S hS (edsPreimage hsq p'))).map
          αU.hom ≫
        ((DerivedPullbackComposition.canonical B S hS).squareIso
          (edsSnd B S hS (edsPreimage hsq p')) (edsEtaleHom B S hS (edsPreimage hsq p'))
          (edsFst B S hS (edsPreimage hsq p')) (edsOpenHom B S hS (edsPreimage hsq p'))
          (isPullback_edsInter B S hS (edsPreimage hsq p')).flip.w).hom.app E ≫
        (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS (edsPreimage hsq p'))).map
          αV.inv ≫
        ((DerivedPullbackComposition.canonical B S hS).squareIso
          (edsSnd B S hS (edsPreimage hsq p')) (edsPreimageEtaleMap hsq p p' q hq)
          (edsPreimageInterMap hsq p p' q hq) (edsSnd B S hS (edsPreimage hsq p))
          (edsSnd_comp_edsPreimageEtaleMap hsq p p' q hq)).inv.app Bo) :
    ∃ (F : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W)))
      (_ : (smallEtaleDerivedModulePullback B S hS
        (edsOpenHom B S hS (edsPreimage hsq p))).obj F ≅ A)
      (_ : (smallEtaleDerivedModulePullback B S hS
        (edsEtaleHom B S hS (edsPreimage hsq p))).obj F ≅ Bo),
      (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect F ∧
        Nonempty ((smallEtaleDerivedModulePullback B S hS q).obj F ≅ E) :=
  exists_glue_isPerfect_derivedPullback_iso_of_eds (edsPreimage hsq p) (edsPreimage hsq p') q
    (edsPreimageOpenMap hsq p p' q hq) (edsPreimageEtaleMap hsq p p' q hq)
    (edsPreimageInterMap hsq p p' q hq) (edsPreimageOpenMap_comp hsq p p' q hq)
    (edsPreimageEtaleMap_comp hsq p p' q hq) (edsFst_comp_edsPreimageOpenMap hsq p p' q hq)
    (edsSnd_comp_edsPreimageEtaleMap hsq p p' q hq) E A Bo hA hBo αU αV c hc

end SquareStep

end AlgebraicGeometry.Space

end
