module

public import StacksFrontier.AlgebraicGeometry.Duality.InvertibleTwistInternalHom
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedDualizingTransitivity
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback

/-!
# Glueing dualizing complexes: the twisted inverse image built from duality

Fix a Noetherian scheme `S` carrying a dualizing complex `ω_S^•` — Situation
[Stacks, Tag 0AU4] — and, for each scheme `X` of finite type over `S`, a complex `ω_X^•`
normalized relative to `ω_S^•` in the sense of [Stacks, Tag 0AU5]. Write
`D_X(-) = R𝓗om_{𝒪_X}(-, ω_X^•)`. For a morphism `f : X ⟶ Y` of schemes of finite type over
`S`, [Stacks, Tag 0AUE] part (5) gives the formula

`f_new^! M = D_X(Lf^* D_Y(M))`,

and this file takes that formula as the *definition* of `f_new^!`. The point of doing so is
that it needs no compactification and no `f^!`: the right hand side is a derived internal hom
against a fixed complex, a derived pullback, and a second derived internal hom.

The result of the file is the independence of `f_new^!` of the choice of `ω_S^•`,
[Stacks, Tag 0BV3]. By [Stacks, Tag 0ATP] a second dualizing complex on `S` is
`ω_S^• ⊗^L ℒ` for an invertible object `ℒ` of `D(𝒪_S)`, and by [Stacks, Tag 0A9T] the
normalized complexes upstairs are then replaced by `ω_X^• ⊗^L Lπ_X^*ℒ` and
`ω_Y^• ⊗^L Lπ_Y^*ℒ`. The computation

`D_X^new(K) ≅ D_X(K) ⊗ Lπ_X^*ℒ`,
`f_new^!,new M = D_X(Lf^*(D_Y M) ⊗ Lπ_X^*ℒ) ⊗ Lπ_X^*ℒ ≅ D_X(Lf^* D_Y M) = f_new^! M`

is then pure closed-monoidal algebra with an invertible object, carried out in
`StacksFrontier/AlgebraicGeometry/Duality/InvertibleTwistInternalHom.lean`, together with the
compatibility `Lf^* Lπ_Y^* ≅ Lπ_X^*` of
`Stacks.Duality.derivedPullbackCompIso`.

## Main definitions

All in the namespace `Stacks.Duality`.

* `DualizingBase` — **[Stacks, Tag 0AU4]**, the standing situation: a Noetherian scheme
  together with a dualizing complex on it.
* `FiniteTypeOverBase` — a scheme of finite type over that base, with a chosen complex playing
  the role of the normalized dualizing complex of [Stacks, Tag 0AU5].
* `relativeDual` — `D_X(-) = R𝓗om_{𝒪_X}(-, ω_X^•)`, as a functor `D(𝒪_X)ᵒᵖ ⥤ D(𝒪_X)`.
* `fNewShriek` — `f_new^! = D_X ∘ Lf^* ∘ D_Y`, the formula of [Stacks, Tag 0AUE] part (5), as a
  functor `D(𝒪_Y) ⥤ D(𝒪_X)`.
* `basePullbackTwistIso` — the comparison `Lf^*(Lb^*ℒ) ≅ La^*ℒ` for a factorization
  `f ≫ b = a` of structure morphisms.
* `relativeDualTwistTargetIso`, `relativeDualTwistSourceIso`, `relativeDualTwistCancelIso` —
  how `D_X` reacts to twisting its complex, and to twisting its argument.

## Main results

* `Stacks.Duality.fNewShriekTwistIso` — **[Stacks, Tag 0BV3]**: twisting `ω_X^•` by an
  invertible `ℒ_X` and `ω_Y^•` by an invertible `ℒ_Y` compatibly does not change `f_new^!`, as
  an isomorphism of functors.
* `Stacks.Duality.fNewShriekBaseTwistIso` — the same with the twists pulled back from the base,
  which is the shape [Stacks, Tag 0BV3] is stated in.
* `Stacks.Duality.dualizingIsoRightAdjointObj` — **[Stacks, Tag 0AUD]**: for a proper `f` the
  right adjoint of `Rf_*` carries `ω_Y^•` to `ω_X^•`.

## Implementation notes

*What is a parameter and why.* Three pieces of structure on `D(𝒪_X)` that the source uses
freely are not yet available in this repository at the model of the derived category which
`Stacks.Duality.derivedPullback` lives at, and are therefore instance arguments or explicit
hypotheses here:

* the symmetric monoidal structure `- ⊗^L_{𝒪_X} -` of [Stacks, Tag 06YU], as
  `[MonoidalCategory (DerivedCategory X.Modules)]` and `[BraidedCategory …]`;
* the derived internal hom `R𝓗om_{𝒪_X}(-, -)` of [Stacks, Tag 08DH] together with its
  tensor–hom bijection [Stacks, Tag 08DI], as `[MonoidalClosed (DerivedCategory X.Modules)]`
  — this is exactly the content of
  `Stacks.SheafOfModules.derivedSheafHom` and
  `Stacks.SheafOfModules.derivedSheafHomTensorEquiv`, which are available only at
  `HasDerivedCategory.standard` and so cannot be used in the same statement as
  `Stacks.Duality.derivedPullback`;
* monoidality of `Lf^*`, [Stacks, Tag 0B54], as the family of comparison isomorphisms
  `Lf^*(A ⊗ B) ≅ Lf^*A ⊗ Lf^*B` named `tf` below. Only its values on objects are used, so no
  coherence is asked for.

None of these is a part of [Stacks, Tag 0BV3]; each is an input the source already has.

*`ℒ` is an input, not a choice.* [Stacks, Tag 0ATP] is an existence statement — some invertible
`ℒ` with `ω' ≅ ω_S^• ⊗^L ℒ` exists — and nothing below applies it. The invertible object, its
chosen two-sided inverse, and the identifications of the twisted complexes are hypotheses, which
is also how [Stacks, Tag 0BV3] reads: *any* second dualizing complex is of that form, and the
comparison is built for each one.

*The comparison is an isomorphism of functors.* Every step of it is natural in the
contravariant variable of the internal hom, because the twisting isomorphisms it is built from
come from `Stacks.Duality.parametrizedRightAdjointUniq`, uniqueness of the right adjoint of an
adjunction *with a parameter*, the parameter being that contravariant variable.

*Why [Stacks, Tag 0AUE] carries no attribute.* Part (5) of that lemma is the formula
`f_new^! M = D_X(Lf^* D_Y M)`, and `fNewShriek` is *defined* by that formula, so
`fNewShriek_obj` holds by `rfl`. In the source part (5) is a theorem about an `f_new^!` built
by the glueing construction; proved by `rfl` against a definition that already is the formula
it asserts, it is a tautology and must not carry the tag.

*The right adjoint in [Stacks, Tag 0AUD].* `Stacks.Duality.twistedInverseImage` is
[Stacks, Tag 0A9E]'s right adjoint, but it lives on `quasiCoherentDerivedCategory` at a free
model of the derived category, where `Stacks.Duality.derivedPullback` cannot be read. The
statement below is therefore taken over the arbitrary family of categories `𝒟` that
`Stacks.Duality.UpperShriek` is already indexed by, which a consumer instantiates at
`quasiCoherentDerivedCategory` with `a := Stacks.Duality.twistedInverseImage f hpush`.

## References

* [Stacks Project, Tag 0AU4](https://stacks.math.columbia.edu/tag/0AU4)
* [Stacks Project, Tag 0AU5](https://stacks.math.columbia.edu/tag/0AU5)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 0A9T](https://stacks.math.columbia.edu/tag/0A9T)
* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
* [Stacks Project, Tag 0AUD](https://stacks.math.columbia.edu/tag/0AUD)
* [Stacks Project, Tag 0BV3](https://stacks.math.columbia.edu/tag/0BV3)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed Opposite

universe v v' v₁ v₂ u u₁ u₂

namespace Stacks.Duality

/-! ### The standing situation -/

/-- **Stacks Project, Tag 0AU4.** The standing situation of the section on glueing dualizing
complexes: a Noetherian scheme `S` together with a dualizing complex `ω_S^•` on it, in the
sense of [Stacks, Tag 0A87]. -/
@[stacks 0AU4 "the Situation: a Noetherian scheme with a chosen dualizing complex"]
structure DualizingBase where
  /-- The base scheme `S`. -/
  scheme : Scheme.{u}
  /-- `S` is Noetherian. -/
  [noetherian : AlgebraicGeometry.IsNoetherian scheme]
  /-- The complex `ω_S^•`. -/
  dualizing : DerivedCategory scheme.Modules
  /-- `ω_S^•` is a dualizing complex. -/
  isDualizing : IsDualizingComplex dualizing

attribute [instance] DualizingBase.noetherian

/-- A scheme of finite type over the base of [Stacks, Tag 0AU4], together with a chosen object
of `D(𝒪_X)` playing the role of the complex `ω_X^•` normalized relative to `ω_S^•` of
[Stacks, Tag 0AU5].

The normalization condition itself is not imposed: it is a condition on the upper shriek
functors of [Stacks, Tag 0A9Y], which this repository does not carry, and nothing below uses
it — the comparison of [Stacks, Tag 0BV3] only ever sees how `ω_X^•` changes when the base
complex is twisted. -/
structure FiniteTypeOverBase (B : DualizingBase.{u}) where
  /-- The scheme `X`. -/
  scheme : Scheme.{u}
  /-- The structure morphism `X ⟶ S`. -/
  str : scheme ⟶ B.scheme
  /-- `X` is of finite type over the Noetherian base `S`. -/
  finiteType : IsFiniteTypeOverNoetherian str
  /-- The complex `ω_X^•`. -/
  dualizing : DerivedCategory scheme.Modules

/-! ### The duality functor and `f_new^!` -/

section Functors

variable {X Y : Scheme.{u}}
  [MonoidalCategory (DerivedCategory X.Modules)] [MonoidalClosed (DerivedCategory X.Modules)]
  [MonoidalCategory (DerivedCategory Y.Modules)] [MonoidalClosed (DerivedCategory Y.Modules)]

/-- `D_X(-) = R𝓗om_{𝒪_X}(-, ω_X^•)`, the duality functor of [Stacks, Tag 0AUE] relative to a
chosen complex `ω_X^•` on `X`. -/
def relativeDual (ω : DerivedCategory X.Modules) :
    (DerivedCategory X.Modules)ᵒᵖ ⥤ DerivedCategory X.Modules :=
  MonoidalClosed.internalHom.flip.obj ω

/-- `D_X(K) = R𝓗om_{𝒪_X}(K, ω_X^•)`, the value of `relativeDual ω` at `K`. -/
@[simp]
theorem relativeDual_obj (ω K : DerivedCategory X.Modules) :
    (relativeDual ω).obj (op K) = (ihom K).obj ω :=
  rfl

/-- **The formula of [Stacks, Tag 0AUE] part (5), taken as a definition.** For a morphism
`f : X ⟶ Y` of schemes of finite type over the base, and chosen complexes `ω_X^•` and `ω_Y^•`,

`f_new^! M = D_X(Lf^* D_Y(M))`.

No compactification and no `f^!` enter: the right hand side is `R𝓗om_{𝒪_X}(-, ω_X^•)` applied
to the derived pullback of `R𝓗om_{𝒪_Y}(M, ω_Y^•)`. -/
def fNewShriek (f : X ⟶ Y) (ωX : DerivedCategory X.Modules) (ωY : DerivedCategory Y.Modules) :
    DerivedCategory Y.Modules ⥤ DerivedCategory X.Modules :=
  (relativeDual ωY).rightOp ⋙ (derivedPullback f).op ⋙ relativeDual ωX

/-- `f_new^! M = R𝓗om_{𝒪_X}(Lf^* R𝓗om_{𝒪_Y}(M, ω_Y^•), ω_X^•)`, the value of
`fNewShriek f ωX ωY` at `M`. -/
@[simp]
theorem fNewShriek_obj (f : X ⟶ Y) (ωX : DerivedCategory X.Modules)
    (ωY : DerivedCategory Y.Modules) (M : DerivedCategory Y.Modules) :
    (fNewShriek f ωX ωY).obj M =
      (ihom ((derivedPullback f).obj ((ihom M).obj ωY))).obj ωX :=
  rfl

end Functors

/-! ### Opposite functors -/

/-- `CategoryTheory.Functor.rightOp` carries an isomorphism of functors `Cᵒᵖ ⥤ D` to one of
functors `C ⥤ Dᵒᵖ`. -/
def natIsoRightOp {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {F F' : Cᵒᵖ ⥤ D} (e : F ≅ F') : F.rightOp ≅ F'.rightOp :=
  NatIso.ofComponents (fun Z => (e.symm.app (op Z)).op)
    (fun u => Quiver.Hom.unop_inj (by simp))

/-! ### Twisting the chosen complex by an invertible object -/

section Twist

variable {X : Scheme.{u}}
  [MonoidalCategory (DerivedCategory X.Modules)] [MonoidalClosed (DerivedCategory X.Modules)]

/-- An isomorphism of the chosen complexes induces one of the duality functors. -/
def relativeDualMapIso {ω ω' : DerivedCategory X.Modules} (e : ω ≅ ω') :
    relativeDual ω ≅ relativeDual ω' :=
  MonoidalClosed.internalHom.flip.mapIso e

/-- **`D_X` for a twisted complex**: `R𝓗om(−, ω ⊗ ℒ) ≅ R𝓗om(−, ω) ⊗ ℒ` for an invertible `ℒ`,
as an isomorphism of functors on `D(𝒪_X)ᵒᵖ`. -/
def relativeDualTwistTargetIso (ω : DerivedCategory X.Modules)
    {L : DerivedCategory X.Modules} (h : HasInverse L) :
    relativeDual (ω ⊗ L) ≅ relativeDual ω ⋙ tensorRight L :=
  NatIso.ofComponents (fun K => ((ihomTensorRightCommBifunctor h).app K).app ω)
    (fun φ => NatTrans.congr_app ((ihomTensorRightCommBifunctor h).hom.naturality φ) ω)

/-- **`D_X` on a twisted argument**: `R𝓗om(− ⊗ ℒ, ω) ≅ R𝓗om(ℒ, R𝓗om(−, ω))`, as an
isomorphism of functors on `D(𝒪_X)ᵒᵖ`. -/
def relativeDualTwistSourceIso (ω L : DerivedCategory X.Modules) :
    (tensorRight L).op ⋙ relativeDual ω ≅ relativeDual ω ⋙ ihom L :=
  NatIso.ofComponents (fun K => ((ihomTensorLeftCompBifunctor L).app K).app ω)
    (fun φ => NatTrans.congr_app ((ihomTensorLeftCompBifunctor L).hom.naturality φ) ω)

variable [BraidedCategory (DerivedCategory X.Modules)]

/-- **The cancellation of a twist against itself**: `R𝓗om(− ⊗ ℒ, ω ⊗ ℒ) ≅ R𝓗om(−, ω)` for an
invertible `ℒ`, as an isomorphism of functors on `D(𝒪_X)ᵒᵖ`. -/
def relativeDualTwistCancelIso (ω : DerivedCategory X.Modules)
    {L : DerivedCategory X.Modules} (h : HasInverse L) :
    (tensorRight L).op ⋙ relativeDual (ω ⊗ L) ≅ relativeDual ω :=
  Functor.isoWhiskerLeft (tensorRight L).op (relativeDualTwistTargetIso ω h) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (relativeDualTwistSourceIso ω L) (tensorRight L) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (relativeDual ω) (ihomIsoTensorLeftInv h)) (tensorRight L) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (relativeDual ω) (tensorLeftInvTensorRightIso h) ≪≫
    (relativeDual ω).rightUnitor

end Twist

/-! ### Independence of `f_new^!` of the twist -/

section TwistFunctor

variable {X Y : Scheme.{u}}
  [MonoidalCategory (DerivedCategory X.Modules)] [BraidedCategory (DerivedCategory X.Modules)]
  [MonoidalClosed (DerivedCategory X.Modules)]
  [MonoidalCategory (DerivedCategory Y.Modules)] [MonoidalClosed (DerivedCategory Y.Modules)]

/-- The twist comparison for `Lf^*`, read on the opposite categories. -/
def derivedPullbackTwistOpIso (f : X ⟶ Y)
    {LX : DerivedCategory X.Modules} {LY : DerivedCategory Y.Modules}
    (tw : tensorRight LY ⋙ derivedPullback f ≅ derivedPullback f ⋙ tensorRight LX) :
    (tensorRight LY).op ⋙ (derivedPullback f).op ≅
      (derivedPullback f).op ⋙ (tensorRight LX).op :=
  NatIso.op tw.symm

/-- **Stacks Project, Tag 0BV3.** `f_new^!` does not depend on the choice of the dualizing
complex on the base.

Let `f : X ⟶ Y` be a morphism of schemes of finite type over the base of [Stacks, Tag 0AU4].
Replacing `ω_S^•` by a second dualizing complex replaces it by `ω_S^• ⊗ ℒ` for an invertible
`ℒ` in `D(𝒪_S)` ([Stacks, Tag 0ATP]), and the complexes normalized relative to it by the twists
`ω_X^• ⊗ Lπ_X^*ℒ` and `ω_Y^• ⊗ Lπ_Y^*ℒ` ([Stacks, Tag 0A9T]). This says that the two resulting
functors `f_new^!` are canonically isomorphic — an isomorphism of functors, not merely a family
of isomorphisms of objects.

The computation is the one sketched in the source. The twist passes through the target variable
of `R𝓗om` by `Stacks.Duality.relativeDualTwistTargetIso`, is carried across `Lf^*` by `tw`, and
cancels against the outer twist by `Stacks.Duality.relativeDualTwistCancelIso`; each of those is
natural in the contravariant variable because it comes from
`Stacks.Duality.parametrizedRightAdjointUniq`. The source's `p^!` does not appear: it is one
route to the middle step and is not needed. -/
@[stacks 0BV3 "RESTRICTED: the closed symmetric monoidal structure on the derived categories is
an instance argument; the invertible twist with a chosen two-sided inverse, the identification
of the twisted normalized complexes, and the compatibility of the derived pullback with the
twist are hypotheses"]
def fNewShriekTwistIso (f : X ⟶ Y)
    {ωX ωX' : DerivedCategory X.Modules} {ωY ωY' : DerivedCategory Y.Modules}
    {LX : DerivedCategory X.Modules} (hX : HasInverse LX)
    {LY : DerivedCategory Y.Modules} (hY : HasInverse LY)
    (eX : ωX' ≅ ωX ⊗ LX) (eY : ωY' ≅ ωY ⊗ LY)
    (tw : tensorRight LY ⋙ derivedPullback f ≅ derivedPullback f ⋙ tensorRight LX) :
    fNewShriek f ωX' ωY' ≅ fNewShriek f ωX ωY :=
  Functor.isoWhiskerRight
      (natIsoRightOp (relativeDualMapIso eY ≪≫ relativeDualTwistTargetIso ωY hY) ≪≫
        Functor.rightOpComp (relativeDual ωY) (tensorRight LY))
      ((derivedPullback f).op ⋙ relativeDual ωX') ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (relativeDual ωY).rightOp
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (derivedPullbackTwistOpIso f tw) (relativeDual ωX') ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (derivedPullback f).op
          (Functor.isoWhiskerLeft (tensorRight LX).op (relativeDualMapIso eX) ≪≫
            relativeDualTwistCancelIso ωX hX))

end TwistFunctor

/-! ### The twists coming from the base -/

section BaseTwist

variable {X Y S : Scheme.{u}}

/-- For a factorization `f ≫ b = a` of structure morphisms over the base, the comparison
`Lf^*(Lb^*ℒ) ≅ La^*ℒ`: the composition isomorphism
`Stacks.Duality.derivedPullbackCompIso` read along the factorization. -/
def basePullbackTwistIso (f : X ⟶ Y) (b : Y ⟶ S) (a : X ⟶ S) (hfb : f ≫ b = a)
    (L : DerivedCategory S.Modules) :
    (derivedPullback f).obj ((derivedPullback b).obj L) ≅ (derivedPullback a).obj L :=
  (derivedPullbackCompIso f b).app L ≪≫ eqToIso (by rw [hfb])

variable
  [MonoidalCategory (DerivedCategory X.Modules)] [BraidedCategory (DerivedCategory X.Modules)]
  [MonoidalClosed (DerivedCategory X.Modules)]
  [MonoidalCategory (DerivedCategory Y.Modules)] [MonoidalClosed (DerivedCategory Y.Modules)]
  [MonoidalCategory (DerivedCategory S.Modules)]

/-- **[Stacks, Tag 0BV3] in the shape the source states it**, with both twists pulled back from
the base.

Let `a : X ⟶ S` and `b : Y ⟶ S` be the structure morphisms of two schemes of finite type over
the base and let `f : X ⟶ Y` satisfy `f ≫ b = a`. For an invertible `ℒ` in `D(𝒪_S)` and
complexes `ω_X'`, `ω_Y'` identified with the twists `ω_X^• ⊗ La^*ℒ` and `ω_Y^• ⊗ Lb^*ℒ`, the
two `f_new^!` are isomorphic as functors.

The tensor comparisons `ta`, `tb` and the unit comparisons `ea`, `eb` are what make `La^*ℒ` and
`Lb^*ℒ` invertible; `tf` is the monoidality of `Lf^*` in the twist variable, and
`Stacks.Duality.basePullbackTwistIso` turns `Lf^*Lb^*ℒ` into `La^*ℒ`.

No `@[stacks 0BV3]` attribute is repeated here: the tag sits on
`Stacks.Duality.fNewShriekTwistIso`, of which this is the specialization. -/
def fNewShriekBaseTwistIso (f : X ⟶ Y) (b : Y ⟶ S) (a : X ⟶ S) (hfb : f ≫ b = a)
    {ωX ωX' : DerivedCategory X.Modules} {ωY ωY' : DerivedCategory Y.Modules}
    {L : DerivedCategory S.Modules} (hL : HasInverse L)
    (ta : ∀ A B : DerivedCategory S.Modules, (derivedPullback a).obj (A ⊗ B) ≅
      (derivedPullback a).obj A ⊗ (derivedPullback a).obj B)
    (ea : (derivedPullback a).obj (𝟙_ (DerivedCategory S.Modules)) ≅
      𝟙_ (DerivedCategory X.Modules))
    (tb : ∀ A B : DerivedCategory S.Modules, (derivedPullback b).obj (A ⊗ B) ≅
      (derivedPullback b).obj A ⊗ (derivedPullback b).obj B)
    (eb : (derivedPullback b).obj (𝟙_ (DerivedCategory S.Modules)) ≅
      𝟙_ (DerivedCategory Y.Modules))
    (eX : ωX' ≅ ωX ⊗ (derivedPullback a).obj L)
    (eY : ωY' ≅ ωY ⊗ (derivedPullback b).obj L)
    (tf : tensorRight ((derivedPullback b).obj L) ⋙ derivedPullback f ≅
      derivedPullback f ⋙ tensorRight ((derivedPullback f).obj ((derivedPullback b).obj L))) :
    fNewShriek f ωX' ωY' ≅ fNewShriek f ωX ωY :=
  fNewShriekTwistIso f
    (hasInverseObjOfTensorIso (derivedPullback a) ta ea hL)
    (hasInverseObjOfTensorIso (derivedPullback b) tb eb hL)
    eX eY
    (tf ≪≫ Functor.isoWhiskerLeft (derivedPullback f)
      ((tensoringRight (DerivedCategory X.Modules)).mapIso (basePullbackTwistIso f b a hfb L)))

end BaseTwist

/-! ### The dualizing complex upstairs is the twisted inverse image -/

section Proper

variable {𝒟 : Scheme.{u} → Type v} [∀ X : Scheme.{u}, Category.{v'} (𝒟 X)]

/-- **Stacks Project, Tag 0AUD.** Let `f : X ⟶ Y` be a morphism of schemes of finite type over
the base of [Stacks, Tag 0AU4], with structure morphisms `q : Y ⟶ S` and `p : X ⟶ S` and
`f ≫ q = p`. Let `a` be the right adjoint of `Rf_*` of [Stacks, Tag 0A9E]. If `ω_X^•` and
`ω_Y^•` are normalized relative to `ω_S^•`, there is a canonical isomorphism
`a(ω_Y^•) ≅ ω_X^•`.

This is the argument of the source in the case where the schemes are separated over `S`: there
`ω_X^• = p^!ω_S^•` and `ω_Y^• = q^!ω_S^•`, the properness of `f` enters only through the
identification of `f^!` with `a`, and the composition comparison `f^! ∘ q^! ≅ p^!` — the
`factorIso` field of `Stacks.Duality.UpperShriek` — finishes it. -/
@[stacks 0AUD "RESTRICTED: the upper shriek formalism is a parameter, normalization is taken in
the separated form omega_X = p^! omega_S, and the identification of f^! with the right adjoint,
which is the only place properness is used, is a hypothesis"]
def dualizingIsoRightAdjointObj (A : UpperShriek 𝒟) {X Y S : Scheme.{u}}
    {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S} (hfq : f ≫ q = p)
    (hf : IsShriekable f) (hq : IsShriekable q) (hp : IsShriekable p)
    {a : 𝒟 Y ⥤ 𝒟 X} (hfa : A.shriek f hf ≅ a)
    (ωS : 𝒟 S) {ωX : 𝒟 X} {ωY : 𝒟 Y}
    (nX : ωX ≅ (A.shriek p hp).obj ωS) (nY : ωY ≅ (A.shriek q hq).obj ωS) :
    a.obj ωY ≅ ωX :=
  hfa.symm.app ωY ≪≫ (A.shriek f hf).mapIso nY ≪≫
    ((A.factorIso hfq hf hq hp).app ωS).symm ≪≫ nX.symm

end Proper

end Stacks.Duality

end
