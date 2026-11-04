module

public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.DerivedPushforwardOverPushforwardRing
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ConstructedDerivedAdjunction

/-!
# The trace of the right adjoint of pushforward is evaluation at one

Let `f : Y ⟶ X` be an affine morphism of schemes — a finite morphism is one — and let `a` be a
right adjoint of `Rf_* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`.  The trace map `Tr_{f, K} : Rf_* a(K) ⟶ K`,
that is the counit of `Rf_* ⊣ a`, agrees with the composite

`Rf_* a(K) = R ℰom_{𝒪_X}(f₊ 𝒪_Y, K) ⟶ K`

whose identification is the comparison map of [Stacks, Tag 0AX2] and whose arrow is induced by
the map `𝒪_X ⟶ f₊ 𝒪_Y`.  This is the square of [Stacks, Tag 0AX3].

## The square, and which of its edges are built here

The source draws

```
Rf_* a(K)                     --Tr_{f, K}-->   K
    ‖                                          ‖
R ℰom_{𝒪_X}(f₊ 𝒪_Y, K)            -->          K
```

with both vertical edges equalities.  The right edge is an identity.  The left edge is the
identification of [Stacks, Tag 0AX2]: here it is the canonical comparison map
`AlgebraicGeometry.pushforwardRightAdjointToDerivedInternalHom`,
`Rf_* a(K) ⟶ R ℰom_{𝒪_X}(f₊ 𝒪_Y, K)`, the transpose of the trace along the adjunction of
[Stacks, Tag 0BV0] read through the factorisation of `Rf_*` of [Stacks, Tag 0AVW].  The lower
horizontal edge is the counit of [Stacks, Tag 0BV0], which is the map induced by
`𝒪_X ⟶ f₊ 𝒪_Y`: the adjunction of [Stacks, Tag 0BV0] is the derived form of the adjunction
`restriction of scalars ⊣ ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` of [Stacks, Tag 0BUZ], whose counit sends a
local homomorphism out of `f₊ 𝒪_Y` to its value at the section `1`.

This file builds the edges and proves that the square commutes, which holds for every affine
morphism and every `K` in `D_QCoh(𝒪_X)`.  That the left edge is an *isomorphism* when `f` is
finite, `X` is locally Noetherian and `K` lies in `D_QCoh^+(𝒪_X)` — so that it may be drawn as
an equality — is proved in
`StacksFrontier/AlgebraicGeometry/Duality/FiniteTraceDerivedInternalHomIso.lean`, where
[Stacks, Tag 0AX3] is registered on the two assertions together.

## Main definitions

* `AlgebraicGeometry.derivedRestrictionHomSheafAdjunction` and
  `AlgebraicGeometry.derivedHomSheafRestrictionIso` — the adjunction of [Stacks, Tag 0BV0] and
  the isomorphism of [Stacks, Tag 0BV1], taken from those two theorems.
* `AlgebraicGeometry.derivedInternalHomPushforwardEvaluation` — the lower horizontal arrow
  `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -) ⟶ 𝟭`, for every morphism of schemes.
* `AlgebraicGeometry.pushforwardTraceTranspose` — the adjunct of the trace.
* `AlgebraicGeometry.pushforwardRightAdjointToDerivedInternalHom` — the left vertical edge, the
  comparison map `Rf_* a(K) ⟶ R ℰom_{𝒪_X}(f₊ 𝒪_Y, K)` of [Stacks, Tag 0AX2]; it is an
  isomorphism by `AlgebraicGeometry.isIso_pushforwardRightAdjointToDerivedInternalHom`.

## Main results

* `AlgebraicGeometry.pushforwardRightAdjointToDerivedInternalHom_comp_evaluation` — the square
  of [Stacks, Tag 0AX3] commutes: the comparison map of [Stacks, Tag 0AX2] followed by the map
  induced by `𝒪_X ⟶ f₊ 𝒪_Y` is the trace map.

## Implementation notes

*What the content of the square is.*  The comparison map of [Stacks, Tag 0AX2] is, here as in
the source, the transpose of the trace: the source proves that tag by uniqueness of adjoints,
and the isomorphism uniqueness of adjoints produces between two right adjoints of one functor is
by construction built from the counits.  So the square is the mate identity — the triangle
`L(adjunct of u) ≫ ε = u` of the adjunction of [Stacks, Tag 0BV0] — and the two geometric
inputs that make it a statement about the source's square are that the lower arrow is the counit
of that adjunction, hence the map induced by `𝒪_X ⟶ f₊ 𝒪_Y` ([Stacks, Tag 0BUZ]), and that
`Rf_*` is `Φ` followed by restriction of scalars along `𝒪_X ⟶ f₊ 𝒪_Y` ([Stacks, Tag 0AVW]).

*Why affineness suffices for the square.*  What the commutativity needs of `f` is only that
`Rf_*` carry `D_QCoh` into `D_QCoh`, so that there is a functor for `a` to be adjoint to at all;
that is part (1) of [Stacks, Tag 08D5], available here for an *affine* morphism as
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_isAffineHom`, and the restricted
functor it produces is the canonical `Stacks.Duality.affineHomQuasiCoherentDerivedPushforward`.

*The adjunctions of [Stacks, Tag 0BV0] and [Stacks, Tag 0BV1]* are taken from
`AlgebraicGeometry.derivedRestriction_adj_derivedHomSheaf` and
`AlgebraicGeometry.derivedHomSheaf_comp_derivedRestriction_iso`, which hold for every morphism
of schemes.  The isomorphism of [Stacks, Tag 0BV1] is unique, so nothing is chosen there beyond
reading off the witness of its `∃!`; a right adjoint is unique up to canonical isomorphism, and
which one `AlgebraicGeometry.derivedRestrictionHomSheafAdjunction` names does not matter to the
statement, since the lower arrow is defined from it.

*The right adjoint `a`.*  The square is drawn with `Rf_* a(K)` in it and `Tr_{f, K}` the counit
of `Rf_* ⊣ a`, so every statement below is quantified over a right adjoint `a` of `Rf_*` and an
adjunction exhibiting it.  The model of the derived categories is
`CategoryTheory.HasDerivedCategory.standard`: the lower arrow is built from
`AlgebraicGeometry.derivedRestrictionOfScalars` and `AlgebraicGeometry.derivedHomSheaf`, which
pin that model in their own definitions.

## References

* [Stacks Project, Tag 0AX3](https://stacks.math.columbia.edu/tag/0AX3)
* [Stacks Project, Tag 0AX2](https://stacks.math.columbia.edu/tag/0AX2)
* [Stacks Project, Tag 0AVW](https://stacks.math.columbia.edu/tag/0AVW)
* [Stacks Project, Tag 0BV0](https://stacks.math.columbia.edu/tag/0BV0)
* [Stacks Project, Tag 0BV1](https://stacks.math.columbia.edu/tag/0BV1)
* [Stacks Project, Tag 0BUZ](https://stacks.math.columbia.edu/tag/0BUZ)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0B6M](https://stacks.math.columbia.edu/tag/0B6M)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.AlgebraicGeometry.DerivedAffinePushforward (derivedPushforwardOverRing
  derivedPushforwardOverRingCompRestrictScalarsIso)
open Stacks.Duality (affineHomQuasiCoherentDerivedPushforward derivedPushforward
  quasiCoherentDerivedCategory)

-- Standard model only: `AlgebraicGeometry.derivedRestrictionOfScalars`,
--   `AlgebraicGeometry.derivedHomSheaf`, `AlgebraicGeometry.derivedInternalHomPushforward`.
attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- **The adjunction of [Stacks, Tag 0BV0]**: restriction of scalars along `𝒪_X ⟶ f₊ 𝒪_Y` is
left adjoint to `R ℰom(f₊ 𝒪_Y, -)`.  This reads off a witness of
`AlgebraicGeometry.derivedRestriction_adj_derivedHomSheaf`, which holds for every morphism of
schemes with nothing assumed; a right adjoint is unique up to canonical isomorphism, so which
witness this is does not matter to anything below. -/
def derivedRestrictionHomSheafAdjunction :
    derivedRestrictionOfScalars f ⊣ derivedHomSheaf f :=
  (derivedRestriction_adj_derivedHomSheaf f).some

/-- **The isomorphism of [Stacks, Tag 0BV1]**: following `R ℰom(f₊ 𝒪_Y, -)` by restriction of
scalars gives `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -)`.  This reads off the witness of the `∃!` of
`AlgebraicGeometry.derivedHomSheaf_comp_derivedRestriction_iso`, which holds for every morphism
of schemes with nothing assumed, and which pins the isomorphism uniquely. -/
def derivedHomSheafRestrictionIso :
    derivedHomSheaf f ⋙ derivedRestrictionOfScalars f ≅ derivedInternalHomPushforward f :=
  (derivedHomSheaf_comp_derivedRestriction_iso f).choose

/-- **The map `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -) ⟶ 𝟭` induced by `𝒪_X ⟶ f₊ 𝒪_Y`**, that is, evaluation of a
local homomorphism at the section `1`: the isomorphism of [Stacks, Tag 0BV1] followed by the
counit of the adjunction of [Stacks, Tag 0BV0], which is the derived form of the adjunction
`restriction of scalars ⊣ ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` of [Stacks, Tag 0BUZ].

This is the lower horizontal arrow of the square of [Stacks, Tag 0AX3].  It is built for every
morphism of schemes. -/
def derivedInternalHomPushforwardEvaluation :
    derivedInternalHomPushforward f ⟶ 𝟭 (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) :=
  (derivedHomSheafRestrictionIso f).inv ≫ (derivedRestrictionHomSheafAdjunction f).counit

/-- Evaluation at one, precomposed with the identification of [Stacks, Tag 0BV1], is the counit
of the adjunction of [Stacks, Tag 0BV0]. -/
@[reassoc]
theorem derivedInternalHomPushforwardEvaluation_app (K : DerivedCategory
    (SheafOfModules.{u} X.ringCatSheaf)) :
    (derivedHomSheafRestrictionIso f).hom.app K ≫
        (derivedInternalHomPushforwardEvaluation f).app K =
      (derivedRestrictionHomSheafAdjunction f).counit.app K := by
  rw [derivedInternalHomPushforwardEvaluation, NatTrans.comp_app, Iso.hom_inv_id_app_assoc]

section

variable [IsAffineHom f]
  {a : quasiCoherentDerivedCategory X ⥤ quasiCoherentDerivedCategory Y}
  (adj : affineHomQuasiCoherentDerivedPushforward f ⊣ a)

/-- **The adjunct of the trace map**: the transpose of

`Rf_* a(K) ⟶ K`,

read through the factorisation of `Rf_*` of [Stacks, Tag 0AVW], along the adjunction of
[Stacks, Tag 0BV0].  This is the map `Φ(a(K)) ⟶ R ℰom(f₊ 𝒪_Y, K)` of `f₊ 𝒪_Y`-modules out of
which the comparison map of [Stacks, Tag 0AX2] is built. -/
def pushforwardTraceTranspose (K : quasiCoherentDerivedCategory X) :
    (derivedPushforwardOverRing f).obj (a.obj K).obj ⟶ (derivedHomSheaf f).obj K.obj :=
  (derivedRestrictionHomSheafAdjunction f).homEquiv
    ((derivedPushforwardOverRing f).obj (a.obj K).obj) K.obj
    ((derivedPushforwardOverRingCompRestrictScalarsIso f).inv.app ((a.obj K).obj) ≫
      (adj.counit.app K).hom)

/-- **The comparison map of [Stacks, Tag 0AX2]**, the left vertical edge of the square of
[Stacks, Tag 0AX3]: the canonical map `Rf_* a(K) ⟶ R ℰom_{𝒪_X}(f₊ 𝒪_Y, K)`.

It is the transpose of the trace `Rf_* a(K) ⟶ K` along the adjunction of [Stacks, Tag 0BV0],
taken through the factorisation `Rf_* = Φ` followed by restriction of scalars of
[Stacks, Tag 0AVW] and read into `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` by [Stacks, Tag 0BV1].

[Stacks, Tag 0AX2] is the assertion that this map is invertible when `f` is a finite morphism of
Noetherian schemes and `K` lies in `D_QCoh^+(𝒪_X)`; that is
`AlgebraicGeometry.isIso_pushforwardRightAdjointToDerivedInternalHom`. -/
def pushforwardRightAdjointToDerivedInternalHom (K : quasiCoherentDerivedCategory X) :
    (derivedPushforward f).obj (a.obj K).obj ⟶
      (derivedInternalHomPushforward f).obj K.obj :=
  (derivedPushforwardOverRingCompRestrictScalarsIso f).hom.app ((a.obj K).obj) ≫
    (derivedRestrictionOfScalars f).map (pushforwardTraceTranspose f adj K) ≫
      (derivedHomSheafRestrictionIso f).hom.app K.obj

/-- **The square of [Stacks, Tag 0AX3] commutes.** Let `f : Y ⟶ X` be an affine morphism of
schemes and let `a` be a right adjoint of `Rf_* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`.  Then the
comparison map of [Stacks, Tag 0AX2] followed by the map `R ℰom_{𝒪_X}(f₊ 𝒪_Y, K) ⟶ K` induced
by `𝒪_X ⟶ f₊ 𝒪_Y` is the trace map `Tr_{f, K}`, that is the counit of `Rf_* ⊣ a`.

The whole remark — this together with the invertibility of the comparison map, for `f` finite
and `K` in `D_QCoh^+(𝒪_X)` — is
`AlgebraicGeometry.isIso_pushforwardRightAdjointToDerivedInternalHom_and_comp_evaluation`. -/
theorem pushforwardRightAdjointToDerivedInternalHom_comp_evaluation
    (K : quasiCoherentDerivedCategory X) :
    pushforwardRightAdjointToDerivedInternalHom f adj K ≫
        (derivedInternalHomPushforwardEvaluation f).app K.obj =
      (adj.counit.app K).hom := by
  have hmid : ((derivedRestrictionOfScalars f).map (pushforwardTraceTranspose f adj K) ≫
          (derivedHomSheafRestrictionIso f).hom.app K.obj) ≫
        (derivedInternalHomPushforwardEvaluation f).app K.obj =
      (derivedPushforwardOverRingCompRestrictScalarsIso f).inv.app ((a.obj K).obj) ≫
        (adj.counit.app K).hom :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun t => (derivedRestrictionOfScalars f).map
            (pushforwardTraceTranspose f adj K) ≫ t)
          (derivedInternalHomPushforwardEvaluation_app f K.obj)).trans
        ((Adjunction.homEquiv_counit (derivedRestrictionHomSheafAdjunction f)
              ((derivedPushforwardOverRing f).obj (a.obj K).obj) K.obj
              (pushforwardTraceTranspose f adj K)).symm.trans
          (Equiv.symm_apply_apply _ _)))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t =>
          (derivedPushforwardOverRingCompRestrictScalarsIso f).hom.app ((a.obj K).obj) ≫ t)
        hmid).trans (Iso.hom_inv_id_app_assoc _ _ _))

end

end AlgebraicGeometry

end
