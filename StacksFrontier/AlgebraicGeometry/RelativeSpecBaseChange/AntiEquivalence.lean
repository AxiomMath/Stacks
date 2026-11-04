module

public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.Reduction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The base-change-compatible anti-equivalence, reduced to one statement

Let `S` be a scheme.  The anti-equivalence between the schemes affine over `S` and the
quasi-coherent sheaves of commutative `𝒪_S`-algebras is
`Stacks.AffineAlgebraEquivalence.affineQuasicoherentEquivalence`, and the identification of its
functor with `X ↦ f_* 𝒪_X` is `pushforwardIsoOfEquivalence`.  What the full statement of Stacks
Tag 01SA adds is compatibility with arbitrary base change, which
`StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.Quasicoherent` reduces to a single
assertion: that the base change `g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` of a quasi-coherent algebra is
quasi-coherent.

That assertion is `Stacks.AffineAlgebraEquivalence.IsQuasicoherentAlgebraPullback`, stated in
`StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.Reduction`; this file derives from it the
whole of `AffineAlgebraAntiEquivalence`, so that Tag 01SA stands on exactly one unproved statement
and on nothing else.  It also records the two consequences of the anti-equivalence that
consumers of an affine morphism actually want: an affine morphism `f : X ⟶ S` exhibits `X` as
the relative spectrum of `f_* 𝒪_X`, and being affine is equivalent to being a relative
spectrum.

## Main definitions

* `qcohAlgebraPullbackFunctor` is the base-change functor on quasi-coherent algebras that the
  residual assertion makes available, and `baseChangeQuasicoherentNatIso` is the natural
  isomorphism expressing its compatibility with base change of affine schemes.
* `antiEquivalenceOfQuasicoherentAlgebraPullback` assembles `AffineAlgebraAntiEquivalence` from
  the residual assertion.
* `affineOverRelativeSpecIso` and `overRelativeSpecIso` are the isomorphism
  `X ≅ \underline{Spec}_S(f_* 𝒪_X)`, in the category of schemes affine over `S` and in the
  category of schemes over `S`.

## Main results

* `isQuasicoherent_algebraPullback_of_affine` and `baseChangeAlgebraIso`: the residual
  assertion makes `baseChangeAlgebraHom` an isomorphism at every scheme affine over `S`.
* `isAffineHom_iff_exists_quasicoherentAlgebra`: a morphism of schemes is affine if and only if
  it is the structure morphism of a relative spectrum, up to isomorphism over the base.

## Implementation notes

The residual assertion is stated for an object of `QuasicoherentAlgebra S` rather than for an
algebra sheaf together with an instance argument, so that it is a closed `Prop` that can be
passed around as a hypothesis; `isQuasicoherent_algebraPullback_of_affine` is the instance-form
specialization at `f_* 𝒪_X` that `isIso_baseChangeAlgebraHom_of_isQuasicoherent` consumes.

Naturality of `baseChangeQuasicoherentNatIso` is `baseChangeAlgebraHom_naturality`, but it
cannot be handed to `CategoryTheory.NatIso.ofComponents` directly: the two functors whose
naturality square is at issue are built by `CategoryTheory.ObjectProperty.lift`, and asking the
elaborator to identify their action on a morphism with the composite it unfolds to exhausts the
heartbeat budget in `whnf`.  The four `rfl` lemmas
`comp_qcohAlgebraPullbackFunctor_obj_obj`, `affineBaseChange_comp_obj_obj`,
`comp_qcohAlgebraPullbackFunctor_map_hom` and `affineBaseChange_comp_map_hom` do that
identification one step at a time, each cheap on its own, after which the naturality proof is a
`congrArg` chain checked at default transparency.

`affineOverRelativeSpecIso` is `pushforwardAlgebraIso` transported through the fully faithful
functor `X ↦ f_* 𝒪_X` and then through `Opposite`: both `X` and the relative spectrum of
`f_* 𝒪_X` are carried to `f_* 𝒪_X`, the latter only up to the isomorphism of Tag 01LX part (3),
so full faithfulness produces an isomorphism between them.  The objects of the two functors
have to be supplied explicitly, since the full subcategory inclusion gives the elaborator no
way to invert `ObjectProperty.ι.obj` on the algebra `f_* 𝒪_X`.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.AffineAlgebraEquivalence

/-! ### The residual assertion of Stacks Tag 01SA -/

/-- Base change of quasi-coherent algebras along `g : T ⟶ S`, available once the residual
assertion of Stacks Tag 01SA is known: the restriction of `algebraPullback g` to the full
subcategories of quasi-coherent algebras. -/
public noncomputable def qcohAlgebraPullbackFunctor (h : IsQuasicoherentAlgebraPullback.{u})
    {T S : Scheme.{u}} (g : T ⟶ S) :
    QuasicoherentAlgebra S ⥤ QuasicoherentAlgebra T :=
  ObjectProperty.lift _ ((IsQuasicoherentAlgebra S).ι ⋙ algebraPullback g) (h g)

/-- The residual assertion, specialized to the pushed-forward structure sheaf of a scheme
affine over `S`: the base change of `f_* 𝒪_X` is quasi-coherent. -/
public theorem isQuasicoherent_algebraPullback_of_affine
    (h : IsQuasicoherentAlgebraPullback.{u}) {T S : Scheme.{u}} (g : T ⟶ S) (X : Over S)
    [IsAffineHom X.hom] :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent
      ((algebraPullback g).obj (pushforwardAlgebra X.hom)) :=
  h g ⟨pushforwardAlgebra X.hom, isQuasicoherent_pushforwardAlgebra X.hom⟩

/-- The base-change comparison of algebra sheaves at a scheme affine over `S`, promoted to an
isomorphism by the residual assertion of Stacks Tag 01SA. -/
public noncomputable def baseChangeAlgebraIso (h : IsQuasicoherentAlgebraPullback.{u})
    {T S : Scheme.{u}} (g : T ⟶ S) (X : Over S) [IsAffineHom X.hom] :
    (algebraPullback g).obj (pushforwardAlgebra X.hom) ≅
      pushforwardAlgebra ((Over.pullback g).obj X).hom :=
  letI : IsIso (baseChangeAlgebraHom g X) :=
    isIso_baseChangeAlgebraHom_of_isQuasicoherent g X
      (isQuasicoherent_algebraPullback_of_affine h g X)
  asIso (baseChangeAlgebraHom g X)

/-- The forward map of `baseChangeAlgebraIso` is the base-change comparison itself. -/
public theorem baseChangeAlgebraIso_hom (h : IsQuasicoherentAlgebraPullback.{u})
    {T S : Scheme.{u}} (g : T ⟶ S) (X : Over S) [IsAffineHom X.hom] :
    (baseChangeAlgebraIso h g X).hom = baseChangeAlgebraHom g X :=
  rfl

/-! ### The base-change natural isomorphism -/

section

variable (h : IsQuasicoherentAlgebraPullback.{u}) {T S : Scheme.{u}} (g : T ⟶ S)

/-- The value on an object of the composite of `X ↦ f_* 𝒪_X` with base change of
quasi-coherent algebras is the base change of the pushed-forward structure sheaf. -/
public theorem comp_qcohAlgebraPullbackFunctor_obj_obj (X : (AffineOver S)ᵒᵖ) :
    ((affineQuasicoherentPushforwardFunctor S ⋙ qcohAlgebraPullbackFunctor h g).obj X).obj =
      (algebraPullback g).obj (pushforwardAlgebra X.unop.obj.hom) :=
  rfl

/-- The value on an object of the composite of base change of affine schemes with
`X ↦ f_* 𝒪_X` is the pushed-forward structure sheaf of the base-changed scheme. -/
public theorem affineBaseChange_comp_obj_obj (X : (AffineOver S)ᵒᵖ) :
    (((affineBaseChange g).op ⋙ affineQuasicoherentPushforwardFunctor T).obj X).obj =
      pushforwardAlgebra ((Over.pullback g).obj X.unop.obj).hom :=
  rfl

/-- The action on a morphism of the composite of `X ↦ f_* 𝒪_X` with base change of
quasi-coherent algebras. -/
public theorem comp_qcohAlgebraPullbackFunctor_map_hom {X Y : (AffineOver S)ᵒᵖ} (f : X ⟶ Y) :
    ((affineQuasicoherentPushforwardFunctor S ⋙ qcohAlgebraPullbackFunctor h g).map f).hom =
      (algebraPullback g).map (pushforwardAlgebraMap f.unop.hom) :=
  rfl

/-- The action on a morphism of the composite of base change of affine schemes with
`X ↦ f_* 𝒪_X`. -/
public theorem affineBaseChange_comp_map_hom {X Y : (AffineOver S)ᵒᵖ} (f : X ⟶ Y) :
    (((affineBaseChange g).op ⋙ affineQuasicoherentPushforwardFunctor T).map f).hom =
      pushforwardAlgebraMap ((Over.pullback g).map f.unop.hom) :=
  rfl

/-- The component at a scheme affine over `S` of the base-change natural isomorphism, read in
the category of quasi-coherent `𝒪_T`-algebras. -/
public noncomputable def baseChangeQuasicoherentIso (X : (AffineOver S)ᵒᵖ) :
    (affineQuasicoherentPushforwardFunctor S ⋙ qcohAlgebraPullbackFunctor h g).obj X ≅
      ((affineBaseChange g).op ⋙ affineQuasicoherentPushforwardFunctor T).obj X :=
  letI := X.unop.property
  ObjectProperty.isoMk _ (baseChangeAlgebraIso h g X.unop.obj)

/-- The forward map of `baseChangeQuasicoherentIso`, read in the ambient category of algebra
sheaves, is the base-change comparison. -/
public theorem baseChangeQuasicoherentIso_hom_hom (X : (AffineOver S)ᵒᵖ) :
    (baseChangeQuasicoherentIso h g X).hom.hom =
      letI := X.unop.property
      baseChangeAlgebraHom g X.unop.obj :=
  rfl

/-- **The anti-equivalence of Stacks Tag 01SA commutes with base change**, granted the residual
assertion `IsQuasicoherentAlgebraPullback`: base change of quasi-coherent algebras along
`g : T ⟶ S` corresponds, under `X ↦ f_* 𝒪_X`, to base change of schemes affine over `S`. -/
public noncomputable def baseChangeQuasicoherentNatIso :
    affineQuasicoherentPushforwardFunctor S ⋙ qcohAlgebraPullbackFunctor h g ≅
      (affineBaseChange g).op ⋙ affineQuasicoherentPushforwardFunctor T :=
  NatIso.ofComponents (baseChangeQuasicoherentIso h g) fun {X Y} f ↦
    letI := X.unop.property
    letI := Y.unop.property
    ObjectProperty.hom_ext _ (Eq.trans (Eq.trans
      (congrArg (fun k ↦ k ≫ (baseChangeQuasicoherentIso h g Y).hom.hom)
        (comp_qcohAlgebraPullbackFunctor_map_hom h g f))
      (Eq.trans (congrArg (fun k ↦ (algebraPullback g).map
          (pushforwardAlgebraMap f.unop.hom) ≫ k)
        (baseChangeQuasicoherentIso_hom_hom h g Y))
        (Eq.trans (baseChangeAlgebraHom_naturality g f.unop.hom)
          (congrArg (fun k ↦ baseChangeAlgebraHom g X.unop.obj ≫ k)
            (affineBaseChange_comp_map_hom g f).symm))))
      (congrArg (fun k ↦ k ≫ (((affineBaseChange g).op ⋙
          affineQuasicoherentPushforwardFunctor T).map f).hom)
        (baseChangeQuasicoherentIso_hom_hom h g X).symm))

end

/-! ### The anti-equivalence, reduced to one statement -/

/-- **Stacks Tag 01SA, reduced to one statement.** Granted the residual assertion
`IsQuasicoherentAlgebraPullback`, the schemes affine over a base `S` are anti-equivalent to the
quasi-coherent sheaves of commutative `𝒪_S`-algebras by `X ↦ f_* 𝒪_X`, compatibly with
arbitrary base change.

Every field other than `algebraPullback_isQuasicoherent` is discharged here: the
anti-equivalence is `affineQuasicoherentEquivalence`, its identification with pushforward of
structure sheaves is `pushforwardIsoOfEquivalence`, the base-change isomorphism is
`baseChangeQuasicoherentNatIso` and its canonicity is
`algebraPullbackMap_comp_baseChangeAlgebraHom`. -/
public noncomputable def antiEquivalenceOfQuasicoherentAlgebraPullback
    (h : IsQuasicoherentAlgebraPullback.{u}) : AffineAlgebraAntiEquivalence.{u} where
  algebraPullback g := algebraPullback g
  algebraPullbackMap g := algebraPullbackMap g
  algebraPullback_isPushout g A := algebraPullback_isPushout g A
  algebraPullback_isQuasicoherent g A := h g A
  equivalence S := affineQuasicoherentEquivalence S
  pushforwardIso S X := pushforwardIsoOfEquivalence S X
  pushforwardIso_naturality := fun S {_ _} f ↦ pushforwardIsoOfEquivalence_naturality S f
  baseChangeIso g := baseChangeQuasicoherentNatIso h g
  baseChangeIso_canonical := fun g X ↦
    Eq.trans
      (congrArg (fun k ↦ (algebraPullbackMap g).app (pushforwardAlgebra X.obj.hom) ≫
          Under.Hom.right k)
        (Category.comp_id ((IsQuasicoherentAlgebra _).ι.map
          ((baseChangeQuasicoherentNatIso h g).hom.app (op X)))))
      (Eq.trans (algebraPullbackMap_comp_baseChangeAlgebraHom g X.obj)
        (Eq.trans (Category.id_comp (pushforwardBaseChangeMap g X.obj)).symm
          (congrArg (fun k ↦ k ≫ pushforwardBaseChangeMap g X.obj)
            ((TopCat.Sheaf.pullback CommRingCat g.base).map_id
              (pushforwardAlgebra X.obj.hom).right).symm)))

/-! ### Affine morphisms are relative spectra -/

/-- **Stacks Project, Tag 01S8, the final statement.** An affine morphism `f : X ⟶ S` exhibits
`X` as the relative spectrum of `f_* 𝒪_X`: the isomorphism in the category of schemes affine
over `S`.

Both objects are carried to `f_* 𝒪_X` by the fully faithful functor `X ↦ f_* 𝒪_X`, the relative
spectrum only up to the isomorphism `pushforwardAlgebraIso` of Tag 01LX part (3). -/
@[ega "IV 21.12.1" "Sufficiency"]
public noncomputable def affineOverRelativeSpecIso {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffineHom f] :
    letI := isQuasicoherent_pushforwardAlgebra f
    (⟨Over.mk f, ‹IsAffineHom f›⟩ : AffineOver S) ≅
      relativeSpecAffineOver (pushforwardAlgebra f) :=
  letI := isQuasicoherent_pushforwardAlgebra f
  ((fullyFaithfulAffineQuasicoherentPushforwardFunctor S).preimageIso
    (X := op (relativeSpecAffineOver (pushforwardAlgebra f)))
    (Y := op (⟨Over.mk f, ‹IsAffineHom f›⟩ : AffineOver S))
    ((IsQuasicoherentAlgebra S).ι.preimageIso
      (X := (affineQuasicoherentPushforwardFunctor S).obj
        (op (relativeSpecAffineOver (pushforwardAlgebra f))))
      (Y := (affineQuasicoherentPushforwardFunctor S).obj
        (op (⟨Over.mk f, ‹IsAffineHom f›⟩ : AffineOver S)))
      (pushforwardAlgebraIso (pushforwardAlgebra f)))).unop

/-- **Stacks Project, Tag 01S8, the final statement.** For an affine morphism `f : X ⟶ S` there
is an isomorphism `X ≅ \underline{Spec}_S(f_* 𝒪_X)` of schemes over `S`. -/
@[stacks 01S8 "the final statement: X = Spec_S(f_* O_X) for an affine morphism f : X → S"]
public noncomputable def overRelativeSpecIso {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] :
    letI := isQuasicoherent_pushforwardAlgebra f
    (Over.mk f : Over S) ≅ Over.mk (relativeSpecToBase (pushforwardAlgebra f)) :=
  letI := isQuasicoherent_pushforwardAlgebra f
  (IsAffineHomOver S).ι.mapIso (affineOverRelativeSpecIso f)

/-- A morphism of schemes isomorphic over the base to an affine morphism is affine. -/
public theorem isAffineHom_of_overIso {X Y S : Scheme.{u}} (f : X ⟶ S) (q : Y ⟶ S)
    [IsAffineHom q] (e : (Over.mk f : Over S) ≅ Over.mk q) : IsAffineHom f := by
  have hw : e.hom.left ≫ q = f := Over.w e.hom
  have : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
  rw [← hw]
  infer_instance

/-- **Stacks Project, Tag 01S8, part (3).** A morphism of schemes `f : X ⟶ S` is affine if and
only if there is a quasi-coherent sheaf of `𝒪_S`-algebras `A` and an isomorphism
`X ≅ \underline{Spec}_S(A)` of schemes over `S`.

The forward direction takes `A = f_* 𝒪_X` and is `overRelativeSpecIso`; the converse is
`isAffineHom_relativeSpecToBase` together with `isAffineHom_of_overIso`. -/
@[stacks 01S8 "part (3): f is affine iff X is a relative spectrum over S",
  sga "3 I 4.2" "partial",
  sga "3 III 0.1.7" "0.1.7(a)"]
public theorem isAffineHom_iff_exists_quasicoherentAlgebra {X S : Scheme.{u}} (f : X ⟶ S) :
    IsAffineHom f ↔ ∃ A : QuasicoherentAlgebra S,
      letI := A.property
      Nonempty ((Over.mk f : Over S) ≅ Over.mk (relativeSpecToBase A.obj)) := by
  refine ⟨fun _ ↦ ⟨⟨pushforwardAlgebra f, isQuasicoherent_pushforwardAlgebra f⟩,
    ⟨overRelativeSpecIso f⟩⟩, ?_⟩
  rintro ⟨A, ⟨e⟩⟩
  have := A.property
  have := isAffineHom_relativeSpecToBase A.obj
  exact isAffineHom_of_overIso f (relativeSpecToBase A.obj) e

end Stacks.AffineAlgebraEquivalence

end
