module

public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.AlgebraIso
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.Invertible
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.BaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of the anti-equivalence between affine schemes and quasi-coherent algebras

Let `g : T ⟶ S` be a morphism of schemes and let `X` be a scheme affine over `S`.  The canonical
morphism of `𝒪_T`-algebras
`g⁻¹(X_* 𝒪_X) ⊗_{g⁻¹𝒪_S} 𝒪_T ⟶ (X ×_S T)_* 𝒪_{X ×_S T}`
is an isomorphism, naturally in `X`; and under the identification of the anti-equivalence of
[Stacks, Tag 01SA] with pushforward of structure sheaves it is the canonical inverse-image
comparison `Stacks.AffineAlgebraEquivalence.pushforwardBaseChangeMap`.

These are the two remaining clauses of that tag, `baseChangeIso` and `baseChangeIso_canonical`,
and `affineEquivalenceAlgebras` assembles all nine clauses into the structure
`Stacks.AffineAlgebraEquivalence.AffineAlgebraAntiEquivalence`.

## Main definitions

* `Stacks.AlgebraPullbackQcoh.overHomEquiv`: for `Y` affine over `S` and `X` **arbitrary** over
  `S`, the bijection between morphisms `X ⟶ Y` over `S` and morphisms
  `Y_* 𝒪 ⟶ X_* 𝒪` of `𝒪_S`-algebras.
* `Stacks.AlgebraPullbackQcoh.qcohAlgebraPullback`: algebra pullback restricted to the
  quasi-coherent algebras; this is the functor the `baseChangeIso` clause of Tag 01SA binds
  by a `let`, and `qcohAlgebraPullback_eq` says so on the nose.
* `Stacks.AlgebraPullbackQcoh.baseChangeIso`: **the `baseChangeIso` clause of Tag 01SA.**
* `Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras`: **all nine clauses.**

## Main results

* `Stacks.AlgebraPullbackQcoh.isIso_baseChangeAlgebraHom`: **the base-change morphism is
  invertible** for `X` affine over `S`, over an arbitrary `g`.
* `Stacks.AlgebraPullbackQcoh.baseChangeAlgebraHom_naturality`: it is natural in the scheme over
  `S`, for an arbitrary morphism of `Over S` (no affineness).
* `Stacks.AlgebraPullbackQcoh.baseChangeIso_canonical`: **the `baseChangeIso_canonical`
  clause of Tag 01SA.**
* `Stacks.AlgebraPullbackQcoh.isIso_of_bijective_precomp`: a morphism of quasi-coherent algebra
  sheaves is invertible once precomposition with it is bijective on morphisms into the
  pushed-forward structure sheaves of affine morphisms to the base.

## Route

The morphism to be inverted is
`Stacks.AffineAlgebraEquivalence.baseChangeAlgebraHom`, the transpose, under
`algebraPullbackPushforwardAdjunction`, of the contravariant map on pushed-forward structure
sheaves induced by the fibre-product projection.

It is inverted by a co-Yoneda argument on the representability statement, **not** by a local
computation of sections over affine opens: no tensor product of rings is formed below, and
neither `Stacks.AlgebraicGeometry.SectionsColimit.sectionsPullbackIso` nor
`AlgebraicGeometry.pullbackSpecIso` is used.  For an arbitrary `Z` over `T`, precomposition
with the morphism is the composite of three bijections:

* `algebraPullbackPushforwardAdjunction`, which turns a morphism out of
  `g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` into a morphism `A ⟶ g_*(-)` of `𝒪_S`-algebras;
* `overHomEquiv` over `S`, applied with the source `Z ⟶ T ⟶ S`, which is *not* affine over `S`.
  This is the point at which the fullness and faithfulness results are used in their general
  form: `overHomOfAlgebraHom` and `eq_of_pushforwardAlgebraMap_eq` assume only that the
  *target* is affine over the base;
* `CategoryTheory.Over.mapPullbackAdj`, the universal property of the fibre product.

That the composite is the pullback bijection is
`algebraEquiv_baseChangeAlgebraHom_comp`, proved from `Adjunction.homEquiv_naturality_right`,
the contravariant functoriality of `pushforwardAlgebraMap`, and
`algebraPushforward_map_pushforwardAlgebraMap`.  Bijectivity of precomposition is then
transferred to invertibility by `isIso_of_bijective_precomp`, whose two representing objects
are the relative spectra of the source and the target: the source is quasi-coherent by
`algebraPullback_isQuasicoherent` and the target because the fibre product is affine over
`T`, so `isQuasicoherent_pushforwardAlgebra` applies.

Naturality is the same transposition argument run on a square, and reduces to the naturality of
the fibre-product projections, which is the naturality of the counit of
`CategoryTheory.Over.mapPullbackAdj`.  Assembly into an isomorphism of functors uses that
`pushforwardIsoOfEquivalence` is `Iso.refl`, which is why `baseChangeIso_canonical` is
`algebraPullbackMap_comp_baseChangeAlgebraHom` after two identity cancellations, and in
particular needs no uniqueness argument from the pushout property.

## Registration and hypotheses

Tag 01SA is registered by a single unqualified attribute on the nine-field structure
`affineEquivalenceAlgebras`.

Nothing here assumes anything beyond the hypotheses of Tag 01SA.  `g` is an arbitrary morphism of
schemes throughout; the only affineness is that of `X` over `S`, which is the tag's own
hypothesis in both clauses, carried by the objects of `AffineOver S`.  There is no
Noetherian, finiteness, flatness, separatedness or quasi-compactness hypothesis anywhere, and
`algebraPushforward_map_pushforwardAlgebraMap`, `overHomEquiv`,
`baseChangeProjection_naturality` and `baseChangeAlgebraHom_naturality` assume no affineness at
all.

The two local instances, `isAffineHom_pullback_obj_hom` and `isIso_baseChangeNatTrans_app`, are
deliberately local: nothing outside this file needs them.

## Transparency gotchas

* `rw [← pushforwardAlgebraMap_comp]` and `rw [Category.comp_id]` both fail here, because
  `(algebraPushforward g).obj (pushforwardAlgebra q)` and `pushforwardAlgebra (q ≫ g)` are
  definitionally but not syntactically equal and the rewrite motive is then not type-correct at
  implicit transparency.  Each is replaced by a `have` at the spelling that appears together
  with `congrArg`/`Eq.trans`, which check at default transparency.
* `(relativeSpecAffineOver P).obj.hom` cannot be used in place of `relativeSpecToBase P` in the
  statement of `isIso_of_bijective_precomp`: `relativeSpecAffineOver` is a plain `def` into a
  full subcategory and the resulting morphism is not type-correct at implicit transparency.  The
  criterion is therefore quantified over a scheme and a morphism to `T` rather than over
  `AffineOver T`, and `Over.mk` is applied at the call site, where `exact` checks the two
  spellings at default transparency.
* `NatIso.ofComponents` does not give `(IsQuasicoherentAlgebra T).ι.map (_.hom.app _)` by `rfl`.
  The isomorphism is therefore built as `asIso` of an explicit natural transformation whose
  components are `ObjectProperty.homMk`, for which `ι_map_baseChangeIso_hom_app` is `rfl` — and
  that `rfl` is what `baseChangeIso_canonical` needs.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.AlgebraPullbackQcoh

open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

/-! ### A criterion for invertibility of a morphism of quasi-coherent algebras -/

/-- **A morphism `h : P ⟶ Q` is invertible as soon as precomposition with it is surjective on
morphisms into one object isomorphic to `P` and injective on morphisms into one object
isomorphic to `Q`.**  This is the co-Yoneda criterion in the form in which it can be used when
only *some* objects of the category are known to be representable. -/
theorem isIso_of_surjective_injective_precomp {C : Type*} [Category C] {P Q W₀ W₁ : C}
    (h : P ⟶ Q) (e₀ : W₀ ≅ P) (e₁ : W₁ ≅ Q)
    (H₀ : Function.Surjective fun u : Q ⟶ W₀ => h ≫ u)
    (H₁ : Function.Injective fun u : Q ⟶ W₁ => h ≫ u) : IsIso h := by
  obtain ⟨u, hu' : h ≫ u = e₀.inv⟩ := H₀ e₀.inv
  refine ⟨u ≫ e₀.hom, by rw [← Category.assoc, hu', Iso.inv_hom_id], ?_⟩
  refine (cancel_mono e₁.inv).mp (H₁ ?_)
  change h ≫ ((u ≫ e₀.hom) ≫ h) ≫ e₁.inv = h ≫ (𝟙 Q) ≫ e₁.inv
  simp only [Category.assoc, Category.id_comp]
  rw [← Category.assoc h, hu', Iso.inv_hom_id_assoc]

/-- **A morphism of quasi-coherent algebra sheaves is invertible as soon as it induces a
bijection on morphisms into the pushed-forward structure sheaf of every affine morphism to the
base.**  Only two such targets are used, the relative spectra of the source and of the target
of the morphism, which realise them by [Stacks, Tag 01LX]. -/
theorem isIso_of_bijective_precomp {T : Scheme.{u}} {P Q : AlgebraSheaf T} (h : P ⟶ Q)
    [AlgebraSheaf.IsQuasicoherent P] [AlgebraSheaf.IsQuasicoherent Q]
    (H : ∀ (Z : Scheme.{u}) (q : Z ⟶ T), IsAffineHom q →
      Function.Bijective fun u : Q ⟶ pushforwardAlgebra q => h ≫ u) :
    IsIso h :=
  isIso_of_surjective_injective_precomp h (pushforwardAlgebraIso P) (pushforwardAlgebraIso Q)
    (H (relativeSpec P) (relativeSpecToBase P) inferInstance).2
    (H (relativeSpec Q) (relativeSpecToBase Q) inferInstance).1

/-! ### The pushforward functor on algebra sheaves is a bijection on morphisms -/

/-- **For `Y` affine over `S` and `X` arbitrary over `S`, a morphism `X ⟶ Y` of schemes over
`S` is the same thing as a morphism `Y_* 𝒪 ⟶ X_* 𝒪` of `𝒪_S`-algebras.**  This is the full
faithfulness of the pushforward functor in the form in which the source is *not* assumed
affine over `S`, which is how the fullness and faithfulness results are stated. -/
def overHomEquiv {S : Scheme.{u}} (X Y : Over S) [IsAffineHom Y.hom] :
    (X ⟶ Y) ≃ (pushforwardAlgebra Y.hom ⟶ pushforwardAlgebra X.hom) where
  toFun u := pushforwardAlgebraMap u
  invFun ψ := overHomOfAlgebraHom ψ
  left_inv u := eq_of_pushforwardAlgebraMap_eq
    (pushforwardAlgebraMap_overHomOfAlgebraHom (pushforwardAlgebraMap u))
  right_inv ψ := pushforwardAlgebraMap_overHomOfAlgebraHom ψ

/-! ### Direct image of algebra sheaves on a pushforward map -/

/-- The direct image along `g : T ⟶ S` of the canonical map on pushed-forward structure sheaves
induced by a morphism over `T` is the canonical map induced by the same morphism, read over
`S`. -/
theorem algebraPushforward_map_pushforwardAlgebraMap {T S : Scheme.{u}} (g : T ⟶ S)
    {Z W : Over T} (v : Z ⟶ W) :
    (algebraPushforward g).map (pushforwardAlgebraMap v) =
      pushforwardAlgebraMap ((Over.map g).map v) := by
  ext1
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun V => ?_)
  obtain ⟨U⟩ := V
  have hL : ((algebraPushforward g).map (pushforwardAlgebraMap v)).right.hom.app (op U)
      = (pushforwardAlgebraMap v).right.hom.app (op (g ⁻¹ᵁ U)) := rfl
  rw [hL, pushforwardAlgebraMap_app v (g ⁻¹ᵁ U) (preimage_le_preimage_preimage v _),
    pushforwardAlgebraMap_app ((Over.map g).map v) U
      (preimage_le_preimage_preimage ((Over.map g).map v) U)]
  rfl

/-! ### Precomposition with the base-change morphism is bijective -/

section BaseChange

variable {T S : Scheme.{u}} (g : T ⟶ S) (X : Over S)

/-- The fibre product of a scheme affine over `S` with `T` is affine over `T`. -/
theorem isAffineHom_pullback_obj_hom [IsAffineHom X.hom] :
    IsAffineHom ((Over.pullback g).obj X).hom :=
  isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback X.hom g)
    inferInstance

attribute [local instance] isAffineHom_pullback_obj_hom

/-- The bijection of `CategoryTheory.Over.mapPullbackAdj`, in the direction used here: a
morphism `Z ⟶ X ×_S T` of schemes over `T` is the same thing as a morphism `Z ⟶ X` of schemes
over `S`. -/
abbrev overPullbackEquiv (Z : Over T) :
    (Z ⟶ (Over.pullback g).obj X) ≃ ((Over.map g).obj Z ⟶ X) :=
  ((Over.mapPullbackAdj g).homEquiv Z X).symm

/-- The pullback bijection is composition with the fibre-product projection. -/
theorem overPullbackEquiv_apply (Z : Over T) (v : Z ⟶ (Over.pullback g).obj X) :
    overPullbackEquiv g X Z v = (Over.map g).map v ≫ baseChangeProjection g X :=
  Over.OverMorphism.ext rfl

/-- The bijection between morphisms of `𝒪_T`-algebras out of `g⁻¹(X_* 𝒪) ⊗_{g⁻¹𝒪_S} 𝒪_T` and
morphisms of schemes over `S`, obtained by composing the adjunction for algebra pullback with
the full faithfulness of pushforward over `S`. -/
abbrev algebraEquiv [IsAffineHom X.hom] (Z : Over T) :
    ((algebraPullback g).obj (pushforwardAlgebra X.hom) ⟶ pushforwardAlgebra Z.hom) ≃
      ((Over.map g).obj Z ⟶ X) :=
  ((algebraPullbackPushforwardAdjunction g).homEquiv (pushforwardAlgebra X.hom)
    (pushforwardAlgebra Z.hom)).trans (overHomEquiv ((Over.map g).obj Z) X).symm

/-- The adjunct of `baseChangeAlgebraHom` is the map induced by the fibre-product projection. -/
private theorem homEquiv_baseChangeAlgebraHom :
    (algebraPullbackPushforwardAdjunction g).homEquiv (pushforwardAlgebra X.hom)
        (pushforwardAlgebra ((Over.pullback g).obj X).hom) (baseChangeAlgebraHom g X)
      = pushforwardAlgebraMap (baseChangeProjection g X) :=
  ((algebraPullbackPushforwardAdjunction g).homEquiv _ _).apply_symm_apply _

/-- **The base-change morphism, read through the canonical bijections, is the pullback
bijection.**  This is the heart of the base-change assertion: precomposition with
`baseChangeAlgebraHom` becomes the universal property of the fibre product. -/
theorem algebraEquiv_baseChangeAlgebraHom_comp [IsAffineHom X.hom] (Z : Over T)
    (v : Z ⟶ (Over.pullback g).obj X) :
    algebraEquiv g X Z (baseChangeAlgebraHom g X ≫ pushforwardAlgebraMap v) =
      overPullbackEquiv g X Z v := by
  rw [overPullbackEquiv_apply]
  change (overHomEquiv ((Over.map g).obj Z) X).symm
      ((algebraPullbackPushforwardAdjunction g).homEquiv (pushforwardAlgebra X.hom)
        (pushforwardAlgebra Z.hom)
        (baseChangeAlgebraHom g X ≫ pushforwardAlgebraMap v)) = _
  rw [Adjunction.homEquiv_naturality_right, homEquiv_baseChangeAlgebraHom,
    algebraPushforward_map_pushforwardAlgebraMap]
  have hcomp : pushforwardAlgebraMap (baseChangeProjection g X) ≫
        pushforwardAlgebraMap ((Over.map g).map v)
      = pushforwardAlgebraMap ((Over.map g).map v ≫ baseChangeProjection g X) :=
    (pushforwardAlgebraMap_comp ((Over.map g).map v) (baseChangeProjection g X)).symm
  exact Eq.trans (congrArg (overHomEquiv ((Over.map g).obj Z) X).symm hcomp)
    ((overHomEquiv ((Over.map g).obj Z) X).symm_apply_apply _)

/-- **Precomposition with the base-change morphism is bijective on morphisms into the
pushed-forward structure sheaf of an arbitrary scheme over `T`.**  Nothing is assumed of `Z`;
the affineness used is that of `X` over `S`, which makes the fibre product affine over `T` and
so makes both pushforward functors fully faithful at the objects involved. -/
theorem bijective_precomp_baseChangeAlgebraHom [IsAffineHom X.hom] (Z : Over T) :
    Function.Bijective fun u : pushforwardAlgebra ((Over.pullback g).obj X).hom ⟶
        pushforwardAlgebra Z.hom => baseChangeAlgebraHom g X ≫ u := by
  have hkey : ∀ v : Z ⟶ (Over.pullback g).obj X,
      algebraEquiv g X Z (baseChangeAlgebraHom g X ≫
          overHomEquiv Z ((Over.pullback g).obj X) v)
        = overPullbackEquiv g X Z v :=
    algebraEquiv_baseChangeAlgebraHom_comp g X Z
  constructor
  · intro u₁ u₂ h
    obtain ⟨v₁, rfl⟩ := (overHomEquiv Z ((Over.pullback g).obj X)).surjective u₁
    obtain ⟨v₂, rfl⟩ := (overHomEquiv Z ((Over.pullback g).obj X)).surjective u₂
    exact congrArg (overHomEquiv Z ((Over.pullback g).obj X)) ((overPullbackEquiv g X Z).injective
      ((hkey v₁).symm.trans ((congrArg (algebraEquiv g X Z) h).trans (hkey v₂))))
  · exact fun w => ⟨overHomEquiv Z ((Over.pullback g).obj X)
      ((overPullbackEquiv g X Z).symm (algebraEquiv g X Z w)), (algebraEquiv g X Z).injective
        ((hkey _).trans ((overPullbackEquiv g X Z).apply_symm_apply _))⟩

/-- **The canonical base-change morphism of `𝒪_T`-algebras
`g⁻¹(X_* 𝒪_X) ⊗_{g⁻¹𝒪_S} 𝒪_T ⟶ (X ×_S T)_* 𝒪_{X ×_S T}` is an isomorphism when `X` is affine
over `S`.**  This is the base-change assertion of [Stacks, Tag 01SA], objectwise. -/
theorem isIso_baseChangeAlgebraHom [IsAffineHom X.hom] :
    IsIso (baseChangeAlgebraHom g X) := by
  have : AlgebraSheaf.IsQuasicoherent ((algebraPullback g).obj (pushforwardAlgebra X.hom)) :=
    algebraPullback_isQuasicoherent g _ (isQuasicoherent_pushforwardAlgebra X.hom)
  have : AlgebraSheaf.IsQuasicoherent (pushforwardAlgebra ((Over.pullback g).obj X).hom) :=
    isQuasicoherent_pushforwardAlgebra ((Over.pullback g).obj X).hom
  exact isIso_of_bijective_precomp (baseChangeAlgebraHom g X)
    fun _ q _ => bijective_precomp_baseChangeAlgebraHom g X (Over.mk q)

end BaseChange

/-! ### Naturality of the base-change morphism -/

section Naturality

variable {T S : Scheme.{u}} (g : T ⟶ S)

/-- The fibre-product projections are natural in the scheme over `S`: this is the naturality of
the counit of `CategoryTheory.Over.mapPullbackAdj`. -/
theorem baseChangeProjection_naturality {X Y : Over S} (v : Y ⟶ X) :
    (Over.map g).map ((Over.pullback g).map v) ≫ baseChangeProjection g X
      = baseChangeProjection g Y ≫ v :=
  Over.OverMorphism.ext (by simp [baseChangeProjection])

/-- **The base-change morphism of algebra sheaves is natural in the scheme over `S`.** -/
theorem baseChangeAlgebraHom_naturality {X Y : Over S} (v : Y ⟶ X) :
    (algebraPullback g).map (pushforwardAlgebraMap v) ≫ baseChangeAlgebraHom g Y
      = baseChangeAlgebraHom g X ≫ pushforwardAlgebraMap ((Over.pullback g).map v) := by
  refine ((algebraPullbackPushforwardAdjunction g).homEquiv (pushforwardAlgebra X.hom)
    (pushforwardAlgebra ((Over.pullback g).obj Y).hom)).injective ?_
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_baseChangeAlgebraHom, homEquiv_baseChangeAlgebraHom,
    algebraPushforward_map_pushforwardAlgebraMap]
  have hl : pushforwardAlgebraMap v ≫ pushforwardAlgebraMap (baseChangeProjection g Y)
      = pushforwardAlgebraMap (baseChangeProjection g Y ≫ v) :=
    (pushforwardAlgebraMap_comp (baseChangeProjection g Y) v).symm
  have hr : pushforwardAlgebraMap (baseChangeProjection g X) ≫
        pushforwardAlgebraMap ((Over.map g).map ((Over.pullback g).map v))
      = pushforwardAlgebraMap ((Over.map g).map ((Over.pullback g).map v) ≫
          baseChangeProjection g X) :=
    (pushforwardAlgebraMap_comp ((Over.map g).map ((Over.pullback g).map v))
      (baseChangeProjection g X)).symm
  exact hl.trans (Eq.trans
    (congrArg pushforwardAlgebraMap (baseChangeProjection_naturality g v).symm) hr.symm)

end Naturality

/-! ### The two remaining clauses of Stacks Tag 01SA -/

section Clauses

variable {T S : Scheme.{u}} (g : T ⟶ S)

/-- Pullback of algebra sheaves along `g`, restricted to the quasi-coherent algebras.  This is
the functor `F` bound by the `let` of the `baseChangeIso` clause of [Stacks, Tag 01SA]. -/
def qcohAlgebraPullback : QuasicoherentAlgebra S ⥤ QuasicoherentAlgebra T :=
  ObjectProperty.lift _ ((IsQuasicoherentAlgebra S).ι ⋙ algebraPullback g)
    fun A => algebraPullback_isQuasicoherent g A.obj A.property

/-- `qcohAlgebraPullback g` is the `let`-bound functor of the `baseChangeIso` clause of Tag 01SA,
on the nose. -/
theorem qcohAlgebraPullback_eq :
    qcohAlgebraPullback g = ObjectProperty.lift _
      ((IsQuasicoherentAlgebra S).ι ⋙ algebraPullback g)
      (fun A => algebraPullback_isQuasicoherent g A.obj A.property) := rfl

/-- The natural transformation underlying the base-change isomorphism: at an object `X` affine
over `S` it is the canonical base-change morphism of `𝒪_T`-algebras. -/
def baseChangeNatTrans :
    (affineQuasicoherentEquivalence S).functor ⋙ qcohAlgebraPullback g ⟶
      (AlgebraicGeometry.affineBaseChange g).op ⋙
        (affineQuasicoherentEquivalence T).functor where
  app Xop :=
    have := Xop.unop.property
    ObjectProperty.homMk (baseChangeAlgebraHom g Xop.unop.obj)
  naturality Xop Yop φ := by
    have := Xop.unop.property
    have := Yop.unop.property
    exact ObjectProperty.hom_ext _
      (baseChangeAlgebraHom_naturality g ((IsAffineHomOver S).ι.map φ.unop))

/-- The components of `baseChangeNatTrans`, read in the category of all algebra sheaves, are
the canonical base-change morphisms. -/
theorem ι_map_baseChangeNatTrans_app (X : AffineOver S) :
    (IsQuasicoherentAlgebra T).ι.map ((baseChangeNatTrans g).app (.op X))
      = baseChangeAlgebraHom g X.obj := rfl

/-- Every component of `baseChangeNatTrans` is invertible. -/
theorem isIso_baseChangeNatTrans_app (Xop : (AffineOver S)ᵒᵖ) :
    IsIso ((baseChangeNatTrans g).app Xop) := by
  have := Xop.unop.property
  have : IsIso ((IsQuasicoherentAlgebra T).ι.map ((baseChangeNatTrans g).app Xop)) :=
    isIso_baseChangeAlgebraHom g Xop.unop.obj
  exact (IsQuasicoherentAlgebra T).fullyFaithfulι.isIso_of_isIso_map _

attribute [local instance] isIso_baseChangeNatTrans_app

/-- **The `baseChangeIso` clause of [Stacks, Tag 01SA].**  The anti-equivalence between the
schemes affine over a base and the quasi-coherent algebra sheaves on it commutes with arbitrary
base change, naturally.  Objectwise the isomorphism is the canonical base-change morphism
`g⁻¹(X_* 𝒪_X) ⊗_{g⁻¹𝒪_S} 𝒪_T ⟶ (X ×_S T)_* 𝒪_{X ×_S T}`. -/
def baseChangeIso :
    (affineQuasicoherentEquivalence S).functor ⋙ qcohAlgebraPullback g ≅
      (AlgebraicGeometry.affineBaseChange g).op ⋙
        (affineQuasicoherentEquivalence T).functor :=
  have : IsIso (baseChangeNatTrans g) := NatIso.isIso_of_isIso_app _
  asIso (baseChangeNatTrans g)

/-- The components of `baseChangeIso`, read in the category of all algebra sheaves, are the
canonical base-change morphisms. -/
theorem ι_map_baseChangeIso_hom_app (X : AffineOver S) :
    (IsQuasicoherentAlgebra T).ι.map ((baseChangeIso g).hom.app (.op X))
      = baseChangeAlgebraHom g X.obj := rfl

/-- **The `baseChangeIso_canonical` clause of [Stacks, Tag 01SA].**  After identifying the
anti-equivalence with pushforward of structure sheaves, the base-change isomorphism is the
canonical comparison induced by the fibre-product projection. -/
theorem baseChangeIso_canonical (X : AffineOver S) :
    (algebraPullbackMap g).app
          ((affineQuasicoherentEquivalence S).functor.obj (.op X)).obj ≫
        ((IsQuasicoherentAlgebra T).ι.map ((baseChangeIso g).hom.app (.op X)) ≫
            (pushforwardIsoOfEquivalence T
                ((AlgebraicGeometry.affineBaseChange g).obj X)).hom).right
      = (TopCat.Sheaf.pullback CommRingCat g.base).map
            (pushforwardIsoOfEquivalence S X).hom.right ≫
          pushforwardBaseChangeMap g X.obj := by
  have hS : (pushforwardIsoOfEquivalence S X).hom.right
      = 𝟙 (pushforwardAlgebra X.obj.hom).right := rfl
  have hL : ((IsQuasicoherentAlgebra T).ι.map ((baseChangeIso g).hom.app (.op X)) ≫
        (pushforwardIsoOfEquivalence T
            ((AlgebraicGeometry.affineBaseChange g).obj X)).hom).right
      = (baseChangeAlgebraHom g X.obj).right := by
    refine congrArg Under.Hom.right (Eq.trans ?_ (ι_map_baseChangeIso_hom_app g X))
    exact Category.comp_id _
  have hR : (TopCat.Sheaf.pullback CommRingCat g.base).map
      (pushforwardIsoOfEquivalence S X).hom.right = 𝟙 _ := by
    rw [hS]
    exact (TopCat.Sheaf.pullback CommRingCat g.base).map_id _
  rw [hL, hR]
  exact Eq.trans (algebraPullbackMap_comp_baseChangeAlgebraHom g X.obj)
    (Category.id_comp _).symm

end Clauses

/-! ### The nine clauses, assembled -/

/-- **All nine clauses of [Stacks, Tag 01SA].**  The canonical anti-equivalence between the
schemes affine over a base and the quasi-coherent sheaves of commutative algebras on that base,
compatible with arbitrary base change.

The tag is registered by a single unqualified attribute on this nine-field structure. -/
@[stacks 01SA, sga "3 I 4.2" "more general"]
def affineEquivalenceAlgebras : AffineAlgebraAntiEquivalence.{u} where
  algebraPullback g := algebraPullback g
  algebraPullbackMap g := algebraPullbackMap g
  algebraPullback_isPushout g A := algebraPullback_isPushout g A
  algebraPullback_isQuasicoherent g A := algebraPullback_isQuasicoherent g A.obj A.property
  equivalence S := affineQuasicoherentEquivalence S
  pushforwardIso S X := pushforwardIsoOfEquivalence S X
  pushforwardIso_naturality S := pushforwardIsoOfEquivalence_naturality S
  baseChangeIso g := baseChangeIso g
  baseChangeIso_canonical g X := baseChangeIso_canonical g X

end Stacks.AlgebraPullbackQcoh

end
