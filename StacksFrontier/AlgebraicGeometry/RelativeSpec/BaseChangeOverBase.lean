module

public import StacksFrontier.AlgebraicGeometry.RelativeSpec.BaseFunctoriality
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.RelativeSpecOpenRestriction.RelativeSpecBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The base change of a relative spectrum as a morphism over the base

Let `g : T ⟶ S` be a morphism of schemes, `A` a quasi-coherent `𝒪_S`-algebra and `A'` a
quasi-coherent `𝒪_T`-algebra.  There are two ways to produce a morphism of schemes
`\underline{Spec}_T(A') ⟶ \underline{Spec}_S(A)` lying over `g` from algebra data:

* from a morphism `ψ : g^*A ⟶ A'` of `𝒪_T`-algebras, by contravariance of the relative spectrum
  in the algebra followed by Stacks 01LX (2), which identifies `\underline{Spec}_T(g^*A)` with
  the fibre product `\underline{Spec}_S(A) ×_S T`, and then the projection;
* from a morphism `φ : A ⟶ g_* A'` of `𝒪_S`-algebras, by the universal property of the relative
  spectrum over a varying base, `Stacks.AffineAlgebraEquivalence.relativeSpecMapOverBase`.

This file proves that **the two agree under the adjunction** `g^* ⊣ g_*` of Stacks 01SA: the
morphism built from `ψ` is the morphism built from the adjunct of `ψ`.  The point of the
identification is functoriality.  The first description is the one a base-change construction
produces, and in it the composition law is invisible: a cartesian square pins its top edge down
only up to an automorphism over the base, and an affine morphism has those.  The second
description is *rigid* — `Stacks.AffineAlgebraEquivalence.relativeSpecOverBaseHom_ext` says a
morphism of relative spectra over `g` is determined by its algebra map — so in it the
composition law is a statement about morphisms of algebra sheaves, and that is proved here.

## Main results

* `Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_overRelativeSpecIso_hom` and
  `Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_relativeSpecOverIso_hom`, with their
  `inv` counterparts: the canonical maps on pushed-forward structure sheaves of the two
  isomorphisms out of which Stacks 01LX (2) is assembled.  Both are *exhibited*: each of the two
  isomorphisms is the preimage, under the fully faithful functor `X ↦ X.hom _* 𝒪_X`, of a
  prescribed isomorphism of algebras, so the algebra map it induces is that isomorphism back
  again.
* `Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_relativeSpecBaseChangeIso_inv`: **the
  algebra map of the comparison of Stacks 01LX (2)** is
  `Stacks.AffineAlgebraEquivalence.pullbackAlgebraIso` followed by the inverse of the universal
  isomorphism of the relative spectrum of `g^*A`.
* `Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeMap_eq_relativeSpecMapOverBase`: **the
  identification.** The morphism over `g` that `ψ : g^*A ⟶ A'` induces through Stacks 01LX (2)
  is the morphism over `g` that the adjunct `A ⟶ g_* A'` of `ψ` induces through the universal
  property over a varying base.
* `Stacks.AffineAlgebraEquivalence.relativeSpecMapOverBase_comp`: **the composition law.**
  Composing the morphisms attached to `φ : A ⟶ g_* A'` and `φ' : A' ⟶ g'_* A''` gives the
  morphism attached to `φ` followed by `g_* φ'`, over the composite `g' ≫ g`.

## Implementation notes

**Why the composition law needs no transport.**  The source of
`Stacks.AffineAlgebraEquivalence.relativeSpecOverBaseHom` over `g' ≫ g` is
`CategoryTheory.Over.mk (relativeSpecToBase A'' ≫ g' ≫ g)`, whereas composing through the
intermediate base presents it as `CategoryTheory.Over.mk ((relativeSpecToBase A'' ≫ g') ≫ g)`.
These are different objects of `CategoryTheory.Over S`, and the associator between them is not
an identity.  No transport is needed nonetheless, because the two objects have the *same*
pushed-forward structure sheaf, definitionally:
`Stacks.AffineAlgebraEquivalence.algebraPushforward_pushforwardAlgebra` holds by `rfl`, and so
does `algebraPushforward g' ⋙ algebraPushforward g = algebraPushforward (g' ≫ g)` — the fact
already relied on by `Stacks.AffineAlgebraEquivalence.algebraPullbackComp`, which identifies two
left adjoints of literally the same functor.  So both associations of the structure morphism have
the same pushed-forward structure sheaf, and the equation between algebra maps type-checks as it
stands.

**Where rigidity is applied.**  Every proof below of an equation between morphisms of schemes
goes through `Stacks.AffineAlgebraEquivalence.relativeSpecOverBaseHom_ext`, whose hypothesis is
on the *target* only: the target is a relative spectrum, hence affine over the base.  No
affineness of `g`, of `g'`, or of the sources is used, and none is assumed.

**There is no identity law here, and it is not needed.**  `relativeSpecMapOverBase (𝟙 S) A A`
cannot be fed the identity of `A`: its argument must be a map `A ⟶ (algebraPushforward (𝟙 S)).obj
A`, and the direct image along an identity is not the identity functor on the nose — the
pushforward of sheaves along `(𝟙 S).base` is precomposition with the inverse image of opens.
Consumers get the identity law from the composition law instead: the morphism attached to an
identity of bases is idempotent by the composition law and invertible because it is a base change
of an isomorphism, and an idempotent isomorphism is the identity.

**No `stacks` attribute is carried.**  Stacks 01LX (2) is registered where it is proved, at
`Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso`; Stacks 01LP and 01S4 are the
universal property over a fixed base.  What is added here is the comparison of the two
descriptions of a morphism over a varying base, and the composition law that the rigid
description makes available — consequences of those statements rather than assertions of the
source.

## References

* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01S4](https://stacks.math.columbia.edu/tag/01S4)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.AffineAlgebraEquivalence

/-! ### The algebra maps of the two isomorphisms behind Stacks 01LX (2) -/

section Isos

variable {S : Scheme.{u}}

/-- The two fully faithful functors `X ↦ f_* 𝒪_X` and `ι` are undone by taking preimages. -/
private theorem map_map_preimage_preimage {S : Scheme.{u}} {X Y : (AffineOver S)ᵒᵖ}
    (h : (IsQuasicoherentAlgebra S).ι.obj ((affineQuasicoherentPushforwardFunctor S).obj X) ⟶
      (IsQuasicoherentAlgebra S).ι.obj ((affineQuasicoherentPushforwardFunctor S).obj Y)) :
    (IsQuasicoherentAlgebra S).ι.map ((affineQuasicoherentPushforwardFunctor S).map
      ((fullyFaithfulAffineQuasicoherentPushforwardFunctor S).preimage
        ((IsQuasicoherentAlgebra S).ι.preimage h))) = h :=
  (congrArg (IsQuasicoherentAlgebra S).ι.map
    ((fullyFaithfulAffineQuasicoherentPushforwardFunctor S).map_preimage _)).trans
    ((IsQuasicoherentAlgebra S).ι.map_preimage _)

/-- **The algebra map of Stacks 01S8.**  The comparison `X ≅ \underline{Spec}_S(f_* 𝒪_X)` of an
affine morphism with the relative spectrum of its pushed-forward structure sheaf induces, on
pushed-forward structure sheaves, the universal isomorphism
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso` of that relative spectrum.

The comparison is the preimage of that isomorphism under the fully faithful functor
`X ↦ X.hom _* 𝒪_X`, so this is full faithfulness read forwards. -/
theorem pushforwardAlgebraMap_overRelativeSpecIso_hom {X : Scheme.{u}} (f : X ⟶ S)
    [IsAffineHom f] :
    letI := isQuasicoherent_pushforwardAlgebra f
    pushforwardAlgebraMap (overRelativeSpecIso f).hom =
      (pushforwardAlgebraIso (pushforwardAlgebra f)).hom := by
  let := isQuasicoherent_pushforwardAlgebra f
  show (IsQuasicoherentAlgebra S).ι.map ((affineQuasicoherentPushforwardFunctor S).map
      ((affineOverRelativeSpecIso f).hom).op) = _
  exact map_map_preimage_preimage _

/-- The inverse comparison of Stacks 01S8 induces the inverse of the universal isomorphism. -/
theorem pushforwardAlgebraMap_overRelativeSpecIso_inv {X : Scheme.{u}} (f : X ⟶ S)
    [IsAffineHom f] :
    letI := isQuasicoherent_pushforwardAlgebra f
    pushforwardAlgebraMap (overRelativeSpecIso f).inv =
      (pushforwardAlgebraIso (pushforwardAlgebra f)).inv := by
  let := isQuasicoherent_pushforwardAlgebra f
  show (IsQuasicoherentAlgebra S).ι.map ((affineQuasicoherentPushforwardFunctor S).map
      ((affineOverRelativeSpecIso f).inv).op) = _
  exact map_map_preimage_preimage _

variable {A A' : Stacks.RelativeSpec.AlgebraSheaf.{u} S}
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A]
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A'] (e : A ≅ A')

/-- **The algebra map of the transport of the relative spectrum along an isomorphism of
algebras.**  The isomorphism `\underline{Spec}_S(A) ≅ \underline{Spec}_S(A')` attached to
`e : A ≅ A'` induces on pushed-forward structure sheaves the inverse of `e`, read through the two
universal isomorphisms. -/
theorem pushforwardAlgebraMap_relativeSpecOverIso_hom :
    pushforwardAlgebraMap (relativeSpecOverIso e).hom =
      (pushforwardAlgebraIso A').hom ≫ e.inv ≫ (pushforwardAlgebraIso A).inv := by
  show (IsQuasicoherentAlgebra S).ι.map ((affineQuasicoherentPushforwardFunctor S).map
      ((relativeSpecAffineOverIso e).hom).op) = _
  exact map_map_preimage_preimage _

/-- The inverse transport induces `e` itself, read through the two universal isomorphisms. -/
theorem pushforwardAlgebraMap_relativeSpecOverIso_inv :
    pushforwardAlgebraMap (relativeSpecOverIso e).inv =
      (pushforwardAlgebraIso A).hom ≫ e.hom ≫ (pushforwardAlgebraIso A').inv := by
  show (IsQuasicoherentAlgebra S).ι.map ((affineQuasicoherentPushforwardFunctor S).map
      ((relativeSpecAffineOverIso e).inv).op) = _
  exact (map_map_preimage_preimage _).trans (Category.assoc _ _ _)

end Isos

/-! ### The algebra map of the comparison of Stacks 01LX (2) -/

section BaseChange

variable {T S : Scheme.{u}} (g : T ⟶ S) (A : Stacks.RelativeSpec.AlgebraSheaf.{u} S)
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A]

/-- **The algebra map of the comparison of Stacks 01LX (2).**  The inverse of the identification
`\underline{Spec}_S(A) ×_S T ≅ \underline{Spec}_T(g^*A)` induces, on pushed-forward structure
sheaves, the identification `Stacks.AffineAlgebraEquivalence.pullbackAlgebraIso` of the
pushed-forward structure sheaf of the fibre product with `g^*A`, followed by the inverse of the
universal isomorphism of the relative spectrum of `g^*A`.

Both factors of the comparison are preimages under the fully faithful functor
`X ↦ X.hom _* 𝒪_X`, and the universal isomorphism of the pushed-forward structure sheaf of the
fibre product cancels between them. -/
theorem pushforwardAlgebraMap_relativeSpecBaseChangeIso_inv :
    pushforwardAlgebraMap (relativeSpecBaseChangeIso g A).inv =
      (pullbackAlgebraIso g A).hom ≫
        (pushforwardAlgebraIso ((algebraPullback g).obj A)).inv := by
  have : IsAffineHom (Over.mk (relativeSpecToBase A)).hom := isAffineHom_relativeSpecToBase A
  have : IsAffineHom ((Over.pullback g).obj (Over.mk (relativeSpecToBase A))).hom :=
    isAffineHom_overPullback_hom g (Over.mk (relativeSpecToBase A))
  have := isQuasicoherent_pushforwardAlgebra
    ((Over.pullback g).obj (Over.mk (relativeSpecToBase A))).hom
  rw [relativeSpecBaseChangeIso, Iso.trans_inv, pushforwardAlgebraMap_comp,
    pushforwardAlgebraMap_overRelativeSpecIso_inv,
    pushforwardAlgebraMap_relativeSpecOverIso_inv, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- The base-change comparison of algebras, followed by the identification
`Stacks.AffineAlgebraEquivalence.pullbackAlgebraIso` of the pushed-forward structure sheaf of the
fibre product with `g^*A`, is the base change of the universal isomorphism of
`\underline{Spec}_S(A)`.

This is the definition of `Stacks.AffineAlgebraEquivalence.pullbackAlgebraIso` with the
base-change comparison, which is invertible by
`Stacks.AffineAlgebraEquivalence.isIso_baseChangeAlgebraHom`, cancelled against its inverse. -/
theorem baseChangeAlgebraHom_comp_pullbackAlgebraIso_hom :
    baseChangeAlgebraHom g (Over.mk (relativeSpecToBase A)) ≫ (pullbackAlgebraIso g A).hom =
      (algebraPullback g).map (pushforwardAlgebraIso A).hom := by
  have : IsAffineHom (Over.mk (relativeSpecToBase A)).hom := isAffineHom_relativeSpecToBase A
  rw [pullbackAlgebraIso, Iso.trans_hom, Functor.mapIso_hom, ← Category.assoc, Iso.symm_hom,
    asIso_inv, IsIso.hom_inv_id, Category.id_comp]

end BaseChange

/-! ### The identification of the two descriptions of a morphism over the base -/

section Identification

variable {T S : Scheme.{u}} (g : T ⟶ S) (A : Stacks.RelativeSpec.AlgebraSheaf.{u} S)
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A]
    (A' : Stacks.RelativeSpec.AlgebraSheaf.{u} T)
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A']

/-- The algebra map, read over `S`, of the morphism into the fibre product that `ψ : g^*A ⟶ A'`
induces by contravariance followed by Stacks 01LX (2): it is the base change of the universal
isomorphism of `\underline{Spec}_S(A)`, then `ψ`, then the inverse of the universal isomorphism
of `\underline{Spec}_T(A')`.

Every universal isomorphism of the relative spectrum of `g^*A` cancels: the comparison of Stacks
01LX (2) contributes its inverse and contravariance in the algebra contributes it. -/
@[ega "II 1.5.6" "algebra map of w is u♯"]
theorem baseChangeAlgebraHom_comp_pushforwardAlgebraMap_relativeSpecBaseChange
    (ψ : (algebraPullback g).obj A ⟶ A') :
    baseChangeAlgebraHom g (Over.mk (relativeSpecToBase A)) ≫
        pushforwardAlgebraMap (relativeSpecMapOfAlgebraHom ((algebraPullback g).obj A) A' ψ ≫
          (relativeSpecBaseChangeIso g A).inv) =
      (algebraPullback g).map (pushforwardAlgebraIso A).hom ≫ ψ ≫
        (pushforwardAlgebraIso A').inv := by
  rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_relativeSpecBaseChangeIso_inv,
    pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom, Category.assoc,
    Iso.inv_hom_id_assoc, ← Category.assoc,
    baseChangeAlgebraHom_comp_pullbackAlgebraIso_hom]

/-- **The morphism of relative spectra over `g` attached to an algebra map `ψ : g^*A ⟶ A'` by
contravariance and Stacks 01LX (2) is the morphism attached to the adjunct of `ψ`.**

The left-hand side is the morphism a base-change construction produces: contravariance of the
relative spectrum in the algebra gives a morphism into `\underline{Spec}_T(g^*A)`, Stacks 01LX
(2) identifies that with the fibre product `\underline{Spec}_S(A) ×_S T`, and the projection
lands in `\underline{Spec}_S(A)`.  The right-hand side is the morphism the universal property
over a varying base attaches to the adjunct `A ⟶ g_* A'` of `ψ` under the adjunction of Stacks
01SA.

Both sides are morphisms over `g`, so by rigidity it suffices to compare the algebra maps they
induce, and that comparison is
`Stacks.AffineAlgebraEquivalence.homEquiv_baseChangeAlgebraHom_comp` together with the algebra
map of the comparison of Stacks 01LX (2). -/
@[ega "II 1.5.6"]
theorem relativeSpecBaseChangeMap_eq_relativeSpecMapOverBase
    (ψ : (algebraPullback g).obj A ⟶ A') :
    (relativeSpecMapOfAlgebraHom ((algebraPullback g).obj A) A' ψ ≫
          (relativeSpecBaseChangeIso g A).inv).left ≫
        pullback.fst (relativeSpecToBase A) g =
      relativeSpecMapOverBase g A A'
        ((algebraPullbackPushforwardAdjunction g).homEquiv A A' ψ) := by
  refine relativeSpecMapOverBase_eq_of_pushforwardAlgebraMap g A A' _
    ((Over.map g).map (relativeSpecMapOfAlgebraHom ((algebraPullback g).obj A) A' ψ ≫
        (relativeSpecBaseChangeIso g A).inv) ≫
      baseChangeProjection g (Over.mk (relativeSpecToBase A))) ?_
  rw [← homEquiv_baseChangeAlgebraHom_comp g (Over.mk (relativeSpecToBase A)),
    baseChangeAlgebraHom_comp_pushforwardAlgebraMap_relativeSpecBaseChange,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    relativeSpecOverBaseAlgebraHom_eq, relativeSpecPushforwardIsoOverBase, Functor.mapIso_inv]
  rfl

end Identification

/-! ### The composition law -/

section Functoriality

variable {T' T S : Scheme.{u}} (g' : T' ⟶ T) (g : T ⟶ S)
    (A : Stacks.RelativeSpec.AlgebraSheaf.{u} S)
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A]
    (A' : Stacks.RelativeSpec.AlgebraSheaf.{u} T)
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A']
    (A'' : Stacks.RelativeSpec.AlgebraSheaf.{u} T')
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A'']

/-- **Cancellation of the universal isomorphism of the intermediate relative spectrum.**  The
inverse of `Stacks.AffineAlgebraEquivalence.relativeSpecPushforwardIsoOverBase`, followed by the
direct image along `g` of a map out of `A'` which starts with the universal isomorphism, is the
direct image of the rest of that map.

Stated for a variable `k` rather than applied: the two spellings of the pushed-forward structure
sheaf which the implementation notes discuss make the unfolded form awkward to rewrite in, and
this absorbs the cancellation once. -/
theorem relativeSpecPushforwardIsoOverBase_inv_comp_map
    {C : Stacks.RelativeSpec.AlgebraSheaf.{u} T} (k : A' ⟶ C) :
    (relativeSpecPushforwardIsoOverBase g A').inv ≫
        (algebraPushforward g).map ((pushforwardAlgebraIso A').hom ≫ k) =
      (algebraPushforward g).map k :=
  Eq.trans
    (congrArg (fun z ↦ (relativeSpecPushforwardIsoOverBase g A').inv ≫ z)
      ((algebraPushforward g).map_comp (pushforwardAlgebraIso A').hom k))
    (Eq.trans (Category.assoc _ _ _).symm
      (Eq.trans
        (congrArg (fun z ↦ z ≫ (algebraPushforward g).map k)
          (relativeSpecPushforwardIsoOverBase g A').inv_hom_id)
        (Category.id_comp _)))

/-- **The composition law for the algebra maps.**  Composing the algebra map attached to
`φ : A ⟶ g_* A'` with the direct image along `g` of the algebra map attached to
`φ' : A' ⟶ g'_* A''` gives the algebra map attached, over `g' ≫ g`, to `φ` followed by the direct
image of `φ'`.  The universal isomorphism of `\underline{Spec}_T(A')` cancels between the two,
and the universal isomorphism of `\underline{Spec}_{T'}(A'')` pushed forward along `g` *is* the
one over the composite base morphism, by the same definitional equality the implementation notes
record. -/
theorem relativeSpecOverBaseAlgebraHom_comp (φ : A ⟶ (algebraPushforward g).obj A')
    (φ' : A' ⟶ (algebraPushforward g').obj A'') :
    relativeSpecOverBaseAlgebraHom g A A' φ ≫
        (algebraPushforward g).map (relativeSpecOverBaseAlgebraHom g' A' A'' φ') =
      relativeSpecOverBaseAlgebraHom (g' ≫ g) A A'' (φ ≫ (algebraPushforward g).map φ') :=
  have h : (relativeSpecPushforwardIsoOverBase g A').inv ≫
      (algebraPushforward g).map (relativeSpecOverBaseAlgebraHom g' A' A'' φ') =
        (algebraPushforward g).map φ' ≫
          (relativeSpecPushforwardIsoOverBase (g' ≫ g) A'').inv :=
    Eq.trans
      (relativeSpecPushforwardIsoOverBase_inv_comp_map g A'
        (φ' ≫ (relativeSpecPushforwardIsoOverBase g' A'').inv))
      ((algebraPushforward g).map_comp φ' (relativeSpecPushforwardIsoOverBase g' A'').inv)
  Eq.trans (Category.assoc _ _ _)
    (congrArg (fun z ↦ (pushforwardAlgebraIso A).hom ≫ z)
      (Eq.trans (Category.assoc _ _ _)
        (Eq.trans (congrArg (fun z ↦ φ ≫ z) h) (Category.assoc _ _ _).symm)))

/-- The morphism of relative spectra over `g'` attached to `φ' : A' ⟶ g'_* A''`, read as a
morphism of schemes over `S` through `g`. -/
def relativeSpecOverBaseHomComp (φ' : A' ⟶ (algebraPushforward g').obj A'') :
    (Over.mk (relativeSpecToBase A'' ≫ g' ≫ g) : Over S) ⟶
      Over.mk (relativeSpecToBase A' ≫ g) :=
  Over.homMk (relativeSpecMapOverBase g' A' A'' φ') (by
    change relativeSpecMapOverBase g' A' A'' φ' ≫ relativeSpecToBase A' ≫ g =
      relativeSpecToBase A'' ≫ g' ≫ g
    rw [← Category.assoc, relativeSpecMapOverBase_comp_toBase, Category.assoc])

/-- The algebra map, over `S`, of a morphism over `T` read over `S` is the direct image along `g`
of its algebra map over `T`.  The two sides are morphisms between the *same* algebra sheaves:
the two associations of the structure morphism of the source have the same pushed-forward
structure sheaf definitionally, as the implementation notes record. -/
theorem pushforwardAlgebraMap_relativeSpecOverBaseHomComp
    (φ' : A' ⟶ (algebraPushforward g').obj A'') :
    pushforwardAlgebraMap (relativeSpecOverBaseHomComp g' g A' A'' φ') =
      (algebraPushforward g).map
        (pushforwardAlgebraMap (relativeSpecOverBaseHom g' A' A'' φ')) := by
  ext1
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun Uop => ?_)
  obtain ⟨U⟩ := Uop
  rw [algebraPushforward_map_right_app,
    pushforwardAlgebraMap_app (relativeSpecOverBaseHom g' A' A'' φ') (g ⁻¹ᵁ U)
      (preimage_le_preimage_preimage _ _),
    pushforwardAlgebraMap_app (relativeSpecOverBaseHomComp g' g A' A'' φ') U
      (preimage_le_preimage_preimage _ _)]
  rfl

/-- **The composition law for morphisms of relative spectra over a varying base.**  The
composite of the morphism attached to `φ : A ⟶ g_* A'` with the morphism attached to
`φ' : A' ⟶ g'_* A''` is the morphism over `g' ≫ g` attached to `φ` followed by the direct image
along `g` of `φ'`.

Both sides are morphisms over `g' ≫ g` into `\underline{Spec}_S(A)`, which is affine over `S`,
so by rigidity it suffices that they induce the same algebra map, and there the statement is
`Stacks.AffineAlgebraEquivalence.relativeSpecOverBaseAlgebraHom_comp`. -/
theorem relativeSpecMapOverBase_comp (φ : A ⟶ (algebraPushforward g).obj A')
    (φ' : A' ⟶ (algebraPushforward g').obj A'') :
    relativeSpecMapOverBase g' A' A'' φ' ≫ relativeSpecMapOverBase g A A' φ =
      relativeSpecMapOverBase (g' ≫ g) A A'' (φ ≫ (algebraPushforward g).map φ') :=
  relativeSpecMapOverBase_eq_of_pushforwardAlgebraMap (g' ≫ g) A A'' _
    (relativeSpecOverBaseHomComp g' g A' A'' φ' ≫ relativeSpecOverBaseHom g A A' φ)
    (Eq.trans (pushforwardAlgebraMap_comp _ _)
      (Eq.trans
        (congrArg (fun z ↦ z ≫ pushforwardAlgebraMap
            (relativeSpecOverBaseHomComp g' g A' A'' φ'))
          (pushforwardAlgebraMap_relativeSpecOverBaseHom g A A' φ))
        (Eq.trans
          (congrArg (fun z ↦ relativeSpecOverBaseAlgebraHom g A A' φ ≫ z)
            (Eq.trans (pushforwardAlgebraMap_relativeSpecOverBaseHomComp g' g A' A'' φ')
              (congrArg (algebraPushforward g).map
                (pushforwardAlgebraMap_relativeSpecOverBaseHom g' A' A'' φ'))))
          (relativeSpecOverBaseAlgebraHom_comp g' g A A' A'' φ φ'))))

end Functoriality

end Stacks.AffineAlgebraEquivalence

end
