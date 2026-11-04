module

public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.BaseChangeIso
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.AffineBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.AntiEquivalence
public import StacksFrontier.AlgebraicGeometry.RelativeSpecOpenRestriction.RestrictAlgebra
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of a quasi-coherent algebra along an arbitrary morphism is quasi-coherent

Let `g : T ⟶ S` be an arbitrary morphism of schemes and let `A` be a quasi-coherent sheaf of
commutative `𝒪_S`-algebras.  This file proves that the base change
`(algebraPullback g).obj A = g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` is quasi-coherent.  This is the residual
assertion `Stacks.AffineAlgebraEquivalence.IsQuasicoherentAlgebraPullback` on which the
base-change clause of Stacks Tag 01SA was left standing, and it is the hypothesis needed for
Stacks Tag 01LX part (2) to be stated at all.

The proof is the reduction to the affine case
`Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_of_isAffine`.  Quasi-coherence
of a sheaf of modules is local on the base, so it suffices to check it on the members of an open
covering of `T`; the covering used consists of the affine opens `W` of `T` whose image under `g`
lies in an affine open `V` of `S`, which cover `T` because the affine opens of either scheme form
a basis.  For such a `W`, the inclusion factors as `W.ι ≫ g = g' ≫ V.ι` with
`g' : W ⟶ V` a morphism of affine schemes, so pseudofunctoriality of base change
(`Stacks.AffineAlgebraEquivalence.algebraPullbackComp`) identifies the restriction to `W` of
`(algebraPullback g).obj A` with the base change along `g'` of the restriction of `A` to `V`.
The restriction of `A` to `V` is quasi-coherent by
`Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_of_isOpenImmersion`, and the
affine case applies to `g'`.

## Main definitions

* `Stacks.AffineAlgebraEquivalence.AffineFactorization` indexes the covering: a pair of an affine
  open of `T` and an affine open of `S` containing its image.
* `Stacks.AffineAlgebraEquivalence.algebraPullbackRestrictIso` is the identification of the
  restriction to `W` of the base change along `g` with the base change along `g'` of the
  restriction to `V`.

## Main results

* `AlgebraicGeometry.exists_affineOpen_factorization` and
  `Stacks.AffineAlgebraEquivalence.isOpenCover_affineFactorization`: the affine opens of `T`
  whose image lies in an affine open of `S` cover `T`.
* `Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_obj`: **the base change of a
  quasi-coherent algebra along an arbitrary morphism is quasi-coherent.**
* `Stacks.AffineAlgebraEquivalence.isQuasicoherentAlgebraPullback`: the same statement in the
  packaged form `IsQuasicoherentAlgebraPullback`, which discharges the one hypothesis of
  `Stacks.AffineAlgebraEquivalence.antiEquivalenceOfQuasicoherentAlgebraPullback`.
* `Stacks.AffineAlgebraEquivalence.isIso_baseChangeAlgebraHom`: **the base-change assertion of
  Stacks Tag 01SA for an arbitrary morphism.**  For `X` affine over `S` the comparison
  `g⁻¹(X.hom _* 𝒪_X) ⊗_{g⁻¹𝒪_S} 𝒪_T ⟶ (X ×_S T ⟶ T) _* 𝒪_{X ×_S T}` is an isomorphism.

## Implementation notes

The covering is indexed by a subtype of `T.Opens × S.Opens` rather than by a structure, so that
no new structure is introduced and so that the index type lands in `Type u`, as
`Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_of_presentations` requires.

Locality is applied in the form of that lemma rather than through
`SheafOfModules.IsQuasicoherent.of_coversTop`: the former is stated for the restrictions
`Scheme.Modules.restrictFunctor (W i).ι` to the open subschemes, which is exactly the shape in
which `Stacks.AffineAlgebraEquivalence.isQuasicoherent_restrict_underlyingModule` delivers
quasi-coherence, whereas the latter is stated on the slice sites and would need the transport
`AlgebraicGeometry.Scheme.Modules.overEquiv` in the direction that reflects quasi-coherence.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.RelativeSpec.AlgebraSheaf

universe u

namespace AlgebraicGeometry

/-- **Every point of `T` has an affine open neighbourhood whose image under `g` lies in an affine
open of `S`.** The affine opens of `S` form a basis, so the image of the point lies in one of
them; its preimage is then an open neighbourhood of the point, inside which the affine opens of
`T` likewise form a basis. -/
public theorem exists_affineOpen_factorization {T S : Scheme.{u}} (g : T ⟶ S) (x : T) :
    ∃ (W : T.Opens) (V : S.Opens),
      IsAffineOpen W ∧ IsAffineOpen V ∧ x ∈ W ∧ W ≤ g ⁻¹ᵁ V := by
  obtain ⟨V, hV, hgxV, -⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
    (show g.base x ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨W, hW, hxW, hWV⟩ := Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
    (show x ∈ g ⁻¹ᵁ V from hgxV)
  exact ⟨W, V, hW, hV, hxW, hWV⟩

end AlgebraicGeometry

namespace Stacks.AffineAlgebraEquivalence

/-! ### The covering by affine opens with affine image -/

/-- The index of the covering used to reduce base change of algebras to the affine case: an
affine open `W` of `T` together with an affine open `V` of `S` whose preimage contains `W`. -/
public abbrev AffineFactorization {T S : Scheme.{u}} (g : T ⟶ S) : Type u :=
  { p : T.Opens × S.Opens // IsAffineOpen p.1 ∧ IsAffineOpen p.2 ∧ p.1 ≤ g ⁻¹ᵁ p.2 }

/-- The affine opens of `T` whose image under `g` lies in an affine open of `S` cover `T`. -/
public theorem isOpenCover_affineFactorization {T S : Scheme.{u}} (g : T ⟶ S) :
    IsOpenCover fun p : AffineFactorization g ↦ p.1.1 := by
  refine IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ ?_)
  obtain ⟨W, V, hW, hV, hxW, hWV⟩ := exists_affineOpen_factorization g x
  exact Opens.mem_iSup.mpr ⟨⟨(W, V), hW, hV, hWV⟩, hxW⟩

/-! ### The reduction to a morphism of affine schemes -/

variable {T S : Scheme.{u}} (g : T ⟶ S) (A : Stacks.RelativeSpec.AlgebraSheaf.{u} S)

/-- **The restriction to `W` of the base change along `g` is the base change along `g' : W ⟶ V`
of the restriction to `V`.** Both are the base change along the composite `W.ι ≫ g = g' ≫ V.ι`,
by pseudofunctoriality of base change of algebras. -/
public noncomputable def algebraPullbackRestrictIso {W : T.Opens} {V : S.Opens}
    (h : W ≤ g ⁻¹ᵁ V) :
    (algebraPullback W.ι).obj ((algebraPullback g).obj A) ≅
      (algebraPullback (g.resLE V W h)).obj ((algebraPullback V.ι).obj A) :=
  ((algebraPullbackComp W.ι g).app A).symm ≪≫
    eqToIso (congrArg (fun f : W.toScheme ⟶ S ↦ (algebraPullback f).obj A)
      (g.resLE_comp_ι h).symm) ≪≫
    (algebraPullbackComp (g.resLE V W h) V.ι).app A

/-- The restriction to an affine open `W` of `T` of the base change of a quasi-coherent algebra
along `g` is quasi-coherent, provided the image of `W` lies in an affine open `V` of `S`: the
restriction of `A` to `V` is quasi-coherent, and the induced morphism `W ⟶ V` is a morphism of
affine schemes, so the affine case of the tag applies. -/
public theorem isQuasicoherent_algebraPullback_restrict
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A] {W : T.Opens} {V : S.Opens}
    (hW : IsAffineOpen W) (hV : IsAffineOpen V) (h : W ≤ g ⁻¹ᵁ V) :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent
      ((algebraPullback W.ι).obj ((algebraPullback g).obj A)) :=
  have : IsAffine W.toScheme := hW
  have : IsAffine V.toScheme := hV
  have : Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent ((algebraPullback V.ι).obj A) :=
    isQuasicoherent_algebraPullback_of_isOpenImmersion V.ι A
  Stacks.RelativeSpec.AlgebraSheaf.isQuasicoherent_of_iso
    (algebraPullbackRestrictIso g A h).symm
    (isQuasicoherent_algebraPullback_of_isAffine (g.resLE V W h)
      ((algebraPullback V.ι).obj A))

/-! ### The theorem -/

/-- **The base change of a quasi-coherent algebra along an arbitrary morphism of schemes is
quasi-coherent.** This is the residual assertion of Stacks Tag 01SA, and the prerequisite for
Stacks Tag 01LX part (2).

Quasi-coherence is local on `T`, and on each member of the covering
`isOpenCover_affineFactorization` the base change is a base change along a morphism of affine
schemes, by `isQuasicoherent_algebraPullback_restrict`. -/
public instance isQuasicoherent_algebraPullback_obj
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A] :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent ((algebraPullback g).obj A) := by
  refine Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_of_presentations
    (underlyingModule ((algebraPullback g).obj A))
    (fun p : AffineFactorization g ↦ p.1.1) (isOpenCover_affineFactorization g) fun p ↦ ?_
  obtain ⟨⟨W, V⟩, hW, hV, h⟩ := p
  haveI : ((Scheme.Modules.restrictFunctor W.ι).obj
      (underlyingModule ((algebraPullback g).obj A))).IsQuasicoherent :=
    isQuasicoherent_restrict_underlyingModule W.ι ((algebraPullback g).obj A)
      (isQuasicoherent_algebraPullback_restrict g A hW hV h)
  exact (Stacks.AlgebraicGeometry.AffinePushforward.nonempty_presentation_of_isoSpec
    hW.isoSpec _).some

/-- **The residual assertion of Stacks Tag 01SA, proved.** Base change of a quasi-coherent
algebra along an arbitrary morphism of schemes is quasi-coherent.  Feeding this to
`Stacks.AffineAlgebraEquivalence.antiEquivalenceOfQuasicoherentAlgebraPullback` makes the
base-change-compatible anti-equivalence of that tag unconditional. -/
public theorem isQuasicoherentAlgebraPullback : IsQuasicoherentAlgebraPullback.{u} :=
  fun g A ↦ have := A.property; isQuasicoherent_algebraPullback_obj g A.obj

/-- **The base-change assertion of Stacks Tag 01SA for an arbitrary morphism.** For `X` affine
over `S` the comparison
`g⁻¹(X.hom _* 𝒪_X) ⊗_{g⁻¹𝒪_S} 𝒪_T ⟶ (X ×_S T ⟶ T) _* 𝒪_{X ×_S T}` is an isomorphism. -/
public alias isIso_baseChangeAlgebraHom := Stacks.AlgebraPullbackQcoh.isIso_baseChangeAlgebraHom

/-- **Stacks Project, Tag 01SA, the base-change clause.** The anti-equivalence between the
schemes affine over `S` and the quasi-coherent sheaves of `𝒪_S`-algebras is compatible with
arbitrary base change, unconditionally: the one assertion on which
`Stacks.AffineAlgebraEquivalence.antiEquivalenceOfQuasicoherentAlgebraPullback` was left standing
is `isQuasicoherentAlgebraPullback`, proved above. -/
@[stacks 01SA "compatibility of the anti-equivalence with arbitrary base change",
  ega "II 1.5.2",
  sga "3 I 4.2" "more general"]
public noncomputable def affineAlgebraAntiEquivalence : AffineAlgebraAntiEquivalence.{u} :=
  antiEquivalenceOfQuasicoherentAlgebraPullback isQuasicoherentAlgebraPullback

end Stacks.AffineAlgebraEquivalence

end
