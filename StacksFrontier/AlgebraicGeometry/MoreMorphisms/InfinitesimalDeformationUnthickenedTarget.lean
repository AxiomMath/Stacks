module

public import StacksFrontier.AlgebraicGeometry.Conormal.FirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationSheaf

/-!
# Infinitesimal deformations of maps into an unthickened target

Let `S` be a scheme, let `i : X ⟶ X'` be a first order thickening over `S` and let `j : Y ⟶ Y'`
be an *isomorphism*, the case `Y = Y'` of [Stacks Project, Tag 04FK]. Then the conormal sheaf
`𝒞_{Y/Y'}` vanishes, so the datum `A : a^* 𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of
[Stacks Project, Tag 04FH] carries no information: it is zero, and the third condition of
[Stacks Project, Tag 04FI] holds automatically. The sheaf of [Stacks Project, Tag 04FH] is
therefore the elementary rule assigning to an open `V` of `X'` the set of morphisms `V ⟶ Y'` over
`S` whose restriction to `X ∩ V` is `a`.

## Main definitions

* `Stacks.Thickenings.liftsOverBase`: the morphisms `V ⟶ Y'` over `S` restricting to `a` on
  `i⁻¹V`, with no condition on conormal sheaves.
* `Stacks.Thickenings.liftsOverBaseRestrict` and `Stacks.Thickenings.liftsOverBasePresheaf`: the
  restriction maps of that rule and the presheaf on `X'` they define.

## Main results

* `Stacks.Thickenings.isZero_modulePullback_immersionConormalSheaf_of_isIso`: the pullback of the
  conormal sheaf of an isomorphism vanishes.
* `Stacks.Thickenings.eq_of_isIso` and `Stacks.Thickenings.eq_zero_of_isIso`: there is at most
  one map `A` as in [Stacks Project, Tag 04FH], and it is zero — the first assertion of
  [Stacks Project, Tag 04FK].
* `Stacks.Thickenings.isCompatibleLift_iff_of_isIso`: the third condition of
  [Stacks Project, Tag 04FI] is automatic, so a compatible lift is exactly a lift over `S`
  extending `a`.
* `Stacks.Thickenings.compatibleLiftsPresheafIsoLiftsOverBasePresheaf`: the presheaf of
  [Stacks Project, Tag 04FH] is isomorphic to the elementary rule, by an isomorphism which is the
  identity on underlying morphisms.

The remaining assertion of [Stacks Project, Tag 04FK] — that
`Hom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` acts on the elementary rule, simply transitively over an open
carrying a lift — is `Stacks.Thickenings.exists_simplyTransitive_addAction_liftsOverBase` in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationUnthickenedTargetAction`,
which transports the unrestricted [Stacks Project, Tag 04FJ] along the isomorphism above. The
three assertions of the remark therefore all hold, with no hypothesis beyond the source's.

## Implementation notes

The hypothesis is `CategoryTheory.IsIso j` rather than the literal `Y' = Y` with `j = 𝟙 Y`. This
is a deliberate generalisation of the source: the identity is an isomorphism, so the source's
case is covered, and nothing in the argument uses more than that the conormal sheaf of `j`
vanishes.

Both halves rest on one fact: the source `a^* 𝒞_{Y/Y'}` of `A` is a zero object, because
`Stacks.Conormal.isZero_immersionConormalSheaf_of_isIso` makes `𝒞_{Y/Y'}` zero and the module
pullback is a left adjoint. Two morphisms out of a zero object agree, which both annihilates `A`
and identifies the two sides of the third condition. No affineness and no first-order hypothesis
on `i` enter: the statements hold for arbitrary immersions.

## References

* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 04FH](https://stacks.math.columbia.edu/tag/04FH)
* [Stacks Project, Tag 04FI](https://stacks.math.columbia.edu/tag/04FI)
* [Stacks Project, Tag 04FK](https://stacks.math.columbia.edu/tag/04FK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open AlgebraicGeometry
open Stacks.Immersion

universe u

namespace Stacks.Thickenings

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'}

/-! ### The vanishing of the conormal datum -/

/-- **The pullback of the conormal sheaf of an isomorphism vanishes.** For `j : Y ⟶ Y'` an
isomorphism and `a : X ⟶ Y` any morphism, `a^* 𝒞_{Y/Y'}` is a zero object: the conormal sheaf of
an isomorphism is zero and the module pullback, being a left adjoint, preserves the zero
object. -/
theorem isZero_modulePullback_immersionConormalSheaf_of_isIso [IsImmersion j] [IsIso j]
    (a : X ⟶ Y) :
    IsZero ((modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j)) := by
  have : Functor.IsLeftAdjoint (modulePullback a.toLRSHom.toShHom) :=
    ⟨modulePushforward _, ⟨modulePullbackPushforwardAdjunction _⟩⟩
  exact Functor.map_isZero _ (Stacks.Conormal.isZero_immersionConormalSheaf_of_isIso j)

section

variable [IsImmersion i] [IsImmersion j]

/-- **Any two conormal data for an isomorphic target agree.** The source `a^* 𝒞_{Y/Y'}` of the
map `A` of [Stacks Project, Tag 04FH] is a zero object when `j` is an isomorphism, so there is at
most one such map. -/
theorem eq_of_isIso [IsIso j] (a : X ⟶ Y)
    (A B : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) : A = B :=
  (isZero_modulePullback_immersionConormalSheaf_of_isIso a).eq_of_src A B

/-- **The map `A` of [Stacks Project, Tag 04FH] is zero when `Y = Y'`.** This is the first
assertion of [Stacks Project, Tag 04FK]: in the case `Y = Y'` the conormal datum "is always
zero". -/
@[stacks 04FK "the vanishing of the conormal datum A"]
theorem eq_zero_of_isIso [IsIso j] (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) : A = 0 :=
  eq_of_isIso a A 0

/-! ### The elementary description of the lifting sheaf -/

/-- **The third condition of [Stacks Project, Tag 04FI] is automatic when `Y = Y'`.** A morphism
`b : V ⟶ Y'` out of an open `V` of `X'` is a compatible lift of `a` for the datum `A` exactly
when it is a morphism over `S` restricting to `a` on `i⁻¹V`. -/
theorem isCompatibleLift_iff_of_isIso [IsIso j] (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) (V : X'.Opens) (b : V.toScheme ⟶ Y') :
    IsCompatibleLift pX' pY' a A V b ↔
      b ≫ pY' = V.ι ≫ pX' ∧ i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j := by
  refine ⟨fun hb => ⟨hb.1, hb.2.choose⟩, fun hb => ⟨hb.1, hb.2, ?_⟩⟩
  exact (isZero_modulePullback_immersionConormalSheaf_of_isIso ((i ⁻¹ᵁ V).ι ≫ a)).eq_of_src _ _

end

/-- **The elementary lifting rule of [Stacks Project, Tag 04FK].** For an open `V` of `X'`, the
morphisms `V ⟶ Y'` over `S` whose restriction to `i⁻¹V` is `a`. No condition on conormal sheaves
is imposed. -/
def liftsOverBase (i : X ⟶ X') (j : Y ⟶ Y') (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (V : X'.Opens) : Type u :=
  { b : V.toScheme ⟶ Y' //
    b ≫ pY' = V.ι ≫ pX' ∧ i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j }

/-- The restriction to a smaller open of a lift over `S` extending `a`. -/
def liftsOverBaseRestrict (i : X ⟶ X') (j : Y ⟶ Y') (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y)
    {V V' : X'.Opens} (hV : V' ≤ V) :
    liftsOverBase i j pX' pY' a V ⟶ liftsOverBase i j pX' pY' a V' :=
  TypeCat.ofHom fun c =>
    ⟨X'.homOfLE hV ≫ c.1, by
      rw [Category.assoc, c.2.1, ← Category.assoc, Scheme.homOfLE_ι], by
      rw [← Category.assoc, morphismRestrict_homOfLE, Category.assoc, c.2.2, ← Category.assoc,
        ← Category.assoc, Scheme.homOfLE_ι]⟩

/-- The underlying morphism of a restricted lift is the composite of the inclusion `V' ⟶ V` with
the lift. -/
theorem liftsOverBaseRestrict_coe (i : X ⟶ X') (j : Y ⟶ Y') (pX' : X' ⟶ S) (pY' : Y' ⟶ S)
    (a : X ⟶ Y) {V V' : X'.Opens} (hV : V' ≤ V) (c : liftsOverBase i j pX' pY' a V) :
    (liftsOverBaseRestrict i j pX' pY' a hV c).1 = X'.homOfLE hV ≫ c.1 := rfl

/-- **The presheaf of [Stacks Project, Tag 04FK].** The rule assigning to an open `V` of `X'` the
set of morphisms `V ⟶ Y'` over `S` restricting to `a` on `i⁻¹V`, with restriction along the
inclusions of opens. -/
def liftsOverBasePresheaf (i : X ⟶ X') (j : Y ⟶ Y') (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y) :
    TopCat.Presheaf (Type u) X'.carrier where
  obj V := liftsOverBase i j pX' pY' a V.unop
  map f := liftsOverBaseRestrict i j pX' pY' a f.unop.le
  map_id V := by
    ext c
    exact Subtype.ext
      ((congrArg (fun z => z ≫ c.1) (Scheme.homOfLE_rfl X' V.unop)).trans (Category.id_comp c.1))
  map_comp f g := by
    ext c
    exact Subtype.ext
      ((congrArg (fun z => z ≫ c.1)
        (Scheme.homOfLE_homOfLE X' g.unop.le f.unop.le).symm).trans (Category.assoc _ _ _))

section

variable [IsImmersion i] [IsImmersion j] (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y)

/-- **The sheaf of [Stacks Project, Tag 04FH] is the elementary rule when `Y = Y'`.** The
presheaf of compatible lifts for a datum `A` is isomorphic to the presheaf of lifts over `S`
extending `a`, by the isomorphism which is the identity on underlying morphisms.

This is the description of the sheaf asserted by [Stacks Project, Tag 04FK]. The simply
transitive action of `Hom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` on the elementary rule — the last
assertion of that remark — is
`Stacks.Thickenings.exists_simplyTransitive_addAction_liftsOverBase` in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationUnthickenedTargetAction`,
obtained by transporting the unrestricted [Stacks Project, Tag 04FJ] along this very
isomorphism. -/
@[stacks 04FK "the elementary description of the lifting sheaf"]
def compatibleLiftsPresheafIsoLiftsOverBasePresheaf [IsIso j]
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) :
    compatibleLiftsPresheaf pX' pY' a A ≅ liftsOverBasePresheaf i j pX' pY' a :=
  NatIso.ofComponents
    (fun V =>
      { hom := TypeCat.ofHom fun c =>
          ⟨c.1, (isCompatibleLift_iff_of_isIso pX' pY' a A V.unop c.1).mp c.2⟩
        inv := TypeCat.ofHom fun c =>
          ⟨c.1, (isCompatibleLift_iff_of_isIso pX' pY' a A V.unop c.1).mpr c.2⟩
        hom_inv_id := by ext c; exact Subtype.ext rfl
        inv_hom_id := by ext c; exact Subtype.ext rfl })
    fun f => by ext c; exact Subtype.ext rfl

/-- The isomorphism of [Stacks Project, Tag 04FK] is the identity on underlying morphisms. -/
theorem compatibleLiftsPresheafIsoLiftsOverBasePresheaf_hom_coe [IsIso j]
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) (V : X'.Opens)
    (c : compatibleLifts pX' pY' a A V) :
    (((compatibleLiftsPresheafIsoLiftsOverBasePresheaf pX' pY' a A).hom.app (op V)) c).1
      = c.1 := rfl

end

end Stacks.Thickenings

end
