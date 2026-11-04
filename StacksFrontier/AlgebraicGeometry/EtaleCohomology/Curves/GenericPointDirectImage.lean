module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IrreducibleGenericPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.MultiplicativeSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The direct image along the generic point of an irreducible scheme

A morphism of schemes `i : Y ⟶ X` induces base change `smallEtaleBaseChange i : X.Etale ⥤ Y.Etale`
on small étale sites, running opposite to the morphism of topoi. That functor is continuous, so
precomposition with it carries abelian sheaves on the small étale site of `Y` to abelian sheaves
on the small étale site of `X`: this is the direct image `i_*`, and it has the inverse image
`i^{-1}` as a left adjoint. This file records that pair at the coefficients
`AddCommGrpCat.{max (u + 1) v}` in which this library computes étale cohomology, and specialises
it to the inclusion of the generic point of an irreducible scheme, `j : Spec K ⟶ X` with
`K = X.functionField` the local ring at the generic point.

The second half constructs the comparison morphism `𝐆_{m,X} ⟶ i_* 𝐆_{m,Y}` for an arbitrary
`i : Y ⟶ X`. Along the generic point this is the first map of the divisor sequence
`0 → 𝐆_{m,X} → j_* 𝐆_{m,K} → ⨁_x i_{x,*} ℤ → 0`, and it is constructed directly rather than as
the unit of the adjunction, which would additionally require identifying `i^{-1} 𝐆_{m,X}` with
`𝐆_{m,Y}`: the sections of `i_* 𝐆_{m,Y}` over an étale `X`-scheme `U` are the invertible global
functions on `U ×_X Y`, and the map restricts an invertible function along the projection
`U ×_X Y ⟶ U`.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianDirectImage`: `i_*` on abelian sheaves of small étale
  sites. Its left adjoint `i^{-1}` already existed, as
  `Stacks.EtaleCohomology.etaleAbelianInverseImage`.
* `Stacks.EtaleCohomology.genericPointInclusion`: the morphism `Spec X.functionField ⟶ X`.
* `Stacks.EtaleCohomology.genericPointDirectImage` and
  `Stacks.EtaleCohomology.genericPointInverseImage`: `j_*` and `j^{-1}` for that morphism.
* `Stacks.EtaleCohomology.smallEtaleBaseChangeProjection`: the projection `U ×_X Y ⟶ U`, as a
  natural transformation of functors `X.Etale ⥤ Scheme`.
* `Stacks.EtaleCohomology.multiplicativeDirectImageComparison`: the comparison morphism
  `𝐆_{m,X} ⟶ i_* 𝐆_{m,Y}`.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianInverseImageDirectImageAdj`: `i^{-1} ⊣ i_*`.
* `Stacks.EtaleCohomology.genericPointAdjunction`: `j^{-1} ⊣ j_*` at the generic point.
* `Stacks.EtaleCohomology.etaleAbelianDirectImage_obj_obj`: the sections of `i_* F` over an étale
  `X`-scheme `U` are the sections of `F` over `U ×_X Y`.
* `Stacks.EtaleCohomology.exists_mem_pullback_genericPointInclusion`: the generic fibre of an
  étale neighbourhood with a point carries a point over the generic point of `X`.
* `Stacks.EtaleCohomology.multiplicativeDirectImageComparison_app_ofUnit`: on sections the
  comparison morphism restricts an invertible global function along `U ×_X Y ⟶ U`.

## Implementation notes

`i_*` is `CategoryTheory.Functor.sheafPushforwardContinuous` for the continuous site functor
`Stacks.EtaleCohomology.smallEtaleBaseChange i`, whose continuity is
`Stacks.EtaleCohomology.smallEtaleBaseChange_isContinuous`; no limits in the coefficient category
are needed, because the functor is literally precomposition. `i^{-1}` is the left Kan extension
followed by sheafification, so it needs sheafification at these coefficients, which is
`AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology`. For an *étale* `i` there is a second,
inequivalent pair — restriction and its right adjoint — recorded as
`Stacks.EtaleCohomology.etaleRestriction` and `Stacks.EtaleCohomology.etaleDirectImage`; the two
agree only because restriction along an étale morphism is both the inverse image and a
pushforward for the cocontinuous structure.

The comparison morphism is built by whiskering: both `𝐆_{m,X}` and `i_* 𝐆_{m,Y}` are
`Stacks.EtaleCohomology.globalUnitsAdditive` precomposed with a functor to `Scheme`, so a natural
transformation between those two functors to `Scheme` induces the morphism of sheaves, and
`Stacks.EtaleCohomology.smallEtaleBaseChangeProjection` is that transformation. This is why the
sections formula is a definitional identity.

## References

* [Stacks Project, Tag 03XB](https://stacks.math.columbia.edu/tag/03XB): functoriality of the
  small étale topos.
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM): the divisor sequence,
  whose first map is the comparison morphism along the generic point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

section DirectImage

variable {X Y : Scheme.{u}} (i : Y ⟶ X)

/-- **The direct image `i_*` along `i : Y ⟶ X` on abelian sheaves of the small étale sites**:
precomposition with base change `Stacks.EtaleCohomology.smallEtaleBaseChange i`, which is a
continuous functor of sites. On sections it is `(i_* F)(U) = F(U ×_X Y)`.

This is the right adjoint of `Stacks.EtaleCohomology.etaleAbelianInverseImage`. -/
abbrev etaleAbelianDirectImage :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  (smallEtaleBaseChange i).sheafPushforwardContinuous
    AddCommGrpCat.{max (u + 1) v} X.smallEtaleTopology Y.smallEtaleTopology

/-- **The inverse image is left adjoint to the direct image** for the small étale sites of an
arbitrary morphism of schemes. -/
def etaleAbelianInverseImageDirectImageAdj
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] :
    etaleAbelianInverseImage.{u, v} i ⊣ etaleAbelianDirectImage.{u, v} i :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

/-- The sections of `i_* F` over an étale `X`-scheme `U` are the sections of `F` over the base
change `U ×_X Y`. -/
theorem etaleAbelianDirectImage_obj_obj
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (U : X.Etale) :
    ((etaleAbelianDirectImage.{u, v} i).obj F).obj.obj (op U) =
      F.obj.obj (op ((smallEtaleBaseChange i).obj U)) :=
  rfl

end DirectImage

section GenericPoint

variable (X : Scheme.{u}) [IrreducibleSpace X]

/-- **The inclusion of the generic point of an irreducible scheme**, `Spec K ⟶ X` with
`K = X.functionField` the local ring at the generic point. It is
`AlgebraicGeometry.Scheme.fromSpecStalk` at the generic point. -/
def genericPointInclusion : Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

/-- **The direct image `j_*` along the generic point** of an irreducible scheme, on abelian
sheaves of the small étale sites. Its sections over an étale `X`-scheme `U` are the sections over
the generic fibre `U ×_X Spec K`. -/
abbrev genericPointDirectImage :
    Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  etaleAbelianDirectImage.{u, v} (genericPointInclusion X)

/-- The inverse image `j^{-1}` along the generic point of an irreducible scheme. -/
abbrev genericPointInverseImage :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  etaleAbelianInverseImage.{u, v} (genericPointInclusion X)

/-- **`j^{-1} ⊣ j_*` at the generic point** of an irreducible scheme. -/
def genericPointAdjunction :
    genericPointInverseImage.{u, v} X ⊣ genericPointDirectImage.{u, v} X :=
  etaleAbelianInverseImageDirectImageAdj.{u, v} (genericPointInclusion X)

/-- The generic point of `X` is in the image of the inclusion of the generic point: it is the
image of the closed point of `Spec K`. -/
theorem genericPointInclusion_closedPoint :
    (genericPointInclusion X).base (IsLocalRing.closedPoint X.functionField) =
      genericPoint X :=
  X.fromSpecStalk_closedPoint

/-- **The generic fibre of an étale neighbourhood with a point carries a point lying over the
generic point of `X`.** The structure morphism of an object `U` of the small étale site is
étale, hence universally open, so its image contains the generic point of `X`; it is also the
image of the closed point of `Spec K`; and a fibre product carries a point over any pair with a
common image.

The conclusion names where the point goes, which is the content: its image in `U` is a point of
the fibre of `U` over the generic point, and its image in `Spec K` is the closed point. This is
the geometric input to the divisor sequence of Stacks 03RM — the sections of `j_* 𝐆_{m,K}` over
an étale neighbourhood with a point are functions on a scheme that is not empty, and the
valuations that the sequence's second map takes are read off at these points. -/
theorem exists_mem_pullback_genericPointInclusion (U : X.Etale) (u : U.left) :
    ∃ z : ↥(pullback U.hom (genericPointInclusion X)),
      U.hom.base ((pullback.fst U.hom (genericPointInclusion X)).base z) = genericPoint X ∧
        (pullback.snd U.hom (genericPointInclusion X)).base z =
          IsLocalRing.closedPoint X.functionField := by
  have hne : Nonempty ↥U.left := ⟨u⟩
  obtain ⟨p, hp⟩ :=
    genericPoint_mem_range_of_universallyOpen (X := X) (Y := U.left) U.hom
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := U.hom)
    (g := genericPointInclusion X) p (IsLocalRing.closedPoint X.functionField)
    (hp.trans (genericPointInclusion_closedPoint X).symm)
  exact ⟨z, by rw [hz₁]; exact hp, hz₂⟩

end GenericPoint

section Comparison

/-- The functor sending a scheme to the additive group of its invertible global functions, raised
to the coefficient universe of étale cohomology. It is the factor of
`Stacks.Kummer.multiplicativePresheaf` that does not depend on the base scheme. -/
@[sga "3 I 4.3.2"]
def globalUnitsAdditive : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v} :=
  Scheme.Γ ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
    commGroupAddCommGroupEquivalence.functor ⋙ AddCommGrpCat.uliftFunctor.{max (u + 1) v, u}

/-- `𝐆_m` on the small étale site of `X` is
`Stacks.EtaleCohomology.globalUnitsAdditive` precomposed with the functor taking an étale
`X`-scheme to its underlying scheme. -/
theorem multiplicativePresheaf_eq (X : Scheme.{u}) :
    Stacks.Kummer.multiplicativePresheaf.{u, v} X =
      (Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X).op ⋙ globalUnitsAdditive.{u, v} :=
  rfl

variable {X Y : Scheme.{u}} (i : Y ⟶ X)

/-- **The projection `U ×_X Y ⟶ U`**, natural in the étale `X`-scheme `U`: a natural
transformation from base change along `i : Y ⟶ X` followed by the underlying scheme, to the
underlying scheme. -/
def smallEtaleBaseChangeProjection :
    smallEtaleBaseChange i ⋙ Scheme.Etale.forget Y ⋙ CategoryTheory.Over.forget Y ⟶
      Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X where
  app U := pullback.fst U.hom i
  naturality U V g := by
    change ((smallEtaleBaseChange i).map g).left ≫ pullback.fst V.hom i =
      pullback.fst U.hom i ≫ g.left
    exact pullback.lift_fst _ _ _

/-- **The comparison morphism `𝐆_{m,X} ⟶ i_* 𝐆_{m,Y}`**: an invertible global function on an
étale `X`-scheme `U` restricts to an invertible global function on `U ×_X Y`, which is a section
of `i_* 𝐆_{m,Y}` over `U`. Along the inclusion of the generic point of an irreducible scheme this
is the first map of the divisor sequence of Stacks 03RM. -/
def multiplicativeDirectImageComparison :
    Stacks.Kummer.multiplicativeSheaf.{u, v} X ⟶
      (etaleAbelianDirectImage.{u, v} i).obj (Stacks.Kummer.multiplicativeSheaf.{u, v} Y) :=
  ⟨Functor.whiskerRight (NatTrans.op (smallEtaleBaseChangeProjection i))
    globalUnitsAdditive.{u, v}⟩

/-- **On sections the comparison morphism is restriction along `U ×_X Y ⟶ U`.** -/
@[simp]
theorem multiplicativeDirectImageComparison_app_ofUnit (U : X.Etale) (x : (Γ(U.left, ⊤))ˣ) :
    (multiplicativeDirectImageComparison.{u, v} i).hom.app (op U) (Stacks.Kummer.ofUnit x) =
      Stacks.Kummer.ofUnit (U := (smallEtaleBaseChange i).obj U)
        (Units.map (pullback.fst U.hom i).appTop.hom.toMonoidHom x) :=
  rfl

end Comparison

end Stacks.EtaleCohomology

end
