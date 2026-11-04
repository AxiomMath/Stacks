module

public import StacksFrontier.AlgebraicGeometry.ProEtale.AppProetaleCover
public import StacksFrontier.AlgebraicGeometry.ProEtale.AppProetaleSite
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AppSiteClosedImmersionTopos
public import StacksFrontier.CategoryTheory.Sites.PushforwardFullyFaithful

/-!
# The pro-étale direct image along a closed immersion of affines is fully faithful

Let `i : Z ⟶ X` be a closed immersion of affine schemes.  Restriction of sheaves along
`AlgebraicGeometry.Scheme.proetaleBaseChange i` is the direct image `i_*` of the morphism of
topoi of the *unrestricted* small pro-étale sites `AlgebraicGeometry.Scheme.ProEt`, and this
file proves that it is fully faithful, for an arbitrary coefficient category and in particular
for `AddCommGrpCat`.  That is Stacks 09BL (6) for `i_*`, on the site where the Stacks Project
states it rather than on the site of affine ind-étale objects.

Both ingredients were already unconditional; what was missing was the join between them.  The
fully faithful left adjoint `v` of Stacks 09BK lives on the site `S_app` in the spelling
`AlgebraicGeometry.ProEtale.AppSmallProetale`, while Stacks 098X — the identification of
sheaves on `S_app` with sheaves on the whole small pro-étale site — had been proved for the
spelling `AlgebraicGeometry.ProEtale.AppProetale`.  The two full subcategories of
`S.ProEt` are cut out by object properties which are *equivalent but not syntactically equal*:
one says `StacksDraft.IndEtale Γ(S, ⊤) Γ(V.left, ⊤)`, the other says that `V.hom.appTop` lies
in `CategoryTheory.ObjectProperty.ind` of the étale maps under `Γ(S, ⊤)`.  No functor identified
them.  `AlgebraicGeometry.ProEtale.isAppSmall_iff_isAffineIndEtaleAlgebra` is that
identification, and it is all that is needed: the two inclusions have, objectwise, the same
image, hence literally the same cover-by-image sieves, so cover density transfers.

## Main results

* `AlgebraicGeometry.ProEtale.isAppSmall_iff_isAffineIndEtaleAlgebra` — the two object
  properties cutting out `S_app` agree.
* `AlgebraicGeometry.ProEtale.AppSmallProetale.inclusion_isCoverDense` — the inclusion of
  `S_app` into the small pro-étale site of an affine scheme is cover dense, with nothing
  assumed.
* `AlgebraicGeometry.ProEtale.isContinuous_appProetaleBaseChange_inducedTopology` — the base
  change functor `u` of Stacks 09BK is continuous for the topologies induced by those
  inclusions.
* `AlgebraicGeometry.ProEtale.fullyFaithful_sheafPushforwardContinuous_proetaleBaseChange` —
  restriction of sheaves along pro-étale base change is fully faithful.
* `AlgebraicGeometry.ProEtale.Abelian.fullyFaithful_proetaleDirectImage` — the same for
  abelian coefficients: the direct image of abelian pro-étale sheaves along a closed immersion
  of affine schemes is fully faithful.

## Implementation notes

The topologies on `S_app` are the ones *induced* by the inclusion, as in
`AlgebraicGeometry.ProEtale.AppProetale.inclusion_isDenseSubsite`; the topology of the standard
pro-étale covering families is identified with them only by the refinement half of Stacks 098X,
which is not available.  Nothing is lost: the dense-subsite property, and hence the equivalence
of topoi, holds for the induced topology by `CategoryTheory.Functor.IsDenseSubsite` of a cover
dense fully faithful functor.

Continuity of `u` is proved exactly as `AlgebraicGeometry.ProEtale.appBaseChange_isContinuous`
proves it for the other spelling, and cannot be inherited from
`AlgebraicGeometry.ProEtale.isContinuous_appProetaleBaseChange`, which is continuity for the
standard topology on `S_app`.

Full faithfulness itself needs no topology on the source: it is
`CategoryTheory.Functor.fullyFaithfulSheafPushforwardContinuousOfAdjoint`, which asks only for
continuity of `u` and a fully faithful left adjoint, and in particular does *not* ask `v` to be
continuous — the obstruction that keeps Stacks 09BL (3) conditional on this site.  The transport
from `u` to pro-étale base change is the one used by
`AlgebraicGeometry.ProEtale.isRightAdjoint_proetaleInverseImage_of_appAdjunction`: restriction
along either inclusion is an equivalence, and `u` followed by the inclusion of `Z_app` is the
inclusion of `X_app` followed by base change, so restriction along base change is restriction
along `u` conjugated by the two equivalences.

## References

* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
* [Stacks Project, Tag 098X](https://stacks.math.columbia.edu/tag/098X)
* [Stacks Project, Tag 097Z](https://stacks.math.columbia.edu/tag/097Z)
-/

@[expose] public section

open CategoryTheory

universe w w' u v

namespace AlgebraicGeometry.ProEtale

/-! ### The two spellings of the affine ind-étale site -/

/-- **The two object properties cutting out the site `S_app` agree.** An object of the small
pro-étale site of `S` is affine with ind-étale ring of global sections, in the universe-pinned
algebra spelling `AlgebraicGeometry.ProEtale.IsAppSmall`, exactly when it is affine with
ind-étale coordinate ring in the `CategoryTheory.ObjectProperty.ind` spelling
`AlgebraicGeometry.ProEtale.IsAffineIndEtaleAlgebra`.

The ind-étale halves are the two sides of
`AlgebraicGeometry.ProEtale.indEtale_iff_ind_etale_underMk` at the algebra structure that
`IsAppSmall` supplies, namely the one read off the structure morphism on global sections; the
affineness halves are the same proposition. -/
public theorem isAppSmall_iff_isAffineIndEtaleAlgebra (S : Scheme.{u}) (V : S.ProEt) :
    IsAppSmall S V ↔ IsAffineIndEtaleAlgebra S V := by
  let : Algebra ↥Γ(S, ⊤) ↥Γ(V.left, ⊤) := V.hom.appTop.hom.toAlgebra
  exact and_congr_right fun _ ↦ indEtale_iff_ind_etale_underMk

/-- **Cover density of `S_app` in the small pro-étale site of an affine scheme, with nothing
assumed**, in the spelling `AlgebraicGeometry.ProEtale.AppSmallProetale`.

This is `AlgebraicGeometry.ProEtale.AppProetale.inclusion_isCoverDense` — which is Stacks 098X
from the unconditional `AlgebraicGeometry.ProEtale.hasAppCover`, hence from Proposition 097Z —
moved across `isAppSmall_iff_isAffineIndEtaleAlgebra`.  The move is immediate because the two
inclusions have the same objects in their image: a morphism factors through an object of one
subcategory exactly when it factors through an object of the other, so the two cover-by-image
sieves are equal sieves and not merely equivalent ones.

Registered as an instance, so that the dense-subsite property for the induced topology — and
through `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv` the equivalence of topoi — is found
by instance search for this spelling too. -/
public instance AppSmallProetale.inclusion_isCoverDense (S : Scheme.{u}) [IsAffine S] :
    (AppSmallProetale.inclusion S).IsCoverDense (Scheme.ProEt.topology S) := by
  refine ⟨fun V ↦ ?_⟩
  have h : Sieve.coverByImage (AppSmallProetale.inclusion S) V =
      Sieve.coverByImage (AppProetale.inclusion S) V := by
    refine Sieve.ext fun Y g ↦ ⟨?_, ?_⟩
    · rintro ⟨W, lift, map, fac⟩
      exact ⟨⟨W.obj, (isAppSmall_iff_isAffineIndEtaleAlgebra S W.obj).mp W.property⟩,
        lift, map, fac⟩
    · rintro ⟨W, lift, map, fac⟩
      exact ⟨⟨W.obj, (isAppSmall_iff_isAffineIndEtaleAlgebra S W.obj).mpr W.property⟩,
        lift, map, fac⟩
  rw [h]
  exact (AppProetale.inclusion S).is_cover_of_isCoverDense _ V

/-! ### Base change on `S_app` and on the small pro-étale site -/

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsAffine X] [IsAffine Z]

/-- Base change on the sites `S_app` is the restriction of pro-étale base change on the
unrestricted small pro-étale sites; the identification is definitional. -/
public theorem appProetaleBaseChange_comp_inclusion :
    appProetaleBaseChange i ⋙ AppSmallProetale.inclusion Z =
      AppSmallProetale.inclusion X ⋙ Scheme.proetaleBaseChange i :=
  rfl

/-- **Continuity of the base change functor `u` of Stacks 09BK for the induced topologies.**

`AlgebraicGeometry.ProEtale.isContinuous_appProetaleBaseChange` is continuity for the topology
on `S_app` generated by the standard pro-étale covering families; the equivalence of topoi of
Stacks 098X is available for the topology *induced* by the inclusion, and this is continuity
for that one.  The proof is formal, and is the one of
`AlgebraicGeometry.ProEtale.appBaseChange_isContinuous`: a sheaf on `Z_app` is the restriction
of a sheaf on the small pro-étale site of `Z`, because restriction along a dense subsite is an
equivalence; restricting that sheaf along `X_app ⥤ X_proétale ⥤ Z_proétale` — which is `u`
followed by the inclusion of `Z_app` — again gives a sheaf, both factors being continuous. -/
public instance isContinuous_appProetaleBaseChange_inducedTopology :
    (appProetaleBaseChange i).IsContinuous
      ((AppSmallProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X))
      ((AppSmallProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z)) := by
  refine ⟨fun G ↦ ?_⟩
  let JX := (AppSmallProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X)
  let RZ := (AppSmallProetale.inclusion Z).sheafPushforwardContinuous
    (Type (max (u + 1) u u (u + 1)))
    ((AppSmallProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z))
    (Scheme.ProEt.topology Z)
  have hRZ : RZ.IsEquivalence := inferInstance
  let G' := RZ.objPreimage G
  have e : G.obj ≅ (AppSmallProetale.inclusion Z).op ⋙ G'.obj :=
    (sheafToPresheaf _ _).mapIso (RZ.objObjPreimageIso G).symm
  have hc : (AppSmallProetale.inclusion X ⋙ Scheme.proetaleBaseChange i).IsContinuous
      JX (Scheme.ProEt.topology Z) :=
    Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology X) _
  have hsh : Presieve.IsSheaf JX
      ((AppSmallProetale.inclusion X ⋙ Scheme.proetaleBaseChange i).op ⋙ G'.obj) :=
    Functor.op_comp_isSheaf_of_types _ JX (Scheme.ProEt.topology Z) G'
  exact Presieve.isSheaf_iso JX (Functor.associator (appProetaleBaseChange i).op
    (AppSmallProetale.inclusion Z).op G'.obj ≪≫
      Functor.isoWhiskerLeft (appProetaleBaseChange i).op e.symm) hsh

/-! ### Full faithfulness of the direct image -/

variable [IsClosedImmersion i]

/-- **Stacks 09BL (6) for the direct image `i_*`, on the unrestricted small pro-étale site.**
For a closed immersion `i : Z ⟶ X` of affine schemes, restriction of sheaves along pro-étale
base change — the direct image of the morphism of topoi of the small pro-étale sites — is fully
faithful, for any coefficient category in which the dense subsite of Stacks 098X gives an
equivalence of topoi.

On the sites `S_app` this is
`CategoryTheory.Functor.fullyFaithfulSheafPushforwardContinuousOfAdjoint` applied to the base
change functor `u` of Stacks 09BK and its fully faithful left adjoint `v`; continuity of `v`
is not needed, and is not available.  Restriction along either inclusion of `S_app` is an
equivalence by Stacks 098X, and `appProetaleBaseChange_comp_inclusion` says that `u` followed
by the inclusion of `Z_app` is the inclusion of `X_app` followed by pro-étale base change; so
restriction along pro-étale base change is restriction along `u` conjugated by those two
equivalences, and full faithfulness passes along the conjugation. -/
public noncomputable def fullyFaithful_sheafPushforwardContinuous_proetaleBaseChange
    (A : Type w) [Category.{w'} A]
    [∀ W, Limits.HasLimitsOfShape
      (StructuredArrow W (AppSmallProetale.inclusion X).op) A]
    [∀ W, Limits.HasLimitsOfShape
      (StructuredArrow W (AppSmallProetale.inclusion Z).op) A] :
    ((Scheme.proetaleBaseChange i).sheafPushforwardContinuous A
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)).FullyFaithful := by
  let JX := (AppSmallProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X)
  let JZ := (AppSmallProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z)
  let RX := (AppSmallProetale.inclusion X).sheafPushforwardContinuous A JX
    (Scheme.ProEt.topology X)
  let RZ := (AppSmallProetale.inclusion Z).sheafPushforwardContinuous A JZ
    (Scheme.ProEt.topology Z)
  have hRX : RX.IsEquivalence := inferInstance
  have hRZ : RZ.IsEquivalence := inferInstance
  let eX := RX.asEquivalence
  let Su := (appProetaleBaseChange i).sheafPushforwardContinuous A JX JZ
  let SG := (Scheme.proetaleBaseChange i).sheafPushforwardContinuous A
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)
  have hc : (AppSmallProetale.inclusion X ⋙ Scheme.proetaleBaseChange i).IsContinuous
      JX (Scheme.ProEt.topology Z) :=
    Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology X) _
  let PFG := Functor.sheafPushforwardContinuous
    (AppSmallProetale.inclusion X ⋙ Scheme.proetaleBaseChange i) A JX
    (Scheme.ProEt.topology Z)
  have c1 : SG ⋙ RX ≅ PFG :=
    Functor.sheafPushforwardContinuousComp' (eFG := Iso.refl _) (A := A) (J := JX)
      (K := Scheme.ProEt.topology X) (L := Scheme.ProEt.topology Z)
  have c2 : RZ ⋙ Su ≅ PFG :=
    Functor.sheafPushforwardContinuousComp'
      (eFG := eqToIso (appProetaleBaseChange_comp_inclusion i))
      (A := A) (J := JX) (K := JZ) (L := Scheme.ProEt.topology Z)
  have iso : RZ.asEquivalence.functor ⋙ (Su ⋙ eX.inverse) ≅ SG :=
    (Functor.associator RZ.asEquivalence.functor Su eX.inverse).symm ≪≫
      Functor.isoWhiskerRight (c2 ≪≫ c1.symm) eX.inverse ≪≫
      Functor.associator SG RX eX.inverse ≪≫
      Functor.isoWhiskerLeft SG eX.unitIso.symm ≪≫ SG.rightUnitor
  have hffSu := Functor.fullyFaithfulSheafPushforwardContinuousOfAdjoint A
    (appProetaleBaseChange i) (appProetaleLiftAdjunction i) JX JZ
  exact (RZ.asEquivalence.fullyFaithfulFunctor.comp
    (hffSu.comp eX.fullyFaithfulInverse)).ofIso iso

/-- **Stacks 09BL (6) for the direct image of abelian pro-étale sheaves.** For a closed
immersion `i : Z ⟶ X` of affine schemes, the direct image `i_*` of abelian sheaves on the
unrestricted small pro-étale sites — restriction along pro-étale base change — is fully
faithful.

This is `fullyFaithful_sheafPushforwardContinuous_proetaleBaseChange` at `AddCommGrpCat`, whose
limits of the required shapes exist. -/
public noncomputable def Abelian.fullyFaithful_proetaleDirectImage :
    ((Scheme.proetaleBaseChange i).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)).FullyFaithful :=
  fullyFaithful_sheafPushforwardContinuous_proetaleBaseChange i AddCommGrpCat.{max (u + 1) v}

end AlgebraicGeometry.ProEtale

end
