module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.BeckChevalley
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.ClosedFibreLift
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.ClosedFibreWContractible
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.WeaklyContractibleAbelian
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineIndEtaleWeaklyContractible
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ClopenRefinement
public import StacksCore.Tactic.StacksAttribute

/-!
# Inverse image on the closed fibre of a weakly contractible affine object

Let `i : Z ⟶ X` be a closed immersion of objects of a chosen big pro-étale site — `X` is *not*
assumed affine — and let `U` be an object of the small pro-étale site of `X` which is affine and
weakly contractible and every point of which specializes to a point of `U ×_X Z`. Then
`i^{-1}F(U ×_X Z) = F(U)` for every abelian sheaf `F` on the small pro-étale site of `X`.

The proof is the source's. Inverse image commutes with restriction to a localization, so one
may replace `X` by `U`: that is `AlgebraicGeometry.ProEtale.smallProetaleInverseImageRestrictionIso`
below, for the cartesian square with horizontal arrows `U ⟶ X` and `U ×_X Z ⟶ Z`. After that
replacement the base is affine and weakly contractible, the closed subobject is `U ×_X Z`, and
the object at which the inverse image is evaluated is the final object; so Stacks 09BL (2)
applies and reduces the claim to the identification `v(U ×_X Z) = U` of the final objects under
the lift of affine ind-étale objects, which is
`AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.affineIndEtaleLift_obj_terminalObj_iso`.

## Main definitions

* `AlgebraicGeometry.ProEtale.smallProetaleInverseImageRestrictionIso`: for a cartesian square
  with weakly étale horizontal arrows, inverse image along the vertical arrows commutes with
  restriction along the horizontal ones.

## Main results

* `AlgebraicGeometry.ProEtale.abelianProetaleInverseImage_sections_iso_closedFibre`:
  **Stacks 09AC.**

## Implementation notes

Weak contractibility of `U` is weak contractibility of the underlying object of the chosen big
pro-étale site; by Stacks 098H — `AlgebraicGeometry.ProEtale.isWContractible_globalSections_tfae`
— that is equivalent, for an affine object, to w-contractibility of its ring of global sections,
which is the form in which the hypothesis is consumed, and it implies weak contractibility of `U`
as an object of the small pro-étale site of `X`
(`AlgebraicGeometry.ProEtale.SmallProetale.isWeaklyContractible_of_isWContractible`).

The specialization hypothesis is on the points of the underlying scheme of `U`, and the point of
`U ×_X Z` it produces is taken through the first projection, which is the closed immersion cut
out by the ideal of `Z`.

Abelian sheaves are taken in `AddCommGrpCat.{u + 1}`, the universe of the objects of the sites,
as everywhere else in the library for abelian sheaves on these sites. The isomorphism is one of
functors in the sheaf, so it includes its naturality.

## References

* [Stacks Project, Tag 09AC](https://stacks.math.columbia.edu/tag/09AC)
* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 098H](https://stacks.math.columbia.edu/tag/098H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ProEtale

/-! ### Inverse image commutes with restriction to a localization -/

section Square

universe w w'

variable (B : BigProetaleSite.{u}) {T' T S' S : B.Scheme} (g' : T' ⟶ T) (f' : T' ⟶ S')
  (f : T ⟶ S) (g : S' ⟶ S) (hg : WeaklyEtale (B.inclusion.map g))
  (hg' : WeaklyEtale (B.inclusion.map g')) (h : IsPullback g' f' f g)

/-- **Inverse image commutes with restriction to a localization.** For a cartesian square of a
chosen big pro-étale site whose horizontal arrows `g` and `g'` are weakly étale, restricting to
`T'` the inverse image along `f` of a sheaf on `S` is the inverse image along `f'` of its
restriction to `S'`, naturally in the sheaf.

Both composites are left adjoints, and their right adjoints are the two composite direct images,
which are identified by the Beck–Chevalley isomorphism
`AlgebraicGeometry.ProEtale.smallProetaleSiteBaseChangeMate` of the iterated base-change functors
of the sites. -/
def smallProetaleInverseImageRestrictionIso (A : Type w) [Category.{w'} A]
    [HasWeakSheafify (SmallProetale.topology B T.obj T.property) A]
    [HasWeakSheafify (SmallProetale.topology B T'.obj T'.property) A]
    [∀ F : (SmallProetale B S.obj S.property)ᵒᵖ ⥤ A,
      (smallProetaleBaseChange B T S f).op.HasLeftKanExtension F]
    [∀ F : (SmallProetale B S'.obj S'.property)ᵒᵖ ⥤ A,
      (smallProetaleBaseChange B T' S' f').op.HasLeftKanExtension F] :
    Functor.sheafPullbackConstruction.sheafPullback (smallProetaleBaseChange B T S f) A
        (SmallProetale.topology B S.obj S.property)
        (SmallProetale.topology B T.obj T.property) ⋙
      (smallProetaleCompose B g' hg').sheafPushforwardContinuous A
        (SmallProetale.topology B T'.obj T'.property)
        (SmallProetale.topology B T.obj T.property) ≅
    (smallProetaleCompose B g hg).sheafPushforwardContinuous A
        (SmallProetale.topology B S'.obj S'.property)
        (SmallProetale.topology B S.obj S.property) ⋙
      Functor.sheafPullbackConstruction.sheafPullback (smallProetaleBaseChange B T' S' f') A
        (SmallProetale.topology B S'.obj S'.property)
        (SmallProetale.topology B T'.obj T'.property) := by
  let JS := SmallProetale.topology B S.obj S.property
  let JS' := SmallProetale.topology B S'.obj S'.property
  let JT := SmallProetale.topology B T.obj T.property
  let JT' := SmallProetale.topology B T'.obj T'.property
  let uf := smallProetaleBaseChange B T S f
  let ug := smallProetaleBaseChange B S' S g
  let uf' := smallProetaleBaseChange B T' S' f'
  let ug' := smallProetaleBaseChange B T' T g'
  haveI : uf.IsContinuous JS JT :=
    (smallProetaleBaseChange_isMorphismOfSites B T S f).toIsContinuous
  haveI : ug.IsContinuous JS JS' :=
    (smallProetaleBaseChange_isMorphismOfSites B S' S g).toIsContinuous
  haveI : uf'.IsContinuous JS' JT' :=
    (smallProetaleBaseChange_isMorphismOfSites B T' S' f').toIsContinuous
  haveI : ug'.IsContinuous JT JT' :=
    (smallProetaleBaseChange_isMorphismOfSites B T' T g').toIsContinuous
  haveI : (ug ⋙ uf').IsContinuous JS JT' := Functor.isContinuous_comp ug uf' JS JS' JT'
  haveI : (uf ⋙ ug').IsContinuous JS JT' := Functor.isContinuous_comp uf ug' JS JT JT'
  let adjf := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf A JS JT
  let adjf' := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf' A JS' JT'
  let adjg := (smallProetaleCompose_adj B g hg).sheafPushforwardContinuous (E := A) JS' JS
  let adjg' := (smallProetaleCompose_adj B g' hg').sheafPushforwardContinuous (E := A) JT' JT
  have hR : uf'.sheafPushforwardContinuous A JS' JT' ⋙ ug.sheafPushforwardContinuous A JS JS' ≅
      ug'.sheafPushforwardContinuous A JT JT' ⋙ uf.sheafPushforwardContinuous A JS JT :=
    Functor.sheafPushforwardContinuousComp ug uf' A JS JS' JT' ≪≫
      Functor.sheafPushforwardContinuousIso
        (asIso (smallProetaleSiteBaseChangeMate B g' f' f g hg hg' h)) A JS JT' ≪≫
      (Functor.sheafPushforwardContinuousComp uf ug' A JS JT JT').symm
  exact Adjunction.leftAdjointUniq (adjf.comp adjg') ((adjg.comp adjf').ofNatIsoRight hR)

end Square

/-! ### Stacks 09AC -/

section

variable (B : BigProetaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
  [IsClosedImmersion (B.inclusion.map i)] (U : SmallProetale B X.obj X.property)

/-- The closed fibre `U ×_X Z` of an object `U` of the small pro-étale site of `X` is a closed
subobject of `U`: the first projection is the base change of `i`. -/
instance isClosedImmersion_closedFibreFst :
    IsClosedImmersion (B.inclusion.map (pullback.fst U.obj.hom i)) :=
  MorphismProperty.of_isPullback
    (((IsPullback.of_hasPullback U.obj.hom i).map B.inclusion).flip) ‹_›

/-- The closed fibre of an affine object of the small pro-étale site of `X` is affine. -/
instance isAffine_closedFibre [IsAffine U.obj.left.obj] :
    IsAffine (pullback U.obj.hom i).obj :=
  letI : IsAffine (B.inclusion.obj U.obj.left) := ‹IsAffine U.obj.left.obj›
  (IsClosedImmersion.isAffine_surjective_of_isAffine
    (B.inclusion.map (pullback.fst U.obj.hom i))).1

/-- Composition with the structure morphism of `U` carries the final object of the small
pro-étale site of `U` to `U`. -/
def smallProetaleCompose_obj_smallIdentity :
    (smallProetaleCompose B U.obj.hom U.property).obj
        (smallIdentity B U.obj.left.obj U.obj.left.property) ≅ U :=
  ObjectProperty.isoMk _ (Over.isoMk (Iso.refl _) rfl)

/-- Composition with the structure morphism of the closed fibre of `U` carries the final object
of the small pro-étale site of that fibre to the closed fibre of `U`. -/
def smallProetaleCompose_obj_smallIdentity_closedFibre :
    (smallProetaleCompose B (pullback.snd U.obj.hom i)
          ((smallProetaleBaseChange B Z X i).obj U).property).obj
        (smallIdentity B (pullback U.obj.hom i).obj (pullback U.obj.hom i).property) ≅
      (smallProetaleBaseChange B Z X i).obj U :=
  ObjectProperty.isoMk _ (Over.isoMk (Iso.refl _) rfl)

/-- **Stacks 09AC.** Let `i : Z ⟶ X` be a closed immersion of objects of a chosen big pro-étale
site and let `U` be an object of the small pro-étale site of `X` such that

1. `U` is affine and weakly contractible, and
2. every point of `U` specializes to a point of `U ×_X Z`.

Then `i^{-1}F(U ×_X Z) = F(U)` for every abelian sheaf `F` on the small pro-étale site of `X`,
naturally in `F`.

Weak contractibility of `U` is taken in the chosen big pro-étale site; for an affine object it
is equivalent to w-contractibility of its ring of global sections by Stacks 098H, and it implies
weak contractibility of `U` as an object of the small pro-étale site of `X`. -/
@[stacks 09AC "i^{-1}F(U x_X Z) = F(U) for every abelian sheaf F on X_proetale, naturally in \
F, for an ARBITRARY closed immersion i : Z -> X and U affine and weakly contractible (in the \
chosen big pro-etale site, Tag 098H) all of whose points specialize into U x_X Z"]
def abelianProetaleInverseImage_sections_iso_closedFibre [IsAffine U.obj.left.obj]
    (hU : B.topology.IsWeaklyContractible U.obj.left)
    (hspec : ∀ x : U.obj.left.obj, ∃ w : (pullback U.obj.hom i).obj,
      x ⤳ (B.inclusion.map (pullback.fst U.obj.hom i)).base w) :
    Functor.sheafPullbackConstruction.sheafPullback (smallProetaleBaseChange B Z X i)
        AddCommGrpCat.{u + 1} (SmallProetale.topology B X.obj X.property)
        (SmallProetale.topology B Z.obj Z.property) ⋙
      sheafToPresheaf (SmallProetale.topology B Z.obj Z.property) AddCommGrpCat.{u + 1} ⋙
      (evaluation _ _).obj (op ((smallProetaleBaseChange B Z X i).obj U)) ≅
    sheafToPresheaf (SmallProetale.topology B X.obj X.property) AddCommGrpCat.{u + 1} ⋙
      (evaluation _ _).obj (op U) := by
  classical
  let A := AddCommGrpCat.{u + 1}
  let S' : B.Scheme := U.obj.left
  let g : S' ⟶ X := U.obj.hom
  let T' : B.Scheme := pullback g i
  let f' : T' ⟶ S' := pullback.fst g i
  let g' : T' ⟶ Z := pullback.snd g i
  let W : SmallProetale B Z.obj Z.property := (smallProetaleBaseChange B Z X i).obj U
  let JX := SmallProetale.topology B X.obj X.property
  let JZ := SmallProetale.topology B Z.obj Z.property
  let JS' := SmallProetale.topology B S'.obj S'.property
  let JT' := SmallProetale.topology B T'.obj T'.property
  let topS' := smallIdentity B S'.obj S'.property
  let topT' := smallIdentity B T'.obj T'.property
  haveI : IsAffine S'.obj := ‹IsAffine U.obj.left.obj›
  haveI : IsAffine T'.obj := isAffine_closedFibre B i U
  haveI : IsClosedImmersion (B.inclusion.map f') := isClosedImmersion_closedFibreFst B i U
  -- the ring-theoretic hypotheses of the affine case
  have hA : ProetaleWContractible.IsWContractible.{u, u} Γ(S'.obj, ⊤) :=
    BigProetaleSite.isWContractible_of_isWeaklyContractible B S' hU
  have hI : (affineClosedImmersionRingData B f').1 ≤ Ring.jacobson Γ(S'.obj, ⊤) :=
    le_ringJacobson_appTopKer_of_specializes B f' hspec
  have hWc : ProetaleWContractible.IsWContractible.{u, u} Γ(T'.obj, ⊤) :=
    isWContractible_appTop_of_isWContractible_of_specializes B f' hA hspec
  have hV : (AffineIndEtaleProetale.topology B T').IsWeaklyContractible
      (AffineIndEtaleProetale.terminalObj B T') :=
    AffineIndEtaleProetale.isWeaklyContractible_of_isWContractible B T'
      (AffineIndEtaleProetale.terminalObj B T') hWc
  -- the identification `v(U ×_X Z) = U` of the final objects
  let liftIso : (affineIndEtaleLift B f').obj (AffineIndEtaleProetale.terminalObj B T') ≅
      AffineIndEtaleProetale.terminalObj B S' :=
    AffineIndEtaleProetale.affineIndEtaleLift_obj_terminalObj_iso B f' hA hI
  -- the two restrictions and the two inverse images
  haveI : (smallProetaleCompose B g U.property).IsContinuous JS' JX :=
    smallProetaleCompose_isContinuous B g U.property
  haveI : (smallProetaleCompose B g' W.property).IsContinuous JT' JZ :=
    smallProetaleCompose_isContinuous B g' W.property
  let iInv := Functor.sheafPullbackConstruction.sheafPullback
    (smallProetaleBaseChange B Z X i) A JX JZ
  let iUInv := Functor.sheafPullbackConstruction.sheafPullback
    (smallProetaleBaseChange B T' S' f') A JS' JT'
  let resU := (smallProetaleCompose B g U.property).sheafPushforwardContinuous A JS' JX
  let resW := (smallProetaleCompose B g' W.property).sheafPushforwardContinuous A JT' JZ
  have hBC : iInv ⋙ resW ≅ resU ⋙ iUInv :=
    smallProetaleInverseImageRestrictionIso B g' f' i g U.property W.property
      (IsPullback.of_hasPullback g i).flip A
  -- evaluate at the final objects
  have hresW : resW ⋙ sheafToPresheaf JT' A ⋙ (evaluation _ _).obj (op topT') =
      sheafToPresheaf JZ A ⋙ (evaluation _ _).obj
        (op ((smallProetaleCompose B g' W.property).obj topT')) := rfl
  have hresU : resU ⋙ sheafToPresheaf JS' A ⋙ (evaluation _ _).obj (op topS') =
      sheafToPresheaf JX A ⋙ (evaluation _ _).obj
        (op ((smallProetaleCompose B g U.property).obj topS')) := rfl
  calc iInv ⋙ sheafToPresheaf JZ A ⋙ (evaluation _ _).obj (op W)
      ≅ iInv ⋙ sheafToPresheaf JZ A ⋙ (evaluation _ _).obj
          (op ((smallProetaleCompose B g' W.property).obj topT')) :=
        Functor.isoWhiskerLeft iInv (Functor.isoWhiskerLeft (sheafToPresheaf JZ A)
          ((evaluation _ _).mapIso
            (Iso.op (smallProetaleCompose_obj_smallIdentity_closedFibre B i U))))
    _ ≅ (iInv ⋙ resW) ⋙ sheafToPresheaf JT' A ⋙ (evaluation _ _).obj (op topT') :=
        (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerLeft iInv (eqToIso hresW).symm ≪≫ Functor.associator _ _ _
    _ ≅ (resU ⋙ iUInv) ⋙ sheafToPresheaf JT' A ⋙ (evaluation _ _).obj (op topT') :=
        Functor.isoWhiskerRight hBC _
    _ ≅ resU ⋙ (iUInv ⋙ sheafToPresheaf JT' A ⋙
          (evaluation _ _).obj (op ((AffineIndEtaleProetale.inclusion B T').obj
            (AffineIndEtaleProetale.terminalObj B T')))) := Functor.associator _ _ _
    _ ≅ resU ⋙ (sheafToPresheaf JS' A ⋙ (evaluation _ _).obj
          (op ((AffineIndEtaleProetale.inclusion B S').obj
            ((affineIndEtaleLift B f').obj (AffineIndEtaleProetale.terminalObj B T'))))) :=
        Functor.isoWhiskerLeft resU
          (proetaleInverseImage_sections_iso_affineIndEtaleLiftAddCommGrp B f'
            (AffineIndEtaleProetale.terminalObj B T') hV)
    _ ≅ resU ⋙ (sheafToPresheaf JS' A ⋙ (evaluation _ _).obj (op topS')) :=
        Functor.isoWhiskerLeft resU (Functor.isoWhiskerLeft (sheafToPresheaf JS' A)
          ((evaluation _ _).mapIso (Iso.op
            ((AffineIndEtaleProetale.inclusion B S').mapIso liftIso).symm)))
    _ ≅ sheafToPresheaf JX A ⋙ (evaluation _ _).obj
          (op ((smallProetaleCompose B g U.property).obj topS')) :=
        (Functor.associator _ _ _).symm ≪≫ eqToIso hresU
    _ ≅ sheafToPresheaf JX A ⋙ (evaluation _ _).obj (op U) :=
        Functor.isoWhiskerLeft (sheafToPresheaf JX A) ((evaluation _ _).mapIso
          (Iso.op (smallProetaleCompose_obj_smallIdentity B U)).symm)

end

end AlgebraicGeometry.ProEtale

end
