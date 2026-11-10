module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionRingedSquareCommutes
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceEtale
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.InverseImageComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposRelocalizedMorphism

/-!
# The constructions of Stacks 073M are compatible with étale localization

Let `S` be a scheme and let `f : 𝒳 ⥤ 𝒴` be a morphism of categories fibred in groupoids over
`(Sch/S)_{fppf}`, with `𝒳` and `𝒴` representable by algebraic spaces `F` and `G`, such that the
induced morphism of algebraic spaces `f : F ⟶ G` is étale. Write `f_small` for the corresponding
morphism of small étale ringed topoi. Stacks 0GQA asserts that the diagram

```
(Sh(F_étale), 𝒪_F) --f_small--> (Sh(G_étale), 𝒪_G)
       |                              |
      i_F                            i_G
       v                              v
(Sh(𝒳_étale), 𝒪_𝒳) -----f-----> (Sh(𝒴_étale), 𝒪_𝒴)
       |                              |
      π_F                            π_G
       v                              v
(Sh(F_étale), 𝒪_F) --f_small--> (Sh(G_étale), 𝒪_G)
```

of ringed topoi commutes, where `i_F`, `π_F`, `i_G`, `π_G` are the morphisms of ringed topoi of
Stacks 073M and the middle arrow is the morphism of ringed topoi of Stacks 06TW. Both squares
commute, in the sense of Stacks 04IC: their two composites are 2-isomorphic morphisms of ringed
topoi.

## Main definitions

* `AlgebraicGeometry.Space.etaleSquareFibredLeg` and
  `AlgebraicGeometry.Space.etaleSquareSpaceLeg`: the two composites `f ∘ i_F` and
  `i_G ∘ f_small` around the upper square.
* `AlgebraicGeometry.Space.etaleSquareUpperTwoIso`: the upper square commutes as a diagram of
  ringed topoi.
* `AlgebraicGeometry.Space.etaleLocalizationRingedSquares`: **Stacks 0GQA**, both squares of the
  diagram commute as diagrams of ringed topoi.

## Implementation notes

The upper square is proved on inverse images. The inverse image of `i_G ∘ f_small` is
restriction along the functor `G_étale ⥤ 𝒴` of Stacks 073M followed by `f_small⁻¹`, which for an
étale `f` is restriction along postcomposition `F_étale ⥤ G_étale` (Stacks 03LQ, as
`AlgebraicGeometry.Space.smallToposMorphismTypeU_inverseImageIso`); the inverse image of
`f ∘ i_F` is restriction along `F_étale ⥤ 𝒳 ⥤ 𝒴`. The two composite functors of sites are
isomorphic by `AlgebraicGeometry.Space.restrictionFunctorPostcompIso`, so the two inverse images
are isomorphic. The structure maps are matched by
`AlgebraicGeometry.RingedToposHom.TwoIso.ofSquareInverseImage`: every structure map in sight is,
on underlying sheaves of sets, a transport along an equality of sheaves, except the structure map
of `f_small`, which is the comparison of Stacks 03LQ at the structure sheaf (Stacks 03LV); and the
structure sheaf of `𝒴` carries the components of the comparison isomorphism to the identity,
because they are vertical
(`AlgebraicGeometry.Space.isHomLift_restrictionFunctorPostcompIso_hom_app`).

The lower square is Stacks 073N at the induced morphism, which holds without the étaleness
hypothesis: `AlgebraicGeometry.Space.restrictionRingedSquareTwoIso`.

## References

* [Stacks Project, Tag 0GQA](https://stacks.math.columbia.edu/tag/0GQA)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 073N](https://stacks.math.columbia.edu/tag/073N)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sheaves.ToposPullback

universe ww vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J.HasSheafCompose (forget RingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J.HasSheafCompose (forget CommRingCat.{ww})] [K.HasSheafCompose (forget CommRingCat.{ww})]
  (G : C ⥤ D) [G.IsContinuous J K] (O : Sheaf K CommRingCat.{ww})

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [J.HasSheafCompose (forget RingCat)]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The comparison of the inverse image of a sheaf of commutative rings with its restriction,
followed by a transport along an equality of the restriction with another sheaf, is on
underlying sheaves of sets the transport alone. -/
theorem forget_map_restrictionCommRingIso_hom_comp_eqToHom {O' : Sheaf J CommRingCat.{ww}}
    (h : (G.sheafPushforwardContinuous CommRingCat.{ww} J K).obj O = O') :
    (sheafCompose J (forget CommRingCat.{ww})).map
        ((restrictionCommRingIso J K G O).hom ≫ eqToHom h) =
      eqToHom (congrArg (sheafCompose J (forget CommRingCat.{ww})).obj h) := by
  rw [Functor.map_comp, restrictionCommRingIso_hom_forget, eqToHom_map]
  exact Category.id_comp _

end Stacks.Sheaves.ToposPullback

namespace CategoryTheory.Functor

universe w₁ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {D : Type u₃} [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E]
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'} {K : GrothendieckTopology D}
  {L : GrothendieckTopology E}

/-- **A square of restriction functors at sheaves identified by transports.** Let
`ψ : u ⋙ f ≅ v ⋙ u'` be an isomorphism of continuous functors of sites, and let a sheaf of sets
`Q` on `E` and sheaves on `D`, `C` and `C'` be identified with its restrictions by equalities.
If `Q` carries each component of `ψ` to the identity on sections, then the comparison of the two
iterated restrictions of `Q` induced by `ψ` is the composite of the transports. -/
theorem sheafPushforwardContinuousComp'_hom_app_comp_eqToHom
    (u : C ⥤ D) (f : D ⥤ E) (v : C ⥤ C') (u' : C' ⥤ E) [u.IsContinuous J K]
    [f.IsContinuous K L] [v.IsContinuous J J'] [u'.IsContinuous J' L] [(u ⋙ f).IsContinuous J L]
    (ψ : u ⋙ f ≅ v ⋙ u') (Q : Sheaf L (Type w₁)) {P : Sheaf K (Type w₁)}
    {O : Sheaf J (Type w₁)} {O' : Sheaf J' (Type w₁)}
    (e₁ : (f.sheafPushforwardContinuous (Type w₁) K L).obj Q = P)
    (e₂ : (u.sheafPushforwardContinuous (Type w₁) J K).obj P = O)
    (e₃ : (u'.sheafPushforwardContinuous (Type w₁) J' L).obj Q = O')
    (e₄ : (v.sheafPushforwardContinuous (Type w₁) J J').obj O' = O)
    (hψ : ∀ (U : C) (z : Q.obj.obj (Opposite.op (u'.obj (v.obj U)))),
      HEq (Q.obj.map (ψ.hom.app U).op z) z) :
    (sheafPushforwardContinuousComp' ψ.symm (Type w₁) J J' L ≪≫
        (sheafPushforwardContinuousComp u f (Type w₁) J K L).symm).hom.app Q ≫
      (u.sheafPushforwardContinuous (Type w₁) J K).map (eqToHom e₁) ≫ eqToHom e₂ =
    (v.sheafPushforwardContinuous (Type w₁) J J').map (eqToHom e₃) ≫ eqToHom e₄ := by
  subst e₁ e₂ e₃
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply TypeCat.homEquiv.injective
  funext z
  refine eq_of_heq ((hψ U.unop z).trans ?_)
  have key : ∀ {P' Q' : Sheaf J (Type w₁)} (h : P' = Q') (x : P'.obj.obj U),
      HEq x ((eqToHom h).hom.app U x) := by
    intro P' Q' h x
    cases h
    rfl
  exact key e₄ z

end CategoryTheory.Functor

namespace AlgebraicGeometry.RingedToposHom

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ w₀

variable {A : RingedTopos.{v₁, u₁, w₀}} {B : RingedTopos.{v₂, u₂, w₀}}
  {C : RingedTopos.{v₃, u₃, w₀}} {D : RingedTopos.{v₄, u₄, w₀}}
  [A.J.HasSheafCompose (forget RingCat.{w₀})] [B.J.HasSheafCompose (forget RingCat.{w₀})]
  [C.J.HasSheafCompose (forget RingCat.{w₀})] [D.J.HasSheafCompose (forget RingCat.{w₀})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]

/-- **A square of ringed topoi commutes when its inverse images do, compatibly with the
structure maps.** Consider a square of morphisms of ringed topoi `f ∘ iF` and `iG ∘ fs` from `A`
to `D`, and suppose the inverse image of `fs` is identified, by `ι`, with a functor `R` carrying
the underlying sheaf of `𝒪_B` to that of `𝒪_A`, in such a way that the structure map of `fs`
becomes the identity. Then an isomorphism `γ : iG⁻¹ ∘ R ≅ f⁻¹ ∘ iF⁻¹` which carries the composite
of the structure maps of `iG` (read through `R`) to the composite of those of `f` and `iF` gives a
2-isomorphism of ringed topoi `f ∘ iF ≅ iG ∘ fs`. -/
noncomputable def TwoIso.ofSquareInverseImage (iF : RingedToposHom A C) (f : RingedToposHom C D)
    (fs : RingedToposHom A B) (iG : RingedToposHom B D) {R : B.Topos ⥤ A.Topos}
    (ι : fs.toToposHom.inverseImage ≅ R) (hR : R.obj (B.forgetRing.obj B.O) = A.forgetRing.obj A.O)
    (hι : A.forgetRing.map fs.fSharpInverseImage =
      ι.hom.app (B.forgetRing.obj B.O) ≫ eqToHom hR)
    (γ : iG.toToposHom.inverseImage ⋙ R ≅ f.toToposHom.inverseImage ⋙ iF.toToposHom.inverseImage)
    (h : γ.hom.app (D.forgetRing.obj D.O) ≫
        iF.toToposHom.inverseImage.map (C.forgetRing.map f.fSharpInverseImage) ≫
          A.forgetRing.map iF.fSharpInverseImage =
      R.map (B.forgetRing.map iG.fSharpInverseImage) ≫ eqToHom hR) :
    TwoIso (f.comp iF) (iG.comp fs) :=
  TwoIso.ofInverseImageIso (Functor.isoWhiskerLeft iG.toToposHom.inverseImage ι ≪≫ γ) <|
    ((congrArg (CategoryStruct.comp _) (comp_fSharpInverseImage_forget f iF)).trans
      (Category.assoc _ _ _)).trans <|
    (congrArg (CategoryStruct.comp (ι.hom.app _)) h).trans <|
    (ι.hom.naturality_assoc (B.forgetRing.map iG.fSharpInverseImage) _).symm.trans <|
    (congrArg (CategoryStruct.comp _) hι.symm).trans (comp_fSharpInverseImage_forget iG fs).symm

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.Space

universe u v w v' w'

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
  (eF : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (G ⋙ typeToCat)).p)
  (f : 𝒳 ⥤ 𝒴) (hf : p.IsFibredOneMorphism q f)

section UpperSquare

variable [∀ P : 𝒳ᵒᵖ ⥤ Type u, f.op.HasPointwiseRightKanExtension P]

/-- The composite `f ∘ i_F` around the upper square of Stacks 0GQA: the morphism of ringed topoi
`i_F` of Stacks 073M followed by the morphism of ringed topoi of Stacks 06TW induced by `f`. -/
noncomputable def etaleSquareFibredLeg :
    RingedToposHom (smallEtaleRingedTopos B S hS ⟨F, hF⟩)
      (FibredSite.associatedRingedTopos B S hS q hq .etale) :=
  RingedToposHom.comp (X := smallEtaleRingedTopos B S hS ⟨F, hF⟩)
    (Y := FibredSite.associatedRingedTopos B S hS p hp .etale)
    (Z := FibredSite.associatedRingedTopos B S hS q hq .etale)
    (FibredSite.ringedToposMorphism B S hS p q hp hq f hf .etale)
    (restrictionRingedToposHom B S hS F p hp eF hF)

/-- The composite `i_G ∘ f_small` around the upper square of Stacks 0GQA: the morphism of small
étale ringed topoi of the induced morphism of algebraic spaces followed by the morphism of ringed
topoi `i_G` of Stacks 073M. -/
noncomputable def etaleSquareSpaceLeg :
    RingedToposHom (smallEtaleRingedTopos B S hS ⟨F, hF⟩)
      (FibredSite.associatedRingedTopos B S hS q hq .etale) :=
  RingedToposHom.comp (X := smallEtaleRingedTopos B S hS ⟨F, hF⟩)
    (Y := smallEtaleRingedTopos B S hS ⟨G, hG⟩)
    (Z := FibredSite.associatedRingedTopos B S hS q hq .etale)
    (restrictionRingedToposHom B S hS G q hq eG hG)
    (smallEtaleRingedToposHom B S hS
      (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq))

/-- The comparison of the inverse images of the upper square of Stacks 0GQA, with the inverse
image of `f_small` replaced by restriction along postcomposition: restriction along
`G_étale ⥤ 𝒴` and then along postcomposition `F_étale ⥤ G_étale` is restriction along
`F_étale ⥤ 𝒳` and then along `f`, through the isomorphism of composite functors
`AlgebraicGeometry.Space.restrictionFunctorPostcompIso`. -/
noncomputable def etaleSquareInverseImageIso
    (hg : IsEtale B S hS
      (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq).hom) :
    (restrictionRingedToposHom B S hS G q hq eG hG).toToposHom.inverseImage ⋙
        smallEtaleSetRestriction B S hS
          (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq) hg ≅
      (FibredSite.ringedToposMorphism B S hS p q hp hq f hf .etale).toToposHom.inverseImage ⋙
        (restrictionRingedToposHom B S hS F p hp eF hF).toToposHom.inverseImage := by
  letI := hp.isFibered
  letI := hq.isFibered
  letI := (hf.isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology .etale).over (B.obj hS))).1
  letI := restrictionFunctor_isContinuous B S hS F p hp eF
  letI := restrictionFunctor_isContinuous B S hS G q hq eG
  letI := Functor.isContinuous_comp (restrictionFunctor B S hS F p eF) f
    (SmallEtale.topology B S hS F) (BigFppfOver.associatedTopology B S hS p .etale)
    (BigFppfOver.associatedTopology B S hS q .etale)
  letI : (smallEtalePostcomp B S hS _ hg).IsContinuous (SmallEtale.topology B S hS F)
      (SmallEtale.topology B S hS G) := smallEtalePostcomp_isContinuous B S hS _ hg
  exact Functor.sheafPushforwardContinuousComp' (restrictionFunctorPostcompIso B S hS
        (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq hg).symm (Type u)
      (SmallEtale.topology B S hS F) (SmallEtale.topology B S hS G)
      (BigFppfOver.associatedTopology B S hS q .etale) ≪≫
    (Functor.sheafPushforwardContinuousComp (restrictionFunctor B S hS F p eF) f (Type u)
      (SmallEtale.topology B S hS F) (BigFppfOver.associatedTopology B S hS p .etale)
      (BigFppfOver.associatedTopology B S hS q .etale)).symm

/-- The inverse-image form of the structure map of `i_F` is the comparison of the inverse image
of the structure sheaf with its restriction, followed by the identification of the restricted
structure sheaf of `𝒳` with that of `F`. -/
theorem restrictionRingedToposHom_fSharpInverseImage :
    letI := restrictionFunctor_isContinuous B S hS F p hp eF
    (restrictionRingedToposHom B S hS F p hp eF hF).fSharpInverseImage =
      (restrictionCommRingIso (SmallEtale.topology B S hS F)
        (BigFppfOver.associatedTopology B S hS p .etale)
        (restrictionFunctor B S hS F p eF)
        (FibredSite.structureSheaf B S hS p hp .etale)).hom ≫
      eqToHom (inverseImage_structureSheaf_eq B S hS F p hp eF hF) :=
  Equiv.symm_apply_apply _ _

/-- The inverse-image structure map of `i_F`, on underlying sheaves of sets, is a transport. -/
theorem forgetRing_map_restrictionRingedToposHom_fSharpInverseImage :
    letI := restrictionFunctor_isContinuous B S hS F p hp eF
    (smallEtaleRingedTopos B S hS ⟨F, hF⟩).forgetRing.map
        (restrictionRingedToposHom B S hS F p hp eF hF).fSharpInverseImage =
      eqToHom (congrArg (smallEtaleRingedTopos B S hS ⟨F, hF⟩).forgetRing.obj
        (inverseImage_structureSheaf_eq B S hS F p hp eF hF)) :=
  let := restrictionFunctor_isContinuous B S hS F p hp eF
  (congrArg (smallEtaleRingedTopos B S hS ⟨F, hF⟩).forgetRing.map
    (restrictionRingedToposHom_fSharpInverseImage B S hS F p hp hF eF)).trans
    (Stacks.Sheaves.ToposPullback.forget_map_restrictionCommRingIso_hom_comp_eqToHom
      (SmallEtale.topology B S hS F) (BigFppfOver.associatedTopology B S hS p .etale)
      (restrictionFunctor B S hS F p eF) (FibredSite.structureSheaf B S hS p hp .etale)
      (inverseImage_structureSheaf_eq B S hS F p hp eF hF))

/-- The inverse-image structure map of the morphism of ringed topoi of a 1-morphism, on
underlying sheaves of sets, is a transport. -/
theorem forgetRing_map_ringedToposMorphism_fSharpInverseImage :
    letI := hp.isFibered
    letI := hq.isFibered
    letI := (hf.isContinuous_and_isCocontinuous_inheritedTopology
      ((B.baseTopology .etale).over (B.obj hS))).1
    (FibredSite.associatedRingedTopos B S hS p hp .etale).forgetRing.map
        (FibredSite.ringedToposMorphism B S hS p q hp hq f hf .etale).fSharpInverseImage =
      eqToHom (congrArg (FibredSite.associatedRingedTopos B S hS p hp .etale).forgetRing.obj
        (FibredSite.inverseImageStructureSheaf_eq B S hS p q hp hq f hf .etale)) :=
  let := hp.isFibered
  let := hq.isFibered
  let := (hf.isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology .etale).over (B.obj hS))).1
  (congrArg (FibredSite.associatedRingedTopos B S hS p hp .etale).forgetRing.map
    (FibredSite.ringedToposMorphism_fSharpInverseImage B S hS p q hp hq f hf .etale)).trans
    (Stacks.Sheaves.ToposPullback.forget_map_restrictionCommRingIso_hom_comp_eqToHom
      (BigFppfOver.associatedTopology B S hS p .etale)
      (BigFppfOver.associatedTopology B S hS q .etale) f
      (FibredSite.structureSheaf B S hS q hq .etale)
      (FibredSite.inverseImageStructureSheaf_eq B S hS p q hp hq f hf .etale))

omit [∀ (P : 𝒳ᵒᵖ ⥤ Type u), f.op.HasPointwiseRightKanExtension P] in
/-- The structure sheaf of `𝒴` carries each component of the comparison isomorphism of the
étale square to the identity on sections. -/
theorem forgetRing_structureSheaf_map_restrictionFunctorPostcompIso_hom_app_heq
    (hg : IsEtale B S hS
      (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq).hom)
    (U : SmallEtale B S hS F)
    (z : ((sheafCompose (BigFppfOver.associatedTopology B S hS q .etale)
      (forget CommRingCat.{u})).obj (FibredSite.structureSheaf B S hS q hq .etale)).obj.obj
        (Opposite.op ((restrictionFunctor B S hS G q eG).obj ((smallEtalePostcomp B S hS
          (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq)
            hg).obj U)))) :
    HEq (((sheafCompose (BigFppfOver.associatedTopology B S hS q .etale)
      (forget CommRingCat.{u})).obj (FibredSite.structureSheaf B S hS q hq .etale)).obj.map
        ((restrictionFunctorPostcompIso B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f
          hf.comp_eq hg).hom.app U).op z) z := by
  have := isHomLift_restrictionFunctorPostcompIso_hom_app B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩)
    p q eF eG f hf.comp_eq hg U
  have hφ := IsHomLift.fac' q
    (𝟙 (q.obj ((restrictionFunctor B S hS F p eF ⋙ f).obj U)))
    ((restrictionFunctorPostcompIso B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f
        hf.comp_eq hg).hom.app U)
  change HEq ((forget CommRingCat).map (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
    (q.map ((restrictionFunctorPostcompIso B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f
        hf.comp_eq hg).hom.app U))).op) z) z
  rw [hφ, Category.id_comp, eqToHom_trans, eqToHom_map, eqToHom_op, eqToHom_map, eqToHom_map]
  have key : ∀ {T T' : Type u} (h : T = T') (x : T),
      HEq (ConcreteCategory.hom (eqToHom h : T ⟶ T') x) x := by
    intro T T' h x
    cases h
    rfl
  exact key _ z

omit [∀ (P : 𝒳ᵒᵖ ⥤ Type u), f.op.HasPointwiseRightKanExtension P] in
/-- Restricting the underlying sheaf of `𝒪_G` along postcomposition gives the underlying sheaf of
`𝒪_F`, on the nose. -/
theorem etaleSquare_hR
    (hg : IsEtale B S hS
      (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq).hom) :
    (smallEtaleSetRestriction B S hS
          (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq) hg).obj
        ((smallEtaleRingedTopos B S hS ⟨G, hG⟩).forgetRing.obj
          (smallEtaleRingedTopos B S hS ⟨G, hG⟩).O) =
      (smallEtaleRingedTopos B S hS ⟨F, hF⟩).forgetRing.obj
        (smallEtaleRingedTopos B S hS ⟨F, hF⟩).O :=
  rfl

/-- The structure maps of the upper square of Stacks 0GQA, on underlying sheaves of sets, are
matched by the comparison of inverse images. -/
theorem etaleSquare_h
    (hg : IsEtale B S hS
      (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq).hom) :
    (etaleSquareInverseImageIso B S hS F G p q hp hq hF hG eF eG f hf hg).hom.app
        ((FibredSite.associatedRingedTopos B S hS q hq .etale).forgetRing.obj
          (FibredSite.associatedRingedTopos B S hS q hq .etale).O) ≫
      (restrictionRingedToposHom B S hS F p hp eF hF).toToposHom.inverseImage.map
        ((FibredSite.associatedRingedTopos B S hS p hp .etale).forgetRing.map
          (FibredSite.ringedToposMorphism B S hS p q hp hq f hf .etale).fSharpInverseImage) ≫
      (smallEtaleRingedTopos B S hS ⟨F, hF⟩).forgetRing.map
        (restrictionRingedToposHom B S hS F p hp eF hF).fSharpInverseImage =
    (smallEtaleSetRestriction B S hS
          (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq) hg).map
        ((smallEtaleRingedTopos B S hS ⟨G, hG⟩).forgetRing.map
          (restrictionRingedToposHom B S hS G q hq eG hG).fSharpInverseImage) ≫
      eqToHom (etaleSquare_hR B S hS F G p q hF hG eF eG f hf hg) := by
  rw [forgetRing_map_restrictionRingedToposHom_fSharpInverseImage,
    forgetRing_map_restrictionRingedToposHom_fSharpInverseImage,
    forgetRing_map_ringedToposMorphism_fSharpInverseImage]
  let := hp.isFibered
  let := hq.isFibered
  let := (hf.isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology .etale).over (B.obj hS))).1
  let := restrictionFunctor_isContinuous B S hS F p hp eF
  let := restrictionFunctor_isContinuous B S hS G q hq eG
  let := Functor.isContinuous_comp (restrictionFunctor B S hS F p eF) f
    (SmallEtale.topology B S hS F) (BigFppfOver.associatedTopology B S hS p .etale)
    (BigFppfOver.associatedTopology B S hS q .etale)
  let : (smallEtalePostcomp B S hS _ hg).IsContinuous (SmallEtale.topology B S hS F)
      (SmallEtale.topology B S hS G) := smallEtalePostcomp_isContinuous B S hS _ hg
  refine Functor.sheafPushforwardContinuousComp'_hom_app_comp_eqToHom
    (J := SmallEtale.topology B S hS F) (J' := SmallEtale.topology B S hS G)
    (K := BigFppfOver.associatedTopology B S hS p .etale)
    (L := BigFppfOver.associatedTopology B S hS q .etale)
    (restrictionFunctor B S hS F p eF) f (smallEtalePostcomp B S hS _ hg)
    (restrictionFunctor B S hS G q eG)
    (restrictionFunctorPostcompIso B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f
      hf.comp_eq hg)
    ((sheafCompose (BigFppfOver.associatedTopology B S hS q .etale) (forget CommRingCat.{u})).obj
      (FibredSite.structureSheaf B S hS q hq .etale)) _ _ _ _ ?_
  intro U z
  exact forgetRing_structureSheaf_map_restrictionFunctorPostcompIso_hom_app_heq B S hS F G p q hq hF
      hG eF eG f hf hg U z

omit [∀ (P : 𝒳ᵒᵖ ⥤ Type u), f.op.HasPointwiseRightKanExtension P] in
/-- The structure map of `f_small`, for an étale `f`, through the identification of its inverse
image with restriction along postcomposition. -/
theorem forgetRing_map_smallEtaleRingedToposHom_fSharpInverseImage_eq
    (hg : IsEtale B S hS
      (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq).hom) :
    (smallEtaleRingedTopos B S hS ⟨F, hF⟩).forgetRing.map
        (smallEtaleRingedToposHom B S hS (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩)
          p q eF eG f hf.comp_eq)).fSharpInverseImage =
      (smallToposMorphismTypeU_inverseImageIso B S hS _ hg).hom.app
          ((smallEtaleRingedTopos B S hS ⟨G, hG⟩).forgetRing.obj
            (smallEtaleRingedTopos B S hS ⟨G, hG⟩).O) ≫
        eqToHom (etaleSquare_hR B S hS F G p q hF hG eF eG f hf hg) :=
  (forgetRing_fSharpInverseImage_eq_inverseImageIso B S hS _ hg).trans (Category.comp_id _).symm

/-- **The upper square of Stacks 0GQA commutes.** For an étale induced morphism of algebraic
spaces, the two composites `f ∘ i_F` and `i_G ∘ f_small` are 2-isomorphic morphisms of ringed
topoi. -/
noncomputable def etaleSquareUpperTwoIso
    (hg : IsEtale B S hS
      (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq).hom) :
    RingedToposHom.TwoIso (A := smallEtaleRingedTopos B S hS ⟨F, hF⟩)
      (B := FibredSite.associatedRingedTopos B S hS q hq .etale)
      (etaleSquareFibredLeg B S hS F p q hp hq hF eF f hf)
      (etaleSquareSpaceLeg B S hS F G p q hq hF hG eF eG f hf) :=
  RingedToposHom.TwoIso.ofSquareInverseImage
    (restrictionRingedToposHom B S hS F p hp eF hF)
    (FibredSite.ringedToposMorphism B S hS p q hp hq f hf .etale)
    (smallEtaleRingedToposHom B S hS
      (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq))
    (restrictionRingedToposHom B S hS G q hq eG hG)
    (smallToposMorphismTypeU_inverseImageIso B S hS _ hg)
    (etaleSquare_hR B S hS F G p q hF hG eF eG f hf hg)
    (forgetRing_map_smallEtaleRingedToposHom_fSharpInverseImage_eq B S hS F G p q hF hG eF eG f
      hf hg)
    (etaleSquareInverseImageIso B S hS F G p q hp hq hF hG eF eG f hf hg)
    (etaleSquare_h B S hS F G p q hp hq hF hG eF eG f hf hg)

end UpperSquare

/-- **Stacks 0GQA.** Let `f : 𝒳 ⥤ 𝒴` be a morphism of categories fibred in groupoids over
`(Sch/S)_{fppf}`, with `𝒳` and `𝒴` representable by algebraic spaces `F` and `G` through the
chosen equivalences `eF` and `eG`, such that the induced morphism of algebraic spaces
`f : F ⟶ G` (`AlgebraicGeometry.Space.inducedSpacesHom`) is étale, and let `f_small` be the
corresponding morphism of small étale ringed topoi
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom`). Then the diagram
```
(Sh(F_étale), 𝒪_F) --f_small--> (Sh(G_étale), 𝒪_G)
       |                              |
      i_F                            i_G
       v                              v
(Sh(𝒳_étale), 𝒪_𝒳) -----f-----> (Sh(𝒴_étale), 𝒪_𝒴)
       |                              |
      π_F                            π_G
       v                              v
(Sh(F_étale), 𝒪_F) --f_small--> (Sh(G_étale), 𝒪_G)
```
is a commutative diagram of ringed topoi: the first component is a 2-isomorphism (Stacks 04IC)
`f ∘ i_F ≅ i_G ∘ f_small` of morphisms of ringed topoi, the second a 2-isomorphism
`π_G ∘ f ≅ f_small ∘ π_F`. Here `i_F`, `i_G` are
`AlgebraicGeometry.Space.restrictionRingedToposHom` and `π_F`, `π_G` are
`AlgebraicGeometry.Space.projectionRingedToposHom` (Stacks 073M), and the middle arrow is
`AlgebraicGeometry.FibredSite.ringedToposMorphism` (Stacks 06TW), whose direct image exists by
`AlgebraicGeometry.Space.hasPointwiseRightKanExtension_op_of_equivalenceOver`. -/
@[stacks 0GQA "both squares of the diagram formed by i_F, i_G, pi_F, pi_G, f and f_small commute \
as diagrams of ringed topoi, for an etale induced morphism f : F -> G"]
noncomputable def etaleLocalizationRingedSquares
    (hg : IsEtale B S hS
      (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq).hom) :
    letI : ∀ P : 𝒳ᵒᵖ ⥤ Type u, f.op.HasPointwiseRightKanExtension P :=
      hasPointwiseRightKanExtension_op_of_equivalenceOver B S hS F p G q eF eG f
    RingedToposHom.TwoIso (A := smallEtaleRingedTopos B S hS ⟨F, hF⟩)
        (B := FibredSite.associatedRingedTopos B S hS q hq .etale)
        (etaleSquareFibredLeg B S hS F p q hp hq hF eF f hf)
        (etaleSquareSpaceLeg B S hS F G p q hq hF hG eF eG f hf) ×
      RingedToposHom.TwoIso (A := FibredSite.associatedRingedTopos B S hS p hp .etale)
        (B := smallEtaleRingedTopos B S hS ⟨G, hG⟩)
        (restrictionSquareFibredLeg B S hS G p q hp hq hG eG f hf)
        (restrictionSquareSpaceLeg B S hS F G p hp hF hG eF
          (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq)) :=
  letI : ∀ P : 𝒳ᵒᵖ ⥤ Type u, f.op.HasPointwiseRightKanExtension P :=
    hasPointwiseRightKanExtension_op_of_equivalenceOver B S hS F p G q eF eG f
  (etaleSquareUpperTwoIso B S hS F G p q hp hq hF hG eF eG f hf hg,
    restrictionRingedSquareTwoIso B S hS F G p q hp hq hF hG eF eG f hf)

end AlgebraicGeometry.Space

end
