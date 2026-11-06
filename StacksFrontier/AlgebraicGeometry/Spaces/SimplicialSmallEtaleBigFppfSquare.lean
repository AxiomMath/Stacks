module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.OverSimplicialObjectAugmentationFunctorLeft
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleBigFppf
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfRingedTopos
public import StacksFrontier.CategoryTheory.Sites.Localization.AndMorphisms
public import StacksFrontier.CategoryTheory.Sites.Localization.AndMorphismsTwoSquare
public import StacksFrontier.CategoryTheory.Sites.Simplicial.OverSimplicialObjectTotalSite

/-!
# Fppf hypercoverings of algebraic spaces: the square of topoi

Let `T` be a big fppf site of algebraic spaces over `S`, `U` a simplicial object of it and
`a : U → X` an augmentation. The morphism of topoi `h : Sh((Spaces/U)_{fppf,total}) ⟶
Sh(U_{spaces,étale})` of the functor `u`, `V/U_n ↦ V/U_n`, the augmentation
`a_{fppf} : Sh((Spaces/U)_{fppf,total}) ⟶ Sh((Spaces/X)_fppf)`, the augmentation
`a : Sh(U_{spaces,étale}) ⟶ Sh(X_{spaces,étale})` and the morphism
`h_{-1} = a_X : Sh((Spaces/X)_fppf) ⟶ Sh(X_{spaces,étale})` form a commutative square
(Stacks 0DH5).

The square of sites behind it is `(V/X in degree n) ↦ V ×_X U_n / U_n ↦ V ×_X U_n / X` against
`(V/X in degree n) ↦ V/X`, compared by the first projection. It is Guitart exact: every
factorization of an arrow `W/X ⟶ V/X` with `W/U_m` is joined by a zigzag to the canonical one
through `V ×_X U_m / U_m`. So right Kan extension along the cocontinuous functors exchanges with
restriction along the continuous ones (Stacks 0FN1).

## Main definitions

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.bigFppfTwoSquare`: the `2`-square of sites.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.bigFppfAugmentationSquareIso`:
  **Stacks 0DH5.**
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {U : SimplicialObject T.Spaces} {X : T.Spaces}
  (a : U ⟶ (SimplicialObject.const T.Spaces).obj X)

/-- The first projection `V ×_X U_n ⟶ V`, a morphism over `X`. -/
def bigFppfSquareApp (V : SimplicialSpacesEtaleSite T.schemeSite S T.scheme_mem
      ((SimplicialObject.const T.Spaces).obj X)) :
    (SimplicialOver.augmentationFunctor U a).obj
        ((toBigFppfTotal U).obj ((pullbackFunctor a).obj V)) ⟶
      (SpacesEtale.inclusion T.schemeSite S T.scheme_mem X).obj ((constForget X).obj V) :=
  Over.homMk (pullback.fst V.obj.1.hom (a.app (op V.degree))) pullback.condition

/-- The underlying morphism of `bigFppfSquareApp a V` is the first projection `V ×_X U_n ⟶ V`. -/
theorem bigFppfSquareApp_left (V : SimplicialSpacesEtaleSite T.schemeSite S T.scheme_mem
      ((SimplicialObject.const T.Spaces).obj X)) :
    (bigFppfSquareApp a V).left = pullback.fst V.obj.1.hom (a.app (op V.degree)) := rfl

/-- The first projections `V ×_X U_n ⟶ V` form a natural transformation. -/
def bigFppfSquare :
    (pullbackFunctor a ⋙ toBigFppfTotal U) ⋙ SimplicialOver.augmentationFunctor U a ⟶
      constForget X ⋙ SpacesEtale.inclusion T.schemeSite S T.scheme_mem X where
  app := bigFppfSquareApp a
  naturality {_V V'} g := Over.OverMorphism.ext
    (((Over.comp_left _ _ _ _ _).trans
      (congrArg (· ≫ pullback.fst V'.obj.1.hom (a.app (op V'.degree)))
      (SimplicialOver.augmentationFunctor_map_left_overSimplicialObjectAugmentationFunctorLeft a
        ((toBigFppfTotal U).map ((pullbackFunctor a).map g))))).trans
      ((pullback.lift_fst _ _ _).trans (Over.comp_left _ _ _ _ _).symm))

/-- **The square of sites of Stacks 0DH5**:
`(V/X in degree n) ↦ V ×_X U_n / U_n ↦ V ×_X U_n / X` against `(V/X in degree n) ↦ V/X`,
compared by the first projection. -/
abbrev bigFppfTwoSquare :
    TwoSquare (pullbackFunctor a ⋙ toBigFppfTotal U) (constForget X)
      (SimplicialOver.augmentationFunctor U a)
      (SpacesEtale.inclusion T.schemeSite S T.scheme_mem X) :=
  bigFppfSquare a

namespace BigFppfSquare

variable {a} {X₂ : Grothendieck (SimplicialOver.slices U)}
  {X₃ : SpacesEtale T.schemeSite S T.scheme_mem X}
  (g : (SimplicialOver.augmentationFunctor U a).obj X₂ ⟶
    (SpacesEtale.inclusion T.schemeSite S T.scheme_mem X).obj X₃)

/-- The factorization `W/U_m ⟶ V ×_X U_m / U_m` of an arrow `g : W/X ⟶ V/X`, in degree `m`. -/
def canonicalHom :
    fiberOver U X₂ ⟶ ((pullbackFunctor a).obj ⟨X₂.base.unop, X₃⟩).obj.1 :=
  Over.homMk (pullback.lift g.left (fiberOver U X₂).hom (Over.w g)) (pullback.lift_snd _ _ _)

/-- The factorization of `g` through `V/X` placed in the degree of `W`. -/
def canonicalLift :
    X₂ ⟶ (pullbackFunctor a ⋙ toBigFppfTotal U).obj ⟨X₂.base.unop, X₃⟩ :=
  (slicesι U X₂.base.unop).map (canonicalHom g)

/-- The fiber of `canonicalLift g` is the morphism `W ⟶ V ×_X U_m` induced by `g` and the
structure morphism `W ⟶ U_m`. -/
theorem canonicalLift_fiber_left :
    (Grothendieck.Hom.fiber (canonicalLift g)).left =
      pullback.lift g.left (fiberOver U X₂).hom (Over.w g) :=
  SimplicialOver.overMap_ι_map_fiber_left_simplicialSmallEtaleBigFppf U (op X₂.base.unop)
    (X := fiberOver U X₂) (Y := ((pullbackFunctor a).obj ⟨X₂.base.unop, X₃⟩).obj.1)
    (canonicalHom g)

/-- The image of `canonicalLift g` composed with the first projection `V ×_X U_m ⟶ V` is `g`. -/
theorem canonicalLift_comm :
    (SimplicialOver.augmentationFunctor U a).map (canonicalLift g) ≫
      (bigFppfTwoSquare a).app ⟨X₂.base.unop, X₃⟩ ≫
        (SpacesEtale.inclusion T.schemeSite S T.scheme_mem X).map (𝟙 X₃) = g := by
  refine Over.OverMorphism.ext ?_
  show ((SimplicialOver.augmentationFunctor U a).map (canonicalLift g)).left ≫
    pullback.fst X₃.1.hom (a.app (op X₂.base.unop)) ≫ 𝟙 _ = g.left
  exact (whisker_eq _ (Category.comp_id _)).trans
    ((eq_whisker
      ((SimplicialOver.augmentationFunctor_map_left_overSimplicialObjectAugmentationFunctorLeft a
        (canonicalLift g)).trans (canonicalLift_fiber_left g)) _).trans (pullback.lift_fst _ _ _))

/-- The canonical object of `(bigFppfTwoSquare a).StructuredArrowRightwards g`. -/
abbrev canonicalObj : (bigFppfTwoSquare a).StructuredArrowRightwards g :=
  TwoSquare.StructuredArrowRightwards.mk _ g ⟨X₂.base.unop, X₃⟩ (canonicalLift g) (𝟙 X₃)
    (canonicalLift_comm g)

variable {g}

/-- A morphism into the image of `m : V ⟶ W` under `pullbackFunctor a ⋙ toBigFppfTotal U` is
determined by its components in the two projections of the pullback. -/
private theorem comp_map_eq_of_pullback_eq {V W : SimplicialSpacesEtaleSite T.schemeSite S
      T.scheme_mem ((SimplicialObject.const T.Spaces).obj X)} (m : V ⟶ W)
    {A : Grothendieck (SimplicialOver.slices U)}
    (p : A ⟶ (pullbackFunctor a ⋙ toBigFppfTotal U).obj V)
    (q : A ⟶ (pullbackFunctor a ⋙ toBigFppfTotal U).obj W)
    (hb : Grothendieck.Hom.base p ≫ m.base.op = Grothendieck.Hom.base q)
    (hfst : (Grothendieck.Hom.fiber p).left ≫ pullback.fst V.obj.1.hom (a.app (op V.degree)) ≫
      m.hom = (Grothendieck.Hom.fiber q).left ≫ pullback.fst W.obj.1.hom (a.app (op W.degree)))
    (hsnd : (Grothendieck.Hom.fiber p).left ≫ pullback.snd V.obj.1.hom (a.app (op V.degree)) ≫
      U.map m.base.op = (Grothendieck.Hom.fiber q).left ≫
        pullback.snd W.obj.1.hom (a.app (op W.degree))) :
    p ≫ (pullbackFunctor a ⋙ toBigFppfTotal U).map m = q := by
  refine SimplicialOver.overMapHom_ext_simplicialSmallEtaleBigFppf U hb ?_
  refine (SimplicialOver.overMap_comp_fiber_left_simplicialSmallEtaleBigFppf U p
    ((pullbackFunctor a ⋙ toBigFppfTotal U).map m)).trans ?_
  change _ ≫ ((pullbackFunctor a).map m).hom = _
  have pf : ((pullbackFunctor a).map m).hom ≫ pullback.fst W.obj.1.hom (a.app (op W.degree)) =
      pullback.fst V.obj.1.hom (a.app (op V.degree)) ≫ m.hom := pullback.lift_fst _ _ _
  have ps : ((pullbackFunctor a).map m).hom ≫ pullback.snd W.obj.1.hom (a.app (op W.degree)) =
      pullback.snd V.obj.1.hom (a.app (op V.degree)) ≫ U.map m.base.op := pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((whisker_eq _ pf).trans hfst)
  · exact (Category.assoc _ _ _).trans ((whisker_eq _ ps).trans hsnd)

/-- Every object of `(bigFppfTwoSquare a).StructuredArrowRightwards g` is joined by a zigzag to
the canonical one. -/
theorem zigzag_canonicalObj (j : (bigFppfTwoSquare a).StructuredArrowRightwards g) :
    Zigzag j (canonicalObj g) := by
  obtain ⟨X₁, b₁, b, comm, rfl⟩ := TwoSquare.StructuredArrowRightwards.mk_surjective j
  let m := X₂.base.unop
  have hU : U.map (Grothendieck.Hom.base b₁) ≫ a.app (op X₁.degree) = a.app (op m) :=
    SimplicialOver.augmentationApp_naturality U a (Grothendieck.Hom.base b₁)
  have hb₁ : (Grothendieck.Hom.fiber b₁).left ≫
      pullback.snd X₁.obj.1.hom (a.app (op X₁.degree)) =
        (fiberOver U X₂).hom ≫ U.map (Grothendieck.Hom.base b₁) :=
    Over.w (Grothendieck.Hom.fiber b₁)
  have hc : ((Grothendieck.Hom.fiber b₁).left ≫
      pullback.fst X₁.obj.1.hom (a.app (op X₁.degree))) ≫ b.hom.left = g.left := by
    have h0 : ((SimplicialOver.augmentationFunctor U a).map b₁).left ≫
        pullback.fst X₁.obj.1.hom (a.app (op X₁.degree)) ≫ b.hom.left = g.left :=
      congrArg Over.Hom.left comm
    exact (Category.assoc _ _ _).trans
      ((eq_whisker
        (SimplicialOver.augmentationFunctor_map_left_overSimplicialObjectAugmentationFunctorLeft a
          b₁).symm _).trans h0)
  have hw : ((Grothendieck.Hom.fiber b₁).left ≫
      pullback.fst X₁.obj.1.hom (a.app (op X₁.degree))) ≫ X₁.obj.1.hom =
        (fiberOver U X₂).hom ≫ a.app (op m) :=
    (Category.assoc _ _ _).trans ((whisker_eq _ pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans ((eq_whisker hb₁ _).trans
        ((Category.assoc _ _ _).trans (whisker_eq _ hU)))))
  let X₁' : SimplicialSpacesEtaleSite T.schemeSite S T.scheme_mem
      ((SimplicialObject.const T.Spaces).obj X) := ⟨m, X₁.obj⟩
  let c' : fiberOver U X₂ ⟶ ((pullbackFunctor a).obj X₁').obj.1 :=
    Over.homMk (pullback.lift _ _ hw) (pullback.lift_snd _ _ _)
  let b₁' : X₂ ⟶ (pullbackFunctor a ⋙ toBigFppfTotal U).obj X₁' := (slicesι U m).map c'
  have hb₁' : (Grothendieck.Hom.fiber b₁').left = pullback.lift _ _ hw :=
    SimplicialOver.overMap_ι_map_fiber_left_simplicialSmallEtaleBigFppf U (op m)
      (X := fiberOver U X₂) (Y := ((pullbackFunctor a).obj X₁').obj.1) c'
  have comm' : (SimplicialOver.augmentationFunctor U a).map b₁' ≫ (bigFppfTwoSquare a).app X₁' ≫
      (SpacesEtale.inclusion T.schemeSite S T.scheme_mem X).map b = g := by
    refine Over.OverMorphism.ext ?_
    show ((SimplicialOver.augmentationFunctor U a).map b₁').left ≫
      pullback.fst X₁.obj.1.hom (a.app (op m)) ≫ b.hom.left = g.left
    exact (eq_whisker
      ((SimplicialOver.augmentationFunctor_map_left_overSimplicialObjectAugmentationFunctorLeft a
        b₁').trans hb₁') _).trans
      ((Category.assoc _ _ _).symm.trans ((eq_whisker (pullback.lift_fst _ _ _) _).trans hc))
  let j' : (bigFppfTwoSquare a).StructuredArrowRightwards g :=
    TwoSquare.StructuredArrowRightwards.mk _ g X₁' b₁' b comm'
  let m₁ : X₁' ⟶ X₁ :=
    ⟨(Grothendieck.Hom.base b₁).unop, 𝟙 _, (Category.id_comp _).trans (Category.comp_id _).symm⟩
  let m₂ : X₁' ⟶ ⟨m, X₃⟩ :=
    ⟨𝟙 _, b.hom.left, (Over.w b.hom).trans (Category.comp_id _).symm⟩
  have hm₁ : (constForget X).map m₁ = 𝟙 _ :=
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext rfl)
  have hm₂ : (constForget X).map m₂ = b :=
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext rfl)
  have lf : pullback.lift _ _ hw ≫ pullback.fst X₁.obj.1.hom (a.app (op m)) =
      (Grothendieck.Hom.fiber b₁).left ≫ pullback.fst X₁.obj.1.hom (a.app (op X₁.degree)) :=
    pullback.lift_fst _ _ _
  have ls : pullback.lift _ _ hw ≫ pullback.snd X₁.obj.1.hom (a.app (op m)) =
      (fiberOver U X₂).hom := pullback.lift_snd _ _ _
  have e₁ : b₁' ≫ (pullbackFunctor a ⋙ toBigFppfTotal U).map m₁ = b₁ :=
    comp_map_eq_of_pullback_eq m₁ b₁' b₁ (Category.id_comp _)
      ((eq_whisker hb₁' _).trans ((Category.assoc _ _ _).symm.trans
        ((eq_whisker lf _).trans (Category.comp_id _))))
      ((eq_whisker hb₁' _).trans ((Category.assoc _ _ _).symm.trans
        ((eq_whisker ls _).trans hb₁.symm)))
  have e₂ : b₁' ≫ (pullbackFunctor a ⋙ toBigFppfTotal U).map m₂ = canonicalLift g :=
    comp_map_eq_of_pullback_eq m₂ b₁' _ (Category.id_comp _)
      (((eq_whisker hb₁' _).trans ((Category.assoc _ _ _).symm.trans ((eq_whisker lf _).trans
        (hc.trans (pullback.lift_fst _ _ _).symm)))).trans
          (eq_whisker (canonicalLift_fiber_left g).symm _))
      (((eq_whisker hb₁' _).trans ((Category.assoc _ _ _).symm.trans ((eq_whisker ls _).trans
        ((whisker_eq _ (U.map_id _)).trans ((Category.comp_id _).trans
          (pullback.lift_snd _ _ _).symm))))).trans
            (eq_whisker (canonicalLift_fiber_left g).symm _))
  refine Relation.ReflTransGen.tail (Relation.ReflTransGen.single (b := j') (Or.inr ⟨?_⟩))
    (Or.inl ⟨?_⟩)
  · refine StructuredArrow.homMk (CostructuredArrow.homMk m₁ ?_) ?_
    · exact (eq_whisker hm₁ _).trans (Category.id_comp _)
    · exact CostructuredArrow.hom_ext _ _ e₁
  · refine StructuredArrow.homMk (CostructuredArrow.homMk m₂ ?_) ?_
    · exact (eq_whisker hm₂ _).trans (Category.comp_id _)
    · exact CostructuredArrow.hom_ext _ _ e₂

end BigFppfSquare

open BigFppfSquare in

/-- **The square of sites of Stacks 0DH5 is Guitart exact**: the categories of factorizations of
an arrow `W/X ⟶ V/X` through the square are connected. -/
instance guitartExact_bigFppfTwoSquare : (bigFppfTwoSquare a).GuitartExact := by
  rw [TwoSquare.guitartExact_iff_isConnected_rightwards]
  intro X₂ X₃ g
  have : Nonempty ((bigFppfTwoSquare a).StructuredArrowRightwards g) := ⟨canonicalObj g⟩
  exact zigzag_isConnected fun j₁ j₂ ↦
    (zigzag_canonicalObj j₁).trans (zigzag_symmetric.symm _ _ (zigzag_canonicalObj j₂))

/-- Base change along the augmentation followed by `u` is continuous. -/
instance pullbackFunctor_comp_toBigFppfTotal_isContinuous :
    (pullbackFunctor a ⋙ toBigFppfTotal U).IsContinuous
      (topology ((SimplicialObject.const T.Spaces).obj X))
      (SimplicialOver.totalTopology T.topology U) :=
  Functor.isContinuous_comp (pullbackFunctor a) (toBigFppfTotal U)
    (topology ((SimplicialObject.const T.Spaces).obj X)) (topology U)
    (SimplicialOver.totalTopology T.topology U)

set_option synthInstance.maxHeartbeats 400000 in
/-- **Stacks 0FN1 for the square of Stacks 0DH5**: right Kan extension along the cocontinuous
functors `V/U_n ↦ V/X` and "forget the degree" exchanges with restriction along the continuous
functors `V/X ↦ V ×_X U_n / U_n` and `X_{spaces,étale} ⊂ (Spaces/X)_fppf`. -/
def bigFppfExchangeIso :
    (pullbackFunctor a ⋙ toBigFppfTotal U).sheafPushforwardContinuous (Type (u + 1))
        (topology ((SimplicialObject.const T.Spaces).obj X))
        (SimplicialOver.totalTopology T.topology U) ⋙
      (constForget X).sheafPushforwardCocontinuous (Type (u + 1))
        (topology ((SimplicialObject.const T.Spaces).obj X))
        (SpacesEtale.topology T.schemeSite S T.scheme_mem X) ≅
    (SimplicialOver.augmentationFunctor U a).sheafPushforwardCocontinuous (Type (u + 1))
        (SimplicialOver.totalTopology T.topology U) (BigFppfSpaceOver.topology T X) ⋙
      (SpacesEtale.inclusion T.schemeSite S T.scheme_mem X).sheafPushforwardContinuous
        (Type (u + 1)) (SpacesEtale.topology T.schemeSite S T.scheme_mem X)
        (BigFppfSpaceOver.topology T X) :=
  Stacks.Sites.CocontinuousExchange.sheafIsoOfTwoSquareAndMorphismsTwoSquare (Type (u + 1))
    (topology ((SimplicialObject.const T.Spaces).obj X))
    (SimplicialOver.totalTopology T.topology U)
    (SpacesEtale.topology T.schemeSite S T.scheme_mem X) (BigFppfSpaceOver.topology T X)
    (bigFppfTwoSquare a)

/-- **Stacks 0DH5.** Let `U` be a simplicial algebraic space with an augmentation `a : U → X`.
The square of topoi
```
  Sh((Spaces/U)_{fppf,total}) --h--> Sh(U_{spaces,étale})
           | a_fppf                        | a
           v                               v
  Sh((Spaces/X)_fppf) ------h_{-1}----> Sh(X_{spaces,étale})
```
commutes: `a ∘ h ≅ h_{-1} ∘ a_{fppf}`, where `h` is given by `u : V/U_n ↦ V/U_n`, `a_{fppf}` is
the augmentation of the total site (Stacks 09WL), `a` is the augmentation of the spaces-étale
sites (Stacks 0DE7) and `h_{-1} = a_X` is the comparison of Stacks 0DGM. -/
def bigFppfAugmentationSquareIso :
    ((augmentationRingedToposHom a).toToposHom.comp (bigFppfTotalToposHom U)).pushforward ≅
      ((BigFppfSpaceSite.fppfToSpacesEtaleMorphism T X).comp
        (SimplicialOver.augmentationMorphismOfTopoi T.topology U a)).pushforward :=
  bigFppfExchangeIso a ≪≫ Functor.isoWhiskerRight
    (eqToIso (SimplicialOver.augmentationMorphismOfTopoi_pushforward T.topology U a).symm) _

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
