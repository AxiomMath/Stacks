module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkDeltaFunctors

/-!
# Base change of higher direct images, tested on strict henselizations

Consider a cartesian square of schemes
```
X  ←-h-  Y
|f       |e
S  ←-g-  T
```
with `g` quasi-compact and quasi-separated, an abelian sheaf `F` on `T_étale` and `q ≥ 0`. Stacks
0EZU says that the following are equivalent:

1. for every geometric point `x̄` of `X` with image `s̄ = f(x̄)`,
   `H^q(Spec(𝒪^{sh}_{X,x̄}) ×_S T, F) = H^q(Spec(𝒪^{sh}_{S,s̄}) ×_S T, F)`, that is, the
   restriction map along the canonical morphism
   `Spec(𝒪^{sh}_{X,x̄}) ×_S T ⟶ Spec(𝒪^{sh}_{S,s̄}) ×_S T` is bijective;
2. the base change map `f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism.

The stalk at `x̄` of the base change map is a map `(R^q g_* F)_{s̄} ⟶ (R^q h_* e⁻¹ F)_{x̄}`, and by
Stacks 03Q9 (`AlgebraicGeometry.higherDirectImageStalkIso`) its source and target are the two
cohomology groups of (1), the latter because
`Spec(𝒪^{sh}_{X,x̄}) ×_X Y = Spec(𝒪^{sh}_{X,x̄}) ×_S T`. Under these identifications the stalk of
the base change map is the restriction map. A morphism of sheaves is an isomorphism when it is so
on all stalks at geometric points, which gives the equivalence.

## Main results

* `AlgebraicGeometry.isIso_higherBaseChangeMapAb_app_iff_forall_bijective`: the base change map
  `f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism if and only if the restriction maps along
  the morphisms of strict henselization base changes are bijective.

## Implementation notes

The identification of the stalk of the base change map with the restriction map is an equality of
morphisms of δ-functors in `F` out of the stalks of the higher direct images along `g`, which form
a universal δ-functor, so it is checked in degree zero, on germs of sections.

## References

* [Stacks Project, Tag 0EZU](https://stacks.math.columbia.edu/tag/0EZU)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) {X Y S T : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  {f : X ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T} {g : T ⟶ S}

section Geometry

variable (f g) (x : GeometricPoint X)

/-- The canonical morphism `T ×_S Spec(𝒪^{sh}_{X,x}) ⟶ T ×_S Spec(𝒪^{sh}_{S,f(x)})`, the identity
on `T` and the morphism of strict henselizations on the second factor. -/
def strictHenselizationBaseChangeMap :
    pullback g (strictHenselizationToBase B X hX x ≫ f) ⟶
      strictHenselizationBaseChange B hS g (x.map f) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ strictHenselizationSquareMap B hX hS f x)
    (pullback.condition.trans ((congrArg (_ ≫ ·)
      (strictHenselizationSquareMap_comp B hX hS f x).symm).trans (Category.assoc _ _ _).symm))

/-- The projection of `T ×_S Spec(𝒪^{sh}_{X,x})` to `T` factors through
`AlgebraicGeometry.strictHenselizationBaseChangeMap` and the projection of
`T ×_S Spec(𝒪^{sh}_{S,f(x)})` to `T`. -/
theorem strictHenselizationBaseChangeMap_fst :
    pullback.fst g (strictHenselizationToBase B X hX x ≫ f) =
      strictHenselizationBaseChangeMap B hX hS f g x ≫
        strictHenselizationBaseChangeToSource B hS g (x.map f) :=
  (pullback.lift_fst _ _ _).symm

/-- The morphism `AlgebraicGeometry.strictHenselizationBaseChangeMap` followed by the projection
to `Spec(𝒪^{sh}_{S,f(x)})` is the projection to `Spec(𝒪^{sh}_{X,x})` followed by the morphism of
strict henselizations. -/
theorem strictHenselizationBaseChangeMap_snd :
    strictHenselizationBaseChangeMap B hX hS f g x ≫
        strictHenselizationBaseChangeToStrictHenselization B hS g (x.map f) =
      pullback.snd _ _ ≫ strictHenselizationSquareMap B hX hS f x :=
  pullback.lift_snd _ _ _

variable {f g} (sq : IsPullback h e f g)

/-- The canonical morphism `Y ×_X Spec(𝒪^{sh}_{X,x}) ⟶ T ×_S Spec(𝒪^{sh}_{X,x})`. It is an
isomorphism because `Y = X ×_S T`. -/
def strictHenselizationBaseChangeComparison :
    strictHenselizationBaseChange B hX h x ⟶ pullback g (strictHenselizationToBase B X hX x ≫ f) :=
  pullback.lift (pullback.fst _ _ ≫ e) (pullback.snd _ _)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq.w.symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) pullback.condition).trans
        (Category.assoc _ _ _)))))

/-- The inverse of `AlgebraicGeometry.strictHenselizationBaseChangeComparison`. -/
def strictHenselizationBaseChangeComparisonInv :
    pullback g (strictHenselizationToBase B X hX x ≫ f) ⟶ strictHenselizationBaseChange B hX h x :=
  pullback.lift (sq.lift (pullback.snd _ _ ≫ strictHenselizationToBase B X hX x)
      (pullback.fst _ _) ((Category.assoc _ _ _).trans pullback.condition.symm))
    (pullback.snd _ _) (sq.lift_fst _ _ _)

/-- The canonical morphism `Y ×_X Spec(𝒪^{sh}_{X,x}) ⟶ T ×_S Spec(𝒪^{sh}_{X,x})` is an
isomorphism. -/
instance : IsIso (strictHenselizationBaseChangeComparison B hX x sq) := by
  refine ⟨⟨strictHenselizationBaseChangeComparisonInv B hX x sq, ?_, ?_⟩⟩
  · refine pullback.hom_ext ?_ ?_
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans ?_)
      refine Eq.trans ?_ (Category.id_comp _).symm
      refine sq.hom_ext ?_ ?_
      · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (sq.lift_fst _ _ _)).trans ?_)
        refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (pullback.lift_snd _ _ _)).trans
          pullback.condition.symm)
      · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (sq.lift_snd _ _ _)).trans ?_)
        exact pullback.lift_fst _ _ _
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans ?_)
      exact (pullback.lift_snd _ _ _).trans (Category.id_comp _).symm
  · refine pullback.hom_ext ?_ ?_
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans ?_)
      refine (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ e) (pullback.lift_fst _ _ _)).trans ?_)
      exact (sq.lift_snd _ _ _).trans (Category.id_comp _).symm
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans ?_)
      exact (pullback.lift_snd _ _ _).trans (Category.id_comp _).symm

/-- The projection of `Y ×_X Spec(𝒪^{sh}_{X,x})` to `Y` followed by `e` is
`AlgebraicGeometry.strictHenselizationBaseChangeComparison` followed by the projection of
`T ×_S Spec(𝒪^{sh}_{X,x})` to `T`. -/
theorem strictHenselizationBaseChangeComparison_fst :
    strictHenselizationBaseChangeToSource B hX h x ≫ e =
      strictHenselizationBaseChangeComparison B hX x sq ≫
        pullback.fst g (strictHenselizationToBase B X hX x ≫ f) :=
  (pullback.lift_fst _ _ _).symm

end Geometry

section Lifts

variable {C : Type*} [Category* C]

/-- The first components of two morphisms into a fibre product built from the canonical
morphisms of strict henselization base changes agree. -/
theorem fst_eq_of_strictHenselization_lifts
    {YX A Q M Vl W Xsh Ssh Z TS : C} {L : YX ⟶ A} {ql : A ⟶ Q} {fst₁ : Q ⟶ M} {fst₂ : M ⟶ Vl}
    {fsth : A ⟶ W} {fstf : W ⟶ Vl} {qX : YX ⟶ Xsh} {nlX : Xsh ⟶ W} {σ : Xsh ⟶ Ssh}
    {nlS : Ssh ⟶ Vl} {ℓ : TS ⟶ M} {qS : TS ⟶ Ssh} {ρ : Z ⟶ TS} {sndZ : Z ⟶ Xsh} {κ : YX ⟶ Z}
    (h1 : ql ≫ fst₁ ≫ fst₂ = fsth ≫ fstf) (h3 : L ≫ fsth = qX ≫ nlX)
    (h5 : nlX ≫ fstf = σ ≫ nlS) (h6 : ℓ ≫ fst₂ = qS ≫ nlS) (h8 : ρ ≫ qS = sndZ ≫ σ)
    (h10 : κ ≫ sndZ = qX) :
    ((L ≫ ql) ≫ fst₁) ≫ fst₂ = (κ ≫ ρ ≫ ℓ) ≫ fst₂ := by
  calc ((L ≫ ql) ≫ fst₁) ≫ fst₂ = L ≫ (ql ≫ fst₁ ≫ fst₂) := by simp only [Category.assoc]
    _ = (L ≫ fsth) ≫ fstf := by rw [h1, Category.assoc]
    _ = qX ≫ σ ≫ nlS := by rw [h3, Category.assoc, h5]
    _ = (κ ≫ sndZ) ≫ σ ≫ nlS := by rw [h10]
    _ = κ ≫ (ρ ≫ qS) ≫ nlS := by rw [h8]; simp only [Category.assoc]
    _ = (κ ≫ ρ ≫ ℓ) ≫ fst₂ := by rw [Category.assoc, ← h6]; simp only [Category.assoc]

/-- The second components of two morphisms into a fibre product built from the canonical
morphisms of strict henselization base changes agree. -/
theorem snd_eq_of_strictHenselization_lifts
    {YX A Q M T Y Z TS : C} {L : YX ⟶ A} {ql : A ⟶ Q} {fst₁ : Q ⟶ M} {snd₂ : M ⟶ T}
    {snd₁ : Q ⟶ Y} {e : Y ⟶ T} {sndh : A ⟶ Y} {pX : YX ⟶ Y} {ℓ : TS ⟶ M} {pS : TS ⟶ T}
    {ρ : Z ⟶ TS} {fstZ : Z ⟶ T} {κ : YX ⟶ Z}
    (h2 : ql ≫ snd₁ = sndh) (h4 : L ≫ sndh = pX) (h7 : ℓ ≫ snd₂ = pS) (h9 : ρ ≫ pS = fstZ)
    (h11 : κ ≫ fstZ = pX ≫ e) (h12 : fst₁ ≫ snd₂ = snd₁ ≫ e) :
    ((L ≫ ql) ≫ fst₁) ≫ snd₂ = (κ ≫ ρ ≫ ℓ) ≫ snd₂ := by
  calc ((L ≫ ql) ≫ fst₁) ≫ snd₂ = L ≫ (ql ≫ snd₁) ≫ e := by
        rw [Category.assoc, Category.assoc, h12]; simp only [Category.assoc]
    _ = κ ≫ fstZ := by rw [h2, ← Category.assoc, h4, h11]
    _ = (κ ≫ ρ ≫ ℓ) ≫ snd₂ := by rw [← h9, ← h7]; simp only [Category.assoc]

end Lifts

section Criterion

variable (sq : IsPullback h e f g) (x : GeometricPoint X)

/-- The morphism of strict henselization base changes carries the canonical morphisms into the
base changes of an étale neighbourhood to each other. -/
theorem strictHenselizationBaseChange_lift_eq (V : S.Etale)
    (v : (Scheme.pointSmallEtale (x.map f).hom).fiber.obj V) :
    (strictHenselizationBaseChangeEtaleLift B hX h x
        ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V)
        ((pointSmallEtaleComapFiberIso f x.hom).hom.app V v) ≫
      (smallEtaleSquareBaseChangeHom f g h e sq.w V).left) ≫
        pullback.fst ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj V).hom e =
      strictHenselizationBaseChangeComparison B hX x sq ≫
        strictHenselizationBaseChangeMap B hX hS f g x ≫
          strictHenselizationBaseChangeEtaleLift B hS g (x.map f) V v := by
  have h3 : strictHenselizationBaseChangeEtaleLift B hX h x
      ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V)
        ((pointSmallEtaleComapFiberIso f x.hom).hom.app V v) ≫ pullback.fst _ h = _ :=
    pullback.lift_fst _ _ _
  have h4 : strictHenselizationBaseChangeEtaleLift B hX h x
      ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V)
        ((pointSmallEtaleComapFiberIso f x.hom).hom.app V v) ≫ pullback.snd _ h = _ :=
    pullback.lift_snd _ _ _
  have h6 : strictHenselizationBaseChangeEtaleLift B hS g (x.map f) V v ≫ pullback.fst V.hom g =
      _ := pullback.lift_fst _ _ _
  have h7 : strictHenselizationBaseChangeEtaleLift B hS g (x.map f) V v ≫ pullback.snd V.hom g =
      _ := pullback.lift_snd _ _ _
  have h10 : strictHenselizationBaseChangeComparison B hX x sq ≫
      pullback.snd g (strictHenselizationToBase B X hX x ≫ f) = _ := pullback.lift_snd _ _ _
  exact pullback.hom_ext
    (fst_eq_of_strictHenselization_lifts
      (smallEtaleSquareBaseChangeHom_left_fst_fst f g h e sq.w V) h3
      (strictHenselizationNeighborhoodLift_smallEtaleBaseChange B hS hX f x V v) h6
      (strictHenselizationBaseChangeMap_snd B hX hS f g x) h10)
    (snd_eq_of_strictHenselization_lifts
      (MorphismProperty.Over.w (smallEtaleSquareBaseChangeHom f g h e sq.w V)) h4 h7
      (strictHenselizationBaseChangeMap_fst B hX hS f g x).symm
      (strictHenselizationBaseChangeComparison_fst B hX x sq).symm pullback.condition)

end Criterion

/-- Identities are étale, so the identity is the final object of a small étale site. -/
local instance : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
  ⟨fun _ => inferInstance⟩

/-- **The map from the stalk of a direct image, on germs, read on the identity object.** -/
theorem pushforwardStalkToStrictHenselizationSectionsAb_toPresheafFiber_apply {s : GeometricPoint S}
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (V : S.Etale)
    (v : (Scheme.pointSmallEtale s.hom).fiber.obj V)
    (σ : ToType (F.obj.obj (op ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj V)))) :
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (strictHenselizationBaseChange B hS g s))
        Ab.{u + 1} (isTerminalEtaleMkId _)).hom.app _
      ((pushforwardStalkToStrictHenselizationSectionsAb B hS g s).app F
        ((Scheme.pointSmallEtale s.hom).toPresheafFiber V v ((smallEtalePushforwardAb g).obj F).obj
          σ)) =
      sectionsRestrictionAlong (strictHenselizationBaseChangeToSource B hS g s) F
        ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj V)
        (strictHenselizationBaseChangeEtaleLift B hS g s V v) (pullback.lift_snd _ _ _) σ := by
  have h := ConcreteCategory.congr_hom
    (pushforwardStalkToStrictHenselizationSectionsAb_toPresheafFiber B hS g s V v F) σ
  refine (congrArg _ ((ConcreteCategory.comp_apply _ _ σ).symm.trans h)).trans ?_
  exact (sectionsRestrictionAlong_apply _ F _ _ _ σ).symm

/-- The degree-zero identification of global sections with cohomology, read on the identity
object. -/
theorem equiv₀_smallEtaleGlobalSectionsIsoExtZero_hom {Z : Scheme.{u}}
    (G : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (t : ToType ((Sheaf.Γ (smallEtaleTopology Z)
      Ab.{u + 1}).obj G)) :
    Sheaf.H.equiv₀ G (MorphismProperty.Over.mkIdTerminal _ _)
        (((smallEtaleGlobalSectionsIsoExtZero Z).hom.app G) t) =
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Z) Ab.{u + 1}
        (isTerminalEtaleMkId Z)).hom.app G t :=
  AddEquiv.apply_symm_apply _ _

/-- In degree zero, pulling back with a composite comparison is pulling back followed by the
second map, read on the identity object. -/
theorem equiv₀_etaleCohomologyPullback_comp_zero {Z Z' : Scheme.{u}} (k : Z' ⟶ Z)
    {F : Sheaf (smallEtaleTopology Z) Ab.{u + 1}} {G G' : Sheaf (smallEtaleTopology Z') Ab.{u + 1}}
    (φ : (smallEtalePullbackAb k).obj F ⟶ G) (ψ : G ⟶ G') (y : Sheaf.H.{u + 1} F 0) :
    Sheaf.H.equiv₀ G' (MorphismProperty.Over.mkIdTerminal _ _)
        (etaleCohomologyPullback k (φ ≫ ψ) 0 y) =
      ψ.hom.app _ (Sheaf.H.equiv₀ G (MorphismProperty.Over.mkIdTerminal _ _)
        (etaleCohomologyPullback k φ 0 y)) := by
  rw [← etaleCohomologyPullback_comp_mk₀]
  exact (Sheaf.H.equiv₀_naturality _ ψ _).symm

section Criterion

variable (sq : IsPullback h e f g) (x : GeometricPoint X)

/-- The canonical morphism from `Y ×_X Spec(𝒪^{sh}_{X,x})` to the base change along `e` of the
base change along `g` of an étale neighbourhood `V` of `f(x)`, followed by the structure morphism
to `Y`, is the projection to `Y`. -/
theorem pullback_snd_comp_eq (V : S.Etale)
    (v : (Scheme.pointSmallEtale (x.map f).hom).fiber.obj V) :
    (strictHenselizationBaseChangeEtaleLift B hX h x
        ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V)
        ((pointSmallEtaleComapFiberIso f x.hom).hom.app V v) ≫
      (smallEtaleSquareBaseChangeHom f g h e sq.w V).left) ≫
        ((Stacks.EtaleCohomology.smallEtaleBaseChange e).obj
          ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj V)).hom =
      strictHenselizationBaseChangeToSource B hX h x :=
  (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (MorphismProperty.Over.w (smallEtaleSquareBaseChangeHom f g h e sq.w V))).trans
      (pullback.lift_snd _ _ _))

end Criterion

/-- On stalks, the inverse of the identification of `g_*` with `R⁰g_*` undoes the identification. -/
private theorem stalk_map_pushforwardIsoRightDerivedZero_inv_hom_apply {s : GeometricPoint S}
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (z : ToType ((smallEtaleStalkAb s.hom).obj ((smallEtalePushforwardAb g).obj F))) :
    (smallEtaleStalkAb s.hom).map ((pushforwardIsoRightDerivedZero g).inv.app F)
      ((smallEtaleStalkAb s.hom).map ((pushforwardIsoRightDerivedZero g).hom.app F) z) = z :=
  (ConcreteCategory.comp_apply _ _ _).symm.trans ((ConcreteCategory.congr_hom
    ((smallEtaleStalkAb s.hom).mapIso ((pushforwardIsoRightDerivedZero g).app F)).hom_inv_id
      _).trans (ConcreteCategory.id_apply _))

section DegreeZero

variable (sq : IsPullback h e f g) [QuasiCompact g] [QuasiSeparated g] (x : GeometricPoint X)
  (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (V : S.Etale)
  (v : (Scheme.pointSmallEtale (x.map f).hom).fiber.obj V)
  (σ : ToType (F.obj.obj (op ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj V))))

/-- **The comparison of Stacks 03Q9 in degree zero, on germs**, read through the
identification of degree-zero cohomology with sections on the identity object. -/
theorem higherDirectImageStalkComparison_zero_germ :
    ((higherDirectImageStalkComparison B hS g (x.map f)).app 0).app F
    ((smallEtaleStalkAb (x.map f).hom).map ((pushforwardIsoRightDerivedZero g).hom.app F)
      ((Scheme.pointSmallEtale (x.map f).hom).toPresheafFiber V v
        ((smallEtalePushforwardAb g).obj F).obj σ)) =
    (Sheaf.H.equiv₀ ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS g
      (x.map f))).obj F) (MorphismProperty.Over.mkIdTerminal _ _)).symm
      (sectionsRestrictionAlong (strictHenselizationBaseChangeToSource B hS g (x.map f)) F
        ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj V)
        (strictHenselizationBaseChangeEtaleLift B hS g (x.map f) V v)
        (pullback.lift_snd _ _ _) σ) := by
  rw [higherDirectImageStalkComparison_app_zero]
  refine (congrArg (fun z => ((smallEtaleGlobalSectionsIsoExtZero _).hom.app
    ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS g (x.map f))).obj F))
      (((pushforwardStalkToStrictHenselizationSectionsAb B hS g (x.map f)).app F) z))
        (stalk_map_pushforwardIsoRightDerivedZero_inv_hom_apply _ _)).trans ?_
  apply (Sheaf.H.equiv₀ ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS g
    (x.map f))).obj F) (MorphismProperty.Over.mkIdTerminal _ _)).injective
  refine (equiv₀_smallEtaleGlobalSectionsIsoExtZero_hom _ _).trans ?_
  refine Eq.trans ?_ (AddEquiv.apply_symm_apply _ _).symm
  exact pushforwardStalkToStrictHenselizationSectionsAb_toPresheafFiber_apply B hS F V v σ

omit [QuasiCompact g] [QuasiSeparated g] in
/-- The comparison of cohomology of `T ×_S Spec(𝒪^{sh}_{X,x})` and `Y ×_X Spec(𝒪^{sh}_{X,x})` in
degree zero, read on the identity object. -/
theorem equiv₀_comparisonHom_zero (z : Sheaf.H.{u + 1} ((smallEtalePullbackAb
      (pullback.fst g (strictHenselizationToBase B X hX x ≫ f))).obj F) 0) :
    Sheaf.H.equiv₀ ((smallEtalePullbackAb e ⋙ smallEtalePullbackAb
        (strictHenselizationBaseChangeToSource B hX h x)).obj F)
        (MorphismProperty.Over.mkIdTerminal _ _)
      (((etaleCohomologyRestrictionPrecompHom
      (pullback.fst g (strictHenselizationToBase B X hX x ≫ f))
      (strictHenselizationBaseChangeComparison B hX x sq) (smallEtalePullbackAb e)
      (strictHenselizationBaseChangeToSource B hX h x)
      ((smallEtalePullbackAbComp' _ _ _
        (strictHenselizationBaseChangeComparison_fst B hX x sq)).hom ≫
        (smallEtalePullbackAbComp' (strictHenselizationBaseChangeToSource B hX h x) e _
          rfl).inv)).app 0).app F z) =
    ((smallEtalePullbackAbComp' (strictHenselizationBaseChangeToSource B hX h x) e _
        rfl).inv.app F).hom.app _
      (Sheaf.H.equiv₀ ((smallEtalePullbackAb
        (strictHenselizationBaseChangeToSource B hX h x ≫ e)).obj F)
        (MorphismProperty.Over.mkIdTerminal _ _)
      (etaleCohomologyPullback (strictHenselizationBaseChangeComparison B hX x sq)
        ((smallEtalePullbackAbComp' _ _ _ (strictHenselizationBaseChangeComparison_fst B hX x
          sq)).hom.app F) 0 z)) :=
  (congrArg (Sheaf.H.equiv₀ ((smallEtalePullbackAb e ⋙ smallEtalePullbackAb
        (strictHenselizationBaseChangeToSource B hX h x)).obj F)
        (MorphismProperty.Over.mkIdTerminal _ _))
    ((etaleCohomologyRestrictionPrecompHom_app_app_apply _ _ _ _ _ 0 F z).trans
      (congrArg (fun φ => etaleCohomologyPullback
        (strictHenselizationBaseChangeComparison B hX x sq)
        φ 0 z) (NatTrans.comp_app _ _ F)))).trans
    (equiv₀_etaleCohomologyPullback_comp_zero _ _ _ z)

omit [QuasiCompact g] [QuasiSeparated g] in
/-- The restriction from `T ×_S Spec(𝒪^{sh}_{S,f(x)})` in degree zero, on restrictions of
sections. -/
theorem restrictionHom_zero_sectionsRestrictionAlong :
    ((etaleCohomologyRestrictionHom (strictHenselizationBaseChangeToSource B hS g (x.map f))
      (pullback.fst g (strictHenselizationToBase B X hX x ≫ f))
      (strictHenselizationBaseChangeMap B hX hS f g x)
      (strictHenselizationBaseChangeMap_fst B hX hS f g x)).app 0).app F
      ((Sheaf.H.equiv₀ ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS g
        (x.map f))).obj F) (MorphismProperty.Over.mkIdTerminal _ _)).symm
        (sectionsRestrictionAlong (strictHenselizationBaseChangeToSource B hS g (x.map f)) F
          ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj V)
          (strictHenselizationBaseChangeEtaleLift B hS g (x.map f) V v)
          (pullback.lift_snd _ _ _) σ)) =
    (Sheaf.H.equiv₀ ((smallEtalePullbackAb (pullback.fst g
        (strictHenselizationToBase B X hX x ≫ f))).obj F)
        (MorphismProperty.Over.mkIdTerminal _ _)).symm
      (sectionsRestrictionAlong _ F ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj V)
        (strictHenselizationBaseChangeMap B hX hS f g x ≫
          strictHenselizationBaseChangeEtaleLift B hS g (x.map f) V v)
        (comp_hom_eq_of_hom_eq _ _ _ (strictHenselizationBaseChangeMap_fst B hX hS f g x) _ _
          (pullback.lift_snd _ _ _)) σ) :=
  (etaleCohomologyRestrictionHom_app_app_apply _ _ _ _ 0 F _).trans <|
  (AddEquiv.eq_symm_apply _).2 (equiv₀_etaleCohomologyPullback_sectionsRestrictionAlong
    (strictHenselizationBaseChangeMap B hX hS f g x)
    (strictHenselizationBaseChangeToSource B hS g (x.map f)) _
    (strictHenselizationBaseChangeMap_fst B hX hS f g x) F _
    (strictHenselizationBaseChangeEtaleLift B hS g (x.map f) V v) (pullback.lift_snd _ _ _) σ)

variable [QuasiCompact h] [QuasiSeparated h]

/-- The comparison of Stacks 03Q9 in degree zero, through the identification of `h_*` with its
degree-zero derived functor. -/
theorem higherDirectImageStalkComparison_zero_apply' (G : Sheaf (smallEtaleTopology Y) Ab.{u + 1})
    (z : ToType ((smallEtaleStalkAb x.hom).obj ((smallEtalePushforwardAb h).obj G))) :
    ((higherDirectImageStalkComparison B hX h x).app 0).app G
        ((smallEtaleStalkAb x.hom).map ((pushforwardIsoRightDerivedZero h).hom.app G) z) =
      (smallEtaleGlobalSectionsIsoExtZero _).hom.app _
        ((pushforwardStalkToStrictHenselizationSectionsAb B hX h x).app G z) := by
  rw [higherDirectImageStalkComparison_app_zero]
  exact congrArg (fun z => ((smallEtaleGlobalSectionsIsoExtZero _).hom.app
    ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hX h x)).obj G))
      (((pushforwardStalkToStrictHenselizationSectionsAb B hX h x).app G) z))
    (stalk_map_pushforwardIsoRightDerivedZero_inv_hom_apply _ _)

omit [QuasiCompact g] [QuasiSeparated g] in
/-- **The stalk of the base change map in degree zero, on germs.** -/
theorem stalkBaseChange_comparison_zero_germ :
    Sheaf.H.equiv₀ ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hX h x)).obj
        ((smallEtalePullbackAb e).obj F)) (MorphismProperty.Over.mkIdTerminal _ _)
      (((higherDirectImageStalkComparison B hX h x).app 0).app ((smallEtalePullbackAb e).obj F)
        (((higherBaseChangeStalkHom f g h e sq.w x.hom).app 0).app F
          ((smallEtaleStalkAb (x.map f).hom).map ((pushforwardIsoRightDerivedZero g).hom.app F)
            ((Scheme.pointSmallEtale (x.map f).hom).toPresheafFiber V v
              ((smallEtalePushforwardAb g).obj F).obj σ)))) =
      sectionsRestrictionAlong (strictHenselizationBaseChangeToSource B hX h x)
        ((smallEtalePullbackAb e).obj F)
        ((Stacks.EtaleCohomology.smallEtaleBaseChange e).obj
          ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj V))
        (strictHenselizationBaseChangeEtaleLift B hX h x
            ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V)
            ((pointSmallEtaleComapFiberIso f x.hom).hom.app V v) ≫
          (smallEtaleSquareBaseChangeHom f g h e sq.w V).left)
        (pullback_snd_comp_eq B hX sq x V v)
        (smallEtalePullbackAbUnitApp e F ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj V)
          σ) := by
  have hkey := map_rightDerivedZeroUnit_comp_higherBaseChangeMapAb_zero f g h e sq.w F
  have hnat : (smallEtaleStalkPullbackAbIso f x.hom).inv.app
        (((smallEtalePushforwardAb g).rightDerived 0).obj F)
      ((smallEtaleStalkAb (x.map f).hom).map ((pushforwardIsoRightDerivedZero g).hom.app F)
        ((Scheme.pointSmallEtale (x.map f).hom).toPresheafFiber V v
          ((smallEtalePushforwardAb g).obj F).obj σ)) =
      (smallEtaleStalkAb x.hom).map ((smallEtalePullbackAb f).map
        ((pushforwardIsoRightDerivedZero g).hom.app F))
        ((smallEtaleStalkPullbackAbIso f x.hom).inv.app ((smallEtalePushforwardAb g).obj F)
          ((Scheme.pointSmallEtale (x.map f).hom).toPresheafFiber V v
            ((smallEtalePushforwardAb g).obj F).obj σ)) :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans ((ConcreteCategory.congr_hom
      (((smallEtaleStalkPullbackAbIso f x.hom).inv.naturality
        ((pushforwardIsoRightDerivedZero g).hom.app F)).trans
          (congrArg (_ ≫ ·) (Functor.comp_map _ _ _))) _).trans
            (ConcreteCategory.comp_apply _ _ _))
  have hgerm : (smallEtaleStalkPullbackAbIso f x.hom).inv.app ((smallEtalePushforwardAb g).obj F)
      ((Scheme.pointSmallEtale (x.map f).hom).toPresheafFiber V v
        ((smallEtalePushforwardAb g).obj F).obj σ) =
      (Scheme.pointSmallEtale x.hom).toPresheafFiber
        ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V)
        ((pointSmallEtaleComapFiberIso f x.hom).hom.app V v)
        ((smallEtalePullbackAb f).obj ((smallEtalePushforwardAb g).obj F)).obj
        (smallEtalePullbackAbUnitApp f ((smallEtalePushforwardAb g).obj F) V σ) :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans ((ConcreteCategory.congr_hom
      (toPresheafFiber_comp_smallEtaleStalkPullbackAbIso_inv f x.hom
        ((smallEtalePushforwardAb g).obj F) V v) σ).trans (ConcreteCategory.comp_apply _ _ _))
  have hstep : ((higherBaseChangeStalkHom f g h e sq.w x.hom).app 0).app F
      ((smallEtaleStalkAb (x.map f).hom).map ((pushforwardIsoRightDerivedZero g).hom.app F)
        ((Scheme.pointSmallEtale (x.map f).hom).toPresheafFiber V v
          ((smallEtalePushforwardAb g).obj F).obj σ)) =
      (smallEtaleStalkAb x.hom).map ((pushforwardIsoRightDerivedZero h).hom.app
          ((smallEtalePullbackAb e).obj F))
        ((Scheme.pointSmallEtale x.hom).toPresheafFiber
          ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V)
          ((pointSmallEtaleComapFiberIso f x.hom).hom.app V v)
          ((smallEtalePushforwardAb h).obj ((smallEtalePullbackAb e).obj F)).obj
          (((smallEtaleBaseChangeAb f g h e sq.w).app F).hom.app _
            (smallEtalePullbackAbUnitApp f ((smallEtalePushforwardAb g).obj F) V σ))) := by
    refine (ConcreteCategory.comp_apply _ _ _).trans ?_
    refine (congrArg ((smallEtaleStalkAb x.hom).map ((higherBaseChangeMapAb f g h e sq.w 0).app
      F)) hnat).trans ?_
    refine (ConcreteCategory.comp_apply _ _ _).symm.trans ?_
    refine (ConcreteCategory.congr_hom (((smallEtaleStalkAb x.hom).map_comp _ _).symm.trans
      ((congrArg (smallEtaleStalkAb x.hom).map hkey).trans
        ((smallEtaleStalkAb x.hom).map_comp _ _))) _).trans ?_
    refine (ConcreteCategory.comp_apply _ _ _).trans (congrArg _ ?_)
    refine (congrArg _ hgerm).trans ?_
    exact (Scheme.pointSmallEtale x.hom).toPresheafFiber_naturality_apply
      ((smallEtaleBaseChangeAb f g h e sq.w).app F).hom _ _ _
  refine (congrArg (Sheaf.H.equiv₀ ((smallEtalePullbackAb
    (strictHenselizationBaseChangeToSource B hX h x)).obj ((smallEtalePullbackAb e).obj F))
    (MorphismProperty.Over.mkIdTerminal _ _)) ((congrArg
      (((higherDirectImageStalkComparison B hX h x).app 0).app ((smallEtalePullbackAb e).obj F))
        hstep).trans (higherDirectImageStalkComparison_zero_apply' B hX x _ _))).trans ?_
  refine (equiv₀_smallEtaleGlobalSectionsIsoExtZero_hom _ _).trans ?_
  refine (pushforwardStalkToStrictHenselizationSectionsAb_toPresheafFiber_apply B hX
    ((smallEtalePullbackAb e).obj F) _ _ _).trans ?_
  refine (congrArg _ (smallEtaleBaseChangeAb_app_unitApp f g h e sq.w F V σ)).trans ?_
  exact sectionsRestrictionAlong_map _ _ _ _ _ _ _ _

/-- **The two degree-zero composites agree on germs.** -/
theorem stalkBaseChange_square_zero_germ :
    Sheaf.H.equiv₀ ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hX h x)).obj
        ((smallEtalePullbackAb e).obj F)) (MorphismProperty.Over.mkIdTerminal _ _)
      (((higherDirectImageStalkComparison B hX h x).app 0).app ((smallEtalePullbackAb e).obj F)
        (((higherBaseChangeStalkHom f g h e sq.w x.hom).app 0).app F
          ((smallEtaleStalkAb (x.map f).hom).map ((pushforwardIsoRightDerivedZero g).hom.app F)
            ((Scheme.pointSmallEtale (x.map f).hom).toPresheafFiber V v
              ((smallEtalePushforwardAb g).obj F).obj σ)))) =
    Sheaf.H.equiv₀ ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hX h x)).obj
        ((smallEtalePullbackAb e).obj F)) (MorphismProperty.Over.mkIdTerminal _ _)
      (((etaleCohomologyRestrictionPrecompHom
        (pullback.fst g (strictHenselizationToBase B X hX x ≫ f))
        (strictHenselizationBaseChangeComparison B hX x sq) (smallEtalePullbackAb e)
        (strictHenselizationBaseChangeToSource B hX h x)
        ((smallEtalePullbackAbComp' _ _ _
          (strictHenselizationBaseChangeComparison_fst B hX x sq)).hom ≫
          (smallEtalePullbackAbComp' (strictHenselizationBaseChangeToSource B hX h x) e _
            rfl).inv)).app 0).app F
        (((etaleCohomologyRestrictionHom (strictHenselizationBaseChangeToSource B hS g (x.map f))
          (pullback.fst g (strictHenselizationToBase B X hX x ≫ f))
          (strictHenselizationBaseChangeMap B hX hS f g x)
          (strictHenselizationBaseChangeMap_fst B hX hS f g x)).app 0).app F
          (((higherDirectImageStalkComparison B hS g (x.map f)).app 0).app F
            ((smallEtaleStalkAb (x.map f).hom).map ((pushforwardIsoRightDerivedZero g).hom.app F)
              ((Scheme.pointSmallEtale (x.map f).hom).toPresheafFiber V v
                ((smallEtalePushforwardAb g).obj F).obj σ))))) := by
  refine (stalkBaseChange_comparison_zero_germ B hX sq x F V v σ).trans ?_
  have hR := (congrArg (fun z => Sheaf.H.equiv₀ ((smallEtalePullbackAb
      (strictHenselizationBaseChangeToSource B hX h x)).obj ((smallEtalePullbackAb e).obj F))
      (MorphismProperty.Over.mkIdTerminal _ _)
    (((etaleCohomologyRestrictionPrecompHom
        (pullback.fst g (strictHenselizationToBase B X hX x ≫ f))
        (strictHenselizationBaseChangeComparison B hX x sq) (smallEtalePullbackAb e)
        (strictHenselizationBaseChangeToSource B hX h x)
        ((smallEtalePullbackAbComp' _ _ _
          (strictHenselizationBaseChangeComparison_fst B hX x sq)).hom ≫
          (smallEtalePullbackAbComp' (strictHenselizationBaseChangeToSource B hX h x) e _
            rfl).inv)).app 0).app F
      (((etaleCohomologyRestrictionHom (strictHenselizationBaseChangeToSource B hS g (x.map f))
          (pullback.fst g (strictHenselizationToBase B X hX x ≫ f))
          (strictHenselizationBaseChangeMap B hX hS f g x)
          (strictHenselizationBaseChangeMap_fst B hX hS f g x)).app 0).app F z)))
      (higherDirectImageStalkComparison_zero_germ B hS x F V v σ)).trans
    ((congrArg (fun z => Sheaf.H.equiv₀ ((smallEtalePullbackAb e ⋙ smallEtalePullbackAb
        (strictHenselizationBaseChangeToSource B hX h x)).obj F)
        (MorphismProperty.Over.mkIdTerminal _ _)
      (((etaleCohomologyRestrictionPrecompHom
        (pullback.fst g (strictHenselizationToBase B X hX x ≫ f))
        (strictHenselizationBaseChangeComparison B hX x sq) (smallEtalePullbackAb e)
        (strictHenselizationBaseChangeToSource B hX h x)
        ((smallEtalePullbackAbComp' _ _ _
          (strictHenselizationBaseChangeComparison_fst B hX x sq)).hom ≫
          (smallEtalePullbackAbComp' (strictHenselizationBaseChangeToSource B hX h x) e _
            rfl).inv)).app 0).app F z))
      (restrictionHom_zero_sectionsRestrictionAlong B hX hS x F V v σ)).trans
    ((equiv₀_comparisonHom_zero B hX sq x F _).trans (congrArg _
      (equiv₀_etaleCohomologyPullback_sectionsRestrictionAlong
        (strictHenselizationBaseChangeComparison B hX x sq) _ _
        (strictHenselizationBaseChangeComparison_fst B hX x sq) F _ _ _ σ))))
  refine Eq.trans ?_ hR.symm
  have hinj : Function.Injective (((smallEtalePullbackAbComp'
      (strictHenselizationBaseChangeToSource B hX h x) e _ rfl).hom.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 _)))) :=
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
  apply hinj
  refine (smallEtalePullbackAbComp'_sectionsRestrictionAlong_unitApp _ e _ rfl F _ _ _ σ).trans ?_
  refine Eq.trans ?_ (ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app
    (op (Scheme.Etale.mk (𝟙 _)))) ((smallEtalePullbackAbComp'
      (strictHenselizationBaseChangeToSource B hX h x) e _ rfl).inv_hom_id_app F)) _ |>.trans
        (ConcreteCategory.id_apply _)).symm
  exact ConcreteCategory.congr_hom (sectionsRestrictionAlong_congr _ F _ _ _ _
    (strictHenselizationBaseChange_lift_eq B hX hS sq x V v)) σ

end DegreeZero

section Main

variable (sq : IsPullback h e f g) [QuasiCompact g] [QuasiSeparated g] [QuasiCompact h]
  [QuasiSeparated h] (x : GeometricPoint X)

/-- **The stalk of the base change map is the restriction map**, as morphisms of δ-functors: the
stalk at `x` of `f⁻¹ R^• g_* F ⟶ R^• h_* e⁻¹ F`, read through Stacks 03Q9 on both sides, is the
restriction `H^•(T ×_S Spec(𝒪^{sh}_{S,f(x)}), F) ⟶ H^•(T ×_S Spec(𝒪^{sh}_{X,x}), F)` followed by
the identification of `T ×_S Spec(𝒪^{sh}_{X,x})` with `Y ×_X Spec(𝒪^{sh}_{X,x})`. -/
theorem higherBaseChangeStalkHom_comp_comparison :
    (higherBaseChangeStalkHom f g h e sq.w x.hom ≫
        DeltaFunctor.precompHom (smallEtalePullbackAb e)
          (higherDirectImageStalkComparison B hX h x) :
      higherDirectImageStalkDeltaFunctor g (x.map f) ⟶ _) =
      higherDirectImageStalkComparison B hS g (x.map f) ≫
        etaleCohomologyRestrictionHom (strictHenselizationBaseChangeToSource B hS g (x.map f))
          (pullback.fst g (strictHenselizationToBase B X hX x ≫ f))
          (strictHenselizationBaseChangeMap B hX hS f g x)
          (strictHenselizationBaseChangeMap_fst B hX hS f g x) ≫
        etaleCohomologyRestrictionPrecompHom
          (pullback.fst g (strictHenselizationToBase B X hX x ≫ f))
          (strictHenselizationBaseChangeComparison B hX x sq) (smallEtalePullbackAb e)
          (strictHenselizationBaseChangeToSource B hX h x)
          ((smallEtalePullbackAbComp' _ _ _ (strictHenselizationBaseChangeComparison_fst B hX x
            sq)).hom ≫ (smallEtalePullbackAbComp' (strictHenselizationBaseChangeToSource B hX h x) e
              _ rfl).inv) := by
  apply DeltaFunctor.IsUniversal.hom_ext_zero
  refine NatTrans.ext (funext fun F => ?_)
  refine (cancel_epi ((smallEtaleStalkAb (x.map f).hom).map
    ((pushforwardIsoRightDerivedZero g).hom.app F))).1 ?_
  refine (Scheme.pointSmallEtale (x.map f).hom).presheafFiber_hom_ext fun V v => ?_
  ext σ
  apply (Sheaf.H.equiv₀ ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hX h
    x)).obj ((smallEtalePullbackAb e).obj F)) (MorphismProperty.Over.mkIdTerminal _ _)).injective
  exact stalkBaseChange_square_zero_germ B hX hS sq x F V v σ

end Main

section Statement

variable (sq : IsPullback h e f g) [QuasiCompact g] [QuasiSeparated g]

/-- Consider a cartesian square of schemes
```
X  ←-h-  Y
|f       |e
S  ←-g-  T
```
with `g : T ⟶ S` quasi-compact and quasi-separated, let `F` be an abelian sheaf on `T_étale` and
let `q ≥ 0`. The following are equivalent:

1. for every geometric point `x̄` of `X` with image `s̄ = f(x̄)`, the restriction map
   `H^q(T ×_S Spec(𝒪^{sh}_{S,s̄}), F) ⟶ H^q(T ×_S Spec(𝒪^{sh}_{X,x̄}), F)` along the canonical
   morphism `AlgebraicGeometry.strictHenselizationBaseChangeMap` is bijective;
2. the base change map `f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism.

Here the cohomology groups are those of the inverse images of `F` along the projections to `T`, and
the restriction map is pull back along the canonical morphism together with the comparison of
the iterated inverse image with the inverse image along the composite. -/
@[stacks 0EZU]
theorem isIso_higherBaseChangeMapAb_app_iff_forall_bijective
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (q : ℕ) :
    (∀ x : GeometricPoint X, Function.Bijective
      (etaleCohomologyPullback (strictHenselizationBaseChangeMap B hX hS f g x)
        ((smallEtalePullbackAbComp' _ _ _
          (strictHenselizationBaseChangeMap_fst B hX hS f g x)).hom.app
          F) q)) ↔
      IsIso ((higherBaseChangeMapAb f g h e sq.w q).app F) := by
  have : QuasiCompact h := MorphismProperty.of_isPullback sq.flip inferInstance
  have : QuasiSeparated h := MorphismProperty.of_isPullback sq.flip inferInstance
  rw [← isIso_higherBaseChangeMapAb_app_iff_forall_isIso_stalk f h e g sq F q]
  refine forall_congr' fun x => ?_
  have hsq := congrArg (fun η => (DeltaFunctor.Hom.app η q).app F)
    (higherBaseChangeStalkHom_comp_comparison B hX hS sq x)
  have iαX := isIso_higherDirectImageStalkComparison_app B hX h x q ((smallEtalePullbackAb e).obj F)
  have iαS := isIso_higherDirectImageStalkComparison_app B hS g (x.map f) q F
  have bRκ : Function.Bijective (etaleCohomologyPullback
      (strictHenselizationBaseChangeComparison B hX x sq)
      (((smallEtalePullbackAbComp' _ _ _ (strictHenselizationBaseChangeComparison_fst B hX x
        sq)).hom ≫ (smallEtalePullbackAbComp' (strictHenselizationBaseChangeToSource B hX h x) e _
          rfl).inv).app F) q) :=
    bijective_etaleCohomologyPullback_of_isIso _ _ q
  change (((higherBaseChangeStalkHom f g h e sq.w x.hom).app q).app F ≫
      ((higherDirectImageStalkComparison B hX h x).app q).app ((smallEtalePullbackAb e).obj F)) =
    ((higherDirectImageStalkComparison B hS g (x.map f)).app q).app F ≫
      ((etaleCohomologyRestrictionHom (strictHenselizationBaseChangeToSource B hS g (x.map f))
        (pullback.fst g (strictHenselizationToBase B X hX x ≫ f))
        (strictHenselizationBaseChangeMap B hX hS f g x)
        (strictHenselizationBaseChangeMap_fst B hX hS f g x)).app q).app F ≫
      ((etaleCohomologyRestrictionPrecompHom
        (pullback.fst g (strictHenselizationToBase B X hX x ≫ f))
        (strictHenselizationBaseChangeComparison B hX x sq) (smallEtalePullbackAb e)
        (strictHenselizationBaseChangeToSource B hX h x)
        ((smallEtalePullbackAbComp' _ _ _ (strictHenselizationBaseChangeComparison_fst B hX x
          sq)).hom ≫ (smallEtalePullbackAbComp' (strictHenselizationBaseChangeToSource B hX h x) e
            _ rfl).inv)).app q).app F at hsq
  have hbc : IsIso (((higherBaseChangeStalkHom f g h e sq.w x.hom).app q).app F) ↔
      IsIso ((smallEtaleStalkAb x.hom).map ((higherBaseChangeMapAb f g h e sq.w q).app F)) :=
    isIso_comp_left_iff ((smallEtaleStalkPullbackAbIso f x.hom).inv.app _) _
  refine Iff.trans ?_ hbc
  refine Iff.trans ?_ (isIso_comp_right_iff _ (((higherDirectImageStalkComparison B hX h x).app
    q).app ((smallEtalePullbackAb e).obj F)))
  refine Iff.trans ?_ (iff_of_eq (congrArg IsIso hsq).symm)
  refine Iff.trans ?_ (isIso_comp_left_iff _ _).symm
  refine Iff.trans ?_ (ConcreteCategory.isIso_iff_bijective _).symm
  exact (Function.Bijective.of_comp_iff' bRκ _).symm

end Statement

end AlgebraicGeometry
