module

public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.ModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Injectives
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.HigherDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceAlgebra
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose

/-!
# Base change of direct images of sheaves of modules along a Guitart exact square

Let
```
  𝒵 --- a ---> 𝒳
  |            |
  b            f
  v            v
  𝒴' -- g ---> 𝒴
```
be a square of functors between categories fibred in groupoids over the big fppf category of
`S`, each strictly over the base, filled by a 2-cell `w : a ⋙ f ⟶ b ⋙ g` which acts on the
structure rings by identities. If the square is Guitart exact, then the base change map
`g⁻¹ f_* ⟶ b_* a⁻¹` of direct and inverse images of sheaves of modules of **Stacks 06WE** is an
isomorphism.

This is the degree-zero part of **Stacks 075H**, in the generality of a Guitart exact square
(**Stacks 075B** is the instance of a 2-fibre product square).

## Main definitions

* `AlgebraicGeometry.Stack.moduleDirectImageDataIso`: the direct image of presheaves of modules of
  **Stacks 06WD** is, up to a transport of scalars, the functor of compatible sections.
* `AlgebraicGeometry.Stack.modulePresheafGuitartBaseChangeIso`: the base change isomorphism on
  presheaves of modules.
* `AlgebraicGeometry.Stack.moduleSheafGuitartBaseChangeIso`: the base change isomorphism on
  sheaves of modules.
* `AlgebraicGeometry.Stack.moduleHigherDirectImageGuitartBaseChangeIso`: the base change
  isomorphism `g⁻¹ Rⁱf_* ℱ ≅ Rⁱb_* a⁻¹ℱ` on higher direct images.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]

/-- If `P ⋙ G ≅ H` with `P` additive, homology-preserving and carrying injective objects to
injective objects, then `(Rᵖ G)(P M) ≅ (Rᵖ H)(M)`. -/
noncomputable def rightDerivedObjIsoOfComp [EnoughInjectives C] [EnoughInjectives D]
    (P : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [P.Additive] [G.Additive] [H.Additive]
    [P.PreservesHomology] (hP : ∀ I : C, Injective I → Injective (P.obj I))
    (e : P ⋙ G ≅ H) (M : C) (p : ℕ) :
    (G.rightDerived p).obj (P.obj M) ≅ (H.rightDerived p).obj M :=
  let I := injectiveResolution M
  (Stacks.RelativeCech.mapInjectiveResolution P I
      (fun n => hP _ (I.injective n))).isoRightDerivedObj G p ≪≫
    (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) p).mapIso
      ((NatIso.mapHomologicalComplex e (ComplexShape.up ℕ)).app I.cocomplex) ≪≫
    (I.isoRightDerivedObj H p).symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

universe u v w m v' w'

section Transport

variable {X : Type v} [Category.{w} X] {Y : Type v'} [Category.{w'} Y]
  (f : X ⥤ Y) (R : Yᵒᵖ ⥤ RingCat.{u})

/-- The direct image of presheaves of modules of **Stacks 06WD**, for a ring presheaf `T` on the
source equal to the restriction of the one on the target, is the functor of compatible sections
precomposed with the transport of scalars along that equality. -/
noncomputable def moduleDirectImageDataIso (T : Xᵒᵖ ⥤ RingCat.{u}) (h : T = f.op ⋙ R) :
    (moduleDirectImageData.{u, v, w, m} f R T h).1 ≅
      PresheafOfModules.restrictScalars (eqToHom h.symm) ⋙
        moduleSectionsFunctor.{u, v, w, max u v w m v' w'} f R := by
  subst h
  exact Iso.refl _

/-- Restriction of scalars along the identity of a presheaf of rings, written as `eqToHom` of a
self-equality, is the identity functor. -/
noncomputable def restrictScalarsEqToHomSelfIso {C : Type v} [Category.{w} C]
    (T : Cᵒᵖ ⥤ RingCat.{u}) (h : T = T) :
    PresheafOfModules.restrictScalars.{m} (eqToHom h) ≅ 𝟭 _ :=
  Iso.refl _

end Transport

section Presheaf

variable {𝒵 𝒳 𝒴' 𝒴 : Type (u + 1)} [Category.{u} 𝒵] [Category.{u} 𝒳] [Category.{u} 𝒴']
  [Category.{u} 𝒴]
  (a : 𝒵 ⥤ 𝒳) (b : 𝒵 ⥤ 𝒴') (f : 𝒳 ⥤ 𝒴) (g : 𝒴' ⥤ 𝒴) (w : TwoSquare a b f g)
  (R : 𝒴ᵒᵖ ⥤ RingCat.{u}) (RX : 𝒳ᵒᵖ ⥤ RingCat.{u}) (RY' : 𝒴'ᵒᵖ ⥤ RingCat.{u})
  (RZ : 𝒵ᵒᵖ ⥤ RingCat.{u})
  (hX : RX = f.op ⋙ R) (hY' : RY' = g.op ⋙ R) (hZa : RZ = a.op ⋙ RX) (hZb : RZ = b.op ⋙ RY')
  (ha : b.op ⋙ g.op ⋙ R = a.op ⋙ f.op ⋙ R)
  (hRw : ∀ z : 𝒵ᵒᵖ, R.map (w.op.natTrans.app z) = eqToHom (Functor.congr_obj ha z))
  [w.GuitartExact]

/-- **Base change for the direct image of presheaves of modules of Stacks 06WD along a Guitart
exact square**, with the ring presheaves of the four corners given as presheaves equal to the
restrictions of the one of `𝒴`: `g⁻¹ f_* ≅ b_* a⁻¹`. -/
noncomputable def modulePresheafGuitartBaseChangeIso :
    (moduleDirectImageData.{u, u + 1, u, u} f R RX hX).1 ⋙
        PresheafOfModules.pushforward₀ g R ⋙ PresheafOfModules.restrictScalars (eqToHom hY') ≅
      PresheafOfModules.pushforward₀ a RX ⋙ PresheafOfModules.restrictScalars (eqToHom hZa) ⋙
        (moduleDirectImageData.{u, u + 1, u, u} b RY' RZ hZb).1 := by
  subst hX hY' hZa
  let rX := restrictScalarsEqToHomSelfIso.{u, u + 1, u, u + 1} (f.op ⋙ R) rfl
  let rY := restrictScalarsEqToHomSelfIso.{u, u + 1, u, u + 1} (g.op ⋙ R) rfl
  let rZ := restrictScalarsEqToHomSelfIso.{u, u + 1, u, u + 1} (a.op ⋙ f.op ⋙ R) rfl
  exact Functor.isoWhiskerRight (moduleDirectImageDataIso.{u, u + 1, u, u} f R _ rfl) _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight rX _ ≪≫ Functor.leftUnitor _) _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ rY ≪≫ Functor.rightUnitor _) ≪≫
    moduleSectionsBaseChangeIso.{u, u + 1, u, u + 1, u, u + 1, u, u + 1, u, u}
      a b f g w R ha hRw ≪≫
    Functor.isoWhiskerLeft _ (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight rZ.symm _) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (moduleDirectImageDataIso.{u, u + 1, u, u} b _ _ hZb).symm)

end Presheaf

section Sheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒵 𝒳 𝒴' 𝒴 : Type (u + 1)} [Category.{u} 𝒵] [Category.{u} 𝒳] [Category.{u} 𝒴']
  [Category.{u} 𝒴]
  (pZ : 𝒵 ⥤ BigFppfOver B S hS) (pX : 𝒳 ⥤ BigFppfOver B S hS)
  (pY' : 𝒴' ⥤ BigFppfOver B S hS) (pY : 𝒴 ⥤ BigFppfOver B S hS)
  (hpZ : pZ.IsFiberedInGroupoids) (hpX : pX.IsFiberedInGroupoids)
  (hpY' : pY'.IsFiberedInGroupoids) (hpY : pY.IsFiberedInGroupoids)
  (a : 𝒵 ⥤ 𝒳) (b : 𝒵 ⥤ 𝒴') (f : 𝒳 ⥤ 𝒴) (g : 𝒴' ⥤ 𝒴)
  (ha : a ⋙ pX = pZ) (hb : b ⋙ pY' = pZ) (hf : f ⋙ pY = pX) (hg : g ⋙ pY = pY')
  (w : TwoSquare a b f g)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

include ha hb hf hg in
/-- The two composites around the square agree over the base. -/
theorem comp_comp_eq_of_square : a ⋙ f ⋙ pY = b ⋙ g ⋙ pY := by
  rw [hf, ha, hg, hb]

/-- A 2-cell of the square is **vertical** when its image in the base is an identity. -/
def TwoSquareIsVertical : Prop :=
  ∀ z : 𝒵, pY.map (w.natTrans.app z) =
    eqToHom (show pY.obj (f.obj (a.obj z)) = pY.obj (g.obj (b.obj z)) from
      Functor.congr_obj (comp_comp_eq_of_square B S hS pZ pX pY' pY a b f g ha hb hf hg) z)

/-- The direct image of presheaves of modules of **Stacks 06WD** underlying the one of sheaves
of modules is the functor of compatible sections, up to a transport of scalars. -/
noncomputable def moduleFunctorialityPushforwardIso :
    (moduleFunctoriality.{u, u + 1, u, u} B S hS pX pY hpX hpY f hf).pushforward ≅
      (moduleDirectImageData.{u, u + 1, u, u} f (ringStructureSheafCore B S hS pY hpY τ hτ).obj
        (ringStructureSheafCore B S hS pX hpX τ hτ).obj
        (ringStructureSheafCore_obj_eq B S hS pX pY hpX hpY f hf τ hτ)).1 :=
  Iso.refl _

variable [w.GuitartExact]

/-- **Base change for the direct image of sheaves of modules along a Guitart exact square**
(the degree-zero part of **Stacks 075H**): for a Guitart exact square of categories fibred in
groupoids strictly over the base whose 2-cell is vertical, `f_* ⋙ g⁻¹ ≅ a⁻¹ ⋙ b_*` on sheaves
of modules over the structure sheaves of **Stacks 06TV**. -/
noncomputable def moduleSheafGuitartBaseChangeIso
    (hw : TwoSquareIsVertical B S hS pZ pX pY' pY a b f g ha hb hf hg w) :
    moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS pX pY hpX hpY f hf τ hτ ⋙
        modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS pY' pY hpY' hpY g hg τ hτ ≅
      modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS pZ pX hpZ hpX a ha τ hτ ⋙
        moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS pZ pY' hpZ hpY' b hb τ hτ := by
  let R := (ringStructureSheafCore B S hS pY hpY τ hτ).obj
  have hring : b.op ⋙ g.op ⋙ R = a.op ⋙ f.op ⋙ R := by
    change (b ⋙ g ⋙ pY).op ⋙ (BigFppfOver.structureSheaf B S hS).obj =
      (a ⋙ f ⋙ pY).op ⋙ (BigFppfOver.structureSheaf B S hS).obj
    rw [comp_comp_eq_of_square B S hS pZ pX pY' pY a b f g ha hb hf hg]
  have hRw : ∀ z : 𝒵ᵒᵖ, R.map (w.op.natTrans.app z) = eqToHom (Functor.congr_obj hring z) := by
    intro z
    change (BigFppfOver.structureSheaf B S hS).obj.map (pY.map (w.natTrans.app z.unop)).op = _
    rw [hw z.unop, eqToHom_op, eqToHom_map]
    rfl
  let P := modulePresheafGuitartBaseChangeIso a b f g w R _ _ _
      (ringStructureSheafCore_obj_eq B S hS pX pY hpX hpY f hf τ hτ)
      (ringStructureSheafCore_obj_eq B S hS pY' pY hpY' hpY g hg τ hτ)
      (ringStructureSheafCore_obj_eq B S hS pZ pX hpZ hpX a ha τ hτ)
      (ringStructureSheafCore_obj_eq B S hS pZ pY' hpZ hpY' b hb τ hτ) hring hRw
  let FX := SheafOfModules.forget.{u + 1} (ringStructureSheafCore B S hS pX hpX τ hτ)
  let FY := SheafOfModules.forget.{u + 1} (ringStructureSheafCore B S hS pY hpY τ hτ)
  let FY' := SheafOfModules.forget.{u + 1} (ringStructureSheafCore B S hS pY' hpY' τ hτ)
  let FZ := SheafOfModules.forget.{u + 1} (ringStructureSheafCore B S hS pZ hpZ τ hτ)
  let Pf := moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS pX pY hpX hpY f hf τ hτ
  let Pb := moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS pZ pY' hpZ hpY' b hb τ hτ
  let Lg := modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS pY' pY hpY' hpY g hg τ hτ
  let La := modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS pZ pX hpZ hpX a ha τ hτ
  let e₁ : (Pf ⋙ Lg) ⋙ FY' ≅ FX ⋙ (moduleDirectImageData.{u, u + 1, u, u} f R
      (ringStructureSheafCore B S hS pX hpX τ hτ).obj
      (ringStructureSheafCore_obj_eq B S hS pX pY hpX hpY f hf τ hτ)).1 ⋙
        PresheafOfModules.pushforward₀ g R ⋙ PresheafOfModules.restrictScalars (eqToHom
          (ringStructureSheafCore_obj_eq B S hS pY' pY hpY' hpY g hg τ hτ)) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft Pf
        (modulePullbackForgetIso.{u, u + 1, u, u + 1, u + 1, u} B S hS pY' pY hpY' hpY g hg τ
          hτ) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((moduleSheafFunctoriality.{u, u + 1, u, u, u + 1, u} B S hS pX pY hpX hpY f hf τ
          hτ).pushforward_iso ≪≫
          Functor.isoWhiskerLeft FX (moduleFunctorialityPushforwardIso B S hS pX pY hpX hpY f hf
            τ hτ)) _ ≪≫
      Functor.associator _ _ _
  let e₂ : (La ⋙ Pb) ⋙ FY' ≅ FX ⋙ PresheafOfModules.pushforward₀ a
      (ringStructureSheafCore B S hS pX hpX τ hτ).obj ⋙
        PresheafOfModules.restrictScalars (eqToHom
          (ringStructureSheafCore_obj_eq B S hS pZ pX hpZ hpX a ha τ hτ)) ⋙
        (moduleDirectImageData.{u, u + 1, u, u} b
          (ringStructureSheafCore B S hS pY' hpY' τ hτ).obj
          (ringStructureSheafCore B S hS pZ hpZ τ hτ).obj
          (ringStructureSheafCore_obj_eq B S hS pZ pY' hpZ hpY' b hb τ hτ)).1 :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft La
        ((moduleSheafFunctoriality.{u, u + 1, u, u, u + 1, u} B S hS pZ pY' hpZ hpY' b hb τ
          hτ).pushforward_iso ≪≫
          Functor.isoWhiskerLeft FZ (moduleFunctorialityPushforwardIso B S hS pZ pY' hpZ hpY' b hb
            τ hτ)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (modulePullbackForgetIso.{u, u + 1, u, u + 1, u + 1, u} B S hS pZ pX hpZ hpX a ha τ hτ) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft FX (Functor.associator _ _ _)
  exact ((SheafOfModules.fullyFaithfulForget _).whiskeringRight _).preimageIso
    (e₁ ≪≫ Functor.isoWhiskerLeft FX P ≪≫ e₂.symm)

variable [HasSheafify (associatedTopology B S hS pZ τ) AddCommGrpCat.{u + 1}]
  [(associatedTopology B S hS pZ τ).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasSheafify (associatedTopology B S hS pX τ) AddCommGrpCat.{u + 1}]
  [(associatedTopology B S hS pX τ).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasSheafify (associatedTopology B S hS pY' τ) AddCommGrpCat.{u + 1}]
  [(associatedTopology B S hS pY' τ).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasSheafify (associatedTopology B S hS pY τ) AddCommGrpCat.{u + 1}]
  [(associatedTopology B S hS pY τ).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

omit [HasSheafify (associatedTopology B S hS pY' τ) AddCommGrpCat.{u + 1}]
  [(associatedTopology B S hS pY' τ).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasSheafify (associatedTopology B S hS pY τ) AddCommGrpCat.{u + 1}]
  [(associatedTopology B S hS pY τ).WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- The inverse image of sheaves of modules preserves homology. -/
theorem preservesHomology_modulePullback_succ :
    (modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS pY' pY hpY' hpY g hg τ
      hτ).PreservesHomology := by
  have : PreservesFiniteLimits
      (modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS pY' pY hpY' hpY g hg τ hτ) :=
    preservesFiniteLimits_modulePullback' B S hS pY' pY hpY' hpY g hg τ hτ
  have : PreservesColimits
      (modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS pY' pY hpY' hpY g hg τ hτ) :=
    (moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u}
      B S hS pY' pY hpY' hpY g hg τ hτ).leftAdjoint_preservesColimits
  infer_instance

/-- **Stacks 06X2 (2)** for a faithful 1-morphism out of a category with equalizers: the inverse
image of an injective sheaf of modules is injective. -/
theorem injective_modulePullback_obj_succ [a.Faithful] [HasEqualizers 𝒵]
    (I : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS pX hpX τ hτ)) (hI : Injective I) :
    Injective ((modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS pZ pX hpZ hpX a ha τ
      hτ).obj I) := by
  subst ha
  let := hpZ.isFibered
  let := hpX.isFibered
  let := ((hpX.isFibredOneMorphism
    (show a ⋙ pX = a ⋙ pX from rfl)).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
  exact injective_sheafOfModules_pushforward_obj B S hS (a ⋙ pX) pX a τ hpZ hpX rfl hτ
    (PresheafOfModules.isRightAdjoint_pushforward_of_univLE.{u + 1} _) I

/-- **Base change for the higher direct images of sheaves of modules along a Guitart exact
square** (**Stacks 075H** at module coefficients, for a Guitart exact square with a faithful
side `a` whose source has equalizers): `g⁻¹ Rⁱf_* ℱ ≅ Rⁱb_* a⁻¹ℱ`. -/
noncomputable def moduleHigherDirectImageGuitartBaseChangeIso [a.Faithful] [HasEqualizers 𝒵]
    (hw : TwoSquareIsVertical B S hS pZ pX pY' pY a b f g ha hb hf hg w) (i : ℕ)
    (F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS pX hpX τ hτ)) :
    (modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS pY' pY hpY' hpY g hg τ hτ).obj
        ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS pX pY hpX hpY f hf τ hτ
          i).obj F) ≅
      (moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS pZ pY' hpZ hpY' b hb τ hτ
          i).obj
        ((modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS pZ pX hpZ hpX a ha τ hτ).obj F) := by
  letI : EnoughInjectives (SheafOfModules.{u + 1} (ringStructureSheafCore B S hS pX hpX τ hτ)) :=
    enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS pX hpX τ hτ
  letI : EnoughInjectives (SheafOfModules.{u + 1} (ringStructureSheafCore B S hS pZ hpZ τ hτ)) :=
    enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS pZ hpZ τ hτ
  have := preservesHomology_modulePullback_succ B S hS pY' pY hpY' hpY g hg τ hτ
  have := preservesHomology_modulePullback_succ B S hS pZ pX hpZ hpX a ha τ hτ
  let Pf := moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS pX pY hpX hpY f hf τ hτ
  let Pb := moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS pZ pY' hpZ hpY' b hb τ hτ
  let Lg := modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS pY' pY hpY' hpY g hg τ hτ
  let La := modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS pZ pX hpZ hpX a ha τ hτ
  exact ((Functor.rightDerivedCompIso Pf Lg i).app F).symm ≪≫
    (Functor.rightDerivedIsoOfNatIso
      (moduleSheafGuitartBaseChangeIso B S hS pZ pX pY' pY hpZ hpX hpY' hpY a b f g ha hb hf hg w
        τ hτ hw) i).app F ≪≫
    (Functor.rightDerivedObjIsoOfComp La Pb (La ⋙ Pb)
      (fun I hI => injective_modulePullback_obj_succ B S hS pZ pX hpZ hpX a ha τ hτ I hI)
      (Iso.refl _) F i).symm

end Sheaf

end AlgebraicGeometry.Stack

end
