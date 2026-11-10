module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModuleHigherDirectImageBaseChange

/-!
# The direct image of modules at an object with an initial chart

Let `F : 𝒵 ⥤ 𝒲` be a 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` and
`N` a sheaf of modules on `𝒵`. The direct image `F_* N` of Stacks 06WE is, on underlying abelian
presheaves, the right Kan extension of `N` along `F.op`; so its value at an object `z` of `𝒲` is
the limit of the values of `N` over the structured arrows `z ⟶ F(x)`, and when that category has
an initial object `A` it is the value of `N` at `A`. This file records that identification in a
form with explicit maps (restriction along `A`, then the counit of 06WE), and its consequence for
a 2-cartesian square: the value at `y` of the direct image along `f` is the value of the module at
the first projection of a terminal object of the fibre of `f` over the chart of `y`
(through Stacks 075H in degree zero).

## Main results

* `AlgebraicGeometry.Stack.isIso_moduleSheafPushforwardEvaluation`: at an initial structured
  arrow the evaluation of the direct image is an isomorphism.
* `AlgebraicGeometry.Stack.isInitialStructuredArrowOfIsTerminal`: initial charts from terminal
  objects.
* `AlgebraicGeometry.Stack.moduleSheafPushforwardEvaluationIsoOfTerminal` and its naturality:
  the direct image at `y` as the sections at a terminal object of the fibre.
* `AlgebraicGeometry.Stack.liftFunctorTerminalIso`: the chart of an object sends the terminal
  object to an object isomorphic to it.

## References

* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

namespace AlgebraicGeometry.Stack

universe u

section InitialChart

/-- A commuting square in the source of a functor into presheaves stays commuting after applying
the functor and evaluating at an object. -/
private theorem map_app_comp_comm {𝒞 : Type*} [Category 𝒞] {𝒟 : Type*} [Category 𝒟]
    {E : Type*} [Category E] (Φ : 𝒞 ⥤ 𝒟ᵒᵖ ⥤ E) {X₀ X₁ Y₀ Y₁ : 𝒞} {a : X₀ ⟶ X₁} {b : X₁ ⟶ Y₁}
    {c : X₀ ⟶ Y₀} {d : Y₀ ⟶ Y₁} (h : a ≫ b = c ≫ d) (T : 𝒟ᵒᵖ) :
    (Φ.map a).app T ≫ (Φ.map b).app T = (Φ.map c).app T ≫ (Φ.map d).app T := by
  rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← Φ.map_comp, ← Φ.map_comp, h]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒵 : Type (u + 1)} [Category.{u} 𝒵] {𝒲 : Type (u + 1)} [Category.{u} 𝒲]
  (p : 𝒵 ⥤ BigFppfOver B S hS) (q : 𝒲 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (F : 𝒵 ⥤ 𝒲) (hF : F ⋙ q = p)

attribute [local irreducible] ringStructureSheafCore

/-- **The value of the direct image at an object with an initial chart.** The direct image
`F_* N` of Stacks 06WE, evaluated at an object `z` of the target, maps to `N` evaluated at the
source of any structured arrow `A : z ⟶ F(x)`: restrict along `A`, then apply the counit
`F^* F_* N ⟶ N` at `x`. -/
abbrev moduleSheafPushforwardEvaluation
    (N : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    {z : 𝒲} (A : StructuredArrow (op z) F.op) :
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).obj
        ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
          B.topology le_rfl).obj N)).obj (op z) ⟶
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).obj N).obj A.right :=
  ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).obj
      ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
        B.topology le_rfl).obj N)).map A.hom ≫
    ((modulePullbackCompToPresheafIso.{u, u + 1, u, u + 1, u, u} B S hS p q hp hq F hF
        B.topology le_rfl).inv.app
        ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
          B.topology le_rfl).obj N) ≫
      (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
        ((moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
          B.topology le_rfl).counit.app N)).app A.right

/-- When the structured arrow is initial, the evaluation of the direct image is an
isomorphism: the direct image is the right Kan extension along `F.op`, whose value at `z` is the
limit over the structured arrows, attained at an initial one. -/
theorem isIso_moduleSheafPushforwardEvaluation
    (N : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    {z : 𝒲} (A : StructuredArrow (op z) F.op) (hA : IsInitial A) :
    IsIso (moduleSheafPushforwardEvaluation B S hS p q hp hq F hF N A) := by
  have h := congrArg (fun t => t.app N)
    (moduleSheafAdjunction_counit_realization B S hS p q hp hq F hF)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.ranAdjunction_counit, Functor.whiskeringLeft_obj_map] at h
  have key : moduleSheafPushforwardEvaluation B S hS p q hp hq F hF N A =
      ((moduleSheafPushforwardCompToPresheafIso.{u, u + 1, u, u + 1, u, u}
          B S hS p q hp hq F hF B.topology le_rfl).hom.app N).app (op z) ≫
        (F.op.ranObjObjIsoLimit
          ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).obj N) (op z)).hom ≫
        limit.π _ A := by
    rw [Functor.ranObjObjIsoLimit_hom_π, moduleSheafPushforwardEvaluation, h]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    rw [← Category.assoc]
    exact congrArg (· ≫ _) ((((moduleSheafPushforwardCompToPresheafIso.{u, u + 1, u, u + 1, u, u}
          B S hS p q hp hq F hF B.topology le_rfl).hom.app N)).naturality A.hom)
  rw [key]
  have h₃ := IsLimit.isIso_π_app_of_isInitial (limit.isLimit (StructuredArrow.proj (op z) F.op ⋙
    (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).obj N)) A hA
  have h₁ : IsIso (((moduleSheafPushforwardCompToPresheafIso.{u, u + 1, u, u + 1, u, u}
      B S hS p q hp hq F hF B.topology le_rfl).hom.app N).app (op z)) :=
    (((moduleSheafPushforwardCompToPresheafIso.{u, u + 1, u, u + 1, u, u}
      B S hS p q hp hq F hF B.topology le_rfl).app N).app (op z)).isIso_hom
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ (@IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance h₃)

/-- The evaluation of the direct image at a structured arrow is natural in the module. -/
theorem moduleSheafPushforwardEvaluation_naturality
    {N N' : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp B.topology le_rfl)}
    (φ : N ⟶ N') {z : 𝒲} (A : StructuredArrow (op z) F.op) :
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
        ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
          B.topology le_rfl).map φ)).app (op z) ≫
      moduleSheafPushforwardEvaluation B S hS p q hp hq F hF N' A =
    moduleSheafPushforwardEvaluation B S hS p q hp hq F hF N A ≫
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map φ).app A.right := by
  have h1 := ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
    ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
      B.topology le_rfl).map φ)).naturality A.hom
  have h2 := map_app_comp_comm (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)
    ((moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
      B.topology le_rfl).counit.naturality φ) A.right
  simp only [moduleSheafPushforwardEvaluation, Category.assoc, NatTrans.comp_app]
  rw [← Category.assoc, ← h1, Category.assoc]
  congr 1

end InitialChart

section TerminalChart

variable {C : Type*} [Category C] {D : Type*} [Category D] (L : C ⥤ D)

/-- **A structured arrow out of a terminal object into the image of a terminal object is
initial.** If `z` is terminal in `D` and `t` terminal in `C`, the structured arrow
`op z ⟶ L.op (op t)` given by the unique arrow `L t ⟶ z` is an initial object of the category
of structured arrows from `op z` along `L.op`. -/
def isInitialStructuredArrowOfIsTerminal {z : D} (hz : IsTerminal z) {t : C}
    (ht : IsTerminal t) :
    IsInitial (StructuredArrow.mk (Y := op t) (hz.from (L.obj t)).op :
      StructuredArrow (op z) L.op) :=
  IsInitial.ofUniqueHom
    (fun B => StructuredArrow.homMk (ht.from B.right.unop).op
      (Quiver.Hom.unop_inj (hz.hom_ext _ _)))
    (fun _ _ => StructuredArrow.ext _ _ (Quiver.Hom.unop_inj (ht.hom_ext _ _)))

end TerminalChart

section FibreEvaluation

/-- Three commuting squares paste to a commuting rectangle. -/
private theorem comp₃_square {𝒞 : Type*} [Category 𝒞] {A₀ B₀ C₀ D₀ A₁ B₁ C₁ D₁ : 𝒞}
    (a₀ : A₀ ⟶ B₀) (b₀ : B₀ ⟶ C₀) (c₀ : C₀ ⟶ D₀) (a₁ : A₁ ⟶ B₁) (b₁ : B₁ ⟶ C₁) (c₁ : C₁ ⟶ D₁)
    (vA : A₀ ⟶ A₁) (vB : B₀ ⟶ B₁) (vC : C₀ ⟶ C₁) (vD : D₀ ⟶ D₁)
    (h₁ : vA ≫ a₁ = a₀ ≫ vB) (h₂ : vB ≫ b₁ = b₀ ≫ vC) (h₃ : vC ≫ c₁ = c₀ ≫ vD) :
    vA ≫ a₁ ≫ b₁ ≫ c₁ = (a₀ ≫ b₀ ≫ c₀) ≫ vD := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]
  simp

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] {𝒴' : Type (u + 1)} [Category.{u} 𝒴']
  {𝒴 : Type (u + 1)} [Category.{u} 𝒴]
  (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒴' : 𝒴' ⥤ BigFppfOver B S hS)
  (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS) (f : 𝒳 ⥤ 𝒴) (g : 𝒴' ⥤ 𝒴)
  (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
  (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴')

attribute [local irreducible] ringStructureSheafCore moduleSheafPushforward

variable {z₀ : 𝒴'} (hz₀ : IsTerminal z₀) {t : TwoFibreProductOver p𝒳 p𝒴' p𝒴 f g}
  (ht : IsTerminal t) {y : 𝒴} (c : g.obj z₀ ≅ y)

/-- The initial structured arrow from a terminal object `z₀` of `𝒴'` along the second
projection, at a terminal object `t` of the apex. -/
abbrev fibreTerminalChart : StructuredArrow (op z₀) (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).op :=
  StructuredArrow.mk (Y := op t) (hz₀.from ((TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).obj t)).op

/-- **The direct image at an object, as the sections over a terminal object of the fibre.** For
the canonical 2-cartesian square of `f` and `g`, an object `z₀` terminal in `𝒴'`, an object `t`
terminal in the apex `𝒴' ×_𝒴 𝒳`, and an isomorphism `g(z₀) ≅ y`, the value at `y` of the direct
image of a module `I` on `𝒳` is the value of `I` at the first projection of `t`: base change of
direct images (Stacks 075H in degree zero) followed by the evaluation of the direct image along
the second projection at its initial chart. Natural in `I`, see
`AlgebraicGeometry.Stack.moduleSheafPushforwardEvaluationIsoOfTerminal_naturality`. -/
noncomputable def moduleSheafPushforwardEvaluationIsoOfTerminal
    (I : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p𝒳 h𝒳 B.topology le_rfl)) :
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).obj
        ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc
          B.topology le_rfl).obj I)).obj (op y) ≅
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).obj I).obj (op t.x) :=
  ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).obj
      ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc
        B.topology le_rfl).obj I)).mapIso c.op ≪≫
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).mapIso
      ((fppfModuleDirectImageBaseChangeIso B S hS p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc).app I)).app
        (op z₀) ≪≫
    @asIso _ _ _ _ (moduleSheafPushforwardEvaluation B S hS _ p𝒴'
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq
      ((modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
        (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
        (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq
        B.topology le_rfl).obj I) (fibreTerminalChart B S hS p𝒳 p𝒴' p𝒴 f g hz₀ (t := t)))
      (isIso_moduleSheafPushforwardEvaluation B S hS _ p𝒴' _ h𝒴' _ _ _ _
        (isInitialStructuredArrowOfIsTerminal (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) hz₀ ht))

/-- The underlying morphism of
`AlgebraicGeometry.Stack.moduleSheafPushforwardEvaluationIsoOfTerminal`. -/
theorem moduleSheafPushforwardEvaluationIsoOfTerminal_hom
    (I : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p𝒳 h𝒳 B.topology le_rfl)) :
    (moduleSheafPushforwardEvaluationIsoOfTerminal B S hS p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
        hz₀ ht c I).hom =
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).obj
          ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc
            B.topology le_rfl).obj I)).map c.hom.op ≫
        ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
          ((fppfModuleDirectImageBaseChangeIso B S hS p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc).hom.app
            I)).app (op z₀) ≫
        moduleSheafPushforwardEvaluation B S hS _ p𝒴'
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
          (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq
          ((modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
            (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
            (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
            (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq
            B.topology le_rfl).obj I) (fibreTerminalChart B S hS p𝒳 p𝒴' p𝒴 f g hz₀ (t := t)) :=
  rfl

/-- Naturality of `AlgebraicGeometry.Stack.moduleSheafPushforwardEvaluationIsoOfTerminal` in the
module. -/
theorem moduleSheafPushforwardEvaluationIsoOfTerminal_naturality
    {I J : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p𝒳 h𝒳 B.topology le_rfl)}
    (φ : I ⟶ J) :
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
        ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc
          B.topology le_rfl).map φ)).app (op y) ≫
      (moduleSheafPushforwardEvaluationIsoOfTerminal B S hS p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
        hz₀ ht c J).hom =
    (moduleSheafPushforwardEvaluationIsoOfTerminal B S hS p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
        hz₀ ht c I).hom ≫
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map φ).app (op t.x) := by
  have n₁ : ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
      ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc
        B.topology le_rfl).map φ)).app (op y) ≫
        ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).obj
          ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc
            B.topology le_rfl).obj J)).map c.hom.op =
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).obj
          ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc
            B.topology le_rfl).obj I)).map c.hom.op ≫
        ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
          ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc
            B.topology le_rfl).map φ)).app (op (g.obj z₀)) :=
    (((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
      ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc
        B.topology le_rfl).map φ)).naturality c.hom.op).symm
  have n₂ : ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
        ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc
          B.topology le_rfl).map φ)).app (op (g.obj z₀)) ≫
        ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
          ((fppfModuleDirectImageBaseChangeIso B S hS p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc).hom.app
            J)).app (op z₀) =
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
          ((fppfModuleDirectImageBaseChangeIso B S hS p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc).hom.app
            I)).app (op z₀) ≫
        ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
          ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS _ p𝒴'
            (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
            (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq
            B.topology le_rfl).map
            ((modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
              (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
              (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
              (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq
              B.topology le_rfl).map φ))).app (op z₀) := by
    exact map_app_comp_comm (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)
      ((fppfModuleDirectImageBaseChangeIso B S hS p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc).hom.naturality
        φ) (op z₀)
  have n₃ := moduleSheafPushforwardEvaluation_naturality B S hS _ p𝒴'
    (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
    (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq
    ((modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
        (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
        (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq
        B.topology le_rfl).map φ) (fibreTerminalChart B S hS p𝒳 p𝒴' p𝒴 f g hz₀ (t := t))
  rw [moduleSheafPushforwardEvaluationIsoOfTerminal_hom,
    moduleSheafPushforwardEvaluationIsoOfTerminal_hom]
  exact comp₃_square _ _ _ _ _ _ _ _ _ _ n₁ n₂ n₃

end FibreEvaluation

section ChartIso

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒴 : Type (u + 1)} [Category.{u} 𝒴] (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids)

/-- The functor `Sch/V ⥤ 𝒴` of the chosen cartesian lifts of an object `y` over `V` sends the
terminal object `V = V` to an object isomorphic to `y`: the chosen lift lies over an identity. -/
noncomputable def liftFunctorTerminalIso (y : 𝒴) :
    (Functor.TwoYoneda.liftFunctor q hq (q.obj y) (Functor.Fiber.mk (a := y) rfl)).obj
        (Over.mk (𝟙 (q.obj y))) ≅ y :=
  haveI : q.IsFibered := hq.isFibered
  have hcart : q.IsStronglyCartesian (𝟙 (q.obj y))
      ((Functor.TwoYoneda.chosenLift q hq (q.obj y) (Functor.Fiber.mk (a := y) rfl)
        (Over.mk (𝟙 (q.obj y)))).φ : _ ⟶ y) :=
    (Functor.TwoYoneda.chosenLift q hq (q.obj y) (Functor.Fiber.mk (a := y) rfl)
      (Over.mk (𝟙 (q.obj y)))).isStronglyCartesian
  @asIso _ _ _ _ ((Functor.TwoYoneda.chosenLift q hq (q.obj y) (Functor.Fiber.mk (a := y) rfl)
      (Over.mk (𝟙 (q.obj y)))).φ : _ ⟶ y)
    (@Functor.IsStronglyCartesian.isIso_of_base_isIso _ _ _ _ q _ _ _ _ (𝟙 (q.obj y)) _ hcart _)

end ChartIso

end AlgebraicGeometry.Stack
