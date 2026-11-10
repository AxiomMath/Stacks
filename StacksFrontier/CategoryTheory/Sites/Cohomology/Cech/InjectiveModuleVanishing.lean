module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.DegreeZeroAndSheafCondition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.IntegralComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.IntegralComplexFlatness
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Čech cohomology of an injective sheaf of modules

Let `X` be a ringed site and let `E` be a family of morphisms `U i ⟶ U` in its underlying
category. This file computes the Čech cohomology of a sheaf of `O_X`-modules `I` with respect
to `E`, in the two cases of the displayed formula of the source: in degree zero it is the
module of sections of `I` over `U`, provided `E` covers `U`; in positive degrees it vanishes
as soon as `I` is injective, for any family `E` whatsoever.

Degree zero is the sheaf condition: the degree-zero Čech cohomology of a presheaf is its group
of matching families, and restriction from sections over `U` to matching families is bijective
exactly because `I` is a sheaf and `E` generates a covering sieve.

Positive degrees go through the integral Čech complex `integralCechComplex E`, whose terms are
free abelian presheaves. Tensoring it with the structure presheaf gives a complex of presheaves
of modules which is exact in positive degrees, and applying `Hom(-, I)` to that complex
preserves exactness because `I` is injective as a presheaf of modules — exact sheafification
transports injectivity from module sheaves to module presheaves. Finally that `Hom`-complex is
identified with the Čech complex of `I`, by the corepresentability of evaluation by free
abelian presheaves.

## Main results

* `Stacks.CechSite.moduleCechCohomology_zero_iso`: degree-zero Čech cohomology of a sheaf
  of modules for a covering family is its group of sections over the covered object.
* `Stacks.CechSite.injective_moduleCechCohomology_isZero`: the positive-degree Čech
  cohomology of an injective sheaf of modules vanishes.

## Implementation notes

A covering is represented by a zero-truncated hypercover whose generated sieve belongs to the
topology. The Čech complex is formed from the underlying presheaf of additive groups of the
sheaf of modules; vanishing is expressed categorically by `IsZero`.

The site objects, the site morphisms, the values of the structure sheaf, the coefficient size
and the covering family all have independent universe parameters. The proof in positive degrees
needs the free Čech resolution and the injective coefficient object in one category of
presheaves of modules, so it is run after enlarging the hom-universe of the site with
`ULiftHom`; `modulePresheafULiftEquiv` and `cechULiftHomIso` transport the conclusion back.
Products of the required size are assumed rather than derived, as for Tag 03AW.

## References

* [The Stacks Project, Tag 03FC](https://stacks.math.columbia.edu/tag/03FC)
-/

@[expose] public section

universe a t u v w b c

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

-- Transporting a family along `ULiftHom.up` and transporting the fibre products back along
-- `ULiftHom.down` are the identity only after unfolding, and the terms and differentials of
-- a Čech complex are products and alternating sums of coface maps only after unfolding the
-- functors that assemble them. Making those unfoldings visible is what lets the assumed
-- products be found, and the rewrites below stay type-correct, for every spelling of the
-- index type that occurs; without it the comparison of the two sites needs
-- `backward.isDefEq.respectTransparency`.
attribute [local implicit_reducible] CategoryTheory.PreZeroHypercover.map
  cechFormalCoproduct cechFormalCoproductMap
  CategoryTheory.ULiftHom.up CategoryTheory.ULiftHom.down
  CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor
  CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
  CategoryTheory.Limits.FormalCoproduct.evalOp
  AlgebraicTopology.alternatingCofaceMapComplex
  AlgebraicTopology.AlternatingCofaceMapComplex.obj

private theorem uliftFamily_hasProducts
    {C : Type u} [Category.{v} C] {U : C} (E : PreZeroHypercover.{t} U)
    [hOriginalProducts : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun j ↦ Over.mk (E.f (i j)))] :
    ∀ (n : ℕ) (i : Fin (n + 1) → (E.map (ULiftHom.up.{v, u, b} (C := C))).I₀),
      HasProduct (fun j ↦ Over.mk ((E.map (ULiftHom.up.{v, u, b} (C := C))).f (i j))) := by
  intro n i
  let F : Over U ⥤ Over ((ULiftHom.up.{v, u, b} (C := C)).obj U) :=
    Over.post (ULiftHom.up.{v, u, b} (C := C))
  let : HasProduct (fun j : Fin (n + 1) ↦ Over.mk (E.f (i j))) := hOriginalProducts n i
  let D := Discrete.functor (fun j : Fin (n + 1) ↦ Over.mk (E.f (i j)))
  let : (ULiftHom.up.{v, u, b} (C := C)).IsEquivalence :=
    (ULiftHom.equiv (C := C)).isEquivalence_functor
  let : F.IsEquivalence := inferInstance
  let c := F.mapCone (limit.cone D)
  have hc : IsLimit c := isLimitOfPreserves F (limit.isLimit D)
  let D' := Discrete.functor (fun j : Fin (n + 1) ↦
    Over.mk ((E.map (ULiftHom.up.{v, u, b} (C := C))).f (i j)))
  have hD : D ⋙ F = D' := CategoryTheory.Functor.ext
    (by intro j; cases j; rfl)
    (by
      intro j k f
      cases j with
      | mk a =>
        cases k with
        | mk b =>
          cases f with
          | mk h =>
            cases h
            simp [D, D', F])
  change HasLimit D'
  rw [← hD]
  exact ⟨⟨c, hc⟩⟩

/-- Lifting an abelian group into a universe that already contains the lift level changes
nothing. -/
private noncomputable def largeAddCommGrpUliftIso :
    AddCommGrpCat.uliftFunctor.{w, max w b} ≅
      𝟭 (AddCommGrpCat.{max w b}) :=
  NatIso.ofComponents (fun A => (AddEquiv.ulift).toAddCommGrpIso) (by
    intro A B f
    apply AddCommGrpCat.hom_ext
    ext x
    rfl)

/-- Objectwise, the same for presheaves of abelian groups. -/
private noncomputable def largePresheafUliftIso
    {C : Type u} [Category.{max w b} C]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max w b}) :
    F ⋙ AddCommGrpCat.uliftFunctor.{w, max w b} ≅ F :=
  NatIso.ofComponents (fun V => largeAddCommGrpUliftIso.{w, b}.app (F.obj V)) (by
    intro V W f
    apply AddCommGrpCat.hom_ext
    ext x
    rfl)

private theorem largePresheafUliftIso_inv_naturality
    {C : Type u} [Category.{max w b} C]
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{max w b}} (α : F ⟶ G) :
    α ≫ (largePresheafUliftIso.{u, w, b} G).inv =
      (largePresheafUliftIso.{u, w, b} F).inv ≫
        Functor.whiskerRight α AddCommGrpCat.uliftFunctor.{w, max w b} := by
  ext V x
  have h := largeAddCommGrpUliftIso.{w, b}.inv.naturality (α.app V)
  exact congrArg (fun f => f x) h

/-- Precomposition with an isomorphism of functors, as an isomorphism of hom-groups. -/
private noncomputable def precompIsoAddEquiv
    {A D : Type*} [Category A] [Category D] [Preadditive D]
    {F G H : A ⥤ D} (e : F ≅ G) :
    (F ⟶ H) ≃+ (G ⟶ H) where
  toFun f := e.inv ≫ f
  invFun f := e.hom ≫ f
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by ext X; simp

/-- The corepresentation of the underlying abelian presheaf by extension of scalars is
natural in the abelian presheaf. -/
private theorem extendScalarsPresheafHomAddEquiv_precomp
    {D : Type u} [Category.{v} D] {R : Dᵒᵖ ⥤ RingCat.{w}}
    {F G : Dᵒᵖ ⥤ AddCommGrpCat.{max w b}}
    (g : F ⟶ G)
    (M : PresheafOfModules.{max w b} R)
    (f : extendScalarsPresheaf R G ⟶ M) :
    g ≫ extendScalarsPresheafHomAddEquiv R G M f =
      extendScalarsPresheafHomAddEquiv R F M
        (extendScalarsPresheafMap R g ≫ f) := by
  ext V x
  change (f.app V) (1 ⊗ₜ[ℤ] g.app V x) =
    (f.app V) (1 ⊗ₜ[ℤ] g.app V x)
  rfl

private noncomputable def modulePresheafULiftEquiv
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{w}) :
    PresheafOfModules.{b} R ≌
      PresheafOfModules.{b} ((ULiftHom.down.{v, u, c} (C := C)).op ⋙ R) := by
  let up := ULiftHom.up.{v, u, c} (C := C)
  let down := ULiftHom.down.{v, u, c} (C := C)
  let F := PresheafOfModules.pushforward₀ down R
  let G := PresheafOfModules.pushforward₀ up (down.op ⋙ R)
  refine {
    functor := F
    inverse := G
    unitIso := NatIso.ofComponents (fun _ => PresheafOfModules.isoMk
      (fun _ => Iso.refl _) (by intros; ext x; rfl)) (by intros; ext X x; rfl)
    counitIso := NatIso.ofComponents (fun _ => PresheafOfModules.isoMk
      (fun _ => Iso.refl _) (by intros; ext x; rfl)) (by intros; ext X x; rfl) }

private noncomputable def homTensorIntegralCechComplexIsoRing
    {C : Type u} [Category.{max w b} C] {U : C}
    (E : PreZeroHypercover.{t} U)
    (R : Cᵒᵖ ⥤ RingCat.{w})
    [HasCoproducts.{t}
      (Cᵒᵖ ⥤ AddCommGrpCat.{max w b})]
    [HasProducts.{t} AddCommGrpCat.{max u (max w b)}]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun j ↦ Over.mk (E.f (i j)))]
    (M : PresheafOfModules.{max (max w b) w} R) :
    (((preadditiveYoneda.obj M).mapHomologicalComplex _).obj
      (integralCechComplexTensorRing.{t, w, max w b, u} E R).op) ≅
      (homComplexFunctor
      (integralCechComplex.{t, max w b, u,
        max w b} E)).obj M.presheaf := by
  let C₀ := integralCechComplex.{t, max w b, u,
    max w b} E
  let K := integralCechComplexTensorRing.{t, w, max w b, u} E R
  let e (n : ℕ) : AddCommGrpCat.of (K.X n ⟶ M) ≅
      AddCommGrpCat.of (C₀.X n ⟶ M.presheaf) := by
    let epre : (C₀.X n ⋙ AddCommGrpCat.uliftFunctor.{w,
        max w b} ⟶ M.presheaf) ≃+
        (C₀.X n ⟶ M.presheaf) :=
      precompIsoAddEquiv (largePresheafUliftIso.{u, w, b} (C₀.X n))
    change AddCommGrpCat.of
        (extendScalarsPresheaf R
          (C₀.X n ⋙ AddCommGrpCat.uliftFunctor.{w,
            max w b}) ⟶ M) ≅ _
    exact (extendScalarsPresheafHomAddEquiv R
        (C₀.X n ⋙ AddCommGrpCat.uliftFunctor.{w,
          max w b}) M).toAddCommGrpIso ≪≫
      AddEquiv.toAddCommGrpIso
        (X := AddCommGrpCat.of
          (C₀.X n ⋙ AddCommGrpCat.uliftFunctor.{w,
            max w b} ⟶ M.presheaf))
        (Y := AddCommGrpCat.of (C₀.X n ⟶ M.presheaf)) epre
  refine HomologicalComplex.Hom.isoOfComponents e ?_
  intro i j hij
  obtain rfl : i + 1 = j := hij
  apply AddCommGrpCat.hom_ext
  ext f
  change extendScalarsPresheaf R
      (C₀.X i ⋙ AddCommGrpCat.uliftFunctor.{w,
        max w b}) ⟶ M at f
  change C₀.d (i + 1) i ≫
      ((largePresheafUliftIso.{u, w, b} (C₀.X i)).inv ≫
        (extendScalarsPresheafHomAddEquiv R
          (C₀.X i ⋙ AddCommGrpCat.uliftFunctor.{w,
            max w b}) M) f) =
    (largePresheafUliftIso.{u, w, b} (C₀.X (i + 1))).inv ≫
      (extendScalarsPresheafHomAddEquiv R
        (C₀.X (i + 1) ⋙ AddCommGrpCat.uliftFunctor.{w,
          max w b}) M)
        (K.d (i + 1) i ≫ f)
  rw [← Category.assoc, largePresheafUliftIso_inv_naturality.{u, w, b} (C₀.d (i + 1) i)]
  rw [Category.assoc, extendScalarsPresheafHomAddEquiv_precomp.{u, max w b, w, b}
    (Functor.whiskerRight (C₀.d (i + 1) i) AddCommGrpCat.uliftFunctor.{w, max w b}) M f]
  rfl

private noncomputable def cechULiftHomIso
    {C : Type u} [Category.{v} C] {U : C} (E : PreZeroHypercover.{t} U)
    [hProducts : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun j ↦ Over.mk (E.f (i j)))]
    [hProducts' : ∀ (n : ℕ) (i : Fin (n + 1) →
      (E.map (ULiftHom.up.{v, u, max b t} (C := C))).I₀),
      HasProduct (fun j ↦ Over.mk
        ((E.map (ULiftHom.up.{v, u, max b t} (C := C))).f (i j)))]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max (max b t) v}) :
    (cechComplex
      (E.map (ULiftHom.up.{v, u, max b t} (C := C)))
      ((ULiftHom.down.{v, u, max b t} (C := C)).op ⋙ F)) ≅
      cechComplex E F := by
  let up := ULiftHom.up.{v, u, max b t} (C := C)
  let down := ULiftHom.down.{v, u, max b t} (C := C)
  let E' := E.map up
  let F' := down.op ⋙ F
  let downOver : Over (up.obj U) ⥤ Over U := Over.post (X := up.obj U) down
  letI : down.IsEquivalence := (ULiftHom.equiv (C := C)).symm.isEquivalence_functor
  letI : downOver.IsEquivalence :=
    (Over.postEquiv (X := up.obj U) (ULiftHom.equiv (C := C)).symm).isEquivalence_functor
  letI : ∀ (n : ℕ) (q : ToType (SimplexCategory.mk n) → E'.I₀),
      HasProduct (fun j => downOver.obj (Over.mk (E'.f (q j)))) := by
    intro n q
    change HasProduct (fun j : ToType (SimplexCategory.mk n) => Over.mk (E.f (q j)))
    exact hProducts n q
  letI : ∀ (n : ℕ) (q : ToType (SimplexCategory.mk n) → E.I₀),
      HasProduct (fun j => Over.mk (E.f (q j))) := fun n q => hProducts n q
  letI : ∀ (n : ℕ) (q : ToType (SimplexCategory.mk n) → E'.I₀),
      HasProduct (fun j => Over.mk (E'.f (q j))) := fun n q => hProducts' n q
  let termIso (n : ℕ) :
      (cechComplex E' F').X n ≅ (cechComplex E F).X n := by
    dsimp only [cechComplex, cechComplexFunctor,
      cechSimplicialObject, cechFormalCoproduct,
      FormalCoproduct.cochainComplexFunctor, FormalCoproduct.cosimplicialObjectFunctor,
      FormalCoproduct.evalOp, Functor.comp_obj, Functor.whiskeringLeft_obj_obj,
      Functor.op_obj]
    refine Pi.mapIso (fun i => ?_)
    let eP := PreservesProduct.iso downOver
      (fun j : ToType (SimplexCategory.mk n) => Over.mk (E'.f (i j)))
    let g : (∏ᶜ fun j : ToType (SimplexCategory.mk n) => Over.mk (E.f (i j))).left ⟶
        down.obj (∏ᶜ fun j : ToType (SimplexCategory.mk n) => Over.mk (E'.f (i j))).left :=
      eP.inv.left
    letI : IsIso g := inferInstanceAs (IsIso ((Over.forget U).map eP.inv))
    exact asIso (F.map g.op)
  let S := cechSimplicialObject E
  let S' := cechSimplicialObject E'
  have faceOver_natural (n : ℕ) (k : Fin (n + 2))
      (q : (cechFormalCoproduct E (ToType (SimplexCategory.mk (n + 1)))).I) :
      let δ := (SimplexCategory.δ k).op
      let q₀ := fun j : ToType (SimplexCategory.mk n) =>
        q ((SimplexCategory.Hom.toOrderHom (SimplexCategory.δ k)) j)
      ((PreservesProduct.iso downOver
          (fun j : ToType (SimplexCategory.mk (n + 1)) => Over.mk (E'.f (q j)))).inv ≫
        downOver.map ((S'.map δ).φ q)) =
      (S.map δ).φ q ≫ (PreservesProduct.iso downOver
        (fun j : ToType (SimplexCategory.mk n) => Over.mk (E'.f (q₀ j)))).inv := by
    intro δ q₀
    let : HasProduct (fun j : ToType (SimplexCategory.mk (n + 1)) => Over.mk (E.f (q j))) :=
      hProducts (n + 1) q
    let : HasProduct (fun j : ToType (SimplexCategory.mk n) => Over.mk (E.f (q₀ j))) :=
      hProducts n q₀
    let : HasProduct (fun j : ToType (SimplexCategory.mk (n + 1)) => Over.mk (E'.f (q j))) :=
      hProducts' (n + 1) q
    let : HasProduct (fun j : ToType (SimplexCategory.mk n) => Over.mk (E'.f (q₀ j))) :=
      hProducts' n q₀
    let eP₁ := PreservesProduct.iso downOver
      (fun j : ToType (SimplexCategory.mk (n + 1)) => Over.mk (E'.f (q j)))
    let eP₀ := PreservesProduct.iso downOver
      (fun j : ToType (SimplexCategory.mk n) => Over.mk (E'.f (q₀ j)))
    have hP₁hom : eP₁.hom = piComparison downOver
        (fun j : ToType (SimplexCategory.mk (n + 1)) => Over.mk (E'.f (q j))) := rfl
    have hP₀hom : eP₀.hom = piComparison downOver
        (fun j : ToType (SimplexCategory.mk n) => Over.mk (E'.f (q₀ j))) := rfl
    have hP₁inv : eP₁.inv = inv (piComparison downOver
        (fun j : ToType (SimplexCategory.mk (n + 1)) => Over.mk (E'.f (q j)))) := by
      calc
        eP₁.inv = inv eP₁.hom := IsIso.eq_inv_of_hom_inv_id eP₁.hom_inv_id
        _ = inv (piComparison downOver
            (fun j : ToType (SimplexCategory.mk (n + 1)) => Over.mk (E'.f (q j)))) :=
          IsIso.inv_eq_inv.mpr hP₁hom
    have hcomp :
        eP₁.inv ≫ downOver.map ((S'.map δ).φ q) ≫ eP₀.hom =
          ((S.map δ).φ q) := by
      apply Pi.hom_ext
      intro j
      change (eP₁.inv ≫ downOver.map ((S'.map δ).φ q) ≫ eP₀.hom) ≫
          Pi.π (fun a : ToType (SimplexCategory.mk n) =>
            downOver.obj (Over.mk (E'.f (q₀ a)))) j =
        ((S.map δ).φ q) ≫
          Pi.π (fun a : ToType (SimplexCategory.mk n) => Over.mk (E.f (q₀ a))) j
      let j' := (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ k)) j
      have hface' : ((S'.map δ).φ q) ≫
          Pi.π (fun a : ToType (SimplexCategory.mk n) => Over.mk (E'.f (q₀ a))) j =
          Pi.π (fun a : ToType (SimplexCategory.mk (n + 1)) => Over.mk (E'.f (q a))) j' := by
        dsimp [q₀, S', S, δ, cechSimplicialObject,
          cechFormalCoproductMap]
        simp only [Pi.lift_comp_π]
        simp [j']
      have hface : ((S.map δ).φ q) ≫
          Pi.π (fun a : ToType (SimplexCategory.mk n) => Over.mk (E.f (q₀ a))) j =
          Pi.π (fun a : ToType (SimplexCategory.mk (n + 1)) => Over.mk (E.f (q a))) j' := by
        dsimp [q₀, S, δ, cechSimplicialObject,
          cechFormalCoproductMap]
        simp only [Pi.lift_comp_π]
        simp [j']
      rw [hP₀hom, hP₁inv, Category.assoc, Category.assoc, piComparison_comp_π,
        ← Functor.map_comp, hface', inv_piComparison_comp_map_π, hface]
      rfl
    exact (Iso.eq_comp_inv eP₀).2 ((Category.assoc _ _ _).trans hcomp)
  refine HomologicalComplex.Hom.isoOfComponents termIso ?_
  intro i j hij
  obtain rfl : i + 1 = j := hij
  dsimp only [cechComplex, cechComplexFunctor,
    FormalCoproduct.cochainComplexFunctor, Functor.comp_obj,
    AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  simp only [CochainComplex.of_d,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  apply Pi.hom_ext
  intro q
  have hcat := faceOver_natural i k q
  -- Splitting `F.map (a ≫ b).left.op` is stated once, at a type written out explicitly, so
  -- that the composites of the two families of fibre products are matched up by elaboration
  -- rather than inside a rewrite.
  have key : ∀ {A₁ A₂ A₃ : Over U} (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃),
      F.map (Over.Hom.left (a ≫ b)).op =
        F.map (Over.Hom.left b).op ≫ F.map (Over.Hom.left a).op := by
    intro A₁ A₂ A₃ a b
    rw [Over.comp_left, op_comp, Functor.map_comp]
  have hcatF := congrArg (fun f => F.map (Over.Hom.left f).op) hcat
  have hmain := ((key _ _).symm.trans hcatF).trans (key _ _)
  simp only [Category.assoc]
  simp only [CosimplicialObject.δ,
    FormalCoproduct.cosimplicialObjectFunctor_obj_map]
  simp only [Functor.rightOp_obj, Functor.comp_obj, Functor.whiskeringLeft_obj_obj,
    Functor.op_obj, Opposite.unop_op]
  dsimp only [termIso, id]
  rw [Pi.lift_comp_π,
    Pi.mapIso_hom_π_assoc (g := fun y => F.obj (op ((Over.forget U).obj
      (((cechSimplicialObject E).obj (op (SimplexCategory.mk i))).obj y)))),
    Pi.mapIso_hom_π (g := fun y => F.obj (op ((Over.forget U).obj
      (((cechSimplicialObject E).obj (op (SimplexCategory.mk (i + 1)))).obj y))))]
  exact ((congrArg (fun z => Pi.π (fun y => F.obj (op (downOver.obj
        (∏ᶜ fun j => Over.mk (E'.f (y j)))).left))
      (((cechSimplicialObject E).map (SimplexCategory.δ k).op).f q) ≫ z) hmain.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ F.map (Over.Hom.left (PreservesProduct.iso downOver
          (fun j => Over.mk (E'.f (q j)))).inv).op)
        (Pi.lift_comp_π (fun y => Pi.π (fun x => F.obj (op (down.obj ((Over.forget (up.obj U)).obj
            (((cechSimplicialObject E').obj (op (SimplexCategory.mk i))).obj x)))))
              (((cechSimplicialObject E').map (SimplexCategory.δ k).op).f y) ≫
            ((Over.forget (up.obj U)).op ⋙ down.op ⋙ F).map
              (((cechSimplicialObject E').map (SimplexCategory.δ k).op).φ y).op) q).symm).trans
        (Category.assoc _ _ _))))

/-- Degree-zero Čech cohomology of a sheaf of modules over a sheaf of rings. -/
private theorem moduleCechCohomology_zero_iso_aux
    {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
    (O : Sheaf K RingCat.{w}) {U : C} (E : PreZeroHypercover.{t} U)
    [HasProducts.{t} AddCommGrpCat.{max a u v w t}]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (hE : E.sieve₀ ∈ K U) (I : SheafOfModules.{max a u v w t} O) :
    Nonempty
      (cechCohomology E ((SheafOfModules.toSheaf O).obj I).obj 0 ≅
        ((SheafOfModules.toSheaf O).obj I).obj.obj (op U)) := by
  let F := ((SheafOfModules.toSheaf O).obj I).obj
  let e₁ : F.obj (op U) ≃+ cechH0 E F :=
    AddEquiv.ofBijective (cechRestriction E F)
      (cechRestriction_bijective_of_isSheaf K F ((SheafOfModules.toSheaf O).obj I).property E hE)
  let e₂ : (cechCohomology E
      (A := AddCommGrpCat.{max a u v w t}) F 0 : Type (max a u v w t)) ≃+
      cechH0 E F :=
    cechCohomologyZeroEquiv E F
  exact ⟨(e₂.trans e₁.symm).toAddCommGrpIso⟩

/-- The positive-degree Čech cohomology of an injective sheaf of modules over a sheaf of rings
vanishes. -/
private theorem injective_moduleCechCohomology_isZero_aux
    {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
    (O : Sheaf K RingCat.{w}) {U : C} (E : PreZeroHypercover.{t} U)
    [HasProducts.{t} AddCommGrpCat.{max a u v w t}]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (I : SheafOfModules.{max a u v w t} O) [hI : Injective I] (p : ℕ) (hp : 0 < p) :
    IsZero
      (cechCohomology E ((SheafOfModules.toSheaf O).obj I).obj p) := by
  let up := ULiftHom.up.{v, u, max a u v w t} (C := C)
  let down := ULiftHom.down.{v, u, max a u v w t} (C := C)
  let E' : PreZeroHypercover.{t} (up.obj U) := E.map up
  let R : Cᵒᵖ ⥤ RingCat.{w} := O.obj
  let R' : (ULiftHom.{max a u v w t, u} C)ᵒᵖ ⥤ RingCat.{w} := down.op ⋙ R
  let M₀ : PresheafOfModules.{max a u v w t} R :=
    (SheafOfModules.forget O).obj I
  let eMod : PresheafOfModules.{max a u v w t} R ≌
      PresheafOfModules.{max a u v w t} (down.op ⋙ R) := modulePresheafULiftEquiv R
  let M' : PresheafOfModules.{max a u v w t} R' := eMod.functor.obj M₀
  let : eMod.functor.IsEquivalence := eMod.isEquivalence_functor
  have : HasSheafify K AddCommGrpCat.{max a u v w t} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max a u v w t, v, u} K
  have : K.WEqualsLocallyBijective AddCommGrpCat.{max a u v w t} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max a u v w t, u, v}
      K
  have : Injective M₀ := ModuleSheafCohomology.injective_forget_obj _ I
  have : Injective M' := Functor.injective_obj eMod.functor M₀
  let : ∀ (n : ℕ)
      (i : Fin (n + 1) → E'.I₀),
      HasProduct (fun j ↦ Over.mk (E'.f (i j))) := uliftFamily_hasProducts E
  let T := integralCechComplexTensorRing E' R'
  have hK : T.ExactAt p := (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    (integralCechComplexTensorRing_homology_isZero E' R' p hp)
  have hYonedaEpi : (preadditiveYoneda.obj M').PreservesEpimorphisms :=
    (Injective.injective_iff_preservesEpimorphisms_preadditiveYoneda_obj M').1 inferInstance
  have hYonedaHomology : (preadditiveYoneda.obj M').PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  let := hYonedaEpi
  let := hYonedaHomology
  have hHom :
      (((preadditiveYoneda.obj M').mapHomologicalComplex _).obj T.op).ExactAt p :=
    ShortComplex.Exact.map hK.op (preadditiveYoneda.obj M')
  have hTensorIso := homTensorIntegralCechComplexIsoRing.{t, u, w, max a u v w t} E' R' M'
  have hCechHomIso :=
    (homIntegralCechComplexIso.{t, max (max a u v w t) v, u,
      max (max a u v w t) v} E').app M'.presheaf
  have hLift := hHom.of_iso (hTensorIso ≪≫ hCechHomIso)
  let η : M'.presheaf ≅ M'.presheaf ⋙
      AddCommGrpCat.uliftFunctor.{u, max (max a u v w t) v} :=
    NatIso.ofComponents (fun _ => AddEquiv.ulift.symm.toAddCommGrpIso) (by
      intro V W f
      ext x
      rfl)
  have hLift' :
      (cechComplex E'
        (M'.presheaf ⋙
          AddCommGrpCat.uliftFunctor.{u, max (max a u v w t) v})).ExactAt p := by
    change ((liftedCechComplexFunctor E').obj M'.presheaf).ExactAt p
    exact hLift
  have hCechLift : (cechComplex E' M'.presheaf).ExactAt p :=
    hLift'.of_iso ((cechComplexFunctor E').mapIso η).symm
  let F := ((SheafOfModules.toSheaf O).obj I).obj
  let eM : M'.presheaf ≅ down.op ⋙ F :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro V W f
      rfl)
  exact (hCechLift.of_iso ((cechComplexFunctor E').mapIso eM ≪≫
    cechULiftHomIso.{t, u, v, max a u v w t} E F)).isZero_homology

variable (X : AlgebraicGeometry.RingedSite.{u, v, w}) {U : X.C}
  (E : PreZeroHypercover.{t} U)
  [HasProducts.{t} AddCommGrpCat.{max a u v w t}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  (hE : E.sieve₀ ∈ X.J U)
  (I : SheafOfModules.{max a u v w t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  [hI : Injective I]

include hE
omit hI

/-- **Stacks Project, Tag 03FC (degree zero).** Degree-zero Čech cohomology of a sheaf of
modules for a covering is its underlying additive group of sections over the covered object. -/
@[stacks 03FC "degree zero"]
public theorem moduleCechCohomology_zero_iso :
    Nonempty
      (cechCohomology E
          ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj I).obj 0 ≅
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj I).obj.obj
          (op U)) := by
  exact moduleCechCohomology_zero_iso_aux.{a, t, u, v, w} X.J _ E hE I

include hI
omit hE

/-- **Stacks Project, Tag 03FC (positive degrees).** The positive-degree Čech cohomology of
an injective sheaf of modules vanishes for every family of morphisms. -/
@[stacks 03FC "positive degrees"]
public theorem injective_moduleCechCohomology_isZero (p : ℕ) (hp : 0 < p) :
    IsZero
      (cechCohomology E
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj I).obj p) := by
  exact injective_moduleCechCohomology_isZero_aux.{a, t, u, v, w} X.J _ E I p hp

end Stacks.CechSite

/-! ### Coefficients in a sheaf of rings, not assumed commutative

The two computations above hold verbatim for a site `(C, K)` with a sheaf of rings
`O : Sheaf K RingCat`, not assumed commutative: the integral Čech complex is tensored with the
structure presheaf over `ℤ`, which is central in every ring, and the only property of
extension of scalars the exactness argument uses is additivity
(`Stacks.CechSite.integralCechComplexTensorRing_homology_isZero`). A ringed site is the special
case `O = Stacks.SheafOfModules.Tensor.ringSheaf X.O`. -/

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

-- Transporting a family along `ULiftHom.up` and transporting the fibre products back along
-- `ULiftHom.down` are the identity only after unfolding, and the terms and differentials of
-- a Čech complex are products and alternating sums of coface maps only after unfolding the
-- functors that assemble them. Making those unfoldings visible is what lets the assumed
-- products be found, and the rewrites below stay type-correct, for every spelling of the
-- index type that occurs; without it the comparison of the two sites needs
-- `backward.isDefEq.respectTransparency`.
attribute [local implicit_reducible] CategoryTheory.PreZeroHypercover.map
  cechFormalCoproduct cechFormalCoproductMap
  CategoryTheory.ULiftHom.up CategoryTheory.ULiftHom.down
  CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor
  CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
  CategoryTheory.Limits.FormalCoproduct.evalOp
  AlgebraicTopology.alternatingCofaceMapComplex
  AlgebraicTopology.AlternatingCofaceMapComplex.obj

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
  (O : Sheaf K RingCat.{w}) {U : C}
  (E : PreZeroHypercover.{t} U)
  [HasProducts.{t} AddCommGrpCat.{max a u v w t}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  (hE : E.sieve₀ ∈ K U)
  (I : SheafOfModules.{max a u v w t} O) [hI : Injective I]

include hE
omit hI

/-- **Stacks Project, Tag 03FC (degree zero).** Degree-zero Čech cohomology of a sheaf of
modules for a covering is its underlying additive group of sections over the covered object. -/
@[stacks 03FC "degree zero"]
public theorem moduleCechCohomology_zero_iso_sheafOfRings :
    Nonempty
      (cechCohomology E ((SheafOfModules.toSheaf O).obj I).obj 0 ≅
        ((SheafOfModules.toSheaf O).obj I).obj.obj (op U)) := by
  exact moduleCechCohomology_zero_iso_aux.{a, t, u, v, w} K O E hE I

include hI
omit hE

/-- **Stacks Project, Tag 03FC (positive degrees).** The positive-degree Čech cohomology of
an injective sheaf of modules vanishes for every family of morphisms. -/
@[stacks 03FC "positive degrees"]
public theorem injective_moduleCechCohomology_isZero_sheafOfRings (p : ℕ) (hp : 0 < p) :
    IsZero
      (cechCohomology E ((SheafOfModules.toSheaf O).obj I).obj p) := by
  exact injective_moduleCechCohomology_isZero_aux.{a, t, u, v, w} K O E I p hp

end Stacks.CechSite
