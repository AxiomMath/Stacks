module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.ArtinianLocalRing
public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction.Functor
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.ResidueField.Basic

import all StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction.Functor
import all StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction.Projection

/-!
# Essential surjectivity of the change-of-field functor

This is the third of the four parts of
`StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction`.
It shows that `Spec` sends the comparison fibre product `A ×_l k` to a pushout of schemes, compares
fibres of a fibred category over a commutative square, and proves that the canonical functor
`(𝓕_{𝒳,k,x₀})_{l/k} ⥤ 𝓕_{𝒳,l,x_{l,0}}` is essentially surjective when `𝒳` satisfies (RS).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Deformation.Artin.Site

attribute [local implicit_reducible] CategoryTheory.Over.post
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
  CategoryTheory.Limits.CategoricalPullback.π₁
  CategoryTheory.Limits.CategoricalPullback.π₂

section Equivalence

variable (T : Deformation.ChangeOfFieldsSituation.{u, u, u})
variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable (iΛ : Spec (.of T.Λ) ⟶ S)
variable (B : AlgebraicGeometry.BigFppfSite.{u}) (hS : B.Contains S)
variable {X : Type v} [Category.{w} X]
variable (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
variable (x₀ xₗ : X)
variable (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
variable (hxₗ : (p ⋙ Over.post B.inclusion).obj xₗ =
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ))
variable (η : xₗ ⟶ x₀)

/-- The category structure on the predeformation category of `x₀`. -/
local instance : Category.{max u w}
    (Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀).carrier :=
  (Deformation.Artin.predeformationCategory iΛ
    (p ⋙ Over.post B.inclusion) x₀ hx₀).category

/-- The category structure on the predeformation category of `x_{l,0}`. -/
local instance : Category.{max u w}
    (Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) xₗ hxₗ).carrier :=
  (Deformation.Artin.predeformationCategory iΛ
    (p ⋙ Over.post B.inclusion) xₗ hxₗ).category

/-- A fibre product of rings along a surjection is sent by `Spec` to a pushout of schemes. -/
private theorem isPushout_spec_of_isPullback
    {R A k l : CommRingCat}
    (r : R ⟶ A) (s : R ⟶ k) (f : A ⟶ l) (g : k ⟶ l)
    (hf : Function.Surjective f.hom) (h : IsPullback r s f g) :
    IsPushout (Spec.map f) (Spec.map g) (Spec.map r) (Spec.map s) :=
  Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective f g s r h.flip hf

private theorem comparisonRing_isPullback
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.l) :
    IsPullback (CommRingCat.ofHom (comparisonProjection T A))
      (CommRingCat.ofHom (Deformation.Artin.residueMap
        ((Deformation.comparisonFunctor T).functor.obj A)))
      (CommRingCat.ofHom (Deformation.residueMap T A))
      (CommRingCat.ofHom (algebraMap T.k T.l)) := by
  let e := (Deformation.comparisonFunctor T).pullbackEquiv A
  have h := IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit
    (CommRingCat.ofHom (Deformation.residueMap T A))
    (CommRingCat.ofHom (algebraMap T.k T.l)))
  apply h.of_iso e.toCommRingCatIso.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · ext x
    show x.val.1 = (e (e.symm x)).val.1
    exact congrArg (fun y => y.val.1) (e.apply_symm_apply x).symm
  · ext x
    show x.val.2 =
      Deformation.Artin.residueMap ((Deformation.comparisonFunctor T).functor.obj A) (e.symm x)
    rw [show (Deformation.Artin.residueMap ((Deformation.comparisonFunctor T).functor.obj A))
        (e.symm x) = (e (e.symm x)).val.2 from
      (Deformation.comparisonFunctor T).residue_snd A (e.symm x)]
    exact congrArg (fun y => y.val.2) (e.apply_symm_apply x).symm
  · simp
  · simp

private theorem comparisonSpec_isPushout
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.l) :
    IsPushout
      (Spec.map (CommRingCat.ofHom (Deformation.residueMap T A)))
      (Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
      (Spec.map (CommRingCat.ofHom (comparisonProjection T A)))
      (Spec.map (CommRingCat.ofHom
        (Deformation.Artin.residueMap ((Deformation.comparisonFunctor T).functor.obj A)))) := by
  refine isPushout_spec_of_isPullback _ _ _ _ ?_ (comparisonRing_isPullback T A)
  exact A.residueEquiv.surjective.comp (IsLocalRing.residue_surjective (R := A))

section FiberSquare

open Functor

variable {C : Type*} [Category C] {Y : Type*} [Category Y]
variable (q : Y ⥤ C) (c : q.ChoiceOfPullbacks)
variable {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W)
variable (i : V ⟶ Z) (j : W ⟶ Z) (w : f ≫ i = g ≫ j)

private theorem fiberSquareComparison_hom_ext
    [(Deformation.Artin.fiberSquareComparison q c f g i j w).Faithful]
    {a b : q.Fiber Z} {α β : a ⟶ b}
    (hi : c.map i a ≫ Fiber.fiberInclusion.map α =
      c.map i a ≫ Fiber.fiberInclusion.map β)
    (hj : c.map j a ≫ Fiber.fiberInclusion.map α =
      c.map j a ≫ Fiber.fiberInclusion.map β) : α = β := by
  apply (Deformation.Artin.fiberSquareComparison q c f g i j w).map_injective
  apply CategoricalPullback.hom_ext
  · show c.homMap i α = c.homMap i β
    apply fiber_hom_ext_of_cartesian i (c.map i b) inferInstance
    simpa only [c.homMap_fac] using hi
  · show c.homMap j α = c.homMap j β
    apply fiber_hom_ext_of_cartesian j (c.map j b) inferInstance
    simpa only [c.homMap_fac] using hj

private theorem fiberSquareComparison_hom_exists
    [(Deformation.Artin.fiberSquareComparison q c f g i j w).Full]
    {a b : q.Fiber Z}
    (α : c.obj i a ⟶ c.obj i b) (β : c.obj j a ⟶ c.obj j b)
    (h : (c.pullbackFunctor f).map α ≫
        ((Deformation.Artin.fiberSquareComparison q c f g i j w).obj b).iso.hom =
      ((Deformation.Artin.fiberSquareComparison q c f g i j w).obj a).iso.hom ≫
        (c.pullbackFunctor g).map β) :
    ∃ γ : a ⟶ b,
      c.map i a ≫ Fiber.fiberInclusion.map γ = Fiber.fiberInclusion.map α ≫ c.map i b ∧
      c.map j a ≫ Fiber.fiberInclusion.map γ = Fiber.fiberInclusion.map β ≫ c.map j b := by
  let m : (Deformation.Artin.fiberSquareComparison q c f g i j w).obj a ⟶
      (Deformation.Artin.fiberSquareComparison q c f g i j w).obj b := ⟨α, β, h⟩
  let γ := (Deformation.Artin.fiberSquareComparison q c f g i j w).preimage m
  have hm := (Deformation.Artin.fiberSquareComparison q c f g i j w).map_preimage m
  have hi : c.homMap i γ = α := congrArg CategoricalPullback.Hom.fst hm
  have hj : c.homMap j γ = β := congrArg CategoricalPullback.Hom.snd hm
  refine ⟨γ, ?_, ?_⟩
  · rw [← hi, c.homMap_fac]
  · rw [← hj, c.homMap_fac]

private theorem pullbackFunctor_eqToHom_fac
    {C : Type*} [Category C] {Y : Type*} [Category Y]
    {q : Y ⥤ C} (c : q.ChoiceOfPullbacks) {U V : C}
    {f g : U ⟶ V} (h : f = g) (x : q.Fiber V) :
    Functor.Fiber.fiberInclusion.map
      ((eqToIso (congrArg c.pullbackFunctor h)).hom.app x) ≫ c.map g x = c.map f x := by
  subst g
  simp

private theorem fiberSquareComparison_iso_fac (x : q.Fiber Z) :
    Fiber.fiberInclusion.map
        ((Deformation.Artin.fiberSquareComparison q c f g i j w).obj x).iso.hom ≫
      c.map g (c.obj j x) ≫ c.map j x = c.map f (c.obj i x) ≫ c.map i x := by
  show Fiber.fiberInclusion.map
    (((c.pullbackFunctorCompIso f i).inv.app x) ≫
      ((eqToIso (congrArg c.pullbackFunctor w)).hom.app x) ≫
      ((c.pullbackFunctorCompIso g j).hom.app x)) ≫ _ = _
  simp only [Functor.map_comp, Category.assoc]
  rw [show Fiber.fiberInclusion.map ((c.pullbackFunctorCompIso g j).hom.app x) ≫
      c.map g (c.obj j x) ≫ c.map j x = c.map (g ≫ j) x from c.objCompIso_hom_fac g j x]
  rw [pullbackFunctor_eqToHom_fac c w x]
  have h := c.objCompIso_hom_fac f i x
  show Fiber.fiberInclusion.map (c.objCompIso f i x).inv ≫ c.map (f ≫ i) x = _
  rw [← h]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
  show (𝟙 _ ≫ c.map f (c.obj i x)) ≫ c.map i x = _
  simp

private theorem fiberSquareComparison_glue
    (hq : q.IsFiberedInGroupoids)
    [(Deformation.Artin.fiberSquareComparison q c f g i j w).EssSurj]
    (x : q.Fiber U) (y : q.Fiber V) (z : q.Fiber W)
    (α : x.val ⟶ y.val) (β : x.val ⟶ z.val)
    [q.IsHomLift f α] [q.IsHomLift g β] :
    ∃ (t : q.Fiber Z) (γ : y.val ⟶ t.val) (δ : z.val ⟶ t.val),
      q.IsHomLift i γ ∧ q.IsHomLift j δ ∧ α ≫ γ = β ≫ δ := by
  have : q.IsCartesian f α :=
    (hq.isStronglyCartesian_homLift f α).isCartesian_of_isStronglyCartesian
  have : q.IsCartesian g β :=
    (hq.isStronglyCartesian_homLift g β).isCartesian_of_isStronglyCartesian
  let eV : c.obj f y ≅ x := fiberIsoOfCartesian f (c.map f y) α inferInstance inferInstance
  let eW : c.obj g z ≅ x := fiberIsoOfCartesian g (c.map g z) β inferInstance inferInstance
  let d : CategoricalPullback (c.pullbackFunctor f) (c.pullbackFunctor g) :=
    ⟨y, z, eV ≪≫ eW.symm⟩
  let t := (Deformation.Artin.fiberSquareComparison q c f g i j w).objPreimage d
  let e := (Deformation.Artin.fiberSquareComparison q c f g i j w).objObjPreimageIso d
  let γ := Fiber.fiberInclusion.map e.inv.fst ≫ c.map i t
  let δ := Fiber.fiberInclusion.map e.inv.snd ≫ c.map j t
  have : q.IsHomLift (𝟙 V) (Fiber.fiberInclusion.map e.inv.fst) := e.inv.fst.property
  have : q.IsHomLift (𝟙 W) (Fiber.fiberInclusion.map e.inv.snd) := e.inv.snd.property
  have : q.IsHomLift i γ := by dsimp [γ]; infer_instance
  have : q.IsHomLift j δ := by dsimp [δ]; infer_instance
  refine ⟨t, γ, δ, inferInstance, inferInstance, ?_⟩
  apply (cancel_epi (Fiber.fiberInclusion.map eV.hom)).mp
  have heV : Fiber.fiberInclusion.map eV.hom ≫ α = c.map f y :=
    fiberIsoOfCartesian_hom_fac f (c.map f y) α inferInstance inferInstance
  have heW : Fiber.fiberInclusion.map eW.inv ≫ c.map g z = β :=
    fiberIsoOfCartesian_inv_fac g (c.map g z) β inferInstance inferInstance
  have hw := congrArg
    (fun m => Fiber.fiberInclusion.map m ≫ c.map g (c.obj j t) ≫ c.map j t) e.inv.w
  change Fiber.fiberInclusion.map
      (c.homMap f e.inv.fst ≫
        ((Deformation.Artin.fiberSquareComparison q c f g i j w).obj t).iso.hom) ≫ _ =
    Fiber.fiberInclusion.map (d.iso.hom ≫ c.homMap g e.inv.snd) ≫ _ at hw
  simp only [Functor.map_comp, Category.assoc, fiberSquareComparison_iso_fac] at hw
  have hi : Fiber.fiberInclusion.map (c.homMap f e.inv.fst) ≫
      c.map f (c.obj i t) ≫ c.map i t = c.map f y ≫ γ := by
    simpa only [Category.assoc, γ] using
      congrArg (fun m => m ≫ c.map i t)
        (c.homMap_fac f (show y ⟶ c.obj i t from e.inv.fst))
  have hj : Fiber.fiberInclusion.map (c.homMap g e.inv.snd) ≫
      c.map g (c.obj j t) ≫ c.map j t = c.map g z ≫ δ := by
    simpa only [Category.assoc, δ] using
      congrArg (fun m => m ≫ c.map j t)
        (c.homMap_fac g (show z ⟶ c.obj j t from e.inv.snd))
  rw [hi, hj] at hw
  calc
    Fiber.fiberInclusion.map eV.hom ≫ α ≫ γ = c.map f y ≫ γ := by rw [← Category.assoc, heV]
    _ = Fiber.fiberInclusion.map d.iso.hom ≫ c.map g z ≫ δ := hw
    _ = Fiber.fiberInclusion.map eV.hom ≫ β ≫ δ := by
      show Fiber.fiberInclusion.map (eV.hom ≫ eW.inv) ≫ _ = _
      rw [Functor.map_comp, Category.assoc, ← Category.assoc (Fiber.fiberInclusion.map eW.inv), heW]

/-- Two fibre morphisms agreeing after precomposition with a cartesian lift agree after
precomposition with the chosen pullback arrow. -/
private theorem chosenPullback_cancel_of_lift
    (hq : q.IsFiberedInGroupoids) {a b : q.Fiber Z} (y : q.Fiber V)
    (r : y.val ⟶ a.val) [q.IsHomLift i r] {α β : a ⟶ b}
    (h : r ≫ Fiber.fiberInclusion.map α = r ≫ Fiber.fiberInclusion.map β) :
    c.map i a ≫ Fiber.fiberInclusion.map α = c.map i a ≫ Fiber.fiberInclusion.map β := by
  have := (hq.isStronglyCartesian_homLift i r).isCartesian_of_isStronglyCartesian
  let e : c.obj i a ≅ y := fiberIsoOfCartesian i (c.map i a) r inferInstance inferInstance
  simpa only [← Category.assoc, e, fiberIsoOfCartesian_hom_fac] using
    congrArg (fun m => Fiber.fiberInclusion.map e.hom ≫ m) h

private theorem fiberSquareComparison_hom_ext_of_lifts
    (hq : q.IsFiberedInGroupoids)
    [(Deformation.Artin.fiberSquareComparison q c f g i j w).Faithful]
    {a b : q.Fiber Z} (y : q.Fiber V) (z : q.Fiber W)
    (r : y.val ⟶ a.val) (s : z.val ⟶ a.val)
    [q.IsHomLift i r] [q.IsHomLift j s]
    {α β : a ⟶ b}
    (hi : r ≫ Fiber.fiberInclusion.map α = r ≫ Fiber.fiberInclusion.map β)
    (hj : s ≫ Fiber.fiberInclusion.map α = s ≫ Fiber.fiberInclusion.map β) : α = β :=
  fiberSquareComparison_hom_ext q c f g i j w
    (chosenPullback_cancel_of_lift q c i hq y r hi) (chosenPullback_cancel_of_lift q c j hq z s hj)

private theorem fiberSquareComparison_desc
    (hq : q.IsFiberedInGroupoids)
    [(Deformation.Artin.fiberSquareComparison q c f g i j w).Full]
    {a b : q.Fiber Z}
    (r : (c.obj i a).val ⟶ b.val) (s : (c.obj j a).val ⟶ b.val)
    [q.IsHomLift i r] [q.IsHomLift j s]
    (h : c.map f (c.obj i a) ≫ r =
      Fiber.fiberInclusion.map
        ((Deformation.Artin.fiberSquareComparison q c f g i j w).obj a).iso.hom ≫
      c.map g (c.obj j a) ≫ s) :
    ∃ γ : a ⟶ b,
      c.map i a ≫ Fiber.fiberInclusion.map γ = r ∧
      c.map j a ≫ Fiber.fiberInclusion.map γ = s := by
  have := (hq.isStronglyCartesian_homLift i r).isCartesian_of_isStronglyCartesian
  have := (hq.isStronglyCartesian_homLift j s).isCartesian_of_isStronglyCartesian
  let α : c.obj i a ⟶ c.obj i b :=
    (fiberIsoOfCartesian i r (c.map i b) inferInstance inferInstance).hom
  let β : c.obj j a ⟶ c.obj j b :=
    (fiberIsoOfCartesian j s (c.map j b) inferInstance inferInstance).hom
  have hα : Fiber.fiberInclusion.map α ≫ c.map i b = r :=
    fiberIsoOfCartesian_hom_fac _ _ _ _ _
  have hβ : Fiber.fiberInclusion.map β ≫ c.map j b = s :=
    fiberIsoOfCartesian_hom_fac _ _ _ _ _
  obtain ⟨γ, hγi, hγj⟩ := fiberSquareComparison_hom_exists q c f g i j w α β (by
    apply fiber_hom_ext_of_cartesian (g ≫ j) (c.map g (c.obj j b) ≫ c.map j b)
      (hq.isStronglyCartesian_homLift _ _).isCartesian_of_isStronglyCartesian
    simp only [Functor.map_comp, Category.assoc, fiberSquareComparison_iso_fac]
    calc
      Fiber.fiberInclusion.map (c.homMap f α) ≫
          c.map f (c.obj i b) ≫ c.map i b = c.map f (c.obj i a) ≫ r := by
        rw [← Category.assoc, c.homMap_fac, Category.assoc, hα]
      _ = _ := h
      _ = _ := by
        rw [← hβ, ← Category.assoc (c.map g (c.obj j a)), ← c.homMap_fac]
        simp only [Category.assoc]
        rfl)
  exact ⟨γ, hγi.trans hα, hγj.trans hβ⟩

private theorem fiberSquareComparison_pointed_hom_exists
    (hq : q.IsFiberedInGroupoids)
    [(Deformation.Artin.fiberSquareComparison q c f g i j w).Full]
    {a b : q.Fiber Z} (x : q.Fiber U) (y : q.Fiber V) (z : q.Fiber W)
    (α : x.val ⟶ y.val) (β : x.val ⟶ z.val)
    (r : y.val ⟶ a.val) (s : z.val ⟶ a.val)
    (r' : y.val ⟶ b.val) (s' : z.val ⟶ b.val)
    [q.IsHomLift f α] [q.IsHomLift g β]
    [q.IsHomLift i r] [q.IsHomLift j s]
    [q.IsHomLift i r'] [q.IsHomLift j s']
    (ha : α ≫ r = β ≫ s) (hb : α ≫ r' = β ≫ s') :
    ∃ γ : a ⟶ b,
      r ≫ Fiber.fiberInclusion.map γ = r' ∧
      s ≫ Fiber.fiberInclusion.map γ = s' := by
  have := hq.isStronglyCartesian_homLift i r
  have := hq.isStronglyCartesian_homLift j s
  have := hq.isStronglyCartesian_homLift (f ≫ i) (α ≫ r)
  let eV : c.obj i a ≅ y := fiberIsoOfCartesian i (c.map i a) r inferInstance inferInstance
  let eW : c.obj j a ≅ z := fiberIsoOfCartesian j (c.map j a) s inferInstance inferInstance
  let e : c.obj f (c.obj i a) ≅ x := fiberIsoOfCartesian (f ≫ i)
    (c.map f (c.obj i a) ≫ c.map i a) (α ≫ r)
    (hq.isStronglyCartesian_homLift _ _).isCartesian_of_isStronglyCartesian inferInstance
  have he : Fiber.fiberInclusion.map e.hom ≫ (α ≫ r) =
      c.map f (c.obj i a) ≫ c.map i a := fiberIsoOfCartesian_hom_fac _ _ _ _ _
  have heV : Fiber.fiberInclusion.map eV.hom ≫ r = c.map i a :=
    fiberIsoOfCartesian_hom_fac _ _ _ _ _
  have heW : Fiber.fiberInclusion.map eW.hom ≫ s = c.map j a :=
    fiberIsoOfCartesian_hom_fac _ _ _ _ _
  have hα : Fiber.fiberInclusion.map e.hom ≫ α =
      c.map f (c.obj i a) ≫ Fiber.fiberInclusion.map eV.hom := by
    apply IsStronglyCartesian.ext q i r f
    simpa only [Category.assoc, heV] using he
  have hβ : Fiber.fiberInclusion.map e.hom ≫ β =
      Fiber.fiberInclusion.map
        ((Deformation.Artin.fiberSquareComparison q c f g i j w).obj a).iso.hom ≫
      c.map g (c.obj j a) ≫ Fiber.fiberInclusion.map eW.hom := by
    apply IsStronglyCartesian.ext q j s g
    simp only [Category.assoc, heW, fiberSquareComparison_iso_fac]
    rw [← ha]
    exact he
  obtain ⟨γ, hi, hj⟩ := fiberSquareComparison_desc q c f g i j w hq
    (Fiber.fiberInclusion.map eV.hom ≫ r') (Fiber.fiberInclusion.map eW.hom ≫ s') (by
      rw [← Category.assoc, ← hα]
      rw [← Category.assoc (c.map g (c.obj j a)),
        ← Category.assoc (Fiber.fiberInclusion.map
          ((Deformation.Artin.fiberSquareComparison q c f g i j w).obj a).iso.hom), ← hβ]
      simpa only [Category.assoc] using congrArg (fun m => Fiber.fiberInclusion.map e.hom ≫ m) hb)
  refine ⟨γ, ?_, ?_⟩
  · apply (cancel_epi (Fiber.fiberInclusion.map eV.hom)).mp
    simpa only [← Category.assoc, heV] using hi
  · apply (cancel_epi (Fiber.fiberInclusion.map eW.hom)).mp
    simpa only [← Category.assoc, heW] using hj

private theorem fiberSquareComparison_arrow_ext
    (hq : q.IsFiberedInGroupoids)
    [(Deformation.Artin.fiberSquareComparison q c f g i j w).Faithful]
    {a : q.Fiber Z} {b : Y} (h : Z ⟶ q.obj b)
    (y : q.Fiber V) (z : q.Fiber W)
    (r : y.val ⟶ a.val) (s : z.val ⟶ a.val)
    [q.IsHomLift i r] [q.IsHomLift j s]
    {α β : a.val ⟶ b} [q.IsHomLift h α] [q.IsHomLift h β]
    (hi : r ≫ α = r ≫ β) (hj : s ≫ α = s ≫ β) : α = β := by
  let b₀ : q.Fiber (q.obj b) := ⟨b, rfl⟩
  let b' := c.obj h b₀
  let l := c.map h b₀
  have := hq.isStronglyCartesian_homLift h α
  have := hq.isStronglyCartesian_homLift h β
  have := hq.isStronglyCartesian_homLift h l
  let eα : a ≅ b' := fiberIsoOfCartesian h α l inferInstance inferInstance
  let eβ : a ≅ b' := fiberIsoOfCartesian h β l inferInstance inferInstance
  have hα : Fiber.fiberInclusion.map eα.hom ≫ l = α :=
    fiberIsoOfCartesian_hom_fac _ _ _ _ _
  have hβ : Fiber.fiberInclusion.map eβ.hom ≫ l = β :=
    fiberIsoOfCartesian_hom_fac _ _ _ _ _
  have he : eα.hom = eβ.hom := by
    apply fiberSquareComparison_hom_ext_of_lifts q c f g i j w hq y z r s
    · apply IsStronglyCartesian.ext q h l i
      simpa only [Category.assoc, hα, hβ] using hi
    · apply IsStronglyCartesian.ext q h l j
      simpa only [Category.assoc, hα, hβ] using hj
  rw [← hα, ← hβ, he]

private theorem fiberSquareComparison_pointed_arrow_exists
    (hq : q.IsFiberedInGroupoids)
    [(Deformation.Artin.fiberSquareComparison q c f g i j w).Full]
    {a : q.Fiber Z} {b : Y} (h : Z ⟶ q.obj b)
    (x : q.Fiber U) (y : q.Fiber V) (z : q.Fiber W)
    (α : x.val ⟶ y.val) (β : x.val ⟶ z.val)
    (r : y.val ⟶ a.val) (s : z.val ⟶ a.val)
    (r' : y.val ⟶ b) (s' : z.val ⟶ b)
    [q.IsHomLift f α] [q.IsHomLift g β]
    [q.IsHomLift i r] [q.IsHomLift j s]
    [q.IsHomLift (i ≫ h) r'] [q.IsHomLift (j ≫ h) s']
    (ha : α ≫ r = β ≫ s) (hb : α ≫ r' = β ≫ s') :
    ∃ γ : a.val ⟶ b, q.IsHomLift h γ ∧ r ≫ γ = r' ∧ s ≫ γ = s' := by
  let b₀ : q.Fiber (q.obj b) := ⟨b, rfl⟩
  let b' := c.obj h b₀
  let l := c.map h b₀
  have := hq.isStronglyCartesian_homLift h l
  let r₀ := IsStronglyCartesian.map q h l (g := i) rfl r'
  let s₀ := IsStronglyCartesian.map q h l (g := j) rfl s'
  have hr : r₀ ≫ l = r' := IsStronglyCartesian.fac q h l rfl r'
  have hs : s₀ ≫ l = s' := IsStronglyCartesian.fac q h l rfl s'
  have hb' : α ≫ r₀ = β ≫ s₀ := by
    have : q.IsHomLift (f ≫ i) (β ≫ s₀) := w.symm ▸ inferInstance
    apply IsStronglyCartesian.ext q h l (f ≫ i)
    simpa only [Category.assoc, hr, hs] using hb
  obtain ⟨γ, hγi, hγj⟩ := fiberSquareComparison_pointed_hom_exists q c f g i j w hq
    x y z α β r s r₀ s₀ ha hb'
  refine ⟨Fiber.fiberInclusion.map γ ≫ l, inferInstance, ?_, ?_⟩
  · rw [← Category.assoc, hγi, hr]
  · rw [← Category.assoc, hγj, hs]

end FiberSquare

private theorem siteObject_isArtinianLocal_of_post_eq
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (R : Type u)
    [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    {f : Spec (.of R) ⟶ S}
    (h : (Over.post B.inclusion).obj U = Over.mk f) :
    Deformation.Artin.IsArtinianLocal B S hS U := by
  have he : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U = Spec (.of R) :=
    congrArg Over.left h
  unfold Deformation.Artin.IsArtinianLocal
  rw [he]
  exact ⟨inferInstance, (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.isLocalRing,
    inferInstance⟩

private theorem siteObject_isFiniteTypeOver_of_post_eq
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS) {Z : Scheme.{u}} {f : Z ⟶ S}
    (h : (Over.post B.inclusion).obj U = Over.mk f)
    (hf : LocallyOfFiniteType f ∧ QuasiCompact f) :
    Deformation.Artin.IsFiniteTypeOver B S hS U := by
  show LocallyOfFiniteType ((Over.post B.inclusion).obj U).hom ∧
    QuasiCompact ((Over.post B.inclusion).obj U).hom
  rw [h]
  exact hf

private theorem schemeMap_isPushout
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V W Z : AlgebraicGeometry.BigFppfOver B S hS}
    {sU sV sW sZ : Scheme.{u}}
    {bU : sU ⟶ S} {bV : sV ⟶ S} {bW : sW ⟶ S} {bZ : sZ ⟶ S}
    (hU : (Over.post B.inclusion).obj U = Over.mk bU)
    (hV : (Over.post B.inclusion).obj V = Over.mk bV)
    (hW : (Over.post B.inclusion).obj W = Over.mk bW)
    (hZ : (Over.post B.inclusion).obj Z = Over.mk bZ)
    (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
    (h : IsPushout (schemeMap (Over.post B.inclusion) hU hV f)
      (schemeMap (Over.post B.inclusion) hU hW g)
      (schemeMap (Over.post B.inclusion) hV hZ i)
      (schemeMap (Over.post B.inclusion) hW hZ j)) :
    IsPushout ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j) :=
  h.of_iso (eqToIso (congrArg Over.left hU).symm)
    (eqToIso (congrArg Over.left hV).symm) (eqToIso (congrArg Over.left hW).symm)
    (eqToIso (congrArg Over.left hZ).symm)
    (by simp [schemeMap]) (by simp [schemeMap])
    (by simp [schemeMap]) (by simp [schemeMap])

private theorem schemeMap_isClosedImmersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : AlgebraicGeometry.BigFppfOver B S hS} {sU sV : Scheme.{u}}
    {bU : sU ⟶ S} {bV : sV ⟶ S}
    (hU : (Over.post B.inclusion).obj U = Over.mk bU)
    (hV : (Over.post B.inclusion).obj V = Over.mk bV)
    (f : U ⟶ V) (h : IsClosedImmersion (schemeMap (Over.post B.inclusion) hU hV f)) :
    IsClosedImmersion ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f) := by
  have he : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f =
      eqToHom (congrArg Over.left hU) ≫ schemeMap (Over.post B.inclusion) hU hV f ≫
        eqToHom (congrArg Over.left hV).symm := by simp [schemeMap]
  rw [he]
  infer_instance

omit [IsLocallyNoetherian S] in
private theorem satisfiesRS_comparison_isEquivalence
    (hp : p.IsFiberedInGroupoids)
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hRS : Deformation.Artin.SatisfiesRS B S hS p hp)
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.l)
    {U V W Z : AlgebraicGeometry.BigFppfOver B S hS}
    (hU : (Over.post B.inclusion).obj U =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ))
    (hV : (Over.post B.inclusion).obj V =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hW : (Over.post B.inclusion).obj W =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ A)) ≫ iΛ))
    (hZ : (Over.post B.inclusion).obj Z =
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap T.Λ ((Deformation.comparisonFunctor T).functor.obj A))) ≫ iΛ))
    (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
    (w : f ≫ i = g ≫ j)
    (hf : schemeMap (Over.post B.inclusion) hU hV f =
      Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (hg : schemeMap (Over.post B.inclusion) hU hW g =
      Spec.map (CommRingCat.ofHom (Deformation.residueMap T A)))
    (hi : schemeMap (Over.post B.inclusion) hV hZ i =
      Spec.map (CommRingCat.ofHom
        (Deformation.Artin.residueMap ((Deformation.comparisonFunctor T).functor.obj A))))
    (hj : schemeMap (Over.post B.inclusion) hW hZ j =
      Spec.map (CommRingCat.ofHom (comparisonProjection T A))) :
    letI : p.IsFibered := hp.isFibered
    (Deformation.Artin.fiberSquareComparison p p.chosenPullbacks f g i j w).IsEquivalence := by
  have : p.IsFibered := hp.isFibered
  have hfiniteL := changeFieldPoint_finiteType T iΛ hfinite
  apply hRS g f j i w.symm
  · exact siteObject_isArtinianLocal_of_post_eq B S hS U T.l hU
  · exact siteObject_isArtinianLocal_of_post_eq B S hS W A hW
  · exact siteObject_isArtinianLocal_of_post_eq B S hS V T.k hV
  · exact siteObject_isArtinianLocal_of_post_eq B S hS Z
      ((Deformation.comparisonFunctor T).functor.obj A) hZ
  · exact siteObject_isFiniteTypeOver_of_post_eq B S hS U hU hfiniteL
  · exact siteObject_isFiniteTypeOver_of_post_eq B S hS W hW
      (finiteType_of_baseArtinian iΛ hfiniteL A)
  · exact siteObject_isFiniteTypeOver_of_post_eq B S hS V hV hfinite
  · exact siteObject_isFiniteTypeOver_of_post_eq B S hS Z hZ
      (finiteType_of_baseArtinian iΛ hfinite ((Deformation.comparisonFunctor T).functor.obj A))
  · apply schemeMap_isClosedImmersion B S hS hU hW g
    rw [hg]
    exact IsClosedImmersion.spec_of_surjective _
      (A.residueEquiv.surjective.comp (IsLocalRing.residue_surjective (R := A)))
  · apply schemeMap_isPushout B S hS hU hW hV hZ g f j i
    rw [hf, hg, hi, hj]
    exact comparisonSpec_isPushout T A

private theorem schemeMap_of_homLift
    {C D : Type*} [Category C] [Category D] {S : Scheme.{u}}
    (p : C ⥤ D) (P : D ⥤ Over S)
    {x y : C} {U V : D} {sU sV : Scheme.{u}}
    {bU : sU ⟶ S} {bV : sV ⟶ S}
    (hx : p.obj x = U) (hy : p.obj y = V)
    (hU : P.obj U = Over.mk bU) (hV : P.obj V = Over.mk bV)
    (f : U ⟶ V) (r : x ⟶ y) [p.IsHomLift f r] :
    schemeMap (p ⋙ P) ((congrArg P.obj hx).trans hU) ((congrArg P.obj hy).trans hV) r =
      schemeMap P hU hV f := by
  subst U V
  have hr : p.map r = f := by simpa using IsHomLift.fac' p f r
  simp only [schemeMap, Functor.comp_map, hr]

omit [IsLocallyNoetherian S] in
private theorem exists_deformation_restricting_to
    (hp : p.IsFiberedInGroupoids)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((p ⋙ Over.post B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hRS : Deformation.Artin.SatisfiesRS B S hS p hp)
    (d : Deformation.Artin.DeformationObject iΛ (p ⋙ Over.post B.inclusion) xₗ hxₗ) :
    ∃ (z : X) (hz : (p ⋙ Over.post B.inclusion).obj z =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ
          ((Deformation.comparisonFunctor T).functor.obj d.algebra))) ≫ iΛ))
      (r : x₀ ⟶ z) (s : d.point ⟶ z),
      schemeMap (p ⋙ Over.post B.inclusion) hx₀ hz r =
        Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap
          ((Deformation.comparisonFunctor T).functor.obj d.algebra))) ∧
      schemeMap (p ⋙ Over.post B.inclusion) d.base hz s =
        Spec.map (CommRingCat.ofHom (comparisonProjection T d.algebra)) ∧
      d.arrow ≫ s = η ≫ r := by
  let P := Over.post (X := B.obj hS) B.inclusion
  let A := d.algebra
  let R := (Deformation.comparisonFunctor T).functor.obj A
  let bR := Spec.map (CommRingCat.ofHom (algebraMap T.Λ R)) ≫ iΛ
  have hft := finiteType_of_baseArtinian iΛ hfinite R
  have : LocallyOfFiniteType bR := hft.1
  have : QuasiCompact bR := hft.2
  let Z := siteObjectOverFiniteType B S hS bR
  have hZ : P.obj Z = Over.mk bR := siteObjectOverFiniteType_post B S hS bR
  let i := siteMapOfSchemes B S hS hx₀ hZ
    (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap R))) (residuePoint_base R iΛ)
  have hi : schemeMap P hx₀ hZ i =
      Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap R)) :=
    siteMapOfSchemes_base B S hS hx₀ hZ _ _
  have hjbase : Spec.map (CommRingCat.ofHom (comparisonProjection T A)) ≫ bR =
      Spec.map (CommRingCat.ofHom (algebraMap T.Λ A)) ≫ iΛ := by
    dsimp only [bR]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  let j := siteMapOfSchemes B S hS d.base hZ
    (Spec.map (CommRingCat.ofHom (comparisonProjection T A))) hjbase
  have hj : schemeMap P d.base hZ j =
      Spec.map (CommRingCat.ofHom (comparisonProjection T A)) :=
    siteMapOfSchemes_base B S hS d.base hZ _ _
  have hf : schemeMap P hxₗ hx₀ (p.map η) =
      Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)) := hηbase
  have hg : schemeMap P hxₗ d.base (p.map d.arrow) =
      Spec.map (CommRingCat.ofHom (Deformation.residueMap T A)) := d.arrow_base
  have hw : p.map η ≫ i = p.map d.arrow ≫ j := by
    apply P.map_injective
    apply (schemeMap_eq_iff P hxₗ hZ _ _).mp
    rw [schemeMap_comp P hxₗ hx₀, schemeMap_comp P hxₗ d.base, hf, hg, hi, hj]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, comparisonProjection_residueMap]
  have : p.IsFibered := hp.isFibered
  let := satisfiesRS_comparison_isEquivalence T iΛ B hS p hp hfinite hRS A
    hxₗ hx₀ d.base hZ (p.map η) (p.map d.arrow) i j hw hf hg hi hj
  obtain ⟨z, r, s, hr, hs, he⟩ := fiberSquareComparison_glue p p.chosenPullbacks
    (p.map η) (p.map d.arrow) i j hw hp
    (Functor.Fiber.mk (p := p) (a := xₗ) rfl)
    (Functor.Fiber.mk (p := p) (a := x₀) rfl)
    (Functor.Fiber.mk (p := p) (a := d.point) rfl) η d.arrow
  let hz : (p ⋙ P).obj z.val = Over.mk bR := (congrArg P.obj z.property).trans hZ
  have := hr
  have := hs
  refine ⟨z.val, hz, r, s, ?_, ?_, he.symm⟩
  · exact (schemeMap_of_homLift p P rfl z.property hx₀ hZ i r).trans hi
  · exact (schemeMap_of_homLift p P rfl z.property d.base hZ j s).trans hj

private theorem deformationMorphism_exists_of_common_restriction
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hS : B.Contains S)
    {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (x : X) (hx : (p ⋙ Over.post B.inclusion).obj x =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (a b : Deformation.Artin.DeformationObject iΛ (p ⋙ Over.post B.inclusion) x hx)
    (u : a.algebra ⟶ b.algebra)
    {z : X} {Z : Scheme.{u}} {bZ : Z ⟶ S}
    (hz : (p ⋙ Over.post B.inclusion).obj z = Over.mk bZ)
    (r : a.point ⟶ z) (s : b.point ⟶ z)
    (hb : schemeMap (p ⋙ Over.post B.inclusion) b.base hz s =
      Spec.map (CommRingCat.ofHom u.hom.toRingHom) ≫
        schemeMap (p ⋙ Over.post B.inclusion) a.base hz r)
    (ht : b.arrow ≫ s = a.arrow ≫ r) :
    ∃ m : Deformation.Artin.DeformationMorphism iΛ (p ⋙ Over.post B.inclusion) x hx a b,
      m.ringHom = u ∧ m.arrow ≫ r = s := by
  let P := Over.post (X := B.obj hS) B.inclusion
  let q := p ⋙ P
  have hu : Spec.map (CommRingCat.ofHom u.hom.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap Λ a.algebra)) ≫ iΛ) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ b.algebra)) ≫ iΛ := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext t
    exact u.hom.commutes t
  let g := siteMapOfSchemes B S hS b.base a.base
    (Spec.map (CommRingCat.ofHom u.hom.toRingHom)) hu
  have hg : schemeMap P b.base a.base g = Spec.map (CommRingCat.ofHom u.hom.toRingHom) :=
    siteMapOfSchemes_base B S hS b.base a.base _ _
  have hf : p.map s = g ≫ p.map r := by
    apply P.map_injective
    apply (schemeMap_eq_iff P b.base hz _ _).mp
    rw [schemeMap_comp P b.base a.base, hg]
    exact hb
  have : p.IsFibered := hp.isFibered
  have : p.IsCartesian (p.map r) r :=
    (hp.isStronglyCartesian_homLift _ _).isCartesian_of_isStronglyCartesian
  obtain ⟨χ, ⟨hχ, hχr⟩, _⟩ := cartesian_factor_of_fibered p r g s hf
  have := hχ
  have hχbase : schemeMap q b.base a.base χ =
      Spec.map (CommRingCat.ofHom u.hom.toRingHom) :=
    (schemeMap_of_homLift p P rfl rfl b.base a.base g χ).trans hg
  refine ⟨⟨u, χ, ?_, hχbase⟩, rfl, hχr⟩
  apply cartesian_cancel p hp r
  · apply P.map_injective
    apply (schemeMap_eq_iff q hx a.base _ _).mp
    rw [schemeMap_comp q hx b.base, show schemeMap q hx b.base b.arrow = _ from b.arrow_base,
      show schemeMap q hx a.base a.arrow = _ from a.arrow_base, hχbase, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, artinianResidueMap_natural]
  · rw [Category.assoc, hχr]
    exact ht

private theorem ringHom_comp_cast_codomain
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k} (h : A = B)
    {R : Type u} [CommRing R] (f : R →+* B) :
    (eqToHom h).hom.toRingHom.comp (h.symm ▸ f) = f := by
  subst B
  rfl

private theorem deformation_restriction_target_transport
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type v} [Category.{w} X] {q : X ⥤ Over S} {x₀ : X}
    {hx₀ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {d e : Deformation.Artin.DeformationObject iΛ q x₀ hx₀} (h : d = e)
    {z : X} {A : Type u} [CommRing A] {fA : Spec (.of A) ⟶ S}
    (hz : q.obj z = Over.mk fA) (r : z ⟶ d.point) (f : d.algebra →+* A)
    (hr : schemeMap q hz d.base r = Spec.map (CommRingCat.ofHom f)) :
    schemeMap q hz e.base (r ≫ eqToHom (congrArg Deformation.Artin.DeformationObject.point h)) =
      Spec.map (CommRingCat.ofHom (f.comp
        (eqToHom
          (congrArg Deformation.Artin.DeformationObject.algebra h).symm).hom.toRingHom)) := by
  subst e
  simpa [schemeMap] using hr

private theorem isIso_of_cofibered_map_isIso
    {C D : Type*} [Category C] [Category D] (q : C ⥤ D)
    (hq : Deformation.IsCofiberedInGroupoids q)
    {a b : C} (f : a ⟶ b) [IsIso (q.map f)] : IsIso f := by
  have := hq.isStronglyCartesian_homLift (q.op.map f.op) f.op
  have : IsIso (q.op.map f.op) := inferInstanceAs (IsIso (q.map f).op)
  have : IsIso f.op := Functor.IsStronglyCartesian.isIso_of_base_isIso q.op (q.op.map f.op) f.op
  exact isIso_of_op f

omit [IsLocallyNoetherian S] in
private theorem changeOfFieldFunctor_essSurj
    (hp : p.IsFiberedInGroupoids)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((p ⋙ Over.post B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hRS : Deformation.Artin.SatisfiesRS B S hS p hp)
    (F : ChangeOfFieldFunctor T iΛ B hS p x₀ xₗ hx₀ hxₗ η) : F.toFunctor.EssSurj := by
  let q := p ⋙ Over.post B.inclusion
  let C₀ := Deformation.Artin.predeformationCategory iΛ q x₀ hx₀
  let Cₗ := Deformation.Artin.predeformationCategory iΛ q xₗ hxₗ
  constructor
  intro b
  let d := Cₗ.objects b
  obtain ⟨z, hz, r, s, hr, hs, ht⟩ := exists_deformation_restricting_to
    T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase hfinite hRS d
  let e : Deformation.Artin.DeformationObject iΛ q x₀ hx₀ :=
    ⟨(Deformation.comparisonFunctor T).functor.obj d.algebra, z, r, hz, hr⟩
  let c := C₀.objects.symm e
  have hc : C₀.objects c = e := C₀.objects.apply_symm_apply e
  have hca : (C₀.objects c).algebra = (Deformation.comparisonFunctor T).functor.obj d.algebra :=
    congrArg Deformation.Artin.DeformationObject.algebra hc
  let a : Deformation.ChangeOfFieldsCategory T C₀.projection :=
    ⟨c, d.algebra, eqToIso ((C₀.object_projection c).trans hca)⟩
  let da := Cₗ.objects (F.toFunctor.obj a)
  have hA : da.algebra = a.snd := F.algebra_eq a
  let ra : da.point ⟶ z := F.restriction a ≫
    eqToHom (congrArg Deformation.Artin.DeformationObject.point hc)
  have hra : schemeMap q da.base hz ra =
      Spec.map (CommRingCat.ofHom
        ((hA.symm ▸ deformationProjection T iΛ B hS p x₀ hx₀ a).comp
          (eqToHom hca.symm).hom.toRingHom)) :=
    deformation_restriction_target_transport hc da.base (F.restriction a) _
      (F.restriction_base a)
  have hbase : schemeMap q d.base hz s =
      Spec.map (CommRingCat.ofHom (eqToHom hA).hom.toRingHom) ≫
        schemeMap q da.base hz ra := by
    rw [hs, hra, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    rw [← RingHom.comp_assoc, ringHom_comp_cast_codomain]
    congr 1
  have htri : d.arrow ≫ s = da.arrow ≫ ra := by
    rw [ht]
    dsimp only [ra]
    rw [← Category.assoc, F.arrow_comm, Category.assoc,
      deformation_arrow_transport hc]
  obtain ⟨m, hm, _⟩ := deformationMorphism_exists_of_common_restriction iΛ B hS p hp
    xₗ hxₗ da d (eqToHom hA) hz ra s hbase htri
  let φ := (Cₗ.morphisms (F.toFunctor.obj a) b).symm m
  have hφ : (Cₗ.morphisms (F.toFunctor.obj a) b φ).ringHom = eqToHom hA := by
    simpa only [φ, Equiv.apply_symm_apply] using hm
  have hmap : Cₗ.projection.map φ =
      eqToHom (Cₗ.object_projection (F.toFunctor.obj a)) ≫
        eqToHom hA ≫ eqToHom (Cₗ.object_projection b).symm := by
    have hh := Cₗ.morphism_projection φ
    rw [hφ] at hh
    simpa [Category.assoc] using congrArg
      (fun f => eqToHom (Cₗ.object_projection (F.toFunctor.obj a)) ≫
        f ≫ eqToHom (Cₗ.object_projection b).symm) hh
  have : IsIso (Cₗ.projection.map φ) := hmap ▸ inferInstance
  have : IsIso φ := isIso_of_cofibered_map_isIso Cₗ.projection
    (Deformation.Artin.predeformationCategory_isPredeformationCategory
      B hS iΛ p xₗ hxₗ hp).cofibered φ
  exact ⟨a, ⟨asIso φ⟩⟩

end Equivalence

end Deformation.Artin.Site
