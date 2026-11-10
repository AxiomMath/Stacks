module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentFunctor
import StacksFrontier.Deformation.ArtinCriteria.TangentSpace
public import StacksFrontier.Deformation.Artin.Versality.NonversalThickening.SmallExtensionStages

/-!
# Artinian local algebras over a point and gluing along fibre squares

Spectra of Artinian local algebras with residue field `κ(u)` as objects of the big fppf site over
`S`, and the maps and isomorphisms between them; Cartesian arrows and retractions in categories
fibred in groupoids; and objects glued along a fibre square of the big fppf site.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal TopologicalSpace
open Stacks.Thickenings

namespace Deformation.Artin

universe u v w

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
attribute [local instance] Deformation.Artin.residueFieldAlgebra
attribute [local instance_reducible] AlgebraicGeometry.Scheme.residueField

noncomputable def artinianLocalAlgOver
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Λ : Type u} [CommRing Λ] (sMap : Spec (.of Λ) ⟶ S)
    {k : Type u} [Field k] [Algebra Λ k]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : B.Contains (Spec (.of A.carrier))) :
    AlgebraicGeometry.BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (X := B.obj hA) (Y := B.obj hS)
    (Spec.map (CommRingCat.ofHom (algebraMap Λ A.carrier)) ≫ sMap))

theorem artinianLocalAlgOver_post
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Λ : Type u} [CommRing Λ] (sMap : Spec (.of Λ) ⟶ S)
    {k : Type u} [Field k] [Algebra Λ k]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : B.Contains (Spec (.of A.carrier))) :
    (Over.post (X := B.obj hS) B.inclusion).obj
        (artinianLocalAlgOver B S hS sMap A hA) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A.carrier)) ≫ sMap) := rfl

/-- The scheme morphism underlying an arrow of a category over the big fppf site, read either
through the site or after composing with the inclusion of the site into all schemes. -/
theorem toScheme_map_eqToHom_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    {X Y : F} {W₁ W₂ : AlgebraicGeometry.BigFppfOver B S hS}
    (hX : p.obj X = W₁) (hY : p.obj Y = W₂) (g : X ⟶ Y) :
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (eqToHom hX.symm ≫ p.map g ≫ eqToHom hY) =
      eqToHom (congrArg Over.left (congrArg (Over.post B.inclusion).obj hX)).symm ≫
        ((p ⋙ Over.post B.inclusion).map g).left ≫
        eqToHom (congrArg Over.left (congrArg (Over.post B.inclusion).obj hY)) := by
  subst hX
  subst hY
  simp

theorem exists_cartesian_iso_lift
    {C : Type u} [Category C] {F : Type v} [Category F]
    (p : F ⥤ C) [p.IsFibered] {X Y : C} (e : X ≅ Y)
    (x : F) (hx : p.obj x = X) :
    ∃ y : F, p.obj y = Y ∧ ∃ m : y ⟶ x,
      p.IsHomLift e.inv m ∧ IsIso m := by
  let xf : p.Fiber X := ⟨x, hx⟩
  let c := Functor.chosenPullbacks p
  let yf := (c.pullbackFunctor e.inv).obj xf
  let m := c.map e.inv xf
  have hm : p.IsStronglyCartesian e.inv m := c.isStronglyCartesian e.inv xf
  let : IsIso e.inv := inferInstance
  have hmi : IsIso m := Functor.IsStronglyCartesian.isIso_of_base_isIso p e.inv m
  exact ⟨yf.1, yf.2, m, hm.toIsHomLift, hmi⟩

/-- In a category fibred in groupoids, every arrow is Cartesian.  This is the transport
fact needed to compare the supplied Artinian obstruction with its successive chosen pullbacks. -/
theorem every_arrow_cartesian_of_isFiberedInGroupoids
    {C : Type (u + 1)} [Category.{u, u + 1} C] {F : Type v} [Category.{w, v} F]
    (p : F ⥤ C) (hp : p.IsFiberedInGroupoids) {a b : F} (φ : a ⟶ b) :
    p.IsCartesian (p.map φ) φ := by
  classical
  refine ⟨?_⟩
  intro c ψ hψ
  let hc : p.obj c = p.obj a := IsHomLift.domain_eq p (p.map φ) ψ
  have hfac := IsHomLift.fac' p (p.map φ) ψ
  have hfac' : eqToHom hc ≫ p.map φ = p.map ψ := by
    simpa [hc] using hfac.symm
  obtain ⟨χ, hχ, huniq⟩ := hp.unique_lift φ ψ (eqToHom hc) hfac'
  have hχlift : p.IsHomLift (𝟙 (p.obj a)) χ := by
    apply IsHomLift.of_fac p (𝟙 (p.obj a)) χ hc rfl
    simp [hχ.1]
  refine ⟨χ, ⟨hχlift, hχ.2⟩, ?_⟩
  intro χ' hχ'
  apply huniq χ'
  constructor
  · let : p.IsHomLift (𝟙 (p.obj a)) χ' := hχ'.1
    have h := IsHomLift.fac' p (𝟙 (p.obj a)) χ'
    simpa [hc] using h
  · exact hχ'.2

private theorem mono_of_map_mono_of_fiberedInGroupoids
    {C : Type*} [Category C] {F : Type*} [Category F]
    (p : F ⥤ C) (hp : p.IsFiberedInGroupoids) {x y : F} (f : x ⟶ y)
    [Mono (p.map f)] : Mono f := by
  constructor
  intro z a b hab
  have hpab : p.map a = p.map b := by
    apply (cancel_mono (p.map f)).mp
    simpa only [← p.map_comp] using congrArg p.map hab
  obtain ⟨c, hc, huniq⟩ := hp.unique_lift f (a ≫ f) (p.map a) (p.map_comp a f).symm
  exact (huniq a ⟨rfl, rfl⟩).trans (huniq b ⟨hpab.symm, hab.symm⟩).symm

theorem no_retraction_of_failed_lift
    {C : Type*} [Category C] {F : Type*} [Category F]
    (p : F ⥤ C) (hp : p.IsFiberedInGroupoids)
    {a b x y z x' : F} (i : a ⟶ b) (u : a ⟶ x)
    (hbad : ∀ v : b ⟶ x, i ≫ v ≠ u)
    (r : x ⟶ y) (t : b ⟶ y) (hcomm : u ≫ r = i ≫ t)
    (s : z ⟶ y) [Mono (p.map s)]
    (g : p.obj b ⟶ p.obj z) (hg : g ≫ p.map s = p.map t)
    (α : x' ⟶ x) (β : x' ⟶ z)
    (hsquare : IsPullback (p.map α) (p.map β) (p.map r) (p.map s))
    (hcompat : α ≫ r = β ≫ s) :
    ¬ ∃ γ : z ⟶ x, β ≫ γ = α := by
  rintro ⟨γ, hγ⟩
  obtain ⟨v, ⟨hv, hvs⟩, _⟩ := hp.unique_lift s t g hg
  have hc : p.map u ≫ p.map r = p.map (i ≫ v) ≫ p.map s := by
    simp only [← p.map_comp, Category.assoc, hvs, hcomm]
  let q := hsquare.lift (p.map u) (p.map (i ≫ v)) hc
  obtain ⟨w, ⟨hw, hwα⟩, _⟩ := hp.unique_lift α u q
    (hsquare.lift_fst (p.map u) (p.map (i ≫ v)) hc)
  let : Mono s := mono_of_map_mono_of_fiberedInGroupoids p hp s
  have hwβ : w ≫ β = i ≫ v := by
    apply (cancel_mono s).mp
    calc
      (w ≫ β) ≫ s = w ≫ (α ≫ r) := by rw [Category.assoc, ← hcompat]
      _ = u ≫ r := by rw [← Category.assoc, hwα]
      _ = (i ≫ v) ≫ s := by simpa only [Category.assoc, hvs] using hcomm
  apply hbad (v ≫ γ)
  calc
    i ≫ (v ≫ γ) = (w ≫ β) ≫ γ := by rw [hwβ, Category.assoc]
    _ = u := by rw [Category.assoc, hγ, hwα]

private theorem exists_fiberSquare_object
    {C : Type (u + 1)} [Category.{u, u + 1} C] {F : Type v} [Category.{w, v} F]
    (p : F ⥤ C) (c : p.ChoiceOfPullbacks)
    {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W)
    (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j)
    (hE : (Deformation.Artin.fiberSquareComparison p c f g i j h).IsEquivalence)
    (d : CategoricalPullback (c.pullbackFunctor f) (c.pullbackFunctor g)) :
    ∃ z : p.Fiber Z,
      Nonempty ((Deformation.Artin.fiberSquareComparison p c f g i j h).obj z ≅ d) := by
  let E := Deformation.Artin.fiberSquareComparison p c f g i j h
  let : E.IsEquivalence := hE
  have hess : E.EssSurj := inferInstance
  obtain ⟨z, hz⟩ := hess.mem_essImage d
  exact ⟨z, hz⟩

private def fiberSquareData
    {C : Type (u + 1)} [Category.{u, u + 1} C] {F : Type v} [Category.{w, v} F]
    (p : F ⥤ C) (c : p.ChoiceOfPullbacks)
    {U V W _Z : C} (f : U ⟶ V) (g : U ⟶ W)
    (x : p.Fiber V) (y : p.Fiber W)
    (e : (c.pullbackFunctor f).obj x ≅ (c.pullbackFunctor g).obj y) :
    CategoricalPullback (c.pullbackFunctor f) (c.pullbackFunctor g) :=
  ⟨x, y, e⟩

noncomputable def artinianLocalAlgOverMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Λ : Type u} [CommRing Λ] (sMap : Spec (.of Λ) ⟶ S)
    {k : Type u} [Field k] [Algebra Λ k]
    {A C : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hA : B.Contains (Spec (.of A.carrier)))
    (hC : B.Contains (Spec (.of C.carrier))) (f : A ⟶ C) :
    artinianLocalAlgOver B S hS sMap C hC ⟶ artinianLocalAlgOver B S hS sMap A hA := by
  refine Over.homMk (ObjectProperty.homMk (X := B.obj hC) (Y := B.obj hA)
    (Spec.map (CommRingCat.ofHom f.hom.toRingHom))) ?_
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A.carrier)) ≫ sMap) =
    Spec.map (CommRingCat.ofHom (algebraMap Λ C.carrier)) ≫ sMap
  have hcomp : CommRingCat.ofHom (algebraMap Λ A.carrier) ≫
      CommRingCat.ofHom f.hom.toRingHom =
      CommRingCat.ofHom (algebraMap Λ C.carrier) := by
    ext x
    simp
  rw [← Category.assoc, ← Spec.map_comp, hcomp]

/-- The affine maps attached to composable Artinian algebra maps compose as expected. -/
theorem artinianLocalAlgOverMap_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Λ : Type u} [CommRing Λ] (sMap : Spec (.of Λ) ⟶ S)
    {k : Type u} [Field k] [Algebra Λ k]
    {A C D : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hA : B.Contains (Spec (.of A.carrier)))
    (hC : B.Contains (Spec (.of C.carrier)))
    (hD : B.Contains (Spec (.of D.carrier))) (f : A ⟶ C) (g : C ⟶ D) :
    artinianLocalAlgOverMap B S hS sMap hC hD g ≫
        artinianLocalAlgOverMap B S hS sMap hA hC f =
      artinianLocalAlgOverMap B S hS sMap hA hD (f ≫ g) := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom f.hom.toRingHom) =
    Spec.map (CommRingCat.ofHom (f ≫ g).hom.toRingHom)
  rw [← Spec.map_comp]
  congr 1

theorem artinianLocalAlgOverMap_id
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Λ : Type u} [CommRing Λ] (sMap : Spec (.of Λ) ⟶ S)
    {k : Type u} [Field k] [Algebra Λ k]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : B.Contains (Spec (.of A.carrier))) :
    artinianLocalAlgOverMap B S hS sMap hA hA (𝟙 A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (𝟙 _) = 𝟙 _
  simp

noncomputable def artinianLocalAlgOverIsoOfEq
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Λ : Type u} [CommRing Λ] (sMap : Spec (.of Λ) ⟶ S)
    {k : Type u} [Field k] [Algebra Λ k]
    {A C : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hA : B.Contains (Spec (.of A.carrier)))
    (hC : B.Contains (Spec (.of C.carrier))) (e : A = C) :
    artinianLocalAlgOver B S hS sMap A hA ≅ artinianLocalAlgOver B S hS sMap C hC := by
  cases e
  exact Iso.refl _

noncomputable def artinianLocalAlgOverIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Λ : Type u} [CommRing Λ] (sMap : Spec (.of Λ) ⟶ S)
    {k : Type u} [Field k] [Algebra Λ k]
    {A C : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hA : B.Contains (Spec (.of A.carrier)))
    (hC : B.Contains (Spec (.of C.carrier))) (e : A ≅ C) :
    artinianLocalAlgOver B S hS sMap A hA ≅ artinianLocalAlgOver B S hS sMap C hC := by
  let α := artinianLocalAlgOverMap B S hS sMap hC hA e.inv
  let β := artinianLocalAlgOverMap B S hS sMap hA hC e.hom
  refine ⟨α, β, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    dsimp [α, β, artinianLocalAlgOverMap, Over.Hom.left, Over.homMk,
      CostructuredArrow.homMk, ObjectProperty.homMk]
    change Spec.map (CommRingCat.ofHom e.inv.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom e.hom.hom.toRingHom) = 𝟙 _
    have hcomp : CommRingCat.ofHom e.hom.hom.toRingHom ≫
        CommRingCat.ofHom e.inv.hom.toRingHom = 𝟙 _ := by
      apply CommRingCat.hom_ext
      ext x
      have hx := congrArg (fun g : A ⟶ A => g.hom x) e.hom_inv_id
      exact hx
    rw [← Spec.map_comp]
    rw [hcomp]
    simp
  · apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    dsimp [α, β, artinianLocalAlgOverMap, Over.Hom.left, Over.homMk,
      CostructuredArrow.homMk, ObjectProperty.homMk]
    change Spec.map (CommRingCat.ofHom e.hom.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom e.inv.hom.toRingHom) = 𝟙 _
    have hcomp : CommRingCat.ofHom e.inv.hom.toRingHom ≫
        CommRingCat.ofHom e.hom.hom.toRingHom = 𝟙 _ := by
      apply CommRingCat.hom_ext
      ext x
      have hx := congrArg (fun g : C ⟶ C => g.hom x) e.inv_hom_id
      exact hx
    rw [← Spec.map_comp]
    rw [hcomp]
    simp

theorem artinianLocalAlgOverIsoOfEq_hom
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Λ : Type u} [CommRing Λ] (sMap : Spec (.of Λ) ⟶ S)
    {k : Type u} [Field k] [Algebra Λ k]
    {A C : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hA : B.Contains (Spec (.of A.carrier)))
    (hC : B.Contains (Spec (.of C.carrier))) (e : A = C) :
    (artinianLocalAlgOverIsoOfEq B S hS sMap hA hC e).hom =
      artinianLocalAlgOverMap B S hS sMap hC hA (eqToHom e.symm) := by
  cases e
  exact (artinianLocalAlgOverMap_id B S hS sMap A hA).symm

alias bigFppfOver_post_injective := post_inclusion_obj_injective

attribute [local implicit_reducible] Functor.ChoiceOfPullbacks.pullbackFunctor fiberSquareData
attribute [local implicit_reducible] pullbackStages
private theorem isCartesian_of_fiberedInGroupoids
    {C : Type (u + 1)} [Category.{u} C] {F : Type v} [Category.{w} F]
    (p : F ⥤ C) (hp : p.IsFiberedInGroupoids) {R S : C} {a b : F}
    (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ] : p.IsCartesian f φ := by
  subst_hom_lift p f φ
  exact every_arrow_cartesian_of_isFiberedInGroupoids p hp φ

private theorem pullbackFunctor_eqToHom_fac
    {C : Type (u + 1)} [Category.{u} C] {F : Type v} [Category.{w} F]
    (p : F ⥤ C) (c : p.ChoiceOfPullbacks)
    {U V : C} {f g : U ⟶ V} (h : f = g) (x : p.Fiber V) :
    Functor.Fiber.fiberInclusion.map
        ((eqToHom (congrArg c.pullbackFunctor h)).app x) ≫ c.map g x = c.map f x := by
  subst g
  simp

private theorem fiberSquareComparison_iso_fac
    {C : Type (u + 1)} [Category.{u} C] {F : Type v} [Category.{w} F]
    (p : F ⥤ C) (c : p.ChoiceOfPullbacks)
    {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
    (h : f ≫ i = g ≫ j) (z : p.Fiber Z) :
    Functor.Fiber.fiberInclusion.map
        ((Deformation.Artin.fiberSquareComparison p c f g i j h).obj z).iso.hom ≫
      c.map g (c.obj j z) ≫ c.map j z = c.map f (c.obj i z) ≫ c.map i z := by
  change Functor.Fiber.fiberInclusion.map
    ((c.objCompIso f i z).inv ≫
      (eqToHom (congrArg c.pullbackFunctor h)).app z ≫ (c.objCompIso g j z).hom) ≫
        c.map g (c.obj j z) ≫ c.map j z = _
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc, Functor.ChoiceOfPullbacks.objCompIso_hom_fac]
  rw [pullbackFunctor_eqToHom_fac p c h z]
  exact Functor.fiberIsoOfCartesian_inv_fac _ _ _ _ _

theorem exists_glued_object_of_fiberSquareComparison
    {C : Type (u + 1)} [Category.{u} C] {F : Type v} [Category.{w} F]
    (p : F ⥤ C) (hp : p.IsFiberedInGroupoids) (c : p.ChoiceOfPullbacks)
    {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
    (h : f ≫ i = g ≫ j)
    (hE : (Deformation.Artin.fiberSquareComparison p c f g i j h).IsEquivalence)
    (a : p.Fiber U) (x : p.Fiber V) (b : p.Fiber W)
    (α : a.1 ⟶ x.1) (β : a.1 ⟶ b.1)
    [p.IsHomLift f α] [p.IsHomLift g β] :
    ∃ (y : p.Fiber Z) (r : x.1 ⟶ y.1) (s : b.1 ⟶ y.1),
      p.IsHomLift i r ∧ p.IsHomLift j s ∧ α ≫ r = β ≫ s := by
  let ea : c.obj f x ≅ a := Functor.fiberIsoOfCartesian f (c.map f x) α
    inferInstance (isCartesian_of_fiberedInGroupoids p hp f α)
  let eb : a ≅ c.obj g b := Functor.fiberIsoOfCartesian g β (c.map g b)
    (isCartesian_of_fiberedInGroupoids p hp g β) inferInstance
  let d := fiberSquareData (_Z := Z) p c f g x b (ea ≪≫ eb)
  obtain ⟨y, ⟨e⟩⟩ := exists_fiberSquare_object p c f g i j h hE d
  let er : x ⟶ c.obj i y := e.inv.fst
  let es : b ⟶ c.obj j y := e.inv.snd
  let r : x.1 ⟶ y.1 := Functor.Fiber.fiberInclusion.map er ≫ c.map i y
  let s : b.1 ⟶ y.1 := Functor.Fiber.fiberInclusion.map es ≫ c.map j y
  have hr : p.IsHomLift i r := inferInstance
  have hs : p.IsHomLift j s := inferInstance
  refine ⟨y, r, s, hr, hs, ?_⟩
  have hea : Functor.Fiber.fiberInclusion.map ea.hom ≫ α = c.map f x :=
    Functor.fiberIsoOfCartesian_hom_fac _ _ _ _ _
  have heb : Functor.Fiber.fiberInclusion.map eb.hom ≫ c.map g b = β :=
    Functor.fiberIsoOfCartesian_hom_fac _ _ _ _ _
  let ey : c.obj f (c.obj i y) ≅ c.obj g (c.obj j y) :=
    ((Deformation.Artin.fiberSquareComparison p c f g i j h).obj y).iso
  have hey : Functor.Fiber.fiberInclusion.map ey.hom ≫
      c.map g (c.obj j y) ≫ c.map j y = c.map f (c.obj i y) ≫ c.map i y :=
    fiberSquareComparison_iso_fac p c f g i j h y
  have hew := congrArg (fun q => Functor.Fiber.fiberInclusion.map q ≫
    c.map g (c.obj j y) ≫ c.map j y) e.inv.w
  change Functor.Fiber.fiberInclusion.map (c.homMap f er ≫ ey.hom) ≫
      c.map g (c.obj j y) ≫ c.map j y =
    Functor.Fiber.fiberInclusion.map ((ea.hom ≫ eb.hom) ≫ c.homMap g es) ≫
      c.map g (c.obj j y) ≫ c.map j y at hew
  simp only [Functor.map_comp, Category.assoc, hey,
    Functor.ChoiceOfPullbacks.homMap_fac_assoc] at hew
  change c.map f x ≫ r = Functor.Fiber.fiberInclusion.map ea.hom ≫
    Functor.Fiber.fiberInclusion.map eb.hom ≫ c.map g b ≫ s at hew
  rw [← hea] at hew
  have : IsIso (Functor.Fiber.fiberInclusion.map ea.hom) := inferInstance
  apply (cancel_epi (Functor.Fiber.fiberInclusion.map ea.hom)).mp
  rw [← Category.assoc (Functor.Fiber.fiberInclusion.map eb.hom) (c.map g b) s,
    heb] at hew
  simpa only [Category.assoc] using hew

end Deformation.Artin

end
