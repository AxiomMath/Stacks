module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedCategory.EquivalenceInvariance
public import StacksFrontier.Deformation.CofiberedPresentation.Groupoid
public import StacksFrontier.Deformation.Groupoid.Smooth
public import StacksFrontier.Deformation.Smooth.Basic

/-!
# Smoothness of the groupoid in functors of a presentation

A smooth morphism from a set-valued functor to a category cofibered in groupoids over `𝒞_Λ`
gives a smooth groupoid in functors: the source and target maps of the groupoid produced by
`Deformation.presentationGroupoid` are both smooth.

The proof identifies the arrow functor of that groupoid with the two-fibre product of the
morphism with itself and the source and target maps with the two projections of that product,
which are smooth because one of them is a base change of a smooth morphism; smoothness then
transports along the identifications, all of which lie over identities in `𝒞_Λ`.

## Main results

* `Deformation.isSmooth_presentationGroupoid`: the groupoid in functors of a smooth
  presentation is smooth.

## Implementation notes

The set-valued functor is represented by its category of elements. The constructed groupoid is
`Deformation.presentationGroupoid`, whose source and target maps are the two projections of the
two-fibre product; its category of arrows is identified with that fibre product over the base
by `Deformation.PresentationGroupoid.fibreProductOverBase`, and the projection comparisons lift
identities in the base by `Deformation.PresentationGroupoid.sourceProjectionIso_vertical` and
`Deformation.PresentationGroupoid.targetProjectionIso_vertical`. The construction lifts the
values of the set-valued functor to a common universe with the morphisms of the total category,
so the transport across that universe lift is part of the argument.

Stacks 06L1 has two assertions: this smoothness statement, and the criterion saying that the
canonical morphism out of the quotient of the presentation is an equivalence. The latter is
`Deformation.presentationMorphism_isEquivalence_of_isSmooth_of_fiber_essSurj`, in
`StacksFrontier/Deformation/CofiberedPresentation/QuotientEquivalence.lean`, and it carries the
tag there; this file carries it for the smoothness assertion.

## References

* [Stacks Project, Tag 06L1](https://stacks.math.columbia.edu/tag/06L1)
-/

@[expose] public section

open CategoryTheory

namespace Deformation

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u v w uF vF uU uZ vZ uW vW uY vY uX vX uR uL

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

private theorem isSmooth_comp_equivalence_elements
    {R : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type uR}
    {𝓨 : BasedCategory.{vY, uY} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (E : (BasedCategory.ofFunctor (CategoryOfElements.π R)).obj ≌ 𝓨.obj)
    (hE : E.functor ⋙ 𝓨.p = CategoryOfElements.π R)
    {𝓩 : BasedCategory.{vZ, uZ} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (g : BasedFunctor 𝓨 𝓩)
    (hg : IsSmooth g) :
    IsSmooth
      (BasedFunctor.comp ({ toFunctor := E.functor, w := hE } :
        BasedFunctor (BasedCategory.ofFunctor (CategoryOfElements.π R))
          𝓨) g) := by
  classical
  dsimp [IsSmooth] at hg ⊢
  intro B A f₀ hf y x h hlift
  let e : BasedFunctor (BasedCategory.ofFunctor (CategoryOfElements.π R))
      𝓨 := { toFunctor := E.functor
             w := by simpa only [BasedCategory.ofFunctor] using hE }
  obtain ⟨z, hz, a, hhz, haz, hcomm⟩ := hg f₀ hf y (e.obj x) h hlift
  let x₀ : (BasedCategory.ofFunctor (CategoryOfElements.π R)).obj := E.inverse.obj z
  let i : E.functor.obj x₀ ≅ z := E.counitIso.app z
  have hx₀ : 𝓨.p.obj (e.obj x₀) = x₀.1 := Functor.congr_obj hE x₀
  let : 𝓨.p.IsHomLift f₀ hz := hhz
  have hzB : 𝓨.p.obj z = B := IsHomLift.domain_eq 𝓨.p f₀ hz
  let α : x₀.1 ⟶ B := eqToHom hx₀.symm ≫ 𝓨.p.map i.hom ≫ eqToHom hzB
  have hqI : IsIso (𝓨.p.map i.hom) := Functor.map_isIso 𝓨.p i.hom
  have hα : IsIso α := by dsimp [α]; infer_instance
  let : IsIso α := hα
  let x' : (BasedCategory.ofFunctor (CategoryOfElements.π R)).obj := ⟨B, R.map α x₀.2⟩
  let k₀ : x₀ ⟶ x' := ⟨α, rfl⟩
  have hm : (CategoryOfElements.π R).map k₀ = α := rfl
  have hk₀ : (CategoryOfElements.π R).IsHomLift α k₀ := by
    rw [← hm]
    exact IsHomLift.map (CategoryOfElements.π R) k₀
  let : (BasedCategory.ofFunctor (CategoryOfElements.π R)).p.IsHomLift α k₀ := by
    simpa only [BasedCategory.ofFunctor] using hk₀
  have hEk₀ : 𝓨.p.IsHomLift α (e.map k₀) := e.preserves_isHomLift α k₀
  let : 𝓨.p.IsHomLift α (e.map k₀) := hEk₀
  have hπiso : IsIso ((CategoryOfElements.π R).map k₀) := by simpa [hm] using hα
  let : IsIso ((CategoryOfElements.π R).map k₀) := hπiso
  let : (CategoryOfElements.π R).ReflectsIsomorphisms := inferInstance
  have hk₀_iso : IsIso k₀ := isIso_of_reflects_iso k₀ (CategoryOfElements.π R)
  have hi : 𝓨.p.IsHomLift α i.hom := by
    apply IsHomLift.of_fac 𝓨.p α i.hom hx₀ hzB
    rfl
  let j : e.obj x' ≅ z := (asIso (e.map k₀)).symm ≪≫ i
  have hj : 𝓨.p.IsHomLift (𝟙 B) j.hom := by
    show 𝓨.p.IsHomLift (𝟙 B) (inv (e.map k₀) ≫ i.hom)
    let : 𝓨.p.IsHomLift (asIso α).hom (asIso (e.map k₀)).hom := by
      simpa using hEk₀
    have hinv : 𝓨.p.IsHomLift (inv α) (inv (e.map k₀)) :=
      IsHomLift.inv_lift_inv 𝓨.p (asIso α) (asIso (e.map k₀))
    let _ : 𝓨.p.IsHomLift (inv α) (inv (e.map k₀)) := hinv
    let _ : 𝓨.p.IsHomLift α i.hom := hi
    have hcomp : 𝓨.p.IsHomLift (inv α ≫ α)
        (inv (e.map k₀) ≫ i.hom) := by infer_instance
    simpa using hcomp
  let : 𝓨.p.IsHomLift (𝟙 B) j.hom := hj
  have hfj : 𝓨.p.IsHomLift f₀ (j.hom ≫ hz) := by infer_instance
  let m : e.obj x' ⟶ e.obj x := j.hom ≫ hz
  let h' : x' ⟶ x := e.toFunctor.preimage m
  have hmap : e.map h' = m := by simp [h']
  have hEMap : 𝓨.p.IsHomLift f₀ (e.map h') := by rw [hmap]; exact hfj
  have hh' : (CategoryOfElements.π R).IsHomLift f₀ h' := by
    let : 𝓨.p.IsHomLift f₀ (e.map h') := hEMap
    exact e.isHomLift_map f₀ h'
  let a' : g.obj (e.obj x') ⟶ y := g.map j.hom ≫ a
  let : 𝓩.p.IsHomLift (𝟙 B) (g.map j.hom) := g.preserves_isHomLift (𝟙 B) j.hom
  let : 𝓩.p.IsHomLift (𝟙 B) a := haz
  have ha' : 𝓩.p.IsHomLift (𝟙 B) a' := by
    dsimp [a']
    infer_instance
  refine ⟨x', h', a', hh', ha', ?_⟩
  show g.map (e.map h') = (g.map j.hom ≫ a) ≫ h
  rw [hmap]
  dsimp [m]
  rw [Functor.map_comp, hcomm]
  exact (Category.assoc _ _ _).symm

private theorem isSmooth_of_vertical_natIso
    {𝓧 : BasedCategory.{vX, uX} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓨 : BasedCategory.{vY, uY} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (F G : BasedFunctor 𝓧 𝓨)
    (α : F.toFunctor ≅ G.toFunctor)
    (hα : ∀ x, 𝓨.p.IsHomLift (𝟙 (𝓧.p.obj x)) (α.hom.app x))
    (hF : IsSmooth F) : IsSmooth G := by
  dsimp [IsSmooth] at hF ⊢
  intro B A f₀ hf y x g hg
  have hxA : 𝓧.p.obj x = A :=
    (G.w_obj x).symm.trans (IsHomLift.codomain_eq 𝓨.p f₀ g)
  have hαinv : 𝓨.p.IsHomLift (𝟙 A) (α.inv.app x) := by
    have : 𝓨.p.IsHomLift (𝟙 A) (α.app x).hom := by
      rw [← hxA]
      exact hα x
    exact IsHomLift.lift_id_inv 𝓨.p A (α.app x)
  let : 𝓨.p.IsHomLift (𝟙 A) (α.inv.app x) := hαinv
  let hF' := g ≫ α.inv.app x
  have hF'lift : 𝓨.p.IsHomLift f₀ hF' := by
    let : 𝓨.p.IsHomLift f₀ g := hg
    infer_instance
  obtain ⟨x', h, a, hh, ha, hcomm⟩ := hF f₀ hf y x hF' hF'lift
  have hx'B : 𝓧.p.obj x' = B := IsHomLift.domain_eq 𝓧.p f₀ h
  have hαinv' : 𝓨.p.IsHomLift (𝟙 B) (α.inv.app x') := by
    have : 𝓨.p.IsHomLift (𝟙 B) (α.app x').hom := by
      rw [← hx'B]
      exact hα x'
    exact IsHomLift.lift_id_inv 𝓨.p B (α.app x')
  let a' := α.inv.app x' ≫ a
  have ha' : 𝓨.p.IsHomLift (𝟙 B) a' := by
    let : 𝓨.p.IsHomLift (𝟙 B) (α.inv.app x') := hαinv'
    let : 𝓨.p.IsHomLift (𝟙 B) a := ha
    dsimp [a']
    infer_instance
  refine ⟨x', h, a', hh, ha', ?_⟩
  dsimp [a', hF'] at hcomm ⊢
  calc
    G.map h = (G.map h ≫ α.inv.app x) ≫ α.hom.app x := by simp [Category.assoc]
    _ = (α.inv.app x' ≫ F.map h) ≫ α.hom.app x := by rw [α.inv.naturality h]
    _ = (α.inv.app x' ≫ a) ≫ g := by
      rw [hcomm]
      simp [Category.assoc]

private theorem isSmooth_comp_basedEquivalence
    {𝓧 𝓨 : BasedCategory.{vZ, uZ} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓩 : BasedCategory.{vW, uW} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (E : BasedCategory.Equivalence 𝓧 𝓨)
    (g : BasedFunctor 𝓨 𝓩)
    (hg : IsSmooth g) :
    IsSmooth (BasedFunctor.comp E.functor g) := by
  dsimp [IsSmooth] at hg ⊢
  intro B A f₀ hf y x h hlift
  obtain ⟨z, hz, a, hhz, haz, hcomm⟩ := hg f₀ hf y (E.functor.obj x) h hlift
  have hzB : 𝓨.p.obj z = B := IsHomLift.domain_eq 𝓨.p f₀ hz
  let i : E.functor.obj (E.inverse.obj z) ⟶ z := E.counitIso.hom.toNatTrans.app z
  have hi : 𝓨.p.IsHomLift (𝟙 B) i := by
    have h := E.counitIso.hom.app_isHomLift z
    rw [hzB] at h
    exact h
  let m : E.functor.obj (E.inverse.obj z) ⟶ E.functor.obj x := i ≫ hz
  let h' : E.inverse.obj z ⟶ x := E.equiv.functor.preimage m
  have hmap : E.functor.map h' = m := by
    show E.equiv.functor.map h' = m
    simpa only [h'] using E.equiv.functor.map_preimage m
  have hm : 𝓧.p.IsHomLift f₀ h' := by
    let : 𝓨.p.IsHomLift f₀ (E.functor.map h') := by
      rw [hmap]
      infer_instance
    exact E.functor.isHomLift_map f₀ h'
  let a' := g.map i ≫ a
  have ha' : 𝓩.p.IsHomLift (𝟙 B) a' := by
    let : 𝓩.p.IsHomLift (𝟙 B) (g.map i) := g.preserves_isHomLift (𝟙 B) i
    let : 𝓩.p.IsHomLift (𝟙 B) a := haz
    dsimp [a']
    infer_instance
  refine ⟨E.inverse.obj z, h', a', hm, ha', ?_⟩
  show g.map (E.functor.map h') = (g.map i ≫ a) ≫ h
  rw [hmap]
  dsimp [m]
  rw [Functor.map_comp, hcomm]
  exact (Category.assoc _ _ _).symm

private theorem isSmooth_comp_basedEquivalence_target
    {𝓧 : BasedCategory.{vX, uX} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓨 : BasedCategory.{vY, uY} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓩 : BasedCategory.{vZ, uZ} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (E : 𝓨.obj ≌ 𝓩.obj)
    (hbase : E.functor ⋙ 𝓩.p = 𝓨.p)
    (hunit : ∀ y, 𝓨.p.IsHomLift (𝟙 (𝓨.p.obj y)) (E.unitIso.hom.app y))
    (hvertical : ∀ y, 𝓩.p.IsHomLift (𝟙 (𝓩.p.obj y)) (E.counitIso.hom.app y))
    (hinverse : ∀ {a b : 𝓨.obj} (m : E.functor.obj a ⟶ E.functor.obj b)
      {R S} (f : R ⟶ S), 𝓩.p.IsHomLift f m →
        𝓨.p.IsHomLift f (E.inverse.map m))
    (g : BasedFunctor 𝓧 𝓨)
    (hg : IsSmooth g) :
    IsSmooth (BasedFunctor.comp g
      ({ toFunctor := E.functor, w := hbase } : BasedFunctor 𝓨 𝓩)) := by
  classical
  let F : BasedFunctor 𝓨 𝓩 := { toFunctor := E.functor, w := hbase }
  dsimp [IsSmooth, BasedFunctor.comp, F] at hg ⊢
  intro B A f₀ hf y x h hlift
  let y₀ := E.inverse.obj y
  let i := E.counitIso.hom.app y
  have hyB : 𝓩.p.obj y = B := by
    let : 𝓩.p.IsHomLift f₀ h := hlift
    exact IsHomLift.domain_eq 𝓩.p f₀ h
  have hi : 𝓩.p.IsHomLift (𝟙 B) i := by
    have h := hvertical y
    rw [hyB] at h
    exact h
  let h₀ : y₀ ⟶ E.inverse.obj (E.functor.obj (g.obj x)) :=
    E.unitIso.hom.app y₀ ≫ E.inverse.map (i ≫ h) 
  have hq : 𝓨.p.IsHomLift f₀ (E.inverse.map (i ≫ h)) := by
    have hqZ : 𝓩.p.IsHomLift f₀ (i ≫ h) := by
      let : 𝓩.p.IsHomLift (𝟙 B) i := hi
      let : 𝓩.p.IsHomLift f₀ h := hlift
      infer_instance
    exact hinverse (i ≫ h) f₀ hqZ
  have hy₀ : 𝓨.p.obj y₀ = B := by
    have hdom : 𝓨.p.obj (E.inverse.obj (E.functor.obj y₀)) = B :=
      IsHomLift.domain_eq 𝓨.p f₀ (E.inverse.map (i ≫ h))
    calc
      𝓨.p.obj y₀ = 𝓨.p.obj (E.inverse.obj (E.functor.obj y₀)) := by
        symm
        exact IsHomLift.codomain_eq 𝓨.p (𝟙 (𝓨.p.obj y₀)) (E.unitIso.hom.app y₀)
      _ = B := hdom
  have hunitY : 𝓨.p.IsHomLift (𝟙 B) (E.unitIso.hom.app y₀) := by
    rw [← hy₀]
    exact hunit y₀
  have hxA : 𝓨.p.obj (g.obj x) = A := by
    calc
      𝓨.p.obj (g.obj x) = 𝓩.p.obj (E.functor.obj (g.obj x)) :=
        (Functor.congr_obj hbase (g.obj x)).symm
      _ = A := IsHomLift.codomain_eq 𝓩.p f₀ h
  have hunitx : 𝓨.p.IsHomLift (𝟙 A) (E.unitIso.hom.app (g.obj x)) := by
    rw [← hxA]
    exact hunit (g.obj x)
  have hunitxInv : 𝓨.p.IsHomLift (𝟙 A) (E.unitIso.inv.app (g.obj x)) := by
    let : 𝓨.p.IsHomLift (𝟙 A) (E.unitIso.hom.app (g.obj x)) := hunitx
    have h := IsHomLift.lift_id_inv_isIso 𝓨.p A (E.unitIso.hom.app (g.obj x))
    have hinv : inv (E.unitIso.hom.app (g.obj x)) = E.unitIso.inv.app (g.obj x) := by
      apply (cancel_mono (E.unitIso.hom.app (g.obj x))).1
      simp
    rw [hinv] at h
    exact h
  have hh₀ : 𝓨.p.IsHomLift f₀ h₀ := by
    let : 𝓨.p.IsHomLift (𝟙 B) (E.unitIso.hom.app y₀) := hunitY
    let : 𝓨.p.IsHomLift f₀ (E.inverse.map (i ≫ h)) := hq
    dsimp [h₀]
    infer_instance
  have htriangleY : E.functor.map (E.unitIso.hom.app y₀) ≫
      E.counitIso.hom.app (E.functor.obj y₀) = 𝟙 (E.functor.obj y₀) := by
    simp
  have htriangleX : E.counitIso.inv.app (E.functor.obj (g.obj x)) ≫
      E.functor.map (E.unitIso.inv.app (g.obj x)) = 𝟙 (E.functor.obj (g.obj x)) :=
    E.counitIso_functor_comp (g.obj x)
  have hmapUnitInv : E.functor.map (E.unitIso.inv.app (g.obj x)) =
      E.counitIso.hom.app (E.functor.obj (g.obj x)) := by
    apply (cancel_epi (E.counitIso.inv.app (E.functor.obj (g.obj x)))).1
    calc
      E.counitIso.inv.app (E.functor.obj (g.obj x)) ≫
          E.functor.map (E.unitIso.inv.app (g.obj x)) = 𝟙 _ := htriangleX
      _ = E.counitIso.inv.app (E.functor.obj (g.obj x)) ≫
            E.counitIso.hom.app (E.functor.obj (g.obj x)) := by simp
  have hnat := E.counitIso.hom.naturality (i ≫ h)
  have hnat' : E.functor.map (E.inverse.map (i ≫ h)) ≫
      E.counitIso.hom.app (E.functor.obj (g.obj x)) =
      E.counitIso.hom.app (E.functor.obj y₀) ≫ (i ≫ h) := by
    exact hnat
  have hh₀map : E.functor.map h₀ ≫ E.counitIso.hom.app (E.functor.obj (g.obj x)) =
      i ≫ h := by
    dsimp [h₀]
    rw [Functor.map_comp]
    calc
      (E.functor.map (E.unitIso.hom.app y₀) ≫
          E.functor.map (E.inverse.map (i ≫ h))) ≫
          E.counitIso.hom.app (E.functor.obj (g.obj x))
          = E.functor.map (E.unitIso.hom.app y₀) ≫
              (E.counitIso.hom.app (E.functor.obj y₀) ≫ (i ≫ h)) := by
                  simp only [Category.assoc]
                  rw [hnat']
      _ = i ≫ h := by
        rw [← Category.assoc, htriangleY]
        simp
  obtain ⟨x', h', a, hh', ha, hcomm⟩ := hg f₀ hf y₀ x
    (h₀ ≫ E.unitIso.inv.app (g.obj x)) (by
      let : 𝓨.p.IsHomLift f₀ h₀ := hh₀
      let : 𝓨.p.IsHomLift (𝟙 A) (E.unitIso.inv.app (g.obj x)) := hunitxInv
      infer_instance)
  have hx'B : 𝓨.p.obj (g.obj x') = B := by
    have hbase' : 𝓧.p.obj x' = B := by
      let : 𝓧.p.IsHomLift f₀ h' := hh'
      exact IsHomLift.domain_eq 𝓧.p f₀ h'
    calc
      𝓨.p.obj (g.obj x') = 𝓧.p.obj x' := g.w_obj x'
      _ = B := hbase'
  let a' : E.functor.obj (g.obj x') ⟶ y := E.functor.map a ≫ i
  have ha' : 𝓩.p.IsHomLift (𝟙 B) a' := by
    have haY : 𝓨.p.IsHomLift (𝟙 B) a := by
      exact ha
    let : 𝓨.p.IsHomLift (𝟙 B) a := haY
    have haY' : 𝓨.p.IsHomLift (𝟙 (𝓨.p.obj (g.obj x'))) a := by
      rw [hx'B]
      exact ha
    let : 𝓨.p.IsHomLift (𝟙 (𝓨.p.obj (g.obj x'))) a := haY'
    let : 𝓩.p.IsHomLift (𝟙 B) (E.functor.map a) :=
      BasedFunctor.preserves_isHomLift ({ toFunctor := E.functor, w := hbase } : BasedFunctor 𝓨 𝓩)
        (𝟙 B) a
    let : 𝓩.p.IsHomLift (𝟙 B) i := hi
    dsimp [a']
    infer_instance
  refine ⟨x', h', a', hh', ha', ?_⟩
  have hunitComm : E.functor.map (h₀ ≫ E.unitIso.inv.app (g.obj x)) = i ≫ h := by
    rw [Functor.map_comp, hmapUnitInv]
    exact hh₀map
  calc
    E.functor.map (g.map h') =
        E.functor.map (a ≫ h₀ ≫ E.unitIso.inv.app (g.obj x)) := by rw [← hcomm]
    _ = (E.functor.map a ≫ E.functor.map (h₀ ≫ E.unitIso.inv.app (g.obj x))) := by
      rw [Functor.map_comp]
    _ = a' ≫ h := by
      dsimp [a']
      rw [hunitComm]
      simp [Category.assoc]


private def uliftElementsBasedFunctor
    {C : Type u} [Category.{v} C]
    (U : C ⥤ Type uU) :
    BasedFunctor
      (BasedCategory.ofFunctor (CategoryOfElements.π U))
      (BasedCategory.ofFunctor
        (CategoryOfElements.π (U ⋙ uliftFunctor.{uL, uU}))) where
  toFunctor := (uliftElementsEquivalence U).functor
  w := rfl

private def uliftElementsInverseBasedFunctor
    {C : Type u} [Category.{v} C]
    (U : C ⥤ Type uU) :
    BasedFunctor
      (BasedCategory.ofFunctor
        (CategoryOfElements.π (U ⋙ uliftFunctor.{uL, uU})))
      (BasedCategory.ofFunctor (CategoryOfElements.π U)) where
  toFunctor := (uliftElementsEquivalence U).inverse
  w := rfl

private theorem uliftElementsCounitVertical
    {C : Type u} [Category.{v} C]
    (U : C ⥤ Type uU) (x : (U ⋙ uliftFunctor.{uL, uU}).Elements) :
    (BasedCategory.ofFunctor
      (CategoryOfElements.π (U ⋙ uliftFunctor.{uL, uU}))).p.IsHomLift
        (𝟙 ((CategoryOfElements.π (U ⋙ uliftFunctor.{uL, uU})).obj x))
        ((uliftElementsEquivalence U).counitIso.hom.app x) := by
  show (BasedCategory.ofFunctor
    (CategoryOfElements.π (U ⋙ uliftFunctor.{uL, uU}))).p.IsHomLift
      (𝟙 ((CategoryOfElements.π (U ⋙ uliftFunctor.{uL, uU})).obj x)) (𝟙 x)
  exact IsHomLift.id rfl

private theorem uliftElementsUnitVertical
    {C : Type u} [Category.{v} C]
    (U : C ⥤ Type uU) (x : U.Elements) :
    (BasedCategory.ofFunctor (CategoryOfElements.π U)).p.IsHomLift
      (𝟙 ((CategoryOfElements.π U).obj x))
      ((uliftElementsEquivalence U).unitIso.hom.app x) := by
  show (BasedCategory.ofFunctor (CategoryOfElements.π U)).p.IsHomLift
    (𝟙 ((CategoryOfElements.π U).obj x)) (𝟙 x)
  exact IsHomLift.id rfl

private theorem uliftElementsInverseMapIsHomLift
    {C : Type u} [Category.{v} C]
    (U : C ⥤ Type uU) {a b : (U ⋙ uliftFunctor.{uL, uU}).Elements}
    (m : a ⟶ b) {R S : C} (f : R ⟶ S)
    (hm : (CategoryOfElements.π (U ⋙ uliftFunctor.{uL, uU})).IsHomLift f m) :
    (CategoryOfElements.π U).IsHomLift f
      ((uliftElementsEquivalence U).inverse.map m) := by
  let E := uliftElementsEquivalence U
  let : (CategoryOfElements.π (U ⋙ uliftFunctor.{uL, uU})).IsHomLift f m := hm
  have hdom : (CategoryOfElements.π U).obj (E.inverse.obj a) = R := by
    dsimp [E, uliftElementsEquivalence]
    exact IsHomLift.domain_eq (CategoryOfElements.π (U ⋙ uliftFunctor.{uL, uU})) f m
  have hcod : (CategoryOfElements.π U).obj (E.inverse.obj b) = S := by
    dsimp [E, uliftElementsEquivalence]
    exact IsHomLift.codomain_eq (CategoryOfElements.π (U ⋙ uliftFunctor.{uL, uU})) f m
  exact IsHomLift.of_fac' (CategoryOfElements.π U) f (E.inverse.map m) hdom hcod
    (IsHomLift.fac' (CategoryOfElements.π (U ⋙ uliftFunctor.{uL, uU})) f m)

private def twoFibreProductSwapBased
    {X : Type uX} [Category.{vX} X]
    {S : Type uY} [Category.{vY} S]
    {C : Type u} [Category.{v} C]
    (pX : X ⥤ C) (pS : S ⥤ C)
    (F : X ⥤ S) :
    BasedCategory.Equivalence
      (BasedCategory.ofFunctor
        (TwoFibreProductOver.structureFunctor pX pX pS F F))
      (BasedCategory.ofFunctor
        (TwoFibreProductOver.structureFunctor pX pX pS F F)) := by
  let swapObj : TwoFibreProductOver pX pX pS F F →
      TwoFibreProductOver pX pX pS F F := fun P => {
    base := P.base
    x := P.y
    y := P.x
    hx := P.hy
    hy := P.hx
    iso := P.iso.symm
    vertical := by
      let : pS.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
      exact IsHomLift.lift_id_inv pS P.base P.iso
  }
  let swap : TwoFibreProductOver pX pX pS F F ⥤
      TwoFibreProductOver pX pX pS F F := {
    obj := swapObj
    map := fun {P Q} g => {
      hbase := g.hbase
      a := g.b
      b := g.a
      ha := g.hb
      hb := g.ha
      w := by
        apply (cancel_mono Q.iso.hom).1
        have hl : (F.map g.b ≫ Q.iso.symm.hom) ≫ Q.iso.hom = F.map g.b := by simp
        have hr : (P.iso.symm.hom ≫ F.map g.a) ≫ Q.iso.hom = F.map g.b := by
          calc
            (P.iso.symm.hom ≫ F.map g.a) ≫ Q.iso.hom =
                P.iso.symm.hom ≫ (F.map g.a ≫ Q.iso.hom) := by simp [Category.assoc]
            _ = P.iso.symm.hom ≫ (P.iso.hom ≫ F.map g.b) := by rw [g.w]
            _ = F.map g.b := by simp
        exact hl.trans hr.symm
    }
    map_id := by
      intro P
      apply TwoFibreProductOver.Hom.ext' <;> rfl
    map_comp := by
      intro P Q R g h
      apply TwoFibreProductOver.Hom.ext' <;> rfl
  }
  let Q := BasedCategory.ofFunctor
    (TwoFibreProductOver.structureFunctor pX pX pS F F)
  let e : Q ⥤ᵇ Q := {
    toFunctor := swap
    w := rfl
  }
  let α : (e.comp e).toFunctor ≅ (BasedFunctor.id Q).toFunctor := Iso.refl _
  have hα : ∀ P, Q.p.IsHomLift (𝟙 (Q.p.obj P)) (α.hom.app P) := by
    intro P
    change Q.p.IsHomLift (𝟙 (Q.p.obj P)) (𝟙 P)
    exact IsHomLift.id rfl
  exact {
    functor := e
    inverse := e
    unitIso := BasedNatIso.mkNatIso α hα
    counitIso := BasedNatIso.mkNatIso α hα
  }


/-- A morphism of the category of elements lying over an identity of the base lifts it. -/
private theorem isHomLift_id_of_map_eq_eqToHom {X : Type uX} [Category.{vX} X]
    {C : Type u} [Category.{v} C] (p : X ⥤ C) {a b : X} (φ : a ⟶ b) {T : C}
    (ha : p.obj a = T) (hb : p.obj b = T) (h : p.map φ = eqToHom (ha.trans hb.symm)) :
    p.IsHomLift (𝟙 T) φ := by
  apply IsHomLift.of_fac' p _ φ ha hb
  simp [h]

/-- Smoothness of a functor into the lifted category of elements follows from smoothness of its
composite with the inverse of the universe-lift equivalence, up to a vertical isomorphism. -/
private theorem isSmooth_of_natIso_comp_uliftInverse
    {𝓧 : BasedCategory.{vX, uX} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {R : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type uU}
    (K : BasedFunctor 𝓧 (BasedCategory.ofFunctor (CategoryOfElements.π R)))
    (G : BasedFunctor 𝓧
      (BasedCategory.ofFunctor (CategoryOfElements.π (R ⋙ uliftFunctor.{uL, uU}))))
    (α : K.toFunctor ≅ (BasedFunctor.comp G (uliftElementsInverseBasedFunctor R)).toFunctor)
    (hα : ∀ x, (BasedCategory.ofFunctor (CategoryOfElements.π R)).p.IsHomLift
      (𝟙 (𝓧.p.obj x)) (α.hom.app x))
    (hK : IsSmooth K) : IsSmooth G := by
  have h := isSmooth_comp_basedEquivalence_target
    (𝓨 := BasedCategory.ofFunctor (CategoryOfElements.π R))
    (𝓩 := BasedCategory.ofFunctor (CategoryOfElements.π (R ⋙ uliftFunctor.{uL, uU})))
    (uliftElementsEquivalence R) rfl
    (uliftElementsUnitVertical.{_, _, _, uL} R) (uliftElementsCounitVertical R)
    (fun m _ _ f hm => uliftElementsInverseMapIsHomLift R m f hm)
    (BasedFunctor.comp G (uliftElementsInverseBasedFunctor R))
    (isSmooth_of_vertical_natIso K _ α hα hK)
  refine isSmooth_of_vertical_natIso
    (BasedFunctor.comp (BasedFunctor.comp G (uliftElementsInverseBasedFunctor R))
      (uliftElementsBasedFunctor R)) G
    (Functor.isoWhiskerLeft G.toFunctor (uliftElementsEquivalence R).counitIso)
    (fun x => ?_) (by simpa [BasedFunctor.comp, uliftElementsInverseBasedFunctor,
      uliftElementsBasedFunctor] using h)
  have h := uliftElementsCounitVertical R (G.obj x)
  rwa [show (CategoryOfElements.π (R ⋙ uliftFunctor.{uL, uU})).obj (G.obj x) = 𝓧.p.obj x
    from G.w_obj x] at h

variable {F : Type uF} [Category.{vF} F]
variable (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
variable (U : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type uU)
variable (f : BasedFunctor
  (BasedCategory.ofFunctor (CategoryOfElements.π U))
  (BasedCategory.ofFunctor p))

/-- A smooth presentation has a smooth associated groupoid in functors.

This is one of the two covering declarations of Stacks 06L1; the other is the equivalence
criterion for the quotient morphism,
`Deformation.presentationMorphism_isEquivalence_of_isSmooth_of_fiber_essSurj`. See the
implementation notes. -/
@[stacks 06L1 "smooth_groupoid"]
theorem isSmooth_presentationGroupoid
    (hp : IsCofiberedInGroupoids p)
    (hf : IsSmooth f) :
    GroupoidInFunctors.IsSmooth
      ((presentationGroupoid p U f.toFunctor f.w hp).toGroupoidInFunctors) :=
  by
    classical
    let P := presentationGroupoid p U f.toFunctor f.w hp
    let : Category (TwoFibreProductOver
        (CategoryOfElements.π U) (CategoryOfElements.π U) p f.toFunctor f.toFunctor) :=
      TwoFibreProductOver.instCategory
    let Q := twoFibreProductBasedCategory f f
    let snd := twoFibreProductSnd f f
    let e : BasedFunctor (BasedCategory.ofFunctor (CategoryOfElements.π P.arrows)) Q :=
      { toFunctor := P.fibreProductEquivalence.functor
        w := P.fibreProductOverBase }
    have hsnd : IsSmooth snd :=
      isSmooth_twoFibreProductSnd hp f f hf
    let hsrc := isSmooth_comp_equivalence_elements (R := P.arrows) (𝓨 := Q)
      P.fibreProductEquivalence P.fibreProductOverBase snd hsnd
    have hsourceVertical : ∀ x,
        (BasedCategory.ofFunctor (CategoryOfElements.π U)).p.IsHomLift
          (𝟙 ((BasedCategory.ofFunctor (CategoryOfElements.π P.arrows)).p.obj x))
          (P.sourceProjectionIso.hom.app x) := fun x =>
      isHomLift_id_of_map_eq_eqToHom _ _
        ((P.fibreProductEquivalence.functor.obj x).hy.trans
          (Functor.congr_obj P.fibreProductOverBase x)) rfl
        (P.sourceProjectionIso_vertical x)
    have hsource : IsSmooth (elementsBasedFunctor P.source) :=
      isSmooth_of_natIso_comp_uliftInverse (BasedFunctor.comp e snd) _
        P.sourceProjectionIso hsourceVertical hsrc
    let eswap := twoFibreProductSwapBased (pX := CategoryOfElements.π U)
      (pS := p) (F := f.toFunctor)
    let fst : BasedFunctor Q (BasedCategory.ofFunctor (CategoryOfElements.π U)) :=
      { toFunctor := TwoFibreProductOver.fst
          (CategoryOfElements.π U) (CategoryOfElements.π U) p f.toFunctor f.toFunctor
        w := TwoFibreProductOver.fst_comp_eq }
    have hfst : IsSmooth fst := isSmooth_comp_basedEquivalence eswap snd hsnd
    let htar := isSmooth_comp_equivalence_elements (R := P.arrows) (𝓨 := Q)
      P.fibreProductEquivalence P.fibreProductOverBase fst hfst
    have htargetVertical : ∀ x,
        (BasedCategory.ofFunctor (CategoryOfElements.π U)).p.IsHomLift
          (𝟙 ((BasedCategory.ofFunctor (CategoryOfElements.π P.arrows)).p.obj x))
          (P.targetProjectionIso.hom.app x) := fun x =>
      isHomLift_id_of_map_eq_eqToHom _ _
        ((P.fibreProductEquivalence.functor.obj x).hx.trans
          (Functor.congr_obj P.fibreProductOverBase x)) rfl
        (P.targetProjectionIso_vertical x)
    have htarget : IsSmooth (elementsBasedFunctor P.target) :=
      isSmooth_of_natIso_comp_uliftInverse (BasedFunctor.comp e fst) _
        P.targetProjectionIso htargetVertical htar
    exact ⟨hsource, htarget⟩

end Deformation

end
