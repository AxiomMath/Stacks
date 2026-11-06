module

public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Groupoid.Basic
public import StacksFrontier.Deformation.Smooth.Basic

/-!
# Smooth groupoids in functors on the base category

A groupoid in functors on the base category is smooth when its source and target morphisms are;
the quotient morphism of a smooth groupoid is then smooth.

## Main definitions

* `elementsBasedFunctor` is the based functor between categories of elements induced by a
  natural transformation of set-valued functors.
* `GroupoidInFunctors.IsSmooth` is smoothness of a groupoid in functors.
* `quotientBasedFunctor` views the canonical quotient morphism as a functor over the category of
  Artinian local algebras.

## Main results

* `isSmooth_iff_source` compares groupoid smoothness with source smoothness.
* `source_isSmooth_iff_target` compares source and target smoothness.
* `source_isSmooth_iff_quotient` compares source and quotient-morphism smoothness.

## References

* [Stacks Project, Tag 06KI](https://stacks.math.columbia.edu/tag/06KI)
* [Stacks Project, Tag 06KL](https://stacks.math.columbia.edu/tag/06KL)
-/

@[expose] public section

namespace Deformation

/-! ### Smooth groupoids in functors -/

section
open CategoryTheory
universe u v w z

/-- The based functor between categories of elements induced by a natural transformation of
set-valued functors. -/
@[implicit_reducible, simps] public def elementsBasedFunctor {C : Type u} [Category.{v} C] {F H :
  Functor.{v, z} C (Type z)} (α : F ⟶ H) : BasedFunctor (BasedCategory.ofFunctor
    (Functor.Elements.π F)) (BasedCategory.ofFunctor (Functor.Elements.π H)) where
  toFunctor := NatTrans.mapElements α

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A groupoid in functors is smooth when both its source and target morphisms are smooth. -/
@[stacks 06KI]
public abbrev GroupoidInFunctors.IsSmooth (G : GroupoidInFunctors
  (ArtinianLocalAlgCat.{u, v, w} Λ k)) : Prop := Deformation.IsSmooth (elementsBasedFunctor
    G.source) ∧ Deformation.IsSmooth (elementsBasedFunctor G.target)

end

/-! ### Smoothness of a groupoid and its quotient morphism -/

section
open CategoryTheory
universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The quotient morphism of a groupoid in functors, as a functor over the base. -/
public noncomputable def quotientBasedFunctor
    (G : GroupoidInFunctors (ArtinianLocalAlgCat.{u, v, w} Λ k)) :
    BasedFunctor
      (BasedCategory.ofFunctor (Functor.Elements.π G.objects))
      (BasedCategory.ofFunctor
        (Grothendieck.forget (evaluationFunctor G))) where
  toFunctor := quotientMorphism G
  w := quotientMorphism_over G

/-- Transporting an arrow of the groupoid evaluated at `T` along equalities of its source and
of its target leaves the underlying element of the arrow functor unchanged. -/
public theorem evaluationArrowEquiv_val_transport
    {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    {x x' y y' : G.Evaluation T} (hx : x = x') (hy : y = y') (f : x ⟶ y) :
    (G.evaluationArrowEquiv T x' y' (eqToHom hx.symm ≫ f ≫ eqToHom hy)).1 =
      (G.evaluationArrowEquiv T x y f).1 := by
  cases hx
  cases hy
  simp

private theorem inverseArrow_involutive
    {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) (T : C) (a : G.arrows.obj T) :
    inverseArrow G T (inverseArrow G T a) = a := by
  let : Groupoid (G.objects.obj T) := G.evaluationGroupoid T
  let x := G.source.app T a
  let y := G.target.app T a
  let E₁ := G.evaluationArrowEquiv T x y
  let E₂ := G.evaluationArrowEquiv T y x
  let E₁' := G.evaluationArrowEquiv T
    (G.target.app T (inverseArrow G T a))
    (G.source.app T (inverseArrow G T a))
  let E₂' := G.evaluationArrowEquiv T
    (G.source.app T (inverseArrow G T a))
    (G.target.app T (inverseArrow G T a))
  let α : x ⟶ y := E₁.symm ⟨a, rfl, rfl⟩
  have hs := inverseArrow_source G T a
  have ht := inverseArrow_target G T a
  have hβ : E₂.symm ⟨inverseArrow G T a, hs, ht⟩ = Groupoid.inv α := by
    apply E₂.injective
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]
    rfl
  have hγ : E₂'.symm ⟨inverseArrow G T a, rfl, rfl⟩ =
      eqToHom hs ≫ (E₂.symm ⟨inverseArrow G T a, hs, ht⟩) ≫ eqToHom ht.symm := by
    apply E₂'.injective
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]
    show inverseArrow G T a =
      (E₂' (eqToHom hs ≫
        (E₂.symm ⟨inverseArrow G T a, hs, ht⟩) ≫ eqToHom ht.symm)).1
    rw [evaluationArrowEquiv_val_transport G T hs.symm ht.symm
      (E₂.symm ⟨inverseArrow G T a, hs, ht⟩)]
    exact (congrArg Subtype.val (Equiv.apply_symm_apply E₂
      ⟨inverseArrow G T a, hs, ht⟩)).symm
  show (E₁' (Groupoid.inv
    (E₂'.symm ⟨inverseArrow G T a, rfl, rfl⟩))).1 = a
  have hfinal : (E₁' (eqToHom ht ≫ α ≫ eqToHom hs.symm)).1 = a := by
    have he : eqToHom ht = eqToHom ht.symm.symm := rfl
    rw [he, evaluationArrowEquiv_val_transport G T ht.symm hs.symm α]
    exact congrArg Subtype.val (Equiv.apply_symm_apply E₁ ⟨a, rfl, rfl⟩)
  rw [hγ, hβ, show Groupoid.inv (eqToHom hs ≫ Groupoid.inv α ≫ eqToHom ht.symm) =
      eqToHom ht ≫ α ≫ eqToHom hs.symm by
    simp [Category.assoc, IsIso.inv_comp]]
  exact hfinal

private theorem inverseArrow_naturality
    {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) {T S : C} (f : T ⟶ S)
    (a : G.arrows.obj T) :
    G.arrows.map f (inverseArrow G T a) =
      inverseArrow G S (G.arrows.map f a) := by
  let i := (existsUnique_inverse G).choose
  have hi := (existsUnique_inverse G).choose_spec.1
  calc
    G.arrows.map f (inverseArrow G T a) = G.arrows.map f (i.app T a) :=
      congrArg (G.arrows.map f) (hi T a).symm
    _ = i.app S (G.arrows.map f a) := (NatTrans.naturality_apply i f a).symm
    _ = inverseArrow G S (G.arrows.map f a) := hi S (G.arrows.map f a)

/-- If inversion of arrows swaps `s` and `t`, smoothness of `s` implies smoothness of `t`. -/
private theorem isSmooth_of_inverseArrow_swap
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : GroupoidInFunctors (ArtinianLocalAlgCat.{u, v, w} Λ k)) (s t : G.arrows ⟶ G.objects)
    (hst : ∀ T a, s.app T (inverseArrow G T a) = t.app T a)
    (hts : ∀ T a, t.app T (inverseArrow G T a) = s.app T a) :
    Deformation.IsSmooth (elementsBasedFunctor s) →
      Deformation.IsSmooth (elementsBasedFunctor t) := by
  intro hsource B A f hf y x g hg
  rcases y with @⟨B₀, y₀⟩
  rcases x with @⟨A₀, a₀⟩
  cases hg
  let f₀ : B₀ ⟶ A₀ := g.hom
  let aᵢ := inverseArrow G A₀ a₀
  have hgprop := g.map_val
  change G.objects.map g.hom y₀ = t.app A₀ a₀ at hgprop
  let gᵢ := Functor.Elements.homMk (x := G.objects.elementsMk B₀ y₀)
      (y := G.objects.elementsMk A₀ (s.app A₀ aᵢ)) f₀ (by
        simpa [aᵢ, hst] using hgprop)
  have hgᵢ : (Functor.Elements.π G.objects).IsHomLift f₀ gᵢ :=
    IsHomLift.map (p := Functor.Elements.π G.objects) gᵢ
  obtain ⟨b, hb, c, hhb, hhc, hcomm⟩ :=
    hsource f₀ hf (G.objects.elementsMk B₀ y₀) (G.arrows.elementsMk A₀ aᵢ) gᵢ hgᵢ
  rcases b with @⟨B₁, b₀⟩
  let : (Functor.Elements.π G.arrows).IsHomLift f₀ hb := hhb
  let : (Functor.Elements.π G.objects).IsHomLift (𝟙 B₀) c := hhc
  have hB : B₁ = B₀ := IsHomLift.domain_eq (p := Functor.Elements.π G.arrows) f₀ hb
  cases hB
  have hcbase : c.hom = 𝟙 B₀ := by
    simpa [elementsBasedFunctor, Functor.Elements.π,
      NatTrans.mapElements] using
      (IsHomLift.fac (p := Functor.Elements.π G.objects) (𝟙 B₀) c).symm
  have hbase : hb.hom = f₀ := by
    simpa [Functor.Elements.π] using
      (IsHomLift.fac (p := Functor.Elements.π G.arrows) f₀ hb).symm
  have hsource_b : s.app B₀ b₀ = y₀ := by
    simpa [hcbase, NatTrans.mapElements, G.objects.map_id_apply] using c.map_val
  let bᵢ := inverseArrow G B₀ b₀
  have hmap_b : G.arrows.map f₀ bᵢ = a₀ := by
    calc
      G.arrows.map f₀ bᵢ = inverseArrow G A₀ (G.arrows.map f₀ b₀) :=
        inverseArrow_naturality G f₀ b₀
      _ = inverseArrow G A₀ aᵢ := by rw [← hbase, hb.map_val]
      _ = a₀ := inverseArrow_involutive G A₀ a₀
  let h' := Functor.Elements.homMk (x := G.arrows.elementsMk B₀ bᵢ)
    (y := G.arrows.elementsMk A₀ a₀) f₀ hmap_b
  let c' := Functor.Elements.homMk
    (x := G.objects.elementsMk B₀ (t.app B₀ bᵢ)) (y := G.objects.elementsMk B₀ y₀) (𝟙 B₀) (by
      rw [G.objects.map_id_apply, hts, hsource_b])
  refine ⟨G.arrows.elementsMk B₀ bᵢ, h', c', IsHomLift.map (p := Functor.Elements.π G.arrows) h',
    IsHomLift.map (p := Functor.Elements.π G.objects) c', ?_⟩
  apply Functor.Elements.hom_ext
  show g.hom = (𝟙 B₀) ≫ g.hom
  simp

private theorem source_isSmooth_implies_target
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : GroupoidInFunctors (ArtinianLocalAlgCat.{u, v, w} Λ k)) :
    Deformation.IsSmooth (elementsBasedFunctor G.source) →
      Deformation.IsSmooth (elementsBasedFunctor G.target) :=
  isSmooth_of_inverseArrow_swap G _ _ (inverseArrow_source G) (inverseArrow_target G)

private theorem target_isSmooth_implies_source
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : GroupoidInFunctors (ArtinianLocalAlgCat.{u, v, w} Λ k)) :
    Deformation.IsSmooth (elementsBasedFunctor G.target) →
      Deformation.IsSmooth (elementsBasedFunctor G.source) :=
  isSmooth_of_inverseArrow_swap G _ _ (inverseArrow_target G) (inverseArrow_source G)

set_option backward.isDefEq.respectTransparency false in
private theorem source_isSmooth_implies_quotient
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : GroupoidInFunctors (ArtinianLocalAlgCat.{u, v, w} Λ k)) :
    Deformation.IsSmooth (elementsBasedFunctor G.source) →
      Deformation.IsSmooth (quotientBasedFunctor G) := by
  intro hsource B A f hf y x g hg
  rcases y with @⟨B₀, y₀⟩
  rcases x with @⟨A₀, x₀⟩
  cases hg
  change (⟨B₀, y₀⟩ : Grothendieck (evaluationFunctor G)) ⟶
    ⟨A₀, x₀⟩ at g
  let f₀ : B₀ ⟶ A₀ := g.base
  have hf₀ : Function.Surjective f₀.hom := hf
  let hfiber : (evaluationMap G f₀).obj y₀ ⟶ x₀ := g.fiber
  let e₀ := G.evaluationArrowEquiv A₀ ((evaluationMap G f₀).obj y₀) x₀
  let aa := e₀ hfiber
  let a₀ := aa.1
  have ha₀ : G.source.app A₀ a₀ = G.objects.map f₀ y₀ := aa.2.1
  have ht₀ : G.target.app A₀ a₀ = x₀ := aa.2.2
  let g' := Functor.Elements.homMk (x := G.objects.elementsMk B₀ y₀)
    (y := G.objects.elementsMk A₀ (G.source.app A₀ a₀)) f₀ (by simp [ha₀])
  have hg' : (Functor.Elements.π G.objects).IsHomLift f₀ g' :=
    IsHomLift.map (p := Functor.Elements.π G.objects) g'
  obtain ⟨b, hb, c, hhb, hhc, hcomm⟩ :=
    hsource f₀ hf₀ (G.objects.elementsMk B₀ y₀) (G.arrows.elementsMk A₀ a₀) g' hg'
  rcases b with @⟨B₁, b₀⟩
  let : (Functor.Elements.π G.arrows).IsHomLift f₀ hb := hhb
  let : (Functor.Elements.π G.objects).IsHomLift (𝟙 B₀) c := hhc
  have hB : B₁ = B₀ := IsHomLift.domain_eq (p := Functor.Elements.π G.arrows) f₀ hb
  cases hB
  have hcbase : c.hom = 𝟙 B₀ := by
    simpa [elementsBasedFunctor, Functor.Elements.π,
      NatTrans.mapElements] using
      (IsHomLift.fac (p := Functor.Elements.π G.objects) (𝟙 B₀) c).symm
  have hbase' : hb.hom = f₀ := by
    simpa [Functor.Elements.π] using
      (IsHomLift.fac (p := Functor.Elements.π G.arrows) f₀ hb).symm
  have hsource_b : G.source.app B₀ b₀ = y₀ := by
    simpa [hcbase] using c.map_val
  have hmap_b : G.arrows.map f₀ b₀ = a₀ := by
    rw [← hbase', hb.map_val]
  have htargetmap : G.objects.map f₀ (G.target.app B₀ b₀) = x₀ := by
    rw [← G.target.naturality_apply f₀ b₀, hmap_b, ht₀]
  let x' := G.objects.elementsMk B₀ (G.target.app B₀ b₀)
  let xA : G.objects.Elements := G.objects.elementsMk A₀ x₀
  let h' := Functor.Elements.homMk (F := G.objects) (x := x') (y := xA) f₀ htargetmap
  let : Groupoid (G.objects.obj B₀) := G.evaluationGroupoid B₀
  let ca : G.target.app B₀ b₀ ⟶ y₀ :=
    Groupoid.inv ((G.evaluationArrowEquiv B₀ _ _).symm ⟨b₀, rfl, rfl⟩) ≫
      eqToHom hsource_b
  let c' : (quotientBasedFunctor G).toFunctor.obj x' ⟶
      (⟨B₀, y₀⟩ : Grothendieck (evaluationFunctor G)) :=
    { base := 𝟙 B₀
      fiber := eqToHom (G.objects.map_id_apply B₀ (G.target.app B₀ b₀)) ≫ ca }
  refine ⟨x', h', c', IsHomLift.map (p := Functor.Elements.π G.objects) h',
    IsHomLift.map (p := Grothendieck.forget (evaluationFunctor G)) c', ?_⟩
  cases hsource_b
  let u := (G.evaluationArrowEquiv B₀ (G.source.app B₀ b₀) (G.target.app B₀ b₀)).symm
    ⟨b₀, rfl, rfl⟩
  let eA := G.evaluationArrowEquiv A₀
    ((evaluationMap G f₀).obj (G.source.app B₀ b₀))
    ((evaluationMap G f₀).obj (G.target.app B₀ b₀))
  have hu : (evaluationMap G f₀).map u =
      eA.symm ⟨a₀, ha₀, ht₀.trans htargetmap.symm⟩ := by
    apply eA.injective
    simp only [Equiv.apply_symm_apply]
    apply Subtype.ext
    conv_lhs => rw [evaluationMap_map_arrow]
    simp only [u, Equiv.apply_symm_apply]
    exact hmap_b
  have hα : hfiber = e₀.symm ⟨a₀, ha₀, ht₀⟩ := (Equiv.symm_apply_apply e₀ hfiber).symm
  have hcomp : (evaluationMap G f₀).map u ≫ eqToHom htargetmap = hfiber := by
    rw [hu, hα]
    apply e₀.injective
    simp only [Equiv.apply_symm_apply]
    apply Subtype.ext
    simpa only [eA, e₀, evaluationMap_obj, Equiv.apply_symm_apply,
      eqToHom_refl, Category.id_comp] using
      (evaluationArrowEquiv_val_transport G A₀ rfl htargetmap
        (eA.symm ⟨a₀, ha₀, ht₀.trans htargetmap.symm⟩))
  have hcomp' : (evaluationMap G f₀).map u ≫ eqToHom htargetmap = g.fiber := by
    simpa [hfiber] using hcomp
  let : Groupoid (G.objects.obj A₀) := G.evaluationGroupoid A₀
  apply Grothendieck.ext
  case w_base =>
    show f₀ = (𝟙 B₀) ≫ g.base
    simp [f₀]
  case w_fiber =>
    rw [Grothendieck.comp_fiber]
    simp only [quotientBasedFunctor, quotientMorphism,
      evaluationFunctor, c', ca]
    simpa [Functor.map_comp, eqToHom_map, Category.assoc] using hcomp'

set_option backward.isDefEq.respectTransparency false in
private theorem quotient_isSmooth_implies_target
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : GroupoidInFunctors (ArtinianLocalAlgCat.{u, v, w} Λ k)) :
    Deformation.IsSmooth (quotientBasedFunctor G) →
      Deformation.IsSmooth (elementsBasedFunctor G.target) := by
  let (T : ArtinianLocalAlgCat.{u, v, w} Λ k) :
      Groupoid ((evaluationFunctor G).obj T) :=
    G.evaluationGroupoid T
  intro hquot B A f hf y x g hg
  rcases y with @⟨B₀, y₀⟩
  rcases x with @⟨A₀, a₀⟩
  cases hg
  let f₀ : B₀ ⟶ A₀ := g.hom
  have hgprop := g.map_val
  change G.objects.map f₀ y₀ = G.target.app A₀ a₀ at hgprop
  let xA : G.objects.Elements := G.objects.elementsMk A₀ (G.source.app A₀ a₀)
  let : Groupoid (G.objects.obj A₀) := G.evaluationGroupoid A₀
  let aArrow := (G.evaluationArrowEquiv A₀ (G.source.app A₀ a₀)
    (G.target.app A₀ a₀)).symm ⟨a₀, rfl, rfl⟩
  let α := eqToHom hgprop ≫ Groupoid.inv aArrow
  let yG : Grothendieck (evaluationFunctor G) := ⟨B₀, y₀⟩
  let gQ : yG ⟶ (quotientBasedFunctor G).toFunctor.obj xA := ⟨f₀, α⟩
  have hgQ : (Grothendieck.forget (evaluationFunctor G)).IsHomLift f₀ gQ :=
    IsHomLift.map (p := Grothendieck.forget (evaluationFunctor G)) gQ
  obtain ⟨xB, h, c, hh, hc, hcomm⟩ := hquot f₀ hf yG xA gQ hgQ
  rcases xB with @⟨B₁, z₀⟩
  let : (Functor.Elements.π G.objects).IsHomLift f₀ h := hh
  let : (Grothendieck.forget (evaluationFunctor G)).IsHomLift (𝟙 B₀) c := hc
  have hB : B₁ = B₀ := IsHomLift.domain_eq (p := Functor.Elements.π G.objects) f₀ h
  cases hB
  have hcbase : c.base = 𝟙 B₀ :=
    (IsHomLift.fac (p := Grothendieck.forget (evaluationFunctor G)) (𝟙 B₀) c).symm
  have hval : h.hom = f₀ := by
    simpa [Functor.Elements.π] using
      (IsHomLift.fac (p := Functor.Elements.π G.objects) f₀ h).symm
  have hhprop : G.objects.map f₀ z₀ = G.source.app A₀ a₀ := by
    simpa [elementsBasedFunctor, NatTrans.mapElements, hval] using h.map_val
  let : Groupoid (G.objects.obj B₀) := G.evaluationGroupoid B₀
  have hsourceFiber : z₀ =
      ((evaluationFunctor G).map c.base).toFunctor.obj
        ((quotientBasedFunctor G).obj (G.objects.elementsMk B₀ z₀)).fiber := by
    simp [quotientBasedFunctor, quotientMorphism, evaluationFunctor, evaluationMap, hcbase]
  let δ : z₀ ⟶ y₀ := eqToHom hsourceFiber ≫ c.fiber
  let b₀ := (G.evaluationArrowEquiv B₀ z₀ y₀ δ).1
  have hbsource : G.source.app B₀ b₀ = z₀ :=
    (G.evaluationArrowEquiv B₀ z₀ y₀ δ).2.1
  have hbtgt : G.target.app B₀ b₀ = y₀ :=
    (G.evaluationArrowEquiv B₀ z₀ y₀ δ).2.2
  have hcomm' : (quotientMorphism G).map h = c ≫ gQ := hcomm
  have hcomm_fiber := Grothendieck.congr hcomm'
  let xA₀ := (evaluationMap G h.hom).obj z₀
  change (eqToHom h.map_val : xA₀ ⟶ G.source.app A₀ a₀) = _ at hcomm_fiber
  rw [Grothendieck.comp_fiber c gQ] at hcomm_fiber
  have hdomain : G.objects.map h.hom z₀ = G.objects.map f₀ z₀ :=
    congrArg (fun q => G.objects.map q z₀) hval
  have hcat₀ : eqToHom h.map_val = eqToHom hdomain ≫
      (evaluationMap G f₀).map δ ≫ α := by
    simpa [quotientBasedFunctor, quotientMorphism,
      evaluationFunctor, hval, hcbase, gQ, hsourceFiber, δ,
      Functor.map_comp, eqToHom_map, eqToHom_refl, eqToHom_trans_assoc,
      Category.assoc] using hcomm_fiber
  have hleft : eqToHom h.map_val = eqToHom hdomain ≫ eqToHom hhprop :=
    (eqToHom_trans hdomain hhprop).symm
  have hcat : eqToHom hhprop = (evaluationMap G f₀).map δ ≫ α := by
    rw [hleft] at hcat₀
    apply (cancel_epi (eqToHom hdomain)).mp
    simpa only [Category.assoc] using hcat₀
  have hmap_b : G.arrows.map f₀ b₀ = a₀ := by
    let yA₀ := G.objects.map f₀ y₀
    let aArrow' := eqToHom hhprop ≫ aArrow ≫ eqToHom hgprop.symm
    have hcat' : aArrow' ≫ α = eqToHom hhprop := by
      simp [aArrow', α, Category.assoc]
    have hcancel : (evaluationMap G f₀).map δ = aArrow' := by
      apply (cancel_mono α).mp
      rw [← hcat, hcat']
    have hδ : (G.evaluationArrowEquiv A₀ (G.objects.map f₀ z₀) yA₀
        ((evaluationMap G f₀).map δ)).1 = G.arrows.map f₀ b₀ := by
      simpa [evaluationMap_obj, b₀] using
        evaluationMap_map_arrow G f₀ δ
    have ha : (G.evaluationArrowEquiv A₀ (G.objects.map f₀ z₀) yA₀ aArrow').1 = a₀ :=
      (evaluationArrowEquiv_val_transport G A₀ hhprop.symm hgprop.symm aArrow).trans
        (by simp [aArrow])
    rw [← hδ, hcancel, ha]
  let b := G.arrows.elementsMk B₀ b₀
  let h' := Functor.Elements.homMk (x := b) (y := G.arrows.elementsMk A₀ a₀) f₀ hmap_b
  let c' := Functor.Elements.homMk
    (x := G.objects.elementsMk B₀ (G.target.app B₀ b₀)) (y := G.objects.elementsMk B₀ y₀) (𝟙 B₀) (by
      rw [G.objects.map_id_apply, hbtgt])
  refine ⟨b, h', c', IsHomLift.map (p := Functor.Elements.π G.arrows) h',
    IsHomLift.map (p := Functor.Elements.π G.objects) c', ?_⟩
  apply Functor.Elements.hom_ext
  show g.hom = (𝟙 B₀) ≫ g.hom
  simp

/-- A groupoid in functors is smooth exactly when its source morphism is smooth. -/
@[stacks 06KL "smooth groupoid iff smooth source"]
public theorem isSmooth_iff_source
    (G : GroupoidInFunctors (ArtinianLocalAlgCat.{u, v, w} Λ k)) :
      GroupoidInFunctors.IsSmooth G ↔
      Deformation.IsSmooth (elementsBasedFunctor G.source) :=
  ⟨And.left, fun h => ⟨h, source_isSmooth_implies_target G h⟩⟩

/-- Smoothness of the source and target morphisms of a groupoid in functors are equivalent. -/
@[stacks 06KL "smooth source iff smooth target"]
public theorem source_isSmooth_iff_target
    (G : GroupoidInFunctors (ArtinianLocalAlgCat.{u, v, w} Λ k)) :
    Deformation.IsSmooth (elementsBasedFunctor G.source) ↔
      Deformation.IsSmooth (elementsBasedFunctor G.target) :=
  ⟨source_isSmooth_implies_target G, target_isSmooth_implies_source G⟩

/-- The source morphism is smooth exactly when the quotient morphism is smooth. -/
@[stacks 06KL "smooth source iff smooth quotient morphism"]
public theorem source_isSmooth_iff_quotient
    (G : GroupoidInFunctors (ArtinianLocalAlgCat.{u, v, w} Λ k)) :
    Deformation.IsSmooth (elementsBasedFunctor G.source) ↔
      Deformation.IsSmooth (quotientBasedFunctor G) :=
  ⟨source_isSmooth_implies_quotient G,
    target_isSmooth_implies_source G ∘ quotient_isSmooth_implies_target G⟩

end

end Deformation
