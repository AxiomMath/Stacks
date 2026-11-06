module

public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValued
public import Mathlib.CategoryTheory.ShrinkYoneda
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsBigFppfRepresentable
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsBigFppfSmall
public import StacksFrontier.Deformation.Artin.AlgebraicSpaceCriterion
public import StacksFrontier.Deformation.Artin.FunctorFormalObject
public import StacksFrontier.Deformation.Artin.FunctorOpenVersality
public import StacksFrontier.Deformation.Artin.FunctorTangentSpace
public import StacksFrontier.Deformation.ArtinCriteria.TangentSpace
public import StacksFrontier.Deformation.Artin.FiniteDimensional.TangentTransfer
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Morphism
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FunctorForm

/-!
# Artin's criterion on the locally Noetherian étale site (Stacks 0GE7)

Let `S` be a locally Noetherian scheme and `F` a set-valued functor on the locally Noetherian
site `(Noetherian/S)_étale` (`AlgebraicGeometry.LocallyNoetherianOver`). Stacks 0GE7 says that if
the diagonal of `F` is representable, `F` satisfies Artin's axioms `[-1]`–`[5]` in the form of
Section 0GE6, and the local rings of `S` at its finite type points are G-rings, then `F` is the
restriction of a unique limit preserving algebraic space on the big fppf site of `S`.

The source's proof extends `F` by Stacks 0GE3, checks the diagonal of the extension by Stacks 0GE5,
observes that axioms `[-1]`, `[2]`, `[3]`, `[4]`, `[5]` only involve locally Noetherian test
objects, and applies Stacks 07Y1. This file provides the comparison steps and the assembly.

## Main definitions

* `AlgebraicGeometry.LocallyNoetherianOver.SatisfiesArtinAxioms`: Artin's axioms for a functor on
  the locally Noetherian site, one field per axiom, each the predicate the corresponding tag of
  the contraction section is proved in.
* `AlgebraicGeometry.LocallyNoetherianOver.elementsComparison`: the comparison of the categories
  fibred in sets of `F` and of an extension `F'`.
* `AlgebraicGeometry.LocallyNoetherianOver.elementsToFibredCategoryULift`: the comparison of the
  category fibred in sets of `F` with the category fibred in groupoids of a `Type u`-valued
  functor `G` on the big fppf site whose restriction, lifted to the universe of `F`, is `F`.

## Main results

* `AlgebraicGeometry.LocallyNoetherianOver.existsUnique_isAlgebraicSpace_restriction_iso`:
  Stacks 0GE7.
* `CategoryTheory.Presheaf.uliftYoneda_relativelyRepresentable_diag_of_iso`,
  `AlgebraicGeometry.LocallyNoetherianOver.satisfiesRSFunctor_of_satisfiesRS`,
  `LocallyNoetherianOver.finiteDimensional_tangentSpaceArtinian_bigElementsToOver`,
  `AlgebraicGeometry.LocallyNoetherianOver.exists_eq_of_hasEffectiveFormalObjects`,
  `AlgebraicGeometry.LocallyNoetherianOver.openVersality_of_hasOpenVersality`: the axioms pass
  from `F` to an extension `F'`.
* `Deformation.isDeformationCategory_comp_of_surjective`: being a deformation category pulls back
  along a fully faithful functor surjective on objects; this is how the tangent spaces of the
  extension are compared with those of `F`.
* `AlgebraicGeometry.LocallyNoetherianOver.existsUnique_iso_of_restriction_iso`: uniqueness of the
  extension.

## References

* [Stacks Project, Tag 0GE6](https://stacks.math.columbia.edu/tag/0GE6)
* [Stacks Project, Tag 0GE7](https://stacks.math.columbia.edu/tag/0GE7)
* [Stacks Project, Tag 07Y1](https://stacks.math.columbia.edu/tag/07Y1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v v₁ u₁ u

/-- The components of an isomorphism of set-valued functors are injective. -/
private theorem injective_hom_app {D : Type*} [Category D] {M N : D ⥤ Type w} (e : M ≅ N)
    (Z : D) : Function.Injective (e.hom.app Z) :=
  (e.app Z).toEquiv.injective

namespace CategoryTheory.Presheaf

variable {C : Type u₁} [Category.{v₁} C] {P Q : Cᵒᵖ ⥤ Type (max w v₁)}

/-- Representing the equalizer of two sections is invariant under isomorphisms of presheaves. -/
lemma representsEqualizer_iff_of_iso (e : P ≅ Q) {X Y : C} (snd : X ⟶ Y) (a b : P.obj (op Y)) :
    RepresentsEqualizer P snd a b ↔
      RepresentsEqualizer Q snd (e.hom.app _ a) (e.hom.app _ b) := by
  have key : ∀ (Z : C) (φ : Z ⟶ Y), Q.map φ.op (e.hom.app _ a) = Q.map φ.op (e.hom.app _ b) ↔
      P.map φ.op a = P.map φ.op b := fun Z φ => by
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
    exact (injective_hom_app e _).eq_iff
  exact ⟨fun h => ⟨h.1, fun Z φ => (key Z φ).trans (h.2 Z φ)⟩,
    fun h => ⟨h.1, fun Z φ => (key Z φ).symm.trans (h.2 Z φ)⟩⟩

/-- Representability of the diagonal is invariant under isomorphisms of presheaves. -/
theorem uliftYoneda_relativelyRepresentable_diag_of_iso (e : P ≅ Q)
    (h : (uliftYoneda.{w} (C := C)).relativelyRepresentable (diag P)) :
    (uliftYoneda.{w} (C := C)).relativelyRepresentable (diag Q) := by
  rw [uliftYoneda_relativelyRepresentable_diag_iff] at h ⊢
  intro Y a b
  obtain ⟨X, snd, hX⟩ := h Y (e.inv.app _ a) (e.inv.app _ b)
  refine ⟨X, snd, ?_⟩
  have := (representsEqualizer_iff_of_iso e snd _ _).1 hX
  simpa only [Iso.inv_hom_id_app_apply] using this

/-- Relative representability is invariant under an isomorphism of the embedding functors. -/
theorem _root_.CategoryTheory.Functor.relativelyRepresentable_of_iso {C D : Type*} [Category C]
    [Category D] {F G : C ⥤ D} (e : F ≅ G) {X Y : D} {f : X ⟶ Y}
    (h : F.relativelyRepresentable f) : G.relativelyRepresentable f := by
  intro a g
  obtain ⟨b, snd, fst, hpb⟩ := h (e.hom.app a ≫ g)
  refine ⟨b, snd, e.inv.app b ≫ fst, hpb.of_iso (e.app b) (Iso.refl _) (e.app a) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)⟩

variable {C : Type u₁} [Category.{v₁} C]

/-- The diagonal of a presheaf with values in the universe of the morphisms is representable
for the Yoneda embedding exactly when the equalizers of pairs of sections are representable. -/
theorem yoneda_relativelyRepresentable_diag_iff {P : Cᵒᵖ ⥤ Type v₁} :
    (yoneda (C := C)).relativelyRepresentable (diag P) ↔
      ∀ (Y : C) (a b : P.obj (op Y)), ∃ (X : C) (snd : X ⟶ Y),
        RepresentsEqualizer.{0} P snd a b := by
  rw [← uliftYoneda_relativelyRepresentable_diag_iff]
  exact ⟨Functor.relativelyRepresentable_of_iso uliftYonedaIsoYoneda.{0}.symm,
    Functor.relativelyRepresentable_of_iso uliftYonedaIsoYoneda.{0}⟩

/-- Representing an equalizer is insensitive to lifting the values to a larger universe. -/
theorem representsEqualizer_comp_uliftFunctor_iff {P : Cᵒᵖ ⥤ Type v₁} {X Y : C} (snd : X ⟶ Y)
    (a b : P.obj (op Y)) :
    RepresentsEqualizer.{w} (P ⋙ uliftFunctor.{w}) snd (ULift.up a) (ULift.up b) ↔
      RepresentsEqualizer.{0} P snd a b := by
  refine ⟨fun h => ⟨h.1, fun Z φ => ?_⟩, fun h => ⟨h.1, fun Z φ => ?_⟩⟩
  · rw [← h.2 Z φ]
    exact ⟨fun hab => congrArg ULift.up hab, fun hab => congrArg ULift.down hab⟩
  · rw [← h.2 Z φ]
    exact ⟨fun hab => congrArg ULift.down hab, fun hab => congrArg ULift.up hab⟩

end CategoryTheory.Presheaf

namespace AlgebraicGeometry.LocallyNoetherianOver

open Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An Artinian local object of the big fppf site is locally Noetherian. -/
theorem isLocallyNoetherian_of_isArtinianLocal {X : BigFppfOver B S hS}
    (hX : IsArtinianLocal B S hS X) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj X) := by
  obtain ⟨h₁, h₂, h₃⟩ := hX
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj X, ⊤) := inferInstance
  exact isLocallyNoetherian_of_isOpenImmersion
    ((BigFppfOver.toScheme B S hS).obj X).isoSpec.hom

/-- **Condition (RS) passes from the locally Noetherian site to the big fppf site.** The pushout
squares of Artinian local schemes that condition (RS) quantifies over lie in the locally
Noetherian site. -/
theorem satisfiesRSFunctor_of_satisfiesRS {F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}
    {F : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type w}
    (e : (LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F' ≅ F)
    (hF : SatisfiesRS B S hS F) : SatisfiesRSFunctor B S hS F' := by
  intro X X' Y Y' i j i' j' w hX hX' hY hY' hX₁ hX'₁ hY₁ hY'₁ hci hpo a b hab
  let X₀ : LocallyNoetherianOver B S hS := ⟨X, isLocallyNoetherian_of_isArtinianLocal hX⟩
  let X'₀ : LocallyNoetherianOver B S hS := ⟨X', isLocallyNoetherian_of_isArtinianLocal hX'⟩
  let Y₀ : LocallyNoetherianOver B S hS := ⟨Y, isLocallyNoetherian_of_isArtinianLocal hY⟩
  let Y'₀ : LocallyNoetherianOver B S hS := ⟨Y', isLocallyNoetherian_of_isArtinianLocal hY'⟩
  let i₀ : X₀ ⟶ X'₀ := ObjectProperty.homMk i
  let j₀ : X₀ ⟶ Y₀ := ObjectProperty.homMk j
  let i'₀ : X'₀ ⟶ Y'₀ := ObjectProperty.homMk i'
  let j'₀ : Y₀ ⟶ Y'₀ := ObjectProperty.homMk j'
  have hinj := injective_hom_app e
  have hab' : F.map j₀.op (e.hom.app (op Y₀) a) = F.map i₀.op (e.hom.app (op X'₀) b) := by
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
    exact congrArg _ hab
  obtain ⟨t, ⟨ht₁, ht₂⟩, hu⟩ := hF i₀ j₀ i'₀ j'₀ (ObjectProperty.hom_ext _ w) hX hX' hY hY'
    hX₁ hX'₁ hY₁ hY'₁ hci hpo _ _ hab'
  refine ⟨e.inv.app (op Y'₀) t,
    ⟨@hinj (op Y₀) (F'.map j'.op (e.inv.app (op Y'₀) t)) a ?_,
      @hinj (op X'₀) (F'.map i'.op (e.inv.app (op Y'₀) t)) b ?_⟩,
    fun t' ht' => @hinj (op Y'₀) t' (e.inv.app (op Y'₀) t) ?_⟩
  · show e.hom.app (op Y₀) (((LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F').map j'₀.op
      (e.inv.app (op Y'₀) t)) = _
    rw [NatTrans.naturality_apply, Iso.inv_hom_id_app_apply, ht₁]
  · show e.hom.app (op X'₀) (((LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F').map i'₀.op
      (e.inv.app (op Y'₀) t)) = _
    rw [NatTrans.naturality_apply, Iso.inv_hom_id_app_apply, ht₂]
  · rw [Iso.inv_hom_id_app_apply]
    refine hu _ ⟨?_, ?_⟩
    · rw [← NatTrans.naturality_apply]
      exact congrArg _ ht'.1
    · rw [← NatTrans.naturality_apply]
      exact congrArg _ ht'.2

end AlgebraicGeometry.LocallyNoetherianOver

namespace Deformation.Artin

open AlgebraicGeometry

variable {S : Scheme.{u}} {X : Type u₁} [Category.{v₁} X] {X' : Type*} [Category X']

/-- The spectrum of an Artinian local algebra over `S` is locally Noetherian. -/
theorem isLocallyNoetherian_of_eq_spec {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k) (i : Spec (.of Λ) ⟶ S) {T : Over S}
    (h : T = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ i)) :
    IsLocallyNoetherian T.left := by
  subst h
  show IsLocallyNoetherian (Spec (.of A))
  infer_instance

/-- **Versality is detected on a full subcategory containing the Noetherian objects.** Let
`Φ : X ⥤ X'` be a fully faithful functor over `Sch/S` reaching every object of `X'` lying over a
locally Noetherian scheme. An object of `X` is versal at a point exactly when its image is: the
test objects of versality lie over spectra of Artinian local rings. -/
theorem isVersalAt_comp_iff (q' : X' ⥤ Over S) (Φ : X ⥤ X') [Φ.Full] [Φ.Faithful]
    (hsurj : ∀ y' : X', IsLocallyNoetherian (q'.obj y').left → ∃ y : X, Φ.obj y = y')
    (U : Over S) (u₀ : U.left) (x : X) (hx : (Φ ⋙ q').obj x = U) :
    IsVersalAt U (Φ ⋙ q') u₀ x hx ↔ IsVersalAt U q' u₀ (Φ.obj x) hx := by
  let := residueFieldAlgebra U u₀
  constructor
  · intro h A B f hf y' z' hy' hz' i' hi' a' ha'
    obtain ⟨y, rfl⟩ := hsurj y' (isLocallyNoetherian_of_eq_spec A _ hy')
    obtain ⟨z, rfl⟩ := hsurj z' (isLocallyNoetherian_of_eq_spec B _ hz')
    obtain ⟨b, hb⟩ := h A B f hf y z hy' hz' (Φ.preimage i')
      (by simpa only [Functor.comp_map, Functor.map_preimage] using hi') (Φ.preimage a')
      (by simpa only [Functor.comp_map, Functor.map_preimage] using ha')
    refine ⟨Φ.map b, ?_⟩
    rw [← Φ.map_preimage i', ← Functor.map_comp, hb, Functor.map_preimage]
  · intro h A B f hf y z hy hz i hi a ha
    obtain ⟨b, hb⟩ := h A B f hf (Φ.obj y) (Φ.obj z) hy hz (Φ.map i) hi (Φ.map a) ha
    refine ⟨Φ.preimage b, Φ.map_injective ?_⟩
    rw [Functor.map_comp, Functor.map_preimage, hb]

/-- **Openness of versality descends along a fully faithful functor** reaching every object over a
locally Noetherian scheme: the versal locus of an object over a finite type `S`-scheme is open
for `q'` once it is for `Φ ⋙ q'`. -/
private theorem openVersality_of_comp [IsLocallyNoetherian S] (q' : X' ⥤ Over S) (Φ : X ⥤ X')
    [Φ.Full] [Φ.Faithful]
    (hsurj : ∀ y' : X', IsLocallyNoetherian (q'.obj y').left → ∃ y : X, Φ.obj y = y')
    (h : ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : X) (hx : (Φ ⋙ q').obj x = U) (u₀ : U.left), IsFiniteTypePoint u₀ →
        IsVersalAt U (Φ ⋙ q') u₀ x hx →
        ∃ V : U.left.Opens, u₀ ∈ V.1 ∧ ∀ (u : U.left), u ∈ V.1 → IsFiniteTypePoint u →
          IsVersalAt U (Φ ⋙ q') u x hx) :
    ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : X') (hx : q'.obj x = U) (u₀ : U.left), IsFiniteTypePoint u₀ →
        IsVersalAt U q' u₀ x hx →
        ∃ V : U.left.Opens, u₀ ∈ V.1 ∧ ∀ (u : U.left), u ∈ V.1 → IsFiniteTypePoint u →
          IsVersalAt U q' u x hx := by
  intro U hU x hx u₀ hu₀ hv
  obtain ⟨y, rfl⟩ := hsurj x (by
    rw [hx]
    exact LocallyOfFiniteType.isLocallyNoetherian U.hom)
  obtain ⟨V, hV, hVu⟩ := h U hU y hx u₀ hu₀ ((isVersalAt_comp_iff q' Φ hsurj U u₀ y hx).2 hv)
  exact ⟨V, hV, fun u hu hfin =>
    (isVersalAt_comp_iff q' Φ hsurj U u y hx).1 (hVu u hu hfin)⟩

end Deformation.Artin

namespace Deformation

section Pullback

variable {C : Type*} [Category C] {𝓓 : Type*} [Category 𝓓] {𝓓' : Type*} [Category 𝓓']
  (Ψ : 𝓓 ⥤ 𝓓') [Ψ.Full] [Ψ.Faithful] (hsurj : ∀ d' : 𝓓', ∃ d : 𝓓, Ψ.obj d = d')

include hsurj in
/-- **Being fibred in groupoids pulls back along a fully faithful functor which is surjective on
objects.** -/
theorem isFiberedInGroupoids_comp_of_surjective {r : 𝓓' ⥤ C} (hr : r.IsFiberedInGroupoids) :
    (Ψ ⋙ r).IsFiberedInGroupoids where
  exists_lift {V U} f x hx := by
    obtain ⟨y', φ', hφ'⟩ := hr.exists_lift f (Ψ.obj x) hx
    obtain ⟨y, rfl⟩ := hsurj y'
    exact ⟨y, Ψ.preimage φ', isHomLift_of_comp_map Ψ f _ (by rwa [Functor.map_preimage])⟩
  unique_lift {x y z} φ ψ f hf := by
    obtain ⟨χ', ⟨hχ'₁, hχ'₂⟩, hu⟩ := hr.unique_lift (Ψ.map φ) (Ψ.map ψ) f hf
    refine ⟨Ψ.preimage χ', ⟨?_, Ψ.map_injective ?_⟩, fun χ hχ => Ψ.map_injective ?_⟩
    · show r.map (Ψ.map (Ψ.preimage χ')) = f
      rw [Functor.map_preimage, hχ'₁]
    · rw [Functor.map_comp, Functor.map_preimage, hχ'₂]
    · rw [Functor.map_preimage]
      exact hu _ ⟨hχ.1, by rw [← Functor.map_comp, hχ.2]⟩

include hsurj in
/-- **Being cofibred in groupoids pulls back along a fully faithful functor which is surjective
on objects.** -/
theorem isCofiberedInGroupoids_comp_of_surjective {r : 𝓓' ⥤ C}
    (hr : IsCofiberedInGroupoids r) : IsCofiberedInGroupoids (Ψ ⋙ r) :=
  isFiberedInGroupoids_comp_of_surjective Ψ.op (fun d' => by
    obtain ⟨d, hd⟩ := hsurj d'.unop
    exact ⟨Opposite.op d, congrArg Opposite.op hd⟩) hr

include hsurj in
/-- The fibres of the composite are equivalent to the fibres of the target projection. -/
theorem nonempty_fiber_equivalence_of_surjective (r : 𝓓' ⥤ C) (A : C) :
    Nonempty ((Ψ ⋙ r).Fiber A ≌ r.Fiber A) := by
  let G := fiberFunctorOfComp Ψ (q := r) A
  have : G.EssSurj := ⟨fun z => by
    obtain ⟨d, hd⟩ := hsurj z.1
    have hA : (Ψ ⋙ r).obj d = A := by
      show r.obj (Ψ.obj d) = A
      rw [hd]
      exact z.2
    exact ⟨⟨d, hA⟩, ⟨eqToIso (Subtype.ext hd)⟩⟩⟩
  have : G.IsEquivalence := { }
  exact ⟨G.asEquivalence⟩

include hsurj in
/-- **Condition (RS) pulls back along a fully faithful functor which is surjective on objects.** -/
theorem satisfiesRS_comp_of_surjective {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] {r : 𝓓' ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k} (h : SatisfiesRS r) :
    SatisfiesRS (Ψ ⋙ r) := by
  refine ⟨isCofiberedInGroupoids_comp_of_surjective Ψ hsurj h.1, fun {x₁ x₂ x} f₁ f₂ hf => ?_⟩
  obtain ⟨c', ⟨hc'⟩, ⟨hc'r⟩⟩ := h.2 (Ψ.map f₁) (Ψ.map f₂) hf
  obtain ⟨P, hP⟩ := hsurj c'.pt
  let g₁ : P ⟶ x₁ := Ψ.preimage (eqToHom hP ≫ c'.fst)
  let g₂ : P ⟶ x₂ := Ψ.preimage (eqToHom hP ≫ c'.snd)
  have hcond : g₁ ≫ f₁ = g₂ ≫ f₂ := Ψ.map_injective (by
    simp only [g₁, g₂, Functor.map_comp, Functor.map_preimage, Category.assoc, c'.condition])
  let c := PullbackCone.mk g₁ g₂ hcond
  have hΨ : IsLimit (c.map Ψ) := IsLimit.ofIsoLimit hc' (PullbackCone.ext (eqToIso hP.symm)
    (by
      show c'.fst = eqToHom hP.symm ≫ Ψ.map (Ψ.preimage (eqToHom hP ≫ c'.fst))
      rw [Functor.map_preimage, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp])
    (by
      show c'.snd = eqToHom hP.symm ≫ Ψ.map (Ψ.preimage (eqToHom hP ≫ c'.snd))
      rw [Functor.map_preimage, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]))
  refine ⟨c, ⟨isLimitOfReflects Ψ ((PullbackCone.isLimitMapConeEquiv c Ψ).symm hΨ)⟩, ⟨?_⟩⟩
  refine IsLimit.ofIsoLimit hc'r (PullbackCone.ext (r.mapIso (eqToIso hP.symm)) ?_ ?_)
  · show r.map c'.fst = r.map (eqToHom hP.symm) ≫ r.map (Ψ.map g₁)
    rw [← Functor.map_comp, Functor.map_preimage, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
  · show r.map c'.snd = r.map (eqToHom hP.symm) ≫ r.map (Ψ.map g₂)
    rw [← Functor.map_comp, Functor.map_preimage, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]

include hsurj in
/-- **Being a deformation category pulls back along a fully faithful functor which is surjective
on objects.** -/
theorem isDeformationCategory_comp_of_surjective {Λ : Type u} {k : Type w} [CommRing Λ]
    [Field k] [Algebra Λ k] {r : 𝓓' ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (h : IsDeformationCategory r) : IsDeformationCategory (Ψ ⋙ r) := by
  obtain ⟨E⟩ := nonempty_fiber_equivalence_of_surjective Ψ hsurj r (residueFieldObject Λ k)
  obtain ⟨E'⟩ := h.predeformation.specialFiber
  exact ⟨⟨isCofiberedInGroupoids_comp_of_surjective Ψ hsurj h.predeformation.cofibered,
      ⟨E.trans (E'.trans (Discrete.equivalence Equiv.punitEquivPUnit))⟩⟩,
    satisfiesRS_comp_of_surjective Ψ hsurj h.satisfiesRS⟩

end Pullback

end Deformation

namespace Deformation.Artin

open AlgebraicGeometry

section PredeformationComp

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {S : Scheme.{u}}
  (iΛ : Spec (.of Λ) ⟶ S) {X : Type u₁} [Category.{v₁} X] {X' : Type*} [Category X']
  (q' : X' ⥤ Over S) (Φ : X ⥤ X') (x₀ : X)
  (hx₀ : (Φ ⋙ q').obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- The image under `Φ` of a deformation of `x₀`. -/
def deformationObjectComp (a : DeformationObject iΛ (Φ ⋙ q') x₀ hx₀) :
    DeformationObject iΛ q' (Φ.obj x₀) hx₀ where
  algebra := a.algebra
  point := Φ.obj a.point
  arrow := Φ.map a.arrow
  base := a.base
  arrow_base := a.arrow_base

/-- The image under `Φ` of a morphism of deformations of `x₀`. -/
def deformationMorphismComp {a b : DeformationObject iΛ (Φ ⋙ q') x₀ hx₀}
    (f : DeformationMorphism iΛ (Φ ⋙ q') x₀ hx₀ a b) :
    DeformationMorphism iΛ q' (Φ.obj x₀) hx₀ (deformationObjectComp iΛ q' Φ x₀ hx₀ a)
      (deformationObjectComp iΛ q' Φ x₀ hx₀ b) where
  ringHom := f.ringHom
  arrow := Φ.map f.arrow
  triangle := by
    change Φ.map b.arrow ≫ Φ.map f.arrow = Φ.map a.arrow
    rw [← Φ.map_comp, f.triangle]
  arrow_base := f.arrow_base

/-- **The functor of predeformation categories induced by `Φ`**, for the composite projection
`Φ ⋙ q'`. -/
def predeformationComp :
    letI := (predeformationCategory iΛ (Φ ⋙ q') x₀ hx₀).category
    letI := (predeformationCategory iΛ q' (Φ.obj x₀) hx₀).category
    (predeformationCategory iΛ (Φ ⋙ q') x₀ hx₀).carrier ⥤
      (predeformationCategory iΛ q' (Φ.obj x₀) hx₀).carrier :=
  letI := (predeformationCategory iΛ (Φ ⋙ q') x₀ hx₀).category
  letI := (predeformationCategory iΛ q' (Φ.obj x₀) hx₀).category
  { obj := fun a => deformationObjectComp iΛ q' Φ x₀ hx₀ a
    map := fun f => deformationMorphismComp iΛ q' Φ x₀ hx₀ f
    map_id := fun _ => DeformationMorphism.ext_of_components iΛ q' (Φ.obj x₀) hx₀ rfl
      (Φ.map_id _)
    map_comp := fun _ _ => DeformationMorphism.ext_of_components iΛ q' (Φ.obj x₀) hx₀ rfl
      (Φ.map_comp _ _) }

/-- The functor `predeformationComp` commutes with the projections of the two predeformation
categories. -/
theorem predeformationComp_comp_projection :
    letI := (predeformationCategory iΛ (Φ ⋙ q') x₀ hx₀).category
    letI := (predeformationCategory iΛ q' (Φ.obj x₀) hx₀).category
    predeformationComp iΛ q' Φ x₀ hx₀ ⋙ (predeformationCategory iΛ q' (Φ.obj x₀) hx₀).projection =
      (predeformationCategory iΛ (Φ ⋙ q') x₀ hx₀).projection :=
  rfl

variable [Φ.Full] [Φ.Faithful]

/-- If `Φ` is fully faithful, then `predeformationComp` is faithful. -/
instance predeformationComp_faithful :
    letI := (predeformationCategory iΛ (Φ ⋙ q') x₀ hx₀).category
    letI := (predeformationCategory iΛ q' (Φ.obj x₀) hx₀).category
    (predeformationComp iΛ q' Φ x₀ hx₀).Faithful :=
  letI := (predeformationCategory iΛ (Φ ⋙ q') x₀ hx₀).category
  letI := (predeformationCategory iΛ q' (Φ.obj x₀) hx₀).category
  ⟨fun {a b} f g hfg => by
    have h₁ : (deformationMorphismComp iΛ q' Φ x₀ hx₀ f).ringHom =
        (deformationMorphismComp iΛ q' Φ x₀ hx₀ g).ringHom :=
      congrArg DeformationMorphism.ringHom hfg
    have h₂ : Φ.map (show DeformationMorphism iΛ (Φ ⋙ q') x₀ hx₀ a b from f).arrow =
        Φ.map (show DeformationMorphism iΛ (Φ ⋙ q') x₀ hx₀ a b from g).arrow :=
      congrArg DeformationMorphism.arrow hfg
    exact DeformationMorphism.ext_of_components iΛ (Φ ⋙ q') x₀ hx₀ h₁ (Φ.map_injective h₂)⟩

/-- If `Φ` is fully faithful, then `predeformationComp` is full. -/
instance predeformationComp_full :
    letI := (predeformationCategory iΛ (Φ ⋙ q') x₀ hx₀).category
    letI := (predeformationCategory iΛ q' (Φ.obj x₀) hx₀).category
    (predeformationComp iΛ q' Φ x₀ hx₀).Full :=
  letI := (predeformationCategory iΛ (Φ ⋙ q') x₀ hx₀).category
  letI := (predeformationCategory iΛ q' (Φ.obj x₀) hx₀).category
  ⟨fun {a b} g => by
    let g' : DeformationMorphism iΛ q' (Φ.obj x₀) hx₀ (deformationObjectComp iΛ q' Φ x₀ hx₀ a)
      (deformationObjectComp iΛ q' Φ x₀ hx₀ b) := g
    obtain ⟨χ, hχ⟩ := Φ.map_surjective g'.arrow
    let f : DeformationMorphism iΛ (Φ ⋙ q') x₀ hx₀ a b :=
      { ringHom := g'.ringHom
        arrow := χ
        triangle := Φ.map_injective (((Φ.map_comp _ _).trans
          (congrArg (Φ.map (show DeformationObject iΛ (Φ ⋙ q') x₀ hx₀ from b).arrow ≫ ·)
            hχ)).trans g'.triangle)
        arrow_base := by
          have := g'.arrow_base
          rw [← hχ] at this
          exact this }
    exact ⟨f, DeformationMorphism.ext_of_components iΛ q' (Φ.obj x₀) hx₀ rfl hχ⟩⟩

omit [Φ.Faithful] in
/-- If `Φ` is full and every object of `X'` lying over a locally Noetherian scheme is in the
image of `Φ`, then `predeformationComp` is surjective on objects. -/
theorem predeformationComp_surjective
    (hsurj : ∀ y' : X', IsLocallyNoetherian (q'.obj y').left → ∃ y : X, Φ.obj y = y')
    (d' : (predeformationCategory iΛ q' (Φ.obj x₀) hx₀).carrier) :
    ∃ d, (predeformationComp iΛ q' Φ x₀ hx₀).obj d = d' := by
  obtain ⟨A, y', arr, base, ab⟩ := (show DeformationObject iΛ q' (Φ.obj x₀) hx₀ from d')
  obtain ⟨y, rfl⟩ := hsurj y' (isLocallyNoetherian_of_eq_spec A iΛ base)
  obtain ⟨χ, hχ⟩ := Φ.map_surjective arr
  rw [← hχ] at ab
  refine ⟨(⟨A, y, χ, base, ab⟩ : DeformationObject iΛ (Φ ⋙ q') x₀ hx₀), ?_⟩
  exact deformationObject_ext_of_arrow_comp (halg := rfl) (hpoint := rfl) (by
    show Φ.map χ ≫ eqToHom rfl = arr
    rw [eqToHom_refl, Category.comp_id, hχ])

/-- **Finite-dimensionality of tangent spaces passes to a category reaching the same Noetherian
objects.** If the tangent spaces of the predeformation category of `x₀` for `Φ ⋙ q'` are
finite dimensional, in the form of the axiom
`AlgebraicGeometry.LocallyNoetherianOver.HasFiniteDimensionalTangentSpaces`, then so is the
tangent space of the predeformation category of `Φ.obj x₀` for `q'`, whenever the latter is a
deformation category: the induced functor of predeformation categories is fully faithful and
surjective on objects, so the source is a deformation category too and the tangent map is
surjective. -/
theorem finiteDimensional_tangentSpaceArtinian_of_comp
    (hsurj : ∀ y' : X', IsLocallyNoetherian (q'.obj y').left → ∃ y : X, Φ.obj y = y')
    (h : letI := (predeformationCategory iΛ (Φ ⋙ q') x₀ hx₀).category
      ∀ (hP : IsPredeformationCategory (BasedCategory.ofFunctor
          (predeformationCategory iΛ (Φ ⋙ q') x₀ hx₀).projection).p)
        (hS2 : SchlessingerConditionS2 (CategoryOfElements.π (isomorphismClasses
          (BasedCategory.ofFunctor (predeformationCategory iΛ (Φ ⋙ q') x₀ hx₀).projection)
            hP.cofibered))),
        letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor
            (predeformationCategory iΛ (Φ ⋙ q') x₀ hx₀).projection).p) := ⟨hP⟩
        letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π (isomorphismClasses
            (BasedCategory.ofFunctor (predeformationCategory iΛ (Φ ⋙ q') x₀ hx₀).projection)
              hP.cofibered))) := ⟨hS2⟩
        FiniteDimensional k (artinianTangentSpace Λ k (isomorphismClasses
          (BasedCategory.ofFunctor (predeformationCategory iΛ (Φ ⋙ q') x₀ hx₀).projection)
            hP.cofibered)))
    (hD' : letI := (predeformationCategory iΛ q' (Φ.obj x₀) hx₀).category
      IsDeformationCategory (predeformationCategory iΛ q' (Φ.obj x₀) hx₀).projection) :
    letI := (predeformationCategory iΛ q' (Φ.obj x₀) hx₀).category
    letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor
        (predeformationCategory iΛ q' (Φ.obj x₀) hx₀).projection).p) := ⟨hD'.predeformation⟩
    letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π (isomorphismClasses
        (BasedCategory.ofFunctor (predeformationCategory iΛ q' (Φ.obj x₀) hx₀).projection)
          hD'.predeformation.cofibered))) := ⟨tangentConditionS2 hD'⟩
    FiniteDimensional k (tangentSpaceArtinian Λ k (isomorphismClasses
      (BasedCategory.ofFunctor (predeformationCategory iΛ q' (Φ.obj x₀) hx₀).projection)
        hD'.predeformation.cofibered)) := by
  let := (predeformationCategory iΛ (Φ ⋙ q') x₀ hx₀).category
  let := (predeformationCategory iΛ q' (Φ.obj x₀) hx₀).category
  let Ψ := predeformationComp iΛ q' Φ x₀ hx₀
  have hΨ := predeformationComp_surjective iΛ q' Φ x₀ hx₀ hsurj
  have hD : IsDeformationCategory (BasedCategory.ofFunctor
      (predeformationCategory iΛ (Φ ⋙ q') x₀ hx₀).projection).p :=
    isDeformationCategory_comp_of_surjective Ψ hΨ hD'
  have h₂ := (finiteDimensional_artinianTangentSpace_iff_tangentModuleAt
    (𝓕 := BasedCategory.ofFunctor (predeformationCategory iΛ (Φ ⋙ q') x₀ hx₀).projection)
    hD).1 (h hD.predeformation (tangentConditionS2 hD))
  let φ : BasedCategory.ofFunctor (predeformationCategory iΛ (Φ ⋙ q') x₀ hx₀).projection ⥤ᵇ
      BasedCategory.ofFunctor (predeformationCategory iΛ q' (Φ.obj x₀) hx₀).projection :=
    ⟨Ψ, rfl⟩
  have : φ.toFunctor.EssSurj := ⟨fun d' => by
    obtain ⟨d, hd⟩ := hΨ d'
    exact ⟨d, ⟨eqToIso hd⟩⟩⟩
  have h₃ : FiniteDimensional k ↥(tangentModuleAt
      (BasedCategory.ofFunctor (predeformationCategory iΛ q' (Φ.obj x₀) hx₀).projection) hD'
      (FGModuleCat.of k k)) :=
    Module.Finite.of_surjective _ (tangentMapAt_surjective_of_essSurj hD hD' φ _)
  exact finiteDimensional_tangentSpaceArtinian_of_tangentModuleAt hD'
    ((finiteDimensional_tangentModuleAt_uLift_iff hD').2 h₃)

end PredeformationComp

end Deformation.Artin

namespace AlgebraicGeometry.LocallyNoetherianOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The uniqueness half of Stacks 0GE7.** Two limit preserving algebraic spaces on the big fppf
site of a locally Noetherian scheme `S` with the same restriction `F` to the locally Noetherian
site are identified by a unique isomorphism compatible with the identifications of their
restrictions with `F` (Stacks 0GE3). -/
theorem existsUnique_iso_of_restriction_iso [IsLocallyNoetherian S]
    {F : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {F₁ F₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (h₁ : Space.IsAlgebraicSpaceULift.{u + 1} B S hS F₁)
    (h₂ : Space.IsAlgebraicSpaceULift.{u + 1} B S hS F₂)
    (hl₁ : LimitPreserving.{u, u + 1, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F₁)
    (hl₂ : LimitPreserving.{u, u + 1, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F₂)
    (e₁ : (LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F₁ ≅ F)
    (e₂ : (LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F₂ ≅ F) :
    ∃! e : F₁ ≅ F₂,
      Functor.isoWhiskerLeft (LocallyNoetherianOver.toBigFppfOver B S hS).op e ≪≫ e₂ = e₁ := by
  obtain ⟨e, he, hu⟩ := ExtendingFunctors.existsUnique_iso_isoWhiskerLeft_eq_bigFppfOver B hS
    h₁.isSheaf hl₁ h₂.isSheaf hl₂ (e₁ ≪≫ e₂.symm)
  refine ⟨e, ?_, fun e' he' => hu e' ?_⟩
  · beta_reduce
    rw [he, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  · beta_reduce at he' ⊢
    rw [← he', Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]

end AlgebraicGeometry.LocallyNoetherianOver

namespace AlgebraicGeometry.LocallyNoetherianOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w} {F : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type w}
  (e : (LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F' ≅ F)

/-- The category fibred in sets attached to a set-valued functor on the big fppf site of `S`,
over schemes over `S`: the big-site counterpart of
`AlgebraicGeometry.LocallyNoetherianOver.elementsToOver`. -/
abbrev bigElementsToOver (F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w) : F'.Elementsᵒᵖ ⥤ Over S :=
  (CategoryOfElements.π F').leftOp ⋙ Over.post B.inclusion

/-- **The comparison of the categories fibred in sets** of a functor `F` on the locally
Noetherian site and of a functor `F'` on the big fppf site restricting to it along `e`. -/
def elementsComparison : F.Elementsᵒᵖ ⥤ F'.Elementsᵒᵖ :=
  (show F.Elements ⥤ F'.Elements from
    { obj := fun x => F'.elementsMk (op ((LocallyNoetherianOver.toBigFppfOver B S hS).obj x.1.unop))
        (e.inv.app x.1 x.2)
      map := fun {x y} f => ⟨(LocallyNoetherianOver.toBigFppfOver B S hS).op.map f.1, by
        change ((LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F').map f.1 (e.inv.app x.1 x.2) =
          e.inv.app y.1 y.2
        rw [← NatTrans.naturality_apply, f.2]⟩
      map_id := fun x => rfl
      map_comp := fun f g => rfl }).op

/-- The comparison lies over the identity of `Sch/S`. -/
theorem elementsComparison_comp_bigElementsToOver :
    elementsComparison e ⋙ bigElementsToOver F' = elementsToOver B S hS F :=
  rfl

/-- The comparison `elementsComparison e` is faithful. -/
instance : (elementsComparison e).Faithful :=
  ⟨fun {x y} f g h => by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    apply Quiver.Hom.unop_inj
    apply (LocallyNoetherianOver.toBigFppfOver B S hS).map_injective
    exact congrArg (fun k => k.unop.1.unop) h⟩

/-- The comparison `elementsComparison e` is full. -/
instance : (elementsComparison e).Full :=
  ⟨fun {x y} g => by
    obtain ⟨@⟨⟨X₀⟩, x₀⟩⟩ := x
    obtain ⟨@⟨⟨Y₀⟩, y₀⟩⟩ := y
    have hinj : ∀ Z, Function.Injective (e.inv.app Z) := fun Z =>
      ((isIso_iff_bijective (e.inv.app Z)).1 inferInstance).1
    obtain ⟨g₀, hg₀⟩ := (LocallyNoetherianOver.toBigFppfOver B S hS).map_surjective g.unop.1.unop
    have hg : F.map g₀.op y₀ = x₀ := hinj _ (by
      rw [NatTrans.naturality_apply]
      change F'.map ((LocallyNoetherianOver.toBigFppfOver B S hS).map g₀).op (e.inv.app _ y₀) =
        e.inv.app _ x₀
      rw [hg₀]
      exact g.unop.2)
    refine ⟨Quiver.Hom.op ⟨g₀.op, hg⟩, ?_⟩
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    change ((LocallyNoetherianOver.toBigFppfOver B S hS).map g₀).op = g.unop.1
    rw [hg₀]
    rfl⟩

/-- **The comparison reaches every object over a locally Noetherian scheme.** -/
theorem elementsComparison_surjective (y' : F'.Elementsᵒᵖ)
    (hy' : IsLocallyNoetherian ((bigElementsToOver F').obj y').left) :
    ∃ y : F.Elementsᵒᵖ, (elementsComparison e).obj y = y' := by
  obtain ⟨@⟨⟨T⟩, s⟩⟩ := y'
  refine ⟨op (F.elementsMk (op ⟨T, hy'⟩) (e.hom.app (op ⟨T, hy'⟩) s)), ?_⟩
  show op (F'.elementsMk (op T) (e.inv.app _ (e.hom.app (op ⟨T, hy'⟩) s))) =
    op (F'.elementsMk (op T) s)
  rw [Iso.hom_inv_id_app_apply]

include e in
open Deformation Deformation.Artin in
/-- **Axiom `[5]` passes from the locally Noetherian site to the big fppf site.** -/
theorem openVersality_of_hasOpenVersality [IsLocallyNoetherian S] (h : HasOpenVersality B S hS F) :
    ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : F'.Elementsᵒᵖ) (hx : (bigElementsToOver F').obj x = U) (u₀ : U.left),
        IsFiniteTypePoint u₀ → IsVersalAt U (bigElementsToOver F') u₀ x hx →
        ∃ V : U.left.Opens, u₀ ∈ V.1 ∧ ∀ (u : U.left), u ∈ V.1 → IsFiniteTypePoint u →
          IsVersalAt U (bigElementsToOver F') u x hx := by
  exact openVersality_of_comp (bigElementsToOver F') (elementsComparison e)
    (elementsComparison_surjective e) h

include e in
open Deformation Deformation.Artin in
/-- **Axiom `[3]` passes from the locally Noetherian site to the big fppf site.** -/
theorem finiteDimensional_tangentSpaceArtinian_bigElementsToOver
    (h : HasFiniteDimensionalTangentSpaces B S hS F)
    (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (hiΛ : IsOpenImmersion iΛ) (x₀ : F'.Elementsᵒᵖ)
    (hx₀ : (bigElementsToOver F').obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hD : letI := (predeformationCategory iΛ (bigElementsToOver F') x₀ hx₀).category
      IsDeformationCategory (predeformationCategory iΛ (bigElementsToOver F') x₀ hx₀).projection) :
    letI := (predeformationCategory iΛ (bigElementsToOver F') x₀ hx₀).category
    letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor
        (predeformationCategory iΛ (bigElementsToOver F') x₀ hx₀).projection).p) :=
      ⟨hD.predeformation⟩
    letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π (isomorphismClasses
        (BasedCategory.ofFunctor
          (predeformationCategory iΛ (bigElementsToOver F') x₀ hx₀).projection)
          hD.predeformation.cofibered))) := ⟨tangentConditionS2 hD⟩
    FiniteDimensional k (tangentSpaceArtinian Λ k (isomorphismClasses
      (BasedCategory.ofFunctor
        (predeformationCategory iΛ (bigElementsToOver F') x₀ hx₀).projection)
        hD.predeformation.cofibered)) := by
  have hN : IsLocallyNoetherian ((bigElementsToOver F').obj x₀).left := by
    rw [hx₀]
    show IsLocallyNoetherian (Spec (.of k))
    infer_instance
  obtain ⟨y, rfl⟩ := elementsComparison_surjective e x₀ hN
  exact finiteDimensional_tangentSpaceArtinian_of_comp iΛ (bigElementsToOver F')
    (elementsComparison e) y hx₀ (elementsComparison_surjective e) (h Λ k iΛ hiΛ y hx₀) hD

include e in
open Deformation.Artin in
/-- **Axiom `[4]` passes from the locally Noetherian site to the big fppf site**: every formal
object of `F'` is effective. -/
theorem exists_eq_of_hasEffectiveFormalObjects (h : HasEffectiveFormalObjects B S hS F)
    (A : FormalBase S) (hA : ∀ n, B.Contains (A.truncation n))
    (ξ : ∀ n, F'.obj (op (truncationOver B S hS A hA n)))
    (hξ : ∀ n, F'.map (truncationOverSucc B S hS A hA n).op (ξ (n + 1)) = ξ n) :
    ∃ x : F'.obj (op (baseOver B S hS A (A.contains_spec_of_contains_truncation hA))),
      ∀ n, F'.map (restrictionToBase B S hS A (A.contains_spec_of_contains_truncation hA) hA n).op
        x = ξ n := by
  let F₀ := (LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F'
  let ξ₀ : ∀ n, F₀.obj (op (truncationObj B S hS A hA n)) := ξ
  have hξ₀ : ∀ n, F₀.map (truncationObjSucc B S hS A hA n).op (ξ₀ (n + 1)) = ξ₀ n := hξ
  obtain ⟨x, hx⟩ := h A hA (fun n => e.hom.app _ (ξ₀ n)) (fun n => by
    rw [← NatTrans.naturality_apply, hξ₀])
  refine ⟨e.inv.app (op (baseObj B S hS A hA)) x, fun n => ?_⟩
  show F₀.map (truncationObjIncl B S hS A hA n).op (e.inv.app _ x) = ξ₀ n
  rw [← NatTrans.naturality_apply, hx n, Iso.hom_inv_id_app_apply]

end AlgebraicGeometry.LocallyNoetherianOver

namespace AlgebraicGeometry.LocallyNoetherianOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Artin's axioms `[-1]`, `[0]`, `[1]`, `[2]`, `[3]`, `[4]`, `[5]`** of Section 07XZ for a
set-valued functor on the locally Noetherian étale site `(Noetherian/S)_étale`, in the form
reviewed in Section 0GE6. -/
structure SatisfiesArtinAxioms (F : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type w) : Prop where
  /-- Axiom `[-1]`: the cardinalities of the values of `F` on the spectra of fields of finite
  type over `S` are bounded by the size of a single object of the big fppf site. -/
  sizeBounded : ∃ T : BigFppfOver B S hS, ∀ (U : LocallyNoetherianOver B S hS) (K : Type u)
    [Field K], Nonempty ((LocallyNoetherianOver.toScheme B S hS).obj U ≅ Spec (.of K)) →
      LocallyOfFiniteType (B.inclusion.map U.obj.hom) →
      Cardinal.lift.{u} (Cardinal.mk (F.obj (op U))) ≤
        Cardinal.lift.{w} ((BigFppfOver.toScheme B S hS).obj T).size
  /-- Axiom `[0]`: `F` satisfies the sheaf condition for the étale coverings. -/
  isSheaf : ∀ E : Covering (LocallyNoetherianOver B S hS), IsEtaleCovering B S hS E →
    E.2.presieve₀.IsSheafFor F
  /-- Axiom `[1]`: `F` is limit preserving. -/
  limitPreserving : LimitPreserving.{u, w, u, u, u + 1, u}
    (LocallyNoetherianOver.toScheme B S hS) F
  /-- Axiom `[2]`: `F` satisfies the Rim--Schlessinger condition (RS). -/
  satisfiesRS : SatisfiesRS B S hS F
  /-- Axiom `[3]`: the tangent spaces of `F` are finite dimensional. -/
  finiteDimensionalTangentSpaces : HasFiniteDimensionalTangentSpaces B S hS F
  /-- Axiom `[4]`: every formal object of `F` is effective. -/
  effective : HasEffectiveFormalObjects B S hS F
  /-- Axiom `[5]`: `F` satisfies openness of versality. -/
  openVersality : HasOpenVersality B S hS F

end AlgebraicGeometry.LocallyNoetherianOver

namespace AlgebraicGeometry.LocallyNoetherianOver

open Deformation Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {F : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type u}
  (e : (LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ G ≅ F)

/-- **The comparison of the category fibred in sets of a functor `F` on the locally Noetherian
site with the category fibred in groupoids `𝒮_G` of a functor `G` on the big fppf site
restricting to it along `e`.** -/
def elementsToFibredCategory : F.Elementsᵒᵖ ⥤ (Stack.fibredCategory B S hS G).val.obj where
  obj x := ⟨(LocallyNoetherianOver.toBigFppfOver B S hS).obj x.unop.1.unop,
    Discrete.mk (e.inv.app x.unop.1 x.unop.2)⟩
  map {x y} f := ⟨(LocallyNoetherianOver.toBigFppfOver B S hS).map f.unop.1.unop,
    Discrete.eqToHom (by
      change e.inv.app x.unop.1 x.unop.2 =
        ((LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ G).map f.unop.1 (e.inv.app _ y.unop.2)
      rw [← NatTrans.naturality_apply, f.unop.2])⟩
  map_id x := fibredCategory_hom_ext _ _
    (CategoryTheory.Functor.map_id (LocallyNoetherianOver.toBigFppfOver B S hS) _)
  map_comp f g := fibredCategory_hom_ext _ _
    (CategoryTheory.Functor.map_comp (LocallyNoetherianOver.toBigFppfOver B S hS)
      f.unop.1.unop g.unop.1.unop)

/-- The comparison lies over the identity of `Sch/S`. -/
theorem elementsToFibredCategory_comp :
    elementsToFibredCategory e ⋙ ((Stack.fibredCategory B S hS G).val.p ⋙ Over.post B.inclusion) =
      elementsToOver B S hS F :=
  rfl

/-- The functor `elementsToFibredCategory e` is faithful. -/
instance : (elementsToFibredCategory e).Faithful :=
  ⟨fun {x y} f g h => by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    apply Quiver.Hom.unop_inj
    apply (LocallyNoetherianOver.toBigFppfOver B S hS).map_injective
    exact congrArg Pseudofunctor.CoGrothendieck.Hom.base h⟩

/-- The functor `elementsToFibredCategory e` is full. -/
instance : (elementsToFibredCategory e).Full :=
  ⟨fun {x y} φ => by
    obtain ⟨@⟨⟨X₀⟩, x₀⟩⟩ := x
    obtain ⟨@⟨⟨Y₀⟩, y₀⟩⟩ := y
    have hinj : ∀ Z, Function.Injective (e.inv.app Z) := fun Z =>
      ((isIso_iff_bijective (e.inv.app Z)).1 inferInstance).1
    obtain ⟨g₀, hg₀⟩ := (LocallyNoetherianOver.toBigFppfOver B S hS).map_surjective φ.base
    have hg : F.map g₀.op y₀ = x₀ := hinj _ (by
      rw [NatTrans.naturality_apply]
      have := fiber_as_eq_of_hom φ
      change G.map ((LocallyNoetherianOver.toBigFppfOver B S hS).map g₀).op (e.inv.app _ y₀) =
        e.inv.app _ x₀
      rw [hg₀]
      exact this.symm)
    exact ⟨Quiver.Hom.op ⟨g₀.op, hg⟩, fibredCategory_hom_ext _ _ hg₀⟩⟩

/-- **The comparison reaches every object over a locally Noetherian scheme.** -/
theorem elementsToFibredCategory_surjective (y' : (Stack.fibredCategory B S hS G).val.obj)
    (hy' : IsLocallyNoetherian
      (((Stack.fibredCategory B S hS G).val.p ⋙ Over.post B.inclusion).obj y').left) :
    ∃ y : F.Elementsᵒᵖ, (elementsToFibredCategory e).obj y = y' := by
  obtain ⟨T, ⟨s⟩⟩ := y'
  refine ⟨op (F.elementsMk (op ⟨T, hy'⟩) (e.hom.app (op ⟨T, hy'⟩) s)), ?_⟩
  show (⟨T, Discrete.mk (e.inv.app _ (e.hom.app (op ⟨T, hy'⟩) s))⟩ :
    (Stack.fibredCategory B S hS G).val.obj) = ⟨T, ⟨s⟩⟩
  rw [Iso.hom_inv_id_app_apply]

include e in
/-- **Axiom `[4]` for `𝒮_G` from axiom `[4]` for `F`**: every formal object of the category
fibred in groupoids of `G` is effective. -/
theorem isEffective_fibredCategory_of_hasEffectiveFormalObjects
    (h : HasEffectiveFormalObjects B S hS F)
    (ξ : FormalObject B S hS (Stack.fibredCategory B S hS G).val.p) :
    FormalObject.IsEffective B S hS (Stack.fibredCategory B S hS G).val.p
      (Stack.fibredCategory B S hS G).property ξ := by
  let p := (Stack.fibredCategory B S hS G).val.p
  have hA := ξ.base.contains_spec_of_contains_truncation ξ.contains
  let s : ∀ n, G.obj (op (truncationOver B S hS ξ.base ξ.contains n)) := fun n =>
    G.map (eqToHom (ξ.level_eq n).symm).op (ξ.level n).fiber.as
  have L₁ : ∀ {a b : BigFppfOver B S hS} (h : a = b) (y : G.obj (op a)),
      G.map (eqToHom h).op (G.map (eqToHom h.symm).op y) = y := by
    intro a b h y
    subst h
    simp
  have L₂ : ∀ {a a' b b' : BigFppfOver B S hS} (h : a = a') (h' : b = b') (f : a' ⟶ b')
      (y : G.obj (op b)), G.map f.op (G.map (eqToHom h'.symm).op y) =
        G.map (eqToHom h.symm).op (G.map (eqToHom h ≫ f ≫ eqToHom h'.symm).op y) := by
    intro a a' b b' h h' f y
    subst h h'
    simp
  have hs : ∀ n, (ξ.level n).fiber.as = G.map (eqToHom (ξ.level_eq n)).op (s n) :=
    fun n => (L₁ (ξ.level_eq n) _).symm
  have hcompat : ∀ n, G.map (truncationOverSucc B S hS ξ.base ξ.contains n).op (s (n + 1)) =
      s n := fun n => by
    have h₁ := fiber_as_eq_of_hom (ξ.transition n)
    have h₃ : (ξ.transition n).base = eqToHom (ξ.level_eq n) ≫
        truncationOverSucc B S hS ξ.base ξ.contains n ≫ eqToHom (ξ.level_eq (n + 1)).symm :=
      FormalObject.map_transition ξ n
    exact (L₂ (ξ.level_eq n) (ξ.level_eq (n + 1)) _ _).trans
      (congrArg (G.map (eqToHom (ξ.level_eq n).symm).op)
        ((congrArg (fun k => G.map k.op (ξ.level (n + 1)).fiber.as) h₃).symm.trans h₁.symm))
  obtain ⟨x, hx⟩ := exists_eq_of_hasEffectiveFormalObjects e h ξ.base ξ.contains s hcompat
  let X : (Stack.fibredCategory B S hS G).val.obj := ⟨baseOver B S hS ξ.base hA, Discrete.mk x⟩
  let r : ∀ n, ξ.level n ⟶ X := fun n =>
    ⟨eqToHom (ξ.level_eq n) ≫ restrictionToBase B S hS ξ.base hA ξ.contains n,
      Discrete.eqToHom (by
        show (ξ.level n).fiber.as =
          G.map (eqToHom (ξ.level_eq n) ≫ restrictionToBase B S hS ξ.base hA ξ.contains n).op x
        rw [hs n, op_comp, Functor.map_comp_apply, hx n])⟩
  refine FormalObject.isEffective_of_realization (Stack.fibredCategory B S hS G).property
    (hx := (rfl : p.obj X = baseOver B S hS ξ.base hA))
    (R :=
      { r := r
        comp_transition := fun n => fibredCategory_hom_ext _ _ ?_
        map_eq := fun n => congrArg (eqToHom (ξ.level_eq n) ≫ ·)
          (Category.comp_id (restrictionToBase B S hS ξ.base hA ξ.contains n)).symm })
  have L₃ : ∀ {a a' b b' : BigFppfOver B S hS} (h : a = a') (h' : b = b') (f : a' ⟶ b')
      {c : BigFppfOver B S hS} (r₁ : b' ⟶ c) (r₀ : a' ⟶ c), f ≫ r₁ = r₀ →
      (eqToHom h ≫ f ≫ eqToHom h'.symm) ≫ eqToHom h' ≫ r₁ = eqToHom h ≫ r₀ := by
    intro a a' b b' h h' f c r₁ r₀ hf
    subst h h'
    simpa using hf
  exact (congrArg (· ≫ eqToHom (ξ.level_eq (n + 1)) ≫
    restrictionToBase B S hS ξ.base hA ξ.contains (n + 1)) (FormalObject.map_transition ξ n)).trans
    (L₃ (ξ.level_eq n) (ξ.level_eq (n + 1)) _ _ _ (restrictionToBase_succ B S hS ξ.base hA
      ξ.contains n))
end AlgebraicGeometry.LocallyNoetherianOver

namespace AlgebraicGeometry.LocallyNoetherianOver

open Deformation Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {F : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type (max u w)}
  (e : (LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ G ⋙ uliftFunctor.{w} ≅ F)

/-- **The comparison of the category fibred in sets of a functor `F` with values in
`Type (max u w)` on the locally Noetherian site with the category fibred in groupoids `𝒮_G` of a
functor `G` of `Type u` on the big fppf site whose restriction, lifted to `Type (max u w)`, is `F`
along `e`.** -/
def elementsToFibredCategoryULift : F.Elementsᵒᵖ ⥤ (Stack.fibredCategory B S hS G).val.obj where
  obj x := ⟨(LocallyNoetherianOver.toBigFppfOver B S hS).obj x.unop.1.unop,
    Discrete.mk (e.inv.app x.unop.1 x.unop.2).down⟩
  map {x y} f := ⟨(LocallyNoetherianOver.toBigFppfOver B S hS).map f.unop.1.unop,
    Discrete.eqToHom (by
      change (e.inv.app x.unop.1 x.unop.2).down =
        (((LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ G ⋙ uliftFunctor.{w}).map
          f.unop.1 (e.inv.app _ y.unop.2)).down
      rw [← NatTrans.naturality_apply, f.unop.2])⟩
  map_id x := fibredCategory_hom_ext _ _
    (CategoryTheory.Functor.map_id (LocallyNoetherianOver.toBigFppfOver B S hS) _)
  map_comp f g := fibredCategory_hom_ext _ _
    (CategoryTheory.Functor.map_comp (LocallyNoetherianOver.toBigFppfOver B S hS)
      f.unop.1.unop g.unop.1.unop)

/-- The comparison lies over the identity of `Sch/S`. -/
theorem elementsToFibredCategoryULift_comp :
    elementsToFibredCategoryULift e ⋙
        ((Stack.fibredCategory B S hS G).val.p ⋙ Over.post B.inclusion) =
      elementsToOver B S hS F :=
  rfl

/-- The functor `elementsToFibredCategoryULift e` is faithful. -/
instance : (elementsToFibredCategoryULift e).Faithful :=
  ⟨fun {x y} f g h => by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    apply Quiver.Hom.unop_inj
    apply (LocallyNoetherianOver.toBigFppfOver B S hS).map_injective
    exact congrArg Pseudofunctor.CoGrothendieck.Hom.base h⟩

/-- The functor `elementsToFibredCategoryULift e` is full. -/
instance : (elementsToFibredCategoryULift e).Full :=
  ⟨fun {x y} φ => by
    obtain ⟨@⟨⟨X₀⟩, x₀⟩⟩ := x
    obtain ⟨@⟨⟨Y₀⟩, y₀⟩⟩ := y
    have hinj : ∀ Z, Function.Injective (e.inv.app Z) := fun Z =>
      ((isIso_iff_bijective (e.inv.app Z)).1 inferInstance).1
    obtain ⟨g₀, hg₀⟩ := (LocallyNoetherianOver.toBigFppfOver B S hS).map_surjective φ.base
    have hg : F.map g₀.op y₀ = x₀ := hinj _ (by
      rw [NatTrans.naturality_apply]
      have := fiber_as_eq_of_hom φ
      apply ULift.down_injective
      change G.map ((LocallyNoetherianOver.toBigFppfOver B S hS).map g₀).op
        (e.inv.app _ y₀).down = (e.inv.app _ x₀).down
      rw [hg₀]
      exact this.symm)
    exact ⟨Quiver.Hom.op ⟨g₀.op, hg⟩, fibredCategory_hom_ext _ _ hg₀⟩⟩

/-- **The comparison reaches every object over a locally Noetherian scheme.** -/
theorem elementsToFibredCategoryULift_surjective (y' : (Stack.fibredCategory B S hS G).val.obj)
    (hy' : IsLocallyNoetherian
      (((Stack.fibredCategory B S hS G).val.p ⋙ Over.post B.inclusion).obj y').left) :
    ∃ y : F.Elementsᵒᵖ, (elementsToFibredCategoryULift e).obj y = y' := by
  obtain ⟨T, ⟨s⟩⟩ := y'
  let T₀ : LocallyNoetherianOver B S hS := ⟨T, hy'⟩
  refine ⟨op (F.elementsMk (op T₀) (e.hom.app (op T₀) (ULift.up s))), ?_⟩
  have h : (e.inv.app (op T₀) (e.hom.app (op T₀) (ULift.up s))).down = s :=
    congrArg ULift.down ((e.app (op T₀)).toEquiv.symm_apply_apply _)
  show (⟨T, Discrete.mk (e.inv.app (op T₀) (e.hom.app (op T₀) (ULift.up s))).down⟩ :
    (Stack.fibredCategory B S hS G).val.obj) = ⟨T, ⟨s⟩⟩
  rw [h]

include e in
/-- **Axiom `[4]` for the restriction of `G` from axiom `[4]` for `F`.** -/
theorem hasEffectiveFormalObjects_restriction (h : HasEffectiveFormalObjects B S hS F) :
    HasEffectiveFormalObjects B S hS ((LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ G) := by
  intro A hA ξ hξ
  obtain ⟨x, hx⟩ := h A hA (fun n => e.hom.app _ (ULift.up (ξ n))) (fun n =>
    (NatTrans.naturality_apply e.hom _ _).symm.trans
      (congrArg (e.hom.app _) (congrArg ULift.up (hξ n))))
  refine ⟨(e.inv.app _ x).down, fun n => ?_⟩
  calc _ = (e.inv.app _ (F.map (truncationObjIncl B S hS A hA n).op x)).down :=
        (congrArg ULift.down (NatTrans.naturality_apply e.inv _ x)).symm
    _ = (e.inv.app _ (e.hom.app _ (ULift.up (ξ n)))).down := by rw [hx n]
    _ = ξ n := congrArg ULift.down ((e.app _).toEquiv.symm_apply_apply _)

include e in
/-- **Condition (RS) for `G` from condition (RS) for `F`.** -/
theorem satisfiesRSFunctor_of_satisfiesRS_uliftFunctor (h : SatisfiesRS B S hS F) :
    SatisfiesRSFunctor B S hS G := by
  have h' : SatisfiesRSFunctor B S hS (G ⋙ uliftFunctor.{w}) :=
    satisfiesRSFunctor_of_satisfiesRS e h
  intro X X' Y Y' i j i' j' w hX hX' hY hY' hX₁ hX'₁ hY₁ hY'₁ hci hpo a b hab
  obtain ⟨t, ⟨ht₁, ht₂⟩, hu⟩ := h' i j i' j' w hX hX' hY hY' hX₁ hX'₁ hY₁ hY'₁ hci hpo
    (ULift.up a) (ULift.up b) (congrArg ULift.up hab)
  refine ⟨t.down, ⟨congrArg ULift.down ht₁, congrArg ULift.down ht₂⟩, fun s hs => ?_⟩
  exact congrArg ULift.down (hu (ULift.up s) ⟨congrArg ULift.up hs.1, congrArg ULift.up hs.2⟩)

include e in
/-- **Axiom `[5]` for `𝒮_G` from axiom `[5]` for `F`.** -/
theorem openVersality_fibredCategory_of_hasOpenVersality [IsLocallyNoetherian S]
    (h : HasOpenVersality B S hS F) :
    ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : (Stack.fibredCategory B S hS G).val.obj)
        (hx : ((Stack.fibredCategory B S hS G).val.p ⋙ Over.post B.inclusion).obj x = U)
        (u₀ : U.left), IsFiniteTypePoint u₀ →
        IsVersalAt U ((Stack.fibredCategory B S hS G).val.p ⋙ Over.post B.inclusion) u₀ x hx →
        ∃ W : U.left.Opens, u₀ ∈ W.1 ∧ ∀ u : U.left, u ∈ W.1 → IsFiniteTypePoint u →
          IsVersalAt U ((Stack.fibredCategory B S hS G).val.p ⋙ Over.post B.inclusion) u x hx := by
  exact openVersality_of_comp _ (elementsToFibredCategoryULift e)
    (elementsToFibredCategoryULift_surjective e) h

include e in
/-- **Axiom `[3]` for `𝒮_G` from axiom `[3]` for `F`.** -/
theorem finiteDimensional_tangentSpaceArtinian_fibredCategory
    (h : HasFiniteDimensionalTangentSpaces B S hS F)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) [hiΛ : IsOpenImmersion iΛ]
    (x₀ : (Stack.fibredCategory B S hS G).val.obj)
    (hx₀ : ((Stack.fibredCategory B S hS G).val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hD : letI := (predeformationCategory iΛ ((Stack.fibredCategory B S hS G).val.p ⋙
        Over.post B.inclusion) x₀ hx₀).category
      IsDeformationCategory (predeformationCategory iΛ ((Stack.fibredCategory B S hS G).val.p ⋙
        Over.post B.inclusion) x₀ hx₀).projection) :
    letI := (predeformationCategory iΛ ((Stack.fibredCategory B S hS G).val.p ⋙
      Over.post B.inclusion) x₀ hx₀).category
    letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor
        (predeformationCategory iΛ ((Stack.fibredCategory B S hS G).val.p ⋙
          Over.post B.inclusion) x₀ hx₀).projection).p) := ⟨hD.predeformation⟩
    letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π (isomorphismClasses
        (BasedCategory.ofFunctor (predeformationCategory iΛ
          ((Stack.fibredCategory B S hS G).val.p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
        hD.predeformation.cofibered))) := ⟨tangentConditionS2 hD⟩
    FiniteDimensional k (tangentSpaceArtinian Λ k (isomorphismClasses
      (BasedCategory.ofFunctor (predeformationCategory iΛ
        ((Stack.fibredCategory B S hS G).val.p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
      hD.predeformation.cofibered)) := by
  have hN : IsLocallyNoetherian
      (((Stack.fibredCategory B S hS G).val.p ⋙ Over.post B.inclusion).obj x₀).left := by
    rw [hx₀]
    show IsLocallyNoetherian (Spec (.of k))
    infer_instance
  obtain ⟨y, rfl⟩ := elementsToFibredCategoryULift_surjective e x₀ hN
  exact finiteDimensional_tangentSpaceArtinian_of_comp (k := k) iΛ
    ((Stack.fibredCategory B S hS G).val.p ⋙ Over.post B.inclusion)
    (elementsToFibredCategoryULift e) y hx₀ (elementsToFibredCategoryULift_surjective e)
    (h Λ k iΛ hiΛ y hx₀) hD

end AlgebraicGeometry.LocallyNoetherianOver

namespace AlgebraicGeometry.LocallyNoetherianOver

open Deformation Deformation.Artin ExtendingFunctors CategoryTheory.Presheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Lifting the values of a limit preserving functor to a larger universe keeps it limit
preserving. -/
theorem limitPreserving_comp_uliftFunctor {C : Type*} [Category C] {toScheme : C ⥤ Scheme.{u}}
    {P : Cᵒᵖ ⥤ Type u} (h : LimitPreserving.{u, u, u, u} toScheme P) :
    LimitPreserving.{u, max u w, u, u} toScheme (P ⋙ uliftFunctor.{w}) := by
  intro I _ _ D c hc haff hpt
  obtain ⟨h'⟩ := h I D c hc haff hpt
  exact ⟨isColimitOfPreserves uliftFunctor.{w} h'⟩

/-- A functor isomorphic to a limit preserving functor is limit preserving. -/
theorem limitPreserving_of_iso {C : Type*} [Category C] {toScheme : C ⥤ Scheme.{u}}
    {P Q : Cᵒᵖ ⥤ Type w} (e : P ≅ Q) (h : LimitPreserving.{u, w, u, u} toScheme P) :
    LimitPreserving.{u, w, u, u} toScheme Q := by
  intro I _ _ D c hc haff hpt
  obtain ⟨h'⟩ := h I D c hc haff hpt
  exact ⟨h'.mapCoconeEquiv e⟩

/-- **Stacks 0GE7.** Let `S` be a locally Noetherian scheme and let `F` be a set-valued functor
on the locally Noetherian étale site `(Noetherian/S)_étale`. If the diagonal
`Δ : F ⟶ F × F` is representable (Categories 001X), `F` satisfies Artin's axioms `[-1]`,
`[0]`, `[1]`, `[2]`, `[3]`, `[4]`, `[5]` in the form of Section 0GE6, and the local rings of
`S` at its finite type points are G-rings, then there is a limit preserving algebraic space `F'`
on the big fppf site `(Sch/S)_fppf` whose restriction to `(Noetherian/S)_étale` is `F`, and it is
unique: two such are identified by a unique isomorphism compatible with the identifications of
their restrictions with `F`.

The extension is the one of Stacks 0GE3, its diagonal is representable by Stacks 0GE5, the
axioms `[-1]`, `[2]`, `[3]`, `[4]`, `[5]` pass to it because they only involve locally Noetherian
test objects, and Stacks 07Y1 shows it is an algebraic space. -/
@[stacks 0GE7]
theorem existsUnique_isAlgebraicSpace_restriction_iso [IsLocallyNoetherian S]
    (F : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type u)
    (hdiag : (yoneda (C := LocallyNoetherianOver B S hS)).relativelyRepresentable (diag F))
    (hax : SatisfiesArtinAxioms B S hS F)
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    (∃ F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS F' ∧
        LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F' ∧
        Nonempty ((LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F' ≅ F)) ∧
      ∀ (F₁ F₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
        IsAlgebraicSpace B S hS F₁ → IsAlgebraicSpace B S hS F₂ →
        LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F₁ →
        LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F₂ →
        ∀ (e₁ : (LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F₁ ≅ F)
          (e₂ : (LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F₂ ≅ F),
        ∃! e : F₁ ≅ F₂,
          Functor.isoWhiskerLeft (LocallyNoetherianOver.toBigFppfOver B S hS).op e ≪≫ e₂ = e₁ := by
  refine ⟨?_, fun F₁ F₂ h₁ h₂ hl₁ hl₂ e₁ e₂ => ?_⟩
  swap
  · obtain ⟨e, he, hu⟩ := ExtendingFunctors.existsUnique_iso_isoWhiskerLeft_eq_bigFppfOver B hS
      h₁.isSheaf hl₁ h₂.isSheaf hl₂ (e₁ ≪≫ e₂.symm)
    refine ⟨e, ?_, fun e' he' => hu e' ?_⟩
    · beta_reduce
      rw [he, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
    · beta_reduce at he' ⊢
      rw [← he', Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
  -- the functor with lifted values
  let F₁ : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type (max 0 (u + 1)) := F ⋙ uliftFunctor.{u + 1}
  have hFs₁ : ∀ E : Covering (LocallyNoetherianOver B S hS), IsEtaleCovering B S hS E →
      E.2.presieve₀.IsSheafFor F₁ := fun E hE =>
    (Presieve.isSheafFor_comp_uliftFunctor_iff.{u, u + 1}).2 (hax.isSheaf E hE)
  have hFl₁ : LimitPreserving.{u, max 0 (u + 1), u, u, u + 1, u}
      (LocallyNoetherianOver.toScheme B S hS) F₁ :=
    limitPreserving_comp_uliftFunctor hax.limitPreserving
  -- its extension to the big fppf site (Stacks 0GE3)
  let F' := extensionToBigFppfOver.{0} B hS F₁
  have hs' : IsCoveringSheafOnSubcategory.{u + 1, u, u} .zariski (IsContainedOver B (S := S))
      ((ExtendingFunctors.toBigFppfOver B hS).op ⋙ F') :=
    isCoveringSheafOnSubcategory_extensionToBigFppfOver.{0} hFs₁ hFl₁
  have hl' : LimitPreserving.{u, u + 1, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F' :=
    limitPreserving_extensionToBigFppfOver.{0} hFs₁ hFl₁
  have het : Presheaf.IsSheaf ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)) F' :=
    isSheaf_etaleTopology_extensionToBigFppfOver.{0} hFs₁ hFl₁
  obtain ⟨e'⟩ := nonempty_restriction_extensionToBigFppfOver_iso.{0} hFs₁ hFl₁
  -- its diagonal is representable (Stacks 0GE5)
  have h₁ : (uliftYoneda.{u + 1} (C := LocallyNoetherianOver B S hS)).relativelyRepresentable
      (diag F₁) := by
    rw [uliftYoneda_relativelyRepresentable_diag_iff]
    intro Y a b
    obtain ⟨X, snd, h⟩ := yoneda_relativelyRepresentable_diag_iff.1 hdiag Y a.down b.down
    exact ⟨X, snd, (representsEqualizer_comp_uliftFunctor_iff snd a.down b.down).2 h⟩
  have hdF' : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable
      (diag F') :=
    relativelyRepresentable_diag_of_restriction.{0} (B := B) (hS := hS) (hFs := hs') (hFl := hl')
      (hdiag := uliftYoneda_relativelyRepresentable_diag_of_iso e'.symm h₁)
  -- its values are `u`-small, so it is the lift of a `Type u`-valued functor `G`
  have hsmall : FunctorToTypes.Small.{u} F' := fun T =>
    small_obj_of_small_restriction.{0} B hS hs' hl' (fun V =>
      small_map ((e'.app (op V)).toEquiv.trans Equiv.ulift)) T.unop
  let G := FunctorToTypes.shrink.{u} F'
  let eG : G ⋙ uliftFunctor.{u + 1} ≅ F' :=
    NatIso.ofComponents (fun T => Equiv.toIso (Equiv.ulift.trans (equivShrink _).symm))
      (fun f => by ext x; exact Equiv.symm_apply_apply (equivShrink _) _)
  let e : (LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ G ≅ F :=
    (fullyFaithfulULiftFunctor.{u + 1, u}.whiskeringRight _).preimageIso
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (LocallyNoetherianOver.toBigFppfOver B S hS).op eG ≪≫ e')
  let e₀ : (LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ G ⋙ uliftFunctor.{u} ≅ F :=
    Functor.isoWhiskerLeft (LocallyNoetherianOver.toBigFppfOver B S hS).op
      (Functor.isoWhiskerLeft G uliftFunctorTrivial ≪≫ G.rightUnitor) ≪≫ e
  -- the hypotheses of Stacks 07Y1 for `G`
  have hdiagG : Space.IsRepresentableByAlgebraicSpaces B S hS (diag G) := by
    refine Space.IsRepresentableByAlgebraicSpaces.of_relativelyRepresentable ?_
    rw [yoneda_relativelyRepresentable_diag_iff]
    intro T a b
    have h := uliftYoneda_relativelyRepresentable_diag_of_iso eG.symm hdF'
    rw [uliftYoneda_relativelyRepresentable_diag_iff] at h
    obtain ⟨X, snd, h⟩ := h T (ULift.up a) (ULift.up b)
    exact ⟨X, snd, (representsEqualizer_comp_uliftFunctor_iff snd a b).1 h⟩
  have hsize : ∃ T₀ : BigFppfOver B S hS, ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k],
      Nonempty ((BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of k)) →
      LocallyOfFiniteType (B.inclusion.map U.hom) →
      Cardinal.mk (G.obj (op U)) ≤ ((BigFppfOver.toScheme B S hS).obj T₀).size := by
    obtain ⟨T₀, hT₀⟩ := hax.sizeBounded
    refine ⟨T₀, fun U k _ hU hlft => ?_⟩
    obtain ⟨φ⟩ := hU
    have hN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
      isLocallyNoetherian_of_isOpenImmersion φ.hom
    let U₀ : LocallyNoetherianOver B S hS := ⟨U, hN⟩
    have h := hT₀ U₀ k ⟨φ⟩ hlft
    simp only [Cardinal.lift_id] at h
    exact (Cardinal.mk_congr (e.app (op U₀)).toEquiv).trans_le h
  have hF : Presheaf.IsSheaf ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)) G := by
    have h := (Presheaf.isSheaf_of_iso_iff eG).2 het
    rw [isSheaf_iff_isSheaf_of_type] at h ⊢
    exact (Presieve.isSheaf_comp_uliftFunctor_iff _).1 h
  have hlim : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) G :=
    limitPreserving_of_comp_uliftFunctor (limitPreserving_of_iso eG.symm hl')
  have htangent := fun {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
      (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
      (x₀ : (Stack.fibredCategory B S hS G).val.obj)
      (hx₀ : ((Stack.fibredCategory B S hS G).val.p ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (_ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (_ : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) =>
    finiteDimensional_tangentSpaceArtinian_fibredCategory.{u, u} e₀
      hax.finiteDimensionalTangentSpaces iΛ x₀ hx₀
  refine ⟨G, Deformation.Artin.isAlgebraicSpace_of_artinAxioms hdiagG hsize hF hlim
    (satisfiesRSFunctor_of_satisfiesRS e hax.satisfiesRS) htangent
    (isEffective_fibredCategory_of_hasEffectiveFormalObjects e hax.effective)
    (openVersality_fibredCategory_of_hasOpenVersality.{u, u} e₀ hax.openVersality) hG, hlim, ⟨e⟩⟩

end AlgebraicGeometry.LocallyNoetherianOver
