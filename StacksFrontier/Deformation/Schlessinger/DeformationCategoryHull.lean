module

public import StacksFrontier.Deformation.Artin.Basic
public import StacksFrontier.Deformation.ClassicalCase
public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsDenseRestriction
public import StacksFrontier.Deformation.Formal.VersalObject.IsomorphismClassesHull
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.EquivalenceCriterion
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Vanishing
public import StacksFrontier.Deformation.Predeformation.Associated
public import StacksFrontier.Deformation.RimSchlessingerCategory.AutomorphismLifting
public import StacksFrontier.Deformation.Schlessinger.Prorepresentable
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison
import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Hulls and prorepresentability for the isomorphism classes of a deformation category

Let `𝓕` be a deformation category over `𝒞_Λ` in the classical case, with finite-dimensional
tangent space. Then the functor `F` of isomorphism classes of `𝓕` has a hull, and if the
infinitesimal automorphisms of `𝓕` vanish then `F` is prorepresentable.

## Main results

* `Deformation.isThin_fiber_of_infinitesimalAutomorphisms_eq_bot`: in a deformation category
  whose infinitesimal automorphisms vanish every fibre is thin.
* `Deformation.isDeformationFunctor_isomorphismClasses_of_infinitesimalAutomorphisms_eq_bot`:
  the functor of isomorphism classes is then a deformation functor.
* `Deformation.exists_hull_isomorphismClasses_of_isDeformationCategory`: in the classical case
  the functor of isomorphism classes of a deformation category with finite-dimensional tangent
  space has a hull.
* `Deformation.isProrepresentableULift_isomorphismClasses_of_infinitesimalAutomorphisms_eq_bot`:
  and it is prorepresentable when the infinitesimal automorphisms vanish.

## Implementation notes

Prorepresentability is stated in the universe-raised form `Deformation.IsProrepresentableULift`,
as for Stacks 0ET1: the values of the functor of isomorphism classes lie in the universe of the
objects of `𝓕`, not in the morphism universe of `𝒞_Λ`.

## References

* [Stacks Project, Tag 06IZ](https://stacks.math.columbia.edu/tag/06IZ)
* [Stacks Project, Tag 06J7](https://stacks.math.columbia.edu/tag/06J7)
* [Stacks Project, Tag 06JZ](https://stacks.math.columbia.edu/tag/06JZ)
* [Stacks Project, Tag 06K0](https://stacks.math.columbia.edu/tag/06K0)
* [Stacks Project, Tag 06JM](https://stacks.math.columbia.edu/tag/06JM)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

namespace Deformation

universe u v w u₁ v₁

section Thin

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

/-- **Vanishing infinitesimal automorphisms make every fibre thin.** In a deformation category
whose infinitesimal automorphisms vanish, every fibre has at most one morphism between any two
of its objects. -/
public theorem isThin_fiber_of_infinitesimalAutomorphisms_eq_bot (hD : IsDeformationCategory p)
    {Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k)} {xε : p.Fiber Aε}
    (g : residueFieldObject.{u, v, w} Λ k ⟶ Aε) (e : Aε ⟶ residueFieldObject.{u, v, w} Λ k)
    (hpair : IsCanonicalDualNumberPair g e) (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i)
    (htriv : infinitesimalAutomorphisms hD.predeformation.cofibered g e hpair i hi = ⊥)
    (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) : Quiver.IsThin (p.Fiber A) := by
  have hp := hD.predeformation.cofibered
  have hmax : maximalIdeal (residueFieldObject.{u, v, w} Λ k) = ⊥ :=
    maximalIdeal_eq_bot_of_isCanonicalDualNumberPair hpair
  have hendo : ∀ (x : p.Fiber A) (a : x ⟶ x), a = 𝟙 x := by
    intro x a
    let r : A ⟶ residueFieldObject.{u, v, w} Λ k :=
      (ArtinianLocalAlgCat.isTerminal_of_maximalIdeal_eq_bot _ hmax).from A
    obtain ⟨y, ι, hι⟩ := exists_pushforward hp r x.1 x.2
    have hy : p.obj y = residueFieldObject.{u, v, w} Λ k := IsHomLift.codomain_eq p r ι
    obtain ⟨-, hu⟩ := (CategoryTheory.equiv_punit_iff_unique _).mp hD.predeformation.specialFiber
    let m : Functor.Fiber.mk (p := p) hy ⟶ x₀ := (hu (Functor.Fiber.mk hy) x₀).some.default
    let m₁ : y ⟶ x₀.1 := m.1
    let f : x.1 ⟶ x₀.1 := ι ≫ m₁
    have hf : p.IsHomLift r f := by
      have : p.IsHomLift (𝟙 (residueFieldObject.{u, v, w} Λ k)) m₁ := m.2
      have : p.IsHomLift r ι := hι
      exact IsHomLift.comp_lift_id_right' (p := p) r ι (residueFieldObject.{u, v, w} Λ k) m₁
    have hbot := relativeInfinitesimalAutomorphisms_eq_bot hD.satisfiesRS (x' := x) (x := x₀)
      (x₀ := x₀) (xε := xε) r f hf
      (ArtinianLocalAlgCat.hom_surjective _ _ hmax r) (𝟙 _) (𝟙 x₀.1) (IsHomLift.id x₀.2)
      g e hpair i hi htriv
    have : IsIso a := (fiber_isGroupoid p hp A).all_isIso a
    have hcomm : a.1 ≫ f = f := by
      have ha : p.map a.1 = 𝟙 (p.obj x.1) := map_eq_id_of_isHomLift_id a.1 a.2
      obtain ⟨χ, ⟨hχmap, hχfac⟩, -⟩ := exists_unique_cofibered_factor hp f (a.1 ≫ f)
        (𝟙 (p.obj x₀.1)) (by rw [Category.comp_id, Functor.map_comp p a.1 f, ha, Category.id_comp])
      have hχlift : p.IsHomLift (𝟙 (residueFieldObject.{u, v, w} Λ k)) χ :=
        IsHomLift.of_fac p _ χ x₀.2 x₀.2 (by rw [hχmap]; simp)
      have hχid : χ = 𝟙 x₀.1 := congrArg Subtype.val
        ((isThin_specialFiber hD.predeformation x₀ x₀).elim (⟨χ, hχlift⟩ : x₀ ⟶ x₀) (𝟙 x₀))
      rw [← hχfac, hχid, Category.comp_id]
    let α : Aut x := .of (asIso a)
    have hmem : α ∈ relativeInfinitesimalAutomorphisms hp r f hf :=
      (mem_relativeInfinitesimalAutomorphisms_iff hp r f hf α).mpr hcomm
    rw [hbot] at hmem
    have h1 : α = 1 := (Subgroup.mem_bot).mp hmem
    exact congrArg (fun β : Aut x ↦ β.asIso.hom) h1
  refine fun x y ↦ ⟨fun φ ψ ↦ ?_⟩
  have : IsIso ψ := (fiber_isGroupoid p hp A).all_isIso ψ
  calc φ = (φ ≫ inv ψ) ≫ ψ := by simp
    _ = ψ := by rw [hendo x (φ ≫ inv ψ), Category.id_comp]

/-- **Vanishing infinitesimal automorphisms make the functor of isomorphism classes a
deformation functor.** -/
public theorem isDeformationFunctor_isomorphismClasses_of_infinitesimalAutomorphisms_eq_bot
    (hD : IsDeformationCategory p)
    {Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k)} {xε : p.Fiber Aε}
    (g : residueFieldObject.{u, v, w} Λ k ⟶ Aε) (e : Aε ⟶ residueFieldObject.{u, v, w} Λ k)
    (hpair : IsCanonicalDualNumberPair g e) (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i)
    (htriv : infinitesimalAutomorphisms hD.predeformation.cofibered g e hpair i hi = ⊥) :
    IsDeformationFunctor
      (isomorphismClasses (BasedCategory.ofFunctor p) hD.predeformation.cofibered) := by
  refine ⟨isPredeformationFunctor_isomorphismClasses _ hD.predeformation, ?_⟩
  apply (associatedSatisfiesRS_iff_gluingClassesInjective _ hD.satisfiesRS).2
  apply (gluingClassesInjective_iff_automorphismsLift _ hD.predeformation.cofibered).2
  intro A' A f _ x' x φ _ a
  refine ⟨Iso.refl x', ?_⟩
  have ha : a.hom = 𝟙 x :=
    ((isThin_fiber_of_infinitesimalAutomorphisms_eq_bot hD g e hpair i hi htriv A) x x).elim _ _
  rw [Iso.refl_hom, ha]
  show 𝟙 x'.1 ≫ φ = φ ≫ 𝟙 x.1
  simp

end Thin

section Classical

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **A deformation category with finite-dimensional tangent space has a hull** in the
classical case: the functor of isomorphism classes of `𝓕` has a versal formal object whose
differential is bijective. -/
public theorem exists_hull_isomorphismClasses_of_isDeformationCategory (hΛ : IsClassical Λ k)
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (hD : IsDeformationCategory 𝓕.p)
    (hfin :
      letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
      letI : Fact (SchlessingerConditionS2
        (CategoryOfElements.π (isomorphismClasses 𝓕 hD.predeformation.cofibered))) :=
        ⟨Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD⟩
      FiniteDimensional k
        (artinianTangentSpace Λ k (isomorphismClasses 𝓕 hD.predeformation.cofibered))) :
    let G := isomorphismClasses 𝓕 hD.predeformation.cofibered
    ∃ ξ : FormalObject (CategoryOfElements.π G),
      IsHull (categoryOfElements_projection_isCofibered G) ξ := by
  intro G
  let : IsNoetherianRing Λ := hΛ.isNoetherianRing
  let : Module.Finite Λ k := hΛ.moduleFinite
  let : Algebra.IsSeparable (residueImageField Λ k) k := hΛ.isSeparable
  let hS2 := Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD
  let : Fact (IsPredeformationCategory.{u, w, w} 𝓕.p) := ⟨hD.predeformation⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
  let : FiniteDimensional k (tangentSpaceArtinian.{u, w, w} Λ k
      (isomorphismClasses 𝓕 hD.predeformation.cofibered)) :=
    finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace 𝓕 hD.predeformation hS2 hfin
  obtain ⟨ξ, -, hhull⟩ :=
    exists_hull_isomorphismClasses.{u, w, w} Λ k 𝓕 hD.predeformation
      (schlessingerConditionS1_of_satisfiesRS hD.satisfiesRS)
      (schlessingerConditionS2_of_satisfiesRS hD.satisfiesRS) inferInstance
  exact ⟨imageInIsomorphismClasses _ hD.predeformation ξ, hhull⟩

/-- **A deformation category with finite-dimensional tangent space and vanishing infinitesimal
automorphisms has a prorepresentable functor of isomorphism classes** in the classical case. -/
@[sga "7 X 2.27" "more general"]
public theorem isProrepresentableULift_isomorphismClasses_of_infinitesimalAutomorphisms_eq_bot
    (hΛ : IsClassical Λ k)
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (hD : IsDeformationCategory 𝓕.p)
    (hfin :
      letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
      letI : Fact (SchlessingerConditionS2
        (CategoryOfElements.π (isomorphismClasses 𝓕 hD.predeformation.cofibered))) :=
        ⟨Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD⟩
      FiniteDimensional k
        (artinianTangentSpace Λ k (isomorphismClasses 𝓕 hD.predeformation.cofibered)))
    {Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {x₀ : 𝓕.p.Fiber (residueFieldObject.{u, w, w} Λ k)} {xε : 𝓕.p.Fiber Aε}
    (g : residueFieldObject.{u, w, w} Λ k ⟶ Aε) (e : Aε ⟶ residueFieldObject.{u, w, w} Λ k)
    (hpair : IsCanonicalDualNumberPair g e) (i : x₀.1 ⟶ xε.1) (hi : 𝓕.p.IsHomLift g i)
    (htriv : infinitesimalAutomorphisms hD.predeformation.cofibered g e hpair i hi = ⊥) :
    IsProrepresentableULift (isomorphismClasses 𝓕 hD.predeformation.cofibered) := by
  let : IsNoetherianRing Λ := hΛ.isNoetherianRing
  let : Module.Finite Λ k := hΛ.moduleFinite
  have hDF : IsDeformationFunctor (isomorphismClasses 𝓕 hD.predeformation.cofibered) :=
    isDeformationFunctor_isomorphismClasses_of_infinitesimalAutomorphisms_eq_bot
      (p := 𝓕.p) hD g e hpair i hi htriv
  refine (isProrepresentableULift_iff_isDeformationFunctor _).2 ⟨hDF, ?_, ?_⟩
  · let G := isomorphismClasses 𝓕 hD.predeformation.cofibered
    let 𝓖 := BasedCategory.ofFunctor (CategoryOfElements.π G)
    let hDel := (isDeformationCategory_iff G).2 hDF
    let hS2el := Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓖 hDel
    let hS2 := Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD
    exact finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace 𝓖
      hDel.predeformation hS2el
      (finiteDimensional_artinianTangentSpace_of_essSurj 𝓕 𝓖
        hD.predeformation hDel.predeformation hS2 hS2el
        (toIsomorphismClasses 𝓕 hD.predeformation.cofibered)
        (fun A ↦ (isomorphismClassesData 𝓕
          hD.predeformation.cofibered).quotient.fiber_essSurj A)
        hfin)
  · intro first second _
    ext value
    obtain ⟨scalar, rfl⟩ := hΛ.surjective_algebraMap value
    simp

end Classical

end Deformation

end
