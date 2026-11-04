module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleHomDescent

/-!
# Gluing a morphism of `𝒪_X`-modules from a single covering chart

Let `X` be an algebraic space and let `W` be an étale chart of `X` covering the final object of
its small étale site — for instance one whose structure morphism is surjective.  A morphism
`α : M|_W ⟶ N|_W` of the restrictions of two `𝒪_X`-modules extends to a morphism `M ⟶ N` as soon
as its two relocalizations to the kernel pair `W ×_X W` agree, and then the extension is unique.

## Main results

* `AlgebraicGeometry.Space.isCompatible_singleton_of_relocalization_eq`: a morphism over a single
  chart whose two relocalizations along a pair of arrows dominating every pair agree is a
  compatible family for the one-element family at that chart.
* `AlgebraicGeometry.Space.existsUnique_hom_of_single_chart`: such a morphism is the restriction
  of a unique morphism `M ⟶ N` when the chart covers the final object.
* `AlgebraicGeometry.Space.exists_hom_prod`: every pair of arrows into `W` factors through the
  product `W ⨯ W`, and `AlgebraicGeometry.Space.existsUnique_hom_of_single_chart_prod` is the
  gluing with that product as the kernel pair.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **A morphism over a single chart whose two relocalizations along a dominating pair agree is a
compatible family** for the one-element family at that chart. -/
theorem isCompatible_singleton_of_relocalization_eq
    (M N : PresheafOfModules.{u} (Oforget (smallEtaleStructurePresheaf B S hS F hF)))
    (W R : SmallEtale B S hS F) (p q : R ⟶ W)
    (hdom : ∀ (Z : SmallEtale B S hS F) (f g : Z ⟶ W),
      ∃ h : Z ⟶ R, h ≫ p = f ∧ h ≫ q = g)
    (α : (restrFun (smallEtaleStructurePresheaf B S hS F hF) W).obj M ⟶
      (restrFun (smallEtaleStructurePresheaf B S hS F hF) W).obj N)
    (hpq : homRestr (smallEtaleStructurePresheaf B S hS F hF) M N p α =
      homRestr (smallEtaleStructurePresheaf B S hS F hF) M N q α) :
    Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (F := (internalHom (smallEtaleStructurePresheaf B S hS F hF) M N).presheaf ⋙
        CategoryTheory.forget _)
      (fun _ : Unit => α) := by
  intro Z _ _ f g
  obtain ⟨h, hf, hg⟩ := hdom Z f g
  rw [internalHomForget_map_apply, internalHomForget_map_apply, ← hf, ← hg,
    homRestr_comp, homRestr_comp, hpq]

/-- **Gluing a morphism of `𝒪_F`-modules from a single covering chart.**  If `W` covers the final
object of the small étale site and `α : M|_W ⟶ N|_W` has equal relocalizations along a pair of
arrows `p`, `q` through which every pair of arrows into `W` factors, then `α` is the restriction
of a unique morphism `M ⟶ N`. -/
theorem existsUnique_hom_of_single_chart
    (M N : PresheafOfModules.{u} (Oforget (smallEtaleStructurePresheaf B S hS F hF)))
    (hN : Presheaf.IsSheaf (SmallEtale.topology B S hS F) N.presheaf)
    (W : SmallEtale B S hS F)
    (hW : (SmallEtale.topology B S hS F).CoversTop (fun _ : Unit => W))
    (R : SmallEtale B S hS F) (p q : R ⟶ W)
    (hdom : ∀ (Z : SmallEtale B S hS F) (f g : Z ⟶ W),
      ∃ h : Z ⟶ R, h ≫ p = f ∧ h ≫ q = g)
    (α : (restrFun (smallEtaleStructurePresheaf B S hS F hF) W).obj M ⟶
      (restrFun (smallEtaleStructurePresheaf B S hS F hF) W).obj N)
    (hpq : homRestr (smallEtaleStructurePresheaf B S hS F hF) M N p α =
      homRestr (smallEtaleStructurePresheaf B S hS F hF) M N q α) :
    ∃! φ : M ⟶ N,
      (restrFun (smallEtaleStructurePresheaf B S hS F hF) W).map φ = α := by
  obtain ⟨φ, hφ, huniq⟩ :=
    existsUnique_hom_of_isCompatible (smallEtaleStructurePresheaf B S hS F hF) M N hW
      (internalHom_isSheaf_forget (smallEtaleStructurePresheaf B S hS F hF) M N hN)
      (isCompatible_singleton_of_relocalization_eq B S hS F hF M N W R p q hdom α hpq)
  exact ⟨φ, hφ (), fun ψ hψ ↦ huniq ψ fun _ ↦ hψ⟩

/-- **Every pair of arrows into `W` factors through the product `W ⨯ W`**, which for the small
étale site is the fibre product of `W` with itself over the ambient presheaf. -/
theorem exists_hom_prod (W : SmallEtale B S hS F) {Z : SmallEtale B S hS F} (f g : Z ⟶ W) :
    ∃ h : Z ⟶ (W ⨯ W : SmallEtale B S hS F),
      h ≫ Limits.prod.fst = f ∧ h ≫ Limits.prod.snd = g :=
  ⟨Limits.prod.lift f g, Limits.prod.lift_fst f g, Limits.prod.lift_snd f g⟩

/-- **Gluing a morphism of `𝒪_F`-modules from a single covering chart, with the kernel pair taken
to be `W ⨯ W`.**  If `W` covers the final object of the small étale site and the two
relocalizations of `α : M|_W ⟶ N|_W` along the two projections of `W ⨯ W` agree, then `α` is the
restriction of a unique morphism `M ⟶ N`. -/
theorem existsUnique_hom_of_single_chart_prod
    (M N : PresheafOfModules.{u} (Oforget (smallEtaleStructurePresheaf B S hS F hF)))
    (hN : Presheaf.IsSheaf (SmallEtale.topology B S hS F) N.presheaf)
    (W : SmallEtale B S hS F)
    (hW : (SmallEtale.topology B S hS F).CoversTop (fun _ : Unit => W))
    (α : (restrFun (smallEtaleStructurePresheaf B S hS F hF) W).obj M ⟶
      (restrFun (smallEtaleStructurePresheaf B S hS F hF) W).obj N)
    (hpq : homRestr (smallEtaleStructurePresheaf B S hS F hF) M N
          (Limits.prod.fst : (W ⨯ W : SmallEtale B S hS F) ⟶ W) α =
        homRestr (smallEtaleStructurePresheaf B S hS F hF) M N
          (Limits.prod.snd : (W ⨯ W : SmallEtale B S hS F) ⟶ W) α) :
    ∃! φ : M ⟶ N,
      (restrFun (smallEtaleStructurePresheaf B S hS F hF) W).map φ = α :=
  existsUnique_hom_of_single_chart B S hS F hF M N hN W hW (W ⨯ W)
    Limits.prod.fst Limits.prod.snd (fun _ f g ↦ exists_hom_prod B S hS F W f g) α hpq

end AlgebraicGeometry.Space

end
