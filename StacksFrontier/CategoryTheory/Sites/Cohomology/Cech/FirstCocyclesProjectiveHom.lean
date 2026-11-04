module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Projective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FirstCocycles

/-!
# Vanishing of first Čech cohomology passes to homomorphisms out of a projective module

Let `G` be a presheaf of `R`-modules on a category, let `E` be a family of morphisms whose
iterated fibre products exist, and let `M` be a projective `R`-module. If the first Čech
cohomology `Ȟ¹(E, G)` of the underlying abelian presheaf vanishes, so does the first Čech
cohomology of the presheaf `U ↦ Hom_R(M, G(U))`.

This is the step of [Stacks Project, Tag 061J] which turns the vanishing of the cohomology of
a quasi-coherent module `𝓖` into the vanishing of the cohomology of `𝓗om(𝓕, 𝓖)` for a locally
projective `𝓕`, read on a single covering family: the source writes `𝓕` as a direct summand of
a free module and commutes cohomology with products; on Čech cochains the same thing is the
lifting property of a projective module against the surjection of Čech `0`-cochains onto Čech
`1`-coboundaries.

## Main results

* `Stacks.CechSite.subsingleton_cechH1_of_linearEquiv_hom`: the statement above, for an abelian
  presheaf `Θ` given together with natural identifications `Θ(U) ≃ Hom_R(M, G(U))`, which is the
  form in which a presheaf of homomorphisms out of a projective module is usually met.

## References

* [Stacks Project, Tag 061J](https://stacks.math.columbia.edu/tag/061J)
* [Stacks Project, Tag 060L](https://stacks.math.columbia.edu/tag/060L)
-/

@[expose] public section

universe a w v u

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
    [HasProducts.{w} AddCommGrpCat.{a}]

/-- **Vanishing of `Ȟ¹` passes to homomorphisms out of a projective module.** Let `G` be a
presheaf of `R`-modules whose underlying abelian presheaf has vanishing first Čech cohomology
along `E`, let `M` be a projective `R`-module, and let `Θ` be an abelian presheaf whose sections
are identified, naturally, with the `R`-linear maps `M → G(U)`. Then `Ȟ¹(E, Θ)` vanishes. -/
theorem subsingleton_cechH1_of_linearEquiv_hom {R : Type a} [Ring R]
    (G : Cᵒᵖ ⥤ ModuleCat.{a} R) (M : Type a) [AddCommGroup M] [Module R M]
    [Module.Projective R M] (Θ : Cᵒᵖ ⥤ AddCommGrpCat.{a})
    (e : ∀ U : Cᵒᵖ, Θ.obj U ≃+ (M →ₗ[R] G.obj U))
    (he : ∀ {U V : Cᵒᵖ} (k : U ⟶ V) (θ : Θ.obj U),
      e V ((Θ.map k).hom θ) = (G.map k).hom ∘ₗ e U θ)
    (hG : Subsingleton (cechH1 E (G ⋙ forget₂ (ModuleCat.{a} R) AddCommGrpCat.{a}))) :
    Subsingleton (cechH1 E Θ) := by
  let G' := G ⋙ forget₂ (ModuleCat.{a} R) AddCommGrpCat.{a}
  -- the degree-zero Čech differential of `G`, as an `R`-linear map
  let GF : ∀ (n : ℕ) (_ : Fin (n + 1) → E.I₀), Type a := fun n k ↦
    G.obj (op ((∏ᶜ (fun j ↦ Over.mk (E.f (k j))) : Over X).left))
  let D0 : (∀ l : Fin 1 → E.I₀, GF 0 l) →ₗ[R] (∀ k : Fin 2 → E.I₀, GF 1 k) :=
    { toFun := fun t k ↦
        (G.map (faceProjection E k 0).left.op).hom (t fun b ↦ k ((0 : Fin 2).succAbove b)) -
          (G.map (faceProjection E k 1).left.op).hom (t fun b ↦ k ((1 : Fin 2).succAbove b))
      map_add' := fun t t' ↦ funext fun k ↦ by
        simp only [Pi.add_apply, map_add]
        abel
      map_smul' := fun r t ↦ funext fun k ↦ by
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub] }
  have hD0 : ∀ t : cechCochain E G' 0, cechDifferential E G' 0 t = D0 t := fun t ↦
    funext fun k ↦ by
      rw [cechDifferential_zero_apply]
      rfl
  -- every cocycle of `G` is a coboundary
  have hcob : ∀ c : cechCochain E G' 1, c ∈ cocycles1 E G' → ∃ t, D0 t = c := fun c hc ↦ by
    obtain ⟨t, ht⟩ := (cls_eq_zero_iff E G' ⟨c, hc⟩).1 (Subsingleton.elim _ _)
    exact ⟨t, (hD0 t).symm.trans ht⟩
  refine subsingleton_of_forall_eq 0 fun z ↦ ?_
  induction z using QuotientAddGroup.induction_on with
  | H c =>
    obtain ⟨c, hc⟩ := c
    -- the cocycle of `Θ`, evaluated at an element of `M`, is a cocycle of `G`
    let Φ : M →ₗ[R] (∀ k : Fin 2 → E.I₀, GF 1 k) :=
      { toFun := fun m k ↦ e _ (c k) m
        map_add' := fun m m' ↦ funext fun k ↦ by simp only [map_add, Pi.add_apply]
        map_smul' := fun r m ↦ funext fun k ↦ by
          simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }
    have hΦ : ∀ m, Φ m ∈ LinearMap.range D0 := fun m ↦ hcob _ <| by
      rw [mem_cocycles1_iff'] at hc ⊢
      intro k
      have hk := congrArg (fun θ ↦ e _ θ m) (hc k)
      simp only [map_add, he, LinearMap.add_apply, LinearMap.comp_apply] at hk
      exact hk
    obtain ⟨Ψ, hΨ⟩ := Module.projective_lifting_property (LinearMap.rangeRestrict D0)
      (LinearMap.codRestrict (LinearMap.range D0) Φ hΦ) (LinearMap.surjective_rangeRestrict D0)
    let η : cechCochain E Θ 0 := fun l ↦ (e _).symm (LinearMap.proj l ∘ₗ Ψ)
    have hη : cechDifferential E Θ 0 η = c := by
      funext k
      rw [cechDifferential_zero_apply]
      refine (e _).injective (LinearMap.ext fun m ↦ ?_)
      rw [map_sub, he, he]
      simp only [η, AddEquiv.apply_symm_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.proj_apply]
      exact congrFun (congrArg Subtype.val (LinearMap.congr_fun hΨ m)) k
    change QuotientAddGroup.mk _ = 0
    exact (QuotientAddGroup.eq_zero_iff _).2 ((mem_coboundaries1_iff E Θ ⟨c, hc⟩).2 ⟨η, hη⟩)

end Stacks.CechSite

end
