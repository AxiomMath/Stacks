module

public import StacksFrontier.Deformation.Artin.Infinitesimal.DeformationSpaceComparison
public import StacksFrontier.Deformation.Artin.Infinitesimal.AdditivityOfInf
public import StacksFrontier.Deformation.Artin.Infinitesimal.TrivialLiftConjugation

/-!
# The infinitesimal automorphisms of `𝓕_{𝒳,k,x₀}` as a vector space

Let `𝒳` be a category fibred in groupoids over the big fppf site of a locally Noetherian scheme
`S` satisfying (RS*), let `k` be a field of finite type over `S`, and let `x₀` be an object of `𝒳`
over `Spec k`. The infinitesimal automorphisms `Inf(𝓕_{𝒳,k,x₀})` of the deformation category
(Tag 07X0) are the infinitesimal automorphisms `Inf_y(𝓕)` of a point `y` of `𝓕 = 𝓕_{𝒳,k,x₀}`
over `k`, and by Tag 06JX they carry a natural `k`-vector space structure: they are the tangent
space `T_{id_y} Aut(y)` of the automorphism functor at the identity, whose addition is
composition of automorphisms and whose scalar multiplication is transport along `ε ↦ cε`
(Tag 06JV). On the other side, Tag 07Y9 makes the infinitesimal automorphisms of the trivial
deformations of `x₀` into a `k`-linear functor `Inf_{x₀}` of the vector space. This file proves
the second half of Remark 0D18: `Inf(𝓕_{𝒳,k,x₀}) = Inf_{x₀}(k)` as `k`-vector spaces.

The identification is conjugation by an isomorphism `η` between the object `x'₀` underlying the
pushforward of `y` to the dual numbers and the trivial deformation of `x₀` over `k[k]`, which is
compatible with the two arrows out of `x₀` and lies over the comparison of the two presentations
of the dual numbers. Such an `η` exists, and conjugation does not depend on its choice.

The comparison is additive because the addition of `Inf_{x₀}(k)` is composition of
automorphisms of the trivial lift (`Deformation.Artin.autEquiv_add`, the counterpart of Tag
06I7). It is `k`-linear because `η` carries the arrow of `x'₀` induced by `ε ↦ cε` to the
transition arrow of the trivial deformations along multiplication by `c`, up to an
infinitesimal automorphism of the trivial lift, and that automorphism commutes with every other
since `Inf_{x₀}(k)` is abelian.

## Main results

* `Deformation.Artin.localizedAutomorphismTangent_deformationCategory_linearEquiv`: the
  `k`-linear equivalence `Inf(𝓕_{𝒳,k,x₀}) ≃ₗ[k] Inf_{x₀}(k)` for the vector space structure of
  Tag 06JX on the left and that of Tag 07Y9 on the right.

## Implementation notes

The left-hand side is formed at an arbitrary point `y` of `𝓕` over the residue field and an
arbitrary choice `P` of its pushforwards; the source's `Inf(𝓕_{𝒳,k,x₀})` is the case of the
canonical point, and every choice gives the same statement.

`Deformation.Artin.infinitesimalAutomorphisms_deformationCategory_linearEquiv` states this part
of 0D18 with the additive group and the scalar action on the infinitesimal automorphism group
existentially quantified, which any bijection admits. The statement here instead uses the
library's own structures on both sides: `naturalLocalizedTangentAddCommGroup` and
`naturalLocalizedTangentModule` (Tag 06JX, registered on
`exists_naturalLocalizedAutomorphismTangentVectorSpace`) and the `ModuleCat k` value of
`infinitesimalAutomorphismFunctor` (Tag 07Y9). The tangent-space half of 0D18 is
`tangentSpace_deformationCategory_linearEquiv`, already at the intrinsic structures.

## References

* [Stacks Project, Tag 0D18](https://stacks.math.columbia.edu/tag/0D18)
* [Stacks Project, Tag 07X0](https://stacks.math.columbia.edu/tag/07X0)
* [Stacks Project, Tag 06JX](https://stacks.math.columbia.edu/tag/06JX)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Functor

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

universe u v w

namespace Deformation.Artin

attribute [local instance] PredeformationConstruction.category

section Commutative

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids)

/-- The infinitesimal automorphisms of a trivial deformation commute with each other. -/
private theorem trivialDeformation_hom_comm (hRS : SatisfiesRSStar B S hS p hp)
    (Inf : InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp) (M : SiteModule A B)
    (θ θ' : trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M) :
    θ ≫ θ' = θ' ≫ θ := by
  obtain ⟨u₁, rfl⟩ := (Inf.autEquiv M).surjective θ
  obtain ⟨u₂, rfl⟩ := (Inf.autEquiv M).surjective θ'
  rw [← autEquiv_add A B S hS toS hA p x hx hp hRS Inf, add_comm,
    autEquiv_add A B S hS toS hA p x hx hp hRS Inf]

end Commutative

/-- Conjugation by `η` agrees with conjugation by `η'` when the conjugate commutes with
`η.inv ≫ η'.hom`. -/
private theorem conj_eq_conj_of_comm {C : Type*} [Category C] {Y Z : C} (η η' : Y ≅ Z)
    (A : Y ⟶ Y) (ζ : Z ⟶ Z) (hζ : ζ = η.inv ≫ η'.hom)
    (hc : (η.inv ≫ A ≫ η.hom) ≫ ζ = ζ ≫ η.inv ≫ A ≫ η.hom) :
    η.inv ≫ A ≫ η.hom = η'.inv ≫ A ≫ η'.hom := by
  have hη'hom : η'.hom = η.hom ≫ ζ := by simp [hζ]
  calc η.inv ≫ A ≫ η.hom
      = (η'.inv ≫ η.hom ≫ ζ) ≫ η.inv ≫ A ≫ η.hom := by simp [hζ]
    _ = η'.inv ≫ η.hom ≫ (η.inv ≫ A ≫ η.hom) ≫ ζ := by rw [Category.assoc, Category.assoc, hc]
    _ = η'.inv ≫ A ≫ η'.hom := by
      rw [hη'hom]
      simp

section Statement

/-- **Stacks Project, Tag 0D18, infinitesimal automorphisms.** For a category fibred in groupoids
over the big fppf site of a locally Noetherian scheme satisfying (RS*), the infinitesimal
automorphisms of the deformation category of a finite-type field-valued point `x₀`, with their
natural vector space structure of Tag 06JX, are the value at the rank-one vector space of the
infinitesimal automorphism functor of Tag 07Y9: there is a `k`-linear equivalence `E`, which is
conjugation by any isomorphism `η` of the object underlying the dual-number pushforward with the
trivial deformation of `x₀` that is compatible with the arrows out of `x₀` and lies over the
comparison of the two presentations of the dual numbers; such an `η` exists. -/
@[stacks 0D18 "infinitesimal automorphisms"]
public theorem localizedAutomorphismTangent_deformationCategory_linearEquiv
    (B : BigFppfSite.{u}) (S : Scheme.{u}) [IsLocallyNoetherian S] (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (toS : Spec (.of k) ⟶ S)
    (hk : B.Contains (Spec (.of k)))
    (hfin : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp) (x₀ : X)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx : p.obj x₀ = algebraOver k B S hS toS hk)
    (y : (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection.Fiber
      (residueFieldObject.{u, u, u} Λ k))
    (P : ChosenPushforwardsAt
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection y.1) :
    let D := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
    let hD : Deformation.IsDeformationCategory D.projection :=
      isDeformationCategory_predeformationCategory_of_satisfiesRSStar B S hS p hp hRS iΛ x₀
        hx₀ hfin hqc
    letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
    letI := naturalLocalizedTangentModule P hD.satisfiesRS
    let M : SiteModule k B := (fgSiteModule B hk).obj (FGModuleCat.of k k)
    let L := infinitesimalAutomorphismFunctor k B S hS toS hk p x₀ hx hp hRS
    let t := trivialDeformation k B S hS toS hk p x₀ hx hp M
    let yε := P.obj (dualNumbersUnder (p := D.projection) (x := y.1))
    let IsCompatible : ((D.objects yε.1).point ≅ t.1.right) → Prop := fun η =>
      (D.objects yε.1).arrow ≫ η.hom = t.1.hom ∧
        eqToHom (congrArg Over.left (D.objects yε.1).base).symm ≫
            ((p ⋙ Over.post B.inclusion).map η.hom).left ≫ eqToHom (congrArg Over.left
              (trivialDeformation_right_post B S hS iΛ toS hk p hp x₀ hx₀ hx
                (FGModuleCat.of k k))) =
            Spec.map (CommRingCat.ofHom (CategoryTheory.inv
              (dualNumbersUnderHom (p := D.projection) (x := y.1)) ≫
                eqToHom (yε.2.symm.trans (D.object_projection yε.1))).hom.toRingHom)
    ∃ E : localizedAutomorphismFunctorTangent P ≃ₗ[k] (L.functor.obj M : Type w),
      (∃ η, IsCompatible η) ∧
        ∀ η, IsCompatible η → ∀ a, (L.autEquiv M (E a)).1.right =
          η.inv ≫ (D.morphisms yε.1 yε.1 (localizedTangentEquivKernel P a).1.asIso.hom.1).arrow ≫
            η.hom := by
  intro D hD M L t yε IsCompatible
  let := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
  let := naturalLocalizedTangentModule P hD.satisfiesRS
  obtain ⟨η, hη, hηb, Ψ, hΨ, hδ⟩ := exists_trivialLift_conjugation B S hS iΛ toS hk p hp x₀ hx₀ hx
    hD.predeformation y P
  let K := localizedTangentEquivAut P hD.predeformation
  -- composition of infinitesimal automorphisms of the trivial lift is commutative
  have hcomm : ∀ θ θ' : t ⟶ t, θ.1.right ≫ θ'.1.right = θ'.1.right ≫ θ.1.right := fun θ θ' =>
    congrArg (fun θ : t ⟶ t => θ.1.right)
      (trivialDeformation_hom_comm k B S hS toS hk p x₀ hx hp hRS L M θ θ')
  -- conjugation turns composition of automorphisms into composition of endomorphisms
  have hΨmul : ∀ a b, Ψ (a * b) = Ψ a ≫ Ψ b := by
    intro a b
    apply Functor.Fiber.hom_ext
    apply Under.UnderMorphism.ext
    change (Ψ (a * b)).1.right = (Ψ a).1.right ≫ (Ψ b).1.right
    rw [hΨ, hΨ, hΨ]
    change η.inv ≫ (D.morphisms yε.1 yε.1 (b.asIso.hom.1 ≫ a.asIso.hom.1)).arrow ≫ η.hom = _
    rw [D.reversed_composition]
    simp only [Category.assoc, η.hom_inv_id_assoc]
    rfl
  -- conjugation turns transport along the scaling `ε ↦ cε` into the transition map along `c`
  have hΨsmul : ∀ (c : k) a,
      Ψ (P.transportAutHom (tangentScaling (p := D.projection) (x := y.1) c) a) =
        infAutRestrict k B S hS toS hk p x₀ hx hp
          ((fgSiteModule B hk).map (c • 𝟙 (FGModuleCat.of k k))) (Ψ a) := by
    intro c a
    obtain ⟨δ, hδc⟩ := hδ c
    let s := tangentScaling (p := D.projection) (x := y.1) c
    let ψ := η.inv ≫ (D.morphisms yε.1 yε.1 (P.map s)).arrow ≫ η.hom
    have htr : (D.morphisms yε.1 yε.1 (P.transportAutHom s a).asIso.hom.1).arrow ≫
        (D.morphisms yε.1 yε.1 (P.map s)).arrow =
          (D.morphisms yε.1 yε.1 (P.map s)).arrow ≫
            (D.morphisms yε.1 yε.1 a.asIso.hom.1).arrow := by
      rw [← D.reversed_composition, ← D.reversed_composition]
      exact congrArg (fun f => (D.morphisms yε.1 yε.1 f).arrow) (P.map_transportHom s a)
    have hT : (Ψ (P.transportAutHom s a)).1.right ≫ ψ = ψ ≫ (Ψ a).1.right := by
      rw [hΨ, hΨ]
      simp only [ψ, Category.assoc, η.hom_inv_id_assoc]
      rw [reassoc_of% htr]
    apply fiberEndRestrict_eq
    apply Under.UnderMorphism.ext
    change (Ψ (P.transportAutHom s a)).1.right ≫
        (trivialTransitionUnder k B S hS toS hk p x₀ hx hp
          ((fgSiteModule B hk).map (c • 𝟙 (FGModuleCat.of k k)))).right =
      (trivialTransitionUnder k B S hS toS hk p x₀ hx hp
          ((fgSiteModule B hk).map (c • 𝟙 (FGModuleCat.of k k)))).right ≫ (Ψ a).1.right
    have hφ : (trivialTransitionUnder k B S hS toS hk p x₀ hx hp
          ((fgSiteModule B hk).map (c • 𝟙 (FGModuleCat.of k k)))).right = δ.1.right ≫ ψ :=
      hδc.symm
    rw [hφ, reassoc_of% hcomm (Ψ (P.transportAutHom s a)) δ, hT]
    simp only [ψ, Category.assoc]
  let E₀ : localizedAutomorphismFunctorTangent P ≃ (L.functor.obj M : Type w) :=
    K.trans (Ψ.trans (L.autEquiv M).symm)
  have hE₀ : ∀ a, L.autEquiv M (E₀ a) = Ψ (K a) := fun a => (L.autEquiv M).apply_symm_apply _
  have hadd : ∀ a b, E₀ (a + b) = E₀ a + E₀ b := by
    intro a b
    apply (L.autEquiv M).injective
    rw [autEquiv_add k B S hS toS hk p x₀ hx hp hRS L, hE₀, hE₀, hE₀,
      localizedTangentEquivAut_add P hD.predeformation hD.satisfiesRS, hΨmul]
  have hsmul : ∀ (c : k) a, E₀ (c • a) = c • E₀ a := by
    intro c a
    apply (L.autEquiv M).injective
    rw [hE₀, localizedTangentEquivAut_smul P hD.predeformation hD.satisfiesRS, hΨsmul,
      ← hE₀, ← autEquiv_natural' k B S hS toS hk p x₀ hx hp L]
    congr 1
    have hf : (fgSiteModule B hk).map (c • 𝟙 (FGModuleCat.of k k)) = c • 𝟙 M := rfl
    rw [hf, CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
    rfl
  have hX : ∀ a, (L.autEquiv M (E₀ a)).1.right =
      η.inv ≫ (D.morphisms yε.1 yε.1 (localizedTangentEquivKernel P a).1.asIso.hom.1).arrow ≫
        η.hom :=
    fun a => (congrArg (fun θ : t ⟶ t => θ.1.right) (hE₀ a)).trans (hΨ (K a))
  have hb := trivialDeformation_right_post B S hS iΛ toS hk p hp x₀ hx₀ hx (FGModuleCat.of k k)
  refine ⟨{ E₀ with map_add' := hadd, map_smul' := hsmul }, ⟨η, hη, hηb hb⟩,
    fun η' ⟨hη', hηb'⟩ a => ?_⟩
  -- the two compatible identifications differ by an infinitesimal automorphism of the lift
  let ζ := η.inv ≫ η'.hom
  have hζ₁ : t.1.hom ≫ ζ = t.1.hom := by
    change t.1.hom ≫ η.inv ≫ η'.hom = t.1.hom
    rw [← hη, Category.assoc, η.hom_inv_id_assoc, hη']
    exact hη.symm
  have hleft : ((p ⋙ Over.post B.inclusion).map η'.hom).left =
      ((p ⋙ Over.post B.inclusion).map η.hom).left := by
    rw [← cancel_epi (eqToHom (congrArg Over.left (D.objects yε.1).base).symm),
      ← cancel_mono (eqToHom (congrArg Over.left hb))]
    simpa only [Category.assoc] using hηb'.trans (hηb hb).symm
  have hmap : p.map η'.hom = p.map η.hom :=
    BigFppfOver.map_injective_post_inclusion B S hS (Over.OverMorphism.ext hleft)
  have hζ₂ : p.map ζ = 𝟙 _ := by
    rw [p.map_comp, hmap, ← p.map_comp, η.inv_hom_id, p.map_id]
  let ζ' : t ⟶ t := ⟨Under.homMk ζ hζ₁, IsHomLift.of_fac' (Under.post p) (𝟙 _) _ t.2 t.2 (by
    apply Under.UnderMorphism.ext
    simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]
    exact hζ₂)⟩
  have hc : (L.autEquiv M (E₀ a)).1.right ≫ ζ = ζ ≫ (L.autEquiv M (E₀ a)).1.right :=
    hcomm (L.autEquiv M (E₀ a)) ζ'
  rw [hX a] at hc
  change (L.autEquiv M (E₀ a)).1.right = _
  exact (hX a).trans (conj_eq_conj_of_comm η η' _ ζ rfl hc)

end Statement

end Deformation.Artin

end
