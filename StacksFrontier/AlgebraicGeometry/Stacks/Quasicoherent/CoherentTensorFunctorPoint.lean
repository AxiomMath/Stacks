module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoherentPointPullbackUniqueness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoherentTensorExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.TensorFunctorPoint

/-!
# Tensor functors on coherent modules come from points (Stacks 0GRR)

Let `𝒳` be a Noetherian algebraic stack with affine diagonal, `R` a Noetherian ring and
`F : Coh(𝒪_𝒳) ⥤ Mod^{fg}_R` a right exact tensor functor. Then `F` comes from a unique morphism
`Spec R ⟶ 𝒳`. Following the source: by Stacks 0GRJ
(`AlgebraicGeometry.Stack.AlgebraicStacks.exists_coherentTensorExtension`) `F` extends to a right
exact tensor functor `QCoh(𝒪_𝒳) ⥤ Mod_R` commuting with all colimits, to which Stacks 0GRQ
(`AlgebraicGeometry.Stack.AlgebraicStacks.exists_iso_pointPullback_of_tensorFunctor`) applies;
uniqueness is `eq_and_exists_iso_of_iso_coherentPointPullback_of_isNoetherianStack`
(namespace `AlgebraicGeometry.Stack.AlgebraicStacks`).

## Main results

* `existsUnique_coherentPointPullback_iso_of_tensorFunctor`: a right exact tensor functor
  `Coh(𝒪_𝒳) ⥤ Mod^{fg}_R` is isomorphic to coherent pullback along a unique `Spec R ⟶ 𝒳`.

## References

* [Stacks Project, Tag 0GRR](https://stacks.math.columbia.edu/tag/0GRR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Functor.LaxMonoidal

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w w'

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] coherentAmbientMonoidal coherentAmbientBraided coherentAmbientSymmetric
  fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric
  coherentQuasicoherentInclusionBraided

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {R : Type u} [CommRing R]

/-- **Stacks 0GRR.** Let `𝒳` be a Noetherian algebraic stack with affine diagonal (over `Spec ℤ`,
as in the source), `R` a Noetherian ring (with `Spec R` in the site) and
`F : Coh(𝒪_𝒳) ⥤ Mod^{fg}_R` a right exact tensor functor (additive, preserving finite colimits,
braided monoidal). Then `F` comes from a unique morphism `Spec R ⟶ 𝒳`:

1. there are a point `x` of `𝒳` over `Spec R` (lying over some `q : Spec R ⟶ S`) and an
   isomorphism of tensor functors `F ≅ x^*|_{Coh}`;
2. if `E₁ : F ≅ x₁^*|_{Coh}` and `E₂ : F ≅ x₂^*|_{Coh}` are two such, over `q₁` and `q₂`, then
   `q₁ = q₂` and there is a 2-arrow `a : x₁ ≅ x₂` over the identity of `Spec R` inducing
   `E₁⁻¹ ≫ E₂` on coherent modules. -/
@[stacks 0GRR "the morphism Spec R ⟶ 𝒳 is a point over Spec R in the site; uniqueness is up to \
  a 2-arrow inducing the given isomorphism of tensor functors"]
theorem existsUnique_coherentPointPullback_iso_of_tensorFunctor
    (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳)
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (Stack.diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (AlgebraicStacks.viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val))
    [IsNoetherianRing R] (hR : B.Contains (Spec (CommRingCat.of R)))
    (F : Coh.{u, u, w} B S hS 𝒳 ⥤ FGModuleCat.{u} R) [F.Additive] [F.Braided]
    [PreservesFiniteColimits F] :
    (∃ (q : B.obj hR ⟶ B.obj hS) (x : 𝒳.val.val.obj) (hx : 𝒳.val.val.p.obj x = Over.mk q)
      (E : F ≅ coherentPointPullback B S hS 𝒳 x (overSpecIso B S hS 𝒳 hx)),
        NatTrans.IsMonoidal E.hom) ∧
    ∀ {q₁ q₂ : B.obj hR ⟶ B.obj hS} {x₁ x₂ : 𝒳.val.val.obj}
      (hx₁ : 𝒳.val.val.p.obj x₁ = Over.mk q₁) (hx₂ : 𝒳.val.val.p.obj x₂ = Over.mk q₂)
      (E₁ : F ≅ coherentPointPullback B S hS 𝒳 x₁ (overSpecIso B S hS 𝒳 hx₁))
      (E₂ : F ≅ coherentPointPullback B S hS 𝒳 x₂ (overSpecIso B S hS 𝒳 hx₂)),
      NatTrans.IsMonoidal E₁.hom → NatTrans.IsMonoidal E₂.hom →
      q₁ = q₂ ∧ ∃ (a : x₁ ≅ x₂) (ha : (BigFppfOver.toScheme B S hS).map
          (𝒳.val.val.p.map a.hom) ≫ (overSpecIso B S hS 𝒳 hx₂).hom =
            (overSpecIso B S hS 𝒳 hx₁).hom),
        Functor.whiskerLeft (coherentQuasicoherentInclusion B S hS 𝒳)
            (pointPullbackTransportIso B S hS 𝒳 (overSpecIso B S hS 𝒳 hx₁)
              (overSpecIso B S hS 𝒳 hx₂) a ha).hom =
          (coherentPointPullbackCompIso B S hS 𝒳 x₁ _).inv ≫
            Functor.whiskerRight (E₁.inv ≫ E₂.hom)
              (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)) ≫
              (coherentPointPullbackCompIso B S hS 𝒳 x₂ _).hom := by
  refine ⟨?_, fun hx₁ hx₂ E₁ E₂ h₁ h₂ ↦
    eq_and_exists_iso_of_iso_coherentPointPullback_of_isNoetherianStack B S hS h𝒳 hΔ F hx₁ hx₂
      E₁ E₂⟩
  obtain ⟨G, hGa, hGb, hGf, hGc, e, he⟩ := exists_coherentTensorExtension h𝒳 F
  have : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) G := fun _ ↦ inferInstance
  obtain ⟨q, x, hx, t, ht⟩ := exists_iso_pointPullback_of_tensorFunctor h𝒳 hΔ hR G
  have : NatTrans.IsMonoidal (e.symm ≪≫ Functor.isoWhiskerLeft _ t).hom :=
    inferInstanceAs (NatTrans.IsMonoidal (e.inv ≫ Functor.whiskerLeft _ t.hom))
  obtain ⟨E, hE⟩ := exists_iso_coherentPointPullback_of_iso B S hS F x _
    (e.symm ≪≫ Functor.isoWhiskerLeft _ t)
  exact ⟨q, x, hx, E, hE⟩

end AlgebraicGeometry.Stack.AlgebraicStacks
