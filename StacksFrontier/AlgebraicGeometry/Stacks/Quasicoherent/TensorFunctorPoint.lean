module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.TensorFunctorPointExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineTensorPullbackMonoidal
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianStack
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphismConstructionA

/-!
# Tensor functors on quasi-coherent modules come from points (Stacks 0GRQ)

Let `𝒳` be a Noetherian algebraic stack with affine diagonal, `R` a ring and
`F : QCoh(𝒪_𝒳) ⥤ Mod_R` a right exact tensor functor which commutes with direct sums. Then `F`
comes from a unique morphism `Spec R ⟶ 𝒳`: there is a point `x` of `𝒳` over `Spec R` and an
isomorphism of tensor functors `F ≅ x^*`, and any two such are related by a unique 2-arrow.

The proof follows the source. Choose an affine smooth surjective chart `g : U = Spec A ⟶ 𝒳`
(Stacks 04YC; affine because the diagonal is). Stacks 0GRK gives `C = F(g_*𝒪_U)` and `A ⟶ C`;
by Stacks 0GRL and 0GRM the map `R ⟶ C` is faithfully flat. The point `x_C : Spec C ⟶ U ⟶ 𝒳`
satisfies `F(-) ⊗_R C ≅ x_C^*` as tensor functors
(`AlgebraicGeometry.Stack.AlgebraicStacks.isMonoidal_localizedPointPullbackTensorIso`), and
`x_C` descends along `Spec C ⟶ Spec R` by Stacks 0GRP and 0GRH
(`AlgebraicGeometry.Stack.AlgebraicStacks.exists_iso_pointPullback_of_trivialization`).
Uniqueness is Stacks 0GRP with the rigidity of points along the chart
(`AlgebraicGeometry.Stack.AlgebraicStacks.eq_and_existsUnique_iso_of_iso_pointPullback`).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_iso_pointPullback_of_tensorFunctor`: existence.
* `AlgebraicGeometry.Stack.AlgebraicStacks.existsUnique_pointPullback_iso_of_tensorFunctor`:
  **Stacks 0GRQ**.

## References

* [Stacks Project, Tag 0GRQ](https://stacks.math.columbia.edu/tag/0GRQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w w'

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **Existence in Stacks 0GRQ.** Let `𝒳` be a Noetherian algebraic stack with affine (absolute)
diagonal, `R` a ring with `Spec R` in the site and `F : QCoh(𝒪_𝒳) ⥤ Mod_R` an additive, right
exact, braided monoidal functor commuting with direct sums. Then there are a point `x` of `𝒳`
over `Spec R` (over a morphism `q : Spec R ⟶ S`) and an isomorphism of tensor functors
`F ≅ x^*`. -/
theorem exists_iso_pointPullback_of_tensorFunctor
    (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳)
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (Stack.diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val))
    {R : Type u} [CommRing R] (hR : B.Contains (Spec (CommRingCat.of R)))
    (F : quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R) [F.Additive] [F.Braided]
    [PreservesFiniteColimits F] [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F] :
    ∃ (q : B.obj hR ⟶ B.obj hS) (x : 𝒳.val.val.obj) (hx : 𝒳.val.val.p.obj x = Over.mk q)
      (e : F ≅ pointPullback B S hS 𝒳 x (overSpecIso B S hS 𝒳 hx)), NatTrans.IsMonoidal e.hom := by
  obtain ⟨U, hU, g, hsurj, hsmooth⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒳).1 h𝒳.1
  obtain ⟨hfrep, hrel⟩ := hsmooth
  have hsm : AlgebraicStacks.IsSmooth B S hS g :=
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ h => Space.IsSmooth B S hS h) 𝒳.property g.hom hfrep hrel
  let g' : schemeStack.{u, w} B S hS U ⟶ 𝒳 := g
  have hg : IsAffineHom B S hS g' :=
    isAffineHom_of_isAffineHom_diagonal_viewOverIntegers B S hS (contains_terminalScheme B) hU
      hΔ g'
  have hfl : IsFlat B S hS g' := isFlat_of_isSmooth B S hS g' hsm
  let hF : @Functor.Braided _ _ (quasicoherentModulesMonoidal B S hS 𝒳)
      (quasicoherentModulesBraided B S hS 𝒳) _ _ _ _ F := inferInstance
  let := localizedBraided F hF
  let := additive_comparisonInverse_comp F
  let : PreservesFiniteColimits ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) :=
    inferInstanceAs (PreservesFiniteColimits F)
  let : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) :=
    fun J => inferInstanceAs (PreservesColimitsOfShape (Discrete J) F)
  have hff := faithfullyFlat_affineTensorAlgebra g' hg
    ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) hΔ h𝒳 hU hfl hsurj
  have hC := contains_spec_affineTensorAlgebra g' hg
    ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) hU hR hff
  obtain ⟨qC, y, hy, ψ, hψ⟩ := exists_point_over_affineTensorAlgebra g' hg
    ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) hU hC
  let θ := localizedPointPullbackTensorIso g' hg F hU (overSpecIso B S hS 𝒳 hy) ψ hψ
  have : NatTrans.IsMonoidal θ.hom :=
    isMonoidal_localizedPointPullbackTensorIso g' hg F hU (overSpecIso B S hS 𝒳 hy) ψ hψ
  exact exists_iso_pointPullback_of_trivialization θ hΔ U g' hg hsm hsurj hR hff

/-- **Stacks 0GRQ.** Let `𝒳` be a Noetherian algebraic stack with affine diagonal (over
`Spec ℤ`, as in the source), `R` a ring (with `Spec R` in the site) and `F : QCoh(𝒪_𝒳) ⥤ Mod_R` a
right exact tensor functor (additive, preserving finite colimits, braided monoidal) which commutes
with direct sums. Then `F` comes from a unique morphism `Spec R ⟶ 𝒳`:

1. there are a point `x` of `𝒳` over `Spec R` (lying over some `q : Spec R ⟶ S`) and an
   isomorphism of tensor functors `e : F ≅ x^*`;
2. if `e₁ : F ≅ x₁^*` and `e₂ : F ≅ x₂^*` are two such, over `q₁` and `q₂`, then `q₁ = q₂` and
   there is a unique 2-arrow `a : x₁ ≅ x₂` over the identity of `Spec R` whose induced isomorphism
   `x₁^* ≅ x₂^*` is `e₁⁻¹ ≫ e₂`. -/
@[stacks 0GRQ "the morphism Spec R ⟶ 𝒳 is a point over Spec R in the site; uniqueness is up to \
  the unique 2-arrow inducing the given isomorphism of tensor functors"]
theorem existsUnique_pointPullback_iso_of_tensorFunctor
    (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳)
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (Stack.diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val))
    {R : Type u} [CommRing R] (hR : B.Contains (Spec (CommRingCat.of R)))
    (F : quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R) [F.Additive] [F.Braided]
    [PreservesFiniteColimits F] [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F] :
    (∃ (q : B.obj hR ⟶ B.obj hS) (x : 𝒳.val.val.obj) (hx : 𝒳.val.val.p.obj x = Over.mk q)
        (e : F ≅ pointPullback B S hS 𝒳 x (overSpecIso B S hS 𝒳 hx)), NatTrans.IsMonoidal e.hom) ∧
    ∀ {q₁ q₂ : B.obj hR ⟶ B.obj hS} {x₁ x₂ : 𝒳.val.val.obj}
      (hx₁ : 𝒳.val.val.p.obj x₁ = Over.mk q₁) (hx₂ : 𝒳.val.val.p.obj x₂ = Over.mk q₂)
      (e₁ : F ≅ pointPullback B S hS 𝒳 x₁ (overSpecIso B S hS 𝒳 hx₁))
      (e₂ : F ≅ pointPullback B S hS 𝒳 x₂ (overSpecIso B S hS 𝒳 hx₂)),
      NatTrans.IsMonoidal e₁.hom → NatTrans.IsMonoidal e₂.hom →
      q₁ = q₂ ∧ ∃ (a : x₁ ≅ x₂) (ha : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a.hom) ≫
          (overSpecIso B S hS 𝒳 hx₂).hom = (overSpecIso B S hS 𝒳 hx₁).hom),
        pointPullbackTransportIso B S hS 𝒳 (overSpecIso B S hS 𝒳 hx₁) (overSpecIso B S hS 𝒳 hx₂)
            a ha = e₁.symm ≪≫ e₂ ∧
          ∀ (b : x₁ ≅ x₂) (hb : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map b.hom) ≫
              (overSpecIso B S hS 𝒳 hx₂).hom = (overSpecIso B S hS 𝒳 hx₁).hom),
            pointPullbackTransportIso B S hS 𝒳 (overSpecIso B S hS 𝒳 hx₁)
              (overSpecIso B S hS 𝒳 hx₂) b hb = e₁.symm ≪≫ e₂ → b = a :=
  ⟨exists_iso_pointPullback_of_tensorFunctor h𝒳 hΔ hR F,
    fun hx₁ hx₂ e₁ e₂ he₁ he₂ =>
      eq_and_existsUnique_iso_of_iso_pointPullback h𝒳.1 hΔ F hx₁ hx₂ e₁ e₂ he₁ he₂⟩

end AlgebraicGeometry.Stack.AlgebraicStacks
