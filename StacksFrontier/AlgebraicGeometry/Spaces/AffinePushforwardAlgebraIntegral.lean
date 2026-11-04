module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyInjectiveCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteAlgebraSurjectiveSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardAlgebraChartBaseChange

/-!
# The direct-image algebra of an integral affine morphism is integral

Let `g : Y ⟶ X` be an affine morphism of algebraic spaces over `S` which is *integral* in the
sense of Stacks 03ZP.  Then the quasi-coherent `𝒪_X`-algebra `g_* 𝒪_Y` is integral, in the sense
of `AlgebraicGeometry.Space.AlgebraSheaf.IsIntegral`: its structure-algebra map is an integral
ring map on every affine étale chart of `X`.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.IsIntegral.of_iso`: integrality of an algebra sheaf is
  invariant under isomorphism.
* `AlgebraicGeometry.Space.isIntegral_pushforwardAlgebra_over_of_isIntegralHom`: `g_* 𝒪_Y` is
  integral for an integral representable `g`.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraSheaf

variable {B S hS}
variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **Integrality is invariant under isomorphism of algebra sheaves.** -/
theorem IsIntegral.of_iso {A C : AlgebraSheaf.{u, m} B S hS F hF} (e : A ≅ C)
    (hA : A.IsIntegral) : C.IsIntegral :=
  IsIntegral.of_surjective_app e.hom (fun U _ => (bijective_iso_right_app e (op U)).2) hA

end AlgebraSheaf

variable {X : AlgebraicSpaces B S hS}

/-- **The direct-image algebra of an integral morphism is integral**: for a relatively
representable integral morphism `g : Y ⟶ X`, the algebra `g_* 𝒪_Y` is integral. -/
theorem isIntegral_pushforwardAlgebra_over_of_isIntegralHom (g : Over X)
    (hg : yoneda.relativelyRepresentable g.hom.hom)
    (hint : IsIntegralHom B S hS g.hom.hom) :
    (pushforwardAlgebra B S hS g).IsIntegral := by
  refine AlgebraSheaf.IsIntegral.of_iso (chartSharpAlgebraIso B S hS g hg).symm ?_
  intro V hV
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V.obj.left) := hV
  have hsnd : _root_.AlgebraicGeometry.IsIntegralHom
      ((BigFppfOver.toScheme B S hS).map (hg.snd V.1.hom)) :=
    isIntegralHom_toScheme_map_snd B S hS g.left.2 X.2 hg hint V.1.hom
  have hmap : (AlgebraSheaf.ofHom
        (smallBaseChangeSharpCommRingCat B S hS g.hom hg)).algebraMap (op V) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hg.snd V.1.hom)).op).hom := rfl
  rw [hmap, Scheme.Γ_map_op]
  exact _root_.AlgebraicGeometry.IsIntegralHom.isIntegral_app _ ⊤ (isAffineOpen_top _)

end AlgebraicGeometry.Space

end
