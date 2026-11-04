module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationComponentPushforwardAb
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolution
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentLowerShriekAdjunction

/-!
# The left adjoint of a term of the augmented Čech complex

Let `S` be a simplicial-site situation (Stacks 09WE) and `a` an augmentation of `S` towards a
site `(D, K)` (Stacks 0D6Z). The degree-`n` term of the complex of Stacks 0D79 is the functor
`F ↦ a_{n,*}F_n`, and the degree-`n` term of the resolution of Stacks 0D78 is `𝒢 ↦ g_{n!}(a_n⁻¹𝒢)`.
This file exhibits the second as a left adjoint of the first.

Both halves are composites of adjoint pairs the library already has: `a_n⁻¹ ⊣ a_{n,*}` on abelian
sheaves is the abelian reading of the morphism of topoi of Stacks 0D70, part (1), and
`g_{n!} ⊣ g_n^{-1}` is Stacks 09WG on abelian sheaves. Composing them gives
`g_{n!} ∘ a_n⁻¹ ⊣ a_{n,*} ∘ g_n^{-1}`, and the right-hand side is the degree-`n` term of the
complex of Stacks 0D79 by `abelianComponentPushforwardIso`.

The consequence recorded here is the hom-set bijection

`Hom_D(𝒢, a_{n,*}F_n) ≃ Hom_{C_total}(g_{n!}(a_n⁻¹𝒢), F)`,

which is what turns the complex of Stacks 0D79, tested against an abelian sheaf on the
augmentation site, into `Hom(-, F)` applied to the resolution of Stacks 0D78.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation.componentInverseImageAbAdjunction`: the
  adjunction `a_n⁻¹ ⊣ a_{n,*}` on abelian sheaves.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.cechTermLowerShriek`: the functor
  `𝒢 ↦ g_{n!}(a_n⁻¹𝒢)`, the degree-`n` term of the resolution of Stacks 0D78 as a functor of the
  abelian sheaf on the augmentation site.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.cechTermAdjunction`: the adjunction
  `g_{n!} ∘ a_n⁻¹ ⊣ a_{n,*} ∘ g_n^{-1}` between it and the degree-`n` term of the complex of
  Stacks 0D79.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation.cechTermLowerShriek_obj`: the left adjoint
  of the degree-`n` term of the complex of Stacks 0D79 is the degree-`n` term `g_{n!}(a_n⁻¹𝒢)` of
  the resolution of Stacks 0D78.

## References

* [Stacks Project, Tag 0D79](https://stacks.math.columbia.edu/tag/0D79)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Topos.AbelianPushforward
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K) (n : SimplexCategory)

/-- **Stacks 0D70, part (1), on abelian sheaves.** The inverse image `a_n⁻¹` along the
augmentation of the simplicial degree `n` is left adjoint to the direct image `a_{n,*}` along it:
both are the functors the geometric adjunction induces on commutative group objects, read through
the identification of abelian sheaves with commutative group objects. -/
def componentInverseImageAbAdjunction :
    componentInverseImageAb S D K a n ⊣
      abelianPushforward (S.componentTopology n) (componentAugmentation S D K a n) :=
  abelianInverseImageAdjPushforward (S.componentTopology n) (componentAugmentation S D K a n)

/-- The functor `𝒢 ↦ g_{n!}(a_n⁻¹𝒢)` on abelian sheaves: the inverse image along the augmentation
of the simplicial degree `n`, extended by zero from the component of that degree to the total
site. This is the degree-`n` term of the resolution of Stacks 0D78, as a functor of the abelian
sheaf on the augmentation site. -/
abbrev cechTermLowerShriek : Sheaf K Ab.{u} ⥤ Sheaf S.totalTopology Ab.{u} :=
  componentInverseImageAb S D K a n ⋙ componentLowerShriekAb S n

variable [HasSheafify K Ab.{u}]

/-- **The degree-`n` term of the complex of Stacks 0D79 is a right adjoint, and its left adjoint
is the degree-`n` term of the resolution of Stacks 0D78.** The term is `a_{n,*} ∘ g_n^{-1}` by
`abelianComponentPushforwardIso`, and composing the adjunction `g_{n!} ⊣ g_n^{-1}` of
Stacks 09WG with the adjunction `a_n⁻¹ ⊣ a_{n,*}` of Stacks 0D70, part (1), presents its left
adjoint as `g_{n!} ∘ a_n⁻¹`. -/
def cechTermAdjunction :
    cechTermLowerShriek S D K a n ⊣ abelianComponentPushforward S D K a n :=
  ((componentInverseImageAbAdjunction S D K a n).comp
      (S.componentLowerShriekAbAdjunction n)).ofNatIsoRight
    (abelianComponentPushforwardIso S D K a n).symm

omit [HasSheafify K Ab.{u}] in
/-- The left adjoint of the degree-`n` term of the complex of Stacks 0D79 is the degree-`n` term
`g_{n!}(a_n⁻¹𝒢)` of the resolution of Stacks 0D78. -/
theorem cechTermLowerShriek_obj (G : Sheaf K Ab.{u}) (m : ℕ) :
    (cechTermLowerShriek S D K a ⦋m⦌).obj G = resolutionTerm S D K a G m :=
  rfl

/-- A morphism from an abelian sheaf on the augmentation site into the degree-`n` term
`a_{n,*}F_n` of the complex of Stacks 0D79 is the same thing as a morphism `g_{n!}(a_n⁻¹𝒢) ⟶ F`
on the total site: this is the transposition the proof of Stacks 0D79 performs before applying
`Hom(-, F)` to the resolution of Stacks 0D78. -/
theorem cechTermAdjunction_homEquiv_symm_naturality_right
    (G : Sheaf K Ab.{u}) {F F' : Sheaf S.totalTopology Ab.{u}} (α : F ⟶ F')
    (u : G ⟶ (abelianComponentPushforward S D K a n).obj F) :
    ((cechTermAdjunction S D K a n).homEquiv G F').symm
        (u ≫ (abelianComponentPushforward S D K a n).map α) =
      ((cechTermAdjunction S D K a n).homEquiv G F).symm u ≫ α :=
  (cechTermAdjunction S D K a n).homEquiv_naturality_right_symm u α

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
