module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.AcyclicityProductHypercovering
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionFreeYonedaComplex
import StacksFrontier.CategoryTheory.Abelian.Projective.ResolutionLift

/-!
# The `a_!`-image of the resolution of Stacks 0D78 of `a^{-1}ℤ_V^♯` is a quasi-isomorphism

Let `(C, J)` be a small site with equalizers and fibre products, `K` a hypercovering of the
terminal presheaf of `C` and `V` an object of `C`. Stacks 0D78 resolves `a^{-1}ℤ_V^♯` on the total
site of the simplicial-site situation of `K` by the extensions by zero `g_{p!}(a_p^{-1}ℤ_V^♯)`;
this module proves that the extension by zero `a_!` along the augmentation carries the
augmentation of that resolution to a quasi-isomorphism. That statement is the one hypothesis the
cohomological descent of a hypercovering still carried: it is `h` of
`CategoryTheory.SimplicialSemiRepresentable`
`.inverseImageComputesDerivedPushforward_of_quasiIso_freeYoneda_chain`.

The proof is `ChainComplex.quasiIsoAt₀_iff` separating degree zero from the positive degrees, and
the two halves are proved by genuinely different means.

* **In every positive degree** the statement is exactness of the `a_!`-image of the complex of
  Stacks 0D78, which
  `CategoryTheory.SimplicialSemiRepresentable.exactAt_map_resolutionComplex` reduces to exactness
  of the complex of Stacks 01GE for `p ↦ h_V × F(K_p)`. That complex is the one
  `Stacks.CategoryTheory.Hypercovering`
  `.quasiIso_freeAbelianSheafResolutionAugmentation_prodConst_yoneda_comp` resolves `ℤ_V^♯` by, on
  the nose: the functor `L ↦ ℤ_{h_V × F(L)}^♯` of
  `CategoryTheory.SemiRepresentable.freeYonedaProd` *is* the composite of the formal-coproduct
  Yoneda embedding, the product with `h_V` and the free abelian sheaf, so the two complexes are
  equal and not merely isomorphic. The transport is therefore only
  `Stacks.CategoryTheory.Hypercovering.freeAbelianSheafComplexProdConstIsoYoneda`, the image under
  the complex functor of the identification of the underlying simplicial presheaves.
* **In degree zero** the statement is that the `a_!`-image of the augmentation exhibits
  `a_!a^{-1}ℤ_V^♯` as the cokernel of the `a_!`-image of the first differential, and this is
  formal: no identification of `a_!a^{-1}ℤ_V^♯` is involved, nor available. Exactness at the
  augmentation and epimorphy of the augmentation of Stacks 0D78 say that `a^{-1}ℤ_V^♯` is the
  cokernel of the first differential, by
  `CategoryTheory.ShortComplex.exact_and_epi_g_iff_g_is_cokernel`, and `a_!` is a left adjoint, so
  it preserves that colimit.

## Main results

* `ChainComplex.quasiIsoAt₀_map_of_quasiIso`: an additive functor preserving finite colimits
  carries a resolution `ε : Q ⟶ Z[0]` to a morphism that is a quasi-isomorphism *in degree zero*.
  Only right exactness is used, so this is the half of a resolution that survives a functor which
  is merely right exact.
* `CategoryTheory.SimplicialSemiRepresentable.exactAt_succ_freeYonedaSimplicial`: the complex of
  Stacks 01GE for `p ↦ h_V × F(K_p)` is exact in every positive degree.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.quasiIso_map_resolutionChainAugmentation_freeYoneda`: **`a_!` carries the augmentation of the
  resolution of Stacks 0D78 of `a^{-1}ℤ_V^♯` to a quasi-isomorphism.**

## Implementation notes

`CategoryTheory.Limits.PreservesFiniteColimits (augmentationAbelianLowerShriek J K)` is not found
by instance search; it is supplied from
`CategoryTheory.Adjunction.leftAdjoint_preservesColimits` applied to
`CategoryTheory.SimplicialSemiRepresentable.augmentationAbelianLowerShriekAdjunction`, which is
Stacks 09WM part (2).

## References

* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 01GE](https://stacks.math.columbia.edu/tag/01GE)
* [Stacks Project, Tag 09WM](https://stacks.math.columbia.edu/tag/09WM)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialSiteSituation

universe v u v₂ u₂

namespace ChainComplex

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {Z : A} {Q : ChainComplex A ℕ} (F : A ⥤ B) [F.Additive]

/-- **The image of a complex concentrated in degree zero is exact in every positive degree.** The
image is the complex concentrated in degree zero on the image, by
`HomologicalComplex.singleMapHomologicalComplex`. -/
theorem exactAt_succ_map_single₀ (Z : A) (n : ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((ChainComplex.single₀ A).obj Z)).ExactAt (n + 1) :=
  HomologicalComplex.ExactAt.of_iso (ChainComplex.exactAt_succ_single_obj (F.obj Z) n)
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).app Z).symm

/-- **An additive functor preserving finite colimits carries a resolution to a morphism which is
a quasi-isomorphism in degree zero.** For `ε : Q ⟶ Z[0]` a quasi-isomorphism, the degree-zero
content is that `Z` is the cokernel of `Q.d 1 0`, by
`CategoryTheory.ShortComplex.exact_and_epi_g_iff_g_is_cokernel`; a functor preserving finite
colimits preserves that cokernel.

Only right exactness of `F` is used. The positive degrees are *not* preserved by a merely
right-exact functor, which is why they are not part of this statement. -/
theorem quasiIsoAt₀_map_of_quasiIso [PreservesFiniteColimits F]
    (ε : Q ⟶ (ChainComplex.single₀ A).obj Z) [QuasiIso ε] :
    QuasiIsoAt ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map ε) 0 := by
  have key : ∀ S : ShortComplex A, S.Exact ∧ Epi S.g → (S.map F).Exact ∧ Epi (F.map S.g) :=
    ((Functor.preservesFiniteColimits_tfae F).out 4 2).1 ‹_›
  rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
  · exact key _ (ChainComplex.exact₀_and_epi_of_quasiIso ε)
  · exact (congrArg F.map (Q.shape 0 0 (by simp))).trans (F.map_zero _ _)
  all_goals exact F.map_zero _ _

end ChainComplex

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable Stacks.CategoryTheory.Hypercovering
open Stacks.Cohomology.CohomologyPresheaf

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (P : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} P) (V : C)

/-- **Stacks 01GE for a hypercovering of the terminal presheaf with coefficients in `ℤ_V^♯`, in
the spelling the resolution of Stacks 0D78 is identified with.** The complex of free abelian
sheaves on `p ↦ h_V × F(K_p)` is exact in every positive degree.

The complex `freeYonedaSimplicial` is built from
`CategoryTheory.SemiRepresentable.freeYonedaProd`, and that functor *is* the formal-coproduct
Yoneda embedding followed by the product with `h_V` and the free abelian sheaf; so the complex of
Stacks 01GE for the simplicial presheaf `h_V × F(K)` and the alternating face map complex of
`freeYonedaSimplicial` are equal, and the only transport needed is
`Stacks.CategoryTheory.Hypercovering.freeAbelianSheafComplexProdConstIsoYoneda`, which identifies
the simplicial presheaf underlying `h_V × A` with `p ↦ h_V × F(K_p)`. -/
theorem exactAt_succ_freeYonedaSimplicial (n : ℕ) :
    ((AlgebraicTopology.alternatingFaceMapComplex
        (Sheaf P.toGrothendieck AddCommGrpCat.{u})).obj
      (freeYonedaSimplicial P.toGrothendieck H.toSimplicialObject V)).ExactAt (n + 1) := by
  exact HomologicalComplex.ExactAt.of_iso
    (@ChainComplex.exactAt_succ_of_quasiIso _ _ _ _ _ _
      (quasiIso_freeAbelianSheafResolutionAugmentation_prodConst_yoneda_comp P H V) n)
    (freeAbelianSheafComplexProdConstIsoYoneda P (⊤_ (Cᵒᵖ ⥤ Type u)) H (yoneda.obj V))

/-- **The extension by zero `a_!` carries the augmentation of the resolution of Stacks 0D78 of
`a^{-1}ℤ_V^♯` to a quasi-isomorphism**, for a hypercovering `K` of the terminal presheaf of
`(C, J)` and every object `V` of `C`.

This is the hypothesis `h` of
`inverseImageComputesDerivedPushforward_of_quasiIso_freeYoneda_chain`, and with it the
cohomological descent of a hypercovering is unconditional.

`ChainComplex.quasiIsoAt₀_iff` separates the two halves. In degree zero the statement is formal,
`ChainComplex.quasiIsoAt₀_map_of_quasiIso` applied to the resolution of Stacks 0D78 — `a_!` is a
left adjoint by Stacks 09WM part (2), so it preserves the cokernel that exactness at the
augmentation and epimorphy of the augmentation amount to. In a positive degree it is exactness of
the `a_!`-image of the complex, which `exactAt_map_resolutionComplex` reduces to
`exactAt_succ_freeYonedaSimplicial`, that is to Stacks 01GE. -/
theorem quasiIso_map_resolutionChainAugmentation_freeYoneda :
    QuasiIso (((augmentationAbelianLowerShriek P.toGrothendieck
          H.toSimplicialObject).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (Augmentation.resolutionChainAugmentation
        (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
        (situationAugmentation P.toGrothendieck H.toSimplicialObject)
        (freeYonedaSheaf P.toGrothendieck V))) := by
  have : PreservesColimitsOfSize.{0, 0}
      (augmentationAbelianLowerShriek P.toGrothendieck H.toSimplicialObject) :=
    (augmentationAbelianLowerShriekAdjunction P.toGrothendieck
      H.toSimplicialObject).leftAdjoint_preservesColimits
  constructor
  rintro (_ | m)
  · exact ChainComplex.quasiIsoAt₀_map_of_quasiIso _ _
  · rw [quasiIsoAt_iff_exactAt' _ (m + 1) (ChainComplex.exactAt_succ_map_single₀ _ _ m)]
    exact exactAt_map_resolutionComplex P.toGrothendieck H.toSimplicialObject V (m + 1)
      (exactAt_succ_freeYonedaSimplicial P H V m)

end CategoryTheory.SimplicialSemiRepresentable

end
