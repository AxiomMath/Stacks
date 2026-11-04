module

public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.HypercoveringAllModules
public import StacksFrontier.CategoryTheory.Sites.FormalCoproductTerminalAugmentation
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.HomComplexAugmentation

/-!
# The augmentation of the relative hypercovering complex

Let `f : X ⟶ S` be a morphism of schemes and `K` a simplicial object of formal coproducts of opens
of `X`.  `Stacks.AlgebraicGeometry.UniversalPushforward.hypercoveringPushforwardComplexAll` is the
complex

`𝓚⁼(K, f, M) = ( ∏_{i ∈ I₀} f_{i,*}M|_{U_i} ⟶ ∏_{i ∈ I₁} f_{i,*}M|_{U_i} ⟶ ⋯ )`

of `𝒪_S`-modules, as a functor of an arbitrary `𝒪_X`-module `M`.  This file constructs its
augmentation

`ε : (f_*M)[0] ⟶ 𝓚⁼(K, f, M)`,

natural in `M`.  Together with the additivity of `𝓚⁼(K, f, -)` and its vanishing in negative
degrees, this is all but one of the inputs the comparison machinery of
`StacksDraft.DerivedSectionsComparison` — the construction in the proof of [Stacks, Tag 09VX] —
asks for; the remaining one is that `ε` be a quasi-isomorphism at an injective module.

The augmentation itself is `Stacks.CategoryTheory.FormalCoproductAugmentation.terminalAugNatTrans`,
the generic augmentation of a Čech-style complex of formal coproducts at a terminal object of the
indexing category.  Here that indexing category is `Over (⊤ : Opens X)` and its terminal object is
`Over.mk (𝟙 (⊤ : Opens X))`, at which the coefficient presheaf takes the value

`(ι_⊤ ≫ f)_* ι_⊤^* M`,  where  `ι_⊤ : ⊤ ⟶ X`

is the inclusion of the top open.  That is *not* `f_*M`:  `ι_⊤` is an isomorphism of schemes but
not the identity, so the identification needs an isomorphism, which is `topCoefficientIso` below.
This is the one point at which the present situation differs from the Čech situation of
`StacksFrontier.AlgebraicGeometry.CechSiteChange.Resolution`, where the indexing category is `Over X`,
its terminal object is `Over.mk (𝟙 X)`, and the corresponding comparison is the identity.

## Main definitions

* `overMkIdIsoOpensTop`:  `Over.mk (𝟙 X)` and `Over.mk ι_⊤` are isomorphic objects of `Over X`.
* `idMonadIso`, `topMonadIso`:  the monad `a_*a^*` of the identity is the identity functor, and
  therefore so is the monad of `ι_⊤`.
* `topCoefficientIso`:  **the identification `f_*M ≅ (ι_⊤ ≫ f)_* ι_⊤^* M`**, natural in `M`.
* `hypercoveringAugNat`:  the augmentation before the passage to integer degrees, of the
  coefficient presheaf itself rather than of the module.
* `hypercoveringAugAll`:  **the augmentation `ε`**, as a natural transformation
  `f_*(-)[0] ⟶ 𝓚⁼(K, f, -)`.

## Main results

* `hypercoveringAugAll_naturality`:  the naturality of `ε` in the module, in the form the
  hypothesis `hε` of `StacksDraft.DerivedSectionsComparison` is stated in.
* `hypercoveringAugNat_app_f_zero`:  the degree-zero component of the `ℕ`-indexed augmentation is
  the product of the restriction maps to the members of `K₀`.

## Implementation notes

The identification `(pushforwardPresheafAll f) ⋙ ev_{Over.mk (𝟙 ⊤)}` with
`ι_⊤^* ⋙ (ι_⊤ ≫ f)_*` is an *equality* of functors and holds by `rfl`:  the coefficient presheaf
is built from `relativeMonad`, whose value at an object of `Over X` is `a^* ⋙ a_*` by definition,
and pushforward is strictly functorial in this `Mathlib`
(`Stacks.AlgebraicGeometry.RelativeCech.pushforward_comp_functor_map`), so
`ι_⊤^* ⋙ ι_{⊤,*} ⋙ f_*` is `ι_⊤^* ⋙ (ι_⊤ ≫ f)_*` on the nose.  No `eqToHom` is therefore needed
anywhere below, and `topCoefficientIso` is stated directly at the evaluated coefficient presheaf.

`topMonadIso` is obtained from `relativeMonad X` applied to `overMkIdIsoOpensTop`, rather than
constructed by hand:  `relativeMonad X` is a functor, so it carries that isomorphism of objects of
`Over X` to an isomorphism of monads, and the monad of the identity is the identity functor by
`pullbackId` and `pushforwardId`.  The alternative — showing directly that the unit of
`ι_⊤^* ⊣ ι_{⊤,*}` is invertible — would need `ι_⊤^*` to be exhibited as an equivalence.

## References

* [Stacks Project, Tag 01XN](https://stacks.math.columbia.edu/tag/01XN)
* [Stacks Project, Tag 09VX](https://stacks.math.columbia.edu/tag/09VX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.RelativeCech
open Stacks.CategoryTheory.FormalCoproductAugmentation

universe u

namespace Stacks.AlgebraicGeometry.UniversalPushforward

variable {X S : Scheme.{u}}

/-! ### The top open as the terminal object -/

/-- **`Over.mk (𝟙 X)` and `Over.mk ι_⊤` are isomorphic objects of `Over X`.**  The isomorphism of
their sources is `AlgebraicGeometry.Scheme.topIso`, and it is compatible with the structure
morphisms because the inverse of that isomorphism, followed by `ι_⊤`, is the identity. -/
noncomputable def overMkIdIsoOpensTop (X : Scheme.{u}) :
    Over.mk (𝟙 X) ≅ Over.mk (Scheme.Opens.ι (⊤ : X.Opens)) :=
  Over.isoMk X.topIso.symm (Scheme.toIso_inv_ι X)

/-- **The monad `a_*a^*` of the identity morphism is the identity functor**, by `pullbackId` and
`pushforwardId`. -/
noncomputable def idMonadIso (X : Scheme.{u}) :
    pullback (𝟙 X) ⋙ pushforward (𝟙 X) ≅ 𝟭 X.Modules :=
  Functor.isoWhiskerRight (pullbackId X) (pushforward (𝟙 X)) ≪≫
    Functor.leftUnitor _ ≪≫ pushforwardId X

/-- **The monad `ι_{⊤,*}ι_⊤^*` of the inclusion of the top open is the identity functor.**  The
presheaf of monads `Stacks.AlgebraicGeometry.RelativeCech.relativeMonad` is a functor on `Over X`,
so it carries `overMkIdIsoOpensTop` to an isomorphism between the monad of `ι_⊤` and the monad of
the identity, and the latter is the identity functor. -/
noncomputable def topMonadIso (X : Scheme.{u}) :
    𝟭 X.Modules ≅
      pullback (Scheme.Opens.ι (⊤ : X.Opens)) ⋙ pushforward (Scheme.Opens.ι (⊤ : X.Opens)) :=
  ((relativeMonad X).mapIso (overMkIdIsoOpensTop X).op ≪≫ idMonadIso X).symm

/-- **The identification `f_*M ≅ (ι_⊤ ≫ f)_* ι_⊤^* M`**, natural in the `𝒪_X`-module `M`:  the
direct image along `f` is the value of the coefficient presheaf of [Stacks, Tag 01XL] at the
terminal object of `Over (⊤ : Opens X)`.

This is the comparison the Čech situation does not need:  there the terminal object of the
indexing category is `Over.mk (𝟙 X)` and the corresponding map is the identity. -/
noncomputable def topCoefficientIso (f : X ⟶ S) :
    pushforward f ≅ pushforwardPresheafAll f ⋙
      (evaluation (Over (⊤ : Opens X))ᵒᵖ S.Modules).obj (op (Over.mk (𝟙 (⊤ : Opens X)))) :=
  (Functor.leftUnitor (pushforward f)).symm ≪≫
    Functor.isoWhiskerRight (topMonadIso X) (pushforward f)

/-- The value of the coefficient presheaf at the terminal object of `Over (⊤ : Opens X)`, as a
functor of the module, is `ι_⊤^*` followed by the direct image along `ι_⊤ ≫ f`. -/
theorem pushforwardPresheafAll_comp_evaluation_top (f : X ⟶ S) :
    pushforwardPresheafAll f ⋙
        (evaluation (Over (⊤ : Opens X))ᵒᵖ S.Modules).obj (op (Over.mk (𝟙 (⊤ : Opens X)))) =
      pullback (Scheme.Opens.ι (⊤ : X.Opens)) ⋙
        pushforward (Scheme.Opens.ι (⊤ : X.Opens) ≫ f) :=
  rfl

/-- The components of `topCoefficientIso`:  the direct image along `f` of the unit of the monad of
`ι_⊤`. -/
theorem topCoefficientIso_hom_app (f : X ⟶ S) (M : X.Modules) :
    (topCoefficientIso f).hom.app M = (pushforward f).map ((topMonadIso X).hom.app M) :=
  Category.id_comp _

/-! ### The augmentation -/

variable (f : X ⟶ S) (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))

/-- **The augmentation of the relative hypercovering complex before the passage to integer
degrees**, as a natural transformation of functors of the coefficient presheaf's module:  the
generic terminal-object augmentation of a Čech-style complex, whiskered with the coefficient
presheaf of [Stacks, Tag 01XL]. -/
noncomputable def hypercoveringAugNat :
    pushforwardPresheafAll f ⋙
          (evaluation (Over (⊤ : Opens X))ᵒᵖ S.Modules).obj (op (Over.mk (𝟙 (⊤ : Opens X)))) ⋙
        HomologicalComplex.single S.Modules (ComplexShape.up ℕ) 0 ⟶
      pushforwardPresheafAll f ⋙ FormalCoproduct.cochainComplexFunctor K :=
  Functor.whiskerLeft (pushforwardPresheafAll f)
    (terminalAugNatTrans K (Over.mkIdTerminal (X := (⊤ : Opens X))))

/-- **The degree-zero component of the `ℕ`-indexed augmentation** is the product, over the index
type of `K₀`, of the restriction maps of the coefficient presheaf to the members of `K₀`. -/
theorem hypercoveringAugNat_app_f_zero (M : X.Modules) :
    ((hypercoveringAugNat f K).app M).f 0 =
      terminalAugZero K (Over.mkIdTerminal (X := (⊤ : Opens X)))
        ((pushforwardPresheafAll f).obj M) :=
  terminalAugNatTrans_f_zero K (Over.mkIdTerminal (X := (⊤ : Opens X)))
    ((pushforwardPresheafAll f).obj M)

/-- **The augmentation `ε : (f_*M)[0] ⟶ 𝓚⁼(K, f, M)` of the relative hypercovering complex**,
natural in the arbitrary `𝒪_X`-module `M`.

It is assembled from three pieces:  the identification `topCoefficientIso` of `f_*M` with the
value of the coefficient presheaf at the terminal object of `Over (⊤ : Opens X)`, the generic
augmentation `terminalAugNatTrans` of a Čech-style complex of formal coproducts at a terminal
object, and the identification of the extension by zero of a complex concentrated in degree zero
with the complex concentrated in degree zero over the integers. -/
noncomputable def hypercoveringAugAll :
    pushforward f ⋙ HomologicalComplex.single S.Modules (ComplexShape.up ℤ) 0 ⟶
      hypercoveringPushforwardComplexAll f K :=
  Functor.whiskerRight (topCoefficientIso f).hom
      (HomologicalComplex.single S.Modules (ComplexShape.up ℤ) 0) ≫
    (Functor.isoWhiskerLeft
      (pushforwardPresheafAll f ⋙
        (evaluation (Over (⊤ : Opens X))ᵒᵖ S.Modules).obj (op (Over.mk (𝟙 (⊤ : Opens X)))))
      (ComplexShape.Embedding.singleUpNatCompExtendFunctorIso S.Modules)).inv ≫
    Functor.whiskerRight (hypercoveringAugNat f K)
      (ComplexShape.embeddingUpNat.extendFunctor S.Modules)

/-- **The naturality of the augmentation**, in the form the hypothesis `hε` of
`StacksDraft.DerivedSectionsComparison` is stated in. -/
theorem hypercoveringAugAll_naturality {M N : X.Modules} (φ : M ⟶ N) :
    (HomologicalComplex.single S.Modules (ComplexShape.up ℤ) 0).map ((pushforward f).map φ) ≫
        (hypercoveringAugAll f K).app N =
      (hypercoveringAugAll f K).app M ≫ (hypercoveringPushforwardComplexAll f K).map φ :=
  (hypercoveringAugAll f K).naturality φ

/-! ### Reduction of the quasi-isomorphy of `ε` to the `ℕ`-indexed statement -/

/-- The augmentation at one module, unfolded:  the identification of `f_*M` with the coefficient
presheaf's value at the terminal object, then the identification of the extension of a complex
concentrated in degree zero with the complex concentrated in degree zero over the integers, then
the extension of the `ℕ`-indexed augmentation. -/
theorem hypercoveringAugAll_app_eq (M : X.Modules) :
    (hypercoveringAugAll f K).app M =
      (HomologicalComplex.single S.Modules (ComplexShape.up ℤ) 0).map
            ((topCoefficientIso f).hom.app M) ≫
          (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
            (((pushforwardPresheafAll f ⋙
              (evaluation (Over (⊤ : Opens X))ᵒᵖ S.Modules).obj
                (op (Over.mk (𝟙 (⊤ : Opens X))))).obj M)) 0 0 (by simp)).inv ≫
        HomologicalComplex.extendMap ((hypercoveringAugNat f K).app M)
          ComplexShape.embeddingUpNat :=
  rfl

/-- **The augmentation `ε` is a quasi-isomorphism at a module at which its `ℕ`-indexed form is.**
The two intervening identifications are isomorphisms:  `topCoefficientIso` because it is a
natural isomorphism, and the single-complex identification because extension along an embedding
of complex shapes neither creates nor destroys homology. -/
theorem quasiIso_hypercoveringAugAll_app (M : X.Modules)
    (h : QuasiIso ((hypercoveringAugNat f K).app M)) :
    QuasiIso ((hypercoveringAugAll f K).app M) := by
  have : IsIso ((topCoefficientIso f).hom.app M) := ((topCoefficientIso f).app M).isIso_hom
  rw [hypercoveringAugAll_app_eq]
  exact quasiIso_comp _ _ (hφ' := quasiIso_comp _ _
    (hφ' := (HomologicalComplex.quasiIso_extendMap_iff _ _).2 h))

/-- **The `ℕ`-indexed augmentation is a quasi-isomorphism at a module for which the augmented
complex of the coefficient presheaf is a resolution.**  The two hypotheses are the two halves of
the relative form of [Stacks, Tag 01GV]:  in degree zero the augmentation is a kernel of the first
differential, and in every other degree the complex is exact. -/
theorem quasiIso_hypercoveringAugNat_app (M : X.Modules)
    (hker : IsIso (kernel.lift
      (((FormalCoproduct.cochainComplexFunctor K).obj
        ((pushforwardPresheafAll f).obj M)).d 0 1)
      (terminalAugZero K (Over.mkIdTerminal (X := (⊤ : Opens X)))
        ((pushforwardPresheafAll f).obj M))
      (terminalAugZero_comp_d K (Over.mkIdTerminal (X := (⊤ : Opens X)))
        ((pushforwardPresheafAll f).obj M))))
    (hex : ∀ q : ℕ, q ≠ 0 →
      ((FormalCoproduct.cochainComplexFunctor K).obj
        ((pushforwardPresheafAll f).obj M)).ExactAt q) :
    QuasiIso ((hypercoveringAugNat f K).app M) :=
  CochainComplex.quasiIso_mkHomFromSingle_zero
    ((FormalCoproduct.cochainComplexFunctor K).obj ((pushforwardPresheafAll f).obj M))
    (terminalAugZero K (Over.mkIdTerminal (X := (⊤ : Opens X)))
      ((pushforwardPresheafAll f).obj M))
    (terminalAugZero_comp_d_rel K (Over.mkIdTerminal (X := (⊤ : Opens X)))
      ((pushforwardPresheafAll f).obj M))
    hker hex

end Stacks.AlgebraicGeometry.UniversalPushforward

end
