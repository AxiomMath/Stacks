module

public import StacksFrontier.AlgebraicTopology.ExtraDegeneracyLast
public import StacksFrontier.AlgebraicTopology.StandardResolution.Contraction
public import StacksFrontier.Cotangent.HomologyZero
public import StacksFrontier.Cotangent.StandardResolutionIsResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The cotangent complex of a polynomial algebra (Stacks 08QH)

If `B` is a polynomial algebra over `A`, then the cotangent complex `L_{B/A}` is quasi-isomorphic
to `Ω[B⁄A][0]`.

## Main definitions

* `CommAlgCat.cotangentSectionD`, `CommAlgCat.cotangentSection`: the generator `1 ⊗ d (θ b)` and
  the induced map `Ω[B⁄A] → Ω[P₀⁄A] ⊗[P₀] B`.
* `CommAlgCat.cotangentSimplicialModuleAugmented`: the cotangent simplicial module, augmented to
  `Ω[B⁄A]`.
* `CommAlgCat.cotangentExtraDegeneracyLast`: its contraction.

## Main results

* `CommAlgCat.exists_section_of_isPolynomialAlgebra`: for `B` a polynomial algebra, the counit
  `A[B] ⟶ B` of the polynomial-algebra comonad has an `A`-algebra section.
* `CommAlgCat.nonempty_standardResolutionExtraDegeneracyLast`: the standard resolution of a
  polynomial algebra is contractible.
* `CommAlgCat.cotangentComplex_iso_kaehlerDifferential`: **Stacks 08QH**.

## Implementation notes

The Stacks proof deduces 08QH from the identification `L_{B/A} = Lπ_!(Ω_{𝒪/A} ⊗ B)` of Lemma
08PU together with the exactness of `π_!` for a polynomial algebra (Lemma 08QG). The argument
here is carried out on the standard resolution directly instead, which is shorter, because for
`B` polynomial the standard resolution is *contractible*, not merely a resolution. (This note
previously said neither input was available. Both now are: 08QG at
`StacksFrontier/Cotangent/PolynomialAlgebraSiteShriek.lean`, and 08PU in `D(B)` at
`CommAlgCat.standardResolutionCotangentDerivedLowerShriekIso` of
`StacksFrontier/Cotangent/PolynomialAlgebraSiteModuleShriekDerived.lean`. The direct argument is
kept because it is shorter, not because the source's route is closed.)

Indeed `B = A[ι]` is a free object, so the counit `ε_B : A[B] ⟶ B` of the polynomial-algebra
comonad `G` admits an `A`-algebra section `θ`, sending a variable `X i` of `A[ι]` to the variable
`[X i]` of `A[B]`. The morphisms `s n = Gⁿ⁺¹ θ` then contract the standard resolution: `s n`
inserts a new *innermost* copy of `G`, and Godement's faces count copies of `G` from the outside,
so it is the *last* face which cancels `s n`. That is an `ExtraDegeneracyLast`, the mirror of
Mathlib's `ExtraDegeneracy`. Only the triangle identity `θ ≫ ε_B = 𝟙` and the naturality of `ε`
are used — no coassociativity, hence no coalgebra structure on `B` — so the contraction is taken
from `SimplicialObject.Augmented.ExtraDegeneracyLast.ofGodement`
(`StacksFrontier.AlgebraicTopology.StandardResolution.Contraction`), which is stated for an arbitrary
endofunctor `Y` with a transformation `d : Y ⟶ 𝟭` and a section of `d_B`.

Pushing the contraction through `P ↦ Ω[P⁄A] ⊗[P] B` is legitimate because the `s n` lie over `B`:
in an augmented simplicial object the augmentation factors through every face, and
`s n ≫ δ_last = 𝟙`, so `s n ≫ ε_{n+1} = ε_n` automatically. The resulting
`ExtraDegeneracyLast` on the augmented cotangent simplicial module is checked on the generators
`1 ⊗ d p`, where each axiom reduces to the corresponding identity of algebra morphisms.

Crossing from the Moore complex to the cotangent complex is then API:
`HomologicalComplex.quasiIso_extendMap_iff` transports the quasi-isomorphism along
`ComplexShape.embeddingUpIntLE 0`, and `HomologicalComplex.extendSingleIso` identifies the
extension of `Ω[B⁄A]` placed in degree `0` with the cochain complex `Ω[B⁄A][0]`.

## References

* [Stacks Project, Tag 08QH](https://stacks.math.columbia.edu/tag/08QH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology
open scoped TensorProduct ChangeOfRings

universe u v w

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-! ### The standard resolution of a polynomial algebra is contractible -/

/-- The augmentation of the standard resolution in degree zero is the counit of the
polynomial-algebra comonad. -/
public theorem standardResolution_augmentation_eq_counit :
    (standardResolution A B).hom.app (op ⦋0⦌) =
      eqToHom (standardResolution_obj A B 0) ≫ (polynomialComonad.{u, v} A).ε.app B :=
  standardResolution_augmentation A B

/-- If `B` is a polynomial algebra over `A`, the counit `A[B] ⟶ B` of the polynomial-algebra
comonad admits a section in `CommAlgCat A`: writing `B = A[ι]`, the section sends the variable
`X i` of `B` to the variable `[X i]` of `A[B]`. -/
public theorem exists_section_of_isPolynomialAlgebra (hB : Algebra.IsPolynomialAlgebra A B) :
    ∃ θ : B ⟶ (polynomialComonad.{u, v} A).toFunctor.obj B,
      θ ≫ (polynomialComonad.{u, v} A).ε.app B = 𝟙 B := by
  obtain ⟨ι, ⟨e⟩⟩ := hB
  let w : ι → MvPolynomial B A := fun i => MvPolynomial.X (e (MvPolynomial.X i))
  let g : B →ₐ[A] MvPolynomial B A := (MvPolynomial.aeval w).comp e.symm.toAlgHom
  have h2 : ((MvPolynomial.aeval (id : B → B)).comp g).comp e.toAlgHom = e.toAlgHom := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp [g, w]
  refine ⟨CommAlgCat.ofHom g, CommAlgCat.hom_ext (AlgHom.ext fun b => ?_)⟩
  obtain ⟨p, rfl⟩ := e.surjective b
  exact AlgHom.congr_fun h2 p

/-- **The standard resolution of a polynomial algebra is contractible.** Writing `B = A[ι]`, the
section `θ` of the counit given by `exists_section_of_isPolynomialAlgebra` contracts the standard
resolution through the morphisms `Gⁿ⁺¹ θ`, which are cancelled by the last face. -/
public theorem nonempty_standardResolutionExtraDegeneracyLast
    (hB : Algebra.IsPolynomialAlgebra A B) :
    Nonempty (SimplicialObject.Augmented.ExtraDegeneracyLast (standardResolution A B)) := by
  obtain ⟨θ, hθ⟩ := exists_section_of_isPolynomialAlgebra A B hB
  exact ⟨SimplicialObject.Augmented.ExtraDegeneracyLast.ofGodement
    (polynomialComonad.{u, v} A).ε θ hθ _ (standardResolution_obj A B) rfl
    (standardResolution_face A B)
    (by simpa using standardResolution_augmentation_eq_counit A B)⟩

/-! ### The section of the augmentation in degree zero -/

section Section

variable (θ : B ⟶ (standardResolution A B).left.obj (op ⦋0⦌))

/-- The generator `1 ⊗ d (θ b)` of the base-changed differentials in degree zero, attached to a
morphism `θ : B ⟶ P₀`. -/
public noncomputable def cotangentSectionD (b : B) : cotangentTerm A B (op ⦋0⦌) :=
  cotangentTermDifferential A B (op ⦋0⦌) (θ b)

/-- `b ↦ 1 ⊗ d (θ b)` is additive. -/
public theorem cotangentSectionD_add (b c : B) :
    cotangentSectionD A B θ (b + c) = cotangentSectionD A B θ b + cotangentSectionD A B θ c := by
  rw [cotangentSectionD, map_add, cotangentTermDifferential_add]
  rfl

/-- `b ↦ 1 ⊗ d (θ b)` kills the image of `A`. -/
public theorem cotangentSectionD_algebraMap (a : A) :
    cotangentSectionD A B θ (algebraMap A B a) = 0 := by
  rw [cotangentSectionD,
    show θ (algebraMap A B a) =
      algebraMap A ((standardResolution A B).left.obj (op ⦋0⦌)) a from θ.hom.commutes a,
    cotangentTermDifferential_algebraMap]

variable (hθ : θ ≫ (standardResolution A B).hom.app (op ⦋0⦌) = 𝟙 B)

include hθ

/-- A section of the augmentation of the standard resolution, read on elements. -/
public theorem standardResolutionAugmentationHom_section (b : B) :
    standardResolutionAugmentationHom A B (op ⦋0⦌) (θ b) = b := by
  simpa [standardResolutionAugmentationHom] using congrArg (fun k : B ⟶ B => k b) hθ

/-- `b ↦ 1 ⊗ d (θ b)` satisfies the Leibniz rule: `θ` is a section of the augmentation, so the
Leibniz coefficients are `b` and `c` themselves. -/
public theorem cotangentSectionD_mul (b c : B) :
    cotangentSectionD A B θ (b * c) =
      b • cotangentSectionD A B θ c + c • cotangentSectionD A B θ b := by
  rw [cotangentSectionD, map_mul, cotangentTermDifferential_mul,
    standardResolutionAugmentationHom_section A B θ hθ,
    standardResolutionAugmentationHom_section A B θ hθ]
  rfl

/-- The relations defining `Ω[B⁄A]` as a quotient of the free module on `B` are satisfied by
`b ↦ 1 ⊗ d (θ b)`. -/
public theorem kerTotal_le_ker_cotangentSectionD :
    KaehlerDifferential.kerTotal A B ≤
      LinearMap.ker (Finsupp.linearCombination B (cotangentSectionD A B θ)) := by
  rw [KaehlerDifferential.kerTotal, Submodule.span_le]
  rintro _ ((⟨⟨x, y⟩, rfl⟩ | ⟨⟨x, y⟩, rfl⟩) | ⟨a, rfl⟩) <;>
    simp [LinearMap.mem_ker, cotangentSectionD_add A B θ, cotangentSectionD_mul A B θ hθ,
      cotangentSectionD_algebraMap A B θ, add_comm]

/-- The `B`-linear map `Ω[B⁄A] → B ⊗[P₀] Ω[P₀⁄A]` induced by the derivation `b ↦ 1 ⊗ d (θ b)`,
for `θ` a section of the augmentation in degree zero. -/
public noncomputable def cotangentSection :
    ModuleCat.of B (KaehlerDifferential A B) ⟶ cotangentTerm A B (op ⦋0⦌) :=
  ModuleCat.ofHom (X := ModuleCat.of B (KaehlerDifferential A B))
      (Y := cotangentTerm A B (op ⦋0⦌))
    ((show ((B →₀ B) ⧸ KaehlerDifferential.kerTotal A B) →ₗ[B] cotangentTerm A B (op ⦋0⦌) from
        (KaehlerDifferential.kerTotal A B).liftQ
          (Finsupp.linearCombination B (cotangentSectionD A B θ))
          (kerTotal_le_ker_cotangentSectionD A B θ hθ)).comp
      (KaehlerDifferential.quotKerTotalEquiv A B).symm.toLinearMap)

/-- The section sends `d b` to the generator `1 ⊗ d (θ b)`. -/
@[simp]
public theorem cotangentSection_D (b : B) :
    cotangentSection A B θ hθ (KaehlerDifferential.D A B b) = cotangentSectionD A B θ b := by
  have h : (KaehlerDifferential.quotKerTotalEquiv A B).symm (KaehlerDifferential.D A B b) =
      (KaehlerDifferential.kerTotal A B).mkQ (Finsupp.single b 1) :=
    Derivation.congr_fun (KaehlerDifferential.quotKerTotalEquiv_symm_comp_D A B) b
  show (show ((B →₀ B) ⧸ KaehlerDifferential.kerTotal A B) →ₗ[B] cotangentTerm A B (op ⦋0⦌) from
      (KaehlerDifferential.kerTotal A B).liftQ
        (Finsupp.linearCombination B (cotangentSectionD A B θ))
        (kerTotal_le_ker_cotangentSectionD A B θ hθ))
    ((KaehlerDifferential.quotKerTotalEquiv A B).symm (KaehlerDifferential.D A B b)) = _
  rw [h, Submodule.mkQ_apply, Submodule.liftQ_apply, Finsupp.linearCombination_single,
    one_smul]

/-- The section is a section: composed with the augmentation to `Ω[B⁄A]` it is the identity. -/
public theorem cotangentSection_comp_cotangentTermAug :
    cotangentSection A B θ hθ ≫ cotangentTermAug A B (op ⦋0⦌) =
      𝟙 (ModuleCat.of B (KaehlerDifferential A B)) := by
  refine ModuleCat.hom_ext (LinearMap.ext_on
    (KaehlerDifferential.span_range_derivation A B) ?_)
  rintro _ ⟨b, rfl⟩
  rw [ModuleCat.comp_apply, cotangentSection_D, cotangentSectionD, cotangentTermAug_D,
    ModuleCat.id_apply]
  exact congrArg (KaehlerDifferential.D A B) (standardResolutionAugmentationHom_section A B θ hθ b)

end Section

/-! ### The augmented cotangent simplicial module and its contraction -/

/-- The cotangent simplicial module, augmented to the Kähler differentials of `B` over `A`. -/
public noncomputable def cotangentSimplicialModuleAugmented :
    SimplicialObject.Augmented (ModuleCat.{max u v} B) where
  left := (cotangentSimplicialModule A B).object
  right := ModuleCat.of B (KaehlerDifferential A B)
  hom :=
    { app := cotangentTermAug A B
      naturality := fun _ _ f =>
        (cotangentMap_comp_cotangentTermAug A B f).trans (Category.comp_id _).symm }

/-- **The cotangent simplicial module of a contractible standard resolution is contractible.** An
extra degeneracy at the last face of the standard resolution is pushed through
`P ↦ Ω[P⁄A] ⊗[P] B`: the morphisms of the contraction lie over `B`, because `s n ≫ δ_last = 𝟙`
and the augmentation factors through every face. -/
public noncomputable def cotangentExtraDegeneracyLast
    (ed : SimplicialObject.Augmented.ExtraDegeneracyLast (standardResolution A B)) :
    SimplicialObject.Augmented.ExtraDegeneracyLast (cotangentSimplicialModuleAugmented A B) := by
  have hnat : ∀ (n : ℕ) (k : Fin (n + 2)),
      (standardResolution A B).left.δ k ≫ (standardResolution A B).hom.app (op ⦋n⦌) =
        (standardResolution A B).hom.app (op ⦋n + 1⦌) := fun n k =>
    (standardResolution A B).hom.naturality (SimplexCategory.δ k).op
  have hover : ∀ n : ℕ,
      (standardResolutionAugmentationHom A B (op ⦋n + 1⦌)).comp (ed.s n).hom.toRingHom =
      standardResolutionAugmentationHom A B (op ⦋n⦌) := by
    intro n
    refine standardResolutionAugmentationHom_comp_of_over A B (ed.s n) ?_
    rw [← hnat n (Fin.last (n + 1)), ← Category.assoc, ed.s_comp_δ_last n, Category.id_comp]
  have h₀ : cotangentPush A B (ed.s 0) (hover 0) ≫
      cotangentMap A B (SimplexCategory.δ (0 : Fin 2)).op =
      cotangentTermAug A B (op ⦋0⦌) ≫ cotangentSection A B ed.s' ed.s'_comp_ε := by
    refine cotangentTerm_hom_ext A B _ _ _ fun p => ?_
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, cotangentPush_D, cotangentMap_D,
      cotangentTermAug_D, cotangentSection_D, cotangentSectionD]
    exact congrArg (cotangentTermDifferential A B (op ⦋0⦌))
      (congrArg (fun k : (standardResolution A B).left.obj (op ⦋0⦌) ⟶
        (standardResolution A B).left.obj (op ⦋0⦌) => k p) ed.s₀_comp_δ₀)
  have hlast : ∀ n : ℕ, cotangentPush A B (ed.s n) (hover n) ≫
      cotangentMap A B (SimplexCategory.δ (Fin.last (n + 1))).op =
      𝟙 (cotangentTerm A B (op ⦋n⦌)) := by
    intro n
    refine cotangentTerm_hom_ext A B _ _ _ fun p => ?_
    rw [ModuleCat.comp_apply, cotangentPush_D, cotangentMap_D, ModuleCat.id_apply]
    exact congrArg (cotangentTermDifferential A B (op ⦋n⦌))
      (congrArg (fun k : (standardResolution A B).left.obj (op ⦋n⦌) ⟶
        (standardResolution A B).left.obj (op ⦋n⦌) => k p) (ed.s_comp_δ_last n))
  have hface : ∀ (n : ℕ) (i : Fin (n + 2)), cotangentPush A B (ed.s (n + 1)) (hover (n + 1)) ≫
      cotangentMap A B (SimplexCategory.δ i.castSucc).op =
      cotangentMap A B (SimplexCategory.δ i).op ≫ cotangentPush A B (ed.s n) (hover n) := by
    intro n i
    refine cotangentTerm_hom_ext A B _ _ _ fun p => ?_
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, cotangentPush_D, cotangentMap_D,
      cotangentMap_D, cotangentPush_D]
    exact congrArg (cotangentTermDifferential A B (op ⦋n + 1⦌))
      (congrArg (fun k : (standardResolution A B).left.obj (op ⦋n + 1⦌) ⟶
        (standardResolution A B).left.obj (op ⦋n + 1⦌) => k p) (ed.s_comp_δ n i))
  exact
    { s' := cotangentSection A B ed.s' ed.s'_comp_ε
      s := fun n => cotangentPush A B (ed.s n) (hover n)
      s'_comp_ε := cotangentSection_comp_cotangentTermAug A B ed.s' ed.s'_comp_ε
      s₀_comp_δ₀ := h₀
      s_comp_δ_last := hlast
      s_comp_δ := hface }

/-! ### The theorem -/

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks Project, Tag 08QH.** If `B` is a polynomial algebra over the ring `A`, then the
cotangent complex `L_{B/A}` is quasi-isomorphic to `Ω[B⁄A][0]`. -/
@[stacks 08QH]
public theorem cotangentComplex_iso_kaehlerDifferential (hB : Algebra.IsPolynomialAlgebra A B) :
    Nonempty
      (DerivedCategory.Q.obj (cotangentComplex A B) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).obj
          (ModuleCat.of B (KaehlerDifferential A B))) := by
  obtain ⟨ed⟩ := nonempty_standardResolutionExtraDegeneracyLast A B hB
  have he := (cotangentExtraDegeneracyLast A B ed).homotopyEquiv
  have hiso := (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u v} B)
    (HomologicalComplex.extendMap he.hom (ComplexShape.embeddingUpIntLE (0 : ℤ)))).2 inferInstance
  exact ⟨(@asIso _ _ _ _ (DerivedCategory.Q.map (HomologicalComplex.extendMap he.hom
      (ComplexShape.embeddingUpIntLE (0 : ℤ)))) hiso) ≪≫
    DerivedCategory.Q.mapIso (HomologicalComplex.extendSingleIso
      (ComplexShape.embeddingUpIntLE (0 : ℤ))
      (ModuleCat.of B (KaehlerDifferential A B)) 0 0 (by simp))⟩

end CommAlgCat

end
