module

public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CohomologySpectralSequenceTagComponent

/-!
# The total complex of the sections double complex computes cohomology on the total site

Let `S` be a simplicial-site situation (Stacks 09WE) and let `Z^•` be a cochain complex of
abelian sheaves on its total site with injective terms, vanishing in negative degrees. The
double complex

```
A^{q,p} = Γ(C_p, Z^q_p)
```

of `StacksFrontier/CategoryTheory/Sites/Simplicial/CohomologySpectralSequence.lean` has, by
Stacks 0D77, exact columns away from simplicial degree `0`, and in simplicial degree `0` the
augmentation `Γ(C_total, Z^q) → Γ(C_0, Z^q_0)` is a kernel of the first differential. These are
exactly the hypotheses of Stacks 0133, so the induced comparison

```
Γ(C_total, Z^•) ⟶ Tot(A^{•,•})
```

is a quasi-isomorphism, and `H^n(Tot(A^{•,•})) ≅ H^n(Γ(C_total, Z^•))`. Taking `Z^•` to be the
chosen injective resolution of an abelian sheaf `F` on the total site, extended by zero to
integer degrees, the right-hand side is the sheaf cohomology `H^n(C_total, F)`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.totalSectionsComplex`: the complex
  `Γ(C_total, Z^•)`.
* `CategoryTheory.SimplicialSiteSituation.sectionsAlphaNat`: the augmentation
  `Γ(C_total, Z^•) ⟶ A^{•,0}` into the zeroth row of the double complex, as a natural
  transformation in `Z^•`: `cechSectionsAugmentation` applied degreewise.
* `CategoryTheory.SimplicialSiteSituation.sectionsComparisonMap`: the comparison map of
  Stacks 0133, `Γ(C_total, Z^•) ⟶ Tot(A^{•,•})`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.sectionsHypotheses`: the four hypotheses of
  Stacks 0133 for the double complex `A^{q,p} = Γ(C_p, Z^q_p)` of a complex of injective abelian
  sheaves vanishing in negative degrees. Three of them are the vanishing and exactness clauses
  of Stacks 0D77; the fourth is its clauses in degrees `-1` and `0`.
* `CategoryTheory.SimplicialSiteSituation.sectionsComparisonHomologyIso`:
  **`H^n(Γ(C_total, Z^•)) ≅ H^n(Tot(A^{•,•}))`**, and
  `CategoryTheory.SimplicialSiteSituation.sectionsComparisonMap_naturality` for its naturality in
  `Z^•`.
* `CategoryTheory.SimplicialSiteSituation.totalCohomologyIsoTotalComplexHomology`:
  **`H^n(C_total, F) ≅ H^n(Tot(A^{•,•}))`** for the chosen injective resolution of an abelian sheaf
  `F` on the total site.

## Implementation notes

The comparison of Stacks 0133 is taken in its data form, `comparisonMapP`, which is natural in
`Z^•`, rather than through the existential `quasiIso_total_of_resolution`.

## References

* [Stacks Project, Tag 09WJ](https://stacks.math.columbia.edu/tag/09WJ)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D77](https://stacks.math.columbia.edu/tag/0D77)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe v u

/-! ### A monomorphism with exact short complex is a kernel -/

/-- **A monomorphism whose short complex is exact is a kernel of the next map**: in an abelian
category, if `f` is a monomorphism, `f ≫ g = 0` and `T ⟶ A ⟶ B` is exact, then the lift of `f` to
the kernel of `g` is an isomorphism. -/
theorem CategoryTheory.isIso_kernelLift_of_mono_of_exact {C : Type u} [Category.{v} C] [Abelian C]
    {T A B : C} (f : T ⟶ A) (g : A ⟶ B) (hf : f ≫ g = 0) [Mono f]
    (hex : (ShortComplex.mk f g hf).Exact) :
    IsIso (kernel.lift g f hf) :=
  have : Mono (kernel.lift g f hf) := mono_of_mono_fac (kernel.lift_ι g f hf)
  have : Epi (kernel.lift g f hf) :=
    (ShortComplex.mk f g hf).exact_iff_epi_kernel_lift.1 hex
  isIso_of_mono_of_epi _

/-- **The kernel clause for an augmentation, transported to the extension by zero.** If a
monomorphism `ξ : T ⟶ K⁰` into a complex indexed by `ℕ` makes `T ⟶ K⁰ ⟶ K¹` exact, then its
composite `ζ` with the identification of the degree-zero terms is a kernel of the first
differential of the extension of `K` by zero to `ℤ`. -/
theorem CategoryTheory.inducesIsoKernel_extendAugmentation {C : Type u} [Category.{v} C]
    [Abelian C] (K : CochainComplex C ℕ) {T : C} (ξ : T ⟶ K.X 0) (hξ : ξ ≫ K.d 0 1 = 0)
    (hmono : Mono ξ) (hex : (ShortComplex.mk ξ (K.d 0 1) hξ).Exact)
    (h₀ : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))
    (h₁ : ComplexShape.embeddingUpNat.f 1 = (1 : ℤ))
    (ζ : T ⟶ (K.extend ComplexShape.embeddingUpNat).X 0)
    (hζ : ζ = ξ ≫ (K.extendXIso ComplexShape.embeddingUpNat h₀).inv) :
    ∃ hα : ζ ≫ (K.extend ComplexShape.embeddingUpNat).d 0 1 = 0,
      IsIso (kernel.lift ((K.extend ComplexShape.embeddingUpNat).d 0 1) ζ hα) := by
  have hd : (K.extend ComplexShape.embeddingUpNat).d 0 1 =
      (K.extendXIso ComplexShape.embeddingUpNat h₀).hom ≫ K.d 0 1 ≫
        (K.extendXIso ComplexShape.embeddingUpNat h₁).inv :=
    K.extend_d_eq ComplexShape.embeddingUpNat h₀ h₁
  have hα : ζ ≫ (K.extend ComplexShape.embeddingUpNat).d 0 1 = 0 := by
    simp [hζ, hd, reassoc_of% hξ]
  refine ⟨hα, ?_⟩
  have : Mono ζ := by rw [hζ]; infer_instance
  have e : ShortComplex.mk ξ (K.d 0 1) hξ ≅
      ShortComplex.mk ζ ((K.extend ComplexShape.embeddingUpNat).d 0 1) hα :=
    ShortComplex.isoMk (Iso.refl _)
      (K.extendXIso ComplexShape.embeddingUpNat h₀).symm
      (K.extendXIso ComplexShape.embeddingUpNat h₁).symm (by simp [hζ]) (by simp [hd])
  exact isIso_kernelLift_of_mono_of_exact _ _ _ (ShortComplex.exact_of_iso e hex)

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-! ### The zeroth row of the double complex, and the augmentation into it -/

/-- Evaluating the complex of Stacks 0D77, extended by zero, in simplicial degree `0` gives
`Γ(C_0, (-)_0)`. This is `cechSectionsComplexZCompEval` at `n = 0`, with the integer index
written as the literal `0` that `rowZero` uses. -/
def cechSectionsComplexZCompEvalZero :
    S.cechSectionsComplexZ ⋙
        HomologicalComplex.eval Ab.{u} (ComplexShape.up ℤ) (0 : ℤ) ≅
      S.componentSectionsFunctor ⦋0⦌ :=
  Functor.isoWhiskerLeft (S.cechSectionsComplex)
    (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso Ab.{u} (i := 0) (i' := (0 : ℤ)) rfl)

/-- **The zeroth row `A^{•,0}` of the double complex is `Γ(C_0, Z^•_0)`.** -/
def sectionsRowZeroIso (Z : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) :
    rowZero (S.sectionsDoubleComplex Z) ≅
      ((S.componentSectionsFunctor ⦋0⦌).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z :=
  (NatIso.mapHomologicalComplex (S.cechSectionsComplexZCompEvalZero)
    (ComplexShape.up ℤ)).app Z

/-- The complex of global sections `Γ(C_total, Z^•)` of a complex of abelian sheaves on the total
site. -/
abbrev totalSectionsComplex (Z : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) :
    CochainComplex Ab.{u} ℤ :=
  ((Sheaf.Γ S.totalTopology Ab.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z

/-- **The augmentation `Γ(C_total, Z^•) ⟶ A^{•,0}` of Stacks 0D77, degreewise in a complex**, as
a natural transformation: in degree `q` it is the augmentation of Stacks 0D77 at the sheaf `Z^q`,
followed by the identification of the zeroth row. -/
def sectionsAlphaNat :
    (Sheaf.Γ S.totalTopology Ab.{u}).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      S.sectionsDoubleComplexFunctor ⋙ rowZeroFunctor Ab.{u} :=
  NatTrans.mapHomologicalComplex (S.cechSectionsAugmentation) (ComplexShape.up ℤ) ≫
    (NatIso.mapHomologicalComplex (S.cechSectionsComplexZCompEvalZero)
      (ComplexShape.up ℤ)).inv

/-- **The augmentation into the zeroth row**, at a complex of abelian sheaves. -/
abbrev sectionsAlpha (Z : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) :
    S.totalSectionsComplex Z ⟶ rowZero (S.sectionsDoubleComplex Z) :=
  (S.sectionsAlphaNat).app Z

/-- The components of the augmentation: in degree `q` it is the augmentation of Stacks 0D77 at
the sheaf `Z^q`, followed by the inverse of the identification of the extended term. -/
theorem sectionsAlpha_f (Z : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) (q : ℤ)
    (h₀ : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ)) :
    (S.sectionsAlpha Z).f q =
      (S.cechSectionsAugmentation).app (Z.X q) ≫
        (HomologicalComplex.extendXIso ((S.cechSectionsComplex).obj (Z.X q))
          ComplexShape.embeddingUpNat h₀).inv :=
  rfl

/-- **The augmentation is natural in the complex of abelian sheaves.** -/
theorem sectionsAlpha_naturality {Z W : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ}
    (φ : Z ⟶ W) :
    S.sectionsAlpha Z ≫
        rowZeroMap ((S.sectionsDoubleComplexFunctor).map φ) =
      ((Sheaf.Γ S.totalTopology Ab.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).map φ ≫
        S.sectionsAlpha W :=
  ((S.sectionsAlphaNat).naturality φ).symm

/-! ### The hypotheses of Stacks 0133 -/

variable (Z : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ)

/-- **The antidiagonals of the double complex are finite**, for a complex of abelian sheaves
vanishing in negative degrees: a nonzero term has both coordinates between `0` and `n`. -/
theorem diagonalFinite_sections (hZ : ∀ q : ℤ, q < 0 → IsZero (Z.X q)) :
    DiagonalFinite (S.sectionsDoubleComplex Z) := by
  intro n
  refine Set.Finite.subset (Set.finite_Icc (0 : ℤ) n) fun q hq => ?_
  simp only [Set.mem_ofPred_eq] at hq
  by_contra h
  simp only [Set.mem_Icc] at h
  exact hq (S.isZero_sectionsDoubleComplex_X_X Z hZ q (n - q) (by omega))

/-- **The columns of the double complex are exact away from simplicial degree `0`**, for a complex
of injective abelian sheaves. -/
theorem exactAt_sectionsDoubleComplex_X (hinj : ∀ q : ℤ, Injective (Z.X q)) (q p : ℤ)
    (hp : p ≠ 0) : ((S.sectionsDoubleComplex Z).X q).ExactAt p := by
  rcases lt_trichotomy p 0 with h | h | h
  · exact HomologicalComplex.extend_exactAt _ ComplexShape.embeddingUpNat p
      fun j => by change ((j : ℕ) : ℤ) ≠ p; omega
  · exact absurd h hp
  · have hk : ComplexShape.embeddingUpNat.f p.toNat = p := by
      change ((p.toNat : ℕ) : ℤ) = p; omega
    refine (HomologicalComplex.extend_exactAt_iff _ ComplexShape.embeddingUpNat hk).2 ?_
    have := hinj q
    exact S.cechSectionsComplex_exactAt_of_injective (Z.X q) p.toNat (by omega)

/-- **The augmentation is a kernel of the first differential in every degree.** -/
theorem inducesIsoKernel_sectionsAlpha (q : ℤ) :
    ∃ hα : (S.sectionsAlpha Z).f q ≫
        ((S.sectionsDoubleComplex Z).X q).d 0 1 = 0,
      IsIso (kernel.lift (((S.sectionsDoubleComplex Z).X q).d 0 1)
        ((S.sectionsAlpha Z).f q) hα) :=
  inducesIsoKernel_extendAugmentation
    ((S.cechSectionsComplex).obj (Z.X q))
    ((S.cechSectionsAugmentation).app (Z.X q))
    (S.cechSectionsAugmentation_comp_d (Z.X q))
    (S.cechSectionsAugmentation_app_mono (Z.X q))
    (S.cechSectionsComplex_shortComplexZero_exact (Z.X q)) rfl rfl
    ((S.sectionsAlpha Z).f q) rfl

/-- **The hypotheses of Stacks 0133 for the double complex `A^{q,p} = Γ(C_p, Z^q_p)`** of a complex
`Z^•` of injective abelian sheaves on the total site vanishing in negative degrees. -/
theorem sectionsHypotheses (hZ : ∀ q : ℤ, q < 0 → IsZero (Z.X q))
    (hinj : ∀ q : ℤ, Injective (Z.X q)) :
    Hypotheses (S.totalSectionsComplex Z) (S.sectionsDoubleComplex Z)
      (S.sectionsAlpha Z) where
  diagonalFinite := S.diagonalFinite_sections Z hZ
  zero_of_neg q p hp := S.isZero_sectionsDoubleComplex_X_X_of_neg_snd Z q p hp
  exactAt_of_ne_zero := S.exactAt_sectionsDoubleComplex_X Z hinj
  inducesIsoKernel := S.inducesIsoKernel_sectionsAlpha Z

/-! ### The comparison with the total complex -/

variable (hZ : ∀ q : ℤ, q < 0 → IsZero (Z.X q)) (hinj : ∀ q : ℤ, Injective (Z.X q))

/-- **The comparison map of Stacks 0133** for the double complex `A^{q,p} = Γ(C_p, Z^q_p)`:
`Γ(C_total, Z^•) ⟶ Tot(A^{•,•})`, in degree `n` the augmentation of Stacks 0D77 followed by the
inclusion of the summand `A^{n,0}`. -/
def sectionsComparisonMap :
    S.totalSectionsComplex Z ⟶ (S.sectionsDoubleComplex Z).total (ComplexShape.up ℤ) :=
  comparisonMapP _ _ _ (S.sectionsHypotheses Z hZ hinj)

/-- The comparison map of Stacks 0133 is a quasi-isomorphism. -/
instance quasiIso_sectionsComparisonMap :
    QuasiIso (S.sectionsComparisonMap Z hZ hinj) :=
  quasiIso_comparisonMapP _ _ _ _

/-- **`H^n(Γ(C_total, Z^•)) ≅ H^n(Tot(A^{•,•}))`.** This is Stacks 0133 for the double complex
`A^{q,p} = Γ(C_p, Z^q_p)` of a complex of injective abelian sheaves vanishing in negative
degrees. -/
def sectionsComparisonHomologyIso (n : ℤ) :
    (S.totalSectionsComplex Z).homology n ≅
      ((S.sectionsDoubleComplex Z).total (ComplexShape.up ℤ)).homology n :=
  comparisonHomologyIso _ _ _ (S.sectionsHypotheses Z hZ hinj) n

/-- **The comparison map of Stacks 0133 is natural in the complex of abelian sheaves.** -/
theorem sectionsComparisonMap_naturality {W : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ}
    (hW : ∀ q : ℤ, q < 0 → IsZero (W.X q)) (hWinj : ∀ q : ℤ, Injective (W.X q)) (φ : Z ⟶ W) :
    S.sectionsComparisonMap Z hZ hinj ≫
        HomologicalComplex₂.total.map ((S.sectionsDoubleComplexFunctor).map φ)
          (ComplexShape.up ℤ) =
      ((Sheaf.Γ S.totalTopology Ab.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).map φ ≫
        S.sectionsComparisonMap W hW hWinj :=
  comparisonMapP_naturality _ _ _ (S.sectionsHypotheses Z hZ hinj)
    (S.sectionsHypotheses W hW hWinj) _ _ (S.sectionsAlpha_naturality φ)

/-! ### The cohomology of the total site -/

section Sheaf

variable (F : Sheaf S.totalTopology Ab.{u})

/-- The chosen injective resolution of an abelian sheaf on the total site, extended by zero from
`ℕ` to `ℤ`. This is the complex `I^•` of the proof of Stacks 09WJ. -/
abbrev injectiveResolutionZ : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ :=
  (ComplexShape.embeddingUpNat.extendFunctor (Sheaf S.totalTopology Ab.{u})).obj
    (injectiveResolution F).cocomplex

/-- The extended chosen injective resolution vanishes in negative degrees. -/
theorem isZero_injectiveResolutionZ_X (q : ℤ) (hq : q < 0) :
    IsZero ((S.injectiveResolutionZ F).X q) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat q
    fun i => by change ((i : ℕ) : ℤ) ≠ q; omega

/-- **Every term of the extended chosen injective resolution is injective**: in the degrees
coming from `ℕ` it is a term of the resolution, and elsewhere it is a zero object. -/
theorem injective_injectiveResolutionZ_X (q : ℤ) : Injective ((S.injectiveResolutionZ F).X q) := by
  rcases hq : ComplexShape.embeddingUpNat.r q with _ | j
  · exact (HomologicalComplex.isZero_extend_X' _ ComplexShape.embeddingUpNat q hq).injective
  · exact Injective.of_iso
      (HomologicalComplex.extendXIso (injectiveResolution F).cocomplex
        ComplexShape.embeddingUpNat
        (ComplexShape.Embedding.f_eq_of_r_eq_some _ hq)).symm
      ((injectiveResolution F).injective j)

/-- **`H^n(Γ(C_total, I^•)) ≅ H^n(C_total, F)`** for the chosen injective resolution `I^•` of an
abelian sheaf `F` on the total site, extended by zero to `ℤ`. -/
def totalSectionsResolutionRightDerivedIso (n : ℕ) :
    (S.totalSectionsComplex (S.injectiveResolutionZ F)).homology (n : ℤ) ≅
      ((Sheaf.Γ S.totalTopology Ab.{u}).rightDerived n).obj F :=
  (HomologicalComplex.homologyFunctor Ab.{u} (ComplexShape.up ℤ) (n : ℤ)).mapIso
      ((Sheaf.Γ S.totalTopology Ab.{u}).mapExtendIso (injectiveResolution F).cocomplex
        ComplexShape.embeddingUpNat) ≪≫
    HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl) ≪≫
    ((injectiveResolution F).isoRightDerivedObj (Sheaf.Γ S.totalTopology Ab.{u}) n).symm

/-- **`H^n(C_total, F) ≅ H^n(Tot(A^{•,•}))`**, for the double complex `A^{q,p} = Γ(C_p, I^q_p)` of
the chosen injective resolution of an abelian sheaf `F` on the total site. -/
def totalCohomologyIsoTotalComplexHomology (n : ℕ) :
    ((Sheaf.Γ S.totalTopology Ab.{u}).rightDerived n).obj F ≅
      ((S.sectionsDoubleComplex (S.injectiveResolutionZ F)).total
        (ComplexShape.up ℤ)).homology (n : ℤ) :=
  (S.totalSectionsResolutionRightDerivedIso F n).symm ≪≫
    S.sectionsComparisonHomologyIso (S.injectiveResolutionZ F)
      (S.isZero_injectiveResolutionZ_X F) (S.injective_injectiveResolutionZ_X F) (n : ℤ)

end Sheaf

end CategoryTheory.SimplicialSiteSituation

end
