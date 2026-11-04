module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.ComparisonToDerivedSections

/-!
# The total Čech augmentation of a complex with vanishing higher Čech cohomology

Let `(X, O)` be a ringed space, let `U` be an open subset and let `Ui` be a family of opens with
`U = ⨆ i, Ui i`.  For a bounded-below complex `J` of sheaves of `O`-modules the Čech bicomplex
of `J` has `(q, p)` term the Čech `p`-cochains of `J^q`, and the Čech augmentation in each
resolution degree assembles into

`Γ(U, J•) ⟶ Tot(Č•(Ui, J•))`.

`Stacks.Cohomology.CechDerived.cechAlpha` already provides this map, and its
quasi-isomorphy, when every term of `J` is an injective sheaf of modules.  Injectivity is used
for exactly one thing: the higher Čech cohomology of each `J^q` vanishes.  This file replaces
the injectivity hypothesis by that vanishing, which is what the proof of [Stacks, Tag 01FD]
needs: there the relevant complexes are an injective resolution *of a pushforward*, whose terms
are not injective sheaves on the source but do have vanishing higher Čech cohomology.

## Main definitions

* `Stacks.Cohomology.CechDerived.cechTotalAugmentation`: the augmentation
  `Γ(U, J•) ⟶ Tot(Č•(Ui, J•))` for a bounded-below complex `J` with vanishing higher Čech
  cohomology in each resolution degree.

## Main results

* `Stacks.Cohomology.CechDerived.exactAt_cechBicomplex_X_of_isZero_homology`: the columns of the
  Čech bicomplex are exact away from Čech degree zero as soon as the higher Čech cohomology of
  each term vanishes.
* `Stacks.Cohomology.CechDerived.hypotheses_cechAlphaRow_of_isZero_homology`: the hypotheses of
  [Stacks, Tag 0133] for the Čech bicomplex under that vanishing.
* `Stacks.Cohomology.CechDerived.quasiIso_cechTotalAugmentation`: the augmentation is a
  quasi-isomorphism.
* `Stacks.Cohomology.CechDerived.cechTotalAugmentation_naturality`: any two morphisms into the
  total complexes with the augmentation as components form a commutative square with the
  induced map of total complexes.
* `Stacks.Cohomology.CechDerived.isStrictlyGE_total_cechBicomplex`: the total complex of the
  Čech bicomplex of a bounded-below complex is bounded below.
* `Stacks.Cohomology.CechDerived.cechBeta_comp_cechTotalMap_id`: naturality of the companion
  augmentation `β` over the identity of the resolved sheaf of modules.

## Implementation notes

Only the positive-degree branch of
`Stacks.Cohomology.CechDerived.exactAt_cechBicomplex_X` uses injectivity, through
`Stacks.Cohomology.CechSheaf.isZero_cechComplex_homology_of_injective`; everything else --
the vanishing in negative Čech degree, the finiteness of the antidiagonals, and the kernel
clause `Stacks.Cohomology.CechDerived.inducesIsoKernel_cechAlphaRow`, which is the sheaf
condition for the cover and holds for every sheaf of modules -- is already stated in the
generality needed here.  So the generalisation changes that one branch and reuses the rest.

Naturality is stated for arbitrary morphisms into the total complexes whose components are the
Čech augmentation, rather than for `cechTotalAugmentation` itself: the consumers in
[Stacks, Tag 01FD] obtain their augmentations from
`Stacks.Cohomology.CechDerived.CechResolutionComparison`, which pins the components and not the
morphism, and the square needs no vanishing hypothesis at all.

## References

* [Stacks Project, Tag 01FD](https://stacks.math.columbia.edu/tag/01FD)
* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf

universe u

namespace Stacks.Cohomology.CechDerived

attribute [local instance] HasDerivedCategory.standard

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {I : Type u} (U : Opens X) (Ui : I → Opens X) (hU : U = ⨆ i, Ui i)

/-- **The columns of the Čech bicomplex are exact away from Čech degree zero** as soon as the
higher Čech cohomology of every term of the resolved complex vanishes.  In negative degree the
column is supported away from it; in positive degree the column is the Čech complex of the term,
transported along the extension by zero, and the hypothesis is exactly its vanishing.

This is the generalisation of `Stacks.Cohomology.CechDerived.exactAt_cechBicomplex_X` needed by
[Stacks, Tag 01FD], where the resolved complex is an injective resolution of a pushforward: its
terms are not injective sheaves on the source, but their higher Čech cohomology vanishes. -/
lemma exactAt_cechBicomplex_X_of_isZero_homology
    (J : CochainComplex (SheafOfModules.{u} O) ℤ)
    (hJ : ∀ (q : ℤ) (n : ℕ), 0 < n →
      IsZero (((cechComplexNatFunctor O U Ui hU).obj (J.X q)).homology n))
    (q p : ℤ) (hp : p ≠ 0) :
    ((cechBicomplex O U Ui hU J).X q).ExactAt p := by
  rcases lt_trichotomy p 0 with h | h | h
  · exact HomologicalComplex.extend_exactAt _ embeddingUpNat p
      fun j => by change ((j : ℕ) : ℤ) ≠ p; omega
  · exact absurd h hp
  · have hk : embeddingUpNat.f p.toNat = p := by change ((p.toNat : ℕ) : ℤ) = p; omega
    refine (HomologicalComplex.extend_exactAt_iff _ embeddingUpNat hk).2 ?_
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (hJ q p.toNat (by omega))

/-- **The hypotheses of [Stacks, Tag 0133] for the Čech bicomplex of a bounded-below complex
with vanishing higher Čech cohomology**, with the Čech augmentation in each resolution degree.
This is `Stacks.Cohomology.CechDerived.hypotheses_cechAlphaRow` with the injectivity of the
terms weakened to the vanishing it is used for, as required by [Stacks, Tag 01FD]. -/
theorem hypotheses_cechAlphaRow_of_isZero_homology
    (J : CochainComplex (SheafOfModules.{u} O) ℤ) (a : ℤ) [J.IsStrictlyGE a]
    (hJ : ∀ (q : ℤ) (n : ℕ), 0 < n →
      IsZero (((cechComplexNatFunctor O U Ui hU).obj (J.X q)).homology n)) :
    Hypotheses
      (((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).obj J)
      (cechBicomplex O U Ui hU J) (cechAlphaRow O U Ui hU J) where
  diagonalFinite := diagonalFinite_cechBicomplex O U Ui hU J a
  zero_of_neg q p hp := isZero_cechBicomplex_X_X O U Ui hU J q p (Or.inr hp)
  exactAt_of_ne_zero q p hp :=
    exactAt_cechBicomplex_X_of_isZero_homology O U Ui hU J hJ q p hp
  inducesIsoKernel q := inducesIsoKernel_cechAlphaRow O U Ui hU J q

/-- **The total Čech augmentation**: the sections of a bounded-below complex of sheaves of
modules with vanishing higher Čech cohomology include into the total complex of its Čech
bicomplex, in the `(q, 0)` corner.  This is the map `α` of the proof of [Stacks, Tag 01FD],
and agrees with `Stacks.Cohomology.CechDerived.cechAlpha` whenever both are defined. -/
def cechTotalAugmentation (J : CochainComplex (SheafOfModules.{u} O) ℤ) [J.IsStrictlyGE 0]
    (hJ : ∀ (q : ℤ) (n : ℕ), 0 < n →
      IsZero (((cechComplexNatFunctor O U Ui hU).obj (J.X q)).homology n)) :
    ((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).obj J ⟶
      (cechBicomplex O U Ui hU J).total (up ℤ) :=
  comparisonMapP _ _ _ (hypotheses_cechAlphaRow_of_isZero_homology O U Ui hU J 0 hJ)

/-- **The component formula for the total Čech augmentation**: in degree `q` it is the Čech
augmentation of `J^q` followed by the inclusion of the summand `(q, 0)`.  This is the component
formula required by [Stacks, Tag 01FD]. -/
lemma cechTotalAugmentation_f (J : CochainComplex (SheafOfModules.{u} O) ℤ) [J.IsStrictlyGE 0]
    (hJ : ∀ (q : ℤ) (n : ℕ), 0 < n →
      IsZero (((cechComplexNatFunctor O U Ui hU).obj (J.X q)).homology n)) (q : ℤ) :
    (cechTotalAugmentation O U Ui hU J hJ).f q = cechAugmentationInt O U Ui hU (J.X q) ≫
      (cechBicomplex O U Ui hU J).ιTotal (up ℤ) q 0 q (by simp) :=
  comparisonMapP_f _ _ _ _ q

/-- **The total Čech augmentation is a quasi-isomorphism**, by [Stacks, Tag 0133]: the columns
of the Čech bicomplex are the Čech complexes of the terms `J^q`, whose augmented Čech complexes
are exact -- in degree zero because a sheaf satisfies the sheaf condition for the cover, in
positive degree by the assumed vanishing.  This is the quasi-isomorphy used in
[Stacks, Tag 01FD]. -/
instance quasiIso_cechTotalAugmentation (J : CochainComplex (SheafOfModules.{u} O) ℤ)
    [J.IsStrictlyGE 0]
    (hJ : ∀ (q : ℤ) (n : ℕ), 0 < n →
      IsZero (((cechComplexNatFunctor O U Ui hU).obj (J.X q)).homology n)) :
    QuasiIso (cechTotalAugmentation O U Ui hU J hJ) :=
  quasiIso_comparisonMapP _ _ _ _

/-- **A morphism into the total complex of a Čech bicomplex is determined by its components**,
so any such morphism whose components are the Čech augmentation is the total Čech
augmentation. -/
lemma eq_cechTotalAugmentation (J : CochainComplex (SheafOfModules.{u} O) ℤ) [J.IsStrictlyGE 0]
    (hJ : ∀ (q : ℤ) (n : ℕ), 0 < n →
      IsZero (((cechComplexNatFunctor O U Ui hU).obj (J.X q)).homology n))
    (a : ((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).obj J ⟶
      (cechBicomplex O U Ui hU J).total (up ℤ))
    (ha : ∀ q, a.f q = cechAugmentationInt O U Ui hU (J.X q) ≫
      (cechBicomplex O U Ui hU J).ιTotal (up ℤ) q 0 q (by simp)) :
    a = cechTotalAugmentation O U Ui hU J hJ :=
  HomologicalComplex.hom_ext _ _ fun q =>
    (ha q).trans (cechTotalAugmentation_f O U Ui hU J hJ q).symm

/-- **The total Čech augmentation is natural in the resolved complex.**  Stated for arbitrary
morphisms into the total complexes whose components are the Čech augmentation, since that is
how the consumers in [Stacks, Tag 01FD] receive them; no vanishing hypothesis is needed,
because the square is the naturality of the Čech augmentation read inside the `(q, 0)`
summand. -/
lemma cechTotalAugmentation_naturality {J K : CochainComplex (SheafOfModules.{u} O) ℤ}
    [J.IsStrictlyGE 0] [K.IsStrictlyGE 0] (g : J ⟶ K)
    (aJ : ((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).obj J ⟶
      (cechBicomplex O U Ui hU J).total (up ℤ))
    (aK : ((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).obj K ⟶
      (cechBicomplex O U Ui hU K).total (up ℤ))
    (hJ : ∀ q, aJ.f q = cechAugmentationInt O U Ui hU (J.X q) ≫
      (cechBicomplex O U Ui hU J).ιTotal (up ℤ) q 0 q (by simp))
    (hK : ∀ q, aK.f q = cechAugmentationInt O U Ui hU (K.X q) ≫
      (cechBicomplex O U Ui hU K).ιTotal (up ℤ) q 0 q (by simp)) :
    aJ ≫ cechTotalMap O U Ui hU g =
      ((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).map g ≫ aK :=
  HomologicalComplex.hom_ext _ _ fun q =>
    (congrArg (fun m => m ≫ (cechTotalMap O U Ui hU g).f q) (hJ q)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun m => cechAugmentationInt O U Ui hU (J.X q) ≫ m)
            (ιTotal_comp_cechTotalMap O U Ui hU g q 0 q (by simp))).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg
                (fun m => m ≫ (cechBicomplex O U Ui hU K).ιTotal (up ℤ) q 0 q (by simp))
                (cechAugmentationInt_naturality O U Ui hU (g.f q))).trans
              ((Category.assoc _ _ _).trans
                (congrArg
                  (fun m => (SheafOfModules.evaluation.{u} O (op U)).map (g.f q) ≫ m)
                  (hK q).symm))))))

/-- **The total complex of the Čech bicomplex of a complex bounded below in degree `a` is
bounded below in degree `a`.**  A summand of the total complex in degree `n` has either
resolution degree below `a`, where the resolved complex vanishes, or Čech degree negative,
where the Čech complex extended by zero vanishes.  This is what presents the total complex as
an object of the bounded-below derived category in [Stacks, Tag 01FD]. -/
lemma isStrictlyGE_total_cechBicomplex (J : CochainComplex (SheafOfModules.{u} O) ℤ) (a : ℤ)
    [J.IsStrictlyGE a] [(cechBicomplex O U Ui hU J).HasTotal (up ℤ)] :
    CochainComplex.IsStrictlyGE ((cechBicomplex O U Ui hU J).total (up ℤ)) a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  refine (IsZero.iff_id_eq_zero _).2 ?_
  apply HomologicalComplex₂.total.hom_ext (up ℤ)
  intro p q hpq
  refine (isZero_cechBicomplex_X_X O U Ui hU J p q ?_).eq_of_src _ _
  by_cases hp : p < a
  · exact Or.inl (J.isZero_of_isStrictlyGE a p hp)
  · change p + q = n at hpq
    exact Or.inr (by omega)

/-- **`β` is natural in the resolution over the identity of the resolved sheaf.**  Two
morphisms out of a sheaf of modules into the degree-zero terms of two complexes, each killed by
the first differential and compatible with a morphism of the complexes, give the same map into
the total complex after composing with the induced map of total complexes.  This is the form in
which the second square of the proof of [Stacks, Tag 01FD] is used. -/
lemma cechBeta_comp_cechTotalMap_id (J K : CochainComplex (SheafOfModules.{u} O) ℤ)
    [J.IsStrictlyGE 0] [K.IsStrictlyGE 0] {F : SheafOfModules.{u} O}
    (ξ : F ⟶ J.X 0) (hz : ξ ≫ J.d 0 1 = 0) (ξ' : F ⟶ K.X 0) (hz' : ξ' ≫ K.d 0 1 = 0)
    (φ : J ⟶ K) (hξ : ξ ≫ φ.f 0 = ξ') :
    cechBeta O U Ui hU J ξ hz ≫ cechTotalMap O U Ui hU φ =
      cechBeta O U Ui hU K ξ' hz' :=
  (cechBeta_comp_cechTotalMap O U Ui hU J K (𝟙 F) ξ hz ξ' hz' φ
      (hξ.trans (Category.id_comp ξ').symm)).trans
    ((congrArg (fun z => z ≫ cechBeta O U Ui hU K ξ' hz')
        (CategoryTheory.Functor.map_id (cechComplexIntFunctor O U Ui hU) F)).trans
      (Category.id_comp _))

end Stacks.Cohomology.CechDerived

end
