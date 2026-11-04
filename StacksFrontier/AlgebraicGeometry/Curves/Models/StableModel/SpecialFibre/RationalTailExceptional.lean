module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelNumericalTypeIff
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ExceptionalComponentsMeet
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberIntersectionForm
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreGenusEquality
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.GeometricallyReducedSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.ComponentComplementaryDegree
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionDegree
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.BaseChangeDegree
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusNormalizationBound
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.ClosedImmersionIdealSheaves
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.ProductSubscheme
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.RationalTail

/-!
# A rational tail of the special fibre of a minimal model

Let `X ⟶ Spec R` be a regular proper model as in [Stacks, Tag 0C61] whose special fibre `X_k` has
at-worst-nodal singularities and all of whose multiplicities are `1`. A rational tail `C` of
`X_k` is then an exceptional curve of the first kind on `X`, so a minimal model has none.

The argument: `C` is a component `C_Z` of `X_k` with its reduced structure, of genus zero over
`κ_Z = Γ(C_Z, 𝒪)`. As all multiplicities are one, `(C_Z · C_Z) = -∑_{Y ≠ Z} (C_Z · C_Y)`; each
`(C_Z · C_Y)` is the degree of the scheme-theoretic intersection `C_Z ∩ C_Y`, and on the nodal
curve `X_k` these intersections add up to the intersection of `C_Z` with the closure of its
complement, which for a rational tail is a single point with residue field `κ_Z`. So
`(C_Z · C_Z) = -[κ_Z : k]`, and a genus-zero component with this self-intersection is a projective
line over `κ_Z` and an exceptional curve of the first kind.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.comap_ker_comp`: for closed immersions `i` and `j`,
  the inverse image of the ideal of `i ≫ j` along `j` is the ideal of `i`.
* `AlgebraicGeometry.Scheme.IdealSheafData.exists_iso_comap_subscheme_ker_sup`: the inverse image
  of `J` along a closed immersion `ι` cuts out the intersection with `J` of the image of `ι`.
* `Stacks.Models.RegularProperModelSituation.ker_specialFiberComponentι`: the ideal of a
  component in `X_k` is the vanishing ideal of the component.
* `Stacks.Models.RegularProperModelSituation.sum_specialFiberIntersectionMatrix_erase_eq`:
  `∑_{Y ≠ Z} (C_Z · C_Y) = deg (C_Z ∩ X'_{C_Z})` on a nodal special fibre.
* `Stacks.Models.RegularProperModelSituation.not_isRationalTail_specialFiber`: a model without
  exceptional curves of the first kind, with nodal special fibre of multiplicities one, has no
  rational tail in its special fibre.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- **The ideal of a closed subscheme of a closed subscheme.** For closed immersions
`i : A ⟶ X` and `j : X ⟶ Y`, the inverse image along `j` of the ideal of `i ≫ j` is the ideal of
`i`: the square formed by `i`, `𝟙 A`, `j` and `i ≫ j` is cartesian since `j` is a
monomorphism. -/
theorem comap_ker_comp {A X Y : Scheme.{u}} (i : A ⟶ X) (j : X ⟶ Y) [IsClosedImmersion i]
    [IsClosedImmersion j] : (i ≫ j).ker.comap j = i.ker := by
  have hsq : IsPullback i (𝟙 A) j (i ≫ j) := IsPullback.mk' (by simp)
    (fun _ _ _ _ h₂ => by simpa using h₂)
    (fun _ a b hab => ⟨b, (cancel_mono j).1 (by simpa using hab.symm), by simp⟩)
  rw [← ker_fst_of_isClosedImmersion, ← Scheme.Hom.ker_comp_of_isIso hsq.isoPullback.hom,
    IsPullback.isoPullback_hom_fst]

/-- **Pulling an ideal back along a closed immersion.** For a closed immersion `ι : X ⟶ Y` and an
ideal sheaf `J` on `Y`, the closed subscheme of `X` cut out by `ι⁻¹ J` is, as a closed subscheme
of `Y`, the intersection of the image of `ι` with the subscheme cut out by `J`: both are the fibre
product of `ι` with `J.subschemeι`. -/
theorem exists_iso_comap_subscheme_ker_sup {X Y : Scheme.{u}} (ι : X ⟶ Y) [IsClosedImmersion ι]
    (J : Y.IdealSheafData) :
    ∃ e : (J.comap ι).subscheme ≅ (ι.ker ⊔ J).subscheme,
      e.hom ≫ (ι.ker ⊔ J).subschemeι = (J.comap ι).subschemeι ≫ ι := by
  have h1 := Scheme.IdealSheafData.isPullback_comap_subschemeι J ι
  have h1' := h1.of_iso (Iso.refl _) (asIso ι.toImage) (Iso.refl _) (Iso.refl _)
    (fst' := (J.comap ι).subschemeι ≫ ι.toImage) (f' := ι.ker.subschemeι)
    (snd' := (J.comap ι).subschemeMap J ι (J.le_map_comap ι)) (g' := J.subschemeι)
    (by simp) (by simp) (by simp [Scheme.Hom.toImage_imageι]) (by simp)
  have h2 := isPullback_subscheme_sup Y ι.ker J
  refine ⟨h1'.isoIsPullback _ _ h2, ?_⟩
  rw [← inclusion_subschemeι (le_sup_left : ι.ker ≤ ι.ker ⊔ J),
    IsPullback.isoIsPullback_hom_fst_assoc, Category.assoc, Scheme.Hom.toImage_imageι]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- Isomorphic schemes over `Spec k`, via an isomorphism compatible with the structure maps, have
global sections of the same dimension over `k`. -/
private theorem finrank_globalSections_eq_of_iso_comp {k : Type u} [Field k] {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (.of k)) (q : Z ⟶ Spec (.of k)) (e : Z ≅ Y) (h : e.hom ≫ p = q) :
    letI : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
    letI : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop).hom.toAlgebra
    Module.finrank k Γ(Z, ⊤) = Module.finrank k Γ(Y, ⊤) := by
  subst h
  exact finrank_globalSections_eq_of_iso k p e

/-- The ideal of a component `C_Z` in `X_k` is the inverse image of its ideal in `X`. -/
theorem comap_specialFiberComponentIdeal_specialFiberι (Z : irreducibleComponents S.specialFiber) :
    (S.specialFiberComponentIdeal Z).comap S.specialFiberι = (S.specialFiberComponentι Z).ker := by
  have h := Scheme.IdealSheafData.comap_ker_comp (S.specialFiberComponentι Z) S.specialFiberι
  rwa [S.specialFiberComponentι_specialFiberι, Scheme.IdealSheafData.ker_subschemeι] at h

/-- **The ideal of a component in `X_k` is its vanishing ideal**: the component is integral, so
the closed immersion `C_Z ⟶ X_k` is the reduced induced structure on its image `Z`. -/
theorem ker_specialFiberComponentι (Z : irreducibleComponents S.specialFiber) :
    (S.specialFiberComponentι Z).ker =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure Z.1) := by
  have := S.toRegularModelSituation.isIntegral_specialFiberComponentIdeal Z
  rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range, S.range_specialFiberComponentι]

/-- **The intersection number of two distinct components is the degree of their intersection
in `X_k`.** The intersection `C_Z ∩ C_Y` of `ExceptionalComponentsMeet.lean`, formed on `C_Z`, is
the closed subscheme of `X_k` cut out by the sum of the ideals of the two components. -/
theorem finrank_structureSheafCohomology_zero_sup_ker_specialFiberComponentι
    {Z Y : irreducibleComponents S.specialFiber} (h : Z ≠ Y) :
    (Module.finrank S.k (structureSheafCohomology
      (((S.specialFiberComponentι Z).ker ⊔ (S.specialFiberComponentι Y).ker).subschemeι ≫
        S.specialFiberToSpec) 0) : ℤ) = S.specialFiberIntersectionMatrix Z Y := by
  have hcomap : (S.specialFiberComponentι Y).ker.comap (S.specialFiberComponentι Z) =
      S.componentIntersectionIdeal Z Y := by
    rw [componentIntersectionIdeal, ← S.specialFiberComponentι_specialFiberι Z,
      Scheme.IdealSheafData.comap_comp, S.comap_specialFiberComponentIdeal_specialFiberι]
  have hex := Scheme.IdealSheafData.exists_iso_comap_subscheme_ker_sup
    (S.specialFiberComponentι Z) (S.specialFiberComponentι Y).ker
  rw [hcomap] at hex
  obtain ⟨e, he⟩ := hex
  set p := ((S.specialFiberComponentι Z).ker ⊔ (S.specialFiberComponentι Y).ker).subschemeι ≫
    S.specialFiberToSpec with hp
  have hep : e.hom ≫ p =
      (S.componentIntersectionIdeal Z Y).subschemeι ≫ S.specialFiberComponentToSpec Z := by
    rw [hp, ← Category.assoc, he, Category.assoc]
    rfl
  have hiso := finrank_globalSections_eq_of_iso_comp p _ e hep
  have h0 := finrank_structureSheafCohomology_zero_eq_finrank_globalSections S.k p
  have h1 := S.specialFiberIntersectionMatrix_eq_finrank_globalSections h
  rw [h0, h1, ← hiso]

/-- On a scheme over a field, the closure of the complement of the whole scheme is empty, so it
meets nothing: `deg (I ∩ X'_X) = 0`. -/
theorem _root_.AlgebraicGeometry.finrank_structureSheafCohomology_zero_sup_complementary_bot
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (I : X.IdealSheafData) :
    Module.finrank k (structureSheafCohomology
      ((I ⊔ complementaryCurveIdeal (⊥ : X.IdealSheafData)).subschemeι ≫ f) 0) = 0 := by
  have hc : complementaryCurveIdeal (⊥ : X.IdealSheafData) = ⊤ := by
    rw [complementaryCurveIdeal, Scheme.Hom.ker_eq_top_iff_isEmpty]
    exact ⟨fun x => absurd (Set.mem_univ x.1) x.2⟩
  rw [hc, sup_top_eq]
  let : Algebra k Γ((⊤ : X.IdealSheafData).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ ((⊤ : X.IdealSheafData).subschemeι ≫ f).appTop).hom.toAlgebra
  refine (finrank_structureSheafCohomology_zero_eq_finrank_globalSections k
    ((⊤ : X.IdealSheafData).subschemeι ≫ f)).trans ?_
  exact Module.finrank_zero_of_subsingleton

/-- **The intersections of a component with the others add up to its intersection with the
closure of its complement.** On the at-worst-nodal special fibre, for a component `C_Z`,
`∑_{Y ≠ Z} (C_Z · C_Y) = deg (C_Z ∩ X'_{C_Z})`, where `X'_{C_Z}` is the closure of the complement
of `C_Z` in `X_k`: no point lies on three components. -/
theorem sum_specialFiberIntersectionMatrix_erase_eq
    (hnodal : letI : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩
      Stacks.Curves.HasAtWorstNodalSingularities S.k S.specialFiber)
    (Z : irreducibleComponents S.specialFiber) :
    ∑ Y ∈ Finset.univ.erase Z, S.specialFiberIntersectionMatrix Z Y =
      (Module.finrank S.k (structureSheafCohomology
        (((S.specialFiberComponentι Z).ker ⊔
          complementaryCurveIdeal (S.specialFiberComponentι Z).ker).subschemeι ≫
            S.specialFiberToSpec) 0) : ℤ) := by
  classical
  let : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩
  have : IsProper (S.specialFiber ↘ Spec (.of S.k)) :=
    inferInstanceAs (IsProper S.specialFiberToSpec)
  have : LocallyOfFiniteType (S.specialFiber ↘ Spec (.of S.k)) :=
    inferInstanceAs (LocallyOfFiniteType S.specialFiberToSpec)
  let Λ : Finset (Set S.specialFiber) :=
    Finset.univ.image (fun Y : irreducibleComponents S.specialFiber => Y.1)
  have hΛ : ∀ T : Set S.specialFiber, T ∈ Λ ↔ T ∈ irreducibleComponents S.specialFiber ∧
      T ⊆ ((⊥ : S.specialFiber.IdealSheafData).support : Set S.specialFiber) := by
    intro T
    simp only [Λ, Finset.mem_image, Finset.mem_univ, true_and,
      Scheme.IdealSheafData.support_bot, Closeds.coe_top, Set.subset_univ, and_true]
    exact ⟨fun ⟨Y, hY⟩ => hY ▸ Y.2, fun hT => ⟨⟨T, hT⟩, rfl⟩⟩
  have hZΛ : Z.1 ∈ Λ := Finset.mem_image_of_mem _ (Finset.mem_univ Z)
  have key : Module.finrank S.k (structureSheafCohomology
      ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure Z.1) ⊔
        complementaryCurveIdeal (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure Z.1))).subschemeι ≫ S.specialFiberToSpec) 0) =
      Module.finrank S.k (structureSheafCohomology
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure Z.1) ⊔
          complementaryCurveIdeal (⊥ : S.specialFiber.IdealSheafData)).subschemeι ≫
            S.specialFiberToSpec) 0) +
        ∑ T ∈ Λ.erase Z.1, Module.finrank S.k (structureSheafCohomology
          ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure Z.1) ⊔
            Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subschemeι ≫
              S.specialFiberToSpec) 0) :=
    Stacks.Curves.finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_component
      (S.topologicalKrullDim_specialFiber S.nonempty_specialFiber) hnodal ⊥ Λ hΛ hZΛ
  rw [finrank_structureSheafCohomology_zero_sup_complementary_bot, zero_add] at key
  have himg : Λ.erase Z.1 = (Finset.univ.erase Z).image (fun Y => Y.1) := by
    rw [Finset.image_erase Subtype.val_injective]
  rw [S.ker_specialFiberComponentι Z, key, Nat.cast_sum, himg,
    Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
  refine Finset.sum_congr rfl fun Y hY => ?_
  rw [← S.ker_specialFiberComponentι Z, ← S.ker_specialFiberComponentι Y]
  exact (S.finrank_structureSheafCohomology_zero_sup_ker_specialFiberComponentι
    (Finset.ne_of_mem_erase hY).symm).symm

/-- A rational tail of `X_k` is a component with its reduced structure. -/
theorem eq_ker_specialFiberComponentι_of_isRationalTail {C : S.specialFiber.IdealSheafData}
    (hC : letI : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩
      IsRationalTail S.k S.specialFiber C) :
    letI : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩
    C = (S.specialFiberComponentι
      ⟨C.support, IsRationalTail.support_mem_irreducibleComponents hC⟩).ker := by
  let : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩
  have : IsIntegral C.subscheme := IsRationalTail.isIntegral hC
  rw [ker_specialFiberComponentι]
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme C _
    (Closeds.ext (by simp [C.support.isClosed.closure_eq]))

/-- **No component of the special fibre of a minimal model is a rational tail**, when the special
fibre is at-worst-nodal with all multiplicities one: such a tail `C_Z` has genus zero and
`(C_Z · C_Z) = -∑_{Y ≠ Z} (C_Z · C_Y) = -deg (C_Z ∩ X'_{C_Z}) = -[κ_Z : k]`, so it is an
exceptional curve of the first kind. -/
theorem not_isRationalTail_ker_specialFiberComponentι
    (hmin : ¬ S.X.HasExceptionalCurveOfFirstKind)
    (hnodal : letI : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩
      Stacks.Curves.HasAtWorstNodalSingularities S.k S.specialFiber)
    (hmult : ∀ Z, S.specialFiberMultiplicity Z = 1) (Z : irreducibleComponents S.specialFiber) :
    letI : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩
    ¬ IsRationalTail S.k S.specialFiber (S.specialFiberComponentι Z).ker := by
  let : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩
  intro hC
  classical
  have hfac : (asIso (S.specialFiberComponentι Z).toImage).hom ≫
      (S.specialFiberComponentι Z).ker.subschemeι ≫ S.specialFiberToSpec =
        S.specialFiberComponentToSpec Z := by
    rw [asIso_hom, ← Category.assoc, Scheme.Hom.toImage_imageι]
    rfl
  -- the tail has genus zero over its field of constants
  have hg0 : genus (S.specialFiberComponentToSpec Z) = 0 := by
    rw [← hfac, genus_comp_iso_eq]
    exact IsRationalTail.genus_eq_zero hC
  have hgZ : S.specialFiberComponentGenus Z = 0 := by
    have h := S.genus_specialFiberComponentToSpec Z
    rw [hg0] at h
    have hw := S.specialFiberComponentWeight_pos Z
    rcases Nat.mul_eq_zero.mp h.symm with h' | h'
    · omega
    · exact h'
  -- its intersection with the closure of its complement has degree `[κ_Z : k]`
  have hdeg : (Module.finrank S.k (structureSheafCohomology
      (((S.specialFiberComponentι Z).ker ⊔
        complementaryCurveIdeal (S.specialFiberComponentι Z).ker).subschemeι ≫
          S.specialFiberToSpec) 0) : ℤ) = S.specialFiberComponentWeight Z := by
    have h1 := finrank_globalSections_intersection_of_isRationalTail hC
    have h3 := finrank_globalSections_eq_of_iso_comp
      ((S.specialFiberComponentι Z).ker.subschemeι ≫ S.specialFiberToSpec) _
      (asIso (S.specialFiberComponentι Z).toImage) hfac
    rw [finrank_structureSheafCohomology_zero_eq_finrank_globalSections]
    exact_mod_cast h1.trans h3.symm
  -- the row of `C_Z` in the intersection matrix sums to zero
  have hrow : ∑ Y, S.specialFiberIntersectionMatrix Z Y = 0 := by
    have h := S.specialFiberIntersectionProduct_multiplicity_eq_zero Z
    rw [S.specialFiberIntersectionProduct_eq_sum_sum] at h
    have hW : ∀ W, ∑ Y, (S.specialFiberMultiplicity W : ℤ) *
        (((Pi.single Z 1 : irreducibleComponents S.specialFiber → ℕ) Y : ℕ) : ℤ) *
          S.specialFiberIntersectionMatrix W Y = S.specialFiberIntersectionMatrix Z W := by
      intro W
      rw [Finset.sum_eq_single Z (fun Y _ hY => by simp [Pi.single_eq_of_ne hY]) (by simp),
        hmult, S.specialFiberIntersectionMatrix_comm W Z]
      simp
    rw [Finset.sum_congr rfl fun W _ => hW W] at h
    exact h
  have hN : S.specialFiberIntersectionMatrix Z Z = -(S.specialFiberComponentWeight Z : ℤ) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ Z),
      S.sum_specialFiberIntersectionMatrix_erase_eq hnodal Z, hdeg] at hrow
    linarith
  obtain ⟨κ, hκ, ⟨ε⟩⟩ := S.exists_iso_projectiveLineProj_specialFiberComponentIdeal Z hgZ hN
  exact hmin ⟨κ, hκ, _, ε,
    S.isExceptionalCurveOfFirstKind_specialFiberComponentIdeal_of_iso Z hN κ ε⟩

/-- **The special fibre of a minimal model has no rational tail**, when it is at-worst-nodal with
all multiplicities one. -/
theorem not_isRationalTail_specialFiber (hmin : ¬ S.X.HasExceptionalCurveOfFirstKind)
    (hnodal : letI : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩
      Stacks.Curves.HasAtWorstNodalSingularities S.k S.specialFiber)
    (hmult : ∀ Z, S.specialFiberMultiplicity Z = 1) :
    letI : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩
    ∀ C : S.specialFiber.IdealSheafData, ¬ IsRationalTail S.k S.specialFiber C := by
  let : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩
  intro C hC
  have hCK := S.eq_ker_specialFiberComponentι_of_isRationalTail hC
  rw [hCK] at hC
  exact S.not_isRationalTail_ker_specialFiberComponentι hmin hnodal hmult _ hC

end Stacks.Models.RegularProperModelSituation

end
