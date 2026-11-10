module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Completion.Complement
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Basic

/-!
# The divisor at infinity as the zero scheme of a section of `𝒪_P(1)`

Let `ℰ` be a finite locally free module on a scheme `X`, `π : P = 𝐏(ℰ ⊕ 𝒪_X) ⟶ X` its projective
completion and `i : 𝐏(ℰ) ⟶ P` the divisor at infinity. The global section `(0, 1)` of
`ℰ ⊕ 𝒪_X` gives, through the tautological map `π^*(ℰ ⊕ 𝒪_X) ⟶ 𝒪_P(1)`, a global section

  `s ∈ Γ(P, 𝒪_P(1))`.

This file proves, following the proof of [Stacks, Tag 02TY], that the zero scheme `Z(s)` of
[Stacks, Tag 02OQ] is the divisor at infinity and that `s` is a regular section: `Z(s)` is an
effective Cartier divisor, so `𝒪_P(Z(s)) ≅ 𝒪_P(1)`. Over the chart `Proj Γ(U, Sym(ℰ ⊕ 𝒪_X))` of an
affine open `U` of `X`, the section `s` is the section of the twisting sheaf attached to the
degree-one element `T` of `(0, 1)`, and `T` generates the kernel of
`Γ(U, Sym(ℰ ⊕ 𝒪_X)) ⟶ Γ(U, Sym(ℰ))` and is a nonzerodivisor.

## Main definitions

* `Stacks.ProjectiveCompletion.infinityTwistSection`: the section `s ∈ Γ(P, 𝒪_P(1))`.
* `Stacks.ProjectiveCompletion.infinityDivisorIso`: the isomorphism `𝐏(ℰ) ≅ Z(s)` over `P`.

## Main results

* `Stacks.ProjectiveCompletion.zeroScheme_infinityTwistSection_eq_ker`: `Z(s)` is the closed
  subscheme cut out by `i`.
* `Stacks.ProjectiveCompletion.isEffectiveCartierDivisor_zeroScheme_infinityTwistSection`: `Z(s)`
  is an effective Cartier divisor.
* `Stacks.ProjectiveCompletion.isRelativeEffectiveCartierDivisor_zeroScheme_infinityTwistSection`:
  it is a relative effective Cartier divisor over `X`.

## References

* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjDegreeOne
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace Stacks.ProjectiveCompletion

/-! ### Pulling a global section back twice -/

section PullbackSections

variable {X Y Z : Scheme.{u}}

/-- A global section pulled back along `π` and then along `c` is, on the inverse image of an open
`V` containing the image of `c ≫ π`, the section restricted to `V` pulled back twice. -/
theorem pullbackGlobalSections_pullbackGlobalSections (π : Y ⟶ X) (c : Z ⟶ Y) (M : X.Modules)
    (V : X.Opens) (h : ⊤ ≤ c ⁻¹ᵁ π ⁻¹ᵁ V) (x : Γ(M, ⊤)) :
    pullbackGlobalSections c ((Scheme.Modules.pullback π).obj M)
        (pullbackGlobalSections π M x) =
      ((Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback π).obj M)).val.map
        (homOfLE h).op
        (unitSection c ((Scheme.Modules.pullback π).obj M) (π ⁻¹ᵁ V)
          (unitSection π M V (M.val.map (homOfLE le_top).op x))) := by
  set N := (Scheme.Modules.pullback π).obj M
  set N' := (Scheme.Modules.pullback c).obj N
  have h1 := Stacks.Chow.GenuineChern.unitSection_restrict π M (le_top : V ≤ ⊤) x
  have key := fun {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ ⊤) =>
    Stacks.Chow.GenuineChern.unitSection_restrict c N hW (unitSection π M ⊤ x)
  rw [h1, key (π.preimage_mono le_top)]
  change N'.val.map _ (unitSection c N ⊤ (N.val.map _ (unitSection π M ⊤ x))) = _
  rw [show N.val.map (eqToHom (show (⊤ : Y.Opens) = π ⁻¹ᵁ ⊤ by simp)).op
      (unitSection π M ⊤ x) =
      N.val.map (homOfLE (show (⊤ : Y.Opens) ≤ π ⁻¹ᵁ ⊤ from le_top)).op
        (unitSection π M ⊤ x) from rfl, key le_top]
  change N'.presheaf.map _ (N'.presheaf.map _ _) = N'.presheaf.map _ (N'.presheaf.map _ _)
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp]
  rfl

/-- A global section pulled back along `π`, mapped by `φ : π^*M ⟶ L` and pulled back along `c`, is
`c^*φ` applied to the section restricted to an open `V` containing the image of `c ≫ π` and
pulled back twice. -/
theorem pullbackGlobalSections_app_pullbackGlobalSections (π : Y ⟶ X) (c : Z ⟶ Y)
    (M : X.Modules) (L : Y.Modules) (φ : (Scheme.Modules.pullback π).obj M ⟶ L) (V : X.Opens)
    (h : ⊤ ≤ c ⁻¹ᵁ π ⁻¹ᵁ V) (x : Γ(M, ⊤)) :
    pullbackGlobalSections c L (φ.app ⊤ (pullbackGlobalSections π M x)) =
      ((Scheme.Modules.pullback c).map φ).app ⊤
        (((Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback π).obj M)).val.map
          (homOfLE h).op
          (unitSection c ((Scheme.Modules.pullback π).obj M) (π ⁻¹ᵁ V)
            (unitSection π M V (M.val.map (homOfLE le_top).op x)))) :=
  (pullbackGlobalSections_natural c φ _).trans
    (congrArg _ (pullbackGlobalSections_pullbackGlobalSections π c M V h x))

end PullbackSections

/-! ### The zero scheme of the image of a pulled-back section, on a chart -/

section Chart

variable {X : Scheme.{u}} (G : X.Modules) [G.IsQuasicoherent] (hqc : IsQuasicoherentPieces G)
  (M : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
  (f : M ⟶ G)

/-- **The global section `τ(π^*f(x))` of `𝒪(1)`** on the projective bundle `𝐏(G)` attached to a
global section `x` of `M` and `f : M ⟶ G`: the pullback of `x` mapped by `π^*M ⟶ π^*G ⟶ 𝒪(1)`. -/
def tautologicalSectionOf (x : Γ(M, ⊤)) :
    Γ(Stacks.ProjectiveBundleSplitting.tautologicalTwist G hqc, ⊤) :=
  Scheme.Modules.Hom.app (Stacks.Chow.GenuineChern.bundleSectionHom G hqc M f) ⊤
    (pullbackGlobalSections (relativeProj (schemeSheafGradedAlgebra G hqc)).toBase M x)

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] in
/-- **The zero scheme of `τ(π^*f(x))` on a chart.** For a global section `x` of `M` and
`f : M ⟶ G`, the image of `π^*x` under `π^*M ⟶ π^*G ⟶ 𝒪(1)` is a global section of `𝒪(1)` on
`𝐏(G)`; over an affine open `V` of the base, the inverse image of its zero scheme along the chart
`Proj Γ(V, Sym G) ⟶ 𝐏(G)` is the zero scheme of the global section of the twisting sheaf attached
to the degree-one element `f(x|_V)`. -/
theorem comap_chart_zeroScheme_bundleSectionHom_app (x : Γ(M, ⊤)) (V : X.Opens)
    (hV : IsAffineOpen V) (y : (schemeSheafGradedAlgebra G hqc).grading V 1)
    (hy : (y : (schemeSheafGradedAlgebra G hqc).sectionRing V) =
      DirectSum.of ((schemeSheafGradedAlgebra G hqc).sectionPieces V) 1
        ((Scheme.Modules.symmetricAlgebraGen X G).val.app (op V)
          (f.val.app (op V) (M.val.map (homOfLE le_top).op x)))) :
    letI := Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart
      (relativeProj (schemeSheafGradedAlgebra G hqc)) V hV
    haveI := algebraicGeometry_isInvertible_twistingSheaf
      ((schemeSheafGradedAlgebra G hqc).grading V)
      (adjoin_grading_one_eq_top G V hqc hV) ((1 : ℕ) : ℤ)
    (@Stacks.Divisors.zeroScheme _ (Stacks.ProjectiveBundleSplitting.tautologicalTwist G hqc)
        (Stacks.Chow.GenuineChern.isInvertible_tautologicalTwist' G hqc)
        (tautologicalSectionOf G hqc M f x)).comap
        ((relativeProj (schemeSheafGradedAlgebra G hqc)).chart V hV) =
      Stacks.Divisors.zeroScheme
        (AlgebraicGeometry.Proj ((schemeSheafGradedAlgebra G hqc).grading V))
        (twistingSheafModule ((schemeSheafGradedAlgebra G hqc).grading V) ((1 : ℕ) : ℤ))
        (degreeSection ((schemeSheafGradedAlgebra G hqc).grading V) 1 y) := by
  obtain ⟨y, hy'⟩ := y
  change y = _ at hy
  subst hy
  unfold tautologicalSectionOf
  let := Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart
    (relativeProj (schemeSheafGradedAlgebra G hqc)) V hV
  have := algebraicGeometry_isInvertible_twistingSheaf
    ((schemeSheafGradedAlgebra G hqc).grading V)
    (adjoin_grading_one_eq_top G V hqc hV) ((1 : ℕ) : ℤ)
  let := Stacks.Chow.GenuineChern.isInvertible_tautologicalTwist' G hqc
  have := Stacks.Chow.GenuineChern.isInvertible_pullback
    ((relativeProj (schemeSheafGradedAlgebra G hqc)).chart V hV)
    (Stacks.ProjectiveBundleSplitting.tautologicalTwist G hqc)
  have hsec := pullbackGlobalSections_app_pullbackGlobalSections
    (relativeProj (schemeSheafGradedAlgebra G hqc)).toBase
    ((relativeProj (schemeSheafGradedAlgebra G hqc)).chart V hV) M
    (Stacks.ProjectiveBundleSplitting.tautologicalTwist G hqc)
    (Stacks.Chow.GenuineChern.bundleSectionHom G hqc M f) V
    (Stacks.Chow.GenuineChern.top_le_chart_preimage G hqc V hV) x
  have hval := Stacks.Chow.GenuineChern.chartIso_bundleSectionHom_unitSection G hqc M f V hV
    (M.val.map (homOfLE le_top).op x)
  refine (Stacks.Divisors.zeroScheme_pullback
    ((relativeProj (schemeSheafGradedAlgebra G hqc)).chart V hV)
    (Stacks.ProjectiveBundleSplitting.tautologicalTwist G hqc) _).symm.trans ?_
  refine (congrArg (Stacks.Divisors.zeroScheme _
    ((Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra G hqc)).chart V hV)).obj
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist G hqc))) hsec).trans ?_
  exact AlgebraicGeometry.zeroScheme_eq_of_iso _ hval

end Chart

/-! ### The section `s` of `𝒪_P(1)` -/

variable {X : Scheme.{u}} (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The section `s ∈ Γ(P, 𝒪_P(1))` of the projective completion attached to `(0, 1)`**: the
global section `1` of `𝒪_X`, pulled back to `P`, mapped to `𝒪_P(1)` by `π^*𝒪_X ⟶ π^*(ℰ ⊕ 𝒪_X)`
followed by the tautological map `π^*(ℰ ⊕ 𝒪_X) ⟶ 𝒪_P(1)`. -/
abbrev infinityTwistSection :
    Γ(Stacks.ProjectiveBundleSplitting.tautologicalTwist (completionModule E)
      (Stacks.Chow.bundlePieces (completionModule E)), ⊤) :=
  tautologicalSectionOf (completionModule E) (Stacks.Chow.bundlePieces (completionModule E))
    (Stacks.Ample.unitModule X) (completionInclusion E) (unitModuleOne X ⊤)

/-- The degree-one element `T` of `Γ(U, Sym(ℰ ⊕ 𝒪_X))`, written as the image of the restriction
of the global section `1`. -/
theorem infinitySection_eq_restrict (U : X.Opens) :
    infinitySection E U = DirectSum.of ((completionAlgebra E).sectionPieces U) 1
      ((Scheme.Modules.symmetricAlgebraGen X (completionModule E)).val.app (op U)
        ((completionInclusion E).val.app (op U)
          ((Stacks.Ample.unitModule X).val.map (homOfLE le_top).op (unitModuleOne X ⊤)))) := by
  rw [unitModuleOne_restrict]
  rfl

/-! ### The divisor at infinity is the zero scheme of `s` -/

section Divisor

/-- The zero scheme of `s`, in the spelling of the relative `Proj`, is the kernel of the closed
immersion `Proj_X(Sym(ℰ)) ⟶ Proj_X(Sym(ℰ ⊕ 𝒪_X))`. -/
theorem zeroScheme_infinityTwistSection_eq_ker :
    @Stacks.Divisors.zeroScheme (relativeProj (completionAlgebra E)).scheme
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist (completionModule E)
          (Stacks.Chow.bundlePieces (completionModule E)))
        (Stacks.Chow.GenuineChern.isInvertible_tautologicalTwist' (completionModule E)
          (Stacks.Chow.bundlePieces (completionModule E))) (infinityTwistSection E) =
      (Stacks.AlgebraicGeometry.ProjBundleSurjection.map
        (Stacks.Chow.GenuineChern.surjectiveOnAffineSections_bundle
          (completionProjection E))).ker := by
  let := Stacks.Chow.GenuineChern.isInvertible_tautologicalTwist' (completionModule E)
    (Stacks.Chow.bundlePieces (completionModule E))
  refine Stacks.Chow.GenuineChern.zeroScheme_eq_ker_map_of_charts
    (Stacks.Chow.GenuineChern.surjectiveOnAffineSections_bundle
      (completionProjection E))
    (fun U : X.affineOpens => U.1) (fun U => U.2) (AlgebraicGeometry.iSup_affineOpens_eq_top X)
    (fun U => adjoin_grading_one_eq_top (completionModule E) U.1
      (Stacks.Chow.bundlePieces (completionModule E)) U.2)
    (fun U => ⟨infinitySection E U.1, infinitySection_mem E U.1⟩)
    (Stacks.ProjectiveBundleSplitting.tautologicalTwist (completionModule E)
      (Stacks.Chow.bundlePieces (completionModule E)))
    (infinityTwistSection E) (fun U => ?_) (fun U => ker_sectionHom_eq_span E U.1 U.2)
  exact comap_chart_zeroScheme_bundleSectionHom_app (completionModule E)
    (Stacks.Chow.bundlePieces (completionModule E)) (Stacks.Ample.unitModule X)
    (completionInclusion E) (unitModuleOne X ⊤) U.1 U.2
    ⟨infinitySection E U.1, infinitySection_mem E U.1⟩ (infinitySection_eq_restrict E U.1)

/-- The zero scheme of `s`, in the spelling of the relative `Proj`, is an effective Cartier
divisor. -/
theorem isEffectiveCartierDivisor_zeroScheme_infinityTwistSection :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (@Stacks.Divisors.zeroScheme (relativeProj (completionAlgebra E)).scheme
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist (completionModule E)
          (Stacks.Chow.bundlePieces (completionModule E)))
        (Stacks.Chow.GenuineChern.isInvertible_tautologicalTwist' (completionModule E)
          (Stacks.Chow.bundlePieces (completionModule E))) (infinityTwistSection E)) := by
  let := Stacks.Chow.GenuineChern.isInvertible_tautologicalTwist' (completionModule E)
    (Stacks.Chow.bundlePieces (completionModule E))
  exact Stacks.Chow.GenuineChern.isEffectiveCartierDivisor_zeroScheme_of_charts
    (fun U : X.affineOpens => U.1) (fun U => U.2) (AlgebraicGeometry.iSup_affineOpens_eq_top X)
    (fun U => adjoin_grading_one_eq_top (completionModule E) U.1
      (Stacks.Chow.bundlePieces (completionModule E)) U.2)
    (fun U => ⟨infinitySection E U.1, infinitySection_mem E U.1⟩) _ _
    (fun U => comap_chart_zeroScheme_bundleSectionHom_app (completionModule E)
      (Stacks.Chow.bundlePieces (completionModule E)) (Stacks.Ample.unitModule X)
      (completionInclusion E) (unitModuleOne X ⊤) U.1 U.2
      ⟨infinitySection E U.1, infinitySection_mem E U.1⟩ (infinitySection_eq_restrict E U.1))
    (fun U => isRegular_infinitySection E U.1 U.2)

/-- **The divisor at infinity `D = Z(s)`**: the zero scheme of the section
`s ∈ Γ(P, 𝒪_P(1))` attached to `(0, 1)`. -/
abbrev infinityDivisor : (projectiveCompletion E).IdealSheafData :=
  Stacks.Divisors.zeroScheme (projectiveCompletion E) (Stacks.Chow.bundleTwist (completionModule E))
    (infinityTwistSection E)

/-- **`Z(s)` is the closed subscheme cut out by the divisor at infinity `i : 𝐏(ℰ) ⟶ P`.** -/
theorem infinityDivisor_eq_ker : infinityDivisor E = (infinityEmbedding E).ker :=
  zeroScheme_infinityTwistSection_eq_ker E

/-- **`s` is a regular section: `Z(s)` is an effective Cartier divisor**, so that
`𝒪_P(Z(s)) ≅ 𝒪_P(1)`. -/
theorem isEffectiveCartierDivisor_infinityDivisor :
    Stacks.Divisors.IsEffectiveCartierDivisor (infinityDivisor E) :=
  isEffectiveCartierDivisor_zeroScheme_infinityTwistSection E

/-- The lift of the closed immersion `i : 𝐏(ℰ) ⟶ P` through the closed subscheme `Z(s) ⟶ P` is
an isomorphism. -/
instance isIso_lift_infinityDivisor :
    IsIso (IsClosedImmersion.lift (infinityDivisor E).subschemeι (infinityEmbedding E)
      ((Scheme.IdealSheafData.ker_subschemeι _).trans (infinityDivisor_eq_ker E)).le) :=
  IsClosedImmersion.isIso_lift _ _
    ((Scheme.IdealSheafData.ker_subschemeι _).trans (infinityDivisor_eq_ker E))

/-- **`𝐏(ℰ) ≅ Z(s)` over `P`**: the divisor at infinity is the zero scheme of `s`. -/
def infinityDivisorIso : Stacks.Chow.bundle E ≅ (infinityDivisor E).subscheme :=
  asIso (IsClosedImmersion.lift (infinityDivisor E).subschemeι (infinityEmbedding E)
    ((Scheme.IdealSheafData.ker_subschemeι _).trans (infinityDivisor_eq_ker E)).le)

/-- The isomorphism `𝐏(ℰ) ≅ Z(s)` followed by the inclusion `Z(s) ⟶ P` is the embedding
`i : 𝐏(ℰ) ⟶ P`. -/
@[reassoc (attr := simp)]
theorem infinityDivisorIso_hom_subschemeι :
    (infinityDivisorIso E).hom ≫ (infinityDivisor E).subschemeι = infinityEmbedding E :=
  IsClosedImmersion.lift_fac _ _ _

/-- The inverse isomorphism `Z(s) ≅ 𝐏(ℰ)` followed by the embedding `i : 𝐏(ℰ) ⟶ P` is the
inclusion `Z(s) ⟶ P`. -/
@[reassoc (attr := simp)]
theorem infinityDivisorIso_inv_infinityEmbedding :
    (infinityDivisorIso E).inv ≫ infinityEmbedding E = (infinityDivisor E).subschemeι := by
  rw [Iso.inv_comp_eq, infinityDivisorIso_hom_subschemeι]

/-- **`Z(s)` is a relative effective Cartier divisor over `X`**, when `ℰ` has rank `n + 1`: it is
`𝐏(ℰ)`, which is flat over `X`. -/
theorem isRelativeEffectiveCartierDivisor_infinityDivisor (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] :
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor (projectiveCompletionProj E)
      (infinityDivisor E) := by
  refine ⟨isEffectiveCartierDivisor_infinityDivisor E, ?_⟩
  have hflat : Flat ((infinityDivisorIso E).inv ≫ Stacks.Chow.bundleProj E) :=
    @Flat.comp _ _ _ _ _ inferInstance (Stacks.Chow.flat_bundleProj E n)
  rw [← infinityEmbedding_comp_projectiveCompletionProj, ← Category.assoc,
    infinityDivisorIso_inv_infinityEmbedding] at hflat
  exact hflat

end Divisor

end Stacks.ProjectiveCompletion

end
