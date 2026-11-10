module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Completion.Basic
public import StacksFrontier.RingTheory.GradedAlgebra.SymmetricAway.LineChart
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraAffineSections
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleOfModule
public import StacksFrontier.AlgebraicGeometry.SymTwistChart.DegreeOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectSumSeparated

/-!
# The vector bundle over an affine open, as a chart of the projective completion

Let `ℰ` be a finite locally free module on a scheme `X` and `P = 𝐏(ℰ ⊕ 𝒪_X)` its projective
completion. Over an affine open `U` of `X`, the part of `P` over `U` is `Proj` of the graded ring
`Γ(U, Sym(ℰ ⊕ 𝒪_X)) = Sym_{Γ(X, U)}(Γ(ℰ, U) ⊕ Γ(X, U))`, and the degree-one element `T` attached to
the section `(0, 1)` of `ℰ ⊕ 𝒪_X` cuts out the standard open `D₊(T)`, which is
`Spec Sym_{Γ(X, U)}(Γ(ℰ, U)) = Spec Γ(U, Sym(ℰ))` by `Stacks.SymmetricAway.lineChartEquiv`. This
file builds the resulting morphism

  `Spec Γ(U, Sym(ℰ)) ⟶ P`

from the part of the vector bundle `Spec_X(Sym(ℰ))` over `U` to the projective completion.

## Main definitions

* `Stacks.ProjectiveCompletion.sectionsSplitting`: the splitting
  `Γ(ℰ ⊕ 𝒪_X, U) = Γ(ℰ, U) ⊕ Γ(X, U)` of the sections over an open.
* `Stacks.ProjectiveCompletion.infinitySection`: the degree-one element `T` of the graded ring of
  sections of `Sym(ℰ ⊕ 𝒪_X)` over an affine open.
* `Stacks.ProjectiveCompletion.chartRingEquiv`: the identification
  `Γ(U, Sym(ℰ)) ≃+* Γ(U, Sym(ℰ ⊕ 𝒪_X))_{(T)}`.
* `Stacks.ProjectiveCompletion.chartToCompletion`: the morphism `Spec Γ(U, Sym(ℰ)) ⟶ P`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj HomogeneousLocalization

universe u

namespace Stacks.ProjectiveCompletion

variable {X : Scheme.{u}} (E : X.Modules)

/-! ### Standard opens along a morphism of graded rings -/

section Away

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
  [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ) {s : A} {t : B} (hst : f s = t)

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
include hst in
/-- If `f s = t`, then `f` maps the powers of `s` into the powers of `t`. -/
theorem powers_le_comap_powers : Submonoid.powers s ≤ (Submonoid.powers t).comap f := by
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by simp [← hst]⟩

include hst in
/-- `Away.map` along `f`, read at an element equal to the image of `s` rather than at `f s` itself:
a fraction `a / sⁿ` goes to `f a / tⁿ`. -/
theorem map_away_mk {d : ℕ} (hs : s ∈ 𝒜 d) (ht : t ∈ ℬ d) (n : ℕ) (a : A)
    (ha : a ∈ 𝒜 (n • d)) :
    HomogeneousLocalization.map f (powers_le_comap_powers f hst) (Away.mk 𝒜 hs n a ha) =
      Away.mk ℬ ht n (f a) (GradedRingHom.map_mem f ha) := by
  subst hst
  exact Away.map_mk f s hs n a ha

include hst in
/-- **The standard open `D₊(t)` maps to `D₊(s)`** under `Proj.map f`, when `t = f s`: the square
of `AlgebraicGeometry.Proj.awayι_comp_map`, read at an element equal to `f s`. -/
@[reassoc]
theorem awayι_comp_map_of_eq (hf : HomogeneousIdeal.irrelevant ℬ ≤
      (HomogeneousIdeal.irrelevant 𝒜).map f) {i : ℕ} (hi : 0 < i) (hs : s ∈ 𝒜 i)
    (ht : t ∈ ℬ i) :
    Proj.awayι ℬ t ht hi ≫ Proj.map f hf =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map f
        (powers_le_comap_powers f hst))) ≫ Proj.awayι 𝒜 s hs hi := by
  subst hst
  exact Proj.awayι_comp_map f hf hi s hs

end Away

/-! ### The splitting of the sections -/

/-- **The splitting `Γ(ℰ ⊕ 𝒪_X, U) = Γ(ℰ, U) ⊕ Γ(X, U)`** of the sections over an open `U`, by
the sections of the two inclusions and the two projections; the line is spanned by the section
`(0, 1)`. -/
def sectionsSplitting (U : X.Opens) :
    Stacks.SymmetricAway.LineSplitting Γ(X, U) Γ(E, U) Γ(completionModule E, U) where
  j := Stacks.SymGraded.AffinePieces.sectionsLinearMap (completionInl E) U
  p := Stacks.SymGraded.AffinePieces.sectionsLinearMap (completionProjection E) U
  q :=
    { toFun x := (completionSnd E).app U x
      map_add' := map_add _
      map_smul' r x := Scheme.Modules.Hom.app_smul _ r x }
  t₀ := Scheme.Modules.Hom.app (completionInclusion E) U
    (unitModuleOne X U)
  p_j m := by
    change Scheme.Modules.Hom.app (biprod.inl ≫ biprod.fst : E ⟶ E) U m = m
    rw [biprod.inl_fst]
    rfl
  q_j m := by
    change Scheme.Modules.Hom.app (biprod.inl ≫ biprod.snd : E ⟶ Stacks.Ample.unitModule X) U m = 0
    rw [biprod.inl_snd]
    rfl
  p_t₀ := by
    change Scheme.Modules.Hom.app (biprod.inr ≫ biprod.fst : Stacks.Ample.unitModule X ⟶ E) U
      (unitModuleOne X U) = 0
    rw [biprod.inr_fst]
    rfl
  q_t₀ := by
    change Scheme.Modules.Hom.app (biprod.inr ≫ biprod.snd :
      Stacks.Ample.unitModule X ⟶ Stacks.Ample.unitModule X) U
        (unitModuleOne X U) = (1 : Γ(X, U))
    rw [biprod.inr_snd]
    rfl
  j_p_add_q_smul n := by
    have h := congrArg
      (fun φ : completionModule E ⟶ completionModule E => Scheme.Modules.Hom.app φ U n)
      (biprod.total : biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 _)
    refine Eq.trans ?_ h
    change _ = Scheme.Modules.Hom.app biprod.inl U (Scheme.Modules.Hom.app biprod.fst U n) +
      Scheme.Modules.Hom.app biprod.inr U (Scheme.Modules.Hom.app biprod.snd U n)
    congr 1
    refine Eq.trans (Scheme.Modules.Hom.app_smul biprod.inr _ _).symm ?_
    congr 1
    exact mul_one (M := Γ(X, U)) _

/-- The inclusion of `sectionsSplitting` is the map on sections of `completionInl`. -/
@[simp]
theorem sectionsSplitting_j (U : X.Opens) (m : Γ(E, U)) :
    (sectionsSplitting E U).j m = Scheme.Modules.Hom.app (completionInl E) U m := rfl

/-- The projection of `sectionsSplitting` is the map on sections of `completionProjection`. -/
@[simp]
theorem sectionsSplitting_p (U : X.Opens) (n : Γ(completionModule E, U)) :
    (sectionsSplitting E U).p n = Scheme.Modules.Hom.app (completionProjection E) U n := rfl

/-- The line coordinate of `sectionsSplitting` is the map on sections of `completionSnd`. -/
@[simp]
theorem sectionsSplitting_q (U : X.Opens) (n : Γ(completionModule E, U)) :
    (sectionsSplitting E U).q n = (show Γ(X, U) from Scheme.Modules.Hom.app
      (completionSnd E) U n) := rfl

/-- The line generator of `sectionsSplitting` is the section `(0, 1)` of `ℰ ⊕ 𝒪_X`. -/
theorem sectionsSplitting_t₀ (U : X.Opens) :
    (sectionsSplitting E U).t₀ =
      Scheme.Modules.Hom.app (completionInclusion E) U
        (unitModuleOne X U) := rfl

/-! ### The chart over an affine open -/

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- The graded algebra `Sym(ℰ ⊕ 𝒪_X)` whose relative `Proj` is the projective completion. -/
scoped notation "completionAlgebra " E:max =>
  schemeSheafGradedAlgebra (completionModule E) (Stacks.Chow.bundlePieces (completionModule E))

/-- **The degree-one element `T`** of `Γ(U, Sym(ℰ ⊕ 𝒪_X))` attached to the section `(0, 1)`. -/
def infinitySection (U : X.Opens) : (completionAlgebra E).sectionRing U :=
  DirectSum.of ((completionAlgebra E).sectionPieces U) 1
    ((Scheme.Modules.symmetricAlgebraGen X (completionModule E)).val.app (op U)
      (sectionsSplitting E U).t₀)

/-- The element `T` has degree one. -/
theorem infinitySection_mem (U : X.Opens) :
    infinitySection E U ∈ (completionAlgebra E).grading U 1 :=
  (completionAlgebra E).of_mem_grading U _

variable {E} {U : X.Opens} (hU : IsAffineOpen U)

/-- The identification of `Γ(U, Sym(ℰ ⊕ 𝒪_X))` with the symmetric algebra of the sections. -/
abbrev sectionRingEquiv :
    (completionAlgebra E).sectionRing U ≃+*
      SymmetricAlgebra Γ(X, U) Γ(completionModule E, U) :=
  Stacks.SymGraded.AffinePieces.symSectionRingEquiv (completionModule E) hU
    (Stacks.Chow.bundlePieces (completionModule E))

/-- `sectionRingEquiv` identifies the degree-`n` part of `Γ(U, Sym(ℰ ⊕ 𝒪_X))` with the `n`-th
symmetric power of `Γ(ℰ ⊕ 𝒪_X, U)`. -/
theorem sectionRingEquiv_mem_iff (n : ℕ) (x : (completionAlgebra E).sectionRing U) :
    sectionRingEquiv hU x ∈ SymPow.symmetricPower n Γ(X, U) Γ(completionModule E, U) ↔
      x ∈ (completionAlgebra E).grading U n :=
  Stacks.SymGraded.AffinePieces.mem_symmetricPower_symSectionRingEquiv _ hU _ n x

/-- `sectionRingEquiv` sends `T` to the degree-one generator attached to the section `(0, 1)`. -/
theorem sectionRingEquiv_infinitySection :
    sectionRingEquiv hU (infinitySection E U) =
      SymmetricAlgebra.ι _ _ (sectionsSplitting E U).t₀ :=
  Stacks.SymGraded.AffinePieces.symSectionRingEquiv_of_symmetricAlgebraGen _ hU _ _

/-- **`Γ(U, Sym(ℰ)) ≃+* Γ(U, Sym(ℰ ⊕ 𝒪_X))_{(T)}`**: the ring of sections of `Sym(ℰ)` over an
affine open is the degree-zero part of the localization of the graded ring of sections of
`Sym(ℰ ⊕ 𝒪_X)` at `T`. -/
def chartRingEquiv :
    (Scheme.Modules.symmetricAlgebraSheaf X E).right.obj.obj (op U) ≃+*
      Away ((completionAlgebra E).grading U) (infinitySection E U) :=
  (Stacks.SymAlgSections.symSectionsRingEquiv E hU).symm.trans
    (Stacks.SymmetricAway.lineChartEquiv (sectionsSplitting E U)
      ((completionAlgebra E).grading U) (sectionRingEquiv hU) (sectionRingEquiv_mem_iff hU)
      (infinitySection_mem E U) (sectionRingEquiv_infinitySection hU))

/-- **The chart `Spec Γ(U, Sym(ℰ)) ⟶ P`**: the standard open `D₊(T)` of the chart
`Proj Γ(U, Sym(ℰ ⊕ 𝒪_X))` of the projective completion over `U`, identified with
`Spec Γ(U, Sym(ℰ))` by `Stacks.ProjectiveCompletion.chartRingEquiv`. -/
def chartToCompletion :
    Spec ((Scheme.Modules.symmetricAlgebraSheaf X E).right.obj.obj (op U)) ⟶
      projectiveCompletion E :=
  Spec.map (CommRingCat.ofHom
      (R := Away ((completionAlgebra E).grading U) (infinitySection E U))
      (S := ((Scheme.Modules.symmetricAlgebraSheaf X E).right.obj.obj (op U) : CommRingCat))
      (chartRingEquiv hU).symm.toRingHom) ≫
    Proj.awayι ((completionAlgebra E).grading U) (infinitySection E U)
      (infinitySection_mem E U) one_pos ≫
    (relativeProj (completionAlgebra E)).chart U hU

/-! ### The degree-one generators of `Sym(ℰ)` in the ring of sections -/

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
variable (E) in
/-- The degree-one section of `Sym(ℰ)` attached to a section `m` of `ℰ`, in the ring of sections
of `Sym(ℰ)` as an algebra sheaf. -/
def symGenSection (U : X.Opens) (m : Γ(E, U)) :
    (Scheme.Modules.symmetricAlgebraSheaf X E).right.obj.obj (op U) :=
  (Scheme.Modules.symmetricAlgebra X E).ungradedIncl 1
    ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) m)

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
/-- The identification `Sym_{Γ(X, U)}(Γ(ℰ, U)) ≃+* Γ(U, Sym(ℰ))` sends a degree-one generator `m`
to the image of the degree-one section of `Sym(ℰ)` attached to `m`. -/
theorem symSectionsRingEquiv_ι [E.IsQuasicoherent] (m : Γ(E, U)) :
    Stacks.SymAlgSections.symSectionsRingEquiv E hU (SymmetricAlgebra.ι _ _ m) =
      symGenSection E U m := by
  have hdec : DirectSum.decompose (fun n : ℕ => SymPow.symmetricPower n Γ(X, U) Γ(E, U))
      (SymmetricAlgebra.ι Γ(X, U) Γ(E, U) m) =
      DirectSum.of (fun n : ℕ => (SymPow.symmetricPower n Γ(X, U) Γ(E, U) : Type u)) 1
        ⟨SymmetricAlgebra.ι Γ(X, U) Γ(E, U) m, by
          rw [SymPow.symmetricPower, pow_one]; exact LinearMap.mem_range_self _ m⟩ :=
    DirectSum.decompose_of_mem _ _
  change Stacks.RelativeSpec.totalSectionsRingEquiv X (Scheme.Modules.symmetricAlgebra X E)
      (Scheme.Modules.symmetricAlgebra_mul_comm X E) hU
      (Stacks.SymAlgSections.symPowersRingEquiv E hU (DirectSum.decompose _ _)) = _
  rw [hdec]
  change Stacks.RelativeSpec.totalSectionsRingEquiv X (Scheme.Modules.symmetricAlgebra X E)
      (Scheme.Modules.symmetricAlgebra_mul_comm X E) hU
      (Stacks.SymAlgSections.ofSymPowers E hU (DirectSum.of _ 1 _)) = _
  rw [Stacks.SymAlgSections.ofSymPowers_of, Stacks.SymAlgSections.symPowerIncl_apply,
    Stacks.SymAlgSections.pieceUnit_apply]
  rw [symGenSection, Stacks.SymGraded.AffinePieces.symmetricAlgebraGen_app_eq]
  rfl

/-! ### Compatibility with restriction -/

section Restriction

variable {U' : X.Opens} (hU' : IsAffineOpen U') (h : U ≤ U')

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
/-- The section `(0, 1)` of `ℰ ⊕ 𝒪_X` over `U'` restricts to the section `(0, 1)` over `U`. -/
theorem sectionsSplitting_t₀_restrict :
    (completionModule E).presheaf.map (homOfLE h).op (sectionsSplitting E U').t₀ =
      (sectionsSplitting E U).t₀ := by
  rw [sectionsSplitting_t₀, sectionsSplitting_t₀]
  refine (PresheafOfModules.naturality_apply (completionInclusion E).val
    (homOfLE h).op _).symm.trans ?_
  exact congrArg (Scheme.Modules.Hom.app (completionInclusion E) U) (unitModuleOne_restrict X h)

/-- Restriction of sections of `Sym(ℰ ⊕ 𝒪_X)` sends the degree-one element attached to a section
`n` of `ℰ ⊕ 𝒪_X` over `U'` to the one attached to the restriction of `n` to `U`. -/
private theorem resRingHom_of_symmetricAlgebraGen (n : Γ(completionModule E, U')) :
    (completionAlgebra E).resRingHom h
        (DirectSum.of ((completionAlgebra E).sectionPieces U') 1
          ((Scheme.Modules.symmetricAlgebraGen X (completionModule E)).val.app (op U') n)) =
      DirectSum.of ((completionAlgebra E).sectionPieces U) 1
        ((Scheme.Modules.symmetricAlgebraGen X (completionModule E)).val.app (op U)
          ((completionModule E).presheaf.map (homOfLE h).op n)) :=
  ((completionAlgebra E).resRingHom_of h _).trans
    (congrArg (DirectSum.of ((completionAlgebra E).sectionPieces U) 1)
      (PresheafOfModules.naturality_apply
        (Scheme.Modules.symmetricAlgebraGen X (completionModule E)).val (homOfLE h).op n).symm)

/-- **`T` is compatible with restriction.** -/
theorem res_infinitySection :
    (completionAlgebra E).res h (infinitySection E U') = infinitySection E U := by
  change (completionAlgebra E).resRingHom h (infinitySection E U') = _
  rw [infinitySection, resRingHom_of_symmetricAlgebraGen, sectionsSplitting_t₀_restrict]
  rfl

/-! ### Dehomogenization on sections -/

/-- **Dehomogenization on the sections over an affine open**: the ring map
`Γ(U, Sym(ℰ ⊕ 𝒪_X)) → Γ(U, Sym(ℰ))` setting `T = 1`. -/
def sectionsDehomogenize :
    (completionAlgebra E).sectionRing U →+*
      (Scheme.Modules.symmetricAlgebraSheaf X E).right.obj.obj (op U) :=
  (Stacks.SymAlgSections.symSectionsRingEquiv E hU).toRingHom.comp
    ((sectionsSplitting E U).dehomogenize.toRingHom.comp (sectionRingEquiv hU).toRingHom)

/-- `sectionsDehomogenize` is the dehomogenization of `sectionsSplitting`, transported along
`sectionRingEquiv` and `Stacks.SymAlgSections.symSectionsRingEquiv`. -/
theorem sectionsDehomogenize_apply (x : (completionAlgebra E).sectionRing U) :
    sectionsDehomogenize hU x = Stacks.SymAlgSections.symSectionsRingEquiv E hU
      ((sectionsSplitting E U).dehomogenize (sectionRingEquiv hU x)) := rfl

/-- The inverse of `chartRingEquiv` on a fraction `x / Tⁿ` is the dehomogenization of `x`. -/
theorem chartRingEquiv_symm_mk (n : ℕ) (x : (completionAlgebra E).sectionRing U)
    (hx : x ∈ (completionAlgebra E).grading U (n • 1)) :
    (chartRingEquiv hU).symm (Away.mk _ (infinitySection_mem E U) n x hx) =
      sectionsDehomogenize hU x := by
  change Stacks.SymAlgSections.symSectionsRingEquiv E hU
      ((Stacks.SymmetricAway.lineChartEquiv (sectionsSplitting E U)
        ((completionAlgebra E).grading U) (sectionRingEquiv hU) (sectionRingEquiv_mem_iff hU)
        (infinitySection_mem E U) (sectionRingEquiv_infinitySection hU)).symm
          (Away.mk _ (infinitySection_mem E U) n x hx)) = _
  rw [Stacks.SymmetricAway.lineChartEquiv_symm_mk]
  rfl

/-- Dehomogenization on the structure map. -/
theorem sectionsDehomogenize_strHom (r : Γ(X, U)) :
    sectionsDehomogenize hU ((completionAlgebra E).strHom U r) =
      ((Scheme.Modules.symmetricAlgebraSheaf X E).hom.hom.app (op U)).hom r := by
  have h1 : (completionAlgebra E).strHom U r =
      (sectionRingEquiv hU).symm (algebraMap Γ(X, U) _ r) :=
    (Stacks.SymTwistChart.symSectionRingEquiv_symm_algebraMap _ _ hU r).symm
  rw [sectionsDehomogenize_apply, h1, RingEquiv.apply_symm_apply, AlgHom.commutes]
  exact Stacks.SymAlgSections.symSectionsRingEquiv_algebraMap E hU r

/-- Dehomogenization on a degree-one generator: `n ↦ p(n) + q(n)`. -/
theorem sectionsDehomogenize_gen (n : Γ(completionModule E, U)) :
    sectionsDehomogenize hU (DirectSum.of ((completionAlgebra E).sectionPieces U) 1
        ((Scheme.Modules.symmetricAlgebraGen X (completionModule E)).val.app (op U) n)) =
      symGenSection E U ((sectionsSplitting E U).p n) +
        ((Scheme.Modules.symmetricAlgebraSheaf X E).hom.hom.app (op U)).hom
          ((sectionsSplitting E U).q n) := by
  rw [sectionsDehomogenize_apply,
    Stacks.SymGraded.AffinePieces.symSectionRingEquiv_of_symmetricAlgebraGen,
    Stacks.SymmetricAway.LineSplitting.dehomogenize_ι, map_add, symSectionsRingEquiv_ι,
    Stacks.SymAlgSections.symSectionsRingEquiv_algebraMap]

variable {U' : X.Opens} (hU' : IsAffineOpen U') (h : U ≤ U')

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
/-- The projection of `sectionsSplitting` commutes with restriction. -/
theorem sectionsSplitting_p_restrict (n : Γ(completionModule E, U')) :
    (sectionsSplitting E U).p ((completionModule E).presheaf.map (homOfLE h).op n) =
      E.presheaf.map (homOfLE h).op ((sectionsSplitting E U').p n) :=
  PresheafOfModules.naturality_apply (completionProjection E).val (homOfLE h).op n

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
/-- The line coordinate of `sectionsSplitting` commutes with restriction. -/
theorem sectionsSplitting_q_restrict (n : Γ(completionModule E, U')) :
    (sectionsSplitting E U).q ((completionModule E).presheaf.map (homOfLE h).op n) =
      X.presheaf.map (homOfLE h).op ((sectionsSplitting E U').q n) :=
  PresheafOfModules.naturality_apply
    (completionSnd E).val (homOfLE h).op n

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
/-- The structure map of `Sym(ℰ)` commutes with restriction. -/
theorem symmetricAlgebraSheaf_structure_restrict (r : Γ(X, U')) :
    ((Scheme.Modules.symmetricAlgebraSheaf X E).right.obj.map (homOfLE h).op).hom
        (((Scheme.Modules.symmetricAlgebraSheaf X E).hom.hom.app (op U')).hom r) =
      ((Scheme.Modules.symmetricAlgebraSheaf X E).hom.hom.app (op U)).hom
        (X.presheaf.map (homOfLE h).op r) :=
  (ConcreteCategory.congr_hom
    ((Scheme.Modules.symmetricAlgebraSheaf X E).hom.hom.naturality (homOfLE h).op) r).symm

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
/-- The degree-one generators of `Sym(ℰ)` commute with restriction. -/
theorem ungradedIncl_gen_restrict (m : Γ(E, U')) :
    ((Scheme.Modules.symmetricAlgebraSheaf X E).right.obj.map (homOfLE h).op).hom
        (symGenSection E U' m) =
      symGenSection E U (E.presheaf.map (homOfLE h).op m) := by
  refine ((Scheme.Modules.symmetricAlgebra X E).ungradedIncl_naturality (homOfLE h).op 1 _).trans
    ?_
  exact congrArg ((Scheme.Modules.symmetricAlgebra X E).ungradedIncl 1)
    (PresheafOfModules.naturality_apply
      (Scheme.Modules.symmetricAlgebraGen X E).val (homOfLE h).op m).symm

/-- **Dehomogenization commutes with restriction.** -/
theorem sectionsDehomogenize_res (a : (completionAlgebra E).sectionRing U') :
    sectionsDehomogenize hU ((completionAlgebra E).res h a) =
      ((Scheme.Modules.symmetricAlgebraSheaf X E).right.obj.map (homOfLE h).op).hom
        (sectionsDehomogenize hU' a) := by
  have key : (sectionsDehomogenize hU).comp (((completionAlgebra E).resRingHom h).comp
      (sectionRingEquiv hU').symm.toRingHom) =
      ((Scheme.Modules.symmetricAlgebraSheaf X E).right.obj.map (homOfLE h).op).hom.comp
        ((sectionsDehomogenize hU').comp (sectionRingEquiv hU').symm.toRingHom) := by
    refine SymmetricAlgebra.ringHom_ext (fun r => ?_) (fun n => ?_)
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [Stacks.SymTwistChart.symSectionRingEquiv_symm_algebraMap _ _ hU' r,
        (completionAlgebra E).resRingHom_strHom, sectionsDehomogenize_strHom,
        sectionsDehomogenize_strHom, symmetricAlgebraSheaf_structure_restrict]
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      have hn : (sectionRingEquiv hU').symm (SymmetricAlgebra.ι _ _ n) =
          DirectSum.of ((completionAlgebra E).sectionPieces U') 1
            ((Scheme.Modules.symmetricAlgebraGen X (completionModule E)).val.app (op U') n) :=
        (RingEquiv.symm_apply_eq _).2
          (Stacks.SymGraded.AffinePieces.symSectionRingEquiv_of_symmetricAlgebraGen _ hU' _ n).symm
      rw [hn]
      refine (congrArg (sectionsDehomogenize hU)
        (resRingHom_of_symmetricAlgebraGen h n)).trans ?_
      rw [sectionsDehomogenize_gen, sectionsDehomogenize_gen, map_add,
        sectionsSplitting_p_restrict, sectionsSplitting_q_restrict, ungradedIncl_gen_restrict,
        symmetricAlgebraSheaf_structure_restrict]
  have hx := RingHom.congr_fun key (sectionRingEquiv hU' a)
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply] at hx
  exact hx

/-- **The charts are compatible with restriction**: for affine opens `U ⊆ U'` of `X`, the chart
over `U` is the restriction of the chart over `U'`. -/
theorem specMap_comp_chartToCompletion :
    Spec.map ((Scheme.Modules.symmetricAlgebraSheaf X E).right.obj.map (homOfLE h).op) ≫
        chartToCompletion hU' = chartToCompletion hU := by
  have hres : HomogeneousIdeal.irrelevant ((completionAlgebra E).grading U) ≤
      (HomogeneousIdeal.irrelevant ((completionAlgebra E).grading U')).map
        ((completionAlgebra E).res h) :=
    Stacks.AlgebraicGeometry.RelativeProjGeneral.irrelevant_le_map_res_of_le_opens
      (completionAlgebra E).toGradedAlgebra (U := ⟨U, hU⟩) (V := ⟨U', hU'⟩) h
  have hdom := projInclusionDomain_eq_top (completionAlgebra E) U U' h hU hU'
  have hmap : projInclusionMap (completionAlgebra E) U U' h hU hU' =
      Proj.map ((completionAlgebra E).res h) hres :=
    Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map _ _ _ hres hdom
  have hring : CommRingCat.ofHom
      (R := Away ((completionAlgebra E).grading U') (infinitySection E U'))
      (S := ((Scheme.Modules.symmetricAlgebraSheaf X E).right.obj.obj (op U') : CommRingCat))
      (chartRingEquiv hU').symm.toRingHom ≫
        (Scheme.Modules.symmetricAlgebraSheaf X E).right.obj.map (homOfLE h).op =
      CommRingCat.ofHom (HomogeneousLocalization.map ((completionAlgebra E).res h)
          (powers_le_comap_powers _ (res_infinitySection h))) ≫
        CommRingCat.ofHom
          (R := Away ((completionAlgebra E).grading U) (infinitySection E U))
          (S := ((Scheme.Modules.symmetricAlgebraSheaf X E).right.obj.obj (op U) : CommRingCat))
          (chartRingEquiv hU).symm.toRingHom := by
    ext x
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (infinitySection_mem E U') x
    change ((Scheme.Modules.symmetricAlgebraSheaf X E).right.obj.map (homOfLE h).op).hom
        ((chartRingEquiv hU').symm (Away.mk _ (infinitySection_mem E U') n a ha)) =
      (chartRingEquiv hU).symm (HomogeneousLocalization.map ((completionAlgebra E).res h)
          (powers_le_comap_powers _ (res_infinitySection h))
          (Away.mk _ (infinitySection_mem E U') n a ha))
    rw [map_away_mk _ (res_infinitySection h) (infinitySection_mem E U') (infinitySection_mem E U),
      chartRingEquiv_symm_mk, chartRingEquiv_symm_mk]
    exact (sectionsDehomogenize_res hU hU' h a).symm
  have haway := awayι_comp_map_of_eq ((completionAlgebra E).res h) (res_infinitySection h) hres
    one_pos (infinitySection_mem E U') (infinitySection_mem E U)
  rw [chartToCompletion, chartToCompletion,
    ← (relativeProj (completionAlgebra E)).chart_transition U U' h hU hU', hmap]
  calc _ = (Spec.map ((Scheme.Modules.symmetricAlgebraSheaf X E).right.obj.map (homOfLE h).op) ≫
          Spec.map (CommRingCat.ofHom
            (R := Away ((completionAlgebra E).grading U') (infinitySection E U'))
            (S := ((Scheme.Modules.symmetricAlgebraSheaf X E).right.obj.obj (op U') :
              CommRingCat)) (chartRingEquiv hU').symm.toRingHom)) ≫
          Proj.awayι ((completionAlgebra E).grading U') (infinitySection E U')
            (infinitySection_mem E U') one_pos ≫
          (relativeProj (completionAlgebra E)).chart U' hU' := (Category.assoc _ _ _).symm
    _ = (Spec.map (CommRingCat.ofHom
            (R := Away ((completionAlgebra E).grading U) (infinitySection E U))
            (S := ((Scheme.Modules.symmetricAlgebraSheaf X E).right.obj.obj (op U) :
              CommRingCat)) (chartRingEquiv hU).symm.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map ((completionAlgebra E).res h)
            (powers_le_comap_powers _ (res_infinitySection h))))) ≫
          Proj.awayι ((completionAlgebra E).grading U') (infinitySection E U')
            (infinitySection_mem E U') one_pos ≫
          (relativeProj (completionAlgebra E)).chart U' hU' := by
      rw [← Spec.map_comp, ← Spec.map_comp, hring]
    _ = _ := by
      rw [Category.assoc, ← Category.assoc (Spec.map _) (Proj.awayι _ _ _ _), ← haway,
        Category.assoc]
      rfl

end Restriction

end Stacks.ProjectiveCompletion

end
