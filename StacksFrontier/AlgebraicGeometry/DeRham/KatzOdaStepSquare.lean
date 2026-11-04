module

public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCoefficientSummand
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceStepSquaresProof

/-!
# The step-square compatibility of the action of a local form, and the Katz–Oda rule

For `f : X ⟶ Y` quasi-compact, quasi-separated and smooth over `g : Y ⟶ S`, `U ⊆ Y` open and `ω`
a `p`-form on `U`, this file proves `Stacks.DeRhamSmooth.WedgeStepSquare` unconditionally
(`Stacks.DeRhamSmooth.wedgeStepSquare`): through the identification of Section 0FMK of the graded
pieces at the cuts `k` and `k + p`, the action of `ρ(f⁻¹ω)` on `gr^kΩ^•_{X/S}|_{f⁻¹(U)}` is
`(ω ∧ -) ⊗ 1`. Degree by degree, both sides are read on the epimorphism
`Stacks.DeRhamSmooth.coefficientSummandToTarget` out of `f^{-1}(j_!(Ω^k|_U)) ⊗ Ω^q_{X/S}`, where
they become projections onto the graded piece of the wedge summands of the step, which agree by
`Stacks.DeRhamSmooth.restrictedLeftMulCochain_comp_summand_pulledBack`.

With it, `Stacks.DeRhamSmooth.isKatzOdaLeibniz_of_wedgeStepSquare` gives the Katz–Oda rule for the
first differential in the flat case of [Stacks, Tag 0FMN] with no hypothesis left
(`Stacks.DeRhamSmooth.isKatzOdaLeibniz_deRhamFirstPageFlatDifferential`).

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
* [Stacks Project, Section 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage


universe u

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf
attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax

namespace Stacks.DeRhamSmooth

open Stacks.DeRhamDirectImage

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)


/-! ### The components of the identification of Section 0FMK -/

/-- **Above the cut the identification of Section 0FMK is the degreewise comparison**
`Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX`. -/
theorem gradedPieceIsoGradedTargetComplexOfStepSquares_hom_f_succ [Smooth f] (k j : ℕ)
    (hcut hup) :
    (gradedPieceIsoGradedTargetComplexOfStepSquares f g k hcut hup).hom.f ((k + 1 + j : ℕ) : ℤ) =
      (gradedPieceXIsoGradedTargetX f g k j).hom :=
  congrArg Iso.hom (CochainComplex.isoXOfGE_eq _ _ _ _ _ _ (j + 1) _ (by push_cast; ring))

/-- **In the degree of the cut the identification of Section 0FMK is the comparison at the cut**
`Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetXAtCut`. -/
theorem gradedPieceIsoGradedTargetComplexOfStepSquares_hom_f_cut [Smooth f] (k : ℕ)
    (hcut hup) :
    (gradedPieceIsoGradedTargetComplexOfStepSquares f g k hcut hup).hom.f (k : ℤ) =
      (gradedPieceXIsoGradedTargetXAtCut f g k).hom :=
  congrArg Iso.hom (CochainComplex.isoXOfGE_eq _ _ _ _ _ _ 0 _ (by push_cast; ring))

/-- Cancelling an isomorphism after a factorization, at generic objects. -/
theorem comp_eq_comp_of_comp_comp_eq {C : Type*} [Category C] {P F G T : C} (z : P ⟶ F)
    (π : F ⟶ G) (s : G ⟶ T) (s' : T ⟶ G) (E : P ⟶ T) (h : z ≫ π ≫ s = E) (hs : s ≫ s' = 𝟙 G) :
    z ≫ π = E ≫ s' := by
  rw [← h, Category.assoc, Category.assoc, hs, Category.comp_id]

/-- Cancelling an isomorphism after a factorization, at generic objects. -/
theorem comp_eq_comp_inv_of_comp_comp_hom_eq {C : Type*} [Category C] {P F G T : C} (z : P ⟶ F)
    (ι : F ⟶ G) (e : G ≅ T) (s : P ⟶ T) (h : z ≫ (ι ≫ e.hom) = s) : z ≫ ι = s ≫ e.inv := by
  rw [← h]
  simp

/-- The components of an isomorphism of complexes are inverse to each other. -/
theorem hom_f_comp_inv_f {C : Type*} [Category C] {_ : Limits.HasZeroMorphisms C} {ι : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (e : K ≅ L) (n : ι) :
    e.hom.f n ≫ e.inv.f n = 𝟙 (K.X n) := by
  rw [← HomologicalComplex.comp_f, e.hom_inv_id, HomologicalComplex.id_f]

/-- **The step factorization above the cut**: an epimorphism `z` onto the degree-`n` term of the
`k`-th step, `n = k + 1 + j`, through which the projection onto the graded piece is the summand
read in the target complex followed by the inverse of the identification of Section 0FMK, and
the inclusion of the step is the `(k, j + 1)` summand of the wedge map. -/
theorem exists_stepFactorization_succ [Smooth f] (k j : ℕ) (hcut hup) :
    ∃ Z : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).obj
          ((_root_.pullback (relativeBase f g)).obj ((_root_.pushforward (toInverseImageBase g)).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))))).obj
        ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ))) ⟶
        ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).X ((k + 1 + j : ℕ) : ℤ),
      Z ≫ (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
          (deRhamSmoothFiltration f g)).f ((k + 1 + j : ℕ) : ℤ) =
        coefficientSummandToTarget f g k
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)) (j + 1)
            ((k + 1 + j : ℕ) : ℤ) (by push_cast; ring) ≫
          (gradedPieceIsoGradedTargetComplexOfStepSquares f g k hcut hup).inv.f
            ((k + 1 + j : ℕ) : ℤ) ∧
      Z ≫ ((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f ((k + 1 + j : ℕ) : ℤ) =
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
              ((Stacks.DeRhamPullback.deRhamPullbackChain f g).f k)).app
            ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras (f ≫ g)))).X (j + 1)) ≫
          AlgebraicGeometry.SheafOfModules.exteriorProductComponent
            (Scheme.Hom.deRhamAlgebras (f ≫ g)) k (j + 1) ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras (f ≫ g)))).XIsoOfEq
              (add_add_one_eq_add_one_add k j)).hom) ≫
          (deRhamSmoothExtendXIso f g (k + 1 + j)).inv := by
  obtain ⟨z, -, hZ⟩ := exists_epi_comp_ι_app_f_eq_summand f g k j
  have h1 := comp_grMapπ_f_comp_gradedPieceXIsoGradedTargetX_hom f g k j z hZ
  rw [← gradedPieceIsoGradedTargetComplexOfStepSquares_hom_f_succ f g k j hcut hup] at h1
  exact ⟨z, comp_eq_comp_of_comp_comp_eq _ _ _ _ _ h1 (hom_f_comp_inv_f _ _),
    comp_eq_comp_inv_of_comp_comp_hom_eq _ _ _ _ hZ⟩

/-- The factorization at the cut, at generic objects. -/
theorem cut_comp_comp_eq {C : Type*} [Category C] {P W₀ W₁ W₂ F G T A₁ A₂ A₃ : C}
    (w : P ⟶ W₀) (a : F ≅ W₀) (π : F ⟶ G) (s : G ⟶ T) (r₁ : W₀ ⟶ W₁) (r₂ : W₁ ⟶ W₂)
    (r₃ : W₂ ⟶ T) (e₁ : P ⟶ A₁) (e₂ : A₁ ⟶ A₂) (e₃ : A₂ ⟶ A₃) (e₄ : A₃ ⟶ W₂)
    (hπ : π ≫ s = a.hom ≫ r₁ ≫ r₂ ≫ r₃) (hw : w ≫ r₁ ≫ r₂ = e₁ ≫ e₂ ≫ e₃ ≫ e₄) :
    (w ≫ a.inv) ≫ π ≫ s = e₁ ≫ e₂ ≫ e₃ ≫ e₄ ≫ r₃ := by
  rw [hπ, Category.assoc, Iso.inv_hom_id_assoc, ← reassoc_of% hw]

/-- **The step factorization at the cut**: the surjection of Section 50.12 at the cut, carried
into the degree-`k` term of the `k`-th step, through which the projection onto the graded piece is
the summand read in the target complex followed by the inverse of the identification of Section
0FMK, and the inclusion of the step is the `(k, 0)` summand of the wedge map. -/
theorem exists_stepFactorization_cut [Smooth f] (k : ℕ) (hcut hup) :
    ∃ Z : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).obj
          ((_root_.pullback (relativeBase f g)).obj ((_root_.pushforward (toInverseImageBase g)).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))))).obj
        ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 : ℕ) : ℤ))) ⟶
        ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).X ((k : ℕ) : ℤ),
      Z ≫ (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
          (deRhamSmoothFiltration f g)).f ((k : ℕ) : ℤ) =
        coefficientSummandToTarget f g k
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)) 0
            ((k : ℕ) : ℤ) (by push_cast; ring) ≫
          (gradedPieceIsoGradedTargetComplexOfStepSquares f g k hcut hup).inv.f ((k : ℕ) : ℤ) ∧
      Z ≫ ((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f ((k : ℕ) : ℤ) =
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
              ((Stacks.DeRhamPullback.deRhamPullbackChain f g).f k)).app
            ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras (f ≫ g)))).X 0) ≫
          AlgebraicGeometry.SheafOfModules.exteriorProductComponent
            (Scheme.Hom.deRhamAlgebras (f ≫ g)) k 0 ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras (f ≫ g)))).XIsoOfEq (Nat.add_zero k)).hom) ≫
          (deRhamSmoothExtendXIso f g k).inv := by
  have h1 := cut_comp_comp_eq
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map (pulledBackFormsComparison f g k)).app
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
        g)))).X 0) ≫ Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
        S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)) ((pulledBackDifferentialsAlgebras f g).exteriorPower k) ((Scheme.Hom.deRhamAlgebras (f ≫
        g)).exteriorPower 0)))
    (filtrationXIsoCutWedgeSource f g k) _ _ _ _ _ _ _ _ _
    (grMapπ_f_gradedPieceXIsoGradedTargetXAtCut_hom f g k)
    (cutSource_comp_cutWedgeSource_comp_mixedTensor_inv f g k)
  rw [← gradedPieceIsoGradedTargetComplexOfStepSquares_hom_f_cut f g k hcut hup] at h1
  exact ⟨_, comp_eq_comp_of_comp_comp_eq _ _ _ _ _ h1 (hom_f_comp_inv_f _ _),
    comp_eq_comp_inv_of_comp_comp_hom_eq _ _ _ _
      (cutSource_comp_inv_comp_ι_app_f_comp_extendXIso_hom f g k)⟩

/-- **The step factorizations, transported to another name of their degree.** -/
theorem stepFactorization_transport {C : Type*} [Category C] {_ : Limits.HasZeroMorphisms C}
    {K L Fc Ω : CochainComplex C ℤ} (π : Fc ⟶ K) (s : L ⟶ K)
    (ι : Fc ⟶ Ω) {P : C} (n₀ : ℤ) (Z : P ⟶ Fc.X n₀)
    (E : ∀ e : ℤ, n₀ = e → (P ⟶ L.X e)) (A : P ⟶ Ω.X n₀)
    (hπ : Z ≫ π.f n₀ = E n₀ rfl ≫ s.f n₀) (hι : Z ≫ ι.f n₀ = A) (e : ℤ) (he : n₀ = e) :
    (Z ≫ (Fc.XIsoOfEq he).hom) ≫ π.f e = E e he ≫ s.f e ∧
      (Z ≫ (Fc.XIsoOfEq he).hom) ≫ ι.f e = A ≫ (Ω.XIsoOfEq he).hom := by
  subst he
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
  exact ⟨hπ, hι⟩

/-- **The step-square compatibility in one degree, at generic objects.** After the epimorphism
`ρ(Eε)` the two sides become the projections onto the graded piece of two morphisms into the
step, which agree after the monomorphism `ρ(ι₃)` by `hcore`. -/
theorem map_comp_comp_eq_of_stepFactorizations {C D : Type*} [Category C] [Category D]
    (ρ : C ⥤ D) {Src T₀ T₁ T₂ T₃ G₁ G₃ P P' F₁ F₃ Ω₁ Ω₃ : C}
    (Eε : Src ⟶ T₀) (tε : T₀ ⟶ T₁) (tα : T₀ ⟶ T₂) (sh : T₂ ⟶ T₃) (s₁ : T₁ ⟶ G₁)
    (s₃ : T₃ ⟶ G₃) (E₁ : P ⟶ T₁) (E₂ : P' ⟶ T₂) (E₃ : P' ⟶ T₃) (nε : Src ⟶ P)
    (nα : Src ⟶ P') (Z₁ : P ⟶ F₁) (π₁ : F₁ ⟶ G₁) (Z₃ : P' ⟶ F₃) (π₃ : F₃ ⟶ G₃)
    (ι₁ : F₁ ⟶ Ω₁) (ι₃ : F₃ ⟶ Ω₃) (μ : ρ.obj G₁ ⟶ ρ.obj G₃) (act : ρ.obj F₁ ⟶ ρ.obj F₃)
    (w : ρ.obj Ω₁ ⟶ ρ.obj Ω₃) (c : ρ.obj G₃ ⟶ ρ.obj G₃)
    (hepi : Epi (ρ.map Eε)) (hmono : Mono (ρ.map ι₃))
    (h₁ : Eε ≫ tε = nε ≫ E₁) (h₂ : Eε ≫ tα = nα ≫ E₂) (h₃ : E₂ ≫ sh = E₃)
    (hZ₁ : Z₁ ≫ π₁ = E₁ ≫ s₁) (hZ₃ : Z₃ ≫ π₃ = E₃ ≫ s₃)
    (hμ : ρ.map π₁ ≫ μ = act ≫ ρ.map π₃) (hact : act ≫ ρ.map ι₃ = ρ.map ι₁ ≫ w)
    (hcore : ρ.map (nε ≫ Z₁ ≫ ι₁) ≫ w = ρ.map (nα ≫ Z₃ ≫ ι₃)) (hc : c = 𝟙 _) :
    ρ.map (tε ≫ s₁) ≫ μ = ρ.map (tα ≫ sh ≫ s₃) ≫ c := by
  subst hc
  have key : ρ.map nε ≫ ρ.map Z₁ ≫ act = ρ.map nα ≫ ρ.map Z₃ := by
    refine hmono.right_cancellation _ _ ?_
    simpa only [Functor.map_comp, Category.assoc, hact] using hcore
  refine hepi.left_cancellation _ _ ?_
  rw [Category.comp_id, ← ρ.map_comp_assoc, ← ρ.map_comp, reassoc_of% h₁, ← hZ₁,
    reassoc_of% h₂, reassoc_of% h₃, ← hZ₃]
  simp only [Functor.map_comp, Category.assoc, hμ, reassoc_of% key]

open CochainComplex.HomComplex in
/-- A component of a cochain, at another name of its target degree. -/
theorem cochain_v_eq_v_comp_map_XIsoOfEq {C D : Type*} [Category C] {_ : Preadditive C}
    [Category D] {_ : Preadditive D} (Φ : C ⥤ D) {_ : Φ.PreservesZeroMorphisms}
    (K : CochainComplex C ℤ) {p : ℤ}
    (γ : Cochain ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) p)
    (n n' e : ℤ) (h : n + p = n') (h' : n + p = e) (he : n' = e) :
    γ.v n e h' = γ.v n n' h ≫ Φ.map (K.XIsoOfEq he).hom := by
  subst he
  simp

/-- The paste of the core equation with a transport of the target degree, at generic objects. -/
theorem map_comp_comp_eq_of_core {C D : Type*} [Category C] [Category D] (Φ : C ⥤ D)
    {Q P P' F₁ F₃ A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ B₅ : C} (nε : Q ⟶ P) (nα : Q ⟶ P')
    (Z₁ : P ⟶ F₁) (ι₁ : F₁ ⟶ A₄) (Z₃ : P' ⟶ F₃) (ι₃ : F₃ ⟶ B₅)
    (a₁ : P ⟶ A₁) (a₂ : A₁ ⟶ A₂) (a₃ : A₂ ⟶ A₃) (a₄ : A₃ ⟶ A₄)
    (b₁ : P' ⟶ B₁) (b₂ : B₁ ⟶ B₂) (b₃ : B₂ ⟶ B₃) (b₄ : B₃ ⟶ B₄) (x : B₄ ⟶ B₅)
    (γ : Φ.obj A₄ ⟶ Φ.obj B₄) (γ' : Φ.obj A₄ ⟶ Φ.obj B₅)
    (h₁ : Z₁ ≫ ι₁ = (a₁ ≫ a₂ ≫ a₃) ≫ a₄) (h₃ : Z₃ ≫ ι₃ = ((b₁ ≫ b₂ ≫ b₃) ≫ b₄) ≫ x)
    (hγ : γ' = γ ≫ Φ.map x)
    (hcore : Φ.map (nε ≫ a₁ ≫ a₂ ≫ a₃ ≫ a₄) ≫ γ = Φ.map (nα ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄)) :
    Φ.map (nε ≫ Z₁ ≫ ι₁) ≫ γ' = Φ.map (nα ≫ Z₃ ≫ ι₃) := by
  rw [h₁, h₃, hγ]
  simp only [Category.assoc] at hcore ⊢
  rw [← Category.assoc, hcore]
  simp only [Functor.map_comp, Category.assoc]

/-- **The step factorization above the cut `k + p`, read at the degree `(k + 1 + j) + p`.** -/
theorem exists_stepFactorization_succ_shift [Smooth f] (k p j : ℕ) :
    ∃ Z : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).obj
          ((_root_.pullback (relativeBase f g)).obj ((_root_.pushforward (toInverseImageBase g)).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g ((k + p : ℕ) : ℤ))))).obj
        ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ))) ⟶
        ((deRhamSmoothFiltration f g).filtration.obj (op ((k + p : ℕ) : ℤ))).X
          (((k + 1 + j : ℕ) : ℤ) + (p : ℤ)),
      Z ≫ (FilteredObject.grMapπ (FilteredObject.succHom ((k + p : ℕ) : ℤ))
          (deRhamSmoothFiltration f g)).f (((k + 1 + j : ℕ) : ℤ) + (p : ℤ)) =
        coefficientSummandToTarget f g (k + p)
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g ((k + p : ℕ) : ℤ)) (j + 1)
            (((k + 1 + j : ℕ) : ℤ) + (p : ℤ)) (by push_cast; ring) ≫
          (gradedPieceIsoGradedTargetComplexOfStepSquares f g (k + p) (stepSquares f g (k + p)).1
            (stepSquares f g (k + p)).2).inv.f (((k + 1 + j : ℕ) : ℤ) + (p : ℤ)) ∧
      Z ≫ ((deRhamSmoothFiltration f g).filtration.ι.app (op ((k + p : ℕ) : ℤ))).f
          (((k + 1 + j : ℕ) : ℤ) + (p : ℤ)) =
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
              ((Stacks.DeRhamPullback.deRhamPullbackChain f g).f (k + p))).app
            ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras (f ≫ g)))).X (j + 1)) ≫
          AlgebraicGeometry.SheafOfModules.exteriorProductComponent
            (Scheme.Hom.deRhamAlgebras (f ≫ g)) (k + p) (j + 1) ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras (f ≫ g)))).XIsoOfEq
              (add_add_one_eq_add_one_add (k + p) j)).hom) ≫
          (deRhamSmoothExtendXIso f g (k + p + 1 + j)).inv) ≫
          ((deRhamSmoothFiltration f g).X.XIsoOfEq
            (show ((k + p + 1 + j : ℕ) : ℤ) = ((k + 1 + j : ℕ) : ℤ) + (p : ℤ) by
              push_cast; ring)).hom :=
  (exists_stepFactorization_succ f g (k + p) j (stepSquares f g (k + p)).1
      (stepSquares f g (k + p)).2).elim fun Z hZ =>
    ⟨_, stepFactorization_transport _ _ _ ((k + p + 1 + j : ℕ) : ℤ) Z
      (fun e he => coefficientSummandToTarget f g (k + p)
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g ((k + p : ℕ) : ℤ)) (j + 1) e
        (by subst he; push_cast; ring)) _ hZ.1 hZ.2 (((k + 1 + j : ℕ) : ℤ) + (p : ℤ))
      (by push_cast; ring)⟩

/-- **The step factorization at the cut `k + p`, read at the degree `k + p`.** -/
theorem exists_stepFactorization_cut_shift [Smooth f] (k p : ℕ) :
    ∃ Z : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).obj
          ((_root_.pullback (relativeBase f g)).obj ((_root_.pushforward (toInverseImageBase g)).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g ((k + p : ℕ) : ℤ))))).obj
        ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 : ℕ) : ℤ))) ⟶
        ((deRhamSmoothFiltration f g).filtration.obj (op ((k + p : ℕ) : ℤ))).X
          ((k : ℤ) + (p : ℤ)),
      Z ≫ (FilteredObject.grMapπ (FilteredObject.succHom ((k + p : ℕ) : ℤ))
          (deRhamSmoothFiltration f g)).f ((k : ℤ) + (p : ℤ)) =
        coefficientSummandToTarget f g (k + p)
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g ((k + p : ℕ) : ℤ)) 0
            ((k : ℤ) + (p : ℤ)) (by push_cast; ring) ≫
          (gradedPieceIsoGradedTargetComplexOfStepSquares f g (k + p) (stepSquares f g (k + p)).1
            (stepSquares f g (k + p)).2).inv.f ((k : ℤ) + (p : ℤ)) ∧
      Z ≫ ((deRhamSmoothFiltration f g).filtration.ι.app (op ((k + p : ℕ) : ℤ))).f
          ((k : ℤ) + (p : ℤ)) =
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
              ((Stacks.DeRhamPullback.deRhamPullbackChain f g).f (k + p))).app
            ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras (f ≫ g)))).X 0) ≫
          AlgebraicGeometry.SheafOfModules.exteriorProductComponent
            (Scheme.Hom.deRhamAlgebras (f ≫ g)) (k + p) 0 ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras (f ≫ g)))).XIsoOfEq
              (Nat.add_zero (k + p))).hom) ≫
          (deRhamSmoothExtendXIso f g (k + p)).inv) ≫
          ((deRhamSmoothFiltration f g).X.XIsoOfEq
            (show ((k + p : ℕ) : ℤ) = (k : ℤ) + (p : ℤ) by push_cast; ring)).hom :=
  (exists_stepFactorization_cut f g (k + p) (stepSquares f g (k + p)).1
      (stepSquares f g (k + p)).2).elim fun Z hZ =>
    ⟨_, stepFactorization_transport _ _ _ ((k + p : ℕ) : ℤ) Z
      (fun e he => coefficientSummandToTarget f g (k + p)
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g ((k + p : ℕ) : ℤ)) 0 e
        (by subst he; push_cast; ring)) _ hZ.1 hZ.2 ((k : ℤ) + (p : ℤ))
      (by push_cast; ring)⟩

/-- **The core of the step-square compatibility above the cut**: on the step factorizations at the
cuts `k` and `k + p`, left multiplication by `ρ(f⁻¹ω)` carries the summand of `f⁻¹(j_!(Ω^k|_U))`
read through the counit to the summand read through `(ω ∧ -)♭`. -/
theorem restrictedLeftMulCochain_comp_stepFactorization_succ (U : Y.Opens) (p : ℕ)
    (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U)) (k j : ℕ)
    (Z₁ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).obj
          ((_root_.pullback (relativeBase f g)).obj ((_root_.pushforward (toInverseImageBase g)).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))))).obj
        ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ))) ⟶
        ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).X ((k + 1 + j : ℕ) : ℤ))
    (Z₃ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).obj
          ((_root_.pullback (relativeBase f g)).obj ((_root_.pushforward (toInverseImageBase g)).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g ((k + p : ℕ) : ℤ))))).obj
        ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ))) ⟶
        ((deRhamSmoothFiltration f g).filtration.obj (op ((k + p : ℕ) : ℤ))).X
          (((k + 1 + j : ℕ) : ℤ) + (p : ℤ)))
    (h₁ : Z₁ ≫ ((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f
          ((k + 1 + j : ℕ) : ℤ) =
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
              ((Stacks.DeRhamPullback.deRhamPullbackChain f g).f k)).app
            ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras (f ≫ g)))).X (j + 1)) ≫
          AlgebraicGeometry.SheafOfModules.exteriorProductComponent
            (Scheme.Hom.deRhamAlgebras (f ≫ g)) k (j + 1) ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras (f ≫ g)))).XIsoOfEq
              (add_add_one_eq_add_one_add k j)).hom) ≫
          (deRhamSmoothExtendXIso f g (k + 1 + j)).inv))
    (h₃ : Z₃ ≫ ((deRhamSmoothFiltration f g).filtration.ι.app (op ((k + p : ℕ) : ℤ))).f
          (((k + 1 + j : ℕ) : ℤ) + (p : ℤ)) =
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
              ((Stacks.DeRhamPullback.deRhamPullbackChain f g).f (k + p))).app
            ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras (f ≫ g)))).X (j + 1)) ≫
          AlgebraicGeometry.SheafOfModules.exteriorProductComponent
            (Scheme.Hom.deRhamAlgebras (f ≫ g)) (k + p) (j + 1) ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras (f ≫ g)))).XIsoOfEq
              (add_add_one_eq_add_one_add (k + p) j)).hom) ≫
          (deRhamSmoothExtendXIso f g (k + p + 1 + j)).inv) ≫
          ((deRhamSmoothFiltration f g).X.XIsoOfEq
            (show ((k + p + 1 + j : ℕ) : ℤ) = ((k + 1 + j : ℕ) : ℤ) + (p : ℤ) by
              push_cast; ring)).hom) :
    (moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U)).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
            ((_root_.pullback (relativeBase f g)).map
              ((_root_.pushforward (toInverseImageBase g)).map
                ((restrictAdjunction U).counit.app
                  (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))))).app
            ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
              (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ))) ≫
          Z₁ ≫ ((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f
            ((k + 1 + j : ℕ) : ℤ)) ≫
      (SheafOfModules.DifferentialGradedAlgebra.restrictedLeftMulCochain
        (X := inverseImageBase (f ≫ g)) (pulledBackOpen f g U) (deRhamDGA f g)
        (pulledBackForm f g U p ω)).v ((k + 1 + j : ℕ) : ℤ) (((k + 1 + j : ℕ) : ℤ) + (p : ℤ)) rfl =
    (moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U)).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
            ((_root_.pullback (relativeBase f g)).map
              ((_root_.pushforward (toInverseImageBase g)).map
                (((restrictAdjunction U).homEquiv _ _).symm
                  (restrictedFormsWedge g U ω (k : ℤ) ((k + p : ℕ) : ℤ)
                    (by push_cast; ring)))))).app
            ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
              (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ))) ≫
          Z₃ ≫ ((deRhamSmoothFiltration f g).filtration.ι.app (op ((k + p : ℕ) : ℤ))).f
            (((k + 1 + j : ℕ) : ℤ) + (p : ℤ))) :=
  map_comp_comp_eq_of_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₃
    (cochain_v_eq_v_comp_map_XIsoOfEq _ _ _ _ _ _ _ _ _)
    (restrictedLeftMulCochain_comp_summand_pulledBack f g U p k (k + p) (j + 1)
      (k + 1 + j) (k + p + 1 + j) (by omega) (by omega) (by omega) ω
      ((restrictAdjunction U).counit.app
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))
      (((restrictAdjunction U).homEquiv _ _).symm
        (restrictedFormsWedge g U ω (k : ℤ) ((k + p : ℕ) : ℤ) (by push_cast; ring)))
      (moduleRestriction_map_homEquiv_symm U _))

/-- **The core of the step-square compatibility at the cut**: on the step factorizations at the
cuts `k` and `k + p`, left multiplication by `ρ(f⁻¹ω)` carries the summand of `f⁻¹(j_!(Ω^k|_U))`
read through the counit to the summand read through `(ω ∧ -)♭`. -/
theorem restrictedLeftMulCochain_comp_stepFactorization_cut (U : Y.Opens) (p : ℕ)
    (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U)) (k : ℕ)
    (Z₁ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).obj
          ((_root_.pullback (relativeBase f g)).obj ((_root_.pushforward (toInverseImageBase g)).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))))).obj
        ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 : ℕ) : ℤ))) ⟶
        ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).X ((k : ℕ) : ℤ))
    (Z₃ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).obj
          ((_root_.pullback (relativeBase f g)).obj ((_root_.pushforward (toInverseImageBase g)).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g ((k + p : ℕ) : ℤ))))).obj
        ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 : ℕ) : ℤ))) ⟶
        ((deRhamSmoothFiltration f g).filtration.obj (op ((k + p : ℕ) : ℤ))).X
          ((k : ℤ) + (p : ℤ)))
    (h₁ : Z₁ ≫ ((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f ((k : ℕ) : ℤ) =
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
              ((Stacks.DeRhamPullback.deRhamPullbackChain f g).f k)).app
            ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras (f ≫ g)))).X 0) ≫
          AlgebraicGeometry.SheafOfModules.exteriorProductComponent
            (Scheme.Hom.deRhamAlgebras (f ≫ g)) k 0 ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras (f ≫ g)))).XIsoOfEq
              (Nat.add_zero k)).hom) ≫
          (deRhamSmoothExtendXIso f g k).inv))
    (h₃ : Z₃ ≫ ((deRhamSmoothFiltration f g).filtration.ι.app (op ((k + p : ℕ) : ℤ))).f
          ((k : ℤ) + (p : ℤ)) =
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
              ((Stacks.DeRhamPullback.deRhamPullbackChain f g).f (k + p))).app
            ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras (f ≫ g)))).X 0) ≫
          AlgebraicGeometry.SheafOfModules.exteriorProductComponent
            (Scheme.Hom.deRhamAlgebras (f ≫ g)) (k + p) 0 ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras (f ≫ g)))).XIsoOfEq
              (Nat.add_zero (k + p))).hom) ≫
          (deRhamSmoothExtendXIso f g (k + p)).inv) ≫
          ((deRhamSmoothFiltration f g).X.XIsoOfEq
            (show ((k + p : ℕ) : ℤ) = (k : ℤ) + (p : ℤ) by push_cast; ring)).hom) :
    (moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U)).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
            ((_root_.pullback (relativeBase f g)).map
              ((_root_.pushforward (toInverseImageBase g)).map
                ((restrictAdjunction U).counit.app
                  (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))))).app
            ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
              (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 : ℕ) : ℤ))) ≫
          Z₁ ≫ ((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f
            ((k : ℕ) : ℤ)) ≫
      (SheafOfModules.DifferentialGradedAlgebra.restrictedLeftMulCochain
        (X := inverseImageBase (f ≫ g)) (pulledBackOpen f g U) (deRhamDGA f g)
        (pulledBackForm f g U p ω)).v ((k : ℕ) : ℤ) ((k : ℤ) + (p : ℤ)) rfl =
    (moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U)).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
            ((_root_.pullback (relativeBase f g)).map
              ((_root_.pushforward (toInverseImageBase g)).map
                (((restrictAdjunction U).homEquiv _ _).symm
                  (restrictedFormsWedge g U ω (k : ℤ) ((k + p : ℕ) : ℤ)
                    (by push_cast; ring)))))).app
            ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
              (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((0 : ℕ) : ℤ))) ≫
          Z₃ ≫ ((deRhamSmoothFiltration f g).filtration.ι.app (op ((k + p : ℕ) : ℤ))).f
            ((k : ℤ) + (p : ℤ))) :=
  map_comp_comp_eq_of_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₃
    (cochain_v_eq_v_comp_map_XIsoOfEq _ _ _ _ _ _ _ _ _)
    (restrictedLeftMulCochain_comp_summand_pulledBack f g U p k (k + p) 0
      k (k + p) (by omega) (by omega) (by omega) ω
      ((restrictAdjunction U).counit.app
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))
      (((restrictAdjunction U).homEquiv _ _).symm
        (restrictedFormsWedge g U ω (k : ℤ) ((k + p : ℕ) : ℤ) (by push_cast; ring)))
      (moduleRestriction_map_homEquiv_symm U _))

/-- `ρ` of the inclusion of a filtration step is a monomorphism, `ρ` being a right adjoint. -/
private theorem mono_map_filtration_ι_app_f [Smooth f] (U : Y.Opens) (c : ℕ) (n : ℤ) :
    Mono ((moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U)).map
      (((deRhamSmoothFiltration f g).filtration.ι.app (op (c : ℤ))).f n)) :=
  have : (moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U)).IsRightAdjoint :=
    (ExtensionByZeroModules.jShriekAdjunction (pulledBackOpen f g U)
      (structureSheafRing (inverseImageBase (f ≫ g)))).isRightAdjoint
  @Functor.map_mono _ _ _ _ _ _ _ _ _ (CochainComplex.mono_ι_app_f (deRhamSmoothFiltration f g) _ n)

/-- `ρ` of the coefficient summand of `f⁻¹(j_!(Ω^k|_U))` is an epimorphism, `ρ` being a left
adjoint. -/
private theorem epi_map_coefficientSummandToTarget [Smooth f] (U : Y.Opens) (k q : ℕ) (n : ℤ)
    (h : n + -(k : ℤ) = (q : ℤ)) :
    Epi ((moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U)).map
      (coefficientSummandToTarget f g k
        ((moduleRestriction Y.toRingedSpace U ⋙
          ExtensionByZeroModules.jShriek U (structureSheafRing Y.toRingedSpace)).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))) q n h)) :=
  have : (moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U)).IsLeftAdjoint :=
    moduleRestriction_isLeftAdjoint _ _
  @Functor.map_epi _ _ _ _
    (moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U)) _ _ _ _
    (epi_coefficientSummandToTarget f g k _ q n h)

section Main

variable [QuasiCompact f] [QuasiSeparated f] [Smooth f]

omit [QuasiCompact f] [QuasiSeparated f] in
/-- **`Stacks.DeRhamSmooth.WedgeStepSquare` above the cut**, in degree `k + 1 + j`. -/
theorem wedgeStepSquare_f_succ (U : Y.Opens) (p : ℕ)
    (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U)) (k j : ℕ) :
    (((moduleRestriction (inverseImageBase (f ≫ g))
          (preimageOpen (relativeBase f g) U)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((coefficientTargetComplex f g k).map ((restrictAdjunction U).counit.app
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))) ≫
          (gradedPieceIsoGradedTargetComplexOfStepSquares f g k (stepSquares f g k).1
            (stepSquares f g k).2).inv) ≫
        wedgeActionGr f g U p ω (k : ℤ) ((k + p : ℕ) : ℤ) (by push_cast; ring)).f
          ((k + 1 + j : ℕ) : ℤ) =
      (((moduleRestriction (inverseImageBase (f ≫ g))
            (preimageOpen (relativeBase f g) U)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((coefficientTargetComplex f g k).map (((restrictAdjunction U).homEquiv _ _).symm
              (restrictedFormsWedge g U ω (k : ℤ) ((k + p : ℕ) : ℤ) (by push_cast; ring))) ≫
            coefficientTargetComplexShiftHom f g k p _ ≫
            (CategoryTheory.shiftFunctor _ (p : ℤ)).map
              (gradedPieceIsoGradedTargetComplexOfStepSquares f g (k + p)
                (stepSquares f g (k + p)).1 (stepSquares f g (k + p)).2).inv) ≫
        (((moduleRestriction (inverseImageBase (f ≫ g))
              (preimageOpen (relativeBase f g) U)).mapHomologicalComplex
            (ComplexShape.up ℤ)).commShiftIso (p : ℤ)).hom.app _).f
          ((k + 1 + j : ℕ) : ℤ) := by
  refine (exists_stepFactorization_succ f g k j (stepSquares f g k).1
    (stepSquares f g k).2).elim fun Z₁ hZ₁ => ?_
  refine (exists_stepFactorization_succ_shift f g k p j).elim fun Z₃ hZ₃ => ?_
  have hcore := restrictedLeftMulCochain_comp_stepFactorization_succ f g U p ω k j Z₁ Z₃
    hZ₁.2 hZ₃.2
  have h₁ := coefficientSummandToTarget_naturality f g k ((restrictAdjunction U).counit.app
    (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))) (j + 1)
    ((k + 1 + j : ℕ) : ℤ) (by push_cast; ring)
  have h₂ := coefficientSummandToTarget_naturality f g k (((restrictAdjunction U).homEquiv _ _).symm
    (restrictedFormsWedge g U ω (k : ℤ) ((k + p : ℕ) : ℤ) (by push_cast; ring))) (j + 1)
    ((k + 1 + j : ℕ) : ℤ) (by push_cast; ring)
  have h₃ := coefficientSummandToTarget_comp_shiftHom_f f g k p
    (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g ((k + p : ℕ) : ℤ)) (j + 1)
    ((k + 1 + j : ℕ) : ℤ) (by push_cast; ring)
  have hμ := CochainComplex.Filtered.grπ_actionGr
    (respectsFiltration_restrictedLeftMulCochain f g U p ω)
    (respectsFiltration_δ_restrictedLeftMulCochain f g U p ω) (k : ℤ) ((k + p : ℕ) : ℤ)
    (by push_cast; ring) ((k + 1 + j : ℕ) : ℤ)
  have hact := CochainComplex.Filtered.actionStep_ι
    (respectsFiltration_restrictedLeftMulCochain f g U p ω) (k : ℤ) ((k + p : ℕ) : ℤ)
    (by push_cast; ring) ((k + 1 + j : ℕ) : ℤ) (((k + 1 + j : ℕ) : ℤ) + (p : ℤ)) rfl
  have hepi := epi_map_coefficientSummandToTarget f g U k (j + 1) ((k + 1 + j : ℕ) : ℤ)
    (by push_cast; ring)
  have hmono := mono_map_filtration_ι_app_f f g U (k + p) (((k + 1 + j : ℕ) : ℤ) + (p : ℤ))
  have hc := Functor.mapHomologicalComplex_commShiftIso_hom_app_f
    (moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U))
    (gradedPiece (inverseImageBase (f ≫ g)) ((k + p : ℕ) : ℤ) (deRhamSmoothFiltration f g))
    (p : ℤ) ((k + 1 + j : ℕ) : ℤ)
  refine Eq.mpr ?_ (map_comp_comp_eq_of_stepFactorizations
    (moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hepi hmono h₁ h₂ h₃ hZ₁.1 hZ₃.1 hμ hact hcore hc)
  kernel_rfl

omit [QuasiCompact f] [QuasiSeparated f] in
/-- **`Stacks.DeRhamSmooth.WedgeStepSquare` at the cut**, in degree `k`. -/
theorem wedgeStepSquare_f_cut (U : Y.Opens) (p : ℕ)
    (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U)) (k : ℕ) :
    (((moduleRestriction (inverseImageBase (f ≫ g))
          (preimageOpen (relativeBase f g) U)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((coefficientTargetComplex f g k).map ((restrictAdjunction U).counit.app
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))) ≫
          (gradedPieceIsoGradedTargetComplexOfStepSquares f g k (stepSquares f g k).1
            (stepSquares f g k).2).inv) ≫
        wedgeActionGr f g U p ω (k : ℤ) ((k + p : ℕ) : ℤ) (by push_cast; ring)).f
          ((k : ℕ) : ℤ) =
      (((moduleRestriction (inverseImageBase (f ≫ g))
            (preimageOpen (relativeBase f g) U)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((coefficientTargetComplex f g k).map (((restrictAdjunction U).homEquiv _ _).symm
              (restrictedFormsWedge g U ω (k : ℤ) ((k + p : ℕ) : ℤ) (by push_cast; ring))) ≫
            coefficientTargetComplexShiftHom f g k p _ ≫
            (CategoryTheory.shiftFunctor _ (p : ℤ)).map
              (gradedPieceIsoGradedTargetComplexOfStepSquares f g (k + p)
                (stepSquares f g (k + p)).1 (stepSquares f g (k + p)).2).inv) ≫
        (((moduleRestriction (inverseImageBase (f ≫ g))
              (preimageOpen (relativeBase f g) U)).mapHomologicalComplex
            (ComplexShape.up ℤ)).commShiftIso (p : ℤ)).hom.app _).f
          ((k : ℕ) : ℤ) := by
  refine (exists_stepFactorization_cut f g k (stepSquares f g k).1
    (stepSquares f g k).2).elim fun Z₁ hZ₁ => ?_
  refine (exists_stepFactorization_cut_shift f g k p).elim fun Z₃ hZ₃ => ?_
  have hcore := restrictedLeftMulCochain_comp_stepFactorization_cut f g U p ω k Z₁ Z₃
    hZ₁.2 hZ₃.2
  have h₁ := coefficientSummandToTarget_naturality f g k ((restrictAdjunction U).counit.app
    (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))) 0
    ((k : ℕ) : ℤ) (by push_cast; ring)
  have h₂ := coefficientSummandToTarget_naturality f g k (((restrictAdjunction U).homEquiv _ _).symm
    (restrictedFormsWedge g U ω (k : ℤ) ((k + p : ℕ) : ℤ) (by push_cast; ring))) 0
    ((k : ℕ) : ℤ) (by push_cast; ring)
  have h₃ := coefficientSummandToTarget_comp_shiftHom_f f g k p
    (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g ((k + p : ℕ) : ℤ)) 0
    ((k : ℕ) : ℤ) (by push_cast; ring)
  have hμ := CochainComplex.Filtered.grπ_actionGr
    (respectsFiltration_restrictedLeftMulCochain f g U p ω)
    (respectsFiltration_δ_restrictedLeftMulCochain f g U p ω) (k : ℤ) ((k + p : ℕ) : ℤ)
    (by push_cast; ring) ((k : ℕ) : ℤ)
  have hact := CochainComplex.Filtered.actionStep_ι
    (respectsFiltration_restrictedLeftMulCochain f g U p ω) (k : ℤ) ((k + p : ℕ) : ℤ)
    (by push_cast; ring) ((k : ℕ) : ℤ) ((k : ℤ) + (p : ℤ)) rfl
  have hepi := epi_map_coefficientSummandToTarget f g U k 0 ((k : ℕ) : ℤ) (by push_cast; ring)
  have hmono := mono_map_filtration_ι_app_f f g U (k + p) ((k : ℤ) + (p : ℤ))
  have hc := Functor.mapHomologicalComplex_commShiftIso_hom_app_f
    (moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U))
    (gradedPiece (inverseImageBase (f ≫ g)) ((k + p : ℕ) : ℤ) (deRhamSmoothFiltration f g))
    (p : ℤ) ((k : ℕ) : ℤ)
  refine Eq.mpr ?_ (map_comp_comp_eq_of_stepFactorizations
    (moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hepi hmono h₁ h₂ h₃ hZ₁.1 hZ₃.1 hμ hact hcore hc)
  kernel_rfl

variable (U : Y.Opens)

omit [QuasiCompact f] [QuasiSeparated f] in
/-- **The step-square compatibility of the action of a local form**, unconditionally: through
the identification of Section 0FMK of the graded pieces at the cuts `k` and `k + p`, the action
of `ρ(f⁻¹ω)` on `gr^k|_V` is `(ω ∧ -) ⊗ 1`. -/
theorem wedgeStepSquare (p : ℕ) (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U))
    (k : ℕ) : WedgeStepSquare f g U p ω k := by
  unfold WedgeStepSquare
  refine HomologicalComplex.hom_ext _ _ fun d => ?_
  by_cases hd : d < (k : ℤ)
  · exact ((moduleRestriction (inverseImageBase (f ≫ g))
      (preimageOpen (relativeBase f g) U)).map_isZero
        (isZero_coefficientTargetComplex_X f g k _ d hd)).eq_of_src _ _
  obtain ⟨q, hq⟩ : ∃ q : ℕ, (k : ℤ) + q = d := ⟨(d - k).toNat, by omega⟩
  cases q with
  | zero =>
    obtain rfl : d = ((k : ℕ) : ℤ) := by omega
    exact wedgeStepSquare_f_cut f g U p ω k
  | succ j =>
    obtain rfl : d = ((k + 1 + j : ℕ) : ℤ) := by
      push_cast at hq ⊢
      omega
    exact wedgeStepSquare_f_succ f g U p ω k j

/-- **The Katz–Oda rule for the first differential, unconditionally** ([Stacks, Tag 0FMN], flat
case): when the de Rham cohomology sheaves `ℋ^q_dR(X/Y)` are flat, the first differential
`d_1 : Ω^p_{Y/S} ⊗ ℋ^q_dR(X/Y) ⟶ Ω^{p+1}_{Y/S} ⊗ ℋ^q_dR(X/Y)` of the spectral sequence of
Section 0FMK satisfies the Leibniz rule `d_1(ω ⊗ s) = dω ⊗ s + (-1)^p ω ∧ d_1(1 ⊗ s)` of a
Gauss–Manin connection. This is
`Stacks.DeRhamSmooth.isKatzOdaLeibniz_of_wedgeStepSquare` with its hypothesis discharged by
`Stacks.DeRhamSmooth.wedgeStepSquare`. -/
theorem isKatzOdaLeibniz_deRhamFirstPageFlatDifferential
    (hflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
      (deRhamCohomologySheaf f q)) (q : ℤ) :
    Scheme.Hom.IsKatzOdaLeibniz g (deRhamCohomologySheaf f q)
      (fun p => deRhamFirstPageFlatDifferential f g hflat p q) :=
  isKatzOdaLeibniz_of_wedgeStepSquare f g hflat q
    (fun U p ω k => wedgeStepSquare f g U p ω k)

end Main

end Stacks.DeRhamSmooth
