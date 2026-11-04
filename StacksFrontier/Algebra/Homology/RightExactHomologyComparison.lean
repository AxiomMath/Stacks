module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Abelian.Basic
public import StacksFrontier.CategoryTheory.Preadditive.MatrixKernelSplitting

/-!
# The comparison map `G(H^n(X)) ⟶ H^n(G(X))` for a right exact functor

Let `G : C ⥤ D` be an additive functor between abelian categories which preserves finite
colimits, and let `X` be a cochain complex in `C`. The cohomology `H^n(X)` is the cokernel of the
map `X^{n-1} ⟶ Z^n(X)` into the cycles, so `G(H^n(X))` is the cokernel of `G(X^{n-1}) ⟶ G(Z^n(X))`,
and the map `G(Z^n(X)) ⟶ Z^n(G(X))` given by the universal property of the kernel descends to a
canonical comparison `G(H^n(X)) ⟶ H^n(G(X))`.

## Main definitions

* `cyclesComparisonRightExactHomologyComparison`: the map `G(Z^n(X)) ⟶ Z^n(G(X))`.
* `homologyComparisonRightExactHomologyComparison`: the map `G(H^n(X)) ⟶ H^n(G(X))`.

## Main results

* `homologyComparison_naturality_rightExactHomologyComparison`: the comparison is natural in `X`.
* `isIso_homologyComparison_of_isIso_cyclesComparison_rightExactHomologyComparison`: it is an
  isomorphism when the comparison on cycles is, in particular
  (`isIso_cyclesComparison_of_isLimit_rightExactHomologyComparison`) when `G` carries the kernel
  `Z^n(X) ⟶ X^n` of the differential to a kernel.
* `isIso_map_homologyComparison_iff_leftExactHomologyComparison`: for `e : G₁ ⋙ G₂ ≅ G₃` with
  the comparison of `G₂` an isomorphism, `G₂` of the comparison of `G₁` is an isomorphism
  exactly when the comparison of `G₃` is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
  [Abelian E]

section

variable (G : C ⥤ D) [G.Additive] (X : CochainComplex C ℤ) (n : ℤ)

/-- **The comparison on cycles**, `G(Z^n(X)) ⟶ Z^n(G(X))`. -/
def cyclesComparisonRightExactHomologyComparison :
    G.obj (X.cycles n) ⟶ ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X).cycles n :=
  ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X).liftCycles (G.map (X.iCycles n)) (n + 1)
    (by simp) (by simp [← G.map_comp])

/-- The comparison on cycles followed by `Z^n(G(X)) ⟶ G(X)^n` is `G(Z^n(X) ⟶ X^n)`. -/
@[reassoc (attr := simp)] private theorem cyclesComparison_comp_iCycles :
    G.cyclesComparisonRightExactHomologyComparison X n ≫
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X).iCycles n = G.map (X.iCycles n) :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- `G(X^{n-1} ⟶ Z^n(X))` followed by the comparison on cycles is the map
`G(X^{n-1}) ⟶ Z^n(G(X))`. -/
theorem map_toCycles_comp_cyclesComparison_rightExactHomologyComparison :
    G.map (X.toCycles (n - 1) n) ≫ G.cyclesComparisonRightExactHomologyComparison X n =
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X).toCycles (n - 1) n := by
  apply (cancel_mono (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X).iCycles n)).mp
  simp [← G.map_comp]

/-- The comparison on cycles is natural in `X`. -/
theorem cyclesComparison_naturality_rightExactHomologyComparison {X Y : CochainComplex C ℤ}
    (φ : X ⟶ Y) :
    G.map (HomologicalComplex.cyclesMap φ n) ≫ G.cyclesComparisonRightExactHomologyComparison Y n =
      G.cyclesComparisonRightExactHomologyComparison X n ≫
        HomologicalComplex.cyclesMap ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) n := by
  apply (cancel_mono (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj Y).iCycles n)).mp
  rw [Category.assoc, Category.assoc, cyclesComparison_comp_iCycles, HomologicalComplex.cyclesMap_i,
    ← G.map_comp]
  simp

/-- If `G` carries the kernel `Z^n(X) ⟶ X^n` of the differential to a kernel, the comparison on
cycles is an isomorphism. -/
theorem isIso_cyclesComparison_of_isLimit_rightExactHomologyComparison
    (hG : IsLimit (KernelFork.ofι (G.map (X.iCycles n))
      (show G.map (X.iCycles n) ≫ G.map (X.d n (n + 1)) = 0 by
        rw [← G.map_comp, HomologicalComplex.iCycles_d, G.map_zero]))) :
    IsIso (G.cyclesComparisonRightExactHomologyComparison X n) := by
  let Y := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hG (Y.iCycles n) (Y.iCycles_d n (n + 1))
  have hl' : l ≫ G.map (X.iCycles n) = Y.iCycles n := hl
  refine ⟨l, ?_, ?_⟩
  · refine Fork.IsLimit.hom_ext hG ?_
    show (G.cyclesComparisonRightExactHomologyComparison X n ≫ l) ≫ G.map (X.iCycles n) =
      𝟙 _ ≫ G.map (X.iCycles n)
    rw [Category.assoc, hl', cyclesComparison_comp_iCycles, Category.id_comp]
  · apply (cancel_mono (Y.iCycles n)).mp
    rw [Category.assoc, cyclesComparison_comp_iCycles, hl', Category.id_comp]

/-- **A split kernel is preserved**: if the differential `X^n ⟶ X^{n+1}` has a kernel split by
`u, v, w`, the comparison on cycles is an isomorphism for every additive `G`. -/
theorem isIso_cyclesComparison_of_splitting_rightExactHomologyComparison {K : C} (u : K ⟶ X.X n)
    (v : X.X n ⟶ K) (w : X.X (n + 1) ⟶ X.X n) (h₁ : u ≫ v = 𝟙 K) (h₂ : u ≫ X.d n (n + 1) = 0)
    (h₃ : X.d n (n + 1) ≫ w + v ≫ u = 𝟙 _) :
    IsIso (G.cyclesComparisonRightExactHomologyComparison X n) := by
  let k := X.liftCycles u (n + 1) (by simp) h₂
  have hk : k ≫ X.iCycles n = u := X.liftCycles_i _ _ _ _
  have e₁ : X.iCycles n ≫ v ≫ k = 𝟙 _ := by
    apply (cancel_mono (X.iCycles n)).mp
    rw [Category.assoc, Category.assoc, hk, Category.id_comp]
    simpa using X.iCycles n ≫= h₃
  have e₃ : X.d n (n + 1) ≫ w + (v ≫ k) ≫ X.iCycles n = 𝟙 _ := by
    rw [Category.assoc, hk, h₃]
  exact G.isIso_cyclesComparison_of_isLimit_rightExactHomologyComparison X n
    (isLimitMapKernelForkOfSplittingMatrixKernelSplitting G e₁ (X.iCycles_d n (n + 1)) e₃)

variable [PreservesFiniteColimits G]

/-- `G(H^n(X))` is the cokernel of `G(X^{n-1}) ⟶ G(Z^n(X))`. -/
def homologyIsCokernelMapRightExactHomologyComparison :
    IsColimit (CokernelCofork.ofπ (G.map (X.homologyπ n))
      (show G.map (X.toCycles (n - 1) n) ≫ G.map (X.homologyπ n) = 0 by
        rw [← G.map_comp, HomologicalComplex.toCycles_comp_homologyπ, G.map_zero])) :=
  isColimitCoforkMapOfIsColimit' G (X.toCycles_comp_homologyπ (n - 1) n)
    (X.homologyIsCokernel (n - 1) n (by simp))

/-- **The comparison** `G(H^n(X)) ⟶ H^n(G(X))`. -/
def homologyComparisonRightExactHomologyComparison :
    G.obj (X.homology n) ⟶ ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X).homology n :=
  (CokernelCofork.IsColimit.desc' (G.homologyIsCokernelMapRightExactHomologyComparison X n)
    (G.cyclesComparisonRightExactHomologyComparison X n ≫
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X).homologyπ n)
    (by rw [← Category.assoc, map_toCycles_comp_cyclesComparison_rightExactHomologyComparison,
      HomologicalComplex.toCycles_comp_homologyπ])).1

/-- `G(Z^n(X) ⟶ H^n(X))` followed by the comparison is the comparison on cycles followed by
`Z^n(G(X)) ⟶ H^n(G(X))`. -/
@[reassoc (attr := simp)]
theorem map_homologyπ_comp_homologyComparison_rightExactHomologyComparison :
    G.map (X.homologyπ n) ≫ G.homologyComparisonRightExactHomologyComparison X n =
      G.cyclesComparisonRightExactHomologyComparison X n ≫
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X).homologyπ n :=
  (CokernelCofork.IsColimit.desc'
    (G.homologyIsCokernelMapRightExactHomologyComparison X n) _ _).2

/-- Two morphisms out of `G(H^n(X))` agree if they agree after composing with
`G(Z^n(X) ⟶ H^n(X))`. -/
theorem homologyComparison_hom_ext_rightExactHomologyComparison {W : D}
    {f g : G.obj (X.homology n) ⟶ W}
    (h : G.map (X.homologyπ n) ≫ f = G.map (X.homologyπ n) ≫ g) : f = g :=
  Cofork.IsColimit.hom_ext (G.homologyIsCokernelMapRightExactHomologyComparison X n) h

/-- **The comparison is natural.** -/
theorem homologyComparison_naturality_rightExactHomologyComparison {X Y : CochainComplex C ℤ}
    (φ : X ⟶ Y) :
    G.map (HomologicalComplex.homologyMap φ n) ≫
        G.homologyComparisonRightExactHomologyComparison Y n =
      G.homologyComparisonRightExactHomologyComparison X n ≫
        HomologicalComplex.homologyMap ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) n := by
  refine G.homologyComparison_hom_ext_rightExactHomologyComparison X n ?_
  rw [← G.map_comp_assoc, HomologicalComplex.homologyπ_naturality, G.map_comp_assoc,
    map_homologyπ_comp_homologyComparison_rightExactHomologyComparison,
    map_homologyπ_comp_homologyComparison_rightExactHomologyComparison_assoc,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc, ← Category.assoc,
    cyclesComparison_naturality_rightExactHomologyComparison]

/-- **If the comparison on cycles is an isomorphism, so is the comparison on cohomology.** Both
sides are cokernels of the map from the term in degree `n - 1` into the cycles. -/
theorem isIso_homologyComparison_of_isIso_cyclesComparison_rightExactHomologyComparison
    [IsIso (G.cyclesComparisonRightExactHomologyComparison X n)] :
    IsIso (G.homologyComparisonRightExactHomologyComparison X n) := by
  let Y := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X
  let cY := Y.homologyIsCokernel (n - 1) n (by simp)
  obtain ⟨e', he'⟩ := CokernelCofork.IsColimit.desc' cY
    (CategoryTheory.inv (G.cyclesComparisonRightExactHomologyComparison X n) ≫
      G.map (X.homologyπ n))
    (by rw [← map_toCycles_comp_cyclesComparison_rightExactHomologyComparison, Category.assoc,
      IsIso.hom_inv_id_assoc, ← G.map_comp, HomologicalComplex.toCycles_comp_homologyπ,
      G.map_zero])
  rw [CokernelCofork.π_ofπ] at he'
  refine ⟨e', ?_, ?_⟩
  · refine G.homologyComparison_hom_ext_rightExactHomologyComparison X n ?_
    rw [map_homologyπ_comp_homologyComparison_rightExactHomologyComparison_assoc, he',
      IsIso.hom_inv_id_assoc, Category.comp_id]
  · refine Cofork.IsColimit.hom_ext cY ?_
    simp only [Cofork.ofπ_pt, CokernelCofork.π_ofπ]
    rw [reassoc_of% he', map_homologyπ_comp_homologyComparison_rightExactHomologyComparison,
      IsIso.inv_hom_id_assoc]
    exact (Category.comp_id _).symm

/-- **An exact functor commutes with cohomology**: the comparison is an isomorphism when `G` also
preserves finite limits. -/
theorem isIso_homologyComparison_of_preservesFiniteLimits_rightExactHomologyComparison
    [PreservesFiniteLimits G] :
    IsIso (G.homologyComparisonRightExactHomologyComparison X n) := by
  have : IsIso (G.cyclesComparisonRightExactHomologyComparison X n) :=
    G.isIso_cyclesComparison_of_isLimit_rightExactHomologyComparison X n
      (isLimitForkMapOfIsLimit' G (X.iCycles_d n (n + 1)) (X.cyclesIsKernel n (n + 1) (by simp)))
  exact G.isIso_homologyComparison_of_isIso_cyclesComparison_rightExactHomologyComparison X n

end

section Comp

variable (G₁ : C ⥤ D) (G₂ : D ⥤ E) (G₃ : C ⥤ E) [G₁.Additive] [G₂.Additive] [G₃.Additive]
  (e : G₁ ⋙ G₂ ≅ G₃) (X : CochainComplex C ℤ) (n : ℤ)

/-- The isomorphism of complexes `G₃(X) ≅ G₂(G₁(X))` induced by `e : G₁ ⋙ G₂ ≅ G₃`. -/
def mapHomologicalComplexCompIsoOfIsoRightExactHomologyComparison :
    (G₃.mapHomologicalComplex (ComplexShape.up ℤ)).obj X ≅
      (G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) :=
  HomologicalComplex.Hom.isoOfComponents (fun i => e.symm.app (X.X i)) (fun i j _ =>
    (e.inv.naturality (X.d i j)).symm)

/-- For `e : G₁ ⋙ G₂ ≅ G₃`, the comparison on cycles of `G₃` corresponds under `e` to the
composite of `G₂` of the comparison on cycles of `G₁` and the comparison on cycles of `G₂`. -/
theorem cyclesComparison_comp_rightExactHomologyComparison :
    G₃.cyclesComparisonRightExactHomologyComparison X n ≫
        HomologicalComplex.cyclesMap
          (mapHomologicalComplexCompIsoOfIsoRightExactHomologyComparison G₁ G₂ G₃ e X).hom n =
      e.inv.app (X.cycles n) ≫ G₂.map (G₁.cyclesComparisonRightExactHomologyComparison X n) ≫
        G₂.cyclesComparisonRightExactHomologyComparison
          ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) n := by
  apply (cancel_mono (((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj X)).iCycles n)).mp
  simp [mapHomologicalComplexCompIsoOfIsoRightExactHomologyComparison, ← G₂.map_comp]

variable [PreservesFiniteColimits G₁] [PreservesFiniteColimits G₂] [PreservesFiniteColimits G₃]

/-- For `e : G₁ ⋙ G₂ ≅ G₃`, the comparison of `G₃` corresponds under `e` to the composite of
`G₂` of the comparison of `G₁` and the comparison of `G₂` at `G₁(X)`. -/
theorem homologyComparison_comp_rightExactHomologyComparison :
    G₃.homologyComparisonRightExactHomologyComparison X n ≫
        HomologicalComplex.homologyMap
          (mapHomologicalComplexCompIsoOfIsoRightExactHomologyComparison G₁ G₂ G₃ e X).hom n =
      e.inv.app (X.homology n) ≫ G₂.map (G₁.homologyComparisonRightExactHomologyComparison X n) ≫
        G₂.homologyComparisonRightExactHomologyComparison
          ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) n := by
  refine G₃.homologyComparison_hom_ext_rightExactHomologyComparison X n ?_
  rw [map_homologyπ_comp_homologyComparison_rightExactHomologyComparison_assoc,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    cyclesComparison_comp_rightExactHomologyComparison, e.inv.naturality_assoc]
  simp only [Functor.comp_map, Category.assoc, ← G₂.map_comp_assoc,
    map_homologyπ_comp_homologyComparison_rightExactHomologyComparison, G₂.map_comp,
    map_homologyπ_comp_homologyComparison_rightExactHomologyComparison]

include e in
/-- **The comparison and composition.** For `e : G₁ ⋙ G₂ ≅ G₃` with the comparison of `G₂` at
`G₁(X)` an isomorphism, `G₂` of the comparison of `G₁` is an isomorphism exactly when the
comparison of `G₃` is. -/
theorem isIso_map_homologyComparison_iff_leftExactHomologyComparison
    [IsIso (G₂.homologyComparisonRightExactHomologyComparison
      ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) n)] :
    IsIso (G₂.map (G₁.homologyComparisonRightExactHomologyComparison X n)) ↔
      IsIso (G₃.homologyComparisonRightExactHomologyComparison X n) := by
  simpa using
    (congrArg IsIso (homologyComparison_comp_rightExactHomologyComparison G₁ G₂ G₃ e X n)).symm

include e in
/-- If the comparisons of `G₁` at `X` and of `G₂` at `G₁(X)` are isomorphisms, so is the
comparison of `G₃ ≅ G₁ ⋙ G₂`. -/
theorem isIso_homologyComparison_of_comp_rightExactHomologyComparison
    [IsIso (G₁.homologyComparisonRightExactHomologyComparison X n)]
    [IsIso (G₂.homologyComparisonRightExactHomologyComparison
      ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) n)] :
    IsIso (G₃.homologyComparisonRightExactHomologyComparison X n) :=
  (isIso_map_homologyComparison_iff_leftExactHomologyComparison G₁ G₂ G₃ e X n).1 inferInstance

end Comp

end CategoryTheory.Functor
