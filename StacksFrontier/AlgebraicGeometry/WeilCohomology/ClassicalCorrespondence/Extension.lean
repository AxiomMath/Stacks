module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalCorrespondence.VarietyComparison
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationClopen

/-!
# Extending isomorphisms of Weil data from varieties to all smooth projective schemes

Let `W`, `W'` be data (D0)–(D3) satisfying (A), (B), (C) over an algebraically closed field `k`.
Every smooth projective scheme `X` is the disjoint union of its connected components `X_i`, which
are smooth projective varieties, and `H^*(X) = ∏_i H^*(X_i)` through the restrictions (Stacks
0FHJ; `WeilData.eq_zero_of_pull_eq_zero`, `WeilData.sum_extendByZero_pull`). Hence isomorphisms
`Θ_V : H^n(V) ≅ H'^n(V)` given on varieties only, natural for morphisms of varieties and
compatible with cup products and units, extend uniquely to all smooth projective schemes:
`Θ_X(a)` is the class restricting to `Θ_{X_i}(a|_{X_i})` on each `X_i`. If on varieties `Θ`
scales the cycle classes by `κⁱ` and the traces by `κ^d`, read in coordinates of the Tate lines,
so does its extension, and it is then the isomorphism of cohomology of an isomorphism of data
(D0)–(D3) preserving cycle classes and traces, with `F(1) ≅ F(1)'` the coordinates scaled by
`κ⁻¹`.

This is how an isomorphism of classical Weil cohomology theories, given on varieties, is turned
into an isomorphism of the data of Section 0FHA in the proof of Stacks 0FH3.

## Main definitions

* `Stacks.WeilCohomology.WeilData.VarietyGradedIso`: isomorphisms on varieties.
* `Stacks.WeilCohomology.WeilData.VarietyGradedIso.toGradedIso`: their extension.
* `Stacks.WeilCohomology.WeilData.VarietyGradedIso.toIso`: the isomorphism of data.

## Main results

* `Stacks.WeilCohomology.WeilData.VarietyGradedIso.toIso_preservesCycleClass`,
  `Stacks.WeilCohomology.WeilData.VarietyGradedIso.toIso_preservesTrace`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme SmoothProjective

namespace WeilData

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F]

/-! ### Components -/

section Components

variable (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- Every point lies on a component. -/
theorem exists_mem_range_compAtι (x : X.obj.left) :
    ∃ i ∈ (Finset.univ : Finset (Idx X)), x ∈ Set.range (compAtι X i).hom.left := by
  refine ⟨(idxEquiv X).symm (_root_.ConnectedComponents.mk x), Finset.mem_univ _, ?_⟩
  change x ∈ Set.range (compOpens X _).ι
  rw [Scheme.Opens.range_ι]
  rw [Equiv.apply_symm_apply]
  exact rfl

/-- Distinct components are disjoint. -/
theorem disjoint_range_compAtι (i j : Idx X) (hij : i ≠ j) :
    Disjoint (Set.range (compAtι X i).hom.left) (Set.range (compAtι X j).hom.left) := by
  change Disjoint (Set.range (compOpens X _).ι) (Set.range (compOpens X _).ι)
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  change Disjoint (_root_.ConnectedComponents.mk ⁻¹' {idxEquiv X i})
    (_root_.ConnectedComponents.mk ⁻¹' {idxEquiv X j})
  refine Set.disjoint_left.2 fun x hx hx' ↦ hij ((idxEquiv X).injective ?_)
  exact (Set.mem_singleton_iff.1 hx).symm.trans (Set.mem_singleton_iff.1 hx')

/-- A component of a nonempty equidimensional scheme of dimension `d` is nonempty equidimensional
of dimension `d`. -/
theorem isNonemptyEquidimensional_compAt {d : ℕ} (hX : IsNonemptyEquidimensional X d)
    (i : Idx X) : IsNonemptyEquidimensional ((toSchemeCat k).obj (compAt X i)) d where
  nonempty := by
    obtain ⟨x, hx⟩ := _root_.ConnectedComponents.surjective_coe (idxEquiv X i)
    exact ⟨⟨x, hx⟩⟩
  relativeDimension := RelativeDimension.comp_isOpenImmersion _ _ hX.relativeDimension

end Components

variable {W W' : WeilData k F}

/-- The dimension of a nonempty equidimensional scheme is determined. -/
theorem _root_.Stacks.WeilCohomology.IsNonemptyEquidimensional.dim_eq
    {X : (SmoothProjectiveScheme k).FullSubcategory}
    {d d' : ℕ} (hX : IsNonemptyEquidimensional X d) (hX' : IsNonemptyEquidimensional X d') :
    d = d' := by
  have := hX.nonempty
  have h := (topologicalKrullDim_eq_of_relativeDimension X.obj.hom hX.relativeDimension).symm.trans
    (topologicalKrullDim_eq_of_relativeDimension X.obj.hom hX'.relativeDimension)
  exact_mod_cast h

/-- Pullback along a composite on homogeneous classes. -/
theorem pullDeg_comp_apply {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    (g : Y ⟶ Z) (n : ℤ) (a : W.grade Z n) :
    W.pullDeg (f ≫ g) n a = W.pullDeg f n (W.pullDeg g n a) :=
  Subtype.ext (by rw [coe_pullDeg, coe_pullDeg, coe_pullDeg, W.pull_comp]; rfl)

/-- **The trace of a disjoint union** (Stacks 0FHP), for the decomposition into components: for
`X` nonempty equidimensional of dimension `d`, `∫_X a = ∑_i ∫_{X_i} a|_{X_i}` in coordinates. -/
theorem traceCoord_eq_sum (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) (X : (SmoothProjectiveScheme k).FullSubcategory)
    {d : ℕ} (hX : IsNonemptyEquidimensional X d) (a : W.grade X (2 * (d : ℤ))) :
    W.traceCoord X d hX a = ∑ i, W.traceCoord _ d (isNonemptyEquidimensional_compAt X hX i)
      (W.pullDeg (compAtι X i) _ a) := by
  have hproj : ∀ (Y : (SmoothProjectiveScheme k).FullSubcategory)
      (hY : IsNonemptyEquidimensional Y d) (b : W.grade Y (2 * (d : ℤ))),
      W.traceCoord Y d hY b = W.traceProj Y d hY b := by
    intro Y hY b
    rw [traceProj_of_mem W Y d hY b.2, trace_eq_traceCoord, LinearEquiv.apply_symm_apply]
  rw [hproj]
  conv_lhs => rw [← sum_extendByZero_pull (hA := hA) (hB := hB) (hC := hC) Finset.univ
    (fun i ↦ compAtι X i) (fun x ↦ exists_mem_range_compAtι X x)
    (fun i _ j _ hij ↦ disjoint_range_compAtι X i j hij) (a : W.H X)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hproj, ← mul_one (extendByZero hA hB hC (compAtι X i) _),
    traceProj_extendByZero_mul (hA := hA) (hB := hB) (hC := hC) _ hX
      (isNonemptyEquidimensional_compAt X hX i), map_one, mul_one, coe_pullDeg]

/-- **Isomorphisms of cohomology given on smooth projective varieties**: `H^n(V) ≅ H'^n(V)`,
natural for morphisms of varieties, compatible with cup products and units. -/
structure VarietyGradedIso (W W' : WeilData k F) where
  /-- The isomorphisms `H^n(V) ≅ H'^n(V)`. -/
  e : ∀ (V : (SmoothProjective k).FullSubcategory) (n : ℤ),
    W.grade ((toSchemeCat k).obj V) n ≃ₗ[F] W'.grade ((toSchemeCat k).obj V) n
  /-- They commute with pullbacks. -/
  e_pull : ∀ {V V' : (SmoothProjective k).FullSubcategory} (f : V ⟶ V') (n : ℤ)
    (a : W.grade ((toSchemeCat k).obj V') n),
    e V n (W.pullDeg ((toSchemeCat k).map f) n a) = W'.pullDeg ((toSchemeCat k).map f) n (e V' n a)
  /-- They commute with cup products. -/
  e_mul : ∀ (V : (SmoothProjective k).FullSubcategory) (i j : ℤ)
    (a : W.grade ((toSchemeCat k).obj V) i) (b : W.grade ((toSchemeCat k).obj V) j),
    (e V (i + j) ⟨(a : W.H ((toSchemeCat k).obj V)) * (b : W.H ((toSchemeCat k).obj V)),
      SetLike.GradedMul.mul_mem a.2 b.2⟩ : W'.H ((toSchemeCat k).obj V)) =
      (e V i a : W'.H ((toSchemeCat k).obj V)) * (e V j b : W'.H ((toSchemeCat k).obj V))
  /-- They send `1` to `1`. -/
  e_one : ∀ V, (e V 0 ⟨1, SetLike.GradedOne.one_mem⟩ : W'.H ((toSchemeCat k).obj V)) = 1

namespace VarietyGradedIso

variable (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
  (hA' : W'.PoincareDuality) (hB' : W'.Kunneth) (hC' : W'.CycleClassAxiom hA'.perfectPairing)

/-- The inverse isomorphisms. -/
def symm (Θ : VarietyGradedIso W W') : VarietyGradedIso W' W where
  e V n := (Θ.e V n).symm
  e_pull f n a := by
    apply (Θ.e _ n).injective
    rw [LinearEquiv.apply_symm_apply, Θ.e_pull, LinearEquiv.apply_symm_apply]
  e_mul V i j a b := by
    have h := Θ.e_mul V i j ((Θ.e V i).symm a) ((Θ.e V j).symm b)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    have h' : ((Θ.e V (i + j)).symm
        ⟨(a : W'.H ((toSchemeCat k).obj V)) * (b : W'.H ((toSchemeCat k).obj V)),
          SetLike.GradedMul.mul_mem a.2 b.2⟩) =
        ⟨((Θ.e V i).symm a : W.H ((toSchemeCat k).obj V)) *
          ((Θ.e V j).symm b : W.H ((toSchemeCat k).obj V)),
          SetLike.GradedMul.mul_mem ((Θ.e V i).symm a).2 ((Θ.e V j).symm b).2⟩ := by
      apply (Θ.e V (i + j)).injective
      rw [LinearEquiv.apply_symm_apply]
      exact Subtype.ext h.symm
    rw [h']
  e_one V := by
    have h := Θ.e_one V
    have h' : (Θ.e V 0).symm ⟨1, SetLike.GradedOne.one_mem⟩ = ⟨1, SetLike.GradedOne.one_mem⟩ := by
      apply (Θ.e V 0).injective
      rw [LinearEquiv.apply_symm_apply]
      exact Subtype.ext h.symm
    rw [h']

variable (Θ : VarietyGradedIso W W')

include hA' hB' hC' in
/-- Classes of `H'^*(X)` are determined by their restrictions to the components of `X`. -/
theorem ext_of_pull_compAtι {X : (SmoothProjectiveScheme k).FullSubcategory} {z z' : W'.H X}
    (h : ∀ i, W'.pull (compAtι X i) z = W'.pull (compAtι X i) z') : z = z' :=
  sub_eq_zero.1 (eq_zero_of_pull_eq_zero (hA := hA') (hB := hB') (hC := hC') Finset.univ
    (fun i ↦ compAtι X i) (fun x ↦ exists_mem_range_compAtι X x)
    (fun i _ ↦ by rw [map_sub, h i, sub_self]))

/-- The extension `Θ_X` on `X`, as a map into `H'^*(X)`: the class restricting to
`Θ_{X_i}(a|_{X_i})` on the component `X_i`. -/
def extMap (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) :
    W.grade X n →ₗ[F] W'.H X :=
  ∑ i, extendByZero hA' hB' hC' (compAtι X i) ∘ₗ (W'.grade _ n).subtype ∘ₗ
    (Θ.e (compAt X i) n).toLinearMap ∘ₗ W.pullDeg (compAtι X i) n

theorem extMap_mem (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) (a : W.grade X n) :
    Θ.extMap hA' hB' hC' X n a ∈ W'.grade X n := by
  rw [extMap, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i _ ↦
    extendByZero_mem (hA := hA') (hB := hB') (hC := hC') _ (Θ.e _ n _).2

/-- **The extension `Θ_X : H^n(X) → H'^n(X)`.** -/
def ext (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) :
    W.grade X n →ₗ[F] W'.grade X n :=
  (Θ.extMap hA' hB' hC' X n).codRestrict _ (Θ.extMap_mem hA' hB' hC' X n)

/-- **The extension restricts to `Θ` on the components.** -/
theorem pull_ext (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) (a : W.grade X n)
    (j : Idx X) :
    W'.pull (compAtι X j) (Θ.ext hA' hB' hC' X n a : W'.H X) =
      Θ.e (compAt X j) n (W.pullDeg (compAtι X j) n a) := by
  change W'.pull (compAtι X j) (Θ.extMap hA' hB' hC' X n a) = _
  rw [extMap, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.comp_apply]
  rw [Finset.sum_eq_single j (fun i _ hij ↦ pull_extendByZero_of_disjoint (hA := hA') (hB := hB')
      (hC := hC') _ _ (disjoint_range_compAtι X j i (Ne.symm hij)) _)
      (fun h ↦ (h (Finset.mem_univ j)).elim)]
  exact pull_extendByZero_self (hA := hA') (hB := hB') (hC := hC') _ _

/-- The extension restricts to `Θ` on the components, on homogeneous classes. -/
theorem pullDeg_ext (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) (a : W.grade X n)
    (j : Idx X) :
    W'.pullDeg (compAtι X j) n (Θ.ext hA' hB' hC' X n a) =
      Θ.e (compAt X j) n (W.pullDeg (compAtι X j) n a) :=
  Subtype.ext ((coe_pullDeg _ _ _ _).trans (Θ.pull_ext hA' hB' hC' X n a j))

include hA hB hC in
/-- `Θ_X` is bijective, with inverse the extension of `Θ⁻¹`. -/
theorem ext_symm_ext (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) (a : W.grade X n) :
    Θ.symm.ext hA hB hC X n (Θ.ext hA' hB' hC' X n a) = a := by
  refine Subtype.ext (ext_of_pull_compAtι hA hB hC fun i ↦ ?_)
  rw [Θ.symm.pull_ext hA hB hC, Θ.pullDeg_ext hA' hB' hC']
  exact congrArg Subtype.val (LinearEquiv.symm_apply_apply _ _)

/-- **The extension of `Θ`**, a linear isomorphism `H^n(X) ≅ H'^n(X)` for every `X`. -/
def extEquiv (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) :
    W.grade X n ≃ₗ[F] W'.grade X n :=
  LinearEquiv.ofLinear (Θ.ext hA' hB' hC' X n) (Θ.symm.ext hA hB hC X n)
    (LinearMap.ext fun b ↦ Θ.symm.ext_symm_ext hA' hB' hC' hA hB hC X n b)
    (LinearMap.ext fun a ↦ Θ.ext_symm_ext hA hB hC hA' hB' hC' X n a)

@[simp]
theorem extEquiv_apply (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ)
    (a : W.grade X n) : Θ.extEquiv hA hB hC hA' hB' hC' X n a = Θ.ext hA' hB' hC' X n a :=
  rfl

/-- **The extension of `Θ` as degreewise isomorphisms of Weil data**: it commutes with pullbacks,
cup products and units, by restriction to the components. -/
def toGradedIso : GradedIso W W' where
  e := Θ.extEquiv hA hB hC hA' hB' hC'
  e_pull {X Y} f n a := by
    refine Subtype.ext (ext_of_pull_compAtι hA' hB' hC' fun j ↦ ?_)
    rw [extEquiv_apply, extEquiv_apply, Θ.pull_ext hA' hB' hC', coe_pullDeg,
      ← pullDeg_comp_apply, ← resIdx_compAtι, pullDeg_comp_apply, Θ.e_pull,
      ← Θ.pullDeg_ext hA' hB' hC', ← pullDeg_comp_apply, resIdx_compAtι, pullDeg_comp_apply,
      coe_pullDeg, coe_pullDeg]
  e_mul X i j a b := by
    refine ext_of_pull_compAtι hA' hB' hC' fun l ↦ ?_
    have h : W.pullDeg (compAtι X l) (i + j) ⟨(a : W.H X) * (b : W.H X),
        SetLike.GradedMul.mul_mem a.2 b.2⟩ =
        ⟨(W.pullDeg (compAtι X l) i a : W.H _) * (W.pullDeg (compAtι X l) j b : W.H _),
          SetLike.GradedMul.mul_mem (W.pullDeg (compAtι X l) i a).2
            (W.pullDeg (compAtι X l) j b).2⟩ :=
      Subtype.ext (by simp only [coe_pullDeg, map_mul])
    rw [extEquiv_apply, Θ.pull_ext hA' hB' hC', map_mul, extEquiv_apply, extEquiv_apply,
      Θ.pull_ext hA' hB' hC', Θ.pull_ext hA' hB' hC', ← Θ.e_mul, h]
  e_one X := by
    refine ext_of_pull_compAtι hA' hB' hC' fun l ↦ ?_
    have h : W.pullDeg (compAtι X l) 0 ⟨1, SetLike.GradedOne.one_mem⟩ =
        ⟨1, SetLike.GradedOne.one_mem⟩ :=
      Subtype.ext (by simp only [coe_pullDeg, map_one])
    rw [extEquiv_apply, Θ.pull_ext hA' hB' hC', map_one, ← Θ.e_one, h]

/-- On varieties, the extension of `Θ` is `Θ`. -/
theorem toGradedIso_e_toSchemeCat (V : (SmoothProjective k).FullSubcategory) (n : ℤ)
    (a : W.grade ((toSchemeCat k).obj V) n) :
    (Θ.toGradedIso hA hB hC hA' hB' hC').e ((toSchemeCat k).obj V) n a = Θ.e V n a := by
  refine Subtype.ext (ext_of_pull_compAtι hA' hB' hC' fun i ↦ ?_)
  change W'.pull _ (Θ.ext hA' hB' hC' ((toSchemeCat k).obj V) n a :
    W'.H ((toSchemeCat k).obj V)) = _
  rw [Θ.pull_ext hA' hB' hC', ← ClassicalWeilCohomologyTheory.toSchemeCat_map_compIso_hom,
    Θ.e_pull, coe_pullDeg]

variable {Θ}

/-- **Scaled cycle classes extend**: if `Θ(γ(β)) = κⁱ γ'(β)` on varieties, the same holds for the
extension on every smooth projective scheme. -/
theorem toGradedIso_cycleClassCoord (κ : F) (hγ : ∀ (V : (SmoothProjective k).FullSubcategory)
      (i : ℕ) (β : codimensionChowGroup k ((toSchemeCat k).obj V).obj.hom i),
      Θ.e V (2 * (i : ℤ)) (W.cycleClassCoord _ i β) = κ ^ i • W'.cycleClassCoord _ i β)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ)
    (β : codimensionChowGroup k X.obj.hom i) :
    (Θ.toGradedIso hA hB hC hA' hB' hC').e X (2 * (i : ℤ)) (W.cycleClassCoord X i β) =
      κ ^ i • W'.cycleClassCoord X i β := by
  refine Subtype.ext (ext_of_pull_compAtι hA' hB' hC' fun l ↦ ?_)
  change W'.pull _ (Θ.ext hA' hB' hC' X _ (W.cycleClassCoord X i β) : W'.H X) = _
  rw [Θ.pull_ext hA' hB' hC', ← cycleClassCoord_codimensionGysin W hC.pullback, hγ]
  simp only [SetLike.val_smul, map_smul]
  rw [← coe_pullDeg, ← cycleClassCoord_codimensionGysin W' hC'.pullback]

/-- **Scaled traces extend**: if `∫'_V Θ(a) = κ^d ∫_V a` on varieties, the same holds for the
extension on every nonempty equidimensional smooth projective scheme. -/
theorem traceCoord_toGradedIso (κ : F) (htr : ∀ (V : (SmoothProjective k).FullSubcategory) (d : ℕ)
      (hV : IsNonemptyEquidimensional ((toSchemeCat k).obj V) d)
      (a : W.grade ((toSchemeCat k).obj V) (2 * (d : ℤ))),
      W'.traceCoord _ d hV (Θ.e V _ a) = κ ^ d * W.traceCoord _ d hV a)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ) (hX : IsNonemptyEquidimensional X d)
    (a : W.grade X (2 * (d : ℤ))) :
    W'.traceCoord X d hX ((Θ.toGradedIso hA hB hC hA' hB' hC').e X _ a) =
      κ ^ d * W.traceCoord X d hX a := by
  rw [traceCoord_eq_sum hA' hB' hC' X hX, traceCoord_eq_sum hA hB hC X hX, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change W'.traceCoord _ d _ (W'.pullDeg _ _ (Θ.ext hA' hB' hC' X _ a)) = _
  rw [Θ.pullDeg_ext hA' hB' hC', htr]

variable (Θ)

/-- **The isomorphism of data (D0)–(D3)** extending `Θ`, for the Tate lines identified by the
coordinates scaled by `κ⁻¹`. -/
def toIso (κ : Fˣ) : Iso W W' :=
  (Θ.toGradedIso hA hB hC hA' hB' hC').toIso ((tateLineCoordinate W.finrank_tate).trans
    ((LinearEquiv.smulOfUnit κ⁻¹).trans (tateLineCoordinate W'.finrank_tate).symm))

/-- The isomorphisms of cohomology of `Θ.toIso` are the extension of `Θ`. -/
theorem gradeEquiv_toIso (κ : Fˣ) (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ)
    (a : W.grade X n) :
    (Θ.toIso hA hB hC hA' hB' hC' κ).gradeEquiv X n a =
      (Θ.toGradedIso hA hB hC hA' hB' hC').e X n a :=
  LinearEquiv.congr_fun (GradedIso.gradeEquiv_toIso _ _ X n) a

/-- In coordinates, `Θ.toIso` on `H^n(X)(m)` is the extension of `Θ` scaled by `κ^{-m}`. -/
theorem twCoord_twEquiv_toIso (κ : Fˣ) (X : (SmoothProjectiveScheme k).FullSubcategory)
    (n m : ℤ) (x : W.Tw X n m) :
    W'.twCoord X n m ((Θ.toIso hA hB hC hA' hB' hC' κ).twEquiv X n m x) =
      ((κ⁻¹ ^ m : Fˣ) : F) • (Θ.toGradedIso hA hB hC hA' hB' hC').e X n (W.twCoord X n m x) := by
  have ht : ((tateLineCoordinate W.finrank_tate).trans
      ((LinearEquiv.smulOfUnit κ⁻¹).trans (tateLineCoordinate W'.finrank_tate).symm)).trans
        (tateLineCoordinate W'.finrank_tate) =
      (tateLineCoordinate W.finrank_tate).trans (LinearEquiv.smulOfUnit κ⁻¹) :=
    LinearEquiv.ext fun l ↦ by simp
  rw [twCoord, Iso.twEquiv, tateTwistCoordinates_tateTwistCongr, toIso, GradedIso.toIso_tateEquiv,
    ht, tateTwistCoordinates_smulOfUnit, map_smul, GradedIso.gradeEquiv_toIso]
  rfl

/-- A unit to a natural power times its inverse to the same power is `1`. -/
private theorem val_inv_zpow_mul_pow (u : Fˣ) (n : ℕ) :
    ((u⁻¹ ^ (n : ℤ) : Fˣ) : F) * (u : F) ^ n = 1 := by
  rw [zpow_natCast, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, inv_mul_cancel,
    one_pow, Units.val_one]

/-- **`Θ.toIso` preserves the cycle class maps**, if `Θ` scales them by `κⁱ` on varieties. -/
theorem toIso_preservesCycleClass (κ : Fˣ) (hγ : ∀ (V : (SmoothProjective k).FullSubcategory)
      (i : ℕ) (β : codimensionChowGroup k ((toSchemeCat k).obj V).obj.hom i),
      Θ.e V (2 * (i : ℤ)) (W.cycleClassCoord _ i β) = (κ : F) ^ i • W'.cycleClassCoord _ i β) :
    (Θ.toIso hA hB hC hA' hB' hC' κ).PreservesCycleClass := by
  intro X i α
  apply (W'.twCoord X _ _).injective
  rw [twCoord_twEquiv_toIso]
  rcases le_or_gt 0 i with hi | hi
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    change W'.cycleClassCoord X n α = ((κ⁻¹ ^ (n : ℤ) : Fˣ) : F) •
      (Θ.toGradedIso hA hB hC hA' hB' hC').e X (2 * (n : ℤ)) (W.cycleClassCoord X n α)
    rw [toGradedIso_cycleClassCoord hA hB hC hA' hB' hC' (κ : F) hγ X n α, smul_smul,
      val_inv_zpow_mul_pow, one_smul]
  · rw [codimensionChowGroup_eq_zero_of_neg X hi α]
    simp

/-- **`Θ.toIso` preserves the trace maps**, if `Θ` scales them by `κ^d` on varieties. -/
theorem toIso_preservesTrace (κ : Fˣ) (htr : ∀ (V : (SmoothProjective k).FullSubcategory) (d : ℕ)
      (hV : IsNonemptyEquidimensional ((toSchemeCat k).obj V) d)
      (a : W.grade ((toSchemeCat k).obj V) (2 * (d : ℤ))),
      W'.traceCoord _ d hV (Θ.e V _ a) = (κ : F) ^ d * W.traceCoord _ d hV a) :
    (Θ.toIso hA hB hC hA' hB' hC' κ).PreservesTrace := by
  intro X d hX a
  rw [trace_eq_traceCoord, trace_eq_traceCoord, twCoord_twEquiv_toIso, map_smul,
    traceCoord_toGradedIso hA hB hC hA' hB' hC' (κ : F) htr X d hX, smul_eq_mul, ← mul_assoc,
    val_inv_zpow_mul_pow, one_mul]

end VarietyGradedIso

end WeilData

end Stacks.WeilCohomology

end
