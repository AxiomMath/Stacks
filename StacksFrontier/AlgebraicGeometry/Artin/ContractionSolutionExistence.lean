module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolution
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionModificationIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence

/-!
# Stacks 0GHC: a representing algebraic space is a solution

In the situation of Stacks 0GH8 (`AlgebraicGeometry.Artin.ContractionSituation`), **Stacks 0GHC**
says: if `X` is an algebraic space locally of finite type over `S` with a functorial bijection
`F(V) = Mor_S(V, X)` on locally Noetherian schemes `V` over `S`, then `X` is a solution, that is,
there are a proper `f : X' ⟶ X`, a closed `T ⊆ |X|` and an isomorphism `a : X_{/T} ≅ W` with
(1) `|f|⁻¹ T = T'`, (2) `f` maps `U'` isomorphically onto an open subspace `U ⊆ X`, and
(3) `g = a ∘ f_{/T}`. This file proves it:
`AlgebraicGeometry.Artin.ContractionSituation.nonempty_solution_of_iso`.

## The proof, and where it departs from the source

`T` is `AlgebraicGeometry.Artin.ContractionSituation.contractedLocus` and `a` is
`AlgebraicGeometry.Artin.ContractionSituation.completionSheafIsoWExt`, as in the source.

**The source's construction of `f` does not work as written.** It sends `x̃ : V ⟶ X'` to the
triple `(x̃⁻¹T', x̃|, g ∘ x̃_{/Z})` and takes `x' = x̃ ∘ (V' ⟶ V)` as compatibility witness. But
the witness must restrict to the *second* projection of `V'_{/Z} = V_{/Z} ×_W X'_{/T'}`, whereas
`x̃ ∘ (V' ⟶ V)` restricts to `x̃_{/Z}` composed with the *first*; the two agree only when the base
change of `g` along `x̂` is an isomorphism, which fails already for `V = X'`, `x̃ = id` and `g` the
completion of the blow-up of the affine plane in the origin along the exceptional curve.

The proof here takes a corrected route which uses `X`:

1. Stacks 0GDU over `X` algebraizes the formal modification `X_{/T} ×_{a, W, g} X'_{/T'} ⟶ X_{/T}`
   (Stacks 0GDN) to a proper `h : X'' ⟶ X`, an isomorphism over `X ∖ T`
   (`AlgebraicGeometry.Artin.ContractionSituation.Algebraization`).
2. The compatibility witnesses which the bijection supplies for the triples of `ξ ∘ h`,
   `ξ : V ⟶ X''`, give a comparison morphism `x'' : X'' ⟶ X'`
   (`AlgebraicGeometry.Artin.ContractionSituation.modificationHom`; Stacks 0GDR, 0AR7, 0GE3).
3. `x''` is locally of finite type, an isomorphism over `U'` and its completion along `T'` is an
   isomorphism (`AlgebraicGeometry.Artin.ContractionSituation.isIso_pullback_snd_modificationHom`,
   `AlgebraicGeometry.Artin.ContractionSituation.completionSheafRestrict_modificationHom`), so
   Stacks 0GDR over `X'` gives a section `φ : X' ⟶ X''` of `x''`, and faithfulness of the same
   functor makes `φ` an inverse of `x''`.
4. `f = h ∘ φ`. Conditions (1), (2), (3) follow from the corresponding properties of `h` and
   `x''`, and `U = X ∖ T`
   (`AlgebraicGeometry.Artin.ContractionSituation.range_pointsMap_solutionOfAlgebraization_U`).

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.solutionOfAlgebraization`: the solution.
* `AlgebraicGeometry.Artin.ContractionSituation.nonempty_solution_of_iso`: **Stacks 0GHC**.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_solution_of_iso_range_U`: the same with
  `|U| = |X| ∖ T`.

## References

* [Stacks Project, Tag 0GDR](https://stacks.math.columbia.edu/tag/0GDR)
* [Stacks Project, Tag 0GDU](https://stacks.math.columbia.edu/tag/0GDU)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHC](https://stacks.math.columbia.edu/tag/0GHC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : contractionFunctor c ≅ morOnLocallyNoetherian B S hS X)
    {hX : IsAlgebraicSpace B S hS X}
    {hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)}
    (A : Algebraization c α hX hft)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `IsIso` and limits in presheaf categories on the big fppf site
/-- The completion `X''_{/|x''|⁻¹T'} ⟶ X'_{/T'}` of `x''` is an isomorphism. -/
theorem isIso_completionSheafMap_modificationHom :
    IsIso (Space.completionSheafMap B S hS (modificationHom c α A) c.T') := by
  have he : IsIso A.eLeft := inferInstanceAs (IsIso ((Over.forget _).map A.e.hom))
  have h1 := completionSheafRestrict_modificationHom c α A
  rw [Space.completionSheafRestrict_eq_eqToHom_comp B S hS _ _ _ _
    (preimage_T'_modificationHom c α A).symm] at h1
  have h2 : Space.completionSheafMap B S hS (modificationHom c α A) c.T' =
      eqToHom (congrArg (Space.completionSheaf B S hS A.Y)
        (preimage_T'_modificationHom c α A)) ≫
        (A.eLeft ≫ pullback.fst c.g (completionSheafIsoWExt c α hX hft).hom) := by
    rw [← h1]; simp
  rw [h2]
  infer_instance

/-- `x''` is locally of finite type. -/
theorem isLocallyOfFiniteType_modificationHom :
    Space.IsLocallyOfFiniteType B S hS (modificationHom c α A) := by
  let e : yoneda.obj (Over.mk (𝟙 (B.obj hS))) ≅ ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    ((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).uniqueUpToIso terminalIsTerminal
  have hT : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    isAlgebraicSpace_of_iso B S hS e.symm (isAlgebraicSpace_yoneda B S hS _)
  refine Space.isLocallyOfFiniteType_of_comp B S hS A.isAlgebraicSpace_Y c.isAlgebraicSpace_X' hT
    (modificationHom c α A) (terminal.from c.X') ?_
  rw [show modificationHom c α A ≫ terminal.from c.X' = terminal.from A.Y from
    terminal.hom_ext _ _]
  exact A.isLocallyOfFiniteType_Y

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `IsIso` and limits in presheaf categories on the big fppf site
/-- **Inverting `x''`, by Stacks 0GDR over `X'`.** There is `φ : X' ⟶ X''` with `φ ∘ x'' = 1`
and `x'' ∘ φ = 1`. -/
theorem exists_inverse_modificationHom :
    ∃ φ : c.X' ⟶ A.Y, φ ≫ modificationHom c α A = 𝟙 _ ∧ modificationHom c α A ≫ φ = 𝟙 _ := by
  have hN := FormalSpace.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyNoetherian
    c.isAlgebraicSpace_X'
    (isLocallyNoetherian_of_isLocallyOfFiniteType_base c c.isLocallyOfFiniteType_X')
  have hNY := FormalSpace.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyNoetherian
    A.isAlgebraicSpace_Y
    (isLocallyNoetherian_of_isLocallyOfFiniteType_base c A.isLocallyOfFiniteType_Y)
  have hfU := isIso_pullback_snd_modificationHom c α A
  have hlft := isLocallyOfFiniteType_modificationHom c α A
  have hiso := isIso_completionSheafMap_modificationHom c α A
  have bij := Space.completionOverFunctor_map_bijective c.isAlgebraicSpace_X' hN c.isClosed_T'
    A.isAlgebraicSpace_Y hlft hfU (𝟙 c.X') c.isAlgebraicSpace_X' hN
  have bij₂ := Space.completionOverFunctor_map_bijective c.isAlgebraicSpace_X' hN c.isClosed_T'
    A.isAlgebraicSpace_Y hlft hfU (modificationHom c α A) A.isAlgebraicSpace_Y hNY
  let invM := @CategoryTheory.inv _ _ _ _
    (Space.completionSheafMap B S hS (modificationHom c α A) c.T') hiso
  have hinv : invM ≫ Space.completionSheafMap B S hS (modificationHom c α A) c.T' = 𝟙 _ :=
    @IsIso.inv_hom_id _ _ _ _ _ hiso
  let τ : (Space.completionOverFunctor B S hS c.T').obj (Over.mk (𝟙 c.X')) ⟶
      (Space.completionOverFunctor B S hS c.T').obj (Over.mk (modificationHom c α A)) :=
    Over.homMk (Space.completionSheafMap B S hS (𝟙 c.X') c.T' ≫ invM)
      (by simp only [Over.mk_hom, Space.completionOverFunctor_obj]; rw [Category.assoc, hinv,
        Category.comp_id])
  obtain ⟨φo, hφo⟩ := bij.2 τ
  have hφo' : (Space.completionOverFunctor B S hS c.T').map φo = τ := hφo
  have hφ : φo.left ≫ modificationHom c α A = 𝟙 _ := by simpa using Over.w φo
  refine ⟨φo.left, hφ, ?_⟩
  let κ : Over.mk (modificationHom c α A) ⟶ Over.mk (𝟙 c.X') :=
    Over.homMk (modificationHom c α A) (by simp)
  let ψo : Over.mk (modificationHom c α A) ⟶ Over.mk (modificationHom c α A) :=
    Over.homMk (modificationHom c α A ≫ φo.left) (by simp [hφ])
  have hψ : ψo = κ ≫ φo := by ext; rfl
  have hmap : (Space.completionOverFunctor B S hS c.T').map ψo =
      (Space.completionOverFunctor B S hS c.T').map (𝟙 _) := by
    rw [hψ, CategoryTheory.Functor.map_comp, hφo', CategoryTheory.Functor.map_id]
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.id_left, τ, Over.homMk_left]
    have hhi : Space.completionSheafMap B S hS (modificationHom c α A) c.T' ≫ invM = 𝟙 _ :=
      @IsIso.hom_inv_id _ _ _ _ _ hiso
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ invM)
      (Over.w ((Space.completionOverFunctor B S hS c.T').map κ))).trans hhi)
  simpa [ψo] using congrArg (fun φ => φ.left) (bij₂.1 hmap)

/-- The inverse `φ : X' ⟶ X''` of `x''`. -/
noncomputable def modificationInv : c.X' ⟶ A.Y :=
  (exists_inverse_modificationHom c α A).choose

/-- `φ` is a section of `x''`. -/
theorem modificationInv_hom : modificationInv c α A ≫ modificationHom c α A = 𝟙 _ :=
  (exists_inverse_modificationHom c α A).choose_spec.1

/-- `φ` is a retraction of `x''`. -/
theorem modificationHom_inv : modificationHom c α A ≫ modificationInv c α A = 𝟙 _ :=
  (exists_inverse_modificationHom c α A).choose_spec.2

/-- The inverse `φ` of `x''` is an isomorphism. -/
instance : IsIso (modificationInv c α A) :=
  ⟨⟨modificationHom c α A, modificationInv_hom c α A, modificationHom_inv c α A⟩⟩

/-- The preimage of `T'` under `|φ ≫ x''|` is `T'`. -/
private theorem preimage_modificationInv_comp_hom :
    Space.pointsMap B S hS c.X' (modificationInv c α A ≫ modificationHom c α A) ⁻¹' c.T' =
      c.T' := by
  rw [modificationInv_hom, Space.pointsMap_id, Set.preimage_id]

/-- Condition (1) for `f = h ∘ φ`. -/
theorem preimage_contractedLocus_modificationInv_comp :
    Space.pointsMap B S hS c.X' (modificationInv c α A ≫ A.h) ⁻¹' contractedLocus c α = c.T' := by
  rw [Space.pointsMap_comp, Set.preimage_comp, ← preimage_T'_modificationHom c α A,
    ← Set.preimage_comp, ← Space.pointsMap_comp]
  exact preimage_modificationInv_comp_hom c α A

/-- The identification of the open parts `X'' ∖ |x''|⁻¹T' = X'' ∖ |h|⁻¹T`. -/
noncomputable def modificationOpenIso :
    (modificationOpen c α A).toFunctor ≅ (modificationOpenH c α A).toFunctor where
  hom := Space.openSubspaceOfPointsRestrict B S hS (𝟙 _) _ _ (modificationOpen_subset c α A)
  inv := Space.openSubspaceOfPointsRestrict B S hS (𝟙 _) _ _ (modificationOpenH_subset c α A)
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The isomorphism `U' ≅ X ∖ T` of condition (2). -/
noncomputable def solutionIsoU :
    c.U'.toFunctor ≅ (Space.openSubspaceOfPoints B S hS X (contractedLocus c α)ᶜ).toFunctor :=
  haveI := Space.isIso_openComplementRestriction B S hS A.h (contractedLocus c α)
    A.isIso_pullback_snd_h
  { hom := modificationOpenInv c α A, inv := modificationOpenRestr c α A,
    hom_inv_id := modificationOpenInv_restr c α A,
    inv_hom_id := modificationOpenRestr_inv c α A } ≪≫ modificationOpenIso c α A ≪≫
    asIso (Space.openComplementRestriction B S hS A.h (contractedLocus c α))

/-- The composite `U' ≅ X ∖ T ⊆ X` is the restriction of `f = h ∘ φ` to `U'`. -/
theorem solutionIsoU_comp_ι :
    (solutionIsoU c α A).hom ≫ (Space.openSubspaceOfPoints B S hS X (contractedLocus c α)ᶜ).ι =
      c.U'.ι ≫ modificationInv c α A ≫ A.h := by
  have hsq := (Space.isPullback_openComplementRestriction B S hS A.h (contractedLocus c α)).w
  simp only [solutionIsoU, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← hsq]
  change modificationOpenInv c α A ≫ (Space.openSubspaceOfPointsRestrict B S hS (𝟙 _) _ _
    (modificationOpen_subset c α A) ≫ (modificationOpenH c α A).ι) ≫ A.h = _
  rw [Space.openSubspaceOfPointsRestrict_comp_ι, Category.comp_id]
  have h1 : modificationOpenInv c α A ≫ (modificationOpen c α A).ι ≫ modificationHom c α A =
      c.U'.ι := by
    rw [← modificationOpenRestr_ι, ← Category.assoc, modificationOpenInv_restr, Category.id_comp]
  have h2 : modificationOpenInv c α A ≫ (modificationOpen c α A).ι =
      c.U'.ι ≫ modificationInv c α A := by
    rw [← h1]
    simp only [Category.assoc, modificationHom_inv, Category.comp_id]
  rw [← Category.assoc, h2, Category.assoc]

set_option synthInstance.maxHeartbeats 400000 in
-- instance search in presheaf categories on the big fppf site (completion sheaf maps)
/-- Condition (3) for `f = h ∘ φ`. -/
theorem completionSheafRestrict_solution_comp_a
    (h : c.T' ⊆ Space.pointsMap B S hS c.X' (modificationInv c α A ≫ A.h) ⁻¹' contractedLocus c α) :
    Space.completionSheafRestrict B S hS (modificationInv c α A ≫ A.h) c.T' (contractedLocus c α)
        h ≫
      (completionSheafIsoWExt c α hX hft).hom = c.g := by
  have h₁ : c.T' ⊆ Space.pointsMap B S hS c.X' (modificationInv c α A) ⁻¹'
      (Space.pointsMap B S hS A.Y A.h ⁻¹' contractedLocus c α) := fun x hx => by
    simpa [Space.pointsMap_comp] using h hx
  rw [Space.completionSheafRestrict_comp B S hS _ _ _ _ _ h₁ (subset_refl _),
    Space.completionSheafRestrict_self, Category.assoc]
  have hw : Space.completionSheafMap B S hS A.h (contractedLocus c α) ≫
      (completionSheafIsoWExt c α hX hft).hom =
        Space.completionSheafRestrict B S hS (modificationHom c α A)
          (Space.pointsMap B S hS A.Y A.h ⁻¹' contractedLocus c α) c.T'
          (contractedLocus_preimage_subset c α A) ≫ c.g := by
    rw [completionSheafRestrict_modificationHom, ← A.eLeft_comp, Category.assoc,
      Category.assoc, contractionModification, ← pullback.condition]
  have hT := (preimage_modificationInv_comp_hom c α A).ge
  rw [hw, ← Category.assoc, ← Space.completionSheafRestrict_comp B S hS _ _ _ _ _ _ _ hT,
    Space.completionSheafRestrict_congr B S hS (modificationInv_hom c α A) c.T' c.T' hT
      (by simp), Space.completionSheafRestrict_id,
    Category.id_comp]

/-- **The solution of Stacks 0GHC**: `f = h ∘ φ : X' ⟶ X''  ⟶ X`, `T` the contracted locus,
`U = X ∖ T` and `a : X_{/T} ≅ W`. -/
noncomputable def solutionOfAlgebraization : Solution c X where
  isAlgebraicSpace_X := hX
  f := modificationInv c α A ≫ A.h
  isProper_f := Space.isProper_comp' B S hS _ _ A.isAlgebraicSpace_Y hX
    (Space.isProper_of_isIso B S hS _) A.isProper_h
  T := contractedLocus c α
  isClosed_T := isClosed_contractedLocus c α hX hft
  preimage_T := preimage_contractedLocus_modificationInv_comp c α A
  U := Space.openSubspaceOfPoints B S hS X (contractedLocus c α)ᶜ
  isOpenSubspace_U := isOpenSubspace_openPart c α (hft := hft) hX
  isoU := solutionIsoU c α A
  isoU_comp_ι := solutionIsoU_comp_ι c α A
  a := completionSheafIsoWExt c α hX hft
  completion_comp_a := completionSheafRestrict_solution_comp_a c α A _

/-- The open subspace `U` of the solution is `X ∖ T`. -/
theorem range_pointsMap_solutionOfAlgebraization_U :
    Set.range (Space.pointsMap B S hS (solutionOfAlgebraization c α A).U.toFunctor
      (solutionOfAlgebraization c α A).U.ι) = (solutionOfAlgebraization c α A).Tᶜ :=
  Space.range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- **Stacks 0GHC, with `|U| = |X| ∖ T`.** In the situation of Stacks 0GH8, an algebraic space `X`
locally of finite type over `S` with a functorial bijection `F(V) = Mor_S(V, X)` on locally
Noetherian schemes `V` over `S` is a solution, by a solution whose open subspace `U` is the
complement of `T`. See `AlgebraicGeometry.Artin.ContractionSituation.nonempty_solution_of_iso`
for the proof and the departure from the source. -/
theorem exists_solution_of_iso_range_U
    (α : contractionFunctor c ≅ morOnLocallyNoetherian B S hS X)
    (hX : IsAlgebraicSpace B S hS X)
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) :
    ∃ s : Solution c X,
      Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ := by
  obtain ⟨A⟩ := nonempty_algebraization c α hX hft
  exact ⟨solutionOfAlgebraization c α A, range_pointsMap_solutionOfAlgebraization_U c α A⟩

/-- **Stacks 0GHC.** In the situation of Stacks 0GH8, if there exist an algebraic space `X`
locally of finite type over `S` and a functorial bijection `F(V) = Mor_S(V, X)` on the category of
locally Noetherian schemes `V` over `S`, then `X` is a solution: there are a proper morphism
`f : X' ⟶ X`, a closed subset `T ⊆ |X|` and an isomorphism `a : X_{/T} ≅ W` such that `T'` is the
inverse image of `T`, `f` maps `U'` isomorphically onto an open subspace `U` of `X`, and
`g = a ∘ f_{/T}`.

The functorial bijection is `α : F ≅ Mor_S(-, X)` with `F` Artin's functor of Stacks 0GHA.

The source's paragraph constructing `f` from a transformation `h_{X'} ⟶ F` is incorrect as
written: its compatibility witness `x' = x̃ ∘ (V' ⟶ V)` restricts on `V'_{/Z}` to the wrong
projection of `V_{/Z} ×_W X'_{/T'}` (already for `V = X'`, `x̃ = id` and `g` the completion of the
blow-up of the affine plane in the origin). The proof takes a corrected route: Stacks 0GDU over `X`
algebraizes the base change of `g` along `a` to `h : X'' ⟶ X`, the witnesses supplied by `α` give
`x'' : X'' ⟶ X'`, Stacks 0GDR over `X'` inverts `x''`, and `f = h ∘ x''⁻¹`. The solution produced
has `U = X ∖ T`, recorded in
`AlgebraicGeometry.Artin.ContractionSituation.exists_solution_of_iso_range_U`. -/
@[stacks 0GHC "the source's construction of f via h_{X'} → F uses the compatibility witness \
x' = x̃ ∘ (V' → V), which is incorrect: it restricts to the wrong projection of \
V_{/Z} ×_W X'_{/T'} (already for g the completion of the blow-up of the plane in the origin, \
V = X', x̃ = id). The proof takes a corrected route through X: 0GDU over X algebraizes the base \
change of g along a, the α-supplied witnesses give X'' → X', and 0GDR over X' inverts it"]
theorem nonempty_solution_of_iso
    (α : contractionFunctor c ≅ morOnLocallyNoetherian B S hS X)
    (hX : IsAlgebraicSpace B S hS X)
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) : c.IsSolution X :=
  (exists_solution_of_iso_range_U c α hX hft).elim fun s _ => ⟨s⟩

end AlgebraicGeometry.Artin.ContractionSituation

end
