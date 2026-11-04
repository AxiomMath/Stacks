module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerTelescope

/-!
# Short exact sequences and cycles of locally finite direct sums

Let `X` be a scheme locally of finite type over the base of a Chow situation. A direct sum
`⨁_j F_j` of coherent `𝒪_X`-modules whose supports form a locally finite family is again
coherent (Stacks 01BY for an infinite direct sum). This file proves the two further facts about
such direct sums that are needed to run an argument on a family of closed subschemes which is
locally finite but possibly infinite, such as the family of Tag 02RW.

* A direct sum of short exact sequences of `𝒪_X`-modules is short exact.
* The `k`-cycle of a locally finite direct sum of objects of `Coh_{≤k}(X)` is the locally finite
  sum of their `k`-cycles: `[⨁_j F_j]_k = ∑_j [F_j]_k`.

## Main definitions

* `Stacks.Chow.sigmaSubtypeShortComplex` — for a predicate `p` on the index type, the split short
  exact sequence `0 ⟶ ⨁_{p j} F_j ⟶ ⨁_j F_j ⟶ ⨁_{¬ p j} F_j ⟶ 0`.
* `Stacks.Chow.sigmaShortComplex` — the direct sum of a family of short complexes.
* `Stacks.Chow.sigmaDimLE` — a locally finite direct sum of objects of `Coh_{≤k}(X)`, as an
  object of `Coh_{≤k}(X)`.

## Main results

* `Stacks.Chow.shortExact_sigmaSubtypeShortComplex` and `Stacks.Chow.shortExact_sigmaShortComplex`
  — the two sequences above are short exact.
* `Stacks.Chow.dimensionLayerCycle_sigmaDimLE_apply` — the coefficient at a point of the cycle of
  a locally finite direct sum is the sum of the coefficients of the cycles of the summands.

## Implementation notes

Only finitely many summands of a locally finite direct sum have a given point `y` in their
support. The direct sum splits as the direct sum of those finitely many summands and of the
others, the second piece having `y` outside its support; the first piece is handled by induction
on the finite set of indices, splitting off one summand at a time.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-! ### Splitting a direct sum along a predicate on the index -/

section Split

variable {J : Type u} (F : J → X.Modules) (p : J → Prop) [DecidablePred p]

/-- The inclusion of the summands indexed by `{j // p j}` into `⨁_j F_j`. -/
def sigmaSubtypeIncl : (∐ fun j : {j // p j} ↦ F j) ⟶ ∐ F :=
  Sigma.desc fun j ↦ Sigma.ι F j.1

/-- The projection of `⨁_j F_j` onto the summands indexed by `{j // ¬ p j}`. -/
def sigmaSubtypeProj : (∐ F) ⟶ ∐ fun j : {j // ¬ p j} ↦ F j :=
  Sigma.desc fun j ↦ if h : p j then 0 else Sigma.ι (fun j : {j // ¬ p j} ↦ F j) ⟨j, h⟩

/-- The retraction of `⨁_j F_j` onto the summands indexed by `{j // p j}`. -/
def sigmaSubtypeRetr : (∐ F) ⟶ ∐ fun j : {j // p j} ↦ F j :=
  Sigma.desc fun j ↦ if h : p j then Sigma.ι (fun j : {j // p j} ↦ F j) ⟨j, h⟩ else 0

/-- The inclusion of the summands indexed by `{j // ¬ p j}` into `⨁_j F_j`. -/
def sigmaSubtypeSect : (∐ fun j : {j // ¬ p j} ↦ F j) ⟶ ∐ F :=
  Sigma.desc fun j ↦ Sigma.ι F j.1

omit [DecidablePred p] in
/-- The inclusion `Stacks.Chow.sigmaSubtypeIncl` restricts to the coprojection on each summand. -/
@[reassoc (attr := simp)]
theorem ι_sigmaSubtypeIncl (j : {j // p j}) :
    Sigma.ι (fun j : {j // p j} ↦ F j) j ≫ sigmaSubtypeIncl F p = Sigma.ι F j.1 :=
  Sigma.ι_desc _ _

omit [DecidablePred p] in
/-- The inclusion `Stacks.Chow.sigmaSubtypeSect` restricts to the coprojection on each summand. -/
@[reassoc (attr := simp)]
theorem ι_sigmaSubtypeSect (j : {j // ¬ p j}) :
    Sigma.ι (fun j : {j // ¬ p j} ↦ F j) j ≫ sigmaSubtypeSect F p = Sigma.ι F j.1 :=
  Sigma.ι_desc _ _

/-- The projection `Stacks.Chow.sigmaSubtypeProj` vanishes on a summand `F_j` with `p j`. -/
@[reassoc]
theorem ι_sigmaSubtypeProj_of_pos (j : J) (h : p j) : Sigma.ι F j ≫ sigmaSubtypeProj F p = 0 := by
  rw [sigmaSubtypeProj, Sigma.ι_desc, dif_pos h]

/-- The projection `Stacks.Chow.sigmaSubtypeProj` is the coprojection on a summand `F_j` with
`¬ p j`. -/
@[reassoc]
theorem ι_sigmaSubtypeProj_of_neg (j : J) (h : ¬ p j) :
    Sigma.ι F j ≫ sigmaSubtypeProj F p = Sigma.ι (fun j : {j // ¬ p j} ↦ F j) ⟨j, h⟩ := by
  rw [sigmaSubtypeProj, Sigma.ι_desc, dif_neg h]

/-- The retraction `Stacks.Chow.sigmaSubtypeRetr` is the coprojection on a summand `F_j` with
`p j`. -/
@[reassoc]
theorem ι_sigmaSubtypeRetr_of_pos (j : J) (h : p j) :
    Sigma.ι F j ≫ sigmaSubtypeRetr F p = Sigma.ι (fun j : {j // p j} ↦ F j) ⟨j, h⟩ := by
  rw [sigmaSubtypeRetr, Sigma.ι_desc, dif_pos h]

/-- The retraction `Stacks.Chow.sigmaSubtypeRetr` vanishes on a summand `F_j` with `¬ p j`. -/
@[reassoc]
theorem ι_sigmaSubtypeRetr_of_neg (j : J) (h : ¬ p j) : Sigma.ι F j ≫ sigmaSubtypeRetr F p = 0 := by
  rw [sigmaSubtypeRetr, Sigma.ι_desc, dif_neg h]

/-- The composite `⨁_{p j} F_j ⟶ ⨁_j F_j ⟶ ⨁_{¬ p j} F_j` is zero. -/
theorem sigmaSubtypeIncl_comp_proj : sigmaSubtypeIncl F p ≫ sigmaSubtypeProj F p = 0 :=
  Sigma.hom_ext _ _ fun j ↦ by
    rw [ι_sigmaSubtypeIncl_assoc, ι_sigmaSubtypeProj_of_pos F p j.1 j.2, comp_zero]

/-- The sequence `0 ⟶ ⨁_{p j} F_j ⟶ ⨁_j F_j ⟶ ⨁_{¬ p j} F_j ⟶ 0`. -/
def sigmaSubtypeShortComplex : ShortComplex X.Modules :=
  ShortComplex.mk (sigmaSubtypeIncl F p) (sigmaSubtypeProj F p) (sigmaSubtypeIncl_comp_proj F p)

/-- The decomposition of `⨁_j F_j` into the summands with `p j` and those with `¬ p j`, read as a
splitting of `Stacks.Chow.sigmaSubtypeShortComplex`. -/
def sigmaSubtypeSplitting : (sigmaSubtypeShortComplex F p).Splitting where
  r := sigmaSubtypeRetr F p
  s := sigmaSubtypeSect F p
  f_r := Sigma.hom_ext _ _ fun j ↦ by
    change Sigma.ι (fun j : {j // p j} ↦ F j) j ≫ sigmaSubtypeIncl F p ≫ sigmaSubtypeRetr F p =
      Sigma.ι (fun j : {j // p j} ↦ F j) j ≫ 𝟙 _
    rw [ι_sigmaSubtypeIncl_assoc, ι_sigmaSubtypeRetr_of_pos F p j.1 j.2, Category.comp_id]
  s_g := Sigma.hom_ext _ _ fun j ↦ by
    change Sigma.ι (fun j : {j // ¬ p j} ↦ F j) j ≫ sigmaSubtypeSect F p ≫ sigmaSubtypeProj F p =
      Sigma.ι (fun j : {j // ¬ p j} ↦ F j) j ≫ 𝟙 _
    rw [ι_sigmaSubtypeSect_assoc, ι_sigmaSubtypeProj_of_neg F p j.1 j.2, Category.comp_id]
  id := Sigma.hom_ext _ _ fun j ↦ by
    change Sigma.ι F j ≫ (sigmaSubtypeRetr F p ≫ sigmaSubtypeIncl F p +
      sigmaSubtypeProj F p ≫ sigmaSubtypeSect F p) = Sigma.ι F j ≫ 𝟙 _
    rw [Preadditive.comp_add, Category.comp_id]
    by_cases h : p j
    · rw [ι_sigmaSubtypeRetr_of_pos_assoc F p j h, ι_sigmaSubtypeProj_of_pos_assoc F p j h,
        ι_sigmaSubtypeIncl, zero_comp, add_zero]
    · rw [ι_sigmaSubtypeRetr_of_neg_assoc F p j h, ι_sigmaSubtypeProj_of_neg_assoc F p j h,
        ι_sigmaSubtypeSect, zero_comp, zero_add]

/-- **A direct sum is the direct sum of the summands with `p j` and those with `¬ p j`.** -/
theorem shortExact_sigmaSubtypeShortComplex : (sigmaSubtypeShortComplex F p).ShortExact :=
  (sigmaSubtypeSplitting F p).shortExact

end Split

/-! ### The direct sum of a family of short exact sequences -/

section SigmaMap

variable {J : Type u} (E : J → ShortComplex X.Modules)

/-- The composite `⨁_j E_j.X₁ ⟶ ⨁_j E_j.X₂ ⟶ ⨁_j E_j.X₃` of the direct sums of the maps of a
family of short complexes is zero. -/
theorem sigmaMap_f_comp_sigmaMap_g :
    (Limits.Sigma.map fun j ↦ (E j).f) ≫ (Limits.Sigma.map fun j ↦ (E j).g) = 0 :=
  Sigma.hom_ext _ _ fun j ↦ by simp

/-- The direct sum `⨁_j E_j` of a family of short complexes of `𝒪_X`-modules. -/
def sigmaShortComplex : ShortComplex X.Modules :=
  ShortComplex.mk _ _ (sigmaMap_f_comp_sigmaMap_g E)

/-- **A direct sum of short exact sequences of `𝒪_X`-modules is short exact.** A direct sum of
monomorphisms is a monomorphism, coproducts being stable under monomorphisms in `X.Modules`; and
a morphism out of `⨁_j E_j.X₂` killing `⨁_j E_j.X₁` is a family of morphisms out of the
`E_j.X₂` killing the `E_j.X₁`, hence a family of morphisms out of the cokernels `E_j.X₃`. -/
theorem shortExact_sigmaShortComplex (hE : ∀ j, (E j).ShortExact) :
    (sigmaShortComplex E).ShortExact := by
  have hmono : ∀ j, Mono (E j).f := fun j ↦ (hE j).mono_f
  have hepi : ∀ j, Epi (E j).g := fun j ↦ (hE j).epi_g
  have hm : Mono (Limits.Sigma.map fun j ↦ (E j).f) :=
    MorphismProperty.instMonoMapOfIsStableUnderCoproductsOfShapeMonomorphisms J
      fun j ↦ (E j).f
  have he : Epi (Limits.Sigma.map fun j ↦ (E j).g) :=
    ⟨fun {_} g h hgh ↦ Sigma.hom_ext _ _ fun j ↦ (cancel_epi (E j).g).1 <| by
      rw [← Limits.Sigma.ι_map_assoc (fun j ↦ (E j).g), hgh, Limits.Sigma.ι_map_assoc]⟩
  have hk : ∀ {W : X.Modules} (g' : (∐ fun j ↦ (E j).X₂) ⟶ W),
      (Limits.Sigma.map fun j ↦ (E j).f) ≫ g' = 0 →
        ∀ j, (E j).f ≫ Sigma.ι (fun j ↦ (E j).X₂) j ≫ g' = 0 := by
    intro W g' hg' j
    rw [← Limits.Sigma.ι_map_assoc (fun j ↦ (E j).f), hg', comp_zero]
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ ?_) hm he
  refine CokernelCofork.IsColimit.ofπ (f := Limits.Sigma.map fun j ↦ (E j).f)
    (Limits.Sigma.map fun j ↦ (E j).g) (sigmaMap_f_comp_sigmaMap_g E)
    (fun {W} g' hg' ↦ Sigma.desc fun j ↦
      (hE j).exact.desc (Sigma.ι (fun j ↦ (E j).X₂) j ≫ g') (hk g' hg' j))
    (fun {W} g' hg' ↦ Sigma.hom_ext _ _ fun j ↦ by
      rw [Limits.Sigma.ι_map_assoc, Sigma.ι_desc, (hE j).exact.g_desc])
    (fun {W} g' hg' m hm' ↦ Sigma.hom_ext _ _ fun j ↦ by
      rw [Sigma.ι_desc]
      refine (cancel_epi (E j).g).1 ?_
      rw [(hE j).exact.g_desc, ← hm', Limits.Sigma.ι_map_assoc])

end SigmaMap

/-! ### The cycle of a locally finite direct sum -/

variable (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)

/-- Objects of `Coh_{≤k}(X)` with isomorphic underlying `𝒪_X`-modules have the same cycle. -/
theorem dimensionLayerCycle_eq_of_moduleIso (M N : CoherentModulesDimLE C f k)
    (e : M.obj.obj ≅ N.obj.obj) : dimensionLayerCycle C f k M = dimensionLayerCycle C f k N := by
  have h := congrArg (dimensionLayerCycleHom C f k) (GrothendieckGroup.of_eq_of_iso
    (((lowerDimensionClass C f (k - 1) k).isoModSerre.Q).mapIso
      (dimLEIsoOfModuleIso C f k M N e)))
  simpa only [dimensionLayerCycleHom_of] using h

/-- The cycle of an object of `Coh_{≤k}(X)` vanishes at every point outside the support of the
underlying module. -/
theorem dimensionLayerCycle_apply_of_notMem_supp (M : CoherentModulesDimLE C f k) {y : X}
    (hy : y ∉ SheafOfModules.supp M.obj.obj) : (dimensionLayerCycle C f k M).1 y = 0 := by
  by_cases hd : relativeDimension C.dimensionFunction f y = k
  · rw [dimensionLayerCycle_apply_of_relativeDimension_eq C f k M hd]
    exact sheafMultiplicity_eq_zero_of_notMem_supp _ hy
  · have hc : _root_.SheafOfModules.IsCoherent M.obj.obj :=
      AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent M.obj.property
    exact cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f M.obj.obj k
      M.property hd

/-- A locally finite direct sum of objects of `Coh_{≤k}(X)`, as an object of `Coh_{≤k}(X)`: it is
coherent by Stacks 01BY for an infinite direct sum, and its support lies in the union of the
supports of the summands. -/
def sigmaDimLE {J : Type u} (F : J → CoherentModulesDimLE C f k)
    (hLF : LocallyFinite fun j ↦ SheafOfModules.supp (F j).obj.obj) :
    CoherentModulesDimLE C f k :=
  dimLEObj C f k (∐ fun j ↦ (F j).obj.obj)
    (isCoherent_coproduct_of_locallyFinite _
      (fun j ↦ AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent (F j).obj.property)
      hLF)
    (fun x hx ↦ by
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (supp_sigma_subset_iUnion_supp _ hx)
      exact relativeDimension_le_of_mem_supp_dimLE C f k (F j) x hj)

/-- The underlying `𝒪_X`-module of `Stacks.Chow.sigmaDimLE` is the direct sum `⨁_j F_j`. -/
theorem sigmaDimLE_obj_obj {J : Type u} (F : J → CoherentModulesDimLE C f k)
    (hLF : LocallyFinite fun j ↦ SheafOfModules.supp (F j).obj.obj) :
    (sigmaDimLE C f k F hLF).obj.obj = ∐ fun j ↦ (F j).obj.obj :=
  rfl

/-- A point outside the supports of all the summands is outside the support of the direct sum, so
the cycle of the direct sum vanishes there. -/
theorem dimensionLayerCycle_sigmaDimLE_apply_of_forall_notMem {J : Type u}
    (F : J → CoherentModulesDimLE C f k)
    (hLF : LocallyFinite fun j ↦ SheafOfModules.supp (F j).obj.obj) {y : X}
    (hy : ∀ j, y ∉ SheafOfModules.supp (F j).obj.obj) :
    (dimensionLayerCycle C f k (sigmaDimLE C f k F hLF)).1 y = 0 :=
  dimensionLayerCycle_apply_of_notMem_supp C f k _ fun hmem ↦ by
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (supp_sigma_subset_iUnion_supp _ hmem)
    exact hy j hj

/-- The cycle of a direct sum is the sum of the cycles of the summands with `p j` and of those
with `¬ p j`. -/
theorem dimensionLayerCycle_sigmaDimLE_eq_add {J : Type u} (F : J → CoherentModulesDimLE C f k)
    (hLF : LocallyFinite fun j ↦ SheafOfModules.supp (F j).obj.obj) (p : J → Prop) :
    dimensionLayerCycle C f k (sigmaDimLE C f k F hLF) =
      dimensionLayerCycle C f k (sigmaDimLE C f k (fun j : {j // p j} ↦ F j)
        (hLF.comp_injective Subtype.val_injective)) +
      dimensionLayerCycle C f k (sigmaDimLE C f k (fun j : {j // ¬ p j} ↦ F j)
        (hLF.comp_injective Subtype.val_injective)) := by
  classical
  exact dimensionLayerCycle_add_of_shortExact C f k _ _ _ _ _ _
    (shortExact_sigmaSubtypeShortComplex (fun j ↦ (F j).obj.obj) p)

/-- The cycle of the direct sum of a finite subfamily is the sum of the cycles of its members. -/
theorem dimensionLayerCycle_sigmaDimLE_finset {J : Type u} (F : J → CoherentModulesDimLE C f k)
    (hLF : LocallyFinite fun j ↦ SheafOfModules.supp (F j).obj.obj) (T : Finset J) (y : X) :
    (dimensionLayerCycle C f k (sigmaDimLE C f k (fun j : {j // j ∈ T} ↦ F j)
      (hLF.comp_injective Subtype.val_injective))).1 y =
      ∑ j ∈ T, (dimensionLayerCycle C f k (F j)).1 y := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact dimensionLayerCycle_sigmaDimLE_apply_of_forall_notMem C f k _ _ fun j ↦
      absurd j.2 (Finset.notMem_empty _)
  | @insert a T ha ih =>
    rw [Finset.sum_insert ha, dimensionLayerCycle_sigmaDimLE_eq_add C f k _ _
      (fun j : {j // j ∈ insert a T} ↦ j.1 = a), cycleGroup_add_apply]
    have h₁ : (dimensionLayerCycle C f k (sigmaDimLE C f k
        (fun j : {j : {j // j ∈ insert a T} // j.1 = a} ↦ F j.1.1)
        ((hLF.comp_injective Subtype.val_injective).comp_injective Subtype.val_injective))).1 y =
          (dimensionLayerCycle C f k (F a)).1 y := by
      let : Unique {j : {j // j ∈ insert a T} // j.1 = a} :=
        ⟨⟨⟨⟨a, Finset.mem_insert_self a T⟩, rfl⟩⟩,
          fun ⟨⟨_, _⟩, hba⟩ ↦ Subtype.ext (Subtype.ext hba)⟩
      let M₁ := sigmaDimLE C f k (fun j : {j : {j // j ∈ insert a T} // j.1 = a} ↦ F j.1.1)
        ((hLF.comp_injective Subtype.val_injective).comp_injective Subtype.val_injective)
      have hiso : (∐ fun j : {j : {j // j ∈ insert a T} // j.1 = a} ↦ (F j.1.1).obj.obj) ≅
          (F a).obj.obj :=
        coproductUniqueIso fun j : {j : {j // j ∈ insert a T} // j.1 = a} ↦ (F j.1.1).obj.obj
      rw [dimensionLayerCycle_eq_of_moduleIso C f k M₁ (F a) hiso]
    let e : {j : {j // j ∈ insert a T} // ¬ j.1 = a} ≃ {j // j ∈ T} :=
      { toFun := fun j ↦ ⟨j.1.1, (Finset.mem_insert.1 j.1.2).resolve_left j.2⟩
        invFun := fun j ↦ ⟨⟨j.1, Finset.mem_insert_of_mem j.2⟩, fun h ↦ ha (h ▸ j.2)⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have hiso : (∐ fun j : {j : {j // j ∈ insert a T} // ¬ j.1 = a} ↦ (F j.1.1).obj.obj) ≅
        ∐ fun j : {j // j ∈ T} ↦ (F j).obj.obj :=
      Sigma.whiskerEquiv (f := fun j : {j : {j // j ∈ insert a T} // ¬ j.1 = a} ↦ (F j.1.1).obj.obj)
        (g := fun j : {j // j ∈ T} ↦ (F j).obj.obj) e fun _ ↦ Iso.refl _
    have h₂ := dimensionLayerCycle_eq_of_moduleIso C f k
      (sigmaDimLE C f k (fun j : {j : {j // j ∈ insert a T} // ¬ j.1 = a} ↦ F j.1.1)
        ((hLF.comp_injective Subtype.val_injective).comp_injective Subtype.val_injective))
      (sigmaDimLE C f k (fun j : {j // j ∈ T} ↦ F j) (hLF.comp_injective Subtype.val_injective))
      hiso
    rw [h₁, h₂, ih]

/-- **The cycle of a locally finite direct sum is the sum of the cycles of the summands.** For a
family of objects of `Coh_{≤k}(X)` whose supports form a locally finite family, the coefficient
at any point `y` of `[⨁_j F_j]_k` is `∑_j` of the coefficients at `y` of the `[F_j]_k`, a sum with
only finitely many nonzero terms.

Only the finitely many summands with `y` in their support contribute: the direct sum splits as the
direct sum of those and of the others, the second piece having `y` outside its support. -/
theorem dimensionLayerCycle_sigmaDimLE_apply {J : Type u} (F : J → CoherentModulesDimLE C f k)
    (hLF : LocallyFinite fun j ↦ SheafOfModules.supp (F j).obj.obj) (y : X) :
    (dimensionLayerCycle C f k (sigmaDimLE C f k F hLF)).1 y =
      ∑ᶠ j, (dimensionLayerCycle C f k (F j)).1 y := by
  classical
  set T : Finset J := (hLF.point_finite y).toFinset with hT
  have hmem : ∀ j, j ∈ T ↔ y ∈ SheafOfModules.supp (F j).obj.obj := fun j ↦
    (hLF.point_finite y).mem_toFinset
  have h₀ := dimensionLayerCycle_sigmaDimLE_apply_of_forall_notMem C f k
    (fun j : {j // ¬ j ∈ T} ↦ F j) (hLF.comp_injective Subtype.val_injective) (y := y)
    fun j h ↦ j.2 ((hmem j.1).2 h)
  rw [dimensionLayerCycle_sigmaDimLE_eq_add C f k F hLF (fun j ↦ j ∈ T), cycleGroup_add_apply,
    h₀, add_zero, dimensionLayerCycle_sigmaDimLE_finset C f k F hLF T]
  refine (finsum_eq_sum_of_support_subset _ fun j hj ↦ ?_).symm
  by_contra hjT
  exact hj (dimensionLayerCycle_apply_of_notMem_supp C f k (F j) fun h ↦ hjT ((hmem j).2 h))

end Stacks.Chow

end
