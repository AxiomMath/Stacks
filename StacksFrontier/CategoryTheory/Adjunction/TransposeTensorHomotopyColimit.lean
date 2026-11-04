module

public import StacksFrontier.Algebra.Homology.DerivedCategory.HomotopyColimitComparison

/-!
# Transposed tensor maps, and their comparison on homotopy colimits

Abstract bookkeeping for [Stacks, Tag 0CX8]. Let `ext ⊣ res` be an adjunction `𝒜 ⇄ 𝒜₀`,
`TX : 𝒳 ⥤ 𝒳 ⥤ 𝒳` a bifunctor, `GA : 𝒳 ⥤ 𝒜` and `Q : 𝒳 ⥤ 𝒜₀` functors, `φ : K ⟶ G` and
`ψ : TX(-, G) ⋙ GA ⟶ Q ⋙ res`. The **transposed tensor map** at `E` is the adjoint of
`GA(E ⊗ φ) ≫ ψ_E`, a map `ext(GA(E ⊗ K)) ⟶ Q(E)`; it is natural in `E`.

Given moreover `P : 𝒳`, a transformation `π : TX(P, -) ⋙ GA ⟶ Lj ⋙ GU` invertible at `G` (`hπ`)
and a map
`π' : Q(P) ⟶ Y`, the **transposed unit map** is the adjoint of `GU(Lj φ) ≫ π_G⁻¹ ≫ ψ_P ≫ res π'`.
If `P` is a homotopy colimit of objects `Eₘ` through maps `cₘ` such that `ext(GA(cₘ ⊗ K)) ≫ π_K`
and `Q(cₘ) ≫ π'` exhibit homotopy colimits, and the transposed tensor maps at the `Eₘ` are
invertible, then the transposed unit map is invertible.

## Main definitions

* `CategoryTheory.transposeTensorMap`, `CategoryTheory.transposeUnitMap`.

## Main results

* `CategoryTheory.transposeTensorMap_naturality`.
* `CategoryTheory.isIso_transposeUnitMap`.
* `CategoryTheory.Pretriangulated.IsHomotopyColimit.hasCoproduct`: the direct sum occurring in a
  homotopy colimit statement, as a term.
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Category _root_.CategoryTheory.Functor Limits Pretriangulated

variable {𝒳 𝒰 𝒜 𝒜₀ : Type*} [Category 𝒳] [Category 𝒰] [Category 𝒜] [Category 𝒜₀]
  (TX : 𝒳 ⥤ 𝒳 ⥤ 𝒳) (GA : 𝒳 ⥤ 𝒜) (Lj : 𝒳 ⥤ 𝒰) (GU : 𝒰 ⥤ 𝒜) {ext : 𝒜 ⥤ 𝒜₀} {res : 𝒜₀ ⥤ 𝒜}
  (adj : ext ⊣ res) (Q : 𝒳 ⥤ 𝒜₀) {G K P : 𝒳} (φ : K ⟶ G) (ψ : TX.flip.obj G ⋙ GA ⟶ Q ⋙ res)
  (π : TX.obj P ⋙ GA ⟶ Lj ⋙ GU) (hπ : IsIso (π.app G)) {Y : 𝒜₀} (π' : Q.obj P ⟶ Y)

/-- The adjoint of `GA(E ⊗ φ) ≫ ψ_E`. -/
def transposeTensorMap (E : 𝒳) : ext.obj (GA.obj ((TX.obj E).obj K)) ⟶ Q.obj E :=
  (adj.homEquiv _ _).symm (GA.map ((TX.obj E).map φ) ≫ ψ.app E)

/-- The adjoint of `GU(Lj φ) ≫ π_G⁻¹ ≫ ψ_P ≫ res π'`. -/
def transposeUnitMap : ext.obj (GU.obj (Lj.obj K)) ⟶ Y :=
  (adj.homEquiv _ _).symm (GU.map (Lj.map φ) ≫ @inv _ _ _ _ _ hπ ≫ ψ.app P ≫ res.map π')

/-- **The transposed tensor map is natural.** -/
theorem transposeTensorMap_naturality {E₁ E₂ : 𝒳} (u : E₁ ⟶ E₂) :
    ext.map (GA.map ((TX.flip.obj K).map u)) ≫ transposeTensorMap TX GA adj Q φ ψ E₂ =
      transposeTensorMap TX GA adj Q φ ψ E₁ ≫ Q.map u := by
  dsimp only [transposeTensorMap, Functor.flip_obj_map]
  refine ((adj.homEquiv_naturality_left_symm _ _).symm.trans ?_).trans
    (adj.homEquiv_naturality_right_symm _ _)
  congr 1
  have hψ := ψ.naturality u
  simp only [Functor.comp_map, Functor.flip_obj_map, Functor.flip_obj_obj] at hψ
  rw [← GA.map_comp_assoc, ← (TX.map u).naturality φ, GA.map_comp, assoc, hψ, assoc]

/-- **The transposed unit map after a coprojection** `cₘ : E ⟶ P` is the transposed tensor map at
`E` followed by `Q(c) ≫ π'`. -/
theorem transposeUnitMap_comp {E : 𝒳} (c : E ⟶ P) :
    ext.map (GA.map ((TX.flip.obj K).map c) ≫ π.app K) ≫
        transposeUnitMap TX GA Lj GU adj Q φ ψ π hπ π' =
      transposeTensorMap TX GA adj Q φ ψ E ≫ Q.map c ≫ π' := by
  have := hπ
  dsimp only [transposeTensorMap, transposeUnitMap, Functor.flip_obj_map]
  refine ((adj.homEquiv_naturality_left_symm _ _).symm.trans ?_).trans
    (adj.homEquiv_naturality_right_symm _ _)
  congr 1
  have hπK : π.app K ≫ GU.map (Lj.map φ) = GA.map ((TX.obj P).map φ) ≫ π.app G := by
    simpa only [Functor.comp_map] using (π.naturality φ).symm
  have hψ := ψ.naturality c
  simp only [Functor.comp_map, Functor.flip_obj_map, Functor.flip_obj_obj] at hψ
  rw [assoc, reassoc_of% hπK, IsIso.hom_inv_id_assoc, ← GA.map_comp_assoc,
    ← (TX.map c).naturality φ, GA.map_comp, assoc, reassoc_of% hψ, Functor.map_comp, assoc]

/-- **The transposed unit map is invertible** when the transposed tensor maps at the terms of a
homotopy colimit presentation of `P` are, both sides carrying the presentation to homotopy
colimits. -/
theorem isIso_transposeUnitMap {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete ℕ) (DerivedCategory.homologyFunctor C n)]
    {ext : 𝒜 ⥤ DerivedCategory C} {res : DerivedCategory C ⥤ 𝒜} (adj : ext ⊣ res)
    (Q : 𝒳 ⥤ DerivedCategory C) (ψ : TX.flip.obj G ⋙ GA ⟶ Q ⋙ res)
    {Y : DerivedCategory C} (π' : Q.obj P ⟶ Y) (E : ℕ ⥤ 𝒳) (c : ∀ m, E.obj m ⟶ P)
    [HasCoproduct ((E ⋙ TX.flip.obj K ⋙ GA) ⋙ ext).obj] [HasCoproduct (E ⋙ Q).obj]
    (hc : IsHomotopyColimitCocone ((E ⋙ TX.flip.obj K ⋙ GA) ⋙ ext)
      fun m ↦ ext.map (GA.map ((TX.flip.obj K).map (c m)) ≫ π.app K))
    (hc' : IsHomotopyColimitCocone (E ⋙ Q) fun m ↦ Q.map (c m) ≫ π')
    (hiso : ∀ m, IsIso (transposeTensorMap TX GA adj Q φ ψ (E.obj m))) :
    IsIso (transposeUnitMap TX GA Lj GU adj Q φ ψ π hπ π') :=
  DerivedCategory.isIso_of_isHomotopyColimitCocone_of_iso hc hc'
    (NatIso.ofComponents (fun m ↦ asIso (transposeTensorMap TX GA adj Q φ ψ (E.obj m)))
      fun u ↦ transposeTensorMap_naturality TX GA adj Q φ ψ (E.map u))
    _ fun m ↦ transposeUnitMap_comp TX GA Lj GU adj Q φ ψ π hπ π' (c m)

end CategoryTheory

namespace CategoryTheory.Pretriangulated

variable {D : Type*} [Category D] [Preadditive D] [Limits.HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The direct sum of the system of a homotopy colimit, as an instance one can name: the
`HasCoproduct` instance occurring in the statement `h`. -/
theorem IsHomotopyColimit.hasCoproduct {F : ℕ ⥤ D} {inst : Limits.HasCoproduct F.obj} {K : D}
    (_ : @IsHomotopyColimit D _ _ _ _ _ _ F inst K) : Limits.HasCoproduct F.obj :=
  inst

end CategoryTheory.Pretriangulated
