module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismAssociatedPoints.Flat
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningInjectiveStalk
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeMapSectionsInjectivity
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankStalkBasis
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankLocusPullback
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.Stalks
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.InjectivityOnClosedFibre
public import StacksFrontier.AlgebraicGeometry.Modules.StalkFreePullback
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociatedFieldExtension
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankLocus
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Free maps which are injective at the generic points of the fibres

Let `g : Y ⟶ T` be flat, locally of finite type, with geometrically integral fibres, and let
`α : 𝒪_Y^{⊕ n} ⟶ M` be a map of modules. If `α` is injective on the stalk at the generic point
of every fibre, then `α` is injective.

## Main results

* `AlgebraicGeometry.mono_of_injective_stalk_genericPoint_fiber`: the statement above.

## Implementation notes

A weakly associated point of `𝒪_Y^{⊕ n}` is weakly associated to `𝒪_Y`, the stalk being a free
module over the local ring; by flatness of `𝒪_Y` over `T` (Stacks 05IJ at `𝒢 = 𝒪_T`) it lies in
the relative assassin of `𝒪_Y`, so it is an associated point of the structure sheaf of its
fibre, which is integral, and the only such point is the generic point. Injectivity at the
weakly associated points of the source is enough (Stacks 05AP, 05AN).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A point weakly associated to a finite free module is weakly associated to the scheme: the
stalk is free over the local ring, and a prime weakly associated to a direct sum of copies of the
ring is weakly associated to the ring. -/
theorem mem_schemeWeaklyAssociatedPoints_of_coproductUnit {Y : Scheme.{u}} {n : ℕ} {y : Y}
    (hy : y ∈ Stacks.Divisors.weaklyAssociatedPoints
      (∐ fun _ : Fin n => SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) :
    y ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints Y := by
  have hfree := Stacks.StalkFreeBridge.free_stalk_coproductUnit (X := Y) n y
  let b := Module.Free.chooseBasis (Y.presheaf.stalk y)
    ((∐ fun _ : Fin n => SheafOfModules.unit Y.ringCatSheaf : Y.Modules).presheaf.stalk y)
  have h1 : IsWeaklyAssociatedPrime (Y.presheaf.stalk y)
      (Module.Free.ChooseBasisIndex (Y.presheaf.stalk y)
        ((∐ fun _ : Fin n => SheafOfModules.unit Y.ringCatSheaf : Y.Modules).presheaf.stalk y)
        →₀ Y.presheaf.stalk y) (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) :=
    (LinearEquiv.isWeaklyAssociatedPrime_iff b.repr _).mp hy
  rw [Stacks.Divisors.mem_schemeWeaklyAssociatedPoints_iff]
  exact (LinearEquiv.isWeaklyAssociatedPrime_iff (structureSheafStalkLinearEquiv Y y) _).mpr
    (IsWeaklyAssociatedPrime.of_finsupp h1)

/-- On an integral scheme the only associated point of the structure sheaf is the generic
point. -/
theorem eq_genericPoint_of_mem_associatedPoints_unit {Z : Scheme.{u}} [IsIntegral Z] (z : Z)
    (hz : z ∈ Stacks.Divisors.associatedPoints (SheafOfModules.unit Z.ringCatSheaf)) :
    z = genericPoint Z := by
  have hweak : z ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints Z := by
    simpa [Stacks.Divisors.schemeWeaklyAssociatedPoints] using
      Stacks.Divisors.associatedPoints_subset (SheafOfModules.unit Z.ringCatSheaf) hz
  rw [weaklyAssociatedPointsOfScheme_eq_genericPoints Z, genericPoints_eq_singleton] at hweak
  simpa using hweak

/-- **A free map injective at the generic points of the fibres is injective.** -/
theorem mono_of_injective_stalk_genericPoint_fiber {Y T : Scheme.{u}} (g : Y ⟶ T) [Flat g]
    [LocallyOfFiniteType g] [GeometricallyIntegral g] {n : ℕ} {M : Y.Modules}
    (α : (∐ fun _ : Fin n => SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ M)
    (hα : ∀ t : T, Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
      (g.fiberι t (genericPoint (g.fiber t)))).map ((Scheme.Modules.toPresheaf Y).map α)).hom) :
    Mono α := by
  refine mono_of_stalk_injective_on_weaklyAssociatedPoints_of_source_quasicoherent α ?_
  intro y hy
  have h2 : y ∈ Stacks.Divisors.relativeAssassin g (SheafOfModules.unit Y.ringCatSheaf) :=
    mem_relativeAssassin_of_isWeaklyAssociatedPoint_of_flat g _ y
      (isFlatOver_structureSheafModule g y) (mem_schemeWeaklyAssociatedPoints_of_coproductUnit hy)
  obtain ⟨t, y', hy', rfl⟩ := (Stacks.Divisors.mem_relativeAssassin g _ y).mp h2
  have hy'' : y' ∈ Stacks.Divisors.associatedPoints
      (SheafOfModules.unit (g.fiber t).ringCatSheaf) :=
    associatedPoints_subset_of_mono (Scheme.Modules.pullbackUnitIso (g.fiberι t)).hom hy'
  rw [eq_genericPoint_of_mem_associatedPoints_unit y' hy'']
  exact hα t

/-- A finite free module is free of its rank near every point. -/
theorem freeAtPointOfRank_coproductUnit {Y : Scheme.{u}} (n : ℕ) (y : Y) :
    FreeAtPointOfRank (∐ fun _ : Fin n => SheafOfModules.unit Y.ringCatSheaf : Y.Modules) y n := by
  have h2 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (∐ fun _ : Fin n => SheafOfModules.unit Y.ringCatSheaf : Y.Modules) n :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (Stacks.StalkFreeBridge.coproductUnitIsoFree n).symm
      (SheafOfModules.isFiniteLocallyFreeOfRank_free.{u, u, u} n)
  have h3 : Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.{u, u, u}
      (∐ fun _ : Fin n => SheafOfModules.unit Y.ringCatSheaf : Y.Modules) n :=
    { exists_isFiniteLocallyFreeOfRankData := h2.exists_isFiniteLocallyFreeOfRankData }
  exact ⟨⊤, trivial, invertibleRank_pullback _ _ n h3⟩

/-- A module free of rank `n` near a point of a fibre is free of rank `n` near the generic point
of that fibre: the free-rank locus is open, and a nonempty open of an irreducible space contains
its generic point. -/
theorem freeAtPointOfRank_genericPoint_fiber {Y T : Scheme.{u}} (g : Y ⟶ T)
    [∀ t : T, IrreducibleSpace (g.fiber t)] {M : Y.Modules} {n : ℕ} {y : Y}
    (hy : FreeAtPointOfRank M y n) :
    FreeAtPointOfRank M (g.fiberι (g y) (genericPoint (g.fiber (g y)))) n := by
  obtain ⟨z, hz⟩ : y ∈ Set.range (g.fiberι (g y)) := by
    rw [Scheme.Hom.range_fiberι]
    rfl
  have hopen : IsOpen ((g.fiberι (g y)) ⁻¹' {x | FreeAtPointOfRank M x n}) :=
    (isOpen_setOf_freeAtPointOfRank M n).preimage (g.fiberι (g y)).continuous
  exact ((genericPoint_spec (g.fiber (g y))).mem_open_set_iff hopen).mpr
    ⟨z, trivial, by simpa [hz] using hy⟩

/-- A surjection from `𝒪^{⊕ n}` onto a module free of rank `q` at `y` has `q ≤ n`, and its
stalk map at `y` is injective when `q = n`. -/
private theorem le_and_injective_stalkLinearMap_of_epi {Y : Scheme.{u}} {n q : ℕ} {M : Y.Modules}
    (α : (∐ fun _ : Fin n => SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ M) [Epi α]
    {y : Y} (hy : FreeAtPointOfRank M y q) :
    q ≤ n ∧ (q = n →
      letI := Stacks.ModuleStalkSpecialization.stalkModule M y
      letI := Stacks.ModuleStalkSpecialization.stalkModule
        (∐ fun _ : Fin n => SheafOfModules.unit Y.ringCatSheaf : Y.Modules) y
      Function.Injective (stalkLinearMap _ _ α y)) := by
  let := Stacks.ModuleStalkSpecialization.stalkModule M y
  let := Stacks.ModuleStalkSpecialization.stalkModule
    (∐ fun _ : Fin n => SheafOfModules.unit Y.ringCatSheaf : Y.Modules) y
  obtain ⟨bM⟩ := nonempty_basis_stalk_of_freeAtPointOfRank M y q hy
  obtain ⟨bP⟩ := nonempty_basis_stalk_of_freeAtPointOfRank _ y n
    (freeAtPointOfRank_coproductUnit n y)
  have : Module.Finite (Y.presheaf.stalk y) (M.presheaf.stalk y) := Module.Finite.of_basis bM
  have : Module.Finite (Y.presheaf.stalk y)
      ((∐ fun _ : Fin n => SheafOfModules.unit Y.ringCatSheaf : Y.Modules).presheaf.stalk y) :=
    Module.Finite.of_basis bP
  have : Module.Free (Y.presheaf.stalk y) (M.presheaf.stalk y) := Module.Free.of_basis bM
  have : Module.Free (Y.presheaf.stalk y)
      ((∐ fun _ : Fin n => SheafOfModules.unit Y.ringCatSheaf : Y.Modules).presheaf.stalk y) :=
    Module.Free.of_basis bP
  have hsurj := Stacks.Chow.surjective_stalkLinearMap_of_epi α inferInstance y
  refine ⟨?_, fun hqn ↦ ?_⟩
  · have := LinearMap.finrank_range_le (stalkLinearMap _ _ α y)
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_eq_card_basis bM,
      Module.finrank_eq_card_basis bP] at this
    simpa using this
  · subst hqn
    exact (OrzechProperty.bijective_of_surjective_of_finrank_le (stalkLinearMap _ _ α y) hsurj
      (by rw [Module.finrank_eq_card_basis bM, Module.finrank_eq_card_basis bP])).1

/-- **A surjection from a finite free module which is free of the same rank near some point of
every fibre is an isomorphism.** -/
theorem isIso_of_forall_exists_freeAtPointOfRank {Y T : Scheme.{u}} (g : Y ⟶ T) [Flat g]
    [LocallyOfFiniteType g] [GeometricallyIntegral g] {n : ℕ} {M : Y.Modules}
    (α : (∐ fun _ : Fin n => SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ M) [Epi α]
    (h : ∀ t : T, ∃ y : Y, g y = t ∧ FreeAtPointOfRank M y n) :
    IsIso α := by
  have : Mono α := by
    refine mono_of_injective_stalk_genericPoint_fiber g α fun t ↦ ?_
    obtain ⟨y, rfl, hy⟩ := h t
    exact (le_and_injective_stalkLinearMap_of_epi α (freeAtPointOfRank_genericPoint_fiber g hy)).2
      rfl
  exact isIso_of_mono_of_epi α

/-- **A module receiving a surjection from `𝒪^{⊕ n}` is free of rank at most `n` near a
point.** -/
theorem le_of_freeAtPointOfRank_of_epi {Y : Scheme.{u}} {n q : ℕ} {M : Y.Modules}
    (α : (∐ fun _ : Fin n => SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ M) [Epi α]
    {y : Y} (hy : FreeAtPointOfRank M y q) : q ≤ n :=
  (le_and_injective_stalkLinearMap_of_epi α hy).1

/-- A module isomorphic to `𝒪^{⊕ n}` is free of rank `n` near every point. -/
theorem freeAtPointOfRank_of_isIso {Y : Scheme.{u}} {n : ℕ} {M : Y.Modules}
    (α : (∐ fun _ : Fin n => SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ M) [IsIso α]
    (y : Y) : FreeAtPointOfRank M y n :=
  freeAtPointOfRank_of_moduleIso (asIso α) (freeAtPointOfRank_coproductUnit n y)

end AlgebraicGeometry

namespace AlgebraicGeometry

/-- An open subscheme of a geometrically integral scheme over a base, which still surjects onto
that base, is itself geometrically integral over it. -/
alias geometricallyIntegral_comp_of_isOpenImmersion' :=
  geometricallyIntegral_comp_of_isOpenImmersion

/-- The pullback of a finite free module is the finite free module of the same rank. -/
noncomputable def pullbackCoproductUnitIso {Y X : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) :
    (Scheme.Modules.pullback f).obj
        (∐ fun _ : Fin n => SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅
      (∐ fun _ : Fin n => SheafOfModules.unit Y.ringCatSheaf : Y.Modules) :=
  PreservesCoproduct.iso (Scheme.Modules.pullback f) _ ≪≫
    Sigma.mapIso fun _ ↦ AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f

namespace FreeAtGenericPointsSituation

variable (D : FreeAtGenericPointsSituation.{u})

/-- The family of the situation has geometrically integral fibres: smooth fibres are
geometrically reduced. -/
theorem geometricallyIntegral_f : GeometricallyIntegral D.f :=
  have := D.geometricallyIrreducible_f
  have := geometricallyReduced_of_smooth D.f
  GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible D.f

/-- A *chart* of the situation: an affine open `V` of the base, an affine open `U` of the total
space lying over `V` and surjecting onto it, and a surjection from a finite free module onto the
restriction of the module to `U`. -/
structure Chart where
  /-- The affine open of the base. -/
  V : D.S.Opens
  isAffineOpen_V : IsAffineOpen V
  /-- The affine open of the total space. -/
  U : D.X.Opens
  isAffineOpen_U : IsAffineOpen U
  le : U ≤ D.f ⁻¹ᵁ V
  surj : ∀ v ∈ V, ∃ x ∈ U, D.f.base x = v
  /-- The number of generators. -/
  n : ℕ
  /-- The surjection from the finite free module. -/
  u : (∐ fun _ : Fin n => SheafOfModules.unit U.toScheme.ringCatSheaf : U.toScheme.Modules) ⟶
    (Scheme.Modules.pullback U.ι).obj D.F
  [epi : Epi u]

namespace Chart

variable {D} (c : D.Chart)

attribute [instance] Chart.epi

/-- The restriction of the family to the chart. -/
noncomputable abbrev g : c.U.toScheme ⟶ c.V.toScheme := D.f.resLE c.V c.U c.le

/-- The restriction of the family to the chart is surjective. -/
theorem surjective_g : Surjective c.g := by
  refine ⟨fun v ↦ ?_⟩
  obtain ⟨x, hx, hxv⟩ := c.surj v.1 v.2
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  simp [hxv]

/-- The restriction of the family to the chart is smooth. -/
instance smooth_g : Smooth c.g := by
  unfold g Scheme.Hom.resLE
  infer_instance

/-- The restriction of the family to the chart has geometrically integral fibres. -/
instance geometricallyIntegral_g : GeometricallyIntegral c.g := by
  have := D.geometricallyIntegral_f
  have hs : Surjective (D.X.homOfLE c.le ≫ D.f ∣_ c.V) := by
    have := c.surjective_g
    unfold g Scheme.Hom.resLE at this
    exact this
  have h := geometricallyIntegral_comp_of_isOpenImmersion' (D.X.homOfLE c.le) (D.f ∣_ c.V) hs
  unfold g Scheme.Hom.resLE
  exact h

variable {T : Scheme.{u}} (a : T ⟶ c.V.toScheme)

/-- The base change of the chart, as an open of the base change of the family. -/
noncomputable def j : pullback c.g a ⟶ pullback D.f (a ≫ c.V.ι) :=
  pullback.map c.g a D.f (a ≫ c.V.ι) c.U.ι (𝟙 T) c.V.ι (by simp) (by simp)

/-- The base change of the chart is an open immersion into the base change of the family. -/
instance : IsOpenImmersion (c.j a) := by
  unfold j
  infer_instance

/-- The map `j` intertwines the first projections with the inclusion of `U`. -/
@[reassoc (attr := simp)]
theorem j_fst : c.j a ≫ pullback.fst D.f (a ≫ c.V.ι) = pullback.fst c.g a ≫ c.U.ι := by
  simp only [j, pullback.map, pullback.lift_fst]

/-- The map `j` commutes with the second projections. -/
@[reassoc (attr := simp)]
theorem j_snd : c.j a ≫ pullback.snd D.f (a ≫ c.V.ι) = pullback.snd c.g a := by
  simp only [j, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The module on the base change of the chart is the pullback of the base-changed module. -/
noncomputable def moduleIso :
    (Scheme.Modules.pullback (pullback.fst c.g a)).obj ((Scheme.Modules.pullback c.U.ι).obj D.F) ≅
      (Scheme.Modules.pullback (c.j a)).obj (D.baseChangeModule (Over.mk (a ≫ c.V.ι))) :=
  (Scheme.Modules.pullbackComp (pullback.fst c.g a) c.U.ι).app D.F ≪≫
    (Scheme.Modules.pullbackCongr (c.j_fst a).symm).app D.F ≪≫
    ((Scheme.Modules.pullbackComp (c.j a) (pullback.fst D.f (a ≫ c.V.ι))).app D.F).symm

/-- **The generic-point condition read on the chart.** A scheme over the chart's base satisfies
the generic-point condition of rank `q` exactly when the module pulled back to the base change of
the chart is free of rank `q` near some point of every fibre. -/
theorem condition_iff (q : ℕ) :
    D.Condition q (Over.mk (a ≫ c.V.ι)) ↔ ∀ t : T, ∃ y : ↥(Limits.pullback c.g a),
      pullback.snd c.g a y = t ∧ FreeAtPointOfRank ((Scheme.Modules.pullback
        (pullback.fst c.g a)).obj ((Scheme.Modules.pullback c.U.ι).obj D.F)) y q := by
  constructor
  · intro h t
    have : Surjective (pullback.snd c.g a) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback c.g a) c.surjective_g
    obtain ⟨y₀, hy₀⟩ := (pullback.snd c.g a).surjective t
    let T' : Over D.S := Over.mk (a ≫ c.V.ι)
    have := D.irreducibleSpace_fiber_baseChangeMap T' t
    have hξ := h t (genericPoint ((D.baseChangeMap T').fiber t)) (genericPoint_spec _)
    have hopen : IsOpen ((D.baseChangeMap T').fiberι t ⁻¹' Set.range (c.j a).base) :=
      (c.j a).isOpenEmbedding.isOpen_range.preimage ((D.baseChangeMap T').fiberι t).continuous
    have hy₀mem : (c.j a).base y₀ ∈ Set.range ((D.baseChangeMap T').fiberι t).base := by
      rw [Scheme.Hom.range_fiberι]
      show (c.j a ≫ pullback.snd D.f (a ≫ c.V.ι)).base y₀ = t
      rw [c.j_snd]
      exact hy₀
    obtain ⟨z₀, hz₀⟩ := hy₀mem
    have hgen : genericPoint ((D.baseChangeMap T').fiber t) ∈
        (D.baseChangeMap T').fiberι t ⁻¹' Set.range (c.j a).base :=
      ((genericPoint_spec _).mem_open_set_iff hopen).mpr ⟨z₀, trivial, y₀, hz₀.symm⟩
    obtain ⟨y, hy⟩ := hgen
    refine ⟨y, ?_, ?_⟩
    · have h1 : (c.j a ≫ pullback.snd D.f (a ≫ c.V.ι)).base y = t := by
        rw [Scheme.Hom.comp_base, TopCat.comp_app, hy]
        have hmem : ((D.baseChangeMap T').fiberι t) (genericPoint _) ∈
            Set.range ((D.baseChangeMap T').fiberι t).base := ⟨_, rfl⟩
        rw [Scheme.Hom.range_fiberι] at hmem
        exact hmem
      rwa [c.j_snd] at h1
    · refine freeAtPointOfRank_of_moduleIso (c.moduleIso a).symm ?_
      refine freeAtPointOfRank_pullback (c.j a) _ y q ?_
      rw [hy]
      exact hξ
  · intro h
    rw [D.condition_iff_baseRankLocus_eq_univ, Set.eq_univ_iff_forall]
    intro t
    obtain ⟨y, hy, hfree⟩ := h t
    refine ⟨(c.j a).base y, ?_, ?_⟩
    · exact freeAtPointOfRank_of_isOpenImmersion (c.j a) _ y q
        (freeAtPointOfRank_of_moduleIso (c.moduleIso a) hfree)
    · show (c.j a ≫ pullback.snd D.f (a ≫ c.V.ι)).base y = t
      rw [c.j_snd]
      exact hy

end Chart

end FreeAtGenericPointsSituation

end AlgebraicGeometry

end
