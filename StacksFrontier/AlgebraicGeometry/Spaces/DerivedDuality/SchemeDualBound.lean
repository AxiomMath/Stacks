module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.LocalCharts
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeCoherentDuality
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionUpperShriekDualizing
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedBoundedBelow

/-!
# A uniform bound for the dual on an affine Noetherian scheme

Let `T` be an affine Noetherian scheme and `ω` a dualizing complex on `T`. There is an integer
`b`, an upper bound of an injective amplitude of a module model of `ω`, such that for every object
`Y` of `D(𝒪_T)` with coherent cohomology sheaves vanishing below `m`, the dual `R𝓗om(Y, ω)` has
cohomology sheaves vanishing above `b - m`.

## Main results

* `AlgebraicGeometry.RingedSite.exists_bound_schemeDual`.
* `AlgebraicGeometry.RingedSite.ChartClass.bounded_isStable`: objects with bounded cohomology
  are stable under the dual and under cones.

## References

* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.RingedSite

/-- **A uniform upper bound for the dual on an affine Noetherian scheme.** -/
theorem exists_bound_schemeDual (T : Scheme.{u}) [IsAffine T] [IsNoetherian T]
    (ω : SchemeStdDerived T)
    (hω : letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω) :
    ∃ b : ℤ, ∀ (m : ℤ) (Y : SchemeStdDerived T), SchemeCoherent T Y →
      (∀ i : ℤ, i < m → IsZero ((schemeStdHomology T i).obj Y)) →
        ∀ j : ℤ, b - m < j → IsZero ((schemeStdHomology T j).obj (schemeDual T ω Y)) := by
  let : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
  have hV : IsAffineOpen (⊤ : T.Opens) := isAffineOpen_top T
  have hR : IsNoetherianRing Γ(T, ⊤) := IsLocallyNoetherian.component_noetherian ⟨⊤, hV⟩
  let : HasDerivedCategory (ModuleCat.{u} Γ(T, ⊤)) := HasDerivedCategory.standard _
  let : HasDerivedCategory (⊤ : T.Opens).toScheme.Modules := HasDerivedCategory.standard _
  let : HasDerivedCategory (Spec Γ(T, ⊤)).Modules := HasDerivedCategory.standard _
  have hω' := Stacks.Duality.exists_isDualizingComplex_iso_restrictFunctor ⊤ hV hω
  obtain ⟨a, b, hamp⟩ := hω'.choose_spec.1.finiteInjectiveDimension
  refine ⟨b, fun m Y hY hYge j hj => ?_⟩
  have hM := Stacks.Duality.exists_finite_iso_restrictFunctor_of_isCoherent ⊤ hV Y hY
  have hMge : hM.choose.IsGE m := (DerivedCategory.isGE_iff _ m).2 fun i hi =>
    (AlgebraicGeometry.StandardModel.isZero_homology_mapDerivedCategory_obj_iff Γ(T, ⊤) _ i).1
      ((Stacks.Duality.isZero_restrict_homology_iff ⊤ hV hM.choose_spec.2.some i).1
        (Functor.map_isZero _ (hYge i hi)))
  have hle := Stacks.Duality.isLE_derivedSheafHom_derivedTilde_of_injectiveAmplitude Γ(T, ⊤) _ _
    m a b hMge hamp
  have hres := (Stacks.Duality.isZero_restrict_homology_iff ⊤ hV
    (Stacks.Duality.restrictDerivedSheafHomIsoOfModels ⊤ hV hM.choose_spec.2.some
      hω'.choose_spec.2.some) j).2
      (DerivedCategory.isZero_of_isLE _ (b - m) j hj (hX := hle))
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun y => ?_
  exact Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isZero_stalk_of_isZero_restrict _ _ y
    (Set.mem_univ y) hres

/-- In a distinguished triangle, the third vertex has no cohomology in degree `n` when the second
has none in degree `n` and the first none in degree `n + 1`. -/
theorem isZero_schemeStdHomology_obj₃ {T : Scheme.{u}} (Tr : Triangle (SchemeStdDerived T))
    (hTr : letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
      Tr ∈ distTriang (SchemeStdDerived T)) (n : ℤ)
    (h₂ : IsZero ((schemeStdHomology T n).obj Tr.obj₂))
    (h₁ : IsZero ((schemeStdHomology T (n + 1)).obj Tr.obj₁)) :
    IsZero ((schemeStdHomology T n).obj Tr.obj₃) := by
  let : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
  exact (DerivedCategory.HomologySequence.exact₃ Tr hTr n (n + 1) rfl).isZero_of_both_isZero h₂ h₁

/-- **Objects with bounded cohomology are stable** under the dual of objects with coherent
cohomology on an affine Noetherian scheme (Stacks 0A89: the dualizing complex has finite
injective dimension and is bounded below) and under cones. -/
theorem ChartClass.bounded_isStable : ChartClass.IsStable ChartClass.bounded.{u} where
  dual := by
    intro T _ _ ω hω X hX hP
    let : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
    obtain ⟨a, b, hab⟩ := hP
    obtain ⟨bT, hbT⟩ := exists_bound_schemeDual T ω hω
    obtain ⟨n₀, hn₀⟩ := Stacks.Duality.isBoundedBelow_of_isDualizingComplex ω hω
    have hge : ω.IsGE n₀ := (DerivedCategory.isGE_iff ω n₀).2 fun i hi => hn₀ i hi
    have hle : X.IsLE b := (DerivedCategory.isLE_iff X b).2 fun i hi => hab i (Or.inr hi)
    let : HasDerivedCategory (Stacks.SheafOfModules.StructureSheafModules T.sheaf) :=
      HasDerivedCategory.standard _
    have hD := Stacks.SheafOfModules.isGE_derivedSheafHom T.sheaf X ω b n₀ hle hge
    refine ⟨n₀ - b, bT - a, fun i hi => ?_⟩
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff _ (n₀ - b)).1 hD i hi
    · exact hbT a X hX (fun i hi => hab i (Or.inl hi)) i hi
  obj₃ := by
    intro T _ _ Tr hTr _ _ h₁ h₂
    obtain ⟨a₁, b₁, h₁⟩ := h₁
    obtain ⟨a₂, b₂, h₂⟩ := h₂
    refine ⟨min a₂ (a₁ - 1), max b₂ (b₁ - 1), fun i hi => ?_⟩
    refine isZero_schemeStdHomology_obj₃ Tr hTr i (h₂ i ?_) (h₁ (i + 1) ?_)
    · rcases hi with hi | hi
      · exact Or.inl (lt_of_lt_of_le hi (min_le_left _ _))
      · exact Or.inr (lt_of_le_of_lt (le_max_left _ _) hi)
    · rcases hi with hi | hi
      · exact Or.inl (by have := min_le_right a₂ (a₁ - 1); omega)
      · exact Or.inr (by have := le_max_right b₂ (b₁ - 1); omega)

/-- **A dualizing complex on an affine Noetherian scheme is bounded above**: it has a module
model of finite injective dimension. -/
theorem exists_isZero_homology_of_isDualizingComplex (T : Scheme.{u}) [IsAffine T]
    [IsNoetherian T] (ω : SchemeStdDerived T)
    (hω : letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω) :
    ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero ((schemeStdHomology T j).obj ω) := by
  let : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
  have hV : IsAffineOpen (⊤ : T.Opens) := isAffineOpen_top T
  have hR : IsNoetherianRing Γ(T, ⊤) := IsLocallyNoetherian.component_noetherian ⟨⊤, hV⟩
  let : HasDerivedCategory (ModuleCat.{u} Γ(T, ⊤)) := HasDerivedCategory.standard _
  let : HasDerivedCategory (⊤ : T.Opens).toScheme.Modules := HasDerivedCategory.standard _
  let : HasDerivedCategory (Spec Γ(T, ⊤)).Modules := HasDerivedCategory.standard _
  have hω' := Stacks.Duality.exists_isDualizingComplex_iso_restrictFunctor ⊤ hV hω
  obtain ⟨a, b, I, _, hIle, -, ⟨eI⟩⟩ := hω'.choose_spec.1.finiteInjectiveDimension
  refine ⟨b, fun j hj => ?_⟩
  have h0 : IsZero ((DerivedCategory.homologyFunctor _ j).obj hω'.choose) :=
    (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj I) b j hj).of_iso
      ((DerivedCategory.homologyFunctor _ j).mapIso eI)
  have hres := (Stacks.Duality.isZero_restrict_homology_iff ⊤ hV hω'.choose_spec.2.some j).2
    ((AlgebraicGeometry.StandardModel.isZero_homology_mapDerivedCategory_obj_iff Γ(T, ⊤) _ j).2 h0)
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun y => ?_
  exact Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isZero_stalk_of_isZero_restrict _ _ y
    (Set.mem_univ y) hres

/-- A dualizing complex on an affine Noetherian scheme has bounded cohomology. -/
theorem bounded_of_isDualizingComplex (T : Scheme.{u}) [IsAffine T] [IsNoetherian T]
    (ω : SchemeStdDerived T)
    (hω : letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω) : ChartClass.bounded T ω := by
  let : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
  obtain ⟨b, hb⟩ := exists_isZero_homology_of_isDualizingComplex T ω hω
  obtain ⟨n₀, hn₀⟩ := Stacks.Duality.isBoundedBelow_of_isDualizingComplex ω hω
  exact ⟨n₀, b, fun i hi => hi.elim (hn₀ i) (hb i)⟩

end AlgebraicGeometry.RingedSite
