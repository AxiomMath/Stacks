module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Topology.KrullDimension
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.CategoryTheory.Triangulated.Elementary
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.SchemeModules
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SeparatedCohomologyHomVanishingPredicate
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ExtVanishingRegular

/-!
# Splitting a bounded coherent complex across a gap in its cohomology

Let `X` be a regular Noetherian scheme of finite dimension `d`, let `K` be a bounded complex of
`𝒪_X`-modules with coherent cohomology, and let `a` be an integer. If the cohomology of `K`
vanishes in every degree strictly between `a` and `a + d`, then `K` is the direct sum of its
truncation at `a` and its truncation at `a + d`.

The canonical truncation triangle
`τ^{≤ a + d - 1} K ⟶ K ⟶ τ^{≥ a + d} K ⟶ (τ^{≤ a + d - 1} K)[1]`
exists for every `K`, so the whole content of the statement is that its connecting morphism `δ`
vanishes; once it does, the triangle splits by [Stacks, Tag 05QT]. The vanishing of `δ` is a
`Hom`-vanishing statement: the source of `δ` has cohomology only in degrees `≥ a + d` and its
target has cohomology only in degrees `< a`, and on a regular Noetherian scheme of dimension `d`
no nonzero morphism connects two such complexes. That `Hom`-vanishing is
[Stacks, Tag 0FZ3] part (2), which this development proves:
`AlgebraicGeometry.forall_separatedCohomologyHomVanishing` supplies it in the packaged form
`AlgebraicGeometry.SeparatedCohomologyHomVanishing`.

## Main results

* `AlgebraicGeometry.exists_iso_biprod_truncLE_truncGE` splits `K` as
  `τ^{≤ a + d - 1} K ⊕ τ^{≥ a + d} K`, for every `d`, taking the `Hom`-vanishing as a hypothesis.
* `AlgebraicGeometry.exists_iso_biprod_truncations` is the form the source states, with the
  lower summand named `τ^{≤ a} K`, and with the `Hom`-vanishing discharged.

## Implementation notes

The source writes the conclusion with lower summand `τ^{≤ a} K`, which agrees with
`τ^{≤ a + d - 1} K` exactly because the gap hypothesis kills the cohomology in the degrees
between them; that identification, and hence the source's statement, needs `0 < d`. At `d = 0`
the two truncations differ by one degree and the stated splitting is false: on a nonempty
regular Noetherian scheme of dimension `0` the structure sheaf placed in degree `a` would have
to be isomorphic to its own direct square. Positivity of `d` is therefore recorded as an
explicit hypothesis of `exists_iso_biprod_truncations`, while
`exists_iso_biprod_truncLE_truncGE`, which names the lower summand `τ^{≤ a + d - 1} K`, holds for
every `d` and is where the argument actually takes place.

Membership of `K` in `D^b_{Coh}(𝒪_X)` is spelled out as the conjunction of `t`-boundedness for
the canonical t-structure and coherence of every cohomology sheaf, rather than through a
subcategory, so that the truncations — which are formed in `D(𝒪_X)` — can be fed back to the
carried `Hom`-vanishing without transporting along an equivalence. The equality of objects in
the source is read as the existence of an isomorphism: the splitting of a triangle is not
canonical, so `Nonempty` is the honest conclusion.

## References

* [Stacks Project, Tag 0FZ4](https://stacks.math.columbia.edu/tag/0FZ4)
* [Stacks Project, Tag 0FZ3](https://stacks.math.columbia.edu/tag/0FZ3)
* [Stacks Project, Tag 08J5](https://stacks.math.columbia.edu/tag/08J5)
* [Stacks Project, Tag 05QT](https://stacks.math.columbia.edu/tag/05QT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### Coherence of the cohomology of a truncation -/

/-- A zero sheaf of modules is coherent. -/
private theorem isCoherent_of_isZero {X : Scheme.{u}} {M : X.Modules} (hM : IsZero M) :
    M.IsCoherent :=
  have := CoherentAbelian.coherentModules_containsZero (R := X.ringCatSheaf)
  have := CoherentAbelian.coherentModules_isClosedUnderIsomorphisms (R := X.ringCatSheaf)
  ObjectProperty.prop_of_isZero (P := fun M : SheafOfModules X.ringCatSheaf => M.IsCoherent) hM

/-- In degrees `≤ c`, the map from `τ^{≤ c} K` to `K` is an isomorphism on cohomology. -/
private theorem isIso_homologyMap_truncLEι_app {X : Scheme.{u}} (K : DerivedCategory X.Modules)
    (c i : ℤ) (hic : i ≤ c) :
    IsIso ((DerivedCategory.homologyFunctor X.Modules i).map
      ((DerivedCategory.TStructure.t.truncLEι c).app K)) :=
  DerivedCategory.isIso_homologyMap_truncLTι_app (c + 1) i (by omega) K

/-- Truncating from above preserves coherence of the cohomology: below the truncation degree the
cohomology is that of the object, and above it the cohomology vanishes. -/
private theorem isCoherent_homology_truncLE_obj {X : Scheme.{u}} (K : DerivedCategory X.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsCoherent) (c i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.TStructure.t.truncLE c).obj K)).IsCoherent := by
  by_cases hic : i ≤ c
  · have := isIso_homologyMap_truncLEι_app K c i hic
    exact AlgebraicGeometry.isCoherent_of_moduleIso
      (asIso ((DerivedCategory.homologyFunctor X.Modules i).map
        ((DerivedCategory.TStructure.t.truncLEι c).app K))).symm (hK i)
  · exact isCoherent_of_isZero (DerivedCategory.isZero_of_isLE _ c i (by omega))

/-- Truncating from below preserves coherence of the cohomology: at and above the truncation
degree the cohomology is that of the object, and below it the cohomology vanishes. -/
private theorem isCoherent_homology_truncGE_obj {X : Scheme.{u}} (K : DerivedCategory X.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsCoherent) (c i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.TStructure.t.truncGE c).obj K)).IsCoherent := by
  by_cases hic : c ≤ i
  · have := DerivedCategory.isIso_homologyMap_truncGEπ_app c i hic K
    exact AlgebraicGeometry.isCoherent_of_moduleIso
      (asIso ((DerivedCategory.homologyFunctor X.Modules i).map
        ((DerivedCategory.TStructure.t.truncGEπ c).app K))) (hK i)
  · exact isCoherent_of_isZero (DerivedCategory.isZero_of_isGE _ c i (by omega))

/-- The cohomology of the shift by one of an object with coherent cohomology is coherent. -/
private theorem isCoherent_homology_shift {X : Scheme.{u}} (L : DerivedCategory X.Modules)
    (hL : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj (L⟦(1 : ℤ)⟧)).IsCoherent := by
  have e := ((DerivedCategory.homologyFunctor X.Modules 0).shiftIso (1 : ℤ) i (i + 1)
    (by omega)).app L
  have : (((DerivedCategory.homologyFunctor X.Modules 0).shift (i + 1)).obj L).IsCoherent := by
    simpa [DerivedCategory.shift_homologyFunctor] using hL (i + 1)
  simpa [DerivedCategory.shift_homologyFunctor] using
    AlgebraicGeometry.isCoherent_of_moduleIso e.symm this

/-! ### The gap pushes the lower truncation down -/

/-- Under the gap hypothesis the truncation of `K` at `a + d - 1` is already concentrated in
degrees `≤ a`: the degrees it retains above `a` are exactly those the gap hypothesis kills. -/
private theorem isLE_truncLE_obj_of_cohomology_gap {X : Scheme.{u}}
    (K : DerivedCategory X.Modules) (a : ℤ) (d : ℕ)
    (hgap : ∀ i : ℤ, a < i → i < a + (d : ℤ) →
      IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K)) :
    ((DerivedCategory.TStructure.t.truncLE (a + (d : ℤ) - 1)).obj K).IsLE a :=
  (DerivedCategory.isLE_iff _ a).2 fun i hi => by
    by_cases hic : i ≤ a + (d : ℤ) - 1
    · have := isIso_homologyMap_truncLEι_app K (a + (d : ℤ) - 1) i hic
      exact (hgap i hi (by omega)).of_iso
        (asIso ((DerivedCategory.homologyFunctor X.Modules i).map
          ((DerivedCategory.TStructure.t.truncLEι (a + (d : ℤ) - 1)).app K)))
    · exact DerivedCategory.isZero_of_isLE _ (a + (d : ℤ) - 1) i (by omega)

/-! ### The splitting -/

/-- **The splitting of a bounded coherent complex across a gap in its cohomology.** Let `X` be a
regular Noetherian scheme of dimension `d`, let `K` be a bounded complex of `𝒪_X`-modules with
coherent cohomology and let `a` be an integer such that `H^i(K) = 0` for `a < i < a + d`. Then
`K` is the direct sum of `τ^{≤ a + d - 1} K` and `τ^{≥ a + d} K`.

The truncation triangle of [Stacks, Tag 08J5] at the cut `a + d - 1 < a + d` has connecting
morphism `τ^{≥ a + d} K ⟶ (τ^{≤ a + d - 1} K)[1]`. The gap hypothesis makes the target of that
morphism concentrated in degrees `< a`, while its source is concentrated in degrees `≥ a + d`,
so the carried `Hom`-vanishing forces it to be zero and [Stacks, Tag 05QT] splits the
triangle. -/
public theorem exists_iso_biprod_truncLE_truncGE (X : Scheme.{u}) [IsNoetherian X]
    (hX : IsRegular X) (d : ℕ) (hd : topologicalKrullDim X = (d : WithBot ℕ∞))
    (hvan : SeparatedCohomologyHomVanishing X d)
    (K : DerivedCategory X.Modules)
    (hKbdd : DerivedCategory.TStructure.t.bounded K)
    (hKcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsCoherent)
    (a : ℤ)
    (hgap : ∀ i : ℤ, a < i → i < a + (d : ℤ) →
      IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K)) :
    Nonempty (K ≅ (DerivedCategory.TStructure.t.truncLE (a + (d : ℤ) - 1)).obj K ⊞
      (DerivedCategory.TStructure.t.truncGE (a + (d : ℤ))).obj K) := by
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := hKbdd
  have : DerivedCategory.TStructure.t.IsGE K m := hm
  have : DerivedCategory.TStructure.t.IsLE K n := hn
  have hA'LE := isLE_truncLE_obj_of_cohomology_gap K a d hgap
  have : (((DerivedCategory.TStructure.t.truncLE (a + (d : ℤ) - 1)).obj K)⟦(1 : ℤ)⟧).IsLE
      (a - 1) :=
    DerivedCategory.TStructure.t.isLE_shift _ a 1 (a - 1) (by omega)
  have hc : a + (d : ℤ) - 1 + 1 = a + (d : ℤ) := by omega
  have hBbdd : DerivedCategory.TStructure.t.bounded
      ((DerivedCategory.TStructure.t.truncGE (a + (d : ℤ))).obj K) :=
    ⟨⟨a + (d : ℤ), inferInstance⟩, ⟨n, inferInstance⟩⟩
  have hA'bdd : DerivedCategory.TStructure.t.bounded
      ((DerivedCategory.TStructure.t.truncLE (a + (d : ℤ) - 1)).obj K) :=
    ⟨⟨m, inferInstance⟩, ⟨a + (d : ℤ) - 1, inferInstance⟩⟩
  have hsub := hvan hX hd _ _ hBbdd
    (DerivedCategory.TStructure.t.bounded.le_shift (1 : ℤ) _ hA'bdd)
    (isCoherent_homology_truncGE_obj K hKcoh (a + (d : ℤ)))
    (isCoherent_homology_shift _ (isCoherent_homology_truncLE_obj K hKcoh (a + (d : ℤ) - 1))) a
    (fun i hi => DerivedCategory.isZero_of_isGE _ (a + (d : ℤ)) i (by omega))
    (fun i hi => DerivedCategory.isZero_of_isLE _ (a - 1) i (by omega))
  have hT := DerivedCategory.TStructure.t.triangleLEGE_distinguished (a + (d : ℤ) - 1)
    (a + (d : ℤ)) hc K
  set T := (DerivedCategory.TStructure.t.triangleLEGE (a + (d : ℤ) - 1) (a + (d : ℤ)) hc).obj K
  have hδ : T.mor₃ = 0 :=
    (show Subsingleton (T.obj₃ ⟶ T.obj₁⟦(1 : ℤ)⟧) from hsub).elim _ _
  obtain ⟨s, hs⟩ := T.coyoneda_exact₃ hT (𝟙 T.obj₃) (by rw [Category.id_comp, hδ])
  have := isIso_biprod_desc_of_distTriang T hT s hs.symm
  exact ⟨(asIso (biprod.desc T.mor₁ s)).symm⟩

/-- **[Stacks, Tag 0FZ4].** Let `X` be a regular Noetherian scheme of finite dimension `d`, with
`0 < d`. Let `K` be a bounded complex of `𝒪_X`-modules with coherent cohomology and let `a` be
an integer such that `H^i(K) = 0` for `a < i < a + d`. Then `K = τ^{≤ a} K ⊕ τ^{≥ a + d} K`.

This is `exists_iso_biprod_truncLE_truncGE` together with the identification
`τ^{≤ a + d - 1} K = τ^{≤ a} K`, which holds because the gap hypothesis makes
`τ^{≤ a + d - 1} K` concentrated in degrees `≤ a`. The `Hom`-vanishing of
[Stacks, Tag 0FZ3] part (2) that the splitting consumes is supplied by
`AlgebraicGeometry.forall_separatedCohomologyHomVanishing`, so no hypothesis beyond the
source's — and `0 < d`, without which the source's statement is false — is assumed. -/
@[stacks 0FZ4 "a bounded coherent complex splits across a cohomology gap of length the dimension"]
public theorem exists_iso_biprod_truncations (X : Scheme.{u}) [IsNoetherian X]
    (hX : IsRegular X) (d : ℕ) (hd : topologicalKrullDim X = (d : WithBot ℕ∞)) (hd0 : 0 < d)
    (K : DerivedCategory X.Modules)
    (hKbdd : DerivedCategory.TStructure.t.bounded K)
    (hKcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsCoherent)
    (a : ℤ)
    (hgap : ∀ i : ℤ, a < i → i < a + (d : ℤ) →
      IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K)) :
    Nonempty (K ≅ (DerivedCategory.TStructure.t.truncLE a).obj K ⊞
      (DerivedCategory.TStructure.t.truncGE (a + (d : ℤ))).obj K) := by
  obtain ⟨e⟩ := exists_iso_biprod_truncLE_truncGE X hX d hd
    (forall_separatedCohomologyHomVanishing X d) K hKbdd hKcoh a hgap
  have := isLE_truncLE_obj_of_cohomology_gap K a d hgap
  have : IsIso ((DerivedCategory.TStructure.t.truncLE a).map
      ((DerivedCategory.TStructure.t.truncLEι (a + (d : ℤ) - 1)).app K)) :=
    DerivedCategory.TStructure.t.isIso_truncLE_map_truncLEι_app a (a + (d : ℤ) - 1)
      (by omega) K
  exact ⟨e ≪≫ biprod.mapIso
    ((asIso ((DerivedCategory.TStructure.t.truncLEι a).app
        ((DerivedCategory.TStructure.t.truncLE (a + (d : ℤ) - 1)).obj K))).symm ≪≫
      asIso ((DerivedCategory.TStructure.t.truncLE a).map
        ((DerivedCategory.TStructure.t.truncLEι (a + (d : ℤ) - 1)).app K)))
    (Iso.refl _)⟩

end AlgebraicGeometry

end
