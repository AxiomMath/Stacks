module

public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.PerfectBoundedCoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.PerfectTensorTriangleStep
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedDualTensorIsoSheafHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedBoundedBelow
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHom
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSiteComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Tensoring and taking internal Hom against a perfect complex on a Noetherian scheme

Let `X` be a Noetherian scheme and let `E` be a perfect object of `D(𝒪_X)`. Parts (2)-(5) of
[Stacks, Tag 0FXU] say that for `L` in `D_Coh(𝒪_X)`, `D^b_Coh(𝒪_X)`, `D^+_Coh(𝒪_X)` and
`D^-_Coh(𝒪_X)` respectively, both

`E ⊗^𝐋_{𝒪_X} L`  and  `R𝓗om_{𝒪_X}(E, L)`

lie in the same one of those four categories. Part (1), that `E` itself lies in
`D^b_Coh(𝒪_X)`, is
`Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect`.

## Main results

* `Stacks.AlgebraicGeometry.PerfectCohomology.derivedCategoryB_coherent_of_isPerfect`:
  **[Stacks, Tag 0FXU], part (2).**
* `Stacks.AlgebraicGeometry.PerfectCohomology.derivedCategoryBBounded_coherent_of_isPerfect`:
  **[Stacks, Tag 0FXU], part (3).**
* `Stacks.AlgebraicGeometry.PerfectCohomology.derivedCategoryBPlus_coherent_of_isPerfect`:
  **[Stacks, Tag 0FXU], part (4).**
* `Stacks.AlgebraicGeometry.PerfectCohomology.derivedCategoryBMinus_coherent_of_isPerfect`:
  **[Stacks, Tag 0FXU], part (5).**

## The route

The two operations are exchanged by the derived dual `E^∨ = R𝓗om_{𝒪_X}(E, 𝒪_X)`. For a perfect
`E` the canonical map `E^∨ ⊗^𝐋 L ⟶ R𝓗om(E, L)` of [Stacks, Tag 08I1] is invertible, which is
[Stacks, Tag 08JJ] in the form `AlgebraicGeometry.RingedSite.derivedDualTensorIsoSheafHom`, and
`E^∨` is again perfect, which is [Stacks, Tag 08DQ]. Since the bidual map `E ⟶ (E^∨)^∨` is also
invertible for a perfect `E`, again [Stacks, Tag 08JJ], the two operations are

`R𝓗om(E, L) ≅ E^∨ ⊗^𝐋 L`  and  `E ⊗^𝐋 L ≅ R𝓗om(E^∨, L)`,

so every conclusion about the derived tensor product with an arbitrary perfect first factor
yields the matching conclusion about the derived internal Hom, and conversely.

Coherence of the cohomology sheaves of `E ⊗^𝐋 L` is [Stacks, Tag 0AZS] part (2),
`AlgebraicGeometry.TorFormula.derivedCategoryBMinus_derivedTensor`, once both factors are
bounded above; `E` is, by part (1). For an `L` with no bound above, a single degree `n` of
`E ⊗^𝐋 L` is computed by a truncation: with `E^∨` living in degrees `≤ d`, the object
`E ⊗^𝐋 τ_{≥ n+d+1}L ≅ R𝓗om(E^∨, τ_{≥ n+d+1}L)` lies in degrees `≥ n + 1` by the boundedness
clause of [Stacks, Tag 0D0C], so the cohomology of that vertex vanishes in degrees `n - 1` and
`n`, and the long exact sequence of the truncation triangle identifies
`H^n(E ⊗^𝐋 τ_{≤ n+d}L)` with `H^n(E ⊗^𝐋 L)`.

The bound above on `E ⊗^𝐋 L` is the right t-exactness of the derived tensor product,
[Stacks, Tag 06YU], and the bound below is the boundedness clause of [Stacks, Tag 0D0C] read
through `E ⊗^𝐋 L ≅ R𝓗om(E^∨, L)`.

## Implementation notes

The derived tensor product is the one of [Stacks, Tag 06YU] on a ringed space,
`Stacks.Cohomology.TorAmplitude.derTensor`, in the spelling
`AlgebraicGeometry.TorFormula.derivedTensor` that [Stacks, Tag 0AZS] is stated at; the derived
internal Hom is `Stacks.SheafOfModules.derivedSheafHom`, the bifunctor of [Stacks, Tag 08DH].

The category of `𝒪_X`-modules is spelled `StrictlyPerfect.OXMod X.toRingedSpace`, as in part
(1). The derived internal Hom and the derived dual are stated at
`Stacks.SheafOfModules.StructureSheafModules X.sheaf` and the derived tensor product at
`X.Modules`; the three are definitionally equal and the conversion crosses them in term
position, but instance search does not. So the two operations are given the names
`derivedTensorObj` and `derivedSheafHomObj` below, whose ascribed value type is the one
spelling, and every `DerivedCategoryB` predicate is read at that spelling: a predicate whose
object argument is spelled differently from its own carrier makes the elaborator search for the
`Abelian` instance instead of taking it from the object, and that search does not succeed
through these imports.

Perfectness is `AlgebraicGeometry.RingedSpace.IsPerfect`, the spelling part (1) is stated at;
`Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSite` carries it to the ringed-site
reading of [Stacks, Tag 08G5] that the two dual statements are stated at.

## References

* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
* [Stacks Project, Tag 0AZS](https://stacks.math.columbia.edu/tag/0AZS)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0D0C](https://stacks.math.columbia.edu/tag/0D0C)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open Stacks.SheafOfModules (derivedSheafHom derivedDual)
open AlgebraicGeometry.TorFormula (derivedTensor)

universe u

namespace Stacks.AlgebraicGeometry.PerfectCohomology

-- The priority selects the standard model of `D(𝒪_X)`, which the derived internal Hom, the
-- derived dual and `AlgebraicGeometry.TorFormula.derivedTensor` are all read at, over the
-- locally small one arriving with the imports.
attribute [local instance 100000] HasDerivedCategory.standard

variable (X : Scheme.{u})

/-! ### The derived dual of a perfect object -/

/-- **The derived dual of a perfect object of `D(𝒪_X)` is perfect**, read at the ringed-space
spelling of perfectness. This is [Stacks, Tag 08DQ] transported along
`Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSite`. -/
theorem isPerfect_derivedDual_of_isPerfect
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) :
    RingedSpace.IsPerfect (X := X.toRingedSpace) (derivedDual X.sheaf E) :=
  (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSite X.toRingedSpace
      (derivedDual X.sheaf E)).2
    (Stacks.SheafOfModules.isPerfect_derivedDual X.sheaf E
      ((Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSite X.toRingedSpace E).1 hE))

/-- **The bidual of a perfect object of `D(𝒪_X)`.** For a perfect `E` the canonical map
`E ⟶ (E^∨)^∨` of [Stacks, Tag 0A97] is invertible, which is one of the assertions of
[Stacks, Tag 08JJ]. -/
def derivedBidualIso (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) :
    E ≅ derivedDual X.sheaf (derivedDual X.sheaf E) :=
  let S := Stacks.SheafOfModules.ringedSite X.sheaf
  let T := Stacks.SheafOfModules.canonicalDerivedTensorProduct S
  @asIso _ _ _ _ (AlgebraicGeometry.RingedSite.derivedBidual S T E)
    (AlgebraicGeometry.RingedSite.isIso_derivedBidual_of_isPerfect S T E
      ((Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSite X.toRingedSpace E).1 hE))

/-- **`R𝓗om(E, L) ≅ E^∨ ⊗^𝐋 L` for a perfect `E`**: the canonical map of [Stacks, Tag 08I1] is
invertible, which is one of the assertions of [Stacks, Tag 08JJ]. -/
def derivedSheafHomIsoTensorDual
    (E L : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) :
    ((derivedSheafHom X.sheaf).obj (op E)).obj L ≅
      ((derivedTensor X).obj (derivedDual X.sheaf E)).obj L :=
  (AlgebraicGeometry.RingedSite.derivedDualTensorIsoSheafHom
    (Stacks.SheafOfModules.ringedSite X.sheaf) E L
    ((Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSite X.toRingedSpace E).1 hE)).symm

/-- **`E ⊗^𝐋 L ≅ R𝓗om(E^∨, L)` for a perfect `E`**: the previous identification at the perfect
object `E^∨`, composed with the bidual isomorphism of `E`. -/
def derivedTensorIsoSheafHomDual
    (E L : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) :
    ((derivedTensor X).obj E).obj L ≅
      ((derivedSheafHom X.sheaf).obj (op (derivedDual X.sheaf E))).obj L :=
  ((derivedTensor X).mapIso (derivedBidualIso X E hE)).app L ≪≫
    (derivedSheafHomIsoTensorDual X (derivedDual X.sheaf E) L
      (isPerfect_derivedDual_of_isPerfect X E hE)).symm

/-! ### The two operations, read at one spelling of `D(𝒪_X)` -/

/-- **`E ⊗^𝐋_{𝒪_X} L`**, the derived tensor product of [Stacks, Tag 06YU], with its value read
in the `StrictlyPerfect.OXMod` spelling of `D(𝒪_X)` that part (1) of [Stacks, Tag 0FXU] is
stated at. `AlgebraicGeometry.TorFormula.derivedTensor` lands in `DerivedCategory X.Modules`,
which is the same category definitionally; the ascription is what lets the `DerivedCategoryB`
predicates below take their instances from the spelling their hypotheses are stated at. -/
abbrev derivedTensorObj
    (E L : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)) :
    DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) :=
  ((derivedTensor X).obj E).obj L

/-- **`R𝓗om_{𝒪_X}(E, L)`**, the derived internal Hom of [Stacks, Tag 08DH], read in the same
spelling of `D(𝒪_X)`; `Stacks.SheafOfModules.derivedSheafHom` lands in
`DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf)`. -/
abbrev derivedSheafHomObj
    (E L : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)) :
    DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) :=
  ((derivedSheafHom X.sheaf).obj (op E)).obj L

/-! ### Coherence of the cohomology sheaves -/

/-- Coherence of an `𝒪_X`-module transfers along an isomorphism. -/
private theorem isCoherent_of_iso_stacks {M N : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace}
    (e : M ≅ N) (h : M.IsCoherent) : N.IsCoherent :=
  (isCoherentStacks_of_iso e h.stacksIsCoherent).rootIsCoherent

/-- A one-sided vanishing range of the cohomology objects pulls back along an isomorphism. -/
private theorem exists_isZero_homology_of_iso
    {A B : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)} (e : A ≅ B)
    {r : ℤ → ℤ → Prop}
    (h : ∃ m, ∀ i, r m i →
      IsZero ((DerivedCategory.homologyFunctor
        (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) i).obj B)) :
    ∃ m, ∀ i, r m i →
      IsZero ((DerivedCategory.homologyFunctor
        (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) i).obj A) :=
  h.imp fun _ hm i hi => (hm i hi).of_iso
    ((DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) i).mapIso e)

/-- **Every cohomology sheaf of `E ⊗^𝐋_{𝒪_X} L` is coherent** for a perfect `E` and an `L` all
of whose cohomology sheaves are coherent, with no boundedness assumption on `L`.

A single degree `n` is computed by the canonical truncation `τ_{≤ n+d}L`, where `d` is an upper
bound for the degrees of `E^∨`: that truncation lies in `D^-_Coh(𝒪_X)`, so its derived tensor
product with `E` does too by [Stacks, Tag 0AZS] part (2), while the complementary vertex
`τ_{≥ n+d+1}L` tensors into degrees `≥ n + 1` because `E ⊗^𝐋 - ≅ R𝓗om(E^∨, -)` and the derived
internal Hom out of a complex in degrees `≤ d` shifts a bound below by at most `d`. -/
theorem derivedCategoryB_derivedTensor_of_isPerfect [IsNoetherian X]
    (E L : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hL : DerivedCategoryB.derivedCategoryB
      (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent) L) :
    DerivedCategoryB.derivedCategoryB
      (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent)
      (derivedTensorObj X E L) := by
  classical
  obtain ⟨d, hd⟩ := (isBoundedCoherent_of_isPerfect X (derivedDual X.sheaf E)
    (isPerfect_derivedDual_of_isPerfect X E hE)).1.2
  have hDLE : (derivedDual X.sheaf E).IsLE d :=
    (DerivedCategory.isLE_iff (derivedDual X.sheaf E) d).mpr hd
  have hEb := isBoundedCoherent_of_isPerfect X E hE
  intro n
  let T := (DerivedCategory.TStructure.t.triangleLEGE (n + d) (n + d + 1) rfl).obj L
  have hle₁ : T.obj₁.IsLE (n + d) :=
    DerivedCategory.TStructure.t.isLE_truncLE_obj L (n + d) (n + d) le_rfl
  have hge₃ : T.obj₃.IsGE (n + d + 1) :=
    DerivedCategory.TStructure.t.isGE_truncGE_obj L (n + d + 1) (n + d + 1) le_rfl
  -- The third vertex, tensored with `E`, lives in degrees `≥ n + 1`.
  have hge : (derivedTensorObj X E T.obj₃).IsGE (n + 1) := by
    have := Stacks.SheafOfModules.isGE_derivedSheafHom X.sheaf (derivedDual X.sheaf E)
      T.obj₃ d (n + d + 1) hDLE hge₃
    rw [show n + d + 1 - d = n + 1 by omega] at this
    exact DerivedCategory.TStructure.t.isGE_of_iso
      (derivedTensorIsoSheafHomDual X E T.obj₃ hE).symm (n + 1)
  -- The tensored triangle, and the resulting isomorphism in degree `n`. Tensoring with a fixed
  -- object commutes with the shift and is exact; both are fields of the datum of Tag 06YU and
  -- neither is found by instance search at this spelling.
  have hiso := isIso_homologyMap_derivedTensor_mor₁ X.toRingedSpace E T
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished (n + d) (n + d + 1) rfl L) n
    (DerivedCategory.isZero_of_isGE (derivedTensorObj X E T.obj₃) (n + 1) n (by omega))
    (DerivedCategory.isZero_of_isGE (derivedTensorObj X E T.obj₃) (n + 1) (n - 1) (by omega))
  -- The first vertex has coherent cohomology, so its tensor product with `E` is in `D^-_Coh`.
  have hcoh₁ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) i).obj T.obj₁).IsCoherent := by
    intro i
    by_cases hi : i ≤ n + d
    · have := Stacks.SmallDerivedCategory.isIso_homologyFunctor_map_truncLEι L (n + d) i hi
      exact isCoherent_of_iso_stacks X
        (asIso ((DerivedCategory.homologyFunctor
            (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) i).map
          ((DerivedCategory.TStructure.t.truncLEι (n + d)).app L))).symm (hL i)
    · exact (Stacks.SheafOfModules.isCoherent_of_isZero
        (DerivedCategory.isZero_of_isLE T.obj₁ (n + d) i (by omega))).rootIsCoherent
  have h₁ := _root_.AlgebraicGeometry.TorFormula.derivedCategoryBMinus_derivedTensor X E T.obj₁
    ⟨hEb.1.2, hEb.2⟩
    ⟨⟨n + d, fun m hm => DerivedCategory.isZero_of_isLE T.obj₁ (n + d) m hm⟩, hcoh₁⟩
  exact isCoherent_of_iso_stacks X (@asIso _ _ _ _ _ hiso) (h₁.2 n)

/-- **Every cohomology sheaf of `R𝓗om_{𝒪_X}(E, L)` is coherent** for a perfect `E` and an `L`
all of whose cohomology sheaves are coherent: the internal Hom is the derived tensor product
with the perfect object `E^∨`. -/
theorem derivedCategoryB_derivedSheafHom_of_isPerfect [IsNoetherian X]
    (E L : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hL : DerivedCategoryB.derivedCategoryB
      (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent) L) :
    DerivedCategoryB.derivedCategoryB
      (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent)
      (derivedSheafHomObj X E L) :=
  fun n => isCoherent_of_iso_stacks X
    ((DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) n).mapIso
      (derivedSheafHomIsoTensorDual X E L hE)).symm
    (derivedCategoryB_derivedTensor_of_isPerfect X (derivedDual X.sheaf E) L
      (isPerfect_derivedDual_of_isPerfect X E hE) hL n)

/-! ### Cohomological bounds -/

/-- **A bound above on `L` gives one on `E ⊗^𝐋_{𝒪_X} L`** for a perfect `E`: the derived tensor
product of [Stacks, Tag 06YU] is right t-exact, and `E` is bounded above by part (1). -/
theorem isBoundedAbove_derivedTensor_of_isPerfect [IsNoetherian X]
    (E L : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hL : DerivedCategoryB.IsBoundedAbove L) :
    DerivedCategoryB.IsBoundedAbove (derivedTensorObj X E L) := by
  obtain ⟨a, ha⟩ := (isBoundedCoherent_of_isPerfect X E hE).1.2
  obtain ⟨b, hb⟩ := hL
  have : (derivedTensorObj X E L).IsLE (a + b) :=
    @Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct _ _ _ X.sheaf _ _ _ _ _ _ _
      E L a b ((DerivedCategory.isLE_iff E a).mpr ha) ((DerivedCategory.isLE_iff L b).mpr hb)
  exact ⟨a + b, fun m hm => DerivedCategory.isZero_of_isLE _ (a + b) m hm⟩

/-- **A bound below on `L` gives one on `E ⊗^𝐋_{𝒪_X} L`** for a perfect `E`: the tensor product
is `R𝓗om(E^∨, L)`, and the derived internal Hom out of a bounded-above object into a
bounded-below one is bounded below, the boundedness clause of [Stacks, Tag 0D0C]. -/
theorem isBoundedBelow_derivedTensor_of_isPerfect [IsNoetherian X]
    (E L : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hL : DerivedCategoryB.IsBoundedBelow L) :
    DerivedCategoryB.IsBoundedBelow (derivedTensorObj X E L) := by
  obtain ⟨m, hm⟩ := Stacks.SheafOfModules.isBoundedBelow_derivedSheafHom X.sheaf
    (derivedDual X.sheaf E) L
    (isBoundedCoherent_of_isPerfect X (derivedDual X.sheaf E)
      (isPerfect_derivedDual_of_isPerfect X E hE)).1.2 hL
  exact exists_isZero_homology_of_iso X (derivedTensorIsoSheafHomDual X E L hE) ⟨m, hm⟩

/-- **A bound above on `L` gives one on `R𝓗om_{𝒪_X}(E, L)`** for a perfect `E`: the internal
Hom is the derived tensor product with the perfect object `E^∨`. -/
theorem isBoundedAbove_derivedSheafHom_of_isPerfect [IsNoetherian X]
    (E L : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hL : DerivedCategoryB.IsBoundedAbove L) :
    DerivedCategoryB.IsBoundedAbove (derivedSheafHomObj X E L) := by
  obtain ⟨m, hm⟩ := isBoundedAbove_derivedTensor_of_isPerfect X (derivedDual X.sheaf E) L
    (isPerfect_derivedDual_of_isPerfect X E hE) hL
  exact exists_isZero_homology_of_iso X (derivedSheafHomIsoTensorDual X E L hE) ⟨m, hm⟩

/-- **A bound below on `L` gives one on `R𝓗om_{𝒪_X}(E, L)`** for a perfect `E`: this is the
boundedness clause of [Stacks, Tag 0D0C], `E` being bounded above by part (1). -/
theorem isBoundedBelow_derivedSheafHom_of_isPerfect [IsNoetherian X]
    (E L : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hL : DerivedCategoryB.IsBoundedBelow L) :
    DerivedCategoryB.IsBoundedBelow (derivedSheafHomObj X E L) :=
  Stacks.SheafOfModules.isBoundedBelow_derivedSheafHom X.sheaf E L
    (isBoundedCoherent_of_isPerfect X E hE).1.2 hL

/-! ### Parts (2)-(5) of Tag 0FXU -/

/-- **[Stacks, Tag 0FXU], part (2).** Let `X` be a Noetherian scheme and let `E` in `D(𝒪_X)` be
perfect. If `L` is in `D_Coh(𝒪_X)` then `E ⊗^𝐋_{𝒪_X} L` and `R𝓗om_{𝒪_X}(E, L)` are in
`D_Coh(𝒪_X)`. -/
@[stacks 0FXU "part (2): for L in D_Coh(𝒪_X) both E ⊗^𝐋 L and R𝓗om(E, L) are in D_Coh(𝒪_X)"]
theorem derivedCategoryB_coherent_of_isPerfect [IsNoetherian X]
    (E L : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hL : DerivedCategoryB.derivedCategoryB
      (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent) L) :
    DerivedCategoryB.derivedCategoryB
        (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent)
        (derivedTensorObj X E L) ∧
      DerivedCategoryB.derivedCategoryB
        (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent)
        (derivedSheafHomObj X E L) :=
  ⟨derivedCategoryB_derivedTensor_of_isPerfect X E L hE hL,
    derivedCategoryB_derivedSheafHom_of_isPerfect X E L hE hL⟩

/-- **[Stacks, Tag 0FXU], part (3).** Let `X` be a Noetherian scheme and let `E` in `D(𝒪_X)` be
perfect. If `L` is in `D^b_Coh(𝒪_X)` then `E ⊗^𝐋_{𝒪_X} L` and `R𝓗om_{𝒪_X}(E, L)` are in
`D^b_Coh(𝒪_X)`. -/
@[stacks 0FXU "part (3): for L in D^b_Coh(𝒪_X) both E ⊗^𝐋 L and R𝓗om(E, L) are in \
D^b_Coh(𝒪_X)"]
theorem derivedCategoryBBounded_coherent_of_isPerfect [IsNoetherian X]
    (E L : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hL : DerivedCategoryB.derivedCategoryBBounded
      (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent) L) :
    DerivedCategoryB.derivedCategoryBBounded
        (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent)
        (derivedTensorObj X E L) ∧
      DerivedCategoryB.derivedCategoryBBounded
        (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent)
        (derivedSheafHomObj X E L) :=
  ⟨⟨⟨isBoundedBelow_derivedTensor_of_isPerfect X E L hE hL.1.1,
      isBoundedAbove_derivedTensor_of_isPerfect X E L hE hL.1.2⟩,
    derivedCategoryB_derivedTensor_of_isPerfect X E L hE hL.2⟩,
   ⟨⟨isBoundedBelow_derivedSheafHom_of_isPerfect X E L hE hL.1.1,
      isBoundedAbove_derivedSheafHom_of_isPerfect X E L hE hL.1.2⟩,
    derivedCategoryB_derivedSheafHom_of_isPerfect X E L hE hL.2⟩⟩

/-- **[Stacks, Tag 0FXU], part (4).** Let `X` be a Noetherian scheme and let `E` in `D(𝒪_X)` be
perfect. If `L` is in `D^+_Coh(𝒪_X)` then `E ⊗^𝐋_{𝒪_X} L` and `R𝓗om_{𝒪_X}(E, L)` are in
`D^+_Coh(𝒪_X)`. -/
@[stacks 0FXU "part (4): for L in D^+_Coh(𝒪_X) both E ⊗^𝐋 L and R𝓗om(E, L) are in \
D^+_Coh(𝒪_X)"]
theorem derivedCategoryBPlus_coherent_of_isPerfect [IsNoetherian X]
    (E L : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hL : DerivedCategoryB.derivedCategoryBPlus
      (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent) L) :
    DerivedCategoryB.derivedCategoryBPlus
        (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent)
        (derivedTensorObj X E L) ∧
      DerivedCategoryB.derivedCategoryBPlus
        (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent)
        (derivedSheafHomObj X E L) :=
  ⟨⟨isBoundedBelow_derivedTensor_of_isPerfect X E L hE hL.1,
      derivedCategoryB_derivedTensor_of_isPerfect X E L hE hL.2⟩,
   ⟨isBoundedBelow_derivedSheafHom_of_isPerfect X E L hE hL.1,
      derivedCategoryB_derivedSheafHom_of_isPerfect X E L hE hL.2⟩⟩

/-- **[Stacks, Tag 0FXU], part (5).** Let `X` be a Noetherian scheme and let `E` in `D(𝒪_X)` be
perfect. If `L` is in `D^-_Coh(𝒪_X)` then `E ⊗^𝐋_{𝒪_X} L` and `R𝓗om_{𝒪_X}(E, L)` are in
`D^-_Coh(𝒪_X)`. -/
@[stacks 0FXU "part (5): for L in D^-_Coh(𝒪_X) both E ⊗^𝐋 L and R𝓗om(E, L) are in \
D^-_Coh(𝒪_X)"]
theorem derivedCategoryBMinus_coherent_of_isPerfect [IsNoetherian X]
    (E L : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hL : DerivedCategoryB.derivedCategoryBMinus
      (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent) L) :
    DerivedCategoryB.derivedCategoryBMinus
        (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent)
        (derivedTensorObj X E L) ∧
      DerivedCategoryB.derivedCategoryBMinus
        (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent)
        (derivedSheafHomObj X E L) :=
  ⟨⟨isBoundedAbove_derivedTensor_of_isPerfect X E L hE hL.1,
      derivedCategoryB_derivedTensor_of_isPerfect X E L hE hL.2⟩,
   ⟨isBoundedAbove_derivedSheafHom_of_isPerfect X E L hE hL.1,
      derivedCategoryB_derivedSheafHom_of_isPerfect X E L hE hL.2⟩⟩

end Stacks.AlgebraicGeometry.PerfectCohomology

end
