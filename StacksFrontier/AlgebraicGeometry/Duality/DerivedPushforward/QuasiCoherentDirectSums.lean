module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationLevelHomology
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.BoundedDirectSums
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DirectSums
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointBoundedBelow
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.QuasiCoherentDirectImage
public import StacksFrontier.Homology.PseudoCoherent.Locality
import StacksCore.Tactic.StacksAttribute

/-!
# `Rf_*` commutes with arbitrary direct sums on `D_QCoh`

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes. The derived direct
image `Rf_* : D_QCoh(𝒪_X) ⟶ D_QCoh(𝒪_S)` commutes with direct sums indexed by an arbitrary type
of the scheme universe. This is [Stacks, Tag 08DZ].

## Main results

* `Stacks.Duality.DerivedPushforward.isIso_sigmaComparison_of_isQuasicoherent`: the comparison
  morphism `⨁ᵢ Rf_*(Eᵢ) ⟶ Rf_*(⨁ᵢ Eᵢ)` is invertible for a family of objects of `D(𝒪_X)` with
  quasi-coherent cohomology.
* `preservesColimitsOfShape_discrete_quasiCoherentDerivedPushforward` and
  `preservesColimitsOfShape_discrete_qcqsQuasiCoherentDerivedPushforward`, both in the namespace
  `Stacks.Duality.DerivedPushforward`: **[Stacks, Tag 08DZ]** — the restricted functor
  `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)` preserves direct sums indexed by an arbitrary type of the
  scheme universe, first with the quasi-coherence of the cohomology of `Rf_*E` as a hypothesis
  and then with it discharged by [Stacks, Tag 08D5] part (1).

## Implementation notes

The argument is the one in the source, with the spectral sequences of [Stacks, Tag 015J]
replaced by the truncation triangles of the canonical t-structure. Invertibility is tested on
each cohomology sheaf and is local on `S`, so one fixes a degree `q` and an affine open
`V ⊆ S`; after pulling back to `V` the target is quasi-compact, so [Stacks, Tag 08D5] part (2)
bounds the cohomological dimension of `Rf_*` followed by that pullback by some `N`. Writing `G`
for that composite, the family is cut twice:

* below, by the triangle `τ_{≤ q - N}E ⟶ E ⟶ τ_{> q - N}E`, whose first vertex `G` carries into
  degrees `≤ q - 1`, so that `H^q` sees no difference between the second and third vertices;
* above, by the triangle `τ_{≤ q}E' ⟶ E' ⟶ τ_{> q}E'` applied to the result, whose third vertex
  `G` carries into degrees `≥ q + 1` because `Rf_*` moves cohomology to the right, so that `H^q`
  sees no difference between the first and second vertices.

What is left is a family lying in degrees `[q - N + 1, q]`, which is
`Stacks.Duality.DerivedPushforward.isIso_sigmaComparison_of_isGE_isLE`.

Each cut is run on the comparison morphism of triangles
`CategoryTheory.Pretriangulated.coproductMapTriangleHom`, whose three components are the
direct-sum comparison morphisms at the three families of vertices and whose source and target are
both distinguished; `Stacks.Duality.DerivedPushforward.isIso_homologyMap_hom₂_of_isIso_hom₃` and
its companion then move invertibility between components along the long exact sequences.

**The model.** Everything in this file is at `HasDerivedCategory.standard`, because
`AlgebraicGeometry.isLE_rightDerived_pullback_obj` — the form of [Stacks, Tag 08D5] part (2) used
here, over a quasi-compact open of the target — is stated there, part (2) having been *proved*
only at `standard`: its whole chain of Čech and basis inputs is stated there. The dévissage of
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/BoundedDirectSums.lean`, by contrast,
is model-independent, and is used here at the standard model.

The statements below therefore do *not* discharge the direct-sum hypotheses carried by
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_quasiCoherentDerivedPushforward_of_generator`
and `Stacks.Duality.isLeftAdjoint_affineQuasiCoherentDerivedPushforward`: those are stated at the
locally small model, where `D_QCoh` has the direct sums that Brown representability asks for,
and the statements below are about `Stacks.Duality.quasiCoherentDerivedCategory` at `standard`
instead. That gap *is* closed, but elsewhere: part (2) is transported off `standard` in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/UniformBoundAnyModel.lean` and its
restricted form in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/UniformBoundRestrict.lean`, and
`StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasiCoherentDirectSumsLocallySmall`
then re-runs the argument of this file at the locally small model. Only the three declarations of
the `Pullback` section and the `Local`, `Open` and `Qcoh` sections are restated there; the
triangle-cutting lemmas of this file are stated for an arbitrary `[HasDerivedCategory]` and are
reused as they stand.

## References

* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace

universe u v₁ u₁ v₂ u₂

namespace Stacks.Duality.DerivedPushforward

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

attribute [local instance] AlgebraicGeometry.pullback_preservesFiniteLimits_of_isOpenImmersion

/-! ### Moving invertibility between the components of a morphism of triangles -/

section TriangleHom

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory A]

/-- **Invertibility on the second component of a morphism of distinguished triangles**, given it
on the third, when the first vertices are cohomologically silent in degrees `q` and `q + 1`: in
the long exact sequences the second morphism of each triangle is then invertible on `H^q`, and
the square of the morphism of triangles transports invertibility. -/
theorem isIso_homologyMap_hom₂_of_isIso_hom₃
    {T T' : Triangle (DerivedCategory A)} (hT : T ∈ distTriang _) (hT' : T' ∈ distTriang _)
    (φ : T ⟶ T') (q : ℤ)
    (hz : IsZero ((DerivedCategory.homologyFunctor A q).obj T.obj₁))
    (hz' : IsZero ((DerivedCategory.homologyFunctor A (q + 1)).obj T.obj₁))
    (hw : IsZero ((DerivedCategory.homologyFunctor A q).obj T'.obj₁))
    (hw' : IsZero ((DerivedCategory.homologyFunctor A (q + 1)).obj T'.obj₁))
    (h : IsIso ((DerivedCategory.homologyFunctor A q).map φ.hom₃)) :
    IsIso ((DerivedCategory.homologyFunctor A q).map φ.hom₂) := by
  have e₁ : IsIso ((DerivedCategory.homologyFunctor A q).map T.mor₂) :=
    Stacks.TruncationLevel.isIso_homologyMap_mor₂ T hT q hz hz'
  have e₂ : IsIso ((DerivedCategory.homologyFunctor A q).map T'.mor₂) :=
    Stacks.TruncationLevel.isIso_homologyMap_mor₂ T' hT' q hw hw'
  have hsq : (DerivedCategory.homologyFunctor A q).map T.mor₂ ≫
      (DerivedCategory.homologyFunctor A q).map φ.hom₃
      = (DerivedCategory.homologyFunctor A q).map φ.hom₂ ≫
        (DerivedCategory.homologyFunctor A q).map T'.mor₂ := by
    rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂]
  have hl : IsIso ((DerivedCategory.homologyFunctor A q).map T.mor₂ ≫
      (DerivedCategory.homologyFunctor A q).map φ.hom₃) := by
    have := h
    infer_instance
  rw [hsq] at hl
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor A q).map T'.mor₂)

/-- **Invertibility on the second component of a morphism of distinguished triangles**, given it
on the first, when the third vertices are cohomologically silent in degrees `q` and `q - 1`. -/
theorem isIso_homologyMap_hom₂_of_isIso_hom₁
    {T T' : Triangle (DerivedCategory A)} (hT : T ∈ distTriang _) (hT' : T' ∈ distTriang _)
    (φ : T ⟶ T') (q : ℤ)
    (hz : IsZero ((DerivedCategory.homologyFunctor A q).obj T.obj₃))
    (hz' : IsZero ((DerivedCategory.homologyFunctor A (q - 1)).obj T.obj₃))
    (hw : IsZero ((DerivedCategory.homologyFunctor A q).obj T'.obj₃))
    (hw' : IsZero ((DerivedCategory.homologyFunctor A (q - 1)).obj T'.obj₃))
    (h : IsIso ((DerivedCategory.homologyFunctor A q).map φ.hom₁)) :
    IsIso ((DerivedCategory.homologyFunctor A q).map φ.hom₂) := by
  have e₁ : IsIso ((DerivedCategory.homologyFunctor A q).map T.mor₁) :=
    Stacks.TruncationLevel.isIso_homologyMap_mor₁ T hT q hz hz'
  have e₂ : IsIso ((DerivedCategory.homologyFunctor A q).map T'.mor₁) :=
    Stacks.TruncationLevel.isIso_homologyMap_mor₁ T' hT' q hw hw'
  have hsq : (DerivedCategory.homologyFunctor A q).map T.mor₁ ≫
      (DerivedCategory.homologyFunctor A q).map φ.hom₂
      = (DerivedCategory.homologyFunctor A q).map φ.hom₁ ≫
        (DerivedCategory.homologyFunctor A q).map T'.mor₁ := by
    rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁]
  have hr : IsIso ((DerivedCategory.homologyFunctor A q).map φ.hom₁ ≫
      (DerivedCategory.homologyFunctor A q).map T'.mor₁) := by
    have := h
    infer_instance
  rw [← hsq] at hr
  exact IsIso.of_isIso_comp_left ((DerivedCategory.homologyFunctor A q).map T.mor₁) _

end TriangleHom

/-! ### Pullback to an open of the target, on the derived category -/

section Pullback

variable {S V : Scheme.{u}} (j : V ⟶ S) [IsOpenImmersion j]

/-- Pullback along an open immersion of the target, on unbounded derived categories. It is exact,
so no derivation is involved. -/
abbrev derivedPullbackOpen : DerivedCategory S.Modules ⥤ DerivedCategory V.Modules :=
  (Scheme.Modules.pullback j).mapDerivedCategory

/-- `Stacks.Duality.DerivedPushforward.derivedPullbackOpen` preserves direct sums: pullback does,
being a left adjoint, hence so does its action on cochain complexes, and the localization
functor is essentially surjective and preserves direct sums. -/
theorem preservesColimitsOfShape_discrete_derivedPullbackOpen (α : Type u) :
    PreservesColimitsOfShape (Discrete α) (derivedPullbackOpen j) := by
  have h₁ : PreservesColimitsOfShape (Discrete α)
      ((Scheme.Modules.pullback j).mapHomologicalComplex (ComplexShape.up ℤ)) := inferInstance
  have h₂ : PreservesColimitsOfShape (Discrete α) (DerivedCategory.Q (C := V.Modules)) :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts V.Modules α
  have h₃ : PreservesColimitsOfShape (Discrete α)
      ((Scheme.Modules.pullback j).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) := comp_preservesColimitsOfShape _ _
  have h₄ : PreservesColimitsOfShape (Discrete α)
      (DerivedCategory.Q ⋙ (Scheme.Modules.pullback j).mapDerivedCategory) :=
    (preservesColimitsOfShape_iff_of_natIso
      (Scheme.Modules.pullback j).mapDerivedCategoryFactors).2 h₃
  exact preservesColimitsOfShape_discrete_of_essSurj_comp
    DerivedCategory.Q (Scheme.Modules.pullback j).mapDerivedCategory α

/-- `Stacks.Duality.DerivedPushforward.derivedPullbackOpen` preserves lower cohomological bounds:
it is exact, so it commutes with the cohomology functors. -/
theorem isGE_derivedPullbackOpen_obj (E : DerivedCategory S.Modules) (n : ℤ) (hE : E.IsGE n) :
    ((derivedPullbackOpen j).obj E).IsGE n := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  have := hE
  exact ((Scheme.Modules.pullback j).map_isZero (E.isZero_of_isGE n i hi)).of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (Scheme.Modules.pullback j) i).app E)

end Pullback

/-! ### Cutting a family of distinguished triangles in a fixed degree -/

section Cut

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]
  (Ψ : C ⥤ DerivedCategory B) [Ψ.CommShift ℤ] [Ψ.IsTriangulated]
  {α : Type*} (T : α → Triangle C)
  [HasCoproduct fun k ↦ (T k).obj₁] [HasCoproduct fun k ↦ (T k).obj₂]
  [HasCoproduct fun k ↦ (T k).obj₃]
  [HasCoproduct fun k ↦ Ψ.obj ((T k).obj₁)] [HasCoproduct fun k ↦ Ψ.obj ((T k).obj₂)]
  [HasCoproduct fun k ↦ Ψ.obj ((T k).obj₃)]

/-- **Cutting away the first vertices.** For a family of distinguished triangles whose first
vertices `Ψ` carries to objects with no cohomology in degrees `q` and `q + 1`, both separately
and after taking the direct sum, invertibility in degree `q` of the direct-sum comparison
morphism at the third family of vertices gives it at the second. -/
theorem isIso_homologyMap_sigmaComparison_of_isIso_obj₃ (hT : ∀ k, T k ∈ distTriang C) (q : ℤ)
    (hz : IsZero ((DerivedCategory.homologyFunctor B q).obj (∐ fun k ↦ Ψ.obj ((T k).obj₁))))
    (hz' : IsZero ((DerivedCategory.homologyFunctor B (q + 1)).obj
      (∐ fun k ↦ Ψ.obj ((T k).obj₁))))
    (hw : IsZero ((DerivedCategory.homologyFunctor B q).obj (Ψ.obj (∐ fun k ↦ (T k).obj₁))))
    (hw' : IsZero ((DerivedCategory.homologyFunctor B (q + 1)).obj
      (Ψ.obj (∐ fun k ↦ (T k).obj₁))))
    (h : IsIso ((DerivedCategory.homologyFunctor B q).map
      (sigmaComparison Ψ fun k ↦ (T k).obj₃))) :
    IsIso ((DerivedCategory.homologyFunctor B q).map
      (sigmaComparison Ψ fun k ↦ (T k).obj₂)) :=
  isIso_homologyMap_hom₂_of_isIso_hom₃
    (coproductMapTriangle_mem_distTriang Ψ T hT)
    (Ψ.map_distinguished _ (coproductTriangle_distinguished T hT))
    (coproductMapTriangleHom Ψ T) q hz hz' hw hw' h

/-- **Cutting away the third vertices.** For a family of distinguished triangles whose third
vertices `Ψ` carries to objects with no cohomology in degrees `q` and `q - 1`, both separately
and after taking the direct sum, invertibility in degree `q` of the direct-sum comparison
morphism at the first family of vertices gives it at the second. -/
theorem isIso_homologyMap_sigmaComparison_of_isIso_obj₁ (hT : ∀ k, T k ∈ distTriang C) (q : ℤ)
    (hz : IsZero ((DerivedCategory.homologyFunctor B q).obj (∐ fun k ↦ Ψ.obj ((T k).obj₃))))
    (hz' : IsZero ((DerivedCategory.homologyFunctor B (q - 1)).obj
      (∐ fun k ↦ Ψ.obj ((T k).obj₃))))
    (hw : IsZero ((DerivedCategory.homologyFunctor B q).obj (Ψ.obj (∐ fun k ↦ (T k).obj₃))))
    (hw' : IsZero ((DerivedCategory.homologyFunctor B (q - 1)).obj
      (Ψ.obj (∐ fun k ↦ (T k).obj₃))))
    (h : IsIso ((DerivedCategory.homologyFunctor B q).map
      (sigmaComparison Ψ fun k ↦ (T k).obj₁))) :
    IsIso ((DerivedCategory.homologyFunctor B q).map
      (sigmaComparison Ψ fun k ↦ (T k).obj₂)) :=
  isIso_homologyMap_hom₂_of_isIso_hom₁
    (coproductMapTriangle_mem_distTriang Ψ T hT)
    (Ψ.map_distinguished _ (coproductTriangle_distinguished T hT))
    (coproductMapTriangleHom Ψ T) q hz hz' hw hw' h

end Cut

/-! ### The derived direct image followed by pullback to an open of the target -/

section Local

variable {X S : Scheme.{u}} (f : X ⟶ S) {V : Scheme.{u}} (j : V ⟶ S) [IsOpenImmersion j]

/-- The derived direct image along `f`, followed by pullback to an open `V ⊆ S`. By
[Stacks, Tag 08FE] this is the derived direct image along the restricted morphism
`f⁻¹V ⟶ V`, which is what gives it a uniform cohomological bound when `V` is quasi-compact. -/
abbrev derivedPushforwardPullback : DerivedCategory X.Modules ⥤ DerivedCategory V.Modules :=
  Stacks.Duality.derivedPushforward f ⋙ derivedPullbackOpen j

/-- The unit exhibiting `Stacks.Duality.derivedPushforward` as a right derived functor of
degreewise direct image. -/
abbrev derivedPushforwardUnit :
    (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ Stacks.Duality.derivedPushforward f :=
  (Stacks.Duality.homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-- **The uniform cohomological bound of [Stacks, Tag 08D5] part (2), after pullback to a
quasi-compact open of the target.** -/
theorem exists_isLE_derivedPushforwardPullback_obj [AlgebraicGeometry.QuasiCompact f]
    [AlgebraicGeometry.QuasiSeparated f] [CompactSpace V] :
    ∃ N : ℤ, ∀ (E : DerivedCategory X.Modules) (d : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) →
      E.IsLE d → ((derivedPushforwardPullback f j).obj E).IsLE (d + N - 1) :=
  AlgebraicGeometry.isLE_rightDerived_pullback_obj f j
    (Stacks.Duality.derivedPushforward f) (derivedPushforwardUnit f)

/-- `Rf_*` followed by pullback to an open of the target preserves lower cohomological bounds:
`Rf_*` moves cohomology to the right and pullback along an open immersion is exact. -/
theorem isGE_derivedPushforwardPullback_obj (E : DerivedCategory X.Modules) (n : ℤ)
    (hE : E.IsGE n) : ((derivedPushforwardPullback f j).obj E).IsGE n := by
  have := hE
  exact isGE_derivedPullbackOpen_obj j _ n
    (Stacks.DerivedFunctor.isGE_totalRightDerived_obj (Scheme.Modules.pushforward f) E n)

end Local

/-! ### Quasi-coherence of a direct sum -/

/-- The cohomology sheaves of a direct sum of objects with quasi-coherent cohomology are
quasi-coherent: cohomology commutes with direct sums, and quasi-coherent modules are closed
under them. -/
theorem isQuasicoherent_homology_sigmaObj {X : Scheme.{u}} {α : Type u}
    (E : α → DerivedCategory X.Modules)
    (hqc : ∀ k (i : ℤ), ((DerivedCategory.homologyFunctor X.Modules i).obj (E k)).IsQuasicoherent)
    (i : ℤ) : ((DerivedCategory.homologyFunctor X.Modules i).obj (∐ E)).IsQuasicoherent := by
  have hpres : PreservesColimit (Discrete.functor E)
      (DerivedCategory.homologyFunctor X.Modules i) :=
    (Stacks.Duality.preservesColimitsOfShape_derivedHomologyFunctor X.Modules i).preservesColimit
  refine (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (PreservesCoproduct.iso (DerivedCategory.homologyFunctor X.Modules i) E).symm ?_
  exact isQuasicoherent_sigmaObj X _ fun k ↦ hqc k i

/-- The direct-sum comparison morphism of a composite is invertible as soon as those of the two
factors are. -/
private theorem isIso_sigmaComparison_comp_of_isIso {C : Type*} [Category C] {D : Type*}
    [Category D] {E : Type*} [Category E] {J : Type*} (R : C ⥤ D) (S : D ⥤ E) (X : J → C)
    [HasCoproduct X] [HasCoproduct fun j ↦ R.obj (X j)]
    [HasCoproduct fun j ↦ S.obj (R.obj (X j))] (hR : IsIso (sigmaComparison R X))
    (hS : IsIso (sigmaComparison S fun j ↦ R.obj (X j))) : IsIso (sigmaComparison (R ⋙ S) X) := by
  rw [sigmaComparison_comp]
  infer_instance

/-! ### The two cuts, and the statement over an affine open of the target -/

variable {X S : Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.QuasiCompact f]
  [AlgebraicGeometry.QuasiSeparated f]

section Open
variable {V : Scheme.{u}} (j : V ⟶ S) [IsOpenImmersion j]

/-- **The upper cut.** For a family lying in degrees `≥ a`, the direct-sum comparison morphism
of `Rf_*` followed by pullback to a quasi-compact open of the target is invertible in every
degree `q`: the triangle `τ_{≤ q}E ⟶ E ⟶ τ_{> q}E` has its third vertex carried into degrees
`≥ q + 1`, which `H^q` and `H^{q-1}` do not see, and its first vertex lies in the window
`[a, q]`, where the dévissage of
`Stacks.Duality.DerivedPushforward.isIso_sigmaComparison_of_isGE_isLE` applies. -/
theorem isIso_homologyMap_sigmaComparison_of_isGE {α : Type u}
    (Z : α → DerivedCategory X.Modules) (a : ℤ)
    (hge : ∀ k, (Z k).IsGE a) (q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor V.Modules q).map
      (sigmaComparison (derivedPushforwardPullback f j) Z)) := by
  have hvan : ∀ (k : α) (m : ℤ), m < q + 1 →
      IsZero ((DerivedCategory.homologyFunctor V.Modules m).obj
        ((derivedPushforwardPullback f j).obj
          ((DerivedCategory.TStructure.t.truncGT q).obj (Z k)))) := fun k m hm ↦
    DerivedCategory.isZero_of_isGE _ (q + 1) m hm
      (hX := isGE_derivedPushforwardPullback_obj f j _ (q + 1) inferInstance)
  have hsum : ∀ m : ℤ, m < q + 1 → IsZero ((DerivedCategory.homologyFunctor V.Modules m).obj
      ((derivedPushforwardPullback f j).obj
        (∐ fun k ↦ (DerivedCategory.TStructure.t.truncGT q).obj (Z k)))) := fun m hm ↦
    DerivedCategory.isZero_of_isGE _ (q + 1) m hm
      (hX := isGE_derivedPushforwardPullback_obj f j _ (q + 1)
        (Stacks.Duality.isGE_sigmaObj X.Modules _ (q + 1) fun _ ↦ inferInstance))
  have hbase : IsIso ((DerivedCategory.homologyFunctor V.Modules q).map
      (sigmaComparison (derivedPushforwardPullback f j)
        fun k ↦ (DerivedCategory.TStructure.t.truncLE q).obj (Z k))) := by
    have hb : IsIso (sigmaComparison (Stacks.Duality.derivedPushforward f)
        (fun k ↦ (DerivedCategory.TStructure.t.truncLE q).obj (Z k))) := by
      refine isIso_sigmaComparison_of_isGE_isLE f a q _ (fun k ↦ ?_) (fun _ ↦ ?_)
      · have := hge k
        infer_instance
      · infer_instance
    have hRj : IsIso (sigmaComparison (derivedPullbackOpen j)
        (fun k ↦ (Stacks.Duality.derivedPushforward f).obj
          ((DerivedCategory.TStructure.t.truncLE q).obj (Z k)))) :=
      isIso_sigmaComparison_of_preservesColimit _ _
        (preservesColimitsOfShape_discrete_derivedPullbackOpen j α).preservesColimit
    have := isIso_sigmaComparison_comp_of_isIso _ _ _ hb hRj
    infer_instance
  exact isIso_homologyMap_sigmaComparison_of_isIso_obj₁ (derivedPushforwardPullback f j)
    (fun k ↦ Triangle.mk
      ((DerivedCategory.TStructure.t.truncLEι q).app (Z k))
      ((DerivedCategory.TStructure.t.truncGTπ q).app (Z k))
      ((DerivedCategory.TStructure.t.truncGTδLE q).app (Z k)))
    (fun k ↦ DerivedCategory.TStructure.t.triangleLEGT_distinguished q (Z k)) q
    (Stacks.Duality.isZero_homologyFunctor_sigmaObj V.Modules _ q fun k ↦ hvan k q (by omega))
    (Stacks.Duality.isZero_homologyFunctor_sigmaObj V.Modules _ (q - 1)
      fun k ↦ hvan k (q - 1) (by omega))
    (hsum q (by omega)) (hsum (q - 1) (by omega)) hbase

variable [CompactSpace V]

/-- **The two cuts together.** For a family of objects of `D(𝒪_X)` with quasi-coherent
cohomology, the direct-sum comparison morphism of `Rf_*` followed by pullback to a quasi-compact
open of the target is invertible in every degree `q`. The triangle
`τ_{≤ q - N}E ⟶ E ⟶ τ_{> q - N}E`, with `N` the bound of [Stacks, Tag 08D5] part (2), has its
first vertex carried into degrees `≤ q - 1`, which `H^q` and `H^{q+1}` do not see, and its third
vertex lies in degrees `≥ q - N + 1`, where
`Stacks.Duality.DerivedPushforward.isIso_homologyMap_sigmaComparison_of_isGE` applies. -/
theorem isIso_homologyMap_sigmaComparison_pullback {α : Type u}
    (E : α → DerivedCategory X.Modules)
    (hqc : ∀ (k : α) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj (E k)).IsQuasicoherent) (q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor V.Modules q).map
      (sigmaComparison (derivedPushforwardPullback f j) E)) := by
  obtain ⟨N, hN⟩ := exists_isLE_derivedPushforwardPullback_obj f j
  have hqcW : ∀ (k : α) (i : ℤ), ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.TStructure.t.truncLE (q - N)).obj (E k))).IsQuasicoherent := fun k i ↦
    Stacks.Duality.isQuasicoherent_homology_truncLE (E k) (hqc k) (q - N) i
  have hvan : ∀ (k : α) (m : ℤ), q - 1 < m →
      IsZero ((DerivedCategory.homologyFunctor V.Modules m).obj
        ((derivedPushforwardPullback f j).obj
          ((DerivedCategory.TStructure.t.truncLE (q - N)).obj (E k)))) := fun k m hm ↦
    DerivedCategory.isZero_of_isLE _ (q - N + N - 1) m (by omega)
      (hX := hN _ (q - N) (hqcW k) inferInstance)
  have hsum : ∀ m : ℤ, q - 1 < m → IsZero ((DerivedCategory.homologyFunctor V.Modules m).obj
      ((derivedPushforwardPullback f j).obj
        (∐ fun k ↦ (DerivedCategory.TStructure.t.truncLE (q - N)).obj (E k)))) := fun m hm ↦
    DerivedCategory.isZero_of_isLE _ (q - N + N - 1) m (by omega)
      (hX := hN _ (q - N) (fun i ↦ isQuasicoherent_homology_sigmaObj _ hqcW i)
        (Stacks.Duality.isLE_sigmaObj X.Modules _ (q - N) fun _ ↦ inferInstance))
  exact isIso_homologyMap_sigmaComparison_of_isIso_obj₃ (derivedPushforwardPullback f j)
    (fun k ↦ Triangle.mk
      ((DerivedCategory.TStructure.t.truncLEι (q - N)).app (E k))
      ((DerivedCategory.TStructure.t.truncGTπ (q - N)).app (E k))
      ((DerivedCategory.TStructure.t.truncGTδLE (q - N)).app (E k)))
    (fun k ↦ DerivedCategory.TStructure.t.triangleLEGT_distinguished (q - N) (E k)) q
    (Stacks.Duality.isZero_homologyFunctor_sigmaObj V.Modules _ q fun k ↦ hvan k q (by omega))
    (Stacks.Duality.isZero_homologyFunctor_sigmaObj V.Modules _ (q + 1)
      fun k ↦ hvan k (q + 1) (by omega))
    (hsum q (by omega)) (hsum (q + 1) (by omega))
    (isIso_homologyMap_sigmaComparison_of_isGE f j
      (fun k ↦ (DerivedCategory.TStructure.t.truncGT (q - N)).obj (E k)) (q - N + 1)
      (fun _ ↦ inferInstance) q)

end Open

/-- **`Rf_*` commutes with arbitrary direct sums of objects with quasi-coherent cohomology.**
Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes and let `E` be a
family of objects of `D(𝒪_X)` with quasi-coherent cohomology sheaves, indexed by a type of the
scheme universe. Then the canonical morphism `⨁ₖ Rf_*(Eₖ) ⟶ Rf_*(⨁ₖ Eₖ)` is an isomorphism.

Invertibility is tested on each cohomology sheaf and is local on `S`, so it is enough to check
it after restriction to each affine open `U ⊆ S`; restriction is isomorphic to pullback, pullback
commutes with the cohomology functors, and over an affine open the statement is
`Stacks.Duality.DerivedPushforward.isIso_homologyMap_sigmaComparison_pullback`. -/
theorem isIso_sigmaComparison_of_isQuasicoherent {α : Type u}
    (E : α → DerivedCategory X.Modules)
    (hqc : ∀ (k : α) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj (E k)).IsQuasicoherent) :
    IsIso (sigmaComparison (Stacks.Duality.derivedPushforward f) E) := by
  rw [DerivedCategory.isIso_iff]
  intro q
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict _
    (fun U : S.affineOpens ↦ (U : S.Opens)) (IsOpenCover.mk (iSup_affineOpens_eq_top S))
    fun U ↦ ?_
  have hA : IsAffine (U : S.Opens).toScheme := U.2
  have hC : CompactSpace (U : S.Opens).toScheme :=
    Scheme.compactSpace_of_isAffine (U : S.Opens).toScheme
  have hloc := isIso_homologyMap_sigmaComparison_pullback f (U : S.Opens).ι E hqc q
  have hRj : IsIso (sigmaComparison (derivedPullbackOpen (U : S.Opens).ι)
      (fun k ↦ (Stacks.Duality.derivedPushforward f).obj (E k))) :=
    isIso_sigmaComparison_of_preservesColimit _ _
      (preservesColimitsOfShape_discrete_derivedPullbackOpen (U : S.Opens).ι α).preservesColimit
  have hstep : IsIso ((DerivedCategory.homologyFunctor (U : S.Opens).toScheme.Modules q).map
      ((derivedPullbackOpen (U : S.Opens).ι).map
        (sigmaComparison (Stacks.Duality.derivedPushforward f) E))) := by
    rw [sigmaComparison_comp, Functor.map_comp] at hloc
    have := hRj
    exact IsIso.of_isIso_comp_left
      ((DerivedCategory.homologyFunctor (U : S.Opens).toScheme.Modules q).map
        (sigmaComparison (derivedPullbackOpen (U : S.Opens).ι)
          (fun k ↦ (Stacks.Duality.derivedPushforward f).obj (E k)))) _
  have hpb := (NatIso.isIso_map_iff
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (Scheme.Modules.pullback (U : S.Opens).ι) q)
    (sigmaComparison (Stacks.Duality.derivedPushforward f) E)).1 hstep
  exact (NatIso.isIso_map_iff
    (Scheme.Modules.restrictFunctorIsoPullback (U : S.Opens).ι) _).2 hpb


/-! ### [Stacks, Tag 08DZ] -/

section Qcoh

/-- **`D_QCoh(𝒪_Z)` is closed under direct sums** indexed by a type of the scheme universe, at
the model in force here. This is [Stacks, Tag 08DT]; it is proved exactly as
`Stacks.Duality.DerivedPushforward.derivedQuasicoherent_isClosedUnderCoproducts`, which states it
at the locally small model instead. -/
theorem isClosedUnderCoproducts_derivedQuasicoherent (Z : Scheme.{u}) (α : Type u) :
    (DerivedCategoryB.derivedCategoryB (A := Z.Modules)
      (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).IsClosedUnderColimitsOfShape
      (Discrete α) :=
  Stacks.Duality.derivedCategoryB_isClosedUnderCoproducts _ _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre Z)
    (isQuasicoherent_sigmaObj Z)

variable {X S : Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.QuasiCompact f]
  [AlgebraicGeometry.QuasiSeparated f]

/-- **`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)` commutes with direct sums**, with the quasi-coherence
of the cohomology sheaves of `Rf_*E` taken as a hypothesis.

The inclusion of `D_QCoh` preserves direct sums, because the quasi-coherent objects are closed
under them, and reflects isomorphisms, being fully faithful; and the restricted functor followed
by the inclusion on the target *is* the inclusion on the source followed by `Rf_*`, where
`Stacks.Duality.DerivedPushforward.isIso_sigmaComparison_of_isQuasicoherent` applies. -/
theorem preservesColimitsOfShape_discrete_quasiCoherentDerivedPushforward
    (hpush : ∀ (K : Stacks.Duality.quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor S.Modules i).obj
        ((Stacks.Duality.derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (α : Type u) :
    PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward f hpush) := by
  have hclX := isClosedUnderCoproducts_derivedQuasicoherent X α
  have hclS := isClosedUnderCoproducts_derivedQuasicoherent S α
  refine preservesColimitsOfShape_discrete_of_isIso_sigmaComparison _ fun Ê ↦ ?_
  have hiX : PreservesColimitsOfShape (Discrete α)
      (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf))) := inferInstance
  have hiS : PreservesColimitsOfShape (Discrete α)
      (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (A := S.Modules)
        (SheafOfModules.isQuasicoherent S.ringCatSheaf))) := inferInstance
  have hRf : IsIso (sigmaComparison (Stacks.Duality.derivedPushforward f)
      (fun k ↦ (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf))).obj (Ê k))) :=
    isIso_sigmaComparison_of_isQuasicoherent f _ fun k i ↦ (Ê k).2 i
  have hiXc : IsIso (sigmaComparison (ObjectProperty.ι
      (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf))) Ê) :=
    isIso_sigmaComparison_of_preservesColimit _ Ê hiX.preservesColimit
  have hiSc : IsIso (sigmaComparison (ObjectProperty.ι
      (DerivedCategoryB.derivedCategoryB (A := S.Modules)
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)))
      (fun k ↦ (Stacks.Duality.quasiCoherentDerivedPushforward f hpush).obj (Ê k))) :=
    isIso_sigmaComparison_of_preservesColimit _ _ hiS.preservesColimit
  exact isIso_sigmaComparison_of_isIso_comp
    (Stacks.Duality.quasiCoherentDerivedPushforward f hpush)
    (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (A := S.Modules)
      (SheafOfModules.isQuasicoherent S.ringCatSheaf))) Ê inferInstance
    (isIso_sigmaComparison_comp_of_isIso _ (Stacks.Duality.derivedPushforward f) _ hiXc hRf) hiSc

/-- **`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)`** for a quasi-compact and quasi-separated morphism of
schemes. That `Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_S)` is [Stacks, Tag 08D5] part (1),
`AlgebraicGeometry.isQuasicoherent_derivedPushforward`, so no hypothesis is left. -/
abbrev qcqsQuasiCoherentDerivedPushforward :
    Stacks.Duality.quasiCoherentDerivedCategory X ⥤
      Stacks.Duality.quasiCoherentDerivedCategory S :=
  Stacks.Duality.quasiCoherentDerivedPushforward f
    fun K i ↦ AlgebraicGeometry.isQuasicoherent_derivedPushforward f K i

/-- **[Stacks, Tag 08DZ].** Let `f : X ⟶ S` be a quasi-separated and quasi-compact morphism of
schemes. Then `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)` commutes with direct sums: for every index type
`α` of the scheme universe it preserves `α`-indexed direct sums.

The index types are those of the scheme universe because those are the ones for which
`D_QCoh(𝒪_X)` has direct sums at all ([Stacks, Tag 08DT],
`AlgebraicGeometry.hasCoproducts_quasicoherentDerivedCategory`). -/
@[stacks 08DZ]
theorem preservesColimitsOfShape_discrete_qcqsQuasiCoherentDerivedPushforward (α : Type u) :
    PreservesColimitsOfShape (Discrete α) (qcqsQuasiCoherentDerivedPushforward f) :=
  preservesColimitsOfShape_discrete_quasiCoherentDerivedPushforward f _ α

end Qcoh

end Stacks.Duality.DerivedPushforward

end
