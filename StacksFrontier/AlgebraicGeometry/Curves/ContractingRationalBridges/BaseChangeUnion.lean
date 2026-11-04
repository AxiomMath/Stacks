module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.SepClosedConjugacy
public import StacksFrontier.AlgebraicGeometry.Curves.NodalLocality

/-!
# Rational bridges after an arbitrary extension of the ground field: the union form

Let `X` be a proper one-dimensional scheme over a field `k` with `H⁰(X, 𝒪_X) = k` and at worst
nodal singularities, and let `C ⊆ X` be a rational bridge. For an *arbitrary* field extension
`K/k` the inverse image of `C` in the base change `X_K` is the scheme-theoretic union of the
reduced structures on the irreducible components of `X_K` lying over `C`, and every one of those
components is a rational bridge of `X_K`.

## Main results

* `AlgebraicGeometry.exists_finset_isRationalBridge_baseChange`: **[Stacks, Tag 0E65] in the
  union form**, for an arbitrary field extension.
* `Stacks.Curves.isRationalBridge_vanishingIdeal_component_baseChange`: an irreducible component
  of `X_K` lying over a rational bridge is itself a rational bridge.
* `Stacks.Curves.finrank_sup_complementaryCurveIdeal_component_eq_two_of_isRationalBridge`: over
  a separably closed extension `Ω/k` every irreducible component of `C_Ω` has complementary
  degree two.
* `AlgebraicGeometry.genus_toSpecΓ_eq_zero_of_genus_eq_zero` and
  `AlgebraicGeometry.genus_eq_zero_of_genus_toSpecΓ_eq_zero`: for a proper integral scheme over a
  field, the genus over the ground field and the genus over the field of global functions vanish
  together.
* `Stacks.Curves.genus_eq_zero_of_support_subset`: a reduced one-dimensional closed subcurve of a
  genus-zero reduced one-dimensional closed subcurve has genus zero.

## How the descent runs

The complementary degree of a component of `C_K` is read off at the algebraic closure `Ω` of `K`.
There the bookkeeping identity `Stacks.Curves.sum_finrank_sup_complementaryCurveIdeal_eq` applies
to the inverse image of the component, whose own components all have complementary degree two by
`Stacks.Curves.finrank_sup_complementaryCurveIdeal_component_eq_two` — the symmetry input of that
statement being the conjugacy of the components of `C_Ω` over a separably closed extension,
`Stacks.Curves.finrank_sup_complementaryCurveIdeal_eq_of_image_eq` — and the identity then
collapses to `deg (Z ∩ X') = 2 h⁰(Z)`. Both sides descend to `K`, the left one by
`Stacks.Curves.finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_comap` and the
right one by `AlgebraicGeometry.finrank_structureSheafCohomology_zero_comap_baseChange`, and the
tower formula `AlgebraicGeometry.finrank_structureSheafCohomology_zero_intersection_eq_mul` turns
the resulting equality into the *relative* degree two that the rational-bridge condition asks for.

The genus clause is obtained the same way round: the inverse image of the component in `X_Ω` is a
closed subcurve of the genus-zero `C_Ω`, hence of genus zero by
`Stacks.Curves.genus_eq_zero_of_support_subset`, and the genus is unchanged by base change.

## Implementation notes

The rational-bridge condition takes the genus over the field of global functions of the bridge,
while base change of the genus is a statement over the ground field. The two are related by
`AlgebraicGeometry.genus_toSpecΓ_eq_zero_of_genus_eq_zero` and its converse: the two cohomology
modules
`H¹(Z, 𝒪_Z)` are restrictions of scalars of one and the same cohomology module of the sheaf of
modules on `Z`, so they have the same underlying group and vanish together, and over a field a
finite-dimensional space is of dimension zero exactly when it vanishes.

The extension `Ω/K` is taken algebraically closed rather than merely separably closed so that the
intermediate field `K` needs no hypothesis at all: everything used of `Ω` is that it is separably
closed, and `AlgebraicClosure K` supplies that for every `K`.

## References

* [Stacks Project, Tag 0E65](https://stacks.math.columbia.edu/tag/0E65)
* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 04KX](https://stacks.math.columbia.edu/tag/04KX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData
open Stacks.Curves

universe u

namespace AlgebraicGeometry

/-- Dimension zero transfers between two field structures on the same underlying group. -/
private theorem finrank_eq_zero_of_finrank_eq_zero {F₁ F₂ M₁ M₂ : Type*} [Field F₁] [Field F₂]
    [AddCommGroup M₁] [Module F₁ M₁] [Module.Finite F₁ M₁] [AddCommGroup M₂] [Module F₂ M₂]
    (h : Module.finrank F₁ M₁ = 0) (e : M₁ ≃+ M₂) : Module.finrank F₂ M₂ = 0 :=
  have := Module.finrank_zero_iff.mp h
  have := e.toEquiv.symm.subsingleton
  Module.finrank_zero_of_subsingleton

/-- **If a proper integral scheme over a field has genus zero over that field, then it has genus
zero over its own field of global functions.** The two cohomology modules `H¹(Z, 𝒪_Z)` entering
`AlgebraicGeometry.genus (Z ⟶ Spec k)` and `AlgebraicGeometry.genus Z.toSpecΓ` are restrictions of
scalars of one and the same cohomology module of the sheaf of modules on `Z`
(`AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverField`), so they have the same
underlying group; over the ground field the module is finite dimensional, so dimension zero means
that it vanishes, and a vanishing module has dimension zero over every ring.

This is not an instance of `AlgebraicGeometry.genus_toSpecΓ_eq_genus`, which identifies the two
genera outright but only when `Γ(Z, 𝒪_Z)` is `k` itself: a rational bridge has a finite extension
of `k` for its global functions, so that hypothesis is unavailable here, and only the vanishing of
the genus — not its value — transfers. -/
theorem genus_toSpecΓ_eq_zero_of_genus_eq_zero (k : Type u) [Field k] {Z : Scheme.{u}}
    [IsIntegral Z] (f : Z ⟶ Spec (.of k)) [IsProper f] (hf : genus f = 0) :
    letI : Field Γ(Z, ⊤) := (isField_of_universallyClosed k f).toField
    letI : IsProper Z.toSpecΓ := Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ f
    genus Z.toSpecΓ = 0 := by
  let : Field Γ(Z, ⊤) := (isField_of_universallyClosed k f).toField
  let : IsProper Z.toSpecΓ := Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ f
  have : FiniteDimensional k (cohomologyOverField k f (SheafOfModules.unit Z.ringCatSheaf) 1) :=
    forall_finiteDimensional_cohomologyOverField_unit k f 1
  have h1 : Module.finrank k
      (cohomologyOverField k f (SheafOfModules.unit Z.ringCatSheaf) 1) = 0 := by
    rw [← (structureSheafCohomologyIsoCohomologyOverField k f 1).toLinearEquiv.finrank_eq]
    exact hf
  rw [genus_eq_finrank_structureSheafCohomology,
    (structureSheafCohomologyIsoCohomologyOverField Γ(Z, ⊤)
      Z.toSpecΓ 1).toLinearEquiv.finrank_eq]
  exact finrank_eq_zero_of_finrank_eq_zero h1 (AddEquiv.refl _)

/-- **If a proper integral scheme over a field has genus zero over its own field of global
functions, then it has genus zero over the ground field.** This is the converse of
`AlgebraicGeometry.genus_toSpecΓ_eq_zero_of_genus_eq_zero` and has the same proof with the roles
of the two fields exchanged. -/
theorem genus_eq_zero_of_genus_toSpecΓ_eq_zero (k : Type u) [Field k] {Z : Scheme.{u}}
    [IsIntegral Z] (f : Z ⟶ Spec (.of k)) [IsProper f]
    (hZ : letI : Field Γ(Z, ⊤) := (isField_of_universallyClosed k f).toField
      letI : IsProper Z.toSpecΓ :=
        Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ f
      genus Z.toSpecΓ = 0) :
    genus f = 0 := by
  let : Field Γ(Z, ⊤) := (isField_of_universallyClosed k f).toField
  let : IsProper Z.toSpecΓ := Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ f
  have : FiniteDimensional Γ(Z, ⊤)
      (cohomologyOverField Γ(Z, ⊤) Z.toSpecΓ (SheafOfModules.unit Z.ringCatSheaf) 1) :=
    forall_finiteDimensional_cohomologyOverField_unit Γ(Z, ⊤) Z.toSpecΓ 1
  have h1 : Module.finrank Γ(Z, ⊤)
      (cohomologyOverField Γ(Z, ⊤) Z.toSpecΓ (SheafOfModules.unit Z.ringCatSheaf) 1) = 0 := by
    rw [← (structureSheafCohomologyIsoCohomologyOverField Γ(Z, ⊤)
      Z.toSpecΓ 1).toLinearEquiv.finrank_eq]
    exact hZ
  rw [genus_eq_finrank_structureSheafCohomology,
    (structureSheafCohomologyIsoCohomologyOverField k f 1).toLinearEquiv.finrank_eq]
  exact finrank_eq_zero_of_finrank_eq_zero h1 (AddEquiv.refl _)

end AlgebraicGeometry

namespace Stacks.Curves

/-- **The reduced induced structure on an irreducible component of a one-dimensional
equidimensional curve has dimension one.** The closed immersion of the reduced structure is a
homeomorphism onto the component, and the component has dimension one by
`Stacks.Curves.topologicalKrullDim_irreducibleComponent_eq_one`. -/
theorem topologicalKrullDim_subscheme_vanishingIdeal_component_eq_one {F : Type u} [Field F]
    {S : Scheme.{u}} (q : S ⟶ Spec (.of F)) [LocallyOfFiniteType q]
    (hS_equidimensional : Equidimensional S) (hS_dimension : topologicalKrullDim S = 1)
    {Z : Set S} (hZ : Z ∈ irreducibleComponents (S : Type u)) :
    topologicalKrullDim (vanishingIdeal (Closeds.closure Z)).subscheme = 1 := by
  have hZclosed : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hrange : Set.range (vanishingIdeal (Closeds.closure Z)).subschemeι.base = Z := by
    simpa [hZclosed.closure_eq] using range_subschemeι_vanishingIdeal (Closeds.closure Z)
  have hemb : Topology.IsEmbedding
      (vanishingIdeal (Closeds.closure Z)).subschemeι.base :=
    IsPreimmersion.isEmbedding (vanishingIdeal (Closeds.closure Z)).subschemeι
  have e : (vanishingIdeal (Closeds.closure Z)).subscheme ≃ₜ Z :=
    hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)
  rw [IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph]
  exact topologicalKrullDim_irreducibleComponent_eq_one q hS_equidimensional hS_dimension Z hZ

/-- An irreducible component with its reduced induced structure is integral. -/
private theorem isIntegral_subscheme_vanishingIdeal_component {Y : Scheme.{u}} {Z : Set Y}
    (hZ : Z ∈ irreducibleComponents (Y : Type u)) :
    IsIntegral (vanishingIdeal (Closeds.closure Z)).subscheme := by
  have h := Stacks.AffineNoProperComponent.isIntegral_componentIdealSheafData (X := Y) ⟨Z, hZ⟩
  rwa [componentIdealSheafData_eq_vanishingIdeal_closure] at h

/-- A scheme of finite type and proper over a field is Noetherian. -/
private theorem isNoetherian_of_isProper_field {k : Type u} [Field k] {S : Scheme.{u}}
    (f : S ⟶ Spec (.of k)) [IsProper f] : IsNoetherian S :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := QuasiCompact.compactSpace_of_compactSpace f
  ⟨⟩

/-- In a Noetherian scheme the irreducible components inside a given set form a finite set. -/
private theorem exists_finset_mem_iff_irreducibleComponents_subset {Y : Scheme.{u}}
    [IsNoetherian Y] (T : Set Y) :
    ∃ Λ : Finset (Set Y), ∀ Z : Set Y, Z ∈ Λ ↔ Z ∈ irreducibleComponents Y ∧ Z ⊆ T :=
  ⟨((finite_irreducibleComponents_of_isNoetherian (X := Y)).subset
    fun _ hZ => hZ.1).toFinset, fun _ => Set.Finite.mem_toFinset _⟩

/-- An irreducible component with its reduced induced structure is equidimensional. -/
private theorem equidimensional_subscheme_vanishingIdeal_component {Y : Scheme.{u}} {Z : Set Y}
    (hZ : Z ∈ irreducibleComponents (Y : Type u)) :
    Equidimensional (vanishingIdeal (Closeds.closure Z)).subscheme :=
  have := isIntegral_subscheme_vanishingIdeal_component hZ
  TopologicalSpace.Equidimensional.of_preirreducibleSpace _

/-- **A reduced one-dimensional closed subcurve of a genus-zero reduced one-dimensional closed
subcurve has genus zero.** Both are unions of irreducible components of `X`
(`Stacks.Curves.eq_union_irreducibleComponents`), so the larger one is the scheme-theoretic union
of the smaller one with the remaining components; those two pieces meet in a closed subscheme of
the intersection of the smaller one with the closure of its complement, which is finite and
discrete by [Stacks, Tag 0E38] (2)(a), so `AlgebraicGeometry.genus_add_le_genus_union` bounds the
sum of the two genera by zero. -/
theorem genus_eq_zero_of_support_subset {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X) (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme]
    (hI_equidimensional : Equidimensional I.subscheme)
    (hI_dimension : topologicalKrullDim I.subscheme = 1)
    (hI_genus : genus (I.subschemeι ≫ (X ↘ Spec (.of k))) = 0)
    (J : X.IdealSheafData) [IsReduced J.subscheme]
    (hJ_equidimensional : Equidimensional J.subscheme)
    (hJ_dimension : topologicalKrullDim J.subscheme = 1)
    (hJ_support : (J.support : Set X) ⊆ (I.support : Set X)) :
    genus (J.subschemeι ≫ (X ↘ Spec (.of k))) = 0 := by
  classical
  have hIun := eq_union_irreducibleComponents hX_equidimensional hX_dimension hX_nodal I
    hI_equidimensional hI_dimension
  have hJun := eq_union_irreducibleComponents hX_equidimensional hX_dimension hX_nodal J
    hJ_equidimensional hJ_dimension
  have hsup : (⨆ D : {D : Set X // D ∈ irreducibleComponents X ∧ D ⊆ (J.support : Set X)},
        Closeds.closure D.1) ⊔
      (⨆ D : {D : Set X // D ∈ irreducibleComponents X ∧ D ⊆ (I.support : Set X) ∧
        ¬ D ⊆ (J.support : Set X)}, Closeds.closure D.1)
      = ⨆ D : {D : Set X // D ∈ irreducibleComponents X ∧ D ⊆ (I.support : Set X)},
        Closeds.closure D.1 := by
    refine le_antisymm (sup_le (iSup_le fun D => ?_) (iSup_le fun D => ?_)) (iSup_le fun D => ?_)
    · exact le_iSup (fun D : {D : Set X // D ∈ irreducibleComponents X ∧
        D ⊆ (I.support : Set X)} => Closeds.closure D.1)
        ⟨D.1, D.2.1, D.2.2.trans hJ_support⟩
    · exact le_iSup (fun D : {D : Set X // D ∈ irreducibleComponents X ∧
        D ⊆ (I.support : Set X)} => Closeds.closure D.1) ⟨D.1, D.2.1, D.2.2.1⟩
    · by_cases hD : D.1 ⊆ (J.support : Set X)
      · exact le_sup_of_le_left (le_iSup
          (fun D : {D : Set X // D ∈ irreducibleComponents X ∧
            D ⊆ (J.support : Set X)} => Closeds.closure D.1) ⟨D.1, D.2.1, hD⟩)
      · exact le_sup_of_le_right (le_iSup
          (fun D : {D : Set X // D ∈ irreducibleComponents X ∧ D ⊆ (I.support : Set X) ∧
            ¬ D ⊆ (J.support : Set X)} => Closeds.closure D.1) ⟨D.1, D.2.1, D.2.2, hD⟩)
  have hIJ : J ⊓ vanishingIdeal
      (⨆ D : {D : Set X // D ∈ irreducibleComponents X ∧ D ⊆ (I.support : Set X) ∧
        ¬ D ⊆ (J.support : Set X)}, Closeds.closure D.1) = I := by
    refine Eq.trans (congrArg (fun T => T ⊓ vanishingIdeal
      (⨆ D : {D : Set X // D ∈ irreducibleComponents X ∧ D ⊆ (I.support : Set X) ∧
        ¬ D ⊆ (J.support : Set X)}, Closeds.closure D.1)) hJun) ?_
    rw [← vanishingIdeal_sup, hsup, ← hIun]
  have hJc : complementaryCurveIdeal J = vanishingIdeal
      (⨆ D : {D : Set X // D ∈ irreducibleComponents X ∧ ¬ D ⊆ (J.support : Set X)},
        Closeds.closure D.1) :=
    complementaryCurveIdeal_eq_union_irreducibleComponents hX_nodal J
  have hcomp : complementaryCurveIdeal J ≤ vanishingIdeal
      (⨆ D : {D : Set X // D ∈ irreducibleComponents X ∧ D ⊆ (I.support : Set X) ∧
        ¬ D ⊆ (J.support : Set X)}, Closeds.closure D.1) := by
    rw [hJc]
    refine vanishingIdeal_antimono (iSup_le fun D => le_iSup
      (fun D : {D : Set X // D ∈ irreducibleComponents X ∧ ¬ D ⊆ (J.support : Set X)} =>
        Closeds.closure D.1) ⟨D.1, D.2.1, D.2.2.2⟩)
  have hint := isZero_structureSheafCohomology_of_intersection_le hX_equidimensional
    hX_dimension hX_nodal J hJ_equidimensional hJ_dimension
    (J ⊔ vanishingIdeal
      (⨆ D : {D : Set X // D ∈ irreducibleComponents X ∧ D ⊆ (I.support : Set X) ∧
        ¬ D ⊆ (J.support : Set X)}, Closeds.closure D.1))
    (sup_le_sup_left hcomp J) 1 one_pos
  have hle := genus_add_le_genus_union k (X ↘ Spec (.of k)) J (vanishingIdeal
    (⨆ D : {D : Set X // D ∈ irreducibleComponents X ∧ D ⊆ (I.support : Set X) ∧
      ¬ D ⊆ (J.support : Set X)}, Closeds.closure D.1)) hint
  rw [hIJ, hI_genus] at hle
  omega

/-- The inverse image of a closed subscheme of `X` in a base change of `X` along a field
extension is a closed subscheme of the corresponding base change of that closed subscheme. -/
theorem isPullback_subschemeι_comap_baseChange (k E : Type u) [Field k] [Field E] [Algebra k E]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (C : X.IdealSheafData) :
    IsPullback ((C.comapIso (pullback.fst (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k E))))).hom ≫
        pullback.snd (pullback.fst (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k E)))) C.subschemeι)
      ((C.comap (pullback.fst (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k E))))).subschemeι ≫
        pullback.snd (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k E))))
      (C.subschemeι ≫ (X ↘ Spec (.of k)))
      (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
  isPullback_subschemeι_comp _ _ (X ↘ Spec (.of k)) _ (IsPullback.of_hasPullback _ _) C

/-- A rational bridge is the reduced induced structure on its support, that support being an
irreducible component. -/
theorem eq_vanishingIdeal_closure_support_of_isRationalBridge (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    C = vanishingIdeal (Closeds.closure (C.support : Set X)) := by
  have : IsIntegral C.subscheme := hC.isIntegral
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme C _
    (Closeds.ext (by rw [Closeds.coe_closure, C.support.isClosed.closure_eq]))

/-- A rational bridge of a one-dimensional curve has dimension one. -/
theorem topologicalKrullDim_subscheme_eq_one_of_isRationalBridge (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (hX_dimension : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    topologicalKrullDim C.subscheme = 1 := by
  have hXeq : Equidimensional X :=
    equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hX_dimension
  have h := topologicalKrullDim_subscheme_vanishingIdeal_component_eq_one (X ↘ Spec (.of k))
    hXeq hX_dimension hC.support_mem_irreducibleComponents
  rwa [← eq_vanishingIdeal_closure_support_of_isRationalBridge k X hC] at h

/-- **The inverse image of a rational bridge in a base change is reduced.** The bridge is an
irreducible component of a nodal curve, hence geometrically reduced over the ground field by
[Stacks, Tag 0E37] in the form `Stacks.Curves.geometricallyReduced_vanishingIdeal_component`, and
its inverse image in the base change is one of its base changes. -/
theorem isReduced_subscheme_comap_baseChange_of_isRationalBridge (k E : Type u) [Field k]
    [Field E] [Algebra k E] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (hX_dimension : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hX_nodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    IsReduced (C.comap (pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k E))))).subscheme := by
  have hXeq : Equidimensional X :=
    equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hX_dimension
  have : GeometricallyReduced (C.subschemeι ≫ (X ↘ Spec (.of k))) := by
    have h := geometricallyReduced_vanishingIdeal_component (k := k) (X := X) hXeq hX_dimension
      hX_nodal hC.support_mem_irreducibleComponents
    rwa [← eq_vanishingIdeal_closure_support_of_isRationalBridge k X hC] at h
  exact GeometricallyReduced.geometrically_isReduced
    (Spec.map (CommRingCat.ofHom (algebraMap k E))) _ _
    (isPullback_subschemeι_comap_baseChange k E X C)

/-- **The inverse image of a rational bridge in a base change is equidimensional.** It is a base
change of the bridge, which is irreducible of dimension one, and the local dimension of a base
change over a field is the local dimension downstairs, part (1) of [Stacks, Tag 02FY]. -/
theorem equidimensional_subscheme_comap_baseChange_of_isRationalBridge (k E : Type u) [Field k]
    [Field E] [Algebra k E] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (hX_dimension : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    Equidimensional (C.comap (pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k E))))).subscheme := by
  have : IsIntegral C.subscheme := hC.isIntegral
  exact TopologicalSpace.Equidimensional.of_homeomorph
    (isPullback_subschemeι_comap_baseChange k E X C).isoPullback.hom.homeomorph
    (equidimensional_pullback_spec_algebraMap k E (C.subschemeι ≫ (X ↘ Spec (.of k)))
      (TopologicalSpace.Equidimensional.of_preirreducibleSpace C.subscheme)
      (topologicalKrullDim_subscheme_eq_one_of_isRationalBridge k X hX_dimension hC))

/-- **The inverse image of a rational bridge in a base change has dimension one**, by [Stacks,
Tag 0BY9]. -/
theorem topologicalKrullDim_subscheme_comap_baseChange_of_isRationalBridge_eq_one
    (k E : Type u) [Field k] [Field E] [Algebra k E] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (hX_dimension : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    topologicalKrullDim (C.comap (pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k E))))).subscheme = 1 :=
  (topologicalKrullDim_baseChange k E _ _ (C.subschemeι ≫ (X ↘ Spec (.of k)))
      (isPullback_subschemeι_comap_baseChange k E X C)).trans
    (topologicalKrullDim_subscheme_eq_one_of_isRationalBridge k X hX_dimension hC)

/-- **The inverse image of a rational bridge in a base change has genus zero.** The genus of the
bridge over the ground field is zero because its genus over its own field of global functions is
(`AlgebraicGeometry.genus_eq_zero_of_genus_toSpecΓ_eq_zero`), and the genus is unchanged by base
change. -/
theorem genus_subschemeι_comap_baseChange_of_isRationalBridge_eq_zero
    (k E : Type u) [Field k] [Field E] [Algebra k E] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    genus ((C.comap (pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k E))))).subschemeι ≫
      pullback.snd (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k E)))) = 0 := by
  have : IsIntegral C.subscheme := hC.isIntegral
  refine (genus_baseChange k E _ _ (C.subschemeι ≫ (X ↘ Spec (.of k)))
    (isPullback_subschemeι_comap_baseChange k E X C)).trans ?_
  exact genus_eq_zero_of_genus_toSpecΓ_eq_zero k (C.subschemeι ≫ (X ↘ Spec (.of k)))
    hC.genus_eq_zero


/-- **Over a separably closed extension every irreducible component of the inverse image of a
rational bridge has complementary degree two.**

The components of `C_Ω` all have the same image in `X`, namely the support of `C`, so they are
conjugate and their complementary degrees agree
(`Stacks.Curves.finrank_sup_complementaryCurveIdeal_eq_of_image_eq`, [Stacks, Tag 04KY]); the
inverse image of `C` has complementary degree twice its own degree, by the tower formula applied
to the degree-two clause of `AlgebraicGeometry.IsRationalBridge`; and
`Stacks.Curves.finrank_sup_complementaryCurveIdeal_component_eq_two` turns those two facts into
the value two at each single component. -/
theorem finrank_sup_complementaryCurveIdeal_component_eq_two_of_isRationalBridge
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (hX_dimension : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalBridge k X C)
    (Z₀ : Set (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))
    (hZ₀ : Z₀ ∈ irreducibleComponents (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))
    (hZ₀_subset : Z₀ ⊆ ((C.comap (pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))).support :
        Set (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))) :
    Module.finrank Ω (structureSheafCohomology
        ((vanishingIdeal (Closeds.closure Z₀) ⊔
            complementaryCurveIdeal (vanishingIdeal (Closeds.closure Z₀))).subschemeι ≫
          pullback.snd (X ↘ Spec (.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) 0) = 2 := by
  classical
  let g : Spec (.of Ω) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let Y := pullback (X ↘ Spec (.of k)) g
  let p : Y ⟶ X := pullback.fst (X ↘ Spec (.of k)) g
  let s : Y ⟶ Spec (.of Ω) := pullback.snd (X ↘ Spec (.of k)) g
  let _ : Y.Over (Spec (.of Ω)) := ⟨s⟩
  have : IsProper (Y ↘ Spec (.of Ω)) := by
    show IsProper (pullback.snd (X ↘ Spec (.of k)) g); infer_instance
  have : LocallyOfFiniteType (Y ↘ Spec (.of Ω)) := inferInstance
  have hsq : IsPullback p s (X ↘ Spec (.of k)) g := IsPullback.of_hasPullback _ _
  have : IsNoetherian X := isNoetherian_of_isProper_field (X ↘ Spec (.of k))
  have hXeq : Equidimensional X :=
    equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hX_dimension
  have hYeq : Equidimensional Y :=
    equidimensional_pullback_spec_algebraMap k Ω (X ↘ Spec (.of k)) hXeq hX_dimension
  have hYdim : topologicalKrullDim Y = 1 :=
    (topologicalKrullDim_baseChange k Ω p s (X ↘ Spec (.of k)) hsq).trans hX_dimension
  have hYnodal : HasAtWorstNodalSingularities Ω Y :=
    hasAtWorstNodalSingularities_baseChange k Ω X hXeq hX_dimension hX_nodal
  -- the inverse image of the bridge
  have hIred : IsReduced (C.comap p).subscheme :=
    isReduced_subscheme_comap_baseChange_of_isRationalBridge k Ω X hX_dimension hX_nodal hC
  have hIeq : Equidimensional (C.comap p).subscheme :=
    equidimensional_subscheme_comap_baseChange_of_isRationalBridge k Ω X hX_dimension hC
  have hIdim : topologicalKrullDim (C.comap p).subscheme = 1 :=
    topologicalKrullDim_subscheme_comap_baseChange_of_isRationalBridge_eq_one k Ω X hX_dimension
      hC
  have hIgenus : genus ((C.comap p).subschemeι ≫ s) = 0 :=
    genus_subschemeι_comap_baseChange_of_isRationalBridge_eq_zero k Ω X hC
  -- the components of the inverse image of the bridge
  have : IsNoetherian Y := isNoetherian_of_isProper_field (Y ↘ Spec (.of Ω))
  obtain ⟨Λ, hΛ⟩ := exists_finset_mem_iff_irreducibleComponents_subset
    ((C.comap p).support : Set Y)
  have hZcomp : ∀ Z ∈ Λ, Z ∈ irreducibleComponents (Y : Type u) :=
    fun Z hZ => ((hΛ Z).mp hZ).1
  have hZred : ∀ Z ∈ Λ, IsReduced (vanishingIdeal (Closeds.closure Z)).subscheme :=
    fun Z _ => Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hZeq : ∀ Z ∈ Λ, Equidimensional (vanishingIdeal (Closeds.closure Z)).subscheme :=
    fun Z hZ => equidimensional_subscheme_vanishingIdeal_component (hZcomp Z hZ)
  have hZdim : ∀ Z ∈ Λ,
      topologicalKrullDim (vanishingIdeal (Closeds.closure Z)).subscheme = 1 :=
    fun Z hZ => topologicalKrullDim_subscheme_vanishingIdeal_component_eq_one
      (Y ↘ Spec (.of Ω)) hYeq hYdim (hZcomp Z hZ)
  -- the complementary degree of the inverse image of the bridge is twice its degree
  have : Flat p := MorphismProperty.of_isPullback hsq.flip
    (Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance))
  have : IsIntegral C.subscheme := hC.isIntegral
  have hdeg_down : Module.finrank k (structureSheafCohomology
        ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k))) 0)
      = Module.finrank k (structureSheafCohomology
        (C.subschemeι ≫ (X ↘ Spec (.of k))) 0) * 2 := by
    rw [finrank_structureSheafCohomology_zero_intersection_eq_mul (X ↘ Spec (.of k)) C]
    exact congrArg _ hC.intersection_finrank_eq_two
  have hdelta : Module.finrank Ω (structureSheafCohomology
        ((C.comap p ⊔ complementaryCurveIdeal (C.comap p)).subschemeι ≫ s) 0)
      = Module.finrank k (structureSheafCohomology
        ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k))) 0) := by
    have h := finrank_structureSheafCohomology_zero_comap_baseChange k Ω
      (X ↘ Spec (.of k)) p s hsq (intersectionWithComplementaryCurveIdeal C)
    rwa [← intersectionWithComplementaryCurveIdeal_comap C p] at h
  have hzero : Module.finrank Ω (structureSheafCohomology ((C.comap p).subschemeι ≫ s) 0)
      = Module.finrank k (structureSheafCohomology
        (C.subschemeι ≫ (X ↘ Spec (.of k))) 0) :=
    finrank_structureSheafCohomology_zero_comap_baseChange k Ω (X ↘ Spec (.of k)) p s hsq C
  have hdeg : Module.finrank Ω (structureSheafCohomology
        ((C.comap p ⊔ complementaryCurveIdeal (C.comap p)).subschemeι ≫ s) 0)
      = 2 * Module.finrank Ω (structureSheafCohomology ((C.comap p).subschemeι ≫ s) 0) := by
    rw [hdelta, hzero, hdeg_down, Nat.mul_comm]
  -- the components all have the same image in `X`, hence the same complementary degree
  have himg : ∀ Z ∈ Λ, p.base '' Z = (C.support : Set X) := by
    intro Z hZ
    refine eq_of_mem_irreducibleComponents_subset
      (mapsTo_irreducibleComponents_baseChange k Ω X (X ↘ Spec (.of k)) (hZcomp Z hZ))
      hC.support_mem_irreducibleComponents ?_
    rintro x ⟨y, hy, rfl⟩
    have hmem := ((hΛ Z).mp hZ).2 hy
    rwa [Scheme.IdealSheafData.support_comap] at hmem
  have hsym : ∀ Z ∈ Λ, ∀ W ∈ Λ,
      Module.finrank Ω (structureSheafCohomology
          ((vanishingIdeal (Closeds.closure Z) ⊔
            complementaryCurveIdeal (vanishingIdeal (Closeds.closure Z))).subschemeι ≫
              (Y ↘ Spec (.of Ω))) 0)
        = Module.finrank Ω (structureSheafCohomology
          ((vanishingIdeal (Closeds.closure W) ⊔
            complementaryCurveIdeal (vanishingIdeal (Closeds.closure W))).subschemeι ≫
              (Y ↘ Spec (.of Ω))) 0) := by
    intro Z hZ W hW
    exact finrank_sup_complementaryCurveIdeal_eq_of_image_eq k Ω X hXeq hX_dimension hX_nodal
      Z W (hZcomp Z hZ) (hZcomp W hW) (by rw [himg Z hZ, himg W hW])
  exact finrank_sup_complementaryCurveIdeal_component_eq_two (k := Ω) (X := Y) hYeq hYdim hYnodal
    (C.comap p) hIeq hIdim Λ hΛ hZred hZeq hZdim hIgenus hdeg hsym
    ((hΛ Z₀).mpr ⟨hZ₀, hZ₀_subset⟩)

/-- **An irreducible component of the inverse image of a rational bridge is a rational bridge.**

Let `X` be a proper one-dimensional at worst nodal curve over `k` with `H⁰(X, 𝒪_X) = k`, let
`C ⊆ X` be a rational bridge, and let `K/k` be an arbitrary field extension. An irreducible
component `W` of `X_K` contained in the inverse image of `C`, taken with its reduced induced
structure, is a rational bridge of `X_K`.

Both the degree clause and the genus clause are read off over `Ω = AlgebraicClosure K`, where the
components of `C_Ω` are conjugate; see the module documentation. -/
theorem isRationalBridge_vanishingIdeal_component_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (hX_dimension : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalBridge k X C)
    (W : Set (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    (hW : W ∈ irreducibleComponents (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    (hW_subset : W ⊆ ((C.comap (pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).support :
        Set (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) :
    letI : (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).Over (Spec (.of K)) :=
      ⟨pullback.snd _ _⟩
    letI : IsProper ((pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) ↘ Spec (.of K)) :=
      inferInstanceAs (IsProper (pullback.snd (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    IsRationalBridge K (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (vanishingIdeal (Closeds.closure W)) := by
  classical
  let gK : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let YK := pullback (X ↘ Spec (.of k)) gK
  let pK : YK ⟶ X := pullback.fst (X ↘ Spec (.of k)) gK
  let _ : YK.Over (Spec (.of K)) := ⟨pullback.snd (X ↘ Spec (.of k)) gK⟩
  have : IsProper (YK ↘ Spec (.of K)) :=
    inferInstanceAs (IsProper (pullback.snd (X ↘ Spec (.of k)) gK))
  have : LocallyOfFiniteType (YK ↘ Spec (.of K)) := inferInstance
  have hsqK : IsPullback pK (YK ↘ Spec (.of K)) (X ↘ Spec (.of k)) gK :=
    IsPullback.of_hasPullback _ _
  have hXeq : Equidimensional X :=
    equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hX_dimension
  have hKeq : Equidimensional YK :=
    equidimensional_pullback_spec_algebraMap k K (X ↘ Spec (.of k)) hXeq hX_dimension
  have hKdim : topologicalKrullDim YK = 1 :=
    (topologicalKrullDim_baseChange k K pK (YK ↘ Spec (.of K)) (X ↘ Spec (.of k)) hsqK).trans
      hX_dimension
  have hKnodal : HasAtWorstNodalSingularities K YK :=
    hasAtWorstNodalSingularities_baseChange k K X hXeq hX_dimension hX_nodal
  have hWclosed : IsClosed W := isClosed_of_mem_irreducibleComponents W hW
  -- the component with its reduced induced structure
  have hWint := isIntegral_subscheme_vanishingIdeal_component hW
  have hWsupport : ((vanishingIdeal (Closeds.closure W)).support : Set YK) = W := by
    rw [coe_support_vanishingIdeal, Closeds.coe_closure, hWclosed.closure_eq]
  have hWeq : Equidimensional (vanishingIdeal (Closeds.closure W)).subscheme :=
    equidimensional_subscheme_vanishingIdeal_component hW
  have hWdim : topologicalKrullDim (vanishingIdeal (Closeds.closure W)).subscheme = 1 :=
    topologicalKrullDim_subscheme_vanishingIdeal_component_eq_one (YK ↘ Spec (.of K))
      hKeq hKdim hW
  -- the algebraic closure of `K` carries the `k`-algebra structure and the tower over `K`
  let gΩ : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure K)))
  let YΩ := pullback (X ↘ Spec (.of k)) gΩ
  let pΩ : YΩ ⟶ X := pullback.fst (X ↘ Spec (.of k)) gΩ
  let _ : YΩ.Over (Spec (.of (AlgebraicClosure K))) :=
    ⟨pullback.snd (X ↘ Spec (.of k)) gΩ⟩
  have : IsProper (YΩ ↘ Spec (.of (AlgebraicClosure K))) :=
    inferInstanceAs (IsProper (pullback.snd (X ↘ Spec (.of k)) gΩ))
  have : LocallyOfFiniteType (YΩ ↘ Spec (.of (AlgebraicClosure K))) := inferInstance
  have hsqΩ : IsPullback pΩ (YΩ ↘ Spec (.of (AlgebraicClosure K))) (X ↘ Spec (.of k)) gΩ :=
    IsPullback.of_hasPullback _ _
  have hΩeq : Equidimensional YΩ :=
    equidimensional_pullback_spec_algebraMap k (AlgebraicClosure K) (X ↘ Spec (.of k))
      hXeq hX_dimension
  have hΩdim : topologicalKrullDim YΩ = 1 :=
    (topologicalKrullDim_baseChange k (AlgebraicClosure K) pΩ
      (YΩ ↘ Spec (.of (AlgebraicClosure K))) (X ↘ Spec (.of k)) hsqΩ).trans hX_dimension
  have hΩnodal : HasAtWorstNodalSingularities (AlgebraicClosure K) YΩ :=
    hasAtWorstNodalSingularities_baseChange k (AlgebraicClosure K) X hXeq hX_dimension hX_nodal
  -- the comparison `X_Ω ⟶ X_K`
  let b : YΩ ⟶ YK := baseChangeComparison k K (AlgebraicClosure K) X (X ↘ Spec (.of k))
  have hb : IsPullback b (YΩ ↘ Spec (.of (AlgebraicClosure K))) (YK ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) :=
    isPullback_baseChangeComparison k K (AlgebraicClosure K) X (X ↘ Spec (.of k))
  have hbp : b ≫ pK = pΩ :=
    baseChangeComparison_comp_fst k K (AlgebraicClosure K) X (X ↘ Spec (.of k))
  -- the inverse image of the component in `X_Ω` is the reduced structure on `b ⁻¹' W`
  have : GeometricallyReduced ((vanishingIdeal (Closeds.closure W)).subschemeι ≫
      (YK ↘ Spec (.of K))) :=
    geometricallyReduced_vanishingIdeal_component (k := K) (X := YK) hKeq hKdim hKnodal hW
  have hWpb : IsPullback
      (((vanishingIdeal (Closeds.closure W)).comapIso b).hom ≫
        pullback.snd b (vanishingIdeal (Closeds.closure W)).subschemeι)
      (((vanishingIdeal (Closeds.closure W)).comap b).subschemeι ≫
        (YΩ ↘ Spec (.of (AlgebraicClosure K))))
      ((vanishingIdeal (Closeds.closure W)).subschemeι ≫ (YK ↘ Spec (.of K)))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) :=
    isPullback_subschemeι_comp b (YΩ ↘ Spec (.of (AlgebraicClosure K))) (YK ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) hb
      (vanishingIdeal (Closeds.closure W))
  have hredΩ : IsReduced ((vanishingIdeal (Closeds.closure W)).comap b).subscheme :=
    GeometricallyReduced.geometrically_isReduced
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) _ _ hWpb
  have hsuppΩ : ((vanishingIdeal (Closeds.closure W)).comap b).support
      = Closeds.closure (b.base ⁻¹' W) := by
    apply Closeds.ext
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, coe_support_vanishingIdeal,
      Closeds.coe_closure, Closeds.coe_closure, hWclosed.closure_eq,
      (hWclosed.preimage b.continuous).closure_eq]
  have hcomapΩ : vanishingIdeal (Closeds.closure (b.base ⁻¹' W))
      = (vanishingIdeal (Closeds.closure W)).comap b :=
    (Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ hsuppΩ).symm
  -- `b ⁻¹' W` lies inside the inverse image of the bridge
  have hpreimage : b.base ⁻¹' W ⊆ ((C.comap pΩ).support : Set YΩ) := by
    intro y hy
    have hmem := hW_subset hy
    rw [Scheme.IdealSheafData.support_comap] at hmem ⊢
    change pK.base (b.base y) ∈ (C.support : Set X) at hmem
    show pΩ.base y ∈ (C.support : Set X)
    rwa [← hbp]
  have hΩsub : ((vanishingIdeal (Closeds.closure (b.base ⁻¹' W))).support : Set YΩ)
      ⊆ ((C.comap pΩ).support : Set YΩ) := by
    rw [coe_support_vanishingIdeal, Closeds.coe_closure,
      (hWclosed.preimage b.continuous).closure_eq]
    exact hpreimage
  -- the inverse image of the bridge in `X_Ω`
  have hIredΩ : IsReduced (C.comap pΩ).subscheme :=
    isReduced_subscheme_comap_baseChange_of_isRationalBridge k (AlgebraicClosure K) X
      hX_dimension hX_nodal hC
  have hIeqΩ : Equidimensional (C.comap pΩ).subscheme :=
    equidimensional_subscheme_comap_baseChange_of_isRationalBridge k (AlgebraicClosure K) X
      hX_dimension hC
  have hIdimΩ : topologicalKrullDim (C.comap pΩ).subscheme = 1 :=
    topologicalKrullDim_subscheme_comap_baseChange_of_isRationalBridge_eq_one k
      (AlgebraicClosure K) X hX_dimension hC
  have hIgenusΩ :
      genus ((C.comap pΩ).subschemeι ≫ (YΩ ↘ Spec (.of (AlgebraicClosure K)))) = 0 :=
    genus_subschemeι_comap_baseChange_of_isRationalBridge_eq_zero k (AlgebraicClosure K) X hC
  -- the reduced structure on `b ⁻¹' W` is a one-dimensional subcurve of genus zero
  have : IsReduced (vanishingIdeal (Closeds.closure (b.base ⁻¹' W))).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hJeqΩ : Equidimensional
      (vanishingIdeal (Closeds.closure (b.base ⁻¹' W))).subscheme := by
    rw [hcomapΩ]
    exact TopologicalSpace.Equidimensional.of_homeomorph hWpb.isoPullback.hom.homeomorph
      (equidimensional_pullback_spec_algebraMap K (AlgebraicClosure K)
        ((vanishingIdeal (Closeds.closure W)).subschemeι ≫ (YK ↘ Spec (.of K))) hWeq hWdim)
  have hJdimΩ : topologicalKrullDim
      (vanishingIdeal (Closeds.closure (b.base ⁻¹' W))).subscheme = 1 := by
    rw [hcomapΩ]
    exact (topologicalKrullDim_baseChange K (AlgebraicClosure K) _ _
      ((vanishingIdeal (Closeds.closure W)).subschemeι ≫ (YK ↘ Spec (.of K))) hWpb).trans hWdim
  have hJgenusΩ : genus ((vanishingIdeal (Closeds.closure (b.base ⁻¹' W))).subschemeι ≫
      (YΩ ↘ Spec (.of (AlgebraicClosure K)))) = 0 :=
    genus_eq_zero_of_support_subset (k := AlgebraicClosure K) (X := YΩ) hΩeq hΩdim hΩnodal
      (C.comap pΩ) hIeqΩ hIdimΩ hIgenusΩ (vanishingIdeal (Closeds.closure (b.base ⁻¹' W)))
      hJeqΩ hJdimΩ hΩsub
  -- the bookkeeping identity at the algebraic closure
  have : IsNoetherian YΩ := isNoetherian_of_isProper_field (YΩ ↘ Spec (.of (AlgebraicClosure K)))
  obtain ⟨Λ, hΛ⟩ := exists_finset_mem_iff_irreducibleComponents_subset
    ((vanishingIdeal (Closeds.closure (b.base ⁻¹' W))).support : Set YΩ)
  have hZcomp : ∀ Z ∈ Λ, Z ∈ irreducibleComponents (YΩ : Type u) :=
    fun Z hZ => ((hΛ Z).mp hZ).1
  have hZsub : ∀ Z ∈ Λ, Z ⊆ ((C.comap pΩ).support : Set YΩ) :=
    fun Z hZ => (((hΛ Z).mp hZ).2).trans hΩsub
  have hZred : ∀ Z ∈ Λ, IsReduced (vanishingIdeal (Closeds.closure Z)).subscheme :=
    fun Z _ => Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hZeq : ∀ Z ∈ Λ, Equidimensional (vanishingIdeal (Closeds.closure Z)).subscheme :=
    fun Z hZ => equidimensional_subscheme_vanishingIdeal_component (hZcomp Z hZ)
  have hZdim : ∀ Z ∈ Λ,
      topologicalKrullDim (vanishingIdeal (Closeds.closure Z)).subscheme = 1 :=
    fun Z hZ => topologicalKrullDim_subscheme_vanishingIdeal_component_eq_one
      (YΩ ↘ Spec (.of (AlgebraicClosure K))) hΩeq hΩdim (hZcomp Z hZ)
  have hZgenus : ∀ Z ∈ Λ, genus ((vanishingIdeal (Closeds.closure Z)).subschemeι ≫
      (YΩ ↘ Spec (.of (AlgebraicClosure K)))) = 0 := by
    intro Z hZ
    have := hZred Z hZ
    refine genus_eq_zero_of_support_subset (k := AlgebraicClosure K) (X := YΩ) hΩeq hΩdim
      hΩnodal (C.comap pΩ) hIeqΩ hIdimΩ hIgenusΩ _ (hZeq Z hZ) (hZdim Z hZ) ?_
    have hZclosed : IsClosed Z := isClosed_of_mem_irreducibleComponents Z (hZcomp Z hZ)
    rw [coe_support_vanishingIdeal, Closeds.coe_closure, hZclosed.closure_eq]
    exact hZsub Z hZ
  have hZtwo : ∀ Z ∈ Λ, Module.finrank (AlgebraicClosure K)
      (structureSheafCohomology ((vanishingIdeal (Closeds.closure Z) ⊔
        complementaryCurveIdeal (vanishingIdeal (Closeds.closure Z))).subschemeι ≫
          (YΩ ↘ Spec (.of (AlgebraicClosure K)))) 0) = 2 :=
    fun Z hZ => finrank_sup_complementaryCurveIdeal_component_eq_two_of_isRationalBridge k
      (AlgebraicClosure K) X hX_dimension hX_nodal C hC Z (hZcomp Z hZ) (hZsub Z hZ)
  have hZone : ∀ Z ∈ Λ, Module.finrank (AlgebraicClosure K)
      (structureSheafCohomology ((vanishingIdeal (Closeds.closure Z)).subschemeι ≫
        (YΩ ↘ Spec (.of (AlgebraicClosure K)))) 0) = 1 :=
    fun Z hZ => finrank_structureSheafCohomology_zero_vanishingIdeal_component_eq_one
      (k := AlgebraicClosure K) (X := YΩ) hΩeq hΩdim hΩnodal (hZcomp Z hZ)
  have hsum := sum_finrank_sup_complementaryCurveIdeal_eq (k := AlgebraicClosure K) (X := YΩ)
    hΩeq hΩdim hΩnodal (vanishingIdeal (Closeds.closure (b.base ⁻¹' W))) hJeqΩ hJdimΩ
    Λ hΛ hZred hZeq hZdim hJgenusΩ hZgenus
  rw [Finset.sum_congr rfl hZtwo, Finset.sum_congr rfl hZone, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, mul_one] at hsum
  have hΩtwice : Module.finrank (AlgebraicClosure K) (structureSheafCohomology
        ((vanishingIdeal (Closeds.closure (b.base ⁻¹' W)) ⊔
          complementaryCurveIdeal (vanishingIdeal (Closeds.closure (b.base ⁻¹' W)))).subschemeι ≫
          (YΩ ↘ Spec (.of (AlgebraicClosure K)))) 0)
      = 2 * Module.finrank (AlgebraicClosure K) (structureSheafCohomology
        ((vanishingIdeal (Closeds.closure (b.base ⁻¹' W))).subschemeι ≫
          (YΩ ↘ Spec (.of (AlgebraicClosure K)))) 0) := by
    omega
  -- descend both sides to `K`
  have hdeltaK : Module.finrank (AlgebraicClosure K) (structureSheafCohomology
        ((vanishingIdeal (Closeds.closure (b.base ⁻¹' W)) ⊔
          complementaryCurveIdeal (vanishingIdeal (Closeds.closure (b.base ⁻¹' W)))).subschemeι ≫
          (YΩ ↘ Spec (.of (AlgebraicClosure K)))) 0)
      = Module.finrank K (structureSheafCohomology
        ((vanishingIdeal (Closeds.closure W) ⊔
          complementaryCurveIdeal (vanishingIdeal (Closeds.closure W))).subschemeι ≫
            (YK ↘ Spec (.of K))) 0) :=
    finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_comap K
      (AlgebraicClosure K) (YK ↘ Spec (.of K)) b (YΩ ↘ Spec (.of (AlgebraicClosure K)))
      hb W hWclosed hredΩ
  have hzeroK : Module.finrank (AlgebraicClosure K) (structureSheafCohomology
        ((vanishingIdeal (Closeds.closure (b.base ⁻¹' W))).subschemeι ≫
          (YΩ ↘ Spec (.of (AlgebraicClosure K)))) 0)
      = Module.finrank K (structureSheafCohomology
        ((vanishingIdeal (Closeds.closure W)).subschemeι ≫ (YK ↘ Spec (.of K))) 0) := by
    rw [hcomapΩ]
    exact finrank_structureSheafCohomology_zero_comap_baseChange K (AlgebraicClosure K)
      (YK ↘ Spec (.of K)) b (YΩ ↘ Spec (.of (AlgebraicClosure K))) hb
      (vanishingIdeal (Closeds.closure W))
  rw [hdeltaK, hzeroK] at hΩtwice
  -- the relative degree is two
  let : Field Γ((vanishingIdeal (Closeds.closure W)).subscheme, ⊤) :=
    (isField_of_universallyClosed K
      ((vanishingIdeal (Closeds.closure W)).subschemeι ≫ (YK ↘ Spec (.of K)))).toField
  let : Algebra K Γ((vanishingIdeal (Closeds.closure W)).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫
      ((vanishingIdeal (Closeds.closure W)).subschemeι ≫
        (YK ↘ Spec (.of K))).appTop).hom.toAlgebra
  have : Module.Finite K Γ((vanishingIdeal (Closeds.closure W)).subscheme, ⊤) :=
    RingHom.Finite.comp (finite_appTop_of_universallyClosed K
        ((vanishingIdeal (Closeds.closure W)).subschemeι ≫ (YK ↘ Spec (.of K))))
      (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.finite
  have hpos : 0 < Module.finrank K (structureSheafCohomology
      ((vanishingIdeal (Closeds.closure W)).subschemeι ≫ (YK ↘ Spec (.of K))) 0) := by
    rw [finrank_structureSheafCohomology_zero_eq_finrank_globalSections K
      ((vanishingIdeal (Closeds.closure W)).subschemeι ≫ (YK ↘ Spec (.of K)))]
    exact Module.finrank_pos
  let : Algebra Γ((vanishingIdeal (Closeds.closure W)).subscheme, ⊤)
      Γ((intersectionWithComplementaryCurveIdeal
        (vanishingIdeal (Closeds.closure W))).subscheme, ⊤) :=
    (Scheme.IdealSheafData.inclusion (le_sup_left :
      vanishingIdeal (Closeds.closure W) ≤ intersectionWithComplementaryCurveIdeal
        (vanishingIdeal (Closeds.closure W)))).appTop.hom.toAlgebra
  have htower := finrank_structureSheafCohomology_zero_intersection_eq_mul
    (YK ↘ Spec (.of K)) (vanishingIdeal (Closeds.closure W))
  have hrel : Module.finrank Γ((vanishingIdeal (Closeds.closure W)).subscheme, ⊤)
      Γ((intersectionWithComplementaryCurveIdeal
        (vanishingIdeal (Closeds.closure W))).subscheme, ⊤) = 2 := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [← htower, hΩtwice, Nat.mul_comm]
  -- the closure of the complement of the component is nonempty
  have hXcomp : ((C.support : Set X)ᶜ).Nonempty := by
    let U : X.Opens := C.support.compl
    let u : U.toScheme ⟶ X := U.ι
    by_contra hU
    have : IsEmpty U.toScheme := ⟨fun x => hU ⟨x.1, x.2⟩⟩
    obtain ⟨z⟩ : Nonempty u.image := by
      simpa [u, U, complementaryCurve] using hC.complementaryCurve_nonempty
    have hz := (IsDominant.denseRange : DenseRange u.toImage.base) z
    simp [Set.range_eq_empty] at hz
  have hsurj : Surjective pK :=
    MorphismProperty.of_isPullback hsqK.flip
      (⟨fun _ => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩ : Surjective gK)
  have hWcomp : Nonempty (complementaryCurve (vanishingIdeal (Closeds.closure W))) := by
    obtain ⟨x, hx⟩ := hXcomp
    obtain ⟨y, hy⟩ := hsurj.surj x
    refine ⟨(Scheme.Opens.ι (vanishingIdeal (Closeds.closure W)).support.compl).toImage
      ⟨y, ?_⟩⟩
    intro hmem
    have hyW : y ∈ W := by rwa [← hWsupport]
    have hxy := hW_subset hyW
    rw [Scheme.IdealSheafData.support_comap] at hxy
    change pK.base y ∈ (C.support : Set X) at hxy
    rw [hy] at hxy
    exact hx hxy
  -- the genus of the component is zero
  have hWgenusK : genus ((vanishingIdeal (Closeds.closure W)).subschemeι ≫
      (YK ↘ Spec (.of K))) = 0 := by
    rw [← genus_baseChange K (AlgebraicClosure K) _ _
      ((vanishingIdeal (Closeds.closure W)).subschemeι ≫ (YK ↘ Spec (.of K))) hWpb, ← hcomapΩ]
    exact hJgenusΩ
  have hWgenus : genus (vanishingIdeal (Closeds.closure W)).subscheme.toSpecΓ = 0 :=
    genus_toSpecΓ_eq_zero_of_genus_eq_zero K
      ((vanishingIdeal (Closeds.closure W)).subschemeι ≫ (YK ↘ Spec (.of K))) hWgenusK
  exact ⟨hWint, by rwa [hWsupport], hWcomp, hrel, hWgenus⟩

end Stacks.Curves

namespace AlgebraicGeometry

/-- **[Stacks, Tag 0E65] in the union form.** Let `X` be a proper one-dimensional scheme over a
field `k` with `H⁰(X, 𝒪_X) = k` and at worst nodal singularities, and let `C ⊆ X` be a rational
bridge. For an arbitrary field extension `K/k` — no normality, separability, algebraicity or
finiteness is assumed — the inverse image of `C` in the base change `X_K` is the
scheme-theoretic *union* of a finite set of rational bridges of `X_K`, namely of the reduced
structures on the irreducible components of `X_K` lying over `C`.

The tag asserts a *disjoint* union, which is false; that erratum is recorded at
`AlgebraicGeometry.exists_iso_sigma_isRationalBridge_baseChange`, which proves the disjoint form
under the extra hypothesis that the bridge is geometrically integral over its field of global
functions `k' = Γ(C, 𝒪_C)`. The dichotomy behind the repair is this: a rational bridge is either
geometrically integral over `k'` — exactly the hypothesis that earlier statement carries, and
then `C_K` really is a disjoint union of `[k' ⊗_k K : K]`-many bridges — or it acquires precisely
two geometric components, meeting in one point and carrying one point of `C ∩ X'` each. In the
second case the two components of `C_K` meet, so no disjoint decomposition exists, while the
union form is still correct and is what this statement proves.

What makes each component come out with complementary degree exactly two is a symmetry: over a
separably closed extension the components of `C_Ω` all have the same image in `X` and are
therefore conjugate, so their complementary degrees agree
(`Stacks.Curves.finrank_sup_complementaryCurveIdeal_eq_of_image_eq`). The counting identity
`Stacks.Curves.sum_finrank_sup_complementaryCurveIdeal_eq` alone does not suffice: it only says
that the complementary degrees sum to twice the number of components, which a chain of three
components with degrees `(1, 4, 1)` satisfies just as well. -/
@[stacks 0E65 "base_change_union"]
theorem exists_finset_isRationalBridge_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalBridge k X C) :
    letI : (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).Over (Spec (.of K)) :=
      ⟨pullback.snd _ _⟩
    letI : IsProper ((pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) ↘ Spec (.of K)) :=
      inferInstanceAs (IsProper (pullback.snd (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    ∃ Λ : Finset (Set (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})),
      (∀ Z ∈ Λ, IsRationalBridge K (pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Scheme.IdealSheafData.vanishingIdeal
            (TopologicalSpace.Closeds.closure Z))) ∧
        C.comap (pullback.fst (X ↘ Spec (.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          = Λ.inf fun Z => Scheme.IdealSheafData.vanishingIdeal
              (TopologicalSpace.Closeds.closure Z) := by
  classical
  let gK : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let YK := pullback (X ↘ Spec (.of k)) gK
  let pK : YK ⟶ X := pullback.fst (X ↘ Spec (.of k)) gK
  let sK : YK ⟶ Spec (.of K) := pullback.snd (X ↘ Spec (.of k)) gK
  let _ : YK.Over (Spec (.of K)) := ⟨sK⟩
  have : IsProper (YK ↘ Spec (.of K)) := by
    show IsProper (pullback.snd (X ↘ Spec (.of k)) gK); infer_instance
  have : LocallyOfFiniteType (YK ↘ Spec (.of K)) := inferInstance
  have hsqK : IsPullback pK sK (X ↘ Spec (.of k)) gK := IsPullback.of_hasPullback _ _
  have hXeq : TopologicalSpace.Equidimensional X :=
    equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hdim
  have hKeq : TopologicalSpace.Equidimensional YK :=
    Stacks.Curves.equidimensional_pullback_spec_algebraMap k K (X ↘ Spec (.of k)) hXeq hdim
  have hKdim : topologicalKrullDim YK = 1 :=
    (topologicalKrullDim_baseChange k K pK sK (X ↘ Spec (.of k)) hsqK).trans hdim
  have hKnodal : Stacks.Curves.HasAtWorstNodalSingularities K YK :=
    Stacks.Curves.hasAtWorstNodalSingularities_baseChange k K X hXeq hdim hnodal
  have hIred : IsReduced (C.comap pK).subscheme :=
    Stacks.Curves.isReduced_subscheme_comap_baseChange_of_isRationalBridge k K X hdim hnodal hC
  have hIeq : TopologicalSpace.Equidimensional (C.comap pK).subscheme :=
    Stacks.Curves.equidimensional_subscheme_comap_baseChange_of_isRationalBridge k K X hdim hC
  have hIdim : topologicalKrullDim (C.comap pK).subscheme = 1 :=
    Stacks.Curves.topologicalKrullDim_subscheme_comap_baseChange_of_isRationalBridge_eq_one k K X
      hdim hC
  have : IsNoetherian YK := isNoetherian_of_isProper_field (YK ↘ Spec (.of K))
  obtain ⟨Λ, hΛ⟩ := exists_finset_mem_iff_irreducibleComponents_subset
    ((C.comap pK).support : Set YK)
  refine ⟨Λ, fun Z hZ => ?_, ?_⟩
  · exact Stacks.Curves.isRationalBridge_vanishingIdeal_component_baseChange k K X hdim hnodal
      C hC Z ((hΛ Z).mp hZ).1 ((hΛ Z).mp hZ).2
  · have hunion := Stacks.Curves.eq_union_irreducibleComponents hKeq hKdim hKnodal (C.comap pK)
      hIeq hIdim
    rw [Scheme.IdealSheafData.vanishingIdeal_iSup] at hunion
    rw [hunion, Finset.inf_eq_iInf, iInf_subtype]
    simp only [hΛ]
    rfl

end AlgebraicGeometry

end
