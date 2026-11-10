module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.WhitneyHomotopy
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.TotalLocalizedChern
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.WhitneyDirectSum
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedModificationComparison

/-!
# The Whitney formula for localized Chern classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i : Z ⟶ X` be a closed immersion and let
`E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` be a distinguished triangle of perfect objects of `D(𝒪_X)` such that
`E₃ ⟶ E₁[1]` satisfies one of the conditions (a)–(d) of Stacks 0FBD. If `E₁|_{X ∖ Z}` and
`E₃|_{X ∖ Z}` are finite locally free of rank `< p₁` and `< p₃` placed in degree `0`, then
Stacks 0FBD states

  `c⁽ᵖ¹⁺ᵖ³⁾(Z ⟶ X, E₂) = c⁽ᵖ¹⁾(Z ⟶ X, E₁) c⁽ᵖ³⁾(Z ⟶ X, E₃)`   in `A⁽ᵖ¹⁺ᵖ³⁾(Z ⟶ X)`,

and if `E₁|_{X ∖ Z}` and `E₃|_{X ∖ Z}` are zero, Stacks 0FBE states
`P_p(Z ⟶ X, E₂) = P_p(Z ⟶ X, E₁) + P_p(Z ⟶ X, E₃)` for all `p` and
`ch(Z ⟶ X, E₂) = ch(Z ⟶ X, E₁) + ch(Z ⟶ X, E₃)`.

This file assembles the proof of the source.

* *The statement makes sense.* The rank bound for `E₂` is
  `Stacks.Chow.LocalizedChernData.exists_isFiniteLocallyFreeOfRankLT_restrict_obj₂`. Rotating the
  triangle, a representation of `E₃ ⟶ E₁[1]` after an envelope `f : Y ⟶ X` by a map
  `γ : 𝓐^• ⟶ 𝓑^•` of locally bounded complexes of finite locally free modules gives one of
  `Lf^*E₁ ⟶ Lf^*E₂` by `P₁ ⟶ C(φ)`, with `P₁ = 𝓑^•[-1]`, `P₃ = 𝓐^•[-1]` and `φ = -γ[-1]`
  (`Stacks.Chow.exists_envelope_mappingCone_presentation`), so the Chern classes of `E₁`, `E₂`,
  `E₃` are defined by Stacks 0F9F.
* *The components of degree below the cutoff* are the Whitney formula of Stacks 0F9F.
* *Reduction to an envelope.* Restriction along the envelope `f` is injective (Stacks 0GUC) and
  compatible with the classes (Stacks 0FB3) and the products of Stacks 0FA0, so it suffices to
  prove the identity on `Y`, where `Lf^*E₂ ≅ C(φ)`, `Lf^*E₁ ≅ P₁` and `Lf^*E₃ ≅ P₃[1]`.
* *Deformation to the direct sum.* On `Y` the classes of `C(φ)` are those of
  `C(0) = P₁ ⊕ P₃[1] ≅ Lf^*E₁ ⊕ Lf^*E₃`
  (`Stacks.Chow.LocalizedChernData.localizedChern_mappingCone_eq`,
  `Stacks.Chow.LocalizedChernData.localizedPowerSum_mappingCone_eq`).
* *The direct sum.* For `A`, `B` represented by locally bounded complexes of finite locally free
  modules, the last paragraph of the proof of Stacks 0FBD computes the classes of `A ⊕ B` on the
  modification `W = W_A ×_{𝐏¹_X} W_B` of the graph constructions, from Stacks 0FAU, Stacks 0FE8 and
  Stacks 0FAY, resp. Stacks 0FAZ
  (`Stacks.Chow.LocalizedChernData.totalLocalizedChern_eq_cutoffMul_of_modification`,
  `Stacks.Chow.LocalizedChernData.localizedPowerSum_eq_add_of_modification`, and Stacks 0FE8 for
  `A ⊕ B` and `Lg_A^*Q_A ⊕ Lg_B^*Q_B` on `W`,
  `Stacks.Chow.LocalizedChernData.localizedChern_biprod_eq_modificationChernClass`).

## Main results

* `Stacks.Chow.LocalizedChernData.totalLocalizedChern_triangle` — Stacks 0FBD.
* `Stacks.Chow.LocalizedChernData.totalLocalizedChern_triangle_eq_cutoffMul` — the identity of
  Stacks 0FBD with any output cutoff `r ≥ p₁ + p₃ - 1`.
* `Stacks.Chow.LocalizedChernData.localizedPowerSum_localizedChernChar_triangle` — Stacks 0FBE,
  with its two halves `Stacks.Chow.LocalizedChernData.localizedPowerSum_triangle` and
  `Stacks.Chow.LocalizedChernData.localizedChernChar_triangle`.
* `Stacks.Chow.LocalizedChernData.totalLocalizedChern_biprod_eq_cutoffMul`,
  `Stacks.Chow.LocalizedChernData.localizedPowerSum_biprod_eq_add` — the direct-sum case, for
  objects represented by locally bounded complexes of finite locally free modules.
* `Stacks.Chow.exists_iso_mappingCone_of_mor₃` — the middle vertex of a distinguished triangle
  whose third morphism is represented by a map of complexes `γ` is the mapping cone of `-γ[-1]`.
* `Stacks.Chow.HasTriangleChernCondition.of_mor₃`,
  `Stacks.Chow.hasDefinedChernClasses_triangle_of_mor₃` — the conditions of Stacks 0FBD on
  `E₃ ⟶ E₁[1]` give those of Stacks 0F9F on `E₁ ⟶ E₂`, and the Chern classes of `E₁`, `E₂`, `E₃`
  are defined.

## Implementation notes

The two tagged theorems state the conditions (a)–(d) of the source on the morphism
`E₃ ⟶ E₁[1]` directly, as a disjunction in the source's order. They are the conditions of
Stacks 0F9F read on `E₃ ⟶ E₁[1]` in place of `E₁ ⟶ E₂`, and the intermediate lemmas take them in
that form, `Stacks.Chow.HasTriangleChernCondition`;
`Stacks.Chow.hasTriangleChernCondition_of_conditions` passes from one to the other.

The rank bound for `E₂|_{X ∖ Z}` obtained is `< p₁ + p₃ - 1`, so the identity holds with any
output cutoff `r` with `p₁ + p₃ ≤ r + 1` (`Stacks.Chow.localizedGradingCutoffMul`); the source's
case is `r = p₁ + p₃`, and the case `p₁ = p₃ = r = 1` is the multiplicativity in the ring
`A⁽¹⁾(Z ⟶ X)` used by Stacks 0FES.

## References

* [Stacks Project, Tag 0FBD](https://stacks.math.columbia.edu/tag/0FBD)
* [Stacks Project, Tag 0FBE](https://stacks.math.columbia.edu/tag/0FBE)
* [Stacks Project, Tag 0F9F](https://stacks.math.columbia.edu/tag/0F9F)
* [Stacks Project, Tag 0FE8](https://stacks.math.columbia.edu/tag/0FE8)
* [Stacks Project, Tag 0FB3](https://stacks.math.columbia.edu/tag/0FB3)
* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace Stacks.Chow

/-! ### Distinguished triangles whose third morphism is represented by a map of complexes -/

section Cone

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- **The middle vertex of a distinguished triangle as a mapping cone, from its third morphism.**
Let `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` be distinguished in `D(𝒜)` and let `γ : 𝓐 ⟶ 𝓑` be a map of complexes
representing `E₃ ⟶ E₁[1]`. Then `E₁ ≅ 𝓑[-1]` and `E₂ ≅ C(-γ[-1])`, compatibly with
`E₁ ⟶ E₂` and the inclusion `𝓑[-1] ⟶ C(-γ[-1])`: both triangles
`𝓐[-1] ⟶ 𝓑[-1] ⟶ C(-γ[-1]) ⟶ 𝓐` and `E₃[-1] ⟶ E₁ ⟶ E₂ ⟶ E₃` are distinguished, and they agree
on their first morphism. -/
theorem exists_iso_mappingCone_of_mor₃ (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    {A B : CochainComplex C ℤ} (γ : A ⟶ B) (e₃ : DerivedCategory.Q.obj A ≅ T.obj₃)
    (e₁ : DerivedCategory.Q.obj B ≅ T.obj₁⟦(1 : ℤ)⟧)
    (w : DerivedCategory.Q.map γ ≫ e₁.hom = e₃.hom ≫ T.mor₃) :
    ∃ (i₁ : DerivedCategory.Q.obj (B⟦(-1 : ℤ)⟧) ≅ T.obj₁)
      (i₂ : DerivedCategory.Q.obj (CochainComplex.mappingCone (-(γ⟦(-1 : ℤ)⟧'))) ≅ T.obj₂),
      DerivedCategory.Q.map (CochainComplex.mappingCone.inr _) ≫ i₂.hom = i₁.hom ≫ T.mor₁ := by
  let j₁ : DerivedCategory.Q.obj (A⟦(-1 : ℤ)⟧) ≅ T.obj₃⟦(-1 : ℤ)⟧ :=
    (DerivedCategory.Q.commShiftIso (-1 : ℤ)).app A ≪≫ (shiftFunctor _ (-1 : ℤ)).mapIso e₃
  let j₂ : DerivedCategory.Q.obj (B⟦(-1 : ℤ)⟧) ≅ T.obj₁ :=
    (DerivedCategory.Q.commShiftIso (-1 : ℤ)).app B ≪≫ (shiftFunctor _ (-1 : ℤ)).mapIso e₁ ≪≫
      (shiftEquiv (DerivedCategory C) (1 : ℤ)).unitIso.symm.app T.obj₁
  have comm : (DerivedCategory.Q.mapTriangle.obj
      (CochainComplex.mappingCone.triangle (-(γ⟦(-1 : ℤ)⟧')))).mor₁ ≫ j₂.hom =
      j₁.hom ≫ T.invRotate.mor₁ := by
    have h := DerivedCategory.Q.commShiftIso_hom_naturality γ (-1 : ℤ)
    change DerivedCategory.Q.map (-(γ⟦(-1 : ℤ)⟧')) ≫
        ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).hom.app B ≫ (e₁.hom)⟦(-1 : ℤ)⟧' ≫
          (shiftEquiv (DerivedCategory C) (1 : ℤ)).unitIso.inv.app T.obj₁) =
      ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).hom.app A ≫ (e₃.hom)⟦(-1 : ℤ)⟧') ≫
        (-(T.mor₃⟦(-1 : ℤ)⟧') ≫ (shiftEquiv (DerivedCategory C) (1 : ℤ)).unitIso.inv.app T.obj₁)
    simp only [Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc,
      neg_inj]
    have w' : (DerivedCategory.Q.map γ)⟦(-1 : ℤ)⟧' ≫ (e₁.hom)⟦(-1 : ℤ)⟧' =
        (e₃.hom)⟦(-1 : ℤ)⟧' ≫ T.mor₃⟦(-1 : ℤ)⟧' := by
      rw [← Functor.map_comp, ← Functor.map_comp, w]
    rw [reassoc_of% h]
    exact congrArg (fun g => (DerivedCategory.Q.commShiftIso (-1 : ℤ)).hom.app A ≫ g)
      ((reassoc_of% w') ((shiftEquiv (DerivedCategory C) (1 : ℤ)).unitIso.inv.app T.obj₁))
  let e := isoTriangleOfIso₁₂ _ _ (DerivedCategory.mappingCone_triangle_distinguished _)
    (inv_rot_of_distTriang T hT) j₁ j₂ comm
  exact ⟨j₂, Triangle.π₃.mapIso e, e.hom.comm₂⟩

end Cone

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The mapping cone of zero -/

/-- **The mapping cone of zero is the direct sum**: for complexes `K`, `L`, the image in `D(𝒪_Y)`
of the mapping cone of `0 : K ⟶ L` is `L ⊕ K[1]`, the triangle `L ⟶ C(0) ⟶ K[1] ⟶ L[1]` being
distinguished with third morphism zero. -/
theorem nonempty_mappingCone_zero_iso_biprod {Y : Scheme.{u}} (K L : CochainComplex Y.Modules ℤ) :
    Nonempty (DerivedCategory.Q.obj (CochainComplex.mappingCone (C := Y.Modules) (0 : K ⟶ L)) ≅
      DerivedCategory.Q.obj L ⊞ DerivedCategory.Q.obj (K⟦(1 : ℤ)⟧)) := by
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (0 : K ⟶ L))
  have hT : T ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished _
  have hz : T.rotate.mor₃ = 0 := by
    change -(shiftFunctor _ (1 : ℤ)).map (DerivedCategory.Q.map (0 : K ⟶ L)) = 0
    simp
  obtain ⟨e, -⟩ := exists_iso_binaryBiproduct_of_distTriang T.rotate (rot_of_distTriang _ hT) hz
  exact ⟨e ≪≫ biprod.mapIso (Iso.refl _) ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app K).symm⟩

/-! ### The conditions of Stacks 0FBD -/

section Presentation

variable {X : Scheme.{u}} {E₁ E₂ E₃ : DerivedCategory X.Modules}

/-- **A representation of the third morphism after an envelope gives the triangle by a mapping
cone.** Let `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` be distinguished in `D(𝒪_X)`, and let `f : Y ⟶ X` be an
envelope such that `Lf^*E₃ ⟶ Lf^*(E₁[1])` is represented by a map of locally bounded complexes of
finite locally free modules (condition (d) of Stacks 0FBD). Then there are locally bounded
complexes of finite locally free modules `P₁`, `P₃` on `Y` and `φ : P₃ ⟶ P₁` with
`Lf^*E₁ ≅ P₁`, `Lf^*E₂ ≅ C(φ)`, compatibly with `Lf^*E₁ ⟶ Lf^*E₂` and `P₁ ⟶ C(φ)`, and
`Lf^*E₃ ≅ P₃[1]`: `Lf^*` is exact (Stacks 06YJ) and
`Stacks.Chow.exists_iso_mappingCone_of_mor₃` applies. -/
theorem exists_envelope_mappingCone_presentation (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃)
    (c : E₃ ⟶ E₁⟦(1 : ℤ)⟧) (hT : Triangle.mk a b c ∈ distTriang _)
    (h : HasEnvelopeMapPresentation c) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsEnvelope f) (P₁ P₃ : CochainComplex Y.Modules ℤ)
      (φ : P₃ ⟶ P₁) (i₁ : DerivedCategory.Q.obj P₁ ≅ (derivedPullback f.toLRSHom.toShHom).obj E₁)
      (i₂ : DerivedCategory.Q.obj (CochainComplex.mappingCone φ) ≅
        (derivedPullback f.toLRSHom.toShHom).obj E₂),
      IsLocallyBoundedFiniteLocallyFree P₁ ∧ IsLocallyBoundedFiniteLocallyFree P₃ ∧
        DerivedCategory.Q.map (CochainComplex.mappingCone.inr φ) ≫ i₂.hom =
          i₁.hom ≫ (derivedPullback f.toLRSHom.toShHom).map a ∧
        Nonempty (DerivedCategory.Q.obj ((shiftFunctor (CochainComplex Y.Modules ℤ) (1 : ℤ)).obj
          P₃) ≅ (derivedPullback f.toLRSHom.toShHom).obj E₃) := by
  obtain ⟨Y, f, hf, A, B, γ, eA, eB, hA, hB, w⟩ := h
  let F := schemeDerivedPullback f
  let T := F.mapTriangle.obj (Triangle.mk a b c)
  have hT' : T ∈ distTriang _ := F.map_distinguished _ hT
  let e₁ : DerivedCategory.Q.obj B ≅ T.obj₁⟦(1 : ℤ)⟧ := eB ≪≫ (F.commShiftIso (1 : ℤ)).app E₁
  have w' : DerivedCategory.Q.map γ ≫ e₁.hom = eA.hom ≫ T.mor₃ := by
    change DerivedCategory.Q.map γ ≫ eB.hom ≫ (F.commShiftIso (1 : ℤ)).hom.app E₁ =
      eA.hom ≫ F.map c ≫ (F.commShiftIso (1 : ℤ)).hom.app E₁
    have := congrArg (· ≫ (F.commShiftIso (1 : ℤ)).hom.app E₁) w
    simp only [Category.assoc] at this
    exact this.trans (Category.assoc _ _ _)
  obtain ⟨i₁, i₂, hi⟩ := exists_iso_mappingCone_of_mor₃ T hT' γ eA e₁ w'
  exact ⟨Y, f, hf, B⟦(-1 : ℤ)⟧, A⟦(-1 : ℤ)⟧, -(γ⟦(-1 : ℤ)⟧'), i₁, i₂,
    isLocallyBoundedFiniteLocallyFree_shift hB (-1),
    isLocallyBoundedFiniteLocallyFree_shift hA (-1),
    hi, ⟨DerivedCategory.Q.mapIso
      ((shiftFunctorCompIsoId (CochainComplex Y.Modules ℤ) (-1 : ℤ) 1 (by norm_num)).app A) ≪≫ eA⟩⟩

/-- **Condition (d) of Stacks 0FBD on `E₃ ⟶ E₁[1]` gives condition (1) of Stacks 0F9F on
`E₁ ⟶ E₂`**: after the envelope, `Lf^*E₁ ⟶ Lf^*E₂` is represented by the inclusion
`P₁ ⟶ C(φ)` of `Stacks.Chow.exists_envelope_mappingCone_presentation`. -/
theorem HasEnvelopeMapPresentation.mor₁_of_mor₃ {a : E₁ ⟶ E₂} {b : E₂ ⟶ E₃}
    {c : E₃ ⟶ E₁⟦(1 : ℤ)⟧} (hT : Triangle.mk a b c ∈ distTriang _)
    (h : HasEnvelopeMapPresentation c) : HasEnvelopeMapPresentation a := by
  obtain ⟨Y, f, hf, P₁, P₃, φ, i₁, i₂, h₁, h₃, w, -⟩ :=
    exists_envelope_mappingCone_presentation a b c hT h
  exact ⟨Y, f, hf, P₁, _, CochainComplex.mappingCone.inr φ, i₁, i₂, h₁,
    isLocallyBoundedFiniteLocallyFree_mappingCone φ h₃ h₁, w⟩

/-- **The conditions of Stacks 0FBD give condition (1) of Stacks 0F9F.** Let
`E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` be a distinguished triangle in `D(𝒪_X)` with `E₁`, `E₃` perfect, and
suppose `E₃ ⟶ E₁[1]` satisfies one of the conditions (a) `X` quasi-compact, (b) the irreducible
components of `X` quasi-compact, (c) `E₃ ⟶ E₁[1]` represented by a map of locally bounded
complexes of finite locally free modules, (d) the same after an envelope. Then after some envelope
`E₁ ⟶ E₂` is represented by a map of locally bounded complexes of finite locally free modules: the
conditions (a), (b), (c) give (d) for the perfect objects `E₃`, `E₁[1]` (Stacks 0F9F), and
`Stacks.Chow.HasEnvelopeMapPresentation.mor₁_of_mor₃` applies. -/
theorem HasTriangleChernCondition.hasEnvelopeMapPresentation_mor₁ (C : ChowSituation.{u})
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (h₁ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E₁)
    (h₃ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E₃)
    {a : E₁ ⟶ E₂} {b : E₂ ⟶ E₃} {c : E₃ ⟶ E₁⟦(1 : ℤ)⟧} (hT : Triangle.mk a b c ∈ distTriang _)
    (hc : HasTriangleChernCondition c) : HasEnvelopeMapPresentation a :=
  HasEnvelopeMapPresentation.mor₁_of_mor₃ hT (hc.hasEnvelopeMapPresentation C sX h₃
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift h₁ 1))

/-- **The conditions of Stacks 0FBD on `E₃ ⟶ E₁[1]` give a condition of Stacks 0F9F on
`E₁ ⟶ E₂`**, namely its condition (1)
(`Stacks.Chow.HasTriangleChernCondition.hasEnvelopeMapPresentation_mor₁`). -/
theorem HasTriangleChernCondition.of_mor₃ (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (h₁ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E₁)
    (h₃ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E₃)
    {a : E₁ ⟶ E₂} {b : E₂ ⟶ E₃} {c : E₃ ⟶ E₁⟦(1 : ℤ)⟧} (hT : Triangle.mk a b c ∈ distTriang _)
    (hc : HasTriangleChernCondition c) : HasTriangleChernCondition a :=
  Or.inl (hc.hasEnvelopeMapPresentation_mor₁ C sX h₁ h₃ hT)

/-- **The conditions (a)–(d) of Stacks 0FBD**, as the source states them on a morphism
`c : E ⟶ E'` of `D(𝒪_X)` — (a) `X` is quasi-compact, (b) the irreducible components of `X` are
quasi-compact, (c) `c` is represented by a map of locally bounded complexes of finite locally free
`𝒪_X`-modules, (d) the same holds for `Lf^*c` after an envelope `f : Y ⟶ X` — are the four
conditions of Stacks 0F9F on `c`, listed in another order. -/
theorem hasTriangleChernCondition_of_conditions {E E' : DerivedCategory X.Modules} {c : E ⟶ E'}
    (hc : CompactSpace X ∨ (∀ T ∈ irreducibleComponents X, IsCompact T) ∨
      HasMapPresentation c ∨ HasEnvelopeMapPresentation c) :
    HasTriangleChernCondition c := by
  rcases hc with h | h | h | h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inl h

/-- **The Chern classes in Stacks 0FBD are defined.** Let `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` be a
distinguished triangle of perfect objects of `D(𝒪_X)` such that `E₃ ⟶ E₁[1]` satisfies one of the
conditions (a)–(d) of Stacks 0FBD. Then the Chern classes of `E₁`, `E₂` and `E₃` are defined
(Stacks 0F9F, through `Stacks.Chow.HasTriangleChernCondition.of_mor₃`). -/
theorem hasDefinedChernClasses_triangle_of_mor₃ (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (h₁ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E₁)
    (h₂ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E₂)
    (h₃ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E₃)
    {a : E₁ ⟶ E₂} {b : E₂ ⟶ E₃} {c : E₃ ⟶ E₁⟦(1 : ℤ)⟧} (hT : Triangle.mk a b c ∈ distTriang _)
    (hc : HasTriangleChernCondition c) :
    HasDefinedChernClasses E₁ ∧ HasDefinedChernClasses E₂ ∧ HasDefinedChernClasses E₃ :=
  hasDefinedChernClasses_triangle C sX (Triangle.mk a b c) hT h₁ h₂
    (hc.of_mor₃ C sX h₁ h₃ hT)

end Presentation

namespace LocalizedChernData

/-! ### The statement makes sense -/

section Restriction

variable (D : LocalizedChernData.{u}) {E₁ E₂ E₃ : DerivedCategory D.X.Modules}

/-- **The statement of Stacks 0FBD makes sense.** If `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` is distinguished and
`E₁|_{X ∖ Z}`, `E₃|_{X ∖ Z}` are finite locally free of ranks `< p₁`, `< p₃` placed in degree `0`,
then `E₂|_{X ∖ Z}` is finite locally free of rank `< r` placed in degree `0` for every `r` with
`p₁ + p₃ ≤ r + 1` (`Stacks.Chow.exists_isFiniteLocallyFreeOfRankLT_derivedPullback_obj₂`). -/
theorem exists_isFiniteLocallyFreeOfRankLT_restrict_obj₂ (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃)
    (c : E₃ ⟶ E₁⟦(1 : ℤ)⟧) (hT : Triangle.mk a b c ∈ distTriang _) {p₁ p₃ r : ℕ}
    (hr : p₁ + p₃ ≤ r + 1)
    (r₁ : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₁ ∧
        Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj E₁ ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (r₃ : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₃ ∧
        Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj E₃ ≅ (DerivedCategory.singleFunctor _ 0).obj M)) :
    ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M r ∧
        Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj E₂ ≅ (DerivedCategory.singleFunctor _ 0).obj M) := by
  have r₁' : ∃ M : (Scheme.Opens.toScheme (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens)).Modules,
        IsFiniteLocallyFreeOfRankLT M p₁ ∧
      Nonempty ((derivedPullback (Scheme.Opens.ι (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens)).toLRSHom.toShHom).obj
          E₁ ≅ (DerivedCategory.singleFunctor _ 0).obj M) := r₁
  have r₃' : ∃ M : (Scheme.Opens.toScheme (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens)).Modules,
        IsFiniteLocallyFreeOfRankLT M p₃ ∧
      Nonempty ((derivedPullback (Scheme.Opens.ι (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens)).toLRSHom.toShHom).obj
          E₃ ≅ (DerivedCategory.singleFunctor _ 0).obj M) := r₃
  have key := exists_isFiniteLocallyFreeOfRankLT_derivedPullback_obj₂ (Y := D.X)
    (Scheme.Opens.ι (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens)) (Triangle.mk a b c) hT
    (a := p₁) (c := p₃)
  simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃] at key
  have k₂ := key r₁'
  have k₃ := k₂ r₃'
  obtain ⟨M, hM, e⟩ := k₃
  exact ⟨M, hM.mono (by omega), e⟩

/-- **The statement of Stacks 0FBE makes sense**: if `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` is distinguished and
`E₁|_{X ∖ Z}`, `E₃|_{X ∖ Z}` are zero, so is `E₂|_{X ∖ Z}`. -/
theorem isZero_restrict_obj₂ (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (c : E₃ ⟶ E₁⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a b c ∈ distTriang _)
    (z₁ : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E₁))
    (z₃ : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E₃)) :
    IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E₂) :=
  isZero_derivedPullback_obj₂ (Scheme.Opens.ι (⟨(Set.range D.i.base)ᶜ,
    D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens)) (Triangle.mk a b c) hT z₁ z₃

end Restriction

/-! ### The components of degree below the cutoff -/

section Fst

variable (D : LocalizedChernData.{u}) {E₁ E₂ E₃ : DerivedCategory D.X.Modules} {p₁ p₃ r : ℕ}
  (h₁ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₁)
  (h₂ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₂)
  (h₃ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₃)
  (r₁ : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
    D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
    IsFiniteLocallyFreeOfRankLT M p₁ ∧
      Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
          D.X.Opens).isOpenEmbedding)).obj E₁ ≅ (DerivedCategory.singleFunctor _ 0).obj M))
  (r₂ : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
    D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
    IsFiniteLocallyFreeOfRankLT M r ∧
      Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
          D.X.Opens).isOpenEmbedding)).obj E₂ ≅ (DerivedCategory.singleFunctor _ 0).obj M))
  (r₃ : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
    D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
    IsFiniteLocallyFreeOfRankLT M p₃ ∧
      Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
          D.X.Opens).isOpenEmbedding)).obj E₃ ≅ (DerivedCategory.singleFunctor _ 0).obj M))
  (d₁ : HasDefinedChernClasses E₁) (d₂ : HasDefinedChernClasses E₂)
  (d₃ : HasDefinedChernClasses E₃)

/-- **The components of degree `< r` of the identity of Stacks 0FBD with output cutoff `r`.**
Let `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` be a distinguished triangle of perfect objects of `D(𝒪_X)` such that
`E₁ ⟶ E₂` satisfies a condition of Stacks 0F9F, with `E₁|_{X ∖ Z}`, `E₂|_{X ∖ Z}`,
`E₃|_{X ∖ Z}` finite locally free of rank `< p₁`, `< r`, `< p₃` in degree `0`, and
`p₁ + p₃ ≤ r + 1`. In a degree `n < r` the component of `c⁽ʳ⁾(Z ⟶ X, E₂)` is `c_n(E₂)` and that of
the product `c⁽ᵖ¹⁾(Z ⟶ X, E₁) c⁽ᵖ³⁾(Z ⟶ X, E₃)` is `∑_{i + j = n} c_i(E₁) c_j(E₃)`; they agree by
the Whitney formula of Stacks 0F9F. -/
theorem totalLocalizedChern_triangle_cutoffMul_fst (hr : p₁ + p₃ ≤ r + 1) (a : E₁ ⟶ E₂)
    (b : E₂ ⟶ E₃) (c : E₃ ⟶ E₁⟦(1 : ℤ)⟧) (hT : Triangle.mk a b c ∈ distTriang _)
    (ha : HasTriangleChernCondition a) (n : {n : ℤ // n < (r : ℤ)}) :
    (totalLocalizedChern (D := D.withObject E₂ r h₂ r₂) d₂
        (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₂)).1 n =
      (localizedGradingCutoffMul D.base (D.i ≫ D.a) D.a D.i rfl r hr
        (totalLocalizedChern (D := D.withObject E₁ p₁ h₁ r₁) d₁
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₁))
        (totalLocalizedChern (D := D.withObject E₃ p₃ h₃ r₃) d₃
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₃))).1 n := by
  rw [localizedGradingCutoffMul_fst, totalLocalizedChern_fst,
    perfectChernClass_triangle D.base D.a (Triangle.mk a b c) hT h₁ h₂ ha d₁ d₂ d₃,
    TotalChowClass.intComponent_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [localizedGradingPush_totalLocalizedChern (D := D.withObject E₁ p₁ h₁ r₁) d₁
      (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₁),
    localizedGradingPush_totalLocalizedChern (D := D.withObject E₃ p₃ h₃ r₃) d₃
      (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₃)]

end Fst

/-! ### Objects given by a mapping cone: the deformation to the direct sum -/

section MappingCone

variable (D : LocalizedChernData.{u}) {P₁ P₃ : CochainComplex D.X.Modules ℤ}
  (hP₁ : IsLocallyBoundedFiniteLocallyFree P₁) (hP₃ : IsLocallyBoundedFiniteLocallyFree P₃)
  (φ : P₃ ⟶ P₁) {E₁ E₂ E₃ : DerivedCategory D.X.Modules}
  (i₁ : DerivedCategory.Q.obj P₁ ≅ E₁)
  (i₂ : DerivedCategory.Q.obj (CochainComplex.mappingCone φ) ≅ E₂)
  (i₃ : DerivedCategory.Q.obj ((shiftFunctor (CochainComplex D.X.Modules ℤ) (1 : ℤ)).obj P₃) ≅ E₃)

include hP₁ hP₃ φ i₁ i₂ i₃ in
/-- **The components of degree `≥ r` of the identity of Stacks 0FBD, for a mapping cone, from the
direct sum.** Let `φ : P₃ ⟶ P₁` be a map of locally bounded complexes of finite locally free
`𝒪_X`-modules and let `E₁ ≅ P₁`, `E₂ ≅ C(φ)`, `E₃ ≅ P₃[1]`, with `E₁|_{X ∖ Z}`, `E₃|_{X ∖ Z}`
finite locally free of rank `< p₁`, `< p₃` in degree `0`, and `p₁ + p₃ ≤ r + 1`. If
`c⁽ʳ⁾(Z ⟶ X, E₁ ⊕ E₃) = c⁽ᵖ¹⁾(Z ⟶ X, E₁) c⁽ᵖ³⁾(Z ⟶ X, E₃)`, then in every degree `n ≥ r` the
component of `c⁽ʳ⁾(Z ⟶ X, E₂)` is that of the product: `c_n(Z ⟶ X, E₂) = c_n(Z ⟶ X, E₁ ⊕ E₃)`
by the deformation of `C(φ)` to `C(0) ≅ E₁ ⊕ E₃` over `𝐀¹_X`
(`Stacks.Chow.LocalizedChernData.localizedChern_mappingCone_eq`). -/
theorem totalLocalizedChern_snd_of_mappingCone {p₁ p₃ r : ℕ} (hr : p₁ + p₃ ≤ r + 1)
    (h₁ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₁)
    (h₂ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₂)
    (h₃ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₃)
    (h₀ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace)
      (E₁ ⊞ E₃ : DerivedCategory D.X.Modules))
    (r₁ : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₁ ∧
        Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj E₁ ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (r₂ : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M r ∧
        Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj E₂ ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (r₃ : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₃ ∧
        Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj E₃ ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (r₀ : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M r ∧
        Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj (E₁ ⊞ E₃ : DerivedCategory D.X.Modules) ≅
          (DerivedCategory.singleFunctor _ 0).obj M))
    (d₁ : HasDefinedChernClasses E₁) (d₂ : HasDefinedChernClasses E₂)
    (d₃ : HasDefinedChernClasses E₃)
    (d₀ : HasDefinedChernClasses (E₁ ⊞ E₃ : DerivedCategory D.X.Modules))
    (hsum : totalLocalizedChern (D := D.withObject (E₁ ⊞ E₃) r h₀ r₀) d₀
        (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₀) =
      localizedGradingCutoffMul D.base (D.i ≫ D.a) D.a D.i rfl r hr
        (totalLocalizedChern (D := D.withObject E₁ p₁ h₁ r₁) d₁
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₁))
        (totalLocalizedChern (D := D.withObject E₃ p₃ h₃ r₃) d₃
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₃)))
    (n : {n : ℤ // (r : ℤ) ≤ n}) :
    (totalLocalizedChern (D := D.withObject E₂ r h₂ r₂) d₂
        (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₂)).2 n =
      (localizedGradingCutoffMul D.base (D.i ≫ D.a) D.a D.i rfl r hr
        (totalLocalizedChern (D := D.withObject E₁ p₁ h₁ r₁) d₁
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₁))
        (totalLocalizedChern (D := D.withObject E₃ p₃ h₃ r₃) d₃
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₃))).2 n := by
  refine Eq.trans ?_ (congrArg (fun x => x.2 n) hsum)
  have hq : (D.withObject E₂ r h₂ r₂).p ≤ n.1.toNat := by
    have := n.2
    change r ≤ n.1.toNat
    omega
  obtain ⟨M₁, hM₁, ⟨e₁⟩⟩ := r₁
  obtain ⟨M₃, hM₃, ⟨e₃⟩⟩ := r₃
  let D₂ : LocalizedChernData.{u} := (D.withObject E₂ r h₂ r₂).ofLe hq
  have y₁ : ∃ M : OXMod.{u, u, u} (D₂.X.toRingedSpace.restrict (⟨(Set.range D₂.i.base)ᶜ,
      D₂.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D₂.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₁ ∧
        Nonempty ((derivedPullback (D₂.X.toRingedSpace.ofRestrict (⟨(Set.range D₂.i.base)ᶜ,
          D₂.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D₂.X.Opens).isOpenEmbedding)).obj (DerivedCategory.Q.obj P₁) ≅
              (DerivedCategory.singleFunctor _ 0).obj M) :=
    ⟨M₁, hM₁, ⟨(derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).mapIso
        i₁ ≪≫ e₁⟩⟩
  have y₃ : ∃ M : OXMod.{u, u, u} (D₂.X.toRingedSpace.restrict (⟨(Set.range D₂.i.base)ᶜ,
      D₂.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D₂.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₃ ∧
        Nonempty ((derivedPullback (D₂.X.toRingedSpace.ofRestrict (⟨(Set.range D₂.i.base)ᶜ,
          D₂.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D₂.X.Opens).isOpenEmbedding)).obj (DerivedCategory.Q.obj
              ((shiftFunctor (CochainComplex D₂.X.Modules ℤ) (1 : ℤ)).obj P₃)) ≅
              (DerivedCategory.singleFunctor _ 0).obj M) :=
    ⟨M₃, hM₃, ⟨(derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).mapIso
        i₃ ≪≫ e₃⟩⟩
  have hp : p₁ + p₃ ≤ D₂.p + 1 := by
    have := n.2
    change p₁ + p₃ ≤ n.1.toNat + 1
    omega
  let e₀ : (E₁ ⊞ E₃ : DerivedCategory D.X.Modules) ≅
      DerivedCategory.Q.obj (CochainComplex.mappingCone (C := D.X.Modules) (0 : P₃ ⟶ P₁)) :=
    biprod.mapIso i₁.symm i₃.symm ≪≫ (nonempty_mappingCone_zero_iso_biprod P₃ P₁).some.symm
  exact congrArg (bivariantClassDegreeCongr D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a)
    D.a D.i rfl (Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg r) n.2)))
    (localizedChern_mappingCone_eq (D := D₂) hP₁ hP₃ φ y₁ y₃ hp i₂.symm
      (E₁ ⊞ E₃ : DerivedCategory D.X.Modules) e₀ d₂ d₀)

include hP₁ hP₃ φ i₁ i₂ i₃ in
/-- **Stacks 0FBE for a mapping cone, from the direct sum.** Let `φ : P₃ ⟶ P₁` be a map of locally
bounded complexes of finite locally free `𝒪_X`-modules and let `E₁ ≅ P₁`, `E₂ ≅ C(φ)`,
`E₃ ≅ P₃[1]`, with `E₁|_{X ∖ Z}` and `E₃|_{X ∖ Z}` zero. If
`P_q(Z ⟶ X, E₁ ⊕ E₃) = P_q(Z ⟶ X, E₁) + P_q(Z ⟶ X, E₃)`, then
`P_q(Z ⟶ X, E₂) = P_q(Z ⟶ X, E₁) + P_q(Z ⟶ X, E₃)`: by the deformation of `C(φ)` to
`C(0) ≅ E₁ ⊕ E₃` over `𝐀¹_X` (`Stacks.Chow.LocalizedChernData.localizedPowerSum_mappingCone_eq`),
`P_q(Z ⟶ X, E₂) = P_q(Z ⟶ X, E₁ ⊕ E₃)`. -/
theorem localizedPowerSum_of_mappingCone
    (h₁ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₁)
    (h₂ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₂)
    (h₃ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₃)
    (h₀ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace)
      (E₁ ⊞ E₃ : DerivedCategory D.X.Modules))
    (z₁ : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E₁))
    (z₂ : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E₂))
    (z₃ : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E₃))
    (z₀ : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj
        (E₁ ⊞ E₃ : DerivedCategory D.X.Modules)))
    (d₁ : HasDefinedChernClasses E₁) (d₂ : HasDefinedChernClasses E₂)
    (d₃ : HasDefinedChernClasses E₃)
    (d₀ : HasDefinedChernClasses (E₁ ⊞ E₃ : DerivedCategory D.X.Modules)) (q : ℕ)
    (hsum : (D.withZeroObject (E₁ ⊞ E₃ : DerivedCategory D.X.Modules) h₀ z₀).localizedPowerSum
        d₀ z₀ q =
      (D.withZeroObject E₁ h₁ z₁).localizedPowerSum d₁ z₁ q +
        (D.withZeroObject E₃ h₃ z₃).localizedPowerSum d₃ z₃ q) :
    (D.withZeroObject E₂ h₂ z₂).localizedPowerSum d₂ z₂ q =
      (D.withZeroObject E₁ h₁ z₁).localizedPowerSum d₁ z₁ q +
        (D.withZeroObject E₃ h₃ z₃).localizedPowerSum d₃ z₃ q := by
  refine Eq.trans ?_ hsum
  let D₂ : LocalizedChernData.{u} := D.withZeroObject E₂ h₂ z₂
  have y₁ : IsZero ((derivedPullback (D₂.X.toRingedSpace.ofRestrict (⟨(Set.range D₂.i.base)ᶜ,
      D₂.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D₂.X.Opens).isOpenEmbedding)).obj
        (DerivedCategory.Q.obj P₁)) :=
    z₁.of_iso ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).mapIso i₁)
  have y₃ : IsZero ((derivedPullback (D₂.X.toRingedSpace.ofRestrict (⟨(Set.range D₂.i.base)ᶜ,
      D₂.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D₂.X.Opens).isOpenEmbedding)).obj
        (DerivedCategory.Q.obj ((shiftFunctor (CochainComplex D₂.X.Modules ℤ) (1 : ℤ)).obj P₃))) :=
    z₃.of_iso ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).mapIso i₃)
  let e₀ : (E₁ ⊞ E₃ : DerivedCategory D.X.Modules) ≅
      DerivedCategory.Q.obj (CochainComplex.mappingCone (C := D.X.Modules) (0 : P₃ ⟶ P₁)) :=
    biprod.mapIso i₁.symm i₃.symm ≪≫ (nonempty_mappingCone_zero_iso_biprod P₃ P₁).some.symm
  exact localizedPowerSum_mappingCone_eq (D := D₂) hP₁ hP₃ φ y₁ y₃ i₂.symm
    (E₁ ⊞ E₃ : DerivedCategory D.X.Modules) e₀ d₂ d₀ q

end MappingCone

/-- **`P_p(Z ⟶ X, E)` restricts along an envelope on which `E` is represented to
`P_p(Z ×_X Y ⟶ Y, Lg^*E)`**, the class of Remark 0GUK for the base change: the restriction is the
class of Stacks 0FB2 upstairs
(`Stacks.Chow.LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedPowerSum`),
which is the class of Remark 0GUK there
(`Stacks.Chow.LocalizedSituation.localizedPowerSum_toLocalizedChernData`). -/
theorem supportedRestriction_localizedPowerSum_of_isEnvelope (D : LocalizedChernData.{u})
    (hE : HasDefinedChernClasses D.E) {Y : Scheme.{u}} (g : Y ⟶ D.X) [LocallyOfFiniteType g]
    (hg : IsEnvelope g)
    (hc : ∃ P : CochainComplex (OXMod.{u, u, u} (D.pullback g).X.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ (D.pullback g).E))
    (h : D.IsZeroOnComplement) (p : ℕ) :
    supportedRestriction D.base (D.i ≫ D.a) D.a D.i rfl g (D.localizedPowerSum hE h p) =
      (D.pullback g).localizedPowerSum (hE.derivedPullback g) h.pullback p :=
  (bivariantClassCongrBase_bivariantRestriction_localizedPowerSum hE g hg hc h p).trans
    (LocalizedSituation.localizedPowerSum_toLocalizedChernData
      ((D.pullback g).toSituation hc) h.pullback p).symm

/-! ### The direct sum, from Stacks 0FE8 -/

section DirectSum

variable (D : LocalizedChernData.{u}) {E₁ E₃ : DerivedCategory D.X.Modules} {p₁ p₃ : ℕ}
  (h₁ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₁)
  (h₃ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₃)

/-- **The common-modification data of Stacks 0FE8 for a direct sum**: `Q = Lg₁^*Q₁ ⊕ Lg₃^*Q₃` is
perfect, satisfies the finiteness condition, and over `𝐀¹_X` is the pullback of `E₁ ⊕ E₃`. -/
private theorem perfect_finiteness_iso_biprod_graphObject
    (c₁ : ∃ P : CochainComplex D.X.Modules ℤ, IsLocallyBoundedFiniteLocallyFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ E₁))
    (c₃ : ∃ P : CochainComplex D.X.Modules ℤ, IsLocallyBoundedFiniteLocallyFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ E₃))
    {W : Scheme.{u}} (b : W ⟶ projectiveLineProduct D.a)
    (g₁ : W ⟶ graphBlowup D.a E₁ h₁) (hb₁ : g₁ ≫ graphBlowupToBase D.a E₁ h₁ = b)
    (g₃ : W ⟶ graphBlowup D.a E₃ h₃) (hb₃ : g₃ ≫ graphBlowupToBase D.a E₃ h₃ = b) :
    let Q₁ : DerivedCategory W.Modules := (derivedPullback g₁.toLRSHom.toShHom).obj
      (graphObject D.a E₁ h₁)
    let Q₃ : DerivedCategory W.Modules := (derivedPullback g₃.toLRSHom.toShHom).obj
      (graphObject D.a E₃ h₃)
    let Q : DerivedCategory W.Modules := Q₁ ⊞ Q₃
    Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) Q ∧
      LocalizedChernFiniteness D.base (modificationProjection D.a b ≫ D.a) Q ∧
      Nonempty ((derivedPullback
        (pullback.fst b (projectiveLineAffineChart D.a)).toLRSHom.toShHom).obj Q ≅
        (derivedPullback (pullback.fst b (projectiveLineAffineChart D.a) ≫
          modificationProjection D.a b).toLRSHom.toShHom).obj
            (E₁ ⊞ E₃ : DerivedCategory D.X.Modules)) := by
  intro Q₁ Q₃ Q
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_isLocallyBoundedFiniteLocallyFree_biprod_derivedPullback g₁ g₃
    (exists_isLocallyBoundedFiniteLocallyFree_graphObject D.a E₁ h₁ c₁)
    (exists_isLocallyBoundedFiniteLocallyFree_graphObject D.a E₃ h₃ c₃)
  exact ⟨isPerfect_of_iso_biprod (Iso.refl _)
      (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ _
        (isPerfect_graphObject D.base D.a E₁ h₁))
      (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ _
        (isPerfect_graphObject D.base D.a E₃ h₃)),
    Or.inr (Or.inr (Or.inl ⟨P, hP, ⟨eP.symm⟩⟩)),
    nonempty_derivedPullback_biprod_iso E₁ E₃ _ _ _ _
      (nonempty_derivedPullback_affineChart_derivedPullback_graphObject D.a E₁ h₁ g₁ hb₁)
      (nonempty_derivedPullback_affineChart_derivedPullback_graphObject D.a E₃ h₃ g₃ hb₃)⟩

/-- **Stacks 0FE8 for a direct sum on a common modification, for `c_n`.** Let `E₁`, `E₃` be
represented by locally bounded complexes of finite locally free `𝒪_X`-modules, with
`(E₁ ⊕ E₃)|_{X ∖ Z}` finite locally free of rank `< q` in degree `0`, let `b_j : W_j ⟶ 𝐏¹_X`, `Q_j`
be their graph constructions, let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X` with
`b = b_j ∘ g_j`, and let `T ⊆ W_∞` be closed, contain the points over `X ∖ Z`, and be such that
`Q = Lg₁^*Q₁ ⊕ Lg₃^*Q₃` restricts to a finite locally free module of rank `< q` in degree `0` on
`T`. Then `c_q(Z ⟶ X, E₁ ⊕ E₃) = c'_q(Q)`: `Q` is perfect, represented by a locally bounded
complex of finite locally free modules, and over `𝐀¹_X` it is the pullback of `E₁ ⊕ E₃`
(Stacks 0F90 (2), (5)), so Stacks 0FE8
(`Stacks.Chow.LocalizedSituation.modificationChernClass_eq_localizedChern`) applies. -/
theorem localizedChern_biprod_eq_modificationChernClass {q : ℕ}
    (hAB : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace)
      (E₁ ⊞ E₃ : DerivedCategory D.X.Modules))
    (sAB : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M q ∧
        Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj (E₁ ⊞ E₃ : DerivedCategory D.X.Modules) ≅
              (DerivedCategory.singleFunctor _ 0).obj M))
    (c₁ : ∃ P : CochainComplex D.X.Modules ℤ, IsLocallyBoundedFiniteLocallyFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ E₁))
    (c₃ : ∃ P : CochainComplex D.X.Modules ℤ, IsLocallyBoundedFiniteLocallyFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ E₃))
    (dAB : HasDefinedChernClasses (E₁ ⊞ E₃ : DerivedCategory D.X.Modules))
    {W : Scheme.{u}} (b : W ⟶ projectiveLineProduct D.a) [IsProper b]
    (hW : IsIso (pullback.snd b (projectiveLineAffineChart D.a)))
    (g₁ : W ⟶ graphBlowup D.a E₁ h₁) (hb₁ : g₁ ≫ graphBlowupToBase D.a E₁ h₁ = b)
    (g₃ : W ⟶ graphBlowup D.a E₃ h₃) (hb₃ : g₃ ≫ graphBlowupToBase D.a E₃ h₃ = b)
    {T : Scheme.{u}} (t : T ⟶ modificationFibreAtInfinity D.a b) [IsClosedImmersion t]
    (hT : ∀ w, modificationProjectionAtInfinity D.a b w ∉ Set.range D.i → w ∈ Set.range t)
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M q ∧
      Nonempty ((derivedPullback (t ≫ modificationInclusionAtInfinity D.a b).toLRSHom.toShHom).obj
        ((derivedPullback g₁.toLRSHom.toShHom).obj (graphObject D.a E₁ h₁) ⊞
          (derivedPullback g₃.toLRSHom.toShHom).obj (graphObject D.a E₃ h₃)) ≅
        (DerivedCategory.singleFunctor _ 0).obj M)) :
    (D.withObject (E₁ ⊞ E₃ : DerivedCategory D.X.Modules) q hAB sAB).localizedChern dAB
        (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject sAB) =
      modificationChernClass D.base D.a b hW D.i t
        (hasDefinedChernClasses_biprod
          (HasDefinedChernClasses.derivedPullback
            (hasDefinedChernClasses_graphObject_of_isLocallyBoundedFiniteLocallyFree D.base D.a
              E₁ h₁ c₁) g₁)
          (HasDefinedChernClasses.derivedPullback
            (hasDefinedChernClasses_graphObject_of_isLocallyBoundedFiniteLocallyFree D.base D.a
              E₃ h₃ c₃) g₃))
        q hT hrank := by
  let S : LocalizedSituation.{u} :=
    ⟨D.withObject (E₁ ⊞ E₃ : DerivedCategory D.X.Modules) q hAB sAB,
      D.finiteness_of_iso_biprod (Iso.refl _) (Or.inr (Or.inr ⟨c₁, c₃⟩))⟩
  have hS : S.IsFiniteLocallyFreeOfRankLTOnComplement := sAB
  obtain ⟨hQp, hfin, hF⟩ :=
    perfect_finiteness_iso_biprod_graphObject D h₁ h₃ c₁ c₃ b g₁ hb₁ g₃ hb₃
  exact (LocalizedSituation.localizedChern_toLocalizedChernData S hS).trans
    (S.modificationChernClass_eq_localizedChern b hW t hQp hfin hF hT hrank hS).symm

/-- **Stacks 0FE8 for a direct sum on a common modification, for `P_p`**: as
`Stacks.Chow.LocalizedChernData.localizedChern_biprod_eq_modificationChernClass`, for `E₁`, `E₃`
vanishing off `Z` and `T` on which `Q = Lg₁^*Q₁ ⊕ Lg₃^*Q₃` restricts to zero,
`P_p(Z ⟶ X, E₁ ⊕ E₃) = P'_p(Q)`
(`Stacks.Chow.LocalizedSituation.modificationPowerSum_eq_localizedPowerSum`). -/
theorem localizedPowerSum_biprod_eq_modificationPowerSum
    (hAB : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace)
      (E₁ ⊞ E₃ : DerivedCategory D.X.Modules))
    (zAB : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj
        (E₁ ⊞ E₃ : DerivedCategory D.X.Modules)))
    (c₁ : ∃ P : CochainComplex D.X.Modules ℤ, IsLocallyBoundedFiniteLocallyFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ E₁))
    (c₃ : ∃ P : CochainComplex D.X.Modules ℤ, IsLocallyBoundedFiniteLocallyFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ E₃))
    (dAB : HasDefinedChernClasses (E₁ ⊞ E₃ : DerivedCategory D.X.Modules)) (p : ℕ)
    {W : Scheme.{u}} (b : W ⟶ projectiveLineProduct D.a) [IsProper b]
    (hW : IsIso (pullback.snd b (projectiveLineAffineChart D.a)))
    (g₁ : W ⟶ graphBlowup D.a E₁ h₁) (hb₁ : g₁ ≫ graphBlowupToBase D.a E₁ h₁ = b)
    (g₃ : W ⟶ graphBlowup D.a E₃ h₃) (hb₃ : g₃ ≫ graphBlowupToBase D.a E₃ h₃ = b)
    {T : Scheme.{u}} (t : T ⟶ modificationFibreAtInfinity D.a b) [IsClosedImmersion t]
    (hT : ∀ w, modificationProjectionAtInfinity D.a b w ∉ Set.range D.i → w ∈ Set.range t)
    (hzero : IsZero ((derivedPullback
      (t ≫ modificationInclusionAtInfinity D.a b).toLRSHom.toShHom).obj
        ((derivedPullback g₁.toLRSHom.toShHom).obj (graphObject D.a E₁ h₁) ⊞
          (derivedPullback g₃.toLRSHom.toShHom).obj (graphObject D.a E₃ h₃)))) :
    (D.withZeroObject (E₁ ⊞ E₃ : DerivedCategory D.X.Modules) hAB zAB).localizedPowerSum dAB zAB
        p =
      modificationPowerSum D.base D.a b hW D.i t
        (hasDefinedChernClasses_biprod
          (HasDefinedChernClasses.derivedPullback
            (hasDefinedChernClasses_graphObject_of_isLocallyBoundedFiniteLocallyFree D.base D.a
              E₁ h₁ c₁) g₁)
          (HasDefinedChernClasses.derivedPullback
            (hasDefinedChernClasses_graphObject_of_isLocallyBoundedFiniteLocallyFree D.base D.a
              E₃ h₃ c₃) g₃))
        p hT hzero := by
  let S : LocalizedSituation.{u} :=
    ⟨D.withZeroObject (E₁ ⊞ E₃ : DerivedCategory D.X.Modules) hAB zAB,
      D.finiteness_of_iso_biprod (Iso.refl _) (Or.inr (Or.inr ⟨c₁, c₃⟩))⟩
  have hS : S.IsZeroOnComplement := zAB
  obtain ⟨hQp, hfin, hF⟩ :=
    perfect_finiteness_iso_biprod_graphObject D h₁ h₃ c₁ c₃ b g₁ hb₁ g₃ hb₃
  exact (LocalizedSituation.localizedPowerSum_toLocalizedChernData S hS p).trans
    (S.modificationPowerSum_eq_localizedPowerSum b hW t hQp hfin hF p hT hzero hS).symm

/-- **The direct-sum case of Stacks 0FBD, for objects represented by complexes.** Let `E₁`, `E₃`
be represented by locally bounded complexes of finite locally free `𝒪_X`-modules, with
`E₁|_{X ∖ Z}`, `E₃|_{X ∖ Z}` finite locally free of rank `< p₁`, `< p₃` in degree `0`, and let
`p₁ + p₃ ≤ r + 1`. Then `c⁽ʳ⁾(Z ⟶ X, E₁ ⊕ E₃) = c⁽ᵖ¹⁾(Z ⟶ X, E₁) c⁽ᵖ³⁾(Z ⟶ X, E₃)`. This is the
last paragraph of the proof of Stacks 0FBD, on the modification `W = W₁ ×_{𝐏¹_X} W₃` of the graph
constructions `b_j : W_j ⟶ 𝐏¹_X` of `E₁`, `E₃`
(`Stacks.Chow.LocalizedChernData.totalLocalizedChern_eq_cutoffMul_of_modification`), with
Stacks 0FE8 for `E₁ ⊕ E₃` and `Lg₁^*Q₁ ⊕ Lg₃^*Q₃` on `W`
(`Stacks.Chow.LocalizedChernData.localizedChern_biprod_eq_modificationChernClass`). -/
theorem totalLocalizedChern_biprod_eq_cutoffMul {r : ℕ} (hr : p₁ + p₃ ≤ r + 1)
    (hAB : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace)
      (E₁ ⊞ E₃ : DerivedCategory D.X.Modules))
    (r₁ : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₁ ∧
        Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj E₁ ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (r₃ : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₃ ∧
        Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj E₃ ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (rAB : ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M r ∧
        Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj (E₁ ⊞ E₃ : DerivedCategory D.X.Modules) ≅
              (DerivedCategory.singleFunctor _ 0).obj M))
    (c₁ : ∃ P : CochainComplex D.X.Modules ℤ, IsLocallyBoundedFiniteLocallyFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ E₁))
    (c₃ : ∃ P : CochainComplex D.X.Modules ℤ, IsLocallyBoundedFiniteLocallyFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ E₃))
    (d₁ : HasDefinedChernClasses E₁) (d₃ : HasDefinedChernClasses E₃)
    (dAB : HasDefinedChernClasses (E₁ ⊞ E₃ : DerivedCategory D.X.Modules)) :
    totalLocalizedChern (D := D.withObject (E₁ ⊞ E₃ : DerivedCategory D.X.Modules) r hAB rAB) dAB
        (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject rAB) =
      localizedGradingCutoffMul D.base (D.i ≫ D.a) D.a D.i rfl r hr
        (totalLocalizedChern (D := D.withObject E₁ p₁ h₁ r₁) d₁
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₁))
        (totalLocalizedChern (D := D.withObject E₃ p₃ h₃ r₃) d₃
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₃)) := by
  have := isProper_graphBlowupToBase D.a E₁ h₁
  have := isProper_graphBlowupToBase D.a E₃ h₃
  have hA := isIso_pullbackSnd_pullbackFst_comp_projectiveLineAffineChart D.a _ _
    (isIso_pullback_snd_graphBlowupToBase D.a E₁ h₁)
    (isIso_pullback_snd_graphBlowupToBase D.a E₃ h₃)
  exact D.totalLocalizedChern_eq_cutoffMul_of_modification h₁ h₃ r₁ r₃
    (Or.inr (Or.inr (Or.inl c₁))) (Or.inr (Or.inr (Or.inl c₃))) (Iso.refl _) hr hA
    (pullback.fst _ _) rfl (pullback.snd _ _) pullback.condition.symm
    (fun n hn {_} t _ hT hrank => D.localizedChern_biprod_eq_modificationChernClass h₁ h₃ hAB _ c₁
      c₃ dAB _ hA _ rfl _ pullback.condition.symm t hT hrank)

/-- **The direct-sum case of Stacks 0FBE, for objects represented by complexes.** Let `E₁`, `E₃`
be represented by locally bounded complexes of finite locally free `𝒪_X`-modules, with
`E₁|_{X ∖ Z}` and `E₃|_{X ∖ Z}` zero. Then
`P_p(Z ⟶ X, E₁ ⊕ E₃) = P_p(Z ⟶ X, E₁) + P_p(Z ⟶ X, E₃)`: the last paragraph of the proof of
Stacks 0FBD with Stacks 0FAZ, on `W = W₁ ×_{𝐏¹_X} W₃`
(`Stacks.Chow.LocalizedChernData.localizedPowerSum_eq_add_of_modification`), with Stacks 0FE8 on
`W` (`Stacks.Chow.LocalizedChernData.localizedPowerSum_biprod_eq_modificationPowerSum`). -/
theorem localizedPowerSum_biprod_eq_add
    (hAB : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace)
      (E₁ ⊞ E₃ : DerivedCategory D.X.Modules))
    (z₁ : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E₁))
    (z₃ : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E₃))
    (zAB : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj
        (E₁ ⊞ E₃ : DerivedCategory D.X.Modules)))
    (c₁ : ∃ P : CochainComplex D.X.Modules ℤ, IsLocallyBoundedFiniteLocallyFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ E₁))
    (c₃ : ∃ P : CochainComplex D.X.Modules ℤ, IsLocallyBoundedFiniteLocallyFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ E₃))
    (d₁ : HasDefinedChernClasses E₁) (d₃ : HasDefinedChernClasses E₃)
    (dAB : HasDefinedChernClasses (E₁ ⊞ E₃ : DerivedCategory D.X.Modules)) (p : ℕ) :
    (D.withZeroObject (E₁ ⊞ E₃ : DerivedCategory D.X.Modules) hAB zAB).localizedPowerSum dAB zAB p =
      (D.withZeroObject E₁ h₁ z₁).localizedPowerSum d₁ z₁ p +
        (D.withZeroObject E₃ h₃ z₃).localizedPowerSum d₃ z₃ p := by
  have := isProper_graphBlowupToBase D.a E₁ h₁
  have := isProper_graphBlowupToBase D.a E₃ h₃
  have hA := isIso_pullbackSnd_pullbackFst_comp_projectiveLineAffineChart D.a _ _
    (isIso_pullback_snd_graphBlowupToBase D.a E₁ h₁)
    (isIso_pullback_snd_graphBlowupToBase D.a E₃ h₃)
  exact D.localizedPowerSum_eq_add_of_modification (h₁ := h₁) (h₃ := h₃)
    (fin₁ := Or.inr (Or.inr (Or.inl c₁))) (fin₃ := Or.inr (Or.inr (Or.inl c₃))) (z₁ := z₁)
    (z₃ := z₃) (Iso.refl _) hA (pullback.fst _ _) rfl (pullback.snd _ _) pullback.condition.symm p
    (fun {_} t _ hT hzero => D.localizedPowerSum_biprod_eq_modificationPowerSum h₁ h₃ hAB zAB c₁ c₃
      dAB p _ hA _ rfl _ pullback.condition.symm t hT hzero)

end DirectSum

/-! ### Stacks 0FBD and Stacks 0FBE -/

section Reduction

variable (D : LocalizedChernData.{u}) {E₁ E₂ E₃ : DerivedCategory D.X.Modules} {p₁ p₃ : ℕ}
  (h₁ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₁)
  (h₂ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₂)
  (h₃ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₃)

/-- **Stacks 0FBD with output cutoff `r`.** Let `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` be a distinguished
triangle of perfect objects of `D(𝒪_X)` such that `E₃ ⟶ E₁[1]` satisfies one of the conditions
(a)–(d) of Stacks 0FBD, with `E₁|_{X ∖ Z}`, `E₃|_{X ∖ Z}` finite locally free of rank `< p₁`,
`< p₃` in degree `0`, and let `p₁ + p₃ ≤ r + 1`. Then

  `c⁽ʳ⁾(Z ⟶ X, E₂) = c⁽ᵖ¹⁾(Z ⟶ X, E₁) c⁽ᵖ³⁾(Z ⟶ X, E₃)`   in `A⁽ʳ⁾(Z ⟶ X)`,

with the multiplication of Stacks 0FA0 with output cutoff `r`
(`Stacks.Chow.localizedGradingCutoffMul`). The case `p₁ = p₃ = r = 1` is the multiplicativity in
the ring `A⁽¹⁾(Z ⟶ X)` used by Stacks 0FES.

As in the source: on an envelope `f : Y ⟶ X` with `Lf^*E₂ ≅ C(φ)`, `Lf^*E₁ ≅ P₁`,
`Lf^*E₃ ≅ P₃[1]` (`Stacks.Chow.exists_envelope_mappingCone_presentation`), the components of degree
`< r` are the Whitney formula of Stacks 0F9F, and those of degree `≥ r` are those of the class of
`C(0) ≅ Lf^*E₁ ⊕ Lf^*E₃` by the deformation of `C(φ)` to `C(0)`, which is the product by the
direct-sum case (`Stacks.Chow.LocalizedChernData.totalLocalizedChern_biprod_eq_cutoffMul`);
restriction along `f` is injective (Stacks 0GUC) and compatible with the classes (Stacks 0FB3) and
the products. -/
theorem totalLocalizedChern_triangle_eq_cutoffMul {r : ℕ} (hr : p₁ + p₃ ≤ r + 1)
    (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (c : E₃ ⟶ E₁⟦(1 : ℤ)⟧) (hT : Triangle.mk a b c ∈ distTriang _)
    (r₁ : (∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₁ ∧
        Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj E₁ ≅ (DerivedCategory.singleFunctor _ 0).obj M)))
    (r₃ : (∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₃ ∧
        Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj E₃ ≅ (DerivedCategory.singleFunctor _ 0).obj M)))
    (hc : HasTriangleChernCondition c) :
    totalLocalizedChern (D := D.withObject E₂ r h₂
        (D.exists_isFiniteLocallyFreeOfRankLT_restrict_obj₂ a b c hT hr r₁ r₃))
        (hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT hc).2.1
        (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject _) =
      localizedGradingCutoffMul D.base (D.i ≫ D.a) D.a D.i rfl r hr
        (totalLocalizedChern (D := D.withObject E₁ p₁ h₁ r₁)
          (hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT hc).1
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₁))
        (totalLocalizedChern (D := D.withObject E₃ p₃ h₃ r₃)
          (hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT hc).2.2
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₃)) := by
  obtain ⟨d₁, d₂, d₃⟩ := hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT hc
  obtain ⟨Y, f, hf, P₁, P₃, φ, i₁, i₂, hP₁, hP₃, w, ⟨i₃⟩⟩ :=
    exists_envelope_mappingCone_presentation a b c hT (hc.hasEnvelopeMapPresentation D.base D.a h₃
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift h₁ 1))
  have : IsProper f := hf.isProper
  have r₂ := D.exists_isFiniteLocallyFreeOfRankLT_restrict_obj₂ a b c hT hr r₁ r₃
  refine localizedGradingRestriction_injective_of_isEnvelope (C := D.base) (sZ := D.i ≫ D.a)
    (sX := D.a) (i := D.i) (hi := rfl) (f := f) hf ?_
  have e₂ := localizedGradingRestriction_totalLocalizedChern (D := D.withObject E₂ r h₂ r₂) d₂
    (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₂) f
  have em := localizedGradingRestriction_localizedGradingCutoffMul (C := D.base)
    (sZ := D.i ≫ D.a) (sX := D.a) (i := D.i) (hi := rfl) (f := f) hr
    (totalLocalizedChern (D := D.withObject E₁ p₁ h₁ r₁) d₁
      (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₁))
    (totalLocalizedChern (D := D.withObject E₃ p₃ h₃ r₃) d₃
      (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₃))
  rw [localizedGradingRestriction_totalLocalizedChern (D := D.withObject E₁ p₁ h₁ r₁) d₁
      (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₁) f,
    localizedGradingRestriction_totalLocalizedChern (D := D.withObject E₃ p₃ h₃ r₃) d₃
      (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₃) f] at em
  refine e₂.trans (Eq.trans ?_ em.symm)
  -- the identity on `Y`
  let D' := D.pullback f
  let F := schemeDerivedPullback f
  have hY₁ : Cohomology.PerfectComplexes.IsPerfect (X := D'.X.toRingedSpace) (F.obj E₁) :=
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ _ h₁
  have hY₂ : Cohomology.PerfectComplexes.IsPerfect (X := D'.X.toRingedSpace) (F.obj E₂) :=
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ _ h₂
  have hY₃ : Cohomology.PerfectComplexes.IsPerfect (X := D'.X.toRingedSpace) (F.obj E₃) :=
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ _ h₃
  have rY₁ : (∃ M : OXMod.{u, u, u} (D'.X.toRingedSpace.restrict (⟨(Set.range D'.i.base)ᶜ,
      D'.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D'.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₁ ∧
        Nonempty ((derivedPullback (D'.X.toRingedSpace.ofRestrict (⟨(Set.range D'.i.base)ᶜ,
          D'.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D'.X.Opens).isOpenEmbedding)).obj (F.obj E₁) ≅
              (DerivedCategory.singleFunctor _ 0).obj M)) :=
    IsFiniteLocallyFreeOfRankLTOnComplement.pullback (D := D.withObject E₁ p₁ h₁ r₁) (f := f)
      (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₁)
  have rY₂ : (∃ M : OXMod.{u, u, u} (D'.X.toRingedSpace.restrict (⟨(Set.range D'.i.base)ᶜ,
      D'.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D'.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M r ∧
        Nonempty ((derivedPullback (D'.X.toRingedSpace.ofRestrict (⟨(Set.range D'.i.base)ᶜ,
          D'.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D'.X.Opens).isOpenEmbedding)).obj (F.obj E₂) ≅
              (DerivedCategory.singleFunctor _ 0).obj M)) :=
    IsFiniteLocallyFreeOfRankLTOnComplement.pullback (D := D.withObject E₂ r h₂ r₂) (f := f)
      (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₂)
  have rY₃ : (∃ M : OXMod.{u, u, u} (D'.X.toRingedSpace.restrict (⟨(Set.range D'.i.base)ᶜ,
      D'.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D'.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₃ ∧
        Nonempty ((derivedPullback (D'.X.toRingedSpace.ofRestrict (⟨(Set.range D'.i.base)ᶜ,
          D'.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D'.X.Opens).isOpenEmbedding)).obj (F.obj E₃) ≅
              (DerivedCategory.singleFunctor _ 0).obj M)) :=
    IsFiniteLocallyFreeOfRankLTOnComplement.pullback (D := D.withObject E₃ p₃ h₃ r₃) (f := f)
      (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₃)
  have dY₁ : HasDefinedChernClasses (F.obj E₁) := d₁.derivedPullback f
  have dY₂ : HasDefinedChernClasses (F.obj E₂) := d₂.derivedPullback f
  have dY₃ : HasDefinedChernClasses (F.obj E₃) := d₃.derivedPullback f
  have hY₀ : Cohomology.PerfectComplexes.IsPerfect (X := D'.X.toRingedSpace)
      (F.obj E₁ ⊞ F.obj E₃ : DerivedCategory D'.X.Modules) :=
    isPerfect_of_iso_biprod (Iso.refl _) hY₁ hY₃
  have rY₀ : (∃ M : OXMod.{u, u, u} (D'.X.toRingedSpace.restrict (⟨(Set.range D'.i.base)ᶜ,
      D'.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D'.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M r ∧
        Nonempty ((derivedPullback (D'.X.toRingedSpace.ofRestrict (⟨(Set.range D'.i.base)ᶜ,
          D'.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D'.X.Opens).isOpenEmbedding)).obj
              (F.obj E₁ ⊞ F.obj E₃ : DerivedCategory D'.X.Modules) ≅
                (DerivedCategory.singleFunctor _ 0).obj M)) :=
    D'.exists_isFiniteLocallyFreeOfRankLT_restrict_of_iso_biprod (Iso.refl _) hr rY₁ rY₃
  have dY₀ : HasDefinedChernClasses (F.obj E₁ ⊞ F.obj E₃ : DerivedCategory D'.X.Modules) :=
    hasDefinedChernClasses_biprod (E := F.obj E₁) (F := F.obj E₃) dY₁ dY₃
  have hT' : Triangle.mk (F.map a) (F.map b) (F.map c ≫ (F.commShiftIso (1 : ℤ)).hom.app E₁) ∈
      distTriang _ := F.map_distinguished _ hT
  have ha' : HasTriangleChernCondition (F.map a) :=
    Or.inr (Or.inl ⟨P₁, _, CochainComplex.mappingCone.inr φ, i₁, i₂, hP₁,
      isLocallyBoundedFiniteLocallyFree_mappingCone φ hP₃ hP₁, w⟩)
  have cY₁ : ∃ P : CochainComplex D'.X.Modules ℤ, IsLocallyBoundedFiniteLocallyFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ F.obj E₁) := ⟨P₁, hP₁, ⟨i₁⟩⟩
  have cY₃ : ∃ P : CochainComplex D'.X.Modules ℤ, IsLocallyBoundedFiniteLocallyFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ F.obj E₃) :=
    ⟨_, isLocallyBoundedFiniteLocallyFree_shift hP₃ 1, ⟨i₃⟩⟩
  have hsum' := totalLocalizedChern_biprod_eq_cutoffMul D' hY₁ hY₃ hr hY₀ rY₁ rY₃
    rY₀ cY₁ cY₃ dY₁ dY₃ dY₀
  refine Prod.ext (funext fun n => ?_) (funext fun n => ?_)
  · exact totalLocalizedChern_triangle_cutoffMul_fst D' hY₁ hY₂ hY₃ rY₁ rY₂ rY₃ dY₁ dY₂ dY₃ hr
      (F.map a) (F.map b) _ hT' ha' n
  · exact totalLocalizedChern_snd_of_mappingCone D' hP₁ hP₃ φ i₁ i₂ i₃ hr hY₁ hY₂ hY₃ hY₀ rY₁ rY₂
      rY₃ rY₀ dY₁ dY₂ dY₃ dY₀ hsum' n

/-- **Stacks 0FBD.** Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type
over `S`, let `Z ⟶ X` be a closed immersion and let `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` be a distinguished
triangle of perfect objects of `D(𝒪_X)`. Assume (1) `E₁|_{X ∖ Z}` and `E₃|_{X ∖ Z}` are finite
locally free of rank `< p₁` and `< p₃` placed in degree `0`, and (2) one of: (a) `X` is
quasi-compact, (b) `X` has quasi-compact irreducible components, (c) `E₃ ⟶ E₁[1]` is represented
by a map of locally bounded complexes of finite locally free `𝒪_X`-modules, (d) the same holds for
`Lf^*E₃ ⟶ Lf^*E₁[1]` after an envelope `f : Y ⟶ X`. These are stated as the hypothesis `hc`,
in the source's order (a), (b), (c), (d). Then

  `c⁽ᵖ¹⁺ᵖ³⁾(Z ⟶ X, E₂) = c⁽ᵖ¹⁾(Z ⟶ X, E₁) c⁽ᵖ³⁾(Z ⟶ X, E₃)`   in `A⁽ᵖ¹⁺ᵖ³⁾(Z ⟶ X)`,

with the classes of Remark 0FBC (`Stacks.Chow.LocalizedChernData.totalLocalizedChern`) and the
multiplication of Remark 0FA0 (`Stacks.Chow.localizedGradingMul`). That the statement makes
sense, i.e. that `E₂|_{X ∖ Z}` is finite locally free of rank `< p₁ + p₃` in degree `0` and that
the Chern classes of `E₁`, `E₂`, `E₃` are defined, is
`Stacks.Chow.LocalizedChernData.exists_isFiniteLocallyFreeOfRankLT_restrict_obj₂` and
`Stacks.Chow.hasDefinedChernClasses_triangle_of_mor₃`. This is the output cutoff `r = p₁ + p₃` of
`Stacks.Chow.LocalizedChernData.totalLocalizedChern_triangle_eq_cutoffMul`. -/
@[stacks 0FBD]
theorem totalLocalizedChern_triangle
    (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (c : E₃ ⟶ E₁⟦(1 : ℤ)⟧) (hT : Triangle.mk a b c ∈ distTriang _)
    (r₁ : (∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₁ ∧
        Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj E₁ ≅ (DerivedCategory.singleFunctor _ 0).obj M)))
    (r₃ : (∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₃ ∧
        Nonempty ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
            D.X.Opens).isOpenEmbedding)).obj E₃ ≅ (DerivedCategory.singleFunctor _ 0).obj M)))
    (hc : CompactSpace D.X ∨ (∀ T ∈ irreducibleComponents D.X, IsCompact T) ∨
      HasMapPresentation c ∨ HasEnvelopeMapPresentation c) :
    totalLocalizedChern (D := D.withObject E₂ (p₁ + p₃) h₂
        (D.exists_isFiniteLocallyFreeOfRankLT_restrict_obj₂ a b c hT (by omega) r₁ r₃))
        (hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT
          (hasTriangleChernCondition_of_conditions hc)).2.1
        (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject _) =
      localizedGradingMul D.base (D.i ≫ D.a) D.a D.i rfl
        (totalLocalizedChern (D := D.withObject E₁ p₁ h₁ r₁)
          (hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT
            (hasTriangleChernCondition_of_conditions hc)).1
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₁))
        (totalLocalizedChern (D := D.withObject E₃ p₃ h₃ r₃)
          (hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT
            (hasTriangleChernCondition_of_conditions hc)).2.2
          (D.isFiniteLocallyFreeOfRankLTOnComplement_withObject r₃)) :=
  D.totalLocalizedChern_triangle_eq_cutoffMul h₁ h₂ h₃ (by omega) a b c hT r₁ r₃
    (hasTriangleChernCondition_of_conditions hc)

/-- **Stacks 0FBE, the power sums.** Let `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` be a distinguished triangle of
perfect objects of `D(𝒪_X)` such that `E₃ ⟶ E₁[1]` satisfies one of the conditions (a)–(d) of
Stacks 0FBD, with `E₁|_{X ∖ Z}` and `E₃|_{X ∖ Z}` zero. Then
`P_p(Z ⟶ X, E₂) = P_p(Z ⟶ X, E₁) + P_p(Z ⟶ X, E₃)`: on an envelope `f : Y ⟶ X` with
`Lf^*E₂ ≅ C(φ)`, `Lf^*E₁ ≅ P₁`, `Lf^*E₃ ≅ P₃[1]` the classes of `C(φ)` are those of
`C(0) ≅ Lf^*E₁ ⊕ Lf^*E₃`, which are the sums by the direct-sum case
(`Stacks.Chow.LocalizedChernData.localizedPowerSum_biprod_eq_add`), and restriction along `f` is
injective (Stacks 0GUC), additive, and compatible with the classes (Stacks 0FB3). -/
theorem localizedPowerSum_triangle
    (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (c : E₃ ⟶ E₁⟦(1 : ℤ)⟧) (hT : Triangle.mk a b c ∈ distTriang _)
    (z₁ : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E₁))
    (z₃ : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E₃))
    (hc : HasTriangleChernCondition c) (p : ℕ) :
    (D.withZeroObject E₂ h₂ (D.isZero_restrict_obj₂ a b c hT z₁ z₃)).localizedPowerSum
        (hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT hc).2.1
        (D.isZero_restrict_obj₂ a b c hT z₁ z₃) p =
      (D.withZeroObject E₁ h₁ z₁).localizedPowerSum
          (hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT hc).1 z₁ p +
        (D.withZeroObject E₃ h₃ z₃).localizedPowerSum
          (hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT hc).2.2 z₃ p := by
  obtain ⟨d₁, d₂, d₃⟩ := hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT hc
  obtain ⟨Y, f, hf, P₁, P₃, φ, i₁, i₂, hP₁, hP₃, -, ⟨i₃⟩⟩ :=
    exists_envelope_mappingCone_presentation a b c hT (hc.hasEnvelopeMapPresentation D.base D.a h₃
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift h₁ 1))
  have : IsProper f := hf.isProper
  have z₂ := D.isZero_restrict_obj₂ a b c hT z₁ z₃
  refine supportedRestriction_injective_of_isEnvelope (C := D.base) (sZ := D.i ≫ D.a)
    (sX := D.a) (i := D.i) (hi := rfl) (f := f) hf ?_
  have c₁ : ∃ P : CochainComplex (OXMod.{u, u, u} Y.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ (derivedPullback f.toLRSHom.toShHom).obj E₁) :=
    ⟨P₁, hP₁, ⟨i₁⟩⟩
  have c₂ : ∃ P : CochainComplex (OXMod.{u, u, u} Y.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ (derivedPullback f.toLRSHom.toShHom).obj E₂) :=
    ⟨_, isLocallyBoundedFiniteLocallyFree_mappingCone φ hP₃ hP₁, ⟨i₂⟩⟩
  have c₃ : ∃ P : CochainComplex (OXMod.{u, u, u} Y.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ (derivedPullback f.toLRSHom.toShHom).obj E₃) :=
    ⟨_, isLocallyBoundedFiniteLocallyFree_shift hP₃ 1, ⟨i₃⟩⟩
  have k₁ := supportedRestriction_localizedPowerSum_of_isEnvelope (D.withZeroObject E₁ h₁ z₁) d₁ f
    hf c₁ z₁ p
  have k₂ := supportedRestriction_localizedPowerSum_of_isEnvelope (D.withZeroObject E₂ h₂ z₂) d₂ f
    hf c₂ z₂ p
  have k₃ := supportedRestriction_localizedPowerSum_of_isEnvelope (D.withZeroObject E₃ h₃ z₃) d₃ f
    hf c₃ z₃ p
  rw [supportedRestriction_add D.base (D.i ≫ D.a) D.a D.i rfl f]
  refine k₂.trans (Eq.trans ?_ (congrArg₂ (· + ·) k₁ k₃).symm)
  -- the identity on `Y`
  let D' := D.pullback f
  let F := schemeDerivedPullback f
  have hY₁ : Cohomology.PerfectComplexes.IsPerfect (X := D'.X.toRingedSpace) (F.obj E₁) :=
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ _ h₁
  have hY₂ : Cohomology.PerfectComplexes.IsPerfect (X := D'.X.toRingedSpace) (F.obj E₂) :=
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ _ h₂
  have hY₃ : Cohomology.PerfectComplexes.IsPerfect (X := D'.X.toRingedSpace) (F.obj E₃) :=
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ _ h₃
  have zY₁ : IsZero ((derivedPullback (D'.X.toRingedSpace.ofRestrict (⟨(Set.range D'.i.base)ᶜ,
      D'.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D'.X.Opens).isOpenEmbedding)).obj
        (F.obj E₁)) :=
    IsZeroOnComplement.pullback (D := D.withZeroObject E₁ h₁ z₁) (f := f) z₁
  have zY₂ : IsZero ((derivedPullback (D'.X.toRingedSpace.ofRestrict (⟨(Set.range D'.i.base)ᶜ,
      D'.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D'.X.Opens).isOpenEmbedding)).obj
        (F.obj E₂)) :=
    IsZeroOnComplement.pullback (D := D.withZeroObject E₂ h₂ z₂) (f := f) z₂
  have zY₃ : IsZero ((derivedPullback (D'.X.toRingedSpace.ofRestrict (⟨(Set.range D'.i.base)ᶜ,
      D'.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D'.X.Opens).isOpenEmbedding)).obj
        (F.obj E₃)) :=
    IsZeroOnComplement.pullback (D := D.withZeroObject E₃ h₃ z₃) (f := f) z₃
  have dY₁ : HasDefinedChernClasses (F.obj E₁) := d₁.derivedPullback f
  have dY₂ : HasDefinedChernClasses (F.obj E₂) := d₂.derivedPullback f
  have dY₃ : HasDefinedChernClasses (F.obj E₃) := d₃.derivedPullback f
  have hY₀ : Cohomology.PerfectComplexes.IsPerfect (X := D'.X.toRingedSpace)
      (F.obj E₁ ⊞ F.obj E₃ : DerivedCategory D'.X.Modules) :=
    isPerfect_of_iso_biprod (Iso.refl _) hY₁ hY₃
  have zY₀ : IsZero ((derivedPullback (D'.X.toRingedSpace.ofRestrict (⟨(Set.range D'.i.base)ᶜ,
      D'.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D'.X.Opens).isOpenEmbedding)).obj
        (F.obj E₁ ⊞ F.obj E₃ : DerivedCategory D'.X.Modules)) :=
    D'.isZero_restrict_of_iso_biprod (Iso.refl _) zY₁ zY₃
  have dY₀ : HasDefinedChernClasses (F.obj E₁ ⊞ F.obj E₃ : DerivedCategory D'.X.Modules) :=
    hasDefinedChernClasses_biprod (E := F.obj E₁) (F := F.obj E₃) dY₁ dY₃
  have cY₁ : ∃ P : CochainComplex D'.X.Modules ℤ, IsLocallyBoundedFiniteLocallyFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ F.obj E₁) := ⟨P₁, hP₁, ⟨i₁⟩⟩
  have cY₃ : ∃ P : CochainComplex D'.X.Modules ℤ, IsLocallyBoundedFiniteLocallyFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ F.obj E₃) :=
    ⟨_, isLocallyBoundedFiniteLocallyFree_shift hP₃ 1, ⟨i₃⟩⟩
  have hsum' := localizedPowerSum_biprod_eq_add D' hY₁ hY₃ hY₀ zY₁ zY₃ zY₀ cY₁ cY₃
    dY₁ dY₃ dY₀ p
  exact localizedPowerSum_of_mappingCone D' hP₁ hP₃ φ i₁ i₂ i₃ hY₁ hY₂ hY₃ hY₀ zY₁ zY₂ zY₃ zY₀ dY₁
    dY₂ dY₃ dY₀ p hsum'

/-- **Stacks 0FBE, the Chern character**: under the hypotheses of
`Stacks.Chow.LocalizedChernData.localizedPowerSum_triangle`,
`ch_p(Z ⟶ X, E₂) = ch_p(Z ⟶ X, E₁) + ch_p(Z ⟶ X, E₃)` for every `p`, since `ch_p = P_p / p!`. -/
theorem localizedChernChar_triangle
    (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (c : E₃ ⟶ E₁⟦(1 : ℤ)⟧) (hT : Triangle.mk a b c ∈ distTriang _)
    (z₁ : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E₁))
    (z₃ : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E₃))
    (hc : HasTriangleChernCondition c) (p : ℕ) :
    (D.withZeroObject E₂ h₂ (D.isZero_restrict_obj₂ a b c hT z₁ z₃)).localizedChernChar
        (hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT hc).2.1
        (D.isZero_restrict_obj₂ a b c hT z₁ z₃) p =
      (D.withZeroObject E₁ h₁ z₁).localizedChernChar
          (hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT hc).1 z₁ p +
        (D.withZeroObject E₃ h₃ z₃).localizedChernChar
          (hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT hc).2.2 z₃ p := by
  unfold localizedChernChar
  rw [localizedPowerSum_triangle D h₁ h₂ h₃ a b c hT z₁ z₃ hc p,
    TensorProduct.tmul_add]

/-- **Stacks 0FBE.** Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type
over `S`, let `Z ⟶ X` be a closed immersion and let `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` be a distinguished
triangle of perfect objects of `D(𝒪_X)`. Assume (1) `E₁|_{X ∖ Z}` and `E₃|_{X ∖ Z}` are zero,
and (2) one of the conditions (a)–(d) of Stacks 0FBD on `E₃ ⟶ E₁[1]`, stated as the hypothesis `hc`
in the source's order: (a) `X` is quasi-compact, (b) `X` has quasi-compact irreducible components,
(c) `E₃ ⟶ E₁[1]` is represented by a map of locally bounded complexes of finite locally free
`𝒪_X`-modules, (d) the same holds for `Lf^*E₃ ⟶ Lf^*E₁[1]` after an envelope `f : Y ⟶ X`. Then

  `P_p(Z ⟶ X, E₂) = P_p(Z ⟶ X, E₁) + P_p(Z ⟶ X, E₃)`   for all `p`,

and consequently `ch(Z ⟶ X, E₂) = ch(Z ⟶ X, E₁) + ch(Z ⟶ X, E₃)`, in every degree `p`, for the
classes of Remark 0GUK (`Stacks.Chow.LocalizedChernData.localizedPowerSum`,
`Stacks.Chow.LocalizedChernData.localizedChernChar`). The case `p = 0` is included.

The localized classes `P_p(Z ⟶ X, E)` are defined for `p ≥ 0` (Definition 0FB5); the source's
`p ∈ 𝐙` ranges over those. -/
@[stacks 0FBE]
theorem localizedPowerSum_localizedChernChar_triangle
    (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (c : E₃ ⟶ E₁⟦(1 : ℤ)⟧) (hT : Triangle.mk a b c ∈ distTriang _)
    (z₁ : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E₁))
    (z₃ : IsZero ((derivedPullback (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E₃))
    (hc : CompactSpace D.X ∨ (∀ T ∈ irreducibleComponents D.X, IsCompact T) ∨
      HasMapPresentation c ∨ HasEnvelopeMapPresentation c) :
    (∀ p : ℕ,
      (D.withZeroObject E₂ h₂ (D.isZero_restrict_obj₂ a b c hT z₁ z₃)).localizedPowerSum
          (hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT
            (hasTriangleChernCondition_of_conditions hc)).2.1
          (D.isZero_restrict_obj₂ a b c hT z₁ z₃) p =
        (D.withZeroObject E₁ h₁ z₁).localizedPowerSum
            (hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT
              (hasTriangleChernCondition_of_conditions hc)).1 z₁ p +
          (D.withZeroObject E₃ h₃ z₃).localizedPowerSum
            (hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT
              (hasTriangleChernCondition_of_conditions hc)).2.2 z₃ p) ∧
      ∀ p : ℕ,
        (D.withZeroObject E₂ h₂ (D.isZero_restrict_obj₂ a b c hT z₁ z₃)).localizedChernChar
            (hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT
              (hasTriangleChernCondition_of_conditions hc)).2.1
            (D.isZero_restrict_obj₂ a b c hT z₁ z₃) p =
          (D.withZeroObject E₁ h₁ z₁).localizedChernChar
              (hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT
                (hasTriangleChernCondition_of_conditions hc)).1 z₁ p +
            (D.withZeroObject E₃ h₃ z₃).localizedChernChar
              (hasDefinedChernClasses_triangle_of_mor₃ D.base D.a h₁ h₂ h₃ hT
                (hasTriangleChernCondition_of_conditions hc)).2.2 z₃ p :=
  ⟨fun p => localizedPowerSum_triangle D h₁ h₂ h₃ a b c hT z₁ z₃
    (hasTriangleChernCondition_of_conditions hc) p,
    fun p => localizedChernChar_triangle D h₁ h₂ h₃ a b c hT z₁ z₃
      (hasTriangleChernCondition_of_conditions hc) p⟩

end Reduction

end LocalizedChernData

end Stacks.Chow

end
