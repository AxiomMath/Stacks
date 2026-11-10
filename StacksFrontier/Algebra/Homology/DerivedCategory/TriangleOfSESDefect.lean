module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-!
# Connecting morphisms under a map of short exact sequences with a Leibniz defect

Let `S : 0 ⟶ S₁ ⟶ S₂ ⟶ S₃ ⟶ 0` and `T : 0 ⟶ T₁ ⟶ T₂ ⟶ T₃ ⟶ 0` be short exact sequences of
cochain complexes in an abelian category. The connecting morphism `δ : S₃ ⟶ S₁[1]` of the
distinguished triangle of `S` in the derived category is natural for morphisms of short
exact sequences (`DerivedCategory.triangleOfSESδ_naturality`). This file proves the version in
which the middle map is not a morphism of complexes: it is a degree-zero cochain
`φ₂ : S₂ ⟶ T₂` compatible with the two outer morphisms of complexes `φ₁` and `φ₃`, whose failure
to commute with the differentials factors as `δ φ₂ = S.g ∘ h ∘ T.f` through a degree-one cocycle
`h : S₃ ⟶ T₁`. Then

`φ₃ ≫ δ_T = δ_S ≫ φ₁[1] + h`

in the derived category.

This is the shape in which the Leibniz rule of the first differential of the spectral sequence
of a filtered complex is proved: multiplication by a form `ω` acts on the graded pieces of the
filtration of a de Rham complex by morphisms of complexes, but on two consecutive steps only by a
cochain, whose defect is multiplication by `dω`. That is the input to the Katz–Oda description
of the Gauss–Manin connection in [Stacks, Tag 0FMN].

## Main results

* `DerivedCategory.map_triangleOfSESδ_of_defect`: the formula above.
* `DerivedCategory.TriangleOfSESDefect.coneMap`: the morphism of mapping cones
  `cone(S.f) ⟶ cone(T.f)` it is proved with, together with its compatibility with the projections
  onto the third terms (`coneMap_descShortComplex`) and with the third morphisms of the mapping
  cone triangles up to `h` (`coneMap_triangle_mor₃`).

## Implementation notes

The morphism of mapping cones is `CochainComplex.mappingCone.lift` with components
`fst ∘ φ₁ - snd ∘ S.g ∘ h` and `snd ∘ φ₂`; the correction `- snd ∘ S.g ∘ h` is exactly what makes
the lifting condition hold when `φ₂` is not a morphism of complexes, and it is also what produces
the term `h` in the formula. The connecting morphism of a short exact sequence is
`inv (descShortComplex) ≫ mor₃` by definition, so the formula follows by cancelling the
quasi-isomorphism `descShortComplex S`.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)

-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated Preadditive CochainComplex HomComplex

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {S T : ShortComplex (CochainComplex C ℤ)}
  (φ₁ : S.X₁ ⟶ T.X₁) (φ₂ : Cochain S.X₂ T.X₂ 0) (φ₃ : S.X₃ ⟶ T.X₃) (h : Cocycle S.X₃ T.X₁ 1)

namespace TriangleOfSESDefect

/-- The first component `fst ∘ φ₁ - snd ∘ S.g ∘ h` of the comparison of mapping cones, a
degree-one cocycle `cone(S.f) ⟶ T₁`. -/
noncomputable def coneFst : Cocycle (mappingCone S.f) T.X₁ 1 :=
  Cocycle.mk ((mappingCone.fst S.f).1.comp (Cochain.ofHom φ₁) (add_zero 1) -
      (mappingCone.snd S.f).comp ((Cochain.ofHom S.g).comp h.1 (zero_add 1)) (zero_add 1))
    2 (by norm_num) (by
      rw [δ_sub, δ_comp_ofHom, Cocycle.δ_eq_zero, Cochain.zero_comp,
        δ_comp (mappingCone.snd S.f) _ (zero_add 1) 1 2 2 (by norm_num) (zero_add 1)
          (by norm_num), δ_ofHom_comp, Cocycle.δ_eq_zero, Cochain.comp_zero,
        mappingCone.δ_snd, Cochain.neg_comp,
        Cochain.comp_assoc _ _ _ (add_zero 1) (zero_add 1) (by norm_num),
        ← Cochain.comp_assoc (Cochain.ofHom S.f) _ _ (zero_add 0) (zero_add 1) (by norm_num),
        ← Cochain.ofHom_comp, S.zero, Cochain.ofHom_zero, Cochain.zero_comp, Cochain.comp_zero]
      simp)

variable {φ₁ φ₂ h}

omit [HasDerivedCategory C] in
/-- The lifting condition for the comparison of mapping cones. -/
theorem coneFst_eq
    (h₁₂ : (Cochain.ofHom S.f).comp φ₂ (zero_add 0) = Cochain.ofHom (φ₁ ≫ T.f))
    (hδ : δ 0 1 φ₂ =
      (Cochain.ofHom S.g).comp (h.1.comp (Cochain.ofHom T.f) (add_zero 1)) (zero_add 1)) :
    δ 0 1 ((mappingCone.snd S.f).comp φ₂ (zero_add 0)) +
      (coneFst φ₁ h).1.comp (Cochain.ofHom T.f) (add_zero 1) = 0 := by
  rw [δ_comp (mappingCone.snd S.f) φ₂ (zero_add 0) 1 1 1 (zero_add 1) (zero_add 1) (zero_add 1),
    hδ, mappingCone.δ_snd]
  simp only [coneFst, Cocycle.mk_coe, Int.negOnePow_zero, one_smul, Cochain.neg_comp,
    Cochain.sub_comp]
  rw [Cochain.comp_assoc _ _ _ (add_zero 1) (zero_add 0) (by norm_num), h₁₂,
    Cochain.comp_assoc _ (Cochain.ofHom φ₁) _ (add_zero 1) (zero_add 0) (by norm_num),
    ← Cochain.ofHom_comp,
    Cochain.comp_assoc (mappingCone.snd S.f) _ _ (zero_add 1) (add_zero 1) (by norm_num),
    Cochain.comp_assoc (Cochain.ofHom S.g) h.1 _ (zero_add 1) (add_zero 1) (by norm_num)]
  abel

/-- **The comparison of mapping cones** `cone(S.f) ⟶ cone(T.f)` attached to a map of short exact
sequences with a Leibniz defect. -/
noncomputable def coneMap
    (h₁₂ : (Cochain.ofHom S.f).comp φ₂ (zero_add 0) = Cochain.ofHom (φ₁ ≫ T.f))
    (hδ : δ 0 1 φ₂ =
      (Cochain.ofHom S.g).comp (h.1.comp (Cochain.ofHom T.f) (add_zero 1)) (zero_add 1)) :
    mappingCone S.f ⟶ mappingCone T.f :=
  mappingCone.lift T.f (coneFst φ₁ h) ((mappingCone.snd S.f).comp φ₂ (zero_add 0))
    (coneFst_eq h₁₂ hδ)

omit [HasDerivedCategory C] in
/-- The comparison of mapping cones commutes with the projections onto the third terms. -/
theorem coneMap_descShortComplex
    (h₁₂ : (Cochain.ofHom S.f).comp φ₂ (zero_add 0) = Cochain.ofHom (φ₁ ≫ T.f))
    (h₂₃ : φ₂.comp (Cochain.ofHom T.g) (zero_add 0) = Cochain.ofHom (S.g ≫ φ₃))
    (hδ : δ 0 1 φ₂ =
      (Cochain.ofHom S.g).comp (h.1.comp (Cochain.ofHom T.f) (add_zero 1)) (zero_add 1)) :
    coneMap h₁₂ hδ ≫ mappingCone.descShortComplex T =
      mappingCone.descShortComplex S ≫ φ₃ := by
  refine Cochain.ofHom_injective ?_
  rw [Cochain.ofHom_comp, Cochain.ofHom_comp]
  simp only [coneMap, mappingCone.descShortComplex, mappingCone.ofHom_lift,
    mappingCone.ofHom_desc, mappingCone.liftCochain_descCochain, Cochain.comp_zero, zero_add]
  rw [Cochain.comp_assoc _ _ _ (zero_add 0) (zero_add 0) (zero_add 0), h₂₃, Cochain.ofHom_comp]
  simp only [mappingCone.descCochain, Cochain.comp_zero, zero_add]
  rw [Cochain.comp_assoc _ _ _ (zero_add 0) (zero_add 0) (zero_add 0)]

omit [HasDerivedCategory C] in
/-- The comparison of mapping cones commutes with the third morphisms of the mapping cone
triangles up to the defect `h`. -/
theorem coneMap_triangle_mor₃
    (h₁₂ : (Cochain.ofHom S.f).comp φ₂ (zero_add 0) = Cochain.ofHom (φ₁ ≫ T.f))
    (hδ : δ 0 1 φ₂ =
      (Cochain.ofHom S.g).comp (h.1.comp (Cochain.ofHom T.f) (add_zero 1)) (zero_add 1)) :
    coneMap h₁₂ hδ ≫ Cocycle.equivHomShift.symm (-mappingCone.fst T.f) =
      Cocycle.equivHomShift.symm (-mappingCone.fst S.f) ≫ φ₁⟦(1 : ℤ)⟧' +
        mappingCone.descShortComplex S ≫ Cocycle.equivHomShift.symm h := by
  rw [← Cocycle.equivHomShift_symm_precomp, ← Cocycle.equivHomShift_symm_postcomp,
    ← Cocycle.equivHomShift_symm_precomp, ← map_add]
  congr 1
  refine Cocycle.ext ?_
  change (Cochain.ofHom (coneMap h₁₂ hδ)).comp (-(mappingCone.fst T.f).1) (zero_add 1) =
    (-(mappingCone.fst S.f).1).comp (Cochain.ofHom φ₁) (add_zero 1) +
      (Cochain.ofHom (mappingCone.descShortComplex S)).comp h.1 (zero_add 1)
  rw [Cochain.comp_neg, Cochain.neg_comp]
  simp only [coneMap, mappingCone.ofHom_lift, mappingCone.liftCochain_fst, coneFst,
    Cocycle.mk_coe, mappingCone.descShortComplex, mappingCone.ofHom_desc,
    mappingCone.descCochain, Cochain.comp_zero, zero_add]
  rw [Cochain.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (by norm_num)]
  abel

end TriangleOfSESDefect

open TriangleOfSESDefect in
/-- **The connecting morphism under a map of short exact sequences with a Leibniz defect.**
Let `S` and `T` be short exact sequences of cochain complexes, `φ₁ : S.X₁ ⟶ T.X₁` and
`φ₃ : S.X₃ ⟶ T.X₃` morphisms of complexes and `φ₂` a degree-zero cochain `S.X₂ ⟶ T.X₂`
compatible with `S.f, T.f` and with `S.g, T.g`, which fails to be a morphism of complexes by
`δ φ₂ = S.g ∘ h ∘ T.f` for a degree-one cocycle `h : S.X₃ ⟶ T.X₁`. Then in the derived category

`φ₃ ≫ δ_T = δ_S ≫ φ₁[1] + h`.

For `h = 0` this is the naturality of the connecting morphism. -/
theorem map_triangleOfSESδ_of_defect (hS : S.ShortExact) (hT : T.ShortExact)
    (h₁₂ : (Cochain.ofHom S.f).comp φ₂ (zero_add 0) = Cochain.ofHom (φ₁ ≫ T.f))
    (h₂₃ : φ₂.comp (Cochain.ofHom T.g) (zero_add 0) = Cochain.ofHom (S.g ≫ φ₃))
    (hδ : δ 0 1 φ₂ =
      (Cochain.ofHom S.g).comp (h.1.comp (Cochain.ofHom T.f) (add_zero 1)) (zero_add 1)) :
    Q.map φ₃ ≫ triangleOfSESδ hT =
      triangleOfSESδ hS ≫ (Q.map φ₁)⟦(1 : ℤ)⟧' +
        (Q.map (Cocycle.equivHomShift.symm h) ≫ (Q.commShiftIso (1 : ℤ)).hom.app T.X₁ :
          Q.obj S.X₃ ⟶ (Q.obj T.X₁)⟦(1 : ℤ)⟧) := by
  have := mappingCone.quasiIso_descShortComplex hS
  have := mappingCone.quasiIso_descShortComplex hT
  have key := coneMap_triangle_mor₃ h₁₂ hδ
  have key₂ := coneMap_descShortComplex φ₃ h₁₂ h₂₃ hδ
  have d {R : ShortComplex (CochainComplex C ℤ)} (hR : R.ShortExact) :
      Q.map (mappingCone.descShortComplex R) ≫ triangleOfSESδ hR =
        Q.map (Cocycle.equivHomShift.symm (-mappingCone.fst R.f)) ≫
          (Q.commShiftIso (1 : ℤ)).hom.app R.X₁ :=
    descShortComplex_triangleOfSESδ hR
  have k₁ : Q.map (mappingCone.descShortComplex S) ≫ Q.map φ₃ ≫ triangleOfSESδ hT =
      Q.map (coneMap h₁₂ hδ) ≫ Q.map (Cocycle.equivHomShift.symm (-mappingCone.fst T.f)) ≫
        (Q.commShiftIso (1 : ℤ)).hom.app T.X₁ := by
    rw [← Functor.map_comp_assoc, ← key₂, Functor.map_comp, assoc, d hT]
  have k₂ : Q.map (coneMap h₁₂ hδ) ≫ Q.map (Cocycle.equivHomShift.symm (-mappingCone.fst T.f)) =
      Q.map (Cocycle.equivHomShift.symm (-mappingCone.fst S.f)) ≫ Q.map (φ₁⟦(1 : ℤ)⟧') +
        Q.map (mappingCone.descShortComplex S) ≫ Q.map (Cocycle.equivHomShift.symm h) :=
    (Q.map_comp _ _).symm.trans ((congrArg Q.map key).trans
      ((Q.map_add).trans (congrArg₂ (· + ·) (Q.map_comp _ _) (Q.map_comp _ _))))
  have k₃ : Q.map (φ₁⟦(1 : ℤ)⟧') ≫ (Q.commShiftIso (1 : ℤ)).hom.app T.X₁ =
      (Q.commShiftIso (1 : ℤ)).hom.app S.X₁ ≫ (Q.map φ₁)⟦(1 : ℤ)⟧' :=
    (Q.commShiftIso (1 : ℤ)).hom.naturality φ₁
  rw [← cancel_epi (Q.map (mappingCone.descShortComplex S)), k₁, ← assoc, k₂, add_comp, assoc,
    assoc, k₃, comp_add, reassoc_of% (d hS)]

end DerivedCategory
