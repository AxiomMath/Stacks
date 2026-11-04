module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeAdmissible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeComparison

/-!
# Functoriality of the shift and of the cone, and the naturality of the connecting morphism

Let `R` be a sheaf of rings on a site and let `(A, d)` be a sheaf of differential graded
`R`-algebras. A morphism of right differential graded `A`-modules induces a morphism of their
chosen degree-one shifts, and a commutative square

```
K₁ --f₁--> L₁
|          |
α          β
v          v
K₂ --f₂--> L₂
```

induces a morphism of the cones of `f₁` and `f₂`. This file constructs both, records that the
cone morphism is compatible with the cone's inclusion, with the cone's projection and with the
comparison `q` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedConeComparison.lean`, and deduces
from these the **naturality of the connecting morphism `δ = - p ∘ q⁻¹`** in the short exact
sequence — the second of the two conditions in the definition of a `δ`-functor,
[Stacks, Tag 0150].

## Main definitions

* `SheafOfModules.DifferentialGradedModule.ShiftPackage.map`: the morphism of chosen shifts
  induced by a morphism of right differential graded modules;
  `SheafOfModules.DifferentialGradedModule.coneShiftHom` is the case of the chosen shift packages.
* `SheafOfModules.DifferentialGradedModule.ConePackage.map`: the morphism of cones induced by a
  commutative square; `SheafOfModules.DifferentialGradedModule.coneHom` is the case of the chosen
  cone packages, and `SheafOfModules.DifferentialGradedModule.shortComplexConeHom` is the case of
  a morphism of short complexes.

## Main results

* `SheafOfModules.DifferentialGradedModule.ConePackage.inclusion_map`: the cone morphism extends
  the morphism of the middle terms along the cones' inclusions.
* `SheafOfModules.DifferentialGradedModule.ConePackage.map_projection`: the cone morphism is
  compatible with the cones' projections and the induced morphism of the chosen shifts.
* `SheafOfModules.DifferentialGradedModule.shortComplexConeHom_coneDescHom`: the cone morphism of
  a morphism of short complexes is compatible with the comparisons `q`.
* `SheafOfModules.DifferentialGradedModule.shortExactδ_naturality`: **the connecting morphism of
  a short exact sequence is natural in the short exact sequence.**

## Implementation notes

*Where the morphisms come from.* On the underlying complexes both morphisms are the obvious ones:
the degree-one shift of a morphism of cochain complexes, and Mathlib's
`CochainComplex.mappingCone.map`. The content is that they commute with the right action of the
algebra, which is read off the two coordinates of the degreewise splitting of the cone: in the
second coordinate the cone acts as its middle term does (`ConePackage.action_second`), and in the
first it acts as the shifted source does (`ConePackage.action_first`, together with
`ShiftPackage.xIso_mul`). The first coordinate is the one where the two degrees `(n + 1) + i` and
`(n + i) + 1` differ, so its equations run through the transport `SheafOfModules.castHom`, as the
module laws themselves do.

*Why the connecting morphism is natural without a triangulated structure.* The naturality square
is an identity between morphisms of `D(A, d)` obtained by inverting the comparisons `q`, and
inverting them needs only that they are quasi-isomorphisms — which is
`SheafOfModules.DifferentialGradedModule.quasiIso_coneDescHom`. No translation functor on
`D(A, d)` enters: as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedConeComparison.lean`, the target
of `δ` is spelled as the image of the differential graded shift rather than as a translate, and
the right-hand vertical arrow of the square is accordingly the image of `coneShiftHom` rather than
a translate of a morphism.

## References

* [Stacks Project, Tag 0FTB](https://stacks.math.columbia.edu/tag/0FTB)
* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
* [Stacks Project, Tag 0150](https://stacks.math.columbia.edu/tag/0150)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}

/-! ### Evaluation on sections and transports along equalities of degrees -/

/-- Evaluating a composite of morphisms of sheaves of modules on a section over `U` evaluates the
two morphisms in turn. -/
theorem comp_val_app' {X Y Z : SheafOfModules.{m} R} (φ : X ⟶ Y) (ψ : Y ⟶ Z) (U : Cᵒᵖ)
    (z : X.val.obj U) : (φ ≫ ψ).val.app U z = ψ.val.app U (φ.val.app U z) := rfl

/-- Equal morphisms of sheaves of modules agree on every section. -/
alias congr_val_app' := congr_val_app

/-- A section heterogeneously equal to a section in another degree is the transport of that
section along the equality of degrees. -/
alias eq_castHom_of_heq' := eq_castHom_of_heq

/-- A degreewise family of morphisms of sheaves of modules commutes with the transport of
sections along an equality of degrees. -/
theorem castHom_comm {X Y : ℤ → SheafOfModules.{m} R} (ψ : ∀ k : ℤ, X k ⟶ Y k)
    {i j : ℤ} (h : i = j) (U : Cᵒᵖ) (x : (X i).val.obj U) :
    (ψ j).val.app U (castHom X h U x) = castHom Y h U ((ψ i).val.app U x) := by
  subst h
  rfl

/-! ### Functoriality of the chosen shift -/

namespace ShiftPackage

variable {K K' : DifferentialGradedModule.{t, a, m} A}

/-- Sections of a piece of a chosen shift are determined by their image under the degreewise
identification with the shifted complex. -/
theorem xIso_app_injective (S : ShiftPackage K) (n : ℤ) (U : Cᵒᵖ)
    {x y : (S.shifted.complex.X n).val.obj U}
    (h : ((S.xIso n).hom).val.app U x = ((S.xIso n).hom).val.app U y) : x = y := by
  calc x = ((S.xIso n).inv).val.app U (((S.xIso n).hom).val.app U x) :=
        (congr_val_app' (S.xIso n).hom_inv_id U x).symm
    _ = ((S.xIso n).inv).val.app U (((S.xIso n).hom).val.app U y) := by rw [h]
    _ = y := congr_val_app' (S.xIso n).hom_inv_id U y

/-- The underlying morphism of complexes of the morphism of chosen shifts: the degree-one shift
of the underlying morphism of complexes, read through the identifications of the two chosen
shifts with the shifted complexes. -/
def mapComplex (S : ShiftPackage K) (S' : ShiftPackage K') (φ : K ⟶ K') :
    S.shifted.complex ⟶ S'.shifted.complex :=
  eqToHom S.shifted_complex ≫
    (CochainComplex.shiftFunctor (SheafOfModules.{m} R) (1 : ℤ)).map φ.toHomologicalComplex ≫
    eqToHom S'.shifted_complex.symm

/-- In each degree, the underlying morphism of complexes of the morphism of chosen shifts,
followed by the identification of the target shift, is the identification of the source shift
followed by the morphism of complexes in degree `n + 1`. -/
theorem mapComplex_f_xIso (S : ShiftPackage K) (S' : ShiftPackage K') (φ : K ⟶ K')
    (n : ℤ) :
    (mapComplex S S' φ).f n ≫ (S'.xIso n).hom =
      (S.xIso n).hom ≫ φ.toHomologicalComplex.f (n + 1) := by
  show ((S.xIso n).hom ≫ φ.toHomologicalComplex.f (n + 1) ≫ (S'.xIso n).inv) ≫
    (S'.xIso n).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The morphism of chosen shifts induced by a morphism of right differential graded
modules.** On the underlying complexes it is the degree-one shift of the underlying morphism; it
commutes with the right action because a chosen shift acts as the module it shifts does
(`ShiftPackage.xIso_mul`). -/
def map (S : ShiftPackage K) (S' : ShiftPackage K') (φ : K ⟶ K') : S.shifted ⟶ S'.shifted where
  toHomologicalComplex := mapComplex S S' φ
  map_mul n i U x y := by
    refine S'.xIso_app_injective (n + i) U ?_
    have hkey : ∀ (k : ℤ) (z : (S.shifted.complex.X k).val.obj U),
        ((S'.xIso k).hom).val.app U (((mapComplex S S' φ).f k).val.app U z) =
          (φ.toHomologicalComplex.f (k + 1)).val.app U (((S.xIso k).hom).val.app U z) :=
      fun k z => congr_val_app' (mapComplex_f_xIso S S' φ k) U z
    rw [hkey (n + i), S.xIso_mul n i U x y,
      castHom_comm (fun k : ℤ => φ.toHomologicalComplex.f k) (add_right_comm n 1 i) U,
      φ.map_mul (n + 1) i U _ y, S'.xIso_mul n i U _ y, hkey n]

/-- The degreewise formula for the morphism of chosen shifts: in degree `n` it is the morphism of
complexes in degree `n + 1`, read through the identifications of the two chosen shifts. -/
theorem map_f (S : ShiftPackage K) (S' : ShiftPackage K') (φ : K ⟶ K') (n : ℤ) :
    (S.map S' φ).toHomologicalComplex.f n =
      (S.xIso n).hom ≫ φ.toHomologicalComplex.f (n + 1) ≫ (S'.xIso n).inv :=
  rfl

/-- In each degree, the morphism of chosen shifts followed by the identification of the target
shift is the identification of the source shift followed by the morphism of complexes in degree
`n + 1`. -/
theorem map_f_xIso (S : ShiftPackage K) (S' : ShiftPackage K') (φ : K ⟶ K') (n : ℤ) :
    (S.map S' φ).toHomologicalComplex.f n ≫ (S'.xIso n).hom =
      (S.xIso n).hom ≫ φ.toHomologicalComplex.f (n + 1) :=
  mapComplex_f_xIso S S' φ n

end ShiftPackage

/-- The morphism of the chosen degree-one shifts induced by a morphism of right differential
graded modules. -/
abbrev coneShiftHom {K K' : DifferentialGradedModule.{t, a, m} A} (φ : K ⟶ K') :
    shift K ⟶ shift K' :=
  (shiftPackage K).map (shiftPackage K') φ

/-! ### The morphism of mapping cones induced by a commutative square -/

section MappingConeMap

variable {K₁ L₁ K₂ L₂ : CochainComplex (SheafOfModules.{m} R) ℤ}

/-- The morphism of mapping cones induced by a commutative square restricts, along the inclusions
of the shifted sources, to the morphism of the sources in degree `n + 1`. -/
theorem coneInlX_mappingCone_map (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (α : K₁ ⟶ K₂) (β : L₁ ⟶ L₂)
    (comm : φ₁ ≫ β = α ≫ φ₂) (n : ℤ) :
    coneInlX φ₁ n ≫ (CochainComplex.mappingCone.map φ₁ φ₂ α β comm).f n =
      α.f (n + 1) ≫ coneInlX φ₂ n := by
  have h : (CochainComplex.mappingCone.inl φ₁).v (n + 1) n (by omega) ≫
        (CochainComplex.mappingCone.map φ₁ φ₂ α β comm).f n =
      α.f (n + 1) ≫ (CochainComplex.mappingCone.inl φ₂).v (n + 1) n (by omega) := by
    simp [CochainComplex.mappingCone.map,
      CochainComplex.HomComplex.Cochain.comp_v _ _ (by omega : (0 : ℤ) + (-1) = -1)
        (n + 1) (n + 1) n (by omega) (by omega)]
  exact h

/-- The morphism of mapping cones induced by a commutative square restricts, along the inclusions
of the targets, to the morphism of the targets. -/
theorem coneInrX_mappingCone_map (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (α : K₁ ⟶ K₂) (β : L₁ ⟶ L₂)
    (comm : φ₁ ≫ β = α ≫ φ₂) (n : ℤ) :
    coneInrX φ₁ n ≫ (CochainComplex.mappingCone.map φ₁ φ₂ α β comm).f n =
      β.f n ≫ coneInrX φ₂ n := by
  have h : (CochainComplex.mappingCone.inr φ₁).f n ≫
        (CochainComplex.mappingCone.map φ₁ φ₂ α β comm).f n =
      (β ≫ CochainComplex.mappingCone.inr φ₂).f n := by
    simp [CochainComplex.mappingCone.map]
  exact h

/-- Read through the degreewise splittings, the morphism of mapping cones induced by a
commutative square is the direct sum of the shifted morphism of the sources and the morphism of
the targets. -/
theorem coneSplit_inv_mappingCone_map (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (α : K₁ ⟶ K₂) (β : L₁ ⟶ L₂)
    (comm : φ₁ ≫ β = α ≫ φ₂) (n : ℤ) :
    (coneSplit φ₁ n).inv ≫ (CochainComplex.mappingCone.map φ₁ φ₂ α β comm).f n =
      biprod.map (α.f (n + 1)) (β.f n) ≫ (coneSplit φ₂ n).inv := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, biprod_inl_coneSplit_inv, coneInlX_mappingCone_map,
      biprod.inl_map_assoc, biprod_inl_coneSplit_inv]
  · rw [← Category.assoc, biprod_inr_coneSplit_inv, coneInrX_mappingCone_map,
      biprod.inr_map_assoc, biprod_inr_coneSplit_inv]

end MappingConeMap

/-! ### Functoriality of the cone -/

namespace ConePackage

variable {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{t, a, m} A} {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}

/-- The underlying morphism of complexes of the morphism of cones: Mathlib's
`CochainComplex.mappingCone.map`, with its declared type spelled as the cone packages spell it. -/
def mapComplex (P₁ : ConePackage f₁) (P₂ : ConePackage f₂) (α : K₁ ⟶ K₂) (β : L₁ ⟶ L₂)
    (comm : f₁ ≫ β = α ≫ f₂) : P₁.cone.complex ⟶ P₂.cone.complex :=
  eqToHom P₁.cone_complex ≫
    CochainComplex.mappingCone.map f₁.toHomologicalComplex f₂.toHomologicalComplex
      α.toHomologicalComplex β.toHomologicalComplex (congrArg Hom.toHomologicalComplex comm) ≫
    eqToHom P₂.cone_complex.symm

/-- The degreewise formula for the underlying morphism of complexes of the morphism of cones: read
through the degreewise splittings it is the direct sum of the shifted morphism of the sources and
the morphism of the targets. -/
theorem mapComplex_f (P₁ : ConePackage f₁) (P₂ : ConePackage f₂) (α : K₁ ⟶ K₂)
    (β : L₁ ⟶ L₂) (comm : f₁ ≫ β = α ≫ f₂) (n : ℤ) :
    (mapComplex P₁ P₂ α β comm).f n =
      (P₁.componentIso n).hom ≫
        biprod.map (α.toHomologicalComplex.f (n + 1)) (β.toHomologicalComplex.f n) ≫
        (P₂.componentIso n).inv := by
  show (eqToHom P₁.cone_complex ≫
      CochainComplex.mappingCone.map f₁.toHomologicalComplex f₂.toHomologicalComplex
        α.toHomologicalComplex β.toHomologicalComplex (congrArg Hom.toHomologicalComplex comm) ≫
      eqToHom P₂.cone_complex.symm).f n = _
  obtain ⟨⟨cplx₁, mul₁, ha₁, ho₁, hl₁⟩, incl₁, proj₁, hc₁, iso₁, hiso₁, af₁, as₁, hi₁, hp₁⟩ := P₁
  obtain ⟨⟨cplx₂, mul₂, ha₂, ho₂, hl₂⟩, incl₂, proj₂, hc₂, iso₂, hiso₂, af₂, as₂, hi₂, hp₂⟩ := P₂
  dsimp only at hc₁ hc₂ hiso₁ hiso₂ ⊢
  subst hc₁
  subst hc₂
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id,
    show iso₁ n = coneSplit f₁.toHomologicalComplex n from eq_of_heq (hiso₁ n),
    show iso₂ n = coneSplit f₂.toHomologicalComplex n from eq_of_heq (hiso₂ n),
    ← Iso.inv_comp_eq]
  exact coneSplit_inv_mappingCone_map _ _ _ _ _ n

/-- **The morphism of cones induced by a commutative square.** On the underlying complexes it is
Mathlib's `CochainComplex.mappingCone.map`; it commutes with the right action because, read
through the degreewise splittings, it is the direct sum of the shifted morphism of the sources
and the morphism of the targets, and the cone acts coordinatewise. -/
def map (P₁ : ConePackage f₁) (P₂ : ConePackage f₂) (α : K₁ ⟶ K₂) (β : L₁ ⟶ L₂)
    (comm : f₁ ≫ β = α ≫ f₂) : P₁.cone ⟶ P₂.cone where
  toHomologicalComplex := mapComplex P₁ P₂ α β comm
  map_mul n i U x y := by
    have hA : ∀ (k : ℤ) (z : (P₁.cone.complex.X k).val.obj U),
        ((P₂.componentIso k).hom ≫ biprod.fst).val.app U
            (((mapComplex P₁ P₂ α β comm).f k).val.app U z) =
          (α.toHomologicalComplex.f (k + 1)).val.app U
            (((P₁.componentIso k).hom ≫ biprod.fst).val.app U z) := by
      intro k z
      have h : (mapComplex P₁ P₂ α β comm).f k ≫ (P₂.componentIso k).hom ≫ biprod.fst =
          ((P₁.componentIso k).hom ≫ biprod.fst) ≫ α.toHomologicalComplex.f (k + 1) := by
        rw [mapComplex_f]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, biprod.map_fst]
      exact congr_val_app' h U z
    have hB : ∀ (k : ℤ) (z : (P₁.cone.complex.X k).val.obj U),
        ((P₂.componentIso k).hom ≫ biprod.snd).val.app U
            (((mapComplex P₁ P₂ α β comm).f k).val.app U z) =
          (β.toHomologicalComplex.f k).val.app U
            (((P₁.componentIso k).hom ≫ biprod.snd).val.app U z) := by
      intro k z
      have h : (mapComplex P₁ P₂ α β comm).f k ≫ (P₂.componentIso k).hom ≫ biprod.snd =
          ((P₁.componentIso k).hom ≫ biprod.snd) ≫ β.toHomologicalComplex.f k := by
        rw [mapComplex_f]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, biprod.map_snd]
      exact congr_val_app' h U z
    refine P₂.sections_ext (n + i) U ?_ ?_
    · rw [hA (n + i),
        eq_castHom_of_heq' (X := K₁.complex.X) (add_right_comm n 1 i) U
          (P₁.action_first n i U x y),
        castHom_comm (fun k : ℤ => α.toHomologicalComplex.f k) (add_right_comm n 1 i) U,
        α.map_mul (n + 1) i U _ y,
        eq_castHom_of_heq' (X := K₂.complex.X) (add_right_comm n 1 i) U
          (P₂.action_first n i U (((mapComplex P₁ P₂ α β comm).f n).val.app U x) y),
        hA n]
    · rw [hB (n + i), P₁.action_second n i U x y, β.map_mul n i U _ y,
        P₂.action_second n i U (((mapComplex P₁ P₂ α β comm).f n).val.app U x) y, hB n]

/-- The degreewise formula for the morphism of cones: read through the degreewise splittings it
is the direct sum of the shifted morphism of the sources and the morphism of the targets. -/
theorem map_f (P₁ : ConePackage f₁) (P₂ : ConePackage f₂) (α : K₁ ⟶ K₂) (β : L₁ ⟶ L₂)
    (comm : f₁ ≫ β = α ≫ f₂) (n : ℤ) :
    (P₁.map P₂ α β comm).toHomologicalComplex.f n =
      (P₁.componentIso n).hom ≫
        biprod.map (α.toHomologicalComplex.f (n + 1)) (β.toHomologicalComplex.f n) ≫
        (P₂.componentIso n).inv :=
  mapComplex_f P₁ P₂ α β comm n

/-- **The morphism of cones extends the morphism of the middle terms along the cones'
inclusions.** -/
theorem inclusion_map (P₁ : ConePackage f₁) (P₂ : ConePackage f₂) (α : K₁ ⟶ K₂) (β : L₁ ⟶ L₂)
    (comm : f₁ ≫ β = α ≫ f₂) :
    P₁.inclusion ≫ P₁.map P₂ α β comm = β ≫ P₂.inclusion :=
  Hom.ext fun n => by
    show P₁.inclusion.toHomologicalComplex.f n ≫ (P₁.map P₂ α β comm).toHomologicalComplex.f n =
      β.toHomologicalComplex.f n ≫ P₂.inclusion.toHomologicalComplex.f n
    rw [P₁.inclusion_f n, P₂.inclusion_f n, map_f, Category.assoc, Iso.inv_hom_id_assoc,
      ← Category.assoc, biprod.inr_map, Category.assoc]

/-- **The morphism of cones is compatible with the cones' projections** and the morphism of the
chosen shifts induced by the morphism of the sources. -/
theorem map_projection (P₁ : ConePackage f₁) (P₂ : ConePackage f₂) (α : K₁ ⟶ K₂) (β : L₁ ⟶ L₂)
    (comm : f₁ ≫ β = α ≫ f₂) :
    P₁.map P₂ α β comm ≫ P₂.projection = P₁.projection ≫ coneShiftHom α :=
  Hom.ext fun n => by
    show (P₁.map P₂ α β comm).toHomologicalComplex.f n ≫ P₂.projection.toHomologicalComplex.f n =
      P₁.projection.toHomologicalComplex.f n ≫ (coneShiftHom α).toHomologicalComplex.f n
    rw [← cancel_mono (((shiftPackage K₂).xIso n).hom), Category.assoc, Category.assoc,
      P₂.projection_f n, ShiftPackage.map_f_xIso, map_f,
      ← Category.assoc (P₁.projection.toHomologicalComplex.f n), P₁.projection_f n]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, biprod.map_fst]

end ConePackage

/-- The morphism of the chosen cones induced by a commutative square. -/
abbrev coneHom {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{t, a, m} A} (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
    (α : K₁ ⟶ K₂) (β : L₁ ⟶ L₂) (comm : f₁ ≫ β = α ≫ f₂) :
    (conePackage f₁).cone ⟶ (conePackage f₂).cone :=
  (conePackage f₁).map (conePackage f₂) α β comm

/-- The morphism of the chosen cones of the first maps of two short complexes induced by a
morphism of short complexes. -/
abbrev shortComplexConeHom {S₁ S₂ : ShortComplex (DifferentialGradedModule.{t, a, m} A)}
    (φ : S₁ ⟶ S₂) : (conePackage S₁.f).cone ⟶ (conePackage S₂.f).cone :=
  coneHom S₁.f S₂.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm

/-! ### Compatibility with the comparison, and the naturality of the connecting morphism -/

section Comparison

variable [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- The degreewise formula for the comparison `q`: read through the degreewise splitting of the
cone it is the second projection followed by the second map of the short complex. -/
theorem coneDescHom_f (S : ShortComplex (DifferentialGradedModule.{t, a, m} A)) (n : ℤ) :
    (coneDescHom S).toHomologicalComplex.f n =
      ((conePackage S.f).componentIso n).hom ≫ biprod.snd ≫ S.g.toHomologicalComplex.f n :=
  conePackage_coneDesc_f S (conePackage S.f) n

/-- **The morphism of cones is compatible with the comparisons `q`**: this is the naturality of
the comparison of the cone with the third term, at the level of right differential graded
modules. -/
theorem shortComplexConeHom_coneDescHom
    {S₁ S₂ : ShortComplex (DifferentialGradedModule.{t, a, m} A)} (φ : S₁ ⟶ S₂) :
    shortComplexConeHom φ ≫ coneDescHom S₂ = coneDescHom S₁ ≫ φ.τ₃ :=
  Hom.ext fun n => by
    show (shortComplexConeHom φ).toHomologicalComplex.f n ≫
        (coneDescHom S₂).toHomologicalComplex.f n =
      (coneDescHom S₁).toHomologicalComplex.f n ≫ φ.τ₃.toHomologicalComplex.f n
    have hcomm : S₁.g.toHomologicalComplex.f n ≫ φ.τ₃.toHomologicalComplex.f n =
        φ.τ₂.toHomologicalComplex.f n ≫ S₂.g.toHomologicalComplex.f n :=
      congrArg (fun ψ : S₁.X₂ ⟶ S₂.X₃ => ψ.toHomologicalComplex.f n) φ.comm₂₃.symm
    rw [coneDescHom_f, coneDescHom_f, ConePackage.map_f]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, biprod.map_snd_assoc]
    rw [hcomm]

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The morphism of cones is compatible with the cones' projections, with the sign the
connecting morphism carries. -/
theorem shortComplexConeHom_neg_projection
    {S₁ S₂ : ShortComplex (DifferentialGradedModule.{t, a, m} A)} (φ : S₁ ⟶ S₂) :
    shortComplexConeHom φ ≫ (-(conePackage S₂.f).projection) =
      (-(conePackage S₁.f).projection) ≫ coneShiftHom φ.τ₁ := by
  rw [Preadditive.comp_neg, Preadditive.neg_comp, ConePackage.map_projection]

/-- **The naturality of the connecting morphism.** For a morphism `φ` of short exact
sequences of right differential graded `A`-modules, the square formed by the connecting
morphisms `δ = - p ∘ q⁻¹` of the two sequences, the image of `φ.τ₃` and the image of the induced
morphism of the chosen degree-one shifts of the first terms commutes. This is the second of the
two conditions in the definition of a `δ`-functor, [Stacks, Tag 0150].

Because `D(A, d)` carries no translation functor in this development — see the implementation
notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedConeComparison.lean` — the
right-hand vertical arrow is the image of the differential graded shift
`SheafOfModules.DifferentialGradedModule.coneShiftHom` of `φ.τ₁` rather than a translate of the
image of `φ.τ₁`. -/
@[stacks 0FTB "the naturality of the connecting morphism δ in the short exact sequence"]
theorem shortExactδ_naturality {S₁ S₂ : ShortComplex (DifferentialGradedModule.{t, a, m} A)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) :
    shortExactδ h₁ ≫ (moduleToDerivedCategory A).map (coneShiftHom φ.τ₁) =
      (moduleToDerivedCategory A).map φ.τ₃ ≫ shortExactδ h₂ := by
  have := isIso_moduleToDerivedCategory_map_coneDescHom h₁
  have := isIso_moduleToDerivedCategory_map_coneDescHom h₂
  have hp : (moduleToDerivedCategory A).map (shortComplexConeHom φ) ≫
        (moduleToDerivedCategory A).map (-(conePackage S₂.f).projection) =
      (moduleToDerivedCategory A).map (-(conePackage S₁.f).projection) ≫
        (moduleToDerivedCategory A).map (coneShiftHom φ.τ₁) := by
    rw [← Functor.map_comp, ← Functor.map_comp, shortComplexConeHom_neg_projection]
  have hinv : inv ((moduleToDerivedCategory A).map (coneDescHom S₁)) ≫
        (moduleToDerivedCategory A).map (shortComplexConeHom φ) =
      (moduleToDerivedCategory A).map φ.τ₃ ≫
        inv ((moduleToDerivedCategory A).map (coneDescHom S₂)) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, ← Functor.map_comp,
      ← Functor.map_comp, shortComplexConeHom_coneDescHom]
  show (inv ((moduleToDerivedCategory A).map (coneDescHom S₁)) ≫
      (moduleToDerivedCategory A).map (-(conePackage S₁.f).projection)) ≫
        (moduleToDerivedCategory A).map (coneShiftHom φ.τ₁) =
    (moduleToDerivedCategory A).map φ.τ₃ ≫
      inv ((moduleToDerivedCategory A).map (coneDescHom S₂)) ≫
        (moduleToDerivedCategory A).map (-(conePackage S₂.f).projection)
  rw [Category.assoc, ← hp, ← Category.assoc, hinv, Category.assoc]

end Comparison

end SheafOfModules.DifferentialGradedModule

end
