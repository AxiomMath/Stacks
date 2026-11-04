module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedBiprodShiftAffine

/-!
# The two-open step of [Stacks, Tag 09IM], as pure category theory

In the two-open case of [Stacks, Tag 09IM] the scheme is covered by a quasi-compact open `U`, over
which a perfect object `A` supported on `T` and a map `a : A ⟶ E|_U` are given, and an affine open
`V`. The affine case of the lemma at `V`, applied to `A|_{U ⊓ V}`, produces an object `B` over `V`
with a map `β : B ⟶ E|_V` and an isomorphism `B|_{U ⊓ V} ≅ A|_{U ⊓ V} ⊕ (A|_{U ⊓ V})[1]`, through
which `β` restricted to the overlap is the projection followed by `a` restricted to the overlap;
[Stacks, Tag 08DG] then glues `A ⊕ A[1]` over `U` to `B` over `V`.

This file states and proves that step for four categories, four functors between them, a
comparison `ω` of the two routes to the overlap, and the affine case and the glueing as
hypotheses. The classes of good objects over the four categories are four unrelated predicates
`GC`, `GU`, `GV` and `GW`.

## Main results

* `Stacks.LiftingProblem.biprodShiftIsoOfObjIso_hom_fst`: the comparison
  `H(G ⊕ G[1]) ≅ Z ⊕ Z[1]` attached to an isomorphism `HG ≅ Z`, for an additive, shift-commuting
  `H`, carries the projection to the image of the projection.
* `Stacks.LiftingProblem.exists_biprod_iso_hom_of_affine_overlap`: the two-open step. From the
  affine case over `V` and the glueing of [Stacks, Tag 08DG], a lift over the whole space whose
  restriction to `U` is `A ⊕ A[1]` and whose map to `E` is, in those coordinates, the projection
  followed by `a`.
* `Stacks.LiftingProblem.exists_biprod_iso_hom_of_equivalence`: the splitting statement of the
  affine case transports along an equivalence of the categories over the overlap.

## References

* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
open Stacks.Perfect.SupportedBiprodShift (biprodShiftIsoOfFunctorIso)
open Stacks.Perfect.SupportedBiprodShiftAffine (biprodShiftIsoOfObjIso)

namespace Stacks.LiftingProblem

noncomputable section

/-! ### The projection through the biproduct comparison -/

variable {C₁ C₃ : Type*} [Category C₁] [Category C₃] [Preadditive C₁] [Preadditive C₃]
  [HasBinaryBiproducts C₁] [HasBinaryBiproducts C₃] [HasShift C₁ ℤ] [HasShift C₃ ℤ]

/-- **The comparison `H(G ⊕ G[1]) ≅ Z ⊕ Z[1]` carries the projection to the image of the
projection**, followed by the given isomorphism `i : HG ≅ Z`. -/
theorem biprodShiftIsoOfObjIso_hom_fst (H : C₁ ⥤ C₃) (hH : H.Additive)
    (cH : H.CommShift ℤ) {G : C₁} {Z : C₃} (i : H.obj G ≅ Z) :
    (biprodShiftIsoOfObjIso H hH cH i).hom ≫ biprod.fst =
      H.map (biprod.fst : G ⊞ G⟦(1 : ℤ)⟧ ⟶ G) ≫ i.hom := by
  let := hH
  let := cH
  simp [biprodShiftIsoOfObjIso, biprodShiftIsoOfFunctorIso, Functor.biprodIsoOfAdditive]

/-! ### The step -/

/-- **The two-open step of [Stacks, Tag 09IM], in the strengthened form.** Let `resU : C ⥤ DU`
and `resV : C ⥤ DV` be the two restrictions to the members of a cover by two opens, let
`rU : DU ⥤ DW` and `rV : DV ⥤ DW` be the restrictions to the overlap, and let
`ω : resU ⋙ rU ≅ resV ⋙ rV` be the comparison of the two routes to it. Let `A` be an object of
`DU` with `A ⊕ A[1]` in the good class and `a : A ⟶ resU E`. Suppose

* `affine`: over `V` every good object `F` of `DW` with a map to `rV (resV E)` is split off some
  good `B` of `DV` as `F ⊕ F[1]`, compatibly — the affine case of [Stacks, Tag 09IM];
* `glue`: a good object over `U` and a good object over `V`, identified over the overlap
  compatibly with their maps to the restrictions of `E`, come from a good object over `C` with a
  map to `E` — [Stacks, Tag 08DG].

Then there is a good `R` with `ρ : R ⟶ E` and an isomorphism `resU R ≅ A ⊕ A[1]` through which
`resU ρ` is the projection onto `A` followed by `a`. -/
theorem exists_biprod_iso_hom_of_affine_overlap
    {C DU DV DW : Type*} [Category C] [Category DU] [Category DV] [Category DW]
    [Preadditive DU] [Preadditive DW] [HasBinaryBiproducts DU] [HasBinaryBiproducts DW]
    [HasShift DU ℤ] [HasShift DW ℤ]
    {resU : C ⥤ DU} {resV : C ⥤ DV} {rU : DU ⥤ DW} {rV : DV ⥤ DW}
    (hrU : rU.Additive) (crU : rU.CommShift ℤ) (ω : resU ⋙ rU ≅ resV ⋙ rV)
    (GC : C → Prop) (GU : DU → Prop) (GV : DV → Prop) (GW : DW → Prop)
    {E : C} {A : DU} (hA : GU (A ⊞ A⟦(1 : ℤ)⟧)) (hAW : GW (rU.obj A))
    (a : A ⟶ resU.obj E)
    (affine : ∀ F : DW, GW F → ∀ α : F ⟶ rV.obj (resV.obj E),
      ∃ (B : DV) (β : B ⟶ resV.obj E) (e : rV.obj B ≅ F ⊞ F⟦(1 : ℤ)⟧),
        GV B ∧ rV.map β = e.hom ≫ biprod.fst ≫ α)
    (glue : ∀ A' : DU, GU A' → ∀ B : DV, GV B → ∀ (a' : A' ⟶ resU.obj E)
      (b : B ⟶ resV.obj E) (c : rU.obj A' ≅ rV.obj B),
      rU.map a' ≫ ω.hom.app E = c.hom ≫ rV.map b →
      ∃ (R : C) (ρ : R ⟶ E), GC R ∧ ∃ (f : resU.obj R ≅ A') (_ : resV.obj R ≅ B),
        resU.map ρ = f.hom ≫ a') :
    ∃ (R : C) (ρ : R ⟶ E), GC R ∧
      ∃ f : resU.obj R ≅ A ⊞ A⟦(1 : ℤ)⟧, resU.map ρ = f.hom ≫ biprod.fst ≫ a := by
  obtain ⟨B, β, e, hB, hβ⟩ := affine (rU.obj A) hAW (rU.map a ≫ ω.hom.app E)
  have hab : rU.map (biprod.fst ≫ a) ≫ ω.hom.app E =
      (biprodShiftIsoOfObjIso rU hrU crU (Iso.refl (rU.obj A)) ≪≫ e.symm).hom ≫ rV.map β := by
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hβ, Iso.inv_hom_id_assoc, Functor.map_comp,
      Category.assoc, reassoc_of% biprodShiftIsoOfObjIso_hom_fst, Iso.refl_hom, Category.id_comp]
  obtain ⟨R, ρ, hR, f, -, hρ⟩ :=
    glue (A ⊞ A⟦(1 : ℤ)⟧) hA B hB (biprod.fst ≫ a) β
      (biprodShiftIsoOfObjIso rU hrU crU (Iso.refl (rU.obj A)) ≪≫ e.symm) hab
  exact ⟨R, ρ, hR, f, hρ⟩

/-! ### Moving the affine case onto the overlap -/

/-- **The splitting statement transports along an equivalence of the overlap categories.** Let
`resO : DV ⥤ DO` and `rV : DV ⥤ DW` be two restrictions of `DV`, let `Ψ : DO ≌ DW` be an
equivalence identifying their targets and let `κ : resO ⋙ Ψ.functor ≅ rV` compare them. If over
`DO` every good `F` with a map `α : F ⟶ resO E` is split off a good `B` as `F ⊕ F[1]` compatibly
with `α`, then the same holds over `DW`. -/
theorem exists_biprod_iso_hom_of_equivalence
    {DV DO DW : Type*} [Category DV] [Category DO] [Category DW]
    [Preadditive DO] [Preadditive DW] [HasBinaryBiproducts DO] [HasBinaryBiproducts DW]
    [HasShift DO ℤ] [HasShift DW ℤ]
    {resO : DV ⥤ DO} {rV : DV ⥤ DW} (Ψ : DO ≌ DW) (κ : resO ⋙ Ψ.functor ≅ rV)
    (hΨ : Ψ.functor.Additive) (cΨ : Ψ.functor.CommShift ℤ)
    (GV : DV → Prop) (GO : DO → Prop) (GW : DW → Prop)
    (hGback : ∀ F : DW, GW F → GO (Ψ.inverse.obj F)) {E : DV}
    (hyp : ∀ F : DO, GO F → ∀ α : F ⟶ resO.obj E,
      ∃ (B : DV) (β : B ⟶ E) (e : resO.obj B ≅ F ⊞ F⟦(1 : ℤ)⟧), GV B ∧
        resO.map β = e.hom ≫ biprod.fst ≫ α)
    (F : DW) (hF : GW F) (α : F ⟶ rV.obj E) :
    ∃ (B : DV) (β : B ⟶ E) (e : rV.obj B ≅ F ⊞ F⟦(1 : ℤ)⟧), GV B ∧
      rV.map β = e.hom ≫ biprod.fst ≫ α := by
  obtain ⟨B, β, e₀, hB, hβ⟩ := hyp (Ψ.inverse.obj F) (hGback F hF)
    (Ψ.inverse.map (α ≫ κ.inv.app E) ≫ (Ψ.unitIso.app (resO.obj E)).inv)
  have hnat : rV.map β = κ.inv.app B ≫ Ψ.functor.map (resO.map β) ≫ κ.hom.app E := by
    rw [← Functor.comp_map, κ.hom.naturality, Iso.inv_hom_id_app_assoc]
  have hα : Ψ.functor.map (Ψ.inverse.map (α ≫ κ.inv.app E) ≫
      (Ψ.unitIso.app (resO.obj E)).inv) ≫ κ.hom.app E = (Ψ.counitIso.app F).hom ≫ α := by
    simp
  refine ⟨B, β, (κ.app B).symm ≪≫ Ψ.functor.mapIso e₀ ≪≫
    biprodShiftIsoOfObjIso Ψ.functor hΨ cΨ (Ψ.counitIso.app F), hB, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv, Category.assoc,
    reassoc_of% biprodShiftIsoOfObjIso_hom_fst]
  rw [← hα, hnat, hβ]
  simp only [Functor.map_comp, Category.assoc]

end

end Stacks.LiftingProblem

end
