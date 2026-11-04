module

public import StacksFrontier.AlgebraicGeometry.Curves.SheafDerivationAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.AffineOpenOperator
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OperatorGluing

/-!
# Gluing vector fields from affine-local data

Let `Y` be a scheme over a field `k` and let `U` be an open cover of `Y`. This file glues a
family of operators on the structure sheaf, one over each member of the cover, into a vector
field on `Y` in the sense of Section 53.26 — with the vanishing on the base asked for only as the
vanishing on `Γ(Spec k, ⊤)` over the member itself.

That is the difference from `Stacks.Curves.existsUnique_sheafDerivationOf_of_cover`, which asks
for the vanishing on the sections of `g⁻¹ 𝒪_{Spec k}`: those are a sheafified left Kan extension
and cannot be written down, so the hypothesis cannot be checked directly against ring-level data.
Here the operators are glued first and the passage to `g⁻¹ 𝒪_{Spec k}` is made once, globally, by
`Stacks.Curves.sheafDerivationOfFamily`.

## Main results

* `Stacks.Curves.existsUnique_sheafDerivationOf_of_affineCover` — **a compatible family of
  operators on the members of an open cover, each obeying the Leibniz rule and killing the image
  of `Γ(Spec k, ⊤)`, glues to a unique vector field.**

Combined with
`Stacks.AlgebraicGeometry.DifferentialsAffine.exists_rawOp_of_leibniz` this turns a family of
`k`-derivations of the coordinate rings of the members of an affine open cover into a vector
field on `Y`.

## Implementation notes

The glued family is `DiffOp.coverGlue`, which needs only naturality and the agreement on
overlaps; the order condition of `DiffOp.existsUnique_globalOp_of_cover` is not used, because the
Leibniz rule of the glued family is checked directly against the sheaf condition instead of being
transported through the order-one identification.

Both the Leibniz rule and the vanishing on the base are identities between sections of `𝒪_Y`, so
both are checked on the members of the cover and assembled by
`TopCat.Presheaf.IsSheaf.section_ext`. The vanishing is asked for only over `Γ(Spec k, ⊤)`
because `Spec` of a field has only the two opens (`Stacks.Curves.opens_eq_bot_or_eq_top`), and it
is asked for only over the member `U i` itself because naturality carries it to every open
inside.

## References

* [Stacks Project, Tag 0E66](https://stacks.math.columbia.edu/tag/0E66)
* [Stacks Project, Tag 09CR](https://stacks.math.columbia.edu/tag/09CR)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
  {ι : Type*} (U : ι → Y.Opens) (hU : ∀ p : Y, ∃ i, p ∈ U i)
  (d : ∀ i, DiffOp.RawOp (SheafOfModules.unit Y.ringCatSheaf)
    (SheafOfModules.unit Y.ringCatSheaf) (U i))
  (hnat : ∀ i, (d i).IsNatural) (hagree : DiffOp.AgreeOnCover U d)

/-- The family of additive maps on the sections of `𝒪_Y` glued from a compatible family of
operators on the members of an open cover. -/
noncomputable def glueFamily (W : Y.Opens) : Γ(Y, W) →+ Γ(Y, W) :=
  DiffOp.coverGlue U hU d hnat hagree (op W)

/-- On an open contained in a member of the cover, the glued family is the operator of that
member. -/
theorem glueFamily_apply (i : ι) {W : Y.Opens} (hW : W ≤ U i) (x : Γ(Y, W)) :
    glueFamily U hU d hnat hagree W x = (d i).unitOp (Over.mk (homOfLE hW)) x :=
  DiffOp.coverGlueHom_app_apply U hU d hnat hagree i hW x

/-- The glued family commutes with restriction of sections. -/
theorem glueFamily_map {W W' : Y.Opens} (h : W' ≤ W) (x : Γ(Y, W)) :
    (Y.presheaf.map (homOfLE h).op).hom (glueFamily U hU d hnat hagree W x)
      = glueFamily U hU d hnat hagree W' ((Y.presheaf.map (homOfLE h).op).hom x) :=
  (DiffOp.coverGlue_isNatural U hU d hnat hagree ⊤
    (Over.mk (homOfLE (le_top : W' ≤ ⊤))) (Over.mk (homOfLE (le_top : W ≤ ⊤)))
    (Over.homMk (homOfLE h) (Subsingleton.elim _ _)) x).symm

/-- The glued family, restricted to an open contained in a member of the cover, is the operator
of that member applied to the restricted section. -/
theorem map_glueFamily (i : ι) {W W' : Y.Opens} (hW' : W' ≤ W) (hi : W' ≤ U i) (x : Γ(Y, W)) :
    (Y.presheaf.map (homOfLE hW').op).hom (glueFamily U hU d hnat hagree W x)
      = (d i).unitOp (Over.mk (homOfLE hi))
        ((Y.presheaf.map (homOfLE hW').op).hom x) := by
  rw [glueFamily_map U hU d hnat hagree hW' x, glueFamily_apply U hU d hnat hagree i hi]

/-- Two sections over `W` are equal if, for each member `U i` of the cover, they agree on some open
`V ≤ W` containing `U i ⊓ W`. -/
private theorem eq_of_forall_restrict_cover (hU : ∀ p : Y, ∃ i, p ∈ U i)
    {W : Y.Opens} {x y : Γ(Y, W)}
    (h : ∀ i, ∃ (V : Y.Opens) (hV : V ≤ W), U i ⊓ W ≤ V ∧
      (Y.presheaf.map (homOfLE hV).op).hom x = (Y.presheaf.map (homOfLE hV).op).hom y) :
    x = y := by
  refine TopCat.Presheaf.IsSheaf.section_ext Y.sheaf.property fun p hp ↦ ?_
  obtain ⟨i, hi⟩ := hU p
  obtain ⟨V, hV, hle, hxy⟩ := h i
  exact ⟨V, hV, hle ⟨hi, hp⟩, hxy⟩

variable (hleib : ∀ (i : ι) (W : Over (U i)) (a b : Y.ringCatSheaf.obj.obj (op W.left)),
  (d i).unitOp W (a * b) = a * (d i).unitOp W b + b * (d i).unitOp W a)

include hleib in
/-- **The Leibniz rule for the glued family.** -/
theorem glueFamily_mul (W : Y.Opens) (a b : Γ(Y, W)) :
    glueFamily U hU d hnat hagree W (a * b)
      = a * glueFamily U hU d hnat hagree W b + b * glueFamily U hU d hnat hagree W a := by
  refine eq_of_forall_restrict_cover U hU fun i ↦ ⟨W ⊓ U i, inf_le_left, (inf_comm ..).le, ?_⟩
  simp only [map_add, map_mul,
    map_glueFamily U hU d hnat hagree i (inf_le_left : W ⊓ U i ≤ W) inf_le_right]
  exact hleib i (Over.mk (homOfLE (inf_le_right : W ⊓ U i ≤ U i))) _ _

variable (hbase : ∀ (i : ι) (r : Γ(Spec (.of k), ⊤)),
  (d i).unitOp (Over.mk (homOfLE (le_refl (U i)))) ((g.appLE ⊤ (U i) le_top).hom r) = 0)

include hbase in
/-- **The glued family kills the base.** -/
theorem glueFamily_app (V : (Spec (.of k)).Opens) (r : Γ(Spec (.of k), V)) :
    glueFamily U hU d hnat hagree (g ⁻¹ᵁ V) ((g.app V).hom r) = 0 := by
  rcases opens_eq_bot_or_eq_top V with rfl | rfl
  · exact TopCat.Presheaf.IsSheaf.section_ext Y.sheaf.property fun p hp ↦ absurd hp (by simp)
  · refine eq_of_forall_restrict_cover U hU fun i ↦ ⟨U i, le_top, inf_le_left, ?_⟩
    have hle : U i ≤ g ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := le_top
    rw [map_zero, map_glueFamily U hU d hnat hagree i hle (le_refl (U i)),
      show (Y.presheaf.map (homOfLE hle).op).hom ((g.app ⊤).hom r)
        = (g.appLE ⊤ (U i) le_top).hom r by rw [← CommRingCat.comp_apply]; rfl]
    exact hbase i r

include hU hnat hagree hleib hbase in
/-- **Gluing a vector field from affine-local data.** A family of operators on the structure
sheaf, one over each member of an open cover of a `k`-scheme `Y`, compatible with restriction,
agreeing on the opens contained in two members, obeying the Leibniz rule and killing the image of
`Γ(Spec k, ⊤)` over each member, glues to a unique vector field on `Y`.

Unlike `Stacks.Curves.existsUnique_sheafDerivationOf_of_cover`, the vanishing on the base is
asked for in the form in which affine-local data supplies it: on the image of `Γ(Spec k, ⊤)` in
the sections over the member of the cover, not on the sections of `g⁻¹ 𝒪_{Spec k}`. -/
theorem existsUnique_sheafDerivationOf_of_affineCover :
    ∃! D : SheafDerivationOf g,
      ∀ (i : ι) (W : Y.Opens) (hW : W ≤ U i) (s : Γ(Y, W)),
        D.onSections s = (d i).unitOp (Over.mk (homOfLE hW)) s := by
  refine ⟨sheafDerivationOfFamily g (glueFamily U hU d hnat hagree)
      (glueFamily_mul U hU d hnat hagree hleib)
      (fun {_ _} h x ↦ glueFamily_map U hU d hnat hagree h x)
      (glueFamily_app g U hU d hnat hagree hbase),
    fun i W hW s ↦ glueFamily_apply U hU d hnat hagree i hW s, fun D' hD' ↦ ?_⟩
  refine SheafDerivationOf.ext' fun W s ↦ ?_
  refine eq_of_forall_restrict_cover U hU fun i ↦
    ⟨W ⊓ U i, inf_le_left, (inf_comm ..).le, ?_⟩
  rw [← D'.onSections_restrict (inf_le_left : W ⊓ U i ≤ W) s,
    hD' i (W ⊓ U i) inf_le_right _, sheafDerivationOfFamily_onSections,
    map_glueFamily U hU d hnat hagree i (inf_le_left : W ⊓ U i ≤ W) inf_le_right]

end Stacks.Curves

end
