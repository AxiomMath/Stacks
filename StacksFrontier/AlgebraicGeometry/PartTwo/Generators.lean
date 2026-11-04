module

public import StacksFrontier.AlgebraicGeometry.PartTwo.Basic

/-!
# [Stacks, Tag 01R3], part (2): the affine conormal sections and their generators

For an immersion `i : Z ⟶ X` and an affine open `V ⊆ X` whose inverse image under `i` is the
spectrum of `Γ(X, V) ⧸ I`, the sections over `V` of the direct image of the conormal sheaf are
canonically `I / I²`. This file proves the generator formula for that identification: the class
of `a ∈ I` is the image under the quotient map of any section of the ideal sheaf of a closed
factorization of `i` that restricts to `a`, at every such factorization and every open of it.

## Main results

* `Stacks.Conormal.affineConormalIsoCotangent_eq_conormalAffineSectionsIsoCotangent`: the
  affine-base-change identification of the conormal sections with `I / I²` and the one built by
  the locality comparison are the same isomorphism.
* `Stacks.Tag01R3PartTwo.affineConormalIsoCotangent_inv_toCotangent`: the generator formula at an
  arbitrary closed-immersion factorization and an arbitrary open of it.
* `Stacks.Tag01R3PartTwo.affineConormalIsoCotangentWithQuotient`: that identification bundled
  with the generator formula.
* `Stacks.Tag01R3PartTwo.affineConormalIsoCotangent_inv_toCotangent_liftCoborder`: the formula at
  the defining factorization `i = i.liftCoborder ≫ ι_{i.coborderRange}`, where the quotient map
  is the adjunction unit itself.

Compatibility with restriction to a smaller affine open is
`Stacks.Tag01R3PartTwo.affineConormalIsoCotangent_restrict`, in
`StacksFrontier.AlgebraicGeometry.PartTwo.Restrict`: the formula holds at every open of every
factorization, so it can be read at the coborder factorization over the smaller open, where one
section of the coborder ideal sheaf serves both presentations.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Conormal

/-- An isomorphism of modules inverts a value it has sent to a point. -/
private theorem inv_apply_eq_of_hom_apply_eq {R : Type*} [Ring R] {M N : ModuleCat R} (f : M ≅ N)
    {x : M} {y : N} (h : f.hom.hom x = y) : f.inv.hom y = x := by
  rw [← h]; exact f.hom_inv_id_apply x

/-- The affine-base-change identification of the conormal sections with `I / I²` and the one
built by the locality comparison agree.

Both inverses send the class of `a ∈ I` to the quotient generator of one and the same section of
the coborder ideal sheaf naming `a`, and `Ideal.toCotangent` is surjective. -/
theorem affineConormalIsoCotangent_eq_conormalAffineSectionsIsoCotangent {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsImmersion i] (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    Stacks.Conormal.affineConormalIsoCotangent i V hV I e he =
      Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent i V hV I e he := by
  refine Iso.ext ((Iso.inv_eq_inv _ _).mp (ConcreteCategory.hom_ext _ _ ?_))
  intro z
  obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective I z
  obtain ⟨y₀, hy₀⟩ := Stacks.Tag01R3PartTwo.exists_coborderSection i V hV I e he a
  have hle : i ⁻¹ᵁ V ≤ i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ V) :=
    le_of_eq (Stacks.Tag01R3PartTwo.preimage_eq_liftCoborder_preimage i V)
  have hA := affineConormalIsoCotangent_hom_pullbackSection i V hV I e he hle a y₀
    (by rw [← Scheme.Hom.appLE_preimage_self i.coborderRange.ι V]; exact hy₀)
  have hB := Stacks.Tag01R3PartTwo.conormalAffineSectionsIsoCotangent_toCotangent
    i V hV I e he a y₀ hy₀
  rw [inv_apply_eq_of_hom_apply_eq _ hA, inv_apply_eq_of_hom_apply_eq _ hB]
  rw [Stacks.Conormal.OpenFactorizations.conormalQuotientMap_liftCoborder i]
  exact Stacks.Conormal.Tag01R3Generators.res_eq (Stacks.Conormal.conormalSheaf i) _ _ _

end Stacks.Conormal

namespace Stacks.Tag01R3PartTwo

/-- **[Stacks, Tag 01R3], part (2): canonical affine generators.** The inverse affine
identification sends the class of an ideal section to its canonical conormal quotient, on every
open of every closed-immersion factorization, after restricting the ambient section.

The formula is proved at the coborder factorization by
`conormalAffineSectionsIsoCotangent_toCotangent` and moved to `(U, i')` by the compatibility
`Stacks.Conormal.OpenFactorizations.generator_eq_of_two_factorizations`, at the common source
open `i' ⁻¹ᵁ W`. The section of the coborder ideal sheaf that the comparison needs is produced by
`exists_coborderSection` from the presentation alone. -/
@[stacks 01R3 "part (2): canonical affine generators"]
theorem affineConormalIsoCotangent_inv_toCotangent {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i']
    (hfac : i' ≫ U.ι = i)
    (W : U.toScheme.Opens) (hW : W ≤ U.ι ⁻¹ᵁ V)
    (a : I)
    (x : (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.obj (.op W))
    (hx : (U.ι.appLE V W hW).hom (a : Γ(X, V)) =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i'.toLRSHom.toShHom))).val.app (.op W) x) :
    (Stacks.Conormal.conormalSheaf i).val.map
        (homOfLE (show i' ⁻¹ᵁ W ≤ i ⁻¹ᵁ V from by
          rw [← hfac]; exact i'.preimage_mono hW)).op
        ((Stacks.Conormal.affineConormalIsoCotangent i V hV I e he).inv.hom
          (I.toCotangent a)) =
      (Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op W) x := by
  rw [Stacks.Conormal.affineConormalIsoCotangent_eq_conormalAffineSectionsIsoCotangent
    i V hV I e he]
  obtain ⟨y₀, hy₀⟩ := exists_coborderSection i V hV I e he a
  have hT₂ : i' ⁻¹ᵁ W ≤ i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ V) := by
    rw [← preimage_eq_liftCoborder_preimage i V, ← hfac]
    exact i'.preimage_mono hW
  have hinv := Stacks.Conormal.inv_apply_eq_of_hom_apply_eq _
    (conormalAffineSectionsIsoCotangent_toCotangent i V hV I e he a y₀ hy₀)
  rw [hinv]
  refine Eq.trans (Stacks.Conormal.Tag01R3Generators.res_comp (Stacks.Conormal.conormalSheaf i)
    (eqToHom (preimage_eq_liftCoborder_preimage i V))
    (homOfLE (hT₂.trans_eq (preimage_eq_liftCoborder_preimage i V).symm))
    (homOfLE hT₂) _) ?_
  refine Eq.trans (Stacks.Conormal.OpenFactorizations.generator_eq_of_two_factorizations
    i V (a : Γ(X, V)) i.coborderRange U i.liftCoborder i' i.liftCoborder_ι hfac
    (i.coborderRange.ι ⁻¹ᵁ V) le_rfl W hW y₀ x hy₀ hx (i' ⁻¹ᵁ W) hT₂ le_rfl) ?_
  exact Stacks.Conormal.Tag01R3Generators.res_self (Stacks.Conormal.conormalSheaf i) _ _

/-- **[Stacks, Tag 01R3], part (2): the affine identification with canonical quotient
generators.** The sections over an affine open `V` of the ambient scheme of the direct image of
the conormal sheaf are `I.Cotangent`, *together with* the formula on ideal generators for every
closed-immersion factorization and every open of it.

The isomorphism is `Stacks.Conormal.affineConormalIsoCotangent` and the second component is
`affineConormalIsoCotangent_inv_toCotangent`. -/
@[stacks 01R3 "part (2): affine identification with canonical quotient generators"]
noncomputable def affineConormalIsoCotangentWithQuotient {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    { c : ((modulePushforward i.toLRSHom.toShHom).obj
        (Stacks.Conormal.conormalSheaf i)).val.obj (.op V) ≅
          ModuleCat.of Γ(X, V) I.Cotangent //
      ∀ (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i']
        (hfac : i' ≫ U.ι = i)
        (W : U.toScheme.Opens) (hW : W ≤ U.ι ⁻¹ᵁ V)
        (a : I)
        (x : (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.obj (.op W)),
        (U.ι.appLE V W hW).hom (a : Γ(X, V)) =
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom i'.toLRSHom.toShHom))).val.app (.op W) x →
        (Stacks.Conormal.conormalSheaf i).val.map
          (homOfLE (show i' ⁻¹ᵁ W ≤ i ⁻¹ᵁ V from by
            rw [← hfac]; exact i'.preimage_mono hW)).op
          (c.inv.hom (I.toCotangent a)) =
            (Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op W) x } :=
  ⟨Stacks.Conormal.affineConormalIsoCotangent i V hV I e he,
    fun U i' _ hfac W hW a x hax =>
      affineConormalIsoCotangent_inv_toCotangent i V hV I e he U i' hfac W hW a x hax⟩

/-- **[Stacks, Tag 01R3], part (2): defining adjunction-unit generators.** On the defining
factorization the affine generator is the image under the defining adjunction unit itself.

This is `affineConormalIsoCotangent_inv_toCotangent` at `(i.coborderRange, i.liftCoborder)`,
with `Stacks.Conormal.OpenFactorizations.conormalQuotientMap_liftCoborder` — the normalization
`Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf_liftCoborder` read on the quotient map —
replacing the quotient map by the unit. -/
@[stacks 01R3 "part (2): defining adjunction-unit generators"]
theorem affineConormalIsoCotangent_inv_toCotangent_liftCoborder {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (W : i.coborderRange.toScheme.Opens) (hW : W ≤ i.coborderRange.ι ⁻¹ᵁ V)
    (a : I)
    (x : (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom).val.obj (.op W))
    (hx : (i.coborderRange.ι.appLE V W hW).hom (a : Γ(X, V)) =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i.liftCoborder.toLRSHom.toShHom))).val.app (.op W) x) :
    (Stacks.Conormal.conormalSheaf i).val.map
        (homOfLE (show i.liftCoborder ⁻¹ᵁ W ≤ i ⁻¹ᵁ V from
          (i.liftCoborder.preimage_mono hW).trans_eq
            (congrArg (fun f : Z ⟶ X ↦ f ⁻¹ᵁ V) i.liftCoborder_ι))).op
        ((Stacks.Conormal.affineConormalIsoCotangent i V hV I e he).inv.hom
          (I.toCotangent a)) =
      ((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
        (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom)).val.app (.op W) x :=
  (affineConormalIsoCotangent_inv_toCotangent i V hV I e he i.coborderRange i.liftCoborder
      i.liftCoborder_ι W hW a x hx).trans
    (congr($(Stacks.Conormal.OpenFactorizations.conormalQuotientMap_liftCoborder i).val.app
      (.op W) x))

end Stacks.Tag01R3PartTwo

end
