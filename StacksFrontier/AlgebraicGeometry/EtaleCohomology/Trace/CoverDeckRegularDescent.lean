module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverDeckStepEight
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocallyConstantSelfMapTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.RegularDescentSheafRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRestrictScalarsNatural

/-!
# The deck action on the compactified cover is multiplication in `A[H]`

Let `G` be a Galois covering `f : V ⟶ U` with group `H`, `V ⟶ V̄` an open immersion and `σ` an
endomorphism of `V̄` restricting to the action of `g ∈ H` on `V`.  The sheaf `f_* j^{-1} A_{V̄}` on
`U` is the restriction of scalars along `A ⟶ A[H]` of the descent sheaf of `A[H]`: the
restriction of the constant sheaf `A_{V̄}` is `A_V`, which is the sheaf of locally constant
`A`-valued maps (Stacks 03P5), and
`Stacks.EtaleCohomology.EtaleGaloisCovering.regularDescentRestrictScalarsIso` identifies its
direct image with the descent sheaf.  Under this identification the action of `g` used in Step 8
of the proof of [Stacks, Tag 03UG] — the restriction of the canonical twist of `A_{V̄}` along `σ`,
pushed forward along `f` — is multiplication by `g⁻¹`, so traces of the deck transformations are
conjugacy traces of the trace over `A[H]` (Step 7).

## Main results

* `Stacks.EtaleCohomology.coverDescentIso`: `f_* j^{-1} A_{V̄} ≅ D(A[H])|_A`.
* `Stacks.EtaleCohomology.directImageTwist_comp_coverDescentIso_hom`: the deck transformation is
  `Stacks.Trace.groupElementAction`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 4–8.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section RestrictionForm

variable (Λ : Type) [CommRing Λ] (M : ModuleCat.{u + 1} Λ) {V Vb : Scheme.{u}} (j : V ⟶ Vb)
  [Etale j] [Mono j] (a : V ⟶ V) (σ : Vb ⟶ Vb) [IsIntegralHom σ] (sq : IsPullback a j j σ)

/-- `Stacks.EtaleCohomology.restrictionConstantIso_hom_comp_constantSelfMapTwist` with the
restricted twist written as `Stacks.EtaleCohomology.restrictionTwist`. -/
theorem restrictionConstantIso_hom_comp_constantSelfMapTwist_eq_restrictionTwist :
    (restrictionConstantIso Λ M j).hom ≫ constantSelfMapTwist Λ M a =
      restrictionTwist Λ j a σ sq (etaleModuleConstantSheaf Λ M Vb) (constantSelfMapTwist Λ M σ) ≫
        (etaleModuleDirectImage.{u, 0} Λ a).map (restrictionConstantIso Λ M j).hom :=
  restrictionConstantIso_hom_comp_constantSelfMapTwist Λ M j a σ sq

end RestrictionForm

section Descent

variable (A : Type) [CommRing A] {U : Scheme.{u}} {H : Type} [Group H] [Fintype H]
  (G : EtaleGaloisCovering U H) {Vb : Scheme.{u}} (jV : G.cover.left ⟶ Vb) [Etale jV] [Mono jV]
  (g : H) (σ : Vb ⟶ Vb) [IsIntegralHom σ] (sq : IsPullback (G.act g) jV jV σ)

/-- The module `A`, in the universe of sheaves on the small étale sites. -/
abbrev uliftCoefficientModule : ModuleCat.{u + 1} A := ModuleCat.of A (ULift.{u + 1} A)

/-- **`f_* j^{-1} A_{V̄} ≅ D(A[H])|_A`**: the restriction of the constant sheaf `A_{V̄}` is `A_V`,
which is the sheaf of locally constant maps; its direct image is the restriction of scalars of
the descent sheaf of `A[H]`. -/
def coverDescentIso :
    (etaleModuleDirectImage.{u, 0} A G.cover.hom).obj ((etaleModuleRestriction.{u, 0} A jV).obj
        (etaleModuleConstantSheaf A (uliftCoefficientModule.{u} A) Vb)) ≅
      G.regularDescentRestrictScalars (A := A) :=
  (etaleModuleDirectImage.{u, 0} A G.cover.hom).mapIso
      (restrictionConstantIso A (uliftCoefficientModule.{u} A) jV) ≪≫
    (etaleModuleDirectImage.{u, 0} A G.cover.hom).mapIso
      (smallEtaleConstantSheafIsoLocallyConstantMapsModule.{u, 0} A G.cover.left
        (uliftCoefficientModule.{u} A)) ≪≫
    (G.regularDescentRestrictScalarsIso (A := A)).symm

/-- If `d₀`, `d₁`, `d₂` commute with `x₁` and `x₂`, and `d₂ = l` corresponds to `θ` under `e`, then
`d₀` and `θ` commute with `x₁ ≫ x₂ ≫ e.inv`. -/
private lemma descentChase {C : Type*} [Category* C] {P Q R S : C} (x₁ : P ⟶ Q) (x₂ : Q ⟶ R)
    (e : S ≅ R) (d₀ : P ⟶ P) (d₁ : Q ⟶ Q) (d₂ l : R ⟶ R) (θ : S ⟶ S)
    (h₁ : x₁ ≫ d₁ = d₀ ≫ x₁) (h₂ : x₂ ≫ d₂ = d₁ ≫ x₂) (h₃ : d₂ = l)
    (h₄ : θ ≫ e.hom = e.hom ≫ l) :
    d₀ ≫ x₁ ≫ x₂ ≫ e.inv = (x₁ ≫ x₂ ≫ e.inv) ≫ θ := by
  have h₅ : l ≫ e.inv = e.inv ≫ θ := by
    rw [Iso.comp_inv_eq, Category.assoc, h₄, Iso.inv_hom_id_assoc]
  rw [← reassoc_of% h₁, ← reassoc_of% h₂, h₃, h₅, Category.assoc, Category.assoc]

/-- **The deck transformation `g` on `f_* j^{-1} A_{V̄}` is multiplication by `g⁻¹` on
`D(A[H])|_A`.** -/
theorem directImageTwist_comp_coverDescentIso_hom :
    directImageTwist A G.cover.hom (G.act g) (G.act_comp_hom g)
        ((etaleModuleRestriction.{u, 0} A jV).obj
          (etaleModuleConstantSheaf A (uliftCoefficientModule.{u} A) Vb))
        (restrictionTwist A jV (G.act g) σ sq
          (etaleModuleConstantSheaf A (uliftCoefficientModule.{u} A) Vb)
          (constantSelfMapTwist A (uliftCoefficientModule.{u} A) σ)) ≫
        (coverDescentIso A G jV).hom =
      (coverDescentIso A G jV).hom ≫
        (etaleModuleRestrictScalarsNatTrans (MonoidAlgebra.singleOneRingHom (R := A) (M := H))
          (Stacks.Trace.groupElementAction.{0, 0, u + 1} A H g) U).app G.regularDescentSheaf := by
  have h₁ := directImageTwist_naturality A G.cover.hom (G.act g) (G.act_comp_hom g) _ _
    (restrictionConstantIso A (uliftCoefficientModule.{u} A) jV).hom
    (restrictionConstantIso_hom_comp_constantSelfMapTwist_eq_restrictionTwist A
      (uliftCoefficientModule.{u} A) jV (G.act g) σ sq)
  have h₂ := directImageTwist_naturality A G.cover.hom (G.act g) (G.act_comp_hom g) _ _
    (constantSheafToSmallEtaleLocallyConstantMapsModule.{u, 0} A G.cover.left
      (uliftCoefficientModule.{u} A))
    (constantSheafToLocallyConstant_comp_locallyConstantToDirectImage A
      (uliftCoefficientModule.{u} A) (G.act g))
  have h₃ : directImageTwist A G.cover.hom (G.act g) (G.act_comp_hom g) _
      (locallyConstantToDirectImage A (ULift.{u + 1} A) (G.act g)) =
      locallyConstantPushforwardMap A (ULift.{u + 1} A) G.cover.hom G.cover.hom (G.act g)
        (G.act_comp_hom g) :=
    (locallyConstantPushforwardMap_eq_map_comp A (ULift.{u + 1} A) G.cover.hom (G.act g)
      (G.act_comp_hom g)).symm
  have h₄ := G.regularDescentRestrictScalarsHom_groupElementAction (A := A) g
  exact descentChase _ _ (G.regularDescentRestrictScalarsIso (A := A)) _ _ _ _ _ h₁ h₂ h₃ h₄

end Descent

end Stacks.EtaleCohomology
