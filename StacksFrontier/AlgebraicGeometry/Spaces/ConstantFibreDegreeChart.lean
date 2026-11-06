module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.DegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers

/-!
# A chart of constant fibre degree is finite locally free

Let `Z` be an algebraic space over a scheme `S` and let `ψ : h_V ⟶ Z` be an étale chart of `Z`
which is separated. The base change of `ψ` along itself is represented by a morphism of schemes
`V ×_Z V ⟶ V`, and this file shows that if the fibre of `ψ` above *every* field-valued point of
`Z` is finite locally free of one and the same rank `d`, then that morphism of schemes is finite
locally free of rank `d`.

## Main results

* `AlgebraicGeometry.Space.property_map_snd_yoneda_map_comp_iff`: base change of a
  representable morphism along a composite `yoneda.map g ≫ a` is the base change along `a`
  followed by the base change along `g`, read as an equivalence of any property of scheme
  morphisms which respects isomorphisms.
* `AlgebraicGeometry.Space.property_fiberToSpecResidueField_map_snd`: the residue-field fibre
  of the represented base change of `f : h_W ⟶ Z` to a chart `h_V ⟶ Z`, at a scheme point `v`
  of `V`, is the represented fibre of `f` above the field-valued point of `Z` carried by `v`.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_map_snd_self_of_forall_fieldValuedPoint`
  and `AlgebraicGeometry.Space.isFiniteLocallyFree_map_snd_self_of_forall_fieldValuedPoint`:
  constant fibre rank makes the self base change of a separated étale chart finite locally free
  of that rank.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_map_snd_fieldMorphism_of_degree_eq`: a
  fibre of degree at least `d` and not at least `d + 1`, in the sense of Stacks 086T, is finite
  locally free of rank exactly `d`.

## References

* [Stacks Project, Tag 03JI](https://stacks.math.columbia.edu/tag/03JI)
* [Stacks Project, Tag 086T](https://stacks.math.columbia.edu/tag/086T)
* [Stacks Project, Tag 086R](https://stacks.math.columbia.edu/tag/086R)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullback_presheaf_constantFibreDegreeChart
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (Limits.functorCategoryHasLimitsOfShape :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)).has_limit _

/-! ### Base change of a representable morphism along a composite -/

/-- **Base change along a composite.** For a representable `f : h_W ⟶ X`, a morphism
`a : h_U ⟶ X` and a morphism `g : T ⟶ U` of the site, the morphism of schemes representing the
base change of `f` along `yoneda.map g ≫ a` and the base change along `g` of the morphism of
schemes representing the base change of `f` along `a` agree up to isomorphism of their sources.
Any property of morphisms of schemes which respects isomorphisms therefore holds of one exactly
when it holds of the other. -/
theorem property_map_snd_yoneda_map_comp_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W U T : BigFppfOver B S hS}
    {f : yoneda.obj W ⟶ X} (hf : yoneda.relativelyRepresentable f)
    (a : yoneda.obj U ⟶ X) (g : T ⟶ U) :
    P ((BigFppfOver.toScheme B S hS).map (hf.snd (yoneda.map g ≫ a))) ↔
      P (pullback.snd ((BigFppfOver.toScheme B S hS).map (hf.snd a))
        ((BigFppfOver.toScheme B S hS).map g)) := by
  set F := BigFppfOver.toScheme B S hS with hF
  let : PreservesLimitsOfShape WalkingCospan F := by apply comp_preservesLimitsOfShape
  have hpaste := ((IsPullback.of_hasPullback (hf.snd a) g).map yoneda).paste_horiz
    (hf.isPullback a)
  set e := yoneda.preimageIso
    (hpaste.isoIsPullback _ _ (hf.isPullback (yoneda.map g ≫ a))) with hedef
  have he : e.hom ≫ hf.snd (yoneda.map g ≫ a) = pullback.snd (hf.snd a) g := by
    apply yoneda.map_injective
    simp [e, hpaste.isoIsPullback_hom_snd _ _ (hf.isPullback (yoneda.map g ≫ a))]
  have key : ∀ {A B C : Scheme.{u}} (e : A ≅ B) (g : A ⟶ C) (h : B ⟶ C), e.hom ≫ h = g →
      (P g ↔ P h) := by
    rintro A B C e g h rfl
    exact P.cancel_left_of_respectsIso e.hom h
  refine (key (F.mapIso e) (F.map (pullback.snd (hf.snd a) g)) _
    (by simp [← F.map_comp, he])).symm.trans ?_
  exact key (((IsPullback.of_hasPullback (hf.snd a) g).map F).isoIsPullback _ _
    (IsPullback.of_hasPullback (F.map (hf.snd a)) (F.map g))) _ _
    (((IsPullback.of_hasPullback (hf.snd a) g).map F).isoIsPullback_hom_snd _ _ _)

/-! ### The residue-field fibre of a base change to a chart -/

/-- Let `f : h_W ⟶ X` be a morphism from a scheme into an algebraic space over `S`, let
`ψ : h_V ⟶ X` be a morphism from a scheme, and suppose a property `P` of morphisms of schemes
holds of the represented fibre of `f` above every field-valued point of `X`. Then `P` holds of
the residue-field fibre, at every scheme point of `V`, of the morphism of schemes representing
the base change of `f` along `ψ`. -/
theorem property_fiberToSpecResidueField_map_snd (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {W V : BigFppfOver B S hS} (f : yoneda.obj W ⟶ X) (ψ : yoneda.obj V ⟶ X)
    (hP : ∀ p : FieldValuedPoint B S hS X,
      P ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX f).snd
          (yonedaEquiv.symm p.value))))
    (v : (BigFppfOver.toScheme B S hS).obj V) :
    P (((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX f).snd
        ψ)).fiberToSpecResidueField v) := by
  set hf := relativelyRepresentable_of_isAlgebraicSpace B S hS hX f with hfdef
  set q := schemePointRepresentative B S hS V v with hqdef
  have hvalue : yonedaEquiv.symm (FieldValuedPoint.map B S hS (yoneda.obj V) ψ q).value =
      yoneda.map q.siteHom ≫ ψ := fieldMorphism_map_yoneda B S hS X ψ q
  have hcomp : P ((BigFppfOver.toScheme B S hS).map
      (hf.snd (yoneda.map q.siteHom ≫ ψ))) := by
    rw [← hvalue]
    exact hP _
  rwa [property_map_snd_yoneda_map_comp_iff B S hS P hf ψ q.siteHom,
    toScheme_map_siteHom_schemePointRepresentative B S hS V v] at hcomp

/-! ### Constant fibre degree on a chart -/

/-- **A separated étale chart of constant fibre degree has finite locally free self base
change.** Let `ψ : h_V ⟶ Z` be an étale and separated morphism from a scheme into an algebraic
space over `S`, and suppose the fibre of `ψ` above every field-valued point of `Z` is finite
locally free of rank `d`. Then the morphism of schemes `V ×_Z V ⟶ V` representing the base
change of `ψ` along itself is finite locally free of rank `d`. -/
theorem isFiniteLocallyFreeOfRank_map_snd_self_of_forall_fieldValuedPoint
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    {V : BigFppfOver B S hS} (ψ : yoneda.obj V ⟶ Z)
    (hψ : (MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)).presheaf ψ)
    (hsep : IsSeparated B S hS ψ) (d : ℕ)
    (hrank : ∀ p : FieldValuedPoint B S hS Z,
      IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_of_isAlgebraicSpace B S hS hZ ψ).snd
          (yonedaEquiv.symm p.value))) d) :
    IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hZ ψ).snd ψ)) d := by
  obtain ⟨hflat, hfp, hsepScheme, -⟩ :=
    baseChange_properties_of_etale_chart B S hS (f := ψ) ψ hZ hψ
      (isFlat_of_presheafEtale B S hS hψ)
      (isLocallyOfFinitePresentation_of_presheafEtale B S hS hψ) hsep
      (isLocallyQuasiFinite_of_presheafEtale B S hS hψ)
  let := hflat
  let := hfp
  let := hsepScheme
  exact rank_of_constant_fiber_rank _ d fun v =>
    property_fiberToSpecResidueField_map_snd B S hS
      (IsFiniteLocallyFreeOfRank.property.{u} d) hZ ψ ψ hrank v

/-- **A separated étale chart of constant fibre degree has finite locally free self base
change.** Let `ψ : h_V ⟶ Z` be an étale and separated morphism from a scheme into an algebraic
space over `S` whose fibre above every field-valued point of `Z` is finite locally free of rank
`d`. Then the morphism of schemes `V ×_Z V ⟶ V` representing the base change of `ψ` along itself
is finite locally free. -/
theorem isFiniteLocallyFree_map_snd_self_of_forall_fieldValuedPoint
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    {V : BigFppfOver B S hS} (ψ : yoneda.obj V ⟶ Z)
    (hψ : (MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)).presheaf ψ)
    (hsep : IsSeparated B S hS ψ) (d : ℕ)
    (hrank : ∀ p : FieldValuedPoint B S hS Z,
      IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_of_isAlgebraicSpace B S hS hZ ψ).snd
          (yonedaEquiv.symm p.value))) d) :
    IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hZ ψ).snd ψ)) :=
  have := isFiniteLocallyFreeOfRank_map_snd_self_of_forall_fieldValuedPoint B S hS hZ ψ hψ
    hsep d hrank
  IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d

/-- Let `ψ : h_V ⟶ Z` be an étale morphism from a separated scheme `V` into an algebraic space
over `S` whose fibre above every field-valued point of `Z` is finite locally free of rank `d`.
Then the morphism of schemes `V ×_Z V ⟶ V` representing the base change of `ψ` along itself is
finite locally free. -/
theorem isFiniteLocallyFree_map_snd_self_of_isSeparated_scheme
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    {V : BigFppfOver B S hS} (ψ : yoneda.obj V ⟶ Z)
    (hψ : (MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)).presheaf ψ)
    (hV : Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj V)) (d : ℕ)
    (hrank : ∀ p : FieldValuedPoint B S hS Z,
      IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_of_isAlgebraicSpace B S hS hZ ψ).snd
          (yonedaEquiv.symm p.value))) d) :
    IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hZ ψ).snd ψ)) :=
  isFiniteLocallyFree_map_snd_self_of_forall_fieldValuedPoint B S hS hZ ψ hψ
    (isSeparated_of_scheme_isSeparated B S hS hV ψ) d hrank

/-! ### Reading the rank off the degree condition of Stacks 086T -/

/-- **A fibre of degree at least `d` and not at least `d + 1` is finite locally free of rank
`d`.** The degree condition is the one of Stacks 086T, stated on the fibre product of presheaves
with the two properties in their relatively representable form: a fibre which is not finite
counts as having infinite degree, so the condition at `d + 1` failing says both that the fibre
*is* finite and that no rank `d + 1` or larger occurs. -/
theorem isFiniteLocallyFreeOfRank_map_snd_fieldMorphism_of_degree_eq
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    {V : BigFppfOver B S hS} (ψ : yoneda.obj V ⟶ Z) (d : ℕ)
    (p : FieldValuedPoint B S hS Z)
    (hge : ¬ (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
            (BigFppfOver.toScheme B S hS)).presheaf
            (pullback.fst (yonedaEquiv.symm p.value) ψ) ∨
      ∃ r : ℕ, d ≤ r ∧
        (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
          (BigFppfOver.toScheme B S hS)).presheaf
          (pullback.fst (yonedaEquiv.symm p.value) ψ))
    (hlt : ¬ (¬ (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
            (BigFppfOver.toScheme B S hS)).presheaf
            (pullback.fst (yonedaEquiv.symm p.value) ψ) ∨
      ∃ r : ℕ, d + 1 ≤ r ∧
        (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
          (BigFppfOver.toScheme B S hS)).presheaf
          (pullback.fst (yonedaEquiv.symm p.value) ψ))) :
    IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_of_isAlgebraicSpace B S hS hZ ψ).snd
        (yonedaEquiv.symm p.value))) d := by
  obtain ⟨hfin, hno⟩ := not_or.1 hlt
  rcases hge with hnf | ⟨r, hdr, hr⟩
  · exact absurd (not_not.1 hfin) hnf
  obtain rfl : r = d := le_antisymm (not_lt.1 fun h => hno ⟨r, h, hr⟩) hdr
  exact (presheaf_pullback_fst_iff_property_snd B S hS
    (P := IsFiniteLocallyFreeOfRank.property.{u} r)
    (relativelyRepresentable_of_isAlgebraicSpace B S hS hZ ψ)
    (yonedaEquiv.symm p.value)).1 hr

end AlgebraicGeometry.Space

end
