module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStableOpenOfDualizing
public import StacksFrontier.AlgebraicGeometry.Quot.UniqueStableModelsReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOfFieldFibres

/-!
# The total space of a stable family of curves is a scheme

Let `f : X → S` be a stable family of curves (Stacks 0E75) and `ω = ω_{X/S}` its relative
dualizing sheaf (Stacks 0E6R). By Stacks 0E74 the module `ω` is ample relative to `f`: over every
point `s` of `S` the fibre `X_s` is stable, so `ω_{X_s}` is ample (Stacks 0E3P), and the locus of
the base over which `ω` is relatively ample is open (Stacks 0D3D) and contains every point. A
morphism of algebraic spaces carrying a relatively ample module is representable (Stacks 0D31,
0D32), and `S` is a scheme, so `X` is a scheme.

In particular the total space of a stable family of curves over the spectrum of a discrete
valuation ring is a scheme, which is `AlgebraicGeometry.StableFamilyTotalIsScheme`, the input of
the reduction of Stacks 0E97 for algebraic spaces to the case of schemes.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_iso_schemeSpace_total_of_isRelativelyAmple`: a family of
  curves whose structure morphism carries a relatively ample module has a scheme as total space.
* `AlgebraicGeometry.CurveFamily.isRelativelyAmple_of_isStableCurveFamily`: the relative
  dualizing sheaf of a stable family of curves is relatively ample (Stacks 0E74, (1) implies (2),
  over the whole base).
* `AlgebraicGeometry.CurveFamily.exists_iso_schemeSpace_total_of_isStableCurveFamily`: the total
  space of a stable family of curves is a scheme.
* `AlgebraicGeometry.stableFamilyTotalIsScheme_of`: `AlgebraicGeometry.StableFamilyTotalIsScheme`.

## Implementation notes

Nothing here carries a `stacks` attribute. One result is not yet available and is an explicit
hypothesis, in the shape of `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamily_of_dualizing`:

* `hω`: every prestable family of curves has a relative dualizing sheaf
  (`AlgebraicGeometry.CurveFamily.IsRelativeDualizingSheaf`; Stacks 0E6P, 0E6Q, 0E6R).

Stacks 0D3D enters through `AlgebraicGeometry.Space.isRelativelyAmple_of_isProper_of_fieldFibres`.
The fibrewise ampleness is
`AlgebraicGeometry.CurveFamily.exists_fibre_hasGenusTwo_iff_exists_fibre_isRelativelyAmple`
(Stacks 0E74 on one fibre), applied to the identity of the family.

## References

* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0E75](https://stacks.math.columbia.edu/tag/0E75)
* [Stacks Project, Tag 0E3P](https://stacks.math.columbia.edu/tag/0E3P)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0D32](https://stacks.math.columbia.edu/tag/0D32)
* [Stacks Project, Tag 0E97](https://stacks.math.columbia.edu/tag/0E97)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- **A family of curves with a relatively ample module has a scheme as total space.** If the
structure morphism `X ⟶ S` of a family of curves carries a module ample relative to it in the
sense of Stacks 0D31, then `X` is a scheme of the site: the morphism is representable and its
target `S` is a scheme (Stacks 0D32). -/
theorem exists_iso_schemeSpace_total_of_isRelativelyAmple (F : CurveFamily B hZ)
    {L : Space.Modules.{u, u} B integerBase hZ F.total.1 F.total.2}
    (hL : Space.IsRelativelyAmple B integerBase hZ F.toBase L) :
    ∃ (X : Scheme.{u}) (hX : B.Contains X),
      Nonempty (F.total ≅ schemeSpace (integerSiteObject B hZ hX)) := by
  have : (schemeSpace F.base).1.IsRepresentable :=
    inferInstanceAs (yoneda.obj F.base).IsRepresentable
  have : F.total.1.IsRepresentable := hL.isRepresentable
  obtain ⟨T, ⟨e⟩⟩ : ∃ T : BigFppfOver B integerBase hZ, Nonempty (F.total ≅ schemeSpace T) :=
    ⟨F.total.1.reprX, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso F.total.1.reprW.symm⟩⟩
  obtain ⟨⟨T, hT⟩, ⟨⟨⟩⟩, tHom⟩ := T
  obtain rfl : tHom = ObjectProperty.homMk (specULiftZIsTerminal.from _) :=
    ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _)
  exact ⟨T, hT, ⟨e⟩⟩

/-- **The relative dualizing sheaf of a stable family of curves is relatively ample** (Stacks
0E74, (1) implies (2), over the whole base). Let `F` be a stable family of curves and `ω` a
relative dualizing sheaf of `F`. Then `ω` is ample relative to the structure morphism of `F`.

By Stacks 0D3D read on field-valued points
(`AlgebraicGeometry.Space.isRelativelyAmple_of_isProper_of_fieldFibres`) it suffices that over
every field-valued point of the base some fibre carries the pullback of `ω` as a relatively ample
module. Every fibre of `F` is stable, so this is Stacks 0E74 on one fibre
(`AlgebraicGeometry.CurveFamily.exists_fibre_hasGenusTwo_iff_exists_fibre_isRelativelyAmple`),
applied to the identity of `F`. -/
theorem isRelativelyAmple_of_isStableCurveFamily {F : CurveFamily B hZ}
    (hF : IsStableCurveFamily B hZ F)
    {ω : Space.Modules.{u, u} B integerBase hZ F.total.1 F.total.2}
    (hω : F.IsRelativeDualizingSheaf B hZ ω) :
    Space.IsRelativelyAmple B integerBase hZ F.toBase ω := by
  have hid : schemeSpaceMap (𝟙 F : F ⟶ F).baseMap = 𝟙 (schemeSpace F.base) :=
    ObjectProperty.hom_ext _ (yoneda.map_id _)
  refine Space.isRelativelyAmple_of_isProper_of_fieldFibres F.proper hω.1 fun t => ?_
  obtain ⟨X'', p'', f'', hsq, hamp⟩ :=
    (exists_fibre_hasGenusTwo_iff_exists_fibre_isRelativelyAmple hF.1 hω (𝟙 F) t).1 (hF.2 t)
  rw [hid, Category.comp_id] at hsq
  exact ⟨X'', p'', f'', hsq, hamp⟩

/-- **The total space of a stable family of curves is a scheme.** Let `F` be a stable family of
curves over a scheme `S`. Its relative dualizing sheaf (`hω`) is relatively ample
(`AlgebraicGeometry.CurveFamily.isRelativelyAmple_of_isStableCurveFamily`, from Stacks 0E74 and
0D3D), so the total space of `F` is a scheme of the site
(`AlgebraicGeometry.CurveFamily.exists_iso_schemeSpace_total_of_isRelativelyAmple`). -/
theorem exists_iso_schemeSpace_total_of_isStableCurveFamily {F : CurveFamily B hZ}
    (hF : IsStableCurveFamily B hZ F)
    (hω : ∀ X : CurveFamily B hZ, IsPrestableCurveFamily B hZ X →
      ∃ ω : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2,
        X.IsRelativeDualizingSheaf B hZ ω) :
    ∃ (X : Scheme.{u}) (hX : B.Contains X),
      Nonempty (F.total ≅ schemeSpace (integerSiteObject B hZ hX)) := by
  obtain ⟨ω, hωF⟩ := hω F hF.1
  exact F.exists_iso_schemeSpace_total_of_isRelativelyAmple
    (isRelativelyAmple_of_isStableCurveFamily hF hωF)

end CurveFamily

variable (B hZ) in
/-- **The total space of a stable family of curves over a discrete valuation ring is a scheme**
(`AlgebraicGeometry.StableFamilyTotalIsScheme`), from the existence of relative dualizing sheaves
(`hω`, Stacks 0E6R): it is
`AlgebraicGeometry.CurveFamily.exists_iso_schemeSpace_total_of_isStableCurveFamily` over the
spectrum of the ring. -/
theorem stableFamilyTotalIsScheme_of (g : ℕ)
    (hω : ∀ X : CurveFamily B hZ, IsPrestableCurveFamily B hZ X →
      ∃ ω : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2,
        X.IsRelativeDualizingSheaf B hZ ω) :
    StableFamilyTotalIsScheme B hZ g := by
  intro R _ _ _ hR F _ hF
  exact CurveFamily.exists_iso_schemeSpace_total_of_isStableCurveFamily hF.1 hω

end AlgebraicGeometry

end
