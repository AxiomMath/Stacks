module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteBaseChangeAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangle

/-!
# Extension by zero commutes with a finite direct image

Let `π : Y ⟶ X` be finite, `j : U ⟶ X` an open immersion and `V = U ×_X Y`, with projections
`j' : V ⟶ Y` and `g : V ⟶ U`. Then `j_! g_* F ≅ π_* j'_! F` for every abelian sheaf `F` on the
small étale site of `V`.

## Main results

* `Stacks.EtaleCohomology.nonempty_extensionByZero_directImage_iso`: `j_! g_* F ≅ π_* j'_! F`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme TopologicalSpace

universe u

namespace Stacks.EtaleCohomology

variable {X Y U V : Scheme.{u}} (π : Y ⟶ X) [IsFinite π] (j : U ⟶ X) [IsOpenImmersion j]
  (j' : V ⟶ Y) [IsOpenImmersion j'] (g : V ⟶ U) (sq : IsPullback j' g π j)

include sq

omit [IsOpenImmersion j] in
/-- The inverse image of `π_* j'_! F` along a closed complement of `U` vanishes. -/
theorem isZero_inverseImage_directImage_extensionByZero_of_complement {Z : Scheme.{u}} (i : Z ⟶ X)
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (F : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsZero ((etaleAbelianInverseImage.{u, u + 1} i).obj
      ((etaleAbelianDirectImage.{u, u + 1} π).obj ((extensionByZero.{u, u + 1} j').obj F))) := by
  have hbc := isIso_etaleAbelianBaseChange_of_isFinite_of_isPullback_succUniverse π i
    (pullback.fst π i) (pullback.snd π i) (IsPullback.of_hasPullback π i)
  have hdisj : Disjoint (Set.range (pullback.fst π i).base) (Set.range j'.base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, rfl⟩ ⟨v, hv⟩
    have h1 : π.base ((pullback.fst π i).base p) = i.base ((pullback.snd π i).base p) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    have h2 : π.base (j'.base v) = j.base (g.base v) := by
      rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
    have hmem : j.base (g.base v) ∈ Set.range j.base := ⟨_, rfl⟩
    rw [hij, ← h2, hv, h1] at hmem
    exact hmem ⟨_, rfl⟩
  have hz := (etaleAbelianDirectImage.{u, u + 1} (pullback.snd π i)).map_isZero
    (isZero_etaleAbelianInverseImage_extensionByZero_of_disjoint.{u, u + 1}
      (pullback.fst π i) j' hdisj F)
  exact hz.of_iso (asIso ((etaleAbelianBaseChange.{u, u + 1} π i (pullback.fst π i)
    (pullback.snd π i) (IsPullback.of_hasPullback π i).w).app _))

omit [IsOpenImmersion j] [IsOpenImmersion j'] in
/-- The base change of `π_*` to `U`: `j⁻¹ π_* F ≅ g_* j'⁻¹ F`. -/
theorem nonempty_inverseImage_directImage_iso
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Nonempty ((etaleAbelianInverseImage.{u, u + 1} j).obj
        ((etaleAbelianDirectImage.{u, u + 1} π).obj F) ≅
      (etaleAbelianDirectImage.{u, u + 1} g).obj
        ((etaleAbelianInverseImage.{u, u + 1} j').obj F)) := by
  have := isIso_etaleAbelianBaseChange_of_isFinite_of_isPullback_succUniverse π j j' g sq
  exact ⟨asIso ((etaleAbelianBaseChange.{u, u + 1} π j j' g sq.w).app F)⟩

omit [IsFinite π] [IsOpenImmersion j] sq in
/-- `j'⁻¹ j'_! F ≅ F` for an open immersion `j'`. -/
theorem nonempty_inverseImage_extensionByZero_iso
    (F : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Nonempty ((etaleAbelianInverseImage.{u, u + 1} j').obj
        ((extensionByZero.{u, u + 1} j').obj F) ≅ F) :=
  ⟨(etaleAbelianInverseImageRestrictionIso.{u, u + 1} j').app _ ≪≫
    (asIso ((extensionByZeroAdj.{u, u + 1} j').unit.app F)).symm⟩

/-- The restriction to `U` of `π_* j'_! F` is `g_* F`. -/
theorem nonempty_etaleRestriction_directImage_extensionByZero_iso
    (F : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Nonempty ((etaleRestriction.{u, u + 1} j).obj
        ((etaleAbelianDirectImage.{u, u + 1} π).obj ((extensionByZero.{u, u + 1} j').obj F)) ≅
      (etaleAbelianDirectImage.{u, u + 1} g).obj F) := by
  obtain ⟨e₁⟩ := nonempty_inverseImage_directImage_iso π j j' g sq
    ((extensionByZero.{u, u + 1} j').obj F)
  obtain ⟨e₂⟩ := nonempty_inverseImage_extensionByZero_iso j' F
  exact ⟨((etaleAbelianInverseImageRestrictionIso.{u, u + 1} j).app _).symm ≪≫ e₁ ≪≫
    (etaleAbelianDirectImage.{u, u + 1} g).mapIso e₂⟩

/-- **Extension by zero commutes with a finite direct image.** For `π` finite, `j` an open
immersion and `V = U ×_X Y`, `j_! g_* F ≅ π_* j'_! F`. -/
theorem nonempty_extensionByZero_directImage_iso
    (F : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Nonempty ((extensionByZero.{u, u + 1} j).obj ((etaleAbelianDirectImage.{u, u + 1} g).obj F) ≅
      (etaleAbelianDirectImage.{u, u + 1} π).obj ((extensionByZero.{u, u + 1} j').obj F)) := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩ : Closeds X)
  have hirange : Set.range I.subschemeι.base = (Set.range j.base)ᶜ :=
    (Scheme.IdealSheafData.range_subschemeι _).trans
      (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  have hij : Set.range j.base = (Set.range I.subschemeι.base)ᶜ := by
    rw [hirange, compl_compl]
  set A := (etaleAbelianDirectImage.{u, u + 1} π).obj ((extensionByZero.{u, u + 1} j').obj F)
  obtain ⟨hzero, hS⟩ :=
    shortExact_extensionByZero_etaleAbelianDirectImage.{u, u + 1} I.subschemeι j hij A
  have : IsIso ((extensionByZeroAdj.{u, u + 1} j).counit.app A) :=
    hS.isIso_f_iff.mpr <| (etaleAbelianDirectImage.{u, u + 1} I.subschemeι).map_isZero <|
      isZero_inverseImage_directImage_extensionByZero_of_complement π j j' g sq I.subschemeι hij F
  obtain ⟨e⟩ := nonempty_etaleRestriction_directImage_extensionByZero_iso π j j' g sq F
  exact ⟨(extensionByZero.{u, u + 1} j).mapIso e.symm ≪≫
    asIso ((extensionByZeroAdj.{u, u + 1} j).counit.app A)⟩

end Stacks.EtaleCohomology

end
