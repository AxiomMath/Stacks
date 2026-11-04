module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap

/-!
# Ideal sheaves of finite type and their inverse images

A quasi-coherent ideal sheaf `I` on a scheme `X` is of finite type when its ideal on every affine
open is finitely generated (`AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType`). This file
proves that the condition is local — it is enough to find, around every point of every affine
open, a standard open on which the ideal is finitely generated — and deduces that the inverse
image of an ideal sheaf of finite type along an arbitrary morphism of schemes is again of finite
type. Equivalently, the closed subscheme cut out by a finite type ideal sheaf stays so after
arbitrary base change.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isFiniteType_of_forall_exists_basicOpen`: locality of
  finite type for an ideal sheaf.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType.comap`: the inverse image of an ideal
  sheaf of finite type is of finite type.

## Implementation notes

Locality rests on `Ideal.fg_of_localizationSpan`: an ideal of a commutative ring is finitely
generated as soon as its image in `R_g` is, for a family of `g` generating the unit ideal. On an
affine open `U` the ideal of `I` on the standard open `D(g)` is the image of the ideal on `U`
(`AlgebraicGeometry.Scheme.IdealSheafData.map_ideal_basicOpen`), and `Γ(X, D(g))` is a model of
`R_g` (`AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`), so the hypothesis of
`Ideal.fg_of_localizationSpan` is exactly finite generation on the standard opens; that the
standard opens cover `U` is the statement that the `g` generate the unit ideal
(`AlgebraicGeometry.IsAffineOpen.self_le_iSup_basicOpen_iff`).

For the inverse image along `f : X ⟶ Y` this reduces the question to a standard open `D(g)` of
an affine open of `X` small enough to land in an affine open `V` of `Y`. There `f` restricts to a
morphism of affine schemes `D(g) ⟶ V`, where the inverse image of an ideal sheaf is computed by
`Stacks.IdealSheaf.ideal_comap_top_of_isAffine` as the image of the ideal upstairs, and an image
of a finitely generated ideal is finitely generated. No affineness or quasi-compactness of `f` is
needed.

## References

* [Stacks Project, Tag 01QX](https://stacks.math.columbia.edu/tag/01QX)
* [Stacks Project, Tag 01TV](https://stacks.math.columbia.edu/tag/01TV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- Finite generation of an ideal is preserved by the inverse image along an isomorphism of
commutative rings, because that inverse image is the image under the inverse isomorphism. -/
private theorem fg_of_fg_map_iso {R S : CommRingCat.{u}} (e : R ≅ S) {K : Ideal R}
    (h : (Ideal.map e.hom.hom K).FG) : K.FG := by
  have hK : K = Ideal.map e.inv.hom (Ideal.map e.hom.hom K) := by
    rw [Ideal.map_map, ← CommRingCat.hom_comp, e.hom_inv_id, CommRingCat.hom_id, Ideal.map_id]
  exact hK ▸ h.map _

/-- The ideal of global sections of the inverse image of `I` along the inclusion of an affine
open `V` is finitely generated exactly when the ideal of `I` on `V` is. -/
private theorem fg_ideal_comap_ι_top_iff (I : X.IdealSheafData) {V : X.Opens}
    (hV : IsAffineOpen V) (hT : IsAffineOpen (⊤ : V.toScheme.Opens)) :
    ((I.comap V.ι).ideal ⟨⊤, hT⟩).FG ↔ (I.ideal ⟨V, hV⟩).FG := by
  rw [Stacks.IdealSheaf.ideal_comap_ι_top I hV hT]
  exact ⟨fun h ↦ fg_of_fg_map_iso V.topIso.symm h, fun h ↦ h.map _⟩

/-- **Finite type is a local condition on an ideal sheaf.** If every point of every affine open
`U` lies in a standard open `D(g)`, `g : Γ(X, U)`, on which the ideal of `I` is finitely
generated, then `I` is of finite type. -/
theorem isFiniteType_of_forall_exists_basicOpen (I : X.IdealSheafData)
    (H : ∀ (U : X.affineOpens) (x : X), x ∈ U.1 → ∃ g : Γ(X, U.1),
      x ∈ X.basicOpen g ∧ (I.ideal (X.affineBasicOpen g)).FG) :
    I.IsFiniteType := by
  intro U
  set s : Set Γ(X, U.1) := {g | (I.ideal (X.affineBasicOpen g)).FG}
  have hcover : U.1 ≤ ⨆ g : s, X.basicOpen (g : Γ(X, U.1)) := by
    intro x hx
    obtain ⟨g, hxg, hfg⟩ := H U x hx
    exact Opens.mem_iSup.mpr ⟨⟨g, hfg⟩, hxg⟩
  refine Ideal.fg_of_localizationSpan s (U.2.self_le_iSup_basicOpen_iff.mp hcover)
    fun g ↦ ?_
  have hloc : IsLocalization.Away (g : Γ(X, U.1)) Γ(X, X.basicOpen (g : Γ(X, U.1))) :=
    U.2.isLocalization_basicOpen _
  let e : Localization.Away (g : Γ(X, U.1)) ≃ₐ[Γ(X, U.1)]
      Γ(X, X.basicOpen (g : Γ(X, U.1))) :=
    IsLocalization.algEquiv (Submonoid.powers (g : Γ(X, U.1))) _ _
  have hbase : Ideal.map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen (g : Γ(X, U.1)))) (I.ideal U) =
      I.ideal (X.affineBasicOpen (g : Γ(X, U.1))) := by
    rw [← I.map_ideal_basicOpen U (g : Γ(X, U.1))]
    rfl
  have hstep : Ideal.map (algebraMap Γ(X, U.1) (Localization.Away (g : Γ(X, U.1))))
      (I.ideal U) =
      Ideal.map (e.symm : Γ(X, X.basicOpen (g : Γ(X, U.1))) →+* _)
        (Ideal.map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen (g : Γ(X, U.1)))) (I.ideal U)) := by
    rw [Ideal.map_map]
    congr 1
    exact (RingHom.ext fun x ↦ e.symm.commutes x).symm
  rw [hstep, hbase]
  exact g.2.map _

/-- **The inverse image of an ideal sheaf of finite type is of finite type.** Equivalently, a
closed subscheme defined by a finite type ideal sheaf stays defined by one after arbitrary base
change (compare [Stacks, Tag 01TV]). -/
theorem IsFiniteType.comap {I : Y.IdealSheafData} (hI : I.IsFiniteType) (f : X ⟶ Y) :
    (I.comap f).IsFiniteType := by
  refine isFiniteType_of_forall_exists_basicOpen _ fun U x hx ↦ ?_
  obtain ⟨V, hVaff, hfxV⟩ : ∃ V : Y.Opens, IsAffineOpen V ∧ f x ∈ V := by
    obtain ⟨_, ⟨V, hVaff, rfl⟩, hmem, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    exact ⟨V, hVaff, hmem⟩
  obtain ⟨g, hgle, hxg⟩ :=
    U.2.exists_basicOpen_le (V := U.1 ⊓ f ⁻¹ᵁ V) ⟨x, hx, hfxV⟩ hx
  refine ⟨g, hxg, ?_⟩
  have hW : IsAffineOpen (X.basicOpen g) := U.2.basicOpen g
  have hWa : IsAffine (X.basicOpen g).toScheme := hW
  have hVa : IsAffine V.toScheme := hVaff
  have hcomap : (I.comap f).comap (X.basicOpen g).ι =
      (I.comap V.ι).comap (f.resLE V (X.basicOpen g) (hgle.trans inf_le_right)) := by
    rw [← comap_comp, ← comap_comp, Scheme.Hom.resLE_comp_ι]
  have htop : (((I.comap f).comap (X.basicOpen g).ι).ideal
      ⟨⊤, isAffineOpen_top (X.basicOpen g).toScheme⟩).FG := by
    rw [hcomap, Stacks.IdealSheaf.ideal_comap_top_of_isAffine]
    exact ((fg_ideal_comap_ι_top_iff I hVaff (isAffineOpen_top V.toScheme)).mpr
      (hI ⟨V, hVaff⟩)).map _
  exact (fg_ideal_comap_ι_top_iff (I.comap f) hW
    (isAffineOpen_top (X.basicOpen g).toScheme)).mp htop

end AlgebraicGeometry.Scheme.IdealSheafData

end
