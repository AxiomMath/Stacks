module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Coproducts of schemes are universal colimits

A coproduct of a small family of schemes is a *universal* colimit: pulling the cofan back
along any morphism into the coproduct again produces a colimit cofan. Equivalently, a scheme
over a disjoint union decomposes canonically as the disjoint union of its restrictions to the
summands. The same holds in the slice category of schemes over a fixed base.

## Main results

* `AlgebraicGeometry.isUniversalColimit_sigmaCofan`: the canonical cofan of a coproduct of
  schemes is a universal colimit.
* `AlgebraicGeometry.isUniversalColimit_of_isColimit_cofan` and
  `AlgebraicGeometry.isUniversalColimit_of_isColimit_discrete`: the same for an arbitrary
  colimit cofan, respectively an arbitrary colimit of a discrete diagram.
* `AlgebraicGeometry.isUniversalColimit_of_isColimit_cofanOver`: the same in the slice
  category over a fixed base scheme.
* `AlgebraicGeometry.isColimitCofanOfIsColimitLeft`: a cofan in the slice category is a
  colimit as soon as the underlying cofan of schemes is.
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {I : Type v} [Small.{u} I]

/-- A cocone over a discrete diagram is a colimit iff the associated cofan is. -/
private theorem nonempty_isColimit_iff_cofanMk {C : Type*} [Category C] {J : Type*}
    {F : Discrete J ⥤ C}
    (c : Cocone F) :
    Nonempty (IsColimit c) ↔ Nonempty (IsColimit (Cofan.mk c.pt (fun i ↦ c.ι.app ⟨i⟩))) :=
  ((IsColimit.precomposeHomEquiv Discrete.natIsoFunctor.symm c).symm.nonempty_congr).trans
    (IsColimit.equivIsoColimit (show (Cocone.precompose Discrete.natIsoFunctor.symm.hom).obj c ≅
      Cofan.mk c.pt (fun i ↦ c.ι.app ⟨i⟩) from
        Cocone.ext (Iso.refl _) (by intro j; simp))).nonempty_congr

/-- The canonical cofan of a coproduct of a small family of schemes is a universal
colimit. -/
theorem isUniversalColimit_sigmaCofan (X : I → Scheme.{u}) :
    IsUniversalColimit (Cofan.mk (∐ X) (Sigma.ι X)) := by
  intro F' c' α g h hα hp
  change ∀ j, IsPullback (c'.ι.app j) (α.app j) g (Sigma.ι X j.as) at hp
  have hi (i : I) : IsOpenImmersion (c'.ι.app ⟨i⟩) :=
    MorphismProperty.of_isPullback (hp ⟨i⟩).flip
      (show IsOpenImmersion (Sigma.ι X i) from inferInstance)
  have hr (i : I) : (c'.ι.app ⟨i⟩).opensRange = g ⁻¹ᵁ (Sigma.ι X i).opensRange := by
    rw [← Scheme.Hom.opensRange_pullbackFst (Sigma.ι X i) g]
    simpa only [(hp ⟨i⟩).isoPullback_hom_fst] using
      (Scheme.Hom.opensRange_comp_of_isIso (hp ⟨i⟩).isoPullback.hom
        (pullback.fst g (Sigma.ι X i)))
  apply (nonempty_isColimit_iff_cofanMk c').mpr
  apply AlgebraicGeometry.nonempty_isColimit_cofanMk_of
  · simp only [hr]
    rw [eq_top_iff]
    intro y _
    obtain ⟨i, x, hx⟩ := (AlgebraicGeometry.sigmaOpenCover X).exists_eq (g.base y)
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨i, x, hx⟩
  · intro i j hij
    dsimp only [Function.onFun]
    rw [hr, hr, disjoint_iff]
    apply le_antisymm _ bot_le
    intro y hy
    have hmem : g y ∈ (Sigma.ι X i).opensRange ⊓ (Sigma.ι X j).opensRange := hy
    rwa [disjoint_iff.mp (AlgebraicGeometry.disjoint_opensRange_sigmaι X i j hij)] at hmem

/-- Any colimit cofan of a small family of schemes is a universal colimit. -/
theorem isUniversalColimit_of_isColimit_cofan {X : I → Scheme.{u}} {c : Cofan X}
    (hc : IsColimit c) : IsUniversalColimit c :=
  (isUniversalColimit_sigmaCofan X).of_iso ((coproductIsCoproduct X).uniqueUpToIso hc)

/-- Any colimit of a small discrete diagram of schemes is a universal colimit. -/
theorem isUniversalColimit_of_isColimit_discrete {F : Discrete I ⥤ Scheme.{u}}
    {c : Cocone F} (hc : IsColimit c) : IsUniversalColimit c := by
  have hc' := ((nonempty_isColimit_iff_cofanMk c).mp ⟨hc⟩).some
  exact ((isUniversalColimit_of_isColimit_cofan hc').precompose_isIso
    Discrete.natIsoFunctor.hom).of_iso
      (Cocone.ext (Iso.refl _) (by intro j; simp))

/-- Any colimit cofan of a small family of schemes over a base is a universal colimit in the
slice category. -/
theorem isUniversalColimit_of_isColimit_cofanOver {S : Scheme.{u}} {Y : I → Over S}
    {c : Cofan Y} (hc : IsColimit c) : IsUniversalColimit c :=
  .of_mapCocone (Over.forget S)
    (isUniversalColimit_of_isColimit_discrete (isColimitOfPreserves (Over.forget S) hc))

/-- The canonical cofan of a coproduct of a small family of schemes over a base is a
universal colimit in the slice category. -/
theorem isUniversalColimit_sigmaCofanOver {S : Scheme.{u}} (Y : I → Over S) :
    IsUniversalColimit (Cofan.mk (∐ Y) (Sigma.ι Y)) :=
  isUniversalColimit_of_isColimit_cofanOver (coproductIsCoproduct Y)

/-- A cofan of schemes over a base is a colimit as soon as the underlying cofan of schemes
is. -/
def isColimitCofanOfIsColimitLeft {S : Scheme.{u}} {Y : I → Over S} (c : Cofan Y)
    (hc : IsColimit (Cofan.mk c.pt.left (fun i ↦ (c.inj i).left))) : IsColimit c :=
  isColimitOfReflects (Over.forget S)
    ((Cofan.isColimitMapCoconeEquiv (Over.forget S) Y c).symm hc)

end AlgebraicGeometry

end
