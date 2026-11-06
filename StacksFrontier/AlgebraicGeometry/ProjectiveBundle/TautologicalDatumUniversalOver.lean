module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.ClassifiesDescent
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumBaseChangeSpec
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.UniversalOver

/-!
# The canonical tautological datum is universal over every test scheme

`Stacks.RelativeProj.TautologicalDatum.IsUniversalOver` asks that the base change of a tautological
datum of `𝐏(F)` along every morphism `f : T ⟶ X` be universal (Tag 0B3V at every base change).
For the canonical datum `Stacks.RelativeProj.tautologicalDatum F` this holds: its base change is
isomorphic, as a tautological datum, to the canonical datum of `𝐏(F')` — see
`Stacks.RelativeProj.tautologicalDatum_baseChange_univ_comp_tautologicalDatumTwistBaseChangeIso_hom`
— which is universal (`Stacks.RelativeProj.isUniversal_tautologicalDatum`), and universality only
depends on the datum up to such an isomorphism.

With this instance, Tag 01O4's mapping-in bijection
`Stacks.RelativeProj.TautologicalDatum.overMorphismEquivInvertibleQuotients` holds for the
canonical datum with no hypothesis. This file also computes that bijection on a morphism: it
sends `h : T ⟶ 𝐏(F)` over `f` to the class of the invertible quotient `h^*𝒪(1)` it pulls back
(`Stacks.RelativeProj.TautologicalDatum.overMorphismEquivInvertibleQuotients_apply`).

## Main results

* `Stacks.RelativeProj.TautologicalDatum.classifies_iff_of_univ_comp`: two tautological data
  identified over the universal quotients classify the same quotients.
* `Stacks.RelativeProj.isUniversalOver_tautologicalDatum`: **the canonical datum is universal
  over every test scheme.**
* `Stacks.RelativeProj.TautologicalDatum.overMorphismEquivInvertibleQuotients_apply`: the
  mapping-in bijection on a morphism.
* `Stacks.RelativeProj.TautologicalDatum.eq_of_overQuotient_isEquivalent`: two morphisms over the
  base pulling back equivalent quotients are equal.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Modules

variable {T X P P' : Scheme.{u}}

/-- **The pasting coherence of a section of a base change.** For a square `b ≫ π = π' ≫ f`, a
section `σ` of `π'` and `h = σ ≫ b`, the two identifications of `f^*M` with `h^*π^*M` agree: one
through the section `σ` and the square, the other directly. -/
theorem sectionOfBaseChange_coherence (f : T ⟶ X) (π : P ⟶ X) (π' : P' ⟶ T) (b : P' ⟶ P)
    (hb : b ≫ π = π' ≫ f) (h : T ⟶ P) (hh : h ≫ π = f) (σ : T ⟶ P') (hσ : σ ≫ π' = 𝟙 T)
    (hσb : σ ≫ b = h) (M : X.Modules) :
    (Scheme.Modules.pullbackId T).inv.app ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.pullbackCongr hσ).inv.app ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.pullbackComp σ π').inv.app ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.pullback σ).map ((Scheme.Modules.pullbackComp π' f).hom.app M) ≫
        (Scheme.Modules.pullback σ).map ((Scheme.Modules.pullbackCongr hb).inv.app M) ≫
        (Scheme.Modules.pullback σ).map ((Scheme.Modules.pullbackComp b π).inv.app M) ≫
        (Scheme.Modules.pullbackComp σ b).hom.app ((Scheme.Modules.pullback π).obj M) ≫
        (Scheme.Modules.pullbackCongr hσb).hom.app ((Scheme.Modules.pullback π).obj M) =
      (Scheme.Modules.pullbackCongr hh).inv.app M ≫
        (Scheme.Modules.pullbackComp h π).inv.app M := by
  subst hσb
  have hA := pullbackComp_congr_assoc σ b π (σ ≫ b) rfl (π' ≫ f) hb f
    (by rw [Category.assoc, hb, ← Category.assoc, hσ, Category.id_comp]) M
  have hB := pullbackComp_congr_assoc σ π' f (𝟙 T) hσ (π' ≫ f) rfl f (Category.id_comp f) M
  have u := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality (f := f)) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_app] at u
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_refl,
    NatTrans.id_app, Category.comp_id, Functor.map_comp, Category.assoc] at hA hB ⊢
  -- `u` reads `(pullbackComp (𝟙 T) f).hom` through the unit of the identity
  have u' : (Scheme.Modules.pullbackComp (𝟙 T) f).hom.app M =
      (Scheme.Modules.pullbackId T).hom.app ((Scheme.Modules.pullback f).obj M) ≫
        eqToHom (by simp) := by
    have u₂ : (Scheme.Modules.pullbackComp (𝟙 T) f).inv.app M ≫
        (Scheme.Modules.pullbackId T).hom.app ((Scheme.Modules.pullback f).obj M) =
          eqToHom (by simp) := by
      simpa using u
    have u₃ := (Iso.inv_comp_eq ((Scheme.Modules.pullbackComp (𝟙 T) f).app M)).1 u₂
    simp only [Iso.app_hom] at u₃
    rw [u₃, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  have cancel₁ : ∀ {W : T.Modules}
      (t : (Scheme.Modules.pullback σ).obj ((Scheme.Modules.pullback (b ≫ π)).obj M) ⟶ W),
      (Scheme.Modules.pullback σ).map ((Scheme.Modules.pullbackComp b π).inv.app M) ≫
        (Scheme.Modules.pullback σ).map ((Scheme.Modules.pullbackComp b π).hom.app M) ≫ t = t := by
    intro W t
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  refine ((Iso.app (Scheme.Modules.pullbackComp (σ ≫ b) π) M).cancel_iso_hom_right _ _).1 ?_
  simp only [Iso.app_hom, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hA' := hA =≫ eqToHom (congrArg (fun g => (Scheme.Modules.pullback g).obj M) hh.symm)
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at hA'
  rw [← hA', cancel₁]
  have hB' := hB =≫ eqToHom (congrArg (fun g => (Scheme.Modules.pullback g).obj M) hh.symm)
  simp only [Category.assoc, eqToHom_trans] at hB'
  simp only [eqToHom_map, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [hB', u', Iso.inv_hom_id_app_assoc]
  simp

end Stacks.Modules

namespace Stacks.RelativeProj

namespace TautologicalDatum

variable {X : Scheme.{u}} {F : X.Modules} [F.IsQuasicoherent]

/-- Two tautological data identified over their universal quotients pull back identified
quotients along a section. -/
theorem pullbackQuotientMap_comp_map_of_univ_comp (D₁ D₂ : TautologicalDatum X F)
    (α : D₁.twist ≅ D₂.twist) (hα : D₁.univ ≫ α.hom = D₂.univ) (σ : X ⟶ projectiveBundle X F)
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) :
    D₁.pullbackQuotientMap σ hσ ≫ (Scheme.Modules.pullback σ).map α.hom =
      D₂.pullbackQuotientMap σ hσ := by
  simp only [pullbackQuotientMap, Category.assoc, ← Functor.map_comp, hα]

/-- **Two tautological data identified over their universal quotients classify the same
quotients.** -/
theorem classifies_iff_of_univ_comp (D₁ D₂ : TautologicalDatum X F) (α : D₁.twist ≅ D₂.twist)
    (hα : D₁.univ ≫ α.hom = D₂.univ) (σ : X ⟶ projectiveBundle X F)
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) (Q : Stacks.Divisors.InvertibleQuotient X F) :
    D₁.Classifies σ hσ Q ↔ D₂.Classifies σ hσ Q := by
  rw [classifies_iff, classifies_iff]
  constructor <;> rintro ⟨β, hβ⟩
  · refine ⟨(Scheme.Modules.pullback σ).mapIso α.symm ≪≫ β, ?_⟩
    simp [← pullbackQuotientMap_comp_map_of_univ_comp D₁ D₂ α hα σ hσ, hβ]
  · refine ⟨(Scheme.Modules.pullback σ).mapIso α ≪≫ β, ?_⟩
    simp [← hβ, ← pullbackQuotientMap_comp_map_of_univ_comp D₁ D₂ α hα σ hσ]

/-- **Universality depends on a tautological datum only up to isomorphism over the universal
quotients.** -/
theorem isUniversal_of_univ_comp (D₁ D₂ : TautologicalDatum X F) [D₁.IsUniversal]
    (α : D₁.twist ≅ D₂.twist) (hα : D₁.univ ≫ α.hom = D₂.univ) : D₂.IsUniversal where
  exists_classifies Q := by
    obtain ⟨σ, hσ, h⟩ := IsUniversal.exists_classifies (D := D₁) Q
    exact ⟨σ, hσ, (classifies_iff_of_univ_comp D₁ D₂ α hα σ hσ Q).1 h⟩
  eq_of_classifies σ σ' hσ hσ' Q h h' :=
    IsUniversal.eq_of_classifies (D := D₁) σ σ' hσ hσ' Q
      ((classifies_iff_of_univ_comp D₁ D₂ α hα σ hσ Q).2 h)
      ((classifies_iff_of_univ_comp D₁ D₂ α hα σ' hσ' Q).2 h')

end TautologicalDatum

/-- **The canonical tautological datum is universal over every test scheme**: its base change
along any `f : T ⟶ X` is identified with the canonical datum of `𝐏(F')`, which is universal. -/
instance isUniversalOver_tautologicalDatum {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] :
    (tautologicalDatum F).IsUniversalOver where
  isUniversal_baseChange f F' _ hF :=
    TautologicalDatum.isUniversal_of_univ_comp (tautologicalDatum F')
      ((tautologicalDatum F).baseChange f F F' hF)
      (tautologicalDatumTwistBaseChangeIso f F F' hF).symm
      ((Iso.comp_inv_eq _).2
        (tautologicalDatum_baseChange_univ_comp_tautologicalDatumTwistBaseChangeIso_hom
          f F F' hF).symm)

namespace TautologicalDatum

variable {X : Scheme.{u}} {F : X.Modules} [F.IsQuasicoherent] {T : Scheme.{u}} {f : T ⟶ X}
  (F' : T.Modules) [F'.IsQuasicoherent] (hF : F' ≅ (Scheme.Modules.pullback f).obj F)

/-- The inverse of the canonical identification `b^*π^*F ≅ π'^*F'`, written out. -/
theorem tautologicalBaseChangeIso_inv_eq :
    (tautologicalBaseChangeIso f F F' hF).inv =
      (Scheme.Modules.pullback (projectiveBundleToBase T F')).map hF.hom ≫
        (Scheme.Modules.pullbackComp (projectiveBundleToBase T F') f).hom.app F ≫
        (Scheme.Modules.pullbackCongr
          (projectiveBundleBaseChange_comp_projectiveBundleToBase f F F' hF)).inv.app F ≫
        (Scheme.Modules.pullbackComp (projectiveBundleBaseChange f F F' hF)
          (projectiveBundleToBase X F)).inv.app F := by
  simp [tautologicalBaseChangeIso]

/-- **The quotient a morphism over the base pulls back is the one its section pulls back from the
base-changed datum.** For `h : T ⟶ 𝐏(F)` over `f` and `σ : T ⟶ 𝐏(F')` the section it corresponds
to, the invertible quotient `σ^*` of the base-changed tautological datum is `h^*𝒪(1)` with the
pulled-back tautological quotient. -/
theorem pullbackQuotient_overMorphismEquivSection_isEquivalent (D : TautologicalDatum X F)
    (h : T ⟶ projectiveBundle X F) (hh : h ≫ projectiveBundleToBase X F = f) :
    ((D.baseChange f F F' hF).pullbackQuotient (overMorphismEquivSection F' hF ⟨h, hh⟩).1
      (overMorphismEquivSection F' hF ⟨h, hh⟩).2).IsEquivalent (D.overQuotient F' hF h hh) := by
  set σ := (overMorphismEquivSection F' hF ⟨h, hh⟩).1 with hσdef
  have hσ : σ ≫ projectiveBundleToBase T F' = 𝟙 T :=
    (overMorphismEquivSection F' hF ⟨h, hh⟩).2
  have hσb : σ ≫ projectiveBundleBaseChange f F F' hF = h :=
    (isPullback_projectiveBundleBaseChange f F F' hF).lift_fst _ _ _
  refine ⟨(Scheme.Modules.pullbackComp σ (projectiveBundleBaseChange f F F' hF)).app D.twist ≪≫
    (Scheme.Modules.pullbackCongr hσb).app D.twist, ?_⟩
  have coh := Stacks.Modules.sectionOfBaseChange_coherence f (projectiveBundleToBase X F)
    (projectiveBundleToBase T F') (projectiveBundleBaseChange f F F' hF)
    (projectiveBundleBaseChange_comp_projectiveBundleToBase f F F' hF) h hh σ hσ hσb F
  have n₁ := (Scheme.Modules.pullbackComp σ (projectiveBundleToBase T F')).inv.naturality hF.hom
  have n₂ := (Scheme.Modules.pullbackCongr hσ).inv.naturality hF.hom
  have n₃ := (Scheme.Modules.pullbackId T).inv.naturality hF.hom
  have n₄ := ((Scheme.Modules.pullbackComp σ (projectiveBundleBaseChange f F F' hF)).hom ≫
    (Scheme.Modules.pullbackCongr hσb).hom).naturality D.univ
  simp only [Functor.comp_map, Functor.id_map, NatTrans.comp_app, Category.assoc] at n₁ n₂ n₃ n₄
  show ((Scheme.Modules.pullbackId T).inv.app F' ≫
      (Scheme.Modules.pullbackCongr hσ).inv.app F' ≫
      (Scheme.Modules.pullbackComp σ (projectiveBundleToBase T F')).inv.app F' ≫
      (Scheme.Modules.pullback σ).map ((tautologicalBaseChangeIso f F F' hF).inv ≫
        (Scheme.Modules.pullback (projectiveBundleBaseChange f F F' hF)).map D.univ)) ≫
      ((Scheme.Modules.pullbackComp σ (projectiveBundleBaseChange f F F' hF)).hom.app D.twist ≫
        (Scheme.Modules.pullbackCongr hσb).hom.app D.twist) =
    hF.hom ≫ (Scheme.Modules.pullbackCongr hh).inv.app F ≫
      (Scheme.Modules.pullbackComp h (projectiveBundleToBase X F)).inv.app F ≫
      (Scheme.Modules.pullback h).map D.univ
  rw [tautologicalBaseChangeIso_inv_eq]
  simp only [Functor.map_comp, Category.assoc]
  rw [n₄, ← reassoc_of% n₁, ← reassoc_of% n₂, ← reassoc_of% n₃, reassoc_of% coh]

/-- **Tag 01O4's mapping-in bijection on a morphism**: it sends `h : T ⟶ 𝐏(F)` over `f` to the
class of the invertible quotient `h^*𝒪(1)` of `F'` that `h` pulls back. -/
theorem overMorphismEquivInvertibleQuotients_apply (D : TautologicalDatum X F) [D.IsUniversalOver]
    (h : T ⟶ projectiveBundle X F) (hh : h ≫ projectiveBundleToBase X F = f) :
    D.overMorphismEquivInvertibleQuotients F' hF ⟨h, hh⟩ =
      Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid T F') (D.overQuotient F' hF h hh) :=
  Quotient.sound (D.pullbackQuotient_overMorphismEquivSection_isEquivalent F' hF h hh)

/-- **Two morphisms over the base pulling back equivalent quotients are equal.** -/
theorem eq_of_overQuotient_isEquivalent (D : TautologicalDatum X F) [D.IsUniversalOver]
    (h₁ h₂ : T ⟶ projectiveBundle X F) (hh₁ : h₁ ≫ projectiveBundleToBase X F = f)
    (hh₂ : h₂ ≫ projectiveBundleToBase X F = f)
    (he : (D.overQuotient F' hF h₁ hh₁).IsEquivalent (D.overQuotient F' hF h₂ hh₂)) :
    h₁ = h₂ :=
  congrArg Subtype.val (D.eq_of_overMorphismEquivInvertibleQuotients_eq F' hF ⟨h₁, hh₁⟩ ⟨h₂, hh₂⟩
    (by rw [overMorphismEquivInvertibleQuotients_apply, overMorphismEquivInvertibleQuotients_apply];
        exact Quotient.sound he))

/-- **The morphism over the base classified by a quotient pulls back that quotient.** -/
theorem overQuotient_classifyingMorphismOver_isEquivalent (D : TautologicalDatum X F)
    [D.IsUniversalOver] (Q : Stacks.Divisors.InvertibleQuotient T F') :
    (D.overQuotient F' hF (D.classifyingMorphismOver F' hF Q).1
      (D.classifyingMorphismOver F' hF Q).2).IsEquivalent Q := by
  have h := D.overMorphismEquivInvertibleQuotients_classifyingMorphismOver F' hF Q
  rw [show D.classifyingMorphismOver F' hF Q = ⟨(D.classifyingMorphismOver F' hF Q).1,
    (D.classifyingMorphismOver F' hF Q).2⟩ from rfl, overMorphismEquivInvertibleQuotients_apply]
    at h
  exact Quotient.exact h

end TautologicalDatum

end Stacks.RelativeProj

end
