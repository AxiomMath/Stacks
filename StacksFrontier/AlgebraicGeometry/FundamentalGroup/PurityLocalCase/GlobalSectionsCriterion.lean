module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine
import StacksFrontier.RingTheory.Depth.RingEquiv

/-!
# Extending a finite étale cover of a punctured spectrum over the whole spectrum

Let `A` be a Noetherian local ring of depth at least two and let `V` be finite étale over the
punctured spectrum `U = Spec A ∖ {𝔪}`. Then `V` is the restriction of a finite étale scheme over
`Spec A` exactly when the ring `Γ(V, ⊤)` of global sections of `V` is finite étale over `A`.

One direction is a construction: if `Γ(V, ⊤)` is finite étale over `A` then `Spec Γ(V, ⊤)` is
the extension, because depth at least two makes `Γ(U, 𝒪_U) = A`, so `U` is already the punctured
spectrum of its own ring of sections and `V ⟶ U` is affine. The other direction says that an
extension `Y ⟶ Spec A` cannot change the global sections: `Y` is affine, `V` is the open
subscheme of `Y` over `U`, and depth at least two at every closed point of `Y` forces the
restriction `Γ(Y, ⊤) ⟶ Γ(V, ⊤)` to be an isomorphism.

## Main results

* `AlgebraicGeometry.exists_finiteEtale_extension_iff_globalSections_finiteEtale` — the
  equivalence above.

## Implementation notes

The depth hypothesis is `2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A`. Transporting it to
the closed points of a scheme finite flat over `Spec A` uses
`Module.depth_self_eq_of_ringEquiv` at the closed point of `Spec A` and the depth inequality
along a flat local homomorphism; from there the identification of `Y` with the spectrum of its
sections over the punctured part is
`AlgebraicGeometry.exists_iso_spec_sections_punctured_spectrum`.

That `V` is the base change of `Y` is expressed by a cartesian square whose top map is the given
structure morphism of `V`, and the `A`-algebra structure on `Γ(V, ⊤)` is the one induced by
`V ⟶ Spec A` through the canonical identification of `A` with the global sections of `Spec A`.

## References

* [Stacks Project, Tag 0BLK](https://stacks.math.columbia.edu/tag/0BLK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace

universe u

namespace AlgebraicGeometry

private lemma toSpecΓ_comp_baseMap
    (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) :
    X.toSpecΓ ≫
      Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop) = f := by
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality f,
    Category.assoc]
  simp [toSpecΓ_SpecMap_ΓSpecIso_inv]

private lemma affineCover_isPullback_of_globalSectionsIso
    (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens)
    (hqc : CompactSpace U.toScheme) (V : Scheme.{u}) (π : V ⟶ U.toScheme) [IsAffineHom π]
    [IsIso (Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫
      U.ι.appTop))] :
    IsPullback π V.toSpecΓ U.ι
      (Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫
        (π ≫ U.ι).appTop)) := by
  let e := (Scheme.ΓSpecIso (.of A)).inv ≫ U.ι.appTop
  have := hqc
  have : U.toScheme.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion U.ι
  apply (Scheme.isPullback_toSpecΓ_toSpecΓ π).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso (Spec.map e))
  · simp
  · simp
  · simpa [e] using toSpecΓ_comp_baseMap A U.ι
  · simp only [asIso_hom, Iso.refl_hom, Category.id_comp]
    rw [← Spec.map_comp]
    congr 1

private lemma exists_extension_of_sections_finiteEtale
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (V : Scheme.{u}) (π : V ⟶ (Stacks.Divisors.puncturedSpectrum A).toScheme)
    [IsFinite π]
    [IsIso (Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫
      (Stacks.Divisors.puncturedSpectrum A).ι.appTop))]
    (h : letI : Algebra A Γ(V, ⊤) :=
      ((Scheme.ΓSpecIso (.of A)).inv ≫
        (π ≫ (Stacks.Divisors.puncturedSpectrum A).ι).appTop).hom.toAlgebra
      Module.Finite A Γ(V, ⊤) ∧ Algebra.Etale A Γ(V, ⊤)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)) (g : V ⟶ Y),
      IsFinite f ∧ Etale f ∧
        IsPullback π g (Stacks.Divisors.puncturedSpectrum A).ι f := by
  let : Algebra A Γ(V, ⊤) :=
    ((Scheme.ΓSpecIso (.of A)).inv ≫
      (π ≫ (Stacks.Divisors.puncturedSpectrum A).ι).appTop).hom.toAlgebra
  exact ⟨Spec Γ(V, ⊤), Spec.map (CommRingCat.ofHom (algebraMap A Γ(V, ⊤))), V.toSpecΓ,
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.mpr h.1),
    (AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @Etale)
      (Q := RingHom.Etale)).2 (RingHom.etale_algebraMap.mpr h.2),
    affineCover_isPullback_of_globalSectionsIso A _
      (@NoetherianSpace.compactSpace _ _
        (NoetherianSpace.set
          ((Stacks.Divisors.puncturedSpectrum A).1 : Set (PrimeSpectrum A)))) V π⟩

private noncomputable def localStalkEquiv
    (A : Type u) [CommRing A] [IsLocalRing A] :
    A ≃+* (Spec (.of A)).presheaf.stalk (IsLocalRing.closedPoint A) :=
  ((IsLocalization.atUnits A (IsLocalRing.maximalIdeal A).primeCompl
    (S := Localization.AtPrime (IsLocalRing.maximalIdeal A))
      (fun _ hx => IsLocalRing.notMem_maximalIdeal.mp hx)).toRingEquiv).trans
    (Spec.stalkIso (.of A) (IsLocalRing.closedPoint A)).commRingCatIsoToRingEquiv.symm

private lemma spec_depth_at_closed_points
    (A : Type u) [CommRing A] [IsLocalRing A]
    {d : ℕ∞} (hdepth : d ≤ Module.depth A (IsLocalRing.maximalIdeal A) A) :
    ∀ y : Spec (.of A), IsClosed ({y} : Set (Spec (.of A))) →
      d ≤ Module.depth ((Spec (.of A)).presheaf.stalk y)
        (IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk y))
        ((Spec (.of A)).presheaf.stalk y) := by
  intro y hy
  obtain rfl : y = IsLocalRing.closedPoint A :=
    PrimeSpectrum.ext ((IsLocalRing.isMaximal_iff (R := A)).mp
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hy))
  have := (Spec (.of A)).isLocalRing (IsLocalRing.closedPoint A)
  exact hdepth.trans (Module.depth_self_eq_of_ringEquiv (localStalkEquiv A)).le

private lemma depth_le_stalk_of_flat
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : Y ⟶ X) [Flat f] (y : Y) {d : ℕ∞}
    (hdepth : d ≤ Module.depth (X.presheaf.stalk (f y))
      (IsLocalRing.maximalIdeal (X.presheaf.stalk (f y)))
      (X.presheaf.stalk (f y))) :
    d ≤ Module.depth (Y.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (Y.presheaf.stalk y) := by
  let : Algebra (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
    (f.stalkMap y).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
    Flat.stalkMap f y
  have : IsLocalHom (algebraMap (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
  rw [Module.depth_self_eq_depth_self_add_depth_quotient_map_maximalIdeal
    (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)]
  exact hdepth.trans (le_add_right le_rfl)

private lemma depth_at_closed_point_of_finiteFlat
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsFinite f] [Flat f]
    {d : ℕ∞} (hdepth : d ≤ Module.depth A (IsLocalRing.maximalIdeal A) A)
    (y : Y) (hy : IsClosed ({y} : Set Y)) :
    d ≤ Module.depth (Y.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (Y.presheaf.stalk y) := by
  have hclosed : IsClosed ({f y} : Set (Spec (.of A))) := by
    simpa only [Set.image_singleton] using (Scheme.Hom.isClosedMap f) {y} hy
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  exact depth_le_stalk_of_flat f y
    (spec_depth_at_closed_points A hdepth (f y) hclosed)

private lemma open_appTop_topIso
    (X : Scheme.{u}) (U : X.Opens) :
    U.ι.appTop ≫ U.topIso.hom =
      X.presheaf.map (homOfLE le_top).op := by
  let f : (Opposite.op (⊤ : X.Opens)) ⟶
      Opposite.op (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) :=
    (homOfLE le_top).op
  let g : Opposite.op (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) ⟶ Opposite.op U :=
    (eqToHom U.ι_image_top.symm).op
  have hfg : f ≫ g = (homOfLE le_top).op := Subsingleton.elim _ _
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← hfg]
  convert (X.presheaf.map_comp f g).symm using 1
  congr 1

private lemma sections_appTop_isIso
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsFinite f] [Flat f]
    (hdepth : 2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A) :
    IsIso (f ⁻¹ᵁ (Stacks.Divisors.puncturedSpectrum A)).ι.appTop := by
  have : IsAffine Y := isAffine_of_isAffineHom f
  obtain ⟨e, he⟩ := exists_iso_spec_sections_punctured_spectrum
    A f (depth_at_closed_point_of_finiteFlat A f hdepth)
  let r := Y.presheaf.map
    (homOfLE (show f ⁻¹ᵁ (Stacks.Divisors.puncturedSpectrum A) ≤ ⊤ from le_top)).op
  have hr : IsIso (Spec.map r) :=
    @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ e.isIso_hom
      (IsAffine.affine : IsIso Y.toSpecΓ) he
  exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _
    (f ⁻¹ᵁ (Stacks.Divisors.puncturedSpectrum A)).topIso.isIso_hom
    ((ConcreteCategory.isIso_iff_bijective r).2 (isIso_SpecMap_iff.1 hr))
    (open_appTop_topIso _ _)

private lemma extension_appTop_isIso
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (V : Scheme.{u}) (π : V ⟶ (Stacks.Divisors.puncturedSpectrum A).toScheme)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) (g : V ⟶ Y)
    [IsFinite f] [Flat f]
    (hp : IsPullback π g (Stacks.Divisors.puncturedSpectrum A).ι f)
    (hdepth : 2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A) :
    IsIso g.appTop := by
  let U := Stacks.Divisors.puncturedSpectrum A
  let W := f ⁻¹ᵁ U
  have hW : IsIso W.ι.appTop := sections_appTop_isIso A f hdepth
  let e : V ≅ W.toScheme :=
    hp.isoPullback ≪≫ pullbackSymmetry U.ι f ≪≫ pullbackRestrictIsoRestrict f U
  have heg : e.hom ≫ W.ι = g := by
    change ((hp.isoPullback.hom ≫ (pullbackSymmetry U.ι f).hom) ≫
      (pullbackRestrictIsoRestrict f U).hom) ≫ W.ι = g
    rw [Category.assoc, pullbackRestrictIsoRestrict_hom_ι,
      Category.assoc, pullbackSymmetry_hom_comp_fst, hp.isoPullback_hom_snd]
  have heapp : IsIso e.hom.appTop :=
    @Scheme.Hom.instIsIsoCommRingCatApp _ _ e.hom e.isIso_hom ⊤
  simpa only [← Scheme.Hom.comp_appTop, heg] using
    (IsIso.comp_isIso' hW heapp : IsIso (W.ι.appTop ≫ e.hom.appTop))

private lemma sections_finiteEtale_of_extension
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (V : Scheme.{u}) (π : V ⟶ (Stacks.Divisors.puncturedSpectrum A).toScheme)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) (g : V ⟶ Y)
    [IsFinite f] [Etale f]
    (hp : IsPullback π g (Stacks.Divisors.puncturedSpectrum A).ι f)
    (hdepth : 2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A) :
    letI : Algebra A Γ(V, ⊤) :=
      ((Scheme.ΓSpecIso (.of A)).inv ≫
        (π ≫ (Stacks.Divisors.puncturedSpectrum A).ι).appTop).hom.toAlgebra
    Module.Finite A Γ(V, ⊤) ∧ Algebra.Etale A Γ(V, ⊤) := by
  have : IsAffine Y := isAffine_of_isAffineHom f
  let a := (Scheme.ΓSpecIso (.of A)).inv
  let b := f.appTop
  let c := g.appTop
  have haBij := (ConcreteCategory.isIso_iff_bijective a).1 inferInstance
  have hcBij :=
    (ConcreteCategory.isIso_iff_bijective c).1 (extension_appTop_isIso A V π f g hp hdepth)
  have hmap : (π ≫ (Stacks.Divisors.puncturedSpectrum A).ι).appTop = b ≫ c := by
    rw [hp.w, Scheme.Hom.comp_appTop]
  let h := a ≫ (π ≫ (Stacks.Divisors.puncturedSpectrum A).ι).appTop
  have hcomp : h = (a ≫ b) ≫ c := by simp only [h, hmap, Category.assoc]
  have hFin : h.hom.Finite := hcomp.symm ▸
    RingHom.Finite.comp (RingHom.Finite.of_surjective _ hcBij.2)
      (RingHom.Finite.comp (Scheme.Hom.finite_appTop f) (RingHom.Finite.of_surjective _ haBij.2))
  have hEt : h.hom.Etale := hcomp.symm ▸
    RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective haBij)
        (HasRingHomProperty.appTop (P := @Etale) f ‹Etale f›)) (RingHom.Etale.of_bijective hcBij)
  let : Algebra A Γ(V, ⊤) := h.hom.toAlgebra
  exact ⟨RingHom.finite_algebraMap.mp hFin, RingHom.etale_algebraMap.mp hEt⟩

private lemma puncturedSpectrum_baseMap_isIso
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : 2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A) :
    IsIso (Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫
      (Stacks.Divisors.puncturedSpectrum A).ι.appTop)) := by
  let U := Stacks.Divisors.puncturedSpectrum A
  have happ : IsIso U.ι.appTop := by
    have h := sections_appTop_isIso A (𝟙 _) hdepth
    simp only [Scheme.Hom.id_preimage] at h
    exact h
  have : IsIso ((Scheme.ΓSpecIso (.of A)).inv ≫ U.ι.appTop) :=
    IsIso.comp_isIso' inferInstance happ
  infer_instance

/-- **Stacks Project, Tag 0BLK.** For a Noetherian local ring of depth at least two, a finite
étale scheme over the punctured spectrum extends to a finite étale scheme over the whole
spectrum if and only if its ring of global sections is finite étale over the ring. -/
@[stacks 0BLK]
lemma exists_finiteEtale_extension_iff_globalSections_finiteEtale
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (V : Scheme.{u}) (π : V ⟶ (Stacks.Divisors.puncturedSpectrum A).toScheme)
    [IsFinite π] [Etale π]
    (hdepth : 2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A) :
    (∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)) (g : V ⟶ Y),
      IsFinite f ∧ Etale f ∧ IsPullback π g (Stacks.Divisors.puncturedSpectrum A).ι f) ↔
      letI : Algebra A Γ(V, ⊤) :=
        ((Scheme.ΓSpecIso (.of A)).inv ≫
          (π ≫ (Stacks.Divisors.puncturedSpectrum A).ι).appTop).hom.toAlgebra
      Module.Finite A Γ(V, ⊤) ∧ Algebra.Etale A Γ(V, ⊤) := by
  have := puncturedSpectrum_baseMap_isIso A hdepth
  exact ⟨fun ⟨Y, f, g, _, _, hp⟩ ↦ sections_finiteEtale_of_extension A V π f g hp hdepth,
    exists_extension_of_sections_finiteEtale A V π⟩

end AlgebraicGeometry

end
