module

public import StacksFrontier.AlgebraicGeometry.Perfect.GeomReducedFibre.SpecCase
public import StacksFrontier.AlgebraicGeometry.Perfect.GeomReducedFibre.ModelTransfer

/-!
# Reduction of [Stacks, Tag 0G7Y] to an affine base

The affine case `exists_away_splitting_and_finiteEtale` is stated for a morphism to `Spec R`
whose fibre over a prime `p` is geometrically reduced in the sense of
`FibreGeometricallyReducedAt`. This file supplies the passage from an arbitrary base:

* `fibreGeometricallyReducedAt_of_isPullback`: if the fibre `X_s` of `f : X ⟶ S` is
  geometrically reduced and `Spec R ⟶ S` sends `p` to `s`, then the base change of `f` to
  `Spec R` satisfies `FibreGeometricallyReducedAt` at `p`;
* the finite etaleness of `Γ(S, V) → Γ(X, f⁻¹V)` for all affine opens `V` inside an affine open
  on which it is known, the locality of finite etale ring maps on the base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace StacksDraft.Perfect.GeomReducedFibre

/-- **A geometrically reduced fibre gives `FibreGeometricallyReducedAt` after base change.** -/
theorem fibreGeometricallyReducedAt_of_isPullback {X S Y : Scheme.{u}} (f : X ⟶ S) (s : S)
    [hgr : GeometricallyReduced (f.fiberToSpecResidueField s)] {R : Type u} [CommRing R]
    (φ : Spec (.of R) ⟶ S) {g : Y ⟶ Spec (.of R)} {q : Y ⟶ X} (hsq : IsPullback q g f φ)
    (p : Ideal R) [p.IsPrime] (hp : φ (⟨p, ‹_›⟩ : PrimeSpectrum R) = s) :
    FibreGeometricallyReducedAt g p := by
  intro K _ ψ hψ Z a b hZ
  let y : Spec (.of K) ⟶ S := Spec.map (CommRingCat.ofHom ψ) ≫ φ
  have hy : y (IsLocalRing.closedPoint K) = s := by
    refine Eq.trans ?_ hp
    show φ ((Spec.map (CommRingCat.ofHom ψ)) (IsLocalRing.closedPoint K)) = _
    congr 1
    refine PrimeSpectrum.ext ?_
    show Ideal.comap ψ (IsLocalRing.maximalIdeal K) = p
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, hψ]
  have key : ∀ (x : S) (_ : x = s) (ι : S.residueField x ⟶ .of K),
      Spec.map ι ≫ S.fromSpecResidueField x = y →
        ∃ ι' : S.residueField s ⟶ .of K, Spec.map ι' ≫ S.fromSpecResidueField s = y := by
    rintro x rfl ι h
    exact ⟨ι, h⟩
  obtain ⟨ι, hι⟩ := key _ hy _
    (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S y)
  have hout := hZ.paste_horiz hsq
  change IsPullback (a ≫ q) b f y at hout
  rw [← hι] at hout
  have hF := IsPullback.of_hasPullback f (S.fromSpecResidueField s)
  let a' : Z ⟶ f.fiber s := hF.lift (a ≫ q) (b ≫ Spec.map ι)
    (hout.w.trans (Category.assoc _ _ _).symm)
  exact hgr.geometrically_isReduced (Spec.map ι) a' b <|
    .of_right (h₁₂ := pullback.fst f (S.fromSpecResidueField s)) (by rwa [hF.lift_fst])
      (hF.lift_snd _ _ _) hF

section Locality

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]

/-- On a basic open of an affine open of the base, the map on sections is the localization of the
map on the affine open; the source of `f` need not be affine, only `f` quasi-compact and
quasi-separated. -/
theorem appLE_basicOpen_eq_away_map {V : S.Opens} (hV : IsAffineOpen V) (t : Γ(S, V)) :
    letI := hV.isLocalization_basicOpen t
    letI := isLocalization_basicOpen_of_qcqs (f.isCompact_preimage hV.isCompact)
      (f.isQuasiSeparated_preimage hV.isQuasiSeparated) (f.app V t)
    f.appLE (S.basicOpen t) (X.basicOpen (f.app V t)) (by rw [Scheme.preimage_basicOpen]) =
      CommRingCat.ofHom (IsLocalization.Away.map _ _ (f.app V).hom t) := by
  let := hV.isLocalization_basicOpen t
  let := isLocalization_basicOpen_of_qcqs (f.isCompact_preimage hV.isCompact)
    (f.isQuasiSeparated_preimage hV.isQuasiSeparated) (f.app V t)
  ext : 1
  apply IsLocalization.ringHom_ext (.powers t)
  rw [IsLocalization.Away.map, CommRingCat.hom_ofHom, IsLocalization.map_comp,
    RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]
  rfl

variable {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

include P in
/-- The property on the basic open from the property of the localization. -/
theorem app_basicOpen_iff_away_map (hP : RingHom.RespectsIso @P) {V : S.Opens}
    (hV : IsAffineOpen V) (t : Γ(S, V)) :
    P (f.app (S.basicOpen t)).hom ↔ P (Localization.awayMap (f.app V).hom t) := by
  let := hV.isLocalization_basicOpen t
  let := isLocalization_basicOpen_of_qcqs (f.isCompact_preimage hV.isCompact)
    (f.isQuasiSeparated_preimage hV.isQuasiSeparated) (f.app V t)
  rw [hP.isLocalization_away_iff Γ(S, S.basicOpen t) Γ(X, X.basicOpen (f.app V t)) (f.app V).hom t,
    ← CommRingCat.hom_ofHom (IsLocalization.Away.map _ _ (f.app V).hom t),
    ← appLE_basicOpen_eq_away_map f hV t, Scheme.Hom.app_eq_appLE]
  exact Scheme.Hom.appLE_congr _ _ rfl (Scheme.preimage_basicOpen f t) (fun φ => P φ.hom)

/-- **A local property of ring maps passes from an affine open to a basic open.** -/
theorem app_basicOpen_of_app (hP : RingHom.RespectsIso @P)
    (hP' : RingHom.LocalizationAwayPreserves @P) {V : S.Opens} (hV : IsAffineOpen V)
    (t : Γ(S, V)) (h : P (f.app V).hom) : P (f.app (S.basicOpen t)).hom := by
  rw [app_basicOpen_iff_away_map f hP hV t, hP.isLocalization_away_iff
    (Localization.Away t) (Localization.Away ((f.app V).hom t))]
  exact hP' (f.app V).hom t _ _ h

/-- **A local property of ring maps holds on an affine open if it holds on a cover by basic
opens.** -/
theorem app_of_app_basicOpen (hP : RingHom.RespectsIso @P)
    (hP'' : RingHom.OfLocalizationSpan @P) {V : S.Opens} (hV : IsAffineOpen V)
    (s : Set Γ(S, V)) (hs : Ideal.span s = ⊤) (h : ∀ t ∈ s, P (f.app (S.basicOpen t)).hom) :
    P (f.app V).hom :=
  hP'' (f.app V).hom s hs fun t => (app_basicOpen_iff_away_map f hP hV t.1).1 (h t.1 t.2)

/-- **A local property of ring maps passes from an affine open to every smaller affine open.** -/
theorem app_of_le (hP : RingHom.RespectsIso @P) (hP' : RingHom.LocalizationAwayPreserves @P)
    (hP'' : RingHom.OfLocalizationSpan @P) {U V : S.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hVU : V ≤ U) (h : P (f.app U).hom) : P (f.app V).hom := by
  choose a c hac hx using fun x : V => exists_basicOpen_le_affine_inter hU hV x.1 ⟨hVU x.2, x.2⟩
  refine app_of_app_basicOpen f hP hP'' hV (Set.range c) ?_ ?_
  · rw [← hV.self_le_iSup_basicOpen_iff]
    intro x hx'
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨⟨c ⟨x, hx'⟩, ⟨x, hx'⟩, rfl⟩, hac ⟨x, hx'⟩ ▸ hx ⟨x, hx'⟩⟩
  · rintro _ ⟨x, rfl⟩
    rw [← hac x]
    exact app_basicOpen_of_app f hP hP' hU (a x) h

end Locality

end StacksDraft.Perfect.GeomReducedFibre

end
