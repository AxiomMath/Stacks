module

public import StacksFrontier.AlgebraicGeometry.CompactOpenLocalization.Basic
public import StacksFrontier.AlgebraicGeometry.FibreProductSystem.Basic

/-!
# The stage at which the fibre products of a quasi-compact open give an open immersion

Let `A` be an affine open of a scheme `X`, say `A = Spec B` with `B = Γ(X, A)`, let `W ≤ A` be
a quasi-compact open, and suppose `R = Γ(X, W)` is presented as the filtered colimit of a
diagram `F` of rings, with `s : B ⟶ R` the restriction map.  Forming the fibre products
`B_j = B ×_R F.obj j` gives, at a single stage `j`, a finite family of standard opens of
`Spec (F.obj j)` which maps by an open immersion to `Spec B_j`.

## Main results

* `Localization.bijective_awayMap_comp_ringEquiv`: bijectivity of the canonical map on
  localizations away from an element is unchanged by composing with a ring isomorphism on the
  target.
* `RingFibreProduct.exists_stage_isOpenImmersion_iSup_basicOpen`: the open immersion, at a
  single stage, for the fibre products over a presentation of `Γ(X, W)` as a filtered colimit.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
* [Stacks Project, Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

/-- **Bijectivity of the map on localizations away from an element is insensitive to a ring
isomorphism on the target.**  For `s : B →+* R` and `e : R ≃+* R'`, the canonical map
`B_g → R'_{e (s g)}` is bijective exactly when `B_g → R_{s g}` is. -/
theorem Localization.bijective_awayMap_comp_ringEquiv {B R R' : Type u} [CommRing B]
    [CommRing R] [CommRing R'] (s : B →+* R) (e : R ≃+* R') (g : B) :
    Function.Bijective (Localization.awayMap ((e : R →+* R').comp s) g) ↔
      Function.Bijective (Localization.awayMap s g) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [Localization.awayMap_injective_iff]
      intro a ha
      refine (Localization.awayMap_injective_iff.mp h.1) a ?_
      rw [RingHom.comp_apply, ha, map_zero]
    · rw [Localization.awayMap_surjective_iff]
      intro a
      obtain ⟨b, m, hb⟩ := (Localization.awayMap_surjective_iff.mp h.2) (e a)
      refine ⟨b, m, e.injective ?_⟩
      rwa [map_mul, map_pow]
  · intro h
    refine ⟨?_, ?_⟩
    · rw [Localization.awayMap_injective_iff]
      intro a ha
      refine (Localization.awayMap_injective_iff.mp h.1) a ?_
      rw [RingHom.comp_apply] at ha
      exact (map_eq_zero_iff _ e.injective).mp ha
    · rw [Localization.awayMap_surjective_iff]
      intro a
      obtain ⟨b, m, hb⟩ := (Localization.awayMap_surjective_iff.mp h.2) (e.symm a)
      exact ⟨b, m, by simp [hb]⟩

namespace RingFibreProduct

open AlgebraicGeometry

/-- **The fibre products over a filtered colimit presentation of the sections of a
quasi-compact open give an open immersion at a single stage.**

Let `W` be a quasi-compact open of an affine open `A` of a scheme `X`, and present
`Γ(X, W)` as the filtered colimit of a diagram `F` of rings: `e` identifies the colimit point
with `Γ(X, W)`, and `s` is the restriction map `Γ(X, A) ⟶ Γ(X, W)` read through that
identification.  Then at a single stage `j` there are finitely many elements `f_l` of `F.obj j`
whose images in `Γ(X, W)` are the restrictions of sections `g_l` of `A` with
`D(g_l) ⊆ W` covering `W`, and the union of the standard opens `D(f_l)` maps by an open
immersion to the spectrum of the fibre product `Γ(X, A) ×_{Γ(X, W)} F.obj j`.

Moreover `c.ι.app j (f l) = s (g l)` for each `l`, and each `Localization.awayMap s (g l)` is
bijective. -/
theorem exists_stage_isOpenImmersion_iSup_basicOpen {X : Scheme.{u}} {A W : X.Opens}
    (hA : IsAffineOpen A) (hW : IsCompact (W : Set X)) (hWA : W ≤ A)
    {K : Type u} [Category.{u} K] [IsFiltered K] {F : K ⥤ CommRingCat.{u}} (c : Cocone F)
    (hc : IsColimit c) (s : X.presheaf.obj (op A) ⟶ c.pt)
    (e : c.pt ⟶ X.presheaf.obj (op W)) (he : Function.Bijective e.hom)
    (hse : s ≫ e = X.presheaf.map (homOfLE hWA).op) :
    ∃ (n : ℕ) (g : Fin n → Γ(X, A)) (j : K) (f : Fin n → F.obj j),
      (∀ l, X.basicOpen (g l) ≤ W) ∧ W = ⨆ l, X.basicOpen (g l) ∧
        (∀ l, e (c.ι.app j (f l)) = (X.presheaf.map (homOfLE hWA).op) (g l)) ∧
        (∀ l, c.ι.app j (f l) = s (g l)) ∧
        (∀ l, Function.Bijective (Localization.awayMap s.hom (g l))) ∧
        IsOpenImmersion
          ((⨆ l, PrimeSpectrum.basicOpen (f l) : (Spec (F.obj j)).Opens).ι ≫
            Spec.map ((fibreProductSystemSnd c s).app j)) := by
  obtain ⟨n, g, hgle, hgcov, hgloc⟩ := hA.exists_basicOpen_cover_bijective_awayMap hW hWA
  have hcomp : ((RingEquiv.ofBijective e.hom he : c.pt →+* Γ(X, W)).comp s.hom) =
      (X.presheaf.map (homOfLE hWA).op).hom := by
    ext a
    change e (s a) = _
    rw [← CommRingCat.comp_apply, hse]
  have hloc : ∀ l, Function.Bijective (Localization.awayMap s.hom (g l)) := fun l =>
    (Localization.bijective_awayMap_comp_ringEquiv s.hom
        (RingEquiv.ofBijective e.hom he) (g l)).mp (by rw [hcomp]; exact hgloc l)
  obtain ⟨j, f, hf⟩ := exists_stage_lift_of_isColimit c hc (fun l => s (g l))
  refine ⟨n, g, j, f, hgle, hgcov, fun l => ?_, hf, hloc,
    isOpenImmersion_iSup_basicOpen_comp_specMap_snd c s j f g hf hloc⟩
  rw [hf l, ← CommRingCat.comp_apply, hse]

end RingFibreProduct

end
