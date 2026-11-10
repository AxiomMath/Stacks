module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.LargestOpenEtaleSquare
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Local

/-!
# Étale locality of the property induced on germs

A property `P` of morphisms of schemes which is étale local on the source and target induces a
property of morphisms of germs: a morphism of germs has the induced property if one of its
representatives has `P`. The induced property is again étale local on the source and target.

## Main definitions

* `AlgebraicGeometry.MorphismOfGerms.HasRepresentativeWithProperty` is the property induced on
  morphisms of germs by a property of morphisms of schemes.

## Main results

* `AlgebraicGeometry.MorphismOfGerms.hasRepresentativeWithProperty_isEtaleLocalOnSourceAndTarget`:
  **Stacks 04R6**, the induced property is étale local on the source and target.

## Implementation notes

The existential quantifier ranges over representatives of the morphism of germs, with `P`
applied to the representative's morphism from its open neighbourhood to the whole target
scheme.

The proof goes through the largest open locus of Tag 0CEY: a representative has the induced
property exactly when the distinguished point of its source lies in the largest open locus of
its morphism, which is `hasRepresentativeWithProperty_iff_mem_largestOpen` below. Given an
étale square of germs, both horizontal representatives are compared with a common
representative of the composite, and Tag 0CEZ identifies the two loci at the distinguished
point.

## References

* [Stacks Project, Tag 04R6](https://stacks.math.columbia.edu/tag/04R6)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory

universe u

namespace MorphismOfGerms

/-- A morphism of germs has the property induced by `P` if some representative has `P`. -/
abbrev HasRepresentativeWithProperty (P : MorphismProperty Scheme.{u})
    {X Y : GermOfScheme.{u}} (f : MorphismOfGerms X Y) : Prop :=
  ∃ g : Representative X Y, mk g = f ∧ P g.hom

/-- A representative has the induced property exactly when the distinguished point of its
source lies in the largest open locus of its morphism. -/
private theorem hasRepresentativeWithProperty_iff_mem_largestOpen
    (P : MorphismProperty Scheme.{u})
    (hP : AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget P)
    {X Y : GermOfScheme.{u}} (f : Representative X Y) :
    HasRepresentativeWithProperty P (mk f) ↔
      (⟨X.point, f.mem_source⟩ : f.source.toScheme) ∈ largestOpen P f.hom := by
  have : P.IsLocalAtSource Scheme.etalePrecoverage :=
    AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.isLocalAtSource_etalePrecoverage P hP
  have G := largestOpen_isGreatest_etale P f.hom
  constructor
  · rintro ⟨g, hgf, hPg⟩
    obtain ⟨U, hxU, hUg, hUf, heq⟩ := mk_eq_mk_iff.mp hgf
    let L : f.source.toScheme.Opens := f.source.ι ⁻¹ᵁ U
    have hPfU : P (X.scheme.homOfLE hUf ≫ f.hom) := by
      rw [← heq]
      exact hP.precomp.precomp (X.scheme.homOfLE hUg) (by infer_instance) _ hPg
    let I : X.scheme.Opens := f.source.ι ''ᵁ L
    have hIU : I = U := by
      dsimp [I, L]
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr hUf]
    let e := Scheme.Hom.isoImage f.source.ι L
    have hPL : P (L.ι ≫ f.hom) := by
      have hIUle : I ≤ U := hIU.le
      have heqmap : (e.hom ≫ X.scheme.homOfLE hIUle) ≫ X.scheme.homOfLE hUf = L.ι := by
        apply (cancel_mono f.source.ι).1
        simp [e, Scheme.Hom.isoImage_hom_ι, Scheme.homOfLE_ι]
      rw [← heqmap]
      exact hP.precomp.precomp (e.hom ≫ X.scheme.homOfLE hIUle) (by infer_instance) _ hPfU
    exact G.2 hPL hxU
  · intro hx
    let L : f.source.toScheme.Opens := largestOpen P f.hom
    let I : X.scheme.Opens := f.source.ι ''ᵁ L
    have hIle : I ≤ f.source := f.source.ι_image_le L
    have hxI : X.point ∈ I := ⟨⟨X.point, f.mem_source⟩, hx, rfl⟩
    let e := Scheme.Hom.isoImage f.source.ι L
    have hPI : P (X.scheme.homOfLE hIle ≫ f.hom) := by
      have heqmap : e.inv ≫ L.ι = X.scheme.homOfLE hIle := by
        apply (cancel_mono f.source.ι).1
        simp [e, I, Scheme.homOfLE_ι]
      rw [← heqmap]
      exact hP.precomp.precomp e.inv (by infer_instance) _ G.1
    refine ⟨restrictRepresentative f I hxI hIle, mk_eq_mk_iff.mpr ⟨I, hxI, le_rfl, hIle, ?_⟩,
      hPI⟩
    simp [restrictRepresentative]

/-- Étale locality on the source and target of a property of morphisms of schemes passes to
the property it induces on morphisms of germs. -/
@[stacks 04R6]
theorem hasRepresentativeWithProperty_isEtaleLocalOnSourceAndTarget
    (P : MorphismProperty Scheme.{u})
    (hP : AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget P) :
    IsEtaleLocalOnSourceAndTarget (HasRepresentativeWithProperty P) :=
  ⟨by
    have hι : ∀ {X Y Z : GermOfScheme.{u}} (f : Representative X Y)
        (g : Representative Y Z),
        ((f.source.ι.isoImage (f.hom ⁻¹ᵁ g.source)).inv ≫ (f.hom ⁻¹ᵁ g.source).ι)
          ⟨X.point, (compRepresentative f g).mem_source⟩ = ⟨X.point, f.mem_source⟩ := by
      intro X Y Z f g
      rw [Scheme.Opens.isoImage_ι_inv_ι]
      exact Subtype.ext (by simp)
    have hrestrict : ∀ {X Y Z : GermOfScheme.{u}} (f : Representative X Y)
        (g : Representative Y Z),
        ((f.source.ι.isoImage (f.hom ⁻¹ᵁ g.source)).inv ≫ f.hom ∣_ g.source)
          ⟨X.point, (compRepresentative f g).mem_source⟩ = ⟨Y.point, g.mem_source⟩ := by
      intro X Y Z f g
      apply Subtype.ext
      change ((f.hom ∣_ g.source) ≫ g.source.ι) ((f.source.ι.isoImage (f.hom ⁻¹ᵁ g.source)).inv
        ⟨X.point, (compRepresentative f g).mem_source⟩) = Y.point
      rw [← f.map_point, morphismRestrict_ι]
      exact congrArg f.hom (hι f g)
    rintro U' U V' V a b h' h ⟨A, rfl, hAet⟩ ⟨B, rfl, hBet⟩ hsq
    obtain ⟨H', rfl⟩ := exists_rep h'
    obtain ⟨H, rfl⟩ := exists_rep h
    have : Etale A.hom := hAet
    obtain ⟨W, hxW, hWF, hWG, hagree⟩ := mk_eq_mk_iff.mp (by simpa only [comp_mk] using hsq :
      mk (compRepresentative H' B) = mk (compRepresentative A H))
    let α := compRepresentative A H
    let β := compRepresentative H' B
    let q₀ : α.source.toScheme ⟶ H.source.toScheme :=
      (A.source.ι.isoImage (A.hom ⁻¹ᵁ H.source)).inv ≫ A.hom ∣_ H.source
    let r₀ : β.source.toScheme ⟶ B.source.toScheme :=
      (H'.source.ι.isoImage (H'.hom ⁻¹ᵁ B.source)).inv ≫ H'.hom ∣_ B.source
    let s₀ : β.source.toScheme ⟶ H'.source.toScheme :=
      (H'.source.ι.isoImage (H'.hom ⁻¹ᵁ B.source)).inv ≫ (H'.hom ⁻¹ᵁ B.source).ι
    let q : W.toScheme ⟶ H.source.toScheme := U'.scheme.homOfLE hWG ≫ q₀
    let r : W.toScheme ⟶ B.source.toScheme := U'.scheme.homOfLE hWF ≫ r₀
    let s : W.toScheme ⟶ H'.source.toScheme := U'.scheme.homOfLE hWF ≫ s₀
    let x' : W.toScheme := ⟨U'.point, hxW⟩
    have : Etale q₀ := by dsimp [q₀, α, compRepresentative]; infer_instance
    have : Etale s₀ := by dsimp [s₀, β, compRepresentative]; infer_instance
    have hq : Etale q := by dsimp [q]; infer_instance
    have hs : Etale s := by dsimp [s]; infer_instance
    have hsq₂ : s ≫ H'.hom = r ≫ B.source.ι := by
      simp [s, s₀, r, r₀, β, compRepresentative, morphismRestrict_ι, Category.assoc]
    let pα : α.source.toScheme := ⟨U'.point, α.mem_source⟩
    let pβ : β.source.toScheme := ⟨U'.point, β.mem_source⟩
    have hq₀point : q₀ pα = ⟨U.point, H.mem_source⟩ := hrestrict A H
    have hs₀point : s₀ pβ = ⟨U'.point, H'.mem_source⟩ := hι H' B
    have hWpoint : ∀ {V : U'.scheme.Opens} (h : W ≤ V) (hV : U'.point ∈ V),
        U'.scheme.homOfLE h x' = ⟨U'.point, hV⟩ := fun h _ => Scheme.homOfLE_apply' h _ hxW
    have hqpoint : q x' = ⟨U.point, H.mem_source⟩ := by
      simpa only [q, Scheme.Hom.comp_apply, hWpoint hWG α.mem_source] using hq₀point
    have hspoint : s.base x' = ⟨U'.point, H'.mem_source⟩ := by
      simpa only [s, Scheme.Hom.comp_apply, hWpoint hWF β.mem_source] using hs₀point
    have hmem₁ := mem_largestOpen_iff_of_etaleAt P hP H.hom r B.hom q hagree.symm x'
      ((etale_iff_forall_etaleAt q).mp hq x')
      ((etale_iff_forall_etaleAt B.hom).mp hBet (r.base x'))
    have hmem₂ := mem_largestOpen_iff_of_etaleAt P hP H'.hom r B.source.ι s hsq₂ x'
      ((etale_iff_forall_etaleAt s).mp hs x')
      ((etale_iff_forall_etaleAt B.source.ι).mp inferInstance (r.base x'))
    rw [hasRepresentativeWithProperty_iff_mem_largestOpen P hP H,
      hasRepresentativeWithProperty_iff_mem_largestOpen P hP H', ← hqpoint, ← hspoint]
    exact hmem₁.trans hmem₂.symm⟩

end MorphismOfGerms

end AlgebraicGeometry

end
