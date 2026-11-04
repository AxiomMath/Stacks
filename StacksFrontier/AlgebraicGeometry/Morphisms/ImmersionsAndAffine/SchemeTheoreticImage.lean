module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.Constructible
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent

/-!
# The scheme theoretic image of a partial section

Let `f : X ⟶ Y` be a separated morphism and let `s` be a section of `f` defined over a
retrocompact open subset `V` of `Y`. Then the scheme theoretic image of `s`, a closed subscheme
of `X`, maps isomorphically onto `Y` above `V`.

Retrocompactness of `V` makes `V.ι` quasi-compact, hence `s` quasi-compact, so its scheme
theoretic image behaves well under restriction. Over `V` the section becomes a closed immersion
splitting the separated morphism `f ∣_ V`, so its image is the whole of `V`, and the canonical
identification of the restricted image with the pullback of the image along `V` transports that
to the statement about `pullback.snd`.

## Main results

* `AlgebraicGeometry.isIso_pullback_snd_imageι_comp_of_section`: the morphism from the scheme
  theoretic image of a partial section to the base becomes an isomorphism over the domain of the
  section.

## Implementation notes

That the scheme theoretic image is isomorphic to the base over the open subscheme is expressed
canonically by saying that the second projection from its pullback to that open subscheme is an
isomorphism; the open subset is a `Scheme.Opens`, so openness is part of the datum. The
restricted image is compared with the pullback by
`AlgebraicGeometry.imageMorphismRestrictIso` of Tag 01R8, part (3).

## References

* [Stacks Project, Tag 0CNG](https://stacks.math.columbia.edu/tag/0CNG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- If an isomorphism followed by `g` is a morphism `k` that is an isomorphism, so is `g`. -/
private theorem isIso_of_hom_comp_eq {C : Type*} [Category C] {A B D : C} (e : A ≅ B)
    {g : B ⟶ D} {k : A ⟶ D} (h : e.hom ≫ g = k) (hk : IsIso k) : IsIso g := by
  have : IsIso (e.hom ≫ g) := h ▸ hk
  exact IsIso.of_isIso_comp_left e.hom g

/-- The identification of the restricted image with the pullback, and the compatibility of that
identification with the embedding into the open subscheme, specialised to a section. Pulling
these two steps out of the main proof keeps each elaboration small; stated inline they force the
elaborator to unfold the image of a restricted morphism inside a goal about `IsIso`. -/
private theorem isIso_pullbackFst_comp_morphismRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (s : V.toScheme ⟶ X) [QuasiCompact s]
    (hs : IsIso ((s ∣_ f ⁻¹ᵁ V).imageι ≫ f ∣_ V)) :
    IsIso (pullback.fst (f ⁻¹ᵁ V).ι s.imageι ≫ f ∣_ V) :=
  isIso_of_hom_comp_eq (imageMorphismRestrictIso s (f ⁻¹ᵁ V))
    (by rw [← Category.assoc, imageMorphismRestrictIso_hom_fst]) hs

/-- **Stacks 0CNG.** The scheme-theoretic image of a section over a retrocompact open subset of
the target of a separated morphism is isomorphic to that open subset after base change. -/
@[stacks 0CNG]
lemma isIso_pullback_snd_imageι_comp_of_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] (V : Y.Opens) (hV : IsRetrocompact (V : Set Y))
    (s : V.toScheme ⟶ X) (hs : s ≫ f = V.ι) :
    IsIso (pullback.snd (s.imageι ≫ f) V.ι) := by
  let : QuasiCompact V.ι :=
    (quasiCompact_iff_isSpectralMap).2
      ((IsRetrocompact_iff_isSpectralMap_subtypeVal).mp hV)
  let : QuasiCompact s := by
    have hcomp : QuasiCompact (s ≫ f) := by simpa [hs]
    exact QuasiCompact.of_comp s f
  let U : X.Opens := f ⁻¹ᵁ V
  let t : (s ⁻¹ᵁ U).toScheme ⟶ U.toScheme := s ∣_ U
  let g : U.toScheme ⟶ V.toScheme := f ∣_ V
  have hD : s ⁻¹ᵁ U = ⊤ := by
    dsimp [U]; rw [← Scheme.Hom.comp_preimage, hs]; simp
  have hDIsIso : IsIso ((s ⁻¹ᵁ U).ι) := by
    rw [hD]; change IsIso ((Scheme.topIso V.toScheme).hom); infer_instance
  have htcomp : t ≫ g = (s ⁻¹ᵁ U).ι := by
    apply (cancel_mono V.ι).mp
    have hgι : g ≫ V.ι = U.ι ≫ f := morphismRestrict_ι f V
    have htι : t ≫ U.ι = (s ⁻¹ᵁ U).ι ≫ s := morphismRestrict_ι s U
    calc
      t ≫ (g ≫ V.ι) = t ≫ (U.ι ≫ f) := by rw [hgι]
      _ = (s ⁻¹ᵁ U).ι ≫ (s ≫ f) := by
        show (t ≫ U.ι) ≫ f = ((s ⁻¹ᵁ U).ι ≫ s) ≫ f
        rw [htι]
      _ = (s ⁻¹ᵁ U).ι ≫ V.ι := by rw [hs]
  have hclosedComp : IsClosedImmersion (t ≫ g) := by
    rw [htcomp]
    let : IsIso ((s ⁻¹ᵁ U).ι) := hDIsIso
    infer_instance
  have : IsSeparated g := inferInstance
  have : IsClosedImmersion t := IsClosedImmersion.of_comp t g
  have htImageIso : IsIso t.toImage := inferInstance
  have htgIso : IsIso (t.imageι ≫ g) := by
    have htcompIso : IsIso (t ≫ g) := by
      rw [htcomp]; exact hDIsIso
    rw [← t.toImage_imageι] at htcompIso
    exact (isIso_comp_left_iff t.toImage (t.imageι ≫ g)).mp htcompIso
  have hfstIso : IsIso (pullback.fst U.ι s.imageι ≫ g) :=
    isIso_pullbackFst_comp_morphismRestrict f V s htgIso
  have hsndIso : IsIso (pullback.snd s.imageι U.ι ≫ g) :=
    isIso_of_hom_comp_eq (pullbackSymmetry U.ι s.imageι)
      (by rw [← Category.assoc, pullbackSymmetry_hom_comp_snd]) hfstIso
  let eOpen := pullbackRestrictIsoRestrict f V
  let mMap : pullback s.imageι (pullback.fst f V.ι) ⟶ pullback s.imageι U.ι :=
    pullback.map s.imageι (pullback.fst f V.ι) s.imageι U.ι
      (𝟙 _) eOpen.hom (𝟙 _) (by simp) (by
        rw [Category.comp_id, pullbackRestrictIsoRestrict_hom_ι])
  let eMap : pullback s.imageι (pullback.fst f V.ι) ≅ pullback s.imageι U.ι := asIso mMap
  let ePullback : pullback (s.imageι ≫ f) V.ι ≅ pullback s.imageι U.ι :=
    (pullbackRightPullbackFstIso f V.ι s.imageι).symm ≪≫ eMap
  have hmapSnd :
      mMap ≫ pullback.snd s.imageι U.ι =
        pullback.snd s.imageι (pullback.fst f V.ι) ≫ eOpen.hom := by
    dsimp [mMap]; rw [pullback.map, pullback.lift_snd]
  have hprojection : pullback.snd (s.imageι ≫ f) V.ι =
      ePullback.hom ≫ pullback.snd s.imageι U.ι ≫ g := by
    apply (cancel_mono V.ι).mp
    rw [← pullback.condition]
    have hpath : ePullback.hom ≫ pullback.snd s.imageι U.ι ≫ g ≫ V.ι =
        pullback.fst (s.imageι ≫ f) V.ι ≫ (s.imageι ≫ f) := by
      show ((pullbackRightPullbackFstIso f V.ι s.imageι).inv ≫ mMap) ≫
          pullback.snd s.imageι U.ι ≫ (f ∣_ V) ≫ V.ι =
        pullback.fst (s.imageι ≫ f) V.ι ≫ (s.imageι ≫ f)
      calc
        ((pullbackRightPullbackFstIso f V.ι s.imageι).inv ≫ mMap) ≫
              pullback.snd s.imageι U.ι ≫ (f ∣_ V) ≫ V.ι =
            ((pullbackRightPullbackFstIso f V.ι s.imageι).inv ≫
              (mMap ≫ pullback.snd s.imageι U.ι)) ≫ (f ∣_ V) ≫ V.ι := by simp [Category.assoc]
        _ = ((pullbackRightPullbackFstIso f V.ι s.imageι).inv ≫
              (pullback.snd s.imageι (pullback.fst f V.ι) ≫ eOpen.hom)) ≫
                (f ∣_ V) ≫ V.ι := by rw [hmapSnd]
        _ = ((pullbackRightPullbackFstIso f V.ι s.imageι).inv ≫
              (pullback.snd s.imageι (pullback.fst f V.ι) ≫
                pullback.fst f V.ι)) ≫ f := by simp [Category.assoc, eOpen, morphismRestrict_ι]
        _ = (pullback.fst (s.imageι ≫ f) V.ι ≫ s.imageι) ≫ f := by
              rw [pullbackRightPullbackFstIso_inv_snd_fst]
        _ = pullback.fst (s.imageι ≫ f) V.ι ≫ (s.imageι ≫ f) := by simp [Category.assoc]
    exact hpath.symm
  rw [hprojection]
  infer_instance

end AlgebraicGeometry
