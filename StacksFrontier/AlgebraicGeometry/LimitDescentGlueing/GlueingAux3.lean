module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Glueing two models of a scheme over a base change

Let `π : S ⟶ T` be a morphism of schemes and let `f : X ⟶ S` be a scheme over `S`.  Suppose `X` is
covered by two opens `A` and `B`, and that each of them is exhibited as a base change along `π`:
`A = ZA ×_T S` and `B = ZB ×_T S` for schemes `ZA`, `ZB` over `T`.  Suppose further that the two
induced descents of `A ⊓ B` — an open `VA ⊆ ZA` and an open `VB ⊆ ZB` — have been identified by an
isomorphism `φ : VA ≅ VB` over `T`, and that `Y` is a scheme over `T` glued out of `ZA` and `ZB`
along `φ`.  Then `X` is the base change of `Y` along `π`.

The glueing of `ZA` and `ZB` along `φ` is not performed here: `Y` together with the two open
immersions `jA : ZA ⟶ Y` and `jB : ZB ⟶ Y` is a hypothesis, described by the three properties that
pin down a glueing — the two immersions agree on `VA`, they cover `Y`, and their ranges meet
exactly in the image of `VA`.  This keeps the result independent of the particular colimit used to
build `Y`; for instance `Y` may be `CategoryTheory.Limits.pushout` of the two open immersions out
of `VA`, which exists by Mathlib's locally directed glueing.

## Main results

* `AlgebraicGeometry.isPullback_of_glueData`: the statement above, together with the
  compatibility of the glued morphism `X ⟶ Y` with the two pieces.

## Implementation notes

The morphism `g : X ⟶ Y` is glued from `hA ≫ jA` and `hB ≫ jB` on the two-element open cover
`{A, B}` of `X`, via `AlgebraicGeometry.Scheme.Cover.glueMorphisms`.  Its compatibility on
`pullback A.ι B.ι` is transported from `A ⊓ B` along
`AlgebraicGeometry.IsOpenImmersion.isPullback`, which identifies `A ⊓ B` with that pullback.

That `g` is the base change of `Y` is then checked on the two-element open cover `{jA, jB}` of `Y`
by `AlgebraicGeometry.Scheme.isPullback_of_openCover`, whose two instances are the hypotheses `hmA`
and `hmB` transported along `pullback g jA ≅ A` and `pullback g jB ≅ B`.  Producing those two
isomorphisms is the only place the hypotheses `hVA`, `hVB` and `hint` are used: they say exactly
that `g` meets the range of `jA` in `A` and the range of `jB` in `B`.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-! ### Glueing a morphism along two opens covering the source -/

/-- Two morphisms out of two opens covering a scheme which agree on the intersection of the opens
glue to a morphism out of the whole scheme.

This is `AlgebraicGeometry.Scheme.Cover.glueMorphisms` for the two-element cover `{A, B}`. -/
private lemma exists_hom_of_sup_eq_top {X Y : Scheme.{u}} {A B : X.Opens} (hAB : A ⊔ B = ⊤)
    (a : A.toScheme ⟶ Y) (b : B.toScheme ⟶ Y)
    (h : pullback.fst A.ι B.ι ≫ a = pullback.snd A.ι B.ι ≫ b) :
    ∃ g : X ⟶ Y, A.ι ≫ g = a ∧ B.ι ≫ g = b := by
  let U : Bool → X.Opens := fun c => bif c then A else B
  let 𝒱 : X.OpenCover := X.openCoverOfIsOpenCover U (.mk (by rw [iSup_bool_eq]; exact hAB))
  have hfT : 𝒱.f true = A.ι := rfl
  have hfF : 𝒱.f false = B.ι := rfl
  let F : ∀ c : Bool, 𝒱.X c ⟶ Y := fun c => Bool.rec (motive := fun c => 𝒱.X c ⟶ Y) b a c
  have hc : ∀ x y, pullback.fst (𝒱.f x) (𝒱.f y) ≫ F x = pullback.snd _ _ ≫ F y := by
    rintro (_ | _) (_ | _)
    · change pullback.fst B.ι B.ι ≫ b = pullback.snd B.ι B.ι ≫ b
      rw [(cancel_mono B.ι).mp (pullback.condition (f := B.ι) (g := B.ι))]
    · change pullback.fst B.ι A.ι ≫ b = pullback.snd B.ι A.ι ≫ a
      rw [← cancel_epi (pullbackSymmetry A.ι B.ι).hom]
      simp [h]
    · exact h
    · change pullback.fst A.ι A.ι ≫ a = pullback.snd A.ι A.ι ≫ a
      rw [(cancel_mono A.ι).mp (pullback.condition (f := A.ι) (g := A.ι))]
  refine ⟨𝒱.glueMorphisms F hc, ?_, ?_⟩
  · have := 𝒱.ι_glueMorphisms F hc true
    rwa [hfT] at this
  · have := 𝒱.ι_glueMorphisms F hc false
    rwa [hfF] at this

/-! ### Recognising a pullback square on a two-element cover of the target -/

/-- A commuting square whose upper-right corner `Y` is covered by two open immersions `jA` and `jB`
is a pullback square as soon as its two restrictions along `jA` and `jB` are.

This is `AlgebraicGeometry.Scheme.isPullback_of_openCover` for the two-element cover
`{jA, jB}`. -/
private lemma isPullback_of_pair_openCover {W Y S T ZA ZB : Scheme.{u}}
    (gW : W ⟶ Y) (fW : W ⟶ S) (qY : Y ⟶ T) (π : S ⟶ T)
    (jA : ZA ⟶ Y) (jB : ZB ⟶ Y) [IsOpenImmersion jA] [IsOpenImmersion jB]
    (hcov : jA.opensRange ⊔ jB.opensRange = ⊤)
    (HA : IsPullback (pullback.snd gW jA) (pullback.fst gW jA ≫ fW) (jA ≫ qY) π)
    (HB : IsPullback (pullback.snd gW jB) (pullback.fst gW jB ≫ fW) (jB ≫ qY) π) :
    IsPullback gW fW qY π := by
  let 𝒰 : Y.OpenCover :=
    { I₀ := Bool
      X := fun c => bif c then ZA else ZB
      f := fun c => Bool.rec (motive := fun c => (bif c then ZA else ZB) ⟶ Y) jB jA c
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun y ↦ ?_, ?_⟩
        · have hy : y ∈ jA.opensRange ⊔ jB.opensRange := hcov ▸ trivial
          rcases hy with hy | hy
          · exact ⟨true, hy⟩
          · exact ⟨false, hy⟩
        · rintro (_ | _) <;> infer_instance }
  refine Scheme.isPullback_of_openCover gW fW qY π 𝒰 ?_
  rintro (_ | _)
  · exact HB
  · exact HA

/-! ### Locating the pieces of the glued morphism -/

/-- If a morphism `g : X ⟶ Y` factors as `h ≫ j` on an open `U` of `X`, then `U` is contained in
the part of `X` lying over the range of `j`. -/
private lemma le_preimage_opensRange {X Y Z : Scheme.{u}} {U : X.Opens} {h : U.toScheme ⟶ Z}
    {j : Z ⟶ Y} [IsOpenImmersion j] {g : X ⟶ Y} (hg : U.ι ≫ g = h ≫ j) :
    U ≤ g ⁻¹ᵁ j.opensRange := by
  rintro x hxU
  obtain ⟨y, rfl⟩ : ∃ y : U.toScheme, U.ι y = x := ⟨⟨x, hxU⟩, rfl⟩
  change g (U.ι y) ∈ j.opensRange
  rw [← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply]
  exact Scheme.Hom.mem_opensRange.2 ⟨_, rfl⟩

/-- The converse inclusion to `AlgebraicGeometry.le_preimage_opensRange`, restricted to `U`.

Suppose `g : X ⟶ Y` factors as `h ≫ j` on an open `U` of `X`, that `j` and a second open immersion
`j'` meet exactly in the image of an open `W ⊆ Z`, and that `h` pulls `W` back to the part of `U`
lying in a second open `V ⊆ X`.  Then a point of `U` whose image under `g` lies in the range of
`j'` already lies in `V`. -/
private lemma preimage_opensRange_inf_le {X Y Z Z' : Scheme.{u}} {U V : X.Opens}
    {h : U.toScheme ⟶ Z} {j : Z ⟶ Y} {j' : Z' ⟶ Y} [IsOpenImmersion j] [IsOpenImmersion j']
    {W : Z.Opens} (hW : h ⁻¹ᵁ W = U.ι ⁻¹ᵁ V)
    (hint : j.opensRange ⊓ j'.opensRange = (W.ι ≫ j).opensRange)
    {g : X ⟶ Y} (hg : U.ι ≫ g = h ≫ j) :
    g ⁻¹ᵁ j'.opensRange ⊓ U ≤ V := by
  rintro x ⟨hxg, hxU⟩
  obtain ⟨y, rfl⟩ : ∃ y : U.toScheme, U.ι y = x := ⟨⟨x, hxU⟩, rfl⟩
  have egx : g (U.ι y) = j (h y) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hg]
  have hmem : g (U.ι y) ∈ j.opensRange ⊓ j'.opensRange :=
    ⟨Scheme.Hom.mem_opensRange.2 ⟨_, egx.symm⟩, hxg⟩
  rw [hint] at hmem
  obtain ⟨z, hz⟩ := Scheme.Hom.mem_opensRange.1 hmem
  rw [Scheme.Hom.comp_apply, egx] at hz
  have key : y ∈ h ⁻¹ᵁ W := by
    change h y ∈ W
    rw [← j.isOpenEmbedding.injective hz]
    exact z.2
  rw [hW] at key
  exact key

/-- Combination of the two previous lemmas: if `A ⊔ B = ⊤`, if `g` factors as `h ≫ j` on `A`, if
`j` and `j'` meet exactly in the image of `W ⊆ Z`, and if `h` pulls `W` back to the part of `A`
lying in `B`, then `A` is exactly the part of `X` lying over the range of `j`. -/
private lemma preimage_opensRange_eq {X Y Z Z' : Scheme.{u}} {A B : X.Opens} (hAB : A ⊔ B = ⊤)
    {h : A.toScheme ⟶ Z} {j : Z ⟶ Y} {j' : Z' ⟶ Y} [IsOpenImmersion j] [IsOpenImmersion j']
    {W : Z'.Opens} {h' : B.toScheme ⟶ Z'} (hW : h' ⁻¹ᵁ W = B.ι ⁻¹ᵁ A)
    (hint : j'.opensRange ⊓ j.opensRange = (W.ι ≫ j').opensRange)
    {g : X ⟶ Y} (hg : A.ι ≫ g = h ≫ j) (hg' : B.ι ≫ g = h' ≫ j') :
    g ⁻¹ᵁ j.opensRange = A := by
  refine le_antisymm ?_ (le_preimage_opensRange hg)
  calc g ⁻¹ᵁ j.opensRange = g ⁻¹ᵁ j.opensRange ⊓ (A ⊔ B) := by rw [hAB, inf_top_eq]
    _ = g ⁻¹ᵁ j.opensRange ⊓ A ⊔ g ⁻¹ᵁ j.opensRange ⊓ B := inf_sup_left _ _ _
    _ ≤ A ⊔ A := sup_le_sup inf_le_right (preimage_opensRange_inf_le hW hint hg')
    _ = A := sup_idem _

/-! ### The glueing lemma -/

/-- **Glueing two models of a scheme over a base change along a common open.** -/
public lemma isPullback_of_glueData {X S T Y ZA ZB : Scheme.{u}} (π : S ⟶ T) (f : X ⟶ S)
    {A B : X.Opens} (hAB : A ⊔ B = ⊤)
    {qA : ZA ⟶ T} {qB : ZB ⟶ T} {hA : A.toScheme ⟶ ZA} {hB : B.toScheme ⟶ ZB}
    (hmA : IsPullback hA (A.ι ≫ f) qA π) (hmB : IsPullback hB (B.ι ≫ f) qB π)
    {VA : ZA.Opens} {VB : ZB.Opens}
    (hVA : hA ⁻¹ᵁ VA = A.ι ⁻¹ᵁ B) (hVB : hB ⁻¹ᵁ VB = B.ι ⁻¹ᵁ A)
    (φ : VA.toScheme ≅ VB.toScheme)
    (qY : Y ⟶ T) (jA : ZA ⟶ Y) (jB : ZB ⟶ Y) [IsOpenImmersion jA] [IsOpenImmersion jB]
    (hjA : jA ≫ qY = qA) (hjB : jB ≫ qY = qB)
    (hpo : VA.ι ≫ jA = φ.hom ≫ VB.ι ≫ jB)
    (hcov : jA.opensRange ⊔ jB.opensRange = ⊤)
    (hint : jA.opensRange ⊓ jB.opensRange = (VA.ι ≫ jA).opensRange)
    (wA : (A ⊓ B : X.Opens).toScheme ⟶ VA.toScheme)
    (hwA : wA ≫ VA.ι = X.homOfLE inf_le_left ≫ hA)
    (hwB : wA ≫ φ.hom ≫ VB.ι = X.homOfLE inf_le_right ≫ hB) :
    ∃ g : X ⟶ Y, IsPullback g f qY π ∧ A.ι ≫ g = hA ≫ jA ∧ B.ι ≫ g = hB ≫ jB := by
  -- The intersection `A ⊓ B` is a pullback of `A.ι` and `B.ι`.
  have hsq : IsPullback (X.homOfLE (inf_le_left : A ⊓ B ≤ A))
      (X.homOfLE (inf_le_right : A ⊓ B ≤ B)) A.ι B.ι :=
    IsOpenImmersion.isPullback _ _ _ _ (by simp)
      (by simp [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self])
  -- On `A ⊓ B` the two prospective pieces of the glued morphism agree, by `hwA`, `hpo` and `hwB`.
  have key : X.homOfLE (inf_le_left : A ⊓ B ≤ A) ≫ hA ≫ jA
      = X.homOfLE (inf_le_right : A ⊓ B ≤ B) ≫ hB ≫ jB := by
    rw [← Category.assoc, ← Category.assoc, ← hwA, ← hwB, Category.assoc, hpo]
    simp
  -- Hence they agree on `pullback A.ι B.ι`, and so they glue.
  obtain ⟨g, hgA, hgB⟩ := exists_hom_of_sup_eq_top hAB (hA ≫ jA) (hB ≫ jB) (by
    rw [← cancel_epi hsq.isoPullback.hom, hsq.isoPullback_hom_fst_assoc,
      hsq.isoPullback_hom_snd_assoc]
    exact key)
  -- The intersection of the ranges of `jA` and `jB` seen inside `ZB`.
  have hint' : jB.opensRange ⊓ jA.opensRange = (VB.ι ≫ jB).opensRange := by
    rw [inf_comm, hint]
    simp only [hpo]
    exact Scheme.Hom.opensRange_comp_of_isIso _ _
  -- `A` and `B` are exactly the parts of `X` lying over `ZA` and `ZB`.
  have hrA : g ⁻¹ᵁ jA.opensRange = A := preimage_opensRange_eq hAB hVB hint' hgA hgB
  have hrB : g ⁻¹ᵁ jB.opensRange = B :=
    preimage_opensRange_eq (by rw [sup_comm]; exact hAB) hVA hint hgB hgA
  -- So each piece sits in a pullback square over `g`.
  have hpA : IsPullback hA A.ι jA g :=
    IsOpenImmersion.isPullback hA A.ι jA g hgA (by simpa using hrA)
  have hpB : IsPullback hB B.ι jB g :=
    IsOpenImmersion.isPullback hB B.ι jB g hgB (by simpa using hrB)
  -- Transporting `hmA` and `hmB` along those squares and glueing them gives the pullback square.
  refine ⟨g, isPullback_of_pair_openCover g f qY π jA jB hcov ?_ ?_, hgA, hgB⟩
  · exact hmA.of_iso' hpA.flip.isoPullback.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp [hjA]) (by simp)
  · exact hmB.of_iso' hpB.flip.isoPullback.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp [hjB]) (by simp)

end AlgebraicGeometry
