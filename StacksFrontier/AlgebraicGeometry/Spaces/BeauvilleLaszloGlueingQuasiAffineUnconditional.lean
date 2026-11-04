module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingQuasiAffineRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafSeparatedOfClosedRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatRelationQuotient

/-!
# Quasi-affine glueing triples are glued from separated algebraic spaces (Stacks 0F9U)

Let `(R → R', f)` be a glueing pair, `X = Spec R`, `U = Spec R_f`, `X' = Spec R'` and
`U' = Spec R'_f`. This module proves Stacks 0F9U: a cartesian triple `(V, V', Y')` of algebraic
spaces over `U ← U' → X'` whose three components are quasi-affine is isomorphic to the image under
the gluing functor of Stacks 0F9N of a separated algebraic space `Y` over `X`.

The proof is the source's. An affine glueable chart `T` of the triple is constructed (steps 1–3,
`BeauvilleLaszlo.Space.exists_affineGlueable_chart`); the kernel pair of the chart is realized as
an affine glueable relation `W ⇉ T` which is flat, locally of finite presentation, closed in
`T ⨯ T` and an equivalence relation (steps 4–8, `BeauvilleLaszlo.Space.exists_relation_data` and
the three lemmas following it). The quotient `Y = T/W` is an algebraic space by Stacks 04S6, is
separated by Stacks 0420, and base change commutes with forming it, so its image under the gluing
functor is the triple (`BeauvilleLaszlo.Space.nonempty_glueingFunctor_iso_of_quotient`).

## Main results

* `AlgebraicGeometry.Space.exists_quotient_of_isEquivalenceRelation`: the quotient of an algebraic
  space by a flat, locally finitely presented equivalence relation closed in the square is a
  separated algebraic space, and every base change of the quotient map is universal among maps
  coequalizing the base-changed relation.
* `BeauvilleLaszlo.Space.exists_isSeparatedOver_iso_of_isQuasiAffineComponents`:
  **Stacks 0F9U.**

## References

* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9U](https://stacks.math.columbia.edu/tag/0F9U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **The quotient of an algebraic space by a flat equivalence relation closed in the square.**
Let `p₀, p₁ : W ⟶ T` be morphisms of algebraic spaces over `S` forming an equivalence relation,
flat and locally of finite presentation, with `(p₀, p₁) : W ⟶ T ⨯ T` a closed immersion. Then
there are a separated algebraic space `Y` over `S` and `π : T ⟶ Y` coequalizing `p₀, p₁` such that
for every morphism `g : S' ⟶ S` of the site the base change of `π` is universal among maps to
algebraic spaces over `S'` coequalizing the base changes of `p₀, p₁`. -/
theorem exists_quotient_of_isEquivalenceRelation (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {W T : AlgebraicSpaces B S hS} (p₀ p₁ : W ⟶ T)
    (hrel : IsEquivalenceRelation p₀.hom p₁.hom)
    (h₀F : IsFlat B S hS p₀.hom) (h₀L : IsLocallyOfFinitePresentation B S hS p₀.hom)
    (h₁F : IsFlat B S hS p₁.hom) (h₁L : IsLocallyOfFinitePresentation B S hS p₁.hom)
    (hci : IsClosedImmersion B S hS (prod.lift p₀.hom p₁.hom)) :
    ∃ (Y : AlgebraicSpaces B S hS) (π : T ⟶ Y), p₀ ≫ π = p₁ ≫ π ∧
      IsSeparatedOver B S hS Y.obj ∧
      ∀ {S' : Scheme.{u}} {hS' : B.Contains S'} (g : B.obj hS' ⟶ B.obj hS)
        (A : AlgebraicSpaces B S' hS')
        (k : (BeauvilleLaszlo.Space.baseChange B S' S hS' hS g).obj T ⟶ A),
        (BeauvilleLaszlo.Space.baseChange B S' S hS' hS g).map p₀ ≫ k =
            (BeauvilleLaszlo.Space.baseChange B S' S hS' hS g).map p₁ ≫ k →
          ∃! d, (BeauvilleLaszlo.Space.baseChange B S' S hS' hS g).map π ≫ d = k := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  let Φ := (Over.equivalenceOfIsTerminal
    (terminalIsTerminal : IsTerminal (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)))).inverse
  let j : PreRelation (Φ.obj W.obj) (Φ.obj T.obj) := prod.lift (Φ.map p₀.hom) (Φ.map p₁.hom)
  have ht : j.target = Φ.map p₀.hom := prod.lift_fst _ _
  have hs : j.source = Φ.map p₁.hom := prod.lift_snd _ _
  have htl : j.target.left = p₀.hom := congrArg (·.left) ht
  have hsl : j.source.left = p₁.hom := congrArg (·.left) hs
  have hrelj : IsEquivalenceRelation j.target j.source := by
    rw [ht, hs]
    exact isEquivalenceRelation_map Φ p₀.hom p₁.hom hrel
  obtain ⟨halg, hsep⟩ := isSeparatedOver_quotientSheaf_of_isClosedImmersion B S hS j
    W.property T.property hrelj (by rwa [htl]) (by rwa [htl]) (by rwa [hsl]) (by rwa [hsl])
    (by rwa [htl, hsl])
  let Y : AlgebraicSpaces B S hS := ⟨(quotientSheaf j).obj, halg⟩
  let π : T ⟶ Y := ObjectProperty.homMk (toQuotientSheaf j)
  have hπ : p₀ ≫ π = p₁ ≫ π := by
    apply ObjectProperty.hom_ext
    have h := target_toQuotientSheaf_eq_source j
    rwa [htl, hsl] at h
  refine ⟨Y, π, hπ, hsep, fun {S' hS'} g A k hk => ?_⟩
  have hk' : (OverShriek.relocalizeRestrict g).map j.target.left ≫ k.hom =
      (OverShriek.relocalizeRestrict g).map j.source.left ≫ k.hom := by
    rw [htl, hsl]
    exact congrArg (·.hom) hk
  obtain ⟨d, hd, hdu⟩ := existsUnique_desc_relocalizeRestrict_quotientSheaf g j
    A.property.isSheaf k.hom hk'
  exact ⟨ObjectProperty.homMk d, ObjectProperty.hom_ext _ hd,
    fun d' hd' => ObjectProperty.hom_ext _ (hdu d'.hom (congrArg (·.hom) hd'))⟩

end AlgebraicGeometry.Space

namespace BeauvilleLaszlo.Space

variable {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
  (B : BigFppfSite.{u})
  (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
  (hU : B.Contains (Spec (.of (Localization.Away f))))
  (hX' : B.Contains (Spec (.of R')))
  (hX : B.Contains (Spec (.of R)))

/-- **Stacks 0F9U.** Let `(g : R → R', f)` be a glueing pair, and let `X = Spec R`,
`U = Spec R_f`, `X' = Spec R'` and `U' = Spec R'_{g f}` be the four corners of its square, all in
the big fppf site `B`. Any cartesian triple `(V, V', Y')` of algebraic spaces over `U ← U' → X'`
whose three components are quasi-affine is isomorphic to the image, under the gluing functor of
Stacks 0F9N, of an algebraic space `Y` over `X` which is separated over `X`. -/
@[stacks 0F9U]
theorem exists_isSeparatedOver_iso_of_isQuasiAffineComponents
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f)
    (Z : GlueingData B (Spec (.of (Localization.Away (g f))))
      (Spec (.of (Localization.Away f))) (Spec (.of R')) hU' hU hX'
      (canGU g f B hU' hU) (canGX' g f B hU' hX'))
    (hZ : quasiAffineComponents B (Spec (.of (Localization.Away (g f))))
      (Spec (.of (Localization.Away f))) (Spec (.of R')) hU' hU hX'
      (canGU g f B hU' hU) (canGX' g f B hU' hX') Z) :
    ∃ Y : AlgebraicSpaces B (Spec (.of R)) hX,
      AlgebraicGeometry.Space.IsSeparatedOver B (Spec (.of R)) hX Y.obj ∧
        Nonempty ((beauvilleLaszloGlueingSpaces B _ _ _ _ hU' hU hX' hX
          (canGU g f B hU' hU) (canGX' g f B hU' hX') (canJU f B hU hX) (canJX' g B hX' hX)
          (canonical_comm g f B hU' hU hX' hX)).functor.obj Y ≅ Z) := by
  obtain ⟨T, q, hTa, hTg, hqU, hqM, hqX⟩ := exists_affineGlueable_chart g f B hU' hU hX' hX
    (canonical_comm g f B hU' hU hX' hX) hglue Z hZ
  obtain ⟨W, p₀, p₁, eW, hWa, hWg, hp₀, hp₁, hk⟩ := exists_relation_data g f B hU' hU hX' hX
    hglue hTa hTg q hqU hqM hqX
  have hc := chartLegs_of g f B hU' hU hX' hX q hqU hqM hqX
  obtain ⟨⟨h₀F, h₀L⟩, ⟨h₁F, h₁L⟩⟩ := relation_flat g f B hU' hU hX' hX hglue hTa hTg q hc p₀ p₁
    hWa hk
  have hci := relation_isClosedImmersion g f B hU' hU hX' hX hglue hTa q hc p₀ p₁ hWa hk
  have hrel := relation_isEquivalenceRelation g f B hU' hU hX' hX hglue hTa hTg q p₀ p₁ eW hWa
    hWg hp₀ hp₁ h₁F hci
  obtain ⟨Y, π, hπ, hsep, hu⟩ := AlgebraicGeometry.Space.exists_quotient_of_isEquivalenceRelation
    B _ hX p₀ p₁ hrel h₀F h₀L h₁F h₁L hci
  exact ⟨Y, hsep, nonempty_glueingFunctor_iso_of_quotient B _ _ _ _ hU' hU hX' hX _ _ _ _
    (canonical_comm g f B hU' hU hX' hX) (canonicalSpec g f B hU' hU hX' hX) p₀ p₁ π hπ q
    (hu _) (hu _) (hu _) hk.1 hk.2.1 hk.2.2 hc.1.isLocallySurjective
    hc.2.1.isLocallySurjective hc.2.2.isLocallySurjective⟩

end BeauvilleLaszlo.Space

end
