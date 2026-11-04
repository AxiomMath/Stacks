module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalProperIntersection

/-!
# Composition of the classes of smooth closed subschemes meeting transversally

Let `k` be a field, let `X`, `Y`, `Z` be smooth and separated over `k` of constant dimensions
`d`, `e`, `f`, with `Y` proper, and let `A ⊆ X × Y` and `B ⊆ Y × Z` be closed subschemes which are
themselves smooth over `k`, of constant dimensions `e - r` and `f - s`. If the fibre product
`A ×_Y B` over the middle factor is smooth over `k` of the expected dimension `f - (r + s)` and
maps by a closed immersion to `X × Z`, then

  `[B] ∘ [A] = [A ×_Y B]`   in   `CH_{f-(r+s)}(X × Z)`.

This is the computation the proofs of Stacks 0FG2, 0FG3 and 0FGI make again and again: the
intersection `pr₁₂⁻¹(A) ∩ pr₂₃⁻¹(B)` is `A ×_Y B`, it has the expected dimension, and all the
local rings involved are Cohen–Macaulay because everything is smooth over `k`. It is the case of
`DiagonalClassFamily.ProperIntersectionFormula.compositionInt_closedSubscheme` in which the
dimension and Cohen–Macaulay hypotheses are discharged by smoothness, stated for the canonical
family of diagonal classes, whose proper-intersection formula is Stacks 0FFD.

The fibre product is allowed to be presented by any scheme `F` isomorphic to it, compatibly with
the maps to `X × Z`; this is how it is met in practice, where `A ×_Y B` is recognized as a familiar
scheme embedded in `X × Z`.

## Main results

* `Stacks.WeilCohomology.compositionInt_smoothTransversal`: `[B] ∘ [A] = [F]` on integral Chow
  groups, for the canonical family of diagonal classes.
* `Stacks.WeilCohomology.compositionInt_graph_left`: `[B] ∘ [Γ_g] = [(g × 1)(B)]`.
* `Stacks.WeilCohomology.compositionInt_graph_right_of_isIso`: `[Γ_g] ∘ [A] = [(1 × g⁻¹)(A)]` for
  an isomorphism `g`.

The structure morphisms of `A`, `B` and `F` over `k` are passed as separate morphisms `qA`, `qB`,
`qF` together with the equations identifying them, so that the lemmas apply to whatever form the
structure morphism of a smooth scheme takes in practice.

## References

* [Stacks Project, Tag 0FFD](https://stacks.math.columbia.edu/tag/0FFD)
* [Stacks Project, Tag 0FG2](https://stacks.math.columbia.edu/tag/0FG2)
* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  (sZ : Z ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]
  [Smooth sX] [Smooth sY] [Smooth sZ] [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ]

/-- Every irreducible component of a scheme smooth of constant relative dimension `n` over `k`
has delta-dimension `n`, read in any equal integer degree. -/
theorem deltaDimension_irreducibleComponent_of_relativeDimension_eq {T : Scheme.{u}}
    (q : T ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType q] {n : ℕ}
    (hq : RelativeDimension q n) {m : ℤ} (hm : (n : ℤ) = m) (V : irreducibleComponents T) :
    deltaDimension (fieldChowSituation k) q
      ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = m :=
  hm ▸ deltaDimension_irreducibleComponent_of_relativeDimension k q n hq V

/-- **The composition of the classes of two smooth closed subschemes meeting transversally.**
Let `a : A ⟶ X × Y` and `b : B ⟶ Y × Z` be closed immersions with `A` and `B` smooth over `k` of
constant dimensions `e - r` and `f - s`. Let `F` be smooth over `k` of constant dimension
`f - (r + s)`, let `j : F ⟶ X × Z` be a closed immersion and let `φ : A ×_Y B ≅ F` be an
isomorphism carrying the map `A ×_Y B ⟶ X × Z` to `j`. Then, for the canonical family of diagonal
classes, `[B] ∘ [A] = [F]` in `CH_{f-(r+s)}(X × Z)`. -/
theorem compositionInt_smoothTransversal [IsProper sY] {d e f : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (hZ : RelativeDimension sZ f) (r s : ℤ) {A B F : Scheme.{u}}
    (a : A ⟶ Limits.pullback sX sY) [IsClosedImmersion a]
    (b : B ⟶ Limits.pullback sY sZ) [IsClosedImmersion b]
    (j : F ⟶ Limits.pullback sX sZ) [IsClosedImmersion j]
    (φ : compositionFibre a b ≅ F) (hφ : φ.hom ≫ j = compositionFibre.toProduct a b)
    {qA : A ⟶ (fieldChowSituation k).S} {qB : B ⟶ (fieldChowSituation k).S}
    {qF : F ⟶ (fieldChowSituation k).S} [Smooth qA] [Smooth qB] [Smooth qF]
    (hqA : a ≫ prodBase sX sY = qA) (hqB : b ≫ prodBase sY sZ = qB)
    (hqF : j ≫ prodBase sX sZ = qF)
    {nA nB nF : ℕ} (hA : RelativeDimension qA nA) (hB : RelativeDimension qB nB)
    (hF : RelativeDimension qF nF)
    (hnA : (nA : ℤ) = e - r) (hnB : (nB : ℤ) = f - s) (hnF : (nF : ℤ) = f - (r + s)) :
    compositionInt k sX sY sZ (canonicalDiagonalClassFamily k) hX hY hZ r s
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX sY) a ((e : ℤ) - r)))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sY sZ) b ((f : ℤ) - s))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase sX sZ) j ((f : ℤ) - (r + s))) := by
  have : IsClosedImmersion (compositionFibre.toProduct a b) := by
    rw [← hφ]; infer_instance
  have hmor : compositionFibre.toProduct a b ≫ prodBase sX sZ = φ.hom ≫ qF := by
    rw [← hφ, Category.assoc, hqF]
  rw [DiagonalClassFamily.ProperIntersectionFormula.compositionInt_closedSubscheme
      k sX sY sZ (canonicalDiagonalClassFamily_properIntersectionFormula k) hX hY hZ r s a b
      (fun T ↦ (deltaDimension_congr hqA _).trans
        (deltaDimension_irreducibleComponent_of_relativeDimension_eq k _ hA hnA T))
      (fun T ↦ (deltaDimension_congr hqB _).trans
        (deltaDimension_irreducibleComponent_of_relativeDimension_eq k _ hB hnB T)) ?_ ?_,
    cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ j φ hφ]
  · rw [schemeDeltaDimension_congr _ hmor, schemeDeltaDimension_comp_iso]
    exact schemeDeltaDimension_le_of_forall_irreducibleComponent _
      (deltaDimension_irreducibleComponent_of_relativeDimension_eq k _ hF hnF)
  · intro x _
    subst hqA hqB
    exact ⟨isCohenMacaulayLocalRing_stalk_of_smooth k (a ≫ prodBase sX sY) _,
      isCohenMacaulayLocalRing_stalk_of_smooth k (b ≫ prodBase sY sZ) _⟩

attribute [local instance] isClosedImmersion_graphMorphism

/-- **Composition with the graph of a morphism on the source side.** For `f : Y ⟶ X` over `k`
and a smooth closed subscheme `b : B ⟶ Y × Z` of constant dimension `f - s`, if
`(f × 1) ∘ b : B ⟶ X × Z` is a closed immersion then `[B] ∘ [Γ_f] = [(f × 1)(B)]`: the fibre
product `Γ_f ×_Y B` is `B` itself, the graph being a section of the second projection. -/
theorem compositionInt_graph_left [IsProper sY] {d e f : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (hZ : RelativeDimension sZ f) (s : ℤ) (g : Y ⟶ X)
    (hg : g ≫ sX = sY) {B : Scheme.{u}} (b : B ⟶ Limits.pullback sY sZ) [IsClosedImmersion b]
    [IsClosedImmersion (b ≫ pullback.map sY sZ sX sZ g (𝟙 Z) (𝟙 _) (by simpa using hg.symm)
      (by simp))]
    {qB : B ⟶ (fieldChowSituation k).S} [Smooth qB] (hqB : b ≫ prodBase sY sZ = qB) {nB : ℕ}
    (hB : RelativeDimension qB nB) (hnB : (nB : ℤ) = f - s) :
    compositionInt k sX sY sZ (canonicalDiagonalClassFamily k) hX hY hZ 0 s
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX sY) (graphMorphism sX sY g hg) ((e : ℤ) - 0)))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sY sZ) b ((f : ℤ) - s))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase sX sZ) (b ≫ pullback.map sY sZ sX sZ g (𝟙 Z) (𝟙 _) (by simpa using hg.symm)
          (by simp)) ((f : ℤ) - (0 + s))) := by
  set Γ := graphMorphism sX sY g hg
  have hΓ : Γ ≫ pullback.snd sX sY = 𝟙 Y := graphMorphism_snd _ _ _ _
  have hΓf : Γ ≫ pullback.fst sX sY = g := graphMorphism_fst _ _ _ _
  have : IsIso (Γ ≫ pullback.snd sX sY) := by rw [hΓ]; infer_instance
  have hj : (b ≫ pullback.map sY sZ sX sZ g (𝟙 Z) (𝟙 _) (by simpa using hg.symm) (by simp)) ≫
      prodBase sX sZ = qB := by
    rw [← hqB]; simp [prodBase, hg]
  refine compositionInt_smoothTransversal k sX sY sZ hX hY hZ 0 s Γ b _
    (asIso (pullback.snd (Γ ≫ pullback.snd sX sY) (b ≫ pullback.fst sY sZ))) ?_
    (qA := sY) (by rw [prodBase, ← Category.assoc, hΓf, hg]) hqB hj hY hB hB (by simp) hnB
    (by rw [hnB]; ring)
  have hc : pullback.fst (Γ ≫ pullback.snd sX sY) (b ≫ pullback.fst sY sZ) ≫ Γ ≫
      pullback.snd sX sY = pullback.snd _ _ ≫ b ≫ pullback.fst sY sZ := by
    simpa only [Category.assoc] using pullback.condition
  apply pullback.hom_ext
  · simp only [asIso_hom, compositionFibre.toProduct, pullback.map, Category.assoc,
      pullback.lift_fst]
    rw [← reassoc_of% hc]
    simp only [reassoc_of% hΓ, hΓf]
  · simp only [asIso_hom, compositionFibre.toProduct, pullback.map, Category.assoc,
      pullback.lift_snd, Category.comp_id]

/-- **Composition with the graph of an isomorphism on the target side.** For an isomorphism
`g : Z ⟶ Y` over `k` and a smooth closed subscheme `a : A ⟶ X × Y` of constant dimension `e - r`,
`[Γ_g] ∘ [A] = [(1 × g⁻¹)(A)]`: the fibre product `A ×_Y Γ_g` is `A`, because `Γ_g ⟶ Y` is the
isomorphism `g`. -/
theorem compositionInt_graph_right_of_isIso [IsProper sY] {d e f : ℕ}
    (hX : RelativeDimension sX d) (hY : RelativeDimension sY e) (hZ : RelativeDimension sZ f)
    (r : ℤ) (g : Z ⟶ Y) [IsIso g] (hg : g ≫ sY = sZ) {A : Scheme.{u}}
    (a : A ⟶ Limits.pullback sX sY) [IsClosedImmersion a] {qA : A ⟶ (fieldChowSituation k).S}
    [Smooth qA] (hqA : a ≫ prodBase sX sY = qA) {nA : ℕ} (hA : RelativeDimension qA nA)
    (hnA : (nA : ℤ) = e - r)
    (hnA' : (nA : ℤ) = f - r) :
    compositionInt k sX sY sZ (canonicalDiagonalClassFamily k) hX hY hZ r 0
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX sY) a ((e : ℤ) - r)))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sY sZ) (graphMorphism sY sZ g hg) ((f : ℤ) - 0))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase sX sZ) (a ≫ pullback.map sX sY sX sZ (𝟙 X) (inv g) (𝟙 _) (by simp)
          (by rw [Category.comp_id, IsIso.eq_inv_comp, hg])) ((f : ℤ) - (r + 0))) := by
  set Γ := graphMorphism sY sZ g hg
  have hΓ : Γ ≫ pullback.fst sY sZ = g := graphMorphism_fst _ _ _ _
  have hΓs : Γ ≫ pullback.snd sY sZ = 𝟙 Z := graphMorphism_snd _ _ _ _
  have : IsIso (Γ ≫ pullback.fst sY sZ) := by rw [hΓ]; infer_instance
  set m := pullback.map sX sY sX sZ (𝟙 X) (inv g) (𝟙 _) (by simp)
    (by rw [Category.comp_id, IsIso.eq_inv_comp, hg])
  have : IsIso m := by
    refine ⟨pullback.map sX sZ sX sY (𝟙 X) g (𝟙 _) (by simp) (by simp [hg]), ?_, ?_⟩ <;>
      apply pullback.hom_ext <;> simp [m]
  have hj : (a ≫ m) ≫ prodBase sX sZ = qA := by rw [← hqA]; simp [m, prodBase]
  refine compositionInt_smoothTransversal k sX sY sZ hX hY hZ r 0 a Γ (a ≫ m)
    (asIso (pullback.fst (a ≫ pullback.snd sX sY) (Γ ≫ pullback.fst sY sZ))) ?_
    (qB := sZ) hqA (by rw [prodBase, ← Category.assoc, hΓ, hg]) hj hA hZ hA hnA (by simp)
    (by rw [hnA']; ring)
  apply pullback.hom_ext
  · simp only [asIso_hom, Category.assoc, compositionFibre.toProduct, m, pullback.map,
      pullback.lift_fst, Category.comp_id]
  · simp only [asIso_hom, Category.assoc, compositionFibre.toProduct, pullback.lift_snd, m,
      pullback.lift_snd]
    rw [← cancel_mono g]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have := pullback.condition (f := a ≫ pullback.snd sX sY) (g := Γ ≫ pullback.fst sY sZ)
    simp only [hΓ] at this
    rw [this, reassoc_of% hΓs]

end Stacks.WeilCohomology

end
