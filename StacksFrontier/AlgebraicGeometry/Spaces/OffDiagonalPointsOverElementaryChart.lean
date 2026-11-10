module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas

/-!
# No off-diagonal points over a point whose residue-field point is a monomorphism

Let `e : W ⟶ X` be a morphism from a scheme to an algebraic space and `w ∈ W` a point such that
the composite `Spec κ(w) ⟶ W ⟶ X` is a monomorphism, as for the distinguished point of an
elementary étale neighbourhood (Stacks 0BBP). Let `P` be a scheme with a monomorphism
`j : P ⟶ W ×_G T` over a common base `G`, and let `π : P ⟶ W ⟶ X` be the induced morphism. If
every point of `P` over `t ∈ T` maps to `w` in `W`, then every point of `P ×_X P` lying over `t`
is on the diagonal.

This is the fibre hypothesis of
`AlgebraicGeometry.Space.exists_isOpen_isClosedImmersion_of_isFinite_of_unramified` in the
situation of the proof that families of curves are étale locally schemes (Stacks 0E6F), where
`P` is a finite piece of a divisor on an étale chart.

## Main results

* `AlgebraicGeometry.Space.mem_range_of_mono_residueFieldMap`: the statement above, proved with
  `P ×_X P` and its diagonal replaced by any `Q` carrying two morphisms to `P` which agree over
  `X` and over `T`, admit a common section `δ` and jointly determine maps into `Q`; the
  conclusion is then that a point of `Q` over `t` lies in the range of `δ`.

## Implementation notes

For a point `q` of `P ×_X P` over `t`, the residue-field point `Spec κ(q) ⟶ P ×_X P` followed by
either projection and `j` gives two morphisms `Spec κ(q) ⟶ W` through `w`. Both factor through
`Spec κ(w)`, and their composites with `Spec κ(w) ⟶ X` agree, so they agree; they also agree in
`T`, so the two morphisms `Spec κ(q) ⟶ P` agree, and the residue-field point of `q` factors
through the diagonal.

## References

* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "𝒯" => BigFppfOver.toScheme B S hS

/-- A morphism of the site out of the residue-field point of a scheme of the site, whose
underlying morphism of schemes passes through a point `w` of the target, factors through the
residue-field point of `w`. -/
theorem exists_comp_residueFieldMap_eq {Q W : BigFppfOver B S hS} (q : Q.left.1)
    (g : residueFieldObject B S hS Q q (B.residueField_spec_contains Q.left.property q) ⟶ W)
    (w : W.left.1) (hw : B.Contains (Spec (.of (W.left.1.residueField w))))
    (hg : ∀ x, (𝒯).map g x = w) :
    ∃ α : residueFieldObject B S hS Q q (B.residueField_spec_contains Q.left.property q) ⟶
        residueFieldObject B S hS W w hw,
      α ≫ residueFieldMap B S hS W w hw = g := by
  set K := Q.left.1.residueField q
  let g₀ : Spec (.of K) ⟶ W.left.1 := (𝒯).map g
  have hpt : g₀ (IsLocalRing.closedPoint K) = w := hg _
  let α₀ : Spec (.of K) ⟶ Spec (W.left.1.residueField w) :=
    Spec.map (W.left.1.descResidueField (Scheme.stalkClosedPointTo g₀)) ≫
      Spec.map (W.left.1.residueFieldCongr hpt.symm).hom
  have hα₀ : α₀ ≫ W.left.1.fromSpecResidueField w = g₀ := by
    simp only [α₀, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
    exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K W.left.1 g₀
  obtain ⟨α, hα⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS (X :=
      residueFieldObject B S hS Q q (B.residueField_spec_contains Q.left.property q))
    (Y := residueFieldObject B S hS W w hw) α₀ (by
      change α₀ ≫ (W.left.1.fromSpecResidueField w ≫ W.hom.1) =
        B.inclusion.map (residueFieldObject B S hS Q q _).hom
      rw [← Category.assoc, hα₀]
      exact congrArg (fun k => k.1) (Over.w g))
  refine ⟨α, (𝒯).map_injective ?_⟩
  rwa [Functor.map_comp, hα]

/-- **Every point of a fibre product `P ×_{X'} P` over `t` is on the diagonal.** Let
`e : W ⟶ X` be a morphism from a scheme to an algebraic space and `w ∈ W` a point whose
residue-field point is a monomorphism into `X`. Let `j : P ⟶ W ×_G T` be a monomorphism, and let
`a, b : Q ⟶ P` be two morphisms which agree after `j`, the projection to `W` and `e`, and after
`j` and the projection to `T`, such that maps into `Q` are determined by their composites with
`a` and `b` (as for a fibre product of `P` with itself over some `X'` mapping to `X` and to `T`),
with a common section `δ`. If every point of `P` over `t ∈ T` maps to `w`, then every point of `Q`
over `t` is in the range of `δ`. -/
theorem mem_range_of_mono_residueFieldMap
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W T G P Q : BigFppfOver B S hS}
    (e : yoneda.obj W ⟶ X) (w : W.left.1) (hw : B.Contains (Spec (.of (W.left.1.residueField w))))
    (hmono : Mono (yoneda.map (residueFieldMap B S hS W w hw) ≫ e))
    (gW : W ⟶ G) (gT : T ⟶ G) (j : P ⟶ pullback gW gT) [Mono j]
    (t : (𝒯).obj T)
    (hP : ∀ v : (𝒯).obj P, (𝒯).map (j ≫ pullback.snd gW gT) v = t →
      (𝒯).map (j ≫ pullback.fst gW gT) v = w)
    (a b : Q ⟶ P) (δ : P ⟶ Q)
    (habX : yoneda.map (a ≫ j ≫ pullback.fst gW gT) ≫ e =
      yoneda.map (b ≫ j ≫ pullback.fst gW gT) ≫ e)
    (habT : a ≫ j ≫ pullback.snd gW gT = b ≫ j ≫ pullback.snd gW gT)
    (huniq : ∀ {Y : BigFppfOver B S hS} (u₁ u₂ : Y ⟶ Q), u₁ ≫ a = u₂ ≫ a → u₁ ≫ b = u₂ ≫ b →
      u₁ = u₂)
    (hδa : δ ≫ a = 𝟙 P) (hδb : δ ≫ b = 𝟙 P)
    (q : (𝒯).obj Q) (hq : (𝒯).map (a ≫ j ≫ pullback.snd gW gT) q = t) :
    q ∈ Set.range ((𝒯).map δ) := by
  set hK := B.residueField_spec_contains Q.left.property q
  let φ := residueFieldMap B S hS Q q hK
  have hφ : ∀ x, (𝒯).map φ x = q := fun x => Scheme.fromSpecResidueField_apply q x
  have key : ∀ c : Q ⟶ P, (𝒯).map (c ≫ j ≫ pullback.snd gW gT) q = t →
      ∃ α, α ≫ residueFieldMap B S hS W w hw = φ ≫ c ≫ j ≫ pullback.fst gW gT := fun c hc =>
    exists_comp_residueFieldMap_eq q _ w hw fun x => by
      rw [Functor.map_comp, Scheme.Hom.comp_apply, hφ, Functor.map_comp, Scheme.Hom.comp_apply]
      apply hP
      rwa [← Scheme.Hom.comp_apply, ← Functor.map_comp]
  obtain ⟨α, hα⟩ := key a hq
  obtain ⟨β, hβ⟩ := key b (by rwa [← habT])
  have hαβ : α = β := by
    apply Yoneda.fullyFaithful.map_injective
    rw [← cancel_mono (yoneda.map (residueFieldMap B S hS W w hw) ≫ e), ← Category.assoc,
      ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hα, hβ,
      Functor.map_comp yoneda φ (a ≫ j ≫ pullback.fst gW gT),
      Functor.map_comp yoneda φ (b ≫ j ≫ pullback.fst gW gT), Category.assoc, Category.assoc, habX]
  have hfst : φ ≫ a ≫ j ≫ pullback.fst gW gT = φ ≫ b ≫ j ≫ pullback.fst gW gT := by
    rw [← hα, ← hβ, hαβ]
  have hφab : φ ≫ a = φ ≫ b := by
    rw [← cancel_mono j]
    apply pullback.hom_ext
    · simpa only [Category.assoc] using hfst
    · simp only [Category.assoc, habT]
  have hφδ : (φ ≫ a) ≫ δ = φ := by
    apply huniq <;> simp [hδa, hδb, hφab]
  obtain ⟨x⟩ : Nonempty ((𝒯).obj (residueFieldObject B S hS Q q hK)) :=
    inferInstanceAs (Nonempty (Spec (.of (Q.left.1.residueField q))))
  refine ⟨(𝒯).map (φ ≫ a) x, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hφδ, hφ]

end AlgebraicGeometry.Space

end
