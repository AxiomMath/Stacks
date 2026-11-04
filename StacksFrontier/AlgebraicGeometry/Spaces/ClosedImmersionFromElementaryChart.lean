module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteUnramifiedClosedImmersionNearFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.OffDiagonalPointsOverElementaryChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingProperness

/-!
# A finite piece of an elementary étale chart is a closed subspace near a fibre

Let `f : X ⟶ S₀` be a separated morphism from an algebraic space to a scheme, `e : W ⟶ X` an
étale morphism from a scheme with a point `w` whose residue-field point is a monomorphism into `X`
(the distinguished point of an elementary étale neighbourhood, Stacks 0BBP), and `U ⟶ S₀` a
morphism of schemes. Let `P ⟶ W ×_{S₀} U` be a closed immersion with `P` finite over `U`, all of
whose points over `u ∈ U` map to `w`. Then over an open neighbourhood `V` of `u` the morphism
`P ⟶ W ×_{S₀} U ⟶ X ×_{S₀} U` is a closed immersion.

This combines `AlgebraicGeometry.Space.exists_isOpen_isClosedImmersion_of_isFinite_of_unramified`
with its fibre hypothesis `AlgebraicGeometry.Space.mem_range_of_mono_residueFieldMap`. It is the
step of the proof that families of curves are étale locally schemes (Stacks 0E6F) which moves a
divisor from an étale chart to the family.

## Main results

* `AlgebraicGeometry.Space.exists_isOpen_isClosedImmersion_of_elementaryChart`.

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

/-- Composing with `yoneda.map j` commutes with identifying a composite with a Yoneda image. -/
private theorem yoneda_map_comp_comp_eq {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {P Q U : BigFppfOver B S hS} {f : yoneda.obj Q ⟶ X} {g : X ⟶ yoneda.obj U} {s : Q ⟶ U}
    (j : P ⟶ Q) (h : f ≫ g = yoneda.map s) : (yoneda.map j ≫ f) ≫ g = yoneda.map (j ≫ s) := by
  rw [Category.assoc, h, Functor.map_comp]

/-- **A finite piece of an elementary étale chart is a closed subspace near a fibre.** In the
situation described in the module docstring, with `X_U` a fibre product `X ×_{S₀} U` and
`e_U : W ×_{S₀} U ⟶ X_U` the base change of `e`, there is an open neighbourhood `V` of `u` such
that for every scheme `Y ⟶ X_U` over `V`, the base change `P ×_{X_U} Y ⟶ Y` of
`π = j ≫ e_U` is a closed immersion. -/
theorem exists_isOpen_isClosedImmersion_of_elementaryChart
    {X XU : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hXU : IsAlgebraicSpace B S hS XU)
    {S₀ W U P : BigFppfOver B S hS} (fX : X ⟶ yoneda.obj S₀) (hsep : IsSeparated B S hS fX)
    (e : yoneda.obj W ⟶ X) (he : (MorphismProperty.inverseImage @Etale (𝒯)).presheaf e)
    (w : W.left.1) (hw : B.Contains (Spec (.of (W.left.1.residueField w))))
    (hmono : Mono (yoneda.map (residueFieldMap B S hS W w hw) ≫ e))
    (gW : W ⟶ S₀) (hgW : e ≫ fX = yoneda.map gW) (φ : U ⟶ S₀)
    (qU : XU ⟶ X) (fU : XU ⟶ yoneda.obj U) (sqU : IsPullback qU fU fX (yoneda.map φ))
    (eU : yoneda.obj (pullback gW φ) ⟶ XU)
    (heU₁ : eU ≫ qU = yoneda.map (pullback.fst gW φ) ≫ e)
    (heU₂ : eU ≫ fU = yoneda.map (pullback.snd gW φ))
    (j : P ⟶ pullback gW φ) [_root_.AlgebraicGeometry.IsClosedImmersion ((𝒯).map j)]
    [_root_.AlgebraicGeometry.IsFinite ((𝒯).map (j ≫ pullback.snd gW φ))]
    (u : (𝒯).obj U)
    (hPu : ∀ v, (𝒯).map (j ≫ pullback.snd gW φ) v = u → (𝒯).map (j ≫ pullback.fst gW φ) v = w) :
    ∃ V : ((𝒯).obj U).Opens, u ∈ V ∧
      ∀ {Y Z : BigFppfOver B S hS} (g : yoneda.obj Y ⟶ XU) (pY : Y ⟶ U),
        g ≫ fU = yoneda.map pY → ∀ (a : Z ⟶ P) (b : Z ⟶ Y),
        IsPullback (yoneda.map a) (yoneda.map b) (yoneda.map j ≫ eU) g →
        (∀ y, (𝒯).map pY y ∈ V) → _root_.AlgebraicGeometry.IsClosedImmersion ((𝒯).map b) := by
  -- `e_U` is a base change of `e`, hence étale
  have sqW : IsPullback (yoneda.map (pullback.fst gW φ)) eU e qU := by
    refine IsPullback.of_bot ?_ heU₁.symm sqU
    rw [heU₂, hgW]
    exact (IsPullback.of_hasPullback gW φ).map yoneda
  have := MorphismProperty.relative_isStableUnderBaseChange
    (P := MorphismProperty.inverseImage @Etale (𝒯)) (F := yoneda)
  have heU : (MorphismProperty.inverseImage @Etale (𝒯)).presheaf eU :=
    MorphismProperty.of_isPullback sqW he
  have hunj : (MorphismProperty.inverseImage @Unramified (𝒯)).presheaf (yoneda.map j) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS @Unramified j).2 inferInstance
  have hunU : (MorphismProperty.inverseImage @Unramified (𝒯)).presheaf eU :=
    MorphismProperty.relative_monotone (fun _ _ _ h => by
      show Unramified _
      have : Etale _ := h
      infer_instance) _ heU
  have : (MorphismProperty.inverseImage @Unramified (𝒯)).IsStableUnderComposition :=
    ⟨fun f g hf hg => by
      show Unramified _
      rw [Functor.map_comp]
      exact MorphismProperty.comp_mem @Unramified _ _ hf hg⟩
  have hun : (MorphismProperty.inverseImage @Unramified (𝒯)).presheaf (yoneda.map j ≫ eU) :=
    MorphismProperty.comp_mem _ _ _ hunj hunU
  have hsepU : IsSeparated B S hS fU := isSeparated_baseChange_of_isPullback sqU hsep
  have hπ := yoneda_map_comp_comp_eq j heU₂
  have : Mono j := ⟨fun g₁ g₂ h => (𝒯).map_injective ((cancel_mono ((𝒯).map j)).1 (by
    rw [← Functor.map_comp, ← Functor.map_comp, h]))⟩
  refine exists_isOpen_isClosedImmersion_of_isFinite_of_unramified hXU fU hsepU
    (j ≫ pullback.snd gW φ) (yoneda.map j ≫ eU) hπ hun u ?_
  intro Q a b δ sq hδa hδb q hq
  refine mem_range_of_mono_residueFieldMap e w hw hmono gW φ j u hPu a b δ ?_ ?_ ?_ hδa hδb q
    (by simpa only [Category.assoc] using hq)
  · have := sq.w =≫ qU
    simp only [Category.assoc, heU₁] at this
    simpa only [Functor.map_comp, Category.assoc] using this
  · apply Yoneda.fullyFaithful.map_injective
    have := sq.w =≫ fU
    simp only [Category.assoc, heU₂] at this
    simpa only [Functor.map_comp, Category.assoc] using this
  · intro Y u₁ u₂ h₁ h₂
    apply Yoneda.fullyFaithful.map_injective
    apply sq.hom_ext
    · rw [← Functor.map_comp, ← Functor.map_comp, h₁]
    · rw [← Functor.map_comp, ← Functor.map_comp, h₂]

/-- **The finite piece is a closed subspace over a neighbourhood.** In the situation of
`AlgebraicGeometry.Space.exists_isOpen_isClosedImmersion_of_elementaryChart`, there is an open
neighbourhood `V` of `u` such that for every morphism `ι : U' ⟶ U` of the site with image in `V`,
the morphism `P ×_U U' ⟶ X_U ×_U U'` induced by `π = j ≫ e_U` is a closed immersion of
algebraic spaces. -/
theorem exists_isOpen_isClosedImmersion_baseChange_of_elementaryChart
    {X XU : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hXU : IsAlgebraicSpace B S hS XU)
    {S₀ W U P : BigFppfOver B S hS} (fX : X ⟶ yoneda.obj S₀) (hsep : IsSeparated B S hS fX)
    (e : yoneda.obj W ⟶ X) (he : (MorphismProperty.inverseImage @Etale (𝒯)).presheaf e)
    (w : W.left.1) (hw : B.Contains (Spec (.of (W.left.1.residueField w))))
    (hmono : Mono (yoneda.map (residueFieldMap B S hS W w hw) ≫ e))
    (gW : W ⟶ S₀) (hgW : e ≫ fX = yoneda.map gW) (φ : U ⟶ S₀)
    (qU : XU ⟶ X) (fU : XU ⟶ yoneda.obj U) (sqU : IsPullback qU fU fX (yoneda.map φ))
    (eU : yoneda.obj (pullback gW φ) ⟶ XU)
    (heU₁ : eU ≫ qU = yoneda.map (pullback.fst gW φ) ≫ e)
    (heU₂ : eU ≫ fU = yoneda.map (pullback.snd gW φ))
    (j : P ⟶ pullback gW φ) [_root_.AlgebraicGeometry.IsClosedImmersion ((𝒯).map j)]
    [_root_.AlgebraicGeometry.IsFinite ((𝒯).map (j ≫ pullback.snd gW φ))]
    (u : (𝒯).obj U)
    (hPu : ∀ v, (𝒯).map (j ≫ pullback.snd gW φ) v = u → (𝒯).map (j ≫ pullback.fst gW φ) v = w) :
    ∃ V : ((𝒯).obj U).Opens, u ∈ V ∧
      ∀ {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_ : IsAlgebraicSpace B S hS X')
        {U' P' : BigFppfOver B S hS} (ι : U' ⟶ U), (∀ t', (𝒯).map ι t' ∈ V) →
        ∀ (q : X' ⟶ XU) (f' : X' ⟶ yoneda.obj U'), IsPullback q f' fU (yoneda.map ι) →
        ∀ (pP : P' ⟶ P) (p' : P' ⟶ U'), IsPullback pP p' (j ≫ pullback.snd gW φ) ι →
        ∀ (π' : yoneda.obj P' ⟶ X'), π' ≫ q = yoneda.map pP ≫ yoneda.map j ≫ eU →
          π' ≫ f' = yoneda.map p' → IsClosedImmersion B S hS π' := by
  obtain ⟨V, hu, hV⟩ := exists_isOpen_isClosedImmersion_of_elementaryChart hXU fX hsep e he w hw
    hmono gW hgW φ qU fU sqU eU heU₁ heU₂ j u hPu
  refine ⟨V, hu, fun {X'} hX' {U' P'} ι hι q f' sqX pP p' sqP π' h₁ h₂ => ?_⟩
  have hπ := yoneda_map_comp_comp_eq j heU₂
  exact isClosedImmersion_of_isPullback_of_forall_mem hX' fU (j ≫ pullback.snd gW φ)
    (yoneda.map j ≫ eU) hπ V hV ι hι q f' sqX pP p' sqP π' h₁ h₂

end AlgebraicGeometry.Space

end
