module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivationMovedLiftConormal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftChartKernel

/-!
# Comorphisms and Equation 0619 under precomposition with a morphism of thickenings

Let `(h, h') : (Z₂ ⊂ X₂) ⟶ (Z ⊂ X)` be a morphism of thickenings of algebraic spaces
(`i₂ ≫ h' = h ≫ i`) and let `c : X ⟶ W` be a morphism whose restriction to `Z` factors through a
closed subspace `W₀ ⊆ W` (`i ≫ c = e₀ ≫ j`).  This file proves the two naturality statements the
compatibility of the action `θ · c` of [Stacks Project, Tag 0CK6] with restriction rests on.

* The comorphism of `h' ≫ c`, read as a map `j^{-1}𝒪_W ⟶ (h ≫ e₀)_*(i₂^{-1}𝒪_{X₂})` on the
  small étale site of `W₀`, is the comorphism of `c`, read as a map
  `j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)`, followed by the direct image along `e₀` of the comorphism
  `i^{-1}𝒪_X ⟶ h_*(i₂^{-1}𝒪_{X₂})` of `h'` and by the comparison of iterated direct images
  (`AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp_source`).
* The derivation attached by Equation [Stacks Project, Tag 0619] to the composite
  `(h ≫ e)^*Ω ≅ h^*e^*Ω ⟶ h^*C ⟶ C₂` of `h^*θ` with a map `γ : h^*C ⟶ C₂` is the derivation
  attached to `θ` followed by the direct image of the transpose `C ⟶ h_*C₂` of `γ`
  (`AlgebraicGeometry.Space.derivationFamilyOfHom_comp`).

## Implementation notes

The diagram chases are carried out at abstract categories
(`AlgebraicGeometry.Space.structureSharpThroughThickening_source_chase`,
`AlgebraicGeometry.Space.restrictedSharpThroughThickening_source_chase`) and instantiated with
every equation handed over explicitly: rewriting a comparison of iterated direct images in place
over the small étale ringed site exhausts the elaboration budget.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (3)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section PushforwardComp

variable {V₁ V₂ V₃ V₄ : AlgebraicSpaces B S hS}

/-- **The associativity cocycle law of [Stacks Project, Tag 03G2], part (3), at sheaves of
rings**, for the comparison `g_*(f_*O) ⟶ (f ≫ g)_*O` of iterated direct images. -/
theorem pushforwardRingSheafCompHom_assoc (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃) (k : V₃ ⟶ V₄)
    (O : Sheaf (SmallEtale.topology B S hS V₁.1) RingCat.{u}) :
    pullbackRingSheafMap (SmallEtale.topology B S hS V₄.1)
          (smallToposMorphismTypeU B S hS k).pushforward
          (pushforwardRingSheafCompHom B S hS f g O) ≫
        pushforwardRingSheafCompHom B S hS (f ≫ g) k O =
      pushforwardRingSheafCompHom B S hS g k
          (pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₂.1)
            (smallToposMorphismTypeU B S hS f).pushforward O) ≫
        pushforwardRingSheafCompHom B S hS f (g ≫ k) O := by
  refine (sheafCompose (SmallEtale.topology B S hS V₄.1)
    (CategoryTheory.forget RingCat.{u})).map_injective ?_
  simp only [pushforwardRingSheafCompHom, Functor.map_comp,
    sheafCompose_map_pullbackRingSheafComp_hom, ringSheafMap_pullbackRingSheafMap, Category.assoc]
  exact smallToposMorphismTypeU_comp_assoc B S hS f g k _

/-- An `eqToHom` between direct images along two equal morphisms slides across the comparison
of iterated direct images. -/
theorem map_eqToHom_comp_pushforwardRingSheafCompHom {m m' : V₁ ⟶ V₂} (p : m = m')
    (k : V₂ ⟶ V₃) (O : Sheaf (SmallEtale.topology B S hS V₁.1) RingCat.{u}) :
    pullbackRingSheafMap (SmallEtale.topology B S hS V₃.1)
          (smallToposMorphismTypeU B S hS k).pushforward
          (eqToHom (congrArg (fun n : V₁ ⟶ V₂ ↦
            pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₂.1)
              (smallToposMorphismTypeU B S hS n).pushforward O) p)) ≫
        pushforwardRingSheafCompHom B S hS m' k O =
      pushforwardRingSheafCompHom B S hS m k O ≫
        eqToHom (congrArg (fun n : V₁ ⟶ V₂ ↦
            pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₃.1)
              (smallToposMorphismTypeU B S hS (n ≫ k)).pushforward O) p) := by
  subst p
  simp only [eqToHom_refl, pullbackRingSheafMap_id, Category.id_comp, Category.comp_id]

end PushforwardComp

/-! ### The comorphism read through a thickening, under precomposition -/

section Source

variable {X₂ X W : AlgebraicSpaces B S hS} (Z₂ : ClosedSubspaces B S hS X₂.1)
  (Z : ClosedSubspaces B S hS X.1) (h' : X₂ ⟶ X)
  (h : (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
  (hsq : subspaceInclusion B S hS X₂ Z₂ ≫ h' = h ≫ subspaceInclusion B S hS X Z)

include hsq in
/-- Along a morphism of thickenings `(h, h') : (Z₂ ⊂ X₂) ⟶ (Z ⊂ X)`, the restriction of
`h' ≫ c` to `Z₂` is `h` followed by the restriction of `c` to `Z`: `i₂ ≫ h' ≫ c = h ≫ i ≫ c`. -/
theorem comp_assoc_of_square (c : X ⟶ W) :
    subspaceInclusion B S hS X₂ Z₂ ≫ h' ≫ c = h ≫ subspaceInclusion B S hS X Z ≫ c := by
  rw [← Category.assoc, hsq, Category.assoc]

/-- The diagram chase behind
`AlgebraicGeometry.Space.structureSharpThroughThickeningAt_comp_source`, at an abstract
category: the terms over the small étale ringed site exhaust the elaboration budget as soon as
a comparison is rewritten in place. -/
theorem structureSharpThroughThickening_source_chase {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (Fc : 𝒟 ⥤ 𝒞)
    {A : 𝒞} {OX P1 P2 P3 P4 P5 IX : 𝒟} {Q Q₂ R R₄ N N' : 𝒞}
    {s : A ⟶ Fc.obj OX} {hs' : OX ⟶ P1} {hu₂ : P1 ⟶ P2} {hc₂ : P2 ⟶ P3} {hE : P3 ⟶ P4}
    {hci : P4 ⟶ P5} {u : OX ⟶ IX} {iσ : IX ⟶ P5} {hk : P5 ⟶ P4}
    {cmpHc : Fc.obj P1 ⟶ Q} {sComp : A ⟶ Q} {U : Q ⟶ Q₂} {cmpI2 : Q₂ ⟶ R} {Ep Ep' : R ⟶ R₄}
    {cmpHc' : Fc.obj P2 ⟶ Q₂} {cmpA : Fc.obj P3 ⟶ R} {cmpB : Fc.obj P4 ⟶ R₄}
    {cmpIc' : Fc.obj P5 ⟶ N'} {cmpHi : N' ⟶ R₄} {cmpIc : Fc.obj IX ⟶ N} {σ' : N ⟶ N'}
    {st : OX ⟶ P4} {L : A ⟶ R₄} {M : A ⟶ N}
    (e1 : u ≫ iσ = st ≫ hci) (e2 : Fc.map iσ ≫ cmpIc' = cmpIc ≫ σ')
    (e3 : s ≫ Fc.map hs' ≫ cmpHc = sComp) (e4 : Fc.map hu₂ ≫ cmpHc' = cmpHc ≫ U)
    (e5 : Fc.map hc₂ ≫ cmpA = cmpHc' ≫ cmpI2) (e6 : Fc.map hk ≫ cmpB = cmpIc' ≫ cmpHi)
    (e7 : hci ≫ hk = 𝟙 P4) (e8 : Fc.map hE ≫ cmpB = cmpA ≫ Ep')
    (hst : st = (hs' ≫ hu₂ ≫ hc₂) ≫ hE) (hL : L = (sComp ≫ U ≫ cmpI2) ≫ Ep)
    (hM : M = s ≫ Fc.map u ≫ cmpIc) (hEp : Ep = Ep') :
    L = M ≫ σ' ≫ cmpHi := by
  subst hst hL hM hEp
  have e1' : Fc.map u ≫ Fc.map iσ =
      Fc.map hs' ≫ Fc.map hu₂ ≫ Fc.map hc₂ ≫ Fc.map hE ≫ Fc.map hci := by
    simp only [← Fc.map_comp, e1, Category.assoc]
  have e7' : Fc.map hci ≫ Fc.map hk = 𝟙 _ := by rw [← Fc.map_comp, e7, Fc.map_id]
  calc ((sComp ≫ U ≫ cmpI2) ≫ Ep)
      = s ≫ Fc.map hs' ≫ Fc.map hu₂ ≫ Fc.map hc₂ ≫ Fc.map hE ≫ cmpB := by
        rw [e8, reassoc_of% e5, reassoc_of% e4, ← e3]; simp only [Category.assoc]
    _ = s ≫ Fc.map u ≫ Fc.map iσ ≫ Fc.map hk ≫ cmpB := by
        rw [reassoc_of% e1', reassoc_of% e7']
    _ = (s ≫ Fc.map u ≫ cmpIc) ≫ σ' ≫ cmpHi := by
        rw [e6, reassoc_of% e2]; simp only [Category.assoc]

/-- `AlgebraicGeometry.Space.structureSharpThroughThickening` with its comparison of iterated
direct images written as `AlgebraicGeometry.Space.pushforwardRingSheafCompHom`. -/
theorem structureSharpThroughThickening_eq_compHom {X W : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS X.1) (c : X ⟶ W) :
    structureSharpThroughThickening B S hS Z c =
      structureSharp B S hS c ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map
          (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z))
            (structureRingSheaf B S hS X)) ≫
        pushforwardRingSheafCompHom B S hS (subspaceInclusion B S hS X Z) c
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) :=
  rfl

/-- The defining equation of `AlgebraicGeometry.Space.structureSharpThroughThickeningAt`. -/
theorem structureSharpThroughThickeningAt_eq {X W : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS X.1) (c : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e) :
    structureSharpThroughThickeningAt B S hS Z c e h =
      structureSharpThroughThickening B S hS Z c ≫
        eqToHom (congrArg (fun m : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W ↦
          pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
            (smallToposMorphismTypeU B S hS m).pushforward
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))) h) :=
  rfl

/-- `AlgebraicGeometry.Space.structureSharpThroughThickeningAt` unfolded to the comorphism, the
direct image of the unit and the comparison of iterated direct images, followed by an `eqToHom`. -/
private theorem structureSharpThroughThickeningAt_eq_compHom {X W : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS X.1) (c : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e) :
    structureSharpThroughThickeningAt B S hS Z c e h =
      (structureSharp B S hS c ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map
          (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z))
            (structureRingSheaf B S hS X)) ≫
        pushforwardRingSheafCompHom B S hS (subspaceInclusion B S hS X Z) c
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))) ≫
        eqToHom (congrArg (fun m : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W ↦
          pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
            (smallToposMorphismTypeU B S hS m).pushforward
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))) h) :=
  (structureSharpThroughThickeningAt_eq B S hS Z c e h).trans
    (congrArg (· ≫ _) (structureSharpThroughThickening_eq_compHom B S hS Z c))

/-- **The comorphism read through a thickening, under precomposition with a morphism of
thickenings** `(h, h') : (Z₂ ⊂ X₂) ⟶ (Z ⊂ X)`: the comorphism of `h' ≫ c` read in
`(i₂ ≫ h' ≫ c)_*(i₂^{-1}𝒪_{X₂})` is that of `c` read in `(i ≫ c)_*(i^{-1}𝒪_X)`, followed by the
direct image of the comorphism `i^{-1}𝒪_X ⟶ h_*(i₂^{-1}𝒪_{X₂})` of `h'` and by the comparison
of iterated direct images. -/
theorem structureSharpThroughThickeningAt_comp_source (c : X ⟶ W) :
    structureSharpThroughThickeningAt B S hS Z₂ (h' ≫ c)
        (h ≫ subspaceInclusion B S hS X Z ≫ c) (comp_assoc_of_square B S hS Z₂ Z h' h hsq c) =
      structureSharpThroughThickening B S hS Z c ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS X Z ≫ c))).map
          (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq) ≫
        pushforwardRingSheafCompHom B S hS h (subspaceInclusion B S hS X Z ≫ c)
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂)) := by
  have e1 := ringUnit_comp_map_restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq
  have e2 := pushforwardRingSheafCompHom_naturality B S hS (subspaceInclusion B S hS X Z) c
    (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq)
  have e3 := structureSharp_comp_pushforwardRingSheafCompHom B S hS h' c
  have e4 := pushforwardRingSheafCompHom_naturality B S hS h' c
    (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X₂ Z₂))
      (structureRingSheaf B S hS X₂))
  have e5 := pushforwardRingSheafCompHom_assoc B S hS (subspaceInclusion B S hS X₂ Z₂) h' c
    (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂))
  have e6 := pushforwardRingSheafCompHom_assoc B S hS h (subspaceInclusion B S hS X Z) c
    (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂))
  have e7 := pushforwardRingSheafCompInv_comp_hom B S hS h (subspaceInclusion B S hS X Z)
    (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂))
  have e8 := map_eqToHom_comp_pushforwardRingSheafCompHom B S hS hsq c
    (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂))
  exact structureSharpThroughThickening_source_chase
    (pushforwardRingFunctor (smallToposMorphismTypeU B S hS c))
    e1 e2 e3 e4 e5 e6 e7 e8
    (structureSharpThroughThickeningAt_eq_compHom B S hS Z₂ h' _ hsq)
    (structureSharpThroughThickeningAt_eq_compHom B S hS Z₂ (h' ≫ c) _ _)
    (structureSharpThroughThickening_eq_compHom B S hS Z c) rfl

include hsq in
/-- `AlgebraicGeometry.Space.structureSharpThroughThickeningAt_comp_source` with the restriction
of `c` to the thickening named. -/
theorem structureSharpThroughThickeningAt_comp_source_at (c : X ⟶ W)
    (κ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (hκ : subspaceInclusion B S hS X Z ≫ c = κ)
    (hκ₂ : subspaceInclusion B S hS X₂ Z₂ ≫ h' ≫ c = h ≫ κ) :
    structureSharpThroughThickeningAt B S hS Z₂ (h' ≫ c) (h ≫ κ) hκ₂ =
      structureSharpThroughThickeningAt B S hS Z c κ hκ ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS κ)).map
          (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq) ≫
        pushforwardRingSheafCompHom B S hS h κ
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂)) := by
  subst hκ
  refine (structureSharpThroughThickeningAt_comp_source B S hS Z₂ Z h' h hsq c).trans ?_
  rw [structureSharpThroughThickeningAt_eq, eqToHom_refl, Category.comp_id]

/-- The diagram chase behind
`AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp_source`, at an abstract
category. -/
theorem restrictedSharpThroughThickening_source_chase {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (G : 𝒟 ⥤ 𝒞)
    {A : 𝒞} {B0 T T' T₂ : 𝒟} {R R₁ R₁' : 𝒞}
    {η : A ⟶ G.obj B0} {r₂ : B0 ⟶ T₂} {r : B0 ⟶ T} {es : T ⟶ T'} {ch : T' ⟶ T₂}
    {a₂ : A ⟶ R} {ci₂ : R ⟶ G.obj T₂} {a : A ⟶ R₁} {ci : R₁ ⟶ G.obj T}
    {σj : R₁ ⟶ R₁'} {ci' : R₁' ⟶ G.obj T'} {chj : R₁' ⟶ R} {cm : G.obj T' ⟶ R₁'}
    {cm₂ : G.obj T₂ ⟶ R}
    (E1 : η ≫ G.map r₂ = a₂ ≫ ci₂) (E2 : η ≫ G.map r = a ≫ ci)
    (E3 : σj ≫ ci' = ci ≫ G.map es) (E4 : a₂ = a ≫ σj ≫ chj)
    (Pa : G.map ch ≫ cm₂ = cm ≫ chj) (I₁ : ci' ≫ cm = 𝟙 _) (I₂ : cm₂ ≫ ci₂ = 𝟙 _) :
    η ≫ G.map r₂ = η ≫ G.map (r ≫ es ≫ ch) := by
  have E6 : ci' ≫ G.map ch = chj ≫ ci₂ := by
    calc ci' ≫ G.map ch = ci' ≫ G.map ch ≫ cm₂ ≫ ci₂ := by rw [I₂, Category.comp_id]
      _ = chj ≫ ci₂ := by rw [reassoc_of% Pa, reassoc_of% I₁]
  rw [E1, E4, G.map_comp, G.map_comp, reassoc_of% E2, ← reassoc_of% E3, E6]
  simp only [Category.assoc]

include hsq in
/-- The square of a morphism of thickenings `(e₀, c)` precomposed with `(h, h')`: if
`i ≫ c = e₀ ≫ j`, then `i₂ ≫ h' ≫ c = (h ≫ e₀) ≫ j`. -/
theorem comp_assoc_of_square_restricted (W₀ : ClosedSubspaces B S hS W.1) (c : X ⟶ W)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀) :
    subspaceInclusion B S hS X₂ Z₂ ≫ h' ≫ c = (h ≫ e₀) ≫ subspaceInclusion B S hS W W₀ := by
  rw [comp_assoc_of_square B S hS Z₂ Z h' h hsq c, hc, Category.assoc]

/-- **The comorphism read on a closed subspace of the target, under precomposition with a
morphism of thickenings** `(h, h') : (Z₂ ⊂ X₂) ⟶ (Z ⊂ X)`: the transported comorphism
`j^{-1}𝒪_W ⟶ (h ≫ e₀)_*(i₂^{-1}𝒪_{X₂})` of `h' ≫ c` is that of `c` followed by the direct image
along `e₀` of the transported comorphism `i^{-1}𝒪_X ⟶ h_*(i₂^{-1}𝒪_{X₂})` of `h'` and by the
comparison of iterated direct images. -/
theorem restrictedSharpThroughThickening_comp_source (W₀ : ClosedSubspaces B S hS W.1)
    (c : X ⟶ W)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀) :
    restrictedSharpThroughThickening B S hS Z₂ W₀ (h' ≫ c) (h ≫ e₀)
        (comp_assoc_of_square_restricted B S hS Z₂ Z h' h hsq W₀ c e₀ hc) =
      restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS e₀)).map
          (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq) ≫
        pushforwardRingSheafCompHom B S hS h e₀
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂)) := by
  refine ((ringImageAdjunction (smallToposMorphismTypeU B S hS
    (subspaceInclusion B S hS W W₀))).homEquiv _ _).injective ?_
  rw [ringImageAdjunction_homEquiv_apply, ringImageAdjunction_homEquiv_apply]
  exact restrictedSharpThroughThickening_source_chase
    (pushforwardRingFunctor (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀)))
    (ringUnit_comp_map_restrictedSharpThroughThickening B S hS Z₂ W₀ (h' ≫ c) (h ≫ e₀) _)
    (ringUnit_comp_map_restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc)
    (pushforwardRingSheafCompInv_naturality B S hS e₀ (subspaceInclusion B S hS W W₀)
      (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq))
    (structureSharpThroughThickeningAt_comp_source_at B S hS Z₂ Z h' h hsq c _ hc _)
    (pushforwardRingSheafCompHom_assoc B S hS h e₀ (subspaceInclusion B S hS W W₀) _)
    (pushforwardRingSheafCompInv_comp_hom B S hS e₀ (subspaceInclusion B S hS W W₀) _)
    (pushforwardRingSheafCompHom_comp_inv B S hS (h ≫ e₀) (subspaceInclusion B S hS W W₀) _)

end Source

/-! ### Equation 0619 under precomposition -/

section Derivation

variable {P Q R T : AlgebraicSpaces B S hS}

/-- The derivation attached to `θ` by Equation [Stacks Project, Tag 0619], evaluated on a
section: the universal derivation followed by the transpose of `θ`. -/
theorem derivationFamilyOfHom_eq_homEquiv (b : R ⟶ T) (e : Q ⟶ R)
    (C : Modules.{u, u} B S hS Q.1 Q.2)
    (θ : (modulePullback B S hS e).obj (sheafOfDifferentials B S hS b) ⟶ C)
    (V : (SmallEtale B S hS R.1)ᵒᵖ) (y : (structureRingSheaf B S hS R).obj.obj V) :
    derivationFamilyOfHom B S hS b e C θ V y =
      ((((modulePullbackAdjunction B S hS e).homEquiv _ _ θ).val.app V).hom
        ((universalDerivation B S hS b).d y)) :=
  rfl

/-- Evaluating a composite of morphisms of modules on a local section. -/
theorem modulesHom_comp_val_app_hom {Y : AlgebraicSpaces B S hS}
    {M N K : Modules.{u, u} B S hS Y.1 Y.2} (a : M ⟶ N) (c : N ⟶ K)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ) (t : M.val.obj U) :
    ((a ≫ c).val.app U).hom t = (c.val.app U).hom ((a.val.app U).hom t) :=
  rfl

/-- **Equation [Stacks Project, Tag 0619] under precomposition.**  For `θ : e^*Ω_{R/T} ⟶ C`
and a map `γ : h^*C ⟶ C₂`, the derivation attached to the composite
`(h ≫ e)^*Ω_{R/T} ≅ h^*e^*Ω_{R/T} ⟶ h^*C ⟶ C₂` is the derivation attached to `θ` followed by
the direct image along `e` of the transpose `C ⟶ h_*C₂` of `γ` and by the comparison
`e_*h_* ≅ (h ≫ e)_*`. -/
theorem derivationFamilyOfHom_comp (b : R ⟶ T) (h : P ⟶ Q) (e : Q ⟶ R)
    (C : Modules.{u, u} B S hS Q.1 Q.2) (C₂ : Modules.{u, u} B S hS P.1 P.2)
    (θ : (modulePullback B S hS e).obj (sheafOfDifferentials B S hS b) ⟶ C)
    (γ : (modulePullback B S hS h).obj C ⟶ C₂) (V : (SmallEtale B S hS R.1)ᵒᵖ)
    (y : (structureRingSheaf B S hS R).obj.obj V) :
    derivationFamilyOfHom B S hS b (h ≫ e) C₂
        ((modulePullbackCompIso B S hS h e).inv.app (sheafOfDifferentials B S hS b) ≫
          (modulePullback B S hS h).map θ ≫ γ) V y =
      (((modulePushforward B S hS e).map
            ((modulePullbackAdjunction B S hS h).homEquiv _ _ γ) ≫
          (modulePushforwardCompIso B S hS h e).hom.app C₂).val.app V).hom
        (derivationFamilyOfHom B S hS b e C θ V y) := by
  have step : (modulePullbackAdjunction B S hS (h ≫ e)).homEquiv _ _
      ((modulePullbackCompIso B S hS h e).inv.app (sheafOfDifferentials B S hS b) ≫
          (modulePullback B S hS h).map θ ≫ γ) =
      (modulePullbackAdjunction B S hS e).homEquiv _ _ θ ≫
        (modulePushforward B S hS e).map
            ((modulePullbackAdjunction B S hS h).homEquiv _ _ γ) ≫
          (modulePushforwardCompIso B S hS h e).hom.app C₂ := by
    rw [homEquiv_modulePullbackCompIso_inv_app_comp, Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_right, Category.assoc]
  rw [derivationFamilyOfHom_eq_homEquiv, derivationFamilyOfHom_eq_homEquiv, step,
    modulesHom_comp_val_app_hom]

end Derivation

end AlgebraicGeometry.Space

end
