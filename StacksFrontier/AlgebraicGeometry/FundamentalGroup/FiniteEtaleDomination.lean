module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ClosedImmersionPositiveCharacteristic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleUniversalHomeomorphismDescent

/-!
# Domination of finite étale covers along a morphism

Let `g : X' ⟶ X` be a morphism of schemes. Say that `g` **dominates finite étale covers** if every
finite étale cover `V` of `X'` maps monomorphically into the base change `U ×_X X'` of some finite
étale cover `U` of `X`. When `X` and `X'` are connected this forces the induced homomorphism of
étale fundamental groups `π₁(X', x') → π₁(X, g ∘ x')` to be injective
(`AlgebraicGeometry.injective_etaleFundamentalGroupMap_of_forall_exists_mono`); it is the criterion
of Stacks Tag 0BN7 read on schemes.

This file proves that the property holds for finite étale morphisms, for universal
homeomorphisms, is stable under composition, and passes to cofiltered limits of quasi-compact
quasi-separated schemes with affine transition morphisms (Stacks Tag 0BTV). These are the four
steps of the proof of injectivity in Stacks Tag 0BTX.

## Main definitions

* `AlgebraicGeometry.DominatesFiniteEtale` — the property.

## Main results

* `AlgebraicGeometry.dominatesFiniteEtale_of_finiteEtale`,
  `AlgebraicGeometry.dominatesFiniteEtale_of_universalHomeomorphism`,
  `AlgebraicGeometry.DominatesFiniteEtale.comp`,
  `AlgebraicGeometry.dominatesFiniteEtale_of_isLimit`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- A morphism `g : X' ⟶ X` **dominates finite étale covers** if every finite étale cover of `X'`
maps monomorphically into the base change of a finite étale cover of `X`. -/
def DominatesFiniteEtale {X' X : Scheme.{u}} (g : X' ⟶ X) : Prop :=
  ∀ V : FiniteEtaleOver X', ∃ (U : FiniteEtaleOver X)
    (j : V ⟶ (finiteEtaleBaseChange g).obj U), Mono j.left

/-- A morphism of pullbacks over the same second factor which is compatible with a monomorphism
of the first factors and with the second projections is a monomorphism. -/
lemma mono_of_comp_pullback_fst {Y Z A A' : Scheme.{u}} {f : A ⟶ Z} {f' : A' ⟶ Z} {g : Y ⟶ Z}
    (φ : pullback f g ⟶ pullback f' g) (a : A ⟶ A') [Mono a]
    (h₁ : φ ≫ pullback.fst f' g = pullback.fst f g ≫ a)
    (h₂ : φ ≫ pullback.snd f' g = pullback.snd f g) : Mono φ := by
  constructor
  intro T u v h
  apply pullback.hom_ext
  · rw [← cancel_mono a, Category.assoc, Category.assoc, ← h₁, ← Category.assoc, h,
      Category.assoc]
  · rw [← h₂, ← Category.assoc, h, Category.assoc]

/-- Base change along a morphism preserves monomorphisms between finite étale covers. -/
lemma mono_finiteEtaleBaseChange_map_left {X' X : Scheme.{u}} (g : X' ⟶ X)
    {U U' : FiniteEtaleOver X} (j : U ⟶ U') [Mono j.left] :
    Mono ((finiteEtaleBaseChange g).map j).left :=
  mono_of_comp_pullback_fst (f := U.hom) (f' := U'.hom) _ j.left
    (finiteEtaleBaseChange_map_left_fst g j)
    (MorphismProperty.Over.w ((finiteEtaleBaseChange g).map j))

/-- An isomorphism of finite étale covers has an invertible, hence monomorphic, underlying
morphism. -/
lemma mono_left_of_iso {X : Scheme.{u}} {V W : FiniteEtaleOver X} (e : V ≅ W) :
    Mono e.hom.left :=
  have : IsIso e.hom.left := ⟨e.inv.left, congrArg (·.left) e.hom_inv_id,
    congrArg (·.left) e.inv_hom_id⟩
  inferInstance

/-- A monomorphism into a base change, followed by the base change of a monomorphism and the
composition isomorphism, is a monomorphism. -/
private theorem mono_left_comp_map_baseChangeComp {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U)
    (fg : S ⟶ U) (hfg : fg = f ≫ g) {V : FiniteEtaleOver S} {B : FiniteEtaleOver T}
    {A : FiniteEtaleOver U} (a : V ⟶ (finiteEtaleBaseChange f).obj B) [Mono a.left]
    (j : B ⟶ (finiteEtaleBaseChange g).obj A) [Mono j.left] :
    Mono (a ≫ (finiteEtaleBaseChange f).map j ≫
      ((finiteEtaleBaseChangeComp f g fg hfg).app A).inv).left := by
  have := mono_finiteEtaleBaseChange_map_left f j
  have := mono_left_of_iso ((finiteEtaleBaseChangeComp f g fg hfg).app A).symm
  simp only [MorphismProperty.Comma.comp_left]
  infer_instance

/-- **Finite étale morphisms dominate finite étale covers.** A finite étale cover `V` of `X'` is a
finite étale cover of `X` by composition, and its graph `V ⟶ V ×_X X'` is a monomorphism. -/
theorem dominatesFiniteEtale_of_finiteEtale {X' X : Scheme.{u}} (g : X' ⟶ X) [IsFinite g]
    [Etale g] : DominatesFiniteEtale g := by
  intro V
  have hV : finiteEtale V.hom := V.prop
  have : IsFinite V.hom := hV.1
  have : Etale V.hom := hV.2
  let U : FiniteEtaleOver X := MorphismProperty.Over.mk ⊤ (V.hom ≫ g) ⟨inferInstance, inferInstance⟩
  let j : V ⟶ (finiteEtaleBaseChange g).obj U :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 V.left) V.hom (by exact Category.id_comp _))
      (pullback.lift_snd _ _ _)
  refine ⟨U, j, ?_⟩
  have : IsSplitMono j.left := ⟨⟨⟨pullback.fst _ _, pullback.lift_fst _ _ _⟩⟩⟩
  infer_instance

/-- **Universal homeomorphisms dominate finite étale covers**: every finite étale cover of the
source is a base change (Stacks Tag 0BQN). -/
theorem dominatesFiniteEtale_of_universalHomeomorphism {X' X : Scheme.{u}} (g : X' ⟶ X)
    [UniversalHomeomorphism g] : DominatesFiniteEtale g := by
  intro V
  obtain ⟨U, ⟨e⟩⟩ := exists_finiteEtaleBaseChange_iso_of_universalHomeomorphism g V
  exact ⟨U, e.inv, mono_left_of_iso e.symm⟩

/-- **Domination is stable under composition.** -/
theorem DominatesFiniteEtale.comp {X'' X' X : Scheme.{u}} {g₁ : X'' ⟶ X'} {g₂ : X' ⟶ X}
    (h₁ : DominatesFiniteEtale g₁) (h₂ : DominatesFiniteEtale g₂) :
    DominatesFiniteEtale (g₁ ≫ g₂) := by
  intro V
  obtain ⟨U₁, j₁, hj₁⟩ := h₁ V
  obtain ⟨U₂, j₂, hj₂⟩ := h₂ U₁
  exact ⟨U₂, _, mono_left_comp_map_baseChangeComp g₁ g₂ _ rfl j₁ j₂⟩

/-- Domination only depends on the morphism up to equality. -/
theorem DominatesFiniteEtale.of_eq {X' X : Scheme.{u}} {g g' : X' ⟶ X}
    (h : DominatesFiniteEtale g) (hgg' : g = g') : DominatesFiniteEtale g' :=
  hgg' ▸ h

section Limit

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]

/-- **Domination passes to limits.** Let `X' = lim Xᵢ` be the limit of a cofiltered system of
quasi-compact and quasi-separated schemes with affine transition morphisms, over a scheme `X`
through morphisms `pᵢ : Xᵢ ⟶ X`. If every `pᵢ` dominates finite étale covers, so does
`X' ⟶ X`: a finite étale cover of `X'` comes from a stage (Stacks Tag 0BTV). -/
theorem dominatesFiniteEtale_of_isLimit (hc : IsLimit c) {X : Scheme.{u}} (g : c.pt ⟶ X)
    (p : ∀ i, D.obj i ⟶ X) (hp : ∀ i, c.π.app i ≫ p i = g)
    (hdom : ∀ i, DominatesFiniteEtale (p i)) : DominatesFiniteEtale g := by
  intro V
  obtain ⟨i, B, ⟨e⟩⟩ := exists_finiteEtale_model D c hc V
  obtain ⟨U, j, hj⟩ := hdom i B
  have := mono_left_of_iso e
  exact ⟨U, _, mono_left_comp_map_baseChangeComp (c.π.app i) (p i) g (hp i).symm e.hom j⟩

end Limit

/-- **Injectivity from domination.** A morphism of connected schemes that dominates finite étale
covers induces an injective homomorphism of étale fundamental groups. -/
theorem injective_etaleFundamentalGroupMap_of_dominatesFiniteEtale {X' X : Scheme.{u}}
    [ConnectedSpace X'] [ConnectedSpace X] (g : X' ⟶ X) (x : GeometricPoint X')
    (h : DominatesFiniteEtale g) : Function.Injective (etaleFundamentalGroupMap g x) :=
  injective_etaleFundamentalGroupMap_of_forall_exists_mono g x h

end AlgebraicGeometry
