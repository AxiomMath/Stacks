module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleToposRetraction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartBaseChangeRepresentation

/-!
# The structure sheaf of a thickening with a retraction

Let `i : X ⟶ X'` be a thickening of algebraic spaces with a retraction `q : X' ⟶ X`,
`i ≫ q = 𝟙 X`. Restricting the structure sheaf of `X'` along chart base change along `q` gives
a sheaf of commutative rings `A = q_* 𝒪_{X'}` on the small étale site of `X`
(`AlgebraicGeometry.Space.thickeningRetractionRing`), with ring maps `s : 𝒪_X ⟶ A` (pullback
along the cartesian projection, the structure map of `q`) and `r : A ⟶ 𝒪_X` (restriction to the
base change along `i`, read on the charts of `X` through
`AlgebraicGeometry.Space.smallBaseChangeRetractionIso`), and `s ≫ r = 𝟙`
(`AlgebraicGeometry.Space.thickeningRetractionSection_comp_restriction`). This is the input of
`Deformation.ComplexLift.splitSqZeroExtIso` in the proof of Stacks 0DLL, where
`X₀ ⟶ X_V ⟶ X₀` is the section and retraction of the base change along
`Spec k ⟶ Spec k[V] ⟶ Spec k`.

No `@[stacks]` attribute is claimed here: the declarations below supply inputs to Tag 0DLL, not
any part of its statement.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' : AlgebraicSpaces B S hS} {i : X ⟶ X'} (hi : IsThickeningHom B S hS i)
  {q : X' ⟶ X} (h : i ≫ q = 𝟙 X) (hq : yoneda.relativelyRepresentable q.hom)

/-- **The structure sheaf of `X'` on the small étale site of `X`**, through chart base change
along the retraction `q`: its sections over an étale chart `U` of `X` are the global functions
on `U ×_X X'`. -/
abbrev thickeningRetractionRing : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u} :=
  letI := isContinuous_smallBaseChange B S hS q hq
  ((smallBaseChange B S hS q hq).sheafPushforwardContinuous CommRingCat.{u}
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS X'.1)).obj
    (structureSheaf B S hS X'.1 X'.2)

/-- The ring map `𝒪_X ⟶ q_* 𝒪_{X'}`: pullback of functions along the cartesian projection
`U ×_X X' ⟶ U`. -/
abbrev thickeningRetractionSection :
    structureSheaf B S hS X.1 X.2 ⟶ thickeningRetractionRing B S hS hq :=
  smallBaseChangeSharpCommRingCat B S hS q hq

/-- The ring map `q_* 𝒪_{X'} ⟶ 𝒪_X`: restriction of functions on `U ×_X X'` to its base change
`(U ×_X X') ×_{X'} X ≅ U` along `i`. -/
abbrev thickeningRetractionRestriction :
    thickeningRetractionRing B S hS hq ⟶ structureSheaf B S hS X.1 X.2 :=
  letI := isContinuous_smallBaseChange B S hS q hq
  ((smallBaseChange B S hS q hq).sheafPushforwardContinuous CommRingCat.{u}
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS X'.1)).map
      (smallBaseChangeSharpCommRingCat B S hS i hi.isClosedImmersion.rep) ≫
    (sheafPushforwardRetractionIso B S hS hi h hq CommRingCat.{u}).hom.app
      (structureSheaf B S hS X.1 X.2)

/-- Three morphisms of objects of the site composing to the identity give three maps of global
functions composing to the identity. -/
theorem Γ_map_op_comp_three_eq_id {P Q R : BigFppfOver B S hS} (f : P ⟶ Q) (g : Q ⟶ R)
    (e : R ⟶ P) (hfg : f ≫ g ≫ e = 𝟙 P) :
    Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map e).op ≫
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op ≫
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map f).op = 𝟙 _ := by
  rw [← Scheme.Γ.map_comp, ← Scheme.Γ.map_comp, ← op_comp, ← op_comp,
    ← (BigFppfOver.toScheme B S hS).map_comp, ← (BigFppfOver.toScheme B S hS).map_comp,
    Category.assoc, hfg, CategoryTheory.Functor.map_id, op_id, Scheme.Γ.map_id]

/-- **`s ≫ r = 𝟙`**: pulling a function on `U` back to `U ×_X X'` and restricting it to the
section `U ⟶ U ×_X X'` gives it back. -/
theorem thickeningRetractionSection_comp_restriction :
    thickeningRetractionSection B S hS hq ≫ thickeningRetractionRestriction B S hS hi h hq =
      𝟙 _ := by
  ext U a
  have hτ : ((smallBaseChangeRetractionIso B S hS i q h hi.isClosedImmersion.rep hq).inv.app
        U.unop).hom.left ≫ hi.isClosedImmersion.rep.snd (hq.fst U.unop.1.hom) ≫
        hq.snd U.unop.1.hom = 𝟙 _ :=
    congrArg (fun g => g.hom.left)
      (smallBaseChangeRetractionInv_hom B S hS i q h hi.isClosedImmersion.rep hq U.unop)
  have key : (thickeningRetractionSection B S hS hq ≫
      thickeningRetractionRestriction B S hS hi h hq).hom.app U = 𝟙 _ :=
    Γ_map_op_comp_three_eq_id B S hS _ _ _ hτ
  exact congrArg (fun φ => φ a) (congrArg CommRingCat.Hom.hom key)

/-- **A chart base changed along a base change of schemes is a fibre product of schemes.** Let
`q : X' ⟶ X` be the base change of a morphism `τ : T ⟶ T₀` of schemes of the site along
`p : X ⟶ T₀`, with projection `p' : X' ⟶ T`. For an étale chart `W` of `X`, the scheme of the
base-changed chart `W ×_X X'` is the fibre product `W ×_{T₀} T` of schemes, through the cartesian
projection to `W` and the map `w'` to `T`. In the proof of Stacks 0DLL, `T₀ = Spec k`,
`T = Spec k[V]` and `X' = X_V`, so `W ×_X X_V = W ×_{Spec k} Spec k[V]`. -/
theorem isPullback_toScheme_smallBaseChange_of_isPullback {T T₀ : BigFppfOver B S hS}
    {τ : T ⟶ T₀} {p : X.1 ⟶ yoneda.obj T₀} {p' : X'.1 ⟶ yoneda.obj T}
    (hpb : IsPullback q.hom p' p (yoneda.map τ)) (W : SmallEtale B S hS X.1)
    {w' : hq.pullback W.1.hom ⟶ T} {w₀ : W.1.left ⟶ T₀}
    (hw' : yoneda.map w' = hq.fst W.1.hom ≫ p') (hw₀ : yoneda.map w₀ = W.1.hom ≫ p) :
    IsPullback ((BigFppfOver.toScheme B S hS).map w')
      ((BigFppfOver.toScheme B S hS).map (hq.snd W.1.hom))
      ((BigFppfOver.toScheme B S hS).map τ) ((BigFppfOver.toScheme B S hS).map w₀) := by
  refine AlgebraicGeometry.Stack.ChartBaseChange.isPullback_toScheme_of_isPullback_yoneda ?_
  rw [hw', hw₀]
  exact IsPullback.paste_horiz (hq.isPullback W.1.hom) hpb.flip

end AlgebraicGeometry.Space

end
