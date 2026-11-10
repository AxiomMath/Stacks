module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBaseChangeBundle
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernCompositionReduction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedComponentReduction

/-!
# Stacks 0FEC for virtual normal sheaves of arbitrary rank

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `Z ⟶ Y ⟶ X` be closed
immersions of schemes locally of finite type over `S`, and let `𝒩`, `𝒩'`, `𝒩''` be virtual normal
sheaves for `Z ⊆ X`, `Z ⊆ Y` and `Y ⊆ X` forming a conormal-compatible triple
(`Stacks.Chow.ConormalCompatibleVirtualNormalBundles`). **Stacks 0FEC** asserts

  `c(Z ⟶ X, 𝒩) = c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒩'')`   in `A^*(Z ⟶ X)^∧`,

for the classes of Stacks 0FBK in the completed bivariant groups of Stacks 0FE0 and the
composition on completions. The ranks of the three sheaves are only locally constant.

This file deduces the statement at arbitrary rank from the statement at constant rank,
`Stacks.Chow.virtualNormalGysinClass_eq_compositeVirtualNormalGysinClass_of_cases`, which is
proved there from the two cases `Y = X` and `Y` an effective Cartier divisor of the source's
proof (`Stacks.Chow.CompositionIsoCase`, `Stacks.Chow.CompositionCartierCase`); those two cases
are hypotheses here as they are there.

The reduction is connected component by connected component of `Z`. For a connected component
`Z_a`, lying in the connected component `Y_b` of `Y`, let `W_a ⊆ X` be the intersection of the
open of `X` meeting `Z` in `Z_a` with the open of `X` meeting `Y` inside `Y_b`
(`Stacks.Chow.compositionNeighbourhood`). Over `W_a` the three sheaves have constant ranks
`p + q`, `p` and `q`. Both sides are compared degree by degree, and a homogeneous class on
`Z ⟶ X` is determined by its restrictions (Stacks 0F9Z) to the opens `W_a`
(`Stacks.Chow.BivariantClass.eq_of_bivariantRestriction_eq`, from Stacks 0FDZ). The restriction of
a completed class `c(Z ⟶ X, 𝒩)` to an open lying over the neighbourhood of one component is the
homogeneous class of the base change (Stacks 0FBK,
`completedBivariantRestriction_completedVirtualNormalGysinClass_of_le_componentNeighbourhood`),
restriction commutes with composition on completions, and the composition on completions of
homogeneous classes is their composite
(`Stacks.Chow.completedBivariantCompositeOfInvertible_toCompleted`). This reduces the formula over
`W_a` to the formula at constant rank for the base change of the triple to `W_a`.

## Main definitions

* `Stacks.Chow.VirtualNormalBundle.baseChangeCompDualIso` — the duals of the base changes of a
  virtual normal sheaf along two stacked squares and along the pasted square agree, compatibly
  with the surjections onto the conormal sheaf.
* `Stacks.Chow.componentSquareProjection` — a cartesian square over the neighbourhood of a
  connected component `Z_a` factors through `Z_a`.
* `Stacks.Chow.compositionNeighbourhood` — the open `W_a` above.

## Main results

* `Stacks.Chow.BivariantClass.eq_of_bivariantRestriction_eq` — a class is determined by its
  restrictions to opens around the connected components of its source.
* `Stacks.Chow.bivariantTransport_bivariantRestriction_completedVirtualNormalGysinClass`,
  `Stacks.Chow.bivariantRestriction_completedVirtualNormalGysinClass_eq_zero`,
  `completedBivariantRestriction_completedVirtualNormalGysinClass_of_le_componentNeighbourhood` —
  Stacks 0FBK, the base-change clause, for the completed class along a morphism into the
  neighbourhood of a component.
* `Stacks.Chow.completedBivariantCompositeOfInvertible_toCompleted` — composition on completions
  extends composition of homogeneous classes.
* `completedVirtualNormalGysinClass_eq_completedBivariantCompositeOfInvertible_of_cases` —
  **Stacks 0FEC at arbitrary rank**, from the two cases of the proof.

## Implementation notes

The two cases of the source's proof enter as the hypotheses `CompositionIsoCase C` and
`CompositionCartierCase C`, exactly as in the statement at constant rank from which the result is
derived; no other hypothesis is added. The source states the composite in `A^*(Z ⟶ X)^∧`; here it
is `Stacks.Chow.completedBivariantCompositeOfInvertible`, the composition on completions at the
Gysin system of the first Chern class rule.

## References

* [Stacks Project, Tag 0FEC](https://stacks.math.columbia.edu/tag/0FEC)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

/-! ### The base change along two stacked squares -/

section Stacked

variable {Z₁ Z₂ Z₃ X₁ X₂ X₃ : Scheme.{u}} {i₁ : Z₁ ⟶ X₁} {i₂ : Z₂ ⟶ X₂} {i₃ : Z₃ ⟶ X₃}
  [IsImmersion i₁] [IsImmersion i₂] [IsImmersion i₃] {f₁ : Z₁ ⟶ Z₂} {g₁ : X₁ ⟶ X₂}
  {f₂ : Z₂ ⟶ Z₃} {g₂ : X₂ ⟶ X₃}

/-- **The duals of the two base changes along stacked squares.** For a virtual normal sheaf `N`
of `i₃` and stacked cartesian squares, the dual of the base change along the upper square of the
base change along the lower square is the dual of the base change along the pasted square: both
are `f₁^* f₂^* (N^∨)`, through the dual base-change isomorphisms and `(f₁ ≫ f₂)^* ≅ f₁^* f₂^*`. -/
def VirtualNormalBundle.baseChangeCompDualIso (N : VirtualNormalBundle i₃)
    (sq₂ : IsPullback i₂ f₂ g₂ i₃) (sq₁ : IsPullback i₁ f₁ g₁ i₂) :
    dualSheaf ((N.baseChange i₃ i₂ f₂ g₂ sq₂).baseChange i₂ i₁ f₁ g₁ sq₁).bundle ≅
      dualSheaf (N.baseChange i₃ i₁ (f₁ ≫ f₂) (g₁ ≫ g₂) (sq₁.paste_vert sq₂)).bundle :=
  ((@asIso _ _ _ _ (pullbackDualMap f₁ (N.baseChange i₃ i₂ f₂ g₂ sq₂).bundle)
      (pullbackDualMap_isIso f₁ _ (N.baseChange i₃ i₂ f₂ g₂ sq₂).isFiniteLocallyFree)).symm ≪≫
    (modulePullback f₁.toLRSHom.toShHom).mapIso (@asIso _ _ _ _ (pullbackDualMap f₂ N.bundle)
      (pullbackDualMap_isIso f₂ N.bundle N.isFiniteLocallyFree)).symm) ≪≫
  ((@asIso _ _ _ _ (pullbackDualMap (f₁ ≫ f₂) N.bundle)
      (pullbackDualMap_isIso (f₁ ≫ f₂) N.bundle N.isFiniteLocallyFree)).symm ≪≫
    (modulePullbackComp f₁.toLRSHom.toShHom f₂.toLRSHom.toShHom).app _).symm

/-- **The identification of the duals is compatible with the surjections onto the conormal
sheaf**: both surjections are the pullback along `f₁` of the base-changed surjection followed by
the conormal map of the upper square (Stacks 04G2,
`Stacks.Chow.pullback_map_comp_immersionConormalSheafMap_comp`). -/
theorem VirtualNormalBundle.baseChangeCompDualIso_hom_comp_surjection (N : VirtualNormalBundle i₃)
    (sq₂ : IsPullback i₂ f₂ g₂ i₃) (sq₁ : IsPullback i₁ f₁ g₁ i₂) :
    (N.baseChangeCompDualIso sq₂ sq₁).hom ≫
        (N.baseChange i₃ i₁ (f₁ ≫ f₂) (g₁ ≫ g₂) (sq₁.paste_vert sq₂)).surjection =
      ((N.baseChange i₃ i₂ f₂ g₂ sq₂).baseChange i₂ i₁ f₁ g₁ sq₁).surjection := by
  let W : @Quiver.Hom Z₁.Modules _ ((modulePullback f₁.toLRSHom.toShHom).obj
      ((modulePullback f₂.toLRSHom.toShHom).obj (dualSheaf N.bundle))) (conormalModule i₁) :=
    (modulePullback f₁.toLRSHom.toShHom).map
      ((modulePullback f₂.toLRSHom.toShHom).map N.surjection ≫
        Stacks.Immersion.immersionConormalSheafMap i₂ i₃ f₂ g₂
          (Stacks.Immersion.toShHom_square sq₂.w)) ≫
    Stacks.Immersion.immersionConormalSheafMap i₁ i₂ f₁ g₁
      (Stacks.Immersion.toShHom_square sq₁.w)
  let P₂ := @asIso _ _ _ _ (pullbackDualMap f₂ N.bundle)
    (pullbackDualMap_isIso f₂ N.bundle N.isFiniteLocallyFree)
  let P₁ := @asIso _ _ _ _ (pullbackDualMap f₁ (N.baseChange i₃ i₂ f₂ g₂ sq₂).bundle)
    (pullbackDualMap_isIso f₁ _ (N.baseChange i₃ i₂ f₂ g₂ sq₂).isFiniteLocallyFree)
  let P := @asIso _ _ _ _ (pullbackDualMap (f₁ ≫ f₂) N.bundle)
    (pullbackDualMap_isIso (f₁ ≫ f₂) N.bundle N.isFiniteLocallyFree)
  let Q : @Iso Z₁.Modules _
      (dualSheaf ((N.baseChange i₃ i₂ f₂ g₂ sq₂).baseChange i₂ i₁ f₁ g₁ sq₁).bundle)
      ((modulePullback f₁.toLRSHom.toShHom).obj
        ((modulePullback f₂.toLRSHom.toShHom).obj (dualSheaf N.bundle))) :=
    P₁.symm ≪≫ (modulePullback f₁.toLRSHom.toShHom).mapIso P₂.symm
  let Q' : @Iso Z₁.Modules _
      (dualSheaf (N.baseChange i₃ i₁ (f₁ ≫ f₂) (g₁ ≫ g₂) (sq₁.paste_vert sq₂)).bundle)
      ((modulePullback f₁.toLRSHom.toShHom).obj
        ((modulePullback f₂.toLRSHom.toShHom).obj (dualSheaf N.bundle))) :=
    P.symm ≪≫ (modulePullbackComp f₁.toLRSHom.toShHom f₂.toLRSHom.toShHom).app _
  have hA : ((N.baseChange i₃ i₂ f₂ g₂ sq₂).baseChange i₂ i₁ f₁ g₁ sq₁).surjection =
      Q.hom ≫ W :=
    (P₁.inv ≫= (Functor.map_comp (modulePullback f₁.toLRSHom.toShHom) P₂.inv _ =≫
      Stacks.Immersion.immersionConormalSheafMap i₁ i₂ f₁ g₁
        (Stacks.Immersion.toShHom_square sq₁.w))).trans
      ((P₁.inv ≫= Category.assoc _ _ _).trans (Category.assoc _ _ _).symm)
  have hB : (N.baseChange i₃ i₁ (f₁ ≫ f₂) (g₁ ≫ g₂) (sq₁.paste_vert sq₂)).surjection =
      Q'.hom ≫ W :=
    (P.inv ≫= pullback_map_comp_immersionConormalSheafMap_comp sq₁.w sq₂.w N.surjection).trans
      (Category.assoc _ _ _).symm
  change (Q ≪≫ Q'.symm).hom ≫ _ = _
  rw [hA, hB]
  exact (Category.assoc _ _ _).trans (Q.hom ≫= Iso.inv_hom_id_assoc Q' W)

end Stacked

/-! ### Cartesian squares over the neighbourhood of a connected component -/

section ComponentSquare

variable {Z X Z' X' : Scheme.{u}} [LocallyConnectedSpace Z] [LocallyConnectedSpace X]
  {i : Z ⟶ X} [IsClosedImmersion i] {i' : Z' ⟶ X'} [IsClosedImmersion i'] {g : Z' ⟶ Z}
  {f : X' ⟶ X} (sq : IsPullback i' g f i) (a : _root_.ConnectedComponents Z)
  {h : X' ⟶ (componentNeighbourhood i a : Scheme.{u})}
  (hh : h ≫ (componentNeighbourhood i a).ι = f)

omit [IsClosedImmersion i'] in
include sq hh in
/-- The commutativity of the square over the neighbourhood of a component. -/
theorem comp_componentNeighbourhood_ι_eq :
    (i' ≫ h) ≫ (componentNeighbourhood i a).ι = g ≫ i := by
  rw [Category.assoc, hh, sq.w]

/-- For a cartesian square `Z' = Z ×_X X'` whose base `X' ⟶ X` factors through the open `U_a` of
a connected component `Z_a` of `Z`, the projection `Z' ⟶ Z_a`: since `Z ×_X U_a = Z_a`, the
square factors through `Z_a ⟶ U_a`. -/
def componentSquareProjection : Z' ⟶ (Z.connectedComponentOpens a : Scheme.{u}) :=
  (isPullback_componentRestriction i a).lift (i' ≫ h) g (comp_componentNeighbourhood_ι_eq sq a hh)

omit [IsClosedImmersion i'] in
/-- The projection `componentSquareProjection sq a hh : Z' ⟶ Z_a` followed by the inclusion
`Z_a ⟶ Z` is `g`. -/
@[reassoc (attr := simp)]
theorem componentSquareProjection_ι :
    componentSquareProjection sq a hh ≫ (Z.connectedComponentOpens a).ι = g :=
  IsPullback.lift_snd _ _ _ _

omit [IsClosedImmersion i'] in
/-- The projection `componentSquareProjection sq a hh : Z' ⟶ Z_a` followed by `Z_a ⟶ U_a` is
`i' ≫ h`. -/
@[reassoc (attr := simp)]
theorem componentSquareProjection_componentRestriction :
    componentSquareProjection sq a hh ≫ componentRestriction i a = i' ≫ h :=
  IsPullback.lift_fst _ _ _ _

omit [IsClosedImmersion i'] in
/-- **The square over the neighbourhood of a component is cartesian**: `Z' = Z_a ×_{U_a} X'`. -/
theorem isPullback_componentSquareProjection :
    IsPullback i' (componentSquareProjection sq a hh) h (componentRestriction i a) := by
  refine IsPullback.of_bot ?_ (componentSquareProjection_componentRestriction sq a hh).symm
    (isPullback_componentRestriction i a)
  rw [componentSquareProjection_ι, hh]
  exact sq

/-- The base change of `𝒩` along the square is the base change of `𝒩|_{Z_a}` along the square
over `Z_a ⟶ U_a`, pasted with the square of the construction. -/
theorem VirtualNormalBundle.baseChange_eq_paste (𝒩 : VirtualNormalBundle i) :
    𝒩.baseChange i i' g f sq =
      𝒩.baseChange i i' (componentSquareProjection sq a hh ≫ (Z.connectedComponentOpens a).ι)
        (h ≫ (componentNeighbourhood i a).ι)
        ((isPullback_componentSquareProjection sq a hh).paste_vert
          (isPullback_componentRestriction i a)) :=
  𝒩.baseChange_congr (componentSquareProjection_ι sq a hh).symm hh.symm _ _

include hh in
/-- **The base change of `𝒩` along a square over the neighbourhood of a component has the rank of
`𝒩` on that component**: it is the pullback of `𝒩|_{Z_a}` along `Z' ⟶ Z_a`. -/
theorem isFiniteLocallyFreeOfRank_baseChange_of_componentNeighbourhood
    (𝒩 : VirtualNormalBundle i) (r : ℕ) (hr : componentRank 𝒩.bundle a = r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.baseChange i i' g f sq).bundle r := by
  subst hr
  have h₁ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((modulePullback (componentSquareProjection sq a hh).toLRSHom.toShHom).obj
        ((modulePullback (Z.connectedComponentOpens a).ι.toLRSHom.toShHom).obj 𝒩.bundle))
      (componentRank 𝒩.bundle a) :=
    isFiniteLocallyFreeOfRank_modulePullback (componentSquareProjection sq a hh)
      (𝒩.toComponent i a).bundle (componentRank 𝒩.bundle a) inferInstance
  have hg : (componentSquareProjection sq a hh).toLRSHom.toShHom ≫
      (Z.connectedComponentOpens a).ι.toLRSHom.toShHom = g.toLRSHom.toShHom := by
    conv_rhs => rw [← componentSquareProjection_ι sq a hh]
    rfl
  have e : (modulePullback (componentSquareProjection sq a hh).toLRSHom.toShHom).obj
        ((modulePullback (Z.connectedComponentOpens a).ι.toLRSHom.toShHom).obj 𝒩.bundle) ≅
      (modulePullback g.toLRSHom.toShHom).obj 𝒩.bundle :=
    ((modulePullbackComp (componentSquareProjection sq a hh).toLRSHom.toShHom
      (Z.connectedComponentOpens a).ι.toLRSHom.toShHom).app 𝒩.bundle).symm ≪≫
      (modulePullbackCongr hg).app 𝒩.bundle
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e h₁

end ComponentSquare

/-! ### A class is determined by its restrictions to neighbourhoods of the components -/

section Neighbourhoods

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Z ⟶ X) [LocallyOfFiniteType f]
  (hf : f ≫ sX = sZ) [IsLocallyNoetherian Z]

/-- **A bivariant class is determined by its restrictions to neighbourhoods of the connected
components of its source.** Let `W_a ⊆ X` be an open containing the image of the connected
component `Z_a`, for every `a`. Two classes in `A^n(Z ⟶ X)` with the same restrictions
(Stacks 0F9Z) along every `W_a ⟶ X` are equal: on a test scheme `t : T ⟶ X` the class
`c ∩ α ∈ CH_*(Z ×_X T)` is determined by its restrictions to the open and closed pieces lying
over the `Z_a` (Stacks 0FDZ), and the piece over `Z_a` lies in `Z ×_X t⁻¹(W_a)`, where the cap
operation is that of the restriction of `c` along `W_a ⟶ X` (Stacks 0B76 (2)). -/
theorem BivariantClass.eq_of_bivariantRestriction_eq {n : ℤ}
    (W : _root_.ConnectedComponents Z → X.Opens)
    (hW : ∀ a, Z.connectedComponentOpens a ≤ f ⁻¹ᵁ W a)
    {c d : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf n}
    (h : ∀ a, bivariantRestriction C (gysinSystemOfInvertible C) sZ sX f hf (W a).ι n
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c =
      bivariantRestriction C (gysinSystemOfInvertible C) sZ sX f hf (W a).ι n
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) d) :
    c = d := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun {T} t _ k β ↦ ?_
  have hdec := IsClopenDecomposition.preimage
    (Scheme.isClopenDecomposition_connectedComponentOpens Z) (pullback.fst f t)
  apply (chowGroupClopenEquiv C (pullback.fst f t ≫ sZ) hdec (k - n)
    (rationalEquivalenceDecomposes_of_isClopenDecomposition C _ hdec (k - n))).injective
  funext a
  rw [chowGroupClopenEquiv_apply, chowGroupClopenEquiv_apply,
    chowGroupClopenRestrict_eq_chowGroupRestrict, chowGroupClopenRestrict_eq_chowGroupRestrict]
  set O := pullback.fst f t ⁻¹ᵁ Z.connectedComponentOpens a
  set V := t ⁻¹ᵁ W a
  -- the caps of `c` and `d` agree on test schemes over `W_a`
  have hcap : ∀ {S : Scheme.{u}} (s : S ⟶ (W a : Scheme.{u})) [LocallyOfFiniteType s] (m : S ⟶ X)
      [LocallyOfFiniteType m] (_ : s ≫ (W a).ι = m) (γ : chowGroup C (m ≫ sX) k),
      c.cap m k γ = d.cap m k γ := by
    intro S s _ m _ hm γ
    subst hm
    have key := congrArg (fun e ↦ BivariantClass.cap e s k
      (chowGroupCongr C (Category.assoc s (W a).ι sX) k γ)) (h a)
    simp only [bivariantRestriction_cap, bivariantRestrictionCap_apply,
      chowGroupCongr_chowGroupCongr] at key
    exact chowPushforwardOfIso_injective C _ _ _ _ _ key
  -- restricting the test scheme to `t⁻¹(W_a)`
  have sqv := isPullback_baseChangeMapOfEq f t V.ι (V.ι ≫ t) rfl
  have : IsOpenImmersion (baseChangeMapOfEq f t V.ι (V.ι ≫ t) rfl) :=
    MorphismProperty.of_isPullback sqv (P := @IsOpenImmersion) inferInstance
  have hvY : V.ι ≫ (t ≫ sX) = (V.ι ≫ t) ≫ sX := (Category.assoc _ _ _).symm
  have hres : ∀ e : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf n,
      chowGroupRestrict C (pullback.fst f t ≫ sZ) (pullback.fst f (V.ι ≫ t) ≫ sZ)
          (baseChangeMapOfEq f t V.ι (V.ι ≫ t) rfl)
          (baseChangeMapOfEq_comp_structure sZ f t V.ι (V.ι ≫ t) rfl) (k - n) (e.cap t k β) =
        e.cap (V.ι ≫ t) k (chowGroupRestrict C (t ≫ sX) ((V.ι ≫ t) ≫ sX) V.ι hvY k β) :=
    fun e ↦ BivariantClass.cap_chowGroupRestrict C _ sZ sX f hf n e t V.ι (V.ι ≫ t) rfl _ sqv
      (baseChangeMapOfEq_fst f t V.ι (V.ι ≫ t) rfl) k hvY
      (baseChangeMapOfEq_comp_structure sZ f t V.ι (V.ι ≫ t) rfl) β
  have hV : chowGroupRestrict C (pullback.fst f t ≫ sZ) (pullback.fst f (V.ι ≫ t) ≫ sZ)
      (baseChangeMapOfEq f t V.ι (V.ι ≫ t) rfl)
      (baseChangeMapOfEq_comp_structure sZ f t V.ι (V.ι ≫ t) rfl) (k - n) (c.cap t k β) =
      chowGroupRestrict C (pullback.fst f t ≫ sZ) (pullback.fst f (V.ι ≫ t) ≫ sZ)
      (baseChangeMapOfEq f t V.ι (V.ι ≫ t) rfl)
      (baseChangeMapOfEq_comp_structure sZ f t V.ι (V.ι ≫ t) rfl) (k - n) (d.cap t k β) := by
    rw [hres, hres]
    exact hcap (t ∣_ W a) (V.ι ≫ t) (morphismRestrict_ι t (W a)) _
  -- the piece over `Z_a` lies in `Z ×_X t⁻¹(W_a)`
  have hle : O ≤ pullback.snd f t ⁻¹ᵁ V := by
    intro x hx
    change t (pullback.snd f t x) ∈ W a
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact hW a hx
  have hcond : (O.ι ≫ pullback.fst f t) ≫ f = (pullback.snd f t).resLE V O hle ≫ (V.ι ≫ t) := by
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Category.assoc,
      pullback.condition]
  have hfac : pullback.lift _ _ hcond ≫ baseChangeMapOfEq f t V.ι (V.ι ≫ t) rfl = O.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, baseChangeMapOfEq_fst, pullback.lift_fst]
    · rw [Category.assoc, baseChangeMapOfEq_snd, pullback.lift_snd_assoc,
        Scheme.Hom.resLE_comp_ι]
  have hfacs : pullback.lift _ _ hcond ≫ (pullback.fst f (V.ι ≫ t) ≫ sZ) =
      O.ι ≫ (pullback.fst f t ≫ sZ) := by
    rw [← baseChangeMapOfEq_comp_structure sZ f t V.ι (V.ι ≫ t) rfl, ← Category.assoc, hfac]
  have : IsOpenImmersion (pullback.lift _ _ hcond ≫ baseChangeMapOfEq f t V.ι (V.ι ≫ t) rfl) := by
    rw [hfac]; infer_instance
  have : IsOpenImmersion (pullback.lift _ _ hcond) :=
    IsOpenImmersion.of_comp _ (baseChangeMapOfEq f t V.ι (V.ι ≫ t) rfl)
  have hs : (pullback.lift _ _ hcond ≫ baseChangeMapOfEq f t V.ι (V.ι ≫ t) rfl) ≫
      (pullback.fst f t ≫ sZ) = O.ι ≫ (pullback.fst f t ≫ sZ) := by rw [hfac]
  rw [chowGroupRestrict_congr C _ _ O.ι _ _ _ hfac.symm hs,
    ← chowGroupRestrict_comp C (pullback.fst f t ≫ sZ) (pullback.fst f (V.ι ≫ t) ≫ sZ) _
      (baseChangeMapOfEq_comp_structure sZ f t V.ι (V.ι ≫ t) rfl) (k - n) _
      (pullback.lift _ _ hcond) hfacs, hV, chowGroupRestrict_comp]

end Neighbourhoods

/-! ### The completed class on a test scheme over the neighbourhood of a component -/

section CompletedBaseChange

/-- The class `c(Z ⟶ X, 𝒩)` at constant rank does not depend on how the structure morphism of the
target is written, on cap operations. -/
theorem virtualNormalGysinClass_cap_congr_structure (C : ChowSituation.{u}) {Z X : Scheme.{u}}
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] {s s' : X ⟶ C.S} [LocallyOfFiniteType s]
    [LocallyOfFiniteType s'] (e : s = s') (i : Z ⟶ X) [IsClosedImmersion i] (h₁ : i ≫ s = sZ)
    (h₂ : i ≫ s' = sZ) (N : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N.bundle r] {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ s) k) :
    (virtualNormalBundleClass C sZ s i h₁ N r).cap t k α =
      (virtualNormalBundleClass C sZ s' i h₂ N r).cap t k
        (chowGroupCongr C (by rw [e]) k α) := by
  subst e
  rfl

/-- Two completed classes whose images in every degree agree are equal (Stacks 0FE0). -/
private theorem eq_of_completedBivariantSequenceOfInvertible_apply_eq (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {c d : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf}
    (h : ∀ m, completedBivariantSequenceOfInvertible C sX sY f hf c m =
      completedBivariantSequenceOfInvertible C sX sY f hf d m) : c = d :=
  completedBivariantSequence_injective C (gysinSystemOfInvertible C) _ _ _ _
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) (funext h)

variable (C : ChowSituation.{u}) {Z X Z' X' : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ)
  [IsLocallyNoetherian Z] [IsLocallyNoetherian X] (𝒩 : VirtualNormalBundle i)
  (a : _root_.ConnectedComponents Z) {f : X' ⟶ X} [LocallyOfFiniteType f]
  {h : X' ⟶ (componentNeighbourhood i a : Scheme.{u})} [LocallyOfFiniteType h]
  (hh : h ≫ (componentNeighbourhood i a).ι = f)

omit [LocallyOfFiniteType h] in
include hh in
/-- **The degree parts of `c(Z ⟶ X, 𝒩)` other than the rank vanish over the neighbourhood of a
component.** If `f : X' ⟶ X` factors through the open `U_a` of a connected component `Z_a`, the
restriction (Stacks 0F9Z) along `f` of the degree-`m` part of the completed class vanishes for
`m` other than the rank `r_a` of `𝒩` on `Z_a`: the base change `Z ×_X X'` lies over `Z_a`, on
which the completed class is concentrated in degree `r_a`. -/
theorem bivariantRestriction_completedVirtualNormalGysinClass_eq_zero (m : ℤ)
    (hm : m ≠ (componentRank 𝒩.bundle a : ℤ)) :
    bivariantRestriction C (gysinSystemOfInvertible C) sZ sX i hi f m
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (completedBivariantSequenceOfInvertible C sZ sX i hi
          (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) m) = 0 := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun {T} t _ k α ↦ ?_
  rw [BivariantClass.zero_cap, bivariantRestriction_cap, bivariantRestrictionCap_apply]
  have ht : (t ≫ h) ≫ (componentNeighbourhood i a).ι = t ≫ f := by rw [Category.assoc, hh]
  have hz := chowGroupRestrict_cap_eq_zero_of_connectedComponentRestriction_eq_zero C
    (gysinSystemOfInvertible C) sZ sX i hi m
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) _ a
    (bivariantConnectedComponentRestriction_completedVirtualNormalGysinClass_eq_zero C sZ sX i hi
      𝒩 a m hm) (t ≫ f) k (chowGroupCongr C (Category.assoc t f sX).symm k α)
    (pullback.fst i (t ≫ f) ≫ sZ) (𝟙 _) (Category.id_comp _)
    ((componentTestIso i a (t ≫ h) (t ≫ f) ht).inv ≫
      pullback.fst (componentRestriction i a) (t ≫ h))
    (by rw [Category.assoc, ← componentTestIso_hom_fst i a (t ≫ h) (t ≫ f) ht,
      Iso.inv_hom_id_assoc, Category.id_comp])
  rw [chowGroupRestrict_id] at hz
  rw [hz, map_zero]

include hh in
/-- **The base-change clause of Stacks 0FBK for the completed class, over the neighbourhood of a
component.** Let `Z' = Z ×_X X'` be a cartesian square whose base `f : X' ⟶ X` factors through the
open `U_a` of a connected component `Z_a` of `Z`, on which `𝒩` has rank `r`. The restriction
(Stacks 0F9Z) along `f` of the degree-`r` part of `c(Z ⟶ X, 𝒩)`, carried to `Z'`, is
`c(Z' ⟶ X', g^*𝒩)`: over `U_a` the completed class is `c(Z_a ⟶ U_a, 𝒩|_{Z_a})`
(`Stacks.Chow.chowGroupRestrict_completedVirtualNormalGysinClass_cap_of_eq`), whose base change
along `X' ⟶ U_a` is the class of `g^*𝒩` (Stacks 0FBK at constant rank,
`Stacks.Chow.virtualNormalGysinClass_cap_baseChange`, with
`Stacks.Chow.VirtualNormalBundle.baseChangeCompDualIso`). -/
theorem bivariantTransport_bivariantRestriction_completedVirtualNormalGysinClass
    {i' : Z' ⟶ X'} [IsClosedImmersion i'] {g : Z' ⟶ Z} (sq : IsPullback i' g f i) (r : ℕ)
    (hr : componentRank 𝒩.bundle a = r) (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ']
    (hi' : i' ≫ (f ≫ sX) = sZ') :
    haveI := isFiniteLocallyFreeOfRank_baseChange_of_componentNeighbourhood sq a hh 𝒩 r hr
    bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst i f ≫ sZ) sZ' (f ≫ sX)
        (pullback.snd i f) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) i' hi'
        sq.flip.isoPullback.symm (sq.flip.isoPullback_inv_snd) (r : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestriction C (gysinSystemOfInvertible C) sZ sX i hi f (r : ℤ)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (completedBivariantSequenceOfInvertible C sZ sX i hi
            (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) (r : ℤ))) =
      virtualNormalBundleClass C sZ' (f ≫ sX) i' hi' (𝒩.baseChange i i' g f sq) r := by
  have := isFiniteLocallyFreeOfRank_baseChange_of_componentNeighbourhood sq a hh 𝒩 r hr
  subst hr
  have sqa := isPullback_componentSquareProjection sq a hh
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((𝒩.toComponent i a).baseChange (componentRestriction i a) i'
        (componentSquareProjection sq a hh) h sqa).bundle (componentRank 𝒩.bundle a) :=
    isFiniteLocallyFreeOfRank_modulePullback _ _ _ inferInstance
  -- the base change of `𝒩` is the base change of `𝒩|_{Z_a}`
  have hstack : virtualNormalBundleClass C sZ' (f ≫ sX) i' hi' (𝒩.baseChange i i' g f sq)
      (componentRank 𝒩.bundle a) =
      virtualNormalBundleClass C sZ' (f ≫ sX) i' hi'
        ((𝒩.toComponent i a).baseChange (componentRestriction i a) i'
          (componentSquareProjection sq a hh) h sqa) (componentRank 𝒩.bundle a) := by
    have key : ∀ (N : VirtualNormalBundle i') (_ : N = 𝒩.baseChange i i'
        (componentSquareProjection sq a hh ≫ (Z.connectedComponentOpens a).ι)
        (h ≫ (componentNeighbourhood i a).ι) (sqa.paste_vert (isPullback_componentRestriction i a)))
        [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N.bundle (componentRank 𝒩.bundle a)],
        virtualNormalBundleClass C sZ' (f ≫ sX) i' hi' N (componentRank 𝒩.bundle a) =
          virtualNormalBundleClass C sZ' (f ≫ sX) i' hi'
            ((𝒩.toComponent i a).baseChange (componentRestriction i a) i'
              (componentSquareProjection sq a hh) h sqa) (componentRank 𝒩.bundle a) := by
      intro N hN _
      subst hN
      have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((𝒩.baseChange i (componentRestriction i a) (Z.connectedComponentOpens a).ι
            (componentNeighbourhood i a).ι (isPullback_componentRestriction i a)).baseChange
              (componentRestriction i a) i' (componentSquareProjection sq a hh) h sqa).bundle
          (componentRank 𝒩.bundle a) := this
      exact virtualNormalGysinClass_eq_of_dualIso C sZ' (f ≫ sX) i' hi' _ _
        (𝒩.baseChangeCompDualIso (isPullback_componentRestriction i a) sqa)
        (𝒩.baseChangeCompDualIso_hom_comp_surjection (isPullback_componentRestriction i a) sqa)
        (componentRank 𝒩.bundle a)
    exact key _ (VirtualNormalBundle.baseChange_eq_paste sq a hh 𝒩)
  rw [hstack]
  refine eq_of_isBivariantTransport C _ _ _ _ _ _ _ _ _ _ _
    (isBivariantTransport_bivariantTransport C _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
  intro T t _ k α
  rw [bivariantTransportCap_apply, bivariantRestriction_cap, bivariantRestrictionCap_apply,
    chowPushforwardOfIso_comp_eq C _ _ _ _ _ _
      (pullbackLeftPullbackSndIso_inv_transportPullbackIso_hom i i' g f sq t)]
  swap
  · rw [← hi', ← hi]
    exact subschemeTestBaseChangeIso_hom_comp_structure i i' g f sq t sX
  have he : f ≫ sX = h ≫ ((componentNeighbourhood i a).ι ≫ sX) := by rw [← hh, Category.assoc]
  have hi'a : i' ≫ (h ≫ ((componentNeighbourhood i a).ι ≫ sX)) = sZ' := by rwa [← he]
  have ht : (t ≫ h) ≫ (componentNeighbourhood i a).ι = t ≫ f := by rw [Category.assoc, hh]
  rw [virtualNormalGysinClass_cap_congr_structure C sZ' he i' hi' hi'a _ _ t k α,
    virtualNormalGysinClass_cap_baseChange C ((Z.connectedComponentOpens a).ι ≫ sZ)
      ((componentNeighbourhood i a).ι ≫ sX) (componentRestriction i a)
      (componentRestriction_comp_structureMorphism C sZ sX i hi a) i'
      (componentSquareProjection sq a hh) h sqa (𝒩.toComponent i a) (componentRank 𝒩.bundle a)
      sZ' hi'a t k]
  -- over `U_a` the completed class is the class of the component
  have hC := chowGroupRestrict_completedVirtualNormalGysinClass_cap_of_eq C sZ sX i hi 𝒩 a
    (componentRank 𝒩.bundle a) rfl (t ≫ h) (t ≫ f) ht k
    (chowGroupCongr C (Category.assoc t h ((componentNeighbourhood i a).ι ≫ sX)).symm k
      (chowGroupCongr C (by rw [he]) k α))
  rw [chowGroupCongr_chowGroupCongr, chowGroupCongr_chowGroupCongr] at hC
  rw [← hC, ← chowPushforwardOfIso_iso_inv_eq_chowGroupRestrict C _ _ _
      (by rw [← componentTestIso_hom_fst_assoc i a (t ≫ h) (t ≫ f) ht, Iso.inv_hom_id_assoc]),
    chowPushforwardOfIso_comp_apply]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _
  rw [Iso.inv_comp_eq]
  apply pullback.hom_ext
  · apply sq.hom_ext
    · simp only [Category.assoc, pullback.condition, subschemeTestBaseChangeIso_hom_snd_assoc,
        componentTestIso_hom_snd_assoc]
    · simp only [Category.assoc]
      rw [subschemeTestBaseChangeIso_hom_fst, componentTestIso_hom_fst]
      have hfst := subschemeTestBaseChangeIso_hom_fst_assoc (componentRestriction i a) i'
        (componentSquareProjection sq a hh) h sqa t (Z.connectedComponentOpens a).ι
      rw [componentSquareProjection_ι] at hfst
      exact hfst
  · simp only [Category.assoc, subschemeTestBaseChangeIso_hom_snd, componentTestIso_hom_snd]

include hh in
/-- **The restriction of the completed class along a morphism into the neighbourhood of a
component** (Stacks 0FBK, the base-change clause, on Stacks 0FE0). If `f : X' ⟶ X` factors
through the open `U_a` of a connected component `Z_a` of `Z`, on which `𝒩` has rank `r`, the
restriction (Stacks 0F9Z) of `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` along `f` is the homogeneous class
`c(Z ×_X X' ⟶ X', g^*𝒩) ∈ A^r`, read as a completed class. -/
theorem completedBivariantRestriction_completedVirtualNormalGysinClass_of_le_componentNeighbourhood
    (r : ℕ) (hr : componentRank 𝒩.bundle a = r) [IsLocallyNoetherian X']
    [IsLocallyNoetherian (pullback i f)] :
    haveI := isFiniteLocallyFreeOfRank_baseChange_of_componentNeighbourhood
      (isPullback_pullbackSnd i f) a hh 𝒩 r hr
    completedBivariantRestrictionViaSequence C sZ sX i hi f
        (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) =
      (virtualNormalBundleClass C (pullback.fst i f ≫ sZ) (f ≫ sX) (pullback.snd i f)
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f)
        (baseChangeVirtualNormalBundle i f 𝒩) r).toCompleted C := by
  have := isFiniteLocallyFreeOfRank_baseChange_of_componentNeighbourhood
    (isPullback_pullbackSnd i f) a hh 𝒩 r hr
  refine eq_of_completedBivariantSequenceOfInvertible_apply_eq C _ _ _ _ fun m ↦ ?_
  rw [completedBivariantSequenceOfInvertible_completedBivariantRestriction,
    completedBivariantSequenceOfInvertible_toCompleted]
  by_cases hm : m = (r : ℤ)
  · subst hm
    rw [Pi.single_eq_same]
    have hB := bivariantTransport_bivariantRestriction_completedVirtualNormalGysinClass C sZ sX i
      hi 𝒩 a hh (isPullback_pullbackSnd i f) r hr (pullback.fst i f ≫ sZ)
      (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f)
    refine Eq.trans ?_ hB
    -- the transport along the identification of the chosen fibre product with itself
    refine (BivariantClass.ext C _ _ _ _ _ _ fun {T} t _ k α ↦ ?_)
    rw [bivariantTransport_cap, bivariantTransportCap_apply,
      chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _) ?_ _ (Category.id_comp _),
      chowPushforwardOfIso_id]
    apply pullback.hom_ext
    · have hid : (isPullback_pullbackSnd i f).flip.isoPullback.symm.hom = 𝟙 _ := by
        apply pullback.hom_ext <;> simp
      simp only [transportPullbackIso_hom_fst, Category.id_comp]
      rw [hid, Category.comp_id]
    · simp
  · rw [Pi.single_eq_of_ne hm]
    exact bivariantRestriction_completedVirtualNormalGysinClass_eq_zero C sZ sX i hi 𝒩 a hh m
      (by rwa [hr])

end CompletedBaseChange

/-! ### Composites of homogeneous classes on completions -/

section HomogeneousComposite

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z) [LocallyOfFiniteType g] (hf : f ≫ sY = sX)
  (hg : g ≫ sZ = sY) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]

/-- **The composition on completions extends the composition of homogeneous classes**
(Stacks 0FE0 and Stacks 0B75): for `x ∈ A^p(X ⟶ Y)` and `y ∈ A^q(Y ⟶ Z)` read as completed
classes, their composite on completions is `x ∘ y ∈ A^{p+q}(X ⟶ Z)`, read in degree `n = p + q`,
as a completed class. On a connected component `X_w` this is the compatibility of restriction to
connected components with composition
(`Stacks.Chow.bivariantConnectedComponentRestriction_bivariantCompositeOfInvertible`). -/
theorem completedBivariantCompositeOfInvertible_toCompleted {p q n : ℤ} (hn : p + q = n)
    (x : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p)
    (y : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg q) :
    completedBivariantCompositeOfInvertible C sX sY sZ f g hf hg (x.toCompleted C)
        (y.toCompleted C) =
      (BivariantClass.copy C (gysinSystemOfInvertible C) sX sZ rfl
        (comp_comp_structureMorphism_eq hf hg) (comp_comp_structureMorphism_eq hf hg) hn
        (bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q x y)).toCompleted C := by
  subst hn
  funext w
  rw [completedBivariantCompositeOfInvertible_of_of C sX sY sZ f g hf hg _ _ w p q
      (by rw [BivariantClass.toCompleted_apply, DirectSum.of_eq_same])
      (by rw [BivariantClass.toCompleted_apply, DirectSum.of_eq_same]),
    BivariantClass.toCompleted_apply, BivariantClass.toCompleted_apply,
    BivariantClass.toCompleted_apply, DirectSum.of_eq_same, DirectSum.of_eq_same]
  exact congrArg (DirectSum.of _ (p + q))
    (bivariantConnectedComponentRestriction_bivariantCompositeOfInvertible C sX sY sZ f g hf hg
      (x := x) (y := y) (w := w)).symm

end HomogeneousComposite

/-! ### Transport along mutually inverse isomorphisms -/

section TransportInverse

variable (C : ChowSituation.{u}) (G : GysinSystem C) {A B W : Scheme.{u}} (sA : A ⟶ C.S)
  [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sW : W ⟶ C.S)
  [LocallyOfFiniteType sW] (v : A ⟶ W) [LocallyOfFiniteType v] (hv : v ≫ sW = sA)
  (u : B ⟶ W) [LocallyOfFiniteType u] (hu : u ≫ sW = sB) (p : ℤ)
  (hgys : G.IsNaturalUnderBaseChangeIso)

/-- **Transporting back along an inverse isomorphism.** For isomorphisms `θ : A ≅ B` and
`θ' : B ≅ A` over `W` with `θ ≫ θ' = 𝟙`, transporting a class along `θ` and then along `θ'` gives
the class back. -/
theorem bivariantTransport_bivariantTransport_of_hom_comp_hom_eq_id (θ : A ≅ B)
    (hθ : θ.hom ≫ u = v) (θ' : B ≅ A) (hθ' : θ'.hom ≫ v = u) (h : θ.hom ≫ θ'.hom = 𝟙 A)
    (c : BivariantClass C G sA sW v hv p) :
    bivariantTransport C G sB sA sW u hu v hv θ' hθ' p hgys
        (bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys c) = c := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun {T} t _ k α ↦ ?_
  rw [bivariantTransport_cap, bivariantTransportCap_apply, bivariantTransport_cap,
    bivariantTransportCap_apply, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _) ?_ _ (Category.id_comp _),
    chowPushforwardOfIso_id]
  apply pullback.hom_ext
  · simp only [Category.assoc, transportPullbackIso_hom_fst, transportPullbackIso_hom_fst_assoc,
      h, Category.comp_id, Category.id_comp]
  · simp

end TransportInverse

/-! ### Stacks 0FEC at arbitrary rank -/

section Main

variable {C : ChowSituation.{u}} (hiso : CompositionIsoCase C) (hcart : CompositionCartierCase C)
  {Z Y X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sY : Y ⟶ C.S)
  [LocallyOfFiniteType sY] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {i : Z ⟶ Y} {j : Y ⟶ X}
  [IsClosedImmersion i] [IsClosedImmersion j] (hi : i ≫ sY = sZ) (hj : j ≫ sX = sY)
  (D : ConormalCompatibleVirtualNormalBundles i j)

/-- The open `W_a = U_a ∩ V_b ⊆ X` around a connected component `Z_a` of `Z`, for the component
neighbourhoods `U_a` of `Z_a` (for `Z ⟶ X`) and `V_b` of the connected component `Y_b` of `Y`
containing `i(Z_a)` (for `Y ⟶ X`): it meets `Z` in `Z_a` and `Y` inside `Y_b`, so the three
virtual normal sheaves have constant rank over it. -/
abbrev compositionNeighbourhood [LocallyConnectedSpace Z] [LocallyConnectedSpace Y]
    [LocallyConnectedSpace X] (a : _root_.ConnectedComponents Z) : X.Opens :=
  componentNeighbourhood (i ≫ j) a ⊓
    componentNeighbourhood j (i.continuous.connectedComponentsMap a)

/-- The open `W_a` contains the image of the connected component `Z_a`. -/
theorem le_preimage_compositionNeighbourhood [LocallyConnectedSpace Z]
    [LocallyConnectedSpace Y] [LocallyConnectedSpace X] (a : _root_.ConnectedComponents Z) :
    Z.connectedComponentOpens a ≤ (i ≫ j) ⁻¹ᵁ compositionNeighbourhood (i := i) (j := j) a := by
  intro x hx
  refine ⟨?_, ?_⟩
  · have := (preimage_componentNeighbourhood (i ≫ j) a).ge hx
    exact this
  · have hy := (preimage_componentNeighbourhood j (i.continuous.connectedComponentsMap a)).ge
      (i.connectedComponentOpens_le_preimage a hx)
    exact hy

/-- The base change `Y ×_X W_a ⟶ Y` lands in the component neighbourhood of `Z_a` in `Y`. -/
theorem range_pullbackFst_subset_componentNeighbourhood [LocallyConnectedSpace Z]
    [LocallyConnectedSpace Y] [LocallyConnectedSpace X] (a : _root_.ConnectedComponents Z) :
    Set.range (pullback.fst j (compositionNeighbourhood (i := i) (j := j) a).ι) ⊆
      Set.range (componentNeighbourhood i a).ι := by
  rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  intro y hjy
  refine ⟨?_, ?_⟩
  · exact (preimage_componentNeighbourhood j (i.continuous.connectedComponentsMap a)).le hjy.2
  · rintro ⟨z, hz, rfl⟩
    exact hz ((preimage_componentNeighbourhood (i ≫ j) a).le hjy.1)

include hiso hcart in
/-- **Stacks 0FEC over the neighbourhood of a connected component.** Over the open `W_a` of a
connected component `Z_a` of `Z` (`Stacks.Chow.compositionNeighbourhood`), the three virtual normal
sheaves have constant ranks `p + q`, `p` and `q`, and the two sides of the composition formula
restrict (Stacks 0F9Z) to the two sides of the formula at constant rank for the base change of `D`
to `W_a` (Stacks 0FBK,
`completedBivariantRestriction_completedVirtualNormalGysinClass_of_le_componentNeighbourhood`, and
the restriction of composites on completions), which agree by
`Stacks.Chow.virtualNormalGysinClass_eq_compositeVirtualNormalGysinClass_of_cases`. -/
theorem bivariantRestriction_compositionNeighbourhood_eq_of_cases
    (a : _root_.ConnectedComponents Z) (n : ℤ) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    bivariantRestriction C (gysinSystemOfInvertible C) sZ sX (i ≫ j)
        (comp_comp_structureMorphism_eq hi hj) (compositionNeighbourhood (i := i) (j := j) a).ι n
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (completedBivariantSequenceOfInvertible C sZ sX (i ≫ j)
          (comp_comp_structureMorphism_eq hi hj)
          (completedVirtualNormalGysinClass C sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj)
            D.bundleZX) n) =
      bivariantRestriction C (gysinSystemOfInvertible C) sZ sX (i ≫ j)
        (comp_comp_structureMorphism_eq hi hj) (compositionNeighbourhood (i := i) (j := j) a).ι n
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (completedBivariantSequenceOfInvertible C sZ sX (i ≫ j)
          (comp_comp_structureMorphism_eq hi hj)
          (completedBivariantCompositeOfInvertible C sZ sY sX i j hi hj
            (completedVirtualNormalGysinClass C sZ sY i hi D.bundleZY)
            (completedVirtualNormalGysinClass C sY sX j hj D.bundleYX)) n) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  set W := compositionNeighbourhood (i := i) (j := j) a
  set g := W.ι
  set b := i.continuous.connectedComponentsMap a
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  have : IsLocallyNoetherian (pullback j g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst j g ≫ sY)
  have : IsLocallyNoetherian (pullback (i ≫ j) g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (i ≫ j) g ≫ sZ)
  have : IsLocallyNoetherian (pullback i (pullback.fst j g)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i (pullback.fst j g) ≫ sZ)
  -- the factorizations through the component neighbourhoods
  have hU : X.homOfLE (inf_le_left : W ≤ componentNeighbourhood (i ≫ j) a) ≫
      (componentNeighbourhood (i ≫ j) a).ι = g := Scheme.homOfLE_ι _ _
  have hV : X.homOfLE (inf_le_right : W ≤ componentNeighbourhood j b) ≫
      (componentNeighbourhood j b).ι = g := Scheme.homOfLE_ι _ _
  have hYf := IsOpenImmersion.lift_fac (componentNeighbourhood i a).ι (pullback.fst j g)
    (range_pullbackFst_subset_componentNeighbourhood (i := i) (j := j) a)
  set hY := IsOpenImmersion.lift (componentNeighbourhood i a).ι (pullback.fst j g)
    (range_pullbackFst_subset_componentNeighbourhood (i := i) (j := j) a)
  -- the ranks over `W_a`
  set p := componentRank D.bundleZY.bundle a
  set q := componentRank D.bundleYX.bundle b
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (testBaseChange D g).bundleZY.bundle p :=
    isFiniteLocallyFreeOfRank_baseChange_of_componentNeighbourhood
      (isPullback_pullbackSnd i (pullback.fst j g)) a hYf D.bundleZY p rfl
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (testBaseChange D g).bundleYX.bundle q :=
    isFiniteLocallyFreeOfRank_baseChange_of_componentNeighbourhood
      (isPullback_pullbackSnd j g) b hV D.bundleYX q rfl
  have sqP := IsPullback.paste_horiz (isPullback_pullbackSnd i (pullback.fst j g))
      (isPullback_pullbackSnd j g)
  have hr : componentRank D.bundleZX.bundle a = p + q := by
    have h₁ := isFiniteLocallyFreeOfRank_baseChange_of_componentNeighbourhood sqP a hU D.bundleZX
      _ rfl
    have h₂ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (testBaseChange D g).bundleZX.bundle (p + q) := inferInstance
    obtain ⟨x₀, hx₀⟩ := _root_.ConnectedComponents.surjective_coe a
    have hxa : x₀ ∈ Z.connectedComponentOpens a := (Scheme.mem_connectedComponentOpens Z).2 hx₀
    have hxW := le_preimage_compositionNeighbourhood (i := i) (j := j) a hxa
    obtain ⟨y, hy₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := j) (g := g) (i x₀)
      ⟨(i ≫ j) x₀, hxW⟩ rfl
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i)
      (g := pullback.fst j g) x₀ y hy₁.symm
    exact Scheme.Modules.isFiniteLocallyFreeOfRank_unique _ h₁ h₂ z
  -- the right-hand side over `W_a`: the composite of the two restricted classes
  conv_rhs => rw [← completedBivariantSequenceOfInvertible_completedBivariantRestriction,
    completedBivariantRestriction_completedBivariantCompositeOfInvertible,
    completedBivariantSequenceOfInvertible_completedBivariantTransport,
    completedBivariantRestriction_completedVirtualNormalGysinClass_of_le_componentNeighbourhood
      C sZ sY i hi D.bundleZY a hYf p rfl,
    completedBivariantRestriction_completedVirtualNormalGysinClass_of_le_componentNeighbourhood
      C sY sX j hj D.bundleYX b hV q rfl,
    completedBivariantCompositeOfInvertible_toCompleted C _ _ _ _ _ _ _
      (by push_cast; rfl : (p : ℤ) + q = ((p + q : ℕ) : ℤ)),
    completedBivariantSequenceOfInvertible_toCompleted]
  by_cases hn : n = ((p + q : ℕ) : ℤ)
  · subst hn
    rw [Pi.single_eq_same]
    -- the formula at constant rank for the base change of `D` to `W_a`
    have hconst := virtualNormalGysinClass_eq_compositeVirtualNormalGysinClass_of_cases
      (pullback.fst i (pullback.fst j g) ≫ sZ) (pullback.fst j g ≫ sY) (g ≫ sX)
      (pullbackSnd_comp_structureMorphism_eq C sZ sY i hi (pullback.fst j g))
      (pullbackSnd_comp_structureMorphism_eq C sY sX j hj g) (testBaseChange D g) p q hiso hcart
    -- the left-hand side over `W_a` is the class of the base change of `𝒩`
    have hB := bivariantTransport_bivariantRestriction_completedVirtualNormalGysinClass C sZ sX
      (i ≫ j) (comp_comp_structureMorphism_eq hi hj) D.bundleZX a hU sqP (p + q) hr
      (pullback.fst i (pullback.fst j g) ≫ sZ)
      (comp_comp_structureMorphism_eq
        (pullbackSnd_comp_structureMorphism_eq C sZ sY i hi (pullback.fst j g))
        (pullbackSnd_comp_structureMorphism_eq C sY sX j hj g))
    have hφθ : sqP.flip.isoPullback.symm.hom ≫ (pullbackRightPullbackFstIso j g i).hom = 𝟙 _ := by
      apply pullback.hom_ext <;> simp
    refine (bivariantTransport_bivariantTransport_of_hom_comp_hom_eq_id C
      (gysinSystemOfInvertible C) (pullback.fst (i ≫ j) g ≫ sZ)
      (pullback.fst i (pullback.fst j g) ≫ sZ) (g ≫ sX) (pullback.snd (i ≫ j) g)
      (pullbackSnd_comp_structureMorphism_eq C sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj)
        g)
      (pullback.snd i (pullback.fst j g) ≫ pullback.snd j g)
      (comp_comp_structureMorphism_eq
        (pullbackSnd_comp_structureMorphism_eq C sZ sY i hi (pullback.fst j g))
        (pullbackSnd_comp_structureMorphism_eq C sY sX j hj g)) ((p + q : ℕ) : ℤ)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      sqP.flip.isoPullback.symm sqP.flip.isoPullback_inv_snd (pullbackRightPullbackFstIso j g i)
      (pullbackRightPullbackFstIso_hom_snd j g i) hφθ _).symm.trans ?_
    rw [hB]
    exact congrArg (fun c ↦ bivariantTransport C (gysinSystemOfInvertible C) _ _ _ _ _ _ _ _
      (pullbackRightPullbackFstIso_hom_snd j g i) _
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c) hconst
  · rw [Pi.single_eq_of_ne hn, bivariantTransport_zero]
    exact bivariantRestriction_completedVirtualNormalGysinClass_eq_zero C sZ sX (i ≫ j)
      (comp_comp_structureMorphism_eq hi hj) D.bundleZX a hU n (by rwa [hr])

/-- **Stacks 0FEC, for virtual normal sheaves of arbitrary rank, from its two cases.** Let
`Z ⟶ Y ⟶ X` be closed immersions of schemes locally of finite type over the base, and let `D` be
a conormal-compatible triple of virtual normal sheaves `𝒩`, `𝒩'`, `𝒩''` for `Z ⊆ X`, `Z ⊆ Y` and
`Y ⊆ X`, of arbitrary (locally constant) ranks. Granted the two cases of the source's proof
(`Stacks.Chow.CompositionIsoCase`, `Stacks.Chow.CompositionCartierCase`),

  `c(Z ⟶ X, 𝒩) = c(Z ⟶ Y, 𝒩') ∘ c(Y ⟶ X, 𝒩'')`   in `A^*(Z ⟶ X)^∧`.

Both sides are completed classes, so they are compared degree by degree (Stacks 0FE0), and a
class of each degree is determined by its restrictions to the opens `W_a` around the connected
components `Z_a` of `Z` (`Stacks.Chow.BivariantClass.eq_of_bivariantRestriction_eq`), where
the formula is the formula at constant rank
(`Stacks.Chow.bivariantRestriction_compositionNeighbourhood_eq_of_cases`). -/
theorem completedVirtualNormalGysinClass_eq_completedBivariantCompositeOfInvertible_of_cases
    (hiso : CompositionIsoCase C) (hcart : CompositionCartierCase C) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    completedVirtualNormalGysinClass C sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj)
        D.bundleZX =
      completedBivariantCompositeOfInvertible C sZ sY sX i j hi hj
        (completedVirtualNormalGysinClass C sZ sY i hi D.bundleZY)
        (completedVirtualNormalGysinClass C sY sX j hj D.bundleYX) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  refine eq_of_completedBivariantSequenceOfInvertible_apply_eq C _ _ _ _ fun n ↦ ?_
  exact BivariantClass.eq_of_bivariantRestriction_eq C sZ sX (i ≫ j)
    (comp_comp_structureMorphism_eq hi hj) (compositionNeighbourhood (i := i) (j := j))
    (le_preimage_compositionNeighbourhood (i := i) (j := j))
    (fun a ↦ bivariantRestriction_compositionNeighbourhood_eq_of_cases hiso hcart sZ sY sX hi hj D
      a n)

end Main

end Stacks.Chow

end
