module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SheafSystems

/-!
# Higher direct images along a limit of morphisms of schemes

Let `I` be a preordered set, let `(X_i, f_{i'i})` and `(S_i, h_{i'i})` be inverse systems of
schemes over `I`, and let `g_i : X_i ⟶ S_i` be a morphism from the first system to the second, so
that for `i' ≥ i` the square `g_{i'} ≫ h_{i'i} = f_{i'i} ≫ g_i` commutes. Let `f_i : X ⟶ X_i` be
the projections of a cone over the first system and `h_i : S ⟶ S_i` those of a limit cone over the
second. The limit morphism `g : X ⟶ S` is the unique morphism with `g ≫ h_i = f_i ≫ g_i`.

Let `(ℱ_i, φ_{i'i})` be a system of abelian sheaves on `(X_i, f_{i'i})` in the sense of Stacks
0EZL, and let `ℱ` on the small étale site of `X` carry maps `ι_i : f_i^{-1}ℱ_i ⟶ ℱ`. Stacks 0EYM
asserts `R^p g_* ℱ = colim_i h_i^{-1} R^p g_{i, *} ℱ_i`. This file constructs the two families of
maps that assertion is about, from the base change map on higher direct images of Stacks 0F02:

* `ψ_{i'i} : h_{i'i}^{-1} R^p g_{i, *} ℱ_i ⟶ R^p g_{i', *} ℱ_{i'}`, the base change map of the
  transition square followed by `R^p g_{i', *} φ_{i'i}`;
* `ψ_i : h_i^{-1} R^p g_{i, *} ℱ_i ⟶ R^p g_* ℱ`, the base change map of the projection square
  followed by `R^p g_* ι_i`.

## Main definitions

* `Stacks.EtaleCohomology.LimitHigherDirectImage.limitMorphism` — the limit morphism `g : X ⟶ S`.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.transitionMap` — the map `ψ_{i'i}`.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.projectionMap` — the map `ψ_i`.

## Main results

* `Stacks.EtaleCohomology.LimitHigherDirectImage.limitMorphism_comp_π` — the limit morphism
  satisfies `g ≫ h_i = f_i ≫ g_i`, the commutativity of the projection square.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.transitionMap_naturality`,
  `Stacks.EtaleCohomology.LimitHigherDirectImage.projectionMap_naturality` — both families are
  natural in the system of sheaves: a map of systems commutes with them. This is what makes the
  two families available to the dimension-shifting induction of the source, which runs over a
  short exact sequence of systems.

## Implementation notes

The source assumes `I` directed, the `g_i` quasi-compact and quasi-separated, and the transition
morphisms affine. None of those enters the construction of the maps or the naturality statements,
so none of them is a hypothesis here; they are what the colimit assertion needs. The cone over
the system of the `X_i` is likewise not required to be a limit cone: only the limit property of
the cone over the `S_i` is used, to produce `g`.

The sheaf `ℱ` and the maps `ι_i` presenting `colim f_i^{-1}ℱ_i` are hypotheses, as in the source,
where `ℱ = colim f_i^{-1}ℱ_i` is given data rather than a construction, and as in
`Stacks.EtaleCohomology.QcqsLimitCohomology`.

What is *not* proved here is the colimit assertion of Stacks 0EYM, and the clause strings of the
tag say so. Two inputs of the source's argument are missing from the base of this repository, in
the forms the argument consumes them.

The first is the pasting of base change maps, Stacks 0E47, which the source cites for the two
compatibilities `ψ_{i''i} = ψ_{i''i'} ∘ h_{i''i'}^{-1}ψ_{i'i}` and
`ψ_{i'} ∘ h_{i'}^{-1}ψ_{i'i} = ψ_i`. Those compatibilities are what would turn the first family
into a system of sheaves on `(S_i, h_{i'i})` and the second into a cocone over it. Pasting is
available for the base change map of ringed topoi on sheaves of modules
(`Stacks.Cohomology.DerivedBaseChangePasting.derivedBaseChangeMap_horizontal`) and for the
unbounded derived base change map of abelian étale sheaves
(`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_comp_app`), but not for the bounded below
map `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb` through which
`Stacks.EtaleCohomology.higherBaseChangeMapAb`, and hence `ψ`, is defined.

The second is the comparison of Stacks 04HR at the level of cohomology. The source's argument
runs on the small *affine* étale site, where Stacks 0EYL presents the site of the limit as the
colimit of the sites of the levels and Stacks 09YQ computes the cohomology of a colimit of
sheaves. Both carriers of Stacks 09YQ in this repository state in their own clause strings that
their cohomology is the right-derived `sheafSections` on the small affine étale sites and that the
comparison across Stacks 04HR is not performed. The higher direct images here are those of the
small étale site, `Stacks.EtaleCohomology.smallEtalePushforwardAb` right-derived, which is where
Stacks 03Q8 and 04I2 live, so that comparison is exactly the bridge the colimit assertion needs.

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)

Tags covered: 0EYM (the comparison maps and their naturality).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology.LimitHigherDirectImage

variable {I : Type v} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS)

/-- The transition square `g_{i'} ≫ h_{i'i} = f_{i'i} ≫ g_i` of a morphism of inverse systems of
schemes: the naturality square of `γ`, in the orientation the base change map expects. -/
theorem transition_comm {i j : Iᵒᵖ} (a : i ⟶ j) :
    γ.app i ≫ DS.map a = DX.map a ≫ γ.app j :=
  (γ.naturality a).symm

variable (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS)

/-- **The limit `g : X ⟶ S` of a system of morphisms of schemes** `g_i : X_i ⟶ S_i`: the morphism
to the limit of the `S_i` induced by the compatible family `f_i ≫ g_i`. -/
def limitMorphism : cX.pt ⟶ cS.pt :=
  hcS.lift ((Cone.postcompose γ).obj cX)

/-- The projection square `g ≫ h_i = f_i ≫ g_i` of the limit morphism. -/
theorem limitMorphism_comp_π (i : Iᵒᵖ) :
    limitMorphism γ cX cS hcS ≫ cS.π.app i = cX.π.app i ≫ γ.app i :=
  hcS.fac _ i

/-- Naturality of a transformation `G ⟶ P ⋙ K` against a map `ι` followed by `K.map`, for maps
`ι`, `ι'`, `β` and `α` with `P.map α ≫ ι' = ι ≫ β`. -/
private theorem map_comp_app_comp_map_naturality {C D E : Type*} [Category C] [Category D]
    [Category E] {G : C ⥤ E} {P : C ⥤ D} {K : D ⥤ E} (τ : G ⟶ P ⋙ K) {A A' : C} {B B' : D}
    (α : A ⟶ A') (ι : P.obj A ⟶ B) (ι' : P.obj A' ⟶ B') (β : B ⟶ B')
    (h : P.map α ≫ ι' = ι ≫ β) :
    G.map α ≫ τ.app A' ≫ K.map ι' = (τ.app A ≫ K.map ι) ≫ K.map β := by
  rw [← Category.assoc, τ.naturality α, Category.assoc, Category.assoc, Functor.comp_map,
    ← K.map_comp, h, K.map_comp]

variable (p : ℕ)

/-- **The transition maps of Stacks 0EYM**, `ψ_{i'i} : h_{i'i}^{-1} R^p g_{i, *} ℱ_i ⟶
R^p g_{i', *} ℱ_{i'}`: the base change map of the transition square
`g_{i'} ≫ h_{i'i} = f_{i'i} ≫ g_i` on higher direct images, followed by `R^p g_{i', *}` of the
transition map `φ_{i'i} : f_{i'i}^{-1}ℱ_i ⟶ ℱ_{i'}` of the system of sheaves. -/
@[stacks 0EYM "the transition maps `ψ_{i'i} : h_{i'i}^{-1} R^p g_{i, *} ℱ_i ⟶ \
R^p g_{i', *} ℱ_{i'}` of the first paragraph of the proof, constructed from the base change map \
on higher direct images of Stacks 0F02 and the transition map of the system of sheaves. The \
cocycle condition `ψ_{i''i} = ψ_{i''i'} ∘ h_{i''i'}^{-1}ψ_{i'i}`, which the source gets from \
Stacks 0E47, is NOT proved: pasting of base change maps is carried for ringed topoi on sheaves \
of modules and for the unbounded derived étale base change map, but not for the bounded below \
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb` that \
`Stacks.EtaleCohomology.higherBaseChangeMapAb` descends from. The colimit assertion \
`R^p g_* ℱ = colim_i h_i^{-1} R^p g_{i, *} ℱ_i` is NOT proved either; it additionally needs the \
comparison of Stacks 04HR at the level of cohomology, the carried Stacks 09YQ being stated for \
the right-derived `sheafSections` of the small AFFINE étale sites."]
def transitionMap (F : EtaleSheafSystem DX Ab.{u + 1}) {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtalePullbackAb (DS.map a)).obj
        (((smallEtalePushforwardAb (γ.app j)).rightDerived p).obj (F.obj j)) ⟶
      ((smallEtalePushforwardAb (γ.app i)).rightDerived p).obj (F.obj i) :=
  (higherBaseChangeMapAb (DS.map a) (γ.app j) (γ.app i) (DX.map a)
        (transition_comm γ a) p).app (F.obj j) ≫
    ((smallEtalePushforwardAb (γ.app i)).rightDerived p).map (F.map a)

/-- **The transition maps are natural in the system of sheaves.** A family `α_i : ℱ_i ⟶ ℱ'_i`
commuting with the transition maps of the two systems commutes with the maps `ψ_{i'i}` they
induce. This is what lets the dimension-shifting induction of the source, which runs over a short
exact sequence of systems, compare the maps of its three terms. -/
theorem transitionMap_naturality {F F' : EtaleSheafSystem DX Ab.{u + 1}}
    (α : ∀ i : Iᵒᵖ, F.obj i ⟶ F'.obj i)
    (hα : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (smallEtalePullbackAb (DX.map a)).map (α j) ≫ F'.map a = F.map a ≫ α i)
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtalePullbackAb (DS.map a)).map
          (((smallEtalePushforwardAb (γ.app j)).rightDerived p).map (α j)) ≫
        transitionMap γ p F' a =
      transitionMap γ p F a ≫
        ((smallEtalePushforwardAb (γ.app i)).rightDerived p).map (α i) := by
  exact map_comp_app_comp_map_naturality (higherBaseChangeMapAb (DS.map a) (γ.app j) (γ.app i)
    (DX.map a) (transition_comm γ a) p) _ _ _ _ (hα a)

variable (𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})

/-- **The cocone maps of Stacks 0EYM**, `ψ_i : h_i^{-1} R^p g_{i, *} ℱ_i ⟶ R^p g_* ℱ`: the base
change map of the projection square `g ≫ h_i = f_i ≫ g_i` on higher direct images, followed by
`R^p g_*` of the map `ι_i : f_i^{-1}ℱ_i ⟶ ℱ` presenting `ℱ` as `colim f_i^{-1}ℱ_i`. -/
@[stacks 0EYM "the cocone maps `ψ_i : h_i^{-1} R^p g_{i, *} ℱ_i ⟶ R^p g_* ℱ` of the first \
paragraph of the proof, constructed from the base change map on higher direct images of Stacks \
0F02 and the map `ι_i : f_i^{-1}ℱ_i ⟶ ℱ` presenting the colimit. The compatibility \
`ψ_{i'} ∘ h_{i'}^{-1}ψ_{i'i} = ψ_i`, which the source gets from Stacks 0E47, is NOT proved, for \
the reason recorded on `transitionMap`; so these maps are not exhibited as a cocone. The colimit \
assertion `R^p g_* ℱ = colim_i h_i^{-1} R^p g_{i, *} ℱ_i` is NOT proved."]
def projectionMap (F : EtaleSheafSystem DX Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕) (i : Iᵒᵖ) :
    (smallEtalePullbackAb (cS.π.app i)).obj
        (((smallEtalePushforwardAb (γ.app i)).rightDerived p).obj (F.obj i)) ⟶
      ((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived p).obj 𝓕 :=
  (higherBaseChangeMapAb (cS.π.app i) (γ.app i) (limitMorphism γ cX cS hcS) (cX.π.app i)
        (limitMorphism_comp_π γ cX cS hcS i) p).app (F.obj i) ≫
    ((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived p).map (ι i)

/-- **The cocone maps are natural in the system of sheaves and its colimit.** A family
`α_i : ℱ_i ⟶ ℱ'_i` and a map `β : ℱ ⟶ ℱ'` compatible with the two presentations of the colimit
commute with the maps `ψ_i` they induce. -/
theorem projectionMap_naturality {F F' : EtaleSheafSystem DX Ab.{u + 1}}
    {𝓕' : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}}
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (ι' : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F'.obj i) ⟶ 𝓕')
    (α : ∀ i : Iᵒᵖ, F.obj i ⟶ F'.obj i) (β : 𝓕 ⟶ 𝓕')
    (hαβ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).map (α i) ≫ ι' i = ι i ≫ β)
    (i : Iᵒᵖ) :
    (smallEtalePullbackAb (cS.π.app i)).map
          (((smallEtalePushforwardAb (γ.app i)).rightDerived p).map (α i)) ≫
        projectionMap γ cX cS hcS p 𝓕' F' ι' i =
      projectionMap γ cX cS hcS p 𝓕 F ι i ≫
        ((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived p).map β := by
  exact map_comp_app_comp_map_naturality (higherBaseChangeMapAb (cS.π.app i) (γ.app i)
    (limitMorphism γ cX cS hcS) (cX.π.app i) (limitMorphism_comp_π γ cX cS hcS i) p) _ _ _ _
    (hαβ i)

end Stacks.EtaleCohomology.LimitHigherDirectImage

end
