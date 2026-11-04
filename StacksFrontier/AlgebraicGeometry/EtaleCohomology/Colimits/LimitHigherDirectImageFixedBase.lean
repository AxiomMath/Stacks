module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImage

/-!
# Higher direct images along a limit of schemes over a fixed base

Let `S` be a scheme, let `I` be a preordered set and let `(X_i, f_{i'i})` be an inverse system of
schemes over `I` whose members carry structure morphisms `g_i : X_i ⟶ S` compatible with the
transitions, `g_{i'} = f_{i'i} ≫ g_i`. Let `f_i : X ⟶ X_i` be the projections of a cone over the
system and let `g : X ⟶ S` satisfy `g = f_i ≫ g_i`. Let `(ℱ_i, φ_{i'i})` be a system of abelian
sheaves on `(X_i, f_{i'i})` in the sense of Stacks 0EZL and let `ℱ` on the small étale site of
`X` carry maps `ι_i : f_i^{-1}ℱ_i ⟶ ℱ`. Stacks 09Z1 asserts

`R^p g_* ℱ = colim_{i ∈ I} R^p g_{i, *} ℱ_i`

in the category of abelian sheaves on the small étale site of `S`. This file constructs the two
families of maps that assertion is about:

* `ψ_{i'i} : R^p g_{i, *} ℱ_i ⟶ R^p g_{i', *} ℱ_{i'}`, the base change map of Stacks 0F02 for
  the square `g_{i'} ≫ 𝟙_S = f_{i'i} ≫ g_i`, followed by `R^p g_{i', *} φ_{i'i}`;
* `ψ_i : R^p g_{i, *} ℱ_i ⟶ R^p g_* ℱ`, the base change map of the square
  `g ≫ 𝟙_S = f_i ≫ g_i`, followed by `R^p g_* ι_i`.

Both live in the category of abelian sheaves on the small étale site of `S` itself, with no
inverse image along a transition of the base intervening: the base of Stacks 09Z1 is the *same*
scheme `S` at every index, so the inverse image occurring in the base change map of Stacks 0F02
is the one along `𝟙_S`, and it is removed by the comparison
`Stacks.EtaleCohomology.smallEtalePullbackAbIdOf` of that inverse image with the identity
functor.

## Main definitions

* `Stacks.EtaleCohomology.FixedBaseHigherDirectImage.stage` — the sheaf `R^p g_{i, *} ℱ_i` on the
  small étale site of `S`.
* `Stacks.EtaleCohomology.FixedBaseHigherDirectImage.transitionMap` — the map `ψ_{i'i}`.
* `Stacks.EtaleCohomology.FixedBaseHigherDirectImage.projectionMap` — the map `ψ_i`.

## Main results

* `Stacks.EtaleCohomology.FixedBaseHigherDirectImage.transitionMap_naturality` and
  `Stacks.EtaleCohomology.FixedBaseHigherDirectImage.projectionMap_naturality` — both families
  are natural in the system of sheaves: a map of systems commutes with them. This is what makes
  the two families available to the dimension-shifting induction of the source, which runs over a
  short exact sequence of systems.

## Implementation notes

The source assumes `I` directed, the `g_i` and `g` quasi-compact and quasi-separated, and the
transition morphisms affine. None of those enters the construction of the maps or the naturality
statements, so none of them is a hypothesis here; they are what the colimit assertion needs. The
cone over the system is likewise not required to be a limit cone, and `g` is given together with
the equation `g = f_i ≫ g_i` rather than produced from a limit property, so that no connectedness
of the index category is needed to recognise `S` as the limit of the constant system.

The sheaf `ℱ` and the maps `ι_i` presenting `colim f_i^{-1}ℱ_i` are hypotheses, as in the source,
where `ℱ = colim f_i^{-1}ℱ_i` is given data rather than a construction.

The comparison of the inverse image along an identity with the identity functor is not rebuilt
here: it is `Stacks.EtaleCohomology.smallEtalePullbackAbIdOf`, imported from
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedIdentity` and
used at `u = 𝟙_S`, whose proof runs through base change along the identity
(`Stacks.EtaleCohomology.smallEtaleBaseChangeId`) and the direct image
(`Stacks.EtaleCohomology.smallEtalePushforwardAbIdOf`) of which it is the left adjoint.

What is *not* proved here is the colimit assertion of Stacks 09Z1, and the clause strings of the
tag say so. The inputs it needs are recorded on
`Stacks.EtaleCohomology.LimitHigherDirectImage.transitionMap` and on
`Stacks.EtaleCohomology.LimitHigherDirectImage.isColimit_pushforwardStage_of_isLimit`: the cocycle
condition and the cocone identity are there, unconditionally, for the transition maps of a system
of bases, but are not transported to the fixed base, where the comparisons of the inverse image
along `𝟙_S` have to be moved past them; and the colimit assertion itself needs Theorem 09YQ at
quasi-compact quasi-separated levels together with the comparison of Stacks 04HR at the level of
cohomology,
the carriers of Stacks 09YQ in this repository being stated for the right-derived
`CategoryTheory.sheafSections` of the small *affine* étale sites.

## References

* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)

Tags covered: 09Z1 (the comparison maps and their naturality).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology

namespace FixedBaseHigherDirectImage

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {S : Scheme.{u}}
  (g : ∀ i : Iᵒᵖ, D.obj i ⟶ S) (p : ℕ)

/-- The sheaf `R^p g_{i, *} ℱ_i` on the small étale site of the base, the `i`-th object of the
diagram of Stacks 09Z1. -/
abbrev stage (F : EtaleSheafSystem D Ab.{u + 1}) (i : Iᵒᵖ) :
    Sheaf (smallEtaleTopology S) Ab.{u + 1} :=
  ((smallEtalePushforwardAb (g i)).rightDerived p).obj (F.obj i)

/-- The transition map `ψ_{i'i} : R^p g_{i, *} ℱ_i ⟶ R^p g_{i', *} ℱ_{i'}`: the base change map
`higherBaseChangeMapAb` for the square `g_{i'} ≫ 𝟙_S = f_{i'i} ≫ g_i`, read through the
identification of the inverse image along `𝟙_S` with the identity functor, followed by
`R^p g_{i', *}` of the transition map `φ_{i'i} : f_{i'i}^{-1}ℱ_i ⟶ ℱ_{i'}` of the system of
sheaves. -/
@[stacks 09Z1 "the transition maps `ψ_{i'i} : R^p g_{i, *} ℱ_i ⟶ R^p g_{i', *} ℱ_{i'}` of the \
diagram whose colimit the lemma computes, constructed from the base change map on higher direct \
images of Stacks 0F02 for the square over the fixed base and the transition map of the system of \
sheaves. The cocycle condition `ψ_{i''i} = ψ_{i''i'} ∘ ψ_{i'i}` is NOT proved here: the \
pasting law it reduces to, `Stacks.EtaleCohomology.higherBaseChangeMapAb_paste_app`, is \
unconditional, and the cocycle condition for the transition maps of a system of bases is \
`Stacks.EtaleCohomology.LimitHigherDirectImage.transitionMap_comp`, but neither is transported \
to the fixed base, where the comparisons of the inverse image along `𝟙_S` have to be moved past \
them. The colimit assertion \
`R^p g_* ℱ = colim_i R^p g_{i, *} ℱ_i` is NOT proved either; it additionally needs Theorem 09YQ \
at quasi-compact quasi-separated levels and the comparison of Stacks 04HR at the level of \
cohomology, the carriers of 09YQ in this repository being stated for the right-derived \
`CategoryTheory.sheafSections` of the small AFFINE étale sites."]
def transitionMap (F : EtaleSheafSystem D Ab.{u + 1}) {i j : Iᵒᵖ} (a : i ⟶ j)
    (w : g i = D.map a ≫ g j) :
    stage g p F j ⟶ stage g p F i :=
  (smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.app (stage g p F j) ≫
    (higherBaseChangeMapAb (𝟙 S) (g j) (g i) (D.map a)
          ((Category.comp_id (g i)).trans w) p).app (F.obj j) ≫
      ((smallEtalePushforwardAb (g i)).rightDerived p).map (F.map a)

/-- **The transition maps are natural in the system of sheaves.** A family `α_i : ℱ_i ⟶ ℱ'_i`
commuting with the transition maps of the two systems commutes with the maps `ψ_{i'i}` they
induce. This is what lets the dimension-shifting induction of the source, which runs over a short
exact sequence of systems, compare the maps of its three terms. -/
theorem transitionMap_naturality {F F' : EtaleSheafSystem D Ab.{u + 1}}
    (α : ∀ i : Iᵒᵖ, F.obj i ⟶ F'.obj i)
    (hα : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (smallEtalePullbackAb (D.map a)).map (α j) ≫ F'.map a = F.map a ≫ α i)
    {i j : Iᵒᵖ} (a : i ⟶ j) (w : g i = D.map a ≫ g j) :
    ((smallEtalePushforwardAb (g j)).rightDerived p).map (α j) ≫ transitionMap g p F' a w =
      transitionMap g p F a w ≫
        ((smallEtalePushforwardAb (g i)).rightDerived p).map (α i) := by
  have hid := (smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.naturality
    (((smallEtalePushforwardAb (g j)).rightDerived p).map (α j))
  have hnat := (higherBaseChangeMapAb (𝟙 S) (g j) (g i) (D.map a)
    ((Category.comp_id (g i)).trans w) p).naturality (α j)
  dsimp only [Functor.comp_map] at hnat
  dsimp only [transitionMap]
  dsimp only [Functor.id_map] at hid
  simp only [Category.assoc]
  rw [reassoc_of% hid, reassoc_of% hnat, ← Functor.map_comp, hα a, Functor.map_comp]

variable (c : Cone D) (gX : c.pt ⟶ S) (𝓕 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1})

/-- The map `ψ_i : R^p g_{i, *} ℱ_i ⟶ R^p g_* ℱ`: the base change map `higherBaseChangeMapAb`
for the square `g ≫ 𝟙_S = f_i ≫ g_i`, read through the identification of the inverse image along
`𝟙_S` with the identity functor, followed by `R^p g_*` of the map `ι_i : f_i^{-1}ℱ_i ⟶ ℱ`
presenting `ℱ` as `colim f_i^{-1}ℱ_i`. -/
@[stacks 09Z1 "the cocone maps `ψ_i : R^p g_{i, *} ℱ_i ⟶ R^p g_* ℱ` whose universality the \
lemma asserts, constructed from the base change map on higher direct images of Stacks 0F02 for \
the square over the fixed base and the map `ι_i : f_i^{-1}ℱ_i ⟶ ℱ` presenting the colimit. The \
compatibility `ψ_{i'} ∘ ψ_{i'i} = ψ_i`, which would exhibit these maps as a cocone, is NOT \
proved, for the reason recorded on \
`Stacks.EtaleCohomology.FixedBaseHigherDirectImage.transitionMap`. The colimit assertion \
`R^p g_* ℱ = colim_i R^p g_{i, *} ℱ_i` is NOT proved."]
def projectionMap (F : EtaleSheafSystem D Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕) (i : Iᵒᵖ)
    (w : gX = c.π.app i ≫ g i) :
    stage g p F i ⟶ ((smallEtalePushforwardAb gX).rightDerived p).obj 𝓕 :=
  (smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.app (stage g p F i) ≫
    (higherBaseChangeMapAb (𝟙 S) (g i) gX (c.π.app i)
          ((Category.comp_id gX).trans w) p).app (F.obj i) ≫
      ((smallEtalePushforwardAb gX).rightDerived p).map (ι i)

/-- **The cocone maps are natural in the system of sheaves and its colimit.** A family
`α_i : ℱ_i ⟶ ℱ'_i` and a map `β : ℱ ⟶ ℱ'` compatible with the two presentations of the colimit
commute with the maps `ψ_i` they induce. -/
theorem projectionMap_naturality {F F' : EtaleSheafSystem D Ab.{u + 1}}
    {𝓕' : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}}
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (ι' : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F'.obj i) ⟶ 𝓕')
    (α : ∀ i : Iᵒᵖ, F.obj i ⟶ F'.obj i) (β : 𝓕 ⟶ 𝓕')
    (hαβ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).map (α i) ≫ ι' i = ι i ≫ β)
    (i : Iᵒᵖ) (w : gX = c.π.app i ≫ g i) :
    ((smallEtalePushforwardAb (g i)).rightDerived p).map (α i) ≫
        projectionMap g p c gX 𝓕' F' ι' i w =
      projectionMap g p c gX 𝓕 F ι i w ≫
        ((smallEtalePushforwardAb gX).rightDerived p).map β := by
  have hid := (smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.naturality
    (((smallEtalePushforwardAb (g i)).rightDerived p).map (α i))
  have hnat := (higherBaseChangeMapAb (𝟙 S) (g i) gX (c.π.app i)
    ((Category.comp_id gX).trans w) p).naturality (α i)
  dsimp only [Functor.comp_map] at hnat
  dsimp only [projectionMap]
  dsimp only [Functor.id_map] at hid
  simp only [Category.assoc]
  rw [reassoc_of% hid, reassoc_of% hnat, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun z =>
    (smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.app
          (((smallEtalePushforwardAb (g i)).rightDerived p).obj (F.obj i)) ≫
        (higherBaseChangeMapAb (𝟙 S) (g i) gX (c.π.app i)
            ((Category.comp_id gX).trans w) p).app (F.obj i) ≫
          ((smallEtalePushforwardAb gX).rightDerived p).map z) (hαβ i)

end FixedBaseHigherDirectImage

end Stacks.EtaleCohomology

end
