module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImage

/-!
# Higher direct images along a limit of morphisms: derived objects and complexes

Let `I` be a preordered set, let `(X_i, f_{i'i})` and `(S_i, h_{i'i})` be inverse systems of
schemes over `I`, and let `g_i : X_i ⟶ S_i` be a morphism from the first system to the second.
Let `f_i : X ⟶ X_i` be the projections of a cone over the first system, `h_i : S ⟶ S_i` those of
a limit cone over the second, and `g : X ⟶ S` the limit morphism, as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImage`.

Stacks 0EYM asserts `R^p g_* ℱ = colim_i h_i^{-1} R^p g_{i, *} ℱ_i` for a system of abelian
sheaves. Stacks 0GIU and 0GIV are its two consequences for *derived* coefficients:

* 0GIU: for `K_0 ∈ D^+(X_{0, étale})`, with `K_i` the pullback of `K_0` to `X_i` and `K` the
  pullback of `K_0` to `X`, one has `R^p g_* K = colim_{i ≥ 0} h_i^{-1} R^p g_{i, *} K_i` for all
  `p ∈ ℤ`;
* 0GIV: for a system of complexes of abelian sheaves `ℱ_i^•` on `X_{i, étale}` with transition
  maps of complexes `φ_{i'i} : f_{i'i}^{-1}ℱ_i^• ⟶ ℱ_{i'}^•` satisfying the cocycle condition,
  and uniformly bounded below (`ℱ_i^n = 0` for `n < a`, with `a` independent of `i`), one has
  `R^p g_*(colim f_i^{-1}ℱ_i^•) = colim_{i ≥ 0} h_i^{-1} R^p g_{i, *} ℱ_i^•` for all `p ∈ ℤ`.

This file constructs the comparison maps both assertions are about, in the bounded below derived
category, from the derived base change comparison
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb` of Stacks 0F02.

## Main definitions

* `Stacks.EtaleCohomology.LimitHigherDirectImage.derivedProjectionMap` — the comparison map
  `h_i^{-1} H^p(R g_{i, *} L) ⟶ H^p(R g_* M)` attached to an object `L` of `D^+(X_{i, étale})`,
  an object `M` of `D^+(X_{étale})` and a map `κ : R f_i^{-1} L ⟶ M`. This is the engine both
  tags specialize.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.derivedTransitionMap` — the analogous map
  `h_{i'i}^{-1} H^p(R g_{i, *} L) ⟶ H^p(R g_{i', *} L')` for a transition `i' ≥ i`.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.pullbackProjectionMap` — **[Stacks, Tag 0GIU]**
  the map `h_i^{-1} R^p g_{i, *} K_i ⟶ R^p g_* K` for `K_i` the derived pullback of
  `K_0 ∈ D^+(X_{0, étale})` to `X_i`.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.complexPullbackObj`,
  `Stacks.EtaleCohomology.LimitHigherDirectImage.complexProjectionMap` —
  **[Stacks, Tag 0GIV]** the map `h_i^{-1} R^p g_{i, *} ℱ_i^• ⟶ R^p g_* ℱ^•` for a uniformly
  bounded below system of complexes of abelian sheaves and a complex `ℱ^•` on `X` receiving the
  pullbacks `f_i^{-1}ℱ_i^•`.

## Main results

* `Stacks.EtaleCohomology.LimitHigherDirectImage.derivedProjectionMap_naturality` — the
  comparison map is natural in the pair `(L, M)` together with its map `κ`. This is what makes
  the family available to the dimension-shifting induction of the source, which runs over the
  distinguished triangle `H^a(K_0)[-a] → K_0 → τ_{≥ a + 1}K_0`.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.derivedTransitionMap_naturality` — the same for
  the transition maps.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.complexProjectionMap_eq` — the map of 0GIV is
  the map of the engine at the bounded below complexes, with `κ` the inverse of the
  right-derived-functor unit of the (exact) inverse image followed by the given map of
  complexes.

## Implementation notes

What is **not** proved here is the colimit assertion of either tag, and the clause strings of
the two tags say so. The obstruction is not the derived bookkeeping of this file but the
unproved state of Stacks 0EYM itself in this repository: its carrier
`Stacks.EtaleCohomology.LimitHigherDirectImage.transitionMap` /
`Stacks.EtaleCohomology.LimitHigherDirectImage.projectionMap` constructs the comparison maps for
sheaves and states in its own clause strings that neither the cocycle condition (which needs
pasting of base change maps, Stacks 0E47, for the bounded below map
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`) nor the colimit assertion is proved.
Both 0GIU and 0GIV are purely formal consequences of that assertion — 0GIU by dimension
shifting, 0GIV by the two spectral sequences of a Cartan-Eilenberg resolution (Stacks 015J) —
so neither can be closed before 0EYM is. In particular the colimit `colim_{i ≥ 0} h_i^{-1} R^p
g_{i, *} K_i` cannot even be *formed* as a functor here: forming it requires the first family to
be a system of sheaves on `(S_i, h_{i'i})`, which is exactly the cocycle condition that 0EYM's
carrier leaves open.

As in that carrier, and as in the source where `K` is the pullback of `K_0` and
`ℱ^• = colim f_i^{-1}ℱ_i^•` are given data, the target of the comparison map is a hypothesis
rather than a construction: 0GIU takes `K` together with isomorphisms
`κ_i : R f_i^{-1} K_i ≅ K`, and 0GIV takes `ℱ^•` together with maps of complexes
`ι_i : f_i^{-1}ℱ_i^• ⟶ ℱ^•`. This is a generalization, not a weakening: in the situation of the
source those data exist, and the construction never uses more about them than their type.

The index `p` is an arbitrary integer, as in both sources, rather than a natural number: the
derived objects live in `D^+` and `H^p` is `DerivedCategory.Plus.homologyFunctor` at `p : ℤ`.

The uniform lower bound `a` of 0GIV is carried as a hypothesis in the form the source states it
(`ℱ_i^n = 0` for `n < a`), via `CochainComplex.IsStrictlyGE`. It is what places every `ℱ_i^•` in
the bounded below homotopy category, and in the source it is additionally what bounds the range
of the spectral sequences; only the first use is exercised here.

## References

* [Stacks Project, Tag 0GIU](https://stacks.math.columbia.edu/tag/0GIU)
* [Stacks Project, Tag 0GIV](https://stacks.math.columbia.edu/tag/0GIV)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)

Tags covered: 0GIU, 0GIV (the comparison maps of the two assertions and their naturality; the
colimit assertions themselves are not proved, see the implementation notes).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology.LimitHigherDirectImage

attribute [local instance] HasDerivedCategory.standard

/-- The bounded below derived category of abelian sheaves on the small étale site of a scheme,
written `D^+(X_étale)` in the source. -/
abbrev PlusAb (X : Scheme.{u}) : Type _ :=
  DerivedCategory.Plus (Sheaf (smallEtaleTopology X) Ab.{u + 1})

/-- The degree-`p` cohomology functor on `D^+(X_étale)`, written `H^p` in the source. -/
abbrev homologyAb (X : Scheme.{u}) (p : ℤ) :
    PlusAb X ⥤ Sheaf (smallEtaleTopology X) Ab.{u + 1} :=
  DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X) Ab.{u + 1}) p

/-- The total right derived direct image `R g_* : D^+(X_étale) ⥤ D^+(S_étale)` of a morphism of
schemes, on abelian sheaves of the small étale sites. -/
abbrev derivedPushforwardAb {X S : Scheme.{u}} (g : X ⟶ S) : PlusAb X ⥤ PlusAb S :=
  (smallEtalePushforwardAb g).rightDerivedFunctorPlus

/-- The total right derived inverse image `R f^{-1} : D^+(Y_étale) ⥤ D^+(X_étale)` of a morphism
of schemes, on abelian sheaves of the small étale sites. Inverse image is exact, so this is the
degreewise inverse image. -/
abbrev derivedPullbackAb {X Y : Scheme.{u}} (f : X ⟶ Y) : PlusAb Y ⥤ PlusAb X :=
  (smallEtalePullbackAb f).rightDerivedFunctorPlus

variable {I : Type v} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS)

/-- Naturality of a composite `e ≫ H(x) ≫ H(y)` of a natural comparison, a base change map and a
map induced by a morphism `κ`, given the three commuting squares. -/
private theorem comparison_naturality_aux {C D : Type*} [Category C] [Category D] (H : C ⥤ D)
    {P P₁ : D} {A A₁ B B₁ B' B₁' : C} (s : P ⟶ P₁) (e : P ⟶ H.obj A) (e₁ : P₁ ⟶ H.obj A₁)
    (w : A ⟶ A₁) (x : A ⟶ B) (x₁ : A₁ ⟶ B₁) (u : B ⟶ B₁) (y : B ⟶ B') (y₁ : B₁ ⟶ B₁')
    (z : B' ⟶ B₁') (h1 : s ≫ e₁ = e ≫ H.map w) (h2 : w ≫ x₁ = x ≫ u) (h3 : u ≫ y₁ = y ≫ z) :
    s ≫ e₁ ≫ H.map x₁ ≫ H.map y₁ = e ≫ H.map x ≫ H.map y ≫ H.map z := by
  rw [← Category.assoc s, h1]
  simp only [Category.assoc, ← H.map_comp]
  rw [← Category.assoc, h2, Category.assoc, h3]

/-! ### The comparison map for a transition `i' ≥ i` -/

section Transition

variable (p : ℤ)

/-- **The comparison map of Stacks 0GIU and 0GIV for a transition**, at the level of bounded
below derived categories: for `L` an object of `D^+(X_{i, étale})`, `L'` an object of
`D^+(X_{i', étale})` and a map `κ : R f_{i'i}^{-1} L ⟶ L'`, the map
`h_{i'i}^{-1} H^p(R g_{i, *} L) ⟶ H^p(R g_{i', *} L')` obtained from the derived base change
comparison of the transition square `g_{i'} ≫ h_{i'i} = f_{i'i} ≫ g_i` followed by
`H^p(R g_{i', *} κ)`, the source being identified using exactness of `h_{i'i}^{-1}`. -/
def derivedTransitionMap {i j : Iᵒᵖ} (a : i ⟶ j) (L : PlusAb (DX.obj j)) (L' : PlusAb (DX.obj i))
    (κ : (derivedPullbackAb (DX.map a)).obj L ⟶ L') :
    (smallEtalePullbackAb (DS.map a)).obj
        ((homologyAb (DS.obj j) p).obj ((derivedPushforwardAb (γ.app j)).obj L)) ⟶
      (homologyAb (DS.obj i) p).obj ((derivedPushforwardAb (γ.app i)).obj L') :=
  (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
        (smallEtalePullbackAb (DS.map a)) p).inv.app
      ((derivedPushforwardAb (γ.app j)).obj L) ≫
    (homologyAb (DS.obj i) p).map
      ((smallEtaleDerivedBaseChangeAb (DS.map a) (γ.app j) (γ.app i) (DX.map a)
        (transition_comm γ a)).app L) ≫
    (homologyAb (DS.obj i) p).map ((derivedPushforwardAb (γ.app i)).map κ)

/-- **The transition comparison map is natural in its data.** A pair of maps `α : L ⟶ L₁`,
`α' : L' ⟶ L₁'` compatible with the two maps `κ`, `κ₁` commutes with the comparison maps they
induce. -/
theorem derivedTransitionMap_naturality {i j : Iᵒᵖ} (a : i ⟶ j) {L L₁ : PlusAb (DX.obj j)}
    {L' L₁' : PlusAb (DX.obj i)} (κ : (derivedPullbackAb (DX.map a)).obj L ⟶ L')
    (κ₁ : (derivedPullbackAb (DX.map a)).obj L₁ ⟶ L₁') (α : L ⟶ L₁) (α' : L' ⟶ L₁')
    (hκ : (derivedPullbackAb (DX.map a)).map α ≫ κ₁ = κ ≫ α') :
    (smallEtalePullbackAb (DS.map a)).map
          ((homologyAb (DS.obj j) p).map ((derivedPushforwardAb (γ.app j)).map α)) ≫
        derivedTransitionMap γ p a L₁ L₁' κ₁ =
      derivedTransitionMap γ p a L L' κ ≫
        (homologyAb (DS.obj i) p).map ((derivedPushforwardAb (γ.app i)).map α') := by
  dsimp only [derivedTransitionMap]
  exact comparison_naturality_aux (homologyAb (DS.obj i) p) _ _ _ _ _ _ _ _ _ _
    ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
      (smallEtalePullbackAb (DS.map a)) p).inv.naturality
        ((derivedPushforwardAb (γ.app j)).map α))
    ((smallEtaleDerivedBaseChangeAb (DS.map a) (γ.app j) (γ.app i) (DX.map a)
      (transition_comm γ a)).naturality α)
    (by simp only [Functor.comp_map, ← Functor.map_comp]; exact congrArg _ hκ)

end Transition

/-! ### The comparison map for the limit -/

section Projection

variable (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS) (p : ℤ)

/-- **The comparison map of Stacks 0GIU and 0GIV**, at the level of bounded below derived
categories: for `L` an object of `D^+(X_{i, étale})`, `M` an object of `D^+(X_étale)` and a map
`κ : R f_i^{-1} L ⟶ M`, the map `h_i^{-1} H^p(R g_{i, *} L) ⟶ H^p(R g_* M)` obtained from the
derived base change comparison of the projection square `g ≫ h_i = f_i ≫ g_i` followed by
`H^p(R g_* κ)`, the source being identified using exactness of `h_i^{-1}`. -/
def derivedProjectionMap (i : Iᵒᵖ) (L : PlusAb (DX.obj i)) (M : PlusAb cX.pt)
    (κ : (derivedPullbackAb (cX.π.app i)).obj L ⟶ M) :
    (smallEtalePullbackAb (cS.π.app i)).obj
        ((homologyAb (DS.obj i) p).obj ((derivedPushforwardAb (γ.app i)).obj L)) ⟶
      (homologyAb cS.pt p).obj
        ((derivedPushforwardAb (limitMorphism γ cX cS hcS)).obj M) :=
  (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
        (smallEtalePullbackAb (cS.π.app i)) p).inv.app
      ((derivedPushforwardAb (γ.app i)).obj L) ≫
    (homologyAb cS.pt p).map
      ((smallEtaleDerivedBaseChangeAb (cS.π.app i) (γ.app i) (limitMorphism γ cX cS hcS)
        (cX.π.app i) (limitMorphism_comp_π γ cX cS hcS i)).app L) ≫
    (homologyAb cS.pt p).map
      ((derivedPushforwardAb (limitMorphism γ cX cS hcS)).map κ)

/-- **The comparison map is natural in its data.** A pair of maps `α : L ⟶ L₁`, `β : M ⟶ M₁`
compatible with the two maps `κ`, `κ₁` commutes with the comparison maps they induce. This is
what lets the dimension-shifting induction of the source, which runs over the distinguished
triangle `H^a(K_0)[-a] → K_0 → τ_{≥ a + 1}K_0`, compare the maps of its three terms. -/
theorem derivedProjectionMap_naturality (i : Iᵒᵖ) {L L₁ : PlusAb (DX.obj i)}
    {M M₁ : PlusAb cX.pt} (κ : (derivedPullbackAb (cX.π.app i)).obj L ⟶ M)
    (κ₁ : (derivedPullbackAb (cX.π.app i)).obj L₁ ⟶ M₁) (α : L ⟶ L₁) (β : M ⟶ M₁)
    (hκ : (derivedPullbackAb (cX.π.app i)).map α ≫ κ₁ = κ ≫ β) :
    (smallEtalePullbackAb (cS.π.app i)).map
          ((homologyAb (DS.obj i) p).map ((derivedPushforwardAb (γ.app i)).map α)) ≫
        derivedProjectionMap γ cX cS hcS p i L₁ M₁ κ₁ =
      derivedProjectionMap γ cX cS hcS p i L M κ ≫
        (homologyAb cS.pt p).map
          ((derivedPushforwardAb (limitMorphism γ cX cS hcS)).map β) := by
  dsimp only [derivedProjectionMap]
  exact comparison_naturality_aux (homologyAb cS.pt p) _ _ _ _ _ _ _ _ _ _
    ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
      (smallEtalePullbackAb (cS.π.app i)) p).inv.naturality
        ((derivedPushforwardAb (γ.app i)).map α))
    ((smallEtaleDerivedBaseChangeAb (cS.π.app i) (γ.app i) (limitMorphism γ cX cS hcS)
      (cX.π.app i) (limitMorphism_comp_π γ cX cS hcS i)).naturality α)
    (by simp only [Functor.comp_map, ← Functor.map_comp]; exact congrArg _ hκ)

end Projection

/-! ### Stacks 0GIU: a bounded below derived object pulled back from one level -/

section Pullback

variable (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS) (p : ℤ) {i₀ : Iᵒᵖ}

/-- The pullback `K_i` to `X_i` of an object `K_0` of `D^+(X_{0, étale})`, for `i ≥ 0`: the total
right derived inverse image along the transition `f_{i 0} : X_i ⟶ X_0`. Inverse image is exact,
so this is `K_0` pulled back degreewise. -/
abbrev derivedLevelPullback {i : Iᵒᵖ} (a : i ⟶ i₀) (K₀ : PlusAb (DX.obj i₀)) : PlusAb (DX.obj i) :=
  (derivedPullbackAb (DX.map a)).obj K₀

/-- **The comparison map of Stacks 0GIU**, `h_i^{-1} R^p g_{i, *} K_i ⟶ R^p g_* K`, for
`K_0 ∈ D^+(X_{0, étale})`, `K_i` the pullback of `K_0` to `X_i` and `K` the pullback of `K_0` to
`X`: the derived comparison map `derivedProjectionMap` at `L = K_i`, `M = K` and
`κ = κ_i : R f_i^{-1} K_i ≅ K`. -/
@[stacks 0GIU "the comparison maps `h_i^{-1} R^p g_{i, *} K_i ⟶ R^p g_* K` of the assertion, \
for all `p ∈ ℤ`, with `K_i` the derived pullback of `K_0 ∈ D^+(X_{0, étale})` to `X_i`, built \
from the derived base change comparison of Stacks 0F02 together with exactness of `h_i^{-1}`; \
their naturality in `K_0` is `derivedProjectionMap_naturality`. The colimit assertion \
`R^p g_* K = colim_{i ≥ 0} h_i^{-1} R^p g_{i, *} K_i` is NOT proved, and cannot be: it is a \
formal consequence (by the dimension-shifting induction of the source over the triangle \
`H^a(K_0)[-a] → K_0 → τ_{≥ a+1}K_0`) of the colimit assertion of Stacks 0EYM, which the carrier \
`Stacks.EtaleCohomology.LimitHigherDirectImage.projectionMap` of that tag states in its own \
clause string is not proved; indeed the colimit itself cannot be formed, since that needs the \
cocycle condition of Stacks 0E47 which 0EYM's carrier also leaves open. EXTRA HYPOTHESIS: the \
pullback `K` of `K_0` to `X` and the isomorphisms `κ_i : R f_i^{-1} K_i ≅ K` are taken as data, \
as `ℱ` and `ι_i` are in 0EYM's carrier and as `K` is given data in the source; this is a \
generalization, since in the source's situation those data exist."]
def pullbackProjectionMap (K₀ : PlusAb (DX.obj i₀)) (K : PlusAb cX.pt) {i : Iᵒᵖ} (a : i ⟶ i₀)
    (κ : (derivedPullbackAb (cX.π.app i)).obj (derivedLevelPullback a K₀) ≅ K) :
    (smallEtalePullbackAb (cS.π.app i)).obj
        ((homologyAb (DS.obj i) p).obj
          ((derivedPushforwardAb (γ.app i)).obj (derivedLevelPullback a K₀))) ⟶
      (homologyAb cS.pt p).obj
        ((derivedPushforwardAb (limitMorphism γ cX cS hcS)).obj K) :=
  derivedProjectionMap γ cX cS hcS p i (derivedLevelPullback a K₀) K κ.hom

/-- The map of Stacks 0GIU is the derived comparison map of `derivedProjectionMap` at the
pullbacks of `K_0`. -/
theorem pullbackProjectionMap_eq (K₀ : PlusAb (DX.obj i₀)) (K : PlusAb cX.pt) {i : Iᵒᵖ}
    (a : i ⟶ i₀) (κ : (derivedPullbackAb (cX.π.app i)).obj (derivedLevelPullback a K₀) ≅ K) :
    pullbackProjectionMap γ cX cS hcS p K₀ K a κ =
      derivedProjectionMap γ cX cS hcS p i (derivedLevelPullback a K₀) K κ.hom :=
  rfl

end Pullback

/-! ### Stacks 0GIV: a uniformly bounded below system of complexes -/

section Complexes

/-- A cochain complex of abelian sheaves on the small étale site of a scheme which vanishes in
degrees `< a`, as an object of the bounded below homotopy category. -/
def plusHomotopyObj {X : Scheme.{u}} (a : ℤ)
    (F : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ) [F.IsStrictlyGE a] :
    HomotopyCategory.Plus (Sheaf (smallEtaleTopology X) Ab.{u + 1}) :=
  ⟨(HomotopyCategory.quotient _ _).obj F, by
    rw [HomotopyCategory.plus_quotient_obj_iff]; exact ⟨a, inferInstance⟩⟩

/-- A cochain complex of abelian sheaves on the small étale site of a scheme which vanishes in
degrees `< a`, as an object of `D^+(X_étale)`. This is the object whose degree-`p` cohomology of
the total right derived direct image is the hypercohomology `R^p g_*` of the complex. -/
abbrev plusComplexObj {X : Scheme.{u}} (a : ℤ)
    (F : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ) [F.IsStrictlyGE a] :
    PlusAb X :=
  DerivedCategory.Plus.Qh.obj (plusHomotopyObj a F)

variable (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS) (p : ℤ) (a : ℤ)

/-- The termwise inverse image `f_i^{-1}ℱ_i^•` along the projection `f_i : X ⟶ X_i` of a complex
of abelian sheaves on `X_{i, étale}`. -/
abbrev complexPullbackObj (i : Iᵒᵖ)
    (F : CochainComplex (Sheaf (smallEtaleTopology (DX.obj i)) Ab.{u + 1}) ℤ) :
    CochainComplex (Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}) ℤ :=
  ((smallEtalePullbackAb (cX.π.app i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj F

/-- The comparison `R f_i^{-1}(ℱ_i^•) ⟶ ℱ^•` in `D^+(X_étale)` attached to a map of complexes
`ι_i : f_i^{-1}ℱ_i^• ⟶ ℱ^•`: inverse image is exact, so the unit of its total right derived
functor is invertible, and the comparison is the inverse of that unit followed by the class of
`ι_i`. -/
def complexPullbackComparison (i : Iᵒᵖ)
    (F : CochainComplex (Sheaf (smallEtaleTopology (DX.obj i)) Ab.{u + 1}) ℤ) [F.IsStrictlyGE a]
    (G : CochainComplex (Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}) ℤ) [G.IsStrictlyGE a]
    (ι : complexPullbackObj cX i F ⟶ G) :
    (derivedPullbackAb (cX.π.app i)).obj (plusComplexObj a F) ⟶ plusComplexObj a G :=
  letI : IsIso (smallEtalePullbackAb (cX.π.app i)).rightDerivedFunctorPlusUnith :=
    (smallEtalePullbackAb (cX.π.app i)).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  letI : IsIso ((smallEtalePullbackAb (cX.π.app i)).rightDerivedFunctorPlusUnith.app
      (plusHomotopyObj a F)) :=
    NatIso.isIso_app_of_isIso _ _
  let ι' : (smallEtalePullbackAb (cX.π.app i)).mapHomotopyCategoryPlus.obj
      (plusHomotopyObj a F) ⟶ plusHomotopyObj a G :=
    ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map ι)
  inv ((smallEtalePullbackAb (cX.π.app i)).rightDerivedFunctorPlusUnith.app
      (plusHomotopyObj a F)) ≫ DerivedCategory.Plus.Qh.map ι'

/-- **The comparison map of Stacks 0GIV**, `h_i^{-1} R^p g_{i, *} ℱ_i^• ⟶ R^p g_* ℱ^•`, for a
complex `ℱ_i^•` of abelian sheaves on `X_{i, étale}` vanishing in degrees `< a`, a complex `ℱ^•`
on `X_étale` vanishing in degrees `< a`, and a map of complexes
`ι_i : f_i^{-1}ℱ_i^• ⟶ ℱ^•`: the derived comparison map `derivedProjectionMap` at the classes of
the two complexes in the bounded below derived categories, with `κ` the comparison
`complexPullbackComparison`. -/
@[stacks 0GIV "the comparison maps `h_i^{-1} R^p g_{i, *} ℱ_i^• ⟶ R^p g_* ℱ^•` of the \
assertion, for all `p ∈ ℤ`, where `R^p g_*` of a complex is the degree-`p` cohomology of the \
total right derived direct image of its class in `D^+`; built from the derived base change \
comparison of Stacks 0F02, exactness of `h_i^{-1}`, and — for the pullback of the complex — the \
invertibility of the right-derived-functor unit of the exact functor `f_i^{-1}`. The uniform \
lower bound `a` of the source (`ℱ_i^n = 0` for `n < a`, `a` independent of `i`) is carried as \
`CochainComplex.IsStrictlyGE`; naturality is `derivedProjectionMap_naturality`. The colimit \
assertion `R^p g_*(colim f_i^{-1}ℱ_i^•) = colim_{i ≥ 0} h_i^{-1} R^p g_{i, *} ℱ_i^•` is NOT \
proved, and cannot be: it is a formal consequence (by the two spectral sequences of a \
Cartan-Eilenberg resolution, Stacks 015J) of the colimit assertion of Stacks 0EYM, which the \
carrier `Stacks.EtaleCohomology.LimitHigherDirectImage.projectionMap` of that tag states in its \
own clause string is not proved; indeed the colimit itself cannot be formed, since that needs \
the cocycle condition of Stacks 0E47 which 0EYM's carrier also leaves open. EXTRA HYPOTHESIS: \
the complex `ℱ^• = colim f_i^{-1}ℱ_i^•` and the maps of complexes `ι_i : f_i^{-1}ℱ_i^• ⟶ ℱ^•` \
are taken as data, as `ℱ` and `ι_i` are in 0EYM's carrier and as the colimit is given data in \
the source; this is a generalization, since in the source's situation those data exist. The \
transition maps `φ_{i'i}` and their cocycle condition are the data of the system; the \
transition form of the comparison map is `derivedTransitionMap`."]
def complexProjectionMap (i : Iᵒᵖ)
    (F : CochainComplex (Sheaf (smallEtaleTopology (DX.obj i)) Ab.{u + 1}) ℤ) [F.IsStrictlyGE a]
    (G : CochainComplex (Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}) ℤ) [G.IsStrictlyGE a]
    (ι : complexPullbackObj cX i F ⟶ G) :
    (smallEtalePullbackAb (cS.π.app i)).obj
        ((homologyAb (DS.obj i) p).obj
          ((derivedPushforwardAb (γ.app i)).obj (plusComplexObj a F))) ⟶
      (homologyAb cS.pt p).obj
        ((derivedPushforwardAb (limitMorphism γ cX cS hcS)).obj (plusComplexObj a G)) :=
  derivedProjectionMap γ cX cS hcS p i (plusComplexObj a F) (plusComplexObj a G)
    (complexPullbackComparison cX a i F G ι)

/-- The map of Stacks 0GIV is the derived comparison map of `derivedProjectionMap` at the
classes of the two complexes, with `κ` the comparison `complexPullbackComparison`. -/
theorem complexProjectionMap_eq (i : Iᵒᵖ)
    (F : CochainComplex (Sheaf (smallEtaleTopology (DX.obj i)) Ab.{u + 1}) ℤ) [F.IsStrictlyGE a]
    (G : CochainComplex (Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}) ℤ) [G.IsStrictlyGE a]
    (ι : complexPullbackObj cX i F ⟶ G) :
    complexProjectionMap γ cX cS hcS p a i F G ι =
      derivedProjectionMap γ cX cS hcS p i (plusComplexObj a F) (plusComplexObj a G)
        (complexPullbackComparison cX a i F G ι) :=
  rfl

end Complexes

end Stacks.EtaleCohomology.LimitHigherDirectImage

end
