module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleSetsVerticalPasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImage

/-!
# The comparison maps of Stacks 0EYM in degree zero form a system and a cocone

Let `I` be a preordered set, let `(X_i, f_{i'i})` and `(S_i, h_{i'i})` be inverse systems of
schemes over `I`, and let `g_i : X_i ⟶ S_i` be a morphism from the first system to the second, so
that for `i' ≥ i` the square `g_{i'} ≫ h_{i'i} = f_{i'i} ≫ g_i` commutes. Let `(ℱ_i, φ_{i'i})` be
a system of sheaves on `(X_i, f_{i'i})` in the sense of Stacks 0EZL.

Stacks 0EYM asserts `R^p g_* ℱ = colim_i h_i^{-1} R^p g_{i, *} ℱ_i` for `ℱ = colim f_i^{-1}ℱ_i`.
In degree `p = 0` the higher direct image is the direct image itself, and the assertion is about
the *underived* pushforward; the source states it for sheaves of sets as well as for abelian
sheaves, the dimension shifting that produces the higher degrees being what needs abelian
coefficients.

This file treats that degree-zero, arbitrary-coefficient case of the comparison maps, and proves
the two compatibilities that the abelian file `Colimits/LimitHigherDirectImage.lean` records as
unproved:

* the transition maps `ψ_{i'i} : h_{i'i}^{-1} g_{i, *}ℱ_i ⟶ g_{i', *}ℱ_{i'}` satisfy the cocycle
  condition `ψ_{i''i} = ψ_{i''i'} ∘ h_{i''i'}^{-1}ψ_{i'i}`, so that `(g_{i, *}ℱ_i, ψ_{i'i})` is
  itself a system of sheaves on `(S_i, h_{i'i})` in the sense of Stacks 0EZL;
* the cocone maps `ψ_i : h_i^{-1} g_{i, *}ℱ_i ⟶ g_* ℱ` satisfy
  `ψ_{i'} ∘ h_{i'}^{-1}ψ_{i'i} = ψ_i`, so that they form a cocone over that system with vertex
  `g_* ℱ`.

Together these are the whole first paragraph of the source's proof in degree zero. The first is
what makes `i ↦ h_i^{-1} g_{i, *}ℱ_i` a diagram at all, hence what the word `colim` in the
assertion presupposes; the second is what makes `g_* ℱ` a candidate for its colimit. What the
assertion then says, and what is *not* proved here, is that this cocone is a colimiting one.

The reason the underived case goes through where the abelian higher-degree case does not is that
the underived base change map is the mate, under the inverse-image/direct-image adjunctions, of
the identification of the two composite direct images around the square; so the cocycle condition
is the pasting law for those identifications, which is the associativity pentagon
`Stacks.EtaleCohomology.smallEtalePushforwardComp'_assoc` of
`Colimits/DirectImageSystem.lean` and nothing else. The abelian higher direct images are
obtained from the *bounded below derived* base change map, for which pasting is not carried.

Rather than compose a base change map with `g_{i', *}φ_{i'i}`, the map `ψ_{i'i}` is built as the
transpose of `g_{i, *}` of the transpose of `φ_{i'i}` followed by the square identification. The
two descriptions agree — the transpose of a mate is the unit followed by the square
identification — and the transposed form is the one on which the cocycle condition is an identity
between composites of comparison isomorphisms.

## Main definitions

* `Stacks.EtaleCohomology.EtaleSheafSystem.mapTranspose` — the transpose
  `ℱ_i ⟶ f_{i'i, *}ℱ_{i'}` of the transition map of a system of sheaves.
* `Stacks.EtaleCohomology.LimitDirectImage.squarePushforwardIso` — the identification
  `v_* g_{0, *} ≅ g_{1, *} u_*` of the two composite direct images around a commutative square,
  for arbitrary coefficients and with the common diagonal carried as a named morphism.
* `Stacks.EtaleCohomology.LimitDirectImage.transitionSquareIso` — that identification for the
  transition square of the system.
* `Stacks.EtaleCohomology.LimitDirectImage.transitionMap` — the map `ψ_{i'i}`.
* `Stacks.EtaleCohomology.LimitDirectImage.transitionSystem` — **the system of sheaves
  `(g_{i, *}ℱ_i, ψ_{i'i})`** on `(S_i, h_{i'i})`.
* `Stacks.EtaleCohomology.LimitDirectImage.etalePullback` and
  `Stacks.EtaleCohomology.LimitDirectImage.etaleAdjunction` — inverse image along an arbitrary
  morphism of schemes and its adjunction, the counterparts of
  `Stacks.EtaleCohomology.systemPullback` and `Stacks.EtaleCohomology.systemAdjunction` for a
  morphism that is not a transition of an inverse system.
* `Stacks.EtaleCohomology.LimitDirectImage.coneTranspose` — the transpose `ℱ_i ⟶ f_{i, *}ℱ` of a
  map `ι_i : f_i^{-1}ℱ_i ⟶ ℱ` presenting the colimit.
* `Stacks.EtaleCohomology.LimitDirectImage.projectionSquareIso` — the square identification for
  the projection square `g ≫ h_i = f_i ≫ g_i` of the limit morphism.
* `Stacks.EtaleCohomology.LimitDirectImage.projectionMap` — the map `ψ_i`.

## Main results

* `Stacks.EtaleCohomology.smallEtalePushforwardComp'_assoc_app` — the associativity pentagon of
  the comparison of direct images, evaluated at a sheaf.
* `Stacks.EtaleCohomology.EtaleSheafSystem.mapTranspose_comp` — the cocycle condition of a system
  of sheaves, transposed.
* `Stacks.EtaleCohomology.LimitDirectImage.squarePushforwardIso_paste_app` — **the pasting law**
  for the square identifications: the identification of the outer rectangle of two horizontally
  composable squares is the composite of the identifications of the two squares, read through the
  comparisons of the direct images along the two composite horizontal legs.
* `Stacks.EtaleCohomology.LimitDirectImage.transitionSquareIso_paste_app` and
  `Stacks.EtaleCohomology.LimitDirectImage.projectionSquareIso_paste_app` — that pasting law for
  the two rectangles the source's compatibilities are about.
* `Stacks.EtaleCohomology.LimitDirectImage.coneTranspose_comp` — the compatibility of a colimit
  presentation with the transition maps of the system, transposed.
* `Stacks.EtaleCohomology.LimitDirectImage.projectionMap_comp` — **the cocone condition**
  `ψ_{i'} ∘ h_{i'}^{-1}ψ_{i'i} = ψ_i`.

## Implementation notes

*What is not proved.* The colimit assertion of Stacks 0EYM itself is not proved here, in any
coefficients, and no `@[stacks 0EYM]` attribute appears: what is proved is the source's first
paragraph, that the comparison maps form a system and a cocone over it, and not the assertion
that the cocone is colimiting. The source's hypotheses that `I` is directed, that the `g_i` are
quasi-compact and quasi-separated and that the transition morphisms are affine play no role in
the first paragraph and are therefore not assumed; they are what the colimit assertion needs.
Section "The remaining inputs" of this note records what is missing.

*Named composites.* Every composite of morphisms of schemes that enters a comparison isomorphism
is carried as a named morphism together with an equation identifying it, as in
`Colimits/DirectImageSystem.lean`. This is what lets the comparison for the composite transition
`D.map (a ≫ b)` be plugged into the pasting law directly, instead of through a transport along
`Functor.map_comp`.

*Relation to the abelian pasting law.*
`Stacks.EtaleCohomology.smallEtaleSquarePushforwardIso_paste_app` of
`BaseChangeHigher/SmallEtaleBaseChangePasting.lean` is
`Stacks.EtaleCohomology.LimitDirectImage.squarePushforwardIso_paste_app` at `Ab`, with the
composites written out rather than named; its proof is the same three instances of the
associativity pentagon. That module is downstream of this directory and could be refactored onto
the general statement.

*The remaining inputs of the colimit assertion.* With the system and the cocone in hand, what the
assertion `g_* ℱ = colim_i h_i^{-1} g_{i, *}ℱ_i` for sheaves of sets still needs is that the
cocone is colimiting, and that needs:

1. a presentation of the small étale site of `S = lim S_i` as the colimit of the small étale
   sites of the `S_i`. What is carried is the *affine* étale version, Stacks 0EYL, at
   `Colimits/AffineEtaleSites.lean`; passing from it to the small étale site is the comparison of
   Stacks 04HR, whose only carrier is
   `StacksFrontier/AlgebraicGeometry/EtaleCohomology/PointsOtherTopologies/SmallEtale.lean`, stated
   for points rather than for cohomology;
2. the identification of the sections of a colimit of inverse images over an object of such a
   colimit site with the filtered colimit of the sections at the levels. This is Stacks 09YN,
   carried at
   `StacksFrontier/CategoryTheory/Sites/InverseSystem/CohomologyOfColimitOfFiniteSites.lean`, for
   abstract sites in which the covering sieves are finitely generated, with the colimit sheaf
   presented by its universal property;
3. the identification of `U ×_S X` with the limit of the `U_i ×_{S_i} X_{i'}`, for `U` an étale
   `S`-scheme descending to level `i`, which is where the affineness of the transition morphisms
   and the quasi-compactness and quasi-separatedness of the `g_i` enter.

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe w' w v u

namespace Stacks.EtaleCohomology

/-- The cocycle identity for maps `m₁ : L₁ X ⟶ Y₁`, `m₂ : L₂ Y₁ ⟶ Y₂` of left adjoints, read
on either side of the adjunctions: `m₂ ∘ L₂ m₁` composed with the comparison is `h` iff the
transpose of `h` is the composite of the transposes through the comparison of right adjoints. -/
private theorem leftAdjointCompIso_inv_comp_iff {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁]
    [Category* C₂] {L₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} (adj₁ : L₁ ⊣ R₁) {L₂ : C₁ ⥤ C₂}
    {R₂ : C₂ ⥤ C₁} (adj₂ : L₂ ⊣ R₂) {L : C₀ ⥤ C₂} {R : C₂ ⥤ C₀} (adj : L ⊣ R)
    (e : R₂ ⋙ R₁ ≅ R) {X : C₀} {Y₁ : C₁} {Y₂ : C₂} (m₁ : L₁.obj X ⟶ Y₁) (m₂ : L₂.obj Y₁ ⟶ Y₂)
    (h : L.obj X ⟶ Y₂) :
    (Adjunction.leftAdjointCompIso adj₁ adj₂ adj e).inv.app X ≫ L₂.map m₁ ≫ m₂ = h ↔
      adj.homEquiv X Y₂ h = adj₁.homEquiv X Y₁ m₁ ≫ R₁.map (adj₂.homEquiv Y₁ Y₂ m₂) ≫
        e.hom.app Y₂ := by
  have := leftAdjointCompIso_inv_homEquiv_symm adj₁ adj₂ adj e (adj₁.homEquiv X Y₁ m₁)
    (adj₂.homEquiv Y₁ Y₂ m₂)
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  rw [this, Equiv.symm_apply_eq, eq_comm]

/-! ### The transition map of a system of sheaves, transposed -/

section Transpose

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {A : Type w} [Category.{w'} A]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).IsRightAdjoint]

/-- **The transition map of a system of sheaves, transposed.** The datum
`φ_{i'i} : f_{i'i}^{-1}ℱ_i ⟶ ℱ_{i'}` of a system of sheaves in the sense of Stacks 0EZL
corresponds, under the inverse-image/direct-image adjunction along the transition morphism, to a
map `ℱ_i ⟶ f_{i'i, *}ℱ_{i'}`. -/
public def EtaleSheafSystem.mapTranspose (F : EtaleSheafSystem D A) {i j : Iᵒᵖ} (a : i ⟶ j) :
    F.obj j ⟶ (systemPushforward D A a).obj (F.obj i) :=
  (systemAdjunction D A a).homEquiv _ _ (F.map a)

/-- The transpose of the transposed transition map is the transition map itself. -/
public theorem EtaleSheafSystem.homEquiv_symm_mapTranspose (F : EtaleSheafSystem D A)
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    ((systemAdjunction D A a).homEquiv (F.obj j) (F.obj i)).symm (F.mapTranspose a) = F.map a :=
  Equiv.symm_apply_apply _ _

/-- **The cocycle condition of a system of sheaves, transposed.** The transpose of the map
attached to a composite transition is the composite of the transposes, read through the
comparison of the direct images along the two factors. -/
public theorem EtaleSheafSystem.mapTranspose_comp (F : EtaleSheafSystem D A)
    {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    F.mapTranspose (a ≫ b) =
      F.mapTranspose b ≫ (systemPushforward D A b).map (F.mapTranspose a) ≫
        (smallEtalePushforwardComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)
            A).hom.app (F.obj i) := by
  exact (leftAdjointCompIso_inv_comp_iff (systemAdjunction D A b) (systemAdjunction D A a)
    (systemAdjunction D A (a ≫ b))
    (smallEtalePushforwardComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b) A)
    (F.map b) (F.map a) _).1 (F.map_comp a b)

end Transpose

namespace LimitDirectImage

/-! ### The square identification of the two composite direct images -/

section Square

variable {X₁ X₀ S₁ S₀ : Scheme.{u}} (g₁ : X₁ ⟶ S₁) (g₀ : X₀ ⟶ S₀) (u : S₁ ⟶ S₀) (v : X₁ ⟶ X₀)
  (d : X₁ ⟶ S₀) (hdg : d = g₁ ≫ u) (hdv : d = v ≫ g₀) (A : Type w) [Category.{w'} A]

/-- **The identification `v_* g_{0, *} ≅ g_{1, *} u_*` of the two composite direct images around a
commutative square** of schemes, for arbitrary coefficients. Both composites are compared with
the direct image along the common diagonal `d`, which is carried as a named morphism together
with the two equations identifying it, so that no transport along `Category.assoc` enters.

For abelian coefficients and the diagonal written out this is
`Stacks.EtaleCohomology.smallEtaleSquarePushforwardIso`; the base change map of a square is its
mate. -/
public def squarePushforwardIso :
    smallEtalePushforward v A ⋙ smallEtalePushforward g₀ A ≅
      smallEtalePushforward g₁ A ⋙ smallEtalePushforward u A :=
  smallEtalePushforwardComp' v g₀ d hdv A ≪≫ (smallEtalePushforwardComp' g₁ u d hdg A).symm

end Square

/-! ### The pasting law -/

section Paste

/-- The cancellation that turns three instances of the associativity pentagon into the pasting
identity for the square identifications.

Stated on variables in a single category: the morphisms it is applied to are components of
comparisons of composite direct images, and at those types the rearrangement is unreadable. The
three pentagons enter as `hP₁`, `hP₂`, `hP₃`; the three remaining hypotheses are that the three
comparisons being inverted are invertible. -/
private theorem pastingAlgebra {E : Type*} [Category* E] {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ : E}
    {a : O₁ ⟶ O₂} {b : O₂ ⟶ O₃} {dd : O₄ ⟶ O₃} {d' : O₃ ⟶ O₄}
    {ee : O₁ ⟶ O₅} {gg : O₆ ⟶ O₅} {gg' : O₅ ⟶ O₆} {l : O₅ ⟶ O₃} {m : O₇ ⟶ O₃}
    {hh : O₆ ⟶ O₇} {jj : O₈ ⟶ O₇} {jj' : O₇ ⟶ O₈} {kk : O₈ ⟶ O₄}
    (hd : dd ≫ d' = 𝟙 O₄) (hg : gg' ≫ gg = 𝟙 O₅) (hj : jj' ≫ jj = 𝟙 O₇)
    (hP₁ : a ≫ b = ee ≫ l) (hP₂ : hh ≫ m = gg ≫ l) (hP₃ : jj ≫ m = kk ≫ dd) :
    a ≫ b ≫ d' = ee ≫ gg' ≫ hh ≫ jj' ≫ kk := by
  have hl : gg' ≫ hh ≫ m = l := by rw [hP₂, ← Category.assoc, hg, Category.id_comp]
  have hm : jj' ≫ kk = m ≫ d' := by
    rw [← Category.id_comp (m ≫ d'), ← hj, Category.assoc, reassoc_of% hP₃, hd,
      Category.comp_id]
  rw [hm, reassoc_of% hl, reassoc_of% hP₁]

variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}} (g₀ : X₀ ⟶ S₀) (g₁ : X₁ ⟶ S₁) (g₂ : X₂ ⟶ S₂)
  (u₁ : S₁ ⟶ S₀) (u₂ : S₂ ⟶ S₁) (v₁ : X₁ ⟶ X₀) (v₂ : X₂ ⟶ X₁)
  (u : S₂ ⟶ S₀) (v : X₂ ⟶ X₀) (d₁ : X₁ ⟶ S₀) (d₂ : X₂ ⟶ S₁) (d : X₂ ⟶ S₀)
  (hu : u = u₂ ≫ u₁) (hv : v = v₂ ≫ v₁)
  (hd₁g : d₁ = g₁ ≫ u₁) (hd₁v : d₁ = v₁ ≫ g₀)
  (hd₂g : d₂ = g₂ ≫ u₂) (hd₂v : d₂ = v₂ ≫ g₁)
  (hdg : d = g₂ ≫ u) (hdv : d = v ≫ g₀)
  (A : Type w) [Category.{w'} A]

include hu hd₂g hdg in
/-- The diagonal of the outer rectangle is also the diagonal of the first square followed by the
upper right leg. -/
private theorem rectangle_diag_right : d = d₂ ≫ u₁ := by
  rw [hdg, hu, hd₂g, Category.assoc]

include hv hd₁v hdv in
/-- The diagonal of the outer rectangle is also the upper left leg followed by the diagonal of
the second square. -/
private theorem rectangle_diag_left : d = v₂ ≫ d₁ := by
  rw [hdv, hv, hd₁v, Category.assoc]

/-- **The pasting law for the square identifications of direct images.** For two horizontally
composable commutative squares of schemes

```
X₂ --v₂--> X₁ --v₁--> X₀
|g₂         |g₁        |g₀
S₂ --u₂--> S₁ --u₁--> S₀
```

the identification of the two composite direct images around the outer rectangle is the composite
of the identifications of the two squares, read through the comparisons of the direct images along
the two composite horizontal legs `u = u₂ ≫ u₁` and `v = v₂ ≫ v₁`.

The hypotheses are the commutativity of the two squares and nothing else: the squares need not be
cartesian and no finiteness or separatedness condition enters. For abelian coefficients, with the
diagonals and the two composite legs written out rather than named, this is
`Stacks.EtaleCohomology.smallEtaleSquarePushforwardIso_paste_app`.

Since the base change map of a square is the mate of the square identification, this is the
underived half of the pasting law of Stacks 0E47. -/
public theorem squarePushforwardIso_paste_app (𝓖 : Sheaf (smallEtaleTopology X₂) A) :
    (smallEtalePushforward g₀ A).map
          ((smallEtalePushforwardComp' v₂ v₁ v hv A).hom.app 𝓖) ≫
        (squarePushforwardIso g₂ g₀ u v d hdg hdv A).hom.app 𝓖 =
      (squarePushforwardIso g₁ g₀ u₁ v₁ d₁ hd₁g hd₁v A).hom.app
            ((smallEtalePushforward v₂ A).obj 𝓖) ≫
          (smallEtalePushforward u₁ A).map
              ((squarePushforwardIso g₂ g₁ u₂ v₂ d₂ hd₂g hd₂v A).hom.app 𝓖) ≫
            (smallEtalePushforwardComp' u₂ u₁ u hu A).hom.app
              ((smallEtalePushforward g₂ A).obj 𝓖) := by
  have hr := rectangle_diag_right g₂ u₁ u₂ u d₂ d hu hd₂g hdg
  have hl := rectangle_diag_left g₀ v₁ v₂ v d₁ d hv hd₁v hdv
  have hP₁ := smallEtalePushforwardComp'_assoc_app v₂ v₁ g₀ v hv d₁ hd₁v d hdv hl A 𝓖
  have hP₂ := smallEtalePushforwardComp'_assoc_app v₂ g₁ u₁ d₂ hd₂v d₁ hd₁g d hr hl A 𝓖
  have hP₃ := smallEtalePushforwardComp'_assoc_app g₂ u₂ u₁ d₂ hd₂g u hu d hr hdg A 𝓖
  simp only [squarePushforwardIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  refine pastingAlgebra ?_ ?_ ?_ hP₁ hP₂ hP₃
  · exact Iso.hom_inv_id_app _ _
  · exact Iso.inv_hom_id_app _ _
  · rw [← Functor.map_comp, Iso.inv_hom_id_app]
    exact CategoryTheory.Functor.map_id _ _

end Paste

/-! ### The comparison maps of Stacks 0EYM in degree zero, and their cocycle condition -/

section System

variable {I : Type v} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS)
  (A : Type w) [Category.{w'} A]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward DX A a).IsRightAdjoint]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward DS A a).IsRightAdjoint]

/-- The direct image `g_{i, *}ℱ_i` of the sheaf at a level along the morphism at that level. -/
public abbrev directImage (F : EtaleSheafSystem DX A) (i : Iᵒᵖ) :
    Sheaf (smallEtaleTopology (DS.obj i)) A :=
  (smallEtalePushforward (γ.app i) A).obj (F.obj i)

/-- The identification `f_{i'i, *} g_{i, *} ≅ g_{i', *} h_{i'i, *}` of the two composite direct
images around the transition square `g_{i'} ≫ h_{i'i} = f_{i'i} ≫ g_i` of a morphism of inverse
systems of schemes. -/
public def transitionSquareIso {i j : Iᵒᵖ} (a : i ⟶ j) :
    systemPushforward DX A a ⋙ smallEtalePushforward (γ.app j) A ≅
      smallEtalePushforward (γ.app i) A ⋙ systemPushforward DS A a :=
  squarePushforwardIso (γ.app i) (γ.app j) (DS.map a) (DX.map a) (γ.app i ≫ DS.map a) rfl
    (LimitHigherDirectImage.transition_comm γ a) A

/-- **The transition maps of Stacks 0EYM in degree zero**,
`ψ_{i'i} : h_{i'i}^{-1} g_{i, *}ℱ_i ⟶ g_{i', *}ℱ_{i'}`: the transpose of `g_{i, *}` of the
transposed transition map `ℱ_i ⟶ f_{i'i, *}ℱ_{i'}` of the system, followed by the identification
of the two composite direct images around the transition square.

Equivalently, and this is the source's description, it is the base change map of the transition
square on direct images followed by `g_{i', *}φ_{i'i}`: the base change map is the mate of the
square identification, and the transpose of a mate is the unit of the adjunction followed by that
identification. -/
public def transitionMap (F : EtaleSheafSystem DX A) {i j : Iᵒᵖ} (a : i ⟶ j) :
    (systemPullback DS A a).obj (directImage γ A F j) ⟶ directImage γ A F i :=
  ((systemAdjunction DS A a).homEquiv _ _).symm
    ((smallEtalePushforward (γ.app j) A).map (F.mapTranspose a) ≫
      (transitionSquareIso γ A a).hom.app (F.obj i))

/-- The transpose of the transition map is `g_{i, *}` of the transposed transition map of the
system followed by the square identification. This is the defining description of
`Stacks.EtaleCohomology.LimitDirectImage.transitionMap`, recorded in transposed form because that
is the form the cocycle condition is an identity of. -/
public theorem transitionMap_transpose (F : EtaleSheafSystem DX A) {i j : Iᵒᵖ} (a : i ⟶ j) :
    (systemAdjunction DS A a).homEquiv _ _ (transitionMap γ A F a) =
      (smallEtalePushforward (γ.app j) A).map (F.mapTranspose a) ≫
        (transitionSquareIso γ A a).hom.app (F.obj i) :=
  Equiv.apply_symm_apply _ _

omit [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward DX A a).IsRightAdjoint]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward DS A a).IsRightAdjoint] in
/-- **The pasting law for the transition squares of a morphism of inverse systems of schemes**:
the square identification of the composite transition is the composite of the identifications of
the two factors, read through the comparisons of the direct images along the composite
transitions. This is
`Stacks.EtaleCohomology.LimitDirectImage.squarePushforwardIso_paste_app` for the rectangle
obtained by stacking the transition square of `b` on that of `a`, whose outer rectangle is the
transition square of `a ≫ b`. -/
public theorem transitionSquareIso_paste_app {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k)
    (𝓖 : Sheaf (smallEtaleTopology (DX.obj i)) A) :
    (smallEtalePushforward (γ.app k) A).map
          ((smallEtalePushforwardComp' (DX.map a) (DX.map b) (DX.map (a ≫ b)) (DX.map_comp a b)
              A).hom.app 𝓖) ≫
        (transitionSquareIso γ A (a ≫ b)).hom.app 𝓖 =
      (transitionSquareIso γ A b).hom.app ((systemPushforward DX A a).obj 𝓖) ≫
        (systemPushforward DS A b).map ((transitionSquareIso γ A a).hom.app 𝓖) ≫
          (smallEtalePushforwardComp' (DS.map a) (DS.map b) (DS.map (a ≫ b)) (DS.map_comp a b)
              A).hom.app ((smallEtalePushforward (γ.app i) A).obj 𝓖) :=
  squarePushforwardIso_paste_app (γ.app k) (γ.app j) (γ.app i) (DS.map b) (DS.map a)
    (DX.map b) (DX.map a) (DS.map (a ≫ b)) (DX.map (a ≫ b)) (γ.app j ≫ DS.map b)
    (γ.app i ≫ DS.map a) (γ.app i ≫ DS.map (a ≫ b)) (DS.map_comp a b) (DX.map_comp a b) rfl
    (LimitHigherDirectImage.transition_comm γ b) rfl
    (LimitHigherDirectImage.transition_comm γ a) rfl
    (LimitHigherDirectImage.transition_comm γ (a ≫ b)) A 𝓖

omit [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward DS A a).IsRightAdjoint] in
/-- The cocycle identity satisfied by the transposed transition maps: the pasting law for the
transition squares combined with the transposed cocycle condition of the system of sheaves. -/
private theorem transpose_cocycle (F : EtaleSheafSystem DX A) {i j k : Iᵒᵖ} (a : i ⟶ j)
    (b : j ⟶ k) :
    ((smallEtalePushforward (γ.app k) A).map (F.mapTranspose b) ≫
          (transitionSquareIso γ A b).hom.app (F.obj j)) ≫
        (systemPushforward DS A b).map
            ((smallEtalePushforward (γ.app j) A).map (F.mapTranspose a) ≫
              (transitionSquareIso γ A a).hom.app (F.obj i)) ≫
          (smallEtalePushforwardComp' (DS.map a) (DS.map b) (DS.map (a ≫ b)) (DS.map_comp a b)
              A).hom.app ((smallEtalePushforward (γ.app i) A).obj (F.obj i)) =
      (smallEtalePushforward (γ.app k) A).map (F.mapTranspose (a ≫ b)) ≫
        (transitionSquareIso γ A (a ≫ b)).hom.app (F.obj i) := by
  have hnat := (transitionSquareIso γ A b).hom.naturality (F.mapTranspose a)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  rw [F.mapTranspose_comp a b]
  simp only [Functor.map_comp, Category.assoc]
  rw [transitionSquareIso_paste_app γ A a b (F.obj i), reassoc_of% hnat]

/-- **The direct images form a system of sheaves.** Let `(X_i, f_{i'i})` and `(S_i, h_{i'i})` be
inverse systems of schemes and `g_i : X_i ⟶ S_i` a morphism of systems, and let `(ℱ_i, φ_{i'i})`
be a system of sheaves on `(X_i, f_{i'i})`. The direct images `g_{i, *}ℱ_i` carry the maps
`ψ_{i'i} : h_{i'i}^{-1} g_{i, *}ℱ_i ⟶ g_{i', *}ℱ_{i'}` of the first paragraph of the proof of
Stacks 0EYM, and `(g_{i, *}ℱ_i, ψ_{i'i})` is a system of sheaves on `(S_i, h_{i'i})` in the sense
of Stacks 0EZL: the maps satisfy the cocycle condition
`ψ_{i''i} = ψ_{i''i'} ∘ h_{i''i'}^{-1}ψ_{i'i}`.

This is what makes `i ↦ h_i^{-1} g_{i, *}ℱ_i` a diagram, and hence what the colimit assertion
`g_* ℱ = colim_i h_i^{-1} g_{i, *}ℱ_i` of Stacks 0EYM presupposes. The assertion itself is not
proved; the coefficients are arbitrary and the direct image is the underived one, so the sheaves
of sets of the source are the instance `A = Type (max (u + 1) v)`. -/
public def transitionSystem (F : EtaleSheafSystem DX A) : EtaleSheafSystem DS A where
  obj i := directImage γ A F i
  map a := transitionMap γ A F a
  map_comp {i j k} a b := by
    refine (leftAdjointCompIso_inv_homEquiv_symm (systemAdjunction DS A b)
      (systemAdjunction DS A a) (systemAdjunction DS A (a ≫ b))
      (smallEtalePushforwardComp' (DS.map a) (DS.map b) (DS.map (a ≫ b)) (DS.map_comp a b) A)
      _ _).trans ?_
    exact congrArg ((systemAdjunction DS A (a ≫ b)).homEquiv _ _).symm
      (transpose_cocycle γ A F a b)

end System

/-! ### The cocone of Stacks 0EYM in degree zero -/

section Cocone

/-- **The inverse image of sheaves along a morphism of schemes**, as the left adjoint of the
direct image. This is `Stacks.EtaleCohomology.systemPullback` for an arbitrary morphism in place
of a transition of an inverse system, standing to it as
`Stacks.EtaleCohomology.smallEtalePushforward` stands to
`Stacks.EtaleCohomology.systemPushforward`.

Writing the two topologies in terms of the source and target of the morphism, rather than in
terms of a cone whose projections are the morphisms of interest, is what lets the continuity
instance be found: the source of a cone projection `c.π.app i` is `((const).obj c.pt).obj i`,
which is `c.pt` only after unfolding `CategoryTheory.Functor.const`, and instance unification does
not unfold it. -/
public abbrev etalePullback {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type w) [Category.{w'} A]
    [(smallEtalePushforward f A).IsRightAdjoint] :
    Sheaf (smallEtaleTopology Y) A ⥤ Sheaf (smallEtaleTopology X) A :=
  (smallEtaleBaseChange f).sheafPullback A (smallEtaleTopology Y) (smallEtaleTopology X)

/-- The inverse image along a morphism of schemes is left adjoint to the direct image. -/
public def etaleAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type w) [Category.{w'} A]
    [(smallEtalePushforward f A).IsRightAdjoint] :
    etalePullback f A ⊣ smallEtalePushforward f A :=
  Functor.sheafAdjunctionContinuous (smallEtaleBaseChange f) A (smallEtaleTopology Y)
    (smallEtaleTopology X)

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} (A : Type w) [Category.{w'} A]
  (c : Cone D) [∀ i : Iᵒᵖ, (smallEtalePushforward (c.π.app i) A).IsRightAdjoint]

/-- The comparison `f_{i, *} f_{i'i, *} ≅ f_{i', *}` of direct images coming from the
factorisation `f_{i'} = f_{i'} ≫ f_{i'i}` of a projection of a cone through a transition. This is
`Stacks.EtaleCohomology.coneDirectImageComp` with the composite carried as a named morphism, in
the form the pasting law consumes. -/
public abbrev coneProjectionComp {i j : Iᵒᵖ} (a : i ⟶ j) :
    smallEtalePushforward (c.π.app i) A ⋙ systemPushforward D A a ≅
      smallEtalePushforward (c.π.app j) A :=
  smallEtalePushforwardComp' (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm A

variable {𝓕 : Sheaf (smallEtaleTopology c.pt) A}

/-- **The presentation map of a colimit, transposed.** A map `f_i^{-1}𝓖_i ⟶ 𝓕` corresponds, under
the inverse-image/direct-image adjunction along the projection `f_i`, to a map
`𝓖_i ⟶ f_{i, *}𝓕`. -/
public def coneTranspose {G : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) A}
    (ι : ∀ i : Iᵒᵖ, (etalePullback (c.π.app i) A).obj (G i) ⟶ 𝓕) (i : Iᵒᵖ) :
    G i ⟶ (smallEtalePushforward (c.π.app i) A).obj 𝓕 :=
  (etaleAdjunction (c.π.app i) A).homEquiv _ _ (ι i)

/-- The transpose of the transposed presentation map is the presentation map itself. -/
public theorem homEquiv_symm_coneTranspose
    {G : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) A}
    (ι : ∀ i : Iᵒᵖ, (etalePullback (c.π.app i) A).obj (G i) ⟶ 𝓕) (i : Iᵒᵖ) :
    ((etaleAdjunction (c.π.app i) A).homEquiv (G i) 𝓕).symm (coneTranspose A c ι i) = ι i :=
  Equiv.symm_apply_apply _ _

variable [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).IsRightAdjoint]

/-- **The compatibility of a colimit presentation with the transition maps, transposed.** If the
maps `ι_i : f_i^{-1}ℱ_i ⟶ 𝓕` are compatible with the transition maps of the system, then their
transposes satisfy the corresponding identity through the comparison of the direct images along
the two factors of a projection. -/
public theorem coneTranspose_comp (F : EtaleSheafSystem D A)
    (ι : ∀ i : Iᵒᵖ, (etalePullback (c.π.app i) A).obj (F.obj i) ⟶ 𝓕)
    (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (Adjunction.leftAdjointCompIso (systemAdjunction D A a) (etaleAdjunction (c.π.app i) A)
            (etaleAdjunction (c.π.app j) A) (coneProjectionComp A c a)).inv.app (F.obj j) ≫
          (etalePullback (c.π.app i) A).map (F.map a) ≫ ι i = ι j)
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    coneTranspose A c ι j =
      F.mapTranspose a ≫ (systemPushforward D A a).map (coneTranspose A c ι i) ≫
        (coneProjectionComp A c a).hom.app 𝓕 := by
  exact (leftAdjointCompIso_inv_comp_iff (systemAdjunction D A a)
    (etaleAdjunction (c.π.app i) A) (etaleAdjunction (c.π.app j) A) (coneProjectionComp A c a)
    (F.map a) (ι i) _).1 (hι a)

end Cocone

section CoconeMaps

variable {I : Type v} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS)
  (A : Type w) [Category.{w'} A]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward DX A a).IsRightAdjoint]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward DS A a).IsRightAdjoint]
  (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS)
  [∀ i : Iᵒᵖ, (smallEtalePushforward (cX.π.app i) A).IsRightAdjoint]
  [∀ i : Iᵒᵖ, (smallEtalePushforward (cS.π.app i) A).IsRightAdjoint]

/-- The identification `f_{i, *} g_{i, *} ≅ g_* h_{i, *}` of the two composite direct images
around the projection square `g ≫ h_i = f_i ≫ g_i` of the limit morphism. -/
public def projectionSquareIso (i : Iᵒᵖ) :
    smallEtalePushforward (cX.π.app i) A ⋙ smallEtalePushforward (γ.app i) A ≅
      smallEtalePushforward (LimitHigherDirectImage.limitMorphism γ cX cS hcS) A ⋙
        smallEtalePushforward (cS.π.app i) A :=
  squarePushforwardIso (LimitHigherDirectImage.limitMorphism γ cX cS hcS) (γ.app i)
    (cS.π.app i) (cX.π.app i)
    (LimitHigherDirectImage.limitMorphism γ cX cS hcS ≫ cS.π.app i) rfl
    (LimitHigherDirectImage.limitMorphism_comp_π γ cX cS hcS i) A

omit [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward DX A a).IsRightAdjoint]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward DS A a).IsRightAdjoint]
  [∀ i : Iᵒᵖ, (smallEtalePushforward (cX.π.app i) A).IsRightAdjoint]
  [∀ i : Iᵒᵖ, (smallEtalePushforward (cS.π.app i) A).IsRightAdjoint] in
/-- **The pasting law for the projection square stacked on a transition square**: the outer
rectangle of the projection square at `i'` and the transition square from `i'` to `i` is the
projection square at `i`, because `f_i = f_{i'} ≫ f_{i'i}` and `h_i = h_{i'} ≫ h_{i'i}`. -/
public theorem projectionSquareIso_paste_app {i j : Iᵒᵖ} (a : i ⟶ j)
    (𝓖 : Sheaf (smallEtaleTopology cX.pt) A) :
    (smallEtalePushforward (γ.app j) A).map ((coneProjectionComp A cX a).hom.app 𝓖) ≫
        (projectionSquareIso γ A cX cS hcS j).hom.app 𝓖 =
      (transitionSquareIso γ A a).hom.app ((smallEtalePushforward (cX.π.app i) A).obj 𝓖) ≫
        (systemPushforward DS A a).map ((projectionSquareIso γ A cX cS hcS i).hom.app 𝓖) ≫
          (coneProjectionComp A cS a).hom.app
            ((smallEtalePushforward
              (LimitHigherDirectImage.limitMorphism γ cX cS hcS) A).obj 𝓖) :=
  squarePushforwardIso_paste_app (γ.app j) (γ.app i)
    (LimitHigherDirectImage.limitMorphism γ cX cS hcS) (DS.map a) (cS.π.app i) (DX.map a)
    (cX.π.app i) (cS.π.app j) (cX.π.app j) (γ.app i ≫ DS.map a)
    (LimitHigherDirectImage.limitMorphism γ cX cS hcS ≫ cS.π.app i)
    (LimitHigherDirectImage.limitMorphism γ cX cS hcS ≫ cS.π.app j)
    (cS.w a).symm (cX.w a).symm rfl (LimitHigherDirectImage.transition_comm γ a) rfl
    (LimitHigherDirectImage.limitMorphism_comp_π γ cX cS hcS i) rfl
    (LimitHigherDirectImage.limitMorphism_comp_π γ cX cS hcS j) A 𝓖

variable {𝓕 : Sheaf (smallEtaleTopology cX.pt) A} (F : EtaleSheafSystem DX A)
  (ι : ∀ i : Iᵒᵖ, (etalePullback (cX.π.app i) A).obj (F.obj i) ⟶ 𝓕)

/-- **The cocone maps of Stacks 0EYM in degree zero**,
`ψ_i : h_i^{-1} g_{i, *}ℱ_i ⟶ g_* ℱ`: the transpose of `g_{i, *}` of the transposed presentation
map `ℱ_i ⟶ f_{i, *}ℱ` of the colimit, followed by the identification of the two composite direct
images around the projection square.

Equivalently, and this is the source's description, it is the base change map of the projection
square on direct images followed by `g_*ι_i`. -/
public def projectionMap (i : Iᵒᵖ) :
    (etalePullback (cS.π.app i) A).obj (directImage γ A F i) ⟶
      (smallEtalePushforward (LimitHigherDirectImage.limitMorphism γ cX cS hcS) A).obj 𝓕 :=
  ((etaleAdjunction (cS.π.app i) A).homEquiv _ _).symm
    ((smallEtalePushforward (γ.app i) A).map (coneTranspose A cX ι i) ≫
      (projectionSquareIso γ A cX cS hcS i).hom.app 𝓕)

/-- **The cocone maps are compatible with the transition maps.** Let `(ℱ_i, φ_{i'i})` be a system
of sheaves on `(X_i, f_{i'i})` and let the maps `ι_i : f_i^{-1}ℱ_i ⟶ ℱ` present `ℱ` compatibly
with the transitions. Then the maps `ψ_i` of Stacks 0EYM satisfy
`ψ_{i'} ∘ h_{i'}^{-1}ψ_{i'i} = ψ_i`, so they form a cocone, over the system
`Stacks.EtaleCohomology.LimitDirectImage.transitionSystem`, with vertex `g_* ℱ`.

Together with that system this is the whole first paragraph of the source's proof in degree zero.
What remains of the colimit assertion `g_* ℱ = colim_i h_i^{-1} g_{i, *}ℱ_i` is that this cocone
is a *colimiting* one; the module note lists the three inputs that still needs. -/
public theorem projectionMap_comp
    (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (Adjunction.leftAdjointCompIso (systemAdjunction DX A a) (etaleAdjunction (cX.π.app i) A)
            (etaleAdjunction (cX.π.app j) A) (coneProjectionComp A cX a)).inv.app (F.obj j) ≫
          (etalePullback (cX.π.app i) A).map (F.map a) ≫ ι i = ι j)
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    (Adjunction.leftAdjointCompIso (systemAdjunction DS A a) (etaleAdjunction (cS.π.app i) A)
          (etaleAdjunction (cS.π.app j) A) (coneProjectionComp A cS a)).inv.app
            (directImage γ A F j) ≫
        (etalePullback (cS.π.app i) A).map (transitionMap γ A F a) ≫
          projectionMap γ A cX cS hcS F ι i =
      projectionMap γ A cX cS hcS F ι j := by
  refine (leftAdjointCompIso_inv_homEquiv_symm (systemAdjunction DS A a)
    (etaleAdjunction (cS.π.app i) A) (etaleAdjunction (cS.π.app j) A)
    (coneProjectionComp A cS a) _ _).trans ?_
  refine congrArg ((etaleAdjunction (cS.π.app j) A).homEquiv _ _).symm ?_
  have hnat := (transitionSquareIso γ A a).hom.naturality (coneTranspose A cX ι i)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  rw [coneTranspose_comp A cX F ι hι a]
  simp only [Functor.map_comp, Category.assoc]
  rw [projectionSquareIso_paste_app γ A cX cS hcS a 𝓕, reassoc_of% hnat]

end CoconeMaps

/-! ### The case of sheaves of sets -/

section Sets

/-- The direct image of sheaves of sets along a transition morphism of an inverse system of
schemes has a left adjoint. Stated for one transition at a time: the instance search for the
quantified family `∀ i j (a : i ⟶ j), _` that the systems of sheaves of sets take does not find
it from the instances for single morphisms alone. -/
public instance systemPushforward_isRightAdjoint_type {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) {i j : Iᵒᵖ} (a : i ⟶ j) :
    (systemPushforward D (Type (max (u + 1) v)) a).IsRightAdjoint :=
  inferInstance

variable {I : Type v} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS)

/-- **The direct images of a system of sheaves of sets form a system of sheaves of sets**, with
the transition maps `ψ_{i'i}` of the first paragraph of the proof of Stacks 0EYM.

This is `Stacks.EtaleCohomology.LimitDirectImage.transitionSystem` at the coefficients
`Type (max (u + 1) v)` of `Stacks.EtaleCohomology.smallEtaleDirectImage`, where the
inverse-image/direct-image adjunctions the construction transposes across are available
unconditionally: inverse image of sheaves of sets on a small étale site is a left Kan extension
along base change followed by sheafification. -/
public abbrev setTransitionSystem (F : EtaleSheafSystem DX (Type (max (u + 1) v))) :
    EtaleSheafSystem DS (Type (max (u + 1) v)) :=
  transitionSystem γ (Type (max (u + 1) v)) F

end Sets

end LimitDirectImage

end Stacks.EtaleCohomology

end
