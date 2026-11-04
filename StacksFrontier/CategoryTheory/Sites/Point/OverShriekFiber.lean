module

public import Mathlib.CategoryTheory.Sites.Point.Over
public import StacksFrontier.CategoryTheory.Sites.Localization.LowerShriekCoproductSheaf
public import StacksFrontier.CategoryTheory.Sites.Localization.LowerShriekCoproducts

/-! # The stalk of `j_{U!}G` at a point: a coproduct over the points above it

Let `(C, J)` be a site, let `p` be a point of `C` with fibre functor `u = p.fiber`, and let `U` be
an object of `C`.  Stacks 04H4 computes the stalk at `p` of the extension by zero
`j_{U!}G` of a sheaf `G` on the localized site `C/U`:
```
  (j_{U!}G)_p = ∐_q G_q ,
```
the coproduct being over the points `q = q_x` of `C/U` above `p`, one for each `x ∈ u(U)`, as
constructed in Stacks 04H2 (Mathlib's `GrothendieckTopology.Point.over`).

The proof is the one Stacks gives.  By Stacks 03CD the sheaf `j_{U!}G` is the sheafification of
the presheaf
```
  V ↦ ∐_{φ ∈ Mor_C(V, U)} G(V →φ U) ,
```
which is `CategoryTheory.OverShriek.presheaf` of
`StacksFrontier/CategoryTheory/Sites/Localization/LowerShriekCoproducts.lean`, and by
Stacks 00Y8 the stalk of a sheaf at `p` is the stalk of any presheaf whose sheafification it is —
here Mathlib's `Point.presheafToSheafCompSheafFiberIso`.  So the stalk is the filtered colimit
```
  colim_{(V, y)} ∐_{φ : V ⟶ U} G(V →φ U) ,
```
and one assigns to a class of `(V, y, φ, s)` the element `x = u(φ)(y)` of `u(U)`; this splits the
colimit as `∐_{x ∈ u(U)} colim_{(φ : V ⟶ U, y), u(φ)(y) = x} G(V →φ U)`, and the inner colimit is
by construction the stalk of `G` at the point `q_x = p.over x`.

The splitting is carried out below elementwise, in the two directions Stacks describes: for a
fixed `x`, `sigmaToPresheafFiber` sends the class of `(V →φ U, y, s)` in `G_{q_x}` to the class of
`(V, y, φ, s)`; `presheafFiberIndex` is Stacks' assignment `(V, y, φ, s) ↦ u(φ)(y)`, which shows
the pieces are disjoint; and each piece is injective by the filtered-colimit criterion, the
descent datum for `G_{q_x}` being manufactured from the one for the big colimit.

## Main results

* `CategoryTheory.OverShriek.sigmaToPresheafFiber`: the map `G_{q_x} ⟶ (∐-presheaf)_p`.
* `CategoryTheory.OverShriek.presheafFiberIndex`: the map `(∐-presheaf)_p ⟶ u(U)` sending the
  class of `(V, y, φ, s)` to `u(φ)(y)`.
* `CategoryTheory.OverShriek.presheafFiberSigmaEquiv`: the presheaf-level statement,
  `∐_{x ∈ u(U)} G_{q_x} ≃ (∐-presheaf)_p`.
* `CategoryTheory.OverShriek.sheafFiberSigmaEquiv` (Stacks 04H4): the statement itself,
  `∐_{x ∈ u(U)} G_{q_x} ≃ (j_{U!}G)_p`, for a sheaf `G` on `C/U`.

The coproduct is realized as the sigma type, which is the coproduct in `Type v`; the index set
`u(U)` is the one Stacks uses, and it is in bijection with the set of points of `C/U` above `p` by
Stacks 04H3 (see `StacksFrontier/CategoryTheory/Sites/Point/OverBijection.lean`).

Tags covered: 04H4.
-/

@[expose] public section

open CategoryTheory Opposite Limits GrothendieckTopology
universe v u

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{v} C]
  (Φ : Point.{v} J) {U : C} (G : (Over U)ᵒᵖ ⥤ Type v)

/-- The map `G_{q_x} ⟶ (∐_{φ : V ⟶ U} G(V →φ U))_p` of Stacks 04H4: the class of a section `s`
of `G` over `V →φ U` at a point `y` of the fibre of `q_x` at `V →φ U` — so `y ∈ u(V)` with
`u(φ)(y) = x` — is sent to the class of `(φ, s)` at `y ∈ u(V)`.

Well-definedness is the compatibility of these assignments with restriction, which is
`OverShriek.sigmaMk_eq`: restricting `(φ, s)` along `g : W ⟶ V` over `U` gives `(g ≫ φ, s|_W)`. -/
noncomputable def sigmaToPresheafFiber (x : Φ.fiber.obj U) :
    (Φ.over x).presheafFiber.obj G ⟶ Φ.presheafFiber.obj (presheaf G) :=
  (Φ.over x).presheafFiberDesc
    (fun W w => ↾fun s => Φ.toPresheafFiber W.left w.1 (presheaf G) ⟨W.hom, s⟩)
    (by
      intro W W' g w
      obtain ⟨V, ψ, rfl⟩ := Over.mk_surjective W
      obtain ⟨V', ψ', rfl⟩ := Over.mk_surjective W'
      ext s
      change
        Φ.toPresheafFiber V w.1 (presheaf G) ⟨ψ, G.map g.op s⟩ =
          Φ.toPresheafFiber V' (Φ.fiber.map g.left w.1) (presheaf G) ⟨ψ', s⟩
      have key :
        (⟨g.left ≫ ψ', G.map (Over.homMk g.left rfl : Over.mk (g.left ≫ ψ') ⟶ Over.mk ψ').op s⟩ :
            Σ φ : V ⟶ U, G.obj (op (Over.mk φ))) =
          ⟨ψ, G.map g.op s⟩ :=
        sigmaMk_eq G s (Over.homMk g.left rfl : Over.mk (g.left ≫ ψ') ⟶ Over.mk ψ') g rfl
      rw [← key]
      exact Φ.toPresheafFiber_w_apply g.left w.1 (presheaf G) ⟨ψ', s⟩)

/-- The index map `(∐_{φ : V ⟶ U} G(V →φ U))_p ⟶ u(U)` of Stacks 04H4: "to each element
`(V, y, φ, s)` of this colimit, we can assign `x = u(φ)(y) ∈ u(U)`".  It is well defined because
`u(g ≫ φ)(y) = u(φ)(u(g)(y))`. -/
noncomputable def presheafFiberIndex : Φ.presheafFiber.obj (presheaf G) ⟶ Φ.fiber.obj U :=
  Φ.presheafFiberDesc (fun _ y => ↾fun p => Φ.fiber.map p.1 y)
    (by
      intro V V' f y
      ext p
      obtain ⟨ψ', s⟩ := p
      simp [presheaf])

/-- The defining formula for `sigmaToPresheafFiber`. -/
lemma sigmaToPresheafFiber_apply (x : Φ.fiber.obj U) (W : Over U) (w : (Φ.over x).fiber.obj W)
    (s : G.obj (op W)) :
    sigmaToPresheafFiber Φ G x ((Φ.over x).toPresheafFiber W w G s) =
      Φ.toPresheafFiber W.left w.1 (presheaf G) ⟨W.hom, s⟩ := by
  unfold sigmaToPresheafFiber
  exact
    ConcreteCategory.congr_hom ((Φ.over x).toPresheafFiber_presheafFiberDesc (P := G) _ _ W w) s

omit [LocallySmall.{v} C] in
/-- The defining formula for `presheafFiberIndex`. -/
lemma presheafFiberIndex_apply (V : C) (y : Φ.fiber.obj V) (p : (presheaf G).obj (op V)) :
    presheafFiberIndex Φ G (Φ.toPresheafFiber V y (presheaf G) p) = Φ.fiber.map p.1 y := by
  unfold presheafFiberIndex
  exact
    ConcreteCategory.congr_hom (Φ.toPresheafFiber_presheafFiberDesc (P := presheaf G) _ _ V y) p

/-- The piece of the colimit coming from `x` has index `x`: this is what makes the decomposition
of Stacks 04H4 a decomposition into disjoint pieces. -/
lemma presheafFiberIndex_sigmaToPresheafFiber (x : Φ.fiber.obj U)
    (t : (Φ.over x).presheafFiber.obj G) :
    presheafFiberIndex Φ G (sigmaToPresheafFiber Φ G x t) = x := by
  obtain ⟨W, w, s, rfl⟩ := (Φ.over x).toPresheafFiber_jointly_surjective (P := G) t
  rw [sigmaToPresheafFiber_apply]
  exact
    (presheafFiberIndex_apply Φ G W.left w.1 ⟨W.hom, s⟩).trans
      ((FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).1 w.2)

set_option backward.isDefEq.respectTransparency false in
/-- Each piece `G_{q_x} ⟶ (∐-presheaf)_p` is injective.  Both sides are filtered colimits of
sets, and a descent datum witnessing an equality in the big colimit — a morphism `f : V' ⟶ V` and
a point `y'` of the fibre at `V'` over `y` along which the two sections agree — is turned into one
for `G_{q_x}` by taking the object `V' → V → U` of `C/U` and the point `y'`, which lies over `x`
because `y` does. -/
lemma sigmaToPresheafFiber_injective (x : Φ.fiber.obj U) :
    Function.Injective (fun t => sigmaToPresheafFiber Φ G x t) := by
  intro t₁ t₂ h
  obtain ⟨W, w, s₁, s₂, rfl, rfl⟩ := (Φ.over x).toPresheafFiber_jointly_surjective₂ (P := G) t₁ t₂
  obtain ⟨V, ψ, rfl⟩ := Over.mk_surjective W
  simp only [sigmaToPresheafFiber_apply] at h
  rw [Φ.toPresheafFiber_eq_iff'] at h
  obtain ⟨V', f, y', hy', hs⟩ := h
  rw [(Φ.over x).toPresheafFiber_eq_iff']
  refine ⟨Over.mk (f ≫ ψ), Over.homMk f rfl, ⟨y', ?_⟩, ?_, sigma_snd_inj hs⟩
  · refine (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).2 ?_
    dsimp only [Over.mk_hom, Over.mk_left] at hy' ⊢
    rw [Functor.map_comp_apply, hy']
    exact (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).1 w.2
  · exact Subtype.ext hy'

/-- **Stacks 04H4 at the level of presheaves.**  The stalk at `p` of the coproduct presheaf
`V ↦ ∐_{φ : V ⟶ U} G(V →φ U)` is the coproduct `∐_{x ∈ u(U)} G_{q_x}` of the stalks of `G` at
the points `q_x` of `C/U` above `p`.

The map is `sigmaToPresheafFiber` on each piece; the pieces are pairwise disjoint because
`presheafFiberIndex` recovers `x`, injective on each piece by
`sigmaToPresheafFiber_injective`, and jointly surjective because every class in the colimit is
represented by some `(V, y, φ, s)`. -/
noncomputable def presheafFiberSigmaEquiv :
    (Σ x : Φ.fiber.obj U, (Φ.over x).presheafFiber.obj G) ≃ Φ.presheafFiber.obj (presheaf G) :=
  Equiv.ofBijective (fun q => sigmaToPresheafFiber Φ G q.1 q.2)
    ⟨by
      rintro ⟨x₁, t₁⟩ ⟨x₂, t₂⟩ h
      obtain rfl : x₁ = x₂ := by
        rw [← presheafFiberIndex_sigmaToPresheafFiber Φ G x₁ t₁, ←
          presheafFiberIndex_sigmaToPresheafFiber Φ G x₂ t₂]
        exact congrArg _ h
      exact congrArg _ (sigmaToPresheafFiber_injective Φ G x₁ h), by
      intro p
      obtain ⟨V, y, ⟨ψ, s⟩, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := presheaf G) p
      refine
        ⟨⟨Φ.fiber.map ψ y,
            (Φ.over (Φ.fiber.map ψ y)).toPresheafFiber (Over.mk ψ)
              ⟨y, (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).2 rfl⟩ G s⟩,
          ?_⟩
      exact sigmaToPresheafFiber_apply Φ G _ (Over.mk ψ) _ s⟩

noncomputable section

variable (J)
variable [HasWeakSheafify J (Type v)] [HasSheafify (J.over U) (Type v)]
  [((Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J).IsRightAdjoint]

/-- **Stacks 04H4.** Let `C` be a site, `p` a point of `C` given by `u : C ⥤ Set`, and `U` an
object of `C`.  For any sheaf `F` on `C/U`,
```
  (j_{U!}F)_p = ∐_x F_{q_x} ,
```
the coproduct being over the points `q_x` of `C/U` attached to the elements `x` of `u(U)` as in
Stacks 04H2.

Here `j_{U!}` is `(Over.forget U).sheafPullback`, the left adjoint of the restriction
`j_U⁻¹ = GrothendieckTopology.overPullback`, and the coproduct is the sigma type, which is the
coproduct in `Type v`.  The proof combines the presheaf-level statement
`presheafFiberSigmaEquiv` with Stacks 03CD (`OverShriek.sheafifyIso`: `j_{U!}` of a sheafification
is the sheafification of the coproduct presheaf) and Stacks 00Y8 (`Point.presheafFiber` and
`Point.sheafFiber` agree across sheafification). -/
@[stacks 04H4]
def sheafFiberSigmaEquiv (F : Sheaf (J.over U) (Type v)) :
    (Σ x : Φ.fiber.obj U, (Φ.over x).sheafFiber.obj F) ≃
      Φ.sheafFiber.obj (((Over.forget U).sheafPullback (Type v) (J.over U) J).obj F) :=
  (Equiv.sigmaCongrRight fun x =>
        (((Φ.over x).sheafToPresheafCompPresheafFiberIso (A := Type v)).app F).toEquiv.symm).trans
    ((presheafFiberSigmaEquiv Φ F.obj).trans
      ((((Φ.presheafToSheafCompSheafFiberIso (Type v)).app (presheaf F.obj)).symm ≪≫
          Φ.sheafFiber.mapIso
            ((sheafifyIso F.obj J).symm ≪≫
              ((Over.forget U).sheafPullback (Type v) (J.over U) J).mapIso
                (asIso ((sheafificationAdjunction (J.over U) (Type v)).counit.app F)))).toEquiv))

end

end CategoryTheory.OverShriek
