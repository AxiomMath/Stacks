module

public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumUnitCoassoc

/-!
# The cocycle diagram of step 4 of Stacks 0APK, produced from the descent datum

`AlgebraicGeometry.DescentDatum.isEffective_of_cocycleDiagram_of_legs_of_restrictOpen` reduces
the coassociativity obligation `hkey` of step 4 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) to a *cocycle diagram* of rings:
a pushout square presenting a ring `Q₃` as `Γ(X, ⊤) ⊗_{Γ(S, ⊤)} Γ(X ×_S E, 𝒪)`, two morphisms
`Λ, Λ' : Γ(X ×_S E, 𝒪) ⟶ Q₃` pinned down on the two legs of that square, and one equation
between their composites with the coaction.  The pushout square is proved there as
`AlgebraicGeometry.DescentDatum.isPushout_algebraMap_transitionTargetBaseChange`; this file
supplies the rest, so that the obligation is discharged outright.

Geometrically the two morphisms are restriction along the two maps

```
(x₁, v, x₂) ↦ (x₂, x₁ · v)        (x₁, v, x₂) ↦ (x₂, v)
```

of `(X ×_S V) ×_S X` to `X ×_S V`, and the equation they must satisfy after composing with the
coaction `(x, v) ↦ x · v` is `x₂ · (x₁ · v) = x₂ · v`, which is the cocycle condition of the
descent datum read on the triple fibre product.  So the whole content of the obligation is the
cocycle condition, and that is proved, on generalized points, as
`AlgebraicGeometry.DescentDatum.act_act`.  Transporting it from the binary products of
`CategoryTheory.Over S`, where the gluing isomorphism is stated, to the literal fibre products,
where the rings of functions live, is what this file does.

## Main results

* `AlgebraicGeometry.DescentDatum.act_left_eq_pullbackLift` : **the bridge.**  The action of a
  descent datum on generalized points, read on the underlying schemes, is
  `CategoryTheory.Limits.pullback.lift` of the two points followed by the gluing isomorphism and
  the projection to `V`.
* `AlgebraicGeometry.DescentDatum.act_act_pullbackLift` : **the cocycle condition on the literal
  fibre products.**  This is `AlgebraicGeometry.DescentDatum.act_act` through the bridge.
* `AlgebraicGeometry.DescentDatum.comp_transitionPullbackIso_inv_comp_pullbackFst` : the coaction
  `(x, v) ↦ x · v`, which is `φ⁻¹` followed by the projection to `V`, expressed through the
  action of the previous two results.
* `AlgebraicGeometry.DescentDatum.exists_transitionTriple_restrictions` : **the geometric heart.**
  The two maps `(x₁, v, x₂) ↦ (x₂, x₁ · v)` and `(x₁, v, x₂) ↦ (x₂, v)` exist, are pinned down by
  their two components, and become equal after composing with the coaction.  No hypothesis beyond
  the descent datum itself.
* `AlgebraicGeometry.DescentDatum.exists_cocycleDiagram_descentAlgebraTransition` : **the cocycle
  diagram of step 4, produced.**  This is exactly the hypothesis `hcocycle` of
  `AlgebraicGeometry.DescentDatum.isEffective_of_cocycleDiagram_of_legs_of_restrictOpen`, now a
  theorem.
* `AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen` : **the residue of
  Stacks 0APK over an affine base with the coassociativity obligation gone.**  Three hypotheses
  remain, `hlegs`, `hrestrict` and `hglueing`, unchanged character for character.

## Implementation notes

*Why the morphisms are produced existentially.* `Λ` and `Λ'` are restriction along the two maps
above, and those maps are `CategoryTheory.Limits.pullback.lift` terms whose third argument is a
proof.  Naming them with `def`s would add two definitions whose only content is a pair of
projections, and `rw` cannot cross the proof argument when the two components are rewritten
(the motive is not type correct, because the proof depends on them).  So
`AlgebraicGeometry.DescentDatum.exists_transitionTriple_restrictions` exhibits the two maps
together with the equations that characterize them, and everything downstream uses only those
equations.  The same device makes the five equations of the diagram pure functoriality of
`AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap`.

*Why the bridge takes its two components as hypotheses.*
`AlgebraicGeometry.DescentDatum.act_left_eq_pullbackLift` and
`AlgebraicGeometry.DescentDatum.comp_transitionPullbackIso_inv_comp_pullbackFst` are stated with
`hv : v.left = α` rather than with `α` inlined, for the same reason: the caller substitutes, so
no `rw` ever has to pass through the proof argument of a `pullback.lift`.

*The two containments.* `AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap` asks that the source
subset be contained in the preimage of the target subset.  For `(x₁, v, x₂) ↦ (x₂, v)` that is an
identity; for `(x₁, v, x₂) ↦ (x₂, x₁ · v)` it is exactly the hypothesis `h₂` of
`AlgebraicGeometry.DescentDatum.transitionSectionsIso`, that `X ×_S E` lands in `E ×_S X` under
`φ⁻¹`.  No new invariance hypothesis is introduced.

*No tag.* `AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen` is still a
reduction, not Stacks 0APK: it carries three hypotheses no declaration of this repository
discharges, and the statement of Tag 0APK is for arbitrary fpqc covering families while this is
the affine single-morphism case.

## References

* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.DescentDatum

section Action

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f)

/-- **The action of a descent datum, read on the literal fibre products.**  Let `D` be a descent
datum relative to `f : X ⟶ S`, let `T` be a scheme over `S`, and let `v` and `x` be generalized
points of `V` and of `X` over `T`, whose underlying morphisms of schemes are `α` and `β`.  Then
the underlying morphism of the point `v · x` is `α` and `β` assembled into a point of `V ×_S X`,
followed by the gluing isomorphism and the projection of `X ×_S V` to `V`.

The products of `AlgebraicGeometry.DescentDatum.act` are binary products in
`CategoryTheory.Over S`, while the rings of functions of step 4 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) live on the literal fibre products;
this is the transport between them, by `CategoryTheory.Over.prodLeftIsoPullback` at both ends.
The two components `α` and `β` are taken as hypotheses so that a caller may substitute them
without rewriting under the proof argument of `CategoryTheory.Limits.pullback.lift`. -/
theorem act_left_eq_pullbackLift {T : Over S} (v : T ⟶ (Over.map f).obj D.over)
    (x : T ⟶ Over.mk f) {α : T.left ⟶ D.over.left} {β : T.left ⟶ X}
    (hv : v.left = α) (hx : x.left = β) (h : α ≫ (D.over.hom ≫ f) = β ≫ f) :
    (D.act v x).left =
      pullback.lift α β h ≫ D.transitionPullbackIso.hom ≫
        pullback.snd f (D.over.hom ≫ f) := by
  subst hv
  subst hx
  have hΦ : D.transitionPullbackIso.hom =
      (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).inv ≫
        D.transition.hom.left.left ≫
          (Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj D.over)).hom := rfl
  have hsnd : (Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj D.over)).hom ≫
      pullback.snd f (D.over.hom ≫ f) =
      (prod.snd : Over.mk f ⨯ (Over.map f).obj D.over ⟶ _).left :=
    Over.prodLeftIsoPullback_hom_snd _ _
  have hlift : (prod.lift v x).left ≫
      (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).hom =
      pullback.lift v.left x.left h := by
    have hfst := Over.prodLeftIsoPullback_hom_fst ((Over.map f).obj D.over) (Over.mk f)
    have hsnd0 := Over.prodLeftIsoPullback_hom_snd ((Over.map f).obj D.over) (Over.mk f)
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hfst, ← Over.comp_left, prod.lift_fst]
      exact (pullback.lift_fst v.left x.left h).symm
    · rw [Category.assoc, hsnd0, ← Over.comp_left, prod.lift_snd]
      exact (pullback.lift_snd v.left x.left h).symm
  rw [hΦ, ← hlift, act, gluingAction, Over.comp_left, Over.comp_left,
    Category.assoc, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, hsnd]

/-- **The cocycle condition of a descent datum on the literal fibre products.**  For a point `α`
of `V` and two points `β`, `γ` of `X` over a common scheme `T`, acting by `β` and then by `γ` is
acting by `γ`:
```
(α · β) · γ = α · γ,
```
with the action written out as `CategoryTheory.Limits.pullback.lift` followed by the gluing
isomorphism and the projection to `V`.

This is `AlgebraicGeometry.DescentDatum.act_act` through
`AlgebraicGeometry.DescentDatum.act_left_eq_pullbackLift`, and it is the only input of this file
which is not formal: it is the cocycle condition itself. -/
theorem act_act_pullbackLift {T : Scheme.{u}} (α : T ⟶ D.over.left) (β γ : T ⟶ X)
    (hβ : α ≫ (D.over.hom ≫ f) = β ≫ f) (hγ : α ≫ (D.over.hom ≫ f) = γ ≫ f)
    (hα' : (pullback.lift α β hβ ≫ D.transitionPullbackIso.hom ≫
        pullback.snd f (D.over.hom ≫ f)) ≫ (D.over.hom ≫ f) = γ ≫ f) :
    pullback.lift (pullback.lift α β hβ ≫ D.transitionPullbackIso.hom ≫
          pullback.snd f (D.over.hom ≫ f)) γ hα' ≫
        D.transitionPullbackIso.hom ≫ pullback.snd f (D.over.hom ≫ f) =
      pullback.lift α γ hγ ≫ D.transitionPullbackIso.hom ≫
        pullback.snd f (D.over.hom ≫ f) := by
  have hγβ : γ ≫ f = β ≫ f := hγ.symm.trans hβ
  have key := congrArg Over.Hom.left (D.act_act
    (Over.homMk α hβ : (Over.mk (β ≫ f) : Over S) ⟶ (Over.map f).obj D.over)
    (Over.homMk β rfl : (Over.mk (β ≫ f) : Over S) ⟶ Over.mk f)
    (Over.homMk γ hγβ : (Over.mk (β ≫ f) : Over S) ⟶ Over.mk f))
  have hinner := D.act_left_eq_pullbackLift (T := Over.mk (β ≫ f))
    (Over.homMk α hβ : (Over.mk (β ≫ f) : Over S) ⟶ (Over.map f).obj D.over)
    (Over.homMk β rfl : (Over.mk (β ≫ f) : Over S) ⟶ Over.mk f)
    (α := α) (β := β) rfl rfl hβ
  have houter := D.act_left_eq_pullbackLift (T := Over.mk (β ≫ f))
    (D.act (Over.homMk α hβ : (Over.mk (β ≫ f) : Over S) ⟶ (Over.map f).obj D.over)
      (Over.homMk β rfl : (Over.mk (β ≫ f) : Over S) ⟶ Over.mk f))
    (Over.homMk γ hγβ : (Over.mk (β ≫ f) : Over S) ⟶ Over.mk f)
    (α := pullback.lift α β hβ ≫ D.transitionPullbackIso.hom ≫
      pullback.snd f (D.over.hom ≫ f))
    (β := γ) hinner rfl hα'
  have hsingle := D.act_left_eq_pullbackLift (T := Over.mk (β ≫ f))
    (Over.homMk α hβ : (Over.mk (β ≫ f) : Over S) ⟶ (Over.map f).obj D.over)
    (Over.homMk γ hγβ : (Over.mk (β ≫ f) : Over S) ⟶ Over.mk f)
    (α := α) (β := γ) rfl rfl hγ
  rw [houter, hsingle] at key
  exact key

/-- The coaction `(x, v) ↦ x · v` lies over the projection of `X ×_S V` to `X`, in the form in
which the two lifts of this file need it: composed with the structure morphism of `V` over `S` it
is the projection to `X` followed by `f`.

This is `AlgebraicGeometry.DescentDatum.transitionPullbackIso_inv_comp_pullbackFst` with `f`
appended. -/
theorem transitionPullbackIso_inv_comp_pullbackFst_comp :
    D.transitionPullbackIso.inv ≫
        pullback.fst (D.over.hom ≫ f) f ≫ D.over.hom ≫ f =
      pullback.fst f (D.over.hom ≫ f) ≫ f := by
  rw [← Category.assoc (pullback.fst (D.over.hom ≫ f) f), ← Category.assoc,
    D.transitionPullbackIso_inv_comp_pullbackFst]

/-- **The coaction of a descent datum is the action of the first coordinate on the second.**  A
point `w` of `X ×_S V` with coordinates `β` in `X` and `α` in `V` satisfies
```
w · (φ⁻¹ followed by the projection to V) = α · β,
```
the right-hand side being the action of
`AlgebraicGeometry.DescentDatum.act_left_eq_pullbackLift`.  Geometrically: the coaction
`(x, v) ↦ x · v` of step 4 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) is the gluing isomorphism read
after the swap, which is
`AlgebraicGeometry.DescentDatum.transitionPullbackIso_inv_eq`. -/
theorem comp_transitionPullbackIso_inv_comp_pullbackFst {T : Scheme.{u}}
    (w : T ⟶ pullback f (D.over.hom ≫ f)) {α : T ⟶ D.over.left} {β : T ⟶ X}
    (hα : w ≫ pullback.snd f (D.over.hom ≫ f) = α)
    (hβ : w ≫ pullback.fst f (D.over.hom ≫ f) = β)
    (hw : α ≫ (D.over.hom ≫ f) = β ≫ f) :
    w ≫ D.transitionPullbackIso.inv ≫ pullback.fst (D.over.hom ≫ f) f =
      pullback.lift α β hw ≫ D.transitionPullbackIso.hom ≫
        pullback.snd f (D.over.hom ≫ f) := by
  subst hα
  subst hβ
  have hswap : w ≫ (pullbackSymmetry f (D.over.hom ≫ f)).hom =
      pullback.lift (w ≫ pullback.snd f (D.over.hom ≫ f))
        (w ≫ pullback.fst f (D.over.hom ≫ f)) hw := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_fst]
    · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_snd]
  calc w ≫ D.transitionPullbackIso.inv ≫ pullback.fst (D.over.hom ≫ f) f
      = (w ≫ (pullbackSymmetry f (D.over.hom ≫ f)).hom) ≫
          D.transitionPullbackIso.hom ≫ pullback.snd f (D.over.hom ≫ f) := by
        rw [D.transitionPullbackIso_inv_eq]
        simp only [Category.assoc, pullbackSymmetry_hom_comp_fst]
    _ = _ := by rw [hswap]

/-- **The two restriction maps of the cocycle diagram of step 4 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK), and their cocycle identity.**
There are two morphisms `l, l' : (X ×_S V) ×_S X ⟶ X ×_S V` with

* `l` the map `(x₁, v, x₂) ↦ (x₂, x₁ · v)`: its `X`-coordinate is the second copy of `X` and its
  `V`-coordinate is the coaction applied to the first two;
* `l'` the map `(x₁, v, x₂) ↦ (x₂, v)`: its `X`-coordinate is the second copy of `X` and its
  `V`-coordinate is `v`;

and they satisfy `x₂ · (x₁ · v) = x₂ · v`, that is, their composites with the coaction agree.
The last clause is `AlgebraicGeometry.DescentDatum.act_act_pullbackLift`, i.e. the cocycle
condition of the datum; the first four are
`CategoryTheory.Limits.pullback.lift_fst` and `CategoryTheory.Limits.pullback.lift_snd`.

This is the geometric content of the hypothesis `hkey` of step 4, and it holds for every descent
datum with no further hypothesis. -/
theorem exists_transitionTriple_restrictions :
    ∃ l l' : pullback (pullback.fst f (D.over.hom ≫ f) ≫ f) f ⟶
        pullback f (D.over.hom ≫ f),
      l ≫ pullback.fst f (D.over.hom ≫ f) =
          pullback.snd (pullback.fst f (D.over.hom ≫ f) ≫ f) f ∧
        l ≫ pullback.snd f (D.over.hom ≫ f) =
          pullback.fst (pullback.fst f (D.over.hom ≫ f) ≫ f) f ≫
            D.transitionPullbackIso.inv ≫ pullback.fst (D.over.hom ≫ f) f ∧
        l' ≫ pullback.fst f (D.over.hom ≫ f) =
          pullback.snd (pullback.fst f (D.over.hom ≫ f) ≫ f) f ∧
        l' ≫ pullback.snd f (D.over.hom ≫ f) =
          pullback.fst (pullback.fst f (D.over.hom ≫ f) ≫ f) f ≫
            pullback.snd f (D.over.hom ≫ f) ∧
        l ≫ D.transitionPullbackIso.inv ≫ pullback.fst (D.over.hom ≫ f) f =
          l' ≫ D.transitionPullbackIso.inv ≫ pullback.fst (D.over.hom ≫ f) f := by
  have hβ : (pullback.fst (pullback.fst f (D.over.hom ≫ f) ≫ f) f ≫
        pullback.snd f (D.over.hom ≫ f)) ≫ (D.over.hom ≫ f) =
      (pullback.fst (pullback.fst f (D.over.hom ≫ f) ≫ f) f ≫
        pullback.fst f (D.over.hom ≫ f)) ≫ f := by
    simp only [Category.assoc]
    rw [← pullback.condition (f := f) (g := D.over.hom ≫ f)]
  have hγ : (pullback.fst (pullback.fst f (D.over.hom ≫ f) ≫ f) f ≫
        pullback.snd f (D.over.hom ≫ f)) ≫ (D.over.hom ≫ f) =
      pullback.snd (pullback.fst f (D.over.hom ≫ f) ≫ f) f ≫ f := by
    rw [hβ]
    exact (pullback.condition (f := pullback.fst f (D.over.hom ≫ f) ≫ f) (g := f)).trans rfl
  have hA : (pullback.fst (pullback.fst f (D.over.hom ≫ f) ≫ f) f ≫
        D.transitionPullbackIso.inv ≫ pullback.fst (D.over.hom ≫ f) f) ≫
        (D.over.hom ≫ f) =
      pullback.snd (pullback.fst f (D.over.hom ≫ f) ≫ f) f ≫ f := by
    simp only [Category.assoc]
    rw [D.transitionPullbackIso_inv_comp_pullbackFst_comp]
    exact pullback.condition (f := pullback.fst f (D.over.hom ≫ f) ≫ f) (g := f)
  have hr1A := D.comp_transitionPullbackIso_inv_comp_pullbackFst
    (pullback.fst (pullback.fst f (D.over.hom ≫ f) ≫ f) f) rfl rfl hβ
  have hαA : (pullback.lift (pullback.fst (pullback.fst f (D.over.hom ≫ f) ≫ f) f ≫
          pullback.snd f (D.over.hom ≫ f))
        (pullback.fst (pullback.fst f (D.over.hom ≫ f) ≫ f) f ≫
          pullback.fst f (D.over.hom ≫ f)) hβ ≫
        D.transitionPullbackIso.hom ≫ pullback.snd f (D.over.hom ≫ f)) ≫
        (D.over.hom ≫ f) =
      pullback.snd (pullback.fst f (D.over.hom ≫ f) ≫ f) f ≫ f := by
    rw [← hr1A]; exact hA
  refine ⟨pullback.lift _ _ hA.symm, pullback.lift _ _ hγ.symm,
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
  rw [D.comp_transitionPullbackIso_inv_comp_pullbackFst _
      ((pullback.lift_snd _ _ _).trans hr1A) (pullback.lift_fst _ _ _) hαA,
    D.comp_transitionPullbackIso_inv_comp_pullbackFst _
      (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _) hγ]
  exact D.act_act_pullbackLift _ _ _ hβ hγ hαA

end Action

section Diagram

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f) (E : Set D.over.left)
    [Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤)]
    (hRA : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop)
    [IsAffine S] [IsAffine X] [Flat f] [QuasiSeparatedSpace D.over.left]
    {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
    (hU : ∀ i, IsCompact (U i : Set D.over.left)) (hE : E = ⋂ i, (U i : Set D.over.left))
    (h₁ : (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E))
    (h₂ : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E))

include hRA hU hE in
/-- **The cocycle diagram of step 4 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK), produced from the descent datum.**
Let `f : X ⟶ S` be a flat morphism of affine schemes, let `D` be a descent datum relative to `f`
whose scheme `V` is quasi-separated, and let `E ⊆ V` be an intersection of a nonempty family of
quasi-compact opens whose two preimages are exchanged by the gluing isomorphism.  Then there are
a ring `Q₃`, a presentation of it as `Γ(X, ⊤) ⊗_{Γ(S, ⊤)} Γ(X ×_S E, 𝒪)`, and two morphisms
`Λ₀, Λ₀'` out of `Γ(X ×_S E, 𝒪)` satisfying the four leg conditions and the cocycle identity.

This is the hypothesis `hcocycle` of
`AlgebraicGeometry.DescentDatum.isEffective_of_cocycleDiagram_of_legs_of_restrictOpen`, which is
to say the coassociativity obligation `hkey` of step 4, now a theorem.  `Q₃` is
`Γ((X ×_S V) ×_S X ⊇ E-part, 𝒪)` and its pushout square is
`AlgebraicGeometry.DescentDatum.isPushout_algebraMap_transitionTargetBaseChange`; `Λ₀` and `Λ₀'`
are restriction along the two maps of
`AlgebraicGeometry.DescentDatum.exists_transitionTriple_restrictions`, their leg conditions are
functoriality of `AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap` together with the two
components of those maps, and the cocycle identity is their last clause, i.e. the cocycle
condition of the datum. -/
theorem exists_cocycleDiagram_descentAlgebraTransition :
    ∃ (Q₃ : CommRingCat.{u}) (i₃ : CommRingCat.of ↥Γ(X, ⊤) ⟶ Q₃)
      (j₃ Λ₀ Λ₀' : (pullback f (D.over.hom ≫ f)).sectionsRingOnSubset
        (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⟶ Q₃),
      IsPushout (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)))
          (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) ≫
            (pullback.fst f (D.over.hom ≫ f)).appTop ≫
              (pullback f (D.over.hom ≫ f)).topToSubset
                (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E)) i₃ j₃ ∧
        ((pullback.fst f (D.over.hom ≫ f)).appTop ≫
          (pullback f (D.over.hom ≫ f)).topToSubset
            (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E)) ≫ Λ₀ = i₃ ∧
        Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
            (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _) ≫ Λ₀ =
          (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
              (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
            (D.transitionSectionsIso E h₁ h₂).hom) ≫ j₃ ∧
        ((pullback.fst f (D.over.hom ≫ f)).appTop ≫
          (pullback f (D.over.hom ≫ f)).topToSubset
            (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E)) ≫ Λ₀' = i₃ ∧
        Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
            (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _) ≫ Λ₀' =
          Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
            (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _) ≫ j₃ ∧
        (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
              (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
            (D.transitionSectionsIso E h₁ h₂).hom) ≫ Λ₀ =
          (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
              (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
            (D.transitionSectionsIso E h₁ h₂).hom) ≫ Λ₀' := by
  obtain ⟨l, l', hl1, hl2, hl1', hl2', hlcoc⟩ := D.exists_transitionTriple_restrictions
  have cl : (⇑(pullback.fst (pullback.fst f (D.over.hom ≫ f) ≫ f) f) ⁻¹'
        (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E)) ⊆
      ⇑l ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) := by
    change _ ⊆ ⇑(l ≫ pullback.snd f (D.over.hom ≫ f)) ⁻¹' E
    rw [hl2]
    exact fun z hz => h₂ hz
  have cl' : (⇑(pullback.fst (pullback.fst f (D.over.hom ≫ f) ≫ f) f) ⁻¹'
        (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E)) ⊆
      ⇑l' ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) := by
    change _ ⊆ ⇑(l' ≫ pullback.snd f (D.over.hom ≫ f)) ⁻¹' E
    rw [hl2']
    exact subset_rfl
  refine ⟨_, _, _, Scheme.sectionsRingOnSubsetMap l _ _ cl,
    Scheme.sectionsRingOnSubsetMap l' _ _ cl',
    D.isPushout_algebraMap_transitionTargetBaseChange E hRA U hU hE, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, Scheme.topToSubset_comp_sectionsRingOnSubsetMap, ← Category.assoc,
      ← Scheme.Hom.comp_appTop, hl1]
  · rw [Scheme.sectionsRingOnSubsetMap_comp, transitionSectionsIso_hom, Category.assoc,
      Scheme.sectionsRingOnSubsetMap_comp]
    exact (Scheme.sectionsRingOnSubsetMap_congr
        (hl2.trans (Category.assoc _ _ _).symm) _ _ _ _).trans
      (Scheme.sectionsRingOnSubsetMap_comp _ _ _ _ _ _ _).symm
  · rw [Category.assoc, Scheme.topToSubset_comp_sectionsRingOnSubsetMap, ← Category.assoc,
      ← Scheme.Hom.comp_appTop, hl1']
  · rw [Scheme.sectionsRingOnSubsetMap_comp, Scheme.sectionsRingOnSubsetMap_comp]
    exact Scheme.sectionsRingOnSubsetMap_congr hl2' _ _ _ _
  · rw [transitionSectionsIso_hom, Category.assoc, Category.assoc,
      Scheme.sectionsRingOnSubsetMap_comp, Scheme.sectionsRingOnSubsetMap_comp]
    exact (Scheme.sectionsRingOnSubsetMap_comp _ _ _ _ _ _ _).trans
      ((Scheme.sectionsRingOnSubsetMap_congr
          ((Category.assoc _ _ _).trans (hlcoc.trans (Category.assoc _ _ _).symm))
          _ _ _ _).trans
        (Scheme.sectionsRingOnSubsetMap_comp _ _ _ _ _ _ _).symm)

end Diagram

section Residue

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f)

/-- **The residue of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) over an affine
base, with the coassociativity obligation discharged.**  Let `f : X ⟶ S` be a surjective flat
quasi-compact morphism of affine schemes and let `D` be a descent datum relative to `f` whose
scheme over `X` is ind-quasi-affine.  Then `D` is effective as soon as `hlegs`, `hrestrict` and
`hglueing` hold.

This is `AlgebraicGeometry.DescentDatum.isEffective_of_cocycleDiagram_of_legs_of_restrictOpen`
with its first hypothesis supplied by
`AlgebraicGeometry.DescentDatum.exists_cocycleDiagram_descentAlgebraTransition`; the remaining
three are unchanged, character for character.  `hglueing` is
[Stacks, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4).

**This is not Stacks 0APK and carries no tag.** -/
theorem isEffective_of_legs_of_restrictOpen
    [IsAffine S] [IsAffine X] [Flat f] [Surjective f] [QuasiCompact f]
    [IsIndQuasiAffineHom D.over.hom]
    (hlegs : ∀ (E : Set D.over.left) {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
      (_hU : ∀ i, IsCompact (U i : Set D.over.left))
      (_hE : E = ⋂ i, (U i : Set D.over.left)) (hEinv : D.IsTransitionInvariantSet E)
      (W : D.over.left.Opens) (_hWinv : D.IsTransitionInvariant W)
      (_hWE : (W : Set D.over.left) ⊆ E),
      (Spec.map (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
            (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
          (D.transitionSectionsIso E
            (D.subset_preimage_transitionPullbackIso_hom_of_invariantSet E hEinv)
            (D.subset_preimage_transitionPullbackIso_inv_of_invariantSet E hEinv)).hom)).base ⁻¹'
          subsetΓSpecImage D.over.left E (W : Set D.over.left) =
        (Spec.map (Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
            (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _))).base ⁻¹'
          subsetΓSpecImage D.over.left E (W : Set D.over.left))
    (hrestrict : ∀ (E : Set D.over.left)
      [Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤)] [Algebra ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      [Algebra ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      [IsScalarTower ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      (hRA : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop)
      (hRC : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
        (D.over.hom ≫ f).appTop ≫ D.over.left.topToSubset E)
      (hAC : CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
        D.over.hom.appTop ≫ D.over.left.topToSubset E)
      [QuasiSeparatedSpace D.over.left] {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
      (hU : ∀ i, IsCompact (U i : Set D.over.left)) (hE : E = ⋂ i, (U i : Set D.over.left))
      (h₁ : (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
        ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E))
      (h₂ : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
        ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E))
      (W : D.over.left.Opens) (hWinv : D.IsTransitionInvariant W)
      (_hWE : (W : Set D.over.left) ⊆ E)
      (W₀ : (Spec (CommRingCat.of ↥(ModuleCat.descentInvariants ↥Γ(S, ⊤) ↥Γ(X, ⊤)
          ↥(D.over.left.sectionsRingOnSubset E)
          (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂)))).Opens)
      (_hW₀ : ((Spec.map (CommRingCat.ofHom (algebraMap
            (ModuleCat.descentInvariants ↥Γ(S, ⊤) ↥Γ(X, ⊤)
              ↥(D.over.left.sectionsRingOnSubset E)
              (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂))
            ↥(D.over.left.sectionsRingOnSubset E))) ⁻¹ᵁ W₀ :
            (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E))).Opens) :
          Set (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E)))) =
        subsetΓSpecImage D.over.left E (W : Set D.over.left)),
      DescentData.IsEffective (D.restrictOpen W hWinv))
    (hglueing : (∀ v : D.over.left, ∃ (W : D.over.left.Opens) (hW : D.IsTransitionInvariant W),
        v ∈ W ∧ DescentData.IsEffective (D.restrictOpen W hW)) →
      DescentData.IsEffective D) :
    DescentData.IsEffective D := by
  refine D.isEffective_of_cocycleDiagram_of_legs_of_restrictOpen ?_ hlegs hrestrict hglueing
  intro E _ _ _ _ hRA _ _ _ I _ U hU hE h₁ h₂
  exact D.exists_cocycleDiagram_descentAlgebraTransition E hRA U hU hE h₁ h₂

end Residue

end AlgebraicGeometry.DescentDatum

end

end
