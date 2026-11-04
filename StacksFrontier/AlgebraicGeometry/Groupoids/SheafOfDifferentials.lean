module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Assembly.Basic
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareEpi
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareFlatIso
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Compose
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The sheaf of differentials of a groupoid scheme

Let `(U, R, s, t, c)` be a groupoid scheme over a scheme `S`, with identity section `e : U ⟶ R`
and inverse `i : R ⟶ R`. Dividing two arrows with a common source, `(α, β) ↦ α ∘ β⁻¹`, is a
morphism `γ : R ×_{s, U, s} R ⟶ R`, and the square
```
R --Δ_s--→ R ×_{s, U, s} R
|                |
t                γ
↓                ↓
U ---e---------→ R
```
is cartesian: `α ∘ β⁻¹` is an identity arrow exactly when `α = β`, and then the identity arrow
is the one at their common target. Since `e` is an immersion, being a section of `s`, the
canonical map of conormal sheaves of [Stacks Project, Tag 01R4] attached to that square is a map
`t^* 𝒞_{U/R} ⟶ 𝒞_{R/R ×_U R}`, surjective by [Stacks Project, Tag 0473]; and the conormal sheaf
of the diagonal is `Ω_{R/U}` by [Stacks Project, Tag 08S2]. Composing the two gives the
canonical surjection of [Stacks Project, Tag 04R9].

## The roles of `s` and `t`

[Stacks Project, Tag 04R9] reads `Ω_{R/U}` with `R` over `U` via `t`, while the surjection it
displays is `t^* 𝒞_{U/R} ⟶ Ω_{R/U}` and its proof builds that surjection from the square above.
The two readings cannot both be meant. In the pair groupoid of a scheme `V` over `S`, where
`R = V ×_S V` with `t = pr₀` and `s = pr₁` and `e` the diagonal, one has `𝒞_{U/R} = Ω_{V/S}`,
hence `t^* 𝒞_{U/R} = pr₀^* Ω_{V/S}`, whereas the differentials of `t` are `pr₁^* Ω_{V/S}` and
the differentials of `s` are `pr₀^* Ω_{V/S}`. For `V` the disjoint union of a line and a point
over a field those two differ, and only the differentials of `s` admit a surjection from
`t^* 𝒞_{U/R}`. So the displayed formula `t^* 𝒞_{U/R} ⟶ Ω_{R/U}` is what is proved here, with
`Ω_{R/U}` the differentials of `s`; equivalently, after pulling back along the inverse,
`s^* 𝒞_{U/R}` surjects onto the differentials of `t`. The source's own proof produces exactly
this: its `(pr₀, i ∘ pr₁)` is a morphism `R ×_{s, U, t} R ⟶ R ×_{s, U, s} R`, not one into
`R ×_{t, U, t} R`, and its composite with `(1, i)` is the diagonal of `s`.

## The flatness clause

The second clause of [Stacks Project, Tag 04R9] — that the surjection is an isomorphism when `s`
is flat — rests on the flat half of [Stacks Project, Tag 0473], namely that the canonical map of
conormal sheaves of a cartesian square of immersions is an isomorphism when the ambient morphism
is flat. That half is `Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat`, and it is what
is applied here, to the cartesian squares above.

What has to be supplied for it is flatness of the *ambient* morphism of each of those squares,
which is division. Division of arrows with a common source is a base change of the target
morphism along the source morphism, and division of arrows with a common target is a base change
of the source morphism along the target morphism; those are
`Stacks.Groupoids.GroupoidScheme.isPullback_divideSourcePair_snd` and
`Stacks.Groupoids.GroupoidScheme.isPullback_divideTargetPair_fst`, proved on generalized points
from the groupoid axioms. On the target-differentials side flatness of `s` therefore applies
directly; on the source-differentials side it applies through flatness of `t`, which follows
because the inverse is an isomorphism of the underlying schemes
(`AlgebraicGeometry.groupoidInverse_left_isIso`). Both clause-(2) statements are consequently
proved from the source's own hypothesis, that `s` is flat.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.divideSourcePair` and
  `Stacks.Groupoids.GroupoidScheme.divide`: division of two arrows with a common source, formed
  in schemes over `S` and in schemes respectively;
  `Stacks.Groupoids.GroupoidScheme.divideTargetPair` and
  `Stacks.Groupoids.GroupoidScheme.divideTarget` are the same for a common target.
* `Stacks.Groupoids.GroupoidScheme.conormalToDifferentials`: **the canonical map
  `t^* 𝒞_{U/R} ⟶ Ω_{R/U}` of [Stacks Project, Tag 04R9]**, with `R` over `U` via `s`.
* `Stacks.Groupoids.GroupoidScheme.targetConormalToDifferentials`: the same map for the other
  reading, `s^* 𝒞_{U/R} ⟶ Ω_{R/U}` with `R` over `U` via `t`.

## Main results

* `Stacks.Groupoids.GroupoidScheme.eq_of_compose_inverse_eq_identity` and
  `Stacks.Groupoids.GroupoidScheme.eq_of_inverse_compose_eq_identity`: two arrows with a common
  source, resp. target, whose quotient is an identity arrow are equal.
* `Stacks.Groupoids.GroupoidScheme.isPullback_diagonal_divide` and
  `Stacks.Groupoids.GroupoidScheme.isPullback_diagonal_divideTarget`: the displayed square, and
  its analogue for the target, are cartesian.
* `Stacks.Groupoids.GroupoidScheme.epi_conormalToDifferentials` and
  `Stacks.Groupoids.GroupoidScheme.epi_targetConormalToDifferentials`: **the canonical map is
  surjective**, the first clause of [Stacks Project, Tag 04R9], in both readings.
* `Stacks.Groupoids.GroupoidScheme.isPullback_divideSourcePair_snd` and
  `Stacks.Groupoids.GroupoidScheme.isPullback_divideTargetPair_fst`: division is a base change of
  the target, resp. of the source, morphism; hence
  `Stacks.Groupoids.GroupoidScheme.flat_divide` and
  `Stacks.Groupoids.GroupoidScheme.flat_divideTarget`, flatness of division when `s` is flat.
* `Stacks.Groupoids.GroupoidScheme.isIso_conormalToDifferentials` and
  `Stacks.Groupoids.GroupoidScheme.isIso_targetConormalToDifferentials`: **the canonical map is
  an isomorphism when `s` is flat**, the second clause of [Stacks Project, Tag 04R9], in both
  readings.

## Implementation notes

The groupoid axioms of `Stacks.Groupoids.GroupoidScheme` are stated on generalized points in
schemes over `S`, so the cartesian square is proved there, with the composition calculus of
`StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Compose`, and then carried to schemes along
`CategoryTheory.Over.forget`, which preserves pullbacks. The fibre square of `s` with itself
formed in schemes over `S` is not Mathlib's chosen pullback of the underlying morphisms, so the
comparison `Stacks.Groupoids.GroupoidScheme.sourcePairIso` is inserted; the division morphism in
schemes is defined through it, which is why the cartesian square in schemes is obtained by
transporting the one over `S` rather than proved again.

## References

* [Stacks Project, Tag 04R9](https://stacks.math.columbia.edu/tag/04R9)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 01KT](https://stacks.math.columbia.edu/tag/01KT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-! ### The identity section is an immersion -/

/-- **The identity section of a groupoid scheme is an immersion**, being a section of the source
morphism; this is [Stacks Project, Tag 01KT]. -/
@[ega "IV 16.2.3" "special case"]
instance isImmersion_identity_left : IsImmersion G.identity.left := by
  have h : IsImmersion (G.identity.left ≫ G.source.left) := by
    rw [identity_left_comp_source_left G]
    infer_instance
  exact IsImmersion.of_comp G.identity.left G.source.left

/-! ### Division of arrows with a common source -/

/-- The target of the inverse of a generalized arrow is its source. -/
theorem comp_inverse_comp_target {T : Over S} (x : T ⟶ G.arrows) :
    (x ≫ G.inverse) ≫ G.target = x ≫ G.source := by
  rw [Category.assoc, G.target_inverse]

/-- The source of the inverse of a generalized arrow is its target. -/
theorem comp_inverse_comp_source {T : Over S} (x : T ⟶ G.arrows) :
    (x ≫ G.inverse) ≫ G.source = x ≫ G.target := by
  rw [Category.assoc, G.source_inverse]

/-- Division of two arrows with a common source, as a morphism of schemes over `S` out of their
fibre square: the pair `(α, β)` goes to `α ∘ β⁻¹`. -/
@[implicit_reducible]
def divideSourcePair : pullback G.source G.source ⟶ G.arrows :=
  G.compose (pullback.fst G.source G.source)
    (pullback.snd G.source G.source ≫ G.inverse)
    (by rw [Category.assoc, G.target_inverse]; exact pullback.condition)

/-- Division of the two components of a generalized point of the fibre square. -/
private theorem compose_eq_comp_divideSourcePair {T : Over S} (p : T ⟶ pullback G.source G.source)
    (w : (p ≫ pullback.fst G.source G.source) ≫ G.source =
      ((p ≫ pullback.snd G.source G.source) ≫ G.inverse) ≫ G.target) :
    G.compose (p ≫ pullback.fst G.source G.source)
      ((p ≫ pullback.snd G.source G.source) ≫ G.inverse) w = p ≫ G.divideSourcePair := by
  have w' : (p ≫ pullback.fst G.source G.source) ≫ G.source =
      (p ≫ (pullback.snd G.source G.source ≫ G.inverse)) ≫ G.target := by
    simpa only [Category.assoc] using w
  exact (groupoidCompose_arrow_eq _ _ _ _ w w' rfl (Category.assoc _ _ _)).trans
    (groupoidCompose_precomp G p _ _
      (by rw [Category.assoc, G.target_inverse]; exact pullback.condition) w')

/-- Dividing an arrow by itself gives the identity arrow at its target. -/
theorem diagonal_comp_divideSourcePair :
    pullback.diagonal G.source ≫ G.divideSourcePair = G.target ≫ G.identity := by
  have hw : (𝟙 G.arrows) ≫ G.source = ((𝟙 G.arrows) ≫ G.inverse) ≫ G.target := by
    rw [Category.id_comp, Category.id_comp, G.target_inverse]
  have w' : (pullback.diagonal G.source ≫ pullback.fst G.source G.source) ≫ G.source =
      ((pullback.diagonal G.source ≫ pullback.snd G.source G.source) ≫ G.inverse) ≫
        G.target := by
    rw [pullback.diagonal_fst, pullback.diagonal_snd]
    exact hw
  calc pullback.diagonal G.source ≫ G.divideSourcePair
      = G.compose (pullback.diagonal G.source ≫ pullback.fst G.source G.source)
          ((pullback.diagonal G.source ≫ pullback.snd G.source G.source) ≫ G.inverse) w' :=
        (G.compose_eq_comp_divideSourcePair _ w').symm
    _ = G.compose (𝟙 G.arrows) ((𝟙 G.arrows) ≫ G.inverse) hw :=
        groupoidCompose_arrow_eq _ _ _ _ w' hw (pullback.diagonal_fst _)
          (by rw [pullback.diagonal_snd])
    _ = G.target ≫ G.identity :=
        (G.right_inverse G.arrows (𝟙 G.arrows) hw).trans (Category.id_comp _)

/-- Cancelling `y` against `y⁻¹` on the right: `(x ∘ y⁻¹) ∘ y = x` for arrows with a common
source. -/
private theorem compose_compose_inverse_comp {T : Over S} (x y : T ⟶ G.arrows)
    (w : x ≫ G.source = (y ≫ G.inverse) ≫ G.target)
    (w₁ : G.compose x (y ≫ G.inverse) w ≫ G.source = y ≫ G.target) :
    G.compose (G.compose x (y ≫ G.inverse) w) y w₁ = x := by
  have wbi : (y ≫ G.inverse) ≫ G.source = y ≫ G.target := G.comp_inverse_comp_source y
  have hab : x ≫ G.source = y ≫ G.source := w.trans (G.comp_inverse_comp_target y)
  have w₂ : x ≫ G.source = G.compose (y ≫ G.inverse) y wbi ≫ G.target := by
    rw [groupoidCompose_target, Category.assoc, G.target_inverse, hab]
  have w₃ : x ≫ G.source = (x ≫ G.source ≫ G.identity) ≫ G.target := by
    rw [Category.assoc, Category.assoc, G.target_identity, Category.comp_id]
  have hleft : G.compose (y ≫ G.inverse) y wbi = x ≫ G.source ≫ G.identity :=
    (G.left_inverse T y wbi).trans (by rw [← Category.assoc, ← hab, Category.assoc])
  calc G.compose (G.compose x (y ≫ G.inverse) w) y w₁
      = G.compose x (G.compose (y ≫ G.inverse) y wbi) w₂ :=
        groupoidCompose_assoc G x (y ≫ G.inverse) y w wbi w₁ w₂
    _ = x := (groupoidCompose_arrow_eq x x _ (x ≫ G.source ≫ G.identity) w₂ w₃ rfl hleft).trans
        (G.right_identity T x w₃)

/-- **Two arrows with a common source whose quotient is an identity arrow are equal**, and the
identity arrow is then the one at their common target. On generalized points: if
`α ∘ β⁻¹ = e(x)` then `α = β` and `x = t(α)`. -/
theorem eq_of_compose_inverse_eq_identity {T : Over S} (a b : T ⟶ G.arrows)
    (q : T ⟶ G.objects) (w : a ≫ G.source = (b ≫ G.inverse) ≫ G.target)
    (h : G.compose a (b ≫ G.inverse) w = q ≫ G.identity) :
    a = b ∧ a ≫ G.target = q := by
  have hq : a ≫ G.target = q := by
    have h1 := congrArg (fun z : T ⟶ G.arrows => z ≫ G.target) h
    simpa only [groupoidCompose_target, Category.assoc, G.target_identity,
      Category.comp_id] using h1
  have hqb : b ≫ G.target = q := by
    have h2 := congrArg (fun z : T ⟶ G.arrows => z ≫ G.source) h
    simpa only [groupoidCompose_source, Category.assoc, G.source_inverse,
      G.source_identity, Category.comp_id] using h2
  refine ⟨?_, hq⟩
  have w₁ : G.compose a (b ≫ G.inverse) w ≫ G.source = b ≫ G.target :=
    (groupoidCompose_source G a (b ≫ G.inverse) w).trans (G.comp_inverse_comp_source b)
  have w₄ : (q ≫ G.identity) ≫ G.source = b ≫ G.target := by
    rw [Category.assoc, G.source_identity, Category.comp_id, hqb]
  have w₅ : (b ≫ G.target ≫ G.identity) ≫ G.source = b ≫ G.target := by
    rw [Category.assoc, Category.assoc, G.source_identity, Category.comp_id]
  have h5 : q ≫ G.identity = b ≫ G.target ≫ G.identity := by
    rw [← hqb, Category.assoc]
  calc a = G.compose (G.compose a (b ≫ G.inverse) w) b w₁ :=
        (G.compose_compose_inverse_comp a b w w₁).symm
    _ = G.compose (q ≫ G.identity) b w₄ := groupoidCompose_arrow_eq _ _ _ _ w₁ w₄ h rfl
    _ = b := (groupoidCompose_arrow_eq _ _ _ _ w₄ w₅ h5 rfl).trans (G.left_identity T b w₅)

/-- The previous lemma read at a morphism into the fibre square: the two components of a
generalized point of the fibre square whose division is an identity arrow agree. -/
private theorem eq_of_comp_divideSourcePair {T : Over S} (p : T ⟶ pullback G.source G.source)
    (q : T ⟶ G.objects) (hp : p ≫ G.divideSourcePair = q ≫ G.identity) :
    p ≫ pullback.fst G.source G.source = p ≫ pullback.snd G.source G.source ∧
      (p ≫ pullback.fst G.source G.source) ≫ G.target = q := by
  have hab : (p ≫ pullback.fst G.source G.source) ≫ G.source =
      (p ≫ pullback.snd G.source G.source) ≫ G.source := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have w := hab.trans (G.comp_inverse_comp_target (p ≫ pullback.snd G.source G.source)).symm
  exact G.eq_of_compose_inverse_eq_identity _ _ q w
    ((G.compose_eq_comp_divideSourcePair p w).trans hp)

/-! ### The cartesian square -/

/-- **The square formed by the diagonal of the source, the target, division and the identity
section is cartesian**, in schemes over `S`. -/
@[sga "3 VIB 5.1" "more general"]
theorem isPullback_diagonal_divideSourcePair :
    IsPullback (pullback.diagonal G.source) G.target G.divideSourcePair G.identity := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk G.diagonal_comp_divideSourcePair
    (fun c => c.fst ≫ pullback.fst G.source G.source) (fun c => ?_) (fun c => ?_)
    (fun c m h₁ _ => ?_))
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
      exact (G.eq_of_comp_divideSourcePair c.fst c.snd c.condition).1
  · exact (G.eq_of_comp_divideSourcePair c.fst c.snd c.condition).2
  · rw [← h₁, Category.assoc, pullback.diagonal_fst, Category.comp_id]

/-- The fibre square of the source morphism with itself, formed in schemes over `S`, is a fibre
square of the underlying morphism of schemes with itself. -/
theorem isPullback_sourcePair_left :
    IsPullback (pullback.fst G.source G.source).left (pullback.snd G.source G.source).left
      G.source.left G.source.left := by
  simpa using (IsPullback.of_hasPullback G.source G.source).map (Over.forget S)

/-- The comparison of the fibre square of the source morphism with itself formed in schemes over
`S` with Mathlib's chosen pullback of the underlying morphism with itself. -/
def sourcePairIso :
    (pullback G.source G.source).left ≅ pullback G.source.left G.source.left :=
  G.isPullback_sourcePair_left.isoPullback

/-- Division of two arrows with a common source, as a morphism of schemes out of the pullback of
the source morphism with itself: the pair `(α, β)` goes to `α ∘ β⁻¹`. -/
def divide : pullback G.source.left G.source.left ⟶ G.arrows.left :=
  G.sourcePairIso.inv ≫ G.divideSourcePair.left

/-- **The square formed by the diagonal of the source, the target, division and the identity
section is cartesian**, in schemes. -/
@[sga "3 VIB 5.1" "more general"]
theorem isPullback_diagonal_divide :
    IsPullback (pullback.diagonal G.source.left) G.target.left G.divide G.identity.left := by
  have hsq : IsPullback (pullback.diagonal G.source).left G.target.left
      G.divideSourcePair.left G.identity.left := by
    simpa using G.isPullback_diagonal_divideSourcePair.map (Over.forget S)
  refine hsq.of_iso (Iso.refl _) G.sourcePairIso (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.id_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, sourcePairIso, IsPullback.isoPullback_hom_fst, ← Over.comp_left,
        pullback.diagonal_fst, Over.id_left, pullback.diagonal_fst]
    · rw [Category.assoc, sourcePairIso, IsPullback.isoPullback_hom_snd, ← Over.comp_left,
        pullback.diagonal_snd, Over.id_left, pullback.diagonal_snd]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Category.comp_id, divide, Iso.hom_inv_id_assoc]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]

/-! ### The canonical surjection -/

/-- **[Stacks Project, Tag 04R9]: the canonical map `t^* 𝒞_{U/R} ⟶ Ω_{R/U}`**, from the pullback
along the target morphism of the conormal sheaf of the identity section to the sheaf of
relative differentials of the source morphism.

It is the canonical map of conormal sheaves of [Stacks Project, Tag 01R4] attached to the
cartesian square `Stacks.Groupoids.GroupoidScheme.isPullback_diagonal_divide`, whose source is
`t^* 𝒞_{U/R}` and whose target is the conormal sheaf of the diagonal of `s`, followed by the
inverse of the isomorphism of [Stacks Project, Tag 08S2] identifying that conormal sheaf with
`Ω_{R/U}`. See the module docstring on which of `s` and `t` carries the differentials. -/
@[stacks 04R9 "the canonical map"]
def conormalToDifferentials :
    (RingedSpaceModuleAdjunction.modulePullback G.target.left.toLRSHom.toShHom).obj
        (Stacks.Conormal.conormalSheaf G.identity.left) ⟶
      Scheme.Hom.relativeDifferentials G.source.left :=
  Stacks.Immersion.immersionConormalSheafMap (pullback.diagonal G.source.left)
      G.identity.left G.target.left G.divide
      (Stacks.Immersion.toShHom_square G.isPullback_diagonal_divide.w) ≫
    (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal G.source.left).inv

/-- **[Stacks Project, Tag 04R9]: the canonical map `t^* 𝒞_{U/R} ⟶ Ω_{R/U}` is surjective.**
The sheaf of differentials of `R` over `U` is a quotient of the pullback along the target
morphism of the conormal sheaf of the identity section.

The map of conormal sheaves of the cartesian square is surjective by
[Stacks Project, Tag 0473], and the comparison of [Stacks Project, Tag 08S2] is an isomorphism.
-/
@[stacks 04R9 "the canonical surjection"]
theorem epi_conormalToDifferentials : Epi G.conormalToDifferentials := by
  have h := Stacks.Immersion.epi_immersionConormalSheafMap (pullback.diagonal G.source.left)
    G.identity.left G.target.left G.divide G.isPullback_diagonal_divide
  have h2 : Epi (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal
      G.source.left).inv := @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)
  exact epi_comp' h h2


/-! ### Division is a base change, and the flatness clause -/

/-- **Division of arrows with a common source is a base change of the target morphism along the
source morphism**, in schemes over `S`: the square
```
R ×_{s, U, s} R --pr₁--→ R
|                        |
γ                        t
↓                        ↓
R -------s-------------→ U
```
is cartesian. On generalized points: a pair `(δ, β)` with `s(δ) = t(β)` comes from the unique
pair `(δ ∘ β, β)` of arrows with a common source. -/
theorem isPullback_divideSourcePair_snd :
    IsPullback G.divideSourcePair (pullback.snd G.source G.source) G.source G.target := by
  have hw : G.divideSourcePair ≫ G.source = pullback.snd G.source G.source ≫ G.target :=
    (groupoidCompose_source G (pullback.fst G.source G.source)
        (pullback.snd G.source G.source ≫ G.inverse)
        (by rw [Category.assoc, G.target_inverse]; exact pullback.condition)).trans
      (by rw [Category.assoc, G.source_inverse])
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun c => pullback.lift (G.compose c.fst c.snd c.condition) c.snd
      (groupoidCompose_source G c.fst c.snd c.condition)) (fun c => ?_) (fun c => ?_)
    (fun c m h₁ h₂ => ?_))
  · -- the lift divides back to the first leg of the cone
    have w₁ : G.compose c.fst c.snd c.condition ≫ G.source =
        (c.snd ≫ G.inverse) ≫ G.target :=
      (groupoidCompose_source G c.fst c.snd c.condition).trans
        (G.comp_inverse_comp_target c.snd).symm
    have w₂ : c.fst ≫ G.source = G.compose c.snd (c.snd ≫ G.inverse)
        (G.comp_inverse_comp_target c.snd).symm ≫ G.target :=
      c.condition.trans (groupoidCompose_target G c.snd (c.snd ≫ G.inverse) _).symm
    have w₃ : c.fst ≫ G.source = (c.fst ≫ G.source ≫ G.identity) ≫ G.target := by
      rw [Category.assoc, Category.assoc, G.target_identity, Category.comp_id]
    have hinv : G.compose c.snd (c.snd ≫ G.inverse) (G.comp_inverse_comp_target c.snd).symm =
        c.fst ≫ G.source ≫ G.identity := by
      refine (G.right_inverse _ c.snd _).trans ?_
      rw [← Category.assoc, ← c.condition, Category.assoc]
    refine (G.compose_eq_comp_divideSourcePair _
      (by rw [pullback.lift_fst, pullback.lift_snd]; exact w₁)).symm.trans ?_
    calc _ = G.compose (G.compose c.fst c.snd c.condition) (c.snd ≫ G.inverse) w₁ :=
          groupoidCompose_arrow_eq _ _ _ _ _ w₁ (pullback.lift_fst _ _ _)
            (by rw [pullback.lift_snd])
      _ = G.compose c.fst (G.compose c.snd (c.snd ≫ G.inverse)
            (G.comp_inverse_comp_target c.snd).symm) w₂ :=
          groupoidCompose_assoc G c.fst c.snd (c.snd ≫ G.inverse) c.condition _ w₁ w₂
      _ = c.fst := (groupoidCompose_arrow_eq _ _ _ _ w₂ w₃ rfl hinv).trans
          (G.right_identity _ c.fst w₃)
  · exact pullback.lift_snd _ _ _
  · -- the lift is the only such morphism
    have hcond : (m ≫ pullback.fst G.source G.source) ≫ G.source = c.snd ≫ G.source := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, h₂]
    have wα : (m ≫ pullback.fst G.source G.source) ≫ G.source =
        (c.snd ≫ G.inverse) ≫ G.target := hcond.trans (G.comp_inverse_comp_target c.snd).symm
    have w₄ : G.compose (m ≫ pullback.fst G.source G.source) (c.snd ≫ G.inverse) wα ≫
        G.source = c.snd ≫ G.target :=
      (groupoidCompose_source G _ (c.snd ≫ G.inverse) wα).trans
        (G.comp_inverse_comp_source c.snd)
    have wm : (m ≫ pullback.fst G.source G.source) ≫ G.source =
        ((m ≫ pullback.snd G.source G.source) ≫ G.inverse) ≫ G.target := by
      rw [h₂]
      exact wα
    have hm : G.compose (m ≫ pullback.fst G.source G.source) (c.snd ≫ G.inverse) wα = c.fst :=
      ((groupoidCompose_arrow_eq _ _ _ _ wα wm rfl (by rw [h₂])).trans
        (G.compose_eq_comp_divideSourcePair m wm)).trans h₁
    refine pullback.hom_ext ?_ (h₂.trans (pullback.lift_snd _ _ _).symm)
    refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
    exact (G.compose_compose_inverse_comp _ c.snd wα w₄).symm.trans
      (groupoidCompose_arrow_eq _ _ _ _ w₄ c.condition hm rfl)

/-- **Division of arrows with a common source is a base change of the target morphism**, in
schemes. -/
theorem isPullback_divide_snd :
    IsPullback G.divide (pullback.snd G.source.left G.source.left) G.source.left
      G.target.left := by
  have hsq : IsPullback G.divideSourcePair.left (pullback.snd G.source G.source).left
      G.source.left G.target.left := by
    simpa using G.isPullback_divideSourcePair_snd.map (Over.forget S)
  refine hsq.of_iso G.sourcePairIso (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, divide, Iso.hom_inv_id_assoc]
  · rw [Iso.refl_hom, Category.comp_id, sourcePairIso, IsPullback.isoPullback_hom_snd]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- **The target morphism of a groupoid scheme is flat as soon as the source morphism is**, the
inverse being an isomorphism of the underlying schemes. -/
theorem flat_target_left_of_flat_source_left [Flat G.source.left] : Flat G.target.left := by
  have h : G.inverse.left ≫ G.source.left = G.target.left := by
    rw [← Over.comp_left, G.source_inverse]
  have hiso : IsIso G.inverse.left := groupoidInverse_left_isIso G
  rw [← h]
  infer_instance

/-- **Division of arrows with a common source is flat when the source morphism is**, being a base
change of the target morphism, which is flat with the source morphism. -/
theorem flat_divide [Flat G.source.left] : Flat G.divide := by
  have := G.flat_target_left_of_flat_source_left
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback G.isPullback_divide_snd.flip
    inferInstance

/-- **[Stacks Project, Tag 04R9]: the canonical map `t^* 𝒞_{U/R} ⟶ Ω_{R/U}` is an isomorphism
when the source morphism is flat.** With `R` over `U` via `s`, the sheaf of differentials of `R`
over `U` is then *equal* to the pullback along the target morphism of the conormal sheaf of the
identity section, not merely a quotient of it.

Flatness of `s` makes division flat, by
`Stacks.Groupoids.GroupoidScheme.flat_divide`: division is a base change of the target morphism,
which is flat with the source morphism because the inverse is an isomorphism. The map of conormal
sheaves of the cartesian square is then an isomorphism by the flat half of
[Stacks Project, Tag 0473], and so is the comparison of [Stacks Project, Tag 08S2]. -/
@[stacks 04R9 "an isomorphism when the source morphism is flat"]
theorem isIso_conormalToDifferentials [Flat G.source.left] :
    IsIso G.conormalToDifferentials := by
  have := G.flat_divide
  have h1 : IsIso (Stacks.Immersion.immersionConormalSheafMap
      (pullback.diagonal G.source.left) G.identity.left G.target.left G.divide
      (Stacks.Immersion.toShHom_square G.isPullback_diagonal_divide.w)) :=
    Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat
      (pullback.diagonal G.source.left) G.identity.left G.target.left G.divide
      G.isPullback_diagonal_divide
  have h2 : IsIso (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal
      G.source.left).inv := Iso.isIso_inv _
  rw [conormalToDifferentials]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

/-! ### Division of arrows with a common target, and the differentials of the target -/

/-- Division of two arrows with a common target, as a morphism of schemes over `S` out of their
fibre square: the pair `(α, β)` goes to `α⁻¹ ∘ β`. -/
@[implicit_reducible]
def divideTargetPair : pullback G.target G.target ⟶ G.arrows :=
  G.compose (pullback.fst G.target G.target ≫ G.inverse)
    (pullback.snd G.target G.target)
    (by rw [Category.assoc, G.source_inverse]; exact pullback.condition)

/-- Division of the two components of a generalized point of the fibre square. -/
private theorem compose_eq_comp_divideTargetPair {T : Over S} (p : T ⟶ pullback G.target G.target)
    (w : ((p ≫ pullback.fst G.target G.target) ≫ G.inverse) ≫ G.source =
      (p ≫ pullback.snd G.target G.target) ≫ G.target) :
    G.compose ((p ≫ pullback.fst G.target G.target) ≫ G.inverse)
      (p ≫ pullback.snd G.target G.target) w = p ≫ G.divideTargetPair := by
  have w' : (p ≫ (pullback.fst G.target G.target ≫ G.inverse)) ≫ G.source =
      (p ≫ pullback.snd G.target G.target) ≫ G.target := by
    simpa only [Category.assoc] using w
  exact (groupoidCompose_arrow_eq _ _ _ _ w w' (Category.assoc _ _ _) rfl).trans
    (groupoidCompose_precomp G p _ _
      ((G.comp_inverse_comp_source _).trans pullback.condition) w')

/-- Dividing an arrow by itself on the other side gives the identity arrow at its source. -/
theorem diagonal_comp_divideTargetPair :
    pullback.diagonal G.target ≫ G.divideTargetPair = G.source ≫ G.identity := by
  have hw : ((𝟙 G.arrows) ≫ G.inverse) ≫ G.source = (𝟙 G.arrows) ≫ G.target := by
    rw [Category.assoc, G.source_inverse]
  have w' : ((pullback.diagonal G.target ≫ pullback.fst G.target G.target) ≫ G.inverse) ≫
      G.source = (pullback.diagonal G.target ≫ pullback.snd G.target G.target) ≫ G.target := by
    rw [pullback.diagonal_fst, pullback.diagonal_snd]
    exact hw
  calc pullback.diagonal G.target ≫ G.divideTargetPair
      = G.compose ((pullback.diagonal G.target ≫ pullback.fst G.target G.target) ≫ G.inverse)
          (pullback.diagonal G.target ≫ pullback.snd G.target G.target) w' :=
        (G.compose_eq_comp_divideTargetPair _ w').symm
    _ = G.compose ((𝟙 G.arrows) ≫ G.inverse) (𝟙 G.arrows) hw :=
        groupoidCompose_arrow_eq _ _ _ _ w' hw (by rw [pullback.diagonal_fst])
          (pullback.diagonal_snd _)
    _ = G.source ≫ G.identity :=
        (G.left_inverse G.arrows (𝟙 G.arrows) hw).trans (Category.id_comp _)

/-- Cancelling `y` against `y⁻¹` on the left: `y ∘ (y⁻¹ ∘ x) = x` for arrows with a common
target. -/
private theorem compose_inverse_comp_compose {T : Over S} (y x : T ⟶ G.arrows)
    (w : (y ≫ G.inverse) ≫ G.source = x ≫ G.target)
    (w₂ : y ≫ G.source = G.compose (y ≫ G.inverse) x w ≫ G.target) :
    G.compose y (G.compose (y ≫ G.inverse) x w) w₂ = x := by
  have hab : y ≫ G.target = x ≫ G.target := (G.comp_inverse_comp_source y).symm.trans w
  have wai : y ≫ G.source = (y ≫ G.inverse) ≫ G.target := (G.comp_inverse_comp_target y).symm
  have w₁ : G.compose y (y ≫ G.inverse) wai ≫ G.source = x ≫ G.target :=
    ((groupoidCompose_source G y (y ≫ G.inverse) wai).trans
      (G.comp_inverse_comp_source y)).trans hab
  have w₅ : (x ≫ G.target ≫ G.identity) ≫ G.source = x ≫ G.target := by
    rw [Category.assoc, Category.assoc, G.source_identity, Category.comp_id]
  have h6 : y ≫ G.target ≫ G.identity = x ≫ G.target ≫ G.identity := by
    rw [← Category.assoc, hab, Category.assoc]
  calc G.compose y (G.compose (y ≫ G.inverse) x w) w₂
      = G.compose (G.compose y (y ≫ G.inverse) wai) x w₁ :=
        (groupoidCompose_assoc G y (y ≫ G.inverse) x wai w w₁ w₂).symm
    _ = G.compose (x ≫ G.target ≫ G.identity) x w₅ :=
        groupoidCompose_arrow_eq _ _ _ _ w₁ w₅ ((G.right_inverse T y wai).trans h6) rfl
    _ = x := G.left_identity T x w₅

/-- **Two arrows with a common target whose quotient is an identity arrow are equal**, and the
identity arrow is then the one at their common source. On generalized points: if
`α⁻¹ ∘ β = e(x)` then `α = β` and `x = s(α)`. -/
theorem eq_of_inverse_compose_eq_identity {T : Over S} (a b : T ⟶ G.arrows)
    (q : T ⟶ G.objects) (w : (a ≫ G.inverse) ≫ G.source = b ≫ G.target)
    (h : G.compose (a ≫ G.inverse) b w = q ≫ G.identity) :
    a = b ∧ a ≫ G.source = q := by
  have hqa : a ≫ G.source = q := by
    have h2 := congrArg (fun z : T ⟶ G.arrows => z ≫ G.target) h
    simpa only [groupoidCompose_target, Category.assoc, G.target_inverse,
      G.target_identity, Category.comp_id] using h2
  refine ⟨?_, hqa⟩
  have w₂ : a ≫ G.source = G.compose (a ≫ G.inverse) b w ≫ G.target :=
    (G.comp_inverse_comp_target a).symm.trans
      (groupoidCompose_target G (a ≫ G.inverse) b w).symm
  have w₃ : a ≫ G.source = (a ≫ G.source ≫ G.identity) ≫ G.target := by
    rw [Category.assoc, Category.assoc, G.target_identity, Category.comp_id]
  have h5 : q ≫ G.identity = a ≫ G.source ≫ G.identity := by
    rw [← hqa, Category.assoc]
  calc a = G.compose a (G.compose (a ≫ G.inverse) b w) w₂ :=
        ((groupoidCompose_arrow_eq a a (G.compose (a ≫ G.inverse) b w)
          (a ≫ G.source ≫ G.identity) w₂ w₃ rfl (h.trans h5)).trans
            (G.right_identity T a w₃)).symm
    _ = b := G.compose_inverse_comp_compose a b w w₂

/-- The previous lemma read at a morphism into the fibre square of the target morphism with
itself. -/
private theorem eq_of_comp_divideTargetPair {T : Over S} (p : T ⟶ pullback G.target G.target)
    (q : T ⟶ G.objects) (hp : p ≫ G.divideTargetPair = q ≫ G.identity) :
    p ≫ pullback.fst G.target G.target = p ≫ pullback.snd G.target G.target ∧
      (p ≫ pullback.fst G.target G.target) ≫ G.source = q := by
  have hab : (p ≫ pullback.fst G.target G.target) ≫ G.target =
      (p ≫ pullback.snd G.target G.target) ≫ G.target := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have w := (G.comp_inverse_comp_source (p ≫ pullback.fst G.target G.target)).trans hab
  exact G.eq_of_inverse_compose_eq_identity _ _ q w
    ((G.compose_eq_comp_divideTargetPair p w).trans hp)

/-- **The square formed by the diagonal of the target, the source, division and the identity
section is cartesian**, in schemes over `S`. -/
@[sga "3 VIB 5.1" "more general"]
theorem isPullback_diagonal_divideTargetPair :
    IsPullback (pullback.diagonal G.target) G.source G.divideTargetPair G.identity := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk G.diagonal_comp_divideTargetPair
    (fun c => c.fst ≫ pullback.fst G.target G.target) (fun c => ?_) (fun c => ?_)
    (fun c m h₁ _ => ?_))
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
      exact (G.eq_of_comp_divideTargetPair c.fst c.snd c.condition).1
  · exact (G.eq_of_comp_divideTargetPair c.fst c.snd c.condition).2
  · rw [← h₁, Category.assoc, pullback.diagonal_fst, Category.comp_id]

/-- The fibre square of the target morphism with itself, formed in schemes over `S`, is a fibre
square of the underlying morphism of schemes with itself. -/
theorem isPullback_targetPair_left :
    IsPullback (pullback.fst G.target G.target).left (pullback.snd G.target G.target).left
      G.target.left G.target.left := by
  simpa using (IsPullback.of_hasPullback G.target G.target).map (Over.forget S)

/-- The comparison of the fibre square of the target morphism with itself formed in schemes over
`S` with Mathlib's chosen pullback of the underlying morphism with itself. -/
def targetPairIso :
    (pullback G.target G.target).left ≅ pullback G.target.left G.target.left :=
  G.isPullback_targetPair_left.isoPullback

/-- Division of two arrows with a common target, as a morphism of schemes out of the pullback of
the target morphism with itself: the pair `(α, β)` goes to `α⁻¹ ∘ β`. -/
def divideTarget : pullback G.target.left G.target.left ⟶ G.arrows.left :=
  G.targetPairIso.inv ≫ G.divideTargetPair.left

/-- **The square formed by the diagonal of the target, the source, division and the identity
section is cartesian**, in schemes. -/
@[sga "3 VIB 5.1" "more general"]
theorem isPullback_diagonal_divideTarget :
    IsPullback (pullback.diagonal G.target.left) G.source.left G.divideTarget
      G.identity.left := by
  have hsq : IsPullback (pullback.diagonal G.target).left G.source.left
      G.divideTargetPair.left G.identity.left := by
    simpa using G.isPullback_diagonal_divideTargetPair.map (Over.forget S)
  refine hsq.of_iso (Iso.refl _) G.targetPairIso (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.id_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, targetPairIso, IsPullback.isoPullback_hom_fst, ← Over.comp_left,
        pullback.diagonal_fst, Over.id_left, pullback.diagonal_fst]
    · rw [Category.assoc, targetPairIso, IsPullback.isoPullback_hom_snd, ← Over.comp_left,
        pullback.diagonal_snd, Over.id_left, pullback.diagonal_snd]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Category.comp_id, divideTarget, Iso.hom_inv_id_assoc]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- **[Stacks Project, Tag 04R9]: the canonical map `s^* 𝒞_{U/R} ⟶ Ω_{R/U}`**, with `R` over `U`
via `t`. This is the reading of the tag in which the differentials are those of the target
morphism; it is the previous map pulled back along the inverse, and is built here the same way,
from the cartesian square
`Stacks.Groupoids.GroupoidScheme.isPullback_diagonal_divideTarget` and the isomorphism of
[Stacks Project, Tag 08S2]. -/
@[stacks 04R9 "the canonical map for the differentials of the target"]
def targetConormalToDifferentials :
    (RingedSpaceModuleAdjunction.modulePullback G.source.left.toLRSHom.toShHom).obj
        (Stacks.Conormal.conormalSheaf G.identity.left) ⟶
      Scheme.Hom.relativeDifferentials G.target.left :=
  Stacks.Immersion.immersionConormalSheafMap (pullback.diagonal G.target.left)
      G.identity.left G.source.left G.divideTarget
      (Stacks.Immersion.toShHom_square G.isPullback_diagonal_divideTarget.w) ≫
    (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal G.target.left).inv

/-- **[Stacks Project, Tag 04R9]: the canonical map `s^* 𝒞_{U/R} ⟶ Ω_{R/U}` is surjective**, with
`R` over `U` via `t`. The sheaf of differentials of `R` seen as a scheme over `U` via the target
morphism is a quotient of the pullback along the source morphism of the conormal sheaf of the
identity section. -/
@[stacks 04R9 "the canonical surjection for the differentials of the target"]
theorem epi_targetConormalToDifferentials : Epi G.targetConormalToDifferentials := by
  have h := Stacks.Immersion.epi_immersionConormalSheafMap (pullback.diagonal G.target.left)
    G.identity.left G.source.left G.divideTarget G.isPullback_diagonal_divideTarget
  have h2 : Epi (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal
      G.target.left).inv := @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)
  exact epi_comp' h h2


/-! ### Division on the other side is a base change, and the flatness clause there -/

/-- **Division of arrows with a common target is a base change of the source morphism along the
target morphism**, in schemes over `S`: the square
```
R ×_{t, U, t} R --pr₀--→ R
|                        |
γ'                       s
↓                        ↓
R -------t-------------→ U
```
is cartesian, where `γ'` is `(α, β) ↦ α⁻¹ ∘ β`. On generalized points, a pair `(δ, α)` with
`t(δ) = s(α)` comes from the unique pair `(α, α ∘ δ)` of arrows with a common target. -/
theorem isPullback_divideTargetPair_fst :
    IsPullback G.divideTargetPair (pullback.fst G.target G.target) G.target G.source := by
  have hw : G.divideTargetPair ≫ G.target = pullback.fst G.target G.target ≫ G.source :=
    (groupoidCompose_target G (pullback.fst G.target G.target ≫ G.inverse)
        (pullback.snd G.target G.target)
        ((G.comp_inverse_comp_source _).trans pullback.condition)).trans
      (by rw [Category.assoc, G.target_inverse])
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun c => pullback.lift c.snd (G.compose c.snd c.fst c.condition.symm)
      (groupoidCompose_target G c.snd c.fst c.condition.symm).symm) (fun c => ?_) (fun c => ?_)
    (fun c m h₁ h₂ => ?_))
  · -- the lift divides back to the first leg of the cone
    have wli : (c.snd ≫ G.inverse) ≫ G.source = c.snd ≫ G.target :=
      G.comp_inverse_comp_source _
    have w₁ : (c.snd ≫ G.inverse) ≫ G.source =
        G.compose c.snd c.fst c.condition.symm ≫ G.target :=
      wli.trans (groupoidCompose_target G c.snd c.fst c.condition.symm).symm
    have w₂ : G.compose (c.snd ≫ G.inverse) c.snd wli ≫ G.source = c.fst ≫ G.target :=
      (groupoidCompose_source G (c.snd ≫ G.inverse) c.snd wli).trans c.condition.symm
    have w₃ : (c.fst ≫ G.target ≫ G.identity) ≫ G.source = c.fst ≫ G.target := by
      simp only [Category.assoc, G.source_identity, Category.comp_id]
    have hinv : G.compose (c.snd ≫ G.inverse) c.snd wli = c.fst ≫ G.target ≫ G.identity :=
      (G.left_inverse _ c.snd wli).trans (by rw [← Category.assoc, ← c.condition, Category.assoc])
    refine (G.compose_eq_comp_divideTargetPair _
      (by rw [pullback.lift_fst, pullback.lift_snd]; exact w₁)).symm.trans ?_
    calc _ = G.compose (c.snd ≫ G.inverse) (G.compose c.snd c.fst c.condition.symm) w₁ :=
          groupoidCompose_arrow_eq _ _ _ _ _ w₁ (by rw [pullback.lift_fst])
            (pullback.lift_snd _ _ _)
      _ = G.compose (G.compose (c.snd ≫ G.inverse) c.snd wli) c.fst w₂ :=
          (groupoidCompose_assoc G (c.snd ≫ G.inverse) c.snd c.fst wli c.condition.symm
            w₂ w₁).symm
      _ = c.fst := (groupoidCompose_arrow_eq _ _ _ _ w₂ w₃ hinv rfl).trans
          (G.left_identity _ c.fst w₃)
  · exact pullback.lift_fst _ _ _
  · -- the lift is the only such morphism
    have hcondT : c.snd ≫ G.target = (m ≫ pullback.snd G.target G.target) ≫ G.target := by
      rw [← h₂, Category.assoc, Category.assoc, pullback.condition]
    have wβ : (c.snd ≫ G.inverse) ≫ G.source =
        (m ≫ pullback.snd G.target G.target) ≫ G.target :=
      (G.comp_inverse_comp_source c.snd).trans hcondT
    have w₅ : c.snd ≫ G.source =
        G.compose (c.snd ≫ G.inverse) (m ≫ pullback.snd G.target G.target) wβ ≫ G.target :=
      (G.comp_inverse_comp_target c.snd).symm.trans
        (groupoidCompose_target G (c.snd ≫ G.inverse) (m ≫ pullback.snd G.target G.target) wβ).symm
    have wm : ((m ≫ pullback.fst G.target G.target) ≫ G.inverse) ≫ G.source =
        (m ≫ pullback.snd G.target G.target) ≫ G.target := by
      rw [h₂]
      exact wβ
    have hm : G.compose (c.snd ≫ G.inverse) (m ≫ pullback.snd G.target G.target) wβ = c.fst :=
      ((groupoidCompose_arrow_eq _ _ _ _ wβ wm (by rw [h₂]) rfl).trans
        (G.compose_eq_comp_divideTargetPair m wm)).trans h₁
    refine pullback.hom_ext (h₂.trans (pullback.lift_fst _ _ _).symm) ?_
    refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
    exact (G.compose_inverse_comp_compose c.snd _ wβ w₅).symm.trans
      (groupoidCompose_arrow_eq _ _ _ _ w₅ c.condition.symm rfl hm)

/-- **Division of arrows with a common target is a base change of the source morphism**, in
schemes. -/
theorem isPullback_divideTarget_fst :
    IsPullback G.divideTarget (pullback.fst G.target.left G.target.left) G.target.left
      G.source.left := by
  have hsq : IsPullback G.divideTargetPair.left (pullback.fst G.target G.target).left
      G.target.left G.source.left := by
    simpa using G.isPullback_divideTargetPair_fst.map (Over.forget S)
  refine hsq.of_iso G.targetPairIso (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, divideTarget, Iso.hom_inv_id_assoc]
  · rw [Iso.refl_hom, Category.comp_id, targetPairIso, IsPullback.isoPullback_hom_fst]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- **Division of arrows with a common target is flat when the source morphism is**, being a base
change of the source morphism. -/
theorem flat_divideTarget [Flat G.source.left] : Flat G.divideTarget :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback G.isPullback_divideTarget_fst.flip
    inferInstance

/-- **[Stacks Project, Tag 04R9]: the canonical map `s^* 𝒞_{U/R} ⟶ Ω_{R/U}` is an isomorphism
when the source morphism is flat**, with `R` over `U` via `t`. This is the second reading of the
tag, in which the differentials are those of the target morphism.

Here flatness of `s` is used directly: division on this side is a base change of the source
morphism, by `Stacks.Groupoids.GroupoidScheme.isPullback_divideTarget_fst`. -/
@[stacks 04R9 "an isomorphism for the differentials of the target when the source map is flat"]
theorem isIso_targetConormalToDifferentials [Flat G.source.left] :
    IsIso G.targetConormalToDifferentials := by
  have := G.flat_divideTarget
  have h1 : IsIso (Stacks.Immersion.immersionConormalSheafMap
      (pullback.diagonal G.target.left) G.identity.left G.source.left G.divideTarget
      (Stacks.Immersion.toShHom_square G.isPullback_diagonal_divideTarget.w)) :=
    Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat
      (pullback.diagonal G.target.left) G.identity.left G.source.left G.divideTarget
      G.isPullback_diagonal_divideTarget
  have h2 : IsIso (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal
      G.target.left).inv := Iso.isIso_inv _
  rw [targetConormalToDifferentials]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

end Stacks.Groupoids.GroupoidScheme

end
