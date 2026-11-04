module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismEndpoints
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSequenceTerms
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismEndpointsSupplied

/-!
# The six-term exact sequence of a deformation of a morphism of schemes

Let `f : X ⟶ Y` be a morphism of schemes over a field `k`. This file assembles the exact
sequence of [Stacks Project, Tag 0E3V] out of the arrows built elsewhere.

## Main results

* `Deformation.exact_triple_of_simplyTransitiveVAdd`: **Tag 0E3V, exactness at the second, third
  and fourth spots, as torsor algebra.** The three interior spots of the source's sequence are
  the three computations its proof performs with the simply transitive action of
  `Der_k(𝒪_Y, f_*𝒪_X)` on the lifts of `f` to the trivial first-order deformations of its
  endpoints, and nothing else. Stated for an abstract simply transitive action, they reduce to
  exactly three geometric inputs: which pairs of infinitesimal automorphisms of the endpoints
  fix the trivial lift, when two lifts give isomorphic first-order deformations of `f`, and
  which first-order deformations of `f` have both endpoints trivial.
* `Deformation.map_add_of_simplyTransitiveVAdd`: the arrow `b` of the source's sequence is
  additive as soon as the conjugation action and the translation action commute.
* `Deformation.exact_triple_of_simplyTransitive` and
  `Deformation.map_add_of_simplyTransitive`: the same two, with both actions given as bare
  functions with their laws, which is the shape the simple transitivity clause of
  [Stacks Project, Tag 0CK2] delivers.
* `Deformation.map_smul_of_simplyTransitive`: the arrow `b` is homogeneous as soon as scaling the
  conjugating automorphism scales the derivation it displaces the base lift by. That hypothesis
  is the whole content, and it is not formal from the two actions commuting — the scalar action
  on the conjugating side rescales the infinitesimal coordinate of the base, which the action on
  lifts does not see.
* `Deformation.Examples.exact_schemeMorphismTangentPair_obstruction`: **Tag 0E3V, exactness at
  the fifth spot `T(Def_X × Def_Y)`**, from the obstruction map of the last paragraph of the
  source's proof, taken into the group `Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k M)` twisted by the
  coefficient module `M` of the tangent spaces, the source's sequence being the case `M = k`.
  A map out of `T(Def_X × Def_Y)` whose zero locus is the set of pairs of
  first-order deformations of the endpoints along which `f` deforms is exact with the arrow
  `T Def_{X ⟶ Y} → T(Def_X × Def_Y)`: the image of that arrow is described by
  `Deformation.Examples.exists_schemeMorphismTangentPair_eq_iff`, and every element of
  `T Def_X × T Def_Y` is a pair of classes of objects of the two fibres by
  `Deformation.tangentClassAt_surjective`.

## Implementation notes

The obstruction map is a parameter here, pinned by its zero locus rather than by a recipe. Only
the `Zero` of the target is used, so the parameter is a bare function; the `k`-linearity it
carries in the source's sequence is imposed where the whole sequence is assembled, not here.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Deformation

/-! ### The three interior spots as torsor algebra -/

section Torsor

universe uA uG uD uT uE uL uk

/-- Exactness at the second spot, as torsor algebra: `b g` vanishes exactly when `g` fixes the
base point. -/
private theorem exact_of_fixes_base_point
    {A : Type uA} {G : Type uG} {D : Type uD} {L : Type uL} [AddMonoid D]
    (act : D → L → L) (gact : G → L → L) (ℓ₀ : L)
    (hact0 : ∀ ℓ : L, act 0 ℓ = ℓ)
    (htrans : ∀ ℓ : L, ∃! θ : D, act θ ℓ₀ = ℓ)
    (a : A → G) (b : G → D)
    (hb : ∀ g : G, act (b g) ℓ₀ = gact g ℓ₀)
    (ha : ∀ g : G, (∃ x, a x = g) ↔ gact g ℓ₀ = ℓ₀) :
    Function.Exact a b := by
  -- The base point is the orbit of `0`, so simple transitivity pins `0` as the only element
  -- of `D` fixing it.
  have hzero : ∀ θ : D, act θ ℓ₀ = ℓ₀ ↔ θ = 0 := fun θ =>
    ⟨fun hθ => (htrans ℓ₀).unique hθ (hact0 ℓ₀), fun hθ => by rw [hθ, hact0 ℓ₀]⟩
  exact fun g => ((hzero (b g)).symm.trans (by rw [hb g])).trans (ha g).symm

/-- **The second, third and fourth spots of [Stacks Project, Tag 0E3V], as torsor algebra.**

In the source's proof the three interior spots of the sequence

`Inf(𝒲) → Inf(ℋ) ⊕ Inf(𝒢) → D → T𝒲 → Tℋ ⊕ T𝒢`

are three computations with one simply transitive action: `D` acts simply transitively on a set
`L` of lifts, a second group `G` acts on `L` as well, `b` is the unique element of `D` carrying
the base point `ℓ₀` where `G` carries it, and `δ` is the class in `T` of the lift that `D`
produces from `ℓ₀`. Given that, exactness at the three spots needs exactly three inputs:

* `ha`: an element of `G` is in the image of `a` exactly when it fixes the base point. (For
  Tag 0E3V: a pair of infinitesimal automorphisms of `X'` and `Y'` comes from an infinitesimal
  automorphism of `f'` exactly when it commutes with `f'`.)
* `hcls`: the class of a lift vanishes exactly when `G` carries the base point to it. (For
  Tag 0E3V: `(f_ε : X' → Y')` is isomorphic to the trivial deformation exactly when
  `f_ε = β⁻¹ ∘ f' ∘ α` for some pair `(α, β)`.)
* `hc`: an element of `T` is killed by `c` exactly when it is the class of a lift. (For
  Tag 0E3V: a first-order deformation of `f` dies in `T(Def_X × Def_Y)` exactly when both its
  endpoints are trivial, and then it is a lift `X' ⟶ Y'`.)

Only the base point's orbit is used, so the hypothesis on `D` is simple transitivity based
there, and `G` needs no group structure beyond an action. -/
theorem exact_triple_of_simplyTransitiveVAdd
    {A : Type uA} {G : Type uG} {D : Type uD} {T : Type uT} {E : Type uE} {L : Type uL}
    [AddMonoid D] [AddAction D L] [Zero T] [Zero E] [VAdd G L]
    (ℓ₀ : L) (htrans : ∀ ℓ : L, ∃! θ : D, θ +ᵥ ℓ₀ = ℓ)
    (a : A → G) (b : G → D) (cls : L → T) (δ : D → T) (c : T → E)
    (hb : ∀ g : G, b g +ᵥ ℓ₀ = g +ᵥ ℓ₀)
    (ha : ∀ g : G, (∃ x, a x = g) ↔ g +ᵥ ℓ₀ = ℓ₀)
    (hδ : ∀ θ : D, δ θ = cls (θ +ᵥ ℓ₀))
    (hcls : ∀ θ : D, cls (θ +ᵥ ℓ₀) = 0 ↔ ∃ g : G, θ +ᵥ ℓ₀ = g +ᵥ ℓ₀)
    (hc : ∀ t : T, c t = 0 ↔ ∃ ℓ : L, cls ℓ = t) :
    Function.Exact a b ∧ Function.Exact b δ ∧ Function.Exact δ c := by
  refine ⟨exact_of_fixes_base_point (· +ᵥ ·) (· +ᵥ ·) ℓ₀ (zero_vadd D) htrans a b hb ha,
    fun θ => ?_, fun t => ?_⟩
  · -- Exactness at `D`: `δ θ = 0` says `G` carries the base point to `θ +ᵥ ℓ₀`.
    refine (hδ θ ▸ hcls θ).trans ⟨fun ⟨g, hg⟩ => ?_, fun ⟨g, hg⟩ => ⟨g, by rw [← hg, hb g]⟩⟩
    exact ⟨g, ((htrans _).unique (hb g) hg)⟩
  · -- Exactness at `T𝒲`: the image of `δ` is the set of classes of lifts, because every lift
    -- is the orbit of exactly one element of `D`.
    refine (hc t).trans ⟨fun ⟨ℓ, hℓ⟩ => ?_, fun ⟨θ, hθ⟩ => ⟨θ +ᵥ ℓ₀, by rw [← hδ θ, hθ]⟩⟩
    obtain ⟨θ, hθ, _⟩ := htrans ℓ
    exact ⟨θ, by rw [hδ θ, hθ, hℓ]⟩

/-- **The arrow `b` of [Stacks Project, Tag 0E3V] is additive.** With `b g` pinned as the unique
element of `D` carrying the base point where `g` carries it, additivity of `b` is formal from two
facts about the two actions: that `G` acts (so `(g + g') +ᵥ ℓ = g +ᵥ (g' +ᵥ ℓ)`) and that the two
actions **commute**.

For Tag 0E3V the second is the statement that conjugating a lift by a pair of infinitesimal
automorphisms and translating it by a derivation are independent operations, which holds because
both perturbations are of order `ε` and `ε² = 0`. It is the only input additivity needs; no
scalar action is used. -/
theorem map_add_of_simplyTransitiveVAdd
    {G : Type uG} {D : Type uD} {L : Type uL}
    [AddCommMonoid D] [AddAction D L] [AddMonoid G] [AddAction G L]
    (ℓ₀ : L) (htrans : ∀ ℓ : L, ∃! θ : D, θ +ᵥ ℓ₀ = ℓ) (b : G → D)
    (hb : ∀ g : G, b g +ᵥ ℓ₀ = g +ᵥ ℓ₀)
    (hcomm : ∀ (θ : D) (g : G) (ℓ : L), g +ᵥ (θ +ᵥ ℓ) = θ +ᵥ (g +ᵥ ℓ))
    (g g' : G) : b (g + g') = b g + b g' := by
  refine (htrans _).unique (hb (g + g')) ?_
  calc (b g + b g') +ᵥ ℓ₀ = b g' +ᵥ (b g +ᵥ ℓ₀) := by rw [add_comm, add_vadd]
    _ = b g' +ᵥ (g +ᵥ ℓ₀) := by rw [hb g]
    _ = g +ᵥ (b g' +ᵥ ℓ₀) := (hcomm (b g') g ℓ₀).symm
    _ = g +ᵥ (g' +ᵥ ℓ₀) := by rw [hb g']
    _ = (g + g') +ᵥ ℓ₀ := (add_vadd g g' ℓ₀).symm

/-- **The three interior spots, with both actions given as bare functions.** This is
`Deformation.exact_triple_of_simplyTransitiveVAdd` in the shape the geometry delivers: the
simple transitivity clause of [Stacks Project, Tag 0CK2] produces an action as an *existential
over a function* together with its two laws, not as an `AddAction` instance, so the instance is
built here rather than at every use site. -/
theorem exact_triple_of_simplyTransitive
    {A : Type uA} {G : Type uG} {D : Type uD} {T : Type uT} {E : Type uE} {L : Type uL}
    [AddMonoid D] [Zero T] [Zero E]
    (act : D → L → L) (gact : G → L → L) (ℓ₀ : L)
    (hact0 : ∀ ℓ : L, act 0 ℓ = ℓ)
    (hactadd : ∀ (θ η : D) (ℓ : L), act (θ + η) ℓ = act θ (act η ℓ))
    (htrans : ∀ ℓ : L, ∃! θ : D, act θ ℓ₀ = ℓ)
    (a : A → G) (b : G → D) (cls : L → T) (δ : D → T) (c : T → E)
    (hb : ∀ g : G, act (b g) ℓ₀ = gact g ℓ₀)
    (ha : ∀ g : G, (∃ x, a x = g) ↔ gact g ℓ₀ = ℓ₀)
    (hδ : ∀ θ : D, δ θ = cls (act θ ℓ₀))
    (hcls : ∀ θ : D, cls (act θ ℓ₀) = 0 ↔ ∃ g : G, act θ ℓ₀ = gact g ℓ₀)
    (hc : ∀ t : T, c t = 0 ↔ ∃ ℓ : L, cls ℓ = t) :
    Function.Exact a b ∧ Function.Exact b δ ∧ Function.Exact δ c :=
  let : AddAction D L := { vadd := act, zero_vadd := hact0, add_vadd := hactadd }
  let : VAdd G L := ⟨gact⟩
  exact_triple_of_simplyTransitiveVAdd ℓ₀ htrans a b cls δ c hb ha hδ hcls hc

/-- **The second spot alone, with both actions given as bare functions.** The first conjunct of
`Deformation.exact_triple_of_simplyTransitive`, with the three inputs that only the second and
third conjuncts use — the class map, the two arrows out of it and the two `Zero`s — dropped.

Exactness at the second spot is the statement that `b g` vanishes exactly when `g` comes from
`a`, and `b g` vanishes exactly when `g` fixes the base point, because the translation carrying
the base point where `g` carries it is unique. Neither the class of a lift nor the term the
sequence continues into enters. -/
theorem exact_fst_of_simplyTransitive
    {A : Type uA} {G : Type uG} {D : Type uD} {L : Type uL} [AddMonoid D]
    (act : D → L → L) (gact : G → L → L) (ℓ₀ : L)
    (hact0 : ∀ ℓ : L, act 0 ℓ = ℓ)
    (htrans : ∀ ℓ : L, ∃! θ : D, act θ ℓ₀ = ℓ)
    (a : A → G) (b : G → D)
    (hb : ∀ g : G, act (b g) ℓ₀ = gact g ℓ₀)
    (ha : ∀ g : G, (∃ x, a x = g) ↔ gact g ℓ₀ = ℓ₀) :
    Function.Exact a b :=
  exact_of_fixes_base_point act gact ℓ₀ hact0 htrans a b hb ha

/-- **Additivity of `b`, with both actions given as bare functions.** The companion of
`Deformation.map_add_of_simplyTransitiveVAdd` in the shape the geometry delivers. -/
theorem map_add_of_simplyTransitive
    {G : Type uG} {D : Type uD} {L : Type uL} [AddCommMonoid D] [AddMonoid G]
    (act : D → L → L) (gact : G → L → L) (ℓ₀ : L)
    (hact0 : ∀ ℓ : L, act 0 ℓ = ℓ)
    (hactadd : ∀ (θ η : D) (ℓ : L), act (θ + η) ℓ = act θ (act η ℓ))
    (hgact0 : ∀ ℓ : L, gact 0 ℓ = ℓ)
    (hgactadd : ∀ (g g' : G) (ℓ : L), gact (g + g') ℓ = gact g (gact g' ℓ))
    (htrans : ∀ ℓ : L, ∃! θ : D, act θ ℓ₀ = ℓ) (b : G → D)
    (hb : ∀ g : G, act (b g) ℓ₀ = gact g ℓ₀)
    (hcomm : ∀ (θ : D) (g : G) (ℓ : L), gact g (act θ ℓ) = act θ (gact g ℓ))
    (g g' : G) : b (g + g') = b g + b g' :=
  let : AddAction D L := { vadd := act, zero_vadd := hact0, add_vadd := hactadd }
  let : AddAction G L := { vadd := gact, zero_vadd := hgact0, add_vadd := hgactadd }
  map_add_of_simplyTransitiveVAdd ℓ₀ htrans b hb hcomm g g'

/-- **Homogeneity of the arrow `b` of [Stacks Project, Tag 0E3V]**, with both actions given as
bare functions, as the simple transitivity clause of [Stacks Project, Tag 0CK2] delivers them.

Unlike additivity, homogeneity is *not* formal from the two perturbations commuting. Additivity
is available from `Deformation.map_add_of_simplyTransitiveVAdd` because a sum on the conjugating
side and a sum on the translating side are both built from the same binary operation on lifts, so
the two orders of perturbing agree; the scalar action on the conjugating side is of a different
nature — it rescales the infinitesimal coordinate of the base rather than composing two
perturbations — and nothing about the action on lifts sees it.

So the whole content of homogeneity is the hypothesis `hscale`: that translating the base lift by
the `c`-fold of the derivation attached to `g` carries it where conjugating by the `c`-fold of
`g` carries it. Given that, `b (c • g)` and `c • b g` are both the unique translation taking the
base lift to `gact (c • g) ℓ₀`, hence equal. For a morphism of schemes over `k`, `hscale` is the
base-change computation for the translation action along the scaling `ε ↦ cε` of the dual
numbers, which is what `Deformation.naturalLocalizedTangentModule_spec` presents the scalar
action of the `Inf` term as. -/
theorem map_smul_of_simplyTransitive
    {k : Type uk} {G : Type uG} {D : Type uD} {L : Type uL}
    [Semiring k] [AddCommMonoid D] [Module k D] [SMul k G]
    (act : D → L → L) (gact : G → L → L) (ℓ₀ : L)
    (htrans : ∀ ℓ : L, ∃! θ : D, act θ ℓ₀ = ℓ) (b : G → D)
    (hb : ∀ g : G, act (b g) ℓ₀ = gact g ℓ₀)
    (hscale : ∀ (c : k) (g : G), act (c • b g) ℓ₀ = gact (c • g) ℓ₀)
    (c : k) (g : G) : b (c • g) = c • b g := by
  exact (htrans _).unique (hb (c • g)) (hscale c g)

end Torsor

namespace Examples

section SixTerm

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-- **Stacks 0E3V, exactness at the fifth spot.** Let `ob` be a map from `T(Def_X × Def_Y)` to
`Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k M)` whose zero locus is the set of pairs of first-order
deformations of `X` and of `Y` along which `f` deforms — the obstruction map of the last
paragraph of the source's proof. Then the sequence

`T Def_{X ⟶ Y} → T(Def_X × Def_Y) → Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k M)`

is exact at its middle term.

Here the tangent spaces are taken with coefficients in a finite-dimensional `k`-vector space
`M`, i.e. over the square-zero base `k ⊕ M`, and the obstruction group is twisted to match:
the ideal sheaf of the special fibre of a deformation of `X` over that base is `𝒪_X ⊗_k M`, so
the obstruction of the source's proof lies in
`Deformation.Examples.schemeMorphismObstructionExtTwisted`. The source's own sequence is the
case `M = k`, where that group is canonically
`Deformation.Examples.schemeMorphismObstructionExt`, the untwisted
`Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X)`; that identification is not built here.

Both inputs are already available: every element of `T Def_X × T Def_Y` is a pair of classes of
objects of the two fibres over the square-zero extension
(`Deformation.tangentClassAt_surjective`), and the image of the arrow out of `T Def_{X ⟶ Y}`
consists exactly of the pairs along which `f` deforms
(`Deformation.Examples.exists_schemeMorphismTangentPair_eq_iff`). -/
theorem exact_schemeMorphismTangentPair_obstruction
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (hX : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hY : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
    (M : FGModuleCat.{u} k)
    (ob : ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
          (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX M) ×
        ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
          (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) hY M) →
      schemeMorphismObstructionExtTwisted f pY M)
    (hob : ∀ (xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
          ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
        (yε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
          ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)),
      ob (tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
            (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX M xε,
          tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
            (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) hY M yε) = 0 ↔
        ∃ mε : (schemeMorphismDeformationCategoryProjection f pX pY hf).Fiber
            ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M),
          IsIsomorphic ((fiberFunctor (schemeMorphismSourceBased f pX pY hf)
              ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).obj mε) xε ∧
            IsIsomorphic ((fiberFunctor (schemeMorphismTargetBased f pX pY hf)
              ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).obj mε) yε) :
    Function.Exact (schemeMorphismTangentPair f pX pY hf hM hX hY M) ob := by
  rintro ⟨zx, zy⟩
  obtain ⟨xε, rfl⟩ := tangentClassAt_surjective.{u, u, u} (BasedCategory.ofFunctor
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX M zx
  obtain ⟨yε, rfl⟩ := tangentClassAt_surjective.{u, u, u} (BasedCategory.ofFunctor
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) hY M zy
  exact (hob xε yε).trans
    (exists_schemeMorphismTangentPair_eq_iff f pX pY hf hM hX hY M xε yε).symm

end SixTerm

end Examples

end Deformation

end
