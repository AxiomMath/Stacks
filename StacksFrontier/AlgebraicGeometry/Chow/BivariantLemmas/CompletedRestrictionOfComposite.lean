module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedConstantRank

/-!
# Restriction of a completed composite

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. For `i : X ⟶ P`,
`g : P ⟶ Y` and `h : Y' ⟶ Y` locally of finite type, write `P' = P ×_Y Y'`. **Stacks 0F9Z**
restricts a bivariant class along `h`, and restriction is compatible with composition
(Stacks 0B75): `res_h(c ∘ d) = res(c) ∘ res_h(d)`, where `res(c)` is the restriction of `c` along
`P' ⟶ P`, read through the canonical isomorphism `X ×_P P' ≅ X ×_Y Y'`. This file proves that
compatibility on the completed bivariant groups of **Stacks 0FE0**.

The two sides are completed classes on the different sources `X ×_P P'` and `X ×_Y Y'`, so the
statement needs a transport of completed classes along an isomorphism `θ : A ≅ B` of sources over
the target. Reading a completed class as its tuple `(c_n)_n` of homogeneous classes, the transport
is the tuple of the transports `θ_*(c_n)`; it is again almost vanishing on each connected component
`B_j`, because `θ_*(c_n)` vanishes on `B_j` wherever `c_n` vanishes on the component of `A`
containing `θ⁻¹(B_j)`.

Finally a homogeneous class `x ∈ A^n(X ⟶ Y)`, read as a completed class, has the tuple that is `x`
in degree `n` and zero elsewhere, and its restriction is the restriction of `x`.

## Main definitions

* `Stacks.Chow.completedBivariantTransport` — the transport
  `A^*(A ⟶ W)^∧ ⟶ A^*(B ⟶ W)^∧` along an isomorphism `θ : A ≅ B` over `W`.

## Main results

* `Stacks.Chow.bivariantConnectedComponentRestriction_bivariantTransport_eq_zero` — transport
  preserves the vanishing of a class on a connected component.
* `Stacks.Chow.completedBivariantSequenceOfInvertible_completedBivariantTransport` — degree by
  degree, the transport on completions is the transport of homogeneous classes.
* `Stacks.Chow.completedBivariantRestriction_completedBivariantCompositeOfInvertible` —
  `res_h(c ∘ d) = θ_*(res(c) ∘ res_h(d))` on completions.
* `Stacks.Chow.completedBivariantSequenceOfInvertible_toCompleted` — the tuple of a homogeneous
  class read as a completed class.
* `Stacks.Chow.completedBivariantRestriction_toCompleted` — restriction commutes with reading a
  homogeneous class as a completed class.

## Implementation notes

A completed class is determined by its tuple, and a homogeneous class by its restrictions to the
connected components of its source (Stacks 0FDZ). On a connected component `X'_j` of
`X ×_Y Y'` lying over the component `X_w` of `X`, the degree `n` term of the tuple of `c ∘ d` is
the restriction of the finite sum `∑_{p ∈ s} c_p ∘ d_{n-p}` of homogeneous composites, for any
finite set `s` of degrees containing those in which `c` is nonzero on `X_w`. The restriction along
`h` of a class only depends, on `X'_j`, on the class on `X_w`, and the transport along `θ` of a
class only depends, on `X'_j`, on the class on the component of `X ×_P P'` below it. Choosing `s`
large enough for both sides, the identity is reduced to the homogeneous compatibility
`Stacks.Chow.bivariantRestriction_bivariantCompositeOfInvertible`, term by term.

## References

* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transport and restriction on a connected component -/

section Vanishing

variable (C : ChowSituation.{u}) (G : GysinSystem C) {A B W : Scheme.{u}} (sA : A ⟶ C.S)
  [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sW : W ⟶ C.S)
  [LocallyOfFiniteType sW] (v : A ⟶ W) [LocallyOfFiniteType v] (hv : v ≫ sW = sA)
  (u : B ⟶ W) [LocallyOfFiniteType u] (hu : u ≫ sW = sB) (θ : A ≅ B) (hθ : θ.hom ≫ u = v)
  [IsLocallyNoetherian A] [IsLocallyNoetherian B] [IsLocallyNoetherian W] (p : ℤ)
  (hgysO : G.IsNaturalUnderOpenImmersion) (hgys : G.IsNaturalUnderBaseChangeIso)

/-- **Transport preserves vanishing on connected components.** If the restriction (Stacks 0FDZ)
of `x ∈ A^p(A ⟶ W)` to the connected component of `A` containing `θ⁻¹(B_j)` vanishes, then so does
the restriction of its transport `θ_* x ∈ A^p(B ⟶ W)` to `B_j`: the cap operation of the latter is
that of `x` restricted to an open subscheme lying over that component, which is zero by
`Stacks.Chow.chowGroupRestrict_cap_eq_zero_of_connectedComponentRestriction_eq_zero`. -/
theorem bivariantConnectedComponentRestriction_bivariantTransport_eq_zero
    (x : BivariantClass C G sA sW v hv p) (j : _root_.ConnectedComponents B)
    (hx : bivariantConnectedComponentRestriction C G sA sW v hv p hgysO x
      (θ.inv.continuous.connectedComponentsMap j) = 0) :
    bivariantConnectedComponentRestriction C G sB sW u hu p hgysO
      (bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys x) j = 0 := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun {T} t _ k β ↦ ?_
  rw [BivariantClass.zero_cap, bivariantConnectedComponentRestriction_cap, bivariantTransport_cap,
    bivariantTransportCap_apply, chowPushforwardOfIso_hom_eq_chowGroupRestrict,
    chowGroupRestrict_comp]
  refine chowGroupRestrict_cap_eq_zero_of_connectedComponentRestriction_eq_zero C G sA sW v hv p
    hgysO x _ hx _ k _ _ _ _
    (pullback.fst (u.resConnectedComponent j) t ≫ θ.inv.resConnectedComponent j) ?_
  rw [Category.assoc, Scheme.Hom.resConnectedComponent_comp_ι, Category.assoc,
    transportPullbackIso_inv_fst, opensPullbackComparison_fst_assoc]

/-- **Transport on a connected component only sees the component below.** The restriction to the
connected component `B_j` of the transport `θ_* x` only depends on the restriction of `x` to the
connected component of `A` containing `θ⁻¹(B_j)`. -/
theorem bivariantConnectedComponentRestriction_bivariantTransport_eq_of_eq
    (x y : BivariantClass C G sA sW v hv p) (j : _root_.ConnectedComponents B)
    (hxy : bivariantConnectedComponentRestriction C G sA sW v hv p hgysO x
      (θ.inv.continuous.connectedComponentsMap j) =
      bivariantConnectedComponentRestriction C G sA sW v hv p hgysO y
        (θ.inv.continuous.connectedComponentsMap j)) :
    bivariantConnectedComponentRestriction C G sB sW u hu p hgysO
        (bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys x) j =
      bivariantConnectedComponentRestriction C G sB sW u hu p hgysO
        (bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys y) j := by
  have h0 := bivariantConnectedComponentRestriction_bivariantTransport_eq_zero C G sA sB sW v hv u
    hu θ hθ p hgysO hgys (x - y) j (by rw [map_sub, Pi.sub_apply, hxy, sub_self])
  rw [show bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys (x - y) =
      bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys x -
        bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys y from
      map_sub (bivariantTransportAddHom C G sA sB sW v hv u hu θ hθ p hgys) x y,
    map_sub, Pi.sub_apply, sub_eq_zero] at h0
  exact h0

end Vanishing

section RestrictionVanishing

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Y' : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (p : ℤ) (hgysO : G.IsNaturalUnderOpenImmersion) (h : Y' ⟶ Y) [LocallyOfFiniteType h]
  [IsLocallyNoetherian Y'] [IsLocallyNoetherian (pullback f h)]
  (hgys : G.IsNaturalUnderBaseChangeIso)

/-- **Restriction on a connected component only sees the component below.** The restriction to
a connected component `X'_j` of `X ×_Y Y'` of the restriction `res(x)` (Stacks 0F9Z) only depends
on the restriction of `x` to the connected component of `X` below `X'_j`
(`Stacks.Chow.bivariantConnectedComponentRestriction_bivariantRestriction_eq_zero`). -/
theorem bivariantConnectedComponentRestriction_bivariantRestriction_eq_of_eq
    (x y : BivariantClass C G sX sY f hf p) (j : _root_.ConnectedComponents ↥(pullback f h))
    (hxy : bivariantConnectedComponentRestriction C G sX sY f hf p hgysO x
      ((pullback.fst f h).continuous.connectedComponentsMap j) =
      bivariantConnectedComponentRestriction C G sX sY f hf p hgysO y
        ((pullback.fst f h).continuous.connectedComponentsMap j)) :
    bivariantConnectedComponentRestriction C G (pullback.fst f h ≫ sX) (h ≫ sY)
        (pullback.snd f h) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) p hgysO
        (bivariantRestriction C G sX sY f hf h p hgys x) j =
      bivariantConnectedComponentRestriction C G (pullback.fst f h ≫ sX) (h ≫ sY)
        (pullback.snd f h) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) p hgysO
        (bivariantRestriction C G sX sY f hf h p hgys y) j := by
  have h0 := bivariantConnectedComponentRestriction_bivariantRestriction_eq_zero C G sX sY f hf h p
    hgysO hgys (x - y) j (by rw [map_sub, Pi.sub_apply, hxy, sub_self])
  rw [show bivariantRestriction C G sX sY f hf h p hgys (x - y) =
      bivariantRestriction C G sX sY f hf h p hgys x -
        bivariantRestriction C G sX sY f hf h p hgys y from
      map_sub (bivariantRestrictionAddHom C G sX sY f hf h p hgys) x y,
    map_sub, Pi.sub_apply, sub_eq_zero] at h0
  exact h0

end RestrictionVanishing

/-! ### Transport on completions -/

/-- Restricting the tuple term of `c` (Stacks 0FE0) to a connected component recovers `c`. -/
private theorem restriction_completedBivariantSequenceOfInvertible (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf) (p : ℤ)
    (i : _root_.ConnectedComponents X) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f hf p
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (completedBivariantSequenceOfInvertible C sX sY f hf c p) i = c i p :=
  restriction_completedBivariantSequence C (gysinSystemOfInvertible C) sX sY f hf
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) c p i

section CompletedTransport

variable (C : ChowSituation.{u}) {A B W : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
  (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
  (v : A ⟶ W) [LocallyOfFiniteType v] (hv : v ≫ sW = sA) (u : B ⟶ W) [LocallyOfFiniteType u]
  (hu : u ≫ sW = sB) (θ : A ≅ B) (hθ : θ.hom ≫ u = v) [IsLocallyNoetherian A]
  [IsLocallyNoetherian B] [IsLocallyNoetherian W]

/-- The degreewise transport `∏_n A^n(A ⟶ W) ⟶ ∏_n A^n(B ⟶ W)` along `θ : A ≅ B` of the tuple
attached to an element of the completed group (Stacks 0FE0), at the Gysin system of the first Chern
class rule. -/
def completedBivariantTransportSequence :
    completedBivariantGroup C (gysinSystemOfInvertible C) sA sW v hv →+
      ∀ n : ℤ, BivariantClass C (gysinSystemOfInvertible C) sB sW u hu n :=
  (Pi.addMonoidHom fun n ↦ (bivariantTransportAddHom C (gysinSystemOfInvertible C) sA sB sW v hv
    u hu θ hθ n (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)).comp
      (Pi.evalAddMonoidHom _ n)).comp (completedBivariantSequenceOfInvertible C sA sW v hv)

/-- The degreewise transport of the tuple attached to an element of the completed group still
vanishes in almost all degrees on each connected component `B_j` of `B`: it vanishes wherever the
tuple vanishes on the component of `A` containing `θ⁻¹(B_j)`, by
`Stacks.Chow.bivariantConnectedComponentRestriction_bivariantTransport_eq_zero`. -/
theorem completedBivariantTransportSequence_mem
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sA sW v hv) :
    completedBivariantTransportSequence C sA sB sW v hv u hu θ hθ c ∈
      completedBivariantSubgroupOfInvertible C sB sW u hu := by
  intro j
  refine (completedBivariantSequence_mem C (gysinSystemOfInvertible C) sA sW v hv
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) c
    (θ.inv.continuous.connectedComponentsMap j)).subset fun n hn ↦ ?_
  intro hzero
  exact hn (bivariantConnectedComponentRestriction_bivariantTransport_eq_zero C
    (gysinSystemOfInvertible C) sA sB sW v hv u hu θ hθ n
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) _ j hzero)

/-- **Transport of completed classes along an isomorphism of sources.** For `v : A ⟶ W`,
`u : B ⟶ W` and an isomorphism `θ : A ≅ B` over `W`, the map
`θ_* : A^*(A ⟶ W)^∧ ⟶ A^*(B ⟶ W)^∧` of completed bivariant groups (Stacks 0FE0), at the Gysin
system of the first Chern class rule: reading an element of the completed group as the tuple
`(c_n)_n` of Stacks 0FE0, it is the tuple `(θ_* c_n)_n` of the transports
(`Stacks.Chow.bivariantTransport`), which again vanishes in almost all degrees on each connected
component. -/
def completedBivariantTransport :
    completedBivariantGroup C (gysinSystemOfInvertible C) sA sW v hv →+
      completedBivariantGroup C (gysinSystemOfInvertible C) sB sW u hu :=
  (completedBivariantGroupEquivOfInvertible C sB sW u hu).symm.toAddMonoidHom.comp
    ((completedBivariantTransportSequence C sA sB sW v hv u hu θ hθ).codRestrict _
      (completedBivariantTransportSequence_mem C sA sB sW v hv u hu θ hθ))

/-- **Transport on completions, degree by degree.** The degree `n` term of the tuple attached to
`θ_* c` (Stacks 0FE0) is the transport of the degree `n` term of the tuple attached to `c`. -/
@[simp]
theorem completedBivariantSequenceOfInvertible_completedBivariantTransport
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sA sW v hv) (n : ℤ) :
    completedBivariantSequenceOfInvertible C sB sW u hu
        (completedBivariantTransport C sA sB sW v hv u hu θ hθ c) n =
      bivariantTransport C (gysinSystemOfInvertible C) sA sB sW v hv u hu θ hθ n
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (completedBivariantSequenceOfInvertible C sA sW v hv c n) := by
  have h₁ := completedBivariantGroupEquiv_apply C (gysinSystemOfInvertible C) sB sW u hu
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C)
    (completedBivariantTransport C sA sB sW v hv u hu θ hθ c)
  have h₂ := congrArg Subtype.val ((completedBivariantGroupEquivOfInvertible C sB sW u
    hu).apply_symm_apply ⟨completedBivariantTransportSequence C sA sB sW v hv u hu θ hθ c,
      completedBivariantTransportSequence_mem C sA sB sW v hv u hu θ hθ c⟩)
  exact congrFun (h₁.symm.trans h₂) n

/-- **Transport on completions, on connected components.** On the connected component `B_j`, the
degree `n` part of `θ_* c` is the restriction (Stacks 0FDZ) to `B_j` of the transport of the degree
`n` term of the tuple attached to `c`. -/
theorem completedBivariantTransport_apply
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sA sW v hv)
    (j : _root_.ConnectedComponents B) (n : ℤ) :
    completedBivariantTransport C sA sB sW v hv u hu θ hθ c j n =
      bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sB sW u hu n
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (bivariantTransport C (gysinSystemOfInvertible C) sA sB sW v hv u hu θ hθ n
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (completedBivariantSequenceOfInvertible C sA sW v hv c n)) j := by
  rw [← completedBivariantSequenceOfInvertible_completedBivariantTransport]
  exact (restriction_completedBivariantSequenceOfInvertible C _ _ _ _ _ n j).symm

end CompletedTransport

/-! ### Restriction of a completed composite -/

section CompositeRestriction

variable (C : ChowSituation.{u}) {X P Y Y' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (i : X ⟶ P) [LocallyOfFiniteType i] (g : P ⟶ Y) [LocallyOfFiniteType g]
  (hi : i ≫ sP = sX) (hg : g ≫ sY = sP) (h : Y' ⟶ Y) [LocallyOfFiniteType h]

/-- `Stacks.Chow.bivariantRestriction_bivariantCompositeOfInvertible` for the composite read in an
equal degree `n = p + q`. -/
theorem bivariantRestriction_copy_bivariantCompositeOfInvertible {p q n : ℤ} (hn : p + q = n)
    (a : BivariantClass C (gysinSystemOfInvertible C) sX sP i hi p)
    (b : BivariantClass C (gysinSystemOfInvertible C) sP sY g hg q) :
    bivariantRestriction C (gysinSystemOfInvertible C) sX sY (i ≫ g)
        (comp_comp_structureMorphism_eq hi hg) h n
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (BivariantClass.copy C (gysinSystemOfInvertible C) sX sY rfl
          (comp_comp_structureMorphism_eq hi hg) (comp_comp_structureMorphism_eq hi hg) hn
          (bivariantCompositeOfInvertible C sX sP sY i g hi hg p q a b)) =
      bivariantTransport C (gysinSystemOfInvertible C)
        (pullback.fst i (pullback.fst g h) ≫ sX) (pullback.fst (i ≫ g) h ≫ sX) (h ≫ sY)
        (pullback.snd i (pullback.fst g h) ≫ pullback.snd g h)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C sX sP i hi (pullback.fst g h))
          (pullbackSnd_comp_structureMorphism_eq C sP sY g hg h))
        (pullback.snd (i ≫ g) h)
        (pullbackSnd_comp_structureMorphism_eq C sX sY (i ≫ g)
          (comp_comp_structureMorphism_eq hi hg) h)
        (pullbackRightPullbackFstIso g h i) (pullbackRightPullbackFstIso_hom_snd g h i) n
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (BivariantClass.copy C (gysinSystemOfInvertible C)
          (pullback.fst i (pullback.fst g h) ≫ sX) (h ≫ sY) rfl
          (comp_comp_structureMorphism_eq
            (pullbackSnd_comp_structureMorphism_eq C sX sP i hi (pullback.fst g h))
            (pullbackSnd_comp_structureMorphism_eq C sP sY g hg h))
          (comp_comp_structureMorphism_eq
            (pullbackSnd_comp_structureMorphism_eq C sX sP i hi (pullback.fst g h))
            (pullbackSnd_comp_structureMorphism_eq C sP sY g hg h)) hn
          (bivariantCompositeOfInvertible C (pullback.fst i (pullback.fst g h) ≫ sX)
            (pullback.fst g h ≫ sP) (h ≫ sY) (pullback.snd i (pullback.fst g h))
            (pullback.snd g h)
            (pullbackSnd_comp_structureMorphism_eq C sX sP i hi (pullback.fst g h))
            (pullbackSnd_comp_structureMorphism_eq C sP sY g hg h) p q
            (bivariantRestriction C (gysinSystemOfInvertible C) sX sP i hi (pullback.fst g h) p
              (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a)
            (bivariantRestriction C (gysinSystemOfInvertible C) sP sY g hg h q
              (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) b))) := by
  subst hn
  exact bivariantRestriction_bivariantCompositeOfInvertible C sX sP sY i g hi hg h p q a b

variable [IsLocallyNoetherian X] [IsLocallyNoetherian P] [IsLocallyNoetherian Y]
  [IsLocallyNoetherian Y'] [IsLocallyNoetherian (pullback g h)]
  [IsLocallyNoetherian (pullback (i ≫ g) h)] [IsLocallyNoetherian (pullback i (pullback.fst g h))]

/-- **Restriction of a completed composite is the composite of the restrictions** (Stacks 0F9Z and
Stacks 0B75 on the completions of Stacks 0FE0). For `c ∈ A^*(X ⟶ P)^∧`, `d ∈ A^*(P ⟶ Y)^∧` and
`h : Y' ⟶ Y`, the restriction of `c ∘ d` along `h` is the composite of the restriction of `c`
along `P' = P ×_Y Y' ⟶ P` with the restriction of `d` along `h`, transported
(`Stacks.Chow.completedBivariantTransport`) along the canonical isomorphism
`X ×_P P' ≅ X ×_Y Y'`. -/
theorem completedBivariantRestriction_completedBivariantCompositeOfInvertible
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sP i hi)
    (d : completedBivariantGroup C (gysinSystemOfInvertible C) sP sY g hg) :
    completedBivariantRestrictionViaSequence C sX sY (i ≫ g)
        (comp_comp_structureMorphism_eq hi hg) h
        (completedBivariantCompositeOfInvertible C sX sP sY i g hi hg c d) =
      completedBivariantTransport C (pullback.fst i (pullback.fst g h) ≫ sX)
        (pullback.fst (i ≫ g) h ≫ sX) (h ≫ sY)
        (pullback.snd i (pullback.fst g h) ≫ pullback.snd g h)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C sX sP i hi (pullback.fst g h))
          (pullbackSnd_comp_structureMorphism_eq C sP sY g hg h))
        (pullback.snd (i ≫ g) h)
        (pullbackSnd_comp_structureMorphism_eq C sX sY (i ≫ g)
          (comp_comp_structureMorphism_eq hi hg) h)
        (pullbackRightPullbackFstIso g h i) (pullbackRightPullbackFstIso_hom_snd g h i)
        (completedBivariantCompositeOfInvertible C (pullback.fst i (pullback.fst g h) ≫ sX)
          (pullback.fst g h ≫ sP) (h ≫ sY) (pullback.snd i (pullback.fst g h))
          (pullback.snd g h)
          (pullbackSnd_comp_structureMorphism_eq C sX sP i hi (pullback.fst g h))
          (pullbackSnd_comp_structureMorphism_eq C sP sY g hg h)
          (completedBivariantRestrictionViaSequence C sX sP i hi (pullback.fst g h) c)
          (completedBivariantRestrictionViaSequence C sP sY g hg h d)) := by
  classical
  funext j
  refine DirectSum.ext fun n ↦ ?_
  rw [completedBivariantRestriction_apply, completedBivariantTransport_apply]
  set w := (pullback.fst (i ≫ g) h).continuous.connectedComponentsMap j
  set j' := (pullbackRightPullbackFstIso g h i).inv.continuous.connectedComponentsMap j
  set c' := completedBivariantRestrictionViaSequence C sX sP i hi (pullback.fst g h) c
  set d' := completedBivariantRestrictionViaSequence C sP sY g hg h d
  set s := (c w).support ∪ (c' j').support
  -- the finite sums of homogeneous composites on both sides
  set E := ∑ p ∈ s, BivariantClass.copy C (gysinSystemOfInvertible C) sX sY rfl
    (comp_comp_structureMorphism_eq hi hg) (comp_comp_structureMorphism_eq hi hg)
    (by ring : p + (n - p) = n)
    (bivariantCompositeOfInvertible C sX sP sY i g hi hg p (n - p)
      (completedBivariantSequenceOfInvertible C sX sP i hi c p)
      (completedBivariantSequenceOfInvertible C sP sY g hg d (n - p)))
  set E' := ∑ p ∈ s, BivariantClass.copy C (gysinSystemOfInvertible C)
    (pullback.fst i (pullback.fst g h) ≫ sX) (h ≫ sY) rfl
    (comp_comp_structureMorphism_eq
      (pullbackSnd_comp_structureMorphism_eq C sX sP i hi (pullback.fst g h))
      (pullbackSnd_comp_structureMorphism_eq C sP sY g hg h))
    (comp_comp_structureMorphism_eq
      (pullbackSnd_comp_structureMorphism_eq C sX sP i hi (pullback.fst g h))
      (pullbackSnd_comp_structureMorphism_eq C sP sY g hg h))
    (by ring : p + (n - p) = n)
    (bivariantCompositeOfInvertible C (pullback.fst i (pullback.fst g h) ≫ sX)
      (pullback.fst g h ≫ sP) (h ≫ sY) (pullback.snd i (pullback.fst g h)) (pullback.snd g h)
      (pullbackSnd_comp_structureMorphism_eq C sX sP i hi (pullback.fst g h))
      (pullbackSnd_comp_structureMorphism_eq C sP sY g hg h) p (n - p)
      (completedBivariantSequenceOfInvertible C _ _ _ _ c' p)
      (completedBivariantSequenceOfInvertible C _ _ _ _ d' (n - p)))
  -- the left side only sees `c ∘ d` on `X_w`, where it is the restriction of `E`
  have hL := bivariantConnectedComponentRestriction_bivariantRestriction_eq_of_eq C
    (gysinSystemOfInvertible C) sX sY (i ≫ g) (comp_comp_structureMorphism_eq hi hg) n
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) h
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (completedBivariantSequenceOfInvertible C sX sY (i ≫ g) _
      (completedBivariantCompositeOfInvertible C sX sP sY i g hi hg c d) n) E j
    ((restriction_completedBivariantSequenceOfInvertible C sX sY (i ≫ g) _ _ n w).trans
      (bivariantConnectedComponentRestriction_sum_bivariantCompositeOfInvertible C sX sP i hi sY g
        hg c d w n s fun p hp ↦ Finset.mem_union_left _ (DFinsupp.mem_support_iff.2 hp)).symm)
  -- the right side only sees `c' ∘ d'` on the component below, where it is the restriction of `E'`
  have hR := bivariantConnectedComponentRestriction_bivariantTransport_eq_of_eq C
    (gysinSystemOfInvertible C) _ _ (h ≫ sY) _ _ _
    (pullbackSnd_comp_structureMorphism_eq C sX sY (i ≫ g)
      (comp_comp_structureMorphism_eq hi hg) h)
    (pullbackRightPullbackFstIso g h i) (pullbackRightPullbackFstIso_hom_snd g h i) n
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (completedBivariantSequenceOfInvertible C _ _ _ _
      (completedBivariantCompositeOfInvertible C (pullback.fst i (pullback.fst g h) ≫ sX)
        (pullback.fst g h ≫ sP) (h ≫ sY) (pullback.snd i (pullback.fst g h)) (pullback.snd g h)
        (pullbackSnd_comp_structureMorphism_eq C sX sP i hi (pullback.fst g h))
        (pullbackSnd_comp_structureMorphism_eq C sP sY g hg h) c' d') n) E' j
    ((restriction_completedBivariantSequenceOfInvertible C _ _ _ _ _ n j').trans
      (bivariantConnectedComponentRestriction_sum_bivariantCompositeOfInvertible C _ _ _ _ _ _ _
        c' d' j' n s fun p hp ↦ Finset.mem_union_right _ (DFinsupp.mem_support_iff.2 hp)).symm)
  -- the homogeneous compatibility, term by term
  have key : bivariantRestrictionAddHom C (gysinSystemOfInvertible C) sX sY (i ≫ g)
      (comp_comp_structureMorphism_eq hi hg) h n
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) E =
      bivariantTransportAddHom C (gysinSystemOfInvertible C) _ _ (h ≫ sY) _ _ _
        (pullbackSnd_comp_structureMorphism_eq C sX sY (i ≫ g)
          (comp_comp_structureMorphism_eq hi hg) h)
        (pullbackRightPullbackFstIso g h i) (pullbackRightPullbackFstIso_hom_snd g h i) n
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) E' := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    refine (bivariantRestriction_copy_bivariantCompositeOfInvertible C sX sP sY i g hi hg h _ _
      _).trans ?_
    rw [completedBivariantSequenceOfInvertible_completedBivariantRestriction,
      completedBivariantSequenceOfInvertible_completedBivariantRestriction]
    rfl
  rw [hL, hR]
  exact congrArg (fun z ↦ bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) _ _
    _ _ n (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) z j) key

end CompositeRestriction

/-! ### Homogeneous classes as completed classes -/

section Homogeneous

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
  {hf : f ≫ sY = sX} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] {n : ℤ}

/-- **The tuple of a homogeneous class** (Stacks 0FE0): the tuple attached to `x ∈ A^n(X ⟶ Y)`,
read as a completed class, is `x` in degree `n` and zero in every other degree. -/
theorem completedBivariantSequenceOfInvertible_toCompleted
    (x : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf n) :
    completedBivariantSequenceOfInvertible C sX sY f hf (x.toCompleted C) = Pi.single n x := by
  funext m
  apply (bivariantConnectedComponentEquiv C (gysinSystemOfInvertible C) sX sY f hf m
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C)).injective
  funext w
  rw [bivariantConnectedComponentEquiv_apply, bivariantConnectedComponentEquiv_apply]
  refine (restriction_completedBivariantSequenceOfInvertible C sX sY f hf _ m w).trans ?_
  rw [BivariantClass.toCompleted_apply]
  by_cases hm : m = n
  · subst hm
    rw [DirectSum.of_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hm, map_zero, Pi.zero_apply]
    exact DirectSum.of_eq_of_ne n m _ hm

/-- The degree `n` term of the tuple of `x ∈ A^n(X ⟶ Y)`, read as a completed class, is `x`. -/
@[simp]
theorem completedBivariantSequenceOfInvertible_toCompleted_self
    (x : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf n) :
    completedBivariantSequenceOfInvertible C sX sY f hf (x.toCompleted C) n = x := by
  rw [completedBivariantSequenceOfInvertible_toCompleted, Pi.single_eq_same]

/-- The terms in degrees `m ≠ n` of the tuple of `x ∈ A^n(X ⟶ Y)`, read as a completed class,
vanish. -/
theorem completedBivariantSequenceOfInvertible_toCompleted_of_ne
    (x : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf n) {m : ℤ} (hm : m ≠ n) :
    completedBivariantSequenceOfInvertible C sX sY f hf (x.toCompleted C) m = 0 := by
  rw [completedBivariantSequenceOfInvertible_toCompleted, Pi.single_eq_of_ne hm]

variable {Y' : Scheme.{u}} (h : Y' ⟶ Y) [LocallyOfFiniteType h] [IsLocallyNoetherian Y']
  [IsLocallyNoetherian (pullback f h)]

/-- **Restriction of a homogeneous class, on completions** (Stacks 0F9Z on Stacks 0FE0). The
restriction along `h : Y' ⟶ Y` of `x ∈ A^n(X ⟶ Y)`, read as a completed class, is the restriction
of `x`, read as a completed class. -/
theorem completedBivariantRestriction_toCompleted
    (x : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf n) :
    completedBivariantRestrictionViaSequence C sX sY f hf h (x.toCompleted C) =
      (bivariantRestriction C (gysinSystemOfInvertible C) sX sY f hf h n
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) x).toCompleted C := by
  funext j
  refine DirectSum.ext fun m ↦ ?_
  rw [completedBivariantRestriction_apply, BivariantClass.toCompleted_apply]
  by_cases hm : m = n
  · subst hm
    rw [completedBivariantSequenceOfInvertible_toCompleted_self, DirectSum.of_eq_same]
  · rw [completedBivariantSequenceOfInvertible_toCompleted_of_ne C x hm,
      bivariantRestriction_zero, map_zero, Pi.zero_apply]
    exact (DirectSum.of_eq_of_ne n m _ hm).symm

end Homogeneous

end Stacks.Chow

end
