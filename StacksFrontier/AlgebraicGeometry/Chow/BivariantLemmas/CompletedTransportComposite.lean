module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestrictionOfComposite

/-!
# Transport of completed bivariant classes: composites, composition of transports, identity

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. For morphisms
`v : A ⟶ W` and `u : B ⟶ W` locally of finite type and an isomorphism `θ : A ≅ B` over `W`, a
completed bivariant class `c ∈ A^*(A ⟶ W)^∧` (Stacks 0FE0) is carried to the class
`θ_* c ∈ A^*(B ⟶ W)^∧` (`Stacks.Chow.completedBivariantTransport`), whose tuple is the tuple of
the transports `θ_* c_n` of the homogeneous terms. This file proves the three formal properties
of this transport:

* it is compatible with composition (Stacks 0B75 on completions): for `v : A ⟶ P`,
  `u : B ⟶ P` with `θ ≫ u = v` and `g : P ⟶ W`, `θ_*(c ∘ d) = θ_*(c) ∘ d`;
* it is functorial: transporting along `θ` and then along `φ : B ≅ D` is transporting along
  `θ ≫ φ`;
* transporting along an isomorphism whose underlying morphism is the identity changes nothing.

## Main results

* `Stacks.Chow.bivariantTransport_bivariantCompositeOfInvertible` — for homogeneous classes,
  `θ_*(a ∘ b) = θ_*(a) ∘ b`.
* `Stacks.Chow.bivariantTransport_bivariantTransport` — for homogeneous classes,
  `φ_*(θ_* c) = (θ ≫ φ)_* c`.
* `Stacks.Chow.bivariantTransport_of_hom_eq_id` — for homogeneous classes, `θ_* c = c` when
  `θ` is the identity of `A`.
* `Stacks.Chow.completedBivariantTransport_completedBivariantCompositeOfInvertible` —
  `θ_*(c ∘ d) = θ_*(c) ∘ d` on completions.
* `Stacks.Chow.completedBivariantTransport_completedBivariantTransport` —
  `φ_*(θ_* c) = (θ ≫ φ)_* c` on completions.
* `Stacks.Chow.completedBivariantTransport_of_hom_eq_id` — `θ_* c = c` on completions when `θ`
  is the identity of `A`.
* `Stacks.Chow.completedBivariantTransport_heq_congr` — transport respects equality of its data.

## Implementation notes

The homogeneous statements are checked on cap operations: the cap operation of a transport is the
cap operation of the class pushed forward along the induced isomorphism of base changes, and
pushforward along isomorphisms is functorial. The completed statements for transports of
transports and along the identity then hold degree by degree, a completed class being determined
by its tuple. For composites the degree `n` term of `c ∘ d` is only known on each connected
component `B_j`, as the restriction of a finite sum `∑_{p ∈ s} c_p ∘ d_{n-p}` of homogeneous
composites; the transport of a class only depends, on `B_j`, on the class on the component of `A`
below it, so choosing `s` large enough for both sides reduces the identity to the homogeneous one,
term by term.

## References

* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Homogeneous classes -/

section Homogeneous

variable (C : ChowSituation.{u}) (G : GysinSystem C) {A B D W : Scheme.{u}} (sA : A ⟶ C.S)
  [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sD : D ⟶ C.S)
  [LocallyOfFiniteType sD] (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (v : A ⟶ W)
  [LocallyOfFiniteType v] (hv : v ≫ sW = sA) (u : B ⟶ W) [LocallyOfFiniteType u]
  (hu : u ≫ sW = sB) (t : D ⟶ W) [LocallyOfFiniteType t] (ht : t ≫ sW = sD) (p : ℤ)
  (hgys : G.IsNaturalUnderBaseChangeIso)

/-- **Transport is functorial.** Transporting a class along `θ : A ≅ B` and then along
`φ : B ≅ D`, all over `W`, is transporting it along `θ ≫ φ`. -/
theorem bivariantTransport_bivariantTransport (θ : A ≅ B) (hθ : θ.hom ≫ u = v) (φ : B ≅ D)
    (hφ : φ.hom ≫ t = u) (c : BivariantClass C G sA sW v hv p) :
    bivariantTransport C G sB sD sW u hu t ht φ hφ p hgys
        (bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys c) =
      bivariantTransport C G sA sD sW v hv t ht (θ ≪≫ φ)
        (by rw [Iso.trans_hom, Category.assoc, hφ, hθ]) p hgys c := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun {T} g _ k α ↦ ?_
  rw [bivariantTransport_cap, bivariantTransportCap_apply, bivariantTransport_cap,
    bivariantTransportCap_apply, bivariantTransport_cap, bivariantTransportCap_apply,
    chowPushforwardOfIso_comp_apply]
  exact chowPushforwardOfIso_congr_apply C _ _ _ _ (by apply pullback.hom_ext <;> simp) _ _ _ _

/-- **Transport along the identity.** Transporting a class along an isomorphism `θ : A ≅ A` over
`W` whose underlying morphism is the identity gives the class back. -/
theorem bivariantTransport_of_hom_eq_id (θ : A ≅ A) (hθ : θ.hom ≫ v = v) (h : θ.hom = 𝟙 A)
    (c : BivariantClass C G sA sW v hv p) :
    bivariantTransport C G sA sA sW v hv v hv θ hθ p hgys c = c := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun {T} g _ k α ↦ ?_
  rw [bivariantTransport_cap, bivariantTransportCap_apply,
    chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _) (by apply pullback.hom_ext <;> simp [h]) _
      (Category.id_comp _), chowPushforwardOfIso_id]

end Homogeneous

section HomogeneousComposite

variable (C : ChowSituation.{u}) {A B P W : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
  (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
  (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (v : A ⟶ P) [LocallyOfFiniteType v] (hv : v ≫ sP = sA)
  (u : B ⟶ P) [LocallyOfFiniteType u] (hu : u ≫ sP = sB) (g : P ⟶ W) [LocallyOfFiniteType g]
  (hg : g ≫ sW = sP) (θ : A ≅ B) (hθ : θ.hom ≫ u = v)

/-- **Transport of a composite** (Stacks 0B75). For `v : A ⟶ P`, `u : B ⟶ P`, an isomorphism
`θ : A ≅ B` over `P` and `g : P ⟶ W`, the transport along `θ` of the composite
`a ∘ b ∈ A^{p+q}(A ⟶ W)` is the composite `θ_*(a) ∘ b ∈ A^{p+q}(B ⟶ W)`. -/
theorem bivariantTransport_bivariantCompositeOfInvertible (p q : ℤ)
    (a : BivariantClass C (gysinSystemOfInvertible C) sA sP v hv p)
    (b : BivariantClass C (gysinSystemOfInvertible C) sP sW g hg q) :
    bivariantTransport C (gysinSystemOfInvertible C) sA sB sW (v ≫ g)
        (comp_comp_structureMorphism_eq hv hg) (u ≫ g) (comp_comp_structureMorphism_eq hu hg) θ
        (by rw [← Category.assoc, hθ]) (p + q)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantCompositeOfInvertible C sA sP sW v g hv hg p q a b) =
      bivariantCompositeOfInvertible C sB sP sW u g hu hg p q
        (bivariantTransport C (gysinSystemOfInvertible C) sA sB sP v hv u hu θ hθ p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a) b := by
  refine eq_of_isBivariantClassComposition (hpp := properPushforwardDescends C) ?_
    (isBivariantClassComposition_bivariantCompositeOfInvertible C _ _ _ _ _ _ _ _ _ _ _)
  intro T t _ k α
  have hc := isBivariantClassComposition_bivariantCompositeOfInvertible C sA sP sW v g hv hg p q
    a b t k α
  rw [bivariantTransport_cap, bivariantTransportCap_apply]
  have hbase := transportPullbackIso_hom_comp_base C sA sB sW (v ≫ g)
    (comp_comp_structureMorphism_eq hv hg) (u ≫ g) (comp_comp_structureMorphism_eq hu hg) θ
    (by rw [← Category.assoc, hθ]) t
  refine (chowPushforwardOfIso_heq (transportPullbackIso (v ≫ g) (u ≫ g) θ
    (by rw [← Category.assoc, hθ]) t).hom hbase hbase rfl rfl (by ring) hc).trans
    (heq_of_eq ?_)
  rw [bivariantCompositeCap_apply, bivariantCompositeCap_apply, bivariantTransport_cap,
    bivariantTransportCap_apply, properChowPushforward_eq_chowPushforwardOfIso,
    properChowPushforward_eq_chowPushforwardOfIso, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_comp_apply]
  exact chowPushforwardOfIso_congr_apply C _ _ _ _ (by apply pullback.hom_ext <;> simp) _ _ _ _

/-- `Stacks.Chow.bivariantTransport_bivariantCompositeOfInvertible` for the composites read in an
equal degree `n = p + q`. -/
theorem bivariantTransport_copy_bivariantCompositeOfInvertible {p q n : ℤ} (hn : p + q = n)
    (a : BivariantClass C (gysinSystemOfInvertible C) sA sP v hv p)
    (b : BivariantClass C (gysinSystemOfInvertible C) sP sW g hg q) :
    bivariantTransport C (gysinSystemOfInvertible C) sA sB sW (v ≫ g)
        (comp_comp_structureMorphism_eq hv hg) (u ≫ g) (comp_comp_structureMorphism_eq hu hg) θ
        (by rw [← Category.assoc, hθ]) n
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (BivariantClass.copy C (gysinSystemOfInvertible C) sA sW rfl
          (comp_comp_structureMorphism_eq hv hg) (comp_comp_structureMorphism_eq hv hg) hn
          (bivariantCompositeOfInvertible C sA sP sW v g hv hg p q a b)) =
      BivariantClass.copy C (gysinSystemOfInvertible C) sB sW rfl
        (comp_comp_structureMorphism_eq hu hg) (comp_comp_structureMorphism_eq hu hg) hn
        (bivariantCompositeOfInvertible C sB sP sW u g hu hg p q
          (bivariantTransport C (gysinSystemOfInvertible C) sA sB sP v hv u hu θ hθ p
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a) b) := by
  subst hn
  exact bivariantTransport_bivariantCompositeOfInvertible C sA sB sP sW v hv u hu g hg θ hθ p q a b

end HomogeneousComposite

/-! ### Completed classes -/

section Completed

variable (C : ChowSituation.{u}) {A B D P W : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
  (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sD : D ⟶ C.S) [LocallyOfFiniteType sD]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (sW : W ⟶ C.S) [LocallyOfFiniteType sW]

/-- Two completed classes with the same homogeneous terms in every degree are equal. -/
private theorem completed_ext_of_sequence {X Y : Scheme.{u}} {sX : X ⟶ C.S}
    [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y}
    [LocallyOfFiniteType f] {hf : f ≫ sY = sX} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {c d : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf}
    (h : ∀ n, completedBivariantSequenceOfInvertible C sX sY f hf c n =
      completedBivariantSequenceOfInvertible C sX sY f hf d n) : c = d :=
  completedBivariantSequence_injective C (gysinSystemOfInvertible C) _ _ _ _ _ _ _ (funext h)

/-- **Transport of a completed composite** (Stacks 0B75 on the completions of Stacks 0FE0). For
`v : A ⟶ P`, `u : B ⟶ P`, an isomorphism `θ : A ≅ B` over `P` and `g : P ⟶ W`, the transport
along `θ` of `c ∘ d ∈ A^*(A ⟶ W)^∧` is `θ_*(c) ∘ d ∈ A^*(B ⟶ W)^∧`. -/
theorem completedBivariantTransport_completedBivariantCompositeOfInvertible (v : A ⟶ P)
    [LocallyOfFiniteType v] (hv : v ≫ sP = sA) (u : B ⟶ P)
    [LocallyOfFiniteType u] (hu : u ≫ sP = sB) (g : P ⟶ W) [LocallyOfFiniteType g]
    (hg : g ≫ sW = sP) (θ : A ≅ B) (hθ : θ.hom ≫ u = v) [IsLocallyNoetherian A]
    [IsLocallyNoetherian B] [IsLocallyNoetherian P] [IsLocallyNoetherian W]
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sA sP v hv)
    (d : completedBivariantGroup C (gysinSystemOfInvertible C) sP sW g hg) :
    completedBivariantTransport C sA sB sW (v ≫ g) (comp_comp_structureMorphism_eq hv hg) (u ≫ g)
        (comp_comp_structureMorphism_eq hu hg) θ (by rw [← Category.assoc, hθ])
        (completedBivariantCompositeOfInvertible C sA sP sW v g hv hg c d) =
      completedBivariantCompositeOfInvertible C sB sP sW u g hu hg
        (completedBivariantTransport C sA sB sP v hv u hu θ hθ c) d := by
  classical
  funext j
  refine DirectSum.ext fun n ↦ ?_
  rw [completedBivariantTransport_apply]
  set j' := θ.inv.continuous.connectedComponentsMap j
  set s := (c j').support ∪
    (completedBivariantTransport C sA sB sP v hv u hu θ hθ c j).support
  -- the finite sums of homogeneous composites on both sides
  set E := ∑ p ∈ s, BivariantClass.copy C (gysinSystemOfInvertible C) sA sW rfl
    (comp_comp_structureMorphism_eq hv hg) (comp_comp_structureMorphism_eq hv hg)
    (by ring : p + (n - p) = n)
    (bivariantCompositeOfInvertible C sA sP sW v g hv hg p (n - p)
      (completedBivariantSequenceOfInvertible C sA sP v hv c p)
      (completedBivariantSequenceOfInvertible C sP sW g hg d (n - p)))
  set E' := ∑ p ∈ s, BivariantClass.copy C (gysinSystemOfInvertible C) sB sW rfl
    (comp_comp_structureMorphism_eq hu hg) (comp_comp_structureMorphism_eq hu hg)
    (by ring : p + (n - p) = n)
    (bivariantCompositeOfInvertible C sB sP sW u g hu hg p (n - p)
      (completedBivariantSequenceOfInvertible C sB sP u hu
        (completedBivariantTransport C sA sB sP v hv u hu θ hθ c) p)
      (completedBivariantSequenceOfInvertible C sP sW g hg d (n - p)))
  -- the left side only sees `c ∘ d` on the component `A_{j'}` below `B_j`, where it is `E`
  have hL := bivariantConnectedComponentRestriction_bivariantTransport_eq_of_eq C
    (gysinSystemOfInvertible C) sA sB sW (v ≫ g) (comp_comp_structureMorphism_eq hv hg) (u ≫ g)
    (comp_comp_structureMorphism_eq hu hg) θ (by rw [← Category.assoc, hθ]) n
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (completedBivariantSequenceOfInvertible C sA sW (v ≫ g) _
      (completedBivariantCompositeOfInvertible C sA sP sW v g hv hg c d) n) E j
    (((restriction_completedBivariantSequence C (gysinSystemOfInvertible C) sA sW (v ≫ g) _
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
      (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
      (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) _ n j')).trans
      (bivariantConnectedComponentRestriction_sum_bivariantCompositeOfInvertible C sA sP v hv sW g
        hg c d j' n s fun p hp ↦ Finset.mem_union_left _ (DFinsupp.mem_support_iff.2 hp)).symm)
  -- the right side on `B_j` is the restriction of `E'`
  have hR := bivariantConnectedComponentRestriction_sum_bivariantCompositeOfInvertible C sB sP u
    hu sW g hg (completedBivariantTransport C sA sB sP v hv u hu θ hθ c) d j n s
    fun p hp ↦ Finset.mem_union_right _ (DFinsupp.mem_support_iff.2 hp)
  -- the homogeneous compatibility, term by term
  have key : bivariantTransportAddHom C (gysinSystemOfInvertible C) sA sB sW (v ≫ g)
      (comp_comp_structureMorphism_eq hv hg) (u ≫ g) (comp_comp_structureMorphism_eq hu hg) θ
      (by rw [← Category.assoc, hθ]) n
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) E = E' := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    refine (bivariantTransport_copy_bivariantCompositeOfInvertible C sA sB sP sW v hv u hu g hg θ
      hθ _ _ _).trans ?_
    rw [completedBivariantSequenceOfInvertible_completedBivariantTransport]
  rw [hL, ← hR]
  exact congrArg (fun z ↦ bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) _ _
    _ _ n (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) z j) key

/-- **Transport of completed classes is functorial.** Transporting a completed class along
`θ : A ≅ B` and then along `φ : B ≅ D`, all over `W`, is transporting it along `θ ≫ φ`; degree
by degree this is `Stacks.Chow.bivariantTransport_bivariantTransport`. -/
theorem completedBivariantTransport_completedBivariantTransport (v : A ⟶ W)
    [LocallyOfFiniteType v] (hv : v ≫ sW = sA) (u : B ⟶ W)
    [LocallyOfFiniteType u] (hu : u ≫ sW = sB) (t : D ⟶ W) [LocallyOfFiniteType t]
    (ht : t ≫ sW = sD) (θ : A ≅ B) (hθ : θ.hom ≫ u = v) (φ : B ≅ D) (hφ : φ.hom ≫ t = u)
    [IsLocallyNoetherian A] [IsLocallyNoetherian B] [IsLocallyNoetherian D]
    [IsLocallyNoetherian W] (c : completedBivariantGroup C (gysinSystemOfInvertible C) sA sW v hv) :
    completedBivariantTransport C sB sD sW u hu t ht φ hφ
        (completedBivariantTransport C sA sB sW v hv u hu θ hθ c) =
      completedBivariantTransport C sA sD sW v hv t ht (θ ≪≫ φ)
        (by rw [Iso.trans_hom, Category.assoc, hφ, hθ]) c := by
  refine completed_ext_of_sequence C fun n ↦ ?_
  refine (completedBivariantSequenceOfInvertible_completedBivariantTransport C sB sD sW u hu t ht
    φ hφ _ n).trans ?_
  refine (congrArg (bivariantTransport C (gysinSystemOfInvertible C) sB sD sW u hu t ht φ hφ n
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C))
    (completedBivariantSequenceOfInvertible_completedBivariantTransport C sA sB sW v hv u hu θ hθ
      c n)).trans ?_
  refine (bivariantTransport_bivariantTransport C (gysinSystemOfInvertible C) sA sB sD sW v hv u
    hu t ht n (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) θ hθ φ hφ _).trans ?_
  exact (completedBivariantSequenceOfInvertible_completedBivariantTransport C sA sD sW v hv t ht
    (θ ≪≫ φ) (by rw [Iso.trans_hom, Category.assoc, hφ, hθ]) c n).symm

/-- **Transport of completed classes along the identity.** Transporting a completed class along an
isomorphism `θ : A ≅ A` over `W` whose underlying morphism is the identity gives the class back;
degree by degree this is `Stacks.Chow.bivariantTransport_of_hom_eq_id`. -/
theorem completedBivariantTransport_of_hom_eq_id (v : A ⟶ W) [LocallyOfFiniteType v]
    (hv : v ≫ sW = sA) (θ : A ≅ A) (hθ : θ.hom ≫ v = v) (h : θ.hom = 𝟙 A)
    [IsLocallyNoetherian A] [IsLocallyNoetherian W]
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sA sW v hv) :
    completedBivariantTransport C sA sA sW v hv v hv θ hθ c = c := by
  refine completed_ext_of_sequence C fun n ↦ ?_
  refine (completedBivariantSequenceOfInvertible_completedBivariantTransport C sA sA sW v hv v hv
    θ hθ c n).trans ?_
  exact bivariantTransport_of_hom_eq_id C (gysinSystemOfInvertible C) sA sW v hv n
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) θ hθ h _

variable {sA sB sW} in
/-- **Transport of completed classes depends on its data only up to equality.** Transports along
equal isomorphisms into equal morphisms `u = u'` agree, as completed classes for the two
morphisms. -/
theorem completedBivariantTransport_heq_congr {v : A ⟶ W} [LocallyOfFiniteType v]
    {hv : v ≫ sW = sA} {u u' : B ⟶ W} [LocallyOfFiniteType u] [LocallyOfFiniteType u']
    {hu : u ≫ sW = sB} {hu' : u' ≫ sW = sB} {θ θ' : A ≅ B} {hθ : θ.hom ≫ u = v}
    {hθ' : θ'.hom ≫ u' = v} [IsLocallyNoetherian A] [IsLocallyNoetherian B]
    [IsLocallyNoetherian W] (huu : u = u') (hθθ : θ = θ')
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sA sW v hv) :
    completedBivariantTransport C sA sB sW v hv u hu θ hθ c ≍
      completedBivariantTransport C sA sB sW v hv u' hu' θ' hθ' c := by
  subst huu hθθ
  rfl

end Completed

end Stacks.Chow

end
