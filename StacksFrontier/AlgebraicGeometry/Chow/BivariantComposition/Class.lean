module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinNaturality
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.RationalEquivalenceDescent

/-!
# The composite of two bivariant Chow classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` and
`g : Y ⟶ Z` be morphisms of schemes locally of finite type over `S`, and let
`a ∈ A^p(X ⟶ Y)` and `b ∈ A^q(Y ⟶ Z)` be bivariant classes. Stacks 0B75 asserts, after the
definition of a bivariant class, that there is a bilinear composition

  `A^p(X ⟶ Y) × A^q(Y ⟶ Z) ⟶ A^{p+q}(X ⟶ Z)`.

Its cap operation is `Stacks.Chow.bivariantCompositeCap`, and the three naturality conditions of
Stacks 0B76 for that cap operation are
`Stacks.Chow.bivariantCompositeCap_proper_naturality`,
`Stacks.Chow.bivariantCompositeCap_flat_naturality_of_factors` and
`Stacks.Chow.bivariantCompositeCap_gysin_naturality`; they assemble into the composite bivariant
class itself, which satisfies the characterization `Stacks.Chow.IsBivariantClassComposition` of
Stacks 0FE0.

`Stacks.Chow.bivariantCompositeCap` lands in `A_{(k-q)-p}` while the cap operation of a bivariant
class of degree `p + q` must land in `A_{k-(p+q)}`. The two integers are equal but not
definitionally so, so the cap operation of the composite is the composite cap operation followed
by `Stacks.Chow.chowGroupDegreeEquiv` along that equality, and each of the three naturality
conditions is the corresponding condition for `Stacks.Chow.bivariantCompositeCap` commuted past
that transport; the three commutations are
`Stacks.Chow.chowGroupDegreeEquiv_properChowPushforward_comp`,
`Stacks.Chow.flatPullbackChow_heq_of_degree` and
`Stacks.Chow.GysinSystem.onChow_chowGroupDegreeEquiv`. It is also why
`Stacks.Chow.IsBivariantClassComposition` is stated with a heterogeneous equality.

The construction needs the descents Stacks 02S2 for proper pushforward and Stacks 02S1 for flat
pullback, supplied by `Stacks.Chow.properPushforwardDescends` and
`Stacks.Chow.flatPullbackDescends`: the first is already needed to define
`Stacks.Chow.bivariantCompositeCap` at all, and the second supplies the instance for the middle
base change `T' ×_Z Y ⟶ T ×_Z Y` that
`Stacks.Chow.bivariantCompositeCap_flat_naturality_of_factors` takes as an argument and cannot
produce.  They come with the two cases of Stacks 02TA for the Gysin
system, which remain hypotheses: they are properties of the Gysin system `G`, which the bivariant
development carries as a parameter, and an arbitrary `Stacks.Chow.GysinSystem` does not satisfy
them, its first Chern class rules on two schemes being unrelated data.

## Main definitions

* `Stacks.Chow.bivariantComposite` — the composite `a ∘ b ∈ A^{p+q}(X ⟶ Z)`.
* `Stacks.Chow.bivariantCompositeBilinear` — that composite as the bilinear map
  `A^p(X ⟶ Y) ⟶ A^q(Y ⟶ Z) ⟶ A^{p+q}(X ⟶ Z)` the tag asserts.

## Main results

* `Stacks.Chow.bivariantComposite_add_left` and `Stacks.Chow.bivariantComposite_add_right` — the
  composition is additive in each argument, which is what bundles it as a bilinear map.
* `Stacks.Chow.bivariantComposite_cap` — its cap operation is
  `Stacks.Chow.bivariantCompositeCap`, read through the transport of Chow groups along
  `k - q - p = k - (p + q)`.
* `Stacks.Chow.isBivariantClassComposition_bivariantComposite` — the composite satisfies the
  characterization of Stacks 0FE0, so `Stacks.Chow.IsBivariantClassComposition` is inhabited and
  `Stacks.Chow.eq_of_isBivariantClassComposition` identifies the composite with any other class
  satisfying it.

## References

* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transport along an equality of degrees and the three operations -/

section Transport

variable (C : ChowSituation.{u}) {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
  (sB : B ⟶ C.S) [LocallyOfFiniteType sB]

/-- Proper pushforward on Chow groups commutes with the transport along an equality of degrees. -/
theorem chowGroupDegreeEquiv_properChowPushforward_comp (u : A ⟶ B) [IsProper u] (hu : u ≫ sB = sA)
    {k l : ℤ} (hkl : k = l)
    (hfack : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k)
    (hfacl : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu l)
    (x : chowGroup C sA k) :
    chowGroupDegreeEquiv C sB hkl (properChowPushforward C sA sB u hu k hfack x) =
      properChowPushforward C sA sB u hu l hfacl (chowGroupDegreeEquiv C sA hkl x) := by
  subst hkl
  rfl

/-- Flat pullback on Chow groups of classes that agree up to an equality of degrees agrees up to
an equality of degrees. -/
theorem flatPullbackChow_heq_of_degree (v : A ⟶ B) [LocallyOfFiniteType v] [Flat v]
    (hv : v ≫ sB = sA) (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension v r) {k l : ℤ}
    (hkl : k = l)
    (hfack : FlatPullbackFactorsThroughRationalEquivalence C sA sB v hv r hr k)
    (hfacl : FlatPullbackFactorsThroughRationalEquivalence C sA sB v hv r hr l)
    {x : chowGroup C sB k} {y : chowGroup C sB l} (hxy : x ≍ y) :
    flatPullbackChow C sA sB v hv r hr k hfack x ≍
      flatPullbackChow C sA sB v hv r hr l hfacl y := by
  subst hkl
  exact heq_of_eq (congrArg (flatPullbackChow C sA sB v hv r hr k hfack) (eq_of_heq hxy))

end Transport

/-! ### The composite class -/

section Composite

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z)
  [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY)
  (p q : ℤ) (a : BivariantClass C G sX sY f hf p) (b : BivariantClass C G sY sZ g hg q)

/-- The composite `a ∘ b ∈ A^{p+q}(X ⟶ Z)` of bivariant classes `a ∈ A^p(X ⟶ Y)` and
`b ∈ A^q(Y ⟶ Z)`: the bivariant class of degree `p + q` for `f ≫ g` whose cap operation is
`α ↦ a ∩ (b ∩ α)`, that is, `Stacks.Chow.bivariantCompositeCap` read through the transport of Chow
groups along `k - q - p = k - (p + q)` [Stacks, Tag 0B75]. -/
@[stacks 0B75 "the composite bivariant class, assembled from its cap operation and the three
naturality conditions of Stacks 0B76"]
def bivariantComposite (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) :
    BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) (p + q) where
  cap t _ k :=
    (chowGroupDegreeEquiv C (pullback.fst (f ≫ g) t ≫ sX)
        (by ring : k - q - p = k - (p + q))).toAddMonoidHom.comp
      (bivariantCompositeCap C G sX sY sZ f g hf hg (properPushforwardDescends C) p q a b t k)
  cap_properPushforward := by
    intro T T' t ht h hh h' sq hfst k α
    have hprop : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    refine (DFunLike.congr_arg (chowGroupDegreeEquiv C (pullback.fst (f ≫ g) t ≫ sX)
        (by ring : k - q - p = k - (p + q)))
      (bivariantCompositeCap_proper_naturality C G sX sY sZ f g hf hg (properPushforwardDescends C)
        p q a b t h h' sq hfst k α)).trans ?_
    exact chowGroupDegreeEquiv_properChowPushforward_comp C
      (pullback.fst (f ≫ g) (h ≫ t) ≫ sX) (pullback.fst (f ≫ g) t ≫ sX) h'
      (by rw [← Category.assoc, hfst]) (by ring : k - q - p = k - (p + q))
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) _
  cap_flatPullbackChow := by
    intro T T' t ht h hh fh r hr h' sq hfst k α
    have hr' := AlgebraicGeometry.RelativeDimension.of_isPullback sq hr
    have hfth' : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    have hflh' : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    have hftM : LocallyOfFiniteType (compositeMiddleBaseChange g t h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap g t h)
        (P := @LocallyOfFiniteType) inferInstance
    have hflM : Flat (compositeMiddleBaseChange g t h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap g t h) (P := @Flat)
        inferInstance
    refine (chowGroupDegreeEquiv_heq C _ _ _).trans
      ((bivariantCompositeCap_flat_naturality_of_factors C G sX sY sZ f g hf hg
        (properPushforwardDescends C) p q a b t h r hr h' sq hfst k hr'
        (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
        (flatPullbackDescends C _ _ _ _ _ _ _) α).trans ?_)
    exact flatPullbackChow_heq_of_degree C (pullback.fst (f ≫ g) (h ≫ t) ≫ sX)
      (pullback.fst (f ≫ g) t ≫ sX) h' (by rw [← Category.assoc, hfst]) r hr'
      (by ring : k - q - p = k - (p + q)) (flatPullbackDescends C _ _ _ _ _ _ _)
      (flatPullbackDescends C _ _ _ _ _ _ _)
      (chowGroupDegreeEquiv_heq C _ _ _).symm
  cap_gysin := by
    intro T t ht L hL s k D L' s' E e he hbase α
    have hidx : (k + 1) - q - p = (k - q - p) + 1 := by omega
    have hdeg : k - q - p = k - (p + q) := by ring
    have hdeg' : (k - q - p) + 1 = (k - (p + q)) + 1 := by rw [hdeg]
    have hidxP : (k + 1) - (p + q) = (k - (p + q)) + 1 := by omega
    refine ((chowGroupDegreeEquiv_properChowPushforward_comp C
        (pullback.fst (f ≫ g) (D.subschemeι ≫ t) ≫ sX)
        (E.subschemeι ≫ pullback.fst (f ≫ g) t ≫ sX) e.hom hbase hdeg
        (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
        _).symm.trans ?_)
    refine (DFunLike.congr_arg (chowGroupDegreeEquiv C
        (E.subschemeι ≫ pullback.fst (f ≫ g) t ≫ sX) hdeg)
      (bivariantCompositeCap_gysin_naturality C G sX sY sZ f g hf hg (properPushforwardDescends C)
        p q a b hgys hgysc t L s k e he hbase (properPushforwardDescends C _ _ _ _ _)
        α)).trans ?_
    refine (GysinSystem.onChow_chowGroupDegreeEquiv G (pullback.fst (f ≫ g) t ≫ sX) L' s' hdeg
      hdeg' _).trans (congrArg (G.onChow (pullback.fst (f ≫ g) t ≫ sX) L' s' (k - (p + q)))
        (eq_of_heq ?_))
    refine HEq.trans (chowGroupDegreeEquiv_heq C (pullback.fst (f ≫ g) t ≫ sX) hdeg' _) ?_
    refine HEq.trans (heq_eq_mp_index hidx
      (bivariantCompositeCap C G sX sY sZ f g hf hg (properPushforwardDescends C) p q a b t
        (k + 1) α)).symm ?_
    refine HEq.trans (chowGroupDegreeEquiv_heq C (pullback.fst (f ≫ g) t ≫ sX)
      (by ring : (k + 1) - q - p = (k + 1) - (p + q)) _).symm ?_
    exact heq_eq_mp_index hidxP _

/-- The cap operation of the composite is the composite cap operation, read through the transport
of Chow groups along the two readings of the degree. -/
@[simp]
theorem bivariantComposite_cap (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) {T : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sZ) k) :
    (bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc).cap t k α =
      chowGroupDegreeEquiv C (pullback.fst (f ≫ g) t ≫ sX) (by ring : k - q - p = k - (p + q))
        (bivariantCompositeCap C G sX sY sZ f g hf hg (properPushforwardDescends C) p q a b
          t k α) :=
  rfl

/-- The composite class is *the* composite: its cap operation is cap with `b` followed by cap with
`a`, pushed forward along the associativity isomorphism of pullbacks. In particular
`Stacks.Chow.IsBivariantClassComposition` is inhabited, and by
`Stacks.Chow.eq_of_isBivariantClassComposition` the composite class is the unique bivariant class
of degree `p + q` for `f ≫ g` with that cap operation [Stacks, Tag 0FE0].

The formula is stated for an arbitrary Gysin system and so carries its two compatibilities as
hypotheses; `Stacks.Chow.isBivariantClassComposition_bivariantCompositeOfInvertible` is the same
formula at the Gysin system of the first Chern class rule, where both of them are theorems. -/
theorem isBivariantClassComposition_bivariantComposite (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) :
    IsBivariantClassComposition C G sX sY sZ f g hf hg (properPushforwardDescends C) p q a b
      (bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc) :=
  fun t _ _k _α ↦ chowGroupDegreeEquiv_heq C (pullback.fst (f ≫ g) t ≫ sX) _ _

/-! ### Bilinearity -/

/-- The composite is additive in its left argument: both sides cap by the same operation, because
the cap operation of a sum of bivariant classes is the sum of their cap operations and proper
pushforward and the transport of degrees are additive. -/
theorem bivariantComposite_add_left (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) (a₁ a₂ : BivariantClass C G sX sY f hf p)
    (b₀ : BivariantClass C G sY sZ g hg q) :
    bivariantComposite C G sX sY sZ f g hf hg p q (a₁ + a₂) b₀ hgys hgysc =
      bivariantComposite C G sX sY sZ f g hf hg p q a₁ b₀ hgys hgysc +
        bivariantComposite C G sX sY sZ f g hf hg p q a₂ b₀ hgys hgysc := by
  apply BivariantClass.ext
  intro T t _ k α
  simp only [bivariantComposite_cap, bivariantCompositeCap_apply, BivariantClass.add_cap, map_add]

/-- The composite is additive in its right argument: both sides cap by the same operation, because
the cap operation of a sum of bivariant classes is the sum of their cap operations and the cap
operation of `a`, proper pushforward and the transport of degrees are additive. -/
theorem bivariantComposite_add_right (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) (a₀ : BivariantClass C G sX sY f hf p)
    (b₁ b₂ : BivariantClass C G sY sZ g hg q) :
    bivariantComposite C G sX sY sZ f g hf hg p q a₀ (b₁ + b₂) hgys hgysc =
      bivariantComposite C G sX sY sZ f g hf hg p q a₀ b₁ hgys hgysc +
        bivariantComposite C G sX sY sZ f g hf hg p q a₀ b₂ hgys hgysc := by
  apply BivariantClass.ext
  intro T t _ k α
  simp only [bivariantComposite_cap, bivariantCompositeCap_apply, BivariantClass.add_cap, map_add]

/-- The composition `A^p(X ⟶ Y) × A^q(Y ⟶ Z) ⟶ A^{p+q}(X ⟶ Z)` as a bilinear map, that is,
`Stacks.Chow.bivariantComposite` bundled through its additivity in each argument
[Stacks, Tag 0B75]. -/
@[stacks 0B75 "the composition of bivariant classes is bilinear"]
def bivariantCompositeBilinear (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) :
    BivariantClass C G sX sY f hf p →+
      BivariantClass C G sY sZ g hg q →+
        BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) (p + q) :=
  AddMonoidHom.mk'
    (fun a₀ ↦ AddMonoidHom.mk'
      (fun b₀ ↦ bivariantComposite C G sX sY sZ f g hf hg p q a₀ b₀ hgys hgysc)
      (bivariantComposite_add_right C G sX sY sZ f g hf hg p q hgys hgysc a₀))
    (fun a₁ a₂ ↦ AddMonoidHom.ext fun b₀ ↦
      bivariantComposite_add_left C G sX sY sZ f g hf hg p q hgys hgysc a₁ a₂ b₀)

/-- The bilinear composition is the composite. -/
@[simp]
theorem bivariantCompositeBilinear_apply (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) (a₀ : BivariantClass C G sX sY f hf p)
    (b₀ : BivariantClass C G sY sZ g hg q) :
    bivariantCompositeBilinear C G sX sY sZ f g hf hg p q hgys hgysc a₀ b₀ =
      bivariantComposite C G sX sY sZ f g hf hg p q a₀ b₀ hgys hgysc :=
  rfl

end Composite

end Stacks.Chow

end
