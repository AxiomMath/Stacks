module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Class

/-!
# Associativity of the composition of bivariant classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let
`f : X ⟶ Y`, `g : Y ⟶ Z` and `h : Z ⟶ W` be morphisms of schemes locally of finite type over `S`
and let `a ∈ A^p(X ⟶ Y)`, `b ∈ A^q(Y ⟶ Z)` and `c ∈ A^r(Z ⟶ W)` be bivariant classes. The
paragraph of Stacks 0B75 following Stacks 0B76 asserts, of the composition

  `A^p(X ⟶ Y) × A^q(Y ⟶ Z) ⟶ A^{p+q}(X ⟶ Z)`

given by `Stacks.Chow.bivariantCompositeBilinear`, that it is
**associative**:

  `(a ∘ b) ∘ c = a ∘ (b ∘ c)` in `A^{p+q+r}(X ⟶ W)`.

The two sides are indexed by the degrees `(p + q) + r` and `p + (q + r)`, the same integer written
two ways, so the equality is heterogeneous; the morphisms `(f ≫ g) ≫ h` and `f ≫ (g ≫ h)` need no
such transport, composition of schemes being associative definitionally. The geometric content is
that the two ways of pasting the squares of `X ⟶ Y ⟶ Z ⟶ W` over a test scheme `t : T ⟶ W` agree:
both identify `((T ×_W Z) ×_Z Y) ×_Y X` with `T ×_W X` by the same morphism, which is
`Stacks.Chow.pullbackRightPullbackFstIso_assoc_hom`. Associativity carries exactly the hypotheses
`Stacks.Chow.bivariantComposite` carries, namely the two cases of Stacks 02TA for the Gysin
system, without which the composites it compares do not exist.

## Main results

* `Stacks.Chow.bivariantComposite_assoc` — Stacks 0B75, the asserted associativity of the
  composition.
* `Stacks.Chow.bivariantCompositeBilinear_assoc` — the same statement read on the bilinear map
  `Stacks.Chow.bivariantCompositeBilinear`.
* `Stacks.Chow.bivariantComposite_assoc_cap` — the cap-operation identity the proof rests on.
* `Stacks.Chow.pullbackRightPullbackFstIso_assoc_hom` — the coherence of the two pastings of
  pullback squares, which is the geometric content.
* `Stacks.Chow.BivariantClass.heq_of_cap_heq` — a bivariant class is determined by its cap
  operations, across an equality of degrees.

## References

* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Bivariant classes of two equal degrees -/

/-- A bivariant class is determined by its cap operations, across an equality of degrees: two
classes for the same morphism whose degrees are the same integer written two ways are
heterogeneously equal as soon as all their cap operations are. -/
theorem BivariantClass.heq_of_cap_heq (C : ChowSituation.{u}) (G : GysinSystem C)
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (w : X ⟶ Y) [LocallyOfFiniteType w] (hw : w ≫ sY = sX) {d e : ℤ}
    (hde : d = e) (c : BivariantClass C G sX sY w hw d) (c' : BivariantClass C G sX sY w hw e)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t] (k : ℤ)
      (α : chowGroup C (t ≫ sY) k), c.cap t k α ≍ c'.cap t k α) :
    c ≍ c' := by
  subst hde
  refine heq_of_eq (BivariantClass.ext C G sX sY w hw d ?_)
  intro T t ht k α
  exact eq_of_heq (H t k α)

/-- The cap operation of a bivariant class absorbs the transport of a Chow group along an equality
of degrees, the transport on the right being taken along the reflexivity of the common degree. -/
private theorem cap_chowGroupDegreeEquiv (C : ChowSituation.{u}) (G : GysinSystem C)
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)
    (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    {k l : ℤ} (hkl : k = l) (hkl' : k - p = l - p) (α : chowGroup C (g ≫ sY) k) :
    c.cap g l (chowGroupDegreeEquiv C (g ≫ sY) hkl α) =
      chowGroupDegreeEquiv C (pullback.fst f g ≫ sX) hkl' (c.cap g k α) :=
  (c.cap_transport_eq g hkl hkl' rfl α).symm

/-! ### The coherence of the two pullback-square pastings -/

/-- For `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ W` and a test morphism `t : T ⟶ W`, the two ways of
identifying `((T ×_W Z) ×_Z Y) ×_Y X` with `T ×_W X` agree: pasting first the square of `f` over
`g` and then the result over `h` gives the same morphism as pasting first the square of `g` over
`h` and then `f` over the composite. -/
theorem pullbackRightPullbackFstIso_assoc_hom {X Y Z W T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ W) (t : T ⟶ W) :
    (pullbackRightPullbackFstIso g (pullback.fst h t) f).hom ≫
        (pullbackRightPullbackFstIso h t (f ≫ g)).hom =
      (testBaseChangeIso f (pullback.fst (g ≫ h) t) (pullbackRightPullbackFstIso h t g).hom
            (pullback.fst g (pullback.fst h t)) (pullbackRightPullbackFstIso_hom_fst h t g)).hom ≫
        (pullbackRightPullbackFstIso (g ≫ h) t f).hom := by
  refine pullback.hom_ext ?_ ?_
  · change _ = _ ≫ pullback.fst (f ≫ g ≫ h) t
    simp [pullbackRightPullbackFstIso_hom_fst]
  · change _ = _ ≫ pullback.snd (f ≫ g ≫ h) t
    simp [pullbackRightPullbackFstIso_hom_snd]

/-! ### Associativity -/

section Assoc

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z W : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (g : Y ⟶ Z) [LocallyOfFiniteType g] (h : Z ⟶ W)
  [LocallyOfFiniteType h] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (hh : h ≫ sW = sZ) (p q r : ℤ)
  (a : BivariantClass C G sX sY f hf p) (b : BivariantClass C G sY sZ g hg q)
  (c : BivariantClass C G sZ sW h hh r)

/-- The two triple composites of three bivariant classes cap the same way on every test scheme and
every Chow class: both are cap with `c`, then with `b`, then with `a`, pushed forward to `T ×_W X`
along the pasting of the three pullback squares, and the two pastings agree by
`Stacks.Chow.pullbackRightPullbackFstIso_assoc_hom`. The degrees `k - ((p + q) + r)` and
`k - (p + (q + r))` are the same integer written two ways, whence the heterogeneous equality. -/
theorem bivariantComposite_assoc_cap (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) {T : Scheme.{u}} (t : T ⟶ W)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sW) k) :
    (bivariantComposite C G sX sZ sW (f ≫ g) h (comp_comp_structureMorphism_eq hf hg) hh (p + q) r
          (bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc) c hgys hgysc).cap t k
        α ≍
      (bivariantComposite C G sX sY sW f (g ≫ h) hf (comp_comp_structureMorphism_eq hg hh) p
          (q + r) a (bivariantComposite C G sY sZ sW g h hg hh q r b c hgys hgysc) hgys
          hgysc).cap t k α := by
  -- The last pasting isomorphism lands in `pullback ((f ≫ g) ≫ h) t` only up to the definitional
  -- associativity of composition, which instance search does not see; name its properness.
  have hpr : IsProper (Y := pullback ((f ≫ g) ≫ h) t)
      (pullbackRightPullbackFstIso (g ≫ h) t f).hom :=
    inferInstanceAs (IsProper (pullbackRightPullbackFstIso (g ≫ h) t f).hom)
  have hcomp := properChowPushforward_comp_eq C
    (pullback.fst f (pullback.fst g (pullback.fst h t)) ≫ sX)
    (pullback.fst (f ≫ g) (pullback.fst h t) ≫ sX)
    (pullback.fst f (pullback.fst (g ≫ h) t) ≫ sX)
    (pullback.fst ((f ≫ g) ≫ h) t ≫ sX)
    (pullbackRightPullbackFstIso g (pullback.fst h t) f).hom
    (pullbackRightPullbackFstIso h t (f ≫ g)).hom
    (testBaseChangeIso f (pullback.fst (g ≫ h) t) (pullbackRightPullbackFstIso h t g).hom
      (pullback.fst g (pullback.fst h t)) (pullbackRightPullbackFstIso_hom_fst h t g)).hom
    (pullbackRightPullbackFstIso (g ≫ h) t f).hom
    (pullbackRightPullbackFstIso_assoc_hom f g h t)
    (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g (pullback.fst h t))
    (pullbackRightPullbackFstIso_hom_comp_fst_comp sX (f ≫ g) h t)
    (by rw [← Category.assoc, testBaseChangeIso_hom_fst])
    (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f (g ≫ h) t)
    (k - r - q - p)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (a.cap (pullback.fst g (pullback.fst h t)) (k - r - q)
      (b.cap (pullback.fst h t) (k - r) (c.cap t k α)))
  simp only [bivariantComposite_cap, bivariantCompositeCap_apply]
  rw [cap_chowGroupDegreeEquiv C G sX sY f hf p a (pullback.fst (g ≫ h) t)
      (show k - r - q = k - (q + r) by ring) (show k - r - q - p = k - (q + r) - p by ring),
    a.proper_naturality_of_test_eq (pullback.fst (g ≫ h) t)
      (pullbackRightPullbackFstIso h t g).hom (pullback.fst g (pullback.fst h t))
      (pullbackRightPullbackFstIso_hom_fst h t g)
      (testBaseChangeIso f (pullback.fst (g ≫ h) t) (pullbackRightPullbackFstIso h t g).hom
        (pullback.fst g (pullback.fst h t)) (pullbackRightPullbackFstIso_hom_fst h t g)).hom
      (IsPullback.of_vert_isIso ⟨by simp⟩) (testBaseChangeIso_hom_fst f
        (pullback.fst (g ≫ h) t) (pullbackRightPullbackFstIso h t g).hom
        (pullback.fst g (pullback.fst h t)) (pullbackRightPullbackFstIso_hom_fst h t g))
      (k - r - q) (by rw [← Category.assoc, pullbackRightPullbackFstIso_hom_fst])
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)]
  refine HEq.trans (chowGroupDegreeEquiv_heq C _ _ _)
    (HEq.trans ?_ (chowGroupDegreeEquiv_heq C _ _ _).symm)
  rw [← chowGroupDegreeEquiv_properChowPushforward_comp C _ _
      (pullbackRightPullbackFstIso h t (f ≫ g)).hom _
      (show k - r - q - p = k - r - (p + q) by ring)
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _),
    ← chowGroupDegreeEquiv_properChowPushforward_comp C _ _
      (pullbackRightPullbackFstIso (g ≫ h) t f).hom _
      (show k - r - q - p = k - (q + r) - p by ring)
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)]
  exact HEq.trans (chowGroupDegreeEquiv_heq C _ _ _)
    (HEq.trans (heq_of_eq hcomp) (chowGroupDegreeEquiv_heq C _ _ _).symm)

/-- The composition of bivariant classes is associative: for `a ∈ A^p(X ⟶ Y)`, `b ∈ A^q(Y ⟶ Z)`
and `c ∈ A^r(Z ⟶ W)` the two triple composites `(a ∘ b) ∘ c` and `a ∘ (b ∘ c)` agree in
`A^{p+q+r}(X ⟶ W)`, the equality being heterogeneous because the two sides are indexed by
`(p + q) + r` and `p + (q + r)` [Stacks, Tag 0B75]. -/
@[stacks 0B75 "the composition of bivariant classes is associative: for a ∈ A^p(X ⟶ Y), \
b ∈ A^q(Y ⟶ Z) and c ∈ A^r(Z ⟶ W) the triple composites (a ∘ b) ∘ c and a ∘ (b ∘ c) agree in \
A^{p+q+r}(X ⟶ W), the degrees (p + q) + r and p + (q + r) being the same integer written two ways"]
theorem bivariantComposite_assoc (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) :
    bivariantComposite C G sX sZ sW (f ≫ g) h (comp_comp_structureMorphism_eq hf hg) hh (p + q) r
        (bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc) c hgys hgysc ≍
      bivariantComposite C G sX sY sW f (g ≫ h) hf (comp_comp_structureMorphism_eq hg hh) p
        (q + r) a (bivariantComposite C G sY sZ sW g h hg hh q r b c hgys hgysc) hgys hgysc := by
  refine BivariantClass.heq_of_cap_heq C G sX sW ((f ≫ g) ≫ h)
    (comp_comp_structureMorphism_eq (comp_comp_structureMorphism_eq hf hg) hh)
    (add_assoc p q r) _ _ ?_
  intro T t ht k α
  exact bivariantComposite_assoc_cap C G sX sY sZ sW f g h hf hg hh p q r a b c hgys hgysc t k α

/-- Associativity of the composition, read on the bilinear map
`Stacks.Chow.bivariantCompositeBilinear` that bundles it [Stacks, Tag 0B75]. -/
@[stacks 0B75 "the bilinear composition A^p(X ⟶ Y) × A^q(Y ⟶ Z) ⟶ A^{p+q}(X ⟶ Z) is associative"]
theorem bivariantCompositeBilinear_assoc (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) :
    bivariantCompositeBilinear C G sX sZ sW (f ≫ g) h (comp_comp_structureMorphism_eq hf hg) hh
          (p + q) r hgys hgysc
        (bivariantCompositeBilinear C G sX sY sZ f g hf hg p q hgys hgysc a b) c ≍
      bivariantCompositeBilinear C G sX sY sW f (g ≫ h) hf
        (comp_comp_structureMorphism_eq hg hh) p (q + r) hgys hgysc a
        (bivariantCompositeBilinear C G sY sZ sW g h hg hh q r hgys hgysc b c) := by
  simp only [bivariantCompositeBilinear_apply]
  exact bivariantComposite_assoc C G sX sY sZ sW f g h hf hg hh p q r a b c hgys hgysc

end Assoc

end Stacks.Chow

end
