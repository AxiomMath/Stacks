module

public import StacksFrontier.AlgebraicGeometry.Duality.GlueingDualizingComplexes
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedDualizingTransitivity
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Associativity
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersionRestriction

/-!
# The upper shriek formalism of a choice of compactifications

The structure `Stacks.Duality.UpperShriek` bundles a functor `f^!` for every separated finite-type
morphism `f` with Noetherian target, the comparisons `k^! ≅ f^! ∘ g^!` of [Stacks, Tag 0ATX] for
factorizations `k = g ∘ f`, the unit `(𝟙_X)^! ≅ 𝟭`, and the associativity and unit laws of
[Stacks, Tag 0ATY]. This file constructs it on `D⁺_QCoh` from compactification data: a
compactification of every such morphism, which is exactly what Nagata's theorem [Stacks, Tag 0F41]
provides.

## Main definitions

* `Stacks.Duality.ftsOf`, `Stacks.Duality.ftsHomOf`: a separated finite-type morphism read as an
  object, and a morphism over the base read as a morphism, of `FTS_S`.
* `Stacks.Duality.UpperShriek.ofCompactifications`: the upper shriek formalism on `D⁺_QCoh`
  attached to a compactification of every shriekable morphism. The functors are those of
  [Stacks, Tag 0A9Y], the comparisons those of [Stacks, Tag 0ATX] and the coherence is
  `Stacks.Duality.upperShriekFactorIso_assoc`.
* `Stacks.Duality.UpperShriek.ofNagata`: the same with the compactifications chosen from the one
  input `∀ f, IsShriekable f → ∃ j : CompactificationOf (Over.mk f), QuasiCompact j.immersion`,
  the shape of the predicate `HasCompactification` of [Stacks, Tag 0F41].
* `Stacks.Duality.UpperShriek.shriekOfIsoOfIsProper`: for proper `f`, `f^!` is the right adjoint
  `a` of `Rf_*` on `D⁺_QCoh`, and `Stacks.Duality.UpperShriek.twistedInverseImageObjIsoOfIsProper`,
  the resulting `a(ω_Y^•) ≅ ω_X^•` of [Stacks, Tag 0AUD] for schemes separated over the base.
* `Stacks.Duality.UpperShriek.shriekOfIsoOfIsOpenImmersion`: for an open immersion `j`, `j^!` is
  restriction on `D⁺_QCoh` at any compactification ([Stacks, Tag 0AU0]).

## Implementation notes

*The base.* `f^!` is constructed for morphisms of `FTS_S`, and only the compactification and the
underlying morphism of schemes enter the functor, not the base `S`. The functor of a shriekable
`f : X ⟶ Y` is taken over `S = Y`, and the comparison of `k = g ∘ f` over the target of `g`.

## References

* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0ATY](https://stacks.math.columbia.edu/tag/0ATY)
* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

/-- A separated finite-type morphism `p : X ⟶ S`, as an object of `FTS_S`. -/
abbrev ftsOf {X S : Scheme.{u}} (p : X ⟶ S) (hp : isSeparatedFiniteType p) : FTS S :=
  MorphismProperty.Over.mk ⊤ p hp

/-- A morphism of schemes over `S` between separated finite-type schemes over `S`, as a morphism
of `FTS_S`. -/
abbrev ftsHomOf {X Y S : Scheme.{u}} (f : X ⟶ Y) {p : X ⟶ S} {q : Y ⟶ S}
    (hp : isSeparatedFiniteType p) (hq : isSeparatedFiniteType q) (e : f ≫ q = p) :
    ftsOf p hp ⟶ ftsOf q hq :=
  MorphismProperty.Over.homMk f e trivial

/-- The identity is separated and of finite type. -/
theorem isSeparatedFiniteType_id (S : Scheme.{u}) : isSeparatedFiniteType (𝟙 S) :=
  ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

namespace UpperShriek

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))

/-- The functor `f^!` of a shriekable `f : X ⟶ Y` at the compactification `c f`, over the base
`Y`. -/
abbrev shriekOf {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsShriekable f) :
    quasiCoherentDerivedCategoryPlusOfModel Y ⥤ quasiCoherentDerivedCategoryPlusOfModel X :=
  haveI := hf.target_noetherian
  upperShriekPlus (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y)
    (Category.comp_id f)) (c f hf)

/-- The comparison `k^! ≅ f^! ∘ g^!` of [Stacks, Tag 0ATX] for `e : f ≫ g = k`, at the
compactifications `c f`, `c g`, `c k`, over the target of `g`. -/
def factorIsoOf {W X Y : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Y} {k : W ⟶ Y} (e : f ≫ g = k)
    (hf : IsShriekable f) (hg : IsShriekable g) (hk : IsShriekable k) :
    shriekOf c k hk ≅ shriekOf c g hg ⋙ shriekOf c f hf := by
  subst e
  haveI := hg.target_noetherian
  exact upperShriekCompIso
    (ftsHomOf f hk.separatedFiniteType hg.separatedFiniteType rfl)
    (ftsHomOf g hg.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id g))
    (c f hf) (c g hg) (c (f ≫ g) hk)

/-- The unit `(𝟙_X)^! ≅ 𝟭` at the compactification `c (𝟙_X)`. -/
def unitIsoOf (X : Scheme.{u}) (h : IsShriekable (𝟙 X)) : shriekOf c (𝟙 X) h ≅ 𝟭 _ := by
  haveI := h.target_noetherian
  exact upperShriekPlusIdIso (ftsOf (𝟙 X) h.separatedFiniteType) (c (𝟙 X) h)

/-- The comparisons `factorIsoOf` are associative: for `h ∘ g ∘ f`, the two composites
`k^! ⟶ f^! g^! h^!` through `(g ∘ h)^!` and through `(f ∘ g)^!` agree. -/
theorem factorIsoOf_assoc {W X Y Z : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z}
    {fg : W ⟶ Y} {gh : X ⟶ Z} {k : W ⟶ Z} (efg : f ≫ g = fg) (egh : g ≫ h = gh)
    (ek : fg ≫ h = k) (ek' : f ≫ gh = k) (hf : IsShriekable f) (hg : IsShriekable g)
    (hh : IsShriekable h) (hfg : IsShriekable fg) (hgh : IsShriekable gh) (hk : IsShriekable k)
    (K : quasiCoherentDerivedCategoryPlusOfModel Z) :
    (factorIsoOf c ek' hf hgh hk).hom.app K ≫
        (shriekOf c f hf).map ((factorIsoOf c egh hg hh hgh).hom.app K) =
      (factorIsoOf c ek hfg hh hk).hom.app K ≫
        (factorIsoOf c efg hf hg hfg).hom.app ((shriekOf c h hh).obj K) := by
  subst efg egh ek
  have := hh.target_noetherian
  exact upperShriekFactorIso_assoc
    (f := ftsHomOf f hk.separatedFiniteType hgh.separatedFiniteType rfl)
    (g := ftsHomOf g hgh.separatedFiniteType hh.separatedFiniteType rfl)
    (h := ftsHomOf h hh.separatedFiniteType (isSeparatedFiniteType_id Z) (Category.comp_id h))
    rfl rfl rfl rfl (c f hf) (c g hg) (c h hh) (c (f ≫ g) hfg) (c (g ≫ h) hgh)
    (c ((f ≫ g) ≫ h) hk) K

/-- Left unit law: the comparison for `𝟙_X ≫ g = g` followed by the unit `(𝟙_X)^! ≅ 𝟭` is the
identity of `g^!`. -/
theorem factorIsoOf_id_comp {X Y : Scheme.{u}} {g : X ⟶ Y} (e : 𝟙 X ≫ g = g)
    (h₁ : IsShriekable (𝟙 X)) (hg : IsShriekable g)
    (K : quasiCoherentDerivedCategoryPlusOfModel Y) :
    (factorIsoOf c e h₁ hg hg).hom.app K ≫ (unitIsoOf c X h₁).hom.app ((shriekOf c g hg).obj K) =
      𝟙 _ := by
  have := hg.target_noetherian
  have e₁ : factorIsoOf c e h₁ hg hg =
      upperShriekFactorIso (f := 𝟙 (ftsOf g hg.separatedFiniteType))
        (g := ftsHomOf g hg.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id g))
        rfl (c (𝟙 X) h₁) (c g hg) (c g hg) := rfl
  have e₂ : unitIsoOf c X h₁ = upperShriekPlusIdIso (ftsOf g hg.separatedFiniteType) (c (𝟙 X) h₁) :=
    rfl
  rw [e₁, e₂]
  exact upperShriekFactorIso_id_comp
    (g := ftsHomOf g hg.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id g))
    rfl (c (𝟙 X) h₁) (c g hg) K

/-- Right unit law: the comparison for `f ≫ 𝟙_Y = f` followed by `f^!` of the unit
`(𝟙_Y)^! ≅ 𝟭` is the identity of `f^!`. -/
theorem factorIsoOf_comp_id {X Y : Scheme.{u}} {f : X ⟶ Y} (e : f ≫ 𝟙 Y = f)
    (hf : IsShriekable f) (h₁ : IsShriekable (𝟙 Y))
    (K : quasiCoherentDerivedCategoryPlusOfModel Y) :
    (factorIsoOf c e hf h₁ hf).hom.app K ≫ (shriekOf c f hf).map ((unitIsoOf c Y h₁).hom.app K) =
      𝟙 _ := by
  have := hf.target_noetherian
  have e₁ : factorIsoOf c e hf h₁ hf =
      upperShriekFactorIso
        (f := ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id f))
        (g := 𝟙 (ftsOf (𝟙 Y) (isSeparatedFiniteType_id Y)))
        rfl (c f hf) (c (𝟙 Y) h₁) (c f hf) := rfl
  have e₂ : unitIsoOf c Y h₁ =
      upperShriekPlusIdIso (ftsOf (𝟙 Y) (isSeparatedFiniteType_id Y)) (c (𝟙 Y) h₁) := rfl
  rw [e₁, e₂]
  exact upperShriekFactorIso_comp_id
    (f := ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id f))
    rfl (c f hf) (c (𝟙 Y) h₁) K

/-- **The upper shriek formalism of a choice of compactifications.** For a compactification
`c f` of every separated finite-type `f` with Noetherian target, the functors `f^!` of
[Stacks, Tag 0A9Y] on `D⁺_QCoh`, the comparisons `k^! ≅ f^! ∘ g^!` of [Stacks, Tag 0ATX] and
their associativity of [Stacks, Tag 0ATY] (`Stacks.Duality.upperShriekFactorIso_assoc`). The unit
`(𝟙_X)^! ≅ 𝟭` and its two laws, the rest of [Stacks, Tag 0ATY], are
`Stacks.Duality.UpperShriek.unitIsoOf`, `Stacks.Duality.UpperShriek.factorIsoOf_id_comp` and
`Stacks.Duality.UpperShriek.factorIsoOf_comp_id`. -/
def ofCompactifications :
    UpperShriek fun X : Scheme.{u} => quasiCoherentDerivedCategoryPlusOfModel X where
  shriek f hf := shriekOf c f hf
  factorIso e hf hg hk := factorIsoOf c e hf hg hk
  factorIso_assoc efg egh ek ek' hf hg hh hfg hgh hk K :=
    factorIsoOf_assoc c efg egh ek ek' hf hg hh hfg hgh hk K

/-- The functor `f^!` of the formalism `ofCompactifications c` is `shriekOf c f hf`. -/
theorem ofCompactifications_shriek {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsShriekable f) :
    (ofCompactifications c).shriek f hf = shriekOf c f hf :=
  rfl

/-- **The upper shriek formalism of Nagata compactifications.** Given the one input that every
separated finite-type morphism with Noetherian target has a compactification (the statement of
[Stacks, Tag 0F41] at the shape of `HasCompactification`), the formalism
`Stacks.Duality.UpperShriek.ofCompactifications` at a chosen compactification of each morphism. -/
def ofNagata (hN : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f →
      ∃ j : CompactificationOf (Over.mk f), QuasiCompact j.immersion) :
    UpperShriek fun X : Scheme.{u} => quasiCoherentDerivedCategoryPlusOfModel X :=
  ofCompactifications fun f hf => (hN f hf).choose

/-- **For a proper shriekable `f`, `f^!` is the right adjoint `a` of `Rf_*`** on `D⁺_QCoh`
([Stacks, Tag 0AA0] and the definition of [Stacks, Tag 0A9Y]): `f^!` at `c f` is `f^!` at the
identity compactification, which is `a`. -/
def shriekOfIsoOfIsProper {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsShriekable f) [IsProper f] :
    haveI := hf.target_noetherian
    haveI := hf.source_noetherian
    shriekOf c f hf ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙
        twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f) :=
  haveI := hf.target_noetherian
  haveI := hf.source_noetherian
  haveI : IsProper (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y)
    (Category.comp_id f)).left := inferInstanceAs (IsProper f)
  Functor.isoWhiskerRight (DominatingCompactification.upperShriekPlusIso
      (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id f))
      (c f hf) (properCompactification
        (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id f))))
      (ObjectProperty.ι _) ≪≫
    upperShriekPlusCompιIso
      (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id f))
      (properCompactification
        (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id f))) ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι _) (upperShriekProperIso
      (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id f)))

/-- **For a shriekable open immersion `j`, `j^!` is restriction** on `D⁺_QCoh`, at the
compactification `c j` ([Stacks, Tag 0AU0] together with [Stacks, Tag 0AA0]). -/
def shriekOfIsoOfIsOpenImmersion {X Y : Scheme.{u}} (j : X ⟶ Y) (hj : IsShriekable j)
    [IsOpenImmersion j] :
    shriekOf c j hj ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ OpenImmersion.restrictedDerivedRestrict j :=
  haveI := hj.target_noetherian
  haveI : IsOpenImmersion (ftsHomOf j hj.separatedFiniteType (isSeparatedFiniteType_id Y)
    (Category.comp_id j)).left := inferInstanceAs (IsOpenImmersion j)
  Functor.isoWhiskerRight (DominatingCompactification.upperShriekPlusIso
      (ftsHomOf j hj.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id j))
      (c j hj) (openCompactification
        (ftsHomOf j hj.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id j))))
      (ObjectProperty.ι _) ≪≫
    upperShriekPlusCompιIso
      (ftsHomOf j hj.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id j))
      (openCompactification
        (ftsHomOf j hj.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id j))) ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι _) (upperShriekIsoRestrictOfOpenImmersion
      (ftsHomOf j hj.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id j)))

/-- **[Stacks, Tag 0AUD] for schemes separated over the base, for the upper shriek functors of
compactifications.** Let `f : X ⟶ Y` be proper, `q : Y ⟶ S` and `p = f ≫ q` separated of finite
type over a Noetherian `S`, and `a` the right adjoint of `Rf_*` ([Stacks, Tag 0A9E]). If
`ω_X^• ≅ p^!ω_S^•` and `ω_Y^• ≅ q^!ω_S^•`, then `a(ω_Y^•) ≅ ω_X^•`. -/
def twistedInverseImageObjIsoOfIsProper {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S}
    {p : X ⟶ S} (hfq : f ≫ q = p) (hf : IsShriekable f) (hq : IsShriekable q)
    (hp : IsShriekable p) [IsProper f] (ωS : quasiCoherentDerivedCategoryPlusOfModel S)
    {ωX : quasiCoherentDerivedCategoryPlusOfModel X}
    {ωY : quasiCoherentDerivedCategoryPlusOfModel Y}
    (nX : ωX ≅ (shriekOf c p hp).obj ωS) (nY : ωY ≅ (shriekOf c q hq).obj ωS) :
    haveI := hf.target_noetherian
    haveI := hf.source_noetherian
    (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj ωY.obj ≅
      ωX.obj :=
  haveI := hf.target_noetherian
  haveI := hf.source_noetherian
  (shriekOfIsoOfIsProper c f hf).symm.app ωY ≪≫
    (ObjectProperty.ι _).mapIso (dualizingIsoRightAdjointObj (ofCompactifications c) hfq hf hq hp
      (Iso.refl _) ωS nX nY)

end UpperShriek

end Stacks.Duality

end
