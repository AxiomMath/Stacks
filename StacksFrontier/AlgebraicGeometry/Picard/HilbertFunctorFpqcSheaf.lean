module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FaithfullyFlatSections
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorOfPoints

/-!
# The Hilbert functor of points and the fpqc sheaf property

Let `X` be a scheme over `S` and let `d` be a natural number. The degree-`d` Hilbert functor of
points of `X` sends an `S`-scheme `T` to the set of closed subschemes of `X ×_S T` which are
finite locally free of rank `d` over `T`, and a morphism of `S`-schemes to base change of such
subschemes. This file constructs that functor and proves the separatedness half of its fpqc
sheaf property.

## Main definitions

* `Stacks.Hilbert.baseChange` — the base change of a degree-`d` Hilbert family along a morphism
  of `S`-schemes.
* `Stacks.Hilbert.hilbertFunctorOfRank` — the degree-`d` Hilbert functor of points, a presheaf
  of sets on the schemes over `S`.

## Main results

* `Stacks.Hilbert.isPullback_familyBaseChangeMap` — the comparison map `X ×_S T' ⟶ X ×_S T`
  exhibits `X ×_S T'` as the fibre product of `X ×_S T` with `T'` over `T`.
* `Stacks.Hilbert.baseChange_id` and `Stacks.Hilbert.baseChange_comp` — functoriality of base
  change, which is what makes `hilbertFunctorOfRank` a functor.
* `Stacks.Hilbert.hilbertFamily_ext_of_baseChange_eq` — a degree-`d` Hilbert family is
  determined by its base changes along a jointly surjective family of flat morphisms.
* `Stacks.Hilbert.isSeparated_fpqcTopology_hilbertFunctorOfRank` — **the separatedness clause of
  Stacks Tag 0B95**: the degree-`d` Hilbert functor is separated for the fpqc topology on the
  schemes over `S`.

## Implementation notes

*Only the separatedness clause of Tag 0B95 is proved here.* The sheaf property of the Hilbert
functor has two halves. Separatedness — a compatible family of families has at most one
amalgamation — is proved here, unconditionally and in full generality: no hypothesis on
`X ⟶ S`, on `d`, or on the covering. The gluing clause — a compatible family of families has an
amalgamation — is the source's appeal to effective descent for closed immersions along an
arbitrary fpqc covering, Stacks 03I0, namely
`AlgebraicGeometry.DescentData.isFamilyEffective_of_isClosedImmersion` of
`StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionFpqcDescent`, which is unconditional. That
half, and with it the full sheaf property
`Stacks.Hilbert.isSheaf_fpqcTopology_hilbertFunctorOfRank`, is proved in
`StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorFpqcGluing`, which imports this file. Nothing
in either file is conditional; the tag records which clause the statement below is.

*How separatedness is proved.* A Hilbert family is recorded by its ideal sheaf, so separatedness
is injectivity of `AlgebraicGeometry.Scheme.IdealSheafData.comap` along the base change of the
covering to `X ×_S T`. That base change is again jointly surjective and flat, by
`Stacks.Hilbert.isPullback_familyBaseChangeMap`, and injectivity of `comap` along such a family
is the identity `⨅ i, (I.comap (q i)).map (q i) = I`. The inequality `≤` of that identity is one
half of the Galois connection `AlgebraicGeometry.Scheme.IdealSheafData.map_gc`; the other half
holds because the upper adjoint `map` preserves infima, which reduces the claim to the
vanishing of the intersection of the kernel ideal sheaves of the family base changed to the
closed subscheme itself. That vanishing is checked on affine opens, where it says that a section
killed by every member of a jointly surjective family of flat morphisms is zero — a flat
morphism is injective on stalks, which is
`AlgebraicGeometry.Scheme.Hom.stalkMap_injective_of_flat`.

*Reduction of the sheaf-theoretic statement to a covering family.* Membership in
`AlgebraicGeometry.Scheme.fpqcTopology.over S` is transported to the fpqc precoverage of `S` by
`CategoryTheory.GrothendieckTopology.mem_over_iff` together with
`CategoryTheory.Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition`, which produces
a covering family refining the given sieve. Separatedness only needs *some* family of arrows of
the sieve to test with, so no passage from the refinement back to the sieve is required; this is
why the proof does not go through the generated sieve.

*The three parts of Section 0B94.* The section states the set `Hilb^d_{X/S}(T)`, which is
`Stacks.Hilbert.HilbertFamily`; that base change along `T' ⟶ T` carries a degree-`d` family
over `T` to one over `T'`, which is `Stacks.Hilbert.baseChange`; and the functor assembled from
these, which is `Stacks.Hilbert.hilbertFunctorOfRank`. The same three sentences in the source's
own vocabulary of closed subschemes `Z ⊂ X_T`, the bijection with the ideal-sheaf form used here,
and the notation `\underline{Hilb}^d_{X/S}` for a representing scheme are in
`StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorClosedSubschemes`. The remaining sentences
are the announcement of Proposition 0B9A, which carries its own tag, and the aside that the
functor is in general an algebraic space, for which the source itself gives no reference.

## References

* [Stacks Project, Tag 0B94](https://stacks.math.columbia.edu/tag/0B94)
* [Stacks Project, Tag 0B95](https://stacks.math.columbia.edu/tag/0B95)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 03I0](https://stacks.math.columbia.edu/tag/03I0)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

/-- Comparing the two fibre products over `S` of a scheme with the members of a morphism
`T' ⟶ T` exhibits `X ×_S T'` as the fibre product of `X ×_S T` with `T'` over `T`. -/
theorem isPullback_pullback_map_snd {S A T T' : Scheme.{u}} (a : A ⟶ S) (b : T ⟶ S)
    (c : T' ⟶ S) (h : T' ⟶ T) (hc : c = h ≫ b)
    (w₁ : a ≫ 𝟙 S = 𝟙 A ≫ a) (w₂ : c ≫ 𝟙 S = h ≫ b) :
    IsPullback (pullback.map a c a b (𝟙 A) h (𝟙 S) w₁ w₂)
      (pullback.snd a c) (pullback.snd a b) h := by
  subst hc
  refine IsPullback.of_right (h₁₂ := pullback.fst a b) ?_ ?_ (IsPullback.of_hasPullback a b)
  · have e : pullback.map a (h ≫ b) a b (𝟙 A) h (𝟙 S) w₁ w₂ ≫ pullback.fst a b =
        pullback.fst a (h ≫ b) := by
      simp only [pullback.map, pullback.lift_fst, Category.comp_id]
    rw [e]
    simpa using IsPullback.of_hasPullback a (h ≫ b)
  · simp only [pullback.map, pullback.lift_snd]

/-- The square comparing `X ×_S T'` with `X ×_S T` over `T' ⟶ T` is cartesian. -/
theorem isPullback_familyBaseChangeMap {S : Scheme.{u}} (X : Over S) {T' T : Over S}
    (g : T' ⟶ T) :
    IsPullback (familyBaseChangeMap X g) ((Over.pullback T'.hom).obj X).hom
      ((Over.pullback T.hom).obj X).hom g.left :=
  isPullback_pullback_map_snd X.hom T.hom T'.hom g.left (Over.w g).symm (by simp) (by simp)

/-- Base changing a closed subscheme of `X ×_S T` to `X ×_S T'` is a cartesian square over
`T' ⟶ T`. -/
theorem isPullback_familyBaseChangeMap_subschemeι {S : Scheme.{u}} (X : Over S)
    {T' T : Over S} (g : T' ⟶ T)
    (I : ((Over.pullback T.hom).obj X).left.IdealSheafData) :
    IsPullback
      ((I.comapIso (familyBaseChangeMap X g)).hom ≫
        pullback.snd (familyBaseChangeMap X g) I.subschemeι)
      ((I.comap (familyBaseChangeMap X g)).subschemeι ≫ ((Over.pullback T'.hom).obj X).hom)
      (I.subschemeι ≫ ((Over.pullback T.hom).obj X).hom) g.left :=
  (AlgebraicGeometry.isPullback_of_isClosedImmersion
      (I.comap (familyBaseChangeMap X g)).subschemeι I.subschemeι _ (familyBaseChangeMap X g)
      (by
        rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Category.assoc,
          pullback.condition])
      (by simp [Scheme.IdealSheafData.ker_subschemeι])).flip.paste_vert
    (isPullback_familyBaseChangeMap X g)

/-- **Stacks Project, Section 0B94.** The base change of a degree-`d` Hilbert family along a
morphism of `S`-schemes: the closed subscheme cut out by the pullback of its ideal sheaf.

This is the section's assertion that for a morphism `T' ⟶ T` over `S` and a
`Z ∈ Hilb^d_{X/S}(T)` the base change `Z_{T'} ⊂ X_{T'}` is again an element of
`Hilb^d_{X/S}(T')` — the type below says exactly that, and it is the one part of the section
that requires an argument. That the resulting closed subscheme really is `Z_{T'}`, that is that
its ideal sheaf is the pullback of `Z`'s, is `Stacks.Hilbert.baseChange_ideal`. The set
`Hilb^d_{X/S}(T)` is `Stacks.Hilbert.HilbertFamily` and the functor is
`Stacks.Hilbert.hilbertFunctorOfRank`. -/
@[stacks 0B94 "base change of families: that for a morphism `T' ⟶ T` over `S` and a `Z` in \
`Hilb^d_{X/S}(T)` the base change `Z_{T'} ⊂ X_{T'}` lies in `Hilb^d_{X/S}(T')`.  This is the \
part of the section that requires an argument; the set `Hilb^d_{X/S}(T)` is \
`Stacks.Hilbert.HilbertFamily` and the functor is `Stacks.Hilbert.hilbertFunctorOfRank`"]
def baseChange {S : Scheme.{u}} (X : Over S) {T' T : Over S} {d : ℕ} (g : T' ⟶ T)
    (Z : HilbertFamily X T d) : HilbertFamily X T' d where
  ideal := Z.ideal.comap (familyBaseChangeMap X g)
  isFiniteLocallyFreeOfRank :=
    have := Z.isFiniteLocallyFreeOfRank
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (isPullback_familyBaseChangeMap_subschemeι X g Z.ideal)

/-- The ideal sheaf of a base-changed Hilbert family is the pullback of the original one. -/
theorem baseChange_ideal {S : Scheme.{u}} (X : Over S) {T' T : Over S} {d : ℕ} (g : T' ⟶ T)
    (Z : HilbertFamily X T d) :
    (baseChange X g Z).ideal = Z.ideal.comap (familyBaseChangeMap X g) :=
  rfl

/-- The comparison map for the identity is the identity. -/
theorem familyBaseChangeMap_id {S : Scheme.{u}} (X : Over S) (T : Over S) :
    familyBaseChangeMap X (𝟙 T) = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_ <;>
    simp [familyBaseChangeMap, pullback.map]

/-- The comparison maps compose. -/
theorem familyBaseChangeMap_comp {S : Scheme.{u}} (X : Over S) {T'' T' T : Over S}
    (g : T'' ⟶ T') (h : T' ⟶ T) :
    familyBaseChangeMap X (g ≫ h) = familyBaseChangeMap X g ≫ familyBaseChangeMap X h := by
  refine pullback.hom_ext ?_ ?_ <;>
    simp only [familyBaseChangeMap, pullback.map, Category.assoc, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc, Over.comp_left]

/-- Base change along the identity does nothing. -/
theorem baseChange_id {S : Scheme.{u}} (X : Over S) {T : Over S} {d : ℕ}
    (Z : HilbertFamily X T d) : baseChange X (𝟙 T) Z = Z := by
  refine HilbertFamily.ext ?_
  rw [baseChange_ideal, familyBaseChangeMap_id, Scheme.IdealSheafData.comap_id]

/-- Base change along a composite is the composite of the base changes. -/
theorem baseChange_comp {S : Scheme.{u}} (X : Over S) {T'' T' T : Over S} {d : ℕ}
    (g : T'' ⟶ T') (h : T' ⟶ T) (Z : HilbertFamily X T d) :
    baseChange X (g ≫ h) Z = baseChange X g (baseChange X h Z) := by
  refine HilbertFamily.ext ?_
  rw [baseChange_ideal, baseChange_ideal, baseChange_ideal, familyBaseChangeMap_comp,
    Scheme.IdealSheafData.comap_comp]

/-- **Stacks Project, Section 0B94.** The degree-`d` Hilbert functor of points of `X` over `S`.
It sends an `S`-scheme `T` to the degree-`d` Hilbert families in `X` over `T` and a morphism to
the base change of families.

This is the functor `Hilb^d_{X/S} : (Sch/S)ᵒᵖ ⥤ Sets` of the section, for an arbitrary morphism
`X ⟶ S` of schemes and an arbitrary degree `d`. Its values are
`Stacks.Hilbert.HilbertFamily`, which carries the other part of the section; that base change
of a degree-`d` family is again one, which is what makes the assignment a functor, is
`Stacks.Hilbert.baseChange` together with `Stacks.Hilbert.baseChange_id` and
`Stacks.Hilbert.baseChange_comp`. -/
@[stacks 0B94 "the functor `Hilb^d_{X/S} : (Sch/S)ᵒᵖ ⥤ Sets` itself, acting on morphisms by \
base change of families.  Its values, the sets `Hilb^d_{X/S}(T)`, are \
`Stacks.Hilbert.HilbertFamily`, which carries the other part of this section"]
def hilbertFunctorOfRank {S : Scheme.{u}} (X : Over S) (d : ℕ) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := HilbertFamily X T.unop d
  map g := ↾fun Z ↦ baseChange X g.unop Z
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro Z
    exact baseChange_id X Z
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro Z
    exact baseChange_comp X h.unop g.unop Z

/-! ### Faithfully flat families detect sections and ideal sheaves -/

/-- A section of a scheme killed by every member of a jointly surjective family of flat
morphisms is zero: a flat morphism is injective on stalks, and every point of the base is in
the image of some member. -/
private theorem eq_zero_of_app_eq_zero_of_flat_family {Z : Scheme.{u}} {ι : Type*}
    {V : ι → Scheme.{u}} (q : ∀ i, V i ⟶ Z) (hflat : ∀ i, Flat (q i))
    (hsurj : ∀ z : Z, ∃ i, ∃ y : V i, q i y = z) (U : Z.Opens) {s : Γ(Z, U)}
    (h : ∀ i, ((q i).app U).hom s = 0) : s = 0 := by
  have key (i : ι) (y : V i) (hy : q i y ∈ U) : Z.presheaf.germ U (q i y) hy s = 0 := by
    have := hflat i
    refine (q i).stalkMap_injective_of_flat y ?_
    rw [map_zero, Scheme.Hom.germ_stalkMap_apply, h i, map_zero]
  refine TopCat.Presheaf.section_ext Z.sheaf U s 0 fun x hx ↦ ?_
  obtain ⟨i, y, rfl⟩ := hsurj x
  rw [map_zero]
  exact key i y hx

/-- The kernels of a jointly surjective family of flat morphisms meet in the zero ideal
sheaf. -/
private theorem iInf_ker_eq_bot {Z : Scheme.{u}} {ι : Type*} {V : ι → Scheme.{u}}
    (q : ∀ i, V i ⟶ Z) (hflat : ∀ i, Flat (q i))
    (hsurj : ∀ z : Z, ∃ i, ∃ y : V i, q i y = z) : ⨅ i, (q i).ker = ⊥ := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U : Z.affineOpens ↦ U)
    (iSup_affineOpens_eq_top Z) fun U ↦ ?_
  simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  refine le_antisymm (fun s hs ↦ ?_) bot_le
  exact Ideal.mem_bot.mpr (eq_zero_of_app_eq_zero_of_flat_family q hflat hsurj U.1 fun i ↦
    (q i).ideal_ker_le U (Scheme.IdealSheafData.le_def.mp (iInf_le (fun i ↦ (q i).ker) i) U hs))

/-- Base changing a jointly surjective family of flat morphisms along a morphism `f` gives a
jointly surjective family of flat morphisms. -/
private theorem flat_and_surj_of_isPullback {W W' : Scheme.{u}} {ι : Type*}
    {V P : ι → Scheme.{u}} {f : W' ⟶ W} {q : ∀ i, V i ⟶ W} {p : ∀ i, P i ⟶ W'}
    {r : ∀ i, P i ⟶ V i} (sq : ∀ i, IsPullback (p i) (r i) f (q i)) (hflat : ∀ i, Flat (q i))
    (hsurj : ∀ w : W, ∃ i, ∃ y : V i, q i y = w) :
    (∀ i, Flat (p i)) ∧ ∀ w : W', ∃ i, ∃ y : P i, p i y = w := by
  refine ⟨fun i ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback (sq i).flip (hflat i),
    fun w ↦ ?_⟩
  obtain ⟨i, y, hy⟩ := hsurj (f w)
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback w y hy.symm
  exact ⟨i, (sq i).isoPullback.inv z, by rwa [← Scheme.Hom.comp_apply, (sq i).isoPullback_inv_fst]⟩

/-- An ideal sheaf is recovered from its pullbacks along a jointly surjective family of flat
morphisms: it is the intersection of the scheme-theoretic images of those pullbacks. -/
private theorem iInf_map_comap_eq_self {W : Scheme.{u}} {ι : Type*} {V : ι → Scheme.{u}}
    (q : ∀ i, V i ⟶ W) (hflat : ∀ i, Flat (q i))
    (hsurj : ∀ w : W, ∃ i, ∃ y : V i, q i y = w) (I : W.IdealSheafData) :
    ⨅ i, (I.comap (q i)).map (q i) = I := by
  have key (i : ι) : (I.comap (q i)).map (q i) =
      (pullback.snd (q i) I.subschemeι).ker.map I.subschemeι := by
    calc (I.comap (q i)).map (q i)
        = ((I.comap (q i)).subschemeι ≫ q i).ker := by
          rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι]
      _ = ((I.comapIso (q i)).hom ≫
            pullback.snd (q i) I.subschemeι ≫ I.subschemeι).ker := by
          rw [← Scheme.IdealSheafData.comapIso_hom_fst I (q i), Category.assoc,
            pullback.condition]
      _ = (pullback.snd (q i) I.subschemeι ≫ I.subschemeι).ker :=
          Scheme.Hom.ker_comp_of_isIso _ _
      _ = (pullback.snd (q i) I.subschemeι).ker.map I.subschemeι :=
          (Scheme.IdealSheafData.map_ker _ _).symm
  obtain ⟨hflat', hsurj'⟩ := flat_and_surj_of_isPullback
    (fun i ↦ (IsPullback.of_hasPullback (q i) I.subschemeι).flip) hflat hsurj
  calc ⨅ i, (I.comap (q i)).map (q i)
      = ⨅ i, (pullback.snd (q i) I.subschemeι).ker.map I.subschemeι := by simp_rw [key]
    _ = (⨅ i, (pullback.snd (q i) I.subschemeι).ker).map I.subschemeι :=
        ((Scheme.IdealSheafData.map_gc I.subschemeι).u_iInf).symm
    _ = (⊥ : I.subscheme.IdealSheafData).map I.subschemeι := by
        rw [iInf_ker_eq_bot _ hflat' hsurj']
    _ = I := by rw [Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]

/-- Two ideal sheaves with the same pullbacks along a jointly surjective family of flat
morphisms are equal. -/
private theorem idealSheafData_ext_of_comap_eq {W : Scheme.{u}} {ι : Type*}
    {V : ι → Scheme.{u}} (q : ∀ i, V i ⟶ W) (hflat : ∀ i, Flat (q i))
    (hsurj : ∀ w : W, ∃ i, ∃ y : V i, q i y = w) {I J : W.IdealSheafData}
    (h : ∀ i, I.comap (q i) = J.comap (q i)) : I = J := by
  rw [← iInf_map_comap_eq_self q hflat hsurj I, ← iInf_map_comap_eq_self q hflat hsurj J]
  exact iInf_congr fun i ↦ by rw [h i]

/-- **Ideal sheaves are determined by their pullbacks along a flat cover.** Two ideal sheaves
with the same pullbacks along a jointly surjective family of flat morphisms are equal. -/
alias idealSheafData_eq_of_comap_eq := idealSheafData_ext_of_comap_eq

/-- In a cartesian square of schemes, a point of one factor whose image agrees with the image
of a point of the other factor is hit by the fibre product. -/
theorem exists_preimage_of_isPullback {P A B D : Scheme.{u}} {p₁ : P ⟶ A} {p₂ : P ⟶ B}
    {f : A ⟶ D} {g : B ⟶ D} (sq : IsPullback p₁ p₂ f g) (a : A) (b : B) (e : f a = g b) :
    ∃ v : P, p₁ v = a := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback a b e
  refine ⟨sq.isoPullback.inv z, ?_⟩
  rwa [← Scheme.Hom.comp_apply, sq.isoPullback_inv_fst]

/-! ### The separatedness clause of the fpqc sheaf property -/

/-- **Hilbert families are determined by their base changes along a flat cover.** Two
degree-`d` Hilbert families in `X` over `T` whose base changes along a jointly surjective family
of flat morphisms to `T` agree are equal. -/
theorem hilbertFamily_ext_of_baseChange_eq {S : Scheme.{u}} (X : Over S) {T : Over S} {d : ℕ}
    {ι : Type*} {Y : ι → Over S} (g : ∀ i, Y i ⟶ T) (hflat : ∀ i, Flat (g i).left)
    (hsurj : ∀ t : T.left, ∃ i, ∃ y : (Y i).left, (g i).left y = t)
    {Z W : HilbertFamily X T d} (h : ∀ i, baseChange X (g i) Z = baseChange X (g i) W) :
    Z = W := by
  obtain ⟨hflat', hsurj'⟩ := flat_and_surj_of_isPullback
    (fun i ↦ isPullback_familyBaseChangeMap X (g i)) (fun i ↦ hflat i) hsurj
  exact HilbertFamily.ext (idealSheafData_ext_of_comap_eq
    (fun i ↦ familyBaseChangeMap X (g i)) hflat' hsurj'
    (fun i ↦ by rw [← baseChange_ideal, ← baseChange_ideal, h i]))

/-- **Stacks Project, Tag 0B95, separatedness.** The degree-`d` Hilbert functor of points of `X`
over `S` is separated for the fpqc topology on the schemes over `S`: a section has at most one
amalgamation along any fpqc covering sieve. -/
@[stacks 0B95 "the separatedness clause of the sheaf property"]
theorem isSeparated_fpqcTopology_hilbertFunctorOfRank {S : Scheme.{u}} (X : Over S) (d : ℕ) :
    Presieve.IsSeparated (Scheme.fpqcTopology.over S) (hilbertFunctorOfRank X d) := by
  intro T Q hQ x t₁ t₂ h₁ h₂
  rw [GrothendieckTopology.mem_over_iff,
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hQ
  obtain ⟨R, hR, hle⟩ := hQ
  obtain ⟨ι, C, g, rfl⟩ := R.exists_eq_ofArrows
  have hdata := (Scheme.presieve₀_mem_precoverage_iff (P := @Flat)
      (⟨ι, C, g⟩ : PreZeroHypercover T.left)).mp
    (Scheme.propQCPrecoverage_le_precoverage (P := @Flat) T.left hR)
  refine hilbertFamily_ext_of_baseChange_eq X
    (fun i ↦ (Over.homMk (g i) rfl : Over.mk (g i ≫ T.hom) ⟶ T)) (fun i ↦ hdata.2 i)
    (fun t ↦ hdata.1 t) fun i ↦ ?_
  have hmem : Q (Over.homMk (g i) rfl : Over.mk (g i ≫ T.hom) ⟶ T) :=
    (Sieve.overEquiv_iff Q (g i)).mp (hle _ _ (Presieve.ofArrows.mk i))
  exact (h₁ _ hmem).trans (h₂ _ hmem).symm

end Stacks.Hilbert

end
