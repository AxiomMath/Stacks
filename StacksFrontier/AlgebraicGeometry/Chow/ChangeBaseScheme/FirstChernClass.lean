module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionGysinRetraction
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.TotalSpaceComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# The first Chern class under a change of the base scheme

Let `B` be a flat base change of Chow situations with dimension shift `c` — a flat morphism
`g : S' ⟶ S` of the two bases whose dimension functions differ by `c` on the generic points of
the fibres of `g`, which is [Stacks, Tag 0FVG] — let `X` be locally of finite type over `S` and
let `ℒ` be an invertible `𝒪_X`-module with base change `ℒ'` on `X' = X ×_S S'`. This file proves
[Stacks, Tag 0FVM]: the square

  `CH_k(X) ⟶ CH_{k+c}(X')`, `CH_{k-1}(X) ⟶ CH_{k+c-1}(X')`

whose horizontal arrows are the base-change map `g^*` of [Stacks, Tag 0FVJ] and whose vertical
arrows are `c₁(ℒ) ∩ -` and `c₁(ℒ') ∩ -` commutes.

## The source's argument, and how it is carried out here

Let `p : L ⟶ X` be the line bundle attached to `ℒ` with zero section `o : X ⟶ L`. By clause (5)
of [Stacks, Tag 0F96] the class `β = c₁(ℒ) ∩ α` satisfies `o_*α = -p^*β`, and by clause (4) of
the same tag `p^*` is injective, so `β` is the **unique** class with that property. The source
then says: the same characterization holds after base change, so the lemma follows from
[Stacks, Tag 0FVK] (flat pullback commutes with base change, applied to `p`) and
[Stacks, Tag 0FVL] (proper pushforward commutes with base change, applied to `o`).

Carrying that out needs one comparison of schemes. The base change `L ×_S S'` is the fibre
product the two tags work over, while the line bundle of `ℒ'` is
`Stacks.LineBundle.Situation.totalSpace` of the base-changed situation
`Stacks.LineBundle.Situation.baseChange`, which clause (5) is stated for. Those two schemes are
canonically isomorphic, because both are cartesian over `p` and `X' ⟶ X`:
`Stacks.LineBundle.Situation.isPullback_baseChange` for the first and
`Stacks.Chow.isPullback_baseChangeMorphism` for the second. The isomorphism
`Stacks.Chow.lineBundleBaseChangeIso` between them is what transports clause (5) from the one to
the other, and that transport is `Stacks.Chow.zeroSectionBaseChange_chowPushforward_eq_neg`. That
the zero section of `Tot(ℒ')` is carried to the zero section of `Tot(ℒ)` by the canonical
morphism is `Stacks.LineBundle.Situation.zeroSection_comp_baseChangeToTotalSpace` of
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.TotalSpaceComparison`.

Both transports are along an isomorphism over `S'`, so nothing beyond the following is needed:
proper pushforward is functorial (`Stacks.Chow.properChowPushforward_comp`), and flat pullback
commutes with pushforward along isomorphisms in a commuting square
(`Stacks.Chow.flatPullbackChow_chowPushforwardOfIso`).

## Main definitions

* `Stacks.Chow.lineBundleBaseChangeIso` — the isomorphism `Tot(ℒ') ≅ Tot(ℒ) ×_S S'` over `S'`,
  from the two cartesian squares over `p : Tot(ℒ) ⟶ X` and `X' ⟶ X`.

## Main results

* `Stacks.Chow.properChowPushforward_baseChangeChowPullback_of_base` — [Stacks, Tag 0FVL], the
  Chow square, with the structure morphism of the source an independent morphism and the
  factorization a hypothesis, and with the base-changed morphism a parameter pinned down by its
  two projections. This is the shape the zero section needs: `o` composes with the structure
  morphism of `Tot(ℒ)` to the structure morphism of `X`, not to a syntactic composite.
* `Stacks.Chow.baseChange_flatPullbackChow_apply` — [Stacks, Tag 0FVK], the Chow square, read as
  an equality of classes through `Stacks.Chow.chowGroupCast` rather than as a heterogeneous
  equality of homomorphisms.
* `Stacks.Chow.zeroSectionBaseChange_chowPushforward_eq_neg` — clause (5) of
  [Stacks, Tag 0F96] for the base-changed line bundle, transported to the fibre product
  `Tot(ℒ) ×_S S'`.
* `Stacks.Chow.baseChange_firstChernClassCapChow` — **[Stacks, Tag 0FVM]**: the square of Chow
  groups commutes.

## Implementation notes

The cap product `Stacks.Chow.firstChernClassCapChow` of [Stacks, Tag 02TI] is indexed by the
degree of its *value*, so `c₁(ℒ) ∩ - : CH_{k+1}(X) ⟶ CH_k(X)` is `firstChernClassCapChow C k`.
The square of the source is therefore written here at `k + 1` in the top row; since the source
states it for every `k ∈ ℤ`, nothing is lost. The two descriptions `(k + 1) + c` and
`(k + c) + 1` of the degree of the base change of the top-left corner differ by associativity
and commutativity of addition in `ℤ`, and the transport between them is
`Stacks.Chow.chowGroupCast`.

The invertible module on `X'` is `(D.baseChange g).L`, which **is**
`(Scheme.Modules.pullback g).obj D.L` — the base change of `ℒ` — by
`Stacks.LineBundle.Situation.baseChange_L`, which holds by `rfl`. It is written through the
base-changed situation so that its invertibility is the structure field
`Stacks.LineBundle.Situation.invertible` rather than a separately supplied instance.

## References

* [Stacks Project, Tag 0FVM](https://stacks.math.columbia.edu/tag/0FVM)
* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVJ](https://stacks.math.columbia.edu/tag/0FVJ)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
* [Stacks Project, Tag 0FVL](https://stacks.math.columbia.edu/tag/0FVL)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 0B74](https://stacks.math.columbia.edu/tag/0B74)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transports along an equality of degrees -/

/-- A family of homomorphisms of Chow groups commutes with the transport along an equality of
degrees. -/
private theorem chowGroupCast_naturality (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (r : Y ⟶ C.S) [LocallyOfFiniteType r]
    (φ : ∀ n : ℤ, chowGroup C p n →+ chowGroup C r n) {i j : ℤ} (h : i = j)
    (x : chowGroup C p i) :
    φ j (chowGroupCast C p h x) = chowGroupCast C r h (φ i x) := by
  subst h
  rfl

/-- A heterogeneous equality of homomorphisms into Chow groups of equal degrees, read as an
equality of values through the transport. -/
private theorem chowGroupCast_apply_of_heq (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] {A : Type u} [AddCommGroup A] {i j : ℤ} (h : i = j)
    (φ : A →+ chowGroup C p i) (ψ : A →+ chowGroup C p j) (hφψ : HEq φ ψ) (a : A) :
    chowGroupCast C p h (φ a) = ψ a := by
  subst h
  exact congrArg (fun t : A →+ chowGroup C p i ↦ t a) (eq_of_heq hφψ)

/-- Transport along an equality of degrees composes. -/
private theorem chowGroupCast_comp_eq (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] {i j l : ℤ} (h : i = j) (h' : j = l) (h'' : i = l)
    (x : chowGroup C p i) :
    chowGroupCast C p h' (chowGroupCast C p h x) = chowGroupCast C p h'' x := by
  subst h
  subst h'
  rfl

/-- The base-change homomorphism on Chow groups commutes with the transport along an equality of
degrees. -/
theorem baseChangeChowPullback_chowGroupCast (B : FlatBaseChangeSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] {i j : ℤ} (h : i = j)
    (h' : i + B.c = j + B.c) (x : chowGroup B.base f i) :
    baseChangeChowPullback B f j (chowGroupCast B.base f h x) =
      chowGroupCast B.baseChange (pullback.snd f B.g) h' (baseChangeChowPullback B f i x) := by
  subst h
  rfl

/-! ### Stacks 0FVL with the base morphism of the source a parameter -/

/-- **[Stacks, Tag 0FVL], the Chow square**, with the structure morphism of the source an
independent morphism `sX` and the factorization `f ≫ sY = sX` a hypothesis, and with the
base-changed morphism a parameter `f'` pinned down by its two projections.

This is `Stacks.Chow.properChowPushforward_baseChangeChowPullback_of_baseChangeChowPullback` in
the shape a section of a morphism needs: the zero section `o : X ⟶ L` of a line bundle satisfies
`o ≫ (p ≫ sX) = sX`, so the Chow group it pushes forward from is `CH_k(X)` and not the Chow
group of a syntactic composite. Substituting the factorization reduces the statement to the one
with `sX = f ≫ sY`, where `f'` is forced to be `Stacks.Chow.baseChangeMorphism` because the two
projections of a fibre product jointly determine a morphism into it. -/
theorem properChowPushforward_baseChangeChowPullback_of_base
    (B : FlatBaseChangeSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ B.base.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ B.base.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [IsProper f] (hbase : f ≫ sY = sX)
    (f' : (pullback sX B.g : Scheme.{u}) ⟶ (pullback sY B.g : Scheme.{u})) [IsProper f']
    (hfst : f' ≫ pullback.fst sY B.g = pullback.fst sX B.g ≫ f)
    (hsnd : f' ≫ pullback.snd sY B.g = pullback.snd sX B.g) (k : ℤ)
    (w : chowGroup B.base sX k) :
    properChowPushforward B.baseChange (pullback.snd sX B.g) (pullback.snd sY B.g) f' hsnd
        (k + B.c)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper B.baseChange
          (pullback.snd sX B.g) (pullback.snd sY B.g) f' hsnd (k + B.c))
        (baseChangeChowPullback B sX k w) =
      baseChangeChowPullback B sY k
        (properChowPushforward B.base sX sY f hbase k
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper B.base sX sY f hbase k)
          w) := by
  subst hbase
  have hf' : f' = baseChangeMorphism B sY f := by
    refine pullback.hom_ext ?_ ?_
    · rw [hfst, baseChangeMorphism_comp_fst]
    · rw [hsnd, baseChangeMorphism_comp_snd]
  subst hf'
  exact properChowPushforward_baseChangeChowPullback_of_baseChangeChowPullback B sY f k w

/-! ### Stacks 0FVK as an equality of classes -/

/-- **[Stacks, Tag 0FVK], the Chow square**, read as an equality of classes. The two routes land
in degrees `(k + r) + c` and `(k + c) + r`, so the tagged statement
`Stacks.Chow.baseChange_flatPullback_chow` is a heterogeneous equality of homomorphisms; this is
its value at a class, with the transport `Stacks.Chow.chowGroupCast` between the two degrees
written out. -/
theorem baseChange_flatPullbackChow_apply (B : FlatBaseChangeSituation.{u}) {Y X : Scheme.{u}}
    (sY : Y ⟶ B.base.S) [LocallyOfFiniteType sY] (sX : X ⟶ B.base.S) [LocallyOfFiniteType sX]
    (f : Y ⟶ X) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sY)
    (f' : (pullback sY B.g : Scheme.{u}) ⟶ (pullback sX B.g : Scheme.{u}))
    [LocallyOfFiniteType f'] [Flat f']
    (hbase' : f' ≫ pullback.snd sX B.g = pullback.snd sY B.g)
    (hcomm : pullback.fst sY B.g ≫ f = f' ≫ pullback.fst sX B.g)
    (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
    (hf' : AlgebraicGeometry.RelativeDimension f' r) (k : ℤ)
    (hidx : k + (r : ℤ) + B.c = k + B.c + (r : ℤ)) (α : chowGroup B.base sX k) :
    chowGroupCast B.baseChange (pullback.snd sY B.g) hidx
        (baseChangeChowPullback B sY (k + (r : ℤ))
          (flatPullbackChowOfRelativeDimension B.base sY sX f hbase r hf k α)) =
      flatPullbackChowOfRelativeDimension B.baseChange (pullback.snd sY B.g)
        (pullback.snd sX B.g) f' hbase' r hf' (k + B.c) (baseChangeChowPullback B sX k α) :=
  chowGroupCast_apply_of_heq B.baseChange (pullback.snd sY B.g) hidx _ _
    (baseChange_flatPullback_chow B sY sX f hbase f' hbase' hcomm r hf hf' k) α

/-! ### The line bundle of the base-changed module as a fibre product over the new base -/

variable (B : FlatBaseChangeSituation.{u}) (D : Stacks.LineBundle.Situation.{u})
  (sX : D.X ⟶ B.base.S) [LocallyOfFiniteType sX]

attribute [local instance] Stacks.LineBundle.Situation.flat_totalSpaceToBase

/-- The projection `X' = X ×_S S' ⟶ X` of the base change, along which the line bundle is pulled
back. -/
abbrev baseProjection : (pullback sX B.g : Scheme.{u}) ⟶ D.X := pullback.fst sX B.g

/-- The base-changed line-bundle situation: the module `ℒ'` on `X' = X ×_S S'`. This is
`Stacks.LineBundle.Situation.baseChange` of `D` along `X' ⟶ X`, written out field by field so
that its underlying scheme is the fibre product `X ×_S S'` for instance search and not an opaque
projection; `Stacks.Chow.baseChangeSituation_eq` records that the two agree. -/
abbrev baseChangeSituation : Stacks.LineBundle.Situation.{u} where
  X := (pullback sX B.g : Scheme.{u})
  S := D.S
  f := baseProjection B D sX ≫ D.f
  L := (Scheme.Modules.pullback (baseProjection B D sX)).obj D.L
  invertible := @Stacks.InvertiblePullback.isInvertible_pullback_ringCatSheaf
    (pullback sX B.g : Scheme.{u}) D.X (baseProjection B D sX) D.L D.invertible

omit [LocallyOfFiniteType sX] in
/-- The line-bundle situation `Stacks.Chow.baseChangeSituation` is the base change of `D` along
the projection `X' ⟶ X`. -/
theorem baseChangeSituation_eq :
    baseChangeSituation B D sX = D.baseChange (baseProjection B D sX) := rfl

/-- The base change of the projection `p : Tot(ℒ) ⟶ X` of the line bundle, as a morphism
`Tot(ℒ) ×_S S' ⟶ X'`. -/
abbrev totalSpaceBaseChangeMorphism :
    (pullback (D.totalSpaceToBase ≫ sX) B.g : Scheme.{u}) ⟶ (pullback sX B.g : Scheme.{u}) :=
  baseChangeMorphism B sX D.totalSpaceToBase

/-- The base change `Tot(ℒ) ×_S S' ⟶ X'` of the projection of the line bundle is locally of
finite type. -/
instance locallyOfFiniteType_totalSpaceBaseChangeMorphism :
    LocallyOfFiniteType (totalSpaceBaseChangeMorphism B D sX) :=
  MorphismProperty.of_isPullback
    (isPullback_baseChangeMorphism B sX D.totalSpaceToBase) (P := @LocallyOfFiniteType)
    inferInstance

/-- The base change `Tot(ℒ) ×_S S' ⟶ X'` of the projection of the line bundle is flat. -/
instance flat_totalSpaceBaseChangeMorphism :
    Flat (totalSpaceBaseChangeMorphism B D sX) :=
  MorphismProperty.of_isPullback
    (isPullback_baseChangeMorphism B sX D.totalSpaceToBase) (P := @Flat) inferInstance

omit [LocallyOfFiniteType sX] in
/-- **The base change of the projection of a line bundle is flat of relative dimension one**,
which is the first assertion of [Stacks, Tag 0FVK] for `p : Tot(ℒ) ⟶ X`. -/
theorem relativeDimension_totalSpaceBaseChangeMorphism :
    AlgebraicGeometry.RelativeDimension (totalSpaceBaseChangeMorphism B D sX) 1 :=
  AlgebraicGeometry.RelativeDimension.of_isPullback
    (isPullback_baseChangeMorphism B sX D.totalSpaceToBase) D.relativeDimension_totalSpaceToBase

/-- **The total space of the base-changed line bundle is the base change of the total space.**
Both `Tot_{X'}(ℒ')` and `Tot(ℒ) ×_S S'` are cartesian over the cospan formed by the projection
`p : Tot(ℒ) ⟶ X` of the line bundle and the projection `X' ⟶ X` of the base change — the first by
`Stacks.LineBundle.Situation.isPullback_baseChange` and the second by
`Stacks.Chow.isPullback_baseChangeMorphism` — so they are canonically isomorphic. -/
def lineBundleBaseChangeIso :
    (baseChangeSituation B D sX).totalSpace ≅
      (pullback (D.totalSpaceToBase ≫ sX) B.g : Scheme.{u}) :=
  (D.isPullback_baseChange (baseProjection B D sX)).isoPullback ≪≫
    (isPullback_baseChangeMorphism B sX D.totalSpaceToBase).isoPullback.symm

omit [LocallyOfFiniteType sX] in
/-- The comparison isomorphism followed by the projection `Tot(ℒ) ×_S S' ⟶ Tot(ℒ)` is the map
`Tot_{X'}(ℒ') ⟶ Tot(ℒ)` covering `X' ⟶ X`. -/
theorem lineBundleBaseChangeIso_hom_comp_fst :
    (lineBundleBaseChangeIso B D sX).hom ≫
        pullback.fst (D.totalSpaceToBase ≫ sX) B.g =
      D.baseChangeToTotalSpace (baseProjection B D sX) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun m ↦ (D.isPullback_baseChange (baseProjection B D sX)).isoPullback.hom ≫ m)
        (isPullback_baseChangeMorphism B sX D.totalSpaceToBase).isoPullback_inv_fst).trans
      (D.isPullback_baseChange (baseProjection B D sX)).isoPullback_hom_fst)

omit [LocallyOfFiniteType sX] in
/-- The comparison isomorphism is compatible with the projections to `X'`: followed by
`Tot(ℒ) ×_S S' ⟶ X'` it is the projection `Tot_{X'}(ℒ') ⟶ X'`. -/
theorem lineBundleBaseChangeIso_hom_comp_baseChangeMorphism :
    (lineBundleBaseChangeIso B D sX).hom ≫ totalSpaceBaseChangeMorphism B D sX =
      (baseChangeSituation B D sX).totalSpaceToBase :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun m ↦ (D.isPullback_baseChange (baseProjection B D sX)).isoPullback.hom ≫ m)
        (isPullback_baseChangeMorphism B sX D.totalSpaceToBase).isoPullback_inv_snd).trans
      (D.isPullback_baseChange (baseProjection B D sX)).isoPullback_hom_snd)

omit [LocallyOfFiniteType sX] in
/-- The comparison isomorphism is an isomorphism over the new base scheme `S'`. -/
theorem lineBundleBaseChangeIso_hom_comp_snd :
    (lineBundleBaseChangeIso B D sX).hom ≫
        pullback.snd (D.totalSpaceToBase ≫ sX) B.g =
      (baseChangeSituation B D sX).totalSpaceToBase ≫ pullback.snd sX B.g := by
  rw [← baseChangeMorphism_comp_snd B sX D.totalSpaceToBase, ← Category.assoc,
    lineBundleBaseChangeIso_hom_comp_baseChangeMorphism]

/-- The zero section of the base-changed line bundle, read in the fibre product
`Tot(ℒ) ×_S S'`. -/
abbrev zeroSectionBaseChange :
    (pullback sX B.g : Scheme.{u}) ⟶
      (pullback (D.totalSpaceToBase ≫ sX) B.g : Scheme.{u}) :=
  (baseChangeSituation B D sX).zeroSection ≫ (lineBundleBaseChangeIso B D sX).hom

omit [LocallyOfFiniteType sX] in
/-- The zero section of the base-changed line bundle, followed by the projection to `Tot(ℒ)`, is
the projection `X' ⟶ X` followed by the zero section of `ℒ`. -/
theorem zeroSectionBaseChange_comp_fst :
    zeroSectionBaseChange B D sX ≫ pullback.fst (D.totalSpaceToBase ≫ sX) B.g =
      pullback.fst sX B.g ≫ D.zeroSection := by
  show ((baseChangeSituation B D sX).zeroSection ≫ (lineBundleBaseChangeIso B D sX).hom) ≫
    pullback.fst (D.totalSpaceToBase ≫ sX) B.g = _
  rw [Category.assoc, lineBundleBaseChangeIso_hom_comp_fst]
  exact D.zeroSection_comp_baseChangeToTotalSpace (baseProjection B D sX)

omit [LocallyOfFiniteType sX] in
/-- The zero section of the base-changed line bundle, followed by the projection to `S'`, is the
projection `X' ⟶ S'`. -/
theorem zeroSectionBaseChange_comp_snd :
    zeroSectionBaseChange B D sX ≫ pullback.snd (D.totalSpaceToBase ≫ sX) B.g =
      pullback.snd sX B.g := by
  show ((baseChangeSituation B D sX).zeroSection ≫ (lineBundleBaseChangeIso B D sX).hom) ≫
    pullback.snd (D.totalSpaceToBase ≫ sX) B.g = _
  rw [Category.assoc, lineBundleBaseChangeIso_hom_comp_snd, ← Category.assoc,
    (baseChangeSituation B D sX).zeroSection_comp_totalSpaceToBase, Category.id_comp]

/-! ### Clause (5) of Stacks 0F96 for the base-changed line bundle -/

/-- Pushforward along the comparison isomorphism, as a homomorphism of Chow groups over `S'`. -/
abbrev comparisonChowPushforward (j : ℤ) :
    chowGroup B.baseChange
        ((baseChangeSituation B D sX).totalSpaceToBase ≫ pullback.snd sX B.g) j →+
      chowGroup B.baseChange (pullback.snd (D.totalSpaceToBase ≫ sX) B.g) j :=
  chowPushforwardOfIso B.baseChange
    ((baseChangeSituation B D sX).totalSpaceToBase ≫ pullback.snd sX B.g)
    (pullback.snd (D.totalSpaceToBase ≫ sX) B.g) (lineBundleBaseChangeIso B D sX).hom
    (lineBundleBaseChangeIso_hom_comp_snd B D sX) j

/-- **Pushing a flat pullback along the projection of the base-changed line bundle forward along
the comparison isomorphism gives the flat pullback along the base-changed projection.** This is
`Stacks.Chow.flatPullbackChow_chowPushforwardOfIso` for the square whose two isomorphisms are the
identity of `X'` and the comparison, and whose two flat morphisms are the two projections. -/
theorem comparisonChowPushforward_flatPullbackChow (j : ℤ)
    (γ : chowGroup B.baseChange (pullback.snd sX B.g) j) :
    comparisonChowPushforward B D sX (j + ((1 : ℕ) : ℤ))
        (flatPullbackChowOfRelativeDimension B.baseChange
          ((baseChangeSituation B D sX).totalSpaceToBase ≫ pullback.snd sX B.g)
          (pullback.snd sX B.g) (baseChangeSituation B D sX).totalSpaceToBase rfl 1
          (baseChangeSituation B D sX).relativeDimension_totalSpaceToBase j γ) =
      flatPullbackChowOfRelativeDimension B.baseChange
        (pullback.snd (D.totalSpaceToBase ≫ sX) B.g) (pullback.snd sX B.g)
        (totalSpaceBaseChangeMorphism B D sX)
        (baseChangeMorphism_comp_snd B sX D.totalSpaceToBase) 1
        (relativeDimension_totalSpaceBaseChangeMorphism B D sX) j γ := by
  have hsq : (baseChangeSituation B D sX).totalSpaceToBase ≫ (𝟙 (pullback sX B.g)) =
      (lineBundleBaseChangeIso B D sX).hom ≫ totalSpaceBaseChangeMorphism B D sX := by
    rw [Category.comp_id, lineBundleBaseChangeIso_hom_comp_baseChangeMorphism]
  have h := flatPullbackChow_chowPushforwardOfIso B.baseChange (pullback.snd sX B.g)
    ((baseChangeSituation B D sX).totalSpaceToBase ≫ pullback.snd sX B.g)
    (pullback.snd sX B.g) (pullback.snd (D.totalSpaceToBase ≫ sX) B.g)
    (𝟙 (pullback sX B.g)) (Category.id_comp _) (lineBundleBaseChangeIso B D sX).hom
    (lineBundleBaseChangeIso_hom_comp_snd B D sX)
    (baseChangeSituation B D sX).totalSpaceToBase rfl (totalSpaceBaseChangeMorphism B D sX)
    (baseChangeMorphism_comp_snd B sX D.totalSpaceToBase) hsq 1
    (baseChangeSituation B D sX).relativeDimension_totalSpaceToBase
    (relativeDimension_totalSpaceBaseChangeMorphism B D sX) j
    (flatPullbackFactorsThroughRationalEquivalence_general B.baseChange
      ((baseChangeSituation B D sX).totalSpaceToBase ≫ pullback.snd sX B.g)
      (pullback.snd sX B.g) (baseChangeSituation B D sX).totalSpaceToBase rfl 1
      (baseChangeSituation B D sX).relativeDimension_totalSpaceToBase j)
    (flatPullbackFactorsThroughRationalEquivalence_general B.baseChange
      (pullback.snd (D.totalSpaceToBase ≫ sX) B.g) (pullback.snd sX B.g)
      (totalSpaceBaseChangeMorphism B D sX)
      (baseChangeMorphism_comp_snd B sX D.totalSpaceToBase) 1
      (relativeDimension_totalSpaceBaseChangeMorphism B D sX) j) γ
  have hid : chowPushforwardOfIso B.baseChange (pullback.snd sX B.g) (pullback.snd sX B.g)
      (𝟙 (pullback sX B.g)) (Category.id_comp _) j γ = γ :=
    congrFun (congrArg DFunLike.coe
      (properChowPushforward_id B.baseChange (pullback.snd sX B.g) j
        (properPushforwardFactorsThroughRationalEquivalence_of_isIso B.baseChange
          (pullback.snd sX B.g) (pullback.snd sX B.g) (𝟙 (pullback sX B.g))
          (Category.id_comp _) j))) γ
  rw [hid] at h
  exact h.symm

/-- **Clause (5) of [Stacks, Tag 0F96] for the base-changed line bundle, transported to the
fibre product `Tot(ℒ) ×_S S'`.** For every class `δ` on `X'`,

  `õ_*δ = -p̃^*(c₁(ℒ') ∩ δ)`

where `õ` is the zero section read in the fibre product and `p̃` is the base change of the
projection of the line bundle. Pushing clause (5) for `ℒ'` forward along the comparison
isomorphism turns its left-hand side into `õ_*δ` by functoriality of proper pushforward and its
right-hand side into `p̃^*(c₁(ℒ') ∩ δ)` by
`Stacks.Chow.comparisonChowPushforward_flatPullbackChow`. -/
theorem zeroSectionBaseChange_chowPushforward_eq_neg (j : ℤ)
    (δ : chowGroup B.baseChange (pullback.snd sX B.g) (j + 1)) :
    properChowPushforward B.baseChange (pullback.snd sX B.g)
        (pullback.snd (D.totalSpaceToBase ≫ sX) B.g) (zeroSectionBaseChange B D sX)
        (zeroSectionBaseChange_comp_snd B D sX) (j + 1)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper B.baseChange
          (pullback.snd sX B.g) (pullback.snd (D.totalSpaceToBase ≫ sX) B.g)
          (zeroSectionBaseChange B D sX) (zeroSectionBaseChange_comp_snd B D sX) (j + 1)) δ =
      -chowGroupCast B.baseChange (pullback.snd (D.totalSpaceToBase ≫ sX) B.g)
          (show j + ((1 : ℕ) : ℤ) = j + 1 from by simp)
        (flatPullbackChowOfRelativeDimension B.baseChange
          (pullback.snd (D.totalSpaceToBase ≫ sX) B.g) (pullback.snd sX B.g)
          (totalSpaceBaseChangeMorphism B D sX)
          (baseChangeMorphism_comp_snd B sX D.totalSpaceToBase) 1
          (relativeDimension_totalSpaceBaseChangeMorphism B D sX) j
          (firstChernClassCapChow B.baseChange j (pullback.snd sX B.g)
            (baseChangeSituation B D sX).L δ)) := by
  have hcomp := properChowPushforward_comp B.baseChange (pullback.snd sX B.g)
    ((baseChangeSituation B D sX).totalSpaceToBase ≫ pullback.snd sX B.g)
    (pullback.snd (D.totalSpaceToBase ≫ sX) B.g) (baseChangeSituation B D sX).zeroSection
    (lineBundleBaseChangeIso B D sX).hom
    (zeroSection_comp_totalSpaceToBase_comp B.baseChange (baseChangeSituation B D sX)
      (pullback.snd sX B.g))
    (lineBundleBaseChangeIso_hom_comp_snd B D sX) (j + 1)
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper B.baseChange
      (pullback.snd sX B.g)
      ((baseChangeSituation B D sX).totalSpaceToBase ≫ pullback.snd sX B.g)
      (baseChangeSituation B D sX).zeroSection
      (zeroSection_comp_totalSpaceToBase_comp B.baseChange (baseChangeSituation B D sX)
        (pullback.snd sX B.g)) (j + 1))
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso B.baseChange
      ((baseChangeSituation B D sX).totalSpaceToBase ≫ pullback.snd sX B.g)
      (pullback.snd (D.totalSpaceToBase ≫ sX) B.g) (lineBundleBaseChangeIso B D sX).hom
      (lineBundleBaseChangeIso_hom_comp_snd B D sX) (j + 1))
  have hval := congrFun (congrArg DFunLike.coe hcomp) δ
  rw [properChowPushforward_congr B.baseChange (pullback.snd sX B.g)
    (pullback.snd (D.totalSpaceToBase ≫ sX) B.g)
    ((baseChangeSituation B D sX).zeroSection ≫ (lineBundleBaseChangeIso B D sX).hom)
    (zeroSectionBaseChange B D sX) rfl _ (zeroSectionBaseChange_comp_snd B D sX) (j + 1) _
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper B.baseChange
      (pullback.snd sX B.g) (pullback.snd (D.totalSpaceToBase ≫ sX) B.g)
      (zeroSectionBaseChange B D sX) (zeroSectionBaseChange_comp_snd B D sX) (j + 1))] at hval
  rw [← hval]
  show comparisonChowPushforward B D sX (j + 1)
      (zeroSectionChowPushforward B.baseChange (baseChangeSituation B D sX)
        (pullback.snd sX B.g) (j + 1) δ) = _
  rw [zeroSectionChowPushforward_eq_neg_flatPullbackChow_firstChernClassCapChow B.baseChange
    (baseChangeSituation B D sX) (pullback.snd sX B.g) j δ, map_neg,
    chowGroupCast_naturality B.baseChange
      ((baseChangeSituation B D sX).totalSpaceToBase ≫ pullback.snd sX B.g)
      (pullback.snd (D.totalSpaceToBase ≫ sX) B.g)
      (fun n ↦ comparisonChowPushforward B D sX n)
      (show j + ((1 : ℕ) : ℤ) = j + 1 from by simp),
    comparisonChowPushforward_flatPullbackChow B D sX j]

/-! ### Stacks 0FVL for the zero section of the line bundle -/

/-- **[Stacks, Tag 0FVL] for the zero section of the line bundle.** Base change commutes with
pushforward along the zero section: `g^*(o_*α) = õ_*(g^*α)`, where `õ` is the zero section read
in the fibre product `Tot(ℒ) ×_S S'`.

This is `Stacks.Chow.properChowPushforward_baseChangeChowPullback_of_base` at `f = o`, whose two
projection hypotheses are `Stacks.Chow.zeroSectionBaseChange_comp_fst` — the content of
`Stacks.LineBundle.Situation.zeroSection_comp_baseChangeToTotalSpace` — and
`Stacks.Chow.zeroSectionBaseChange_comp_snd`. -/
theorem baseChangeChowPullback_zeroSectionChowPushforward (j : ℤ)
    (a : chowGroup B.base sX j) :
    baseChangeChowPullback B (D.totalSpaceToBase ≫ sX) j
        (zeroSectionChowPushforward B.base D sX j a) =
      properChowPushforward B.baseChange (pullback.snd sX B.g)
        (pullback.snd (D.totalSpaceToBase ≫ sX) B.g) (zeroSectionBaseChange B D sX)
        (zeroSectionBaseChange_comp_snd B D sX) (j + B.c)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper B.baseChange
          (pullback.snd sX B.g) (pullback.snd (D.totalSpaceToBase ≫ sX) B.g)
          (zeroSectionBaseChange B D sX) (zeroSectionBaseChange_comp_snd B D sX) (j + B.c))
        (baseChangeChowPullback B sX j a) :=
  (properChowPushforward_baseChangeChowPullback_of_base B sX (D.totalSpaceToBase ≫ sX)
    D.zeroSection (zeroSection_comp_totalSpaceToBase_comp B.base D sX)
    (zeroSectionBaseChange B D sX) (zeroSectionBaseChange_comp_fst B D sX)
    (zeroSectionBaseChange_comp_snd B D sX) j a).symm

/-! ### Injectivity of the base change of the flat pullback -/

/-- **The flat pullback along the base change of the projection of a line bundle is injective.**
It is the flat pullback along the projection of the base-changed line bundle, pushed forward
along the comparison isomorphism, by
`Stacks.Chow.comparisonChowPushforward_flatPullbackChow`; the first is split by the Gysin map of
the zero section — clause (4) of [Stacks, Tag 0F96], which is the injectivity half of
[Stacks, Tag 0B74] — and the second is an isomorphism of Chow groups. -/
theorem injective_flatPullbackChow_totalSpaceBaseChangeMorphism (j : ℤ) :
    Function.Injective (flatPullbackChowOfRelativeDimension B.baseChange
      (pullback.snd (D.totalSpaceToBase ≫ sX) B.g) (pullback.snd sX B.g)
      (totalSpaceBaseChangeMorphism B D sX)
      (baseChangeMorphism_comp_snd B sX D.totalSpaceToBase) 1
      (relativeDimension_totalSpaceBaseChangeMorphism B D sX) j) := by
  have hpinj : Function.Injective (flatPullbackChowOfRelativeDimension B.baseChange
      ((baseChangeSituation B D sX).totalSpaceToBase ≫ pullback.snd sX B.g)
      (pullback.snd sX B.g) (baseChangeSituation B D sX).totalSpaceToBase rfl 1
      (baseChangeSituation B D sX).relativeDimension_totalSpaceToBase j) :=
    Function.LeftInverse.injective
      (zeroSectionGysinChow_flatPullbackChowOfRelativeDimension B.baseChange
        (baseChangeSituation B D sX) (pullback.snd sX B.g) j)
  have hcompinj : Function.Injective
      (comparisonChowPushforward B D sX (j + ((1 : ℕ) : ℤ))) := by
    intro a b hab
    have h := congrArg (chowPushforwardOfIso B.baseChange
      (pullback.snd (D.totalSpaceToBase ≫ sX) B.g)
      ((baseChangeSituation B D sX).totalSpaceToBase ≫ pullback.snd sX B.g)
      (inv (lineBundleBaseChangeIso B D sX).hom)
      (by rw [IsIso.inv_comp_eq, lineBundleBaseChangeIso_hom_comp_snd])
      (j + ((1 : ℕ) : ℤ))) hab
    rwa [chowPushforwardOfIso_inv_comp, chowPushforwardOfIso_inv_comp] at h
  intro x y hxy
  rw [← comparisonChowPushforward_flatPullbackChow B D sX j x,
    ← comparisonChowPushforward_flatPullbackChow B D sX j y] at hxy
  exact hpinj (hcompinj hxy)

/-! ### Stacks 0FVM -/

/-- **[Stacks, Tag 0FVM].** In the flat base-change situation of [Stacks, Tag 0FVG] let `X` be
locally of finite type over `S`, let `X' = X ×_S S'` be the base change by `S' ⟶ S`, and let `ℒ`
be an invertible `𝒪_X`-module with base change `ℒ'` on `X'`. Then the square

  `CH_{k+1}(X) --g^*--> CH_{k+1+c}(X')`
  `      |c₁(ℒ) ∩ -             |c₁(ℒ') ∩ -`
  `CH_k(X)     --g^*--> CH_{k+c}(X')`

of Chow groups commutes, `g^*` being the base-change map of [Stacks, Tag 0FVJ].

The cap product of [Stacks, Tag 02TI] is indexed by the degree of its value, so the top row is
written at `k + 1`; the source states the square for every `k ∈ ℤ`, so nothing is lost. The
transport between the two spellings `(k + 1) + c` and `(k + c) + 1` of the degree of the base
change of the top-left corner is `Stacks.Chow.chowGroupCast`. The module `ℒ'` is
`(D.baseChange g).L`, which is the pullback `g^*ℒ` by
`Stacks.LineBundle.Situation.baseChange_L`.

**Proof.** Let `p : Tot(ℒ) ⟶ X` be the line bundle attached to `ℒ` with zero section `o`. By
clause (5) of [Stacks, Tag 0F96], `o_*α = -p^*(c₁(ℒ) ∩ α)`. Applying `g^*` and using
[Stacks, Tag 0FVL] on `o` and [Stacks, Tag 0FVK] on `p` turns this into

  `õ_*(g^*α) = -p̃^*(g^*(c₁(ℒ) ∩ α))`

on the fibre product `Tot(ℒ) ×_S S'`, where `õ` and `p̃` are the base changes of `o` and `p`. On
the other hand `Stacks.Chow.zeroSectionBaseChange_chowPushforward_eq_neg` — clause (5) for `ℒ'`,
transported along `Tot(ℒ') ≅ Tot(ℒ) ×_S S'` — gives

  `õ_*(g^*α) = -p̃^*(c₁(ℒ') ∩ g^*α)`.

So `p̃^*` takes the same value on the two classes to be identified, and `p̃^*` is injective by
`Stacks.Chow.injective_flatPullbackChow_totalSpaceBaseChangeMorphism`. -/
@[stacks 0FVM]
theorem baseChange_firstChernClassCapChow (k : ℤ) (α : chowGroup B.base sX (k + 1)) :
    firstChernClassCapChow B.baseChange (k + B.c) (pullback.snd sX B.g)
        (baseChangeSituation B D sX).L
        (chowGroupCast B.baseChange (pullback.snd sX B.g)
          (show k + 1 + B.c = k + B.c + 1 from by omega)
          (baseChangeChowPullback B sX (k + 1) α)) =
      baseChangeChowPullback B sX k (firstChernClassCapChow B.base k sX D.L α) := by
  have hd : k + 1 + B.c = k + B.c + 1 := by omega
  have h2 : k + B.c + ((1 : ℕ) : ℤ) = k + B.c + 1 := by simp
  have hc1 : k + ((1 : ℕ) : ℤ) + B.c = k + B.c + 1 := by push_cast; ring
  have hidx : k + ((1 : ℕ) : ℤ) + B.c = k + B.c + ((1 : ℕ) : ℤ) := by push_cast; ring
  have h1c : k + ((1 : ℕ) : ℤ) + B.c = k + 1 + B.c := by simp
  -- the base change of clause (5) of Stacks 0F96 on `X`
  have hB := congrArg (baseChangeChowPullback B (D.totalSpaceToBase ≫ sX) (k + 1))
    (zeroSectionChowPushforward_eq_neg_flatPullbackChow_firstChernClassCapChow B.base D sX k α)
  rw [baseChangeChowPullback_zeroSectionChowPushforward B D sX (k + 1) α, map_neg,
    baseChangeChowPullback_chowGroupCast B (D.totalSpaceToBase ≫ sX)
      (show k + ((1 : ℕ) : ℤ) = k + 1 by simp) h1c] at hB
  -- clause (5) of Stacks 0F96 on `X'`, transported to the fibre product
  have hC := zeroSectionBaseChange_chowPushforward_eq_neg B D sX (k + B.c)
    (chowGroupCast B.baseChange (pullback.snd sX B.g) hd
      (baseChangeChowPullback B sX (k + 1) α))
  rw [chowGroupCast_naturality B.baseChange (pullback.snd sX B.g)
    (pullback.snd (D.totalSpaceToBase ≫ sX) B.g)
    (fun n ↦ properChowPushforward B.baseChange (pullback.snd sX B.g)
      (pullback.snd (D.totalSpaceToBase ≫ sX) B.g) (zeroSectionBaseChange B D sX)
      (zeroSectionBaseChange_comp_snd B D sX) n
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper B.baseChange
        (pullback.snd sX B.g) (pullback.snd (D.totalSpaceToBase ≫ sX) B.g)
        (zeroSectionBaseChange B D sX) (zeroSectionBaseChange_comp_snd B D sX) n)) hd,
    hB, map_neg, chowGroupCast_comp_eq B.baseChange
      (pullback.snd (D.totalSpaceToBase ≫ sX) B.g) h1c hd hc1] at hC
  -- Stacks 0FVK applied to the projection of the line bundle
  have hK := baseChange_flatPullbackChow_apply B (D.totalSpaceToBase ≫ sX) sX
    D.totalSpaceToBase rfl (totalSpaceBaseChangeMorphism B D sX)
    (baseChangeMorphism_comp_snd B sX D.totalSpaceToBase)
    (baseChangeMorphism_comp_fst B sX D.totalSpaceToBase).symm 1
    D.relativeDimension_totalSpaceToBase
    (relativeDimension_totalSpaceBaseChangeMorphism B D sX) k hidx
    (firstChernClassCapChow B.base k sX D.L α)
  refine injective_flatPullbackChow_totalSpaceBaseChangeMorphism B D sX (k + B.c) ?_
  refine (chowGroupCast B.baseChange (pullback.snd (D.totalSpaceToBase ≫ sX) B.g)
    h2).injective ?_
  refine Eq.trans (neg_inj.1 hC.symm) ?_
  rw [← hK]
  exact (chowGroupCast_comp_eq B.baseChange
    (pullback.snd (D.totalSpaceToBase ≫ sX) B.g) hidx h2 hc1 _).symm

/-- **[Stacks, Tag 0FVM] for an invertible module on `X` itself.** The square of
`Stacks.Chow.baseChange_firstChernClassCapChow`, stated for an invertible `𝒪_X`-module `ℒ` and
its base change `(X' ⟶ X)^*ℒ` rather than for a line-bundle situation. The line bundle the proof
needs is that of the situation `(X, ℒ)`, whose base morphism plays no part. -/
theorem baseChange_firstChernClassCapChow_module (B : FlatBaseChangeSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ B.base.S) [LocallyOfFiniteType sX] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (k : ℤ) (α : chowGroup B.base sX (k + 1)) :
    firstChernClassCapChow B.baseChange (k + B.c) (pullback.snd sX B.g)
        ((Scheme.Modules.pullback (pullback.fst sX B.g)).obj L)
        (chowGroupCast B.baseChange (pullback.snd sX B.g)
          (show k + 1 + B.c = k + B.c + 1 from by omega)
          (baseChangeChowPullback B sX (k + 1) α)) =
      baseChangeChowPullback B sX k (firstChernClassCapChow B.base k sX L α) :=
  baseChange_firstChernClassCapChow B ⟨X, X, 𝟙 X, L⟩ sX k α

end Stacks.Chow

end
