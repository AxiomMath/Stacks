module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.GroupoidComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.GroupoidAssembly.ArrowComposition

/-!
# The target of the composition and of the unit of the finite part of a groupoid

Let `(U, R, s, t, c, e, i)` be a groupoid in algebraic spaces over `B` whose source and target
are separated and locally of finite type, and let `(U', Z_univ, s', t', c', e', i')` be the
structure spaces and structure morphisms of its finite part, built in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidStructure.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidComposition.lean`
(Stacks 04RU, clauses (1), (2) and part of (3)). This is the second of the three parts which
complete clause (3) of Stacks 04RU (the first is `ArrowComposition.lean`, the third
`SectionGroupoid.lean`, both in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidAssembly/`); it proves
the identities `t' ∘ c' = t' ∘ pr₁` and `t' ∘ e' = 𝟙`.

The identity `t' ∘ c' = t' ∘ pr₁` was the one missing. On points it is the cocycle identity
`c(c(Z₂, i ∘ z₂), i ∘ z₁) = c(Z₂, i ∘ c(z₁, z₂))` between open subspaces of `R`, for a
composable pair `((u₁, Z₁, z₁), (u₂, Z₂, z₂))`, that is one with
`(u₁, Z₁) = (t ∘ z₂, c(Z₂, i ∘ z₂))`. It is proved here by comparing, at a point of
`Z_univ ×_{s', U', t'} Z_univ` over a scheme `V` of the site, the two pairs of Stacks 04PC over
`V` which the target morphism names: both are base changes of the twisted pair
`(t ∘ z, c(Z, i ∘ z))`, their bases agree because the target of a composite is the target of its
first entry in the *given* groupoid, and their open subspaces agree because

* a section `r` of `R` lies in the twisted pair at a point `y` of `Z_univ` exactly when
  `(t'(y), r)` is a section of `Z_univ` — this is the keystone
  `AlgebraicGeometry.Space.FinitePartUniversalOpen.targetPair_subspace_eq` of the composition
  module — and also exactly when `(s'(y), c(r, z(y)))` is a section of `Z_univ`, by the very
  construction of the twist;
* so, applying both descriptions at the point `y₂` and to the section `c(r, z₁)`, the condition
  `c(r, z₁) ∈ Z₁` is equivalent to `c(c(r, z₁), z₂) ∈ Z₂`, which is `c(r, c(z₁, z₂)) ∈ Z₂` by
  associativity of the composition of the given groupoid.

The same comparison, run at the unit instead, gives `t' ∘ e' = 𝟙`: there the twist is by an
identity arrow, and the right unit law `c(r, e(s(r))) = r` makes the two base changes equal
morphism by morphism.

## Main results

* `AlgebraicGeometry.Space.FinitePartUniversalOpen.targetPair_preimage_lift_eq`: **the cocycle
  identity**, as an equality of preimages of the open subspace of the twisted pair.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.comp_hom_comp_target` and
  `AlgebraicGeometry.Space.FinitePartUniversalOpen.comp_comp_target`: `t' ∘ c' = t' ∘ pr₁`.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.unitMap_comp_target`: `t' ∘ e' = 𝟙`.

## Implementation notes

### Carried hypotheses

Everything is carried by the data of a `AlgebraicGeometry.Space.FinitePartUniversalOpen G`, as
in the two modules it continues: **no separatedness, finite type or étaleness hypothesis
appears**, those having been consumed in producing the structure by
`AlgebraicGeometry.Space.finitePartUniversalOpen`. Of its fields the three parts together use
`unit`, `unit_source`, `unit_identity`, `objects`, `objectProjection`, `objectsEquiv`,
`universalOpen`, `universalOpen_base` and `universalOpen_spec`; they use neither
`objectProjection_etale`, `objectProjection_spec`, `universalOpen_containsUnit` nor
`universalOpen_closed` directly (the last two enter only through the construction of `e'` and
`t'` in the earlier modules). No further hypothesis is carried by any declaration here.

### Restated private declarations

The following are `private` in the modules which prove them, so they are restated here with
their statements unchanged and with their proofs transcribed; only the names differ, to keep
the two copies distinguishable.

From `StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/FppfSheaf.lean`:

* `eq_preimage_of_isPullback` is restated as `subfunctor_eq_preimage_of_isPullback`;
* `pullback_map_isPullback` as `isPullback_fst_of_ambient`;
* `subfunctor_eq_preimage_of_projection_isPullback` as
  `subfunctor_eq_preimage_of_isPullback_projection`;
* `pullbackBaseMap` as `ambientBaseMap`, with `pullbackBaseMap_fst`, `pullbackBaseMap_snd` and
  `pullbackBaseMap_isPullback` as `ambientBaseMap_fst`, `ambientBaseMap_snd` and
  `isPullback_ambientBaseMap`;
* `PairBaseChange` as `IsPairBaseChange`;
* `pairBaseChange_subspace` as `isPairBaseChange_subspace`.

`pair_eq_of_subspace_eq` is new as a statement; its proof follows the pattern of
`FppfSheaf.lean`'s `pairBaseChange_unique`, destructuring the two pairs and substituting the
base and the open subspace.

Of the `PairBaseChange` theory of `FppfSheaf.lean` nothing else is needed: in particular
`exists_pair_of_compatible_opens` and `pairBaseChange_cover_ext`, which an earlier analysis
expected to be required, are **not** used. The reason is that the two pairs to be compared are
always compared at a morphism out of a *scheme of the site*, where the characterisation bundled
with `AlgebraicGeometry.Space.finiteOpenSubspaceEquiv` applies directly; no base change of
pairs along a morphism of algebraic spaces, and so no fpqc descent, occurs.

### Shape of the proofs

Comparisons of sections of ambient fibre products are made component by component and never by
rewriting inside a `CategoryTheory.Limits.pullback.lift`, whose third argument is a proof the
type of the term depends on; `eq_pullback_lift` and `pullback_lift_congr` are what replace such
rewriting, exactly as `AlgebraicGeometry.Space.compose_congr` and `composeMor_congr` replace
rewriting inside a composite of two arrows. For the same reason the two descriptions of the
open subspace of the twisted pair are packaged as `targetPair_preimage_untwist` and
`targetPair_preimage_target`, which take the two components of the section as arguments, so
that the cocycle identity becomes an equality of `pullback.lift`s of explicit components.

The second component of an untwisted section of an ambient fibre product is literally a
composite `AlgebraicGeometry.Space.composeMor`, by `untwistAmbient_snd_composeMor` of
`ArrowComposition.lean`, so the cocycle argument is morphism algebra.

## References

* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PE](https://stacks.math.columbia.edu/tag/04PE)
* [Stacks Project, Tag 04RT](https://stacks.math.columbia.edu/tag/04RT)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Space

/-! ### Cartesian squares, preimages of subfunctors and base change of a pair -/

/-- A subfunctor which is cartesian over another one along a morphism is its preimage. -/
private theorem subfunctor_eq_preimage_of_isPullback {D : Type v} [Category.{w} D]
    {F₁ F₂ : D ⥤ Type u} (A : Subfunctor F₁) (A' : Subfunctor F₂)
    (f : F₁ ⟶ F₂) (j : A.toFunctor ⟶ A'.toFunctor)
    (h : IsPullback j A.ι A'.ι f) : A = A'.preimage f := by
  ext U x
  have hh := Types.range_snd_of_isPullback (h.app U)
  have hA := congrArg (fun K : Subfunctor F₁ => K.obj U) (Subfunctor.range_ι A)
  have hA' := congrArg (fun K : Subfunctor F₂ => K.obj U) (Subfunctor.range_ι A')
  change Set.range (A.ι.app U) = A.obj U at hA
  change Set.range (A'.ι.app U) = A'.obj U at hA'
  rw [hA, hA'] at hh
  exact Set.ext_iff.mp hh x

/-- The first projection of an ambient fibre product is cartesian over the first projection of
a second one along the morphism of the bases. -/
private theorem isPullback_fst_of_ambient {D : Type v} [Category.{w} D]
    [HasPullbacks D] {T T' A A' : D} (a : T ⟶ A') (b : T' ⟶ A')
    (f : A ⟶ A') (g : T' ⟶ T) (m : pullback b f ⟶ pullback a f)
    (hb : b = g ≫ a)
    (hm₁ : m ≫ pullback.fst a f = pullback.fst b f ≫ g)
    (hm₂ : m ≫ pullback.snd a f = pullback.snd b f) :
    IsPullback (pullback.fst b f) m g (pullback.fst a f) := by
  apply IsPullback.of_bot (h₂₁ := pullback.fst a f) (v₂₁ := pullback.snd a f)
      (v₂₂ := a) (h₃₁ := f)
  · simpa only [hm₂, ← hb] using IsPullback.of_hasPullback b f
  · exact hm₁.symm
  · exact IsPullback.of_hasPullback a f

/-- A subfunctor whose projection is cartesian over the projection of another one is the
preimage of that one. -/
private theorem subfunctor_eq_preimage_of_isPullback_projection
    {D : Type v} [Category.{w} D] {T T' F F' : D ⥤ Type u}
    (p : F ⟶ T) (q : F' ⟶ T') (g : T' ⟶ T) (m : F' ⟶ F)
    (A : Subfunctor F) (A' : Subfunctor F')
    (j : A'.toFunctor ⟶ A.toFunctor)
    (h : IsPullback (A'.ι ≫ q) j g (A.ι ≫ p))
    (hm : IsPullback q m g p) (hj : j ≫ A.ι = A'.ι ≫ m) :
    A' = A.preimage m :=
  subfunctor_eq_preimage_of_isPullback A' A m j (h.flip.of_bot hj hm.flip)

/-- The comparison morphism of ambient fibre products induced by a morphism of the bases: the
morphism of the bases on the first component and the identity on the second. -/
private def ambientBaseMap {D : Type v} [Category.{w} D]
    [HasPullbacks D] {T T' A A' : D} (a : T ⟶ A') (b : T' ⟶ A')
    (f : A ⟶ A') (g : T' ⟶ T) (hb : b = g ≫ a) :
    pullback b f ⟶ pullback a f :=
  pullback.lift (pullback.fst b f ≫ g) (pullback.snd b f)
    (by rw [Category.assoc, ← hb, pullback.condition])

/-- The first component of the comparison morphism is the morphism of the bases. -/
private theorem ambientBaseMap_fst {D : Type v} [Category.{w} D]
    [HasPullbacks D] {T T' A A' : D} (a : T ⟶ A') (b : T' ⟶ A')
    (f : A ⟶ A') (g : T' ⟶ T) (hb : b = g ≫ a) :
    ambientBaseMap a b f g hb ≫ pullback.fst a f = pullback.fst b f ≫ g :=
  pullback.lift_fst _ _ _

/-- The comparison morphism does not move the second component. -/
private theorem ambientBaseMap_snd {D : Type v} [Category.{w} D]
    [HasPullbacks D] {T T' A A' : D} (a : T ⟶ A') (b : T' ⟶ A')
    (f : A ⟶ A') (g : T' ⟶ T) (hb : b = g ≫ a) :
    ambientBaseMap a b f g hb ≫ pullback.snd a f = pullback.snd b f :=
  pullback.lift_snd _ _ _

/-- The comparison morphism of ambient fibre products is cartesian over the morphism of the
bases. -/
private theorem isPullback_ambientBaseMap {D : Type v} [Category.{w} D]
    [HasPullbacks D] {T T' A A' : D} (a : T ⟶ A') (b : T' ⟶ A')
    (f : A ⟶ A') (g : T' ⟶ T) (hb : b = g ≫ a) :
    IsPullback (pullback.fst b f) (ambientBaseMap a b f g hb) g
      (pullback.fst a f) :=
  isPullback_fst_of_ambient a b f g _ hb
    (ambientBaseMap_fst a b f g hb) (ambientBaseMap_snd a b f g hb)

/-- A section of an ambient fibre product is the one determined by its two components. -/
private theorem eq_pullback_lift {D : Type v} [Category.{w} D] [HasPullbacks D]
    {W A A' A'' : D} {f : A ⟶ A''} {g : A' ⟶ A''} (M : W ⟶ pullback f g)
    (φ : W ⟶ A) (ψ : W ⟶ A')
    (hφ : M ≫ pullback.fst f g = φ) (hψ : M ≫ pullback.snd f g = ψ)
    (hc : φ ≫ f = ψ ≫ g) : M = pullback.lift φ ψ hc := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst, hφ]
  · rw [pullback.lift_snd, hψ]

/-- The section of a fibre product determined by two components depends only on those
components. -/
theorem pullback_lift_congr {D : Type v} [Category.{w} D] [HasPullbacks D]
    {W A A' A'' : D} {f : A ⟶ A''} {g : A' ⟶ A''}
    (φ φ' : W ⟶ A) (ψ ψ' : W ⟶ A')
    (hc : φ ≫ f = ψ ≫ g) (hc' : φ' ≫ f = ψ' ≫ g)
    (hφ : φ = φ') (hψ : ψ = ψ') :
    pullback.lift φ ψ hc = pullback.lift φ' ψ' hc' := by
  subst hφ
  subst hψ
  rfl

/-- The comparison morphism of ambient fibre products is the section determined by the
morphism of the bases and the second projection. -/
private theorem ambientBaseMap_eq_lift {D : Type v} [Category.{w} D]
    [HasPullbacks D] {T T' A A' : D} (a : T ⟶ A') (b : T' ⟶ A')
    (f : A ⟶ A') (g : T' ⟶ T) (hb : b = g ≫ a)
    (hc : (pullback.fst b f ≫ g) ≫ a = pullback.snd b f ≫ f) :
    ambientBaseMap a b f g hb = pullback.lift (pullback.fst b f ≫ g) (pullback.snd b f) hc :=
  rfl

/-- The pair `q` over `U` is the base change of the pair `p` over `T` along `g : U ⟶ T`. -/
private abbrev IsPairBaseChange (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {T U : AlgebraicSpaces B S hS}
    (g : U ⟶ T) (p : FiniteOpenSubspace B S hS f T)
    (q : FiniteOpenSubspace B S hS f U) : Prop :=
  q.toBase.hom = g.hom ≫ p.toBase.hom ∧
    ∃ j : q.subspace.toFunctor ⟶ p.subspace.toFunctor,
      IsPullback (q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom) j g.hom
        (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom) ∧
      j ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom =
        q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom

/-- The open subspace of a base-changed pair is the preimage of the original open subspace
under the comparison morphism of the ambient fibre products. -/
private theorem isPairBaseChange_subspace (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T U : AlgebraicSpaces B S hS} {g : U ⟶ T} {p : FiniteOpenSubspace B S hS f T}
    {q : FiniteOpenSubspace B S hS f U}
    (h : IsPairBaseChange B S hS f g p q) :
    q.subspace = p.subspace.preimage
      (ambientBaseMap p.toBase.hom q.toBase.hom f.hom g.hom h.1) := by
  obtain ⟨hb, j, hj, hX⟩ := h
  apply subfunctor_eq_preimage_of_isPullback_projection
    (pullback.fst p.toBase.hom f.hom) (pullback.fst q.toBase.hom f.hom)
    g.hom _ p.subspace q.subspace j hj
    (isPullback_ambientBaseMap _ _ _ _ hb)
  apply pullback.hom_ext
  · simpa only [Category.assoc, ambientBaseMap_fst] using hj.w.symm
  · simpa only [Category.assoc, ambientBaseMap_snd] using hX

/-- Two pairs over the same algebraic space with the same base and with open subspaces
identified by a morphism of the ambient fibre product over the identity are equal. -/
private theorem pair_eq_of_subspace_eq (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {U : AlgebraicSpaces B S hS} (q r : FiniteOpenSubspace B S hS f U)
    (hb : q.toBase = r.toBase)
    (κ : pullback q.toBase.hom f.hom ⟶ pullback r.toBase.hom f.hom)
    (hκ₁ : κ ≫ pullback.fst r.toBase.hom f.hom = pullback.fst q.toBase.hom f.hom)
    (hκ₂ : κ ≫ pullback.snd r.toBase.hom f.hom = pullback.snd q.toBase.hom f.hom)
    (hz : q.subspace = r.subspace.preimage κ) : q = r := by
  obtain ⟨aq, Zq, oq, fq⟩ := q
  obtain ⟨ar, Zr, orr, fr⟩ := r
  obtain rfl : aq = ar := hb
  have h₁ : κ ≫ pullback.fst aq.hom f.hom = pullback.fst aq.hom f.hom := hκ₁
  have h₂ : κ ≫ pullback.snd aq.hom f.hom = pullback.snd aq.hom f.hom := hκ₂
  have hid : κ = 𝟙 (pullback aq.hom f.hom) := by
    apply pullback.hom_ext
    · rw [h₁, Category.id_comp]
    · rw [h₂, Category.id_comp]
  have hz' : Zq = Zr.preimage κ := hz
  rw [hid, Subfunctor.preimage_id] at hz'
  subst hz'
  rfl

/-- The two components of the canonical section of the ambient fibre product of a
base-changed pair are composable. -/
private theorem ambient_condition_of_base (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T U : AlgebraicSpaces B S hS} (g : U ⟶ T) (p : FiniteOpenSubspace B S hS f T)
    (q : FiniteOpenSubspace B S hS f U)
    (hb : q.toBase.hom = g.hom ≫ p.toBase.hom) :
    (pullback.fst q.toBase.hom f.hom ≫ g.hom) ≫ p.toBase.hom =
      pullback.snd q.toBase.hom f.hom ≫ f.hom :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z => pullback.fst q.toBase.hom f.hom ≫ z) hb.symm).trans
      pullback.condition)

/-- Two pairs over the same algebraic space, each a base change of a pair with the same base,
whose open subspaces have the same preimage description, are equal. -/
private theorem pair_eq_of_isPairBaseChange (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T₁ T₂ U : AlgebraicSpaces B S hS}
    {p₁ : FiniteOpenSubspace B S hS f T₁} {p₂ : FiniteOpenSubspace B S hS f T₂}
    {g₁ : U ⟶ T₁} {g₂ : U ⟶ T₂}
    (q r : FiniteOpenSubspace B S hS f U)
    (hq : IsPairBaseChange B S hS f g₁ p₁ q)
    (hr : IsPairBaseChange B S hS f g₂ p₂ r)
    (hb : g₁.hom ≫ p₁.toBase.hom = g₂.hom ≫ p₂.toBase.hom)
    (hsub : ∀ (hc₁ : (pullback.fst q.toBase.hom f.hom ≫ g₁.hom) ≫ p₁.toBase.hom =
        pullback.snd q.toBase.hom f.hom ≫ f.hom)
      (hc₂ : (pullback.fst q.toBase.hom f.hom ≫ g₂.hom) ≫ p₂.toBase.hom =
        pullback.snd q.toBase.hom f.hom ≫ f.hom),
      p₁.subspace.preimage
          (pullback.lift (pullback.fst q.toBase.hom f.hom ≫ g₁.hom)
            (pullback.snd q.toBase.hom f.hom) hc₁) =
        p₂.subspace.preimage
          (pullback.lift (pullback.fst q.toBase.hom f.hom ≫ g₂.hom)
            (pullback.snd q.toBase.hom f.hom) hc₂)) :
    q = r := by
  have hbh := hq.1.trans (hb.trans hr.1.symm)
  have hbase : q.toBase = r.toBase := ObjectProperty.hom_ext _ hbh
  have hc₁ := ambient_condition_of_base B S hS f g₁ p₁ q hq.1
  have hc₂ := ambient_condition_of_base B S hS f g₂ p₂ q (hbh.trans hr.1)
  refine pair_eq_of_subspace_eq B S hS f q r hbase
    (ambientBaseMap r.toBase.hom q.toBase.hom f.hom (𝟙 U.obj)
      (by rw [congrArg (fun z : U ⟶ Y => z.hom) hbase, Category.id_comp])) ?_ ?_ ?_
  · rw [ambientBaseMap_fst, Category.comp_id]
  · rw [ambientBaseMap_snd]
  · have hκ : ambientBaseMap r.toBase.hom q.toBase.hom f.hom (𝟙 U.obj)
          (by rw [congrArg (fun z : U ⟶ Y => z.hom) hbase, Category.id_comp]) ≫
        ambientBaseMap p₂.toBase.hom r.toBase.hom f.hom g₂.hom hr.1 =
        pullback.lift (pullback.fst q.toBase.hom f.hom ≫ g₂.hom)
          (pullback.snd q.toBase.hom f.hom) hc₂ := by
      refine eq_pullback_lift _ _ _ ?_ ?_ hc₂
      · rw [Category.assoc, ambientBaseMap_fst, ← Category.assoc, ambientBaseMap_fst,
          Category.comp_id]
      · rw [Category.assoc, ambientBaseMap_snd, ambientBaseMap_snd]
    rw [isPairBaseChange_subspace B S hS f hq, isPairBaseChange_subspace B S hS f hr,
      ← Subfunctor.preimage_comp, hκ]
    exact hsub hc₁ hc₂


namespace FinitePartUniversalOpen

variable {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicGeometry.AlgebraicSpaces C S hS}
  {G : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B}

/-! ### Reading the twisted pair through the universal open subspace -/

/-- The preimage of the open subspace of the twisted pair under a section of its ambient fibre
product is the preimage of the universal open subspace under untwisting: the section `(y, r)`
lies in the twisted pair exactly when `(s'(y), c(r, z(y)))` lies in `Z_univ`. -/
public theorem targetPair_preimage_untwist (F : FinitePartUniversalOpen G)
    {Amb : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (φ : Amb ⟶ F.arrows.obj) (ψ : Amb ⟶ G.arrows.obj)
    (hM : φ ≫ F.targetPair.toBase.hom = ψ ≫ G.source.hom)
    (hc : ψ ≫ G.source.hom = (φ ≫ F.arrowMap.hom) ≫ G.target.hom)
    (hU : (φ ≫ F.source.hom) ≫ F.universalOpen.toBase.hom =
      composeMor G ψ (φ ≫ F.arrowMap.hom) hc ≫ G.source.hom) :
    F.targetPair.subspace.preimage (pullback.lift φ ψ hM) =
      F.universalOpen.subspace.preimage
        (pullback.lift (φ ≫ F.source.hom)
          (composeMor G ψ (φ ≫ F.arrowMap.hom) hc) hU) := by
  rw [F.targetPair_subspace_preimage, ← Subfunctor.preimage_comp]
  refine congrArg (fun m => F.universalOpen.subspace.preimage m) ?_
  have h1 : pullback.lift φ ψ hM ≫
      pullback.snd F.targetPair.toBase.hom G.source.hom = ψ :=
    pullback.lift_snd _ _ _
  have h2 : pullback.lift φ ψ hM ≫
      (pullback.fst F.targetPair.toBase.hom G.source.hom ≫ F.arrowMap.hom) =
      φ ≫ F.arrowMap.hom := by
    rw [← Category.assoc, pullback.lift_fst]
  have hc' : (pullback.lift φ ψ hM ≫
        pullback.snd F.targetPair.toBase.hom G.source.hom) ≫ G.source.hom =
      (pullback.lift φ ψ hM ≫
        (pullback.fst F.targetPair.toBase.hom G.source.hom ≫ F.arrowMap.hom)) ≫
        G.target.hom := by
    rw [h1, h2]
    exact hc
  refine eq_pullback_lift _ _ _ ?_ ?_ hU
  · calc (pullback.lift φ ψ hM ≫ F.untwistAmbient ≫ F.baseChangeAmbient) ≫
          pullback.fst F.universalOpen.toBase.hom G.source.hom
        = pullback.lift φ ψ hM ≫ F.untwistAmbient ≫ F.baseChangeAmbient ≫
            pullback.fst F.universalOpen.toBase.hom G.source.hom := by
              simp only [Category.assoc]
      _ = pullback.lift φ ψ hM ≫ F.untwistAmbient ≫
            pullback.fst (F.source ≫ F.universalOpen.toBase).hom G.source.hom ≫
              F.source.hom := by rw [F.baseChangeAmbient_fst]
      _ = pullback.lift φ ψ hM ≫ (F.untwistAmbient ≫
            pullback.fst (F.source ≫ F.universalOpen.toBase).hom G.source.hom) ≫
              F.source.hom := by simp only [Category.assoc]
      _ = pullback.lift φ ψ hM ≫
            pullback.fst F.targetPair.toBase.hom G.source.hom ≫ F.source.hom := by
              rw [F.untwistAmbient_fst]
      _ = (pullback.lift φ ψ hM ≫
            pullback.fst F.targetPair.toBase.hom G.source.hom) ≫ F.source.hom :=
            (Category.assoc _ _ _).symm
      _ = φ ≫ F.source.hom := by rw [pullback.lift_fst]
  · calc (pullback.lift φ ψ hM ≫ F.untwistAmbient ≫ F.baseChangeAmbient) ≫
          pullback.snd F.universalOpen.toBase.hom G.source.hom
        = pullback.lift φ ψ hM ≫ F.untwistAmbient ≫ F.baseChangeAmbient ≫
            pullback.snd F.universalOpen.toBase.hom G.source.hom := by
              simp only [Category.assoc]
      _ = pullback.lift φ ψ hM ≫ F.untwistAmbient ≫
            pullback.snd (F.source ≫ F.universalOpen.toBase).hom G.source.hom := by
              rw [F.baseChangeAmbient_snd]
      _ = pullback.lift φ ψ hM ≫ (F.untwistAmbient ≫
            pullback.snd (F.source ≫ F.universalOpen.toBase).hom G.source.hom) := rfl
      _ = pullback.lift φ ψ hM ≫ composeMor G
            (pullback.snd F.targetPair.toBase.hom G.source.hom)
            (pullback.fst F.targetPair.toBase.hom G.source.hom ≫ F.arrowMap.hom)
            F.targetPair_ambient_condition := by
              rw [F.untwistAmbient_snd_composeMor]
      _ = composeMor G
            (pullback.lift φ ψ hM ≫
              pullback.snd F.targetPair.toBase.hom G.source.hom)
            (pullback.lift φ ψ hM ≫
              (pullback.fst F.targetPair.toBase.hom G.source.hom ≫ F.arrowMap.hom))
            hc' := comp_composeMor G _ _ _ _ hc'
      _ = composeMor G ψ (φ ≫ F.arrowMap.hom) hc :=
            composeMor_congr G _ _ _ _ hc' hc h1 h2

/-- The preimage of the open subspace of the twisted pair under a section of its ambient fibre
product is the preimage of the universal open subspace read at the target: the section `(y, r)`
lies in the twisted pair exactly when `(t'(y), r)` lies in `Z_univ`. -/
public theorem targetPair_preimage_target (F : FinitePartUniversalOpen G)
    {Amb : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (φ : Amb ⟶ F.arrows.obj) (ψ : Amb ⟶ G.arrows.obj)
    (hM : φ ≫ F.targetPair.toBase.hom = ψ ≫ G.source.hom)
    (hU : (φ ≫ F.target.hom) ≫ F.universalOpen.toBase.hom = ψ ≫ G.source.hom) :
    F.targetPair.subspace.preimage (pullback.lift φ ψ hM) =
      F.universalOpen.subspace.preimage
        (pullback.lift (φ ≫ F.target.hom) ψ hU) := by
  rw [F.targetPair_subspace_eq, ← Subfunctor.preimage_comp]
  refine congrArg (fun m => F.universalOpen.subspace.preimage m) ?_
  refine eq_pullback_lift _ _ _ ?_ ?_ hU
  · rw [Category.assoc, F.targetAmbientLift_fst, ← Category.assoc, pullback.lift_fst]
  · rw [Category.assoc, F.targetAmbientLift_snd, pullback.lift_snd]

/-- **The cocycle identity.** For three morphisms into the arrow space of the finite part with
`φ₃ ≫ t' = φ₂ ≫ s'`, `φ₁ ≫ s' = φ₃ ≫ s'` and arrow `φ₁ ≫ z = c(φ₂ ≫ z, φ₃ ≫ z)`, the twisted
pair has the same preimage along the section determined by `φ₁` as along the one determined by
`φ₂`: on points this is `c(c(Z₂, i ∘ z₂), i ∘ z₁) = c(Z₂, i ∘ c(z₁, z₂))`. -/
public theorem targetPair_preimage_lift_eq (F : FinitePartUniversalOpen G)
    {Amb : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (φ₁ φ₂ φ₃ : Amb ⟶ F.arrows.obj) (ψ : Amb ⟶ G.arrows.obj)
    (hM₁ : φ₁ ≫ F.targetPair.toBase.hom = ψ ≫ G.source.hom)
    (hM₂ : φ₂ ≫ F.targetPair.toBase.hom = ψ ≫ G.source.hom)
    (hsrc : φ₁ ≫ F.source.hom = φ₃ ≫ F.source.hom)
    (hcond : φ₃ ≫ F.target.hom = φ₂ ≫ F.source.hom)
    (harrc : (φ₂ ≫ F.arrowMap.hom) ≫ G.source.hom =
      (φ₃ ≫ F.arrowMap.hom) ≫ G.target.hom)
    (harr : φ₁ ≫ F.arrowMap.hom =
      composeMor G (φ₂ ≫ F.arrowMap.hom) (φ₃ ≫ F.arrowMap.hom) harrc) :
    F.targetPair.subspace.preimage (pullback.lift φ₁ ψ hM₁) =
      F.targetPair.subspace.preimage (pullback.lift φ₂ ψ hM₂) := by
  have hc₁ := F.targetPair_ambient_cond φ₁ ψ hM₁
  have hc₂ := F.targetPair_ambient_cond φ₂ ψ hM₂
  have hU₁ := F.untwist_base_condition φ₁ ψ hc₁
  have hU₄ := F.untwist_base_condition φ₂ ψ hc₂
  have hN : φ₃ ≫ F.targetPair.toBase.hom =
      composeMor G ψ (φ₂ ≫ F.arrowMap.hom) hc₂ ≫ G.source.hom := by
    rw [F.targetPair_toBase_hom, F.arrowMap_comp_target_hom, reassoc_of% hcond,
      ← F.arrowMap_comp_source_hom, composeMor_comp_source, Category.assoc]
  have hc₃ := F.targetPair_ambient_cond φ₃
    (composeMor G ψ (φ₂ ≫ F.arrowMap.hom) hc₂) hN
  have hU₂ := F.untwist_base_condition φ₃
    (composeMor G ψ (φ₂ ≫ F.arrowMap.hom) hc₂) hc₃
  have hU₃ := F.untwist_target_condition φ₃
    (composeMor G ψ (φ₂ ≫ F.arrowMap.hom) hc₂) hN
  have h₄ : ψ ≫ G.source.hom =
      composeMor G (φ₂ ≫ F.arrowMap.hom) (φ₃ ≫ F.arrowMap.hom) harrc ≫
        G.target.hom := hc₂.trans (composeMor_comp_target G _ _ harrc).symm
  have hBeq : composeMor G ψ (φ₁ ≫ F.arrowMap.hom) hc₁ =
      composeMor G (composeMor G ψ (φ₂ ≫ F.arrowMap.hom) hc₂)
        (φ₃ ≫ F.arrowMap.hom) hc₃ :=
    (composeMor_congr G _ _ _ _ hc₁ h₄ rfl harr).trans
      (composeMor_assoc G ψ (φ₂ ≫ F.arrowMap.hom) (φ₃ ≫ F.arrowMap.hom)
        hc₂ harrc hc₃ h₄).symm
  calc F.targetPair.subspace.preimage (pullback.lift φ₁ ψ hM₁)
      = F.universalOpen.subspace.preimage
          (pullback.lift (φ₁ ≫ F.source.hom)
            (composeMor G ψ (φ₁ ≫ F.arrowMap.hom) hc₁) hU₁) :=
        F.targetPair_preimage_untwist φ₁ ψ hM₁ hc₁ hU₁
    _ = F.universalOpen.subspace.preimage
          (pullback.lift (φ₃ ≫ F.source.hom)
            (composeMor G (composeMor G ψ (φ₂ ≫ F.arrowMap.hom) hc₂)
              (φ₃ ≫ F.arrowMap.hom) hc₃) hU₂) :=
        congrArg (fun m => F.universalOpen.subspace.preimage m)
          (pullback_lift_congr _ _ _ _ hU₁ hU₂ hsrc hBeq)
    _ = F.targetPair.subspace.preimage
          (pullback.lift φ₃ (composeMor G ψ (φ₂ ≫ F.arrowMap.hom) hc₂) hN) :=
        (F.targetPair_preimage_untwist φ₃
          (composeMor G ψ (φ₂ ≫ F.arrowMap.hom) hc₂) hN hc₃ hU₂).symm
    _ = F.universalOpen.subspace.preimage
          (pullback.lift (φ₃ ≫ F.target.hom)
            (composeMor G ψ (φ₂ ≫ F.arrowMap.hom) hc₂) hU₃) :=
        F.targetPair_preimage_target φ₃
          (composeMor G ψ (φ₂ ≫ F.arrowMap.hom) hc₂) hN hU₃
    _ = F.universalOpen.subspace.preimage
          (pullback.lift (φ₂ ≫ F.source.hom)
            (composeMor G ψ (φ₂ ≫ F.arrowMap.hom) hc₂) hU₄) :=
        congrArg (fun m => F.universalOpen.subspace.preimage m)
          (pullback_lift_congr _ _ _ _ hU₃ hU₄ hcond rfl)
    _ = F.targetPair.subspace.preimage (pullback.lift φ₂ ψ hM₂) :=
        (F.targetPair_preimage_untwist φ₂ ψ hM₂ hc₂ hU₄).symm

/-- The cocycle identity, read after precomposition with a morphism of presheaves. -/
private theorem targetPair_preimage_lift_eq_comp (F : FinitePartUniversalOpen G)
    {Amb Y₀ : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (π : Amb ⟶ Y₀) (h k k₂ : Y₀ ⟶ F.arrows.obj) (ψ : Amb ⟶ G.arrows.obj)
    (hcond : k₂ ≫ F.target.hom = k ≫ F.source.hom)
    (hsrc : h ≫ F.source.hom = k₂ ≫ F.source.hom)
    (harrc : (k ≫ F.arrowMap.hom) ≫ G.source.hom =
      (k₂ ≫ F.arrowMap.hom) ≫ G.target.hom)
    (harr : h ≫ F.arrowMap.hom =
      composeMor G (k ≫ F.arrowMap.hom) (k₂ ≫ F.arrowMap.hom) harrc)
    (hM₁ : (π ≫ h) ≫ F.targetPair.toBase.hom = ψ ≫ G.source.hom)
    (hM₂ : (π ≫ k) ≫ F.targetPair.toBase.hom = ψ ≫ G.source.hom) :
    F.targetPair.subspace.preimage (pullback.lift (π ≫ h) ψ hM₁) =
      F.targetPair.subspace.preimage (pullback.lift (π ≫ k) ψ hM₂) := by
  have hsrc' : (π ≫ h) ≫ F.source.hom = (π ≫ k₂) ≫ F.source.hom := by
    rw [Category.assoc, hsrc, Category.assoc]
  have hcond' : (π ≫ k₂) ≫ F.target.hom = (π ≫ k) ≫ F.source.hom := by
    rw [Category.assoc, hcond, Category.assoc]
  have hX : (π ≫ (k ≫ F.arrowMap.hom)) ≫ G.source.hom =
      (π ≫ (k₂ ≫ F.arrowMap.hom)) ≫ G.target.hom := by
    simpa only [Category.assoc] using congrArg (π ≫ ·) harrc
  have harrc' : ((π ≫ k) ≫ F.arrowMap.hom) ≫ G.source.hom =
      ((π ≫ k₂) ≫ F.arrowMap.hom) ≫ G.target.hom := by
    simpa only [Category.assoc] using hX
  have harr' : (π ≫ h) ≫ F.arrowMap.hom =
      composeMor G ((π ≫ k) ≫ F.arrowMap.hom) ((π ≫ k₂) ≫ F.arrowMap.hom) harrc' :=
    calc (π ≫ h) ≫ F.arrowMap.hom
        = π ≫ h ≫ F.arrowMap.hom := Category.assoc _ _ _
      _ = π ≫ composeMor G (k ≫ F.arrowMap.hom) (k₂ ≫ F.arrowMap.hom) harrc := by
            rw [harr]
      _ = composeMor G (π ≫ k ≫ F.arrowMap.hom) (π ≫ k₂ ≫ F.arrowMap.hom) hX :=
            comp_composeMor G π _ _ harrc hX
      _ = composeMor G ((π ≫ k) ≫ F.arrowMap.hom) ((π ≫ k₂) ≫ F.arrowMap.hom) harrc' :=
            composeMor_congr G _ _ _ _ hX harrc'
              (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm
  exact F.targetPair_preimage_lift_eq (π ≫ h) (π ≫ k) (π ≫ k₂) ψ hM₁ hM₂
    hsrc' hcond' harrc' harr'

/-! ### The pairs classified at a section -/

/-- The pair which the classifying morphism of the twisted pair names at a morphism out of a
scheme of the site is the base change of the twisted pair along that morphism. -/
private theorem isPairBaseChange_targetClassify (F : FinitePartUniversalOpen G)
    (V : AlgebraicGeometry.BigFppfOver C S hS) (h : yoneda.obj V ⟶ F.arrows.obj) :
    IsPairBaseChange C S hS G.source
      (ObjectProperty.homMk h : AlgebraicGeometry.schemeSpace V ⟶ F.arrows)
      F.targetPair
      ((AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS G.source).sections V
        (F.targetClassify.app (op V) (yonedaEquiv h))) := by
  have spec := (finiteOpenSubspaceEquiv C S hS G.source F.arrows).2 F.targetClassify V h
  rwa [show (finiteOpenSubspaceEquiv C S hS G.source F.arrows).1 F.targetClassify =
    F.targetPair from Equiv.apply_symm_apply _ _] at spec

/-- The pair which the inclusion of the object space names at a morphism out of a scheme of the
site is the base change of the universal pair along that morphism. -/
private theorem isPairBaseChange_objectsInclusion (F : FinitePartUniversalOpen G)
    (V : AlgebraicGeometry.BigFppfOver C S hS) (m : yoneda.obj V ⟶ F.objects.obj) :
    IsPairBaseChange C S hS G.source
      (ObjectProperty.homMk m : AlgebraicGeometry.schemeSpace V ⟶ F.objects)
      F.universalOpen
      ((AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS G.source).sections V
        (F.objectsInclusion.app (op V) (yonedaEquiv m))) := by
  have spec := (finiteOpenSubspaceEquiv C S hS G.source F.objects).2 F.objectsInclusion V m
  rwa [F.objectsInclusion_spec] at spec

/-! ### The target of a composite -/

/-- At a composable triple of morphisms out of a scheme of the site the target morphism
classifies the same pair after composing as on the first entry. -/
public theorem targetClassify_app_eq_of_composable (F : FinitePartUniversalOpen G)
    (V : AlgebraicGeometry.BigFppfOver C S hS)
    (h k k₂ : yoneda.obj V ⟶ F.arrows.obj)
    (hcond : k₂ ≫ F.target.hom = k ≫ F.source.hom)
    (hsrc : h ≫ F.source.hom = k₂ ≫ F.source.hom)
    (harrc : (k ≫ F.arrowMap.hom) ≫ G.source.hom =
      (k₂ ≫ F.arrowMap.hom) ≫ G.target.hom)
    (harr : h ≫ F.arrowMap.hom =
      composeMor G (k ≫ F.arrowMap.hom) (k₂ ≫ F.arrowMap.hom) harrc) :
    F.targetClassify.app (op V) (yonedaEquiv h) =
      F.targetClassify.app (op V) (yonedaEquiv k) := by
  have hq := F.isPairBaseChange_targetClassify V h
  have hr := F.isPairBaseChange_targetClassify V k
  have etp := F.targetPair_toBase_hom
  have hbase' : h ≫ F.targetPair.toBase.hom = k ≫ F.targetPair.toBase.hom :=
    calc h ≫ F.targetPair.toBase.hom
        = h ≫ F.arrowMap.hom ≫ G.target.hom := by rw [etp]
      _ = (h ≫ F.arrowMap.hom) ≫ G.target.hom := (Category.assoc _ _ _).symm
      _ = composeMor G (k ≫ F.arrowMap.hom) (k₂ ≫ F.arrowMap.hom) harrc ≫
            G.target.hom := by rw [harr]
      _ = (k ≫ F.arrowMap.hom) ≫ G.target.hom := composeMor_comp_target G _ _ harrc
      _ = k ≫ F.arrowMap.hom ≫ G.target.hom := Category.assoc _ _ _
      _ = k ≫ F.targetPair.toBase.hom := by rw [etp]
  apply Equiv.injective
    ((AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS G.source).sections V)
  refine pair_eq_of_isPairBaseChange C S hS G.source _ _ hq hr hbase' fun _ _ => ?_
  exact F.targetPair_preimage_lift_eq_comp
    (pullback.fst
      ((AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS G.source).sections V
        (F.targetClassify.app (op V) (yonedaEquiv h))).toBase.hom G.source.hom)
    h k k₂ _ hcond hsrc harrc harr _ _

/-- **Stacks 04RU, clause (3).** The target of a composite is the target of its first entry;
on points this is the cocycle identity `c(c(Z₂, i ∘ z₂), i ∘ z₁) = c(Z₂, i ∘ c(z₁, z₂))`
between open subspaces. -/
public theorem comp_hom_comp_targetClassify (F : FinitePartUniversalOpen G) :
    F.comp.hom ≫ F.targetClassify = F.compFst ≫ F.targetClassify := by
  ext V p
  have hcond : yonedaEquiv.symm (F.compSnd.app V p) ≫ F.target.hom =
      yonedaEquiv.symm (F.compFst.app V p) ≫ F.source.hom := by
    rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right]
    exact congrArg (fun z => yonedaEquiv.symm z)
      (congrArg (fun m => m.app V p) F.comp_condition).symm
  have hsrc : yonedaEquiv.symm (F.comp.hom.app V p) ≫ F.source.hom =
      yonedaEquiv.symm (F.compSnd.app V p) ≫ F.source.hom := by
    rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right]
    exact congrArg (fun z => yonedaEquiv.symm z)
      (congrArg (fun m => m.app V p) F.comp_hom_comp_source)
  have harrc : (yonedaEquiv.symm (F.compFst.app V p) ≫ F.arrowMap.hom) ≫ G.source.hom =
      (yonedaEquiv.symm (F.compSnd.app V p) ≫ F.arrowMap.hom) ≫ G.target.hom := by
    rw [Category.assoc, Category.assoc, yonedaEquiv_symm_naturality_right,
      yonedaEquiv_symm_naturality_right]
    exact congrArg (fun z => yonedaEquiv.symm z) (F.comp_composable_app V p)
  have hnat : ∀ (m : (AlgebraicGeometry.AlgebraicSpaces.fiberProduct C S hS
        F.source F.target).obj ⟶ F.arrows.obj)
      (V' : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
      (w : (yoneda.obj V.unop).obj V'),
      (yonedaEquiv.symm (m.app V p) ≫ F.arrowMap.hom).app V' w =
        F.arrowMap.hom.app V' (m.app V'
          ((AlgebraicGeometry.AlgebraicSpaces.fiberProduct C S hS
            F.source F.target).obj.map w.op p)) := by
    intro m V' w
    show F.arrowMap.hom.app V' (F.arrows.obj.map w.op (m.app V p)) = _
    exact congrArg (fun z => F.arrowMap.hom.app V' z)
      (NatTrans.naturality_apply m w.op p).symm
  have harr : yonedaEquiv.symm (F.comp.hom.app V p) ≫ F.arrowMap.hom =
      composeMor G (yonedaEquiv.symm (F.compFst.app V p) ≫ F.arrowMap.hom)
        (yonedaEquiv.symm (F.compSnd.app V p) ≫ F.arrowMap.hom) harrc := by
    ext V' w
    have hx : G.source.hom.app V'
        ((yonedaEquiv.symm (F.compFst.app V p) ≫ F.arrowMap.hom).app V' w) =
        G.target.hom.app V'
          ((yonedaEquiv.symm (F.compSnd.app V p) ≫ F.arrowMap.hom).app V' w) :=
      congrArg (fun z => z.app V' w) harrc
    show (yonedaEquiv.symm (F.comp.hom.app V p) ≫ F.arrowMap.hom).app V' w =
      (composeMor G (yonedaEquiv.symm (F.compFst.app V p) ≫ F.arrowMap.hom)
        (yonedaEquiv.symm (F.compSnd.app V p) ≫ F.arrowMap.hom) harrc).app V' w
    refine ((hnat F.comp.hom V' w).trans ?_).trans
      (composeMor_app G _ _ harrc V' w hx).symm
    refine (F.comp_arrowMap_app V' _).trans ?_
    exact compose_congr G V' _ _ _ _ (F.comp_composable_app V' _) hx
      (hnat F.compFst V' w).symm (hnat F.compSnd V' w).symm
  have key := F.targetClassify_app_eq_of_composable V.unop
    (yonedaEquiv.symm (F.comp.hom.app V p))
    (yonedaEquiv.symm (F.compFst.app V p))
    (yonedaEquiv.symm (F.compSnd.app V p)) hcond hsrc harrc harr
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at key
  exact key

/-- The inclusion of the object space of the finite part into the finite part presheaf is a
monomorphism, being an isomorphism followed by the inclusion of a subfunctor. -/
public theorem mono_objectsInclusion (F : FinitePartUniversalOpen G) :
    Mono F.objectsInclusion := by
  show Mono (F.objectsEquiv.hom ≫
    (finitePartWithSection C S hS G.source F.unit F.unit_source).toSubfunctor.ι)
  infer_instance

/-- Two morphisms into the object space of the finite part which name the same sections of the
finite part presheaf are equal. -/
public theorem objects_hom_ext (F : FinitePartUniversalOpen G)
    {X : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a b : X ⟶ F.objects.obj)
    (h : a ≫ F.objectsInclusion = b ≫ F.objectsInclusion) : a = b := by
  have := F.mono_objectsInclusion
  exact (cancel_mono F.objectsInclusion).1 h

/-- **Stacks 04RU, clause (3).** `t' ∘ c' = t' ∘ pr₁`: the target of a composite of the finite
part is the target of its first entry. -/
public theorem comp_hom_comp_target (F : FinitePartUniversalOpen G) :
    F.comp.hom ≫ F.target.hom = F.compFst ≫ F.target.hom := by
  refine F.objects_hom_ext _ _ ?_
  rw [Category.assoc, Category.assoc, F.target_comp_objectsInclusion]
  exact F.comp_hom_comp_targetClassify

/-- **Stacks 04RU, clause (3).** The composition of the finite part is compatible with the
target morphism, in the form the groupoid axiom asks for. -/
public theorem comp_comp_target (F : FinitePartUniversalOpen G) :
    F.comp ≫ F.target =
      (ObjectProperty.homMk F.compFst :
        AlgebraicGeometry.AlgebraicSpaces.fiberProduct C S hS F.source F.target ⟶
          F.arrows) ≫ F.target :=
  ObjectProperty.hom_ext _ F.comp_hom_comp_target

/-! ### The target of the unit -/

/-- The unit of the finite part followed by the arrow map is the unit of the groupoid. -/
private theorem unitMap_hom_comp_arrowMap_hom (F : FinitePartUniversalOpen G) :
    F.unitMap.hom ≫ F.arrowMap.hom = F.universalOpen.toBase.hom ≫ F.unit.hom :=
  congrArg (fun z : F.objects ⟶ G.arrows => z.hom) F.unitMap_comp_arrowMap

/-- The preimage of the open subspace of the twisted pair under the unit section of its ambient
fibre product is the preimage of the universal open subspace: on points this is
`c(Z, i ∘ e(u)) = Z`, which is the right unit law `c(r, e(s(r))) = r`. -/
private theorem targetPair_preimage_unit_eq (F : FinitePartUniversalOpen G)
    {Amb : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (φ : Amb ⟶ F.arrows.obj) (μ : Amb ⟶ F.objects.obj) (ψ : Amb ⟶ G.arrows.obj)
    (hφu : φ = μ ≫ F.unitMap.hom)
    (hM : φ ≫ F.targetPair.toBase.hom = ψ ≫ G.source.hom)
    (hN : μ ≫ F.universalOpen.toBase.hom = ψ ≫ G.source.hom) :
    F.targetPair.subspace.preimage (pullback.lift φ ψ hM) =
      F.universalOpen.subspace.preimage (pullback.lift μ ψ hN) := by
  subst hφu
  have hunitSource : F.unitMap.hom ≫ F.source.hom = 𝟙 F.objects.obj :=
    congrArg (fun z : F.objects ⟶ F.objects => z.hom) F.unitMap_comp_source
  have hc := F.targetPair_ambient_cond (μ ≫ F.unitMap.hom) ψ hM
  have hU := F.untwist_base_condition (μ ≫ F.unitMap.hom) ψ hc
  have hφ : (μ ≫ F.unitMap.hom) ≫ F.source.hom = μ := by
    rw [Category.assoc, hunitSource, Category.comp_id]
  have hφam : (μ ≫ F.unitMap.hom) ≫ F.arrowMap.hom =
      ψ ≫ G.source.hom ≫ F.unit.hom := by
    rw [Category.assoc, F.unitMap_hom_comp_arrowMap_hom, reassoc_of% hN]
  have h' : ψ ≫ G.source.hom = (ψ ≫ G.source.hom ≫ F.unit.hom) ≫ G.target.hom := by
    simp only [Category.assoc, F.unit_comp_target, Category.comp_id]
  have hψ : composeMor G ψ ((μ ≫ F.unitMap.hom) ≫ F.arrowMap.hom) hc = ψ :=
    (composeMor_congr G _ _ _ _ hc h' rfl hφam).trans
      (composeMor_unit_right G F.unit F.unit_identity ψ h')
  rw [F.targetPair_preimage_untwist (μ ≫ F.unitMap.hom) ψ hM hc hU]
  exact congrArg (fun z => F.universalOpen.subspace.preimage z)
    (pullback_lift_congr _ _ _ _ hU hN hφ hψ)

/-- The pair which the target morphism names at the unit is the universal pair itself: on
points this is `c(Z, i ∘ e(u)) = Z`. -/
public theorem targetClassify_unitMap_app (F : FinitePartUniversalOpen G)
    (V : AlgebraicGeometry.BigFppfOver C S hS) (m : yoneda.obj V ⟶ F.objects.obj) :
    F.targetClassify.app (op V) (yonedaEquiv (m ≫ F.unitMap.hom)) =
      F.objectsInclusion.app (op V) (yonedaEquiv m) := by
  have hq := F.isPairBaseChange_targetClassify V (m ≫ F.unitMap.hom)
  have hr := F.isPairBaseChange_objectsInclusion V m
  have hbase' : (m ≫ F.unitMap.hom) ≫ F.targetPair.toBase.hom =
      m ≫ F.universalOpen.toBase.hom := by
    simp only [Category.assoc, F.targetPair_toBase_hom, reassoc_of% F.unitMap_hom_comp_arrowMap_hom,
      F.unit_comp_target, Category.comp_id]
  apply Equiv.injective
    ((AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS G.source).sections V)
  refine pair_eq_of_isPairBaseChange C S hS G.source _ _ hq hr hbase' fun _ _ => ?_
  exact F.targetPair_preimage_unit_eq _ _ _ (Category.assoc _ _ _).symm _ _

/-- **Stacks 04RU, clause (3).** `t' ∘ e' = 𝟙`: the unit of the finite part is a section of
its target morphism as well as of its source morphism. -/
public theorem unitMap_comp_target (F : FinitePartUniversalOpen G) :
    F.unitMap ≫ F.target = 𝟙 F.objects := by
  apply ObjectProperty.hom_ext
  show F.unitMap.hom ≫ F.target.hom = 𝟙 F.objects.obj
  refine F.objects_hom_ext _ _ ?_
  rw [Category.assoc, F.target_comp_objectsInclusion, Category.id_comp]
  ext V x
  show F.targetClassify.app V (F.unitMap.hom.app V x) = F.objectsInclusion.app V x
  have key := F.targetClassify_unitMap_app V.unop (yonedaEquiv.symm x)
  rwa [yonedaEquiv_symm_naturality_right, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply] at key

end FinitePartUniversalOpen

end AlgebraicGeometry.Space

end
