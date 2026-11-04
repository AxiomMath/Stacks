module

public import Mathlib.CategoryTheory.Sites.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites

/-! # Inverse systems of sites with finite coverings

Stacks 0A34 is a "situation", i.e. a package of data rather than a proposition: a cofiltered
index category, a site with finite coverings at each index, and transition functors running
opposite to the index morphisms which are morphisms of sites, compatible with composition and
identities.

The Mathlib counterparts of the ingredients are `CategoryTheory.GrothendieckTopology` for a site,
`CategoryTheory.IsCofiltered` for the index category, and `CategoryTheory.Functor.IsContinuous`
for a morphism of sites (which, as in Stacks 00WV and 00X1, points the opposite way to its
underlying functor).

Stacks 0A34 (3) asks each transition to be a morphism of sites `f_a` given by a functor `u_a`
*continuous in the sense of Stacks 00WV*, and that is two conditions: `u_a` sends coverings to
coverings, and `u_a` preserves the fibre product of a member of a covering with an arbitrary
morphism into its base. `Functor.IsContinuous` is not that definition but the *conclusion* Stacks
00WW draws from it — restriction along `u_a` carries sheaves to sheaves — and the second condition
does not follow from it, so each is a field of its own, `coverPreserving` and
`preservesPullbacks`, next to the existence of those fibre products (`hasPullbacks`,
Stacks 00VH (3)).

## Main definitions

* `InverseSystemOfSites`: the data of an inverse system of sites with finite coverings
  (Stacks 0A34).
* `InverseSystemOfFiniteSites`: the same data carrying the finiteness condition the source
  imposes, namely that every covering sieve *contains* a finite covering family rather than being
  *generated* by one (Stacks 0A34).

## Main results

* `InverseSystemOfSites.continuous`: the transition functors are continuous in Mathlib's sense,
  that being one half of the morphism-of-sites condition.
* `InverseSystemOfSites.toInverseSystemOfFiniteSites`: a system whose covering sieves are finitely
  generated is in particular one whose coverings are finite.

## References

* [Stacks 0A34](https://stacks.math.columbia.edu/tag/0A34)
* [Stacks 00VH](https://stacks.math.columbia.edu/tag/00VH)
* [Stacks 00WV](https://stacks.math.columbia.edu/tag/00WV)

Tags covered: 0A34.
-/

@[expose] public section

open CategoryTheory

universe v u u'

/-- An *inverse system of sites with finite coverings*, following the Stacks
Project tag `situation-inverse-limit-sites`.

The data consists of:

* a cofiltered index category `I`;
* for each `i : I`, a (small) category `C i` equipped with a Grothendieck
  topology `J i` such that every covering sieve admits a finite generating family;
* for each morphism `a : i ⟶ j` in `I`, a functor `u a : C j ⥤ C i` continuous in the sense of
  Stacks 00WV and giving a morphism of sites in the sense of Stacks 00X1 (note the reversed
  direction: the morphism of sites `f a : C i ⟶ C j` is given by `u a : C j ⥤ C i`);
* compatibility with composition `u (b ≫ a) = u a ⋙ u b` and identities
  `u (𝟙 i) = 𝟭 (C i)`.
-/
@[stacks_fixed 0A34]
structure InverseSystemOfSites where
  /-- The index category. -/
  I : Type u
  /-- The category structure on the index. -/
  [catI : Category.{v} I]
  /-- The index category is cofiltered. -/
  [cofiltered : IsCofiltered I]
  /-- The underlying category at each index. -/
  C : I → Type u'
  /-- Each `C i` is a small category. Smallness is forced rather than chosen:
  `Functor.IsMorphismOfSites` is stated for `Type u`-valued sheaves over
  `[SmallCategory _]`, that being what supplies `HasWeakSheafify` and hence
  `sheafPullback`, so it is the only setting in which the exactness of `f_a^{-1}`
  below can be *stated* at all. Stacks 00VH sites are small, and every dependent
  already instantiates this structure at a small category. -/
  [catC : ∀ i, SmallCategory (C i)]
  /-- The Grothendieck topology at each index. -/
  J : ∀ i, GrothendieckTopology (C i)
  /-- Finiteness condition: every covering sieve admits a finite generating family. -/
  finiteCoverings : ∀ (i : I) {X : C i} (S : Sieve X),
      S ∈ (J i) X →
      ∃ (ι : Type) (_ : Finite ι) (Y : ι → C i) (f : ∀ a, Y a ⟶ X),
        Sieve.generate (Presieve.ofArrows Y f) = S
  /-- The continuous functor `u_a : C j ⥤ C i` associated to `a : i ⟶ j` in `I`.
  Note the reversed direction relative to the morphism of sites. -/
  u : ∀ {i j : I}, (i ⟶ j) → (C j ⥤ C i)
  /-- `f_a : C i ⟶ C j` is a MORPHISM OF SITES, not merely a continuous functor.
  Stacks 0A34 (3) asks for "a morphism of sites `f_a` given by a continuous functor
  `u_a`", and morphism of sites (Stacks 00X1) is continuity PLUS exactness of
  `f_a^{-1}`; 00X1 remarks the exactness cannot be dropped. Recording only
  continuity here made the conclusion of Stacks 0A35 FALSE, by a two-object
  counterexample with both topologies trivial: taking every `J i = ⊥` makes
  continuity hold vacuously (every presheaf is a `⊥`-sheaf) while leaving exactness
  a real condition, and then `f_1^{-1}` is the left Kan extension along `u.op`,
  whose value at `V` is `P W₁ ⊔ P W₂` — two elements at the terminal sheaf, so not
  terminal, so the empty limit is not preserved. -/
  isMorphismOfSites : ∀ {i j : I} (a : i ⟶ j), (u a).IsMorphismOfSites (J j) (J i)
  /-- The coverings of `C i` that are finite admit pullbacks — Stacks 00VH (3), existence half.
  Logically independent of exactness above: the counterexample that forced
  `isMorphismOfSites` has no non-trivial coverings at all, so it says nothing about
  fibre products, and the descent argument of Stacks 0A35 needs both. These are the fibre
  products `preservesPullbacks` speaks about. -/
  hasPullbacks : ∀ i, ((J i).toPrecoverage ⊓ Precoverage.finite (C i)).HasPullbacks
  /-- **Stacks 00WV (1)**: `u_a` sends the coverings of `C j` to coverings of `C i`, a covering
  being — as in Stacks 00VH — a finite family generating a covering sieve.

  This is the first of the two clauses of the source's *definition* of a continuous functor;
  `Functor.IsContinuous`, hence the `isMorphismOfSites` field, is the *conclusion* Stacks 00WW
  draws from that definition, so neither clause can be read off it and each is carried here.
  Mathlib's `CoverPreserving` is the sieve-level form of this clause; the covering-level form
  below is the one Stacks 00VH states, and is what the finiteness of the coverings makes
  available. -/
  coverPreserving : ∀ {i j : I} (a : i ⟶ j),
      ((J j).toPrecoverage ⊓ Precoverage.finite (C j)) ≤
        ((J i).toPrecoverage ⊓ Precoverage.finite (C i)).comap (u a)
  /-- **Stacks 00WV (2)**: `u_a` preserves the fibre products of a covering, namely the ones
  `hasPullbacks` provides — for a member `g : W ⟶ V` of a covering of `V` and an arbitrary
  `f : T ⟶ V`, the canonical map `u_a(T ×_V W) → u_a T ×_{u_a V} u_a W` is an isomorphism.

  Stated against an arbitrary `f`, which is the literal condition of the source and what Stacks
  09YL and 0A35 use: 09YL's axiom (3) transports the fibre products of a covering of a member
  along an arbitrary morphism of that member, and the descent of Stacks 0A35 factors a pair of
  morphisms out of an object of `C l` through `u_a` of a fibre product. Mathlib's
  `Precoverage.PullbacksPreservedBy` is the special case where `f` too is a member of the
  covering, and is weaker.

  Again not a consequence of `isMorphismOfSites`, and in the opposite direction to the
  counterexample that forced it, which has no non-trivial coverings at all: let `C j` be
  `{V, W₁, W₂, A}` with `h_t : W_t ⟶ V` and `A = W₁ ×_V W₂`, let `C i` be that category with an
  extra object `B` and a pair `B ⟶ W₁`, `B ⟶ W₂` over `V` not factoring through `A`, let `J j` be
  generated by `{h₁, h₂}` and `J i` by `{h₁, h₂}` together with the empty covering of `B`. A
  `J i`-sheaf is a one-point set at `B`, so restriction along the inclusion `C j ⥤ C i` has the
  sheaf property for `{h₁, h₂}` — the inclusion is continuous in Mathlib's sense — while the
  inclusion does not preserve `A`. -/
  preservesPullbacks : ∀ {i j : I} (a : i ⟶ j) {V : C j} {R : Presieve V},
      R ∈ ((J j).toPrecoverage ⊓ Precoverage.finite (C j)) V →
      ∀ {W : C j} {g : W ⟶ V}, R g → ∀ {T : C j} (f : T ⟶ V),
        Limits.PreservesLimit (Limits.cospan f g) (u a)
  /-- Compatibility with composition: `u (b ≫ a) = u a ⋙ u b`. -/
  comp : ∀ {i j k : I} (b : i ⟶ j) (a : j ⟶ k),
      u (b ≫ a) = u a ⋙ u b
  /-- The identity morphism in `I` maps to the identity functor. -/
  id_map : ∀ i, u (𝟙 i) = 𝟭 (C i)

attribute [instance] InverseSystemOfSites.catI
attribute [instance] InverseSystemOfSites.cofiltered
attribute [instance] InverseSystemOfSites.catC

/-- The transition functor `u a` is continuous. Kept under its old name and shape so
that every existing `D.continuous a` — Stacks 09YL, 09YN, 0A35, 0EXJ — reads
verbatim as before, now that continuity is one half of the `isMorphismOfSites`
field rather than the whole of a field of its own. -/
theorem InverseSystemOfSites.continuous (D : InverseSystemOfSites.{v, u, u'})
    {i j : D.I} (a : i ⟶ j) : (D.u a).IsContinuous (D.J j) (D.J i) :=
  (D.isMorphismOfSites a).isContinuous

/-- An *inverse system of sites with finite coverings* (Stacks 0A34), carrying the finiteness
condition the source actually imposes.

In Stacks 00VH a site is a category together with a collection of *coverings*, each of which is a
*finite* family of morphisms with a common target, and its Grothendieck topology is the one those
coverings generate. So the content of "the coverings of `C i` are finite" is that the finite
covering families generate `J i`, that is: every covering sieve `S` of `J i` **contains** a finite
covering family. That is the `finiteCoverings` field here.

`InverseSystemOfSites.finiteCoverings` instead asks that every covering sieve be **generated** by a
finite family, which is strictly stronger: `InverseSystemOfSites` is the special case of this
structure in which every covering sieve happens to be finitely generated. Nothing of the kind is
available on the sites this situation is meant for — on `Spec k[t]` the sieve generated by all the
standard opens `D(f)` is a covering sieve of the Zariski, hence also of the étale, topology and is
dominated by no finite subfamily — so no inverse system of étale sites satisfies the stronger
condition and Stacks 09YL could not be applied to one. Every such system does satisfy the
condition below.

Every other field, and the record-level data, is literally that of `InverseSystemOfSites`, so the
two structures are interchangeable wherever `finiteCoverings` is not used; and a strong system is a
weak one, `InverseSystemOfSites.toInverseSystemOfFiniteSites`. -/
@[stacks_fixed 0A34]
structure InverseSystemOfFiniteSites where
  /-- The index category. -/
  I : Type u
  /-- The category structure on the index. -/
  [catI : Category.{v} I]
  /-- The index category is cofiltered. -/
  [cofiltered : IsCofiltered I]
  /-- The underlying category at each index. -/
  C : I → Type u'
  /-- Each `C i` is a small category, for the reason recorded on
  `InverseSystemOfSites.catC`: it is the only setting in which the exactness of `f_a^{-1}` can be
  stated at all. -/
  [catC : ∀ i, SmallCategory (C i)]
  /-- The Grothendieck topology at each index. -/
  J : ∀ i, GrothendieckTopology (C i)
  /-- **Finiteness of the coverings, Stacks 00VH**: every covering sieve of `J i` contains a finite
  covering family, so the coverings of `C i` in the sense of Stacks 00VH — the members of both
  `(J i).toPrecoverage` and `Precoverage.finite (C i)` — generate `J i`. -/
  finiteCoverings : ∀ (i : I) {X : C i} (S : Sieve X),
      S ∈ (J i) X →
      ∃ R : Presieve X, R ≤ S.arrows ∧
        R ∈ (J i).toPrecoverage X ∧ R ∈ Precoverage.finite (C i) X
  /-- The continuous functor `u_a : C j ⥤ C i` associated to `a : i ⟶ j` in `I`.
  Note the reversed direction relative to the morphism of sites. -/
  u : ∀ {i j : I}, (i ⟶ j) → (C j ⥤ C i)
  /-- **Stacks 0A34 (3)**: `f_a : C i ⟶ C j` is a morphism of sites (Stacks 00X1), not merely a
  continuous functor; see `InverseSystemOfSites.isMorphismOfSites` for the counterexample that
  shows the exactness of `f_a^{-1}` cannot be dropped. -/
  isMorphismOfSites : ∀ {i j : I} (a : i ⟶ j), (u a).IsMorphismOfSites (J j) (J i)
  /-- **Stacks 00VH (3)**, existence half: the finite coverings of `C i` admit pullbacks. These
  are the fibre products `preservesPullbacks` speaks about. -/
  hasPullbacks : ∀ i, ((J i).toPrecoverage ⊓ Precoverage.finite (C i)).HasPullbacks
  /-- **Stacks 00WV (1)**: `u_a` sends the coverings of `C j`, in the covering-level sense of
  Stacks 00VH, to coverings of `C i`. The first clause of the source's definition of a continuous
  functor, which cannot be read off `isMorphismOfSites`; see
  `InverseSystemOfSites.coverPreserving`. -/
  coverPreserving : ∀ {i j : I} (a : i ⟶ j),
      ((J j).toPrecoverage ⊓ Precoverage.finite (C j)) ≤
        ((J i).toPrecoverage ⊓ Precoverage.finite (C i)).comap (u a)
  /-- **Stacks 00WV (2)**: `u_a` preserves the fibre product of a member `g` of a covering with an
  arbitrary `f` into its base. Stated against an arbitrary `f`, which is the literal condition of
  the source and what Stacks 09YL and 0A35 use; see
  `InverseSystemOfSites.preservesPullbacks`. -/
  preservesPullbacks : ∀ {i j : I} (a : i ⟶ j) {V : C j} {R : Presieve V},
      R ∈ ((J j).toPrecoverage ⊓ Precoverage.finite (C j)) V →
      ∀ {W : C j} {g : W ⟶ V}, R g → ∀ {T : C j} (f : T ⟶ V),
        Limits.PreservesLimit (Limits.cospan f g) (u a)
  /-- Compatibility with composition: `u (b ≫ a) = u a ⋙ u b`. -/
  comp : ∀ {i j k : I} (b : i ⟶ j) (a : j ⟶ k),
      u (b ≫ a) = u a ⋙ u b
  /-- The identity morphism in `I` maps to the identity functor. -/
  id_map : ∀ i, u (𝟙 i) = 𝟭 (C i)

attribute [instance] InverseSystemOfFiniteSites.catI
attribute [instance] InverseSystemOfFiniteSites.cofiltered
attribute [instance] InverseSystemOfFiniteSites.catC

/-- A system whose covering sieves are finitely *generated* is one whose coverings are finite: if
`Sieve.generate (Presieve.ofArrows Y f) = S` then the finite family `Presieve.ofArrows Y f` is
contained in `S.arrows`, is a covering of `J i`, and is finite. Every field other than
`finiteCoverings` is carried over unchanged, so the two systems have the same record-level data. -/
def InverseSystemOfSites.toInverseSystemOfFiniteSites (D : InverseSystemOfSites.{v, u, u'}) :
    InverseSystemOfFiniteSites.{v, u, u'} where
  I := D.I
  catI := D.catI
  cofiltered := D.cofiltered
  C := D.C
  catC := D.catC
  J := D.J
  finiteCoverings := fun i {X} S hS => by
    obtain ⟨ι, hι, Y, f, hgen⟩ := D.finiteCoverings i S hS
    have := hι
    refine ⟨Presieve.ofArrows Y f, ?_, ?_, Precoverage.ofArrows_mem_finite Y f⟩
    · rw [← hgen]
      exact Sieve.le_generate _
    · rw [GrothendieckTopology.mem_toPrecoverage_iff, hgen]
      exact hS
  u := D.u
  isMorphismOfSites := D.isMorphismOfSites
  hasPullbacks := D.hasPullbacks
  coverPreserving := D.coverPreserving
  preservesPullbacks := D.preservesPullbacks
  comp := D.comp
  id_map := D.id_map
