module

public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.CategoryTheory.MorphismProperty.Ind
public import Mathlib.CategoryTheory.Presentable.StrongGenerator
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski
public import StacksFrontier.RingTheory.ColimitPresentation.Canonical

/-!
# Local isomorphisms as a morphism property, and the composition of ind-Zariski maps

A ring map is *ind-Zariski* when its target is a filtered colimit, as an algebra over the
source, of local isomorphisms (`AlgebraicGeometry.ProEtale.IsIndZariski`, Tag 096N). This file
sets up the morphism-property calculus for local isomorphisms of rings and uses it to reduce the
composition-stability of ind-Zariski maps to a single named spreading-out statement.

The pattern is the one the ind-étale theory in this repository already follows: a property of
ring maps is turned into a `CategoryTheory.MorphismProperty` on `CommRingCat`, its permanence
properties are recorded as instances, and `CategoryTheory.MorphismProperty.ind` of it is then
handled by the general machinery of `Mathlib.CategoryTheory.MorphismProperty.Ind`.

## Main definitions

* `RingHom.IsLocalIso`: being a local isomorphism, for a bare ring map rather than for an
  algebra. This is `Algebra.IsLocalIso` read through `RingHom.toAlgebra`.
* `CommRingCat.localIso` (imported): being a local isomorphism, as a morphism property on
  `CommRingCat`. It is defined in `StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski` as
  `RingHom.Locally RingHom.IsStandardOpenImmersion`, which
  `RingHom.isLocalIso_iff_locally` identifies with `RingHom.IsLocalIso`.

## Main results

* `RingHom.IsLocalIso.stableUnderComposition`, `RingHom.IsLocalIso.respectsIso`,
  `RingHom.IsLocalIso.isStableUnderBaseChange`, `RingHom.IsLocalIso.containsIdentities`:
  the permanence properties of local isomorphisms, in the `RingHom` spelling.
* `RingHom.IsLocalIso.finitePresentation`: a local isomorphism is of finite presentation.
* `CommRingCat.localIso_le_isFinitelyPresentable`: a local isomorphism is a finitely presentable
  morphism of `CommRingCat`, which is the size hypothesis every result about
  `CategoryTheory.MorphismProperty.ind` needs.
* `CommRingCat.localIso_ind_iff_exists`: the factorization criterion for ind-local-isomorphisms,
  the ind-Zariski analogue of Lemma 07C3.
* `AlgebraicGeometry.ProEtale.isIndZariski_of_isLocalIso`: a local isomorphism is ind-Zariski,
  with the source, the target and the index category in independent universes.
* `AlgebraicGeometry.ProEtale.isIndZariski_iff_ind_algebraMap`: for a base and an algebra in one
  universe, being ind-Zariski is being an ind-local-isomorphism ring map.
* `AlgebraicGeometry.ProEtale.isIndZariski_comp_of_isLocalIso`: the case of Tag 096Q in which the
  first of the two maps is a local isomorphism. Unconditional.
* `AlgebraicGeometry.ProEtale.isIndZariski_of_isPushout`: an ind-Zariski algebra stays ind-Zariski
  after cobase change. Unconditional, and in particular independent of Tag 096Q.
* `AlgebraicGeometry.ProEtale.isIndZariski_comp_of_preIndSpreads`: the composition of two
  ind-Zariski maps is ind-Zariski, *given* that local isomorphisms spread out in a filtered
  colimit of base rings (`CategoryTheory.MorphismProperty.PreIndSpreads`).

## Implementation notes

Tag 096Q, the composition-stability of ind-Zariski maps, is **not** proved here. What is proved
is that it follows from exactly one missing input, namely
`CategoryTheory.MorphismProperty.PreIndSpreads.{u} CommRingCat.localIso.{u}`:

> if `B = colim Bᵢ` is a filtered colimit of rings and `B → E` is a local isomorphism, then
> there is an index `i`, a local isomorphism `Bᵢ → E'`, and a pushout square identifying `E`
> with the base change of `E'` along `Bᵢ → B`.

That is item (9) of Stacks Lemma 00U2 for local isomorphisms rather than for étale maps; the
étale case is `StacksFrontier.RingTheory.Etale.FilteredColimit.Basic`'s `exists_isPushout_etale`,
deduced from `Algebra.Etale.exists_subalgebra_fg`, and Mathlib has no analogue of the latter for
`Algebra.IsLocalIso`. Being a local isomorphism is a Zariski-local condition on the target rather
than a condition on a presentation, so the finite data that has to descend is a finite family of
standard open immersions together with their overlaps, i.e. the descent of a gluing datum.

One further remark on the scope of what is proved here.
`isIndZariski_comp_of_preIndSpreads` has its base, its intermediate ring and its target in a
  single universe, whereas `IsIndZariski` is stated for independent universes. The obstruction
  is that `IsIndZariski.{u, v, t}` puts its stages in `CommAlgCat.{max u v}`, and Mathlib
  provides `HasColimits`, `CategoryTheory.commAlgCatEquivUnder` and hence the presentability API
  for `CommAlgCat.{s} A` only when `s` is the universe of `A` itself. The universe-free statement
  therefore needs the transport that `StacksFrontier.RingTheory.Etale.IndEtaleUniverse` performs for
  ind-étale algebras: lift all three rings into a common universe with `ULift`, apply the
  single-universe statement, and come back, using that a local isomorphism, being of finite
  presentation, has a model in the universe of its base.

## References

* [Stacks Project, Tag 096N](https://stacks.math.columbia.edu/tag/096N)
* [Stacks Project, Tag 096Q](https://stacks.math.columbia.edu/tag/096Q)
* [Stacks Project, Tag 00U2](https://stacks.math.columbia.edu/tag/00U2)
* [Stacks Project, Tag 0BUF](https://stacks.math.columbia.edu/tag/0BUF)
-/

@[expose] public section

universe u v t

open CategoryTheory Limits TensorProduct

namespace RingHom

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)

/-- A ring map is a **local isomorphism** if, source locally in the geometric sense, it is a
standard open immersion. This is `Algebra.IsLocalIso` for the algebra structure that the ring
map itself induces. -/
def IsLocalIso : Prop :=
  letI := f.toAlgebra
  Algebra.IsLocalIso R S

/-- For an algebra, the structure map is a local isomorphism exactly when the algebra is. -/
lemma isLocalIso_algebraMap [Algebra R S] :
    (algebraMap R S).IsLocalIso ↔ Algebra.IsLocalIso R S := by
  rw [IsLocalIso, toAlgebra_algebraMap]

/-- Being a local isomorphism is being Zariski-locally a standard open immersion. This
identifies the `Algebra.IsLocalIso` spelling used in this file with the one that
`StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski` uses to define `CommRingCat.localIso`. -/
lemma isLocalIso_iff_locally {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    f.IsLocalIso ↔ RingHom.Locally RingHom.IsStandardOpenImmersion f := by
  algebraize [f]
  rw [← f.algebraMap_toAlgebra, isLocalIso_algebraMap, Algebra.isLocalIso_iff_locally]

end RingHom

namespace RingHom.IsLocalIso

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {f : R →+* S} {g : S →+* T}

/-- A ring map that is a local isomorphism makes its target a local isomorphism as an algebra
over its source, for the induced algebra structure. -/
lemma toAlgebra (hf : f.IsLocalIso) :
    @Algebra.IsLocalIso R S _ _ f.toAlgebra :=
  let := f.toAlgebra; hf

/-- A bijective ring map is a local isomorphism. -/
lemma of_bijective (hf : Function.Bijective f) : f.IsLocalIso :=
  let := f.toAlgebra
  let : Algebra.IsStandardOpenImmersion R S :=
    ⟨1, IsLocalization.away_of_isUnit_of_bijective _ isUnit_one hf⟩
  (inferInstance : Algebra.IsLocalIso R S)

/-- The identity map of a ring is a local isomorphism. -/
lemma id (R : Type*) [CommRing R] : (RingHom.id R).IsLocalIso :=
  of_bijective Function.bijective_id

/-- The composition of two local isomorphisms is a local isomorphism. -/
lemma comp (hf : f.IsLocalIso) (hg : g.IsLocalIso) : (g.comp f).IsLocalIso := by
  algebraize [f, g, g.comp f]
  have : Algebra.IsLocalIso R S := hf
  have : Algebra.IsLocalIso S T := hg
  exact .trans _ S _

/-- Local isomorphisms contain the identities. -/
theorem containsIdentities : ContainsIdentities.{u} IsLocalIso := id

/-- Local isomorphisms are stable under composition. -/
theorem stableUnderComposition : StableUnderComposition.{u} IsLocalIso := @comp

/-- Being a local isomorphism only depends on a ring map up to isomorphism of source and
target. -/
theorem respectsIso : RespectsIso.{u} IsLocalIso :=
  stableUnderComposition.respectsIso fun e ↦ of_bijective e.bijective

/-- Local isomorphisms are stable under base change. -/
theorem isStableUnderBaseChange : IsStableUnderBaseChange.{u} IsLocalIso := by
  refine .mk respectsIso ?_
  introv h
  rw [isLocalIso_algebraMap] at h ⊢
  infer_instance

/-- A local isomorphism is of finite presentation: its target is covered by finitely many
standard open immersions, each of which is a localization away from one element and hence of
finite presentation, and finite presentation is Zariski local on the target. -/
theorem finitePresentation (hf : f.IsLocalIso) : f.FinitePresentation := by
  algebraize [f]
  have : Algebra.IsLocalIso R S := hf
  have hfp : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_span_eq_top_target _
      (Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top R S) fun g hg => by
        obtain ⟨r, hr⟩ := (Algebra.isStandardOpenImmersion_iff R (Localization.Away g)).mp hg
        exact IsLocalization.Away.finitePresentation r
  exact RingHom.finitePresentation_algebraMap.mpr hfp

end RingHom.IsLocalIso

namespace CommRingCat

-- `CommRingCat.localIso`, the morphism property of local isomorphisms of commutative rings, its
-- unfolding `CommRingCat.localIso_iff`, and its `RespectsIso`, `IsStableUnderComposition` and
-- `IsStableUnderCobaseChange` instances are defined in
-- `StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski`. That file states the property as
-- `RingHom.Locally RingHom.IsStandardOpenImmersion`, which `RingHom.isLocalIso_iff_locally`
-- identifies with `RingHom.IsLocalIso`.

/-- `CommRingCat.localIso` on a bundled ring map is `RingHom.IsLocalIso` on the ring map. -/
lemma localIso_ofHom_iff {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    localIso (ofHom f) ↔ f.IsLocalIso :=
  (localIso_iff _).trans (RingHom.isLocalIso_iff_locally f).symm

/-- Identity morphisms of commutative rings are local isomorphisms. -/
instance : (localIso.{u}).ContainsIdentities where
  id_mem R := (localIso_iff _).mpr ((RingHom.isLocalIso_iff_locally _).mp
    (RingHom.IsLocalIso.id R))

/-- Precomposing a local isomorphism with a local isomorphism gives a local isomorphism. -/
instance : (localIso.{u}).RespectsLeft localIso.{u} where
  precomp _ hi _ hf := MorphismProperty.comp_mem _ _ _ hi hf

/-- **The factorization criterion for ind-local-isomorphisms.** A ring map `f : X ⟶ Y` is a
filtered colimit of local isomorphisms exactly when every factorization of `f` through a
finitely presentable `X`-algebra `Z` can be pushed further, through an `X`-algebra `W` that is a
local isomorphism over `X`.

This is Mathlib's `CategoryTheory.MorphismProperty.ind_iff_exists`, which needs the finite
accessibility of the categories of algebras supplied above; it is the ind-Zariski analogue of
Lemma 07C3 and the shape in which spreading-out arguments are usually run. -/
theorem localIso_ind_iff_exists {X Y : CommRingCat.{u}} (f : X ⟶ Y) :
    MorphismProperty.ind.{u} localIso.{u} f ↔
      ∀ {Z : CommRingCat.{u}} (p : X ⟶ Z) (g : Z ⟶ Y),
        MorphismProperty.isFinitelyPresentable.{u} _ p → p ≫ g = f →
        ∃ (W : CommRingCat.{u}) (u : Z ⟶ W) (v : W ⟶ Y), u ≫ v = g ∧ localIso.{u} (p ≫ u) :=
  MorphismProperty.ind_iff_exists localIso_le_isFinitelyPresentable f

/-- **The composition of two ind-local-isomorphisms is an ind-local-isomorphism**, given that
local isomorphisms spread out in a filtered colimit of base rings.

The hypothesis `CategoryTheory.MorphismProperty.PreIndSpreads` is item (9) of Lemma `00U2` for
local isomorphisms: a local isomorphism out of a filtered colimit `colim Bᵢ` is the base change
of a local isomorphism out of some `Bᵢ`. It is the one input this file does not provide. -/
theorem localIso_ind_comp [MorphismProperty.PreIndSpreads.{u} localIso.{u}]
    {X Y Z : CommRingCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : MorphismProperty.ind.{u} localIso.{u} f)
    (hg : MorphismProperty.ind.{u} localIso.{u} g) :
    MorphismProperty.ind.{u} localIso.{u} (f ≫ g) :=
  (MorphismProperty.IsStableUnderComposition.ind_of_preIndSpreads
    localIso_le_isFinitelyPresentable).comp_mem _ _ hf hg

end CommRingCat

namespace AlgebraicGeometry.ProEtale

/-- **A local isomorphism is ind-Zariski.** The source, the target and the index category of the
presentation lie in independent universes; the presentation is the one-object diagram. -/
theorem isIndZariski_of_isLocalIso (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsLocalIso A B] : IsIndZariski.{u, v, t} A B :=
  have e : B ≃ₐ[A] ULift.{u} B := (ULift.algEquiv (R := A) (A := B)).symm
  ObjectProperty.le_ind _ _ (Algebra.IsLocalIso.of_algEquiv e)

/-- **Ind-Zariskiness of an algebra is ind-local-isomorphy of its structure map.** For a base and
an algebra in a single universe, being a filtered colimit of local isomorphisms, in the spelling
`AlgebraicGeometry.ProEtale.IsIndZariski` of Definition 096N, is being an ind-local-isomorphism
ring map for the morphism property `CommRingCat.localIso`. -/
theorem isIndZariski_iff_ind_algebraMap {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    IsIndZariski.{u, u, u} A B ↔
      MorphismProperty.ind.{u} CommRingCat.localIso.{u}
        (CommRingCat.ofHom (algebraMap A B)) := by
  have hinv : (fun C : CommAlgCat.{u} A ↦ Algebra.IsLocalIso A C) =
      (CommRingCat.localIso.{u}).underObj.inverseImage
        (commAlgCatEquivUnder (CommRingCat.of A)).functor := by
    ext S
    show Algebra.IsLocalIso A S ↔ CommRingCat.localIso (CommRingCat.ofHom (algebraMap A S))
    rw [CommRingCat.localIso_ofHom_iff, RingHom.isLocalIso_algebraMap]
  rw [show IsIndZariski.{u, u, u} A B ↔
      ObjectProperty.ind.{u} (fun C : CommAlgCat.{u} A ↦ Algebra.IsLocalIso A C)
        (CommAlgCat.of A B) from
    (ObjectProperty.ind.{u} (fun C : CommAlgCat.{u} A ↦
      Algebra.IsLocalIso A C)).prop_iff_of_iso
      (CommAlgCat.isoMk (ULift.algEquiv (R := A) (A := B))),
    MorphismProperty.ind_iff_ind_underMk,
    ← ObjectProperty.ind_iff_of_equivalence (CommRingCat.localIso.{u}).underObj
      (commAlgCatEquivUnder (CommRingCat.of A))
      (Under.mk (CommRingCat.ofHom (algebraMap A B))), ← hinv]
  exact (ObjectProperty.ind.{u} (fun C : CommAlgCat.{u} A ↦
    Algebra.IsLocalIso A C)).prop_iff_of_iso
    ((commAlgCatEquivUnder (CommRingCat.of A)).unitIso.app (CommAlgCat.of A B))

/-- The structure map of a tower `A → B → C` is the composite of the two structure maps. -/
private theorem ofHom_algebraMap_comp (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    CommRingCat.ofHom (algebraMap A C) =
      CommRingCat.ofHom (algebraMap A B) ≫ CommRingCat.ofHom (algebraMap B C) := by
  rw [IsScalarTower.algebraMap_eq A B C, CommRingCat.ofHom_comp]

/-- **An ind-Zariski map precomposed with a local isomorphism is ind-Zariski.** This is the case
of Tag 096Q in which the first of the two maps is a local isomorphism rather than merely
ind-Zariski; no spreading out is needed, because the presentation of the target as a filtered
colimit is unchanged and only its structure maps are precomposed. -/
theorem isIndZariski_comp_of_isLocalIso (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra.IsLocalIso A B] (hBC : IsIndZariski.{u, u, u} B C) :
    IsIndZariski.{u, u, u} A C := by
  rw [isIndZariski_iff_ind_algebraMap] at hBC ⊢
  rw [ofHom_algebraMap_comp A B C]
  exact MorphismProperty.RespectsLeft.precomp (Q := CommRingCat.localIso.{u})
    (CommRingCat.ofHom (algebraMap A B))
    ((CommRingCat.localIso_ofHom_iff _).mpr (RingHom.isLocalIso_algebraMap.mpr ‹_›)) _ hBC

/-- **An ind-Zariski algebra stays ind-Zariski after cobase change.** Let `A → B` and `A → A'` be
ring maps and let `B'` be a pushout of `B` and `A'` over `A`, that is, `B' = B ⊗[A] A'`. If `A'`
is ind-Zariski over `A`, then `B'` is ind-Zariski over `B`.

This needs no spreading out either: a presentation of `A'` by local isomorphisms over `A`
pushes out to a presentation of `B'` by local isomorphisms over `B`, because local isomorphisms
are stable under base change and the pushout functor preserves colimits. In particular the
cobase change of an ind-Zariski map is independent of Tag 096Q. -/
theorem isIndZariski_of_isPushout (A B A' B' : Type u) [CommRing A] [CommRing B] [CommRing A']
    [CommRing B'] [Algebra A B] [Algebra A A'] [Algebra A B'] [Algebra B B'] [Algebra A' B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [Algebra.IsPushout A B A' B']
    (h : IsIndZariski.{u, u, u} A A') : IsIndZariski.{u, u, u} B B' := by
  rw [isIndZariski_iff_ind_algebraMap] at h ⊢
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
    (CommRingCat.isPushout_of_isPushout A B A' B') h

/-- **The composition of two ind-Zariski maps is ind-Zariski**, for a base, an intermediate ring
and a target in a single universe, and given that local isomorphisms spread out in a filtered
colimit of base rings.

This is Tag 096Q in the single-universe case, reduced to
`CategoryTheory.MorphismProperty.PreIndSpreads.{u} CommRingCat.localIso.{u}`; see the module
docstring for what that hypothesis says and for why the universe-free statement needs a further
transport. It carries no Stacks tag, because the hypothesis is not discharged. -/
theorem isIndZariski_comp_of_preIndSpreads
    [MorphismProperty.PreIndSpreads.{u} CommRingCat.localIso.{u}]
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAB : IsIndZariski.{u, u, u} A B) (hBC : IsIndZariski.{u, u, u} B C) :
    IsIndZariski.{u, u, u} A C := by
  rw [isIndZariski_iff_ind_algebraMap] at hAB hBC ⊢
  rw [ofHom_algebraMap_comp A B C]
  exact CommRingCat.localIso_ind_comp _ _ hAB hBC

end AlgebraicGeometry.ProEtale

end
