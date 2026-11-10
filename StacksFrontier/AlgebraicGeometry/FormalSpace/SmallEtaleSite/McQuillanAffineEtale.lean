module

public import Mathlib.CategoryTheory.Category.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.EtaleModWeakIdeal

/-!
# The affine étale site of a McQuillan affine formal algebraic space

Let `A` be a weakly admissible topological ring and let `X = Spf A` be the associated McQuillan
affine formal algebraic space.  Stacks 0DEF identifies `(X_{affine,étale})^{opp}` with the
category whose objects are the `A`-algebras `B^∧ = lim B/JB`, for `A → B` an étale ring map and
`J` ranging over the weak ideals of definition of `A`, and whose morphisms are the continuous
`A`-algebra homomorphisms.

This file builds that category.  An object is an étale ring map out of `A`; the `A`-algebra it
names is `TopologicalRing.CompletionOver` of that map, which *is* the inverse limit of the
rings `B/JB` over the weak ideals of definition `J` of `A`, with its inverse-limit topology.  A
morphism is a continuous ring homomorphism between two such completions commuting with the
canonical maps out of `A`, which is exactly a continuous `A`-algebra homomorphism.

## Main definitions

* `AlgebraicGeometry.FormalSpace.EtaleCompletion`: an étale ring map out of `A`, i.e. the datum
  naming an object `B^∧` of the category of Stacks 0DEF.
* `AlgebraicGeometry.FormalSpace.EtaleCompletion.completion`: the `A`-algebra `B^∧ = lim B/JB`
  attached to such a datum.
* `AlgebraicGeometry.FormalSpace.EtaleCompletion.Hom` and
  `AlgebraicGeometry.FormalSpace.EtaleCompletion.instCategory`: the continuous `A`-algebra
  homomorphisms between those completions, and the resulting category.
* `AlgebraicGeometry.FormalSpace.EtaleCompletion.self`: the object named by the identity of `A`.
* `AlgebraicGeometry.FormalSpace.EtaleCompletion.homOfAlgebraHom`: the morphism of the category
  induced by an `A`-algebra homomorphism of the underlying étale algebras.

## Main results

* `AlgebraicGeometry.FormalSpace.EtaleCompletion.isWeaklyAdmissible_completion`: every object of
  the category is itself a weakly admissible topological ring, so `Spf` of it makes sense.
* `AlgebraicGeometry.FormalSpace.EtaleCompletion.etale_quotientMap`: for every object and every
  weak ideal of definition `J` of `A`, the induced ring map `A/J → B^∧ / ker(B^∧ → B/JB)` of
  quotient stages is étale.  This is the ring-theoretic engine of Stacks 0AN8: it says that the
  stages of `Spf B^∧ ⟶ Spf A` are étale, which is why the objects of this category are charts of
  the affine étale site at all.
* `AlgebraicGeometry.FormalSpace.EtaleCompletion.homOfAlgebraHom_id` and
  `AlgebraicGeometry.FormalSpace.EtaleCompletion.homOfAlgebraHom_comp`: that construction is
  functorial in the étale algebra.

## Implementation notes

Stacks 0DEF is proved by combining Stacks 0DEE — the comparison of `X_{affine,étale}` with the
category of affine formal algebraic spaces representable étale over `X` — with Stacks 0AN8 —
the comparison of the latter with the present category of completions.  The first of the two
is available as an equivalence, `AlgebraicGeometry.FormalSpace.affineEtaleEquivalence` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/Affine/EtaleSiteEquivalence.lean`; so is the
second, `AlgebraicGeometry.FormalSpace.isEquivalence_etaleCompletionCharts` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/SmallEtaleSite/EtaleCompletionEquivalence.lean`,
built from the essential surjectivity of `Spf`,
`AlgebraicGeometry.FormalSpace.isEssentiallySurjectiveSpf'`; its full faithfulness, which is
Stacks 0AN0, `AlgebraicGeometry.FormalSpace.existsUnique_continuousHom_formalSpectrumMap_eq`;
and the ring-theoretic first step, reproduced here as `etale_quotientMap`.  Their composition is
`AlgebraicGeometry.FormalSpace.mcQuillanAffineEtaleEquivalence` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/SmallEtaleSite/McQuillanEtaleEquivalence.lean`, which
is where the whole of Stacks 0DEF is stated.  This file builds the algebra side of that
identification, namely the category described by the tag's items (1) and (2); it is
unconditional, where the geometric side needs a supplied big fppf site.

A morphism is required to commute with `TopologicalRing.CompletionOver.canonicalMap`, the
canonical map `A → B^∧`, rather than with an `Algebra A B^∧` instance: the completion is a
`Subring` of a product of quotients of `B`, and the canonical map is the structure map of
Stacks 0AN6, so this is the `A`-algebra structure the construction actually carries.  Carrying
it as an equation between ring homomorphisms also makes morphism equality decided by the
underlying ring homomorphism alone, which is what `Hom.ext` records.

## References

* [Stacks Project, Tag 0DEF](https://stacks.math.columbia.edu/tag/0DEF)
* [Stacks Project, Tag 0DEE](https://stacks.math.columbia.edu/tag/0DEE)
* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
-/

@[expose] public section

open CategoryTheory TopologicalRing

namespace AlgebraicGeometry.FormalSpace

universe u

variable (A : Type u) [CommRing A] [TopologicalSpace A]

/-- **Stacks 0DEF**, item (1): the datum naming an object of the category attached to a weakly
admissible topological ring `A`.  It is an étale ring map `A → B`; the `A`-algebra it names is
the completion `B^∧ = lim B/JB`, the limit being over the weak ideals of definition `J` of `A`,
see `AlgebraicGeometry.FormalSpace.EtaleCompletion.completion`. -/
@[stacks 0DEF "item (1), the objects: an `A`-algebra of the form `B^∧ = lim B/JB` for an étale \
ring map `A → B`, named here by that ring map together with its étaleness, the completion \
being `TopologicalRing.CompletionOver` of it.  The equivalence with `(X_affine,étale)^opp` is \
not constructed: it needs Stacks 0DEE as an equivalence, which this library has only as a \
comparison functor, and Stacks 0AN8 as an equivalence, which this library has only in the \
ring-theoretic form `EtaleCompletion.etale_quotientMap`"]
structure EtaleCompletion where
  /-- The étale `A`-algebra whose completion is the object. -/
  carrier : Type u
  /-- Its ring structure. -/
  [commRing : CommRing carrier]
  /-- The structure map `A → B`. -/
  str : A →+* carrier
  /-- The structure map is étale. -/
  etale : str.Etale

attribute [instance] EtaleCompletion.commRing

namespace EtaleCompletion

variable {A}

/-- The `A`-algebra `B^∧ = lim B/JB` named by an object, the limit being over the weak ideals of
definition `J` of `A`.  It carries the inverse-limit topology of Stacks 0AN6, with each `B/JB`
discrete. -/
abbrev completion (Y : EtaleCompletion A) : Type u := TopologicalRing.CompletionOver Y.str

/-- The canonical map `A → B^∧`, the `A`-algebra structure of an object. -/
abbrev structureMap (Y : EtaleCompletion A) : A →+* Y.completion :=
  TopologicalRing.CompletionOver.canonicalMap Y.str

/-- **Stacks 0DEF**, item (2): a morphism of the category, a continuous `A`-algebra
homomorphism `B₁^∧ → B₂^∧` between the completions named by two objects.  The `A`-algebra
structures are the canonical maps of Stacks 0AN6, so being an `A`-algebra homomorphism is the
displayed commuting triangle. -/
@[stacks 0DEF "item (2), the morphisms: the continuous `A`-algebra homomorphisms between the \
objects, with the `A`-algebra structure of `B^∧` given by the canonical map \
`TopologicalRing.CompletionOver.canonicalMap`.  The equivalence with `(X_affine,étale)^opp` is \
not constructed, for the reasons recorded on `EtaleCompletion`"]
structure Hom (Y Z : EtaleCompletion A) where
  /-- The underlying ring homomorphism of completions. -/
  toRingHom : Y.completion →+* Z.completion
  /-- It is continuous for the inverse-limit topologies. -/
  continuous_toRingHom : Continuous toRingHom
  /-- It is a homomorphism of `A`-algebras. -/
  comp_structureMap : toRingHom.comp Y.structureMap = Z.structureMap

/-- A morphism of the category of Stacks 0DEF is determined by its underlying ring
homomorphism: continuity and `A`-linearity are propositions. -/
@[ext]
theorem Hom.ext {Y Z : EtaleCompletion A} {g h : Hom Y Z}
    (w : g.toRingHom = h.toRingHom) : g = h := by
  obtain ⟨g₁, _, _⟩ := g
  obtain ⟨h₁, _, _⟩ := h
  obtain rfl : g₁ = h₁ := w
  rfl

/-- The category of Stacks 0DEF: the objects of item (1) and the morphisms of item (2).
Composition is composition of ring homomorphisms. -/
instance instCategory : Category.{u} (EtaleCompletion A) where
  Hom Y Z := Hom Y Z
  id Y := ⟨RingHom.id _, continuous_id, RingHom.id_comp _⟩
  comp g h :=
    ⟨h.toRingHom.comp g.toRingHom, h.continuous_toRingHom.comp g.continuous_toRingHom, by
      rw [RingHom.comp_assoc, g.comp_structureMap, h.comp_structureMap]⟩
  id_comp _ := Hom.ext (RingHom.comp_id _)
  comp_id _ := Hom.ext (RingHom.id_comp _)
  assoc _ _ _ := Hom.ext (RingHom.comp_assoc _ _ _).symm

/-- The ring homomorphism underlying the identity morphism is the identity. -/
@[simp]
theorem id_toRingHom (Y : EtaleCompletion A) : Hom.toRingHom (𝟙 Y) = RingHom.id _ := rfl

/-- The ring homomorphism underlying a composite `g ≫ h` is the composite of the underlying ring
homomorphisms of `h` and `g`. -/
@[simp]
theorem comp_toRingHom {Y Z W : EtaleCompletion A} (g : Y ⟶ Z) (h : Z ⟶ W) :
    (g ≫ h).toRingHom = h.toRingHom.comp g.toRingHom := rfl

/-! ### The category is not degenerate -/

variable (A) in
/-- The object named by the identity of `A`, whose completion is `A^∧ = lim A/J`. -/
def self : EtaleCompletion A where
  carrier := A
  str := RingHom.id A
  etale := RingHom.Etale.containsIdentities A

/-- The category `EtaleCompletion A` has an object, namely `self A`. -/
instance : Nonempty (EtaleCompletion A) := ⟨self A⟩

section AlgebraHom

variable {Y Z W : EtaleCompletion A}

/-- An `A`-algebra homomorphism of the underlying étale algebras carries a weak ideal of
definition of `A` extended to the source into the same ideal extended to the target. -/
theorem extendedIdeal_le_comap {φ : Y.carrier →+* Z.carrier} (hφ : φ.comp Y.str = Z.str)
    (J : WeakIdealOfDefinitionIndex A) :
    extendedIdeal Y.str J ≤ (extendedIdeal Z.str J).comap φ := by
  refine Ideal.map_le_iff_le_comap.mpr ?_
  rw [Ideal.comap_comap, hφ]
  exact Ideal.le_comap_map

/-- The map of stages `B₁/JB₁ → B₂/JB₂` induced by an `A`-algebra homomorphism of the
underlying étale algebras. -/
abbrev stageMap (φ : Y.carrier →+* Z.carrier) (hφ : φ.comp Y.str = Z.str)
    (J : WeakIdealOfDefinitionIndex A) :
    Y.carrier ⧸ extendedIdeal Y.str J →+* Z.carrier ⧸ extendedIdeal Z.str J :=
  Ideal.quotientMap (extendedIdeal Z.str J) φ (extendedIdeal_le_comap hφ J)

/-- The stage maps are compatible with the transition maps of the two inverse systems. -/
theorem stageMap_transitionMap {φ : Y.carrier →+* Z.carrier} (hφ : φ.comp Y.str = Z.str)
    {J K : WeakIdealOfDefinitionIndex A} (h : (J.1 : Ideal A) ≤ K.1)
    (x : Y.carrier ⧸ extendedIdeal Y.str J) :
    transitionMap Z.str h (stageMap φ hφ J x)
      = stageMap φ hφ K (transitionMap Y.str h x) := by
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective x
  rw [← hy, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
    Ideal.quotientMap_mk]

/-- The continuous `A`-algebra homomorphism `B₁^∧ → B₂^∧` of completions induced by an
`A`-algebra homomorphism `B₁ → B₂` of the underlying étale algebras: on the stage attached to
a weak ideal of definition `J` of `A` it is the induced map `B₁/JB₁ → B₂/JB₂`. -/
def mapOfAlgebraHom (φ : Y.carrier →+* Z.carrier) (hφ : φ.comp Y.str = Z.str) :
    Y.completion →+* Z.completion where
  toFun x := ⟨fun J ↦ stageMap φ hφ J (x.1 J), fun J K h ↦ by
    rw [stageMap_transitionMap hφ h (x.1 J)]
    exact congrArg (stageMap φ hφ K) (x.2 J K h)⟩
  map_one' := Subtype.ext (funext fun J ↦ map_one (stageMap φ hφ J))
  map_mul' x y := Subtype.ext (funext fun J ↦ map_mul (stageMap φ hφ J) (x.1 J) (y.1 J))
  map_zero' := Subtype.ext (funext fun J ↦ map_zero (stageMap φ hφ J))
  map_add' x y := Subtype.ext (funext fun J ↦ map_add (stageMap φ hφ J) (x.1 J) (y.1 J))

/-- The induced map of completions is continuous: each stage of the source is open in it and
each stage of the target is discrete. -/
theorem continuous_mapOfAlgebraHom (φ : Y.carrier →+* Z.carrier) (hφ : φ.comp Y.str = Z.str) :
    Continuous (mapOfAlgebraHom φ hφ) := by
  let (J : WeakIdealOfDefinitionIndex A) :
      TopologicalSpace (Y.carrier ⧸ extendedIdeal Y.str J) := ⊥
  let (J : WeakIdealOfDefinitionIndex A) :
      DiscreteTopology (Y.carrier ⧸ extendedIdeal Y.str J) := discreteTopology_bot _
  let (J : WeakIdealOfDefinitionIndex A) :
      TopologicalSpace (Z.carrier ⧸ extendedIdeal Z.str J) := ⊥
  exact continuous_induced_rng.mpr <| continuous_pi fun J ↦
    continuous_of_discreteTopology.comp ((continuous_apply J).comp continuous_subtype_val)

/-- The induced map of completions is a homomorphism of `A`-algebras. -/
theorem mapOfAlgebraHom_comp_structureMap (φ : Y.carrier →+* Z.carrier)
    (hφ : φ.comp Y.str = Z.str) :
    (mapOfAlgebraHom φ hφ).comp Y.structureMap = Z.structureMap := by
  refine RingHom.ext fun a ↦ Subtype.ext (funext fun J ↦ ?_)
  change stageMap φ hφ J (Ideal.Quotient.mk (extendedIdeal Y.str J) (Y.str a))
    = Ideal.Quotient.mk (extendedIdeal Z.str J) (Z.str a)
  rw [Ideal.quotientMap_mk, show φ (Y.str a) = Z.str a from RingHom.congr_fun hφ a]

/-- **Stacks 0DEF**, item (2), realized: the morphism of the category induced by an
`A`-algebra homomorphism of the underlying étale algebras.  So the Hom-sets of this category
are populated by more than the identities. -/
def homOfAlgebraHom (φ : Y.carrier →+* Z.carrier) (hφ : φ.comp Y.str = Z.str) : Y ⟶ Z where
  toRingHom := mapOfAlgebraHom φ hφ
  continuous_toRingHom := continuous_mapOfAlgebraHom φ hφ
  comp_structureMap := mapOfAlgebraHom_comp_structureMap φ hφ

/-- Two morphisms agree if their stages agree on every element of `B₁/JB₁` hit by a point of the
completion. -/
private theorem hom_ext_of_stage {g h : Y ⟶ Z}
    (H : ∀ (J : WeakIdealOfDefinitionIndex A) (x : Y.completion) (y : Y.carrier),
      Ideal.Quotient.mk (extendedIdeal Y.str J) y = x.1 J →
        (g.toRingHom x).1 J = (h.toRingHom x).1 J) : g = h :=
  Hom.ext (RingHom.ext fun x ↦ Subtype.ext (funext fun J ↦ by
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (x.1 J)
    exact H J x y hy))

/-- The identity of the underlying étale algebra induces the identity morphism. -/
theorem homOfAlgebraHom_id (Y : EtaleCompletion A) :
    homOfAlgebraHom (RingHom.id Y.carrier) (RingHom.id_comp Y.str) = 𝟙 Y := by
  refine hom_ext_of_stage fun J x y hy ↦ ?_
  change stageMap (RingHom.id Y.carrier) (RingHom.id_comp Y.str) J (x.1 J) = x.1 J
  rw [← hy, Ideal.quotientMap_mk, RingHom.id_apply]

/-- The construction is functorial in the underlying étale algebra. -/
theorem homOfAlgebraHom_comp (φ : Y.carrier →+* Z.carrier) (hφ : φ.comp Y.str = Z.str)
    (ψ : Z.carrier →+* W.carrier) (hψ : ψ.comp Z.str = W.str)
    (hψφ : (ψ.comp φ).comp Y.str = W.str) :
    homOfAlgebraHom (ψ.comp φ) hψφ = homOfAlgebraHom φ hφ ≫ homOfAlgebraHom ψ hψ := by
  refine hom_ext_of_stage fun J x y hy ↦ ?_
  change stageMap (ψ.comp φ) hψφ J (x.1 J)
    = stageMap ψ hψ J (stageMap φ hφ J (x.1 J))
  rw [← hy, Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.quotientMap_mk,
    RingHom.comp_apply]

end AlgebraHom

/-! ### Weak admissibility of the objects -/

/-- Every object of the category of Stacks 0DEF is itself a weakly admissible topological ring,
so that `Spf` of it is again a McQuillan affine formal algebraic space.  This is Stacks 0AN6 for
the completion of an étale algebra. -/
theorem isWeaklyAdmissible_completion [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (Y : EtaleCompletion A) :
    TopologicalRing.IsWeaklyAdmissible Y.completion :=
  TopologicalRing.completionOver_isWeaklyAdmissible Y.str hA

/-! ### The étale quotient stages of an object -/

/-- **Stacks 0AN8**, the ring-theoretic engine behind Stacks 0DEF.  For an object `B^∧` of the
category and a weak ideal of definition `J` of `A`, the map of quotient stages
`A/J → B^∧ / ker(B^∧ → B/JB)` is étale.  These stage maps are the morphisms of affine schemes
whose colimit is `Spf B^∧ ⟶ Spf A`, so this is what makes an object of this category a chart of
the affine étale site of `Spf A`. -/
theorem etale_quotientMap (Y : EtaleCompletion A)
    (J : TopologicalRing.WeakIdealOfDefinitionIndex A) :
    (Ideal.quotientMap (RingHom.ker (TopologicalRing.CompletionOver.projection Y.str J))
      Y.structureMap
      (TopologicalRing.CompletionOver.le_comap_ker_projection Y.str J)).Etale :=
  TopologicalRing.CompletionOver.etale_quotientMap_canonicalMap Y.etale J

end EtaleCompletion

end AlgebraicGeometry.FormalSpace

end
