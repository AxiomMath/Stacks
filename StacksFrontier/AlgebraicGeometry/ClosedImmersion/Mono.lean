module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Topology.Category.TopCat.EpiMono
public import Mathlib.Topology.Sheaves.Functors

/-!
# A closed immersion of locally ringed spaces is a monomorphism

A closed immersion of locally ringed spaces `i : Z ⟶ X` is a morphism whose underlying map of
spaces is a closed embedding and whose comparison map on structure sheaves is surjective in the
sheaf-theoretic sense. This file shows that such a morphism is a monomorphism, which is the
uniqueness half of the universal property of a closed subspace.

## Main results

* `eq_of_isLocallySurjective_comp_eq`: a locally surjective morphism of presheaves can be
  cancelled on the left against morphisms into a separated presheaf.
* `pushforward_map_injective`: pushing forward presheaves along an inducing map is faithful.
* `presheafedSpaceHom_eq_of_comp_eq`: the key computation, at the level of presheafed spaces: a
  morphism with closed-embedding base and locally surjective sheaf comparison can be cancelled
  on the right against morphisms out of a space whose presheaf is a sheaf.
* `mono_of_isClosedEmbedding_of_isLocallySurjective`: a closed immersion of locally ringed
  spaces is a monomorphism.
* `subsingleton_factorization`: the resulting uniqueness statement, that a morphism `f : Y ⟶ X`
  admits at most one factorization through a monomorphism `i : Z ⟶ X`.

## Implementation notes

Surjectivity of the structure-sheaf comparison map is taken as an explicit hypothesis, in the
form `CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.toTopCat) i.c`,
i.e. for every open `V` of `X` the sieve of opens of `V` on which a given section of
`i.base _* Z.presheaf` is in the image of `i.c` is a covering sieve. The equivalent elementary
statement, that every section is locally in the image, is Mathlib's
`TopCat.Presheaf.isLocallySurjective_iff`, whose left-hand side is this condition by definition.
So a caller holding the section-level statement can feed it in through that iff.

Monomorphy cannot be established on the underlying presheafed space, since cancellation there
would have to hold against test objects carrying an arbitrary presheaf, and the argument needs
the test object's presheaf to be a sheaf. The reduction therefore stops at
`presheafedSpaceHom_eq_of_comp_eq`, which carries the sheaf condition on the test object as a
hypothesis; `LocallyRingedSpace.Hom.ext'` then transfers the conclusion back, the sheaf
condition being available on every locally ringed space.

The cancellation of `i.c` is where local surjectivity is used: two morphisms out of
`i.base _* Z.presheaf` agreeing after composition with `i.c` agree on a covering sieve of every
section, hence agree, because the target is separated — it is a pushforward of a sheaf, by
`TopCat.Sheaf.pushforward_sheaf_of_sheaf`. The closed embedding enters twice: through
injectivity, to cancel `i.base` in `TopCat`, and through the induced topology, which makes
pushforward along `i.base` faithful since every open of `Z` is the preimage of an open of `X`.

## References

* [Stacks Project, Tag 01HP](https://stacks.math.columbia.edu/tag/01HP)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.ClosedImmersion

section Presheaf

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Type*} [Category* A]
  {FA : A → A → Type*} {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
  [ConcreteCategory A FA]

/-- A locally surjective morphism of presheaves `f : F ⟶ G` can be cancelled on the left: two
morphisms `a b : G ⟶ H` into a `J`-separated presheaf `H` with `f ≫ a = f ≫ b` are equal. -/
theorem eq_of_isLocallySurjective_comp_eq {F G H : Cᵒᵖ ⥤ A} {f : F ⟶ G}
    (hf : Presheaf.IsLocallySurjective J f) (hH : Presheaf.IsSeparated J H) {a b : G ⟶ H}
    (hab : f ≫ a = f ≫ b) : a = b := by
  ext U
  refine DFunLike.ext _ _ fun t => ?_
  refine hH U.unop (Presheaf.imageSieve f t) (hf.imageSieve_mem t) _ _ fun V g hg => ?_
  have key : (f ≫ a).app (op V) (Presheaf.localPreimage f t g hg)
      = (f ≫ b).app (op V) (Presheaf.localPreimage f t g hg) := by rw [hab]
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Presheaf.app_localPreimage] at key
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← a.naturality g.op,
    ← b.naturality g.op, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, key]

end Presheaf

section Pushforward

variable {C : Type*} [Category* C]

/-- Pushing forward presheaves along an inducing continuous map is faithful: every open of the
source is the preimage of an open of the target, so a morphism of presheaves is determined by
its components on preimages. -/
theorem pushforward_map_injective {S T : TopCat} {f : S ⟶ T} (hf : Topology.IsInducing f)
    {ℱ 𝒢 : S.Presheaf C} {a b : ℱ ⟶ 𝒢}
    (h : (TopCat.Presheaf.pushforward C f).map a = (TopCat.Presheaf.pushforward C f).map b) :
    a = b := by
  refine NatTrans.ext (funext fun W => ?_)
  obtain ⟨W⟩ := W
  obtain ⟨t, ht, hts⟩ := hf.isOpen_iff.1 W.isOpen
  obtain rfl : (Opens.map f).obj ⟨t, ht⟩ = W := Opens.ext hts
  simpa only [TopCat.Presheaf.pushforward_map_app'] using NatTrans.congr_app h (op ⟨t, ht⟩)

end Pushforward

/-- The computation underlying monomorphy, carried out on presheafed spaces. Let `i : Z ⟶ X` be a
morphism of presheafed spaces of commutative rings whose base map is a closed embedding and whose
sheaf comparison map `i.c` is locally surjective. Then `i` can be cancelled on the right against
morphisms out of any presheafed space whose presheaf is a sheaf. -/
theorem presheafedSpaceHom_eq_of_comp_eq {Y Z X : PresheafedSpace.{u} CommRingCat.{u}}
    {i : Z ⟶ X} (hbase : Topology.IsClosedEmbedding i.base)
    (hsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) i.c)
    (hY : Y.presheaf.IsSheaf) {g₁ g₂ : Y ⟶ Z} (h : g₁ ≫ i = g₂ ≫ i) : g₁ = g₂ := by
  have : Mono i.base := (TopCat.mono_iff_injective _).2 hbase.injective
  obtain ⟨b₁, c₁⟩ := g₁
  obtain ⟨b₂, c₂⟩ := g₂
  obtain rfl : b₁ = b₂ := (cancel_mono i.base).1 (congrArg PresheafedSpace.Hom.base h)
  have key : (⟨b₁ ≫ i.base, i.c ≫ (TopCat.Presheaf.pushforward _ i.base).map c₁⟩ :
      PresheafedSpace.Hom Y X)
      = ⟨b₁ ≫ i.base, i.c ≫ (TopCat.Presheaf.pushforward _ i.base).map c₂⟩ := h
  injection key with _ hcomp
  have hcc : c₁ = c₂ :=
    pushforward_map_injective hbase.isEmbedding.isInducing
      (eq_of_isLocallySurjective_comp_eq hsurj
        (TopCat.Sheaf.pushforward_sheaf_of_sheaf i.base
          (TopCat.Sheaf.pushforward_sheaf_of_sheaf b₁ hY)).isSeparated hcomp)
  subst hcc
  rfl

/-- **A closed immersion of locally ringed spaces is a monomorphism.** Precisely, a morphism
`i : Z ⟶ X` of locally ringed spaces whose base map is a closed embedding and whose structure
sheaf comparison map `i.c` is locally surjective for the topology of opens of `X` is a
monomorphism. This is the uniqueness half of [Stacks Project, Tag
01HP](https://stacks.math.columbia.edu/tag/01HP). -/
theorem mono_of_isClosedEmbedding_of_isLocallySurjective {Z X : LocallyRingedSpace.{u}}
    (i : Z ⟶ X) (hbase : Topology.IsClosedEmbedding i.base)
    (hsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.toTopCat) i.c) :
    Mono i where
  right_cancellation {Y} g₁ g₂ h := by
    refine LocallyRingedSpace.Hom.ext'
      (presheafedSpaceHom_eq_of_comp_eq (i := i.toHom) hbase hsurj Y.IsSheaf ?_)
    simpa only [LocallyRingedSpace.comp_toHom] using congrArg LocallyRingedSpace.Hom.toHom h

/-- A morphism `f : Y ⟶ X` of locally ringed spaces admits at most one factorization through a
monomorphism `i : Z ⟶ X`. Combined with
`mono_of_isClosedEmbedding_of_isLocallySurjective` this is the uniqueness statement for
factorizations through a closed immersion. -/
theorem subsingleton_factorization {Y Z X : LocallyRingedSpace.{u}} (i : Z ⟶ X) [Mono i]
    (f : Y ⟶ X) : Subsingleton {g : Y ⟶ Z // g ≫ i = f} :=
  ⟨fun g₁ g₂ => Subtype.ext ((cancel_mono i).1 (g₁.2.trans g₂.2.symm))⟩

end Stacks.ClosedImmersion

end
