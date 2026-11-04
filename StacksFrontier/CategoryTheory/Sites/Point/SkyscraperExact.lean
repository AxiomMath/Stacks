module

public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward
public import StacksFrontier.CategoryTheory.Sites.Point.SkyscraperStalkSplitting
import StacksCore.Tactic.StacksAttribute

/-!
# The skyscraper functor on abelian groups is exact

Let `p` be a point of the topos of sheaves on a site `(C, J)`. Its direct image
`p_* : Set ⥤ Sh(C)` carries the abelian group structure of an abelian group `A` along, giving
a functor `p_* : Ab ⥤ Ab(C)` to the category of sheaves of abelian groups, and this functor is
exact.

Left exactness is formal: on abelian group objects `p_*` is still a right adjoint, the right
adjoint of the stalk functor `p^{-1}`, so it preserves all limits. Right exactness is where the
point is used: every epimorphism of sets is split, so `p_*` of sheaves of sets preserves
epimorphisms, and an epimorphism of abelian sheaves is detected on the underlying sheaves of
sets through local surjectivity. A functor between abelian categories which preserves
epimorphisms and kernels preserves homology, hence finite colimits.

## Main definitions

* `Stacks.Topos.Skyscraper.skyscraperAb`: the functor `p_* : Ab ⥤ Ab(C)`.
* `Stacks.Topos.Skyscraper.stalkAb`: the functor `p^{-1} : Ab(C) ⥤ Ab` on abelian groups.
* `Stacks.Topos.Skyscraper.stalkAbAdjSkyscraperAb`: the adjunction `p^{-1} ⊣ p_*` on abelian
  groups.

## Main results

* `Stacks.Topos.Skyscraper.skyscraperAb_exact`: `p_* : Ab ⥤ Ab(C)` is exact.

## Implementation notes

An abelian sheaf is the same thing as a commutative group object in sheaves of sets
(`CategoryTheory.Sites.AbelianSheaf.equivalence`) and an abelian group is the same thing as a
commutative group object in sets (`commGrpAddEquivalence`). The functor `p_*` on abelian groups
is obtained by transporting `Functor.mapCommGrp` of the direct image through those two
equivalences; this is the same recipe as `CategoryTheory.Sites.abelianInverseImage` for the
inverse image, and the adjunction is the corresponding composite of adjunctions, so the stalk
functor on abelian groups is literally its left adjoint rather than merely an abstract one.

`skyscraperAb_forgetIso` identifies the underlying sheaf of sets of `p_*A` with `p_*` of the
underlying set of `A`; the two agree definitionally, as for the inverse image.

The abelian structure on `Sh(C, J)`-valued abelian sheaves needs sheafification of abelian
presheaves, which for a general site is not automatic, so `HasSheafify J AddCommGrpCat` is
carried as a hypothesis of the exactness statement: without it the target category is not
abelian and exactness is not a statement about homology at all. Left exactness needs no such
hypothesis and is stated separately.

## References

* [Stacks Project, Tag 05V7](https://stacks.math.columbia.edu/tag/05V7)
* [Stacks Project, Tag 05UY](https://stacks.math.columbia.edu/tag/05UY)
-/

@[expose] public section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

namespace Stacks.Topos.Skyscraper

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sites

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (p : PointOfTopos.{w, v, u} J)

/-- The inverse image functor of a point of a topos preserves finite limits. -/
noncomputable local instance preservesFiniteLimitsInverseImageExact :
    PreservesFiniteLimits p.inverseImage :=
  p.preservesFiniteLimits

/-- The braided monoidal structure on the inverse image functor of a point of a topos, for the
cartesian monoidal structures. -/
noncomputable local instance inverseImageBraidedExact : p.inverseImage.Braided :=
  .ofChosenFiniteProducts _

/-- The direct image functor of a point of a topos preserves finite limits. -/
noncomputable local instance preservesFiniteLimitsPushforwardExact :
    PreservesFiniteLimits p.pushforward :=
  p.preservesFiniteLimits_pushforward

/-- The braided monoidal structure on the direct image functor of a point of a topos, for the
cartesian monoidal structures. -/
noncomputable local instance pushforwardBraidedExact : p.pushforward.Braided :=
  .ofChosenFiniteProducts _

/-- The direct image `p_* : Ab ⥤ Ab(C)` of a point of a topos on abelian groups: internalize
the group operations, apply the direct image of sheaves of sets, and read the resulting
operations as abelian groups of sections. -/
noncomputable def skyscraperAb : AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w} :=
  (commGrpAddEquivalence.inverse ⋙ p.pushforward.mapCommGrp) ⋙ AbelianSheaf.externalSheaf J

/-- The stalk functor `p^{-1} : Ab(C) ⥤ Ab` of a point of a topos on abelian groups, the left
adjoint of `skyscraperAb`. -/
noncomputable def stalkAb : Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
  AbelianSheaf.internalSheaf J ⋙ p.inverseImage.mapCommGrp ⋙ commGrpAddEquivalence.functor

/-- The adjunction `p^{-1} ⊣ p_*` on abelian groups: the adjunction of the point lifted to
commutative group objects and composed with the two internalization equivalences. -/
noncomputable def stalkAbAdjSkyscraperAb : stalkAb p ⊣ skyscraperAb p :=
  (AbelianSheaf.equivalence J).toAdjunction.comp
    (p.adj.mapCommGrp.comp commGrpAddEquivalence.toAdjunction)

/-- Forgetting the abelian group structure of `p_*A` recovers the direct image of the
underlying set of `A`, naturally in `A`. In this construction the underlying sheaves and their
maps agree definitionally. -/
noncomputable def skyscraperAb_forgetIso :
    skyscraperAb p ⋙ sheafCompose J (forget AddCommGrpCat.{w}) ≅
      forget AddCommGrpCat.{w} ⋙ p.pushforward :=
  Iso.refl _

/-- The direct image `p_* : Ab ⥤ Ab(C)` of a point of a topos is left exact. -/
theorem preservesFiniteLimits_skyscraperAb : PreservesFiniteLimits (skyscraperAb p) :=
  have : PreservesLimitsOfSize.{0, 0} (skyscraperAb p) :=
    (stalkAbAdjSkyscraperAb p).rightAdjoint_preservesLimits
  inferInstance

/-- A split surjection of sheaves of sets is surjective on sections, hence locally
surjective. -/
private theorem isLocallySurjective_of_isSplitEpi {X Y : Sheaf J (Type w)} (ψ : X ⟶ Y)
    (hψ : IsSplitEpi ψ) : Sheaf.IsLocallySurjective ψ := by
  refine Presheaf.isLocallySurjective_of_surjective J ψ.hom fun U y => ?_
  obtain ⟨σ⟩ := hψ.exists_splitEpi
  refine ⟨σ.section_.hom.app U y, ?_⟩
  change (ConcreteCategory.hom ((σ.section_ ≫ ψ).hom.app U)) y = y
  rw [σ.id]
  rfl

/-- The direct image `p_* : Ab ⥤ Ab(C)` of a point of a topos preserves epimorphisms. -/
theorem preservesEpimorphisms_skyscraperAb : (skyscraperAb p).PreservesEpimorphisms where
  preserves {A B} f hf := by
    classical
    have hsurj : Function.Surjective ((forget AddCommGrpCat.{w}).map f) :=
      (AddCommGrpCat.epi_iff_surjective f).1 hf
    have : Epi ((forget AddCommGrpCat.{w}).map f) :=
      (epi_iff_surjective ((forget AddCommGrpCat.{w}).map f)).2 hsurj
    have hsplit : IsSplitEpi ((forget AddCommGrpCat.{w}).map f) := isSplitEpi_of_epi _
    have heq : (sheafCompose J (forget AddCommGrpCat.{w})).map ((skyscraperAb p).map f) =
        p.pushforward.map ((forget AddCommGrpCat.{w}).map f) := rfl
    have hls : Sheaf.IsLocallySurjective
        ((sheafCompose J (forget AddCommGrpCat.{w})).map ((skyscraperAb p).map f)) := by
      rw [heq]
      exact isLocallySurjective_of_isSplitEpi
        (p.pushforward.map ((forget AddCommGrpCat.{w}).map f)) inferInstance
    have : Sheaf.IsLocallySurjective ((skyscraperAb p).map f) :=
      (Presheaf.isLocallySurjective_iff_whisker_forget J ((skyscraperAb p).map f).hom).2 hls
    infer_instance

/-- The direct image `p_* : Ab ⥤ Ab(C)` of a point of a topos is exact. -/
@[stacks 05V7 "(1) p_* is exact"]
theorem skyscraperAb_exact [HasSheafify J AddCommGrpCat.{w}] :
    exactFunctor AddCommGrpCat.{w} (Sheaf J AddCommGrpCat.{w}) (skyscraperAb p) := by
  have hlim : PreservesFiniteLimits (skyscraperAb p) := preservesFiniteLimits_skyscraperAb p
  have : (skyscraperAb p).PreservesEpimorphisms := preservesEpimorphisms_skyscraperAb p
  have : (skyscraperAb p).PreservesZeroMorphisms :=
    preservesZeroMorphisms_of_preserves_terminal_object
  have : (skyscraperAb p).Additive := additive_of_preserves_binary_products _
  have : PreservesHomology (skyscraperAb p) :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  have : PreservesFiniteColimits (skyscraperAb p) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  rw [exactFunctor_iff]
  exact ⟨hlim, inferInstance⟩

end Stacks.Topos.Skyscraper

end
