module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentExact
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentRestriction

/-!
# The component restrictions on a total simplicial site are jointly conservative

Let `S` be a simplicial-site situation (Stacks 09WE). Every object of its total category lies in
one of the components (`CategoryTheory.SimplicialSiteSituation.exists_componentFunctor_obj`), and
restriction to the component of simplicial degree `n` does not change sections
(`CategoryTheory.SimplicialSiteSituation.restrict_obj_obj`). So a morphism of sheaves on the
total site whose restriction to every component is injective, or invertible, is injective, or
invertible, over every object of the total site, and hence injective or invertible.

This is the step by which a statement about a sheaf on the total site is reduced to the family of
statements about its components: it is what the proof of Stacks 0DH3 means by "we can check this
on `𝒞_n`, i.e., after applying `g_n^{-1}`".

## Main results

* `CategoryTheory.SimplicialSiteSituation.mono_iff_forall_mono_restrict` and
  `.isIso_iff_forall_isIso_restrict`: **the restrictions of sheaves of sets to the components are
  jointly conservative**, and jointly reflect injections.
* `CategoryTheory.SimplicialSiteSituation.epi_iff_forall_epi_restrict`: they also jointly reflect
  surjections.
* `CategoryTheory.SimplicialSiteSituation.mono_iff_forall_mono_componentMorphism_inverseImage`:
  the same for the inverse images along the component morphisms of topoi of Stacks 09WG, which
  are the restrictions read through the comparison of Stacks 00XR (1).
* `CategoryTheory.SimplicialSiteSituation.mono_iff_forall_mono_componentModuleRestriction`: the
  same for sheaves of modules, over the restricted sheaves of rings.

## Implementation notes

The coefficients are sets or modules in the universe of the site. For sheaves of sets the two
rewrites `CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono` and
`CategoryTheory.NatTrans.mono_iff_mono_app` reduce invertibility and injectivity of a morphism of
sheaves to the same over each object, and the instance bundle the first of them carries — a
concrete category with the sheafification colimits — is available for `Type u` on a site of that
size, but not for an arbitrary coefficient category. For sheaves of modules the reduction to
sections is the same pair of rewrites after `CategoryTheory.SheafOfModules.toSheaf`, which is
faithful and, being a right adjoint, preserves monomorphisms.

The direction that restriction preserves what it reflects is not proved by hand: restriction of
sheaves of sets preserves finite limits (`.restrict_preservesFiniteLimits`) and restriction of
sheaves of modules is a right adjoint (`.componentModuleRestriction_isRightAdjoint`), and either
property gives preservation of monomorphisms by instance search.

**Why nothing here carries a tag.** The source does not state joint conservativity of the
component restrictions as a numbered result. Stacks 09WG asserts continuity and cocontinuity of
the component inclusion and the existence and properties of `g_{n!}`; it does not assert that the
`g_n^{-1}` are jointly conservative. That is a consequence of the equivalence of Stacks 09VM
between sheaves on the total site and systems of degreewise sheaves, and is used without comment
in the proofs that reduce a statement about a sheaf on a total site to its components — among
them the proof of Stacks 0DH3. It is therefore recorded here untagged, as is its Zariski
counterpart `AlgebraicGeometry.SimplicialScheme.isIso_iff_forall_isIso_componentModule`.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09VM](https://stacks.math.columbia.edu/tag/09VM)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SimplicialSiteSituation

universe u

variable (S : SimplicialSiteSituation.{u})

section Sets

/-- **The restrictions of sheaves of sets to the simplicial components jointly reflect
injections.** A morphism of sheaves on the total site is a monomorphism as soon as its
restriction to every component is one: injectivity of a morphism of sheaves is injectivity on
sections over every object, and every object of the total category lies in a component. -/
theorem mono_iff_forall_mono_restrict {F G : Sheaf S.totalTopology (Type u)} (f : F ⟶ G) :
    Mono f ↔ ∀ n : SimplexCategory, Mono ((S.restrict.{u, u} n).map f) := by
  refine ⟨fun _ n ↦ ?_, fun h ↦ ?_⟩
  · have : PreservesLimitsOfShape WalkingCospan (S.restrict.{u, u} n) := inferInstance
    exact Functor.map_mono _ f
  · rw [Sheaf.Hom.mono_iff_presheaf_mono, NatTrans.mono_iff_mono_app]
    intro U
    obtain ⟨W⟩ := U
    obtain ⟨m, V, rfl⟩ := exists_componentFunctor_obj S W
    have hm := h m
    rw [Sheaf.Hom.mono_iff_presheaf_mono, NatTrans.mono_iff_mono_app] at hm
    exact hm (op V)

/-- **The restrictions of sheaves of sets to the simplicial components are jointly
conservative.** A morphism of sheaves on the total site is invertible as soon as its restriction
to every component is: invertibility of a morphism of sheaves is invertibility on sections over
every object, and every object of the total category lies in a component. -/
theorem isIso_iff_forall_isIso_restrict {F G : Sheaf S.totalTopology (Type u)} (f : F ⟶ G) :
    IsIso f ↔ ∀ n : SimplexCategory, IsIso ((S.restrict.{u, u} n).map f) := by
  refine ⟨fun _ n ↦ inferInstance, fun h ↦ ?_⟩
  have hval : IsIso ((sheafToPresheaf S.totalTopology (Type u)).map f) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    obtain ⟨W⟩ := U
    obtain ⟨m, V, rfl⟩ := exists_componentFunctor_obj S W
    have := h m
    have hm : IsIso ((sheafToPresheaf (S.componentTopology m) (Type u)).map
        ((S.restrict.{u, u} m).map f)) := Functor.map_isIso _ _
    rw [NatTrans.isIso_iff_isIso_app] at hm
    exact hm (op V)
  exact isIso_of_reflects_iso f (sheafToPresheaf S.totalTopology (Type u))

/-- The inverse image along the component morphism of topoi of Stacks 09WG is the restriction to
that component, by the comparison of Stacks 00XR (1): the component inclusion is cocontinuous as
well as continuous, so the sheafification in the inverse image is unnecessary. -/
noncomputable def componentMorphismInverseImageIsoRestrict (n : SimplexCategory) :
    (componentMorphism S n).inverseImage ≅ S.restrict.{u, u} n :=
  (componentFunctor S n).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    (Type u) (S.componentTopology n) S.totalTopology

/-- **The restrictions of sheaves of sets to the simplicial components jointly reflect
surjections.** A morphism of sheaves on the total site is an epimorphism as soon as its
restriction to every component is one.

Epimorphy of a morphism of sheaves of sets is local surjectivity. Given a section over an object
of the total site, that object lies in a component; local surjectivity of the restriction there
produces a covering sieve of the component over which the section is in the image, and the
component inclusion is continuous, hence cover-preserving, so the sieve that covering generates
on the total site is a covering sieve. It consists of morphisms along which the section is in the
image, because the sieve of those is a sieve. -/
theorem epi_iff_forall_epi_restrict {F G : Sheaf S.totalTopology (Type u)} (f : F ⟶ G) :
    Epi f ↔ ∀ n : SimplexCategory, Epi ((S.restrict.{u, u} n).map f) := by
  refine ⟨fun _ n ↦ ?_, fun h ↦ ?_⟩
  · have hadj : ((componentMorphism S n).inverseImage).IsLeftAdjoint :=
      ⟨_, ⟨(componentMorphism S n).adj⟩⟩
    have hepi : ((componentMorphism S n).inverseImage).PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_isLeftAdjoint _
    have := Functor.PreservesEpimorphisms.of_iso
      (componentMorphismInverseImageIsoRestrict S n)
    exact Functor.map_epi _ f
  · rw [← Sheaf.isLocallySurjective_iff_epi]
    refine ⟨fun {W} s ↦ ?_⟩
    obtain ⟨m, V, rfl⟩ := exists_componentFunctor_obj S W
    have hm : Sheaf.IsLocallySurjective ((S.restrict.{u, u} m).map f) := by
      rw [Sheaf.isLocallySurjective_iff_epi]
      exact h m
    have hs := Presheaf.imageSieve_mem (S.componentTopology m)
      ((S.restrict.{u, u} m).map f).hom (U := op V) s
    have hpush := (CoverPreserving.of_isContinuous (componentFunctor S m)
      (S.componentTopology m) S.totalTopology).cover_preserve hs
    refine S.totalTopology.superset_covering ?_ hpush
    rintro X g ⟨Y, i, hh, hi, rfl⟩
    exact (Presheaf.imageSieve f.hom s).downward_closed hi hh

/-- **The inverse images along the component morphisms of topoi jointly reflect injections.**
This is `mono_iff_forall_mono_restrict` read through
`componentMorphismInverseImageIsoRestrict`. -/
theorem mono_iff_forall_mono_componentMorphism_inverseImage
    {F G : Sheaf S.totalTopology (Type u)} (f : F ⟶ G) :
    Mono f ↔ ∀ n : SimplexCategory, Mono ((componentMorphism S n).inverseImage.map f) := by
  rw [mono_iff_forall_mono_restrict]
  refine forall_congr' fun n ↦ ?_
  have e := componentMorphismInverseImageIsoRestrict S n
  have key₁ : (S.restrict.{u, u} n).map f =
      e.inv.app F ≫ (componentMorphism S n).inverseImage.map f ≫ e.hom.app G := by
    rw [e.hom.naturality, ← Category.assoc, e.inv_hom_id_app, Category.id_comp]
  have key₂ : (componentMorphism S n).inverseImage.map f =
      e.hom.app F ≫ (S.restrict.{u, u} n).map f ≫ e.inv.app G := by
    rw [← Category.assoc, ← e.hom.naturality, Category.assoc, e.hom_inv_id_app, Category.comp_id]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := h
    rw [key₂]
    infer_instance
  · have := h
    rw [key₁]
    infer_instance

end Sets

section Modules

variable (O : Sheaf S.totalTopology RingCat.{u})

/-- **The restrictions of sheaves of modules to the simplicial components jointly reflect
injections.** A morphism of sheaves of `O`-modules on the total site is a monomorphism as soon as
its restriction to every component is one over the restricted sheaf of rings.

Injectivity of a morphism of sheaves of modules is injectivity of the underlying morphism of
abelian sheaves on sections over every object, restriction does not change sections, and every
object of the total category lies in a component. -/
theorem mono_iff_forall_mono_componentModuleRestriction {M N : SheafOfModules.{u} O}
    (α : M ⟶ N) :
    Mono α ↔ ∀ n : SimplexCategory, Mono ((componentModuleRestriction S O n).map α) := by
  refine ⟨fun _ n ↦ Functor.map_mono _ α, fun h ↦ ?_⟩
  have htotal : HasWeakSheafify S.totalTopology AddCommGrpCat.{u} :=
    (GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} S.totalTopology).1
  rw [← (SheafOfModules.toSheaf O).mono_map_iff_mono, Sheaf.Hom.mono_iff_presheaf_mono,
    NatTrans.mono_iff_mono_app]
  intro U
  obtain ⟨W⟩ := U
  obtain ⟨m, V, rfl⟩ := exists_componentFunctor_obj S W
  have hcomp : HasWeakSheafify (S.componentTopology m) AddCommGrpCat.{u} :=
    (GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} (S.componentTopology m)).1
  have hm := h m
  rw [← (SheafOfModules.toSheaf (componentRingSheaf S O m)).mono_map_iff_mono,
    Sheaf.Hom.mono_iff_presheaf_mono, NatTrans.mono_iff_mono_app] at hm
  exact hm (op V)

end Modules

end CategoryTheory.SimplicialSiteSituation

end
