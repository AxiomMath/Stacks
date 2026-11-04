module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSeparator

/-!
# Quasi-coherent modules on a flat groupoid in algebraic spaces: the Grothendieck conditions

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces whose source and target are flat.  Its
quasi-coherent modules form an abelian category by Stacks 06VZ
(`AlgebraicGeometry.Space.QuasicoherentModule.abelian_of_closure`), in which kernels and colimits
are computed on the underlying `𝒪_U`-modules.  This file proves the three Grothendieck conditions
which follow from that description alone: the forgetful functor to `𝒪_U`-modules is exact and
faithful and preserves colimits, so the category is locally small, has colimits, and its filtered
colimits are exact, these being true of `𝒪_U`-modules (Stacks 03DB).  What is left for the
category to be a Grothendieck abelian category is a separator.

## Main results

* `AlgebraicGeometry.Space.QuasicoherentModule.preservesColimitsOfSize_forget`: the forgetful
  functor preserves colimits.
* `AlgebraicGeometry.Space.QuasicoherentModule.preservesFiniteLimits_forget`: it is left exact
  when the source is flat.
* `AlgebraicGeometry.Space.QuasicoherentModule.locallySmall`: the category is locally small.
* `AlgebraicGeometry.Space.QuasicoherentModule.ab5OfSize`: filtered colimits are exact.
* `AlgebraicGeometry.Space.QuasicoherentModule.isGrothendieckAbelian_of_hasSeparator`: with a
  separator, the category is a Grothendieck abelian category.

## References

* [Stacks Project, Tag 06VZ](https://stacks.math.columbia.edu/tag/06VZ)
* [Stacks Project, Tag 077X](https://stacks.math.columbia.edu/tag/077X)
* [Stacks Project, Tag 03DB](https://stacks.math.columbia.edu/tag/03DB)
* [Stacks Project, Tag 079A](https://stacks.math.columbia.edu/tag/079A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.QuasicoherentModule

open GroupoidInAlgebraicSpaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)

/-- The forgetful functor from quasi-coherent modules on a groupoid in algebraic spaces to the
modules on its space of objects is faithful: a morphism is its underlying morphism. -/
instance faithful_forget : (forget G).Faithful where
  map_injective h := Hom.ext h

/-- Quasi-coherent modules on a groupoid in algebraic spaces have colimits indexed at the universe
of the schemes (Stacks 077X). -/
instance hasColimitsOfSize : HasColimitsOfSize.{u, u} (QuasicoherentModule B S hS G) :=
  quasicoherentModule_hasColimits_of_closure B S hS G

/-- Quasi-coherent modules on a groupoid in algebraic spaces have filtered colimits indexed at the
universe of the schemes. -/
instance hasFilteredColimitsOfSize :
    HasFilteredColimitsOfSize.{u, u} (QuasicoherentModule B S hS G) :=
  ⟨fun _ _ _ => inferInstance⟩

/-- **The forgetful functor preserves colimits.**  A colimit of quasi-coherent modules on the
groupoid is the colimit of the underlying modules, which is quasi-coherent by Stacks 03M1, with
its induced transition morphism (Stacks 077X). -/
theorem preservesColimitsOfSize_forget : PreservesColimitsOfSize.{u, u} (forget G) where
  preservesColimitsOfShape {K} _ := ⟨fun {D} => by
    have := isClosedUnderColimitsOfShape_quasicoherentSheaves_schemeUniverse B S hS
      G.objects.1 G.objects.2 K
    have hqc : (colimit (D ⋙ forget G)).IsQuasicoherentOnSite :=
      ObjectProperty.prop_colimit _ _ fun k => (D.obj k).F.property
    exact preservesColimit_of_preserves_colimit_cocone
      (liftedColimitCoconeIsColimit D _ (colimit.isColimit _) hqc)
      (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (fun j => by
        simp [liftedColimitCocone])))⟩

/-- **The forgetful functor is left exact when the source is flat.**  It preserves kernels, which
are computed on the underlying modules (Stacks 06VZ), and, being additive, finite products. -/
theorem preservesFiniteLimits_forget (hs : IsFlat B S hS G.source.hom)
    (ht : IsFlat B S hS G.target.hom) : PreservesFiniteLimits (forget G) := by
  let := abelian_of_closure G hs ht
  let := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS G.objects.1 G.objects.2
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS G.source hs
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS (G.comp ≫ G.source)
    (isFlat_comp_comp_source G hs)
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS
    (identityArrow G ≫ G.source) (isFlat_identityArrow_comp_source G)
  have : ∀ {M N : QuasicoherentModule B S hS G} (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) (forget G) := fun f =>
    preservesLimit_forget (parallelPair f 0) _ (limit.isLimit _)
      (isQuasicoherentOnSite_limit_parallelPair G f)
  exact Functor.preservesFiniteLimits_of_preservesKernels (forget G)

/-- **Quasi-coherent modules on a groupoid in algebraic spaces form a locally small category**,
at the universe of the schemes: the forgetful functor to the modules on the space of objects is
faithful, and those are locally small. -/
theorem locallySmall : LocallySmall.{u} (QuasicoherentModule B S hS G) :=
  have := locallySmall_modules_smallEtale B S hS G.objects.1 G.objects.2
  locallySmall_of_faithful (forget G)

/-- **Filtered colimits of quasi-coherent modules on a flat groupoid are exact.**  The forgetful
functor to the modules on the space of objects preserves colimits and finite limits and reflects
isomorphisms, so it reflects finite limits, and filtered colimits of modules are exact
(Stacks 03DB). -/
theorem ab5OfSize (hs : IsFlat B S hS G.source.hom) (ht : IsFlat B S hS G.target.hom) :
    letI := abelian_of_closure G hs ht
    AB5OfSize.{u, u} (QuasicoherentModule B S hS G) := by
  let := abelian_of_closure G hs ht
  have := preservesColimitsOfSize_forget G
  have := preservesFiniteLimits_forget G hs ht
  have : ReflectsFiniteLimits (forget G) :=
    ⟨fun _ _ _ => reflectsLimitsOfShape_of_reflectsIsomorphisms⟩
  exact ⟨fun K _ _ => HasExactColimitsOfShape.domain_of_functor K (forget G)⟩

/-- **The quasi-coherent modules on a flat groupoid in algebraic spaces form a Grothendieck
abelian category as soon as they have a separator**: local smallness, the existence of filtered
colimits and their exactness hold unconditionally. -/
theorem isGrothendieckAbelian_of_hasSeparator (hs : IsFlat B S hS G.source.hom)
    (ht : IsFlat B S hS G.target.hom) [HasSeparator (QuasicoherentModule B S hS G)] :
    letI := abelian_of_closure G hs ht
    IsGrothendieckAbelian.{u} (QuasicoherentModule B S hS G) :=
  let := abelian_of_closure G hs ht
  { locallySmall := locallySmall G
    ab5OfSize := ab5OfSize G hs ht }

end AlgebraicGeometry.Space.QuasicoherentModule

end
