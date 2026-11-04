module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Restriction

/-!
# Adequacy on a restricted domain of algebras

A module-valued functor on commutative `A`-algebras may be defined only on a chosen domain
`ι : C ⥤ CommAlgCat A`; `AdequateFunctor.IsAdequate ι F` is adequacy of such a functor, computed
on that domain. The domain that matters geometrically is
`AdequateFunctor.siteAlgebraInclusion A P`, the algebras whose spectra belong to a chosen big
site, because the sections of a sheaf of modules on a big site are defined exactly there.

The algebraic results on adequate module-valued functors are, however, all proved for the *full*
domain `𝟭 (CommAlgCat A)`: restriction of the base ring [Stacks, Tag 06V9], finite products
[Stacks, Tag 06VB] and descent [Stacks, Tag 06VH]. This file supplies the comparison between the
two domains, and carries 06V9 across it.

## Main definitions

* `AdequateFunctor.restrictDomain` — restriction of a module-valued functor along a functor
  `j : C' ⥤ C` of algebra domains.
* `AdequateFunctor.siteRestrictAlgebras` — an `A'`-algebra whose spectrum lies in the site,
  read as such an `A`-algebra along a ring map `A → A'`.
* `AdequateFunctor.restrictFunctorOn` — restriction of the base ring of a module-valued functor
  defined only on the site algebras, with `AdequateFunctor.restrictFunctorOn_obj` reading off
  its values.

## Main results

* `AdequateFunctor.pushforward₀_preservesLimit_parallelPair` — reindexing a presheaf of modules
  preserves kernels, because kernels are computed objectwise.
* `AdequateFunctor.IsAdequate.restrictDomain` — adequacy survives shrinking the domain.
* `AdequateFunctor.IsAdequate.exists_extension` — conversely, an adequate functor on any domain
  is the restriction of an adequate functor on *all* algebras, namely of the kernel presenting
  it. Together with the previous result this says that adequacy on a domain is exactly
  restriction of adequacy on all algebras.
* `AdequateFunctor.IsAdequate.restrictBaseOn` — [Stacks, Tag 06V9] on the site domain: adequacy
  of a functor defined on the `A`-algebras in a big site survives restriction to the
  `A'`-algebras in that site.

## Implementation notes

The condition that an algebra's spectrum belong to the big site depends only on the underlying
ring, not on the algebra structure, so `AdequateFunctor.restrictAlgebras` carries the site
algebras of `A'` into the site algebras of `A`; that is `siteRestrictAlgebras`, and
`siteRestrictAlgebras_comp_siteAlgebraInclusion` records that it is compatible with the two
inclusions on the nose.

`restrictDomain` is `PresheafOfModules.pushforward₀` for the opposite functor, i.e. plain
reindexing, and `restrictFunctorOn` is `restrictFunctor` reindexed in the same way. Both
identifications hold definitionally, which is what makes `restrictFunctor_comp_restrictDomain` and
the proof of `IsAdequate.restrictBaseOn` short: `IsAdequate.restrictBaseOn` is the composite of the
full-domain `AdequateFunctor.IsAdequate.restrict` with `IsAdequate.exists_extension` before it and
`IsAdequate.restrictDomain` after it.

No `@[stacks]` attribute is placed here. The tagged statement of 06V9 is
`AdequateFunctor.IsAdequate.restrict` in
`StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Restriction`, which already carries the
tag; `IsAdequate.restrictBaseOn` is that statement transported to a restricted domain, not a
further part of the tag's covering set.

## References

* [Stacks Project, Tag 06UT](https://stacks.math.columbia.edu/tag/06UT)
* [Stacks Project, Tag 06V9](https://stacks.math.columbia.edu/tag/06V9)
* [Stacks Project, Tag 06Z3](https://stacks.math.columbia.edu/tag/06Z3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w w' v u u' u₁ v₁ u₂ v₂ u₃ v₃

namespace AdequateFunctor

/-! ### Reindexing preserves kernels -/

section Reindex

variable {E : Type u₁} [Category.{v₁} E] {E' : Type u₂} [Category.{v₂} E']

/-- Reindexing a presheaf of modules along `K` preserves the kernel of a morphism, because
kernels of presheaves of modules are computed objectwise. -/
theorem pushforward₀_preservesLimit_parallelPair (K : E' ⥤ E) (R : Eᵒᵖ ⥤ RingCat.{w'})
    {F G : PresheafOfModules.{w} R} (e : F ⟶ G) :
    PreservesLimit (parallelPair e 0) (PresheafOfModules.pushforward₀.{w} K R) := by
  let P := PresheafOfModules.pushforward₀.{w} K R
  let c : Fork e 0 := Fork.ofι (kernel.ι e) (kernel.condition e)
  have hc : IsLimit c := kernelIsKernel e
  apply preservesLimit_of_preserves_limit_cone hc
  apply PresheafOfModules.evaluationJointlyReflectsLimits (parallelPair e 0 ⋙ P) (P.mapCone c)
  intro X
  have hc₂ : IsLimit ((P ⋙ PresheafOfModules.evaluation (K.op ⋙ R) X).mapCone c) :=
    isLimitOfPreserves (PresheafOfModules.evaluation R (K.op.obj X)) hc
  exact hc₂.ofIsoLimit (Functor.mapConeMapCone c).symm

/-- Reindexing a presheaf of modules along `K` preserves colimits of any shape admitted by
abelian groups, because colimits of presheaves of modules are computed objectwise.

`PresheafOfModules.preservesColimitsOfShape_pushforward₀` states this already, but only when the
sections of the presheaves lie in the same universe as the rings; here the value universe `w` and
the ring universe `w'` are independent, as they are for module-valued functors, so that statement
does not apply. The proof is the one there. -/
theorem pushforward₀_preservesColimitsOfShape (K : E' ⥤ E) (R : Eᵒᵖ ⥤ RingCat.{w'})
    (J : Type u₃) [Category.{v₃} J] [HasColimitsOfShape J AddCommGrpCat.{w}] :
    PreservesColimitsOfShape J (PresheafOfModules.pushforward₀.{w} K R) :=
  ⟨fun {D} => ⟨fun hc => ⟨PresheafOfModules.evaluationJointlyReflectsColimits
    (D ⋙ PresheafOfModules.pushforward₀.{w} K R) _ fun X =>
      isColimitOfPreserves (PresheafOfModules.evaluation R (K.op.obj X)) hc⟩⟩⟩

/-- Reindexing a presheaf of modules is additive, in particular it preserves zero morphisms. -/
instance pushforward₀_preservesZeroMorphisms (K : E' ⥤ E) (R : Eᵒᵖ ⥤ RingCat.{w'}) :
    (PresheafOfModules.pushforward₀.{w} K R).PreservesZeroMorphisms :=
  ⟨by intro X Y; ext Z x; rfl⟩

/-- Reindexing a presheaf of modules commutes with taking the kernel of a morphism. -/
private def pushforward₀_kernelIso (K : E' ⥤ E) (R : Eᵒᵖ ⥤ RingCat.{w'})
    {F G : PresheafOfModules.{w} R} (e : F ⟶ G) :
    (PresheafOfModules.pushforward₀.{w} K R).obj (kernel e) ≅
      kernel ((PresheafOfModules.pushforward₀.{w} K R).map e) :=
  haveI := pushforward₀_preservesLimit_parallelPair.{w} K R e
  PreservesKernel.iso _ e

end Reindex

/-! ### Shrinking the domain of algebras -/

section Domain

variable {A : Type u} [CommRing A] {C : Type u₁} [Category.{v₁} C]
  {C' : Type u₂} [Category.{v₂} C']

/-- Restrict a module-valued functor on the algebra domain `ι` to the smaller domain `j ⋙ ι`. -/
abbrev restrictDomain (j : C' ⥤ C) (ι : C ⥤ CommAlgCat.{max u v} A) :
    ModuleValuedFunctorOn.{w} ι ⥤ ModuleValuedFunctorOn.{w} (j ⋙ ι) :=
  PresheafOfModules.pushforward₀.{w} j.op (algebraRingDiagramOn.{v} ι)

/-- An adequate module-valued functor stays adequate after shrinking its domain of algebras:
the presenting modules and their map are unchanged. -/
theorem IsAdequate.restrictDomain (j : C' ⥤ C) (ι : C ⥤ CommAlgCat.{max u v} A)
    (F : ModuleValuedFunctorOn.{w} ι) (hF : IsAdequate.{w, v} ι F) :
    IsAdequate.{w, v} (j ⋙ ι) ((AdequateFunctor.restrictDomain.{w, v} j ι).obj F) := by
  obtain ⟨M, N, g, ⟨e⟩⟩ := hF
  exact ⟨M, N, g, ⟨(AdequateFunctor.restrictDomain.{max u v w, v} j ι).mapIso e ≪≫
    pushforward₀_kernelIso.{max u v w} j.op (algebraRingDiagramOn.{v} ι) _⟩⟩

/-- A linearly adequate module-valued functor stays linearly adequate after shrinking its
domain of algebras: the restriction of its presenting morphism of finite free module extensions
presents the restriction, reindexing preserving kernels. -/
theorem IsLinearlyAdequate.restrictDomain (j : C' ⥤ C) (ι : C ⥤ CommAlgCat.{max u v} A)
    (F : ModuleValuedFunctorOn.{w} ι) (hF : IsLinearlyAdequate.{w, v} ι F) :
    IsLinearlyAdequate.{w, v} (j ⋙ ι) ((AdequateFunctor.restrictDomain.{w, v} j ι).obj F) := by
  obtain ⟨n, m, g, ⟨e⟩⟩ := hF
  exact ⟨n, m, _, ⟨(AdequateFunctor.restrictDomain.{max u v w, v} j ι).mapIso e ≪≫
    pushforward₀_kernelIso.{max u v w} j.op (algebraRingDiagramOn.{v} ι) g⟩⟩

/-- An adequate module-valued functor on any domain of algebras is the restriction of an
adequate module-valued functor on all algebras, namely of the kernel that presents it. -/
theorem IsAdequate.exists_extension (ι : C ⥤ CommAlgCat.{max u v} A)
    (F : ModuleValuedFunctorOn.{w} ι) (hF : IsAdequate.{w, v} ι F) :
    ∃ G : ModuleValuedFunctor.{max u v w, v} A, IsAdequate.{max u v w, v} (𝟭 _) G ∧
      Nonempty ((presheafOfModulesUliftFunctor.{max u v} (algebraRingDiagramOn.{v} ι)).obj F ≅
        (AdequateFunctor.restrictDomain.{max u v w, v} ι (𝟭 _)).obj G) := by
  obtain ⟨M, N, g, ⟨e⟩⟩ := hF
  refine ⟨kernel ((moduleExtensionFunctor.{max u v w, v} A).map g), ⟨M, N, g, ?_⟩, ⟨?_⟩⟩
  · exact (isKernelPresentation_iff.{max u v w} _ g).mpr ⟨Iso.refl _⟩
  · exact e ≪≫
      (pushforward₀_kernelIso.{max u v w} ι.op (algebraRingDiagram.{v} A) _).symm

end Domain

/-! ### Changing the base ring on the site domain -/

section Site

variable {A : Type u} {A' : Type u'} [CommRing A] [CommRing A']

/-- An `A'`-algebra whose spectrum belongs to the chosen big site, read as such an `A`-algebra
along `f : A →+* A'`. Belonging to the site is a condition on the spectrum of the underlying
ring, which `AdequateFunctor.restrictAlgebras` does not change. -/
def siteRestrictAlgebras (f : A →+* A') (P : ObjectProperty Scheme.{max u u' v}) :
    AlgebrasInSite.{max u u' v, u'} A' P ⥤ AlgebrasInSite.{max u u' v, u} A P :=
  ObjectProperty.lift _
    (siteAlgebraInclusion.{max u u' v, u'} A' P ⋙ restrictAlgebras.{max u u' v} f)
    fun X => X.property

/-- Restricting the base ring of a site algebra is compatible with the two inclusions of site
algebras into all algebras. -/
theorem siteRestrictAlgebras_comp_siteAlgebraInclusion (f : A →+* A')
    (P : ObjectProperty Scheme.{max u u' v}) :
    siteRestrictAlgebras.{v} f P ⋙ siteAlgebraInclusion.{max u u' v, u} A P =
      siteAlgebraInclusion.{max u u' v, u'} A' P ⋙ restrictAlgebras.{max u u' v} f := rfl

/-- The identity comparison of scalar rings underlying restriction of the base ring, on the
site algebras. -/
def siteRestrictRingDiagram (f : A →+* A') (P : ObjectProperty Scheme.{max u u' v}) :
    algebraRingDiagramOn.{max u u' v} (siteAlgebraInclusion.{max u u' v, u'} A' P) ⟶
      (siteRestrictAlgebras.{v} f P).op.op ⋙
        algebraRingDiagramOn.{max u u' v} (siteAlgebraInclusion.{max u u' v, u} A P) :=
  Functor.whiskerLeft (siteAlgebraInclusion.{max u u' v, u'} A' P).op.op
    (restrictRingDiagram.{max u u' v} f)

/-- Restrict a module-valued functor on the `A`-algebras in the site to the `A'`-algebras in
the site. This is `AdequateFunctor.restrictFunctor` on the site domain. -/
def restrictFunctorOn (f : A →+* A') (P : ObjectProperty Scheme.{max u u' v}) :
    ModuleValuedFunctorOn.{w, max u u' v} (siteAlgebraInclusion.{max u u' v, u} A P) ⥤
      ModuleValuedFunctorOn.{w, max u u' v} (siteAlgebraInclusion.{max u u' v, u'} A' P) :=
  PresheafOfModules.pushforward (siteRestrictRingDiagram.{v} f P)

/-- Restriction of the base ring does not change the value of the functor: on an `A'`-algebra
in the site it is the value of the original functor on that algebra read over `A`. -/
@[simp] theorem restrictFunctorOn_obj (f : A →+* A') (P : ObjectProperty Scheme.{max u u' v})
    (F : ModuleValuedFunctorOn.{w, max u u' v} (siteAlgebraInclusion.{max u u' v, u} A P))
    (X : (AlgebrasInSite.{max u u' v, u'} A' P)ᵒᵖᵒᵖ) :
    ((((restrictFunctorOn.{w, v} f P).obj F).obj X) : Type w) =
      ((F.obj ((siteRestrictAlgebras.{v} f P).op.op.obj X)) : Type w) := rfl

/-- Restricting the base ring and shrinking the domain to the site algebras commute, on the
nose. -/
theorem restrictFunctor_comp_restrictDomain (f : A →+* A')
    (P : ObjectProperty Scheme.{max u u' v}) :
    restrictFunctor.{w, max u u' v} f ⋙
        restrictDomain.{w, max u u' v} (siteAlgebraInclusion.{max u u' v, u'} A' P) (𝟭 _) =
      restrictDomain.{w, max u u' v} (siteAlgebraInclusion.{max u u' v, u} A P) (𝟭 _) ⋙
        restrictFunctorOn.{w, v} f P := rfl

/-- [Stacks, Tag 06V9] on the site domain: an adequate module-valued functor on the
`A`-algebras in a big site stays adequate after restriction to the `A'`-algebras in that site,
with its values lifted so that the presenting modules of the restriction are available. -/
theorem IsAdequate.restrictBaseOn (f : A →+* A') (P : ObjectProperty Scheme.{max u u' v})
    (F : ModuleValuedFunctorOn.{w, max u u' v} (siteAlgebraInclusion.{max u u' v, u} A P))
    (hF : IsAdequate.{w, max u u' v} (siteAlgebraInclusion.{max u u' v, u} A P) F) :
    IsAdequate.{max u u' v w, max u u' v} (siteAlgebraInclusion.{max u u' v, u'} A' P)
      ((restrictFunctorOn.{max u u' v w, v} f P).obj
        ((presheafOfModulesUliftFunctor.{max u u' v}
            (algebraRingDiagramOn.{max u u' v}
              (siteAlgebraInclusion.{max u u' v, u} A P))).obj F)) := by
  obtain ⟨G, hG, ⟨eG⟩⟩ := IsAdequate.exists_extension
    (siteAlgebraInclusion.{max u u' v, u} A P) F hF
  exact (IsAdequate.restrictDomain.{max u u' v w, max u u' v}
    (siteAlgebraInclusion.{max u u' v, u'} A' P) (𝟭 _) _
      (IsAdequate.restrict.{max u u' v w, v} f G hG)).of_iso
    ((restrictFunctorOn.{max u u' v w, v} f P).mapIso eG ≪≫
      (presheafOfModulesUliftIso.{u, max u' v w} _ _).symm)

end Site

end AdequateFunctor

end
