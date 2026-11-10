module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompactSupport
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekSubsheaf

/-!
# Proper morphisms and the support conditions on étale sheaves

The proper-support direct image `f_! F` of an abelian sheaf on the small étale site is cut out
of the ordinary direct image `f_* F` by requiring the support of a section over an étale test
object `V ⟶ Y` to be proper over `V`. When `f` itself is proper, that requirement is automatic:
the support is a closed subscheme of `X ×_Y V`, and a closed immersion followed by the proper
base change `X ×_Y V ⟶ V` is proper. Hence the canonical inclusion `f_! F ⟶ f_* F` is an
isomorphism.

The same mechanism applies to compact supports: if `X` is proper over a field `k`, then every
global section of an abelian sheaf on the small étale site of `X` has support proper over `k`,
so the subgroup of compactly supported sections is everything.

## Main results

* `AlgebraicGeometry.SmallEtale.fShriekSubsheaf_arrow_isIso`: for a proper morphism the
  inclusion of the proper-support direct image into the ordinary direct image is an
  isomorphism.
* `AlgebraicGeometry.SmallEtale.compactlySupportedSections_eq_top_of_isProper`: on a scheme
  proper over a field every global section has compact support.

## Implementation notes

The proper-support direct image is realised as the bundled monomorphism
`AlgebraicGeometry.SmallEtale.fShriekSubsheaf` into `f_* F`, so the statement `f_! = f_*` is
the assertion that this monomorphism is an isomorphism; no separate inverse has to be chosen.
It is proved by checking that the inclusion is both locally injective and locally surjective:
injectivity is sectionwise because the inclusion is a monomorphism of sheaves of abelian
groups, and surjectivity is sectionwise by the properness just described.

## References

* [Stacks Project, Tag 0F51](https://stacks.math.columbia.edu/tag/0F51)
* [Stacks Project, Tag 0F73](https://stacks.math.columbia.edu/tag/0F73)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.SmallEtale

section ProperSupport

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})

/-- Over a proper morphism every section of the direct image has proper support: its support
is a closed subscheme of `X ×_Y V`, and the projection `X ×_Y V ⟶ V` is proper. -/
public theorem properSupportSections_of_isProper [IsProper (B.inclusion.map f)]
    (V : SmallEtale B Y.obj Y.property)
    (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj V))) :
    properSupportSections B f F V s := by
  have := hasPullbacks_bigEtaleSite B
  have := preservesPullbacks_bigEtaleSiteInclusion B
  change IsProper ((Scheme.IdealSheafData.vanishingIdeal _).subschemeι ≫
    B.inclusion.map (pullback.fst V.obj.hom f))
  exact MorphismProperty.comp_mem (W := @IsProper) _ _ inferInstance
    (MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback V.obj.hom f).flip.map B.inclusion) inferInstance)

/-- **Stacks 0F51.** For a proper morphism, the canonical inclusion of the proper-support
direct image `f_! F` into the ordinary direct image `f_* F` is an isomorphism. -/
@[stacks 0F51]
public theorem fShriekSubsheaf_arrow_isIso [IsProper (B.inclusion.map f)] :
    IsIso ((fShriekSubsheaf B f F).val.arrow) := by
  set g := (fShriekSubsheaf B f F).val.arrow
  have hlocsurj : Sheaf.IsLocallySurjective g := by
    rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
    exact Presheaf.isLocallySurjective_of_surjective _ _ fun U s =>
      ((fShriekSubsheaf B f F).2 U.unop s).mpr (properSupportSections_of_isProper B f F U.unop s)
  have hlocinj : Sheaf.IsLocallyInjective g :=
    (Sheaf.isLocallyInjective_iff_injective g).2 fun U =>
      (AddCommGrpCat.mono_iff_injective _).mp
        ((NatTrans.mono_iff_mono_app (f := (sheafToPresheaf _ _).map g)).mp
          (Functor.map_mono (sheafToPresheaf _ _) g) U)
  exact (Sheaf.isLocallyBijective_iff_isIso g).mp ⟨hlocinj, hlocsurj⟩

end ProperSupport

section CompactSupport

variable (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f]
  (B : BigEtaleSite.{u}) (hX : B.Contains X)
  (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{v})

/-- **Stacks 0F73.** On a scheme proper over a field, every global section of an abelian sheaf
on the small étale site has compact support. -/
@[stacks 0F73]
public theorem compactlySupportedSections_eq_top_of_isProper :
    compactlySupportedSections k X f B hX F = ⊤ := by
  ext s
  simp only [AddSubgroup.mem_top, mem_compactlySupportedSections, iff_true]
  change IsProper ((Scheme.IdealSheafData.vanishingIdeal _).subschemeι ≫ f)
  infer_instance

end CompactSupport

end AlgebraicGeometry.SmallEtale

end
