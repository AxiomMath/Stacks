module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SupportedSectionsInjective

/-!
# The sequence of cohomology with support in a closed subscheme

Let `i : Z ⟶ X` be a closed immersion of schemes and let `j : U ⟶ X` be the inclusion of the
open complement.  For an abelian sheaf `F` on `X_étale` the sections of `F` with support in `Z`
form the kernel of the restriction map `F ⟶ j_*(F|_U)`, and that kernel is the direct image
along `i` of the abelian sheaf `ℋ_Z(F)` on `Z_étale`.  Hence the sequence

`0 ⟶ i_*ℋ_Z(F) ⟶ F ⟶ j_*(F|_U)`

is exact, naturally in `F`.

## Main definitions

* `AlgebraicGeometry.supportedSectionsPushforward` — the functor `F ↦ i_*ℋ_Z(F)`.
* `AlgebraicGeometry.supportedSectionsPushforwardIso` — its identification with the subsheaf of
  sections with support in the closed subscheme.
* `AlgebraicGeometry.supportedSectionsPushforwardInclusion` — the resulting natural
  transformation `i_*ℋ_Z ⟶ 𝟭`.
* `AlgebraicGeometry.supportedSectionsShortComplex` — the short complex
  `i_*ℋ_Z(F) ⟶ F ⟶ j_*(F|_U)`.

## Main results

* `AlgebraicGeometry.mono_supportedSectionsPushforwardInclusion_app` and
  `AlgebraicGeometry.supportedSectionsShortComplex_exact` — the sequence
  `0 ⟶ i_*ℋ_Z(F) ⟶ F ⟶ j_*(F|_U)` is exact.

## Implementation notes

The identification of `i_*ℋ_Z(F)` with the subsheaf of sections with support in `Z` is the
invertibility of the unit of the inverse image/direct image adjunction along `i` there, which is
`AlgebraicGeometry.isIso_unit_supportedSectionsSubsheaf`; assembled over all `F` it is a natural
isomorphism because the unit is natural.  Exactness is then exactness of the kernel sequence of
the restriction map, transported through the pointwise computation of the kernel of a natural
transformation and through that isomorphism.

The other two assertions of [Stacks, Tag 0A45] — the distinguished triangle
`i_*Rℋ_Z(F) ⟶ F ⟶ Rj_*(F|_U) ⟶ i_*Rℋ_Z(F)[1]` and the isomorphisms
`R^pj_*(F|_U) ≅ i_*ℋ^{p+1}_Z(F)` for `p ≥ 1` — and the surjection
`F ⟶ j_*(F|_U) ⟶ i_*ℋ¹_Z(F) ⟶ 0` completing the sequence above are not proved here; they rest
on the surjectivity of `ℐ ⟶ j_*(ℐ|_U)` for an injective abelian sheaf `ℐ`, which the source
takes from [Stacks, Tag 093X] and which is
`AlgebraicGeometry.epi_complementRestriction_app_of_injective`.  The whole of Tag 0A45 is stated
in `AlgebraicGeometry.cohomologyWithSupportSequences`.

## References

* [Stacks Project, Tag 0A45](https://stacks.math.columbia.edu/tag/0A45)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The comparison with the pointwise kernel is compatible with the two inclusions. -/
private theorem kernelObjIso_hom_comp {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Abelian D] {F G : C ⥤ D} (η : F ⟶ G) (A : C) :
    (kernelObjIso η A).hom ≫ kernel.ι (η.app A) = (kernel.ι η).app A :=
  kernelComparison_comp_ι η ((evaluation C D).obj A)

variable (B : BigEtaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
  [IsClosedImmersion (B.inclusion.map i)]

/-- Sections with support in the closed subscheme, pushed forward to the ambient small étale
site: the functor `F ↦ i_*ℋ_Z(F)`. -/
public abbrev supportedSectionsPushforward :
    SmallEtaleAbelianSheaf B X ⥤ SmallEtaleAbelianSheaf B X :=
  supportedSections B i ⋙
    (smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Z.obj Z.property)

/-- The unit of the inverse image/direct image adjunction along the closed immersion, read on
the subsheaf of sections with support in that subscheme: a natural transformation from that
subsheaf to the direct image of `ℋ_Z`. -/
public def supportedSectionsUnit :
    supportedSectionsSubsheaf B i ⟶ supportedSectionsPushforward B i where
  app F := ((smallEtaleBaseChange B i).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B Z.obj Z.property)).unit.app
      ((supportedSectionsSubsheaf B i).obj F)
  naturality _ _ f :=
    ((smallEtaleBaseChange B i).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B Z.obj Z.property)).unit.naturality
        ((supportedSectionsSubsheaf B i).map f)

/-- **The subsheaf of sections with support in a closed subscheme is the direct image of
`ℋ_Z`.** The comparison is the unit of the inverse image/direct image adjunction along the
closed immersion, invertible by `isIso_unit_supportedSectionsSubsheaf`. -/
public def supportedSectionsPushforwardIso :
    supportedSectionsSubsheaf B i ≅ supportedSectionsPushforward B i :=
  haveI : ∀ F, IsIso ((supportedSectionsUnit B i).app F) := fun F =>
    isIso_unit_supportedSectionsSubsheaf B i F
  haveI : IsIso (supportedSectionsUnit B i) := NatIso.isIso_of_isIso_app _
  asIso (supportedSectionsUnit B i)

/-- The inclusion of the subsheaf of sections with support in the closed subscheme into the
identity functor. -/
public def supportedSectionsSubsheafι :
    supportedSectionsSubsheaf B i ⟶ 𝟭 (SmallEtaleAbelianSheaf B X) :=
  kernel.ι (complementRestriction B i)

/-- The canonical map `i_*ℋ_Z(F) ⟶ F`, natural in `F`. -/
public def supportedSectionsPushforwardInclusion :
    supportedSectionsPushforward B i ⟶ 𝟭 (SmallEtaleAbelianSheaf B X) :=
  (supportedSectionsPushforwardIso B i).inv ≫ supportedSectionsSubsheafι B i

/-- The canonical map `i_*ℋ_Z(F) ⟶ F` is the comparison isomorphism followed by the inclusion
of the subsheaf of sections with support in the closed subscheme. -/
public theorem supportedSectionsPushforwardInclusion_app (F : SmallEtaleAbelianSheaf B X) :
    (supportedSectionsPushforwardInclusion B i).app F =
      (supportedSectionsPushforwardIso B i).inv.app F ≫
        (supportedSectionsSubsheafι B i).app F := by
  simp only [supportedSectionsPushforwardInclusion]
  rfl

/-- Sections with support in the closed subscheme restrict to zero on the open complement. -/
public theorem supportedSectionsSubsheafι_comp_complementRestriction :
    supportedSectionsSubsheafι B i ≫ complementRestriction B i = 0 :=
  kernel.condition (complementRestriction B i)

/-- Sections with support in the closed subscheme restrict to zero on the open complement, at
an abelian sheaf. -/
public theorem supportedSectionsSubsheafι_comp_app (F : SmallEtaleAbelianSheaf B X) :
    (supportedSectionsSubsheafι B i).app F ≫ (complementRestriction B i).app F = 0 := by
  rw [← NatTrans.comp_app, supportedSectionsSubsheafι_comp_complementRestriction,
    NatTrans.app_zero]

/-- The composition of the two maps of the sequence vanishes, at an abelian sheaf. -/
public theorem supportedSectionsPushforwardInclusion_comp_app
    (F : SmallEtaleAbelianSheaf B X) :
    (supportedSectionsPushforwardInclusion B i).app F ≫
      (complementRestriction B i).app F = 0 := by
  rw [supportedSectionsPushforwardInclusion_app, Category.assoc,
    supportedSectionsSubsheafι_comp_app, comp_zero]

/-- The canonical map `i_*ℋ_Z(F) ⟶ F` followed by restriction to the open complement
vanishes. -/
public theorem supportedSectionsPushforwardInclusion_comp_complementRestriction :
    supportedSectionsPushforwardInclusion B i ≫ complementRestriction B i = 0 :=
  NatTrans.ext (funext fun F => by
    rw [NatTrans.comp_app, supportedSectionsPushforwardInclusion_comp_app, NatTrans.app_zero])

/-- The short complex `i_*ℋ_Z(F) ⟶ F ⟶ j_*(F|_U)`: the canonical map out of the sections with
support in the closed subscheme, followed by restriction to the open complement. -/
public def supportedSectionsShortComplex (F : SmallEtaleAbelianSheaf B X) :
    ShortComplex (SmallEtaleAbelianSheaf B X) :=
  ShortComplex.mk ((supportedSectionsPushforwardInclusion B i).app F)
    ((complementRestriction B i).app F)
    (supportedSectionsPushforwardInclusion_comp_app B i F)

/-- The same sequence with the subsheaf of sections with support in the closed subscheme on the
left, before the comparison with the direct image of `ℋ_Z`. -/
private def supportedSectionsSubsheafShortComplex (F : SmallEtaleAbelianSheaf B X) :
    ShortComplex (SmallEtaleAbelianSheaf B X) :=
  ShortComplex.mk ((supportedSectionsSubsheafι B i).app F)
    ((complementRestriction B i).app F)
    (supportedSectionsSubsheafι_comp_app B i F)

/-- The value at an abelian sheaf of the subsheaf of sections with support in the closed
subscheme is the kernel of the component there of the restriction map to the open complement. -/
private def supportedSectionsSubsheafObjKernelIso (F : SmallEtaleAbelianSheaf B X) :
    (supportedSectionsSubsheaf B i).obj F ≅ kernel ((complementRestriction B i).app F) :=
  kernelObjIso (complementRestriction B i) F

/-- That comparison is compatible with the two inclusions. -/
private theorem supportedSectionsSubsheafObjKernelIso_hom_comp
    (F : SmallEtaleAbelianSheaf B X) :
    (supportedSectionsSubsheafObjKernelIso B i F).hom ≫
        kernel.ι ((complementRestriction B i).app F) =
      (supportedSectionsSubsheafι B i).app F :=
  kernelObjIso_hom_comp (complementRestriction B i) F

/-- The sequence with the subsheaf on the left is the kernel sequence of the restriction map to
the open complement. -/
private def supportedSectionsSubsheafShortComplexIso (F : SmallEtaleAbelianSheaf B X) :
    supportedSectionsSubsheafShortComplex B i F ≅
      ShortComplex.kernelSequence ((complementRestriction B i).app F) :=
  ShortComplex.isoMk (supportedSectionsSubsheafObjKernelIso B i F) (Iso.refl _)
    (Iso.refl _)
    (by
      dsimp only [supportedSectionsSubsheafShortComplex, ShortComplex.kernelSequence,
        ShortComplex.mk]
      simpa using supportedSectionsSubsheafObjKernelIso_hom_comp B i F)
    (by simp [supportedSectionsSubsheafShortComplex, ShortComplex.kernelSequence])

/-- The sequence `i_*ℋ_Z(F) ⟶ F ⟶ j_*(F|_U)` is isomorphic to the one with the subsheaf of
sections with support in the closed subscheme on the left. -/
private def supportedSectionsShortComplexIso (F : SmallEtaleAbelianSheaf B X) :
    supportedSectionsShortComplex B i F ≅ supportedSectionsSubsheafShortComplex B i F :=
  ShortComplex.isoMk ((supportedSectionsPushforwardIso B i).app F).symm (Iso.refl _)
    (Iso.refl _)
    (by
      dsimp only [supportedSectionsShortComplex, supportedSectionsSubsheafShortComplex,
        ShortComplex.mk]
      simp [supportedSectionsPushforwardInclusion_app])
    (by simp [supportedSectionsShortComplex, supportedSectionsSubsheafShortComplex])

/-- **Stacks 0A45.** The sections with support in the closed subscheme include into an abelian
sheaf: the first map of the sequence `0 ⟶ i_*ℋ_Z(F) ⟶ F ⟶ j_*(F|_U)` is a monomorphism. -/
@[stacks 0A45 "exactness of 0 ⟶ i_*ℋ_Z(F) ⟶ F ⟶ j_*(F|_U): the first map is a monomorphism"]
public theorem mono_supportedSectionsPushforwardInclusion_app
    (F : SmallEtaleAbelianSheaf B X) :
    Mono ((supportedSectionsPushforwardInclusion B i).app F) := by
  have hι : Mono ((supportedSectionsSubsheafι B i).app F) :=
    inferInstanceAs (Mono ((kernel.ι (complementRestriction B i)).app F))
  rw [supportedSectionsPushforwardInclusion_app]
  exact mono_comp _ _

/-- **Stacks 0A45.** The sequence `0 ⟶ i_*ℋ_Z(F) ⟶ F ⟶ j_*(F|_U)` is exact at `F`: a section
restricting to zero on the open complement has support in the closed subscheme.  Together with
`mono_supportedSectionsPushforwardInclusion_app` this is the exactness of that sequence. -/
@[stacks 0A45 "exactness of 0 ⟶ i_*ℋ_Z(F) ⟶ F ⟶ j_*(F|_U): exactness at F"]
public theorem supportedSectionsShortComplex_exact (F : SmallEtaleAbelianSheaf B X) :
    (supportedSectionsShortComplex B i F).Exact :=
  ShortComplex.exact_of_iso
    (supportedSectionsShortComplexIso B i F ≪≫
      supportedSectionsSubsheafShortComplexIso B i F).symm
    (ShortComplex.kernelSequence_exact ((complementRestriction B i).app F))

end AlgebraicGeometry

end
