module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformModule
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Basic

/-!
# The two strict transforms along a blowup agree

The blowup of a scheme `S` in a quasi-coherent ideal sheaf `ℐ` has two constructions, the
relative `Proj` of the Rees algebra *sheaf* (`AlgebraicGeometry.blowUp`) and the gluing of the
`Proj` of the ordinary Rees algebras (`Stacks.Blowup.blowUp`), and they are isomorphic over `S`
by `AlgebraicGeometry.blowUpIso`. Each carries its own strict transform: the general
`Stacks.StrictTransform` family for the first and the `Stacks.Blowup.strictTransform` family for
the second. This file identifies the two.

The identification is assembled from two independent facts. The `Stacks.Blowup` strict transforms
*are* the general ones at the morphism `Stacks.Blowup.blowUpToBase ℐ` and its exceptional ideal,
by definition. And the general strict transform is carried across an isomorphism of the second
morphism over `S`: the induced isomorphism of base changes transports the exceptional preimage,
hence the defining ideal, the strict transform of `X`, and — by the universal property of the
quotient by the supported sections — the strict transform of a module.

## Main definitions

* `Stacks.StrictTransform.baseChangeIso`: the identification of `X ×_S S'` with `X ×_S S''`
  induced by an isomorphism `e : S' ≅ S''` with `e ≫ b'' = b'`.
* `Stacks.StrictTransform.schemeIso` and `Stacks.StrictTransform.sheafIso`: the resulting
  identifications of the strict transform of `X` and of the strict transform of a module.
* `Stacks.Blowup.blowUpPullbackIso`, `Stacks.Blowup.strictTransformIso`,
  `Stacks.Blowup.strictTransformSheafIso` and
  `Stacks.Blowup.pullbackStrictTransformModuleIso`: those identifications for the two
  constructions of the blowup.

## Main results

* `Stacks.Blowup.strictTransformIdeal_eq_ideal` and
  `Stacks.Blowup.strictTransformSheaf_eq_sheaf`: the `Stacks.Blowup` strict transforms are the
  general ones at `Stacks.Blowup.blowUpToBase ℐ`.
* `Stacks.StrictTransform.map_ideal`: the defining ideals of the two strict transforms of `X`
  correspond under the identification of the base changes.
* `Stacks.StrictTransform.map_π_comp_sheafIso_hom`: the identification of the strict transforms
  of a module is compatible with the two quotient maps out of `pr_X^* F`.
* `Stacks.Blowup.strictTransformIso_hom_strictTransformToSource` and
  `Stacks.Blowup.strictTransformIso_hom_strictTransformMap`: the identification of the strict
  transforms of `X` is compatible with the projections to `X` and to the blowup.

## Implementation notes

`Stacks.Blowup.strictTransformSheaf` is a cokernel of
`AlgebraicGeometry.SheafOfModules.supportedSectionsSubmodule` while
`Stacks.StrictTransform.sheaf` is a cokernel of
`AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule`; the two submodules are the same
construction written over the two spellings of the site of opens, so
`Stacks.Blowup.strictTransformSheaf_eq_sheaf` holds by `rfl` even though instance search does not
see it. Stating the comparison through that equality is what keeps the rest of the file in one
vocabulary, in which both strict transforms are quotients by supported sections and the universal
property applies to each.

The universal property used is
`AlgebraicGeometry.Scheme.Modules.exists_cokernelSupportedSectionsIso` in its constructive form
`Stacks.Abelian.isoOfEpiSameKernel`, so that
`Stacks.StrictTransform.sheafIso` is a definition with a body rather than a choice from an
existence statement. Its three hypotheses are discharged as follows: both quotient maps are
epimorphisms, the pullback of one along the base-change isomorphism being the image of an
epimorphism under a left adjoint; both become isomorphisms over the complement of the exceptional
preimage, by `AlgebraicGeometry.Scheme.Modules.isIso_restrictFunctor_map_pullback_map` on the
transported side; and neither target has nonzero sections supported on the exceptional preimage,
by `AlgebraicGeometry.Scheme.Modules.supportedSections_eq_zero_of_pullback` on the transported
side. No retrocompactness or quasi-coherence hypothesis is needed for any of this.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 084L](https://stacks.math.columbia.edu/tag/084L)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.StrictTransform

open AlgebraicGeometry.Scheme.Modules hiding pullback

variable {X S S' S'' : Scheme.{u}} (f : X ⟶ S) {b' : S' ⟶ S} {b'' : S'' ⟶ S}
  (e : S' ≅ S'') (he : e.hom ≫ b'' = b') (E : S'.IdealSheafData) (E' : S''.IdealSheafData)

/-- The identification of the two base changes of `f` induced by an isomorphism `e` of the two
second morphisms over `S`: the map of fibre products which is the identity on `X` and `e` on the
second factor. -/
def baseChangeIso : baseChange f b' ≅ baseChange f b'' where
  hom := pullback.lift (pullback.fst f b') (pullback.snd f b' ≫ e.hom)
    (by rw [Category.assoc, he, pullback.condition])
  inv := pullback.lift (pullback.fst f b'') (pullback.snd f b'' ≫ e.inv)
    (by rw [Category.assoc, ← he, Iso.inv_hom_id_assoc, pullback.condition])
  hom_inv_id := by
    apply pullback.hom_ext <;>
      simp
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp

/-- The identification of the two base changes commutes with the projections to `X`. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_fst :
    (baseChangeIso f e he).hom ≫ pullback.fst f b'' = pullback.fst f b' :=
  pullback.lift_fst _ _ _

/-- The identification of the two base changes is `e` on the second factor. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_snd :
    (baseChangeIso f e he).hom ≫ pullback.snd f b'' = pullback.snd f b' ≫ e.hom :=
  pullback.lift_snd _ _ _

/-- The inverse image of the exceptional preimage for `E'` is the exceptional preimage for its
inverse image `E` on `S'`. -/
theorem baseChangeIso_preimage_exceptionalPreimage (hE : E'.comap e.hom = E) :
    (baseChangeIso f e he).hom.base ⁻¹' exceptionalPreimage f b'' E' =
      exceptionalPreimage f b' E := by
  subst hE
  have hpre {A B C : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C) (Z : Set C) :
      (p ≫ q).base ⁻¹' Z = p.base ⁻¹' (q.base ⁻¹' Z) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  rw [show exceptionalPreimage f b'' E' =
      (pullback.snd f b'').base ⁻¹' (E'.support : Set S'') from rfl, ← hpre,
    baseChangeIso_hom_snd f e he, hpre,
    show exceptionalPreimage f b' (E'.comap e.hom) =
      (pullback.snd f b').base ⁻¹' ((E'.comap e.hom).support : Set S') from rfl,
    Scheme.IdealSheafData.support_comap]
  rfl

/-- The inverse image of the open complement of the exceptional preimage for `E'` is the open
complement of the exceptional preimage for its inverse image `E` on `S'`. -/
theorem baseChangeIso_preimage_exceptionalComplement (hE : E'.comap e.hom = E) :
    (baseChangeIso f e he).hom ⁻¹ᵁ exceptionalComplement f b'' E' =
      exceptionalComplement f b' E := by
  refine TopologicalSpace.Opens.ext ?_
  change (baseChangeIso f e he).hom.base ⁻¹' ((exceptionalComplement f b'' E' : Set _)) = _
  rw [← compl_compl ((exceptionalComplement f b'' E' : Set (baseChange f b''))),
    ← exceptionalPreimage_eq_compl, Set.preimage_compl,
    baseChangeIso_preimage_exceptionalPreimage f e he E E' hE, exceptionalPreimage_eq_compl,
    compl_compl]

/-- The complement of the exceptional preimage is carried onto the complement of the exceptional
preimage, as subsets of the two base changes. -/
theorem range_exceptionalComplement_ι_comp_baseChangeIso_hom (hE : E'.comap e.hom = E) :
    Set.range ((exceptionalComplement f b' E).ι ≫ (baseChangeIso f e he).hom) =
      Set.range (exceptionalComplement f b'' E').ι := by
  have hsurj : Function.Surjective ⇑(baseChangeIso f e he).hom := by
    rw [← Scheme.coe_homeoOfIso (baseChangeIso f e he)]
    exact (Scheme.homeoOfIso (baseChangeIso f e he)).surjective
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
    Scheme.Opens.range_ι, ← baseChangeIso_preimage_exceptionalComplement f e he E E' hE,
    Scheme.Hom.coe_preimage]
  exact Set.image_preimage_eq _ hsurj

/-- **The defining ideals of the two strict transforms of `X` correspond.** The image of the
defining ideal for `b'` under the identification of the base changes is the defining ideal
for `b''`. -/
theorem map_ideal (hE : E'.comap e.hom = E) :
    (ideal f b' E).map (baseChangeIso f e he).hom = ideal f b'' E' := by
  rw [ideal_eq_ker_ι, Scheme.IdealSheafData.map_ker, ideal_eq_ker_ι,
    ← IsOpenImmersion.isoOfRangeEq_hom_fac
      ((exceptionalComplement f b' E).ι ≫ (baseChangeIso f e he).hom)
      (exceptionalComplement f b'' E').ι
      (range_exceptionalComplement_ι_comp_baseChangeIso_hom f e he E E' hE),
    Scheme.Hom.ker_comp_of_isIso]

/-- The kernel of the closed immersion of the strict transform for `b''` is the kernel of the
closed immersion of the strict transform for `b'` followed by the identification of the base
changes. -/
theorem ker_subschemeι_comp_baseChangeIso_hom (hE : E'.comap e.hom = E) :
    (ideal f b'' E').subschemeι.ker =
      ((ideal f b' E).subschemeι ≫ (baseChangeIso f e he).hom).ker := by
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.ker_subschemeι, map_ideal f e he E E' hE]

/-- **The two strict transforms of `X` agree.** The isomorphism is over the base change: see
`Stacks.StrictTransform.schemeIso_hom_subschemeι`. -/
def schemeIso (hE : E'.comap e.hom = E) : scheme f b' E ≅ scheme f b'' E' :=
  have := IsClosedImmersion.isIso_lift (ideal f b'' E').subschemeι
    ((ideal f b' E).subschemeι ≫ (baseChangeIso f e he).hom)
    (ker_subschemeι_comp_baseChangeIso_hom f e he E E' hE)
  asIso (IsClosedImmersion.lift (ideal f b'' E').subschemeι
    ((ideal f b' E).subschemeι ≫ (baseChangeIso f e he).hom)
    (ker_subschemeι_comp_baseChangeIso_hom f e he E E' hE).le)

/-- The identification of the two strict transforms of `X` commutes with their closed immersions
into the base changes, through `Stacks.StrictTransform.baseChangeIso`. -/
@[reassoc (attr := simp)]
theorem schemeIso_hom_subschemeι (hE : E'.comap e.hom = E) :
    (schemeIso f e he E E' hE).hom ≫ (ideal f b'' E').subschemeι =
      (ideal f b' E).subschemeι ≫ (baseChangeIso f e he).hom :=
  IsClosedImmersion.lift_fac _ _ _

/-- The pullback of `pr_X^* F` along the identification of the base changes is `pr_X^* F` for the
other base change. -/
def pullbackFstIso (F : X.Modules) :
    (Scheme.Modules.pullback (baseChangeIso f e he).hom).obj
        ((Scheme.Modules.pullback (pullback.fst f b'')).obj F) ≅
      (Scheme.Modules.pullback (pullback.fst f b')).obj F :=
  (Scheme.Modules.pullbackComp (baseChangeIso f e he).hom (pullback.fst f b'')).app F ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeIso_hom_fst f e he)).app F

/-- A morphism into `pr_X^* F` dies against the pullback of the quotient map for `b''` exactly
when it dies against the quotient map for `b'`: both quotient maps have the same kernel. -/
theorem comp_map_π_eq_zero_iff (hE : E'.comap e.hom = E) (F : X.Modules)
    {A : (baseChange f b').Modules}
    (a : A ⟶ (Scheme.Modules.pullback (baseChangeIso f e he).hom).obj
      ((Scheme.Modules.pullback (pullback.fst f b'')).obj F)) :
    a ≫ (Scheme.Modules.pullback (baseChangeIso f e he).hom).map (π f b'' E' F) = 0 ↔
      a ≫ ((pullbackFstIso f e he F).hom ≫ π f b' E F) = 0 := by
  have hV : (baseChangeIso f e he).hom ⁻¹ᵁ exceptionalComplement f b'' E' =
      exceptionalComplement f b' E :=
    baseChangeIso_preimage_exceptionalComplement f e he E E' hE
  have hcompl : ((exceptionalComplement f b' E : Set (baseChange f b')))ᶜ =
      (baseChangeIso f e he).hom.base ⁻¹' exceptionalPreimage f b'' E' := by
    rw [baseChangeIso_preimage_exceptionalPreimage f e he E E' hE, exceptionalPreimage_eq_compl]
  have h2 : IsIso ((restrictFunctor (exceptionalComplement f b'' E').ι).map (π f b'' E' F)) :=
    isIso_restrictFunctor_map_π f b'' E' F
  have h3 : IsIso ((restrictFunctor (exceptionalComplement f b' E).ι).map
      ((Scheme.Modules.pullback (baseChangeIso f e he).hom).map (π f b'' E' F))) := by
    have h := isIso_restrictFunctor_map_pullback_map (baseChangeIso f e he).hom
      (exceptionalComplement f b'' E') (π f b'' E' F)
    rwa [hV] at h
  have h4 : IsIso ((restrictFunctor (exceptionalComplement f b' E).ι).map (π f b' E F)) :=
    isIso_restrictFunctor_map_π f b' E F
  have h5 : IsIso ((restrictFunctor (exceptionalComplement f b' E).ι).map
      ((pullbackFstIso f e he F).hom ≫ π f b' E F)) := by
    rw [Functor.map_comp]; infer_instance
  have h6 : Mono ((restrictAdjunction (exceptionalComplement f b' E).ι).unit.app
      ((Scheme.Modules.pullback (baseChangeIso f e he).hom).obj (sheaf f b'' E' F))) := by
    refine mono_unit_app_of_supportedSections_eq_zero _ _ ?_
    rw [hcompl]
    exact supportedSections_eq_zero_of_pullback (baseChangeIso f e he).hom
      (exceptionalPreimage f b'' E') _ (supportedSections_sheaf_eq_zero f b'' E' F)
  have h7 : Mono ((restrictAdjunction (exceptionalComplement f b' E).ι).unit.app
      (sheaf f b' E F)) := mono_unit_app_sheaf f b' E F
  exact (comp_eq_zero_iff_restrictFunctor_map_eq_zero (exceptionalComplement f b' E)
      ((Scheme.Modules.pullback (baseChangeIso f e he).hom).map (π f b'' E' F)) a).trans
    (comp_eq_zero_iff_restrictFunctor_map_eq_zero (exceptionalComplement f b' E)
      ((pullbackFstIso f e he F).hom ≫ π f b' E F) a).symm

/-- **The two strict transforms of a module agree.** The strict transform for `b''`, pulled back
along the identification of the base changes, is the strict transform for `b'`. -/
def sheafIso (hE : E'.comap e.hom = E) (F : X.Modules) :
    (Scheme.Modules.pullback (baseChangeIso f e he).hom).obj (sheaf f b'' E' F) ≅
      sheaf f b' E F :=
  Stacks.Abelian.isoOfEpiSameKernel
    ((Scheme.Modules.pullback (baseChangeIso f e he).hom).map (π f b'' E' F))
    ((pullbackFstIso f e he F).hom ≫ π f b' E F)
    fun {_} a ↦ comp_map_π_eq_zero_iff f e he E E' hE F a

/-- **The identification of the two strict transforms of a module is compatible with the two
quotient maps** out of `pr_X^* F`. -/
@[reassoc (attr := simp)]
theorem map_π_comp_sheafIso_hom (hE : E'.comap e.hom = E) (F : X.Modules) :
    (Scheme.Modules.pullback (baseChangeIso f e he).hom).map (π f b'' E' F) ≫
        (sheafIso f e he E E' hE F).hom =
      (pullbackFstIso f e he F).hom ≫ π f b' E F :=
  Stacks.Abelian.isoOfEpiSameKernel_fac _ _
    fun {_} a ↦ comp_map_π_eq_zero_iff f e he E E' hE F a

end Stacks.StrictTransform

namespace Stacks.Blowup

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℐ : S.IdealSheafData)

/-- The exceptional ideal of `Stacks.Blowup.blowUp` has as inverse image along the comparison
isomorphism of the two blowups the exceptional ideal of `AlgebraicGeometry.blowUp`. -/
theorem comap_exceptionalIdeal_blowUpIso_hom :
    (exceptionalIdeal ℐ).comap (AlgebraicGeometry.blowUpIso ℐ).hom =
      AlgebraicGeometry.exceptionalIdeal ℐ := by
  rw [exceptionalIdeal, ← Scheme.IdealSheafData.comap_comp,
    AlgebraicGeometry.blowUpIso_hom_blowUpToBase]

/-- The defining ideal of the strict transform of `X` along `Stacks.Blowup.blowUp` is the general
strict-transform ideal of `Stacks.StrictTransform` at the blowup morphism and its exceptional
ideal. -/
theorem strictTransformIdeal_eq_ideal :
    strictTransformIdeal f ℐ =
      Stacks.StrictTransform.ideal f (blowUpToBase ℐ) (exceptionalIdeal ℐ) := rfl

/-- The strict transform of a module along `Stacks.Blowup.blowUp` is the general strict transform
of `Stacks.StrictTransform` at the blowup morphism and its exceptional ideal. -/
theorem strictTransformSheaf_eq_sheaf (ℱ : X.Modules) :
    strictTransformSheaf f ℐ ℱ =
      Stacks.StrictTransform.sheaf f (blowUpToBase ℐ) (exceptionalIdeal ℐ) ℱ := rfl

/-- The identification of the two base changes `X ×_S S'` of `f` along the two constructions of
the blowup of `S` in `ℐ`. -/
def blowUpPullbackIso :
    Stacks.StrictTransform.baseChange f (AlgebraicGeometry.blowUpToBase ℐ) ≅
      blowUpPullback f ℐ :=
  Stacks.StrictTransform.baseChangeIso f (AlgebraicGeometry.blowUpIso ℐ)
    (AlgebraicGeometry.blowUpIso_hom_blowUpToBase ℐ)

/-- The identification of the two base changes commutes with the projections to `X`. -/
@[reassoc (attr := simp)]
theorem blowUpPullbackIso_hom_blowUpPullbackToSource :
    (blowUpPullbackIso f ℐ).hom ≫ blowUpPullbackToSource f ℐ =
      pullback.fst f (AlgebraicGeometry.blowUpToBase ℐ) :=
  Stacks.StrictTransform.baseChangeIso_hom_fst f (AlgebraicGeometry.blowUpIso ℐ)
    (AlgebraicGeometry.blowUpIso_hom_blowUpToBase ℐ)

/-- The identification of the two base changes commutes with the projections to the two blowups,
through `AlgebraicGeometry.blowUpIso`. -/
@[reassoc (attr := simp)]
theorem blowUpPullbackIso_hom_blowUpPullbackToBlowUp :
    (blowUpPullbackIso f ℐ).hom ≫ blowUpPullbackToBlowUp f ℐ =
      pullback.snd f (AlgebraicGeometry.blowUpToBase ℐ) ≫ (AlgebraicGeometry.blowUpIso ℐ).hom :=
  Stacks.StrictTransform.baseChangeIso_hom_snd f (AlgebraicGeometry.blowUpIso ℐ)
    (AlgebraicGeometry.blowUpIso_hom_blowUpToBase ℐ)

/-- **The defining ideals of the two strict transforms of `X` along the two constructions of the
blowup correspond** under the identification of the base changes. -/
theorem map_ideal_blowUpPullbackIso_hom :
    (Stacks.StrictTransform.ideal f (AlgebraicGeometry.blowUpToBase ℐ)
        (AlgebraicGeometry.exceptionalIdeal ℐ)).map (blowUpPullbackIso f ℐ).hom =
      strictTransformIdeal f ℐ :=
  Stacks.StrictTransform.map_ideal f (AlgebraicGeometry.blowUpIso ℐ)
    (AlgebraicGeometry.blowUpIso_hom_blowUpToBase ℐ) _ _
    (comap_exceptionalIdeal_blowUpIso_hom ℐ)

/-- **The two strict transforms of `X` along the two constructions of the blowup agree.** -/
def strictTransformIso :
    Stacks.StrictTransform.scheme f (AlgebraicGeometry.blowUpToBase ℐ)
        (AlgebraicGeometry.exceptionalIdeal ℐ) ≅ strictTransform f ℐ :=
  Stacks.StrictTransform.schemeIso f (AlgebraicGeometry.blowUpIso ℐ)
    (AlgebraicGeometry.blowUpIso_hom_blowUpToBase ℐ) _ _
    (comap_exceptionalIdeal_blowUpIso_hom ℐ)

/-- The identification of the two strict transforms of `X` commutes with their closed immersions
into the base changes, through `Stacks.Blowup.blowUpPullbackIso`. -/
@[reassoc (attr := simp)]
theorem strictTransformIso_hom_strictTransformι :
    (strictTransformIso f ℐ).hom ≫ strictTransformι f ℐ =
      (Stacks.StrictTransform.ideal f (AlgebraicGeometry.blowUpToBase ℐ)
          (AlgebraicGeometry.exceptionalIdeal ℐ)).subschemeι ≫ (blowUpPullbackIso f ℐ).hom :=
  Stacks.StrictTransform.schemeIso_hom_subschemeι f (AlgebraicGeometry.blowUpIso ℐ)
    (AlgebraicGeometry.blowUpIso_hom_blowUpToBase ℐ) _ _
    (comap_exceptionalIdeal_blowUpIso_hom ℐ)

/-- The identification of the two strict transforms of `X` is compatible with the projections
to `X`. -/
@[reassoc (attr := simp)]
theorem strictTransformIso_hom_strictTransformToSource :
    (strictTransformIso f ℐ).hom ≫ strictTransformToSource f ℐ =
      (Stacks.StrictTransform.ideal f (AlgebraicGeometry.blowUpToBase ℐ)
          (AlgebraicGeometry.exceptionalIdeal ℐ)).subschemeι ≫
        pullback.fst f (AlgebraicGeometry.blowUpToBase ℐ) := by
  simp [strictTransformToSource]

/-- The identification of the two strict transforms of `X` is compatible with the projections
to the blowup, through `AlgebraicGeometry.blowUpIso`. -/
@[reassoc (attr := simp)]
theorem strictTransformIso_hom_strictTransformMap :
    (strictTransformIso f ℐ).hom ≫ strictTransformMap f ℐ =
      (Stacks.StrictTransform.ideal f (AlgebraicGeometry.blowUpToBase ℐ)
          (AlgebraicGeometry.exceptionalIdeal ℐ)).subschemeι ≫
        pullback.snd f (AlgebraicGeometry.blowUpToBase ℐ) ≫
          (AlgebraicGeometry.blowUpIso ℐ).hom := by
  simp [strictTransformMap]

/-- **The two strict transforms of a module along the two constructions of the blowup agree**, as
modules on the base change. -/
def strictTransformSheafIso (ℱ : X.Modules) :
    (Scheme.Modules.pullback (blowUpPullbackIso f ℐ).hom).obj (strictTransformSheaf f ℐ ℱ) ≅
      Stacks.StrictTransform.sheaf f (AlgebraicGeometry.blowUpToBase ℐ)
        (AlgebraicGeometry.exceptionalIdeal ℐ) ℱ :=
  Stacks.StrictTransform.sheafIso f (AlgebraicGeometry.blowUpIso ℐ)
    (AlgebraicGeometry.blowUpIso_hom_blowUpToBase ℐ) _ _
    (comap_exceptionalIdeal_blowUpIso_hom ℐ) ℱ

/-- The identification of the two strict transforms of a module is compatible with the two
quotient maps out of `pr_X^* ℱ`. -/
@[reassoc (attr := simp)]
theorem map_cokernel_π_comp_strictTransformSheafIso_hom (ℱ : X.Modules) :
    (Scheme.Modules.pullback (blowUpPullbackIso f ℐ).hom).map
          (cokernel.π (SheafOfModules.supportedSectionsSubmodule (exceptionalPullbackSet f ℐ)
            ((Scheme.Modules.pullback (blowUpPullbackToSource f ℐ)).obj ℱ)).ι) ≫
        (strictTransformSheafIso f ℐ ℱ).hom =
      (Stacks.StrictTransform.pullbackFstIso f (AlgebraicGeometry.blowUpIso ℐ)
          (AlgebraicGeometry.blowUpIso_hom_blowUpToBase ℐ) ℱ).hom ≫
        Stacks.StrictTransform.π f (AlgebraicGeometry.blowUpToBase ℐ)
          (AlgebraicGeometry.exceptionalIdeal ℐ) ℱ :=
  Stacks.StrictTransform.map_π_comp_sheafIso_hom f (AlgebraicGeometry.blowUpIso ℐ)
    (AlgebraicGeometry.blowUpIso_hom_blowUpToBase ℐ) _ _
    (comap_exceptionalIdeal_blowUpIso_hom ℐ) ℱ

/-- **The strict transform of a module, as a module on the strict transform of `X` itself, agrees
for the two constructions of the blowup.** Pulled back along the identification of the two strict
transforms of `X`, `Stacks.Blowup.strictTransformModule` is the pullback to the strict transform
of the general strict transform of `Stacks.StrictTransform`. -/
def pullbackStrictTransformModuleIso (ℱ : X.Modules) :
    (Scheme.Modules.pullback (strictTransformIso f ℐ).hom).obj (strictTransformModule f ℐ ℱ) ≅
      (Scheme.Modules.pullback (Stacks.StrictTransform.ideal f
          (AlgebraicGeometry.blowUpToBase ℐ)
          (AlgebraicGeometry.exceptionalIdeal ℐ)).subschemeι).obj
        (Stacks.StrictTransform.sheaf f (AlgebraicGeometry.blowUpToBase ℐ)
          (AlgebraicGeometry.exceptionalIdeal ℐ) ℱ) :=
  (Scheme.Modules.pullbackComp (strictTransformIso f ℐ).hom (strictTransformι f ℐ)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (strictTransformIso_hom_strictTransformι f ℐ)).app _ ≪≫
      ((Scheme.Modules.pullbackComp
        (Stacks.StrictTransform.ideal f (AlgebraicGeometry.blowUpToBase ℐ)
          (AlgebraicGeometry.exceptionalIdeal ℐ)).subschemeι
        (blowUpPullbackIso f ℐ).hom).app _).symm ≪≫
        (Scheme.Modules.pullback (Stacks.StrictTransform.ideal f
          (AlgebraicGeometry.blowUpToBase ℐ)
          (AlgebraicGeometry.exceptionalIdeal ℐ)).subschemeι).mapIso
          (strictTransformSheafIso f ℐ ℱ)

end Stacks.Blowup

end
