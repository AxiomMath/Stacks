module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupportEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsSubsheaf

/-!
# The supported-section subsheaf and its quotient commute with étale pullback

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S`, let `T ⊆ |Y|` be a
set of points and let `G` be an `𝒪_Y`-module.  The subsheaf of sections of `G` supported on `T`
of Stacks 0859 pulls back along `f` to the subsheaf of sections of `f^*G` supported on
`|f|⁻¹T`, and therefore so does the quotient of `G` by it.

The quotient is what the strict transform of Stacks 0862 is built from, so this is the input
that part (3) of Stacks 0863 consumes; see
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformEtaleRestriction.lean`.

## Main definitions

* `AlgebraicGeometry.Space.supportedSectionsSubmoduleMap` is the morphism of supported-section
  subsheaves induced by a morphism of modules, and
  `AlgebraicGeometry.Space.supportedSectionsSubmoduleMapIso` its isomorphism version.
* `AlgebraicGeometry.Space.etaleRestrictionSupportedSectionsSheaf` is the étale restriction of
  the supported-section subsheaf, read as a sheaf submodule of the étale pullback.

## Main results

* `AlgebraicGeometry.Space.sectionSupportedIn_etaleModulePullback_iff`: a section of `f^*G` over
  an étale chart of `X` is supported on `|f|⁻¹T` exactly when the corresponding section of `G`
  over the postcomposite chart of `Y` is supported on `T`.
* `AlgebraicGeometry.Space.etaleRestrictionSupportedSectionsSheaf_eq`: the étale restriction of
  the supported-section subsheaf *is* the supported-section subsheaf of the étale pullback, as
  an equality of sheaf submodules.
* `AlgebraicGeometry.Space.supportedSectionsQuotientMapIso`: the quotient by the
  supported-section subsheaf is carried along an isomorphism of the ambient module.
* `AlgebraicGeometry.Space.etaleSupportedSectionsQuotientIso` and
  `AlgebraicGeometry.Space.modulePullbackSupportedSectionsQuotientIso`: the quotient of a module
  by its sections supported on `T` commutes with pullback along an étale morphism, for étale
  restriction of sections and for the pullback `f^*` of Stacks 03LU respectively.

## Implementation notes

The whole of the étale comparison is the chartwise statement
`AlgebraicGeometry.Space.sectionSupportedIn_etaleModulePullback_iff`, which is the abelian-sheaf
lemma `AlgebraicGeometry.Space.sectionSupportedOn_etaleAbelianRestriction_iff` applied to the
sheaf underlying the module: `AlgebraicGeometry.Space.etaleModulePullback` is restriction of
sections along `AlgebraicGeometry.Space.smallEtalePostcomp` and performs no change of scalars,
so the abelian sheaf underlying the étale pullback of a module *is* the étale restriction of the
abelian sheaf underlying it, on the nose.  That is also why the comparison is an equality of
sheaf submodules rather than only an isomorphism.

From the chartwise statement the equality of submodules is assembled by the ladder of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleIdealSheafRestriction.lean`: the restricted family of
submodules is written down first, then shown chartwise equal to the supported-section subsheaf
of the pullback by `PresheafOfModules.Submodule.ext`, which supplies the locality condition of
the restricted family by transport and hence the sheaf submodule, and
`SheafOfModules.Submodule.ext` upgrades the equality.

For the quotient two more things are needed.  First that étale restriction preserves cokernels,
which is `AlgebraicGeometry.Space.preservesFiniteColimits_etaleModulePullback` together with
additivity, the latter holding sectionwise.  Second that the quotient is carried along an
isomorphism of the ambient module, which is
`AlgebraicGeometry.Space.supportedSectionsQuotientMapIso`: a morphism of modules does not
enlarge the support of a section (Stacks 04KB,
`AlgebraicGeometry.Space.supportOfSection_map_subset`), so it restricts to the supported-section
subsheaves, functorially, and `CategoryTheory.Limits.cokernel.mapIso` applies.  That second
ingredient is what carries the comparison from étale restriction over to the pullback `f^*` of
Stacks 03LU along Stacks 03LW,
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`.

The three steps assembling `AlgebraicGeometry.Space.etaleSupportedSectionsQuotientIso` are kept
as separate declarations over abstract data, and composed only at the end: elaborating the
composite in one term makes the unifier whnf the concrete cokernels and exhausts the heartbeat
budget.

Nothing here is a clause of Stacks 0859, which has no base-change statement; the étale
compatibility that the proof of Stacks 0863 cites 0859 for is this file, and it is proved from
the defining chartwise description of the subsheaf rather than from parts (2) or (3) of that
tag — no quasi-coherence, no finitely generated ideal and no ideal-power torsion is involved.

## References

* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 085A](https://stacks.math.columbia.edu/tag/085A)
* [Stacks Project, Tag 04KB](https://stacks.math.columbia.edu/tag/04KB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

/-! ### Functoriality of the supported-section subsheaf in the module -/

section Functoriality

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (T : Set (points B S hS F)) {G₁ G₂ G₃ : Modules.{u, m} B S hS F hF}

/-- A morphism of modules `ψ : G₁ ⟶ G₂` carries a section supported in `T` to a section
supported in `T`, since the support of the image of a section is contained in the support of
the section (`AlgebraicGeometry.Space.supportOfSection_map_subset`). -/
theorem SectionSupportedIn.map (ψ : G₁ ⟶ G₂) (V : SmallEtale B S hS F)
    (s : G₁.val.obj (op V)) (hs : SectionSupportedIn B S hS F hF T G₁ V s) :
    SectionSupportedIn B S hS F hF T G₂ V (ψ.val.app (op V) s) :=
  fun _ hx => hs (supportOfSection_map_subset B S hS F
    ((SheafOfModules.toSheaf _).map ψ) V s hx)

/-- The morphism of supported-section subsheaves induced by a morphism `ψ : G₁ ⟶ G₂` of
modules: over every étale chart it is the restriction of `ψ` to the sections supported in `T`,
which lands in the sections supported in `T` by
`AlgebraicGeometry.Space.SectionSupportedIn.map`. -/
def supportedSectionsSubmoduleMap (ψ : G₁ ⟶ G₂) :
    (supportedSectionsSubmodule B S hS F hF T G₁).toSheafOfModules ⟶
      (supportedSectionsSubmodule B S hS F hF T G₂).toSheafOfModules :=
  ⟨{ app := fun V => ModuleCat.ofHom
       ((ψ.val.app V).hom.restrict (p := (supportedSectionsSubmodule B S hS F hF T G₁).obj V)
         (q := (supportedSectionsSubmodule B S hS F hF T G₂).obj V)
         (fun _ hx => SectionSupportedIn.map B S hS F hF T ψ V.unop _ hx))
     naturality := fun f => by
       ext x
       exact Subtype.ext (PresheafOfModules.naturality_apply ψ.val f x.1) }⟩

/-- The induced morphism of supported-section subsheaves is compatible with the inclusions into
the ambient modules: it is the restriction of `ψ` and nothing else. -/
theorem supportedSectionsSubmoduleMap_comp_ι (ψ : G₁ ⟶ G₂) :
    supportedSectionsSubmoduleMap B S hS F hF T ψ ≫
        (supportedSectionsSubmodule B S hS F hF T G₂).ι =
      (supportedSectionsSubmodule B S hS F hF T G₁).ι ≫ ψ := rfl

/-- The identity induces the identity on the supported-section subsheaf. -/
theorem supportedSectionsSubmoduleMap_id :
    supportedSectionsSubmoduleMap B S hS F hF T (𝟙 G₁) = 𝟙 _ := rfl

/-- The induced morphism of supported-section subsheaves is compatible with composition. -/
theorem supportedSectionsSubmoduleMap_comp (ψ : G₁ ⟶ G₂) (χ : G₂ ⟶ G₃) :
    supportedSectionsSubmoduleMap B S hS F hF T (ψ ≫ χ) =
      supportedSectionsSubmoduleMap B S hS F hF T ψ ≫
        supportedSectionsSubmoduleMap B S hS F hF T χ := rfl

/-- An isomorphism of modules induces an isomorphism of their supported-section subsheaves, by
functoriality of `AlgebraicGeometry.Space.supportedSectionsSubmoduleMap`. -/
def supportedSectionsSubmoduleMapIso (ψ : G₁ ≅ G₂) :
    (supportedSectionsSubmodule B S hS F hF T G₁).toSheafOfModules ≅
      (supportedSectionsSubmodule B S hS F hF T G₂).toSheafOfModules where
  hom := supportedSectionsSubmoduleMap B S hS F hF T ψ.hom
  inv := supportedSectionsSubmoduleMap B S hS F hF T ψ.inv
  hom_inv_id := by
    rw [← supportedSectionsSubmoduleMap_comp, ψ.hom_inv_id, supportedSectionsSubmoduleMap_id]
  inv_hom_id := by
    rw [← supportedSectionsSubmoduleMap_comp, ψ.inv_hom_id, supportedSectionsSubmoduleMap_id]

end Functoriality

/-! ### The quotient by the supported sections, along an isomorphism of modules -/

section QuotientFunctoriality

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (T : Set (points B S hS F)) {G₁ G₂ : Modules.{u, u} B S hS F hF}

/-- **The quotient of a module by its sections supported on `T` is carried along an isomorphism
of the module.**  The isomorphism of the subsheaves is
`AlgebraicGeometry.Space.supportedSectionsSubmoduleMapIso`, and it commutes with the two
inclusions, so `CategoryTheory.Limits.cokernel.mapIso` applies. -/
def supportedSectionsQuotientMapIso (ψ : G₁ ≅ G₂) :
    cokernel (supportedSectionsSubmodule B S hS F hF T G₁).ι ≅
      cokernel (supportedSectionsSubmodule B S hS F hF T G₂).ι :=
  cokernel.mapIso _ _ (supportedSectionsSubmoduleMapIso B S hS F hF T ψ) ψ
    (supportedSectionsSubmoduleMap_comp_ι B S hS F hF T ψ.hom)

end QuotientFunctoriality

/-! ### Étale restriction of the supported-section subsheaf -/

section EtaleRestriction

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- Étale restriction of modules is additive: it is restriction of sections, and addition of
morphisms of modules is computed sectionwise. -/
instance additive_etaleModulePullback (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (etaleModulePullback.{u, u} B S hS f hf).Additive :=
  ⟨by intros; ext W; rfl⟩

/-- **Being supported on a set of points is unchanged by étale restriction.**  A section of the
étale pullback `f^*G` over an étale chart `V` of `X` is supported on `|f|⁻¹T` exactly when the
corresponding section of `G` over the postcomposite chart `V ⟶ X ⟶ Y` is supported on `T`.

Both sides unfold to the same containment of subsets of the points of one and the same scheme
chart, by `AlgebraicGeometry.Space.sectionSupportedOn_etaleAbelianRestriction_iff`: the abelian
sheaf underlying `f^*G` is the étale restriction of the abelian sheaf underlying `G`. -/
theorem sectionSupportedIn_etaleModulePullback_iff (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (T : Set (points B S hS Y.1)) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (V : SmallEtale B S hS X.1)
    (s : ((etaleModulePullback B S hS f hf).obj G).val.obj (op V)) :
    SectionSupportedIn B S hS X.1 X.2 (pointsMap B S hS X.1 f.hom ⁻¹' T)
        ((etaleModulePullback B S hS f hf).obj G) V s ↔
      SectionSupportedIn B S hS Y.1 Y.2 T G ((smallEtalePostcomp B S hS f hf).obj V) s :=
  sectionSupportedOn_etaleAbelianRestriction_iff B S hS f hf T
    (moduleAddSheaf B S hS Y.1 Y.2 G) V s

/-- The étale restriction of the supported-section subsheaf of `G`, as a family of submodules of
the étale pullback `f^*G` indexed by the étale charts of `X`: its sections over a chart `V` are
the sections of `G` over the postcomposite chart `V ⟶ X ⟶ Y` that are supported on `T`.

Étale restriction of modules carries `𝒪_Y` to `𝒪_X` with no change of scalars, which is what
makes this family a family of submodules of `f^*G`. -/
def etaleRestrictionSupportedSections (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (T : Set (points B S hS Y.1)) (G : Modules.{u, u} B S hS Y.1 Y.2) :
    ((etaleModulePullback B S hS f hf).obj G).val.Submodule where
  obj V := (supportedSectionsSubmodule B S hS Y.1 Y.2 T G).toSubmodule.obj
    ((smallEtalePostcomp B S hS f hf).op.obj V)
  map g := (supportedSectionsSubmodule B S hS Y.1 Y.2 T G).toSubmodule.map
    ((smallEtalePostcomp B S hS f hf).op.map g)

/-- **The étale restriction of the supported-section subsheaf is the supported-section subsheaf
of the étale pullback, chartwise.**  This is
`AlgebraicGeometry.Space.sectionSupportedIn_etaleModulePullback_iff` assembled over all étale
charts of `X` into an equality of families of submodules of `f^*G`. -/
theorem etaleRestrictionSupportedSections_eq (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (T : Set (points B S hS Y.1)) (G : Modules.{u, u} B S hS Y.1 Y.2) :
    etaleRestrictionSupportedSections B S hS f hf T G =
      (supportedSectionsSubmodule B S hS X.1 X.2 (pointsMap B S hS X.1 f.hom ⁻¹' T)
        ((etaleModulePullback B S hS f hf).obj G)).toSubmodule :=
  PresheafOfModules.Submodule.ext fun V ↦ by
    ext s
    exact (sectionSupportedIn_etaleModulePullback_iff B S hS f hf T G V.unop s).symm

/-- The étale restriction of the supported-section subsheaf of `G`, as a *sheaf* submodule of
`f^*G`: membership is local because it is membership in the supported-section subsheaf of
`f^*G`. -/
def etaleRestrictionSupportedSectionsSheaf (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (T : Set (points B S hS Y.1)) (G : Modules.{u, u} B S hS Y.1 Y.2) :
    ((etaleModulePullback B S hS f hf).obj G).Submodule where
  toSubmodule := etaleRestrictionSupportedSections B S hS f hf T G
  isSheaf := by
    rw [etaleRestrictionSupportedSections_eq]
    exact (supportedSectionsSubmodule B S hS X.1 X.2 (pointsMap B S hS X.1 f.hom ⁻¹' T)
      ((etaleModulePullback B S hS f hf).obj G)).isSheaf

/-- **The étale restriction of the supported-section subsheaf of `G` *is* the supported-section
subsheaf of `f^*G`**, as an equality of sheaf submodules of `f^*G`. -/
theorem etaleRestrictionSupportedSectionsSheaf_eq (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (T : Set (points B S hS Y.1)) (G : Modules.{u, u} B S hS Y.1 Y.2) :
    etaleRestrictionSupportedSectionsSheaf B S hS f hf T G =
      supportedSectionsSubmodule B S hS X.1 X.2 (pointsMap B S hS X.1 f.hom ⁻¹' T)
        ((etaleModulePullback B S hS f hf).obj G) :=
  SheafOfModules.Submodule.ext (etaleRestrictionSupportedSections_eq B S hS f hf T G)

/-- The étale restriction of the inclusion of the supported-section subsheaf is the inclusion of
its étale restriction, so the two cokernels are the same object. -/
theorem cokernel_etaleModulePullback_map_supportedSections_ι (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (T : Set (points B S hS Y.1))
    (G : Modules.{u, u} B S hS Y.1 Y.2) :
    cokernel ((etaleModulePullback.{u, u} B S hS f hf).map
        (supportedSectionsSubmodule B S hS Y.1 Y.2 T G).ι) =
      cokernel (etaleRestrictionSupportedSectionsSheaf B S hS f hf T G).ι := by
  unfold SheafOfModules.Submodule.ι
  rfl

/-- The quotient by the étale restriction of the supported-section subsheaf is the quotient by
the supported-section subsheaf of the étale pullback, by
`AlgebraicGeometry.Space.etaleRestrictionSupportedSectionsSheaf_eq`. -/
theorem cokernel_etaleRestrictionSupportedSectionsSheaf_ι (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (T : Set (points B S hS Y.1))
    (G : Modules.{u, u} B S hS Y.1 Y.2) :
    cokernel (etaleRestrictionSupportedSectionsSheaf B S hS f hf T G).ι =
      cokernel (supportedSectionsSubmodule B S hS X.1 X.2 (pointsMap B S hS X.1 f.hom ⁻¹' T)
        ((etaleModulePullback B S hS f hf).obj G)).ι :=
  congrArg (fun N : ((etaleModulePullback B S hS f hf).obj G).Submodule => cokernel N.ι)
    (etaleRestrictionSupportedSectionsSheaf_eq B S hS f hf T G)

/-- Étale restriction commutes with the cokernel of the inclusion of the supported-section
subsheaf, because it preserves finite colimits
(`AlgebraicGeometry.Space.preservesFiniteColimits_etaleModulePullback`) and is additive. -/
def etaleModulePullbackSupportedSectionsCokernelIso (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (T : Set (points B S hS Y.1)) (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (etaleModulePullback.{u, u} B S hS f hf).obj
        (cokernel (supportedSectionsSubmodule B S hS Y.1 Y.2 T G).ι) ≅
      cokernel ((etaleModulePullback.{u, u} B S hS f hf).map
        (supportedSectionsSubmodule B S hS Y.1 Y.2 T G).ι) :=
  have := preservesFiniteColimits_etaleModulePullback B S hS f hf
  PreservesCokernel.iso (etaleModulePullback.{u, u} B S hS f hf)
    (supportedSectionsSubmodule B S hS Y.1 Y.2 T G).ι

/-- **The quotient of a module by its sections supported on `T` commutes with étale
restriction.**  For an étale `f : X ⟶ Y`, the étale restriction of the quotient of `G` by its
sections supported on `T` is the quotient of `f^*G` by its sections supported on `|f|⁻¹T`. -/
def etaleSupportedSectionsQuotientIso (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (T : Set (points B S hS Y.1)) (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (etaleModulePullback.{u, u} B S hS f hf).obj
        (cokernel (supportedSectionsSubmodule B S hS Y.1 Y.2 T G).ι) ≅
      cokernel (supportedSectionsSubmodule B S hS X.1 X.2 (pointsMap B S hS X.1 f.hom ⁻¹' T)
        ((etaleModulePullback B S hS f hf).obj G)).ι :=
  (etaleModulePullbackSupportedSectionsCokernelIso B S hS f hf T G).trans
    ((eqToIso (cokernel_etaleModulePullback_map_supportedSections_ι B S hS f hf T G)).trans
      (eqToIso (cokernel_etaleRestrictionSupportedSectionsSheaf_ι B S hS f hf T G)))

/-- **The quotient of a module by its sections supported on `T` commutes with pullback along an
étale morphism**, for the pullback `f^*` of Stacks 03LU: the pullback of the quotient of `G` by
its sections supported on `T` is the quotient of `f^*G` by its sections supported on `|f|⁻¹T`.

This is `AlgebraicGeometry.Space.etaleSupportedSectionsQuotientIso` transported along
Stacks 03LW, `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, the transport of
the ambient module being carried out by
`AlgebraicGeometry.Space.supportedSectionsQuotientMapIso`. -/
def modulePullbackSupportedSectionsQuotientIso (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (T : Set (points B S hS Y.1)) (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS f).obj
        (cokernel (supportedSectionsSubmodule B S hS Y.1 Y.2 T G).ι) ≅
      cokernel (supportedSectionsSubmodule B S hS X.1 X.2 (pointsMap B S hS X.1 f.hom ⁻¹' T)
        ((modulePullback B S hS f).obj G)).ι :=
  (((modulePullbackIsoEtaleModulePullback B S hS f hf).app
      (cokernel (supportedSectionsSubmodule B S hS Y.1 Y.2 T G).ι)).trans
    (etaleSupportedSectionsQuotientIso B S hS f hf T G)).trans
      (supportedSectionsQuotientMapIso B S hS X.1 X.2 (pointsMap B S hS X.1 f.hom ⁻¹' T)
        ((modulePullbackIsoEtaleModulePullback B S hS f hf).app G).symm)

end EtaleRestriction

end AlgebraicGeometry.Space

end
