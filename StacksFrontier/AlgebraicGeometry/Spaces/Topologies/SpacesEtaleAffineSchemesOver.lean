module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfAffinePresentedModules
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.CategoryTheory.Sites.SlicePost.MorphismOfSitesGeneral

/-!
# Affine schemes étale over an object of the spaces-étale site

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `X` one of its objects and `W`
an object of the spaces-étale site of `X`. The affine schemes over `W` whose composite morphism
to `X` is étale form a dense subsite of the slice `X_{spaces,étale}/W`. On it the sections of the
structure sheaf are those of the big fppf site, and the base change presheaf
`A ↦ 𝒪(A) ⊗_{𝒪(W₀)} M` attached to a module over the ring of an affine scheme `W₀` identified
with `W` is a sheaf.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.EtaleAffineSchemesOver`: the affine schemes étale over `W`.
* `AlgebraicGeometry.BigFppfSpaceSite.EtaleAffineSchemesOver.toSmallSlice`: the embedding into
  the slice `X_{spaces,étale}/W`.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.EtaleAffineSchemesOver.toSmallSlice_isCoverDense`: the
  affine schemes étale over `W` cover every object of the slice.
* `AlgebraicGeometry.BigFppfSpaceSite.EtaleAffineSchemesOver.baseChangeIsSheaf`: the base change
  presheaf is a sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {X : T.Spaces}

variable (W : Space.SpacesEtale T.schemeSite S T.scheme_mem X)

/-- The property of an affine scheme over `W` that its composite morphism to `X` is étale. -/
def IsEtaleAffineSchemeOver : ObjectProperty (AffineSchemesOver T W.obj) :=
  fun A ↦ Space.IsEtaleOver T.schemeSite S T.scheme_mem X
    ((AffineSchemesOver.toSlice T W.obj).obj A).left

/-- **The affine schemes étale over an object `W` of the spaces-étale site of `X`**: the affine
schemes over the algebraic space underlying `W` whose composite morphism to `X` is étale. -/
abbrev EtaleAffineSchemesOver := (IsEtaleAffineSchemeOver W).FullSubcategory

namespace EtaleAffineSchemesOver

variable {W}

/-- The object of the slice `X_{spaces,étale}/W` attached to an affine scheme étale over `W`. -/
abbrev toSmallSliceObj (A : EtaleAffineSchemesOver W) : Over W :=
  Over.mk (Y := ⟨((AffineSchemesOver.toSlice T W.obj).obj A.obj).left, A.property⟩)
    (ObjectProperty.homMk ((AffineSchemesOver.toSlice T W.obj).obj A.obj).hom)

variable (W) in
/-- **The embedding of the affine schemes étale over `W` into the slice `X_{spaces,étale}/W`.** -/
abbrev toSmallSlice : EtaleAffineSchemesOver W ⥤ Over W where
  obj A := toSmallSliceObj A
  map f := Over.homMk (ObjectProperty.homMk ((AffineSchemesOver.toSlice T W.obj).map f.hom).left)
    (ObjectProperty.hom_ext _ (Over.w ((AffineSchemesOver.toSlice T W.obj).map f.hom)))
  map_id A := Over.OverMorphism.ext (ObjectProperty.hom_ext _
    (congrArg (fun q => q.left) ((AffineSchemesOver.toSlice T W.obj).map_id A.obj)))
  map_comp f g := Over.OverMorphism.ext (ObjectProperty.hom_ext _
    (congrArg (fun q => q.left) ((AffineSchemesOver.toSlice T W.obj).map_comp f.hom g.hom)))

/-- The embedding of the affine schemes étale over `W` into the slice is faithful. -/
instance toSmallSlice_faithful : (toSmallSlice W).Faithful where
  map_injective h := ObjectProperty.hom_ext _ ((AffineSchemesOver.toSlice T W.obj).map_injective
    (Over.OverMorphism.ext (congrArg (fun q => q.left.hom) h)))

/-- The embedding of the affine schemes étale over `W` into the slice is full. -/
instance toSmallSlice_full : (toSmallSlice W).Full where
  map_surjective {A A'} f := by
    obtain ⟨g, hg⟩ := (AffineSchemesOver.toSlice T W.obj).map_surjective
      (X := A.obj) (Y := A'.obj) (Over.homMk f.left.hom
        (congrArg (fun q => q.hom) (Over.w f)))
    exact ⟨ObjectProperty.homMk g,
      Over.OverMorphism.ext (ObjectProperty.hom_ext _ (congrArg (fun q => q.left) hg))⟩

/-- **The affine schemes étale over `W` cover every object of the slice at `W`.** -/
instance toSmallSlice_isCoverDense :
    (toSmallSlice W).IsCoverDense
      ((Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X).over W) where
  is_cover Z := by
    rw [GrothendieckTopology.mem_over_iff]
    refine GrothendieckTopology.superset_covering _ ?_
      (Space.SpacesEtale.generate_affineSchemePresieve_mem T.schemeSite S T.scheme_mem X Z.left)
    rw [Sieve.generate_le_iff]
    rintro U g ⟨Ŵ, hŴ, ⟨e⟩⟩
    rw [Sieve.overEquiv_iff]
    have het : Space.IsEtaleOver T.schemeSite S T.scheme_mem X
        (Over.mk ((e.hom ≫ (g ≫ Z.hom).hom.left) ≫ W.obj.hom)) := by
      have h1 : (e.hom ≫ (g ≫ Z.hom).hom.left) ≫ W.obj.hom = e.hom ≫ U.obj.hom := by
        rw [Category.assoc, Over.w (g ≫ Z.hom).hom]
      change Space.IsEtale T.schemeSite S T.scheme_mem
        ((e.hom ≫ (g ≫ Z.hom).hom.left) ≫ W.obj.hom).hom
      rw [h1]
      exact Space.isEtale_comp T.schemeSite S T.scheme_mem
        (Space.isEtale_of_isIso T.schemeSite S T.scheme_mem e.hom.hom) U.property
    let A : EtaleAffineSchemesOver W :=
      ⟨⟨CostructuredArrow.mk (e.hom ≫ (g ≫ Z.hom).hom.left), hŴ⟩, het⟩
    refine ⟨⟨A, Over.homMk (ObjectProperty.homMk (Over.homMk e.inv ?_)) ?_,
      Over.homMk (ObjectProperty.homMk (Over.homMk (e.hom ≫ g.hom.left) ?_)) ?_, ?_⟩⟩
    · change e.inv ≫ (e.hom ≫ (g ≫ Z.hom).hom.left) ≫ W.obj.hom = U.obj.hom
      rw [Category.assoc, e.inv_hom_id_assoc, Over.w (g ≫ Z.hom).hom]
    · exact ObjectProperty.hom_ext _ (Over.OverMorphism.ext (e.inv_hom_id_assoc _))
    · change (e.hom ≫ g.hom.left) ≫ Z.left.obj.hom =
        (e.hom ≫ (g ≫ Z.hom).hom.left) ≫ W.obj.hom
      simp only [Category.assoc]
      rw [Over.w g.hom, Over.w (g ≫ Z.hom).hom]
    · exact ObjectProperty.hom_ext _ (Over.OverMorphism.ext (Category.assoc _ _ _))
    · exact Over.OverMorphism.ext (ObjectProperty.hom_ext _
        (Over.OverMorphism.ext (e.inv_hom_id_assoc g.hom.left)))

variable (W) in
/-- The topology on the affine schemes étale over `W` induced from the spaces-étale topology. -/
abbrev topology : GrothendieckTopology (EtaleAffineSchemesOver W) :=
  (toSmallSlice W).inducedTopology
    ((Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X).over W)

/-- The structure sheaf of rings of the spaces-étale site of `X`, restricted to the slice at
`W`. -/
noncomputable abbrev sliceRingSheaf :
    Sheaf ((Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X).over W) RingCat.{u + 1} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf
    (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O).over W

/-- The structure sheaf of rings restricted to the affine schemes étale over `W`. -/
noncomputable abbrev ringPresheaf : (EtaleAffineSchemesOver W)ᵒᵖ ⥤ RingCat.{u + 1} :=
  (Stacks.DenseSubsiteModules.ringRestriction (topology W)
    ((Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X).over W) (toSmallSlice W)
    sliceRingSheaf).obj

/-- The sections of the structure sheaf of rings on the affine schemes étale over `W` are
commutative. -/
instance ringPresheaf_commSections :
    Stacks.TerminalBaseChange.CommSections (ringPresheaf (W := W)) where
  mul_comm A a b := mul_comm (G := Space.globalFunctions' T.schemeSite S T.scheme_mem
    ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A.unop.obj.obj.left).1) a b

/-- An affine scheme together with an identification of the space it represents with the space
underlying `W`, as an affine scheme étale over `W`. -/
def ofIso (V₀ : T.Schemes)
    (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
    (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ W.obj.left) :
    EtaleAffineSchemesOver W :=
  ⟨AffineSchemesOver.ofIso V₀ hV₀ e, Space.isEtale_comp T.schemeSite S T.scheme_mem
    (Space.isEtale_of_isIso T.schemeSite S T.scheme_mem e.hom.hom) W.property⟩

/-- **An affine scheme identified with `W` is a terminal affine scheme étale over `W`.** -/
noncomputable def isTerminalOfIso (V₀ : T.Schemes)
    (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
    (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ W.obj.left) :
    IsTerminal (ofIso V₀ hV₀ e) :=
  IsTerminal.ofUniqueHom
    (fun A ↦ ObjectProperty.homMk ((AffineSchemesOver.isTerminalOfIso V₀ hV₀ e).from A.obj))
    (fun _ _ ↦ ObjectProperty.hom_ext _ ((AffineSchemesOver.isTerminalOfIso V₀ hV₀ e).hom_ext _ _))

/-- The image in the slice at `W` of an affine scheme identified with `W` is terminal. -/
noncomputable def isTerminal_toSmallSlice_ofIso (V₀ : T.Schemes)
    (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
    (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ W.obj.left) :
    IsTerminal ((toSmallSlice W).obj (ofIso V₀ hV₀ e)) :=
  Over.mkIdTerminal.ofIso
    (Over.isoMk (f := (toSmallSlice W).obj (ofIso V₀ hV₀ e)) (g := Over.mk (𝟙 W))
      (ObjectProperty.isoMk _ (Over.isoMk (f := Over.mk (e.hom ≫ W.obj.hom)) (g := W.obj) e rfl))
      (ObjectProperty.hom_ext _ (Over.OverMorphism.ext (Category.comp_id _)))).symm

/-- The base change presheaf on the affine schemes étale over `W` is the restriction of the base
change presheaf on all affine schemes over `W`. -/
theorem baseChangePresheaf_presheaf_eq (V₀ : T.Schemes)
    (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
    (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ W.obj.left)
    (M : ModuleCat.{u + 1} ((ringPresheaf (W := W)).obj (op (ofIso V₀ hV₀ e)))) :
    ((Stacks.TerminalBaseChange.baseChangePresheaf.{u + 1} (ringPresheaf (W := W))
        (isTerminalOfIso V₀ hV₀ e)).obj M).presheaf =
      (IsEtaleAffineSchemeOver W).ι.op ⋙
        ((Stacks.TerminalBaseChange.baseChangePresheaf.{u + 1}
          (AffineSchemesOver.ringPresheaf (T := T) (V := W.obj))
          (AffineSchemesOver.isTerminalOfIso V₀ hV₀ e)).obj M).presheaf := rfl

/-- **The base change presheaf `A ↦ 𝒪(A) ⊗ M` on the affine schemes étale over `W` is a
sheaf.** -/
theorem baseChangeIsSheaf (V₀ : T.Schemes)
    (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
    (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ W.obj.left) :
    Stacks.DenseSubsiteBaseChange.BaseChangeIsSheaf (topology W)
      ((Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X).over W) (toSmallSlice W)
      sliceRingSheaf (isTerminalOfIso V₀ hV₀ e) := by
  intro M
  have : (Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem X).IsContinuous
      (Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X) (BigFppfSpaceOver.topology T X) :=
    (spacesEtaleInclusion_isMorphismOfSites T X).isContinuous
  have := Functor.isContinuous_overPost_of_isContinuous
    (Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X) (BigFppfSpaceOver.topology T X)
    (Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem X) W
  let P := (AffineSchemesOver.associatedSheaf V₀ hV₀ e).obj M
  let Pab := (SheafOfModules.toSheaf _).obj P
  let Q := ((Over.post (X := W)
      (Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem X)).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} ((Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X).over W)
    ((BigFppfSpaceOver.topology T X).over
      ((Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem X).obj W))).obj Pab
  have hQ : Presheaf.IsSheaf (topology W) ((toSmallSlice W).op ⋙ Q.obj) :=
    (toSmallSlice W).op_comp_isSheaf _ _ Q
  have hQ' : Presheaf.IsSheaf (topology W) ((IsEtaleAffineSchemeOver W).ι.op ⋙
      ((AffineSchemesOver.toSlice T W.obj).op ⋙ Pab.obj)) := hQ
  let eb0 := (sheafToPresheaf _ _).mapIso ((SheafOfModules.toSheaf _).mapIso
      ((Stacks.DenseSubsiteBaseChange.associatedSheafRestrictionIso
        (AffineSchemesOver.baseChangeIsSheaf V₀ hV₀ e)).app M))
  let eb : (AffineSchemesOver.toSlice T W.obj).op ⋙ Pab.obj ≅
      ((Stacks.TerminalBaseChange.baseChangePresheaf.{u + 1}
          (AffineSchemesOver.ringPresheaf (T := T) (V := W.obj))
          (AffineSchemesOver.isTerminalOfIso V₀ hV₀ e)).obj M).presheaf := eb0
  rw [baseChangePresheaf_presheaf_eq]
  exact (Presheaf.isSheaf_of_iso_iff (Functor.isoWhiskerLeft (IsEtaleAffineSchemeOver W).ι.op eb)).1
    hQ'

end EtaleAffineSchemesOver


end AlgebraicGeometry.BigFppfSpaceSite
