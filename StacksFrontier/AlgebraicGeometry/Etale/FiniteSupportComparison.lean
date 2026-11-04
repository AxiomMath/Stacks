module

public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalk
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekComposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finite support and proper support agree for separated locally quasi-finite morphisms

Let `f : X ⟶ Y` be a morphism of a big étale site which is separated, locally of finite type
and locally quasi-finite as a morphism of schemes, and let `F` be an abelian sheaf on the small
étale site of `X`. Two direct images of `F` are available: the finite-support presheaf
`f_{p!}F` of Stacks 0F6M, whose value over an étale test object `V` is the colimit of the
groups `H_Z(F)` over the subsets `Z ⊆ X_V` carrying a subscheme structure finite over `V`; and
the proper-support sheaf `f_!F` of Stacks 0F4X, whose sections over `V` are the sections of `F`
over `X_V` whose support is proper over `V`. This file identifies the two, functorially in `F`
and compatibly with restriction along `V' ⟶ V`.

Separatedness makes every eligible support closed, so each `H_Z(F)` is already a subgroup of
`F(X_V)`; local quasi-finiteness makes every closed subset proper over `V` finite over `V`, so
every proper-support section is accounted for by one of the supports.

## Main definitions

* `AlgebraicGeometry.SmallEtale.finiteSupportOpenIso` — for separated `f`, the canonical open of
  an eligible support is all of `X_V`, so its inclusion is an isomorphism of the small étale
  site.
* `AlgebraicGeometry.SmallEtale.finiteSupportExtension` — a section supported on an eligible
  support, read as a section of `F` over the whole of `X_V`.
* `AlgebraicGeometry.SmallEtale.finiteSupportStageMap` — the map `H_Z(F) ⟶ (f_!F)(V)` sending a
  supported section to its extension, and
  `AlgebraicGeometry.SmallEtale.finiteSupportColimitToProper` the induced map out of the
  colimit.
* `AlgebraicGeometry.SmallEtale.finiteSupportComparisonApp` — the comparison map
  `(f_{p!}F)(V) ⟶ (f_!F)(V)`.

## Main results

* `AlgebraicGeometry.SmallEtale.finiteSupport_isClosed` and
  `AlgebraicGeometry.SmallEtale.isProperOver_finiteSupport` — an eligible support is closed and
  proper over `V`.
* `AlgebraicGeometry.SmallEtale.properSupportSections_of_supportSection_subset` and
  `AlgebraicGeometry.SmallEtale.finiteSupportOfProperSupport` — a section supported inside an
  eligible support has proper support, and conversely the support of a proper-support section is
  eligible.
* `AlgebraicGeometry.SmallEtale.exists_finiteSupport_union` — the eligible supports are closed
  under finite unions, so the colimit defining `f_{p!}F(V)` is filtered.
* `AlgebraicGeometry.SmallEtale.finiteSupportColimitToProper_bijective` — the comparison is
  bijective over every étale test object.

## Implementation notes

The comparison map is pinned down on the colimit generators: on the generator of an eligible
support it is the map out of that stage, which sends a supported section to its extension to
`X_V`. Since the canonical open of an eligible support is the whole of `X_V` here, that
extension restricts back to the section one started with, which is what makes the comparison
canonical.

Mathlib's `AlgebraicGeometry.LocallyQuasiFinite` does not include local finite type, unlike the
convention of the source, so the latter is assumed separately throughout.

## References

* [Stacks Project, Tag 0F6N](https://stacks.math.columbia.edu/tag/0F6N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.SmallEtale

section EligibleSupports

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- An immersion whose composite with a separated morphism is finite is a closed immersion. -/
private theorem isClosedImmersion_of_isFinite_comp {Z W W' : Scheme.{u}} (i : Z ⟶ W) {p : W ⟶ W'}
    (hfin : IsFinite (i ≫ p)) (hp : IsSeparated p) [IsImmersion i] :
    IsClosedImmersion i :=
  have := hfin
  have := hp
  have : IsFinite i := .of_comp i p
  (IsClosedImmersion.iff_isFinite_and_mono i).2 ⟨inferInstance, inferInstance⟩

/-- A property stable under base change passes from `f` to the projection `X_V ⟶ V`. -/
private theorem baseChangeProjection_of_property (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (hf : P (B.inclusion.map f))
    (V : SmallEtale B Y.obj Y.property) : P (B.inclusion.map (pullback.fst V.obj.hom f)) :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback V.obj.hom f).map B.inclusion).flip hf

/-- For a separated morphism an eligible support is closed: the immersion realising it is
finite over `V`, because the projection `X_V ⟶ V` is separated, and a finite immersion is a
closed immersion. -/
public theorem finiteSupport_isClosed [IsSeparated (B.inclusion.map f)]
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V) : IsClosed E.1 := by
  obtain ⟨Z, i, hi, hfin, hrange⟩ := E.property
  have hsep : IsSeparated (B.inclusion.map (pullback.fst V.obj.hom f)) :=
    baseChangeProjection_of_property B f @IsSeparated inferInstance V
  let : IsImmersion i := hi
  have := isClosedImmersion_of_isFinite_comp i hfin hsep
  rw [← hrange]
  exact i.isClosedEmbedding.isClosed_range

/-- For a separated morphism an eligible support is a closed subset proper over `V`: the
subscheme structure witnessing eligibility is finite over `V`, hence proper over `V`, and
properness over `V` does not depend on the chosen closed subscheme structure. -/
public theorem isProperOver_finiteSupport [IsSeparated (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)]
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V) :
    IsProper ((Scheme.IdealSheafData.vanishingIdeal
        (⟨E.1, finiteSupport_isClosed B f V E⟩ :
          Closeds ((SmallEtale.toScheme B X.obj X.property).obj
            (baseChange B f V)))).subschemeι ≫
      B.inclusion.map (pullback.fst V.obj.hom f)) := by
  let p : (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V) ⟶
      B.inclusion.obj V.obj.left := B.inclusion.map (pullback.fst V.obj.hom f)
  have : LocallyOfFiniteType p := locallyOfFiniteType_baseChangeProjection B f V
  have hsep : IsSeparated p := baseChangeProjection_of_property B f @IsSeparated inferInstance V
  have hclosed : IsClosed E.1 := finiteSupport_isClosed B f V E
  let Eclosed : Closeds ((SmallEtale.toScheme B X.obj X.property).obj
    (baseChange B f V)) := ⟨E.1, hclosed⟩
  obtain ⟨Z, i, hi, hfin, hrange⟩ := E.property
  let : IsImmersion i := hi
  have := isClosedImmersion_of_isFinite_comp i hfin hsep
  let I := i.ker
  have hIsupportSet : (I.support : Set _) = E.1 := by
    rw [Scheme.Hom.support_ker, hrange, hclosed.closure_eq]
  have hiProper : IsProper (i ≫ p) := by
    let : IsFinite (i ≫ p) := hfin
    infer_instance
  have hIProper : IsProper (I.subschemeι ≫ p) := by
    have hsurj : Surjective i.toImage := by
      refine ⟨?_⟩
      rintro ⟨x, hx⟩
      have hx' : x ∈ E.1 := by rwa [← hIsupportSet]
      obtain ⟨z, hz⟩ := hrange ▸ hx'
      exact ⟨z, I.subschemeι.isClosedEmbedding.injective <|
        congrArg I.subschemeι (Subtype.ext hz : i.toImage z = ⟨x, hx⟩)⟩
    have hiso : IsIso i.toImage :=
      (isIso_iff_isOpenImmersion_and_surjective i.toImage).2 ⟨inferInstance, hsurj⟩
    let e : Z ≅ I.subscheme := @asIso _ _ _ _ i.toImage hiso
    have heq : e.hom ≫ (I.subschemeι ≫ p) = i ≫ p := by
      show i.toImage ≫ (I.subschemeι ≫ p) = i ≫ p
      rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    have hArrow : Arrow.mk (i ≫ p) ≅ Arrow.mk (I.subschemeι ≫ p) :=
      Arrow.isoMk e (Iso.refl _) heq
    exact (MorphismProperty.arrow_mk_iso_iff @IsProper hArrow).mp hiProper
  exact (isProperOver_iff_exists_isProper p Eclosed).2 ⟨I, Closeds.ext hIsupportSet, hIProper⟩

/-- A section of `F` over `X_V` whose support lies inside an eligible support has proper
support over `V`, since a closed subset of a closed subset proper over `V` is proper
over `V`. -/
public theorem properSupportSections_of_supportSection_subset
    [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V)
    (s : F.obj.obj (op (baseChange B f V)))
    (hs : supportSection B X.obj X.property F (baseChange B f V) s ⊆ E.1) :
    properSupportSections B f F V s := by
  let p : (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V) ⟶
      B.inclusion.obj V.obj.left := B.inclusion.map (pullback.fst V.obj.hom f)
  have : LocallyOfFiniteType p := locallyOfFiniteType_baseChangeProjection B f V
  exact isProperOver_of_le p
    (show (zeroOpen B X.obj X.property F (baseChange B f V) s).compl ≤
      (⟨E.1, finiteSupport_isClosed B f V E⟩ : Closeds _) from hs)
    (isProperOver_finiteSupport B f V E)

/-- A closed subset of `X_V` proper over `V` is an eligible support: it is proper and locally
quasi-finite over `V`, hence finite over `V`. -/
public theorem isFiniteSupport_of_isProper [LocallyOfFiniteType (B.inclusion.map f)]
    [LocallyQuasiFinite (B.inclusion.map f)]
    (V : SmallEtale B Y.obj Y.property)
    (Z : Closeds ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)))
    (hZ : IsProper ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫
      B.inclusion.map (pullback.fst V.obj.hom f))) :
    IsFiniteSupport B f V (Z : Set _) := by
  let p : (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V) ⟶
      B.inclusion.obj V.obj.left := B.inclusion.map (pullback.fst V.obj.hom f)
  have hp : LocallyQuasiFinite p :=
    baseChangeProjection_of_property B f @LocallyQuasiFinite inferInstance V
  have : LocallyOfFiniteType p := locallyOfFiniteType_baseChangeProjection B f V
  obtain ⟨I, hI, hIproper⟩ := (isProperOver_iff_exists_isProper p Z).1 hZ
  have hqf : LocallyQuasiFinite (I.subschemeι ≫ p) :=
    (@LocallyQuasiFinite.comp_iff _ _ _ I.subschemeι p hp).2 inferInstance
  refine ⟨I.subscheme, I.subschemeι, inferInstance,
    (IsFinite.iff_isProper_and_locallyQuasiFinite _).2 ⟨hIproper, hqf⟩, ?_⟩
  rw [← hI]
  exact I.range_subschemeι

/-- The support of a section with proper support over `V` is an eligible support. -/
public def finiteSupportOfProperSupport [LocallyOfFiniteType (B.inclusion.map f)]
    [LocallyQuasiFinite (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (V : SmallEtale B Y.obj Y.property) (s : F.obj.obj (op (baseChange B f V)))
    (hs : properSupportSections B f F V s) : FiniteSupport B f V :=
  ⟨supportSection B X.obj X.property F (baseChange B f V) s,
    isFiniteSupport_of_isProper B f V
      (zeroOpen B X.obj X.property F (baseChange B f V) s).compl hs⟩

/-- Two eligible supports are contained in a third, namely their union. The colimit defining
the finite-support direct image is therefore filtered. -/
public theorem exists_finiteSupport_union [IsSeparated (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    (V : SmallEtale B Y.obj Y.property) (E E' : FiniteSupport B f V) :
    ∃ E'' : FiniteSupport B f V, E.1 ⊆ E''.1 ∧ E'.1 ⊆ E''.1 ∧ E''.1 = E.1 ∪ E'.1 := by
  let p : (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V) ⟶
      B.inclusion.obj V.obj.left := B.inclusion.map (pullback.fst V.obj.hom f)
  have : LocallyOfFiniteType p := locallyOfFiniteType_baseChangeProjection B f V
  let Z : Closeds ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)) :=
    ⟨E.1, finiteSupport_isClosed B f V E⟩
  let Z' : Closeds ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)) :=
    ⟨E'.1, finiteSupport_isClosed B f V E'⟩
  have hZ''proper : IsProperOver p (Z ⊔ Z') := by
    have h := isProperOver_iSup p (fun b : Bool => if b then Z else Z') (by
      intro b
      cases b
      · show IsProperOver p Z'
        exact isProperOver_finiteSupport B f V E'
      · show IsProperOver p Z
        exact isProperOver_finiteSupport B f V E)
    rwa [iSup_bool_eq] at h
  exact ⟨⟨(Z ⊔ Z' : Closeds _), isFiniteSupport_of_isProper B f V (Z ⊔ Z') hZ''proper⟩,
    Set.subset_union_left, Set.subset_union_right, rfl⟩

end EligibleSupports

section CanonicalOpen

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [IsSeparated (B.inclusion.map f)]

/-- For a separated morphism the canonical open of an eligible support is all of `X_V`: the
support is closed, and the coborder of a closed set is the whole space. -/
public theorem finiteSupportOpen_eq_top (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) : finiteSupportOpen B f V E = ⊤ :=
  Opens.ext (finiteSupport_isClosed B f V E).coborder_eq

/-- For a separated morphism the inclusion of the canonical open of an eligible support into
`X_V` is an isomorphism of the small étale site, since that open is all of `X_V`. -/
public instance isIso_openObjectι_finiteSupportOpen (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) :
    IsIso (openObjectι B X.obj X.property (baseChange B f V) (finiteSupportOpen B f V E)) := by
  have : IsIso ((SmallEtale.toScheme B X.obj X.property).map
      (openObjectι B X.obj X.property (baseChange B f V) (finiteSupportOpen B f V E))) := by
    rw [openObjectι_map, finiteSupportOpen_eq_top, ← Scheme.topIso_hom]
    infer_instance
  exact isIso_of_reflects_iso _ (SmallEtale.toScheme B X.obj X.property)

/-- The canonical open of an eligible support, as an object of the small étale site, is
canonically isomorphic to `X_V` itself. -/
public def finiteSupportOpenIso (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V) :
    finiteSupportOpenObject B f V E ≅ baseChange B f V :=
  asIso (openObjectι B X.obj X.property (baseChange B f V) (finiteSupportOpen B f V E))

/-- The forward map of `AlgebraicGeometry.SmallEtale.finiteSupportOpenIso` is the inclusion of
the canonical open of the support into `X_V`. -/
@[simp]
public theorem finiteSupportOpenIso_hom (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) :
    (finiteSupportOpenIso B f V E).hom =
      openObjectι B X.obj X.property (baseChange B f V) (finiteSupportOpen B f V E) :=
  rfl

variable (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})

/-- A section supported on an eligible support, read as a section of `F` over the whole of
`X_V` through the isomorphism `AlgebraicGeometry.SmallEtale.finiteSupportOpenIso`. -/
public def finiteSupportExtension (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V)
    (s : supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)) :
    F.obj.obj (op (baseChange B f V)) :=
  (F.obj.map (finiteSupportOpenIso B f V E).inv.op).hom s.val

/-- Restriction along an isomorphism and along its inverse are mutually inverse. -/
private theorem map_hom_map_inv_apply {C : Type*} [Category C] (G : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    {A A' : C} (e : A ≅ A') (x : G.obj (op A)) :
    (G.map e.hom.op).hom ((G.map e.inv.op).hom x) = x := by
  rw [← ConcreteCategory.comp_apply, ← G.map_comp, ← op_comp, Iso.hom_inv_id]
  simp

/-- The extension of a supported section restricts on the canonical open of its support to the
section one started with. -/
public theorem finiteSupportExtension_restrict (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V)
    (s : supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)) :
    (F.obj.map (openObjectι B X.obj X.property (baseChange B f V)
      (finiteSupportOpen B f V E)).op).hom (finiteSupportExtension B f F V E s) = s.val := by
  exact map_hom_map_inv_apply F.obj (finiteSupportOpenIso B f V E) s.val

/-- A section of `F` over `X_V` is the extension of `s` once it restricts to `s` on the canonical
open of the support. -/
private theorem finiteSupportExtension_eq_of_restrict_eq (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V)
    (s : supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E))
    (x : F.obj.obj (op (baseChange B f V)))
    (h : (F.obj.map (openObjectι B X.obj X.property (baseChange B f V)
      (finiteSupportOpen B f V E)).op).hom x = s.val) :
    finiteSupportExtension B f F V E s = x :=
  (AddCommGrpCat.mono_iff_injective _).mp inferInstance
    ((finiteSupportExtension_restrict B f F V E s).trans h.symm)

/-- The support of the extension of a supported section is contained in that support. -/
public theorem supportSection_finiteSupportExtension_subset
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V)
    (s : supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)) :
    supportSection B X.obj X.property F (baseChange B f V)
      (finiteSupportExtension B f F V E s) ⊆ E.1 := by
  have hsupp := supportSection_map B X.obj X.property F (finiteSupportOpenObject B f V E)
    (baseChange B f V) (finiteSupportOpenIso B f V E).inv s.val
  have hcomp : (SmallEtale.toScheme B X.obj X.property).map
        (finiteSupportOpenIso B f V E).inv ≫
      (SmallEtale.toScheme B X.obj X.property).map (finiteSupportOpenIso B f V E).hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  intro x hx
  have hxS : ((SmallEtale.toScheme B X.obj X.property).map
      (finiteSupportOpenIso B f V E).inv).base x ∈
      supportSection B X.obj X.property F (finiteSupportOpenObject B f V E) s.val := by
    change x ∈ supportSection B X.obj X.property F (baseChange B f V)
      ((F.obj.map (finiteSupportOpenIso B f V E).inv.op).hom s.val) at hx
    rwa [hsupp] at hx
  have hxE : (finiteSupportOpen B f V E).ι.base
      (((SmallEtale.toScheme B X.obj X.property).map
        (finiteSupportOpenIso B f V E).inv).base x) ∈ E.1 := s.property hxS
  have hι : (finiteSupportOpen B f V E).ι =
      (SmallEtale.toScheme B X.obj X.property).map (finiteSupportOpenIso B f V E).hom :=
    (openObjectι_map B X.obj X.property (baseChange B f V) (finiteSupportOpen B f V E)).symm
  have hxId : ((SmallEtale.toScheme B X.obj X.property).map (finiteSupportOpenIso B f V E).hom)
      (((SmallEtale.toScheme B X.obj X.property).map (finiteSupportOpenIso B f V E).inv) x)
      = x := by
    rw [← Scheme.Hom.comp_apply, hcomp]
    rfl
  rw [hι] at hxE
  change ((SmallEtale.toScheme B X.obj X.property).map (finiteSupportOpenIso B f V E).hom)
    (((SmallEtale.toScheme B X.obj X.property).map (finiteSupportOpenIso B f V E).inv) x)
      ∈ E.1 at hxE
  rwa [hxId] at hxE

/-- The extension of a supported section has proper support over `V`. -/
public theorem properSupportSections_finiteSupportExtension
    [LocallyOfFiniteType (B.inclusion.map f)] (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V)
    (s : supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)) :
    properSupportSections B f F V (finiteSupportExtension B f F V E s) :=
  properSupportSections_of_supportSection_subset B f F V E _
    (supportSection_finiteSupportExtension_subset B f F V E s)

end CanonicalOpen

section StageMap

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})

omit [LocallyOfFiniteType (B.inclusion.map f)] in
/-- Enlarging an eligible support and then restricting the extension to the canonical open of
the larger support is the transition map of Stacks 0F6F on supported sections. -/
public theorem finiteSupportExtension_transition (V : SmallEtale B Y.obj Y.property)
    (E E' : FiniteSupport B f V) (h : E.1 ⊆ E'.1)
    (hc : IsClosed ((Subtype.val : E'.1 → _) ⁻¹' E.1))
    (s : supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)) :
    (F.obj.map (openObjectι B X.obj X.property (baseChange B f V)
      (finiteSupportOpen B f V E')).op).hom (finiteSupportExtension B f F V E s) =
      (supportedSectionsMap B X.obj X.property F (baseChange B f V) E.1 E'.1
        (finiteSupport_isLocallyClosed B f V E) (finiteSupport_isLocallyClosed B f V E')
        h hc s).val := by
  let U := finiteSupportOpen B f V E
  let U' := finiteSupportOpen B f V E'
  let j' := openObjectι B X.obj X.property (baseChange B f V) U'
  let e := finiteSupportOpenIso B f V E
  let a := openObjectHomOfLE B X.obj X.property (baseChange B f V)
    (supportOpen_antitone B X.obj X.property (baseChange B f V) E.1 E'.1
      (finiteSupport_isLocallyClosed B f V E) (finiteSupport_isLocallyClosed B f V E') h hc)
  have hpath : j' ≫ e.inv = a := by
    apply (SmallEtale.toScheme B X.obj X.property).map_injective
    calc
      (SmallEtale.toScheme B X.obj X.property).map (j' ≫ e.inv) =
          (SmallEtale.toScheme B X.obj X.property).map j' ≫
            (SmallEtale.toScheme B X.obj X.property).map e.inv := by
        rw [Functor.map_comp]
      _ = U'.ι ≫ (SmallEtale.toScheme B X.obj X.property).map e.inv := by
        rw [openObjectι_map]
      _ = (SmallEtale.toScheme B X.obj X.property).map a := by
        apply (cancel_mono U.ι).1
        calc
          U'.ι ≫ (SmallEtale.toScheme B X.obj X.property).map e.inv ≫ U.ι = U'.ι := by
            rw [show U.ι = (SmallEtale.toScheme B X.obj X.property).map e.hom from
              (openObjectι_map B X.obj X.property (baseChange B f V) U).symm,
              ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
              Category.comp_id]
          _ = (SmallEtale.toScheme B X.obj X.property).map a ≫ U.ι := by
            rw [openObjectHomOfLE_map, Scheme.homOfLE_ι]
  calc
    _ = (F.obj.map (j' ≫ e.inv).op).hom s.val := by
      show (F.obj.map j'.op).hom ((F.obj.map e.inv.op).hom s.val) = _
      rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp]
    _ = (F.obj.map a.op).hom s.val := by rw [hpath]
    _ = _ := by rw [supportedSectionsMap_apply]

omit [LocallyOfFiniteType (B.inclusion.map f)] in
/-- Restriction to the canonical open of an eligible support is injective on sections of `F`
over `X_V`: for a separated morphism that open is all of `X_V`. -/
public theorem finiteSupportOpen_restrict_injective (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) :
    Function.Injective (F.obj.map (openObjectι B X.obj X.property (baseChange B f V)
      (finiteSupportOpen B f V E)).op).hom :=
  (AddCommGrpCat.mono_iff_injective _).mp inferInstance

omit [IsSeparated (B.inclusion.map f)] in
/-- The inclusion of `f_!F` into the small-étale direct image is injective on sections over
every étale test object. -/
public theorem fShriekSubsheaf_arrow_app_injective (V : SmallEtale B Y.obj Y.property) :
    Function.Injective ((fShriekSubsheaf B f F).val.arrow.hom.app (op V)).hom := by
  have hmono : Mono (fShriekSubsheaf B f F).val.arrow.hom :=
    Functor.map_mono (sheafToPresheaf (SmallEtale.topology B Y.obj Y.property)
      AddCommGrpCat.{v}) (fShriekSubsheaf B f F).val.arrow
  exact (AddCommGrpCat.mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app _).1 hmono (op V))

omit [LocallyOfFiniteType (B.inclusion.map f)] in
/-- Extension of supported sections to `X_V` takes the zero section to the zero section. -/
public theorem finiteSupportExtension_zero (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) : finiteSupportExtension B f F V E 0 = 0 :=
  map_zero (F.obj.map (finiteSupportOpenIso B f V E).inv.op).hom

omit [LocallyOfFiniteType (B.inclusion.map f)] in
/-- Extension of supported sections to `X_V` is additive. -/
public theorem finiteSupportExtension_add (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V)
    (s t : supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)) :
    finiteSupportExtension B f F V E (s + t) =
      finiteSupportExtension B f F V E s + finiteSupportExtension B f F V E t :=
  map_add (F.obj.map (finiteSupportOpenIso B f V E).inv.op).hom s.val t.val

/-- The map from the sections supported on an eligible support to the sections of `f_!F` over
the same test object: a supported section is sent to its extension to `X_V`, which has proper
support over `V`. -/
public def finiteSupportStageMap (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) :
    supportedSections B X.obj X.property F (baseChange B f V) E.1
        (finiteSupport_isLocallyClosed B f V E) →+
      (properSupportSheaf B f F).obj.obj (op V) where
  toFun s := ⟨finiteSupportExtension B f F V E s,
    properSupportSections_finiteSupportExtension B f F V E s⟩
  map_zero' := Subtype.ext (finiteSupportExtension_zero B f F V E)
  map_add' s t := Subtype.ext (finiteSupportExtension_add B f F V E s t)

/-- The section of `f_!F` attached to a supported section restricts to its extension
to `X_V`. -/
public theorem finiteSupportStageMap_arrow (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V)
    (s : supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)) :
    ((fShriekSubsheaf B f F).val.arrow.hom.app (op V)).hom
        (finiteSupportStageMap B f F V E s) =
      finiteSupportExtension B f F V E s :=
  rfl

/-- A section of `f_!F` is the image of a supported section once their extensions agree. -/
private theorem finiteSupportStageMap_eq_of_extension_eq (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V)
    (s : supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E))
    (y : (properSupportSheaf B f F).obj.obj (op V))
    (h : finiteSupportExtension B f F V E s =
      ((fShriekSubsheaf B f F).val.arrow.hom.app (op V)).hom y) :
    finiteSupportStageMap B f F V E s = y :=
  fShriekSubsheaf_arrow_app_injective B f F V h

/-- The map out of the stage of an eligible support, as a morphism of abelian groups from the
value of the diagram of supported sections to the sections of `f_!F`. -/
public def finiteSupportStageHom (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) :
    (finiteSupportDiagram B f F V).obj E ⟶ (properSupportSheaf B f F).obj.obj (op V) :=
  AddCommGrpCat.ofHom (finiteSupportStageMap B f F V E)

/-- The map out of the stage of an eligible support sends a supported section to its image
in `f_!F`. -/
public theorem finiteSupportStageHom_apply (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V)
    (s : supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)) :
    (finiteSupportStageHom B f F V E).hom s = finiteSupportStageMap B f F V E s :=
  rfl

/-- Distinct supported sections give distinct sections of `f_!F`. -/
public theorem finiteSupportStageMap_injective (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) :
    Function.Injective (finiteSupportStageMap B f F V E) := by
  intro s t hst
  have h : finiteSupportExtension B f F V E s = finiteSupportExtension B f F V E t :=
    congrArg (fun z => ((fShriekSubsheaf B f F).val.arrow.hom.app (op V)).hom z) hst
  have h' := congrArg (fun z => (F.obj.map (openObjectι B X.obj X.property
    (baseChange B f V) (finiteSupportOpen B f V E)).op).hom z) h
  rw [finiteSupportExtension_restrict B f F V E s,
    finiteSupportExtension_restrict B f F V E t] at h'
  exact Subtype.ext h'

/-- The maps out of the stages are compatible with the transition maps of the diagram of
supported sections, so they assemble into a cocone. -/
public theorem finiteSupportStageMap_compatible (V : SmallEtale B Y.obj Y.property)
    {E E' : FiniteSupport B f V} (h : E ⟶ E') :
    (finiteSupportDiagram B f F V).map h ≫ finiteSupportStageHom B f F V E' =
      finiteSupportStageHom B f F V E := by
  apply AddCommGrpCat.hom_ext
  ext s
  show finiteSupportStageMap B f F V E'
      (((finiteSupportDiagram B f F V).map h).hom s) = finiteSupportStageMap B f F V E s
  apply finiteSupportStageMap_eq_of_extension_eq
  refine finiteSupportExtension_eq_of_restrict_eq B f F V E' _
    (finiteSupportExtension B f F V E s) ?_
  rw [finiteSupportExtension_transition B f F V E E' (leOfHom h)
    (finiteSupport_closedWithin B f V E E' (leOfHom h)) s]
  rfl

/-- Every section of `f_!F` over an étale test object comes from a supported section: its own
support is an eligible support, because for a locally quasi-finite morphism a closed subset
proper over `V` is finite over `V`. -/
public theorem exists_finiteSupportStageMap_eq [LocallyQuasiFinite (B.inclusion.map f)]
    (V : SmallEtale B Y.obj Y.property)
    (y : (properSupportSheaf B f F).obj.obj (op V)) :
    ∃ (E : FiniteSupport B f V)
      (s : supportedSections B X.obj X.property F (baseChange B f V) E.1
        (finiteSupport_isLocallyClosed B f V E)),
      finiteSupportStageMap B f F V E s = y := by
  have ht : properSupportSections B f F V
      (((fShriekSubsheaf B f F).val.arrow.hom.app (op V)).hom y) :=
    ((fShriekSubsheaf B f F).property V _).1 ⟨y, rfl⟩
  set t : F.obj.obj (op (baseChange B f V)) :=
    ((fShriekSubsheaf B f F).val.arrow.hom.app (op V)).hom y
  let E : FiniteSupport B f V := finiteSupportOfProperSupport B f F V t ht
  have hE : E.1 = supportSection B X.obj X.property F (baseChange B f V) t := rfl
  have hsupp := supportSection_map B X.obj X.property F (baseChange B f V)
    (finiteSupportOpenObject B f V E) (finiteSupportOpenIso B f V E).hom t
  refine ⟨E, ⟨(F.obj.map (finiteSupportOpenIso B f V E).hom.op).hom t, ?_⟩, ?_⟩
  · have hι : (SmallEtale.toScheme B X.obj X.property).map
        (finiteSupportOpenIso B f V E).hom = (finiteSupportOpen B f V E).ι :=
      openObjectι_map B X.obj X.property (baseChange B f V) (finiteSupportOpen B f V E)
    show supportSection B X.obj X.property F (finiteSupportOpenObject B f V E)
      ((F.obj.map (finiteSupportOpenIso B f V E).hom.op).hom t) ⊆
        (finiteSupportOpen B f V E).ι.base ⁻¹' E.1
    rw [hsupp, hι, hE]
  · apply finiteSupportStageMap_eq_of_extension_eq
    exact map_hom_map_inv_apply F.obj (finiteSupportOpenIso B f V E).symm t

/-- The maps out of the stages are compatible with restriction along a morphism `V' ⟶ V` of
the small étale site of `Y`. -/
public theorem finiteSupportStageMap_restrict {V V' : SmallEtale B Y.obj Y.property}
    (g : V' ⟶ V) (E : FiniteSupport B f V)
    (s : supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)) :
    letI d := finiteSupportBaseChange B f F g E
    finiteSupportStageMap B f F V' d.support (d.sectionsMap s) =
      (((properSupportFunctor B f).obj F).obj.map g.op).hom
        (finiteSupportStageMap B f F V E s) := by
  let d := finiteSupportBaseChange B f F g E
  show finiteSupportStageMap B f F V' d.support (d.sectionsMap s) =
    (((properSupportFunctor B f).obj F).obj.map g.op).hom
      (finiteSupportStageMap B f F V E s)
  let c := (smallEtaleBaseChange B f).map g
  let j := openObjectι B X.obj X.property (baseChange B f V) (finiteSupportOpen B f V E)
  let j' := openObjectι B X.obj X.property (baseChange B f V')
    (finiteSupportOpen B f V' d.support)
  let η := (fShriekSubsheaf B f F).val.arrow.hom
  have hc : j' ≫ c = d.openMap ≫ j := by
    apply (SmallEtale.toScheme B X.obj X.property).map_injective
    rw [Functor.map_comp, Functor.map_comp, openObjectι_map, openObjectι_map]
    exact d.openMap_commutes.symm
  have hfun : F.obj.map c.op ≫ F.obj.map j'.op = F.obj.map j.op ≫ F.obj.map d.openMap.op := by
    rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp, hc]
  have hcomm (t : (properSupportSheaf B f F).obj.obj (op V)) :
      (η.app (op V')).hom ((((properSupportFunctor B f).obj F).obj.map g.op).hom t) =
        (F.obj.map c.op).hom ((η.app (op V)).hom t) := by
    have hnat := ConcreteCategory.congr_hom (η.naturality g.op) t
    simp only [Functor.sheafPushforwardContinuous_obj_obj_map, Quiver.Hom.unop_op] at hnat
    exact hnat
  apply finiteSupportStageMap_eq_of_extension_eq
  rw [hcomm]
  refine finiteSupportExtension_eq_of_restrict_eq B f F V' d.support _
    ((F.obj.map c.op).hom (finiteSupportExtension B f F V E s)) ?_
  rw [d.sectionsMap_apply s, ← finiteSupportExtension_restrict B f F V E s]
  simpa only [ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom hfun (finiteSupportExtension B f F V E s)

/-- The maps out of the stages are natural in the abelian sheaf. -/
public theorem finiteSupportStageMap_sheaf
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}}
    (φ : F ⟶ G) (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V)
    (s : supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)) :
    finiteSupportStageMap B f G V E
        (supportedSectionsSheafMap B X.obj X.property φ (baseChange B f V) E.1
          (finiteSupport_isLocallyClosed B f V E) s) =
      (((properSupportFunctor B f).map φ).hom.app (op V)).hom
        (finiteSupportStageMap B f F V E s) := by
  let j := openObjectι B X.obj X.property (baseChange B f V) (finiteSupportOpen B f V E)
  let ηF := (fShriekSubsheaf B f F).val.arrow.hom.app (op V)
  let ηG := (fShriekSubsheaf B f G).val.arrow.hom.app (op V)
  have hcomm (t : (properSupportSheaf B f F).obj.obj (op V)) :
      ηG.hom ((((properSupportFunctor B f).map φ).hom.app (op V)).hom t) =
        (φ.hom.app (op (baseChange B f V))).hom (ηF.hom t) := by
    have hp := congrArg (fun k => k.hom.app (op V) |>.hom t) (fShriekMap B f F G φ).property
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      Functor.sheafPushforwardContinuous_map_hom_app] at hp
    exact hp
  apply finiteSupportStageMap_eq_of_extension_eq
  rw [hcomm]
  refine finiteSupportExtension_eq_of_restrict_eq B f G V E _
    ((φ.hom.app (op (baseChange B f V))).hom (finiteSupportExtension B f F V E s)) ?_
  change _ = (φ.hom.app (op _)).hom s.val
  rw [← finiteSupportExtension_restrict B f F V E s]
  simpa only [ConcreteCategory.comp_apply] using
    (ConcreteCategory.congr_hom (φ.hom.naturality j.op) (finiteSupportExtension B f F V E s)).symm

end StageMap

section Comparison

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]

/-- The eligible supports over an étale test object form a filtered category: the empty subset
is one of them, and the union of two of them is one of them. This is what makes the colimit
defining the finite-support direct image a filtered colimit. -/
public theorem isFiltered_finiteSupport [LocallyQuasiFinite (B.inclusion.map f)]
    (V : SmallEtale B Y.obj Y.property) : IsFiltered (FiniteSupport B f V) where
  toIsFilteredOrEmpty :=
    { cocone_objs := by
        intro E E'
        obtain ⟨E'', hE, hE', _⟩ := exists_finiteSupport_union B f V E E'
        exact ⟨E'', homOfLE hE, homOfLE hE', trivial⟩
      cocone_maps := by
        intro E E' _ _
        exact ⟨E', 𝟙 _, by subsingleton⟩ }
  nonempty := by
    have : LocallyOfFiniteType (B.inclusion.map (pullback.fst V.obj.hom f)) :=
      locallyOfFiniteType_baseChangeProjection B f V
    exact ⟨⟨_, isFiniteSupport_of_isProper B f V ⊥
      (isProperOver_bot (B.inclusion.map (pullback.fst V.obj.hom f)))⟩⟩

variable (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max u v})

/-- The cocone on the diagram of supported sections whose leg at an eligible support is the
map out of that stage. -/
public def finiteSupportCocone (V : SmallEtale B Y.obj Y.property) :
    Cocone (finiteSupportDiagram B f F V) where
  pt := (properSupportSheaf B f F).obj.obj (op V)
  ι :=
    { app := fun E => AddCommGrpCat.ofHom (finiteSupportStageMap B f F V E)
      naturality := by
        intro E E' h
        exact finiteSupportStageMap_compatible B f F V h }

/-- The map from the colimit of the supported sections over all eligible supports to the
sections of `f_!F` over the same test object, induced by the maps out of the stages. -/
public def finiteSupportColimitToProper (V : SmallEtale B Y.obj Y.property)
    [Small.{max u v} (FiniteSupport B f V)] :
    colimit (finiteSupportDiagram B f F V) ⟶ (properSupportSheaf B f F).obj.obj (op V) :=
  colimit.desc (finiteSupportDiagram B f F V) (finiteSupportCocone B f F V)

/-- The leg of the cocone at an eligible support is the map out of that stage. -/
public theorem finiteSupportCocone_ι_app (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) :
    (finiteSupportCocone B f F V).ι.app E = finiteSupportStageHom B f F V E :=
  rfl

/-- On the colimit generator of an eligible support the comparison map is the leg of the
defining cocone at that stage. -/
public theorem finiteSupportColimitToProper_ι (V : SmallEtale B Y.obj Y.property)
    [Small.{max u v} (FiniteSupport B f V)] (E : FiniteSupport B f V) :
    colimit.ι (finiteSupportDiagram B f F V) E ≫ finiteSupportColimitToProper B f F V =
      (finiteSupportCocone B f F V).ι.app E :=
  colimit.ι_desc (finiteSupportCocone B f F V) E

/-- The comparison map out of the colimit is bijective: injective because each stage injects
into `f_!F` and the index is filtered, surjective because the support of a proper-support
section is itself an eligible support. -/
public theorem finiteSupportColimitToProper_bijective
    [LocallyQuasiFinite (B.inclusion.map f)] (V : SmallEtale B Y.obj Y.property)
    [Small.{max u v} (FiniteSupport B f V)] :
    Function.Bijective (finiteSupportColimitToProper B f F V).hom := by
  classical
  have : IsFiltered (FiniteSupport B f V) := isFiltered_finiteSupport B f V
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{max u v})
  constructor
  · intro x y hxy
    obtain ⟨E, s, hs⟩ := Concrete.colimit_exists_rep (finiteSupportDiagram B f F V) x
    obtain ⟨E', t, ht⟩ := Concrete.colimit_exists_rep (finiteSupportDiagram B f F V) y
    have hE := ConcreteCategory.congr_hom (finiteSupportColimitToProper_ι B f F V E) s
    have hE' := ConcreteCategory.congr_hom (finiteSupportColimitToProper_ι B f F V E') t
    simp only [ConcreteCategory.comp_apply, finiteSupportCocone_ι_app] at hE hE'
    have hstage : (finiteSupportStageHom B f F V E).hom s =
        (finiteSupportStageHom B f F V E').hom t := by
      rw [← hs, ← ht] at hxy
      rwa [← hE, ← hE']
    obtain ⟨E'', hE₂, hE₂', _⟩ := exists_finiteSupport_union B f V E E'
    have hinj : Function.Injective (finiteSupportStageHom B f F V E'').hom := fun _ _ hab =>
      finiteSupportStageMap_injective B f F V E'' hab
    have hcommon : ((finiteSupportDiagram B f F V).map (homOfLE hE₂)).hom s =
        ((finiteSupportDiagram B f F V).map (homOfLE hE₂')).hom t := by
      apply hinj
      have hleft := ConcreteCategory.congr_hom
        (finiteSupportStageMap_compatible B f F V (homOfLE hE₂)) s
      have hright := ConcreteCategory.congr_hom
        (finiteSupportStageMap_compatible B f F V (homOfLE hE₂')) t
      simp only [ConcreteCategory.comp_apply] at hleft hright
      exact hleft.trans (hstage.trans hright.symm)
    exact hs ▸ ht ▸ Concrete.colimit_rep_eq_of_exists (finiteSupportDiagram B f F V) s t
      ⟨E'', homOfLE hE₂, homOfLE hE₂', hcommon⟩
  · intro y
    obtain ⟨E, s, hs⟩ := exists_finiteSupportStageMap_eq B f F V y
    refine ⟨(colimit.ι (finiteSupportDiagram B f F V) E).hom s, ?_⟩
    have h := ConcreteCategory.congr_hom (finiteSupportColimitToProper_ι B f F V E) s
    simp only [finiteSupportCocone_ι_app] at h
    exact h.trans hs

variable (hsmall : ∀ V : SmallEtale B Y.obj Y.property, Small.{max u v} (FiniteSupport B f V))
  (P : {P : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max u v} ⥤
      ((SmallEtale B Y.obj Y.property)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) //
    FiniteSupportPushforwardSpec B f hsmall P})

/-- The comparison map from the finite-support direct image to the proper-support direct image
over one étale test object. -/
public def finiteSupportComparisonApp (V : SmallEtale B Y.obj Y.property) :
    (P.val.obj F).obj (op V) ⟶ (properSupportSheaf B f F).obj.obj (op V) := by
  letI := hsmall V
  exact eqToHom (P.property.obj_eq F V) ≫ finiteSupportColimitToProper B f F V

/-- On the colimit generator of an eligible support the comparison map is the leg of the cocone
at that stage. -/
public theorem finiteSupportComparisonApp_ι (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) :
    letI := hsmall V
    colimit.ι (finiteSupportDiagram B f F V) E ≫ eqToHom (P.property.obj_eq F V).symm ≫
        finiteSupportComparisonApp B f F hsmall P V =
      (finiteSupportCocone B f F V).ι.app E := by
  dsimp only [finiteSupportComparisonApp]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact finiteSupportColimitToProper_ι B f F V E

end Comparison



end AlgebraicGeometry.SmallEtale

end
