module

public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Subterminal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleTopos
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Comparison

/-!
# Subterminal sheaves on the small étale site

A subsheaf of the final sheaf on the small étale site of a scheme `S` is represented by a
unique open subscheme of `S`: the open on which the sheaf has a section.

## Main results

* `CategoryTheory.IsSubterminal.map_of_preservesFiniteLimits`: a functor preserving finite limits
  carries subterminal objects to subterminal objects.  In particular the inverse image of a
  morphism of topoi takes a subsheaf of the final sheaf to a subsheaf of the final sheaf, which is
  how a subterminal sheaf arises in the proof of [Stacks Project, Tag 04I7]: there one pulls back
  the sheaf of an affine open of the target and asks for the open representing the result.
* `AlgebraicGeometry.existsUnique_open_of_isSubterminal` identifies the unique open subscheme
  representing a subterminal sheaf on the small étale site.

## Implementation notes

The sheaf represented by an open subscheme is the sheafification of its functor of points,
restricted from schemes over `S` to the chosen small étale site. Using the sheafification
avoids having to choose a separate object of the bounded site for the open.

The open in question is the union of the images of the étale objects carrying a section. That
family covers it, and the sections glue there because the sheaf is subterminal, so any two
agree; conversely a section over an étale object forces its image into the open.

## References

* [Stacks Project, Tag 04HV](https://stacks.math.columbia.edu/tag/04HV)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w w'

namespace CategoryTheory

open CategoryTheory.Limits

/-- **A functor preserving finite limits carries subterminal objects to subterminal objects.**

Being subterminal is the monomorphicity of the map to the terminal object, and a functor
preserving finite limits preserves both the terminal object and monomorphisms.  The intended
instance is the inverse image of a morphism of topoi, which is left exact: a subsheaf of the final
sheaf pulls back to a subsheaf of the final sheaf.  That is the first step of the passage from
[Stacks Project, Tag 04I6] to [Stacks Project, Tag 04I7], which pulls back the sheaf of an affine
open of the target and then represents the result by an open of the source through
`AlgebraicGeometry.existsUnique_open_of_isSubterminal`. -/
@[sga "4 IV 6.4.3" "Subterminal clause",
  sga "4 IV 9.2.5" "more general",
  sga "4 VIII 7.9.3" "more general"]
theorem IsSubterminal.map_of_preservesFiniteLimits {C : Type u} [Category.{v} C]
    {D : Type w} [Category.{w'} D] [HasTerminal C] (F : C ⥤ D) [PreservesFiniteLimits F]
    {X : C} (hX : IsSubterminal X) : IsSubterminal (F.obj X) := by
  have hT : IsTerminal (F.obj (⊤_ C)) := isLimitOfHasTerminalOfPreservesLimit F
  have : Mono (terminal.from X) := hX.mono_terminal_from
  have : Mono (F.map (terminal.from X)) := inferInstance
  intro Z f g
  rw [← cancel_mono (F.map (terminal.from X))]
  exact hT.hom_ext _ _

end CategoryTheory

namespace AlgebraicGeometry

private abbrev SupportIndex (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS) :=
  {U : SmallEtale B S hS // Nonempty (F.obj.obj (op U))}

private noncomputable def sheafYonedaEquiv {C : Type u} [Category.{w} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type (max (w + 1) v))]
    (U : C) (F : Sheaf J (Type (max (w + 1) v))) :
    Equiv (((presheafToSheaf J (Type (max (w + 1) v))).obj
      (uliftYoneda.{max (w + 1) v}.obj U)) ⟶ F)
      (F.obj.obj (op U)) :=
  ((sheafificationAdjunction J (Type (max (w + 1) v))).homEquiv
    (uliftYoneda.{max (w + 1) v}.obj U) F).trans
      (uliftYonedaEquiv.{max (w + 1) v})

private theorem section_subsingleton {C : Type u} [Category.{w} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type (max (w + 1) v))]
    (F : Sheaf J (Type (max (w + 1) v)))
    (hF : IsSubterminal F) (U : C) : Subsingleton (F.obj.obj (op U)) :=
  ⟨fun _ _ => (sheafYonedaEquiv J U F).symm.injective (IsSubterminal.def.mp hF _ _)⟩

/-- The structure morphism of an object of the small étale site of `S`, as a morphism of
schemes to `S`. -/
public def smallEtaleMap (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : SmallEtale B S hS) :
    (SmallEtale.toScheme B S hS).obj U ⟶ S :=
  B.inclusion.map U.obj.hom

/-- The image in `S` of an object of the small étale site, as an open subset.

The structure morphism is étale, hence flat and locally of finite presentation, hence an open
map, so its set-theoretic image is open. -/
public noncomputable def smallEtaleImageOpen (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (U : SmallEtale B S hS) : S.Opens := by
  let f := smallEtaleMap B S hS U
  refine ⟨Set.range f.base, ?_⟩
  have : Etale f := U.property
  exact f.isOpenMap.isOpen_range

/-- The image open of an object of the small étale site is the range of its structure
morphism. -/
@[simp]
public theorem smallEtaleImageOpen_coe (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (U : SmallEtale B S hS) :
    (smallEtaleImageOpen B S hS U : Set S) = Set.range (smallEtaleMap B S hS U).base :=
  rfl

private noncomputable def supportOpen (B : BigEtaleSite.{u})
  (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS) : S.Opens :=
  ⨆ i : SupportIndex B S hS F,
    smallEtaleImageOpen B S hS i.1

private theorem supportOpen_contains_map_range (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS)
    (U : SmallEtale B S hS) (s : F.obj.obj (op U)) :
    Set.range (smallEtaleMap B S hS U).base ⊆ (supportOpen B S hS F : Set S) :=
  fun _ hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, ⟨s⟩⟩, hx⟩

private theorem open_size_lt (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (W : S.Opens) :
    (W : Scheme).size < B.cutoff :=
  Scheme.size_lt_of_isOpenImmersion W.ι hS

private noncomputable def smallEtaleOpenObject (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (W : S.Opens) :
    SmallEtale B S hS := by
  let Wobj : B.Scheme := B.obj (W : Scheme) (open_size_lt B S hS W)
  let f : Wobj ⟶ B.obj S hS := ObjectProperty.homMk W.ι
  refine ⟨Over.mk f, ?_⟩
  change Etale W.ι
  infer_instance

private theorem smallEtaleOpenObject_range (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (W : S.Opens) :
    Set.range (smallEtaleMap B S hS (smallEtaleOpenObject B S hS W)).base =
      (W : Set S) := by
  show Set.range W.ι.base = (W : Set S)
  simp only [Scheme.Opens.range_ι]

private noncomputable abbrev supportBaseObject (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS) : B.Scheme :=
  B.obj (supportOpen B S hS F : Scheme) (open_size_lt B S hS (supportOpen B S hS F))

private noncomputable abbrev supportObject (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS) :
    SmallEtale B S hS := by
  let W := supportOpen B S hS F
  let Wobj : B.Scheme := supportBaseObject B S hS F
  let f : Wobj ⟶ B.obj S hS := ObjectProperty.homMk W.ι
  refine ⟨Over.mk f, ?_⟩
  change Etale W.ι
  infer_instance

private theorem supportObject_underlying_eq (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS) :
    B.inclusion.obj (supportObject B S hS F).obj.left = supportOpen B S hS F :=
  rfl

/-- A morphism over `S` from an object of the small étale site to an open `W`, when its image
lies in `W`. -/
private noncomputable def smallEtaleToOpen (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (W : S.Opens)
    (U : SmallEtale B S hS) (h : Set.range (smallEtaleMap B S hS U).base ⊆ (W : Set S)) :
    Over.mk (smallEtaleMap B S hS U) ⟶ Over.mk W.ι :=
  have hrange : Set.range (smallEtaleMap B S hS U).base ⊆ Set.range W.ι.base := by
    simpa only [Scheme.Opens.range_ι] using h
  Over.homMk (IsOpenImmersion.lift W.ι _ hrange) (IsOpenImmersion.lift_fac W.ι _ hrange)

private noncomputable abbrev supportSectionArrow (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS)
    (U : SmallEtale B S hS) (s : F.obj.obj (op U)) :
    Over.mk (smallEtaleMap B S hS U) ⟶ Over.mk (supportOpen B S hS F).ι :=
  smallEtaleToOpen B S hS _ U (supportOpen_contains_map_range B S hS F U s)

private noncomputable abbrev supportSchemeCoverFamily (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS) :
    PreZeroHypercover.{u + 1} (supportOpen B S hS F : Scheme) where
  I₀ := SupportIndex B S hS F
  X i := (SmallEtale.toScheme B S hS).obj i.1
  f i := (supportSectionArrow B S hS F i.1 (Classical.choice i.2)).left

private theorem supportSchemeCoverFamily_etale (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS) :
    (supportSchemeCoverFamily B S hS F).presieve₀ ∈
      Scheme.etalePrecoverage (supportOpen B S hS F) := by
  show Presieve.ofArrows _ _ ∈
    Scheme.precoverage (@Etale : MorphismProperty Scheme) (supportOpen B S hS F)
  refine (Scheme.ofArrows_mem_precoverage_iff
    (@Etale : MorphismProperty Scheme)).2 ⟨fun x => ?_, fun i => ?_⟩
  · obtain ⟨i, hx⟩ := (TopologicalSpace.Opens.mem_iSup.mp x.property)
    change x.val ∈ Set.range (smallEtaleMap B S hS i.1).base at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨i, ⟨y, ?_⟩⟩
    apply Subtype.ext
    let a := supportSectionArrow B S hS F i.1 (Classical.choice i.2)
    have hfac : a.left ≫ (supportOpen B S hS F).ι = smallEtaleMap B S hS i.1 := Over.w a
    have hpoint := congrArg (fun g => g y) hfac
    change (a.left y).val = smallEtaleMap B S hS i.1 y at hpoint
    exact hpoint.trans hy
  · let a := supportSectionArrow B S hS F i.1 (Classical.choice i.2)
    have hW : Etale (supportOpen B S hS F).ι := inferInstance
    have hfac : a.left ≫ (supportOpen B S hS F).ι = smallEtaleMap B S hS i.1 := Over.w a
    apply MorphismProperty.of_postcomp @Etale a.left (supportOpen B S hS F).ι hW
    rw [hfac]
    exact i.1.property

private noncomputable abbrev supportFamilyMap (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS)
    (i : SupportIndex B S hS F) :
    i.1.obj.left ⟶ supportBaseObject B S hS F := by
  let s := Classical.choice i.2
  exact ObjectProperty.homMk
    (supportSectionArrow B S hS F i.1 s).left

private noncomputable abbrev supportCoverFamily (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS) :
    PreZeroHypercover.{u + 1} (supportBaseObject B S hS F) where
  I₀ := SupportIndex B S hS F
  X i := i.1.obj.left
  f i := supportFamilyMap B S hS F i

private theorem supportCoverFamily_etale (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS) :
    IsEtaleCovering
      ⟨supportBaseObject B S hS F, supportCoverFamily B S hS F⟩ := by
  show ((supportCoverFamily B S hS F).map B.inclusion).presieve₀ ∈
    Scheme.etalePrecoverage _
  exact supportSchemeCoverFamily_etale B S hS F

private noncomputable def supportCoveringRep (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS) : Covering B.Scheme :=
  Classical.choose (B.exists_covering_rep
    ⟨supportBaseObject B S hS F, supportCoverFamily B S hS F⟩
    (supportCoverFamily_etale B S hS F))

private theorem supportCoveringRep_isCovering (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS) :
    B.IsCovering (supportCoveringRep B S hS F) :=
  (Classical.choose_spec (B.exists_covering_rep
    ⟨supportBaseObject B S hS F, supportCoverFamily B S hS F⟩
    (supportCoverFamily_etale B S hS F))).1

private theorem supportCoveringRep_targetEq (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS) :
    supportBaseObject B S hS F = (supportCoveringRep B S hS F).1 :=
  Classical.choose ((Classical.choose_spec (B.exists_covering_rep
    ⟨supportBaseObject B S hS F, supportCoverFamily B S hS F⟩
    (supportCoverFamily_etale B S hS F))).2)

private theorem supportCoveringRep_comb (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS) :
    (supportCoveringRep_targetEq B S hS F ▸ supportCoverFamily B S hS F).CombinatoriallyEquivalent
      (supportCoveringRep B S hS F).2 :=
  Classical.choose_spec ((Classical.choose_spec (B.exists_covering_rep
    ⟨supportBaseObject B S hS F, supportCoverFamily B S hS F⟩
    (supportCoverFamily_etale B S hS F))).2)

private theorem supportCoveringRep_presieve_eq (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS) :
    (supportCoveringRep B S hS F).2.presieve₀ =
      (supportCoveringRep_targetEq B S hS F ▸
        supportCoverFamily B S hS F).presieve₀ :=
  (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent
    (supportCoveringRep_comb B S hS F)).symm

private noncomputable def supportRepSmallTarget (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS) :
    SmallEtale B S hS := by
  let h := supportCoveringRep_targetEq B S hS F
  let f : (supportCoveringRep B S hS F).1 ⟶ B.obj S hS :=
    eqToHom h.symm ≫ (supportObject B S hS F).obj.hom
  refine ⟨Over.mk f, ?_⟩
  change Etale (B.inclusion.map f)
  have : Etale (B.inclusion.map (eqToHom h.symm)) := inferInstance
  have : Etale (B.inclusion.map ((supportObject B S hS F).obj.hom)) :=
    (supportObject B S hS F).property
  rw [Functor.map_comp]
  infer_instance

private noncomputable def supportRepSmallComponent (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS)
    (i : (supportCoveringRep B S hS F).2.I₀) :
    SmallEtale B S hS := by
  let h := supportCoveringRep_targetEq B S hS F
  let E := (supportCoveringRep B S hS F).2
  let f : E.X i ⟶ B.obj S hS :=
    E.f i ≫ eqToHom h.symm ≫
      (supportObject B S hS F).obj.hom
  refine ⟨Over.mk f, ?_⟩
  change Etale (B.inclusion.map f)
  have hE := (supportCoveringRep_isCovering B S hS F).1
  change ((supportCoveringRep B S hS F).2.map B.inclusion).presieve₀ ∈
    Scheme.etalePrecoverage _ at hE
  have : Etale (B.inclusion.map (E.f i)) :=
    ((Scheme.ofArrows_mem_precoverage_iff (@Etale : MorphismProperty Scheme)).1 hE).2 i
  have : Etale (B.inclusion.map (eqToHom h.symm)) := inferInstance
  have : Etale (B.inclusion.map ((supportObject B S hS F).obj.hom)) :=
    (supportObject B S hS F).property
  change Etale ((B.inclusion.map (E.f i) ≫
    B.inclusion.map (eqToHom h.symm)) ≫
      B.inclusion.map ((supportObject B S hS F).obj.hom))
  have : Etale (B.inclusion.map (E.f i) ≫ B.inclusion.map (eqToHom h.symm)) :=
    Etale.etale_comp _ _
  exact Etale.etale_comp _ _

private noncomputable def supportRepSmallMap (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS)
  (i : (supportCoveringRep B S hS F).2.I₀) :
    supportRepSmallComponent B S hS F i ⟶ supportRepSmallTarget B S hS F := by
  let h := supportCoveringRep_targetEq B S hS F
  let E := (supportCoveringRep B S hS F).2
  exact ObjectProperty.homMk (Over.homMk (E.f i)
    (by dsimp [supportRepSmallComponent, supportRepSmallTarget, E, h]))

private noncomputable def supportRepSmallFamily (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS) :
    PreZeroHypercover (supportRepSmallTarget B S hS F) where
  I₀ := (supportCoveringRep B S hS F).2.I₀
  X i := supportRepSmallComponent B S hS F i
  f i := supportRepSmallMap B S hS F i

private theorem supportRepSmallFamily_isCovering (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS) :
    SmallEtale.IsCovering B S hS
      ⟨supportRepSmallTarget B S hS F, supportRepSmallFamily B S hS F⟩ := by
  show B.IsCovering
    ⟨(Over.forget (B.obj S hS)).obj
        ((SmallEtale.inclusion B S hS).obj
          (supportRepSmallTarget B S hS F)),
      (supportRepSmallFamily B S hS F).map
        (SmallEtale.inclusion B S hS ⋙ Over.forget (B.obj S hS))⟩
  show B.IsCovering (supportCoveringRep B S hS F)
  exact supportCoveringRep_isCovering B S hS F

private noncomputable def preZeroIndexTransportEquiv {C : Type w} [Category.{w'} C]
    {X Y : C} (h : X = Y) (E : PreZeroHypercover X) :
    (h ▸ E).I₀ ≃ E.I₀ := by
  cases h
  exact Equiv.refl _

private theorem preZeroX_transport {C : Type w} [Category.{w'} C]
    {X Y : C} (h : X = Y) (E : PreZeroHypercover X) (i : (h ▸ E).I₀) :
    (h ▸ E).X i = E.X (preZeroIndexTransportEquiv h E i) := by
  cases h
  simp [preZeroIndexTransportEquiv]

private theorem preZeroF_transport {C : Type w} [Category.{w'} C]
    {X Y : C} (h : X = Y) (E : PreZeroHypercover X) (i : (h ▸ E).I₀) :
    (h ▸ E).f i =
      eqToHom (preZeroX_transport h E i) ≫ E.f (preZeroIndexTransportEquiv h E i) ≫
        eqToHom h := by
  cases h
  cases (preZeroX_transport rfl E i)
  simp [preZeroIndexTransportEquiv, eqToHom_refl]

private noncomputable def supportRepComponentIndex (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS)
    (i : (supportCoveringRep B S hS F).2.I₀) : SupportIndex B S hS F :=
  preZeroIndexTransportEquiv (supportCoveringRep_targetEq B S hS F)
    (supportCoverFamily B S hS F) ((Classical.choose
      (supportCoveringRep_comb B S hS F).2) i)

private theorem supportRepComponentSourceEq (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS)
    (i : (supportCoveringRep B S hS F).2.I₀) :
    (supportCoveringRep B S hS F).2.X i =
      (supportCoverFamily B S hS F).X (supportRepComponentIndex B S hS F i) :=
  (Classical.choose (Classical.choose_spec (supportCoveringRep_comb B S hS F).2) i).trans
    (preZeroX_transport (supportCoveringRep_targetEq B S hS F) (supportCoverFamily B S hS F) _)

private theorem supportFamilyMap_fac (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS)
    (i : SupportIndex B S hS F) :
    supportFamilyMap B S hS F i ≫ (supportObject B S hS F).obj.hom = i.1.obj.hom := by
  apply B.inclusion.map_injective
  let s := Classical.choice i.2
  have hfac := Over.w (supportSectionArrow B S hS F i.1 s)
  show B.inclusion.map (supportFamilyMap B S hS F i) ≫
      B.inclusion.map ((supportObject B S hS F).obj.hom) = _
  simpa [supportFamilyMap, supportObject, smallEtaleMap, Functor.map_comp] using hfac

private noncomputable def supportRepComponentIso (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS)
    (i : (supportCoveringRep B S hS F).2.I₀) :
    supportRepSmallComponent B S hS F i ≅
      (supportRepComponentIndex B S hS F i).1 := by
  let h := supportCoveringRep_targetEq B S hS F
  let j := (Classical.choose (supportCoveringRep_comb B S hS F).2) i
  let idx := preZeroIndexTransportEquiv h (supportCoverFamily B S hS F) j
  have hsrc := Classical.choose (Classical.choose_spec
    (supportCoveringRep_comb B S hS F).2) i
  have hmap := Classical.choose_spec
    (Classical.choose_spec (supportCoveringRep_comb B S hS F).2) i
  let hsrc' := preZeroX_transport h (supportCoverFamily B S hS F) j
  have hcomp : (supportCoveringRep B S hS F).2.X i =
      (supportCoverFamily B S hS F).X idx :=
    hsrc.trans hsrc'
  have hmap' :
      (supportCoveringRep B S hS F).2.f i ≫ eqToHom h.symm =
        eqToHom hcomp ≫
          supportFamilyMap B S hS F idx := by
    rw [hmap, preZeroF_transport h (supportCoverFamily B S hS F) j,
      show hcomp = hsrc.trans hsrc' by rfl]
    dsimp only [idx]
    simp [supportFamilyMap, Category.assoc, eqToHom_trans, eqToHom_refl]
  have htriangle :
      eqToHom hcomp ≫ idx.1.obj.hom =
        (supportRepSmallComponent B S hS F i).obj.hom := by
    change eqToHom hcomp ≫ idx.1.obj.hom =
      (supportCoveringRep B S hS F).2.f i ≫ eqToHom h.symm ≫
        (supportObject B S hS F).obj.hom
    rw [← supportFamilyMap_fac B S hS F idx]
    change (eqToHom hcomp ≫ supportFamilyMap B S hS F idx) ≫
        (supportObject B S hS F).obj.hom =
      ((supportCoveringRep B S hS F).2.f i ≫ eqToHom h.symm) ≫
        (supportObject B S hS F).obj.hom
    exact (congrArg (fun g => g ≫ (supportObject B S hS F).obj.hom) hmap').symm
  exact ObjectProperty.isoMk _ <| Over.isoMk (eqToIso hcomp) htriangle

private theorem supportSection_on_open (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS)
    (hF : IsSubterminal F) : Nonempty
      (F.obj.obj (op (supportRepSmallTarget B S hS F))) := by
  let E := supportRepSmallFamily B S hS F
  have hpre : E.presieve₀ ∈ SmallEtale.precoverage B S hS
      (supportRepSmallTarget B S hS F) :=
    ⟨E, rfl, supportRepSmallFamily_isCovering B S hS F⟩
  have hsf : Presieve.IsSheafFor F.obj E.presieve₀ :=
    (Presieve.isSheafFor_iff_generate E.presieve₀).2 <|
      (isSheaf_iff_isSheaf_of_type
        (SmallEtale.topology B S hS) F.obj).1 F.property
        (Sieve.generate E.presieve₀) (Precoverage.generate_mem_toGrothendieck hpre)
  let localSection : (i : E.I₀) → F.obj.obj (op (E.X i)) := fun i =>
    F.obj.map (supportRepComponentIso B S hS F i).hom.op
      (Classical.choice (supportRepComponentIndex B S hS F i).2)
  let family : Presieve.FamilyOfElements F.obj E.presieve₀ := fun {V} f hf => by
    have hm : ∃ i, ∃ e : V ≅ E.X i, e.hom ≫ E.f i = f := by
      cases hf with
      | mk i => exact ⟨i, Iso.refl _, rfl⟩
    let i := Classical.choose hm
    let e := Classical.choose (Classical.choose_spec hm)
    exact F.obj.map e.hom.op (localSection i)
  have hcompatible : family.Compatible := by
    intro _ _ T _ _ _ _ _ _ _
    exact (section_subsingleton.{_, v, _}
      (SmallEtale.topology B S hS) F hF T).elim _ _
  exact ⟨hsf.amalgamate family hcompatible⟩

private noncomputable def supportRepTargetIso (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS) :
    supportRepSmallTarget B S hS F ≅ supportObject B S hS F := by
  let h := supportCoveringRep_targetEq B S hS F
  refine ObjectProperty.isoMk _ <| Over.isoMk (eqToIso h.symm) ?_
  rfl

private theorem supportOpen_has_section (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS)
    (hF : IsSubterminal F) : Nonempty
      (F.obj.obj (op (supportObject B S hS F))) :=
  ⟨F.obj.map (supportRepTargetIso B S hS F).inv.op
    (Classical.choice (supportSection_on_open B S hS F hF))⟩

/-- The presheaf on the small étale site of `S` represented by an open subscheme `W` of `S`,
with its sections raised to a fixed universe.

An open subscheme of `S` is an object of the big étale slice over `S`, and this is the
restriction to the small étale site of the presheaf it represents there. -/
public noncomputable abbrev openRepresentable.{u₁, v₁}
    (B : BigEtaleSite.{u₁}) (S : Scheme.{u₁}) (hS : B.Contains S)
    (W : S.Opens) :
    (SmallEtale B S hS)ᵒᵖ ⥤ Type (max (u₁ + 1) v₁) :=
  ((SmallEtale.inclusion B S hS ⋙
    Over.post (X := B.obj S hS) B.inclusion).op ⋙
      uliftYoneda.{max (u₁ + 1) v₁}.obj
        (Over.mk W.ι))

private noncomputable abbrev supportRepresentable.{u₁, v₁}
    (B : BigEtaleSite.{u₁}) (S : Scheme.{u₁}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u₁, max (u₁ + 1) v₁} B S hS) :
    (SmallEtale B S hS)ᵒᵖ ⥤ Type (max (u₁ + 1) v₁) :=
  openRepresentable.{u₁, v₁} B S hS (supportOpen B S hS F)

/-- The presheaf represented by an open subscheme of `S` is a sheaf on the small étale site.

The fpqc topology on the schemes over `S` is subcanonical, so a representable presheaf is an
fpqc sheaf, and an fpqc sheaf restricts to a sheaf on the chosen small étale site. -/
public theorem openRepresentable_isSheaf.{u₁, v₁} (B : BigEtaleSite.{u₁})
    (S : Scheme.{u₁}) (hS : B.Contains S)
    (W : S.Opens) :
    Presheaf.IsSheaf (SmallEtale.topology B S hS)
      (openRepresentable.{u₁, v₁} B S hS W) := by
  let P : (Over S)ᵒᵖ ⥤ Type (max (u₁ + 1) v₁) :=
    uliftYoneda.{max (u₁ + 1) v₁}.obj (Over.mk W.ι)
  have hP : Presheaf.IsSheaf (Scheme.fpqcTopology.over S) P :=
    (isSheaf_iff_isSheaf_of_type (Scheme.fpqcTopology.over S) P).2
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable P)
  exact isSheaf_chosenSmallEtale_of_isSheaf_fpqc B S hS P hP

private noncomputable def representableArrowToSupportObject
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS)
    (U : SmallEtale B S hS)
    (x : (supportRepresentable B S hS F).obj (op U)) :
    U ⟶ supportObject B S hS F := by
  change ULift (Over.mk (smallEtaleMap B S hS U) ⟶
    Over.mk (supportOpen B S hS F).ι) at x
  let a := x.down
  let hobj := supportObject_underlying_eq B S hS F
  let cast : (supportOpen B S hS F : Scheme) ⟶
      B.inclusion.obj (supportObject B S hS F).obj.left := eqToHom hobj.symm
  let g' : B.inclusion.obj U.obj.left ⟶
      B.inclusion.obj (supportObject B S hS F).obj.left := a.left ≫ cast
  let g : U.obj.left ⟶ supportBaseObject B S hS F :=
    B.inclusion.preimage g'
  have hg : g ≫ (supportObject B S hS F).obj.hom = U.obj.hom := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, B.inclusion.map_preimage]
    change (a.left ≫ cast) ≫
        B.inclusion.map (supportObject B S hS F).obj.hom =
      B.inclusion.map U.obj.hom
    rw [Category.assoc, show cast ≫ B.inclusion.map (supportObject B S hS F).obj.hom =
        (supportOpen B S hS F).ι by simp [cast, supportObject, supportBaseObject]]
    simpa [smallEtaleMap] using a.w
  exact ObjectProperty.homMk (Over.homMk g hg)

private theorem representableArrow_map (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS)
    {U V : SmallEtale B S hS} (f : op U ⟶ op V)
    (x : (supportRepresentable B S hS F).obj (op U)) :
    representableArrowToSupportObject B S hS F V
      ((supportRepresentable B S hS F).map f x) =
      f.unop ≫ representableArrowToSupportObject B S hS F U x := by
  have hobj := supportObject_underlying_eq B S hS F
  let cast : (supportOpen B S hS F : Scheme) ⟶
      B.inclusion.obj (supportObject B S hS F).obj.left := eqToHom hobj.symm
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  show B.inclusion.preimage (X := V.obj.left)
      (Y := supportBaseObject B S hS F)
      (B.inclusion.map (Over.Hom.left f.unop.hom) ≫
        (Over.Hom.left x.down ≫ cast)) =
    Over.Hom.left f.unop.hom ≫
      B.inclusion.preimage (X := U.obj.left)
        (Y := supportBaseObject B S hS F) (Over.Hom.left x.down ≫ cast)
  calc
    _ = B.inclusion.preimage (B.inclusion.map (Over.Hom.left f.unop.hom)) ≫
          B.inclusion.preimage (Over.Hom.left x.down ≫ cast) :=
      B.inclusion.preimage_comp _ _
    _ = _ := by simp only [Functor.preimage_map]

private noncomputable def supportRepresentableToSheaf
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS)
    (s : F.obj.obj (op (supportObject B S hS F))) :
    supportRepresentable B S hS F ⟶ F.obj := by
  refine ⟨fun U => ↾fun x => F.obj.map
      (representableArrowToSupportObject B S hS F U.unop x).op s, ?_⟩
  intro U V f
  ext x
  symm
  change F.obj.map f
      (F.obj.map (representableArrowToSupportObject B S hS F U.unop x).op s) =
    F.obj.map (representableArrowToSupportObject B S hS F V.unop
      ((supportRepresentable B S hS F).map f x)).op s
  rw [← Functor.map_comp_apply]
  have hcomp := congrArg Quiver.Hom.op (representableArrow_map B S hS F f x)
  rw [op_comp, Quiver.Hom.op_unop] at hcomp
  rw [← hcomp]

private noncomputable def sheafToSupportRepresentable
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS) :
    F.obj ⟶ supportRepresentable B S hS F := by
  refine ⟨fun U => ↾fun s =>
    ULift.up (supportSectionArrow B S hS F U.unop s), ?_⟩
  intro U V f
  ext s
  apply ULift.ext
  apply Over.OverMorphism.ext
  apply (cancel_mono (supportOpen B S hS F).ι).1
  let G := SmallEtale.inclusion B S hS ⋙
    Over.post (X := B.obj S hS) B.inclusion
  have hU := Over.w (supportSectionArrow B S hS F U.unop s)
  have hV := Over.w
    (supportSectionArrow B S hS F V.unop (F.obj.map f s))
  have hf : (G.map f.unop).left ≫ smallEtaleMap B S hS U.unop =
      smallEtaleMap B S hS V.unop := by
    change B.inclusion.map f.unop.hom.left ≫
        B.inclusion.map U.unop.obj.hom = B.inclusion.map V.unop.obj.hom
    rw [← Functor.map_comp]
    exact congrArg B.inclusion.map (Over.w f.unop.hom)
  change (supportSectionArrow B S hS F V.unop (F.obj.map f s)).left ≫
      (supportOpen B S hS F).ι =
    (G.map f.unop).left ≫
      ((supportSectionArrow B S hS F U.unop s).left ≫
        (supportOpen B S hS F).ι)
  exact hV.trans <| hf.symm.trans <|
    congrArg (fun g => (G.map f.unop).left ≫ g) hU.symm

private theorem supportRepresentable_sections_subsingleton
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS)
    (U : SmallEtale B S hS) :
    Subsingleton ((supportRepresentable B S hS F).obj (op U)) := by
  show Subsingleton (ULift
    (Over.mk (smallEtaleMap B S hS U) ⟶ Over.mk (supportOpen B S hS F).ι))
  refine ⟨fun x y => ?_⟩
  apply ULift.ext
  apply Over.OverMorphism.ext
  apply (cancel_mono (supportOpen B S hS F).ι).1
  exact (Over.w x.down).trans (Over.w y.down).symm

private noncomputable def chosenPresheafToSheafIso
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ Type (max (u + 1) v))
    (hP : Presheaf.IsSheaf (SmallEtale.topology B S hS) P) :
    (⟨P, hP⟩ : smallEtaleTopos.{u, max (u + 1) v} B S hS) ≅
      (presheafToSheaf (SmallEtale.topology B S hS)
        (Type (max (u + 1) v))).obj P := by
  apply ObjectProperty.isoMk
  letI : IsIso (toSheafify (SmallEtale.topology B S hS) P) :=
    isIso_toSheafify (SmallEtale.topology B S hS) hP
  exact asIso (toSheafify (SmallEtale.topology B S hS) P)

private theorem openRepresentable_range_subset
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (W : S.Opens) (U : SmallEtale B S hS)
    (x : (openRepresentable B S hS W).obj (op U)) :
    Set.range (smallEtaleMap B S hS U).base ⊆ (W : Set S) := by
  change ULift (Over.mk (smallEtaleMap B S hS U) ⟶ Over.mk W.ι) at x
  rintro _ ⟨z, rfl⟩
  have hcomm := Over.w x.down
  change x.down.left ≫ W.ι = smallEtaleMap B S hS U at hcomm
  have hpt : W.ι (x.down.left z) = (smallEtaleMap B S hS U) z := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun f => f z) hcomm
  show (smallEtaleMap B S hS U).base z ∈ W
  rw [← hpt]
  exact (x.down.left z).property

private theorem openRepresentable_nonempty_of_range_subset
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (W : S.Opens) (U : SmallEtale B S hS)
    (h : Set.range (smallEtaleMap B S hS U).base ⊆ (W : Set S)) :
    Nonempty ((openRepresentable B S hS W).obj (op U)) := by
  exact ⟨ULift.up (smallEtaleToOpen B S hS W U h)⟩

private noncomputable def supportSheafificationIso
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS)
    (hF : IsSubterminal F) :
    F ≅ (presheafToSheaf (SmallEtale.topology B S hS)
      (Type (max (u + 1) v))).obj (supportRepresentable B S hS F) := by
  let P := supportRepresentable B S hS F
  let hP := openRepresentable_isSheaf B S hS (supportOpen B S hS F)
  let α : F.obj ⟶ P := sheafToSupportRepresentable B S hS F
  let β : P ⟶ F.obj := supportRepresentableToSheaf B S hS F
    (Classical.choice (supportOpen_has_section B S hS F hF))
  have hαβ : α ≫ β = 𝟙 _ := by
    ext U x
    exact (section_subsingleton.{_, v, _} (SmallEtale.topology B S hS)
      F hF U.unop).elim _ _
  have hβα : β ≫ α = 𝟙 _ := by
    ext U x
    exact (supportRepresentable_sections_subsingleton B S hS F U.unop).elim _ _
  let e : F ≅ ⟨P, hP⟩ := ObjectProperty.isoMk _ {
    hom := α
    inv := β
    hom_inv_id := hαβ
    inv_hom_id := hβα
  }
  exact e.trans (chosenPresheafToSheafIso B S hS P hP)

/-- A subterminal sheaf on the small étale site is represented by a unique open
subscheme of the base. -/
@[stacks 04HV]
public theorem existsUnique_open_of_isSubterminal
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max (u + 1) v} B S hS)
    (hF : IsSubterminal F) :
    ∃! W : S.Opens,
      Nonempty (F ≅
        (presheafToSheaf (SmallEtale.topology B S hS)
          (Type (max (u + 1) v))).obj
          ((SmallEtale.inclusion B S hS ⋙
            Over.post (X := B.obj S hS) B.inclusion).op ⋙
            uliftYoneda.{max (u + 1) v}.obj (Over.mk W.ι))) := by
  refine ⟨supportOpen B S hS F, ⟨supportSheafificationIso B S hS F hF⟩, ?_⟩
  rintro W ⟨e⟩
  let P := openRepresentable B S hS W
  let hP := openRepresentable_isSheaf B S hS W
  let e' := e.trans (chosenPresheafToSheafIso B S hS P hP).symm
  apply le_antisymm
  · intro x hx
    let U := smallEtaleOpenObject B S hS W
    have hrange : Set.range (smallEtaleMap B S hS U).base = (W : Set S) :=
      smallEtaleOpenObject_range B S hS W
    obtain ⟨p⟩ := openRepresentable_nonempty_of_range_subset B S hS W U hrange.subset
    exact supportOpen_contains_map_range B S hS F U (e'.inv.hom.app (op U) p)
      (hrange.symm.subset hx)
  · refine iSup_le fun i => ?_
    obtain ⟨s⟩ := i.2
    exact openRepresentable_range_subset B S hS W i.1 (e'.hom.hom.app (op i.1) s)

end AlgebraicGeometry

end
