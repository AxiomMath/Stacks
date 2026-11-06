module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubterminalSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Subterminal sheaves on the small étale site, in every sections universe

The sections universe of `StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubterminalSheaves` is
`max (u + 1) v`. The declarations here generalize it to every sections universe `max u v`, so
that `v := u` reaches the universe `u` of the sections of the small étale ringed topos. The
generalized forms of declarations of that module carry a prime.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w w'

namespace CategoryTheory

/-! ### Subterminal objects: two general criteria

The two facts about `CategoryTheory.IsSubterminal` that the representability of a subterminal
sheaf is used through, neither of which is in Mathlib. -/

/-- **A functor to types all of whose values are subsingletons is subterminal.** Two morphisms
into it agree because they agree in every component. -/
public theorem isSubterminal_of_subsingleton_obj {D : Type*} [Category D] (P : D ⥤ Type w)
    (h : ∀ X : D, Subsingleton (P.obj X)) : IsSubterminal P := by
  intro Q α β
  ext X x
  exact (h X).elim _ _

/-- **A left-exact functor carries a subterminal object to a subterminal object.** The morphism
from a subterminal object to a terminal object is a monomorphism, a functor preserving finite
limits preserves both the terminal object and that monomorphism, and a monomorphism to a
terminal object exhibits its source as subterminal. -/
@[sga "4 IV 6.4.3" "Subterminal clause"]
public theorem IsSubterminal.map {C : Type*} [Category C] {D : Type*} [Category D] {A : C}
    (hA : IsSubterminal A) {T : C} (hT : Limits.IsTerminal T) (G : C ⥤ D)
    [Limits.PreservesFiniteLimits G] : IsSubterminal (G.obj A) := by
  have hGT : Limits.IsTerminal (G.obj T) := hT.isTerminalObj G
  have h1 : Mono (hT.from A) := hA.mono_isTerminal_from hT
  have h2 : Mono (hGT.from (G.obj A)) := by
    rw [hGT.hom_ext (hGT.from (G.obj A)) (G.map (hT.from A))]
    exact G.map_mono _
  exact isSubterminal_of_mono_isTerminal_from hGT

/-- **A subterminal object admitting a morphism from a terminal object is terminal.** The given
morphism and the morphism to the terminal object are mutually inverse: one composite is forced
by terminality, the other by subterminality. -/
public def IsSubterminal.isTerminal {C : Type*} [Category C] {A T : C} (hA : IsSubterminal A)
    (hT : Limits.IsTerminal T) (s : T ⟶ A) : Limits.IsTerminal A :=
  hT.ofIso
    { hom := s
      inv := hT.from A
      hom_inv_id := hT.hom_ext _ _
      inv_hom_id := hA _ _ }

end CategoryTheory

namespace AlgebraicGeometry

/-- **Presheaves of types on the small étale site of `S` admit a left exact sheafification, in
every universe `max u v` at or above that of the schemes.** This generalizes
`AlgebraicGeometry.SmallEtale.hasSheafify_type`, which covers the universe `u + 1` of the objects
of the site only.

The sections universe of the small étale ringed topos `AlgebraicGeometry.smallEtaleRingedSite` is
`u`, one below the universe of the objects of the site, and so is not covered by Mathlib's
unconditional instance. What bridges the gap is `CategoryTheory.hasSheafifyEssentiallySmallSite`
fed with `AlgebraicGeometry.SmallEtale.essentiallySmall`: on a `u`-small model of the site the
covering sieves of an object form a `u`-small type, so the plus construction converges for
`Type w` sections for every `w ≥ u`. -/
public instance (priority := low) SmallEtale.hasSheafify_type' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    HasSheafify (SmallEtale.topology B S hS) (Type (max u v)) :=
  hasSheafifyEssentiallySmallSite.{u} _ _

private abbrev SupportIndex' (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS) :=
  {U : SmallEtale B S hS // Nonempty (F.obj.obj (op U))}

private noncomputable def sheafYonedaEquiv' {C : Type u} [Category.{w} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type (max w v))]
    (U : C) (F : Sheaf J (Type (max w v))) :
    Equiv (((presheafToSheaf J (Type (max w v))).obj
      (uliftYoneda.{max w v}.obj U)) ⟶ F)
      (F.obj.obj (op U)) :=
  ((sheafificationAdjunction J (Type (max w v))).homEquiv
    (uliftYoneda.{max w v}.obj U) F).trans
      (uliftYonedaEquiv.{max w v})

private theorem section_subsingleton' {C : Type u} [Category.{w} C]
    (J : GrothendieckTopology C) (F : Sheaf J (Type (max w v)))
    [HasWeakSheafify J (Type (max w v))]
    (hF : IsSubterminal F) (U : C) : Subsingleton (F.obj.obj (op U)) :=
  ⟨fun _ _ => (sheafYonedaEquiv' J U F).symm.injective (hF _ _)⟩

private noncomputable def supportOpen' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS) : S.Opens :=
  ⨆ i : SupportIndex' B S hS F,
    smallEtaleImageOpen B S hS i.1

private theorem supportOpen_contains_map_range' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS)
    (U : SmallEtale B S hS) (s : F.obj.obj (op U)) :
    Set.range (smallEtaleMap B S hS U).base ⊆ (supportOpen' B S hS F : Set S) :=
  fun _ hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, ⟨s⟩⟩, hx⟩

/-- **Every open subscheme of `S` is the image of an object of the small étale site of `S`**,
namely of the open subscheme itself: an open immersion is étale and an open subscheme of a
scheme below the size cutoff is again below it. -/
public theorem exists_smallEtale_range_eq (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (W : S.Opens) :
    ∃ U : SmallEtale B S hS,
      Set.range (smallEtaleMap B S hS U).base = (W : Set S) :=
  ⟨⟨Over.mk (ObjectProperty.homMk W.ι :
      B.obj (W : Scheme) (AlgebraicGeometry.Scheme.size_lt_of_isOpenImmersion W.ι hS) ⟶
        B.obj S hS), show Etale W.ι from inferInstance⟩,
    by change Set.range W.ι.base = (W : Set S); simp only [Scheme.Opens.range_ι]⟩

private noncomputable abbrev supportBaseObject' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS) : B.Scheme :=
  B.obj (supportOpen' B S hS F : Scheme)
    (AlgebraicGeometry.Scheme.size_lt_of_isOpenImmersion (supportOpen' B S hS F).ι hS)

private noncomputable abbrev supportObject' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS) :
    SmallEtale B S hS := by
  let W := supportOpen' B S hS F
  let Wobj : B.Scheme := supportBaseObject' B S hS F
  let f : Wobj ⟶ B.obj S hS := ObjectProperty.homMk W.ι
  refine ⟨Over.mk f, ?_⟩
  change Etale W.ι
  infer_instance

private theorem supportObject_underlying_eq' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS) :
    B.inclusion.obj (supportObject' B S hS F).obj.left = supportOpen' B S hS F :=
  rfl

/-- A morphism over `S` into an open subscheme `W`, from a scheme whose image lies in `W`. -/
private noncomputable def overHomOfRangeSubset {X S : Scheme.{u}} (f : X ⟶ S) (W : S.Opens)
    (h : Set.range f.base ⊆ (W : Set S)) : Over.mk f ⟶ Over.mk W.ι :=
  have hrange : Set.range f.base ⊆ Set.range W.ι.base := by
    simpa only [Scheme.Opens.range_ι] using h
  Over.homMk (IsOpenImmersion.lift W.ι f hrange) (IsOpenImmersion.lift_fac W.ι f hrange)

private noncomputable def supportSectionArrow' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS)
    (U : SmallEtale B S hS) (s : F.obj.obj (op U)) :
    Over.mk (smallEtaleMap B S hS U) ⟶ Over.mk (supportOpen' B S hS F).ι :=
  overHomOfRangeSubset _ _ (supportOpen_contains_map_range' B S hS F U s)

private noncomputable abbrev supportSchemeCoverFamily' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS) :
    PreZeroHypercover.{u + 1} (supportOpen' B S hS F : Scheme) where
  I₀ := SupportIndex' B S hS F
  X i := (SmallEtale.toScheme B S hS).obj i.1
  f i := (supportSectionArrow' B S hS F i.1 (Classical.choice i.2)).left

private theorem supportSchemeCoverFamily_etale' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS) :
    (supportSchemeCoverFamily' B S hS F).presieve₀ ∈
      Scheme.etalePrecoverage (supportOpen' B S hS F) := by
  show Presieve.ofArrows _ _ ∈
    Scheme.precoverage (@Etale : MorphismProperty Scheme) (supportOpen' B S hS F)
  apply (Scheme.ofArrows_mem_precoverage_iff
    (@Etale : MorphismProperty Scheme)).2
  have hfac : ∀ i : SupportIndex' B S hS F,
      (supportSectionArrow' B S hS F i.1 (Classical.choice i.2)).left ≫
        (supportOpen' B S hS F).ι = smallEtaleMap B S hS i.1 :=
    fun i => Over.w _
  constructor
  · intro x
    obtain ⟨i, hx⟩ := (TopologicalSpace.Opens.mem_iSup.mp x.property)
    change x.val ∈ Set.range (smallEtaleMap B S hS i.1).base at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨i, ⟨y, ?_⟩⟩
    apply Subtype.ext
    have hpoint := congrArg (fun g => g y) (hfac i)
    exact hpoint.trans hy
  · intro i
    have hW : Etale (supportOpen' B S hS F).ι := inferInstance
    apply MorphismProperty.of_postcomp @Etale
      (supportSectionArrow' B S hS F i.1 (Classical.choice i.2)).left
      (supportOpen' B S hS F).ι hW
    rw [hfac i]
    exact i.1.property

private noncomputable abbrev supportFamilyMap' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS)
    (i : SupportIndex' B S hS F) :
    i.1.obj.left ⟶ supportBaseObject' B S hS F := by
  let s := Classical.choice i.2
  exact ObjectProperty.homMk
    (supportSectionArrow' B S hS F i.1 s).left

private noncomputable abbrev supportCoverFamily' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS) :
    PreZeroHypercover.{u + 1} (supportBaseObject' B S hS F) where
  I₀ := SupportIndex' B S hS F
  X i := i.1.obj.left
  f i := supportFamilyMap' B S hS F i

private theorem supportCoverFamily_etale' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS) :
    IsEtaleCovering
      ⟨supportBaseObject' B S hS F, supportCoverFamily' B S hS F⟩ := by
  show ((supportCoverFamily' B S hS F).map B.inclusion).presieve₀ ∈
    Scheme.etalePrecoverage _
  exact supportSchemeCoverFamily_etale' B S hS F

private noncomputable def supportCoveringRep' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS) : Covering B.Scheme :=
  Classical.choose (B.exists_covering_rep
    ⟨supportBaseObject' B S hS F, supportCoverFamily' B S hS F⟩
    (supportCoverFamily_etale' B S hS F))

private theorem supportCoveringRep_isCovering' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS) :
    B.IsCovering (supportCoveringRep' B S hS F) :=
  (Classical.choose_spec (B.exists_covering_rep
    ⟨supportBaseObject' B S hS F, supportCoverFamily' B S hS F⟩
    (supportCoverFamily_etale' B S hS F))).1

private theorem supportCoveringRep_targetEq' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS) :
    supportBaseObject' B S hS F = (supportCoveringRep' B S hS F).1 :=
  Classical.choose ((Classical.choose_spec (B.exists_covering_rep
    ⟨supportBaseObject' B S hS F, supportCoverFamily' B S hS F⟩
    (supportCoverFamily_etale' B S hS F))).2)

private theorem supportCoveringRep_comb' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS) :
    (supportCoveringRep_targetEq' B S hS F ▸ supportCoverFamily' B S hS F).CombinatoriallyEquivalent
      (supportCoveringRep' B S hS F).2 :=
  Classical.choose_spec ((Classical.choose_spec (B.exists_covering_rep
    ⟨supportBaseObject' B S hS F, supportCoverFamily' B S hS F⟩
    (supportCoverFamily_etale' B S hS F))).2)

private theorem supportCoveringRep_presieve_eq' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS) :
    (supportCoveringRep' B S hS F).2.presieve₀ =
      (supportCoveringRep_targetEq' B S hS F ▸
        supportCoverFamily' B S hS F).presieve₀ :=
  (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent
    (supportCoveringRep_comb' B S hS F)).symm

private noncomputable def supportRepSmallTarget' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS) :
    SmallEtale B S hS := by
  let h := supportCoveringRep_targetEq' B S hS F
  let f : (supportCoveringRep' B S hS F).1 ⟶ B.obj S hS :=
    eqToHom h.symm ≫ (supportObject' B S hS F).obj.hom
  refine ⟨Over.mk f, ?_⟩
  change Etale (B.inclusion.map f)
  let : Etale (B.inclusion.map (eqToHom h.symm)) := inferInstance
  let : Etale (B.inclusion.map ((supportObject' B S hS F).obj.hom)) :=
    (supportObject' B S hS F).property
  rw [Functor.map_comp]
  infer_instance

private noncomputable def supportRepSmallComponent' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS)
    (i : (supportCoveringRep' B S hS F).2.I₀) :
    SmallEtale B S hS := by
  let h := supportCoveringRep_targetEq' B S hS F
  let E := (supportCoveringRep' B S hS F).2
  let f : E.X i ⟶ B.obj S hS :=
    E.f i ≫ eqToHom h.symm ≫
      (supportObject' B S hS F).obj.hom
  refine ⟨Over.mk f, ?_⟩
  change Etale (B.inclusion.map f)
  have hE : ((supportCoveringRep' B S hS F).2.map B.inclusion).presieve₀ ∈
      Scheme.etalePrecoverage _ := (supportCoveringRep_isCovering' B S hS F).1
  have : Etale (B.inclusion.map (E.f i)) :=
    ((Scheme.ofArrows_mem_precoverage_iff (@Etale : MorphismProperty Scheme)).1 hE).2 i
  let : Etale (B.inclusion.map (eqToHom h.symm)) := inferInstance
  let : Etale (B.inclusion.map ((supportObject' B S hS F).obj.hom)) :=
    (supportObject' B S hS F).property
  change Etale ((B.inclusion.map (E.f i) ≫
    B.inclusion.map (eqToHom h.symm)) ≫
      B.inclusion.map ((supportObject' B S hS F).obj.hom))
  let : Etale (B.inclusion.map (E.f i) ≫ B.inclusion.map (eqToHom h.symm)) :=
    Etale.etale_comp _ _
  exact Etale.etale_comp _ _

private noncomputable def supportRepSmallMap' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS)
    (i : (supportCoveringRep' B S hS F).2.I₀) :
    supportRepSmallComponent' B S hS F i ⟶ supportRepSmallTarget' B S hS F := by
  let h := supportCoveringRep_targetEq' B S hS F
  let E := (supportCoveringRep' B S hS F).2
  exact ObjectProperty.homMk (Over.homMk (E.f i)
    (by dsimp [supportRepSmallComponent', supportRepSmallTarget', E, h]))

private noncomputable def supportRepSmallFamily' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS) :
    PreZeroHypercover (supportRepSmallTarget' B S hS F) where
  I₀ := (supportCoveringRep' B S hS F).2.I₀
  X i := supportRepSmallComponent' B S hS F i
  f i := supportRepSmallMap' B S hS F i

private theorem supportRepSmallFamily_isCovering' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS) :
    SmallEtale.IsCovering B S hS
      ⟨supportRepSmallTarget' B S hS F, supportRepSmallFamily' B S hS F⟩ := by
  show B.IsCovering
    ⟨(Over.forget (B.obj S hS)).obj
        ((SmallEtale.inclusion B S hS).obj
          (supportRepSmallTarget' B S hS F)),
      (supportRepSmallFamily' B S hS F).map
        (SmallEtale.inclusion B S hS ⋙ Over.forget (B.obj S hS))⟩
  show B.IsCovering (supportCoveringRep' B S hS F)
  exact supportCoveringRep_isCovering' B S hS F

/-- Transport of an index of a pre-`0`-hypercover along an equality of its target, read back in
the original family. -/
private def transportedIndex {C : Type*} [Category C] {X Y : C} (h : X = Y)
    (E : PreZeroHypercover X) (i : (h ▸ E).I₀) : E.I₀ := by
  subst h
  exact i

private theorem transportedIndex_X {C : Type*} [Category C] {X Y : C} (h : X = Y)
    (E : PreZeroHypercover X) (i : (h ▸ E).I₀) :
    (h ▸ E).X i = E.X (transportedIndex h E i) := by
  subst h
  rfl

private theorem transportedIndex_f {C : Type*} [Category C] {X Y : C} (h : X = Y)
    (E : PreZeroHypercover X) (i : (h ▸ E).I₀) :
    (h ▸ E).f i =
      eqToHom (transportedIndex_X h E i) ≫ E.f (transportedIndex h E i) ≫ eqToHom h := by
  subst h
  simp only [eqToHom_refl, Category.comp_id]
  exact (Category.id_comp _).symm

private noncomputable def supportRepComponentIndex' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS)
    (i : (supportCoveringRep' B S hS F).2.I₀) : SupportIndex' B S hS F :=
  transportedIndex (supportCoveringRep_targetEq' B S hS F)
    (supportCoverFamily' B S hS F) ((Classical.choose
      (supportCoveringRep_comb' B S hS F).2) i)

private theorem supportRepComponentSourceEq' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS)
    (i : (supportCoveringRep' B S hS F).2.I₀) :
    (supportCoveringRep' B S hS F).2.X i =
      (supportCoverFamily' B S hS F).X (supportRepComponentIndex' B S hS F i) :=
  (Classical.choose (Classical.choose_spec (supportCoveringRep_comb' B S hS F).2) i).trans
    (transportedIndex_X (supportCoveringRep_targetEq' B S hS F) (supportCoverFamily' B S hS F)
      ((Classical.choose (supportCoveringRep_comb' B S hS F).2) i))

private theorem supportFamilyMap_fac' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS)
    (i : SupportIndex' B S hS F) :
    supportFamilyMap' B S hS F i ≫ (supportObject' B S hS F).obj.hom = i.1.obj.hom := by
  apply B.inclusion.map_injective
  let s := Classical.choice i.2
  have hfac := Over.w (supportSectionArrow' B S hS F i.1 s)
  show B.inclusion.map (supportFamilyMap' B S hS F i) ≫
      B.inclusion.map ((supportObject' B S hS F).obj.hom) = _
  simpa [supportFamilyMap', supportObject', smallEtaleMap, Functor.map_comp] using hfac

private noncomputable def supportRepComponentIso' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS)
    (i : (supportCoveringRep' B S hS F).2.I₀) :
    supportRepSmallComponent' B S hS F i ≅
      (supportRepComponentIndex' B S hS F i).1 := by
  let h := supportCoveringRep_targetEq' B S hS F
  let j := (Classical.choose (supportCoveringRep_comb' B S hS F).2) i
  let idx := transportedIndex h (supportCoverFamily' B S hS F) j
  have hsrc := Classical.choose (Classical.choose_spec
    (supportCoveringRep_comb' B S hS F).2) i
  have hmap := Classical.choose_spec
    (Classical.choose_spec (supportCoveringRep_comb' B S hS F).2) i
  let hsrc' := transportedIndex_X h (supportCoverFamily' B S hS F) j
  have hcomp : (supportCoveringRep' B S hS F).2.X i =
      (supportCoverFamily' B S hS F).X idx :=
    hsrc.trans hsrc'
  have hmap' :
      (supportCoveringRep' B S hS F).2.f i ≫ eqToHom h.symm =
        eqToHom hcomp ≫
          supportFamilyMap' B S hS F idx := by
    rw [hmap, transportedIndex_f h (supportCoverFamily' B S hS F) j]
    rw [show hcomp = hsrc.trans hsrc' by rfl]
    dsimp only [idx]
    simp [supportFamilyMap', Category.assoc, eqToHom_trans, eqToHom_refl]
  have htriangle :
      eqToHom hcomp ≫ idx.1.obj.hom =
        (supportRepSmallComponent' B S hS F i).obj.hom := by
    change eqToHom hcomp ≫ idx.1.obj.hom =
      (supportCoveringRep' B S hS F).2.f i ≫ eqToHom h.symm ≫
        (supportObject' B S hS F).obj.hom
    rw [← supportFamilyMap_fac' B S hS F idx]
    change (eqToHom hcomp ≫ supportFamilyMap' B S hS F idx) ≫
        (supportObject' B S hS F).obj.hom =
      ((supportCoveringRep' B S hS F).2.f i ≫ eqToHom h.symm) ≫
        (supportObject' B S hS F).obj.hom
    exact (congrArg (fun g => g ≫ (supportObject' B S hS F).obj.hom) hmap').symm
  exact ObjectProperty.isoMk _ <| Over.isoMk (eqToIso hcomp) htriangle

private theorem supportSection_on_open' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS)
    (hF : IsSubterminal F) : Nonempty
      (F.obj.obj (op (supportRepSmallTarget' B S hS F))) := by
  let E := supportRepSmallFamily' B S hS F
  have hpre : E.presieve₀ ∈ SmallEtale.precoverage B S hS
      (supportRepSmallTarget' B S hS F) :=
    ⟨E, rfl, supportRepSmallFamily_isCovering' B S hS F⟩
  have hgen : Sieve.generate E.presieve₀ ∈
      SmallEtale.topology B S hS (supportRepSmallTarget' B S hS F) :=
    Precoverage.generate_mem_toGrothendieck hpre
  have hsf : Presieve.IsSheafFor F.obj E.presieve₀ :=
    (Presieve.isSheafFor_iff_generate E.presieve₀).2 <|
      (isSheaf_iff_isSheaf_of_type
        (SmallEtale.topology B S hS) F.obj).1 F.property
        (Sieve.generate E.presieve₀) hgen
  let localSection : (i : E.I₀) → F.obj.obj (op (E.X i)) := fun i =>
    F.obj.map (supportRepComponentIso' B S hS F i).hom.op
      (Classical.choice (supportRepComponentIndex' B S hS F i).2)
  let family : Presieve.FamilyOfElements F.obj E.presieve₀ := fun {V} f hf => by
    have hm : ∃ i, ∃ e : V ≅ E.X i, e.hom ≫ E.f i = f := by
      cases hf with
      | mk i => exact ⟨i, Iso.refl _, rfl⟩
    let i := Classical.choose hm
    let e := Classical.choose (Classical.choose_spec hm)
    exact F.obj.map e.hom.op (localSection i)
  have hcompatible : family.Compatible := by
    intro V₁ V₂ T a b f₁ f₂ hf₁ hf₂ h
    exact (section_subsingleton'.{u + 1, v, u}
      (SmallEtale.topology B S hS) F hF T).elim _ _
  exact ⟨hsf.amalgamate family hcompatible⟩

private noncomputable def supportRepTargetIso' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS) :
    supportRepSmallTarget' B S hS F ≅ supportObject' B S hS F := by
  let h := supportCoveringRep_targetEq' B S hS F
  refine ObjectProperty.isoMk _ <| Over.isoMk (eqToIso h.symm) ?_
  rfl

private theorem supportOpen_has_section' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS)
    (hF : IsSubterminal F) : Nonempty
      (F.obj.obj (op (supportObject' B S hS F))) :=
  ⟨F.obj.map (supportRepTargetIso' B S hS F).inv.op
    (Classical.choice (supportSection_on_open' B S hS F hF))⟩

/-- The presheaf on the small étale site of `S` represented by an open subscheme `W` of `S`,
with its sections raised to the universe `max u₁ v₁`.

This generalizes `AlgebraicGeometry.openRepresentable`, whose sections live in `max (u₁ + 1) v₁`:
the sections universe may now be as small as the universe `u₁` of the schemes. An open subscheme
of `S` is an object of the big étale slice over `S`, and this is the restriction to the small
étale site of the presheaf it represents there. -/
public noncomputable abbrev openRepresentable'.{u₁, v₁}
    (B : BigEtaleSite.{u₁}) (S : Scheme.{u₁}) (hS : B.Contains S)
    (W : S.Opens) :
    (SmallEtale B S hS)ᵒᵖ ⥤ Type (max u₁ v₁) :=
  ((SmallEtale.inclusion B S hS ⋙
    Over.post (X := B.obj S hS) B.inclusion).op ⋙
      uliftYoneda.{max u₁ v₁}.obj
        (Over.mk W.ι))

private noncomputable abbrev supportRepresentable'.{u₁, v₁}
    (B : BigEtaleSite.{u₁}) (S : Scheme.{u₁}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u₁, max u₁ v₁} B S hS) :
    (SmallEtale B S hS)ᵒᵖ ⥤ Type (max u₁ v₁) :=
  openRepresentable'.{u₁, v₁} B S hS (supportOpen' B S hS F)

/-- The presheaf represented by an open subscheme of `S` is a sheaf on the small étale site, in
every sections universe `max u₁ v₁`; this generalizes
`AlgebraicGeometry.openRepresentable_isSheaf`.

The fpqc topology on the schemes over `S` is subcanonical, so a representable presheaf is an
fpqc sheaf, and an fpqc sheaf restricts to a sheaf on the chosen small étale site. -/
public theorem openRepresentable_isSheaf'.{u₁, v₁} (B : BigEtaleSite.{u₁})
    (S : Scheme.{u₁}) (hS : B.Contains S)
    (W : S.Opens) :
    Presheaf.IsSheaf (SmallEtale.topology B S hS)
      (openRepresentable'.{u₁, v₁} B S hS W) := by
  let P : (Over S)ᵒᵖ ⥤ Type (max u₁ v₁) :=
    uliftYoneda.{max u₁ v₁}.obj (Over.mk W.ι)
  have hRep : Presieve.IsSheaf (Scheme.fpqcTopology.over S) P :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable P
  exact isSheaf_chosenSmallEtale_of_isSheaf_fpqc B S hS P
    ((isSheaf_iff_isSheaf_of_type (Scheme.fpqcTopology.over S) P).2 hRep)

private noncomputable def representableArrowToSupportObject'
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS)
    (U : SmallEtale B S hS)
    (x : (supportRepresentable' B S hS F).obj (op U)) :
    U ⟶ supportObject' B S hS F := by
  change ULift (Over.mk (smallEtaleMap B S hS U) ⟶
    Over.mk (supportOpen' B S hS F).ι) at x
  let a := x.down
  let hobj := supportObject_underlying_eq' B S hS F
  let cast : (supportOpen' B S hS F : Scheme) ⟶
      B.inclusion.obj (supportObject' B S hS F).obj.left := eqToHom hobj.symm
  let g' : B.inclusion.obj U.obj.left ⟶
      B.inclusion.obj (supportObject' B S hS F).obj.left := a.left ≫ cast
  let g : U.obj.left ⟶ supportBaseObject' B S hS F :=
    B.inclusion.preimage g'
  have hg : g ≫ (supportObject' B S hS F).obj.hom = U.obj.hom := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, B.inclusion.map_preimage]
    change (a.left ≫ cast) ≫
        B.inclusion.map (supportObject' B S hS F).obj.hom =
      B.inclusion.map U.obj.hom
    rw [Category.assoc]
    have hcast : cast ≫ B.inclusion.map (supportObject' B S hS F).obj.hom =
        (supportOpen' B S hS F).ι := by
      simp [cast, supportObject', supportBaseObject']
    rw [hcast]
    simpa [smallEtaleMap] using a.w
  exact ObjectProperty.homMk (Over.homMk g hg)

private theorem representableArrow_map' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS)
    {U V : SmallEtale B S hS} (f : op U ⟶ op V)
    (x : (supportRepresentable' B S hS F).obj (op U)) :
    representableArrowToSupportObject' B S hS F V
      ((supportRepresentable' B S hS F).map f x) =
      f.unop ≫ representableArrowToSupportObject' B S hS F U x := by
  have hobj := supportObject_underlying_eq' B S hS F
  let cast : (supportOpen' B S hS F : Scheme) ⟶
      B.inclusion.obj (supportObject' B S hS F).obj.left := eqToHom hobj.symm
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  show B.inclusion.preimage (X := V.obj.left)
      (Y := supportBaseObject' B S hS F)
      (B.inclusion.map (Over.Hom.left f.unop.hom) ≫
        (Over.Hom.left x.down ≫ cast)) =
    Over.Hom.left f.unop.hom ≫
      B.inclusion.preimage (X := U.obj.left)
        (Y := supportBaseObject' B S hS F) (Over.Hom.left x.down ≫ cast)
  calc
    _ = B.inclusion.preimage (B.inclusion.map (Over.Hom.left f.unop.hom)) ≫
          B.inclusion.preimage (Over.Hom.left x.down ≫ cast) :=
      B.inclusion.preimage_comp _ _
    _ = _ := by simp only [Functor.preimage_map]

private noncomputable def supportRepresentableToSheaf'
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS)
    (s : F.obj.obj (op (supportObject' B S hS F))) :
    supportRepresentable' B S hS F ⟶ F.obj := by
  refine ⟨fun U => ↾fun x => F.obj.map
      (representableArrowToSupportObject' B S hS F U.unop x).op s, ?_⟩
  intro U V f
  ext x
  symm
  change F.obj.map f
      (F.obj.map (representableArrowToSupportObject' B S hS F U.unop x).op s) =
    F.obj.map (representableArrowToSupportObject' B S hS F V.unop
      ((supportRepresentable' B S hS F).map f x)).op s
  rw [← Functor.map_comp_apply]
  have hcomp := congrArg Quiver.Hom.op (representableArrow_map' B S hS F f x)
  have hcomp' :
      (representableArrowToSupportObject' B S hS F (unop V)
        ((supportRepresentable' B S hS F).map f x)).op =
      (representableArrowToSupportObject' B S hS F (unop U) x).op ≫ f := by
    rw [op_comp, Quiver.Hom.op_unop] at hcomp
    exact hcomp
  rw [← hcomp']

private noncomputable def sheafToSupportRepresentable'
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS) :
    F.obj ⟶ supportRepresentable' B S hS F := by
  refine ⟨fun U => ↾fun s =>
    ULift.up (supportSectionArrow' B S hS F U.unop s), ?_⟩
  intro U V f
  ext s
  apply ULift.ext
  apply Over.OverMorphism.ext
  apply (cancel_mono (supportOpen' B S hS F).ι).1
  let G := SmallEtale.inclusion B S hS ⋙
    Over.post (X := B.obj S hS) B.inclusion
  have hU := Over.w (supportSectionArrow' B S hS F U.unop s)
  have hV := Over.w
    (supportSectionArrow' B S hS F V.unop (F.obj.map f s))
  have hf : (G.map f.unop).left ≫ smallEtaleMap B S hS U.unop =
      smallEtaleMap B S hS V.unop := by
    change B.inclusion.map f.unop.hom.left ≫
        B.inclusion.map U.unop.obj.hom = B.inclusion.map V.unop.obj.hom
    rw [← Functor.map_comp]
    exact congrArg B.inclusion.map (Over.w f.unop.hom)
  change (supportSectionArrow' B S hS F V.unop (F.obj.map f s)).left ≫
      (supportOpen' B S hS F).ι =
    (G.map f.unop).left ≫
      ((supportSectionArrow' B S hS F U.unop s).left ≫
        (supportOpen' B S hS F).ι)
  exact hV.trans <| hf.symm.trans <|
    congrArg (fun g => (G.map f.unop).left ≫ g) hU.symm

/-- **The presheaf represented by an open subscheme has at most one section over each object of
the small étale site.** A section over `U` is a factorisation of the structure morphism of `U`
through the open immersion, and an open immersion is a monomorphism. -/
public theorem openRepresentable_obj_subsingleton.{u₁, v₁}
    (B : BigEtaleSite.{u₁}) (S : Scheme.{u₁}) (hS : B.Contains S)
    (W : S.Opens) (U : SmallEtale B S hS) :
    Subsingleton ((openRepresentable'.{u₁, v₁} B S hS W).obj (op U)) := by
  show Subsingleton (ULift (Over.mk (smallEtaleMap B S hS U) ⟶ Over.mk W.ι))
  refine ⟨fun x y => ?_⟩
  apply ULift.ext
  apply Over.OverMorphism.ext
  apply (cancel_mono W.ι).1
  exact (Over.w x.down).trans (Over.w y.down).symm

set_option synthInstance.maxHeartbeats 200000 in
/-- **The sheaf on the small étale site represented by an open subscheme is a subsheaf of the
final sheaf.** This is the direction opposite to Stacks 04HV, and the input through which a
morphism of topoi out of the small étale topos is fed to it: the presheaf has at most one
section over each object of the site, so it is subterminal among presheaves, and sheafification
is left exact. -/
public theorem isSubterminal_openRepresentableSheaf.{u₁, v₁} (B : BigEtaleSite.{u₁})
    (S : Scheme.{u₁}) (hS : B.Contains S) (W : S.Opens) :
    IsSubterminal ((presheafToSheaf (SmallEtale.topology B S hS)
      (Type (max u₁ v₁))).obj (openRepresentable'.{u₁, v₁} B S hS W)) :=
  (isSubterminal_of_subsingleton_obj (openRepresentable'.{u₁, v₁} B S hS W)
    (fun U => openRepresentable_obj_subsingleton.{u₁, v₁} B S hS W U.unop)).map
      Limits.terminalIsTerminal _

private noncomputable def chosenPresheafToSheafIso'
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ Type (max u v))
    (hP : Presheaf.IsSheaf (SmallEtale.topology B S hS) P) :
    (⟨P, hP⟩ : smallEtaleTopos.{u, max u v} B S hS) ≅
      (presheafToSheaf (SmallEtale.topology B S hS)
        (Type (max u v))).obj P := by
  apply ObjectProperty.isoMk
  letI : IsIso (toSheafify (SmallEtale.topology B S hS) P) :=
    isIso_toSheafify (SmallEtale.topology B S hS) hP
  exact asIso (toSheafify (SmallEtale.topology B S hS) P)

/-- **A section over `U` of the presheaf represented by an open `W` forces the image of `U` into
`W`.** The section is a factorisation of the structure morphism of `U` through the open
immersion of `W`, so every point in the image of `U` is the image of a point of `W`. This is the
converse of `AlgebraicGeometry.openRepresentable_nonempty_of_range_subset'`. -/
public theorem openRepresentable_range_subset'.{u₁, v₁}
    (B : BigEtaleSite.{u₁}) (S : Scheme.{u₁}) (hS : B.Contains S)
    (W : S.Opens) (U : SmallEtale B S hS)
    (x : (openRepresentable'.{u₁, v₁} B S hS W).obj (op U)) :
    Set.range (smallEtaleMap B S hS U).base ⊆ (W : Set S) := by
  change ULift (Over.mk (smallEtaleMap B S hS U) ⟶ Over.mk W.ι) at x
  intro y hy
  obtain ⟨z, rfl⟩ := hy
  have hcomm := Over.w x.down
  change x.down.left ≫ W.ι = smallEtaleMap B S hS U at hcomm
  have hpt : W.ι (x.down.left z) = (smallEtaleMap B S hS U) z := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun f => f z) hcomm
  show (smallEtaleMap B S hS U).base z ∈ W
  rw [← hpt]
  exact (x.down.left z).property

/-- **An object of the small étale site whose image lies in an open `W` has a section of the
presheaf represented by `W`**, namely the factorisation of its structure morphism through the
open immersion. -/
public theorem openRepresentable_nonempty_of_range_subset'.{u₁, v₁}
    (B : BigEtaleSite.{u₁}) (S : Scheme.{u₁}) (hS : B.Contains S)
    (W : S.Opens) (U : SmallEtale B S hS)
    (h : Set.range (smallEtaleMap B S hS U).base ⊆ (W : Set S)) :
    Nonempty ((openRepresentable'.{u₁, v₁} B S hS W).obj (op U)) :=
  ⟨ULift.up (overHomOfRangeSubset _ _ h)⟩

/-- **The sheaf represented by an open subscheme `W` has a section over an object `U` of the
small étale site exactly when the image of `U` lies in `W`.**

The presheaf represented by `W` is already a sheaf
(`AlgebraicGeometry.openRepresentable_isSheaf'`), so `CategoryTheory.toSheafify` is an
isomorphism and the sections of the sheafification are the sections of the presheaf; those are
described by `AlgebraicGeometry.openRepresentable_nonempty_of_range_subset'` and
`AlgebraicGeometry.openRepresentable_range_subset'`. -/
public theorem nonempty_openRepresentableSheaf_obj_iff.{u₁, v₁}
    (B : BigEtaleSite.{u₁}) (S : Scheme.{u₁}) (hS : B.Contains S)
    (W : S.Opens) (U : SmallEtale B S hS) :
    Nonempty (((presheafToSheaf (SmallEtale.topology B S hS)
        (Type (max u₁ v₁))).obj (openRepresentable'.{u₁, v₁} B S hS W)).obj.obj (op U)) ↔
      Set.range (smallEtaleMap B S hS U).base ⊆ (W : Set S) := by
  constructor
  · rintro ⟨s⟩
    exact openRepresentable_range_subset'.{u₁, v₁} B S hS W U
      ((isoSheafify (SmallEtale.topology B S hS)
        (openRepresentable_isSheaf'.{u₁, v₁} B S hS W)).inv.app (op U) s)
  · intro h
    exact ⟨(toSheafify (SmallEtale.topology B S hS)
      (openRepresentable'.{u₁, v₁} B S hS W)).app (op U)
        (Classical.choice (openRepresentable_nonempty_of_range_subset'.{u₁, v₁} B S hS W U h))⟩

/-- **The sheaves represented by two open subschemes admit a morphism exactly when the opens are
nested.** One direction is the image under sheafification of the morphism of representables
induced by the inclusion; the other evaluates a morphism at the object of the site given by the
source open, where `AlgebraicGeometry.nonempty_openRepresentableSheaf_obj_iff` turns the
resulting section into the inclusion of images.

This identifies the lattice of open subschemes of `S` with the subobjects of the final sheaf it
represents, which is what carries an adjunction between sheaves to an adjunction between
lattices of opens. -/
public theorem nonempty_hom_openRepresentableSheaf_iff_le.{u₁, v₁}
    (B : BigEtaleSite.{u₁}) (S : Scheme.{u₁}) (hS : B.Contains S) (W W' : S.Opens) :
    Nonempty ((presheafToSheaf (SmallEtale.topology B S hS)
          (Type (max u₁ v₁))).obj (openRepresentable'.{u₁, v₁} B S hS W) ⟶
        (presheafToSheaf (SmallEtale.topology B S hS)
          (Type (max u₁ v₁))).obj (openRepresentable'.{u₁, v₁} B S hS W')) ↔
      W ≤ W' := by
  constructor
  · rintro ⟨φ⟩
    obtain ⟨U, hU⟩ := exists_smallEtale_range_eq B S hS W
    obtain ⟨s⟩ := (nonempty_openRepresentableSheaf_obj_iff.{u₁, v₁} B S hS W U).2 hU.le
    have h := (nonempty_openRepresentableSheaf_obj_iff.{u₁, v₁} B S hS W' U).1
      ⟨φ.hom.app (op U) s⟩
    rwa [hU] at h
  · intro h
    exact ⟨(presheafToSheaf (SmallEtale.topology B S hS) (Type (max u₁ v₁))).map
      (Functor.whiskerLeft _ (uliftYoneda.{max u₁ v₁}.map
        (Over.homMk (S.homOfLE h) (S.homOfLE_ι h) :
          Over.mk W.ι ⟶ Over.mk W'.ι)))⟩

/-- The morphism from the final presheaf to the presheaf represented by the whole of `S`: over
an object of the small étale site the structure morphism factors through the identity open, and
the factorisation is unique, which is all the naturality there is to check. -/
public noncomputable def openRepresentableTopFromTerminal.{u₁, v₁}
    (B : BigEtaleSite.{u₁}) (S : Scheme.{u₁}) (hS : B.Contains S) :
    (Limits.terminal ((SmallEtale B S hS)ᵒᵖ ⥤ Type (max u₁ v₁))) ⟶
      openRepresentable'.{u₁, v₁} B S hS ⊤ := by
  refine ⟨fun U => ↾fun _ => Classical.choice
    (openRepresentable_nonempty_of_range_subset'.{u₁, v₁} B S hS ⊤ U.unop
      (fun _ _ => trivial)), ?_⟩
  intro U V f
  ext x
  exact (openRepresentable_obj_subsingleton.{u₁, v₁} B S hS ⊤ V.unop).elim _ _

/-- **The sheaf on the small étale site represented by the whole of `S` is the final sheaf.**
It is subterminal by `AlgebraicGeometry.isSubterminal_openRepresentableSheaf` and it has a
global section, the identity of `S`. -/
public noncomputable def isTerminal_openRepresentableSheaf_top.{u₁, v₁}
    (B : BigEtaleSite.{u₁}) (S : Scheme.{u₁}) (hS : B.Contains S) :
    Limits.IsTerminal ((presheafToSheaf (SmallEtale.topology B S hS)
      (Type (max u₁ v₁))).obj (openRepresentable'.{u₁, v₁} B S hS ⊤)) :=
  (isSubterminal_openRepresentableSheaf.{u₁, v₁} B S hS ⊤).isTerminal
    (Limits.terminalIsTerminal.isTerminalObj
      (presheafToSheaf (SmallEtale.topology B S hS) (Type (max u₁ v₁))) _)
    ((presheafToSheaf (SmallEtale.topology B S hS) (Type (max u₁ v₁))).map
      (openRepresentableTopFromTerminal.{u₁, v₁} B S hS))

private noncomputable def supportSheafificationIso'
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS)
    (hF : IsSubterminal F) :
    F ≅ (presheafToSheaf (SmallEtale.topology B S hS)
      (Type (max u v))).obj (supportRepresentable' B S hS F) := by
  let P := supportRepresentable' B S hS F
  let hP := openRepresentable_isSheaf' B S hS (supportOpen' B S hS F)
  let α : F.obj ⟶ P := sheafToSupportRepresentable' B S hS F
  let β : P ⟶ F.obj := supportRepresentableToSheaf' B S hS F
    (Classical.choice (supportOpen_has_section' B S hS F hF))
  have hαβ : α ≫ β = 𝟙 _ := by
    ext U x
    exact (section_subsingleton'.{u + 1, v, u} (SmallEtale.topology B S hS)
      F hF U.unop).elim _ _
  have hβα : β ≫ α = 𝟙 _ := by
    ext U x
    exact (openRepresentable_obj_subsingleton B S hS (supportOpen' B S hS F) U.unop).elim _ _
  let e : F ≅ ⟨P, hP⟩ := ObjectProperty.isoMk _ {
    hom := α
    inv := β
    hom_inv_id := hαβ
    inv_hom_id := hβα
  }
  exact e.trans (chosenPresheafToSheafIso' B S hS P hP)

/-- **A subterminal sheaf on the small étale site is represented by a unique open subscheme of
the base**, in every universe of sections at or above the universe of the schemes.

The sections universe is `max u v` with `v` free, so `v := u` gives the universe `u` of the
sections of the small étale ringed topos `AlgebraicGeometry.smallEtaleRingedSite` and
`v := u + 1` the universe `u + 1` of the objects of the site. This generalizes
`AlgebraicGeometry.existsUnique_open_of_isSubterminal` (Stacks 04HV), whose sections universe is
`max (u + 1) v`. -/
public theorem existsUnique_open_of_isSubterminal'
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : smallEtaleTopos.{u, max u v} B S hS)
    (hF : IsSubterminal F) :
    ∃! W : S.Opens,
      Nonempty (F ≅
        (presheafToSheaf (SmallEtale.topology B S hS)
          (Type (max u v))).obj
          ((SmallEtale.inclusion B S hS ⋙
            Over.post (X := B.obj S hS) B.inclusion).op ⋙
            uliftYoneda.{max u v}.obj (Over.mk W.ι))) := by
  refine ⟨supportOpen' B S hS F, ⟨supportSheafificationIso' B S hS F hF⟩, ?_⟩
  rintro W ⟨e⟩
  let P := openRepresentable' B S hS W
  let hP := openRepresentable_isSheaf' B S hS W
  let e' := e.trans (chosenPresheafToSheafIso' B S hS P hP).symm
  apply le_antisymm
  · intro x hx
    obtain ⟨U, hU⟩ := exists_smallEtale_range_eq B S hS W
    obtain ⟨p⟩ : Nonempty (P.obj (op U)) :=
      openRepresentable_nonempty_of_range_subset' B S hS W U hU.le
    exact supportOpen_contains_map_range' B S hS F U (e'.inv.hom.app (op U) p)
      (by rwa [hU])
  · refine iSup_le fun i => ?_
    obtain ⟨s⟩ := i.2
    exact openRepresentable_range_subset' B S hS W i.1 (e'.hom.hom.app (op i.1) s)

end AlgebraicGeometry

end
