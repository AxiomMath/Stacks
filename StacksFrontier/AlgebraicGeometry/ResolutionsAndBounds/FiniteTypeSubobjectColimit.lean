module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectExtension
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjects
public import StacksCore.Tactic.StacksAttribute

/-!
# A quasi-coherent module as the colimit of its finite type submodules

On a quasi-compact and quasi-separated scheme, the quasi-coherent submodules of finite type of a
quasi-coherent module `F` cover `F`, and the canonical cocone they form is a colimit cocone.
Together with the filteredness of the diagram, proved in
`StacksFrontier/AlgebraicGeometry/ResolutionsAndBounds/FiniteTypeSubobjects.lean`, this is the
statement that `F` is the directed colimit of those submodules: Stacks 01PG.

The covering statement is where Stacks 01PF is used, and it is the only place: a section of `F`
over a quasi-compact open generates a finite type quasi-coherent submodule there, 01PF extends
it to one defined on the whole scheme, and the section is then in the image of that submodule.
The colimit statement follows from the covering statement by the general fact that in a
Grothendieck abelian category a filtered diagram of subobjects whose supremum is everything has
the ambient object as its colimit.

That first step is stated separately, for an arbitrary quasi-compact open rather than only for
the affine opens the supremum computation needs, because it is what a consumer of the colimit
actually uses: it says that `Γ(-, W)` is surjective onto the sections of `F` over `W` already at
one stage of the diagram, which is the only part of "sections commute with the colimit" that a
surjectivity statement about `F` requires.

## Main results

* `AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_section`: every section of `F` over
  a quasi-compact open comes from one of those submodules. This is the covering statement in the
  form a consumer of the colimit needs, and the other two results below are read off from it.
* `AlgebraicGeometry.iSup_finiteTypeQuasicoherentSubobject_eq_top`: the quasi-coherent finite
  type submodules of `F` have supremum `⊤`.
* `AlgebraicGeometry.isColimit_finiteTypeQuasicoherentSubobjectCocone`: **Tag 01PG**, the
  canonical cocone is a colimit cocone.
* `AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_sup`: two quasi-coherent submodules
  of finite type are contained in a common one.
* `AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_finset_sections` and
  `AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_sections`: finitely many sections
  over quasi-compact opens all come from a single quasi-coherent submodule of finite type.
* `AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_le_sections`: the same with the
  submodule constrained to lie inside a prescribed quasi-coherent submodule of `F`.

## Implementation notes

`AlgebraicGeometry.restrictTopIso` identifies the global sections of `F|_W` with the sections of
`F` over `W`; its naturality is what turns a section of the supremum over `W` back into a section
of `F` over `W`, and it is used in the sections form rather than through a rewrite, because the
two spellings `Scheme.Modules.Hom.app` and `.val.app` of the same map are not interchangeable by
`rw`.

The diagram is reindexed by a small filtered category before the Grothendieck colimit criterion
is applied, since the category of subobjects satisfying a property is only essentially small.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open SheafOfModules

universe u

namespace AlgebraicGeometry

/-- The global sections of the restriction of `M` to the open subscheme `W` are the sections
of `M` over `W`. -/
public noncomputable def restrictTopIso {X : Scheme.{u}} (M : X.Modules) (W : X.Opens) :
    Γ(M.restrict W.ι, ⊤) ≅ Γ(M, W) :=
  M.restrictAppIso W.ι ⊤ ≪≫ M.presheaf.mapIso (eqToIso (by simp)).op

/-- The isomorphism `restrictTopIso` is natural in the module. -/
public lemma restrictTopIso_naturality {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (W : X.Opens) :
    ((Scheme.Modules.restrictFunctor W.ι).map f).app ⊤ ≫ (restrictTopIso N W).hom =
      (restrictTopIso M W).hom ≫ f.app W := by
  change f.app (W.ι ''ᵁ ⊤) ≫ N.presheaf.map _ = M.presheaf.map _ ≫ f.app W
  exact (f.mapPresheaf.naturality _).symm

/-- **A section over a quasi-compact open comes from a single finite type quasi-coherent
submodule.** On a quasi-compact and quasi-separated scheme, let `F` be a quasi-coherent module
and `W` a quasi-compact open. Every section of `F` over `W` is the image of a section of some
quasi-coherent submodule of `F` of finite type.

This is the surjectivity half of the statement that `Γ(-, W)` carries the filtered colimit of
[Stacks, Tag 01PG] to the colimit of the modules of sections: the colimit of a filtered diagram
of submodules is computed by its legs, so for a *fixed* `W` what has to be produced is one stage
of the diagram containing the given section.

The proof is the source's proof of [Stacks, Tag 01PG]. The section, viewed on the open subscheme
`W`, is a morphism `𝒪_W ⟶ F|_W`; its image is a quasi-coherent submodule of `F|_W` of finite
type containing the section, and [Stacks, Tag 01PF]
(`AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_extension`) extends that submodule
across `X`. Quasi-compactness of `W` is all that is asked of it, so there is no need to shrink
to an affine open first. -/
@[ega "I 9.4.3" "exhaustion clause"]
theorem exists_finiteTypeQuasicoherentSubobject_section {X : Scheme.{u}} (F : X.Modules)
    [CompactSpace X] [QuasiSeparatedSpace X] [F.IsQuasicoherent]
    (W : X.Opens) (hW : IsCompact (W : Set X)) (s : Γ(F, W)) :
    ∃ G : Subobject F, (G : X.Modules).IsQuasicoherent ∧ (G : X.Modules).IsFiniteType ∧
      ∃ t : Γ((G : X.Modules), W), G.arrow.app W t = s := by
  classical
  let Fw : W.toScheme.Modules := F.restrict W.ι
  have : Fw.IsQuasicoherent := inferInstance
  let sTop := (restrictTopIso F W).inv s
  let sLoc : Fw.sections := Fw.val.sectionsMk
    (fun U => Fw.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op sTop)
    (by
      intro U V f
      change Fw.val.presheaf.map f
          (Fw.val.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op sTop) = _
      have hcomp : (homOfLE (show U.unop ≤ ⊤ from le_top)).op ≫ f =
          (homOfLE (show V.unop ≤ ⊤ from le_top)).op := Subsingleton.elim _ _
      calc
        Fw.val.presheaf.map f
            (Fw.val.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op sTop) =
          Fw.val.presheaf.map
            ((homOfLE (show U.unop ≤ ⊤ from le_top)).op ≫ f) sTop :=
              (Fw.val.presheaf.map_comp_apply
                (homOfLE (show U.unop ≤ ⊤ from le_top)).op f sTop).symm
        _ = Fw.val.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op sTop :=
          congrArg (fun j => Fw.val.presheaf.map j sTop) hcomp)
  let O : W.toScheme.Modules := SheafOfModules.unit W.toScheme.ringCatSheaf
  have : O.IsQuasicoherent := (unit_isQuasicoherent_and_isFiniteType (X := W.toScheme)).1
  have : O.IsFiniteType := (unit_isQuasicoherent_and_isFiniteType (X := W.toScheme)).2
  let f : O ⟶ Fw := Fw.unitHomEquiv.symm sLoc
  let I : Subobject Fw := imageSubobject f
  have : (I : W.toScheme.Modules).IsQuasicoherent := imageSubobject_isQuasicoherent f
  have : (I : W.toScheme.Modules).IsFiniteType := imageSubobject_isFiniteType f
  obtain ⟨G, hGqc, hGft, e, he⟩ :=
    exists_finiteTypeQuasicoherentSubobject_extension F W hW I
  let p : O ⟶ (I : W.toScheme.Modules) := factorThruImageSubobject f
  let g : O ⟶ (G : X.Modules).restrict W.ι := p ≫ e.inv
  have hg : g ≫ (Scheme.Modules.restrictFunctor W.ι).map G.arrow = f := by
    dsimp only [g]
    rw [Category.assoc, he, Iso.inv_hom_id_assoc]
    exact imageSubobject_arrow_comp f
  let zSrc := ((G : X.Modules).restrict W.ι).unitHomEquiv g
  have hzSrc : SheafOfModules.sectionsMap
      ((Scheme.Modules.restrictFunctor W.ι).map G.arrow) zSrc = sLoc := by
    calc
      _ = Fw.unitHomEquiv (g ≫ (Scheme.Modules.restrictFunctor W.ι).map G.arrow) :=
        (SheafOfModules.unitHomEquiv_comp_apply g _).symm
      _ = Fw.unitHomEquiv f := congrArg Fw.unitHomEquiv hg
      _ = sLoc := Fw.unitHomEquiv.apply_symm_apply sLoc
  have hsLocTop : sLoc.val (op ⊤) = sTop := by
    change Fw.presheaf.map (𝟙 _) sTop = sTop
    exact ConcreteCategory.congr_hom (Fw.presheaf.map_id (op ⊤)) sTop
  have hzSrcTop :
      (((Scheme.Modules.restrictFunctor W.ι).map G.arrow).val.app (op ⊤))
        (zSrc.val (op ⊤)) = sTop :=
    (congrArg (fun z : Fw.sections => z.val (op ⊤)) hzSrc).trans hsLocTop
  refine ⟨G, hGqc, hGft, (restrictTopIso (G : X.Modules) W).hom (zSrc.val (op ⊤)), ?_⟩
  have hnat : (restrictTopIso F W).hom
      ((((Scheme.Modules.restrictFunctor W.ι).map G.arrow).app ⊤) (zSrc.val (op ⊤))) =
      (G.arrow.app W) ((restrictTopIso (G : X.Modules) W).hom (zSrc.val (op ⊤))) := by
    have h := ConcreteCategory.congr_hom (restrictTopIso_naturality G.arrow W)
      (zSrc.val (op ⊤))
    exact ((ConcreteCategory.comp_apply _ _ _).symm.trans h).trans
      (ConcreteCategory.comp_apply _ _ _)
  rw [← hnat]
  change (restrictTopIso F W).hom
    ((((Scheme.Modules.restrictFunctor W.ι).map G.arrow).val.app (op ⊤))
      (zSrc.val (op ⊤))) = s
  rw [hzSrcTop]
  exact ConcreteCategory.congr_hom (Iso.inv_hom_id (restrictTopIso F W)) s

/-- A section of a submodule is a section of any larger submodule, with the same image in the
ambient module. -/
private lemma exists_section_of_le {X : Scheme.{u}} {F : X.Modules} {A C : Subobject F}
    (h : A ≤ C) (V : X.Opens) (u : Γ((A : X.Modules), V)) :
    ∃ v : Γ((C : X.Modules), V), C.arrow.app V v = A.arrow.app V u :=
  ⟨(Subobject.ofLE A C h).app V u, by
    change ((Subobject.ofLE A C h ≫ C.arrow).app V) u = _
    rw [Subobject.ofLE_arrow]⟩

/-- Finite type quasi-coherent subobjects cover a quasi-coherent module on a qcqs scheme. -/
lemma iSup_finiteTypeQuasicoherentSubobject_eq_top
    {X : Scheme.{u}} (F : X.Modules)
    [CompactSpace X] [QuasiSeparatedSpace X] [F.IsQuasicoherent] :
    (⨆ G : FiniteTypeQuasicoherentSubobject F, G.1) = ⊤ := by
  classical
  let J := FiniteTypeQuasicoherentSubobject F
  let S : Subobject F := ⨆ G : J, G.1
  let q : (S : X.Modules) ⟶ F := S.arrow
  let T := SheafOfModules.toSheaf X.ringCatSheaf
  let qSheaf := T.map q
  have hqSheaf : Epi qSheaf := by
    apply (TopCat.Sheaf.isLocallySurjective_iff_epi qSheaf).1
    rw [TopCat.Presheaf.isLocallySurjective_iff]
    intro U t x hx
    obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
    have hWle : W ≤ U := fun y hy => hWU hy
    let sW : Γ(F, W) := F.presheaf.map (homOfLE hWle).op t
    obtain ⟨G, hGqc, hGft, tG, htG⟩ :=
      exists_finiteTypeQuasicoherentSubobject_section F W hW.isCompact sW
    let GJ : J := ⟨G, hGqc, hGft⟩
    obtain ⟨v, hv⟩ := exists_section_of_le (le_iSup (fun G : J => G.1) GJ) W tG
    exact ⟨W, hWle, ⟨v, hv.trans htG⟩, hxW⟩
  have : Epi q := T.epi_of_epi_map hqSheaf
  have : IsIso q := isIso_of_mono_of_epi q
  simpa only [q, Subobject.mk_arrow] using Subobject.mk_eq_top_of_isIso q

/-- **Stacks Project, Tag 01PG.** On a quasi-compact and quasi-separated scheme, a quasi-coherent
module is the colimit of the canonical diagram of all its quasi-coherent finite type submodules.

This is the colimit half of the tag; the other half, that the diagram is filtered — so that the
colimit is a *directed* one — is
`AlgebraicGeometry.finiteTypeQuasicoherentSubobject_isFiltered`. Together the two are the tag's
assertion, so the tag is attached to both. -/
@[stacks 01PG, ega "I 9.4.9" "quasi-compact scheme"]
noncomputable def isColimit_finiteTypeQuasicoherentSubobjectCocone
    {X : Scheme.{u}} (F : X.Modules)
    [CompactSpace X] [QuasiSeparatedSpace X] [F.IsQuasicoherent] :
    IsColimit (finiteTypeQuasicoherentSubobjectCocone F) := by
  classical
  let P := finiteTypeQuasicoherentSubobjectProperty F
  let J := FiniteTypeQuasicoherentSubobject F
  let D : J ⥤ MonoOver F := P.ι ⋙ Subobject.representative
  have : ObjectProperty.Small.{u} P :=
    ObjectProperty.Small.of_le (P := P) (Q := ⊤) (fun _ _ => trivial)
  have : LocallySmall.{u} (Subobject F) := CategoryTheory.locallySmall_of_thin
  have : LocallySmall.{u} J := locallySmall_of_faithful P.ι
  have : EssentiallySmall.{u} J := essentiallySmall_of_small_of_locallySmall J
  let eJ : J ≌ SmallModel.{u} J := equivSmallModel J
  have : IsFiltered (SmallModel.{u} J) := IsFiltered.of_equivalence eJ
  let Dsmall : SmallModel.{u} J ⥤ MonoOver F := eJ.inverse ⋙ D
  let c : Cocone (D ⋙ MonoOver.forget F) := Cocone.mk (Over.mk (𝟙 F)) {
    app := fun G => (MonoOver.forget F).map (MonoOver.leTop (D.obj G))
    naturality := by
      intro G H f
      apply Over.OverMorphism.ext
      change Subobject.underlying.map f.hom ≫ H.obj.arrow = G.obj.arrow
      exact Subobject.underlying_arrow f.hom
  }
  have hsup : (⨆ G : J, G.1) = ⊤ := iSup_finiteTypeQuasicoherentSubobject_eq_top F
  have hsupSmall : (⨆ G : SmallModel.{u} J, (eJ.inverse.obj G).1) = ⊤ := by
    apply top_unique
    rw [← hsup]
    refine iSup_le fun G => ?_
    have hG : G.1 = (eJ.inverse.obj (eJ.functor.obj G)).1 :=
      Subobject.skeletal F ⟨P.ι.mapIso (eJ.unitIso.app G)⟩
    rw [hG]
    exact le_iSup (fun G : SmallModel.{u} J => (eJ.inverse.obj G).1) _
  have htopSmall : Subobject.mk (𝟙 F) =
      ⨆ G : SmallModel.{u} J, Subobject.mk (Dsmall.obj G).obj.hom := by
    rw [← Subobject.top_eq_id]
    simpa [Dsmall, D, Subobject.mk_arrow] using hsupSmall.symm
  let csmall : Cocone (Dsmall ⋙ MonoOver.forget F) := c.whisker eJ.inverse
  have : Mono csmall.pt.hom := inferInstanceAs (Mono (𝟙 F))
  have hcSmall : IsColimit ((Over.forget F).mapCocone csmall) :=
    IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup Dsmall csmall htopSmall
  have hc : IsColimit ((Over.forget F).mapCocone c) :=
    (IsColimit.whiskerEquivalenceEquiv eJ.symm).symm hcSmall
  exact IsColimit.ofIsoColimit hc (Cocone.ext (Iso.refl F) fun _ => Category.comp_id _)

universe v

/-- **Two quasi-coherent submodules of finite type lie in a common one.** The quasi-coherent
submodules of finite type of a quasi-coherent module form a filtered diagram, so any two of them
admit an upper bound that is again quasi-coherent and of finite type. -/
theorem exists_finiteTypeQuasicoherentSubobject_sup {X : Scheme.{u}} {F : X.Modules}
    [F.IsQuasicoherent] {A B : Subobject F}
    (hAqc : (A : X.Modules).IsQuasicoherent) (hAft : (A : X.Modules).IsFiniteType)
    (hBqc : (B : X.Modules).IsQuasicoherent) (hBft : (B : X.Modules).IsFiniteType) :
    ∃ C : Subobject F, (C : X.Modules).IsQuasicoherent ∧ (C : X.Modules).IsFiniteType ∧
      A ≤ C ∧ B ≤ C := by
  let P := finiteTypeQuasicoherentSubobjectProperty F
  let a : FiniteTypeQuasicoherentSubobject F := ⟨A, hAqc, hAft⟩
  let b : FiniteTypeQuasicoherentSubobject F := ⟨B, hBqc, hBft⟩
  exact ⟨(IsFiltered.max a b).1, (IsFiltered.max a b).2.1, (IsFiltered.max a b).2.2,
    leOfHom (P.ι.map (IsFiltered.leftToMax a b)), leOfHom (P.ι.map (IsFiltered.rightToMax a b))⟩

/-- **Finitely many sections over quasi-compact opens come from a single quasi-coherent submodule
of finite type.** On a quasi-compact and quasi-separated scheme, let `F` be a quasi-coherent
module, let `W` be a family of quasi-compact opens and let a section of `F` over `W j` be given
for every `j` in a finite set `t`. Then one quasi-coherent submodule of `F` of finite type
carries all of them.

This is [Stacks, Tag 01PG] in the form its consumers use: the diagram of quasi-coherent
submodules of finite type is filtered, so the one-section statement
`AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_section` can be amalgamated over a
finite index set. -/
theorem exists_finiteTypeQuasicoherentSubobject_finset_sections {X : Scheme.{u}} (F : X.Modules)
    [CompactSpace X] [QuasiSeparatedSpace X] [F.IsQuasicoherent]
    {ι : Type v} (W : ι → X.Opens) (hW : ∀ j, IsCompact (W j : Set X))
    (s : ∀ j, Γ(F, W j)) (t : Finset ι) :
    ∃ G : Subobject F, (G : X.Modules).IsQuasicoherent ∧ (G : X.Modules).IsFiniteType ∧
      ∀ j ∈ t, ∃ u : Γ((G : X.Modules), W j), G.arrow.app (W j) u = s j := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      obtain ⟨z⟩ := IsFiltered.nonempty (C := FiniteTypeQuasicoherentSubobject F)
      exact ⟨z.1, z.2.1, z.2.2, by simp⟩
  | @insert j t _ ih =>
      obtain ⟨G, hGqc, hGft, hG⟩ := ih
      obtain ⟨H, hHqc, hHft, v, hv⟩ :=
        exists_finiteTypeQuasicoherentSubobject_section F (W j) (hW j) (s j)
      obtain ⟨C, hCqc, hCft, hGC, hHC⟩ :=
        exists_finiteTypeQuasicoherentSubobject_sup hGqc hGft hHqc hHft
      refine ⟨C, hCqc, hCft, fun k hk => ?_⟩
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact (exists_section_of_le hHC (W k) v).imp fun w hw => hw.trans hv
      · obtain ⟨u, hu⟩ := hG k hk
        exact (exists_section_of_le hGC (W k) u).imp fun w hw => hw.trans hu

/-- **Finitely many sections over quasi-compact opens come from a single quasi-coherent submodule
of finite type**, indexed by a finite type rather than by a finite subset. -/
theorem exists_finiteTypeQuasicoherentSubobject_sections {X : Scheme.{u}} (F : X.Modules)
    [CompactSpace X] [QuasiSeparatedSpace X] [F.IsQuasicoherent]
    {ι : Type v} [Finite ι] (W : ι → X.Opens) (hW : ∀ j, IsCompact (W j : Set X))
    (s : ∀ j, Γ(F, W j)) :
    ∃ G : Subobject F, (G : X.Modules).IsQuasicoherent ∧ (G : X.Modules).IsFiniteType ∧
      ∀ j, ∃ u : Γ((G : X.Modules), W j), G.arrow.app (W j) u = s j := by
  classical
  cases nonempty_fintype ι
  obtain ⟨G, hqc, hft, h⟩ :=
    exists_finiteTypeQuasicoherentSubobject_finset_sections F W hW s Finset.univ
  exact ⟨G, hqc, hft, fun j => h j (Finset.mem_univ j)⟩

/-- **A finite type quasi-coherent submodule inside a prescribed one, carrying finitely many
given sections.** Let `I` be a quasi-coherent submodule of `F` on a quasi-compact and
quasi-separated scheme, and let a section of `I` over a quasi-compact open `W j` be given for
each `j` in a finite index type. Then there is a quasi-coherent submodule `G ≤ I` of finite type
whose sections already account for all of them inside `F`. -/
theorem exists_finiteTypeQuasicoherentSubobject_le_sections {X : Scheme.{u}} {F : X.Modules}
    [CompactSpace X] [QuasiSeparatedSpace X] (I : Subobject F)
    (hI : (I : X.Modules).IsQuasicoherent)
    {ι : Type v} [Finite ι] (W : ι → X.Opens) (hW : ∀ j, IsCompact (W j : Set X))
    (s : ∀ j, Γ((I : X.Modules), W j)) :
    ∃ G : Subobject F, G ≤ I ∧ (G : X.Modules).IsQuasicoherent ∧
      (G : X.Modules).IsFiniteType ∧
      ∀ j, ∃ u : Γ((G : X.Modules), W j),
        G.arrow.app (W j) u = I.arrow.app (W j) (s j) := by
  obtain ⟨G, hGqc, hGft, hG⟩ :=
    exists_finiteTypeQuasicoherentSubobject_sections (I : X.Modules) W hW s
  have : Mono (G.arrow ≫ I.arrow) := mono_comp _ _
  let e : ((Subobject.mk (G.arrow ≫ I.arrow) : Subobject F) : X.Modules) ≅ (G : X.Modules) :=
    Subobject.underlyingIso (G.arrow ≫ I.arrow)
  refine ⟨Subobject.mk (G.arrow ≫ I.arrow), Subobject.mk_le_of_comm G.arrow rfl,
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm hGqc,
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} e.symm, fun j => ?_⟩
  obtain ⟨u, hu⟩ := hG j
  refine ⟨e.inv.app (W j) u, ?_⟩
  change ((e.inv ≫ (Subobject.mk (G.arrow ≫ I.arrow)).arrow).app (W j)) u = _
  rw [Subobject.underlyingIso_arrow]
  change I.arrow.app (W j) (G.arrow.app (W j) u) = _
  rw [hu]

end AlgebraicGeometry
