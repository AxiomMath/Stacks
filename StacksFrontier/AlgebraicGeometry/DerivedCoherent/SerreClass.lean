module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeColimit
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Properties.GabberResult.Abelian
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeGeneration
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectColimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coherent modules form a Serre subcategory of the quasi-coherent modules

Let `X` be a scheme. The quasi-coherent `𝒪_X`-modules form an abelian category `QCoh(𝒪_X)`,
and the coherent ones a full subcategory of it. This file records that the inclusion
`Coh(𝒪_X) ⥤ QCoh(𝒪_X)` is exact, that on a locally Noetherian scheme coherence is a Serre
class in `QCoh(𝒪_X)` — closed under subobjects, quotients and extensions — and that on a
Noetherian scheme the Serre class has *enough subobjects*: every epimorphism of quasi-coherent
modules with coherent target is already hit by a coherent submodule of its source.

That last property is what the comparison of derived categories needs, and it is the only
assertion here with real content. It is proved from the filtered system of quasi-coherent
submodules of finite type: the module is their colimit, their images in the target exhaust it,
and a coherent target is of finite type, so a single stage already surjects.

## Main definitions

* `AlgebraicGeometry.coherentToQuasicoherent` is the inclusion of the coherent `𝒪_X`-modules
  into the quasi-coherent ones.
* `AlgebraicGeometry.coherentInQuasicoherent` is coherence, read as a property of objects of
  `QCoh(𝒪_X)`.

## Main results

* `AlgebraicGeometry.coherentInQuasicoherent_isSerreClass`: on a locally Noetherian scheme the
  coherent modules are a Serre class in `QCoh(𝒪_X)`.
* `AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_epi_comp`: on a Noetherian scheme,
  an epimorphism onto a coherent module from a quasi-coherent module stays epimorphic after
  restriction to a suitable quasi-coherent submodule of finite type of its source.
* `AlgebraicGeometry.exists_coherent_epi_comp`: the same statement inside `QCoh(𝒪_X)`, in the
  form the derived-category comparison consumes.

## Implementation notes

Coherence exists in the library both as `SheafOfModules.IsCoherent` and, for the closure
theory, as `Stacks.SheafOfModules.IsCoherent`; the two are identified in
`StacksFrontier/AlgebraicGeometry/CoherentAbelian/Basic.lean`, whose transported package is what
is used here. All statements are phrased for `SheafOfModules.{u} X.ringCatSheaf`, the type at
which `SheafOfModules.isQuasicoherent` and Mathlib's full-subcategory machinery are stated.
`AlgebraicGeometry.Scheme.Modules` is a definitional copy of that type carrying its own
`Category` instance, so results proved there — the subobject and colimit material in
particular — are applied by explicit application rather than through instance search, which
does not see through the copy.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 02MP](https://stacks.math.columbia.edu/tag/02MP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped ZeroObject

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-! ### Exactness of the inclusion of the quasi-coherent modules -/

/-- The inclusion of the quasi-coherent `𝒪_X`-modules into all `𝒪_X`-modules preserves finite
limits: the quasi-coherent modules are a weak Serre subcategory. -/
instance preservesFiniteLimits_quasicoherentι :
    PreservesFiniteLimits (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι :=
  ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _

/-- The inclusion of the quasi-coherent `𝒪_X`-modules into all `𝒪_X`-modules preserves finite
colimits: the quasi-coherent modules are a weak Serre subcategory. -/
instance preservesFiniteColimits_quasicoherentι :
    PreservesFiniteColimits (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι :=
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _

/-- The inclusion of the quasi-coherent `𝒪_X`-modules into all `𝒪_X`-modules preserves
monomorphisms, being left exact. -/
instance preservesMonomorphisms_quasicoherentι :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.PreservesMonomorphisms :=
  ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory _

/-- The inclusion of the quasi-coherent `𝒪_X`-modules into all `𝒪_X`-modules preserves
epimorphisms, being right exact. -/
instance preservesEpimorphisms_quasicoherentι :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.PreservesEpimorphisms :=
  ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory _

/-! ### The inclusion of the coherent modules into the quasi-coherent ones -/

/-- Coherence, read as a property of objects of the category `QCoh(𝒪_X)` of quasi-coherent
`𝒪_X`-modules. -/
abbrev coherentInQuasicoherent :
    ObjectProperty (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  fun M => M.obj.IsCoherent

/-- **Stacks Project, Tag 02MP.** The inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` of the coherent
`𝒪_X`-modules into the quasi-coherent ones, available because a coherent module is
quasi-coherent. -/
def coherentToQuasicoherent :
    SheafOfModules.CoherentModules X.ringCatSheaf ⥤
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  ObjectProperty.ιOfLE fun M hM =>
    have : M.IsCoherent := hM
    isQuasicoherent_of_isCoherent M

/-- The inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` preserves finite limits: it does so after composing
with the exact inclusion of `QCoh(𝒪_X)` into all `𝒪_X`-modules, and that inclusion reflects
limits. -/
instance preservesFiniteLimits_coherentToQuasicoherent :
    PreservesFiniteLimits (coherentToQuasicoherent X) :=
  have : PreservesFiniteLimits (coherentToQuasicoherent X ⋙
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι) := by
    change PreservesFiniteLimits
      (ObjectProperty.ι (fun M : _root_.SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent))
    infer_instance
  preservesFiniteLimits_of_reflects_of_preserves (coherentToQuasicoherent X)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι

/-- The inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` preserves finite colimits: it does so after composing
with the exact inclusion of `QCoh(𝒪_X)` into all `𝒪_X`-modules, and that inclusion reflects
colimits. -/
instance preservesFiniteColimits_coherentToQuasicoherent :
    PreservesFiniteColimits (coherentToQuasicoherent X) :=
  have : PreservesFiniteColimits (coherentToQuasicoherent X ⋙
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι) := by
    change PreservesFiniteColimits
      (ObjectProperty.ι (fun M : _root_.SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent))
    infer_instance
  preservesFiniteColimits_of_reflects_of_preserves (coherentToQuasicoherent X)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι

/-- The inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` is the identity on morphisms, so it preserves the
zero morphisms. -/
instance preservesZeroMorphisms_coherentToQuasicoherent :
    (coherentToQuasicoherent X).PreservesZeroMorphisms :=
  ⟨fun _ _ => rfl⟩

/-- **Stacks Project, Tag 02MP.** The inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` is additive, being
exact. -/
instance additive_coherentToQuasicoherent : (coherentToQuasicoherent X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-! ### Coherence is a Serre class in the quasi-coherent modules -/

/-- The zero quasi-coherent module is coherent. -/
instance containsZero_coherentInQuasicoherent :
    (coherentInQuasicoherent X).ContainsZero := by
  refine ⟨0, isZero_zero _, ?_⟩
  exact ObjectProperty.prop_of_isZero
    (fun M : _root_.SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent)
    (Functor.map_isZero (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι (isZero_zero _))

/-- **Stacks Project, Tag 01Y1.** On a locally Noetherian scheme a quasi-coherent submodule of
a coherent module is coherent. -/
instance isClosedUnderSubobjects_coherentInQuasicoherent [IsLocallyNoetherian X] :
    (coherentInQuasicoherent X).IsClosedUnderSubobjects where
  prop_of_mono {M N} f _ hN :=
    have hm : Mono ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.map f) :=
      Functor.map_mono _ f
    @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono X _ N.obj M.obj hN
      M.property ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.map f) hm

/-- **Stacks Project, Tag 01Y1.** On a locally Noetherian scheme a quasi-coherent quotient of a
coherent module is coherent. -/
instance isClosedUnderQuotients_coherentInQuasicoherent [IsLocallyNoetherian X] :
    (coherentInQuasicoherent X).IsClosedUnderQuotients where
  prop_of_epi {M N} f _ hM :=
    have he : Epi ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.map f) :=
      Functor.map_epi _ f
    @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_epi X _ M.obj N.obj hM
      N.property ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.map f) he

/-- **Stacks Project, Tag 01BY (4).** An extension of coherent quasi-coherent modules is
coherent: the inclusion of `QCoh(𝒪_X)` is exact, so it carries the short exact sequence to one
of `𝒪_X`-modules, where coherence is closed under extensions. -/
instance isClosedUnderExtensions_coherentInQuasicoherent :
    (coherentInQuasicoherent X).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ :=
    ObjectProperty.prop_X₂_of_shortExact
      (P := fun M : _root_.SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent)
      (hS.map_of_exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι) h₁ h₃

/-- **Stacks Project, Tag 02MP.** On a locally Noetherian scheme the coherent modules are a
Serre class in the category of quasi-coherent modules. -/
instance coherentInQuasicoherent_isSerreClass [IsLocallyNoetherian X] :
    (coherentInQuasicoherent X).IsSerreClass where

/-! ### Enough coherent subobjects -/

/-- On a quasi-compact scheme, a module of finite type is not the supremum of a monotone family
of proper subobjects indexed by a small nonempty directed order. -/
theorem exists_eq_top_of_iSup_eq_top_of_monotone [CompactSpace X] {F : X.Modules}
    [F.IsFiniteType] {K : Type u} [Preorder K] [Nonempty K] [IsDirectedOrder K]
    (P : K → Subobject F) (hP : Monotone P) (hsup : ⨆ A, P A = ⊤) : ∃ A, P A = ⊤ := by
  let Fmono : K ⥤ MonoOver F :=
    { obj := fun A => Subobject.representative.obj (P A)
      map := fun h => Subobject.representative.map (homOfLE (hP (leOfHom h)))
      map_id _ := Subsingleton.elim _ _
      map_comp _ _ := Subsingleton.elim _ _ }
  let cOver : Cocone (Fmono ⋙ MonoOver.forget F) := Cocone.mk (Over.mk (𝟙 F))
    { app := fun A => Over.homMk (Fmono.obj A).arrow
      naturality := fun A B h => by
        apply Over.OverMorphism.ext
        dsimp [Fmono]
        exact MonoOver.w (Fmono.map h) }
  have : Mono cOver.pt.hom := by
    dsimp [cOver]
    infer_instance
  have hrep : ∀ A, Subobject.mk (Fmono.obj A).arrow = P A := fun A =>
    Subobject.thinSkeleton_mk_representative_eq_self _
  have hsup' : Subobject.mk cOver.pt.hom = ⨆ A : K, Subobject.mk (Fmono.obj A).arrow :=
    calc
      Subobject.mk cOver.pt.hom = ⊤ := (Subobject.top_eq_id F).symm
      _ = ⨆ A : K, P A := hsup.symm
      _ = ⨆ A : K, Subobject.mk (Fmono.obj A).arrow := iSup_congr fun A => (hrep A).symm
  have hcol : IsColimit ((Over.forget F).mapCocone cOver) :=
    IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup Fmono cOver hsup'
  let D := Fmono ⋙ MonoOver.forget F ⋙ Over.forget F
  let cD := (Over.forget F).mapCocone cOver
  have hcDpt : cD.pt.IsFiniteType := ‹F.IsFiniteType›
  let eCol := IsColimit.coconePointUniqueUpToIso (colimit.isColimit D) hcol
  have hcolFT : (colimit D).IsFiniteType := isFiniteType_of_iso_modules eCol hcDpt
  obtain ⟨A, hA⟩ := @Stacks.SheafOfModules.exists_epi_to_colimit_of_isFiniteType
    _ X.ringCatSheaf _ _ _ _ K _ _ _ _ D hcolFT
  have hfac : colimit.ι D A ≫ eCol.hom = cD.ι.app A :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit D) hcol A
  have : Epi (cD.ι.app A) := hfac ▸ epi_comp' hA inferInstance
  have : Mono (cD.ι.app A) := (Fmono.obj A).property
  exact ⟨A, hrep A ▸ (Subobject.epi_iff_mk_eq_top (cD.ι.app A)).mp inferInstance⟩

/-- On a quasi-compact scheme, a nonempty directed set of subobjects of a module of finite type
with supremum `⊤` contains `⊤`. -/
theorem top_mem_of_directedOn_of_sSup_eq_top [CompactSpace X] {F : X.Modules}
    [F.IsFiniteType] {s : Set (Subobject F)} (hne : s.Nonempty) (hs : DirectedOn (· ≤ ·) s)
    (hsup : sSup s = ⊤) : ⊤ ∈ s := by
  have : Nonempty s := hne.to_subtype
  have : IsDirectedOrder s := ⟨fun a b => by
    obtain ⟨c, hc, hac, hbc⟩ := hs a a.2 b b.2
    exact ⟨⟨c, hc⟩, hac, hbc⟩⟩
  let e := equivSmallModel.{u} s
  let K := CategoryTheory.SmallModel.{u} s
  let toSmallObj : s → K := e.functor.obj
  let fromSmallObj : K → s := e.symm.functor.obj
  have hunit : ∀ i : s, i.1 ≤ (fromSmallObj (toSmallObj i)).1 := fun i =>
    leOfHom (e.unitIso.app i).hom
  let : Preorder K :=
    { le A B := (fromSmallObj A).1 ≤ (fromSmallObj B).1
      le_refl _ := le_rfl
      le_trans _ _ _ h₁ h₂ := le_trans h₁ h₂ }
  have : Nonempty K := ⟨toSmallObj (Classical.arbitrary s)⟩
  have : IsDirectedOrder K := ⟨fun A B => by
    obtain ⟨C, hAC, hBC⟩ := exists_ge_ge (fromSmallObj A) (fromSmallObj B)
    exact ⟨toSmallObj C, (Subtype.coe_le_coe.mpr hAC).trans (hunit C),
      (Subtype.coe_le_coe.mpr hBC).trans (hunit C)⟩⟩
  have hle : sSup s ≤ ⨆ A : K, (fromSmallObj A).1 := sSup_le fun a ha =>
    (hunit ⟨a, ha⟩).trans (le_iSup (fun A : K => (fromSmallObj A).1) (toSmallObj ⟨a, ha⟩))
  obtain ⟨A, hA : (fromSmallObj A).1 = ⊤⟩ := exists_eq_top_of_iSup_eq_top_of_monotone X
    (fun A : K => (fromSmallObj A).1) (fun _ _ h => h) (top_unique (hsup ▸ hle))
  exact hA ▸ (fromSmallObj A).2

/-- On a quasi-compact quasi-separated scheme, the images of the quasi-coherent submodules of
finite type of a quasi-coherent module under an epimorphism are contained in no proper
subobject of the target. -/
theorem eq_top_of_forall_imageSubobject_le [CompactSpace X] [QuasiSeparatedSpace X]
    {G F : X.Modules} [G.IsQuasicoherent] (f : G ⟶ F) [Epi f] (M : Subobject F)
    (hM : ∀ S : FiniteTypeQuasicoherentSubobject G, imageSubobject (S.obj.arrow ≫ f) ≤ M) :
    M = ⊤ := by
  let t : ∀ S : FiniteTypeQuasicoherentSubobject G, (Subobject.underlying.obj S.obj : X.Modules) ⟶
      (Subobject.underlying.obj M : X.Modules) := fun S =>
    factorThruImageSubobject (S.obj.arrow ≫ f) ≫ Subobject.ofLE _ M (hM S)
  have ht : ∀ S, t S ≫ M.arrow = S.obj.arrow ≫ f := fun S => by
    simp only [t, Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]
  have hnat : ∀ {S T : FiniteTypeQuasicoherentSubobject G} (p : S ⟶ T),
      Subobject.underlying.map p.hom ≫ t T = t S := by
    intro S T p
    apply (cancel_mono M.arrow).1
    rw [Category.assoc, ht T, ht S, ← Category.assoc, Subobject.underlying_arrow]
  let d : Cocone (finiteTypeQuasicoherentSubobjectFunctor G) :=
    Cocone.mk (Subobject.underlying.obj M)
      { app := t
        naturality := fun {S T} p => (hnat p).trans (Category.comp_id (t S)).symm }
  let hc := isColimit_finiteTypeQuasicoherentSubobjectCocone G
  have hgf : hc.desc d ≫ M.arrow = f := hc.hom_ext fun S => by
    rw [← Category.assoc, hc.fac d S]
    exact ht S
  have : Epi (hc.desc d ≫ M.arrow) := hgf ▸ ‹Epi f›
  have : Epi M.arrow := epi_of_epi (hc.desc d) M.arrow
  simpa using (Subobject.epi_iff_mk_eq_top M.arrow).mp this

/-- **Stacks Project, Tag 02MP**, the module-level form. On a Noetherian scheme, an
epimorphism from a quasi-coherent module onto a coherent one stays an epimorphism after
restriction to a suitable quasi-coherent submodule of finite type of its source.

The source is the filtered colimit of its quasi-coherent submodules of finite type
([Stacks, Tag 01PG]), so the images of those submodules in the target have supremum the whole
target. The target is coherent, hence of finite type, so one stage of that filtered system
already surjects onto it ([Stacks, Tag 01BB]). -/
@[sga "6 II 2.1.1" "a)"]
theorem exists_finiteTypeQuasicoherentSubobject_epi_comp [IsNoetherian X]
    {G F : X.Modules} [G.IsQuasicoherent] [F.IsCoherent] (f : G ⟶ F) [Epi f] :
    ∃ S : FiniteTypeQuasicoherentSubobject G, Epi (S.obj.arrow ≫ f) := by
  classical
  have : Nonempty (FiniteTypeQuasicoherentSubobject G) := IsFiltered.nonempty
  let img : FiniteTypeQuasicoherentSubobject G → Subobject F := fun S =>
    imageSubobject (S.obj.arrow ≫ f)
  have hmono : ∀ {S U : FiniteTypeQuasicoherentSubobject G}, (S ⟶ U) → img S ≤ img U :=
    fun h => by
      dsimp [img]
      rw [← Subobject.ofLE_arrow (leOfHom h.hom)]
      exact imageSubobject_comp_le _ _
  have : F.IsFiniteType := (show F.IsQuasicoherent ∧ F.IsFiniteType from
    ((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X F).out 1 2).mp ‹F.IsCoherent›).2
  obtain ⟨S, hS⟩ := top_mem_of_directedOn_of_sSup_eq_top X (s := Set.range img)
    (Set.range_nonempty img)
    (by
      rintro _ ⟨S, rfl⟩ _ ⟨T, rfl⟩
      obtain ⟨U, hSU, hTU, -⟩ := IsFilteredOrEmpty.cocone_objs S T
      exact ⟨img U, ⟨U, rfl⟩, hmono hSU, hmono hTU⟩)
    (eq_top_of_forall_imageSubobject_le X f _ fun S => le_sSup ⟨S, rfl⟩)
  refine ⟨S, ?_⟩
  have : Epi (imageSubobject (S.obj.arrow ≫ f)).arrow :=
    (Subobject.epi_iff_mk_eq_top _).2 (by simpa [img] using hS)
  simpa using (inferInstance : Epi (factorThruImageSubobject (S.obj.arrow ≫ f) ≫
    (imageSubobject (S.obj.arrow ≫ f)).arrow))

/-- **Stacks Project, Tag 02MP.** On a Noetherian scheme, an epimorphism of quasi-coherent
`𝒪_X`-modules whose target is coherent stays an epimorphism after restriction to a suitable
coherent submodule of its source: the coherent modules have enough subobjects in `QCoh(𝒪_X)`.
This is the hypothesis under which the inclusion induces an equivalence of bounded above
derived categories. -/
theorem exists_coherent_epi_comp [IsNoetherian X]
    ⦃M N : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory⦄ (f : M ⟶ N)
    (hf : Epi f) (hN : coherentInQuasicoherent X N) :
    ∃ (M' : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (g : M' ⟶ M),
      coherentInQuasicoherent X M' ∧ Epi (g ≫ f) := by
  let G : X.Modules := M.obj
  let F' : X.Modules := N.obj
  let g : G ⟶ F' := (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.map f
  have hg : Epi g := Functor.map_epi (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι f
  obtain ⟨S, hS⟩ := @exists_finiteTypeQuasicoherentSubobject_epi_comp X _ G F'
    M.property hN g hg
  have hSc : (S.obj : X.Modules).IsCoherent :=
    @Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType
      X _ (S.obj : X.Modules) S.property.1 S.property.2
  refine ⟨⟨(S.obj : X.Modules), S.property.1⟩, ObjectProperty.homMk S.obj.arrow, hSc, ?_⟩
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.epi_of_epi_map hS

end AlgebraicGeometry

end
