module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits

/-!
# Restriction of sheaves of modules between slice sites

Let `H : C ⥤ D` be a functor between sites which is both continuous and cocontinuous, and let
`φ : S ⟶ H_* R` be a morphism of sheaves of rings over it.  Then the restriction functor
`SheafOfModules.pushforward φ` preserves all colimits indexed in the universe of the module
sections.  In particular, for an arrow `f : X ⟶ Y` of a site, restriction
`SheafOfModules.overMap R f` from the slice over `Y` to the slice over `X` preserves all colimits.

The file also compares a slice site with an iterated slice site: for `V` an object of the slice
over `U`, `sliceEquiv` is the equivalence of the categories of sheaves of modules on the iterated
slice over `V` and on the slice over `V.left` induced by `Over.iteratedSliceEquiv V`.

## Main results

* `Stacks.SheafOfModules.sheafificationWhiskerIso`: sheafification commutes with restriction of
  abelian presheaves along a continuous cocontinuous functor.
* `Stacks.SheafOfModules.sheafPushforward_preservesColimits`: restriction of abelian sheaves
  along a continuous cocontinuous functor preserves colimits.
* `Stacks.SheafOfModules.pushforward_preservesColimits`: restriction of sheaves of modules
  along such a functor preserves colimits.
* `Stacks.SheafOfModules.overMap_preservesColimits`: restriction of sheaves of modules between
  slice sites preserves colimits.
* `Stacks.SheafOfModules.sliceEquiv`, `Stacks.SheafOfModules.sliceEquivObjIso` and
  `Stacks.SheafOfModules.sliceEquivUnitIso`: the comparison of a module on an iterated slice
  site with the same module on the slice over the base object.
* `Stacks.SheafOfModules.isColimitCofanTransport`: a presentation as a coproduct of copies of
  the structure sheaf travels along an equivalence matching the two structure sheaves.
* `Stacks.SheafOfModules.coversTop_over_of_ofArrows_mem` and
  `Stacks.SheafOfModules.coversTop_ulift_self`: a family generating a covering sieve of `U`
  covers the terminal object of the slice site over `U`, and the family of all objects of a site
  covers its terminal object.

## References

* [Stacks Project, Tag 03DB](https://stacks.math.columbia.edu/tag/03DB)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w t u' v' u₁ v₁ u₂ v₂ r

namespace Stacks.SheafOfModules

/-- Let `L ⊣ U` be an adjunction with `U` fully faithful. A functor `H` out of the codomain of `L`
preserves colimits of a given shape as soon as `L ⋙ H` does. -/
private lemma preservesColimitsOfShape_of_reflection
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (L : A ⥤ B) (U : B ⥤ A) (adj : L ⊣ U) [U.Full] [U.Faithful]
    (H : B ⥤ D) {I : Type*} [Category* I] [HasColimitsOfShape I A]
    [PreservesColimitsOfShape I (L ⋙ H)] : PreservesColimitsOfShape I H := by
  have : L.IsLeftAdjoint := adj.isLeftAdjoint
  constructor
  intro F
  let ht := colimit.isColimit (F ⋙ U)
  have : PreservesColimit ((F ⋙ U) ⋙ L) H :=
    preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves L ht)
      (isColimitOfPreserves (L ⋙ H) ht)
  exact preservesColimit_of_iso_diagram H
    (Functor.associator F U L ≪≫ Functor.isoWhiskerLeft F (asIso adj.counit) ≪≫
      F.rightUnitor)

/-- Sheafification of presheaves of abelian groups commutes with restriction along a continuous
cocontinuous functor of sites. -/
noncomputable def sheafificationWhiskerIso
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (H : C ⥤ D) [H.IsContinuous J K] [H.IsCocontinuous J K] :
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{w}).obj H.op ⋙
        presheafToSheaf J AddCommGrpCat.{w} ≅
      presheafToSheaf K AddCommGrpCat.{w} ⋙ H.sheafPushforwardContinuous _ J K := by
  let η : (Functor.whiskeringLeft _ _ AddCommGrpCat.{w}).obj H.op ⋙
        presheafToSheaf J AddCommGrpCat.{w} ⟶
      presheafToSheaf K AddCommGrpCat.{w} ⋙ H.sheafPushforwardContinuous _ J K :=
    { app P := ⟨sheafifyLift J (Functor.whiskerLeft H.op (toSheafify K P))
        ((H.sheafPushforwardContinuous _ J K).obj ((presheafToSheaf K _).obj P)).property⟩
      naturality P Q f := by
        apply (sheafToPresheaf J AddCommGrpCat.{w}).map_injective
        change sheafifyMap J (Functor.whiskerLeft H.op f) ≫
          sheafifyLift J (Functor.whiskerLeft H.op (toSheafify K Q))
            (H.op_comp_isSheaf J K ((presheafToSheaf K _).obj Q)) =
          sheafifyLift J (Functor.whiskerLeft H.op (toSheafify K P))
            (H.op_comp_isSheaf J K ((presheafToSheaf K _).obj P)) ≫
            Functor.whiskerLeft H.op (sheafifyMap K f)
        rw [sheafifyMap_sheafifyLift, ← sheafifyLift_comp]
        · congr 1
          rw [← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp, toSheafify_naturality]
        · exact H.op_comp_isSheaf J K ((presheafToSheaf K _).obj Q) }
  have (P : Dᵒᵖ ⥤ AddCommGrpCat.{w}) : IsIso (η.app P) := by
    have : Presheaf.IsLocallyInjective K (toSheafify K P) :=
      (K.W_toSheafify P).isLocallyInjective
    have : Presheaf.IsLocallySurjective K (toSheafify K P) :=
      (K.W_toSheafify P).isLocallySurjective
    have : Presheaf.IsLocallyInjective J (Functor.whiskerLeft H.op (toSheafify K P)) :=
      Presheaf.isLocallyInjective_whisker J K H _
    have : Presheaf.IsLocallySurjective J (Functor.whiskerLeft H.op (toSheafify K P)) :=
      Presheaf.isLocallySurjective_whisker J K H _
    apply (J.W_sheafToPresheaf_map_iff_isIso (η.app P)).mp
    have h := (J.W_iff_isLocallyBijective
      (Functor.whiskerLeft H.op (toSheafify K P))).mpr ⟨inferInstance, inferInstance⟩
    have hfac : toSheafify J (H.op ⋙ P) ≫ (η.app P).hom =
        Functor.whiskerLeft H.op (toSheafify K P) :=
      toSheafify_sheafifyLift J _ _
    rw [← hfac] at h
    exact J.W.of_precomp (W' := J.W) _ _ (J.W_toSheafify _) h
  exact NatIso.ofComponents (fun P => asIso (η.app P)) (fun {P Q} f => η.naturality f)

/-- Restriction of sheaves of abelian groups along a continuous cocontinuous functor of sites
preserves colimits. -/
lemma sheafPushforward_preservesColimits
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (H : C ⥤ D) [H.IsContinuous J K] [H.IsCocontinuous J K] :
    PreservesColimitsOfSize.{w, w} (H.sheafPushforwardContinuous AddCommGrpCat.{w} J K) := by
  have : PreservesColimitsOfSize.{w, w} (presheafToSheaf K AddCommGrpCat.{w} ⋙
      H.sheafPushforwardContinuous AddCommGrpCat.{w} J K) :=
    preservesColimits_of_natIso (sheafificationWhiskerIso J K H)
  constructor
  intro I _
  exact preservesColimitsOfShape_of_reflection _ _
    (sheafificationAdjunction K AddCommGrpCat.{w}) _

/-- Restriction of sheaves of modules along a continuous cocontinuous functor of sites preserves
colimits. -/
lemma pushforward_preservesColimits
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (H : C ⥤ D) [H.IsContinuous J K] [H.IsCocontinuous J K]
    {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}}
    (φ : S ⟶ (H.sheafPushforwardContinuous RingCat.{r} J K).obj R) :
    PreservesColimitsOfSize.{w, w} (SheafOfModules.pushforward.{w} φ) := by
  have : PreservesColimitsOfSize.{w, w} (H.sheafPushforwardContinuous AddCommGrpCat.{w} J K) :=
    sheafPushforward_preservesColimits J K H
  have : PreservesColimitsOfSize.{w, w} (SheafOfModules.toSheaf.{w} R) :=
    preservesColimitsOfSize_shrink _
  have : PreservesColimitsOfSize.{w, w} (SheafOfModules.toSheaf.{w} S) :=
    preservesColimitsOfSize_shrink _
  have : PreservesColimitsOfSize.{w, w}
      (SheafOfModules.pushforward.{w} φ ⋙ SheafOfModules.toSheaf.{w} S) :=
    inferInstanceAs (PreservesColimitsOfSize.{w, w}
      (SheafOfModules.toSheaf.{w} R ⋙ H.sheafPushforwardContinuous AddCommGrpCat.{w} J K))
  have : ReflectsColimitsOfSize.{w, w} (SheafOfModules.toSheaf.{w} S) :=
    reflectsColimits_of_reflectsIsomorphisms
  exact preservesColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{w} S)

/-- Restriction of sheaves of modules from the slice site over `Y` to the slice site over `X`
along an arrow `f : X ⟶ Y` preserves colimits. -/
lemma overMap_preservesColimits {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) {X Y : C} (f : X ⟶ Y)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{w}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify (J.over Y) AddCommGrpCat.{w}]
    [(J.over Y).WEqualsLocallyBijective AddCommGrpCat.{w}] :
    PreservesColimitsOfSize.{w, w} (SheafOfModules.overMap.{w} R f) :=
  pushforward_preservesColimits (Over.map f) _

/-- The equivalence between sheaves of modules on the slice site over `V.left` and sheaves of
modules on the iterated slice site over `V`, induced by `Over.iteratedSliceEquiv`. -/
noncomputable def sliceEquiv {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) (U : C) (V : Over U) :
    SheafOfModules.{w} (R.over V.left) ≌ SheafOfModules.{w} ((R.over U).over V) :=
  SheafOfModules.pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv V)
    (S := (R.over U).over V) (R := R.over V.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)

/-- Under `sliceEquiv`, the restriction of `M` to the slice over `V.left` corresponds to its
restriction to the iterated slice over `V`.  Both have the same sections. -/
noncomputable def sliceEquivObjIso {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R) (U : C)
    (V : Over U) :
    (sliceEquiv R U V).functor.obj (M.over V.left) ≅ (M.over U).over V := by
  apply (SheafOfModules.fullyFaithfulForget ((R.over U).over V)).preimageIso
  dsimp [sliceEquiv, SheafOfModules.pushforwardPushforwardEquivalence,
    SheafOfModules.pushforward]
  exact PresheafOfModules.isoMk (fun _ => Iso.refl _) fun _ _ _ => rfl

/-- `sliceEquiv` matches up the two structure sheaves. -/
noncomputable def sliceEquivUnitIso {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w}) (U : C) (V : Over U) :
    (sliceEquiv R U V).functor.obj (SheafOfModules.unit (R.over V.left)) ≅
      SheafOfModules.unit ((R.over U).over V) := by
  apply (SheafOfModules.fullyFaithfulForget ((R.over U).over V)).preimageIso
  dsimp [sliceEquiv, SheafOfModules.pushforwardPushforwardEquivalence,
    SheafOfModules.pushforward]
  exact PresheafOfModules.isoMk (fun _ => Iso.refl _) fun _ _ _ => rfl

/-- An equivalence of categories of sheaves of modules which matches up the two structure
sheaves carries a presentation of a module as a coproduct of copies of the structure sheaf to
such a presentation of the corresponding module. -/
noncomputable def isColimitCofanTransport
    {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁} {R₁ : Sheaf J₁ RingCat.{w}}
    {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂} {R₂ : Sheaf J₂ RingCat.{w}}
    (e : SheafOfModules.{w} R₁ ≌ SheafOfModules.{w} R₂)
    {M : SheafOfModules.{w} R₁} {N : SheafOfModules.{w} R₂}
    (η : e.functor.obj (SheafOfModules.unit R₁) ≅ SheafOfModules.unit R₂)
    (ρ : e.functor.obj M ≅ N)
    {B : Type*} (ι : B → (SheafOfModules.unit R₁ ⟶ M))
    (hc : IsColimit (Cofan.mk M ι)) :
    IsColimit (Cofan.mk N (fun b => η.inv ≫ e.functor.map (ι b) ≫ ρ.hom)) := by
  let F₀ : Discrete B ⥤ SheafOfModules.{w} R₂ :=
    Discrete.functor (fun _ => SheafOfModules.unit R₁) ⋙ e.functor
  let F₁ : Discrete B ⥤ SheafOfModules.{w} R₂ :=
    Discrete.functor (fun _ => SheafOfModules.unit R₂)
  let α : F₀ ≅ F₁ := Discrete.natIso (fun _ => η)
  let c := e.functor.mapCocone (Cofan.mk M ι)
  let d := Cofan.mk N (fun b => η.inv ≫ e.functor.map (ι b) ≫ ρ.hom)
  have hcd : (Cocone.precompose α.inv).obj c ≅ d :=
    Cocone.ext ρ (by intro j; cases j; simp [c, d, α, F₀, F₁])
  exact (IsColimit.equivOfNatIsoOfIso α c d hcd) (isColimitOfPreserves e.functor hc)

/-- A family of arrows generating a covering sieve of `U` is, read in the slice site over `U`, a
family covering the terminal object. -/
lemma coversTop_over_of_ofArrows_mem {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (U : C) {I : Type*} (V : I → C) (f : ∀ i, V i ⟶ U) (h : Sieve.ofArrows V f ∈ J U) :
    (J.over U).CoversTop (fun i => Over.mk (f i)) := by
  intro W
  rw [GrothendieckTopology.mem_over_iff]
  apply J.superset_covering _ (J.pullback_stable W.hom h)
  rintro Z g ⟨T, a, g₁, ⟨j⟩, hcomp⟩
  show ∃ A : Over U, ∃ α : A ⟶ W, ∃ β : Z ⟶ A.left,
    (∃ j, Nonempty (A ⟶ Over.mk (f j))) ∧ g = β ≫ α.left
  exact ⟨Over.mk (g ≫ W.hom), Over.homMk g (by simp), 𝟙 Z,
    ⟨j, ⟨Over.homMk a (by simpa using hcomp)⟩⟩, by simp⟩

/-- The family of all objects of a site, indexed by `ULift C`, covers its terminal object. -/
lemma coversTop_ulift_self {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    J.CoversTop (fun i : ULift.{t} C => i.down) :=
  fun Z => J.superset_covering (fun T _ _ => ⟨⟨T⟩, ⟨𝟙 T⟩⟩) (J.top_mem Z)

end Stacks.SheafOfModules

end
