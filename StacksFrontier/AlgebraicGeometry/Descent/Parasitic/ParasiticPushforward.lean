module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.Defs
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatVanishing
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AbelianSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ModuleInjectives
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiLimits
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.MorphismOfTopoi
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiCovering.BigZariskiMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.PushforwardAdditive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing
public import StacksCore.Tactic.StacksAttribute

/-!
# Direct images of parasitic modules

The direct image and every higher direct image of a parasitic module along a morphism of big
sites are parasitic: an object flat over the target pulls back to an object flat over the
source, and the sections of the direct image over the former are the sections of the module
over the latter.

## Main results

* `AlgebraicGeometry.bigZariskiPushforward_isParasitic`
* `AlgebraicGeometry.bigEtalePushforward_isParasitic`
* `AlgebraicGeometry.bigSmoothPushforward_isParasitic`
* `AlgebraicGeometry.bigSyntomicPushforward_isParasitic`
* `AlgebraicGeometry.bigFppfPushforward_isParasitic`
* `AlgebraicGeometry.bigZariskiHigherDirectImage_isParasitic`
* `AlgebraicGeometry.bigEtaleHigherDirectImage_isParasitic`
* `AlgebraicGeometry.bigSmoothHigherDirectImage_isParasitic`
* `AlgebraicGeometry.bigSyntomicHigherDirectImage_isParasitic`
* `AlgebraicGeometry.bigFppfHigherDirectImage_isParasitic`

## Implementation notes

The morphism of sites is the slice-pullback functor `CategoryTheory.Over.pullback`, and the
direct image of modules is `SheafOfModules.pushforward` along a map of ring sheaves `φ`. Both
ring sheaves are free variables: nothing in the argument uses them, and keeping them free lets
the statement be applied to a module over a pushforward of a structure sheaf without
transporting along an equation of ring sheaves.

The content of the statement about the direct image itself is `flat_pullback_snd_map`: a functor
to schemes that preserves pullbacks carries the second projection of a pullback square to a flat
morphism whenever the opposite side is flat. On each site the canonical functor to schemes
preserves pullbacks, so the sections of the direct image at a flat object are the sections of
the module at a flat object.

For the higher direct images there are two more inputs. Stacks 072W identifies `R^i f_* F` with
the sheafification of the presheaf `V ↦ H^i(f⁻¹V, F)`, so it suffices to see that presheaf
vanish on a family of objects which refines every covering of a flat object — which is
`flatPart_covering`, the observation that the flat part of a covering sieve of a flat object is
again covering. On each flat object itself the cohomology vanishes by Stacks 0755, and
`Stacks.Cohomology.ObjectSections.subsingleton_rightDerived_evaluation` converts that vanishing
of the cohomology of the underlying abelian sheaf into vanishing of right derived sections of
the sheaf of modules.

All the typeclass data the higher direct images need is canonical, so the statements carry no
hypothesis beyond the site, the ring sheaves and the module. Sheafification of abelian
presheaves on a big site and the resulting abelian structure on its sheaves of modules are
instances (`StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AbelianSheaves`), and so is the
existence of enough injectives in the source category of modules, which the right derived
functor is undefined without
(`StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ModuleInjectives`, which is Stacks 01DU
transported to the big slices along the equivalence with a small model). The two categories of
the right derived functor are named explicitly in the statements, because
`CategoryTheory.Functor.rightDerived` takes its `Abelian` instances before the functor itself
and so would have them synthesised before the categories are known.

For the same reason each positive-degree branch opens by pinning the enough injectives of the
source category as a local instance. The conclusion of `higherDirectImage_subsingleton` names a
right derived functor whose site and ring sheaf are still metavariables while its instance
arguments are being synthesised, which only a local instance can answer; that is also why the
two sheafification conditions are restated there by `inferInstance`.

## References

* [Stacks Project, Tag 07AG](https://stacks.math.columbia.edu/tag/07AG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v w r u' v'

namespace AlgebraicGeometry

private lemma flat_pullback_snd_map
    {C : Type v} [Category.{w} C] [HasPullbacks C]
    (G : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan G] {X Y Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) (hf : Flat (G.map f)) :
    Flat (G.map (pullback.snd f g)) := by
  have : Flat (G.map f) := hf
  have hcomp : Flat ((PreservesPullback.iso G f g).hom ≫
      pullback.snd (G.map f) (G.map g)) := by infer_instance
  rw [PreservesPullback.iso_hom_snd] at hcomp
  exact hcomp

/-- A sheaf whose sections are locally the sections of a presheaf `P` has subsingleton sections
on every object of a family `Q` which refines every covering of its members, provided `P` has
subsingleton sections there. Two sections agree because they agree on a covering by members of
`Q`, where the presheaf already has only one section. -/
private lemma subsingleton_of_locallySurjective
    {D : Type u'} [Category.{v'} D] {JD : GrothendieckTopology D}
    {P : Dᵒᵖ ⥤ AddCommGrpCat.{w}} (G : Sheaf JD AddCommGrpCat.{w})
    (η : P ⟶ G.obj) [Presheaf.IsLocallySurjective JD η]
    (Q : D → Prop)
    (hQ : ∀ X, Q X → ∀ S ∈ JD X,
      ∃ R : Presieve X, R ≤ S.arrows ∧ Sieve.generate R ∈ JD X ∧
        ∀ ⦃Y⦄ (f : Y ⟶ X), R f → Q Y)
    (hP : ∀ X, Q X → Subsingleton (P.obj (op X)))
    (X : D) (hX : Q X) : Subsingleton (G.obj.obj (op X)) := by
  apply subsingleton_of_forall_eq 0
  intro s
  obtain ⟨R, hRS, hR, hRQ⟩ :=
    hQ X hX (Presheaf.imageSieve η s) (Presheaf.imageSieve_mem (J := JD) (f := η) (s := s))
  apply G.isSeparated X (Sieve.generate R) hR
  rintro Y f ⟨Z, g, h, hh, rfl⟩
  obtain ⟨t, ht⟩ := hRS Z h hh
  have ht0 : t = 0 := (hP Z (hRQ h hh)).elim _ _
  have hs : G.obj.map h.op s = 0 := by rw [← ht, ht0]; exact map_zero _
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hs, map_zero]

/-- Sheafification of an abelian presheaf has subsingleton sections wherever the presheaf does,
along a family refining every covering of its members. -/
private lemma subsingleton_sheafify
    {D : Type u'} [Category.{v'} D] (JD : GrothendieckTopology D)
    [HasSheafify JD AddCommGrpCat.{w}] [JD.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (P : Dᵒᵖ ⥤ AddCommGrpCat.{w}) (Q : D → Prop)
    (hQ : ∀ X, Q X → ∀ S ∈ JD X,
      ∃ R : Presieve X, R ≤ S.arrows ∧ Sieve.generate R ∈ JD X ∧
        ∀ ⦃Y⦄ (f : Y ⟶ X), R f → Q Y)
    (hP : ∀ X, Q X → Subsingleton (P.obj (op X)))
    (X : D) (hX : Q X) : Subsingleton ((sheafify JD P).obj (op X)) :=
  subsingleton_of_locallySurjective ((presheafToSheaf JD _).obj P)
    (toSheafify JD P) Q hQ hP X hX

/-- Sheafification of a presheaf of modules has subsingleton sections wherever the presheaf
does, along a family refining every covering of its members: the underlying abelian sheaf is
the sheafification of the underlying abelian presheaf. -/
private lemma subsingleton_moduleSheafification
    {D : Type u'} [Category.{v'} D] {JD : GrothendieckTopology D}
    [HasSheafify JD AddCommGrpCat.{w}] [JD.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (O : Sheaf JD RingCat.{r}) (P : PresheafOfModules.{w} O.obj) (Q : D → Prop)
    (hQ : ∀ X, Q X → ∀ S ∈ JD X,
      ∃ R : Presieve X, R ≤ S.arrows ∧ Sieve.generate R ∈ JD X ∧
        ∀ ⦃Y⦄ (f : Y ⟶ X), R f → Q Y)
    (hP : ∀ X, Q X → Subsingleton (P.obj (op X)))
    (X : D) (hX : Q X) :
    Subsingleton (((moduleSheafification O).obj P).val.obj (op X)) := by
  change Subsingleton ((sheafify JD P.presheaf).obj (op X))
  exact subsingleton_sheafify JD P.presheaf Q hQ hP X hX

/-- **Vanishing of a higher direct image along a refining family.** Let `Q` be a family of
objects of the source site which refines every covering of its members. If the cohomology of
`F` in degree `i` vanishes over the image of every member of `Q`, then the `i`-th higher direct
image of `F` has subsingleton sections over every member of `Q`.

By Stacks 072W the higher direct image is the sheafification of the cohomology presheaf, whose
value at an object `V` is the cohomology of `F` over the image of `V`; `Q` refines coverings, so
`subsingleton_moduleSheafification` transports the vanishing from `Q` to the sheafification. -/
private lemma higherDirectImage_subsingleton
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (g : D ⥤ C) [g.IsContinuous JD JC]
    (OC : Sheaf JC RingCat.{r}) (OD : Sheaf JD RingCat.{r})
    (φ : OD ⟶ (g.sheafPushforwardContinuous RingCat.{r} JD JC).obj OC)
    (F : SheafOfModules.{w} OC)
    [HasSheafify JC AddCommGrpCat.{w}] [JC.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}] [JD.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [EnoughInjectives (SheafOfModules.{w} OC)]
    (Q : D → Prop)
    (hQ : ∀ X, Q X → ∀ S ∈ JD X,
      ∃ R : Presieve X, R ≤ S.arrows ∧ Sieve.generate R ∈ JD X ∧
        ∀ ⦃Y⦄ (f : Y ⟶ X), R f → Q Y)
    (i : ℕ)
    (hF : ∀ X, Q X → Subsingleton
      (((SheafOfModules.evaluation OC (op (g.obj X))).rightDerived i).obj F))
    (X : D) (hX : Q X) :
    Subsingleton ((((SheafOfModules.pushforward.{w} φ).rightDerived i).obj F).val.obj
      (op X)) := by
  have hP (Y : D) (hY : Q Y) :
      Subsingleton ((cohPresheafModule g OC OD φ i F).obj (op Y)) := by
    obtain ⟨e⟩ := cohPresheafModule_evaluation_iso g OC OD φ i F Y
    have : Subsingleton ((ModuleCat.restrictScalars (φ.hom.app (op Y)).hom).obj
        (cohomologyOverObject g OC i Y F)) := hF Y hY
    exact (ConcreteCategory.bijective_of_isIso e.hom).injective.subsingleton
  have : Subsingleton ((SheafOfModules.evaluation OD (op X)).obj
      ((moduleSheafification OD).obj (cohPresheafModule g OC OD φ i F))) :=
    subsingleton_moduleSheafification OD (cohPresheafModule g OC OD φ i F) Q hQ hP X hX
  obtain ⟨e⟩ := higherDirectImage_iso_sheafify_cohomologyPresheaf g OC OD φ i F
  exact (ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation OD (op X)).map e.hom)).injective.subsingleton

/-- The direct image of sheaves of modules along a continuous functor preserves finite limits:
limits of sheaves of modules are computed sectionwise, and the direct image is restriction of
sections. -/
private lemma pushforward_preservesFiniteLimits
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (g : D ⥤ C) [g.IsContinuous JD JC]
    (OC : Sheaf JC RingCat.{r}) (OD : Sheaf JD RingCat.{r})
    (φ : OD ⟶ (g.sheafPushforwardContinuous RingCat.{r} JD JC).obj OC) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{w} φ) := by
  have : PreservesFiniteLimits (SheafOfModules.forget.{w} OC) := inferInstance
  have : PreservesFiniteLimits (PresheafOfModules.toPresheaf.{w} OC.obj) := inferInstance
  let : PreservesFiniteLimits
      (SheafOfModules.forget.{w} OC ⋙ PresheafOfModules.toPresheaf OC.obj) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits
      ((Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ AddCommGrpCat.{w}).obj g.op) := inferInstance
  have : (PresheafOfModules.toPresheaf.{w} OD.obj).ReflectsIsomorphisms := inferInstance
  let H : SheafOfModules.{w} OD ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{w} :=
    SheafOfModules.forget.{w} OD ⋙ PresheafOfModules.toPresheaf OD.obj
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{w} φ ⋙ H) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget OC ⋙ PresheafOfModules.toPresheaf OC.obj) ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{w}).obj g.op)
    exact comp_preservesFiniteLimits _ _
  let : PreservesFiniteLimits H := comp_preservesFiniteLimits _ _
  let : H.ReflectsIsomorphisms := by dsimp [H]; infer_instance
  let : ReflectsFiniteLimits H := reflectsFiniteLimits_of_reflectsIsomorphisms H
  exact preservesFiniteLimits_of_reflects_of_preserves (SheafOfModules.pushforward φ) H

/-- The members of a sieve whose image in schemes is flat. -/
private abbrev flatPart {C : Type v} [Category.{w} C]
    (G : C ⥤ Scheme.{u}) {X : C} (V : Sieve X) : Presieve X :=
  fun _ f => V f ∧ Flat (G.map f)

/-- **The flat part of a covering sieve is covering.** If every covering morphism of a
precoverage becomes flat in schemes, then for every sieve covering for the induced topology the
subfamily whose members become flat is still covering. The induction over the generation of the
topology needs flatness to be stable under base change — which is `flat_pullback_snd_map` — and
under composition. -/
private lemma flatPart_covering
    {C : Type v} [Category.{w} C] [HasPullbacks C]
    (G : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan G]
    (P : Precoverage C)
    (hP : ∀ (X : C) (R : Presieve X), R ∈ P X →
      ∀ ⦃Y⦄ (f : Y ⟶ X), R f → Flat (G.map f))
    {X : C} (V : Sieve X) (hV : V ∈ P.toGrothendieck X) :
    Sieve.generate (flatPart G V) ∈ P.toGrothendieck X := by
  induction hV with
  | of X R hR =>
      apply P.toGrothendieck.superset_covering _ (P.generate_mem_toGrothendieck hR)
      apply Sieve.generate_mono
      intro Y f hf
      exact ⟨Sieve.le_generate R Y f hf, hP X R hR f hf⟩
  | top X =>
      have ht : Sieve.generate (flatPart G (⊤ : Sieve X)) = ⊤ := by
        apply Sieve.id_mem_iff_eq_top.mp
        apply Sieve.le_generate
        refine ⟨trivial, ?_⟩
        simpa using (inferInstance : Flat (𝟙 (G.obj X)))
      rw [ht]
      exact P.toGrothendieck.top_mem X
  | pullback X V hV Y f ih =>
      apply P.toGrothendieck.superset_covering _ (P.toGrothendieck.pullback_stable f ih)
      rw [← Sieve.pullbackArrows_comm]
      apply Sieve.generate_mono
      rintro Z g ⟨W, h, hh⟩
      refine ⟨?_, flat_pullback_snd_map G h f hh.2⟩
      change V (pullback.snd h f ≫ f)
      rw [← pullback.condition]
      exact V.downward_closed hh.1 _
  | transitive X V W hV hW ih ih' =>
      apply P.toGrothendieck.transitive ih
      rintro Y g ⟨Z, a, b, hb, rfl⟩
      have hc := ih' hb.1
      have hle : Sieve.generate (flatPart G (W.pullback b)) ≤
          (Sieve.generate (flatPart G W)).pullback b := by
        apply (Sieve.generate_le_iff _ _).mpr
        intro A c hc
        apply Sieve.le_generate
        refine ⟨hc.1, ?_⟩
        rw [Functor.map_comp]
        have : Flat (G.map c) := hc.2
        have : Flat (G.map b) := hb.2
        infer_instance
      simpa only [Sieve.pullback_comp] using P.toGrothendieck.pullback_stable a
        (P.toGrothendieck.superset_covering hle hc)

/-- Every covering of an object flat over the base is refined by a family of objects flat over
the base, for a site given by a precoverage whose covering morphisms are flat, together with a
functor to schemes over the base. -/
private lemma exists_flat_presieve_of_precoverage
    {C : Type v} [Category.{w} C] [HasPullbacks C] {S : Scheme.{u}}
    (G : C ⥤ Over S) [PreservesLimitsOfShape WalkingCospan (G ⋙ Over.forget S)]
    (P : Precoverage C)
    (hP : ∀ (X : C) (R : Presieve X), R ∈ P X →
      ∀ ⦃Y⦄ (f : Y ⟶ X), R f → Flat (G.map f).left)
    (X : C) (hX : Flat (G.obj X).hom)
    (V : Sieve X) (hV : V ∈ P.toGrothendieck X) :
    ∃ R : Presieve X, R ≤ V.arrows ∧ Sieve.generate R ∈ P.toGrothendieck X ∧
      ∀ ⦃Y⦄ (f : Y ⟶ X), R f → Flat (G.obj Y).hom := by
  refine ⟨flatPart (G ⋙ Over.forget S) V, fun _ _ h => h.1,
    flatPart_covering _ P hP V hV, ?_⟩
  intro Y f hf
  rw [← (G.map f).w]
  have : Flat (G.map f).left := hf.2
  have : Flat (G.obj X).hom := hX
  infer_instance

/-- Every covering of an object flat over the base is refined by a family of objects flat over
the base, for the localization at the base of a site given by a precoverage whose covering
morphisms are flat. -/
private lemma exists_flat_presieve_over
    {C : Type v} [Category.{w} C] [HasPullbacks C]
    (G : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan G]
    (P : Precoverage C)
    (hP : ∀ (X : C) (R : Presieve X), R ∈ P X →
      ∀ ⦃Y⦄ (f : Y ⟶ X), R f → Flat (G.map f))
    (S : C) (X : Over S) (hX : Flat (G.map X.hom))
    (V : Sieve X) (hV : V ∈ P.toGrothendieck.over S X) :
    ∃ R : Presieve X, R ≤ V.arrows ∧ Sieve.generate R ∈ P.toGrothendieck.over S X ∧
      ∀ ⦃Y⦄ (f : Y ⟶ X), R f → Flat (G.map Y.hom) := by
  let W := (Sieve.overEquiv X) V
  let A := flatPart G W
  refine ⟨(Presieve.overEquiv X).symm A, ?_, ?_, ?_⟩
  · intro Y f hf
    simpa only [W, OrderIso.symm_apply_apply] using (Sieve.overEquiv_symm_iff W f).mpr hf.1
  · rw [GrothendieckTopology.mem_over_iff]
    change (Sieve.overEquiv X)
      (Sieve.generate (Presieve.functorPullback (Over.forget S) A)) ∈ P.toGrothendieck X.left
    rw [← Sieve.overEquiv_symm_generate, OrderIso.apply_symm_apply]
    exact flatPart_covering G P hP W hV
  · intro Y f hf
    rw [← f.w, Functor.map_comp]
    have : Flat (G.map f.left) := hf.2
    have : Flat (G.map X.hom) := hX
    infer_instance

/-- On the big Zariski site over `S`, every covering of an object flat over `S` is refined by a
family of objects flat over `S`: the covering morphisms are open immersions, hence flat. -/
private lemma zariski_flat_refinement (B : AlgebraicGeometry.BigZariskiSite.{u})
    (S : B.Schemes) :
    ∀ X, Flat ((Over.post B.inclusion).obj X).hom →
      ∀ V ∈ AlgebraicGeometry.BigZariskiOver.topology B S.1 S.2 X,
      ∃ R : Presieve X, R ≤ V.arrows ∧
        Sieve.generate R ∈ AlgebraicGeometry.BigZariskiOver.topology B S.1 S.2 X ∧
        ∀ ⦃Y⦄ (f : Y ⟶ X), R f → Flat ((Over.post B.inclusion).obj Y).hom := by
  let : PreservesLimitsOfShape WalkingCospan
      (Over.post B.inclusion ⋙ Over.forget (B.inclusion.obj S)) := by
    change PreservesLimitsOfShape WalkingCospan (Over.forget S ⋙ B.inclusion)
    infer_instance
  apply exists_flat_presieve_of_precoverage (Over.post B.inclusion)
    (AlgebraicGeometry.BigZariskiOver.precoverage B S.1 S.2)
  rintro X R ⟨E, rfl, hE⟩ Y f ⟨i⟩
  have h := (Scheme.ofArrows_mem_precoverage_iff (@IsOpenImmersion)).mp
    (show (E.map (Over.forget S ⋙ B.inclusion)).presieve₀ ∈
      Scheme.precoverage (@IsOpenImmersion) _ from hE.1)
  have : IsOpenImmersion ((Over.forget S ⋙ B.inclusion).map (E.f i)) := h.2 i
  change Flat ((Over.forget S ⋙ B.inclusion).map (E.f i))
  infer_instance

/-- On the big étale site over `S`, every covering of an object flat over `S` is refined by a
family of objects flat over `S`: the covering morphisms are étale, hence flat. -/
private lemma etale_flat_refinement (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : B.Scheme) :
    ∀ X, Flat ((Over.post B.inclusion).obj X).hom →
      ∀ V ∈ AlgebraicGeometry.BigEtaleOver.topology B S.1 S.2 X,
      ∃ R : Presieve X, R ≤ V.arrows ∧
        Sieve.generate R ∈ AlgebraicGeometry.BigEtaleOver.topology B S.1 S.2 X ∧
        ∀ ⦃Y⦄ (f : Y ⟶ X), R f → Flat ((Over.post B.inclusion).obj Y).hom := by
  let : PreservesLimitsOfShape WalkingCospan
      (Over.post B.inclusion ⋙ Over.forget (B.inclusion.obj S)) := by
    change PreservesLimitsOfShape WalkingCospan (Over.forget S ⋙ B.inclusion)
    infer_instance
  apply exists_flat_presieve_of_precoverage (Over.post B.inclusion)
    (AlgebraicGeometry.BigEtaleOver.precoverage B S.1 S.2)
  rintro X R ⟨E, rfl, hE⟩ Y f ⟨i⟩
  have h := (Scheme.ofArrows_mem_precoverage_iff (@Etale)).mp
    (show (E.map (Over.forget S ⋙ B.inclusion)).presieve₀ ∈
      Scheme.precoverage (@Etale) _ from hE.1)
  have : Etale ((Over.forget S ⋙ B.inclusion).map (E.f i)) := h.2 i
  change Flat ((Over.forget S ⋙ B.inclusion).map (E.f i))
  infer_instance

/-- On the big smooth site over `S`, every covering of an object flat over `S` is refined by a
family of objects flat over `S`: the covering morphisms are smooth, hence flat. -/
private lemma smooth_flat_refinement (B : AlgebraicGeometry.BigSmoothSite.{u})
    (S : B.category) :
    ∀ X, Flat ((Over.post (ObjectProperty.ι _)).obj X).hom →
      ∀ V ∈ AlgebraicGeometry.BigSmoothOver.topology B S.1 S.2 X,
      ∃ R : Presieve X, R ≤ V.arrows ∧
        Sieve.generate R ∈ AlgebraicGeometry.BigSmoothOver.topology B S.1 S.2 X ∧
        ∀ ⦃Y⦄ (f : Y ⟶ X), R f → Flat ((Over.post (ObjectProperty.ι _)).obj Y).hom := by
  apply exists_flat_presieve_over (ObjectProperty.ι _) B.precoverage _ S
  rintro X R ⟨E, hE, rfl⟩ Y f ⟨i⟩
  have h := (Scheme.ofArrows_mem_precoverage_iff (@Smooth)).mp hE.1
  have : Smooth ((ObjectProperty.ι _).map (E.f i)) := h.2 i
  infer_instance

/-- On the big syntomic site over `S`, every covering of an object flat over `S` is refined by a
family of objects flat over `S`: the covering morphisms are syntomic, hence flat. -/
private lemma syntomic_flat_refinement (B : AlgebraicGeometry.BigSyntomicSite.{u})
    (S : B.category) :
    ∀ X, Flat ((Over.post B.inclusion).obj X).hom →
      ∀ V ∈ AlgebraicGeometry.BigSyntomicOver.topology B S.1 S.2 X,
      ∃ R : Presieve X, R ≤ V.arrows ∧
        Sieve.generate R ∈ AlgebraicGeometry.BigSyntomicOver.topology B S.1 S.2 X ∧
        ∀ ⦃Y⦄ (f : Y ⟶ X), R f → Flat ((Over.post B.inclusion).obj Y).hom := by
  apply exists_flat_presieve_over B.inclusion B.precoverage _ S
  rintro X R ⟨E, rfl, hE⟩ Y f ⟨i⟩
  exact AlgebraicGeometry.flat (hE.1.1 i)

/-- On the big fppf site over `S`, every covering of an object flat over `S` is refined by a
family of objects flat over `S`: the covering morphisms are flat by definition. -/
private lemma fppf_flat_refinement (B : AlgebraicGeometry.BigFppfSite.{u}) (S : B.Schemes) :
    ∀ X, Flat ((Over.post B.inclusion).obj X).hom →
      ∀ V ∈ AlgebraicGeometry.BigFppfOver.topology B S.1 S.2 X,
      ∃ R : Presieve X, R ≤ V.arrows ∧
        Sieve.generate R ∈ AlgebraicGeometry.BigFppfOver.topology B S.1 S.2 X ∧
        ∀ ⦃Y⦄ (f : Y ⟶ X), R f → Flat ((Over.post B.inclusion).obj Y).hom := by
  apply exists_flat_presieve_over B.inclusion B.precoverage _ S
  rintro X R ⟨E, rfl, hE⟩ Y f ⟨i⟩
  have hE' : (E.map B.inclusion).presieve₀ ∈ Scheme.fppfPrecoverage _ := by
    simpa only [Precoverage.mem_comap_iff, PreZeroHypercover.presieve₀_map] using
      (show E.presieve₀ ∈ Scheme.fppfPrecoverage.comap B.inclusion X from hE.1)
  rw [Scheme.fppfPrecoverage_eq_inf] at hE'
  exact ((Scheme.ofArrows_mem_precoverage_iff (@Flat)).mp hE'.1).2 i

/-- An abelian category with enough injectives has `Ext`-groups in its own universe of
morphisms, since it is locally small in that universe. -/
private lemma hasExt_morphismUniverse (A : Type u') [Category.{v'} A] [Abelian A]
    [EnoughInjectives A] : HasExt.{v'} A := by
  have : LocallySmall.{v'} A := CategoryTheory.locallySmall_self A
  exact hasExt_of_enoughInjectives A

/-- **Vanishing of every derived direct image along a refining family.** Let `Q` be a family of
objects of the source site which refines every covering of its members. If the direct image of
`F` has subsingleton sections over the members of `Q`, and the cohomology of the underlying
abelian sheaf of `F` vanishes in positive degrees over the image of every member of `Q`, then the
`i`-th right derived functor of the direct image has subsingleton sections over every member
of `Q`. -/
private lemma subsingleton_rightDerived_pushforward
    {C : Type u} [Category.{w} C] {D : Type u'} [Category.{v'} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (g : D ⥤ C) [g.IsContinuous JD JC]
    (OC : Sheaf JC RingCat.{w}) (OD : Sheaf JD RingCat.{w})
    (φ : OD ⟶ (g.sheafPushforwardContinuous RingCat.{w} JD JC).obj OC)
    (F : SheafOfModules.{w} OC)
    [HasSheafify JC AddCommGrpCat.{w}] [JC.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}] [JD.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [IsGrothendieckAbelian.{w} (Sheaf JC AddCommGrpCat.{w})]
    [EnoughInjectives (SheafOfModules.{w} OC)]
    (Q : D → Prop)
    (hQ : ∀ X, Q X → ∀ S ∈ JD X,
      ∃ R : Presieve X, R ≤ S.arrows ∧ Sieve.generate R ∈ JD X ∧
        ∀ ⦃Y⦄ (f : Y ⟶ X), R f → Q Y)
    (i : ℕ)
    (h₀ : ∀ X, Q X → Subsingleton (((SheafOfModules.pushforward.{w} φ).obj F).val.obj (op X)))
    (hF : ∀ [HasExt.{max u w} (Sheaf JC AddCommGrpCat.{w})] (Y : D), Q Y → ∀ n : ℕ,
      IsZero (Sheaf.H'.{max u w} ((SheafOfModules.toSheaf OC).obj F) (n + 1) (g.obj Y)))
    (X : D) (hX : Q X) :
    Subsingleton ((((SheafOfModules.pushforward.{w} φ).rightDerived i).obj F).val.obj
      (op X)) := by
  cases i with
  | zero =>
      have := pushforward_preservesFiniteLimits g OC OD φ
      have : Subsingleton ((SheafOfModules.evaluation OD (op X)).obj
          ((SheafOfModules.pushforward.{w} φ).obj F)) := h₀ X hX
      exact (ConcreteCategory.bijective_of_isIso ((SheafOfModules.evaluation OD (op X)).map
        ((Functor.rightDerivedZeroIsoSelf (SheafOfModules.pushforward.{w} φ)).app F).hom)
        ).injective.subsingleton
  | succ i =>
      have : EnoughInjectives (Sheaf JC AddCommGrpCat.{w}) :=
        IsGrothendieckAbelian.enoughInjectives
      have : HasExt.{max u w} (Sheaf JC AddCommGrpCat.{w}) := hasExt_morphismUniverse _
      have : HasExt.{max u w} (SheafOfModules.{w} OC) := hasExt_morphismUniverse _
      exact higherDirectImage_subsingleton g OC OD φ F Q hQ (i + 1)
        (fun Y hY => _root_.Stacks.Cohomology.ObjectSections.subsingleton_rightDerived_evaluation
          JC OC F (g.obj Y) i (hF Y hY i)) X hX

/-- Direct image of a parasitic module on the big Zariski site is parasitic. -/
@[stacks 07AG "big Zariski direct image"]
public theorem bigZariskiPushforward_isParasitic
    (B : AlgebraicGeometry.BigZariskiSite.{u}) (T S : B.Schemes) (f : T ⟶ S)
    {𝒪S : Sheaf (AlgebraicGeometry.BigZariskiOver.topology B S.1 S.2) RingCat.{u}}
    {𝒪T : Sheaf (AlgebraicGeometry.BigZariskiOver.topology B T.1 T.2) RingCat.{u}}
    (φ : 𝒪S ⟶
      ((Over.pullback f).sheafPushforwardContinuous RingCat.{u}
        (AlgebraicGeometry.BigZariskiOver.topology B S.1 S.2)
        (AlgebraicGeometry.BigZariskiOver.topology B T.1 T.2)).obj
          𝒪T)
    (F : SheafOfModules.{u} 𝒪T)
    (hF : IsParasitic T.1 (Over.post B.inclusion) F.val) :
    IsParasitic S.1 (Over.post B.inclusion)
      ((SheafOfModules.pushforward.{u} φ).obj F).val := by
  intro X hX
  exact hF ((Over.pullback f).obj X)
    (flat_pullback_snd_map (G := B.inclusion) (f := X.hom) (g := f) hX)

/-- Every higher direct image of a parasitic module on the big Zariski site is
parasitic. -/
@[stacks 07AG "big Zariski higher direct images"]
public theorem bigZariskiHigherDirectImage_isParasitic
    (B : AlgebraicGeometry.BigZariskiSite.{u}) (T S : B.Schemes) (f : T ⟶ S)
    {𝒪S : Sheaf (AlgebraicGeometry.BigZariskiOver.topology B S.1 S.2) RingCat.{u}}
    {𝒪T : Sheaf (AlgebraicGeometry.BigZariskiOver.topology B T.1 T.2) RingCat.{u}}
    (φ : 𝒪S ⟶
      ((Over.pullback f).sheafPushforwardContinuous RingCat.{u}
        (AlgebraicGeometry.BigZariskiOver.topology B S.1 S.2)
        (AlgebraicGeometry.BigZariskiOver.topology B T.1 T.2)).obj
          𝒪T)
    (F : SheafOfModules.{u} 𝒪T)
    (hF : IsParasitic T.1 (Over.post B.inclusion) F.val) (i : ℕ) :
    IsParasitic S.1 (Over.post B.inclusion)
      ((Functor.rightDerived (C := SheafOfModules.{u} 𝒪T) (D := SheafOfModules.{u} 𝒪S)
        (SheafOfModules.pushforward.{u} φ) i).obj F).val := by
  intro X hX
  have : EnoughInjectives (SheafOfModules.{u} 𝒪T) := inferInstance
  have : IsGrothendieckAbelian.{u}
      (Sheaf (AlgebraicGeometry.BigZariskiOver.topology B T.1 T.2) AddCommGrpCat.{u}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} _ _
  have : HasSheafify (AlgebraicGeometry.BigZariskiOver.topology B T.1 T.2)
      AddCommGrpCat.{u} := inferInstance
  have : (AlgebraicGeometry.BigZariskiOver.topology B T.1 T.2).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  have : HasSheafify (AlgebraicGeometry.BigZariskiOver.topology B S.1 S.2)
      AddCommGrpCat.{u} := inferInstance
  have : (AlgebraicGeometry.BigZariskiOver.topology B S.1 S.2).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  exact subsingleton_rightDerived_pushforward (Over.pullback f) 𝒪T 𝒪S φ F _
    (zariski_flat_refinement B S) i (bigZariskiPushforward_isParasitic B T S f φ F hF)
    (fun Y hY n => bigZariskiCohomology_isZero_of_isParasitic B T.1 T.2 F hF
      ((Over.pullback f).obj Y)
      (flat_pullback_snd_map B.inclusion Y.hom f hY) _) X hX


/-- Direct image of a parasitic module on the big étale site is parasitic. -/
@[stacks 07AG "big étale direct image"]
public theorem bigEtalePushforward_isParasitic
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)
    {𝒪S : Sheaf (AlgebraicGeometry.BigEtaleOver.topology B S.1 S.2) RingCat.{u}}
    {𝒪T : Sheaf (AlgebraicGeometry.BigEtaleOver.topology B T.1 T.2) RingCat.{u}}
    (φ : 𝒪S ⟶
      ((Over.pullback f).sheafPushforwardContinuous RingCat.{u}
        (AlgebraicGeometry.BigEtaleOver.topology B S.1 S.2)
        (AlgebraicGeometry.BigEtaleOver.topology B T.1 T.2)).obj
          𝒪T)
    (F : SheafOfModules.{u} 𝒪T)
    (hF : IsParasitic T.1 (Over.post B.inclusion) F.val) :
    IsParasitic S.1 (Over.post B.inclusion)
      ((SheafOfModules.pushforward.{u} φ).obj F).val := by
  intro X hX
  exact hF ((Over.pullback f).obj X)
    (flat_pullback_snd_map (G := B.inclusion) (f := X.hom) (g := f) hX)

/-- Higher direct images of a parasitic module on the big étale site are parasitic. -/
@[stacks 07AG "big étale higher direct images"]
public theorem bigEtaleHigherDirectImage_isParasitic
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)
    {𝒪S : Sheaf (AlgebraicGeometry.BigEtaleOver.topology B S.1 S.2) RingCat.{u}}
    {𝒪T : Sheaf (AlgebraicGeometry.BigEtaleOver.topology B T.1 T.2) RingCat.{u}}
    (φ : 𝒪S ⟶
      ((Over.pullback f).sheafPushforwardContinuous RingCat.{u}
        (AlgebraicGeometry.BigEtaleOver.topology B S.1 S.2)
        (AlgebraicGeometry.BigEtaleOver.topology B T.1 T.2)).obj
          𝒪T)
    (F : SheafOfModules.{u} 𝒪T)
    (hF : IsParasitic T.1 (Over.post B.inclusion) F.val) (i : ℕ) :
    IsParasitic S.1 (Over.post B.inclusion)
      ((Functor.rightDerived (C := SheafOfModules.{u} 𝒪T) (D := SheafOfModules.{u} 𝒪S)
        (SheafOfModules.pushforward.{u} φ) i).obj F).val := by
  intro X hX
  have : EnoughInjectives (SheafOfModules.{u} 𝒪T) := inferInstance
  have : IsGrothendieckAbelian.{u}
      (Sheaf (AlgebraicGeometry.BigEtaleOver.topology B T.1 T.2) AddCommGrpCat.{u}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} _ _
  have : HasSheafify (AlgebraicGeometry.BigEtaleOver.topology B T.1 T.2)
      AddCommGrpCat.{u} := inferInstance
  have : (AlgebraicGeometry.BigEtaleOver.topology B T.1 T.2).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  have : HasSheafify (AlgebraicGeometry.BigEtaleOver.topology B S.1 S.2)
      AddCommGrpCat.{u} := inferInstance
  have : (AlgebraicGeometry.BigEtaleOver.topology B S.1 S.2).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  exact subsingleton_rightDerived_pushforward (Over.pullback f) 𝒪T 𝒪S φ F _
    (etale_flat_refinement B S) i (bigEtalePushforward_isParasitic B T S f φ F hF)
    (fun Y hY n => bigEtaleCohomology_isZero_of_isParasitic B T.1 T.2 F hF
      ((Over.pullback f).obj Y)
      (flat_pullback_snd_map B.inclusion Y.hom f hY) _) X hX


/-- Direct image of a parasitic module on the big smooth site is parasitic. -/
@[stacks 07AG "big smooth direct image"]
public theorem bigSmoothPushforward_isParasitic
    (B : AlgebraicGeometry.BigSmoothSite.{u}) (T S : B.category) (f : T ⟶ S)
    {𝒪S : Sheaf (AlgebraicGeometry.BigSmoothOver.topology B S.1 S.2) RingCat.{u}}
    {𝒪T : Sheaf (AlgebraicGeometry.BigSmoothOver.topology B T.1 T.2) RingCat.{u}}
    (φ : 𝒪S ⟶
      ((Over.pullback f).sheafPushforwardContinuous RingCat.{u}
        (AlgebraicGeometry.BigSmoothOver.topology B S.1 S.2)
        (AlgebraicGeometry.BigSmoothOver.topology B T.1 T.2)).obj
          𝒪T)
    (F : SheafOfModules.{u} 𝒪T)
    (hF : IsParasitic T.1 (Over.post (ObjectProperty.ι _)) F.val) :
    IsParasitic S.1 (Over.post (ObjectProperty.ι _))
      ((SheafOfModules.pushforward.{u} φ).obj F).val := by
  intro X hX
  exact hF ((Over.pullback f).obj X)
    (flat_pullback_snd_map (G := ObjectProperty.ι _) (f := X.hom) (g := f) hX)

/-- Higher direct images of a parasitic module on the big smooth site are parasitic. -/
@[stacks 07AG "big smooth higher direct images"]
public theorem bigSmoothHigherDirectImage_isParasitic
    (B : AlgebraicGeometry.BigSmoothSite.{u}) (T S : B.category) (f : T ⟶ S)
    {𝒪S : Sheaf (AlgebraicGeometry.BigSmoothOver.topology B S.1 S.2) RingCat.{u}}
    {𝒪T : Sheaf (AlgebraicGeometry.BigSmoothOver.topology B T.1 T.2) RingCat.{u}}
    (φ : 𝒪S ⟶
      ((Over.pullback f).sheafPushforwardContinuous RingCat.{u}
        (AlgebraicGeometry.BigSmoothOver.topology B S.1 S.2)
        (AlgebraicGeometry.BigSmoothOver.topology B T.1 T.2)).obj
          𝒪T)
    (F : SheafOfModules.{u} 𝒪T)
    (hF : IsParasitic T.1 (Over.post (ObjectProperty.ι _)) F.val) (i : ℕ) :
    IsParasitic S.1 (Over.post (ObjectProperty.ι _))
      ((Functor.rightDerived (C := SheafOfModules.{u} 𝒪T) (D := SheafOfModules.{u} 𝒪S)
        (SheafOfModules.pushforward.{u} φ) i).obj F).val := by
  intro X hX
  have : EnoughInjectives (SheafOfModules.{u} 𝒪T) := inferInstance
  have : IsGrothendieckAbelian.{u}
      (Sheaf (AlgebraicGeometry.BigSmoothOver.topology B T.1 T.2) AddCommGrpCat.{u}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} _ _
  have : HasSheafify (AlgebraicGeometry.BigSmoothOver.topology B T.1 T.2)
      AddCommGrpCat.{u} := inferInstance
  have : (AlgebraicGeometry.BigSmoothOver.topology B T.1 T.2).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  have : HasSheafify (AlgebraicGeometry.BigSmoothOver.topology B S.1 S.2)
      AddCommGrpCat.{u} := inferInstance
  have : (AlgebraicGeometry.BigSmoothOver.topology B S.1 S.2).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  exact subsingleton_rightDerived_pushforward (Over.pullback f) 𝒪T 𝒪S φ F _
    (smooth_flat_refinement B S) i (bigSmoothPushforward_isParasitic B T S f φ F hF)
    (fun Y hY n => bigSmoothCohomology_isZero_of_isParasitic B T.1 T.2 F hF
      ((Over.pullback f).obj Y)
      (flat_pullback_snd_map (ObjectProperty.ι _) Y.hom f hY) _) X hX


/-- Direct image of a parasitic module on the big syntomic site is parasitic. -/
@[stacks 07AG "big syntomic direct image"]
public theorem bigSyntomicPushforward_isParasitic
    (B : AlgebraicGeometry.BigSyntomicSite.{u}) (T S : B.category) (f : T ⟶ S)
    {𝒪S : Sheaf (AlgebraicGeometry.BigSyntomicOver.topology B S.1 S.2) RingCat.{u}}
    {𝒪T : Sheaf (AlgebraicGeometry.BigSyntomicOver.topology B T.1 T.2) RingCat.{u}}
    (φ : 𝒪S ⟶
      ((Over.pullback f).sheafPushforwardContinuous RingCat.{u}
        (AlgebraicGeometry.BigSyntomicOver.topology B S.1 S.2)
        (AlgebraicGeometry.BigSyntomicOver.topology B T.1 T.2)).obj
          𝒪T)
    (F : SheafOfModules.{u} 𝒪T)
    (hF : IsParasitic T.1 (Over.post B.inclusion) F.val) :
    IsParasitic S.1 (Over.post B.inclusion)
      ((SheafOfModules.pushforward.{u} φ).obj F).val := by
  intro X hX
  exact hF ((Over.pullback f).obj X)
    (flat_pullback_snd_map (G := B.inclusion) (f := X.hom) (g := f) hX)

/-- Higher direct images of a parasitic module on the big syntomic site are parasitic. -/
@[stacks 07AG "big syntomic higher direct images"]
public theorem bigSyntomicHigherDirectImage_isParasitic
    (B : AlgebraicGeometry.BigSyntomicSite.{u}) (T S : B.category) (f : T ⟶ S)
    {𝒪S : Sheaf (AlgebraicGeometry.BigSyntomicOver.topology B S.1 S.2) RingCat.{u}}
    {𝒪T : Sheaf (AlgebraicGeometry.BigSyntomicOver.topology B T.1 T.2) RingCat.{u}}
    (φ : 𝒪S ⟶
      ((Over.pullback f).sheafPushforwardContinuous RingCat.{u}
        (AlgebraicGeometry.BigSyntomicOver.topology B S.1 S.2)
        (AlgebraicGeometry.BigSyntomicOver.topology B T.1 T.2)).obj
          𝒪T)
    (F : SheafOfModules.{u} 𝒪T)
    (hF : IsParasitic T.1 (Over.post B.inclusion) F.val) (i : ℕ) :
    IsParasitic S.1 (Over.post B.inclusion)
      ((Functor.rightDerived (C := SheafOfModules.{u} 𝒪T) (D := SheafOfModules.{u} 𝒪S)
        (SheafOfModules.pushforward.{u} φ) i).obj F).val := by
  intro X hX
  have : EnoughInjectives (SheafOfModules.{u} 𝒪T) := inferInstance
  have : IsGrothendieckAbelian.{u}
      (Sheaf (AlgebraicGeometry.BigSyntomicOver.topology B T.1 T.2) AddCommGrpCat.{u}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} _ _
  have : HasSheafify (AlgebraicGeometry.BigSyntomicOver.topology B T.1 T.2)
      AddCommGrpCat.{u} := inferInstance
  have : (AlgebraicGeometry.BigSyntomicOver.topology B T.1 T.2).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  have : HasSheafify (AlgebraicGeometry.BigSyntomicOver.topology B S.1 S.2)
      AddCommGrpCat.{u} := inferInstance
  have : (AlgebraicGeometry.BigSyntomicOver.topology B S.1 S.2).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  exact subsingleton_rightDerived_pushforward (Over.pullback f) 𝒪T 𝒪S φ F _
    (syntomic_flat_refinement B S) i (bigSyntomicPushforward_isParasitic B T S f φ F hF)
    (fun Y hY n => bigSyntomicCohomology_isZero_of_isParasitic B T.1 T.2 F hF
      ((Over.pullback f).obj Y)
      (flat_pullback_snd_map B.inclusion Y.hom f hY) _) X hX


/-- Direct image of a parasitic module on the big fppf site is parasitic. -/
@[stacks 07AG "big fppf direct image"]
public theorem bigFppfPushforward_isParasitic
    (B : AlgebraicGeometry.BigFppfSite.{u}) (T S : B.Schemes) (f : T ⟶ S)
    {𝒪S : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S.1 S.2) RingCat.{u}}
    {𝒪T : Sheaf (AlgebraicGeometry.BigFppfOver.topology B T.1 T.2) RingCat.{u}}
    (φ : 𝒪S ⟶
      ((Over.pullback f).sheafPushforwardContinuous RingCat.{u}
        (AlgebraicGeometry.BigFppfOver.topology B S.1 S.2)
        (AlgebraicGeometry.BigFppfOver.topology B T.1 T.2)).obj
          𝒪T)
    (F : SheafOfModules.{u} 𝒪T)
    (hF : IsParasitic T.1 (Over.post B.inclusion) F.val) :
    IsParasitic S.1 (Over.post B.inclusion)
      ((SheafOfModules.pushforward.{u} φ).obj F).val := by
  intro X hX
  exact hF ((Over.pullback f).obj X)
    (flat_pullback_snd_map (G := B.inclusion) (f := X.hom) (g := f) hX)

/-- Higher direct images of a parasitic module on the big fppf site are parasitic. -/
@[stacks 07AG "big fppf higher direct images"]
public theorem bigFppfHigherDirectImage_isParasitic
    (B : AlgebraicGeometry.BigFppfSite.{u}) (T S : B.Schemes) (f : T ⟶ S)
    {𝒪S : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S.1 S.2) RingCat.{u}}
    {𝒪T : Sheaf (AlgebraicGeometry.BigFppfOver.topology B T.1 T.2) RingCat.{u}}
    (φ : 𝒪S ⟶
      ((Over.pullback f).sheafPushforwardContinuous RingCat.{u}
        (AlgebraicGeometry.BigFppfOver.topology B S.1 S.2)
        (AlgebraicGeometry.BigFppfOver.topology B T.1 T.2)).obj
          𝒪T)
    (F : SheafOfModules.{u} 𝒪T)
    (hF : IsParasitic T.1 (Over.post B.inclusion) F.val) (i : ℕ) :
    IsParasitic S.1 (Over.post B.inclusion)
      ((Functor.rightDerived (C := SheafOfModules.{u} 𝒪T) (D := SheafOfModules.{u} 𝒪S)
        (SheafOfModules.pushforward.{u} φ) i).obj F).val := by
  intro X hX
  have : EnoughInjectives (SheafOfModules.{u} 𝒪T) := inferInstance
  have : IsGrothendieckAbelian.{u}
      (Sheaf (AlgebraicGeometry.BigFppfOver.topology B T.1 T.2) AddCommGrpCat.{u}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} _ _
  have : HasSheafify (AlgebraicGeometry.BigFppfOver.topology B T.1 T.2)
      AddCommGrpCat.{u} := inferInstance
  have : (AlgebraicGeometry.BigFppfOver.topology B T.1 T.2).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  have : HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S.1 S.2)
      AddCommGrpCat.{u} := inferInstance
  have : (AlgebraicGeometry.BigFppfOver.topology B S.1 S.2).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  exact subsingleton_rightDerived_pushforward (Over.pullback f) 𝒪T 𝒪S φ F _
    (fppf_flat_refinement B S) i (bigFppfPushforward_isParasitic B T S f φ F hF)
    (fun Y hY n => bigFppfCohomology_isZero_of_isParasitic B T.1 T.2 F hF
      ((Over.pullback f).obj Y)
      (flat_pullback_snd_map B.inclusion Y.hom f hY) _) X hX


end AlgebraicGeometry

end
