module

public import StacksFrontier.AlgebraicGeometry.ProperLimitStage.NoetherianChow
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.ProperModelFromClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian

/-!
# Tag 0CNV, reduced to Tag 09ZR alone

`AlgebraicGeometry.LimitNoetherianSituation.eventually_isProper_morphismAt_of_exists_properModel`
reduces Tag 0CNV to a factorisation of `f : X ⟶ Y` as a closed immersion followed by a morphism
which is *already presented as a model* over the model of a good diagram for `Y`. The Stacks proof
obtains that presentation from three citations: Tag 09ZR, which factors a proper morphism as a
closed immersion into one that is proper and of finite presentation; part (1) of Tag 01ZM, which
descends a morphism of finite presentation over the limit to a model over a stage; and Tag 081F,
which descends properness of that model to a later stage.

The last two are available in this repository, so this file performs both descents and leaves Tag
09ZR as the only input.

* Part (1) of Tag 01ZM is `AlgebraicGeometry.LimitDescent.hasFinitePresentationModels`.
* Tag 081F is `AlgebraicGeometry.exists_isProper_baseChange_of_isLimit_of_isNoetherian`, Chow's
  lemma having been discharged over a Noetherian base by
  `AlgebraicGeometry.hasChowModification` ([Stacks, Tag 0200]). The stages of the image system of
  a good diagram are Noetherian, which is the case that theorem covers.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.exists_isProper_model_imageSystem`: a morphism which
  is proper and of finite presentation onto a scheme of finite type over the limit is the base
  change of a proper morphism of finite presentation over some stage of the image system of a good
  diagram for the target.
* `eventually_isProper_morphismAt_of_exists_factorisation`, in the same namespace: **the
  conclusion of Tag 0CNV on the single hypothesis of Tag 09ZR**.
* `exists_factorisation_of_finitePresentation` and
  `eventually_isProper_morphismAt_of_isLocallyNoetherian`, in the same namespace: that hypothesis
  is inhabited, and over a locally Noetherian target it is free, so Tag 0CNV's conclusion holds
  there with no hypothesis beyond the tag's own.

## Implementation notes

**The smallness hypothesis of Tag 081F is discharged, not inherited.**
`exists_isProper_baseChange_of_isLimit_of_isNoetherian` carries
`CategoryTheory.EssentiallySmall.{u}` on its index category, and that hypothesis is not free at a
free index universe — `inferInstance` fails for a `Type v` category, and
`StacksDraft.AlgebraicGeometry.F3b.SmallnessNecessary` records why no such instance can exist. It
*is* free for a `Type u` category, and the projections of the image system of a good diagram are
scheme-theoretically dominant, so
`AlgebraicGeometry.exists_small_isLimit_whisker_of_isSchemeTheoreticallyDominant` replaces the
system by a `u`-small subsystem with the same limit, so Tag 081F's own hypothesis costs nothing
here. The statements below do still carry `CategoryTheory.FinallySmall.{u} I`, but for an
unrelated reason: it is inherited from the Tag 0CNS comparison statements
`AlgebraicGeometry.LimitNoetherianSituation.exists_eventual_iso_imageSystem` and
`AlgebraicGeometry.LimitNoetherianSituation.eventually_natural_imageSystem_comparison`, through
`eventually_isProper_morphismAt_of_exists_properModel`. The route below is the same one by
which
`StacksDraft.AlgebraicGeometry.F3b.Limits.FlatImageSystem` applies part (1) of Tag 01ZM, itself
stated at a `Type u` index, to the image system; the four lemmas here mirror its four flat ones
with `AlgebraicGeometry.IsProper` in place of `AlgebraicGeometry.Flat` and Tag 081F in place of
Tag 04AI.

**Separatedness of the model is a second descent, taken before Tag 081F.**
`exists_isProper_baseChange_of_isLimit_of_isNoetherian` asks for `IsSeparated` of the morphism
*at the stage*, because that is what Chow's lemma consumes there; properness at the limit gives
separatedness only at the limit. Tag 01ZQ,
`AlgebraicGeometry.exists_isSeparated_baseChange_of_isLimit`, supplies a stage at which the model
is separated, and Tag 081F is applied after it.

**No `@[stacks 0CNV]` attribute is attached.** `h09ZR` is a hypothesis Tag 0CNV does not carry.
With Tag 09ZR in place the final theorem below is the tag, and the only change would be to delete
that hypothesis and derive it; `hmodel`, the hypothesis of
`eventually_isProper_morphismAt_of_exists_properModel`, is no longer what is outstanding.

## References

* [Stacks Project, Tag 0CNV](https://stacks.math.columbia.edu/tag/0CNV)
* [Stacks Project, Tag 09ZR](https://stacks.math.columbia.edu/tag/09ZR)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZQ](https://stacks.math.columbia.edu/tag/01ZQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe v u

/-! ### Reading a property of a base change off the base-changed object -/

/-- For a morphism property respecting isomorphisms, the base change along `b` of the structure
morphism of `Z : Over S`, read as a morphism of `Over T`, has the property exactly when the
structure morphism of the base-changed object does.

This is the general form of the two-line translation that every descent step below needs twice:
Tag 01ZQ and Tag 081F speak about morphisms of an over category, while the model produced by part
(1) of Tag 01ZM is an object of one. -/
lemma overPullback_map_terminal_iff (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {S T : Scheme.{u}} (b : T ⟶ S) (Z : Over S) :
    P ((Over.pullback b).map (Over.homMk Z.hom : Z ⟶ Over.mk (𝟙 S))).left ↔
      P ((Over.pullback b).obj Z).hom := by
  have h : ((Over.pullback b).map (Over.homMk Z.hom : Z ⟶ Over.mk (𝟙 S))).left ≫
      pullback.snd (𝟙 S) b = ((Over.pullback b).obj Z).hom := by
    simp only [Over.pullback_map_left, Over.pullback_obj_hom, Over.homMk_left, Over.mk_hom]
    exact pullback.lift_snd _ _ _
  rw [← MorphismProperty.cancel_right_of_respectsIso (P := P) _ (pullback.snd (𝟙 S) b), h]

/-- A morphism property respecting isomorphisms transfers along an isomorphism of an over
category. -/
lemma prop_of_overIso (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {S : Scheme.{u}} {A B : Over S} (e : A ≅ B) (h : P A.hom) : P B.hom := by
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  rwa [← MorphismProperty.cancel_left_of_respectsIso (P := P) e.hom.left, e.hom.w]

/-- The base change of a model along a transition morphism, compared with the base change of the
model itself to the limit. -/
noncomputable def overPullbackObj_shiftIso {J : Type u} [Category.{u} J] (D : J ⥤ Scheme.{u})
    (c : Cone D) {i j : J} (a : j ⟶ i) (Z : Over (D.obj i)) :
    (Over.pullback (c.π.app i)).obj Z ≅
      (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map a)).obj Z) :=
  (eqToIso (by rw [c.w a]) :
    (Over.pullback (c.π.app i)).obj Z ≅
      (Over.pullback (c.π.app j ≫ D.map a)).obj Z) ≪≫
    (Over.pullbackComp (c.π.app j) (D.map a)).app Z

/-! ### A proper model over a stage -/

/-- The source of a morphism of finite presentation over a quasi-compact, quasi-separated scheme
is quasi-compact and quasi-separated. -/
private lemma compactSpace_and_quasiSeparatedSpace_of_finitePresentation {S : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S] (Z : Over S) (h : FinitePresentation Z.hom) :
    CompactSpace Z.left ∧ QuasiSeparatedSpace Z.left :=
  let _ : QuasiCompact Z.hom := h.2.1
  let _ : QuasiSeparated Z.hom := h.2.2
  ⟨QuasiCompact.compactSpace_of_compactSpace Z.hom, quasiSeparatedSpace_of_quasiSeparated Z.hom⟩

/-- The base change of a model of finite presentation is of finite presentation. -/
private lemma finitePresentation_pullback_hom {S T : Scheme.{u}} (b : T ⟶ S) (Z : Over S)
    (h : FinitePresentation Z.hom) : FinitePresentation ((Over.pullback b).obj Z).hom := by
  let _ : LocallyOfFinitePresentation Z.hom := h.1
  let _ : QuasiCompact Z.hom := h.2.1
  let _ : QuasiSeparated Z.hom := h.2.2
  change FinitePresentation (pullback.snd Z.hom b)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

section ProperModel

variable (hmod : LimitDescent.HasFinitePresentationModels.{u})

include hmod

/-- A proper morphism of finite presentation over a cofiltered limit of Noetherian schemes
indexed by a category in the scheme universe is the base change of a proper morphism of finite
presentation over a stage.

Part (1) of Tag 01ZM produces the model, Tag 01ZQ makes it separated at a later stage, and Tag
081F makes it proper at a later stage still. -/
private lemma exists_isProper_model_of_small_limit
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsNoetherian (D.obj i)]
    [∀ {i j : J} (a : i ⟶ j), IsAffineHom (D.map a)]
    {X : Scheme.{u}} (f : X ⟶ c.pt) [IsProper f]
    (hfp : FinitePresentation f) :
    ∃ (i : J) (Z : Over (D.obj i)), FinitePresentation Z.hom ∧
      IsProper Z.hom ∧ Nonempty (Over.mk f ≅ (Over.pullback (c.π.app i)).obj Z) := by
  classical
  obtain ⟨i, Z, hZ, ⟨e⟩⟩ := hmod D c hc (Over.mk f) hfp
  let _ : CompactSpace (D.obj i) := inferInstance
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_finitePresentation Z hZ
  let t : Z ⟶ Over.mk (𝟙 (D.obj i)) := Over.homMk Z.hom
  let _ : CompactSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (CompactSpace (D.obj i))
  let _ : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  have hlim : IsProper ((Over.pullback (c.π.app i)).obj Z).hom := prop_of_overIso (@IsProper) e ‹_›
  let _ : IsSeparated ((Over.pullback (c.π.app i)).map t).left :=
    (overPullback_map_terminal_iff (@IsSeparated) _ Z).mpr hlim.toIsSeparated
  obtain ⟨j, a, hsepj⟩ :=
    exists_isSeparated_baseChange_of_isLimit D c i Z (Over.mk (𝟙 (D.obj i))) t hc
  let Z' : Over (D.obj j) := (Over.pullback (D.map a)).obj Z
  have hfpZ' : FinitePresentation Z'.hom := finitePresentation_pullback_hom (D.map a) Z hZ
  let _ : LocallyOfFinitePresentation Z'.hom := hfpZ'.1
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_finitePresentation Z' hfpZ'
  let _ : IsSeparated Z'.hom := (overPullback_map_terminal_iff (@IsSeparated) _ Z).mp hsepj
  let t' : Z' ⟶ Over.mk (𝟙 (D.obj j)) := Over.homMk Z'.hom
  let _ : CompactSpace (Over.mk (𝟙 (D.obj j))).left :=
    inferInstanceAs (CompactSpace (D.obj j))
  let _ : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj j))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj j))
  let _ : IsNoetherian (Over.mk (𝟙 (D.obj j))).left :=
    inferInstanceAs (IsNoetherian (D.obj j))
  let _ : LocallyOfFiniteType t'.left := inferInstanceAs (LocallyOfFiniteType Z'.hom)
  let _ : IsSeparated t'.left := inferInstanceAs (IsSeparated Z'.hom)
  let eShift := overPullbackObj_shiftIso D c a Z
  let _ : IsProper ((Over.pullback (c.π.app j)).map t').left :=
    (overPullback_map_terminal_iff (@IsProper) _ Z').mpr
      (prop_of_overIso (@IsProper) eShift hlim)
  obtain ⟨m, g, hproper⟩ :=
    exists_isProper_baseChange_of_isLimit_of_isNoetherian D c hc j Z'
      (Over.mk (𝟙 (D.obj j))) t'
  let Z'' : Over (D.obj m) := (Over.pullback (D.map g)).obj Z'
  exact ⟨m, Z'', finitePresentation_pullback_hom (D.map g) Z' hfpZ',
    (overPullback_map_terminal_iff (@IsProper) _ Z').mp hproper,
    ⟨e ≪≫ eShift ≪≫ overPullbackObj_shiftIso D c g Z'⟩⟩

attribute [local instance] IsCofiltered.isConnected in
/-- The same, for a system of schemes affine and scheme-theoretically dominant over a base, at an
index universe unrelated to the scheme universe. -/
private lemma exists_isProper_model_of_affine_dominant_limit
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : Iᵒᵖ ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsNoetherian (D.obj i).left]
    [∀ i, IsAffineHom (D.obj i).hom] [IsAffineHom c.pt.hom]
    [∀ i, QuasiCompact (c.π.app i).left]
    [∀ i, IsSchemeTheoreticallyDominant (c.π.app i).left]
    {X : Scheme.{u}} (f : X ⟶ c.pt.left) [IsProper f]
    (hfp : FinitePresentation f) :
    ∃ (i : Iᵒᵖ) (Z : Over (D.obj i).left), FinitePresentation Z.hom ∧
      IsProper Z.hom ∧ Nonempty (Over.mk f ≅ (Over.pullback (c.π.app i).left).obj Z) := by
  obtain ⟨J, hJ, hne, hd, e, ⟨he⟩⟩ :=
    exists_small_isLimit_whisker_of_isSchemeTheoreticallyDominant D c hc
  let _ := hJ
  let _ := hne
  let _ := hd
  let E := e.monotone.functor.op
  let A := (E ⋙ D) ⋙ Over.forget S
  let c' := (Over.forget S).mapCone (c.whisker E)
  let _ (j : Jᵒᵖ) : IsNoetherian (A.obj j) := inferInstanceAs
    (IsNoetherian (D.obj (E.obj j)).left)
  let _ {j k : Jᵒᵖ} (a : j ⟶ k) : IsAffineHom (A.map a) := by
    change IsAffineHom (D.map (E.map a)).left
    have : IsAffineHom ((D.map (E.map a)).left ≫ (D.obj (E.obj k)).hom) := by
      rw [(D.map (E.map a)).w]
      infer_instance
    exact IsAffineHom.of_comp _ (D.obj (E.obj k)).hom
  obtain ⟨j, Z, hZ, hprop, hIso⟩ := exists_isProper_model_of_small_limit hmod A c'
    (isLimitOfPreserves (Over.forget S) he) f hfp
  exact ⟨E.obj j, Z, hZ, hprop, hIso⟩

attribute [local instance] IsCofiltered.isConnected in
/-- A proper morphism of finite presentation over a limit of Noetherian schemes with affine
transition morphisms and scheme-theoretically dominant projections is the base change of a proper
morphism of finite presentation over a stage. -/
private lemma exists_isProper_model_of_noetherian_limit
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsNoetherian (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i, IsSchemeTheoreticallyDominant (c.π.app i)]
    {X : Scheme.{u}} (f : X ⟶ c.pt) [IsProper f]
    (hfp : FinitePresentation f) :
    ∃ (i : Iᵒᵖ) (Z : Over (D.obj i)), FinitePresentation Z.hom ∧
      IsProper Z.hom ∧ Nonempty (Over.mk f ≅ (Over.pullback (c.π.app i)).obj Z) := by
  obtain ⟨i⟩ := ‹Nonempty I›
  let _ : Nonempty (Set.Ici i) := ⟨⟨i, le_rfl⟩⟩
  let _ := directed_tail i
  let _ := initial_tailToOver i
  let E := tailToOver i
  let A := E ⋙ Over.post D
  let c' := ((Over.conePost D (op i)).obj c).whisker E
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv E _).symm
    (Over.isLimitConePost (op i) hc)
  let _ (j : (Set.Ici i)ᵒᵖ) : IsNoetherian (A.obj j).left :=
    inferInstanceAs (IsNoetherian (D.obj (E.obj j).left))
  let _ (j : (Set.Ici i)ᵒᵖ) : IsAffineHom (A.obj j).hom :=
    inferInstanceAs (IsAffineHom (D.map (E.obj j).hom))
  let _ : IsAffineHom c'.pt.hom := EventualLimit.isAffineHom_π_app D c hc (op i)
  let _ (j : (Set.Ici i)ᵒᵖ) : QuasiCompact (c'.π.app j).left := by
    change QuasiCompact (c.π.app (E.obj j).left)
    let _ := EventualLimit.isAffineHom_π_app D c hc (E.obj j).left
    infer_instance
  let _ (j : (Set.Ici i)ᵒᵖ) : IsSchemeTheoreticallyDominant (c'.π.app j).left :=
    inferInstanceAs (IsSchemeTheoreticallyDominant (c.π.app (E.obj j).left))
  let f' : X ⟶ c'.pt.left := f
  let _ : IsProper f' := inferInstanceAs (IsProper f)
  obtain ⟨j, Z, hZ, hprop, hIso⟩ :=
    exists_isProper_model_of_affine_dominant_limit hmod A c' hc' f' hfp
  exact ⟨(E.obj j).left, Z, hZ, hprop, hIso⟩

end ProperModel

namespace LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

section ImageSystemModel

variable (hmod : LimitDescent.HasFinitePresentationModels.{u})

include hmod

attribute [local instance] IsCofiltered.isConnected in
/-- **The 01ZM/081F half of Tag 0CNV's proof.** A proper morphism of finite presentation to a
scheme of finite type over the limit is the base change of a proper morphism of finite
presentation over some stage of the image system of a good diagram for the target. -/
lemma exists_isProper_model_imageSystem
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pY : Y ⟶ D.limitScheme}
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    (f : X ⟶ Y) [IsProper f] (hfp : FinitePresentation f)
    (G : GoodDiagram D pY) :
    ∃ (j : Over (op G.index)) (Z : Over ((GoodDiagram.imageSystem G).obj j)),
      FinitePresentation Z.hom ∧ IsProper Z.hom ∧
      Nonempty (Over.mk f ≅
        (Over.pullback ((GoodDiagram.imageCone G).π.app j)).obj Z) := by
  let _ : Nonempty (Set.Ici G.index) := ⟨⟨G.index, le_rfl⟩⟩
  let _ := directed_tail G.index
  let _ := initial_tailToOver G.index
  let T := tailToOver G.index
  let A := T ⋙ GoodDiagram.imageSystem G
  let c := (GoodDiagram.imageCone G).whisker T
  have hc : IsLimit c := (Functor.Initial.isLimitWhiskerEquiv T _).symm
    (GoodDiagram.isLimit_imageCone D pY G)
  let _ (j : (Set.Ici G.index)ᵒᵖ) : IsNoetherian (A.obj j) :=
    inferInstanceAs (IsNoetherian (GoodDiagram.stageMap G (T.obj j)).image)
  let _ {j k : (Set.Ici G.index)ᵒᵖ} (a : j ⟶ k) : IsAffineHom (A.map a) :=
    inferInstanceAs (IsAffineHom (GoodDiagram.imageTransition G (T.map a)))
  let _ (j : (Set.Ici G.index)ᵒᵖ) : IsSchemeTheoreticallyDominant (c.π.app j) := by
    let _ : QuasiCompact (GoodDiagram.stageMap G (T.obj j)) :=
      GoodDiagram.quasiCompact_stageMap G (T.obj j)
    exact ⟨Scheme.Hom.ker_toImage (GoodDiagram.stageMap G (T.obj j))⟩
  let f' : X ⟶ c.pt := f
  let _ : IsProper f' := inferInstanceAs (IsProper f)
  obtain ⟨j, Z, hZ, hprop, hIso⟩ :=
    exists_isProper_model_of_noetherian_limit hmod A c hc f' hfp
  exact ⟨T.obj j, Z, hZ, hprop, hIso⟩

end ImageSystemModel

/-- **Tag 0CNV, reduced to Tag 09ZR.** The conclusion of Tag 0CNV for a given morphism `F` of
image systems, on the single hypothesis that `f` factors as a closed immersion `ι : X ⟶ X'`
followed by a morphism `X' ⟶ Y` which is proper and of finite presentation — which is the
consequence of Tag 09ZR that the Stacks proof of Tag 0CNV uses.

The two descents of the Stacks proof are performed here: part (1) of Tag 01ZM presents `X' ⟶ Y`
as a model over a stage of the image system of `GY'`, and Tag 081F makes that model proper at a
later stage. See the module documentation for which smallness hypothesis on `I` is discharged
here and which is inherited from Tag 0CNS. -/
theorem eventually_isProper_morphismAt_of_exists_factorisation [FinallySmall.{u} I]
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY)
    (h09ZR : ∃ (X' : Scheme.{u}) (g : X' ⟶ Y) (ι : X ⟶ X') (_ : IsClosedImmersion ι),
      ι ≫ g = f ∧ IsProper g ∧ FinitePresentation g) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)), i₃ ≤ unop j.left → IsProper (F.maps.app j) := by
  obtain ⟨X', g, ι, hι, hιg, hprop, hfp⟩ := h09ZR
  obtain ⟨j, Z, hZ, hpZ, hIso⟩ :=
    exists_isProper_model_imageSystem LimitDescent.hasFinitePresentationModels.{u} D g hfp GY
  exact eventually_isProper_morphismAt_of_exists_properModel D f hf GX GY i₀ hX hY F
    ⟨X', g, ι, hι, hιg, GoodDiagram.ofStage GY j, Z, hZ, hpZ, hIso⟩

/-! ### The hypothesis of Tag 09ZR is inhabited

A theorem over an uninhabited hypothesis is vacuous, so the two statements
below exhibit `h09ZR`. The first is the degenerate factorisation; the second is the case of
Tag 09ZR that this repository already has, and it makes Tag 0CNV unconditional for a locally
Noetherian target. -/

/-- The factorisation asked for by Tag 09ZR, when `f` is *already* proper and of finite
presentation: take `X' = X` and `ι = 𝟙 X`.

This is the base case of the hypothesis `h09ZR` of
`eventually_isProper_morphismAt_of_exists_factorisation`, and the reason that theorem is not
vacuous. -/
lemma exists_factorisation_of_finitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hfp : FinitePresentation f) :
    ∃ (X' : Scheme.{u}) (g : X' ⟶ Y) (ι : X ⟶ X') (_ : IsClosedImmersion ι),
      ι ≫ g = f ∧ IsProper g ∧ FinitePresentation g :=
  ⟨X, f, 𝟙 X, inferInstance, Category.id_comp f, ‹IsProper f›, hfp⟩

/-- **Tag 0CNV for a locally Noetherian target, unconditionally.** Over a locally Noetherian `Y`
the factorisation of Tag 09ZR is the degenerate one, because a proper morphism onto a locally
Noetherian scheme is already of finite presentation — [Stacks, Tag 01TX] part (2),
`AlgebraicGeometry.finitePresentation_of_finiteType`. So Tag 09ZR contributes nothing in that
case and the tag's conclusion holds with no hypothesis beyond its own.

`@[stacks 0CNV]` is still **withheld**: `[IsLocallyNoetherian Y]` is a hypothesis the tag does not
carry, and it is exactly the hypothesis Tag 09ZR exists to remove. Tag 0CNV applies Tag 09ZR to
`f : X ⟶ Y` with `Y` merely quasi-compact and quasi-separated over the limit, which is why this
corollary does not discharge it. -/
theorem eventually_isProper_morphismAt_of_isLocallyNoetherian [FinallySmall.{u} I]
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    [IsProper f] [IsLocallyNoetherian Y]
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)), i₃ ≤ unop j.left → IsProper (F.maps.app j) :=
  eventually_isProper_morphismAt_of_exists_factorisation D f hf GX GY i₀ hX hY F
    (exists_factorisation_of_finitePresentation f (finitePresentation_of_finiteType f))

end LimitNoetherianSituation

end AlgebraicGeometry

end
