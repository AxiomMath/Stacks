module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesAffineCaseTriple
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesAffineCaseSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesAffineCaseBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMapChartFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFMapCompChartFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas

/-!
# The overlap condition of the module of Stacks 0AEX at an affine-legged triple

In a formal glueing situation over a space `X` represented by a chart `Z₀`, take a glueing
triple `(U' ⟵ V' ⟶ Y')` with affine legs `g_U : U' ⟶ U`, `g_Y : Y' ⟶ Y`, and a module triple
`(H, G, φ)` identified with `(g_{U*}𝒪_{U'}, g_{Y*}𝒪_{Y'})`, with `φ` the composite of the two
affine base change isomorphisms through `g_{V*}𝒪_{V'}`.  The sections over `Z₀` of `j_*H` and
of `f_*G` are read as global functions on `U'` and on `Y'`, and those of `(f ∘ j')_*(G|_V)` as
global functions on `V'`.  This file proves that the two canonical maps of Stacks 0AEX into the
sections of `(f ∘ j')_*(G|_V)` become, under these readings, the two restrictions to `V'`.

The statements are made for an arbitrary module triple carrying identifications with the
direct images, which keeps all comparison isomorphisms as variables.  Every statement is written
in the exact syntactic form in which the next one consumes it: the comparison of direct images of
Stacks 03LU is only ever applied to sections whose type is the iterated direct image.

## Main results

* `AlgebraicGeometry.Space.pushforwardUnitGlobal_baseChange_sections`: global functions of a
  direct image along an affine base change.
* `AlgebraicGeometry.Space.pushforwardUnitGlobal_baseChange_unit_sections`: the same, through the
  unit of `g^* ⊣ g_*`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.overlapReading_restrictionOverlapMap` and
  `overlapReading_ambientOverlapMap`: the two canonical maps of Stacks 0AEX, read on `V'`.

## References

* [Stacks Project, Tag 0AEX](https://stacks.math.columbia.edu/tag/0AEX)
* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every algebraic space has a surjective étale scheme chart. -/
theorem exists_surjective_chart (Y : AlgebraicSpaces B S hS) :
    ∃ V : SmallEtale B S hS Y.1,
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) V.1.hom := by
  obtain ⟨V₀, q, hqS, hqE⟩ := Y.2.exists_atlas
  exact ⟨⟨CostructuredArrow.mk q, hqE⟩, hqS⟩

/-- Over a surjective étale scheme chart `V` of `Y`, a morphism `g : Y' ⟶ Y` has a surjective
étale scheme chart of `Y'` lying over `V`. -/
theorem exists_surjective_chart_over {Y' Y : AlgebraicSpaces B S hS} (g : Y' ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (hV : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) V.1.hom) :
    ∃ (U' : SmallEtale B S hS Y'.1)
      (d : (SmallEtale.toOver B S hS Y'.1).obj U' ⟶ (SmallEtale.toOver B S hS Y.1).obj V),
      U'.1.hom ≫ g.hom = yoneda.map d ≫ V.1.hom ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) U'.1.hom := by
  obtain ⟨U₀, p, α, hcomm, hpS, hpE⟩ :=
    exists_surjective_etale_presentation_lift B S hS Y'.2 Y.2 g.hom V.1.left V.1.hom hV V.2
  exact ⟨⟨CostructuredArrow.mk p, hpE⟩, α, hcomm, hpS⟩

section BaseChangeCharts

variable {X Y X' Y' Z : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (k : Y ⟶ Z) (Z₀ : SmallEtale B S hS Z.1) [IsIso Z₀.1.hom]
    {T : SmallEtale B S hS X'.1} {W : SmallEtale B S hS X.1} {U' : SmallEtale B S hS Y'.1}
    {V : SmallEtale B S hS Y.1}
    (a : (SmallEtale.toOver B S hS X'.1).obj T ⟶ (SmallEtale.toOver B S hS X.1).obj W)
    (b : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (c : (SmallEtale.toOver B S hS X'.1).obj T ⟶ (SmallEtale.toOver B S hS Y'.1).obj U')
    (d : (SmallEtale.toOver B S hS Y'.1).obj U' ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (eV : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj Z₀)
    (ha : T.1.hom ≫ g'.hom = yoneda.map a ≫ W.1.hom)
    (hb : W.1.hom ≫ f.hom = yoneda.map b ≫ V.1.hom)
    (hc : T.1.hom ≫ f'.hom = yoneda.map c ≫ U'.1.hom)
    (hd : U'.1.hom ≫ g.hom = yoneda.map d ≫ V.1.hom)
    (heV : V.1.hom ≫ k.hom = yoneda.map eV ≫ Z₀.1.hom)

include ha hb hc in
/-- The affine base change isomorphism of the structure sheaf carries the unit section of a chart
projection to the pullback of the chart projection along the cube. -/
theorem modulePushforwardCounitApp_pullbackPushforwardUnitIso_unitSection
    (sq : IsPullback g' f' f g) (hf : IsAffineHom B S hS f.hom) (habcd : a ≫ b = c ≫ d)
    (s : ((modulePushforward B S hS f).obj
      (SheafOfModules.unit (structureRingSheaf B S hS X))).val.obj (op V)) :
    modulePushforwardCounitApp B S hS f' (SheafOfModules.unit (structureRingSheaf B S hS X'))
        ⟨T, U', c, hc⟩
        ((modulePullbackPushforwardUnitIso sq hf).hom.val.app (op U')
          (modulePullbackUnitSection B S hS g ((modulePushforward B S hS f).obj
            (SheafOfModules.unit (structureRingSheaf B S hS X))) ⟨U', V, d, hd⟩ s)) =
      chartDiagramRestrict B S hS g' ⟨T, W, a, ha⟩
        (modulePushforwardCounitApp B S hS f (SheafOfModules.unit (structureRingSheaf B S hS X))
          ⟨W, V, b, hb⟩ s) := by
  have hβ := congrArg (fun m => m.val.app (op U')
    (modulePullbackUnitSection B S hS g ((modulePushforward B S hS f).obj
      (SheafOfModules.unit (structureRingSheaf B S hS X))) ⟨U', V, d, hd⟩ s))
    (modulePullbackPushforwardUnitIso_hom sq hf)
  refine (congrArg (modulePushforwardCounitApp B S hS f'
    (SheafOfModules.unit (structureRingSheaf B S hS X')) ⟨T, U', c, hc⟩) hβ).trans ?_
  refine (modulePushforwardCounitApp_map B S hS f' (modulePullbackUnitIso B S hS g').hom
    ⟨T, U', c, hc⟩ _).trans ?_
  refine (congrArg ((modulePullbackUnitIso B S hS g').hom.val.app (op T))
    (modulePushforwardCounitApp_moduleBaseChangeMap_unitSection sq.w _ a b c d ha hb hc hd
      habcd s)).trans ?_
  exact modulePullbackUnitIso_hom_unitSection B S hS g' ⟨T, W, a, ha⟩ _

end BaseChangeCharts

/-- The unit section of a module pullback is natural in the module. -/
theorem modulePullbackUnitSection_map {X X' : AlgebraicSpaces B S hS} (g : X ⟶ X')
    {M M' : Modules.{u, u} B S hS X'.1 X'.2} (a : M ⟶ M') (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (s : M.val.obj (op d.V)) :
    ((modulePullback B S hS g).map a).val.app (op d.U) (modulePullbackUnitSection B S hS g M d s) =
      modulePullbackUnitSection B S hS g M' d (a.val.app (op d.V) s) := by
  have hunit := congrArg
    (fun q : M ⟶ (modulePushforward B S hS g).obj ((modulePullback B S hS g).obj M') =>
      q.val.app (op d.V) s) ((modulePullbackAdjunction B S hS g).unit.naturality a)
  exact (modulePushforwardCounitApp_map B S hS g ((modulePullback B S hS g).map a) d _).symm.trans
    (congrArg (modulePushforwardCounitApp B S hS g ((modulePullback B S hS g).obj M') d)
      hunit).symm

/-- The sections of an isomorphism of modules are a bijection. -/
theorem bijective_val_app_apply_of_isIso {X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N) (hφ : IsIso φ) (W : SmallEtale B S hS X.1) :
    Function.Bijective (fun x : M.val.obj (op W) => φ.val.app (op W) x) := by
  have h1 : ∀ x : M.val.obj (op W), (inv φ).val.app (op W) (φ.val.app (op W) x) = x :=
    fun x => congrArg (fun q : M ⟶ M => q.val.app (op W) x) (IsIso.hom_inv_id φ)
  have h2 : ∀ y : N.val.obj (op W), φ.val.app (op W) ((inv φ).val.app (op W) y) = y :=
    fun y => congrArg (fun q : N ⟶ N => q.val.app (op W) y) (IsIso.inv_hom_id φ)
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

/-- The reading of sections as global functions is additive. -/
theorem pushforwardUnitGlobal_add {P X : AlgebraicSpaces B S hS} (h : P ⟶ X)
    (Z₀ : SmallEtale B S hS X.1) [IsIso Z₀.1.hom]
    (x y : ((modulePushforward B S hS h).obj
      (SheafOfModules.unit (structureRingSheaf B S hS P))).val.obj (op Z₀)) :
    pushforwardUnitGlobal B S hS h Z₀ (x + y) =
      pushforwardUnitGlobal B S hS h Z₀ x + pushforwardUnitGlobal B S hS h Z₀ y :=
  Subtype.ext (funext fun E =>
    modulePushforwardCounitApp_add B S hS h _ (isoChartDiagram B S hS h Z₀ E.unop) x y)

section Of

variable {P Q X : AlgebraicSpaces B S hS} (h : P ⟶ Q) (k : Q ⟶ X)

/-! Below, a section `m` over `Z₀` of an `𝒪_X`-module `M` together with a morphism
`φ : M ⟶ k_*h_*F` is read through the composite `φ ≫ (k_*h_* ≅ (h ≫ k)_*)`; the composite is
never split at the comparison isomorphism, whose source is `(h_* ⋙ k_*)F` rather than
`k_*(h_*F)`. -/

/-- A composite into `(h ≫ k)_*F` ending with the comparison of Stacks 03LU, on sections. -/
theorem compIso_comp_val_app_apply (F : Modules.{u, u} B S hS P.1 P.2)
    {M : Modules.{u, u} B S hS X.1 X.2}
    (φ : M ⟶ (modulePushforward B S hS k).obj ((modulePushforward B S hS h).obj F))
    (W : SmallEtale B S hS X.1) (x : M.val.obj (op W)) :
    (φ ≫ (modulePushforwardCompIso B S hS h k).hom.app F).val.app (op W) x =
      ((modulePushforwardCompIso B S hS h k).hom.app F).val.app (op W) (φ.val.app (op W) x) :=
  Stacks.SheafOfModules.comp_val_app_apply φ _ (op W) x

/-- **The chart formula of a composite into `(h ≫ k)_*F`**, in the form of the linear maps of
sections. -/
theorem modulePushforwardHomFMap_comp_compIso_app (F : Modules.{u, u} B S hS P.1 P.2)
    {M : Modules.{u, u} B S hS X.1 X.2}
    (φ : M ⟶ (modulePushforward B S hS k).obj ((modulePushforward B S hS h).obj F))
    {U : SmallEtale B S hS P.1} {V : SmallEtale B S hS Q.1} {W : SmallEtale B S hS X.1}
    (a : (SmallEtale.toOver B S hS P.1).obj U ⟶ (SmallEtale.toOver B S hS Q.1).obj V)
    (b : (SmallEtale.toOver B S hS Q.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj W)
    (ha : U.1.hom ≫ h.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ k.hom = yoneda.map b ≫ W.1.hom) (m : M.val.obj (op W)) :
    (modulePushforwardHomFMap B S hS (h ≫ k) F M
        (φ ≫ (modulePushforwardCompIso B S hS h k).hom.app F)).app
        (ChartDiagram.comp B S hS h k a b ha hb) m =
      (modulePushforwardCounit B S hS h F).app ⟨U, V, a, ha⟩
        ((modulePushforwardHomFMap B S hS k _ M φ).app ⟨V, W, b, hb⟩ m) := by
  have hc := ModuleFMap.compOfIso_app B S hS h k a b ha hb F ((modulePushforward B S hS h).obj F) M
    (modulePushforwardHomFMap B S hS k _ M φ) (modulePushforwardCounit B S hS h F)
    (modulePushforwardCompIso B S hS h k)
    (moduleSheafFunctor_map_modulePushforwardCompIso_hom_app B S hS h k F) m
  rw [ModuleFMap.compOfIso, moduleFMapCompHom_eq, moduleFMapHom_modulePushforwardHomFMap,
    moduleFMapHom_modulePushforwardCounit, CategoryTheory.Functor.map_id, Category.id_comp] at hc
  exact hc

/-- **The chart formula of a composite into `(h ≫ k)_*F`**: the chart projection at a composed
chart diagram is the iterated chart projection. -/
theorem modulePushforwardCounitApp_comp_compIso (F : Modules.{u, u} B S hS P.1 P.2)
    {M : Modules.{u, u} B S hS X.1 X.2}
    (φ : M ⟶ (modulePushforward B S hS k).obj ((modulePushforward B S hS h).obj F))
    {U : SmallEtale B S hS P.1} {V : SmallEtale B S hS Q.1} {W : SmallEtale B S hS X.1}
    (a : (SmallEtale.toOver B S hS P.1).obj U ⟶ (SmallEtale.toOver B S hS Q.1).obj V)
    (b : (SmallEtale.toOver B S hS Q.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj W)
    (ha : U.1.hom ≫ h.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ k.hom = yoneda.map b ≫ W.1.hom)
    (g : (SmallEtale.toOver B S hS P.1).obj U ⟶ (SmallEtale.toOver B S hS X.1).obj W)
    (hg : U.1.hom ≫ (h ≫ k).hom = yoneda.map g ≫ W.1.hom) (hab : g = a ≫ b)
    (m : M.val.obj (op W)) :
    modulePushforwardCounitApp B S hS (h ≫ k) F ⟨U, W, g, hg⟩
        ((φ ≫ (modulePushforwardCompIso B S hS h k).hom.app F).val.app (op W) m) =
      modulePushforwardCounitApp B S hS h F ⟨U, V, a, ha⟩
        (modulePushforwardCounitApp B S hS k _ ⟨V, W, b, hb⟩ (φ.val.app (op W) m)) := by
  subst hab
  have e1 : ∀ (H : Modules.{u, u} B S hS X.1 X.2)
      (q : H ⟶ (modulePushforward B S hS (h ≫ k)).obj F) (x : H.val.obj (op W)),
      (modulePushforwardHomFMap B S hS (h ≫ k) F H q).app
          (ChartDiagram.comp B S hS h k a b ha hb) x =
        modulePushforwardCounitApp B S hS (h ≫ k) F (ChartDiagram.comp B S hS h k a b ha hb)
          (q.val.app (op W) x) := fun _ _ _ => rfl
  have e2 : ∀ (H : Modules.{u, u} B S hS X.1 X.2)
      (q : H ⟶ (modulePushforward B S hS k).obj ((modulePushforward B S hS h).obj F))
      (x : H.val.obj (op W)),
      (modulePushforwardCounit B S hS h F).app ⟨U, V, a, ha⟩
          ((modulePushforwardHomFMap B S hS k _ H q).app ⟨V, W, b, hb⟩ x) =
        modulePushforwardCounitApp B S hS h F ⟨U, V, a, ha⟩
          (modulePushforwardCounitApp B S hS k _ ⟨V, W, b, hb⟩ (q.val.app (op W) x)) :=
    fun _ _ _ => rfl
  have h3 := modulePushforwardHomFMap_comp_compIso_app B S hS h k F φ a b ha hb m
  rw [e1, e2] at h3
  exact h3

variable (Z₀ : SmallEtale B S hS X.1) [IsIso Z₀.1.hom]

/-- **The global function of a section read through a composite**, at a chart: the iterated
chart projection, through any chart diagram over `h` and `k`. -/
theorem pushforwardUnitGlobal_comp_compIso_apply {M : Modules.{u, u} B S hS X.1 X.2}
    (φ : M ⟶ (modulePushforward B S hS k).obj ((modulePushforward B S hS h).obj
      (SheafOfModules.unit (structureRingSheaf B S hS P)))) (m : M.val.obj (op Z₀))
    {U : SmallEtale B S hS P.1} {V : SmallEtale B S hS Q.1}
    (a : (SmallEtale.toOver B S hS P.1).obj U ⟶ (SmallEtale.toOver B S hS Q.1).obj V)
    (b : (SmallEtale.toOver B S hS Q.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj Z₀)
    (ha : U.1.hom ≫ h.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ k.hom = yoneda.map b ≫ Z₀.1.hom) :
    @Eq ((structurePresheaf B S hS P.1 ⋙ forget CommRingCat).obj (op U))
      ((pushforwardUnitGlobal B S hS (h ≫ k) Z₀
        ((φ ≫ (modulePushforwardCompIso B S hS h k).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS P))).val.app (op Z₀) m)).1 (op U))
      (modulePushforwardCounitApp B S hS h _ ⟨U, V, a, ha⟩
        (modulePushforwardCounitApp B S hS k _ ⟨V, Z₀, b, hb⟩ (φ.val.app (op Z₀) m))) :=
  (pushforwardUnitGlobal_apply B S hS (h ≫ k) Z₀ _ U (a ≫ b)
    (ChartDiagram.comp B S hS h k a b ha hb).comm).trans
    (modulePushforwardCounitApp_comp_compIso B S hS h k _ φ a b ha hb (a ≫ b) _ rfl m)

/-- Through an isomorphism, the reading is bijective. -/
theorem bijective_pushforwardUnitGlobal_comp {M : Modules.{u, u} B S hS X.1 X.2}
    (φ : M ⟶ (modulePushforward B S hS k).obj ((modulePushforward B S hS h).obj
      (SheafOfModules.unit (structureRingSheaf B S hS P)))) (hφ : IsIso φ) :
    Function.Bijective (fun m : M.val.obj (op Z₀) =>
      pushforwardUnitGlobal B S hS (h ≫ k) Z₀
        ((φ ≫ (modulePushforwardCompIso B S hS h k).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS P))).val.app (op Z₀) m)) :=
  (bijective_pushforwardUnitGlobal B S hS (h ≫ k) Z₀).comp
    (bijective_val_app_apply_of_isIso B S hS (φ ≫ (modulePushforwardCompIso B S hS h k).hom.app
      (SheafOfModules.unit (structureRingSheaf B S hS P)))
      (@asIso _ _ _ _ φ hφ ≪≫ (modulePushforwardCompIso B S hS h k).app
        (SheafOfModules.unit (structureRingSheaf B S hS P))).isIso_hom Z₀)

/-- The reading is additive. -/
theorem pushforwardUnitGlobal_comp_add {M : Modules.{u, u} B S hS X.1 X.2}
    (φ : M ⟶ (modulePushforward B S hS k).obj ((modulePushforward B S hS h).obj
      (SheafOfModules.unit (structureRingSheaf B S hS P)))) (x y : M.val.obj (op Z₀)) :
    pushforwardUnitGlobal B S hS (h ≫ k) Z₀
        ((φ ≫ (modulePushforwardCompIso B S hS h k).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS P))).val.app (op Z₀) (x + y)) =
      pushforwardUnitGlobal B S hS (h ≫ k) Z₀
        ((φ ≫ (modulePushforwardCompIso B S hS h k).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS P))).val.app (op Z₀) x) +
      pushforwardUnitGlobal B S hS (h ≫ k) Z₀
        ((φ ≫ (modulePushforwardCompIso B S hS h k).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS P))).val.app (op Z₀) y) := by
  rw [map_add]
  exact Subtype.ext (funext fun E =>
    modulePushforwardCounitApp_add B S hS (h ≫ k) _ (isoChartDiagram B S hS (h ≫ k) Z₀ E.unop) _ _)

/-- The reading is semilinear. -/
theorem pushforwardUnitGlobal_comp_smul {M : Modules.{u, u} B S hS X.1 X.2}
    (φ : M ⟶ (modulePushforward B S hS k).obj ((modulePushforward B S hS h).obj
      (SheafOfModules.unit (structureRingSheaf B S hS P))))
    (r : chartRing B S hS X.1 X.2 Z₀) (x : M.val.obj (op Z₀)) :
    pushforwardUnitGlobal B S hS (h ≫ k) Z₀
        ((φ ≫ (modulePushforwardCompIso B S hS h k).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS P))).val.app (op Z₀) (r • x)) =
      pullbackToGlobalFunctions B S hS P ((SmallEtale.toOver B S hS X.1).obj Z₀)
          (ObjectProperty.homMk ((h ≫ k).hom ≫ (asIso Z₀.1.hom).inv)) r *
        pushforwardUnitGlobal B S hS (h ≫ k) Z₀
          ((φ ≫ (modulePushforwardCompIso B S hS h k).hom.app
            (SheafOfModules.unit (structureRingSheaf B S hS P))).val.app (op Z₀) x) := by
  rw [map_smul]
  exact pushforwardUnitGlobal_smul B S hS (h ≫ k) Z₀ r _

/-- The reading is compatible with the transport of direct images along an equality of
morphisms. -/
theorem pushforwardUnitGlobal_comp_eqToHom {k₁ k₂ : Q ⟶ X} (e : k₁ = k₂)
    {M : Modules.{u, u} B S hS X.1 X.2} {N : Modules.{u, u} B S hS Q.1 Q.2}
    (ψ : M ⟶ (modulePushforward B S hS k₁).obj N)
    (α : N ⟶ (modulePushforward B S hS h).obj (SheafOfModules.unit (structureRingSheaf B S hS P)))
    (w : M.val.obj (op Z₀)) :
    pushforwardUnitGlobal B S hS (h ≫ k₂) Z₀
        (((ψ ≫ (eqToHom (congrArg (fun k : Q ⟶ X => modulePushforward B S hS k) e)).app N) ≫
          (modulePushforward B S hS k₂).map α ≫ (modulePushforwardCompIso B S hS h k₂).hom.app
            (SheafOfModules.unit (structureRingSheaf B S hS P))).val.app (op Z₀) w) =
      pushforwardUnitGlobal B S hS (h ≫ k₁) Z₀
        ((ψ ≫ (modulePushforward B S hS k₁).map α ≫ (modulePushforwardCompIso B S hS h k₁).hom.app
            (SheafOfModules.unit (structureRingSheaf B S hS P))).val.app (op Z₀) w) := by
  subst e
  rw [eqToHom_refl, NatTrans.id_app, Category.comp_id]

end Of

/-- The chart-wise proof of global functions along an affine base change, on sections. -/
private theorem pushforwardUnitGlobal_baseChange_sections_aux {X Y X' Y' Z : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (hf : IsAffineHom B S hS f.hom) (k : Y ⟶ Z) (Z₀ : SmallEtale B S hS Z.1) [IsIso Z₀.1.hom]
    (s : ((modulePushforward B S hS (g ≫ k)).obj ((modulePushforward B S hS f').obj
      (SheafOfModules.unit (structureRingSheaf B S hS X')))).val.obj (op Z₀))
    (s₀ : ((modulePushforward B S hS k).obj ((modulePushforward B S hS f).obj
      (SheafOfModules.unit (structureRingSheaf B S hS X)))).val.obj (op Z₀))
    (hm : ∀ (U' : SmallEtale B S hS Y'.1) (V : SmallEtale B S hS Y.1)
      (d : (SmallEtale.toOver B S hS Y'.1).obj U' ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
      (eV : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj Z₀)
      (hd : U'.1.hom ≫ g.hom = yoneda.map d ≫ V.1.hom)
      (heV : V.1.hom ≫ k.hom = yoneda.map eV ≫ Z₀.1.hom)
      (hdE : U'.1.hom ≫ (g ≫ k).hom = yoneda.map (d ≫ eV) ≫ Z₀.1.hom),
      modulePushforwardCounitApp B S hS (g ≫ k) ((modulePushforward B S hS f').obj
          (SheafOfModules.unit (structureRingSheaf B S hS X'))) ⟨U', Z₀, d ≫ eV, hdE⟩ s =
        (modulePullbackPushforwardUnitIso sq hf).hom.val.app (op U')
          (modulePullbackUnitSection B S hS g ((modulePushforward B S hS f).obj
            (SheafOfModules.unit (structureRingSheaf B S hS X))) ⟨U', V, d, hd⟩
            (modulePushforwardCounitApp B S hS k _ ⟨V, Z₀, eV, heV⟩ s₀))) :
    pushforwardUnitGlobal B S hS (f' ≫ g ≫ k) Z₀
      (((modulePushforwardCompIso B S hS f' (g ≫ k)).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X'))).val.app (op Z₀) s) =
      globalFunctionsMap B S hS g' (pushforwardUnitGlobal B S hS (f ≫ k) Z₀
        (((modulePushforwardCompIso B S hS f k).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X))).val.app (op Z₀) s₀)) := by
  have hrf := relativelyRepresentable_of_isAffineHom B S hS f hf
  obtain ⟨V, hV⟩ := exists_surjective_chart B S hS Y
  obtain ⟨U', d, hd, hU'⟩ := exists_surjective_chart_over B S hS g V hV
  obtain ⟨T, c, hc, hT⟩ := exists_surjective_chart_over B S hS f' U' hU'
  obtain ⟨eV, heV⟩ : ∃ eV : (SmallEtale.toOver B S hS Y.1).obj V ⟶
      (SmallEtale.toOver B S hS Z.1).obj Z₀, V.1.hom ≫ k.hom = yoneda.map eV ≫ Z₀.1.hom :=
    ⟨_, (isoChartDiagram B S hS k Z₀ V).comm⟩
  have hcond : (T.1.hom ≫ g'.hom) ≫ f.hom = yoneda.map (c ≫ d) ≫ V.1.hom := by
    have w : g'.hom ≫ f.hom = f'.hom ≫ g.hom := congrArg (fun q => q.hom) sq.w
    rw [Category.assoc, w, ← Category.assoc, hc, Category.assoc, hd, ← Category.assoc,
      ← Functor.map_comp]
  obtain ⟨W, a, b, ha, hb, habcd⟩ : ∃ (W : SmallEtale B S hS X.1)
      (a : (SmallEtale.toOver B S hS X'.1).obj T ⟶ (SmallEtale.toOver B S hS X.1).obj W)
      (b : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj V),
      T.1.hom ≫ g'.hom = yoneda.map a ≫ W.1.hom ∧ W.1.hom ≫ f.hom = yoneda.map b ≫ V.1.hom ∧
        a ≫ b = c ≫ d :=
    ⟨(smallBaseChange B S hS f hrf).obj V, hrf.lift _ _ hcond, hrf.snd V.1.hom,
      (hrf.lift_fst _ _ hcond).symm, hrf.w V.1.hom, hrf.lift_snd _ _ hcond⟩
  have hdE : U'.1.hom ≫ (g ≫ k).hom = yoneda.map (d ≫ eV) ≫ Z₀.1.hom :=
    (ChartDiagram.comp B S hS g k d eV hd heV).comm
  have hcE := (ChartDiagram.comp B S hS f' (g ≫ k) c (d ≫ eV) hc hdE).comm
  have hbE := (ChartDiagram.comp B S hS f k b eV hb heV).comm
  apply globalFunctions_ext_of_surjective B S hS X' T hT
  refine (pushforwardUnitGlobal_apply B S hS (f' ≫ g ≫ k) Z₀ _ T (c ≫ d ≫ eV) hcE).trans ?_
  refine (modulePushforwardCounitApp_compIso' B S hS f' (g ≫ k) c (d ≫ eV) hc hdE _
    (c ≫ d ≫ eV) hcE rfl s).trans ?_
  refine (congrArg (modulePushforwardCounitApp B S hS f'
    (SheafOfModules.unit (structureRingSheaf B S hS X')) ⟨T, U', c, hc⟩)
    (hm U' V d eV hd heV hdE)).trans ?_
  refine (modulePushforwardCounitApp_pullbackPushforwardUnitIso_unitSection B S hS (a := a)
    (b := b) (c := c) (d := d) (ha := ha) (hb := hb) (hc := hc) (hd := hd) sq hf habcd _).trans ?_
  refine Eq.trans ?_ (globalFunctionsMap_apply_chart B S hS g' _ T W a ha).symm
  refine congrArg (chartDiagramRestrict B S hS g' ⟨T, W, a, ha⟩) ?_
  exact ((pushforwardUnitGlobal_apply B S hS (f ≫ k) Z₀ _ W (b ≫ eV) hbE).trans
    (modulePushforwardCounitApp_compIso' B S hS f k b eV hb heV _ (b ≫ eV) hbE rfl s₀)).symm

/-- **Global functions along an affine base change.**  For a cartesian square `X' = X ×_Y Y'`
with `f` affine, a morphism `k : Y ⟶ Z` to a space represented by `Z₀`, morphisms
`φ : M ⟶ k_*f_*𝒪_X` and `ψ : M ⟶ (g ≫ k)_*f'_*𝒪_{X'}` whose chart projections at a section `m`
correspond through the unit sections and the affine base change isomorphism (hypothesis `hm`),
the reading of `m` through `ψ` is the pullback along `g'` of its reading through `φ`. -/
theorem pushforwardUnitGlobal_comp_baseChange {X Y X' Y' Z : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (hf : IsAffineHom B S hS f.hom) (k : Y ⟶ Z) (Z₀ : SmallEtale B S hS Z.1) [IsIso Z₀.1.hom]
    {M : Modules.{u, u} B S hS Z.1 Z.2}
    (φ : M ⟶ (modulePushforward B S hS k).obj ((modulePushforward B S hS f).obj
      (SheafOfModules.unit (structureRingSheaf B S hS X))))
    (ψ : M ⟶ (modulePushforward B S hS (g ≫ k)).obj ((modulePushforward B S hS f').obj
      (SheafOfModules.unit (structureRingSheaf B S hS X')))) (m : M.val.obj (op Z₀))
    (hm : ∀ (U' : SmallEtale B S hS Y'.1) (V : SmallEtale B S hS Y.1)
      (d : (SmallEtale.toOver B S hS Y'.1).obj U' ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
      (eV : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj Z₀)
      (hd : U'.1.hom ≫ g.hom = yoneda.map d ≫ V.1.hom)
      (heV : V.1.hom ≫ k.hom = yoneda.map eV ≫ Z₀.1.hom)
      (hdE : U'.1.hom ≫ (g ≫ k).hom = yoneda.map (d ≫ eV) ≫ Z₀.1.hom),
      modulePushforwardCounitApp B S hS (g ≫ k) ((modulePushforward B S hS f').obj
          (SheafOfModules.unit (structureRingSheaf B S hS X'))) ⟨U', Z₀, d ≫ eV, hdE⟩
          (ψ.val.app (op Z₀) m) =
        (modulePullbackPushforwardUnitIso sq hf).hom.val.app (op U')
          (modulePullbackUnitSection B S hS g ((modulePushforward B S hS f).obj
            (SheafOfModules.unit (structureRingSheaf B S hS X))) ⟨U', V, d, hd⟩
            (modulePushforwardCounitApp B S hS k _ ⟨V, Z₀, eV, heV⟩ (φ.val.app (op Z₀) m)))) :
    pushforwardUnitGlobal B S hS (f' ≫ g ≫ k) Z₀
      ((ψ ≫ (modulePushforwardCompIso B S hS f' (g ≫ k)).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X'))).val.app (op Z₀) m) =
      globalFunctionsMap B S hS g' (pushforwardUnitGlobal B S hS (f ≫ k) Z₀
        ((φ ≫ (modulePushforwardCompIso B S hS f k).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X))).val.app (op Z₀) m)) := by
  rw [compIso_comp_val_app_apply B S hS f' (g ≫ k) _ ψ Z₀ m,
    compIso_comp_val_app_apply B S hS f k _ φ Z₀ m]
  exact pushforwardUnitGlobal_baseChange_sections_aux B S hS sq hf k Z₀ _ _ hm

/-- **Global functions along an affine base change, on sections.**  For a cartesian square
`X' = X ×_Y Y'` with `f` affine, a morphism `k : Y ⟶ Z` to a space represented by `Z₀`, and
sections `s` of `(g ≫ k)_*f'_*𝒪_{X'}` and `s₀` of `k_*f_*𝒪_X` over `Z₀` whose chart projections
correspond through the unit sections and the affine base change isomorphism (hypothesis `hm`),
the global function of `s` on `X'` is the pullback along `g'` of that of `s₀` on `X`. -/
theorem pushforwardUnitGlobal_baseChange_sections {X Y X' Y' Z : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (hf : IsAffineHom B S hS f.hom) (k : Y ⟶ Z) (Z₀ : SmallEtale B S hS Z.1) [IsIso Z₀.1.hom]
    (s : ((modulePushforward B S hS (g ≫ k)).obj ((modulePushforward B S hS f').obj
      (SheafOfModules.unit (structureRingSheaf B S hS X')))).val.obj (op Z₀))
    (s₀ : ((modulePushforward B S hS k).obj ((modulePushforward B S hS f).obj
      (SheafOfModules.unit (structureRingSheaf B S hS X)))).val.obj (op Z₀))
    (hm : ∀ (U' : SmallEtale B S hS Y'.1) (V : SmallEtale B S hS Y.1)
      (d : (SmallEtale.toOver B S hS Y'.1).obj U' ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
      (eV : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj Z₀)
      (hd : U'.1.hom ≫ g.hom = yoneda.map d ≫ V.1.hom)
      (heV : V.1.hom ≫ k.hom = yoneda.map eV ≫ Z₀.1.hom)
      (hdE : U'.1.hom ≫ (g ≫ k).hom = yoneda.map (d ≫ eV) ≫ Z₀.1.hom),
      modulePushforwardCounitApp B S hS (g ≫ k) ((modulePushforward B S hS f').obj
          (SheafOfModules.unit (structureRingSheaf B S hS X'))) ⟨U', Z₀, d ≫ eV, hdE⟩ s =
        (modulePullbackPushforwardUnitIso sq hf).hom.val.app (op U')
          (modulePullbackUnitSection B S hS g ((modulePushforward B S hS f).obj
            (SheafOfModules.unit (structureRingSheaf B S hS X))) ⟨U', V, d, hd⟩
            (modulePushforwardCounitApp B S hS k _ ⟨V, Z₀, eV, heV⟩ s₀))) :
    pushforwardUnitGlobal B S hS (f' ≫ g ≫ k) Z₀
      (((modulePushforwardCompIso B S hS f' (g ≫ k)).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X'))).val.app (op Z₀) s) =
      globalFunctionsMap B S hS g' (pushforwardUnitGlobal B S hS (f ≫ k) Z₀
        (((modulePushforwardCompIso B S hS f k).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X))).val.app (op Z₀) s₀)) :=
  pushforwardUnitGlobal_baseChange_sections_aux B S hS sq hf k Z₀ s s₀ hm

/-- An identity transport of functors acts trivially on sections. -/
theorem eqToHom_app_val_app_refl {P Q : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS P.1 P.2 ⥤ Modules.{u, u} B S hS Q.1 Q.2) (e : F = F)
    (N : Modules.{u, u} B S hS P.1 P.2) (W : SmallEtale B S hS Q.1) (z : (F.obj N).val.obj (op W)) :
    ((eqToHom e).app N).val.app (op W) z = z := by
  rw [eqToHom_refl, NatTrans.id_app]
  rfl

/-- The reading of sections is compatible with the transport of direct images along an equality
of morphisms, on sections. -/
theorem pushforwardUnitGlobal_eqToHom_sections {P Q X : AlgebraicSpaces B S hS} (h : P ⟶ Q)
    (Z₀ : SmallEtale B S hS X.1) [IsIso Z₀.1.hom] {k₁ k₂ : Q ⟶ X} (e : k₁ = k₂)
    {N : Modules.{u, u} B S hS Q.1 Q.2}
    (α : N ⟶ (modulePushforward B S hS h).obj (SheafOfModules.unit (structureRingSheaf B S hS P)))
    (z : ((modulePushforward B S hS k₁).obj N).val.obj (op Z₀)) :
    pushforwardUnitGlobal B S hS (h ≫ k₂) Z₀
        (((modulePushforwardCompIso B S hS h k₂).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS P))).val.app (op Z₀)
          (((modulePushforward B S hS k₂).map α).val.app (op Z₀)
            (((eqToHom (congrArg (fun k : Q ⟶ X => modulePushforward B S hS k) e)).app N).val.app
              (op Z₀) z))) =
      pushforwardUnitGlobal B S hS (h ≫ k₁) Z₀
        (((modulePushforwardCompIso B S hS h k₁).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS P))).val.app (op Z₀)
          (((modulePushforward B S hS k₁).map α).val.app (op Z₀) z)) := by
  subst e
  exact congrArg (fun w => pushforwardUnitGlobal B S hS (h ≫ k₁) Z₀
        (((modulePushforwardCompIso B S hS h k₁).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS P))).val.app (op Z₀)
          (((modulePushforward B S hS k₁).map α).val.app (op Z₀) w)))
    (eqToHom_app_val_app_refl B S hS (modulePushforward B S hS k₁) _ N Z₀ z)

/-- Two maps pushed forward along the same morphism, on sections. -/
theorem modulePushforward_map_val_app_map_val_app {Q X : AlgebraicSpaces B S hS} (k : Q ⟶ X)
    {N₁ N₂ N₃ : Modules.{u, u} B S hS Q.1 Q.2} (a : N₁ ⟶ N₂) (b : N₂ ⟶ N₃)
    (W : SmallEtale B S hS X.1) (z : ((modulePushforward B S hS k).obj N₁).val.obj (op W)) :
    ((modulePushforward B S hS k).map b).val.app (op W)
        (((modulePushforward B S hS k).map a).val.app (op W) z) =
      ((modulePushforward B S hS k).map (a ≫ b)).val.app (op W) z := by
  rw [Functor.map_comp]
  exact (Stacks.SheafOfModules.comp_val_app_apply ((modulePushforward B S hS k).map a)
    ((modulePushforward B S hS k).map b) (op W) z).symm

/-- **Global functions along an affine base change, from the unit, on sections.**  For a
module `Φ(τ)` on `Y` (a functor `Φ` at an object `τ`, so that the statement matches the
functorial maps of Stacks 0AEX on the nose) with a map `a : Φ(τ) ⟶ f_*𝒪_X`, a section `y` of
`k_*Φ(τ)` over `Z₀`, pushed along `k_*` of the unit of `g^* ⊣ g_*`, the comparison
`k_*g_* ≅ (g ≫ k)_*` and `(g ≫ k)_*` of `γ = g^*a ≫ β` with `β` the affine base change
isomorphism, reads as the pullback along `g'` of the global function of `(k_*a)(y)`. -/
theorem pushforwardUnitGlobal_baseChange_unit_sections {X Y X' Y' Z : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (hf : IsAffineHom B S hS f.hom) (k : Y ⟶ Z) (Z₀ : SmallEtale B S hS Z.1) [IsIso Z₀.1.hom]
    {𝒞 : Type*} [Category 𝒞] (Φ : 𝒞 ⥤ Modules.{u, u} B S hS Y.1 Y.2) (τ : 𝒞)
    (a : Φ.obj τ ⟶ (modulePushforward B S hS f).obj
      (SheafOfModules.unit (structureRingSheaf B S hS X)))
    (γ : (Φ ⋙ modulePullback B S hS g).obj τ ⟶ (modulePushforward B S hS f').obj
      (SheafOfModules.unit (structureRingSheaf B S hS X')))
    (hγ : γ = (modulePullback B S hS g).map a ≫ (modulePullbackPushforwardUnitIso sq hf).hom)
    (y : ((modulePushforward B S hS k).obj (Φ.obj τ)).val.obj (op Z₀)) :
    pushforwardUnitGlobal B S hS (f' ≫ g ≫ k) Z₀
      (((modulePushforwardCompIso B S hS f' (g ≫ k)).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X'))).val.app (op Z₀)
        (((modulePushforward B S hS (g ≫ k)).map γ).val.app (op Z₀)
          (((modulePushforwardCompIso B S hS g k).hom.app
              ((Φ ⋙ modulePullback B S hS g).obj τ)).val.app (op Z₀)
            (((modulePushforward B S hS k).map
              ((modulePullbackAdjunction B S hS g).unit.app (Φ.obj τ))).val.app (op Z₀) y)))) =
      globalFunctionsMap B S hS g' (pushforwardUnitGlobal B S hS (f ≫ k) Z₀
        (((modulePushforwardCompIso B S hS f k).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X))).val.app (op Z₀)
          (((modulePushforward B S hS k).map a).val.app (op Z₀) y))) := by
  refine pushforwardUnitGlobal_baseChange_sections B S hS sq hf k Z₀ _ _ ?_
  intro U' V d eV hd heV hdE
  refine (modulePushforwardCounitApp_map B S hS (g ≫ k) γ ⟨U', Z₀, d ≫ eV, hdE⟩ _).trans ?_
  subst hγ
  refine (Stacks.SheafOfModules.comp_val_app_apply ((modulePullback B S hS g).map a) _
    (op U') _).trans ?_
  refine congrArg (fun z => (modulePullbackPushforwardUnitIso sq hf).hom.val.app (op U') z) ?_
  refine Eq.trans ?_ ((congrArg (modulePullbackUnitSection B S hS g _ ⟨U', V, d, hd⟩)
    (modulePushforwardCounitApp_map B S hS k a ⟨V, Z₀, eV, heV⟩ y)).trans
    (modulePullbackUnitSection_map B S hS g a ⟨U', V, d, hd⟩ _).symm).symm
  refine congrArg (fun z => ((modulePullback B S hS g).map a).val.app (op U') z) ?_
  refine (modulePushforwardCounitApp_compIso' B S hS g k d eV hd heV _ (d ≫ eV) hdE rfl _).trans ?_
  exact congrArg (modulePushforwardCounitApp B S hS g _ ⟨U', V, d, hd⟩)
    (modulePushforwardCounitApp_map B S hS k _ ⟨V, Z₀, eV, heV⟩ y)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : FormalGlueingSituation B S hS)

/-- The second canonical map of Stacks 0AEX at a triple, as a composite of two morphisms. -/
theorem ambientOverlapMap_app_eq (t : D.moduleGlueingComma) :
    D.ambientOverlapMap.app t =
      (modulePushforward B S hS D.ambientMorphism).map
          ((modulePullbackAdjunction B S hS D.openImmersionOver).unit.app
            ((Comma.snd (modulePullback B S hS D.overlapRestriction)
              (modulePullback B S hS D.openImmersionOver)).obj t)) ≫
        (modulePushforwardCompIso B S hS D.openImmersionOver D.ambientMorphism).hom.app
          ((Comma.snd (modulePullback B S hS D.overlapRestriction)
            (modulePullback B S hS D.openImmersionOver) ⋙
            modulePullback B S hS D.openImmersionOver).obj t) := by
  rw [ambientOverlapMap_eq, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]

/-- The second canonical map of Stacks 0AEX on sections. -/
theorem ambientOverlapMap_app_apply (t : D.moduleGlueingComma) (W : SmallEtale B S hS D.spaceX.1)
    (y : (D.ambientDirectImage.obj t).val.obj (op W)) :
    (D.ambientOverlapMap.app t).val.app (op W) y =
      ((modulePushforwardCompIso B S hS D.openImmersionOver D.ambientMorphism).hom.app
        ((Comma.snd (modulePullback B S hS D.overlapRestriction)
          (modulePullback B S hS D.openImmersionOver) ⋙
          modulePullback B S hS D.openImmersionOver).obj t)).val.app (op W)
        (((modulePushforward B S hS D.ambientMorphism).map
          ((modulePullbackAdjunction B S hS D.openImmersionOver).unit.app
            ((Comma.snd (modulePullback B S hS D.overlapRestriction)
              (modulePullback B S hS D.openImmersionOver)).obj t))).val.app (op W) y) := by
  rw [ambientOverlapMap_app_eq]
  exact Stacks.SheafOfModules.comp_val_app_apply ((modulePushforward B S hS D.ambientMorphism).map
    ((modulePullbackAdjunction B S hS D.openImmersionOver).unit.app
      ((Comma.snd (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver)).obj t))) _ (op W) y

variable (G : (affineLegs D).FullSubcategory) (Z₀ : SmallEtale B S hS D.spaceX.1) [IsIso Z₀.1.hom]

/-- **The overlap reading of the second canonical map**, for a triple `t` with a map
`e_R : G ⟶ g_{Y*}𝒪_{Y'}` and `γ = j'^*e_R ≫ β_Y`, `β_Y : j'^*g_{Y*}𝒪_{Y'} ≅ g_{V*}𝒪_{V'}`: a
section of `f_*G` over `Z₀`, carried to `(f ∘ j')_*(G|_V)` and read on `V'` through `γ`, is the
restriction to `V'` of the global function on `Y'` of `f_*e_R` of the section. -/
theorem overlapReading_ambientOverlapMap (t : D.moduleGlueingComma)
    (eR : (Comma.snd (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver)).obj t ⟶
      (modulePushforward B S hS (D.affLegYHom G)).obj
      (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegY G))))
    (γ : (Comma.snd (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver) ⋙
        modulePullback B S hS D.openImmersionOver).obj t ⟶
      (modulePushforward B S hS (D.affLegVHom G)).obj
        (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegV G))))
    (hγ : γ = (modulePullback B S hS D.openImmersionOver).map eR ≫
      (modulePullbackPushforwardUnitIso (D.isPullback_affLegVY G) G.property.2.2).hom)
    (y : (D.ambientDirectImage.obj t).val.obj (op Z₀)) :
    pushforwardUnitGlobal B S hS (D.affLegVHom G ≫ D.openImmersionOver ≫ D.ambientMorphism) Z₀
      (((modulePushforwardCompIso B S hS (D.affLegVHom G)
          (D.openImmersionOver ≫ D.ambientMorphism)).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegV G)))).val.app (op Z₀)
        (((modulePushforward B S hS (D.openImmersionOver ≫ D.ambientMorphism)).map γ).val.app
          (op Z₀) ((D.ambientOverlapMap.app t).val.app (op Z₀) y))) =
      globalFunctionsMap B S hS (D.affLegVY G)
        (pushforwardUnitGlobal B S hS (D.affLegYHom G ≫ D.ambientMorphism) Z₀
          (((modulePushforwardCompIso B S hS (D.affLegYHom G) D.ambientMorphism).hom.app
            (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegY G)))).val.app (op Z₀)
            (((modulePushforward B S hS D.ambientMorphism).map eR).val.app (op Z₀) y))) := by
  rw [ambientOverlapMap_app_apply]
  exact pushforwardUnitGlobal_baseChange_unit_sections B S hS (D.isPullback_affLegVY G)
    G.property.2.2 D.ambientMorphism Z₀ (Comma.snd (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver)) t eR γ hγ y

/-- The first canonical map of Stacks 0AEX at a triple, as a composite of four morphisms. -/
theorem restrictionOverlapMap_app_eq (t : D.moduleGlueingComma) :
    D.restrictionOverlapMap.app t =
      (modulePushforward B S hS D.openImmersion).map
          ((modulePullbackAdjunction B S hS D.overlapRestriction).unit.app
            ((Comma.fst (modulePullback B S hS D.overlapRestriction)
              (modulePullback B S hS D.openImmersionOver)).obj t)) ≫
        (modulePushforwardCompIso B S hS D.overlapRestriction D.openImmersion).hom.app
          ((Comma.fst (modulePullback B S hS D.overlapRestriction)
            (modulePullback B S hS D.openImmersionOver) ⋙
            modulePullback B S hS D.overlapRestriction).obj t) ≫
        (modulePushforward B S hS (D.overlapRestriction ≫ D.openImmersion)).map
          ((Comma.natTrans (modulePullback B S hS D.overlapRestriction)
            (modulePullback B S hS D.openImmersionOver)).app t) ≫
        (eqToHom (congrArg (fun g : D.spaceV ⟶ D.spaceX => modulePushforward B S hS g)
          D.overlapRestriction_comp_openImmersion)).app
          ((Comma.snd (modulePullback B S hS D.overlapRestriction)
            (modulePullback B S hS D.openImmersionOver) ⋙
            modulePullback B S hS D.openImmersionOver).obj t) := by
  rw [restrictionOverlapMap_eq, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]

/-- The first canonical map of Stacks 0AEX on sections. -/
theorem restrictionOverlapMap_app_apply (t : D.moduleGlueingComma)
    (W : SmallEtale B S hS D.spaceX.1) (x : (D.restrictionDirectImage.obj t).val.obj (op W)) :
    (D.restrictionOverlapMap.app t).val.app (op W) x =
      ((eqToHom (congrArg (fun g : D.spaceV ⟶ D.spaceX => modulePushforward B S hS g)
          D.overlapRestriction_comp_openImmersion)).app
          ((Comma.snd (modulePullback B S hS D.overlapRestriction)
            (modulePullback B S hS D.openImmersionOver) ⋙
            modulePullback B S hS D.openImmersionOver).obj t)).val.app (op W)
        (((modulePushforward B S hS (D.overlapRestriction ≫ D.openImmersion)).map
          ((Comma.natTrans (modulePullback B S hS D.overlapRestriction)
            (modulePullback B S hS D.openImmersionOver)).app t)).val.app (op W)
          (((modulePushforwardCompIso B S hS D.overlapRestriction D.openImmersion).hom.app
            ((Comma.fst (modulePullback B S hS D.overlapRestriction)
              (modulePullback B S hS D.openImmersionOver) ⋙
              modulePullback B S hS D.overlapRestriction).obj t)).val.app (op W)
            (((modulePushforward B S hS D.openImmersion).map
              ((modulePullbackAdjunction B S hS D.overlapRestriction).unit.app
                ((Comma.fst (modulePullback B S hS D.overlapRestriction)
                  (modulePullback B S hS D.openImmersionOver)).obj t))).val.app (op W) x))) := by
  rw [restrictionOverlapMap_app_eq]
  refine (Stacks.SheafOfModules.comp_val_app_apply ((modulePushforward B S hS D.openImmersion).map
    ((modulePullbackAdjunction B S hS D.overlapRestriction).unit.app
      ((Comma.fst (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver)).obj t))) _ (op W) x).trans ?_
  refine (Stacks.SheafOfModules.comp_val_app_apply
    ((modulePushforwardCompIso B S hS D.overlapRestriction D.openImmersion).hom.app
      ((Comma.fst (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver) ⋙
        modulePullback B S hS D.overlapRestriction).obj t)) _ (op W) _).trans ?_
  exact Stacks.SheafOfModules.comp_val_app_apply
    ((modulePushforward B S hS (D.overlapRestriction ≫ D.openImmersion)).map
      ((Comma.natTrans (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver)).app t)) _ (op W) _

/-- **The overlap reading of the first canonical map**, for a triple `t = (H, G, φ)` with a map
`e_L : H ⟶ g_{U*}𝒪_{U'}` and a map `γ : G|_V ⟶ g_{V*}𝒪_{V'}` with `φ ≫ γ = r^*e_L ≫ β_U`: a
section of `j_*H` over `Z₀`, carried to `(f ∘ j')_*(G|_V)` and read on `V'` through `γ`, is the
restriction to `V'` of the global function on `U'` of `j_*e_L` of the section. -/
theorem overlapReading_restrictionOverlapMap (t : D.moduleGlueingComma)
    (eL : (Comma.fst (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver)).obj t ⟶
      (modulePushforward B S hS (D.affLegUHom G)).obj
        (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegU G))))
    (γ : (Comma.snd (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver) ⋙
        modulePullback B S hS D.openImmersionOver).obj t ⟶
      (modulePushforward B S hS (D.affLegVHom G)).obj
        (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegV G))))
    (hγ : (Comma.natTrans (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver)).app t ≫ γ =
      (modulePullback B S hS D.overlapRestriction).map eL ≫
        (modulePullbackPushforwardUnitIso (D.isPullback_affLegVU G) G.property.1).hom)
    (x : (D.restrictionDirectImage.obj t).val.obj (op Z₀)) :
    pushforwardUnitGlobal B S hS (D.affLegVHom G ≫ D.openImmersionOver ≫ D.ambientMorphism) Z₀
      (((modulePushforwardCompIso B S hS (D.affLegVHom G)
          (D.openImmersionOver ≫ D.ambientMorphism)).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegV G)))).val.app (op Z₀)
        (((modulePushforward B S hS (D.openImmersionOver ≫ D.ambientMorphism)).map γ).val.app
          (op Z₀) ((D.restrictionOverlapMap.app t).val.app (op Z₀) x))) =
      globalFunctionsMap B S hS (D.affLegVU G)
        (pushforwardUnitGlobal B S hS (D.affLegUHom G ≫ D.openImmersion) Z₀
          (((modulePushforwardCompIso B S hS (D.affLegUHom G) D.openImmersion).hom.app
            (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegU G)))).val.app (op Z₀)
            (((modulePushforward B S hS D.openImmersion).map eL).val.app (op Z₀) x))) := by
  rw [restrictionOverlapMap_app_apply]
  refine (pushforwardUnitGlobal_eqToHom_sections B S hS (D.affLegVHom G) Z₀
    D.overlapRestriction_comp_openImmersion γ _).trans ?_
  refine (congrArg (fun z => pushforwardUnitGlobal B S hS
    (D.affLegVHom G ≫ D.overlapRestriction ≫ D.openImmersion) Z₀
      (((modulePushforwardCompIso B S hS (D.affLegVHom G)
          (D.overlapRestriction ≫ D.openImmersion)).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegV G)))).val.app (op Z₀) z))
    (modulePushforward_map_val_app_map_val_app B S hS (D.overlapRestriction ≫ D.openImmersion)
      ((Comma.natTrans (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver)).app t) γ Z₀ _)).trans ?_
  exact pushforwardUnitGlobal_baseChange_unit_sections B S hS (D.isPullback_affLegVU G)
    G.property.1 D.openImmersion Z₀ (Comma.fst (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver)) t eL _ hγ x

end AlgebraicGeometry.Space.FormalGlueingSituation
