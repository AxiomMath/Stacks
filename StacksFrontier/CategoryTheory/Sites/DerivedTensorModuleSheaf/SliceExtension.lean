module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.DerivedTensorSingle
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.FiniteTorDimension
public import StacksFrontier.CategoryTheory.Sites.InverseImageTensor
public import StacksFrontier.CategoryTheory.Sites.Topos.LocalizationShriekExact
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatLocalization

/-!
# Extension by zero from a slice site, and Tor amplitude of restrictions

Let `(C, J)` be a site, `Λ` a commutative ring and `V` an object of `C`. Restriction of sheaves
of `Λ`-modules to the slice site `C/V`, `j^* = J.overPullback`, has a left adjoint, extension by
zero `j_! = (Over.forget V).sheafPullback`. On presheaves `j_!` is the left Kan extension along
`(Over.forget V).op`, whose value at `W` is the coproduct `⨁_{a : W ⟶ V} P(W →a V)`: the discrete
category of arrows `W ⟶ V` is final in the comma category computing it. Consequently

* `j_!` is exact (coproducts of modules are exact, sheafification is exact);
* `j_!` reflects vanishing (on presheaves the unit `P ⟶ j^*j_!P` is the inclusion of a summand);
* the projection formula `j_!(M|_V ⊗ G) ≅ M ⊗ j_!G` holds, naturally in the sheaf `M` on `C`
  (on presheaves, tensoring with `M(W)` commutes with the coproduct).

These give the restriction of Tor amplitude to a slice: if `K` has Tor amplitude in `S`, then for
a sheaf `G` on `C/V`, `j_!Hⁱ(K|_V ⊗^L G) ≅ Hⁱ(K ⊗^L j_!G)`, computed on a bounded above K-flat
representative of `K` by sheafified presheaves of free modules, vanishes for `i ∉ S`. Hence
finite Tor dimension implies locally finite Tor dimension (Stacks 08FZ).

## Main results

* `Stacks.ModuleSheaf.preservesFiniteLimits_sheafPullback_overForget`: `j_!` is left exact.
* `Stacks.ModuleSheaf.isZero_of_isZero_sheafPullback_overForget`: `j_!` reflects vanishing.
* `Stacks.ModuleSheaf.sheafPullbackOverForgetTensorIso`: the projection formula.
* `Stacks.ModuleSheaf.sheafPullbackOverForgetTensorProdIso`: the projection formula, naturally in
  both variables.
* `Stacks.ModuleSheaf.kFlat_overPullback`: restriction to a slice preserves K-flatness
  (Stacks 0E8K).
* `Stacks.ModuleSheaf.HasTorAmplitude.overPullback`: restriction to a slice preserves Tor
  amplitude in a set of degrees bounded above.
* `Stacks.ModuleSheaf.HasFiniteTorDimension.locallyHasFiniteTorDimension`: finite Tor dimension
  implies locally finite Tor dimension.

## References

* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 0E8I](https://stacks.math.columbia.edu/tag/0E8I)
* [Stacks Project, Tag 0E8K](https://stacks.math.columbia.edu/tag/0E8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe t t' w v u

namespace Stacks.ModuleSheaf

variable {C : Type u} [Category.{v} C] (V : C)

namespace SliceExtension

/-- The arrows `W ⟶ V`, as objects of the comma category computing the left Kan extension along
`(Over.forget V).op` at `W`: the arrow `a` is the object `(W →a V, 𝟙_W)`. -/
def overArrowsFunctor (W : Cᵒᵖ) :
    Discrete (W.unop ⟶ V) ⥤ CostructuredArrow (Over.forget V).op W :=
  Discrete.functor fun a => CostructuredArrow.mk (Y := op (Over.mk a)) (𝟙 W)

/-- The arrow `W ⟶ V` attached to an object `(Y, f : W ⟶ Y.left)` of the comma category: the
composite of `f` with the structure arrow of `Y`. -/
def CostructuredArrow.overArrow {W : Cᵒᵖ} (d : CostructuredArrow (Over.forget V).op W) :
    W.unop ⟶ V :=
  d.hom.unop ≫ d.left.unop.hom

/-- The unique morphism from an object of the comma category to the arrow object it lies over. -/
def toOverArrowsFunctor {W : Cᵒᵖ} (d : CostructuredArrow (Over.forget V).op W) :
    d ⟶ (overArrowsFunctor V W).obj ⟨CostructuredArrow.overArrow V d⟩ :=
  CostructuredArrow.homMk
    (Over.homMk d.hom.unop rfl : Over.mk (CostructuredArrow.overArrow V d) ⟶ d.left.unop).op
    ((Category.comp_id _).trans rfl)

/-- An object of the comma category maps only to the arrow object of its own arrow. -/
theorem overArrow_eq {W : Cᵒᵖ} {d : CostructuredArrow (Over.forget V).op W} {a : W.unop ⟶ V}
    (g : d ⟶ (overArrowsFunctor V W).obj ⟨a⟩) : a = CostructuredArrow.overArrow V d := by
  have h₁ : g.left.unop.left ≫ d.left.unop.hom = a := Over.w g.left.unop
  have h₂ : (Over.forget V).op.map g.left = d.hom :=
    (Category.comp_id _).symm.trans (CostructuredArrow.w g)
  rw [← h₁]
  change _ = d.hom.unop ≫ d.left.unop.hom
  rw [← h₂]
  rfl

/-- The morphism to the arrow object is unique. -/
theorem hom_eq_toOverArrowsFunctor {W : Cᵒᵖ} {d : CostructuredArrow (Over.forget V).op W}
    (g : d ⟶ (overArrowsFunctor V W).obj ⟨CostructuredArrow.overArrow V d⟩) :
    g = toOverArrowsFunctor V d := by
  refine CostructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj (Over.OverMorphism.ext ?_))
  exact congrArg Quiver.Hom.unop ((Category.comp_id _).symm.trans (CostructuredArrow.w g))

/-- **The discrete category of arrows `W ⟶ V` is final in the comma category** computing the left
Kan extension along `(Over.forget V).op` at `W`. -/
instance final_overArrowsFunctor (W : Cᵒᵖ) : (overArrowsFunctor V W).Final := by
  refine ⟨fun d => isConnected_of_isTerminal _
    (IsTerminal.ofUniqueHom (X := StructuredArrow.mk (toOverArrowsFunctor V d)) (fun X => ?_) ?_)⟩
  · obtain ⟨⟨⟩, ⟨a⟩, g⟩ := X
    obtain rfl := overArrow_eq V g
    exact StructuredArrow.homMk (𝟙 _) (by
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact hom_eq_toOverArrowsFunctor V g)
  · exact fun _ _ => StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _)

/-- An injection of a colimit cocone over a discrete category is a split monomorphism. -/
theorem isSplitMono_ι_of_isColimit {E : Type*} [Category* E] [HasZeroMorphisms E] {ι : Type*}
    {f : Discrete ι ⥤ E} {c : Cocone f} (hc : IsColimit c) (a : ι) :
    IsSplitMono (c.ι.app ⟨a⟩) := by
  classical
  refine ⟨⟨⟨hc.desc (Cocone.mk _ (Discrete.natTrans fun b =>
    if h : b.as = a then eqToHom (congrArg f.obj (Discrete.ext h)) else 0)), ?_⟩⟩⟩
  simp [hc.fac]

end SliceExtension

open SliceExtension

section Lan

variable (Λ : Type w) [CommRing Λ] [UnivLE.{max u v, w}]

/-- The arrows into `V` form a `w`-small type. -/
instance small_hom_overForget (W : C) : Small.{w} (W ⟶ V) :=
  small_map (Equiv.ulift.{u} (α := W ⟶ V)).symm

/-- Coproducts indexed by the arrows into `V` exist in `ModuleCat.{w} Λ`. -/
instance hasColimitsOfShape_discrete_hom_moduleCat (W : C) :
    HasColimitsOfShape (Discrete (W ⟶ V)) (ModuleCat.{w} Λ) :=
  hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{w} (W ⟶ V))).symm

/-- Coproducts indexed by the arrows into `V` are exact in `ModuleCat.{w} Λ` (Grothendieck's axiom
AB4). -/
instance hasExactColimitsOfShape_discrete_hom_moduleCat (W : C) :
    HasExactColimitsOfShape (Discrete (W ⟶ V)) (ModuleCat.{w} Λ) :=
  HasExactColimitsOfShape.of_domain_equivalence _
    (Discrete.equivalence (equivShrink.{w} (W ⟶ V))).symm

/-- Colimits indexed by the comma category computing the left Kan extension along
`(Over.forget V).op` are exact. -/
theorem hasExactColimitsOfShape_costructuredArrow_overForget (W : Cᵒᵖ) :
    HasExactColimitsOfShape (CostructuredArrow (Over.forget V).op W) (ModuleCat.{w} Λ) :=
  hasExactColimitsOfShape_of_final (ModuleCat.{w} Λ) (overArrowsFunctor V W)

/-- **Left Kan extension of presheaves of modules along `(Over.forget V).op` is left exact.** -/
theorem preservesFiniteLimits_lan_overForget :
    PreservesFiniteLimits ((Over.forget V).op.lan :
      ((Over V)ᵒᵖ ⥤ ModuleCat.{w} Λ) ⥤ (Cᵒᵖ ⥤ ModuleCat.{w} Λ)) := by
  apply preservesFiniteLimits_of_evaluation
  intro W
  have := hasExactColimitsOfShape_costructuredArrow_overForget V Λ W
  have : PreservesFiniteLimits
      (colim (J := CostructuredArrow (Over.forget V).op W) (C := ModuleCat.{w} Λ)) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  exact preservesFiniteLimits_of_natIso
    (Stacks.Sites.LocalizationShriek.lanCompEvaluationIsoColim (E := ModuleCat.{w} Λ)
      (Over.forget V).op W).symm

/-- The unit `P ⟶ j^*j_!P` of the left Kan extension along `(Over.forget V).op` is a
monomorphism. -/
theorem mono_lanUnit_overForget (P : (Over V)ᵒᵖ ⥤ ModuleCat.{w} Λ) :
    Mono ((Over.forget V).op.lanUnit.app P) := by
  suffices ∀ Y, Mono (((Over.forget V).op.lanUnit.app P).app Y) from NatTrans.mono_of_mono_app _
  intro Y
  have hc := (Functor.Final.isColimitWhiskerEquiv (overArrowsFunctor V ((Over.forget V).op.obj Y))
    _).symm (Stacks.InverseImageTensor.lanIsColimit (Over.forget V).op Λ P
      ((Over.forget V).op.obj Y))
  have := isSplitMono_ι_of_isColimit hc Y.unop.hom
  have h : ((Stacks.InverseImageTensor.lanCocone (Over.forget V).op Λ P
      ((Over.forget V).op.obj Y)).whisker (overArrowsFunctor V _)).ι.app ⟨Y.unop.hom⟩ =
      ((Over.forget V).op.lanUnit.app P).app Y := by
    change ((Over.forget V).op.lanUnit.app P).app Y ≫ ((Over.forget V).op.lan.obj P).map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  rw [← h]
  exact @IsSplitMono.mono _ _ _ _ _ this

end Lan

section Projection

variable (Λ : Type w) [CommRing Λ] [UnivLE.{max u v, w}] (P : (Over V)ᵒᵖ ⥤ ModuleCat.{w} Λ)

/-- The projection map `j_!(j^*M ⊗ P) ⟶ M ⊗ j_!P` of presheaves of modules, for `j_!` the left
Kan extension along `(Over.forget V).op`: the map the universal property attaches to
`j^*M ⊗ P ⟶ j^*M ⊗ j^*j_!P`. -/
noncomputable def lanProjMap (M : Cᵒᵖ ⥤ ModuleCat.{w} Λ) :
    (Over.forget V).op.lan.obj (((Over.forget V).op ⋙ M) ⊗ P) ⟶
      M ⊗ (Over.forget V).op.lan.obj P :=
  ((Over.forget V).op.lan.obj _).descOfIsLeftKanExtension ((Over.forget V).op.lanUnit.app _) _
    (((Over.forget V).op ⋙ M) ◁ (Over.forget V).op.lanUnit.app P)

/-- The defining property of the projection map. -/
theorem lanUnit_app_lanProjMap_app (M : Cᵒᵖ ⥤ ModuleCat.{w} Λ) (Y : (Over V)ᵒᵖ) :
    ((Over.forget V).op.lanUnit.app (((Over.forget V).op ⋙ M) ⊗ P)).app Y ≫
        (lanProjMap V Λ P M).app ((Over.forget V).op.obj Y) =
      M.obj ((Over.forget V).op.obj Y) ◁ ((Over.forget V).op.lanUnit.app P).app Y :=
  ((Over.forget V).op.lan.obj _).descOfIsLeftKanExtension_fac_app _ _ _ Y

/-- **The projection map is an isomorphism.** -/
instance isIso_lanProjMap (M : Cᵒᵖ ⥤ ModuleCat.{w} Λ) : IsIso (lanProjMap V Λ P M) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro W
  let F := overArrowsFunctor V W
  let X := ((Over.forget V).op ⋙ M) ⊗ P
  have hc := (Functor.Final.isColimitWhiskerEquiv F _).symm
    (Stacks.InverseImageTensor.lanIsColimit (Over.forget V).op Λ X W)
  have hd := (Functor.Final.isColimitWhiskerEquiv F _).symm
    (Stacks.InverseImageTensor.lanIsColimit (Over.forget V).op Λ P W)
  have he := isColimitOfPreserves (tensorLeft (M.obj W)) hd
  let δ : F ⋙ CostructuredArrow.proj (Over.forget V).op W ⋙ X ≅
      (F ⋙ CostructuredArrow.proj (Over.forget V).op W ⋙ P) ⋙ tensorLeft (M.obj W) :=
    Discrete.natIso fun _ => Iso.refl _
  have he' := (IsColimit.precomposeHomEquiv δ _).symm he
  have h : (lanProjMap V Λ P M).app W = (hc.coconePointUniqueUpToIso he').hom := by
    refine hc.hom_ext fun ⟨a⟩ => Eq.trans ?_
      (IsColimit.comp_coconePointUniqueUpToIso_hom hc he' ⟨a⟩).symm
    have := lanUnit_app_lanProjMap_app V Λ P M (op (Over.mk a))
    refine Eq.trans ?_ (this.trans ?_)
    · change (_ ≫ ((Over.forget V).op.lan.obj X).map (𝟙 W)) ≫ _ = _
      rw [CategoryTheory.Functor.map_id]
      exact congrArg (· ≫ (lanProjMap V Λ P M).app W) (Category.comp_id _)
    · change _ = 𝟙 _ ≫ M.obj W ◁ (_ ≫ ((Over.forget V).op.lan.obj P).map (𝟙 W))
      rw [CategoryTheory.Functor.map_id]
      exact (Category.id_comp _).symm.trans
        (congrArg (fun g => 𝟙 _ ≫ M.obj W ◁ g) (Category.comp_id _).symm)
  rw [h]
  exact Iso.isIso_hom _

/-- The projection map is natural in `M`. -/
theorem lanProjMap_naturality {M M' : Cᵒᵖ ⥤ ModuleCat.{w} Λ} (f : M ⟶ M') :
    (Over.forget V).op.lan.map (Functor.whiskerLeft (Over.forget V).op f ▷ P) ≫
        lanProjMap V Λ P M' = lanProjMap V Λ P M ≫ (f ▷ (Over.forget V).op.lan.obj P) := by
  apply ((Over.forget V).op.lan.obj _).hom_ext_of_isLeftKanExtension
    ((Over.forget V).op.lanUnit.app _)
  ext Y
  have hu := NatTrans.congr_app ((Over.forget V).op.lanUnit.naturality
    (Functor.whiskerLeft (Over.forget V).op f ▷ P)) Y
  simp only [Functor.id_obj, Functor.comp_obj, Functor.whiskeringLeft_obj_obj, Functor.id_map,
    NatTrans.comp_app, Functor.comp_map, Functor.whiskeringLeft_obj_map,
    Functor.whiskerLeft_app] at hu
  simp only [Functor.comp_obj, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [reassoc_of% hu.symm, lanUnit_app_lanProjMap_app,
    reassoc_of% (lanUnit_app_lanProjMap_app V Λ P M Y)]
  simp [whisker_exchange]

/-- **The projection formula for extension from a slice, on presheaves**: naturally in the
presheaf `M` on `C`, `j_!(j^*M ⊗ P) ≅ M ⊗ j_!P`. -/
noncomputable def lanProjIso :
    (Functor.whiskeringLeft _ _ (ModuleCat.{w} Λ)).obj (Over.forget V).op ⋙ tensorRight P ⋙
        (Over.forget V).op.lan ≅ tensorRight ((Over.forget V).op.lan.obj P) :=
  NatIso.ofComponents (fun M => asIso (lanProjMap V Λ P M)) (fun f => lanProjMap_naturality V Λ P f)

variable {V Λ P} in
/-- The projection map is natural in the presheaf on the slice. -/
theorem lanProjMap_naturality_right (M : Cᵒᵖ ⥤ ModuleCat.{w} Λ)
    {P' : (Over V)ᵒᵖ ⥤ ModuleCat.{w} Λ} (g : P ⟶ P') :
    (Over.forget V).op.lan.map (((Over.forget V).op ⋙ M) ◁ g) ≫ lanProjMap V Λ P' M =
      lanProjMap V Λ P M ≫ (M ◁ (Over.forget V).op.lan.map g) := by
  apply ((Over.forget V).op.lan.obj _).hom_ext_of_isLeftKanExtension
    ((Over.forget V).op.lanUnit.app _)
  refine NatTrans.ext (funext fun Y => ?_)
  have hu := NatTrans.congr_app ((Over.forget V).op.lanUnit.naturality
    (((Over.forget V).op ⋙ M) ◁ g)) Y
  have hg := NatTrans.congr_app ((Over.forget V).op.lanUnit.naturality g) Y
  simp only [Functor.id_obj, Functor.comp_obj, Functor.whiskeringLeft_obj_obj, Functor.id_map,
    NatTrans.comp_app, Functor.comp_map, Functor.whiskeringLeft_obj_map,
    Functor.whiskerLeft_app] at hu hg
  simp only [Functor.comp_obj, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [reassoc_of% hu.symm, lanUnit_app_lanProjMap_app,
    reassoc_of% (lanUnit_app_lanProjMap_app V Λ P M Y)]
  change (M.obj (op ((Over.forget V).obj Y.unop)) ◁ g.app Y) ≫ _ = _ ≫
    (M.obj (op ((Over.forget V).obj Y.unop)) ◁
      ((Over.forget V).op.lan.map g).app (op ((Over.forget V).obj Y.unop)))
  exact (MonoidalCategory.whiskerLeft_comp _ _ _).symm.trans
    ((congrArg (M.obj (op ((Over.forget V).obj Y.unop)) ◁ ·) hg).trans
      (MonoidalCategory.whiskerLeft_comp _ _ _))

/-- **The projection formula for extension from a slice, on presheaves, naturally in both
variables**: `j_!(j^*M ⊗ P) ≅ M ⊗ j_!P`. -/
noncomputable def lanProjProdIso :
    ((Functor.whiskeringLeft _ _ (ModuleCat.{w} Λ)).obj (Over.forget V).op).prod
          (𝟭 ((Over V)ᵒᵖ ⥤ ModuleCat.{w} Λ)) ⋙ tensor _ ⋙ (Over.forget V).op.lan ≅
      (𝟭 (Cᵒᵖ ⥤ ModuleCat.{w} Λ)).prod (Over.forget V).op.lan ⋙ tensor _ :=
  NatIso.ofComponents (fun X => asIso (lanProjMap V Λ X.2 X.1)) (fun {X Y} g => by
    obtain ⟨f, g⟩ := g
    change (Over.forget V).op.lan.map (Functor.whiskerLeft (Over.forget V).op f ⊗ₘ g) ≫
        lanProjMap V Λ Y.2 Y.1 = lanProjMap V Λ X.2 X.1 ≫ (f ⊗ₘ (Over.forget V).op.lan.map g)
    rw [tensorHom_def, tensorHom_def, Functor.map_comp, Category.assoc,
      lanProjMap_naturality_right, ← Category.assoc, lanProjMap_naturality, Category.assoc])

end Projection

section Sheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

variable (J : GrothendieckTopology C) (Λ : Type w) [CommRing Λ] [UnivLE.{max u v, w}]

/-- **Extension by zero from a slice is exact.** -/
instance preservesFiniteLimits_sheafPullback_overForget :
    PreservesFiniteLimits ((Over.forget V).sheafPullback (ModuleCat.{w} Λ) (J.over V) J) := by
  have := preservesFiniteLimits_lan_overForget V Λ
  let e : (Over.forget V).sheafPullback (ModuleCat.{w} Λ) (J.over V) J ≅
      sheafToPresheaf (J.over V) (ModuleCat.{w} Λ) ⋙ (Over.forget V).op.lan ⋙
        presheafToSheaf J (ModuleCat.{w} Λ) :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (asIso (sheafificationAdjunction (J.over V)
        (ModuleCat.{w} Λ)).counit).symm _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Stacks.InverseImageTensor.sheafifyCompPullbackIso
        (Over.forget V) Λ (J.over V) J)
  exact preservesFiniteLimits_of_natIso e.symm

/-- **Extension by zero from a slice is additive.** -/
instance additive_sheafPullback_overForget :
    ((Over.forget V).sheafPullback (ModuleCat.{w} Λ) (J.over V) J).Additive :=
  ((Over.forget V).sheafAdjunctionContinuous (ModuleCat.{w} Λ) (J.over V) J).left_adjoint_additive

/-- **Extension by zero from a slice reflects vanishing.** -/
theorem isZero_of_isZero_sheafPullback_overForget (M : Sheaf (J.over V) (ModuleCat.{w} Λ))
    (h : IsZero (((Over.forget V).sheafPullback (ModuleCat.{w} Λ) (J.over V) J).obj M)) :
    IsZero M := by
  let A := ModuleCat.{w} Λ
  let P := (sheafToPresheaf (J.over V) A).obj M
  let eM : (presheafToSheaf (J.over V) A).obj P ≅ M :=
    asIso ((sheafificationAdjunction (J.over V) A).counit.app M)
  have h₁ : IsZero ((presheafToSheaf J A).obj ((Over.forget V).op.lan.obj P)) :=
    h.of_iso (((Stacks.InverseImageTensor.sheafifyCompPullbackIso (Over.forget V) Λ (J.over V)
      J).app P).symm ≪≫ ((Over.forget V).sheafPullback A (J.over V) J).mapIso eM)
  have h₂ : IsZero ((presheafToSheaf (J.over V) A).obj
      ((Over.forget V).op ⋙ (Over.forget V).op.lan.obj P)) :=
    ((J.overPullback A V).map_isZero h₁).of_iso
      (((Over.forget V).pushforwardContinuousSheafificationCompatibility A (J.over V) J).app _)
  have := mono_lanUnit_overForget V Λ P
  exact (IsZero.of_mono ((presheafToSheaf (J.over V) A).map
    ((Over.forget V).op.lanUnit.app P)) h₂).of_iso eM.symm

/-- **The projection formula for extension from a slice**: for a presheaf `P` on `C/V`, naturally
in the sheaf `M` on `C`, `j_!(M|_V ⊗ P^#) ≅ M ⊗ j_!(P^#)`. Sheafification is monoidal and
commutes with `j_!` and with restriction, so this is the presheaf projection formula
`lanProjIso`. -/
noncomputable def sheafPullbackOverForgetTensorIso (P : (Over V)ᵒᵖ ⥤ ModuleCat.{w} Λ) :
    J.overPullback (ModuleCat.{w} Λ) V ⋙
        tensorRight ((presheafToSheaf (J.over V) (ModuleCat.{w} Λ)).obj P) ⋙
          (Over.forget V).sheafPullback (ModuleCat.{w} Λ) (J.over V) J ≅
      tensorRight (((Over.forget V).sheafPullback (ModuleCat.{w} Λ) (J.over V) J).obj
        ((presheafToSheaf (J.over V) (ModuleCat.{w} Λ)).obj P)) :=
  let A := ModuleCat.{w} Λ
  let jl := (Over.forget V).sheafPullback A (J.over V) J
  let sV := presheafToSheaf (J.over V) A
  let sC := presheafToSheaf J A
  let K := (Over.forget V).op
  Functor.isoWhiskerLeft (J.overPullback A V)
      (Functor.isoWhiskerRight (tensorRightSheafifyIso (J.over V) Λ P) jl) ≪≫
    (Iso.refl (sheafToPresheaf J A ⋙ (Functor.whiskeringLeft _ _ A).obj K ⋙ tensorRight P ⋙
      sV ⋙ jl)) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J A ⋙ (Functor.whiskeringLeft _ _ A).obj K ⋙
      tensorRight P) (Stacks.InverseImageTensor.sheafifyCompPullbackIso (Over.forget V) Λ
        (J.over V) J) ≪≫
    (Iso.refl (sheafToPresheaf J A ⋙ ((Functor.whiskeringLeft _ _ A).obj K ⋙ tensorRight P ⋙
      K.lan) ⋙ sC)) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J A)
      (Functor.isoWhiskerRight (lanProjIso V Λ P) sC) ≪≫
    (tensorRightSheafifyIso J Λ (K.lan.obj P)).symm ≪≫
    (curriedTensor (Sheaf J A)).flip.mapIso
      ((Stacks.InverseImageTensor.sheafifyCompPullbackIso (Over.forget V) Λ (J.over V)
        J).app P).symm

/-- **The projection formula for extension from a slice, naturally in both variables**: for a
sheaf `M` on `C` and a sheaf `G` on `C/V`, `j_!(M|_V ⊗ G) ≅ M ⊗ j_!G`. Both sides sheafify
the presheaf projection formula `lanProjProdIso`: sheafification is monoidal and commutes with
`j_!` and with restriction. -/
noncomputable def sheafPullbackOverForgetTensorProdIso :
    (J.overPullback (ModuleCat.{w} Λ) V).prod (𝟭 (Sheaf (J.over V) (ModuleCat.{w} Λ))) ⋙
        tensor _ ⋙ (Over.forget V).sheafPullback (ModuleCat.{w} Λ) (J.over V) J ≅
      (𝟭 (Sheaf J (ModuleCat.{w} Λ))).prod
          ((Over.forget V).sheafPullback (ModuleCat.{w} Λ) (J.over V) J) ⋙ tensor _ :=
  let A := ModuleCat.{w} Λ
  let jl := (Over.forget V).sheafPullback A (J.over V) J
  let ιC := sheafToPresheaf J A
  let ιV := sheafToPresheaf (J.over V) A
  let sC := presheafToSheaf J A
  let sV := presheafToSheaf (J.over V) A
  let R := (Functor.whiskeringLeft _ _ A).obj (Over.forget V).op
  let L := (Over.forget V).op.lan (H := A)
  let cC : ιC ⋙ sC ≅ 𝟭 _ := asIso (sheafificationAdjunction J A).counit
  let cV : ιV ⋙ sV ≅ 𝟭 _ := asIso (sheafificationAdjunction (J.over V) A).counit
  let σ : sV ⋙ jl ≅ L ⋙ sC :=
    Stacks.InverseImageTensor.sheafifyCompPullbackIso (Over.forget V) Λ (J.over V) J
  let a : J.overPullback A V ≅ ιC ⋙ R ⋙ sV :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft (J.overPullback A V) cV.symm
  let b : ιV ⋙ L ⋙ sC ≅ jl :=
    Functor.isoWhiskerLeft ιV σ.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight cV jl ≪≫ Functor.leftUnitor _
  let e₁ : (J.overPullback A V).prod (𝟭 _) ⋙ tensor _ ⋙ jl ≅
      (ιC ⋙ R ⋙ sV).prod (ιV ⋙ sV) ⋙ tensor _ ⋙ jl :=
    Functor.isoWhiskerRight (NatIso.prod a cV.symm) _
  let e₂ : (ιC ⋙ R ⋙ sV).prod (ιV ⋙ sV) ⋙ tensor _ ⋙ jl ≅
      (ιC.prod ιV ⋙ R.prod (𝟭 _)) ⋙ tensor _ ⋙ sV ⋙ jl :=
    Functor.isoWhiskerLeft (ιC.prod ιV ⋙ R.prod (𝟭 _))
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.Monoidal.μNatIso sV) jl ≪≫ Functor.associator _ _ _)
  let e₃ : (ιC.prod ιV ⋙ R.prod (𝟭 _)) ⋙ tensor _ ⋙ sV ⋙ jl ≅
      ιC.prod ιV ⋙ (R.prod (𝟭 _) ⋙ tensor _ ⋙ L) ⋙ sC :=
    Functor.isoWhiskerLeft (ιC.prod ιV ⋙ R.prod (𝟭 _) ⋙ tensor _) σ
  let e₄ : ιC.prod ιV ⋙ (R.prod (𝟭 _) ⋙ tensor _ ⋙ L) ⋙ sC ≅
      ιC.prod ιV ⋙ ((𝟭 _).prod L ⋙ tensor _) ⋙ sC :=
    Functor.isoWhiskerLeft (ιC.prod ιV)
      (Functor.isoWhiskerRight (lanProjProdIso V Λ) sC)
  let e₅ : ιC.prod ιV ⋙ ((𝟭 _).prod L ⋙ tensor _) ⋙ sC ≅
      (ιC ⋙ sC).prod (ιV ⋙ L ⋙ sC) ⋙ tensor _ :=
    Functor.isoWhiskerLeft (ιC.prod ιV ⋙ (𝟭 _).prod L) (Functor.Monoidal.μNatIso sC).symm
  let e₆ : (ιC ⋙ sC).prod (ιV ⋙ L ⋙ sC) ⋙ tensor _ ≅ (𝟭 _).prod jl ⋙ tensor _ :=
    Functor.isoWhiskerRight (NatIso.prod cC b) _
  e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅ ≪≫ e₆

/-- The projection formula with the factors swapped: for a sheaf `G` on `C/V` and a sheaf `M` on
`C`, `j_!(G ⊗ M|_V) ≅ j_!G ⊗ M`. -/
noncomputable def sheafPullbackOverForgetTensorSwapIso (G : Sheaf (J.over V) (ModuleCat.{w} Λ))
    (M : Sheaf J (ModuleCat.{w} Λ)) :
    ((Over.forget V).sheafPullback (ModuleCat.{w} Λ) (J.over V) J).obj
        (G ⊗ (J.overPullback (ModuleCat.{w} Λ) V).obj M) ≅
      ((Over.forget V).sheafPullback (ModuleCat.{w} Λ) (J.over V) J).obj G ⊗ M :=
  ((Over.forget V).sheafPullback (ModuleCat.{w} Λ) (J.over V) J).mapIso
      (β_ G ((J.overPullback (ModuleCat.{w} Λ) V).obj M)) ≪≫
    (sheafPullbackOverForgetTensorProdIso V J Λ).app (M, G) ≪≫ β_ M _

/-- The swapped projection formula is natural in both variables at once. -/
private theorem sheafPullbackOverForgetTensorSwapIso_hom_naturality
    {G G' : Sheaf (J.over V) (ModuleCat.{w} Λ)} (f : G ⟶ G') {M M' : Sheaf J (ModuleCat.{w} Λ)}
    (g : M ⟶ M') :
    ((Over.forget V).sheafPullback (ModuleCat.{w} Λ) (J.over V) J).map
        (f ⊗ₘ (J.overPullback (ModuleCat.{w} Λ) V).map g) ≫
        (sheafPullbackOverForgetTensorSwapIso V J Λ G' M').hom =
      (sheafPullbackOverForgetTensorSwapIso V J Λ G M).hom ≫
        (((Over.forget V).sheafPullback (ModuleCat.{w} Λ) (J.over V) J).map f ⊗ₘ g) := by
  let jV := J.overPullback (ModuleCat.{w} Λ) V
  let jl := (Over.forget V).sheafPullback (ModuleCat.{w} Λ) (J.over V) J
  let π := sheafPullbackOverForgetTensorProdIso V J Λ
  have h : jl.map (jV.map g ⊗ₘ f) ≫ (π.app (M', G')).hom = (π.app (M, G)).hom ≫ (g ⊗ₘ jl.map f) :=
    π.hom.naturality ((g, f) : (M, G) ⟶ (M', G'))
  change jl.map (f ⊗ₘ jV.map g) ≫ jl.map (β_ G' (jV.obj M')).hom ≫ (π.app (M', G')).hom ≫
      (β_ M' (jl.obj G')).hom =
    (jl.map (β_ G (jV.obj M)).hom ≫ (π.app (M, G)).hom ≫ (β_ M (jl.obj G)).hom) ≫
      (jl.map f ⊗ₘ g)
  rw [← Functor.map_comp_assoc, BraidedCategory.braiding_naturality, Functor.map_comp,
    Category.assoc, reassoc_of% h, BraidedCategory.braiding_naturality]
  simp only [Category.assoc]
  rfl

/-- The swapped projection formula is natural in the sheaf on the slice. -/
theorem sheafPullbackOverForgetTensorSwapIso_hom_naturality_left
    {G G' : Sheaf (J.over V) (ModuleCat.{w} Λ)} (f : G ⟶ G') (M : Sheaf J (ModuleCat.{w} Λ)) :
    ((Over.forget V).sheafPullback (ModuleCat.{w} Λ) (J.over V) J).map
        (f ▷ (J.overPullback (ModuleCat.{w} Λ) V).obj M) ≫
        (sheafPullbackOverForgetTensorSwapIso V J Λ G' M).hom =
      (sheafPullbackOverForgetTensorSwapIso V J Λ G M).hom ≫
        ((Over.forget V).sheafPullback (ModuleCat.{w} Λ) (J.over V) J).map f ▷ M := by
  simpa using sheafPullbackOverForgetTensorSwapIso_hom_naturality V J Λ f (𝟙 M)

/-- The swapped projection formula is natural in the sheaf on `C`. -/
theorem sheafPullbackOverForgetTensorSwapIso_hom_naturality_right
    (G : Sheaf (J.over V) (ModuleCat.{w} Λ)) {M M' : Sheaf J (ModuleCat.{w} Λ)} (g : M ⟶ M') :
    ((Over.forget V).sheafPullback (ModuleCat.{w} Λ) (J.over V) J).map
        (G ◁ (J.overPullback (ModuleCat.{w} Λ) V).map g) ≫
        (sheafPullbackOverForgetTensorSwapIso V J Λ G M').hom =
      (sheafPullbackOverForgetTensorSwapIso V J Λ G M).hom ≫
        ((Over.forget V).sheafPullback (ModuleCat.{w} Λ) (J.over V) J).obj G ◁ g := by
  simpa using sheafPullbackOverForgetTensorSwapIso_hom_naturality V J Λ (𝟙 G) g

end Sheaf

section Tor

open CochainComplex.KFlatBifunctor

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
  Stacks.ModuleSheaf.derivedMonoidal CochainComplex.braidedCategory

variable {J : GrothendieckTopology C} {Λ : Type w} [CommRing Λ] [UnivLE.{max u v, w}]
  [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]
  [HasDerivedCategory.{t'} (Sheaf (J.over V) (ModuleCat.{w} Λ))]

/-- **Restriction to a slice preserves Tor amplitude.** If `K` has Tor amplitude in a set `S` of
degrees bounded above, then so has its restriction `K|_V` to the slice site `C/V`. -/
theorem HasTorAmplitude.overPullback {K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))}
    {S : Set ℤ} {b : ℤ} (hS : S ⊆ Set.Iic b) (h : HasTorAmplitude K S) :
    letI := preservesFiniteLimits_overPullback J Λ V
    letI := preservesFiniteColimits_overPullback J Λ V
    HasTorAmplitude ((J.overPullback (ModuleCat.{w} Λ) V).mapDerivedCategory.obj K) S := by
  let := preservesFiniteLimits_overPullback J Λ V
  let := preservesFiniteColimits_overPullback J Λ V
  intro G i hi
  let A := ModuleCat.{w} Λ
  let jV := J.overPullback (ModuleCat.{w} Λ) V
  let jl := (Over.forget V).sheafPullback (ModuleCat.{w} Λ) (J.over V) J
  have : K.IsLE b := (h.mono hS).isLE
  obtain ⟨P, hP, hPLE, ⟨eP⟩⟩ := exists_kFlat_isStrictlyLE_representative K b
  have hadj := (Over.forget V).sheafAdjunctionContinuous (ModuleCat.{w} Λ) (J.over V) J
  have : jl.IsLeftAdjoint := ⟨_, ⟨hadj⟩⟩
  let jP : CochainComplex (Sheaf (J.over V) A) ℤ :=
    (jV.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have : CochainComplex.IsStrictlyLE jP b := isStrictlyLE_mapHomologicalComplex jV P b
  have hjP := kFlat_of_isStrictlyLE jP b (fun n => sheafifiedFree_overPullback_obj (hP n))
  have hPk := kFlat_of_isStrictlyLE P b hP
  let G' := (presheafToSheaf (J.over V) A).obj G.obj
  let eG : G' ≅ G := asIso ((sheafificationAdjunction (J.over V) A).counit.app G)
  let T := (rowFunctor (curriedTensor _) jP).obj G'
  let π := sheafPullbackOverForgetTensorIso V J Λ G.obj
  let e₂ : (jl.mapHomologicalComplex (ComplexShape.up ℤ)).obj T ≅
      (rowFunctor (curriedTensor _) P).obj (jl.obj G') :=
    HomologicalComplex.Hom.isoOfComponents (fun p => π.app (P.X p))
      (fun p q _ => (π.hom.naturality (P.d p q)).symm)
  let e₁ : jV.mapDerivedCategory.obj K ⊗ (DerivedCategory.singleFunctor _ 0).obj G' ≅
      DerivedCategory.Q.obj T :=
    ((jV.mapDerivedCategory.mapIso eP.symm ≪≫ jV.mapDerivedCategoryFactors.app P) ⊗ᵢ
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app G') ≪≫
      (derivedTensorSingleIso (CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat _ hjP)).app G'
  let e₃ : DerivedCategory.Q.obj ((rowFunctor (curriedTensor _) P).obj (jl.obj G')) ≅
      K ⊗ (DerivedCategory.singleFunctor _ 0).obj (jl.obj G') :=
    ((derivedTensorSingleIso (CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat _ hPk)).app
      (jl.obj G')).symm ≪≫ (eP ⊗ᵢ ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm)
  have h₀ : IsZero (jl.obj ((DerivedCategory.homologyFunctor _ i).obj
      (jV.mapDerivedCategory.obj K ⊗ (DerivedCategory.singleFunctor _ 0).obj G'))) :=
    (h (jl.obj G') i hi).of_iso (jl.mapIso ((DerivedCategory.homologyFunctor _ i).mapIso e₁) ≪≫
      ((jl.mapDerivedCategoryHomologyIso i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso (jl.mapDerivedCategoryFactors.app T ≪≫
        DerivedCategory.Q.mapIso e₂ ≪≫ e₃))
  exact (isZero_of_isZero_sheafPullback_overForget V J Λ _ h₀).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso (Iso.refl _ ⊗ᵢ
      (DerivedCategory.singleFunctor _ 0).mapIso eG.symm))

omit [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]
  [HasDerivedCategory.{t'} (Sheaf (J.over V) (ModuleCat.{w} Λ))] in
/-- **Restriction to a slice preserves K-flatness** (Stacks 0E8K for sheaves of `Λ`-modules):
if `P` is a K-flat complex of sheaves of `Λ`-modules on `C`, then `P|_V` is K-flat on `C/V`. -/
theorem kFlat_overPullback {P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (hP : KFlat (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) P) :
    KFlat (curriedTensor (Sheaf (J.over V) (ModuleCat.{w} Λ)))
      (((J.overPullback (ModuleCat.{w} Λ) V).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  intro G hG n
  let A := ModuleCat.{w} Λ
  let jV := J.overPullback A V
  let jl := (Over.forget V).sheafPullback A (J.over V) J
  have hadj := (Over.forget V).sheafAdjunctionContinuous A (J.over V) J
  have : jl.IsLeftAdjoint := ⟨_, ⟨hadj⟩⟩
  let F : Sheaf (J.over V) A ⥤ Sheaf J A ⥤ Sheaf (J.over V) A :=
    curriedTensor _ ⋙ (Functor.whiskeringLeft _ _ _).obj jV
  have : jV.Additive := ⟨fun {_ _ _ _} => rfl⟩
  have : ∀ a : Sheaf (J.over V) A, (F.obj a).Additive := fun a =>
    inferInstanceAs (jV ⋙ tensorLeft a).Additive
  have : F.Additive := ⟨fun {_ _ f g} => by
    ext b : 2
    change ((curriedTensor _).map (f + g)).app (jV.obj b) =
      ((curriedTensor _).map f).app (jV.obj b) + ((curriedTensor _).map g).app (jV.obj b)
    rw [Functor.map_add]
    rfl⟩
  have e := Functor.mapBifunctorTotalIso F (curriedTensor _) jl (𝟭 _) jl
    (sheafPullbackOverForgetTensorSwapIso V J Λ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) (sheafPullbackOverForgetTensorSwapIso_hom_naturality_left V J Λ)
    (sheafPullbackOverForgetTensorSwapIso_hom_naturality_right V J Λ) G P
  have h₂ : ((jl.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (totalComplex F G P)).ExactAt n := (hP _ (hG.map jl) n).of_iso e.symm
  rw [HomologicalComplex.exactAt_iff, ShortComplex.exact_iff_isZero_homology] at h₂ ⊢
  exact isZero_of_isZero_sheafPullback_overForget V J Λ _
    (h₂.of_iso (ShortComplex.mapHomologyIso ((totalComplex F G P).sc n) jl).symm)

/-- **Finite Tor dimension restricts to a slice.** -/
theorem HasFiniteTorDimension.overPullback {K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))}
    (h : HasFiniteTorDimension K) :
    letI := preservesFiniteLimits_overPullback J Λ V
    letI := preservesFiniteColimits_overPullback J Λ V
    HasFiniteTorDimension ((J.overPullback (ModuleCat.{w} Λ) V).mapDerivedCategory.obj K) :=
  let ⟨a, b, h⟩ := h
  ⟨a, b, h.overPullback V Set.Icc_subset_Iic_self⟩

/-- **Finite Tor dimension implies locally finite Tor dimension** (Stacks 08FZ). -/
theorem HasFiniteTorDimension.locallyHasFiniteTorDimension
    [∀ V : C, HasDerivedCategory.{t'} (Sheaf (J.over V) (ModuleCat.{w} Λ))]
    {K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))} (h : HasFiniteTorDimension K) :
    LocallyHasFiniteTorDimension K := fun U =>
  ⟨⊤, by rw [Sieve.generate_top]; exact J.top_mem U, fun V _ _ => h.overPullback V⟩

end Tor

end Stacks.ModuleSheaf

end
