module

public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.GeneratingFamily

/-!
# The presheaf-level pullback of modules and its sheafification map

Let `f : Y ⟶ X` be a morphism of schemes and `F` an `𝒪_X`-module.
`AlgebraicGeometry.Scheme.Modules.pullback` is the sheafification of the pullback of *presheaves*
of modules along the same morphism of ringed sites, by
`CategoryTheory.SheafOfModules.pullbackIso`.  This file builds that presheaf-level pullback and
the canonical morphism from it to `f^*F`, and proves the morphism is a sheafification map, hence
locally bijective for the Zariski topology on `Y`.  The sections of `f^*F` are not computed by
any formula — `AlgebraicGeometry.Scheme.Modules.pullback` is a left adjoint — so this morphism is
the only route from a section of `f^*F` to something with a formula, and it is what the local
bijectivity assertions of Stacks Lemma 070S are chased through.

## Main definitions

* `AlgebraicGeometry.zariskiPullbackPresheaf`: the pullback of `F.val` as a presheaf of modules
  along the structure-sheaf comparison of `f`, i.e. the presheaf whose sheafification is `f^*F`.
* `AlgebraicGeometry.zariskiPullbackSheafifyIso`: the identification of that sheafification with
  `f^*F`, which is `CategoryTheory.SheafOfModules.pullbackIso` at `F`.
* `AlgebraicGeometry.zariskiPullbackToSheaf`: the canonical morphism from the presheaf-level
  pullback to `f^*F`.

## Main results

* `AlgebraicGeometry.W_zariskiPullbackToSheaf`: that morphism is a sheafification map, hence
  locally bijective for the Zariski topology on `Y`; the two instances
  `Presheaf.IsLocallySurjective` and `Presheaf.IsLocallyInjective` follow.
* `AlgebraicGeometry.zariskiPullbackToSheaf_unit` and
  `AlgebraicGeometry.zariskiPullbackToSheaf_unit_app`: it transposes to the unit of the
  *sheaf*-level pullback--pushforward adjunction.
* `AlgebraicGeometry.zariskiPullbackToSheaf_generator`: hence it carries a generator of the
  presheaf-level pullback to the pullback of the corresponding section of `F`.
* `AlgebraicGeometry.span_pullbackSection_mono`: the span of the pullbacks of the sections over
  an open of `X` grows as that open shrinks.
* `AlgebraicGeometry.exists_eq_map_of_zariskiPullbackToSheaf_app_eq`: **two sections of the
  presheaf-level pullback with the same image in `f^*F` agree on a smaller open around every
  point.**  No hypothesis on `F`.

## Implementation notes

The two adjointness instances that the Mathlib definitions ask for are supplied by hand.
`CategoryTheory.PresheafOfModules.pullback` and `CategoryTheory.SheafOfModules.pullbackIso` take
`(pushforward φ).IsRightAdjoint` as an instance argument, and instance search does not reach
through `CategoryTheory.Functor.sheafPushforwardContinuous` to the shape Mathlib's own instance
is stated at; `AlgebraicGeometry.isRightAdjoint_presheafPushforward_ringCatSheafHom` and
`AlgebraicGeometry.isRightAdjoint_sheafPushforward_ringCatSheafHom` state it at the shape that is
needed.  Both classes are propositions, so the instances agree with whatever Mathlib used in
elaborating `AlgebraicGeometry.Scheme.Modules.pullback`.

Every equation below is an `Eq.trans` chain rather than a `rewrite` sequence.  The two spellings
`Y.ringCatSheaf` of `TopCat.Sheaf RingCat ↥Y` and of
`CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Y) RingCat` are definitionally equal and not
syntactically so, and a motive mentioning one of them is rejected at `implicit` transparency.

## References

* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **The global functions of an open subscheme, read on the ambient scheme.**  Restricting a
global function of `X` to `V` and then transporting along
`AlgebraicGeometry.Scheme.Opens.topIso` is the action of the open immersion of `V` on global
functions.  So the ring map along which restriction along the open immersion is semilinear is
the one along which `AlgebraicGeometry.Scheme.Opens.topIso` extends scalars. -/
public theorem ι_appTop_eq_topIso_inv {X : Scheme.{u}} (V : X.Opens) :
    V.ι.appTop =
      X.presheaf.map (homOfLE (le_top (a := V))).op ≫ (Scheme.Opens.topIso V).inv := by
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
  exact (congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _)

/-- **Pushforward of presheaves of modules along a morphism of schemes is a right adjoint**, at
the spelling `CategoryTheory.PresheafOfModules.pullback` asks for.  Mathlib proves this for an
arbitrary morphism of presheaves of rings over small sites, but instance search does not unfold
`CategoryTheory.Functor.sheafPushforwardContinuous` to recognise the shape. -/
public instance isRightAdjoint_presheafPushforward_ringCatSheafHom {X Y : Scheme.{u}}
    (f : Y ⟶ X) : (PresheafOfModules.pushforward.{u} f.toRingCatSheafHom.hom).IsRightAdjoint :=
  PresheafOfModules.instIsRightAdjointPushforward _

/-- **Pushforward of sheaves of modules along a morphism of schemes is a right adjoint**, at the
spelling `CategoryTheory.SheafOfModules.pullbackIso` asks for. -/
public instance isRightAdjoint_sheafPushforward_ringCatSheafHom {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)

/-- The pullback of `F`, as a presheaf of modules, along the structure-sheaf comparison of a
morphism of schemes.  Its sheafification is `f^*F`, by
`AlgebraicGeometry.zariskiPullbackSheafifyIso`. -/
public noncomputable abbrev zariskiPullbackPresheaf : PresheafOfModules.{u} Y.ringCatSheaf.obj :=
  (PresheafOfModules.pullback.{u} f.toRingCatSheafHom.hom).obj F.val

/-- **The pullback of modules is the sheafification of the pullback of presheaves of modules.**
`CategoryTheory.SheafOfModules.pullbackIso` at `F`, read as an isomorphism out of the
sheafification. -/
public noncomputable def zariskiPullbackSheafifyIso :
    (PresheafOfModules.sheafification.{u} (𝟙 Y.ringCatSheaf.obj)).obj
        (zariskiPullbackPresheaf f F) ≅
      (Scheme.Modules.pullback f).obj F :=
  ((SheafOfModules.pullbackIso.{u} f.toRingCatSheafHom).app F).symm

/-- **The canonical morphism from the presheaf-level pullback to `f^*F`**: the sheafification map
followed by `AlgebraicGeometry.zariskiPullbackSheafifyIso`.  It is locally bijective for the
Zariski topology on `Y` (`AlgebraicGeometry.W_zariskiPullbackToSheaf`) and it carries the image of
a section of `F` under the unit of the presheaf-level adjunction to its image under the unit of
the sheaf-level one (`AlgebraicGeometry.zariskiPullbackToSheaf_unit`). -/
public noncomputable def zariskiPullbackToSheaf :
    zariskiPullbackPresheaf f F ⟶ ((Scheme.Modules.pullback f).obj F).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
      (zariskiPullbackPresheaf f F) ≫
    (SheafOfModules.forget Y.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map
        (zariskiPullbackSheafifyIso f F).hom

/-- `AlgebraicGeometry.zariskiPullbackToSheaf` on underlying presheaves of abelian groups is the
sheafification map followed by an isomorphism. -/
public theorem toPresheaf_zariskiPullbackToSheaf :
    (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map (zariskiPullbackToSheaf f F) =
      (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 Y.ringCatSheaf.obj)).unit.app (zariskiPullbackPresheaf f F)) ≫
        (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
          ((SheafOfModules.forget Y.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map
              (zariskiPullbackSheafifyIso f F).hom) :=
  (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map_comp _ _

/-- **`AlgebraicGeometry.zariskiPullbackToSheaf` is locally bijective for the Zariski topology on
`Y`.** -/
public theorem W_zariskiPullbackToSheaf : (Opens.grothendieckTopology ↥Y).W
    ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map (zariskiPullbackToSheaf f F)) := by
  have h1 : (Opens.grothendieckTopology ↥Y).W
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 Y.ringCatSheaf.obj)).unit.app (zariskiPullbackPresheaf f F))) :=
    (Opens.grothendieckTopology ↥Y).W_toSheafify _
  have h2 : (Opens.grothendieckTopology ↥Y).W
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
        ((SheafOfModules.forget Y.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map
            (zariskiPullbackSheafifyIso f F).hom)) :=
    have h3 : IsIso (zariskiPullbackSheafifyIso f F).hom :=
      (zariskiPullbackSheafifyIso f F).isIso_hom
    have h4 : IsIso ((SheafOfModules.forget Y.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map
          (zariskiPullbackSheafifyIso f F).hom) := Functor.map_isIso _ _
    MorphismProperty.of_isIso _ _
  rw [toPresheaf_zariskiPullbackToSheaf]
  exact (Opens.grothendieckTopology ↥Y).W.comp_mem _ _ h1 h2

/-- The underlying morphism of presheaves of `AlgebraicGeometry.zariskiPullbackToSheaf` is locally
surjective for the Zariski topology on `Y`. -/
public instance isLocallySurjective_zariskiPullbackToSheaf :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥Y)
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map (zariskiPullbackToSheaf f F)) :=
  (W_zariskiPullbackToSheaf f F).isLocallySurjective

/-- The underlying morphism of presheaves of `AlgebraicGeometry.zariskiPullbackToSheaf` is locally
injective for the Zariski topology on `Y`. -/
public instance isLocallyInjective_zariskiPullbackToSheaf :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥Y)
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map (zariskiPullbackToSheaf f F)) :=
  (W_zariskiPullbackToSheaf f F).isLocallyInjective

/-- **`AlgebraicGeometry.zariskiPullbackToSheaf` transposes to the sheaf-level unit.**  Composing
the unit of `CategoryTheory.PresheafOfModules.pullbackPushforwardAdjunction` with the pushforward
of the comparison gives the unit of
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`. -/
public theorem zariskiPullbackToSheaf_unit :
    (PresheafOfModules.pullbackPushforwardAdjunction.{u}
          f.toRingCatSheafHom.hom).unit.app F.val ≫
        (PresheafOfModules.pushforward.{u} f.toRingCatSheafHom.hom).map
          (zariskiPullbackToSheaf f F) =
      (SheafOfModules.forget X.ringCatSheaf).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (SheafOfModules.pullbackPushforwardAdjunction.{u} f.toRingCatSheafHom)
    (SheafOfModules.PullbackConstruction.adjunction.{u} f.toRingCatSheafHom) F
  have e1 : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).map
          (((SheafOfModules.pullbackPushforwardAdjunction.{u}
            f.toRingCatSheafHom).leftAdjointUniq
              (SheafOfModules.PullbackConstruction.adjunction.{u}
                f.toRingCatSheafHom)).hom.app F) ≫
        (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).map
          (zariskiPullbackSheafifyIso f F).hom = 𝟙 _ :=
    ((SheafOfModules.pushforward.{u} f.toRingCatSheafHom).map_comp _ _).symm.trans
      ((congrArg ((SheafOfModules.pushforward.{u} f.toRingCatSheafHom).map)
          (((SheafOfModules.pullbackIso.{u} f.toRingCatSheafHom).app F).hom_inv_id)).trans
        ((SheafOfModules.pushforward.{u} f.toRingCatSheafHom).map_id _))
  have h' : (SheafOfModules.PullbackConstruction.adjunction.{u}
          f.toRingCatSheafHom).unit.app F ≫
        (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).map
          (zariskiPullbackSheafifyIso f F).hom =
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
        f.toRingCatSheafHom).unit.app F :=
    (congrArg (fun k => k ≫ (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).map
        (zariskiPullbackSheafifyIso f F).hom) h).symm.trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => (SheafOfModules.pullbackPushforwardAdjunction.{u}
            f.toRingCatSheafHom).unit.app F ≫ k) e1).trans (Category.comp_id _)))
  have hforget : (SheafOfModules.forget X.ringCatSheaf).map
        ((SheafOfModules.PullbackConstruction.adjunction.{u}
          f.toRingCatSheafHom).unit.app F) =
      (PresheafOfModules.pullbackPushforwardAdjunction.{u}
          f.toRingCatSheafHom.hom).unit.app F.val ≫
        (PresheafOfModules.pushforward.{u} f.toRingCatSheafHom.hom).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 Y.ringCatSheaf.obj)).unit.app (zariskiPullbackPresheaf f F)) := rfl
  have hG : (SheafOfModules.forget X.ringCatSheaf).map
        ((SheafOfModules.pushforward.{u} f.toRingCatSheafHom).map
          (zariskiPullbackSheafifyIso f F).hom) =
      (PresheafOfModules.pushforward.{u} f.toRingCatSheafHom.hom).map
        ((SheafOfModules.forget Y.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map
            (zariskiPullbackSheafifyIso f F).hom) := rfl
  refine Eq.trans ?_ (congrArg
    (fun k => (SheafOfModules.forget X.ringCatSheaf).map k) h')
  refine Eq.trans ?_ ((SheafOfModules.forget X.ringCatSheaf).map_comp
    ((SheafOfModules.PullbackConstruction.adjunction.{u} f.toRingCatSheafHom).unit.app F)
    ((SheafOfModules.pushforward.{u} f.toRingCatSheafHom).map
      (zariskiPullbackSheafifyIso f F).hom)).symm
  refine Eq.trans ?_ (congrArg (fun k => k ≫ (SheafOfModules.forget X.ringCatSheaf).map
    ((SheafOfModules.pushforward.{u} f.toRingCatSheafHom).map
      (zariskiPullbackSheafifyIso f F).hom)) hforget.symm)
  refine Eq.trans ?_ (congrArg (fun k =>
    ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
        f.toRingCatSheafHom.hom).unit.app F.val ≫
      (PresheafOfModules.pushforward.{u} f.toRingCatSheafHom.hom).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 Y.ringCatSheaf.obj)).unit.app (zariskiPullbackPresheaf f F))) ≫ k) hG.symm)
  refine Eq.trans ?_ (Category.assoc
    ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
      f.toRingCatSheafHom.hom).unit.app F.val)
    ((PresheafOfModules.pushforward.{u} f.toRingCatSheafHom.hom).map
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 Y.ringCatSheaf.obj)).unit.app (zariskiPullbackPresheaf f F)))
    ((PresheafOfModules.pushforward.{u} f.toRingCatSheafHom.hom).map
      ((SheafOfModules.forget Y.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map
          (zariskiPullbackSheafifyIso f F).hom))).symm
  exact congrArg (fun k => (PresheafOfModules.pullbackPushforwardAdjunction.{u}
      f.toRingCatSheafHom.hom).unit.app F.val ≫ k)
    ((PresheafOfModules.pushforward.{u} f.toRingCatSheafHom.hom).map_comp
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 Y.ringCatSheaf.obj)).unit.app (zariskiPullbackPresheaf f F))
      ((SheafOfModules.forget Y.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map
          (zariskiPullbackSheafifyIso f F).hom))

/-- `AlgebraicGeometry.zariskiPullbackToSheaf_unit` on a single section. -/
public theorem zariskiPullbackToSheaf_unit_app (U : X.Opens) (m : F.val.obj (op U)) :
    (zariskiPullbackToSheaf f F).app (op (f ⁻¹ᵁ U))
        (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
          f.toRingCatSheafHom.hom).unit.app F.val).app (op U) m) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op U) m := by
  have h2 := congrArg (fun k : F.val ⟶ (PresheafOfModules.pushforward.{u}
      f.toRingCatSheafHom.hom).obj (((Scheme.Modules.pullback f).obj F).val) =>
    PresheafOfModules.Hom.app k (op U)) (zariskiPullbackToSheaf_unit f F)
  rw [PresheafOfModules.comp_app] at h2
  exact ConcreteCategory.congr_hom h2 m

/-- **The comparison on a generator.**  `AlgebraicGeometry.zariskiPullbackToSheaf` carries the
restriction to `V` of the image of a section `m` of `F` over `U` under the unit of the
presheaf-level adjunction to the pullback of `m` to `V`. -/
public theorem zariskiPullbackToSheaf_generator (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (m : F.val.obj (op U)) :
    (zariskiPullbackToSheaf f F).app (op V) ((zariskiPullbackPresheaf f F).map (homOfLE h).op
        (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
          f.toRingCatSheafHom.hom).unit.app F.val).app (op U) m)) =
      pullbackSectionHom f F U V h m := by
  refine Eq.trans
    (PresheafOfModules.naturality_apply (zariskiPullbackToSheaf f F) (homOfLE h).op _) ?_
  exact congrArg (fun z => ((Scheme.Modules.pullback f).obj F).val.map (homOfLE h).op z)
    (zariskiPullbackToSheaf_unit_app f F U m)

/-- **The span of the pulled-back sections grows as the open of `X` shrinks.**  For `U' ≤ U` and
`W ≤ f⁻¹U'`, the `Γ(Y, W)`-span of the pullbacks to `W` of the sections of `F` over `U` is
contained in that of the sections over `U'`. -/
public theorem span_pullbackSection_mono (U U' : X.Opens) (hUU' : U' ≤ U) (W : Y.Opens)
    (h : W ≤ f ⁻¹ᵁ U') (h' : W ≤ f ⁻¹ᵁ U) :
    Submodule.span Γ(Y, W)
        (Set.range fun a : Γ(F, U) => pullbackSectionHom f F U W h' a) ≤
      Submodule.span Γ(Y, W)
        (Set.range fun a : Γ(F, U') => pullbackSectionHom f F U' W h a) := by
  refine Submodule.span_le.2 ?_
  rintro z ⟨a, rfl⟩
  exact Submodule.subset_span
    ⟨F.val.map (homOfLE hUU').op a, pullbackSectionHom_map f F U U' hUU' W h h' a⟩


/-- **Two sections of the presheaf-level pullback with the same image in `f^*F` agree locally.**
If sections `t` and `t'` over `V` have the same image under
`AlgebraicGeometry.zariskiPullbackToSheaf`, then every point `y ∈ V` has an open neighbourhood
`W ≤ V` on which the restrictions of `t` and `t'` agree. -/
public theorem exists_eq_map_of_zariskiPullbackToSheaf_app_eq (V : Y.Opens)
    (t t' : (zariskiPullbackPresheaf f F).obj (op V))
    (heq : (zariskiPullbackToSheaf f F).app (op V) t =
      (zariskiPullbackToSheaf f F).app (op V) t')
    (y : ↥Y) (hy : y ∈ V) :
    ∃ (W : Y.Opens) (hWV : W ≤ V), y ∈ W ∧
      (zariskiPullbackPresheaf f F).map (homOfLE hWV).op t =
        (zariskiPullbackPresheaf f F).map (homOfLE hWV).op t' := by
  have hinj : Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥Y)
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map (zariskiPullbackToSheaf f F)) :=
    isLocallyInjective_zariskiPullbackToSheaf f F
  obtain ⟨W, g, hW, hyW⟩ :=
    (Opens.mem_grothendieckTopology ↥Y).1
      (hinj.equalizerSieve_mem (X := op V) t t' heq) y hy
  refine ⟨W, leOfHom g, hyW, ?_⟩
  refine Eq.trans (congrArg (fun k : W ⟶ V =>
    (zariskiPullbackPresheaf f F).map k.op t) (Subsingleton.elim _ g)) ?_
  exact hW.trans (congrArg (fun k : W ⟶ V =>
    (zariskiPullbackPresheaf f F).map k.op t') (Subsingleton.elim g _))


end AlgebraicGeometry

end
