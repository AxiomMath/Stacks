module

public import StacksFrontier.Deformation.RingedSpaceThickening.DeformationDiagram
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionClassesExtFibre
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionThickening
public import StacksFrontier.Deformation.RingedSpaceThickening.IdealMapSections

/-!
# The compatibility equation of a solution of (08U7) is the left square of the diagram

A solution of the problem (08U7) of **Stacks 08U7**, in the form
`AlgebraicGeometry.RingedSpaceThickening.DeformationSolution`, is a first order thickening
`i : X ⟶ X'` with `f' : X' ⟶ S'` over `f ≫ t`, an identification `κ` of `Ker(i^♯)` with `i_*𝒢`,
and the compatibility equation: the canonical map `i_*f^*t^*Ker(t^♯) ⟶ Ker(i^♯)` of
**Stacks 08KZ** is the prescribed `c'` under `κ`. Reading `𝒪_{X'}` on `X` as the extension
`solutionExtension` of `f⁻¹𝒪_{S'}`-algebras, this file shows that the compatibility equation is
exactly the commutativity of the left square of (08U7) for the `f`-map `prescribedFMap c'`,
i.e. the existence of an `S'`-morphism compatible with `f` and `c` in the sense of
**Stacks 0GQ1** (`firstOrderIdealMap_comp_eq_iff_leftSquare`). This is the source's "of course
this is the same thing as saying `𝒪_{X'}` is a solution of (08U7)" in the proof of
**Stacks 0GQ3**.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.prescribedFMap`: the `f`-map `𝒥 ⟶ f_*𝒢` of a
  prescribed map `c' : f^*t^*Ker(t^♯) ⟶ 𝒢`.
* `AlgebraicGeometry.RingedSpaceThickening.solutionExtension`: the extension of
  `f⁻¹𝒪_{S'}`-algebras underlying a thickening over `S'`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.firstOrderIdealMap_comp_eq_iff`: the compatibility
  equation, transposed along `f'^* ⊣ f'_*`.
* `AlgebraicGeometry.RingedSpaceThickening.homEquiv_firstOrderSurjection_comp`: the transpose of
  the reduction map of **Stacks 08KZ** followed by `c'`.
* `AlgebraicGeometry.RingedSpaceThickening.firstOrderIdealMap_comp_eq_iff_leftSquare`, and
  `DeformationSolution.toExtensionSolution`: a `DeformationSolution` is an `ExtensionSolution`.

## References

* [Stacks Project, Tag 0GQ3](https://stacks.math.columbia.edu/tag/0GQ3)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
* [Stacks Project, Tag 0GQ1](https://stacks.math.columbia.edu/tag/0GQ1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-- `eqToHom` between pushforwards along equal morphisms, on sections. -/
theorem eqToHom_modulePushforward_app {X Y : RingedSpace.{u, u}} {k₁ k₂ : X ⟶ Y} (hk : k₁ = k₂)
    (M : SheafOfModules.{u} (structureSheafRing X)) (V : Opens Y.carrier)
    (m : ((modulePushforward k₁).obj M).val.obj (op V)) :
    (eqToHom (congrArg (fun m : X ⟶ Y => (modulePushforward m).obj M) hk)).val.app (op V) m =
      M.val.map (eqToHom (by subst hk; rfl)).op m := by
  subst hk
  exact (ConcreteCategory.congr_hom (M.val.map_id _) m).symm

/-- The inverse of the transpose along `t⁻¹ ⊣ t_*`, evaluated on the image of the unit. -/
theorem homEquiv_symm_app_inverseImageUnit {S S' : RingedSpace.{u, u}} (t : S ⟶ S')
    {F : TopCat.Sheaf CommRingCat.{u} S.carrier}
    (β : S'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).obj F)
    (V : Opens S'.carrier) (z : S'.presheaf.obj (op V)) :
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} t.hom.base).homEquiv _ _).symm
      β).hom.app (op ((Opens.map t.hom.base).obj V)) ((inverseImageUnit t).hom.app (op V) z) =
        β.hom.app (op V) z := by
  have h := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} t.hom.base).homEquiv_unit
    _ _ (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} t.hom.base).homEquiv
      _ _).symm β)).symm.trans (Equiv.apply_symm_apply _ β)
  exact ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op V)) h) z

/-- **Transposing along a composite.** For `f : X ⟶ Y`, `g : Y ⟶ Z`, the transpose along
`(f ≫ g)^* ⊣ (f ≫ g)_*` of `(f ≫ g)^*A ≅ f^*g^*A ⟶ M` is the transpose along `g` of the transpose
along `f`. -/
theorem homEquiv_comp_modulePullbackCompUniq {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : SheafOfModules.{u} (structureSheafRing Z)) (M : SheafOfModules.{u} (structureSheafRing X))
    (φ : (modulePullback f).obj ((modulePullback g).obj A) ⟶ M) :
    homEquiv (f ≫ g) M A ((modulePullbackCompUniq f g).hom.app A ≫ φ) =
      homEquiv g ((modulePushforward f).obj M) A (homEquiv f M _ φ) := by
  let _hf : (SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  let _hg : (SheafOfModules.pushforward (structureSheafHom g)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint g
  let _hfg : (SheafOfModules.pushforward (structureSheafHom (f ≫ g))).IsRightAdjoint :=
    modulePushforward_isRightAdjoint (f ≫ g)
  let adjf := modulePullbackPushforwardAdjunction f
  let adjg := modulePullbackPushforwardAdjunction g
  let adjfg := modulePullbackPushforwardAdjunction (f ≫ g)
  let adj' := (adjg.comp adjf).ofNatIsoRight (modulePushforwardCompSymm f g).symm
  have hu : adjfg.homEquiv _ _ ((modulePullbackCompUniq f g).hom.app A) = adj'.unit.app A :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app adjfg adj' A
  show adjfg.homEquiv _ _ ((modulePullbackCompUniq f g).hom.app A ≫ φ) =
    adjg.homEquiv _ _ (adjf.homEquiv _ _ φ)
  rw [adjfg.homEquiv_naturality_right, hu, ← adj'.homEquiv_unit,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  exact Category.comp_id _

/-- **The compatibility equation of Stacks 08U7, transposed.** For a morphism of first order
thickenings `D`, an identification `κ` of the ideal of `D.i` with `i_*𝒢` and a prescribed map
`c' : f^*t^*𝒥 ⟶ 𝒢`, the canonical map `i_*f^*𝒥 ⟶ Ker(i^♯)` of **Stacks 08KZ** is `c'` under `κ`
exactly when the transpose along `f'` of the reduction followed by `c'` and the inclusion of
`𝒢` is the restriction of `f'^♯` to `Ker(t^♯)`. -/
theorem firstOrderIdealMap_comp_eq_iff (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t)
    (G : SheafOfModules.{u} (structureSheafRing D.X))
    (κ : AlgebraicGeometry.SheafOfModules.idealSheaf D.i ≅ (modulePushforward D.i).obj G)
    (c' : (modulePullback D.f).obj ((modulePullback D.t).obj
      (AlgebraicGeometry.SheafOfModules.idealSheaf D.t)) ⟶ G) :
    (D.firstOrderIdealMap hi ht).1 ≫ κ.hom = (modulePushforward D.i).map c' ↔
      homEquiv D.f' _ _ (D.firstOrderSurjection hi ht ≫ (modulePushforward D.i).map c' ≫
          κ.inv ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.i))) =
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.t)) ≫
          SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.f') := by
  let ι := kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.i))
  let g := (D.firstOrderIdealMap hi ht).1
  let s := D.firstOrderSurjection hi ht
  have hamb : homEquiv D.f' _ _ D.ambientIdealMap =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.t)) ≫
        SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.f') :=
    homEquiv_map_comp_pullbackUnitToUnit D.f' _ _
  have hsg : s ≫ g ≫ ι = D.ambientIdealMap :=
    (Category.assoc s g ι).symm.trans ((congrArg (· ≫ ι) (D.firstOrderIdealMap hi ht).2.1).trans
      D.idealMap.2)
  refine Iff.trans ?_ ((homEquiv D.f' _ _).injective.eq_iff.symm.trans (Eq.congr_right hamb))
  constructor
  · intro h
    refine Eq.trans ?_ hsg
    refine congrArg (s ≫ ·) ?_
    rw [← h]
    exact (Category.assoc _ _ _).trans (congrArg (g ≫ ·) (κ.hom_inv_id_assoc ι))
  · intro h
    have h' : (s ≫ (modulePushforward D.i).map c' ≫ κ.inv) ≫ ι = (s ≫ g) ≫ ι := by
      refine ((Category.assoc _ _ _).trans ((congrArg (s ≫ ·) (Category.assoc _ _ _)).trans
        h)).trans ?_
      exact hsg.symm.trans (Category.assoc s g ι).symm
    have h3 := (D.firstOrderIdealMap hi ht).2.2 ((modulePushforward D.i).map c' ≫ κ.inv)
      ((Category.assoc _ _ _).symm.trans (((cancel_mono ι).1 h').trans
        (D.firstOrderIdealMap hi ht).2.1))
    rw [← h3, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The `f`-map `𝒥 ⟶ f_*𝒢` attached to a prescribed map `c' : f^*t^*Ker(t^♯) ⟶ 𝒢` of
**Stacks 08U7** in the form used by `DeformationSolution`. -/
def prescribedFMap {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} (ht : IsFirstOrderThickening t)
    (f : X ⟶ S) (G : SheafOfModules.{u} (structureSheafRing X))
    (c' : (modulePullback f).obj ((modulePullback t).obj
      (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G) :
    (show SheafOfModules.{u} (structureSheafRing S) from baseIdealModule ht) ⟶
      (modulePushforward f).obj G :=
  (baseIdealIsoPullback ht).hom ≫ homEquiv f G _ c'

/-- **The transpose of the reduction followed by `c'`.** For a morphism of first order
thickenings `D`, the transpose along `f'` of `(f')^*Ker(t^♯) ⟶ i_*f^*t^*Ker(t^♯) ⟶ i_*𝒢 ⟶ N` is
`Ker(t^♯) ≅ t_*𝒥 ⟶ t_*f_*𝒢 = f'_*i_*𝒢 ⟶ f'_*N`, the middle map being `t_*` of the `f`-map
`prescribedFMap`. -/
theorem homEquiv_firstOrderSurjection_comp (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t)
    (G : SheafOfModules.{u} (structureSheafRing D.X))
    (c' : (modulePullback D.f).obj ((modulePullback D.t).obj
      (AlgebraicGeometry.SheafOfModules.idealSheaf D.t)) ⟶ G)
    {N : SheafOfModules.{u} (structureSheafRing D.X')} (l : (modulePushforward D.i).obj G ⟶ N) :
    homEquiv D.f' _ _ (D.firstOrderSurjection hi ht ≫ (modulePushforward D.i).map c' ≫ l) =
      (baseIdealPushforwardIso ht).inv ≫ (modulePushforward D.t).map (prescribedFMap ht D.f G c') ≫
        (modulePushforwardComp D.f D.t).hom.app G ≫
        eqToHom (congrArg (fun k : D.X ⟶ D.S' => (modulePushforward k).obj G) D.comm.symm) ≫
        (modulePushforwardComp D.i D.f').inv.app G ≫ (modulePushforward D.f').map l := by
  have h1 : D.firstOrderSurjection hi ht ≫ (modulePushforward D.i).map c' =
      homEquiv D.i G _ (D.reducedPullbackComparison.hom ≫ c') := by
    rw [homEquiv, Adjunction.homEquiv_unit, Functor.map_comp]
    exact Category.assoc _ _ _
  have h2 : (modulePullbackCompUniq D.i D.f').hom.app D.idealJ ≫
      D.reducedPullbackComparison.hom ≫ c' =
      eqToHom (congrArg (fun k : D.X ⟶ D.S' => (modulePullback k).obj D.idealJ) D.comm) ≫
        (modulePullbackCompUniq D.f D.t).hom.app D.idealJ ≫ c' := by
    simp only [MorphismOfThickenings.reducedPullbackComparison, Iso.trans_hom, Iso.app_hom,
      Iso.symm_hom, eqToIso.hom, Category.assoc, Iso.hom_inv_id_app_assoc]
  have h3 : homEquiv D.f' ((modulePushforward D.i).obj G) D.idealJ
      (homEquiv D.i G _ (D.reducedPullbackComparison.hom ≫ c')) =
      homEquiv D.t _ D.idealJ (homEquiv D.f G _ c') ≫
        (modulePushforwardComp D.f D.t).hom.app G ≫
        eqToHom (congrArg (fun k : D.X ⟶ D.S' => (modulePushforward k).obj G) D.comm.symm) ≫
        (modulePushforwardComp D.i D.f').inv.app G := by
    rw [← homEquiv_comp_modulePullbackCompUniq, h2,
      show homEquiv (D.i ≫ D.f') G D.idealJ =
        (modulePullbackPushforwardAdjunction (D.i ≫ D.f')).homEquiv D.idealJ G from rfl,
      RingedSpaceModuleAdjunction.homEquiv_eqToHom_comp D.comm,
      show (modulePullbackPushforwardAdjunction (D.f ≫ D.t)).homEquiv D.idealJ G =
        homEquiv (D.f ≫ D.t) G D.idealJ from rfl,
      homEquiv_comp_modulePullbackCompUniq]
    rfl
  have h4 : (baseIdealPushforwardIso ht).inv ≫ (modulePushforward D.t).map
      (prescribedFMap ht D.f G c') = homEquiv D.t _ D.idealJ (homEquiv D.f G _ c') := by
    refine (congrArg ((baseIdealPushforwardIso ht).inv ≫ ·)
      ((modulePushforward D.t).map_comp (baseIdealIsoPullback ht).hom
        (homEquiv D.f G _ c'))).trans ?_
    refine (congrArg (fun φ => (baseIdealPushforwardIso ht).inv ≫ φ ≫
      (modulePushforward D.t).map (homEquiv D.f G _ c'))
        (modulePushforward_map_baseIdealIsoPullback_hom ht)).trans ?_
    refine (congrArg ((baseIdealPushforwardIso ht).inv ≫ ·) (Category.assoc _ _ _)).trans ?_
    refine ((baseIdealPushforwardIso ht).inv_hom_id_assoc _).trans ?_
    exact ((modulePullbackPushforwardAdjunction D.t).homEquiv_unit _ _ _).symm
  rw [← Category.assoc, homEquiv, Adjunction.homEquiv_naturality_right, ← homEquiv, h1, h3,
    ← reassoc_of% h4]
  simp only [modulePushforwardComp_hom_app, modulePushforwardComp_inv_app, Category.assoc]
  rfl

/-! ### The extension underlying a solution, and the compatibility with `c` -/

section Compat

variable {X S S' X' : RingedSpace.{u, u}} {t : S ⟶ S'} (ht : IsFirstOrderThickening t)
  {f : X ⟶ S} {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  {i : X ⟶ X'} (hi : IsFirstOrderThickening i) {f' : X' ⟶ S'} (hcomm : i ≫ f' = f ≫ t)
  (κ : AlgebraicGeometry.SheafOfModules.idealSheaf i ≅
    (modulePushforward i).obj (show SheafOfModules.{u} (structureSheafRing X) from G))

/-- The square-zero extension of `f⁻¹𝒪_{S'}`-algebras underlying a first order thickening
`i : X ⟶ X'` with a morphism `f' : X' ⟶ S'` over `f ≫ t` and an identification `κ` of its ideal
with `i_*𝒢`: the structure sheaf `𝒪_{X'}` read on `X` as `i⁻¹𝒪_{X'}`. -/
abbrev solutionExtension : SquareZeroAlgebraExtension (f ≫ t) G :=
  thickeningExtension hi f' (f ≫ t) hcomm G (thickeningIdealIso hi G κ)

omit ht in
/-- The middle arrow of (08U7) for `solutionExtension`, on the image of the unit: `f'^♯`
followed by the unit of `i`, transported from `i⁻¹f'⁻¹V` to `f⁻¹t⁻¹V`. -/
theorem structureFMap_solutionExtension_app (V : Opens S'.carrier) (z : S'.presheaf.obj (op V)) :
    (structureFMap (solutionExtension hi hcomm κ)).hom.app (op ((Opens.map t.hom.base).obj V))
        ((inverseImageUnit t).hom.app (op V) z) =
      (inverseImageBaseRing i).obj.map
        (eqToHom (congrArg (fun m : X ⟶ S' => (Opens.map m.hom.base).obj V) hcomm).symm).op
        ((inverseImageUnit i).hom.app (op ((Opens.map f'.hom.base).obj V))
          (f'.hom.c.app (op V) z)) := by
  refine (homEquiv_symm_app_inverseImageUnit t _ V z).trans ?_
  have hb : (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f ≫ t).hom.base).homEquiv
      _ _ (solutionExtension hi hcomm κ).base = thickeningBaseTranspose f' (f ≫ t) hcomm :=
    Equiv.apply_symm_apply _ _
  rw [hb]
  exact thickeningBaseTranspose_app f' (f ≫ t) hcomm V z

include hcomm in
omit ht in
/-- The two preimages of an open of `S'` in `X` agree, the square commuting. -/
theorem opensMap_eq_of_comm (V : Opens S'.carrier) :
    (Opens.map f.hom.base).obj ((Opens.map t.hom.base).obj V) =
      (Opens.map i.hom.base).obj ((Opens.map f'.hom.base).obj V) :=
  (congrArg (fun m : X ⟶ S' => (Opens.map m.hom.base).obj V) hcomm).symm

/-- **The left square of (08U7) for the extension underlying a solution, on sections.** The
compatibility with an `f`-map `c : 𝒥 ⟶ f_*𝒢` of the middle arrow of `solutionExtension` says:
for every section `x` of `Ker(t^♯)` over `V`, `f'^♯(x) ∈ 𝒪_{X'}(f'⁻¹V)` is the inclusion of
`c(x) ∈ 𝒢(f⁻¹t⁻¹V) = 𝒢(i⁻¹f'⁻¹V)` through `κ`. -/
theorem structureFMap_solutionExtension_iff
    (c : (show SheafOfModules.{u} (structureSheafRing S) from baseIdealModule ht) ⟶
      (modulePushforward f).obj (show SheafOfModules.{u} (structureSheafRing X) from G)) :
    (∀ (U : Opens S.carrier) (s : (baseIdealModule ht).val.obj (op U)),
        ((structureFMap (solutionExtension hi hcomm κ)).hom.app (op U)).hom
          ((baseExtension ht).incl (op U) s) =
        (solutionExtension hi hcomm κ).incl (op ((Opens.map f.hom.base).obj U))
          (c.val.app (op U) s)) ↔
      ∀ (V : Opens S'.carrier) (x : RingHom.ker (t.hom.c.app (op V)).hom),
        f'.hom.c.app (op V) x.1 = (kernel.ι (structureSheafModuleHom i)).val.app _
          (κ.inv.val.app (op ((Opens.map f'.hom.base).obj V))
            (G.val.map (eqToHom (opensMap_eq_of_comm hcomm V).symm).op
              (c.val.app (op ((Opens.map t.hom.base).obj V))
                (baseIdealSectionsEquiv ht V x)))) := by
  have : IsIso t.hom.base := ht.1.1
  have : IsIso i.hom.base := hi.1.1
  let E := solutionExtension hi hcomm κ
  -- the condition at `t⁻¹V`, for the section `e_V x`
  have key : ∀ (V : Opens S'.carrier) (x : RingHom.ker (t.hom.c.app (op V)).hom),
      (((structureFMap E).hom.app (op ((Opens.map t.hom.base).obj V))).hom
          ((baseExtension ht).incl (op _) (baseIdealSectionsEquiv ht V x)) =
        E.incl (op ((Opens.map f.hom.base).obj ((Opens.map t.hom.base).obj V)))
          (c.val.app (op _) (baseIdealSectionsEquiv ht V x))) ↔
      f'.hom.c.app (op V) x.1 = (kernel.ι (structureSheafModuleHom i)).val.app _
          (κ.inv.val.app (op ((Opens.map f'.hom.base).obj V))
            (G.val.map (eqToHom (opensMap_eq_of_comm hcomm V).symm).op
              (c.val.app (op ((Opens.map t.hom.base).obj V))
                (baseIdealSectionsEquiv ht V x)))) := by
    intro V x
    let hV := opensMap_eq_of_comm hcomm V
    let e₂ : op ((Opens.map i.hom.base).obj ((Opens.map f'.hom.base).obj V)) ⟶
        op ((Opens.map f.hom.base).obj ((Opens.map t.hom.base).obj V)) := (eqToHom hV).op
    let e₁ : op ((Opens.map f.hom.base).obj ((Opens.map t.hom.base).obj V)) ⟶
        op ((Opens.map i.hom.base).obj ((Opens.map f'.hom.base).obj V)) := (eqToHom hV.symm).op
    let g : G.val.obj (op ((Opens.map f.hom.base).obj ((Opens.map t.hom.base).obj V))) :=
      c.val.app (op ((Opens.map t.hom.base).obj V)) (baseIdealSectionsEquiv ht V x)
    let w := κ.inv.val.app (op ((Opens.map f'.hom.base).obj V)) (G.val.map e₁ g)
    have hκ : κ.hom.val.app (op ((Opens.map f'.hom.base).obj V)) w = G.val.map e₁ g :=
      ConcreteCategory.congr_hom (congrArg (fun φ => φ.val.app (op ((Opens.map f'.hom.base).obj V)))
        κ.inv_hom_id) _
    have he₁₂ : e₁ ≫ e₂ = 𝟙 _ := by simp [e₁, e₂]
    have he₂₁ : e₂ ≫ e₁ = 𝟙 _ := by simp [e₁, e₂]
    have hg : G.val.map e₂ (G.val.map e₁ g) = g := by
      rw [← PresheafOfModules.map_comp_apply, PresheafOfModules.congr_map_apply _ he₁₂,
        PresheafOfModules.map_id]
      rfl
    have hL : ((structureFMap E).hom.app (op ((Opens.map t.hom.base).obj V))).hom
        ((baseExtension ht).incl (op _) (baseIdealSectionsEquiv ht V x)) =
        (E.sheaf.obj.map e₂).hom ((inverseImageUnit i).hom.app (op ((Opens.map f'.hom.base).obj V))
          (f'.hom.c.app (op V) x.1)) := by
      rw [baseExtension_incl]
      exact structureFMap_solutionExtension_app hi hcomm κ V x.1
    have hR : E.incl (op ((Opens.map f.hom.base).obj ((Opens.map t.hom.base).obj V))) g =
        (E.sheaf.obj.map e₂).hom ((inverseImageUnit i).hom.app (op ((Opens.map f'.hom.base).obj V))
          ((kernel.ι (structureSheafModuleHom i)).val.app _ w)) := by
      rw [← thickeningExtension_incl_kernelIso hi f' (f ≫ t) hcomm G κ, hκ]
      exact (congrArg (E.incl _) hg.symm).trans (E.incl_map _ e₂ _).symm
    have hinj : Function.Injective (fun a => (E.sheaf.obj.map e₂).hom
        ((inverseImageUnit i).hom.app (op ((Opens.map f'.hom.base).obj V)) a)) := by
      intro a b hab
      have h : E.sheaf.obj.map e₂ ≫ E.sheaf.obj.map e₁ = 𝟙 _ := by
        rw [← E.sheaf.obj.map_comp, he₂₁, E.sheaf.obj.map_id]
      have h₁ : ∀ z, (E.sheaf.obj.map e₁).hom ((E.sheaf.obj.map e₂).hom z) = z := fun z =>
        ConcreteCategory.congr_hom h z
      have hab' := ((h₁ _).symm.trans (congrArg (E.sheaf.obj.map e₁).hom hab)).trans (h₁ _)
      exact (bijective_inverseImageUnit_app i _).1 hab'
    rw [hL, hR]
    exact hinj.eq_iff
  refine ⟨fun h V x => (key V x).1 (h _ _), fun h U s => ?_⟩
  obtain ⟨V, rfl⟩ := exists_map_obj_eq t U
  obtain ⟨x, rfl⟩ := (baseIdealSectionsEquiv ht V).surjective s
  exact (key V x).2 (h V x)

/-- The transposed compatibility equation, on sections. -/
theorem transposedCompatibility_iff
    (c : (show SheafOfModules.{u} (structureSheafRing S) from baseIdealModule ht) ⟶
      (modulePushforward f).obj (show SheafOfModules.{u} (structureSheafRing X) from G)) :
    (baseIdealPushforwardIso ht).inv ≫ (modulePushforward t).map c ≫
        (modulePushforwardComp f t).hom.app G ≫
        eqToHom (congrArg (fun k : X ⟶ S' => (modulePushforward k).obj
          (show SheafOfModules.{u} (structureSheafRing X) from G)) hcomm.symm) ≫
        (modulePushforwardComp i f').inv.app G ≫
        (modulePushforward f').map (κ.inv ≫ kernel.ι (structureSheafModuleHom i)) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom t)) ≫
        SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f') ↔
      ∀ (V : Opens S'.carrier) (x : RingHom.ker (t.hom.c.app (op V)).hom),
        f'.hom.c.app (op V) x.1 = (kernel.ι (structureSheafModuleHom i)).val.app _
          (κ.inv.val.app (op ((Opens.map f'.hom.base).obj V))
            (G.val.map (eqToHom (opensMap_eq_of_comm hcomm V).symm).op
              (c.val.app (op ((Opens.map t.hom.base).obj V))
                (baseIdealSectionsEquiv ht V x)))) := by
  have key : ∀ (V : Opens S'.carrier)
      (y : (AlgebraicGeometry.SheafOfModules.idealSheaf t).val.obj (op V)),
      ((baseIdealPushforwardIso ht).inv ≫ (modulePushforward t).map c ≫
        (modulePushforwardComp f t).hom.app G ≫
        eqToHom (congrArg (fun k : X ⟶ S' => (modulePushforward k).obj
          (show SheafOfModules.{u} (structureSheafRing X) from G)) hcomm.symm) ≫
        (modulePushforwardComp i f').inv.app G ≫
        (modulePushforward f').map (κ.inv ≫ kernel.ι (structureSheafModuleHom i))).val.app
          (op V) y =
      (kernel.ι (structureSheafModuleHom i)).val.app _
          (κ.inv.val.app (op ((Opens.map f'.hom.base).obj V))
            (G.val.map (eqToHom (opensMap_eq_of_comm hcomm V).symm).op
              (c.val.app (op ((Opens.map t.hom.base).obj V))
                (baseIdealSectionsEquiv ht V ⟨_, idealSheafι_mem_ker V y⟩)))) := by
    intro V y
    rw [baseIdealSectionsEquiv_idealSheafι]
    exact congrArg (fun z : ((modulePushforward i).obj
        (show SheafOfModules.{u} (structureSheafRing X) from G)).val.obj
          (op ((Opens.map f'.hom.base).obj V)) =>
        (kernel.ι (structureSheafModuleHom i)).val.app _
          (κ.inv.val.app (op ((Opens.map f'.hom.base).obj V)) z))
      (eqToHom_modulePushforward_app hcomm.symm _ V _)
  refine ⟨fun h V x => ?_, fun h => ?_⟩
  · let y := (baseIdealPushforwardIso ht).hom.val.app (op V) (baseIdealSectionsEquiv ht V x)
    have hy : (⟨_, idealSheafι_mem_ker V y⟩ : RingHom.ker (t.hom.c.app (op V)).hom) = x := by
      apply Subtype.ext
      refine (congrArg (fun φ => φ.val.app (op V) (baseIdealSectionsEquiv ht V x))
        (baseIdealPushforwardIso_hom_ι ht)).trans ?_
      show ((baseIdealSectionsEquiv ht V).symm (baseIdealSectionsEquiv ht V x)).1 = x.1
      rw [Equiv.symm_apply_apply]
    have h' := congrArg (fun φ => φ.val.app (op V) y) h
    rw [key, hy] at h'
    exact (congrArg (f'.hom.c.app (op V)) (congrArg Subtype.val hy)).symm.trans h'.symm
  · ext V y
    rw [key]
    exact (h V.unop ⟨_, idealSheafι_mem_ker V.unop y⟩).symm

/-- **The compatibility equation of a solution of Stacks 08U7 is the left square of (08U7).** For
a first order thickening `i : X ⟶ X'` with `f' : X' ⟶ S'` over `f ≫ t` and an identification `κ`
of its ideal with `i_*𝒢`, the canonical map `i_*f^*𝒥 ⟶ Ker(i^♯)` of **Stacks 08KZ** is the
prescribed `c'` under `κ` exactly when the middle arrow of the underlying extension
`solutionExtension` restricts to the `f`-map `prescribedFMap c'` on the ideals. -/
theorem firstOrderIdealMap_comp_eq_iff_leftSquare
    (c' : (modulePullback f).obj ((modulePullback t).obj
      (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶
        (show SheafOfModules.{u} (structureSheafRing X) from G)) :
    ((MorphismOfThickenings.mk X X' S S' i t f f' hi.1 ht.1 hcomm).firstOrderIdealMap hi ht).1 ≫
        κ.hom = (modulePushforward i).map c' ↔
      ∀ (U : Opens S.carrier) (s : (baseIdealModule ht).val.obj (op U)),
        ((structureFMap (solutionExtension hi hcomm κ)).hom.app (op U)).hom
          ((baseExtension ht).incl (op U) s) =
        (solutionExtension hi hcomm κ).incl (op ((Opens.map f.hom.base).obj U))
          ((prescribedFMap ht f _ c').val.app (op U) s) := by
  have h1 := firstOrderIdealMap_comp_eq_iff (MorphismOfThickenings.mk X X' S S' i t f f' hi.1 ht.1
    hcomm) hi ht _ κ c'
  have h2 := homEquiv_firstOrderSurjection_comp (MorphismOfThickenings.mk X X' S S' i t f f' hi.1
    ht.1 hcomm) hi ht _ c' (κ.inv ≫ kernel.ι (structureSheafModuleHom i))
  have h3 := transposedCompatibility_iff ht hcomm κ (prescribedFMap ht f _ c')
  have h4 := structureFMap_solutionExtension_iff ht hi hcomm κ (prescribedFMap ht f _ c')
  exact h1.trans ((Eq.congr_left h2).trans (h3.trans h4.symm))

end Compat

/-- **A solution of Stacks 08U7 in the form `DeformationSolution` is a solution in the form
`ExtensionSolution`**: its structure sheaf read on `X` is an extension of `f⁻¹𝒪_{S'}`-algebras,
and its compatibility equation gives the `S'`-morphism compatible with `f` and the `f`-map
`prescribedFMap c'` (`firstOrderIdealMap_comp_eq_iff_leftSquare`). -/
noncomputable def DeformationSolution.toExtensionSolution {X S S' : RingedSpace.{u, u}}
    {t : S ⟶ S'} {ht : IsFirstOrderThickening t} {f : X ⟶ S}
    {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
    {c' : (modulePullback f).obj ((modulePullback t).obj
      (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶
        (show SheafOfModules.{u} (structureSheafRing X) from G)}
    (Q : DeformationSolution t ht f G c') :
    ExtensionSolution ht f G (prescribedFMap ht f _ c') where
  extension := solutionExtension Q.i_firstOrder Q.comm Q.kernelIso
  lift := ((nonempty_compatibleMorphism_iff ht _).2
    ((firstOrderIdealMap_comp_eq_iff_leftSquare ht Q.i_firstOrder Q.comm Q.kernelIso c').1
      Q.compatibility)).some

section OfExtension

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t} {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  {c' : (modulePullback f).obj ((modulePullback t).obj
    (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶
      (show SheafOfModules.{u} (structureSheafRing X) from G)}

/-- Isomorphic extensions admit compatible morphisms together: by **Stacks 0GQ1** the existence
depends only on the class of the extension. -/
theorem nonempty_compatibleMorphism_of_iso {c : (show SheafOfModules.{u} (structureSheafRing S)
      from baseIdealModule ht) ⟶ (modulePushforward f).obj
        (show SheafOfModules.{u} (structureSheafRing X) from G)}
    {P Q : SquareZeroAlgebraExtension (f ≫ t) G} (e : P ≅ Q)
    (h : Nonempty (CompatibleMorphism (baseExtension ht) P c)) :
    Nonempty (CompatibleMorphism (baseExtension ht) Q c) :=
  (nonempty_compatibleMorphism_iff_pullbackExtClass_eq f (baseExtension ht) Q c).2
    (((nonempty_compatibleMorphism_iff_pullbackExtClass_eq f (baseExtension ht) P c).1 h).trans
      (congrArg (fun z => restrictDerivedExtClass (derivedPullbackNaiveCotangentMap f t)
        (SquareZeroAlgebraExtension.isomorphismClassesEquivExt (f ≫ t) G z)) (Quotient.sound ⟨e⟩ :
        (Quotient.mk _ P : SquareZeroAlgebraExtension.IsomorphismClasses (f ≫ t) G) =
          Quotient.mk _ Q)))

/-- **A solution of Stacks 08U7 in the form `ExtensionSolution` gives one in the form
`DeformationSolution`**: the first order thickening `X ⟶ X' = (X, 𝒪_{X'})` over `S'` of the
extension, with `Ker(i^♯) ≅ i_*𝒢`; its compatibility equation is the left square of (08U7)
(`firstOrderIdealMap_comp_eq_iff_leftSquare`). -/
noncomputable def ExtensionSolution.toDeformationSolution
    (E : ExtensionSolution ht f G (prescribedFMap ht f _ c')) :
    DeformationSolution t ht f G c' where
  X' := E.extension.space
  i := E.extension.thickening
  f' := E.extension.over
  i_firstOrder := E.extension.isFirstOrderThickening_thickening
  comm := E.extension.thickening_comp_over
  kernelIso := E.extension.thickeningKernelIso
  compatibility := by
    intro D
    exact (firstOrderIdealMap_comp_eq_iff_leftSquare ht
      E.extension.isFirstOrderThickening_thickening E.extension.thickening_comp_over
      E.extension.thickeningKernelIso c').2 ((nonempty_compatibleMorphism_iff ht _).1
        (nonempty_compatibleMorphism_of_iso E.extension.isoThickeningExtensionOf ⟨E.lift⟩))

/-- The round trip `ExtensionSolution ⟶ DeformationSolution ⟶ ExtensionSolution` returns an
isomorphic extension. -/
noncomputable def ExtensionSolution.toDeformationSolutionIso
    (E : ExtensionSolution ht f G (prescribedFMap ht f _ c')) :
    E.extension ≅ (E.toDeformationSolution.toExtensionSolution).extension :=
  E.extension.isoThickeningExtensionOf

variable (t ht f G c')

/-- **Isomorphism of solutions of Stacks 08U7 in the form `DeformationSolution`**: an isomorphism
of the underlying extensions of `f⁻¹𝒪_{S'}`-algebras, i.e. of the structure sheaves `𝒪_{X'}` read
on `X`, compatible with the reductions to `𝒪_X`, with the `f⁻¹𝒪_{S'}`-algebra structures (the
morphisms to `S'`) and with the identifications of the ideals with `𝒢`. -/
def DeformationSolution.extensionSetoid : Setoid (DeformationSolution t ht f G c') where
  r Q₁ Q₂ := Nonempty (Q₁.toExtensionSolution.extension ≅ Q₂.toExtensionSolution.extension)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e ≪≫ e'⟩⟩

/-- **The isomorphism classes of solutions in the two forms agree.** -/
noncomputable def DeformationSolution.classesEquivExtensionClasses :
    Quotient (DeformationSolution.extensionSetoid t ht f G c') ≃
      ExtensionSolution.IsomorphismClasses ht f G (prescribedFMap ht f _ c') :=
  Equiv.ofBijective
    (Quotient.map (fun Q => Q.toExtensionSolution) (fun _ _ h => h))
    ⟨by
      rintro ⟨Q₁⟩ ⟨Q₂⟩ h
      have h' : (Quotient.mk _ Q₁.toExtensionSolution :
          ExtensionSolution.IsomorphismClasses ht f G (prescribedFMap ht f _ c')) =
          Quotient.mk _ Q₂.toExtensionSolution := h
      exact Quotient.sound (Quotient.exact h' :
        Nonempty (Q₁.toExtensionSolution.extension ≅ Q₂.toExtensionSolution.extension)),
     by
      rintro ⟨E⟩
      exact ⟨Quotient.mk _ E.toDeformationSolution,
        Quotient.sound ⟨E.toDeformationSolutionIso.symm⟩⟩⟩

/-- `DeformationSolution.classesEquivExtensionClasses` sends the class of `Q` to the class of
`Q.toExtensionSolution`. -/
theorem DeformationSolution.classesEquivExtensionClasses_mk (Q : DeformationSolution t ht f G c') :
    DeformationSolution.classesEquivExtensionClasses t ht f G c' (Quotient.mk _ Q) =
      Quotient.mk _ Q.toExtensionSolution :=
  rfl

end OfExtension

end AlgebraicGeometry.RingedSpaceThickening

end
