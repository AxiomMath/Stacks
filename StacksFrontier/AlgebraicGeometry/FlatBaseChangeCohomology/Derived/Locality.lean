module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.MayerVietoris
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineBaseReduction
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.BaseChange
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition

/-!
# The derived base change map is an isomorphism locally on the base

Let
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
be a commutative square of schemes with `g` and `g'` flat. This file proves that the base change
map `β : g^* Rf_* ⟶ Rf'_* (g')^*` of [Stacks, Tag 02N7] is invertible at a module `ℱ` as soon as,
for the members `U` of an open cover of `S`, the base change map of the square obtained by
restricting the base to `U` and to `g⁻¹(U)` is invertible at `ℱ|_{f⁻¹(U)}`.

This is the opening reduction of the proof of [Stacks, Tag 02KH]: "part (1) is local on `S'` and
hence we may assume `S` and `S'` are affine".

## Main results

* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isIso_schemeBaseChange_restrictSquare`: the base
  change map of the square restricting a morphism over an open of its target is an isomorphism.
* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isIso_of_isIso_pullback_cover`: a morphism of
  `D⁺(𝒪_S)` is invertible as soon as its pullbacks to the members of an open cover of `S` are.
* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isIso_schemeBaseChange_of_cover_base`: the
  locality statement.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
  RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.FlatBaseChangeDerived

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

attribute [local instance] abelianModules enoughInjectivesModules

/-- Pullback of sheaves of modules along a morphism of schemes is right exact. -/
theorem preservesFiniteColimits_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (modulePullback f.toLRSHom.toShHom) :=
  preservesFiniteColimits_modulePullback _

/-! ### The restriction square -/

section RestrictSquare

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)

/-- **The base change map of a restriction square is an isomorphism.** For a morphism `f` and an
open `V` of its target, the square
```
f⁻¹(V) --⊂--> X
  |f|_V       |f
  V ----⊂---> S
```
has invertible base change map `(Rf_* -)|_V ⟶ R(f|_V)_* (-|_{f⁻¹(V)})`: restriction to an open
commutes with direct images on the nose, and restriction preserves injective modules. -/
theorem isIso_schemeBaseChange_restrictSquare :
    IsIso (schemeBaseChange f (f ∣_ V) V.ι (f ⁻¹ᵁ V).ι
      (Stacks.AlgebraicGeometry.AffineBaseChange.restrictSquare f V)) := by
  have hτ : IsIso (schemeModuleBaseChange f (f ∣_ V) V.ι (f ⁻¹ᵁ V).ι
      (Stacks.AlgebraicGeometry.AffineBaseChange.restrictSquare f V)) := by
    rw [moduleBaseChange_eq]
    exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
      (Stacks.AlgebraicGeometry.AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare f V)
  have := isIso_pullbackUnit (f ⁻¹ᵁ V).ι
  have := Stacks.Cohomology.RelativeMayerVietoris.modulePullback_preservesInjectiveObjects
    (f ⁻¹ᵁ V).ι.toLRSHom.toShHom
  exact Stacks.Cohomology.ProperBaseChange.isIso_baseChangeDerived _ _ _ _ _
    (fun _ _ => inferInstance) _
    (fun M hM =>
      have := Functor.PreservesInjectiveObjects.injective_obj
        (F := modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom) hM
      CategoryTheory.Functor.rightAcyclic_of_injective _ _)

end RestrictSquare

/-! ### Pasting along the base -/

section Paste

variable {X X' X'' S S' S'' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {f'' : X'' ⟶ S''}
  {g : S' ⟶ S} {g' : X' ⟶ X} {h : S'' ⟶ S'} {h' : X'' ⟶ X'}

/-- The identification of the pullback along a composite with the composite of the pullbacks, in
the spelling of sheaves of modules on the underlying ringed spaces. -/
def pullbackCompIso (h : S'' ⟶ S') (g : S' ⟶ S) :
    modulePullback g.toLRSHom.toShHom ⋙ modulePullback h.toLRSHom.toShHom ≅
      modulePullback (h ≫ g).toLRSHom.toShHom :=
  Scheme.Modules.pullbackComp h g

/-- **The base change morphisms paste along the base**, at a module. -/
theorem baseChangeNatTrans_pasteBase_app (w₁ : g' ≫ f = f' ≫ g) (w₂ : h' ≫ f' = f'' ≫ h)
    (M : X.Modules) :
    (Scheme.Modules.pullbackComp h g).hom.app ((Scheme.Modules.pushforward f).obj M) ≫
      (AffinePushforward.baseChangeNatTrans
        (Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.pasteBase w₁ w₂)).app M ≫
      (Scheme.Modules.pushforward f'').map ((Scheme.Modules.pullbackComp h' g').inv.app M) =
    (Scheme.Modules.pullback h).map ((AffinePushforward.baseChangeNatTrans w₁).app M) ≫
      (AffinePushforward.baseChangeNatTrans w₂).app ((Scheme.Modules.pullback g').obj M) := by
  have hM := congrArg (fun w => NatTrans.app w M)
    (Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.baseChangeSquare_pasteBase w₁ w₂)
  simp only [Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.natTrans_baseChangeSquare,
    TwoSquare.whiskerRight_app, TwoSquare.whiskerLeft_app] at hM
  rw [hM]
  simp [TwoSquare.vComp]

/-- **The underived base change maps paste along the base**, in the spelling of
`Stacks.Cohomology.BaseChange.pasteTrans`. -/
theorem schemeModuleBaseChange_pasteBase (w₁ : g' ≫ f = f' ≫ g) (w₂ : h' ≫ f' = f'' ≫ h) :
    Functor.whiskerLeft (modulePushforward f.toLRSHom.toShHom) (pullbackCompIso h g).hom ≫
      schemeModuleBaseChange f f'' (h ≫ g) (h' ≫ g')
        (Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.pasteBase w₁ w₂) ≫
      Functor.whiskerRight (pullbackCompIso h' g').inv
        (modulePushforward f''.toLRSHom.toShHom) =
    Stacks.Cohomology.BaseChange.pasteTrans (modulePushforward f.toLRSHom.toShHom)
      (modulePushforward f'.toLRSHom.toShHom) (modulePushforward f''.toLRSHom.toShHom)
      (modulePullback g.toLRSHom.toShHom) (modulePullback g'.toLRSHom.toShHom)
      (modulePullback h.toLRSHom.toShHom) (modulePullback h'.toLRSHom.toShHom)
      (schemeModuleBaseChange f f' g g' w₁) (schemeModuleBaseChange f' f'' h h' w₂) := by
  refine NatTrans.ext (funext fun M => ?_)
  rw [moduleBaseChange_eq, moduleBaseChange_eq, moduleBaseChange_eq]
  exact baseChangeNatTrans_pasteBase_app w₁ w₂ M

end Paste

/-! ### Invertibility in `D⁺` is local -/

/-- **A morphism of `D⁺(𝒪_S)` is invertible as soon as its pullbacks to the members of an open
cover of `S` are.** Invertibility is detected on cohomology sheaves, pullback to an open commutes
with cohomology sheaves, and invertibility of a morphism of sheaves is local. -/
theorem isIso_of_isIso_pullback_cover {S : Scheme.{u}}
    {A B : DerivedCategory.Plus (_root_.SheafOfModules.{u} (structureSheafRing S.toRingedSpace))}
    (φ : A ⟶ B) {ι : Type*} (V : ι → S.Opens) (hV : IsOpenCover V)
    (h : ∀ i, IsIso ((modulePullback (V i).ι.toLRSHom.toShHom).rightDerivedFunctorPlus.map φ)) :
    IsIso φ := by
  rw [DerivedCategory.Plus.isIso_iff]
  intro n
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict _ V hV (fun i => ?_)
  have := preservesFiniteLimits_pullback (V i).ι
  have := preservesFiniteColimits_pullback (V i).ι
  have h₁ : IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((modulePullback (V i).ι.toLRSHom.toShHom).rightDerivedFunctorPlus.map φ)) :=
    have := h i
    inferInstance
  have h₂ : IsIso ((modulePullback (V i).ι.toLRSHom.toShHom).map
      ((DerivedCategory.Plus.homologyFunctor _ n).map φ)) :=
    (NatIso.isIso_map_iff
      (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
        (modulePullback (V i).ι.toLRSHom.toShHom) n) φ).1 h₁
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback (V i).ι) _).2 h₂

/-! ### Locality on the base -/

section LocalityBase

/-- The base change map depends only on the morphisms of the square. -/
theorem isIso_schemeBaseChange_congr {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {b b' : S' ⟶ S} {t t' : X' ⟶ X} (hb : b = b') (ht : t = t') (w : t ≫ f = f' ≫ b)
    (w' : t' ≫ f = f' ≫ b') [Flat b] [Flat t] [Flat b'] [Flat t']
    (Y : DerivedCategory.Plus (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    IsIso ((schemeBaseChange f f' b t w).app Y) ↔
      IsIso ((schemeBaseChange f f' b' t' w').app Y) := by
  subst hb ht
  rfl

/-- The derived pullback of a module along a flat morphism is its pullback. -/
def pullbackSingleIso {X Y : Scheme.{u}} (j : Y ⟶ X) [Flat j]
    (F : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (modulePullback j.toLRSHom.toShHom).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj ((modulePullback j.toLRSHom.toShHom).obj F) :=
  (modulePullback j.toLRSHom.toShHom).rightDerivedFunctorPlus.mapIso
      ((Functor.singleFunctorPlusIsoCompQh 0).app F) ≪≫
    (pullbackQhIso j _).symm ≪≫
    pullbackResolutionIso j F _ ((Functor.singleFunctorPlusIsoCompQh 0).app F).symm

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}
  (H : IsPullback g' f' f g) [Flat g] [Flat g']

include H in
/-- **Locality on the base.** The base change map of a cartesian square with `g` flat is
invertible at an `𝒪_X`-module `ℱ` as soon as, for the members `U` of an open cover of `S`, the
base change map of the square restricted over `U` and `g⁻¹(U)` is invertible at `ℱ|_{f⁻¹(U)}`. -/
theorem isIso_schemeBaseChange_of_cover_base {ι : Type*} (U : ι → S.Opens) (hU : IsOpenCover U)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (h : ∀ i, IsIso ((schemeBaseChange (f ∣_ U i) (f' ∣_ g ⁻¹ᵁ U i)
        (g.resLE (U i) (g ⁻¹ᵁ U i) le_rfl)
        (g'.resLE (f ⁻¹ᵁ U i) (f' ⁻¹ᵁ g ⁻¹ᵁ U i)
          (Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.preimage_le_of_comm H.w le_rfl))
        (Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.restrictBasesSquare H.w (U i)
          le_rfl)).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((modulePullback (f ⁻¹ᵁ U i).ι.toLRSHom.toShHom).obj F)))) :
    IsIso ((schemeBaseChange f f' g g' H.w).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  refine isIso_of_isIso_pullback_cover _ (fun i => g ⁻¹ᵁ U i) (hU.comap g.base.hom) (fun i => ?_)
  let V := U i
  let W := g ⁻¹ᵁ V
  let X₀ := (DerivedCategory.Plus.singleFunctor
    (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F
  let gV := g.resLE V W le_rfl
  let gV' := g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ W)
    (Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.preimage_le_of_comm H.w le_rfl)
  have hV := Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.restrictBasesSquare H.w V
    (le_refl W)
  have hfl : ∀ {A B : Scheme.{u}} (j : A ⟶ B) [Flat j],
      PreservesFiniteLimits (modulePullback j.toLRSHom.toShHom) :=
    fun j _ => preservesFiniteLimits_pullback j
  have hfc : ∀ {A B : Scheme.{u}} (j : A ⟶ B) [Flat j],
      PreservesFiniteColimits (modulePullback j.toLRSHom.toShHom) :=
    fun j _ => preservesFiniteColimits_pullback j
  -- the rectangle over `W ⟶ S' ⟶ S`
  have hA := (Stacks.Cohomology.BaseChange.isIso_derived_paste_app_iff_left
    (modulePushforward f.toLRSHom.toShHom) (modulePushforward f'.toLRSHom.toShHom)
    (modulePushforward (f' ∣_ W).toLRSHom.toShHom)
    (modulePullback g.toLRSHom.toShHom) (modulePullback g'.toLRSHom.toShHom)
    (modulePullback W.ι.toLRSHom.toShHom) (modulePullback (f' ⁻¹ᵁ W).ι.toLRSHom.toShHom)
    (schemeModuleBaseChange f f' g g' H.w)
    (schemeModuleBaseChange f' (f' ∣_ W) W.ι (f' ⁻¹ᵁ W).ι
      (Stacks.AlgebraicGeometry.AffineBaseChange.restrictSquare f' W))
    (isIso_schemeBaseChange_restrictSquare f' W) X₀)
  have hR₁ := (Stacks.Cohomology.BaseChange.isIso_derived_app_iff_paste
    (modulePushforward f.toLRSHom.toShHom) (modulePushforward f'.toLRSHom.toShHom)
    (modulePushforward (f' ∣_ W).toLRSHom.toShHom)
    (modulePullback g.toLRSHom.toShHom) (modulePullback g'.toLRSHom.toShHom)
    (modulePullback W.ι.toLRSHom.toShHom) (modulePullback (f' ⁻¹ᵁ W).ι.toLRSHom.toShHom)
    (schemeModuleBaseChange f f' g g' H.w)
    (schemeModuleBaseChange f' (f' ∣_ W) W.ι (f' ⁻¹ᵁ W).ι
      (Stacks.AlgebraicGeometry.AffineBaseChange.restrictSquare f' W))
    (pullbackCompIso W.ι g) (pullbackCompIso (f' ⁻¹ᵁ W).ι g')
    (schemeModuleBaseChange f (f' ∣_ W) (W.ι ≫ g) ((f' ⁻¹ᵁ W).ι ≫ g')
      (Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.pasteBase H.w
        (Stacks.AlgebraicGeometry.AffineBaseChange.restrictSquare f' W)))
    (schemeModuleBaseChange_pasteBase H.w
      (Stacks.AlgebraicGeometry.AffineBaseChange.restrictSquare f' W)) X₀)
  -- the rectangle over `W ⟶ V ⟶ S`
  have hB₁ : IsIso ((schemeBaseChange f (f ∣_ V) V.ι (f ⁻¹ᵁ V).ι
      (Stacks.AlgebraicGeometry.AffineBaseChange.restrictSquare f V)).app X₀) :=
    have := isIso_schemeBaseChange_restrictSquare f V
    inferInstance
  have hB := (Stacks.Cohomology.BaseChange.isIso_derived_paste_app_iff_right
    (modulePushforward f.toLRSHom.toShHom) (modulePushforward (f ∣_ V).toLRSHom.toShHom)
    (modulePushforward (f' ∣_ W).toLRSHom.toShHom)
    (modulePullback V.ι.toLRSHom.toShHom) (modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom)
    (modulePullback gV.toLRSHom.toShHom) (modulePullback gV'.toLRSHom.toShHom)
    (schemeModuleBaseChange f (f ∣_ V) V.ι (f ⁻¹ᵁ V).ι
      (Stacks.AlgebraicGeometry.AffineBaseChange.restrictSquare f V))
    (schemeModuleBaseChange (f ∣_ V) (f' ∣_ W) gV gV' hV) X₀ hB₁)
  have hR₂ := (Stacks.Cohomology.BaseChange.isIso_derived_app_iff_paste
    (modulePushforward f.toLRSHom.toShHom) (modulePushforward (f ∣_ V).toLRSHom.toShHom)
    (modulePushforward (f' ∣_ W).toLRSHom.toShHom)
    (modulePullback V.ι.toLRSHom.toShHom) (modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom)
    (modulePullback gV.toLRSHom.toShHom) (modulePullback gV'.toLRSHom.toShHom)
    (schemeModuleBaseChange f (f ∣_ V) V.ι (f ⁻¹ᵁ V).ι
      (Stacks.AlgebraicGeometry.AffineBaseChange.restrictSquare f V))
    (schemeModuleBaseChange (f ∣_ V) (f' ∣_ W) gV gV' hV)
    (pullbackCompIso gV V.ι) (pullbackCompIso gV' (f ⁻¹ᵁ V).ι)
    (schemeModuleBaseChange f (f' ∣_ W) (gV ≫ V.ι) (gV' ≫ (f ⁻¹ᵁ V).ι)
      (Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.pasteBase
        (Stacks.AlgebraicGeometry.AffineBaseChange.restrictSquare f V) hV))
    (schemeModuleBaseChange_pasteBase
      (Stacks.AlgebraicGeometry.AffineBaseChange.restrictSquare f V) hV) X₀)
  have hC := isIso_schemeBaseChange_congr (f := f) (f' := f' ∣_ W)
    (Scheme.Hom.resLE_comp_ι g le_rfl).symm
    (Scheme.Hom.resLE_comp_ι g' _).symm
    (Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.pasteBase H.w
      (Stacks.AlgebraicGeometry.AffineBaseChange.restrictSquare f' W))
    (Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.pasteBase
      (Stacks.AlgebraicGeometry.AffineBaseChange.restrictSquare f V) hV) X₀
  have hD : IsIso ((schemeBaseChange (f ∣_ V) (f' ∣_ W) gV gV' hV).app
      ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).rightDerivedFunctorPlus.obj X₀)) :=
    Stacks.Cohomology.RestrictionCover.isIso_app_of_iso _ (pullbackSingleIso (f ⁻¹ᵁ V).ι F) (h i)
  exact hA.1 (hR₁.1 (hC.2 (hR₂.2 (hB.2 hD))))

end LocalityBase

end Stacks.AlgebraicGeometry.FlatBaseChangeDerived

end
