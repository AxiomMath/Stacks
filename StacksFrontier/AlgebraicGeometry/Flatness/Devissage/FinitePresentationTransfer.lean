module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.SliceTransport
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.ElementaryDevissage
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.FiniteSingletonFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit

/-!
# Finite presentation along an elementary dévissage

Let `f : X ⟶ S` be locally of finite presentation and let `D` be an elementary dévissage of a
finite-type quasi-coherent module `F` at a point `x` (Stacks 057S,
`AlgebraicGeometry.ElementaryDevissage`): étale neighbourhoods `U` of `(X, x)` and `V` of
`(S, f x)`, a finitely presented closed immersion `i : Z ⟶ U` carrying a module `G` with
`i_* G ≅ g^* F`, and a factorisation of `Z ⟶ V` as a finite `π : Z ⟶ Y` followed by a smooth
`h : Y ⟶ V`.

This file proves Stacks 057T: the finite morphism `π` is of finite presentation, and the three
modules `F`, `G` and `π_* G` are of finite presentation — near their distinguished points, and
on their stalks at those points — simultaneously.

## Main definitions

* `AlgebraicGeometry.IsFinitePresentationNear`: a sheaf of modules is of finite presentation on
  some open neighbourhood of a point.

## Main results

* `AlgebraicGeometry.ElementaryDevissage.finitePresentation_π`: **Stacks 057T**, the finite
  morphism of an elementary dévissage is of finite presentation.
* `AlgebraicGeometry.ElementaryDevissage.isFinitePresentationNear_iff_closed` and
  `AlgebraicGeometry.ElementaryDevissage.isFinitePresentationNear_iff_pushforward`: **Stacks
  057T**, the equivalence of conditions (1), (2) and (3).
* `AlgebraicGeometry.ElementaryDevissage.finitePresentation_stalk_iff_closed` and
  `AlgebraicGeometry.ElementaryDevissage.finitePresentation_stalk_iff_pushforward`: **Stacks
  057T**, the equivalence of conditions (a), (b) and (c).

## Implementation notes

The source states (1) ⇔ (2) ⇔ (3) and (a) ⇔ (b) ⇔ (c) as two three-way equivalences. Each is
recorded here as a pair of two-way equivalences through the middle condition, which is where the
proof factors anyway: the step from `F` to `G` is étale descent followed by the closed immersion,
and the step from `G` to `π_* G` is the finite morphism `π` with its singleton fibre.

Both steps over a finite morphism with a singleton fibre go through
`StacksFrontier/AlgebraicGeometry/Morphisms/EtaleNeighbourhood/FiniteSingletonFibre.lean` (Stacks
05B8): a prescribed neighbourhood of the source point contains the inverse image of a
neighbourhood of the target point, the stalk map is finite and of finite presentation, and the
stalk of the module is the stalk of its pushforward. Restriction of a direct image to an open of
the target is the direct image of a restriction by
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`.

The stalk conditions are phrased with the ambient module structure of a stalk, the one
`Stacks.StalkFiniteType.finitePresentation_stalk_of_flat` and Stacks 05I7 use, so that the
equivalences compose with those statements without a bridge.

## References

* [Stacks Project, Tag 057T](https://stacks.math.columbia.edu/tag/057T)
* [Stacks Project, Tag 057S](https://stacks.math.columbia.edu/tag/057S)
* [Stacks Project, Tag 05B8](https://stacks.math.columbia.edu/tag/05B8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A sheaf of modules is of finite presentation *near* a point if it is of finite presentation
on some open neighbourhood of that point. -/
def IsFinitePresentationNear {X : Scheme.{u}} (F : X.Modules) (x : X) : Prop :=
  ∃ U : X.Opens, x ∈ U ∧ (F.restrict U.ι).IsFinitePresentation

namespace IsFinitePresentationNear

/-- Finite presentation near a point only depends on the isomorphism class of the module. -/
theorem of_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) {x : X}
    (hF : IsFinitePresentationNear F x) : IsFinitePresentationNear G x := by
  obtain ⟨U, hxU, hU⟩ := hF
  exact ⟨U, hxU, (SheafOfModules.isFinitePresentation (U : Scheme).ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctor U.ι).mapIso e) hU⟩

/-- Finite presentation near a point is invariant under an isomorphism of modules. -/
theorem iff_of_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) (x : X) :
    IsFinitePresentationNear F x ↔ IsFinitePresentationNear G x :=
  ⟨of_iso e, of_iso e.symm⟩

/-- Finite presentation of the restriction to an open passes to the pullback along any morphism
whose range lies in that open. -/
private theorem isFinitePresentation_pullback_of_range_subset {X T : Scheme.{u}} (F : X.Modules)
    {U : X.Opens} (k : T ⟶ X) (hk : Set.range k ⊆ Set.range U.ι)
    (hU : (F.restrict U.ι).IsFinitePresentation) :
    ((Scheme.Modules.pullback k).obj F).IsFinitePresentation := by
  let g : T ⟶ (U : Scheme) := IsOpenImmersion.lift U.ι k hk
  have hgi : g ≫ U.ι = k := IsOpenImmersion.lift_fac U.ι k hk
  have hU' : ((Scheme.Modules.pullback U.ι).obj F).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (U : Scheme).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F) hU
  have hG : ((Scheme.Modules.pullback g).obj
      ((Scheme.Modules.pullback U.ι).obj F)).IsFinitePresentation :=
    @Stacks.StalkFiniteType.isFinitePresentation_pullback _ _ g _ hU'
  have h₁ := (SheafOfModules.isFinitePresentation T.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.pullbackComp g U.ι).app F) hG
  exact (SheafOfModules.isFinitePresentation T.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.pullbackCongr hgi).app F) h₁

/-- Finite presentation on an open subscheme passes to a smaller open subscheme. -/
theorem restrict_le {X : Scheme.{u}} (F : X.Modules) {U V : X.Opens} (hVU : V ≤ U)
    (hU : (F.restrict U.ι).IsFinitePresentation) :
    (F.restrict V.ι).IsFinitePresentation := by
  have hrange : Set.range V.ι ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨y.1, hVU y.2⟩, rfl⟩
  exact (SheafOfModules.isFinitePresentation (V : Scheme).ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app F).symm
    (isFinitePresentation_pullback_of_range_subset F V.ι hrange hU)

/-- Finite presentation near a point is inherited by a pullback at any preimage of that
point. -/
theorem pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules) (y : X)
    (hF : IsFinitePresentationNear F (f y)) :
    IsFinitePresentationNear ((Scheme.Modules.pullback f).obj F) y := by
  obtain ⟨U, hyU, hU⟩ := hF
  refine ⟨f ⁻¹ᵁ U, hyU, ?_⟩
  set V : X.Opens := f ⁻¹ᵁ U
  have hrange : Set.range (V.ι ≫ f) ⊆ Set.range U.ι := by
    rintro _ ⟨y', rfl⟩
    exact ⟨⟨f y'.1, y'.2⟩, rfl⟩
  have hrestr : ((Scheme.Modules.pullback V.ι).obj
      ((Scheme.Modules.pullback f).obj F)).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (V : Scheme).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.pullbackComp V.ι f).app F).symm
      (isFinitePresentation_pullback_of_range_subset F (V.ι ≫ f) hrange hU)
  exact (SheafOfModules.isFinitePresentation (V : Scheme).ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app
      ((Scheme.Modules.pullback f).obj F)).symm hrestr

/-- **Finite presentation near a point descends along an étale morphism.** An étale morphism is
open and flat, so a neighbourhood of `y` on which `e^* F` is of finite presentation gives a
one-element fpqc covering of a neighbourhood of `e y`, and Stacks 05B0 descends finite
presentation along it. -/
theorem of_etale_pullback {X Y : Scheme.{u}} (e : Y ⟶ X) [Etale e] (y : Y) (x : X)
    (hey : e y = x) (F : X.Modules) [F.IsQuasicoherent]
    (hF : IsFinitePresentationNear ((Scheme.Modules.pullback e).obj F) y) :
    IsFinitePresentationNear F x := by
  obtain ⟨A, hyA, hA⟩ := hF
  obtain ⟨_, ⟨B₀, -, rfl⟩, hyB, hBA⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyA A.2
  let B : Y.Opens := B₀
  let eB : B.toScheme ⟶ X := B.ι ≫ e
  let V : X.Opens := ⟨Set.range eB, eB.isOpenMap.isOpen_range⟩
  have hrange : Set.range eB ⊆ Set.range V.ι := fun z hz ↦ ⟨⟨z, hz⟩, rfl⟩
  let g : B.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι eB hrange
  have hgi : g ≫ V.ι = eB := IsOpenImmersion.lift_fac V.ι eB hrange
  have hxV : x ∈ V := ⟨⟨y, hyB⟩, by
    change e (B.ι ⟨y, hyB⟩) = x
    rw [Scheme.Opens.ι_apply]
    exact hey⟩
  have : Etale (g ≫ V.ι) := by
    rw [hgi]
    exact inferInstanceAs (Etale (B.ι ≫ e))
  have : Etale g := Etale.of_comp g V.ι
  have : Scheme.JointlySurjective (Scheme.precoverage @Flat) :=
    @Scheme.instJointlySurjectivePrecoverage.{u} (@Flat.{u})
  let 𝒰₀ : (V : Scheme).Cover (Scheme.precoverage @Flat) :=
    Scheme.Cover.mkOfCovers (P := @Flat) PUnit (fun _ ↦ B.toScheme) (fun _ ↦ g)
      (fun v ↦ by
        obtain ⟨b, hb⟩ := v.2
        refine ⟨(), b, Subtype.ext ?_⟩
        change (g ≫ V.ι) b = v.1
        rw [hgi]
        exact hb)
      (fun _ ↦ inferInstance)
  have : QuasiCompactCover 𝒰₀.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (𝒰 := 𝒰₀) (fun _ ↦ g.isOpenMap)
  let 𝒰 : (V : Scheme).Cover Scheme.fpqcPrecoverage := by
    change (V : Scheme).Cover (Scheme.propQCPrecoverage @Flat)
    exact 𝒰₀.ofQuasiCompactCover
  have hG : ((Scheme.Modules.pullback g).obj (F.restrict V.ι)).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation B.toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.pullbackComp B.ι e).app F ≪≫
        ((Scheme.Modules.pullbackCongr hgi).app F).symm ≪≫
        ((Scheme.Modules.pullbackComp g V.ι).app F).symm ≪≫
        (Scheme.Modules.pullback g).mapIso
          ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app F).symm)
      ((SheafOfModules.isFinitePresentation B.toScheme.ringCatSheaf).prop_of_iso
        ((Scheme.Modules.restrictFunctorIsoPullback B.ι).app ((Scheme.Modules.pullback e).obj F))
        (restrict_le ((Scheme.Modules.pullback e).obj F) (show B ≤ A from hBA) hA))
  have : (F.restrict V.ι).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor V.ι F
  exact ⟨V, hxV, isFinitePresentation_of_pullback_fpqcCover (F.restrict V.ι) 𝒰
    fun _ ↦ hG⟩

/-- **Finite presentation near a point transfers across a finite morphism with a singleton
fibre.** For `f : X ⟶ Y` finite and of finite presentation whose fibre over `y` is `{x}`, a
quasi-coherent module is of finite presentation near `x` exactly when its direct image is of
finite presentation near `y`.

The fibre hypothesis supplies, through Stacks 05B8, a neighbourhood of `y` whose inverse image
lies in a prescribed neighbourhood of `x`; Stacks 05B4 compares finite presentation of a module
with that of its direct image along the restricted morphism. -/
theorem iff_pushforward_of_finite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (hf : FinitePresentation f) (F : X.Modules) [F.IsQuasicoherent]
    (x : X) (y : Y) (hxy : f x = y) (hfiber : f ⁻¹' {y} = {x}) :
    IsFinitePresentationNear F x ↔
      IsFinitePresentationNear ((Scheme.Modules.pushforward f).obj F) y := by
  have : LocallyOfFinitePresentation f := hf.1
  have : QuasiCompact f := hf.2.1
  have : QuasiSeparated f := hf.2.2
  constructor
  · rintro ⟨U, hxU, hU⟩
    obtain ⟨V, hyV, hpre⟩ := exists_open_preimage_le f x y hxy hfiber U hxU
    set W : X.Opens := f ⁻¹ᵁ V
    have : (F.restrict W.ι).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_restrictFunctor W.ι F
    have hfpV : FinitePresentation (f ∣_ V) :=
      FinitePresentation.mk inferInstance inferInstance inferInstance
    have hpush := (isFinitePresentation_iff_pushforward_isFinitePresentation (f ∣_ V) hfpV
      (F.restrict W.ι)).mp (restrict_le F hpre hU)
    exact ⟨V, hyV, (SheafOfModules.isFinitePresentation (V : Scheme).ringCatSheaf).prop_of_iso
      ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso f V).app F).symm hpush⟩
  · rintro ⟨V, hyV, hV⟩
    set W : X.Opens := f ⁻¹ᵁ V
    have : (F.restrict W.ι).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_restrictFunctor W.ι F
    have hfpV : FinitePresentation (f ∣_ V) :=
      FinitePresentation.mk inferInstance inferInstance inferInstance
    have hpush : ((Scheme.Modules.pushforward (f ∣_ V)).obj
        (F.restrict W.ι)).IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation (V : Scheme).ringCatSheaf).prop_of_iso
        ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso f V).app F) hV
    exact ⟨W, show f x ∈ V from hxy ▸ hyV,
      (isFinitePresentation_iff_pushforward_isFinitePresentation (f ∣_ V) hfpV
        (F.restrict W.ι)).mpr hpush⟩

end IsFinitePresentationNear

section Stalks

/-- Finite presentation of a stalk at a point only depends on the point. -/
private theorem finitePresentation_stalk_congr {X : Scheme.{u}} (F : X.Modules) {x y : X}
    (h : x = y) :
    Module.FinitePresentation (ToType (X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) ↔
      Module.FinitePresentation (ToType (X.presheaf.stalk y))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf y)) := by
  cases h
  rfl

/-- **Finite presentation of a stalk is unchanged by a flat pullback.** The stalk map of a flat
morphism is a flat local homomorphism of local rings and Stacks 0098 identifies the stalk of the
pullback with the base change, so finite presentation ascends by base change and descends by
`Stacks.StalkFiniteType.finitePresentation_stalk_of_flat`. -/
private theorem finitePresentation_stalk_pullback_iff {X' X : Scheme.{u}} (g : X' ⟶ X) [Flat g]
    (F : X.Modules) (x' : X') :
    Module.FinitePresentation (ToType (X.presheaf.stalk (g x')))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf (g x'))) ↔
      Module.FinitePresentation (ToType (X'.presheaf.stalk x'))
        (ToType (TopCat.Presheaf.stalk
          ((Scheme.Modules.pullback g).obj F).val.presheaf x')) := by
  refine ⟨fun _ => ?_, Stacks.StalkFiniteType.finitePresentation_stalk_of_flat g F x'⟩
  let _ : Algebra (ToType (X.presheaf.stalk (g x'))) (ToType (X'.presheaf.stalk x')) :=
    (g.stalkMap x').hom.toAlgebra
  have e : TensorProduct (ToType (X.presheaf.stalk (g x'))) (ToType (X'.presheaf.stalk x'))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf (g x')))
      ≃ₗ[ToType (X'.presheaf.stalk x')]
        ToType (TopCat.Presheaf.stalk ((Scheme.Modules.pullback g).obj F).val.presheaf x') :=
    Stacks.ModuleSkyscraper.pullbackStalkLinearEquiv g x' F
  exact (LinearEquiv.finitePresentation_iff e).mp inferInstance

/-- Finite presentation of a stalk is invariant under an isomorphism of modules. -/
private theorem finitePresentation_stalk_iff_of_iso {X : Scheme.{u}} {F G : X.Modules}
    (e : F ≅ G) (x : X) :
    Module.FinitePresentation (ToType (X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) ↔
      Module.FinitePresentation (ToType (X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk G.val.presheaf x)) :=
  LinearEquiv.finitePresentation_iff (moduleStalkLinearEquiv e x)

/-- **Finite presentation of a stalk transfers across a finite morphism with a singleton
fibre.** For `f : X ⟶ Y` finite and of finite presentation whose fibre over `f x` is `{x}`, the
stalk map `𝒪_{Y,f x} → 𝒪_{X,x}` is finite and of finite presentation (Stacks 05B8), so finite
presentation of `F_x` over the two rings agree (Stacks 0564); and `F_x` is the stalk of `f_* F`
at `f x` as an `𝒪_{Y,f x}`-module, again by Stacks 05B8. -/
private theorem finitePresentation_stalk_pushforward_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] (hf : FinitePresentation f) (F : X.Modules) [F.IsQuasicoherent] (x : X)
    (hfiber : f ⁻¹' ({f x} : Set Y) = {x}) :
    Module.FinitePresentation (ToType (X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) ↔
      Module.FinitePresentation (ToType (Y.presheaf.stalk (f x)))
        (ToType (TopCat.Presheaf.stalk
          ((Scheme.Modules.pushforward f).obj F).val.presheaf (f x))) := by
  let _ : Algebra (ToType (Y.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
    (f.stalkMap x).hom.toAlgebra
  let _ : Module (ToType (Y.presheaf.stalk (f x)))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
    Module.compHom _ (f.stalkMap x).hom
  have : IsScalarTower (ToType (Y.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hfin : Module.Finite (ToType (Y.presheaf.stalk (f x))) (ToType (X.presheaf.stalk x)) :=
    RingHom.finite_algebraMap.mp (finite_stalkMap_of_preimage_singleton f x hfiber)
  have hafp : Algebra.FinitePresentation (ToType (Y.presheaf.stalk (f x)))
      (ToType (X.presheaf.stalk x)) :=
    RingHom.finitePresentation_algebraMap.mp
      (finitePresentation_stalkMap_of_preimage_singleton f x hfiber hf)
  obtain ⟨e⟩ := stalk_isomorphic_pushforward_of_finite_singleton_fiber f x hfiber F
  exact (Module.FinitePresentation.restrictScalars_iff (ToType (Y.presheaf.stalk (f x)))
    (ToType (X.presheaf.stalk x)) (ToType (TopCat.Presheaf.stalk F.val.presheaf x))).symm.trans
      (LinearEquiv.finitePresentation_iff e.toLinearEquiv)

end Stalks

namespace ElementaryDevissage

variable {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {x : X}
  {hx : f.asFiber x ∈
    SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)}

/-- **Stacks Project, Tag 057T.** The finite morphism `π` of an elementary dévissage of a
morphism locally of finite presentation is of finite presentation.

The composite `Z ⟶ Y ⟶ V` equals `Z ⟶ U ⟶ X ⟶ S`, which is locally of finite presentation
because the closed immersion `i` is, `U ⟶ X` is étale and `f` is; the structure morphism
`V ⟶ S` is locally of finite type, so Stacks 02FV strips it off twice and leaves `π` locally of
finite presentation. A finite morphism is quasi-compact and quasi-separated, so `π` is of finite
presentation. -/
@[stacks 057T "finite presentation of π"]
theorem finitePresentation_π [LocallyOfFinitePresentation f] (D : ElementaryDevissage f F x hx) :
    FinitePresentation D.π := by
  have : LocallyOfFinitePresentation D.i := D.finitePresentation.locallyOfFinitePresentation
  have : Smooth D.h := D.smooth.smooth
  have : IsFinite D.π := D.finite_π
  have hcomp : (D.π ≫ D.h) ≫ D.V.toBase = (D.i ≫ D.U.toBase) ≫ f := by
    simp only [← D.commutes_closed, Category.assoc, D.commutes_base]
  have : LocallyOfFinitePresentation ((D.π ≫ D.h) ≫ D.V.toBase) := by
    rw [hcomp]
    infer_instance
  have : LocallyOfFinitePresentation (D.π ≫ D.h) :=
    locallyOfFinitePresentation_of_comp (D.π ≫ D.h) D.V.toBase
  have : LocallyOfFinitePresentation D.π := locallyOfFinitePresentation_of_comp D.π D.h
  exact FinitePresentation.mk inferInstance inferInstance inferInstance

/-- **Stacks Project, Tag 057T**, the equivalence of conditions (1) and (2). In an elementary
dévissage, `F` is of finite presentation near `x` exactly when the module `G` on the closed
subscheme is of finite presentation near `z`.

Finite presentation near `x` passes to the étale neighbourhood `U` and back by Stacks 01BQ and
Stacks 05B0; on `U` the module is `i_* G` by the dévissage isomorphism, and the closed immersion
`i` is finite with singleton fibre, so Stacks 05B4 and Stacks 05B8 exchange `i_* G` and `G`. -/
@[stacks 057T "equivalence of (1), (2) and (3)"]
theorem isFinitePresentationNear_iff_closed [F.IsQuasicoherent]
    (D : ElementaryDevissage f F x hx) :
    IsFinitePresentationNear F x ↔ IsFinitePresentationNear D.G D.z := by
  have : D.G.IsQuasicoherent := D.quasicoherent_G
  have : IsClosedImmersion D.i := D.closedImmersion
  have hbridge := IsFinitePresentationNear.iff_pushforward_of_finite D.i D.finitePresentation
    D.G D.z D.U.point D.point_closed D.preimage_i_singleton
  exact ⟨fun hF ↦ hbridge.mpr ((IsFinitePresentationNear.iff_of_iso D.sheafIso D.U.point).mpr
    (IsFinitePresentationNear.pullback D.U.toBase F D.U.point
      (by simpa [D.U.map_point] using hF))), fun hG ↦
    IsFinitePresentationNear.of_etale_pullback D.U.toBase D.U.point x D.U.map_point F
      ((IsFinitePresentationNear.iff_of_iso D.sheafIso D.U.point).mp (hbridge.mp hG))⟩

/-- **Stacks Project, Tag 057T**, the equivalence of conditions (2) and (3). In an elementary
dévissage of a morphism locally of finite presentation, the module `G` is of finite presentation
near `z` exactly when its direct image `π_* G` is of finite presentation near `π z`.

The morphism `π` is finite, of finite presentation by
`AlgebraicGeometry.ElementaryDevissage.finitePresentation_π`, and its fibre over `π z` is `{z}`,
so this is the transfer across a finite morphism with a singleton fibre. -/
@[stacks 057T "equivalence of (1), (2) and (3)"]
theorem isFinitePresentationNear_iff_pushforward [LocallyOfFinitePresentation f]
    (D : ElementaryDevissage f F x hx) :
    IsFinitePresentationNear D.G D.z ↔
      IsFinitePresentationNear ((Scheme.Modules.pushforward D.π).obj D.G) (D.π D.z) := by
  have : IsFinite D.π := D.finite_π
  have : D.G.IsQuasicoherent := D.quasicoherent_G
  exact IsFinitePresentationNear.iff_pushforward_of_finite D.π D.finitePresentation_π D.G D.z
    (D.π D.z) rfl D.preimage_π_singleton

/-- **Stacks Project, Tag 057T**, the equivalence of conditions (a) and (b). In an elementary
dévissage the stalk `F_x` is a finitely presented `𝒪_{X,x}`-module exactly when the stalk `G_z`
is a finitely presented `𝒪_{Z,z}`-module.

The étale morphism `U ⟶ X` is flat, so the stalk map `𝒪_{X,x} → 𝒪_{U,i z}` is a flat local
homomorphism and finite presentation of the stalk is unchanged by the pullback; the pullback of
`F` to `U` is `i_* G`; and the closed immersion `i` is finite, of finite presentation and has
singleton fibre, so Stacks 05B8 and Stacks 0564 exchange `(i_* G)_{i z}` and `G_z`. -/
@[stacks 057T "equivalence of (a), (b) and (c)"]
theorem finitePresentation_stalk_iff_closed (D : ElementaryDevissage f F x hx) :
    Module.FinitePresentation (ToType (X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) ↔
      Module.FinitePresentation (ToType (D.Z.presheaf.stalk D.z))
        (ToType (TopCat.Presheaf.stalk D.G.val.presheaf D.z)) := by
  have : D.G.IsQuasicoherent := D.quasicoherent_G
  have : IsClosedImmersion D.i := D.closedImmersion
  have hpoint : D.U.toBase (D.i D.z) = x := by rw [D.point_closed, D.U.map_point]
  have hfiber : D.i ⁻¹' ({D.i D.z} : Set D.U.scheme) = {D.z} := by
    rw [D.point_closed, D.preimage_i_singleton]
  exact ((finitePresentation_stalk_congr F hpoint.symm).trans
    ((finitePresentation_stalk_pullback_iff D.U.toBase F (D.i D.z)).trans
      (finitePresentation_stalk_iff_of_iso D.sheafIso (D.i D.z)).symm)).trans
    (finitePresentation_stalk_pushforward_iff D.i D.finitePresentation D.G D.z hfiber).symm

/-- **Stacks Project, Tag 057T**, the equivalence of conditions (b) and (c). In an elementary
dévissage of a morphism locally of finite presentation the stalk `G_z` is a finitely presented
`𝒪_{Z,z}`-module exactly when the stalk `(π_* G)_{π z}` is a finitely presented
`𝒪_{Y,π z}`-module.

The morphism `π` is finite, of finite presentation by
`AlgebraicGeometry.ElementaryDevissage.finitePresentation_π`, and its fibre over `π z` is `{z}`,
so this is the transfer of finite presentation of a stalk across a finite morphism with a
singleton fibre. -/
@[stacks 057T "equivalence of (a), (b) and (c)"]
theorem finitePresentation_stalk_iff_pushforward [LocallyOfFinitePresentation f]
    (D : ElementaryDevissage f F x hx) :
    Module.FinitePresentation (ToType (D.Z.presheaf.stalk D.z))
        (ToType (TopCat.Presheaf.stalk D.G.val.presheaf D.z)) ↔
      Module.FinitePresentation (ToType (D.Y.presheaf.stalk (D.π D.z)))
        (ToType (TopCat.Presheaf.stalk
          ((Scheme.Modules.pushforward D.π).obj D.G).val.presheaf (D.π D.z))) := by
  have : IsFinite D.π := D.finite_π
  have : D.G.IsQuasicoherent := D.quasicoherent_G
  exact finitePresentation_stalk_pushforward_iff D.π D.finitePresentation_π D.G D.z
    D.preimage_π_singleton

end ElementaryDevissage

end AlgebraicGeometry

end
