module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Units
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.Perfect.VanishingHigherDirectImagesBaseChange
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.Square

/-!
# Sections of the tensor powers under cohomology and base change

Let

```
Y' --q--> Y
|g'       |g
v         v
T' --h--> T
```

be a cartesian square with `T`, `T'` affine and `g` proper, flat and of finite presentation, and
let `ℳ` be an invertible `𝒪_Y`-module, `ℳ'` one on `Y'` with `ε : q^*ℳ ≅ ℳ'`.  If the higher
direct images of `ℳ^{⊗ n}` along `g` vanish, then the global sections of `(ℳ')^{⊗ n}` are the base
change of those of `ℳ^{⊗ n}`:

`Γ(T', 𝒪) ⊗_{Γ(T, 𝒪)} Γ(Y, ℳ^{⊗ n}) ≅ Γ(Y', (ℳ')^{⊗ n})`, `r ⊗ s ↦ r · q^*s`.

This is the module half of steps (c)–(d) of the proof of [Stacks, Tag 0D4F]: the identification
`A'_d = (A'_0)_d ⊗_{R'_0} R'` of the source, for the Noetherian model and its base change.  The
input is cohomology and base change in the form of [Stacks, Tag 0D4E] (2),
`isIso_baseChange_app_of_isZero_higherDirectImage` (in
`Stacks.AlgebraicGeometry.VanishingHigherDirectImages`),
together with the description of the sections of a pullback over affine opens,
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`.

## Main results

* `Stacks.AlgebraicGeometry.SectionRingBaseChange.exists_bijective_squarePieceMap_tmul`.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
* [Stacks Project, Tag 0D4E](https://stacks.math.columbia.edu/tag/0D4E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct
open Stacks.RingedSpace Stacks.SheafOfModules.TensorPower Stacks.TensorPowerPullback
open RingedSpaceModuleAdjunction
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.SectionRingBaseChange

-- The derived category used by [Stacks, Tag 0D4E], as in the files that state it.
attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The tensor powers of an invertible module -/

section Powers

variable {Y : Scheme.{u}} (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M] (n : ℤ)

/-- The tensor powers of an invertible module are invertible. -/
theorem isInvertibleModule_laurentPowers_piece :
    Stacks.Ample.IsInvertibleModule Y ((Stacks.RelativeAmple.laurentPowers M).piece n) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    Y.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct Y) _).mp
    (Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower Y.presheaf
      (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct Y) M n)

/-- The tensor powers of an invertible module are of finite presentation. -/
theorem isFinitePresentation_laurentPowers_piece :
    ((Stacks.RelativeAmple.laurentPowers M).piece n : Y.Modules).IsFinitePresentation :=
  Stacks.ModuleDescent.isFinitePresentation_of_isInvertible Y _
    (isInvertibleModule_laurentPowers_piece M n)

/-- The tensor powers of an invertible module are finite locally free (of rank one). -/
theorem isFiniteLocallyFree_laurentPowers_piece :
    _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf)
      ((Stacks.RelativeAmple.laurentPowers M).piece n) :=
  have := Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible Y _
    (isInvertibleModule_laurentPowers_piece M n)
  _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (R := Y.ringCatSheaf) _ 1

/-- The tensor powers of an invertible module are quasi-coherent. -/
theorem isQuasicoherent_laurentPowers_piece :
    ((Stacks.RelativeAmple.laurentPowers M).piece n : Y.Modules).IsQuasicoherent :=
  have := isInvertibleModule_laurentPowers_piece M n
  Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _

end Powers

/-! ### Cohomology and base change on global sections -/

section BaseChange

variable {Y' Y T' T : Scheme.{u}} (q : Y' ⟶ Y) (g : Y ⟶ T) (g' : Y' ⟶ T') (h : T' ⟶ T)
  [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
  (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
  (M' : Y'.Modules) [Stacks.Ample.IsInvertibleModule Y' M']
  (ε : (Scheme.Modules.pullback q).obj M ≅ M')

/-- The morphism of `𝒪_{T'}`-modules `h^* g_* ℳ^{⊗ n} ⟶ g'_* (ℳ')^{⊗ n}`: the base-change
morphism, followed by the comparison of the tensor powers and the transport along `ε`. -/
def baseChangePowHom (w : q ≫ g = g' ≫ h) (n : ℤ) :
    (Scheme.Modules.pullback h).obj
        ((Scheme.Modules.pushforward g).obj ((Stacks.RelativeAmple.laurentPowers M).piece n)) ⟶
      (Scheme.Modules.pushforward g').obj ((Stacks.RelativeAmple.laurentPowers M').piece n) :=
  haveI := isInvertible_tensorPower_of_isInvertibleModule Y M
  haveI := isInvertible_tensorPower_of_isInvertibleModule Y' M'
  haveI := isInvertible_tensorPower_of_isInvertibleModule Y' ((Scheme.Modules.pullback q).obj M)
  (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app
      ((Stacks.RelativeAmple.laurentPowers M).piece n) ≫
    (Scheme.Modules.pushforward g').map
      ((pullbackIntPowIso q.toLRSHom.toShHom M n).hom ≫
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε n).hom)

/-- The tensor-power invertibility facts needed to compare `ℳ`, `ℳ'` and `q^*ℳ`. -/
private theorem isInvertible_triple :
    Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (isSheafStructure Y.toRingedSpace) M ∧
    Stacks.SheafOfModules.IsInvertible Y'.toRingedSpace.presheaf
      (isSheafStructure Y'.toRingedSpace) M' ∧
    Stacks.SheafOfModules.IsInvertible Y'.toRingedSpace.presheaf
      (isSheafStructure Y'.toRingedSpace) ((Scheme.Modules.pullback q).obj M) :=
  ⟨isInvertible_tensorPower_of_isInvertibleModule Y M,
    isInvertible_tensorPower_of_isInvertibleModule Y' M',
    isInvertible_tensorPower_of_isInvertibleModule Y' _⟩

omit [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g'] in
/-- **On global sections, `baseChangePowHom` carries the pullback along `h` of a section to its
pullback along `q`**, read in the tensor power of `ℳ'`. -/
theorem baseChangePowHom_app_top (w : q ≫ g = g' ≫ h) (n : ℤ)
    (a : Γ((Scheme.Modules.pushforward g).obj ((Stacks.RelativeAmple.laurentPowers M).piece n),
      ⊤)) :
    (baseChangePowHom q g g' h M M' ε w n).app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app
          ((Scheme.Modules.pushforward g).obj
            ((Stacks.RelativeAmple.laurentPowers M).piece n))).val.app
            (op ⊤) a) =
      squarePieceMap q g g' h w M M' ε ⊤ ⊤ le_top n a := by
  obtain ⟨_, _, _⟩ := isInvertible_triple q M M'
  have h1 := ConcreteCategory.congr_hom
    (Stacks.AlgebraicGeometry.AffineBaseChange.app_top_unit_comp_baseChangeNatTrans w
      ((Stacks.RelativeAmple.laurentPowers M).piece n)) a
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app] at h1
  refine (congrArg (ConcreteCategory.hom (((pullbackIntPowIso q.toLRSHom.toShHom M n).hom ≫
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε n).hom).val.app
      (op (g' ⁻¹ᵁ ⊤)))) h1).trans ?_
  refine Eq.trans ?_ (sectionPull_apply q M M' ε n (g ⁻¹ᵁ ⊤) (g' ⁻¹ᵁ ⊤)
    (preimage_le_preimage q g g' h w ⊤ ⊤ le_top) a).symm
  rw [show (homOfLE (preimage_le_preimage q g g' h w ⊤ ⊤ le_top)).op = 𝟙 (op (g' ⁻¹ᵁ ⊤)) from
    Subsingleton.elim _ _]
  exact congrArg _ (PresheafOfModules.map_id_apply (tensorPower Y'.toRingedSpace.presheaf
    (isSheafStructure Y'.toRingedSpace) ((pullbackFunctor q.toLRSHom.toShHom).obj M) n).val
      (op (g' ⁻¹ᵁ ⊤)) _).symm

omit [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g'] in
/-- **Cohomology and base change for the tensor powers** ([Stacks, Tag 0D4E] (2)).  For a
cartesian square with `g` proper, flat and of finite presentation, if the higher direct images of
`ℳ^{⊗ n}` along `g` vanish then the base-change morphism `h^* g_* ℳ^{⊗ n} ⟶ g'_* (ℳ')^{⊗ n}` is an
isomorphism. -/
theorem isIso_baseChangePowHom (hpb : IsPullback q g' g h) [IsProper g] [Flat g]
    (hfp : _root_.AlgebraicGeometry.FinitePresentation g) (n : ℤ)
    (hvanish : ∀ i : ℤ, 0 < i →
      IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus i).obj
        ((Stacks.RelativeAmple.laurentPowers M).piece n))) :
    IsIso (baseChangePowHom q g g' h M M' ε hpb.w n) := by
  have := isFinitePresentation_laurentPowers_piece M n
  have := isQuasicoherent_laurentPowers_piece M n
  have := isFiniteLocallyFree_laurentPowers_piece M n
  have hflat :=
    _root_.AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree
      g ((Stacks.RelativeAmple.laurentPowers M).piece n)
  have hsupp : let : LocallyOfFinitePresentation g := hfp.locallyOfFinitePresentation
      ∃ Z : Closeds Y, IsProperOver g Z ∧
        _root_.SheafOfModules.supp ((Stacks.RelativeAmple.laurentPowers M).piece n) ⊆
          (Z : Set Y) := by
    let _ : LocallyOfFinitePresentation g := hfp.locallyOfFinitePresentation
    refine ⟨⊤, ?_, fun x _ => trivial⟩
    rw [isProperOver_iff_exists_isProper]
    exact ⟨⊥, Scheme.IdealSheafData.support_bot, inferInstance⟩
  have hβ :=
    VanishingHigherDirectImages.isIso_baseChange_app_of_isZero_higherDirectImage
      g h g' q hpb (congrArg (fun k : Y' ⟶ T => k.toLRSHom.toShHom) hpb.w) hfp
      ((Stacks.RelativeAmple.laurentPowers M).piece n) hflat hsupp hvanish
  obtain ⟨_, _, _⟩ := isInvertible_triple q M M'
  unfold baseChangePowHom
  let e₀ := (pullbackIntPowIso q.toLRSHom.toShHom M n) ≪≫
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε n)
  have i0 : @IsIso Y'.Modules _ _ _ e₀.hom := ⟨⟨e₀.inv, e₀.hom_inv_id, e₀.inv_hom_id⟩⟩
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hβ
    (Functor.map_isIso (Scheme.Modules.pushforward g') e₀.hom)

omit [QuasiCompact g'] [QuasiSeparated g'] in
/-- **Cohomology and base change on global sections.**  For a cartesian square of schemes with
affine base and target and `g` proper, flat and of finite presentation, if the higher direct
images of `ℳ^{⊗ n}` along `g` vanish then pulling back sections is the base change
`Γ(T', 𝒪) ⊗_{Γ(T, 𝒪)} Γ(Y, ℳ^{⊗ n}) ≅ Γ(Y', (ℳ')^{⊗ n})`. -/
theorem exists_bijective_squarePieceMap_tmul [IsAffine T] [IsAffine T']
    (hpb : IsPullback q g' g h) [IsProper g] [Flat g]
    (hfp : _root_.AlgebraicGeometry.FinitePresentation g) (n : ℤ)
    (hvanish : ∀ i : ℤ, 0 < i →
      IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus i).obj
        ((Stacks.RelativeAmple.laurentPowers M).piece n))) :
    ∃ G : (ModuleCat.extendScalars (h.appLE ⊤ ⊤ le_top).hom).obj (ModuleCat.of Γ(T, ⊤)
        Γ((Scheme.Modules.pushforward g).obj ((Stacks.RelativeAmple.laurentPowers M).piece n), ⊤))
          ⟶ ModuleCat.of Γ(T', ⊤) Γ((Scheme.Modules.pushforward g').obj
            ((Stacks.RelativeAmple.laurentPowers M').piece n), ⊤),
      Function.Bijective G ∧ ∀ (x : Γ((Scheme.Modules.pushforward g).obj
          ((Stacks.RelativeAmple.laurentPowers M).piece n), ⊤)),
        G ((1 : Γ(T', ⊤)) ⊗ₜ[Γ(T, ⊤), (h.appLE ⊤ ⊤ le_top).hom] x) =
          squarePieceMap q g g' h hpb.w M M' ε ⊤ ⊤ le_top n x := by
  have := isQuasicoherent_laurentPowers_piece M n
  have : ((Scheme.Modules.pushforward g).obj
      ((Stacks.RelativeAmple.laurentPowers M).piece n)).IsQuasicoherent :=
    AlgebraicGeometry.pushforward_isQuasicoherent g _
  have := isIso_baseChangePowHom q g g' h M M' ε hpb hfp n hvanish
  let E := AlgebraicGeometry.affinePullbackSectionsBaseChangeIso h
    ((Scheme.Modules.pushforward g).obj ((Stacks.RelativeAmple.laurentPowers M).piece n))
    (isAffineOpen_top T) (isAffineOpen_top T') le_top
  let B := (baseChangePowHom q g g' h M M' ε hpb.w n).app ⊤
  let Ψ := E.hom ≫ ModuleCat.ofHom
    (Scheme.Modules.sectionsLinearMap (baseChangePowHom q g g' h M M' ε hpb.w n) ⊤)
  refine ⟨Ψ, ?_, fun x => ?_⟩
  · exact (ConcreteCategory.bijective_of_isIso B).comp (ConcreteCategory.bijective_of_isIso E.hom)
  · have e2 := AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul h
      ((Scheme.Modules.pushforward g).obj ((Stacks.RelativeAmple.laurentPowers M).piece n))
      (isAffineOpen_top T) (isAffineOpen_top T') le_top x
    have e2' := e2.trans (Scheme.Modules.pullbackSection_top h
      ((Scheme.Modules.pushforward g).obj ((Stacks.RelativeAmple.laurentPowers M).piece n))
        le_top x)
    have e3 := baseChangePowHom_app_top q g g' h M M' ε hpb.w n x
    have e4 : Ψ ((1 : Γ(T', ⊤)) ⊗ₜ[Γ(T, ⊤), (h.appLE ⊤ ⊤ le_top).hom] x) =
        B (E.hom ((1 : Γ(T', ⊤)) ⊗ₜ[Γ(T, ⊤), (h.appLE ⊤ ⊤ le_top).hom] x)) := rfl
    have e5 := congrArg B e2'
    rw [e4, e5]
    exact e3

end BaseChange

end Stacks.AlgebraicGeometry.SectionRingBaseChange

end
