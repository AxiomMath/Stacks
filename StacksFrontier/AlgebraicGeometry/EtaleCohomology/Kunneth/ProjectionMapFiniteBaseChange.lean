module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.ProjectionMapPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsAbelianPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting

/-!
# The projection map of Tag 0F1J at a finite direct image of the structure sheaf

The last paragraph of the proof of [Stacks, Tag 0F1J] treats `E = π_*𝔽_ℓ` for a finite
`π : Z ⟶ X`. On the projection map of `h` this is
`isIso_projectionMap_pullback_pushforward_unit`: in the diagram of cartesian squares

```
Z  <-p_Z-- Z' <-hᵢ-- W
|π         |π'       |ρ
X  <-p---- X' <-h--- Y
|πX        |f'       |e
S  <-s---- S' <-g--- T
```

the projection map `p⁻¹Rπ_*Λ̲ ⊗^L Rh_*(e⁻¹F) ⟶ Rh_*(h⁻¹p⁻¹Rπ_*Λ̲ ⊗^L e⁻¹F)` is invertible for
`F ∈ D⁺(T_étale, ℤ/m)`, given derived base change for sheaves annihilated by `m` along
`X ⟶ S` and along `Z ⟶ S` (for `S = Spec K` and `m` invertible in `K` both are
[Stacks, Tag 0F1I]), and the projection formula of [Stacks, Tag 0F0G] on `D(-_étale, ℤ/m)`.

## The proof

The source's. `p⁻¹Rπ_*Λ̲ = Rπ'_*Λ̲` by base change along the integral `π`
(`isIso_baseChangeMap_app_of_isIntegralHom`). The projection map of `h` at `Rπ'_*Λ̲` is then
read through `isIso_projectionMap_pushforward`; of its inputs, the projection formula maps of
the finite `π'` and `ρ` are Tag 0F0G, the projection map of `hᵢ` at `p_Z⁻¹Λ̲ ≅ Λ̲` is
invertible, the base change map along the integral `π'` is again
`isIso_baseChangeMap_app_of_isIntegralHom`, and the base change map `π'⁻¹Rh_* ⟶ Rhᵢ_*ρ⁻¹` at
`e⁻¹F` is invertible because the base change maps of the square over `X` and of the composite
square over `Z` are: that is the pasting law of
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_comp`, read on `D(-_étale, ℤ/m)` by
`isIso_baseChangeMap_app_iff` (`isIso_baseChangeMap_app_pullback_of_comp`). The source uses
Tag 0F1I for `Z` at the same point.

## Main results

* `Stacks.EtaleCohomology.isIso_smallEtaleDerivedBaseChangeAb_app_of_comp` — cancellation in the
  pasting law along the base, for abelian sheaves.
* `Stacks.EtaleCohomology.EtaleCoefficients.isIso_baseChangeMap_app_pullback_of_comp` — the same
  on `D(-_étale, ℤ/m)`.
* `Stacks.EtaleCohomology.EtaleCoefficients.isIso_projectionMap_pullback_pushforward_unit` — the
  projection map at `p⁻¹Rπ_*Λ̲`. Not registered: derived base change along `X ⟶ S` and
  `Z ⟶ S`, and Tag 0F0G on `D(-_étale, ℤ/m)`, are explicit arguments.

## Implementation notes

An object of `D⁺` and its image in `D` are identified through `eqToIso` of a definitional
equation (`ι_obj_pullbackPlusObj`) rather than by `change`: the kernel checks the latter by
unfolding the derived inverse image.

The derived categories are the standard model, as for `smallEtaleDerivedBaseChangeAb`.

## References

* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
* [Stacks Project, Tag 0F1I](https://stacks.math.columbia.edu/tag/0F1I)
* [Stacks Project, Tag 0F0G](https://stacks.math.columbia.edu/tag/0F0G)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {S T X' X'' Y Y'' : Scheme.{u}}

/-- **Cancellation for the pasting law of the bounded below derived étale base change
comparison along the base.** For a commutative square `h ≫ f' = e ≫ g` and a second one
`h'' ≫ f'' = e'' ≫ h` extending its base along `f''`, if the comparisons of the first square
and of the composite extension are invertible at `Z`, then the comparison of the second square
is invertible at `Re⁻¹Z`. -/
theorem isIso_smallEtaleDerivedBaseChangeAb_app_of_comp (f' : X' ⟶ S) (f'' : X'' ⟶ X')
    (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T) (h'' : Y'' ⟶ X'') (e'' : Y'' ⟶ Y)
    (w : h ≫ f' = e ≫ g) (w' : h'' ≫ f'' = e'' ≫ h)
    (w'' : h'' ≫ (f'' ≫ f') = (e'' ≫ e) ≫ g)
    (Z : DerivedCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1}))
    (h₁ : IsIso ((smallEtaleDerivedBaseChangeAb f' g h e w).app Z))
    (h₃ : IsIso ((smallEtaleDerivedBaseChangeAb (f'' ≫ f') g h'' (e'' ≫ e) w'').app Z)) :
    IsIso ((smallEtaleDerivedBaseChangeAb f'' h h'' e'' w').app
      ((smallEtalePullbackAb e).rightDerivedFunctorPlus.obj Z)) := by
  have key := NatTrans.congr_app
    (smallEtaleDerivedBaseChangeAb_comp f' f'' g h e h'' e'' w w' w'') Z
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at key
  rw [key, isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff] at h₃
  exact h₃

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology.EtaleCoefficients

attribute [local instance] HasDerivedCategory.standard

open Stacks.EtaleCohomology.BaseChangeOverField

section Cancellation

variable (m : ℕ) {S' X' X'' T Y Y'' : Scheme.{u}}

/-- `e⁻¹` of a bounded below object of `D(T_étale, ℤ/m)`, as a bounded below object. -/
def pullbackPlusObj (e : Y ⟶ T)
    (K : DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) T).O))) :
    DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) Y).O)) :=
  ⟨(pullback (ULift.{u + 1} (ZMod m)) e).obj (DerivedCategory.Plus.ι.obj K), by
    obtain ⟨b, hb⟩ := K.property
    exact ⟨b, isGE_pullback_obj _ e _ b hb⟩⟩

/-- The underlying complex of abelian sheaves of `e⁻¹K` is the abelian `e⁻¹` of that of `K`. -/
def forgetDerivedPlusPullbackPlusObjIso (e : Y ⟶ T)
    (K : DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) T).O))) :
    (forgetDerivedPlus (ULift.{u + 1} (ZMod m)) Y).obj (pullbackPlusObj m e K) ≅
      (smallEtalePullbackAb e).rightDerivedFunctorPlus.obj
        ((forgetDerivedPlus (ULift.{u + 1} (ZMod m)) T).obj K) :=
  DerivedCategory.Plus.ι.preimageIso ((pullbackForgetPlusIso m e).app K)

/-- The image of `pullbackPlusObj m e K` in `D(Y_étale, ℤ/m)` is `e⁻¹` of the image of `K`. -/
theorem ι_obj_pullbackPlusObj (e : Y ⟶ T)
    (K : DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) T).O))) :
    DerivedCategory.Plus.ι.obj (pullbackPlusObj m e K) =
      (pullback (ULift.{u + 1} (ZMod m)) e).obj (DerivedCategory.Plus.ι.obj K) :=
  rfl

/-- For a commutative square `h ≫ f' = e ≫ g` and a second one `hi ≫ π' = ρ ≫ h` extending its
base along `π'`, if the abelian derived base change comparisons of the first square and of the
composite square are invertible at the underlying complex of abelian sheaves of a bounded below
`K`, then the comparison of the second square is invertible at the underlying complex of
abelian sheaves of `e⁻¹K`. -/
theorem isIso_smallEtaleDerivedBaseChangeAb_app_forgetDerivedPlus_pullbackPlusObj
    (f' : X' ⟶ S') (π' : X'' ⟶ X')
    (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (hi : Y'' ⟶ X'') (ρ : Y'' ⟶ Y)
    (w : h ≫ f' = e ≫ g) (w' : hi ≫ π' = ρ ≫ h) (w'' : hi ≫ (π' ≫ f') = (ρ ≫ e) ≫ g)
    (K : DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) T).O)))
    (h₁ : IsIso ((smallEtaleDerivedBaseChangeAb f' g h e w).app
      ((forgetDerivedPlus (ULift.{u + 1} (ZMod m)) T).obj K)))
    (h₃ : IsIso ((smallEtaleDerivedBaseChangeAb (π' ≫ f') g hi (ρ ≫ e) w'').app
      ((forgetDerivedPlus (ULift.{u + 1} (ZMod m)) T).obj K))) :
    IsIso ((smallEtaleDerivedBaseChangeAb π' h hi ρ w').app
      ((forgetDerivedPlus (ULift.{u + 1} (ZMod m)) Y).obj (pullbackPlusObj m e K))) :=
  (NatTrans.isIso_app_iff_of_iso (smallEtaleDerivedBaseChangeAb π' h hi ρ w')
      (X := (forgetDerivedPlus (ULift.{u + 1} (ZMod m)) Y).obj (pullbackPlusObj m e K))
      (Y := (smallEtalePullbackAb e).rightDerivedFunctorPlus.obj
        ((forgetDerivedPlus (ULift.{u + 1} (ZMod m)) T).obj K))
      (forgetDerivedPlusPullbackPlusObjIso m e K)).2
    (isIso_smallEtaleDerivedBaseChangeAb_app_of_comp f' π' g h e hi ρ w w' w'' _ h₁ h₃)

/-- `isIso_baseChangeMap_app_pullback_of_comp`, at `e⁻¹K` read as a bounded below object. -/
theorem isIso_baseChangeMap_app_ι_pullbackPlusObj_of_comp (f' : X' ⟶ S') (π' : X'' ⟶ X')
    (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (hi : Y'' ⟶ X'') (ρ : Y'' ⟶ Y)
    (w : h ≫ f' = e ≫ g) (w' : hi ≫ π' = ρ ≫ h) (w'' : hi ≫ (π' ≫ f') = (ρ ≫ e) ≫ g)
    (K : DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) T).O)))
    (h₁ : IsIso ((baseChangeMap (ULift.{u + 1} (ZMod m)) f' g h e w).app
      (DerivedCategory.Plus.ι.obj K)))
    (h₃ : IsIso ((baseChangeMap (ULift.{u + 1} (ZMod m)) (π' ≫ f') g hi (ρ ≫ e) w'').app
      (DerivedCategory.Plus.ι.obj K))) :
    IsIso ((baseChangeMap (ULift.{u + 1} (ZMod m)) π' h hi ρ w').app
      (DerivedCategory.Plus.ι.obj (pullbackPlusObj m e K))) := by
  rw [isIso_baseChangeMap_app_iff] at h₁ h₃
  rw [isIso_baseChangeMap_app_iff]
  exact isIso_smallEtaleDerivedBaseChangeAb_app_forgetDerivedPlus_pullbackPlusObj m f' π' g h e hi
    ρ w w' w'' K h₁ h₃

/-- **Cancellation of base change maps along the base, on `D(-_étale, ℤ/m)`.** For a commutative
square `h ≫ f' = e ≫ g` and a second one `hᵢ ≫ π' = ρ ≫ h` extending its base along `π'`, if
the base change maps of the first square and of the composite extension are invertible at a
bounded below `K`, then the base change map `π'⁻¹Rh_* ⟶ Rhᵢ_*ρ⁻¹` of the second square is
invertible at `e⁻¹K`. On the underlying complexes of abelian sheaves this is the pasting law
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_comp`. -/
theorem isIso_baseChangeMap_app_pullback_of_comp (f' : X' ⟶ S') (π' : X'' ⟶ X')
    (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (hi : Y'' ⟶ X'') (ρ : Y'' ⟶ Y)
    (w : h ≫ f' = e ≫ g) (w' : hi ≫ π' = ρ ≫ h) (w'' : hi ≫ (π' ≫ f') = (ρ ≫ e) ≫ g)
    (K : DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) T).O)))
    (h₁ : IsIso ((baseChangeMap (ULift.{u + 1} (ZMod m)) f' g h e w).app
      (DerivedCategory.Plus.ι.obj K)))
    (h₃ : IsIso ((baseChangeMap (ULift.{u + 1} (ZMod m)) (π' ≫ f') g hi (ρ ≫ e) w'').app
      (DerivedCategory.Plus.ι.obj K))) :
    IsIso ((baseChangeMap (ULift.{u + 1} (ZMod m)) π' h hi ρ w').app
      ((pullback (ULift.{u + 1} (ZMod m)) e).obj (DerivedCategory.Plus.ι.obj K))) :=
  (NatTrans.isIso_app_iff_of_iso (baseChangeMap (ULift.{u + 1} (ZMod m)) π' h hi ρ w')
    (X := DerivedCategory.Plus.ι.obj (pullbackPlusObj m e K))
    (Y := (pullback (ULift.{u + 1} (ZMod m)) e).obj (DerivedCategory.Plus.ι.obj K))
    (eqToIso (ι_obj_pullbackPlusObj m e K))).1
    (isIso_baseChangeMap_app_ι_pullbackPlusObj_of_comp m f' π' g h e hi ρ w w' w'' K h₁ h₃)

end Cancellation

section Finite

variable (m : ℕ) {S X X' S' T Y Z Z' W : Scheme.{u}}

/-- The structure sheaf of `D(Z_étale, ℤ/m)`, as a bounded below object. -/
abbrev unitPlus (Z : Scheme.{u}) :
    DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) Z).O)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj (SheafOfModules.unit _)

/-- `ι` of `unitPlus` is the structure sheaf. -/
def ιUnitPlusIso (Z : Scheme.{u}) :
    DerivedCategory.Plus.ι.obj (unitPlus m Z) ≅ unit (ULift.{u + 1} (ZMod m)) Z :=
  (DerivedCategory.Plus.singleFunctorιIso (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (ULift.{u + 1} (ZMod m)) Z).O)) 0).app
      (SheafOfModules.unit _)

/-- In the setting of `isIso_projectionMap_pullback_pushforward_unit`, the base change map
`π'⁻¹Rh_* ⟶ Rhᵢ_*ρ⁻¹` is invertible at `e⁻¹F`. -/
theorem isIso_baseChangeMap_app_pullback_of_derivedBaseChangeHolds (πX : X ⟶ S) (s : S' ⟶ S)
    (p : X' ⟶ X) (f' : X' ⟶ S') (hX' : IsPullback p f' πX s) (g : T ⟶ S') (h : Y ⟶ X')
    (e : Y ⟶ T) (hY : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g] (π : Z ⟶ X)
    (pZ : Z' ⟶ Z) (π' : Z' ⟶ X') (hZ' : IsPullback pZ π' π p) (hi : W ⟶ Z') (ρ : W ⟶ Y)
    (hW : IsPullback hi ρ π' h) (hBC : DerivedBaseChangeHolds πX m)
    (hBCZ : DerivedBaseChangeHolds (π ≫ πX) m)
    (F : DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) T).O))) :
    IsIso ((baseChangeMap (ULift.{u + 1} (ZMod m)) π' h hi ρ hW.w).app
      ((pullback (ULift.{u + 1} (ZMod m)) e).obj (DerivedCategory.Plus.ι.obj F))) :=
  isIso_baseChangeMap_app_pullback_of_comp m f' π' g h e hi ρ hY.w hW.w (hW.paste_vert hY).w F
    (isIso_baseChangeMap_app_of_derivedBaseChangeHolds m πX hBC s p f' hX' g h e hY F)
    (isIso_baseChangeMap_app_of_derivedBaseChangeHolds m (π ≫ πX) hBCZ s pZ (π' ≫ f')
      (hZ'.paste_vert hX') g hi (ρ ≫ e) (hW.paste_vert hY) F)

/-- The base change map `h⁻¹Rπ'_* ⟶ Rρ_*hᵢ⁻¹` along the integral `π'` is invertible at
`p_Z⁻¹Λ̲`. -/
theorem isIso_baseChangeMap_app_pullback_unitPlus {X' Y Z Z' W : Scheme.{u}} (h : Y ⟶ X')
    (π' : Z' ⟶ X') [IsIntegralHom π'] (pZ : Z' ⟶ Z) (hi : W ⟶ Z') (ρ : W ⟶ Y)
    (hW : IsPullback hi ρ π' h) :
    IsIso ((baseChangeMap (ULift.{u + 1} (ZMod m)) h π' ρ hi hW.flip.w).app
      ((pullback (ULift.{u + 1} (ZMod m)) pZ).obj (DerivedCategory.Plus.ι.obj (unitPlus m Z)))) :=
  (NatTrans.isIso_app_iff_of_iso (baseChangeMap (ULift.{u + 1} (ZMod m)) h π' ρ hi hW.flip.w)
      (X := DerivedCategory.Plus.ι.obj (pullbackPlusObj m pZ (unitPlus m Z)))
      (Y := (pullback (ULift.{u + 1} (ZMod m)) pZ).obj (DerivedCategory.Plus.ι.obj (unitPlus m Z)))
      (eqToIso (ι_obj_pullbackPlusObj m pZ (unitPlus m Z)))).1
    (isIso_baseChangeMap_app_of_isIntegralHom m h π' ρ hi hW.flip _)

/-- The projection map of `hᵢ` at `p_Z⁻¹Λ̲`. -/
theorem isIso_projectionMap_pullback_unitPlus {Z Z' W : Scheme.{u}} (pZ : Z' ⟶ Z) (hi : W ⟶ Z')
    (B : DerivedModules (ULift.{u + 1} (ZMod m)) W) :
    IsIso (projectionMap (ULift.{u + 1} (ZMod m)) hi
      ((pullback (ULift.{u + 1} (ZMod m)) pZ).obj (DerivedCategory.Plus.ι.obj (unitPlus m Z))) B) :=
  isIso_projectionMap_of_iso_unit _ hi
    ((pullback (ULift.{u + 1} (ZMod m)) pZ).mapIso (ιUnitPlusIso m Z) ≪≫ pullbackUnitIso _ pZ) B

/-- The projection map of `h` at `Rπ'_*E` is invertible as soon as `E` has invertible projection
maps along `hᵢ` and an invertible base change map `h⁻¹Rπ'_* ⟶ Rρ_*hᵢ⁻¹`. -/
private theorem isIso_projectionMap_pushforward_of_isIso_projectionMap (πX : X ⟶ S) (s : S' ⟶ S)
    (p : X' ⟶ X) (f' : X' ⟶ S') (hX' : IsPullback p f' πX s) (g : T ⟶ S') (h : Y ⟶ X')
    (e : Y ⟶ T) (hY : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g] (π : Z ⟶ X)
    [IsFinite π] (pZ : Z' ⟶ Z) (π' : Z' ⟶ X') (hZ' : IsPullback pZ π' π p) (hi : W ⟶ Z')
    (ρ : W ⟶ Y) (hW : IsPullback hi ρ π' h) (hBC : DerivedBaseChangeHolds πX m)
    (hBCZ : DerivedBaseChangeHolds (π ≫ πX) m)
    (hProjectionFormula : ∀ {A B : Scheme.{u}} (f : A ⟶ B) [IsProper f]
      (E : DerivedModules (ULift.{u + 1} (ZMod m)) A)
      (K : DerivedModules (ULift.{u + 1} (ZMod m)) B),
      IsIso (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap
        (ringedToposHom (ULift.{u + 1} (ZMod m)) f)
        (isMorphismOfSites_ringedToposHom (ULift.{u + 1} (ZMod m)) f) E K))
    (F : DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) T).O)))
    (E : DerivedModules (ULift.{u + 1} (ZMod m)) Z')
    (hE : ∀ B, IsIso (projectionMap (ULift.{u + 1} (ZMod m)) hi E B))
    (hE' : IsIso ((baseChangeMap (ULift.{u + 1} (ZMod m)) h π' ρ hi hW.flip.w).app E)) :
    IsIso (projectionMap (ULift.{u + 1} (ZMod m)) h
      ((pushforward (ULift.{u + 1} (ZMod m)) π').obj E)
      ((pullback (ULift.{u + 1} (ZMod m)) e).obj (DerivedCategory.Plus.ι.obj F))) := by
  have : IsFinite π' := MorphismProperty.of_isPullback (P := @IsFinite) hZ' ‹_›
  have : IsFinite ρ := MorphismProperty.of_isPullback (P := @IsFinite) hW ‹_›
  exact isIso_projectionMap_pushforward _ π' h hi ρ _ _ hW.w hW.flip.w
    (hProjectionFormula π' _ _)
    (isIso_baseChangeMap_app_pullback_of_derivedBaseChangeHolds m πX s p f' hX' g h e hY π pZ π'
      hZ' hi ρ hW hBC hBCZ F)
    (hE _) hE' (hProjectionFormula ρ _ _)

/-- `p⁻¹Rπ_*Λ̲ ≅ Rπ'_*p_Z⁻¹Λ̲` by base change along the integral `π`. -/
private theorem nonempty_pullbackPushforwardUnitIso (p : X' ⟶ X) (π : Z ⟶ X) [IsIntegralHom π]
    (pZ : Z' ⟶ Z) (π' : Z' ⟶ X') (hZ' : IsPullback pZ π' π p) :
    Nonempty ((pullback (ULift.{u + 1} (ZMod m)) p).obj
        ((pushforward (ULift.{u + 1} (ZMod m)) π).obj (unit (ULift.{u + 1} (ZMod m)) Z)) ≅
      (pushforward (ULift.{u + 1} (ZMod m)) π').obj ((pullback (ULift.{u + 1} (ZMod m)) pZ).obj
        (DerivedCategory.Plus.ι.obj (unitPlus m Z)))) := by
  have := isIso_baseChangeMap_app_of_isIntegralHom m p π π' pZ hZ'.flip (unitPlus m Z)
  exact ⟨(pullback (ULift.{u + 1} (ZMod m)) p).mapIso
      ((pushforward (ULift.{u + 1} (ZMod m)) π).mapIso (ιUnitPlusIso m Z).symm) ≪≫
    asIso ((baseChangeMap (ULift.{u + 1} (ZMod m)) p π π' pZ hZ'.flip.w).app
      (DerivedCategory.Plus.ι.obj (unitPlus m Z)))⟩

/-- The core of `isIso_projectionMap_pullback_pushforward_unit`: the projection map of `h` at
`Rπ'_*p_Z⁻¹Λ̲`. -/
theorem isIso_projectionMap_pushforward_pullback_unitPlus (πX : X ⟶ S) (s : S' ⟶ S) (p : X' ⟶ X)
    (f' : X' ⟶ S') (hX' : IsPullback p f' πX s) (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
    (hY : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g] (π : Z ⟶ X) [IsFinite π]
    (pZ : Z' ⟶ Z) (π' : Z' ⟶ X') (hZ' : IsPullback pZ π' π p) (hi : W ⟶ Z') (ρ : W ⟶ Y)
    (hW : IsPullback hi ρ π' h) (hBC : DerivedBaseChangeHolds πX m)
    (hBCZ : DerivedBaseChangeHolds (π ≫ πX) m)
    (hProjectionFormula : ∀ {A B : Scheme.{u}} (f : A ⟶ B) [IsProper f]
      (E : DerivedModules (ULift.{u + 1} (ZMod m)) A)
      (K : DerivedModules (ULift.{u + 1} (ZMod m)) B),
      IsIso (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap
        (ringedToposHom (ULift.{u + 1} (ZMod m)) f)
        (isMorphismOfSites_ringedToposHom (ULift.{u + 1} (ZMod m)) f) E K))
    (F : DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) T).O))) :
    IsIso (projectionMap (ULift.{u + 1} (ZMod m)) h
      ((pushforward (ULift.{u + 1} (ZMod m)) π').obj ((pullback (ULift.{u + 1} (ZMod m)) pZ).obj
        (DerivedCategory.Plus.ι.obj (unitPlus m Z))))
      ((pullback (ULift.{u + 1} (ZMod m)) e).obj (DerivedCategory.Plus.ι.obj F))) := by
  have : IsFinite π' := MorphismProperty.of_isPullback (P := @IsFinite) hZ' ‹_›
  exact isIso_projectionMap_pushforward_of_isIso_projectionMap m πX s p f' hX' g h e hY π pZ π'
    hZ' hi ρ hW hBC hBCZ hProjectionFormula F _ (isIso_projectionMap_pullback_unitPlus m pZ hi)
    (isIso_baseChangeMap_app_pullback_unitPlus m h π' pZ hi ρ hW)

/-- **The projection map of `h` at the inverse image of a finite direct image of the structure
sheaf.** In the setting of [Stacks, Tag 0F1J] over an arbitrary base `S` — cartesian squares

```
Z  <-p_Z-- Z' <-hᵢ-- W
|π         |π'       |ρ
X  <-p---- X' <-h--- Y
|πX        |f'       |e
S  <-s---- S' <-g--- T
```

with `π` finite and `g` quasi-compact and quasi-separated — suppose derived base change holds
for sheaves annihilated by `m` along `X ⟶ S` and along `Z ⟶ S`, and the projection formula of
[Stacks, Tag 0F0G] holds on `D(-_étale, ℤ/m)` for proper morphisms (`hProjectionFormula`). Then
for every `F ∈ D⁺(T_étale, ℤ/m)` the projection map of `h`

`p⁻¹Rπ_*Λ̲ ⊗^L Rh_*(e⁻¹F) ⟶ Rh_*(h⁻¹p⁻¹Rπ_*Λ̲ ⊗^L e⁻¹F)`

is an isomorphism. This is the last paragraph of the source's proof of Tag 0F1J, read on the
projection map: `p⁻¹Rπ_*Λ̲ = Rπ'_*Λ̲` by base change along the integral `π`, and the projection
map of `h` at `Rπ'_*Λ̲` is `Rπ'_*` of the base change map `π'⁻¹Rh_* ⟶ Rhᵢ_*ρ⁻¹` at `e⁻¹F`
(`isIso_projectionMap_pushforward`), which is invertible because the base change maps of the
square over `X` and of the composite square over `Z` are
(`isIso_baseChangeMap_app_pullback_of_comp`). -/
theorem isIso_projectionMap_pullback_pushforward_unit (πX : X ⟶ S) (s : S' ⟶ S) (p : X' ⟶ X)
    (f' : X' ⟶ S') (hX' : IsPullback p f' πX s) (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
    (hY : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g] (π : Z ⟶ X) [IsFinite π]
    (pZ : Z' ⟶ Z) (π' : Z' ⟶ X') (hZ' : IsPullback pZ π' π p) (hi : W ⟶ Z') (ρ : W ⟶ Y)
    (hW : IsPullback hi ρ π' h) (hBC : DerivedBaseChangeHolds πX m)
    (hBCZ : DerivedBaseChangeHolds (π ≫ πX) m)
    (hProjectionFormula : ∀ {A B : Scheme.{u}} (f : A ⟶ B) [IsProper f]
      (E : DerivedModules (ULift.{u + 1} (ZMod m)) A)
      (K : DerivedModules (ULift.{u + 1} (ZMod m)) B),
      IsIso (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap
        (ringedToposHom (ULift.{u + 1} (ZMod m)) f)
        (isMorphismOfSites_ringedToposHom (ULift.{u + 1} (ZMod m)) f) E K))
    (F : DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) T).O))) :
    IsIso (projectionMap (ULift.{u + 1} (ZMod m)) h
      ((pullback (ULift.{u + 1} (ZMod m)) p).obj
        ((pushforward (ULift.{u + 1} (ZMod m)) π).obj (unit (ULift.{u + 1} (ZMod m)) Z)))
      ((pullback (ULift.{u + 1} (ZMod m)) e).obj (DerivedCategory.Plus.ι.obj F))) := by
  obtain ⟨a⟩ := nonempty_pullbackPushforwardUnitIso m p π pZ π' hZ'
  exact (isIso_projectionMap_iff_of_iso _ h a _).2
    (isIso_projectionMap_pushforward_pullback_unitPlus m πX s p f' hX' g h e hY π pZ π' hZ' hi ρ
      hW hBC hBCZ hProjectionFormula F)

/-! ### At every shift -/

/-- `p_Z⁻¹Λ̲[0]⟦k⟧`, as a bounded below object. -/
abbrev pullbackUnitShiftPlus {Z Z' : Scheme.{u}} (pZ : Z' ⟶ Z) (k : ℤ) :
    DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) Z').O)) :=
  (pullbackPlusObj m pZ (unitPlus m Z))⟦k⟧

/-- `p_Z⁻¹Λ̲[0]⟦k⟧ ≅ Λ̲[0]⟦k⟧`. -/
def ιPullbackUnitShiftPlusIso {Z Z' : Scheme.{u}} (pZ : Z' ⟶ Z) (k : ℤ) :
    DerivedCategory.Plus.ι.obj (pullbackUnitShiftPlus m pZ k) ≅
      (unit (ULift.{u + 1} (ZMod m)) Z')⟦k⟧ :=
  (DerivedCategory.Plus.ι.commShiftIso k).app _ ≪≫
    (shiftFunctor _ k).mapIso (eqToIso (ι_obj_pullbackPlusObj m pZ (unitPlus m Z)) ≪≫
      (pullback (ULift.{u + 1} (ZMod m)) pZ).mapIso (ιUnitPlusIso m Z) ≪≫ pullbackUnitIso _ pZ)

/-- `isIso_projectionMap_pushforward_pullback_unitPlus` at every shift of `p_Z⁻¹Λ̲`. -/
theorem isIso_projectionMap_pushforward_pullbackUnitShiftPlus (πX : X ⟶ S) (s : S' ⟶ S)
    (p : X' ⟶ X) (f' : X' ⟶ S') (hX' : IsPullback p f' πX s) (g : T ⟶ S') (h : Y ⟶ X')
    (e : Y ⟶ T) (hY : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g] (π : Z ⟶ X)
    [IsFinite π] (pZ : Z' ⟶ Z) (π' : Z' ⟶ X') (hZ' : IsPullback pZ π' π p) (hi : W ⟶ Z')
    (ρ : W ⟶ Y) (hW : IsPullback hi ρ π' h) (hBC : DerivedBaseChangeHolds πX m)
    (hBCZ : DerivedBaseChangeHolds (π ≫ πX) m)
    (hProjectionFormula : ∀ {A B : Scheme.{u}} (f : A ⟶ B) [IsProper f]
      (E : DerivedModules (ULift.{u + 1} (ZMod m)) A)
      (K : DerivedModules (ULift.{u + 1} (ZMod m)) B),
      IsIso (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap
        (ringedToposHom (ULift.{u + 1} (ZMod m)) f)
        (isMorphismOfSites_ringedToposHom (ULift.{u + 1} (ZMod m)) f) E K))
    (F : DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) T).O))) (k : ℤ) :
    IsIso (projectionMap (ULift.{u + 1} (ZMod m)) h
      ((pushforward (ULift.{u + 1} (ZMod m)) π').obj
        (DerivedCategory.Plus.ι.obj (pullbackUnitShiftPlus m pZ k)))
      ((pullback (ULift.{u + 1} (ZMod m)) e).obj (DerivedCategory.Plus.ι.obj F))) := by
  have : IsFinite π' := MorphismProperty.of_isPullback (P := @IsFinite) hZ' ‹_›
  exact isIso_projectionMap_pushforward_of_isIso_projectionMap m πX s p f' hX' g h e hY π pZ π'
    hZ' hi ρ hW hBC hBCZ hProjectionFormula F _
    (isIso_projectionMap_of_iso_unitShift _ hi (ιPullbackUnitShiftPlusIso m pZ k))
    (isIso_baseChangeMap_app_of_isIntegralHom m h π' ρ hi hW.flip _)

/-- **`isIso_projectionMap_pullback_pushforward_unit` at every shift**: the projection map of
`h` at `(p⁻¹Rπ_*Λ̲)⟦k⟧` and `e⁻¹F` is an isomorphism, for every `k`. -/
theorem isIso_projectionMap_shift_pullback_pushforward_unit (πX : X ⟶ S) (s : S' ⟶ S)
    (p : X' ⟶ X) (f' : X' ⟶ S') (hX' : IsPullback p f' πX s) (g : T ⟶ S') (h : Y ⟶ X')
    (e : Y ⟶ T) (hY : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g] (π : Z ⟶ X)
    [IsFinite π] (pZ : Z' ⟶ Z) (π' : Z' ⟶ X') (hZ' : IsPullback pZ π' π p) (hi : W ⟶ Z')
    (ρ : W ⟶ Y) (hW : IsPullback hi ρ π' h) (hBC : DerivedBaseChangeHolds πX m)
    (hBCZ : DerivedBaseChangeHolds (π ≫ πX) m)
    (hProjectionFormula : ∀ {A B : Scheme.{u}} (f : A ⟶ B) [IsProper f]
      (E : DerivedModules (ULift.{u + 1} (ZMod m)) A)
      (K : DerivedModules (ULift.{u + 1} (ZMod m)) B),
      IsIso (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap
        (ringedToposHom (ULift.{u + 1} (ZMod m)) f)
        (isMorphismOfSites_ringedToposHom (ULift.{u + 1} (ZMod m)) f) E K))
    (F : DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) T).O))) (k : ℤ) :
    IsIso (projectionMap (ULift.{u + 1} (ZMod m)) h
      (((pullback (ULift.{u + 1} (ZMod m)) p).obj
        ((pushforward (ULift.{u + 1} (ZMod m)) π).obj (unit (ULift.{u + 1} (ZMod m)) Z)))⟦k⟧)
      ((pullback (ULift.{u + 1} (ZMod m)) e).obj (DerivedCategory.Plus.ι.obj F))) := by
  obtain ⟨a⟩ := nonempty_pullbackPushforwardUnitIso m p π pZ π' hZ'
  let c : ((pullback (ULift.{u + 1} (ZMod m)) pZ).obj
        (DerivedCategory.Plus.ι.obj (unitPlus m Z)))⟦k⟧ ≅
      DerivedCategory.Plus.ι.obj (pullbackUnitShiftPlus m pZ k) :=
    (shiftFunctor _ k).mapIso (eqToIso (ι_obj_pullbackPlusObj m pZ (unitPlus m Z))).symm ≪≫
      ((DerivedCategory.Plus.ι.commShiftIso k).app _).symm
  let b := (shiftFunctor _ k).mapIso a ≪≫
    ((pushforward (ULift.{u + 1} (ZMod m)) π').commShiftIso k).symm.app _ ≪≫
    (pushforward (ULift.{u + 1} (ZMod m)) π').mapIso c
  exact (isIso_projectionMap_iff_of_iso _ h b _).2
    (isIso_projectionMap_pushforward_pullbackUnitShiftPlus m πX s p f' hX' g h e hY π pZ π' hZ'
      hi ρ hW hBC hBCZ hProjectionFormula F k)

end Finite

end Stacks.EtaleCohomology.EtaleCoefficients

end
