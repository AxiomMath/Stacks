module

public import StacksFrontier.AlgebraicGeometry.Conormal.AffineGenerators
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalSheaf

/-!
# The affine characterization of the induced morphism of conormal sheaves (Stacks 04F7)

Let
```
Z --i--→ Z'
|        |
f        k
↓        ↓
W --j--→ W'
```
be a commutative square of schemes with `i` and `j` immersions. The square induces a morphism
`f^* 𝒞_{W/W'} ⟶ 𝒞_{Z/Z'}` of conormal sheaves, which is
`Stacks.ClosedImmersion.conormalSheafMap` read through the identification
`Stacks.Immersion.conormalSheafSelfIso` of the ringed-space conormal sheaf of a morphism with the
conormal sheaf of an immersion in the sense of [Stacks Project, Tag 01R2]. Specialised to the
canonical morphism of universal first-order thickenings attached to a commutative square of
formally unramified morphisms, this is the morphism of conormal sheaves
`f^* 𝒞_{W/Y} ⟶ 𝒞_{Z/X}` asserted by [Stacks Project, Tag 04F7].

This file proves the **affine characterization** of that morphism. On a compatible pair of
affine opens `V ⊆ W'` and `U ⊆ Z'` cut out by ideals `J ⊆ Γ(W', V)` and `I ⊆ Γ(Z', U)`, the
affine identifications of [Stacks Project, Tag 01R3] part (2) describe the conormal sections as
`J/J²` and `I/I²`, and the induced morphism carries the class of `a : J` to the class of its
image under the ambient ring map `k^♯ : Γ(W', V) ⟶ Γ(Z', U)` ([Stacks Project, Tag 01R4]).

## Main definitions

* `Stacks.Immersion.immersionConormalSheafMap` is the induced morphism
  `f^* 𝒞_{W/W'} ⟶ 𝒞_{Z/Z'}` between the conormal sheaves of two immersions, in the sense of
  [Stacks Project, Tag 01R2].
* `Stacks.Immersion.IsInducedConormalSheafMap` is the affine characterization, as a predicate on
  morphisms `f^* 𝒞_{W/W'} ⟶ 𝒞_{Z/Z'}`.
* `Stacks.Thickenings.universalImmersionConormalSheafMap` is the morphism of conormal sheaves
  `f^* 𝒞_{W/Y} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 04F7], stated for the conormal sheaf of
  `Stacks.Thickenings.immersionConormalSheaf`.
* `Stacks.Thickenings.conormalSheafMapWithCharacterization` bundles that morphism with its
  affine characterization.

## Main results

* `Stacks.Immersion.isInducedConormalSheafMap_immersionConormalSheafMap`: the induced morphism of
  conormal sheaves of a commutative square of immersions satisfies the affine characterization.
* `Stacks.Thickenings.isInducedConormalSheafMap_universalImmersionConormalSheafMap` is that
  statement for the canonical morphism of universal first-order thickenings, which is the affine
  characterization asked for by [Stacks Project, Tag 04F7].
* `Stacks.Immersion.canonicalConormalQuotientMap_comp_pushforward_homEquiv`: the conormal
  quotient map of `j` followed by the transpose of the induced morphism is the unit of
  `k^* ⊣ k_*`, the ideal-sheaf map of the square and the conormal quotient map of `i`, compared by
  `RingedSpaceModuleAdjunction.modulePushforwardSquareIso`.
* `Stacks.ClosedImmersion.unit_comp_pushforward_idealSheafMap_comp_ι`: the section of `ℐ_i` that
  the square produces from a section of `ℐ_j` has for image in `𝒪_{Z'}` the image of the given
  section under `k^♯`.
* `Stacks.Thickenings.universalImmersionConormalSheafMap_eq` identifies
  `Stacks.Thickenings.universalImmersionConormalSheafMap` with
  `Stacks.Thickenings.universalConormalSheafMap`, read through
  `Stacks.Immersion.conormalSheafSelfIso`.

## References

* [Stacks Project, Tag 04F7](https://stacks.math.columbia.edu/tag/04F7)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 04F4](https://stacks.math.columbia.edu/tag/04F4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction 
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.ClosedImmersion.AffineConormal Stacks.ClosedImmersion.IdealSheafAffine

universe u

namespace AlgebraicGeometry.RingedSpace

variable {Zr Xr : RingedSpace.{u, u}}

/-! ### Two more facts about sections -/

/-- **Restriction in a pushforward is restriction along the preimage.** Over opens `B ≤ A` of the
target, the restriction map of `p_* M` is the restriction map of `M` along `p⁻¹B ≤ p⁻¹A`. -/
theorem modulePushforward_obj_val_map (p : Zr ⟶ Xr)
    (M : SheafOfModules.{u} (structureSheafRing Zr)) {A B : Opens Xr.carrier} (g : B ⟶ A)
    (x : ((modulePushforward p).obj M).val.obj (op A)) :
    ((modulePushforward p).obj M).val.map g.op x =
      M.val.map ((Opens.map p.hom.base).map g).op x := rfl

/-- **Two restriction maps between the same opens agree on sections.** -/
theorem val_map_eq_of_subsingleton (M : SheafOfModules.{u} (structureSheafRing Zr))
    {A C : Opens Zr.carrier} (g g' : C ⟶ A) (x : M.val.obj (op A)) :
    M.val.map g.op x = M.val.map g'.op x :=
  M.val.congr_map_apply (congrArg Quiver.Hom.op (Subsingleton.elim g g')) x

end AlgebraicGeometry.RingedSpace

namespace RingedSpaceModuleAdjunction

variable {Z₁ Z₂ X₁ X₂ : RingedSpace.{u, u}} (a : Z₁ ⟶ Z₂) (b : X₁ ⟶ X₂) (j₁ : Z₁ ⟶ X₁)
  (j₂ : Z₂ ⟶ X₂)

/-- **The pushforward comparison of a square, followed by a restriction, is one restriction
map.** -/
theorem modulePushforwardSquareIso_hom_val_app_restrict (comm : j₁ ≫ b = a ≫ j₂)
    (N : SheafOfModules.{u} (structureSheafRing Z₁)) (A : Opens X₂.carrier) {C : Opens Z₁.carrier}
    (g : C ⟶ (Opens.map (a ≫ j₂).hom.base).obj A)
    (g' : C ⟶ (Opens.map (j₁ ≫ b).hom.base).obj A)
    (x : ((modulePushforward b).obj ((modulePushforward j₁).obj N)).val.obj (op A)) :
    N.val.map g.op (((modulePushforwardSquareIso a b j₁ j₂ comm).hom.app N).val.app (op A) x) =
      N.val.map g'.op x :=
  (congrArg (N.val.map g.op)
      (modulePushforwardSquareIso_hom_val_app a b j₁ j₂ comm N A x)).trans
    (val_map_unique N _ g g' x)

end RingedSpaceModuleAdjunction

namespace Stacks.ClosedImmersion

variable {Z Z' W W' : RingedSpace.{u, u}} {i : Z ⟶ Z'} {j : W ⟶ W'} {f : Z ⟶ W} {k : Z' ⟶ W'}

/-! ### The conormal sheaf map of a square is the mate of the pushforward comparison -/

/-- **`Stacks.ClosedImmersion.pullbackCompIso` is componentwise the inverse of the pullback
comparison of the square.** -/
theorem pullbackCompIso_inv (comm : i ≫ k = f ≫ j)
    (M : SheafOfModules.{u} (structureSheafRing W')) :
    (pullbackCompIso comm M).inv = (modulePullbackSquareIso f k i j comm).hom.app M := rfl

/-- **The pullback comparison of the square cancels the identification inside
`Stacks.ClosedImmersion.conormalSheafMap`**, leaving the pullback along `i` of the ideal-sheaf map
of the square. -/
theorem modulePullbackSquareIso_hom_app_comp_conormalSheafMap (comm : i ≫ k = f ≫ j) :
    (modulePullbackSquareIso f k i j comm).hom.app (idealSheaf j) ≫ conormalSheafMap comm =
      (modulePullback i).map (idealSheafMap comm) := by
  rw [conormalSheafMap, ← pullbackCompIso_inv, Iso.inv_hom_id_assoc]

/-- **The conormal quotient maps of a commuting square are exchanged by the induced morphism of
conormal sheaves.** The unit of `j^* ⊣ j_*` at `ℐ_j`, followed by `j_*` of the transpose of
`Stacks.ClosedImmersion.conormalSheafMap`, is the unit of `k^* ⊣ k_*` at `ℐ_j`, followed by `k_*`
of `Stacks.ClosedImmersion.idealSheafMap` and of the unit of `i^* ⊣ i_*` at `ℐ_i`, compared by
`RingedSpaceModuleAdjunction.modulePushforwardSquareIso`. -/
theorem unit_comp_pushforward_homEquiv_conormalSheafMap (comm : i ≫ k = f ≫ j) :
    (modulePullbackPushforwardAdjunction j).unit.app (idealSheaf j) ≫
        (modulePushforward j).map
          ((modulePullbackPushforwardAdjunction f).homEquiv _ _ (conormalSheafMap comm)) =
      ((modulePullbackPushforwardAdjunction k).unit.app (idealSheaf j) ≫
          (modulePushforward k).map (idealSheafMap comm) ≫
          (modulePushforward k).map
            ((modulePullbackPushforwardAdjunction i).unit.app (idealSheaf i))) ≫
        (modulePushforwardSquareIso f k i j comm).hom.app (conormalSheaf i) := by
  have hu := unit_modulePullbackSquareIso f k i j comm (idealSheaf j)
  have h1 := modulePullbackSquareIso_hom_app_comp_conormalSheafMap comm
  have h2 := (modulePullbackPushforwardAdjunction i).unit.naturality (idealSheafMap comm)
  have h3 := (modulePushforwardSquareIso f k i j comm).hom.naturality (conormalSheafMap comm)
  simp only [Functor.comp_map, Functor.id_map] at h2 h3
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hu]
  simp only [Functor.comp_map]
  slice_lhs 4 5 => rw [← h3]
  slice_lhs 3 4 => rw [← Functor.map_comp, ← Functor.map_comp, h1]
  slice_lhs 2 3 => rw [← Functor.map_comp, ← h2, Functor.map_comp]
  simp only [Category.assoc]

/-- **The ideal-sheaf map of a square is the ambient structure-sheaf map.** The unit of
`k^* ⊣ k_*` at `ℐ_j`, followed by `k_*` of `Stacks.ClosedImmersion.idealSheafMap` and of the
inclusion `ℐ_i ⟶ 𝒪_{Z'}`, is the inclusion `ℐ_j ⟶ 𝒪_{W'}` followed by the structure-sheaf map
`k^♯`. -/
theorem unit_comp_pushforward_idealSheafMap_comp_ι (comm : i ≫ k = f ≫ j) :
    (modulePullbackPushforwardAdjunction k).unit.app (idealSheaf j) ≫
        (modulePushforward k).map (idealSheafMap comm ≫ idealSheafι i) =
      idealSheafι j ≫ structureSheafModuleHom k := by
  have hn := (modulePullbackPushforwardAdjunction k).unit.naturality (idealSheafι j)
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hv : (modulePullbackPushforwardAdjunction k).unit.app
        (SheafOfModules.unit (structureSheafRing W')) ≫
      (modulePushforward k).map (modulePullbackUnitToUnit k) = structureSheafModuleHom k :=
    ((modulePullbackPushforwardAdjunction k).homEquiv_unit
      (f := modulePullbackUnitToUnit k)).symm.trans (homEquiv_modulePullbackUnitToUnit k)
  rw [idealSheafMap_comp_ι, Functor.map_comp, ← Category.assoc, ← hn, Category.assoc, hv]

end Stacks.ClosedImmersion

namespace Stacks.Immersion

open Stacks.ClosedImmersion

variable {Z Z' W W' : Scheme.{u}}

/-! ### Scheme-level spellings -/

/-- **The structure-sheaf map of a morphism of schemes, read as a morphism of sheaves of modules,
is the map on sections of the morphism.** -/
theorem structureSheafModuleHom_val_app {Z X : Scheme.{u}} (p : Z ⟶ X) (A : X.Opens)
    (z : Γ(X, A)) :
    (structureSheafModuleHom p.toLRSHom.toShHom).val.app (op A) z = (p.app A).hom z := rfl

/-- **The pushforward of a morphism of sheaves of modules along a morphism of schemes, on
sections**, with the preimage open written `p ⁻¹ᵁ A`. -/
theorem modulePushforward_map_val_app_preimage {Z X : Scheme.{u}} (p : Z ⟶ X)
    {M N : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)} (φ : M ⟶ N)
    (A : X.Opens) (x : ((modulePushforward p.toLRSHom.toShHom).obj M).val.obj (op A)) :
    ((modulePushforward p.toLRSHom.toShHom).map φ).val.app (op A) x =
      φ.val.app (op (p ⁻¹ᵁ A)) x := rfl

/-- **`AlgebraicGeometry.Scheme.Hom.appLE` on an element.** It is the map on sections over the
larger open followed by a restriction. -/
theorem appLE_apply {Z X : Scheme.{u}} (p : Z ⟶ X) (A : X.Opens) (B : Z.Opens)
    (e : B ≤ p ⁻¹ᵁ A) (z : Γ(X, A)) :
    (p.appLE A B e).hom z = (Z.presheaf.map (homOfLE e).op).hom ((p.app A).hom z) := rfl

/-- **`Stacks.Immersion.canonicalConormalQuotientMap` written out.** It is the unit of
`i^* ⊣ i_*` at the ideal sheaf of `i`, followed by the pushforward of
`Stacks.Immersion.conormalSheafSelfIso`. -/
theorem canonicalConormalQuotientMap_eq {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    canonicalConormalQuotientMap i =
      (modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
          (idealSheaf i.toLRSHom.toShHom) ≫
        (modulePushforward i.toLRSHom.toShHom).map (conormalSheafSelfIso i).hom := rfl

/-! ### The induced morphism of conormal sheaves of a square of immersions -/

/-- The commutative square of **ringed spaces** underlying a commutative square of schemes. -/
theorem toShHom_square {i : Z ⟶ Z'} {j : W ⟶ W'} {f : Z ⟶ W} {k : Z' ⟶ W'}
    (hcomm : i ≫ k = f ≫ j) :
    i.toLRSHom.toShHom ≫ k.toLRSHom.toShHom = f.toLRSHom.toShHom ≫ j.toLRSHom.toShHom :=
  congrArg (fun p : Z ⟶ W' => p.toLRSHom.toShHom) hcomm

/-- If `i ≫ k = f ≫ j` and `U ⊆ k⁻¹V`, then `i⁻¹U ⊆ f⁻¹j⁻¹V`. -/
theorem preimage_le_preimage_of_square {i : Z ⟶ Z'} {j : W ⟶ W'} {f : Z ⟶ W} {k : Z' ⟶ W'}
    (hcomm : i ≫ k = f ≫ j) (U : Z'.Opens) (V : W'.Opens) (hUV : U ≤ k ⁻¹ᵁ V) :
    i ⁻¹ᵁ U ≤ f ⁻¹ᵁ (j ⁻¹ᵁ V) := by
  calc
    i ⁻¹ᵁ U ≤ i ⁻¹ᵁ (k ⁻¹ᵁ V) := i.preimage_mono hUV
    _ = f ⁻¹ᵁ (j ⁻¹ᵁ V) := by
      change (i ≫ k) ⁻¹ᵁ V = (f ≫ j) ⁻¹ᵁ V
      rw [hcomm]

/-- **The morphism `f^* 𝒞_{W/W'} ⟶ 𝒞_{Z/Z'}` of conormal sheaves induced by a commutative square
of immersions**, in the sense of [Stacks Project, Tag 01R2]: the ringed-space morphism
`Stacks.ClosedImmersion.conormalSheafMap` conjugated on both sides by
`Stacks.Immersion.conormalSheafSelfIso`, which identifies the ringed-space conormal sheaf of a
morphism with the conormal sheaf of an immersion. -/
def immersionConormalSheafMap (i : Z ⟶ Z') (j : W ⟶ W') (f : Z ⟶ W) (k : Z' ⟶ W')
    [IsImmersion i] [IsImmersion j]
    (comm : i.toLRSHom.toShHom ≫ k.toLRSHom.toShHom =
      f.toLRSHom.toShHom ≫ j.toLRSHom.toShHom) :
    (modulePullback f.toLRSHom.toShHom).obj
        (conormalSheaf j.liftCoborder.toLRSHom.toShHom) ⟶
      conormalSheaf i.liftCoborder.toLRSHom.toShHom :=
  (modulePullback f.toLRSHom.toShHom).map (conormalSheafSelfIso j).inv ≫
    conormalSheafMap comm ≫ (conormalSheafSelfIso i).hom

/-- **The induced morphism of conormal sheaves of a square of immersions is the pullback of the
map of ideal sheaves, conjugated by `Stacks.Immersion.conormalSheafSelfIso`.** -/
theorem immersionConormalSheafMap_eq_pullback_idealSheafMap (i : Z ⟶ Z') (j : W ⟶ W')
    (f : Z ⟶ W) (k : Z' ⟶ W') [IsImmersion i] [IsImmersion j]
    (comm : i.toLRSHom.toShHom ≫ k.toLRSHom.toShHom =
      f.toLRSHom.toShHom ≫ j.toLRSHom.toShHom) :
    immersionConormalSheafMap i j f k comm =
      (modulePullback f.toLRSHom.toShHom).map (conormalSheafSelfIso j).inv ≫
        (pullbackCompIso comm (idealSheaf j.toLRSHom.toShHom)).hom ≫
          (modulePullback i.toLRSHom.toShHom).map (idealSheafMap comm) ≫
            (conormalSheafSelfIso i).hom :=
  congrArg
    (fun t => (modulePullback f.toLRSHom.toShHom).map (conormalSheafSelfIso j).inv ≫ t)
    (Category.assoc _ _ _)

/-- **The conormal quotient maps are exchanged by
`Stacks.Immersion.immersionConormalSheafMap`.** -/
theorem canonicalConormalQuotientMap_comp_pushforward_homEquiv
    (i : Z ⟶ Z') (j : W ⟶ W') (f : Z ⟶ W) (k : Z' ⟶ W') [IsImmersion i] [IsImmersion j]
    (comm : i.toLRSHom.toShHom ≫ k.toLRSHom.toShHom =
      f.toLRSHom.toShHom ≫ j.toLRSHom.toShHom) :
    canonicalConormalQuotientMap j ≫
        (modulePushforward j.toLRSHom.toShHom).map
          ((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _
            (immersionConormalSheafMap i j f k comm)) =
      ((modulePullbackPushforwardAdjunction k.toLRSHom.toShHom).unit.app
            (idealSheaf j.toLRSHom.toShHom) ≫
          (modulePushforward k.toLRSHom.toShHom).map (idealSheafMap comm) ≫
          (modulePushforward k.toLRSHom.toShHom).map (canonicalConormalQuotientMap i)) ≫
        (modulePushforwardSquareIso f.toLRSHom.toShHom k.toLRSHom.toShHom
            i.toLRSHom.toShHom j.toLRSHom.toShHom comm).hom.app
          (conormalSheaf i.liftCoborder.toLRSHom.toShHom) := by
  have hkey := unit_comp_pushforward_homEquiv_conormalSheafMap comm
  have h3 := (modulePushforwardSquareIso f.toLRSHom.toShHom k.toLRSHom.toShHom
    i.toLRSHom.toShHom j.toLRSHom.toShHom comm).hom.naturality (conormalSheafSelfIso i).hom
  simp only [Functor.comp_map] at h3
  have hw : (conormalSheafSelfIso j).hom ≫
      (modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _
        (immersionConormalSheafMap i j f k comm) =
      ((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _
          (conormalSheafMap comm)) ≫
        (modulePushforward f.toLRSHom.toShHom).map (conormalSheafSelfIso i).hom := by
    rw [immersionConormalSheafMap, Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_right, Iso.hom_inv_id_assoc]
  rw [canonicalConormalQuotientMap_eq j, Category.assoc, ← Functor.map_comp, hw,
    Functor.map_comp, ← Category.assoc, hkey, canonicalConormalQuotientMap_eq i,
    Functor.map_comp]
  simp only [Category.assoc]
  slice_lhs 4 5 => rw [← h3]

/-! ### The affine characterization -/

/-- **The affine characterization of the induced morphism of conormal sheaves**, the property of
[Stacks Project, Tag 01R4] for a commutative square of immersions `i ≫ k = f ≫ j`.

Let `V ⊆ W'` and `U ⊆ Z'` be affine opens with `U ⊆ k⁻¹V`, whose scheme-theoretic intersections
with `W` and with `Z` are cut out by ideals `J ⊆ Γ(W', V)` and `I ⊆ Γ(Z', U)`, compatibly with
the affine identifications `V ≅ Spec Γ(W', V)` and `U ≅ Spec Γ(Z', U)`. By
[Stacks Project, Tag 01R3] part (2) the conormal sections over those opens are `J/J²` and
`I/I²`, through `Stacks.Conormal.affineConormalIsoCotangent`. A morphism
`φ : f^* 𝒞_{W/W'} ⟶ 𝒞_{Z/Z'}` is *the* induced one when its transpose along `f^* ⊣ f_*` carries
the class of `a : J` to the class of any `b : I` with `b = k^♯ a`. -/
def IsInducedConormalSheafMap (i : Z ⟶ Z') (j : W ⟶ W') (f : Z ⟶ W) (k : Z' ⟶ W')
    [IsImmersion i] [IsImmersion j] (hcomm : i ≫ k = f ≫ j)
    (φ : (modulePullback f.toLRSHom.toShHom).obj
        (conormalSheaf j.liftCoborder.toLRSHom.toShHom) ⟶
      conormalSheaf i.liftCoborder.toLRSHom.toShHom) : Prop :=
  ∀ (U : Z'.Opens) (hU : IsAffineOpen U) (V : W'.Opens) (hV : IsAffineOpen V)
    (hUV : U ≤ k ⁻¹ᵁ V) (I : Ideal Γ(Z', U)) (J : Ideal Γ(W', V))
    (eZ : pullback i U.ι ≅ Spec (quotRing I))
    (heZ : pullback.snd i U.ι ≫ hU.isoSpec.hom = eZ.hom ≫ quotImmersion Γ(Z', U) I)
    (eW : pullback j V.ι ≅ Spec (quotRing J))
    (heW : pullback.snd j V.ι ≫ hV.isoSpec.hom = eW.hom ≫ quotImmersion Γ(W', V) J)
    (a : J) (b : I),
    (b : Γ(Z', U)) = (k.appLE V U hUV).hom (a : Γ(W', V)) →
    (conormalSheaf i.liftCoborder.toLRSHom.toShHom).val.map
        (homOfLE (preimage_le_preimage_of_square hcomm U V hUV)).op
        (((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _ φ).val.app
          (op (j ⁻¹ᵁ V))
          ((Stacks.Conormal.affineConormalIsoCotangent j V hV J eW heW).inv.hom
            (J.toCotangent a))) =
      (Stacks.Conormal.affineConormalIsoCotangent i U hU I eZ heZ).inv.hom (I.toCotangent b)

/-- **The induced morphism of conormal sheaves satisfies the affine characterization.** This is
[Stacks Project, Tag 01R4] for a commutative square of immersions of schemes: on a compatible
pair of affine opens, the morphism of conormal sheaves induced by the square sends the class of
`a : J` in `J/J²` to the class in `I/I²` of its image under the ambient ring map `k^♯`. -/
theorem isInducedConormalSheafMap_immersionConormalSheafMap
    (i : Z ⟶ Z') (j : W ⟶ W') (f : Z ⟶ W) (k : Z' ⟶ W') [IsImmersion i] [IsImmersion j]
    (hcomm : i ≫ k = f ≫ j) :
    IsInducedConormalSheafMap i j f k hcomm
      (immersionConormalSheafMap i j f k (toShHom_square hcomm)) := by
  intro U hU V hV hUV I J eZ heZ eW heW a b hab
  obtain ⟨y, hy⟩ := exists_idealSheaf_section j V hV J eW heW a
  have hW := Stacks.Conormal.affineConormalIsoCotangent_inv_toCotangent_canonical
    j V hV J eW heW a y hy
  have hK := congr($(canonicalConormalQuotientMap_comp_pushforward_homEquiv i j f k
    (toShHom_square hcomm)).val.app (op V) y)
  have hI := congr($(unit_comp_pushforward_idealSheafMap_comp_ι
    (toShHom_square hcomm)).val.app (op V) y)
  simp only [comp_val_app_apply, modulePushforward_map_val_app_preimage] at hK
  simp only [Functor.map_comp, comp_val_app_apply,
    modulePushforward_map_val_app_preimage] at hI
  obtain ⟨E, hE⟩ : ∃ E : (idealSheaf i.toLRSHom.toShHom).val.obj (op (k ⁻¹ᵁ V)),
      ((modulePushforward k.toLRSHom.toShHom).map (idealSheafMap (toShHom_square hcomm))).val.app
          (op V) (((modulePullbackPushforwardAdjunction k.toLRSHom.toShHom).unit.app
            (idealSheaf j.toLRSHom.toShHom)).val.app (op V) y) = E := ⟨_, rfl⟩
  rw [hE] at hK hI
  have hiU : i ⁻¹ᵁ U ≤ i ⁻¹ᵁ (k ⁻¹ᵁ V) := i.preimage_mono hUV
  have hmid : (idealSheafι i.toLRSHom.toShHom).val.app (op (k ⁻¹ᵁ V)) E =
      (k.app V).hom (a : Γ(W', V)) :=
    hI.trans ((structureSheafModuleHom_val_app k V _).trans
      (congrArg (fun z => (k.app V).hom z) hy))
  have hy' : (idealSheafι i.toLRSHom.toShHom).val.app (op U)
      ((idealSheaf i.toLRSHom.toShHom).val.map (homOfLE hUV).op E) = (b : Γ(Z', U)) :=
    (val_app_naturality (idealSheafι i.toLRSHom.toShHom) (homOfLE hUV) E).trans
      ((unit_val_map_eq (k ⁻¹ᵁ V) U hUV _).trans
        ((congrArg (fun z => (Z'.presheaf.map (homOfLE hUV).op).hom z) hmid).trans
          ((appLE_apply k V U hUV (a : Γ(W', V))).symm.trans hab.symm)))
  have hZgen := Stacks.Conormal.affineConormalIsoCotangent_inv_toCotangent_canonical
    i U hU I eZ heZ b
    ((idealSheaf i.toLRSHom.toShHom).val.map (homOfLE hUV).op E) hy'
  have hnat := val_app_naturality (canonicalConormalQuotientMap i) (homOfLE hUV) E
  have hpf := modulePushforward_obj_val_map i.toLRSHom.toShHom
    (conormalSheaf i.liftCoborder.toLRSHom.toShHom) (homOfLE hUV)
    ((canonicalConormalQuotientMap i).val.app (op (k ⁻¹ᵁ V)) E)
  have hsub := val_map_eq_of_subsingleton (conormalSheaf i.liftCoborder.toLRSHom.toShHom)
    ((Opens.map i.toLRSHom.toShHom.hom.base).map (homOfLE hUV)) (homOfLE hiU)
    ((canonicalConormalQuotientMap i).val.app (op (k ⁻¹ᵁ V)) E)
  have hsq := modulePushforwardSquareIso_hom_val_app_restrict f.toLRSHom.toShHom
    k.toLRSHom.toShHom i.toLRSHom.toShHom j.toLRSHom.toShHom (toShHom_square hcomm)
    (conormalSheaf i.liftCoborder.toLRSHom.toShHom) V
    (homOfLE (preimage_le_preimage_of_square hcomm U V hUV)) (homOfLE hiU)
    ((canonicalConormalQuotientMap i).val.app (op (k ⁻¹ᵁ V)) E)
  refine Eq.trans ?_ hZgen.symm
  refine Eq.trans ?_ hnat.symm
  refine Eq.trans ?_ hpf.symm
  refine Eq.trans ?_ hsub.symm
  refine Eq.trans ?_ hsq
  exact val_map_congr (homOfLE (preimage_le_preimage_of_square hcomm U V hUV))
    (Eq.trans (congrArg _ hW) hK)

end Stacks.Immersion

namespace Stacks.Thickenings

open Stacks.ClosedImmersion Stacks.Immersion

variable {Z X W Y : Scheme.{u}} {h : Z ⟶ X} {h' : W ⟶ Y}

/-! ### Stacks 04F7: the induced morphism of conormal sheaves and its affine characterization -/

/-- **The morphism of conormal sheaves `f^* 𝒞_{W/Y} ⟶ 𝒞_{Z/X}` of
[Stacks Project, Tag 04F7]**, stated for the conormal sheaf
`Stacks.Thickenings.immersionConormalSheaf` of [Stacks Project, Tag 01R2] — which is the conormal
sheaf of [Stacks Project, Tag 04F4] — rather than for the ringed-space conormal sheaf of the
inclusion. -/
def universalImmersionConormalSheafMap (tZ : UniversalFirstOrderThickening h)
    (tW : UniversalFirstOrderThickening h') (f : Z ⟶ W) (g : X ⟶ Y) (comm : h ≫ g = f ≫ h') :
    (modulePullback f.toLRSHom.toShHom).obj (immersionConormalSheaf tW.inclusion) ⟶
      immersionConormalSheaf tZ.inclusion :=
  immersionConormalSheafMap tZ.inclusion tW.inclusion f
    (universalFirstOrderThickeningMap tZ tW f g comm)
    (toShHom_universalFirstOrderThickeningMap_inclusion tZ tW f g comm)

/-- **The two conormal-sheaf morphisms of [Stacks Project, Tag 04F7] agree.** The morphism
`Stacks.Thickenings.universalImmersionConormalSheafMap` between the conormal sheaves of
[Stacks Project, Tag 01R2] is `Stacks.Thickenings.universalConormalSheafMap` between the
ringed-space conormal sheaves of the inclusions, conjugated by
`Stacks.Immersion.conormalSheafSelfIso`. -/
theorem universalImmersionConormalSheafMap_eq (tZ : UniversalFirstOrderThickening h)
    (tW : UniversalFirstOrderThickening h') (f : Z ⟶ W) (g : X ⟶ Y) (comm : h ≫ g = f ≫ h') :
    universalImmersionConormalSheafMap tZ tW f g comm =
      (modulePullback f.toLRSHom.toShHom).map (conormalSheafSelfIso tW.inclusion).inv ≫
        universalConormalSheafMap tZ tW f g comm ≫
          (conormalSheafSelfIso tZ.inclusion).hom :=
  rfl

/-- **The affine characterization of the induced morphism of conormal sheaves.** Let
`h : Z ⟶ X` and `h' : W ⟶ Y` be formally unramified, let `Z ⊂ Z'` and `W ⊂ W'` be universal
first-order thickenings of `h` and of `h'`, and let `h ≫ g = f ≫ h'` be a commutative square. The
morphism of conormal sheaves `f^* 𝒞_{W/Y} ⟶ 𝒞_{Z/X}` induced by the canonical morphism `(f, f')`
of thickenings is *the* map of [Stacks Project, Tag 01R4] for the square `(Z ⊂ Z') → (W ⊂ W')`:
on a compatible pair of affine opens `V ⊆ W'` and `U ⊆ Z'` cut out by ideals `J` and `I`, it
carries the class of `a : J` in `J/J²` to the class in `I/I²` of the image of `a` under the ring
map of `f'`. -/
@[stacks 04F7 "affine characterization of the induced conormal-sheaf morphism"]
theorem isInducedConormalSheafMap_universalImmersionConormalSheafMap
    (tZ : UniversalFirstOrderThickening h) (tW : UniversalFirstOrderThickening h')
    (f : Z ⟶ W) (g : X ⟶ Y) (comm : h ≫ g = f ≫ h') :
    IsInducedConormalSheafMap tZ.inclusion tW.inclusion f
      (universalFirstOrderThickeningMap tZ tW f g comm)
      (universalFirstOrderThickeningMap_inclusion tZ tW f g comm)
      (universalImmersionConormalSheafMap tZ tW f g comm) :=
  isInducedConormalSheafMap_immersionConormalSheafMap tZ.inclusion tW.inclusion f
    (universalFirstOrderThickeningMap tZ tW f g comm)
    (universalFirstOrderThickeningMap_inclusion tZ tW f g comm)

/-- The morphism of conormal sheaves of [Stacks Project, Tag 04F7] together with its affine
characterization, as a subtype. -/
def conormalSheafMapWithCharacterization (tZ : UniversalFirstOrderThickening h)
    (tW : UniversalFirstOrderThickening h') (f : Z ⟶ W) (g : X ⟶ Y) (comm : h ≫ g = f ≫ h') :
    { φ : (modulePullback f.toLRSHom.toShHom).obj (immersionConormalSheaf tW.inclusion) ⟶
        immersionConormalSheaf tZ.inclusion //
      IsInducedConormalSheafMap tZ.inclusion tW.inclusion f
        (universalFirstOrderThickeningMap tZ tW f g comm)
        (universalFirstOrderThickeningMap_inclusion tZ tW f g comm) φ } :=
  ⟨universalImmersionConormalSheafMap tZ tW f g comm,
    isInducedConormalSheafMap_universalImmersionConormalSheafMap tZ tW f g comm⟩

end Stacks.Thickenings

end
