module

public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.Descent
public import StacksFrontier.RingTheory.Dualizing.FlatLocalGorenstein
public import StacksFrontier.RingTheory.Dualizing.GorensteinTransport
import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Composition

/-!
# Composition of Gorenstein morphisms

For composable morphisms of schemes with locally Noetherian fibres, Gorensteinness passes to the
composite. Conversely, when the first morphism is flat, Gorensteinness of the composite implies
Gorensteinness of the first morphism and of the second morphism at the points in the image of
the first.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isGorensteinAt_comp` and
  `AlgebraicGeometry.Scheme.Hom.isGorenstein_comp` give the pointwise and global composition
  statements.
* `AlgebraicGeometry.Scheme.Hom.isGorensteinAt_left_of_comp` and
  `AlgebraicGeometry.Scheme.Hom.isGorensteinAt_right_of_comp` give the pointwise converse.
* `AlgebraicGeometry.Scheme.Hom.isGorenstein_left_of_comp` and
  `AlgebraicGeometry.Scheme.Hom.isGorensteinAt_image_of_comp` give the global converse.

## Implementation notes

The three locally Noetherian fibre hypotheses are supplied separately for the two morphisms and
their composite. Part (3) is split into its two conclusions, as is part (4); the last conclusion
is indexed by a point of the source, and therefore states Gorensteinness at every point in the
image of the first morphism.

The algebra underneath is the Gorenstein criterion for a flat local homomorphism, in the form
`Dualizing.isGorensteinLocalRing_iff_of_flat`: for a flat local homomorphism `B → C` and an ideal
`I ⊆ 𝔪_B`, the ring `C/IC` is Gorenstein exactly when both `B/I` and the closed fibre `C/𝔪_B C`
are. Taking `I` to be the extension of the maximal ideal of the stalk of the outer target turns
the three fibre local rings into the three quotients, through
`AlgebraicGeometry.quotientStalkEquivFiberStalk`, and
`Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff` moves Gorensteinness across those
identifications.

## References

* [Stacks Project, Tag 0C11](https://stacks.math.columbia.edu/tag/0C11)
* [Stacks Project, Tag 0BJL](https://stacks.math.columbia.edu/tag/0BJL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.Duality

/-- **The flat local criterion for Gorensteinness of a quotient.** For a flat local homomorphism
`B → C` and an ideal `I ≤ 𝔪_B`, the ring `C/IC` is Gorenstein precisely when `B/I` and the closed
fibre `C/𝔪_B C` are. -/
private theorem isGorensteinLocalRing_quotientMap_iff {B C : Type*} [CommRing B] [CommRing C]
    [IsLocalRing B] [IsLocalRing C] [Algebra B C] [IsLocalHom (algebraMap B C)]
    [Module.Flat B C] (I : Ideal B) (hI : I ≤ IsLocalRing.maximalIdeal B)
    [IsNoetherianRing (B ⧸ I)] [IsLocalRing (B ⧸ I)]
    [IsNoetherianRing (C ⧸ I.map (algebraMap B C))]
    [IsLocalRing (C ⧸ I.map (algebraMap B C))]
    [IsNoetherianRing (C ⧸ (IsLocalRing.maximalIdeal B).map (algebraMap B C))]
    [IsLocalRing (C ⧸ (IsLocalRing.maximalIdeal B).map (algebraMap B C))] :
    Dualizing.IsGorensteinLocalRing (C ⧸ I.map (algebraMap B C)) ↔
      (Dualizing.IsGorensteinLocalRing (B ⧸ I) ∧
        Dualizing.IsGorensteinLocalRing
          (C ⧸ (IsLocalRing.maximalIdeal B).map (algebraMap B C))) := by
  let β : B →+* C := algebraMap B C
  let J := I.map β
  let K := (IsLocalRing.maximalIdeal B).map β
  let D := B ⧸ I
  let E := C ⧸ J
  let F := C ⧸ K
  let γ : D →+* E := algebraMap D E
  let _ : Module.Flat D E := flat_quotient_map I
  let qB : B →+* D := Ideal.Quotient.mk I
  let qC : C →+* E := Ideal.Quotient.mk J
  let _ : IsLocalHom qB := IsLocalHom.of_surjective qB Ideal.Quotient.mk_surjective
  let _ : IsLocalHom qC := IsLocalHom.of_surjective qC Ideal.Quotient.mk_surjective
  have hcomp : γ.comp qB = qC.comp β := by
    ext b
    show Ideal.quotientMap J β Ideal.le_comap_map (Ideal.Quotient.mk I b) = _
    simp [qC]
  have hmaxD : IsLocalRing.maximalIdeal D = (IsLocalRing.maximalIdeal B).map qB :=
    (IsLocalRing.map_maximalIdeal_of_surjective qB Ideal.Quotient.mk_surjective).symm
  have hmax : (IsLocalRing.maximalIdeal D).map γ ≤ IsLocalRing.maximalIdeal E := by
    calc
      _ = ((IsLocalRing.maximalIdeal B).map β).map qC := by
        rw [hmaxD, Ideal.map_map, hcomp, ← Ideal.map_map]
      _ ≤ (IsLocalRing.maximalIdeal C).map qC :=
        Ideal.map_mono (IsLocalRing.map_maximalIdeal_le β)
      _ = IsLocalRing.maximalIdeal E :=
        IsLocalRing.map_maximalIdeal_of_surjective qC Ideal.Quotient.mk_surjective
  let _ : IsLocalHom γ := (IsLocalRing.local_hom_TFAE γ).out 3 1 |>.mp hmax
  let L := (IsLocalRing.maximalIdeal D).map (algebraMap D E)
  have hL : L = K.map qC := by
    dsimp [L, K]
    rw [hmaxD, Ideal.map_map, hcomp, ← Ideal.map_map]
  have hJK : J ≤ K := Ideal.map_mono hI
  let eClosed : (E ⧸ L) ≃+* F :=
    (Ideal.quotEquivOfEq hL).trans (AlgebraicGeometry.quotientQuotientRingEquiv J K hJK)
  let _ : IsLocalRing (E ⧸ L) := eClosed.symm.isLocalRing
  let _ : IsNoetherianRing (E ⧸ L) := isNoetherianRing_of_ringEquiv _ eClosed.symm
  exact (Dualizing.isGorensteinLocalRing_iff_of_flat D E).trans
    (and_congr_right fun _ => isGorensteinLocalRing_ringEquiv_iff eClosed)

end Stacks.Duality

namespace AlgebraicGeometry.Scheme.Hom

/-- In a composite of scheme morphisms whose first factor is flat at a point, flatness of the
composite at that point descends to the second factor at the image point. -/
private theorem stalkMap_flat_right_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hβ : (f.stalkMap x).hom.Flat) (hcomp : ((f ≫ g).stalkMap x).hom.Flat) :
    (g.stalkMap (f x)).hom.Flat := by
  let α := (g.stalkMap (f x)).hom
  let β := (f.stalkMap x).hom
  have hγ : (β.comp α).Flat := by rwa [stalkMap_comp] at hcomp
  let _ : Algebra _ _ := β.toAlgebra
  let _ : Module.Flat _ _ := RingHom.flat_algebraMap_iff.mpr hβ
  let _ : IsLocalHom (algebraMap _ _) := by
    show IsLocalHom β
    infer_instance
  let _ : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let pβ := Spec.map (CommRingCat.ofHom β)
  let pα := Spec.map (CommRingCat.ofHom α)
  have : Surjective pβ := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
  have : Flat pβ := Flat.SpecMap_iff.mpr hβ
  have : Flat (pβ ≫ pα) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact Flat.SpecMap_iff.mpr hγ
  exact Flat.SpecMap_iff.mp (AlgebraicGeometry.flat_of_comp_of_surjective_flat pβ pα)

/-- **Pointwise composition, in unfolded form.** For `f` flat at `x`, the composite is Gorenstein
at `x` exactly when `f` is Gorenstein at `x` and `g` is Gorenstein at `f x`. -/
private theorem isGorensteinAt_comp_iff_of_flatAt {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hg : ∀ z : Z, IsLocallyNoetherian (g.fiber z))
    (hfg : ∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)) (x : X)
    (hflat : IsFlatAt f.toLRSHom.toShHom x) :
    IsGorensteinAt (f ≫ g) hfg x ↔ IsGorensteinAt f hf x ∧ IsGorensteinAt g hg (f x) := by
  let _ : IsLocallyNoetherian (f.fiber (f x)) := hf (f x)
  let _ : IsLocallyNoetherian (g.fiber (g (f x))) := hg (g (f x))
  let _ : IsLocallyNoetherian ((f ≫ g).fiber ((f ≫ g) x)) := hfg ((f ≫ g) x)
  unfold IsGorensteinAt
  let A := Z.presheaf.stalk (g (f x))
  let B := Y.presheaf.stalk (f x)
  let C := X.presheaf.stalk x
  let α := (g.stalkMap (f x)).hom
  let β := (f.stalkMap x).hom
  let I := Ideal.map α (IsLocalRing.maximalIdeal A)
  let J := I.map β
  let K := (IsLocalRing.maximalIdeal B).map β
  let eG := quotientStalkEquivFiberStalk g (f x)
  let eF := quotientStalkEquivFiberStalk f x
  let eC₀ := quotientStalkEquivFiberStalk (f ≫ g) x
  let _ : IsLocalRing (B ⧸ I) := eG.symm.isLocalRing
  let _ : IsNoetherianRing (B ⧸ I) := isNoetherianRing_of_ringEquiv _ eG.symm
  let _ : IsLocalRing (C ⧸ K) := eF.symm.isLocalRing
  let _ : IsNoetherianRing (C ⧸ K) := isNoetherianRing_of_ringEquiv _ eF.symm
  have hJ : J = Ideal.map ((f ≫ g).stalkMap x).hom (IsLocalRing.maximalIdeal A) := by
    dsimp [J, I, α, β]
    rw [stalkMap_comp, CommRingCat.hom_comp, Ideal.map_map]
    rfl
  let eC := (Ideal.quotEquivOfEq hJ).trans eC₀
  let _ : IsLocalRing (C ⧸ J) := eC.symm.isLocalRing
  let _ : IsNoetherianRing (C ⧸ J) := isNoetherianRing_of_ringEquiv _ eC.symm
  let _ : Algebra B C := β.toAlgebra
  let _ : IsLocalHom (algebraMap B C) := by
    show IsLocalHom β
    infer_instance
  let _ : Module.Flat B C := RingHom.flat_algebraMap_iff.mpr hflat
  have hI : I ≤ IsLocalRing.maximalIdeal B := IsLocalRing.map_maximalIdeal_le α
  have hCrit := Stacks.Duality.isGorensteinLocalRing_quotientMap_iff (B := B) (C := C) I hI
  have hGG : Dualizing.IsGorensteinLocalRing (B ⧸ I) ↔
      Dualizing.IsGorensteinLocalRing
        ((g.fiber (g (f x))).presheaf.stalk (g.asFiber (f x))) :=
    Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff eG
  have hGF : Dualizing.IsGorensteinLocalRing (C ⧸ K) ↔
      Dualizing.IsGorensteinLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff eF
  have hGC : Dualizing.IsGorensteinLocalRing (C ⧸ J) ↔
      Dualizing.IsGorensteinLocalRing
        (((f ≫ g).fiber ((f ≫ g) x)).presheaf.stalk ((f ≫ g).asFiber x)) :=
    Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff eC
  constructor
  · rintro ⟨hflatComp, hGcomp⟩
    obtain ⟨hGbase, hGclosed⟩ := hCrit.mp (hGC.mpr hGcomp)
    exact ⟨⟨hflat, hGF.mp hGclosed⟩, stalkMap_flat_right_of_comp f g x hflat hflatComp,
      hGG.mp hGbase⟩
  · rintro ⟨⟨_, hGf⟩, ⟨hflatG, hGg⟩⟩
    refine ⟨?_, hGC.mp (hCrit.mpr ⟨hGG.mpr hGg, hGF.mpr hGf⟩)⟩
    show ((f ≫ g).stalkMap x).hom.Flat
    rw [stalkMap_comp]
    exact RingHom.Flat.comp hflatG hflat

/-- Gorensteinness at a point is preserved by composition. -/
@[stacks 0C11 "part (1)"]
public theorem isGorensteinAt_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hg : ∀ z : Z, IsLocallyNoetherian (g.fiber z))
    (hfg : ∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)) (x : X)
    (hfx : IsGorensteinAt f hf x) (hgy : IsGorensteinAt g hg (f x)) :
    IsGorensteinAt (f ≫ g) hfg x := by
  exact (isGorensteinAt_comp_iff_of_flatAt f g hf hg hfg x hfx.1).mpr ⟨hfx, hgy⟩

/-- The composite of Gorenstein morphisms is Gorenstein. -/
@[stacks 0C11 "part (2)"]
public theorem isGorenstein_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hg : ∀ z : Z, IsLocallyNoetherian (g.fiber z))
    (hfg : ∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z))
    (hF : IsGorenstein f hf) (hG : IsGorenstein g hg) :
    IsGorenstein (f ≫ g) hfg := fun x =>
  isGorensteinAt_comp f g hf hg hfg x (hF x) (hG (f x))

/-- If a composite is Gorenstein at a point and the first map is flat there, then the first map is
Gorenstein at that point. -/
@[stacks 0C11 "part (3), first morphism"]
public theorem isGorensteinAt_left_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hg : ∀ z : Z, IsLocallyNoetherian (g.fiber z))
    (hfg : ∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)) (x : X)
    (hcomp : IsGorensteinAt (f ≫ g) hfg x)
    (hflat : IsFlatAt f.toLRSHom.toShHom x) :
    IsGorensteinAt f hf x := by
  exact ((isGorensteinAt_comp_iff_of_flatAt f g hf hg hfg x hflat).mp hcomp).1

/-- If a composite is Gorenstein at a point and the first map is flat there, then the second map is
Gorenstein at the image point. -/
@[stacks 0C11 "part (3), second morphism"]
public theorem isGorensteinAt_right_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hg : ∀ z : Z, IsLocallyNoetherian (g.fiber z))
    (hfg : ∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)) (x : X)
    (hcomp : IsGorensteinAt (f ≫ g) hfg x)
    (hflat : IsFlatAt f.toLRSHom.toShHom x) :
    IsGorensteinAt g hg (f x) := by
  exact ((isGorensteinAt_comp_iff_of_flatAt f g hf hg hfg x hflat).mp hcomp).2

/-- If the composite is Gorenstein and the first map is flat, the first map is Gorenstein. -/
@[stacks 0C11 "part (4), first morphism"]
public theorem isGorenstein_left_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hg : ∀ z : Z, IsLocallyNoetherian (g.fiber z))
    (hfg : ∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z))
    (hcomp : IsGorenstein (f ≫ g) hfg) (hflat : Flat f) :
    IsGorenstein f hf := fun x =>
  isGorensteinAt_left_of_comp f g hf hg hfg x (hcomp x) (Flat.stalkMap f x)

/-- If the composite is Gorenstein and the first map is flat, the second map is Gorenstein at each
point in the image of the first. -/
@[stacks 0C11 "part (4), second morphism on the image"]
public theorem isGorensteinAt_image_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hg : ∀ z : Z, IsLocallyNoetherian (g.fiber z))
    (hfg : ∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z))
    (hcomp : IsGorenstein (f ≫ g) hfg) (hflat : Flat f) (x : X) :
    IsGorensteinAt g hg (f x) :=
  isGorensteinAt_right_of_comp f g hf hg hfg x (hcomp x) (Flat.stalkMap f x)

end AlgebraicGeometry.Scheme.Hom
