module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.RingTheory.CohenMacaulay.FlatLocalHom
public import StacksFrontier.RingTheory.Flat.Basic
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterion
public import StacksCore.Tactic.StacksAttribute

/-!
# Composition of Cohen–Macaulay morphisms

For composable morphisms of schemes with locally Noetherian fibres, Cohen–Macaulayness passes
to the composite. Conversely, when the first morphism is flat, Cohen–Macaulayness of the
composite implies Cohen–Macaulayness of the first morphism and of the second morphism at points
in the image of the first.

## Main results

* `AlgebraicGeometry.isCohenMacaulayAt_comp` and `AlgebraicGeometry.isCohenMacaulay_comp` give
  the pointwise and global composition statements.
* `AlgebraicGeometry.isCohenMacaulayAt_left_of_comp_of_flatAt` and
  `AlgebraicGeometry.isCohenMacaulayAt_right_of_comp_of_flatAt` give pointwise reflection.
* `AlgebraicGeometry.isCohenMacaulay_left_of_comp_of_flat` and
  `AlgebraicGeometry.isCohenMacaulayAt_right_of_comp_of_flat` give global reflection.

## Implementation notes

The six declarations state respectively part (1), part (2), the two conclusions of part (3),
and the two conclusions of part (4) of the source lemma. The second conclusion of part (4) is
quantified over `x : X`, thereby expressing the claim at every point of the image of `f`.
Flatness of a scheme morphism is Mathlib's `AlgebraicGeometry.Flat`; flatness at a point is
`AlgebraicGeometry.IsFlatAt`.

The algebra underneath is the flat local criterion for Cohen–Macaulayness: for a flat local
homomorphism `B → C` and an ideal `I ⊆ 𝔪_B`, the ring `C/IC` is Cohen–Macaulay exactly when
both `B/I` and the closed fibre `C/𝔪_B C` are. Applying this to `I` the extension of the
maximal ideal of the stalk of the outer target turns the composition statement into an identity
of fibre local rings, which `AlgebraicGeometry.quotientStalkEquivFiberStalk` supplies.

## References

* [Stacks Project, Tag 0C0W](https://stacks.math.columbia.edu/tag/0C0W)
-/

@[expose] public section

open CategoryTheory
open RingTheory.Sequence

universe u

namespace AlgebraicGeometry

/-- Quotienting twice by nested ideals is quotienting once by the larger one. -/
public noncomputable def quotientQuotientRingEquiv
    {R : Type*} [CommRing R] (I J : Ideal R) (h : I ≤ J) :
    ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) ≃+* R ⧸ J :=
  (Ideal.quotEquivOfEq (Ideal.Quotient.factor_ker h).symm).trans
    ((Ideal.Quotient.factor h).quotientKerEquivOfSurjective
      (Ideal.Quotient.factor_surjective h))

/-- For a surjection `A → B`, the depth of `B` over `A` is its depth over itself. -/
private lemma depth_eq_depth_self_of_surjective
    {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsLocalRing A]
    [Algebra A B] [IsLocalRing B] [IsNoetherianRing B]
    (hsurj : Function.Surjective (algebraMap A B)) :
    (Module.depth A (IsLocalRing.maximalIdeal A) B : WithBot ℕ∞) =
      Module.depth B (IsLocalRing.maximalIdeal B) B := by
  let _ : IsScalarTower A B B := IsScalarTower.of_algebraMap_eq' rfl
  have hmap := Module.depth_eq_depth_map_algebraMap (A := A) (B := B) hsurj
    (IsLocalRing.maximalIdeal A) B
  rw [IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) hsurj] at hmap
  exact congrArg (fun d : ℕ∞ => (d : WithBot ℕ∞)) hmap

/-- A Noetherian local quotient of a Noetherian local ring is Cohen–Macaulay as soon as its
depth over the base agrees with its own dimension. -/
private lemma isCohenMacaulayLocalRing_of_depth_quotient
    {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsLocalRing A]
    [Algebra A B] [IsLocalRing B] [IsNoetherianRing B]
    (hsurj : Function.Surjective (algebraMap A B))
    (hdepth : (Module.depth A (IsLocalRing.maximalIdeal A) B : WithBot ℕ∞) =
      ringKrullDim B) : IsCohenMacaulayLocalRing B :=
  (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay B).mpr
    ((depth_eq_depth_self_of_surjective hsurj).symm.trans hdepth)

/-- Conversely, a Cohen–Macaulay local quotient has depth over the base equal to its
dimension. -/
private lemma depth_quotient_eq_of_isCohenMacaulayLocalRing
    {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsLocalRing A]
    [Algebra A B] [IsLocalRing B] [IsNoetherianRing B]
    (hsurj : Function.Surjective (algebraMap A B))
    (hB : IsCohenMacaulayLocalRing B) :
    (Module.depth A (IsLocalRing.maximalIdeal A) B : WithBot ℕ∞) = ringKrullDim B :=
  (depth_eq_depth_self_of_surjective hsurj).trans
    ((isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay B).mp hB)

/-- The maximal ideal of `B ⧸ I` extends in `C ⧸ I C` to the extension of the maximal ideal
of `B`. -/
private lemma map_maximalIdeal_quotient_map_eq
    {B C : Type*} [CommRing B] [CommRing C] [IsLocalRing B] [Algebra B C]
    (I : Ideal B) [IsLocalRing (B ⧸ I)] :
    (IsLocalRing.maximalIdeal (B ⧸ I)).map
        (algebraMap (B ⧸ I) (C ⧸ I.map (algebraMap B C))) =
      ((IsLocalRing.maximalIdeal B).map (algebraMap B C)).map
        (Ideal.Quotient.mk (I.map (algebraMap B C))) := by
  let _ : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hcomp : (algebraMap (B ⧸ I) (C ⧸ I.map (algebraMap B C))).comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk (I.map (algebraMap B C))).comp (algebraMap B C) := by
    ext b
    change Ideal.quotientMap _ (algebraMap B C) Ideal.le_comap_map (Ideal.Quotient.mk I b) = _
    simp
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective, Ideal.map_map, hcomp, ← Ideal.map_map]

/-- The map `B ⧸ I → C ⧸ I C` induced by a local homomorphism of local rings is local. -/
private lemma isLocalHom_algebraMap_quotient_map
    {B C : Type*} [CommRing B] [CommRing C] [IsLocalRing B] [IsLocalRing C] [Algebra B C]
    [IsLocalHom (algebraMap B C)] (I : Ideal B) [IsLocalRing (B ⧸ I)]
    [IsLocalRing (C ⧸ I.map (algebraMap B C))] :
    IsLocalHom (algebraMap (B ⧸ I) (C ⧸ I.map (algebraMap B C))) := by
  refine ((IsLocalRing.local_hom_TFAE _).out 3 1).mp ?_
  rw [map_maximalIdeal_quotient_map_eq]
  calc _ ≤ (IsLocalRing.maximalIdeal C).map (Ideal.Quotient.mk (I.map (algebraMap B C))) :=
        Ideal.map_mono (IsLocalRing.map_maximalIdeal_le (algebraMap B C))
    _ = _ := IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective

/-- **The flat local criterion for Cohen–Macaulayness of a quotient.** For a flat local
homomorphism `B → C` and an ideal `I ≤ 𝔪_B`, the ring `C/IC` is Cohen–Macaulay precisely when
`B/I` and the closed fibre `C/𝔪_B C` are. -/
private lemma isCohenMacaulayLocalRing_quotientMap_iff
    {B C : Type*} [CommRing B] [CommRing C]
    [IsLocalRing B] [IsLocalRing C]
    [Algebra B C] [IsLocalHom (algebraMap B C)] [Module.Flat B C]
    (I : Ideal B) (hI : I ≤ IsLocalRing.maximalIdeal B)
    [IsNoetherianRing (B ⧸ I)] [IsLocalRing (B ⧸ I)]
    [IsNoetherianRing (C ⧸ I.map (algebraMap B C))]
    [IsLocalRing (C ⧸ I.map (algebraMap B C))]
    [IsNoetherianRing (C ⧸ (IsLocalRing.maximalIdeal B).map (algebraMap B C))]
    [IsLocalRing (C ⧸ (IsLocalRing.maximalIdeal B).map (algebraMap B C))] :
    IsCohenMacaulayLocalRing (C ⧸ I.map (algebraMap B C)) ↔
      (IsCohenMacaulayLocalRing (B ⧸ I) ∧
        IsCohenMacaulayLocalRing
          (C ⧸ (IsLocalRing.maximalIdeal B).map (algebraMap B C))) := by
  let β : B →+* C := algebraMap B C
  let J := I.map β
  let K := (IsLocalRing.maximalIdeal B).map β
  let D := B ⧸ I
  let E := C ⧸ J
  let F := C ⧸ K
  let γ : D →+* E := algebraMap D E
  let _ : Module.Flat D E := flat_quotient_map I
  let _ : IsLocalHom γ := isLocalHom_algebraMap_quotient_map I
  let L := (IsLocalRing.maximalIdeal D).map γ
  have hL : L = K.map (Ideal.Quotient.mk J) := map_maximalIdeal_quotient_map_eq I
  have hJK : J ≤ K := Ideal.map_mono hI
  let eClosed : (E ⧸ L) ≃+* F :=
    (Ideal.quotEquivOfEq hL).trans (quotientQuotientRingEquiv J K hJK)
  let _ : IsLocalRing (E ⧸ L) := eClosed.symm.isLocalRing
  let _ : IsNoetherianRing (E ⧸ L) := isNoetherianRing_of_ringEquiv _ eClosed.symm
  have hCrit := Module.isMaximalCohenMacaulay_self_iff_of_flat D E
  constructor
  · intro hE
    obtain ⟨hDmax, hdepth⟩ :=
      hCrit.mp ((isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay E).mp hE)
    exact ⟨(isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay D).mpr hDmax,
      (isCohenMacaulayLocalRing_iff_of_ringEquiv eClosed).mp
        (isCohenMacaulayLocalRing_of_depth_quotient Ideal.Quotient.mk_surjective hdepth)⟩
  · rintro ⟨hD, hF⟩
    refine (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay E).mpr
      (hCrit.mpr ⟨(isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay D).mp hD, ?_⟩)
    exact depth_quotient_eq_of_isCohenMacaulayLocalRing Ideal.Quotient.mk_surjective
      ((isCohenMacaulayLocalRing_iff_of_ringEquiv eClosed).mpr hF)

/-- In a tower of local homomorphisms whose upper step is flat, flatness of the composite
descends to the lower step. -/
private theorem flat_left_of_flat_comp_of_local_homs
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    (α : A →+* B) (β : B →+* C) [IsLocalHom α] [IsLocalHom β]
    (hβ : β.Flat) (hcomp : (β.comp α).Flat) : α.Flat := by
  let _ : Algebra A B := α.toAlgebra
  let _ : Algebra B C := β.toAlgebra
  let _ : Algebra A C := (β.comp α).toAlgebra
  let _ : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Flat A C := RingHom.flat_algebraMap_iff.mpr hcomp
  have : Module.Flat B C := RingHom.flat_algebraMap_iff.mpr hβ
  have : Module.FaithfullyFlat B C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact RingHom.flat_algebraMap_iff.mp
    (Stacks.Flatness.NilpotentFibreCriterion.flat_of_flat_of_faithfullyFlat (R := A) (S := B) C)

/-- Noetherianity descends along a flat local homomorphism with Noetherian target. -/
private alias isNoetherianRing_of_flat_local_hom :=
  Stacks.Depth.FlatLocalFibreRing.isNoetherianRing_of_flat_of_isLocalHom

/-- Extending the maximal ideal of a stalk of `Z` along the stalk maps of `g` and then `f` is
extending it along the stalk map of `f ≫ g`. -/
private theorem map_map_stalkMap_maximalIdeal_eq
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    Ideal.map (f.stalkMap x).hom (Ideal.map (g.stalkMap (f x)).hom
      (IsLocalRing.maximalIdeal (Z.presheaf.stalk (g (f x))))) =
    Ideal.map ((f ≫ g).stalkMap x).hom
      (IsLocalRing.maximalIdeal (Z.presheaf.stalk (g (f x)))) := by
  dsimp
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp, Ideal.map_map]
  rfl

/-- If the fibre of `f ≫ g` through `x` is locally Noetherian and `f` is flat at `x`, then the
local ring of the fibre of `g` at the image of `x` is Noetherian. -/
private theorem isNoetherianRing_gFiberStalk_of_flatAt_f_compFiber
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hgf : IsLocallyNoetherian ((f ≫ g).fiber ((f ≫ g) x)))
    (hflat : IsFlatAt f.toLRSHom.toShHom x) :
    IsNoetherianRing ((g.fiber (g (f x))).presheaf.stalk (g.asFiber (f x))) := by
  let _ : IsLocallyNoetherian ((f ≫ g).fiber ((f ≫ g) x)) := hgf
  let A := Z.presheaf.stalk (g (f x))
  let B := Y.presheaf.stalk (f x)
  let C := X.presheaf.stalk x
  let α := (g.stalkMap (f x)).hom
  let _ : Algebra B C := (f.stalkMap x).hom.toAlgebra
  let β : B →+* C := algebraMap B C
  let I := Ideal.map α (IsLocalRing.maximalIdeal A)
  let J := I.map β
  let eG := quotientStalkEquivFiberStalk g (f x)
  let eC₀ := quotientStalkEquivFiberStalk (f ≫ g) x
  let _ : IsLocalRing (B ⧸ I) := eG.symm.isLocalRing
  have hJ : J = Ideal.map ((f ≫ g).stalkMap x).hom (IsLocalRing.maximalIdeal A) :=
    map_map_stalkMap_maximalIdeal_eq f g x
  let eC := (Ideal.quotEquivOfEq hJ).trans eC₀
  let _ : IsLocalRing (C ⧸ J) := eC.symm.isLocalRing
  let _ : IsNoetherianRing (C ⧸ J) := isNoetherianRing_of_ringEquiv _ eC.symm
  let _ : IsLocalHom (algebraMap B C) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  let _ : Module.Flat B C := RingHom.flat_algebraMap_iff.mpr hflat
  let D := B ⧸ I
  let E := C ⧸ J
  let _ : IsLocalHom (algebraMap D E) := isLocalHom_algebraMap_quotient_map I
  let _ : Module.Flat D E := flat_quotient_map I
  let _ : IsNoetherianRing D := isNoetherianRing_of_flat_local_hom D E
  exact isNoetherianRing_of_ringEquiv _ eG

/-- If the fibre of `f ≫ g` through `x` is locally Noetherian, then the local ring of the fibre
of `f` at `x` is Noetherian. -/
private theorem isNoetherianRing_fFiberStalk_of_compFiber
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hgf : IsLocallyNoetherian ((f ≫ g).fiber ((f ≫ g) x))) :
    IsNoetherianRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
  let _ : IsLocallyNoetherian ((f ≫ g).fiber ((f ≫ g) x)) := hgf
  let A := Z.presheaf.stalk (g (f x))
  let B := Y.presheaf.stalk (f x)
  let C := X.presheaf.stalk x
  let α := (g.stalkMap (f x)).hom
  let β := (f.stalkMap x).hom
  let I := Ideal.map α (IsLocalRing.maximalIdeal A)
  let J := I.map β
  let K := (IsLocalRing.maximalIdeal B).map β
  let eC₀ := quotientStalkEquivFiberStalk (f ≫ g) x
  have hJ : J = Ideal.map ((f ≫ g).stalkMap x).hom (IsLocalRing.maximalIdeal A) :=
    map_map_stalkMap_maximalIdeal_eq f g x
  let eC := (Ideal.quotEquivOfEq hJ).trans eC₀
  let _ : IsNoetherianRing (C ⧸ J) := isNoetherianRing_of_ringEquiv _ eC.symm
  have hJK : J ≤ K := Ideal.map_mono (IsLocalRing.map_maximalIdeal_le α)
  let _ : IsNoetherianRing (C ⧸ K) := isNoetherianRing_of_surjective (C ⧸ J) (C ⧸ K)
    (Ideal.Quotient.factor hJK) (Ideal.Quotient.factor_surjective hJK)
  exact isNoetherianRing_of_ringEquiv _ (quotientStalkEquivFiberStalk f x)

/-- **Pointwise composition, in unfolded form.** For `f` flat at `x`, the composite is flat at
`x` with Cohen–Macaulay fibre local ring exactly when both factors are. -/
private theorem isCohenMacaulayAt_comp_iff_of_flatAt
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    [IsNoetherianRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x))]
    [IsNoetherianRing ((g.fiber (g (f x))).presheaf.stalk (g.asFiber (f x)))]
    [IsNoetherianRing (((f ≫ g).fiber ((f ≫ g) x)).presheaf.stalk ((f ≫ g).asFiber x))]
    (hflat : IsFlatAt f.toLRSHom.toShHom x) :
    (IsFlatAt (f ≫ g).toLRSHom.toShHom x ∧
      IsCohenMacaulayLocalRing
        (((f ≫ g).fiber ((f ≫ g) x)).presheaf.stalk ((f ≫ g).asFiber x))) ↔
    ((IsFlatAt f.toLRSHom.toShHom x ∧
      IsCohenMacaulayLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) ∧
     (IsFlatAt g.toLRSHom.toShHom (f x) ∧
      IsCohenMacaulayLocalRing
        ((g.fiber (g (f x))).presheaf.stalk (g.asFiber (f x))))) := by
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
  have hJ : J = Ideal.map ((f ≫ g).stalkMap x).hom (IsLocalRing.maximalIdeal A) :=
    map_map_stalkMap_maximalIdeal_eq f g x
  let eC := (Ideal.quotEquivOfEq hJ).trans eC₀
  let _ : IsLocalRing (C ⧸ J) := eC.symm.isLocalRing
  let _ : IsNoetherianRing (C ⧸ J) := isNoetherianRing_of_ringEquiv _ eC.symm
  let _ : Algebra B C := β.toAlgebra
  let _ : IsLocalHom (algebraMap B C) := inferInstanceAs (IsLocalHom β)
  let _ : Module.Flat B C := RingHom.flat_algebraMap_iff.mpr hflat
  have hCM := isCohenMacaulayLocalRing_quotientMap_iff (B := B) (C := C) I
    (IsLocalRing.map_maximalIdeal_le α)
  have hGF : IsCohenMacaulayLocalRing (B ⧸ I) ↔
      IsCohenMacaulayLocalRing
        ((g.fiber (g (f x))).presheaf.stalk (g.asFiber (f x))) :=
    isCohenMacaulayLocalRing_iff_of_ringEquiv eG
  have hFF : IsCohenMacaulayLocalRing (C ⧸ K) ↔
      IsCohenMacaulayLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    isCohenMacaulayLocalRing_iff_of_ringEquiv eF
  have hCF : IsCohenMacaulayLocalRing (C ⧸ J) ↔
      IsCohenMacaulayLocalRing
        (((f ≫ g).fiber ((f ≫ g) x)).presheaf.stalk ((f ≫ g).asFiber x)) :=
    isCohenMacaulayLocalRing_iff_of_ringEquiv eC
  constructor
  · rintro ⟨hflatComp, hCMComp⟩
    change ((f ≫ g).stalkMap x).hom.Flat at hflatComp
    rw [Scheme.Hom.stalkMap_comp] at hflatComp
    obtain ⟨hCMBase, hCMFiber⟩ := hCM.mp (hCF.mpr hCMComp)
    exact ⟨⟨hflat, hFF.mp hCMFiber⟩,
      ⟨flat_left_of_flat_comp_of_local_homs α β hflat hflatComp, hGF.mp hCMBase⟩⟩
  · rintro ⟨⟨hflatF, hCMF⟩, ⟨hflatG, hCMG⟩⟩
    have hflatComp : IsFlatAt (f ≫ g).toLRSHom.toShHom x := by
      change ((f ≫ g).stalkMap x).hom.Flat
      rw [Scheme.Hom.stalkMap_comp]
      exact RingHom.Flat.comp hflatG hflatF
    exact ⟨hflatComp, hCF.mp (hCM.mpr ⟨hGF.mpr hCMG, hFF.mpr hCMF⟩)⟩

/-- The composite of morphisms Cohen–Macaulay at the relevant points is Cohen–Macaulay at the
point of the source. -/
@[stacks 0C0W "part (1)", ega "IV 6.8.3" "(i), Cohen-Macaulay", ega "IV 6.6.1" "a) of (i)"]
public theorem isCohenMacaulayAt_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hg : ∀ z : Z, IsLocallyNoetherian (g.fiber z))
    (hgf : ∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)) (x : X)
    (hfx : Scheme.Hom.IsCohenMacaulayAt f hf x)
    (hgy : Scheme.Hom.IsCohenMacaulayAt g hg (f x)) :
    Scheme.Hom.IsCohenMacaulayAt (f ≫ g) hgf x := by
  let _ : IsLocallyNoetherian (f.fiber (f x)) := hf (f x)
  let _ : IsLocallyNoetherian (g.fiber (g (f x))) := hg (g (f x))
  let _ : IsLocallyNoetherian ((f ≫ g).fiber ((f ≫ g) x)) := hgf ((f ≫ g) x)
  exact (isCohenMacaulayAt_comp_iff_of_flatAt f g x hfx.1).mpr ⟨hfx, hgy⟩

/-- The composite of Cohen–Macaulay morphisms is Cohen–Macaulay. -/
@[stacks 0C0W "part (2)"]
public theorem isCohenMacaulay_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hg : ∀ z : Z, IsLocallyNoetherian (g.fiber z))
    (hgf : ∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z))
    (hfm : Scheme.Hom.IsCohenMacaulay f hf)
    (hgm : Scheme.Hom.IsCohenMacaulay g hg) :
    Scheme.Hom.IsCohenMacaulay (f ≫ g) hgf := fun x =>
  isCohenMacaulayAt_comp f g hf hg hgf x (hfm x) (hgm (f x))

/-- If the composite is Cohen–Macaulay at `x` and `f` is flat at `x`, then `f` is Cohen–Macaulay
at `x`. -/
@[stacks 0C0W "part (3), first conclusion"]
public theorem isCohenMacaulayAt_left_of_comp_of_flatAt {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hgf : ∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)) (x : X)
    (hcomp : Scheme.Hom.IsCohenMacaulayAt (f ≫ g) hgf x)
    (hflat : IsFlatAt f.toLRSHom.toShHom x) :
    Scheme.Hom.IsCohenMacaulayAt f hf x := by
  let _ : IsLocallyNoetherian (f.fiber (f x)) := hf (f x)
  let _ : IsLocallyNoetherian ((f ≫ g).fiber ((f ≫ g) x)) := hgf ((f ≫ g) x)
  let _ : IsNoetherianRing ((g.fiber (g (f x))).presheaf.stalk (g.asFiber (f x))) :=
    isNoetherianRing_gFiberStalk_of_flatAt_f_compFiber f g x (hgf ((f ≫ g) x)) hflat
  exact ((isCohenMacaulayAt_comp_iff_of_flatAt f g x hflat).mp hcomp).1

/-- If the composite is Cohen–Macaulay at `x` and `f` is flat at `x`, then `g` is Cohen–Macaulay
at `f x`. -/
@[stacks 0C0W "part (3), second conclusion"]
public theorem isCohenMacaulayAt_right_of_comp_of_flatAt {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : ∀ z : Z, IsLocallyNoetherian (g.fiber z))
    (hgf : ∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)) (x : X)
    (hcomp : Scheme.Hom.IsCohenMacaulayAt (f ≫ g) hgf x)
    (hflat : IsFlatAt f.toLRSHom.toShHom x) :
    Scheme.Hom.IsCohenMacaulayAt g hg (f x) := by
  let _ : IsLocallyNoetherian (g.fiber (g (f x))) := hg (g (f x))
  let _ : IsLocallyNoetherian ((f ≫ g).fiber ((f ≫ g) x)) := hgf ((f ≫ g) x)
  let _ : IsNoetherianRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    isNoetherianRing_fFiberStalk_of_compFiber f g x (hgf ((f ≫ g) x))
  exact ((isCohenMacaulayAt_comp_iff_of_flatAt f g x hflat).mp hcomp).2

/-- If the composite is Cohen–Macaulay and `f` is flat, then `f` is Cohen–Macaulay. -/
@[stacks 0C0W "part (4), first conclusion"]
public theorem isCohenMacaulay_left_of_comp_of_flat {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hgf : ∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z))
    (hcomp : Scheme.Hom.IsCohenMacaulay (f ≫ g) hgf)
    (hflat : Flat f) : Scheme.Hom.IsCohenMacaulay f hf := fun x =>
  isCohenMacaulayAt_left_of_comp_of_flatAt f g hf hgf x (hcomp x) (Flat.stalkMap f x)

/-- If the composite is Cohen–Macaulay and `f` is flat, then `g` is Cohen–Macaulay at every
point in the image of `f`. -/
@[stacks 0C0W "part (4), second conclusion",
  ega "IV 6.6.1" "a) of (ii)",
  ega "IV 6.8.3" "(ii), Cohen-Macaulay"]
public theorem isCohenMacaulayAt_right_of_comp_of_flat {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : ∀ z : Z, IsLocallyNoetherian (g.fiber z))
    (hgf : ∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z))
    (hcomp : Scheme.Hom.IsCohenMacaulay (f ≫ g) hgf)
    (hflat : Flat f) (x : X) :
    Scheme.Hom.IsCohenMacaulayAt g hg (f x) :=
  isCohenMacaulayAt_right_of_comp_of_flatAt f g hg hgf x (hcomp x) (Flat.stalkMap f x)

end AlgebraicGeometry
