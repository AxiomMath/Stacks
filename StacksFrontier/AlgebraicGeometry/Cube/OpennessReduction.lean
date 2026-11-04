module

public import StacksFrontier.AlgebraicGeometry.Cube.OpennessGenerator
public import StacksFrontier.AlgebraicGeometry.Cube.SectionNeighbourhood
public import StacksFrontier.Homology.Perfect.TwoFaceDegreeZeroLift

/-!
# The openness step of the theorem of the cube, from its fibrewise inputs

With `Q`, `qR`, `C`, `DX`, `DY`, `ΦX` and `ΦY` as in `AlgebraicGeometry.Cube.Openness.Q` and the
definitions after it, this file reduces the openness step of the theorem of the cube
([Stacks, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3)) to four statements about
the base changes to `κ(𝔭)` of the Čech complexes `C`, `DX`, `DY`: the two injectivities
`h0`, `h1` (the latter is the Künneth input) and the liftability of face cocycles `hsX`,
`hsY`. Given these, the trivializing section of the fibre over `𝔭` lifts, up to a scalar
outside `𝔭`, to a global section of `L`
(`StacksDraft.ConeLift.exists_cocycle_lift_of_two_faces`, the module-theoretic heart of
[Stacks, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)), and a global section that
trivializes a fibre trivializes `L` over a neighbourhood of it
(`AlgebraicGeometry.Cube.exists_basicOpen_nonempty_iso_unit`).

## Main results

* `AlgebraicGeometry.Cube.Openness.exists_basicOpen_of_fibre_inputs`: the reduction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open StacksDraft.ConeLift (bcObj bcMap bcUnit)

universe u

noncomputable section

namespace AlgebraicGeometry.Cube.Openness

attribute [local instance 10000] HasDerivedCategory.standard

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  [IsProper f] [IsProper g]
  (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
  (R : Type u) [CommRing R] [IsNoetherianRing R] [Algebra k R]
  {I J : Type u} [Fintype I] [Fintype J] [LinearOrder (I × J)]
  (UX : I → X.Opens) (UY : J → Y.Opens)
  (hUXa : ∀ a, IsAffineOpen (UX a)) (hUYa : ∀ b, IsAffineOpen (UY b))
  (hUX : (⊤ : X.Opens) = ⨆ a, UX a) (hUY : (⊤ : Y.Opens) = ⨆ b, UY b)
  (L : (Q f g R).Modules)

/-- The alternating Čech complex of an invertible module on a proper flat scheme of finite type
over a Noetherian ring has flat terms and perfect image in the derived category. -/
private theorem flat_and_isPerfect_of_isInvertible {R : Type u} [CommRing R] [IsNoetherianRing R]
    {Z : Scheme.{u}} (h : Z ⟶ Spec (.of R)) [IsProper h] [Flat h]
    {K : Type u} [Finite K] [LinearOrder K] (V : K → Z.Opens) (hV : (⊤ : Z.Opens) = ⨆ i, V i)
    (hVa : ∀ i, IsAffineOpen (V i)) (M : Z.Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.property M) :
    (∀ n, Module.Flat R ((Stacks.Cech.alternatingCechModuleComplex h V M).X n)) ∧
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
        ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).obj
          (Stacks.Cech.alternatingCechModuleComplex h V M))) := by
  have := Fintype.ofFinite K
  obtain ⟨hcoh, hflat⟩ := coherent_flat_of_isInvertible h M hM
  have : M.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M).1
  exact ⟨Stacks.Cech.alternatingCechModuleComplex_flat h V M hVa hflat,
    isPerfect_extend_alternatingCechModuleComplex h V M hV hVa
      (fun _ s => Stacks.Cech.inter_isAffineOpen h V hVa s) hflat⟩

include hUXa hUYa hUX hUY in
/-- **The openness step of the theorem of the cube, from its fibrewise inputs.** -/
theorem exists_basicOpen_of_fibre_inputs
    (hL : Stacks.SheafOfModules.IsInvertible (Q f g R).presheaf (Q f g R).ringCatIsSheaf L)
    (𝔭 : PrimeSpectrum R)
    (τ : (Scheme.Modules.pullback (pullback.fst (qR f g R)
        (Spec.map (CommRingCat.ofHom (algebraMap R 𝔭.asIdeal.ResidueField))))).obj L ≅
      SheafOfModules.unit _)
    (h0 : ∀ z : bcObj (algebraMap R 𝔭.asIdeal.ResidueField) ((C f g R UX UY L).X 0),
      (bcMap (algebraMap R 𝔭.asIdeal.ResidueField) ((C f g R UX UY L).d 0 1)).hom z = 0 →
      (bcMap (algebraMap R 𝔭.asIdeal.ResidueField) ((ΦX f g y hy R UX UY L).f 0)).hom z = 0 →
        z = 0)
    (h1 : ∀ c : bcObj (algebraMap R 𝔭.asIdeal.ResidueField) ((C f g R UX UY L).X 1),
      (bcMap (algebraMap R 𝔭.asIdeal.ResidueField) ((C f g R UX UY L).d 1 2)).hom c = 0 →
      ∀ (eX : bcObj (algebraMap R 𝔭.asIdeal.ResidueField) ((DX f g y hy R UX UY L).X 0))
        (eY : bcObj (algebraMap R 𝔭.asIdeal.ResidueField) ((DY f g x hx R UX UY L).X 0)),
      (bcMap (algebraMap R 𝔭.asIdeal.ResidueField) ((ΦX f g y hy R UX UY L).f 1)).hom c =
        (bcMap (algebraMap R 𝔭.asIdeal.ResidueField) ((DX f g y hy R UX UY L).d 0 1)).hom eX →
      (bcMap (algebraMap R 𝔭.asIdeal.ResidueField) ((ΦY f g x hx R UX UY L).f 1)).hom c =
        (bcMap (algebraMap R 𝔭.asIdeal.ResidueField) ((DY f g x hx R UX UY L).d 0 1)).hom eY →
      ∃ c' : bcObj (algebraMap R 𝔭.asIdeal.ResidueField) ((C f g R UX UY L).X 0),
        (bcMap (algebraMap R 𝔭.asIdeal.ResidueField) ((C f g R UX UY L).d 0 1)).hom c' = c)
    (hsX : ∀ z : bcObj (algebraMap R 𝔭.asIdeal.ResidueField) ((DX f g y hy R UX UY L).X 0),
      (bcMap (algebraMap R 𝔭.asIdeal.ResidueField) ((DX f g y hy R UX UY L).d 0 1)).hom z = 0 →
      ∃ z' : (DX f g y hy R UX UY L).X 0, ((DX f g y hy R UX UY L).d 0 1).hom z' = 0 ∧
        ∃ t : R, t ∉ 𝔭.asIdeal ∧ (bcUnit (algebraMap R 𝔭.asIdeal.ResidueField) _).hom z' = t • z)
    (hsY : ∀ z : bcObj (algebraMap R 𝔭.asIdeal.ResidueField) ((DY f g x hx R UX UY L).X 0),
      (bcMap (algebraMap R 𝔭.asIdeal.ResidueField) ((DY f g x hx R UX UY L).d 0 1)).hom z = 0 →
      ∃ z' : (DY f g x hx R UX UY L).X 0, ((DY f g x hx R UX UY L).d 0 1).hom z' = 0 ∧
        ∃ t : R, t ∉ 𝔭.asIdeal ∧
          (bcUnit (algebraMap R 𝔭.asIdeal.ResidueField) _).hom z' = t • z) :
    ∃ r : R, r ∉ 𝔭.asIdeal ∧ Nonempty ((Scheme.Modules.pullback
      ((qR f g R) ⁻¹ᵁ PrimeSpectrum.basicOpen (R := CommRingCat.of R) r).ι).obj L ≅
        SheafOfModules.unit _) := by
  classical
  have hL' : AlgebraicGeometry.SheafOfModules.IsInvertible (Q f g R).presheaf
      (Q f g R).ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL
  obtain ⟨hcoh, hflat⟩ := coherent_flat_of_isInvertible (qR f g R) L hL'
  have := hcoh
  have : L.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent L).1
  -- the three complexes: flatness and perfectness
  have hW := iSup_W f g R UX UY hUX hUY
  have hWa := isAffineOpen_W f g R UX UY hUXa hUYa
  obtain ⟨hflatC, hCp⟩ := flat_and_isPerfect_of_isInvertible (qR f g R) _ hW hWa L hL'
  obtain ⟨hflatX, hXp⟩ := flat_and_isPerfect_of_isInvertible (qX f R) _
    (Stacks.AlgebraicGeometry.ProperFlatGlobalSections.top_eq_iSup_preimage (jX f g y hy R) _ hW)
    (fun s => (hWa s).preimage _) _ (isInvertible_pullback (jX f g y hy R) L)
  obtain ⟨hflatY, hYp⟩ := flat_and_isPerfect_of_isInvertible (qY g R) _
    (Stacks.AlgebraicGeometry.ProperFlatGlobalSections.top_eq_iSup_preimage (jY f g x hx R) _ hW)
    (fun s => (hWa s).preimage _) _ (isInvertible_pullback (jY f g x hx R) L)
  have := hflatC
  have := hflatX
  have := hflatY
  have hb : ∀ {Z : Scheme.{u}} (h : Z ⟶ Spec (.of R)) (V : I × J → Z.Opens) (N : Z.Modules)
      (n : ℕ), Fintype.card (I × J) ≤ n →
      IsZero ((Stacks.Cech.alternatingCechModuleComplex h V N).X n) := fun h V N n hn =>
    @ModuleCat.isZero_of_subsingleton _ _ _ (Stacks.Cech.subsingleton_alternatingSubmodule h V N hn)
  -- the trivializing section of the fibre
  obtain ⟨x0, hx0, hdict⟩ := exists_fibre_cocycle (algebraMap R 𝔭.asIdeal.ResidueField)
    (qR f g R) (pullback.snd (qR f g R)
      (Spec.map (CommRingCat.ofHom (algebraMap R 𝔭.asIdeal.ResidueField))))
    (pullback.fst _ _) (IsPullback.of_hasPullback _ _) L (W f g R UX UY) hWa hW τ
  -- the lift
  obtain ⟨c, hc, s, hs, hcx⟩ := StacksDraft.ConeLift.exists_cocycle_lift_of_two_faces
    𝔭.asIdeal (ΦX f g y hy R UX UY L) (ΦY f g x hx R UX UY L) (Fintype.card (I × J))
    (hb _ _ _) (hb _ _ _) (hb _ _ _) hCp hXp hYp h0 h1 hsX hsY x0 hx0
  obtain ⟨σ, hσ⟩ := hdict c hc s (fun h => hs (Ideal.algebraMap_residueField_eq_zero.1 h)) hcx
  exact exists_basicOpen_nonempty_iso_unit (qR f g R) L hL 𝔭 σ τ hσ

end AlgebraicGeometry.Cube.Openness

end

end
