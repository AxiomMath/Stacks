module

public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom
public import StacksFrontier.Homology.TorAmplitude.KFlatRepresentative
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBifunctorIso
public import StacksFrontier.RingTheory.LocalCohomology.CechFormula.TensorCompatibility

/-!
# Local cohomology passes inside derived Hom

Let `I = (f₁, …, f_r)` be a finitely generated ideal of a commutative ring `A` and let
`Z = V(I)`. For `Y` pseudo-coherent and `W` bounded below there is a canonical isomorphism

`RΓ_Z(RHom_A(Y, W)) ≅ RHom_A(Y, RΓ_Z(W))`

in `D(A)`, natural in `Y`.

This is not a statement about local cohomology at all once the Čech formula is in hand. By
Stacks 0A6R (`Stacks.LocalCohomology.CechFormula.localCohomologyCechIso`) local cohomology is
tensoring with a fixed object, the extended alternating Čech complex `C` of `f`; so both sides
are values of the derived tensor--Hom diagonal `C ⊗ᴸ RHom(Y, W) ⟶ RHom(Y, C ⊗ᴸ W)` of
Stacks 0BYN, and the isomorphism is case (3) of Stacks 0ATK: the diagonal is invertible when the
internal-Hom source is pseudo-coherent, its target is bounded below, and the tensor factor has
Tor amplitude bounded below. The Čech complex supplies the last hypothesis on the nose — it is a
bounded complex of flat modules in degrees `≥ 0` — so the only hypotheses left are the two on
`Y` and `W`.

## Main definitions

* `Stacks.LocalCohomology.CechFormula.localCohomologyDerivedHomMor` — the canonical morphism
  `RΓ_Z(RHom_A(Y, W)) ⟶ RHom_A(Y, RΓ_Z(W))`, the Čech reading of the diagonal of Stacks 0BYN.

## Main results

* `Stacks.LocalCohomology.CechFormula.cechRegularObject_torAmplitudeAbove` — the Čech object has
  Tor amplitude in `[0, ∞]`.
* `Stacks.LocalCohomology.CechFormula.localCohomologyDerivedHomMor_naturality` — the morphism is
  natural in `Y`.
* `Stacks.LocalCohomology.CechFormula.isIso_localCohomologyDerivedHomMor` — **it is invertible**
  for `Y` pseudo-coherent and `W` bounded below.
* `Stacks.LocalCohomology.CechFormula.nonempty_localCohomology_derivedHom_iso` — the resulting
  isomorphism.

## Implementation notes

The tensor--Hom diagonal of Stacks 0BYN is stated for the tensor product of the fixed
tensor--Hom adjunction `StacksDraft.DerivedHom.derivedHomAdjunction`, while the Čech formula is
stated for the canonical derived tensor product of Stacks 0BYI. The two are identified by
`Dualizing.derivedHomAdjunctionTensorNatIso`, naturally in both variables, which is what lets the
Čech isomorphism be read on the diagonal's tensor factor; the Tor-amplitude hypothesis of
Stacks 0ATK is phrased for the canonical tensor product and so needs no such translation.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
* [Stacks Project, Tag 0BYL](https://stacks.math.columbia.edu/tag/0BYL)
* [Stacks Project, Tag 0BYN](https://stacks.math.columbia.edu/tag/0BYN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology.CechFormula

variable {A : Type u} [CommRing A] {r : ℕ}

/-- The extended alternating Čech complex of the regular module is concentrated in degrees
`≥ 0`. -/
theorem cechRegularComplex_isStrictlyGE (f : Fin r → A) :
    (cechRegularComplex.{u, u} f).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro q hq
  exact isZero_extendedCechComplex_X f (regularModule.{u, u} A) q (Or.inl hq)

open StacksDraft.TorAmplitude in
/-- **The Čech object has Tor amplitude in `[0, ∞]`.** It is represented by a K-flat complex of
flat modules concentrated in degrees `≥ 0`, which is the criterion of Stacks 0BYL. This is the
hypothesis on the tensor factor in case (3) of Stacks 0ATK. -/
theorem cechRegularObject_torAmplitudeAbove (f : Fin r → A) (M : ModuleCat.{u} A) (i : ℤ)
    (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj
          (cechRegularObject.{u, u} f)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))) := by
  refine (hasTorAmplitudeAbove_iff_exists_kFlat_flat_representative_canonical
    (cechRegularObject.{u, u} f) 0).2 ?_ M i hi
  exact ⟨cechRegularComplex.{u, u} f, cechRegular_isKFlat f, flat_cechRegularComplex_X f,
    cechRegularComplex_isStrictlyGE f, ⟨Iso.refl _⟩⟩

section Diagonal

variable (I : Ideal A) (hI : I.FG) (f : Fin r → A) (hf : Ideal.span (Set.range f) = I)

/-- The Čech object read as the tensor factor of the fixed tensor--Hom adjunction: local
cohomology of `X` is `C ⊗ᴸ X` for that adjunction's tensor product. -/
def localCohomologyTensorIso (X : DerivedCategory (ModuleCat.{u} A)) :
    (localCohomologyEndofunctor A I hI).obj X ≅
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).tensor.obj
        (cechRegularObject.{u, u} f, X) :=
  (localCohomologyCechIso A I hI f hf).app X ≪≫
    (Dualizing.derivedHomAdjunctionTensorNatIso A).app (cechRegularObject.{u, u} f, X)

/-- **Local cohomology passes inside derived Hom.** The canonical morphism
`RΓ_Z(RHom_A(Y, W)) ⟶ RHom_A(Y, RΓ_Z(W))`: the Čech formula turns both sides into values of the
derived tensor--Hom diagonal of Stacks 0BYN at the extended Čech complex. -/
def localCohomologyDerivedHomMor (W Y : DerivedCategory (ModuleCat.{u} A)) :
    (localCohomologyEndofunctor A I hI).obj
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj (Opposite.op Y, W)) ⟶
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op Y, (localCohomologyEndofunctor A I hI).obj W) :=
  (localCohomologyTensorIso I hI f hf
      ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op Y, W))).hom ≫
    StacksDraft.DerivedHom.derivedTensorHomDiagonal (cechRegularObject.{u, u} f) W Y ≫
    ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.mapIso
      ((Iso.refl (Opposite.op Y)).prod (localCohomologyTensorIso I hI f hf W).symm)).hom

/-- The morphism of `Stacks.LocalCohomology.CechFormula.localCohomologyDerivedHomMor` is natural
in the internal-Hom source. Each of its three factors is: the Čech formula and the comparison of
the two derived tensor products are isomorphisms of functors, the diagonal of Stacks 0BYN is
contravariantly natural in its source, and the last factor is `RHom` of a morphism in the other
variable. -/
theorem localCohomologyDerivedHomMor_naturality (W : DerivedCategory (ModuleCat.{u} A))
    {Y Y' : DerivedCategory (ModuleCat.{u} A)} (g : Y' ⟶ Y) :
    (localCohomologyEndofunctor A I hI).map
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map (g.op, 𝟙 W)) ≫
      localCohomologyDerivedHomMor I hI f hf W Y' =
    localCohomologyDerivedHomMor I hI f hf W Y ≫
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
        (g.op, 𝟙 ((localCohomologyEndofunctor A I hI).obj W)) := by
  have h12 : (localCohomologyEndofunctor A I hI).map
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map (g.op, 𝟙 W)) ≫
      (localCohomologyTensorIso I hI f hf
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
          (Opposite.op Y', W))).hom =
      (localCohomologyTensorIso I hI f hf
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
            (Opposite.op Y, W))).hom ≫
        (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).tensor.map
          (𝟙 (cechRegularObject.{u, u} f),
            (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map (g.op, 𝟙 W)) := by
    have h1 := (localCohomologyCechIso A I hI f hf).hom.naturality
      ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
        ((g.op, 𝟙 W) : (Opposite.op Y, W) ⟶ (Opposite.op Y', W)))
    have h2 := (Dualizing.derivedHomAdjunctionTensorNatIso A).hom.naturality
      ((𝟙 (cechRegularObject.{u, u} f),
        (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
          ((g.op, 𝟙 W) : (Opposite.op Y, W) ⟶ (Opposite.op Y', W))) :
        (cechRegularObject.{u, u} f,
            (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
              (Opposite.op Y, W)) ⟶
          (cechRegularObject.{u, u} f,
            (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj (Opposite.op Y', W)))
    simp only [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp] at h2
    dsimp only [localCohomologyTensorIso, Iso.trans_hom, Iso.app_hom,
      localCohomologyEndofunctor, Functor.comp_map,
      CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor]
    rw [reassoc_of% h1, h2, Category.assoc]
  have h3 := (StacksDraft.DerivedHom.derivedTensorHomDiagonal_natural (R := A)).2.2
    (K := cechRegularObject.{u, u} f) (L := W) g
  dsimp only [StacksDraft.DerivedHom.DerivedInternalHom.Model.hom,
    StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor,
    StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction] at h3
  have h4 : (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
        ((g.op, 𝟙 ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).tensor.obj
          (cechRegularObject.{u, u} f, W)))) ≫
      ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.mapIso
        ((Iso.refl (Opposite.op Y')).prod
          (localCohomologyTensorIso I hI f hf W).symm)).hom =
      ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.mapIso
          ((Iso.refl (Opposite.op Y)).prod
            (localCohomologyTensorIso I hI f hf W).symm)).hom ≫
        (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
          (g.op, 𝟙 ((localCohomologyEndofunctor A I hI).obj W)) := by
    dsimp only [Functor.mapIso_hom]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    refine Prod.ext ?_ ?_ <;> simp
  dsimp only [localCohomologyDerivedHomMor, localCohomologyEndofunctor, Functor.comp_map]
  simp only [Category.assoc]
  rw [reassoc_of% h12, reassoc_of% h3, h4]

/-- **Local cohomology passes inside derived Hom.** For `Y` pseudo-coherent and `W` bounded
below, the canonical morphism `RΓ_Z(RHom_A(Y, W)) ⟶ RHom_A(Y, RΓ_Z(W))` is invertible. Its three
factors are the Čech formula, the derived tensor--Hom diagonal of Stacks 0BYN and `RHom` of an
isomorphism; only the middle one carries a hypothesis, and it is case (3) of Stacks 0ATK, whose
condition on the tensor factor the Čech complex satisfies by
`Stacks.LocalCohomology.CechFormula.cechRegularObject_torAmplitudeAbove`. -/
theorem isIso_localCohomologyDerivedHomMor (W Y : DerivedCategory (ModuleCat.{u} A))
    (hY : StacksDraft.PseudoCoherence.IsPseudoCoherent Y)
    (hW : ∃ b : ℤ, DerivedCategory.IsGE W b) :
    IsIso (localCohomologyDerivedHomMor I hI f hf W Y) := by
  have hd : IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal
      (cechRegularObject.{u, u} f) W Y) :=
    Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal
      (cechRegularObject.{u, u} f) W Y 0
      (Or.inr (Or.inr ⟨hY, hW, fun N i hi => cechRegularObject_torAmplitudeAbove f N i hi⟩))
  rw [localCohomologyDerivedHomMor]
  infer_instance

include hf in
/-- **`RΓ_Z(RHom_A(Y, W)) ≅ RHom_A(Y, RΓ_Z(W))`** for `Y` pseudo-coherent and `W` bounded below.
The isomorphism is `Stacks.LocalCohomology.CechFormula.localCohomologyDerivedHomMor`, which is
natural in `Y` by
`Stacks.LocalCohomology.CechFormula.localCohomologyDerivedHomMor_naturality`. -/
theorem nonempty_localCohomology_derivedHom_iso (W Y : DerivedCategory (ModuleCat.{u} A))
    (hY : StacksDraft.PseudoCoherence.IsPseudoCoherent Y)
    (hW : ∃ b : ℤ, DerivedCategory.IsGE W b) :
    Nonempty ((localCohomologyEndofunctor A I hI).obj
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj (Opposite.op Y, W)) ≅
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op Y, (localCohomologyEndofunctor A I hI).obj W)) :=
  have := isIso_localCohomologyDerivedHomMor I hI f hf W Y hY hW
  ⟨asIso (localCohomologyDerivedHomMor I hI f hf W Y)⟩

end Diagonal

end Stacks.LocalCohomology.CechFormula
