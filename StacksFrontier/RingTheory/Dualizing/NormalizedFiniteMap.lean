module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.RingTheory.Dualizing.Normalized
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldShift

/-!
# Normalized dualizing complexes under a finite local map

Let `f : A → B` be a finite local homomorphism of Noetherian local rings and let `K` be a
*normalized* dualizing complex over `A` (`Dualizing.IsNormalizedDualizingComplex`). Then
`RHom_A(B, K)` is a normalized dualizing complex over `B`. This is [Stacks, Tag 0AX1].

That `RHom_A(B, K)` is dualizing is [Stacks, Tag 0AX0]
(`Dualizing.isDualizingComplex_derivedHom_of_finite`), and by [Stacks, Tag 0A7L]
(`Dualizing.derivedHom_localResidueField_iso_shift`) it is normalized *after some shift* `n`. The
content here is that `n = 0`, and it is proved by exhibiting a nonzero morphism from `κ_B` in
degree zero into `RHom_B(κ_B, RHom_A(B, K))`: if `n` were nonzero there would be none, because
`κ_B` in degree zero admits no nonzero morphism to a nonzero shift of itself
(`Dualizing.residueSingle_shift_hom_eq_zero`).

The nonzero morphism is built by transport along adjunctions. Normalization of `K` gives a
nonzero map `κ_A[0] → K` in `D(A)` after restricting scalars, by
`Dualizing.restrictScalarsDerived_adj_derivedHom` ([Stacks, Tag 0A70]); the extension
`κ_A → κ_B` of residue fields is finite, hence splits as a map of `A`-modules
(`Dualizing.residueFieldMap_finite` and
`Dualizing.exists_linearMap_retraction_of_finite_extension`), and composing with the retraction
turns that into a nonzero map `κ_B[0] → K` in `D(A)`. Adjunction again, now along
`A → κ_B`, and the compatibility of derived Hom with composition of ring maps
(`Dualizing.derivedHomCompIso`, [Stacks, Tag 0C0F]) move it to the required morphism in `D(B)`.
Nonvanishing survives each step because every map used is an isomorphism, a split monomorphism,
or an adjunction bijection.

## Main results

* `Dualizing.isNormalizedDualizingComplex_derivedHom` — **[Stacks, Tag 0AX1]**.

## Implementation notes

The splitting of `κ_A → κ_B` is used only as a splitting of `A`-modules, which is why the
residue-field extension is turned into a tower `A → κ_A → κ_B` by hand. The three single-complex
facts the argument needs over a field — that the identity of `κ[0]` is nonzero and that morphisms
into nonzero shifts vanish — are `Dualizing.residueSingle_id_ne_zero` and
`Dualizing.residueSingle_shift_hom_eq_zero`.

Derived categories are at `HasDerivedCategory.standard`, forced by `Dualizing.derivedHom`, which
bakes that model into its own type; see the note in
`StacksFrontier/RingTheory/Dualizing/NormalizedShift.lean`.

## References

* [Stacks Project, Tag 0AX1](https://stacks.math.columbia.edu/tag/0AX1)
* [Stacks Project, Tag 0AX0](https://stacks.math.columbia.edu/tag/0AX0)
* [Stacks Project, Tag 0A7L](https://stacks.math.columbia.edu/tag/0A7L)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0C0F](https://stacks.math.columbia.edu/tag/0C0F)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- For a finite local homomorphism `A → B` of local rings, the residue field `κ_A` is a
retract of `κ_B` as an `A`-module. -/
theorem exists_residueField_retraction
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] (hf : f.Finite) :
    ∃ (inc : (ModuleCat.restrictScalars.{max v u} (IsLocalRing.residue A)).obj
        ((ModuleCat.uliftFunctor.{v} (IsLocalRing.ResidueField A)).obj
          (ModuleCat.of (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A))) ⟶
      (ModuleCat.restrictScalars.{max v u} ((IsLocalRing.residue B).comp f)).obj
        ((ModuleCat.uliftFunctor.{v} (IsLocalRing.ResidueField B)).obj
          (ModuleCat.of (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField B))))
      (ret : (ModuleCat.restrictScalars.{max v u} ((IsLocalRing.residue B).comp f)).obj
        ((ModuleCat.uliftFunctor.{v} (IsLocalRing.ResidueField B)).obj
          (ModuleCat.of (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField B))) ⟶
      (ModuleCat.restrictScalars.{max v u} (IsLocalRing.residue A)).obj
        ((ModuleCat.uliftFunctor.{v} (IsLocalRing.ResidueField A)).obj
          (ModuleCat.of (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A)))),
      inc ≫ ret = 𝟙 _ := by
  let kA := IsLocalRing.ResidueField A
  let kB := IsLocalRing.ResidueField B
  let g := IsLocalRing.ResidueField.map f
  let t := IsLocalRing.residue B |>.comp f
  let _ : Algebra A kA := (IsLocalRing.residue A).toAlgebra
  let _ : Algebra A kB := t.toAlgebra
  let _ : Algebra kA kB := g.toAlgebra
  let _ : IsScalarTower A kA kB := IsScalarTower.of_algebraMap_eq'
    (RingHom.ext fun a => (IsLocalRing.ResidueField.map_residue f a).symm)
  let _ : Module.Finite kA kB := residueFieldMap_finite f hf
  obtain ⟨r, i, hsplit⟩ :=
    exists_linearMap_retraction_of_finite_extension (A := A) (K := kA) (L := kB)
  let X_A₀ := ModuleCat.of A kA
  let X_B₀ := ModuleCat.of A kB
  refine ⟨by
    change (ModuleCat.uliftFunctor.{v} A).obj X_A₀ ⟶
      (ModuleCat.uliftFunctor.{v} A).obj X_B₀
    exact (ModuleCat.uliftFunctor.{v} A).map (ModuleCat.ofHom i), by
    change (ModuleCat.uliftFunctor.{v} A).obj X_B₀ ⟶
      (ModuleCat.uliftFunctor.{v} A).obj X_A₀
    exact (ModuleCat.uliftFunctor.{v} A).map (ModuleCat.ofHom r), ?_⟩
  ext x
  exact ULift.ext _ _ (LinearMap.congr_fun hsplit x.down)

/-- If `A → B` is a finite local homomorphism of local rings and `RHom_A(κ_A, K)` is `κ_A` in
degree zero, then there is a nonzero morphism in `D(A)` from `κ_B` in degree zero to `K`. -/
theorem exists_single_residueField_hom_ne_zero
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] (hf : f.Finite)
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : Nonempty ((derivedHom.{u, v} (IsLocalRing.residue A)).obj K ≅
      (DerivedCategory.singleFunctor
        (ModuleCat.{max v u} (IsLocalRing.ResidueField A)) 0).obj
          ((ModuleCat.uliftFunctor.{v} (IsLocalRing.ResidueField A)).obj
            (ModuleCat.of (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A))))) :
    ∃ w : (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        ((ModuleCat.restrictScalars.{max v u} ((IsLocalRing.residue B).comp f)).obj
          ((ModuleCat.uliftFunctor.{v} (IsLocalRing.ResidueField B)).obj
            (ModuleCat.of (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField B)))) ⟶ K,
      w ≠ 0 := by
  obtain ⟨eA⟩ := hK
  obtain ⟨inc, ret, hsplit⟩ := exists_residueField_retraction.{u, v} f hf
  let kA := IsLocalRing.ResidueField A
  let M_A := (ModuleCat.uliftFunctor.{v} kA).obj (ModuleCat.of kA kA)
  let fA := ModuleCat.restrictScalars.{max v u} (IsLocalRing.residue A)
  let S_A := (DerivedCategory.singleFunctor (ModuleCat.{max v u} kA) 0).obj M_A
  obtain ⟨adjA⟩ := restrictScalarsDerived_adj_derivedHom.{u, v} (IsLocalRing.residue A)
  let uA : fA.mapDerivedCategory.obj S_A ⟶ K :=
    (adjA.homEquiv S_A K).symm eA.inv
  have huA : uA ≠ 0 := by
    intro h
    have heA : eA.inv = 0 :=
      (adjA.homEquiv S_A K).symm.injective (by simpa [uA] using h)
    apply residueSingle_id_ne_zero.{u, v} kA
    simpa [heA] using eA.inv_hom_id.symm
  let uA' : (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (fA.obj M_A) ⟶ K :=
    (fA.mapDerivedCategorySingleFunctor 0).inv.app M_A ≫ uA
  have huA' : uA' ≠ 0 := by simpa [uA'] using huA
  let uA'' : (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj _ ⟶ K :=
    (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map ret ≫ uA'
  have huA'' : uA'' ≠ 0 := by
    intro h
    have hh : (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map inc ≫ uA'' =
        uA' := by
      dsimp only [uA'']
      rw [← Functor.map_comp_assoc, hsplit, CategoryTheory.Functor.map_id, Category.id_comp]
    apply huA'
    simpa [h] using hh.symm
  exact ⟨uA'', huA''⟩

/-- **Stacks Project, Tag 0AX1.** If `A → B` is a finite local homomorphism of Noetherian local
rings and `K` is a normalized dualizing complex over `A`, then `RHom_A(B, K)` is a normalized
dualizing complex over `B`. -/
@[stacks 0AX1,
  stacks 0A7N "the surjective case, a surjection of local rings being a finite local homomorphism"]
theorem isNormalizedDualizingComplex_derivedHom
    {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f] (hf : f.Finite)
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K) :
    IsNormalizedDualizingComplex.{u, v}
      ((derivedHom.{u, v} f).obj K) := by
  obtain ⟨hdual, hnorm⟩ := hK
  have hdualB := isDualizingComplex_derivedHom_of_finite.{u, v} f hf K hdual
  obtain ⟨n, ⟨eB⟩⟩ := derivedHom_localResidueField_iso_shift.{u, v} _ hdualB
  refine ⟨hdualB, ?_⟩
  obtain ⟨w, hw⟩ := exists_single_residueField_hom_ne_zero.{u, v} f hf K hnorm
  let t := IsLocalRing.residue B |>.comp f
  let kB := IsLocalRing.ResidueField B
  let f_t := ModuleCat.restrictScalars.{max v u} t
  let M_B := (ModuleCat.uliftFunctor.{v} kB).obj (ModuleCat.of kB kB)
  let S_B := (DerivedCategory.singleFunctor (ModuleCat.{max v u} kB) 0).obj M_B
  obtain ⟨adjT⟩ := restrictScalarsDerived_adj_derivedHom.{u, v} t
  let wT : f_t.mapDerivedCategory.obj S_B ⟶ K :=
    (f_t.mapDerivedCategorySingleFunctor 0).hom.app M_B ≫ w
  have hwT : wT ≠ 0 := by simpa [wT] using hw
  let uT : S_B ⟶ (derivedHom.{u, v} t).obj K := adjT.homEquiv S_B K wT
  have huT : uT ≠ 0 := fun h =>
    hwT ((adjT.homEquiv S_B K).injective (by simpa [uT] using h))
  obtain ⟨eComp⟩ := derivedHomCompIso.{u, v} f (IsLocalRing.residue B)
  let uB := uT ≫ (eComp.app K).inv
  have huB : uB ≠ 0 := by simpa [uB] using huT
  obtain rfl : n = 0 := by
    by_contra hne
    exact huB ((Preadditive.IsIso.comp_right_eq_zero _ _).mp
      (residueSingle_shift_hom_eq_zero.{u, v} kB n hne (uB ≫ eB.hom)))
  exact ⟨eB ≪≫ shiftZero ℤ _⟩

end Dualizing

end
