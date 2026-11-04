module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.PrincipalDivisorAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.ExtOfComplementDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ExtensionTorsor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ModuleSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperVanishing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafForgetAbelian

/-!
# Cohomological purity for a principal smooth divisor, in `Ext` form

Let `k` be an algebraically closed field, `ℓ ≥ 1` an integer invertible in `k` and `Λ = ℤ/ℓ`. Let
`φ : X ⟶ 𝐀¹_k` be smooth and `i : T ⟶ X` its fibre over the origin, a principal smooth divisor.
Then there is a class `γ ∈ Ext²_X(i_* Λ_T, Λ_X)` such that

* for every sheaf `G` of `Λ`-modules on `T_étale` and every `q`, the map
  `Ext^q_T(G, Λ_T) ⟶ Ext^{q+2}_X(i_* G, Λ_X)`, `y ↦ i_*(y) ∘ γ`, is bijective;
* `Ext^q_X(i_* G, Λ_X) = 0` for `q < 2`.

This is cohomological purity in codimension one (SGA 4 XVI 3.7; Milne, *Lectures on étale
cohomology* §16), i.e. `Ri^! Λ_X ≅ Λ_T[-2]`, read through `Ext` out of `i_*`. Over the
algebraically closed field `k` the twist `Λ(-1)` is identified with `Λ` by a choice of a primitive
`ℓ`-th root of unity.

## Main results

* `Stacks.EtaleCohomology.Purity.nonempty_moduleRightDerived_one_complement_iso`: for the
  complement `h : φ⁻¹(𝐆_m) ⟶ X` of `T`, `R¹h_* Λ ≅ i_* Λ_T` as sheaves of `Λ`-modules.
* `Stacks.EtaleCohomology.Purity.isZero_moduleRightDerived_complement`: `R^q h_* Λ = 0` for
  `q ≥ 2`.
* `Stacks.EtaleCohomology.Purity.exists_ext_purity_principalDivisor`: cohomological purity for the
  principal smooth divisor `T ⊆ X`, in `Ext` form.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology.Purity

variable {ℓ : ℕ}

/-- The underlying abelian sheaf of the constant sheaf `ℤ/ℓ` of `ℤ/ℓ`-modules. -/
def forgetUnitSheafIso (Y : Scheme.{u}) :
    (etaleModuleForgetAb.{u, 0} (ZMod ℓ) Y).obj (unitSheaf (X := Y) ℓ) ≅
      etaleConstantSheaf Y (ZMod ℓ) :=
  (Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} (ZMod ℓ) Y.smallEtaleTopology).app _

/-- The underlying abelian sheaf of `R^q h_* Λ` is `R^q h_*` of the abelian sheaf `ℤ/ℓ`. -/
private def forgetRightDerivedDirectImageUnitSheafIso {Y Z : Scheme.{u}} (h : Y ⟶ Z) (q : ℕ) :
    (etaleModuleForgetAb.{u, 0} (ZMod ℓ) Z).obj
      (((etaleModuleDirectImage.{u, 0} (ZMod ℓ) h).rightDerived q).obj
        (unitSheaf (X := Y) ℓ)) ≅
      ((etaleAbelianDirectImage.{u, 0} h).rightDerived q).obj (etaleConstantSheaf Y (ZMod ℓ)) :=
  etaleModuleForgetRightDerivedDirectImageIso (ZMod ℓ) h _ q ≪≫
    ((etaleAbelianDirectImage.{u, 0} h).rightDerived q).mapIso (forgetUnitSheafIso _)

variable {k : Type u} [Field k] [IsAlgClosed k] (hℓ : IsUnit (ℓ : k))
  {X T : Scheme.{u}} (φ : X ⟶ affineLine k) [Smooth φ] (i : T ⟶ X) [IsClosedImmersion i]
  (ψ : T ⟶ Spec (.of k)) (hT : IsPullback i ψ φ (origin k))

include hℓ in
/-- For the complement `h : φ⁻¹(𝐆_m) ⟶ X` of the fibre over the origin, the direct image
`h_* Λ` of the constant sheaf `Λ = ℤ/ℓ` of `Λ`-modules is isomorphic to `Λ_X`. -/
theorem nonempty_moduleDirectImage_complement_iso :
    Nonempty ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) (complementOpen φ).ι).obj
      (unitSheaf (X := (complementOpen φ).toScheme) ℓ) ≅ unitSheaf (X := X) ℓ) := by
  obtain ⟨e⟩ := nonempty_directImage_complement_constant_iso hℓ φ
  exact ⟨(Stacks.ArtinSchreier.etaleModuleForgetZModFullyFaithful X ℓ).preimageIso
    ((etaleAbelianDirectImage.{u, 0} (complementOpen φ).ι).mapIso (forgetUnitSheafIso _) ≪≫ e ≪≫
      (forgetUnitSheafIso X).symm)⟩

include hℓ hT in
/-- For the complement `h : φ⁻¹(𝐆_m) ⟶ X` of the fibre `i : T ⟶ X` over the origin,
`R¹h_* Λ ≅ i_* Λ_T` as sheaves of `Λ`-modules, with `Λ = ℤ/ℓ`. -/
theorem nonempty_moduleRightDerived_one_complement_iso :
    Nonempty (((etaleModuleDirectImage.{u, 0} (ZMod ℓ) (complementOpen φ).ι).rightDerived 1).obj
      (unitSheaf (X := (complementOpen φ).toScheme) ℓ) ≅
        (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ)) := by
  obtain ⟨e⟩ := nonempty_rightDerived_one_complement_constant_iso hℓ φ i ψ hT
  exact ⟨(Stacks.ArtinSchreier.etaleModuleForgetZModFullyFaithful X ℓ).preimageIso
    (forgetRightDerivedDirectImageUnitSheafIso (complementOpen φ).ι 1 ≪≫ e ≪≫
      (etaleAbelianDirectImage.{u, 0} i).mapIso (forgetUnitSheafIso T).symm)⟩

include hℓ in
/-- For the complement `h : φ⁻¹(𝐆_m) ⟶ X` of the fibre over the origin, `R^q h_* Λ = 0` for
`q ≥ 2`, as sheaves of `Λ`-modules, where `Λ = ℤ/ℓ`. -/
theorem isZero_moduleRightDerived_complement (q : ℕ) (hq : 2 ≤ q) :
    IsZero (((etaleModuleDirectImage.{u, 0} (ZMod ℓ) (complementOpen φ).ι).rightDerived q).obj
      (unitSheaf (X := (complementOpen φ).toScheme) ℓ)) := by
  have := (Stacks.ArtinSchreier.etaleModuleForgetZModFullyFaithful X ℓ).full
  have := (Stacks.ArtinSchreier.etaleModuleForgetZModFullyFaithful X ℓ).faithful
  refine IsZero.of_full_of_faithful_of_isZero (etaleModuleForgetAb.{u, 0} (ZMod ℓ) X) _ ?_
  exact (isZero_rightDerived_complement_constant hℓ φ q hq).of_iso
    (forgetRightDerivedDirectImageUnitSheafIso (complementOpen φ).ι q)

include hℓ hT in
/-- **Cohomological purity for a principal smooth divisor** (SGA 4 XVI 3.7, codimension one).
For `φ : X ⟶ 𝐀¹_k` smooth over an algebraically closed field `k`, `ℓ ≥ 1` an integer invertible
in `k` and `i : T ⟶ X` the fibre of `φ` over the origin, there is `γ ∈ Ext²_X(i_* Λ_T, Λ_X)`,
`Λ = ℤ/ℓ`, such that `y ↦ i_*(y) ∘ γ` is a bijection `Ext^q_T(G, Λ_T) ≅ Ext^{q+2}_X(i_* G, Λ_X)`
for every sheaf `G` of `Λ`-modules on `T` and every `q`, and `Ext^q_X(i_* G, Λ_X) = 0` for
`q < 2`. -/
theorem exists_ext_purity_principalDivisor :
    ∃ γ : Ext ((etaleModuleDirectImage (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ))
        (unitSheaf (X := X) ℓ) (2 * 1),
      (∀ (G : EtaleModules.{u, 0} (ZMod ℓ) T) (q : ℕ), Function.Bijective
        (fun y : Ext G (unitSheaf (X := T) ℓ) q =>
          (y.mapExactFunctor (etaleModuleDirectImage (ZMod ℓ) i)).comp γ
            (show q + 2 * 1 = q + 2 * 1 from rfl))) ∧
      (∀ (G : EtaleModules.{u, 0} (ZMod ℓ) T) (q : ℕ), q < 2 * 1 →
        Subsingleton (Ext ((etaleModuleDirectImage (ZMod ℓ) i).obj G) (unitSheaf (X := X) ℓ) q)) :=
  exists_ext_purity_of_rightDerived_complement (ZMod ℓ) i (complementOpen φ).ι
    (range_complementOpen_ι φ i ψ hT) _ _ _ (nonempty_moduleDirectImage_complement_iso hℓ φ)
    (nonempty_moduleRightDerived_one_complement_iso hℓ φ i ψ hT)
    (isZero_moduleRightDerived_complement hℓ φ)

end Stacks.EtaleCohomology.Purity

end
