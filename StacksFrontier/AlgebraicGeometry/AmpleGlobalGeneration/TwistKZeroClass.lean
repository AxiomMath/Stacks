module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.Components
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistByInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsSymmetricFiltration
public import StacksFrontier.AlgebraicGeometry.Chow.VectorBundleKZeroPullbackComp
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.AmpleEmbedding
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic

/-!
# Twisting by an invertible module, in `K₀(Vect(-))`

Let `L` be an invertible module on a scheme `X`. Its integer tensor powers `L^{⊗ n}` are finite
locally free, and their classes in the Grothendieck ring `K₀(Vect(X))` are the integer powers of
the unit `[L]`: `[L^{⊗ n}] = [L]^n`. Pulling back along `i : Z ⟶ X` preserves this, so for a finite
locally free module `𝒞` on `Z` the class of `𝒞` is recovered from that of a twist,
`[𝒞] = [𝒞 ⊗ (i^*L)^{⊗ n}] · i^*[L]^{-n}`.

Together with clause (7) of [Stacks, Tag 01Q3] this gives the first step of the proof of
[Stacks, Tag 0FIR]: if `i^*L` is ample, a sufficiently positive twist of `𝒞` is a quotient of a
free module of finite rank, and the class of `𝒞` is the class of that quotient times a class
pulled back from `X`.

## Main results

* `Stacks.Ample.classOf_tensorPowModule_eq_zpow`: `[L^{⊗ n}] = [L]^n` in `K₀(Vect(X))ˣ`.
* `Stacks.Ample.pullbackRingHom_classOf_tensorPowModule`: `i^*[L^{⊗ n}] = [(i^*L)^{⊗ n}]`.
* `Stacks.Ample.classOf_eq_classOf_tensor_mul_pullbackRingHom`:
  `[𝒞] = [𝒞 ⊗ (i^*L)^{⊗ n}] · i^*[L^{⊗ -n}]`.
* `Stacks.Ample.exists_epi_free_tensorPowModule`: clause (7) of [Stacks, Tag 01Q3] with the
  generating sections indexed by `Fin m`.
* `Stacks.Ample.exists_epi_free_twist_classOf_eq`: **the twisting step of [Stacks, Tag 0FIR].**

## Implementation notes

The tensor product of `K₀(Vect(-))` is `AlgebraicGeometry.Scheme.Modules.tensorObjRingedSpace`,
and the addition law for tensor powers, `Stacks.Ample.tensorPowModuleAddIso`, is stated at the
same functor `Stacks.SheafOfModules.Tensor.sheafTensor`; the two differ only in the proof of the
sheaf condition they carry, so the classes multiply with no conversion. Clause (7) of
[Stacks, Tag 01Q3] is stated over the monoidal structure
`Stacks.SheafInternalHom.schemeMonoidalCategory`, which `Stacks.SheafInternalHom.tensorLeftIso`
identifies with that functor.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 0FIR](https://stacks.math.columbia.edu/tag/0FIR)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.VectorBundleKZero

universe u

namespace Stacks.Ample

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- A tensor power of an invertible module is finite locally free, at the spelling of finite
local freeness `K₀(Vect(X))` is built over. -/
theorem isFiniteLocallyFree_tensorPowModule_kZero (n : ℤ) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (tensorPowModule X L n) :=
  have := Stacks.Algebraization.isFiniteLocallyFree_tensorPowModule L n
  Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _

/-- **The addition law for the classes of tensor powers**,
`[L^{⊗ (n + m)}] = [L^{⊗ n}][L^{⊗ m}]`. -/
theorem classOf_tensorPowModule_add (n m : ℤ) :
    classOf X (tensorPowModule X L (n + m)) =
      classOf X (tensorPowModule X L n) * classOf X (tensorPowModule X L m) := by
  rw [classOf_mul _ _ (isFiniteLocallyFree_tensorPowModule_kZero L n)
    (isFiniteLocallyFree_tensorPowModule_kZero L m)]
  exact (classOf_eq_of_iso (tensorPowModuleAddIso X L n m)
    (isFiniteLocallyFree_tensorPowModule_kZero L _ |>.of_iso
      (tensorPowModuleAddIso X L n m).symm)).symm

/-- **The zeroth tensor power has class one.** -/
theorem classOf_tensorPowModule_zero : classOf X (tensorPowModule X L 0) = 1 :=
  (classOf_eq_of_iso (tensorPowModuleZeroIso X L)
    (isFiniteLocallyFree_tensorPowModule_kZero L 0)).trans (classOf_unit X)

/-- The class of a tensor power of an invertible module is a unit of `K₀(Vect(X))`. -/
theorem isUnit_classOf_tensorPowModule (n : ℤ) : IsUnit (classOf X (tensorPowModule X L n)) :=
  IsUnit.of_mul_eq_one (classOf X (tensorPowModule X L (-n))) (by
    rw [← classOf_tensorPowModule_add, add_neg_cancel, classOf_tensorPowModule_zero])

/-- **The class of `L` as a unit of `K₀(Vect(X))`.** -/
def classOfUnit : (VectorBundleKZero X)ˣ :=
  (isUnit_classOf_tensorPowModule L 1).unit

/-- **`[L^{⊗ n}] = [L]^n`** in the units of `K₀(Vect(X))`. -/
theorem classOf_tensorPowModule_eq_zpow (n : ℤ) :
    classOf X (tensorPowModule X L n) = ((classOfUnit L ^ n : (VectorBundleKZero X)ˣ) :
      VectorBundleKZero X) := by
  let f : Multiplicative ℤ →* (VectorBundleKZero X)ˣ :=
    { toFun := fun n => (isUnit_classOf_tensorPowModule L n.toAdd).unit
      map_one' := Units.ext (classOf_tensorPowModule_zero L)
      map_mul' := fun a b => Units.ext (classOf_tensorPowModule_add L a.toAdd b.toAdd) }
  exact congrArg Units.val (show f (Multiplicative.ofAdd n) = f (Multiplicative.ofAdd 1) ^ n by
    rw [← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one])

/-- A tensor power of an invertible module is finite locally free of rank one. -/
theorem isFiniteLocallyFreeOfRank_one_tensorPowModule (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf)
      (tensorPowModule X L n) 1 :=
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (tensorPowModule X L n) :=
    Stacks.InvertibleBridge.algebraicGeometryIsInvertible_of_stacksIsInvertible
  Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme X _

/-! ### Pullback -/

variable {Z : Scheme.{u}} (i : Z ⟶ X)

/-- **Pullback of the class of an invertible module**, as units: `i^*[L] = [i^*L]`. -/
theorem units_map_pullbackRingHom_classOfUnit :
    Units.map (pullbackRingHom i : VectorBundleKZero X →* VectorBundleKZero Z) (classOfUnit L) =
      classOfUnit ((Scheme.Modules.pullback i).obj L) := by
  apply Units.ext
  change pullbackRingHom i (classOf X (tensorPowModule X L 1)) =
    classOf Z (tensorPowModule Z ((Scheme.Modules.pullback i).obj L) 1)
  have hL : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) L :=
    (isFiniteLocallyFree_tensorPowModule_kZero L 1).of_iso (tensorPowModuleOneIso X L)
  rw [classOf_eq_of_iso (tensorPowModuleOneIso X L) (isFiniteLocallyFree_tensorPowModule_kZero L 1),
    classOf_eq_of_iso (tensorPowModuleOneIso Z _)
      (isFiniteLocallyFree_tensorPowModule_kZero ((Scheme.Modules.pullback i).obj L) 1),
    pullbackRingHom_classOf i L hL]

/-- **`i^*[L^{⊗ n}] = [(i^*L)^{⊗ n}]`** in `K₀(Vect(Z))`. -/
theorem pullbackRingHom_classOf_tensorPowModule (n : ℤ) :
    pullbackRingHom i (classOf X (tensorPowModule X L n)) =
      classOf Z (tensorPowModule Z ((Scheme.Modules.pullback i).obj L) n) := by
  rw [classOf_tensorPowModule_eq_zpow, classOf_tensorPowModule_eq_zpow,
    ← units_map_pullbackRingHom_classOfUnit]
  exact congrArg Units.val (map_zpow (Units.map (pullbackRingHom i :
    VectorBundleKZero X →* VectorBundleKZero Z)) (classOfUnit L) n)

/-- **Untwisting in `K₀(Vect(Z))`.** For a finite locally free `𝒞` on `Z`, an invertible `L` on `X`
and `n ∈ ℤ`, `[𝒞] = [𝒞 ⊗ (i^*L)^{⊗ n}] · i^*[L^{⊗ -n}]`. -/
theorem classOf_eq_classOf_tensor_mul_pullbackRingHom (C : Z.Modules)
    (hC : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Z.ringCatSheaf) C) (n : ℤ) :
    classOf Z C =
      classOf Z (Scheme.Modules.tensorObjRingedSpace Z C
          (tensorPowModule Z ((Scheme.Modules.pullback i).obj L) n)) *
        pullbackRingHom i (classOf X (tensorPowModule X L (-n))) := by
  rw [pullbackRingHom_classOf_tensorPowModule, ← classOf_mul _ _ hC
    (isFiniteLocallyFree_tensorPowModule_kZero _ n), mul_assoc,
    ← classOf_tensorPowModule_add, add_neg_cancel, classOf_tensorPowModule_zero, mul_one]

/-! ### Global generation with a finite index of the form `Fin m` -/

/-- **Enlarging the index of an epimorphism out of a free module.** An epimorphism
`𝒪^{⊕ I} ⟶ Q` with `I` finite gives an epimorphism `𝒪^{⊕ m} ⟶ Q` for every large `m`: the extra
generators are sent to zero. -/
theorem exists_epi_free_fin_of_epi_free {Y : Scheme.{u}} {I : Type u} [Finite I] {Q : Y.Modules}
    (φ : SheafOfModules.free (R := Y.ringCatSheaf) I ⟶ Q) [Epi φ] (m₀ : ℕ) :
    ∃ m : ℕ, m₀ ≤ m ∧ ∃ ψ : SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ Q,
      Epi ψ := by
  have := Fintype.ofFinite I
  let g : I → ULift.{u} (Fin (Fintype.card I + m₀)) :=
    fun x => ULift.up (Fin.castAdd m₀ (Fintype.equivFin I x))
  let s := Q.freeHomEquiv φ
  let t := Function.extend g s fun _ => Q.unitHomEquiv (0 : unitModule Y ⟶ Q)
  let ψ := Q.freeHomEquiv.symm t
  exact ⟨Fintype.card I + m₀, Nat.le_add_left _ _, ψ,
    epi_of_epi_fac (f := SheafOfModules.freeMap g) (h := φ) <|
      Q.freeHomEquiv.injective <| funext fun x =>
        (SheafOfModules.freeHomEquiv_comp_apply (SheafOfModules.freeMap g) ψ x).trans
          ((congrArg (SheafOfModules.sectionsMap ψ)
            (congrFun (SheafOfModules.freeHomEquiv_freeMap (R := Y.ringCatSheaf) g) x)).trans
            ((SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection (M := Q) t (g x)).trans
              ((ULift.up_injective.comp ((Fin.castAdd_injective _ _).comp
                (Fintype.equivFin I).injective)).extend_apply s _ x)))⟩

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory in
/-- **Clause (7) of [Stacks, Tag 01Q3], with the generators indexed by `Fin m`.** On a scheme with
an ample invertible module `M`, a quasi-coherent module `F` of finite type has, for every
sufficiently positive `n`, a twist `F ⊗ M^{⊗ n}` which is a quotient of `𝒪^{⊕ m}` for every large
`m`. The tensor product is the one of `K₀(Vect(-))`. -/
theorem exists_epi_free_tensorPowModule {Y : Scheme.{u}} (M : Y.Modules) [IsInvertibleModule Y M]
    (hM : IsAmple Y M) (F : Y.Modules) (hqc : F.IsQuasicoherent)
    (hft : _root_.SheafOfModules.IsFiniteType.{u, u, u} F) (N : ℤ) (m₀ : ℕ) :
    ∃ n : ℤ, N ≤ n ∧ ∃ m : ℕ, m₀ ≤ m ∧
      ∃ ψ : SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin m)) ⟶
        Scheme.Modules.tensorObjRingedSpace Y F (tensorPowModule Y M n), Epi ψ := by
  obtain ⟨n₀, hgen⟩ :=
    Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple M hM F hqc hft
  obtain ⟨σ, hσ⟩ := hgen (max n₀ N) (le_max_left _ _)
  let e : F ⊗ tensorPowModule Y M (max n₀ N) ≅
      Scheme.Modules.tensorObjRingedSpace Y F (tensorPowModule Y M (max n₀ N)) :=
    (Stacks.SheafInternalHom.tensorLeftIso Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) F).app _
  have : Epi (σ.π ≫ e.hom) := @epi_comp _ _ _ _ _ σ.π σ.epi e.hom (IsIso.epi_of_iso e.hom)
  obtain ⟨m, hm, ψ, hψ⟩ := exists_epi_free_fin_of_epi_free (σ.π ≫ e.hom) m₀
  exact ⟨max n₀ N, le_max_right _ _, m, hm, ψ, hψ⟩

/-! ### The twisting step of Tag 0FIR -/

/-- **The twisting step of the proof of [Stacks, Tag 0FIR].** Let `i : Z ⟶ X` be a closed
immersion, `L` an ample invertible module on `X`, and `𝒞` finite locally free of constant rank `r`
on `Z`. Then for every large `m` there are a quotient `𝒪_Z^{⊕ m} ⟶ Q` with `Q` finite locally
free of rank `r` — namely `Q = 𝒞 ⊗ (i^*L)^{⊗ n}` for `n` large — and a class `β ∈ K₀(Vect(X))`
with `[𝒞] = [Q] · i^*β` in `K₀(Vect(Z))`. -/
theorem exists_epi_free_classOf_eq_mul_pullbackRingHom [IsClosedImmersion i]
    (hL : IsAmple X L) (C : Z.Modules) (r : ℕ)
    [hC : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} C r] (m₀ : ℕ) :
    ∃ m : ℕ, m₀ ≤ m ∧ ∃ (Q : Z.Modules)
      (φ : SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ Q), Epi φ ∧
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q r ∧
        ∃ β : VectorBundleKZero X, classOf Z C = classOf Z Q * pullbackRingHom i β := by
  have hM : IsAmple Z ((Scheme.Modules.pullback i).obj L) :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple Z _).mp
      (Scheme.Modules.isAmple_modulePullback_of_isClosedImmersion i L
        ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X L).mpr hL))
  have hCflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := Z.ringCatSheaf) C :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree C r
  have hqc : C.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree C
  have hft : _root_.SheafOfModules.IsFiniteType.{u, u, u} C :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isFiniteType_of_isFiniteLocallyFree C
  obtain ⟨n, -, m, hm, φ, hφ⟩ :=
    exists_epi_free_tensorPowModule ((Scheme.Modules.pullback i).obj L) hM C hqc hft 0 m₀
  refine ⟨m, hm, _, φ, hφ, ?_, _, classOf_eq_classOf_tensor_mul_pullbackRingHom L i C
    (VectorBundleKZero.isFiniteLocallyFree_ofSheaf hCflf) n⟩
  have := Stacks.Chow.isFiniteLocallyFreeOfRank_tensor hC
    (isFiniteLocallyFreeOfRank_one_tensorPowModule ((Scheme.Modules.pullback i).obj L) n)
  rwa [mul_one] at this

end Stacks.Ample

end
