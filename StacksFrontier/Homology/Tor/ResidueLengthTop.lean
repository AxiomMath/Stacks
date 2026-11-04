module

public import StacksFrontier.Homology.Tor.ExtremalDegreesTop
public import StacksFrontier.Homology.Tor.ResidueLength

/-!
# The length count at the top of the window

For an exact, way-out right exact functor `F` on the derived category of `A`-modules and an
object `X` bounded above, the top cohomology of `F(X)` is computed from the top cohomology module
of `X`. For an endofunctor `F` with `F(T) ≅ T`, where `T` is bounded above with finite cohomology
killed by a maximal ideal `m` and nonzero top cohomology, it follows that `H⁰(F(κ[0])) ≅ κ` for
`κ = A/m` whenever `F(κ[0])` has no cohomology above degree zero.

## Main results

* `isIso_homologyMap_mor₂_of_isLE`: the second map of a distinguished triangle whose first object
  has no cohomology above `c` is invertible on cohomology above `c`.
* `nonempty_homology_iso_homology_map_single_top_of_isLE_homology`: the top cohomology of `F(X)`
  is `F` at the top cohomology module of `X`, for an `F` which is right `t`-exact at the single
  complexes of the cohomology modules of `X` below the top degree.
* `nonempty_homology_iso_homology_map_single_top`: the same for `X` with finite cohomology killed
  by `m`, when `F(κ[0])` has no cohomology above zero.
* `nonempty_homology_iso_residueField_of_isLE_of_iso_of_isTorsionBySet`: for an exact, way-out
  right exact endofunctor with `F(T) ≅ T`, `T` bounded above with `H^b(T) ≠ 0`, and `F(κ[0])` with
  no cohomology above zero, `H⁰(F(κ[0])) ≅ κ`.

## References

* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DerivedCategory

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.ResidueLength

universe u w w'

variable {A : Type u} [CommRing A]
  {D : Type w} [Category.{w'} D] [Abelian D]

/-! ### The degeneration at the top -/

/-- In degrees above `c` the second map of a distinguished triangle whose first object has no
cohomology above `c` is invertible on cohomology. -/
theorem isIso_homologyMap_mor₂_of_isLE (T : Triangle (DerivedCategory D))
    (hT : T ∈ distTriang (DerivedCategory D)) (c i : ℤ) (hi : c < i) (h₁ : T.obj₁.IsLE c) :
    IsIso ((homologyFunctor D i).map T.mor₂) := by
  have : Epi ((homologyFunctor D i).map T.mor₂) := by
    rw [HomologySequence.epi_homologyMap_mor₂_iff _ hT i (i + 1) rfl]
    exact (isZero_of_isLE T.obj₁ c (i + 1) (by omega) (hX := h₁)).eq_of_tgt _ _
  have : Mono ((homologyFunctor D i).map T.mor₂) := by
    rw [HomologySequence.mono_homologyMap_mor₂_iff _ hT i]
    exact (isZero_of_isLE T.obj₁ c i (by omega) (hX := h₁)).eq_of_src _ _
  exact isIso_of_mono_of_epi _

/-- Let `X` lie in `D^{≤ b}`, let `F` be exact and way-out right exact with slack `p`, and suppose
that `F(H^i(X)[0])` has no cohomology above degree zero for every `i < b`. Then
`H^b(F(X)) ≅ H⁰(F(H^b(X)[0]))`. -/
theorem nonempty_homology_iso_homology_map_single_top_of_isLE_homology
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory D) [F.CommShift ℤ]
    [F.IsTriangulated] (X : DerivedCategory (ModuleCat.{u} A)) (b p : ℤ) (hb : X.IsLE b)
    (hway : ∀ (Y : DerivedCategory (ModuleCat.{u} A)) (n : ℤ), Y.IsLE n →
      (F.obj Y).IsLE (n + p))
    (hsingle : ∀ i : ℤ, i < b → (F.obj ((singleFunctor (ModuleCat.{u} A) 0).obj
      ((homologyFunctor (ModuleCat.{u} A) i).obj X))).IsLE 0) :
    Nonempty ((homologyFunctor D b).obj (F.obj X) ≅
      (homologyFunctor D 0).obj (F.obj ((singleFunctor (ModuleCat.{u} A) 0).obj
        ((homologyFunctor (ModuleCat.{u} A) b).obj X)))) := by
  have := hb
  have hdown : (F.obj ((TStructure.t.truncLT b).obj X)).IsLE (b - 1) := by
    have := ExtremalDegrees.isLE_map_of_homology_of_wayOut F
      ((TStructure.t.truncLT b).obj X) (b - 1) 0 p inferInstance hway (fun i ↦ by
        by_cases hi : i < b
        · have hiso := ExtremalDegrees.isIso_homology_truncLT b i hi X
          have ecomp := @asIso _ _ _ _ ((homologyFunctor (ModuleCat.{u} A) i).map
            ((TStructure.t.truncLTι b).app X)) hiso
          have h0 : (F.obj ((singleFunctor (ModuleCat.{u} A) 0).obj
              ((homologyFunctor (ModuleCat.{u} A) i).obj
                ((𝟭 (DerivedCategory (ModuleCat.{u} A))).obj X)))).IsLE 0 := hsingle i hi
          exact TStructure.t.isLE_of_iso
            (F.mapIso ((singleFunctor (ModuleCat.{u} A) 0).mapIso ecomp.symm)) 0
        · apply TStructure.t.isLE_of_isZero
          exact F.map_isZero ((singleFunctor (ModuleCat.{u} A) 0).map_isZero
            (isZero_of_isLE ((TStructure.t.truncLT b).obj X) (b - 1) i (by omega))))
    exact TStructure.t.isLE_of_le _ (b - 1 + 0) (b - 1) (by omega)
  have hT := F.map_distinguished _ (TStructure.t.triangleLTGE_distinguished b X)
  have hiso := isIso_homologyMap_mor₂_of_isLE
    (F.mapTriangle.obj ((TStructure.t.triangleLTGE b).obj X)) hT (b - 1) b (by omega) hdown
  obtain ⟨e₁⟩ := ExtremalDegrees.nonempty_iso_truncGE_singleFunctor X b hb
  exact ⟨(@asIso _ _ _ _ _ hiso) ≪≫ (homologyFunctor D b).mapIso (F.mapIso e₁) ≪≫
    (homologyFunctor D b).mapIso
      (ExtremalDegrees.mapSingleShiftIso F ((homologyFunctor (ModuleCat.{u} A) b).obj X) b) ≪≫
    ((homologyFunctor D 0).shiftIso (-b) b 0 (by omega)).app _⟩

/-- Let `X` lie in `D^{≤ b}` with every cohomology module finite and killed by the maximal ideal
`m`, let `F` be exact and way-out right exact with slack `p`, and let `F(κ[0])` have no cohomology
above zero. Then `H^b(F(X)) ≅ H⁰(F(H^b(X)[0]))`. -/
theorem nonempty_homology_iso_homology_map_single_top
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory D) [F.CommShift ℤ]
    [F.IsTriangulated] (m : Ideal A) [m.IsMaximal] (X : DerivedCategory (ModuleCat.{u} A))
    (b p : ℤ) (hb : X.IsLE b)
    (hway : ∀ (Y : DerivedCategory (ModuleCat.{u} A)) (n : ℤ), Y.IsLE n →
      (F.obj Y).IsLE (n + p))
    (hkill : ∀ i : ℤ, Module.IsTorsionBySet A
      ((homologyFunctor (ModuleCat.{u} A) i).obj X) (m : Set A))
    (hfin : ∀ i : ℤ, Module.Finite A ((homologyFunctor (ModuleCat.{u} A) i).obj X))
    (hLE : (F.obj ((singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (A ⧸ m)))).IsLE 0) :
    Nonempty ((homologyFunctor D b).obj (F.obj X) ≅
      (homologyFunctor D 0).obj (F.obj ((singleFunctor (ModuleCat.{u} A) 0).obj
        ((homologyFunctor (ModuleCat.{u} A) b).obj X)))) :=
  nonempty_homology_iso_homology_map_single_top_of_isLE_homology F X b p hb hway
    (fun i _ ↦ by
      have := hfin i
      exact ResidueDevissage.isLE_map_single_of_isTorsionBySet F m 0 hLE _ (hkill i))

/-! ### The length count from the top -/

/-- Let `F : D(A) → D(A)` be exact and way-out right exact with slack `p`, let `T` lie in
`D^{≤ b}` with all of its cohomology finite and killed by the maximal ideal `m` and with `H^b(T)`
nonzero, and let `F(T) ≅ T`. If `F(κ[0])` has no cohomology above zero, then
`H⁰(F(κ[0])) ≅ κ`. -/
theorem nonempty_homology_iso_residueField_of_isLE_of_iso_of_isTorsionBySet
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A))
    [F.CommShift ℤ] [F.IsTriangulated] (m : Ideal A) [m.IsMaximal]
    (T : DerivedCategory (ModuleCat.{u} A)) (b p : ℤ) (hb : T.IsLE b)
    (hway : ∀ (Y : DerivedCategory (ModuleCat.{u} A)) (n : ℤ), Y.IsLE n →
      (F.obj Y).IsLE (n + p))
    (hkill : ∀ i : ℤ, Module.IsTorsionBySet A
      ((homologyFunctor (ModuleCat.{u} A) i).obj T) (m : Set A))
    (hfin : ∀ i : ℤ, Module.Finite A ((homologyFunctor (ModuleCat.{u} A) i).obj T))
    (hLE : (F.obj ((singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (A ⧸ m)))).IsLE 0)
    (htop : ¬ IsZero ((homologyFunctor (ModuleCat.{u} A) b).obj T))
    (e : F.obj T ≅ T) :
    Nonempty ((homologyFunctor (ModuleCat.{u} A) 0).obj
      (F.obj ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ m)))) ≅
        ModuleCat.of A (A ⧸ m)) := by
  obtain ⟨g⟩ := nonempty_homology_iso_homology_map_single_top F m T b p hb hway hkill hfin hLE
  have := hfin b
  exact nonempty_iso_residueField_of_iso m
    (singleFunctor (ModuleCat.{u} A) 0 ⋙ F ⋙ homologyFunctor (ModuleCat.{u} A) 0)
    ((homologyFunctor (ModuleCat.{u} A) b).obj T) (hkill b) htop
    (g.symm ≪≫ (homologyFunctor (ModuleCat.{u} A) b).mapIso e)

end StacksDraft.ResidueLength

end
