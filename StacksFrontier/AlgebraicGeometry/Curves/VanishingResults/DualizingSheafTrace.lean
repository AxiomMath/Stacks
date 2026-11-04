module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexFactorization
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafHom
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.BoundedDirectSums

/-!
# The trace of a morphism of proper curves on dualizing sheaves

Let `k` be a field, `g : Y ⟶ Spec k` and `c : X ⟶ Y` with `X` and `Y` proper over `k` of
dimension at most one. The dualizing complexes `ω_X^• = (c ≫ g)^×(𝒪)` and `ω_Y^• = g^×(𝒪)` of
[Stacks, Tag 0BS2] are related by `ω_X^• = c^×(ω_Y^•)`, because the right adjoint of
`R(c ≫ g)_* = Rg_* ∘ Rc_*` is `c^× ∘ g^×` ([Stacks, Tag 0A9E]). This is the step
`f^! = c^! ∘ g^!` of the proof of [Stacks, Tag 0E7P].

The counit `Rc_* ω_X^• ⟶ ω_Y^•` of `Rc_* ⊣ c^×` is the trace of the source. Its use there is the
following: if `ℒ` is a quasi-coherent `𝒪_X`-module with `R^i c_* ℒ = 0` for `i > 0` and
`c_* ℒ ≅ ω_Y` — in the source `ℒ = c^* ω_Y` — then there is a map `b : ℒ ⟶ ω_X` such that
`c_*(b) : c_* ℒ ⟶ c_* ω_X` is a split monomorphism. Indeed `ℒ[1] ⟶ ω_X^•` is adjoint to
`Rc_*(ℒ[1]) = ω_Y[1] ⟶ ω_Y^•`, and taking `H^{-1}` of the adjunction identity shows that
`c_*(b)` followed by `H^{-1}` of the trace is the given isomorphism `c_* ℒ ≅ ω_Y`.

## Main definitions

* `Stacks.Duality.dualizingComplexOverFieldCompIso`: `ω_X^• ≅ c^×(ω_Y^•)`.
* `Stacks.Duality.homologyNegOneDerivedPushforwardShiftIso`: `H^{-1}(Rc_*(ℱ[0]⟦1⟧)) ≅ c_* ℱ`,
  naturally in `ℱ`.

## Main results

* `Stacks.Duality.exists_pushforward_map_comp_eq_id`: from an isomorphism
  `Rc_*(ℒ[0]⟦1⟧) ≅ ω_Y[0]⟦1⟧`, a map `b : ℒ ⟶ ω_X` with `c_*(b)` split mono.
* `Stacks.Duality.exists_pushforward_map_comp_eq_id_of_isZero`: the same from the vanishing of
  the higher direct images of `ℒ` and an isomorphism `c_* ℒ ≅ ω_Y`.

## References

* [Stacks Project, Tag 0E7P](https://stacks.math.columbia.edu/tag/0E7P)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

open DerivedPushforward

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (c : X ⟶ Y)
  (g : Y ⟶ Spec (CommRingCat.of k)) [QuasiCompact c] [QuasiSeparated c] [QuasiCompact g]
  [QuasiSeparated g] [CompactSpace Y]

/-- `Rc_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` has a right adjoint ([Stacks, Tag 0A9E]). -/
instance isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_compactSpace :
    (qcqsRestrictedDerivedPushforward c).IsLeftAdjoint :=
  isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward c

/-- **`ω_X^• = c^×(ω_Y^•)`**: the dualizing complex of `X` over `k` is the twisted inverse image
along `c` of that of `Y`, by uniqueness of the right adjoint of `R(c ≫ g)_* = Rg_* ∘ Rc_*`. -/
def dualizingComplexOverFieldCompIso :
    dualizingComplexOverField (c ≫ g) ≅
      (twistedInverseImage c (isQuasicoherent_homology_derivedPushforward_of_qcqs c)).obj
        (dualizingComplexOverField g) :=
  ((twistedInverseImageAdjunction (c ≫ g) _).rightAdjointUniq
    (((twistedInverseImageAdjunction c _).comp (twistedInverseImageAdjunction g _)).ofNatIsoLeft
      (qcqsRestrictedDerivedPushforwardCompIso c g).symm)).app _

/-- **`H^{-1}(Rc_*(ℱ[0]⟦1⟧)) = c_* ℱ`**, naturally in the `𝒪_X`-module `ℱ`: the shift moves
`ℱ` to degree `-1`, and the lowest cohomology of `Rc_*` is `R^0 c_* = c_*`. -/
def homologyNegOneDerivedPushforwardShiftIso :
    DerivedCategory.singleFunctor X.Modules 0 ⋙ shiftFunctor (DerivedCategory X.Modules) (1 : ℤ) ⋙
        derivedPushforward c ⋙ DerivedCategory.homologyFunctor Y.Modules (-1) ≅
      Scheme.Modules.pushforward c :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((DerivedCategory.singleFunctors X.Modules).shiftIso 1 (-1) 0
      (by norm_num)) _ ≪≫
    singleCompDerivedPushforwardHomologyIso c (-1) (-1) 0 (by norm_num) ≪≫
    (Scheme.Modules.pushforward c).rightDerivedZeroIsoSelf

omit [QuasiCompact c] [QuasiSeparated c] [CompactSpace ↥Y] in
/-- **`Rc_*(ℒ[0]) = 𝒩[0]` when the higher direct images of `ℒ` vanish**, for any `𝒩 ≅ c_*ℒ`. -/
theorem nonempty_derivedPushforward_iso_of_isZero (L : X.Modules) (N : Y.Modules)
    (hR : ∀ i : ℕ, 0 < i → IsZero (((Scheme.Modules.pushforward c).rightDerived i).obj L))
    (e : (Scheme.Modules.pushforward c).obj L ≅ N) :
    Nonempty ((derivedPushforward c).obj ((DerivedCategory.singleFunctor X.Modules 0).obj L) ≅
      (DerivedCategory.singleFunctor Y.Modules 0).obj N) := by
  let A := (derivedPushforward c).obj ((DerivedCategory.singleFunctor X.Modules 0).obj L)
  have hge : A.IsGE 0 :=
    Stacks.DerivedFunctor.isGE_totalRightDerived_obj (Scheme.Modules.pushforward c) _ 0
  have hle : A.IsLE 0 := by
    rw [DerivedCategory.isLE_iff]
    intro m hm
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) := ⟨m.toNat, by omega⟩
    exact (hR n (by omega)).of_iso
      ((singleCompDerivedPushforwardHomologyIso c 0 n n (by simp)).app L)
  obtain ⟨Z, ⟨eA⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE A 0
  have eZ : Z ≅ N :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso Y.Modules 0).app Z).symm ≪≫
      (DerivedCategory.homologyFunctor Y.Modules 0).mapIso eA.symm ≪≫
      (singleCompDerivedPushforwardHomologyIso c 0 0 0 (by simp)).app L ≪≫
      (Scheme.Modules.pushforward c).rightDerivedZeroIsoSelf.app L ≪≫ e
  exact ⟨eA ≪≫ (DerivedCategory.singleFunctor Y.Modules 0).mapIso eZ⟩

omit [QuasiCompact c] [QuasiSeparated c] [CompactSpace ↥Y] in
/-- **`Rc_*(ℒ[0]⟦1⟧) = 𝒩[0]⟦1⟧` when the higher direct images of `ℒ` vanish**, for any
`𝒩 ≅ c_*ℒ`: `nonempty_derivedPushforward_iso_of_isZero` shifted by one. -/
theorem nonempty_derivedPushforward_shift_iso_of_isZero (L : X.Modules) (N : Y.Modules)
    (hR : ∀ i : ℕ, 0 < i → IsZero (((Scheme.Modules.pushforward c).rightDerived i).obj L))
    (e : (Scheme.Modules.pushforward c).obj L ≅ N) :
    Nonempty ((derivedPushforward c).obj
        (((DerivedCategory.singleFunctor X.Modules 0).obj L)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor Y.Modules 0).obj N)⟦(1 : ℤ)⟧) :=
  ⟨((derivedPushforward c).commShiftIso (1 : ℤ)).app _ ≪≫
    (shiftFunctor (DerivedCategory Y.Modules) (1 : ℤ)).mapIso
      (nonempty_derivedPushforward_iso_of_isZero c L N hR e).some⟩

variable [IsProper (c ≫ g)] [IsProper g]

/-- The canonical map `ω_Y[0]⟦1⟧ ⟶ ω_Y^•`: the dualizing sheaf placed in degree `-1` is the
truncation `τ^{≤ -1} ω_Y^•`. -/
abbrev dualizingSheafShiftToComplex (hdim : topologicalKrullDim Y ≤ (1 : WithBot ℕ∞)) :
    ((DerivedCategory.singleFunctor Y.Modules 0).obj (dualizingSheafOverField g))⟦(1 : ℤ)⟧ ⟶
      (dualizingComplexOverField g).obj :=
  (singleShiftOneIsoTruncLE g hdim).hom ≫
    (DerivedCategory.TStructure.t.truncLEι (-1)).app (dualizingComplexOverField g).obj

omit [CompactSpace ↥Y] in
/-- The canonical map `ω_Y[0]⟦1⟧ ⟶ ω_Y^•` is an isomorphism on `H^{-1}`. -/
theorem isIso_homology_dualizingSheafShiftToComplex
    (hdim : topologicalKrullDim Y ≤ (1 : WithBot ℕ∞)) :
    IsIso ((DerivedCategory.homologyFunctor Y.Modules (-1)).map
      (dualizingSheafShiftToComplex g hdim)) := by
  have := Stacks.DerivedTruncation.isIso_homologyMap_truncLEι
    (dualizingComplexOverField g).obj (-1) (-1) le_rfl
  rw [Functor.map_comp]
  infer_instance

/-- **The trace splits `c_*(b)`.** Given `Rc_*(ℒ[0]⟦1⟧) ≅ ω_Y[0]⟦1⟧`, the map
`b : ℒ ⟶ ω_X` adjoint to `Rc_*(ℒ[1]) ≅ ω_Y[1] ⟶ ω_Y^•` has `c_*(b)` a split monomorphism: its
composite with `H^{-1}` of the trace `Rc_* ω_X^• ⟶ ω_Y^•` is the given isomorphism on `H^{-1}`. -/
theorem exists_pushforward_map_comp_eq_id (hdimX : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (hdimY : topologicalKrullDim Y ≤ (1 : WithBot ℕ∞)) (L : X.Modules) (hL : L.IsQuasicoherent)
    (ψ : (derivedPushforward c).obj (((DerivedCategory.singleFunctor X.Modules 0).obj L)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor Y.Modules 0).obj (dualizingSheafOverField g))⟦(1 : ℤ)⟧) :
    ∃ (b : L ⟶ dualizingSheafOverField (c ≫ g))
      (t : (Scheme.Modules.pushforward c).obj (dualizingSheafOverField (c ≫ g)) ⟶
        (Scheme.Modules.pushforward c).obj L),
      (Scheme.Modules.pushforward c).map b ≫ t = 𝟙 _ := by
  let K : quasiCoherentDerivedCategory X := shiftQuasiCoherent (singleQuasiCoherent L hL 0) 1
  let β : (qcqsRestrictedDerivedPushforward c).obj K ⟶ dualizingComplexOverField g :=
    qcohHom (ψ.hom ≫ dualizingSheafShiftToComplex g hdimY)
  let b' : K ⟶ (twistedInverseImage c
      (isQuasicoherent_homology_derivedPushforward_of_qcqs c)).obj
      (dualizingComplexOverField g) :=
    (twistedInverseImageAdjunction c _).homEquiv K _ β
  let e := dualizingComplexOverFieldCompIso c g
  let b'' : K.obj ⟶ (dualizingComplexOverField (c ≫ g)).obj := (b' ≫ e.inv).hom
  let b := (homDualizingSheafShiftAddEquiv (c ≫ g) hdimX L).symm b''
  let ι := (singleShiftOneIsoTruncLE (c ≫ g) hdimX).hom ≫
    (DerivedCategory.TStructure.t.truncLEι (-1)).app (dualizingComplexOverField (c ≫ g)).obj
  have hb : b'' = ((DerivedCategory.singleFunctor X.Modules 0).map b)⟦(1 : ℤ)⟧' ≫ ι :=
    ((homDualizingSheafShiftAddEquiv (c ≫ g) hdimX L).apply_symm_apply b'').symm.trans
      (homDualizingSheafShiftAddEquiv_apply _ hdimX L b)
  have hadj : (qcqsRestrictedDerivedPushforward c).map b' ≫
      (twistedInverseImageAdjunction c _).counit.app _ = β :=
    ((twistedInverseImageAdjunction c _).homEquiv_counit K
        (dualizingComplexOverField g) b').symm.trans
      (((twistedInverseImageAdjunction c _).homEquiv K
        (dualizingComplexOverField g)).symm_apply_apply β)
  let H := DerivedCategory.homologyFunctor Y.Modules (-1)
  let R := derivedPushforward c
  let φ := ψ.hom ≫ dualizingSheafShiftToComplex g hdimY
  have : IsIso (H.map φ) := by
    have := isIso_homology_dualizingSheafShiftToComplex g hdimY
    rw [H.map_comp]
    infer_instance
  let τ := R.map e.hom.hom ≫ ((twistedInverseImageAdjunction c _).counit.app _).hom
  have h1 : R.map b'' ≫ τ = φ := by
    have h2 := congrArg (fun φ => φ.hom) hadj
    simp only [ObjectProperty.FullSubcategory.comp_hom] at h2
    have h3 : b'.hom = b'' ≫ e.hom.hom := by
      simp [b'', ← ObjectProperty.FullSubcategory.comp_hom]
    rw [← Category.assoc, ← R.map_comp, ← h3]
    exact h2.trans (ι_map_qcohHom _)
  let M := H.map (R.map ι ≫ τ) ≫ inv (H.map φ)
  have hkey : H.map (R.map (((DerivedCategory.singleFunctor X.Modules 0).map b)⟦(1 : ℤ)⟧')) ≫ M =
      𝟙 _ := by
    simp only [M]
    rw [← Category.assoc, ← H.map_comp, ← R.map_comp_assoc, ← hb]
    erw [h1]
    exact IsIso.hom_inv_id _
  let Φ := homologyNegOneDerivedPushforwardShiftIso c
  refine ⟨b, Φ.inv.app _ ≫ M ≫ Φ.hom.app _, ?_⟩
  rw [← Category.assoc, Φ.inv.naturality b]
  simp only [Functor.comp_map, Category.assoc]
  rw [reassoc_of% hkey]
  simp

/-- **The trace splits `c_*(b)`**, for a quasi-coherent `ℒ` on `X` with `R^i c_* ℒ = 0` for
`i > 0` and `c_* ℒ ≅ ω_Y`: there is `b : ℒ ⟶ ω_X` with `c_*(b)` a split monomorphism. -/
theorem exists_pushforward_map_comp_eq_id_of_isZero
    (hdimX : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (hdimY : topologicalKrullDim Y ≤ (1 : WithBot ℕ∞)) (L : X.Modules) (hL : L.IsQuasicoherent)
    (hR : ∀ i : ℕ, 0 < i → IsZero (((Scheme.Modules.pushforward c).rightDerived i).obj L))
    (e : (Scheme.Modules.pushforward c).obj L ≅ dualizingSheafOverField g) :
    ∃ (b : L ⟶ dualizingSheafOverField (c ≫ g))
      (t : (Scheme.Modules.pushforward c).obj (dualizingSheafOverField (c ≫ g)) ⟶
        (Scheme.Modules.pushforward c).obj L),
      (Scheme.Modules.pushforward c).map b ≫ t = 𝟙 _ :=
  exists_pushforward_map_comp_eq_id c g hdimX hdimY L hL
    (nonempty_derivedPushforward_shift_iso_of_isZero c L _ hR e).some

end Stacks.Duality
