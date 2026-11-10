module

public import StacksFrontier.AlgebraicGeometry.Picard.TorsionRankDisjointCover
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyTrivialInvertible.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TrivialRingSheafModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne

/-!
# Extending an invertible module by the structure sheaf across a clopen decomposition

Let `Y` be a scheme and let `U`, `V` be disjoint opens covering it.  Every invertible module `L`
on `U` is the restriction of an invertible module on `Y`, namely `j_*L ⨿ (j_V)_*𝒪_V`, whose
restriction to `V` is trivial.

Consequently, for finitely many pairwise disjoint opens `U i` covering `Y`, the pullback map
`Pic(Y) → ∏ᵢ Pic(U i)` is surjective as well as injective, and

`dim_{F_ℓ} Pic(Y)[ℓ] = ∑ᵢ dim_{F_ℓ} Pic(U i)[ℓ]`

as cardinals.

## Main definitions

* `Stacks.Picard.extendByUnit`: the module `j_*L ⨿ (j_V)_*𝒪_V` on `Y`.

## Main results

* `Stacks.Picard.restrictExtendByUnitIso` and `Stacks.Picard.restrictExtendByUnitIsoUnit`: its
  restrictions to `U` and to `V` are `L` and `𝒪_V`.
* `Stacks.Picard.isInvertible_extendByUnit`: it is invertible when `L` is.
* `Stacks.Picard.bijective_schemePullbackClass_pi_of_pairwise_disjoint`: `Pic(Y) → ∏ᵢ Pic(U i)`
  is bijective for a finite pairwise disjoint open cover.
* `AlgebraicGeometry.bijective_zmodTorsionRestrictPi_picard`: `Pic(Y)[ℓ] → ∏ᵢ Pic(U i)[ℓ]` is
  bijective.
* `AlgebraicGeometry.rank_picardTorsion_eq_sum_of_pairwise_disjoint` and
  `AlgebraicGeometry.finrank_picardTorsion_eq_sum_of_pairwise_disjoint`: the `F_ℓ`-rank of the
  `ℓ`-torsion of `Pic(Y)` is the sum of those of the `Pic(U i)`.

## Implementation notes

The restriction of `j_*L` to an open disjoint from `U` is a zero object: its sections over any
open are sections of `L` over the empty open, and the ring of sections of `𝒪_U` over the empty
open is trivial.  Restriction along an open immersion is a left adjoint, so it commutes with the
binary coproduct, and a binary coproduct with a zero object is the other summand.
Invertibility is checked on the cover of `Y` by `V` and by the images in `Y` of opens of `U`
trivializing `L` (`Stacks.SheafOfModules.isInvertible_of_coversTop_nonempty_iso_unit`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Picard

attribute [local instance] AddSubgroup.torsionBy.zmodModule

variable {Y : Scheme.{u}}

/-! ### Restriction of a pushforward to a disjoint open -/

/-- The sections of a module on a scheme over an empty open are trivial. -/
theorem subsingleton_presheaf_obj_of_eq_bot {X : Scheme.{u}} (M : X.Modules) {W : X.Opens}
    (hW : W = ⊥) : Subsingleton (M.val.obj (op W)) :=
  Stacks.SheafOfModules.subsingleton_sections M (V := op W)
    (CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hW))

/-- **The restriction of `j_*F` to an open disjoint from `U` is zero**, `j : U ⟶ Y` being the
inclusion. -/
theorem isZero_restrict_pushforward_of_disjoint {U W : Y.Opens} (h : Disjoint U W)
    (F : U.toScheme.Modules) :
    IsZero (Scheme.Modules.restrict ((Scheme.Modules.pushforward U.ι).obj F) W.ι) := by
  refine Stacks.SheafOfModules.isZero_of_forall_subsingleton_sections _ fun T => ?_
  refine subsingleton_presheaf_obj_of_eq_bot F (W := U.ι ⁻¹ᵁ (W.ι ''ᵁ T.unop)) ?_
  refine eq_bot_iff.mpr fun x hx => ?_
  have hxU : (U.ι x : Y) ∈ (U : Set Y) := x.2
  obtain ⟨t, -, ht⟩ := hx
  have hxW : (U.ι x : Y) ∈ (W : Set Y) := by
    rw [← ht]
    exact t.2
  exact (Set.disjoint_left.mp (by simpa using h)) hxU hxW

/-! ### Extension by the structure sheaf -/

/-- **The extension of a module on `U` by the structure sheaf of `V`**: the module
`j_*L ⨿ (j_V)_*𝒪_V` on `Y`, for opens `U` and `V` of `Y`. -/
def extendByUnit (U V : Y.Opens) (L : U.toScheme.Modules) : Y.Modules :=
  (Scheme.Modules.pushforward U.ι).obj L ⨿
    (Scheme.Modules.pushforward V.ι).obj (SheafOfModules.unit V.toScheme.ringCatSheaf)

/-- The restriction of `extendByUnit U V L` to `U` is `L`, when `U` and `V` are disjoint. -/
def restrictExtendByUnitIso {U V : Y.Opens} (h : Disjoint U V) (L : U.toScheme.Modules) :
    Scheme.Modules.restrict (extendByUnit U V L) U.ι ≅ L :=
  (PreservesColimitPair.iso (Scheme.Modules.restrictFunctor U.ι) _ _).symm ≪≫
    coprod.mapIso ((Scheme.Modules.restrictFunctorAdjCounitIso U.ι).app L)
      (isZero_restrict_pushforward_of_disjoint h.symm _).isoZero ≪≫
    coprodZeroIso L

/-- The restriction of `extendByUnit U V L` to `V` is `𝒪_V`, when `U` and `V` are disjoint. -/
def restrictExtendByUnitIsoUnit {U V : Y.Opens} (h : Disjoint U V) (L : U.toScheme.Modules) :
    Scheme.Modules.restrict (extendByUnit U V L) V.ι ≅
      SheafOfModules.unit V.toScheme.ringCatSheaf :=
  (PreservesColimitPair.iso (Scheme.Modules.restrictFunctor V.ι) _ _).symm ≪≫
    coprod.mapIso (isZero_restrict_pushforward_of_disjoint h _).isoZero
      ((Scheme.Modules.restrictFunctorAdjCounitIso V.ι).app _) ≪≫
    zeroCoprodIso _

/-! ### Invertibility on an open cover -/

/-- The restriction of a module to the image `U.ι ''ᵁ W` of an open `W` of an open subscheme
`U` is its restriction to `U` followed by its restriction to `W`, transported along
`W ≅ U.ι ''ᵁ W`. -/
def restrictImageIso (M : Y.Modules) (U : Y.Opens) (W : U.toScheme.Opens) :
    Scheme.Modules.restrict M (U.ι ''ᵁ W).ι ≅
      Scheme.Modules.restrict
        (Scheme.Modules.restrict (Scheme.Modules.restrict M U.ι) W.ι) (U.ι.isoImage W).inv :=
  (Scheme.Modules.restrictFunctorCongr (U.ι.isoImage_inv_ι W).symm).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (U.ι.isoImage W).inv (W.ι ≫ U.ι)).app M ≪≫
    (Scheme.Modules.restrictFunctor (U.ι.isoImage W).inv).mapIso
      ((Scheme.Modules.restrictFunctorComp W.ι U.ι).app M)

/-- **A module whose restrictions to the members of an open cover are invertible is
invertible.** -/
theorem isInvertible_of_isInvertible_restrict {ι : Type*} (U : ι → Y.Opens)
    (hU : (⨆ i, U i) = ⊤) (M : Y.Modules)
    (hM : ∀ i, Stacks.SheafOfModules.IsInvertible (U i).toScheme.presheaf
      (structureSheafRing (U i).toScheme.toRingedSpace).property
      (Scheme.Modules.restrict M (U i).ι)) :
    Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property M := by
  choose W hW hiso using fun i =>
    @Stacks.Modules.exists_restrict_iso_unit_of_isInvertible _ _ (hM i)
  refine Stacks.SheafOfModules.isInvertible_of_coversTop_nonempty_iso_unit
    Y.presheaf (structureSheafRing Y.toRingedSpace).property M
    (X := fun p : Σ i, (U i).toScheme => (U p.1).ι ''ᵁ W p.1 p.2) ?_ fun p => ⟨?_⟩
  · refine (Opens.coversTop_iff _ _).2 (IsOpenCover.mk (top_le_iff.1 fun y _ => ?_))
    have hy : y ∈ (⨆ i, U i) := by simp [hU]
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hy
    have hz : (⟨y, hi⟩ : (U i).toScheme) ∈ (⨆ z, W i z) := by
      rw [hW i]
      exact Opens.mem_top _
    obtain ⟨z, hz⟩ := Opens.mem_iSup.1 hz
    exact Opens.mem_iSup.2 ⟨⟨i, z⟩, ⟨_, hz, rfl⟩⟩
  · exact Stacks.Modules.overIsoUnitOfRestrictIsoUnit M _
      (restrictImageIso M (U p.1) (W p.1 p.2) ≪≫
        (Scheme.Modules.restrictFunctor _).mapIso (hiso p.1 p.2).some ≪≫
        Scheme.Modules.restrictUnitIso _)

/-! ### Extending a Picard class -/

/-- **`extendByUnit U V L` is invertible** when `L` is and `U`, `V` are disjoint opens covering
`Y`. -/
theorem isInvertible_extendByUnit {U V : Y.Opens} (h : Disjoint U V) (hcover : U ⊔ V = ⊤)
    (L : U.toScheme.Modules)
    [hL : Stacks.SheafOfModules.IsInvertible U.toScheme.presheaf
      (structureSheafRing U.toScheme.toRingedSpace).property L] :
    Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property (extendByUnit U V L) := by
  refine isInvertible_of_isInvertible_restrict (fun b : Bool => bif b then U else V) ?_ _ ?_
  · rw [← hcover, iSup_bool_eq]
    rfl
  · rintro (_ | _) <;> dsimp only [cond]
    · have := Stacks.SheafOfModules.isInvertible_unit V.toScheme.presheaf
        (structureSheafRing V.toScheme.toRingedSpace).property
      exact Stacks.SheafOfModules.isInvertible_of_iso _ _
        (restrictExtendByUnitIsoUnit h L).symm
    · exact Stacks.SheafOfModules.isInvertible_of_iso _ _ (restrictExtendByUnitIso h L).symm

/-- **Every Picard class of `U` extends to a Picard class of `Y` which is trivial on `V`**, for
disjoint opens `U`, `V` covering `Y`. -/
theorem exists_schemePullbackClass_eq_and_eq_zero {U V : Y.Opens} (h : Disjoint U V)
    (hcover : U ⊔ V = ⊤) (x : ofScheme U.toScheme) :
    ∃ y : ofScheme Y, schemePullbackClass U.ι y = x ∧ schemePullbackClass V.ι y = 0 := by
  let L := (picardRepresentative U.toScheme.toRingedSpace x).obj
  have hM := isInvertible_extendByUnit h hcover L
    (hL := (picardRepresentative U.toScheme.toRingedSpace x).property)
  refine ⟨Stacks.SheafOfModules.picardClass Y.presheaf
    (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) (extendByUnit U V L) hM, ?_, ?_⟩
  · refine (pullbackClass_classOf U.ι.toLRSHom.toShHom _ hM).trans ?_
    conv_rhs => rw [← classOf_picardRepresentative U.toScheme.toRingedSpace x]
    exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
      ⟨(Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app _ ≪≫
        restrictExtendByUnitIso h L⟩
  · exact (pullbackClass_classOf V.ι.toLRSHom.toShHom _ hM).trans
      ((Stacks.AlgebraicGeometry.PicardBaseChange.classOf_eq_zero_iff_nonempty_iso_unit
        (X := V.toScheme.toRingedSpace) _ _).2
        ⟨(Scheme.Modules.restrictFunctorIsoPullback V.ι).symm.app _ ≪≫
          restrictExtendByUnitIsoUnit h L⟩)

/-! ### `Pic(Y) → ∏ᵢ Pic(U i)` is bijective -/

/-- Pullback of Picard classes along an inclusion of opens factors through a larger open. -/
theorem schemePullbackClass_ι_of_le {U W : Y.Opens} (e : U ≤ W) (y : ofScheme Y) :
    schemePullbackClass U.ι y = schemePullbackClass (Y.homOfLE e) (schemePullbackClass W.ι y) := by
  rw [schemePullbackClass, schemePullbackClass, pullbackClass_comp, ← Y.homOfLE_ι e]
  rfl

/-- **`Pic(Y) → ∏ᵢ Pic(U i)` is surjective for a finite pairwise disjoint open cover `U` of
`Y`.** -/
theorem surjective_schemePullbackClass_pi_of_pairwise_disjoint {ι : Type*} [Finite ι]
    (U : ι → Y.Opens) (hcover : IsOpenCover U) (hdisj : Pairwise (Function.onFun Disjoint U)) :
    Function.Surjective
      (fun x : ofScheme Y ↦ fun i ↦ schemePullbackClassHom (U i).ι x) := by
  classical
  have := Fintype.ofFinite ι
  intro x
  have hV : ∀ i, Disjoint (U i) (⨆ j : {j // j ≠ i}, U j) := fun i =>
    disjoint_iSup_iff.mpr fun j => hdisj j.2.symm
  have hcov : ∀ i, U i ⊔ (⨆ j : {j // j ≠ i}, U j) = ⊤ := fun i => by
    refine top_le_iff.mp fun y _ => ?_
    have hy : y ∈ (⨆ j, U j) := by simp [hcover.iSup_eq_top]
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hy
    rcases eq_or_ne j i with rfl | hji
    · exact Or.inl hj
    · exact Or.inr (Opens.mem_iSup.mpr ⟨⟨j, hji⟩, hj⟩)
  choose y hyU hyV using fun i => exists_schemePullbackClass_eq_and_eq_zero (hV i) (hcov i) (x i)
  refine ⟨∑ i, y i, funext fun j => ?_⟩
  change schemePullbackClassHom (U j).ι (∑ i, y i) = x j
  rw [map_sum, Finset.sum_eq_single j]
  · exact hyU j
  · intro i _ hij
    have hle : U j ≤ ⨆ k : {k // k ≠ i}, U k := le_iSup (fun k : {k // k ≠ i} => U k) ⟨j, hij.symm⟩
    change schemePullbackClass (U j).ι (y i) = 0
    rw [schemePullbackClass_ι_of_le hle, hyV i]
    exact map_zero (schemePullbackClassHom (Y.homOfLE hle))
  · exact absurd (Finset.mem_univ j)

/-- **`Pic(Y) ≃ ∏ᵢ Pic(U i)` for a finite pairwise disjoint open cover `U` of `Y`**, the map
being pullback along the inclusions. -/
theorem bijective_schemePullbackClass_pi_of_pairwise_disjoint {ι : Type*} [Finite ι]
    (U : ι → Y.Opens) (hcover : IsOpenCover U) (hdisj : Pairwise (Function.onFun Disjoint U)) :
    Function.Bijective
      (fun x : ofScheme Y ↦ fun i ↦ schemePullbackClassHom (U i).ι x) :=
  ⟨injective_schemePullbackClass_pi_of_pairwise_disjoint U hcover hdisj,
    surjective_schemePullbackClass_pi_of_pairwise_disjoint U hcover hdisj⟩

end Stacks.Picard

namespace AlgebraicGeometry

open Stacks.Picard (ofScheme schemePullbackClassHom zmodTorsionRestrictPi)

attribute [local instance] AddSubgroup.torsionBy.zmodModule

/-- The `ℓ`-torsion of an abelian group is a free `F_ℓ`-module. -/
private instance free_zmod_torsionBy (A : Type*) [AddCommGroup A] (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.Free (ZMod ℓ) (AddSubgroup.torsionBy A (ℓ : ℤ)) :=
  Module.Free.of_divisionRing _ _

/-- **`Pic(Y)[ℓ] → ∏ᵢ Pic(U i)[ℓ]` is bijective** for a finite pairwise disjoint open cover `U`
of `Y`. -/
theorem bijective_zmodTorsionRestrictPi_picard {Y : Scheme.{u}} {ι : Type*} [Finite ι]
    (U : ι → Y.Opens) (hcover : IsOpenCover U) (hdisj : Pairwise (Function.onFun Disjoint U))
    (ℓ : ℕ) :
    Function.Bijective (zmodTorsionRestrictPi (A := ofScheme Y)
      (B := fun i ↦ ofScheme (U i).toScheme) (fun i ↦ schemePullbackClassHom (U i).ι) ℓ) := by
  have hb := Stacks.Picard.bijective_schemePullbackClass_pi_of_pairwise_disjoint U hcover hdisj
  refine ⟨Stacks.Picard.injective_zmodTorsionRestrictPi _ ℓ hb.1.injOn, fun z => ?_⟩
  obtain ⟨x, hx⟩ := hb.2 fun i => (z i : ofScheme (U i).toScheme)
  have hxt : x ∈ AddSubgroup.torsionBy (ofScheme Y) (ℓ : ℤ) := by
    refine AddSubgroup.torsionBy.nsmul_iff.mpr (hb.1 ?_)
    funext i
    have hi : schemePullbackClassHom (U i).ι x = z i := congrFun hx i
    change schemePullbackClassHom (U i).ι (ℓ • x) = schemePullbackClassHom (U i).ι 0
    rw [map_nsmul, hi, map_zero]
    exact AddSubgroup.torsionBy.nsmul_iff.mp (z i).2
  exact ⟨⟨x, hxt⟩, funext fun i => Subtype.ext (congrFun hx i)⟩

/-- **`dim_{F_ℓ} Pic(Y)[ℓ] = ∑ᵢ dim_{F_ℓ} Pic(U i)[ℓ]`**, as cardinals, for a finite pairwise
disjoint open cover `U` of a scheme `Y` and a prime `ℓ`. -/
theorem rank_picardTorsion_eq_sum_of_pairwise_disjoint {Y : Scheme.{u}} {ι : Type u} [Finite ι]
    (U : ι → Y.Opens) (hcover : IsOpenCover U) (hdisj : Pairwise (Function.onFun Disjoint U))
    (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y) (ℓ : ℤ)) =
      Cardinal.sum fun i ↦
        Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme (U i).toScheme) (ℓ : ℤ)) := by
  rw [(LinearEquiv.ofBijective _ (bijective_zmodTorsionRestrictPi_picard U hcover hdisj ℓ)).rank_eq]
  exact rank_pi

/-- **`dim_{F_ℓ} Pic(Y)[ℓ] = ∑ᵢ dim_{F_ℓ} Pic(U i)[ℓ]`** for a finite pairwise disjoint open
cover `U` of a scheme `Y` and a prime `ℓ`, the `ℓ`-torsion of each `Pic(U i)` being
finite-dimensional. -/
theorem finrank_picardTorsion_eq_sum_of_pairwise_disjoint {Y : Scheme.{u}} {ι : Type*}
    [Fintype ι] (U : ι → Y.Opens) (hcover : IsOpenCover U)
    (hdisj : Pairwise (Function.onFun Disjoint U)) (ℓ : ℕ) [Fact ℓ.Prime]
    (hfin : ∀ i, FiniteDimensional (ZMod ℓ)
      (AddSubgroup.torsionBy (ofScheme (U i).toScheme) (ℓ : ℤ))) :
    Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y) (ℓ : ℤ)) =
      ∑ i, Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme (U i).toScheme) (ℓ : ℤ)) := by
  rw [(LinearEquiv.ofBijective _
    (bijective_zmodTorsionRestrictPi_picard U hcover hdisj ℓ)).finrank_eq]
  exact Module.finrank_pi_fintype _

end AlgebraicGeometry

end
