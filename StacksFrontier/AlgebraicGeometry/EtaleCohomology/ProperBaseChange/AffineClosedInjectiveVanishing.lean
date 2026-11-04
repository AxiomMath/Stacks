module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreFirstCohomologyInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.FiniteCoverKilling
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.FiniteDirectImageEffacement

/-!
# Injective sheaves of `ℤ/ℓℤ`-modules on a closed subscheme of an affine scheme

Let `X` be an affine scheme, `i : Z ⟶ X` a closed immersion, `ℓ > 0` and `𝓘` an injective sheaf of
`ℤ/ℓℤ`-modules on `X_étale`. Then `H^q(Z, 𝓘|_Z) = 0` for every `q > 0`. This is the case `n = 0` of
Stacks 0A51 for the ring of coefficients `ℤ/ℓℤ`, which is what the proof of Stacks 0A5H uses in
degrees `q ≥ 2` through Mayer–Vietoris.

The proof is the absorption argument of Stacks 0A5H run with Stacks 09ZD (2) in place of
Stacks 0A5G. A class comes from a constructible `𝒢 ⟶ 𝓘` (Stacks 03SA, 03Q5), `𝒢` embeds into
`⨁ f_{k,*} M̲_k` with `f_k` finite (Stacks 09Z7), and on each summand the class dies along the
monomorphism `f_{k,*} M̲ ⟶ f_{k,*} π_{k,*} π_k^{-1} M̲` for a finite surjective `π_k` killing its
transport to `Y_{k,Z}` (Stacks 09ZD (2), through
`Stacks.EtaleCohomology.comp_directImage_unit_eq_zero_of_restriction_eq_zero`). Since `𝓘` is
injective among sheaves killed by `ℓ`, `𝒢 ⟶ 𝓘` extends along the composite monomorphism, so the
class vanishes.

Stacks 09ZD (2) enters through
`Stacks.EtaleCohomology.exists_isFinite_surjective_restriction_eq_zero_of_iso_constantSheaf`.

## Main results

* `Stacks.EtaleCohomology.subsingleton_H_closed_of_isAffine_of_torsion_extension` — the
  vanishing for an abelian sheaf killed by `ℓ` and injective among such sheaves.
* `Stacks.EtaleCohomology.subsingleton_H_closed_of_injective_of_isAffine` — the vanishing for an
  injective sheaf of `ℤ/ℓℤ`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.Cohomology.ZModSheaf

universe u

attribute [local instance 3000] Abelian.hasFiniteBiproducts

namespace Stacks.EtaleCohomology

/-- **A class through a finite direct image of a constant sheaf dies along a unit.** Let `X` be
affine, `i : Z ⟶ X` a closed immersion, `f : Y ⟶ X` finite and `N` a finite abelian group. By
Stacks 09ZD (2), every `ζ ∈ H^q(Z, i^{-1} f_* N̲)`, `q > 0`, dies along the map induced by
the unit `N̲ ⟶ π_* π^{-1} N̲` for some finite surjective `π : Y' ⟶ Y`. -/
theorem exists_comp_directImage_unit_eq_zero
    {X Z Y : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i] (f : Y ⟶ X) [IsFinite f]
    (N : AddCommGrpCat.{u + 1}) [Finite N] (q : ℕ) (hq : 0 < q)
    (ζ : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i).obj
      ((etaleAbelianDirectImage.{u, 0} f).obj
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj N))) q) :
    ∃ (Y' : Scheme.{u}) (π : Y' ⟶ Y) (_ : IsFinite π) (_ : Surjective π),
      ζ.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} i).map
        ((etaleAbelianDirectImage.{u, 0} f).map
          ((etaleAbelianInverseImageDirectImageAdj.{u, 0} π).unit.app
            ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj N))))) (add_zero q) =
        0 := by
  have : IsAffine Y := isAffine_of_isAffineHom f
  let sq := IsPullback.of_hasPullback f i
  have : IsClosedImmersion (pullback.fst f i) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip ‹IsClosedImmersion i›
  obtain ⟨Y', π, hπ, hπs, -, h⟩ :=
    exists_isFinite_surjective_restriction_eq_zero_of_iso_constantSheaf (pullback.fst f i) N _
      ((etaleAbelianInverseImageConstantIso.{u, 0} (pullback.fst f i)).app N) q hq
      (finiteDirectImageTransport f i (pullback.fst f i) (pullback.snd f i) sq _ q ζ)
  exact ⟨Y', π, hπ, hπs, comp_directImage_unit_eq_zero_of_restriction_eq_zero f i
    (pullback.fst f i) (pullback.snd f i) sq π (pullback.fst π (pullback.fst f i))
    (pullback.snd π (pullback.fst f i)) (IsPullback.of_hasPullback _ _) _ q ζ h⟩

/-- An abelian sheaf `n` times whose identity vanishes has sections killed by `n`. -/
theorem nsmul_eq_zero_of_zsmul_id_eq_zero {X : Scheme.{u}}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (n : ℕ) (h : ((n : ℤ) • 𝟙 F) = 0)
    (U : X.Etaleᵒᵖ) (x : ToType (F.obj.obj U)) : n • x = 0 := by
  have h2 := congrArg (fun φ => φ.hom.app U x) h
  simp only [zsmul_app_apply] at h2
  rw [← natCast_zsmul]
  exact h2

/-- An abelian sheaf whose sections are killed by `n` is killed by `n`. -/
private theorem zsmul_id_eq_zero_of_nsmul_eq_zero {X : Scheme.{u}}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (n : ℕ)
    (h : ∀ (U : X.Etaleᵒᵖ) (x : ToType (F.obj.obj U)), n • x = 0) : ((n : ℤ) • 𝟙 F) = 0 := by
  apply Sheaf.hom_ext
  ext U x
  rw [zsmul_app_apply]
  change ((n : ℤ) • x) = 0
  exact (natCast_zsmul x n).trans (h U x)

/-- Composing a class with `Ext.mk₀` of the images of two morphisms under a functor is composing
it with `Ext.mk₀` of the image of their composite. -/
private theorem ext_comp_mk₀_map_comp {C D : Type*} [Category C] [Category D] [Abelian D]
    [HasExt.{u + 1} D] (F : C ⥤ D) {S : D} {A B B' : C} {q : ℕ} (y : Ext.{u + 1} S (F.obj A) q)
    (a : A ⟶ B) (b : B ⟶ B') :
    (y.comp (Ext.mk₀ (F.map a)) (add_zero q)).comp (Ext.mk₀ (F.map b)) (add_zero q) =
      y.comp (Ext.mk₀ (F.map (a ≫ b))) (add_zero q) := by
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, F.map_comp]

/-- **The absorption argument on a closed subscheme of an affine scheme.** Let `X` be affine,
`i : Z ⟶ X` a closed immersion, `ℓ > 0` and `𝓘` an abelian sheaf on `X_étale` killed by `ℓ`
which is injective among the abelian sheaves killed by `ℓ`: every map into `𝓘` from a sheaf
killed by `ℓ` extends along a monomorphism into a sheaf killed by `ℓ`. Then `H^q(Z, 𝓘|_Z) = 0` for
every `q > 0`. -/
theorem subsingleton_H_closed_of_isAffine_of_torsion_extension
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i] (ℓ : ℕ) [NeZero ℓ]
    (TJ : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hTJ : ((ℓ : ℤ) • 𝟙 TJ) = 0)
    (hext : ∀ {P Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}},
      ((ℓ : ℤ) • 𝟙 P) = 0 → ((ℓ : ℤ) • 𝟙 Q) = 0 → ∀ (m : P ⟶ Q) [Mono m] (g : P ⟶ TJ),
        ∃ h : Q ⟶ TJ, m ≫ h = g)
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i).obj TJ) q) := by
  let Λ := ULift.{u + 1} (ZMod ℓ)
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated i
  let B := BigEtaleSite.containing X
  let XB : B.Scheme := B.obj X (BigEtaleSite.contains_containing X)
  have : CompactSpace XB.obj := inferInstanceAs (CompactSpace X)
  have : QuasiSeparatedSpace XB.obj := inferInstanceAs (QuasiSeparatedSpace X)
  let : HasSheafify (SmallEtale.topology B XB.obj XB.property) (ModuleCat.{u + 1} Λ) :=
    SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B XB Λ
  obtain ⟨I, _, _, D, ι, ⟨hc⟩, hD⟩ :=
    SmallEtale.exists_isColimit_moduleSheafToEtale_isConstructible B XB ℓ TJ hTJ
  let T := SmallEtale.moduleSheafToEtale B XB Λ
  let Ti := etaleAbelianInverseImage.{u, 0} i
  have : PreservesColimitsOfSize.{u + 1, u + 1} Ti :=
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} i).leftAdjoint_preservesColimits
  refine subsingleton_of_forall_eq 0 fun ξ => ?_
  obtain ⟨k, ζ, hζ⟩ := exists_comp_mk₀_eq_of_isColimit Z _ _ (isColimitOfPreserves Ti hc) q ξ
  obtain ⟨n, Y, f, hf, hfp, M, hM, φ, hφ⟩ :=
    AlgebraicGeometry.exists_mono_biproduct_pushforward_constantSheaf_of_isConstructibleModuleSheaf
      B Λ XB (D.obj k) (hD k)
  -- the target, on Mathlib's site
  let N : Fin n → AddCommGrpCat.{u + 1} := fun j =>
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj (M j)
  have hNfin : ∀ j, Finite (N j) := fun j => by
    have : Module.Finite Λ (M j) := hM j
    have : Finite (M j) := Module.finite_of_finite Λ
    exact inferInstanceAs (Finite (M j))
  have hNℓ : ∀ j, ((ℓ : ℤ) • 𝟙 (N j)) = 0 := fun j => by
    ext x
    let x' : M j := x
    have : ((ℓ : ℕ) : Λ) = 0 := congrArg ULift.up (ZMod.natCast_self ℓ)
    change ((ℓ : ℤ) • x') = 0
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul Λ, this, zero_smul]
  let fm : ∀ j, (Y j).obj ⟶ X := fun j => B.inclusion.map (f j)
  have : ∀ j, IsFinite (fm j) := hf
  let P : Fin n → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} := fun j =>
    (etaleAbelianDirectImage.{u, 0} (fm j)).obj
      ((constantSheaf (Y j).obj.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (N j))
  have : PreservesColimitsOfSize.{u + 1, u + 1} T :=
    SmallEtale.moduleSheafToEtale_preservesColimits B XB Λ
  have : PreservesColimitsOfSize.{0, 0} T := preservesColimitsOfSize_shrink T
  have : T.IsLeftAdjoint := SmallEtale.moduleSheafToEtale_isLeftAdjoint B XB Λ
  have : T.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint T
  have : ∀ G' : Fin n → Sheaf (SmallEtale.topology B XB.obj XB.property)
      (ModuleCat.{u + 1} Λ), PreservesBiproduct G' T := fun G' =>
    preservesBiproduct_of_preservesCoproduct T
  let m : T.obj (D.obj k) ⟶ ⨁ P := T.map φ ≫ (T.mapBiproduct _).hom ≫
    biproduct.map (fun j => (SmallEtale.moduleSheafToEtaleDirectImageConstantIso B Λ (f j)
      (M j)).hom)
  have hm : Mono m := by
    have : Mono (T.map φ) := mono_moduleSheafToEtale_map B XB Λ φ
    exact mono_comp _ _
  -- killing each summand
  let y := ζ.comp (Ext.mk₀ (Ti.map m)) (add_zero q)
  choose Y' π hπ hπs hπk using fun j => exists_comp_directImage_unit_eq_zero i (fm j) (N j) q hq
    (y.comp (Ext.mk₀ (Ti.map (biproduct.π P j))) (add_zero q))
  let P' : Fin n → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} := fun j =>
    (etaleAbelianDirectImage.{u, 0} (fm j)).obj ((etaleAbelianDirectImage.{u, 0} (π j)).obj
      ((etaleAbelianInverseImage.{u, 0} (π j)).obj
        ((constantSheaf (Y j).obj.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (N j))))
  let w : ∀ j, P j ⟶ P' j := fun j => (etaleAbelianDirectImage.{u, 0} (fm j)).map
    ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (π j)).unit.app
      ((constantSheaf (Y j).obj.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (N j)))
  have hw : ∀ j, Mono (w j) := fun j => by
    have : Surjective (π j) := hπs j
    have : Mono ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (π j)).unit.app
        ((constantSheaf (Y j).obj.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (N j))) :=
      mono_etaleAbelianUnit_of_surjective (π j) _
    exact Functor.map_mono _ _
  let W : ⨁ P ⟶ ⨁ P' := biproduct.map w
  have hyW : y.comp (Ext.mk₀ (Ti.map W)) (add_zero q) = 0 := by
    rw [show W = ∑ j, biproduct.π P j ≫ w j ≫ biproduct.ι P' j from biproduct.map_eq,
      Ti.map_sum, ext_comp_mk₀_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Category.assoc, ← ext_comp_mk₀_map_comp, ← ext_comp_mk₀_map_comp,
      hπk j, Ext.zero_comp]
  -- the target is killed by `ℓ`
  have hP'ℓ : ((ℓ : ℤ) • 𝟙 (⨁ P')) = 0 := by
    have hj : ∀ j, ((ℓ : ℤ) • 𝟙 (P' j)) = 0 := fun j => by
      let C := constantSheaf (Y j).obj.smallEtaleTopology AddCommGrpCat.{u + 1}
      have : C.Additive := by
        have := preservesBinaryBiproducts_of_preservesBinaryCoproducts C
        exact Functor.additive_of_preservesBinaryBiproducts _
      let E := C ⋙ etaleAbelianInverseImage.{u, 0} (π j) ⋙ etaleAbelianDirectImage.{u, 0} (π j) ⋙
        etaleAbelianDirectImage.{u, 0} (fm j)
      change ((ℓ : ℤ) • 𝟙 (E.obj (N j))) = 0
      rw [← E.map_id, ← Functor.map_zsmul, hNℓ, E.map_zero]
    refine biproduct.hom_ext _ _ fun j => ?_
    rw [Preadditive.zsmul_comp, Category.id_comp, zero_comp, ← Category.comp_id (biproduct.π P' j),
      ← Preadditive.comp_zsmul, hj, comp_zero]
  obtain ⟨h, hh⟩ := hext (zsmul_id_eq_zero_of_nsmul_eq_zero ℓ
    (nsmul_moduleSheafToEtale_eq_zero B XB ℓ (D.obj k))) hP'ℓ (m ≫ W) (ι.app k)
  have hξ : ξ = (y.comp (Ext.mk₀ (Ti.map W)) (add_zero q)).comp (Ext.mk₀ (Ti.map h))
      (add_zero q) := by
    rw [ext_comp_mk₀_map_comp, ext_comp_mk₀_map_comp Ti ζ, ← Category.assoc, hh, ← hζ]
    rfl
  rw [hξ, hyW, Ext.zero_comp]

/-- **Stacks 0A51 for `n = 0` and coefficients `ℤ/ℓℤ`.** Let `X` be an affine scheme,
`i : Z ⟶ X` a closed immersion, `ℓ > 0` and `𝓘` an injective sheaf of `ℤ/ℓℤ`-modules on
`X_étale`. Then `H^q(Z, 𝓘|_Z) = 0` for every `q > 0`. -/
theorem subsingleton_H_closed_of_injective_of_isAffine
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i] (ℓ : ℕ) [NeZero ℓ]
    (J : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ)) [Injective J]
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i).obj
      ((SheafOfModules.toSheaf _).obj J)) q) :=
  subsingleton_H_closed_of_isAffine_of_torsion_extension i ℓ _
    (zsmul_id_eq_zero_of_nsmul_eq_zero ℓ
      (nsmul_toSheaf_eq_zero.{u + 1, u + 1} X.smallEtaleTopology ℓ J))
    (fun hP hQ m _ g => exists_comp_eq_of_injective_toSheaf ℓ J
      (nsmul_eq_zero_of_zsmul_id_eq_zero ℓ hP) (nsmul_eq_zero_of_zsmul_id_eq_zero ℓ hQ) m g) q hq

end Stacks.EtaleCohomology

end
