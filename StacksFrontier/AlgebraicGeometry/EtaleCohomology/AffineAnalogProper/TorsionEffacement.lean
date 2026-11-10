module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.EffaceableRestriction
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AffineClosedInjectiveVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.PrimaryDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProjectiveLineGeometricFibreCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionEtaleCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# Effacing a class on a closed subscheme by a torsion sheaf on the ambient affine scheme

Let `X` be an affine scheme, `i : Z ⟶ X` a closed immersion, `F` a torsion abelian sheaf on
`X_étale` and `ξ ∈ H^q_ét(Z, F|_Z)` with `q > 0`. Then there is a monomorphism `F ⟶ F'` of torsion
abelian sheaves on `X_étale` such that `ξ` maps to zero in `H^q_ét(Z, F'|_Z)`. This is
[Stacks, Tag 09ZE].

The proof is the one of the Stacks project.

1. A torsion sheaf is the filtered colimit of its subsheaves `F[n!]`
   (`Stacks.Torsion.isIso_torsionFiltrationDesc`, the union `𝓕 = ⋃ 𝓕[d]` of Stacks 0DDC), and
   restriction to `Z` is a left adjoint, so by Stacks 03Q5
   (`Stacks.EtaleCohomology.exists_comp_mk₀_eq_of_isColimit`) the class `ξ` comes from a class of
   some `F[n!]|_Z`. Likewise a sheaf killed by `ℓ > 0` is a filtered colimit of constructible
   sheaves (Stacks 03SA, `SmallEtale.exists_isColimit_moduleSheafToEtale_isConstructible`), so a
   class of its restriction comes from a constructible `𝒢 ⟶ F[n!]`.
2. A constructible `𝒢` embeds into `⨁ f_{k,*} M̲_k` with `f_k` finite of finite presentation and
   `M_k` finite (Stacks 09Z7). On each summand the class dies along the monomorphism
   `f_{k,*} M̲ ⟶ f_{k,*} π_{k,*} π_k^{-1} M̲` for a finite surjective `π_k` (Stacks 0959, 03QC,
   03QP and 09ZD (2), through `Stacks.EtaleCohomology.exists_comp_directImage_unit_eq_zero`).
3. A class which dies along a monomorphism `𝒢 ⟶ 𝒢'` dies, after pushing it to `F`, along the
   pushout monomorphism `F ⟶ 𝒢' ⊔_𝒢 F` (`Stacks.EtaleCohomology.effaces_pushout_inr`); the pushout
   of torsion sheaves is torsion, torsion sheaves forming a Serre subcategory (Stacks 0DD7).

Steps 1 (for the constructible stage) and 2 are those of
`Stacks.EtaleCohomology.subsingleton_H_closed_of_isAffine_of_torsion_extension`; here they are
followed by the pushout instead of an extension into an injective object.

## Main results

* `Stacks.EtaleCohomology.exists_effacing_stage_of_zsmul_id_eq_zero` — for a sheaf killed by a
  positive integer `ℓ`, a class comes from a stage `G ⟶ F` on which it dies along a monomorphism
  into a sheaf killed by `ℓ`.
* `Stacks.EtaleCohomology.torsionSheafProperty_pushout` — a pushout of torsion sheaves is torsion.
* `Stacks.EtaleCohomology.exists_mono_comp_etaleAbelianInverseImage_eq_zero_of_torsion`
  — **Stacks 09ZE**.

## Implementation notes

Cohomology is `CategoryTheory.Sheaf.H` on Mathlib's small étale site, with coefficients in
`AddCommGrpCat.{u + 1}`; restriction to `Z` is the exact inverse-image functor
`Stacks.EtaleCohomology.etaleAbelianInverseImage i`, and the image of `ξ` in `H^q(Z, F'|_Z)` is the
composite of `ξ` with the degree-zero class of `i⁻¹(F ⟶ F')`. "Torsion" is the local condition of
Stacks 0DD7, `Stacks.Torsion.torsionSheafProperty`: every local section is annihilated, locally,
by a positive integer.

## References

* [Stacks Project, Tag 09ZE](https://stacks.math.columbia.edu/tag/09ZE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u v

attribute [local instance 3000] Abelian.hasFiniteBiproducts

namespace Stacks.EtaleCohomology

/-- A biproduct of objects each killed by `n` is killed by `n`. -/
theorem biproduct_zsmul_id_eq_zero {C : Type*} [Category C] [Preadditive C] {J : Type*}
    {f : J → C} [HasBiproduct f] {n : ℤ} (h : ∀ j, n • 𝟙 (f j) = 0) : n • 𝟙 (⨁ f) = 0 :=
  biproduct.hom_ext _ _ fun j => by
    rw [Preadditive.zsmul_comp, Category.id_comp, zero_comp,
      ← Category.comp_id (biproduct.π f j), ← Preadditive.comp_zsmul, h, comp_zero]

/-- An additive functor preserves being killed by `n`. -/
theorem zsmul_id_obj_eq_zero_of_additive {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (E : C ⥤ D) [E.Additive] {X : C} {n : ℤ} (h : n • 𝟙 X = 0) :
    n • 𝟙 (E.obj X) = 0 := by
  rw [← E.map_id, ← Functor.map_zsmul, h, E.map_zero]

/-- A module over `ZMod ℓ` is, as an abelian group, killed by `ℓ`. -/
theorem zsmul_id_forget₂_obj_eq_zero (ℓ : ℕ) (M : ModuleCat.{v} (ULift.{v} (ZMod ℓ))) :
    ((ℓ : ℤ) • 𝟙 ((forget₂ (ModuleCat.{v} (ULift.{v} (ZMod ℓ))) AddCommGrpCat.{v}).obj M)) =
      0 := by
  ext x
  let x' : M := x
  have : ((ℓ : ℕ) : ULift.{v} (ZMod ℓ)) = 0 := congrArg ULift.up (ZMod.natCast_self ℓ)
  change ((ℓ : ℤ) • x') = 0
  rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (ULift.{v} (ZMod ℓ)), this, zero_smul]

/-- Composing a class with `i⁻¹(a ≫ b)` is composing with `i⁻¹ a` and then with `i⁻¹ b`. -/
private theorem comp_mk₀_map_comp {X Z : Scheme.{u}} (i : Z ⟶ X)
    {A B C : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (a : A ⟶ B) (b : B ⟶ C) {q : ℕ}
    (y : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i).obj A) q) :
    y.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} i).map (a ≫ b))) (add_zero q) =
      (y.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} i).map a)) (add_zero q)).comp
        (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} i).map b)) (add_zero q) := by
  rw [Functor.map_comp, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero]

/-- Let `X` be affine and `i : Z ⟶ X` a closed immersion. A class `y ∈ H^q(Z, G|_Z)`, `q > 0`, on a
finite sum `G = ⨁ f_{j,*} N̲_j` with `f_j` finite and `N_j` finite abelian groups killed by `ℓ`,
dies along a monomorphism `G ⟶ G'` into a sheaf killed by `ℓ`. -/
theorem exists_mono_biproduct_directImage_constantSheaf_comp_eq_zero
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i] {n : ℕ}
    {Y : Fin n → Scheme.{u}} (f : ∀ j, Y j ⟶ X) [∀ j, IsFinite (f j)]
    (N : Fin n → AddCommGrpCat.{u + 1}) [∀ j, Finite (N j)] (ℓ : ℤ) (hN : ∀ j, ℓ • 𝟙 (N j) = 0)
    (q : ℕ) (hq : 0 < q)
    (y : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i).obj
      (⨁ fun j => (etaleAbelianDirectImage.{u, 0} (f j)).obj
        ((constantSheaf (Y j).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (N j)))) q) :
    ∃ (G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (W : (⨁ fun j => (etaleAbelianDirectImage.{u, 0} (f j)).obj
        ((constantSheaf (Y j).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (N j))) ⟶ G'),
      Mono W ∧ ℓ • 𝟙 G' = 0 ∧
        y.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} i).map W)) (add_zero q) = 0 := by
  let Ti := etaleAbelianInverseImage.{u, 0} i
  let P : Fin n → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} := fun j =>
    (etaleAbelianDirectImage.{u, 0} (f j)).obj
      ((constantSheaf (Y j).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (N j))
  choose Y' π hπ hπs hπk using fun j => exists_comp_directImage_unit_eq_zero i (f j) (N j) q hq
    (y.comp (Ext.mk₀ (Ti.map (biproduct.π P j))) (add_zero q))
  let P' : Fin n → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} := fun j =>
    (etaleAbelianDirectImage.{u, 0} (f j)).obj ((etaleAbelianDirectImage.{u, 0} (π j)).obj
      ((etaleAbelianInverseImage.{u, 0} (π j)).obj
        ((constantSheaf (Y j).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (N j))))
  let w : ∀ j, P j ⟶ P' j := fun j => (etaleAbelianDirectImage.{u, 0} (f j)).map
    ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (π j)).unit.app
      ((constantSheaf (Y j).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (N j)))
  have hw : ∀ j, Mono (w j) := fun j => by
    have : Surjective (π j) := hπs j
    have : Mono ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (π j)).unit.app
        ((constantSheaf (Y j).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (N j))) :=
      mono_etaleAbelianUnit_of_surjective (π j) _
    exact Functor.map_mono _ _
  refine ⟨⨁ P', biproduct.map w, inferInstance, biproduct_zsmul_id_eq_zero fun j => ?_, ?_⟩
  · let C := constantSheaf (Y j).smallEtaleTopology AddCommGrpCat.{u + 1}
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts C
    have : C.Additive := Functor.additive_of_preservesBinaryBiproducts _
    exact zsmul_id_obj_eq_zero_of_additive (C ⋙ etaleAbelianInverseImage.{u, 0} (π j) ⋙
      etaleAbelianDirectImage.{u, 0} (π j) ⋙ etaleAbelianDirectImage.{u, 0} (f j)) (hN j)
  rw [show biproduct.map w = ∑ j, biproduct.π P j ≫ w j ≫ biproduct.ι P' j from biproduct.map_eq,
    Ti.map_sum, ext_comp_mk₀_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [comp_mk₀_map_comp, comp_mk₀_map_comp, hπk j, Ext.zero_comp]

/-- **An effacing constructible stage of a sheaf killed by `ℓ`.** Let `X` be affine,
`i : Z ⟶ X` a closed immersion, `ℓ > 0` and `F` an abelian sheaf on `X_étale` killed by `ℓ`. Every
class `ξ ∈ H^q(Z, F|_Z)` with `q > 0` is the image of a class `ζ ∈ H^q(Z, G|_Z)` along some
`g : G ⟶ F` such that `ζ` dies in `H^q(Z, G'|_Z)` for a monomorphism `G ⟶ G'` into an abelian
sheaf `G'` killed by `ℓ`. Here `G` is constructible and `G'` is a finite sum of sheaves
`f_* π_* π⁻¹ M̲` with `f`, `π` finite. -/
theorem exists_effacing_stage_of_zsmul_id_eq_zero
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i] (ℓ : ℕ) [NeZero ℓ]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : ((ℓ : ℤ) • 𝟙 F) = 0)
    (q : ℕ) (hq : 0 < q) (ξ : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i).obj F) q) :
    ∃ (G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (g : G ⟶ F) (ι : G ⟶ G'),
      Mono ι ∧ ((ℓ : ℤ) • 𝟙 G') = 0 ∧
        ∃ ζ : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i).obj G) q,
          ζ.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} i).map g)) (add_zero q) = ξ ∧
            ζ.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} i).map ι)) (add_zero q) = 0 := by
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
    SmallEtale.exists_isColimit_moduleSheafToEtale_isConstructible B XB ℓ F hF
  let T := SmallEtale.moduleSheafToEtale B XB Λ
  let Ti := etaleAbelianInverseImage.{u, 0} i
  have : PreservesColimitsOfSize.{u + 1, u + 1} Ti :=
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} i).leftAdjoint_preservesColimits
  obtain ⟨k, ζ, hζ⟩ := exists_comp_mk₀_eq_of_isColimit Z _ _ (isColimitOfPreserves Ti hc) q ξ
  obtain ⟨n, Y, f, hf, hfp, M, hM, φ, hφ⟩ :=
    AlgebraicGeometry.exists_mono_biproduct_pushforward_constantSheaf_of_isConstructibleModuleSheaf
      B Λ XB (D.obj k) (hD k)
  let N : Fin n → AddCommGrpCat.{u + 1} := fun j =>
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj (M j)
  have hNfin : ∀ j, Finite (N j) := fun j => by
    have : Module.Finite Λ (M j) := hM j
    have : Finite (M j) := Module.finite_of_finite Λ
    exact inferInstanceAs (Finite (M j))
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
  have : Mono (T.map φ) := mono_moduleSheafToEtale_map B XB Λ φ
  have : Mono m := mono_comp _ _
  obtain ⟨G', W, hW, hG', hyW⟩ :=
    exists_mono_biproduct_directImage_constantSheaf_comp_eq_zero i fm N (ℓ : ℤ)
      (fun j => zsmul_id_forget₂_obj_eq_zero ℓ (M j)) q hq
      (ζ.comp (Ext.mk₀ (Ti.map m)) (add_zero q))
  refine ⟨_, G', ι.app k, m ≫ W, mono_comp _ _, hG', ζ, hζ, ?_⟩
  rwa [comp_mk₀_map_comp]

/-- The pushout of two torsion abelian sheaves on `X_étale` is torsion: it is a quotient of their
biproduct, and torsion sheaves form a Serre subcategory (Stacks 0DD7). -/
theorem torsionSheafProperty_pushout {X : Scheme.{u}}
    {G F F' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (a : G ⟶ F) (b : G ⟶ F')
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F)
    (hF' : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F') :
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology (pushout a b) := by
  have : Epi (biprod.desc (pushout.inl a b) (pushout.inr a b)) :=
    ⟨fun g h hgh => pushout.hom_ext
      (by simpa using biprod.inl ≫= hgh) (by simpa using biprod.inr ≫= hgh)⟩
  exact (Stacks.Torsion.torsionSheafProperty.{u + 1} X.smallEtaleTopology).prop_of_epi
    (biprod.desc (pushout.inl a b) (pushout.inr a b))
    ((Stacks.Torsion.torsionSheafProperty.{u + 1} X.smallEtaleTopology).prop_biprod hF hF')

/-- **Stacks 09ZE.** Let `X` be an affine scheme, `F` a torsion abelian sheaf on `X_étale`,
`Z ⊂ X` a closed subscheme (`i : Z ⟶ X` a closed immersion) and `ξ ∈ H^q_ét(Z, F|_Z)` for some
`q > 0`. Then there exists an injective map `F ⟶ F'` of torsion abelian sheaves on `X_étale` such
that the image of `ξ` in `H^q_ét(Z, F'|_Z)` is zero.

Restriction to `Z` is the inverse image `etaleAbelianInverseImage i`, and the image of `ξ` is its
composite with the degree-zero class of `i⁻¹(F ⟶ F')`. Torsion is the local condition of
Stacks 0DD7, `Stacks.Torsion.torsionSheafProperty`. -/
@[stacks 09ZE]
theorem exists_mono_comp_etaleAbelianInverseImage_eq_zero_of_torsion
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (q : ℕ) (hq : 0 < q)
    (ξ : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i).obj F) q) :
    ∃ (F' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : F ⟶ F'), Mono φ ∧
      Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F' ∧
        ξ.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} i).map φ)) (add_zero q) = 0 := by
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated i
  let := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
  let Ti := etaleAbelianInverseImage.{u, 0} i
  have : PreservesColimitsOfSize.{u + 1, u + 1} Ti :=
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} i).leftAdjoint_preservesColimits
  have : IsIso (Stacks.Torsion.torsionFiltrationDesc X.smallEtaleTopology F) :=
    Stacks.Torsion.isIso_torsionFiltrationDesc _ F hF
  have hc : IsColimit (Cocone.mk F (Stacks.Torsion.torsionFiltrationι X.smallEtaleTopology F)) :=
    IsColimit.ofIsoColimit (colimit.isColimit _)
      (Cocone.ext (asIso (Stacks.Torsion.torsionFiltrationDesc X.smallEtaleTopology F))
        (fun j ↦ Stacks.Torsion.ι_torsionFiltrationDesc _ F j))
  obtain ⟨n, ζ, hζ⟩ := exists_comp_mk₀_eq_of_isColimit Z _ _ (isColimitOfPreserves Ti hc) q ξ
  have : NeZero (Nat.factorial n.down) := ⟨Nat.factorial_ne_zero _⟩
  have hn : (((Nat.factorial n.down : ℕ) : ℤ) •
      𝟙 ((Stacks.Torsion.torsionFiltration X.smallEtaleTopology F).obj n)) = 0 := by
    rw [natCast_zsmul]
    exact nsmul_id_kernel_eq_zero F _
  obtain ⟨G, G', g, ι, hι, hG', ζ', hζ'g, hζ'ι⟩ :=
    exists_effacing_stage_of_zsmul_id_eq_zero i _ _ hn q hq ζ
  let g' := g ≫ (Stacks.Torsion.torsionFiltrationι X.smallEtaleTopology F).app n
  obtain ⟨hmono, hkill⟩ := effaces_pushout_inr.{u, 0, u + 1} i g' ι q ζ' hζ'ι
  refine ⟨pushout ι g', pushout.inr ι g', hmono,
    torsionSheafProperty_pushout ι g'
      (torsionSheafProperty_of_zsmul_id_eq_zero (Nat.factorial_pos _) hG') hF, ?_⟩
  have hξ : ζ'.comp (Ext.mk₀ (Ti.map g')) (add_zero q) = ξ := by
    rw [comp_mk₀_map_comp, hζ'g, ← hζ]
    rfl
  rwa [← hξ]

end Stacks.EtaleCohomology

end
