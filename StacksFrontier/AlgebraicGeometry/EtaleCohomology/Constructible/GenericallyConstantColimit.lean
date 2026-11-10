module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.GenericTrivialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.MainstreamTransport
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# Torsion sheaves as colimits of sheaves constant near the generic points

Let `X` be a reduced quasi-compact quasi-separated scheme and `F` an abelian sheaf on Mathlib's
small étale site of `X` annihilated by an integer `n > 0`. Then `F` is the colimit of a filtered
diagram of abelian sheaves, each annihilated by `n`, each of which becomes constant with finite
value on an affine scheme étale over `X` through any prescribed generic point of `X`.

## Main results

* `AlgebraicGeometry.exists_isColimit_isConstant_near_genericPoints` — the statement above.

## Implementation notes

The result follows from Stacks 03SA (3) on Mathlib's site
(`AlgebraicGeometry.SmallEtale.exists_isColimit_moduleSheafToEtale_isConstructible`) together with
the local constancy of a constructible sheaf near a generic point
(`exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_isConstructibleModuleSheaf`).

## References

* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

/-- Every element of a module over `ULift (ZMod n)` is killed by `n`. -/
private lemma intCast_zsmul_eq_zero_of_module_ulift_zmod (n : ℕ) {M : Type*} [AddCommGroup M]
    [Module (ULift.{u + 1} (ZMod n)) M] (y : M) : (n : ℤ) • y = 0 := by
  have h : ((n : ℤ) : ULift.{u + 1} (ZMod n)) = 0 := by
    ext
    simp
  rw [← Int.cast_smul_eq_zsmul (ULift.{u + 1} (ZMod n)), h, zero_smul]

/-- A sheaf of modules over `ULift (ZMod n)` is annihilated by `n` once its module structure is
forgotten. -/
private lemma zsmul_id_sheafCompose_forget₂ {C : Type*} [Category* C] (J : GrothendieckTopology C)
    (n : ℕ) [J.HasSheafCompose (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
      AddCommGrpCat.{u + 1})]
    (M : Sheaf J (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))) :
    (n : ℤ) • 𝟙 ((sheafCompose J (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
      AddCommGrpCat.{u + 1})).obj M) = 0 := by
  apply Sheaf.hom_ext
  ext U x
  let y : M.obj.obj U := x
  change (n : ℤ) • y = 0
  exact intCast_zsmul_eq_zero_of_module_ulift_zmod n y

/-- **A torsion sheaf on a reduced scheme is a filtered colimit of sheaves constant near the
generic points.** Let `X` be a reduced quasi-compact quasi-separated scheme, `n > 0`, and `F` an
abelian sheaf on Mathlib's small étale site of `X` annihilated by `n`. Then `F` is the colimit of a
filtered diagram `D` of abelian sheaves annihilated by `n` such that for every term `D i` and every
generic point `η` of `X` there is an étale morphism `h : V ⟶ X` from an affine scheme with `η` in
its image along which `D i` becomes the constant sheaf on a finite abelian group annihilated by
`n`. -/
public theorem exists_isColimit_isConstant_near_genericPoints (X : Scheme.{u}) [IsReduced X]
    [CompactSpace X] [QuasiSeparatedSpace X] (n : ℕ) [NeZero n]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : (n : ℤ) • 𝟙 F = 0) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, (n : ℤ) • 𝟙 (D.obj i) = 0 ∧
          ∀ η ∈ genericPoints X, ∃ (V : Scheme.{u}) (h : V ⟶ X), Etale h ∧ IsAffine V ∧
            η ∈ Set.range h.base ∧ ∃ M : AddCommGrpCat.{u + 1}, Finite M ∧ (n : ℤ) • 𝟙 M = 0 ∧
              Nonempty ((etaleAbelianInverseImage.{u, 0} h).obj (D.obj i) ≅
                (constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) := by
  let B := BigEtaleSite.containing X
  let XB : B.Scheme := B.obj X (BigEtaleSite.contains_containing X)
  have : CompactSpace XB.obj := ‹CompactSpace X›
  have : QuasiSeparatedSpace XB.obj := ‹QuasiSeparatedSpace X›
  have : IsReduced XB.obj := ‹IsReduced X›
  obtain ⟨I, hI, hfilt, D, ι, hc, hD⟩ :=
    SmallEtale.exists_isColimit_moduleSheafToEtale_isConstructible B XB n F hF
  refine ⟨I, hI, hfilt, D ⋙ SmallEtale.moduleSheafToEtale B XB _, ι, hc, fun i => ⟨?_, ?_⟩⟩
  · let E := SmallEtale.sheafEquiv B X (BigEtaleSite.contains_containing X) AddCommGrpCat.{u + 1}
    have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
    change (n : ℤ) • 𝟙 (E.functor.obj _) = 0
    rw [← E.functor.map_id, ← Functor.map_zsmul, zsmul_id_sheafCompose_forget₂, Functor.map_zero]
  · intro η hη
    obtain ⟨O, o, ho, hηo, hlc⟩ :=
      exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_isConstructibleModuleSheaf B _ XB
        (D.obj i) (hD i) hη
    obtain ⟨x, hx⟩ := hηo
    obtain ⟨V, E, hVa, hxV, hE, ⟨c⟩⟩ :=
      exists_etale_affine_constant_of_isFiniteTypeLocallyConstant B _ O _ hlc x
    let v : V.obj.left ⟶ XB := V.obj.hom ≫ o
    have : Etale (B.inclusion.map V.obj.hom) := V.property
    have : IsOpenImmersion (B.inclusion.map o) := ho
    refine ⟨V.obj.left.obj, B.inclusion.map v, ?_, hVa, ?_, ?_⟩
    · change Etale (B.inclusion.map V.obj.hom ≫ B.inclusion.map o)
      infer_instance
    · obtain ⟨y, hy⟩ := hxV
      refine ⟨y, ?_⟩
      change (B.inclusion.map o).base ((B.inclusion.map V.obj.hom).base y) = η
      rw [hy, hx]
    · have : Module.Finite (ULift.{u + 1} (ZMod n)) E := (ModuleCat.isFG_iff E).mp hE
      have : Finite (ULift.{u + 1} (ZMod n)) := Finite.of_equiv _ Equiv.ulift.symm
      have hfin : Finite E := Module.finite_of_finite (ULift.{u + 1} (ZMod n))
      refine ⟨(forget₂ _ AddCommGrpCat.{u + 1}).obj E, hfin, ?_, ⟨?_⟩⟩
      · ext x
        exact intCast_zsmul_eq_zero_of_module_ulift_zmod (M := E) n x
      exact (SmallEtale.moduleSheafToEtalePullbackIso B _ v).app (D.obj i) ≪≫
        (SmallEtale.moduleSheafToEtale B V.obj.left _).mapIso
          (((smallEtaleSheafPullbackCompIso B V.obj.left O XB V.obj.hom o _).app (D.obj i)).symm ≪≫
            c.symm) ≪≫
        (SmallEtale.moduleSheafToEtaleConstantIso B V.obj.left _).app E

end AlgebraicGeometry

end
