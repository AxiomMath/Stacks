module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.NormalizationRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.EtaleCoverRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FilteredColimitClasses
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionDegreewise
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Coproduct

/-!
# Restriction of a constant sheaf on a curve through the components of its normalization

Let `Y` be proper over a separably closed field `k`, of dimension at most one, and let `k'` be a
separably closed extension of `k`. Write `Ỹ = ∐ Zᵢ` for the normalization of `Y` over `k`, split
into its normal irreducible pieces (Stacks 0BXR), and `gᵢ : Zᵢ ⟶ Y` for the composite finite
morphisms; they are jointly surjective, the normalization being finite and dominant. For a finite
abelian group `M` killed by a prime `ℓ` the constant sheaf `M_Y` is a finite sum of copies of
`ℤ/ℓ`, and `ℤ/ℓ_Y` embeds into `⨁ᵢ gᵢ_* gᵢ^{-1} ℤ/ℓ_Y = ⨁ᵢ gᵢ_* ℤ/ℓ_{Zᵢ}`, with cokernel killed by
`ℓ`. Restriction to `Y_{k'}` on `gᵢ_* ℤ/ℓ_{Zᵢ}` is restriction on `ℤ/ℓ_{Zᵢ}` to `(Zᵢ)_{k'}`, since
`gᵢ` is finite. So surjectivity in degree `q` for `M_Y` follows from surjectivity in degree `q`
for `ℤ/ℓ` on every proper normal irreducible `k`-scheme of dimension at most one, together with
injectivity in degree `q` and surjectivity in degree `q - 1` for sheaves on `Y` killed by `ℓ`.
This is the last step of the dévissage of Stacks 03SC (7) before the base case.

## Main results

* `Stacks.EtaleCohomology.exists_iso_biproduct_zmod` — a finite abelian group killed by a prime
  `ℓ` is a finite biproduct of copies of `ℤ/ℓ`.
* `Stacks.EtaleCohomology.finite_of_isOpenImmersion_cover` — a compact scheme which is a coproduct
  of nonempty schemes has finitely many summands.
* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_constant_zmod_of_normal` —
  the reduction of `ℤ/ℓ_Y` to the normal irreducible components of the normalization.
* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_constant_of_normal` — the same
  for `M_Y`, `M` finite and killed by `ℓ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **A finite abelian group killed by a prime is a finite sum of copies of `ℤ/ℓ`.** It is a
finite-dimensional vector space over `𝔽_ℓ`. -/
theorem exists_iso_biproduct_zmod (ℓ : ℕ) [Fact ℓ.Prime] (M : AddCommGrpCat.{u + 1}) [Finite M]
    (hM : (ℓ : ℤ) • 𝟙 M = 0) :
    ∃ r : ℕ, Nonempty (M ≅ ⨁ fun _ : Fin r => AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) := by
  have hx : ∀ x : M, ℓ • x = 0 := fun x => by
    have h := congrArg (fun φ : M ⟶ M => φ.hom x) hM
    simpa [natCast_zsmul] using h
  let : Module (ZMod ℓ) M := AddCommGroup.zmodModule hx
  have h1 : Module.Free (ZMod ℓ) M := Module.Free.of_divisionRing (ZMod ℓ) M
  have h2 : Module.Finite (ZMod ℓ) M := Module.Finite.of_finite
  let b := @Module.finBasis (ZMod ℓ) M _ _ _ h1 _ h2
  refine ⟨Module.finrank (ZMod ℓ) M, ⟨?_⟩⟩
  refine ?_ ≪≫ (AddCommGrpCat.biproductIsoPi _).symm
  exact AddEquiv.toAddCommGrpIso (b.equivFun.toAddEquiv.trans
    (AddEquiv.piCongrRight fun _ => AddEquiv.ulift.symm))

/-- **A compact coproduct of nonempty schemes has finitely many summands.** The summands are a
cover of the coproduct by pairwise disjoint nonempty opens. -/
theorem finite_of_compactSpace_sigma {I : Type u} (Z : I → Scheme.{u}) [∀ i, Nonempty (Z i)]
    [CompactSpace (∐ Z : Scheme.{u})] : Finite I := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i => Set.range (Sigma.ι Z i).base) (fun i => (Sigma.ι Z i).isOpenEmbedding.isOpen_range)
    (fun x _ => Set.mem_iUnion.2 (Stacks.Chow.exists_mem_range_sigmaι Z x))
  refine Set.finite_univ_iff.1 (t.finite_toSet.subset fun i _ => ?_)
  by_contra hi
  obtain ⟨z⟩ := ‹∀ i, Nonempty (Z i)› i
  obtain ⟨j, hj, hjz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ ((Sigma.ι Z i).base z)))
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  exact Set.disjoint_left.1 (Stacks.Chow.pairwise_disjoint_range_sigmaι Z hij) ⟨z, rfl⟩ hjz

/-- An additive functor carries an object killed by `n` to one killed by `n`. -/
theorem zsmul_id_map_eq_zero {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] {A : C} {n : ℤ} (hA : n • 𝟙 A = 0) :
    n • 𝟙 (F.obj A) = 0 := by
  rw [← F.map_id, ← F.map_zsmul, hA, F.map_zero]

/-- A finite biproduct of objects killed by `n` is killed by `n`. -/
theorem zsmul_id_biproduct_eq_zero {C : Type*} [Category C] [Preadditive C] {J : Type}
    [Finite J] (f : J → C) [HasBiproduct f] {n : ℤ} (hf : ∀ j, n • 𝟙 (f j) = 0) :
    n • 𝟙 (⨁ f) = 0 := by
  refine biproduct.hom_ext _ _ fun j => ?_
  rw [Preadditive.zsmul_comp, Category.id_comp, zero_comp, ← Category.comp_id (biproduct.π f j),
    ← Preadditive.comp_zsmul, hf j, comp_zero]

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsSepClosed k] [IsSepClosed k']

omit [IsSepClosed k] [IsSepClosed k'] in
/-- **The constant sheaf `ℤ/ℓ` on a curve, through the components of its normalization.** Let `Y`
be proper over `k` of dimension at most one, `ℓ` a prime and `q` a degree. Suppose restriction to
the scalar extension is surjective in degree `q` on `ℤ/ℓ` for every proper normal irreducible
`k`-scheme of dimension at most one, and, for sheaves on `Y` killed by `ℓ`, injective in degree
`q` and surjective in degree `q - 1`. Then it is surjective in degree `q` on `ℤ/ℓ_Y`.

The normal irreducible pieces `Zᵢ` of the normalization of `Y` give jointly surjective finite
morphisms `gᵢ : Zᵢ ⟶ Y`; the sum of the units `ℤ/ℓ_Y ⟶ ⨁ᵢ gᵢ_* gᵢ^{-1} ℤ/ℓ_Y` is a monomorphism
with cokernel killed by `ℓ`, and on each `gᵢ_* gᵢ^{-1} ℤ/ℓ_Y = gᵢ_* ℤ/ℓ_{Zᵢ}` restriction is
restriction on `ℤ/ℓ_{Zᵢ}`, `gᵢ` being finite. -/
theorem surjective_etaleCohomologyRestrictionMap_constant_zmod_of_normal
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k)) [IsProper π] (hdim : topologicalKrullDim Y ≤ 1)
    (ℓ : ℕ) (q : ℕ)
    (hbase : ∀ (C : Scheme.{u}) (πC : C ⟶ Spec (.of k)), IsProper πC → IsNormal C →
      IrreducibleSpace C → topologicalKrullDim C ≤ 1 →
      Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (scalarExtensionFst k k' πC) ((constantSheaf C.smallEtaleTopology
          AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))) q))
    (hinj : ∀ G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}, (ℓ : ℤ) • 𝟙 G = 0 →
      Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (scalarExtensionFst k k' π) G q))
    (hprev : ∀ m, q = m + 1 → ∀ G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1},
      (ℓ : ℤ) • 𝟙 G = 0 → Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (scalarExtensionFst k k' π) G m)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' π)
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))) q) := by
  have : LocallyOfFiniteType π := inferInstance
  let ν := normalizationOverField k π
  have : IsFinite ν := isFinite_normalizationOverField k π
  have : IsDominant ν := isDominant_normalizationOverField k π
  obtain ⟨I, Z, hirr, hnorm, e, -⟩ :=
    exists_iso_normalizationSchemeOverField_coproduct_normal_irreducible k π
  have : ∀ i, Nonempty (Z i) := fun i => (hirr i).toNonempty
  have : CompactSpace (∐ Z : Scheme.{u}) := by
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace π
    have : CompactSpace (normalizationSchemeOverField k π) :=
      QuasiCompact.compactSpace_of_compactSpace ν
    exact (QuasiCompact.compactSpace_of_compactSpace e.inv :)
  have : Finite I := finite_of_compactSpace_sigma Z
  let σ := (Finite.equivFin I).symm
  let g : ∀ a : Fin (Nat.card I), Z (σ a) ⟶ Y := fun a => Sigma.ι Z (σ a) ≫ e.inv ≫ ν
  have hgfin : ∀ a, IsFinite (g a) := fun a => by
    have := Stacks.Chow.isClosedImmersion_sigmaι Z (σ a)
    dsimp only [g]
    infer_instance
  have hg : ⋃ a, Set.range (g a).base = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨x, rfl⟩ := ν.surjective y
    obtain ⟨i, hi⟩ := Stacks.Chow.exists_mem_range_sigmaι Z (e.hom.base x)
    have hi' : e.hom.base x ∈ Set.range (Sigma.ι Z (σ (σ.symm i))).base := by
      rwa [Equiv.apply_symm_apply]
    obtain ⟨z, hz⟩ := hi'
    refine Set.mem_iUnion.2 ⟨σ.symm i, z, ?_⟩
    simp only [g, Scheme.Hom.comp_apply]
    rw [hz]
    show (e.hom ≫ e.inv ≫ ν).base x = _
    rw [e.hom_inv_id_assoc]
  let A := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))
  have hA : (ℓ : ℤ) • 𝟙 A = 0 := by
    have : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).Additive := inferInstance
    refine zsmul_id_map_eq_zero _ ?_
    ext x
    simp
  let P := fun a => (etaleAbelianDirectImage.{u, 0} (g a)).obj
    ((etaleAbelianInverseImage.{u, 0} (g a)).obj A)
  let m : A ⟶ ⨁ P := biproduct.lift fun a =>
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} (g a)).unit.app A
  have : Mono m := mono_biproductLift_unit_of_iUnion_range_eq_univ g hg A
  have hP : (ℓ : ℤ) • 𝟙 (⨁ P) = 0 := zsmul_id_biproduct_eq_zero P fun a =>
    zsmul_id_map_eq_zero _ (zsmul_id_map_eq_zero _ hA)
  have hQ : (ℓ : ℤ) • 𝟙 (cokernel m) = 0 := by
    have h := nsmul_id_cokernel_eq_zero_of_nsmul_id.{u, 0} m (n := ℓ)
      (by rw [← natCast_zsmul]; exact hP)
    rwa [← natCast_zsmul] at h
  refine surjective_etaleCohomologyRestrictionMap_of_mono.{u, 0, u + 1} _ m q ?_
    (hinj _ hQ) fun n hn => hprev n hn _ hQ
  refine surjective_etaleCohomologyRestrictionMap_biproduct.{u, u + 1} _ P q fun a => ?_
  have := hgfin a
  rw [etaleCohomologyRestrictionMap_surjective_directImage_iff_of_isFinite.{u, u + 1} (g a) _ _ _
    (isPullback_scalarExtension_closed k k' π (g a))]
  have := hirr (σ a)
  have := hnorm (σ a)
  have : IsProper (g a ≫ π) := inferInstance
  exact surjective_etaleCohomologyRestrictionMap_of_iso_objectUniverse.{u, u + 1} _
    ((etaleAbelianInverseImageConstantIso.{u, 0} (g a)).app _).symm q
    (hbase (Z (σ a)) (g a ≫ π) inferInstance inferInstance inferInstance
      ((topologicalKrullDim_le_of_locallyQuasiFinite (g a)).trans hdim))

omit [IsSepClosed k] [IsSepClosed k'] in
/-- **The constant sheaf of a finite group killed by `ℓ` on a curve, through the components of its
normalization.** The hypotheses are those of
`Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_constant_zmod_of_normal`; the
constant sheaf of `M ≅ (ℤ/ℓ)^r` is the biproduct of `r` copies of `ℤ/ℓ_Y`, the constant sheaf
functor being additive. -/
theorem surjective_etaleCohomologyRestrictionMap_constant_of_normal
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k)) [IsProper π] (hdim : topologicalKrullDim Y ≤ 1)
    (ℓ : ℕ) [Fact ℓ.Prime] (M : AddCommGrpCat.{u + 1}) [Finite M] (hM : (ℓ : ℤ) • 𝟙 M = 0)
    (q : ℕ)
    (hbase : ∀ (C : Scheme.{u}) (πC : C ⟶ Spec (.of k)), IsProper πC → IsNormal C →
      IrreducibleSpace C → topologicalKrullDim C ≤ 1 →
      Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (scalarExtensionFst k k' πC) ((constantSheaf C.smallEtaleTopology
          AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))) q))
    (hinj : ∀ G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}, (ℓ : ℤ) • 𝟙 G = 0 →
      Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (scalarExtensionFst k k' π) G q))
    (hprev : ∀ m, q = m + 1 → ∀ G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1},
      (ℓ : ℤ) • 𝟙 G = 0 → Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (scalarExtensionFst k k' π) G m)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' π)
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q) := by
  obtain ⟨r, ⟨eM⟩⟩ := exists_iso_biproduct_zmod ℓ M hM
  let K := constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}
  have : K.Additive := inferInstance
  refine surjective_etaleCohomologyRestrictionMap_of_iso_objectUniverse.{u, u + 1} _
    ((K.mapBiproduct _).symm ≪≫ K.mapIso eM.symm) q ?_
  exact surjective_etaleCohomologyRestrictionMap_biproduct.{u, u + 1} _ _ q fun _ =>
    surjective_etaleCohomologyRestrictionMap_constant_zmod_of_normal k k' π hdim ℓ q hbase hinj
      hprev

end Stacks.EtaleCohomology

end
