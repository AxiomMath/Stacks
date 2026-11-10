module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.NormalComponentsRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.DenseOpenRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ReductionRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteOverFieldRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.GenericallyConstantColimit
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleDescent

/-!
# The induction on the degree for restriction to a scalar extension of a curve

Let `k ⊆ k'` be separably closed fields and `ℓ` a prime. This file assembles the dévissage of
Stacks 03SC (7): surjectivity of restriction `H^q(X, F) ⟶ H^q(X_{k'}, F)` for every sheaf `F`
killed by `ℓ` on every proper `k`-scheme `X` of dimension at most one, by induction on `q`, from

* injectivity of restriction in every degree, for every abelian sheaf on such an `X`;
* the base case: surjectivity in every degree for `ℤ/ℓ` on every proper normal irreducible
  `k`-scheme of dimension at most one.

The step in degree `q` is the source's. Replacing `X` by its reduction changes nothing. The sheaf
`F` is a filtered colimit of sheaves `G` killed by `ℓ` which, near every generic point `η`, become
constant on a finite group `M_η` along an étale `h_η : V_η ⟶ X` from an affine scheme, and
cohomology commutes with that colimit. The images of the `h_η` form a dense open `W` whose
complement `Z` is finite over `k`, so `G` embeds into `i_* i^{-1} G ⊕ ⨁_η h_η* h_η^{-1} G`, with
cokernel killed by `ℓ` (handled by injectivity and the degree `q - 1`). On `i_* i^{-1} G`
restriction is bijective, `Z` being finite over `k`. On `h_η* M_η`, `h_η` factors as an open
immersion `t` into the normalization `Y` of `X` in `V_η` followed by the finite `ν : Y ⟶ X`, so
restriction on `h_η* M_η` is restriction on `t_* M_η` over `Y`, which reduces to `M_Y`, and the
constant sheaf `M_Y` reduces through the components of the normalization of `Y` to the base case.

## Main results

* `exists_iso_constantSheaf_of_zsmul_id_eq_zero`: a constant sheaf killed by `n` is the constant
  sheaf of a group killed by `n`.
* `surjective_etaleCohomologyRestrictionMap_directImage_inverseImage_of_etale`: the step on
  `h_* h^{-1} G` for `h^{-1} G` constant.
* `surjective_etaleCohomologyRestrictionMap_of_constant_near_genericPoints`: the step for a sheaf
  constant near the generic points of a reduced curve.
* `surjective_etaleCohomologyRestrictionMap_of_zsmul_id_eq_zero_of_curve`: the induction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **A constant sheaf killed by `n` is the constant sheaf of a group killed by `n`.** The
constant sheaf functor preserves cokernels and is additive, so the constant sheaf of
`M / nM = coker (n : M ⟶ M)` is the cokernel of `n` on the constant sheaf of `M`, which is zero. -/
theorem exists_iso_constantSheaf_of_zsmul_id_eq_zero {V : Scheme.{u}}
    (M : AddCommGrpCat.{u + 1}) [Finite M] (n : ℤ)
    (h : n • 𝟙 ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) = 0) :
    ∃ M' : AddCommGrpCat.{u + 1}, Finite M' ∧ n • 𝟙 M' = 0 ∧
      Nonempty ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M ≅
        (constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M') := by
  let K := constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}
  have : K.Additive := inferInstance
  have : PreservesFiniteColimits K := by
    have : (presheafToSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).IsLeftAdjoint :=
      (sheafificationAdjunction _ _).isLeftAdjoint
    exact inferInstanceAs (PreservesFiniteColimits (Functor.const _ ⋙ presheafToSheaf _ _))
  let φ : M ⟶ M := n • 𝟙 M
  refine ⟨cokernel φ, ?_, ?_, ⟨?_⟩⟩
  · exact Finite.of_surjective _ ((AddCommGrpCat.epi_iff_surjective (cokernel.π φ)).1 inferInstance)
  · refine (cancel_epi (cokernel.π φ)).1 ?_
    rw [Preadditive.comp_zsmul, Category.comp_id, comp_zero, ← Category.id_comp (cokernel.π φ),
      ← Preadditive.zsmul_comp]
    exact cokernel.condition φ
  · have hφ : K.map φ = 0 := by rw [Functor.map_zsmul, K.map_id]; exact h
    exact cokernelZeroIsoTarget.symm ≪≫ cokernelIsoOfEq hφ.symm ≪≫
      (PreservesCokernel.iso K φ).symm

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsSepClosed k] [IsSepClosed k']

/-- A proper scheme over an affine scheme is compact and quasi-separated. -/
private theorem compactSpace_and_quasiSeparatedSpace_of_isProper {Z : Scheme.{u}}
    {R : CommRingCat.{u}} (f : Z ⟶ Spec R) [IsProper f] :
    CompactSpace Z ∧ QuasiSeparatedSpace Z :=
  ⟨QuasiCompact.compactSpace_of_compactSpace f, quasiSeparatedSpace_of_quasiSeparated f⟩

omit [IsSepClosed k] in
/-- A proper scheme over a field is Noetherian. -/
theorem isNoetherian_of_isProper {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsProper π] :
    IsNoetherian X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  have := (compactSpace_and_quasiSeparatedSpace_of_isProper π).1
  exact AlgebraicGeometry.IsNoetherian.mk

/-- **The step on `h_* h^{-1} G` for `h^{-1} G` constant.** Let `X` be reduced and proper over `k`,
of dimension at most one, `h : V ⟶ X` étale from an affine scheme with `h^{-1} G ≅ M_V`, `M` finite
and killed by the prime `ℓ`. Then restriction to the scalar extension is surjective in degree `q`
on `h_* h^{-1} G`, given the base case in degree `q`, injectivity everywhere, and surjectivity in
degree `q - 1` for sheaves killed by `ℓ` on proper `k`-schemes of dimension at most one. -/
theorem surjective_etaleCohomologyRestrictionMap_directImage_inverseImage_of_etale
    {X V : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsProper π] [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1) (h : V ⟶ X) [Etale h] [IsAffine V]
    (ℓ : ℕ) [Fact ℓ.Prime] (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (M : AddCommGrpCat.{u + 1}) [Finite M] (hM : (ℓ : ℤ) • 𝟙 M = 0)
    (e : (etaleAbelianInverseImage.{u, 0} h).obj G ≅
      (constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) (q : ℕ)
    (hbase : ∀ (C : Scheme.{u}) (πC : C ⟶ Spec (.of k)), IsProper πC → IsNormal C →
      IrreducibleSpace C → topologicalKrullDim C ≤ 1 →
      Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (scalarExtensionFst k k' πC) ((constantSheaf C.smallEtaleTopology
          AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))) q))
    (hinj : ∀ (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of k)), IsProper πY →
      topologicalKrullDim Y ≤ 1 → ∀ (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
        (p : ℕ), Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
          (scalarExtensionFst k k' πY) G p))
    (hprev : ∀ m, q = m + 1 → ∀ (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of k)), IsProper πY →
      topologicalKrullDim Y ≤ 1 → ∀ G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1},
        (ℓ : ℤ) • 𝟙 G = 0 → Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
          (scalarExtensionFst k k' πY) G m)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' π)
      ((etaleAbelianDirectImage.{u, 0} h).obj ((etaleAbelianInverseImage.{u, 0} h).obj G)) q) := by
  have : IsNoetherian X := isNoetherian_of_isProper k π
  obtain ⟨Y, t, ν, ht, hν, htν, hgen⟩ :=
    exists_isOpenImmersion_isFinite_factorization_of_etale k π h
  refine surjective_etaleCohomologyRestrictionMap_of_iso_objectUniverse.{u, u + 1} _
    ((etaleAbelianDirectImage.{u, 0} h).mapIso e.symm) q ?_
  rw [surjective_etaleCohomologyRestrictionMap_directImage_comp_iff.{u, u + 1} k k' π t ν h
    htν.symm]
  have : IsProper (ν ≫ π) := inferInstance
  have hdimY : topologicalKrullDim Y ≤ 1 :=
    (topologicalKrullDim_le_of_locallyQuasiFinite ν).trans hdim
  have : IsNoetherian Y := isNoetherian_of_isProper k (ν ≫ π)
  exact surjective_etaleCohomologyRestrictionMap_directImage_constant k k' (ν ≫ π) hdimY t hgen M q
    (surjective_etaleCohomologyRestrictionMap_constant_of_normal k k' (ν ≫ π) hdimY ℓ M hM q hbase
      (fun G _ => hinj Y _ inferInstance hdimY G q)
      (fun m hm G hG => hprev m hm Y _ inferInstance hdimY G hG))
    (fun G => hinj Y _ inferInstance hdimY G (q + 1))

/-- **The step for a sheaf constant near the generic points of a reduced curve.** Let `X` be
reduced and proper over `k`, of dimension at most one, and `G` killed by the prime `ℓ` such that
every generic point lies in the image of an étale `h : V ⟶ X` from an affine scheme along which `G`
becomes constant on a finite group killed by `ℓ`. Then restriction is surjective in degree `q` on
`G`, given the base case in degree `q`, injectivity everywhere, and the degree `q - 1`. -/
theorem surjective_etaleCohomologyRestrictionMap_of_constant_near_genericPoints
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsProper π] [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1) (ℓ : ℕ) [Fact ℓ.Prime]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : (ℓ : ℤ) • 𝟙 G = 0)
    (hloc : ∀ η ∈ genericPoints X, ∃ (V : Scheme.{u}) (h : V ⟶ X), Etale h ∧ IsAffine V ∧
      η ∈ Set.range h.base ∧ ∃ M : AddCommGrpCat.{u + 1}, Finite M ∧ (ℓ : ℤ) • 𝟙 M = 0 ∧
        Nonempty ((etaleAbelianInverseImage.{u, 0} h).obj G ≅
          (constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)) (q : ℕ)
    (hbase : ∀ (C : Scheme.{u}) (πC : C ⟶ Spec (.of k)), IsProper πC → IsNormal C →
      IrreducibleSpace C → topologicalKrullDim C ≤ 1 →
      Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (scalarExtensionFst k k' πC) ((constantSheaf C.smallEtaleTopology
          AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))) q))
    (hinj : ∀ (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of k)), IsProper πY →
      topologicalKrullDim Y ≤ 1 → ∀ (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
        (p : ℕ), Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
          (scalarExtensionFst k k' πY) G p))
    (hprev : ∀ m, q = m + 1 → ∀ (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of k)), IsProper πY →
      topologicalKrullDim Y ≤ 1 → ∀ G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1},
        (ℓ : ℤ) • 𝟙 G = 0 → Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
          (scalarExtensionFst k k' πY) G m)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' π)
      G q) := by
  have : IsNoetherian X := isNoetherian_of_isProper k π
  have : Finite (genericPoints X) :=
    (genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).to_subtype
  let σ := (Finite.equivFin (genericPoints X)).symm
  choose V h hh hV hηV M hMfin hMℓ he using fun a : Fin (Nat.card (genericPoints X)) =>
    hloc (σ a).1 (σ a).2
  let W : X.Opens := ⟨⋃ a, Set.range (h a).base,
    isOpen_iUnion fun a => (isOpenMap_of_etale (h a) (hh a)).isOpen_range⟩
  have hW : genericPoints X ⊆ W := fun η hη => by
    refine Set.mem_iUnion.2 ⟨σ.symm ⟨η, hη⟩, ?_⟩
    have := hηV (σ.symm ⟨η, hη⟩)
    rwa [Equiv.apply_symm_apply] at this
  obtain ⟨Z, i, hi, hZfin, hZ⟩ := exists_isClosedImmersion_isFinite_range_eq_compl k π hdim W hW
  let T : Option (Fin (Nat.card (genericPoints X))) → Scheme.{u} := fun o => o.elim Z V
  let g : ∀ o, T o ⟶ X := fun o => Option.rec (motive := fun o => T o ⟶ X) i h o
  have hg : ⋃ o, Set.range (g o).base = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ (W : Set X)
    · obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hx
      exact Set.mem_iUnion.2 ⟨some a, ha⟩
    · have : x ∈ Set.range i.base := by rw [hZ]; exact hx
      exact Set.mem_iUnion.2 ⟨none, this⟩
  let P := fun o => (etaleAbelianDirectImage.{u, 0} (g o)).obj
    ((etaleAbelianInverseImage.{u, 0} (g o)).obj G)
  let m : G ⟶ ⨁ P := biproduct.lift fun o =>
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} (g o)).unit.app G
  have : Mono m := mono_biproductLift_unit_of_iUnion_range_eq_univ g hg G
  have hP : (ℓ : ℤ) • 𝟙 (⨁ P) = 0 := zsmul_id_biproduct_eq_zero P fun o =>
    have : (etaleAbelianDirectImage.{u, 0} (g o)).Additive :=
      Functor.additive_of_preserves_binary_products _
    zsmul_id_map_eq_zero _ (zsmul_id_map_eq_zero _ hG)
  have hQ : (ℓ : ℤ) • 𝟙 (cokernel m) = 0 := by
    have h := nsmul_id_cokernel_eq_zero_of_nsmul_id.{u, 0} m (n := ℓ)
      (by rw [← natCast_zsmul]; exact hP)
    rwa [← natCast_zsmul] at h
  refine surjective_etaleCohomologyRestrictionMap_of_mono.{u, 0, u + 1} _ m q ?_
    (hinj X π inferInstance hdim _ q) fun n hn => hprev n hn X π inferInstance hdim _ hQ
  refine surjective_etaleCohomologyRestrictionMap_biproduct.{u, u + 1} _ P q fun o => ?_
  cases o with
  | none =>
    have : IsFinite i := inferInstance
    change Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} _
      ((etaleAbelianDirectImage.{u, 0} i).obj ((etaleAbelianInverseImage.{u, 0} i).obj G)) q)
    rw [etaleCohomologyRestrictionMap_surjective_directImage_iff_of_isFinite.{u, u + 1} i _ _ _
      (isPullback_scalarExtension_closed k k' π i)]
    exact (etaleCohomologyRestrictionMap_bijective_of_isFinite_of_isSepClosed k k' (i ≫ π)
      _ q).2
  | some a =>
    have := hh a
    have := hV a
    have := hMfin a
    exact surjective_etaleCohomologyRestrictionMap_directImage_inverseImage_of_etale k k' π hdim
      (h a) ℓ G (M a) (hMℓ a) (he a).some q hbase hinj hprev

/-- **The step in degree `q` for a sheaf killed by a prime.** Let `X` be proper over `k` of
dimension at most one and `F` killed by the prime `ℓ`. Restriction is surjective in degree `q` on
`F`, given the base case in degree `q`, injectivity in every degree, and surjectivity in degree
`q - 1`. -/
theorem surjective_etaleCohomologyRestrictionMap_of_zsmul_id_eq_zero_step
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsProper π]
    (hdim : topologicalKrullDim X ≤ 1) (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : (ℓ : ℤ) • 𝟙 F = 0) (q : ℕ)
    (hbase : ∀ (C : Scheme.{u}) (πC : C ⟶ Spec (.of k)), IsProper πC → IsNormal C →
      IrreducibleSpace C → topologicalKrullDim C ≤ 1 →
      Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (scalarExtensionFst k k' πC) ((constantSheaf C.smallEtaleTopology
          AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))) q))
    (hinj : ∀ (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of k)), IsProper πY →
      topologicalKrullDim Y ≤ 1 → ∀ (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
        (p : ℕ), Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
          (scalarExtensionFst k k' πY) G p))
    (hprev : ∀ m, q = m + 1 → ∀ (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of k)), IsProper πY →
      topologicalKrullDim Y ≤ 1 → ∀ G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1},
        (ℓ : ℤ) • 𝟙 G = 0 → Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
          (scalarExtensionFst k k' πY) G m)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' π)
      F q) := by
  rw [surjective_etaleCohomologyRestrictionMap_iff_reduction.{u, u + 1} k k' π F q]
  let π₀ := X.reductionι ≫ π
  have : IsProper π₀ := inferInstance
  have hdim₀ : topologicalKrullDim X.reduction ≤ 1 :=
    (topologicalKrullDim_le_of_locallyQuasiFinite X.reductionι).trans hdim
  let F₀ := (etaleAbelianInverseImage.{u, 0} X.reductionι).obj F
  have hF₀ : (ℓ : ℤ) • 𝟙 F₀ = 0 := zsmul_id_map_eq_zero _ hF
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_isProper π₀
  have : IsProper (pullback.snd π₀ (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback π₀ _) ‹IsProper π₀›
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_isProper
    (pullback.snd π₀ (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨I, _, _, D, ι, ⟨hc⟩, hD⟩ :=
    exists_isColimit_isConstant_near_genericPoints X.reduction ℓ F₀ hF₀
  refine surjective_etaleCohomologyRestrictionMap_of_isColimit_of_qcqs X.reduction
    (scalarExtensionFst k k' π₀) hc q
    fun j => ?_
  exact surjective_etaleCohomologyRestrictionMap_of_constant_near_genericPoints k k' π₀ hdim₀ ℓ
    (D.obj j) (hD j).1 (hD j).2 q hbase hinj hprev

/-- **Stacks 03SC (7), the induction on the degree, for sheaves killed by a prime.** Let `k ⊆ k'`
be separably closed and `ℓ` a prime. Suppose restriction to the scalar extension is injective in
every degree for every abelian sheaf on every proper `k`-scheme of dimension at most one, and
surjective in every degree for `ℤ/ℓ` on every proper normal irreducible `k`-scheme of dimension at
most one. Then it is surjective in every degree for every sheaf killed by `ℓ` on every proper
`k`-scheme of dimension at most one. -/
theorem surjective_etaleCohomologyRestrictionMap_of_zsmul_id_eq_zero_of_curve
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hbase : ∀ (q : ℕ) (C : Scheme.{u}) (πC : C ⟶ Spec (.of k)), IsProper πC → IsNormal C →
      IrreducibleSpace C → topologicalKrullDim C ≤ 1 →
      Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (scalarExtensionFst k k' πC) ((constantSheaf C.smallEtaleTopology
          AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))) q))
    (hinj : ∀ (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of k)), IsProper πY →
      topologicalKrullDim Y ≤ 1 → ∀ (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
        (p : ℕ), Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
          (scalarExtensionFst k k' πY) G p))
    (q : ℕ) (X : Scheme.{u}) (π : X ⟶ Spec (.of k)) [IsProper π]
    (hdim : topologicalKrullDim X ≤ 1) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : (ℓ : ℤ) • 𝟙 F = 0) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' π)
      F q) := by
  induction q using Nat.strong_induction_on generalizing X with
  | _ q ih =>
    exact surjective_etaleCohomologyRestrictionMap_of_zsmul_id_eq_zero_step k k' π hdim ℓ F hF q
      (hbase q) hinj fun m hm Y πY _ hY G hG =>
        have : IsProper πY := ‹_›
        ih m (by omega) Y πY hY G hG

end Stacks.EtaleCohomology

end
