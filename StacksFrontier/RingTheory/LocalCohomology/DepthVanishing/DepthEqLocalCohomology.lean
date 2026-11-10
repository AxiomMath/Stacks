module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
public import Mathlib.RingTheory.Depth.Rees
public import StacksFrontier.RingTheory.Depth.ExtAlongIdeal
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.BelowDepth
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.DerivedTorsion
public import StacksFrontier.RingTheory.Dualizing.LocalCohomologyNoetherian.UniverseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Depth is the first nonvanishing degree of `Ext` and of local cohomology

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `M` a finite `A`-module with `IM ≠ M`. The
`I`-depth of `M` admits three descriptions, and this file supplies two of the statements of
[Stacks, Lemma 0AVZ] relating them.

The first is a vanishing statement: `Ext^i_A(N, M) = 0` for every `i` below `depth_I(M)` and
every finite `A`-module `N` annihilated by a power of `I`. The point is that the hypothesis on
`N` is only that its support lies in `V(I)`, so Rees' theorem applies to it and not merely to
the residue module `A ⧸ I`.

The second identifies the depth with the least degree in which local cohomology supported on
`V(I)` is nonzero:

`depth_I(M) = inf {i | H^i_{V(I)}(M) ≠ 0}`,

the infimum being taken in `ℕ∞`, so that the empty set of degrees contributes `⊤`.

## Main results

* `Module.subsingleton_ext_of_lt_depth` — `Ext^i_A(N, M) = 0` for `i < depth_I(M)` and `N`
  finite and annihilated by a power of `I`.
* `Stacks.LocalCohomology.depth_eq_sInf_nontrivial_localCohomologyWithSupportIn` — the depth is
  the infimum of the degrees in which `H^i_{V(I)}(M)` is nonzero.
* `Stacks.LocalCohomology.depth_eq_sInf_nontrivial_ext_and_localCohomology_and_subsingleton_ext`
  — `depth_I(M)` is both the least degree of a nonzero `Ext^i_A(A ⧸ I, M)` and the least degree
  of a nonzero `H^i_{V(I)}(M)`, and the `Ext`-vanishing statement holds.

## Implementation notes

`HasDerivedCategory.standard` is a file-level local instance: both
`Stacks.LocalCohomology.localCohomologyWithSupportIn` and the `Ext` system of
`Dualizing.extPowers` are defined under it, so their model is part of their type.  The standard
model is a derived category of `ModuleCat A`, and `H^0_{V(I)}` at this model is the submodule of
supported sections, by `Stacks.LocalCohomology.nonempty_localCohomologyWithSupportIn_zero_iso`.

## References

* [Stacks Project, Tag 0AVZ](https://stacks.math.columbia.edu/tag/0AVZ)
* [Stacks Project, Tag 0954](https://stacks.math.columbia.edu/tag/0954)
* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)

## Tags

depth, local cohomology, ext, Rees theorem
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open Dualizing (powerTorsionComplex kInjectiveRepresentative kInjectiveRepresentativeIso
  localCohomology quotientPowerSucc extPowers)

attribute [local instance] HasDerivedCategory.standard

universe u v w z

namespace Module

/-- Ext from a finite module annihilated by a power of `I` vanishes below the `I`-depth. -/
@[stacks 0AVZ "Ext vanishing below depth for modules annihilated by an ideal power",
  sga "2 III 2.2" "(a), Noetherian f.g.",
  sga "2 IV 5.3" "Ext^i(M,A)=0 for i<n",
  sga "2 III 3.3" "affine (iv)⇒(v)"]
theorem subsingleton_ext_of_lt_depth
    (R : Type u) [CommRing R] [IsNoetherianRing R] [Small.{v} R]
    (I : Ideal R) (M N : ModuleCat.{v} R)
    [Module.Finite R M] [Module.Finite R N]
    (hIM : I • (⊤ : Submodule R M) ≠ ⊤)
    (hN : ∃ n : ℕ, I ^ n ≤ Module.annihilator R N)
    (i : ℕ) (hi : (i : ℕ∞) < Module.depth R I M) :
    Subsingleton (Ext N M i) := by
  obtain ⟨n, hn⟩ := hN
  have hsupp : Module.support R N ⊆ PrimeSpectrum.zeroLocus I := by
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]
    exact fun x hx => Ideal.mem_radical_iff.mpr ⟨n, hn (Ideal.pow_mem_pow hx n)⟩
  have hExtQ : ∀ j < i + 1,
      Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M j) := by
    intro j hj
    apply not_nontrivial_iff_subsingleton.mp
    intro hnt
    have hdepth : Module.depth R I (M : Type v) ≤ (j : ℕ∞) := by
      rw [Module.depth_eq_sInf_nontrivial_ext (R := R) (I := I) (M := (M : Type v))]
      exact sInf_le ⟨j, rfl, hnt⟩
    have hji : (j : ℕ∞) ≤ i := by exact_mod_cast (Nat.lt_succ_iff.mp hj)
    exact (not_le_of_gt (lt_of_le_of_lt hji hi)) hdepth
  obtain ⟨rs, hlen, hmem, hreg⟩ := (ModuleCat.exists_isRegular_tfae I (i + 1) M
      (lt_top_iff_ne_top.mpr hIM)).out 2 4 |>.mp hExtQ
  exact ModuleCat.subsingleton_ext_of_exists_isRegular I N hsupp M
    (lt_top_iff_ne_top.mpr hIM) rs hmem hreg i (by omega)

end Module

namespace Stacks.LocalCohomology.DepthEq

open Stacks.LocalCohomology

/-- A linear equivalence between the underlying modules identifies the `I`-power-torsion
submodules, after transporting along the equivalence. -/
private noncomputable def primaryComponentUliftEquiv
    (A : Type u) [CommRing A] (I : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M] :
    Ideal.primaryComponent M I ≃ₗ[A]
      Ideal.primaryComponent (ULift.{v} M) I := by
  let e : M ≃ₗ[A] ULift.{v} M := ULift.moduleEquiv.symm
  refine
    { toFun := fun x => ⟨e x.1, ?_⟩
      invFun := fun x => ⟨e.symm x.1, ?_⟩
      left_inv := by intro x; apply Subtype.ext; simp [e]
      right_inv := by intro x; apply Subtype.ext; simp [e]
      map_add' := by intro x y; apply Subtype.ext; exact map_add e x.1 y.1
      map_smul' := by intro r x; apply Subtype.ext; exact map_smul e r x.1 }
  · exact Ideal.primaryComponent_map_mem I e.toLinearMap x
  · exact Ideal.primaryComponent_map_mem I e.symm.toLinearMap x

/-- A small module is the universe lift of its own small model. -/
private noncomputable def moduleShrinkUliftIso
    (R : Type u) [CommRing R] [Small.{u} R]
    (M : ModuleCat.{max u v} R) [Small.{u} M] :
    (ModuleCat.uliftFunctor.{v} R).obj (ModuleCat.of R (Shrink.{u} M)) ≅ M :=
  LinearEquiv.toModuleIso
    ((ULift.moduleEquiv : ULift.{v} (Shrink.{u} M) ≃ₗ[R] Shrink.{u} M).trans
      (Shrink.linearEquiv R M))

/-- Whether `I` acts transitively on a module is invariant under a linear equivalence. -/
private lemma smul_top_eq_top_iff_of_linearEquiv
    (R : Type u) [CommRing R] (I : Ideal R) {M : Type w} {N : Type z}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    I • (⊤ : Submodule R M) = ⊤ ↔ I • (⊤ : Submodule R N) = ⊤ := by
  rw [← Submodule.map_eq_top_iff (e := e), Submodule.map_smul'', Submodule.map_top,
    LinearEquiv.range]

/-- Nontriviality transfers across an isomorphism of modules. -/
private lemma nontrivial_iff_of_moduleIso
    {R : Type u} [Ring R] {M N : ModuleCat.{w} R} (e : M ≅ N) :
    Nontrivial M ↔ Nontrivial N :=
  e.toLinearEquiv.toEquiv.nontrivial_congr

/-- For a K-injective complex representing `K`, local cohomology with support in `T` is the
cohomology of the complex of `T`-supported sections. -/
private noncomputable def localSupportHomologyIsoOfKInjective
    (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{max u v} A))
    (J : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (eK : DerivedCategory.Q.obj J ≅ K) [J.IsKInjective] (i : ℤ) :
    localCohomologyWithSupportIn.{u, v} A T K i ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
        (DerivedCategory.Q.obj
          (((sectionsWithSupportInFunctor.{u, v} A T).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J)) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso
      ((derivedSectionsWithSupportIn.{u, v} A T).mapIso
        (eK.symm ≪≫
          ((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app J).symm)) ≪≫
    localCohomologyWithSupportInIsoOfKInjective.{u, v} T i J ≪≫
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A) i).app
      (((sectionsWithSupportInFunctor.{u, v} A T).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J)).symm

/-- Local cohomology with support in `V(I)` is the cohomology of derived `I`-power torsion. -/
private noncomputable def localCohomologyWithSupportInHomologyIso
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    localCohomologyWithSupportIn.{u, 0} A
      (PrimeSpectrum.zeroLocus (I : Set A)) K i ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (localCohomology A I K) :=
  localSupportHomologyIsoOfKInjective.{u, 0} A (PrimeSpectrum.zeroLocus (I : Set A)) K
      (kInjectiveRepresentative A K) (kInjectiveRepresentativeIso A K) i ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
      (DerivedCategory.Q.mapIso
        (powerTorsionComplexIsoSectionsWithSupportIn A I
          (kInjectiveRepresentative A K)).symm)

/-- Local cohomology with support in `V(I)` of a universe-lifted module is the universe lift of
the cohomology of derived `I`-power torsion computed in the smaller universe. -/
private noncomputable def localCohomologyUliftIso
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : ModuleCat.{u} A) (i : ℤ) :
    localCohomologyWithSupportIn.{u, v} A
      (PrimeSpectrum.zeroLocus (I : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
        ((ModuleCat.uliftFunctor.{v} A).obj M)) i ≅
      (ModuleCat.uliftFunctor.{v} A).obj
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          (localCohomology A I
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)))) := by
  let C₀ := ModuleCat.{u} A
  let C₁ := ModuleCat.{max u v} A
  let U := ModuleCat.uliftFunctor.{v} A
  let K₀ := (DerivedCategory.singleFunctor C₀ 0).obj M
  let Kplus := (DerivedCategory.Plus.singleFunctor C₀ 0).obj M
  let hRes := DerivedCategory.Plus.exists_injective_nonempty_iso Kplus 0
  let L := Classical.choose hRes
  have hResL : ∃ (_ : L.obj.IsStrictlyGE 0),
      Nonempty (DerivedCategory.Plus.Q.obj
        ((InjectiveObject.ι C₀).mapCochainComplexPlus.obj L) ≅ Kplus) :=
    Classical.choose_spec hRes
  let hL : L.obj.IsStrictlyGE 0 := Classical.choose hResL
  let ePlus : DerivedCategory.Plus.Q.obj
      ((InjectiveObject.ι C₀).mapCochainComplexPlus.obj L) ≅ Kplus :=
    Classical.choice (Classical.choose_spec hResL)
  let J₀ := ((InjectiveObject.ι C₀).mapCochainComplexPlus.obj L).obj
  let e₀ : DerivedCategory.Q.obj J₀ ≅ K₀ := by
    let eι := DerivedCategory.Plus.ι.mapIso ePlus
    let eS := (DerivedCategory.Plus.singleFunctorιIso C₀ 0).app M
    change DerivedCategory.Q.obj J₀ ≅ K₀
    exact eι ≪≫ eS
  let UJ := (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj J₀
  have hJ₀GE : CochainComplex.IsStrictlyGE J₀ 0 := by
    exact (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff
      (K := L.obj) (F := InjectiveObject.ι C₀) 0).2 hL
  haveI : ∀ n : ℤ, Injective (J₀.X n) := by
    intro n
    change Injective ((InjectiveObject.ι C₀).obj (L.obj.X n))
    infer_instance
  letI : CochainComplex.IsStrictlyGE J₀ 0 := hJ₀GE
  have hJ₀ : CochainComplex.IsKInjective J₀ :=
    CochainComplex.isKInjective_of_injective J₀ 0
  letI : CochainComplex.IsKInjective J₀ := hJ₀
  letI : U.PreservesInjectiveObjects := inferInstance
  have hUJGE : CochainComplex.IsStrictlyGE UJ 0 := by
    exact (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff
      (K := J₀) (F := U) 0).2 hJ₀GE
  letI : CochainComplex.IsStrictlyGE UJ 0 := hUJGE
  haveI : ∀ n : ℤ, Injective (UJ.X n) := fun n => by
    change Injective (U.obj (J₀.X n))
    infer_instance
  have hUJ : CochainComplex.IsKInjective UJ :=
    CochainComplex.isKInjective_of_injective UJ 0
  letI : CochainComplex.IsKInjective UJ := hUJ
  let eU : DerivedCategory.Q.obj UJ ≅ U.mapDerivedCategory.obj K₀ :=
    (U.mapDerivedCategoryFactors.app J₀).symm ≪≫ U.mapDerivedCategory.mapIso e₀
  let eS := (U.mapDerivedCategorySingleFunctor 0).app M
  let eK : DerivedCategory.Q.obj UJ ≅
      (DerivedCategory.singleFunctor C₁ 0).obj (U.obj M) := eU ≪≫ eS
  let eBig := localSupportHomologyIsoOfKInjective.{u, v} A
    (PrimeSpectrum.zeroLocus (I : Set A)) _ UJ eK i
  let eSmall := (localCohomologyWithSupportInHomologyIso A I K₀ i).symm ≪≫
    (localSupportHomologyIsoOfKInjective.{u, 0} A
      (PrimeSpectrum.zeroLocus (I : Set A)) K₀ J₀ e₀ i) ≪≫
    (DerivedCategory.homologyFunctorFactors C₀ i).app
      (((sectionsWithSupportInFunctor.{u, 0}
        A (PrimeSpectrum.zeroLocus (I : Set A))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J₀)
  let eBig' := eBig ≪≫
    (DerivedCategory.homologyFunctorFactors C₁ i).app
      (((sectionsWithSupportInFunctor.{u, v}
        A (PrimeSpectrum.zeroLocus (I : Set A))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj UJ)
  let eLiftHomology := (uliftHomologyIso A
      (((sectionsWithSupportInFunctor.{u, 0}
        A (PrimeSpectrum.zeroLocus (I : Set A))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J₀) i).symm ≪≫
    HomologicalComplex.homologyMapIso
      (sectionsWithSupportUliftComplexIso A I J₀) i
  exact eBig' ≪≫ (U.mapIso eSmall ≪≫ eLiftHomology).symm

/-- The transition map of the system of quotients by powers of `I` sends the class of `r` to
the class of `r`. -/
private lemma quotientPowerSucc_hom_mk (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ) (r : R) :
    (quotientPowerSucc R I n).hom (Ideal.Quotient.mk (I ^ (n + 1)) r) =
      Ideal.Quotient.mk (I ^ n) r := rfl

/-- The transition map of the `Ext` system is precomposition with the quotient map. -/
lemma extPowers_succ_apply
    (R : Type u) [CommRing R] (I : Ideal R) (K : DerivedCategory (ModuleCat.{u} R))
    (q : ℤ) (n : ℕ)
    (x : DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (R ⧸ I ^ n))) K q) :
    (extPowers R I K q).map (homOfLE (Nat.le_succ n)) x =
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (quotientPowerSucc R I n) ≫ x := by
  dsimp only [extPowers]
  rw [Functor.ofSequence_map_homOfLE_succ]
  rfl

/-- Each transition map of the `Ext` system is injective in the depth degree. -/
private theorem extPowers_succ_injective_of_depth
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hIM : I • (⊤ : Submodule R M) ≠ ⊤)
    (d : ℕ) (hd : (d : ℕ∞) = Module.depth R I M)
    (n : ℕ) (_hn : 1 ≤ n) :
    Function.Injective
      ((extPowers R I
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) (d : ℤ)).map
          (homOfLE (Nat.le_succ n))) := by
  classical
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M
  let F := extPowers R I K (d : ℤ)
  let Qₙ := ModuleCat.of R (R ⧸ I ^ n)
  let Qnext := ModuleCat.of R (R ⧸ I ^ (n + 1))
  let g := quotientPowerSucc R I n
  let S := g.hom.shortComplexKer
  have hsurj : Function.Surjective g.hom := fun y => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk (I ^ (n + 1)) r, quotientPowerSucc_hom_mk R I n r⟩
  have : Epi g := (ModuleCat.epi_iff_surjective g).mpr hsurj
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hsurj
  have hker : I ≤ Module.annihilator R (S.X₁ : Type u) := by
    intro a ha
    rw [Module.mem_annihilator]
    intro x
    obtain ⟨r, hrrep⟩ := Ideal.Quotient.mk_surjective (x.1 : R ⧸ I ^ (n + 1))
    have hrq : (Ideal.Quotient.mk (I ^ n) r : R ⧸ I ^ n) = 0 := by
      have hx := x.2
      rw [← hrrep] at hx
      rw [← quotientPowerSucc_hom_mk R I n r]
      simpa [S, g] using hx
    apply Subtype.ext
    change a • (x.1 : R ⧸ I ^ (n + 1)) = 0
    rw [← hrrep]
    change (Ideal.Quotient.mk (I ^ (n + 1)) a) *
      (Ideal.Quotient.mk (I ^ (n + 1)) r) = 0
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_succ]
    simpa [mul_comm] using Ideal.mul_mem_mul (Ideal.Quotient.eq_zero_iff_mem.mp hrq) ha
  have hinj : Function.Injective (fun z : Abelian.Ext Qₙ M d =>
      (Abelian.Ext.mk₀ g).comp z (zero_add d)) := by
    by_cases hd0 : d = 0
    · subst d
      exact Abelian.Ext.precomp_mk₀_injective_of_epi M g
    · have hdepth_lt : ((d - 1 : ℕ) : ℕ∞) < Module.depth R I M := by
        rw [← hd]
        exact_mod_cast (Nat.sub_lt (Nat.pos_of_ne_zero hd0) (by omega))
      have hkerExt : Subsingleton (Abelian.Ext S.X₁ M (d - 1)) :=
        Module.subsingleton_ext_of_lt_depth R I M S.X₁ hIM ⟨1, by simpa using hker⟩
          (d - 1) hdepth_lt
      intro x y hxy
      have hzero : (Abelian.Ext.mk₀ g).comp (x - y) (zero_add d) = 0 := by
        simp [sub_eq_add_neg, hxy]
      obtain ⟨z, hz⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS M
        (x - y) hzero (n₀ := d - 1) (by omega)
      exact sub_eq_zero.mp (by simpa [hkerExt.elim z 0] using hz.symm)
  intro x y hxy
  change ShiftedHom ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Qₙ)
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) (d : ℤ) at x y
  change (F.map (homOfLE (Nat.le_succ n))) x =
    (F.map (homOfLE (Nat.le_succ n))) y at hxy
  let eₙ := Abelian.Ext.homEquiv (X := Qₙ) (Y := M) (n := d)
  let enext := Abelian.Ext.homEquiv (X := Qnext) (Y := M) (n := d)
  have hnat (z : Abelian.Ext Qₙ M d) :
      enext ((Abelian.Ext.mk₀ g).comp z (zero_add d)) =
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map g ≫ eₙ z := by
    simpa [eₙ, enext, Abelian.Ext.hom] using
      (Abelian.Ext.singleFunctor_map_comp_hom (C := ModuleCat.{u} R) g z).symm
  have key (w : ShiftedHom ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Qₙ)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) (d : ℤ)) :
      enext ((Abelian.Ext.mk₀ g).comp (eₙ.symm w) (zero_add d)) =
        (F.map (homOfLE (Nat.le_succ n))) w := by
    rw [hnat, eₙ.apply_symm_apply]
    exact (extPowers_succ_apply R I K (d : ℤ) n w).symm
  have heq := (key x).trans (hxy.trans (key y).symm)
  exact eₙ.symm.injective (hinj (enext.injective heq))

/-- In a sequential colimit of modules that vanishes, every element dies at a finite stage. -/
private lemma exists_stage_map_eq_zero_of_colimit_isZero
    {A : Type u} [CommRing A] (F : ℕ ⥤ ModuleCat.{u + 1} A)
    [HasColimit F] (hF : IsZero (colimit F)) (n : ℕ) (x : F.obj n) :
    ∃ m : ℕ, ∃ hnm : n ≤ m, F.map (homOfLE hnm) x = 0 := by
  let e : ℕ ≌ CategoryTheory.AsSmall.{u + 1, 0, 0} ℕ :=
    CategoryTheory.AsSmall.equiv
  let G : CategoryTheory.AsSmall.{u + 1, 0, 0} ℕ ⥤ ModuleCat.{u + 1} A :=
    e.inverse ⋙ F
  let w : e.functor ⋙ G ≅ F :=
    (Functor.associator e.functor e.inverse F).symm ≪≫
      Functor.isoWhiskerRight e.unitIso.symm F ≪≫ Functor.leftUnitor F
  have hG : IsZero (colimit G) :=
    IsZero.of_iso hF (HasColimit.isoOfEquivalence (F := F) (G := G) e w).symm
  let j : CategoryTheory.AsSmall.{u + 1, 0, 0} ℕ := ⟨n⟩
  let hcol := colimit.isColimit G
  let hmodel := ModuleCat.FilteredColimits.colimitCoconeIsColimit G
  have hι' : (colimit.cocone G).ι.app j = 0 := hG.eq_of_tgt _ _
  have hmodelι : (ModuleCat.FilteredColimits.colimitCocone G).ι.app j = 0 := by
    rw [← hcol.comp_coconePointUniqueUpToIso_hom hmodel j, hι', zero_comp]
  let xG : G.obj j := x
  have hx : ModuleCat.FilteredColimits.M.mk G ⟨j, xG⟩ = 0 :=
    congrArg (fun f : G.obj j ⟶ ModuleCat.FilteredColimits.colimit G => f xG) hmodelι
  have hx' : ModuleCat.FilteredColimits.M.mk G ⟨j, xG⟩ =
      ModuleCat.FilteredColimits.M.mk G ⟨j, (0 : G.obj j)⟩ := by
    rw [hx, ModuleCat.FilteredColimits.colimit_zero_eq]
  obtain ⟨m, f, hmap⟩ :=
    (Functor.ιColimitType_eq_iff_of_isFiltered'
      (F := G ⋙ forget (ModuleCat.{u + 1} A)) xG 0).mp hx'
  let hm : ℕ := e.inverse.obj m
  have hnm : n ≤ hm := leOfHom (e.inverse.map f)
  refine ⟨hm, hnm, ?_⟩
  have hmap₀ : G.map f xG = 0 := by simpa using hmap
  have hmap₁ : F.map (e.inverse.map f) x = 0 := by
    simpa [G, xG] using hmap₀
  rwa [Subsingleton.elim (e.inverse.map f) (homOfLE hnm)] at hmap₁

end Stacks.LocalCohomology.DepthEq

namespace Stacks.LocalCohomology

open Stacks.LocalCohomology.DepthEq

/-- Depth is the first degree with nonzero local cohomology supported on `V(I)`. -/
@[stacks 0AVZ "equality of depth and the first nonzero local-cohomology degree"]
theorem depth_eq_sInf_nontrivial_localCohomologyWithSupportIn
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{max u v} R) [Module.Finite R M]
    (hIM : I • (⊤ : Submodule R M) ≠ ⊤) :
    Module.depth R I M =
      sInf {n : ℕ∞ | ∃ i : ℕ, n = (i : ℕ∞) ∧
      Nontrivial
          (localCohomologyWithSupportIn
            R (PrimeSpectrum.zeroLocus (I : Set R))
              ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)
              (i : ℤ))} := by
  let LCH := fun i : ℕ =>
    localCohomologyWithSupportIn R (PrimeSpectrum.zeroLocus (I : Set R))
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) (i : ℤ)
  let S : Set ℕ∞ := {n | ∃ i : ℕ, n = (i : ℕ∞) ∧ Nontrivial (LCH i)}
  change Module.depth R I M = sInf S
  have hlow : Module.depth R I M ≤ sInf S :=
    depth_le_sInf_nontrivial_localCohomologyWithSupportIn.{u, v} I M hIM
  cases hdepth : Module.depth R I M with
  | top =>
    rw [hdepth] at hlow
    exact le_antisymm hlow le_top
  | coe d =>
    have : Small.{u} (M : Type (max u v)) := Module.Finite.small.{u} R M
    let eM : Shrink.{u} (M : Type (max u v)) ≃ₗ[R] (M : Type (max u v)) :=
      Shrink.linearEquiv R (M : Type (max u v))
    let M₀ : ModuleCat.{u} R := ModuleCat.of R (Shrink.{u} (M : Type (max u v)))
    have : Module.Finite R (Shrink.{u} (M : Type (max u v))) := Module.Finite.equiv eM.symm
    have hIM₀ : I • (⊤ : Submodule R M₀) ≠ ⊤ :=
      mt (smul_top_eq_top_iff_of_linearEquiv R I eM).mp hIM
    have hdepth₀ : Module.depth R I (M₀ : Type u) = (d : ℕ∞) := by
      rw [Module.depth_eq_depth_of_linearEquiv I eM, hdepth]
    let E : Set ℕ∞ := {n | ∃ j : ℕ, n = (j : ℕ∞) ∧
      Nontrivial (Abelian.Ext
        (ModuleCat.of R (Shrink.{u} (R ⧸ I))) M₀ j)}
    have hEdepth : Module.depth R I (M₀ : Type u) = sInf E := by
      simpa [E] using Module.depth_eq_sInf_nontrivial_ext
        (R := R) (I := I) (M := (M₀ : Type u))
    have hEne : E.Nonempty := by
      by_contra hE
      have hEempty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hE
      have htop : Module.depth R I (M₀ : Type u) = ⊤ := by
        rw [hEdepth, hEempty]
        simp
      rw [hdepth₀] at htop
      exact (ENat.natCast_ne_top d) htop
    have : Nonempty E := hEne.to_subtype
    obtain ⟨e, he⟩ := ENat.exists_eq_iInf (fun x : E => (x : ℕ∞))
    have heval : (e : ℕ∞) = sInf E := by
      simpa only [sInf_eq_iInf'] using he
    rcases e.property with ⟨j, hj, hExt⟩
    have hjd : j = d := by
      apply ENat.natCast_inj.mp
      calc
        (j : ℕ∞) = (e : ℕ∞) := hj.symm
        _ = sInf E := heval
        _ = Module.depth R I (M₀ : Type u) := hEdepth.symm
        _ = (d : ℕ∞) := hdepth₀
    subst j
    let Qsmall : ModuleCat.{u} R := ModuleCat.of R (Shrink.{u} (R ⧸ I))
    let Qone : ModuleCat.{u} R := ModuleCat.of R (R ⧸ I)
    let eQ : Qsmall ≅ Qone := (Shrink.linearEquiv R (R ⧸ I)).toModuleIso
    let eSingle := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso eQ
    let K₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M₀
    let eExt := Abelian.Ext.homAddEquiv (X := Qsmall) (Y := M₀) (n := d)
    have : Nontrivial (Abelian.Ext Qsmall M₀ d) := hExt
    obtain ⟨z, hz⟩ := exists_ne (0 : Abelian.Ext Qsmall M₀ d)
    let zStage1 : DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Qone) K₀ (d : ℤ) :=
      eSingle.inv ≫ eExt z
    have hzStage1 : zStage1 ≠ 0 := fun h =>
      hz (eExt.map_eq_zero_iff.mp ((Preadditive.IsIso.comp_left_eq_zero eSingle.inv _).mp h))
    let F : ℕ ⥤ ModuleCat.{u + 1} R := extPowers R I K₀ (d : ℤ)
    let Qpow1 : ModuleCat.{u} R := ModuleCat.of R (R ⧸ I ^ (1 : ℕ))
    let ePow : Qpow1 ≅ Qone := eqToIso (by
      change ModuleCat.of R (R ⧸ I ^ (1 : ℕ)) = ModuleCat.of R (R ⧸ I)
      rw [pow_one])
    let ePowSingle := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso ePow
    let z₁ : F.obj 1 := by
      change DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Qpow1) K₀ (d : ℤ)
      exact ePowSingle.hom ≫ zStage1
    have hz₁ : z₁ ≠ 0 := fun h =>
      hzStage1 ((Preadditive.IsIso.comp_left_eq_zero ePowSingle.hom _).mp h)
    have hsurvive : ∀ (m : ℕ) (hm : 1 ≤ m), F.map (homOfLE hm) z₁ ≠ 0 := by
      intro m hm
      induction m with
      | zero => omega
      | succ m ih =>
          by_cases hm0 : m = 0
          · subst m
            have hId : F.map (homOfLE (Nat.le_refl 1)) z₁ = z₁ := by simp
            simpa only [hId] using hz₁
          · have hmpos : 1 ≤ m := by omega
            have hprev : F.map (homOfLE (show 1 ≤ m from hmpos)) z₁ ≠ 0 := ih hmpos
            have hcomp : homOfLE (show 1 ≤ m + 1 from hm) =
                homOfLE (show 1 ≤ m from hmpos) ≫ homOfLE (Nat.le_succ m) := by
              apply Subsingleton.elim
            intro hkill
            have hkill' : F.map (homOfLE (Nat.le_succ m))
                (F.map (homOfLE (show 1 ≤ m from hmpos)) z₁) = 0 := by
              change F.map (homOfLE (show 1 ≤ m + 1 from hm)) z₁ = 0 at hkill
              rw [hcomp, Functor.map_comp] at hkill
              exact hkill
            have hinj := extPowers_succ_injective_of_depth
              R I M₀ hIM₀ d hdepth₀.symm m hmpos
            have hkill'' : F.map (homOfLE (Nat.le_succ m))
                (F.map (homOfLE (show 1 ≤ m from hmpos)) z₁) =
                  F.map (homOfLE (Nat.le_succ m)) 0 := by simpa using hkill'
            exact hprev (by simpa using hinj hkill'')
    let Ccol : ModuleCat.{u + 1} R := CategoryTheory.Limits.colimit F
    have hcol : Nontrivial Ccol := by
      by_contra hnt
      have : Subsingleton Ccol := not_nontrivial_iff_subsingleton.mp hnt
      have hzero : IsZero Ccol := ModuleCat.isZero_iff_subsingleton.mpr inferInstance
      obtain ⟨m, h1m, hkill⟩ := exists_stage_map_eq_zero_of_colimit_isZero F hzero 1 z₁
      exact hsurvive m h1m hkill
    let L := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (d : ℤ)).obj
      (localCohomology R I K₀)
    let eCol := localCohomologyHomologyIsoColimitExt R I K₀ (d : ℤ)
    have hLift : Nontrivial ((ModuleCat.uliftFunctor.{u + 1} R).obj L) :=
      (nontrivial_iff_of_moduleIso eCol).2 hcol
    have hL : Nontrivial L :=
      (Equiv.nontrivial_congr (Equiv.ulift : ULift.{u + 1} L ≃ L)).mp hLift
    have hLiftV : Nontrivial ((ModuleCat.uliftFunctor.{v} R).obj L) :=
      (Equiv.nontrivial_congr (Equiv.ulift : ULift.{v} L ≃ L)).mpr hL
    let eBridge := localCohomologyUliftIso R I M₀ (d : ℤ)
    have hSmall : Nontrivial
        (localCohomologyWithSupportIn
          R (PrimeSpectrum.zeroLocus (I : Set R))
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj
            ((ModuleCat.uliftFunctor.{v} R).obj M₀)) (d : ℤ)) :=
      (nontrivial_iff_of_moduleIso eBridge).mpr hLiftV
    let eM' := moduleShrinkUliftIso R M
    let eInput := (DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).mapIso eM'
    let RF := derivedSectionsWithSupportIn.{u, v}
      R (PrimeSpectrum.zeroLocus (I : Set R))
    let eTarget := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) (d : ℤ)).mapIso
      (RF.mapIso eInput)
    have hBig : Nontrivial (LCH d) := (nontrivial_iff_of_moduleIso eTarget).mp hSmall
    have hup : sInf S ≤ (d : ℕ∞) := sInf_le ⟨d, rfl, hBig⟩
    exact le_antisymm (by simpa [hdepth] using hlow) (by simpa [hdepth] using hup)

/-- Let `R` be a Noetherian ring, `I ⊆ R` an ideal and `M` a finite
`R`-module with `IM ≠ M`. Then the three integers of the source are equal — `depth_I(M)`, the
least `i` with `Ext^i_R(R/I, M) ≠ 0`, and the least `i` with `H^i_{V(I)}(M) ≠ 0`, each of the
last two read as an infimum in `ℕ∞` — and moreover `Ext^i_R(N, M) = 0` for every `i` below
`depth_I(M)` and every finite `R`-module `N` annihilated by a power of `I`.

The source's `H^i_I(M)`, the cohomology of derived `I`-power torsion, is `H^i_{V(I)}(M)` here:
the two agree because `R` is Noetherian, by
`Stacks.LocalCohomology.isIso_compareSectionsWithSupportLocalCohomology_app`
([Stacks, Tag 0955]). -/
@[stacks 0AVZ "the three-way equality and the moreover clause conjoined, with the local \
cohomology of the third quantity in the RΓ_{V(I)} model",
  sga "2 III 2.3" "special case",
  sga "2 III 2.4" "(2)⇔(4)",
  sga "2 IV 5.3" "Ext^i_A(k, special case",
  sga "2 VII 1.2" "(i) ⇔ (iii)"]
theorem depth_eq_sInf_nontrivial_ext_and_localCohomology_and_subsingleton_ext
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hIM : I • (⊤ : Submodule R M) ≠ ⊤) :
    Module.depth R I M =
        sInf {n : ℕ∞ | ∃ i : ℕ, n = (i : ℕ∞) ∧
          Nontrivial (Abelian.Ext (ModuleCat.of R (Shrink.{u} (R ⧸ I))) M i)} ∧
      Module.depth R I M =
        sInf {n : ℕ∞ | ∃ i : ℕ, n = (i : ℕ∞) ∧
          Nontrivial (localCohomologyWithSupportIn R (PrimeSpectrum.zeroLocus (I : Set R))
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) (i : ℤ))} ∧
      ∀ (N : ModuleCat.{u} R) [Module.Finite R N], (∃ k : ℕ, I ^ k ≤ Module.annihilator R N) →
        ∀ i : ℕ, (i : ℕ∞) < Module.depth R I M → Subsingleton (Abelian.Ext N M i) :=
  ⟨Module.depth_eq_sInf_nontrivial_ext R I (M : Type u),
    depth_eq_sInf_nontrivial_localCohomologyWithSupportIn.{u, u} R I M hIM,
    fun N _ hN i hi ↦ Module.subsingleton_ext_of_lt_depth.{u, u} R I M N hIM hN i hi⟩

end Stacks.LocalCohomology


end
