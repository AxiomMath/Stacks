module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotientFraction

/-!
# Vanishing of meromorphic sections on a basic open

On a quasi-compact open of a scheme, a meromorphic function that vanishes on the basic open
defined by a regular function there is annihilated by a power of that function.

## Main results

* `AlgebraicGeometry.toTotalQuotientSheaf_app_injective`: the canonical map from the structure
  sheaf to the sheaf of total quotient rings is injective on sections.
* `AlgebraicGeometry.pow_mul_eq_zero_of_res_basicOpen_eq_zero`: a uniform annihilating power
  exists over a quasi-compact open.
* `AlgebraicGeometry.pow_mul_eq_zero_of_restrict_basicOpen_eq_zero`: the same over the whole
  of a quasi-compact scheme.

## References

* [Stacks Project, Tag 08I7](https://stacks.math.columbia.edu/tag/08I7)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The canonical map from the structure sheaf to the sheaf of total quotient rings is
injective on sections over every open. -/
theorem toTotalQuotientSheaf_app_injective (X : Scheme.{u}) (U : X.Opens) :
    Function.Injective ((X.toTotalQuotientSheaf.hom.app (op U)).hom) :=
  Stacks.SheafifyMono.injective_toTotalQuotientSheaf_app X.sheaf U

private lemma exists_pow_mul_eq_zero_of_isAffineOpen
    (X : Scheme.{u}) {U : Opens X} (hU : IsAffineOpen U)
    (h : Γ(X, U)) (g : (X.presheaf.totalQuotientPresheaf).obj (op U))
    (hg : (X.totalQuotientSheaf.presheaf.map
      (homOfLE (X.basicOpen_le h)).op).hom
      (((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        X.presheaf.totalQuotientPresheaf).app (op U)).hom g) = 0) :
    ∃ n : ℕ,
      (((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        X.presheaf.totalQuotientPresheaf).app (op U)).hom
        (((X.presheaf.toTotalQuotientPresheaf.app (op U)).hom (h ^ n)))) *
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        X.presheaf.totalQuotientPresheaf).app (op U)).hom g = 0 := by
  let S := (X.presheaf.submonoidPresheafOfStalk
    (fun x => nonZeroDivisors ↑(X.presheaf.stalk x))).obj (op U)
  let Q := X.presheaf.totalQuotientPresheaf
  let : Algebra (↑(X.presheaf.obj (op U))) (↑(Q.obj (op U))) := by
    show Algebra (↑(X.presheaf.obj (op U))) (Localization S)
    infer_instance
  let : IsLocalization S (↑(Q.obj (op U))) := by
    show IsLocalization S (Localization S)
    infer_instance
  obtain ⟨a, s, hrep⟩ := IsLocalization.exists_mk'_eq S g
  let alg := (X.presheaf.toTotalQuotientPresheaf.app (op U)).hom
  let η := CategoryTheory.toSheafify (Opens.grothendieckTopology X) Q
  let α := (η.app (op U)).hom
  let res := (X.totalQuotientSheaf.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom
  have hspec : alg s * g = alg a := by
    rw [← hrep]
    exact IsLocalization.mk'_spec' (Q.obj (op U)) a s
  have hspecη : α (alg s) * α g = α (alg a) :=
    (α.map_mul _ _).symm.trans (congrArg α hspec)
  have hgres : res (α g) = 0 := hg
  have hresa : res (α (alg a)) = 0 :=
    (congrArg res hspecη).symm.trans <| (res.map_mul _ _).trans <| by rw [hgres, mul_zero]
  have haD : (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom a = 0 :=
    toTotalQuotientSheaf_app_injective X (X.basicOpen h) <|
      (NatTrans.naturality_apply X.toTotalQuotientSheaf.hom (homOfLE (X.basicOpen_le h)).op a).trans
        (hresa.trans (map_zero _).symm)
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen
    X hU a h haD
  have hKill : α (alg (h ^ n)) * α (alg a) = 0 := by simp only [← map_mul, hn, map_zero]
  have hden : α (alg s) * (α (alg (h ^ n)) * α g) = α (alg s) * 0 := by
    rw [mul_left_comm, hspecη, hKill, mul_zero]
  exact ⟨n, (α.isUnit_map (IsLocalization.map_units (Q.obj (op U)) s)).mul_left_cancel hden⟩

private lemma presheaf_res_res
    {Y : TopCat.{u}} (F : TopCat.Presheaf CommRingCat Y)
    {A B C : Opens Y} (hBA : B ≤ A) (hCB : C ≤ B)
    (hCA : C ≤ A) (x : F.obj (op A)) :
    F.map (homOfLE hCB).op (F.map (homOfLE hBA).op x) =
      F.map (homOfLE hCA).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

private lemma exists_affine_local_annihilator
    (X : Scheme.{u}) {W : X.Opens} (h : Γ(X, W))
    (f : X.totalQuotientSheaf.presheaf.obj (op W))
    (hf : X.totalQuotientSheaf.presheaf.map
      (homOfLE (X.basicOpen_le h)).op f = 0)
    (x : W) :
    ∃ (U : X.Opens) (hUW : U ≤ W), (x : X) ∈ U ∧ ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      (X.toTotalQuotientSheaf.hom.app (op U)).hom
            (X.presheaf.map (homOfLE hUW).op h) ^ m *
          (X.totalQuotientSheaf.presheaf.map (homOfLE hUW).op).hom f = 0 := by
  let Q := X.presheaf.totalQuotientPresheaf
  let S := X.totalQuotientSheaf
  let η := CategoryTheory.toSheafify (Opens.grothendieckTopology X) Q
  have hloc : TopCat.Presheaf.IsLocallySurjective η := by
    show CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) η
    infer_instance
  obtain ⟨V, hVW, ⟨g, hg⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff η).mp hloc W f x x.2
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.2
  have hWU : U ≤ V := SetLike.coe_subset_coe.mp hUV
  have hUW : U ≤ W := hWU.trans hVW
  let gU := Q.map (homOfLE hWU).op g
  have hg' : (η.app (op V)).hom g = S.presheaf.map (homOfLE hVW).op f := hg
  have hliftU : (η.app (op U)).hom gU = S.presheaf.map (homOfLE hUW).op f := by
    have hnat : (η.app (op U)).hom gU =
        S.presheaf.map (homOfLE hWU).op ((η.app (op V)).hom g) :=
      NatTrans.naturality_apply η (homOfLE hWU).op g
    rw [hnat, hg', presheaf_res_res S.presheaf hVW hWU hUW f]
  let hU' := X.presheaf.map (homOfLE hUW).op h
  let D := X.basicOpen hU'
  let leDU : D ≤ U := X.basicOpen_le hU'
  let leDW : D ≤ W := leDU.trans hUW
  have leDh : D ≤ X.basicOpen h := (X.basicOpen_res h (homOfLE hUW).op).le.trans inf_le_right
  have hgD : S.presheaf.map (homOfLE leDU).op ((η.app (op U)).hom gU) = 0 := by
    rw [hliftU, presheaf_res_res S.presheaf hUW leDU leDW f,
      ← presheaf_res_res S.presheaf (X.basicOpen_le h) leDh leDW f, hf, map_zero]
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_isAffineOpen X hU hU' gU hgD
  refine ⟨U, hUW, hxU, n, fun m hm => ?_⟩
  have hψ : (X.toTotalQuotientSheaf.hom.app (op U)).hom hU' ^ n =
      (η.app (op U)).hom
        ((X.presheaf.toTotalQuotientPresheaf.app (op U)).hom (hU' ^ n)) := by
    simp only [map_pow]
    rfl
  rw [← Nat.sub_add_cancel hm, pow_add, mul_assoc, hψ, ← hliftU]
  exact mul_eq_zero_of_right _ hn

/-- A meromorphic function on a quasi-compact open which vanishes on the basic open of a
regular function there is annihilated by a power of that regular function. -/
@[stacks 08I7]
lemma pow_mul_eq_zero_of_res_basicOpen_eq_zero
    (X : Scheme.{u}) {W : X.Opens} (hW : IsCompact (W : Set X)) (h : Γ(X, W))
    (f : X.totalQuotientSheaf.presheaf.obj (op W))
    (hf : X.totalQuotientSheaf.presheaf.map
      (homOfLE (X.basicOpen_le h)).op f = 0) :
    ∃ n : ℕ,
      (X.toTotalQuotientSheaf.hom.app (op W)).hom h ^ n * f = 0 := by
  classical
  choose U hUW hx n hn using exists_affine_local_annihilator X h f hf
  obtain ⟨s, hs⟩ := hW.elim_finite_subcover (fun x : W => (U x : Set X))
    (fun x => (U x).isOpen)
    (fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hx ⟨z, hz⟩⟩)
  refine ⟨s.sup n, ?_⟩
  refine X.totalQuotientSheaf.eq_of_locally_eq' (fun i : s => U i) W
    (fun i => homOfLE (hUW i)) ?_ _ _ ?_
  · intro z hz
    obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.mp (hs hz)
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hzy⟩
  · intro i
    rw [map_zero, map_mul, map_pow, ← NatTrans.naturality_apply
      X.toTotalQuotientSheaf.hom (homOfLE (hUW i)).op h]
    exact hn i (s.sup n) (Finset.le_sup i.property)

/-- A meromorphic function vanishing on the basic open of a global regular function is
annihilated by a power of that regular function. -/
@[stacks 08I7]
lemma pow_mul_eq_zero_of_restrict_basicOpen_eq_zero
    (X : Scheme.{u}) [CompactSpace X] (h : Γ(X, ⊤))
    (f : X.totalQuotientSheaf.presheaf.obj (op ⊤))
    (hf : X.totalQuotientSheaf.presheaf.map
      (homOfLE (X.basicOpen_le h)).op f = 0) :
    ∃ n : ℕ,
      (X.toTotalQuotientSheaf.hom.app (op ⊤)).hom h ^ n * f = 0 :=
  pow_mul_eq_zero_of_res_basicOpen_eq_zero X
    (by simpa only [Opens.coe_top] using isCompact_univ) h f hf

end AlgebraicGeometry
