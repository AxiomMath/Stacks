module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectSupportedExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectTensorBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportTriangles
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.PerfectToPseudoCoherentGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DistinguishedTrianglesGeneral
public import StacksFrontier.CategoryTheory.Preadditive.AdditiveFunctorBiprod
public import StacksFrontier.Homology.DerivedCategory.Bridge.Basic
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
import StacksCore.Tactic.StacksAttribute

/-!
# The cohomology sheaves of the extension of a perfect object with support

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`, `W ⊆ X` a
quasi-compact open subspace, `T ⊆ |X|` a closed subset whose open complement has quasi-compact
inclusion, `E` an object of `D_QCoh(𝒪_X)` and `α : P ⟶ E|_W` a morphism from a perfect object
`P` of `D(𝒪_W)` supported on `T ∩ |W|`. Stacks 09IV extends `α` to a morphism `β : R ⟶ E` from
a perfect object `R` of `D(𝒪_X)` supported on `T`. Stacks 09IW records what the proof gives:

1. `R|_W ≅ P ⊕ P^{⊕ n₁}[1] ⊕ ⋯ ⊕ P^{⊕ nₘ}[m]` for some `m ≥ 0` and `n_j ≥ 0`;
2. hence the highest degree cohomology sheaf of `R|_W` is that of `P`;
3. repeating the construction for the map `P^{⊕ n₁}[1] ⊕ ⋯ ⊕ P^{⊕ nₘ}[m] ⟶ R|_W`, taking cones
   and using induction, the cohomology sheaves of `R|_W` and `P` agree above any given degree.

## Main results

* `AlgebraicGeometry.Space.exists_isPerfect_restrict_iso_biprod_isIso_homologyFunctor_map_inl`:
  **Stacks 09IW, (1) and (2).** There are `R`, `β` as in Stacks 09IV and an isomorphism
  `R|_W ≅ P ⊞ C` with `C` a finite sum of positive shifts of `P`
  (`CategoryTheory.IsFiniteSumOfPositiveShifts`), under which `β|_W` is `α` on `P` and zero on
  `C`; and whenever `Hⁱ(P) = 0` for `i > d`, the inclusion of the summand `P` induces
  `Hⁱ(P) ≅ Hⁱ(R|_W)` for every `i ≥ d`.
* `AlgebraicGeometry.Space.exists_isPerfect_retract_restrict_isIso_homologyFunctor_map`:
  **Stacks 09IW, (3).** For every integer `N` there are `R`, `β` as in Stacks 09IV, with
  `s : P ⟶ R|_W` and `r : R|_W ⟶ P` such that `s ≫ r = 𝟙 P`, `s ≫ β|_W = α` (indeed
  `β|_W = r ≫ α`), and `Hⁱ(s) : Hⁱ(P) ⟶ Hⁱ(R|_W)` is an isomorphism for every `i ≥ N`.

Along the way:

* `CategoryTheory.Pretriangulated.isIso_biprod_desc_of_distTriang_of_eq_comp_inr`: the cone of
  `C ⊕ C' ⟶ P ⊕ C`, the identity of `C` on the first summand and zero on the second, is
  `P ⊕ C'[1]`, with prescribed inclusions; this is the computation of "taking cones".
* `AlgebraicGeometry.Space.exists_isZero_homology_of_lt_of_isPerfect`: a perfect object on a
  quasi-compact algebraic space is bounded above.
* `AlgebraicGeometry.Space.derivedCategoryB_isQuasicoherentOnSite_of_isPerfect`: a perfect object
  has quasi-coherent cohomology sheaves.
* `Space.exists_isPerfect_restrict_iso_biprod_isFiniteSumOfPositiveShifts_of_models`: the
  construction of Stacks 09IV
  (`AlgebraicGeometry.Space.exists_isPerfect_restrict_iso_biprod_isFiniteSumOfPositiveShifts`) at
  arbitrary models of the two derived categories.

## Implementation notes

**Reading of (2).** "The highest degree cohomology sheaf of `R|_W` equals that of `P`" is read
as: for every `d` with `Hⁱ(P) = 0` for all `i > d` (in particular for the top nonzero degree of
`P`), the map `Hⁱ(P) ⟶ Hⁱ(R|_W)` induced by the inclusion of the summand `P` is an isomorphism
for all `i ≥ d`. The cohomology of `P⟦k⟧`, `k ≥ 1`, in degree `i` is that of `P` in degree
`i + k > d`, so the complementary summand has no cohomology from degree `d` on.

**Reading of (3)** is the statement of Stacks 09IV, with `P` a direct summand of `R|_W`
compatibly with `α` and `β|_W` as there (`s ≫ r = 𝟙 P` and `s ≫ β|_W = α`), plus the equality
of the cohomology sheaves `Hⁱ(P) ≅ Hⁱ(R|_W)` for `i ≥ N`, through `s`.

**The induction of (3).** It carries `R`, `β` and `R|_W ≅ P ⊞ C` with `C` perfect, supported on
`T ∩ |W|`, `Hⁱ(C) = 0` for `i ≥ n`, and `β|_W` equal to `α` on `P` and to zero on `C`. Write
`F ⟶ R ⟶ E` for the fibre of `β`; it lies in `D_QCoh(𝒪_X)`, since `R` and `E` do. The inclusion
`C ⟶ R|_W` is killed by `β|_W`, so it lifts to `C ⟶ F|_W`, and the construction of Stacks 09IV
for this map gives `β' : R' ⟶ F` with `R'|_W ≅ C ⊞ C'`, `C'` a finite sum of positive shifts of
`C`, and `β'|_W` the lift on `C` and zero on `C'`. The cone `R₁` of `R' ⟶ F ⟶ R` restricts to
`P ⊕ C'[1]`, whose second summand has no cohomology from degree `n - 1` on. The morphism
`β₁ : R₁ ⟶ E` extending `β` is the one of the octahedral axiom for `R' ⟶ F ⟶ R`, whose fibre is
the cone `G` of `β'`; this is what makes `β₁|_W` vanish on `C'[1]`, the inclusion of `C'[1]` being
chosen through `G|_W`. Taking the fibre of `β` rather than `R` itself as the target of the
repeated construction is what keeps a map to `E`: the composite `R' ⟶ R ⟶ E` then vanishes.
The induction starts from the bound above of the perfect object `P` on the quasi-compact `W`.

**Models.** All statements are at arbitrary models `[HasDerivedCategory]` of `D(𝒪_X)` and
`D(𝒪_W)`. "`E` lies in `D_QCoh(𝒪_X)`" is the object property
`DerivedCategoryB.derivedCategoryB` of the quasi-coherence predicate, whose full subcategory is
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory` (Stacks 071X), and "supported on `T`" is
the defining condition of Stacks 08GF, `AlgebraicGeometry.Space.CohomologySupportedOn`, on every
cohomology sheaf; both are read at the given model. Stacks 09IV is stated at the standard models;
it is carried to the given ones along `StacksDraft.DerivedModel.modelEquiv`.

## References

* [Stacks Project, Tag 09IW](https://stacks.math.columbia.edu/tag/09IW)
* [Stacks Project, Tag 09IV](https://stacks.math.columbia.edu/tag/09IV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated StacksDraft.DerivedModel

universe w w' u

/-! ### Finite sums of positive shifts -/

namespace CategoryTheory

namespace IsFiniteSumOfPositiveShifts

section Shifts

variable {D : Type*} [Category D] [Preadditive D] [HasBinaryBiproducts D] [HasShift D ℤ]

/-- A property of objects closed under isomorphisms and binary biproducts, held by the zero
objects and by the positive shifts of `P`, holds for every finite sum of positive shifts of `P`. -/
theorem prop {P : D} (Q : D → Prop) (hiso : ∀ {A Z : D}, (A ≅ Z) → Q A → Q Z)
    (hzero : ∀ {Z : D}, IsZero Z → Q Z) (hbiprod : ∀ {A B : D}, Q A → Q B → Q (A ⊞ B))
    (hshift : ∀ k : ℕ, Q (P⟦(k : ℤ) + 1⟧)) {C : D} (hC : IsFiniteSumOfPositiveShifts P C) :
    Q C := by
  induction hC with
  | zero hZ => exact hzero hZ
  | add k _ e ih => exact hiso e.some.symm (hbiprod ih (hshift k))

/-- A finite sum of positive shifts of `P` is one of any object isomorphic to `P`. -/
theorem of_iso_left {P P' C : D} (h : IsFiniteSumOfPositiveShifts P C) (e : P ≅ P') :
    IsFiniteSumOfPositiveShifts P' C := by
  induction h with
  | zero hZ => exact zero hZ
  | add k _ e' ih =>
    exact add k ih ⟨e'.some ≪≫ biprod.mapIso (Iso.refl _) ((shiftFunctor D _).mapIso e)⟩

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts in
/-- An additive functor commuting with the shift carries finite sums of positive shifts of `P`
to finite sums of positive shifts of the image of `P`. -/
theorem map {D' : Type*} [Category D'] [Preadditive D'] [HasBinaryBiproducts D']
    [HasShift D' ℤ] (G : D ⥤ D') [G.Additive] [G.CommShift ℤ] {P C : D}
    (h : IsFiniteSumOfPositiveShifts P C) :
    IsFiniteSumOfPositiveShifts (G.obj P) (G.obj C) := by
  induction h with
  | zero hZ => exact zero (G.map_isZero hZ)
  | add k _ e ih =>
    exact add k ih ⟨G.mapIso e.some ≪≫ G.mapBiprod _ _ ≪≫
      biprod.mapIso (Iso.refl _) ((G.commShiftIso ((k : ℤ) + 1)).app P)⟩

end Shifts

section Homology

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]

/-- An object of a derived category with no cohomology from degree `n` on: `Hⁱ(P) = 0` for
`i ≥ n`. Then a finite sum `C` of positive shifts of `P` has no cohomology from degree `n - 1`
on, since `Hⁱ(P⟦k⟧) = H^{k + i}(P)`. -/
theorem isZero_homologyFunctor_obj {P C : DerivedCategory A}
    (h : IsFiniteSumOfPositiveShifts P C) (n : ℤ)
    (hP : ∀ i : ℤ, n ≤ i → IsZero ((DerivedCategory.homologyFunctor A i).obj P)) :
    ∀ i : ℤ, n - 1 ≤ i → IsZero ((DerivedCategory.homologyFunctor A i).obj C) := by
  refine h.prop (fun X => ∀ i : ℤ, n - 1 ≤ i →
      IsZero ((DerivedCategory.homologyFunctor A i).obj X)) ?_ ?_ ?_ ?_
  · intro A' Z e hA i hi
    exact (hA i hi).of_iso ((DerivedCategory.homologyFunctor A i).mapIso e.symm)
  · intro Z hZ i _
    exact (DerivedCategory.homologyFunctor A i).map_isZero hZ
  · intro A' B' hA hB i hi
    let H := DerivedCategory.homologyFunctor A i
    refine (IsZero.iff_id_eq_zero _).2 ?_
    rw [← H.map_id, ← biprod.total, H.map_add, H.map_comp, H.map_comp,
      (hA i hi).eq_of_tgt (H.map biprod.fst) 0, (hB i hi).eq_of_tgt (H.map biprod.snd) 0]
    simp
  · intro k i hi
    exact (hP ((k : ℤ) + 1 + i) (by omega)).of_iso
      (((DerivedCategory.homologyFunctor A 0).shiftIso ((k : ℤ) + 1) i ((k : ℤ) + 1 + i)
        rfl).app P)

end Homology

end IsFiniteSumOfPositiveShifts

/-- A self-map of a binary biproduct fixing the inclusion of the first summand and inducing the
identity on the second summand is an isomorphism: it is unipotent upper triangular. -/
theorem isIso_of_biprod_inl_comp_eq_of_inr_comp_snd_eq_id {D : Type*} [Category D]
    [Preadditive D] {X Y : D} [HasBinaryBiproduct X Y] (f : X ⊞ Y ⟶ X ⊞ Y)
    (h₁ : biprod.inl ≫ f = biprod.inl) (h₂ : biprod.inr ≫ f ≫ biprod.snd = 𝟙 Y) : IsIso f := by
  obtain ⟨z, hz⟩ : ∃ z : Y ⟶ X, z = biprod.inr ≫ f ≫ biprod.fst := ⟨_, rfl⟩
  have hr : biprod.inr ≫ f = z ≫ biprod.inl + biprod.inr := by
    apply biprod.hom_ext
    · simp [hz]
    · simp [h₂]
  refine ⟨biprod.desc biprod.inl (biprod.inr - z ≫ biprod.inl), ?_, ?_⟩
  · apply biprod.hom_ext'
    · rw [reassoc_of% h₁]
      simp
    · rw [reassoc_of% hr]
      simp
  · apply biprod.hom_ext'
    · simp [h₁]
    · simp [Preadditive.sub_comp, hr, h₁]

namespace Pretriangulated

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A distinguished triangle `A ⟶ Z ⟶ B ⟶ A⟦1⟧` whose third morphism is zero splits, along any
section `σ` of `Z ⟶ B`: `[mor₁, σ] : A ⊞ B ⟶ Z` is an isomorphism. -/
theorem isIso_biprod_desc_of_mor₃_eq_zero (T : Triangle D) (hT : T ∈ distTriang D)
    (h₀ : T.mor₃ = 0) (σ : T.obj₃ ⟶ T.obj₂) (hσ : σ ≫ T.mor₂ = 𝟙 _) :
    IsIso (biprod.desc T.mor₁ σ) := by
  obtain ⟨e, he₁, he₂⟩ := exists_iso_binaryBiproduct_of_distTriang T hT h₀
  have : IsIso (biprod.desc T.mor₁ σ ≫ e.hom) :=
    isIso_of_biprod_inl_comp_eq_of_inr_comp_snd_eq_id _ (by simp [he₁])
      (by simp [← he₂, hσ])
  exact IsIso.of_isIso_comp_right _ e.hom

/-- **The cone of a map that is the identity on a common summand.** Let `Y ≅ P ⊞ C` and
`Y' ≅ C ⊞ C'`, and let `g : Y' ⟶ Y` be the projection onto `C` followed by the inclusion of `C`.
In a distinguished triangle `Y' ⟶ Y ⟶ Z ⟶ Y'⟦1⟧` on `g`, the object `Z` is `P ⊞ C'⟦1⟧`: the
inclusion of `P` through `Y ⟶ Z`, together with any `j : C'⟦1⟧ ⟶ Z` lifting the inclusion of
`C'⟦1⟧` into `Y'⟦1⟧`, is an isomorphism `P ⊞ C'⟦1⟧ ≅ Z`. -/
theorem isIso_biprod_desc_of_distTriang_of_eq_comp_inr [IsTriangulated D]
    {P C C' Y Y' Z : D} (e : Y ≅ P ⊞ C) (e' : Y' ≅ C ⊞ C') (g : Y' ⟶ Y) (v : Y ⟶ Z)
    (w : Z ⟶ Y'⟦(1 : ℤ)⟧) (hT : Triangle.mk g v w ∈ distTriang D)
    (hg : g = e'.hom ≫ biprod.fst ≫ biprod.inr ≫ e.inv) (j : C'⟦(1 : ℤ)⟧ ⟶ Z)
    (hj : j ≫ w = (biprod.inr ≫ e'.inv)⟦(1 : ℤ)⟧') :
    IsIso (biprod.desc (biprod.inl ≫ e.inv ≫ v) j) := by
  have hbr : ∀ X Y : D, (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.braiding X Y).hom = biprod.inl :=
    fun X Y => by apply biprod.hom_ext <;> simp [biprod.braiding]
  let ι : C'⟦(1 : ℤ)⟧ ≅ C'⟦(1 : ℤ)⟧ :=
    { hom := -𝟙 _, inv := -𝟙 _, hom_inv_id := by simp, inv_hom_id := by simp }
  -- the triangle on the projection `Y' ⟶ C`
  have h₁₂ : Triangle.mk (e'.hom ≫ biprod.fst) (0 : C ⟶ C'⟦(1 : ℤ)⟧)
      ((biprod.inr ≫ e'.inv)⟦(1 : ℤ)⟧') ∈ distTriang D := by
    refine isomorphic_distinguished _
      (rot_of_distTriang _ (binaryBiproductTriangle_distinguished C' C)) _ ?_
    refine Triangle.isoMk _ _ (e' ≪≫ biprod.braiding C C') (Iso.refl _) ι ?_ ?_ ?_
    · show (e'.hom ≫ biprod.fst) ≫ 𝟙 C = (e'.hom ≫ (biprod.braiding C C').hom) ≫ biprod.snd
      simp
    · dsimp
      rw [zero_comp]
      exact comp_zero.symm
    · show (biprod.inr ≫ e'.inv)⟦(1 : ℤ)⟧' ≫ (e'.hom ≫ (biprod.braiding C C').hom)⟦(1 : ℤ)⟧' =
        (-𝟙 _) ≫ (-((biprod.inl : C' ⟶ C' ⊞ C)⟦(1 : ℤ)⟧'))
      rw [← Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, hbr, Preadditive.neg_comp,
        Category.id_comp, neg_neg]
  -- the triangle on the inclusion `C ⟶ Y`
  have h₂₃ : Triangle.mk (biprod.inr ≫ e.inv) (e.hom ≫ biprod.fst)
      (0 : P ⟶ C⟦(1 : ℤ)⟧) ∈ distTriang D := by
    refine isomorphic_distinguished _ (binaryBiproductTriangle_distinguished C P) _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) (e ≪≫ biprod.braiding P C) (Iso.refl _) ?_ ?_ ?_
    · show (biprod.inr ≫ e.inv) ≫ (e.hom ≫ (biprod.braiding P C).hom) = 𝟙 C ≫ biprod.inl
      simp only [Category.assoc, Iso.inv_hom_id_assoc, hbr, Category.id_comp]
    · show (e.hom ≫ biprod.fst) ≫ 𝟙 P = (e.hom ≫ (biprod.braiding P C).hom) ≫ biprod.snd
      simp
    · dsimp
      rw [zero_comp]
      exact comp_zero.symm
  have comm : (e'.hom ≫ biprod.fst) ≫ (biprod.inr ≫ e.inv) = g := by simp [hg]
  let oct := Triangulated.someOctahedron comm h₁₂ h₂₃ hT
  have hsm : (biprod.inl ≫ e.inv ≫ v) ≫ oct.m₃ = 𝟙 P := by
    rw [Category.assoc, Category.assoc, oct.comm₃]
    simp
  have hsplit : IsIso (biprod.desc oct.m₁ (biprod.inl ≫ e.inv ≫ v)) :=
    isIso_biprod_desc_of_mor₃_eq_zero _ oct.mem (by simp) _ hsm
  have hbv : biprod.inr ≫ e.inv ≫ v = 0 := by simpa using oct.comm₁.symm
  have hv' : e.inv ≫ v = biprod.fst ≫ biprod.inl ≫ e.inv ≫ v := by
    apply biprod.hom_ext'
    · simp
    · simp [hbv]
  have hv : v = (e.hom ≫ biprod.fst) ≫ (biprod.inl ≫ e.inv ≫ v) := by
    calc v = e.hom ≫ (e.inv ≫ v) := by simp
      _ = _ := by rw [hv']; simp
  obtain ⟨d, hd⟩ := Triangle.coyoneda_exact₃ _ hT (j - oct.m₁) (by
    dsimp
    rw [Preadditive.sub_comp, hj, oct.comm₂, sub_self])
  have hj' : j = oct.m₁ + (d ≫ e.hom ≫ biprod.fst) ≫ (biprod.inl ≫ e.inv ≫ v) := by
    have h1 : j - oct.m₁ = d ≫ v := hd
    have h2 : d ≫ v = (d ≫ e.hom ≫ biprod.fst) ≫ (biprod.inl ≫ e.inv ≫ v) := by
      conv_lhs => rw [hv]
      simp
    rw [← h2, ← h1]
    abel
  let M : P ⊞ C'⟦(1 : ℤ)⟧ ⟶ C'⟦(1 : ℤ)⟧ ⊞ P :=
    biprod.desc biprod.inr (biprod.inl + (d ≫ e.hom ≫ biprod.fst) ≫ biprod.inr)
  have heq : biprod.desc (biprod.inl ≫ e.inv ≫ v) j =
      M ≫ biprod.desc oct.m₁ (biprod.inl ≫ e.inv ≫ v) := by
    apply biprod.hom_ext'
    · simp [M]
    · rw [hj']
      simp [M]
  have hM : IsIso M := by
    have : IsIso (M ≫ (biprod.braiding _ _).hom) :=
      isIso_of_biprod_inl_comp_eq_of_inr_comp_snd_eq_id _
        (by apply biprod.hom_ext <;> simp [M, biprod.braiding]) (by simp [M, biprod.braiding])
    exact IsIso.of_isIso_comp_right _ (biprod.braiding _ _).hom
  rw [heq]
  infer_instance

end Pretriangulated

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] pointTopology smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

attribute [local instance] RingedSite.ovFunctorLimits RingedSite.ovFunctorColimits

/-! ### Perfect objects: boundedness, quasi-coherence, sums of shifts -/

section Perfect

variable (Y : AlgebraicSpaces B S hS) [HasDerivedCategory.{w} (Modules.{u, u} B S hS Y.1 Y.2)]

/-- **A perfect object on a quasi-compact algebraic space is bounded above.** Perfectness gives a
family covering the final object of the small étale site on whose members the object has a
strictly perfect model; quasi-compactness of `|Y|` refines it to a covering each member of which
maps to one of finitely many of them, and the cohomology sheaves vanish above the largest of the
finitely many bounds of the models. -/
theorem exists_isZero_homology_of_lt_of_isPerfect (hY : IsQuasiCompactSpace B S hS Y.1)
    (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hK : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect K) :
    ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj K) := by
  classical
  let Ys := smallEtaleRingedSite B S hS Y.1 Y.2
  let R := Stacks.SheafOfModules.Tensor.ringSheaf Ys.O
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  obtain ⟨Kι, V, hV, hmod⟩ := Ys.exists_coversTop_isStrictlyPerfect_of_isPerfectComplex E hE
  choose P hP q hq using hmod
  choose Nk hNk using fun k => exists_bound_of_isStrictlyPerfect B S hS Y (V k) (P k) (hP k)
  have : CompactSpace (points B S hS Y.1) :=
    compactSpace_points_of_isQuasiCompactSpace B S hS Y.2 hY
  obtain ⟨F, I, W, hW, hkind⟩ :=
    exists_coversTop_finite_near B S hS Y hV Set.univ isCompact_univ isClosed_univ
  refine ⟨((F.sup Nk : ℕ) : ℤ), fun n hn => ?_⟩
  refine IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (Modules.{u, u} B S hS Y.1 Y.2) n).app E)
  -- vanishing on the members carrying a model
  have hloc : ∀ k ∈ F,
      IsZero ((SheafOfModules.overFunctor.{u} R (V k)).obj (E.homology n)) := by
    intro k hk
    have hle : Nk k ≤ F.sup Nk := Finset.le_sup hk
    have hPz : IsZero ((P k).homology n) :=
      ShortComplex.isZero_homology_of_isZero_X₂ _ (hNk k n (Or.inr (by omega)))
    have := hq k
    exact hPz.of_iso (((StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
        (SheafOfModules.overFunctor.{u} R (V k)) (ComplexShape.up ℤ) n).app E).symm ≪≫
      (asIso (HomologicalComplex.homologyMap (q k) n)).symm)
  refine Stacks.SheafOfModules.isZero_of_coversTop hW _ fun i => ?_
  rcases hkind i with ⟨k, hk, ⟨g⟩⟩ | hout
  · have : (SheafOfModules.overMap.{u} R g).PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
    exact ((SheafOfModules.overMap.{u} R g).map_isZero (hloc k hk)).of_iso
      ((SheafOfModules.overFunctorMap.{u} R g).app (E.homology n)).symm
  · exact isZero_over_of_forall_notMem_supportOfSheaf B S hS Y _ (W i)
      (fun z _ => hout z (Set.mem_univ _))

/-- **A perfect object has quasi-coherent cohomology sheaves**, at any model of `D(𝒪_Y)`: a
perfect object is pseudo-coherent (Stacks 08G8), and pseudo-coherent objects lie in
`D_QCoh(𝒪_Y)` (Stacks 08JL). -/
theorem derivedCategoryB_isQuasicoherentOnSite_of_isPerfect
    (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hK : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect K) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) K := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  have h := derivedCategoryB_of_isPseudoCoherent_unconditional B S hS Y.1 Y.2
    ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj E)
    ⟨E, fun m => RingedSite.isPseudoCoherentComplexFrom_of_isPerfectComplex_general _ hE m,
      ⟨Iso.refl _⟩⟩
  intro n
  exact (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_of_iso
    ((@DerivedCategory.homologyFunctorFactors (Modules.{u, u} B S hS Y.1 Y.2) _ _
      (HasDerivedCategory.standard _) n).app E ≪≫
      ((DerivedCategory.homologyFunctorFactors (Modules.{u, u} B S hS Y.1 Y.2) n).app E).symm ≪≫
      (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).mapIso e) (h n)

variable {Y}

/-- A finite sum of positive shifts of a perfect object is perfect. -/
theorem isPerfect_of_isFiniteSumOfPositiveShifts
    {P C : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)}
    (hC : IsFiniteSumOfPositiveShifts P C)
    (hP : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect P) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect C := by
  have hiso : ∀ {K L : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)}, (K ≅ L) →
      (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect K →
      (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect L := by
    rintro K L e ⟨E, hE, ⟨f⟩⟩
    exact ⟨E, hE, ⟨f ≪≫ e⟩⟩
  refine hC.prop _ hiso (fun {Z} hZ => ?_) (fun hA hB => ?_)
    (fun k => RingedSite.isPerfect_shift_general _ hP _)
  · exact hiso ((isZero_zero _).iso hZ)
      (RingedSite.isPerfect_obj₃_of_distinguished_general _ _ (contractible_distinguished P) hP hP)
  · exact RingedSite.isPerfect_obj₂_of_distinguished_general _ _
      (binaryBiproductTriangle_distinguished _ _) hA hB

/-- The support of the cohomology sheaves of a shift. -/
theorem supportOfSheaf_homology_shift (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (k i : ℤ) :
    supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf.{u} _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj (K⟦k⟧))) =
      supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf.{u} _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) (k + i)).obj K)) :=
  supportOfSheaf_eq_of_iso B S hS Y
    (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).shiftIso k i (k + i)
      rfl).app K)

/-- A finite sum of positive shifts of an object supported on `T` is supported on `T`. -/
theorem supportOfSheaf_homology_subset_of_isFiniteSumOfPositiveShifts
    {P C : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)}
    (hC : IsFiniteSumOfPositiveShifts P C) (T : Set (points B S hS Y.1))
    (hP : ∀ i : ℤ, supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf.{u} _).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj P)) ⊆ T) :
    ∀ i : ℤ, supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf.{u} _).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj C)) ⊆ T := by
  refine hC.prop (fun X => ∀ i : ℤ, supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf.{u} _).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj X)) ⊆ T)
    (fun e h i => ?_) (fun hZ i => ?_) (fun hA hB i => ?_) (fun k i => ?_)
  · exact (le_of_eq (supportOfSheaf_eq_of_iso B S hS Y
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).mapIso
        e.symm))).trans (h i)
  · rw [(supportOfSheaf_eq_empty_iff_isZero B S hS Y _).2
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).map_isZero hZ)]
    exact Set.empty_subset _
  · exact (subset_union_homology_obj₂_of_distinguished
      (fun M : Modules.{u, u} B S hS Y.1 Y.2 =>
        supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf.{u} _).obj M))
      (supportOfSheaf_toSheaf_subset_union_of_exact B S hS Y.1 Y.2) _
      (binaryBiproductTriangle_distinguished _ _) i).trans (Set.union_subset (hA i) (hB i))
  · rw [supportOfSheaf_homology_shift]
    exact hP _

end Perfect

/-! ### The construction of Stacks 09IV at arbitrary models -/

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts in
/-- **The construction of Stacks 09IV, with its shape, at arbitrary models.** This is
`AlgebraicGeometry.Space.exists_isPerfect_restrict_iso_biprod_isFiniteSumOfPositiveShifts` with
`D(𝒪_X)` and `D(𝒪_W)` at any models: `E` has quasi-coherent cohomology sheaves, `P` is perfect
and supported on `T ∩ |W|`, and there are a perfect `R` supported on `T`, `β : R ⟶ E` and
`R|_W ≅ P ⊞ C` with `C` a finite sum of positive shifts of `P`, under which `β|_W` is `α` on `P`
and zero on `C`. -/
theorem exists_isPerfect_restrict_iso_biprod_isFiniteSumOfPositiveShifts_of_models
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (W : Subfunctor X.1) (hW : IsOpenSubspace B S hS W)
    (hWqc : IsQuasiCompactSpace B S hS W.toFunctor) (T : Set (points B S hS X.1))
    (hT : IsClosed T)
    (hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι)
    [hDX : HasDerivedCategory.{w} (Modules.{u, u} B S hS X.1 X.2)]
    [hDW : HasDerivedCategory.{w'} (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2)]
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) E)
    (P : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2))
    (hP : (smallEtaleRingedSite B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2).IsPerfect P)
    (hPT : ∀ i : ℤ, supportOfSheaf B S hS (openSubspaceSpace B S hS W hW).1
      ((SheafOfModules.toSheaf.{u} _).obj ((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
          (openSubspaceSpace B S hS W hW).2) i).obj P)) ⊆
        pointsMap B S hS W.toFunctor W.ι ⁻¹' T)
    (α : P ⟶ (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj E) :
    ∃ (R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (β : R ⟶ E),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect R ∧
      (∀ i : ℤ, supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf.{u} _).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj R)) ⊆ T) ∧
      ∃ (C : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
          (openSubspaceSpace B S hS W hW).2))
        (e : (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj R ≅ P ⊞ C),
        IsFiniteSumOfPositiveShifts P C ∧
        (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map β =
          e.hom ≫ biprod.fst ≫ α := by
  set F := etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
    (isEtale_openSubspaceHom B S hS W hW) with hF
  -- the comparisons with the standard models; these are not instances, and the standard models
  -- are written out wherever they occur, so that instance search only sees the given ones
  let ΨX := modelEquiv (HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)) hDX
  let ΨW := modelEquiv (HasDerivedCategory.standard (Modules.{u, u} B S hS
    (openSubspaceSpace B S hS W hW).1 (openSubspaceSpace B S hS W hW).2)) hDW
  have : ΨW.functor.Additive := modelEquiv_functor_additive _ hDW
  -- restriction commutes with the comparisons
  let τ : ΨX.functor ⋙ F.mapDerivedCategory ≅
      @Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _
        (HasDerivedCategory.standard _) F _ _ _ ⋙ ΨW.functor :=
    modelEquivCompMapDerivedCategoryIso F (HasDerivedCategory.standard _) hDX hDW ≪≫
      (mapDerivedCategoryCompModelEquivIso F (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) hDW).symm
  -- the data at the standard models
  have hE₀ : @DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
      (ΨX.inverse.obj E) := by
    refine (derivedCategoryB_modelEquiv_functor_obj_iff _ (HasDerivedCategory.standard _) hDX
      _).1 fun n => ?_
    exact (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_of_iso
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) n).mapIso
        (ΨX.counitIso.app E).symm) (hE n)
  obtain ⟨Pc, hPc, ⟨eP⟩⟩ := hP
  have hPT₀ : CohomologySupportedOn B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2 (pointsMap B S hS W.toFunctor W.ι ⁻¹' T)
      (ΨW.inverse.obj P) :=
    fun i => (le_of_eq (supportOfSheaf_eq_of_iso B S hS (openSubspaceSpace B S hS W hW)
      (((modelHomologyFunctorIso (HasDerivedCategory.standard _) hDW i).app
          (ΨW.inverse.obj P)).symm ≪≫
        (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
          (openSubspaceSpace B S hS W hW).2) i).mapIso (ΨW.counitIso.app P)))).trans (hPT i)
  let α₀ : ΨW.inverse.obj P ⟶ (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _)
      _ _ _ (HasDerivedCategory.standard _) F _ _ _).obj (ΨX.inverse.obj E) :=
    ΨW.functor.preimage (ΨW.counitIso.hom.app P ≫ α ≫
      F.mapDerivedCategory.map (ΨX.counitIso.inv.app E) ≫ τ.hom.app (ΨX.inverse.obj E))
  obtain ⟨R₀, β₀, hR₀, hR₀T, C₀, e₀, hC₀, hβ₀⟩ :=
    exists_isPerfect_restrict_iso_biprod_isFiniteSumOfPositiveShifts B.contains_terminal X hXqc
      hXqs W hW hWqc T hT hTqc ⟨ΨX.inverse.obj E, hE₀⟩ (ΨW.inverse.obj P)
      ⟨Pc, hPc, ⟨((modelInverseCompQIso (HasDerivedCategory.standard _) hDW).app Pc).symm ≪≫
        ΨW.inverse.mapIso eP⟩⟩ hPT₀ α₀
  have hβ₀' : (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _
      (HasDerivedCategory.standard _) F _ _ _).map β₀ = e₀.hom ≫ biprod.fst ≫ α₀ := hβ₀
  obtain ⟨Rc, hRc, ⟨eR⟩⟩ := hR₀
  refine ⟨ΨX.functor.obj R₀, ΨX.functor.map β₀ ≫ ΨX.counitIso.hom.app E,
    ⟨Rc, hRc, ⟨((modelCompQIso (HasDerivedCategory.standard _) hDX).app Rc).symm ≪≫
      ΨX.functor.mapIso eR⟩⟩,
    fun i => (le_of_eq (supportOfSheaf_eq_of_iso B S hS X
      ((modelHomologyFunctorIso (HasDerivedCategory.standard _) hDX i).app R₀))).trans (hR₀T i),
    ΨW.functor.obj C₀, τ.app R₀ ≪≫ ΨW.functor.mapIso e₀ ≪≫
      ΨW.functor.mapBiprod (ΨW.inverse.obj P) C₀ ≪≫
      biprod.mapIso (ΨW.counitIso.app P) (Iso.refl _),
    (hC₀.map ΨW.functor).of_iso_left (ΨW.counitIso.app P), ?_⟩
  have hα₀ : ΨW.functor.map α₀ = ΨW.counitIso.hom.app P ≫ α ≫
      F.mapDerivedCategory.map (ΨX.counitIso.inv.app E) ≫ τ.hom.app (ΨX.inverse.obj E) :=
    ΨW.functor.map_preimage _
  have key : F.mapDerivedCategory.map (ΨX.functor.map β₀) =
      τ.hom.app R₀ ≫ ΨW.functor.map
        ((@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _
          (HasDerivedCategory.standard _) F _ _ _).map β₀) ≫
        τ.inv.app (ΨX.inverse.obj E) := by
    rw [← cancel_mono (τ.hom.app (ΨX.inverse.obj E)), Category.assoc, Category.assoc,
      Iso.inv_hom_id_app]
    refine (τ.hom.naturality β₀).trans ?_
    congr 1
    exact (Category.comp_id _).symm
  show F.mapDerivedCategory.map (ΨX.functor.map β₀ ≫ ΨX.counitIso.hom.app E) = _
  rw [Functor.map_comp, key, hβ₀', Functor.map_comp, Functor.map_comp, hα₀]
  have hε : F.mapDerivedCategory.map (ΨX.counitIso.inv.app E) ≫
      F.mapDerivedCategory.map (ΨX.counitIso.hom.app E) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app]
    exact F.mapDerivedCategory.map_id _
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.mapBiprod_hom, biprod.mapIso_hom,
    Iso.app_hom, Iso.refl_hom, Category.assoc, Iso.hom_inv_id_app_assoc, hε, Functor.id_obj,
    Category.comp_id, biprod.map_fst_assoc, biprod.lift_fst_assoc]
  exact congrArg (fun t => τ.hom.app R₀ ≫ ΨW.functor.map e₀.hom ≫ ΨW.functor.map biprod.fst ≫
    ΨW.counitIso.hom.app P ≫ t) (Category.comp_id α)
/-! ### The cohomology of the restriction -/

/-- **The inductive step of Stacks 09IW (3).** Let `β : R ⟶ E` with `R` perfect and supported on
`T`, and `R|_W ≅ P ⊞ C` with `C` perfect, supported on `T ∩ |W|` and without cohomology from
degree `n` on, `β|_W` being `α` on `P` and zero on `C`. Then there is another such datum
`β₁ : R₁ ⟶ E`, `R₁|_W ≅ P ⊞ C₁`, whose complementary summand `C₁` has no cohomology from
degree `n - 1` on.

The inclusion `C ⟶ R|_W` is killed by `β|_W`, so it lifts to the fibre `F` of `β`, which lies in
`D_QCoh(𝒪_X)`; the construction of Stacks 09IV for the lift gives `β' : R' ⟶ F` with
`R'|_W ≅ C ⊞ C'`, and `R₁` is the cone of `R' ⟶ F ⟶ R`, with `R₁|_W ≅ P ⊞ C'[1]`. The morphism
`β₁ : R₁ ⟶ E` is the one of the octahedral axiom for `R' ⟶ F ⟶ R`, and the inclusion of `C'[1]`
into `R₁|_W` is taken through the cone of `β'`, where `β₁` vanishes. -/
theorem exists_isPerfect_restrict_iso_biprod_isZero_homology_of_sub_one
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (W : Subfunctor X.1) (hW : IsOpenSubspace B S hS W)
    (hWqc : IsQuasiCompactSpace B S hS W.toFunctor) (T : Set (points B S hS X.1))
    (hT : IsClosed T)
    (hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι)
    [hDX : HasDerivedCategory.{w} (Modules.{u, u} B S hS X.1 X.2)]
    [hDW : HasDerivedCategory.{w'} (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2)]
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) E)
    (P : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2))
    (α : P ⟶ (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj E)
    (R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (β : R ⟶ E)
    (hR : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect R)
    (hRT : ∀ i : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf.{u} _).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj R)) ⊆ T)
    (C : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2))
    (e : (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj R ≅ P ⊞ C)
    (hC : (smallEtaleRingedSite B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2).IsPerfect C)
    (hCT : ∀ i : ℤ, supportOfSheaf B S hS (openSubspaceSpace B S hS W hW).1
      ((SheafOfModules.toSheaf.{u} _).obj ((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
          (openSubspaceSpace B S hS W hW).2) i).obj C)) ⊆
        pointsMap B S hS W.toFunctor W.ι ⁻¹' T)
    (n : ℤ)
    (hCn : ∀ i : ℤ, n ≤ i → IsZero ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
        (openSubspaceSpace B S hS W hW).2) i).obj C))
    (hβ : (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map β =
        e.hom ≫ biprod.fst ≫ α) :
    ∃ (R₁ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (β₁ : R₁ ⟶ E),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect R₁ ∧
      (∀ i : ℤ, supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf.{u} _).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj R₁)) ⊆ T) ∧
      ∃ (C₁ : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
          (openSubspaceSpace B S hS W hW).2))
        (e₁ : (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj R₁ ≅ P ⊞ C₁),
        (smallEtaleRingedSite B S hS (openSubspaceSpace B S hS W hW).1
          (openSubspaceSpace B S hS W hW).2).IsPerfect C₁ ∧
        (∀ i : ℤ, supportOfSheaf B S hS (openSubspaceSpace B S hS W hW).1
          ((SheafOfModules.toSheaf.{u} _).obj ((DerivedCategory.homologyFunctor
            (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
              (openSubspaceSpace B S hS W hW).2) i).obj C₁)) ⊆
            pointsMap B S hS W.toFunctor W.ι ⁻¹' T) ∧
        (∀ i : ℤ, n - 1 ≤ i → IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS
            (openSubspaceSpace B S hS W hW).1
          (openSubspaceSpace B S hS W hW).2) i).obj C₁)) ∧
        (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map β₁ =
          e₁.hom ≫ biprod.fst ≫ α := by
  classical
  -- the fibre `F ⟶ R ⟶ E` of `β`, in `D_QCoh(𝒪_X)`
  obtain ⟨F, u', w', hT₁⟩ := distinguished_cocone_triangle₁ β
  have hF : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) F :=
    ObjectProperty.ext_of_isTriangulatedClosed₁ _ _ hT₁
      (derivedCategoryB_isQuasicoherentOnSite_of_isPerfect X R hR) hE
  -- the inclusion of `C` lifts to `F|_W`
  have hT₁' := (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map_distinguished _ hT₁
  obtain ⟨α', hα'⟩ : ∃ α' : C ⟶ (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj F,
      biprod.inr ≫ e.inv = α' ≫ (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map u' :=
    Triangle.coyoneda_exact₂ _ hT₁' (biprod.inr ≫ e.inv) (by
    show (biprod.inr ≫ e.inv) ≫ (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map β = 0
    rw [hβ]
    simp)
  -- the construction of Stacks 09IV for the lift
  obtain ⟨R', β', hR', hR'T, C', e', hC', hβ'⟩ :=
    exists_isPerfect_restrict_iso_biprod_isFiniteSumOfPositiveShifts_of_models X hXqc hXqs W hW
      hWqc T hT hTqc F hF C hC hCT α'
  -- the octahedron for `R' ⟶ F ⟶ R`
  obtain ⟨G, v₁₂, w₁₂, h₁₂⟩ := distinguished_cocone_triangle β'
  obtain ⟨R₁, v, w₁₃, h₁₃⟩ := distinguished_cocone_triangle (β' ≫ u')
  let oct := Triangulated.someOctahedron rfl h₁₂ hT₁ h₁₃
  -- restriction to `W`
  have hg : (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map (β' ≫ u') = e'.hom ≫
          biprod.fst ≫ biprod.inr ≫ e.inv := by
    rw [Functor.map_comp, hβ', Category.assoc, Category.assoc, ← hα']
  have hT₁₃' := (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map_distinguished _ h₁₃
  have hT₁₂' := (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map_distinguished _ h₁₂
  obtain ⟨k, hk⟩ : ∃ k : C'⟦(1 : ℤ)⟧ ⟶ (etaleModulePullback.{u, u} B S hS
      (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj G,
      (biprod.inr ≫ e'.inv)⟦(1 : ℤ)⟧' = k ≫ ((etaleModulePullback.{u, u} B S hS
          (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map w₁₂ ≫
        ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app R') :=
    Triangle.coyoneda_exact₁ _ hT₁₂' ((biprod.inr ≫ e'.inv)⟦(1 : ℤ)⟧') (by
    show (biprod.inr ≫ e'.inv)⟦(1 : ℤ)⟧' ≫ ((etaleModulePullback.{u, u} B S hS
        (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map β')⟦(1 : ℤ)⟧' = 0
    rw [← Functor.map_comp, Category.assoc, hβ', Iso.inv_hom_id_assoc, biprod.inr_fst_assoc,
      zero_comp, Functor.map_zero])
  let j₁ := k ≫ (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map oct.m₁
  have hj₁ : j₁ ≫ ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map w₁₃ ≫
          ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app R') =
      (biprod.inr ≫ e'.inv)⟦(1 : ℤ)⟧' := by
    rw [hk]
    simp only [j₁, Category.assoc, ← Functor.map_comp_assoc, oct.comm₂]
  have hiso := isIso_biprod_desc_of_distTriang_of_eq_comp_inr e e'
      ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map (β' ≫ u'))
    ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map v)
          ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map w₁₃ ≫
          ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.commShiftIso
          (1 : ℤ)).hom.app R') hT₁₃' hg
    j₁ hj₁
  let e₁ := (asIso (biprod.desc (biprod.inl ≫ e.inv ≫ (etaleModulePullback.{u, u} B S hS
      (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map v) j₁)).symm
  refine ⟨R₁, oct.m₃, RingedSite.isPerfect_obj₃_of_distinguished_general _ _ h₁₃ hR' hR,
    fun i => ?_, C'⟦(1 : ℤ)⟧, e₁,
    RingedSite.isPerfect_shift_general _ (isPerfect_of_isFiniteSumOfPositiveShifts hC' hC) _,
    fun i => ?_, fun i hi => ?_, ?_⟩
  · exact (subset_union_homology_obj₃_of_distinguished
      (fun M : Modules.{u, u} B S hS X.1 X.2 =>
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf.{u} _).obj M))
      (supportOfSheaf_toSheaf_subset_union_of_exact B S hS X.1 X.2) _ h₁₃ i).trans
      (Set.union_subset (hRT i) (hR'T (i + 1)))
  · rw [supportOfSheaf_homology_shift]
    exact supportOfSheaf_homology_subset_of_isFiniteSumOfPositiveShifts hC' _ hCT _
  · exact (hC'.isZero_homologyFunctor_obj n hCn (1 + i) (by omega)).of_iso
      (((DerivedCategory.homologyFunctor _ 0).shiftIso 1 i (1 + i) rfl).app C')
  · rw [← cancel_epi e₁.inv, Iso.inv_hom_id_assoc]
    apply biprod.hom_ext'
    · simp only [e₁, Iso.symm_inv, asIso_hom, biprod.inl_desc_assoc, Category.assoc,
        ← Functor.map_comp, oct.comm₃, hβ]
      simp
    · simp only [e₁, Iso.symm_inv, asIso_hom, biprod.inr_desc_assoc, j₁, Category.assoc,
        ← Functor.map_comp]
      have hm : oct.m₁ ≫ oct.m₃ = 0 := comp_distTriang_mor_zero₁₂ _ oct.mem
      simp only [biprod.inr_fst_assoc, zero_comp]
      rw [hm, Functor.map_zero, comp_zero]

/-- **Stacks 09IW, first two assertions.** Let `S` be a scheme, `X` a quasi-compact and
quasi-separated algebraic space over `S`, `W ⊆ X` a quasi-compact open subspace, `T ⊆ |X|` a
closed subset such that `X \ T ⟶ X` is quasi-compact, `E` an object of `D_QCoh(𝒪_X)` and
`α : P ⟶ E|_W` a morphism from a perfect object `P` of `D(𝒪_W)` supported on `T ∩ W`. The
construction of Stacks 09IV gives `β : R ⟶ E`, with `R` a perfect object of `D(𝒪_X)` supported
on `T`, such that

1. `R|_W ≅ P ⊕ C` with `C ≅ P^{⊕ n₁}[1] ⊕ ⋯ ⊕ P^{⊕ nₘ}[m]` for some `m ≥ 0` and `n_j ≥ 0`
   (`CategoryTheory.IsFiniteSumOfPositiveShifts`), `β|_W` being `α` on `P` and zero on `C`;
2. the highest degree cohomology sheaf of `R|_W` is that of `P`: whenever `Hⁱ(P) = 0` for all
   `i > d`, the inclusion of the summand `P` induces `Hⁱ(P) ≅ Hⁱ(R|_W)` for every `i ≥ d`.

Both derived categories are taken at arbitrary models; "supported on" is the condition of
Stacks 08GF on every cohomology sheaf, and `D_QCoh(𝒪_X)` is the condition of Stacks 071X. -/
@[stacks 09IW "first and second assertions: the shape of the restriction, and its top cohomology"]
theorem exists_isPerfect_restrict_iso_biprod_isIso_homologyFunctor_map_inl
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (W : Subfunctor X.1) (hW : IsOpenSubspace B S hS W)
    (hWqc : IsQuasiCompactSpace B S hS W.toFunctor) (T : Set (points B S hS X.1))
    (hT : IsClosed T)
    (hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι)
    [hDX : HasDerivedCategory.{w} (Modules.{u, u} B S hS X.1 X.2)]
    [hDW : HasDerivedCategory.{w'} (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2)]
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) E)
    (P : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2))
    (hP : (smallEtaleRingedSite B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2).IsPerfect P)
    (hPT : ∀ i : ℤ, supportOfSheaf B S hS (openSubspaceSpace B S hS W hW).1
      ((SheafOfModules.toSheaf.{u} _).obj ((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
          (openSubspaceSpace B S hS W hW).2) i).obj P)) ⊆
        pointsMap B S hS W.toFunctor W.ι ⁻¹' T)
    (α : P ⟶ (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj E) :
    ∃ (R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (β : R ⟶ E),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect R ∧
      (∀ i : ℤ, supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf.{u} _).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj R)) ⊆ T) ∧
      ∃ (C : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
          (openSubspaceSpace B S hS W hW).2))
        (e : (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj R ≅ P ⊞ C),
        IsFiniteSumOfPositiveShifts P C ∧
        (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map β =
          e.hom ≫ biprod.fst ≫ α ∧
        ∀ d : ℤ, (∀ i : ℤ, d < i → IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS
            (openSubspaceSpace B S hS W hW).1
          (openSubspaceSpace B S hS W hW).2) i).obj P)) →
          ∀ i : ℤ, d ≤ i → IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS
              (openSubspaceSpace B S hS W hW).1
          (openSubspaceSpace B S hS W hW).2) i).map (biprod.inl ≫ e.inv)) := by
  obtain ⟨R, β, hR, hRT, C, e, hC, hβ⟩ :=
    exists_isPerfect_restrict_iso_biprod_isFiniteSumOfPositiveShifts_of_models X hXqc hXqs W hW
      hWqc T hT hTqc E hE P hP hPT α
  refine ⟨R, β, hR, hRT, C, e, hC, hβ, fun d hd i hi => ?_⟩
  have hCz := hC.isZero_homologyFunctor_obj (d + 1) (fun j hj => hd j (by omega)) i (by omega)
  have := isIso_map_biprod_inl_of_isZero (DerivedCategory.homologyFunctor _ i) (A := P) hCz
  rw [Functor.map_comp]
  infer_instance

/-- **Stacks 09IW, third assertion.** In the situation of Stacks 09IV — `S` a scheme, `X` a
quasi-compact and quasi-separated algebraic space over `S`, `W ⊆ X` a quasi-compact open subspace,
`T ⊆ |X|` closed with `X \ T ⟶ X` quasi-compact, `E` in `D_QCoh(𝒪_X)` and `α : P ⟶ E|_W` with
`P` perfect in `D(𝒪_W)` supported on `T ∩ W` — one can achieve equality of the cohomology sheaves
of `R|_W` and `P` above any given degree: for every integer `N` there is `β : R ⟶ E` with `R`
perfect in `D(𝒪_X)` and supported on `T`, and `P` a direct summand of `R|_W` compatibly with `α`
and `β|_W` — `s : P ⟶ R|_W` and `r : R|_W ⟶ P` with `s ≫ r = 𝟙 P` and `s ≫ β|_W = α`, indeed
`β|_W = r ≫ α` — such that `Hⁱ(s) : Hⁱ(P) ⟶ Hⁱ(R|_W)` is an isomorphism for every `i ≥ N`.

Both derived categories are taken at arbitrary models. -/
@[stacks 09IW "third assertion: equality of cohomology sheaves above any given degree"]
theorem exists_isPerfect_retract_restrict_isIso_homologyFunctor_map
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (W : Subfunctor X.1) (hW : IsOpenSubspace B S hS W)
    (hWqc : IsQuasiCompactSpace B S hS W.toFunctor) (T : Set (points B S hS X.1))
    (hT : IsClosed T)
    (hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι)
    [hDX : HasDerivedCategory.{w} (Modules.{u, u} B S hS X.1 X.2)]
    [hDW : HasDerivedCategory.{w'} (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2)]
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) E)
    (P : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2))
    (hP : (smallEtaleRingedSite B S hS (openSubspaceSpace B S hS W hW).1
      (openSubspaceSpace B S hS W hW).2).IsPerfect P)
    (hPT : ∀ i : ℤ, supportOfSheaf B S hS (openSubspaceSpace B S hS W hW).1
      ((SheafOfModules.toSheaf.{u} _).obj ((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
          (openSubspaceSpace B S hS W hW).2) i).obj P)) ⊆
        pointsMap B S hS W.toFunctor W.ι ⁻¹' T)
    (α : P ⟶ (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
      (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj E) (N : ℤ) :
    ∃ (R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (β : R ⟶ E),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect R ∧
      (∀ i : ℤ, supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf.{u} _).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj R)) ⊆ T) ∧
      ∃ (s : P ⟶ (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj R)
        (r : (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj R ⟶ P),
        s ≫ r = 𝟙 P ∧
        s ≫ (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map β = α ∧
        (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map β = r ≫ α ∧
        ∀ i : ℤ, N ≤ i → IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS
            (openSubspaceSpace B S hS W hW).1
          (openSubspaceSpace B S hS W hW).2) i).map s) := by
  obtain ⟨b, hb⟩ := exists_isZero_homology_of_lt_of_isPerfect (openSubspaceSpace B S hS W hW)
    hWqc P hP
  obtain ⟨R₀, β₀, hR₀, hR₀T, C₀, e₀, hC₀, hβ₀⟩ :=
    exists_isPerfect_restrict_iso_biprod_isFiniteSumOfPositiveShifts_of_models X hXqc hXqs W hW
      hWqc T hT hTqc E hE P hP hPT α
  have key : ∀ k : ℕ, ∃ (R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (β : R ⟶ E),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect R ∧
      (∀ i : ℤ, supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf.{u} _).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj R)) ⊆ T) ∧
      ∃ (C : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
          (openSubspaceSpace B S hS W hW).2))
        (e : (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.obj R ≅ P ⊞ C),
        (smallEtaleRingedSite B S hS (openSubspaceSpace B S hS W hW).1
          (openSubspaceSpace B S hS W hW).2).IsPerfect C ∧
        (∀ i : ℤ, supportOfSheaf B S hS (openSubspaceSpace B S hS W hW).1
          ((SheafOfModules.toSheaf.{u} _).obj ((DerivedCategory.homologyFunctor
            (Modules.{u, u} B S hS (openSubspaceSpace B S hS W hW).1
              (openSubspaceSpace B S hS W hW).2) i).obj C)) ⊆
            pointsMap B S hS W.toFunctor W.ι ⁻¹' T) ∧
        (∀ i : ℤ, b - k ≤ i → IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS
            (openSubspaceSpace B S hS W hW).1
          (openSubspaceSpace B S hS W hW).2) i).obj C)) ∧
        (etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS W hW)
          (isEtale_openSubspaceHom B S hS W hW)).mapDerivedCategory.map β =
          e.hom ≫ biprod.fst ≫ α := by
    intro k
    induction k with
    | zero =>
      exact ⟨R₀, β₀, hR₀, hR₀T, C₀, e₀, isPerfect_of_isFiniteSumOfPositiveShifts hC₀ hP,
        supportOfSheaf_homology_subset_of_isFiniteSumOfPositiveShifts hC₀ _ hPT,
        fun i hi => hC₀.isZero_homologyFunctor_obj (b + 1) (fun j hj => hb j (by omega)) i
          (by omega), hβ₀⟩
    | succ k ih =>
      obtain ⟨R, β, hR, hRT, C, e, hC, hCT, hCn, hβ⟩ := ih
      obtain ⟨R₁, β₁, hR₁, hR₁T, C₁, e₁, hC₁, hC₁T, hC₁n, hβ₁⟩ :=
        exists_isPerfect_restrict_iso_biprod_isZero_homology_of_sub_one X hXqc hXqs W hW hWqc T
          hT hTqc E hE P α R β hR hRT C e hC hCT (b - k) hCn hβ
      exact ⟨R₁, β₁, hR₁, hR₁T, C₁, e₁, hC₁, hC₁T, fun i hi => hC₁n i (by omega), hβ₁⟩
  have hN := Int.self_le_toNat (b - N)
  obtain ⟨R, β, hR, hRT, C, e, -, -, hCn, hβ⟩ := key (b - N).toNat
  refine ⟨R, β, hR, hRT, biprod.inl ≫ e.inv, e.hom ≫ biprod.fst, by simp, by simp [hβ],
    by simp [hβ], fun i hi => ?_⟩
  have hCz := hCn i (by omega)
  have := isIso_map_biprod_inl_of_isZero (DerivedCategory.homologyFunctor _ i) (A := P) hCz
  rw [Functor.map_comp]
  infer_instance

end AlgebraicGeometry.Space

end
