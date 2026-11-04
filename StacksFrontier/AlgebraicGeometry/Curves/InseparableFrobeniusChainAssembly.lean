module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableFactorizationChain
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableFrobeniusIteration
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.RelativeFrobeniusDegree

/-!
# Assembling the degree-`p` chain of a purely inseparable morphism of curves

The identification of a purely inseparable nonconstant morphism of proper nonsingular curves
with an iterated relative Frobenius is proved in
`StacksFrontier/AlgebraicGeometry/Curves/InseparableFrobeniusIteration.lean` from a chain of
degree-`p` steps presented as a family indexed by `ℕ`, while the factorization that produces
such a chain, [Stacks, Tag 0CCX], delivers it as a family indexed by `Fin (n + 1)`.  This file
converts the one presentation into the other and discharges the remaining hypotheses of the
assembly, so that the identification is available with no hypothesis beyond those of its
source.

## Main results

* `AlgebraicGeometry.isPurelyInseparable_functionFieldMap_iff_residueFieldMap` and
  `AlgebraicGeometry.isSeparable_functionField_iff_residueField`: the extension of function
  fields of a dominant morphism of integral schemes and the extension of residue fields at the
  generic point are the same extension.
* `AlgebraicGeometry.residueDegree_relativeFrobenius_isCurve`: the relative Frobenius of a
  smooth curve has residue degree `p` at the generic point, which is the shape in which the
  assembly consumes [Stacks, Tag 0CCF].
* `AlgebraicGeometry.existsUnique_nat_existsUnique_iso_nFoldFrobeniusTwist`: the conclusion of
  [Stacks, Tag 0CCZ] with no carried hypothesis.

## Implementation notes

The chain of [Stacks, Tag 0CCX] is a family `Z : Fin (n + 1) → ProperNonsingularCurve k` with
edges `g i : Z i.castSucc ⟶ Z i.succ`, the composition along the chain being recorded by
morphisms `w i : Z i ⟶ Y` satisfying `g i ≫ w i.succ = w i.castSucc`.  The assembly instead
takes a family indexed by `ℕ`, constrained only below the index `n`, and reads the composition
off `AlgebraicGeometry.InseparableFrobeniusIteration.chainComp`.  The conversion extends the
family past `n` by the last curve of the chain and the edges past `n` by identities, which is
legitimate precisely because no constraint is imposed there; the two readings of "`f` is the
composition along the chain" are reconciled by
`AlgebraicGeometry.InseparableFrobeniusChainAssembly.chainComp_comp_ladder`.

Each edge of the chain of [Stacks, Tag 0CCX] carries its degree and the nonseparability of its
extension of function fields, whereas the assembly consumes pure inseparability of the
extension of residue fields at the generic point.  The two are reconciled by
`AlgebraicGeometry.isPurelyInseparable_residueFieldMap_genericPoint`, a nonseparable extension
of degree the characteristic being purely inseparable, after transporting nonseparability from
function fields to residue fields.

## References

* [Stacks Project, Tag 0CCZ](https://stacks.math.columbia.edu/tag/0CCZ)
* [Stacks Project, Tag 0CCX](https://stacks.math.columbia.edu/tag/0CCX)
* [Stacks Project, Tag 0CCF](https://stacks.math.columbia.edu/tag/0CCF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-! ### Transporting the extension of function fields to the residue fields -/

/-- Pure inseparability of a homomorphism of fields transfers along a commuting square of ring
isomorphisms. -/
theorem RingHom.isPurelyInseparable_of_ringEquiv {A B C D : Type*}
    [Field A] [Field B] [Field C] [Field D]
    (f : A →+* B) (g : C →+* D) (e : A ≃+* C) (e' : B ≃+* D)
    (h : g.comp e.toRingHom = e'.toRingHom.comp f)
    (hf : f.IsPurelyInseparable) : g.IsPurelyInseparable := by
  let _ := f.toAlgebra
  let _ := g.toAlgebra
  let _ : IsPurelyInseparable A B := hf
  let q := ringExpChar A
  let _ : ExpChar C q := expChar_of_injective_ringHom (f := e.toRingHom) e.injective q
  apply (isPurelyInseparable_iff_pow_mem C q).mpr
  intro x
  obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem A q (e'.symm x)
  refine ⟨n, e y, ?_⟩
  show g (e y) = x ^ q ^ n
  rw [show g (e y) = e' (f y) from DFunLike.congr_fun h y, ← RingHom.algebraMap_toAlgebra f, hy,
    map_pow, e'.apply_symm_apply]

/-- For a dominant morphism of integral schemes, the extension of function fields is purely
inseparable exactly when the extension of residue fields at the generic point is: the two
extensions are identified by the canonical isomorphisms of a function field with the residue
field at the generic point. -/
theorem isPurelyInseparable_functionFieldMap_iff_residueFieldMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    (functionFieldMap f).IsPurelyInseparable ↔
      (f.residueFieldMap (genericPoint X)).hom.IsPurelyInseparable := by
  have hsquare := residueFieldMap_comp_genericResidueEquivOfDominant f
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact RingHom.isPurelyInseparable_of_ringEquiv _ _ (genericResidueEquivOfDominant f)
      (genericResidueEquiv X) hsquare h
  · refine RingHom.isPurelyInseparable_of_ringEquiv _ _ (genericResidueEquivOfDominant f).symm
      (genericResidueEquiv X).symm ?_ h
    ext x
    simpa [RingEquiv.eq_symm_apply] using
      (RingHom.ext_iff.mp hsquare ((genericResidueEquivOfDominant f).symm x)).symm

/-- For a dominant morphism of integral schemes, the extension of function fields is separable
exactly when the extension of residue fields at the generic point is. -/
theorem isSeparable_functionField_iff_residueField {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    @Algebra.IsSeparable Y.functionField X.functionField _ _
        (functionFieldMap f).toAlgebra ↔
      @Algebra.IsSeparable (Y.residueField (f (genericPoint X)))
        (X.residueField (genericPoint X)) _ _
        (f.residueFieldMap (genericPoint X)).hom.toAlgebra := by
  let _ := (functionFieldMap f).toAlgebra
  let _ := (f.residueFieldMap (genericPoint X)).hom.toAlgebra
  exact Algebra.IsSeparable.iff_of_equiv_equiv (genericResidueEquivOfDominant f)
    (genericResidueEquiv X) (residueFieldMap_comp_genericResidueEquivOfDominant f)

/-! ### Nonconstancy of a dominant morphism of proper curves -/

/-- A curve over a field has more than one point: a space with at most one point has dimension at
most zero. -/
theorem nontrivial_of_isCurve {k : Type u} [Field k] {X : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    [IsCurve k pX] : Nontrivial X := by
  by_contra h
  have _ : Subsingleton X := not_nontrivial_iff_subsingleton.mp h
  have hle := topologicalKrullDim_zero_of_discreteTopology X
  rw [IsCurve.topologicalKrullDim_eq_one (k := k) (f := pX)] at hle
  norm_num at hle

/-- A dominant morphism from a proper curve over `k` to a curve over `k` is nonconstant: it is
proper, hence closed, so its dense image is the whole target, which has more than one point. -/
theorem nontrivial_range_of_isDominant_of_isCurve {k : Type u} [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) [IsCurve k pX] [IsCurve k pY] [IsProper pX]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) [IsDominant f] : (Set.range f).Nontrivial := by
  have _ : Nontrivial Y := nontrivial_of_isCurve pY
  have _ : IsProper (f ≫ pY) := hf ▸ (inferInstance : IsProper pX)
  have _ : IsProper f := IsProper.of_comp f pY
  rw [Set.range_eq_univ.mpr (inferInstance : Surjective f).surj]
  exact Set.nontrivial_univ

/-! ### The relative Frobenius of a smooth curve -/

/-- **[Stacks, Tag 0CCF] at a smooth curve.** The relative Frobenius of a smooth curve over a
field of characteristic `p` has residue degree `p` at the generic point. -/
theorem residueDegree_relativeFrobenius_isCurve {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (hS : IsInCharacteristic (Spec (.of k)) p) (Z : Over (Spec (.of k)))
    [IsCurve k Z.hom] [Smooth Z.hom] :
    (relativeFrobenius (Spec (.of k)) p hS Z).left.residueDegree (genericPoint Z.left) = p := by
  have h : (relativeFrobenius (Spec (.of k)) p hS Z).left.residueDegree
      (genericPoint Z.left) = p ^ 1 :=
    residueDegree_relativeFrobenius_genericPoint Z.hom p hS (geometricallyReduced_of_smooth Z.hom)
      1 (IsCurve.topologicalKrullDim_eq_one (k := k) (f := Z.hom))
  simpa using h

/-! ### From the chain of Tag 0CCX to the chain the assembly consumes -/

namespace InseparableFrobeniusChainAssembly

open InseparableFrobeniusIteration

/-- The composition along the first `n` edges of a chain, read off a family of morphisms to a
common target satisfying the ladder identity. -/
theorem chainComp_comp_ladder {S : Scheme.{u}} (C : ℕ → Over S) (g : ∀ i, C i ⟶ C (i + 1))
    {T : Over S} (w : ∀ i, C i ⟶ T) (n : ℕ)
    (hladder : ∀ i, i < n → g i ≫ w (i + 1) = w i) :
    chainComp C g n ≫ w n = w 0 := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [chainComp_succ, Category.assoc, hladder m (by omega)]
      exact ih fun i hi => hladder i (by omega)

end InseparableFrobeniusChainAssembly

open InseparableFrobeniusIteration InseparableFrobeniusChainAssembly in
/-- **Stacks Project, Tag 0CCZ.** Let `f : X ⟶ Y` be a nonconstant morphism of proper nonsingular
curves over a field `k` of characteristic `p`, with `X` smooth and the induced extension of
function fields purely inseparable. Then there is a unique number `n` of iterations and, for it, a
unique isomorphism over `k` of the `n`-fold Frobenius twist of `X` with `Y` carrying the `n`-fold
relative Frobenius of `X` to `f`.

Both inputs of the source's proof are supplied here: the degree-`p` factorization of
`AlgebraicGeometry.exists_chain_isInseparableDegreePrime` ([Stacks, Tag 0CCX]), converted to the
indexing the assembly uses, and the degree of the relative Frobenius of a smooth curve,
`AlgebraicGeometry.residueDegree_relativeFrobenius_isCurve` ([Stacks, Tag 0CCF]). -/
@[stacks 0CCZ "the unique number of iterations and the unique isomorphism of the correspondingly \
iterated Frobenius twist of X with Y carrying the iterated relative Frobenius to f"]
theorem existsUnique_nat_existsUnique_iso_nFoldFrobeniusTwist
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsInCharacteristic (Spec (.of k)) p)
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY] [IsProper pX] [IsProper pY] [Smooth pX]
    (hXreg : IsRegular X) (hYreg : IsRegular Y)
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (hnonconstant : (Set.range f).Nontrivial)
    (hpure : (f.residueFieldMap (genericPoint X)).hom.IsPurelyInseparable) :
    ∃! m : ℕ, ∃! e : nFoldFrobeniusTwist (Spec (.of k)) p hS m (Over.mk pX) ≅ Over.mk pY,
      nFoldRelativeFrobenius (Spec (.of k)) p hS m (Over.mk pX) ≫ e.hom = Over.homMk f hf := by
  classical
  have _ : IsDominant f := isDominant_of_nontrivial_range_of_isCurve pX pY f hnonconstant
  let F : Over.mk pX ⟶ Over.mk pY := Over.homMk f hf
  have _ : IsDominant F.left := inferInstanceAs (IsDominant f)
  have hpureff : (functionFieldMap f).IsPurelyInseparable :=
    (isPurelyInseparable_functionFieldMap_iff_residueFieldMap f).mpr hpure
  obtain ⟨n, Z, g, w, e, hiso, hlast, hstart, hladder, hedge⟩ :=
    exists_chain_isInseparableDegreePrime (k := k) p pX pY hXreg hYreg F hpureff
  -- the chain of `Fin (n + 1)`, reindexed by `ℕ`
  let idx : ℕ → Fin (n + 1) := fun i => ⟨min i n, Nat.lt_succ_of_le (min_le_right i n)⟩
  have hidx0 : idx 0 = 0 := Fin.ext (by simp [idx])
  have hidxn : idx n = Fin.last n := Fin.ext (by simp [idx])
  have hidxlt : ∀ i, (hi : i < n) → idx i = (⟨i, hi⟩ : Fin n).castSucc := fun i hi =>
    Fin.ext (by simp [idx, Nat.min_eq_left hi.le])
  have hidxsucc : ∀ i, (hi : i < n) → idx (i + 1) = (⟨i, hi⟩ : Fin n).succ := fun i hi =>
    Fin.ext (by simp [idx, Nat.min_eq_left (by omega : i + 1 ≤ n)])
  have hidxstab : ∀ i, ¬ i < n → idx i = idx (i + 1) := by
    intro i hi
    apply Fin.ext
    simp only [idx]
    omega
  -- each edge below `n`, transported to the new indexing, with all its properties
  have key : ∀ i, (hi : i < n) → ∃ G : (Z (idx i)).obj ⟶ (Z (idx (i + 1))).obj,
      G ≫ w (idx (i + 1)) = w (idx i) ∧ (Set.range G.left).Nontrivial ∧
        G.left.residueDegree (genericPoint (Z (idx i)).obj.left) = p ∧
        (G.left.residueFieldMap (genericPoint (Z (idx i)).obj.left)).hom.IsPurelyInseparable := by
    intro i hi
    rw [hidxlt i hi, hidxsucc i hi]
    generalize (⟨i, hi⟩ : Fin n) = j
    obtain ⟨hdom, -, hns, hdeg⟩ := hedge j
    have _ : IsDominant (g j).left := hdom
    have _ : IsCurve k (Z j.castSucc).obj.hom := (Z _).isCurve
    have _ : IsCurve k (Z j.succ).obj.hom := (Z _).isCurve
    have _ : IsProper (Z j.castSucc).obj.hom := (Z _).isProper
    refine ⟨g j, hladder j, ?_, hdeg, ?_⟩
    · exact nontrivial_range_of_isDominant_of_isCurve (Z j.castSucc).obj.hom
        (Z j.succ).obj.hom (g j).left (Over.w (g j))
    · exact isPurelyInseparable_residueFieldMap_genericPoint p (Z j.castSucc).obj.hom
        (Z j.succ).obj.hom (g j).left hdeg
        fun hsep => hns ((isSeparable_functionField_iff_residueField _).mpr hsep)
  let C : ℕ → Over (Spec (.of k)) := fun i => (Z (idx i)).obj
  let W : ∀ i, C i ⟶ Over.mk pY := fun i => w (idx i)
  have hcurve : ∀ i, IsCurve k (C i).hom := fun i => (Z (idx i)).isCurve
  have hproper : ∀ i, IsProper (C i).hom := fun i => (Z (idx i)).isProper
  have hreg : ∀ i, IsRegular (C i).left := fun i => (Z (idx i)).isRegular
  let G : ∀ i, C i ⟶ C (i + 1) := fun i =>
    if hi : i < n then (key i hi).choose
    else eqToHom (congrArg (fun j : Fin (n + 1) => (Z j).obj) (hidxstab i hi))
  have hG : ∀ i, (hi : i < n) → G i = (key i hi).choose := fun i hi => dif_pos hi
  -- the two ends of the chain
  have hGspec : ∀ i, (hi : i < n) → G i ≫ W (i + 1) = W i ∧ (Set.range (G i).left).Nontrivial ∧
      (G i).left.residueDegree (genericPoint (C i).left) = p ∧
      ((G i).left.residueFieldMap (genericPoint (C i).left)).hom.IsPurelyInseparable :=
    fun i hi => by rw [hG i hi]; exact (key i hi).choose_spec
  obtain ⟨e', hiso', hstart'⟩ : ∃ (e' : Over.mk pX ⟶ C 0), IsIso e' ∧ e' ≫ W 0 = F := by
    change ∃ e' : Over.mk pX ⟶ (Z (idx 0)).obj, IsIso e' ∧ e' ≫ w (idx 0) = F
    rw [hidx0]
    exact ⟨e, hiso, hstart⟩
  have hlast' : IsIso (W n) := by
    change IsIso (w (idx n))
    rw [hidxn]
    exact hlast
  let iX : C 0 ≅ Over.mk pX := (asIso e').symm
  let iY : C n ≅ Over.mk pY := asIso (W n)
  refine existsUnique_nat_existsUnique_iso_nFoldFrobeniusTwist_of_inseparable_chain p hS
    (fun Z _ _ => residueDegree_relativeFrobenius_isCurve p hS Z) pX pY hXreg hYreg f hf
    hnonconstant hpure n C G hcurve hproper hreg
    (fun i hi => (hGspec i hi).2.1) (fun i hi => (hGspec i hi).2.2.1)
    (fun i hi => (hGspec i hi).2.2.2) iX iY ?_
  have hchain : chainComp C G n ≫ W n = W 0 :=
    chainComp_comp_ladder C G W n fun i hi => (hGspec i hi).1
  calc iX.inv ≫ chainComp C G n ≫ iY.hom
      = e' ≫ chainComp C G n ≫ W n := rfl
    _ = e' ≫ W 0 := by rw [hchain]
    _ = F := hstart'

end AlgebraicGeometry

end
