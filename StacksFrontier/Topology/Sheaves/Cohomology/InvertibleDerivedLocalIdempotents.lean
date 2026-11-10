module

public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedClauseThreeToTwo
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleLocalSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedFactorInvertible
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedFactorUnit

/-!
# Clause (2) of Stacks 0FPG from local idempotents

Let `K`, `K'` be complexes of `𝒪_X`-modules. Suppose every point has an open neighbourhood `V`
carrying finitely many orthogonal idempotents `f_n` of `𝒪_X(V)` summing to `1`, such that `f_n`
acts on `H^k(K)|_V` as the identity for `k = n` and as zero otherwise, and on `H^k(K')|_V` as the
identity for `k = -n` and as zero otherwise, no nonzero section over an open of `V` acts as zero on
all the `H^k(K)`, and `H^n(K) ⊗ H^{-n}(K')` is the `n`-th factor over `V`. Then the idempotents
glue to a locally finite complete family of orthogonal idempotents of `Γ(X, 𝒪_X)`, and `K`
satisfies clause (2) of Stacks 0FPG.

## Main definitions

* `Stacks.Cohomology.InvertibleDerived.LocalSplitting`: the local datum above.

## Main results

* `Stacks.Cohomology.InvertibleDerived.hasInvertibleModuleDecomposition_of_localSplitting`.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open StrictlyPerfect Stacks.SheafOfModules.DerivedMonoidal

universe u d

namespace Stacks.Cohomology.InvertibleDerived

variable {X : RingedSpace.{u, u}}

/-- The restriction of a section of `𝒪_X` over `V` to an open `W ≤ V`. -/
public abbrev resLE {V W : Opens X.carrier} (h : W ≤ V) (s : X.presheaf.obj (op V)) :
    X.presheaf.obj (op W) :=
  X.presheaf.map (homOfLE h).op s

/-- **A local splitting of a complex over an open set `V`**: finitely many orthogonal idempotents
of `𝒪_X(V)` summing to `1`, acting on the cohomology sheaves of `K` over `V` as the degree
projections, faithfully, and such that over any global family of idempotents restricting to them
the cohomology sheaves are invertible over the corners on `V`. -/
public structure LocalSplitting (K K' : CochainComplex (Mod X.sheaf) ℤ) (V : Opens X.carrier) where
  /-- The degrees which occur over `V`. -/
  S : Finset ℤ
  /-- The idempotents. -/
  f : ℤ → X.presheaf.obj (op V)
  /-- Each `f n` is idempotent. -/
  idem : ∀ n, IsIdempotentElem (f n)
  /-- The `f n` are pairwise orthogonal. -/
  ortho : ∀ n m, n ≠ m → f n * f m = 0
  /-- `f n` vanishes for `n ∉ S`. -/
  eq_zero : ∀ n ∉ S, f n = 0
  /-- The `f n` with `n ∈ S` sum to `1`. -/
  sum_eq_one : ∑ n ∈ S, f n = 1
  /-- `f n` acts on `H^k(K)` over `V` as `1` for `k = n` and as `0` otherwise. -/
  smul : ∀ (n k : ℤ) {W : Opens X.carrier} (hW : W ≤ V) (m : (K.homology k).val.obj (op W)),
    ringSec (U := op W) (resLE hW (f n)) • m = if k = n then m else 0
  /-- `f n` acts on `H^k(K')` over `V` as `1` for `k = -n` and as `0` otherwise. -/
  smul' : ∀ (n k : ℤ) {W : Opens X.carrier} (hW : W ≤ V) (m : (K'.homology k).val.obj (op W)),
    ringSec (U := op W) (resLE hW (f n)) • m = if k = -n then m else 0
  /-- No nonzero section over an open of `V` acts as zero on every cohomology sheaf of `K`. -/
  faithful : ∀ {W : Opens X.carrier} (_ : W ≤ V) (t : X.presheaf.obj (op W)),
    (∀ (k : ℤ) {W' : Opens X.carrier} (hW' : W' ≤ W) (m : (K.homology k).val.obj (op W')),
      ringSec (U := op W') (resLE hW' t) • m = 0) → t = 0
  /-- Over `V`, `H^n(K) ⊗ H^{-n}(K')` is the image of multiplication by any global section
  restricting to `f_n`. -/
  pairing : ∀ (n : ℤ) (e : X.presheaf.obj (op ⊤)), IsIdempotentElem e →
    (∀ {W : Opens X.carrier} (hW : W ≤ V), globalRes e W = resLE hW (f n)) →
      letI := SheafOfModules.monoidalCategorySheafTensor X.sheaf
      Nonempty ((restrictModules X V).obj
          (MonoidalCategory.tensorObj (K.homology n) (K'.homology (-n)) : Mod X.sheaf) ≅
        (restrictModules X V).obj (splitObj (C := Mod X.sheaf)
          (smulHom e (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))))

namespace LocalSplitting

variable {K K' : CochainComplex (Mod X.sheaf) ℤ}

/-- Restricting a section of `𝒪_X` from `V` to `W` and then to `W'` is restricting it from `V` to
`W'`. -/
public theorem resLE_resLE {V W W' : Opens X.carrier} (h : W ≤ V) (h' : W' ≤ W)
    (s : X.presheaf.obj (op V)) : resLE h' (resLE h s) = resLE (h'.trans h) s := by
  rw [resLE, resLE, resLE, ← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  rfl

/-- Two local splittings agree on the overlap of their opens. -/
public theorem resLE_f_eq {V V' : Opens X.carrier} (A : LocalSplitting K K' V)
    (B : LocalSplitting K K' V') (n : ℤ) :
    resLE (inf_le_left : V ⊓ V' ≤ V) (A.f n) = resLE (inf_le_right : V ⊓ V' ≤ V') (B.f n) := by
  refine sub_eq_zero.mp (A.faithful inf_le_left _ fun k W' hW' m => ?_)
  have hsub : resLE hW' (resLE (inf_le_left : V ⊓ V' ≤ V) (A.f n) -
      resLE (inf_le_right : V ⊓ V' ≤ V') (B.f n)) =
      resLE (hW'.trans inf_le_left) (A.f n) - resLE (hW'.trans inf_le_right) (B.f n) :=
    (map_sub _ _ _).trans (congrArg₂ (· - ·) (resLE_resLE _ _ _) (resLE_resLE _ _ _))
  exact (congrArg (fun a => ringSec (U := op W') a • m) hsub).trans
    ((sub_smul (ringSec (U := op W') (resLE _ (A.f n)))
      (ringSec (U := op W') (resLE _ (B.f n))) m).trans
      (sub_eq_zero.mpr ((A.smul n k _ m).trans (B.smul n k _ m).symm)))

end LocalSplitting

section Glue

variable {K K' : CochainComplex (Mod X.sheaf) ℤ} (V : X.carrier → Opens X.carrier)
  (hxV : ∀ x, x ∈ V x) (A : ∀ x, LocalSplitting K K' (V x))

include hxV in
/-- Opens `V x` with `x ∈ V x` for every point `x` cover `X`. -/
public theorem iSup_eq_top_of_mem : iSup V = ⊤ :=
  top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ⟨x, hxV x⟩

/-- The degree `n` idempotents of the local splittings agree on overlaps. -/
public theorem isCompatible_localSplitting (n : ℤ) :
    TopCat.Presheaf.IsCompatible X.presheaf V fun x => (A x).f n :=
  fun x y => (A x).resLE_f_eq (A y) n

/-- The glued idempotent of degree `n`. -/
public def glueSplitting (n : ℤ) : X.presheaf.obj (op ⊤) :=
  (presheaf_existsUnique_gluing V ⊤ (fun _ => homOfLE le_top)
    (iSup_eq_top_of_mem V hxV ▸ le_rfl) _ (isCompatible_localSplitting V A n)).exists.choose

/-- The glued idempotent of degree `n` restricts on `V x` to the idempotent `f n` of the splitting
at `x`. -/
public theorem globalRes_glueSplitting (n : ℤ) (x : X.carrier) :
    globalRes (glueSplitting V hxV A n) (V x) = (A x).f n :=
  (presheaf_existsUnique_gluing V ⊤ (fun _ => homOfLE le_top)
    (iSup_eq_top_of_mem V hxV ▸ le_rfl) _ (isCompatible_localSplitting V A n)).exists.choose_spec x

/-- The glued idempotent of degree `n` restricts on an open `W ≤ V x` to the restriction of the
idempotent `f n` of the splitting at `x`. -/
public theorem globalRes_glueSplitting_of_le (n : ℤ) (x : X.carrier) {W : Opens X.carrier}
    (h : W ≤ V x) : globalRes (glueSplitting V hxV A n) W = resLE h ((A x).f n) := by
  rw [← globalRes_glueSplitting V hxV A n x, ← map_globalRes _ (homOfLE h).op]

/-- **The glued idempotents.** -/
public def glueIdempotents : LocallyFiniteIdempotents X where
  e := glueSplitting V hxV A
  idem n := global_eq_of_res_eq V (iSup_eq_top_of_mem V hxV) fun x => by
    rw [globalRes_mul, globalRes_glueSplitting]
    exact (A x).idem n
  ortho n m hnm := global_eq_of_res_eq V (iSup_eq_top_of_mem V hxV) fun x => by
    rw [globalRes_mul, globalRes_glueSplitting, globalRes_glueSplitting, globalRes_zero]
    exact (A x).ortho n m hnm
  locallyFinite x := ⟨V x, (A x).S, hxV x, fun n hn => by
      rw [globalRes_glueSplitting]
      exact (A x).eq_zero n hn, by
    simp only [globalRes_glueSplitting]
    exact (A x).sum_eq_one⟩

/-- A section is acted on by the glued idempotent `e_n` as a given section `m'` as soon as this
holds on each `W ⊓ V x`, where `e_n` restricts to `f n` of the splitting at `x`. -/
private theorem globalRes_glueSplitting_smul_eq (n : ℤ) (M : Mod X.sheaf) (W : Opens X.carrier)
    (m m' : M.val.obj (op W))
    (h : ∀ x, ringSec (U := op (W ⊓ V x)) (resLE (inf_le_right : W ⊓ V x ≤ V x) ((A x).f n)) •
      M.val.map (homOfLE (inf_le_left : W ⊓ V x ≤ W)).op m =
      M.val.map (homOfLE (inf_le_left : W ⊓ V x ≤ W)).op m') :
    ringSec (U := op W) (globalRes (glueSplitting V hxV A n) W) • m = m' :=
  mod_eq_of_locally_eq _ (fun x => W ⊓ V x) W (fun _ => homOfLE inf_le_left)
    (fun y hy => Opens.mem_iSup.mpr ⟨y, Opens.mem_inf.mpr ⟨hy, hxV y⟩⟩) _ _ fun x =>
    (res_smulHom (glueSplitting V hxV A n) M inf_le_left m).trans
      ((congrArg (fun a => ringSec (U := op (W ⊓ V x)) a • M.val.map (homOfLE inf_le_left).op m)
        (globalRes_glueSplitting_of_le V hxV A n x inf_le_right)).trans (h x))

/-- The glued idempotents act on the cohomology sheaves of `K` as the degree projections. -/
public theorem actsOnHomology_glueIdempotents :
    ActsOnHomology (fun n => smulNatTrans ((glueIdempotents V hxV A).e n)) K := by
  intro n k
  rw [smulNatTrans_app]
  split_ifs with hkn
  · ext W m
    exact globalRes_glueSplitting_smul_eq V hxV A n _ W.unop m m fun x =>
      (A x).smul n k inf_le_right _ |>.trans (ite_eq_left hkn)
  · ext W m
    exact globalRes_glueSplitting_smul_eq V hxV A n _ W.unop m 0 fun x =>
      (A x).smul n k inf_le_right _ |>.trans ((ite_eq_right hkn).trans (map_zero _).symm)

/-- `e_n` acts as the identity on `H^{-n}(K')`. -/
public theorem actsAsOne_glueIdempotents_neg (n : ℤ) :
    (glueIdempotents V hxV A).ActsAsOne n (K'.homology (-n)) := fun W m =>
  globalRes_glueSplitting_smul_eq V hxV A n _ W.unop m m fun x =>
    (A x).smul' n (-n) inf_le_right _ |>.trans (ite_eq_left rfl)

include hxV A in
/-- **Clause (2) of Stacks 0FPG from local splittings.** -/
public theorem hasInvertibleModuleDecomposition_of_localSplitting
    [HasDerivedCategory.{d} (Mod X.sheaf)] :
    HasInvertibleModuleDecomposition X (DerivedCategory.Q.obj K) := by
  let := SheafOfModules.monoidalCategorySheafTensor X.sheaf
  refine hasInvertibleModuleDecomposition_of_idempotents
    (actsOnHomology_glueIdempotents V hxV A) fun n => ?_
  have hF' := actsAsOne_glueIdempotents_neg V hxV A n
  refine isInvertibleModule_of_restrict_tensorObj_iso (glueIdempotents V hxV A).productDecomposition
    n _ (LocallyFiniteIdempotents.factorModule hF') V hxV fun x => ?_
  obtain ⟨e⟩ := (A x).pairing n ((glueIdempotents V hxV A).e n) ((glueIdempotents V hxV A).idem n)
    (fun hW => globalRes_glueSplitting_of_le V hxV A n x hW)
  let t : (MonoidalCategory.tensorObj
      (((glueIdempotents V hxV A).productDecomposition.toOXMod n).obj
        (LocallyFiniteIdempotents.factorModule (actsOnHomology_glueIdempotents V hxV A |>
          actsAsOne_homology <| n)))
      (((glueIdempotents V hxV A).productDecomposition.toOXMod n).obj
        (LocallyFiniteIdempotents.factorModule hF')) : Mod X.sheaf) ≅
      MonoidalCategory.tensorObj (K.homology n) (K'.homology (-n)) :=
    MonoidalCategory.tensorIso (LocallyFiniteIdempotents.toOXModFactorModuleIso _)
      (LocallyFiniteIdempotents.toOXModFactorModuleIso hF')
  exact ⟨(restrictModules X (V x)).mapIso t ≪≫ e ≪≫
    (restrictModules X (V x)).mapIso ((glueIdempotents V hxV A).toOXModUnitIso n).symm⟩

end Glue

end Stacks.Cohomology.InvertibleDerived

end
