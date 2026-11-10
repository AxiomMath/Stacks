module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryCoproducts
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryProducts
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects

/-!
# The cohomological detection window of a compact object

Let `(A, d)` be a differential graded algebra. A compact object `E` of `D(A, d)` only sees
finitely many degrees: there is a bounded interval `[a, b]` of integers such that every object
whose cohomology vanishes throughout `[a, b]` receives only the zero morphism from `E`.

The argument is the one of [Stacks, Tag 09RA] in the form that does not pass through the
classification of compact objects. If no interval worked, one could choose for every `n` an
object `Mₙ` with vanishing cohomology on `[-n, n]` and a nonzero map `E ⟶ Mₙ`. In each fixed
degree only finitely many of the `Mₙ` then have nonvanishing cohomology, which makes the
canonical map `⨁ₙ Mₙ ⟶ ∏ₙ Mₙ` a quasi-isomorphism; so the maps `E ⟶ Mₙ`, which assemble into a
single map into the product, assemble into a single map into the direct sum, and compactness
forces all but finitely many of them to vanish.

## Main definitions

* `DifferentialGradedModule.directSumComponent`: the `i`-th coordinate of a direct sum of
  differential graded modules, as a homomorphism onto the `i`-th summand.
* `DifferentialGradedModule.directSumToProduct`: the canonical map from the direct sum of a
  family of differential graded modules to its product.

## Main results

* `DifferentialGradedModule.isQuasiIsomorphism_directSumToProduct`: the canonical map from the
  direct sum to the product is a quasi-isomorphism as soon as, in every degree, all but finitely
  many members of the family have vanishing cohomology.
* `DifferentialGradedModule.finite_setOf_ne_zero_of_isCompactObject`: under the same hypothesis,
  a compact object of `D(A, d)` admits only finitely many nonzero morphisms into the members of
  the family.
* `DifferentialGradedModule.exists_subsingleton_hom_of_isZero_homology`: **Tag 09RA**, the finite
  cohomological detection window of a compact object.

## Implementation notes

The direct sum of a family of differential graded modules carries the direct sum `⨁ᵢ (f i).M` of
the carriers, while the product carries a submodule of `∏ᵢ (f i).M`, so the canonical map between
them is not an inclusion of two submodules of one ambient module. It is obtained instead from the
universal property of the product applied to the coordinate maps out of the direct sum, which
makes its components available by `DifferentialGradedModule.product.π_lift_apply` and keeps every
subsequent argument componentwise.

Quasi-isomorphy is checked against the cycle-and-boundary criterion
`DifferentialGradedModule.IsQuasiIsomorphism`, which is stated on homogeneous elements and so can
be verified one coordinate at a time. Only one half uses the cohomological finiteness hypothesis:
a cocycle of the product differs by a boundary from a cocycle supported on the finitely many
coordinates with nonvanishing cohomology. The other half needs no hypothesis, because an element
of the product bounding a cocycle of the direct sum may be truncated to the finite support of
that cocycle.

As in `StacksFrontier/Algebra/DifferentialGraded/Module/Product.lean`, the carrier of a product and
the carrier of a direct sum agree with the honest types `↥(productSubmodule f)` and
`⨁ᵢ (f i).M` only by unfolding at default transparency, so points of them are written at the
honest type whenever a coordinate has to be read off.

Vanishing of a `Hom` group is recorded as `Subsingleton` of the morphism type, which is the form
that transfers along isomorphisms of the target without naming a zero element.

## References

* [Stacks Project, Tag 09RA](https://stacks.math.columbia.edu/tag/09RA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

namespace DifferentialGradedModule

universe u v₁ u₁

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-! ### Cohomology and boundaries -/

/-- If the degree-`n` cohomology of a differential graded module vanishes, every homogeneous
cocycle of degree `n` is the boundary of a homogeneous element of degree `n - 1`. -/
theorem exists_d_eq_of_isZero_homology (M : DifferentialGradedModule.{u, u, u} A)
    (n : ℤ) (h : IsZero (M.toCochainComplex.homology n))
    (x : M.M) (hx : x ∈ M.grading n) (hdx : M.d x = 0) :
    ∃ y : M.M, y ∈ M.grading (n - 1) ∧ M.d y = x := by
  have he' := (M.toCochainComplex.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)).mp
    ((M.toCochainComplex.exactAt_iff_isZero_homology n).mpr h)
  rw [ShortComplex.moduleCat_exact_iff] at he'
  obtain ⟨y, hy⟩ := he' (show M.grading n from ⟨x, hx⟩) (by
    apply Subtype.ext
    change ((M.toCochainComplex.d n (n + 1)) (show M.grading n from ⟨x, hx⟩) :
      M.grading (n + 1)).val = (0 : M.grading (n + 1)).val
    rwa [toCochainComplex_d_val M n (n + 1) rfl])
  refine ⟨(show M.grading (n - 1) from y).val, y.property, ?_⟩
  have hval := congrArg Subtype.val hy
  change ((M.toCochainComplex.d (n - 1) n) (show M.grading (n - 1) from y) :
    M.grading n).val = x at hval
  rwa [toCochainComplex_d_val M (n - 1) n (by omega)] at hval

/-! ### The canonical map from a direct sum to a product -/

section DirectSumToProduct

variable {ι : Type u} [DecidableEq ι] (f : ι → DifferentialGradedModule.{u, u, u} A)

/-- The `i`-th coordinate `⨁ⱼ f j ⟶ f i` of a direct sum of differential graded modules. Unlike
the `i`-th projection of a product it is not part of a limit cone; it is used to assemble the
canonical map from the direct sum to the product. -/
def directSumComponent (i : ι) : directSumObj f ⟶ f i where
  toFun := DirectSum.component R ι (fun j => (f j).M) i
  map_smul x a := (DirectSum.smul_apply (MulOpposite.op a) x i).trans rfl
  map_grading _ _ hx := hx i
  map_d := LinearMap.ext fun x => directSumD_apply f x i

/-- The `i`-th coordinate of a direct sum reads off the `i`-th component. -/
theorem directSumComponent_apply (i : ι) (x : ⨁ j, (f j).M) :
    (directSumComponent f i).toFun x = x i :=
  rfl

/-- **The canonical map `⨁ᵢ f i ⟶ ∏ᵢ f i`** from the direct sum of a family of differential
graded modules to its product: the lift of the coordinate maps out of the direct sum. -/
noncomputable def directSumToProduct : directSumObj f ⟶ product f :=
  product.lift f (directSumComponent f)

/-- The canonical map from the direct sum to the product has the coordinate maps as its
components. -/
@[simp] theorem product_π_directSumToProduct (i : ι) :
    directSumToProduct f ≫ product.π f i = directSumComponent f i :=
  product.π_lift f (directSumComponent f) i

/-- Composing the `i`-th coprojection into the direct sum with the canonical map to the product
and then with the `j`-th projection gives zero when `j ≠ i`. -/
theorem directSumInj_directSumToProduct_product_π (i j : ι) (hij : j ≠ i) :
    directSumInj f i ≫ directSumToProduct f ≫ product.π f j = 0 := by
  rw [product_π_directSumToProduct]
  refine Hom.ext (LinearMap.ext fun x => ?_)
  change (DirectSum.lof R ι (fun k => (f k).M) i x) j = 0
  rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hij]

omit [DecidableEq ι] in
/-- A projection of the product intertwines the differentials. -/
private theorem product_π_d (i : ι) (y : (product f).M) :
    (product.π f i).toFun ((product f).d y) = (f i).d ((product.π f i).toFun y) :=
  LinearMap.congr_fun (product.π f i).map_d y

/-- Applying the canonical map to the product and reading off the `i`-th coordinate is the `i`-th
coordinate map of the direct sum. -/
@[simp] theorem product_π_directSumToProduct_apply (i : ι) (x : (directSumObj f).M) :
    (product.π f i).toFun ((directSumToProduct f).toFun x)
      = (directSumComponent f i).toFun x :=
  rfl

/-- A finitely supported family of homogeneous elements of degree `n` is homogeneous of degree
`n` in the direct sum. -/
private theorem mk_mem_directSumGrading (n : ℤ) (s : Finset ι) (u : ∀ i, (f i).M)
    (hu : ∀ i, u i ∈ (f i).grading n) :
    DFinsupp.mk (β := fun j => (f j).M) s (fun j : s => u j.1) ∈ directSumGrading f n :=
  (mem_directSumGrading ..).2 fun i => by by_cases hi : i ∈ s <;> simp [hi, hu i]

/-- The differential of a finitely supported family, when its coordinates are known. -/
private theorem directSumD_mk (s : Finset ι) (u : ∀ i, (f i).M) (v : ⨁ j, (f j).M)
    (hs : ∀ i ∈ s, (f i).d (u i) = v i) (hv : ∀ i ∉ s, v i = 0) :
    directSumD f (DFinsupp.mk (β := fun j => (f j).M) s fun j : s => u j.1) = v :=
  DFinsupp.ext fun i => by by_cases hi : i ∈ s <;> simp [directSumD_apply, hi, hs, hv]

/-- The cocycle half of the cycle-and-boundary criterion for the canonical map from the direct sum
to the product: a homogeneous cocycle of the product is, modulo a boundary, the image of the
cocycle of the direct sum supported on the finitely many coordinates whose cohomology does not
vanish. -/
private theorem directSumToProduct_cocycle_aux (n : ℤ) (s : Finset ι) (y : (product f).M)
    (hy : ∀ i, (product.π f i).toFun y ∈ (f i).grading n)
    (hdy : ∀ i, (f i).d ((product.π f i).toFun y) = 0)
    (hs : ∀ i ∉ s, IsZero ((f i).toCochainComplex.homology n)) :
    ∃ x : ⨁ j, (f j).M, x ∈ directSumGrading f n ∧ directSumD f x = 0 ∧
      ∃ z : (product f).M, z ∈ (product f).grading (n - 1) ∧
        (product f).d z = y - (directSumToProduct f).toFun x := by
  have hb : ∀ i, ∃ w : (f i).M, w ∈ (f i).grading (n - 1) ∧
      (f i).d w = if i ∈ s then 0 else (product.π f i).toFun y := by
    intro i
    by_cases hi : i ∈ s
    · exact ⟨0, Submodule.zero_mem _, by simp [hi]⟩
    · obtain ⟨w, hw, hwd⟩ := exists_d_eq_of_isZero_homology (f i) n (hs i hi)
        ((product.π f i).toFun y) (hy i) (hdy i)
      exact ⟨w, hw, by simp [hi, hwd]⟩
  choose w hw hwd using hb
  obtain ⟨z, hz, hzπ⟩ := product.exists_mem_grading f (n - 1) w hw
  refine ⟨DFinsupp.mk (β := fun j => (f j).M) s fun j : s => (product.π f j.1).toFun y,
    mk_mem_directSumGrading f n s _ hy, ?_, z, hz, ?_⟩
  · exact directSumD_mk f s _ 0 (fun i _ => hdy i) fun _ _ => rfl
  · refine product.eq_of_π_eq f fun i => ?_
    rw [product_π_d, hzπ, hwd, map_sub, product_π_directSumToProduct_apply,
      directSumComponent_apply, DFinsupp.mk_apply]
    by_cases hi : i ∈ s <;> simp [hi]

/-- The boundary half of the cycle-and-boundary criterion for the canonical map from the direct
sum to the product: an element of the product bounding a cocycle of the direct sum may be
truncated to the finite support of that cocycle, and bounds it there. -/
private theorem directSumToProduct_boundary_aux (n : ℤ) (x : ⨁ j, (f j).M) (z : (product f).M)
    (hz : z ∈ (product f).grading (n - 1))
    (hzd : ∀ i, (f i).d ((product.π f i).toFun z) = x i) :
    ∃ v : ⨁ j, (f j).M, v ∈ directSumGrading f (n - 1) ∧ directSumD f v = x := by
  classical
  have hzg : ∀ i, (product.π f i).toFun z ∈ (f i).grading (n - 1) :=
    (product.mem_grading_iff f z).1 hz
  refine ⟨DFinsupp.mk (β := fun j => (f j).M) (DFinsupp.support x)
    fun j : DFinsupp.support x => (product.π f j.1).toFun z,
    mk_mem_directSumGrading f (n - 1) _ _ hzg, ?_⟩
  exact directSumD_mk f _ _ x (fun i _ => hzd i) fun _ => DFinsupp.notMem_support_iff.mp

/-- **The canonical map from the direct sum to the product is a quasi-isomorphism** when, in every
degree, all but finitely many members of the family have vanishing cohomology.

In each degree, a cocycle of the product is the sum of its restriction to the finitely many
coordinates with nonvanishing cohomology — which is a cocycle of the direct sum — and a boundary;
and a cocycle of the direct sum which bounds in the product bounds in the direct sum already,
because the bounding element may be truncated to the finite support of the cocycle. -/
theorem isQuasiIsomorphism_directSumToProduct
    (h : ∀ n : ℤ, ∃ s : Finset ι, ∀ i ∉ s, IsZero ((f i).toCochainComplex.homology n)) :
    IsQuasiIsomorphism (directSumToProduct f) := by
  intro n
  obtain ⟨s, hs⟩ := h n
  refine ⟨fun y hy hdy => ?_, fun x hx hdx hbnd => ?_⟩
  · exact directSumToProduct_cocycle_aux f n s y ((product.mem_grading_iff f y).1 hy)
      (fun i => by rw [← product_π_d, hdy, map_zero]) hs
  · obtain ⟨z, hz, hzd⟩ := hbnd
    exact directSumToProduct_boundary_aux f n x z hz
      (fun i => by rw [← product_π_d, hzd]; rfl)

/-- The canonical map from the direct sum to the product becomes an isomorphism in the derived
category when, in every degree, all but finitely many members of the family have vanishing
cohomology. -/
theorem isIso_q_map_directSumToProduct
    (h : ∀ n : ℤ, ∃ s : Finset ι, ∀ i ∉ s, IsZero ((f i).toCochainComplex.homology n)) :
    IsIso ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (directSumToProduct f)) :=
  isIso_q_map_of_isQuasiIsomorphism _ (isQuasiIsomorphism_directSumToProduct f h)

end DirectSumToProduct

/-! ### Finitely many nonzero maps out of a compact object -/

/-- In a preadditive category, a compact object admits only finitely many nonzero morphisms into
the members of a family which has both a direct sum and a product and whose comparison map
between them is an isomorphism.

The morphisms assemble into a single morphism into the product, which transports to the direct
sum and there factors through a finite subsum; the coordinates outside that subsum are killed by
the vanishing of the crossed composites. -/
private lemma finite_setOf_ne_zero_of_isColimit_of_isLimit {D : Type u₁} [Category.{v₁} D]
    [Preadditive D] {ι : Type u} {X : ι → D} {S T E : D}
    (hE : IsCompactObject.{u} E) (j : ∀ i, X i ⟶ S) (p : ∀ i, T ⟶ X i) (q : S ⟶ T) [IsIso q]
    (hc : IsColimit (Cofan.mk S j)) (hp : IsLimit (Fan.mk T p))
    (hcross : ∀ i k, k ≠ i → j i ≫ q ≫ p k = 0)
    (g : ∀ i, E ⟶ X i) : {i | g i ≠ 0}.Finite := by
  classical
  obtain ⟨d, hd⟩ := (CategoryTheory.bijective_cofanMap E hE j hc).surjective
    (hp.lift (Fan.mk E g) ≫ inv q)
  have hsum : hp.lift (Fan.mk E g) ≫ inv q = ∑ i ∈ d.support, d i ≫ j i := by
    rw [← hd]
    conv_lhs => rw [← DirectSum.sum_support_of d]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => CategoryTheory.cofanMap_of E j i (d i)
  refine d.support.finite_toSet.subset fun k hk => ?_
  by_contra hnot
  refine hk ?_
  have hfac : (hp.lift (Fan.mk E g) ≫ inv q) ≫ q ≫ p k = g k := by
    rw [Category.assoc, IsIso.inv_hom_id_assoc]
    exact hp.fac (Fan.mk E g) (Discrete.mk k)
  rw [← hfac, hsum, Preadditive.sum_comp]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Category.assoc, hcross i k (fun hik => hnot (hik ▸ hi)), comp_zero]

/-- A compact object of `D(A, d)` admits only finitely many nonzero morphisms into a family of
differential graded modules which, in every degree, has only finitely many members with
nonvanishing cohomology.

The direct sum and the product of the family agree in `D(A, d)` under that hypothesis
(`DifferentialGradedModule.isIso_q_map_directSumToProduct`), the images of both are a direct sum
and a product there (**Tag 09QI**), and a compact object only maps into a finite subsum. -/
theorem finite_setOf_ne_zero_of_isCompactObject {ι : Type u}
    (f : ι → DifferentialGradedModule.{u, u, u} A)
    (h : ∀ n : ℤ, ∃ s : Finset ι, ∀ i ∉ s, IsZero ((f i).toCochainComplex.homology n))
    (E : derivedCategory' A) [IsCompactObject.{u} E]
    (g : ∀ i, E ⟶ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (f i)) :
    {i | g i ≠ 0}.Finite := by
  classical
  have : IsIso ((toHomotopyCategory.{u, u, u} A ⋙ (quasiIsomorphisms' A).Q).map
    (directSumToProduct f)) := isIso_q_map_directSumToProduct f h
  refine finite_setOf_ne_zero_of_isColimit_of_isLimit ‹IsCompactObject.{u} E›
    (fun i => (toHomotopyCategory.{u, u, u} A ⋙ (quasiIsomorphisms' A).Q).map
      (directSumInj f i))
    (fun i => (toHomotopyCategory.{u, u, u} A ⋙ (quasiIsomorphisms' A).Q).map (product.π f i))
    ((toHomotopyCategory.{u, u, u} A ⋙ (quasiIsomorphisms' A).Q).map (directSumToProduct f))
    ((isColimitMapCoconeCofanMkEquiv _ f (directSumInj f))
      (isColimitOfPreserves _ (isColimit_directSumObj f)))
    ((isLimitMapConeFanMkEquiv _ f (product.π f)) (isLimit_q_mapCone_product f))
    (fun i k hik => ?_) g
  rw [← Functor.map_comp, ← Functor.map_comp,
    directSumInj_directSumToProduct_product_π f i k hik, Functor.map_zero]

/-! ### The detection window -/

/-- **Stacks Tag 09RA.** For every compact object `E` of the derived category of a differential
graded algebra there are integers `a ≤ b` such that `Hom_{D(A, d)}(E, M) = 0` for every object `M`
whose cohomology `Hⁱ(M)` vanishes for all `i ∈ [a, b]`.

If no such interval existed, then for each `n` there would be an object `Mₙ` with vanishing
cohomology on `[-n, n]` and a nonzero morphism `E ⟶ Mₙ`. In each fixed degree only finitely many
of the `Mₙ` have nonvanishing cohomology, so
`DifferentialGradedModule.finite_setOf_ne_zero_of_isCompactObject` applies to the family and
contradicts the fact that all of the chosen morphisms are nonzero. -/
@[stacks 09RA]
theorem exists_subsingleton_hom_of_isZero_homology (A : DifferentialGradedAlgebra.{u, u} R)
    (E : derivedCategory' A) [IsCompactObject.{u} E] :
    ∃ a b : ℤ, a ≤ b ∧ ∀ M : derivedCategory' A,
      (∀ i : ℤ, a ≤ i → i ≤ b → IsZero (M.as.obj.as.toCochainComplex.homology i)) →
        Subsingleton (E ⟶ M) := by
  classical
  by_contra hcon
  have hex (n : ℕ) : ∃ M : derivedCategory' A,
      (∀ i : ℤ, -(n : ℤ) ≤ i → i ≤ n → IsZero (M.as.obj.as.toCochainComplex.homology i)) ∧
      ∃ g : E ⟶ M, g ≠ 0 := by
    by_contra! hn
    exact hcon ⟨-(n : ℤ), n, by omega, fun M hM =>
      ⟨fun p q => (hn M hM p).trans (hn M hM q).symm⟩⟩
  choose M hM g hg using hex
  let f : ULift.{u} ℕ → DifferentialGradedModule.{u, u, u} A := fun i => (M i.down).as.obj.as
  have hcoh : ∀ n : ℤ, ∃ s : Finset (ULift.{u} ℕ),
      ∀ i ∉ s, IsZero ((f i).toCochainComplex.homology n) := by
    intro n
    refine ⟨(Finset.range n.natAbs).map ⟨ULift.up, ULift.up_injective⟩, fun i hi => ?_⟩
    have hn : n.natAbs ≤ i.down := by
      by_contra hn
      exact hi (Finset.mem_map.mpr
        ⟨i.down, Finset.mem_range.mpr (by omega), by cases i; rfl⟩)
    exact hM i.down n (by omega) (by omega)
  exact Set.infinite_univ
    ((finite_setOf_ne_zero_of_isCompactObject f hcoh E fun i => g i.down).subset
      fun i _ => hg i.down)

end DifferentialGradedModule

end
