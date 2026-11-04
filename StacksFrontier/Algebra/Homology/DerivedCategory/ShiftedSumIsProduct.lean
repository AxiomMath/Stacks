module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationTower
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts

/-!
# A sum of objects concentrated in strictly decreasing degrees is their product

Let `A` be an abelian category and let `family : ℕ → D(A)` be a family of objects of its
unbounded derived category with `family n` concentrated in degree `-n`, that is
`(family n).IsGE (-n)` and `(family n).IsLE (-n)`.  The archetype is `family n = ℱ_n[n]` for a
family of objects `ℱ_n` of `A`.

This file proves that the canonical map

`∐ family ⟶ ∏ family`

— `Pi.lift (Sigma.π family)`, the map whose component from the `m`-th summand to the `n`-th
factor is `1` for `m = n` and `0` otherwise — is an isomorphism, *given* that `∐ family` is the
derived limit of the tower of its canonical truncations in the strong sense that the Milnor
triangle based at `∐ family` itself is distinguished.  That input is the content of
**Stacks 08IY** and is not proved here: on the big fppf site of an algebraic stack it is
`AlgebraicGeometry.Stack.isIso_to_isDerivedLimit_truncGETower_of_lqcFbc` composed with
`Stacks.InverseSystem.exists_distTriang_milnor_of_isIso`.  Everything else is unconditional.

## Main results

* `Stacks.ShiftedSum.isLimit_coproductFan_of_finite`: in a preadditive category a finite
  coproduct, with the Kronecker projections `Sigma.π`, is a product.
* `Stacks.ShiftedSum.isLimit_fan_of_split_product_tower`: if an object sits in the Milnor
  triangle of a tower of partial products of a family whose transition maps split, then it is a
  product of the family.
* `Stacks.ShiftedSum.isLimit_truncGE_coproductFan`: `τ_{≥ -N}(∐ family)` is a product of
  `(family n)_{n ≤ N}`.
* `Stacks.ShiftedSum.homologyCoproductIso` and
  `Stacks.ShiftedSum.isZero_homologyCoproduct_of_pos`: the cohomology objects of `∐ family` are
  `H^{-n}(∐ family) = H^{-n}(family n)` and `H^q(∐ family) = 0` for `q > 0`.
* `Stacks.ShiftedSum.isIso_piLift_sigmaPi_of_distTriang_truncation`: the canonical map
  `∐ family ⟶ ∏ family` is an isomorphism.

## Implementation notes

The family is indexed by `ℕ`, with `family n` in degree `-n`, because that is what keeps the
finite sums finite.  For a family indexed by `ℤ` the same statement holds, but those sums
are infinite and the identification of `∐_{n ≤ N}` with `∏_{n ≤ N}` has to be made on
K-injective resolutions, where it holds because such a family of resolutions has, in each
cohomological degree, only finitely many nonzero terms.  That generalization is not carried out
here.

The (co)products used are taken as instance arguments rather than derived from
`Stacks.Injectives.hasCoproducts_derivedCategory` and
`Stacks.Injectives.hasProducts_derivedCategory`, because those produce `HasCoproducts.{w}` for
the universe `w` of `IsGrothendieckAbelian.{w} A`, whereas the index types here live in `Type 0`;
`CategoryTheory.Limits.hasCoproducts_shrink` bridges that at the point of use.

This applies to an abstract abelian `A`, as here.  Over `SheafOfModules` on a site the
universes collapse and the two instances above apply directly, since
`Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck` provides `IsGrothendieckAbelian`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.ShiftedSum

universe w v u

/-! ### Finite sums are products -/

section Finite

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **A finite coproduct in a preadditive category is a product**, with the Kronecker
projections `CategoryTheory.Limits.Sigma.π` as its projections. -/
def isLimit_coproductFan_of_finite {I : Type w} [Finite I] [DecidableEq I] (L : I → C)
    [HasCoproduct L] : IsLimit (Fan.mk (∐ L) (Sigma.π L)) := by
  classical
  have : Fintype I := Fintype.ofFinite I
  refine Fan.IsLimit.mk _ (fun cone => ∑ i : I, cone.proj i ≫ Sigma.ι L i) ?_ ?_
  · intro cone i
    change (∑ j : I, cone.proj j ≫ Sigma.ι L j) ≫ Sigma.π L i = cone.proj i
    rw [Preadditive.sum_comp, Finset.sum_eq_single i]
    · simp
    · intro j _ hne
      simp [Category.assoc, Sigma.ι_π_of_ne L hne]
    · simp
  · intro cone morphism hmorphism
    change ∀ i, morphism ≫ Sigma.π L i = cone.proj i at hmorphism
    have htotal : (∑ i : I, Sigma.π L i ≫ Sigma.ι L i) = 𝟙 (∐ L) := by
      apply Sigma.hom_ext
      intro i
      rw [Preadditive.comp_sum, Finset.sum_eq_single i]
      · simp
      · intro j _ hne
        rw [← Category.assoc, Sigma.ι_π_of_ne L (Ne.symm hne), zero_comp]
      · simp
    calc
      morphism = morphism ≫ (∑ i : I, Sigma.π L i ≫ Sigma.ι L i) := by
        rw [htotal]; exact (Category.comp_id morphism).symm
      _ = ∑ i : I, cone.proj i ≫ Sigma.ι L i := by
        rw [Preadditive.comp_sum]
        simp only [← Category.assoc, hmorphism]

/-- A coproduct all of whose summands but one are zero is that summand, by the Kronecker
projection and inclusion at that index. -/
def coproductIsoOfUniqueSupport {I : Type w} [DecidableEq I] (L : I → C) [HasCoproduct L]
    (i : I) (hzero : ∀ j, j ≠ i → IsZero (L j)) : (∐ L) ≅ L i where
  hom := Sigma.π L i
  inv := Sigma.ι L i
  hom_inv_id := by
    apply Sigma.hom_ext
    intro j
    by_cases hj : j = i
    · subst j; simp
    · exact (hzero j hj).eq_of_src _ _
  inv_hom_id := by simp

end Finite

/-! ### A split tower of partial products -/

section SplitTower

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ degree : ℤ, (shiftFunctor C degree).Additive] [Pretriangulated C]

omit [HasZeroObject C] [HasShift C ℤ] [∀ degree : ℤ, (shiftFunctor C degree).Additive]
  [Pretriangulated C] in
/-- **The Milnor difference map of a tower with sections is a split epimorphism**, in the
explicit form of a solution of `x_N - x_{N+1} ∘ t_N = y_N` for a prescribed `y`. -/
theorem exists_difference_solution_of_sections (objects : ℕ → C)
    (transition : ∀ N, objects (N + 1) ⟶ objects N)
    (sections : ∀ N, objects N ⟶ objects (N + 1))
    (hsections : ∀ N, sections N ≫ transition N = 𝟙 _)
    {source : C} (legs : ∀ N, source ⟶ objects N) :
    ∃ solution : ∀ N, source ⟶ objects N,
      ∀ N, solution N - solution (N + 1) ≫ transition N = legs N := by
  refine ⟨Nat.rec 0 (fun N previous => (previous - legs N) ≫ sections N), ?_⟩
  intro N
  show _ - ((_ - legs N) ≫ sections N) ≫ transition N = legs N
  rw [Category.assoc, hsections, Category.comp_id, sub_sub_cancel]

/-- **An object sitting in the Milnor triangle of a tower of partial products of a family, whose
transition maps are split epimorphisms, is a product of the family.**

The data is: a family `family : ℕ → C`; for each `N` a fan `fans N` on the partial family
`(family n)_{n ≤ N}` which is a limit, with vertex `objects N`; transition maps of the tower
compatible with the projections and admitting sections; and an object `source` with a cone
`legs` over the tower whose composites with the projections are maps `coordinates`, sitting in
the Milnor triangle of the tower.

The conclusion is that `source` with `coordinates` is a product of the whole family. -/
def isLimit_fan_of_split_product_tower (family : ℕ → C)
    (objects : ℕ → C)
    (fans : ∀ N : ℕ, Fan fun i : {n : ℕ // n ≤ N} => family i.val)
    (hobjects : ∀ N, (fans N).pt = objects N)
    (hlimit : ∀ N, IsLimit (fans N))
    (transition : ∀ N, objects (N + 1) ⟶ objects N)
    (sections : ∀ N, objects N ⟶ objects (N + 1))
    (hsections : ∀ N, sections N ≫ transition N = 𝟙 _)
    (projection : ∀ N : ℕ, ∀ i : {n : ℕ // n ≤ N}, objects N ⟶ family i.val)
    (hprojection : ∀ N i,
      projection N i = eqToHom (hobjects N).symm ≫ (fans N).proj i)
    (htransition : ∀ N i,
      transition N ≫ projection N i = projection (N + 1) ⟨i.val, i.property.trans (Nat.le_succ N)⟩)
    [HasProduct objects] (source : C) (legs : ∀ N, source ⟶ objects N)
    (coordinates : ∀ n, source ⟶ family n)
    (hlegs : ∀ N i, legs N ≫ projection N i = coordinates i.val)
    (connecting : (∏ᶜ objects) ⟶ source⟦(1 : ℤ)⟧)
    (htriangle : Triangle.mk (Pi.lift legs)
      (Pi.lift fun N => Pi.π objects N - Pi.π objects (N + 1) ≫ transition N)
      connecting ∈ distTriang C) :
    IsLimit (Fan.mk source coordinates) := by
  classical
  let difference : (∏ᶜ objects) ⟶ ∏ᶜ objects :=
    Pi.lift (fun N => Pi.π objects N - Pi.π objects (N + 1) ≫ transition N)
  let existence := exists_difference_solution_of_sections objects transition
    sections hsections (Pi.π objects)
  let solution := existence.choose
  have hsolution := existence.choose_spec
  have hsection : Pi.lift solution ≫ difference = 𝟙 _ := by
    apply Pi.hom_ext
    intro N
    simpa [difference, Preadditive.comp_sub] using hsolution N
  have hepi : Epi difference := (IsSplitEpi.mk' ⟨Pi.lift solution, hsection⟩).epi
  let triangle := Triangle.mk (Pi.lift legs) difference connecting
  have hdist : triangle ∈ distTriang C := htriangle
  have hconnecting : connecting = 0 :=
    (Triangle.mor₃_eq_zero_iff_epi₂ triangle hdist).mpr hepi
  have hmono : Mono (Pi.lift legs) :=
    (Triangle.mor₃_eq_zero_iff_mono₁ triangle hdist).mp hconnecting
  let stageLift (cone : Fan family) (N : ℕ) : cone.pt ⟶ objects N :=
    (hlimit N).lift (Fan.mk cone.pt (fun i => cone.proj i.val)) ≫ eqToHom (hobjects N)
  have stageLift_fac (cone : Fan family) (N : ℕ) (i) :
      stageLift cone N ≫ projection N i = cone.proj i.val := by
    rw [hprojection]
    dsimp only [stageLift]
    simp
  have stage_ext (N : ℕ) {domain : C} (first second : domain ⟶ objects N)
      (heq : ∀ i, first ≫ projection N i = second ≫ projection N i) : first = second := by
    apply (cancel_mono (eqToHom (hobjects N).symm)).mp
    apply (hlimit N).hom_ext
    rintro ⟨i⟩
    change (first ≫ eqToHom (hobjects N).symm) ≫ (fans N).proj i =
      (second ≫ eqToHom (hobjects N).symm) ≫ (fans N).proj i
    simp only [Category.assoc]
    rw [← hprojection]
    exact heq i
  have compatibility (cone : Fan family) (N : ℕ) :
      stageLift cone (N + 1) ≫ transition N = stageLift cone N := by
    apply stage_ext
    intro i
    rw [Category.assoc, htransition, stageLift_fac, stageLift_fac]
  have kernel_condition (cone : Fan family) :
      Pi.lift (stageLift cone) ≫ difference = 0 := by
    apply Pi.hom_ext
    intro N
    simp [difference, Preadditive.comp_sub, compatibility]
  choose lift hlift using fun cone : Fan family =>
    Triangle.coyoneda_exact₂ triangle hdist (Pi.lift (stageLift cone)) (kernel_condition cone)
  refine Fan.IsLimit.mk _ lift ?_ ?_
  · intro cone n
    calc
      lift cone ≫ coordinates n
          = lift cone ≫ legs n ≫ projection n ⟨n, le_rfl⟩ := by rw [hlegs]
      _ = cone.proj n := by
        have heq := congrArg (fun morphism => morphism ≫ Pi.π objects n) (hlift cone)
        simp only [triangle, Triangle.mk_mor₁, Pi.lift_π, Category.assoc] at heq
        rw [← Category.assoc, ← heq, stageLift_fac]
  · intro cone morphism hmorphism
    change ∀ n, morphism ≫ coordinates n = cone.proj n at hmorphism
    apply (cancel_mono (Pi.lift legs)).mp
    have heq := hlift cone
    change Pi.lift (stageLift cone) = lift cone ≫ Pi.lift legs at heq
    calc
      morphism ≫ Pi.lift legs = Pi.lift (stageLift cone) := by
        apply Pi.hom_ext
        intro N
        simp only [Category.assoc, Pi.lift_π]
        apply stage_ext
        intro i
        rw [Category.assoc, hlegs, stageLift_fac]
        exact hmorphism i.val
      _ = lift cone ≫ Pi.lift legs := heq

end SplitTower

/-! ### The truncations of a sum of objects in strictly decreasing degrees -/

section Truncation

universe m

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The vertex of a limit fan on a family of objects bounded below in degree `n` is bounded
below in degree `n`. -/
theorem isGE_of_isLimit_fan {I : Type*} (L : I → DerivedCategory A) (c : Fan L)
    (hc : IsLimit c) (n : ℤ) (hL : ∀ i, (L i).IsGE n) : c.pt.IsGE n := by
  apply (DerivedCategory.TStructure.t.isGE_iff_orthogonal (n - 1) n (by omega) _).mpr
  intro source morphism hsource
  apply hc.hom_ext
  rintro ⟨i⟩
  show morphism ≫ c.proj i = 0 ≫ c.proj i
  simpa using DerivedCategory.TStructure.t.zero_of_isLE_of_isGE
    (morphism ≫ c.proj i) (n - 1) n (by omega) hsource (hL i)

/-- The index type of a partial sum is finite. -/
instance finite_le_nat (N : ℕ) : Finite {n : ℕ // n ≤ N} :=
  Finite.of_injective (fun i : {n : ℕ // n ≤ N} => (⟨i.1, Nat.lt_succ_of_le i.2⟩ : Fin (N + 1)))
    fun _ _ hab => Subtype.ext (by simpa using hab)

/-- **The canonical truncation of a sum of objects in strictly decreasing degrees is the
corresponding partial sum, and that partial sum is a product.**

For `family n` concentrated in degree `-n`, the truncation `τ_{≥ -N}(∐ family)` is a product of
`(family n)_{n ≤ N}`, with projections the maps `descTruncGE (Sigma.π family n)` factoring the
Kronecker projections through the truncation. -/
def isLimit_truncGE_coproductFan (family : ℕ → DerivedCategory A) (N : ℕ)
    (hge : ∀ n : ℕ, (family n).IsGE (-(n : ℤ)))
    (hle : ∀ n : ℕ, (family n).IsLE (-(n : ℤ)))
    [HasCoproduct family] [HasCoproduct fun i : {n : ℕ // n ≤ N} => family i.val] :
    IsLimit (Fan.mk ((DerivedCategory.TStructure.t.truncGE (-(N : ℤ))).obj (∐ family))
      (fun i : {n : ℕ // n ≤ N} =>
        haveI := hge i.val
        haveI := DerivedCategory.TStructure.t.isGE_of_ge (family i.val) (-(N : ℤ))
          (-(i.val : ℤ)) (by have := i.property; omega)
        DerivedCategory.TStructure.t.descTruncGE (Sigma.π family i.val) (-(N : ℤ)))) := by
  classical
  let restricted := fun i : {n : ℕ // n ≤ N} => family i.val
  let projection := Sigma.desc (fun n : ℕ =>
    if hn : n ≤ N then Sigma.ι restricted ⟨n, hn⟩ else 0)
  have hpartial : IsLimit (Fan.mk (∐ restricted) (Sigma.π restricted)) :=
    isLimit_coproductFan_of_finite restricted
  haveI hcomponentGE (i : {n : ℕ // n ≤ N}) : (family i.val).IsGE (-(N : ℤ)) := by
    have := hge i.val
    exact DerivedCategory.TStructure.t.isGE_of_ge _ (-(N : ℤ)) (-(i.val : ℤ))
      (by have := i.property; omega)
  haveI hpartialGE : (∐ restricted).IsGE (-(N : ℤ)) :=
    isGE_of_isLimit_fan restricted _ hpartial (-(N : ℤ)) (fun i => hcomponentGE i)
  let inclusion : (∐ restricted) ⟶ ∐ family := Sigma.desc (fun i => Sigma.ι family i.val)
  let truncation := (DerivedCategory.TStructure.t.truncGEπ (-(N : ℤ))).app (∐ family)
  let forward := DerivedCategory.TStructure.t.descTruncGE projection (-(N : ℤ))
  let backward := inclusion ≫ truncation
  have hleft : backward ≫ forward = 𝟙 (∐ restricted) := by
    dsimp only [backward, forward, truncation]
    rw [Category.assoc, DerivedCategory.TStructure.t.π_descTruncGE]
    apply Sigma.hom_ext
    intro i
    simp [inclusion, projection, i.property]
  have hright : forward ≫ backward = 𝟙 _ := by
    apply DerivedCategory.TStructure.t.from_truncGE_obj_ext
    dsimp only [forward]
    rw [← Category.assoc, DerivedCategory.TStructure.t.π_descTruncGE]
    apply Sigma.hom_ext
    intro n
    by_cases hn : n ≤ N
    · simp [projection, backward, inclusion, hn, truncation]
    · have hzero : Sigma.ι family n ≫ truncation = 0 :=
        DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ (-(n : ℤ)) (-(N : ℤ))
          (by omega) (hle n) inferInstance
      simpa [projection, hn] using hzero.symm
  let iso : (DerivedCategory.TStructure.t.truncGE (-(N : ℤ))).obj (∐ family) ≅ ∐ restricted :=
    ⟨forward, backward, hright, hleft⟩
  apply hpartial.ofIsoLimit
  refine Fan.ext iso.symm ?_
  intro i
  change Sigma.π restricted i = backward ≫
    DerivedCategory.TStructure.t.descTruncGE (Sigma.π family i.val) (-(N : ℤ))
  dsimp only [backward, truncation]
  rw [Category.assoc, DerivedCategory.TStructure.t.π_descTruncGE]
  apply Sigma.hom_ext
  intro j
  by_cases hij : j = i
  · subst j; simp [inclusion, restricted]
  · have hne : j.val ≠ i.val := fun hval => hij (Subtype.ext hval)
    simp [inclusion, Sigma.ι_π_of_ne _ hij, Sigma.ι_π_of_ne _ hne]

end Truncation

/-! ### The cohomology of a sum of objects in strictly decreasing degrees -/

section Homology

universe m

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{m} A]

/-- **Cohomology of the unbounded derived category commutes with countable direct sums.** The
localization functor preserves direct sums (**Stacks 07D9**) and so does cohomology of complexes
in a Grothendieck abelian category, where countable direct sums are exact. -/
theorem derivedHomology_preservesCoproducts (index : Type) [Countable index] (degree : ℤ) :
    PreservesColimitsOfShape (Discrete index) (DerivedCategory.homologyFunctor A degree) := by
  let exactSums : HasExactCountableDirectSums A :=
    { hasCoproducts := inferInstance
      exact_colim := fun index _ => by
        let : HasExactColimitsOfShape (Discrete (ULift.{m} index)) A := inferInstance
        let : HasExactColimitsOfShape (Discrete index) A :=
          HasExactColimitsOfShape.of_domain_equivalence A
            (Discrete.equivalence Equiv.ulift)
        exact ⟨inferInstance, inferInstance⟩ }
  let : PreservesColimitsOfShape (Discrete (ULift.{m} index)) (DerivedCategory.Q (C := A)) :=
    Stacks.Injectives.derivedCategoryQ_preservesCoproducts A _
  let : PreservesColimitsOfShape (Discrete index) (DerivedCategory.Q (C := A)) :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  have := homologicalComplex_homologyFunctor_preservesCoproducts A exactSums index degree
  have : PreservesColimitsOfShape (Discrete index)
      (DerivedCategory.Q (C := A) ⋙ DerivedCategory.homologyFunctor A degree) :=
    preservesColimitsOfShape_of_natIso (DerivedCategory.homologyFunctorFactors A degree).symm
  exact preservesColimitsOfShape_discrete_of_essSurj_comp
    (DerivedCategory.Q (C := A)) (DerivedCategory.homologyFunctor A degree) index

/-- A coproduct of zero objects is zero. -/
theorem isZero_coproduct {I : Type*} {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    (L : I → C) [HasCoproduct L] (hL : ∀ i, IsZero (L i)) : IsZero (∐ L) := by
  rw [IsZero.iff_id_eq_zero]
  exact Sigma.hom_ext _ _ fun i => (hL i).eq_of_src _ _

variable (family : ℕ → DerivedCategory A) [HasCoproduct family]

/-- **The cohomology of a sum of objects in strictly decreasing degrees, in degree `-n`, is the
cohomology of the `n`-th summand.** -/
def homologyCoproductIso (hge : ∀ n : ℕ, (family n).IsGE (-(n : ℤ)))
    (hle : ∀ n : ℕ, (family n).IsLE (-(n : ℤ))) (n : ℕ) :
    (DerivedCategory.homologyFunctor A (-(n : ℤ))).obj (∐ family) ≅
      (DerivedCategory.homologyFunctor A (-(n : ℤ))).obj (family n) := by
  classical
  letI := derivedHomology_preservesCoproducts (A := A) ℕ (-(n : ℤ))
  letI : HasColimitsOfShape (Discrete ℕ) A :=
    hasColimitsOfShape_of_equivalence (Discrete.equivalence (Equiv.ulift.{m, 0}))
  have hzero (j : ℕ) (hne : j ≠ n) :
      IsZero ((DerivedCategory.homologyFunctor A (-(n : ℤ))).obj (family j)) := by
    by_cases hlt : -(n : ℤ) < -(j : ℤ)
    · exact (DerivedCategory.isGE_iff (family j) (-(j : ℤ))).mp (hge j) _ hlt
    · exact (DerivedCategory.isLE_iff (family j) (-(j : ℤ))).mp (hle j) _ (by omega)
  exact (asIso (sigmaComparison (DerivedCategory.homologyFunctor A (-(n : ℤ))) family)).symm ≪≫
    coproductIsoOfUniqueSupport _ n hzero

/-- **A sum of objects in strictly decreasing degrees `≤ 0` has no cohomology in positive
degrees.** -/
theorem isZero_homologyCoproduct_of_pos
    (hle : ∀ n : ℕ, (family n).IsLE (-(n : ℤ))) (q : ℤ) (hq : 0 < q) :
    IsZero ((DerivedCategory.homologyFunctor A q).obj (∐ family)) := by
  classical
  let := derivedHomology_preservesCoproducts (A := A) ℕ q
  let : HasColimitsOfShape (Discrete ℕ) A :=
    hasColimitsOfShape_of_equivalence (Discrete.equivalence (Equiv.ulift.{m, 0}))
  have hzero (j : ℕ) : IsZero ((DerivedCategory.homologyFunctor A q).obj (family j)) :=
    (DerivedCategory.isLE_iff (family j) (-(j : ℤ))).mp (hle j) _ (by omega)
  exact IsZero.of_iso (isZero_coproduct _ hzero)
    (asIso (sigmaComparison (DerivedCategory.homologyFunctor A q) family)).symm

end Homology

/-! ### The comparison map -/

section Main

universe m

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- **The canonical map from a sum of objects in strictly decreasing degrees to their product is
an isomorphism**, given that the sum sits in the Milnor triangle of the tower of its canonical
truncations with the canonical cone as the triangle's first map.

That input is the content of **Stacks 08IY** for the sum. -/
theorem isIso_piLift_sigmaPi_of_distTriang_truncation (family : ℕ → DerivedCategory A)
    (hge : ∀ n : ℕ, (family n).IsGE (-(n : ℤ)))
    (hle : ∀ n : ℕ, (family n).IsLE (-(n : ℤ)))
    [HasCoproduct family] [HasProduct family]
    [∀ N : ℕ, HasCoproduct fun i : {n : ℕ // n ≤ N} => family i.val]
    [HasProduct fun N : ℕ =>
      (DerivedCategory.TStructure.t.truncGE (-(N : ℤ))).obj (∐ family)]
    (connecting : (∏ᶜ fun N : ℕ =>
        (DerivedCategory.TStructure.t.truncGE (-(N : ℤ))).obj (∐ family)) ⟶
      (∐ family)⟦(1 : ℤ)⟧)
    (htriangle : Triangle.mk
        (Pi.lift fun N : ℕ =>
          (DerivedCategory.TStructure.t.truncGEπ (-(N : ℤ))).app (∐ family))
        (Pi.lift fun N : ℕ =>
          Pi.π (fun N : ℕ =>
            (DerivedCategory.TStructure.t.truncGE (-(N : ℤ))).obj (∐ family)) N -
          Pi.π (fun N : ℕ =>
            (DerivedCategory.TStructure.t.truncGE (-(N : ℤ))).obj (∐ family)) (N + 1) ≫
            (DerivedCategory.TStructure.t.natTransTruncGEOfLE
              (-((N + 1 : ℕ) : ℤ)) (-(N : ℤ)) (by omega)).app (∐ family))
        connecting ∈ distTriang (DerivedCategory A)) :
    IsIso (Pi.lift (Sigma.π family)) := by
  classical
  have hGE : ∀ (N : ℕ) (i : {n : ℕ // n ≤ N}), (family i.val).IsGE (-(N : ℤ)) := by
    intro N i
    have := hge i.val
    exact DerivedCategory.TStructure.t.isGE_of_ge (family i.val) (-(N : ℤ)) (-(i.val : ℤ))
      (by have := i.property; omega)
  let projection (N : ℕ) (i : {n : ℕ // n ≤ N}) :
      (DerivedCategory.TStructure.t.truncGE (-(N : ℤ))).obj (∐ family) ⟶ family i.val :=
    have := hGE N i
    DerivedCategory.TStructure.t.descTruncGE (Sigma.π family i.val) (-(N : ℤ))
  let fans (N : ℕ) :=
    Fan.mk ((DerivedCategory.TStructure.t.truncGE (-(N : ℤ))).obj (∐ family)) (projection N)
  have hlimit (N : ℕ) : IsLimit (fans N) := isLimit_truncGE_coproductFan family N hge hle
  let transition (N : ℕ) :
      (DerivedCategory.TStructure.t.truncGE (-((N + 1 : ℕ) : ℤ))).obj (∐ family) ⟶
        (DerivedCategory.TStructure.t.truncGE (-(N : ℤ))).obj (∐ family) :=
    (DerivedCategory.TStructure.t.natTransTruncGEOfLE
      (-((N + 1 : ℕ) : ℤ)) (-(N : ℤ)) (by omega)).app (∐ family)
  let legs (N : ℕ) :
      (∐ family) ⟶ (DerivedCategory.TStructure.t.truncGE (-(N : ℤ))).obj (∐ family) :=
    (DerivedCategory.TStructure.t.truncGEπ (-(N : ℤ))).app (∐ family)
  have hlegs (N : ℕ) (i : {n : ℕ // n ≤ N}) :
      legs N ≫ projection N i = Sigma.π family i.val := by
    have := hGE N i
    exact DerivedCategory.TStructure.t.π_descTruncGE _ _
  have htransition (N : ℕ) (i : {n : ℕ // n ≤ N}) :
      transition N ≫ projection N i =
        projection (N + 1) ⟨i.val, i.property.trans (Nat.le_succ N)⟩ := by
    have := hGE (N + 1) ⟨i.val, i.property.trans (Nat.le_succ N)⟩
    apply DerivedCategory.TStructure.t.from_truncGE_obj_ext
    dsimp only [transition]
    rw [← Category.assoc, DerivedCategory.TStructure.t.π_natTransTruncGEOfLE_app]
    exact (hlegs N i).trans (hlegs (N + 1) ⟨i.val, i.property.trans (Nat.le_succ N)⟩).symm
  let extended (N : ℕ) : Fan fun i : {n : ℕ // n ≤ N + 1} => family i.val :=
    Fan.mk ((DerivedCategory.TStructure.t.truncGE (-(N : ℤ))).obj (∐ family)) (fun i =>
      if hi : i.val ≤ N then projection N ⟨i.val, hi⟩ else 0)
  let sections (N : ℕ) :
      (DerivedCategory.TStructure.t.truncGE (-(N : ℤ))).obj (∐ family) ⟶
        (DerivedCategory.TStructure.t.truncGE (-((N + 1 : ℕ) : ℤ))).obj (∐ family) :=
    (hlimit (N + 1)).lift (extended N)
  have hsections (N : ℕ) : sections N ≫ transition N = 𝟙 _ := by
    apply (hlimit N).hom_ext
    rintro ⟨i⟩
    show (sections N ≫ transition N) ≫ projection N i = 𝟙 _ ≫ projection N i
    rw [Category.assoc, htransition]
    simpa [sections, fans, extended, i.property] using
      (hlimit (N + 1)).fac (extended N) ⟨⟨i.val, i.property.trans (Nat.le_succ N)⟩⟩
  apply (Fan.nonempty_isLimit_iff_isIso_piLift (Fan.mk (∐ family) (Sigma.π family))).mp
  exact ⟨isLimit_fan_of_split_product_tower family
    (fun N => (DerivedCategory.TStructure.t.truncGE (-(N : ℤ))).obj (∐ family)) fans
    (fun _ => rfl) hlimit transition sections hsections projection (fun _ _ => by simp [fans])
    htransition (∐ family) legs (Sigma.π family) hlegs connecting htriangle⟩

end Main

end Stacks.ShiftedSum

end
