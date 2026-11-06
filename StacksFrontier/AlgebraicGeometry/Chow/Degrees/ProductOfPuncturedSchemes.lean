module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegree
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.LocalizationSequence

/-!
# Zero cycles on products of punctured proper schemes

Work over the base situation `(S, δ)` of chapter 42 of the Stacks Project with vanishing
dimension function, the case `S = Spec(k)` for a field `k`. Let `X 1, …, X n` be proper over
`S`, let `P i : S ⟶ X i` be sections, let `Q i` be points of `X i` whose residue fields have
degree two over the base, and let `U i ⊆ X i` be the complement of `Q i`. The zero cycle of the
product point `P 1 × ⋯ × P n` is then not rationally equivalent to zero on
`U 1 ×_S ⋯ ×_S U n`; this is Stacks 05WK, whose hypotheses there are that the `X i` be smooth
projective geometrically irreducible curves and that the `P i` and `Q i` be a rational point and
a point of residue degree two on each.

The argument is the one of the Stacks Project. The product `Z = X 1 ×_S ⋯ ×_S X n` is proper
over `S`, so zero cycles on `Z` have a degree, and `U 1 ×_S ⋯ ×_S U n` is the open subscheme of
`Z` on which no coordinate is `Q i`. A point of `Z` outside that open subscheme has some
coordinate equal to `Q i`, so its residue field contains `κ(Q i)` and its degree over the base
is even, while the product point has degree one. If the product point were rationally equivalent
to zero on the open subscheme, the localization sequence of Stacks 02RX would make its prime
cycle on `Z` rationally equivalent to a cycle carried by the complement; the degree is constant
on rational equivalence classes, so one would be even.

## Main definitions

* `Stacks.Chow.overProd`, `Stacks.Chow.overProdπ` — the product over the base of a finite family
  of schemes over the base, and its projections.
* `Stacks.Chow.overProdOpensι` — the inclusion of the product of a family of open subschemes
  into the product of the ambient schemes.

## Main results

* `Stacks.Chow.property_piObj_hom` — a multiplicative morphism property stable under base change
  holds for the structure morphism of a finite product over the base.
* `Stacks.Chow.range_overProdOpensι` — the product of a family of open subschemes is the open
  subscheme of the product cut out by the condition that every coordinate lie in its member of
  the family.
* `Stacks.Chow.single_notMem_rationalEquivalences_of_dvd_boundary_residueDegree` — the degree
  criterion: on an open subscheme of a scheme proper over the base, the prime cycle of a point
  of residue degree one is not rationally equivalent to zero as soon as every point of the
  complement has residue degree divisible by an integer which does not divide one.
* `Stacks.Chow.chowClass_overProdOpens_section_ne_zero` — **Stacks 05WK**.

## Implementation notes

The hypotheses of Stacks 05WK enter only through properness of the factors, the existence of the
sections `P i`, and the degrees of the residue fields of the `Q i`, so that is the generality in
which the statement is given: a smooth projective geometrically irreducible curve over a field
is proper over it, and a rational point and a point of residue degree two are exactly the data
`P i` and `Q i`. The base is a `Stacks.Chow.ChowSituation` with vanishing dimension function
rather than literally `Spec(k)`, as elsewhere in this directory; it instantiates to a field
through `Stacks.Chow.fieldChowSituation`.

The prime cycle of a point is supplied as a cycle together with the equation identifying its
coefficient function with `Function.locallyFinsuppWithin.single`, which is how
`Stacks.Chow.properPushforward_single` phrases the same thing.

## References

* [Stacks Project, Tag 05WK](https://stacks.math.columbia.edu/tag/05WK)
* [Stacks Project, Tag 05WL](https://stacks.math.columbia.edu/tag/05WL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Products over the base -/

/-- A morphism property which is multiplicative and stable under base change holds for the
structure morphism of a finite product in the category of schemes over a base. -/
theorem property_piObj_hom (W : MorphismProperty Scheme.{u}) [W.IsMultiplicative]
    [W.IsStableUnderBaseChange] {S : Scheme.{u}} {n : ℕ} (D : Fin n → Over S)
    (hD : ∀ i, W (D i).hom) : W (∏ᶜ D).hom := by
  induction n with
  | zero =>
      let c : Fan D := Fan.mk (Over.mk (𝟙 S)) fun i ↦ Fin.elim0 i
      have hc : IsLimit c :=
        { lift := fun t ↦ Over.homMk t.pt.hom
          fac := fun _ i ↦ Fin.elim0 i.as
          uniq := fun _ m _ ↦ by
            ext
            exact (Category.comp_id m.left).symm.trans m.w }
      exact (W.over_iso_iff ((limit.isLimit _).conePointUniqueUpToIso hc)).mpr (W.id_mem S)
  | succ n ih =>
      let T : Over S := ∏ᶜ fun i : Fin n ↦ D i.succ
      have hT : W T.hom := ih (fun i ↦ D i.succ) fun i ↦ hD i.succ
      let e : (∏ᶜ D) ≅ D 0 ⨯ T :=
        (limit.isLimit _).conePointUniqueUpToIso
          (extendFanIsLimit D (limit.isLimit _) (prodIsProd (D 0) T))
      refine (W.over_iso_iff e).mpr ?_
      rw [← (prod.snd : D 0 ⨯ T ⟶ T).w]
      exact W.comp_mem _ _
        (W.of_isPullback (Over.isPullback_of_binaryFan_isLimit
          (BinaryFan.mk prod.fst prod.snd) (prodIsProd (D 0) T)) (hD 0)) hT

/-- The product over the base of a finite family of schemes over the base. -/
def overProd {S : Scheme.{u}} {n : ℕ} {Y : Fin n → Scheme.{u}} (g : ∀ i, Y i ⟶ S) : Over S :=
  ∏ᶜ fun i ↦ Over.mk (g i)

/-- The `i`-th projection of the product over the base. -/
def overProdπ {S : Scheme.{u}} {n : ℕ} {Y : Fin n → Scheme.{u}} (g : ∀ i, Y i ⟶ S) (i : Fin n) :
    (overProd g).left ⟶ Y i :=
  (Pi.π (fun i ↦ Over.mk (g i)) i).left

/-- The projections of the product over the base are morphisms over the base. -/
theorem overProdπ_comp {S : Scheme.{u}} {n : ℕ} {Y : Fin n → Scheme.{u}} (g : ∀ i, Y i ⟶ S)
    (i : Fin n) : overProdπ g i ≫ g i = (overProd g).hom :=
  (Pi.π (fun i ↦ Over.mk (g i)) i).w

/-- A morphism over the base into the product over the base is determined by its components. -/
theorem overProd_hom_ext {S T : Scheme.{u}} {n : ℕ} {Y : Fin n → Scheme.{u}} (g : ∀ i, Y i ⟶ S)
    (a b : T ⟶ (overProd g).left) (hbase : a ≫ (overProd g).hom = b ≫ (overProd g).hom)
    (h : ∀ i, a ≫ overProdπ g i = b ≫ overProdπ g i) : a = b := by
  let a' : Over.mk (a ≫ (overProd g).hom) ⟶ overProd g := Over.homMk a
  let b' : Over.mk (a ≫ (overProd g).hom) ⟶ overProd g := Over.homMk b hbase.symm
  exact congrArg Over.Hom.left (Pi.hom_ext a' b' fun i ↦ by ext; exact h i)

/-- The product over the base of a finite family of proper morphisms is proper over the base. -/
instance isProper_overProd_hom {S : Scheme.{u}} {n : ℕ} {Y : Fin n → Scheme.{u}}
    (g : ∀ i, Y i ⟶ S) [∀ i, IsProper (g i)] : IsProper (overProd g).hom :=
  property_piObj_hom @IsProper _ fun i ↦ (inferInstance : IsProper (g i))

/-- The product over the base of a finite family of morphisms locally of finite type is locally
of finite type over the base. -/
instance locallyOfFiniteType_overProd_hom {S : Scheme.{u}} {n : ℕ} {Y : Fin n → Scheme.{u}}
    (g : ∀ i, Y i ⟶ S) [∀ i, LocallyOfFiniteType (g i)] :
    LocallyOfFiniteType (overProd g).hom :=
  property_piObj_hom @LocallyOfFiniteType _ fun i ↦ (inferInstance : LocallyOfFiniteType (g i))

/-- The inclusion of the product over the base of a family of open subschemes into the product
over the base of the ambient schemes. -/
def overProdOpensι {S : Scheme.{u}} {n : ℕ} {Y : Fin n → Scheme.{u}} (g : ∀ i, Y i ⟶ S)
    (U : ∀ i, (Y i).Opens) :
    (overProd fun i ↦ (U i).ι ≫ g i).left ⟶ (overProd g).left :=
  (Limits.Pi.map fun i ↦ (Over.homMk (U i).ι rfl :
    Over.mk ((U i).ι ≫ g i) ⟶ Over.mk (g i))).left

/-- The inclusion of a product of open subschemes is compatible with the projections. -/
theorem overProdOpensι_comp_π {S : Scheme.{u}} {n : ℕ} {Y : Fin n → Scheme.{u}}
    (g : ∀ i, Y i ⟶ S) (U : ∀ i, (Y i).Opens) (i : Fin n) :
    overProdOpensι g U ≫ overProdπ g i =
      overProdπ (fun i ↦ (U i).ι ≫ g i) i ≫ (U i).ι :=
  congrArg Over.Hom.left (Limits.Pi.map_π _ i)

/-- The inclusion of a product of open subschemes is a morphism over the base. -/
theorem overProdOpensι_comp_hom {S : Scheme.{u}} {n : ℕ} {Y : Fin n → Scheme.{u}}
    (g : ∀ i, Y i ⟶ S) (U : ∀ i, (Y i).Opens) :
    overProdOpensι g U ≫ (overProd g).hom = (overProd fun i ↦ (U i).ι ≫ g i).hom :=
  (Limits.Pi.map fun i ↦ (Over.homMk (U i).ι rfl :
    Over.mk ((U i).ι ≫ g i) ⟶ Over.mk (g i))).w

/-- Morphisms into the factors whose images lie in the open subschemes and which agree over the
base assemble into a morphism into the product of the open subschemes. -/
private theorem exists_hom_overProd_opens {S T : Scheme.{u}} {n : ℕ} {Y : Fin n → Scheme.{u}}
    (g : ∀ i, Y i ⟶ S) (U : ∀ i, (Y i).Opens) (h : T ⟶ S) (a : ∀ i, T ⟶ Y i)
    (hrange : ∀ i, Set.range (a i).base ⊆ Set.range (U i).ι.base) (hcomp : ∀ i, a i ≫ g i = h) :
    ∃ b : T ⟶ (overProd fun i ↦ (U i).ι ≫ g i).left,
      b ≫ (overProd fun i ↦ (U i).ι ≫ g i).hom = h ∧
        ∀ i, b ≫ overProdπ (fun i ↦ (U i).ι ≫ g i) i ≫ (U i).ι = a i := by
  let t i := IsOpenImmersion.lift (U i).ι (a i) (hrange i)
  have ht i : t i ≫ (U i).ι = a i := IsOpenImmersion.lift_fac _ _ _
  let bO : Over.mk h ⟶ overProd fun i ↦ (U i).ι ≫ g i :=
    Pi.lift fun i ↦ (Over.homMk (t i) (by
      change t i ≫ (U i).ι ≫ g i = h
      rw [← Category.assoc, ht, hcomp]) : Over.mk h ⟶ Over.mk ((U i).ι ≫ g i))
  refine ⟨bO.left, bO.w, fun i ↦ ?_⟩
  have hb : bO.left ≫ overProdπ (fun i ↦ (U i).ι ≫ g i) i = t i :=
    congrArg Over.Hom.left (Limits.Pi.lift_comp_π _ i)
  rw [← Category.assoc, hb, ht]

private theorem isOpenImmersion_and_range_overProdOpensι {S : Scheme.{u}} {n : ℕ}
    {Y : Fin n → Scheme.{u}} (g : ∀ i, Y i ⟶ S) (U : ∀ i, (Y i).Opens) :
    IsOpenImmersion (overProdOpensι g U) ∧
      Set.range (overProdOpensι g U).base =
        {x | ∀ i, (overProdπ g i).base x ∈ U i} := by
  set j := overProdOpensι g U with hjdef
  set E : Fin n → Scheme.{u} := fun i ↦ (U i : Scheme.{u}) with hEdef
  let W : (overProd g).left.Opens :=
    ⟨⋂ i, (overProdπ g i).base ⁻¹' (U i : Set (Y i)),
      isOpen_iInter_of_finite fun i ↦ (U i).isOpen.preimage (overProdπ g i).continuous⟩
  have hWmem : ∀ x : (overProd g).left,
      x ∈ (W : Set (overProd g).left) ↔ ∀ i, (overProdπ g i).base x ∈ U i := fun _ ↦
    Set.mem_iInter
  have hWset : (W : Set (overProd g).left) = {x | ∀ i, (overProdπ g i).base x ∈ U i} :=
    Set.ext hWmem
  have hj (i) : j ≫ overProdπ g i = overProdπ (fun i ↦ (U i).ι ≫ g i) i ≫ (U i).ι :=
    overProdOpensι_comp_π g U i
  have hr : Set.range j.base ⊆ Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    refine (hWmem _).mpr fun i ↦ ?_
    show (overProdπ g i).base (j.base x) ∈ (U i : Set (Y i))
    rw [← Scheme.Opens.range_ι]
    exact ⟨(overProdπ (fun i ↦ (U i).ι ≫ g i) i).base x,
      congrArg (fun φ : (overProd fun i ↦ (U i).ι ≫ g i).left ⟶ Y i ↦ φ.base x) (hj i).symm⟩
  let a := IsOpenImmersion.lift W.ι j hr
  have ha : a ≫ W.ι = j := IsOpenImmersion.lift_fac _ _ _
  have hri (i) : Set.range (W.ι ≫ overProdπ g i).base ⊆ Set.range (U i).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact (hWmem _).mp x.property i
  obtain ⟨b, hbbase, hb⟩ := exists_hom_overProd_opens g U (W.ι ≫ (overProd g).hom)
    (fun i ↦ W.ι ≫ overProdπ g i) hri fun i ↦ by rw [Category.assoc, overProdπ_comp]
  have hjbase : j ≫ (overProd g).hom = (overProd fun i ↦ (U i).ι ≫ g i).hom :=
    overProdOpensι_comp_hom g U
  have hbj : b ≫ j = W.ι := by
    refine overProd_hom_ext g _ _ ?_ fun i ↦ ?_
    · rw [Category.assoc, hjbase, hbbase]
    · rw [Category.assoc, hj, hb]
  have hab : a ≫ b = 𝟙 _ := by
    refine overProd_hom_ext (fun i ↦ (U i).ι ≫ g i) _ _ ?_ fun i ↦ ?_
    · rw [Category.assoc, hbbase, ← Category.assoc, ha, hjbase, Category.id_comp]
    · refine (cancel_mono (U i).ι).mp ?_
      simp only [Category.assoc, Category.id_comp, hb]
      rw [← Category.assoc, ha, hj]
  have hba : b ≫ a = 𝟙 _ := by
    refine (cancel_mono W.ι).mp ?_
    rw [Category.assoc, ha, hbj, Category.id_comp]
  have _ : IsIso a := ⟨⟨b, hab, hba⟩⟩
  have hjoi : IsOpenImmersion j := by rw [← ha]; infer_instance
  refine ⟨hjoi, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    have hh := hr hx
    rw [Scheme.Opens.range_ι, hWset] at hh
    exact hh
  · intro x hx
    exact ⟨b.base ⟨x, (hWmem x).mpr hx⟩,
      congrArg (fun φ : W.toScheme ⟶ (overProd g).left ↦ φ.base ⟨x, (hWmem x).mpr hx⟩) hbj⟩

/-- The product over the base of a family of open subschemes is an open immersion into the
product over the base. -/
instance isOpenImmersion_overProdOpensι {S : Scheme.{u}} {n : ℕ} {Y : Fin n → Scheme.{u}}
    (g : ∀ i, Y i ⟶ S) (U : ∀ i, (Y i).Opens) : IsOpenImmersion (overProdOpensι g U) :=
  (isOpenImmersion_and_range_overProdOpensι g U).1

/-- The product over the base of a family of open subschemes is the open subscheme of the
product over the base on which every coordinate lies in its member of the family. -/
theorem range_overProdOpensι {S : Scheme.{u}} {n : ℕ} {Y : Fin n → Scheme.{u}}
    (g : ∀ i, Y i ⟶ S) (U : ∀ i, (Y i).Opens) :
    Set.range (overProdOpensι g U).base = {x | ∀ i, (overProdπ g i).base x ∈ U i} :=
  (isOpenImmersion_and_range_overProdOpensι g U).2

/-! ### Residue degrees of sections -/

/-- A section of a morphism has residue degree one, and the morphism has residue degree one at
every point in the image of the section. -/
theorem residueDegree_eq_one_of_section {X S : Scheme.{u}} (p : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ p = 𝟙 S) (s : S) :
    p.residueDegree (σ.base s) = 1 ∧ σ.residueDegree s = 1 := by
  have h := residueDegree_comp σ p s
  rw [hσ, Scheme.Hom.residueDegree_id] at h
  exact mul_eq_one.mp h.symm

/-! ### Prime cycles -/

private theorem classicalSingle_self {X : Type u} [TopologicalSpace X] (x : X) (c : ℤ) :
    (@Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _ x c) x = c := by
  let _ : DecidableEq X := Classical.decEq X
  simp

private theorem classicalSingle_of_ne {X : Type u} [TopologicalSpace X] {x y : X} (h : y ≠ x)
    (c : ℤ) :
    (@Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _ x c) y = 0 := by
  let _ : DecidableEq X := Classical.decEq X
  simp [h]

/-- Over a base with vanishing dimension function a point whose residue field is finite over its
image has relative dimension zero. -/
theorem relativeDimension_eq_zero_of_residueDegree_ne_zero {X S : Scheme.{u}}
    (δ : DimensionFunction S) (hδ : ∀ s : S, δ s = 0) (f : X ⟶ S) (x : X)
    (hx : f.residueDegree x ≠ 0) : relativeDimension δ f x = 0 := by
  let _ : Algebra (S.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have _ : Module.Finite (S.residueField (f.base x)) (X.residueField x) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hx)
  simp [relativeDimension, hδ, trdeg_eq_zero]

/-- The prime cycle of a point of relative dimension zero is a zero cycle. -/
theorem single_mem_cyclesOfDimension_zero (C : ChowSituation.{u}) {X : Scheme.{u}}
    [DecidableEq X] (p : X ⟶ C.S) [LocallyOfFiniteType p] (x : X)
    (hx : relativeDimension C.dimensionFunction p x = 0) :
    Function.locallyFinsuppWithin.single x (1 : ℤ) ∈ cyclesOfDimension C p 0 := by
  rw [mem_cyclesOfDimension_iff_forall_point]
  intro z hz
  have hzx : z = x := by
    by_contra h
    simp [h] at hz
  exact hzx ▸ hx

/-- A pushed-forward cycle vanishes outside the image of the morphism. -/
theorem properPushforward_apply_eq_zero_of_notMem_range (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (k : ℤ)
    (α : CycleGroup C sX k) (y : Y) (hy : y ∉ Set.range f.base) :
    (properPushforward C sX sY f hf k α).1 y = 0 := by
  rw [properPushforward_apply]
  have he : f.base ⁻¹' {y} = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    exact fun h ↦ hy ⟨x, h⟩
  rw [he, finsum_mem_empty]

/-- Over a base with vanishing dimension function the degree of the prime cycle of a point is
the residue degree of that point over the base. -/
theorem cycleDegree_single (C : ChowSituation.{u}) (hδ : ∀ s : C.S, C.dimensionFunction s = 0)
    {X : Scheme.{u}} (p : X ⟶ C.S) [IsProper p] (x : X) (α : CycleGroup C p 0)
    (hα : α.1 =
      @Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _ x (1 : ℤ)) :
    cycleDegree C p (p.base x) α = (p.residueDegree x : ℤ) := by
  have hd : relativeDimension C.dimensionFunction (𝟙 C.S) (p.base x) = 0 := by
    rw [relativeDimension_id]
    exact hδ _
  rw [cycleDegree_apply, properPushforward_single C p (𝟙 C.S) p (Category.comp_id p) 0 x α hα,
    ite_eq_left hd]
  exact classicalSingle_self (p.base x) _

/-- If every point in the support of a zero cycle has residue degree over the base divisible by
`d`, then so is the degree of the cycle. -/
theorem dvd_cycleDegree_of_dvd_residueDegree (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [IsProper p] (s : C.S) (d : ℤ) (α : CycleGroup C p 0)
    (h : ∀ x : X, α.1 x ≠ 0 → d ∣ (p.residueDegree x : ℤ)) :
    d ∣ cycleDegree C p s α := by
  rw [cycleDegree_apply, properPushforward_apply]
  refine finsum_mem_induction (fun z : ℤ ↦ d ∣ z) (dvd_zero d) (fun _ _ ↦ dvd_add) ?_
  intro x _
  by_cases hx : α.1 x = 0
  · rw [hx, zero_mul]
    exact dvd_zero d
  · split_ifs
    · exact dvd_mul_of_dvd_right (h x hx) _
    · rw [mul_zero]
      exact dvd_zero d

/-! ### The degree criterion -/

/-- **The degree criterion.** Let `X` be proper over a base with vanishing dimension function,
let `j : V ⟶ X` be an open immersion, and let `d` be an integer not dividing one such that every
point of `X` outside the image of `j` has residue degree over the base divisible by `d`. Then the
prime cycle of a point of `V` whose image has residue degree one over the base is not rationally
equivalent to zero on `V`. -/
theorem single_notMem_rationalEquivalences_of_dvd_boundary_residueDegree
    (C : ChowSituation.{u}) (hδ : ∀ s : C.S, C.dimensionFunction s = 0) {X V : Scheme.{u}}
    (p : X ⟶ C.S) [IsProper p] (pV : V ⟶ C.S) [LocallyOfFiniteType pV] (j : V ⟶ X)
    [IsOpenImmersion j] (hj : j ≫ p = pV) {d : ℤ} (hd : ¬ d ∣ (1 : ℤ))
    (hboundary : ∀ x : X, x ∉ Set.range j.base → d ∣ (p.residueDegree x : ℤ))
    (v : V) (hv : p.residueDegree (j.base v) = 1) (α : CycleGroup C pV 0)
    (hα : α.1 =
      @Function.locallyFinsuppWithin.single V _ ℤ (Classical.decEq V) _ v (1 : ℤ)) :
    α ∉ rationalEquivalences C pV 0 := by
  subst hj
  intro hmem
  -- the image of `j`, as an open subscheme of `X`
  obtain ⟨W, hW⟩ : ∃ W : X.Opens, (W : Set X) = Set.range j.base := ⟨j.opensRange, by simp⟩
  have hWrange : Set.range j.base = Set.range W.ι.base := by rw [Scheme.Opens.range_ι, hW]
  let e : V ≅ (W : Scheme.{u}) := IsOpenImmersion.isoOfRangeEq j W.ι hWrange
  have he : e.hom ≫ W.ι = j := IsOpenImmersion.isoOfRangeEq_hom_fac j W.ι hWrange
  have hebase : ∀ z : V, W.ι.base (e.hom.base z) = j.base z := fun z ↦
    congrArg (fun φ : V ⟶ X ↦ φ.base z) he
  have hecomm : e.hom ≫ (W.ι ≫ p) = j ≫ p := by rw [← Category.assoc, he]
  have _ : MorphismProperty.ContainsIdentities (@IsProper) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have _ : IsProper e.hom := MorphismProperty.of_isIso @IsProper e.hom
  -- the relative dimension of the point `j v`
  have hvne : p.residueDegree (j.base v) ≠ 0 := by rw [hv]; exact one_ne_zero
  have hdimX : relativeDimension C.dimensionFunction p (j.base v) = 0 :=
    relativeDimension_eq_zero_of_residueDegree_ne_zero C.dimensionFunction hδ p (j.base v) hvne
  -- the prime cycle of `j v` on `X`
  let a : CycleGroup C p 0 :=
    ⟨@Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _ (j.base v) (1 : ℤ),
      @single_mem_cyclesOfDimension_zero C X (Classical.decEq X) p _ (j.base v) hdimX⟩
  -- it restricts to `α` transported along `e`
  have hβ : cycleGroupOpensRestrict C p W 0 a =
      properPushforward C (j ≫ p) (W.ι ≫ p) e.hom hecomm 0 α := by
    have hdimW : relativeDimension C.dimensionFunction (W.ι ≫ p) (e.hom.base v) = 0 := by
      rw [relativeDimension_comp_isOpenImmersion, hebase]
      exact hdimX
    have hpush : (properPushforward C (j ≫ p) (W.ι ≫ p) e.hom hecomm 0 α).1 =
        @Function.locallyFinsuppWithin.single (W : Scheme.{u}) _ ℤ
          (Classical.decEq (W : Scheme.{u})) _ (e.hom.base v) (1 : ℤ) := by
      rw [properPushforward_single C (j ≫ p) (W.ι ≫ p) e.hom hecomm 0 v α hα,
        ite_eq_left hdimW, residueDegree_eq_one_of_isOpenImmersion, Nat.cast_one]
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
    rw [cycleGroupOpensRestrict_apply, hpush]
    by_cases hz : z = e.hom.base v
    · rw [hz, classicalSingle_self]
      show (@Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
        (j.base v) (1 : ℤ)) (W.ι.base (e.hom.base v)) = 1
      rw [hebase]
      exact classicalSingle_self _ _
    · rw [classicalSingle_of_ne hz]
      show (@Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
        (j.base v) (1 : ℤ)) (W.ι.base z) = 0
      refine classicalSingle_of_ne ?_ _
      intro hcon
      exact hz (W.isOpenEmbedding.injective (hcon.trans (hebase v).symm))
  -- the rational equivalence on the open subscheme
  have hres : RationallyEquivalent C (W.ι ≫ p) 0 (cycleGroupOpensRestrict C p W 0 a)
      (cycleGroupOpensRestrict C p W 0 0) := by
    show cycleGroupOpensRestrict C p W 0 a - cycleGroupOpensRestrict C p W 0 0 ∈
      rationalEquivalences C (W.ι ≫ p) 0
    rw [map_zero, sub_zero, hβ]
    exact properPushforwardFactorsThroughRationalEquivalence_of_isProper C (j ≫ p) (W.ι ≫ p)
      e.hom hecomm 0 α hmem
  -- the closed complement of the open subscheme
  let I : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X)ᶜ, W.isOpen.isClosed_compl⟩
  have hI : Set.range I.subschemeι.base = (Set.range W.ι.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, Scheme.Opens.range_ι]
    rfl
  obtain ⟨γ, hγ⟩ := exists_rationallyEquivalent_properPushforward_of_cycleGroupRestrict C p
    (I.subschemeι ≫ p) I.subschemeι rfl W hI 0 a 0 hres
  -- compare degrees
  have hzero := cycleDegree_eq_zero_of_mem_rationalEquivalences C hδ p (p.base (j.base v))
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C p (𝟙 C.S) p
      (Category.comp_id p) 0) hγ
  rw [zero_add, map_sub, cycleDegree_single C hδ p (j.base v) a rfl, hv, Nat.cast_one,
    sub_eq_zero] at hzero
  refine hd ?_
  rw [hzero]
  refine dvd_cycleDegree_of_dvd_residueDegree C p _ d _ ?_
  intro x hx
  refine hboundary x ?_
  have hxI : x ∈ Set.range I.subschemeι.base := by
    by_contra hcon
    exact hx (properPushforward_apply_eq_zero_of_notMem_range C (I.subschemeι ≫ p) p
      I.subschemeι rfl 0 γ x hcon)
  rw [hI, ← hWrange] at hxI
  exact hxI

/-! ### Stacks 05WK -/

/-- **Stacks 05WK.** Let the base be a situation for Chow homology with vanishing dimension
function, the case of the spectrum of a field. Let `X i` be proper over the base, each with a
section `P i` and a point `Q i` whose residue field has degree two over the base, and let `U i`
be the complement of `Q i`. The sections assemble into a section of the product of the `U i` over
the base, and the prime cycle of each of its points is not rationally equivalent to zero: the
class of `P 1 × ⋯ × P n` is nonzero in the zeroth Chow group of `U 1 ×_S ⋯ ×_S U n`. -/
@[stacks 05WK]
theorem chowClass_overProdOpens_section_ne_zero (C : ChowSituation.{u})
    (hδ : ∀ s : C.S, C.dimensionFunction s = 0) {n : ℕ} {X : Fin n → Scheme.{u}}
    (f : ∀ i, X i ⟶ C.S) [∀ i, IsProper (f i)] (P : ∀ i, C.S ⟶ X i)
    (hP : ∀ i, P i ≫ f i = 𝟙 C.S) (Q : ∀ i, X i) (hQ : ∀ i, (f i).residueDegree (Q i) = 2)
    (U : ∀ i, (X i).Opens) (hU : ∀ i, (U i : Set (X i)) = {Q i}ᶜ) :
    ∃ σ : C.S ⟶ (overProd fun i ↦ (U i).ι ≫ f i).left,
      σ ≫ (overProd fun i ↦ (U i).ι ≫ f i).hom = 𝟙 C.S ∧
        (∀ i, σ ≫ overProdπ (fun i ↦ (U i).ι ≫ f i) i ≫ (U i).ι = P i) ∧
          ∀ s₀ : C.S, ∃ α : CycleGroup C (overProd fun i ↦ (U i).ι ≫ f i).hom 0,
            α.1 = @Function.locallyFinsuppWithin.single _ _ ℤ
                (Classical.decEq (overProd fun i ↦ (U i).ι ≫ f i).left) _ (σ.base s₀) (1 : ℤ) ∧
              QuotientAddGroup.mk' (rationalEquivalences C
                (overProd fun i ↦ (U i).ι ≫ f i).hom 0) α ≠ 0 := by
  -- the sections avoid the punctures
  have hr (i) : Set.range (P i).base ⊆ Set.range (U i).ι.base := by
    rw [Scheme.Opens.range_ι, hU]
    rintro _ ⟨s, rfl⟩ hcon
    have hdeg := (residueDegree_eq_one_of_section (f i) (P i) (hP i) s).1
    rw [show (P i).base s = Q i from hcon, hQ i] at hdeg
    exact absurd hdeg (by decide)
  obtain ⟨σ, hσ, hσπ⟩ := exists_hom_overProd_opens f U (𝟙 C.S) P hr hP
  refine ⟨σ, hσ, hσπ, ?_⟩
  · intro s₀
    let j := overProdOpensι f U
    have hjhom : j ≫ (overProd f).hom = (overProd fun i ↦ (U i).ι ≫ f i).hom :=
      overProdOpensι_comp_hom f U
    have hsec : (σ ≫ j) ≫ (overProd f).hom = 𝟙 C.S := by
      rw [Category.assoc, hjhom]
      exact hσ
    have hv : (overProd f).hom.residueDegree ((σ ≫ j).base s₀) = 1 :=
      (residueDegree_eq_one_of_section (overProd f).hom (σ ≫ j) hsec s₀).1
    have hvj : (σ ≫ j).base s₀ = j.base (σ.base s₀) := rfl
    -- the point has relative dimension zero over the base
    have hdim : relativeDimension C.dimensionFunction
        (overProd fun i ↦ (U i).ι ≫ f i).hom (σ.base s₀) = 0 := by
      rw [← hjhom, relativeDimension_comp_isOpenImmersion]
      refine relativeDimension_eq_zero_of_residueDegree_ne_zero C.dimensionFunction hδ
        (overProd f).hom _ ?_
      rw [← hvj, hv]
      exact one_ne_zero
    refine ⟨⟨@Function.locallyFinsuppWithin.single _ _ ℤ
        (Classical.decEq (overProd fun i ↦ (U i).ι ≫ f i).left) _ (σ.base s₀) (1 : ℤ),
      @single_mem_cyclesOfDimension_zero C _
        (Classical.decEq (overProd fun i ↦ (U i).ι ≫ f i).left) _ _ _ hdim⟩, rfl, ?_⟩
    rw [Ne, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    refine single_notMem_rationalEquivalences_of_dvd_boundary_residueDegree C hδ
      (overProd f).hom (overProd fun i ↦ (U i).ι ≫ f i).hom j hjhom
      (d := 2) (by decide) ?_ (σ.base s₀) (by rw [← hvj]; exact hv) _ rfl
    -- every point off the product of the open subschemes has even residue degree
    intro x hx
    have hnot : ¬ ∀ i, (overProdπ f i).base x ∈ U i := by
      intro hcon
      refine hx ?_
      rw [range_overProdOpensι f U]
      exact hcon
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hi' : (overProdπ f i).base x ∉ (U i : Set (X i)) := hi
    rw [hU i] at hi'
    have hQi : (overProdπ f i).base x = Q i := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not] using hi'
    have hcomp := residueDegree_comp (overProdπ f i) (f i) x
    rw [overProdπ_comp, hQi, hQ i] at hcomp
    have h2 : 2 ∣ (overProd f).hom.residueDegree x := ⟨_, hcomp⟩
    exact_mod_cast h2

end Stacks.Chow

end
