module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.Product
public import StacksFrontier.Algebra.DifferentialGraded.Module.ProductHomotopy
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyP
public import StacksCore.Tactic.StacksAttribute

/-! # Products in the derived category of a differential graded algebra

Let `(A, d)` be a differential graded algebra over a commutative ring `R`. The canonical functor
`Mod_{(A,d)} ⥤ D(A, d)` to the derived category — the quotient by homotopy followed by the
localization at the quasi-isomorphisms — carries a product of differential graded modules to a
product in `D(A, d)`.

## Main results

* `DifferentialGradedModule.isQuasiIsomorphism_of_quasiIso`: the converse of
  `DifferentialGradedModule.quasiIso_of_isQuasiIsomorphism` — a homomorphism whose underlying
  cochain map is a quasi-isomorphism satisfies the cycle-and-boundary criterion.
* `DifferentialGradedModule.isQuasiIsomorphism_productMap`: a product of quasi-isomorphisms is a
  quasi-isomorphism.
* `DifferentialGradedModule.productHomotopy`: a family of homotopies between the components of
  two maps into a product assembles into a homotopy between the maps.
* `DifferentialGradedModule.isLimit_toHomotopyCategory_mapCone_product`: the image of the
  product fan in the homotopy category `K(A, d)` is a limit fan.
* `DifferentialGradedModule.isLimit_q_mapCone_product`: its image in `D(A, d)` is a limit fan.
* `DifferentialGradedModule.derivedCategoryQ_preservesProducts`: the canonical functor to the
  derived category preserves products.
* `DifferentialGradedModule.nonempty_isLimit_derivedProductFan`: the same, in the form that names
  the product object `∏ᶜ f` and its projections.

## Implementation notes

The preservation of products is proved without resolutions, in three steps:

1. `Mod_{(A,d)}` has products, degreewise, with a named object
   (`DifferentialGradedModule.product`);
2. the homotopy category has the *same* products, because a homotopy into a product is
   determined componentwise (`DifferentialGradedModule.productHomotopy`);
3. the localization at the quasi-isomorphisms preserves them, because a product of
   quasi-isomorphisms is again one (`DifferentialGradedModule.isQuasiIsomorphism_productMap`)
   and `quasiIsomorphisms' A` admits a calculus of fractions on both sides.

Step 3 is a general fact about localizations, isolated here as
`localized_product_hom_existsUnique`: if `C` has `J`-indexed products, `W` admits a left and a
right calculus of fractions, and the `J`-indexed product of a family of maps in `W` is again in
`W`, then the localization functor carries those products to products. Both calculi are used: the
left one to write a morphism of the localization as a fraction, the right one to compare two such.

The cycle-and-boundary criterion `DifferentialGradedModule.IsQuasiIsomorphism` is componentwise
for a product of named differential graded modules (`DifferentialGradedModule.product`). It is
related to Mathlib's `QuasiIso` in both directions; the direction from `QuasiIso` to the criterion
is `DifferentialGradedModule.isQuasiIsomorphism_of_quasiIso`, which computes the homology of a
short complex of modules as `ker g / range f` through
`CategoryTheory.ShortComplex.moduleCatLeftHomologyData`.

The base ring, the algebra and every module live in one universe `u`, and the index type of a
product is taken in `Type u`, matching
`DifferentialGradedModule.instHasProducts : HasProducts.{u}`; the Stacks Project allows an
arbitrary index universe.

## References

* [Stacks Project, Tag 09QI](https://stacks.math.columbia.edu/tag/09QI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ u

namespace DifferentialGradedModule

/-! ### Products in a localization

A localization at a class of morphisms admitting a calculus of fractions on both sides preserves
those products of the ambient category that the class is closed under. The statements take a
chosen limit fan on every family. -/

section LocalizedProduct

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  [W.HasLeftCalculusOfFractions] [W.HasRightCalculusOfFractions]
  {J : Type*} (c : ∀ F : J → C, Fan F) (hc : ∀ F, IsLimit (c F))
  (hw : ∀ (F G : J → C) (φ : ∀ i, F i ⟶ G i), (∀ i, W (φ i)) →
    W ((hc G).lift (Fan.mk (c F).pt fun i => (c F).proj i ≫ φ i)))

include W hc hw

omit [W.HasRightCalculusOfFractions] in
/-- Two morphisms into a product become equal in the localization as soon as all their
components do. -/
private lemma localized_product_map_ext {F : J → C} {X : C} (a b : X ⟶ (c F).pt)
    (h : ∀ i, L.map a ≫ L.map ((c F).proj i) = L.map b ≫ L.map ((c F).proj i)) :
    L.map a = L.map b := by
  classical
  have hi (i : J) := (W.map_eq_iff_postcomp L (a ≫ (c F).proj i) (b ≫ (c F).proj i)).mp
    (by simpa only [L.map_comp] using h i)
  choose G s hs he using hi
  let t := (hc G).lift (Fan.mk (c F).pt fun i => (c F).proj i ≫ s i)
  have : IsIso (L.map t) := Localization.inverts L W t (hw F G s hs)
  apply (cancel_mono (L.map t)).mp
  simp only [← L.map_comp]
  congr 1
  refine (hc G).hom_ext fun i => ?_
  simpa only [t, Category.assoc, IsLimit.fac, Fan.mk_π_app] using he i.as

/-- Two morphisms of the localization out of the image of an object and into the image of a
product are equal as soon as all their components are. -/
private lemma localized_product_hom_ext {F : J → C} {X : C}
    (a b : L.obj X ⟶ L.obj (c F).pt)
    (h : ∀ i, a ≫ L.map ((c F).proj i) = b ≫ L.map ((c F).proj i)) : a = b := by
  obtain ⟨α, rfl⟩ := Localization.exists_rightFraction L W a
  obtain ⟨β, rfl⟩ := Localization.exists_rightFraction L W b
  obtain ⟨δ, hδ⟩ := (MorphismProperty.LeftFraction.mk α.s β.s β.hs).exists_rightFraction
  have : IsIso (L.map δ.s) := Localization.inverts L W δ.s δ.hs
  have : IsIso (L.map α.s) := Localization.inverts L W α.s α.hs
  apply (cancel_epi (L.map δ.s ≫ L.map α.s)).mp
  have hb : L.map δ.s ≫ L.map α.s ≫ β.map L (Localization.inverts L W) =
      L.map (δ.f ≫ β.f) := by
    rw [← Category.assoc, ← L.map_comp, hδ, L.map_comp, Category.assoc, β.map_s_comp_map,
      ← L.map_comp]
  have ha : L.map δ.s ≫ L.map α.s ≫ α.map L (Localization.inverts L W) =
      L.map (δ.s ≫ α.f) := by rw [α.map_s_comp_map, ← L.map_comp]
  simp only [Category.assoc]
  rw [ha, hb]
  refine localized_product_map_ext L W c hc hw _ _ fun i => ?_
  rw [← ha, ← hb]
  simpa only [Category.assoc] using congrArg (fun k => L.map δ.s ≫ L.map α.s ≫ k) (h i)

/-- **A localization carries a product it is compatible with to a product.** Given a family of
morphisms of the localization out of the image of an object and into the images of the factors,
there is exactly one morphism into the image of the product with those components. -/
private lemma localized_product_hom_existsUnique (F : J → C) (X : C)
    (a : ∀ i, L.obj X ⟶ L.obj (F i)) :
    ∃! g : L.obj X ⟶ L.obj (c F).pt, ∀ i, g ≫ L.map ((c F).proj i) = a i := by
  classical
  choose α hα using fun i => Localization.exists_leftFraction L W (a i)
  let G := fun i => (α i).Y'
  let t := (hc G).lift (Fan.mk (c F).pt fun i => (c F).proj i ≫ (α i).s)
  let g := (hc G).lift (Fan.mk X fun i => (α i).f)
  have : IsIso (L.map t) :=
    Localization.inverts L W t (hw F G (fun i => (α i).s) fun i => (α i).hs)
  have hfac (i : J) : (L.map g ≫ inv (L.map t)) ≫ L.map ((c F).proj i) = a i := by
    have : IsIso (L.map (α i).s) := Localization.inverts L W _ (α i).hs
    apply (cancel_mono (L.map (α i).s)).mp
    have ht : L.map ((c F).proj i) ≫ L.map (α i).s = L.map t ≫ L.map ((c G).proj i) := by
      rw [← L.map_comp, ← L.map_comp]
      exact congrArg L.map
        ((hc G).fac (Fan.mk (c F).pt fun i => (c F).proj i ≫ (α i).s) ⟨i⟩).symm
    rw [Category.assoc, Category.assoc, ht]
    simp only [IsIso.inv_hom_id_assoc]
    rw [← L.map_comp, show g ≫ (c G).proj i = (α i).f from (hc G).fac _ ⟨i⟩, hα i,
      (α i).map_comp_map_s]
  exact ⟨L.map g ≫ inv (L.map t), hfac,
    fun g' hg' => localized_product_hom_ext L W c hc hw _ _
      fun i => (hg' i).trans (hfac i).symm⟩

end LocalizedProduct

/-! ### The cycle-and-boundary criterion is necessary

The homology of a short complex of modules is `ker g / range f`, and a morphism of short
complexes is a quasi-isomorphism exactly when the induced map of those quotients is bijective.
Spelled out on elements, that is the cycle-and-boundary criterion. Only the direction from
`QuasiIso` to the criterion is proved here; the other one is
`DifferentialGradedModule.quasiIso_of_isQuasiIsomorphism`. -/

section ShortComplex

variable {R : Type u} [Ring R]

/-- The class in homology of a cycle of a short complex of modules. -/
private def cycleClass (S : ShortComplex (ModuleCat.{u} R)) :
    LinearMap.ker S.g.hom →ₗ[R] S.homology :=
  (S.moduleCatCyclesIso.inv ≫ S.homologyπ).hom

/-- Through `CategoryTheory.ShortComplex.moduleCatLeftHomologyData`, taking the class of a cycle
is the quotient map by the cycles coming from `S.X₁`. -/
private lemma cycleClass_eq (S : ShortComplex (ModuleCat.{u} R)) :
    cycleClass S = S.moduleCatHomologyIso.inv.hom.comp
      (LinearMap.range S.moduleCatToCycles).mkQ :=
  congrArg ModuleCat.Hom.hom S.moduleCatCyclesIso_inv_π

/-- Every homology class is the class of a cycle. -/
private lemma cycleClass_surjective (S : ShortComplex (ModuleCat.{u} R)) :
    Function.Surjective (cycleClass S) := by
  rw [cycleClass_eq]
  exact S.moduleCatHomologyIso.symm.toLinearEquiv.surjective.comp
    (Submodule.mkQ_surjective _)

/-- A cycle has class zero exactly when it is a boundary. -/
private lemma cycleClass_eq_zero (S : ShortComplex (ModuleCat.{u} R))
    (z : LinearMap.ker S.g.hom) :
    cycleClass S z = 0 ↔ ∃ x : S.X₁, S.f.hom x = z.val := by
  rw [cycleClass_eq]
  show S.moduleCatHomologyIso.symm.toLinearEquiv
    ((LinearMap.range S.moduleCatToCycles).mkQ z) = 0 ↔ _
  refine (show S.moduleCatHomologyIso.symm.toLinearEquiv
    ((LinearMap.range S.moduleCatToCycles).mkQ z) = 0 ↔
    (LinearMap.range S.moduleCatToCycles).mkQ z = 0 from
      S.moduleCatHomologyIso.symm.toLinearEquiv.map_eq_zero_iff).trans ?_
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨fun ⟨x, hx⟩ => ⟨x, congrArg Subtype.val hx⟩, fun ⟨x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩

/-- Taking the class of a cycle is natural: a morphism of short complexes carrying a cycle to a
cycle carries its class to the class of the image. -/
private lemma cycleClass_naturality {S T : ShortComplex (ModuleCat.{u} R)} (a : S ⟶ T)
    (x : LinearMap.ker S.g.hom) (y : LinearMap.ker T.g.hom)
    (h : a.τ₂.hom x.val = y.val) :
    (ShortComplex.homologyMap a).hom (cycleClass S x) = cycleClass T y := by
  have hc : (ShortComplex.cyclesMap a).hom (S.moduleCatCyclesIso.inv.hom x) =
      T.moduleCatCyclesIso.inv.hom y := by
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    show (S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap a ≫ T.iCycles).hom x =
      (T.moduleCatCyclesIso.inv ≫ T.iCycles).hom y
    rw [ShortComplex.cyclesMap_i, ← Category.assoc, S.moduleCatCyclesIso_inv_iCycles,
      T.moduleCatCyclesIso_inv_iCycles]
    exact h
  show (S.moduleCatCyclesIso.inv ≫ S.homologyπ ≫ ShortComplex.homologyMap a).hom x = _
  rw [ShortComplex.homologyπ_naturality]
  show T.homologyπ.hom ((ShortComplex.cyclesMap a).hom
    (S.moduleCatCyclesIso.inv.hom x)) = T.homologyπ.hom (T.moduleCatCyclesIso.inv.hom y)
  rw [hc]

/-- **A quasi-isomorphism of short complexes of modules satisfies the cycle-and-boundary
criterion**: a cycle of the source whose image is a boundary is a boundary, and every cycle of
the target is the image of a cycle of the source modulo a boundary. -/
private lemma shortComplex_criteria_of_quasiIso {S T : ShortComplex (ModuleCat.{u} R)}
    (a : S ⟶ T) (ha : ShortComplex.QuasiIso a) :
    (∀ x : S.X₂, S.g.hom x = 0 →
      (∃ y : T.X₁, T.f.hom y = a.τ₂.hom x) → ∃ y : S.X₁, S.f.hom y = x) ∧
    (∀ y : T.X₂, T.g.hom y = 0 →
      ∃ x : S.X₂, S.g.hom x = 0 ∧ ∃ w : T.X₁, T.f.hom w = y - a.τ₂.hom x) := by
  rw [ShortComplex.quasiIso_iff, ConcreteCategory.isIso_iff_bijective] at ha
  have hz (x : S.X₂) (hx : S.g.hom x = 0) : T.g.hom (a.τ₂.hom x) = 0 := by
    simpa [hx] using congrArg (fun k : S.X₂ ⟶ T.X₃ => k.hom x) a.comm₂₃
  refine ⟨fun x hx hbound => ?_, fun y hy => ?_⟩
  · apply (cycleClass_eq_zero S ⟨x, hx⟩).mp
    apply ha.1
    rw [map_zero, cycleClass_naturality a ⟨x, hx⟩ ⟨a.τ₂.hom x, hz x hx⟩ rfl]
    exact (cycleClass_eq_zero T _).mpr hbound
  · obtain ⟨c, hc⟩ := ha.2 (cycleClass T ⟨y, hy⟩)
    obtain ⟨x, rfl⟩ := cycleClass_surjective S c
    refine ⟨x.val, x.property, ?_⟩
    apply (cycleClass_eq_zero T (⟨y, hy⟩ - ⟨a.τ₂.hom x.val, hz x.val x.property⟩)).mp
    rw [map_sub, ← cycleClass_naturality a x ⟨a.τ₂.hom x.val, hz x.val x.property⟩ rfl, hc,
      sub_self]

end ShortComplex

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-- The differential of the underlying cochain complex, read on the underlying module, for an
arbitrary target degree `m` with `n + 1 = m`. -/
lemma toCochainComplex_d_val (M : DifferentialGradedModule.{u, u, u} A) (n m : ℤ)
    (hm : n + 1 = m)
    (x : M.grading n) : (M.toCochainComplex.d n m x : M.grading m).val = M.d x := by
  subst m
  rw [toCochainComplex_d]
  rfl

/-- **The cycle-and-boundary criterion is necessary**, the converse of
`DifferentialGradedModule.quasiIso_of_isQuasiIsomorphism`: a homomorphism of differential graded
modules whose underlying cochain map is a quasi-isomorphism satisfies the criterion. -/
theorem isQuasiIsomorphism_of_quasiIso {M N : DifferentialGradedModule.{u, u, u} A} (f : M ⟶ N)
    (hf : QuasiIso ((forgetToCochainComplex A).map f)) : IsQuasiIsomorphism f := by
  intro n
  have hq : QuasiIsoAt f.toCochainMap n := (quasiIso_iff _).mp hf n
  have h := shortComplex_criteria_of_quasiIso _
    ((quasiIsoAt_iff' f.toCochainMap (n - 1) n (n + 1) (by simp) (by simp)).mp hq)
  change (∀ x : M.grading n, M.toCochainComplex.d n (n + 1) x = 0 →
      (∃ z : N.grading (n - 1), N.toCochainComplex.d (n - 1) n z = f.gradedMap n x) →
        ∃ z : M.grading (n - 1), M.toCochainComplex.d (n - 1) n z = x) ∧
    (∀ y : N.grading n, N.toCochainComplex.d n (n + 1) y = 0 →
      ∃ x : M.grading n, M.toCochainComplex.d n (n + 1) x = 0 ∧
        ∃ z : N.grading (n - 1), N.toCochainComplex.d (n - 1) n z = y - f.gradedMap n x) at h
  have hd {P : DifferentialGradedModule.{u, u, u} A} {k m : ℤ} (hm : k + 1 = m)
      (x : P.grading k) (y : P.grading m) :
      P.toCochainComplex.d k m x = y ↔ P.d x.val = y.val := by
    refine Subtype.ext_iff.trans ?_
    rw [toCochainComplex_d_val P k m hm]
  refine ⟨fun y hy hdy => ?_, fun x hx hdx ⟨z, hz, hdz⟩ => ?_⟩
  · obtain ⟨x, hx, z, hz⟩ := h.2 ⟨y, hy⟩ ((hd rfl _ 0).2 hdy)
    exact ⟨x.val, x.property, (hd rfl _ 0).1 hx, z.val, z.property, (hd (by lia) _ _).1 hz⟩
  · obtain ⟨y, hy⟩ := h.1 ⟨x, hx⟩ ((hd rfl _ 0).2 hdx) ⟨⟨z, hz⟩, (hd (by lia) _ _).2 hdz⟩
    exact ⟨y.val, y.property, (hd (by lia) _ _).1 hy⟩

/-- A homomorphism of differential graded modules commutes with the differentials, on an
element. -/
private lemma hom_d_apply {M N : DifferentialGradedModule.{u, u, u} A} (h : M ⟶ N) (x : M.M) :
    h.toFun (M.d x) = N.d (h.toFun x) :=
  (LinearMap.congr_fun h.map_d x : h.toFun (M.d x) = N.d (h.toFun x))

/-! ### The product of a family of homomorphisms -/

section ProductMap

variable {ι : Type u} {M N : ι → DifferentialGradedModule.{u, u, u} A}

/-- The components of an element killed by the differential of a product are killed by the
differentials of the factors. -/
private lemma d_π_apply_eq_zero {M : ι → DifferentialGradedModule.{u, u, u} A}
    (y : (product M).M) (hdy : (product M).d y = 0) (i : ι) :
    (M i).d ((product.π M i).toFun y) = 0 := by
  rw [← hom_d_apply (product.π M i) y, hdy, map_zero]

/-- **The product of a family of homomorphisms** `f i : M i ⟶ N i`, as a homomorphism
`∏ᵢ M i ⟶ ∏ᵢ N i`. -/
def productMap (f : ∀ i, M i ⟶ N i) : product M ⟶ product N :=
  product.lift N fun i => product.π M i ≫ f i

/-- The `i`-th projection of `productMap f` is the `i`-th projection followed by `f i`. -/
@[simp] theorem productMap_comp_π (f : ∀ i, M i ⟶ N i) (i : ι) :
    productMap f ≫ product.π N i = product.π M i ≫ f i :=
  product.π_lift N _ i

/-- On elements, the `i`-th component of `productMap f x` is `f i` applied to the `i`-th
component of `x`. -/
@[simp] theorem π_productMap_apply (f : ∀ i, M i ⟶ N i) (i : ι) (x : (product M).M) :
    (product.π N i).toFun ((productMap f).toFun x) = (f i).toFun ((product.π M i).toFun x) :=
  rfl

/-- A product of quasi-isomorphisms is a quasi-isomorphism, in the cycle-and-boundary form. -/
theorem isQuasiIsomorphism_productMap (f : ∀ i, M i ⟶ N i)
    (hf : ∀ i, IsQuasiIsomorphism (f i)) : IsQuasiIsomorphism (productMap f) := by
  classical
  intro n
  constructor
  · intro y hy hdy
    choose x hx hdx z hz hzeq using fun i =>
      (hf i n).1 _ ((product.mem_grading_iff N y).1 hy i) (d_π_apply_eq_zero y hdy i)
    obtain ⟨X, hXmem, hXπ⟩ := product.exists_mem_grading M n x hx
    obtain ⟨Z, hZmem, hZπ⟩ := product.exists_mem_grading N (n - 1) z hz
    refine ⟨X, hXmem, ?_, Z, hZmem, ?_⟩
    · refine product.eq_zero_of_π_eq_zero M _ fun i => ?_
      rw [hom_d_apply (product.π M i) X, hXπ i, hdx i]
    · refine product.eq_of_π_eq N fun i => ?_
      rw [hom_d_apply (product.π N i) Z, hZπ i, hzeq i, map_sub, π_productMap_apply, hXπ i]
  · intro y hy hdy ⟨z, hzmem, hzeq⟩
    have hzi : ∀ i, (product.π N i).toFun z ∈ (N i).grading (n - 1) :=
      (product.mem_grading_iff N z).1 hzmem
    have hzeqi : ∀ i, (N i).d ((product.π N i).toFun z) = (f i).toFun ((product.π M i).toFun y) :=
      fun i => by rw [← hom_d_apply (product.π N i) z, hzeq, π_productMap_apply]
    choose w hw hweq using fun i =>
      (hf i n).2 _ ((product.mem_grading_iff M y).1 hy i) (d_π_apply_eq_zero y hdy i)
        ⟨_, hzi i, hzeqi i⟩
    obtain ⟨W, hWmem, hWπ⟩ := product.exists_mem_grading M (n - 1) w hw
    refine ⟨W, hWmem, product.eq_of_π_eq M fun i => ?_⟩
    rw [hom_d_apply (product.π M i) W, hWπ i, hweq i]

/-- A product of quasi-isomorphisms is a quasi-isomorphism, in Mathlib's sense for the
underlying cochain maps. -/
theorem quasiIso_productMap (f : ∀ i, M i ⟶ N i)
    (hf : ∀ i, QuasiIso ((forgetToCochainComplex A).map (f i))) :
    QuasiIso ((forgetToCochainComplex A).map (productMap f)) :=
  quasiIso_of_isQuasiIsomorphism _
    (isQuasiIsomorphism_productMap f fun i => isQuasiIsomorphism_of_quasiIso (f i) (hf i))

end ProductMap

/-! ### The product in the homotopy category -/

section HomotopyProduct

variable {ι : Type u} (f : ι → DifferentialGradedModule.{u, u, u} A)

/-- **A homotopy into a product is determined componentwise.** Given homotopies between the
components of two homomorphisms into `∏ᵢ f i`, their assembly — a degree `-1` map into the
product, obtained from `DifferentialGradedModule.exists_productLift` — is a homotopy between the
two homomorphisms themselves. -/
@[no_expose]
def productHomotopy {T : DifferentialGradedModule.{u, u, u} A} {a b : T ⟶ product f}
    (h : ∀ i, Homotopic (a ≫ product.π f i) (b ≫ product.π f i)) : Homotopy a b :=
  let hc : ∀ i, Homotopy (a ≫ product.π f i) (b ≫ product.π f i) :=
    fun i => Classical.choice (h i)
  let hex := exists_productLift (product.π f) (product.eq_zero_of_π_eq_zero f)
    (product.exists_mem_grading f) (-1) (fun i => (hc i).toLinearMap)
    (fun i x y => map_add _ x y)
    (fun i r x => by
      rw [show (r : R) • x = (algebraMap R (MulOpposite A.A) r) • x from
        (IsScalarTower.algebraMap_smul _ r x).symm, map_smul,
        IsScalarTower.algebraMap_smul])
    (fun i c x => map_smul _ (MulOpposite.op c) x)
    (fun i n x hx => by
      rw [show n + (-1 : ℤ) = n - 1 from by ring]
      exact (hc i).map_grading n x hx)
  { toLinearMap :=
      { toFun := hex.choose
        map_add' := hex.choose_spec.1
        map_smul' := fun c x => by
          rw [← MulOpposite.op_unop c]
          exact hex.choose_spec.2.2.1 c.unop x }
    map_grading := fun n x hx => by
      have hh := hex.choose_spec.2.2.2.1 n x hx
      rwa [show n + (-1 : ℤ) = n - 1 from by ring] at hh
    homotopy_eq := fun x => product.eq_of_π_eq f fun i => by
      have hπ := hex.choose_spec.2.2.2.2
      have key : (product.π f i).toFun ((product f).d (hex.choose x) + hex.choose (T.d x))
          = (product.π f i).toFun (a.toFun x) - (product.π f i).toFun (b.toFun x) := by
        rw [map_add, hom_d_apply (product.π f i) (hex.choose x), hπ i x, hπ i (T.d x)]
        exact ((hc i).homotopy_eq x).symm
      rw [map_sub]
      exact key.symm }

/-- Homomorphisms into a product whose components are pairwise homotopic are themselves
homotopic. -/
theorem homotopic_of_π_homotopic {T : DifferentialGradedModule.{u, u, u} A} {a b : T ⟶ product f}
    (h : ∀ i, Homotopic (a ≫ product.π f i) (b ≫ product.π f i)) : Homotopic a b :=
  ⟨productHomotopy f h⟩

/-- **The universal property of the product in the homotopy category.** A family of homotopy
classes of homomorphisms into the factors is the family of components of exactly one homotopy
class of homomorphisms into the product. -/
theorem existsUnique_toHomotopyCategory_lift {Y : HomotopyCategory.{u, u, u} A}
    (a : ∀ i, Y ⟶ (toHomotopyCategory.{u, u, u} A).obj (f i)) :
    ∃! l : Y ⟶ (toHomotopyCategory.{u, u, u} A).obj (product f),
      ∀ i, l ≫ (toHomotopyCategory.{u, u, u} A).map (product.π f i) = a i := by
  classical
  let q := toHomotopyCategory.{u, u, u} A
  let g : ∀ i, Y.as ⟶ f i := fun i => q.preimage (a i)
  let l₀ : Y.as ⟶ product f := product.lift f g
  have hfac : ∀ i, q.map (l₀ ≫ product.π f i) = a i := fun i => by
    rw [show l₀ ≫ product.π f i = g i from product.π_lift f g i]
    exact q.map_preimage (a i)
  refine ⟨q.map l₀, fun i => (q.map_comp _ _).symm.trans (hfac i), fun m hm => ?_⟩
  · let m₀ : Y.as ⟶ product f := q.preimage m
    have hpre : q.map m₀ = m := q.map_preimage m
    have hcomp : ∀ i, q.map (m₀ ≫ product.π f i) = q.map (l₀ ≫ product.π f i) := fun i => by
      rw [q.map_comp, hpre, hfac i]
      exact hm i
    exact hpre.symm.trans
      ((CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) _ _).mpr
        (homotopic_of_π_homotopic f fun i =>
          (CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) _ _).mp (hcomp i)))

/-- **The image of the product fan in the homotopy category is a limit fan.** -/
@[no_expose]
def isLimit_toHomotopyCategory_mapCone_product :
    IsLimit ((toHomotopyCategory.{u, u, u} A).mapCone (Fan.mk (product f) (product.π f))) :=
  IsLimit.ofExistsUnique fun s => by
    obtain ⟨l, hl, hu⟩ := existsUnique_toHomotopyCategory_lift f fun i => s.π.app ⟨i⟩
    exact ⟨l, fun ⟨i⟩ => hl i, fun m hm => hu m fun i => hm ⟨i⟩⟩

end HomotopyProduct

/-! ### The product fan of the homotopy category -/

section HomotopyProductFan

variable {ι : Type u} (F : ι → HomotopyCategory.{u, u, u} A)

/-- The fan in the homotopy category `K(A, d)` whose vertex is the product of the underlying
differential graded modules and whose projections are the classes of the projections. -/
def homotopyProductFan : Fan F :=
  Fan.mk ((toHomotopyCategory.{u, u, u} A).obj (product fun i => (F i).as))
    fun i => (toHomotopyCategory.{u, u, u} A).map (product.π (fun i => (F i).as) i)

/-- **`K(A, d)` has products, computed on the underlying differential graded modules** (Tag
09JR), with the product object available by name. -/
@[no_expose]
def isLimit_homotopyProductFan : IsLimit (homotopyProductFan F) :=
  IsLimit.ofExistsUnique fun s => by
    obtain ⟨l, hl, hu⟩ :=
      existsUnique_toHomotopyCategory_lift (fun i => (F i).as) fun i => s.π.app ⟨i⟩
    exact ⟨l, fun ⟨i⟩ => hl i, fun m hm => hu m fun i => hm ⟨i⟩⟩

end HomotopyProductFan

/-! ### Products in the derived category -/

section Derived

variable {ι : Type u}

/-- A product of quasi-isomorphisms of `K(A, d)` is a quasi-isomorphism: the lift between the
fans `DifferentialGradedModule.homotopyProductFan` induced by a family of quasi-isomorphisms is a
quasi-isomorphism. -/
theorem quasiIsomorphisms_homotopyProductFan_lift (F G : ι → HomotopyCategory.{u, u, u} A)
    (φ : ∀ i, F i ⟶ G i) (hφ : ∀ i, quasiIsomorphisms' A (φ i)) :
    quasiIsomorphisms' A ((isLimit_homotopyProductFan G).lift
      (Fan.mk (homotopyProductFan F).pt fun i => (homotopyProductFan F).proj i ≫ φ i)) := by
  classical
  let q := toHomotopyCategory.{u, u, u} A
  let φ₀ : ∀ i, (F i).as ⟶ (G i).as := fun i => q.preimage (φ i)
  have he : (isLimit_homotopyProductFan G).lift
      (Fan.mk (homotopyProductFan F).pt fun i => (homotopyProductFan F).proj i ≫ φ i)
      = q.map (productMap φ₀) := by
    refine (isLimit_homotopyProductFan G).hom_ext fun ⟨i⟩ => ?_
    rw [IsLimit.fac]
    show q.map (product.π (fun i => (F i).as) i) ≫ φ i
      = q.map (productMap φ₀) ≫ q.map (product.π (fun i => (G i).as) i)
    rw [← q.map_comp, productMap_comp_π φ₀ i, q.map_comp, q.map_preimage]
  rw [he]
  exact (quasiIsomorphisms_map_iff' A (productMap φ₀)).2
    (quasiIso_productMap φ₀ fun i => hφ i (φ₀ i) (q.map_preimage (φ i)))

/-- **The image of the product fan in the derived category is a limit fan.** -/
@[no_expose]
def isLimit_q_mapCone_product (f : ι → DifferentialGradedModule.{u, u, u} A) :
    IsLimit ((toHomotopyCategory.{u, u, u} A ⋙ (quasiIsomorphisms' A).Q).mapCone
      (Fan.mk (product f) (product.π f))) := by
  classical
  let q := toHomotopyCategory.{u, u, u} A
  let L := (quasiIsomorphisms' A).Q
  refine IsLimit.ofExistsUnique fun s => ?_
  let Y : HomotopyCategory.{u, u, u} A := L.objPreimage s.pt
  let e : L.obj Y ≅ s.pt := L.objObjPreimageIso s.pt
  obtain ⟨g, hg, hgu⟩ := localized_product_hom_existsUnique L (quasiIsomorphisms' A)
    homotopyProductFan isLimit_homotopyProductFan quasiIsomorphisms_homotopyProductFan_lift
    (fun i => q.obj (f i)) Y fun i => e.hom ≫ s.π.app ⟨i⟩
  refine ⟨e.inv ≫ g, fun ⟨i⟩ => ?_, fun m hm => ?_⟩
  · change (e.inv ≫ g) ≫ L.map (q.map (product.π f i)) = s.π.app ⟨i⟩
    rw [Category.assoc,
      show g ≫ L.map (q.map (product.π f i)) = e.hom ≫ s.π.app ⟨i⟩ from hg i,
      Iso.inv_hom_id_assoc]
  · have key : e.hom ≫ m = g := by
      refine hgu (e.hom ≫ m) fun i => ?_
      change (e.hom ≫ m) ≫ L.map (q.map (product.π f i)) = e.hom ≫ s.π.app ⟨i⟩
      rw [Category.assoc,
        show m ≫ L.map (q.map (product.π f i)) = s.π.app ⟨i⟩ from hm ⟨i⟩]
    change m = e.inv ≫ g
    rw [← key]
    exact (Iso.inv_hom_id_assoc e m).symm

end Derived

/-- *"Products in `D(A, d)` are obtained by taking products of differential graded modules"*,
in the form that the canonical functor
`Mod_{(A,d)} ⥤ D(A, d)` — the quotient by homotopy followed by the localization at the
quasi-isomorphisms — preserves products. Preservation of limits of discrete diagrams records both
that the image of a product is a product and that its projections are the images of the canonical
ones, including for the empty family. -/
@[stacks 09QI "products"]
instance derivedCategoryQ_preservesProducts (A : DifferentialGradedAlgebra.{u, u} R) (ι : Type u) :
    PreservesLimitsOfShape (Discrete ι)
      (toHomotopyCategory.{u, u, u} A ⋙ (quasiIsomorphisms' A).Q) := by
  classical
  refine ⟨fun {F} => ?_⟩
  have := preservesLimit_of_preserves_limit_cone (product.isLimit (F.obj ∘ Discrete.mk))
    (isLimit_q_mapCone_product (F.obj ∘ Discrete.mk))
  exact preservesLimit_of_iso_diagram _ (Discrete.natIsoFunctor (F := F)).symm

/-- The abstract product `∏ᶜ f` of differential graded modules is carried to a product in the
derived category: the fan whose vertex is the image of `∏ᶜ f` and whose projections are the
images of the canonical ones is a limit fan. -/
theorem nonempty_isLimit_derivedProductFan {ι : Type u}
    (f : ι → DifferentialGradedModule.{u, u, u} A) :
    Nonempty (IsLimit (Fan.mk
      ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory.{u, u, u} A).obj (∏ᶜ f)))
      fun i => (quasiIsomorphisms' A).Q.map ((toHomotopyCategory.{u, u, u} A).map (Pi.π f i)))) :=
  ⟨IsLimit.ofExistsUnique fun s => by
    obtain ⟨l, hl, hu⟩ := (isLimitOfPreserves
        (toHomotopyCategory.{u, u, u} A ⋙ (quasiIsomorphisms' A).Q)
      (productIsProduct f)).existsUnique
        (CategoryTheory.Limits.Cone.mk s.pt (Discrete.natTrans fun j => s.π.app j))
    exact ⟨l, fun j => hl j, fun m hm => hu m fun j => hm j⟩⟩

end DifferentialGradedModule

end
