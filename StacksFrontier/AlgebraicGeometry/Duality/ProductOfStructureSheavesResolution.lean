module

public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ProductOfStructureSheavesNotQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.SheafComplexLocality.Basic
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.TruncationTower
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CohomologyOfAProduct

/-!
# A product of injective resolutions of the structure sheaf

Let `Y` be a scheme, let `𝒪_Y → J` be an injective resolution of the structure sheaf, read as a
cochain complex indexed by `ℤ`, and let `ι` be a type. The product complex `∏_{k ∈ ι} J` is a
resolution of the product module `∏_{k ∈ ι} 𝒪_Y`: the canonical morphism

`(∏_{k ∈ ι} 𝒪_Y)[0] ⟶ ∏_{k ∈ ι} J`

is a quasi-isomorphism. Products of sheaves are not exact in general, and the content is Serre
vanishing ([Stacks, Tag 01XB]): over an affine open `W` the complex of sections `Γ(W, J)` computes
the cohomology of `𝒪_Y` on `W`, which vanishes in positive degrees, so every cocycle of
`Γ(W, ∏_k J) = ∏_k Γ(W, J)` of positive degree is a coboundary, and the affine opens form a basis.
In degree zero the statement is left exactness of sections, which commutes with products.

This is the computation behind [Stacks, Tag 0GEU]: `∏_k J` is the internal Hom complex out of
`(⊕_k 𝒪_Y)[0]` into `J`, so it represents `R𝓗om_{𝒪_Y}(⊕_k 𝒪_Y, 𝒪_Y)`, and the quasi-isomorphism
identifies that object with `∏_k 𝒪_Y` in degree zero.

## Main results

* `Stacks.Duality.ProductResolution.exact_sections_cochainComplex` — over an affine open, the
  sections of the resolution are exact in positive degrees.
* `Stacks.Duality.ProductResolution.exactAt_pi_cochainComplex` — the product of copies of the
  resolution is exact in positive degrees.
* `Stacks.Duality.ProductResolution.quasiIso_piLift` — the canonical morphism
  `(∏_k 𝒪_Y)[0] ⟶ ∏_k J` is a quasi-isomorphism.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 0GEU](https://stacks.math.columbia.edu/tag/0GEU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.Duality.ProductResolution

universe u

variable {Y : Scheme.{u}}

/-- The inverse of an isomorphism of sheaves of modules undoes it on sections. -/
lemma iso_inv_hom_apply {R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    {A B : SheafOfModules.{u} R} (e : A ≅ B) (V : (Opens Y)ᵒᵖ) (x : A.val.obj V) :
    e.inv.val.app V (e.hom.val.app V x) = x := by
  show (e.hom ≫ e.inv).val.app V x = x
  rw [e.hom_inv_id]
  rfl

/-- The isomorphism of sheaves of modules undoes its inverse on sections. -/
lemma iso_hom_inv_apply {R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    {A B : SheafOfModules.{u} R} (e : A ≅ B) (V : (Opens Y)ᵒᵖ) (x : B.val.obj V) :
    e.hom.val.app V (e.inv.val.app V x) = x := by
  show (e.inv ≫ e.hom).val.app V x = x
  rw [e.inv_hom_id]
  rfl

/-- An element of the target of an isomorphism whose inverse image is zero is zero. -/
private lemma eq_zero_of_iso_inv_apply_eq_zero
    {R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    {A B : SheafOfModules.{u} R} (e : A ≅ B) (V : (Opens Y)ᵒᵖ)
    (x : B.val.obj V) (h : e.inv.val.app V x = 0) : x = 0 :=
  (iso_hom_inv_apply e V x).symm.trans ((congrArg (e.hom.val.app V) h).trans (map_zero _))

variable (R0 : InjectiveResolution (SheafOfModules.unit Y.ringCatSheaf))

/-- **Serre vanishing on the sections of an injective resolution.** Over an affine open `W`, a
cocycle of positive degree of the complex of sections `Γ(W, J)` of an injective resolution of
`𝒪_Y` is a coboundary. This is [Stacks, Tag 01XB] read through the computation of the right
derived functors of sections by an injective resolution. -/
lemma exact_sections_cocomplex (W : Y.Opens) (hW : IsAffineOpen W) (n : ℕ)
    (y : (R0.cocomplex.X (n + 1)).val.obj (op W))
    (hy : (R0.cocomplex.d (n + 1) (n + 2)).val.app (op W) y = 0) :
    ∃ x : (R0.cocomplex.X n).val.obj (op W), (R0.cocomplex.d n (n + 1)).val.app (op W) x = y := by
  have hz := isZero_rightDerived_evaluation_of_isAffineOpen Y
    (SheafOfModules.unit Y.ringCatSheaf) W hW (n + 1) (Nat.succ_pos n)
  have h2 := hz.of_iso (R0.isoRightDerivedObj
    (SheafOfModules.evaluation Y.ringCatSheaf (op W)) (n + 1)).symm
  have hex : (((SheafOfModules.evaluation Y.ringCatSheaf (op W)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj R0.cocomplex).ExactAt (n + 1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 h2
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)] at hex
  exact (ShortComplex.moduleCat_exact_iff _).1 hex y hy

/-- The resolution, as a cochain complex indexed by `ℤ`. -/
abbrev J : CochainComplex (SheafOfModules.{u} Y.ringCatSheaf) ℤ := R0.cochainComplex

/-- **Serre vanishing on the sections of the `ℤ`-indexed resolution.** Over an affine open, a
cocycle of positive degree of `Γ(W, J)` is a coboundary. -/
lemma exact_sections_cochainComplex (W : Y.Opens) (hW : IsAffineOpen W) (i : ℤ) (hi : 0 < i)
    (y : ((J R0).X i).val.obj (op W)) (hy : ((J R0).d i (i + 1)).val.app (op W) y = 0) :
    ∃ x : ((J R0).X (i - 1)).val.obj (op W), ((J R0).d (i - 1) i).val.app (op W) x = y := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n + 1 : ℕ) := ⟨i.toNat - 1, by omega⟩
  have hd1 := R0.cochainComplex_d ((n + 1 : ℕ) : ℤ) ((n + 1 : ℕ) + 1 : ℤ) (n + 1) (n + 2) rfl
    (by push_cast; ring)
  have hd0 := R0.cochainComplex_d ((n + 1 : ℕ) - 1 : ℤ) ((n + 1 : ℕ) : ℤ) n (n + 1)
    (by push_cast; ring) rfl
  set y' := (R0.cochainComplexXIso ((n + 1 : ℕ) : ℤ) (n + 1) rfl).hom.val.app (op W) y
  have hy' : (R0.cocomplex.d (n + 1) (n + 2)).val.app (op W) y' = 0 := by
    rw [hd1] at hy
    exact eq_zero_of_iso_inv_apply_eq_zero _ _ _ hy
  obtain ⟨x', hx'⟩ := exact_sections_cocomplex R0 W hW n y' hy'
  refine ⟨(R0.cochainComplexXIso ((n + 1 : ℕ) - 1 : ℤ) n (by push_cast; ring)).inv.val.app
    (op W) x', ?_⟩
  rw [hd0]
  show (R0.cochainComplexXIso ((n + 1 : ℕ) : ℤ) (n + 1) rfl).inv.val.app (op W)
    ((R0.cocomplex.d n (n + 1)).val.app (op W)
      ((R0.cochainComplexXIso ((n + 1 : ℕ) - 1 : ℤ) n (by push_cast; ring)).hom.val.app (op W)
        ((R0.cochainComplexXIso ((n + 1 : ℕ) - 1 : ℤ) n
          (by push_cast; ring)).inv.val.app (op W) x'))) = y
  rw [iso_hom_inv_apply, hx']
  exact iso_inv_hom_apply _ _ _

/-- The degree-zero part of the resolution: on the sections over any open, `𝒪_Y(V)` is the
kernel of `J^0(V) ⟶ J^1(V)`, the inclusion being the augmentation `R0.ι'`. -/
lemma exact_sections_zero (V : (Opens Y)ᵒᵖ) :
    Function.Injective ((R0.ι'.f 0).val.app V) ∧
      ∀ y : ((J R0).X 0).val.obj V, ((J R0).d 0 1).val.app V y = 0 →
        ∃ o : (SheafOfModules.unit Y.ringCatSheaf).val.obj V, (R0.ι'.f 0).val.app V o = y := by
  have : (SheafOfModules.evaluation Y.ringCatSheaf V).PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  have hS : (ShortComplex.mk (R0.ι.f 0) (R0.cocomplex.d 0 1) R0.ι_f_zero_comp_complex_d).Exact :=
    ShortComplex.exact_of_f_is_kernel _ R0.isLimitKernelFork
  have hSE := hS.map_of_mono_of_preservesKernel (SheafOfModules.evaluation Y.ringCatSheaf V)
    inferInstance inferInstance
  have hmono : Function.Injective ((SheafOfModules.evaluation Y.ringCatSheaf V).map (R0.ι.f 0)) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hd := R0.cochainComplex_d (0 : ℤ) 1 0 1 rfl rfl
  set e0 := R0.cochainComplexXIso (0 : ℤ) 0 rfl
  set e1 := R0.cochainComplexXIso (1 : ℤ) 1 rfl
  have hιapp : ∀ o, (R0.ι'.f 0).val.app V o =
      e0.inv.val.app V ((R0.ι.f 0).val.app V o) := fun o ↦
    congrArg (fun φ ↦ φ.val.app V o) R0.ι'_f_zero
  refine ⟨fun o o' h ↦ ?_, fun y hy ↦ ?_⟩
  · have h' := congrArg (e0.hom.val.app V) (((hιapp o).symm.trans h).trans (hιapp o'))
    exact hmono ((iso_hom_inv_apply e0 V _).symm.trans (h'.trans (iso_hom_inv_apply e0 V _)))
  · have hy1 : e1.inv.val.app V ((R0.cocomplex.d 0 1).val.app V (e0.hom.val.app V y)) = 0 :=
      (congrArg (fun φ ↦ φ.val.app V y) hd).symm.trans hy
    have hy' : (R0.cocomplex.d 0 1).val.app V (e0.hom.val.app V y) = 0 :=
      eq_zero_of_iso_inv_apply_eq_zero e1 V _ hy1
    obtain ⟨o, ho⟩ := (ShortComplex.moduleCat_exact_iff _).1 hSE (e0.hom.val.app V y) hy'
    exact ⟨o, (hιapp o).trans ((congrArg (e0.inv.val.app V) ho).trans (iso_inv_hom_apply e0 V y))⟩

section Generic

variable {T : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
  [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {ι : Type}

omit [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Sections of a product of complexes are families of sections.** Taking the coordinates of a
section over `V` of the degree-`i` term of a product of cochain complexes of sheaves of modules is
a bijection onto the families of sections of the factors. -/
lemma bijective_pi_coordinates (K : ι → CochainComplex (SheafOfModules.{u} R) ℤ)
    (i : ℤ) (V : (Opens T)ᵒᵖ) :
    Function.Bijective (fun (s : ((∏ᶜ K).X i).val.obj V) (k : ι) ↦
      ((Pi.π K k).f i).val.app V s) := by
  set P := piComparison (HomologicalComplex.eval _ (ComplexShape.up ℤ) i) K
  have heq : (fun (s : ((∏ᶜ K).X i).val.obj V) (k : ι) ↦ ((Pi.π K k).f i).val.app V s) =
      (fun (s : ((SheafOfModules.evaluation R V).obj
          (∏ᶜ fun k ↦ (K k).X i) : Type u)) (k : ι) ↦
        ((SheafOfModules.evaluation R V).map (Pi.π (fun k ↦ (K k).X i) k) s :
          ((SheafOfModules.evaluation R V).obj ((K k).X i) : Type u))) ∘
        (P.val.app V) := by
    funext s k
    exact (congrArg (fun φ ↦ φ.val.app V s)
      (piComparison_comp_π (HomologicalComplex.eval _ (ComplexShape.up ℤ) i) K k)).symm
  rw [heq]
  exact (bijective_piSections (fun k ↦ (K k).X i) V).comp
    (ConcreteCategory.bijective_of_isIso ((SheafOfModules.evaluation R V).map P))

omit [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The differential of a product of complexes acts coordinatewise. -/
lemma coord_d (K : ι → CochainComplex (SheafOfModules.{u} R) ℤ) (k : ι) (i j : ℤ)
    (V : (Opens T)ᵒᵖ) (s : ((∏ᶜ K).X i).val.obj V) :
    ((Pi.π K k).f j).val.app V (((∏ᶜ K).d i j).val.app V s) =
      ((K k).d i j).val.app V (((Pi.π K k).f i).val.app V s) :=
  congrArg (fun φ ↦ φ.val.app V s) ((Pi.π K k).comm i j).symm

omit [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Each coordinate of the restriction of a cocycle of a product of complexes is a cocycle. -/
private lemma d_coord_map_eq_zero (K : ι → CochainComplex (SheafOfModules.{u} R) ℤ) (k : ι)
    (i j : ℤ) {V W : Opens T} (f : W ⟶ V) (z : ((∏ᶜ K).X i).val.obj (op V))
    (hz : ((∏ᶜ K).d i j).val.app (op V) z = 0) :
    ((K k).d i j).val.app (op W)
      (((Pi.π K k).f i).val.app (op W) (((∏ᶜ K).X i).val.map f.op z)) = 0 :=
  (coord_d K k i j (op W) _).symm.trans
    ((congrArg (((Pi.π K k).f j).val.app (op W))
      ((PresheafOfModules.naturality_apply ((∏ᶜ K).d i j).val f.op z).trans
        ((congrArg (((∏ᶜ K).X j).val.map f.op) hz).trans (map_zero _)))).trans (map_zero _))

/-- **A product of complexes which are locally exact on a basis is exact.** If, over every member
of a basis of the topology, every cocycle of degree `i` of each factor is a coboundary, then the
product complex is exact in degree `i`. -/
lemma exactAt_pi_of_basis (K : ι → CochainComplex (SheafOfModules.{u} R) ℤ) (i : ℤ)
    {B : Set (Opens T)} (hB : Opens.IsBasis B)
    (h : ∀ (k : ι), ∀ W ∈ B, ∀ y : ((K k).X i).val.obj (op W),
      ((K k).d i (i + 1)).val.app (op W) y = 0 →
        ∃ x : ((K k).X (i - 1)).val.obj (op W), ((K k).d (i - 1) i).val.app (op W) x = y) :
    (∏ᶜ K).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)]
  refine Stacks.SheafOfModules.ComplexLocality.exact_of_locallyExact _ fun {V} z hz ↦ ?_
  refine ⟨Sieve.generate (fun W (_ : W ⟶ V) ↦ W ∈ B), ?_, ?_⟩
  · refine (Opens.mem_grothendieckTopology T).2 fun x hx ↦ ?_
    obtain ⟨W, hW, hxW, hWV⟩ := (Opens.isBasis_iff_nbhd.mp hB) hx
    exact ⟨W, homOfLE hWV, ⟨W, 𝟙 W, homOfLE hWV, hW, Category.id_comp _⟩, hxW⟩
  · rintro Z p ⟨W, a, b, hW, rfl⟩
    choose xk hxk using fun k ↦ h k W hW _ (d_coord_map_eq_zero K k i (i + 1) b z hz)
    obtain ⟨xW, hxW⟩ := (bijective_pi_coordinates K (i - 1) (op W)).2 xk
    have hdx : ((∏ᶜ K).d (i - 1) i).val.app (op W) xW = ((∏ᶜ K).X i).val.map b.op z := by
      refine (bijective_pi_coordinates K i (op W)).1 (funext fun k ↦ ?_)
      exact (coord_d K k (i - 1) i (op W) xW).trans
        ((congrArg (((K k).d (i - 1) i).val.app (op W)) (congrFun hxW k)).trans (hxk k))
    refine ⟨((∏ᶜ K).X (i - 1)).val.map a.op xW, ?_⟩
    refine (PresheafOfModules.naturality_apply ((∏ᶜ K).d (i - 1) i).val a.op xW).trans ?_
    refine (congrArg (((∏ᶜ K).X i).val.map a.op) hdx).trans ?_
    exact (PresheafOfModules.map_comp_apply ((∏ᶜ K).X i).val b.op a.op z).symm

omit [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A product of complexes whose factors vanish in degree `i` vanishes in degree `i`. -/
lemma isZero_pi_X (K : ι → CochainComplex (SheafOfModules.{u} R) ℤ) (i : ℤ)
    (h : ∀ k, IsZero ((K k).X i)) : IsZero ((∏ᶜ K).X i) :=
  (Stacks.Cohomology.ModuleComparison.isZero_pi h).of_iso
    (asIso (piComparison (HomologicalComplex.eval _ (ComplexShape.up ℤ) i) K))

/-- The product of morphisms out of modules in degree zero, as a morphism out of the product
module in degree zero. -/
def piLiftSingle (M : ι → SheafOfModules.{u} R) (K : ι → CochainComplex (SheafOfModules.{u} R) ℤ)
    (g : ∀ k, (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (M k) ⟶ K k) :
    (HomologicalComplex.single (SheafOfModules.{u} R) (ComplexShape.up ℤ) 0).obj (∏ᶜ M) ⟶
      ∏ᶜ K :=
  Pi.lift fun k ↦ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (Pi.π M k) ≫ g k

/-- The coordinates of the image under `piLiftSingle` of a section in degree zero. -/
lemma coord_piLiftSingle (M : ι → SheafOfModules.{u} R)
    (K : ι → CochainComplex (SheafOfModules.{u} R) ℤ)
    (g : ∀ k, (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (M k) ⟶ K k)
    (k : ι) (V : (Opens T)ᵒᵖ) (x : (∏ᶜ M).val.obj V) :
    ((Pi.π K k).f 0).val.app V (((piLiftSingle M K g).f 0).val.app V x) =
      ((g k).f 0).val.app V ((Pi.π M k).val.app V x) :=
  congrArg (fun φ : (HomologicalComplex.single (SheafOfModules.{u} R) (ComplexShape.up ℤ) 0).obj
      (∏ᶜ M) ⟶ K k ↦ (φ.f 0).val.app V x)
    (Pi.lift_comp_π (fun k ↦ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (Pi.π M k) ≫ g k)
      k)

/-- Degree zero of `quasiIso_piLiftSingle`: the product module is the kernel of the first
differential of the product complex, because it is so on every module of sections. -/
lemma quasiIsoAt_zero_piLiftSingle (M : ι → SheafOfModules.{u} R)
    (K : ι → CochainComplex (SheafOfModules.{u} R) ℤ)
    (g : ∀ k, (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (M k) ⟶ K k)
    (hneg : ∀ k (i : ℤ), i < 0 → IsZero ((K k).X i))
    (hinj : ∀ k (V : (Opens T)ᵒᵖ), Function.Injective (((g k).f 0).val.app V))
    (hsurj : ∀ k (V : (Opens T)ᵒᵖ) (y : ((K k).X 0).val.obj V), ((K k).d 0 1).val.app V y = 0 →
      ∃ o : (M k).val.obj V, ((g k).f 0).val.app V o = y) :
    QuasiIsoAt (piLiftSingle M K g) 0 := by
  rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp)]
  have h1 : ((HomologicalComplex.single (SheafOfModules.{u} R) (ComplexShape.up ℤ) 0).obj
      (∏ᶜ M)).d (-1) 0 = 0 :=
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (∏ᶜ M) (-1)
      (by decide)).eq_of_src _ _
  have h2 : ((HomologicalComplex.single (SheafOfModules.{u} R) (ComplexShape.up ℤ) 0).obj
      (∏ᶜ M)).d 0 1 = 0 :=
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (∏ᶜ M) 1
      (by decide)).eq_of_tgt _ _
  have h3 : (∏ᶜ K).d (-1) 0 = 0 :=
    (isZero_pi_X K (-1) fun k ↦ hneg k (-1) (by decide)).eq_of_src _ _
  refine (ShortComplex.quasiIso_iff_of_zeros _ h1 h2 h3).2 ⟨?_, ?_⟩
  · refine Stacks.SheafOfModules.ComplexLocality.exact_of_locallyExact _ fun {V} z hz ↦ ?_
    refine ⟨⊤, (Opens.grothendieckTopology T).top_mem V, fun W p _ ↦ ?_⟩
    choose o ho using fun k ↦ hsurj k (op W) _ (d_coord_map_eq_zero K k 0 1 p z hz)
    obtain ⟨x, hx⟩ := (bijective_piSections M (op W)).2 o
    refine ⟨x, (bijective_pi_coordinates K 0 (op W)).1 (funext fun k ↦ ?_)⟩
    exact (coord_piLiftSingle M K g k (op W) x).trans
      ((congrArg (((g k).f 0).val.app (op W)) (congrFun hx k)).trans (ho k))
  · refine (SheafOfModules.forget _).mono_of_mono_map ?_
    refine PresheafOfModules.mono_of_injective fun V x x' h ↦ ?_
    refine (bijective_piSections M V).1 (funext fun k ↦ hinj k V ?_)
    exact (coord_piLiftSingle M K g k V x).symm.trans
      ((congrArg (((Pi.π K k).f 0).val.app V) h).trans (coord_piLiftSingle M K g k V x'))

/-- **A product of resolutions which are locally exact on a basis is a resolution.** Let
`g_k : M_k[0] ⟶ K_k` be morphisms into complexes vanishing in negative degrees, such that on the
sections over every open `M_k` is the kernel of `K_k^0 ⟶ K_k^1`, and such that, over every member
of a basis of the topology, every positive-degree cocycle of `K_k` is a coboundary. Then the
induced morphism `(∏_k M_k)[0] ⟶ ∏_k K_k` is a quasi-isomorphism. -/
theorem quasiIso_piLiftSingle (M : ι → SheafOfModules.{u} R)
    (K : ι → CochainComplex (SheafOfModules.{u} R) ℤ)
    (g : ∀ k, (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (M k) ⟶ K k)
    {B : Set (Opens T)} (hB : Opens.IsBasis B)
    (hneg : ∀ k (i : ℤ), i < 0 → IsZero ((K k).X i))
    (hpos : ∀ k (i : ℤ), 0 < i → ∀ W ∈ B, ∀ y : ((K k).X i).val.obj (op W),
      ((K k).d i (i + 1)).val.app (op W) y = 0 →
        ∃ x : ((K k).X (i - 1)).val.obj (op W), ((K k).d (i - 1) i).val.app (op W) x = y)
    (hinj : ∀ k (V : (Opens T)ᵒᵖ), Function.Injective (((g k).f 0).val.app V))
    (hsurj : ∀ k (V : (Opens T)ᵒᵖ) (y : ((K k).X 0).val.obj V), ((K k).d 0 1).val.app V y = 0 →
      ∃ o : (M k).val.obj V, ((g k).f 0).val.app V o = y) :
    QuasiIso (piLiftSingle M K g) := by
  refine ⟨fun i ↦ ?_⟩
  have hne (hi : i ≠ 0) (h : (∏ᶜ K).ExactAt i) : QuasiIsoAt (piLiftSingle M K g) i :=
    (quasiIsoAt_iff_exactAt _ i (HomologicalComplex.exactAt_single_obj _ _ _ _ hi)).2 h
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · exact hne hi.ne (ShortComplex.exact_of_isZero_X₂ _ (isZero_pi_X K i fun k ↦ hneg k i hi))
  · exact quasiIsoAt_zero_piLiftSingle M K g hneg hinj hsurj
  · exact hne hi.ne' (exactAt_pi_of_basis K i hB fun k ↦ hpos k i hi)

end Generic

/-- **The product of copies of the resolution resolves the product module.** For an injective
resolution `𝒪_Y → J` and a type `ι`, the canonical morphism `(∏_k 𝒪_Y)[0] ⟶ ∏_k J` is a
quasi-isomorphism. -/
theorem quasiIso_piLiftSingle_cochainComplex (ι : Type) :
    QuasiIso (piLiftSingle (fun _ : ι ↦ SheafOfModules.unit Y.ringCatSheaf) (fun _ ↦ J R0)
      (fun _ ↦ R0.ι')) :=
  quasiIso_piLiftSingle (R := Y.ringCatSheaf) _ _ _ Y.isBasis_affineOpens
    (fun _ i hi ↦ CochainComplex.isZero_of_isStrictlyGE _ 0 i (by omega))
    (fun _ i hi W hW y hy ↦ exact_sections_cochainComplex R0 W hW i hi y hy)
    (fun _ V ↦ (exact_sections_zero R0 V).1) (fun _ V ↦ (exact_sections_zero R0 V).2)

end Stacks.Duality.ProductResolution

end
