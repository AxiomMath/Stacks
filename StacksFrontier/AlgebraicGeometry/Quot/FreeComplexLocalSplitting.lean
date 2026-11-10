module

public import StacksFrontier.AlgebraicGeometry.Quot.FreeComplexKernelFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.ResidueFieldTestScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.RingTheory.Matrix.FibreExactSplitting

/-!
# A complex of free modules splits near a point where its `H⁻¹` vanishes on fibres

Let `c` be a scheme of the big fppf site and `G` a complex of `𝒪`-modules on it whose terms in
degrees `-2, …, 1` are free, with differentials given by matrices of functions.  If `H⁻¹` of the
inverse image of `G` to every scheme over `c` vanishes, then at every point `x` of `c` the
complex `κ(x)^{n₂} → κ(x)^{n₁} → κ(x)^{n₀}` is exact in the middle, so on a principal open
neighbourhood of `x` the cokernel of `D₁` is free and split, and the degree-zero sections functor
of `G` there is the kernel functor of a matrix (Stacks 08JX, the last paragraph of the proof).

## Main definitions

* `AlgebraicGeometry.Space.matOf`: the matrix of functions of a morphism of free modules.
* `AlgebraicGeometry.Space.FreeTruncation`: free terms in degrees `-2, …, 1` with matrix
  differentials.
* `AlgebraicGeometry.Space.FreeTruncation.pull`: its inverse image along a morphism of schemes.

## Main results

* `AlgebraicGeometry.Space.matMap_matOf`: every morphism of free modules is the morphism of its
  matrix.
* `AlgebraicGeometry.Space.exists_basicOpen_test`: a principal open of a scheme as an object of
  the site.
* `AlgebraicGeometry.Space.FreeTruncation.exists_basicOpen_matKerIso`: the splitting near a
  point.

## References

* [Stacks Project, Tag 08JX](https://stacks.math.columbia.edu/tag/08JX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Matrix

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Morphisms of free modules are matrices -/

section Matrices

variable (T : BigFppfOver B S hS)

/-- **The matrix of functions of a morphism of free modules**: its entries are the values of its
components. -/
def matOf {n m : ℕ} (φ : freeObj (unitT T) n ⟶ freeObj (unitT T) m) :
    Matrix (Fin n) (Fin m) (Gam T) :=
  fun j k => unitEndValueHom T (biproduct.ι (fun _ : Fin n => unitT T) j ≫ φ ≫
    biproduct.π (fun _ : Fin m => unitT T) k)

/-- **Every morphism of free modules is the morphism of its matrix.** -/
theorem matMap_matOf {n m : ℕ} (φ : freeObj (unitT T) n ⟶ freeObj (unitT T) m) :
    matMap T (matOf T φ) = φ := by
  refine biproduct.hom_ext' _ _ fun j => biproduct.hom_ext _ _ fun k => ?_
  rw [Category.assoc, Category.assoc, ι_freeMat_π]
  exact funEnd_unitEndValueHom T _

/-- The matrix of the morphism of a matrix is the matrix. -/
theorem matOf_matMap {n m : ℕ} (M : Matrix (Fin n) (Fin m) (Gam T)) :
    matOf T (matMap T M) = M := by
  funext j k
  change unitEndValueHom T (biproduct.ι (fun _ : Fin n => unitT T) j ≫ freeMat _ _ ≫
    biproduct.π (fun _ : Fin m => unitT T) k) = M j k
  rw [ι_freeMat_π, unitEndValueHom_funEnd]

/-- A matrix is determined by its morphism of free modules. -/
theorem matMap_injective {n m : ℕ} :
    Function.Injective (fun M : Matrix (Fin n) (Fin m) (Gam T) => matMap T M) :=
  fun M N h => by
    rw [← matOf_matMap T M, ← matOf_matMap T N]
    exact congrArg (matOf T) h

end Matrices

/-! ### Principal opens as objects of the site -/

/-- The kernel of evaluation of global functions at a point is a prime ideal. -/
instance _root_.AlgebraicGeometry.Scheme.isPrime_ker_evaluation (X : Scheme.{u}) (x : X) :
    (RingHom.ker (X.evaluation ⊤ x trivial).hom).IsPrime :=
  RingHom.ker_isPrime _

/-- A point outside the kernel of evaluation of `a` lies in the image of a map onto `D(a)`. -/
private theorem mem_range_of_range_eq_basicOpen {X Y : Scheme.{u}} {g : Y ⟶ X} {a : Γ(X, ⊤)}
    (x : X) (hrange : Set.range g.base = (X.basicOpen a : Set _))
    (ha : a ∉ RingHom.ker (X.evaluation ⊤ x trivial).hom) : x ∈ Set.range g.base := by
  rw [hrange, SetLike.mem_coe, ← Scheme.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) _ x trivial]
  exact fun h => ha (RingHom.mem_ker.mpr h)

/-- **A principal open of a scheme of the site, as an object of the site**: an open immersion
onto `D(a)` along which `a` becomes a unit. -/
theorem exists_basicOpen_test (c : BigFppfOver B S hS) (a : Gam c) :
    ∃ (d : BigFppfOver B S hS) (t : d ⟶ c),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map t) ∧
        Set.range ((BigFppfOver.toScheme B S hS).map t).base =
          (((BigFppfOver.toScheme B S hS).obj c).basicOpen a : Set _) ∧
        IsUnit (((BigFppfOver.toScheme B S hS).map t).appTop.hom a) := by
  let X := (BigFppfOver.toScheme B S hS).obj c
  let V := X.basicOpen a
  have hV : B.Contains (V : Scheme.{u}) := B.contains_coe_opens c.left.property V
  obtain ⟨d, t, e, ht⟩ := exists_siteObject_toScheme_map_eq B S hS hV V.ι
  refine ⟨d, t, ?_, ?_, ?_⟩
  · rw [ht]; infer_instance
  · have hsurj : Set.range e.hom.base = Set.univ := Set.range_eq_univ.mpr fun y =>
      ⟨e.inv.base y, by
        change (e.inv ≫ e.hom).base y = y
        rw [e.inv_hom_id]
        rfl⟩
    rw [ht, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj, Set.image_univ,
      Scheme.Opens.range_ι]
  · rw [ht, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    refine IsUnit.map _ ?_
    rw [Scheme.Opens.ι_appTop]
    have hle : V.ι ''ᵁ ⊤ ≤ X.basicOpen a := by
      rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
    have h := (X.toRingedSpace.isUnit_res_basicOpen a).map (X.presheaf.map (homOfLE hle).op).hom
    have h2 : (X.presheaf.map (homOfLE (le_top : V.ι ''ᵁ ⊤ ≤ ⊤)).op).hom a =
        (X.presheaf.map (homOfLE hle).op).hom
          ((X.presheaf.map (homOfLE (X.toRingedSpace.basicOpen_le a)).op).hom a) := by
      have hm := X.presheaf.map_comp (homOfLE (X.toRingedSpace.basicOpen_le a)).op
        (homOfLE hle).op
      have hs : (homOfLE (le_top : V.ι ''ᵁ ⊤ ≤ ⊤)).op =
          (homOfLE (X.toRingedSpace.basicOpen_le a)).op ≫ (homOfLE hle).op := Subsingleton.elim _ _
      rw [hs, hm]
      rfl
    exact h2 ▸ h


/-! ### Complexes with free terms in degrees `-2, …, 1` -/

/-- **Free terms in degrees `-2, …, 1` with matrix differentials**, for a complex of
`𝒪`-modules on the algebraic space of a scheme `T`. -/
structure FreeTruncation {T : BigFppfOver B S hS}
    (G : CochainComplex (toposModules B S hS ((schemeSpaceFunctor B S hS).obj T)) ℤ) where
  /-- The rank in degree `-2`. -/
  n₂ : ℕ
  /-- The rank in degree `-1`. -/
  n₁ : ℕ
  /-- The rank in degree `0`. -/
  n₀ : ℕ
  /-- The rank in degree `1`. -/
  m : ℕ
  /-- The term in degree `-2` is free. -/
  e₂ : G.X (-2) ≅ freeObj (unitT T) n₂
  /-- The term in degree `-1` is free. -/
  e₁ : G.X (-1) ≅ freeObj (unitT T) n₁
  /-- The term in degree `0` is free. -/
  e₀ : G.X 0 ≅ freeObj (unitT T) n₀
  /-- The term in degree `1` is free. -/
  e₁' : G.X 1 ≅ freeObj (unitT T) m
  /-- The matrix of the differential out of degree `-2`. -/
  D₂ : Matrix (Fin n₂) (Fin n₁) (Gam T)
  /-- The matrix of the differential out of degree `-1`. -/
  D₁ : Matrix (Fin n₁) (Fin n₀) (Gam T)
  /-- The matrix of the differential out of degree `0`. -/
  D₀ : Matrix (Fin n₀) (Fin m) (Gam T)
  hd₂ : G.d (-2) (-1) = e₂.hom ≫ matMap T D₂ ≫ e₁.inv
  hd₁ : G.d (-1) 0 = e₁.hom ≫ matMap T D₁ ≫ e₀.inv
  hd₀ : G.d 0 1 = e₀.hom ≫ matMap T D₀ ≫ e₁'.inv

namespace FreeTruncation

variable {T : BigFppfOver B S hS}
  {G : CochainComplex (toposModules B S hS ((schemeSpaceFunctor B S hS).obj T)) ℤ}

/-- Free terms in degrees `-2, …, 1` give a `FreeTruncation`, the matrices being those of the
differentials. -/
def ofIsos {n₂ n₁ n₀ m : ℕ} (e₂ : G.X (-2) ≅ freeObj (unitT T) n₂)
    (e₁ : G.X (-1) ≅ freeObj (unitT T) n₁) (e₀ : G.X 0 ≅ freeObj (unitT T) n₀)
    (e₁' : G.X 1 ≅ freeObj (unitT T) m) : FreeTruncation G where
  n₂ := n₂
  n₁ := n₁
  n₀ := n₀
  m := m
  e₂ := e₂
  e₁ := e₁
  e₀ := e₀
  e₁' := e₁'
  D₂ := matOf T (e₂.inv ≫ G.d (-2) (-1) ≫ e₁.hom)
  D₁ := matOf T (e₁.inv ≫ G.d (-1) 0 ≫ e₀.hom)
  D₀ := matOf T (e₀.inv ≫ G.d 0 1 ≫ e₁'.hom)
  hd₂ := by rw [matMap_matOf]; simp
  hd₁ := by rw [matMap_matOf]; simp
  hd₀ := by rw [matMap_matOf]; simp

/-- The two matrices out of degrees `-2` and `-1` compose to zero. -/
theorem D₂_mul_D₁ (Φ : FreeTruncation G) : Φ.D₂ * Φ.D₁ = 0 := by
  refine matMap_injective T ?_
  change matMap T (Φ.D₂ * Φ.D₁) = matMap T 0
  rw [matMap_mul, matMap_zero]
  have h : (Φ.e₂.hom ≫ matMap T Φ.D₂ ≫ Φ.e₁.inv) ≫ (Φ.e₁.hom ≫ matMap T Φ.D₁ ≫ Φ.e₀.inv) = 0 := by
    rw [← Φ.hd₂, ← Φ.hd₁]
    exact G.d_comp_d (-2) (-1) 0
  calc matMap T Φ.D₂ ≫ matMap T Φ.D₁ = Φ.e₂.inv ≫
        ((Φ.e₂.hom ≫ matMap T Φ.D₂ ≫ Φ.e₁.inv) ≫ (Φ.e₁.hom ≫ matMap T Φ.D₁ ≫ Φ.e₀.inv)) ≫
          Φ.e₀.hom := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    _ = 0 := by rw [h, zero_comp, comp_zero]

variable {T' : BigFppfOver B S hS}

/-- Inverse image along a morphism of schemes, read through `f^*𝒪^n ≅ 𝒪^n`, carries a morphism
of free modules with a given matrix to the morphism of the pulled back matrix. -/
theorem pull_map_eq (t : T' ⟶ T) {X₀ X₁ : toposModules B S hS ((schemeSpaceFunctor B S hS).obj T)}
    {n m : ℕ} (a : X₀ ≅ freeObj (unitT T) n) (b : X₁ ≅ freeObj (unitT T) m)
    (M : Matrix (Fin n) (Fin m) (Gam T)) (g : X₀ ⟶ X₁) (hg : g = a.hom ≫ matMap T M ≫ b.inv) :
    ((toposModulePullbackData B S hS).pull ((schemeSpaceFunctor B S hS).map t)).map g =
      (((toposModulePullbackData B S hS).pull ((schemeSpaceFunctor B S hS).map t)).mapIso a ≪≫
          pullFreeIso ((schemeSpaceFunctor B S hS).map t) n).hom ≫
        matMap T' (M.map ((BigFppfOver.toScheme B S hS).map t).appTop.hom) ≫
        (((toposModulePullbackData B S hS).pull ((schemeSpaceFunctor B S hS).map t)).mapIso b ≪≫
          pullFreeIso ((schemeSpaceFunctor B S hS).map t) m).inv := by
  rw [← pullFreeIso_inv_map_matMap ((schemeSpaceFunctor B S hS).map t) t rfl M, hg]
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]

/-- **The inverse image of a `FreeTruncation`** along a morphism of schemes `t : T' ⟶ T`: the
terms stay free and the matrices are pulled back along `t`. -/
def pull (Φ : FreeTruncation G) (t : T' ⟶ T) :
    FreeTruncation ((((toposModulePullbackData B S hS).pull
      ((schemeSpaceFunctor B S hS).map t)).mapHomologicalComplex (ComplexShape.up ℤ)).obj G) where
  n₂ := Φ.n₂
  n₁ := Φ.n₁
  n₀ := Φ.n₀
  m := Φ.m
  e₂ := ((toposModulePullbackData B S hS).pull ((schemeSpaceFunctor B S hS).map t)).mapIso Φ.e₂ ≪≫
    pullFreeIso ((schemeSpaceFunctor B S hS).map t) _
  e₁ := ((toposModulePullbackData B S hS).pull ((schemeSpaceFunctor B S hS).map t)).mapIso Φ.e₁ ≪≫
    pullFreeIso ((schemeSpaceFunctor B S hS).map t) _
  e₀ := ((toposModulePullbackData B S hS).pull ((schemeSpaceFunctor B S hS).map t)).mapIso Φ.e₀ ≪≫
    pullFreeIso ((schemeSpaceFunctor B S hS).map t) _
  e₁' := ((toposModulePullbackData B S hS).pull ((schemeSpaceFunctor B S hS).map t)).mapIso Φ.e₁' ≪≫
    pullFreeIso ((schemeSpaceFunctor B S hS).map t) _
  D₂ := Φ.D₂.map ((BigFppfOver.toScheme B S hS).map t).appTop.hom
  D₁ := Φ.D₁.map ((BigFppfOver.toScheme B S hS).map t).appTop.hom
  D₀ := Φ.D₀.map ((BigFppfOver.toScheme B S hS).map t).appTop.hom
  hd₂ := pull_map_eq t Φ.e₂ Φ.e₁ Φ.D₂ _ Φ.hd₂
  hd₁ := pull_map_eq t Φ.e₁ Φ.e₀ Φ.D₁ _ Φ.hd₁
  hd₀ := pull_map_eq t Φ.e₀ Φ.e₁' Φ.D₀ _ Φ.hd₀

/-- **Exactness of the fibre at a point from the vanishing of `H⁻¹`**: if `H⁻¹` of the inverse
image of `G` to every scheme over `T` vanishes, the complex
`κ(x)^{n₂} → κ(x)^{n₁} → κ(x)^{n₀}` of the fibre at a point `x` is exact in the middle.  The
fibre is computed on the residue field of `x` as a test scheme, where the vanishing makes the
kernels orthogonal. -/
theorem fibre_exact (Φ : FreeTruncation G) (x : (BigFppfOver.toScheme B S hS).obj T)
    (hvan : ∀ (T' : BigFppfOver B S hS) (t : T' ⟶ T),
      IsZero (((((toposModulePullbackData B S hS).pull
        ((schemeSpaceFunctor B S hS).map t)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          G).homology (-1))) :
    ∀ v : Fin Φ.n₁ → (RingHom.ker
        (((BigFppfOver.toScheme B S hS).obj T).evaluation ⊤ x trivial).hom).ResidueField,
      v ᵥ* Φ.D₁.map (algebraMap _ _) = 0 → ∃ y, y ᵥ* Φ.D₂.map (algebraMap _ _) = v := by
  let φ := (((BigFppfOver.toScheme B S hS).obj T).evaluation ⊤ x trivial).hom
  refine fibre_exact_of_forall_dotProduct_eq_zero φ Φ.D₂ Φ.D₁ fun v l hv hl => ?_
  obtain ⟨T', f, ι, hι⟩ := exists_residueField_test T x
  let ψ := ((BigFppfOver.toScheme B S hS).map f).appTop.hom
  let ρ : ((BigFppfOver.toScheme B S hS).obj T).residueField x →+* Gam T' := ι.symm.toRingHom
  have hψ : ∀ a, ψ a = ρ (φ a) := fun a => by
    change ψ a = ι.symm (φ a)
    rw [← hι a, RingEquiv.symm_apply_apply]
  have hmap : ∀ {p q : ℕ} (D : Matrix (Fin p) (Fin q) (Gam T)),
      D.map ψ = (D.map φ).map ρ := fun D => by
    ext i j; exact hψ (D i j)
  let Φ' := Φ.pull f
  have hz := dotProduct_eq_zero_of_isZero_homology _ Φ'.e₂ Φ'.e₁ Φ'.e₀ Φ'.D₂ Φ'.D₁ Φ'.hd₂ Φ'.hd₁
    (hvan T' f) (ρ ∘ v) (by
      change (ρ ∘ v) ᵥ* Φ.D₁.map ψ = 0
      rw [hmap]
      funext k
      rw [← RingHom.map_vecMul ρ (Φ.D₁.map φ) v k, hv]
      simp)
    (ρ ∘ l) (by
      change Φ.D₂.map ψ *ᵥ (ρ ∘ l) = 0
      rw [hmap]
      funext k
      rw [← RingHom.map_mulVec ρ (Φ.D₂.map φ) l k, hl]
      simp)
  have h2 : ρ (v ⬝ᵥ l) = 0 := (RingHom.map_dotProduct ρ v l).trans hz
  have := congrArg ι h2
  simpa [ρ] using this


/-- **Near a point where `H⁻¹` vanishes on the fibres, the degree-zero sections functor of a
complex with free terms in degrees `-2, …, 1` is the kernel functor of a matrix.**  The fibre at
`x` is exact (`AlgebraicGeometry.Space.FreeTruncation.fibre_exact`), so on a principal open
neighbourhood of `x` the cokernel of `D₁` is free and split
(`Matrix.exists_away_split_of_fibre_exact`), and there the degree-zero sections functor is the
kernel functor of `s D₀` (`AlgebraicGeometry.Space.degreeZeroSectionsMatKerIso`). -/
theorem exists_basicOpen_matKerIso (Φ : FreeTruncation G)
    (x : (BigFppfOver.toScheme B S hS).obj T)
    (hvan : ∀ (T' : BigFppfOver B S hS) (t : T' ⟶ T),
      IsZero (((((toposModulePullbackData B S hS).pull
        ((schemeSpaceFunctor B S hS).map t)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          G).homology (-1))) :
    ∃ (d : BigFppfOver B S hS) (t : d ⟶ T),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map t) ∧
        x ∈ Set.range ((BigFppfOver.toScheme B S hS).map t).base ∧
        ∃ (r m : ℕ) (N : Matrix (Fin r) (Fin m) (Gam d)),
          Nonempty (degreeZeroSectionsFunctor (schemesOverCone ((schemeSpaceFunctor B S hS).obj d))
            ((((toposModulePullbackData B S hS).pull
              ((schemeSpaceFunctor B S hS).map t)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj G) ≅ matKerFunctor d N) := by
  obtain ⟨f, hf, r, hB⟩ := exists_away_split_of_fibre_exact _ Φ.D₂ Φ.D₁ Φ.D₂_mul_D₁
    (Φ.fibre_exact x hvan)
  obtain ⟨d, t, hoi, hrange, hunit⟩ := exists_basicOpen_test T f
  let : Algebra (Gam T) (Gam d) := ((BigFppfOver.toScheme B S hS).map t).appTop.hom.toAlgebra
  obtain ⟨q, s, t', h₁, h₂, h₃⟩ := hB (Gam d) hunit
  let Φ' := Φ.pull t
  refine ⟨d, t, hoi, ?_, r, Φ'.m, _, ⟨degreeZeroSectionsMatKerIso _ Φ'.e₁ Φ'.e₀ Φ'.D₁ Φ'.hd₁ q s t'
    h₁ h₂ h₃ Φ'.e₁' Φ'.D₀ Φ'.hd₀⟩⟩
  exact mem_range_of_range_eq_basicOpen x hrange hf

end FreeTruncation


/-! ### Direct summands of free modules are free near a point -/

section Summands

variable {c : BigFppfOver B S hS}

/-- A retract `X` of `Y` whose idempotent `r ≫ i` factors as `A ≫ B` with `B ≫ A = 𝟙` is
isomorphic to the middle object of the factorisation. -/
def isoOfRetractOfFactor {C : Type*} [Category* C] {X Y Z : C} (i : X ⟶ Y) (r : Y ⟶ X)
    (hir : i ≫ r = 𝟙 X) (A : Y ⟶ Z) (B : Z ⟶ Y) (hri : r ≫ i = A ≫ B) (hBA : B ≫ A = 𝟙 Z) :
    X ≅ Z where
  hom := i ≫ A
  inv := B ≫ r
  hom_inv_id := by
    rw [Category.assoc, ← Category.assoc A, ← hri, ← Category.assoc, ← Category.assoc, hir,
      Category.id_comp, hir]
  inv_hom_id := by
    rw [Category.assoc, ← Category.assoc r, hri, Category.assoc, ← Category.assoc B, hBA,
      Category.id_comp]

/-- The idempotent matrix of a retraction of a free module. -/
theorem matOf_retract_mul_self {M : toposModules B S hS ((schemeSpaceFunctor B S hS).obj c)} {n : ℕ}
    (i : M ⟶ freeObj (unitT c) n) (r : freeObj (unitT c) n ⟶ M) (hir : i ≫ r = 𝟙 M) :
    matOf c (r ≫ i) * matOf c (r ≫ i) = matOf c (r ≫ i) := by
  refine matMap_injective c ?_
  change matMap c (matOf c (r ≫ i) * matOf c (r ≫ i)) = matMap c (matOf c (r ≫ i))
  rw [matMap_mul, matMap_matOf, Category.assoc, ← Category.assoc i, hir, Category.id_comp]

/-- **A direct summand of a free module is free on a principal open neighbourhood of a point**,
uniformly: there are `f` not vanishing at `x` and a rank `ρ` such that the summand becomes free of
rank `ρ` after inverse image to any scheme over `c` on which `f` is a unit. -/
theorem exists_away_free_of_retract {M : toposModules B S hS ((schemeSpaceFunctor B S hS).obj c)}
    {n : ℕ} (i : M ⟶ freeObj (unitT c) n) (r : freeObj (unitT c) n ⟶ M) (hir : i ≫ r = 𝟙 M)
    (x : (BigFppfOver.toScheme B S hS).obj c) :
    ∃ f ∉ RingHom.ker (((BigFppfOver.toScheme B S hS).obj c).evaluation ⊤ x trivial).hom,
      ∃ ρ : ℕ, ∀ (d : BigFppfOver B S hS) (t : d ⟶ c),
        IsUnit (((BigFppfOver.toScheme B S hS).map t).appTop.hom f) →
          Nonempty (((toposModulePullbackData B S hS).pull
            ((schemeSpaceFunctor B S hS).map t)).obj M ≅ freeObj (unitT d) ρ) := by
  obtain ⟨f, hf, ρ, hB⟩ := exists_away_retract_of_idempotent
    (RingHom.ker (((BigFppfOver.toScheme B S hS).obj c).evaluation ⊤ x trivial).hom)
    (matOf c (r ≫ i)) (matOf_retract_mul_self i r hir)
  refine ⟨f, hf, ρ, fun d t hu => ?_⟩
  let : Algebra (Gam c) (Gam d) := ((BigFppfOver.toScheme B S hS).map t).appTop.hom.toAlgebra
  obtain ⟨a, b, hba, hab⟩ := hB (Gam d) hu
  let P := (toposModulePullbackData B S hS).pull ((schemeSpaceFunctor B S hS).map t)
  let e := pullFreeIso ((schemeSpaceFunctor B S hS).map t) n
  let i' := P.map i ≫ e.hom
  let r' := e.inv ≫ P.map r
  have hir' : i' ≫ r' = 𝟙 _ := by
    simp only [i', r', Category.assoc, Iso.hom_inv_id_assoc, ← P.map_comp, hir, P.map_id]
  have hri' : r' ≫ i' = matMap d (a * b) := by
    rw [hab]
    refine Eq.trans ?_ (pullFreeIso_inv_map_matMap ((schemeSpaceFunctor B S hS).map t) t rfl _)
    rw [matMap_matOf]
    simp only [i', r', Category.assoc, P.map_comp, e, P]
  rw [matMap_mul] at hri'
  have hBA : matMap d b ≫ matMap d a = 𝟙 _ := by rw [← matMap_mul, hba, matMap_one]
  exact ⟨isoOfRetractOfFactor i' r' hir' (matMap d a) (matMap d b) hri' hBA⟩

end Summands


/-! ### Complexes with summands of free modules as terms -/

section Assembly

/-- The degree-zero sections functors of isomorphic complexes are isomorphic. -/
def degreeZeroSectionsIsoOfIso {X : AlgebraicSpaces B S hS} {I : Type*} [Category* I]
    {π : I ⥤ AlgebraicSpaces B S hS} (κ : PullbackData.ConeTo π X)
    {K K' : CochainComplex (toposModules B S hS X) ℤ} (e : K ≅ K') :
    degreeZeroSectionsFunctor κ K ≅ degreeZeroSectionsFunctor κ K' :=
  @asIso _ _ _ _ (degreeZeroSectionsMap κ e.hom) (isIso_degreeZeroSectionsMap κ e.hom fun i => by
    have : IsIso ((((toposModulePullbackData B S hS).pull (κ.leg i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map e.hom) := inferInstance
    infer_instance)

/-- The inverse image along a composite of morphisms of schemes is the iterated inverse image, on
complexes. -/
def pullCompComplexIso {c d₁ d : BigFppfOver B S hS} (t₂ : d ⟶ d₁) (t₁ : d₁ ⟶ c)
    (F : CochainComplex (toposModules B S hS ((schemeSpaceFunctor B S hS).obj c)) ℤ) :
    (((toposModulePullbackData B S hS).pull
        ((schemeSpaceFunctor B S hS).map (t₂ ≫ t₁))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj F ≅
      (((toposModulePullbackData B S hS).pull
          ((schemeSpaceFunctor B S hS).map t₂)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        ((((toposModulePullbackData B S hS).pull
            ((schemeSpaceFunctor B S hS).map t₁)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F) :=
  (NatIso.mapHomologicalComplex (eqToIso (congrArg (toposModulePullbackData B S hS).pull
      ((schemeSpaceFunctor B S hS).map_comp t₂ t₁)) ≪≫
      (toposModulePullbackData B S hS).compIso _ _) (ComplexShape.up ℤ)).app F ≪≫
    ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app F).symm

variable {c : BigFppfOver B S hS}

/-- **The terms of a complex of direct summands of free modules are free near a point**, in
degrees `-2, …, 1`: a common principal open neighbourhood on which the four summands are free. -/
theorem exists_basicOpen_freeTruncation
    (F : CochainComplex (toposModules B S hS ((schemeSpaceFunctor B S hS).obj c)) ℤ)
    (hF : ∀ j : ℤ, ∃ (n : ℕ) (i : F.X j ⟶ freeObj (unitT c) n) (r : freeObj (unitT c) n ⟶ F.X j),
      i ≫ r = 𝟙 _) (x : (BigFppfOver.toScheme B S hS).obj c) :
    ∃ (d : BigFppfOver B S hS) (t : d ⟶ c),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map t) ∧
        x ∈ Set.range ((BigFppfOver.toScheme B S hS).map t).base ∧
        Nonempty (FreeTruncation ((((toposModulePullbackData B S hS).pull
          ((schemeSpaceFunctor B S hS).map t)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            F)) := by
  let p := RingHom.ker (((BigFppfOver.toScheme B S hS).obj c).evaluation ⊤ x trivial).hom
  have key : ∀ j : ℤ, ∃ f ∉ p, ∃ ρ : ℕ, ∀ (d : BigFppfOver B S hS) (t : d ⟶ c),
      IsUnit (((BigFppfOver.toScheme B S hS).map t).appTop.hom f) →
        Nonempty (((toposModulePullbackData B S hS).pull ((schemeSpaceFunctor B S hS).map t)).obj
          (F.X j) ≅ freeObj (unitT d) ρ) := fun j => by
    obtain ⟨n, i, r, hir⟩ := hF j
    exact exists_away_free_of_retract i r hir x
  obtain ⟨f₂, hf₂, ρ₂, h₂⟩ := key (-2)
  obtain ⟨f₁, hf₁, ρ₁, h₁⟩ := key (-1)
  obtain ⟨f₀, hf₀, ρ₀, h₀⟩ := key 0
  obtain ⟨f₃, hf₃, ρ₃, h₃⟩ := key 1
  have hp : p.IsPrime := inferInstance
  have hf : f₂ * f₁ * f₀ * f₃ ∉ p := by
    intro h
    rcases hp.mem_or_mem h with h | h
    · rcases hp.mem_or_mem h with h | h
      · rcases hp.mem_or_mem h with h | h
        · exact hf₂ h
        · exact hf₁ h
      · exact hf₀ h
    · exact hf₃ h
  obtain ⟨d, t, hoi, hrange, hunit⟩ := exists_basicOpen_test c (f₂ * f₁ * f₀ * f₃)
  simp only [map_mul] at hunit
  have u₃ := isUnit_of_mul_isUnit_right hunit
  have hunit' := isUnit_of_mul_isUnit_left hunit
  have u₀ := isUnit_of_mul_isUnit_right hunit'
  have hunit'' := isUnit_of_mul_isUnit_left hunit'
  have u₁ := isUnit_of_mul_isUnit_right hunit''
  have u₂ := isUnit_of_mul_isUnit_left hunit''
  obtain ⟨e₂⟩ := h₂ d t u₂
  obtain ⟨e₁⟩ := h₁ d t u₁
  obtain ⟨e₀⟩ := h₀ d t u₀
  obtain ⟨e₃⟩ := h₃ d t u₃
  refine ⟨d, t, hoi, ?_, ⟨FreeTruncation.ofIsos e₂ e₁ e₀ e₃⟩⟩
  exact mem_range_of_range_eq_basicOpen x hrange hf

/-- **Stacks 08JX, the local model.**  Let `F` be a complex of `𝒪`-modules on the algebraic space
of a scheme `c` whose terms are direct summands of finite free modules, and such that `H⁻¹` of
its inverse image to every scheme over `c` vanishes.  Every point of `c` has an open
neighbourhood on which the degree-zero sections functor of `F` is the kernel functor of a matrix
of functions. -/
theorem exists_open_matKerIso
    (F : CochainComplex (toposModules B S hS ((schemeSpaceFunctor B S hS).obj c)) ℤ)
    (hF : ∀ j : ℤ, ∃ (n : ℕ) (i : F.X j ⟶ freeObj (unitT c) n) (r : freeObj (unitT c) n ⟶ F.X j),
      i ≫ r = 𝟙 _)
    (hvan : ∀ (T' : BigFppfOver B S hS) (t : T' ⟶ c),
      IsZero (((((toposModulePullbackData B S hS).pull
        ((schemeSpaceFunctor B S hS).map t)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          F).homology (-1)))
    (x : (BigFppfOver.toScheme B S hS).obj c) :
    ∃ (d : BigFppfOver B S hS) (t : d ⟶ c),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map t) ∧
        x ∈ Set.range ((BigFppfOver.toScheme B S hS).map t).base ∧
        ∃ (r m : ℕ) (N : Matrix (Fin r) (Fin m) (Gam d)),
          Nonempty (degreeZeroSectionsFunctor (schemesOverCone ((schemeSpaceFunctor B S hS).obj d))
            ((((toposModulePullbackData B S hS).pull
              ((schemeSpaceFunctor B S hS).map t)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj F) ≅ matKerFunctor d N) := by
  obtain ⟨d₁, t₁, hoi₁, ⟨y, hy⟩, ⟨Φ⟩⟩ := exists_basicOpen_freeTruncation F hF x
  have hvan' : ∀ (T' : BigFppfOver B S hS) (t : T' ⟶ d₁),
      IsZero (((((toposModulePullbackData B S hS).pull
        ((schemeSpaceFunctor B S hS).map t)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((((toposModulePullbackData B S hS).pull
            ((schemeSpaceFunctor B S hS).map t₁)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj F)).homology (-1)) := fun T' t =>
    (hvan T' (t ≫ t₁)).of_iso
      (HomologicalComplex.homologyMapIso (pullCompComplexIso t t₁ F) (-1)).symm
  obtain ⟨d, t₂, hoi₂, ⟨z, hz⟩, r, m, N, ⟨e⟩⟩ := Φ.exists_basicOpen_matKerIso y hvan'
  refine ⟨d, t₂ ≫ t₁, ?_, ⟨z, ?_⟩, r, m, N,
    ⟨degreeZeroSectionsIsoOfIso _ (pullCompComplexIso t₂ t₁ F) ≪≫ e⟩⟩
  · rw [Functor.map_comp]; infer_instance
  · rw [Functor.map_comp, Scheme.Hom.comp_base, TopCat.comp_app, hz, hy]

end Assembly

end AlgebraicGeometry.Space

end
