module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Extensions by a copower, and their classes

Let `𝒜` be an abelian `k`-linear category, `G` an object of `𝒜` and `V` a finite-dimensional
`k`-vector space. The *copower* `G ⊗ V` is the direct sum of `dim V` copies of `G`, indexed by the
standard basis `Module.finBasis k V`; a linear map `f : V ⟶ W` acts by its matrix in the two
standard bases. This makes `V ↦ G ⊗ V` an additive `k`-linear functor `FGModuleCat k ⥤ 𝒜`.

A deformation of a module over the square-zero extension `k[V] = k ⊕ V` is, after the direct
image to the special fibre, an object `E` with a map `p : E ⟶ G` onto the reduction and, for every
`v ∈ V`, a map `μ v : G ⟶ E` by which multiplication by `v` factors as `p ≫ μ v`; flatness says
that the induced sequence `0 ⟶ G ⊗ V ⟶ E ⟶ G ⟶ 0` is short exact. This file records that
structure in an arbitrary abelian `k`-linear category, as
`Deformation.ModuleDeformation.CopowerExtension`, together with its class in
`Ext¹(G, G ⊗ V)` and the two properties of the class the tangent space of Stacks 08W8 needs:

* the class is natural in `V`: a map of such extensions over a linear map `f : V ⟶ W`, which is
  the identity on `G` and intertwines the two families `μ`, carries the first class to the
  second after pushing out along `G ⊗ f`;
* the class determines the extension: two extensions over the same `V` with the same class are
  isomorphic, by an isomorphism compatible with the maps to `G` and with the families `μ`.

The first is Mathlib's naturality of the class of a short exact sequence, the second is
Stacks 06XV, `CategoryTheory.Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum`.

It also records the coordinates of an automorphism of the middle term of a short exact sequence
which induces the identity on both outer terms, the shape in which the infinitesimal automorphisms
of Stacks 08W8 are embedded into `Hom(G, G)`.

## Main definitions

* `Deformation.ModuleDeformation.copowerFunctor`: the functor `V ↦ G ⊗ V`.
* `Deformation.ModuleDeformation.extCoefficientFunctor`: the functor `V ↦ Ext¹(G, G ⊗ V)`.
* `Deformation.ModuleDeformation.CopowerExtension` and its class
  `Deformation.ModuleDeformation.CopowerExtension.extensionClass`.
* `Deformation.ModuleDeformation.extensionAutomorphismCoordinates`: the coordinates
  `a ↦ t` with `a - 𝟙 = g ≫ t ≫ f` of an automorphism of the middle term of a short exact
  sequence fixing both outer terms, as a homomorphism of monoids.

## Main results

* `Deformation.ModuleDeformation.CopowerExtension.extensionClass_comp_mk₀_map`: naturality.
* `Deformation.ModuleDeformation.CopowerExtension.exists_iso_of_extensionClass_eq`: the class
  determines the extension.
* `Deformation.ModuleDeformation.finiteDimensional_ext_copowerObj`: `Ext¹(X, G ⊗ V)` is
  finite-dimensional when `Ext¹(X, G)` is.
-/

@[expose] public noncomputable section

namespace Deformation.ModuleDeformation

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

attribute [local instance] Abelian.hasFiniteBiproducts

universe v w w' u₁ v₁

variable {k : Type w} [Field k]

/-! ### The copower `G ⊗ V` -/

section Copower

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Preadditive 𝒜] [Linear k 𝒜] [HasFiniteBiproducts 𝒜]

/-- The standard basis of a finite-dimensional vector space. -/
noncomputable abbrev stdBasis (V : FGModuleCat.{v} k) :
    Module.Basis (Fin (Module.finrank k V)) k V :=
  Module.finBasis k V

/-- The copower `G ⊗ V`: one copy of `G` for each vector of the standard basis of `V`. -/
noncomputable abbrev copowerObj (G : 𝒜) (V : FGModuleCat.{v} k) : 𝒜 :=
  ⨁ fun _ : Fin (Module.finrank k V) => G

/-- The matrix of a linear map in the two standard bases. -/
noncomputable def copowerCoeff {V W : FGModuleCat.{v} k} (f : V ⟶ W)
    (i : Fin (Module.finrank k V)) (j : Fin (Module.finrank k W)) : k :=
  (stdBasis W).repr (f.hom.hom (stdBasis V i)) j

/-- The matrix of the identity is the identity matrix. -/
theorem copowerCoeff_id (V : FGModuleCat.{v} k) (i j : Fin (Module.finrank k V)) :
    copowerCoeff (𝟙 V) i j = if i = j then 1 else 0 := by
  rw [copowerCoeff]
  show (stdBasis V).repr (stdBasis V i) j = _
  rw [Module.Basis.repr_self, Finsupp.single_apply]

/-- The matrix of a composite is the product of the matrices. -/
theorem copowerCoeff_comp {U V W : FGModuleCat.{v} k} (f : U ⟶ V) (g : V ⟶ W)
    (i : Fin (Module.finrank k U)) (l : Fin (Module.finrank k W)) :
    copowerCoeff (f ≫ g) i l = ∑ j, copowerCoeff f i j * copowerCoeff g j l := by
  simp only [copowerCoeff]
  show (stdBasis W).repr (g.hom.hom (f.hom.hom (stdBasis U i))) l = _
  conv_lhs => rw [← (stdBasis V).sum_repr (f.hom.hom (stdBasis U i))]
  rw [map_sum]
  simp only [map_smul, map_sum, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]

/-- The matrix of a sum of linear maps is the sum of their matrices. -/
theorem copowerCoeff_add {V W : FGModuleCat.{v} k} (f g : V ⟶ W) (i j) :
    copowerCoeff (f + g) i j = copowerCoeff f i j + copowerCoeff g i j := by
  simp only [copowerCoeff]
  show (stdBasis W).repr (f.hom.hom (stdBasis V i) + g.hom.hom (stdBasis V i)) j = _
  rw [map_add, Finsupp.add_apply]

/-- The matrix of a scalar multiple of a linear map is the scalar multiple of its matrix. -/
theorem copowerCoeff_smul {V W : FGModuleCat.{v} k} (c : k) (f : V ⟶ W) (i j) :
    copowerCoeff (c • f) i j = c * copowerCoeff f i j := by
  simp only [copowerCoeff]
  show (stdBasis W).repr (c • f.hom.hom (stdBasis V i)) j = _
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

/-- The map of copowers attached to a linear map: its matrix acting by scalars. -/
noncomputable def copowerMap (G : 𝒜) {V W : FGModuleCat.{v} k} (f : V ⟶ W) :
    copowerObj G V ⟶ copowerObj G W :=
  biproduct.matrix fun i j => copowerCoeff f i j • 𝟙 G

/-- The `(i, j)` entry of `G ⊗ f` is the `(i, j)` entry of the matrix of `f` times `𝟙 G`. -/
@[reassoc (attr := simp)]
theorem ι_copowerMap_π (G : 𝒜) {V W : FGModuleCat.{v} k} (f : V ⟶ W) (i j) :
    biproduct.ι _ i ≫ copowerMap G f ≫ biproduct.π _ j = copowerCoeff f i j • 𝟙 G := by
  simp [copowerMap]

/-- The entries of a composite of maps of copowers are the entries of the product matrix. -/
theorem copowerMap_comp_entry (G : 𝒜) {U V W : FGModuleCat.{v} k} (f : U ⟶ V) (g : V ⟶ W)
    (i : Fin (Module.finrank k U)) (l : Fin (Module.finrank k W)) :
    biproduct.ι _ i ≫ copowerMap G (f ≫ g) ≫ biproduct.π _ l =
      biproduct.ι _ i ≫ (copowerMap G f ≫ copowerMap G g) ≫ biproduct.π _ l := by
  rw [ι_copowerMap_π, copowerCoeff_comp, Category.assoc]
  conv_rhs => rw [← Category.assoc (copowerMap G f), ← Category.id_comp (copowerMap G g),
    ← biproduct.total (f := fun _ : Fin (Module.finrank k V) => G)]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc, ι_copowerMap_π,
    Linear.comp_smul, Category.comp_id, Finset.sum_smul, smul_smul]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]

/-- **The copower functor** `V ↦ G ⊗ V`. -/
noncomputable def copowerFunctor (G : 𝒜) : FGModuleCat.{v} k ⥤ 𝒜 where
  obj V := copowerObj G V
  map f := copowerMap G f
  map_id V := by
    change copowerMap G (𝟙 V) = 𝟙 _
    ext i j
    rw [ι_copowerMap_π, copowerCoeff_id, Category.id_comp, biproduct.ι_π]
    by_cases h : i = j
    · subst h
      simp
    · simp [Ne.symm h]
  map_comp f g := by
    change copowerMap G (f ≫ g) = copowerMap G f ≫ copowerMap G g
    ext i l
    exact copowerMap_comp_entry G f g l i

/-- The copower functor sends a linear map `f` to `copowerMap G f`. -/
theorem copowerFunctor_map (G : 𝒜) {V W : FGModuleCat.{v} k} (f : V ⟶ W) :
    (copowerFunctor G).map f = copowerMap G f := rfl

/-- The copower functor is additive. -/
instance (G : 𝒜) : (copowerFunctor (k := k) G).Additive where
  map_add {V W f g} := by
    change copowerMap G (f + g) = copowerMap G f + copowerMap G g
    ext i j
    simp only [ι_copowerMap_π, Preadditive.add_comp, Preadditive.comp_add,
      copowerCoeff_add, add_smul]

/-- The copower functor is `k`-linear. -/
instance (G : 𝒜) : (copowerFunctor (k := k) G).Linear k where
  map_smul {V W} f c := by
    change copowerMap G (c • f) = c • copowerMap G f
    ext i j
    simp only [ι_copowerMap_π, Linear.smul_comp, Linear.comp_smul,
      copowerCoeff_smul, smul_smul]

/-- The map out of the copower `G ⊗ V` determined by a linear family of maps out of `G`: its
component at a basis vector `b` is the value at `b`. -/
noncomputable def copowerDesc (G : 𝒜) {E : 𝒜} {V : FGModuleCat.{v} k}
    (μ : ↥V →ₗ[k] (G ⟶ E)) : copowerObj G V ⟶ E :=
  biproduct.desc fun i => μ (stdBasis V i)

/-- The component of `copowerDesc G μ` at the `i`-th basis vector is `μ` of that vector. -/
@[reassoc (attr := simp)]
theorem ι_copowerDesc (G : 𝒜) {E : 𝒜} {V : FGModuleCat.{v} k} (μ : ↥V →ₗ[k] (G ⟶ E)) (i) :
    biproduct.ι _ i ≫ copowerDesc G μ = μ (stdBasis V i) := by
  simp [copowerDesc]

/-- **The map of copowers intertwines two families over a linear map.** If `μ v ≫ φ = μ' (f v)`
for every `v`, then `copowerDesc μ ≫ φ = (G ⊗ f) ≫ copowerDesc μ'`. -/
theorem copowerDesc_comp (G : 𝒜) {E E' : 𝒜} {V W : FGModuleCat.{v} k}
    (μ : ↥V →ₗ[k] (G ⟶ E)) (μ' : ↥W →ₗ[k] (G ⟶ E')) (f : V ⟶ W) (φ : E ⟶ E')
    (h : ∀ v, μ v ≫ φ = μ' (f.hom.hom v)) :
    copowerDesc G μ ≫ φ = copowerMap G f ≫ copowerDesc G μ' := by
  ext i
  rw [ι_copowerDesc_assoc, h]
  conv_lhs => rw [← (stdBasis W).sum_repr (f.hom.hom (stdBasis V i))]
  rw [map_sum, ← Category.assoc, ← Category.id_comp (copowerDesc G μ'),
    ← biproduct.total (f := fun _ : Fin (Module.finrank k W) => G)]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc, ι_copowerDesc,
    ι_copowerMap_π_assoc, Linear.smul_comp, Category.id_comp, map_smul]
  rfl

omit [HasFiniteBiproducts 𝒜] in
/-- A linear family of maps out of `G` is determined by its values on the standard basis. -/
theorem linearMap_ext_stdBasis {E : 𝒜} {V : FGModuleCat.{v} k} (G : 𝒜)
    {μ μ' : ↥V →ₗ[k] (G ⟶ E)} (h : ∀ i, μ (stdBasis V i) = μ' (stdBasis V i)) : μ = μ' :=
  (stdBasis V).ext h

end Copower

/-! ### Finite-dimensionality of `Ext` into a copower -/

section FiniteDimensional

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜] [Linear k 𝒜] [HasExt.{w'} 𝒜]

/-- **`Ext^n(X, G ⊗ V)` is finite-dimensional when `Ext^n(X, G)` is**: composing with the
projections embeds it into the product of finitely many copies of `Ext^n(X, G)`. -/
theorem finiteDimensional_ext_copowerObj (X G : 𝒜) (V : FGModuleCat.{v} k) (n : ℕ)
    [FiniteDimensional k (Ext X G n)] : FiniteDimensional k (Ext X (copowerObj G V) n) := by
  let ψ : Ext X (copowerObj G V) n →ₗ[k] (Fin (Module.finrank k V) → Ext X G n) :=
    { toFun := fun e i => e.comp (Ext.mk₀ (biproduct.π _ i)) (add_zero n)
      map_add' := fun e e' => by
        funext i
        exact Ext.add_comp e e' _ (add_zero n)
      map_smul' := fun c e => by
        funext i
        exact Ext.smul_comp e _ (add_zero n) c }
  refine FiniteDimensional.of_injective ψ ?_
  intro e e' h
  have hπ : ∀ i, e.comp (Ext.mk₀ (biproduct.π _ i)) (add_zero n) =
      e'.comp (Ext.mk₀ (biproduct.π _ i)) (add_zero n) := fun i => congrFun h i
  rw [← Ext.comp_mk₀_id e, ← biproduct.total (f := fun _ : Fin (Module.finrank k V) => G),
    ← Ext.comp_mk₀_id e', ← biproduct.total (f := fun _ : Fin (Module.finrank k V) => G)]
  have hsum : ∀ (x : Ext X (copowerObj G V) n),
      x.comp (Ext.mk₀ (∑ i, biproduct.π (fun _ : Fin (Module.finrank k V) => G) i ≫
        biproduct.ι (fun _ : Fin (Module.finrank k V) => G) i)) (add_zero n) =
      ∑ i, (x.comp (Ext.mk₀ (biproduct.π (fun _ : Fin (Module.finrank k V) => G) i))
        (add_zero n)).comp
        (Ext.mk₀ (biproduct.ι (fun _ : Fin (Module.finrank k V) => G) i)) (add_zero n) := by
    intro x
    have hmk : ∀ (s : Finset (Fin (Module.finrank k V))),
        Ext.mk₀ (∑ i ∈ s, biproduct.π (fun _ : Fin (Module.finrank k V) => G) i ≫
          biproduct.ι (fun _ : Fin (Module.finrank k V) => G) i) =
        ∑ i ∈ s, Ext.mk₀ (biproduct.π (fun _ : Fin (Module.finrank k V) => G) i ≫
          biproduct.ι (fun _ : Fin (Module.finrank k V) => G) i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [Ext.mk₀_zero]
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Ext.mk₀_add, ih]
    rw [hmk]
    induction (Finset.univ : Finset (Fin (Module.finrank k V))) using Finset.induction_on with
    | empty => simp [Ext.comp_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Ext.comp_add, ih, ← Ext.mk₀_comp_mk₀,
        ← Ext.comp_assoc_of_third_deg_zero]
  rw [hsum, hsum]
  exact Finset.sum_congr rfl fun i _ => by rw [hπ i]

end FiniteDimensional

/-! ### The functor `V ↦ Ext¹(X, G ⊗ V)` -/

section ExtFunctor

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜] [Linear k 𝒜] [HasExt.{w'} 𝒜]

/-- Postcomposition with a map of the second argument, as a linear map of `Ext` groups. -/
noncomputable def extPostcomp (X : 𝒜) {Y Y' : 𝒜} (g : Y ⟶ Y') (n : ℕ) :
    Ext X Y n →ₗ[k] Ext X Y' n where
  toFun e := e.comp (Ext.mk₀ g) (add_zero n)
  map_add' e e' := Ext.add_comp e e' _ (add_zero n)
  map_smul' c e := Ext.smul_comp e _ (add_zero n) c

/-- `extPostcomp X g n` sends `e` to its composite with `Ext.mk₀ g`. -/
theorem extPostcomp_apply (X : 𝒜) {Y Y' : 𝒜} (g : Y ⟶ Y') (n : ℕ) (e : Ext X Y n) :
    extPostcomp (k := k) X g n e = e.comp (Ext.mk₀ g) (add_zero n) := rfl

/-- Postcomposition with a sum of maps is the sum of the postcompositions. -/
theorem extPostcomp_add (X : 𝒜) {Y Y' : 𝒜} (g g' : Y ⟶ Y') (n : ℕ) :
    extPostcomp (k := k) X (g + g') n = extPostcomp X g n + extPostcomp X g' n := by
  ext e
  show e.comp (Ext.mk₀ (g + g')) (add_zero n) =
    e.comp (Ext.mk₀ g) (add_zero n) + e.comp (Ext.mk₀ g') (add_zero n)
  rw [Ext.mk₀_add, Ext.comp_add]

/-- Postcomposition with a scalar multiple of a map is the scalar multiple of the
postcomposition. -/
theorem extPostcomp_smul (X : 𝒜) {Y Y' : 𝒜} (c : k) (g : Y ⟶ Y') (n : ℕ) :
    extPostcomp (k := k) X (c • g) n = c • extPostcomp X g n := by
  ext e
  show e.comp (Ext.mk₀ (c • g)) (add_zero n) = c • e.comp (Ext.mk₀ g) (add_zero n)
  rw [Ext.mk₀_smul, Ext.comp_smul]

/-- **The functor `V ↦ Ext^n(X, C V)`** for an additive `k`-linear functor `C`, acting by
postcomposition with the images of linear maps. -/
noncomputable def extCoefficientFunctor (X : 𝒜) (C : FGModuleCat.{v} k ⥤ 𝒜) [C.Additive]
    [C.Linear k] (n : ℕ) : FGModuleCat.{v} k ⥤ ModuleCat.{w'} k where
  obj V := ModuleCat.of k (Ext X (C.obj V) n)
  map f := ModuleCat.ofHom (extPostcomp X (C.map f) n)
  map_id V := by
    ext e
    change e.comp (Ext.mk₀ (C.map (𝟙 V))) (add_zero n) = e
    rw [C.map_id, Ext.comp_mk₀_id]
  map_comp f g := by
    ext e
    change e.comp (Ext.mk₀ (C.map (f ≫ g))) (add_zero n) =
      (e.comp (Ext.mk₀ (C.map f)) (add_zero n)).comp (Ext.mk₀ (C.map g)) (add_zero n)
    rw [C.map_comp, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- The functor `V ↦ Ext^n(X, C V)` sends `f` to postcomposition with `Ext.mk₀ (C.map f)`. -/
theorem extCoefficientFunctor_map_apply (X : 𝒜) (C : FGModuleCat.{v} k ⥤ 𝒜) [C.Additive]
    [C.Linear k] (n : ℕ) {V W : FGModuleCat.{v} k} (f : V ⟶ W)
    (e : Ext X (C.obj V) n) :
    ((extCoefficientFunctor X C n).map f) e = e.comp (Ext.mk₀ (C.map f)) (add_zero n) := rfl

/-- The functor `V ↦ Ext^n(X, C V)` is additive. -/
instance (X : 𝒜) (C : FGModuleCat.{v} k ⥤ 𝒜) [C.Additive] [C.Linear k] (n : ℕ) :
    (extCoefficientFunctor X C n).Additive where
  map_add {V W f g} := by
    apply ModuleCat.hom_ext
    change extPostcomp (k := k) X (C.map (f + g)) n =
      extPostcomp (k := k) X (C.map f) n + extPostcomp (k := k) X (C.map g) n
    rw [C.map_add, extPostcomp_add]

/-- The functor `V ↦ Ext^n(X, C V)` is `k`-linear. -/
instance (X : 𝒜) (C : FGModuleCat.{v} k ⥤ 𝒜) [C.Additive] [C.Linear k] (n : ℕ) :
    (extCoefficientFunctor X C n).Linear k where
  map_smul {V W} f c := by
    apply ModuleCat.hom_ext
    change extPostcomp (k := k) X (C.map (c • f)) n = c • extPostcomp (k := k) X (C.map f) n
    rw [C.map_smul, extPostcomp_smul]

end ExtFunctor

/-! ### Extensions by a copower -/

section CopowerExtension

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜] [Linear k 𝒜]

/-- **An extension of `G` by the copower `G ⊗ V` presented by a linear family.** An object `E`
with a map `p : E ⟶ G` and a linear family `μ : V → Hom(G, E)` of maps killed by `p`, such that
`0 ⟶ G ⊗ V ⟶ E ⟶ G ⟶ 0`, with first map `copowerDesc μ`, is short exact. -/
structure CopowerExtension (G : 𝒜) (V : FGModuleCat.{v} k) where
  /-- The middle term. -/
  E : 𝒜
  /-- The map onto the reduction. -/
  p : E ⟶ G
  /-- The linear family of maps out of `G`. -/
  μ : ↥V →ₗ[k] (G ⟶ E)
  /-- Each of them is killed by `p`. -/
  μ_p : ∀ v, μ v ≫ p = 0
  /-- The sequence `0 ⟶ G ⊗ V ⟶ E ⟶ G ⟶ 0` is short exact. -/
  shortExact : (ShortComplex.mk (copowerDesc (k := k) G μ) p (by
    ext i; rw [ι_copowerDesc_assoc, μ_p, comp_zero])).ShortExact

namespace CopowerExtension

variable {G : 𝒜}

/-- The short complex of an extension by a copower. -/
abbrev shortComplex {V : FGModuleCat.{v} k} (A : CopowerExtension G V) : ShortComplex 𝒜 :=
  ShortComplex.mk (copowerDesc (k := k) G A.μ) A.p (by
    ext i; rw [ι_copowerDesc_assoc, A.μ_p, comp_zero])

variable [HasExt.{w'} 𝒜]

/-- **The class of an extension by a copower** in `Ext¹(G, G ⊗ V)`. -/
noncomputable def extensionClass {V : FGModuleCat.{v} k} (A : CopowerExtension G V) :
    Ext G (copowerObj G V) 1 :=
  A.shortExact.extClass

/-- **Naturality of the class.** A map `φ` of middle terms over a linear map `f : V ⟶ W`, which
is compatible with the maps to `G` and carries each `μ v` to `μ' (f v)`, carries the class of the
first extension, pushed out along `G ⊗ f`, to the class of the second. -/
theorem extensionClass_comp_mk₀_map {V W : FGModuleCat.{v} k} (A : CopowerExtension G V)
    (A' : CopowerExtension G W) (f : V ⟶ W) (φ : A.E ⟶ A'.E) (hp : φ ≫ A'.p = A.p)
    (hμ : ∀ v, A.μ v ≫ φ = A'.μ (f.hom.hom v)) :
    A.extensionClass.comp (Ext.mk₀ ((copowerFunctor G).map f)) (add_zero 1) =
      A'.extensionClass := by
  let m : A.shortComplex ⟶ A'.shortComplex :=
    { τ₁ := (copowerFunctor G).map f
      τ₂ := φ
      τ₃ := 𝟙 G
      comm₁₂ := (copowerDesc_comp G A.μ A'.μ f φ hμ).symm
      comm₂₃ := by simpa using hp }
  show A.shortExact.extClass.comp (Ext.mk₀ m.τ₁) (add_zero 1) = _
  rw [ShortComplex.ShortExact.extClass_naturality A.shortExact A'.shortExact m]
  exact Ext.mk₀_id_comp _

/-- **The class determines the extension.** Two extensions of `G` by `G ⊗ V` with the same class
are isomorphic, by an isomorphism of middle terms compatible with the maps to `G` and carrying
each `μ v` of the first to `μ v` of the second. This is Stacks 06XV. -/
theorem exists_iso_of_extensionClass_eq {V : FGModuleCat.{v} k} (A A' : CopowerExtension G V)
    (h : A.extensionClass = A'.extensionClass) :
    ∃ φ : A.E ≅ A'.E, φ.hom ≫ A'.p = A.p ∧ ∀ v, A.μ v ≫ φ.hom = A'.μ v := by
  obtain ⟨φ, h₁, h₂⟩ := ((Ext.extClass_surjective_and_eq_iff_iso_and_baerSum 𝒜 G
    (copowerObj G V)).2.1 A.E A'.E (copowerDesc G A.μ) A.p _ (copowerDesc G A'.μ) A'.p _
    A.shortExact A'.shortExact).1 h
  refine ⟨φ, h₂, fun v => ?_⟩
  have hb : ∀ i, A.μ (stdBasis V i) ≫ φ.hom = A'.μ (stdBasis V i) := fun i => by
    rw [← ι_copowerDesc G A.μ i, Category.assoc, h₁, ι_copowerDesc]
  let L : ↥V →ₗ[k] (G ⟶ A'.E) :=
    { toFun := fun v => A.μ v ≫ φ.hom
      map_add' := fun v v' => by rw [map_add, Preadditive.add_comp]
      map_smul' := fun c v => by
        rw [map_smul, Linear.smul_comp]
        rfl }
  exact LinearMap.congr_fun (linearMap_ext_stdBasis G (μ := L) (μ' := A'.μ) hb) v

end CopowerExtension

end CopowerExtension

/-! ### Coordinates of automorphisms fixing both outer terms -/

section Coordinates

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜]

/-- A map `X₃ ⟶ X₁` of a short exact sequence is determined by its composite `g ≫ t ≫ f`. -/
private theorem eq_of_comp_comp_eq {S : ShortComplex 𝒜} (hS : S.ShortExact)
    {t t' : S.X₃ ⟶ S.X₁} (h : S.g ≫ t ≫ S.f = S.g ≫ t' ≫ S.f) : t = t' := by
  have := hS.mono_f
  have := hS.epi_g
  exact (cancel_mono S.f).1 ((cancel_epi S.g).1 h)

/-- An endomorphism of the middle term of a short exact sequence inducing the identity on both
outer terms is `𝟙 + g ≫ t ≫ f` for exactly one `t : X₃ ⟶ X₁`. -/
theorem existsUnique_hom_of_extensionEndomorphism {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (a : S.X₂ ⟶ S.X₂) (hi : S.f ≫ a = S.f) (hp : a ≫ S.g = S.g) :
    ∃! t : S.X₃ ⟶ S.X₁, S.g ≫ t ≫ S.f = a - 𝟙 S.X₂ := by
  have := hS.mono_f
  have := hS.epi_g
  have ha : (a - 𝟙 S.X₂) ≫ S.g = 0 := by
    simp [Preadditive.sub_comp, hp]
  let l := hS.exact.lift (a - 𝟙 S.X₂) ha
  have hl : l ≫ S.f = a - 𝟙 S.X₂ := hS.exact.lift_f _ _
  have hil : S.f ≫ l = 0 := by
    apply (cancel_mono S.f).1
    simp only [Category.assoc, hl, zero_comp, Preadditive.comp_sub, Category.comp_id, hi,
      sub_self]
  refine ⟨hS.exact.desc l hil, ?_, ?_⟩
  · dsimp only
    rw [← Category.assoc, hS.exact.g_desc, hl]
  · intro t ht
    apply eq_of_comp_comp_eq hS
    rw [ht, ← Category.assoc, hS.exact.g_desc, hl]

/-- The coordinate `t` of an endomorphism `a = 𝟙 + g ≫ t ≫ f` of the middle term. -/
noncomputable def extensionEndomorphismCoordinates {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (a : S.X₂ ⟶ S.X₂) (hi : S.f ≫ a = S.f) (hp : a ≫ S.g = S.g) : S.X₃ ⟶ S.X₁ :=
  (existsUnique_hom_of_extensionEndomorphism hS a hi hp).choose

/-- The coordinate `t` of `a` satisfies `g ≫ t ≫ f = a - 𝟙`. -/
theorem extensionEndomorphismCoordinates_spec {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (a : S.X₂ ⟶ S.X₂) (hi : S.f ≫ a = S.f) (hp : a ≫ S.g = S.g) :
    S.g ≫ extensionEndomorphismCoordinates hS a hi hp ≫ S.f = a - 𝟙 S.X₂ :=
  (existsUnique_hom_of_extensionEndomorphism hS a hi hp).choose_spec.1

/-- **The coordinates of a family of automorphisms fixing both outer terms**, as a homomorphism
from a monoid to the additive group `Hom(X₃, X₁)` read multiplicatively: composition of
automorphisms is addition of coordinates. -/
noncomputable def extensionAutomorphismCoordinates {S : ShortComplex 𝒜} (hS : S.ShortExact)
    {M : Type*} [Monoid M] (ρ : M →* Aut S.X₂) (hi : ∀ a, S.f ≫ (ρ a).asIso.hom = S.f)
    (hp : ∀ a, (ρ a).asIso.hom ≫ S.g = S.g) : M →* Multiplicative (S.X₃ ⟶ S.X₁) where
  toFun a :=
    Multiplicative.ofAdd (extensionEndomorphismCoordinates hS (ρ a).asIso.hom (hi a) (hp a))
  map_one' := by
    have := hS.mono_f
    have := hS.epi_g
    change extensionEndomorphismCoordinates hS (ρ 1).asIso.hom (hi 1) (hp 1) = 0
    apply (cancel_epi S.g).1
    apply (cancel_mono S.f).1
    rw [Category.assoc, extensionEndomorphismCoordinates_spec]
    simp only [map_one, comp_zero, zero_comp]
    exact sub_self _
  map_mul' a b := by
    have := hS.mono_f
    have := hS.epi_g
    change extensionEndomorphismCoordinates hS (ρ (a * b)).asIso.hom (hi (a * b)) (hp (a * b)) =
      extensionEndomorphismCoordinates hS (ρ a).asIso.hom (hi a) (hp a) +
        extensionEndomorphismCoordinates hS (ρ b).asIso.hom (hi b) (hp b)
    apply (cancel_epi S.g).1
    apply (cancel_mono S.f).1
    simp only [Category.assoc, Preadditive.comp_add, Preadditive.add_comp,
      extensionEndomorphismCoordinates_spec]
    rw [map_mul]
    change (ρ b).asIso.hom ≫ (ρ a).asIso.hom - 𝟙 S.X₂ =
      ((ρ a).asIso.hom - 𝟙 S.X₂) + ((ρ b).asIso.hom - 𝟙 S.X₂)
    have h : (ρ b).asIso.hom ≫ ((ρ a).asIso.hom - 𝟙 S.X₂) = (ρ a).asIso.hom - 𝟙 S.X₂ := by
      rw [← extensionEndomorphismCoordinates_spec hS (ρ a).asIso.hom (hi a) (hp a),
        ← Category.assoc, hp b]
    rw [Preadditive.comp_sub, Category.comp_id] at h
    rw [← h]
    abel

/-- The coordinate `t` of `ρ a` satisfies `g ≫ t ≫ f = ρ a - 𝟙`. -/
theorem extensionAutomorphismCoordinates_spec {S : ShortComplex 𝒜} (hS : S.ShortExact)
    {M : Type*} [Monoid M] (ρ : M →* Aut S.X₂) (hi : ∀ a, S.f ≫ (ρ a).asIso.hom = S.f)
    (hp : ∀ a, (ρ a).asIso.hom ≫ S.g = S.g) (a : M) :
    S.g ≫ Multiplicative.toAdd (extensionAutomorphismCoordinates hS ρ hi hp a) ≫ S.f =
      (ρ a).asIso.hom - 𝟙 S.X₂ :=
  extensionEndomorphismCoordinates_spec hS (ρ a).asIso.hom (hi a) (hp a)

/-- The coordinates are injective on a monoid acting faithfully. -/
theorem extensionAutomorphismCoordinates_injective {S : ShortComplex 𝒜} (hS : S.ShortExact)
    {M : Type*} [Monoid M] (ρ : M →* Aut S.X₂) (hi : ∀ a, S.f ≫ (ρ a).asIso.hom = S.f)
    (hp : ∀ a, (ρ a).asIso.hom ≫ S.g = S.g) (hρ : Function.Injective ρ) :
    Function.Injective (extensionAutomorphismCoordinates hS ρ hi hp) := by
  intro a b hab
  refine hρ <| Aut.ext <| Iso.ext <| sub_left_injective (b := 𝟙 S.X₂) ?_
  exact (extensionAutomorphismCoordinates_spec hS ρ hi hp a).symm.trans
    ((congrArg (fun t => S.g ≫ Multiplicative.toAdd t ≫ S.f) hab).trans
      (extensionAutomorphismCoordinates_spec hS ρ hi hp b))

/-- The coordinates are compatible with scalar multiplication of the differences from the
identity. -/
theorem extensionAutomorphismCoordinates_smul {R : Type*} [Semiring R] [Linear R 𝒜]
    {S : ShortComplex 𝒜} (hS : S.ShortExact) {M : Type*} [Monoid M] (ρ : M →* Aut S.X₂)
    (hi : ∀ a, S.f ≫ (ρ a).asIso.hom = S.f) (hp : ∀ a, (ρ a).asIso.hom ≫ S.g = S.g)
    (c : R) (a b : M)
    (h : (ρ b).asIso.hom - 𝟙 S.X₂ = c • ((ρ a).asIso.hom - 𝟙 S.X₂)) :
    Multiplicative.toAdd (extensionAutomorphismCoordinates hS ρ hi hp b) =
      c • Multiplicative.toAdd (extensionAutomorphismCoordinates hS ρ hi hp a) := by
  apply eq_of_comp_comp_eq hS
  rwa [extensionAutomorphismCoordinates_spec, Linear.smul_comp, Linear.comp_smul,
    extensionAutomorphismCoordinates_spec]

end Coordinates

end Deformation.ModuleDeformation

end
