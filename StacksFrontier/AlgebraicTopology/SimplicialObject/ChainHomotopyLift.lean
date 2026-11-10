module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.DoldKan.Decomposition
public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.AlgebraicTopology.DoldKan.Normalized
public import Mathlib.AlgebraicTopology.DoldKan.PInfty
public import Mathlib.AlgebraicTopology.MooreComplex
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksFrontier.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Copower
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Equivalence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Chain homotopies of normalized complexes lift to simplicial homotopies

In an abelian category, every chain homotopy between the maps of normalized Moore complexes induced
by two morphisms of simplicial objects comes from a simplicial homotopy. The proof uses the
cylinder of a complex, which represents pairs of morphisms equipped with a homotopy, and the
diamond complex with its comparison map.
-/

/-!
## More homotopies in abelian categories

Let `A` be an abelian category. This file relates simplicial homotopies of simplicial objects
of `A` to chain homotopies of their normalized Moore complexes, in the direction converse to
[Stacks, Tag 019S]: *every* chain homotopy between `N(a)` and `N(b)` comes from a simplicial
homotopy from `a` to `b`, and on the nose — the produced homotopy induces the given chain
homotopy, degree by degree.

For a complex `K` in an additive category the cylinder `⋄K = K.cylinder` — the homotopy cofiber of
`(1, -1) : K ⟶ K ⊞ K`, whose degree `n` part is `K_{n-1} ⊕ K_n ⊕ K_n` with differential
`(z, x, y) ↦ (-dz, dx + z, dy - z)` — carries a canonical triple: the two inclusions
`ι₀ K, ι₁ K : K ⟶ ⋄K` and a homotopy `⋄h` from `ι₀ K` to `ι₁ K` whose component `K_i ⟶ (⋄K)_j` for
`c.Rel j i` is the inclusion `inlX K i j`. Composing with that triple is a bijection from `⋄K ⟶ M`
onto the triples `(a, b, h)` with `a, b : K ⟶ M` and `h` a homotopy from `a` to `b`, and `K ↦ ⋄K`
is functorial by the unique action on morphisms compatible with the triple. So the cylinder
*represents* pairs of morphisms equipped with a homotopy.

### Main results

* `HomologicalComplex.cylinder.exists_map_descEquiv`: the cylinder of a homological complex
  represents the functor of pairs of morphisms equipped with a homotopy, by composition with
  the canonical triple `(ι₀, ι₁, ⋄h)`, and the construction is functorial.
* `CategoryTheory.SimplicialObject.exists_homotopy_of_homotopy_normalizedMooreComplex_map`:
  given a chain homotopy `H` between the maps `N(a), N(b) : N(U) ⟶ N(V)` of normalized Moore
  complexes, there is a simplicial homotopy from `a` to `b` whose induced chain homotopy on
  normalized Moore complexes is `H`.

### References

* [Stacks, Tag 01A2](https://stacks.math.columbia.edu/tag/01A2)
* [Stacks, Tag 01A4](https://stacks.math.columbia.edu/tag/01A4)
* [Stacks, Tag 019A](https://stacks.math.columbia.edu/tag/019A)
* [Stacks, Tag 019K](https://stacks.math.columbia.edu/tag/019K)
* [Stacks, Tag 019S](https://stacks.math.columbia.edu/tag/019S)
-/

section

@[expose] public section

universe v u

/-! ### The cylinder represents pairs of morphisms together with a homotopy -/

section CylinderRepresents

open CategoryTheory Category Limits Preadditive
open HomologicalComplex HomologicalComplex.cylinder

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {ι : Type*} {c : ComplexShape ι} [DecidableRel c.Rel]

/-- The canonical homotopy from `ι₀ K` to `ι₁ K`, whose component `K.X i ⟶ K.cylinder.X j`
for `c.Rel j i` is the inclusion `inlX K i j hij`; the source's `⋄h`. -/
private noncomputable def homotopyι₀ι₁ (K : HomologicalComplex C c)
    (hc : ∀ j, ∃ i, c.Rel i j) : Homotopy (ι₀ K) (ι₁ K) :=
  Homotopy.equivSubZero.symm ((Homotopy.ofEq (by
      rw [cylinder.ι₀, cylinder.ι₁, ← Preadditive.sub_comp]
      congr 1
      exact (biprod.hom_ext _ _ (by simp) (by simp)).symm)).trans
    (homotopyCofiber.inrCompHomotopy (biprod.lift (𝟙 K) (-𝟙 K)) hc))

private lemma homotopyι₀ι₁_hom (K : HomologicalComplex C c) (hc : ∀ j, ∃ i, c.Rel i j)
    (i j : ι) (hij : c.Rel j i) :
    (homotopyι₀ι₁ K hc).hom i j = inlX K i j hij := by
  simp only [homotopyι₀ι₁, Homotopy.equivSubZero, Equiv.coe_fn_symm_mk, Homotopy.trans_hom,
    Homotopy.ofEq_hom, Pi.zero_apply, zero_add]
  exact homotopyCofiber.inrCompHomotopy_hom _ hc i j hij

/-- The component of `cylinder.desc a b h` on the first summand is `h`. -/
private lemma inlX_desc_f {K M : HomologicalComplex C c} (a b : K ⟶ M) (h : Homotopy a b)
    (i j : ι) (hij : c.Rel j i) :
    inlX K i j hij ≫ (cylinder.desc a b h).f j = h.hom i j := by
  dsimp [cylinder.desc]
  rw [homotopyCofiber.inlX_desc_f]
  simp [Homotopy.equivSubZero]

/-- Two morphisms out of the cylinder agree as soon as their restrictions along `ι₀`, `ι₁`
and the inclusions `inlX` agree. -/
private lemma cylinder_hom_ext {K M : HomologicalComplex C c} {f g : K.cylinder ⟶ M}
    (h₀ : ι₀ K ≫ f = ι₀ K ≫ g) (h₁ : ι₁ K ≫ f = ι₁ K ≫ g)
    (hl : ∀ (i j : ι) (hij : c.Rel j i),
      inlX K i j hij ≫ f.f j = inlX K i j hij ≫ g.f j) : f = g := by
  have hr : homotopyCofiber.inr (biprod.lift (𝟙 K) (-𝟙 K)) ≫ f =
      homotopyCofiber.inr (biprod.lift (𝟙 K) (-𝟙 K)) ≫ g :=
    biprod.hom_ext' _ _ (by simpa [cylinder.ι₀] using h₀)
      (by simpa [cylinder.ι₁] using h₁)
  ext j
  by_cases hj : c.Rel j (c.next j)
  · refine homotopyCofiber.ext_from_X _ _ _ hj (hl _ _ hj) ?_
    simpa using congr_arg (fun u => HomologicalComplex.Hom.f u j) hr
  · refine homotopyCofiber.ext_from_X' (biprod.lift (𝟙 K) (-𝟙 K)) _ hj ?_
    simpa using congr_arg (fun u => HomologicalComplex.Hom.f u j) hr

omit [HasBinaryBiproducts C] [DecidableRel c.Rel] in
/-- Two triples `(a, b, h)` agree as soon as the morphisms agree and the homotopies agree in
the components indexed by related pairs. -/
private lemma sigma_ext {K M : HomologicalComplex C c}
    {x y : Σ (a : K ⟶ M) (b : K ⟶ M), Homotopy a b}
    (h₁ : x.1 = y.1) (h₂ : x.2.1 = y.2.1)
    (h : ∀ (i j : ι) (_ : c.Rel j i), x.2.2.hom i j = y.2.2.hom i j) : x = y := by
  obtain ⟨a, b, hx⟩ := x
  obtain ⟨a', b', hy⟩ := y
  dsimp only at h₁ h₂ h
  subst h₁
  subst h₂
  have : hx = hy := by
    ext i j
    by_cases hij : c.Rel j i
    · exact h _ _ hij
    · rw [hx.zero _ _ hij, hy.zero _ _ hij]
  rw [this]

/-- The action of the cylinder on a morphism: the morphism descending the triple
`(φ ≫ ι₀, φ ≫ ι₁, ⋄h ∘ φ)`. -/
private noncomputable def cylinderMap (hc : ∀ j, ∃ i, c.Rel i j)
    (K L : HomologicalComplex C c) (φ : K ⟶ L) : K.cylinder ⟶ L.cylinder :=
  cylinder.desc (φ ≫ ι₀ L) (φ ≫ ι₁ L) ((homotopyι₀ι₁ L hc).compLeft φ)

@[reassoc]
private lemma inlX_cylinderMap_f (hc : ∀ j, ∃ i, c.Rel i j)
    (K L : HomologicalComplex C c) (φ : K ⟶ L) (i j : ι) (hij : c.Rel j i) :
    inlX K i j hij ≫ (cylinderMap hc K L φ).f j = φ.f i ≫ inlX L i j hij := by
  rw [cylinderMap, inlX_desc_f, Homotopy.compLeft_hom, homotopyι₀ι₁_hom L hc i j hij]

/-- The bijection between triples `(a, b, h)` and morphisms out of the cylinder. -/
private noncomputable def descEquiv (hc : ∀ j, ∃ i, c.Rel i j)
    (K M : HomologicalComplex C c) :
    (Σ (a : K ⟶ M) (b : K ⟶ M), Homotopy a b) ≃ (K.cylinder ⟶ M) where
  toFun x := cylinder.desc x.1 x.2.1 x.2.2
  invFun f := ⟨ι₀ K ≫ f, ι₁ K ≫ f, (homotopyι₀ι₁ K hc).compRight f⟩
  left_inv x := by
    refine sigma_ext (by simp) (by simp) fun i j hij => ?_
    rw [Homotopy.compRight_hom, homotopyι₀ι₁_hom K hc i j hij, inlX_desc_f]
  right_inv f := by
    refine cylinder_hom_ext (by simp) (by simp) fun i j hij => ?_
    rw [inlX_desc_f, Homotopy.compRight_hom, homotopyι₀ι₁_hom K hc i j hij]

end

namespace HomologicalComplex.cylinder

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {ι : Type*} {c : ComplexShape ι} [DecidableRel c.Rel]

/-- **Stacks 01A2**.
Let `C` be an additive category and `c` a complex shape in which every index is the target of a
relation (as for chain complexes). Then the cylinder `⋄K = K.cylinder` of a complex `K` represents
the functor `M ↦ {(a, b, h) | a, b : K ⟶ M and h a homotopy from a to b}`: the map sending
`f : ⋄K ⟶ M` to the triple obtained by composing the two inclusions `ι₀ K, ι₁ K : K ⟶ ⋄K` and the
canonical homotopy between them with `f` is a bijection. Moreover `K ↦ ⋄K` is functorial, by the
unique action on morphisms compatible with the inclusions and with the canonical homotopy. -/
@[stacks 01A2]
public theorem exists_map_descEquiv (hc : ∀ j, ∃ i, c.Rel i j) :
    ∃ map : ∀ (K L : HomologicalComplex C c), (K ⟶ L) → (K.cylinder ⟶ L.cylinder),
      (∀ K : HomologicalComplex C c, map K K (𝟙 K) = 𝟙 K.cylinder) ∧
      (∀ (K L M : HomologicalComplex C c) (φ : K ⟶ L) (ψ : L ⟶ M),
        map K M (φ ≫ ψ) = map K L φ ≫ map L M ψ) ∧
      (∀ (K L : HomologicalComplex C c) (φ : K ⟶ L), ι₀ K ≫ map K L φ = φ ≫ ι₀ L) ∧
      (∀ (K L : HomologicalComplex C c) (φ : K ⟶ L), ι₁ K ≫ map K L φ = φ ≫ ι₁ L) ∧
      (∀ (K L : HomologicalComplex C c) (φ : K ⟶ L) (i j : ι) (hij : c.Rel j i),
        inlX K i j hij ≫ (map K L φ).f j = φ.f i ≫ inlX L i j hij) ∧
      ∀ K M : HomologicalComplex C c,
        ∃ e : (Σ (a : K ⟶ M) (b : K ⟶ M), Homotopy a b) ≃ (K.cylinder ⟶ M),
          ∀ x : Σ (a : K ⟶ M) (b : K ⟶ M), Homotopy a b,
            ι₀ K ≫ e x = x.1 ∧ ι₁ K ≫ e x = x.2.1 ∧
              ∀ (i j : ι) (hij : c.Rel j i),
                inlX K i j hij ≫ (e x).f j = x.2.2.hom i j := by
  refine ⟨cylinderMap hc, ?_, ?_, fun K L φ => by simp [cylinderMap],
    fun K L φ => by simp [cylinderMap], inlX_cylinderMap_f hc, fun K M =>
      ⟨descEquiv hc K M, fun x => ⟨by simp [descEquiv], by simp [descEquiv],
        fun i j hij => inlX_desc_f _ _ _ i j hij⟩⟩⟩
  · intro K
    refine cylinder_hom_ext (by simp [cylinderMap]) (by simp [cylinderMap])
      fun i j hij => ?_
    rw [inlX_cylinderMap_f hc]
    simp
  · intro K L M φ ψ
    refine cylinder_hom_ext (by simp [cylinderMap]) (by simp [cylinderMap])
      fun i j hij => ?_
    simp [inlX_cylinderMap_f_assoc hc, inlX_cylinderMap_f hc]

end HomologicalComplex.cylinder

end CylinderRepresents

/-! ### Every chain homotopy of normalized Moore complexes comes from a simplicial homotopy -/

section FromChainHomotopy

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open AlgebraicTopology AlgebraicTopology.DoldKan

section CylinderModel

open Opposite Simplicial SSet SSet.IntervalSimplex

/-! #### The simplicial object `U × Δ[1]` -/

@[instance_reducible]
private noncomputable def deltaOneFintype (m : SimplexCategoryᵒᵖ) :
    Fintype ((Δ[1] : SSet.{0}).obj m) :=
  letI : Fintype (m.unop ⟶ (⦋1⦌ : SimplexCategory)) := Fintype.ofFinite _
  Fintype.ofEquiv _ SSet.stdSimplex.objEquiv.symm

attribute [local instance] deltaOneFintype

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The cylinder `U × Δ[1]` of [Stacks, Tag 019K]: in degree `n` the coproduct of `Δ[1]_n`
copies of `U_n`. The index sets are finite, so the coproducts exist in any abelian
category. -/
private noncomputable def cyl (U : SimplicialObject A) : SimplicialObject A :=
  U.copower (Δ[1] : SSet.{0})

/-- The inclusion of the summand of `(U × Δ[1])_n` indexed by `α ∈ Δ[1]_n`. -/
private noncomputable def cylι (U : SimplicialObject A) (m : SimplexCategoryᵒᵖ)
    (α : (Δ[1] : SSet.{0}).obj m) : U.obj m ⟶ (cyl U).obj m :=
  Sigma.ι (fun _ : (Δ[1] : SSet.{0}).obj m => U.obj m) α

private lemma cylι_hom_ext {U : SimplicialObject A} {m : SimplexCategoryᵒᵖ} {Z : A}
    {f g : (cyl U).obj m ⟶ Z} (h : ∀ α, cylι U m α ≫ f = cylι U m α ≫ g) : f = g :=
  Sigma.hom_ext _ _ h

/-- The projection of `(U × Δ[1])_n` onto the summand indexed by `α ∈ Δ[1]_n`, the source's
`pr_α`; the index sets are finite, so the coproduct is a biproduct and this exists. -/
private noncomputable def cylpr (U : SimplicialObject A) (m : SimplexCategoryᵒᵖ)
    (α : (Δ[1] : SSet.{0}).obj m) : (cyl U).obj m ⟶ U.obj m :=
  Sigma.desc fun β => if β = α then 𝟙 (U.obj m) else 0

private lemma cylι_comp_cylpr (U : SimplicialObject A) (m : SimplexCategoryᵒᵖ)
    (α β : (Δ[1] : SSet.{0}).obj m) :
    cylι U m β ≫ cylpr U m α = if β = α then 𝟙 (U.obj m) else 0 :=
  Sigma.ι_comp_desc _ _

private lemma cylι_comp_cylpr_assoc (U : SimplicialObject A) (m : SimplexCategoryᵒᵖ)
    (α β : (Δ[1] : SSet.{0}).obj m) {Z : A} (h : U.obj m ⟶ Z) :
    cylι U m β ≫ cylpr U m α ≫ h = (if β = α then 𝟙 (U.obj m) else 0) ≫ h := by
  rw [← Category.assoc, cylι_comp_cylpr]

private lemma cylι_comp_map (U : SimplicialObject A) {m m' : SimplexCategoryᵒᵖ} (φ : m ⟶ m')
    (α : (Δ[1] : SSet.{0}).obj m) :
    cylι U m α ≫ (cyl U).map φ = U.map φ ≫ cylι U m' ((Δ[1] : SSet.{0}).map φ α) :=
  Sigma.ι_comp_map' _ _ _

private lemma cylι_comp_delta (U : SimplicialObject A) {n : ℕ} (i : Fin (n + 2))
    (β : (Δ[1] : SSet.{0}) _⦋n + 1⦌) :
    cylι U (op ⦋n + 1⦌) β ≫ (cyl U).δ i
      = U.δ i ≫ cylι U (op ⦋n⦌) ((Δ[1] : SSet.{0}).δ i β) :=
  cylι_comp_map U _ β

private lemma cylι_comp_sigma (U : SimplicialObject A) {n : ℕ} (i : Fin (n + 1))
    (β : (Δ[1] : SSet.{0}) _⦋n⦌) :
    cylι U (op ⦋n⦌) β ≫ (cyl U).σ i
      = U.σ i ≫ cylι U (op ⦋n + 1⦌) ((Δ[1] : SSet.{0}).σ i β) :=
  cylι_comp_map U _ β

private lemma cylι_comp_sigma_assoc (U : SimplicialObject A) {n : ℕ} (i : Fin (n + 1))
    (β : (Δ[1] : SSet.{0}) _⦋n⦌) {Z : A} (h : (cyl U).obj (op ⦋n + 1⦌) ⟶ Z) :
    cylι U (op ⦋n⦌) β ≫ (cyl U).σ i ≫ h
      = U.σ i ≫ cylι U (op ⦋n + 1⦌) ((Δ[1] : SSet.{0}).σ i β) ≫ h := by
  rw [← Category.assoc, cylι_comp_sigma, Category.assoc]

/-- The projection of `(U × Δ[1])_n` onto `U_n`, the identity on every summand. -/
private noncomputable def cylπApp (U : SimplicialObject A) (m : SimplexCategoryᵒᵖ) :
    (cyl U).obj m ⟶ U.obj m :=
  Sigma.desc fun _ => 𝟙 (U.obj m)

private lemma cylι_comp_cylπApp (U : SimplicialObject A) (m : SimplexCategoryᵒᵖ)
    (α : (Δ[1] : SSet.{0}).obj m) : cylι U m α ≫ cylπApp U m = 𝟙 (U.obj m) :=
  Sigma.ι_comp_desc _ _

/-- The projection `U × Δ[1] ⟶ U`, the identity on every summand. -/
private noncomputable def cylπ (U : SimplicialObject A) : cyl U ⟶ U where
  app m := cylπApp U m
  naturality m m' φ := by
    refine cylι_hom_ext fun α => ?_
    have h1 : cylι U m α ≫ (cyl U).map φ ≫ cylπApp U m' = U.map φ := by
      rw [← Category.assoc, cylι_comp_map, Category.assoc, cylι_comp_cylπApp, Category.comp_id]
    have h2 : cylι U m α ≫ cylπApp U m ≫ U.map φ = U.map φ := by
      rw [← Category.assoc, cylι_comp_cylπApp, Category.id_comp]
    rw [h1, h2]

private lemma cylι_comp_cylπ (U : SimplicialObject A) (m : SimplexCategoryᵒᵖ)
    (α : (Δ[1] : SSet.{0}).obj m) : cylι U m α ≫ (cylπ U).app m = 𝟙 (U.obj m) :=
  cylι_comp_cylπApp U m α

private lemma cylι_comp_cylπ_assoc (U : SimplicialObject A) (m : SimplexCategoryᵒᵖ)
    (α : (Δ[1] : SSet.{0}).obj m) {Z : A} (h : U.obj m ⟶ Z) :
    cylι U m α ≫ (cylπ U).app m ≫ h = h := by
  rw [← Category.assoc, cylι_comp_cylπ, Category.id_comp]

/-- The inclusion of `U` as the summand indexed by the constant `a`-simplex: the two vertex
inclusions `e₀`, `e₁ : U ⟶ U × Δ[1]`. -/
private noncomputable def cylEdge (U : SimplicialObject A) (a : Fin 2) : U ⟶ cyl U where
  app m := cylι U m (stdSimplex.const 1 a m)
  naturality m m' φ := by
    rw [cylι_comp_map, map_const]

private lemma cylEdge_app (U : SimplicialObject A) (a : Fin 2) (m : SimplexCategoryᵒᵖ) :
    (cylEdge U a).app m = cylι U m (stdSimplex.const 1 a m) :=
  rfl

private lemma cylEdge_comp_cylπ (U : SimplicialObject A) (a : Fin 2) :
    cylEdge U a ≫ cylπ U = 𝟙 U := by
  ext m
  rw [NatTrans.comp_app, cylEdge_app, NatTrans.id_app]
  exact cylι_comp_cylπ U m _

/-! #### The tautological homotopy -/

/-- The `i`-th component in degree `n` of the tautological homotopy from `e₀` to `e₁`: the
`i`-th degeneracy of `U` followed by the inclusion of the summand indexed by `γ_i`. -/
private noncomputable def cylHtpyH (U : SimplicialObject A) {n : ℕ} (i : Fin (n + 1)) :
    U.obj (op ⦋n⦌) ⟶ (cyl U).obj (op ⦋n + 1⦌) :=
  U.σ i ≫ cylι U (op ⦋n + 1⦌) (stepSimplex i)

/-- The tautological simplicial homotopy from `e₀` to `e₁` on `U × Δ[1]`. -/
private noncomputable def cylHtpy (U : SimplicialObject A) :
    CategoryTheory.SimplicialObject.Homotopy (cylEdge U 0) (cylEdge U 1) where
  h i := cylHtpyH U i
  h_zero_comp_δ_zero n := by
    dsimp only [cylHtpyH, cylEdge]
    rw [Category.assoc, cylι_comp_delta, ← Category.assoc,
      U.δ_comp_σ_self' (i := (0 : Fin (n + 1))) (by simp), Category.id_comp,
      delta_zero_stepSimplex_zero]
  h_last_comp_δ_last n := by
    dsimp only [cylHtpyH, cylEdge]
    rw [Category.assoc, cylι_comp_delta, ← Category.assoc,
      U.δ_comp_σ_succ' (i := Fin.last n) (Fin.succ_last n).symm, Category.id_comp,
      delta_last_stepSimplex_last]
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    dsimp only [cylHtpyH]
    rw [Category.assoc, cylι_comp_delta, ← Category.assoc, U.δ_comp_σ_of_le hij,
      delta_castSucc_stepSimplex_succ i j hij, Category.assoc]
  h_succ_comp_δ_castSucc_succ j := by
    dsimp only [cylHtpyH]
    rw [Category.assoc, cylι_comp_delta, ← Category.assoc,
      U.δ_comp_σ_self' (i := j.succ) (Fin.succ_castSucc j), Category.id_comp,
      Category.assoc, cylι_comp_delta, ← Category.assoc,
      U.δ_comp_σ_succ' (i := j.castSucc) rfl, Category.id_comp,
      delta_stepSimplex_succ_eq]
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    dsimp only [cylHtpyH]
    rw [Category.assoc, cylι_comp_delta, ← Category.assoc, U.δ_comp_σ_of_gt hji,
      delta_succ_stepSimplex_castSucc i j hji, Category.assoc]
  h_comp_σ_castSucc_of_le i j hij := by
    dsimp only [cylHtpyH]
    rw [Category.assoc, cylι_comp_sigma, ← Category.assoc, U.σ_comp_σ hij,
      sigma_castSucc_stepSimplex i j hij, Category.assoc]
  h_comp_σ_succ_of_lt i j hji := by
    dsimp only [cylHtpyH]
    rw [Category.assoc, cylι_comp_sigma, ← Category.assoc, ← U.σ_comp_σ hji,
      sigma_succ_stepSimplex i j hji, Category.assoc]

private lemma cylHtpy_h (U : SimplicialObject A) {n : ℕ} (i : Fin (n + 1)) :
    (cylHtpy U).h i = U.σ i ≫ cylι U (op ⦋n + 1⦌) (stepSimplex i) :=
  rfl

/-! #### Degeneracies and the normalized Moore complex -/

/-- The splitting `p_X : s(X) ⟶ N(X)` of the inclusion kills degeneracies. -/
private lemma degeneraciesVanish_PInftyToNormalizedMooreComplex (U : SimplicialObject A)
    (n : ℕ) : DegeneraciesVanish ((PInftyToNormalizedMooreComplex U).f n) := by
  have h : (PInfty (X := U)).f n ≫ (PInftyToNormalizedMooreComplex U).f n
      = (PInftyToNormalizedMooreComplex U).f n :=
    HomologicalComplex.congr_hom (PInfty_comp_PInftyToNormalizedMooreComplex U) n
  rw [← h]
  exact (degeneraciesVanishPInfty_f U n).comp _

/-- A morphism out of `s(X)_n` that kills degeneracies is unchanged by `P^∞`. -/
private lemma PInfty_f_comp_of_degeneraciesVanish {U : SimplicialObject A} {n : ℕ} {Z : A}
    {f : U.obj (Opposite.op (SimplexCategory.mk n)) ⟶ Z} (hf : DegeneraciesVanish f) :
    (PInfty (X := U)).f n ≫ f = f := by
  have hQ : QInfty.f n ≫ f = 0 := (degeneraciesVanish_iff_QInfty_f_comp f).mp hf
  have h := PInfty_f_add_QInfty_f (X := U) n =≫ f
  rw [Preadditive.add_comp, hQ, add_zero, Category.id_comp] at h
  exact h

/-! #### The splitting `N ⊆ s` in a fixed degree -/

/-- The inclusion `N(U)_n ⟶ U_n`. -/
private noncomputable def normIncl (U : SimplicialObject A) (n : ℕ) :
    ((normalizedMooreComplex A).obj U).X n ⟶ U.obj (op ⦋n⦌) :=
  (inclusionOfMooreComplexMap U).f n

/-- The splitting `U_n ⟶ N(U)_n` of `normIncl`, the degree `n` part of `p_U`. -/
private noncomputable def normProj (U : SimplicialObject A) (n : ℕ) :
    U.obj (op ⦋n⦌) ⟶ ((normalizedMooreComplex A).obj U).X n :=
  (PInftyToNormalizedMooreComplex U).f n

/-- The differential of the alternating face map complex in a fixed degree. -/
@[sga "4 V 1.10" "more general"]
private noncomputable def altD (U : SimplicialObject A) (n : ℕ) :
    U.obj (op ⦋n + 1⦌) ⟶ U.obj (op ⦋n⦌) :=
  ((alternatingFaceMapComplex A).obj U).d (n + 1) n

private lemma altD_eq (U : SimplicialObject A) (n : ℕ) :
    ((alternatingFaceMapComplex A).obj U).d (n + 1) n = altD U n := rfl

private lemma altMap_f {U V : SimplicialObject A} (f : U ⟶ V) (n : ℕ) :
    ((alternatingFaceMapComplex A).map f).f n = f.app (op ⦋n⦌) := rfl

private lemma normIncl_comp_normProj (U : SimplicialObject A) (n : ℕ) :
    normIncl U n ≫ normProj U n = 𝟙 (((normalizedMooreComplex A).obj U).X n) :=
  HomologicalComplex.congr_hom (splitMonoInclusionOfMooreComplexMap U).id n

private lemma normProj_comp_normIncl (U : SimplicialObject A) (n : ℕ) :
    normProj U n ≫ normIncl U n = (PInfty (X := U)).f n :=
  HomologicalComplex.congr_hom
    (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap U) n

private lemma degeneraciesVanish_normProj (U : SimplicialObject A) (n : ℕ) :
    DegeneraciesVanish (normProj U n) :=
  degeneraciesVanish_PInftyToNormalizedMooreComplex U n

private lemma normProj_naturality {U V : SimplicialObject A} (f : U ⟶ V) (n : ℕ) :
    f.app (op ⦋n⦌) ≫ normProj V n = normProj U n ≫ ((normalizedMooreComplex A).map f).f n :=
  HomologicalComplex.congr_hom (PInftyToNormalizedMooreComplex_naturality f) n

private lemma normIncl_naturality {U V : SimplicialObject A} (f : U ⟶ V) (n : ℕ) :
    ((normalizedMooreComplex A).map f).f n ≫ normIncl V n = normIncl U n ≫ f.app (op ⦋n⦌) :=
  HomologicalComplex.congr_hom (NatTrans.naturality (inclusionOfMooreComplex A) f) n

private lemma normProj_comm (U : SimplicialObject A) (n : ℕ) :
    normProj U (n + 1) ≫ ((normalizedMooreComplex A).obj U).d (n + 1) n
      = altD U n ≫ normProj U n :=
  (PInftyToNormalizedMooreComplex U).comm (n + 1) n

/-! #### The retraction -/

/-- The degreewise family of the retraction: the source's `pr_{α^n_{n+1}}`, the projection onto
the summand indexed by the constant `0`-simplex, read off the normalized Moore complex of
`U × Δ[1]` and pushed into that of `U`. -/
private noncomputable def retrS (U : SimplicialObject A) (n : ℕ) :
    ((normalizedMooreComplex A).obj (cyl U)).X n ⟶ ((normalizedMooreComplex A).obj U).X n :=
  normIncl (cyl U) n ≫ cylpr U (op ⦋n⦌) (stdSimplex.const 1 0 (op ⦋n⦌)) ≫ normProj U n

private lemma degeneraciesVanish_cylpr_comp (U : SimplicialObject A) (n : ℕ) :
    DegeneraciesVanish
      (cylpr U (op ⦋n⦌) (stdSimplex.const 1 0 (op ⦋n⦌)) ≫ normProj U n) := by
  obtain _ | m := n
  · simp
  · rw [degeneraciesVanish_succ_iff]
    intro i
    refine cylι_hom_ext fun β => ?_
    rw [comp_zero, cylι_comp_sigma_assoc, cylι_comp_cylpr_assoc]
    split_ifs
    · rw [Category.id_comp, (degeneraciesVanish_normProj U (m + 1)).σ_comp i]
    · rw [zero_comp, comp_zero]

private lemma normProj_comp_retrS (U : SimplicialObject A) (n : ℕ) :
    normProj (cyl U) n ≫ retrS U n
      = cylpr U (op ⦋n⦌) (stdSimplex.const 1 0 (op ⦋n⦌)) ≫ normProj U n := by
  rw [retrS, ← Category.assoc, normProj_comp_normIncl]
  exact PInfty_f_comp_of_degeneraciesVanish (degeneraciesVanish_cylpr_comp U n)

/-- The composite of the chain homotopy induced by `Λ` with any morphism killing each
`σ_k ≫ ι_{γ_k}` vanishes. -/
private lemma htpy_hom_comp (U : SimplicialObject A) (n : ℕ) {Z : A}
    (g : (cyl U).obj (op ⦋n + 1⦌) ⟶ Z)
    (hg : ∀ k : Fin (n + 1), U.σ k ≫ cylι U (op ⦋n + 1⦌) (stepSimplex k) ≫ g = 0) :
    (cylHtpy U).toChainHomotopy.hom n (n + 1) ≫ g = 0 := by
  dsimp only [CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy]
  rw [CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
    Preadditive.neg_comp, Preadditive.sum_comp, neg_eq_zero]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Preadditive.zsmul_comp]
  have hk : (cylHtpy U).h k ≫ g = 0 := by
    rw [cylHtpy_h, Category.assoc]
    exact hg k
  rw [hk, smul_zero]

private lemma htpy_hom_comp_cylpr (U : SimplicialObject A) (n : ℕ) :
    (cylHtpy U).toChainHomotopy.hom n (n + 1) ≫
        cylpr U (op ⦋n + 1⦌) (stdSimplex.const 1 0 (op ⦋n + 1⦌)) ≫ normProj U (n + 1) = 0 := by
  refine htpy_hom_comp U n _ fun k => ?_
  rw [cylι_comp_cylpr_assoc]
  split_ifs with hc
  · exact absurd hc (stepSimplex_ne_const_zero k)
  · rw [zero_comp, comp_zero]

private lemma htpy_hom_comp_cylπ (U : SimplicialObject A) (n : ℕ) :
    (cylHtpy U).toChainHomotopy.hom n (n + 1) ≫
        (cylπ U).app (op ⦋n + 1⦌) ≫ normProj U (n + 1) = 0 := by
  refine htpy_hom_comp U n _ fun k => ?_
  rw [cylι_comp_cylπ_assoc, (degeneraciesVanish_normProj U (n + 1)).σ_comp k]

/-! #### The two vertex inclusions against the retraction -/

private lemma edge_zero_app_comp_cylpr (U : SimplicialObject A) (n : ℕ) :
    (cylEdge U 0).app (op ⦋n⦌) ≫ cylpr U (op ⦋n⦌) (stdSimplex.const 1 0 (op ⦋n⦌))
      = 𝟙 (U.obj (op ⦋n⦌)) := by
  rw [cylEdge_app, cylι_comp_cylpr]
  split_ifs with h
  · rfl
  · exact absurd rfl h

private lemma edge_one_app_comp_cylpr (U : SimplicialObject A) (n : ℕ) :
    (cylEdge U 1).app (op ⦋n⦌) ≫ cylpr U (op ⦋n⦌) (stdSimplex.const 1 0 (op ⦋n⦌)) = 0 := by
  rw [cylEdge_app, cylι_comp_cylpr]
  split_ifs with h
  · exact absurd h (const_one_ne_const_zero n)
  · rfl

private lemma map_edge_zero_comp_retrS (U : SimplicialObject A) (n : ℕ) :
    ((normalizedMooreComplex A).map (cylEdge U 0)).f n ≫ retrS U n
      = 𝟙 (((normalizedMooreComplex A).obj U).X n) := by
  rw [retrS, ← Category.assoc, normIncl_naturality, Category.assoc,
    ← Category.assoc ((cylEdge U 0).app (op ⦋n⦌)), edge_zero_app_comp_cylpr, Category.id_comp,
    normIncl_comp_normProj]

private lemma map_edge_one_comp_retrS (U : SimplicialObject A) (n : ℕ) :
    ((normalizedMooreComplex A).map (cylEdge U 1)).f n ≫ retrS U n = 0 := by
  rw [retrS, ← Category.assoc, normIncl_naturality, Category.assoc,
    ← Category.assoc ((cylEdge U 1).app (op ⦋n⦌)), edge_one_app_comp_cylpr, zero_comp, comp_zero]

private lemma map_edge_comp_map_cylπ (U : SimplicialObject A) (a : Fin 2) (n : ℕ) :
    ((normalizedMooreComplex A).map (cylEdge U a)).f n ≫
        ((normalizedMooreComplex A).map (cylπ U)).f n
      = 𝟙 (((normalizedMooreComplex A).obj U).X n) := by
  rw [← HomologicalComplex.comp_f, ← CategoryTheory.Functor.map_comp, cylEdge_comp_cylπ,
    CategoryTheory.Functor.map_id, HomologicalComplex.id_f]

/-! #### The composite of the homotopy with the retraction -/

/-- The morphism `N(U)_n ⟶ N(U × Δ[1])_{n + 1}` given by the chain homotopy induced by `Λ`,
conjugated by the splitting `N ⊆ s`. -/
private noncomputable def bigT (U : SimplicialObject A) (n : ℕ) :
    ((normalizedMooreComplex A).obj U).X n ⟶
      ((normalizedMooreComplex A).obj (cyl U)).X (n + 1) :=
  normIncl U n ≫ (cylHtpy U).toChainHomotopy.hom n (n + 1) ≫ normProj (cyl U) (n + 1)

private lemma bigT_comp_retrS (U : SimplicialObject A) (n : ℕ) :
    bigT U n ≫ retrS U (n + 1) = 0 := by
  rw [bigT, Category.assoc, Category.assoc, normProj_comp_retrS, htpy_hom_comp_cylpr, comp_zero]

private lemma bigT_comp_map_cylπ (U : SimplicialObject A) (n : ℕ) :
    bigT U n ≫ ((normalizedMooreComplex A).map (cylπ U)).f (n + 1) = 0 := by
  rw [bigT, Category.assoc, Category.assoc, ← normProj_naturality, htpy_hom_comp_cylπ, comp_zero]

/-- The `dNext` term of the homotopy relation, typed as a morphism `U_n ⟶ (U × Δ[1])_n`. -/
private noncomputable def dNextH (U : SimplicialObject A) (n : ℕ) :
    U.obj (op ⦋n⦌) ⟶ (cyl U).obj (op ⦋n⦌) :=
  dNext n (cylHtpy U).toChainHomotopy.hom

private lemma dNextH_eq (U : SimplicialObject A) (n : ℕ) :
    dNext n (cylHtpy U).toChainHomotopy.hom = dNextH U n := rfl

private lemma dNextH_comp_cylpr (U : SimplicialObject A) (n : ℕ) :
    dNextH U n ≫ cylpr U (op ⦋n⦌) (stdSimplex.const 1 0 (op ⦋n⦌)) ≫ normProj U n = 0 := by
  obtain _ | m := n
  · have h0 : dNextH U 0 = 0 := by
      rw [← dNextH_eq]
      apply dNext_eq_zero
      simp
    rw [h0, zero_comp]
  · have h1 : dNextH U (m + 1)
        = ((alternatingFaceMapComplex A).obj U).d (m + 1) m ≫
          (cylHtpy U).toChainHomotopy.hom m (m + 1) := by
      rw [← dNextH_eq]
      exact dNext_eq _ (show (ComplexShape.down ℕ).Rel (m + 1) m by simp)
    rw [h1, Category.assoc, htpy_hom_comp_cylpr, comp_zero]

private lemma bigT_comp_d_comp_retrS (U : SimplicialObject A) (n : ℕ) :
    bigT U n ≫ ((normalizedMooreComplex A).obj (cyl U)).d (n + 1) n ≫ retrS U n
      = 𝟙 (((normalizedMooreComplex A).obj U).X n) := by
  have hchi : ((cylHtpy U).toChainHomotopy.hom n (n + 1) ≫ altD (cyl U) n) ≫
      (cylpr U (op ⦋n⦌) (stdSimplex.const 1 0 (op ⦋n⦌)) ≫ normProj U n) = normProj U n := by
    have h := (cylHtpy U).toChainHomotopy.comm n
    rw [prevD_eq _ (show (ComplexShape.down ℕ).Rel (n + 1) n by simp), altD_eq, dNextH_eq,
      altMap_f, altMap_f] at h
    have h2 := h =≫ (cylpr U (op ⦋n⦌) (stdSimplex.const 1 0 (op ⦋n⦌)) ≫ normProj U n)
    rw [Preadditive.add_comp, Preadditive.add_comp, dNextH_comp_cylpr, zero_add,
      ← Category.assoc ((cylEdge U 1).app (op ⦋n⦌)), edge_one_app_comp_cylpr, zero_comp,
      add_zero, ← Category.assoc ((cylEdge U 0).app (op ⦋n⦌)), edge_zero_app_comp_cylpr,
      Category.id_comp] at h2
    exact h2.symm
  rw [bigT, Category.assoc, Category.assoc,
    ← Category.assoc (normProj (cyl U) (n + 1)), normProj_comm,
    Category.assoc (altD (cyl U) n), normProj_comp_retrS,
    ← Category.assoc ((cylHtpy U).toChainHomotopy.hom n (n + 1)), hchi,
    normIncl_comp_normProj]

/-! #### The morphism to the cylinder -/

/-- The component of `ψ` in the summand `N(U)_{n-1}` of the cylinder: the source's
`(-1)^n pr_{α^n_n} ≫ d^n_n`, here in the form `d ∘ s - s ∘ d`. -/
private noncomputable def psiP (U : SimplicialObject A) (n : ℕ) :
    ((normalizedMooreComplex A).obj (cyl U)).X n ⟶
      ((normalizedMooreComplex A).obj U).cylinder.X n :=
  match n with
  | 0 => 0
  | (j + 1) => (((normalizedMooreComplex A).obj (cyl U)).d (j + 1) j ≫ retrS U j -
      retrS U (j + 1) ≫ ((normalizedMooreComplex A).obj U).d (j + 1) j) ≫
      HomologicalComplex.cylinder.inlX ((normalizedMooreComplex A).obj U) j (j + 1) (by simp)

private lemma psiP_zero (U : SimplicialObject A) : psiP U 0 = 0 := rfl

private lemma psiP_succ (U : SimplicialObject A) (j : ℕ) :
    psiP U (j + 1) = (((normalizedMooreComplex A).obj (cyl U)).d (j + 1) j ≫ retrS U j -
      retrS U (j + 1) ≫ ((normalizedMooreComplex A).obj U).d (j + 1) j) ≫
      HomologicalComplex.cylinder.inlX ((normalizedMooreComplex A).obj U) j (j + 1) (by simp) :=
  rfl

/-- The retraction `ψ : N(U × Δ[1]) ⟶ ⋄N(U)`: the morphism to the cylinder given by the morphism of
complexes `N(π)` together with the degreewise family `retrS`, the source's `pr_{α^n_{n+1}}`. -/
private noncomputable def psi (U : SimplicialObject A) :
    (normalizedMooreComplex A).obj (cyl U) ⟶ ((normalizedMooreComplex A).obj U).cylinder :=
  (normalizedMooreComplex A).map (cylπ U) ≫
      HomologicalComplex.cylinder.ι₁ ((normalizedMooreComplex A).obj U) +
    Homotopy.nullHomotopicMap' fun i j hij =>
      retrS U i ≫ HomologicalComplex.cylinder.inlX ((normalizedMooreComplex A).obj U) i j hij

private lemma psi_eq (U : SimplicialObject A) :
    psi U = (normalizedMooreComplex A).map (cylπ U) ≫
        HomologicalComplex.cylinder.ι₁ ((normalizedMooreComplex A).obj U) +
      Homotopy.nullHomotopicMap' (fun i j hij =>
        retrS U i ≫
          HomologicalComplex.cylinder.inlX ((normalizedMooreComplex A).obj U) i j hij) :=
  rfl

private lemma lift_comp_inrX (U : SimplicialObject A) (n : ℕ) :
    (biprod.lift (𝟙 ((normalizedMooreComplex A).obj U))
        (-𝟙 ((normalizedMooreComplex A).obj U))).f n ≫
        HomologicalComplex.cylinder.inrX ((normalizedMooreComplex A).obj U) n
      = (HomologicalComplex.cylinder.ι₀ ((normalizedMooreComplex A).obj U)).f n
        - (HomologicalComplex.cylinder.ι₁ ((normalizedMooreComplex A).obj U)).f n := by
  have h : (biprod.lift (𝟙 ((normalizedMooreComplex A).obj U))
      (-𝟙 ((normalizedMooreComplex A).obj U)) :
        (normalizedMooreComplex A).obj U ⟶ _) = biprod.inl - biprod.inr :=
    biprod.hom_ext _ _ (by simp) (by simp)
  have h2 : (biprod.lift (𝟙 ((normalizedMooreComplex A).obj U))
        (-𝟙 ((normalizedMooreComplex A).obj U))).f n
      = (biprod.inl : (normalizedMooreComplex A).obj U ⟶ _).f n
        - (biprod.inr : (normalizedMooreComplex A).obj U ⟶ _).f n := by
    rw [← HomologicalComplex.sub_f_apply, h]
  rw [h2, Preadditive.sub_comp]
  rfl

private lemma nullHtpy_f (U : SimplicialObject A) (n : ℕ) :
    (Homotopy.nullHomotopicMap' fun i j hij =>
          retrS U i ≫
            HomologicalComplex.cylinder.inlX
              ((normalizedMooreComplex A).obj U) i j hij).f n
      = psiP U n + retrS U n ≫
          ((HomologicalComplex.cylinder.ι₀ ((normalizedMooreComplex A).obj U)).f n
            - (HomologicalComplex.cylinder.ι₁ ((normalizedMooreComplex A).obj U)).f n) := by
  obtain _ | j := n
  · rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left
      (show (ComplexShape.down ℕ).Rel 1 0 by simp)
      (show ∀ l : ℕ, ¬ (ComplexShape.down ℕ).Rel 0 l by simp), Category.assoc,
      HomologicalComplex.homotopyCofiber_d,
      HomologicalComplex.homotopyCofiber.inlX_d' _ 1 0 (by simp) (by simp),
      lift_comp_inrX, psiP_zero, zero_add]
  · rw [Homotopy.nullHomotopicMap'_f
      (show (ComplexShape.down ℕ).Rel (j + 2) (j + 1) by simp)
      (show (ComplexShape.down ℕ).Rel (j + 1) j by simp), Category.assoc,
      HomologicalComplex.homotopyCofiber_d,
      HomologicalComplex.homotopyCofiber.inlX_d _ (j + 2) (j + 1) j (by simp) (by simp),
      Preadditive.comp_add, Preadditive.comp_neg, lift_comp_inrX, psiP_succ,
      Preadditive.sub_comp]
    simp only [Category.assoc]
    abel

private lemma psi_f (U : SimplicialObject A) (n : ℕ) :
    (psi U).f n = ((normalizedMooreComplex A).map (cylπ U)).f n ≫
        (HomologicalComplex.cylinder.ι₁ ((normalizedMooreComplex A).obj U)).f n
      + (psiP U n + retrS U n ≫
          ((HomologicalComplex.cylinder.ι₀ ((normalizedMooreComplex A).obj U)).f n
            - (HomologicalComplex.cylinder.ι₁ ((normalizedMooreComplex A).obj U)).f n)) := by
  rw [psi_eq, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, nullHtpy_f]

private lemma map_edge_comp_psiP (U : SimplicialObject A) (a : Fin 2)
    (hs : ∀ n, ((normalizedMooreComplex A).map (cylEdge U a)).f n ≫ retrS U n
      = if a = 0 then 𝟙 (((normalizedMooreComplex A).obj U).X n) else 0) (n : ℕ) :
    ((normalizedMooreComplex A).map (cylEdge U a)).f n ≫ psiP U n = 0 := by
  obtain _ | j := n
  · rw [psiP_zero, comp_zero]
  · rw [psiP_succ, ← Category.assoc, Preadditive.comp_sub, ← Category.assoc, ← Category.assoc,
      ((normalizedMooreComplex A).map (cylEdge U a)).comm (j + 1) j, Category.assoc, hs j,
      hs (j + 1)]
    split_ifs
    · rw [Category.comp_id, Category.id_comp, sub_self, zero_comp]
    · rw [comp_zero, zero_comp, sub_self, zero_comp]

private lemma bigT_comp_psi (U : SimplicialObject A) (n : ℕ) :
    bigT U n ≫ (psi U).f (n + 1)
      = HomologicalComplex.cylinder.inlX ((normalizedMooreComplex A).obj U) n (n + 1)
          (by simp) := by
  rw [psi_f, Preadditive.comp_add, Preadditive.comp_add, ← Category.assoc,
    bigT_comp_map_cylπ, zero_comp, zero_add, psiP_succ, ← Category.assoc,
    Preadditive.comp_sub, bigT_comp_d_comp_retrS, ← Category.assoc, bigT_comp_retrS,
    zero_comp, sub_zero, Category.id_comp, ← Category.assoc, bigT_comp_retrS, zero_comp,
    add_zero]

private lemma map_edge_zero_comp_psi (U : SimplicialObject A) :
    (normalizedMooreComplex A).map (cylEdge U 0) ≫ psi U
      = HomologicalComplex.cylinder.ι₀ ((normalizedMooreComplex A).obj U) := by
  ext n
  have h3 := map_edge_comp_psiP U 0 (fun m => by rw [map_edge_zero_comp_retrS]; simp) n
  rw [HomologicalComplex.comp_f, psi_f, Preadditive.comp_add, Preadditive.comp_add,
    ← Category.assoc, map_edge_comp_map_cylπ, Category.id_comp, h3, ← Category.assoc,
    map_edge_zero_comp_retrS, Category.id_comp, zero_add]
  abel

private lemma map_edge_one_comp_psi (U : SimplicialObject A) :
    (normalizedMooreComplex A).map (cylEdge U 1) ≫ psi U
      = HomologicalComplex.cylinder.ι₁ ((normalizedMooreComplex A).obj U) := by
  ext n
  have h3 := map_edge_comp_psiP U 1 (fun m => by rw [map_edge_one_comp_retrS]; simp) n
  rw [HomologicalComplex.comp_f, psi_f, Preadditive.comp_add, Preadditive.comp_add,
    ← Category.assoc, map_edge_comp_map_cylπ, Category.id_comp, h3, ← Category.assoc,
    map_edge_one_comp_retrS, zero_comp, add_zero, add_zero]

end CylinderModel

section

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- For a simplicial object `U` of an abelian category there are a simplicial object `W`, two
morphisms `e₀, e₁ : U ⟶ W`, a simplicial homotopy `Λ` from `e₀` to `e₁` and a morphism
`ψ : N(W) ⟶ ⋄N(U)` to the cylinder of `N(U)` which carries `N(e₀)`, `N(e₁)` and the chain homotopy
induced by `Λ` on normalized Moore complexes to the universal triple `ι₀`, `ι₁`, `⋄h` of the
cylinder.

Equivalently: the morphism `Φ : ⋄N(U) ⟶ N(W)` which the universal property of the cylinder attaches
to the triple `(N(e₀), N(e₁), N(Λ))` is a split monomorphism, and `ψ` is a retraction of it. -/
private theorem exists_universal_homotopy_toCylinder (U : SimplicialObject A) :
    ∃ (W : SimplicialObject A) (e₀ e₁ : U ⟶ W)
      (Λ : CategoryTheory.SimplicialObject.Homotopy e₀ e₁)
      (ψ : (normalizedMooreComplex A).obj W ⟶
        ((normalizedMooreComplex A).obj U).cylinder),
      (normalizedMooreComplex A).map e₀ ≫ ψ = HomologicalComplex.cylinder.ι₀ _ ∧
      (normalizedMooreComplex A).map e₁ ≫ ψ = HomologicalComplex.cylinder.ι₁ _ ∧
      ∀ n : ℕ, (inclusionOfMooreComplexMap U).f n ≫ Λ.toChainHomotopy.hom n (n + 1) ≫
          (PInftyToNormalizedMooreComplex W).f (n + 1) ≫ ψ.f (n + 1) =
        HomologicalComplex.cylinder.inlX _ n (n + 1) (by simp) := by
  refine ⟨cyl U, cylEdge U 0, cylEdge U 1, cylHtpy U, psi U, map_edge_zero_comp_psi U,
    map_edge_one_comp_psi U, fun n => ?_⟩
  have h := bigT_comp_psi U n
  rw [bigT, Category.assoc, Category.assoc] at h
  exact h

end

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A] {U V : SimplicialObject A} {a b : U ⟶ V}

/-- **Stacks 01A4**.
Let `a, b : U ⟶ V` be morphisms of simplicial objects of an abelian category and let `H` be a chain
homotopy between the induced maps `N(a), N(b) : N(U) ⟶ N(V)` of normalized Moore complexes. Then
`a` and `b` are simplicially homotopic, and moreover the homotopy `K` can be chosen so that the
chain homotopy it induces on normalized Moore complexes is `H` itself: `Hₙ = p_V ∘ s(K)ₙ ∘ ι_U`,
where `s(K)` is the chain homotopy of `K` on the alternating face map complexes
([Stacks, Tag 019Q]) and `ι_U`, `p_V` are the canonical inclusion of and projection onto the
normalized Moore complex. By [Stacks, Tag 019L] such a `K` is the same thing as a homotopy
`h : U × Δ[1] ⟶ V` from `a` to `b` in the sense of [Stacks, Tag 019K], with
`K.h i = sⁿᵢ ≫ h_{n + 1, i + 1}`. -/
@[stacks 01A4 "the homotopy of 019K is presented by the family of components \
  `h_{n + 1, i + 1} ∘ sⁿᵢ` it corresponds to under 019L, which is Mathlib's \
  `SimplicialObject.Homotopy`, and out of which the chain homotopy `s(h)` of 019Q is built; \
  `N(h)` is `s(h)` conjugated by the canonical splitting `N ⊆ s` of 019A"]
public theorem exists_homotopy_of_homotopy_normalizedMooreComplex_map
    (H : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    ∃ K : Homotopy a b, ∀ n : ℕ, H.hom n (n + 1) =
      (inclusionOfMooreComplexMap U).f n ≫ K.toChainHomotopy.hom n (n + 1) ≫
        (PInftyToNormalizedMooreComplex V).f (n + 1) := by
  obtain ⟨W, e₀, e₁, Λ, ψ, hψ₀, hψ₁, hψh⟩ := exists_universal_homotopy_toCylinder U
  obtain ⟨-, -, -, -, -, -, huniv⟩ :=
    HomologicalComplex.cylinder.exists_map_descEquiv (C := A) (c := ComplexShape.down ℕ)
      (fun j => ⟨j + 1, by simp⟩)
  obtain ⟨e, he⟩ := huniv ((normalizedMooreComplex A).obj U) ((normalizedMooreComplex A).obj V)
  obtain ⟨hf₀, hf₁, hfh⟩ :=
    he ⟨(normalizedMooreComplex A).map a, (normalizedMooreComplex A).map b, H⟩
  set f := e ⟨(normalizedMooreComplex A).map a, (normalizedMooreComplex A).map b, H⟩ with hf
  clear_value f
  have : (normalizedMooreComplex A).IsEquivalence :=
    inferInstanceAs (CategoryTheory.Abelian.DoldKan.equivalence (A := A)).functor.IsEquivalence
  obtain ⟨φ, hφ⟩ : ∃ φ : W ⟶ V, (normalizedMooreComplex A).map φ = ψ ≫ f :=
    ⟨(normalizedMooreComplex A).preimage (ψ ≫ f), (normalizedMooreComplex A).map_preimage _⟩
  obtain rfl : a = e₀ ≫ φ := by
    refine (normalizedMooreComplex A).map_injective ?_
    rw [Functor.map_comp, hφ, ← Category.assoc, hψ₀, hf₀]
  obtain rfl : b = e₁ ≫ φ := by
    refine (normalizedMooreComplex A).map_injective ?_
    rw [Functor.map_comp, hφ, ← Category.assoc, hψ₁, hf₁]
  refine ⟨Λ.postcomp φ, fun n => ?_⟩
  have hcomp : (Λ.postcomp φ).toChainHomotopy.hom n (n + 1) =
      Λ.toChainHomotopy.hom n (n + 1) ≫ φ.app (Opposite.op (SimplexCategory.mk (n + 1))) := by
    dsimp [CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy]
    rw [CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
      CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
    simp [Preadditive.sum_comp, Preadditive.neg_comp]
  have h2 := hψh n =≫ f.f (n + 1)
  rw [hfh n (n + 1) (by simp)] at h2
  have hnat : ∀ m : ℕ, φ.app (Opposite.op (SimplexCategory.mk m)) ≫
      (PInftyToNormalizedMooreComplex V).f m =
      (PInftyToNormalizedMooreComplex W).f m ≫ ((normalizedMooreComplex A).map φ).f m :=
    fun m => HomologicalComplex.congr_hom (PInftyToNormalizedMooreComplex_naturality φ) m
  rw [hcomp, ← h2]
  simp only [Category.assoc]
  rw [hnat (n + 1), hφ, HomologicalComplex.comp_f]
  congr 2
  exact Category.assoc _ _ _

end CategoryTheory.SimplicialObject

end FromChainHomotopy

end

end

/-!
## The diamond complex and the comparison map into it

Let `C` be a preadditive category with binary biproducts and let `A` be a complex over `C`. The
diamond complex `⋄A` has `(⋄A)_n = A_n ⊕ A_n ⊕ A_{n+1}` and differential
`(x, y, z) ↦ (d x + z, d y - z, -d z)`, and it sits in a termwise split short exact sequence
`0 → A ⊕ A → ⋄A → A[-1] → 0`. Given a termwise split short exact sequence `0 → A ⊕ A → B → Cpx → 0`
whose connecting morphism `δ(s)` factors through `(1, -1) : A[-1] → A[-1] ⊕ A[-1]` as
`δ(s) = (1, -1) ∘ f`, there is a unique morphism `B ⟶ ⋄A` compatible with the two sequences and
with their termwise splittings; degreewise it is `(p_n, q_n, f_n ∘ r_n)`, where
`(p_n, q_n) : B_n → A_n ⊕ A_n` is the projection attached to the splitting.

Everything is stated for cochain complexes `CochainComplex C ℤ`, so the shift `A[-1]` is realized
as `shift1 A` with `(shift1 A)_n = A_{n+1}`. The diamond complex is `CochainComplex.diamond`, and
the other declarations of this section live in the namespace `CochainComplex.diamond`.

### Main definitions

* `shift1`: the shift `A[-1]`, with `(shift1 A)_n = A_{n+1}` and differential `-d`.
* `double`: the complex `A ⊕ A`.
* `col`: the degree-`i` component `(⋄A)_i ⟶ (⋄A)_{i+1}` of the diamond differential.
* `CochainComplex.diamond`: the diamond complex `⋄A`, with `(⋄A)_n = A_n ⊕ A_n ⊕ A_{n+1}`.
* `ι`: the inclusion `A ⊕ A ⟶ ⋄A`, `(u, v) ↦ (u, v, 0)`.
* `ρ`: the projection `⋄A ⟶ A[-1]`, `(x, y, z) ↦ z`.
* `σ`: the degree-`n` morphism `(A[-1])_n ⟶ (⋄A)_n`, `z ↦ (0, 0, z)`.
* `comparisonF`: the degree-`n` component `(p_n, q_n, r_n ≫ f_n)` of the comparison map.
* `comparisonMap`: the comparison map `B ⟶ ⋄A`.

### Main results

* `σ_ρ`: `σ A n` is a section of `(ρ A).f n`.
* `ir_zero`: the composite `A_n ⊕ A_n → B_n → Cpx_n` vanishes.
* `sP_zero`: the composite of `s n` with `(p n, q n)` vanishes.
* `comparison_ι`: `i ≫ comparisonMap = ι A`.
* `comparison_ρ`: `comparisonMap ≫ ρ A = r ≫ f`.
* `comparison_σ`: `s n ≫ (comparisonMap).f n = f.f n ≫ σ A n`.
* `comparison_unique`: a morphism `B ⟶ ⋄A` satisfying the conclusions of `comparison_ι` and
  `comparison_σ` is `comparisonMap`.
* `exists_unique_comparison`: existence and uniqueness of the comparison map `B ⟶ ⋄A`.

### References

* [Stacks, Tag 01A3](https://stacks.math.columbia.edu/tag/01A3)
-/

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.diamond

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

/-! ### The diamond complex and its structural maps -/

/-- The degree-`i` matrix `d_{⋄A,i} : (⋄A)_i ⟶ (⋄A)_{i+1}` of the diamond differential, sending
`(x, y, z)` to `(d x + z, d y - z, -d z)`. -/
noncomputable def col (A : CochainComplex C ℤ) (i : ℤ) :
    A.X i ⊞ A.X i ⊞ A.X (i + 1) ⟶ A.X (i + 1) ⊞ A.X (i + 1) ⊞ A.X ((i + 1) + 1) :=
  biprod.desc
    (biprod.lift (A.d i (i + 1)) (biprod.lift 0 0))
    (biprod.desc
      (biprod.lift 0 (biprod.lift (A.d i (i + 1)) 0))
      (biprod.lift (𝟙 _) (biprod.lift (-(𝟙 _)) (-(A.d (i + 1) ((i + 1) + 1))))))

/-- The diamond differential squares to zero: `col A i ≫ col A (i + 1) = 0`. -/
theorem col_col (A : CochainComplex C ℤ) (i : ℤ) : col A i ≫ col A (i + 1) = 0 := by
  unfold col; ext <;> simp [biprod.lift_desc]

/-- The diamond complex `⋄A` with `(⋄A)_n = A_n ⊕ A_n ⊕ A_{n+1}`. -/
@[implicit_reducible]
noncomputable def _root_.CochainComplex.diamond (A : CochainComplex C ℤ) : CochainComplex C ℤ where
  X n := A.X n ⊞ A.X n ⊞ A.X (n + 1)
  d i j := if h : i + 1 = j then col A i ≫ eqToHom (by rw [h]) else 0
  shape i j hij := by
    rw [ComplexShape.up_Rel] at hij
    exact dite_eq_right hij
  d_comp_d' i j k hij hjk := by
    simp only [ComplexShape.up_Rel] at hij hjk
    subst hij; subst hjk
    rw [dite_eq_left rfl, dite_eq_left rfl]; simp [col_col]

/-- The differential of `⋄A` from degree `i` to degree `i + 1` is `col A i`. -/
theorem diamond_d (A : CochainComplex C ℤ) (i : ℤ) :
    (diamond A).d i (i + 1) = col A i := by
  simp [diamond]

/-- The complex `A ⊕ A`. -/
@[implicit_reducible]
noncomputable def double (A : CochainComplex C ℤ) : CochainComplex C ℤ where
  X n := A.X n ⊞ A.X n
  d i j := biprod.map (A.d i j) (A.d i j)
  shape i j hij := by rw [A.shape _ _ hij]; ext <;> simp
  d_comp_d' i j k _ _ := by ext <;> simp

/-- The differential of `A ⊕ A` is the direct sum of two copies of the differential of `A`. -/
theorem double_d (A : CochainComplex C ℤ) (i j : ℤ) :
    (double A).d i j = biprod.map (A.d i j) (A.d i j) := rfl

/-- The shift `A[-1]`, realized cohomologically by `(shift1 A)_n = A_{n+1}`,
with differential `-d`. -/
@[implicit_reducible]
noncomputable def shift1 (A : CochainComplex C ℤ) : CochainComplex C ℤ where
  X n := A.X (n + 1)
  d i j := -(A.d (i + 1) (j + 1))
  shape i j hij := by
    rw [A.shape, neg_zero]
    simp only [ComplexShape.up_Rel] at hij ⊢
    omega
  d_comp_d' i j k hij hjk := by simp

omit [HasBinaryBiproducts C] in
/-- The differential of `A[-1]` from degree `i` to degree `j` is `-(A.d (i + 1) (j + 1))`. -/
theorem shift1_d (A : CochainComplex C ℤ) (i j : ℤ) :
    (shift1 A).d i j = -(A.d (i + 1) (j + 1)) := rfl

/-- In each degree, `(u, v) ↦ (u, v, 0)` commutes with the differentials of `A ⊕ A` and `⋄A`. -/
theorem ι_comm (A : CochainComplex C ℤ) (i : ℤ) :
    (biprod.lift biprod.fst (biprod.lift biprod.snd (0 : A.X i ⊞ A.X i ⟶ A.X (i + 1))) ≫
        col A i) =
      biprod.map (A.d i (i + 1)) (A.d i (i + 1)) ≫
        biprod.lift biprod.fst (biprod.lift biprod.snd 0) := by
  unfold col
  refine biprod.hom_ext' _ _ ?_ ?_
  · refine biprod.hom_ext _ _ ?_ ?_
    · simp
    · refine biprod.hom_ext _ _ ?_ ?_ <;> simp
  · refine biprod.hom_ext _ _ ?_ ?_
    · simp
    · refine biprod.hom_ext _ _ ?_ ?_ <;> simp

/-- The inclusion `ι : A ⊕ A → ⋄A`, `(u,v) ↦ (u,v,0)`. -/
noncomputable def ι (A : CochainComplex C ℤ) : double A ⟶ diamond A where
  f n := biprod.lift biprod.fst (biprod.lift biprod.snd 0)
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij; subst hij
    rw [diamond_d, double_d]
    exact ι_comm A i

/-- In each degree, `(x, y, z) ↦ z` commutes with the differentials of `⋄A` and `A[-1]`. -/
theorem ρ_comm (A : CochainComplex C ℤ) (i : ℤ) :
    (biprod.snd ≫ biprod.snd) ≫ (-(A.d (i + 1) ((i + 1) + 1))) =
      col A i ≫ (biprod.snd ≫ biprod.snd) := by
  unfold col
  refine biprod.hom_ext' _ _ ?_ ?_
  · simp
  · refine biprod.hom_ext' _ _ ?_ ?_ <;> simp

/-- The projection `ρ : ⋄A → A[-1]`, `(x,y,z) ↦ z`. -/
noncomputable def ρ (A : CochainComplex C ℤ) : diamond A ⟶ shift1 A where
  f n := biprod.snd ≫ biprod.snd
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij; subst hij
    rw [diamond_d, shift1_d]
    exact ρ_comm A i

/-- The degree-`n` morphism `σ_n : (A[-1])_n ⟶ (⋄A)_n`, `z ↦ (0, 0, z)`. -/
noncomputable def σ (A : CochainComplex C ℤ) (n : ℤ) :
    (shift1 A).X n ⟶ (diamond A).X n :=
  biprod.lift 0 (biprod.lift 0 (𝟙 _))

/-- `ρ` splits via `σ` in each degree: `σ_n ≫ ρ_n = 𝟙`. -/
theorem σ_ρ (A : CochainComplex C ℤ) (n : ℤ) :
    σ A n ≫ (ρ A).f n = 𝟙 _ := by
  dsimp only [σ, ρ]
  rw [biprod.lift_snd_assoc]
  exact biprod.lift_snd _ _

/-! ### Derived splitting identities

The hypotheses `hsr` (`s n ≫ r_n = 𝟙`), `hip` (`i_n ≫ (p n, q n) = 𝟙`) and `hsplit`
(`(p n, q n) ≫ i_n + r_n ≫ s n = 𝟙`) say that `(p, q, i, r, s)` realize a degreewise biproduct
decomposition `B_n ≅ (A_n ⊕ A_n) ⊕ Cpx_n`. They force two further vanishing identities. -/

variable {A B Cpx : CochainComplex C ℤ}
  {i : double A ⟶ B} {r : B ⟶ Cpx}
  {p q : ∀ n, B.X n ⟶ A.X n} {s : ∀ n, Cpx.X n ⟶ B.X n}
  {f : Cpx ⟶ shift1 A}

/-- The two maps of the short exact sequence compose to zero: `i.f n ≫ r.f n = 0`. -/
theorem ir_zero
    (hsr : ∀ n, s n ≫ r.f n = 𝟙 _)
    (hip : ∀ n, i.f n ≫ biprod.lift (p n) (q n) = 𝟙 _)
    (hsplit : ∀ n,
      biprod.lift (p n) (q n) ≫ i.f n + r.f n ≫ s n = 𝟙 (B.X n))
    (n : ℤ) : i.f n ≫ r.f n = 0 := by
  have h := hsplit n
  have key := congrArg (fun g => i.f n ≫ g) h
  simp only [Preadditive.comp_add] at key
  rw [reassoc_of% (hip n)] at key
  rw [Category.comp_id] at key
  have hzero : (i.f n ≫ r.f n) ≫ s n = 0 := by
    have h2 : i.f n ≫ r.f n ≫ s n = 0 := by
      rw [add_eq_left] at key
      exact key
    rw [Category.assoc]; exact h2
  have heq : i.f n ≫ r.f n = ((i.f n ≫ r.f n) ≫ s n) ≫ r.f n := by
    rw [Category.assoc, hsr n, Category.comp_id]
  rw [heq, hzero, Limits.zero_comp]

/-- The splitting `s` lands in the complement of the image of `i`, so the projection `(p, q)` kills
it: `s n ≫ biprod.lift (p n) (q n) = 0`. -/
theorem sP_zero
    (hsr : ∀ n, s n ≫ r.f n = 𝟙 _)
    (hip : ∀ n, i.f n ≫ biprod.lift (p n) (q n) = 𝟙 _)
    (hsplit : ∀ n,
      biprod.lift (p n) (q n) ≫ i.f n + r.f n ≫ s n = 𝟙 (B.X n))
    (n : ℤ) : s n ≫ biprod.lift (p n) (q n) = 0 := by
  have h := hsplit n
  have key := congrArg (fun g => g ≫ biprod.lift (p n) (q n)) h
  simp only [Preadditive.add_comp, Category.assoc, hip n, Category.id_comp] at key
  rw [show biprod.lift (p n) (q n) ≫ 𝟙 ((double A).X n) = biprod.lift (p n) (q n) from
    Category.comp_id _] at key
  have hzero : r.f n ≫ s n ≫ biprod.lift (p n) (q n) = 0 := by
    rw [add_eq_left] at key
    exact key
  have heq : s n ≫ biprod.lift (p n) (q n)
      = (s n ≫ r.f n) ≫ s n ≫ biprod.lift (p n) (q n) := by
    rw [hsr n, Category.id_comp]
  rw [heq, Category.assoc, hzero, Limits.comp_zero]

/-- The first component of `sP_zero`: `s n ≫ p n = 0`. -/
theorem sp_zero
    (hsr : ∀ n, s n ≫ r.f n = 𝟙 _)
    (hip : ∀ n, i.f n ≫ biprod.lift (p n) (q n) = 𝟙 _)
    (hsplit : ∀ n,
      biprod.lift (p n) (q n) ≫ i.f n + r.f n ≫ s n = 𝟙 (B.X n))
    (n : ℤ) : s n ≫ p n = 0 := by
  have h := sP_zero hsr hip hsplit n
  have key := congrArg (fun g => g ≫ biprod.fst) h
  simpa only [Category.assoc, biprod.lift_fst, Limits.zero_comp] using key

/-- The second component of `sP_zero`: `s n ≫ q n = 0`. -/
theorem sq_zero
    (hsr : ∀ n, s n ≫ r.f n = 𝟙 _)
    (hip : ∀ n, i.f n ≫ biprod.lift (p n) (q n) = 𝟙 _)
    (hsplit : ∀ n,
      biprod.lift (p n) (q n) ≫ i.f n + r.f n ≫ s n = 𝟙 (B.X n))
    (n : ℤ) : s n ≫ q n = 0 := by
  have h := sP_zero hsr hip hsplit n
  have key := congrArg (fun g => g ≫ biprod.snd) h
  simpa only [Category.assoc, biprod.lift_snd, Limits.zero_comp] using key

/-! ### The comparison map and its chain-map property -/

/-- The first component of the projection onto `A ⊕ A` restricts along `i` to `biprod.fst`. -/
private theorem i_comp_p (hip : ∀ n, i.f n ≫ biprod.lift (p n) (q n) = 𝟙 _) (n : ℤ) :
    i.f n ≫ p n = biprod.fst := by
  simpa using hip n =≫ biprod.fst

/-- The second component of the projection onto `A ⊕ A` restricts along `i` to `biprod.snd`. -/
private theorem i_comp_q (hip : ∀ n, i.f n ≫ biprod.lift (p n) (q n) = 𝟙 _) (n : ℤ) :
    i.f n ≫ q n = biprod.snd := by
  simpa using hip n =≫ biprod.snd

/-- The degree-`n` component of the comparison map,
`φ_n = (p_n, q_n, r_n ≫ f_n) : B_n ⟶ A_n ⊕ A_n ⊕ A_{n+1}`. -/
noncomputable def comparisonF (r : B ⟶ Cpx) (p q : ∀ n, B.X n ⟶ A.X n)
    (f : Cpx ⟶ shift1 A) (n : ℤ) :
    B.X n ⟶ (diamond A).X n :=
  biprod.lift (p n) (biprod.lift (q n) (r.f n ≫ f.f n))

/-- The comparison map commutes with the differentials:
`comparisonF r p q f n ≫ col A n = B.d n (n+1) ≫ comparisonF r p q f (n+1)`. Componentwise this
reads `p_n ≫ d_A + r_n f_n = d_B ≫ p_{n+1}`, `q_n ≫ d_A - r_n f_n = d_B ≫ q_{n+1}` and
`(r_n f_n) ≫ (-d_A) = d_B ≫ r_{n+1} f_{n+1}`. -/
theorem comparison_comm
    (hip : ∀ n, i.f n ≫ biprod.lift (p n) (q n) = 𝟙 _)
    (hsplit : ∀ n,
      biprod.lift (p n) (q n) ≫ i.f n + r.f n ≫ s n = 𝟙 (B.X n))
    (hfac1 : ∀ n, s n ≫ B.d n (n + 1) ≫ p (n + 1) = f.f n)
    (hfac2 : ∀ n, s n ≫ B.d n (n + 1) ≫ q (n + 1) = -(f.f n))
    (n : ℤ) :
    comparisonF r p q f n ≫ col A n
      = B.d n (n + 1) ≫ comparisonF r p q f (n + 1) := by
  have hicomm : i.f n ≫ B.d n (n + 1)
      = biprod.map (A.d n (n + 1)) (A.d n (n + 1)) ≫ i.f (n + 1) := by
    have := i.comm n (n + 1)
    rwa [double_d] at this
  unfold comparisonF col
  rw [biprod.hom_ext_iff, biprod.hom_ext_iff]
  simp only [biprod.lift_desc, Category.assoc, biprod.lift_fst, biprod.lift_snd,
    Preadditive.add_comp, Category.comp_id, Preadditive.comp_neg, comp_zero, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [← Category.id_comp (B.d n (n + 1) ≫ p (n + 1)), ← hsplit n,
      Preadditive.add_comp, Category.assoc, Category.assoc,
      show r.f n ≫ s n ≫ B.d n (n + 1) ≫ p (n + 1) = r.f n ≫ f.f n by rw [hfac1],
      ← Category.assoc (i.f n), hicomm, Category.assoc, i_comp_p hip,
      biprod.map_fst, biprod.lift_fst_assoc]
  · rw [← Category.id_comp (B.d n (n + 1) ≫ q (n + 1)), ← hsplit n,
      Preadditive.add_comp, Category.assoc, Category.assoc,
      show r.f n ≫ s n ≫ B.d n (n + 1) ≫ q (n + 1) = -(r.f n ≫ f.f n) by
        rw [hfac2, Preadditive.comp_neg],
      ← Category.assoc (i.f n), hicomm, Category.assoc, i_comp_q hip,
      biprod.map_snd, biprod.lift_snd_assoc]
  · rw [← Category.assoc (B.d n (n + 1)), ← r.comm n (n + 1), Category.assoc,
      ← f.comm n (n + 1), shift1_d]
    simp [Preadditive.comp_neg]

/-- The comparison map `φ : B ⟶ ⋄A`, with degree-`n` component `(p_n, q_n, r_n ≫ f_n)`. -/
noncomputable def comparisonMap
    (hip : ∀ n, i.f n ≫ biprod.lift (p n) (q n) = 𝟙 _)
    (hsplit : ∀ n,
      biprod.lift (p n) (q n) ≫ i.f n + r.f n ≫ s n = 𝟙 (B.X n))
    (hfac1 : ∀ n, s n ≫ B.d n (n + 1) ≫ p (n + 1) = f.f n)
    (hfac2 : ∀ n, s n ≫ B.d n (n + 1) ≫ q (n + 1) = -(f.f n)) :
    B ⟶ diamond A where
  f n := comparisonF r p q f n
  comm' j k hjk := by
    simp only [ComplexShape.up_Rel] at hjk; subst hjk
    rw [diamond_d]
    exact comparison_comm hip hsplit hfac1 hfac2 j

/-! ### The three compatibility properties of `φ` -/

/-- The comparison map restricts to `ι` on `A ⊕ A`: `i ≫ comparisonMap = ι A`. -/
theorem comparison_ι
    (hsr : ∀ n, s n ≫ r.f n = 𝟙 _)
    (hip : ∀ n, i.f n ≫ biprod.lift (p n) (q n) = 𝟙 _)
    (hsplit : ∀ n,
      biprod.lift (p n) (q n) ≫ i.f n + r.f n ≫ s n = 𝟙 (B.X n))
    (hfac1 : ∀ n, s n ≫ B.d n (n + 1) ≫ p (n + 1) = f.f n)
    (hfac2 : ∀ n, s n ≫ B.d n (n + 1) ≫ q (n + 1) = -(f.f n)) :
    i ≫ comparisonMap hip hsplit hfac1 hfac2 = ι A := by
  ext n
  rw [HomologicalComplex.comp_f]
  dsimp only [comparisonMap, comparisonF, ι]
  refine biprod.hom_ext _ _ ?_ (biprod.hom_ext _ _ ?_ ?_)
  · simp only [Category.assoc, biprod.lift_fst]
    rw [i_comp_p hip]
  · simp only [Category.assoc, biprod.lift_snd, biprod.lift_fst]
    rw [i_comp_q hip]
  · simp only [Category.assoc, biprod.lift_snd]
    rw [← Category.assoc, ir_zero hsr hip hsplit n, Limits.zero_comp]

/-- The comparison map covers `f` on the quotients: `comparisonMap ≫ ρ A = r ≫ f`. -/
theorem comparison_ρ
    (hip : ∀ n, i.f n ≫ biprod.lift (p n) (q n) = 𝟙 _)
    (hsplit : ∀ n,
      biprod.lift (p n) (q n) ≫ i.f n + r.f n ≫ s n = 𝟙 (B.X n))
    (hfac1 : ∀ n, s n ≫ B.d n (n + 1) ≫ p (n + 1) = f.f n)
    (hfac2 : ∀ n, s n ≫ B.d n (n + 1) ≫ q (n + 1) = -(f.f n)) :
    comparisonMap hip hsplit hfac1 hfac2 ≫ ρ A = r ≫ f := by
  ext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  dsimp only [comparisonMap, comparisonF, ρ]
  rw [← Category.assoc, biprod.lift_snd]
  exact biprod.lift_snd _ _

/-- The comparison map is compatible with the two termwise splittings:
`s n ≫ (comparisonMap).f n = f.f n ≫ σ A n`. -/
theorem comparison_σ
    (hsr : ∀ n, s n ≫ r.f n = 𝟙 _)
    (hip : ∀ n, i.f n ≫ biprod.lift (p n) (q n) = 𝟙 _)
    (hsplit : ∀ n,
      biprod.lift (p n) (q n) ≫ i.f n + r.f n ≫ s n = 𝟙 (B.X n))
    (hfac1 : ∀ n, s n ≫ B.d n (n + 1) ≫ p (n + 1) = f.f n)
    (hfac2 : ∀ n, s n ≫ B.d n (n + 1) ≫ q (n + 1) = -(f.f n))
    (n : ℤ) :
    s n ≫ (comparisonMap hip hsplit hfac1 hfac2).f n = f.f n ≫ σ A n := by
  dsimp only [comparisonMap, comparisonF, σ]
  refine biprod.hom_ext _ _ ?_ (biprod.hom_ext _ _ ?_ ?_)
  · simp only [Category.assoc, biprod.lift_fst]
    rw [sp_zero hsr hip hsplit n, Limits.comp_zero]
  · simp only [Category.assoc, biprod.lift_snd_assoc, biprod.lift_fst]
    rw [sq_zero hsr hip hsplit n, Limits.comp_zero]
  · simp only [Category.assoc, biprod.lift_snd]
    rw [← Category.assoc, hsr n, Category.id_comp, Category.comp_id]

/-! ### Uniqueness -/

/-- A morphism `ψ : B ⟶ ⋄A` with `i ≫ ψ = ι A` and `s n ≫ ψ.f n = f.f n ≫ σ A n` in every degree is
the comparison map. -/
theorem comparison_unique
    (hsr : ∀ n, s n ≫ r.f n = 𝟙 _)
    (hip : ∀ n, i.f n ≫ biprod.lift (p n) (q n) = 𝟙 _)
    (hsplit : ∀ n,
      biprod.lift (p n) (q n) ≫ i.f n + r.f n ≫ s n = 𝟙 (B.X n))
    (hfac1 : ∀ n, s n ≫ B.d n (n + 1) ≫ p (n + 1) = f.f n)
    (hfac2 : ∀ n, s n ≫ B.d n (n + 1) ≫ q (n + 1) = -(f.f n))
    (ψ : B ⟶ diamond A)
    (hψι : i ≫ ψ = ι A)
    (hψσ : ∀ n, s n ≫ ψ.f n = f.f n ≫ σ A n) :
    ψ = comparisonMap hip hsplit hfac1 hfac2 := by
  have key : ∀ (χ : B ⟶ diamond A), i ≫ χ = ι A →
      (∀ m, s m ≫ χ.f m = f.f m ≫ σ A m) → ∀ n,
      χ.f n = biprod.lift (p n) (q n) ≫ (ι A).f n + r.f n ≫ (f.f n ≫ σ A n) := by
    intro χ h1 h2 n
    calc χ.f n = 𝟙 _ ≫ χ.f n := by rw [Category.id_comp]
      _ = (biprod.lift (p n) (q n) ≫ i.f n + r.f n ≫ s n) ≫ χ.f n := by rw [hsplit n]
      _ = biprod.lift (p n) (q n) ≫ (i.f n ≫ χ.f n) + r.f n ≫ (s n ≫ χ.f n) := by
            rw [Preadditive.add_comp, Category.assoc, Category.assoc]
      _ = biprod.lift (p n) (q n) ≫ (ι A).f n + r.f n ≫ (f.f n ≫ σ A n) := by
            rw [← HomologicalComplex.comp_f, h1, h2]
  ext n
  rw [key ψ hψι hψσ n,
    key (comparisonMap hip hsplit hfac1 hfac2)
      (comparison_ι hsr hip hsplit hfac1 hfac2)
      (comparison_σ hsr hip hsplit hfac1 hfac2) n]

/-- **Stacks 01A3**.
Let `0 → A ⊕ A → B → Cpx → 0` be a short exact sequence of complexes, split in each degree by
`s n : Cpx_n ⟶ B_n`. If the associated connecting morphism `δ(s) : Cpx → A[-1] ⊕ A[-1]` factors
through `(1, -1) : A[-1] → A[-1] ⊕ A[-1]` as `δ(s) = (1, -1) ∘ f`, then there is a unique morphism
`φ : B ⟶ ⋄A` fitting into a commutative diagram of the two short exact sequences whose vertical
maps are compatible with the splittings `s n` and `σ A n`. -/
@[stacks 01A3]
theorem exists_unique_comparison
    (A B Cpx : CochainComplex C ℤ)
    (i : double A ⟶ B) (r : B ⟶ Cpx)
    (p q : ∀ n, B.X n ⟶ A.X n) (s : ∀ n, Cpx.X n ⟶ B.X n)
    (f : Cpx ⟶ shift1 A)
    -- degreewise biproduct splitting `B_n ≅ (A_n ⊕ A_n) ⊕ C_n`
    (hsr : ∀ n, s n ≫ r.f n = 𝟙 _)
    (hip : ∀ n, i.f n ≫ biprod.lift (p n) (q n) = 𝟙 _)
    (hsplit : ∀ n,
      biprod.lift (p n) (q n) ≫ i.f n + r.f n ≫ s n = 𝟙 (B.X n))
    -- the factorization `δ(s) = (1,-1) ∘ f`
    (hfac1 : ∀ n, s n ≫ B.d n (n + 1) ≫ p (n + 1) = f.f n)
    (hfac2 : ∀ n, s n ≫ B.d n (n + 1) ≫ q (n + 1) = -(f.f n)) :
    ∃! φ : B ⟶ diamond A,
      (i ≫ φ = ι A) ∧
      (φ ≫ ρ A = r ≫ f) ∧
      (∀ n, s n ≫ φ.f n = f.f n ≫ σ A n) := by
  refine ⟨comparisonMap hip hsplit hfac1 hfac2,
    ⟨comparison_ι hsr hip hsplit hfac1 hfac2,
     comparison_ρ hip hsplit hfac1 hfac2,
     comparison_σ hsr hip hsplit hfac1 hfac2⟩, ?_⟩
  rintro ψ ⟨hψι, _, hψσ⟩
  exact comparison_unique hsr hip hsplit hfac1 hfac2 ψ hψι hψσ

end CochainComplex.diamond

end

end
