module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharDirectSum.Basic

/-!
# The stalk of `𝒢^{⊞ n}` is an `n`-tuple of stalks, in the shape `isIso_of_isIso_stalk` consumes

Let `X` be a scheme, `𝒢` a sheaf of `𝒪_X`-modules and `𝒢^{⊞ n}` its `n`-fold biproduct
`AlgebraicGeometry.Scheme.Modules.biprodPow`. This file equips that power with its `n`
inclusions and `n` projections, proves the two biproduct identities they satisfy, and deduces
that **every additive functor from `X.Modules` to abelian groups turns `𝒢^{⊞ n}` into the
`n`-tuples of its value on `𝒢`**:

  `c ↦ ∑ j, F(incl j) (c j)`  is a bijection  `(Fin n → F(𝒢)) → F(𝒢^{⊞ n})`.

Applied to `Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab x` — the functor
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk` tests — this gives the
criterion the construction of the isomorphism `ℰ ⊗ 𝒢 ≅ 𝒢^{⊞ n}` of clause (5) of
[Stacks, Tag 0AYT] is proved by: a morphism assembled out of `n` morphisms `𝒢 ⟶ ℳ` is
invertible as soon as, at every point, `(g_j) ↦ ∑ⱼ (ψ_j)_x (g_j)` is bijective on stalks.

It is the second of the three inputs to that clause. The first is
`AlgebraicGeometry.exists_germ_basis_of_isFiniteLocallyFreeOfRank`
(`StacksFrontier/AlgebraicGeometry/FreeStalkBasis/LocalRank.lean`), the local basis of germs of
a finite locally free module of rank `n`; the third is `n` applications of
`AlgebraicGeometry.exists_hom_app_eq_tmulSection`, which needs nothing new.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.biprodPowIncl`, `…biprodPowProj`: the `j`-th inclusion
  `𝒢 ⟶ 𝒢^{⊞ n}` and projection `𝒢^{⊞ n} ⟶ 𝒢`, by recursion on `n` along the definition of
  `biprodPow` itself.
* `AlgebraicGeometry.Scheme.Modules.biprodPowDesc`: the morphism `𝒢^{⊞ n} ⟶ ℳ` assembled from
  `n` morphisms `𝒢 ⟶ ℳ`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.biprodPowIncl_proj` and
  `AlgebraicGeometry.Scheme.Modules.biprodPow_total`: the two biproduct identities,
  `incl j ≫ proj j' = δ_{j j'}` and `∑ⱼ proj j ≫ incl j = 𝟙`.
* `AlgebraicGeometry.Scheme.Modules.toPresheaf_additive`: the forgetful functor to presheaves of
  abelian groups is additive. Mathlib proves it preserves all limits and reflects isomorphisms
  but does not record additivity.
* `AlgebraicGeometry.bijective_sum_map_biprodPowIncl`: **the brick** — for an additive
  `F : X.Modules ⥤ AddCommGrpCat`, `c ↦ ∑ⱼ F(incl j) (c j)` is bijective, with the `n`
  projections as its inverse.
* `AlgebraicGeometry.isIso_biprodPowDesc_of_bijective_sum_stalkMap`: **the criterion**, in the
  spelling `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk` consumes.
* `AlgebraicGeometry.isIso_biprodPowDesc_biprodPowIncl`: the criterion applied to the
  inclusions themselves, so its hypothesis is satisfiable and the statement is not vacuous.

## Implementation notes

**Why the additivity of `Scheme.Modules.toPresheaf` is not `inferInstance`.** The composite
`Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab x` *is* additive by instance
search once the first factor's additivity is in scope — `CategoryTheory.Functor.additive_comp`
and Mathlib's instance for the stalk functor
(`Mathlib/Topology/Sheaves/Abelian.lean`) do the rest. The first factor is not: it is
`SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _`, both of whose factors carry an
`Additive` instance in Mathlib, but `AlgebraicGeometry.Scheme.Modules` is a `def` with its *own*
`Category` instance, so neither the named composite nor its written-out form is found —
`inferInstanceAs` on the written-out form fails too. What works is
`CategoryTheory.Functor.additive_of_preserves_binary_products`, from Mathlib's
`PreservesLimits (toPresheaf X)`.

**Why `incl`, `proj` and `desc` are defined by recursion and their recursion equations are not
stated.** `Scheme.Modules.biprodPow (n + 1)` is *definitionally* `𝒢 ⊞ 𝒢^{⊞ n}` but not
syntactically so, and an equation between the two spellings makes every later `rw` fail with
*"the target expression is not type-correct under the `implicit` transparency level"*. So the
proofs below never rewrite across that gap: each inductive step either opens with a `show` that
restates the whole goal at the `⊞` spelling, or — for
`AlgebraicGeometry.Scheme.Modules.biprodPow_total`, where the ambient `AddCommMonoid` instance
of a `Finset.sum` also has to move — defers to a helper stated purely in terms of `A ⊞ B` and
applies it. Applications cross the gap; rewrites do not.

**A finite sum of morphisms of abelian groups applied to an element** is
`Stacks.Cohomology.Cech.sum_hom_apply`
(`StacksFrontier/AlgebraicGeometry/Cohomology/Cech/StandardCoverVanishing.lean`) and, in a second
spelling, `Stacks.Cohomology.Basis.hom_sum_apply`.
Neither is imported — both live inside Čech-cohomology files whose import closure is far larger
than the two-line term they would replace, which is therefore inlined at its one use site rather
than given a third name.

**No tag attribute is attached.** This is an input to clause (5) of [Stacks, Tag 0AYT], not the
clause: nothing here mentions a tensor product, a coherent module or a zero-dimensional support,
and the statements hold for an arbitrary scheme and an arbitrary sheaf of modules. The covering
set of that clause is the isomorphism `ℰ ⊗ 𝒢 ≅ 𝒢^{⊞ n}` together with
`AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_mul_of_iso_biprodPow`, and neither
is here.

## References

* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

namespace Scheme.Modules

/-! ### The inclusions and projections of a power -/

/-- **The `j`-th inclusion `𝒢 ⟶ 𝒢^{⊞ n}`**, by recursion on `n`: at `j = 0` the inclusion of
the first summand of `𝒢 ⊞ 𝒢^{⊞ n}`, and at `j = i + 1` the `i`-th inclusion into `𝒢^{⊞ n}`
followed by the inclusion of the second summand. -/
noncomputable def biprodPowIncl (G : X.Modules) : (n : ℕ) → (j : Fin n) → (G ⟶ G.biprodPow n)
  | 0, j => j.elim0
  | (n + 1), j => Fin.cases biprod.inl (fun i => biprodPowIncl G n i ≫ biprod.inr) j

/-- **The `j`-th projection `𝒢^{⊞ n} ⟶ 𝒢`**, by the same recursion. -/
noncomputable def biprodPowProj (G : X.Modules) : (n : ℕ) → (j : Fin n) → (G.biprodPow n ⟶ G)
  | 0, j => j.elim0
  | (n + 1), j => Fin.cases biprod.fst (fun i => biprod.snd ≫ biprodPowProj G n i) j

/-- **The morphism `𝒢^{⊞ n} ⟶ ℳ` assembled from `n` morphisms `𝒢 ⟶ ℳ`.** At `n = 0` the
target is a zero object, so the zero morphism is the only choice. -/
noncomputable def biprodPowDesc (G M : X.Modules) :
    (n : ℕ) → (ψ : Fin n → (G ⟶ M)) → (G.biprodPow n ⟶ M)
  | 0, _ => 0
  | (n + 1), ψ => biprod.desc (ψ 0) (biprodPowDesc G M n fun i => ψ i.succ)

/-- **`biprodPowDesc` restricts along the `j`-th inclusion to the `j`-th given morphism**, which
determines it: the inclusions are jointly epimorphic. -/
theorem biprodPowIncl_desc (G M : X.Modules) (n : ℕ) (ψ : Fin n → (G ⟶ M)) (j : Fin n) :
    biprodPowIncl G n j ≫ biprodPowDesc G M n ψ = ψ j := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    induction j using Fin.cases with
    | zero =>
      show (biprod.inl : G ⟶ G ⊞ G.biprodPow n) ≫
        biprod.desc (ψ 0) (biprodPowDesc G M n fun i => ψ i.succ) = ψ 0
      exact biprod.inl_desc _ _
    | succ i =>
      show (biprodPowIncl G n i ≫ (biprod.inr : G.biprodPow n ⟶ G ⊞ G.biprodPow n)) ≫
        biprod.desc (ψ 0) (biprodPowDesc G M n fun i => ψ i.succ) = ψ i.succ
      rw [Category.assoc, biprod.inr_desc]
      exact ih _ i

/-- **The orthogonality identity** `incl j ≫ proj j' = δ_{j j'}`. -/
theorem biprodPowIncl_proj (G : X.Modules) (n : ℕ) (j j' : Fin n) :
    biprodPowIncl G n j ≫ biprodPowProj G n j' = if j = j' then 𝟙 G else 0 := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    induction j using Fin.cases with
    | zero =>
      induction j' using Fin.cases with
      | zero =>
        show (biprod.inl : G ⟶ G ⊞ G.biprodPow n) ≫ biprod.fst = _
        simp
      | succ i' =>
        show (biprod.inl : G ⟶ G ⊞ G.biprodPow n) ≫
          (biprod.snd ≫ biprodPowProj G n i') = _
        rw [← Category.assoc, biprod.inl_snd, Limits.zero_comp,
          ite_eq_right (Fin.succ_ne_zero i').symm]
    | succ i =>
      induction j' using Fin.cases with
      | zero =>
        show (biprodPowIncl G n i ≫ (biprod.inr : G.biprodPow n ⟶ G ⊞ G.biprodPow n)) ≫
          biprod.fst = _
        rw [Category.assoc, biprod.inr_fst, Limits.comp_zero,
          ite_eq_right (Fin.succ_ne_zero i)]
      | succ i' =>
        show (biprodPowIncl G n i ≫ (biprod.inr : G.biprodPow n ⟶ G ⊞ G.biprodPow n)) ≫
          (biprod.snd ≫ biprodPowProj G n i') = _
        rw [Category.assoc, ← Category.assoc (biprod.inr : G.biprodPow n ⟶ G ⊞ G.biprodPow n),
          biprod.inr_snd, Category.id_comp, ih i i']
        simp [Fin.succ_inj]

/-- The inductive step of `AlgebraicGeometry.Scheme.Modules.biprodPow_total`, stated purely in
terms of `A ⊞ B`: the sum identity for a family of projections and inclusions of `B` carries
over to `A ⊞ B`. Stating it this way keeps the `Finset.sum` of the statement away from the two
spellings of `𝒢^{⊞ (n + 1)}`, between which a rewrite is not type-correct. -/
private theorem biprodPow_total_succ_aux (A B : X.Modules) (n : ℕ)
    (p : Fin n → (B ⟶ A)) (q : Fin n → (A ⟶ B)) (h : (∑ i, p i ≫ q i) = 𝟙 B) :
    (∑ j : Fin (n + 1),
        (Fin.cases (biprod.fst : A ⊞ B ⟶ A) (fun i => biprod.snd ≫ p i) j) ≫
          (Fin.cases (biprod.inl : A ⟶ A ⊞ B) (fun i => q i ≫ biprod.inr) j))
      = 𝟙 (A ⊞ B) := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  have e : (∑ i : Fin n, (biprod.snd ≫ p i) ≫ (q i ≫ (biprod.inr : B ⟶ A ⊞ B)))
      = (biprod.snd : A ⊞ B ⟶ B) ≫ (∑ i : Fin n, p i ≫ q i) ≫ (biprod.inr : B ⟶ A ⊞ B) := by
    rw [Preadditive.sum_comp, Preadditive.comp_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [Category.assoc]
  rw [e, h, Category.id_comp]
  exact biprod.total

/-- **The total identity** `∑ⱼ proj j ≫ incl j = 𝟙 (𝒢^{⊞ n})`, which together with
`AlgebraicGeometry.Scheme.Modules.biprodPowIncl_proj` says that the inclusions and projections
exhibit `𝒢^{⊞ n}` as the biproduct of `n` copies of `𝒢`. -/
theorem biprodPow_total (G : X.Modules) (n : ℕ) :
    (∑ j : Fin n, biprodPowProj G n j ≫ biprodPowIncl G n j) = 𝟙 (G.biprodPow n) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact (isZero_zero X.Modules).eq_of_src _ _
  | succ n ih =>
    exact biprodPow_total_succ_aux G (G.biprodPow n) n (biprodPowProj G n) (biprodPowIncl G n) ih

/-! ### Additivity of the forgetful functor to presheaves of abelian groups -/

/-- **`Scheme.Modules.toPresheaf` is additive.** Mathlib records that it preserves all limits,
is faithful and reflects isomorphisms, but not that it is additive; additivity follows from
preservation of binary products in a preadditive category. -/
theorem toPresheaf_additive (X : Scheme.{u}) : (Scheme.Modules.toPresheaf X).Additive := by
  have h1 : PreservesLimitsOfShape (Discrete WalkingPair) (Scheme.Modules.toPresheaf X) :=
    inferInstance
  exact Functor.additive_of_preserves_binary_products _

/-- **The stalk of the underlying presheaf of abelian groups is an additive functor on
`X.Modules`**, this being the functor
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk` tests. -/
theorem toPresheaf_stalkFunctor_additive (X : Scheme.{u}) (x : X) :
    (Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).Additive := by
  have := toPresheaf_additive X
  infer_instance

end Scheme.Modules

/-! ### The brick -/

/-- A functor to abelian groups applied to a composite, evaluated at an element. -/
private theorem map_map_apply (F : X.Modules ⥤ AddCommGrpCat.{u}) {A B C : X.Modules}
    (f : A ⟶ B) (g : B ⟶ C) (a : ToType (F.obj A)) :
    F.map g (F.map f a) = F.map (f ≫ g) a := by
  rw [F.map_comp]
  rfl

/-- **An additive functor to abelian groups turns `𝒢^{⊞ n}` into the `n`-tuples of its value on
`𝒢`**: the map `c ↦ ∑ⱼ F(incl j) (c j)` is a bijection `(Fin n → F(𝒢)) → F(𝒢^{⊞ n})`, with
`z ↦ (F(proj j) z)ⱼ` as its two-sided inverse.

Both halves are the two biproduct identities of
`AlgebraicGeometry.Scheme.Modules.biprodPowIncl_proj` and
`AlgebraicGeometry.Scheme.Modules.biprodPow_total`, pushed through `F`; nothing else about `F`
is used, and in particular no biproduct in the target category is formed. -/
theorem bijective_sum_map_biprodPowIncl (F : X.Modules ⥤ AddCommGrpCat.{u}) [F.Additive]
    (G : X.Modules) (n : ℕ) :
    Function.Bijective (fun c : Fin n → ToType (F.obj G) =>
      ∑ j, F.map (Scheme.Modules.biprodPowIncl G n j) (c j)) := by
  classical
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun z j => F.map (Scheme.Modules.biprodPowProj G n j) z, fun c => ?_, fun z => ?_⟩
  · funext j
    show F.map (Scheme.Modules.biprodPowProj G n j)
      (∑ j', F.map (Scheme.Modules.biprodPowIncl G n j') (c j')) = c j
    rw [map_sum]
    have e : ∀ j' : Fin n, F.map (Scheme.Modules.biprodPowProj G n j)
          (F.map (Scheme.Modules.biprodPowIncl G n j') (c j'))
        = if j' = j then c j' else 0 := by
      intro j'
      rw [map_map_apply, Scheme.Modules.biprodPowIncl_proj]
      split
      · rw [F.map_id]
        rfl
      · rw [F.map_zero]
        rfl
    rw [Finset.sum_congr rfl fun j' _ => e j']
    simp
  · show (∑ j, F.map (Scheme.Modules.biprodPowIncl G n j)
      (F.map (Scheme.Modules.biprodPowProj G n j) z)) = z
    have hsum : (∑ j : Fin n, F.map (Scheme.Modules.biprodPowProj G n j ≫
            Scheme.Modules.biprodPowIncl G n j)) z
        = ∑ j : Fin n, F.map (Scheme.Modules.biprodPowProj G n j ≫
            Scheme.Modules.biprodPowIncl G n j) z :=
      map_sum (AddMonoidHom.mk' (fun ψ : F.obj (G.biprodPow n) ⟶ F.obj (G.biprodPow n) => ψ z)
        fun a b => AddCommGrpCat.hom_add_apply a b z) _ _
    simp only [map_map_apply]
    rw [← hsum, ← F.map_sum, Scheme.Modules.biprodPow_total, F.map_id]
    rfl

/-! ### The criterion -/

/-- **A morphism assembled out of `n` morphisms `𝒢 ⟶ ℳ` is invertible as soon as, at every
point, `(g_j) ↦ ∑ⱼ (ψ_j)_x (g_j)` is bijective on stalks.** This is
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk` with the stalk of `𝒢^{⊞ n}`
resolved by `AlgebraicGeometry.bijective_sum_map_biprodPowIncl`, and it is the shape in which
the isomorphism `ℰ ⊗ 𝒢 ≅ 𝒢^{⊞ n}` of clause (5) of [Stacks, Tag 0AYT] is to be proved: the
`n` morphisms are the `n` applications of
`AlgebraicGeometry.exists_hom_app_eq_tmulSection`, one per member of the local germ basis of
`ℰ` supplied by
`AlgebraicGeometry.exists_germ_basis_of_isFiniteLocallyFreeOfRank`. -/
theorem isIso_biprodPowDesc_of_bijective_sum_stalkMap (G M : X.Modules) (n : ℕ)
    (ψ : Fin n → (G ⟶ M))
    (h : ∀ x : X, Function.Bijective
      (fun c : Fin n → ToType ((Scheme.Modules.toPresheaf X ⋙
            TopCat.Presheaf.stalkFunctor Ab.{u} x).obj G) =>
        ∑ j, (Scheme.Modules.toPresheaf X ⋙
          TopCat.Presheaf.stalkFunctor Ab.{u} x).map (ψ j) (c j))) :
    IsIso (Scheme.Modules.biprodPowDesc G M n ψ) := by
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk _ fun x => ?_
  have hFadd := Scheme.Modules.toPresheaf_stalkFunctor_additive X x
  set F := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x
  have hα := bijective_sum_map_biprodPowIncl F G n
  let e := Equiv.ofBijective _ hα
  have hcomp : ∀ c : Fin n → ToType (F.obj G),
      F.map (Scheme.Modules.biprodPowDesc G M n ψ)
          (∑ j, F.map (Scheme.Modules.biprodPowIncl G n j) (c j))
        = ∑ j, F.map (ψ j) (c j) := by
    intro c
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_map_apply, Scheme.Modules.biprodPowIncl_desc]
  have hbij : Function.Bijective
      (fun z => F.map (Scheme.Modules.biprodPowDesc G M n ψ) z) := by
    have key : (fun z => F.map (Scheme.Modules.biprodPowDesc G M n ψ) z)
        = (fun c : Fin n → ToType (F.obj G) => ∑ j, F.map (ψ j) (c j)) ∘ e.symm := by
      funext z
      calc F.map (Scheme.Modules.biprodPowDesc G M n ψ) z
          = F.map (Scheme.Modules.biprodPowDesc G M n ψ) (e (e.symm z)) := by
            rw [e.apply_symm_apply]
        _ = ∑ j, F.map (ψ j) (e.symm z j) := hcomp _
    rw [key]
    exact (h x).comp e.symm.bijective
  exact (ConcreteCategory.isIso_iff_bijective
    (F.map (Scheme.Modules.biprodPowDesc G M n ψ))).mpr hbij

/-- **The criterion applied to the inclusions themselves**, so that its hypothesis is
satisfiable and its conclusion is not vacuous: the morphism `𝒢^{⊞ n} ⟶ 𝒢^{⊞ n}` assembled from
the `n` inclusions is invertible, its stalkwise hypothesis being exactly
`AlgebraicGeometry.bijective_sum_map_biprodPowIncl`. -/
theorem isIso_biprodPowDesc_biprodPowIncl (G : X.Modules) (n : ℕ) :
    IsIso (Scheme.Modules.biprodPowDesc G (G.biprodPow n) n
      (Scheme.Modules.biprodPowIncl G n)) := by
  refine isIso_biprodPowDesc_of_bijective_sum_stalkMap G (G.biprodPow n) n
    (Scheme.Modules.biprodPowIncl G n) fun x => ?_
  have hFadd := Scheme.Modules.toPresheaf_stalkFunctor_additive X x
  exact bijective_sum_map_biprodPowIncl
    (Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x) G n

end AlgebraicGeometry

end
