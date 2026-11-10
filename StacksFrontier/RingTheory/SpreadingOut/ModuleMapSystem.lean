module

import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.Algebra.Category.Grp.FilteredColimits

public import StacksFrontier.RingTheory.SpreadingOut.ColimitSystem

/-!
# Spreading out a map of finitely presented modules

Let `S` be the colimit of a directed system of rings `B_λ`. A finitely presented `S`-module `M` is
the colimit of a cartesian system of finite `B_λ`-modules `M_λ`, that is `M_μ = M_λ ⊗_{B_λ} B_μ`.
This file shows that a map `u : M → N` of finitely presented `S`-modules is the colimit of
`B_λ`-linear maps `u_λ : M_λ → N_λ` between two such systems.

## Main definitions

* `SpreadingOut.matMap`: the `A`-linear map `A^{⊕n} → A^{⊕n'}` with a given matrix.
* `SpreadingOut.mapQuot`: the map between presented modules induced by a matrix which carries the
  relations of the source into those of the target.
* `SpreadingOut.relQuotNatTrans`: the map of module systems given at each stage by `mapQuot`.

## Main results

* `SpreadingOut.exists_module_map_system_of_isColimit`: a map `u : M → N` of finitely presented
  `S`-modules is the colimit of `B_λ`-linear maps `u_λ : M_λ → N_λ` of finite `B_λ`-modules, with
  both module systems cartesian.
* `SpreadingOut.injective_of_forall_exists_ge_injective`: the colimit of a map of directed systems
  of modules which is injective at cofinally many stages is injective.
* `RingHom.EssentiallyOfFinitePresentation.exists_isColimit_essFiniteType_module_map`: for a local
  homomorphism of local rings `R → S` essentially of finite presentation, a map of finitely
  presented `S`-modules is the colimit of maps of finite modules over a directed system of local
  homomorphisms `A_λ → B_λ` of local rings essentially of finite type, with colimit `R → S`.

## Implementation notes

The two module systems are the functors `Stacks.SpreadingOut.LocalModuleSystem.relQuot` of
presentations of `M` and `N`, and the map between them is `SpreadingOut.relQuotNatTrans`. The
index of the systems is the tail `{x // l ≤ x}` of the given index, which is final in it.
-/

@[expose] public section

universe u

open CategoryTheory Limits Stacks.SpreadingOut.LocalModuleSystem

namespace SpreadingOut

/-- The `A`-linear map `A^{⊕n} → A^{⊕n'}` with matrix `U`, sending `x` to `∑ₘ xₘ • Uₘ`. -/
public def matMap {A : Type*} [CommRing A] {n n' : ℕ} (U : Fin n → Fin n' → A) :
    (Fin n → A) →ₗ[A] (Fin n' → A) :=
  Fintype.linearCombination A U

/-- The coordinates of `matMap U x`. -/
public lemma matMap_apply {A : Type*} [CommRing A] {n n' : ℕ} (U : Fin n → Fin n' → A)
    (x : Fin n → A) (m' : Fin n') : matMap U x m' = ∑ m, x m * U m m' := by
  simp [matMap, Fintype.linearCombination_apply, Finset.sum_apply]

/-- The matrix map commutes with applying a ring homomorphism coordinatewise. -/
public lemma matMap_map {A A' : Type*} [CommRing A] [CommRing A'] (f : A →+* A')
    {n n' : ℕ} {U : Fin n → Fin n' → A} {U' : Fin n → Fin n' → A'}
    (hU : ∀ m m', f (U m m') = U' m m') (x : Fin n → A) (m' : Fin n') :
    f (matMap U x m') = matMap U' (fun m => f (x m)) m' := by
  rw [matMap_apply, matMap_apply, map_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [map_mul, hU]

/-- The standard basis vector is sent to the corresponding row of the matrix. -/
public lemma matMap_single {A : Type*} [CommRing A] {n n' : ℕ} (U : Fin n → Fin n' → A)
    (m : Fin n) : matMap U (Pi.single m 1) = U m := by
  funext m'
  simp [matMap_apply, Pi.single_apply]

/-- Evaluating a linear combination of vectors coordinatewise. -/
public lemma sum_smul_apply {A : Type*} [CommRing A] {n' : ℕ} {κ : Type*} [Fintype κ]
    (c : κ → A) (y : κ → Fin n' → A) (m' : Fin n') :
    (∑ k, c k • y k) m' = ∑ k, c k * y k m' :=
  Finset.sum_apply ..

section Systems

variable {S : Type u} [CommRing S] {J : Type u} [Preorder J] {B : J ⥤ CommRingCat.{u}}
  {n n' : ℕ} {ι ι' : Type u}
  {rel : ∀ i : J, ι → Fin n → ↑(B.obj i)}
  {hrel : ∀ {i j : J} (h : i ⟶ j) (k : ι) (m : Fin n), (B.map h).hom (rel i k m) = rel j k m}
  {rel' : ∀ i : J, ι' → Fin n' → ↑(B.obj i)}
  {hrel' : ∀ {i j : J} (h : i ⟶ j) (k : ι') (m : Fin n'),
    (B.map h).hom (rel' i k m) = rel' j k m}
  (U : ∀ i : J, Fin n → Fin n' → ↑(B.obj i))
  (hU : ∀ {i j : J} (h : i ⟶ j) (m : Fin n) (m' : Fin n'), (B.map h).hom (U i m m') = U j m m')
  (hUrel : ∀ (i : J) (k : ι), matMap (U i) (rel i k) ∈ relSpan rel' i)

/-- The `B_i`-linear map between the presented modules at stage `i` induced by the matrix `U i`,
which carries the relations of the source into the span of the relations of the target. -/
public def mapQuot (i : J) :
    ((Fin n → ↑(B.obj i)) ⧸ relSpan rel i) →ₗ[↑(B.obj i)]
      ((Fin n' → ↑(B.obj i)) ⧸ relSpan rel' i) :=
  Submodule.liftQ _ ((relSpan rel' i).mkQ ∘ₗ matMap (U i)) (by
    rw [relSpan, Submodule.span_le]
    rintro x ⟨k, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).2 (hUrel i k))

/-- `mapQuot U` sends the class of `y` to the class of `matMap (U i) y`. -/
public lemma mapQuot_mk (i : J) (y : Fin n → ↑(B.obj i)) :
    mapQuot (rel := rel) (rel' := rel') U hUrel i (Submodule.Quotient.mk y)
      = Submodule.Quotient.mk (matMap (U i) y) :=
  rfl

/-- The map of module systems `relQuot rel hrel ⟶ relQuot rel' hrel'` given at each stage `i` by
`mapQuot U i`. -/
public def relQuotNatTrans : relQuot rel hrel ⟶ relQuot rel' hrel' where
  app i := AddCommGrpCat.ofHom (mapQuot (rel := rel) (rel' := rel') U hUrel i).toAddMonoidHom
  naturality {i j} h := by
    ext x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (relSpan rel i) x
    change (Submodule.Quotient.mk (matMap (U j) (coordMap B n h y)) :
        (Fin n' → ↑(B.obj j)) ⧸ relSpan rel' j)
      = Submodule.Quotient.mk (coordMap B n' h (matMap (U i) y))
    exact congrArg _ (funext fun m' => (matMap_map (B.map h).hom (hU h) y m')).symm

/-- `relQuotNatTrans U` sends the class of `y` at stage `i` to the class of `matMap (U i) y`. -/
public lemma relQuotNatTrans_app_mk (i : J) (y : Fin n → ↑(B.obj i)) :
    (relQuotNatTrans (hrel := hrel) (hrel' := hrel') U hU hUrel).app i
        (Submodule.Quotient.mk y)
      = Submodule.Quotient.mk (matMap (U i) y) :=
  rfl

/-- At each stage `i`, `relQuotNatTrans U` is the `B_i`-linear map `mapQuot U i`. -/
public lemma relQuotNatTrans_app_apply (i : J) (m : (Fin n → ↑(B.obj i)) ⧸ relSpan rel i) :
    (relQuotNatTrans (hrel := hrel) (hrel' := hrel') U hU hUrel).app i m
      = mapQuot (rel := rel) (rel' := rel') U hUrel i m :=
  rfl

end Systems

section Legs

variable {S M N : Type u} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N]
  [Module S N] {n n' : ℕ}

/-- If a linear map `u` between cokernels of free presentations sends the class of each standard
basis vector `Pi.single m 1` to the class of `w m`, then it sends the class of `z` to the class of
`matMap w z`. -/
public lemma apply_mk_eq_of_single {ι ι' : Type u} {v : ι → Fin n → S} {v' : ι' → Fin n' → S}
    (e : M ≃ₗ[S] ((Fin n → S) ⧸ Submodule.span S (Set.range v)))
    (e' : N ≃ₗ[S] ((Fin n' → S) ⧸ Submodule.span S (Set.range v')))
    (u : M →ₗ[S] N) (w : Fin n → Fin n' → S)
    (hwu : ∀ m : Fin n, u (e.symm (Submodule.Quotient.mk (Pi.single m 1)))
      = e'.symm (Submodule.Quotient.mk (w m)))
    (z : Fin n → S) :
    u (e.symm (Submodule.Quotient.mk z)) = e'.symm (Submodule.Quotient.mk (matMap w z)) := by
  have h : u ∘ₗ e.symm.toLinearMap ∘ₗ (Submodule.span S (Set.range v)).mkQ
      = e'.symm.toLinearMap ∘ₗ (Submodule.span S (Set.range v')).mkQ ∘ₗ matMap w :=
    (Pi.basisFun S (Fin n)).ext fun m => by simpa [matMap_single] using hwu m
  exact LinearMap.congr_fun h z

end Legs

/-- A ring homomorphism carries a coordinate of a linear combination to the same coordinate of the
linear combination of the images. -/
private theorem map_sum_smul_apply {A A' : Type*} [CommRing A] [CommRing A'] (f : A →+* A')
    {n' : ℕ} {κ : Type*} [Fintype κ] {c : κ → A} {c' : κ → A'} {y : κ → Fin n' → A}
    {y' : κ → Fin n' → A'} (hc : ∀ k, f (c k) = c' k) (hy : ∀ k m', f (y k m') = y' k m')
    (m' : Fin n') : f ((∑ k, c k • y k) m') = (∑ k, c' k • y' k) m' := by
  rw [sum_smul_apply, sum_smul_apply, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_mul, hc, hy]

/-- Let `f : A →+* A'` carry `U`, `x`, `c` and `y` entrywise to `U'`, `x'`, `c'` and `y'`. If
`matMap U x` and `∑ k, c k • y k` have the same image under `f`, then
`matMap U' x' = ∑ k, c' k • y' k`. -/
public lemma matMap_eq_sum_of_map {A A' : Type*} [CommRing A] [CommRing A'] (f : A →+* A')
    {n n' : ℕ} {κ' : Type*} [Fintype κ']
    {U : Fin n → Fin n' → A} {U' : Fin n → Fin n' → A'}
    {x : Fin n → A} {x' : Fin n → A'}
    {c : κ' → A} {c' : κ' → A'} {y : κ' → Fin n' → A} {y' : κ' → Fin n' → A'}
    (hU : ∀ m m', f (U m m') = U' m m') (hx : ∀ m, f (x m) = x' m)
    (hc : ∀ k, f (c k) = c' k) (hy : ∀ k m', f (y k m') = y' k m')
    (h : ∀ m', f (matMap U x m') = f ((∑ k, c k • y k) m')) :
    matMap U' x' = ∑ k, c' k • y' k := by
  funext m'
  have hL : f (matMap U x m') = matMap U' x' m' := by
    rw [matMap_map f hU x m', show (fun m => f (x m)) = x' from funext hx]
  rw [← hL, h m', map_sum_smul_apply f hc hy]

section Colimit

variable {S M N : Type u} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N]
  [Module S N] {J : Type u} [Preorder J] {B : J ⥤ CommRingCat.{u}}
  {σ : B ⟶ (Functor.const J).obj (CommRingCat.of S)}
  {n n' : ℕ} {ι ι' : Type u} {v : ι → Fin n → S} {v' : ι' → Fin n' → S}
  {rel : ∀ i : J, ι → Fin n → ↑(B.obj i)}
  {hrel : ∀ {i j : J} (h : i ⟶ j) (k : ι) (m : Fin n), (B.map h).hom (rel i k m) = rel j k m}
  {hv : ∀ (i : J) (k : ι) (m : Fin n), legHom σ i (rel i k m) = v k m}
  {rel' : ∀ i : J, ι' → Fin n' → ↑(B.obj i)}
  {hrel' : ∀ {i j : J} (h : i ⟶ j) (k : ι') (m : Fin n'),
    (B.map h).hom (rel' i k m) = rel' j k m}
  {hv' : ∀ (i : J) (k : ι') (m : Fin n'), legHom σ i (rel' i k m) = v' k m}
  {e : M ≃ₗ[S] ((Fin n → S) ⧸ Submodule.span S (Set.range v))}
  {e' : N ≃ₗ[S] ((Fin n' → S) ⧸ Submodule.span S (Set.range v'))}

/-- The legs of the two module cocones intertwine the stagewise maps `relQuotNatTrans U` with
`u`. -/
public lemma modCocone_relQuotNatTrans (u : M →ₗ[S] N) (w : Fin n → Fin n' → S)
    (hwu : ∀ m : Fin n, u (e.symm (Submodule.Quotient.mk (Pi.single m 1)))
      = e'.symm (Submodule.Quotient.mk (w m)))
    (U : ∀ i : J, Fin n → Fin n' → ↑(B.obj i))
    (hU : ∀ {i j : J} (h : i ⟶ j) (m : Fin n) (m' : Fin n'),
      (B.map h).hom (U i m m') = U j m m')
    (hUrel : ∀ (i : J) (k : ι), matMap (U i) (rel i k) ∈ relSpan rel' i)
    (hw : ∀ (i : J) (m : Fin n) (m' : Fin n'), legHom σ i (U i m m') = w m m')
    (i : J) (x : (Fin n → ↑(B.obj i)) ⧸ relSpan rel i) :
    u ((modCocone σ rel hrel hv e).app i x)
      = (modCocone σ rel' hrel' hv' e').app i
        ((relQuotNatTrans (hrel := hrel) (hrel' := hrel') U hU hUrel).app i x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (relSpan rel i) x
  rw [modCocone_app_mk σ rel hrel hv e i y, relQuotNatTrans_app_mk U hU hUrel i y,
    modCocone_app_mk σ rel' hrel' hv' e' i (matMap (U i) y),
    apply_mk_eq_of_single e e' u w hwu (coordLeg n σ i y)]
  exact congrArg (fun s => e'.symm (Submodule.Quotient.mk s))
    (funext fun m' => (matMap_map (legHom σ i) (hw i) y m')).symm

end Colimit

section Existence

variable {S M N : Type u} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N]
  [Module S N]

/-- Let `S` be the colimit of a directed system of rings `B_λ`, let `M` and `N` be the cokernels of
matrices `v` and `v'` over `S`, and let `u : M → N`. Then for all `λ` above a single stage `l`
there are finite `B_λ`-modules `M_λ`, `N_λ` and `B_λ`-linear maps `u_λ : M_λ → N_λ` whose
colimits are `M`, `N` and `u`, with both module systems cartesian. -/
public theorem exists_module_map_system_aux
    {Λ₀ : Type u} [Preorder Λ₀] [Nonempty Λ₀] [IsDirected Λ₀ (· ≤ ·)]
    (B₀ : Λ₀ ⥤ CommRingCat.{u}) (σ₀ : B₀ ⟶ (Functor.const Λ₀).obj (CommRingCat.of S))
    (hσ₀ : IsColimit (Cocone.mk (CommRingCat.of S) σ₀)) (u : M →ₗ[S] N)
    {n n' : ℕ} {ι ι' : Type u} [Finite ι] [Finite ι'] {v : ι → Fin n → S} {v' : ι' → Fin n' → S}
    (e : M ≃ₗ[S] ((Fin n → S) ⧸ Submodule.span S (Set.range v)))
    (e' : N ≃ₗ[S] ((Fin n' → S) ⧸ Submodule.span S (Set.range v'))) :
    ∃ (l : Λ₀) (MF NF : {x : Λ₀ // l ≤ x} ⥤ AddCommGrpCat.{u})
      (_ : ∀ i, Module ((tailFunctor l ⋙ B₀).obj i) (MF.obj i))
      (_ : ∀ i, Module ((tailFunctor l ⋙ B₀).obj i) (NF.obj i))
      (hsmulM : ∀ ⦃i j : {x : Λ₀ // l ≤ x}⦄ (h : i ⟶ j)
          (b : (tailFunctor l ⋙ B₀).obj i) (m : MF.obj i),
        MF.map h (b • m) = (tailFunctor l ⋙ B₀).map h b • MF.map h m)
      (hsmulN : ∀ ⦃i j : {x : Λ₀ // l ≤ x}⦄ (h : i ⟶ j)
          (b : (tailFunctor l ⋙ B₀).obj i) (m : NF.obj i),
        NF.map h (b • m) = (tailFunctor l ⋙ B₀).map h b • NF.map h m)
      (μ : MF ⟶ (Functor.const {x : Λ₀ // l ≤ x}).obj (AddCommGrpCat.of M))
      (ν : NF ⟶ (Functor.const {x : Λ₀ // l ≤ x}).obj (AddCommGrpCat.of N))
      (_ : IsColimit (Cocone.mk (AddCommGrpCat.of M) μ))
      (_ : IsColimit (Cocone.mk (AddCommGrpCat.of N) ν))
      (us : MF ⟶ NF),
      (∀ (i : {x : Λ₀ // l ≤ x}) (b : (tailFunctor l ⋙ B₀).obj i) (m : MF.obj i),
        (μ.app i (b • m) : M) = HSMul.hSMul (α := S) (β := M)
          ((Functor.whiskerLeft (tailFunctor l) σ₀).app i b) (μ.app i m)) ∧
      (∀ (i : {x : Λ₀ // l ≤ x}) (b : (tailFunctor l ⋙ B₀).obj i) (m : NF.obj i),
        (ν.app i (b • m) : N) = HSMul.hSMul (α := S) (β := N)
          ((Functor.whiskerLeft (tailFunctor l) σ₀).app i b) (ν.app i m)) ∧
      (∀ i, Module.Finite ((tailFunctor l ⋙ B₀).obj i) (MF.obj i)) ∧
      (∀ i, Module.Finite ((tailFunctor l ⋙ B₀).obj i) (NF.obj i)) ∧
      (∀ ⦃i j : {x : Λ₀ // l ≤ x}⦄ (h : i ⟶ j),
        letI : Algebra ↑((tailFunctor l ⋙ B₀).obj i) ↑((tailFunctor l ⋙ B₀).obj j) :=
          ((tailFunctor l ⋙ B₀).map h).hom.toAlgebra
        letI : Module ↑((tailFunctor l ⋙ B₀).obj i) ↑(MF.obj j) :=
          Module.compHom _ ((tailFunctor l ⋙ B₀).map h).hom
        letI : IsScalarTower ↑((tailFunctor l ⋙ B₀).obj i) ↑((tailFunctor l ⋙ B₀).obj j)
            ↑(MF.obj j) := .of_algebraMap_smul fun _ _ => rfl
        IsBaseChange ↑((tailFunctor l ⋙ B₀).obj j)
          (⟨(MF.map h).hom.toAddHom, hsmulM h⟩ :
            ↑(MF.obj i) →ₗ[↑((tailFunctor l ⋙ B₀).obj i)] ↑(MF.obj j))) ∧
      (∀ ⦃i j : {x : Λ₀ // l ≤ x}⦄ (h : i ⟶ j),
        letI : Algebra ↑((tailFunctor l ⋙ B₀).obj i) ↑((tailFunctor l ⋙ B₀).obj j) :=
          ((tailFunctor l ⋙ B₀).map h).hom.toAlgebra
        letI : Module ↑((tailFunctor l ⋙ B₀).obj i) ↑(NF.obj j) :=
          Module.compHom _ ((tailFunctor l ⋙ B₀).map h).hom
        letI : IsScalarTower ↑((tailFunctor l ⋙ B₀).obj i) ↑((tailFunctor l ⋙ B₀).obj j)
            ↑(NF.obj j) := .of_algebraMap_smul fun _ _ => rfl
        IsBaseChange ↑((tailFunctor l ⋙ B₀).obj j)
          (⟨(NF.map h).hom.toAddHom, hsmulN h⟩ :
            ↑(NF.obj i) →ₗ[↑((tailFunctor l ⋙ B₀).obj i)] ↑(NF.obj j))) ∧
      (∀ (i : {x : Λ₀ // l ≤ x}) (b : (tailFunctor l ⋙ B₀).obj i) (m : MF.obj i),
        us.app i (b • m) = b • us.app i m) ∧
      (∀ (i : {x : Λ₀ // l ≤ x}) (m : MF.obj i), u (μ.app i m) = ν.app i (us.app i m)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have : Fintype ι' := Fintype.ofFinite ι'
  choose w hw0 using fun m : Fin n =>
    Submodule.Quotient.mk_surjective (Submodule.span S (Set.range v'))
      (e' (u (e.symm (Submodule.Quotient.mk (Pi.single m 1)))))
  have hwu : ∀ m : Fin n, u (e.symm (Submodule.Quotient.mk (Pi.single m 1)))
      = e'.symm (Submodule.Quotient.mk (w m)) := fun m => by
    rw [hw0 m, e'.symm_apply_apply]
  have hex : ∀ k : ι, ∃ c : ι' → S, matMap w (v k) = ∑ k', c k' • v' k' := by
    intro k
    have h0 : (Submodule.Quotient.mk (v k) : (Fin n → S) ⧸ Submodule.span S (Set.range v)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span ⟨k, rfl⟩)
    have h1 := apply_mk_eq_of_single e e' u w hwu (v k)
    rw [h0, map_zero, map_zero] at h1
    have h2 : (Submodule.Quotient.mk (matMap w (v k)) :
        (Fin n' → S) ⧸ Submodule.span S (Set.range v')) = 0 := by
      have h3 := congrArg (fun x => e' x) h1.symm
      rwa [e'.apply_symm_apply, map_zero] at h3
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).1
      ((Submodule.Quotient.mk_eq_zero _).1 h2)
    exact ⟨c, hc.symm⟩
  choose C hC using hex
  obtain ⟨l₀, -, z, hz0⟩ := exists_stage_lift σ₀ hσ₀
    (fun p : (ι × Fin n) ⊕ (ι' × Fin n') ⊕ (Fin n × Fin n') ⊕ (ι × ι') =>
      Sum.elim (fun q : ι × Fin n => v q.1 q.2)
        (Sum.elim (fun q : ι' × Fin n' => v' q.1 q.2)
          (Sum.elim (fun q : Fin n × Fin n' => w q.1 q.2)
            (fun q : ι × ι' => C q.1 q.2))) p)
    (Classical.arbitrary Λ₀)
  obtain ⟨aL, aL', aU, aC, haL, haL', haU, haC⟩ :
      ∃ (aL : ι → Fin n → ↑(B₀.obj l₀)) (aL' : ι' → Fin n' → ↑(B₀.obj l₀))
        (aU : Fin n → Fin n' → ↑(B₀.obj l₀)) (aC : ι → ι' → ↑(B₀.obj l₀)),
        (∀ k m, legHom σ₀ l₀ (aL k m) = v k m) ∧
        (∀ k m', legHom σ₀ l₀ (aL' k m') = v' k m') ∧
        (∀ m m', legHom σ₀ l₀ (aU m m') = w m m') ∧
        (∀ k k', legHom σ₀ l₀ (aC k k') = C k k') :=
    ⟨fun k m => z (Sum.inl (k, m)), fun k m' => z (Sum.inr (Sum.inl (k, m'))),
      fun m m' => z (Sum.inr (Sum.inr (Sum.inl (m, m')))),
      fun k k' => z (Sum.inr (Sum.inr (Sum.inr (k, k')))),
      fun _ _ => hz0 _, fun _ _ => hz0 _, fun _ _ => hz0 _, fun _ _ => hz0 _⟩
  obtain ⟨l, hl₀l, heq⟩ := exists_eventually_eq σ₀ hσ₀
    (fun q : ι × Fin n' => matMap aU (aL q.1) q.2)
    (fun q : ι × Fin n' => (∑ k', aC q.1 k' • aL' k') q.2)
    (fun q => by
      rw [matMap_map (legHom σ₀ l₀) haU (aL q.1) q.2,
        show (fun m => legHom σ₀ l₀ (aL q.1 m)) = v q.1 from funext (haL q.1),
        hC q.1, map_sum_smul_apply _ (haC q.1) haL'])
  obtain ⟨cL, cL', cU, cC, hcLdef, hcL'def, hcUdef, hcCdef⟩ :
      ∃ (cL : ι → Fin n → ↑(B₀.obj l)) (cL' : ι' → Fin n' → ↑(B₀.obj l))
        (cU : Fin n → Fin n' → ↑(B₀.obj l)) (cC : ι → ι' → ↑(B₀.obj l)),
        (∀ k m, cL k m = (B₀.map (homOfLE hl₀l)).hom (aL k m)) ∧
        (∀ k m', cL' k m' = (B₀.map (homOfLE hl₀l)).hom (aL' k m')) ∧
        (∀ m m', cU m m' = (B₀.map (homOfLE hl₀l)).hom (aU m m')) ∧
        (∀ k k', cC k k' = (B₀.map (homOfLE hl₀l)).hom (aC k k')) :=
    ⟨_, _, _, _, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  have hcL : ∀ k m, legHom σ₀ l (cL k m) = v k m := fun k m => by
    rw [hcLdef, legHom_map σ₀ (homOfLE hl₀l) (aL k m)]; exact haL k m
  have hcL' : ∀ k m', legHom σ₀ l (cL' k m') = v' k m' := fun k m' => by
    rw [hcL'def, legHom_map σ₀ (homOfLE hl₀l) (aL' k m')]; exact haL' k m'
  have hcU : ∀ m m', legHom σ₀ l (cU m m') = w m m' := fun m m' => by
    rw [hcUdef, legHom_map σ₀ (homOfLE hl₀l) (aU m m')]; exact haU m m'
  have keyl : ∀ k : ι, matMap cU (cL k) = ∑ k', cC k k' • cL' k' := fun k =>
    matMap_eq_sum_of_map (B₀.map (homOfLE hl₀l)).hom
      (fun m m' => (hcUdef m m').symm) (fun m => (hcLdef k m).symm)
      (fun k' => (hcCdef k k').symm) (fun k' m' => (hcL'def k' m').symm)
      (fun m' => heq (k, m'))
  have : Nonempty {x : Λ₀ // l ≤ x} := ⟨⟨l, le_refl l⟩⟩
  have : IsDirected {x : Λ₀ // l ≤ x} (· ≤ ·) := isDirected_tail l
  obtain ⟨tr, htrdef⟩ : ∃ tr : ∀ i : {x : Λ₀ // l ≤ x},
        ↑(B₀.obj l) →+* ↑((tailFunctor l ⋙ B₀).obj i),
      ∀ i : {x : Λ₀ // l ≤ x}, tr i = ((tailFunctor l ⋙ B₀).map
        (homOfLE (show (⟨l, le_refl l⟩ : {x : Λ₀ // l ≤ x}) ≤ i from i.2))).hom :=
    ⟨_, fun _ => rfl⟩
  have htrmap : ∀ (x : ↑(B₀.obj l)) ⦃i j : {x : Λ₀ // l ≤ x}⦄ (h : i ⟶ j),
      ((tailFunctor l ⋙ B₀).map h).hom (tr i x) = tr j x := by
    intro x i j h
    have hc : ((tailFunctor l ⋙ B₀).map
          (homOfLE (show (⟨l, le_refl l⟩ : {x : Λ₀ // l ≤ x}) ≤ i from i.2)))
        ≫ ((tailFunctor l ⋙ B₀).map h)
        = (tailFunctor l ⋙ B₀).map
          (homOfLE (show (⟨l, le_refl l⟩ : {x : Λ₀ // l ≤ x}) ≤ j from j.2)) := by
      rw [← Functor.map_comp]; rfl
    rw [htrdef i, htrdef j]
    exact congrArg (fun g => CommRingCat.Hom.hom g x) hc
  have htrleg : ∀ (i : {x : Λ₀ // l ≤ x}) (x : ↑(B₀.obj l)),
      legHom (Functor.whiskerLeft (tailFunctor l) σ₀) i (tr i x) = legHom σ₀ l x := by
    intro i x
    rw [htrdef i]
    exact legHom_map (Functor.whiskerLeft (tailFunctor l) σ₀)
      (homOfLE (show (⟨l, le_refl l⟩ : {x : Λ₀ // l ≤ x}) ≤ i from i.2)) x
  obtain ⟨rel, hreldef⟩ : ∃ rel : ∀ i : {x : Λ₀ // l ≤ x}, ι → Fin n →
        ↑((tailFunctor l ⋙ B₀).obj i), ∀ i k m, rel i k m = tr i (cL k m) :=
    ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨rel', hrel'def⟩ : ∃ rel' : ∀ i : {x : Λ₀ // l ≤ x}, ι' → Fin n' →
        ↑((tailFunctor l ⋙ B₀).obj i), ∀ i k m', rel' i k m' = tr i (cL' k m') :=
    ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨Uf, hUfdef⟩ : ∃ Uf : ∀ i : {x : Λ₀ // l ≤ x}, Fin n → Fin n' →
        ↑((tailFunctor l ⋙ B₀).obj i), ∀ i m m', Uf i m m' = tr i (cU m m') :=
    ⟨_, fun _ _ _ => rfl⟩
  have hrel : ∀ {i j : {x : Λ₀ // l ≤ x}} (h : i ⟶ j) (k : ι) (m : Fin n),
      ((tailFunctor l ⋙ B₀).map h).hom (rel i k m) = rel j k m := by
    intro i j h k m; rw [hreldef, hreldef]; exact htrmap (cL k m) h
  have hrel' : ∀ {i j : {x : Λ₀ // l ≤ x}} (h : i ⟶ j) (k : ι') (m' : Fin n'),
      ((tailFunctor l ⋙ B₀).map h).hom (rel' i k m') = rel' j k m' := by
    intro i j h k m'; rw [hrel'def, hrel'def]; exact htrmap (cL' k m') h
  have hU : ∀ {i j : {x : Λ₀ // l ≤ x}} (h : i ⟶ j) (m : Fin n) (m' : Fin n'),
      ((tailFunctor l ⋙ B₀).map h).hom (Uf i m m') = Uf j m m' := by
    intro i j h m m'; rw [hUfdef, hUfdef]; exact htrmap (cU m m') h
  have hv : ∀ (i : {x : Λ₀ // l ≤ x}) (k : ι) (m : Fin n),
      legHom (Functor.whiskerLeft (tailFunctor l) σ₀) i (rel i k m) = v k m := by
    intro i k m; rw [hreldef]; exact (htrleg i (cL k m)).trans (hcL k m)
  have hv' : ∀ (i : {x : Λ₀ // l ≤ x}) (k : ι') (m' : Fin n'),
      legHom (Functor.whiskerLeft (tailFunctor l) σ₀) i (rel' i k m') = v' k m' := by
    intro i k m'; rw [hrel'def]; exact (htrleg i (cL' k m')).trans (hcL' k m')
  have hw : ∀ (i : {x : Λ₀ // l ≤ x}) (m : Fin n) (m' : Fin n'),
      legHom (Functor.whiskerLeft (tailFunctor l) σ₀) i (Uf i m m') = w m m' := by
    intro i m m'; rw [hUfdef]; exact (htrleg i (cU m m')).trans (hcU m m')
  have hUrel : ∀ (i : {x : Λ₀ // l ≤ x}) (k : ι),
      matMap (Uf i) (rel i k) ∈ relSpan rel' i := by
    intro i k
    rw [show matMap (Uf i) (rel i k) = ∑ k', tr i (cC k k') • rel' i k' from
      matMap_eq_sum_of_map (tr i) (fun m m' => (hUfdef i m m').symm)
        (fun m => (hreldef i k m).symm) (fun k' => rfl) (fun k' m' => (hrel'def i k' m').symm)
        (fun m' => congrArg (tr i) (congrFun (keyl k) m'))]
    exact Submodule.sum_mem _ fun k' _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k', rfl⟩)
  have := tailFunctor_final l
  have hσt : IsColimit (Cocone.mk (CommRingCat.of S)
      (Functor.whiskerLeft (tailFunctor l) σ₀)) :=
    (Functor.Final.isColimitWhiskerEquiv (tailFunctor l) _).symm hσ₀
  exact ⟨l, relQuot rel hrel, relQuot rel' hrel',
    fun i => inferInstanceAs (Module ↑((tailFunctor l ⋙ B₀).obj i)
      ((Fin n → ↑((tailFunctor l ⋙ B₀).obj i)) ⧸ relSpan rel i)),
    fun i => inferInstanceAs (Module ↑((tailFunctor l ⋙ B₀).obj i)
      ((Fin n' → ↑((tailFunctor l ⋙ B₀).obj i)) ⧸ relSpan rel' i)),
    relQuot_map_smul rel hrel, relQuot_map_smul rel' hrel',
    modCocone (Functor.whiskerLeft (tailFunctor l) σ₀) rel hrel hv e,
    modCocone (Functor.whiskerLeft (tailFunctor l) σ₀) rel' hrel' hv' e',
    isColimit_modCocone _ _ hσt e rel hrel hv,
    isColimit_modCocone _ _ hσt e' rel' hrel' hv',
    relQuotNatTrans (hrel := hrel) (hrel' := hrel') Uf hU hUrel,
    modCocone_app_smul _ rel hrel hv e, modCocone_app_smul _ rel' hrel' hv' e',
    relQuot_finite rel, relQuot_finite rel',
    (fun {_ _} h => isBaseChange_relQuot rel hrel h _ (relQuot_map_mk rel hrel h)),
    (fun {_ _} h => isBaseChange_relQuot rel' hrel' h _ (relQuot_map_mk rel' hrel' h)),
    (fun i b m => map_smul (mapQuot (rel := rel) (rel' := rel') Uf hUrel i) b
      (show (Fin n → ↑((tailFunctor l ⋙ B₀).obj i)) ⧸ relSpan rel i from m)),
    (fun i m => modCocone_relQuotNatTrans (hv := hv) (hv' := hv') u w hwu Uf hU hUrel hw i m)⟩

/-- Let `S` be the colimit of a directed system of rings `B_λ` and let `u : M → N` be a map of
finitely presented `S`-modules. Then there is a stage `l` such that for `λ ≥ l` there are finite
`B_λ`-modules `M_λ`, `N_λ` and `B_λ`-linear maps `u_λ : M_λ → N_λ` with `colim M_λ = M`,
`colim N_λ = N` and `colim u_λ = u`, both module systems being cartesian: `M_μ = M_λ ⊗_{B_λ} B_μ`
and `N_μ = N_λ ⊗_{B_λ} B_μ`. -/
public theorem exists_module_map_system_of_isColimit [Module.FinitePresentation S M]
    [Module.FinitePresentation S N]
    {Λ₀ : Type u} [Preorder Λ₀] [Nonempty Λ₀] [IsDirected Λ₀ (· ≤ ·)]
    (B₀ : Λ₀ ⥤ CommRingCat.{u}) (σ₀ : B₀ ⟶ (Functor.const Λ₀).obj (CommRingCat.of S))
    (hσ₀ : IsColimit (Cocone.mk (CommRingCat.of S) σ₀)) (u : M →ₗ[S] N) :
    ∃ (l : Λ₀) (MF NF : {x : Λ₀ // l ≤ x} ⥤ AddCommGrpCat.{u})
      (_ : ∀ i, Module ((tailFunctor l ⋙ B₀).obj i) (MF.obj i))
      (_ : ∀ i, Module ((tailFunctor l ⋙ B₀).obj i) (NF.obj i))
      (hsmulM : ∀ ⦃i j : {x : Λ₀ // l ≤ x}⦄ (h : i ⟶ j)
          (b : (tailFunctor l ⋙ B₀).obj i) (m : MF.obj i),
        MF.map h (b • m) = (tailFunctor l ⋙ B₀).map h b • MF.map h m)
      (hsmulN : ∀ ⦃i j : {x : Λ₀ // l ≤ x}⦄ (h : i ⟶ j)
          (b : (tailFunctor l ⋙ B₀).obj i) (m : NF.obj i),
        NF.map h (b • m) = (tailFunctor l ⋙ B₀).map h b • NF.map h m)
      (μ : MF ⟶ (Functor.const {x : Λ₀ // l ≤ x}).obj (AddCommGrpCat.of M))
      (ν : NF ⟶ (Functor.const {x : Λ₀ // l ≤ x}).obj (AddCommGrpCat.of N))
      (_ : IsColimit (Cocone.mk (AddCommGrpCat.of M) μ))
      (_ : IsColimit (Cocone.mk (AddCommGrpCat.of N) ν))
      (us : MF ⟶ NF),
      (∀ (i : {x : Λ₀ // l ≤ x}) (b : (tailFunctor l ⋙ B₀).obj i) (m : MF.obj i),
        (μ.app i (b • m) : M) = HSMul.hSMul (α := S) (β := M)
          ((Functor.whiskerLeft (tailFunctor l) σ₀).app i b) (μ.app i m)) ∧
      (∀ (i : {x : Λ₀ // l ≤ x}) (b : (tailFunctor l ⋙ B₀).obj i) (m : NF.obj i),
        (ν.app i (b • m) : N) = HSMul.hSMul (α := S) (β := N)
          ((Functor.whiskerLeft (tailFunctor l) σ₀).app i b) (ν.app i m)) ∧
      (∀ i, Module.Finite ((tailFunctor l ⋙ B₀).obj i) (MF.obj i)) ∧
      (∀ i, Module.Finite ((tailFunctor l ⋙ B₀).obj i) (NF.obj i)) ∧
      (∀ ⦃i j : {x : Λ₀ // l ≤ x}⦄ (h : i ⟶ j),
        letI : Algebra ↑((tailFunctor l ⋙ B₀).obj i) ↑((tailFunctor l ⋙ B₀).obj j) :=
          ((tailFunctor l ⋙ B₀).map h).hom.toAlgebra
        letI : Module ↑((tailFunctor l ⋙ B₀).obj i) ↑(MF.obj j) :=
          Module.compHom _ ((tailFunctor l ⋙ B₀).map h).hom
        letI : IsScalarTower ↑((tailFunctor l ⋙ B₀).obj i) ↑((tailFunctor l ⋙ B₀).obj j)
            ↑(MF.obj j) := .of_algebraMap_smul fun _ _ => rfl
        IsBaseChange ↑((tailFunctor l ⋙ B₀).obj j)
          (⟨(MF.map h).hom.toAddHom, hsmulM h⟩ :
            ↑(MF.obj i) →ₗ[↑((tailFunctor l ⋙ B₀).obj i)] ↑(MF.obj j))) ∧
      (∀ ⦃i j : {x : Λ₀ // l ≤ x}⦄ (h : i ⟶ j),
        letI : Algebra ↑((tailFunctor l ⋙ B₀).obj i) ↑((tailFunctor l ⋙ B₀).obj j) :=
          ((tailFunctor l ⋙ B₀).map h).hom.toAlgebra
        letI : Module ↑((tailFunctor l ⋙ B₀).obj i) ↑(NF.obj j) :=
          Module.compHom _ ((tailFunctor l ⋙ B₀).map h).hom
        letI : IsScalarTower ↑((tailFunctor l ⋙ B₀).obj i) ↑((tailFunctor l ⋙ B₀).obj j)
            ↑(NF.obj j) := .of_algebraMap_smul fun _ _ => rfl
        IsBaseChange ↑((tailFunctor l ⋙ B₀).obj j)
          (⟨(NF.map h).hom.toAddHom, hsmulN h⟩ :
            ↑(NF.obj i) →ₗ[↑((tailFunctor l ⋙ B₀).obj i)] ↑(NF.obj j))) ∧
      (∀ (i : {x : Λ₀ // l ≤ x}) (b : (tailFunctor l ⋙ B₀).obj i) (m : MF.obj i),
        us.app i (b • m) = b • us.app i m) ∧
      (∀ (i : {x : Λ₀ // l ≤ x}) (m : MF.obj i), u (μ.app i m) = ν.app i (us.app i m)) := by
  obtain ⟨n, K, e₁, t, ht⟩ := Module.FinitePresentation.exists_fin S M
  obtain ⟨n', K', e₁', t', ht'⟩ := Module.FinitePresentation.exists_fin S N
  have hspan : Submodule.span S (Set.range (fun x : {x : Fin n → S // x ∈ t} => x.1)) = K := by
    simpa using ht
  have hspan' : Submodule.span S (Set.range (fun x : {x : Fin n' → S // x ∈ t'} => x.1))
      = K' := by
    simpa using ht'
  exact exists_module_map_system_aux B₀ σ₀ hσ₀ u
    (e₁.trans (Submodule.quotEquivOfEq K _ hspan.symm))
    (e₁'.trans (Submodule.quotEquivOfEq K' _ hspan'.symm))

/-- Let `u : M → N` be the colimit of a map `us` of directed systems of modules. If for every `i`
there is `j ≥ i` with `us.app j` injective, then `u` is injective. -/
public theorem injective_of_forall_exists_ge_injective
    {S M N : Type u} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    {MF NF : Λ ⥤ AddCommGrpCat.{u}} (u : M →ₗ[S] N)
    {μ : MF ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M)}
    {ν : NF ⟶ (Functor.const Λ).obj (AddCommGrpCat.of N)}
    (hμ : IsColimit (Cocone.mk (AddCommGrpCat.of M) μ))
    (hν : IsColimit (Cocone.mk (AddCommGrpCat.of N) ν)) (us : MF ⟶ NF)
    (hus : ∀ (i : Λ) (m : MF.obj i), u (μ.app i m) = ν.app i (us.app i m))
    (hcof : ∀ i : Λ, ∃ j, i ≤ j ∧ Function.Injective (us.app j)) :
    Function.Injective u := by
  have : IsFiltered Λ := inferInstance
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨i, m, rfl⟩ := Concrete.isColimit_exists_rep MF hμ x
  have h0 : (ν.app i) (us.app i m) = (ν.app i) 0 := by
    rwa [map_zero, ← hus i m]
  obtain ⟨k, f, g, hfg⟩ := (IsColimit.eq_iff NF hν).1 h0
  obtain ⟨j, hkj, hinj⟩ := hcof k
  have hik : i ≤ k := leOfHom f
  have hij : i ≤ j := hik.trans hkj
  have hnat : ∀ ⦃p q : Λ⦄ (h : p ⟶ q) (y : MF.obj p),
      us.app q (MF.map h y) = NF.map h (us.app p y) :=
    fun {p q} h y => congrArg (fun t : MF.obj p ⟶ NF.obj q => t y) (us.naturality h)
  have hdead : us.app j (MF.map (homOfLE hij) m) = 0 := by
    rw [hnat (homOfLE hij) m,
      show NF.map (homOfLE hij) = NF.map (homOfLE hik) ≫ NF.map (homOfLE hkj) from by
        rw [← NF.map_comp]; rfl]
    change NF.map (homOfLE hkj) (NF.map (homOfLE hik) (us.app i m)) = 0
    rw [show NF.map (homOfLE hik) (us.app i m) = NF.map f (us.app i m) from
        congrArg (fun t : i ⟶ k => (NF.map t) (us.app i m)) (Subsingleton.elim _ f),
      hfg, map_zero, map_zero]
  have hzero : MF.map (homOfLE hij) m = 0 :=
    hinj (hdead.trans (map_zero (ConcreteCategory.hom (us.app j))).symm)
  have hw : (μ.app j) (MF.map (homOfLE hij) m) = (μ.app i) m :=
    congrArg (fun t : MF.obj i ⟶ AddCommGrpCat.of M => t m)
      ((Cocone.mk (AddCommGrpCat.of M) μ).w (homOfLE hij))
  rw [← hw, hzero, map_zero]

end Existence

end SpreadingOut

open CategoryTheory Limits Stacks.SpreadingOut.LocalModuleSystem SpreadingOut in
/-- Let `R → S` be a local homomorphism of local rings which is essentially of finite
presentation, let `M` and `N` be finitely presented `S`-modules and let `u : M → N` be `S`-linear.
Then there are a directed system of local homomorphisms `A_λ → B_λ` of local rings, with `A_λ`
essentially of finite type over `ℤ` and `B_λ` essentially of finite type over `A_λ`, with colimit
`R → S` and local structure maps, in which every `B_μ` is a localization at a prime of
`B_λ ⊗_{A_λ} A_μ`; cartesian systems of finite `B_λ`-modules `M_λ` and `N_λ` with colimits `M` and
`N`; and `B_λ`-linear maps `u_λ : M_λ → N_λ` with colimit `u`. -/
public theorem RingHom.EssentiallyOfFinitePresentation.exists_isColimit_essFiniteType_module_map
    {R S M N : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup M] [Module S M] [Module.FinitePresentation S M]
    [AddCommGroup N] [Module S N] [Module.FinitePresentation S N]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation) (u : M →ₗ[S] N) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (A B : Λ ⥤ CommRingCat.{u}) (φ : A ⟶ B) (MF NF : Λ ⥤ AddCommGrpCat.{u})
      (_ : ∀ i, Module (B.obj i) (MF.obj i))
      (_ : ∀ i, Module (B.obj i) (NF.obj i))
      (hsmulM : ∀ ⦃i j : Λ⦄ (h : i ⟶ j) (b : B.obj i) (m : MF.obj i),
        MF.map h (b • m) = B.map h b • MF.map h m)
      (hsmulN : ∀ ⦃i j : Λ⦄ (h : i ⟶ j) (b : B.obj i) (m : NF.obj i),
        NF.map h (b • m) = B.map h b • NF.map h m)
      (ρ : A ⟶ (Functor.const Λ).obj (CommRingCat.of R))
      (σ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S))
      (μ : MF ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M))
      (ν : NF ⟶ (Functor.const Λ).obj (AddCommGrpCat.of N))
      (_ : IsColimit (Cocone.mk (CommRingCat.of R) ρ))
      (_ : IsColimit (Cocone.mk (CommRingCat.of S) σ))
      (_ : IsColimit (Cocone.mk (AddCommGrpCat.of M) μ))
      (_ : IsColimit (Cocone.mk (AddCommGrpCat.of N) ν))
      (us : MF ⟶ NF),
      (∀ i, φ.app i ≫ σ.app i = ρ.app i ≫ CommRingCat.ofHom (algebraMap R S)) ∧
      (∀ (i : Λ) (b : B.obj i) (m : MF.obj i),
        (μ.app i (b • m) : M) = HSMul.hSMul (α := S) (β := M) (σ.app i b) (μ.app i m)) ∧
      (∀ (i : Λ) (b : B.obj i) (m : NF.obj i),
        (ν.app i (b • m) : N) = HSMul.hSMul (α := S) (β := N) (σ.app i b) (ν.app i m)) ∧
      (∀ i, IsLocalRing (A.obj i)) ∧ (∀ i, IsLocalRing (B.obj i)) ∧
      (∀ i, IsLocalHom (φ.app i).hom) ∧
      (∀ i, IsLocalHom (ρ.app i).hom) ∧
      (∀ i, IsLocalHom (σ.app i).hom) ∧
      (∀ i, Algebra.EssFiniteType ℤ (A.obj i)) ∧
      (∀ i, (φ.app i).hom.EssFiniteType) ∧
      (∀ i, Module.Finite (B.obj i) (MF.obj i)) ∧
      (∀ i, Module.Finite (B.obj i) (NF.obj i)) ∧
      (∀ ⦃i j : Λ⦄ (h : i ⟶ j),
        letI := (pushout.desc (B.map h) (φ.app j) (φ.naturality h).symm).hom.toAlgebra
        ∃ (q : Ideal ↑(pushout (φ.app i) (A.map h))) (_ : q.IsPrime),
          IsLocalization q.primeCompl ↑(B.obj j)) ∧
      (∀ ⦃i j : Λ⦄ (h : i ⟶ j),
        letI : Algebra ↑(B.obj i) ↑(B.obj j) := (B.map h).hom.toAlgebra
        letI : Module ↑(B.obj i) ↑(MF.obj j) := Module.compHom _ (B.map h).hom
        letI : IsScalarTower ↑(B.obj i) ↑(B.obj j) ↑(MF.obj j) :=
          .of_algebraMap_smul fun _ _ => rfl
        IsBaseChange ↑(B.obj j)
          (⟨(MF.map h).hom.toAddHom, hsmulM h⟩ :
            ↑(MF.obj i) →ₗ[↑(B.obj i)] ↑(MF.obj j))) ∧
      (∀ ⦃i j : Λ⦄ (h : i ⟶ j),
        letI : Algebra ↑(B.obj i) ↑(B.obj j) := (B.map h).hom.toAlgebra
        letI : Module ↑(B.obj i) ↑(NF.obj j) := Module.compHom _ (B.map h).hom
        letI : IsScalarTower ↑(B.obj i) ↑(B.obj j) ↑(NF.obj j) :=
          .of_algebraMap_smul fun _ _ => rfl
        IsBaseChange ↑(B.obj j)
          (⟨(NF.map h).hom.toAddHom, hsmulN h⟩ :
            ↑(NF.obj i) →ₗ[↑(B.obj i)] ↑(NF.obj j))) ∧
      (∀ (i : Λ) (b : B.obj i) (m : MF.obj i), us.app i (b • m) = b • us.app i m) ∧
      (∀ (i : Λ) (m : MF.obj i), u (μ.app i m) = ν.app i (us.app i m)) := by
  obtain ⟨Λ₀, instP, instNe, instDir, A₀, B₀, φ₀, ρ₀, σ₀, hρ₀, hσ₀, hcomm₀, hAloc, hBloc,
    hφloc, hρloc, hσloc, hAess, hφess, hcart₀⟩ :=
    exists_ringSystem_of_essentiallyOfFinitePresentation hS
  let _ : Preorder Λ₀ := instP
  let _ : Nonempty Λ₀ := instNe
  let _ : IsDirected Λ₀ (· ≤ ·) := instDir
  obtain ⟨l, MF, NF, instM, instN, hsmulM, hsmulN, μ, ν, hμ, hν, us, hμsemi, hνsemi,
    hMfin, hNfin, hMbc, hNbc, husmul, huscolim⟩ :=
    exists_module_map_system_of_isColimit B₀ σ₀ hσ₀ u
  have := tailFunctor_final l
  exact ⟨{x : Λ₀ // l ≤ x}, inferInstance, ⟨⟨l, le_refl l⟩⟩, isDirected_tail l,
    tailFunctor l ⋙ A₀, tailFunctor l ⋙ B₀, Functor.whiskerLeft (tailFunctor l) φ₀,
    MF, NF, instM, instN, hsmulM, hsmulN,
    Functor.whiskerLeft (tailFunctor l) ρ₀, Functor.whiskerLeft (tailFunctor l) σ₀, μ, ν,
    (Functor.Final.isColimitWhiskerEquiv (tailFunctor l) _).symm hρ₀,
    (Functor.Final.isColimitWhiskerEquiv (tailFunctor l) _).symm hσ₀, hμ, hν, us,
    fun i => hcomm₀ i.1, hμsemi, hνsemi,
    fun i => hAloc i.1, fun i => hBloc i.1, fun i => hφloc i.1, fun i => hρloc i.1,
    fun i => hσloc i.1, fun i => hAess i.1, fun i => hφess i.1, hMfin, hNfin,
    fun {_ _} h => hcart₀ ((tailFunctor l).map h), hMbc, hNbc, husmul, huscolim⟩
