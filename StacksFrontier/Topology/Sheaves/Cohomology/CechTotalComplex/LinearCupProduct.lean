module

public import StacksFrontier.CategoryTheory.Sites.CechComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.RecoveryC.CechCupProduct

/-!
# The cup product on total Čech complexes, linear over a base ring

Let `C` be a category with finite products, let `W : ι → C` be a family of objects -- for the
Čech complex of a topological space, a family of opens covering it -- and let `R` be a
commutative ring.  For complexes `K` and `L` of presheaves of `R`-modules on `C` this file
builds the Alexander--Whitney cup product

`Tot(Tot(Č(W,K)) ⊗_R Tot(Č(W,L))) ⟶ Tot(Č(W,M))`

with the Koszul signs dictated by totalization, where `M` is any complex of coefficient
presheaves receiving a *pairing* of `K` and `L`, i.e. a compatible family of maps out of the
pointwise tensor products `K^a ⊗_R L^b`.  The Čech complex is extended by zero from `ℕ` to `ℤ`,
the Čech degree is the first degree of the double complex, and all totalizations are direct
sums, so neither boundedness of the coefficient complexes nor finiteness of `W` is needed.

## Main definitions

* `Stacks.Cech.LinearCupProduct.totalCechComplexFunctor` is the total Čech complex of a
  complex of presheaves of `R`-modules.
* `Stacks.Cech.LinearCupProduct.tensorPresheafModules` is the pointwise tensor product over
  `R` of two presheaves of `R`-modules, and `Pairing` is a morphism out of it.
* `Stacks.Cech.LinearCupProduct.cechAlexanderWhitney` restricts a pair of Čech cochains to the
  front and back faces and pairs the restrictions.
* `Stacks.Cech.LinearCupProduct.ComplexPairing` is a degreewise pairing of two complexes of
  coefficient presheaves into a third, compatible with the differentials by the Leibniz rule.
* `Stacks.Cech.LinearCupProduct.cechCupProduct` is the signed Alexander--Whitney map.

## Main results

* `Stacks.Cech.LinearCupProduct.cechCupProduct`: the signed Alexander--Whitney map of
  complexes `Tot(Tot(Č(W,K)) ⊗_R Tot(Č(W,L))) ⟶ Tot(Č(W,M))` attached to a `ComplexPairing`.
* `Stacks.Cech.LinearCupProduct.cechCupProduct_ι`: on the pair of homogeneous Čech summands of
  bidegrees `(r, a)` and `(s, b)` the cup product is the front/back restriction formula with the
  sign `cupProductSign (r + a) (r + s) r`.

## References

* [Stacks Project, Tag 07MB](https://stacks.math.columbia.edu/tag/07MB)
* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
* [SGA4, Exposé XVII]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite
open Stacks.CategoryTheory.CechComplex
open Stacks.Cech.CupProduct (tensorModules tensorModulesMap tensorModulesMap_comp cupProductSign
  cupProductSign_summand signed_four_terms sum_front_back moduleCoprodTensorCoprodIso
  moduleCoprodTensorCoprodDesc moduleCoprodTensorCoprodDesc_ι moduleCoprodTensorCoprod_hom_ext)

open scoped TensorProduct

universe u w uC vC uR

namespace Stacks.Cech.LinearCupProduct

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

attribute [local implicit_reducible] CategoryTheory.cechComplexFunctor
  HomologicalComplex₂.ofGradedObject
  HomologicalComplex₂.flip
  HomologicalComplex₂.flipFunctor
  ComplexShape.Embedding.extendFunctor
  CategoryTheory.Functor.mapBifunctorHomologicalComplex
  CategoryTheory.Functor.mapBifunctorHomologicalComplexObj
  CategoryTheory.GradedObject.mapBifunctor
  HomologicalComplex₂.totalFunctor

/-- Presheaves of `R`-modules on `C`: the coefficients of the Čech complex. -/
abbrev PresheafModules (C : Type uC) [Category.{vC} C] (R : Type uR) [CommRing R] :=
  Cᵒᵖ ⥤ ModuleCat.{u} R

section Tensor

variable (R : Type uR) [CommRing R] {C : Type uC} [Category.{vC} C]

/-- The pointwise tensor product over `R` of two presheaves of `R`-modules, as a bifunctor. -/
@[implicit_reducible]
def tensorPresheafModules :
    PresheafModules.{u} C R ⥤ PresheafModules.{u} C R ⥤ PresheafModules.{u} C R :=
  Functor.curry.obj
    { obj := fun F =>
        { obj := fun V => ModuleCat.of R (F.1.obj V ⊗[R] F.2.obj V)
          map := fun f => ModuleCat.ofHom (TensorProduct.map (F.1.map f).hom (F.2.map f).hom)
          map_id := by intro V; simp
          map_comp := by
            intro V₁ V₂ V₃ f g
            simp only [Functor.map_comp, ModuleCat.hom_comp]
            ext : 1
            exact TensorProduct.map_comp _ _ _ _ }
      map := fun f =>
        { app := fun V => ModuleCat.ofHom (TensorProduct.map (f.1.app V).hom (f.2.app V).hom)
          naturality := by
            intro V₁ V₂ g
            ext : 1
            change (TensorProduct.map _ _).comp (TensorProduct.map _ _) =
              (TensorProduct.map _ _).comp (TensorProduct.map _ _)
            rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
            congr 1
            · exact congrArg ModuleCat.Hom.hom (f.1.naturality g)
            · exact congrArg ModuleCat.Hom.hom (f.2.naturality g) }
      map_id _ := NatTrans.ext <| funext fun _ => ModuleCat.hom_ext TensorProduct.map_id
      map_comp _ _ :=
        NatTrans.ext <| funext fun _ => ModuleCat.hom_ext (TensorProduct.map_comp _ _ _ _) }

/-- A pairing of two presheaves of `R`-modules into a third: a morphism out of their pointwise
tensor product over `R`. -/
abbrev Pairing (P Q T : PresheafModules.{u} C R) :=
  ((tensorPresheafModules.{u} R).obj P).obj Q ⟶ T

/-- **A pairing of complexes of coefficient presheaves.**  The maps `K^a ⊗_R L^b ⟶ M^n` for
`a + b = n`, satisfying the Leibniz rule with the Koszul sign. -/
structure ComplexPairing (K L M : CochainComplex (PresheafModules.{u} C R) ℤ) where
  /-- The pairing of a pair of homogeneous coefficient degrees. -/
  μ : ∀ (a b n : ℤ), a + b = n → Pairing.{u} R (K.X a) (L.X b) (M.X n)
  /-- The Leibniz rule relating the pairing to the three differentials. -/
  μ_d : ∀ (a b n : ℤ) (h : a + b = n),
    μ a b n h ≫ M.d n (n + 1) =
      ((tensorPresheafModules.{u} R).map (K.d a (a + 1))).app (L.X b) ≫
          μ (a + 1) b (n + 1) (by omega) +
        a.negOnePow • (((tensorPresheafModules.{u} R).obj (K.X a)).map (L.d b (b + 1)) ≫
          μ a (b + 1) (n + 1) (by omega))

/-- The pointwise tensor product pairs two restriction maps. -/
theorem tensorPresheafModules_map_app {P Q : PresheafModules.{u} C R} {V₁ V₂ : Cᵒᵖ}
    (g : V₁ ⟶ V₂) :
    (((tensorPresheafModules.{u} R).obj P).obj Q).map g =
      tensorModulesMap R (P.map g) (Q.map g) :=
  rfl

/-- The left action of the pointwise tensor product on morphisms. -/
theorem tensorPresheafModules_map_left_app {P P' : PresheafModules.{u} C R}
    (f : P ⟶ P') (Q : PresheafModules.{u} C R) (V : Cᵒᵖ) :
    (((tensorPresheafModules.{u} R).map f).app Q).app V =
      tensorModulesMap R (f.app V) (𝟙 (Q.obj V)) :=
  rfl

/-- The right action of the pointwise tensor product on morphisms. -/
theorem tensorPresheafModules_map_right_app (P : PresheafModules.{u} C R)
    {Q Q' : PresheafModules.{u} C R} (g : Q ⟶ Q') (V : Cᵒᵖ) :
    (((tensorPresheafModules.{u} R).obj P).map g).app V =
      tensorModulesMap R (𝟙 (P.obj V)) (g.app V) :=
  rfl

variable {R}

/-- Tensoring a finite sum of morphisms on the left. -/
theorem tensorModulesMap_sum_left {M M' : ModuleCat.{u} R} {N N' : ModuleCat.{w} R}
    {J : Type*} (S : Finset J) (f : J → (M ⟶ M')) (g : N ⟶ N') :
    tensorModulesMap R (∑ i ∈ S, f i) g = ∑ i ∈ S, tensorModulesMap R (f i) g := by
  induction S using Finset.cons_induction with
  | empty => ext : 1; exact TensorProduct.map_zero_left _
  | cons i S hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons, ← ih]
    exact ModuleCat.hom_ext (TensorProduct.map_add_left _ _ _)

/-- Tensoring a finite sum of morphisms on the right. -/
theorem tensorModulesMap_sum_right {M M' : ModuleCat.{u} R} {N N' : ModuleCat.{w} R}
    {J : Type*} (S : Finset J) (f : M ⟶ M') (g : J → (N ⟶ N')) :
    tensorModulesMap R f (∑ i ∈ S, g i) = ∑ i ∈ S, tensorModulesMap R f (g i) := by
  induction S using Finset.cons_induction with
  | empty => ext : 1; exact TensorProduct.map_zero_right _
  | cons i S hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons, ← ih]
    exact ModuleCat.hom_ext (TensorProduct.map_add_right _ _ _)

/-- Tensoring a sum of two morphisms on the left. -/
theorem tensorModulesMap_add_left {M M' : ModuleCat.{u} R} {N N' : ModuleCat.{w} R}
    (f f' : M ⟶ M') (g : N ⟶ N') :
    tensorModulesMap R (f + f') g = tensorModulesMap R f g + tensorModulesMap R f' g :=
  ModuleCat.hom_ext (TensorProduct.map_add_left _ _ _)

/-- Tensoring a sum of two morphisms on the right. -/
theorem tensorModulesMap_add_right {M M' : ModuleCat.{u} R} {N N' : ModuleCat.{w} R}
    (f : M ⟶ M') (g g' : N ⟶ N') :
    tensorModulesMap R f (g + g') = tensorModulesMap R f g + tensorModulesMap R f g' :=
  ModuleCat.hom_ext (TensorProduct.map_add_right _ _ _)

/-- Tensoring an integer multiple of a morphism on the left. -/
theorem tensorModulesMap_zsmul_left {M M' : ModuleCat.{u} R} {N N' : ModuleCat.{w} R}
    (z : ℤ) (f : M ⟶ M') (g : N ⟶ N') :
    tensorModulesMap R (z • f) g = z • tensorModulesMap R f g := by
  let L : (M ⟶ M') →+
      (((tensorModules R).obj M).obj N ⟶ ((tensorModules R).obj M').obj N') :=
    { toFun := fun f => tensorModulesMap R f g
      map_zero' := ModuleCat.hom_ext (TensorProduct.map_zero_left _)
      map_add' := fun _ _ => ModuleCat.hom_ext (TensorProduct.map_add_left _ _ _) }
  exact L.map_zsmul z f

/-- Tensoring an integer multiple of a morphism on the right. -/
theorem tensorModulesMap_zsmul_right {M M' : ModuleCat.{u} R} {N N' : ModuleCat.{w} R}
    (z : ℤ) (f : M ⟶ M') (g : N ⟶ N') :
    tensorModulesMap R f (z • g) = z • tensorModulesMap R f g := by
  let L : (N ⟶ N') →+
      (((tensorModules R).obj M).obj N ⟶ ((tensorModules R).obj M').obj N') :=
    { toFun := fun g => tensorModulesMap R f g
      map_zero' := ModuleCat.hom_ext (TensorProduct.map_zero_right _)
      map_add' := fun _ _ => ModuleCat.hom_ext (TensorProduct.map_add_right _ _ _) }
  exact L.map_zsmul z g

/-- Reassociated form of `tensorModulesMap_comp`. -/
theorem tensorModulesMap_comp_assoc {M M' M'' : ModuleCat.{u} R} {N N' N'' : ModuleCat.{w} R}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'')
    {Z : ModuleCat.{max u w} R} (h : ((tensorModules R).obj M'').obj N'' ⟶ Z) :
    tensorModulesMap R f g ≫ tensorModulesMap R f' g' ≫ h =
      tensorModulesMap R (f ≫ f') (g ≫ g') ≫ h := by
  rw [← Category.assoc, tensorModulesMap_comp]

end Tensor

section TensorComplexes

variable (R : Type uR) [CommRing R]

/-- **The differential of the total tensor product of two complexes of `R`-modules on a
homogeneous summand**: the differential of the first factor plus, with the sign `(-1)^i`, the
differential of the second. -/
theorem tensorModules_ι_d (K L : CochainComplex (ModuleCat.{u} R) ℤ) (i j n : ℤ)
    (h : i + j = n) :
    HomologicalComplex.ιMapBifunctor K L (tensorModules R) (up ℤ) i j n h ≫
        (HomologicalComplex.mapBifunctor K L (tensorModules R) (up ℤ)).d n (n + 1) =
      tensorModulesMap R (K.d i (i + 1)) (𝟙 _) ≫
          HomologicalComplex.ιMapBifunctor K L (tensorModules R) (up ℤ) (i + 1) j (n + 1)
            (by (try dsimp); omega) +
        i.negOnePow • (tensorModulesMap R (𝟙 _) (L.d j (j + 1)) ≫
          HomologicalComplex.ιMapBifunctor K L (tensorModules R) (up ℤ) i (j + 1) (n + 1)
            (by (try dsimp); omega)) :=
  HomologicalComplex₂.ιTotal_d_up_ℤ _ i j n h

end TensorComplexes

/-! ### The front and back faces -/

/-- The front face: the first `r + 1` of `p + 1` vertices. -/
def frontIdx (r p : ℕ) (h : r ≤ p) : Fin (r + 1) → Fin (p + 1) := fun i => ⟨i.val, by omega⟩

/-- The back face: the `s + 1` vertices of `p + 1` starting at the vertex `r`. -/
def backIdx (r s p : ℕ) (h : r + s ≤ p) : Fin (s + 1) → Fin (p + 1) :=
  fun i => ⟨r + i.val, by omega⟩

/-- The front face sends the vertex `i` to the vertex `i`. -/
@[simp]
theorem frontIdx_val (r p : ℕ) (h : r ≤ p) (i : Fin (r + 1)) :
    (frontIdx r p h i).val = i.val := rfl

/-- The back face sends the vertex `i` to the vertex `r + i`. -/
@[simp]
theorem backIdx_val (r s p : ℕ) (h : r + s ≤ p) (i : Fin (s + 1)) :
    (backIdx r s p h i).val = r + i.val := rfl

/-- The underlying natural number of `Fin.succAbove`: inserting a gap at `p` leaves the
vertices below `p` alone and shifts the others up by one. -/
theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    (p.succAbove i).val = if i.val < p.val then i.val else i.val + 1 := by
  split_ifs with h
  · rw [Fin.succAbove_of_castSucc_lt p i (by simpa [Fin.lt_def] using h)]
    rfl
  · rw [Fin.succAbove_of_le_castSucc p i
      (by simpa [Fin.le_def] using (show p.val ≤ i.val by omega))]
    rfl

/-- The index set of the homogeneous summands of total degree `n`: a Čech degree together with
a coefficient degree summing to `n`. -/
abbrev totalCechIndex (n : ℤ) := {pa : ℕ × ℤ // (pa.1 : ℤ) + pa.2 = n}

/-! ### The Čech cochains and their restrictions -/

section Cech

variable {C : Type uC} [Category.{vC} C] [HasFiniteProducts C]
  {ι : Type w} [UnivLE.{w, u}] (W : ι → C) (R : Type uR) [CommRing R]

/-- The Čech `p`-cochains of a presheaf of `R`-modules for the family `W`. -/
noncomputable abbrev cechCochains (P : PresheafModules.{u} C R) (p : ℕ) : ModuleCat.{u} R :=
  ((cechComplexFunctor W).obj P).X p

/-- The Čech differential from degree `p` to degree `p + 1`. -/
noncomputable abbrev cechD (P : PresheafModules.{u} C R) (p : ℕ) :
    cechCochains W R P p ⟶ cechCochains W R P (p + 1) :=
  ((cechComplexFunctor W).obj P).d p (p + 1)

/-- Restrict a Čech cochain of degree `p` along a map `θ` of vertex sets, landing in the
sections over the formal intersection selected by `t`. -/
noncomputable abbrev cechFaceRestriction (P : PresheafModules.{u} C R) {p q : ℕ}
    (θ : Fin (p + 1) → Fin (q + 1)) (t : Fin (q + 1) → ι) :
    cechCochains W R P p ⟶ P.obj (op (inter W t)) :=
  π W P p (t ∘ θ) ≫ P.map (interMap W t θ).op

/-- Restricting along `θ` and then along `φ` is restricting along `φ ∘ θ`. -/
theorem cechFaceRestriction_comp (P : PresheafModules.{u} C R) {p q k : ℕ}
    (θ : Fin (p + 1) → Fin (q + 1)) (φ : Fin (q + 1) → Fin (k + 1)) (t : Fin (k + 1) → ι) :
    cechFaceRestriction W R P θ (t ∘ φ) ≫ P.map (interMap W t φ).op =
      cechFaceRestriction W R P (φ ∘ θ) t := by
  dsimp only [cechFaceRestriction]
  rw [Category.assoc, ← Functor.map_comp, ← op_comp, ← interMap_comp]
  rfl

/-- The map on Čech cochains induced by a morphism of coefficient presheaves. -/
noncomputable abbrev cechCochainsMap {P Q : PresheafModules.{u} C R} (f : P ⟶ Q) (p : ℕ) :
    cechCochains W R P p ⟶ cechCochains W R Q p :=
  ((cechComplexFunctor W).map f).f p

/-- A morphism of coefficient presheaves acts componentwise on Čech cochains. -/
@[reassoc (attr := simp)]
theorem cechCochainsMap_comp_π {P Q : PresheafModules.{u} C R} (f : P ⟶ Q) (p : ℕ)
    (t : Fin (p + 1) → ι) :
    cechCochainsMap W R f p ≫ π W Q p t = π W P p t ≫ f.app (op (inter W t)) :=
  limMap_π _ _

/-- The Čech complex functor on presheaves of `R`-modules preserves zero morphisms. -/
instance preservesZeroMorphisms_cechComplexFunctor :
    (CategoryTheory.cechComplexFunctor (A := ModuleCat.{u} R) W).PreservesZeroMorphisms where
  map_zero P Q := HomologicalComplex.hom_ext _ _ fun n =>
    hom_ext W Q fun t => (cechCochainsMap_comp_π W R (0 : P ⟶ Q) n t).trans (by simp)

/-- Čech cochains of a composite. -/
@[reassoc]
theorem cechCochainsMap_comp {P Q T : PresheafModules.{u} C R} (f : P ⟶ Q) (g : Q ⟶ T) (p : ℕ) :
    cechCochainsMap W R (f ≫ g) p = cechCochainsMap W R f p ≫ cechCochainsMap W R g p :=
  congrArg (fun φ => HomologicalComplex.Hom.f φ p)
    ((CategoryTheory.cechComplexFunctor W).map_comp f g)

/-- Čech cochains of the identity. -/
theorem cechCochainsMap_id (P : PresheafModules.{u} C R) (p : ℕ) :
    cechCochainsMap W R (𝟙 P) p = 𝟙 _ :=
  congrArg (fun φ => HomologicalComplex.Hom.f φ p)
    ((CategoryTheory.cechComplexFunctor W).map_id P)

/-- Čech cochains of a sum. -/
theorem cechCochainsMap_add {P Q : PresheafModules.{u} C R} (f g : P ⟶ Q) (p : ℕ) :
    cechCochainsMap W R (f + g) p = cechCochainsMap W R f p + cechCochainsMap W R g p := by
  refine hom_ext W Q fun t => ?_
  simp only [cechCochainsMap_comp_π, Preadditive.add_comp]
  change _ ≫ (f.app _ + g.app _) = _
  rw [Preadditive.comp_add]

/-- Čech cochains of an integer multiple. -/
theorem cechCochainsMap_zsmul {P Q : PresheafModules.{u} C R} (f : P ⟶ Q) (p : ℕ) (z : ℤ) :
    cechCochainsMap W R (z • f) p = z • cechCochainsMap W R f p := by
  refine hom_ext W Q fun t => ?_
  simp [cechCochainsMap_comp_π]

/-- Čech cochains commute with the differential. -/
@[reassoc]
theorem cechCochainsMap_d {P Q : PresheafModules.{u} C R} (f : P ⟶ Q) (p : ℕ) :
    cechCochainsMap W R f p ≫ cechD W R Q p = cechD W R P p ≫ cechCochainsMap W R f (p + 1) :=
  ((CategoryTheory.cechComplexFunctor W).map f).comm p (p + 1)

/-- Restriction is natural in the coefficient presheaf. -/
theorem cechFaceRestriction_naturality {P Q : PresheafModules.{u} C R} (f : P ⟶ Q) {p q : ℕ}
    (θ : Fin (p + 1) → Fin (q + 1)) (t : Fin (q + 1) → ι) :
    cechFaceRestriction W R P θ t ≫ f.app (op (inter W t)) =
      cechCochainsMap W R f p ≫ cechFaceRestriction W R Q θ t := by
  dsimp only [cechFaceRestriction]
  rw [Category.assoc, f.naturality, ← Category.assoc, ← cechCochainsMap_comp_π, Category.assoc]

/-- **The Čech differential, componentwise**, in terms of the face restrictions. -/
theorem cechD_comp_π (P : PresheafModules.{u} C R) (p : ℕ) (y : Fin (p + 2) → ι) :
    cechD W R P p ≫ π W P (p + 1) y =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • cechFaceRestriction W R P i.succAbove y :=
  d_comp_π W P p y

/-- **The Čech differential followed by a face restriction** is the alternating sum of the
restrictions along the composites with the face maps. -/
theorem cechD_comp_cechFaceRestriction (P : PresheafModules.{u} C R) (p : ℕ) {q : ℕ}
    (θ : Fin (p + 2) → Fin (q + 1)) (t : Fin (q + 1) → ι) :
    cechD W R P p ≫ cechFaceRestriction W R P θ t =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        cechFaceRestriction W R P (θ ∘ i.succAbove) t := by
  dsimp only [cechFaceRestriction]
  rw [← Category.assoc, cechD_comp_π, Preadditive.sum_comp]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Preadditive.zsmul_comp, cechFaceRestriction_comp]

/-! ### The Alexander--Whitney map -/

variable {P Q T : PresheafModules.{u} C R}

/-- **One homogeneous term of the Alexander--Whitney map**: restrict the two Čech cochains
along the reindexings `θ₁` and `θ₂` and pair the restrictions with `μ`. -/
noncomputable def awTerm (μ : Pairing.{u} R P Q T) {r s q : ℕ}
    (θ₁ : Fin (r + 1) → Fin (q + 1)) (θ₂ : Fin (s + 1) → Fin (q + 1)) (t : Fin (q + 1) → ι) :
    ((tensorModules R).obj (cechCochains W R P r)).obj (cechCochains W R Q s) ⟶
      T.obj (op (inter W t)) :=
  tensorModulesMap R (cechFaceRestriction W R P θ₁ t) (cechFaceRestriction W R Q θ₂ t) ≫
    μ.app (op (inter W t))

/-- A homogeneous term depends only on the two reindexings. -/
theorem awTerm_congr (μ : Pairing.{u} R P Q T) {r s q : ℕ}
    {θ₁ θ₁' : Fin (r + 1) → Fin (q + 1)} {θ₂ θ₂' : Fin (s + 1) → Fin (q + 1)}
    (t : Fin (q + 1) → ι) (h₁ : θ₁ = θ₁') (h₂ : θ₂ = θ₂') :
    awTerm W R μ θ₁ θ₂ t = awTerm W R μ θ₁' θ₂' t := by
  rw [h₁, h₂]

/-- A homogeneous term is restricted by composing both reindexings with `θ`. -/
theorem awTerm_comp_map (μ : Pairing.{u} R P Q T) {r s q k : ℕ}
    (θ₁ : Fin (r + 1) → Fin (q + 1)) (θ₂ : Fin (s + 1) → Fin (q + 1))
    (θ : Fin (q + 1) → Fin (k + 1)) (t : Fin (k + 1) → ι) :
    awTerm W R μ θ₁ θ₂ (t ∘ θ) ≫ T.map (interMap W t θ).op =
      awTerm W R μ (θ ∘ θ₁) (θ ∘ θ₂) t := by
  have hnat := μ.naturality (interMap W t θ).op
  dsimp only [awTerm]
  rw [Category.assoc, ← hnat, ← Category.assoc]
  congr 1
  rw [tensorPresheafModules_map_app, tensorModulesMap_comp]
  congr 1 <;> exact cechFaceRestriction_comp W R _ _ θ t

/-- **The Čech differential on the front factor of a homogeneous term.** -/
theorem awTerm_d_left (μ : Pairing.{u} R P Q T) {r s q : ℕ}
    (θ₁ : Fin (r + 2) → Fin (q + 1)) (θ₂ : Fin (s + 1) → Fin (q + 1)) (t : Fin (q + 1) → ι) :
    tensorModulesMap R (cechD W R P r) (𝟙 (cechCochains W R Q s)) ≫ awTerm W R μ θ₁ θ₂ t =
      ∑ i : Fin (r + 2), (-1 : ℤ) ^ (i : ℕ) • awTerm W R μ (θ₁ ∘ i.succAbove) θ₂ t := by
  dsimp only [awTerm]
  rw [← Category.assoc, tensorModulesMap_comp, Category.id_comp,
    cechD_comp_cechFaceRestriction, tensorModulesMap_sum_left, Preadditive.sum_comp]
  exact Finset.sum_congr rfl fun i _ => by
    rw [tensorModulesMap_zsmul_left, Preadditive.zsmul_comp]

/-- **The Čech differential on the back factor of a homogeneous term.** -/
theorem awTerm_d_right (μ : Pairing.{u} R P Q T) {r s q : ℕ}
    (θ₁ : Fin (r + 1) → Fin (q + 1)) (θ₂ : Fin (s + 2) → Fin (q + 1)) (t : Fin (q + 1) → ι) :
    tensorModulesMap R (𝟙 (cechCochains W R P r)) (cechD W R Q s) ≫ awTerm W R μ θ₁ θ₂ t =
      ∑ i : Fin (s + 2), (-1 : ℤ) ^ (i : ℕ) • awTerm W R μ θ₁ (θ₂ ∘ i.succAbove) t := by
  dsimp only [awTerm]
  rw [← Category.assoc, tensorModulesMap_comp, Category.id_comp,
    cechD_comp_cechFaceRestriction, tensorModulesMap_sum_right, Preadditive.sum_comp]
  exact Finset.sum_congr rfl fun i _ => by
    rw [tensorModulesMap_zsmul_right, Preadditive.zsmul_comp]

/-- **The unsigned Alexander--Whitney product of Čech cochains** relative to a pairing `μ` of
the coefficient presheaves: restrict to the front `r + 1` vertices and the back `s + 1`
vertices, and pair the two restrictions; the target Čech degree is a variable `p` with
`r + s = p`. -/
noncomputable def cechAlexanderWhitneyTo (μ : Pairing.{u} R P Q T) (r s p : ℕ)
    (h : r + s = p) :
    ((tensorModules R).obj (cechCochains W R P r)).obj (cechCochains W R Q s) ⟶
      cechCochains W R T p :=
  lift W T fun t : Fin (p + 1) → ι =>
    awTerm W R μ (frontIdx r p (by omega)) (backIdx r s p (by omega)) t

/-- **The unsigned Alexander--Whitney product of Čech cochains**, in Čech degree `r + s`. -/
noncomputable def cechAlexanderWhitney (μ : Pairing.{u} R P Q T) (r s : ℕ) :
    ((tensorModules R).obj (cechCochains W R P r)).obj (cechCochains W R Q s) ⟶
      cechCochains W R T (r + s) :=
  cechAlexanderWhitneyTo W R μ r s (r + s) rfl

/-- The component of the Alexander--Whitney map at the formal intersection selected by `t`
pairs the restrictions of the two cochains to the front and back faces. -/
@[reassoc]
theorem cechAlexanderWhitneyTo_comp_π (μ : Pairing.{u} R P Q T) (r s p : ℕ) (h : r + s = p)
    (t : Fin (p + 1) → ι) :
    cechAlexanderWhitneyTo W R μ r s p h ≫ π W T p t =
      awTerm W R μ (frontIdx r p (by omega)) (backIdx r s p (by omega)) t :=
  lift_comp_π W T _ t

/-- The component of the Alexander--Whitney map in Čech degree `r + s` at the formal
intersection selected by `t` pairs the restrictions to the front and back faces. -/
@[reassoc]
theorem cechAlexanderWhitney_comp_π (μ : Pairing.{u} R P Q T) (r s : ℕ)
    (t : Fin (r + s + 1) → ι) :
    cechAlexanderWhitney W R μ r s ≫ π W T (r + s) t =
      awTerm W R μ (frontIdx r (r + s) (by omega)) (backIdx r s (r + s) (by omega)) t :=
  cechAlexanderWhitneyTo_comp_π W R μ r s (r + s) rfl t

/-- The shifted Alexander--Whitney map is the unshifted one followed by the identification of
the two Čech degrees. -/
theorem cechAlexanderWhitneyTo_eq (μ : Pairing.{u} R P Q T) (r s p : ℕ) (h : r + s = p) :
    cechAlexanderWhitneyTo W R μ r s p h =
      cechAlexanderWhitney W R μ r s ≫ eqToHom (congrArg (cechCochains W R T) h) := by
  subst p
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- The Alexander--Whitney map followed by a face restriction pairs the restrictions along the
front and back faces reindexed by `θ`. -/
theorem cechAlexanderWhitney_comp_cechFaceRestriction (μ : Pairing.{u} R P Q T) (r s : ℕ)
    {q : ℕ} (θ : Fin (r + s + 1) → Fin (q + 1)) (t : Fin (q + 1) → ι) :
    cechAlexanderWhitney W R μ r s ≫ cechFaceRestriction W R T θ t =
      awTerm W R μ (θ ∘ frontIdx r (r + s) (by omega))
        (θ ∘ backIdx r s (r + s) (by omega)) t := by
  dsimp only [cechFaceRestriction]
  rw [← Category.assoc, cechAlexanderWhitney_comp_π, awTerm_comp_map]

/-- **The Leibniz rule for the Alexander--Whitney map.**  Composing with the Čech differential
of the target is the Čech differential on the front factor plus, with the Koszul sign `(-1)^r`,
the Čech differential on the back factor. -/
theorem cechAlexanderWhitney_d (μ : Pairing.{u} R P Q T) (r s : ℕ) :
    cechAlexanderWhitney W R μ r s ≫ cechD W R T (r + s) =
      tensorModulesMap R (cechD W R P r) (𝟙 _) ≫
        cechAlexanderWhitneyTo W R μ (r + 1) s (r + s + 1) (by omega) +
      (-1 : ℤ) ^ r • (tensorModulesMap R (𝟙 _) (cechD W R Q s) ≫
        cechAlexanderWhitneyTo W R μ r (s + 1) (r + s + 1) (by omega)) := by
  refine hom_ext W T (n := r + s + 1) fun t => ?_
  rw [Category.assoc, cechD_comp_π]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul,
    cechAlexanderWhitney_comp_cechFaceRestriction]
  rw [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc, Category.assoc,
    cechAlexanderWhitneyTo_comp_π, cechAlexanderWhitneyTo_comp_π, awTerm_d_left, awTerm_d_right]
  apply sum_front_back r s
  · intro i
    refine congrArg (fun z => ((-1 : ℤ) ^ (i : ℕ)) • z) (awTerm_congr W R μ t ?_ ?_)
    · funext k
      apply Fin.ext
      simp only [Function.comp_apply, frontIdx, val_succAbove, Fin.val_castSucc, Fin.val_mk]
    · funext k
      apply Fin.ext
      simp only [Function.comp_apply, backIdx, val_succAbove, Fin.val_mk]
      split_ifs <;> omega
  · intro i
    have hsign : ((-1 : ℤ) ^ r) * ((-1 : ℤ) ^ ((i.succ : Fin (s + 2)) : ℕ)) =
        (-1 : ℤ) ^ (r + 1 + (i : ℕ)) := by
      rw [← pow_add, Fin.val_succ]
      ring
    rw [smul_smul, hsign]
    refine congrArg (fun z => ((-1 : ℤ) ^ (r + 1 + (i : ℕ))) • z) (awTerm_congr W R μ t ?_ ?_)
    · funext k
      apply Fin.ext
      simp only [Function.comp_apply, frontIdx, val_succAbove, Fin.val_mk]
      split_ifs <;> omega
    · funext k
      apply Fin.ext
      simp only [Function.comp_apply, backIdx, val_succAbove, Fin.val_succ, Fin.val_mk]
      split_ifs <;> omega
  · have key : awTerm W R μ (frontIdx (r + 1) (r + s + 1) (by omega) ∘
          (Fin.last (r + 1)).succAbove) (backIdx (r + 1) s (r + s + 1) (by omega)) t =
        awTerm W R μ (frontIdx r (r + s + 1) (by omega))
          (backIdx r (s + 1) (r + s + 1) (by omega) ∘ (0 : Fin (s + 2)).succAbove) t := by
      refine awTerm_congr W R μ t ?_ ?_
      · funext k
        apply Fin.ext
        simp only [Fin.succAbove_last, Function.comp_apply, frontIdx, Fin.val_castSucc,
          Fin.val_mk]
      · funext k
        apply Fin.ext
        simp only [Fin.succAbove_zero, Function.comp_apply, backIdx, Fin.val_succ, Fin.val_mk]
        omega
    rw [Fin.val_last, Fin.val_zero, pow_zero, one_smul, key, pow_succ, mul_smul, neg_one_smul,
      smul_neg, neg_add_cancel]

/-! ### Dependence of the Alexander--Whitney map on the pairing -/

/-- Postcomposing the pairing with a map of target presheaves postcomposes the
Alexander--Whitney map with the induced map of Čech cochains. -/
theorem cechAlexanderWhitneyTo_comp_cechCochainsMap (μ : Pairing.{u} R P Q T)
    {T' : PresheafModules.{u} C R} (φ : T ⟶ T') (r s p : ℕ) (h : r + s = p) :
    cechAlexanderWhitneyTo W R μ r s p h ≫ cechCochainsMap W R φ p =
      cechAlexanderWhitneyTo W R (μ ≫ φ) r s p h := by
  refine hom_ext W T' fun t => ?_
  rw [Category.assoc, cechCochainsMap_comp_π, ← Category.assoc,
    cechAlexanderWhitneyTo_comp_π, cechAlexanderWhitneyTo_comp_π]
  dsimp only [awTerm]
  rw [Category.assoc, NatTrans.comp_app]

/-- The Alexander--Whitney map is additive in the pairing. -/
theorem cechAlexanderWhitneyTo_add (μ ν : Pairing.{u} R P Q T) (r s p : ℕ) (h : r + s = p) :
    cechAlexanderWhitneyTo W R (μ + ν) r s p h =
      cechAlexanderWhitneyTo W R μ r s p h + cechAlexanderWhitneyTo W R ν r s p h := by
  refine hom_ext W T fun t => ?_
  rw [Preadditive.add_comp, cechAlexanderWhitneyTo_comp_π, cechAlexanderWhitneyTo_comp_π,
    cechAlexanderWhitneyTo_comp_π]
  dsimp only [awTerm]
  rw [NatTrans.app_add, Preadditive.comp_add]

/-- The Alexander--Whitney map is `ℤ`-linear in the pairing. -/
theorem cechAlexanderWhitneyTo_zsmul (z : ℤ) (μ : Pairing.{u} R P Q T) (r s p : ℕ)
    (h : r + s = p) :
    cechAlexanderWhitneyTo W R (z • μ) r s p h = z • cechAlexanderWhitneyTo W R μ r s p h := by
  refine hom_ext W T fun t => ?_
  rw [Preadditive.zsmul_comp, cechAlexanderWhitneyTo_comp_π, cechAlexanderWhitneyTo_comp_π]
  dsimp only [awTerm]
  rw [NatTrans.app_zsmul, Preadditive.comp_zsmul]

/-- Precomposing the pairing with a map of the first coefficient presheaf. -/
theorem cechAlexanderWhitneyTo_naturality_left {P P' : PresheafModules.{u} C R}
    (f : P ⟶ P') (μ : Pairing.{u} R P' Q T) (r s p : ℕ) (h : r + s = p) :
    cechAlexanderWhitneyTo W R (((tensorPresheafModules.{u} R).map f).app Q ≫ μ) r s p h =
      tensorModulesMap R (cechCochainsMap W R f r) (𝟙 _) ≫
        cechAlexanderWhitneyTo W R μ r s p h := by
  refine hom_ext W T fun t => ?_
  rw [cechAlexanderWhitneyTo_comp_π, Category.assoc, cechAlexanderWhitneyTo_comp_π]
  dsimp only [awTerm]
  simp only [NatTrans.comp_app, tensorPresheafModules_map_left_app, ← Category.assoc,
    tensorModulesMap_comp, Category.comp_id, Category.id_comp, cechFaceRestriction_naturality]

/-- Precomposing the pairing with a map of the second coefficient presheaf. -/
theorem cechAlexanderWhitneyTo_naturality_right {Q Q' : PresheafModules.{u} C R}
    (g : Q ⟶ Q') (μ : Pairing.{u} R P Q' T) (r s p : ℕ) (h : r + s = p) :
    cechAlexanderWhitneyTo W R (((tensorPresheafModules.{u} R).obj P).map g ≫ μ) r s p h =
      tensorModulesMap R (𝟙 _) (cechCochainsMap W R g s) ≫
        cechAlexanderWhitneyTo W R μ r s p h := by
  refine hom_ext W T fun t => ?_
  rw [cechAlexanderWhitneyTo_comp_π, Category.assoc, cechAlexanderWhitneyTo_comp_π]
  dsimp only [awTerm]
  simp only [NatTrans.comp_app, tensorPresheafModules_map_right_app, ← Category.assoc,
    tensorModulesMap_comp, Category.comp_id, Category.id_comp, cechFaceRestriction_naturality]

/-! ### The total Čech complex -/

/-- The Čech complex of a presheaf of `R`-modules, extended by zero from `ℕ` to `ℤ`. -/
@[implicit_reducible]
noncomputable def cechComplexFunctorInt :
    PresheafModules.{u} C R ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  CategoryTheory.cechComplexFunctor W ⋙ embeddingUpNat.extendFunctor (ModuleCat.{u} R)

/-- The integer-indexed Čech complex functor preserves zero morphisms. -/
instance preservesZeroMorphisms_cechComplexFunctorInt :
    (cechComplexFunctorInt W R).PreservesZeroMorphisms := by
  constructor
  intro P₀ Q₀
  change (embeddingUpNat.extendFunctor (ModuleCat.{u} R)).map
    ((CategoryTheory.cechComplexFunctor W).map 0) = 0
  rw [Functor.map_zero, Functor.map_zero]

/-- **The total Čech complex** of a complex of presheaves of `R`-modules: the totalization of
the Čech bicomplex, whose first degree is the Čech degree. -/
@[implicit_reducible]
noncomputable def totalCechComplexFunctor :
    CochainComplex (PresheafModules.{u} C R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  ((cechComplexFunctorInt W R).mapHomologicalComplex (up ℤ) ⋙
      HomologicalComplex₂.flipFunctor (ModuleCat.{u} R) (up ℤ) (up ℤ)) ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{u} R) (up ℤ) (up ℤ) (up ℤ)

/-- The Čech bicomplex of a complex of coefficient presheaves, with the Čech degree second so
that totalization takes the Čech degree first. -/
noncomputable abbrev totalCechBicomplex (K : CochainComplex (PresheafModules.{u} C R) ℤ) :=
  HomologicalComplex₂.flip
    (((cechComplexFunctorInt W R).mapHomologicalComplex (up ℤ)).obj K)

/-- The degree-`p'` piece of the integer-indexed Čech complex, identified with the Čech
cochains of degree `p`. -/
noncomputable def cechExtendXIso (P : PresheafModules.{u} C R) (p : ℕ) {p' : ℤ}
    (h : (p : ℤ) = p') :
    (((CategoryTheory.cechComplexFunctor W).obj P).extend embeddingUpNat).X p' ≅
      cechCochains W R P p :=
  ((CategoryTheory.cechComplexFunctor W).obj P).extendXIso embeddingUpNat h

/-- The differential of the integer-indexed Čech complex from degree `p` to degree `p + 1` is
the Čech differential, transported along `cechExtendXIso`. -/
theorem cechExtend_d_eq (P : PresheafModules.{u} C R) (p : ℕ) {p' q' : ℤ}
    (hp : (p : ℤ) = p') (hq : ((p + 1 : ℕ) : ℤ) = q') :
    (((CategoryTheory.cechComplexFunctor W).obj P).extend embeddingUpNat).d p' q' =
      (cechExtendXIso W R P p hp).hom ≫ cechD W R P p ≫
        (cechExtendXIso W R P (p + 1) hq).inv :=
  HomologicalComplex.extend_d_eq _ _ hp hq

/-- In degree `p` the map of integer-indexed Čech complexes induced by `φ` is the map of Čech
cochains, transported along `cechExtendXIso`. -/
theorem cechExtendMap_f {P₀ Q₀ : PresheafModules.{u} C R} (φ : P₀ ⟶ Q₀) (p : ℕ) {p' : ℤ}
    (h : (p : ℤ) = p') :
    (HomologicalComplex.extendMap
        ((CategoryTheory.cechComplexFunctor W).map φ) embeddingUpNat).f p' =
      (cechExtendXIso W R P₀ p h).hom ≫ cechCochainsMap W R φ p ≫
        (cechExtendXIso W R Q₀ p h).inv :=
  HomologicalComplex.extendMap_f _ _ h

/-- Inclusion of Čech degree `p` and coefficient degree `a` in the total complex. -/
noncomputable def ιTotalCech (K : CochainComplex (PresheafModules.{u} C R) ℤ) (p : ℕ) (a : ℤ) :
    cechCochains W R (K.X a) p ⟶ ((totalCechComplexFunctor W R).obj K).X (p + a) :=
  (cechExtendXIso W R (K.X a) p rfl).inv ≫
    (totalCechBicomplex W R K).ιTotal (up ℤ) p a (p + a) rfl

/-- The same inclusion, with the total degree given as a separate variable. -/
noncomputable def ιTotalCechTo (K : CochainComplex (PresheafModules.{u} C R) ℤ)
    (p : ℕ) (a n : ℤ) (h : (p : ℤ) + a = n) :
    cechCochains W R (K.X a) p ⟶ ((totalCechComplexFunctor W R).obj K).X n :=
  (cechExtendXIso W R (K.X a) p rfl).inv ≫
    (totalCechBicomplex W R K).ιTotal (up ℤ) p a n h

/-- The inclusion with the total degree `n` as a separate variable is `ιTotalCech` followed by
the identification of the degrees `p + a = n`. -/
theorem ιTotalCechTo_eq (K : CochainComplex (PresheafModules.{u} C R) ℤ)
    (p : ℕ) (a n : ℤ) (h : (p : ℤ) + a = n) :
    ιTotalCechTo W R K p a n h =
      ιTotalCech W R K p a ≫
        eqToHom (congrArg (((totalCechComplexFunctor W R).obj K).X) h) := by
  subst n
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- The differential of the total Čech complex is the differential of the total complex of
`totalCechBicomplex`. -/
theorem totalCechComplex_d (K : CochainComplex (PresheafModules.{u} C R) ℤ) (n m : ℤ) :
    ((totalCechComplexFunctor W R).obj K).d n m =
      ((totalCechBicomplex W R K).total (up ℤ)).d n m :=
  rfl

/-- **The differential of the total Čech complex on a homogeneous summand**: the Čech
differential plus, with the Koszul sign, the coefficient differential. -/
theorem ιTotalCechTo_d (K : CochainComplex (PresheafModules.{u} C R) ℤ)
    (p : ℕ) (a n : ℤ) (h : (p : ℤ) + a = n) :
    ιTotalCechTo W R K p a n h ≫ ((totalCechComplexFunctor W R).obj K).d n (n + 1) =
      cechD W R (K.X a) p ≫ ιTotalCechTo W R K (p + 1) a (n + 1) (by push_cast; omega) +
        (p : ℤ).negOnePow • (cechCochainsMap W R (K.d a (a + 1)) p ≫
          ιTotalCechTo W R K p (a + 1) (n + 1) (by omega)) := by
  unfold ιTotalCechTo
  rw [Category.assoc, totalCechComplex_d, HomologicalComplex₂.ιTotal_d_up_ℤ]
  simp only [Units.smul_def]
  rw [Preadditive.comp_add, Preadditive.comp_zsmul]
  congr 1
  · change _ ≫ (((CategoryTheory.cechComplexFunctor W).obj (K.X a)).extend
      embeddingUpNat).d (p : ℤ) (p + 1) ≫ _ = _
    rw [cechExtend_d_eq W R (K.X a) p rfl (q' := (p : ℤ) + 1) (by push_cast; ring)]
    simp only [Iso.inv_hom_id_assoc, Category.assoc]
    congr 1
  · congr 1
    change _ ≫ (HomologicalComplex.extendMap
        ((CategoryTheory.cechComplexFunctor W).map (K.d a (a + 1))) embeddingUpNat).f (p : ℤ) ≫
      _ = _
    rw [cechExtendMap_f W R (K.d a (a + 1)) p rfl]
    simp only [Iso.inv_hom_id_assoc, Category.assoc]

/-- A morphism out of a degree of the total Čech complex, given on every homogeneous
summand. -/
noncomputable def totalCechDesc (K : CochainComplex (PresheafModules.{u} C R) ℤ) {n : ℤ}
    {A : ModuleCat.{u} R}
    (f : ∀ (p : ℕ) (a : ℤ), (p : ℤ) + a = n → (cechCochains W R (K.X a) p ⟶ A)) :
    ((totalCechComplexFunctor W R).obj K).X n ⟶ A :=
  (totalCechBicomplex W R K).totalDesc fun p a h =>
    match p with
    | .ofNat p => (cechExtendXIso W R (K.X a) p rfl).hom ≫ f p a h
    | .negSucc _ => 0

/-- On the homogeneous summand of bidegree `(p, a)`, `totalCechDesc f` restricts to
`f p a h`. -/
theorem ιTotalCech_desc (K : CochainComplex (PresheafModules.{u} C R) ℤ) {n : ℤ}
    {A : ModuleCat.{u} R}
    (f : ∀ (p : ℕ) (a : ℤ), (p : ℤ) + a = n → (cechCochains W R (K.X a) p ⟶ A))
    (p : ℕ) (a : ℤ) (h : (p : ℤ) + a = n) :
    ιTotalCech W R K p a ≫ eqToHom (congrArg (((totalCechComplexFunctor W R).obj K).X) h) ≫
        totalCechDesc W R K f = f p a h := by
  subst n
  simp only [eqToHom_refl, Category.id_comp, ιTotalCech, totalCechDesc, totalCechBicomplex,
    Category.assoc, HomologicalComplex₂.ι_totalDesc, Iso.inv_hom_id_assoc]

/-- Two morphisms out of a degree of the total Čech complex agree as soon as they agree on
every homogeneous summand. -/
theorem totalCech_hom_ext (K : CochainComplex (PresheafModules.{u} C R) ℤ) {n : ℤ}
    {A : ModuleCat.{u} R} {f g : ((totalCechComplexFunctor W R).obj K).X n ⟶ A}
    (h : ∀ (p : ℕ) (a : ℤ) (hpa : (p : ℤ) + a = n),
      ιTotalCech W R K p a ≫
          eqToHom (congrArg (((totalCechComplexFunctor W R).obj K).X) hpa) ≫ f =
        ιTotalCech W R K p a ≫
          eqToHom (congrArg (((totalCechComplexFunctor W R).obj K).X) hpa) ≫ g) :
    f = g := by
  apply HomologicalComplex₂.total.hom_ext (up ℤ) (K := totalCechBicomplex W R K)
  intro p a hpa
  cases p with
  | ofNat p =>
    subst n
    apply (cancel_epi (cechExtendXIso W R (K.X a) p rfl).inv).mp
    have hh := h p a rfl
    simp only [ιTotalCech, eqToHom_refl, Category.id_comp] at hh
    exact ((Category.assoc _ _ _).symm.trans hh).trans (Category.assoc _ _ _)
  | negSucc p =>
    exact (((CategoryTheory.cechComplexFunctor W).obj (K.X a)).isZero_extend_X
      embeddingUpNat (Int.negSucc p) (by intro i; change (i : ℤ) ≠ _; omega)).eq_of_src _ _

/-- The homogeneous summand of the total Čech complex at a given bidegree. -/
noncomputable abbrev totalCechSummand (K : CochainComplex (PresheafModules.{u} C R) ℤ) (n : ℤ)
    (pa : totalCechIndex n) : ModuleCat.{u} R :=
  cechCochains W R (K.X pa.1.2) pa.1.1

/-- **A degree of the total Čech complex is the coproduct of its homogeneous summands.** -/
noncomputable def totalCechXIsoCoproduct (K : CochainComplex (PresheafModules.{u} C R) ℤ)
    (n : ℤ) :
    ((totalCechComplexFunctor W R).obj K).X n ≅ ∐ (totalCechSummand W R K n) where
  hom := totalCechDesc W R K fun p a h => Sigma.ι (totalCechSummand W R K n) ⟨(p, a), h⟩
  inv := Sigma.desc fun pa => ιTotalCech W R K pa.1.1 pa.1.2 ≫
    eqToHom (congrArg (((totalCechComplexFunctor W R).obj K).X) pa.2)
  hom_inv_id := by
    apply totalCech_hom_ext
    intro p a h
    subst n
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    have hh := ιTotalCech_desc W R K
      (fun q b h => Sigma.ι (totalCechSummand W R K ((p : ℤ) + a)) ⟨(q, b), h⟩) p a rfl
    simp only [eqToHom_refl, Category.id_comp] at hh
    rw [← Category.assoc, hh]
    simp
  inv_hom_id := by
    apply Sigma.hom_ext
    rintro ⟨⟨p, a⟩, h⟩
    simp only [Sigma.ι_comp_desc_assoc, Category.comp_id, Category.assoc]
    exact ιTotalCech_desc W R K _ p a h

/-- Under `totalCechXIsoCoproduct`, the inclusion of the summand of bidegree `(r, a)` is the
coproduct inclusion of that summand. -/
theorem ιTotalCechIsoCoproduct (K : CochainComplex (PresheafModules.{u} C R) ℤ) (r : ℕ)
    (a : ℤ) :
    ιTotalCech W R K r a ≫ (totalCechXIsoCoproduct W R K ((r : ℤ) + a)).hom =
      Sigma.ι (totalCechSummand W R K ((r : ℤ) + a)) ⟨(r, a), by push_cast; rfl⟩ := by
  change ιTotalCech W R K r a ≫ totalCechDesc W R K _ = _
  simpa only [eqToHom_refl, Category.id_comp] using ιTotalCech_desc W R K
    (fun p b h => Sigma.ι (totalCechSummand W R K ((r : ℤ) + a)) ⟨(p, b), h⟩) r a rfl

/-! ### The two sides of the cup product on a homogeneous bidegree -/

/-- The Koszul form of the Leibniz rule for the Alexander--Whitney map, with the sign written
as a `negOnePow`. -/
theorem cechAlexanderWhitney_d' (μ : Pairing.{u} R P Q T) (r s : ℕ) :
    cechAlexanderWhitney W R μ r s ≫ cechD W R T (r + s) =
      tensorModulesMap R (cechD W R P r) (𝟙 _) ≫
        cechAlexanderWhitneyTo W R μ (r + 1) s (r + s + 1) (by omega) +
      ((r : ℤ).negOnePow : ℤ) • (tensorModulesMap R (𝟙 _) (cechD W R Q s) ≫
        cechAlexanderWhitneyTo W R μ r (s + 1) (r + s + 1) (by omega)) := by
  rw [cechAlexanderWhitney_d, Int.coe_negOnePow_natCast]

variable {K L M : CochainComplex (PresheafModules.{u} C R) ℤ}

/-- **The inclusion of a homogeneous bidegree into the source of the cup product**, the tensor
product over `R` of the two total Čech complexes. -/
noncomputable def ιTensorSource (K L : CochainComplex (PresheafModules.{u} C R) ℤ)
    (r s : ℕ) (a b n : ℤ) (h : ((r : ℤ) + a) + ((s : ℤ) + b) = n) :
    ((tensorModules R).obj (cechCochains W R (K.X a) r)).obj (cechCochains W R (L.X b) s) ⟶
      (HomologicalComplex.mapBifunctor ((totalCechComplexFunctor W R).obj K)
        ((totalCechComplexFunctor W R).obj L) (tensorModules R) (up ℤ)).X n :=
  tensorModulesMap R (ιTotalCech W R K r a) (ιTotalCech W R L s b) ≫
    HomologicalComplex.ιMapBifunctor ((totalCechComplexFunctor W R).obj K)
      ((totalCechComplexFunctor W R).obj L) (tensorModules R) (up ℤ)
      ((r : ℤ) + a) ((s : ℤ) + b) n h

/-- With the degrees `i` and `j` of the two factors given as separate variables, the inclusion
of a homogeneous bidegree into the source is `ιTensorSource`. -/
theorem ιTensorSource_eq (K L : CochainComplex (PresheafModules.{u} C R) ℤ) (r s : ℕ)
    (a b i j n : ℤ) (hi : (r : ℤ) + a = i) (hj : (s : ℤ) + b = j) (h : i + j = n) :
    tensorModulesMap R (ιTotalCechTo W R K r a i hi) (ιTotalCechTo W R L s b j hj) ≫
        HomologicalComplex.ιMapBifunctor ((totalCechComplexFunctor W R).obj K)
          ((totalCechComplexFunctor W R).obj L) (tensorModules R) (up ℤ) i j n h =
      ιTensorSource W R K L r s a b n (by omega) := by
  subst i j
  rfl

/-- Precomposing the first factor of `ιTensorSource` with a map into a Čech degree. -/
private theorem tensorModulesMap_comp_ιTotalCechTo_left {X : ModuleCat.{u} R} {r : ℕ} {a : ℤ}
    (f : X ⟶ cechCochains W R (K.X a) r) (s : ℕ) (b i n : ℤ) (hi : (r : ℤ) + a = i)
    (h : i + ((s : ℤ) + b) = n) :
    tensorModulesMap R (f ≫ ιTotalCechTo W R K r a i hi) (ιTotalCech W R L s b) ≫
        HomologicalComplex.ιMapBifunctor ((totalCechComplexFunctor W R).obj K)
          ((totalCechComplexFunctor W R).obj L) (tensorModules R) (up ℤ) i ((s : ℤ) + b) n h =
      tensorModulesMap R f (𝟙 _) ≫ ιTensorSource W R K L r s a b n (by omega) := by
  rw [← Category.id_comp (ιTotalCech W R L s b), ← tensorModulesMap_comp, Category.assoc]
  exact congrArg (tensorModulesMap R f (𝟙 _) ≫ ·)
    (ιTensorSource_eq W R K L r s a b i _ n hi rfl h)

/-- Precomposing the second factor of `ιTensorSource` with a map into a Čech degree. -/
private theorem tensorModulesMap_comp_ιTotalCechTo_right {X : ModuleCat.{u} R} {s : ℕ} {b : ℤ}
    (r : ℕ) (a : ℤ) (g : X ⟶ cechCochains W R (L.X b) s) (j n : ℤ) (hj : (s : ℤ) + b = j)
    (h : ((r : ℤ) + a) + j = n) :
    tensorModulesMap R (ιTotalCech W R K r a) (g ≫ ιTotalCechTo W R L s b j hj) ≫
        HomologicalComplex.ιMapBifunctor ((totalCechComplexFunctor W R).obj K)
          ((totalCechComplexFunctor W R).obj L) (tensorModules R) (up ℤ) ((r : ℤ) + a) j n h =
      tensorModulesMap R (𝟙 _) g ≫ ιTensorSource W R K L r s a b n (by omega) := by
  rw [← Category.id_comp (ιTotalCech W R K r a), ← tensorModulesMap_comp, Category.assoc]
  exact congrArg (tensorModulesMap R (𝟙 _) g ≫ ·)
    (ιTensorSource_eq W R K L r s a b _ j n rfl hj h)

/-- **The differential of the source on a homogeneous bidegree.**  There are four terms: the
Čech differential of each factor and the coefficient differential of each factor, with the
Koszul signs of the two nested totalizations. -/
theorem ιTensorSource_d (K L : CochainComplex (PresheafModules.{u} C R) ℤ) (r s : ℕ)
    (a b n : ℤ) (h : ((r : ℤ) + a) + ((s : ℤ) + b) = n) :
    ιTensorSource W R K L r s a b n h ≫
        (HomologicalComplex.mapBifunctor ((totalCechComplexFunctor W R).obj K)
          ((totalCechComplexFunctor W R).obj L) (tensorModules R) (up ℤ)).d n (n + 1) =
      tensorModulesMap R (cechD W R (K.X a) r) (𝟙 _) ≫
          ιTensorSource W R K L (r + 1) s a b (n + 1) (by push_cast; omega) +
        ((r : ℤ).negOnePow : ℤ) •
          (tensorModulesMap R (cechCochainsMap W R (K.d a (a + 1)) r) (𝟙 _) ≫
            ιTensorSource W R K L r s (a + 1) b (n + 1) (by omega)) +
        (((r : ℤ) + a).negOnePow : ℤ) •
          (tensorModulesMap R (𝟙 _) (cechD W R (L.X b) s) ≫
              ιTensorSource W R K L r (s + 1) a b (n + 1) (by push_cast; omega) +
            ((s : ℤ).negOnePow : ℤ) • (tensorModulesMap R (𝟙 _)
                (cechCochainsMap W R (L.d b (b + 1)) s) ≫
              ιTensorSource W R K L r s a (b + 1) (n + 1) (by omega))) := by
  change (tensorModulesMap R _ _ ≫ _) ≫ _ = _
  rw [Category.assoc, tensorModules_ι_d]
  simp only [Units.smul_def]
  rw [Preadditive.comp_add, Preadditive.comp_zsmul, ← Category.assoc, tensorModulesMap_comp,
    Category.comp_id, ← Category.assoc, tensorModulesMap_comp, Category.comp_id]
  change tensorModulesMap R (ιTotalCechTo W R K r a ((r : ℤ) + a) rfl ≫ _) _ ≫ _ +
    (((r : ℤ) + a).negOnePow : ℤ) •
      (tensorModulesMap R _ (ιTotalCechTo W R L s b ((s : ℤ) + b) rfl ≫ _) ≫ _) = _
  rw [ιTotalCechTo_d, ιTotalCechTo_d]
  simp only [Units.smul_def]
  rw [tensorModulesMap_add_left, tensorModulesMap_add_right, tensorModulesMap_zsmul_left,
    tensorModulesMap_zsmul_right]
  simp only [Preadditive.add_comp, Preadditive.zsmul_comp]
  congr 2
  · exact tensorModulesMap_comp_ιTotalCechTo_left W R _ _ _ _ _ _ _
  · congr 1
    exact tensorModulesMap_comp_ιTotalCechTo_left W R _ _ _ _ _ _ _
  · congr 1
    · exact tensorModulesMap_comp_ιTotalCechTo_right W R _ _ _ _ _ _ _
    · congr 1
      exact tensorModulesMap_comp_ιTotalCechTo_right W R _ _ _ _ _ _ _

/-- **The unsigned image of a homogeneous bidegree in the target of the cup product**: pair the
front and back restrictions with the coefficient pairing and include into the total Čech
complex of `M`. -/
noncomputable def ιPairingTarget (D : ComplexPairing R K L M) (r s : ℕ) (a b n : ℤ)
    (h : ((r : ℤ) + a) + ((s : ℤ) + b) = n) :
    ((tensorModules R).obj (cechCochains W R (K.X a) r)).obj (cechCochains W R (L.X b) s) ⟶
      ((totalCechComplexFunctor W R).obj M).X n :=
  cechAlexanderWhitney W R (D.μ a b (a + b) rfl) r s ≫
    ιTotalCechTo W R M (r + s) (a + b) n (by push_cast; omega)

/-- The Alexander--Whitney map into Čech degree `p` followed by the inclusion into total degree
`n` is `ιPairingTarget`. -/
theorem ιPairingTarget_eq (D : ComplexPairing R K L M) (r s p : ℕ) (a b c n : ℤ)
    (hp : r + s = p) (hc : a + b = c) (hn : (p : ℤ) + c = n) :
    cechAlexanderWhitneyTo W R (D.μ a b c hc) r s p hp ≫ ιTotalCechTo W R M p c n hn =
      ιPairingTarget W R D r s a b n (by omega) := by
  subst p
  subst c
  rfl

/-- **The differential of the target on a homogeneous bidegree.** -/
theorem ιPairingTarget_d (D : ComplexPairing R K L M) (r s : ℕ) (a b n : ℤ)
    (h : ((r : ℤ) + a) + ((s : ℤ) + b) = n) :
    ιPairingTarget W R D r s a b n h ≫ ((totalCechComplexFunctor W R).obj M).d n (n + 1) =
      tensorModulesMap R (cechD W R (K.X a) r) (𝟙 _) ≫
          ιPairingTarget W R D (r + 1) s a b (n + 1) (by push_cast; omega) +
        ((r : ℤ).negOnePow : ℤ) • (tensorModulesMap R (𝟙 _) (cechD W R (L.X b) s) ≫
          ιPairingTarget W R D r (s + 1) a b (n + 1) (by push_cast; omega)) +
        ((((r + s : ℕ)) : ℤ).negOnePow : ℤ) •
          (tensorModulesMap R (cechCochainsMap W R (K.d a (a + 1)) r) (𝟙 _) ≫
              ιPairingTarget W R D r s (a + 1) b (n + 1) (by omega) +
            (a.negOnePow : ℤ) • (tensorModulesMap R (𝟙 _)
                (cechCochainsMap W R (L.d b (b + 1)) s) ≫
              ιPairingTarget W R D r s a (b + 1) (n + 1) (by omega))) := by
  have hA : cechAlexanderWhitney W R (D.μ a b (a + b) rfl) r s ≫
      (cechD W R (M.X (a + b)) (r + s) ≫
        ιTotalCechTo W R M (r + s + 1) (a + b) (n + 1) (by push_cast; omega)) =
      tensorModulesMap R (cechD W R (K.X a) r) (𝟙 _) ≫
          ιPairingTarget W R D (r + 1) s a b (n + 1) (by push_cast; omega) +
        ((r : ℤ).negOnePow : ℤ) • (tensorModulesMap R (𝟙 _) (cechD W R (L.X b) s) ≫
          ιPairingTarget W R D r (s + 1) a b (n + 1) (by push_cast; omega)) := by
    rw [← Category.assoc, cechAlexanderWhitney_d', Preadditive.add_comp,
      Preadditive.zsmul_comp, Category.assoc, Category.assoc,
      ιPairingTarget_eq W R D (r + 1) s (r + s + 1) a b (a + b) (n + 1) (by omega) rfl
        (by push_cast; omega),
      ιPairingTarget_eq W R D r (s + 1) (r + s + 1) a b (a + b) (n + 1) (by omega) rfl
        (by push_cast; omega)]
  have hB : cechAlexanderWhitney W R (D.μ a b (a + b) rfl) r s ≫
      (cechCochainsMap W R (M.d (a + b) (a + b + 1)) (r + s) ≫
        ιTotalCechTo W R M (r + s) (a + b + 1) (n + 1) (by push_cast; omega)) =
      tensorModulesMap R (cechCochainsMap W R (K.d a (a + 1)) r) (𝟙 _) ≫
          ιPairingTarget W R D r s (a + 1) b (n + 1) (by omega) +
        (a.negOnePow : ℤ) • (tensorModulesMap R (𝟙 _)
            (cechCochainsMap W R (L.d b (b + 1)) s) ≫
          ιPairingTarget W R D r s a (b + 1) (n + 1) (by omega)) := by
    rw [← Category.assoc,
      show cechAlexanderWhitney W R (D.μ a b (a + b) rfl) r s =
        cechAlexanderWhitneyTo W R (D.μ a b (a + b) rfl) r s (r + s) rfl from rfl,
      cechAlexanderWhitneyTo_comp_cechCochainsMap, D.μ_d a b (a + b) rfl]
    simp only [Units.smul_def]
    rw [cechAlexanderWhitneyTo_add, cechAlexanderWhitneyTo_zsmul,
      cechAlexanderWhitneyTo_naturality_left, cechAlexanderWhitneyTo_naturality_right,
      Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc, Category.assoc,
      ιPairingTarget_eq W R D r s (r + s) (a + 1) b (a + b + 1) (n + 1) rfl (by omega)
        (by push_cast; omega),
      ιPairingTarget_eq W R D r s (r + s) a (b + 1) (a + b + 1) (n + 1) rfl (by omega)
        (by push_cast; omega)]
  conv_lhs => unfold ιPairingTarget
  rw [Category.assoc, ιTotalCechTo_d]
  simp only [Units.smul_def]
  rw [Preadditive.comp_add, Preadditive.comp_zsmul, hA, hB, Int.coe_negOnePow_natCast,
    Int.coe_negOnePow_natCast]

/-! ### The cup product -/

/-- **The signed Alexander--Whitney map on one pair of homogeneous summands.**  The sign is
`cupProductSign n p r` with `n = r + a` the total degree of the first factor, `p = r + s` the
Čech degree of the target and `r` the Čech degree of the front face. -/
noncomputable def cechCupProductSummand (D : ComplexPairing R K L M) {n₁ n₂ n : ℤ}
    (hn : n₁ + n₂ = n) (α : totalCechIndex n₁) (β : totalCechIndex n₂) :
    ((tensorModules R).obj (totalCechSummand W R K n₁ α)).obj
        (totalCechSummand W R L n₂ β) ⟶
      ((totalCechComplexFunctor W R).obj M).X n :=
  cupProductSign ((α.1.1 : ℤ) + α.1.2) ((α.1.1 : ℤ) + (β.1.1 : ℤ)) (α.1.1 : ℤ) •
    ιPairingTarget W R D α.1.1 β.1.1 α.1.2 β.1.2 n (by
      have h₁ := α.2
      have h₂ := β.2
      omega)

/-- On the summands of bidegrees `(r, a)` and `(s, b)`, the signed Alexander--Whitney map is
`ιPairingTarget` with the sign `(-1)^(a s)`. -/
theorem cechCupProductSummand_eq (D : ComplexPairing R K L M) (r s : ℕ) (a b n : ℤ)
    (h : ((r : ℤ) + a) + ((s : ℤ) + b) = n) :
    cechCupProductSummand W R D h ⟨(r, a), rfl⟩ ⟨(s, b), rfl⟩ =
      (((a * s).negOnePow : ℤ)) • ιPairingTarget W R D r s a b n h := by
  dsimp only [cechCupProductSummand]
  rw [cupProductSign_summand]

/-- The cup product in one total degree. -/
noncomputable def cechCupProductDegree (D : ComplexPairing R K L M) (n : ℤ) :
    (HomologicalComplex.mapBifunctor ((totalCechComplexFunctor W R).obj K)
        ((totalCechComplexFunctor W R).obj L) (tensorModules R) (up ℤ)).X n ⟶
      ((totalCechComplexFunctor W R).obj M).X n :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := (totalCechComplexFunctor W R).obj K)
    (K₂ := (totalCechComplexFunctor W R).obj L)
    (F := tensorModules R) (c := up ℤ) (j := n)
    (A := ((totalCechComplexFunctor W R).obj M).X n)
    fun n₁ n₂ hn =>
      tensorModulesMap R ((totalCechXIsoCoproduct W R K n₁).hom)
          ((totalCechXIsoCoproduct W R L n₂).hom) ≫
        moduleCoprodTensorCoprodDesc (totalCechSummand W R K n₁) (totalCechSummand W R L n₂)
          fun α β => cechCupProductSummand W R D hn α β

/-- The cup product in degree `n` restricts to `cechCupProductSummand` on each homogeneous
bidegree of the source. -/
theorem ιTensorSource_cechCupProductDegree (D : ComplexPairing R K L M) (r s : ℕ)
    (a b n : ℤ) (h : ((r : ℤ) + a) + ((s : ℤ) + b) = n) :
    ιTensorSource W R K L r s a b n h ≫ cechCupProductDegree W R D n =
      cechCupProductSummand W R D h ⟨(r, a), rfl⟩ ⟨(s, b), rfl⟩ := by
  unfold ιTensorSource cechCupProductDegree
  rw [Category.assoc, HomologicalComplex.ι_mapBifunctorDesc, ← Category.assoc,
    tensorModulesMap_comp, ιTotalCechIsoCoproduct, ιTotalCechIsoCoproduct,
    moduleCoprodTensorCoprodDesc_ι]

/-- Two morphisms out of a degree of the source agree as soon as they agree on every
homogeneous bidegree. -/
theorem ιTensorSource_hom_ext (K L : CochainComplex (PresheafModules.{u} C R) ℤ) {n : ℤ}
    {A : ModuleCat.{u} R}
    {f g : (HomologicalComplex.mapBifunctor ((totalCechComplexFunctor W R).obj K)
      ((totalCechComplexFunctor W R).obj L) (tensorModules R) (up ℤ)).X n ⟶ A}
    (h : ∀ (r s : ℕ) (a b : ℤ) (h : ((r : ℤ) + a) + ((s : ℤ) + b) = n),
      ιTensorSource W R K L r s a b n h ≫ f = ιTensorSource W R K L r s a b n h ≫ g) :
    f = g := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro n₁ n₂ hn
  let Mα := totalCechSummand W R K n₁
  let Nβ := totalCechSummand W R L n₂
  let eK := totalCechXIsoCoproduct W R K n₁
  let eL := totalCechXIsoCoproduct W R L n₂
  let tK := ((totalCechComplexFunctor W R).obj K).X n₁
  let tL := ((totalCechComplexFunctor W R).obj L).X n₂
  let eLeft : ((tensorModules R).obj tK).obj tL ≅ ((tensorModules R).obj (∐ Mα)).obj tL :=
    ((tensorModules R).mapIso eK).app tL
  let eRight : ((tensorModules R).obj (∐ Mα)).obj tL ≅
      ((tensorModules R).obj (∐ Mα)).obj (∐ Nβ) :=
    ((tensorModules R).obj (∐ Mα)).mapIso eL
  let e := eLeft ≪≫ eRight
  apply (cancel_epi e.symm.hom).1
  apply moduleCoprodTensorCoprod_hom_ext Mα Nβ
  intro α β
  rcases α with ⟨⟨r, a⟩, hr⟩
  subst n₁
  rcases β with ⟨⟨s, b⟩, hs⟩
  subst n₂
  have hKinv : Sigma.ι Mα ⟨(r, a), by push_cast; rfl⟩ ≫ eK.inv = ιTotalCech W R K r a := by
    rw [← ιTotalCechIsoCoproduct W R K r a, Category.assoc]
    simp [Mα, eK]
  have hLinv : Sigma.ι Nβ ⟨(s, b), by push_cast; rfl⟩ ≫ eL.inv = ιTotalCech W R L s b := by
    rw [← ιTotalCechIsoCoproduct W R L s b, Category.assoc]
    simp [Nβ, eL]
  have hinput : tensorModulesMap R (Sigma.ι Mα ⟨(r, a), by push_cast; rfl⟩)
        (Sigma.ι Nβ ⟨(s, b), by push_cast; rfl⟩) ≫ e.symm.hom =
      tensorModulesMap R (ιTotalCech W R K r a) (ιTotalCech W R L s b) := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change eK.inv.hom ((Sigma.ι Mα ⟨(r, a), by push_cast; rfl⟩).hom x) ⊗ₜ[R]
          eL.inv.hom ((Sigma.ι Nβ ⟨(s, b), by push_cast; rfl⟩).hom y) =
        (ιTotalCech W R K r a).hom x ⊗ₜ[R] (ιTotalCech W R L s b).hom y
    rw [show eK.inv.hom ((Sigma.ι Mα ⟨(r, a), by push_cast; rfl⟩).hom x) =
          (ιTotalCech W R K r a).hom x from congrArg (fun φ => φ.hom x) hKinv,
      show eL.inv.hom ((Sigma.ι Nβ ⟨(s, b), by push_cast; rfl⟩).hom y) =
          (ιTotalCech W R L s b).hom y from congrArg (fun φ => φ.hom y) hLinv]
  simp only [← Category.assoc, hinput]
  exact h r s a b hn

/-- The degreewise cup products commute with the differentials. -/
theorem cechCupProductDegree_comm (D : ComplexPairing R K L M) (n : ℤ) :
    cechCupProductDegree W R D n ≫ ((totalCechComplexFunctor W R).obj M).d n (n + 1) =
      (HomologicalComplex.mapBifunctor ((totalCechComplexFunctor W R).obj K)
          ((totalCechComplexFunctor W R).obj L) (tensorModules R) (up ℤ)).d n (n + 1) ≫
        cechCupProductDegree W R D (n + 1) := by
  apply ιTensorSource_hom_ext W R K L
  intro r s a b h
  rw [← Category.assoc, ιTensorSource_cechCupProductDegree, cechCupProductSummand_eq,
    Preadditive.zsmul_comp, ιPairingTarget_d]
  conv_rhs => rw [← Category.assoc, ιTensorSource_d]
  simp only [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc,
    ιTensorSource_cechCupProductDegree, cechCupProductSummand_eq, Preadditive.comp_zsmul,
    Nat.cast_add, Nat.cast_one]
  exact signed_four_terms (r : ℤ) (s : ℤ) a _ _ _ _

/-- **The Čech cup product** at coefficients in presheaves of modules over a base ring `R`: the
signed Alexander--Whitney map

`Tot(Tot(Č(W,K)) ⊗_R Tot(Č(W,L))) ⟶ Tot(Č(W,M))`

attached to a pairing `D` of the coefficient complexes.  On the summand on which the first
factor has total degree `n`, the target has Čech degree `p`, and the front face has Čech
degree `r`, its coefficient is `cupProductSign n p r = (-1)^((p+r)n+rp+r)`.

The source tensors over `R`; the pairing `D` is where the coefficients are tensored, and it is
not required to be a tensor product over `R`. -/
@[stacks 07MB "at module coefficients over a base ring, relative to a coefficient pairing"]
noncomputable def cechCupProduct (D : ComplexPairing R K L M) :
    HomologicalComplex.mapBifunctor ((totalCechComplexFunctor W R).obj K)
        ((totalCechComplexFunctor W R).obj L) (tensorModules R) (up ℤ) ⟶
      (totalCechComplexFunctor W R).obj M where
  f := cechCupProductDegree W R D
  comm' n n' hnn' := by
    have hnn : n + 1 = n' := by simpa [ComplexShape.up] using hnn'
    subst n'
    exact cechCupProductDegree_comm W R D n

/-- **On homogeneous summands the cup product is the front/back restriction formula** with the
sign `(-1)^((p+r)n+rp+r)`, the restrictions being paired by `D`. -/
@[stacks 07MB "the signed Alexander--Whitney formula at module coefficients over a base ring"]
theorem cechCupProduct_ι (D : ComplexPairing R K L M) (r s : ℕ) (a b : ℤ) :
    tensorModulesMap R (ιTotalCech W R K r a) (ιTotalCech W R L s b) ≫
        HomologicalComplex.ιMapBifunctor ((totalCechComplexFunctor W R).obj K)
          ((totalCechComplexFunctor W R).obj L) (tensorModules R) (up ℤ)
          ((r : ℤ) + a) ((s : ℤ) + b) (((r : ℤ) + a) + ((s : ℤ) + b)) rfl ≫
        (cechCupProduct W R D).f (((r : ℤ) + a) + ((s : ℤ) + b)) =
      cupProductSign ((r : ℤ) + a) ((r : ℤ) + (s : ℤ)) (r : ℤ) •
        (cechAlexanderWhitney W R (D.μ a b (a + b) rfl) r s ≫
          ιTotalCech W R M (r + s) (a + b) ≫
          eqToHom (congrArg (((totalCechComplexFunctor W R).obj M).X) (by push_cast; ring))) := by
  change ιTensorSource W R K L r s a b _ rfl ≫ cechCupProductDegree W R D _ = _
  rw [ιTensorSource_cechCupProductDegree]
  dsimp only [cechCupProductSummand]
  rw [ιPairingTarget, ιTotalCechTo_eq]

end Cech

end Stacks.Cech.LinearCupProduct

end
