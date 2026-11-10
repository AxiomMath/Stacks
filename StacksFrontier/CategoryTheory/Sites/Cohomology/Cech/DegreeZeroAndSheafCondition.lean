module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Whiskering
public import StacksFrontier.CategoryTheory.Sites.Sheafification.CechH0
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
import StacksCore.Tactic.StacksAttribute

/-!
# Degree-zero Čech cohomology and the sheaf condition

Stacks 03AN characterises abelian sheaves by their degree-zero Čech cohomology: an abelian
presheaf on a site is a sheaf exactly when, for every covering family, restriction from
sections over the covered object to the degree-zero Čech cohomology of the family is
bijective.

Degree-zero Čech cohomology is presented here as the additive group of matching families,
`PreZeroHypercover.IsMatching` cut out inside the product of the sections over the members of
the family. That presentation needs no fibre products at all, and the sheaf condition in
that form is Mathlib's; the comparison `cechCohomologyZeroEquiv` identifies it with the
degree-zero homology of the Čech complex of Stacks 03AM whenever the products forming that
complex exist, so the criterion also holds in the Čech-complex formulation.

## Main definitions

* `Stacks.CechSite.cechH0`: degree-zero Čech cohomology, as the additive group of matching
  families.
* `Stacks.CechSite.cechRestriction`: restriction of a section to all members of the family.
* `Stacks.CechSite.cechCohomologyZeroEquiv`: the identification of `cechH0` with the
  degree-zero homology of the Čech complex.
* `Stacks.CechSite.cechRestrictionToCohomology`: restriction, as a map into the degree-zero
  homology of the Čech complex.

## Main results

* `Stacks.CechSite.isSheaf_iff_bijective_cechRestriction`: the degree-zero Čech
  characterisation of abelian sheaves.
* `Stacks.CechSite.cechRestriction_bijective_of_isSheaf`: bijectivity for a single covering
  family of a sheaf, needing only the covering sieve and no ambient fibre products.
* `Stacks.CechSite.cechRestrictionToCohomology_bijective_iff`: the same bijectivity, stated
  for the map into the degree-zero homology of the Čech complex.
* `Stacks.CechSite.cechCohomologyZeroEquiv_apply`: the component formula that pins the
  comparison to the canonical cycles of the Čech complex.

## Implementation notes

Covering families in the criterion are indexed in `Type (max u v)`, which is large enough to
represent every covering sieve on a category `Category.{v, u}`. The comparison with the Čech
complex goes through the kernel of the degree-zero differential: a cochain in degree zero is
a family of sections indexed by singletons, and the singleton iterated fibre product is
canonically isomorphic to the member itself, which is what `singletonProjection` records; the
differential vanishes on such a cochain exactly when the family is matching.

## References

* [Stacks Project, Tag 03AN](https://stacks.math.columbia.edu/tag/03AN)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

universe a w v u

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type u} [Category.{v} C]

/-- The additive subgroup of families of sections satisfying the matching condition. -/
public def matchingFamiliesAddSubgroup {X : C} (E : PreZeroHypercover.{w} X)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) : AddSubgroup (∀ i, F.obj (op (E.X i))) where
  carrier := PreZeroHypercover.IsMatching (F ⋙ forget AddCommGrpCat.{a}) E
  zero_mem' := by
    intro i j T p q hpq
    simp
  add_mem' := by
    intro s t hs ht i j T p q hpq
    have hs' := hs i j T p q hpq
    have ht' := ht i j T p q hpq
    change F.map p.op (s i) = F.map q.op (s j) at hs'
    change F.map p.op (t i) = F.map q.op (t j) at ht'
    change F.map p.op (s i + t i) = F.map q.op (s j + t j)
    rw [map_add, map_add, hs', ht']
  neg_mem' := by
    intro s hs i j T p q hpq
    have hs' := hs i j T p q hpq
    change F.map p.op (s i) = F.map q.op (s j) at hs'
    change F.map p.op (-s i) = F.map q.op (-s j)
    rw [map_neg, map_neg, hs']

/-- Degree-zero Čech cohomology, as the additive group of matching families. -/
public abbrev cechH0 {X : C} (E : PreZeroHypercover.{w} X)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) :=
  matchingFamiliesAddSubgroup E F

section

/-- A product of abelian groups is the group of families: `Pi.π` assembles into an additive
equivalence with the dependent function type. -/
public noncomputable def productAddEquiv {ι : Type w} (G : ι → AddCommGrpCat.{a})
    [HasProduct G] : (∏ᶜ G : AddCommGrpCat.{a}) ≃+ ∀ i, G i := by
  let f : (∏ᶜ G : AddCommGrpCat.{a}) →+ ∀ i, G i :=
    { toFun := fun x i ↦ Pi.π G i x
      map_zero' := funext fun _ ↦ map_zero _
      map_add' := fun _ _ ↦ funext fun _ ↦ map_add _ _ _ }
  refine AddEquiv.ofBijective f ⟨fun x y h ↦ ?_, fun s ↦ ?_⟩
  · change (fun i ↦ Pi.π G i x) = (fun i ↦ Pi.π G i y) at h
    have hh : AddCommGrpCat.ofHom (uliftZMultiplesHom _ x) =
        AddCommGrpCat.ofHom (uliftZMultiplesHom _ y) := by
      refine Pi.hom_ext _ _ fun i ↦ ?_
      ext n
      change Pi.π G i (n.down • x) = Pi.π G i (n.down • y)
      simpa only [map_zsmul] using congrArg (fun z ↦ n.down • z) (congrFun h i)
    have hh' := ConcreteCategory.congr_hom hh (ULift.up (1 : ℤ))
    change (1 : ℤ) • x = (1 : ℤ) • y at hh'
    simpa using hh'
  · refine ⟨Pi.lift (fun i ↦ AddCommGrpCat.ofHom (uliftZMultiplesHom _ (s i)))
      (ULift.up (1 : ℤ)), ?_⟩
    ext i
    change Pi.π G i (Pi.lift (fun j ↦ AddCommGrpCat.ofHom
      (uliftZMultiplesHom _ (s j))) (ULift.up (1 : ℤ))) = _
    rw [← ConcreteCategory.comp_apply, Pi.lift_comp_π]
    change (1 : ℤ) • s i = s i
    exact one_zsmul _

/-- The projection from the iterated fibre product over a one-element family to its single
member. It is an isomorphism, by `singletonProjection_isIso`. -/
public noncomputable abbrev singletonProjection {X : C} (E : PreZeroHypercover.{w} X)
    (i : E.I₀) :
    (∏ᶜ (fun _ : Fin 1 ↦ Over.mk (E.f i)) : Over X) ⟶ Over.mk (E.f i) :=
  Pi.π _ 0

/-- The projection out of a one-fold product is an isomorphism. -/
public lemma singletonProjection_isIso {X : C}
    (E : PreZeroHypercover.{w} X) (i : E.I₀) : IsIso (singletonProjection E i) := by
  change IsIso ((productUniqueIso (fun _ : Fin 1 ↦ Over.mk (E.f i))).hom)
  infer_instance

attribute [local instance] singletonProjection_isIso

/-- Restricting along `g.left` and then `f.left` is the identity when `f ≫ g = 𝟙 _`. -/
private theorem map_left_op_map_left_op_apply {X : C} (F : Cᵒᵖ ⥤ AddCommGrpCat.{a})
    {A B : Over X} (f : A ⟶ B) (g : B ⟶ A) (h : f ≫ g = 𝟙 A) (x : F.obj (op A.left)) :
    F.map f.left.op (F.map g.left.op x) = x := by
  rw [← Functor.map_comp_apply, ← op_comp, ← Over.comp_left, h, Over.id_left, op_id, F.map_id]
  rfl

section Comparison

variable {X : C} (E : PreZeroHypercover.{w} X)
    [HasProducts.{w} AddCommGrpCat.{a}]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{a})

/-- The factor of the degree-`n` term of the Čech complex indexed by `k`: the sections of the
presheaf over the iterated fibre product of the members `E.X (k j)`. -/
public noncomputable abbrev cochainFactor (n : ℕ) (k : Fin (n + 1) → E.I₀) :=
  F.obj (op ((∏ᶜ (fun j ↦ Over.mk (E.f (k j))) : Over X).left))

/-- A morphism of presheaves acts on the Čech complex coordinatewise: the degree-`n` term is a
product of evaluations, and the induced map is the product of the components of the morphism. -/
public lemma cechComplexFunctor_map_f_π {F G : Cᵒᵖ ⥤ AddCommGrpCat.{a}} (φ : F ⟶ G)
    (n : ℕ) (k : Fin (n + 1) → E.I₀) :
    ((cechComplexFunctor E).map φ).f n ≫ Pi.π (cochainFactor E G n) k =
      Pi.π (cochainFactor E F n) k ≫
        φ.app (op ((∏ᶜ (fun j ↦ Over.mk (E.f (k j))) : Over X).left)) := by
  simp only [cechComplexFunctor, cechSimplicialObject, cechFormalCoproduct,
    OrderHom.toFun_eq_coe, FormalCoproduct.cochainComplexFunctor,
    FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp, Functor.comp_obj,
    Functor.whiskeringLeft_obj_obj, Functor.op_obj, Over.forget_obj, Functor.comp_map,
    Functor.op_map, Quiver.Hom.unop_op, Over.forget_map, cochainFactor,
    Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app,
    AlgebraicTopology.alternatingCofaceMapComplex_map,
    AlgebraicTopology.AlternatingCofaceMapComplex.map, Functor.rightOp_obj]
  exact Pi.map_π _ k

/-- A morphism of presheaves acts on the Čech complex coordinatewise, on elements. -/
public lemma cechComplexFunctor_map_f_π_apply {F G : Cᵒᵖ ⥤ AddCommGrpCat.{a}}
    (φ : F ⟶ G) (n : ℕ) (k : Fin (n + 1) → E.I₀) (x : (cechComplex E F).X n) :
    Pi.π (cochainFactor E G n) k (((cechComplexFunctor E).map φ).f n x) =
      φ.app (op ((∏ᶜ (fun j ↦ Over.mk (E.f (k j))) : Over X).left))
        (Pi.π (cochainFactor E F n) k x) :=
  ConcreteCategory.congr_hom (cechComplexFunctor_map_f_π.{a, w, v, u} E φ n k) x

/-- The degree-zero Čech cochain attached to a family of sections of the members of `E`,
restricting the section indexed by `k 0` along the singleton projection. -/
public noncomputable def familyToCochain :
    (∀ i, F.obj (op (E.X i))) →+ (cechComplex E F).X 0 :=
  (productAddEquiv (cochainFactor E F 0)).symm.toAddMonoidHom.comp
    (AddMonoidHom.pi fun k ↦
      (F.map (Pi.π (fun j : Fin 1 ↦ Over.mk (E.f (k j))) 0).left.op).hom.comp
        (Pi.evalAddMonoidHom _ (k 0)))

/-- The components of `familyToCochain`. -/
public lemma familyToCochain_π (s : ∀ i, F.obj (op (E.X i)))
    (k : Fin 1 → E.I₀) :
    Pi.π (cochainFactor E F 0) k (familyToCochain E F s) =
      F.map (Pi.π (fun j : Fin 1 ↦ Over.mk (E.f (k j))) 0).left.op (s (k 0)) :=
  congrFun ((productAddEquiv (cochainFactor E F 0)).apply_symm_apply _) k

/-- The family of sections underlying a degree-zero Čech cochain, obtained by transporting
the component at the singleton `{i}` back along the singleton projection. -/
public noncomputable def cochainToFamily :
    ((cechComplex E F).X 0 : Type a) →+ ∀ i, F.obj (op (E.X i)) :=
  AddMonoidHom.pi fun i ↦
    (F.map (inv (singletonProjection E i)).left.op).hom.comp
      (Pi.π (cochainFactor E F 0) (fun _ ↦ i)).hom

/-- `cochainToFamily` is a left inverse of `familyToCochain`. -/
public lemma cochainToFamily_familyToCochain (s : ∀ i, F.obj (op (E.X i))) :
    cochainToFamily E F (familyToCochain E F s) = s := by
  ext i
  change F.map (inv (singletonProjection E i)).left.op
    (Pi.π (cochainFactor E F 0) (fun _ ↦ i) (familyToCochain E F s)) = _
  rw [familyToCochain_π]
  exact map_left_op_map_left_op_apply F _ _ (IsIso.inv_hom_id _) _

/-- `cochainToFamily` is a right inverse of `familyToCochain`. -/
public lemma familyToCochain_cochainToFamily (x : (cechComplex E F).X 0) :
    familyToCochain E F (cochainToFamily E F x) = x := by
  apply (productAddEquiv (cochainFactor E F 0)).injective
  ext k
  change Pi.π (cochainFactor E F 0) k (familyToCochain E F (cochainToFamily E F x)) = _
  rw [familyToCochain_π]
  obtain ⟨i, rfl⟩ : ∃ i, k = fun _ ↦ i := ⟨k 0, funext fun j ↦ congrArg k (Fin.eq_zero j)⟩
  exact map_left_op_map_left_op_apply F _ _ (IsIso.hom_inv_id _) _

/-- The alternating-sum formula for the degree-zero Čech differential, evaluated at a pair
of indices. The statement never mentions the Čech complex, only the two `Pi.lift`s that its
differential unfolds to, so every step of its proof stays inside the product
`∏ᶜ cochainFactor E F 0`; `differential_π` then applies it to an actual degree-zero cochain.
Keeping the two apart is what lets the computation be done by `simp` at all: an element of
`(cechComplex E F).X 0` is only definitionally an element of `∏ᶜ cochainFactor E F 0`, and
that definitional unfolding goes through `Limits.FormalCoproduct.evalOp`, which `simp` does
not unfold. -/
public lemma pi_π_alternatingSum_apply (k : Fin 2 → E.I₀)
    (y : (∏ᶜ cochainFactor E F 0 : AddCommGrpCat.{a})) (t : ∀ i, F.obj (op (E.X i)))
    (hy : ∀ l : Fin 1 → E.I₀, Pi.π (cochainFactor E F 0) l y =
      F.map (Pi.π (fun j : Fin 1 ↦ Over.mk (E.f (l j))) 0).left.op (t (l 0))) :
    Pi.π (cochainFactor E F 1) k
      ((Pi.lift (fun l : Fin 2 → E.I₀ ↦
          Pi.π (cochainFactor E F 0) (l ∘ (0 : Fin 2).succAbove) ≫
            F.map (Pi.lift (fun j : Fin 1 ↦
              Pi.π (fun b : Fin 2 ↦ Over.mk (E.f (l b))) ((0 : Fin 2).succAbove j))).left.op) -
        Pi.lift (fun l : Fin 2 → E.I₀ ↦
          Pi.π (cochainFactor E F 0) (l ∘ (1 : Fin 2).succAbove) ≫
            F.map (Pi.lift (fun j : Fin 1 ↦
              Pi.π (fun b : Fin 2 ↦ Over.mk (E.f (l b))) ((1 : Fin 2).succAbove j))).left.op))
        y) =
      F.map (Pi.π (fun j : Fin 2 ↦ Over.mk (E.f (k j))) 1).left.op (t (k 1)) -
        F.map (Pi.π (fun j : Fin 2 ↦ Over.mk (E.f (k j))) 0).left.op (t (k 0)) := by
  simp only [AddCommGrpCat.hom_sub, AddMonoidHom.sub_apply, map_sub,
    ← ConcreteCategory.comp_apply, Pi.lift_comp_π]
  simp only [ConcreteCategory.comp_apply, hy]
  simp only [← Functor.map_comp_apply, ← op_comp, ← Over.comp_left]
  simp only [Function.comp_def, Pi.lift_comp_π]
  rfl

/-- The degree-zero Čech differential of the cochain attached to a family of sections, read
off at a pair of indices: it is the difference of the two restrictions of the family to the
corresponding iterated fibre product. -/
public lemma differential_π (s : ∀ i, F.obj (op (E.X i))) (k : Fin 2 → E.I₀) :
    Pi.π (cochainFactor E F 1) k
      ((cechComplex E F).d 0 1 (familyToCochain E F s)) =
    F.map (Pi.π (fun j : Fin 2 ↦ Over.mk (E.f (k j))) 1).left.op (s (k 1)) -
      F.map (Pi.π (fun j : Fin 2 ↦ Over.mk (E.f (k j))) 0).left.op (s (k 0)) := by
  simp only [cechComplex, cechComplexFunctor,
    Functor.comp_obj, FormalCoproduct.cochainComplexFunctor_obj_d,
    CochainComplex.of.d, Nat.reduceAdd, ↓reduceDIte, eqToHom_refl,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul,
    neg_one_zsmul, ← sub_eq_add_neg]
  exact pi_π_alternatingSum_apply E F k (familyToCochain E F s) s (familyToCochain_π E F s)

omit [HasProducts.{w} AddCommGrpCat.{a}] in
/-- A family of sections is matching exactly when the two restrictions to every pairwise
iterated fibre product agree; agreement on those chosen products already implies agreement
over every cone, because such a cone factors through the product. -/
public lemma isMatching_iff_product (s : ∀ i, F.obj (op (E.X i))) :
    PreZeroHypercover.IsMatching (F ⋙ forget AddCommGrpCat.{a}) E s ↔
      ∀ k : Fin 2 → E.I₀,
        F.map (Pi.π (fun j : Fin 2 ↦ Over.mk (E.f (k j))) 1).left.op (s (k 1)) =
          F.map (Pi.π (fun j : Fin 2 ↦ Over.mk (E.f (k j))) 0).left.op (s (k 0)) := by
  refine ⟨fun h k ↦ h _ _ _ _ _ ((Over.w _).trans (Over.w _).symm),
    fun h i j T p q hpq ↦ ?_⟩
  let k : Fin 2 → E.I₀ := ![i, j]
  let l : Over.mk (p ≫ E.f i) ⟶ ∏ᶜ (fun t : Fin 2 ↦ Over.mk (E.f (k t))) :=
    Pi.lift (fun t ↦ by
      refine Fin.cases (Over.homMk p) (fun t ↦ ?_) t
      obtain rfl := Fin.eq_zero t
      exact Over.homMk q hpq.symm)
  have h₀ : l.left ≫ (Pi.π (fun t : Fin 2 ↦ Over.mk (E.f (k t))) 0).left = p :=
    congrArg Over.Hom.left (Pi.lift_comp_π _ 0)
  have h₁ : l.left ≫ (Pi.π (fun t : Fin 2 ↦ Over.mk (E.f (k t))) 1).left = q :=
    congrArg Over.Hom.left (Pi.lift_comp_π _ 1)
  have hh := congrArg (fun z ↦ F.map l.left.op z) (h k)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
    h₁, h₀] at hh
  exact hh.symm

/-- The degree-zero Čech differential kills the cochain of a family of sections exactly when
the family is matching. -/
public lemma differential_eq_zero_iff (s : ∀ i, F.obj (op (E.X i))) :
    (cechComplex E F).d 0 1 (familyToCochain E F s) = 0 ↔
      PreZeroHypercover.IsMatching (F ⋙ forget AddCommGrpCat.{a}) E s := by
  rw [isMatching_iff_product E F]
  refine ⟨fun h k ↦ ?_, fun h ↦ ?_⟩
  · have hh := congrArg (fun x ↦ Pi.π (cochainFactor E F 1) k x) h
    rw [differential_π] at hh
    have hz : Pi.π (cochainFactor E F 1) k (0 : (cechComplex E F).X 1) = 0 :=
      (Pi.π (cochainFactor E F 1) k).hom.map_zero
    rwa [hz, sub_eq_zero] at hh
  · apply (productAddEquiv (cochainFactor E F 1)).injective
    ext k
    change Pi.π (cochainFactor E F 1) k
      ((cechComplex E F).d 0 1 (familyToCochain E F s)) =
        Pi.π (cochainFactor E F 1) k 0
    rw [differential_π, map_zero, sub_eq_zero]
    exact h k

/-- The kernel of the degree-zero Čech differential is the group of matching families. -/
public noncomputable def cyclesEquivMatching :
    AddMonoidHom.ker ((cechComplex E F).d 0 1).hom ≃+ cechH0 E F where
  toFun x := ⟨cochainToFamily E F x, (differential_eq_zero_iff E F _).mp (by
    rw [familyToCochain_cochainToFamily]
    exact x.property)⟩
  invFun s := ⟨familyToCochain E F s, (differential_eq_zero_iff E F _).mpr s.property⟩
  left_inv x := Subtype.ext (familyToCochain_cochainToFamily E F x)
  right_inv s := Subtype.ext (cochainToFamily_familyToCochain E F s)
  map_add' x y := Subtype.ext ((cochainToFamily E F).map_add x y)

end Comparison

/-- The degree-zero homology of a cochain complex of abelian groups indexed by `ℕ` is the
kernel of its first differential. -/
public noncomputable def homologyZeroEquivKernel (K : CochainComplex AddCommGrpCat.{a} ℕ) :
    (K.homology 0 : Type a) ≃+ AddMonoidHom.ker (K.d 0 1).hom :=
  (K.isoHomologyπ₀.symm ≪≫ K.cyclesIsoSc' 0 0 1 (by simp) (by simp) ≪≫
    (K.sc' 0 0 1).abCyclesIso).addCommGroupIsoToAddEquiv

/-- The canonical identification of matching-family degree-zero Čech cohomology with the
degree-zero homology of the Čech complex. -/
public noncomputable def cechCohomologyZeroEquiv {X : C} (E : PreZeroHypercover.{w} X)
    [HasProducts.{w} AddCommGrpCat.{a}]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) :
    (cechCohomology E (A := AddCommGrpCat.{a}) F 0 : Type a) ≃+
      cechH0 E F :=
  (homologyZeroEquivKernel (cechComplex E F)).trans (cyclesEquivMatching E F)

end

/-- The comparison with degree-zero Čech homology evaluates a cycle at the singleton
indexed by `i`, identifying the singleton fibre product with `E.X i`. -/
public theorem cechCohomologyZeroEquiv_apply {X : C} (E : PreZeroHypercover.{w} X)
    [HasProducts.{w} AddCommGrpCat.{a}]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{a})
    (h : (cechCohomology E (A := AddCommGrpCat.{a}) F 0 : Type a))
    (i : E.I₀) :
    (cechCohomologyZeroEquiv E F h : ∀ j, F.obj (op (E.X j))) i =
      F.map ((productUniqueIso (fun _ : Fin 1 ↦ Over.mk (E.f i))).inv.left).op
        (Pi.π (fun k : Fin 1 → E.I₀ ↦
            F.obj (op ((∏ᶜ (fun j : Fin 1 ↦ Over.mk (E.f (k j))) : Over X).left)))
          (fun _ ↦ i)
          (((cechComplex E F).isoHomologyπ₀.inv ≫
              (cechComplex E F).iCycles 0) h)) := by
  have := singletonProjection_isIso E i
  let K := cechComplex E F
  have hcycles (x : (K.sc' 0 0 1).cycles) :
      ((K.sc' 0 0 1).abCyclesIso.hom x).val = (K.sc' 0 0 1).iCycles x := by
    rw [← (K.sc' 0 0 1).abCyclesIso_inv_apply_iCycles]
    simp
  change F.map (inv (singletonProjection E i)).left.op
    (Pi.π (cochainFactor E F 0) (fun _ ↦ i)
      ((homologyZeroEquivKernel K h).val)) = _
  have hc : (homologyZeroEquivKernel K h).val =
      (K.isoHomologyπ₀.inv ≫ K.iCycles 0) h := by
    change ((K.sc' 0 0 1).abCyclesIso.hom
      ((K.cyclesIsoSc' 0 0 1 (by simp) (by simp)).hom
        (K.isoHomologyπ₀.inv h))).val = _
    rw [hcycles, ← ConcreteCategory.comp_apply, K.cyclesIsoSc'_hom_iCycles]
    rfl
  have hi : inv (singletonProjection E i) =
      (productUniqueIso (fun _ : Fin 1 ↦ Over.mk (E.f i))).inv :=
    IsIso.inv_eq_of_hom_inv_id
      (productUniqueIso (fun _ : Fin 1 ↦ Over.mk (E.f i))).hom_inv_id
  rw [hc, hi]

/-- The canonical map from sections on the target of a family to its degree-zero Čech
cohomology, sending a section to all of its restrictions. -/
public def cechRestriction {X : C} (E : PreZeroHypercover.{w} X)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) :
    F.obj (op X) →+ cechH0 E F where
  toFun s := ⟨fun i => F.map (E.f i).op s, by
      change PreZeroHypercover.IsMatching (F ⋙ forget AddCommGrpCat.{a}) E _
      intro i j T p q hpq
      change F.map p.op (F.map (E.f i).op s) = F.map q.op (F.map (E.f j).op s)
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hpq]⟩
  map_zero' := by ext i; simp
  map_add' _ _ := by ext i; simp

/-- The natural map from sections to degree-zero homology of the Čech complex. -/
public noncomputable def cechRestrictionToCohomology {X : C} (E : PreZeroHypercover.{w} X)
    [HasProducts.{w} AddCommGrpCat.{a}]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) :
    F.obj (op X) →+ (cechCohomology E (A := AddCommGrpCat.{a}) F 0 : Type a) :=
  (cechCohomologyZeroEquiv E F).symm.toAddMonoidHom.comp (cechRestriction E F)

/-- Under the canonical comparison, the map to Čech homology is restriction to all
members of the covering family. -/
public theorem cechCohomologyZeroEquiv_comp_cechRestrictionToCohomology
    {X : C} (E : PreZeroHypercover.{w} X)
    [HasProducts.{w} AddCommGrpCat.{a}]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) (s : F.obj (op X)) :
    cechCohomologyZeroEquiv E F (cechRestrictionToCohomology E F s) =
      cechRestriction E F s :=
  (cechCohomologyZeroEquiv E F).apply_symm_apply _

/-- For an individual family whose Čech complex exists, bijectivity into degree-zero
Čech homology is equivalent to bijectivity into matching families. -/
@[stacks 03AN "the Čech-complex formulation"]
public theorem cechRestrictionToCohomology_bijective_iff {X : C}
    (E : PreZeroHypercover.{w} X)
    [HasProducts.{w} AddCommGrpCat.{a}]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) :
    Function.Bijective (cechRestrictionToCohomology E F) ↔
      Function.Bijective (cechRestriction E F) :=
  (cechCohomologyZeroEquiv E F).symm.bijective.of_comp_iff' (cechRestriction E F)

/-- For a sheaf and a single covering family, restriction to degree-zero Čech cohomology
is bijective. This formulation only needs the covering sieve and no pullbacks in the
ambient category. -/
public theorem cechRestriction_bijective_of_isSheaf
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{a})
    (hF : Presheaf.IsSheaf J F) {X : C} (E : PreZeroHypercover.{w} X)
    (hE : E.sieve₀ ∈ J X) : Function.Bijective (cechRestriction E F) :=
  (Presieve.isSheafFor_ofArrows_iff_bijective_toCompatible _ _).1
    (((isSheaf_iff_isSheaf_of_type J (F ⋙ forget AddCommGrpCat.{a})).1
      (GrothendieckTopology.HasSheafCompose.isSheaf F hF)).isSheafFor E.presieve₀ hE)

/-- **Stacks 03AN.** An abelian presheaf is a sheaf if and only if restriction to the
degree-zero Čech cohomology of every covering family is bijective. -/
@[stacks 03AN]
public theorem isSheaf_iff_bijective_cechRestriction
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) :
    Presheaf.IsSheaf J F ↔
      ∀ {X : C} (E : PreZeroHypercover.{max u v} X), E.sieve₀ ∈ J X →
        Function.Bijective (cechRestriction E F) := by
  refine ⟨fun hF _ E hE ↦ cechRestriction_bijective_of_isSheaf J F hF E hE, fun h ↦ ?_⟩
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{a})
  apply (isSheaf_iff_isSheaf_of_type J _).2
  intro X S hS
  have hE : S.arrows.preZeroHypercover.sieve₀ ∈ J X := by
    change Sieve.generate S.arrows.preZeroHypercover.presieve₀ ∈ J X
    simpa using hS
  have h' := (Presieve.isSheafFor_ofArrows_iff_bijective_toCompatible
    (F ⋙ forget AddCommGrpCat.{a}) S.arrows.preZeroHypercover.f).2
    (h S.arrows.preZeroHypercover hE)
  change Presieve.IsSheafFor _ S.arrows.preZeroHypercover.presieve₀ at h'
  simpa using h'

end Stacks.CechSite
