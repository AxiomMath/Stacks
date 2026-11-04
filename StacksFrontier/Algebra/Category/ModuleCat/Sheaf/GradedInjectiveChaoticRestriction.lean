module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedGrothendieck
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedRelativeTensorUnitor

/-!
# Injective graded modules over a preorder with the chaotic topology have surjective restrictions

Let `C` be a preorder with the chaotic topology, `R` a sheaf of rings on it and `A` a sheaf of
graded `R`-algebras. If a right graded `A`-module `I` is an injective object of the category of
right graded `A`-modules, then its restriction maps `I^d(n') ⟶ I^d(n)`, for `n ≤ n'`, are
surjective in every degree `d`. No flatness of `A` over `R` is needed.

The argument extends a homomorphism along a monomorphism of graded modules. For `n : C` and a
degree `d`, let `A_{≤ n}[-d]` be the graded submodule of the shifted regular module `A[-d]` whose
sections over `U` are those of `A[-d]` if `U ≤ n` and zero otherwise; on the chaotic topology it
is a sheaf. For `n ≤ n'` it is a graded submodule of `A_{≤ n'}[-d]`. A section `x` of `I^d` over
`n` defines the homomorphism `A_{≤ n}[-d] ⟶ I`, `a ↦ x|_U · a` over `U ≤ n`, which sends the
unit `1 ∈ A^0(n)` to `x`. By injectivity it extends to `A_{≤ n'}[-d]`, and the image of the unit
over `n'` restricts to `x`. This is the source's lifting along `R[h_n] ⊆ R[h_{n'}]` of the free
modules on the representable presheaves, in the graded form.

## Main definitions

* `SheafOfModules.ChaoticTruncation.sheaf`: the sheaf of modules `M_{≤ n}` whose sections are
  those of `M` over the objects below `n` and zero elsewhere, and
  `SheafOfModules.ChaoticTruncation.graded` the same for a graded module.
* `SheafOfModules.ChaoticTruncation.genModule`: the graded module `A_{≤ n}[-d]`, and
  `SheafOfModules.ChaoticTruncation.genHom` the homomorphism out of it attached to a section.

## Main results

* `SheafOfModules.GradedModule.surjective_map_of_injective`: **the restriction maps of an
  injective right graded module are surjective.**
* `SheafOfModules.DifferentialGradedModule.surjective_map_of_gradedInjective`: the same for a
  graded injective right differential graded module.

## References

* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
* [Stacks Project, Tag 0FSP](https://stacks.math.columbia.edu/tag/0FSP)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe t m u

namespace SheafOfModules

variable {C : Type u} [Preorder C] {R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{t}}

namespace ChaoticTruncation

/-- The sections of `M` over `U` if `U ≤ n`, and zero otherwise. -/
def submodule (n : C) (M : SheafOfModules.{m} R) (U : Cᵒᵖ) :
    _root_.Submodule (R.obj.obj U) (M.val.obj U) where
  carrier := {x | U.unop ≤ n ∨ x = 0}
  add_mem' {x y} hx hy := by
    rcases hx with hx | rfl
    · exact Or.inl hx
    · simpa using hy
  zero_mem' := Or.inr rfl
  smul_mem' r x hx := by
    rcases hx with hx | rfl
    · exact Or.inl hx
    · exact Or.inr (smul_zero r)

/-- Membership in the truncated sections. -/
theorem mem_submodule {n : C} {M : SheafOfModules.{m} R} {U : Cᵒᵖ} {x : M.val.obj U} :
    x ∈ submodule n M U ↔ U.unop ≤ n ∨ x = 0 := Iff.rfl

/-- Over an object not below `n` the truncated sections are zero. -/
theorem submodule_eq_zero {n : C} {M : SheafOfModules.{m} R} {U : Cᵒᵖ}
    (hU : ¬ U.unop ≤ n) (x : submodule n M U) : x = 0 :=
  Subtype.ext ((mem_submodule.1 x.2).resolve_left hU)

/-- The presheaf of modules `M_{≤ n}`: the sections of `M` over the objects below `n`, and zero
elsewhere. -/
def presheaf (n : C) (M : SheafOfModules.{m} R) : PresheafOfModules.{m} R.obj where
  obj U := ModuleCat.of (R.obj.obj U) (submodule n M U)
  map {U V} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.obj.map f).hom).obj
        (ModuleCat.of _ (submodule n M V)))
    { toFun := fun x => ⟨M.val.map f x.1, by
        rcases mem_submodule.1 x.2 with h | h
        · exact Or.inl ((leOfHom f.unop).trans h)
        · exact Or.inr (by rw [h]; exact map_zero _)⟩
      map_add' := fun x y => Subtype.ext (map_add (M.val.map f).hom x.1 y.1)
      map_smul' := fun r x => Subtype.ext (M.val.map_smul f r x.1) }
  map_id U := by
    ext x
    exact Subtype.ext (congrArg (fun g => g x.1)
      (congrArg (fun φ => ConcreteCategory.hom φ) (M.val.presheaf.map_id U)))
  map_comp f g := by
    ext x
    exact Subtype.ext (M.val.map_comp_apply f g x.1)

/-- The restriction maps of `M_{≤ n}` are those of `M`. -/
theorem presheaf_map_val (n : C) (M : SheafOfModules.{m} R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : submodule n M U) : ((presheaf n M).map f x).1 = M.val.map f x.1 := rfl

/-- The sheaf of modules `M_{≤ n}`: on the chaotic topology every presheaf is a sheaf. -/
def sheaf (n : C) (M : SheafOfModules.{m} R) : SheafOfModules.{m} R :=
  ⟨presheaf n M, Presheaf.isSheaf_bot _⟩

/-- The inclusion `M_{≤ n} ⟶ M_{≤ n'}` for `n ≤ n'`. -/
def sheafLE {n n' : C} (h : n ≤ n') (M : SheafOfModules.{m} R) :
    sheaf n M ⟶ sheaf n' M :=
  ⟨{ app U := ModuleCat.ofHom
       { toFun := fun x => ⟨x.1, (mem_submodule.1 x.2).imp (fun hU => hU.trans h) id⟩
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl }
     naturality := fun f => by ext x; rfl }⟩

/-- The inclusion `M_{≤ n} ⟶ M_{≤ n'}` does not change the underlying section. -/
theorem sheafLE_app_val {n n' : C} (h : n ≤ n') (M : SheafOfModules.{m} R) (U : Cᵒᵖ)
    (x : submodule n M U) : ((sheafLE h M).val.app U x).1 = x.1 := rfl

/-- The inclusion `M_{≤ n} ⟶ M_{≤ n'}` is a monomorphism. -/
instance mono_sheafLE {n n' : C} (h : n ≤ n') (M : SheafOfModules.{m} R) :
    Mono (sheafLE h M) :=
  ⟨fun {Z} g₁ g₂ hg => by
    ext U z
    exact Subtype.ext (congrArg (fun φ : Z ⟶ sheaf n' M => (φ.val.app U z).1) hg)⟩

/-- Transport along an equality of degrees does not change the underlying section. -/
theorem cast_val {n : C} (N : ℤ → SheafOfModules.{m} R) {p q : ℤ} (h : p = q) (U : Cᵒᵖ)
    (z : submodule n (N p) U) :
    (castHom (fun k => sheaf n (N k)) h U z).1 = castHom N h U z.1 := by
  subst h
  rfl

/-- Truncated sections in equal degrees with heterogeneously equal underlying sections are
heterogeneously equal. -/
theorem heq_of_val {n : C} {N : ℤ → SheafOfModules.{m} R} {p q : ℤ} (h : p = q) {U : Cᵒᵖ}
    {x : submodule n (N p) U} {y : submodule n (N q) U} (hxy : HEq x.1 y.1) :
    HEq x y := by
  subst h
  exact heq_of_eq (Subtype.ext (eq_of_heq hxy))

variable {A : GradedAlgebra.{t, m} R}

/-- The graded module `N_{≤ n}`: the truncation of every piece, with the action of `N`. -/
def graded (n : C) (N : GradedModule.{t, m, m} A) : GradedModule.{t, m, m} A where
  piece p := sheaf n (N.piece p)
  smul p i U := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun b => ⟨N.smul p i U x.1 b, by
        rcases mem_submodule.1 x.2 with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])⟩)
        (fun b b' => Subtype.ext (map_add (N.smul p i U x.1) b b')))
      (fun x y => AddMonoidHom.ext fun b => Subtype.ext (by
        change N.smul p i U (x.1 + y.1) b = N.smul p i U x.1 b + N.smul p i U y.1 b
        simp))
  smul_smul_left p i U r x b := Subtype.ext (N.smul_smul_left p i U r x.1 b)
  smul_smul_right p i U r x b := Subtype.ext (N.smul_smul_right p i U r x.1 b)
  smul_naturality p i U V f x b := Subtype.ext (N.smul_naturality p i f x.1 b)
  smul_mul p i j U x b c := heq_of_val (N := N.piece) (add_assoc p i j) (N.smul_mul p i j U x.1 b c)
  smul_one p U x := heq_of_val (N := N.piece) (add_zero p) (N.smul_one p U x.1)

/-- Transport along an equality of degrees in a truncation does not change the underlying
section. -/
theorem graded_castHom_val (n : C) (N : GradedModule.{t, m, m} A) {p q : ℤ} (h : p = q)
    (U : Cᵒᵖ) (z : submodule n (N.piece p) U) :
    (castHom (graded n N).piece h U z).1 = castHom N.piece h U z.1 := by
  subst h
  rfl

/-- The action on `N_{≤ n}` is that of `N`. -/
theorem graded_smul_val (n : C) (N : GradedModule.{t, m, m} A) (p i : ℤ) (U : Cᵒᵖ)
    (x : submodule n (N.piece p) U) (b : (A.piece i).val.obj U) :
    ((graded n N).smul p i U x b).1 = N.smul p i U x.1 b := rfl

/-- The inclusion `N_{≤ n} ⟶ N_{≤ n'}` of graded modules for `n ≤ n'`. -/
def gradedLE {n n' : C} (h : n ≤ n') (N : GradedModule.{t, m, m} A) :
    graded n N ⟶ graded n' N where
  app p := sheafLE h (N.piece p)
  map_smul _ _ _ _ _ := rfl

/-- The action of a graded module, transported in the algebra degree. -/
theorem smul_heq_right (N : GradedModule.{t, m, m} A) (p : ℤ) {q q' : ℤ} (h : q = q') (U : Cᵒᵖ)
    (x : (N.piece p).val.obj U) {z : (A.piece q).val.obj U} {z' : (A.piece q').val.obj U}
    (hz : HEq z z') : HEq (N.smul p q U x z) (N.smul p q' U x z') := by
  subst h
  rw [eq_of_heq hz]

/-- The graded module `A_{≤ n}[-d]`: the truncation at `n` of the regular module, shifted so that
its unit sits in degree `d`. -/
abbrev genModule (n : C) (d : ℤ) : GradedModule.{t, m, m} A :=
  (graded n (GradedModule.regularModule A)).shift (-d)

/-- The unit of `A` over `n`, as a section of degree `d` of `A_{≤ n}[-d]`. -/
def gen (n : C) (d : ℤ) : submodule n (A.piece (d + -d)) (op n) :=
  ⟨castHom A.piece (by omega : (0 : ℤ) = d + -d) (op n) (A.one.eval (op n)), Or.inl le_rfl⟩

variable (I : GradedModule.{t, m, m} A) {n : C} {d : ℤ} (x : (I.piece d).val.obj (op n))

/-- The restriction of `x` to an object below `n`. -/
def genRestrict (U : Cᵒᵖ) (h : U.unop ≤ n) : (I.piece d).val.obj U :=
  (I.piece d).val.map (homOfLE h : U.unop ⟶ n).op x

/-- Restricting the restriction of `x` further is restricting `x`. -/
theorem genRestrict_naturality {U V : Cᵒᵖ} (f : U ⟶ V) (hU : U.unop ≤ n) (hV : V.unop ≤ n) :
    (I.piece d).val.map f (genRestrict I x U hU) = genRestrict I x V hV := by
  rw [genRestrict, genRestrict, ← PresheafOfModules.map_comp_apply]
  congr 2

/-- The restriction of `x` to `n` itself is `x`. -/
theorem genRestrict_self : genRestrict I x (op n) le_rfl = x := by
  rw [genRestrict, show (homOfLE (le_refl n)).op = 𝟙 (op n) from
    Quiver.Hom.unop_inj (Subsingleton.elim _ _)]
  exact (I.piece d).val.map_id_apply (op n) x

open Classical in
/-- The component of the homomorphism attached to `x`. -/
def genHomApp (p : ℤ) (U : Cᵒᵖ) :
    submodule n (A.piece (p + -d)) U →ₗ[R.obj.obj U] (I.piece p).val.obj U where
  toFun y := if h : U.unop ≤ n then castHom I.piece (by omega : d + (p + -d) = p) U
      (I.smul d (p + -d) U (genRestrict I x U h) y.1) else 0
  map_add' y y' := by
    split_ifs
    · simp only [Submodule.coe_add, map_add]
    · simp
  map_smul' r y := by
    split_ifs
    · rw [SetLike.val_smul, I.smul_smul_right, castHom_smul, RingHom.id_apply]
    · simp

/-- Over an object below `n` the homomorphism attached to `x` is `a ↦ x|_U · a`. -/
theorem genHomApp_of_le (p : ℤ) {U : Cᵒᵖ} (h : U.unop ≤ n)
    (y : submodule n (A.piece (p + -d)) U) :
    genHomApp I x p U y = castHom I.piece (by omega : d + (p + -d) = p) U
      (I.smul d (p + -d) U (genRestrict I x U h) y.1) :=
  dif_pos h

/-- The components of the homomorphism attached to `x` commute with restriction. -/
theorem genHomApp_naturality (p : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (y : submodule n (A.piece (p + -d)) U) (y' : submodule n (A.piece (p + -d)) V)
    (hy : y'.1 = (A.piece (p + -d)).val.map f y.1) :
    genHomApp I x p V y' = (I.piece p).val.map f (genHomApp I x p U y) := by
  by_cases hU : U.unop ≤ n
  · have hV : V.unop ≤ n := (leOfHom f.unop).trans hU
    rw [genHomApp_of_le I x p hV, genHomApp_of_le I x p hU, castHom_naturality,
      I.smul_naturality, hy, genRestrict_naturality I x f hU hV]
  · obtain rfl := submodule_eq_zero hU y
    obtain rfl : y' = 0 := Subtype.ext (hy.trans (map_zero _))
    rw [map_zero, map_zero, map_zero]
    rfl

/-- The homomorphism attached to `x` sends the generator to `x`. -/
theorem genHomApp_gen : genHomApp I x d (op n) (gen n d) = x := by
  rw [genHomApp_of_le I x d (le_refl n), genRestrict_self]
  apply eq_of_heq
  refine (heq_castHom _ _ _ _).trans ?_
  refine HEq.trans ?_ (I.smul_one d (op n) x)
  exact smul_heq_right I d (by omega) (op n) x (heq_castHom _ _ _ _)

/-- The components of the homomorphism attached to `x` commute with the action of `A`. -/
theorem genHomApp_smul (p i : ℤ) (U : Cᵒᵖ) (y : submodule n (A.piece (p + -d)) U)
    (b : (A.piece i).val.obj U) (z : submodule n (A.piece (p + i + -d)) U)
    (hz : HEq z.1 ((A.mul (p + -d) i).app U y.1 b)) :
    genHomApp I x (p + i) U z = I.smul p i U (genHomApp I x p U y) b := by
  by_cases hU : U.unop ≤ n
  · rw [genHomApp_of_le I x (p + i) hU, genHomApp_of_le I x p hU, Cofree.smul_castHom_left]
    apply eq_of_heq
    refine (heq_castHom _ _ _ _).trans (HEq.trans ?_ (heq_castHom _ _ _ _).symm)
    refine HEq.trans ?_ (I.smul_mul d (p + -d) i U _ y.1 b).symm
    exact smul_heq_right I d (by omega) U _ hz
  · rw [submodule_eq_zero hU z, submodule_eq_zero hU y, map_zero, map_zero, map_zero,
      AddMonoidHom.zero_apply]

/-- The homomorphism `A_{≤ n}[-d] ⟶ I` attached to a section `x` of `I^d` over `n`:
`a ↦ x|_U · a` over `U ≤ n`. -/
def genHom : genModule n d ⟶ I where
  app p := ⟨{ app U := ModuleCat.ofHom (genHomApp I x p U)
              naturality := fun f => by
                ext y
                exact genHomApp_naturality I x p f y _ rfl }⟩
  map_smul p i U y b := genHomApp_smul I x p i U y b _
    ((heq_of_eq (graded_castHom_val n (GradedModule.regularModule A) _ U _)).trans
      (heq_castHom _ _ _ _))

/-- The components of `genHom` are `genHomApp`. -/
theorem genHom_app_apply (p : ℤ) (U : Cᵒᵖ) (y : submodule n (A.piece (p + -d)) U) :
    ((genHom I x).app p).val.app U y = genHomApp I x p U y := rfl

/-- The inclusion `A_{≤ n}[-d] ⟶ A_{≤ n'}[-d]` for `n ≤ n'`. -/
abbrev genModuleLE {n n' : C} (h : n ≤ n') (d : ℤ) :
    genModule (A := A) n d ⟶ genModule n' d :=
  GradedModule.shiftHom (gradedLE h _) (-d)

/-- The inclusion `A_{≤ n}[-d] ⟶ A_{≤ n'}[-d]` is a monomorphism. -/
instance {n n' : C} (h : n ≤ n') (d : ℤ) : Mono (genModuleLE (A := A) h d) :=
  GradedModule.mono_of_mono_app _ fun _ => mono_sheafLE h _

/-- The generator over `n'` restricts to the image of the generator over `n`. -/
theorem gen_restrict {n n' : C} (h : n ≤ n') (d : ℤ) :
    (presheaf n' (A.piece (d + -d))).map (homOfLE h).op (gen n' d) =
      (sheafLE h (A.piece (d + -d))).val.app (op n) (gen n d) := by
  apply Subtype.ext
  rw [presheaf_map_val, sheafLE_app_val]
  show (A.piece (d + -d)).val.map _ (castHom A.piece _ (op n') (A.one.eval (op n'))) =
    castHom A.piece _ (op n) (A.one.eval (op n))
  rw [castHom_naturality]
  congr 1
  exact A.one.2 (homOfLE h).op

end ChaoticTruncation

open ChaoticTruncation

variable {A : GradedAlgebra.{t, m} R} (I : GradedModule.{t, m, m} A)

/-- **Over a preorder with the chaotic topology, the restriction maps of an injective right
graded module are surjective.** -/
theorem GradedModule.surjective_map_of_injective [Injective I] {n n' : C} (h : n ≤ n') (d : ℤ) :
    Function.Surjective ((I.piece d).val.map (homOfLE h).op) := by
  intro x₀
  let x : (I.piece d).val.obj (op n) := x₀
  let g := Injective.factorThru (genHom I x) (genModuleLE (A := A) h d)
  have hg : genModuleLE h d ≫ g = genHom I x := Injective.comp_factorThru _ _
  refine ⟨(g.app d).val.app (op n') (gen n' d), ?_⟩
  rw [← PresheafOfModules.naturality_apply (g.app d).val (homOfLE h).op (gen n' d)]
  show (g.app d).val.app (op n) ((presheaf n' (A.piece (d + -d))).map (homOfLE h).op
    (gen n' d)) = x
  rw [gen_restrict]
  show (((genModuleLE h d ≫ g).app d).val.app (op n) (gen n d)) = x
  rw [hg, genHom_app_apply, genHomApp_gen]

/-- **The restriction maps of a graded injective differential graded module are surjective**, in
every degree, over a preorder with the chaotic topology. -/
theorem DifferentialGradedModule.surjective_map_of_gradedInjective
    {A : DifferentialGradedAlgebra.{t, m} R} {I : DifferentialGradedModule.{t, m, m} A}
    (hI : DifferentialGradedModule.GradedInjective I) {n n' : C} (h : n ≤ n') (k : ℤ) :
    Function.Surjective ((I.complex.X k).val.map (homOfLE h).op) :=
  GradedModule.surjective_map_of_injective ((forgetToGradedModule A).obj I) h k

end SheafOfModules
