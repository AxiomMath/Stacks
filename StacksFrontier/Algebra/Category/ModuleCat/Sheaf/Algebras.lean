module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# Bilinear maps of presheaves of modules and their extension along local bijections

Let `R` be a presheaf of rings on a site `(C, J)`. A *bilinear map* of presheaves of
`R`-modules `M`, `N` with values in `P` is a family of biadditive maps on sections
`M(U) × N(U) ⟶ P(U)`, linear in each variable and compatible with the restriction maps.
This is the sectionwise form of a morphism `M ⊗_p N ⟶ P`.

The main result is that when the target `P` is a sheaf, a bilinear map does not see the
difference between a presheaf and its associated sheaf in either variable: restriction along
a morphism `α : M ⟶ M'` which is both locally injective and locally surjective is a bijection
on bilinear maps into `P`. Equivalently, every bilinear map out of `M` extends uniquely to one
out of `M'`.

## Main definitions

* `Stacks.BilinearMap` is a bilinear map of presheaves of modules, given on sections.
* `Stacks.BilinearMap.flip` interchanges the two variables.
* `Stacks.BilinearMap.compLeft` and `compRight` restrict a bilinear map along a morphism in
  the first, respectively the second, variable.
* `Stacks.BilinearMap.Factors` says that a bilinear map does not distinguish two sections with
  the same image under a morphism in the first variable, and
  `Stacks.BilinearMap.extendOfFactors` extends such a bilinear map along a locally surjective
  morphism into a sheaf.
* `Stacks.BilinearMap.extendVal` is the value of the extension of a bilinear map along a
  locally bijective morphism, and `Stacks.BilinearMap.extend` bundles those values into a
  bilinear map.

## Main results

* `Stacks.BilinearMap.existsUnique_extend`: for a locally injective and locally surjective
  `α : M ⟶ M'`, a sheaf `P` and a bilinear map `β : M × N ⟶ P`, every pair of sections `a` of
  `M'` and `b` of `N` over a common object admits a unique section of `P` which restricts to
  `β m b` along every local lift `m` of `a`.
* `Stacks.BilinearMap.compLeftEquiv` and `compRightEquiv`: restriction along a locally
  bijective morphism is a bijection on bilinear maps into a sheaf, in the first and in the
  second variable respectively.
* `Stacks.BilinearMap.compLeft_injective`: for a locally surjective `α` and a separated `P`,
  restriction along `α` in the first variable is injective on bilinear maps into `P`.
* `Stacks.eq_of_forall_lift` and `Stacks.eq_of_forall_lift₂`: two sections of a separated
  presheaf of modules agree as soon as they agree after restriction along the local lifts of
  one, respectively two, given sections.

## References

* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory PresheafOfModules Opposite

universe v u₁ u w₁ w₂ w₃

namespace Stacks

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- An `R`-bilinear map of presheaves of `R`-modules, given on sections. The first two laws
say that the map is linear in each variable, the last that it commutes with the restriction
maps of the three presheaves. -/
structure BilinearMap (M : PresheafOfModules.{w₁} R) (N : PresheafOfModules.{w₂} R)
    (P : PresheafOfModules.{w₃} R) where
  /-- The biadditive map on sections over an object of the site. -/
  app (X : Cᵒᵖ) : M.obj X →+ N.obj X →+ P.obj X
  /-- Linearity in the first variable. -/
  map_smul_left (X : Cᵒᵖ) (r : R.obj X) (x : M.obj X) (y : N.obj X) :
    app X (r • x) y = r • app X x y
  /-- Linearity in the second variable. -/
  map_smul_right (X : Cᵒᵖ) (r : R.obj X) (x : M.obj X) (y : N.obj X) :
    app X x (r • y) = r • app X x y
  /-- Compatibility with the restriction maps. -/
  naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.obj X) (y : N.obj X) :
    P.map f (app X x y) = app Y (M.map f x) (N.map f y)

variable {M M' : PresheafOfModules.{w₁} R} {N N' : PresheafOfModules.{w₂} R}
  {P : PresheafOfModules.{w₃} R}

/-! ### Sections of a separated presheaf of modules -/

/-- Membership of `f` in the image sieve of a section `a` of `M'` gives a lift along `α` of the
restriction of `a` along `f`. -/
lemma imageSieve_apply (α : M ⟶ M') {X : Cᵒᵖ} (a : M'.obj X) {Y : C} (f : Y ⟶ X.unop)
    (hf : Presheaf.imageSieve ((toPresheaf R).map α) a f) :
    ∃ m : M.obj (op Y), α.app (op Y) m = M'.map f.op a := hf

section Separated

variable (hP : Presheaf.IsSeparated J P.presheaf) (α : M ⟶ M')
  [PresheafOfModules.IsLocallySurjective J α]
include hP

/-- Two sections of a separated presheaf agree as soon as they agree after restriction along
every local lift of a given section of `M'`. -/
lemma eq_of_forall_lift {X : Cᵒᵖ} (a : M'.obj X) (x y : P.obj X)
    (h : ∀ {Y : Cᵒᵖ} (f : X ⟶ Y) (m : M.obj Y), α.app Y m = M'.map f a →
      P.map f x = P.map f y) : x = y := by
  refine hP _ _ (Presheaf.imageSieve_mem J ((toPresheaf _).map α) a) _ _ ?_
  rintro Y f ⟨m, hm⟩
  exact h f.op m hm

/-- The two-section version of `eq_of_forall_lift`. -/
lemma eq_of_forall_lift₂ {X : Cᵒᵖ} (a a' : M'.obj X) (x y : P.obj X)
    (h : ∀ {Y : Cᵒᵖ} (f : X ⟶ Y) (m m' : M.obj Y), α.app Y m = M'.map f a →
      α.app Y m' = M'.map f a' → P.map f x = P.map f y) : x = y := by
  refine hP _ _ (J.intersection_covering
    (Presheaf.imageSieve_mem J ((toPresheaf _).map α) a)
    (Presheaf.imageSieve_mem J ((toPresheaf _).map α) a')) _ _ ?_
  rintro Y f ⟨⟨m, hm⟩, ⟨m', hm'⟩⟩
  exact h f.op m m' hm hm'

end Separated

namespace BilinearMap

/-- A bilinear map is additive in its first variable. -/
lemma map_add_left (β : BilinearMap M N P) (X : Cᵒᵖ) (x x' : M.obj X) (y : N.obj X) :
    β.app X (x + x') y = β.app X x y + β.app X x' y := by
  rw [map_add]; rfl

/-- Two bilinear maps agreeing on all pairs of sections are equal. -/
@[ext]
lemma ext {β₁ β₂ : BilinearMap M N P}
    (h : ∀ (X : Cᵒᵖ) (x : M.obj X) (y : N.obj X), β₁.app X x y = β₂.app X x y) : β₁ = β₂ := by
  obtain ⟨app₁, _, _, _⟩ := β₁
  obtain ⟨app₂, _, _, _⟩ := β₂
  simp only [BilinearMap.mk.injEq]
  ext X x y
  exact h X x y

/-- A bilinear map with its two variables interchanged. -/
def flip (β : BilinearMap M N P) : BilinearMap N M P where
  app X :=
    AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun x => β.app X x y)
        (fun x x' => β.map_add_left X x x' y))
      (fun y y' => by ext x; exact map_add (β.app X x) y y')
  map_smul_left X r y x := β.map_smul_right X r x y
  map_smul_right X r y x := β.map_smul_left X r x y
  naturality f y x := β.naturality f x y

/-- The value of `Stacks.BilinearMap.flip` at `y` and `x` is the value of `β` at `x` and `y`. -/
@[simp]
lemma flip_app (β : BilinearMap M N P) (X : Cᵒᵖ) (y : N.obj X) (x : M.obj X) :
    β.flip.app X y x = β.app X x y := rfl

/-- Interchanging the two variables of a bilinear map is an involutive bijection. -/
@[simps]
def flipEquiv : BilinearMap M N P ≃ BilinearMap N M P where
  toFun := flip
  invFun := flip
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

/-- Restriction of a bilinear map along a morphism in the first variable. -/
def compLeft (β : BilinearMap M' N P) (α : M ⟶ M') : BilinearMap M N P where
  app X := (β.app X).comp (ConcreteCategory.hom (α.app X)).toAddMonoidHom
  map_smul_left X r x y := by
    change β.app X (α.app X (r • x)) y = _
    rw [_root_.map_smul]
    exact β.map_smul_left X r (α.app X x) y
  map_smul_right X r x y := β.map_smul_right X r (α.app X x) y
  naturality {X Y} f x y := by
    change P.map f (β.app X (α.app X x) y) = β.app Y (α.app Y (M.map f x)) (N.map f y)
    rw [β.naturality f, naturality_apply α f x]

/-- The value of `β.compLeft α` at `x` and `y` is the value of `β` at `α x` and `y`. -/
@[simp]
lemma compLeft_app (β : BilinearMap M' N P) (α : M ⟶ M') (X : Cᵒᵖ) (x : M.obj X)
    (y : N.obj X) : (β.compLeft α).app X x y = β.app X (α.app X x) y := rfl

/-- Restriction of a bilinear map along a morphism in the second variable. -/
def compRight (β : BilinearMap M N' P) (α : N ⟶ N') : BilinearMap M N P :=
  (β.flip.compLeft α).flip

/-- The value of `β.compRight α` at `x` and `y` is the value of `β` at `x` and `α y`. -/
@[simp]
lemma compRight_app (β : BilinearMap M N' P) (α : N ⟶ N') (X : Cᵒᵖ) (x : M.obj X)
    (y : N.obj X) : (β.compRight α).app X x y = β.app X x (α.app X y) := rfl

section Separated

variable (hP : Presheaf.IsSeparated J P.presheaf) (α : M ⟶ M')
include hP

section
variable [PresheafOfModules.IsLocallySurjective J α]

/-- A bilinear map into a separated presheaf of modules is determined by its restriction
along a locally surjective morphism in the first variable. -/
lemma app_eq_of_isLocallySurjective (β₁ β₂ : BilinearMap M' N P)
    (h : ∀ (X : Cᵒᵖ) (x : M.obj X) (y : N.obj X),
      β₁.app X (α.app X x) y = β₂.app X (α.app X x) y)
    (X : Cᵒᵖ) (a : M'.obj X) (b : N.obj X) : β₁.app X a b = β₂.app X a b := by
  refine eq_of_forall_lift hP α a _ _ ?_
  intro Y f m hm
  rw [β₁.naturality f, β₂.naturality f, show M'.map f a = α.app Y m from hm.symm]
  exact h _ m _

/-- Restriction along a locally surjective morphism in the first variable is injective on
bilinear maps into a separated presheaf of modules. -/
lemma compLeft_injective : Function.Injective (fun β : BilinearMap M' N P => β.compLeft α) :=
  fun β₁ β₂ h => BilinearMap.ext fun X a b =>
    app_eq_of_isLocallySurjective hP α β₁ β₂
      (fun Y x y => congrArg (fun γ : BilinearMap M N P => γ.app Y x y) h) X a b

end

variable [PresheafOfModules.IsLocallyInjective J α]

/-- A bilinear map into a separated presheaf only depends on the image of its first argument
under a locally injective morphism. -/
lemma app_eq_of_isLocallyInjective (β : BilinearMap M N P) {X : Cᵒᵖ} (m m' : M.obj X)
    (hm : α.app X m = α.app X m') (y : N.obj X) : β.app X m y = β.app X m' y := by
  refine hP _ _ (Presheaf.equalizerSieve_mem J ((toPresheaf _).map α) m m' hm) _ _ ?_
  intro Y f hf
  show P.map f.op _ = P.map f.op _
  rw [β.naturality f.op, β.naturality f.op, show M.map f.op m = M.map f.op m' from hf]

end Separated

/-- `β` **factors through** `α` **in the first variable**: it does not distinguish two sections
of `M` with the same image under `α`. -/
abbrev Factors (α : M ⟶ M') (β : BilinearMap M N P) : Prop :=
  ∀ (X : Cᵒᵖ) (m m' : M.obj X), α.app X m = α.app X m' →
    ∀ y : N.obj X, β.app X m y = β.app X m' y

/-- If `α` is locally injective and the target is separated then every bilinear map out of the
source of `α` factors through it. -/
lemma factors_of_isLocallyInjective (hP : Presheaf.IsSeparated J P.presheaf) (α : M ⟶ M')
    [PresheafOfModules.IsLocallyInjective J α] (β : BilinearMap M N P) : Factors α β :=
  fun _ m m' hm y => app_eq_of_isLocallyInjective hP α β m m' hm y

section ExtendOfFactors

variable (hP : Presheaf.IsSheaf J P.presheaf) (α : M ⟶ M')
  [PresheafOfModules.IsLocallySurjective J α]
include hP

/-- **Extension of a bilinear map along a locally surjective morphism through which it
factors.** If `α : M ⟶ M'` is locally surjective, `P` is a sheaf and the bilinear map
`β : M × N ⟶ P` does not distinguish two sections of `M` with the same image under `α` — that
is the hypothesis `hfac : Factors α β` — then for every pair of sections `a` of `M'` and `b` of
`N` over the same object there is a unique section of `P` whose restriction along each local
lift `m` of `a` is `β m b`. -/
lemma existsUnique_extendOfFactors (β : BilinearMap M N P) (hfac : Factors α β)
    {X : Cᵒᵖ} (a : M'.obj X) (b : N.obj X) :
    ∃! x : P.obj X, ∀ {Y : Cᵒᵖ} (f : X ⟶ Y) (m : M.obj Y),
      α.app Y m = M'.map f a → P.map f x = β.app Y m (N.map f b) := by
  set φ := (toPresheaf R).map α
  set S := Presheaf.imageSieve φ a
  have hSmem : S ∈ J X.unop := Presheaf.imageSieve_mem J φ a
  have hPtype : Presheaf.IsSheaf J (P.presheaf ⋙ forget AddCommGrpCat.{w₃}) :=
    ((sheafCompose J (forget AddCommGrpCat.{w₃})).obj ⟨P.presheaf, hP⟩).2
  choose m hm using fun (Y : C) (f : Y ⟶ X.unop) (hf : S f) => imageSieve_apply α a f hf
  have hfam : Presieve.FamilyOfElements.Compatible
      (P := P.presheaf ⋙ forget AddCommGrpCat.{w₃}) (R := S.arrows)
      (fun Y f hf => β.app (op Y) (m Y f hf) (N.map f.op b)) := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac
    show P.map g₁.op (β.app (op Y₁) (m Y₁ f₁ h₁) (N.map f₁.op b)) =
      P.map g₂.op (β.app (op Y₂) (m Y₂ f₂ h₂) (N.map f₂.op b))
    have e₁ := β.naturality g₁.op (m Y₁ f₁ h₁) (N.map f₁.op b)
    have e₂ := β.naturality g₂.op (m Y₂ f₂ h₂) (N.map f₂.op b)
    have hb : N.map g₁.op (N.map f₁.op b) = N.map g₂.op (N.map f₂.op b) := by
      rw [← N.map_comp_apply, ← N.map_comp_apply, ← op_comp, ← op_comp, fac]
    have hmm : α.app (op Z) (M.map g₁.op (m Y₁ f₁ h₁)) =
        α.app (op Z) (M.map g₂.op (m Y₂ f₂ h₂)) := by
      rw [naturality_apply α g₁.op, naturality_apply α g₂.op, hm, hm,
        ← M'.map_comp_apply, ← M'.map_comp_apply, ← op_comp, ← op_comp, fac]
    rw [e₁, e₂, hb]
    exact hfac _ _ _ hmm _
  have key {Y : Cᵒᵖ} (f : X ⟶ Y) (m₀ : M.obj Y) (hm₀ : α.app Y m₀ = M'.map f a) :
      P.map f ((hPtype.isSheafFor S hSmem).amalgamate _ hfam) = β.app Y m₀ (N.map f b) :=
    ((hPtype.isSheafFor S hSmem).isAmalgamation hfam f.unop ⟨m₀, hm₀⟩).trans
      (hfac _ _ m₀ ((hm _ f.unop ⟨m₀, hm₀⟩).trans hm₀.symm) _)
  exact ⟨_, fun f m₀ hm₀ => key f m₀ hm₀, fun y hy =>
    eq_of_forall_lift hP.isSeparated α a _ _ fun f m₀ hm₀ =>
      (hy f m₀ hm₀).trans (key f m₀ hm₀).symm⟩

variable (β : BilinearMap M N P) (hfac : Factors α β) {X : Cᵒᵖ}

/-- The value at a pair of sections of the extension of a bilinear map along a locally
surjective morphism through which it factors. -/
noncomputable def extendValOfFactors (a : M'.obj X) (b : N.obj X) : P.obj X :=
  (existsUnique_extendOfFactors hP α β hfac a b).choose

/-- The defining property of `Stacks.BilinearMap.extendValOfFactors`: it restricts to `β m b` along
every local lift `m` of `a`. -/
lemma map_extendValOfFactors (a : M'.obj X) (b : N.obj X) {Y : Cᵒᵖ} (f : X ⟶ Y) (mm : M.obj Y)
    (hm : α.app Y mm = M'.map f a) :
    P.map f (extendValOfFactors hP α β hfac a b) = β.app Y mm (N.map f b) :=
  (existsUnique_extendOfFactors hP α β hfac a b).choose_spec.1 f mm hm

/-- `Stacks.BilinearMap.extendValOfFactors` is the only section of `P` with the property
recorded by `Stacks.BilinearMap.map_extendValOfFactors`. -/
lemma eq_extendValOfFactors (a : M'.obj X) (b : N.obj X) (x : P.obj X)
    (hx : ∀ {Y : Cᵒᵖ} (f : X ⟶ Y) (mm : M.obj Y),
      α.app Y mm = M'.map f a → P.map f x = β.app Y mm (N.map f b)) :
    x = extendValOfFactors hP α β hfac a b :=
  (existsUnique_extendOfFactors hP α β hfac a b).choose_spec.2 x hx

/-- On a section of `M'` which is globally in the image of `α`, the extension is computed by
`β` on any preimage. -/
@[simp]
lemma extendValOfFactors_app (m₀ : M.obj X) (b : N.obj X) :
    extendValOfFactors hP α β hfac (α.app X m₀) b = β.app X m₀ b := by
  refine (eq_extendValOfFactors hP α β hfac _ b _ ?_).symm
  intro Y f mm hm
  rw [β.naturality f]
  exact hfac _ _ mm ((naturality_apply α f m₀).trans hm.symm) _

/-- `Stacks.BilinearMap.extendValOfFactors` is additive in its first argument. -/
lemma extendValOfFactors_add_left (a a' : M'.obj X) (b : N.obj X) :
    extendValOfFactors hP α β hfac (a + a') b =
      extendValOfFactors hP α β hfac a b + extendValOfFactors hP α β hfac a' b := by
  refine eq_of_forall_lift₂ hP.isSeparated α a a' _ _ ?_
  intro Y f mm mm' hm hm'
  have hmm : α.app Y (mm + mm') = M'.map f (a + a') := by
    rw [map_add, hm, hm']
    exact (map_add (ConcreteCategory.hom (M'.map f)) a a').symm
  rw [map_extendValOfFactors hP α β hfac _ b f _ hmm, map_add (ConcreteCategory.hom (P.map f)),
    map_extendValOfFactors hP α β hfac a b f mm hm,
    map_extendValOfFactors hP α β hfac a' b f mm' hm']
  exact β.map_add_left Y mm mm' (N.map f b)

/-- `Stacks.BilinearMap.extendValOfFactors` is linear in its first argument. -/
lemma extendValOfFactors_smul_left (r : R.obj X) (a : M'.obj X) (b : N.obj X) :
    extendValOfFactors hP α β hfac (r • a) b = r • extendValOfFactors hP α β hfac a b := by
  refine eq_of_forall_lift hP.isSeparated α a _ _ ?_
  intro Y f mm hm
  have hmm : α.app Y (R.map f r • mm) = M'.map f (r • a) := by
    rw [M'.map_smul, ← hm, _root_.map_smul]
    rfl
  rw [map_extendValOfFactors hP α β hfac _ b f _ hmm,
    P.map_smul f r (extendValOfFactors hP α β hfac a b),
    map_extendValOfFactors hP α β hfac a b f mm hm]
  exact β.map_smul_left Y _ mm _

/-- `Stacks.BilinearMap.extendValOfFactors` is additive in its second argument. -/
lemma extendValOfFactors_add_right (a : M'.obj X) (b b' : N.obj X) :
    extendValOfFactors hP α β hfac a (b + b') =
      extendValOfFactors hP α β hfac a b + extendValOfFactors hP α β hfac a b' := by
  refine eq_of_forall_lift hP.isSeparated α a _ _ ?_
  intro Y f mm hm
  rw [map_extendValOfFactors hP α β hfac a _ f mm hm, map_add (ConcreteCategory.hom (P.map f)),
    map_extendValOfFactors hP α β hfac a b f mm hm,
    map_extendValOfFactors hP α β hfac a b' f mm hm, map_add (ConcreteCategory.hom (N.map f))]
  exact map_add (β.app Y mm) _ _

/-- `Stacks.BilinearMap.extendValOfFactors` is linear in its second argument. -/
lemma extendValOfFactors_smul_right (r : R.obj X) (a : M'.obj X) (b : N.obj X) :
    extendValOfFactors hP α β hfac a (r • b) = r • extendValOfFactors hP α β hfac a b := by
  refine eq_of_forall_lift hP.isSeparated α a _ _ ?_
  intro Y f mm hm
  rw [map_extendValOfFactors hP α β hfac a _ f mm hm, N.map_smul,
    P.map_smul f r (extendValOfFactors hP α β hfac a b),
    map_extendValOfFactors hP α β hfac a b f mm hm]
  exact β.map_smul_right Y _ mm _

/-- `Stacks.BilinearMap.extendValOfFactors` commutes with the restriction maps. -/
lemma extendValOfFactors_naturality {Y : Cᵒᵖ} (f : X ⟶ Y) (a : M'.obj X) (b : N.obj X) :
    P.map f (extendValOfFactors hP α β hfac a b) =
      extendValOfFactors hP α β hfac (X := Y) (M'.map f a) (N.map f b) := by
  refine eq_of_forall_lift hP.isSeparated α (X := Y) (M'.map f a) _ _ ?_
  intro W g mm hm
  have hm' : α.app W mm = M'.map (f ≫ g) a := by rw [hm, M'.map_comp_apply]
  rw [← P.map_comp_apply, map_extendValOfFactors hP α β hfac a b (f ≫ g) mm hm',
    map_extendValOfFactors hP α β hfac (X := Y) (M'.map f a) (N.map f b) g mm hm, N.map_comp_apply]

/-- **The extension of a bilinear map along a locally surjective morphism through which it
factors.** -/
noncomputable def extendOfFactors : BilinearMap M' N P where
  app X :=
    AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => extendValOfFactors hP α β hfac a b)
        (extendValOfFactors_add_right hP α β hfac a))
      (fun a a' => by ext b; exact extendValOfFactors_add_left hP α β hfac a a' b)
  map_smul_left X r a b := extendValOfFactors_smul_left hP α β hfac r a b
  map_smul_right X r a b := extendValOfFactors_smul_right hP α β hfac r a b
  naturality f a b := extendValOfFactors_naturality hP α β hfac f a b

/-- The value of `Stacks.BilinearMap.extendOfFactors` at `a` and `b` is
`Stacks.BilinearMap.extendValOfFactors` at `a` and `b`. -/
@[simp]
lemma extendOfFactors_app (X : Cᵒᵖ) (a : M'.obj X) (b : N.obj X) :
    (extendOfFactors hP α β hfac).app X a b = extendValOfFactors hP α β hfac a b := rfl

/-- The restriction of `Stacks.BilinearMap.extendOfFactors` along `α` is `β`. -/
@[simp]
lemma extendOfFactors_compLeft : (extendOfFactors hP α β hfac).compLeft α = β := by
  ext X m₀ b
  exact extendValOfFactors_app hP α β hfac m₀ b

end ExtendOfFactors

section Extend

variable (hP : Presheaf.IsSheaf J P.presheaf) (α : M ⟶ M')
  [PresheafOfModules.IsLocallySurjective J α]
  [PresheafOfModules.IsLocallyInjective J α]
include hP

/-- **Extension of a bilinear map along a locally bijective morphism.** If `α : M ⟶ M'` is
locally injective and locally surjective and `P` is a sheaf, then for every bilinear map
`β : M × N ⟶ P` and every pair of sections `a` of `M'` and `b` of `N` over the same object
there is a unique section of `P` whose restriction along each local lift `m` of `a` is
`β m b`. -/
lemma existsUnique_extend (β : BilinearMap M N P) {X : Cᵒᵖ} (a : M'.obj X) (b : N.obj X) :
    ∃! x : P.obj X, ∀ {Y : Cᵒᵖ} (f : X ⟶ Y) (m : M.obj Y),
      α.app Y m = M'.map f a → P.map f x = β.app Y m (N.map f b) :=
  existsUnique_extendOfFactors hP α β (factors_of_isLocallyInjective hP.isSeparated α β) a b

variable (β : BilinearMap M N P) {X : Cᵒᵖ}

/-- The value at a pair of sections of the extension of a bilinear map along a locally
bijective morphism. -/
noncomputable def extendVal (a : M'.obj X) (b : N.obj X) : P.obj X :=
  extendValOfFactors hP α β (factors_of_isLocallyInjective hP.isSeparated α β) a b

/-- `Stacks.BilinearMap.extendVal` restricts to `β m b` along every local lift `m` of `a`. -/
lemma map_extendVal (a : M'.obj X) (b : N.obj X) {Y : Cᵒᵖ} (f : X ⟶ Y) (mm : M.obj Y)
    (hm : α.app Y mm = M'.map f a) :
    P.map f (extendVal hP α β a b) = β.app Y mm (N.map f b) :=
  map_extendValOfFactors hP α β _ a b f mm hm

/-- `Stacks.BilinearMap.extendVal` is the only section of `P` with the property recorded by
`Stacks.BilinearMap.map_extendVal`. -/
lemma eq_extendVal (a : M'.obj X) (b : N.obj X) (x : P.obj X)
    (hx : ∀ {Y : Cᵒᵖ} (f : X ⟶ Y) (mm : M.obj Y),
      α.app Y mm = M'.map f a → P.map f x = β.app Y mm (N.map f b)) :
    x = extendVal hP α β a b :=
  eq_extendValOfFactors hP α β _ a b x hx

/-- On a section of `M'` in the image of `α`, `Stacks.BilinearMap.extendVal` is computed by `β`
on any preimage. -/
@[simp]
lemma extendVal_app (m₀ : M.obj X) (b : N.obj X) :
    extendVal hP α β (α.app X m₀) b = β.app X m₀ b :=
  extendValOfFactors_app hP α β _ m₀ b

/-- `Stacks.BilinearMap.extendVal` is additive in its first argument. -/
lemma extendVal_add_left (a a' : M'.obj X) (b : N.obj X) :
    extendVal hP α β (a + a') b = extendVal hP α β a b + extendVal hP α β a' b :=
  extendValOfFactors_add_left hP α β _ a a' b

/-- `Stacks.BilinearMap.extendVal` is linear in its first argument. -/
lemma extendVal_smul_left (r : R.obj X) (a : M'.obj X) (b : N.obj X) :
    extendVal hP α β (r • a) b = r • extendVal hP α β a b :=
  extendValOfFactors_smul_left hP α β _ r a b

/-- `Stacks.BilinearMap.extendVal` is additive in its second argument. -/
lemma extendVal_add_right (a : M'.obj X) (b b' : N.obj X) :
    extendVal hP α β a (b + b') = extendVal hP α β a b + extendVal hP α β a b' :=
  extendValOfFactors_add_right hP α β _ a b b'

/-- `Stacks.BilinearMap.extendVal` is linear in its second argument. -/
lemma extendVal_smul_right (r : R.obj X) (a : M'.obj X) (b : N.obj X) :
    extendVal hP α β a (r • b) = r • extendVal hP α β a b :=
  extendValOfFactors_smul_right hP α β _ r a b

/-- `Stacks.BilinearMap.extendVal` commutes with the restriction maps. -/
lemma extendVal_naturality {Y : Cᵒᵖ} (f : X ⟶ Y) (a : M'.obj X) (b : N.obj X) :
    P.map f (extendVal hP α β a b) = extendVal hP α β (X := Y) (M'.map f a) (N.map f b) :=
  extendValOfFactors_naturality hP α β _ f a b

/-- **The extension of a bilinear map along a locally bijective morphism.** -/
noncomputable def extend : BilinearMap M' N P :=
  extendOfFactors hP α β (factors_of_isLocallyInjective hP.isSeparated α β)

/-- The value of `Stacks.BilinearMap.extend` at `a` and `b` is `Stacks.BilinearMap.extendVal`
at `a` and `b`. -/
@[simp]
lemma extend_app (X : Cᵒᵖ) (a : M'.obj X) (b : N.obj X) :
    (extend hP α β).app X a b = extendVal hP α β a b := rfl

/-- The restriction of `Stacks.BilinearMap.extend` along `α` is `β`. -/
@[simp]
lemma extend_compLeft : (extend hP α β).compLeft α = β :=
  extendOfFactors_compLeft hP α β _

end Extend

section Equiv

variable (hP : Presheaf.IsSheaf J P.presheaf)
include hP

/-- **Bilinear maps into a sheaf do not see a local bijection in the first variable.**
Restriction along a locally injective and locally surjective morphism `α : M ⟶ M'` is a
bijection from bilinear maps out of `M'` to bilinear maps out of `M`, when the target is a
sheaf. -/
noncomputable def compLeftEquiv (α : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective J α]
    [PresheafOfModules.IsLocallyInjective J α] :
    BilinearMap M' N P ≃ BilinearMap M N P where
  toFun β' := β'.compLeft α
  invFun β := extend hP α β
  left_inv β' := compLeft_injective hP.isSeparated α (extend_compLeft hP α (β'.compLeft α))
  right_inv β := extend_compLeft hP α β

/-- `Stacks.BilinearMap.compLeftEquiv` sends `β'` to its restriction along `α`. -/
@[simp]
lemma compLeftEquiv_apply (α : M ⟶ M')
    [PresheafOfModules.IsLocallySurjective J α]
    [PresheafOfModules.IsLocallyInjective J α] (β' : BilinearMap M' N P) :
    compLeftEquiv (N := N) hP α β' = β'.compLeft α := rfl

/-- **Bilinear maps into a sheaf do not see a local bijection in the second variable.** -/
noncomputable def compRightEquiv (α : N ⟶ N')
    [PresheafOfModules.IsLocallySurjective J α]
    [PresheafOfModules.IsLocallyInjective J α] :
    BilinearMap M N' P ≃ BilinearMap M N P :=
  flipEquiv.trans ((compLeftEquiv (N := M) hP α).trans flipEquiv)

/-- `Stacks.BilinearMap.compRightEquiv` sends `β'` to its restriction along `α` in the second
variable. -/
@[simp]
lemma compRightEquiv_apply (α : N ⟶ N')
    [PresheafOfModules.IsLocallySurjective J α]
    [PresheafOfModules.IsLocallyInjective J α] (β' : BilinearMap M N' P) :
    compRightEquiv (M := M) hP α β' = β'.compRight α := by
  ext X x y
  rfl

end Equiv

end BilinearMap

end Stacks
