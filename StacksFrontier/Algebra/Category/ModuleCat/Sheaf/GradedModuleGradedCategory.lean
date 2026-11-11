module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedInternalHomSheaf
public import StacksFrontier.Algebra.DGA.DirectSumGrading
public import StacksFrontier.CategoryTheory.Graded.DegreeZero
public import StacksCore.Tactic.StacksAttribute

/-!
# The graded category of right graded modules over a sheaf of graded algebras

Let `(C, O)` be a ringed site and let `A` be a sheaf of graded `O`-algebras. Following
[Stacks, Tag 0FR1], the right graded `A`-modules are the objects of a graded category
`Mod^gr(A)` over `R = Γ(C, O)`: the morphisms `L → M` are
`⨁_{n ∈ ℤ} Hom^n(L, M)`, where `Hom^n(L, M)` is the `R`-module of maps of right graded
`A`-modules homogeneous of degree `n` (`SheafOfModules.GradedHomOfDegree`), and composition is
composition of maps, `Hom^m(L, M) × Hom^n(K, L) → Hom^{n + m}(K, M)`,
`(g, f) ↦ g ∘ f` (`SheafOfModules.GradedHomOfDegree.comp`). The associated category
`(Mod^gr(A))^0` is the category of graded `A`-modules.

## Main definitions

* `SheafOfModules.GradedHomOfDegree.id`: the identity of a right graded module, homogeneous of
  degree zero.
* `SheafOfModules.GradedHomOfDegree.components`: a homogeneous map `f` of degree `n` as the
  family of its components `f_{p, q} : L^{-q} → M^p`, `p + q = n`, and
  `SheafOfModules.GradedHomOfDegree.componentsEquiv`, which identifies `Hom^n(L, M)` with the
  subset of `∏_{p + q = n} Hom_O(L^{-q}, M^p)` of the families with
  `f_{p, q}(m a) = f_{p - i, q + i}(m) a` (`SheafOfModules.GradedHomOfDegree.IsComponentFamily`).
* `SheafOfModules.GradedModuleCat A`: the graded category `Mod^gr(A)`, a type synonym for the
  right graded `A`-modules, whose morphisms `SheafOfModules.GradedModuleCat.Hom` are the finite
  sums `⨁_n Hom^n(L, M)`.
* `SheafOfModules.GradedModuleCat.degreeZeroEquivalence`: the equivalence between the degree-zero
  category `(Mod^gr(A))^0` and the category `SheafOfModules.GradedModule A` of graded
  `A`-modules, which is the identity on objects.

## Main results

* `SheafOfModules.GradedHomOfDegree.id_comp_app`, `comp_id_app` and `comp_assoc_app`: the unit
  and associativity laws of composition, componentwise.
* `SheafOfModules.GradedHomOfDegree.add_comp`, `comp_add`, `smul_comp` and `comp_smul`:
  composition is `Γ(C, O)`-bilinear.
* `SheafOfModules.GradedModuleCat.instCategory`, `instPreadditive`, `instLinear` and
  `instGradedCategory`: the category `Mod^gr(A)`, its `Γ(C, O)`-linear structure and its
  grading by the degrees of homogeneous maps.

## Implementation notes

The base is an arbitrary sheaf of rings `R` on a site whose rings of sections are commutative,
recorded by the instance argument `∀ U, IsMulCommutative (R.obj.obj U)`; a ringed site
`(C, O)` is the case `R := O`, and then `Γ(C, R)` is the ring
`Stacks.Cohomology.SiteModules.GlobalSectionRing R`, made commutative by
`SheafOfModules.GradedModuleCat.globalSectionCommRing`. The construction of the graded category
follows `StacksFrontier/CategoryTheory/Graded/GradedModule.lean`, where a morphism is a `DirectSum`
of the homogeneous pieces.

The components `f_{p, q}` of [Stacks, Tag 0FR1] are indexed by pairs `(p, q)` with `p + q = n`;
since `-(q + i) + i` and `-q`, and `(p - i) + i` and `p`, are equal but not definitionally so, the
displayed compatibility is stated with the transports `SheafOfModules.castHom` between the
pieces of `L` and of `M`.

## References

* [Stacks Project, Tag 0FR1](https://stacks.math.columbia.edu/tag/0FR1)
* [Stacks Project, Tag 09MN](https://stacks.math.columbia.edu/tag/09MN)
-/

@[expose] public section

open CategoryTheory Opposite

universe t a w v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : GradedAlgebra.{t, a} R}

namespace GradedHomOfDegree

section Laws

variable {K L M N : GradedModule.{t, a, w} A} {m n k : ℤ}

/-- The components of a composite, through an arbitrary intermediate degree. -/
theorem comp_app_eq (g : GradedHomOfDegree L M m) (f : GradedHomOfDegree K L n) (i j : ℤ)
    (hij : i + (n + m) = j) (l : ℤ) (hl : i + n = l) :
    (g.comp f).app i j hij = f.app i l hl ≫ g.app l j (by omega) := by
  subst hl
  exact comp_app g f i j hij

/-- **The identity in `Mod^gr(A)`**: the identity of a right graded `A`-module, homogeneous of
degree zero. -/
@[stacks 0FR1 "the identity of `Mod^gr(A)`, in `Hom^0(M, M)`"]
def id (M : GradedModule.{t, a, w} A) : GradedHomOfDegree M M 0 where
  app i j hij := eqToHom (congrArg M.piece (by omega : i = j))
  map_mul i j hij p U x b := by
    obtain rfl : j = i := by omega
    simp only [eqToHom_refl]
    rfl

/-- The diagonal components of the identity are identities. -/
@[simp]
theorem id_app_self (M : GradedModule.{t, a, w} A) (i : ℤ) (h : i + 0 = i) :
    (id M).app i i h = 𝟙 _ := by
  simp only [id, eqToHom_refl]

/-- Composing with the identity on the left does nothing, componentwise. -/
theorem id_comp_app (f : GradedHomOfDegree K L n) (i j : ℤ) (hij : i + (n + 0) = j) :
    ((id L).comp f).app i j hij = f.app i j (by omega) := by
  rw [comp_app_eq _ _ i j hij j (by omega), id_app_self, Category.comp_id]

/-- Composing with the identity on the right does nothing, componentwise. -/
theorem comp_id_app (f : GradedHomOfDegree K L n) (i j : ℤ) (hij : i + (0 + n) = j) :
    (f.comp (id K)).app i j hij = f.app i j (by omega) := by
  rw [comp_app_eq _ _ i j hij i (by omega), id_app_self, Category.id_comp]

/-- Composition of homogeneous maps is associative, componentwise. -/
theorem comp_assoc_app (h : GradedHomOfDegree M N k) (g : GradedHomOfDegree L M m)
    (f : GradedHomOfDegree K L n) (i j : ℤ) (hij : i + (n + m + k) = j) :
    (h.comp (g.comp f)).app i j hij = ((h.comp g).comp f).app i j (by omega) := by
  rw [comp_app_eq h (g.comp f) i j hij (i + n + m) (by omega),
    comp_app_eq g f i (i + n + m) (by omega) (i + n) rfl,
    comp_app_eq (h.comp g) f i j (by omega) (i + n) rfl,
    comp_app_eq h g (i + n) j (by omega) (i + n + m) rfl, Category.assoc]

end Laws

section Bilinear

variable [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]
variable {K L M : GradedModule.{t, a, w} A} {m n : ℤ}

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The restriction of a sum to a slice site is the sum of the restrictions. -/
theorem toLocal_add (f g : GradedHomOfDegree M L n) (U : C) :
    (f + g).toLocal U = f.toLocal U + g.toLocal U :=
  toLocal_ofLocal _ (by intros; rfl) U

/-- The restriction of `c • f` to the slice site over `U` is `c|_U • f|_U`. -/
theorem toLocal_smul (c : Stacks.Cohomology.SiteModules.GlobalSectionRing R)
    (f : GradedHomOfDegree M L n) (U : C) :
    (c • f).toLocal U = c.1 (op U) • f.toLocal U :=
  toLocal_ofLocal _ (smul_toLocal_restrict c f) U

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- Composition in `Mod^gr(A)` is additive in the first variable. -/
@[stacks 0FR1 "composition is additive in `g`"]
theorem add_comp (g g' : GradedHomOfDegree L M m) (f : GradedHomOfDegree K L n) :
    (g + g').comp f = g.comp f + g'.comp f :=
  eq_of_toLocal fun U => by
    rw [toLocal_comp, toLocal_add, toLocal_add, toLocal_comp, toLocal_comp,
      GradedLocalHom.add_comp]

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- Composition in `Mod^gr(A)` is additive in the second variable. -/
@[stacks 0FR1 "composition is additive in `f`"]
theorem comp_add (g : GradedHomOfDegree L M m) (f f' : GradedHomOfDegree K L n) :
    g.comp (f + f') = g.comp f + g.comp f' :=
  eq_of_toLocal fun U => by
    rw [toLocal_comp, toLocal_add, toLocal_add, toLocal_comp, toLocal_comp,
      GradedLocalHom.comp_add]

/-- Composition in `Mod^gr(A)` is `Γ(C, O)`-linear in the first variable. -/
@[stacks 0FR1 "composition is `R`-linear in `g`"]
theorem smul_comp (c : Stacks.Cohomology.SiteModules.GlobalSectionRing R)
    (g : GradedHomOfDegree L M m) (f : GradedHomOfDegree K L n) :
    (c • g).comp f = c • g.comp f :=
  eq_of_toLocal fun U => by
    rw [toLocal_comp, toLocal_smul, toLocal_smul, toLocal_comp, GradedLocalHom.smul_comp]

/-- Composition in `Mod^gr(A)` is `Γ(C, O)`-linear in the second variable. -/
@[stacks 0FR1 "composition is `R`-linear in `f`"]
theorem comp_smul (c : Stacks.Cohomology.SiteModules.GlobalSectionRing R)
    (g : GradedHomOfDegree L M m) (f : GradedHomOfDegree K L n) :
    g.comp (c • f) = c • g.comp f :=
  eq_of_toLocal fun U => by
    rw [toLocal_comp, toLocal_smul, toLocal_smul, toLocal_comp, GradedLocalHom.comp_smul]

/-- Composition `Hom^n(K, L) × Hom^m(L, M) → Hom^{n + m}(K, M)`, `(f, g) ↦ g ∘ f`, bundled as
an additive map in both variables. -/
noncomputable def compAddHom (K L M : GradedModule.{t, a, w} A) (n m : ℤ) :
    GradedHomOfDegree K L n →+ GradedHomOfDegree L M m →+ GradedHomOfDegree K M (n + m) :=
  AddMonoidHom.mk' (fun f => AddMonoidHom.mk' (fun g => g.comp f) fun g g' => add_comp g g' f)
    fun f f' => AddMonoidHom.ext fun g => comp_add g f f'

/-- The bundled composition sends `f` and `g` to `g ∘ f`. -/
@[simp]
theorem compAddHom_apply (f : GradedHomOfDegree K L n) (g : GradedHomOfDegree L M m) :
    compAddHom K L M n m f g = g.comp f := rfl

end Bilinear

section Components

variable {L M : GradedModule.{t, a, w} A} {n : ℤ}

/-- Two values of a homogeneous map on sections transported between propositionally equal
source degrees are related by transport in the target. -/
theorem app_castHom_source (f : GradedHomOfDegree L M n) {i i' j j' : ℤ} (hi : i = i')
    (hj : j = j') (hij : i + n = j) (hij' : i' + n = j') (U : Cᵒᵖ) (x : (L.piece i).val.obj U) :
    (f.app i' j' hij').val.app U (castHom L.piece hi U x) =
      castHom M.piece hj U ((f.app i j hij).val.app U x) := by
  subst hi hj
  rfl

/-- **The components of a homogeneous map** (Stacks 0FR1): a map `f` homogeneous of degree `n`
as the family `f_{p, q} : L^{-q} → M^p`, `p + q = n`, of its components; the reversal of indices
is that of the source. -/
@[stacks 0FR1 "the components `f_{p, q} : L^{-q} → M^p`, `p + q = n`, of `f ∈ Hom^n(L, M)`"]
def components (f : GradedHomOfDegree L M n) (p q : ℤ) (h : p + q = n) :
    L.piece (-q) ⟶ M.piece p :=
  f.app (-q) p (by omega)

/-- The condition singling out `Hom^n(L, M)` inside `∏_{p + q = n} Hom_O(L^{-q}, M^p)`:
`f_{p, q}(m a) = f_{p - i, q + i}(m) a` for local sections `a` of `A^i` and `m` of
`L^{-q - i}`. The degree `-q - i` is written `-(q + i)`, the degree of the source of
`f_{p - i, q + i}`, and the products `m a`, of degree `-(q + i) + i`, and `f_{p - i, q + i}(m) a`,
of degree `(p - i) + i`, are transported to the degrees `-q` and `p`. -/
def IsComponentFamily (f : ∀ p q : ℤ, p + q = n → (L.piece (-q) ⟶ M.piece p)) : Prop :=
  ∀ (p q : ℤ) (h : p + q = n) (i : ℤ) (U : Cᵒᵖ) (x : (L.piece (-(q + i))).val.obj U)
    (b : (A.piece i).val.obj U),
    (f p q h).val.app U (castHom L.piece (by omega) U (L.smul (-(q + i)) i U x b)) =
      castHom M.piece (by omega) U
        (M.smul (p - i) i U ((f (p - i) (q + i) (by omega)).val.app U x) b)

/-- The components of a homogeneous map satisfy the compatibility of Stacks 0FR1. -/
theorem isComponentFamily_components (f : GradedHomOfDegree L M n) :
    IsComponentFamily f.components := by
  intro p q h i U x b
  simp only [components]
  rw [app_castHom_source f (i := -(q + i) + i) (j := p - i + i) (by omega) (by omega)
    (by omega), f.map_mul]

/-- A family of maps `f_{p, q} : L^{-q} → M^p`, `p + q = n`, is unchanged by transport along
equalities of its indices. -/
theorem family_castHom (f : ∀ p q : ℤ, p + q = n → (L.piece (-q) ⟶ M.piece p))
    {p q p' q' s : ℤ} (hp : p = p') (hq : q = q') (h : p + q = n) (h' : p' + q' = n) (U : Cᵒᵖ)
    (hs : s = -q) (x : (L.piece s).val.obj U) :
    (f p' q' h').val.app U (castHom L.piece (by omega) U x) =
      castHom M.piece hp U ((f p q h).val.app U (castHom L.piece hs U x)) := by
  subst hp hq hs
  rfl

/-- Precomposing a component of a family with a transport of its source degree changes only
the index. -/
theorem family_eqToHom (f : ∀ p q : ℤ, p + q = n → (L.piece (-q) ⟶ M.piece p)) {p q q' : ℤ}
    (hq : q = q') (h : p + q = n) (h' : p + q' = n) :
    eqToHom (congrArg L.piece (by omega : -q = -q')) ≫ f p q' h' = f p q h := by
  subst hq
  simp

/-- Precomposing a homogeneous map with a transport of its source degree changes only the
index. -/
theorem eqToHom_comp_app (f : GradedHomOfDegree L M n) {i i' j : ℤ} (hi : i = i')
    (h : i + n = j) (h' : i' + n = j) :
    eqToHom (congrArg L.piece hi) ≫ f.app i' j h' = f.app i j h := by
  subst hi
  simp

private theorem eqToHom_val_app_eq_castHom (X : ℤ → SheafOfModules.{w} R) {i j : ℤ} (h : i = j)
    (U : Cᵒᵖ) (x : (X i).val.obj U) :
    (eqToHom (congrArg X h)).val.app U x = castHom X h U x := by
  subst h
  rfl

private theorem comp_val_app_apply {X Y Z : SheafOfModules.{w} R} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Cᵒᵖ) (x : X.val.obj U) : (f ≫ g).val.app U x = g.val.app U (f.val.app U x) := rfl

/-- The homogeneous map of degree `n` with prescribed components, for a family satisfying the
compatibility of Stacks 0FR1. -/
def ofComponents (f : ∀ p q : ℤ, p + q = n → (L.piece (-q) ⟶ M.piece p))
    (hf : IsComponentFamily f) : GradedHomOfDegree L M n where
  app i j hij := eqToHom (congrArg L.piece (neg_neg i).symm) ≫ f j (-i) (by omega)
  map_mul i j hij p U x b := by
    have key := hf (j + p) (-(i + p)) (by omega) p U
      (castHom L.piece (by omega : i = -(-(i + p) + p)) U x) b
    rw [Cofree.smul_castHom_left, Cofree.castHom_castHom,
      family_castHom f (p := j) (q := -i) (p' := j + p - p) (q' := -(i + p) + p) (by omega)
        (by omega) (by omega) (by omega) U (by omega : i = -(-i)),
      Cofree.smul_castHom_left, Cofree.castHom_castHom] at key
    rw [comp_val_app_apply, comp_val_app_apply, eqToHom_val_app_eq_castHom,
      eqToHom_val_app_eq_castHom]
    exact key

/-- **Stacks 0FR1, in terms of components**: `Hom^n(L, M)` is the subset of
`∏_{p + q = n} Hom_O(L^{-q}, M^p)` of the families `f = (f_{p, q})` with
`f_{p, q}(m a) = f_{p - i, q + i}(m) a`; a homogeneous map corresponds to the family of its
components. -/
@[stacks 0FR1 "`Hom^n(L, M) ⊂ ∏_{p + q = n} Hom_O(L^{-q}, M^p)` is the subset of the families
with `f_{p, q}(m a) = f_{p - i, q + i}(m) a`"]
def componentsEquiv (L M : GradedModule.{t, a, w} A) (n : ℤ) :
    GradedHomOfDegree L M n ≃
      {f : ∀ p q : ℤ, p + q = n → (L.piece (-q) ⟶ M.piece p) // IsComponentFamily f} where
  toFun f := ⟨f.components, f.isComponentFamily_components⟩
  invFun f := ofComponents f.1 f.2
  left_inv f := ext fun i _ hij => eqToHom_comp_app f (neg_neg i).symm hij _
  right_inv f := Subtype.ext (funext fun _ => funext fun q => funext fun h =>
    family_eqToHom f.1 (neg_neg q).symm h _)

/-- The family attached to a homogeneous map is the family of its components. -/
@[simp]
theorem componentsEquiv_apply (f : GradedHomOfDegree L M n) :
    (componentsEquiv L M n f).1 = f.components := rfl

end Components

section DegreeZero

variable {K L M : GradedModule.{t, a, w} A}

/-- A homomorphism of graded `A`-modules, as a homogeneous map of degree zero. -/
def ofGradedModuleHom (φ : L ⟶ M) : GradedHomOfDegree L M 0 where
  app i j hij := φ.app i ≫ eqToHom (congrArg M.piece (by omega : i = j))
  map_mul i j hij p U x b := by
    obtain rfl : j = i := by omega
    simp only [eqToHom_refl, Category.comp_id]
    exact GradedModule.Hom.map_smul φ j p U x b

/-- A homogeneous map of degree zero, as a homomorphism of graded `A`-modules. -/
def toGradedModuleHom (f : GradedHomOfDegree L M 0) : L ⟶ M where
  app n := f.app n n (add_zero n)
  map_smul n i U x y := f.map_mul n n (add_zero n) i U x y

/-- The components of a homogeneous map of degree zero are those of the homomorphism of graded
modules it defines. -/
@[simp]
theorem toGradedModuleHom_app (f : GradedHomOfDegree L M 0) (n : ℤ) :
    (toGradedModuleHom f).app n = f.app n n (add_zero n) := rfl

/-- A homomorphism of graded modules is recovered from the homogeneous map of degree zero it
defines. -/
@[simp]
theorem toGradedModuleHom_ofGradedModuleHom (φ : L ⟶ M) :
    toGradedModuleHom (ofGradedModuleHom φ) = φ :=
  GradedModule.Hom.ext fun n => by
    simp only [toGradedModuleHom_app, ofGradedModuleHom, eqToHom_refl, Category.comp_id]

/-- A homogeneous map of degree zero is recovered from the homomorphism of graded modules it
defines. -/
@[simp]
theorem ofGradedModuleHom_toGradedModuleHom (f : GradedHomOfDegree L M 0) :
    ofGradedModuleHom (toGradedModuleHom f) = f :=
  ext fun i j hij => by
    obtain rfl : j = i := by omega
    simp only [ofGradedModuleHom, eqToHom_refl, Category.comp_id, toGradedModuleHom_app]

/-- The identity homomorphism is the identity homogeneous map. -/
theorem ofGradedModuleHom_id (L : GradedModule.{t, a, w} A) :
    ofGradedModuleHom (𝟙 L) = id L :=
  ext fun _ _ _ => Category.id_comp _

/-- The homogeneous map of degree zero defined by a composite is the composite, componentwise. -/
theorem ofGradedModuleHom_comp_app (φ : K ⟶ L) (ψ : L ⟶ M) (i j : ℤ) (hij : i + (0 + 0) = j) :
    ((ofGradedModuleHom ψ).comp (ofGradedModuleHom φ)).app i j hij =
      (ofGradedModuleHom (φ ≫ ψ)).app i j (by omega) := by
  rw [comp_app_eq _ _ i j hij i (by omega)]
  simp only [ofGradedModuleHom, eqToHom_refl, Category.comp_id]
  rw [← Category.assoc]
  rfl

end DegreeZero

end GradedHomOfDegree

/-- **The graded category `Mod^gr(A)` of Stacks 0FR1**: its objects are the right graded
`A`-modules. This is a type synonym so that it can carry the category structure whose morphisms
are the finite sums of homogeneous maps, rather than only the maps of degree zero. -/
@[stacks 0FR1 "the objects of `Mod^gr(A)`: right graded `A`-modules"]
def GradedModuleCat (A : GradedAlgebra.{t, a} R) := GradedModule.{t, a, w} A

namespace GradedModuleCat

/-- The right graded `A`-module underlying an object of `Mod^gr(A)`. -/
abbrev toGradedModule (L : GradedModuleCat.{t, a, w} A) : GradedModule.{t, a, w} A := L


variable [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]

/-- The ring `Γ(C, O)` of global sections of a sheaf of rings with commutative rings of
sections is commutative. -/
@[implicit_reducible]
def globalSectionCommRing : CommRing (Stacks.Cohomology.SiteModules.GlobalSectionRing R) :=
  { (inferInstance : Ring (Stacks.Cohomology.SiteModules.GlobalSectionRing R)) with
    mul_comm := fun x y => Subtype.ext (funext fun U => by
      change (x.1 U : R.obj.obj U) * y.1 U = y.1 U * x.1 U
      exact Std.Commutative.comm _ _) }

attribute [local instance] globalSectionCommRing

/-- The morphisms `L → M` of `Mod^gr(A)`: `⨁_{n ∈ ℤ} Hom^n(L, M)`. -/
abbrev Hom (L M : GradedModuleCat.{t, a, w} A) :=
  DirectSum ℤ (fun n => GradedHomOfDegree L.toGradedModule M.toGradedModule n)

/-- Composition of finite sums of homogeneous maps, extending
`Hom^n(K, L) × Hom^m(L, M) → Hom^{n + m}(K, M)`, `(f, g) ↦ g ∘ f`, additively. -/
noncomputable def comp (K L M : GradedModuleCat.{t, a, w} A) : Hom K L →+ Hom L M →+ Hom K M :=
  DirectSum.toAddMonoid fun n => AddMonoidHom.flip <|
    DirectSum.toAddMonoid fun m => AddMonoidHom.flip <|
      (DirectSum.of (fun k => GradedHomOfDegree K.toGradedModule M.toGradedModule k)
        (n + m)).compHom.comp
        (GradedHomOfDegree.compAddHom K.toGradedModule L.toGradedModule
          M.toGradedModule n m)

/-- The composite of homogeneous summands of degrees `n` and `m` is the homogeneous summand of
degree `n + m` given by their composite. -/
@[simp]
theorem comp_of_of {K L M : GradedModuleCat.{t, a, w} A} {n m : ℤ}
    (f : GradedHomOfDegree K.toGradedModule L.toGradedModule n)
    (g : GradedHomOfDegree L.toGradedModule M.toGradedModule m) :
    comp K L M (DirectSum.of _ n f) (DirectSum.of _ m g) = DirectSum.of _ (n + m) (g.comp f) := by
  simp [comp]

/-- The identity of `Mod^gr(A)`, concentrated in degree zero. -/
noncomputable def id (M : GradedModuleCat.{t, a, w} A) : Hom M M :=
  DirectSum.of _ 0 (GradedHomOfDegree.id M.toGradedModule)

/-- Homogeneous summands of equal degrees with equal components are equal. -/
theorem of_eq_of {L M : GradedModuleCat.{t, a, w} A} {n n' : ℤ}
    (f : GradedHomOfDegree L.toGradedModule M.toGradedModule n)
    (f' : GradedHomOfDegree L.toGradedModule M.toGradedModule n') (h : n = n')
    (hf : ∀ (i j : ℤ) (hij : i + n = j), f.app i j hij = f'.app i j (by omega)) :
    DirectSum.of (fun k => GradedHomOfDegree L.toGradedModule M.toGradedModule k) n f =
      DirectSum.of (fun k => GradedHomOfDegree L.toGradedModule M.toGradedModule k) n' f' := by
  subst h
  exact congrArg _ (GradedHomOfDegree.ext hf)

private theorem category_comp_id (M N : GradedModuleCat.{t, a, w} A) (f : Hom M N) :
    comp M N N f (id N) = f := by
  induction f using DirectSum.induction_on with
  | of n f =>
    rw [id, comp_of_of]
    exact of_eq_of _ _ (add_zero n) fun i j hij => GradedHomOfDegree.id_comp_app f i j hij
  | _ => simp_all [comp]

private theorem category_id_comp (M N : GradedModuleCat.{t, a, w} A) (f : Hom M N) :
    comp M M N (id M) f = f := by
  induction f using DirectSum.induction_on with
  | of n f =>
    rw [id, comp_of_of]
    exact of_eq_of _ _ (zero_add n) fun i j hij => GradedHomOfDegree.comp_id_app f i j hij
  | _ => simp_all [comp]

private theorem category_comp_assoc (M N P Q : GradedModuleCat.{t, a, w} A)
    (f : Hom M N) (g : Hom N P) (h : Hom P Q) :
    comp M P Q (comp M N P f g) h = comp M N Q f (comp N P Q g h) := by
  induction f using DirectSum.induction_on with
  | of n f =>
    induction g using DirectSum.induction_on with
    | of m g =>
      induction h using DirectSum.induction_on with
      | of k h =>
        rw [comp_of_of, comp_of_of, comp_of_of, comp_of_of]
        exact of_eq_of _ _ (add_assoc n m k) fun i j hij =>
          GradedHomOfDegree.comp_assoc_app h g f i j hij
      | _ => simp_all
    | _ => simp_all
  | _ => simp_all

/-- **The category `Mod^gr(A)` of Stacks 0FR1**: the morphisms `L → M` are
`⨁_n Hom^n(L, M)`, and composition is composition of homogeneous maps,
`Hom^m(L, M) × Hom^n(K, L) → Hom^{n + m}(K, M)`, extended additively. -/
@[stacks 0FR1 "`Hom_{Mod^gr(A)}(L, M) = ⨁_n Hom^n(L, M)`, with composition `(g, f) ↦ g ∘ f`"]
noncomputable instance instCategory : Category (GradedModuleCat.{t, a, w} A) where
  Hom := Hom
  id := id
  comp f g := comp _ _ _ f g
  id_comp := by intros; apply category_id_comp
  comp_id := by intros; apply category_comp_id
  assoc := by intros; apply category_comp_assoc

/-- In `Mod^gr(A)`, the composite of homogeneous morphisms of degrees `n` and `m` is the
homogeneous morphism of degree `n + m` given by their composite. -/
@[simp]
theorem of_comp_of {K L M : GradedModuleCat.{t, a, w} A} {n m : ℤ}
    (f : GradedHomOfDegree K.toGradedModule L.toGradedModule n)
    (g : GradedHomOfDegree L.toGradedModule M.toGradedModule m) :
    CategoryStruct.comp (X := K) (Y := L) (Z := M)
        (DirectSum.of (fun k => GradedHomOfDegree K.toGradedModule L.toGradedModule k) n f)
        (DirectSum.of (fun k => GradedHomOfDegree L.toGradedModule M.toGradedModule k) m g) =
      (DirectSum.of (fun k => GradedHomOfDegree K.toGradedModule M.toGradedModule k) (n + m)
        (g.comp f) : K ⟶ M) :=
  comp_of_of f g

/-- `Mod^gr(A)` is preadditive, with the addition of finite sums of homogeneous maps. -/
noncomputable instance instPreadditive : Preadditive (GradedModuleCat.{t, a, w} A) where
  homGroup X Y := inferInstanceAs (AddCommGroup (Hom X Y))
  add_comp M N P f g h :=
    congrArg (fun k : Hom N P →+ Hom M P => k h) ((comp M N P).map_add f g)
  comp_add M N P f g h := (comp M N P f).map_add g h

private theorem category_comp_smul_left (M N P : GradedModuleCat.{t, a, w} A)
    (r : Stacks.Cohomology.SiteModules.GlobalSectionRing R) (f : Hom M N) (g : Hom N P) :
    comp M N P (r • f) g = r • comp M N P f g := by
  induction f using DirectSum.induction_on with
  | of m f =>
    induction g using DirectSum.induction_on with
    | of n g =>
      rw [← DirectSum.of_smul, comp_of_of, comp_of_of, ← DirectSum.of_smul,
        GradedHomOfDegree.comp_smul]
    | _ => simp_all [smul_add]
  | _ => simp_all [smul_add, comp]

private theorem category_comp_smul_right (M N P : GradedModuleCat.{t, a, w} A) (f : Hom M N)
    (r : Stacks.Cohomology.SiteModules.GlobalSectionRing R) (g : Hom N P) :
    comp M N P f (r • g) = r • comp M N P f g := by
  induction f using DirectSum.induction_on with
  | of m f =>
    induction g using DirectSum.induction_on with
    | of n g =>
      rw [← DirectSum.of_smul, comp_of_of, comp_of_of, ← DirectSum.of_smul,
        GradedHomOfDegree.smul_comp]
    | _ => simp_all [smul_add]
  | _ => simp_all [smul_add, comp]

/-- `Mod^gr(A)` is linear over `R = Γ(C, O)`: composition is `R`-bilinear. -/
@[stacks 0FR1 "`Mod^gr(A)` is `R`-linear, `R = Γ(C, O)`"]
noncomputable instance instLinear :
    Linear (Stacks.Cohomology.SiteModules.GlobalSectionRing R) (GradedModuleCat.{t, a, w} A) where
  homModule X Y := inferInstanceAs
    (Module (Stacks.Cohomology.SiteModules.GlobalSectionRing R) (Hom X Y))
  smul_comp := by intros; apply category_comp_smul_left
  comp_smul := by intros; apply category_comp_smul_right

/-- **The graded category `Mod^gr(A)` over `R = Γ(C, O)` of Stacks 0FR1**: the degree-`n`
morphisms `L → M` are the homogeneous maps `Hom^n(L, M)`, identities have degree zero and
composition adds degrees. -/
@[stacks 0FR1 "`Mod^gr(A)` is a graded category over `R = Γ(C, O)` with degree-`n` morphisms
`Hom^n(L, M)`"]
noncomputable instance instGradedCategory :
    GradedCategory (Stacks.Cohomology.SiteModules.GlobalSectionRing R)
      (GradedModuleCat.{t, a, w} A) where
  grade L M := DirectSum.lofRange (R := Stacks.Cohomology.SiteModules.GlobalSectionRing R)
    (fun n => GradedHomOfDegree L.toGradedModule M.toGradedModule n)
  decomposition L M := DirectSum.lofRangeDecomposition _
  id_mem M := ⟨GradedHomOfDegree.id M.toGradedModule, rfl⟩
  comp_mem := by
    rintro K L M m n _ _ ⟨g, rfl⟩ ⟨f, rfl⟩
    change comp K L M (DirectSum.of _ n f) (DirectSum.of _ m g) ∈
      DirectSum.lofRange (R := Stacks.Cohomology.SiteModules.GlobalSectionRing R)
        (fun k => GradedHomOfDegree K.toGradedModule M.toGradedModule k) (m + n)
    rw [add_comm m n]
    exact ⟨g.comp f, (comp_of_of f g).symm⟩

/-- A morphism of `Mod^gr(A)` has degree `n` if and only if it is a single homogeneous map of
degree `n`. -/
theorem mem_grade_iff {L M : GradedModuleCat.{t, a, w} A} {n : ℤ} {f : L ⟶ M} :
    f ∈ GradedCategory.grade (R := Stacks.Cohomology.SiteModules.GlobalSectionRing R) L M n ↔
      ∃ g : GradedHomOfDegree L.toGradedModule M.toGradedModule n, DirectSum.of _ n g = f := Iff.rfl

/-- The degree-`n` part `Hom^n(L, M)` of a morphism of `Mod^gr(A)`. -/
noncomputable def degreePart {L M : GradedModuleCat.{t, a, w} A} (f : Hom L M) (n : ℤ) :
    GradedHomOfDegree L.toGradedModule M.toGradedModule n :=
  f n

/-- The degree-`n` part of a homogeneous morphism of degree `n` is that morphism. -/
@[simp]
theorem degreePart_of {L M : GradedModuleCat.{t, a, w} A} {n : ℤ}
    (f : GradedHomOfDegree L.toGradedModule M.toGradedModule n) :
    degreePart (DirectSum.of (fun k => GradedHomOfDegree L.toGradedModule M.toGradedModule k)
      n f) n = f :=
  DirectSum.of_eq_same n f

/-- The degree-`d` part of a homogeneous morphism of degree `n = d`, componentwise. -/
theorem degreePart_of_app {L M : GradedModuleCat.{t, a, w} A} {n d : ℤ} (h : n = d)
    (f : GradedHomOfDegree L.toGradedModule M.toGradedModule n) (i j : ℤ) (hij : i + d = j) :
    (degreePart (DirectSum.of (fun k => GradedHomOfDegree L.toGradedModule M.toGradedModule k)
      n f) d).app i j hij = f.app i j (by omega) := by
  subst h
  rw [degreePart_of]

open GradedCategory in
/-- A morphism of the degree-zero category `(Mod^gr(A))^0` is a single homogeneous map of
degree zero, its degree-zero part. -/
theorem degreeZero_eq_of {L M : GradedModuleCat.{t, a, w} A}
    (φ : DegreeZero.Hom (Stacks.Cohomology.SiteModules.GlobalSectionRing R)
      (GradedModuleCat.{t, a, w} A) L M) :
    φ.1 = DirectSum.of (fun k => GradedHomOfDegree L.toGradedModule M.toGradedModule k) 0
      (degreePart φ.1 0) := by
  obtain ⟨g, hg⟩ := φ.2
  rw [← hg, DirectSum.lof_eq_of]
  exact congrArg _ (degreePart_of g).symm

open GradedCategory in
/-- The functor from `(Mod^gr(A))^0` to the category of graded `A`-modules: a degree-zero
morphism is sent to its degree-zero part. -/
noncomputable def fromDegreeZero :
    DegreeZero (Stacks.Cohomology.SiteModules.GlobalSectionRing R) (GradedModuleCat.{t, a, w} A) ⥤
      GradedModule.{t, a, w} A where
  obj L := toGradedModule L
  map φ := (degreePart φ.1 0).toGradedModuleHom
  map_id L := GradedModule.Hom.ext fun n => by
    change (degreePart (L := L) (M := L)
      (DirectSum.of _ 0 (GradedHomOfDegree.id L.toGradedModule)) 0).app n n (add_zero n) = 𝟙 _
    rw [degreePart_of, GradedHomOfDegree.id_app_self]
  map_comp φ ψ := GradedModule.Hom.ext fun n => by
    obtain ⟨g, hg⟩ := φ.2
    obtain ⟨h, hh⟩ := ψ.2
    change (degreePart (comp _ _ _ φ.1 ψ.1) 0).app n n (add_zero n) =
      (degreePart φ.1 0).app n n (add_zero n) ≫ (degreePart ψ.1 0).app n n (add_zero n)
    rw [← hg, ← hh, DirectSum.lof_eq_of, DirectSum.lof_eq_of, comp_of_of,
      degreePart_of_app (zero_add 0), degreePart_of, degreePart_of,
      GradedHomOfDegree.comp_app_eq _ _ n n _ n (add_zero n)]

open GradedCategory in
/-- The functor from the category of graded `A`-modules to `(Mod^gr(A))^0`: a homomorphism is
sent to the homogeneous map of degree zero it defines. -/
noncomputable def toDegreeZero : GradedModule.{t, a, w} A ⥤
    DegreeZero (Stacks.Cohomology.SiteModules.GlobalSectionRing R)
      (GradedModuleCat.{t, a, w} A) where
  obj M := M
  map φ := ⟨DirectSum.of _ 0 (GradedHomOfDegree.ofGradedModuleHom φ), ⟨_, rfl⟩⟩
  map_id L := Subtype.ext
    (congrArg (DirectSum.of (fun k => GradedHomOfDegree L L k) 0)
      (GradedHomOfDegree.ofGradedModuleHom_id L))
  map_comp {K L M} φ ψ := Subtype.ext
    ((of_eq_of (L := K) (M := M) _ _ (by omega) fun i j hij =>
      (GradedHomOfDegree.ofGradedModuleHom_comp_app φ ψ i j _).symm).trans
      (comp_of_of (K := K) (L := L) (M := M) _ _).symm)

open GradedCategory in
/-- **The associated category of `Mod^gr(A)` (Stacks 0FR1)**: the degree-zero category
`(Mod^gr(A))^0` is equivalent to the category of graded `A`-modules, by the identity on objects;
a degree-zero morphism is its degree-zero part, a homomorphism of graded `A`-modules. -/
@[stacks 0FR1 "the associated category `(Mod^gr(A))^0` is the category of graded `A`-modules"]
noncomputable def degreeZeroEquivalence :
    DegreeZero (Stacks.Cohomology.SiteModules.GlobalSectionRing R) (GradedModuleCat.{t, a, w} A) ≌
      GradedModule.{t, a, w} A :=
  CategoryTheory.Equivalence.mk fromDegreeZero toDegreeZero
    (NatIso.ofComponents (fun L => Iso.refl L) fun φ => by
      refine (Category.comp_id φ).trans (Eq.trans ?_ (Category.id_comp _).symm)
      refine Subtype.ext ((degreeZero_eq_of φ).trans ?_)
      exact congrArg (DirectSum.of _ 0)
        (GradedHomOfDegree.ofGradedModuleHom_toGradedModuleHom _).symm)
    (NatIso.ofComponents (fun M => Iso.refl M) fun {L M} φ => by
      refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp φ).symm)
      exact (congrArg GradedHomOfDegree.toGradedModuleHom (degreePart_of (L := L) (M := M) _)).trans
        (GradedHomOfDegree.toGradedModuleHom_ofGradedModuleHom φ))

end GradedModuleCat

end SheafOfModules

end
