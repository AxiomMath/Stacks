module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Čech cohomology as a functor on presheaves of modules

Fix a ringed space `X = (X, O_X)`, an index set `I`, and an open set `U` together with an open
covering `U = ⋃_{i ∈ I} U_i`. For a tuple of indices `(i_0, …, i_p) ∈ I^{p+1}` write
`U_{i_0…i_p} = U_{i_0} ∩ … ∩ U_{i_p}` for the `(p+1)`-fold intersection. For every presheaf `F`
of `O_X`-modules the cochain complex `Hom_{O_X}(K(U)_•, F)` is isomorphic to the Čech complex
`Č^•(U, F)`, naturally in `F`, where `K(U)_•` is the chain complex with
`K(U)_p = ⨁_{(i_0,…,i_p) ∈ I^{p+1}} (j_{i_0…i_p})_{p!} O_{U_{i_0…i_p}}`.

The type of presheaves of `O_X`-modules is `StacksCechPresheaf.ModPresheaf`; all other names below
are in the namespace `StacksCechPresheaf.ModPresheaf`.

## Main definitions

* `extZeroOX`: the extension by zero `j_{p!} O_V` of the structure sheaf on an open `V`, with
  `(j_{p!} O_V)(W) = O_X(W)` if `W ⊆ V` and `0` otherwise.
* `extZeroCanonical`: the canonical map `(j_V)_{p!} O_V → (j_{V'})_{p!} O_{V'}` for `V ⊆ V'`.
* `Cover`: an open covering of an open subset of `X`.
* `KComplex`: the chain complex `K(U)_•`, supported in non-negative degrees, with the
  alternating-sum differential `Kdiff` built from the canonical maps.
* `CechComplex`: the Čech complex `Č^•(U, F)`, with
  `Č^p(U, F) = ∏_{(i_0,…,i_p) ∈ I^{p+1}} F(U_{i_0…i_p})` and differential
  `d(s)_{i_0…i_{p+1}} = ∑_j (-1)^j s_{i_0…ĵ…i_{p+1}}|_{U_{i_0…i_{p+1}}}`.
* `main_iso`: the natural isomorphism `Hom_{O_X}(K(U)_•, -) ≅ Č^•(U, -)`.

## Main results

* `adjEquiv_exists`: `Hom_{O_X}(j_{p!} O_V, F) ≅ F(V)`, by evaluation on `1 ∈ O_X(V)`.
* `main_theorem_exists`: the functors `F ↦ Hom_{O_X}(K(U)_•, F)` and `F ↦ Č^•(U, F)` are
  naturally isomorphic.

## Implementation notes

The category `PMod(O_X)` of presheaves of `O_X`-modules is modelled concretely by
`ModPresheaf X`: an object assigns to each
open `W` an `O_X(W)`-module, with compatible restriction maps, and a morphism is a family of
`O_X(W)`-linear maps compatible with restriction. The complexes are valued in `AddCommGrpCat`:
the isomorphism is one of complexes of abelian groups, and the `O_X(U)`-module structure is not
tracked.

## References

* [Stacks Project, Tag 01EL](https://stacks.math.columbia.edu/tag/01EL)
-/

open CategoryTheory TopologicalSpace Opposite

universe u

namespace StacksCechPresheaf

variable {X : AlgebraicGeometry.RingedSpace}

/-! ## The category `PMod(O_X)` of presheaves of `O_X`-modules -/

/-- The ring of sections `O_X(W)`. -/
abbrev sections (X : AlgebraicGeometry.RingedSpace) (W : Opens X.carrier) : CommRingCat :=
  X.presheaf.obj (op W)

/-- A presheaf of `O_X`-modules over a ringed space `X` (an object of `PMod(O_X)`): to each open
`W` it assigns an abelian group `obj W` that is a module over the ring of sections `O_X(W)`, with
restriction maps `res` that are additive, semilinear over the restriction map of `O_X`, and
compatible with identities and composition. -/
@[sga "3 I 3.1" "special case"]
structure ModPresheaf (X : AlgebraicGeometry.RingedSpace) where
  /-- The sections over an open `W`. -/
  obj : Opens X.carrier → Type u
  /-- The abelian group structure on the sections over `W`. -/
  addCommGroup : ∀ W, AddCommGroup (obj W)
  /-- The `O_X(W)`-module structure on the sections over `W`. -/
  module : ∀ W, Module (sections X W) (obj W)
  /-- Restriction of sections along `W ≤ W'`. -/
  res : ∀ {W W' : Opens X.carrier}, W ≤ W' → obj W' → obj W
  /-- Restriction is semilinear over the restriction map of `O_X`. -/
  map_smul : ∀ {W W'} (h : W ≤ W') (r : sections X W') (x : obj W'),
      res h (r • x) = (X.presheaf.map (homOfLE h).op r) • res h x
  /-- Restriction is additive. -/
  map_add : ∀ {W W'} (h : W ≤ W') (x y : obj W'), res h (x + y) = res h x + res h y
  /-- Restriction along `W ≤ W` is the identity. -/
  res_id : ∀ {W} (x : obj W), res (le_refl W) x = x
  /-- Restriction is compatible with composition of inclusions. -/
  res_comp : ∀ {W W' W''} (h : W ≤ W') (h' : W' ≤ W'') (x : obj W''),
      res (h.trans h') x = res h (res h' x)

attribute [instance] ModPresheaf.addCommGroup ModPresheaf.module

namespace ModPresheaf

/-- Restriction packaged as an additive group homomorphism. -/
def resHom (P : ModPresheaf X) {W W' : Opens X.carrier} (h : W ≤ W') : P.obj W' →+ P.obj W :=
  AddMonoidHom.mk' (P.res h) (P.map_add h)

/-- `resHom` is restriction. -/
@[simp] theorem resHom_apply (P : ModPresheaf X) {W W'} (h : W ≤ W') (x : P.obj W') :
    P.resHom h x = P.res h x := rfl

/-- Restriction maps `0` to `0`. -/
theorem res_zero (P : ModPresheaf X) {W W'} (h : W ≤ W') : P.res h (0 : P.obj W') = 0 :=
  (P.resHom h).map_zero

/-- Restriction commutes with negation. -/
theorem res_neg (P : ModPresheaf X) {W W'} (h : W ≤ W') (x : P.obj W') :
    P.res h (-x) = - P.res h x := (P.resHom h).map_neg x

/-- Restriction commutes with finite sums. -/
theorem res_sum (P : ModPresheaf X) {W W'} (h : W ≤ W') {ι} (s : Finset ι) (f : ι → P.obj W') :
    P.res h (∑ i ∈ s, f i) = ∑ i ∈ s, P.res h (f i) := map_sum (P.resHom h) f s

/-- Restriction commutes with integer multiples. -/
theorem res_zsmul (P : ModPresheaf X) {W W'} (h : W ≤ W') (z : ℤ) (x : P.obj W') :
    P.res h (z • x) = z • P.res h x := map_zsmul (P.resHom h) z x

end ModPresheaf

/-- A morphism of presheaves of `O_X`-modules `Hom_{O_X}(F, G)`: an `O_X(W)`-linear map on each
open `W`, compatible with restriction. -/
@[ext,
  sga "3 I 3.1" "morphisms",
  sga "4 IV 11.1.2" "partial"]
structure ModPresheaf.Hom (F G : ModPresheaf X) where
  /-- The `O_X(W)`-linear map on sections over `W`. -/
  app : ∀ W, F.obj W →ₗ[sections X W] G.obj W
  /-- The maps commute with restriction. -/
  naturality : ∀ {W W'} (h : W ≤ W') (x : F.obj W'),
      app W (F.res h x) = G.res h (app W' x)

namespace ModPresheaf
variable {F G H : ModPresheaf X}

/-- The identity morphism. -/
def Hom.id (F : ModPresheaf X) : Hom F F where
  app W := LinearMap.id
  naturality := by intro W W' h x; rfl

/-- Composition of morphisms. -/
def Hom.comp (f : Hom F G) (g : Hom G H) : Hom F H where
  app W := (g.app W).comp (f.app W)
  naturality := by intro W W' h x; simp only [LinearMap.comp_apply, f.naturality, g.naturality]

/-- Presheaves of `O_X`-modules form a category. -/
instance : Category (ModPresheaf X) where
  Hom F G := Hom F G
  id F := Hom.id F
  comp f g := Hom.comp f g

/-- Morphisms of presheaves of modules agree if they agree on every open. -/
@[ext] theorem hom_ext {f g : F ⟶ G} (h : ∀ W, f.app W = g.app W) : f = g := Hom.ext (funext h)

/-- The identity morphism is the identity on every open. -/
@[simp] theorem id_app (W) : (𝟙 F : Hom F F).app W = LinearMap.id := rfl
/-- Composition of morphisms is composition on every open. -/
@[simp] theorem comp_app (f : F ⟶ G) (g : G ⟶ H) (W) :
    (f ≫ g).app W = (g.app W).comp (f.app W) := rfl

/-! ### Additive (preadditive) structure on the morphism spaces -/

/-- The zero morphism. -/
instance : Zero (Hom F G) where
  zero := { app := fun _ => 0, naturality := by intro W W' h x; simp [G.res_zero] }

/-- The sum of two morphisms, taken on every open. -/
instance : Add (Hom F G) where
  add f g :=
    { app := fun W => f.app W + g.app W
      naturality := by
        intro W W' h x
        simp only [LinearMap.add_apply, f.naturality, g.naturality, G.map_add] }

/-- The negative of a morphism, taken on every open. -/
instance : Neg (Hom F G) where
  neg f :=
    { app := fun W => - f.app W
      naturality := by
        intro W W' h x
        simp only [LinearMap.neg_apply, f.naturality, G.res_neg] }

/-- The zero morphism is zero on every open. -/
@[simp] theorem zero_app (W) : (0 : Hom F G).app W = 0 := rfl
/-- A sum of morphisms is the sum on every open. -/
@[simp] theorem add_app (f g : Hom F G) (W) : (f + g).app W = f.app W + g.app W := rfl
/-- The negative of a morphism is the negative on every open. -/
@[simp] theorem neg_app (f : Hom F G) (W) : (-f).app W = - f.app W := rfl

/-- Morphisms of presheaves of modules form an abelian group. -/
instance : AddCommGroup (Hom F G) where
  add_assoc a b c := by ext W; simp [add_assoc]
  zero_add a := by ext W; simp
  add_zero a := by ext W; simp
  add_comm a b := by ext W; simp [add_comm]
  neg_add_cancel a := by ext W; simp
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The category of presheaves of modules is preadditive. -/
instance : Preadditive (ModPresheaf X) where
  homGroup F G := inferInstanceAs (AddCommGroup (Hom F G))
  add_comp := by
    intro P Q R f f' g
    apply hom_ext; intro W; ext x
    change (g.app W) ((f.app W) x + (f'.app W) x)
        = (g.app W) ((f.app W) x) + (g.app W) ((f'.app W) x)
    rw [(g.app W).map_add]
  comp_add := by
    intro P Q R f g g'
    apply hom_ext; intro W; ext x
    rfl

/-! ## Extension by zero `j_{p!} O_V` -/

open Classical in
/-- Underlying module of `(j_{p!} O_V)(W)`: the submodule `⊤` of `O_X(W)` (over itself) when
`W ⊆ V`, and `⊥` otherwise. -/
noncomputable def extZeroSub (X : AlgebraicGeometry.RingedSpace) (V W : Opens X.carrier) :
    Submodule (sections X W) (sections X W) :=
  if W ≤ V then ⊤ else ⊥

open Classical in
/-- For `W ⊆ V` the value `extZeroSub X V W` is all of `O_X(W)`. -/
theorem extZeroSub_eq_top {V W : Opens X.carrier} (h : W ≤ V) : extZeroSub X V W = ⊤ :=
  ite_eq_left h
open Classical in
/-- For `W ⊄ V` the value `extZeroSub X V W` is zero. -/
theorem extZeroSub_eq_bot {V W : Opens X.carrier} (h : ¬ W ≤ V) : extZeroSub X V W = ⊥ :=
  ite_eq_right h

/-- For `W ⊄ V` every element of `extZeroSub X V W` is zero. -/
theorem mem_extZeroSub_of_not_le {V W : Opens X.carrier}
    (hW : ¬ W ≤ V) (y : sections X W) (hy : y ∈ extZeroSub X V W) : y = 0 := by
  rw [extZeroSub_eq_bot hW] at hy; exact (Submodule.mem_bot _).1 hy

/-- Restriction along `W ≤ W'` maps `extZeroSub X V W'` into `extZeroSub X V W`. -/
theorem extZeroSub_res_mem (V : Opens X.carrier) {W W' : Opens X.carrier} (h : W ≤ W')
    (x : extZeroSub X V W') : (X.presheaf.map (homOfLE h).op) x.1 ∈ extZeroSub X V W := by
  by_cases hWV : W ≤ V
  · rw [extZeroSub_eq_top hWV]; trivial
  · have hW'V : ¬ W' ≤ V := fun hh => hWV (le_trans h hh)
    have hx : (x.1 : sections X W') = 0 := mem_extZeroSub_of_not_le hW'V _ x.2
    have hz : (X.presheaf.map (homOfLE h).op) x.1 = 0 := by rw [hx]; simp
    rw [hz]; exact Submodule.zero_mem _

/-- For `V ⊆ V'`, `extZeroSub X V W` is contained in `extZeroSub X V' W`. -/
theorem extZeroSub_mono_mem {V V' W : Opens X.carrier} (h : V ≤ V')
    (y : sections X W) (hy : y ∈ extZeroSub X V W) : y ∈ extZeroSub X V' W := by
  by_cases hWV' : W ≤ V'
  · rw [extZeroSub_eq_top hWV']; trivial
  · by_cases hWV : W ≤ V
    · exact absurd (le_trans hWV h) hWV'
    · have : y = 0 := mem_extZeroSub_of_not_le hWV y hy
      rw [this]; exact Submodule.zero_mem _

/-- The extension by zero `j_{p!} O_V` of the structure sheaf on `V`, as a presheaf of
`O_X`-modules: `(j_{p!} O_V)(W) = O_X(W)` for `W ⊆ V`, and `0` otherwise, with restriction maps
induced from those of `O_X`. -/
noncomputable def extZeroOX (X : AlgebraicGeometry.RingedSpace) (V : Opens X.carrier) :
    ModPresheaf X where
  obj W := extZeroSub X V W
  addCommGroup W := inferInstance
  module W := inferInstance
  res {W W'} h x := ⟨(X.presheaf.map (homOfLE h).op) x.1, extZeroSub_res_mem V h x⟩
  map_smul {W W'} h r x := by
    apply Subtype.ext
    change (X.presheaf.map (homOfLE h).op) ((r • x).1)
        = (X.presheaf.map (homOfLE h).op r) • ((X.presheaf.map (homOfLE h).op) x.1)
    have h1 : ((r • x : extZeroSub X V W').1) = r * x.1 := rfl
    rw [h1, map_mul]; rfl
  map_add {W W'} h x y := by apply Subtype.ext; simp
  res_id {W} x := by
    apply Subtype.ext; change (X.presheaf.map (homOfLE (le_refl W)).op) x.1 = x.1; simp
  res_comp {W W' W''} h h' x := by
    apply Subtype.ext
    change (X.presheaf.map (homOfLE (h.trans h')).op) x.1
        = (X.presheaf.map (homOfLE h).op) ((X.presheaf.map (homOfLE h').op) x.1)
    rw [← CategoryTheory.comp_apply, ← X.presheaf.map_comp]; rfl

/-- The underlying `O_X(W)`-linear map of `extZeroCanonical` on the open `W`: the inclusion
`(j_{p!} O_V)(W) → (j_{p!} O_{V'})(W)`. -/
noncomputable def extZeroCanonicalApp {V V' : Opens X.carrier} (h : V ≤ V') (W : Opens X.carrier) :
    (extZeroSub X V W) →ₗ[sections X W] (extZeroSub X V' W) where
  toFun x := ⟨x.1, extZeroSub_mono_mem h x.1 x.2⟩
  map_add' x y := by apply Subtype.ext; rfl
  map_smul' r x := by apply Subtype.ext; rfl

/-- For `V ⊆ V'`, the canonical map `(j_V)_{p!} O_V → (j_{V'})_{p!} O_{V'}` of presheaves of
`O_X`-modules (the identity where `W ⊆ V`, zero otherwise). Under the adjunction `adjEquiv_exists`
it corresponds to `1 ∈ O_X(V)`. -/
noncomputable def extZeroCanonical {V V' : Opens X.carrier} (h : V ≤ V') :
    extZeroOX X V ⟶ extZeroOX X V' where
  app W := extZeroCanonicalApp h W
  naturality := by intro W W' hh x; apply Subtype.ext; rfl

/-! ## The adjunction `Hom(j_{p!} O_V, F) ≅ F(V)` -/

variable {F G H : ModPresheaf X}

/-- The canonical section `1 ∈ (j_{p!} O_V)(V) = O_X(V)`. -/
noncomputable def extZeroOne (V : Opens X.carrier) : (extZeroOX X V).obj V :=
  ⟨(1 : sections X V), by
    show (1 : sections X V) ∈ extZeroSub X V V
    rw [extZeroSub_eq_top (le_refl V)]; trivial⟩

/-- Forward map of the adjunction `Hom_{O_X}(j_{p!} O_V, F) → F(V)`, given by evaluating a morphism
on the canonical section `1 ∈ O_X(V)`. -/
noncomputable def adjForward (V : Opens X.carrier) (F : ModPresheaf X)
    (φ : extZeroOX X V ⟶ F) : F.obj V := φ.app V (extZeroOne V)

open Classical in
/-- The component at `W` of the morphism `j_{p!} O_V → F` associated to a section `s ∈ F(V)`: the
`O_X(W)`-linear map `x ↦ x · (s|_W)` for `W ⊆ V` (and `0` for `W ⊄ V`, where the domain is `0`). -/
noncomputable def adjInverseApp (V : Opens X.carrier) (F : ModPresheaf X) (s : F.obj V)
    (W : Opens X.carrier) : (extZeroOX X V).obj W →ₗ[sections X W] F.obj W where
  toFun x := if h : W ≤ V then (x.1 : sections X W) • F.res h s else 0
  map_add' x y := by
    by_cases h : W ≤ V
    · simp only [dite_eq_left h]
      have : ((x + y : (extZeroOX X V).obj W).1 : sections X W) = x.1 + y.1 := rfl
      rw [this, add_smul]
    · simp only [dite_eq_right h, add_zero]
  map_smul' r x := by
    by_cases h : W ≤ V
    · simp only [dite_eq_left h, RingHom.id_apply]
      change ((r • x).1 : sections X W) • F.res h s = r • ((x.1 : sections X W) • F.res h s)
      have : ((r • x : (extZeroOX X V).obj W).1 : sections X W) = r * x.1 := rfl
      rw [this, mul_smul]
    · simp only [dite_eq_right h, smul_zero]

open Classical in
/-- Inverse map of the adjunction `F(V) → Hom_{O_X}(j_{p!} O_V, F)`. -/
noncomputable def adjInverse (V : Opens X.carrier) (F : ModPresheaf X) (s : F.obj V) :
    extZeroOX X V ⟶ F where
  app W := adjInverseApp V F s W
  naturality := by
    intro W W' h x
    by_cases hW'V : W' ≤ V
    · have hWV : W ≤ V := le_trans h hW'V
      change (if hh : W ≤ V then ((X.presheaf.map (homOfLE h).op) x.1 : sections X W) • F.res hh s
            else 0)
          = F.res h (if hh : W' ≤ V then (x.1 : sections X W') • F.res hh s else 0)
      rw [dite_eq_left hWV, dite_eq_left hW'V, F.map_smul h x.1 (F.res hW'V s),
          ← F.res_comp h hW'V s]
    · have hzero : ((X.presheaf.map (homOfLE h).op) x.1 : sections X W) = 0 := by
        have hx0 : (x.1 : sections X W') = 0 := mem_extZeroSub_of_not_le hW'V _ x.2
        rw [hx0]; simp
      change (if hh : W ≤ V then ((X.presheaf.map (homOfLE h).op) x.1 : sections X W) • F.res hh s
            else 0)
          = F.res h (if hh : W' ≤ V then (x.1 : sections X W') • F.res hh s else 0)
      rw [dite_eq_right hW'V, F.res_zero]
      by_cases hWV : W ≤ V
      · rw [dite_eq_left hWV, hzero, zero_smul]
      · rw [dite_eq_right hWV]

/-- For every presheaf `F` of `O_X`-modules there is an additive isomorphism
`Hom_{O_X}(j_{p!} O_V, F) ≅ F(V)` whose forward map is evaluation on `1 ∈ O_X(V)` (`adjForward`)
and whose inverse is `adjInverse`. This is the adjunction `j_{p!} ⊣ (·|_V)` evaluated at `O_V`. -/
theorem adjEquiv_exists (V : Opens X.carrier) (F : ModPresheaf X) :
    ∃ e : (extZeroOX X V ⟶ F) ≃+ F.obj V,
      (∀ φ, e φ = adjForward V F φ) ∧ (∀ s, e.symm s = adjInverse V F s) := by
  classical
  refine ⟨⟨⟨adjForward V F, adjInverse V F, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro φ
    refine hom_ext fun W => ?_
    refine LinearMap.ext fun x => ?_
    change adjInverseApp V F (adjForward V F φ) W x = φ.app W x
    change (if h : W ≤ V then (x.1 : sections X W) • F.res h (adjForward V F φ) else 0)
        = φ.app W x
    by_cases h : W ≤ V
    · rw [dite_eq_left h]
      change (x.1 : sections X W) • F.res h (φ.app V (extZeroOne V)) = φ.app W x
      rw [← φ.naturality h (extZeroOne V), ← (φ.app W).map_smul]
      congr 1
      apply Subtype.ext
      change (x.1 : sections X W) * (X.presheaf.map (homOfLE h).op) (extZeroOne V).1 = x.1
      change (x.1 : sections X W) * (X.presheaf.map (homOfLE h).op) (1 : sections X V) = x.1
      rw [map_one, mul_one]
    · rw [dite_eq_right h]
      have hx0 : (x.1 : sections X W) = 0 := mem_extZeroSub_of_not_le h _ x.2
      have hx : x = 0 := Subtype.ext hx0
      rw [hx, map_zero]
  · intro s
    change (adjInverse V F s).app V (extZeroOne V) = s
    change adjInverseApp V F s V (extZeroOne V) = s
    change (if h : V ≤ V then ((extZeroOne V).1 : sections X V) • F.res h s else 0) = s
    rw [dite_eq_left (le_refl V)]
    change ((1 : sections X V) • F.res (le_refl V) s) = s
    rw [F.res_id, one_smul]
  · intro φ ψ
    change (φ + ψ).app V (extZeroOne V) = φ.app V (extZeroOne V) + ψ.app V (extZeroOne V)
    rw [add_app]; rfl
  · intro φ; rfl
  · intro s; rfl

/-- The adjunction isomorphism `Hom_{O_X}(j_{p!} O_V, -) ≅ (-)(V)` is natural in the presheaf
argument: for a morphism `α : F ⟶ G` of presheaves of `O_X`-modules and a morphism
`φ : j_{p!} O_V ⟶ F`, evaluating the post-composed morphism `φ ≫ α` on `1 ∈ O_X(V)` is the same as
applying `α` on sections over `V` to the evaluation of `φ`. In other words, the naturality square
`F(V) → G(V)` versus `Hom(j_{p!} O_V, F) → Hom(j_{p!} O_V, G)` commutes. -/
theorem adjForward_naturality (V : Opens X.carrier) {F G : ModPresheaf X} (α : F ⟶ G)
    (φ : extZeroOX X V ⟶ F) :
    adjForward V G (φ ≫ α) = α.app V (adjForward V F φ) :=
  rfl

/-! ## Indexing and intersections -/

section Indexing
variable {I : Type u}

/-- An open covering of an open subset of `X` by a family of opens indexed by `I`: the data of the
covered open `carrierOpen`, the family `obj : I → Opens X` of the `U_i`, and the covering
hypothesis `carrierOpen = ⨆ i, obj i` (i.e. `U = ⋃_i U_i`). -/
structure Cover (X : AlgebraicGeometry.RingedSpace) (I : Type u) where
  /-- The covered open set `U ⊆ X`. -/
  carrierOpen : Opens X.carrier
  /-- The family of opens `U_i` indexed by `I`. -/
  obj : I → Opens X.carrier
  /-- The covering condition `U = ⋃_i U_i`. -/
  covers : carrierOpen = ⨆ i, obj i

/-- The `(p+1)`-fold intersection `U_{i_0…i_p} = ⨅_k U_{σ k}` for a tuple `σ : Fin (p+1) → I`. -/
@[sga "4½ Arcata 6.1"]
def interOpens (U : Cover X I) {p : ℕ} (σ : Fin (p + 1) → I) : Opens X.carrier := ⨅ k, U.obj (σ k)

/-- Deleting the `j`-th index from a `(p+2)`-tuple yields a `(p+1)`-tuple `(i_0…ĵ…i_{p+1})`. -/
def omitIdx {p : ℕ} (σ : Fin (p + 2) → I) (j : Fin (p + 2)) : Fin (p + 1) → I :=
  fun k => σ (j.succAbove k)

/-- The intersection over a tuple is contained in the intersection over any of its faces:
`U_{i_0…i_{p+1}} ⊆ U_{i_0…ĵ…i_{p+1}}`. -/
theorem interOpens_le_omitIdx (U : Cover X I) {p : ℕ} (σ : Fin (p + 2) → I) (j : Fin (p + 2)) :
    interOpens U σ ≤ interOpens U (omitIdx σ j) := by
  apply le_iInf; intro k; exact iInf_le _ (j.succAbove k)

end Indexing

/-! ## The chain complex `K(U)_•`

The term in degree `p` is the direct sum `K(U)_p = ⨁_{σ : Fin (p+1) → I} (j_σ)_{p!} O_{U_σ}`,
formed as a genuine object of `PMod(O_X)`: its sections over `W` are the direct sum of the
sections of the summands, with componentwise restriction. -/

section Complex
variable {I : Type u}

/-- Sections over `W` of the direct-sum term `K(U)_p`. -/
abbrev KtermObj (U : Cover X I) (p : ℕ) (W : Opens X.carrier) : Type u :=
  DirectSum (Fin (p + 1) → I) (fun σ => (extZeroOX X (interOpens U σ)).obj W)

open Classical in
/-- The degree-`p` term `K(U)_p = ⨁_σ (j_σ)_{p!} O_{U_σ}` as a presheaf of `O_X`-modules. -/
noncomputable def Kterm (U : Cover X I) (p : ℕ) : ModPresheaf X where
  obj W := KtermObj U p W
  addCommGroup W := inferInstance
  module W := inferInstance
  res {W W'} h := DirectSum.map (fun σ => (extZeroOX X (interOpens U σ)).resHom h)
  map_smul {W W'} h r x := by
    refine DirectSum.induction_on x ?_ ?_ ?_
    · rw [smul_zero, (DirectSum.map _).map_zero, smul_zero]
    · intro σ y
      rw [← DirectSum.of_smul, DirectSum.map_of, DirectSum.map_of, ← DirectSum.of_smul]
      congr 1
      change (extZeroOX X (interOpens U σ)).resHom h (r • y)
          = (X.presheaf.map (homOfLE h).op r) • (extZeroOX X (interOpens U σ)).resHom h y
      simp only [resHom_apply]
      exact (extZeroOX X (interOpens U σ)).map_smul h r y
    · intro a b ha hb
      rw [smul_add, (DirectSum.map _).map_add, (DirectSum.map _).map_add, ha, hb, smul_add]
  map_add {W W'} h x y := (DirectSum.map _).map_add x y
  res_id {W} x := by
    refine DirectSum.induction_on x ?_ ?_ ?_
    · rw [(DirectSum.map _).map_zero]
    · intro σ y
      rw [DirectSum.map_of]
      congr 1
      change (extZeroOX X (interOpens U σ)).resHom (le_refl W) y = y
      simp only [resHom_apply]; exact (extZeroOX X (interOpens U σ)).res_id y
    · intro a b ha hb; rw [(DirectSum.map _).map_add, ha, hb]
  res_comp {W W' W''} h h' x := by
    refine DirectSum.induction_on x ?_ ?_ ?_
    · rw [(DirectSum.map _).map_zero, (DirectSum.map _).map_zero, (DirectSum.map _).map_zero]
    · intro σ y
      rw [DirectSum.map_of, DirectSum.map_of, DirectSum.map_of]
      congr 1
      change (extZeroOX X (interOpens U σ)).resHom (h.trans h') y
          = (extZeroOX X (interOpens U σ)).resHom h ((extZeroOX X (interOpens U σ)).resHom h' y)
      simp only [resHom_apply]; exact (extZeroOX X (interOpens U σ)).res_comp h h' y
    · intro a b ha hb
      rw [(DirectSum.map _).map_add, ha, hb, (DirectSum.map _).map_add, (DirectSum.map _).map_add]

open Classical in
/-- The image in `K(U)_p` (over `W`) of a single summand `(j_σ)_{p!} O_{U_σ}` of `K(U)_{p+1}` under
the differential: `∑_{j} (-1)^j ·` (canonical map into the `(omitIdx σ j)`-summand). -/
noncomputable def KdiffSummand (U : Cover X I) (p : ℕ) (W : Opens X.carrier)
    (σ : Fin (p + 2) → I) :
    (extZeroOX X (interOpens U σ)).obj W →ₗ[sections X W] KtermObj U p W :=
  ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
    (DirectSum.lof (sections X W) (Fin (p + 1) → I)
        (fun τ => (extZeroOX X (interOpens U τ)).obj W) (omitIdx σ j)).comp
      (extZeroCanonicalApp (interOpens_le_omitIdx U σ j) W)

open Classical in
/-- The component at `W` of the differential `K(U)_{p+1} → K(U)_p`. -/
noncomputable def KdiffApp (U : Cover X I) (p : ℕ) (W : Opens X.carrier) :
    KtermObj U (p + 1) W →ₗ[sections X W] KtermObj U p W :=
  DirectSum.toModule (sections X W) (Fin (p + 2) → I) (KtermObj U p W)
    (fun σ => KdiffSummand U p W σ)

/-- The differential component `KdiffApp` commutes with restriction. -/
theorem KdiffApp_naturality (U : Cover X I) (p : ℕ) {W W' : Opens X.carrier} (h : W ≤ W')
    (x : (Kterm U (p + 1)).obj W') :
    KdiffApp U p W ((Kterm U (p + 1)).res h x)
      = (Kterm U p).res h (KdiffApp U p W' x) := by
  classical
  refine DirectSum.induction_on x ?_ ?_ ?_
  · change KdiffApp U p W ((Kterm U (p + 1)).res h 0)
        = (Kterm U p).res h (KdiffApp U p W' 0)
    rw [(Kterm U (p + 1)).res_zero, (KdiffApp U p W).map_zero,
        (KdiffApp U p W').map_zero, (Kterm U p).res_zero]
  · intro σ y
    show KdiffApp U p W ((Kterm U (p + 1)).res h (DirectSum.of _ σ y))
        = (Kterm U p).res h (KdiffApp U p W' (DirectSum.of _ σ y))
    rw [show (Kterm U (p + 1)).res h (DirectSum.of _ σ y)
          = DirectSum.map (fun σ => (extZeroOX X (interOpens U σ)).resHom h)
              (DirectSum.of _ σ y) from rfl,
        DirectSum.map_of]
    change KdiffApp U p W (DirectSum.of _ σ ((extZeroOX X (interOpens U σ)).resHom h y))
        = (Kterm U p).res h (KdiffApp U p W' (DirectSum.of _ σ y))
    rw [show KdiffApp U p W (DirectSum.of _ σ ((extZeroOX X (interOpens U σ)).resHom h y))
          = KdiffSummand U p W σ ((extZeroOX X (interOpens U σ)).resHom h y) from
        DirectSum.toModule_lof _ _ _,
        show KdiffApp U p W' (DirectSum.of _ σ y)
          = KdiffSummand U p W' σ y from DirectSum.toModule_lof _ _ _]
    simp only [KdiffSummand, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
      LinearMap.comp_apply]
    rw [(Kterm U p).res_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [(Kterm U p).res_zsmul]
    congr 1
    change DirectSum.lof (sections X W) (Fin (p + 1) → I)
            (fun τ => (extZeroOX X (interOpens U τ)).obj W) (omitIdx σ j)
            (extZeroCanonicalApp (interOpens_le_omitIdx U σ j) W
              ((extZeroOX X (interOpens U σ)).resHom h y))
        = (Kterm U p).res h
            (DirectSum.lof (sections X W') (Fin (p + 1) → I)
              (fun τ => (extZeroOX X (interOpens U τ)).obj W') (omitIdx σ j)
              (extZeroCanonicalApp (interOpens_le_omitIdx U σ j) W' y))
    rw [show (Kterm U p).res h
            (DirectSum.lof (sections X W') (Fin (p + 1) → I)
              (fun τ => (extZeroOX X (interOpens U τ)).obj W') (omitIdx σ j)
              (extZeroCanonicalApp (interOpens_le_omitIdx U σ j) W' y))
          = DirectSum.map (fun τ => (extZeroOX X (interOpens U τ)).resHom h)
              (DirectSum.of _ (omitIdx σ j)
                (extZeroCanonicalApp (interOpens_le_omitIdx U σ j) W' y)) from rfl,
        DirectSum.map_of]
    change DirectSum.of (fun τ => (extZeroOX X (interOpens U τ)).obj W) (omitIdx σ j)
            (extZeroCanonicalApp (interOpens_le_omitIdx U σ j) W
              ((extZeroOX X (interOpens U σ)).resHom h y))
        = DirectSum.of (fun τ => (extZeroOX X (interOpens U τ)).obj W) (omitIdx σ j)
            ((extZeroOX X (interOpens U (omitIdx σ j))).resHom h
              (extZeroCanonicalApp (interOpens_le_omitIdx U σ j) W' y))
    congr 1
  · intro a b ha hb
    show KdiffApp U p W ((Kterm U (p + 1)).res h (a + b))
        = (Kterm U p).res h (KdiffApp U p W' (a + b))
    rw [(Kterm U (p + 1)).map_add, (KdiffApp U p W).map_add,
        (KdiffApp U p W').map_add, (Kterm U p).map_add, ha, hb]

open Classical in
/-- The differential `∂_{p+1} : K(U)_{p+1} → K(U)_p`, a morphism of presheaves of `O_X`-modules: on
the summand indexed by a `(p+2)`-tuple `σ` it is the alternating sum `∑_j (-1)^j` of the canonical
maps `extZeroCanonical` into the summands of `K(U)_p` indexed by the faces `omitIdx σ j`. -/
@[sga "4 V 1.10" "special case"]
noncomputable def Kdiff (U : Cover X I) (p : ℕ) : Kterm U (p + 1) ⟶ Kterm U p where
  app W := KdiffApp U p W
  naturality h x := KdiffApp_naturality U p h x

/-- Pointwise simplicial identity for `Fin.succAbove`: omitting index `i` then `j` is the same face
as omitting `i.succAbove j` then `j.predAbove i`. -/
private theorem succAbove_face_eq (p : ℕ) (i : Fin (p + 3)) (j : Fin (p + 2)) (l : Fin (p + 1)) :
    i.succAbove (j.succAbove l) = (i.succAbove j).succAbove ((j.predAbove i).succAbove l) := by
  apply Fin.ext
  have hi := i.isLt; have hj := j.isLt; have hl := l.isLt
  simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, apply_dite Fin.val, apply_ite Fin.val,
    Fin.val_castSucc, Fin.val_succ, Fin.val_pred, Fin.coe_castPred]
  split_ifs <;> omega

/-- The pair of signs reverses under the simplicial involution
`(i,j) ↦ (i.succAbove j, j.predAbove i)`. -/
private theorem sign_face_neg (p : ℕ) (i : Fin (p + 3)) (j : Fin (p + 2)) :
    ((-1:ℤ)^(i.succAbove j).val * (-1:ℤ)^(j.predAbove i).val)
      = -((-1:ℤ)^(i.val) * (-1:ℤ)^(j.val)) := by
  rw [← pow_add, ← pow_add]
  have key : (i.succAbove j).val + (j.predAbove i).val + 1 = i.val + j.val ∨
             (i.succAbove j).val + (j.predAbove i).val = i.val + j.val + 1 := by
    have hi := i.isLt; have hj := j.isLt
    simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, apply_dite Fin.val, apply_ite Fin.val,
      Fin.val_castSucc, Fin.val_succ, Fin.val_pred, Fin.coe_castPred]
    split_ifs <;> omega
  rcases key with h | h
  · rw [← h, pow_succ]; ring
  · rw [h, pow_succ]; ring

/-- Abstract simplicial `d∘d = 0`: a doubly-indexed signed sum of terms depending only on the
composite face vanishes via the sign-reversing involution `(i,j) ↦ (i.succAbove j, j.predAbove i)`.
-/
theorem abstract_dd_zero (p : ℕ) {M : Type*} [AddCommGroup M]
    (a : Fin (p + 3) → Fin (p + 2) → M)
    (hface : ∀ i j, a i j = a (i.succAbove j) (j.predAbove i)) :
    (∑ i : Fin (p+3), ∑ j : Fin (p+2),
       ((-1:ℤ)^(i:ℕ) * (-1:ℤ)^(j:ℕ)) • a i j) = 0 := by
  rw [← Fintype.sum_prod_type']
  refine Finset.sum_involution
    (fun x _ => (x.1.succAbove x.2, x.2.predAbove x.1)) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ -
    simp only
    rw [← hface, sign_face_neg, neg_smul, add_neg_cancel]
  · rintro ⟨i, j⟩ - _
    simp only [ne_eq, Prod.mk.injEq, not_and]
    intro hi
    exact absurd hi (Fin.succAbove_ne i j)
  · intro x _; exact Finset.mem_univ _
  · rintro ⟨i, j⟩ -
    simp only [Prod.mk.injEq]
    refine ⟨Fin.succAbove_succAbove_predAbove i j, ?_⟩
    apply Fin.ext
    have hi := i.isLt; have hj := j.isLt
    simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, apply_dite Fin.val, apply_ite Fin.val,
      Fin.val_castSucc, Fin.val_succ, Fin.val_pred, Fin.coe_castPred]
    split_ifs <;> omega

/-- The composite face `omitIdx (omitIdx σ i) j` equals
`omitIdx (omitIdx σ (i.succAbove j)) (j.predAbove i)` (the simplicial identity, pointwise on the
tuple). -/
private theorem omitIdx_omitIdx_face {p : ℕ} (σ : Fin (p + 3) → I)
    (i : Fin (p + 3)) (j : Fin (p + 2)) :
    omitIdx (omitIdx σ i) j
      = omitIdx (omitIdx σ (i.succAbove j)) (j.predAbove i) := by
  funext l
  change σ (i.succAbove (j.succAbove l)) = σ ((i.succAbove j).succAbove ((j.predAbove i).succAbove
      l))
  rw [succAbove_face_eq]

/-- The intersection over a tuple is contained in the intersection over any twice-omitted tuple. -/
private theorem interOpens_le_omitIdx_omitIdx (U : Cover X I) {p : ℕ} (σ : Fin (p + 3) → I)
    (i : Fin (p + 3)) (j : Fin (p + 2)) :
    interOpens U σ ≤ interOpens U (omitIdx (omitIdx σ i) j) :=
  (interOpens_le_omitIdx U σ i).trans (interOpens_le_omitIdx U (omitIdx σ i) j)

/-- Anything depending on the twice-omitted tuple (and the inclusion into it) satisfies the
simplicial face identity. -/
private theorem apply_omitIdx_omitIdx_face {M : Sort*} (U : Cover X I) {p : ℕ}
    (σ : Fin (p + 3) → I) (f : ∀ τ : Fin (p + 1) → I, interOpens U σ ≤ interOpens U τ → M)
    (i : Fin (p + 3)) (j : Fin (p + 2)) :
    f (omitIdx (omitIdx σ i) j) (interOpens_le_omitIdx_omitIdx U σ i j)
      = f (omitIdx (omitIdx σ (i.succAbove j)) (j.predAbove i))
        (interOpens_le_omitIdx_omitIdx U σ _ _) := by
  have key : ∀ τ τ' (h : τ = τ') h₁ h₂, f τ h₁ = f τ' h₂ := by
    rintro _ _ rfl _ _; rfl
  exact key _ _ (omitIdx_omitIdx_face σ i j) _ _

/-- The differential of `K(U)_•` squares to zero: `∂_p ∘ ∂_{p+1} = 0`. -/
theorem Kdiff_comp_Kdiff (U : Cover X I) (p : ℕ) :
    Kdiff U (p + 1) ≫ Kdiff U p = 0 := by
  classical
  refine hom_ext fun W => ?_
  change (Kdiff U (p + 1) ≫ Kdiff U p).app W = (0 : Kterm U (p + 1 + 1) ⟶ Kterm U p).app W
  rw [comp_app, zero_app]
  refine DirectSum.linearMap_ext (sections X W) ?_
  intro σ
  refine LinearMap.ext fun x => ?_
  change (KdiffApp U p W) ((KdiffApp U (p + 1) W)
      (DirectSum.lof (sections X W) (Fin (p + 1 + 1 + 1) → I)
        (fun τ => (extZeroOX X (interOpens U τ)).obj W) σ x)) = 0
  rw [show (KdiffApp U (p + 1) W) = DirectSum.toModule (sections X W) (Fin (p + 3) → I)
        (KtermObj U (p + 1) W) (fun σ => KdiffSummand U (p + 1) W σ) from rfl,
    DirectSum.toModule_lof]
  have hle := interOpens_le_omitIdx_omitIdx U σ
  change (KdiffApp U p W) (KdiffSummand U (p + 1) W σ x) = 0
  rw [show KdiffSummand U (p + 1) W σ x
      = ∑ i : Fin (p + 3), (-1 : ℤ) ^ (i : ℕ) •
          DirectSum.lof (sections X W) (Fin (p + 1 + 1) → I)
            (fun τ => (extZeroOX X (interOpens U τ)).obj W) (omitIdx σ i)
            (extZeroCanonicalApp (interOpens_le_omitIdx U σ i) W x) from by
        rw [KdiffSummand, LinearMap.coe_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rfl]
  rw [map_sum]
  rw [show (0 : KtermObj U p W)
      = ∑ i : Fin (p + 3), ∑ j : Fin (p + 2),
          ((-1 : ℤ) ^ (i : ℕ) * (-1 : ℤ) ^ (j : ℕ)) •
            DirectSum.lof (sections X W) (Fin (p + 1) → I)
              (fun τ => (extZeroOX X (interOpens U τ)).obj W) (omitIdx (omitIdx σ i) j)
              (extZeroCanonicalApp (hle i j) W x) from
      (abstract_dd_zero p (fun i j => DirectSum.lof (sections X W) (Fin (p + 1) → I)
        (fun τ => (extZeroOX X (interOpens U τ)).obj W) (omitIdx (omitIdx σ i) j)
        (extZeroCanonicalApp (hle i j) W x)) (by
          intro i j
          exact apply_omitIdx_omitIdx_face U σ (fun τ h => DirectSum.lof (sections X W)
            (Fin (p + 1) → I) (fun τ => (extZeroOX X (interOpens U τ)).obj W) τ
            (extZeroCanonicalApp h W x)) i j)).symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul_of_tower,
    show (KdiffApp U p W) (DirectSum.lof (sections X W) (Fin (p + 2) → I)
        (fun τ => (extZeroOX X (interOpens U τ)).obj W) (omitIdx σ i)
        (extZeroCanonicalApp (interOpens_le_omitIdx U σ i) W x))
      = KdiffSummand U p W (omitIdx σ i)
          (extZeroCanonicalApp (interOpens_le_omitIdx U σ i) W x) from
      DirectSum.toModule_lof _ _ _]
  rw [show KdiffSummand U p W (omitIdx σ i)
        (extZeroCanonicalApp (interOpens_le_omitIdx U σ i) W x)
      = ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
          DirectSum.lof (sections X W) (Fin (p + 1) → I)
            (fun τ => (extZeroOX X (interOpens U τ)).obj W) (omitIdx (omitIdx σ i) j)
            (extZeroCanonicalApp (hle i j) W x) from by
        rw [KdiffSummand, LinearMap.coe_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [LinearMap.smul_apply, LinearMap.comp_apply]
        congr 1]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]

/-- The homologically graded chain complex of presheaves of `O_X`-modules with `K(U)_p` in degree
`p ≥ 0` and the alternating-sum differential `∂`. -/
noncomputable def KComplex (U : Cover X I) : ChainComplex (ModPresheaf X) ℕ :=
  ChainComplex.of (Kterm U) (Kdiff U) (Kdiff_comp_Kdiff U)

/-! ## The Hom-complex `Hom_{O_X}(K(U)_•, F)`

Applying the contravariant additive functor `Hom_{O_X}(-, F) = preadditiveYoneda.obj F` to the
chain complex `K(U)_•` gives the cochain complex whose degree-`p` term is
`Hom_{O_X}(K(U)_p, F)` and whose codifferential is precomposition with `∂_{p+1}`. -/

/-- The cochain complex `Hom_{O_X}(K(U)_•, F)`: the image of the chain complex `K(U)_•` under the
contravariant Hom-functor `Hom_{O_X}(-, F)`. -/
@[sga "4 V 2.3.3" "C^•(U, special case"]
noncomputable def HomComplex (U : Cover X I) (F : ModPresheaf X) :
    HomologicalComplex AddCommGrpCat (ComplexShape.down ℕ).symm :=
  ((preadditiveYoneda.obj F).mapHomologicalComplex _).obj (KComplex U).op

/-! ## The Čech complex `Č^•(U, F)` -/

/-- Degree-`p` term of the Čech complex: `Č^p(U, F) = ∏_{σ : Fin (p+1) → I} F(U_σ)`. -/
@[sga "4 V 2.4.3" "partial"]
abbrev CechObj (U : Cover X I) (F : ModPresheaf X) (p : ℕ) : Type u :=
  ∀ σ : Fin (p + 1) → I, F.obj (interOpens U σ)

/-- The Čech differential `d : Č^p(U, F) → Č^{p+1}(U, F)` as an additive group homomorphism:
`d(s)_{i_0…i_{p+1}} = ∑_j (-1)^j s_{i_0…ĵ…i_{p+1}}|_{U_{i_0…i_{p+1}}}`. -/
@[sga "4 V 2.4.3" "partial"]
noncomputable def cechDiffHom (U : Cover X I) (F : ModPresheaf X) (p : ℕ) :
    CechObj U F p →+ CechObj U F (p + 1) where
  toFun s := fun σ =>
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      F.res (interOpens_le_omitIdx U σ j) (s (omitIdx σ j))
  map_zero' := by
    funext σ
    apply Finset.sum_eq_zero
    intro j _
    change (-1 : ℤ) ^ (j : ℕ) • F.res (interOpens_le_omitIdx U σ j)
        ((0 : CechObj U F p) (omitIdx σ j)) = 0
    rw [show ((0 : CechObj U F p) (omitIdx σ j)) = 0 from rfl, F.res_zero, smul_zero]
  map_add' s t := by
    funext σ
    change (∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
          F.res (interOpens_le_omitIdx U σ j) ((s + t) (omitIdx σ j)))
        = (∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
            F.res (interOpens_le_omitIdx U σ j) (s (omitIdx σ j)))
          + ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
            F.res (interOpens_le_omitIdx U σ j) (t (omitIdx σ j))
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    change (-1 : ℤ) ^ (j : ℕ) • F.res (interOpens_le_omitIdx U σ j)
          (s (omitIdx σ j) + t (omitIdx σ j))
        = (-1 : ℤ) ^ (j : ℕ) • F.res (interOpens_le_omitIdx U σ j) (s (omitIdx σ j))
          + (-1 : ℤ) ^ (j : ℕ) • F.res (interOpens_le_omitIdx U σ j) (t (omitIdx σ j))
    rw [F.map_add, smul_add]

/-- The Čech codifferential as an `AddCommGrpCat` morphism. -/
@[sga "4 V 2.4.3" "partial"]
noncomputable def cechDiffMor (U : Cover X I) (F : ModPresheaf X) (p : ℕ) :
    AddCommGrpCat.of (CechObj U F p) ⟶ AddCommGrpCat.of (CechObj U F (p + 1)) :=
  AddCommGrpCat.ofHom (cechDiffHom U F p)

/-- The Čech differential squares to zero. -/
theorem cechDiff_comp_cechDiff (U : Cover X I) (F : ModPresheaf X) (p : ℕ) :
    cechDiffMor U F p ≫ cechDiffMor U F (p + 1) = 0 := by
  apply AddCommGrpCat.hom_ext
  ext s σ
  change (cechDiffHom U F (p+1)) (cechDiffHom U F p s) σ = (0 : CechObj U F (p+2)) σ
  change (∑ i : Fin (p+3), (-1 : ℤ) ^ (i : ℕ) •
      F.res (interOpens_le_omitIdx U σ i) ((cechDiffHom U F p s) (omitIdx σ i)))
    = (0 : CechObj U F (p+2)) σ
  change (∑ i : Fin (p+3), (-1 : ℤ) ^ (i : ℕ) •
      F.res (interOpens_le_omitIdx U σ i) ((cechDiffHom U F p s) (omitIdx σ i)))
    = 0
  have hle := interOpens_le_omitIdx_omitIdx U σ
  have hstep : ∀ i : Fin (p+3),
      (-1 : ℤ) ^ (i : ℕ) • F.res (interOpens_le_omitIdx U σ i)
          ((cechDiffHom U F p s) (omitIdx σ i))
        = ∑ j : Fin (p+2), ((-1 : ℤ) ^ (i : ℕ) * (-1 : ℤ) ^ (j : ℕ)) •
            F.res (hle i j) (s (omitIdx (omitIdx σ i) j)) := by
    intro i
    change (-1 : ℤ) ^ (i : ℕ) • F.res (interOpens_le_omitIdx U σ i)
        (∑ j : Fin (p+2), (-1 : ℤ) ^ (j : ℕ) •
          F.res (interOpens_le_omitIdx U (omitIdx σ i) j) (s (omitIdx (omitIdx σ i) j)))
      = _
    rw [F.res_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [F.res_zsmul, smul_smul]
    change ((-1 : ℤ) ^ (i : ℕ) * (-1 : ℤ) ^ (j : ℕ)) •
        F.res (interOpens_le_omitIdx U σ i)
          (F.res (interOpens_le_omitIdx U (omitIdx σ i) j) (s (omitIdx (omitIdx σ i) j)))
      = ((-1 : ℤ) ^ (i : ℕ) * (-1 : ℤ) ^ (j : ℕ)) •
        F.res (hle i j) (s (omitIdx (omitIdx σ i) j))
    rw [← F.res_comp]
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  refine abstract_dd_zero p (fun i j => F.res (hle i j) (s (omitIdx (omitIdx σ i) j))) ?_
  intro i j
  exact apply_omitIdx_omitIdx_face U σ (fun τ h => F.res h (s τ)) i j

/-- The cohomologically graded cochain complex with `Č^p(U, F) = ∏_σ F(U_σ)` in degree `p ≥ 0` and
the Čech differential `d`. -/
@[sga "4 V 2.4.3" "special case"]
noncomputable def CechComplex (U : Cover X I) (F : ModPresheaf X) :
    CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of (fun p => AddCommGrpCat.of (CechObj U F p)) (cechDiffMor U F)
    (cechDiff_comp_cechDiff U F)

/-! ## The two functors `F ↦ Hom_{O_X}(K(U)_•, F)` and `F ↦ Č^•(U, F)` -/

/-- The functor `F ↦ Hom_{O_X}(K(U)_•, F)` from `PMod(O_X)` to cochain complexes of abelian groups.
-/
noncomputable def homComplexFunctor (U : Cover X I) :
    ModPresheaf X ⥤ CochainComplex AddCommGrpCat ℕ where
  obj F := HomComplex U F
  map {F G} α :=
    (NatTrans.mapHomologicalComplex (preadditiveYoneda.map α) _).app (KComplex U).op
  map_id F := by
    simp only [preadditiveYoneda.map_id]
    rfl
  map_comp {F G H} α β := by
    simp only [preadditiveYoneda.map_comp]
    rfl

/-- The map on Čech complexes induced by a morphism `α : F ⟶ G`, given degreewise by applying `α`
on sections. -/
noncomputable def cechFunctorMapHom (U : Cover X I) {F G : ModPresheaf X} (α : F ⟶ G) (p : ℕ) :
    CechObj U F p →+ CechObj U G p where
  toFun s := fun σ => α.app (interOpens U σ) (s σ)
  map_zero' := by funext σ; simp
  map_add' s t := by funext σ; simp

/-- `cechFunctorMapHom` commutes with the Čech differential. -/
theorem cechFunctorMap_comm (U : Cover X I) {F G : ModPresheaf X} (α : F ⟶ G) (p : ℕ) :
    cechDiffMor U F p ≫ AddCommGrpCat.ofHom (cechFunctorMapHom U α (p + 1))
      = AddCommGrpCat.ofHom (cechFunctorMapHom U α p) ≫ cechDiffMor U G p := by
  apply AddCommGrpCat.hom_ext
  ext s σ
  change (cechFunctorMapHom U α (p + 1)) (cechDiffHom U F p s) σ
      = (cechDiffHom U G p) (cechFunctorMapHom U α p s) σ
  change α.app (interOpens U σ)
        (∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
          F.res (interOpens_le_omitIdx U σ j) (s (omitIdx σ j)))
      = ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
          G.res (interOpens_le_omitIdx U σ j)
            ((cechFunctorMapHom U α p s) (omitIdx σ j))
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  congr 1
  change α.app (interOpens U σ) (F.res (interOpens_le_omitIdx U σ j) (s (omitIdx σ j)))
      = G.res (interOpens_le_omitIdx U σ j) (α.app (interOpens U (omitIdx σ j)) (s (omitIdx σ j)))
  exact α.naturality (interOpens_le_omitIdx U σ j) (s (omitIdx σ j))

/-- The functor `F ↦ Č^•(U, F)` from `PMod(O_X)` to cochain complexes of abelian groups. -/
@[sga "4 V 2.4.3" "special case"]
noncomputable def cechComplexFunctor (U : Cover X I) :
    ModPresheaf X ⥤ CochainComplex AddCommGrpCat ℕ where
  obj F := CechComplex U F
  map {F G} α :=
    { f := fun p => AddCommGrpCat.ofHom (cechFunctorMapHom U α p)
      comm' := by
        intro p q hpq
        obtain rfl : p + 1 = q := hpq
        change AddCommGrpCat.ofHom (cechFunctorMapHom U α p) ≫ (CechComplex U G).d p (p + 1)
            = (CechComplex U F).d p (p + 1) ≫ AddCommGrpCat.ofHom (cechFunctorMapHom U α (p + 1))
        simp only [CechComplex, CochainComplex.of_d]
        exact (cechFunctorMap_comm U α p).symm }
  map_id F := by
    apply HomologicalComplex.hom_ext
    intro p
    apply AddCommGrpCat.hom_ext
    ext s
    funext σ
    change (cechFunctorMapHom U (𝟙 F) p) s σ = s σ
    change (𝟙 F : F ⟶ F).app (interOpens U σ) (s σ) = s σ
    rw [id_app]; rfl
  map_comp {F G H} α β := by
    apply HomologicalComplex.hom_ext
    intro p
    apply AddCommGrpCat.hom_ext
    ext s
    funext σ
    rfl

end Complex

/-! ## The isomorphism `Hom_{O_X}(K(U)_•, F) ≅ Č^•(U, F)` -/

section MainStatement
variable {I : Type u}

open ModPresheaf

/-! ### Degreewise identification `Hom_{O_X}(K(U)_p, F) ≅ Č^p(U, F)`

The additive isomorphism `degEquiv U F p : (Kterm U p ⟶ F) ≃+ CechObj U F p` is the composite of
the universal property of the direct sum and the adjunction `adjEquiv_exists` on each summand. -/

open Classical in
/-- The inclusion of the `σ`-summand `(j_σ)_{p!} O_{U_σ}` into `K(U)_p`, as a morphism of
presheaves of `O_X`-modules. -/
noncomputable def Kincl (U : Cover X I) (p : ℕ) (σ : Fin (p + 1) → I) :
    extZeroOX X (interOpens U σ) ⟶ Kterm U p where
  app W := DirectSum.lof (sections X W) (Fin (p + 1) → I)
    (fun τ => (extZeroOX X (interOpens U τ)).obj W) σ
  naturality := by
    intro W W' h x
    change DirectSum.lof (sections X W) (Fin (p + 1) → I)
        (fun τ => (extZeroOX X (interOpens U τ)).obj W) σ
        ((extZeroOX X (interOpens U σ)).res h x)
      = (Kterm U p).res h
        (DirectSum.lof (sections X W') (Fin (p + 1) → I)
          (fun τ => (extZeroOX X (interOpens U τ)).obj W') σ x)
    change _ = DirectSum.map (fun τ => (extZeroOX X (interOpens U τ)).resHom h)
        (DirectSum.lof (sections X W') (Fin (p + 1) → I)
          (fun τ => (extZeroOX X (interOpens U τ)).obj W') σ x)
    rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.map_of]
    rfl

/-- The forward degreewise map `(Kterm U p ⟶ F) → CechObj U F p`, given on each summand by
`adjForward` applied to the restriction of `φ` to that summand. -/
noncomputable def degForward (U : Cover X I) (F : ModPresheaf X) (p : ℕ)
    (φ : Kterm U p ⟶ F) : CechObj U F p :=
  fun σ => adjForward (interOpens U σ) F (Kincl U p σ ≫ φ)

open Classical in
/-- The inverse degreewise map `CechObj U F p → (Kterm U p ⟶ F)`. Given a family `s`, the morphism
on sections over `W` is the direct-sum universal map assembled from the per-summand adjoints
`adjInverse (interOpens U σ) F (s σ)`. -/
noncomputable def degInverse (U : Cover X I) (F : ModPresheaf X) (p : ℕ)
    (s : CechObj U F p) : Kterm U p ⟶ F where
  app W := DirectSum.toModule (sections X W) (Fin (p + 1) → I) (F.obj W)
    (fun σ => (adjInverse (interOpens U σ) F (s σ)).app W)
  naturality := by
    intro W W' h x
    refine DirectSum.induction_on x ?_ ?_ ?_
    · rw [(Kterm U p).res_zero, map_zero, map_zero, F.res_zero]
    · intro σ y
      change (DirectSum.toModule (sections X W) (Fin (p + 1) → I) (F.obj W)
            (fun σ => (adjInverse (interOpens U σ) F (s σ)).app W))
          ((Kterm U p).res h (DirectSum.lof (sections X W') (Fin (p + 1) → I)
            (fun τ => (extZeroOX X (interOpens U τ)).obj W') σ y))
        = F.res h ((DirectSum.toModule (sections X W') (Fin (p + 1) → I) (F.obj W')
            (fun σ => (adjInverse (interOpens U σ) F (s σ)).app W'))
          (DirectSum.lof (sections X W') (Fin (p + 1) → I)
            (fun τ => (extZeroOX X (interOpens U τ)).obj W') σ y))
      rw [DirectSum.toModule_lof]
      change (DirectSum.toModule (sections X W) (Fin (p + 1) → I) (F.obj W)
            (fun σ => (adjInverse (interOpens U σ) F (s σ)).app W))
          (DirectSum.map (fun τ => (extZeroOX X (interOpens U τ)).resHom h)
            (DirectSum.lof (sections X W') (Fin (p + 1) → I)
              (fun τ => (extZeroOX X (interOpens U τ)).obj W') σ y))
        = F.res h ((adjInverse (interOpens U σ) F (s σ)).app W' y)
      rw [DirectSum.lof_eq_of, DirectSum.map_of,
        ← DirectSum.lof_eq_of (sections X W) (Fin (p + 1) → I)
          (fun τ => (extZeroOX X (interOpens U τ)).obj W) σ
          ((extZeroOX X (interOpens U σ)).resHom h y),
        DirectSum.toModule_lof]
      change (adjInverse (interOpens U σ) F (s σ)).app W
            ((extZeroOX X (interOpens U σ)).res h y)
        = F.res h ((adjInverse (interOpens U σ) F (s σ)).app W' y)
      exact (adjInverse (interOpens U σ) F (s σ)).naturality h y
    · intro a b ha hb
      rw [(Kterm U p).map_add h a b, LinearMap.map_add, LinearMap.map_add, F.map_add, ha, hb]

open Classical in
/-- The degreewise additive isomorphism `(Kterm U p ⟶ F) ≃+ Č^p(U, F)`, the composite of the
universal property of the direct sum and the adjunction `adjEquiv_exists` on each summand. -/
noncomputable def degEquiv (U : Cover X I) (F : ModPresheaf X) (p : ℕ) :
    (Kterm U p ⟶ F) ≃+ CechObj U F p where
  toFun := degForward U F p
  invFun := degInverse U F p
  left_inv φ := by
    refine hom_ext fun W => ?_
    refine DirectSum.linearMap_ext (sections X W) ?_
    intro σ
    refine LinearMap.ext fun x => ?_
    obtain ⟨e, he, hesymm⟩ := adjEquiv_exists (interOpens U σ) F
    change (degInverse U F p (degForward U F p φ)).app W
        (DirectSum.lof (sections X W) (Fin (p + 1) → I)
          (fun τ => (extZeroOX X (interOpens U τ)).obj W) σ x)
      = φ.app W (DirectSum.lof (sections X W) (Fin (p + 1) → I)
          (fun τ => (extZeroOX X (interOpens U τ)).obj W) σ x)
    change (DirectSum.toModule (sections X W) (Fin (p + 1) → I) (F.obj W)
          (fun σ => (adjInverse (interOpens U σ) F (degForward U F p φ σ)).app W))
        (DirectSum.lof (sections X W) (Fin (p + 1) → I)
          (fun τ => (extZeroOX X (interOpens U τ)).obj W) σ x)
      = φ.app W (DirectSum.lof (sections X W) (Fin (p + 1) → I)
          (fun τ => (extZeroOX X (interOpens U τ)).obj W) σ x)
    rw [DirectSum.toModule_lof]
    have hadj : adjInverse (interOpens U σ) F (degForward U F p φ σ) = Kincl U p σ ≫ φ := by
      change adjInverse (interOpens U σ) F (adjForward (interOpens U σ) F (Kincl U p σ ≫ φ))
        = Kincl U p σ ≫ φ
      rw [← he, ← hesymm]
      exact e.symm_apply_apply (Kincl U p σ ≫ φ)
    rw [hadj]
    rfl
  right_inv s := by
    funext σ
    obtain ⟨e, he, hesymm⟩ := adjEquiv_exists (interOpens U σ) F
    change adjForward (interOpens U σ) F (Kincl U p σ ≫ degInverse U F p s) = s σ
    have hval : Kincl U p σ ≫ degInverse U F p s = adjInverse (interOpens U σ) F (s σ) := by
      refine hom_ext fun W => ?_
      refine LinearMap.ext fun x => ?_
      change (degInverse U F p s).app W
          (DirectSum.lof (sections X W) (Fin (p + 1) → I)
            (fun τ => (extZeroOX X (interOpens U τ)).obj W) σ x)
        = (adjInverse (interOpens U σ) F (s σ)).app W x
      change (DirectSum.toModule (sections X W) (Fin (p + 1) → I) (F.obj W)
            (fun σ => (adjInverse (interOpens U σ) F (s σ)).app W))
          (DirectSum.lof (sections X W) (Fin (p + 1) → I)
            (fun τ => (extZeroOX X (interOpens U τ)).obj W) σ x)
        = (adjInverse (interOpens U σ) F (s σ)).app W x
      rw [DirectSum.toModule_lof]
    rw [hval, ← hesymm, ← he]
    exact e.apply_symm_apply (s σ)
  map_add' φ ψ := by
    funext σ
    change adjForward (interOpens U σ) F (Kincl U p σ ≫ (φ + ψ))
      = adjForward (interOpens U σ) F (Kincl U p σ ≫ φ)
        + adjForward (interOpens U σ) F (Kincl U p σ ≫ ψ)
    change (Kincl U p σ ≫ (φ + ψ)).app (interOpens U σ) (extZeroOne (interOpens U σ))
      = (Kincl U p σ ≫ φ).app (interOpens U σ) (extZeroOne (interOpens U σ))
        + (Kincl U p σ ≫ ψ).app (interOpens U σ) (extZeroOne (interOpens U σ))
    simp only [comp_app]
    rfl

/-- Restricting `1` along `interOpens U σ ≤ interOpens U (omitIdx σ j)` inside
`extZeroOX (interOpens U (omitIdx σ j))` equals the canonical-map image of `1`. -/
theorem extZeroOne_res_eq_canonical (U : Cover X I) {p : ℕ} (σ : Fin (p + 2) → I)
    (j : Fin (p + 2)) :
    (extZeroOX X (interOpens U (omitIdx σ j))).res (interOpens_le_omitIdx U σ j)
        (extZeroOne (interOpens U (omitIdx σ j)))
      = extZeroCanonicalApp (interOpens_le_omitIdx U σ j) (interOpens U σ)
        (extZeroOne (interOpens U σ)) := by
  apply Subtype.ext
  change (X.presheaf.map (homOfLE (interOpens_le_omitIdx U σ j)).op) (1 : sections X _)
      = (1 : sections X (interOpens U σ))
  rw [map_one]

/-- The degreewise forward map `degForward` intertwines precomposition with `Kdiff` (the
`HomComplex` codifferential) and the Čech differential `cechDiffHom`. -/
theorem degForward_diff (U : Cover X I) (F : ModPresheaf X) (p : ℕ) (φ : Kterm U p ⟶ F) :
    cechDiffHom U F p (degForward U F p φ)
      = degForward U F (p + 1) (Kdiff U p ≫ φ) := by
  classical
  funext σ
  change (∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        F.res (interOpens_le_omitIdx U σ j) (degForward U F p φ (omitIdx σ j)))
    = adjForward (interOpens U σ) F (Kincl U (p + 1) σ ≫ (Kdiff U p ≫ φ))
  have hRHS : adjForward (interOpens U σ) F (Kincl U (p + 1) σ ≫ (Kdiff U p ≫ φ))
      = ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
          φ.app (interOpens U σ)
            (DirectSum.lof (sections X (interOpens U σ)) (Fin (p + 1) → I)
              (fun τ => (extZeroOX X (interOpens U τ)).obj (interOpens U σ)) (omitIdx σ j)
              (extZeroCanonicalApp (interOpens_le_omitIdx U σ j) (interOpens U σ)
                (extZeroOne (interOpens U σ)))) := by
    change φ.app (interOpens U σ)
        ((Kdiff U p).app (interOpens U σ)
          (DirectSum.lof (sections X (interOpens U σ)) (Fin (p + 1 + 1) → I)
            (fun τ => (extZeroOX X (interOpens U τ)).obj (interOpens U σ)) σ
            (extZeroOne (interOpens U σ))))
      = _
    change φ.app (interOpens U σ)
        ((KdiffApp U p (interOpens U σ))
          (DirectSum.lof (sections X (interOpens U σ)) (Fin (p + 1 + 1) → I)
            (fun τ => (extZeroOX X (interOpens U τ)).obj (interOpens U σ)) σ
            (extZeroOne (interOpens U σ))))
      = _
    rw [KdiffApp, DirectSum.toModule_lof]
    change φ.app (interOpens U σ)
        ((∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
            (DirectSum.lof (sections X (interOpens U σ)) (Fin (p + 1) → I)
                (fun τ => (extZeroOX X (interOpens U τ)).obj (interOpens U σ)) (omitIdx σ j)).comp
              (extZeroCanonicalApp (interOpens_le_omitIdx U σ j) (interOpens U σ)))
          (extZeroOne (interOpens U σ)))
      = _
    rw [LinearMap.coe_sum, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_apply, map_zsmul]
    rfl
  rw [hRHS]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  show F.res (interOpens_le_omitIdx U σ j) (degForward U F p φ (omitIdx σ j))
    = φ.app (interOpens U σ)
        (DirectSum.lof (sections X (interOpens U σ)) (Fin (p + 1) → I)
          (fun τ => (extZeroOX X (interOpens U τ)).obj (interOpens U σ)) (omitIdx σ j)
          (extZeroCanonicalApp (interOpens_le_omitIdx U σ j) (interOpens U σ)
            (extZeroOne (interOpens U σ))))
  change F.res (interOpens_le_omitIdx U σ j)
      (φ.app (interOpens U (omitIdx σ j))
        (DirectSum.lof (sections X (interOpens U (omitIdx σ j))) (Fin (p + 1) → I)
          (fun τ => (extZeroOX X (interOpens U τ)).obj (interOpens U (omitIdx σ j))) (omitIdx σ j)
          (extZeroOne (interOpens U (omitIdx σ j)))))
    = _
  rw [← φ.naturality (interOpens_le_omitIdx U σ j)]
  congr 1
  show (Kterm U p).res (interOpens_le_omitIdx U σ j)
      (DirectSum.lof (sections X (interOpens U (omitIdx σ j))) (Fin (p + 1) → I)
        (fun τ => (extZeroOX X (interOpens U τ)).obj (interOpens U (omitIdx σ j))) (omitIdx σ j)
        (extZeroOne (interOpens U (omitIdx σ j))))
    = _
  change DirectSum.map (fun τ => (extZeroOX X (interOpens U τ)).resHom (interOpens_le_omitIdx U σ
      j))
      (DirectSum.lof (sections X (interOpens U (omitIdx σ j))) (Fin (p + 1) → I)
        (fun τ => (extZeroOX X (interOpens U τ)).obj (interOpens U (omitIdx σ j))) (omitIdx σ j)
        (extZeroOne (interOpens U (omitIdx σ j))))
    = _
  rw [DirectSum.lof_eq_of, DirectSum.map_of,
    ← DirectSum.lof_eq_of (sections X (interOpens U σ)) (Fin (p + 1) → I)
      (fun τ => (extZeroOX X (interOpens U τ)).obj (interOpens U σ)) (omitIdx σ j)
      ((extZeroOX X (interOpens U (omitIdx σ j))).resHom (interOpens_le_omitIdx U σ j)
        (extZeroOne (interOpens U (omitIdx σ j))))]
  congr 1
  exact extZeroOne_res_eq_canonical U σ j

/-- The degreewise isomorphisms `degEquiv` commute with the differentials. -/
private theorem degEquiv_comm (U : Cover X I) (F : ModPresheaf X) (i : ℕ) :
    (AddEquiv.toAddCommGrpIso (degEquiv U F i)).hom ≫ (CechComplex U F).d i (i + 1)
      = (HomComplex U F).d i (i + 1) ≫ (AddEquiv.toAddCommGrpIso (degEquiv U F (i + 1))).hom := by
  apply AddCommGrpCat.hom_ext
  ext φ
  rw [show (CechComplex U F).d i (i + 1) = cechDiffMor U F i from by
        simp only [CechComplex, CochainComplex.of_d]]
  rw [show (HomComplex U F).d i (i + 1)
        = (preadditiveYoneda.obj F).map ((Kdiff U i).op) from by
      simp only [HomComplex, Functor.mapHomologicalComplex_obj_d, HomologicalComplex.op_d,
        show (KComplex U).d (i + 1) i = Kdiff U i from by simp only [KComplex, ChainComplex.of_d]]]
  change cechDiffHom U F i (degForward U F i φ) = degForward U F (i + 1) (Kdiff U i ≫ φ)
  exact degForward_diff U F i φ

/-- For a ringed space `X` and an open covering `U : U.carrierOpen = ⋃_i U.obj i`, the two functors
`F ↦ Hom_{O_X}(K(U)_•, F)` (`homComplexFunctor`) and `F ↦ Č^•(U, F)` (`cechComplexFunctor`) from
`PMod(O_X)` to cochain complexes of abelian groups are naturally isomorphic. The degreewise
isomorphism comes from the universal property of the direct sum (`Hom(⨁, F) = ∏ Hom(·, F)`)
together with the adjunction `Hom_{O_X}(j_{p!} O_V, F) ≅ F(V)`. This is [Stacks, Tag 01EL] (Lemma
20.10.3). -/
theorem main_theorem_exists (U : Cover X I) :
    Nonempty (homComplexFunctor U ≅ cechComplexFunctor U) := by
  refine ⟨NatIso.ofComponents
    (fun F => HomologicalComplex.Hom.isoOfComponents
      (fun p => AddEquiv.toAddCommGrpIso (degEquiv U F p))
      (by
        intro i j (hij : i + 1 = j)
        subst hij
        exact degEquiv_comm U F i))
    ?_⟩
  intro F G α
  apply HomologicalComplex.hom_ext
  intro p
  apply AddCommGrpCat.hom_ext
  ext φ
  funext σ
  change degForward U G p (φ ≫ α) σ = α.app (interOpens U σ) (degForward U F p φ σ)
  change adjForward (interOpens U σ) G (Kincl U p σ ≫ (φ ≫ α))
      = α.app (interOpens U σ) (adjForward (interOpens U σ) F (Kincl U p σ ≫ φ))
  rw [← Category.assoc, adjForward_naturality (interOpens U σ) α (Kincl U p σ ≫ φ)]

/-- **Stacks 20.10.3, tag 01EL.** The natural isomorphism of functors
`Hom_{O_X}(K(U)_•, -) ≅ Č^•(U, -)` itself (the data, not merely its existence), exhibiting the
isomorphism `Hom_{O_X}(K(U)_•, F) ≅ Č^•(U, F)` as natural in `F`. -/
@[stacks 01EL]
noncomputable def main_iso (U : Cover X I) :
    homComplexFunctor U ≅ cechComplexFunctor U :=
  (main_theorem_exists U).some

/-- For every presheaf `F` of `O_X`-modules there is an isomorphism of cochain complexes (of
abelian groups) `Hom_{O_X}(K(U)_•, F) ≅ Č^•(U, F)`. -/
theorem main_theorem_iso_exists (U : Cover X I) (F : ModPresheaf X) :
    Nonempty (HomComplex U F ≅ CechComplex U F) := by
  refine ⟨HomologicalComplex.Hom.isoOfComponents
    (fun p => AddEquiv.toAddCommGrpIso (degEquiv U F p)) ?_⟩
  intro i j (hij : i + 1 = j)
  subst hij
  exact degEquiv_comm U F i

/-- The isomorphism of cochain complexes (of abelian groups) `Hom_{O_X}(K(U)_•, F) ≅ Č^•(U, F)`
itself, for every presheaf `F` of `O_X`-modules. -/
noncomputable def main_theorem_iso (U : Cover X I) (F : ModPresheaf X) :
    HomComplex U F ≅ CechComplex U F :=
  (main_theorem_iso_exists U F).some

end MainStatement

end ModPresheaf

end StacksCechPresheaf
