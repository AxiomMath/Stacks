module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Tactic.Module
public import StacksFrontier.Algebra.Module.Adequate.Tangent

/-!
# The dual-number pair of a pair `(C, V)`

For a pair `(C, V)` of an `A`-algebra and a module over it, the dual-number pair is
`(C[ε], V ⊕ V)`, where `C[ε] = C ⊕ Cε` acts on `V ⊕ V = V ⊕ εV` by
`(a + bε)(v₀, v₁) = (a v₀, a v₁ + b v₀)`; it is `(C[ε], C[ε] ⊗_C V)` in coordinates.
The construction is functorial in the pair, and the two maps `v ↦ (v, 0)` and `v ↦ (0, v)`,
both lying over `C → C[ε]`, are natural transformations from the identity; the second is the
first followed by multiplication by `ε`. This is the scaling `v ↦ ε v` on which the weight
argument for the higher `Ext` groups of Tag 06ZG runs.

## Main definitions

* `AdequateFunctor.DualPairModule`: `V ⊕ V` with its `C[ε]`-module structure.
* `AdequateFunctor.dualNumberPair`: the pair `(C[ε], V ⊕ V)`.
* `AdequateFunctor.dualNumberPairFunctor`: its functoriality in the pair.
* `AdequateFunctor.dualNumberPairInl`, `AdequateFunctor.dualNumberPairInr`: the natural maps
  `(C, V) → (C[ε], V ⊕ V)` given by `v ↦ (v, 0)` and `v ↦ (0, v)`.
-/

@[expose] public section

namespace AdequateFunctor

open CategoryTheory TrivSqZeroExt

universe u w

section DualModule

variable (C : Type*) [CommRing C] (V : Type*) [AddCommGroup V] [Module C V]

/-- The module `V ⊕ V = V ⊕ εV` over the dual numbers `C[ε]`. -/
def DualPairModule (_C : Type*) (V : Type*) : Type _ := V × V

/-- The additive group structure of `V ⊕ εV`, that of `V × V`. -/
instance : AddCommGroup (DualPairModule C V) := inferInstanceAs (AddCommGroup (V × V))

variable {C V}

variable (C) in
/-- The point `(v₀, v₁)` of `V ⊕ εV`. -/
def DualPairModule.mk (v₀ v₁ : V) : DualPairModule C V := (v₀, v₁)

variable (C) in
/-- The `V`-component. -/
def DualPairModule.fst (x : DualPairModule C V) : V := Prod.fst (α := V) (β := V) x

variable (C) in
/-- The `εV`-component. -/
def DualPairModule.snd (x : DualPairModule C V) : V := Prod.snd (α := V) (β := V) x

omit [CommRing C] [AddCommGroup V] [Module C V] in
/-- Two points of `V ⊕ εV` are equal when both components are. -/
@[ext] lemma DualPairModule.ext {x y : DualPairModule C V}
    (h₀ : DualPairModule.fst C x = DualPairModule.fst C y)
    (h₁ : DualPairModule.snd C x = DualPairModule.snd C y) : x = y := Prod.ext h₀ h₁

omit [CommRing C] [AddCommGroup V] [Module C V] in
/-- The `V`-component of `(v₀, v₁)` is `v₀`. -/
@[simp] lemma DualPairModule.fst_mk (v₀ v₁ : V) :
    DualPairModule.fst C (DualPairModule.mk C v₀ v₁) = v₀ :=
  rfl

omit [CommRing C] [AddCommGroup V] [Module C V] in
/-- The `εV`-component of `(v₀, v₁)` is `v₁`. -/
@[simp] lemma DualPairModule.snd_mk (v₀ v₁ : V) :
    DualPairModule.snd C (DualPairModule.mk C v₀ v₁) = v₁ :=
  rfl

omit [CommRing C] [Module C V] in
/-- The `V`-component is additive. -/
@[simp] lemma DualPairModule.fst_add (x y : DualPairModule C V) :
    DualPairModule.fst C (x + y) = DualPairModule.fst C x + DualPairModule.fst C y :=
  rfl

omit [CommRing C] [Module C V] in
/-- The `εV`-component is additive. -/
@[simp] lemma DualPairModule.snd_add (x y : DualPairModule C V) :
    DualPairModule.snd C (x + y) = DualPairModule.snd C x + DualPairModule.snd C y :=
  rfl

omit [CommRing C] [Module C V] in
/-- The `V`-component of `0` is `0`. -/
@[simp] lemma DualPairModule.fst_zero : DualPairModule.fst C (0 : DualPairModule C V) = 0 := rfl

omit [CommRing C] [Module C V] in
/-- The `εV`-component of `0` is `0`. -/
@[simp] lemma DualPairModule.snd_zero : DualPairModule.snd C (0 : DualPairModule C V) = 0 := rfl

/-- The action `(a + bε)(v₀, v₁) = (a v₀, a v₁ + b v₀)` of `C[ε]` on `V ⊕ εV`. -/
instance : SMul (TrivSqZeroExt C C) (DualPairModule C V) where
  smul q x := DualPairModule.mk C (q.fst • DualPairModule.fst C x)
    (q.fst • DualPairModule.snd C x + q.snd • DualPairModule.fst C x)

/-- The `V`-component of `(a + bε) x` is `a` times that of `x`. -/
@[simp] lemma DualPairModule.fst_smul (q : TrivSqZeroExt C C) (x : DualPairModule C V) :
    DualPairModule.fst C (q • x) = q.fst • DualPairModule.fst C x := rfl

/-- The `εV`-component of `(a + bε)(v₀, v₁)` is `a v₁ + b v₀`. -/
@[simp] lemma DualPairModule.snd_smul (q : TrivSqZeroExt C C) (x : DualPairModule C V) :
    DualPairModule.snd C (q • x) =
      q.fst • DualPairModule.snd C x + q.snd • DualPairModule.fst C x := rfl

/-- `V ⊕ εV` is a module over the dual numbers `C[ε]`. -/
instance : Module (TrivSqZeroExt C C) (DualPairModule C V) where
  one_smul x := DualPairModule.ext (by simp) (by simp)
  mul_smul q q' x := DualPairModule.ext (by simp [mul_smul]) (by
    simp only [DualPairModule.snd_smul, DualPairModule.fst_smul, TrivSqZeroExt.fst_mul,
      TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    module)
  smul_zero q := DualPairModule.ext (by simp) (by simp)
  smul_add q x y := DualPairModule.ext (by simp) (by simp [smul_add]; abel)
  add_smul q q' x := DualPairModule.ext (by simp [add_smul]) (by simp [add_smul]; abel)
  zero_smul x := DualPairModule.ext (by simp) (by simp)

end DualModule

section Pair

variable {A : Type u} [CommRing A]

/-- **The dual-number pair** `(C[ε], V ⊕ εV)` of a pair `(C, V)`. -/
def dualNumberPair (X : AlgebraModulePair.{w} A) : AlgebraModulePair.{w} A :=
  { algebra := TrivSqZeroExt X.algebra X.algebra
    module := DualPairModule X.algebra X.module }

/-- The element `ε` of `C[ε]`, as a scalar of the dual-number pair. -/
def dualEps (X : AlgebraModulePair.{w} A) : (dualNumberPair X).algebra :=
  (inr 1 : TrivSqZeroExt X.algebra X.algebra)

/-- The dual numbers of an algebra map. -/
def dualNumberAlgHom {C D : Type*} [CommRing C] [CommRing D] [Algebra A C] [Algebra A D]
    (f : C →ₐ[A] D) : TrivSqZeroExt C C →ₐ[A] TrivSqZeroExt D D where
  toFun x := ⟨f x.fst, f x.snd⟩
  map_zero' := TrivSqZeroExt.ext (map_zero f) (map_zero f)
  map_one' := TrivSqZeroExt.ext (map_one f) (map_zero f)
  map_add' x y := TrivSqZeroExt.ext (map_add f x.fst y.fst) (map_add f x.snd y.snd)
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · exact map_mul f x.fst y.fst
    · change f (x.fst • y.snd + MulOpposite.op y.fst • x.snd) =
        f x.fst • f y.snd + MulOpposite.op (f y.fst) • f x.snd
      simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, map_add,
        map_mul]
  commutes' a := TrivSqZeroExt.ext (f.commutes a) (map_zero f)

/-- `dualNumberAlgHom f` applies `f` to the scalar part. -/
@[simp] lemma dualNumberAlgHom_fst {C D : Type*} [CommRing C] [CommRing D] [Algebra A C]
    [Algebra A D] (f : C →ₐ[A] D) (x : TrivSqZeroExt C C) :
    (dualNumberAlgHom f x).fst = f x.fst := rfl

/-- `dualNumberAlgHom f` applies `f` to the `ε`-part. -/
@[simp] lemma dualNumberAlgHom_snd {C D : Type*} [CommRing C] [CommRing D] [Algebra A C]
    [Algebra A D] (f : C →ₐ[A] D) (x : TrivSqZeroExt C C) :
    (dualNumberAlgHom f x).snd = f x.snd := rfl

/-- The dual-number pair of a morphism of pairs. -/
def dualNumberPairMap {X Y : AlgebraModulePair.{w} A} (g : X ⟶ Y) :
    dualNumberPair X ⟶ dualNumberPair Y where
  base := dualNumberAlgHom g.base
  linear :=
    { toFun := fun x => DualPairModule.mk Y.algebra (g.linear (DualPairModule.fst X.algebra x))
        (g.linear (DualPairModule.snd X.algebra x))
      map_add' := fun x y => DualPairModule.ext (map_add _ _ _) (map_add _ _ _)
      map_smul' := fun q x => DualPairModule.ext (by
          change g.linear (_ • _) = _
          rw [g.linear.map_smulₛₗ]
          rfl)
        (by
          change g.linear (_ + _) = _
          rw [map_add, g.linear.map_smulₛₗ, g.linear.map_smulₛₗ]
          rfl) }

/-- **The dual-number pair as a functor** on pairs. -/
def dualNumberPairFunctor : AlgebraModulePair.{w} A ⥤ AlgebraModulePair.{w} A where
  obj := dualNumberPair
  map := dualNumberPairMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The map `(C, V) → (C[ε], V ⊕ εV)`, `v ↦ (v, 0)`, over `C → C[ε]`. -/
def dualNumberPairInl (X : AlgebraModulePair.{w} A) : X ⟶ dualNumberPair X where
  base := inlAlgHom A X.algebra X.algebra
  linear :=
    { toFun := fun v => DualPairModule.mk X.algebra v 0
      map_add' := fun v w => DualPairModule.ext rfl (by
        change (0 : X.module) = 0 + 0
        simp)
      map_smul' := fun c v => DualPairModule.ext rfl (by
        change (0 : X.module) = c • (0 : X.module) + (0 : X.algebra) • v
        simp) }

/-- The map `(C, V) → (C[ε], V ⊕ εV)`, `v ↦ (0, v) = ε v`, over `C → C[ε]`. -/
def dualNumberPairInr (X : AlgebraModulePair.{w} A) : X ⟶ dualNumberPair X where
  base := inlAlgHom A X.algebra X.algebra
  linear :=
    { toFun := fun v => DualPairModule.mk X.algebra 0 v
      map_add' := fun v w => DualPairModule.ext (by
        change (0 : X.module) = 0 + 0
        simp) rfl
      map_smul' := fun c v => DualPairModule.ext (by
        change (0 : X.module) = c • (0 : X.module)
        simp) (by
        change c • v = c • v + (0 : X.algebra) • (0 : X.module)
        simp) }

/-- `dualNumberPairInl` sends `v` to `(v, 0)`. -/
@[simp] lemma dualNumberPairInl_linear (X : AlgebraModulePair.{w} A) (v : X.module) :
    (dualNumberPairInl X).linear v = DualPairModule.mk X.algebra v 0 := rfl

/-- `dualNumberPairInr` sends `v` to `(0, v)`. -/
@[simp] lemma dualNumberPairInr_linear (X : AlgebraModulePair.{w} A) (v : X.module) :
    (dualNumberPairInr X).linear v = DualPairModule.mk X.algebra 0 v := rfl

/-- `v ↦ (v, 0)` is natural in the pair. -/
lemma dualNumberPairInl_naturality {X Y : AlgebraModulePair.{w} A} (g : X ⟶ Y) :
    g ≫ dualNumberPairInl Y = dualNumberPairInl X ≫ dualNumberPairMap g :=
  AlgebraModulePair.Hom.ext _ _
    (AlgHom.ext fun _ => TrivSqZeroExt.ext rfl (map_zero g.base).symm)
    (fun _ => DualPairModule.ext (C := Y.algebra) rfl (map_zero g.linear).symm)

/-- `v ↦ (0, v)` is natural in the pair. -/
lemma dualNumberPairInr_naturality {X Y : AlgebraModulePair.{w} A} (g : X ⟶ Y) :
    g ≫ dualNumberPairInr Y = dualNumberPairInr X ≫ dualNumberPairMap g :=
  AlgebraModulePair.Hom.ext _ _
    (AlgHom.ext fun _ => TrivSqZeroExt.ext rfl (map_zero g.base).symm)
    (fun _ => DualPairModule.ext (C := Y.algebra) (map_zero g.linear).symm rfl)

/-- `(0, v)` is `ε` times `(v, 0)`. -/
lemma dualNumberPairInr_eq_eps_smul (X : AlgebraModulePair.{w} A) (v : X.module) :
    (dualNumberPairInr X).linear v =
      dualEps X • (dualNumberPairInl X).linear v :=
  DualPairModule.ext (C := X.algebra)
    (by
      show (0 : X.module) = (inr 1 : TrivSqZeroExt X.algebra X.algebra).fst • v
      simp)
    (by
      show v = (inr 1 : TrivSqZeroExt X.algebra X.algebra).fst • (0 : X.module) +
        (inr 1 : TrivSqZeroExt X.algebra X.algebra).snd • v
      simp)

end Pair

section Coordinates

variable {A : Type u} [CommRing A] (X : AlgebraModulePair.{w} A)

/-! Coordinates on the dual-number pair. `AdequateFunctor.dualNumberPair` is a definition, so that
its structures are always its fields as a pair; these maps and lemmas give access to it as
`(C[ε], V ⊕ εV)`. -/

/-- The scalar part `a` of `a + bε ∈ C[ε]`. -/
def dualAlgFst : (dualNumberPair X).algebra →ₐ[A] X.algebra :=
  TrivSqZeroExt.fstHom A X.algebra X.algebra

/-- The `ε`-part `b` of `a + bε ∈ C[ε]`. -/
def dualAlgSnd : (dualNumberPair X).algebra →+ X.algebra :=
  (TrivSqZeroExt.sndHom X.algebra X.algebra).toAddMonoidHom

/-- The `V`-coordinate of `V ⊕ εV`. -/
def dualCoordFst : (dualNumberPair X).module →+ X.module where
  toFun x := DualPairModule.fst X.algebra x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The `εV`-coordinate of `V ⊕ εV`. -/
def dualCoordSnd : (dualNumberPair X).module →+ X.module where
  toFun x := DualPairModule.snd X.algebra x
  map_zero' := rfl
  map_add' _ _ := rfl

variable {X}

/-- Two dual numbers are equal when their scalar and `ε`-parts are. -/
lemma dualAlg_ext {q q' : (dualNumberPair X).algebra} (h₁ : dualAlgFst X q = dualAlgFst X q')
    (h₂ : dualAlgSnd X q = dualAlgSnd X q') : q = q' :=
  TrivSqZeroExt.ext h₁ h₂

/-- Two points of `V ⊕ εV` are equal when both coordinates are. -/
lemma dualCoord_ext {x y : (dualNumberPair X).module} (h₁ : dualCoordFst X x = dualCoordFst X y)
    (h₂ : dualCoordSnd X x = dualCoordSnd X y) : x = y :=
  DualPairModule.ext (C := X.algebra) h₁ h₂

/-- The `ε`-part of a product: `(a + bε)(a' + b'ε)` has `ε`-part `a b' + b a'`. -/
@[simp] lemma dualAlgSnd_mul (q q' : (dualNumberPair X).algebra) :
    dualAlgSnd X (q * q') =
      dualAlgFst X q * dualAlgSnd X q' + dualAlgSnd X q * dualAlgFst X q' := by
  have h := TrivSqZeroExt.snd_mul (R := X.algebra) (M := X.algebra)
    (q : TrivSqZeroExt X.algebra X.algebra) q'
  rw [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op] at h
  exact h

/-- The `V`-coordinate of `q • x` is the scalar part of `q` times that of `x`. -/
@[simp] lemma dualCoordFst_smul (q : (dualNumberPair X).algebra) (x : (dualNumberPair X).module) :
    dualCoordFst X (q • x) = dualAlgFst X q • dualCoordFst X x := rfl

/-- The `εV`-coordinate of `(a + bε)(v₀, v₁)` is `a v₁ + b v₀`. -/
@[simp] lemma dualCoordSnd_smul (q : (dualNumberPair X).algebra) (x : (dualNumberPair X).module) :
    dualCoordSnd X (q • x) =
      dualAlgFst X q • dualCoordSnd X x + dualAlgSnd X q • dualCoordFst X x := rfl

/-- The `V`-coordinate is `A`-linear. -/
@[simp] lemma dualCoordFst_smul_base (a : A) (x : (dualNumberPair X).module) :
    dualCoordFst X (a • x) = a • dualCoordFst X x := by
  show (algebraMap A X.algebra a) • DualPairModule.fst X.algebra x = _
  exact algebraMap_smul X.algebra a _

/-- The `εV`-coordinate is `A`-linear. -/
@[simp] lemma dualCoordSnd_smul_base (a : A) (x : (dualNumberPair X).module) :
    dualCoordSnd X (a • x) = a • dualCoordSnd X x := by
  show (algebraMap A X.algebra a) • DualPairModule.snd X.algebra x +
    (0 : X.algebra) • DualPairModule.fst X.algebra x = _
  rw [zero_smul, add_zero]
  exact algebraMap_smul X.algebra a _

/-- The scalar part of `ε` is `0`. -/
@[simp] lemma dualAlgFst_eps : dualAlgFst X (dualEps X) = 0 := rfl

/-- The `ε`-part of `ε` is `1`. -/
@[simp] lemma dualAlgSnd_eps : dualAlgSnd X (dualEps X) = 1 := rfl

/-- The scalar part of `c ∈ C ⊆ C[ε]`, along `dualNumberPairInl`, is `c`. -/
@[simp] lemma dualAlgFst_inl (c : X.algebra) :
    dualAlgFst X ((dualNumberPairInl X).base c) = c := rfl

/-- The `ε`-part of `c ∈ C ⊆ C[ε]`, along `dualNumberPairInl`, is `0`. -/
@[simp] lemma dualAlgSnd_inl (c : X.algebra) :
    dualAlgSnd X ((dualNumberPairInl X).base c) = 0 := rfl

/-- The scalar part of `c ∈ C ⊆ C[ε]`, along `dualNumberPairInr`, is `c`. -/
@[simp] lemma dualAlgFst_inr_base (c : X.algebra) :
    dualAlgFst X ((dualNumberPairInr X).base c) = c := rfl

/-- The `ε`-part of `c ∈ C ⊆ C[ε]`, along `dualNumberPairInr`, is `0`. -/
@[simp] lemma dualAlgSnd_inr_base (c : X.algebra) :
    dualAlgSnd X ((dualNumberPairInr X).base c) = 0 := rfl

/-- The `V`-coordinate of `(v, 0)` is `v`. -/
@[simp] lemma dualCoordFst_inl (v : X.module) :
    dualCoordFst X ((dualNumberPairInl X).linear v) = v := rfl

/-- The `εV`-coordinate of `(v, 0)` is `0`. -/
@[simp] lemma dualCoordSnd_inl (v : X.module) :
    dualCoordSnd X ((dualNumberPairInl X).linear v) = 0 := rfl

/-- The `V`-coordinate of `(0, v)` is `0`. -/
@[simp] lemma dualCoordFst_inr (v : X.module) :
    dualCoordFst X ((dualNumberPairInr X).linear v) = 0 := rfl

/-- The `εV`-coordinate of `(0, v)` is `v`. -/
@[simp] lemma dualCoordSnd_inr (v : X.module) :
    dualCoordSnd X ((dualNumberPairInr X).linear v) = v := rfl

/-- The dual numbers of a morphism act on scalar parts by its algebra map. -/
@[simp] lemma dualAlgFst_map {Y : AlgebraModulePair.{w} A} (g : X ⟶ Y)
    (q : (dualNumberPair X).algebra) :
    dualAlgFst Y ((dualNumberPairMap g).base q) = g.base (dualAlgFst X q) := rfl

/-- The dual numbers of a morphism act on `ε`-parts by its algebra map. -/
@[simp] lemma dualAlgSnd_map {Y : AlgebraModulePair.{w} A} (g : X ⟶ Y)
    (q : (dualNumberPair X).algebra) :
    dualAlgSnd Y ((dualNumberPairMap g).base q) = g.base (dualAlgSnd X q) := rfl

/-- The dual-number pair of a morphism acts on `V`-coordinates by its linear map. -/
@[simp] lemma dualCoordFst_map {Y : AlgebraModulePair.{w} A} (g : X ⟶ Y)
    (x : (dualNumberPair X).module) :
    dualCoordFst Y ((dualNumberPairMap g).linear x) = g.linear (dualCoordFst X x) := rfl

/-- The dual-number pair of a morphism acts on `εV`-coordinates by its linear map. -/
@[simp] lemma dualCoordSnd_map {Y : AlgebraModulePair.{w} A} (g : X ⟶ Y)
    (x : (dualNumberPair X).module) :
    dualCoordSnd Y ((dualNumberPairMap g).linear x) = g.linear (dualCoordSnd X x) := rfl

/-- The dual numbers of a morphism send `ε` to `ε`. -/
lemma dualEps_map {Y : AlgebraModulePair.{w} A} (g : X ⟶ Y) :
    (dualNumberPairMap g).base (dualEps X) = dualEps Y :=
  dualAlg_ext (map_zero g.base) (map_one g.base)

end Coordinates

end AdequateFunctor

end
