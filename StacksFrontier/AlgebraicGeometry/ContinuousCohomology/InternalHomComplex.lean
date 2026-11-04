module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.DiscreteInternalHom
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import StacksFrontier.Homology.HomComplex.OpModule

/-!
# The internal Hom complex of complexes of discrete modules

Let `R` be a finite ring and `Q` a compact topological group. For a cochain complex `V` of
discrete `R`-`Q`-modules and a cochain complex `W` of discrete `ℤ`-`Q`-modules, the internal Hom
`Hom_ℤ(V^p, W^q)` of `Stacks.ContinuousCohomology.internalHom` is a module over the completed
group algebra `Rᵐᵒᵖ[[Q]]`, and these assemble into the **internal Hom complex**
`Hom^•_ℤ(V, W)`: its degree-`n` term is `∏_p Hom_ℤ(V^p, W^{p+n})`, with the Hom-complex
differential. It is Mathlib's Hom complex `CochainComplex.HomComplex` of the underlying complexes
of abelian groups, the action of `x ∈ Rᵐᵒᵖ[[Q]]` being the action on each component; the
differential is `Rᵐᵒᵖ[[Q]]`-linear because pre- and postcomposition with morphisms of discrete
modules commute with the action (`Stacks.ContinuousCohomology.internalHom_precomp_smul`,
`Stacks.ContinuousCohomology.internalHom_postcomp_smul`).

For `W = ℚ/ℤ` in degree `0` this is the contragredient complex, and it is the target of the
Galois-equivariant Poincaré pairing of Tag 03VM.

## Main definitions

* `Stacks.ContinuousCohomology.forgetAb`: the underlying abelian group of a discrete module.
* `Stacks.ContinuousCohomology.InternalHomCochain`: the cochains `Cochain V W n` of the underlying
  complexes of abelian groups, with their `Rᵐᵒᵖ[[Q]]`-module structure.
* `Stacks.ContinuousCohomology.internalHomComplex`: the internal Hom complex, a cochain complex of
  `Rᵐᵒᵖ[[Q]]`-modules.
* `Stacks.ContinuousCohomology.internalHomComplexPostcomp`: postcomposition with a morphism of
  complexes of discrete `ℤ`-`Q`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.HomComplex Stacks.GroupHomology

universe u v w

namespace Stacks.ContinuousCohomology

/-- The underlying abelian group of a discrete `R`-`Q`-module. -/
abbrev forgetAb (R : Type u) [Ring R] (Q : Type v) [Group Q] [TopologicalSpace Q] :
    Stacks.Injectives.ContinuousModule.{u, v, w} R Q ⥤ AddCommGrpCat.{w} :=
  Stacks.Injectives.continuousModuleUnderlying.{u, v, w} R Q ⋙
    forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}

/-- Taking the underlying abelian group of a discrete `R`-`Q`-module is additive. -/
instance (R : Type u) [Ring R] (Q : Type v) [Group Q] [TopologicalSpace Q] :
    (forgetAb.{u, v, w} R Q).Additive where
  map_add := rfl

section Laws

variable (R : Type u) [Ring R] [Finite R] {Q : Type v} [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q]
  (V : Stacks.Injectives.ContinuousModule.{u, v, w} R Q)
  (W : Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q)

/-! The module laws of `internalHomModule`, read on `internalHomSMul`. -/

/-- `1 ∈ Rᵐᵒᵖ[[Q]]` acts as the identity on `Hom_ℤ(V, W)`. -/
lemma internalHomSMul_one (φ : V.obj.obj.V →+ W.obj.obj.V) : internalHomSMul R V W 1 φ = φ :=
    (internalHomModule R V W).one_smul φ

/-- The action of `Rᵐᵒᵖ[[Q]]` on `Hom_ℤ(V, W)` is associative: `(x * y) • φ = x • (y • φ)`. -/
lemma internalHomSMul_mul (x y : CompletedGroupAlgebra Rᵐᵒᵖ Q) (φ : V.obj.obj.V →+ W.obj.obj.V) :
    internalHomSMul R V W (x * y) φ = internalHomSMul R V W x (internalHomSMul R V W y φ) :=
    (internalHomModule R V W).mul_smul x y φ

/-- The action on `Hom_ℤ(V, W)` is additive in the scalar: `(x + y) • φ = x • φ + y • φ`. -/
lemma internalHomSMul_add_left (x y : CompletedGroupAlgebra Rᵐᵒᵖ Q)
    (φ : V.obj.obj.V →+ W.obj.obj.V) :
    internalHomSMul R V W (x + y) φ = internalHomSMul R V W x φ + internalHomSMul R V W y φ :=
    (internalHomModule R V W).add_smul x y φ

/-- `0 ∈ Rᵐᵒᵖ[[Q]]` acts as zero on `Hom_ℤ(V, W)`. -/
lemma internalHomSMul_zero_left (φ : V.obj.obj.V →+ W.obj.obj.V) :
    internalHomSMul R V W 0 φ = 0 :=
    (internalHomModule R V W).zero_smul φ

/-- The action of `x ∈ Rᵐᵒᵖ[[Q]]` on `Hom_ℤ(V, W)` is additive: `x • (φ + ψ) = x • φ + x • ψ`. -/
lemma internalHomSMul_add_right (x : CompletedGroupAlgebra Rᵐᵒᵖ Q)
    (φ ψ : V.obj.obj.V →+ W.obj.obj.V) :
    internalHomSMul R V W x (φ + ψ) = internalHomSMul R V W x φ + internalHomSMul R V W x ψ :=
    (internalHomModule R V W).smul_add x φ ψ

/-- `x ∈ Rᵐᵒᵖ[[Q]]` sends the zero map `V → W` to zero. -/
lemma internalHomSMul_zero_right (x : CompletedGroupAlgebra Rᵐᵒᵖ Q) :
    internalHomSMul R V W x 0 = 0 :=
    (internalHomModule R V W).smul_zero x

variable {V W} in
/-- The action of `x ∈ Rᵐᵒᵖ[[Q]]` on a morphism of the underlying abelian groups. -/
def compSMul (x : CompletedGroupAlgebra Rᵐᵒᵖ Q)
    (f : (forgetAb R Q).obj V ⟶ (forgetAb ℤ Q).obj W) :
    (forgetAb R Q).obj V ⟶ (forgetAb ℤ Q).obj W :=
  AddCommGrpCat.ofHom (internalHomSMul R V W x f.hom)

variable {V W}

/-- The underlying additive map of `compSMul R x f` is `internalHomSMul R V W x f.hom`. -/
lemma compSMul_hom (x : CompletedGroupAlgebra Rᵐᵒᵖ Q)
    (f : (forgetAb R Q).obj V ⟶ (forgetAb ℤ Q).obj W) :
    (compSMul R x f).hom = internalHomSMul R V W x f.hom := rfl

/-- `1 ∈ Rᵐᵒᵖ[[Q]]` acts on morphisms `V ⟶ W` of abelian groups as the identity. -/
lemma compSMul_one (f : (forgetAb R Q).obj V ⟶ (forgetAb ℤ Q).obj W) : compSMul R 1 f = f :=
  AddCommGrpCat.hom_ext (internalHomSMul_one R V W f.hom)

/-- `compSMul` is associative: `(x * y)` acts as `x` after `y`. -/
lemma compSMul_mul (x y : CompletedGroupAlgebra Rᵐᵒᵖ Q)
    (f : (forgetAb R Q).obj V ⟶ (forgetAb ℤ Q).obj W) :
    compSMul R (x * y) f = compSMul R x (compSMul R y f) :=
  AddCommGrpCat.hom_ext (internalHomSMul_mul R V W x y f.hom)

/-- `compSMul` is additive in the scalar. -/
lemma compSMul_add_left (x y : CompletedGroupAlgebra Rᵐᵒᵖ Q)
    (f : (forgetAb R Q).obj V ⟶ (forgetAb ℤ Q).obj W) :
    compSMul R (x + y) f = compSMul R x f + compSMul R y f :=
  AddCommGrpCat.hom_ext (internalHomSMul_add_left R V W x y f.hom)

/-- `0 ∈ Rᵐᵒᵖ[[Q]]` acts on morphisms `V ⟶ W` of abelian groups as zero. -/
lemma compSMul_zero_left (f : (forgetAb R Q).obj V ⟶ (forgetAb ℤ Q).obj W) :
    compSMul R 0 f = 0 :=
  AddCommGrpCat.hom_ext (internalHomSMul_zero_left R V W f.hom)

/-- `compSMul R x` is additive in the morphism. -/
lemma compSMul_add_right (x : CompletedGroupAlgebra Rᵐᵒᵖ Q)
    (f g : (forgetAb R Q).obj V ⟶ (forgetAb ℤ Q).obj W) :
    compSMul R x (f + g) = compSMul R x f + compSMul R x g :=
  AddCommGrpCat.hom_ext (internalHomSMul_add_right R V W x f.hom g.hom)

/-- `compSMul R x` sends the zero morphism to zero. -/
lemma compSMul_zero_right (x : CompletedGroupAlgebra Rᵐᵒᵖ Q) :
    compSMul R x (0 : (forgetAb R Q).obj V ⟶ (forgetAb ℤ Q).obj W) = 0 :=
  AddCommGrpCat.hom_ext (internalHomSMul_zero_right R V W x)

/-- `compSMul R x` commutes with the action of the units `±1` of `ℤ`. -/
lemma compSMul_units_smul (x : CompletedGroupAlgebra Rᵐᵒᵖ Q) (ε : ℤˣ)
    (f : (forgetAb R Q).obj V ⟶ (forgetAb ℤ Q).obj W) :
    compSMul R x (ε • f) = ε • compSMul R x f := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · rw [one_smul, one_smul]
  · rw [Units.neg_smul, one_smul, Units.neg_smul, one_smul, ← sub_eq_zero, sub_neg_eq_add,
      ← compSMul_add_right, neg_add_cancel, compSMul_zero_right]

/-- The action commutes with postcomposition by a morphism of discrete `ℤ`-`Q`-modules. -/
lemma compSMul_comp {W' : Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q} (g : W ⟶ W')
    (x : CompletedGroupAlgebra Rᵐᵒᵖ Q) (f : (forgetAb R Q).obj V ⟶ (forgetAb ℤ Q).obj W) :
    compSMul R x f ≫ (forgetAb ℤ Q).map g = compSMul R x (f ≫ (forgetAb ℤ Q).map g) :=
  AddCommGrpCat.hom_ext (internalHom_postcomp_smul R Q V g x f.hom)

/-- The action commutes with precomposition by a morphism of discrete `R`-`Q`-modules. -/
lemma comp_compSMul {V' : Stacks.Injectives.ContinuousModule.{u, v, w} R Q} (g : V' ⟶ V)
    (x : CompletedGroupAlgebra Rᵐᵒᵖ Q) (f : (forgetAb R Q).obj V ⟶ (forgetAb ℤ Q).obj W) :
    (forgetAb R Q).map g ≫ compSMul R x f = compSMul R x ((forgetAb R Q).map g ≫ f) :=
  AddCommGrpCat.hom_ext (internalHom_precomp_smul R Q g W x f.hom)

end Laws

variable (R : Type u) [Ring R] [Finite R] {Q : Type v} [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q]
  (V : CochainComplex (Stacks.Injectives.ContinuousModule.{u, v, w} R Q) ℤ)
  (W : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q) ℤ)

/-- The underlying complex of abelian groups of a complex of discrete `R`-`Q`-modules. -/
abbrev underlyingAb (V : CochainComplex (Stacks.Injectives.ContinuousModule.{u, v, w} R Q) ℤ) :
    CochainComplex AddCommGrpCat.{w} ℤ :=
  ((forgetAb.{u, v, w} R Q).mapHomologicalComplex _).obj V

/-- **The cochains of the internal Hom complex** in degree `n`: Mathlib's cochains between the
underlying complexes of abelian groups. A type synonym, so that it can carry the
`Rᵐᵒᵖ[[Q]]`-module structure. -/
def InternalHomCochain (n : ℤ) : Type w :=
  Cochain (underlyingAb R V) (underlyingAb ℤ W) n

namespace InternalHomCochain

variable {R V W} {n : ℤ}

/-- A cochain, seen in `InternalHomCochain`. -/
def of (z : Cochain (underlyingAb R V) (underlyingAb ℤ W) n) : InternalHomCochain R V W n := z

/-- The underlying cochain. -/
def toCochain (z : InternalHomCochain R V W n) : Cochain (underlyingAb R V) (underlyingAb ℤ W) n :=
  z

omit [Finite R] [IsTopologicalGroup Q] [CompactSpace Q] in
/-- `toCochain` undoes `of`. -/
@[simp] lemma toCochain_of (z : Cochain (underlyingAb R V) (underlyingAb ℤ W) n) :
    toCochain (of z) = z := rfl
omit [Finite R] [IsTopologicalGroup Q] [CompactSpace Q] in
/-- `of` undoes `toCochain`. -/
@[simp] lemma of_toCochain (z : InternalHomCochain R V W n) : of (toCochain z) = z := rfl

omit [Finite R] [IsTopologicalGroup Q] [CompactSpace Q] in
/-- Two internal Hom cochains are equal as soon as their underlying cochains are. -/
lemma ext {z z' : InternalHomCochain R V W n} (h : toCochain z = toCochain z') : z = z' := h

/-- The additive group structure of the underlying cochains. -/
instance : AddCommGroup (InternalHomCochain R V W n) :=
  inferInstanceAs (AddCommGroup (Cochain (underlyingAb R V) (underlyingAb ℤ W) n))

omit [Finite R] [IsTopologicalGroup Q] [CompactSpace Q] in
/-- `toCochain` is additive. -/
@[simp] lemma toCochain_add (z z' : InternalHomCochain R V W n) :
    toCochain (z + z') = toCochain z + toCochain z' := rfl
omit [Finite R] [IsTopologicalGroup Q] [CompactSpace Q] in
/-- `toCochain` sends `0` to `0`. -/
@[simp] lemma toCochain_zero : toCochain (0 : InternalHomCochain R V W n) = 0 := rfl

/-- `x ∈ Rᵐᵒᵖ[[Q]]` acts on each component `Hom_ℤ(V^p, W^q)`. -/
instance : SMul (CompletedGroupAlgebra Rᵐᵒᵖ Q) (InternalHomCochain R V W n) where
  smul x z := of (Cochain.mk fun p q hpq => compSMul R x ((toCochain z).v p q hpq))

/-- The components of `x • z` are those of `z`, acted on by `x` through `compSMul`. -/
lemma toCochain_smul_v (x : CompletedGroupAlgebra Rᵐᵒᵖ Q) (z : InternalHomCochain R V W n)
    (p q : ℤ) (hpq : p + n = q) :
    (toCochain (x • z)).v p q hpq = compSMul R x ((toCochain z).v p q hpq) := rfl

/-- The `Rᵐᵒᵖ[[Q]]`-module structure on the cochains of the internal Hom complex, acting on each
component. -/
instance : Module (CompletedGroupAlgebra Rᵐᵒᵖ Q) (InternalHomCochain R V W n) where
  one_smul z := ext <| Cochain.ext _ _ fun p q hpq => by
    rw [toCochain_smul_v, compSMul_one]
  mul_smul x y z := ext <| Cochain.ext _ _ fun p q hpq => by
    rw [toCochain_smul_v, toCochain_smul_v, toCochain_smul_v, compSMul_mul]
  smul_zero x := ext <| Cochain.ext _ _ fun p q hpq => by
    rw [toCochain_smul_v, toCochain_zero, Cochain.zero_v, compSMul_zero_right]
  smul_add x z z' := ext <| Cochain.ext _ _ fun p q hpq => by
    rw [toCochain_add, Cochain.add_v, toCochain_smul_v, toCochain_smul_v, toCochain_smul_v,
      toCochain_add, Cochain.add_v, compSMul_add_right]
  add_smul x y z := ext <| Cochain.ext _ _ fun p q hpq => by
    rw [toCochain_add, Cochain.add_v, toCochain_smul_v, toCochain_smul_v, toCochain_smul_v,
      compSMul_add_left]
  zero_smul z := ext <| Cochain.ext _ _ fun p q hpq => by
    rw [toCochain_smul_v, compSMul_zero_left]
    rfl

end InternalHomCochain

open InternalHomCochain

/-- The differential of the internal Hom complex is `Rᵐᵒᵖ[[Q]]`-linear. -/
def internalHomδ (n m : ℤ) :
    InternalHomCochain R V W n →ₗ[CompletedGroupAlgebra Rᵐᵒᵖ Q] InternalHomCochain R V W m where
  toFun z := of (δ n m (toCochain z))
  map_add' z z' := δ_add n m (toCochain z) (toCochain z')
  map_smul' x z := by
    apply InternalHomCochain.ext
    by_cases hnm : n + 1 = m
    · refine Cochain.ext _ _ fun p q hpq => ?_
      change (δ n m (toCochain (x • z))).v p q hpq =
        (toCochain (x • of (R := R) (V := V) (W := W) (δ n m (toCochain z)))).v p q hpq
      rw [toCochain_smul_v, toCochain_of, δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl,
        δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl, toCochain_smul_v, toCochain_smul_v,
        compSMul_add_right, compSMul_units_smul]
      congr 1
      · exact compSMul_comp R ((W.d (q - 1) q)) x _
      · congr 1
        exact comp_compSMul R (V.d p (p + 1)) x _
    · have h0 : ∀ z' : Cochain (underlyingAb R V) (underlyingAb ℤ W) n, δ n m z' = 0 :=
        fun z' => δ_shape n m hnm z'
      rw [h0, h0]
      change (0 : Cochain _ _ m) = toCochain (x • (0 : InternalHomCochain R V W m))
      rw [smul_zero]
      rfl

/-- **The internal Hom complex** `Hom^•_ℤ(V, W)` of a complex `V` of discrete `R`-`Q`-modules and
a complex `W` of discrete `ℤ`-`Q`-modules, as a complex of `Rᵐᵒᵖ[[Q]]`-modules: degree `n` is
`∏_p Hom_ℤ(V^p, W^{p+n})`, the differential is `δ`. -/
def internalHomComplex : CochainComplex (ModuleCat.{w} (CompletedGroupAlgebra Rᵐᵒᵖ Q)) ℤ where
  X n := ModuleCat.of _ (InternalHomCochain R V W n)
  d n m := ModuleCat.ofHom (internalHomδ R V W n m)
  shape n m h := by
    refine ModuleCat.hom_ext <| LinearMap.ext fun z => ?_
    change δ n m (toCochain z) = 0
    rw [δ_shape]
    simpa using h
  d_comp_d' i j k _ _ :=
    ModuleCat.hom_ext <| LinearMap.ext fun z => δ_δ i j k (toCochain z)

/-- The differential of the internal Hom complex is the differential `δ` of the underlying
cochains. -/
@[simp]
lemma internalHomComplex_d_apply (n m : ℤ) (z : InternalHomCochain R V W n) :
    toCochain (R := R) (V := V) (W := W) (((internalHomComplex R V W).d n m).hom z) =
      δ n m (toCochain z) := rfl

/-- **Postcomposition** `g_* : Hom^•_ℤ(V, W) ⟶ Hom^•_ℤ(V, W')` with a morphism of complexes of
discrete `ℤ`-`Q`-modules; it is `Rᵐᵒᵖ[[Q]]`-linear. -/
def internalHomComplexPostcomp
    {W W' : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q) ℤ} (g : W ⟶ W') :
    internalHomComplex R V W ⟶ internalHomComplex R V W' where
  f n := ModuleCat.ofHom
    { toFun z := of ((toCochain z).comp
        (Cochain.ofHom (((forgetAb ℤ Q).mapHomologicalComplex _).map g)) (add_zero n))
      map_add' z z' := Cochain.add_comp _ _ _ _
      map_smul' x z := by
        apply InternalHomCochain.ext
        refine Cochain.ext _ _ fun p q hpq => ?_
        change ((toCochain (x • z)).comp _ (add_zero n)).v p q hpq =
          (toCochain (x • of (R := R) (V := V) (W := W')
            ((toCochain z).comp _ (add_zero n)))).v p q hpq
        rw [toCochain_smul_v, toCochain_of, Cochain.comp_zero_cochain_v,
          Cochain.comp_zero_cochain_v, toCochain_smul_v, Cochain.ofHom_v]
        exact compSMul_comp R (g.f q) x _ }
  comm' _ m _ :=
    ModuleCat.hom_ext <| LinearMap.ext fun z => δ_comp_ofHom (toCochain z) _ m

/-- In degree `n`, postcomposition with `g` composes the underlying cochain with the cochain of
`g`. -/
@[simp]
lemma internalHomComplexPostcomp_f_apply
    {W W' : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q) ℤ} (g : W ⟶ W')
    (n : ℤ) (z : InternalHomCochain R V W n) :
    toCochain (R := R) (V := V) (W := W') (((internalHomComplexPostcomp R V g).f n).hom z) =
      (toCochain z).comp (Cochain.ofHom (((forgetAb ℤ Q).mapHomologicalComplex _).map g))
        (add_zero n) := rfl

/-- **Forgetting the module structure** recovers Mathlib's Hom complex of the underlying complexes
of abelian groups, degreewise by the identity. -/
def internalHomComplexForgetIso :
    ((forget₂ (ModuleCat.{w} (CompletedGroupAlgebra Rᵐᵒᵖ Q))
        AddCommGrpCat.{w}).mapHomologicalComplex _).obj (internalHomComplex R V W) ≅
      CochainComplex.HomComplex (underlyingAb R V) (underlyingAb ℤ W) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (AddEquiv.refl (Cochain (underlyingAb R V) (underlyingAb ℤ W) n)).toAddCommGrpIso)
    (by intro i j _; ext z; rfl)

/-- **Postcomposition is a quasi-isomorphism as soon as the underlying morphism of complexes of
abelian groups is a homotopy equivalence.** The homotopies need not be equivariant: being a
quasi-isomorphism is read on the underlying abelian groups. -/
lemma quasiIso_internalHomComplexPostcomp
    {W W' : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q) ℤ} (g : W ⟶ W')
    (e : HomotopyEquiv (underlyingAb ℤ W) (underlyingAb ℤ W'))
    (he : e.hom = ((forgetAb ℤ Q).mapHomologicalComplex _).map g) :
    QuasiIso (internalHomComplexPostcomp R V g) := by
  let ρ : ℤ →+* End (underlyingAb R V) := Int.castRingHom _
  have hq := Stacks.HomComplex.quasiIso_opModuleHomComplexPostcomp ρ e
  have hq' := (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (Stacks.HomComplex.opModuleHomComplexPostcomp ρ e.hom)
    (forget₂ (ModuleCat.{w} ℤᵐᵒᵖ) AddCommGrpCat.{w})).2 hq
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat.{w} (CompletedGroupAlgebra Rᵐᵒᵖ Q)) AddCommGrpCat.{w})]
  refine (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk
    ((internalHomComplexForgetIso R V W).trans
      (Stacks.HomComplex.opModuleHomComplexForgetIso ρ (underlyingAb ℤ W)).symm)
    ((internalHomComplexForgetIso R V W').trans
      (Stacks.HomComplex.opModuleHomComplexForgetIso ρ (underlyingAb ℤ W')).symm) ?_)).2 hq'
  ext n z
  show (toCochain (R := R) (V := V) (W := W) z).comp (Cochain.ofHom e.hom) (add_zero n) =
    (toCochain (R := R) (V := V) (W := W) z).comp
      (Cochain.ofHom (((forgetAb ℤ Q).mapHomologicalComplex _).map g)) (add_zero n)
  rw [he]

/-- **Precomposition** `g^* : Hom^•_ℤ(V, W) ⟶ Hom^•_ℤ(V', W)` with a morphism of complexes of
discrete `R`-`Q`-modules `g : V' ⟶ V`; it is `Rᵐᵒᵖ[[Q]]`-linear. -/
def internalHomComplexPrecomp
    {V' : CochainComplex (Stacks.Injectives.ContinuousModule.{u, v, w} R Q) ℤ} (g : V' ⟶ V) :
    internalHomComplex R V W ⟶ internalHomComplex R V' W where
  f n := ModuleCat.ofHom
    { toFun z := of ((Cochain.ofHom (((forgetAb R Q).mapHomologicalComplex _).map g)).comp
        (toCochain z) (zero_add n))
      map_add' z z' := Cochain.comp_add _ _ _ _
      map_smul' x z := by
        apply InternalHomCochain.ext
        refine Cochain.ext _ _ fun p q hpq => ?_
        change ((Cochain.ofHom _).comp (toCochain (x • z)) (zero_add n)).v p q hpq =
          (toCochain (x • of (R := R) (V := V') (W := W)
            ((Cochain.ofHom _).comp (toCochain z) (zero_add n)))).v p q hpq
        rw [toCochain_smul_v, toCochain_of, Cochain.zero_cochain_comp_v,
          Cochain.zero_cochain_comp_v, toCochain_smul_v, Cochain.ofHom_v]
        exact comp_compSMul R (g.f p) x _ }
  comm' _ m _ :=
    ModuleCat.hom_ext <| LinearMap.ext fun z => δ_ofHom_comp _ (toCochain z) m

/-- In degree `n`, precomposition with `g` composes the cochain of `g` with the underlying
cochain. -/
@[simp]
lemma internalHomComplexPrecomp_f_apply
    {V' : CochainComplex (Stacks.Injectives.ContinuousModule.{u, v, w} R Q) ℤ} (g : V' ⟶ V)
    (n : ℤ) (z : InternalHomCochain R V W n) :
    toCochain (R := R) (V := V') (W := W) (((internalHomComplexPrecomp R V W g).f n).hom z) =
      (Cochain.ofHom (((forgetAb R Q).mapHomologicalComplex _).map g)).comp (toCochain z)
        (zero_add n) := rfl

/-- Pre- and postcomposition commute. -/
lemma internalHomComplexPrecomp_postcomp
    {V' : CochainComplex (Stacks.Injectives.ContinuousModule.{u, v, w} R Q) ℤ} (g : V' ⟶ V)
    {W' : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q) ℤ} (h : W ⟶ W') :
    internalHomComplexPrecomp R V W g ≫ internalHomComplexPostcomp R V' h =
      internalHomComplexPostcomp R V h ≫ internalHomComplexPrecomp R V W' g := by
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext <| LinearMap.ext fun z => ?_
  apply InternalHomCochain.ext
  show ((Cochain.ofHom _).comp (toCochain (R := R) (V := V) (W := W) z) (zero_add n)).comp
      (Cochain.ofHom _) (add_zero n) =
    (Cochain.ofHom _).comp ((toCochain (R := R) (V := V) (W := W) z).comp (Cochain.ofHom _)
      (add_zero n)) (zero_add n)
  exact Cochain.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)

end Stacks.ContinuousCohomology

end
