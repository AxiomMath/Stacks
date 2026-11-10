module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Hom complexes out of a complex with a ring action

Let `𝒜` be a preadditive category, `R` a ring, and `F` a cochain complex in `𝒜` on which `R`
acts by endomorphisms of complexes, i.e. a ring homomorphism `ρ : R →+* End F`. For every cochain
complex `G` in `𝒜`, precomposition with `ρ r` makes each group of cochains `Cochain F G n` a
module over the opposite ring `Rᵐᵒᵖ`, and the differential `δ` is `Rᵐᵒᵖ`-linear because each
`ρ r` is a morphism of complexes. This file assembles these modules into a cochain complex of
`Rᵐᵒᵖ`-modules, the Hom complex `Hom^•(F, G)` with its right `R`-module structure.

This is the structure carried by the Hom complex from the underlying complex of abelian sheaves
of a complex of sheaves of (left) `R`-modules into a complex of abelian sheaves, for a ring `R`
that need not be commutative: the `R`-linear structure of the source is only available as a
family of additive endomorphisms of the underlying abelian sheaves. That is why no `R`-linear
structure on `𝒜` is assumed.

## Main definitions

* `Stacks.HomComplex.OpCochain`: the cochains `Cochain F G n` with the `Rᵐᵒᵖ`-module structure
  `op r • z = ρ r ≫ z`.
* `Stacks.HomComplex.opModuleHomComplex`: the Hom complex `Hom^•(F, G)` as a complex of
  `Rᵐᵒᵖ`-modules.
* `Stacks.HomComplex.opModuleHomComplexPostcomp` and
  `Stacks.HomComplex.opModuleHomComplexPrecomp`: postcomposition with a morphism of complexes,
  and precomposition with an `R`-equivariant one.
* `Stacks.HomComplex.opModuleHomComplexMap`: the map of Hom complexes induced by an additive
  functor.

## Implementation notes

The multiplication of `End F` is `f * g = g ≫ f` (`CategoryTheory.End.mul_asHom`), so
`ρ (s * r) = ρ r ≫ ρ s`, and `op r • (op s • z) = ρ r ≫ ρ s ≫ z = ρ (s * r) ≫ z
= (op r * op s) • z`: precomposition is a left action of `Rᵐᵒᵖ`, i.e. a right action of `R`.
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.HomComplex MulOpposite

universe v u w

namespace Stacks.HomComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] {R : Type w} [Ring R]
  {F : CochainComplex 𝒜 ℤ} (ρ : R →+* End F) (G : CochainComplex 𝒜 ℤ)

/-- The cochains `Cochain F G n`, as a type carrying the `Rᵐᵒᵖ`-module structure coming from an
action `ρ : R →+* End F` of `R` on the source. It is a type synonym, so that the module
structure, which depends on `ρ`, is found by instance search. -/
def OpCochain (_ρ : R →+* End F) (G : CochainComplex 𝒜 ℤ) (n : ℤ) : Type v := Cochain F G n

namespace OpCochain

variable {ρ G} {n : ℤ}

/-- A cochain, seen in `OpCochain`. -/
def of (z : Cochain F G n) : OpCochain ρ G n := z

/-- The underlying cochain. -/
def toCochain (z : OpCochain ρ G n) : Cochain F G n := z

/-- `toCochain` is a left inverse of `of`. -/
@[simp] lemma toCochain_of (z : Cochain F G n) : toCochain (of (ρ := ρ) z) = z := rfl
/-- `of` is a left inverse of `toCochain`. -/
@[simp] lemma of_toCochain (z : OpCochain ρ G n) : of (toCochain z) = z := rfl

/-- `OpCochain ρ G n` carries the additive group structure of `Cochain F G n`. -/
instance : AddCommGroup (OpCochain ρ G n) := inferInstanceAs (AddCommGroup (Cochain F G n))

/-- `toCochain` is additive. -/
@[simp] lemma toCochain_add (z w : OpCochain ρ G n) :
    toCochain (z + w) = toCochain z + toCochain w := rfl
/-- `toCochain` sends `0` to `0`. -/
@[simp] lemma toCochain_zero : toCochain (0 : OpCochain ρ G n) = 0 := rfl

/-- Two elements of `OpCochain` are equal if their underlying cochains are. -/
lemma ext {z w : OpCochain ρ G n} (h : toCochain z = toCochain w) : z = w := h

/-- `op r` acts on cochains by precomposition with `ρ r`. -/
instance : SMul Rᵐᵒᵖ (OpCochain ρ G n) where
  smul r z := of ((Cochain.ofHom (ρ r.unop).asHom).comp (toCochain z) (zero_add n))

/-- The underlying cochain of `op r • z` is `ρ r ≫ z`. -/
@[simp] lemma toCochain_smul (r : Rᵐᵒᵖ) (z : OpCochain ρ G n) :
    toCochain (r • z) = (Cochain.ofHom (ρ r.unop).asHom).comp (toCochain z) (zero_add n) := rfl

/-- Precomposition with the action makes the cochains an `Rᵐᵒᵖ`-module. -/
instance : Module Rᵐᵒᵖ (OpCochain ρ G n) where
  one_smul z := by
    change (Cochain.ofHom (ρ 1).asHom).comp (toCochain z) (zero_add n) = toCochain z
    rw [map_one, End.one_asHom]
    exact Cochain.id_comp _
  mul_smul r s z := by
    change (Cochain.ofHom (ρ (s.unop * r.unop)).asHom).comp (toCochain z) (zero_add n) =
      (Cochain.ofHom (ρ r.unop).asHom).comp ((Cochain.ofHom (ρ s.unop).asHom).comp (toCochain z)
        (zero_add n)) (zero_add n)
    rw [map_mul, End.mul_asHom, Cochain.ofHom_comp]
    exact Cochain.comp_assoc _ _ _ (zero_add 0) (zero_add n) (by omega)
  smul_zero r := Cochain.comp_zero (Cochain.ofHom (ρ r.unop).asHom) (zero_add n)
  smul_add r z w := Cochain.comp_add _ (toCochain z) (toCochain w) (zero_add n)
  add_smul r s z := by
    change (Cochain.ofHom (ρ (r.unop + s.unop)).asHom).comp (toCochain z) (zero_add n) =
      (Cochain.ofHom (ρ r.unop).asHom).comp (toCochain z) (zero_add n) +
        (Cochain.ofHom (ρ s.unop).asHom).comp (toCochain z) (zero_add n)
    rw [map_add, End.add_asHom, Cochain.ofHom_add, Cochain.add_comp]
  zero_smul z := by
    change (Cochain.ofHom (ρ 0).asHom).comp (toCochain z) (zero_add n) = (0 : Cochain F G n)
    rw [map_zero, End.zero_asHom, Cochain.ofHom_zero, Cochain.zero_comp]

end OpCochain

open OpCochain

/-- The Hom-complex differential `δ n m` is `Rᵐᵒᵖ`-linear, because every `ρ r` is a morphism of
complexes. -/
def δOpLinear (n m : ℤ) : OpCochain ρ G n →ₗ[Rᵐᵒᵖ] OpCochain ρ G m where
  toFun z := of (δ n m (toCochain z))
  map_add' z w := δ_add n m (toCochain z) (toCochain w)
  map_smul' r z := δ_ofHom_comp (ρ r.unop).asHom (toCochain z) m

/-- **The Hom complex `Hom^•(F, G)` as a complex of `Rᵐᵒᵖ`-modules**, for an action
`ρ : R →+* End F` of `R` on the source: its degree-`n` term is `Cochain F G n`, on which `op r`
acts by precomposition with `ρ r`, and its differential is `δ`. -/
def opModuleHomComplex : CochainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ where
  X n := ModuleCat.of Rᵐᵒᵖ (OpCochain ρ G n)
  d n m := ModuleCat.ofHom (δOpLinear ρ G n m)
  shape n m h := by
    refine ModuleCat.hom_ext <| LinearMap.ext fun z => ?_
    change δ n m (toCochain z) = 0
    rw [δ_shape]
    simpa using h
  d_comp_d' i j k _ _ :=
    ModuleCat.hom_ext <| LinearMap.ext fun z => δ_δ i j k (toCochain z)

/-- The differential of `opModuleHomComplex ρ G` is `δ` on underlying cochains. -/
@[simp]
lemma opModuleHomComplex_d_apply (n m : ℤ) (z : OpCochain ρ G n) :
    toCochain (ρ := ρ) (G := G) (((opModuleHomComplex ρ G).d n m).hom z) =
      δ n m (toCochain z) := rfl

/-- **Postcomposition** `h_* : Hom^•(F, G) ⟶ Hom^•(F, G')` with a morphism of complexes
`h : G ⟶ G'`; it is `Rᵐᵒᵖ`-linear because the action is by precomposition. -/
def opModuleHomComplexPostcomp {G G' : CochainComplex 𝒜 ℤ} (h : G ⟶ G') :
    opModuleHomComplex ρ G ⟶ opModuleHomComplex ρ G' where
  f n := ModuleCat.ofHom
    { toFun z := of ((toCochain z).comp (Cochain.ofHom h) (add_zero n))
      map_add' z w := Cochain.add_comp (toCochain z) (toCochain w) (Cochain.ofHom h) (add_zero n)
      map_smul' r z := Cochain.comp_assoc (Cochain.ofHom (ρ r.unop).asHom) (toCochain z)
        (Cochain.ofHom h) (zero_add n) (add_zero n) (by omega) }
  comm' _ m _ :=
    ModuleCat.hom_ext <| LinearMap.ext fun z => δ_comp_ofHom (toCochain z) h m

/-- In degree `n`, postcomposition with `h` sends a cochain `z` to `z ≫ h`. -/
@[simp]
lemma opModuleHomComplexPostcomp_f_apply {G G' : CochainComplex 𝒜 ℤ} (h : G ⟶ G') (n : ℤ)
    (z : OpCochain ρ G n) :
    toCochain (ρ := ρ) (G := G') (((opModuleHomComplexPostcomp ρ h).f n).hom z) =
      (toCochain z).comp (Cochain.ofHom h) (add_zero n) := rfl

/-- Postcomposition with the identity is the identity. -/
lemma opModuleHomComplexPostcomp_id :
    opModuleHomComplexPostcomp ρ (𝟙 G) = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext <| LinearMap.ext fun z => ?_
  exact Cochain.comp_id (toCochain z)

/-- Postcomposition with `h ≫ h'` is postcomposition with `h` followed by postcomposition with
`h'`. -/
lemma opModuleHomComplexPostcomp_comp {G G' G'' : CochainComplex 𝒜 ℤ} (h : G ⟶ G')
    (h' : G' ⟶ G'') :
    opModuleHomComplexPostcomp ρ (h ≫ h') =
      opModuleHomComplexPostcomp ρ h ≫ opModuleHomComplexPostcomp ρ h' := by
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext <| LinearMap.ext fun z => ?_
  change (toCochain z).comp (Cochain.ofHom (h ≫ h')) (add_zero n)
      = ((toCochain z).comp (Cochain.ofHom h) (add_zero n)).comp (Cochain.ofHom h') (add_zero n)
  rw [Cochain.ofHom_comp]
  exact (Cochain.comp_assoc _ (Cochain.ofHom h) (Cochain.ofHom h') (add_zero n) (zero_add 0)
    (by omega)).symm

/-- **Precomposition** `g^* : Hom^•(F, G) ⟶ Hom^•(F', G)` with a morphism of complexes
`g : F' ⟶ F` intertwining the two actions; it is `Rᵐᵒᵖ`-linear by the intertwining. -/
def opModuleHomComplexPrecomp {F' : CochainComplex 𝒜 ℤ} (ρ' : R →+* End F') (g : F' ⟶ F)
    (hg : ∀ r : R, (ρ' r).asHom ≫ g = g ≫ (ρ r).asHom) :
    opModuleHomComplex ρ G ⟶ opModuleHomComplex ρ' G where
  f n := ModuleCat.ofHom
    { toFun z := of ((Cochain.ofHom g).comp (toCochain z) (zero_add n))
      map_add' z w := Cochain.comp_add (Cochain.ofHom g) (toCochain z) (toCochain w) (zero_add n)
      map_smul' r z := by
        change (Cochain.ofHom g).comp ((Cochain.ofHom (ρ r.unop).asHom).comp (toCochain z)
            (zero_add n)) (zero_add n) =
          (Cochain.ofHom (ρ' r.unop).asHom).comp ((Cochain.ofHom g).comp (toCochain z) (zero_add n))
            (zero_add n)
        rw [← Cochain.comp_assoc _ _ _ (zero_add 0) (zero_add n) (by omega),
          ← Cochain.comp_assoc _ _ _ (zero_add 0) (zero_add n) (by omega),
          ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, hg] }
  comm' _ m _ :=
    ModuleCat.hom_ext <| LinearMap.ext fun z => δ_ofHom_comp g (toCochain z) m

/-- In degree `n`, precomposition with `g` sends a cochain `z` to `g ≫ z`. -/
@[simp]
lemma opModuleHomComplexPrecomp_f_apply {F' : CochainComplex 𝒜 ℤ} (ρ' : R →+* End F')
    (g : F' ⟶ F) (hg : ∀ r : R, (ρ' r).asHom ≫ g = g ≫ (ρ r).asHom) (n : ℤ) (z : OpCochain ρ G n) :
    toCochain (ρ := ρ') (G := G) (((opModuleHomComplexPrecomp ρ G ρ' g hg).f n).hom z) =
      (Cochain.ofHom g).comp (toCochain z) (zero_add n) := rfl

/-- Pre- and postcomposition commute. -/
lemma opModuleHomComplexPrecomp_postcomp {F' : CochainComplex 𝒜 ℤ} (ρ' : R →+* End F')
    (g : F' ⟶ F) (hg : ∀ r : R, (ρ' r).asHom ≫ g = g ≫ (ρ r).asHom) {G' : CochainComplex 𝒜 ℤ}
    (h : G ⟶ G') :
    opModuleHomComplexPrecomp ρ G ρ' g hg ≫ opModuleHomComplexPostcomp ρ' h =
      opModuleHomComplexPostcomp ρ h ≫ opModuleHomComplexPrecomp ρ G' ρ' g hg := by
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext <| LinearMap.ext fun z => ?_
  change ((Cochain.ofHom g).comp (toCochain z) (zero_add n)).comp (Cochain.ofHom h) (add_zero n) =
    (Cochain.ofHom g).comp ((toCochain z).comp (Cochain.ofHom h) (add_zero n)) (zero_add n)
  exact Cochain.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)

/-- **Forgetting the module structure** recovers Mathlib's Hom complex of abelian groups
`CochainComplex.HomComplex F G`, degreewise by the identity. -/
def opModuleHomComplexForgetIso :
    ((forget₂ (ModuleCat.{v} Rᵐᵒᵖ) AddCommGrpCat.{v}).mapHomologicalComplex _).obj
        (opModuleHomComplex ρ G) ≅ HomComplex F G :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (AddEquiv.refl (Cochain F G n)).toAddCommGrpIso) (by
      intro i j _
      ext z
      rfl)

/-- The forward map of `opModuleHomComplexForgetIso` is the identity on cochains. -/
@[simp]
lemma opModuleHomComplexForgetIso_hom_f_apply (n : ℤ) (z : OpCochain ρ G n) :
    ((opModuleHomComplexForgetIso ρ G).hom.f n).hom z = toCochain z := rfl

/-- The inverse map of `opModuleHomComplexForgetIso` is the identity on cochains. -/
@[simp]
lemma opModuleHomComplexForgetIso_inv_f_apply (n : ℤ) (z : Cochain F G n) :
    toCochain (ρ := ρ) (G := G) (((opModuleHomComplexForgetIso ρ G).inv.f n).hom z) = z := rfl

section Homotopy

variable {G G' : CochainComplex 𝒜 ℤ} {φ₁ φ₂ : G ⟶ G'}

/-- The cochain of degree `-1` on Hom complexes, `z ↦ z ∘ h`, attached to a homotopy `h`
between two morphisms `G ⟶ G'`. -/
def postcompHomotopyCochain (H : Homotopy φ₁ φ₂) :
    Cochain (opModuleHomComplex ρ G) (opModuleHomComplex ρ G') (-1) :=
  Cochain.mk (fun p q hpq => ModuleCat.ofHom
    { toFun z := of ((toCochain z).comp (Cochain.ofHomotopy H) hpq)
      map_add' z w := Cochain.add_comp (toCochain z) (toCochain w) _ hpq
      map_smul' r z := Cochain.comp_assoc (Cochain.ofHom (ρ r.unop).asHom) (toCochain z)
        (Cochain.ofHomotopy H) (zero_add p) hpq (by omega) })

/-- The component of `postcompHomotopyCochain ρ H` from degree `p` to degree `q` sends a
cochain `z` to its composite with the degree `-1` cochain of the homotopy `H`. -/
lemma postcompHomotopyCochain_v (H : Homotopy φ₁ φ₂) (p q : ℤ) (hpq : p + -1 = q)
    (z : OpCochain ρ G p) :
    toCochain (ρ := ρ) (G := G') (((postcompHomotopyCochain ρ H).v p q hpq).hom z) =
      (toCochain z).comp (Cochain.ofHomotopy H) hpq := by
  simp [postcompHomotopyCochain]
  rfl

/-- **Postcomposition carries homotopies to homotopies**: a homotopy `h` between
`φ₁ φ₂ : G ⟶ G'` gives the homotopy `z ↦ z ∘ h` between `φ₁_*` and `φ₂_*`. The identity
`δ (z ∘ h) + (δ z) ∘ h = z ∘ δ h = z ∘ φ₁ - z ∘ φ₂` carries no sign. -/
def opModuleHomComplexPostcompHomotopy (H : Homotopy φ₁ φ₂) :
    Homotopy (opModuleHomComplexPostcomp ρ φ₁) (opModuleHomComplexPostcomp ρ φ₂) :=
  (Cochain.equivHomotopy _ _).symm ⟨postcompHomotopyCochain ρ H, by
    refine Cochain.ext₀ _ _ fun p => ?_
    rw [Cochain.add_v, δ_v (-1) 0 (neg_add_cancel 1) _ p p (add_zero p) (p - 1) (p + 1) rfl rfl,
      Cochain.ofHom_v, Cochain.ofHom_v]
    refine ModuleCat.hom_ext <| LinearMap.ext fun z => OpCochain.ext (ρ := ρ) (G := G') ?_
    have h := δ_comp (toCochain (ρ := ρ) (G := G) z) (Cochain.ofHomotopy H)
      (show p + -1 = p - 1 by omega) (p + 1) 0 p (by omega) rfl (neg_add_cancel 1)
    rw [δ_ofHomotopy, Cochain.comp_sub, Int.negOnePow_neg, Int.negOnePow_one,
      Units.neg_smul, one_smul] at h
    change (toCochain (ρ := ρ) (G := G) z).comp (Cochain.ofHom φ₁) (add_zero p) =
      δ (p - 1) p ((toCochain (ρ := ρ) (G := G) z).comp (Cochain.ofHomotopy H) (by omega)) +
        (0 : ℤ).negOnePow • (δ p (p + 1) (toCochain (ρ := ρ) (G := G) z)).comp
          (Cochain.ofHomotopy H) (by omega) +
        (toCochain (ρ := ρ) (G := G) z).comp (Cochain.ofHom φ₂) (add_zero p)
    rw [h, Int.negOnePow_zero, one_smul]
    abel⟩

/-- **Postcomposition with a homotopy equivalence is a homotopy equivalence** of Hom
complexes. -/
def opModuleHomComplexPostcompHomotopyEquiv (e : HomotopyEquiv G G') :
    HomotopyEquiv (opModuleHomComplex ρ G) (opModuleHomComplex ρ G') where
  hom := opModuleHomComplexPostcomp ρ e.hom
  inv := opModuleHomComplexPostcomp ρ e.inv
  homotopyHomInvId := by
    rw [← opModuleHomComplexPostcomp_comp, ← opModuleHomComplexPostcomp_id ρ G]
    exact opModuleHomComplexPostcompHomotopy ρ e.homotopyHomInvId
  homotopyInvHomId := by
    rw [← opModuleHomComplexPostcomp_comp, ← opModuleHomComplexPostcomp_id ρ G']
    exact opModuleHomComplexPostcompHomotopy ρ e.homotopyInvHomId

/-- Postcomposition with a homotopy equivalence is a quasi-isomorphism of Hom complexes. -/
lemma quasiIso_opModuleHomComplexPostcomp (e : HomotopyEquiv G G') :
    QuasiIso (opModuleHomComplexPostcomp ρ e.hom) :=
  (opModuleHomComplexPostcompHomotopyEquiv ρ e).quasiIso_hom

end Homotopy

section PrecompHomotopy

variable {F' : CochainComplex 𝒜 ℤ} (ρ' : R →+* End F') {g₁ g₂ : F' ⟶ F}
  (hg₁ : ∀ r : R, (ρ' r).asHom ≫ g₁ = g₁ ≫ (ρ r).asHom)
  (hg₂ : ∀ r : R, (ρ' r).asHom ≫ g₂ = g₂ ≫ (ρ r).asHom)

/-- An equivariant homotopy `h` commutes with the actions, as a cochain of degree `-1`. -/
lemma ofHomotopy_comp_ofHom_eq {H : Homotopy g₁ g₂}
    (hH : ∀ (r : R) (p q : ℤ) (hpq : p + -1 = q),
      (ρ' r).asHom.f p ≫ (Cochain.ofHomotopy H).v p q hpq =
        (Cochain.ofHomotopy H).v p q hpq ≫ (ρ r).asHom.f q)
    (r : R) :
    (Cochain.ofHomotopy H).comp (Cochain.ofHom (ρ r).asHom) (add_zero (-1)) =
      (Cochain.ofHom (ρ' r).asHom).comp (Cochain.ofHomotopy H) (zero_add (-1)) := by
  ext a b hab
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Cochain.ofHom_v, hH]

/-- The cochain of degree `-1` on Hom complexes, `z ↦ (-1)ᵖ h ∘ z` on `Hom^p`, attached to an
equivariant homotopy `h` between two morphisms `F' ⟶ F`. -/
def precompHomotopyCochain (H : Homotopy g₁ g₂)
    (hH : ∀ (r : R) (p q : ℤ) (hpq : p + -1 = q),
      (ρ' r).asHom.f p ≫ (Cochain.ofHomotopy H).v p q hpq =
        (Cochain.ofHomotopy H).v p q hpq ≫ (ρ r).asHom.f q) :
    Cochain (opModuleHomComplex ρ G) (opModuleHomComplex ρ' G) (-1) :=
  Cochain.mk (fun p q hpq => ModuleCat.ofHom
    { toFun z := of (p.negOnePow • (Cochain.ofHomotopy H).comp (toCochain z) (by omega))
      map_add' z w := by
        apply OpCochain.ext (ρ := ρ') (G := G)
        change p.negOnePow • (Cochain.ofHomotopy H).comp (toCochain z + toCochain w) _ = _
        rw [Cochain.comp_add, smul_add]
        rfl
      map_smul' r z := by
        apply OpCochain.ext (ρ := ρ') (G := G)
        change p.negOnePow • (Cochain.ofHomotopy H).comp
            ((Cochain.ofHom (ρ r.unop).asHom).comp (toCochain z) (zero_add p)) (by omega) =
          (Cochain.ofHom (ρ' r.unop).asHom).comp
            (p.negOnePow • (Cochain.ofHomotopy H).comp (toCochain z) (by omega)) (zero_add q)
        rw [Cochain.comp_units_smul]
        congr 1
        rw [← Cochain.comp_assoc _ _ _ (add_zero (-1)) (zero_add p) (by omega),
          ofHomotopy_comp_ofHom_eq ρ ρ' hH,
          Cochain.comp_assoc _ _ _ (zero_add (-1)) (show (-1 : ℤ) + p = q by omega)
            (show (0 : ℤ) + -1 + p = q by omega)] })

/-- **Precomposition carries equivariant homotopies to homotopies**: an equivariant homotopy `h`
between `g₁ g₂ : F' ⟶ F` gives the homotopy `z ↦ (-1)ᵖ h ∘ z` between `g₁^*` and `g₂^*`. -/
def opModuleHomComplexPrecompHomotopy (H : Homotopy g₁ g₂)
    (hH : ∀ (r : R) (p q : ℤ) (hpq : p + -1 = q),
      (ρ' r).asHom.f p ≫ (Cochain.ofHomotopy H).v p q hpq =
        (Cochain.ofHomotopy H).v p q hpq ≫ (ρ r).asHom.f q) :
    Homotopy (opModuleHomComplexPrecomp ρ G ρ' g₁ hg₁) (opModuleHomComplexPrecomp ρ G ρ' g₂ hg₂) :=
  (Cochain.equivHomotopy _ _).symm ⟨precompHomotopyCochain ρ G ρ' H hH, by
    refine Cochain.ext₀ _ _ fun p => ?_
    rw [Cochain.add_v, δ_v (-1) 0 (neg_add_cancel 1) _ p p (add_zero p) (p - 1) (p + 1) rfl rfl,
      Cochain.ofHom_v, Cochain.ofHom_v]
    refine ModuleCat.hom_ext <| LinearMap.ext fun z => OpCochain.ext (ρ := ρ') (G := G) ?_
    have h := δ_comp (Cochain.ofHomotopy H) (toCochain (ρ := ρ) (G := G) z)
      (show -1 + p = p - 1 by omega) 0 (p + 1) p (by omega) (neg_add_cancel 1) rfl
    rw [δ_ofHomotopy, Cochain.sub_comp] at h
    change (Cochain.ofHom g₁).comp (toCochain (ρ := ρ) (G := G) z) (zero_add p) =
      δ (p - 1) p (p.negOnePow • (Cochain.ofHomotopy H).comp
          (toCochain (ρ := ρ) (G := G) z) (by omega)) +
        (0 : ℤ).negOnePow • ((p + 1).negOnePow • (Cochain.ofHomotopy H).comp
          (δ p (p + 1) (toCochain (ρ := ρ) (G := G) z)) (by omega)) +
        (Cochain.ofHom g₂).comp (toCochain (ρ := ρ) (G := G) z) (zero_add p)
    rw [δ_units_smul, h, Int.negOnePow_zero, one_smul, smul_add, smul_smul, Int.units_mul_self,
      one_smul, Int.negOnePow_succ, Units.neg_smul]
    abel⟩

end PrecompHomotopy

section Map

variable {ℬ : Type*} [Category.{v} ℬ] [Preadditive ℬ] (Φ : 𝒜 ⥤ ℬ) [Φ.Additive]

/-- The action of `R` on `Φ F` transported along an additive functor `Φ`. -/
def mapAction : R →+* End ((Φ.mapHomologicalComplex _).obj F) where
  toFun r := .of ((Φ.mapHomologicalComplex _).map (ρ r).asHom)
  map_one' := by
    rw [map_one]; exact congrArg End.of ((Φ.mapHomologicalComplex _).map_id F)
  map_mul' r s := by
    rw [map_mul]
    exact congrArg End.of ((Φ.mapHomologicalComplex _).map_comp _ _)
  map_zero' := by
    rw [map_zero]; exact congrArg End.of ((Φ.mapHomologicalComplex _).map_zero F F)
  map_add' r s := by
    rw [map_add]; exact congrArg End.of (Φ.mapHomologicalComplex _).map_add

/-- `mapAction ρ Φ r` is the image of `ρ r` under `Φ`. -/
@[simp]
lemma mapAction_apply (r : R) :
    mapAction ρ Φ r = .of ((Φ.mapHomologicalComplex _).map (ρ r).asHom) := rfl

/-- **The map of Hom complexes induced by an additive functor** `Φ`,
`Hom^•(F, G) ⟶ Hom^•(Φ F, Φ G)`, `z ↦ Φ z`; it is `Rᵐᵒᵖ`-linear for the transported action. -/
def opModuleHomComplexMap :
    opModuleHomComplex ρ G ⟶
      opModuleHomComplex (mapAction ρ Φ) ((Φ.mapHomologicalComplex _).obj G) where
  f n := ModuleCat.ofHom
    { toFun z := of ((toCochain z).map Φ)
      map_add' z w := Cochain.map_add (toCochain z) (toCochain w) Φ
      map_smul' r z := by
        change ((Cochain.ofHom (ρ r.unop).asHom).comp (toCochain z) (zero_add n)).map Φ =
          (Cochain.ofHom ((Φ.mapHomologicalComplex _).map (ρ r.unop).asHom)).comp
            ((toCochain z).map Φ) (zero_add n)
        rw [Cochain.map_comp, Cochain.map_ofHom] }
  comm' n m _ :=
    ModuleCat.hom_ext <| LinearMap.ext fun z => δ_map n m (toCochain z) Φ

/-- In degree `n`, `opModuleHomComplexMap ρ G Φ` sends a cochain `z` to its image under `Φ`. -/
@[simp]
lemma opModuleHomComplexMap_f_apply (n : ℤ) (z : OpCochain ρ G n) :
    toCochain (ρ := mapAction ρ Φ) (G := (Φ.mapHomologicalComplex _).obj G)
      (((opModuleHomComplexMap ρ G Φ).f n).hom z) = (toCochain z).map Φ := rfl

/-- The functor map commutes with postcomposition. -/
lemma opModuleHomComplexMap_postcomp {G' : CochainComplex 𝒜 ℤ} (h : G ⟶ G') :
    opModuleHomComplexMap ρ G Φ ≫
        opModuleHomComplexPostcomp (mapAction ρ Φ) ((Φ.mapHomologicalComplex _).map h) =
      opModuleHomComplexPostcomp ρ h ≫ opModuleHomComplexMap ρ G' Φ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext <| LinearMap.ext fun z => ?_
  change ((toCochain (ρ := ρ) (G := G) z).map Φ).comp
      (Cochain.ofHom ((Φ.mapHomologicalComplex _).map h)) (add_zero n) =
    ((toCochain (ρ := ρ) (G := G) z).comp (Cochain.ofHom h) (add_zero n)).map Φ
  rw [Cochain.map_comp, Cochain.map_ofHom]

end Map

end Stacks.HomComplex
