module

public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSections.ModuleSystem
public import StacksFrontier.CategoryTheory.Equivalence.Pow

/-!
# Shifting the graded module of twisted sections

Stacks Tag 01QK is a remark in the situation of Stacks Tag 01QH: `X` is a scheme, `𝓛` an ample
invertible `𝒪_X`-module, `S = Γ_*(X, 𝓛)` the graded section ring, `Y = Proj S`, and
`f : X ⟶ Y` the canonical morphism (Stacks Tag 01PZ). For a quasi-coherent `𝓕` with
`M = Γ_*(X, 𝓛, 𝓕)`, Stacks Tag 01QJ provides a map `θ_𝓕 : f^* M~ ⟶ 𝓕`, and the remark asserts
that the square

  `f^* M~ ⊗ f^* 𝒪_Y(n) ⟶ f^* (M(n)~)`,   verticals `θ_𝓕 ⊗ θ_{𝓛^{⊗ n}}` and `θ_{𝓕 ⊗ 𝓛^{⊗ n}}`,

whose bottom edge is the identity of `𝓕 ⊗ 𝓛^{⊗ n}`, commutes — "using the obvious
identification `M(n) = Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n})`".

This file proves that identification, at the level of an arbitrary monoidal category, for the
graded module of sections of the integer iterates of an autoequivalence, which is the shape
`Γ_*(X, 𝓛, 𝓕)` is built in by `Stacks.SheafOfModules.Invertible.twistedSections`. Neither
assertion of Stacks Tag 01QK is proved here: not the square, and not the first assertion, that
the isomorphism `f^* 𝒪_Y(n) → 𝓛^{⊗ n}` of Stacks Tag 01QI is `θ_{𝓛^{⊗ n}}`. So no
`@[stacks 01QK]` attribute is carried in this file.

The degree-`i` piece of `Γ_*(𝓕 ⊗ 𝓛^{⊗ n})` is `Γ(X, (𝓕 ⊗ 𝓛^{⊗ n}) ⊗ 𝓛^{⊗ i})` while the degree-`i`
piece of `M(n)` is `Γ(X, 𝓕 ⊗ 𝓛^{⊗ (n + i)})`; the two differ by the addition law for the
integer powers of "tensor by `𝓛`", which is `CategoryTheory.Equivalence.powAdd`. That is the
transport, and `Stacks.Monoidal.ModuleSystem.powShiftEquiv` is where it is isolated.

## Main definitions

* `Stacks.Monoidal.ModuleSystem.shift`: **`M(n)`**, the shift of a module system by an integer.
* `Stacks.Monoidal.ModuleSystem.SystemEquiv`: a comparison of module systems over one power
  system — a degreewise isomorphism commuting with the successor comparisons.
* `Stacks.Monoidal.ModuleSystem.powModuleSystem`: the module system `i ↦ (e ^ i).obj F` of the
  integer iterates of an autoequivalence `e`, for a natural comparison `κ : S.gen ⊗ - ≅ e`.
  This is the shape of `Γ_*(X, 𝓛, 𝓕)`.
* `Stacks.Monoidal.ModuleSystem.powShiftEquiv`: **the identification**, as a comparison of
  module systems `powModuleSystem ((e ^ n).obj F) ≅ (powModuleSystem F).shift n`.

## Main results

* `Stacks.Monoidal.ModuleSystem.SystemEquiv.actIso_comm`: **a comparison of module systems
  respects the action isomorphisms**, in every degree. This is the whole content of
  `SystemEquiv`, and it is what makes a degreewise isomorphism an isomorphism of graded
  modules rather than merely of graded abelian groups.
* `Stacks.Monoidal.ModuleSystem.SystemEquiv.sectionsAddEquiv_sectionSMul`: the degreewise
  additive isomorphism on global sections carries the action of a homogeneous section of the
  section ring to the action of the same section.
* `Stacks.Monoidal.ModuleSystem.powAdd_powSucc_comm`: the commutation of the addition law with
  the successor comparison in the right exponent — the cocycle identity
  `CategoryTheory.Equivalence.powAdd_assoc` at right exponent one, read at an object. This is
  the computational heart of `powShiftEquiv`.
* `Stacks.Monoidal.ModuleSystem.powShiftEquiv_sectionSMul`: **the identification is an
  isomorphism of graded modules over the section ring**, which is the form the remark uses it
  in.

## Implementation notes

`Γ_*(X, 𝓛, 𝓕)` is the global sections of a `Stacks.Monoidal.ModuleSystem` over a
`Stacks.Monoidal.PowerSystem`: a family `obj : ℤ → C` with comparisons
`S.gen ⊗ obj i ≅ obj (i + 1)`, whose graded-module structure over the section ring is
`Stacks.Monoidal.ModuleSystem.gmodule`. In a `SystemEquiv`, the field `comm` is what makes the
degreewise isomorphism respect the action of `Γ_*(X, 𝓛)`.

**The shift's reindexing.** `M.succIso (n + i)` lands in `M.obj (n + i + 1)` whereas
`(M.shift n).succIso i` must land in `M.obj (n + (i + 1))`. Addition on `ℤ` is not
associative definitionally, so one `eqToIso` is unavoidable; it is placed in `shift` itself.
The matching transport on the `powAdd` side is supplied by `powAdd_cast_hom`, and the two cancel
inside `powAdd_powSucc_comm`, so the final statement carries no `eqToHom`.

**The degree bookkeeping needs no transport.** `Stacks.Monoidal.natShift` recurses on the
natural number, so `(0 : ℕ) +ᵥ b` is `b` and `(a + 1) +ᵥ b` is `a +ᵥ (b + 1)`, both
definitionally. `actIso_comm` is therefore a plain induction on the power-system degree, with no
`eqToHom`, following the recursion that defines `actIso`.

**Coherence is isolated from the degrees**, in `actIso_comm_aux_zero` and
`actIso_comm_aux_succ`, as `ModuleSystem.actIso_assoc` isolates its own coherence into
`actIso_assoc_aux_zero` and `actIso_assoc_aux_succ`. Each aux lemma mentions only abstract
objects and morphisms.

**`rw` and the monoidal instance.** `actIso_comm_aux_zero` is a `calc` of `congrArg`s, not a
`rw` chain: `rw` fails to match `CategoryTheory.MonoidalCategory.leftUnitor_naturality`
against the goal, because `rw` matches only up to instance transparency and the monoidal
structure reaches the goal by a different path from the one `rw` elaborates the class field
with. `congrArg` compares the two sides up to full unfolding and is unaffected.

## References

* [Stacks Project, Tag 01QK](https://stacks.math.columbia.edu/tag/01QK)
* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
* [Stacks Project, Tag 01QI](https://stacks.math.columbia.edu/tag/01QI)
* [Stacks Project, Tag 01QH](https://stacks.math.columbia.edu/tag/01QH)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 01MQ](https://stacks.math.columbia.edu/tag/01MQ)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped DirectSum

universe v u

namespace Stacks.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-! ### Coherence for the compatibility of a comparison with the action isomorphisms -/

/-- The degree-zero case of the compatibility of the action isomorphisms with a comparison of
module systems, isolated from the degrees: only `whisker_exchange` and the naturality of the
left unitor are used. -/
theorem actIso_comm_aux_zero {Sa Mb Nb : C} (e : Sa ≅ 𝟙_ C) (f : Mb ⟶ Nb) :
    (Sa ◁ f) ≫ ((e.hom ▷ Nb) ≫ (λ_ Nb).hom) = ((e.hom ▷ Mb) ≫ (λ_ Mb).hom) ≫ f :=
  calc (Sa ◁ f) ≫ ((e.hom ▷ Nb) ≫ (λ_ Nb).hom)
      = ((Sa ◁ f) ≫ (e.hom ▷ Nb)) ≫ (λ_ Nb).hom := (Category.assoc _ _ _).symm
    _ = ((e.hom ▷ Mb) ≫ (𝟙_ C ◁ f)) ≫ (λ_ Nb).hom :=
        congrArg (· ≫ (λ_ Nb).hom) (whisker_exchange e.hom f)
    _ = (e.hom ▷ Mb) ≫ ((𝟙_ C ◁ f) ≫ (λ_ Nb).hom) := Category.assoc _ _ _
    _ = (e.hom ▷ Mb) ≫ ((λ_ Mb).hom ≫ f) :=
        congrArg (e.hom ▷ Mb ≫ ·) (MonoidalCategory.leftUnitor_naturality f)
    _ = ((e.hom ▷ Mb) ≫ (λ_ Mb).hom) ≫ f := (Category.assoc _ _ _).symm

/-- The inductive step of the compatibility of the action isomorphisms with a comparison of
module systems, isolated from the degrees: only `whisker_exchange`, the naturality of the
associator in its last variable, and the functoriality of whiskering are used. -/
theorem actIso_comm_aux_succ {Sa Sa1 G Mb Nb Mb1 Nb1 Mv Nv : C}
    (σ : Sa ⊗ G ≅ Sa1) (τM : G ⊗ Mb ≅ Mb1) (τN : G ⊗ Nb ≅ Nb1)
    (f : Mb ⟶ Nb) (f1 : Mb1 ⟶ Nb1) (w : Mv ⟶ Nv)
    (aM : Sa ⊗ Mb1 ⟶ Mv) (aN : Sa ⊗ Nb1 ⟶ Nv)
    (hcomm : (G ◁ f) ≫ τN.hom = τM.hom ≫ f1)
    (ih : (Sa ◁ f1) ≫ aN = aM ≫ w) :
    (Sa1 ◁ f) ≫ ((σ.inv ▷ Nb) ≫ (α_ Sa G Nb).hom ≫ (Sa ◁ τN.hom) ≫ aN)
      = ((σ.inv ▷ Mb) ≫ (α_ Sa G Mb).hom ≫ (Sa ◁ τM.hom) ≫ aM) ≫ w := by
  rw [← Category.assoc, whisker_exchange, Category.assoc,
    associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, hcomm,
    whiskerLeft_comp_assoc, ih]
  simp only [Category.assoc]

/-- The cancellation that turns the commuting square of a comparison of module systems into a
statement about the successor comparisons alone: the comparison `κ` is stripped off both sides
by its own naturality. -/
theorem succIso_comm_of_pow_comm {G Za Zb Wa Wb T T' T'' : C}
    (κa : G ⊗ Za ≅ Wa) (κb : G ⊗ Zb ≅ Wb) (φ : Za ⟶ Zb) (ψ : Wa ⟶ Wb)
    (pa : Wa ⟶ T) (pb : Wb ⟶ T') (q : T' ⟶ T'') (r : T ⟶ T'')
    (hκ : (G ◁ φ) ≫ κb.hom = κa.hom ≫ ψ) (hstar : ψ ≫ (pb ≫ q) = pa ≫ r) :
    (G ◁ φ) ≫ ((κb.hom ≫ pb) ≫ q) = (κa.hom ≫ pa) ≫ r :=
  calc (G ◁ φ) ≫ ((κb.hom ≫ pb) ≫ q)
      = ((G ◁ φ) ≫ κb.hom) ≫ (pb ≫ q) := by simp only [Category.assoc]
    _ = (κa.hom ≫ ψ) ≫ (pb ≫ q) := congrArg (· ≫ (pb ≫ q)) hκ
    _ = κa.hom ≫ (ψ ≫ (pb ≫ q)) := Category.assoc _ _ _
    _ = κa.hom ≫ (pa ≫ r) := congrArg (κa.hom ≫ ·) hstar
    _ = (κa.hom ≫ pa) ≫ r := (Category.assoc _ _ _).symm

namespace ModuleSystem

variable {S : PowerSystem C}

/-! ### The shift of a module system -/

/-- **The shift `M(n)` of a module system.** Its degree-`i` object is the degree-`n + i` object
of `M`, and its successor comparison is that of `M`, reindexed by the associativity of addition
on `ℤ`: `M.succIso (n + i)` lands in `M.obj (n + i + 1)`, and the shift wants
`M.obj (n + (i + 1))`. -/
noncomputable def shift (M : ModuleSystem S) (n : ℤ) : ModuleSystem S where
  obj i := M.obj (n + i)
  succIso i := M.succIso (n + i) ≪≫ eqToIso (congrArg M.obj (add_assoc n i 1))

/-- The degree-`i` object of `M(n)` is the degree-`n + i` object of `M`. -/
@[simp]
theorem shift_obj (M : ModuleSystem S) (n i : ℤ) : (M.shift n).obj i = M.obj (n + i) := rfl

/-- The successor comparison of `M(n)` is that of `M`, reindexed by the associativity of
addition. -/
theorem shift_succIso (M : ModuleSystem S) (n i : ℤ) :
    (M.shift n).succIso i
      = M.succIso (n + i) ≪≫ eqToIso (congrArg M.obj (add_assoc n i 1)) := rfl

/-! ### Comparisons of module systems -/

/-- **A comparison of module systems over one power system**: a degreewise isomorphism which
commutes with the successor comparisons. This is the data that makes two module systems have
the *same* graded module of global sections, action included; without the commutation `comm`
the degreewise isomorphism says nothing about the action of the section ring. -/
structure SystemEquiv (M N : ModuleSystem S) where
  /-- The degreewise isomorphism. -/
  app : ∀ i : ℤ, M.obj i ≅ N.obj i
  /-- The degreewise isomorphism commutes with the successor comparisons. -/
  comm : ∀ i : ℤ,
    (S.gen ◁ (app i).hom) ≫ (N.succIso i).hom = (M.succIso i).hom ≫ (app (i + 1)).hom

namespace SystemEquiv

variable {M N : ModuleSystem S}

/-- The identity comparison. -/
noncomputable def refl (M : ModuleSystem S) : SystemEquiv M M where
  app _ := Iso.refl _
  comm _ := by simp

/-- **The comparison is compatible with the action isomorphisms**, in every degree `a` of the
power system and every degree `b` of the module system. This is the whole content of
`SystemEquiv`: it is proved by induction on `a`, exactly as `actIso` is defined, with the
degree-zero case the naturality of the left unitor and the inductive step
`Stacks.Monoidal.actIso_comm_aux_succ`.

No index transport appears: `(0 : ℕ) +ᵥ b` is `b` and `(a + 1) +ᵥ b` is `a +ᵥ (b + 1)`, both
definitionally, because `Stacks.Monoidal.natShift` recurses on the natural number. -/
theorem actIso_comm (φ : SystemEquiv M N) : ∀ (a : ℕ) (b : ℤ),
    (S.obj a ◁ (φ.app b).hom) ≫ (N.actIso a b).hom
      = (M.actIso a b).hom ≫ (φ.app (a +ᵥ b)).hom
  | 0, b => by
      simp only [actIso_zero, Iso.trans_hom, whiskerRightIso_hom]
      exact actIso_comm_aux_zero S.objZeroIso (φ.app b).hom
  | a + 1, b => by
      simp only [actIso_succ, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
        whiskerRightIso_hom]
      exact actIso_comm_aux_succ (S.succIso a) (M.succIso b) (N.succIso b)
        (φ.app b).hom (φ.app (b + 1)).hom (φ.app (a +ᵥ (b + 1))).hom
        (M.actIso a (b + 1)).hom (N.actIso a (b + 1)).hom (φ.comm b)
        (φ.actIso_comm a (b + 1))

/-- **The comparison is compatible with the action of global sections.** Transporting a global
section of `M.obj b` along the comparison and then acting by `s` is acting by `s` and then
transporting. -/
theorem sectionSMul_comm (φ : SystemEquiv M N) {a : ℕ} {b : ℤ}
    (s : 𝟙_ C ⟶ S.obj a) (t : 𝟙_ C ⟶ M.obj b) :
    N.sectionSMul s (t ≫ (φ.app b).hom)
      = M.sectionSMul s t ≫ (φ.app (a +ᵥ b)).hom := by
  rw [ModuleSystem.sectionSMul, ModuleSystem.sectionSMul,
    ← sectionTensor_comp_whiskerLeft, Category.assoc, φ.actIso_comm a b, ← Category.assoc]

section Preadditive

variable [Preadditive C]

/-- The comparison, read on global sections in a single degree, as an isomorphism of additive
groups. -/
@[simps]
noncomputable def sectionsAddEquiv (φ : SystemEquiv M N) (i : ℤ) :
    (𝟙_ C ⟶ M.obj i) ≃+ (𝟙_ C ⟶ N.obj i) where
  toFun t := t ≫ (φ.app i).hom
  invFun u := u ≫ (φ.app i).inv
  left_inv t := by simp
  right_inv u := by simp
  map_add' t t' := Preadditive.add_comp _ _ _ _ _ _

/-- **A comparison of module systems is an isomorphism of graded modules over the section
ring**: the degreewise additive isomorphism `sectionsAddEquiv` carries the action of a global
section of `S.obj a` to the action of the same section. -/
theorem sectionsAddEquiv_sectionSMul (φ : SystemEquiv M N) {a : ℕ} {b : ℤ}
    (s : 𝟙_ C ⟶ S.obj a) (t : 𝟙_ C ⟶ M.obj b) :
    φ.sectionsAddEquiv (a +ᵥ b) (M.sectionSMul s t)
      = N.sectionSMul s (φ.sectionsAddEquiv b t) :=
  (φ.sectionSMul_comm s t).symm

end Preadditive

end SystemEquiv

/-! ### The module system of the iterates of an autoequivalence, and its shift -/

omit [MonoidalCategory C] in
/-- The addition law at a target exponent presented by an equation is the addition law at the
literal sum, reindexed along that equation. -/
theorem powAdd_cast_hom (e : C ≌ C) (n m p : ℤ) (h : n + m = p) (M : C) :
    (CategoryTheory.Equivalence.powAdd e n m p h).hom.app M =
      (CategoryTheory.Equivalence.powAdd e n m (n + m) rfl).hom.app M ≫
        eqToHom (congrArg (fun q => (e ^ q).functor.obj M) h) := by
  subst h
  simp

omit [MonoidalCategory C] in
/-- **The addition law commutes with the successor comparison in the right exponent.** This is
the cocycle identity `CategoryTheory.Equivalence.powAdd_assoc` at right exponent one, read at
an object, with the two reindexing transports cancelled against each other — which is why no
`eqToHom` survives on the right-hand side: iterating `e` first `n` times and then `i + 1`
times, versus `n + i` times and then once, are the same up to the addition law. -/
theorem powAdd_powSucc_comm (e : C ≌ C) (F : C) (n i : ℤ) :
    e.functor.map ((CategoryTheory.Equivalence.powAdd e n i (n + i) rfl).hom.app F)
        ≫ ((CategoryTheory.Equivalence.powSucc e (n + i) (n + i + 1) rfl).hom.app F
            ≫ eqToHom (congrArg (fun q => (e ^ q).functor.obj F) (add_assoc n i 1)))
      = (CategoryTheory.Equivalence.powSucc e i (i + 1) rfl).hom.app ((e ^ n).functor.obj F)
          ≫ (CategoryTheory.Equivalence.powAdd e n (i + 1) (n + (i + 1)) rfl).hom.app F := by
  have hsum : n + (i + 1) = n + i + 1 := by omega
  have key := NatTrans.congr_app (congrArg Iso.hom
    (CategoryTheory.Equivalence.powAdd_assoc e n i 1 (n + i) (i + 1) (n + i + 1)
      rfl rfl rfl)) F
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj] at key
  have key' : e.functor.map ((CategoryTheory.Equivalence.powAdd e n i (n + i) rfl).hom.app F)
        ≫ (CategoryTheory.Equivalence.powSucc e (n + i) (n + i + 1) rfl).hom.app F
      = (CategoryTheory.Equivalence.powSucc e i (i + 1) rfl).hom.app ((e ^ n).functor.obj F)
        ≫ (CategoryTheory.Equivalence.powAdd e n (i + 1) (n + i + 1) hsum).hom.app F := key
  rw [← Category.assoc, key', powAdd_cast_hom e n (i + 1) (n + i + 1) hsum F]
  simp

section Pow

variable (S)

/-- **The module system of the integer iterates of an autoequivalence.** For `e` an
autoequivalence of `C` and `κ` a comparison identifying `S.gen ⊗ -` with `e`, the family
`i ↦ (e ^ i).obj F` is a module system over `S`: its successor comparison is `κ` followed by
the successor comparison of the iterates.

This is the shape of `Γ_*(X, 𝓛, 𝓕)`: there `e` is "tensor by `𝓛`", `κ` is the braiding
followed by the identification of the monoidal tensor product with the tensor product sheaf,
and `(e ^ i).obj 𝓕` is `𝓕 ⊗ 𝓛^{⊗ i}`. -/
noncomputable def powModuleSystem (e : C ≌ C) (κ : ∀ Z : C, S.gen ⊗ Z ≅ e.functor.obj Z)
    (F : C) : ModuleSystem S where
  obj i := (e ^ i).functor.obj F
  succIso i := κ _ ≪≫ (CategoryTheory.Equivalence.powSucc e i (i + 1) rfl).app F

/-- The degree-`i` object of `powModuleSystem S e κ F` is `(e ^ i).obj F`. -/
@[simp]
theorem powModuleSystem_obj (e : C ≌ C) (κ : ∀ Z : C, S.gen ⊗ Z ≅ e.functor.obj Z) (F : C)
    (i : ℤ) : (powModuleSystem S e κ F).obj i = (e ^ i).functor.obj F := rfl

/-- The successor comparison of `powModuleSystem S e κ F` is `κ` followed by the successor
comparison of the iterates of `e`. -/
theorem powModuleSystem_succIso (e : C ≌ C) (κ : ∀ Z : C, S.gen ⊗ Z ≅ e.functor.obj Z) (F : C)
    (i : ℤ) : (powModuleSystem S e κ F).succIso i
      = κ _ ≪≫ (CategoryTheory.Equivalence.powSucc e i (i + 1) rfl).app F := rfl

/-- **The identification `Γ_*(F ⊗ g^{⊗ n}) = Γ_*(F)(n)`, as a comparison of module systems.**

This is the "obvious identification `M(n) = Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n})`" that Stacks Tag 01QK's
square is stated modulo, proved at the level of an arbitrary monoidal category. It is *not* a
definitional coincidence: the degree-`i` object on the left is `(e ^ i).obj ((e ^ n).obj F)`
and on the right it is `(e ^ (n + i)).obj F`, and the transport between them is the addition
law `CategoryTheory.Equivalence.powAdd`. The commutation with the successor comparisons — the
field that makes this an identification of graded *modules* and not merely of graded abelian
groups — is `powAdd_powSucc_comm`, after `κ` is stripped off both sides by its own
naturality. -/
noncomputable def powShiftEquiv (e : C ≌ C) (κ : ∀ Z : C, S.gen ⊗ Z ≅ e.functor.obj Z)
    (hκ : ∀ ⦃Z Z' : C⦄ (f : Z ⟶ Z'),
      (S.gen ◁ f) ≫ (κ Z').hom = (κ Z).hom ≫ e.functor.map f)
    (F : C) (n : ℤ) :
    SystemEquiv (powModuleSystem S e κ ((e ^ n).functor.obj F))
      ((powModuleSystem S e κ F).shift n) where
  app i := (CategoryTheory.Equivalence.powAdd e n i (n + i) rfl).app F
  comm i :=
    succIso_comm_of_pow_comm (κ ((e ^ i).functor.obj ((e ^ n).functor.obj F)))
      (κ ((e ^ (n + i)).functor.obj F))
      ((CategoryTheory.Equivalence.powAdd e n i (n + i) rfl).hom.app F)
      (e.functor.map ((CategoryTheory.Equivalence.powAdd e n i (n + i) rfl).hom.app F))
      ((CategoryTheory.Equivalence.powSucc e i (i + 1) rfl).hom.app ((e ^ n).functor.obj F))
      ((CategoryTheory.Equivalence.powSucc e (n + i) (n + i + 1) rfl).hom.app F)
      (eqToHom (congrArg (fun q => (e ^ q).functor.obj F) (add_assoc n i 1)))
      ((CategoryTheory.Equivalence.powAdd e n (i + 1) (n + (i + 1)) rfl).hom.app F)
      (hκ _) (powAdd_powSucc_comm e F n i)

/-- **The identification of Stacks Tag 01QK is an isomorphism of graded modules over the
section ring.** In degree `i` it is the additive isomorphism

  `Γ(𝟙_ C, (e ^ i).obj ((e ^ n).obj F)) ≃+ Γ(𝟙_ C, (e ^ (n + i)).obj F)`,

i.e. `Γ_*(F ⊗ g^{⊗ n})_i ≃+ Γ_*(F)_{n + i} = (Γ_*(F)(n))_i`, and it carries the action of a
homogeneous global section of the section ring to the action of the same section. -/
theorem powShiftEquiv_sectionSMul [Preadditive C] (e : C ≌ C)
    (κ : ∀ Z : C, S.gen ⊗ Z ≅ e.functor.obj Z)
    (hκ : ∀ ⦃Z Z' : C⦄ (f : Z ⟶ Z'),
      (S.gen ◁ f) ≫ (κ Z').hom = (κ Z).hom ≫ e.functor.map f)
    (F : C) (n : ℤ) {a : ℕ} {b : ℤ} (s : 𝟙_ C ⟶ S.obj a)
    (t : 𝟙_ C ⟶ (e ^ b).functor.obj ((e ^ n).functor.obj F)) :
    (powShiftEquiv S e κ hκ F n).sectionsAddEquiv (a +ᵥ b)
        ((powModuleSystem S e κ ((e ^ n).functor.obj F)).sectionSMul s t)
      = ((powModuleSystem S e κ F).shift n).sectionSMul s
          ((powShiftEquiv S e κ hκ F n).sectionsAddEquiv b t) :=
  (powShiftEquiv S e κ hκ F n).sectionsAddEquiv_sectionSMul s t

end Pow

end ModuleSystem

end Stacks.Monoidal

end
