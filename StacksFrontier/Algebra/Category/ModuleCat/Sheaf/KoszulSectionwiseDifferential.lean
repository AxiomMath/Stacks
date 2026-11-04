module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.RingTheory.Koszul.Semilinear

/-!
# The Koszul differential of the sectionwise exterior algebra of a presheaf of modules

Let `O` be a presheaf of commutative rings on a category `C`, let `F` be a presheaf of
`O`-modules and let `θ` be a *sectionwise functional* on `F`: an `O(X)`-linear map
`F(X) ⟶ O(X)` for every object `X`, compatible with restriction. This file equips the
`ℤ`-graded sectionwise exterior algebra
`Stacks.GradedAlgebra.extendFamily (fun n ↦ PresheafOfModules.extPow n F)` — the graded algebra
whose sheafification is the exterior algebra of `SheafOfModules.algebras` — with the Koszul
differential of `θ`, and proves the three identities a Koszul complex is made of: the graded
Leibniz rule, the value on a degree-one generator, and square-zeroness.

Nothing here is a hypothesis: over a presheaf the sections of `extPow n F` are the honest
exterior power `⋀ⁿ_{O(X)}(F(X))`, so the differential *is* `Koszul.contraction` and each identity
*is* the corresponding statement about `CliffordAlgebra.contractLeft`. The whole content of the
file is therefore bookkeeping: the degree transports of a `ℤ`-grading obtained by extending an
`ℕ`-grading by zero, and the two spellings of a section of `extPow`.

## Main definitions

* `PresheafOfModules.SectionwiseDual`: a functional on a presheaf of modules, sectionwise.
* `PresheafOfModules.extPowKoszulD`: the Koszul differential `⋀^{n+1} F ⟶ ⋀ⁿ F` of a sectionwise
  functional, as a morphism of presheaves of modules. Its naturality is
  `Koszul.mapₛₗ_contraction`.
* `PresheafOfModules.extKoszulD`: the same differential read on the `ℤ`-extended family, so that
  it lowers degree by one in every integer degree.
* `PresheafOfModules.extCoe`: **the uniform coercion**, sending a section of the degree-`n` piece
  of the `ℤ`-extended family to an element of `ExteriorAlgebra (O X) (F X)` — the subtype
  coercion in a nonnegative degree and the zero map in a negative one.

## Main results

* `PresheafOfModules.extCoe_injective`, `extCoe_add`, `extCoe_zsmul`, `extCoe_degCast`,
  `extCoe_mul` and `extCoe_extKoszulD`: the six properties of the uniform coercion. Together they
  reduce every identity about the `ℤ`-graded sectionwise algebra to an identity in
  `ExteriorAlgebra (O X) (F X)`, where no degree appears.
* `PresheafOfModules.extKoszulD_mul`: **the graded Leibniz rule**, in exactly the shape
  `Stacks.RegularSequence.KoszulChainData` asks for.
* `PresheafOfModules.extKoszulD_extPowGen`: the value of the differential on a degree-one
  generator is the functional times the unit.
* `PresheafOfModules.extKoszulD_comp`: the differential squares to zero.

## Implementation notes

What is forced and what is chosen.

* **The uniform coercion is the whole technique.** `Stacks.GradedAlgebra.extendFamily` is defined
  by a match on the *constructors* of `ℤ`, so a statement in degree `n : ℤ` cannot be proved
  without case-splitting on `n`; and the degree transports `Stacks.degCast` of a graded Leibniz
  rule live in a family indexed by `ℤ`. Mapping everything into the single ungraded type
  `ExteriorAlgebra (O X) (F X)`, where the six lemmas above say that the coercion is injective and
  commutes with every operation in sight, makes the Leibniz rule one application of
  `Koszul.contraction_mul_of_mem` and confines the case analysis to those six lemmas, each of
  which is two or three lines.
* `extPowKoszulDApp` interposes a declaration whose expected type is already spelled at
  `(extPow n F).obj X` rather than at `⋀ⁿ`, for the reason recorded in the section docstring of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseAlgebras`: `ExteriorAlgebra` is a
  Clifford quotient, and the `whnf` a structure-instance elaborator performs on a field does not
  terminate inside the heartbeat limit if the comparison is left to it.
* In degree zero the differential is the zero morphism, and that is not a choice: its target is
  the degree `-1` piece of the extended family, which has no nonzero sections. The uniform
  coercion lemma `extCoe_extKoszulD` holds there all the same, because contraction annihilates
  exterior degree zero (`Koszul.contraction_eq_zero_of_mem_zero`).
* No `@[stacks]` attribute. Stacks Tag 062K asserts the existence and uniqueness of the Koszul
  differential on the exterior algebra of a *sheaf* of modules; this file constructs it on a
  presheaf, which is the input to the sheafification, not the tag's statement.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0622](https://stacks.math.columbia.edu/tag/0622)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped ExteriorAlgebra

universe v u w a

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- **A functional on a presheaf of modules, sectionwise**: an `O(X)`-linear map `F(X) ⟶ O(X)`
for every object `X` of the site, compatible with restriction.

This is the input of the Koszul differential. It is not a morphism into a unit presheaf of
modules: the Koszul complex of Stacks Tag 062K is attached to a morphism `F ⟶ O♯` of sheaves of
modules, and the data that survives on the underlying presheaves, after restriction of scalars,
is exactly this. -/
structure SectionwiseDual (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) where
  /-- The functional over an object of the site. -/
  app (X : Cᵒᵖ) : Module.Dual ((O ⋙ forget₂ CommRingCat RingCat).obj X) (F.obj X)
  /-- Compatibility with restriction: the functional of the smaller object computes the
  restriction of the scalar. -/
  naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : F.obj X) :
    ((O ⋙ forget₂ CommRingCat RingCat).map f).hom (app X m) = app Y (F.restrictₛₗ f m)

namespace SectionwiseDual

variable {F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}

/-! ### The differential in nonnegative degrees -/

/-- The Koszul differential of a sectionwise functional over an object of the site, retyped at the
sections of `extPow`. -/
noncomputable def extPowKoszulDApp (θ : SectionwiseDual.{v, u, w, a} F) (n : ℕ) (X : Cᵒᵖ) :
    (extPow (n + 1) F).obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] (extPow n F).obj X :=
  Koszul.d (θ.app X) n

/-- Read in the exterior algebra, `extPowKoszulDApp` is contraction with the functional. -/
theorem extPowKoszulDApp_coe (θ : SectionwiseDual.{v, u, w, a} F) (n : ℕ) (X : Cᵒᵖ)
    (x : (extPow (n + 1) F).obj X) :
    ((extPowSections n F X (θ.extPowKoszulDApp n X x) :
          ⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (F.obj X)) :
        ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) =
      Koszul.contraction (θ.app X)
        ((extPowSections (n + 1) F X x : ⋀[(O ⋙ forget₂ _ RingCat).obj X]^(n + 1) (F.obj X)) :
          ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) := rfl

/-- **The Koszul differential of a sectionwise functional**, as a morphism of presheaves of
modules `⋀^{n+1} F ⟶ ⋀ⁿ F`. Its naturality is `Koszul.mapₛₗ_contraction`: the restriction maps of
`extPow` are the semilinear base changes `ExteriorAlgebra.mapₛₗ` of the restriction maps of `F`,
and the compatibility of the functionals those need is the `naturality` field. -/
noncomputable def extPowKoszulD (θ : SectionwiseDual.{v, u, w, a} F) (n : ℕ) :
    extPow (n + 1) F ⟶ extPow n F where
  app X := ModuleCat.ofHom (θ.extPowKoszulDApp n X)
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext
    (Koszul.mapₛₗ_contraction _ _ _ _ (fun m => θ.naturality f m) _).symm)

/-- The component of `extPowKoszulD` over an object `X` is `extPowKoszulDApp`. -/
theorem extPowKoszulD_app (θ : SectionwiseDual.{v, u, w, a} F) (n : ℕ) (X : Cᵒᵖ)
    (x : (extPow (n + 1) F).obj X) :
    PresheafOfModules.Hom.app (θ.extPowKoszulD n) X x = θ.extPowKoszulDApp n X x := rfl

/-! ### The differential on the `ℤ`-extended family -/

/-- The `ℤ`-indexed family of sectionwise exterior powers: the exterior powers in nonnegative
degrees and the zero presheaf in negative ones. This is the family whose sheafification is the
exterior algebra of `SheafOfModules.algebras`. -/
noncomputable abbrev extPowFamily (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) :
    ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat) :=
  Stacks.GradedAlgebra.extendFamily fun n : ℕ => extPow n F

/-- **The Koszul differential on the `ℤ`-extended family.** In degree `n + 1` it is
`PresheafOfModules.SectionwiseDual.extPowKoszulD`, transported along
`((n + 1 : ℕ) : ℤ) - 1 = ((n : ℕ) : ℤ)`; in degree zero and in negative degrees it is the zero
morphism, which is forced, the target having no nonzero sections. -/
noncomputable def extKoszulD (θ : SectionwiseDual.{v, u, w, a} F) :
    (n : ℤ) → (extPowFamily F n ⟶ extPowFamily F (n - 1))
  | Int.ofNat 0 => 0
  | Int.ofNat (m + 1) =>
      θ.extPowKoszulD m ≫
        eqToHom (congrArg (extPowFamily F)
          (show ((m : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) - 1 by omega))
  | Int.negSucc _ => 0

/-! ### The uniform coercion -/

/-- **The uniform coercion.** A section of the degree-`n` piece of the `ℤ`-extended family of
sectionwise exterior powers, read as an element of `ExteriorAlgebra (O X) (F X)`: the subtype
coercion in a nonnegative degree, and the zero map in a negative one, where there are no nonzero
sections anyway. -/
noncomputable def extCoe (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) :
    (n : ℤ) → (X : Cᵒᵖ) → (extPowFamily F n).obj X →
      ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)
  | Int.ofNat k, X => fun x =>
      ((extPowSections k F X x : ⋀[(O ⋙ forget₂ _ RingCat).obj X]^k (F.obj X)) :
        ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X))
  | Int.negSucc _, _ => fun _ => 0

/-- In a nonnegative degree the uniform coercion is the coercion of the exterior power. -/
theorem extCoe_natCast (k : ℕ) (X : Cᵒᵖ) (x : (extPow k F).obj X) :
    extCoe F (k : ℤ) X x =
      ((extPowSections k F X x : ⋀[(O ⋙ forget₂ _ RingCat).obj X]^k (F.obj X)) :
        ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) := rfl

/-- The uniform coercion of a section of a nonnegative degree lands in that exterior power. -/
theorem extCoe_mem (k : ℕ) (X : Cᵒᵖ) (x : (extPowFamily F ((k : ℕ) : ℤ)).obj X) :
    extCoe F ((k : ℕ) : ℤ) X x ∈ ⋀[(O ⋙ forget₂ _ RingCat).obj X]^k (F.obj X) :=
  Subtype.property (extPowSections k F X x)

/-- The uniform coercion vanishes in a negative degree. -/
private theorem extCoe_eq_zero_of_neg {n : ℤ} (hn : n < 0) (X : Cᵒᵖ)
    (x : (extPowFamily F n).obj X) : extCoe F n X x = 0 := by
  cases n with
  | ofNat k => exact absurd hn (Int.not_lt.2 (Int.natCast_nonneg k))
  | negSucc k => rfl

/-- **The uniform coercion is injective.** In a nonnegative degree it is the coercion of a
submodule; in a negative one the source has only the zero section. -/
theorem extCoe_injective (n : ℤ) (X : Cᵒᵖ) : Function.Injective (extCoe F n X) := by
  match n with
  | Int.ofNat k => exact fun x y h => Subtype.ext h
  | Int.negSucc k =>
    exact fun x y _ => by
      rw [Stacks.GradedAlgebra.extendFamily_section_eq_zero (by omega : (Int.negSucc k) < 0) X x,
        Stacks.GradedAlgebra.extendFamily_section_eq_zero (by omega : (Int.negSucc k) < 0) X y]

/-- The uniform coercion is additive. -/
theorem extCoe_add (n : ℤ) (X : Cᵒᵖ) (x y : (extPowFamily F n).obj X) :
    extCoe F n X (x + y) = extCoe F n X x + extCoe F n X y := by
  match n with
  | Int.ofNat _ => rfl
  | Int.negSucc _ => exact (add_zero 0).symm

/-- The uniform coercion sends the zero section to zero. -/
theorem extCoe_zero (n : ℤ) (X : Cᵒᵖ) : extCoe F n X 0 = 0 := by
  match n with
  | Int.ofNat _ => rfl
  | Int.negSucc _ => rfl

/-- The uniform coercion commutes with multiplication by an integer. -/
theorem extCoe_zsmul (n : ℤ) (X : Cᵒᵖ) (c : ℤ) (x : (extPowFamily F n).obj X) :
    extCoe F n X (c • x) = c • extCoe F n X x := by
  match n with
  | Int.ofNat _ => rfl
  | Int.negSucc _ => exact (smul_zero c).symm

/-- The uniform coercion forgets a degree transport. -/
theorem extCoe_degCast {n m : ℤ} (h : n = m) (X : Cᵒᵖ) (x : (extPowFamily F n).obj X) :
    extCoe F m X
        (Stacks.degCast (F := fun q : ℤ => ((extPowFamily F q).obj X : Type (max w a))) h x) =
      extCoe F n X x := by
  subst h; rfl

/-- The uniform coercion forgets a transport of sections along an equality of degrees. -/
theorem extCoe_app_eqToHom {i j : ℤ} (h : i = j) (X : Cᵒᵖ) (y : (extPowFamily F i).obj X) :
    extCoe F j X (PresheafOfModules.Hom.app (eqToHom (congrArg (extPowFamily F) h)) X y) =
      extCoe F i X y := by
  subst h; rfl

/-- **The uniform coercion turns the graded multiplication into the multiplication of the
exterior algebra.** -/
theorem extCoe_mul (n m : ℤ) (X : Cᵒᵖ) (x : (extPowFamily F n).obj X)
    (y : (extPowFamily F m).obj X) :
    extCoe F (n + m) X
        (((extPowGradedAlgebra F).extend.mul n m).app X x y) =
      extCoe F n X x * extCoe F m X y := by
  match n, m with
  | Int.ofNat k, Int.ofNat l => rfl
  | Int.ofNat k, Int.negSucc l =>
    rw [show (((extPowGradedAlgebra F).extend.mul (Int.ofNat k) (Int.negSucc l)).app X x y) = 0 from
        (extPowGradedAlgebra F).extendMul_app_eq_zero_of_neg_right _ (by omega) X x y,
      extCoe_zero, extCoe_eq_zero_of_neg (by omega : (Int.negSucc l) < 0) X y, mul_zero]
  | Int.negSucc k, m =>
    rw [show (((extPowGradedAlgebra F).extend.mul (Int.negSucc k) m).app X x y) = 0 from
        (extPowGradedAlgebra F).extendMul_app_eq_zero_of_neg_left (by omega) _ X x y,
      extCoe_zero, extCoe_eq_zero_of_neg (by omega : (Int.negSucc k) < 0) X x, zero_mul]

/-- The uniform coercion of the Koszul differential in a positive degree, for a local section
of `extPow (m + 1) F`: it is contraction with the functional. -/
theorem extCoe_extKoszulD_succ (θ : SectionwiseDual.{v, u, w, a} F) (m : ℕ) (X : Cᵒᵖ)
    (x : (extPow (m + 1) F).obj X) :
    extCoe F (((m + 1 : ℕ) : ℤ) - 1) X
        (PresheafOfModules.Hom.app (θ.extKoszulD ((m + 1 : ℕ) : ℤ)) X x) =
      Koszul.contraction (θ.app X) (extCoe F ((m + 1 : ℕ) : ℤ) X x) := by
  have hm : ((m : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) - 1 := by omega
  exact (extCoe_app_eqToHom hm X (θ.extPowKoszulDApp m X x)).trans
    (θ.extPowKoszulDApp_coe m X x)

/-- **The uniform coercion turns the Koszul differential into contraction.** This holds in every
integer degree, including degree zero, where the differential is the zero morphism and contraction
vanishes because exterior degree zero is the image of the structure map. -/
theorem extCoe_extKoszulD (θ : SectionwiseDual.{v, u, w, a} F) (n : ℤ) (X : Cᵒᵖ)
    (x : (extPowFamily F n).obj X) :
    extCoe F (n - 1) X (PresheafOfModules.Hom.app (θ.extKoszulD n) X x) =
      Koszul.contraction (θ.app X) (extCoe F n X x) := by
  match n with
  | Int.ofNat 0 =>
    rw [show PresheafOfModules.Hom.app (θ.extKoszulD (Int.ofNat 0)) X x = 0 from rfl,
      extCoe_zero]
    exact (Koszul.contraction_eq_zero_of_mem_zero (θ.app X) (by
      exact (extPowSections 0 F X x).2)).symm
  | Int.ofNat (m + 1) => exact θ.extCoe_extKoszulD_succ m X x
  | Int.negSucc k =>
    rw [extCoe_eq_zero_of_neg (by omega : (Int.negSucc k) - 1 < 0), extCoe_eq_zero_of_neg
      (by omega : (Int.negSucc k) < 0), map_zero]

/-! ### The three identities -/

/-- **The graded Leibniz rule for the sectionwise Koszul differential**, in the shape
`Stacks.RegularSequence.KoszulChainData` asks for: the differential of a product of homogeneous
local sections is the alternating Leibniz expression, with the two degree transports written as
`Stacks.degCast`. -/
theorem extKoszulD_mul (θ : SectionwiseDual.{v, u, w, a} F) (n m : ℤ) (X : Cᵒᵖ)
    (x : (extPowFamily F n).obj X) (y : (extPowFamily F m).obj X) :
    PresheafOfModules.Hom.app (θ.extKoszulD (n + m)) X
        (((extPowGradedAlgebra F).extend.mul n m).app X x y) =
      Stacks.degCast (F := fun q : ℤ => ((extPowFamily F q).obj X : Type (max w a)))
          (by ring : (n - 1) + m = n + m - 1)
          (((extPowGradedAlgebra F).extend.mul (n - 1) m).app X
            (PresheafOfModules.Hom.app (θ.extKoszulD n) X x) y) +
        (Int.negOnePow n : ℤ) •
          Stacks.degCast (F := fun q : ℤ => ((extPowFamily F q).obj X : Type (max w a)))
            (by ring : n + (m - 1) = n + m - 1)
            (((extPowGradedAlgebra F).extend.mul n (m - 1)).app X x
              (PresheafOfModules.Hom.app (θ.extKoszulD m) X y)) := by
  refine extCoe_injective (n + m - 1) X ?_
  rw [extCoe_add, extCoe_zsmul, extCoe_degCast, extCoe_degCast, extCoe_mul, extCoe_mul,
    extCoe_extKoszulD, extCoe_extKoszulD, extCoe_extKoszulD, extCoe_mul]
  rcases lt_or_ge n 0 with hn | hn
  · rw [extCoe_eq_zero_of_neg hn]
    simp
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have hsign : ((Int.negOnePow (k : ℤ) : ℤ)) = (-1 : ℤ) ^ k := by
      rw [Int.negOnePow_def, zpow_natCast, Units.val_pow_eq_pow_val]
      norm_num
    rw [Koszul.contraction_mul_of_mem (θ.app X) k (extCoe_mem k X x)]
    congr 1
    rw [hsign, ← Int.cast_smul_eq_zsmul ((O ⋙ forget₂ CommRingCat RingCat).obj X)]
    push_cast
    ring_nf

/-- **The value of the sectionwise Koszul differential on a degree-one generator**: the
functional of the generating section, times the unit of the exterior algebra in degree zero. -/
theorem extKoszulD_extPowGen (θ : SectionwiseDual.{v, u, w, a} F) (X : Cᵒᵖ) (e : F.obj X) :
    PresheafOfModules.Hom.app (θ.extKoszulD 1) X
        (PresheafOfModules.Hom.app (extPowGen F) X e) =
      θ.app X e • (extPowGradedAlgebra F).extend.one.eval X := by
  refine extCoe_injective ((1 : ℤ) - 1) X ?_
  refine (θ.extCoe_extKoszulD 1 X _).trans ?_
  exact (by
    rw [Koszul.contraction, CliffordAlgebra.contractLeft_ι, Algebra.algebraMap_eq_smul_one] :
    Koszul.contraction (θ.app X) (ExteriorAlgebra.ι _ e) = θ.app X e • 1)

/-- **The sectionwise Koszul differential squares to zero**, because contraction does. -/
theorem extKoszulD_comp (θ : SectionwiseDual.{v, u, w, a} F) (n : ℤ) :
    θ.extKoszulD n ≫ θ.extKoszulD (n - 1) = 0 := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine extCoe_injective (n - 1 - 1) X ?_
  refine (θ.extCoe_extKoszulD (n - 1) X _).trans ?_
  refine (congrArg _ (θ.extCoe_extKoszulD n X x)).trans ?_
  exact (CliffordAlgebra.contractLeft_contractLeft (θ.app X) (extCoe F n X x)).trans
    (extCoe_zero (n - 1 - 1) X).symm

end SectionwiseDual

end PresheafOfModules

end
