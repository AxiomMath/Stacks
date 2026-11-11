module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraDescentQuotientIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedInternalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedGrothendieck
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import Mathlib.Algebra.Module.MinimalAxioms

/-!
# A graded module over a restriction of scalars is a graded module over the algebra

Let `O` be a sheaf of commutative rings on a site, `θ : S ⟶ O` a morphism of sheaves of rings
and `A` a sheaf of graded `O`-algebras. Write `A|_S` for `A` read as a sheaf of graded
`S`-algebras along `θ` (`SheafOfModules.GradedAlgebra.scalarRestrict`). A right graded
`A|_S`-module `M` carries a unique structure of right graded `A`-module with the same
homogeneous pieces, the same multiplication and the same underlying sheaves of abelian groups:
a section `r` of `O` acts on a homogeneous section `x` of `M` by multiplication with the
homogeneous section `r · 1` of `A` of degree zero,

`r • x = x (r · 1)`.

This is what makes a graded tensor product `P ⊗_{B} A` formed over `S` — for instance over
`f⁻¹O_𝒟` in the pullback of Stacks, Tag 0FR7 — an object of `Mod(A)`, the right graded modules
over `A` as a sheaf of graded `O`-algebras.

## Main definitions

* `SheafOfModules.GradedModule.ofScalarRestrict`: the right graded `A`-module underlying a right
  graded `A|_S`-module.
* `SheafOfModules.GradedModule.ofScalarRestrictMap`,
  `SheafOfModules.GradedModule.ofScalarRestrictFunctor` and
  `SheafOfModules.GradedModule.ofScalarRestrictHomOfDegree`: the construction on homomorphisms,
  the functor `Mod(A|_S) ⥤ Mod(A)`, and the construction on homomorphisms homogeneous of degree
  `n`.

## Main results

* `SheafOfModules.GradedModule.ofScalarRestrict_smul`: the multiplication is the original one.
* `SheafOfModules.GradedModule.ofScalarRestrict_smul_θ`: the new action of `O` extends the old
  action of `S`: `θ s` acts as `s` did.

## Implementation notes

The action of `O` on the pieces is defined with `Module.ofMinimalAxioms` on the sections of the
original underlying presheaf of abelian groups, and the pieces are built with
`PresheafOfModules.ofPresheaf`, so their underlying presheaves of abelian groups are those of
`M` on the nose and the sheaf condition is inherited. The module axioms are the associativity of
the action with the multiplication of `A` together with the `O`-bilinearity of that
multiplication; commutativity of `O` enters in `(rs) • x = r • (s • x)`, because
`x (s · 1) (r · 1) = x ((sr) · 1)`.

## References

* [Stacks Project, Tag 0FR7](https://stacks.math.columbia.edu/tag/0FR7)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe t a m v u

namespace SheafOfModules.GradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {O : Sheaf J CommRingCat.{t}}
  {S : Sheaf J RingCat.{t}} (θ : S ⟶ Sheaf.toRingCat J O)
  {A : GradedAlgebra.{t, a} (Sheaf.toRingCat J O)}

/-- Sections of the sheaf of rings underlying a sheaf of commutative rings commute. -/
theorem toRingCat_mul_comm (U : Cᵒᵖ) (r s : (Sheaf.toRingCat J O).obj.obj U) :
    r * s = s * r :=
  @mul_comm (O.obj.obj U) _ r s

/-- The homogeneous section `r · 1` of degree zero of `A`, read in `A|_S`. -/
def scalarOne (U : Cᵒᵖ) (r : (Sheaf.toRingCat J O).obj.obj U) :
    ((A.scalarRestrict θ).piece 0).val.obj U :=
  (r • A.one.eval U : (A.piece 0).val.obj U)

/-- `r · 1` is additive in `r`. -/
theorem scalarOne_add (U : Cᵒᵖ) (r s : (Sheaf.toRingCat J O).obj.obj U) :
    scalarOne θ (A := A) U (r + s) = scalarOne θ U r + scalarOne θ U s :=
  add_smul r s (A.one.eval U)

/-- `1 · 1 = 1`. -/
theorem scalarOne_one (U : Cᵒᵖ) :
    scalarOne θ (A := A) U 1 = (A.scalarRestrict θ).one.eval U :=
  one_smul _ (A.one.eval U)

/-- The product of `r · 1` and `s · 1` in degree zero is `(rs) · 1`. -/
theorem mul_scalarOne (U : Cᵒᵖ) (r s : (Sheaf.toRingCat J O).obj.obj U) :
    ((A.scalarRestrict θ).mul 0 0).app U (scalarOne θ U r) (scalarOne θ U s) =
      scalarOne θ (A := A) U (r * s) := by
  change (A.mul 0 0).app U (r • A.one.eval U) (s • A.one.eval U) = (r * s) • A.one.eval U
  rw [(A.mul 0 0).map_smul_left, (A.mul 0 0).map_smul_right, smul_smul,
    eq_of_heq (A.mul_one 0 U (A.one.eval U))]

omit [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- Scalar multiples of heterogeneously equal sections in equal degrees are heterogeneously
equal. -/
theorem smul_heq_smul {R : Sheaf J RingCat.{t}} (P : ℤ → SheafOfModules.{a} R) {k k' : ℤ}
    (h : k = k') (U : Cᵒᵖ) (r : R.obj.obj U) {z : (P k).val.obj U} {z' : (P k').val.obj U}
    (hz : HEq z z') : HEq (r • z) (r • z') := by
  subst h
  cases hz
  rfl

/-- The action of a section `r` of `O` on a homogeneous section of `A`, read in `A|_S`. -/
def algSMul (i : ℤ) (U : Cᵒᵖ) (r : (Sheaf.toRingCat J O).obj.obj U)
    (y : ((A.scalarRestrict θ).piece i).val.obj U) : ((A.scalarRestrict θ).piece i).val.obj U :=
  (r • (@id ((A.piece i).val.obj U) y) : (A.piece i).val.obj U)

/-- Multiplying by `r · 1` on the left is the action of `r`. -/
theorem heq_mul_scalarOne_left (U : Cᵒᵖ) (r : (Sheaf.toRingCat J O).obj.obj U) (i : ℤ)
    (y : ((A.scalarRestrict θ).piece i).val.obj U) :
    HEq (((A.scalarRestrict θ).mul 0 i).app U (scalarOne θ U r) y) (algSMul θ i U r y) := by
  change HEq ((A.mul 0 i).app U (r • A.one.eval U) (@id ((A.piece i).val.obj U) y))
    (r • (@id ((A.piece i).val.obj U) y))
  rw [(A.mul 0 i).map_smul_left]
  exact smul_heq_smul A.piece (zero_add i) U r (A.one_mul i U y)

/-- Multiplying by `r · 1` on the right is the action of `r`. -/
theorem heq_mul_scalarOne_right (U : Cᵒᵖ) (r : (Sheaf.toRingCat J O).obj.obj U) (i : ℤ)
    (y : ((A.scalarRestrict θ).piece i).val.obj U) :
    HEq (((A.scalarRestrict θ).mul i 0).app U y (scalarOne θ U r)) (algSMul θ i U r y) := by
  change HEq ((A.mul i 0).app U (@id ((A.piece i).val.obj U) y) (r • A.one.eval U))
    (r • (@id ((A.piece i).val.obj U) y))
  rw [(A.mul i 0).map_smul_right]
  exact smul_heq_smul A.piece (add_zero i) U r (A.mul_one i U y)

/-- The section `r · 1` commutes with restriction. -/
theorem scalarOne_naturality {U V : Cᵒᵖ} (f : U ⟶ V) (r : (Sheaf.toRingCat J O).obj.obj U) :
    ((A.scalarRestrict θ).piece 0).val.map f (scalarOne θ U r) =
      scalarOne θ V ((Sheaf.toRingCat J O).obj.map f r) := by
  change (A.piece 0).val.map f (r • A.one.eval U) =
    (Sheaf.toRingCat J O).obj.map f r • A.one.eval V
  rw [(A.piece 0).val.map_smul, PresheafOfModules.sections_property]
  rfl

variable (M : GradedModule.{t, a, m} (A.scalarRestrict θ))

/-- The two values of the action of `M` in heterogeneously equal algebra degrees agree. -/
theorem smul_heq_smul_right {n i i' : ℤ} (h : i = i') (U : Cᵒᵖ) (x : (M.piece n).val.obj U)
    {y : ((A.scalarRestrict θ).piece i).val.obj U} {y' : ((A.scalarRestrict θ).piece i').val.obj U}
    (hy : HEq y y') : HEq (M.smul n i U x y) (M.smul n i' U x y') := by
  subst h
  cases hy
  rfl

/-- The action of a section `r` of `O` on a homogeneous section of degree `n` of `M`:
multiplication by `r · 1`. -/
def scalarAct (n : ℤ) (U : Cᵒᵖ) (r : (Sheaf.toRingCat J O).obj.obj U) :
    (M.piece n).val.obj U →+ (M.piece n).val.obj U :=
  (castHom M.piece (add_zero n) U).comp ((M.smul n 0 U).flip (scalarOne θ U r))

theorem scalarAct_apply (n : ℤ) (U : Cᵒᵖ) (r : (Sheaf.toRingCat J O).obj.obj U)
    (x : (M.piece n).val.obj U) :
    scalarAct θ M n U r x = castHom M.piece (add_zero n) U (M.smul n 0 U x (scalarOne θ U r)) :=
  rfl

/-- The action of `r` is heterogeneously equal to multiplication by `r · 1`. -/
theorem scalarAct_heq (n : ℤ) (U : Cᵒᵖ) (r : (Sheaf.toRingCat J O).obj.obj U)
    (x : (M.piece n).val.obj U) :
    HEq (scalarAct θ M n U r x) (M.smul n 0 U x (scalarOne θ U r)) :=
  heq_castHom M.piece (add_zero n) U _

/-- Acting by `r` and then multiplying by `y` is multiplying by `r y`. -/
theorem smul_scalarAct (n i : ℤ) (U : Cᵒᵖ) (r : (Sheaf.toRingCat J O).obj.obj U)
    (x : (M.piece n).val.obj U) (y : ((A.scalarRestrict θ).piece i).val.obj U) :
    M.smul n i U (scalarAct θ M n U r x) y = M.smul n i U x (algSMul θ i U r y) := by
  rw [scalarAct_apply, Cofree.smul_castHom_left]
  refine eq_of_heq ((heq_castHom M.piece _ U _).trans ?_)
  refine (M.smul_mul n 0 i U x (scalarOne θ U r) y).trans ?_
  exact smul_heq_smul_right θ M (zero_add i) U x (heq_mul_scalarOne_left θ U r i y)

/-- Multiplying by `y` and then acting by `r` is multiplying by `r y`. -/
theorem scalarAct_smul (n i : ℤ) (U : Cᵒᵖ) (r : (Sheaf.toRingCat J O).obj.obj U)
    (x : (M.piece n).val.obj U) (y : ((A.scalarRestrict θ).piece i).val.obj U) :
    scalarAct θ M (n + i) U r (M.smul n i U x y) = M.smul n i U x (algSMul θ i U r y) := by
  refine eq_of_heq ((scalarAct_heq θ M (n + i) U r _).trans ?_)
  refine (M.smul_mul n i 0 U x y (scalarOne θ U r)).trans ?_
  exact smul_heq_smul_right θ M (add_zero i) U x (heq_mul_scalarOne_right θ U r i y)

/-- Acting by `1` is the identity. -/
theorem scalarAct_one (n : ℤ) (U : Cᵒᵖ) (x : (M.piece n).val.obj U) :
    scalarAct θ M n U 1 x = x := by
  refine eq_of_heq ((scalarAct_heq θ M n U 1 x).trans ?_)
  rw [scalarOne_one]
  exact M.smul_one n U x

/-- Acting by `r s` is acting by `s` and then by `r`. -/
theorem scalarAct_mul (n : ℤ) (U : Cᵒᵖ) (r s : (Sheaf.toRingCat J O).obj.obj U)
    (x : (M.piece n).val.obj U) :
    scalarAct θ M n U (r * s) x = scalarAct θ M n U r (scalarAct θ M n U s x) := by
  refine eq_of_heq ((scalarAct_heq θ M n U (r * s) x).trans ?_)
  refine HEq.trans ?_ (scalarAct_heq θ M n U r _).symm
  rw [scalarAct_apply, Cofree.smul_castHom_left]
  refine HEq.trans ?_ (heq_castHom M.piece _ U _).symm
  refine HEq.trans ?_ (M.smul_mul n 0 0 U x (scalarOne θ U s) (scalarOne θ U r)).symm
  rw [mul_scalarOne, toRingCat_mul_comm U r s]
  rfl

/-- The action of `r` commutes with restriction, along the restriction of `r`. -/
theorem scalarAct_naturality (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (r : (Sheaf.toRingCat J O).obj.obj U) (x : (M.piece n).val.obj U) :
    (M.piece n).val.map f (scalarAct θ M n U r x) =
      scalarAct θ M n V ((Sheaf.toRingCat J O).obj.map f r) ((M.piece n).val.map f x) := by
  change (M.piece n).val.map f
      (castHom M.piece (add_zero n) U (M.smul n 0 U x (scalarOne θ U r))) =
    castHom M.piece (add_zero n) V (M.smul n 0 V ((M.piece n).val.map f x)
      (scalarOne θ V ((Sheaf.toRingCat J O).obj.map f r)))
  rw [castHom_naturality, M.smul_naturality, scalarOne_naturality]

/-- The `O(U)`-module structure on the sections over `U` of the degree-`n` piece. -/
abbrev scalarModule (n : ℤ) (U : Cᵒᵖ) :
    Module ((Sheaf.toRingCat J O).obj.obj U) ((M.piece n).val.presheaf.obj U) :=
  letI : SMul ((Sheaf.toRingCat J O).obj.obj U) ((M.piece n).val.presheaf.obj U) :=
    ⟨fun r x => scalarAct θ M n U r x⟩
  Module.ofMinimalAxioms
    (fun r x y => map_add (scalarAct θ M n U r) x y)
    (fun r s x => by
      change castHom M.piece (add_zero n) U (M.smul n 0 U x (scalarOne θ U (r + s))) =
        castHom M.piece (add_zero n) U (M.smul n 0 U x (scalarOne θ U r)) +
          castHom M.piece (add_zero n) U (M.smul n 0 U x (scalarOne θ U s))
      rw [scalarOne_add, map_add, map_add])
    (fun r s x => scalarAct_mul θ M n U r s x)
    (fun x => scalarAct_one θ M n U x)

/-- The degree-`n` piece of the lifted module, as a presheaf of `O`-modules. -/
noncomputable def liftPresheaf (n : ℤ) : PresheafOfModules.{m} (Sheaf.toRingCat J O).obj :=
  letI := fun U => scalarModule θ M n U
  PresheafOfModules.ofPresheaf (M.piece n).val.presheaf
    (fun {_ _} f r x => scalarAct_naturality θ M n f r x)

/-- The degree-`n` piece of the lifted module, as a sheaf of `O`-modules. -/
noncomputable def liftPiece (n : ℤ) : SheafOfModules.{m} (Sheaf.toRingCat J O) where
  val := liftPresheaf θ M n
  isSheaf := (M.piece n).isSheaf

/-- **The right graded `A`-module underlying a right graded `A|_S`-module.** The pieces have the
same underlying sheaves of abelian groups, a section `r` of `O` acting by multiplication with
`r · 1`, and the multiplication is the original one. -/
noncomputable def ofScalarRestrict : GradedModule.{t, a, m} A where
  piece n := liftPiece θ M n
  smul n i U := M.smul n i U
  smul_smul_left n i U r x y :=
    (smul_scalarAct θ M n i U r x y).trans (scalarAct_smul θ M n i U r x y).symm
  smul_smul_right n i U r x y := (scalarAct_smul θ M n i U r x y).symm
  smul_naturality n i _ _ f x y := M.smul_naturality n i f x y
  smul_mul n i j U x y z := M.smul_mul n i j U x y z
  smul_one n U x := M.smul_one n U x

/-- The multiplication of `ofScalarRestrict θ M` is that of `M`. -/
theorem ofScalarRestrict_smul (n i : ℤ) (U : Cᵒᵖ) (x : (M.piece n).val.obj U)
    (y : (A.piece i).val.obj U) :
    (ofScalarRestrict θ M).smul n i U x y = M.smul n i U x y :=
  rfl

/-- The action of a section `r` of `O` on `ofScalarRestrict θ M` is multiplication by `r · 1`. -/
theorem ofScalarRestrict_smul_eq (n : ℤ) (U : Cᵒᵖ) (r : (Sheaf.toRingCat J O).obj.obj U)
    (x : ((ofScalarRestrict θ M).piece n).val.obj U) :
    r • x = scalarAct θ M n U r x :=
  rfl

/-- **The new action of `O` extends the old action of `S`**: `θ s` acts on `ofScalarRestrict θ M`
as `s` acts on `M`. -/
theorem ofScalarRestrict_smul_θ (n : ℤ) (U : Cᵒᵖ) (s : S.obj.obj U)
    (x : (M.piece n).val.obj U) :
    scalarAct θ M n U ((θ.hom.app U).hom s) x = s • x := by
  have h : scalarOne θ (A := A) U ((θ.hom.app U).hom s) =
      s • (A.scalarRestrict θ).one.eval U := rfl
  rw [scalarAct_apply, h, M.smul_smul_right, castHom_smul]
  exact congrArg (s • ·) (eq_of_heq ((heq_castHom M.piece (add_zero n) U _).trans
    (M.smul_one n U x)))

/-! ### Homomorphisms -/

variable {M} {M' : GradedModule.{t, a, m} (A.scalarRestrict θ)}

/-- A homomorphism of right graded `A|_S`-modules commutes with the action of `O`. -/
theorem app_scalarAct (g : M ⟶ M') (n : ℤ) (U : Cᵒᵖ) (r : (Sheaf.toRingCat J O).obj.obj U)
    (x : (M.piece n).val.obj U) :
    (g.app n).val.app U (scalarAct θ M n U r x) =
      scalarAct θ M' n U r ((g.app n).val.app U x) := by
  rw [scalarAct_apply, scalarAct_apply, hom_app_castHom, g.map_smul]

/-- The morphism of sheaves of `O`-modules underlying a morphism of sheaves of `S`-modules which
commutes with the actions of `O`. -/
noncomputable def liftPieceHom {i j : ℤ} {M₁ M₂ : GradedModule.{t, a, m} (A.scalarRestrict θ)}
    (φ : M₁.piece i ⟶ M₂.piece j)
    (hφ : ∀ (U : Cᵒᵖ) (r : (Sheaf.toRingCat J O).obj.obj U) (x : (M₁.piece i).val.obj U),
      φ.val.app U (scalarAct θ M₁ i U r x) = scalarAct θ M₂ j U r (φ.val.app U x)) :
    liftPiece θ M₁ i ⟶ liftPiece θ M₂ j :=
  ⟨PresheafOfModules.homMk (M₁ := (liftPiece θ M₁ i).val) (M₂ := (liftPiece θ M₂ j).val)
    ((PresheafOfModules.toPresheaf S.obj).map φ.val) hφ⟩

/-- The components of `liftPieceHom` are those of the original morphism. -/
theorem liftPieceHom_app {i j : ℤ} {M₁ M₂ : GradedModule.{t, a, m} (A.scalarRestrict θ)}
    (φ : M₁.piece i ⟶ M₂.piece j) (hφ) (U : Cᵒᵖ) (x : (M₁.piece i).val.obj U) :
    (liftPieceHom θ φ hφ).val.app U x = φ.val.app U x :=
  rfl

/-- **The homomorphism of right graded `A`-modules underlying a homomorphism of right graded
`A|_S`-modules**: the same degreewise maps. -/
noncomputable def ofScalarRestrictMap (g : M ⟶ M') :
    ofScalarRestrict θ M ⟶ ofScalarRestrict θ M' where
  app n := liftPieceHom θ (g.app n) (app_scalarAct θ g n)
  map_smul n i U x y := g.map_smul n i U x y

/-- The degreewise maps of `ofScalarRestrictMap θ g` are those of `g`. -/
theorem ofScalarRestrictMap_app (g : M ⟶ M') (n : ℤ) (U : Cᵒᵖ) (x : (M.piece n).val.obj U) :
    ((ofScalarRestrictMap θ g).app n).val.app U x = (g.app n).val.app U x :=
  rfl

variable (A) in
/-- **The functor `Mod(A|_S) ⥤ Mod(A)`**, the identity on underlying degreewise data. -/
noncomputable def ofScalarRestrictFunctor :
    GradedModule.{t, a, m} (A.scalarRestrict θ) ⥤ GradedModule.{t, a, m} A where
  obj M := ofScalarRestrict θ M
  map g := ofScalarRestrictMap θ g
  map_id _ := Hom.ext fun _ => SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ => rfl)
  map_comp _ _ := Hom.ext fun _ =>
    SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ => rfl)

omit [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- Values of a homogeneous homomorphism on heterogeneously equal sections in equal degrees are
heterogeneously equal. -/
theorem _root_.SheafOfModules.GradedHomOfDegree.app_heq {R : Sheaf J RingCat.{t}}
    {B : GradedAlgebra.{t, a} R} {M₁ M₂ : GradedModule.{t, a, m} B} {d : ℤ}
    (g : GradedHomOfDegree M₁ M₂ d) {i i' j j' : ℤ} (hij : i + d = j) (hij' : i' + d = j')
    (hi : i = i') (U : Cᵒᵖ) {x : (M₁.piece i).val.obj U} {x' : (M₁.piece i').val.obj U}
    (hx : HEq x x') : HEq ((g.app i j hij).val.app U x) ((g.app i' j' hij').val.app U x') := by
  subst hi
  obtain rfl : j = j' := by omega
  cases hx
  rfl

/-- A homogeneous homomorphism of right graded `A|_S`-modules commutes with the action of `O`. -/
theorem homOfDegree_app_scalarAct {d : ℤ} (g : GradedHomOfDegree M M' d) (i j : ℤ)
    (hij : i + d = j) (U : Cᵒᵖ) (r : (Sheaf.toRingCat J O).obj.obj U)
    (x : (M.piece i).val.obj U) :
    (g.app i j hij).val.app U (scalarAct θ M i U r x) =
      scalarAct θ M' j U r ((g.app i j hij).val.app U x) := by
  refine eq_of_heq (HEq.trans ?_ (scalarAct_heq θ M' j U r _).symm)
  refine HEq.trans (g.app_heq hij (show i + 0 + d = j + 0 by omega) (add_zero i).symm U
    (scalarAct_heq θ M i U r x)) ?_
  rw [g.map_mul i j hij 0 U x (scalarOne θ U r)]

/-- **The homomorphism of right graded `A`-modules homogeneous of degree `d` underlying one of
right graded `A|_S`-modules**: the same components. -/
noncomputable def ofScalarRestrictHomOfDegree {d : ℤ} (g : GradedHomOfDegree M M' d) :
    GradedHomOfDegree (ofScalarRestrict θ M) (ofScalarRestrict θ M') d where
  app i j hij := liftPieceHom θ (g.app i j hij) (homOfDegree_app_scalarAct θ g i j hij)
  map_mul i j hij p U x b := g.map_mul i j hij p U x b

/-- The components of `ofScalarRestrictHomOfDegree θ g` are those of `g`. -/
theorem ofScalarRestrictHomOfDegree_app {d : ℤ} (g : GradedHomOfDegree M M' d) (i j : ℤ)
    (hij : i + d = j) (U : Cᵒᵖ) (x : (M.piece i).val.obj U) :
    ((ofScalarRestrictHomOfDegree θ g).app i j hij).val.app U x =
      (g.app i j hij).val.app U x :=
  rfl

end SheafOfModules.GradedModule
