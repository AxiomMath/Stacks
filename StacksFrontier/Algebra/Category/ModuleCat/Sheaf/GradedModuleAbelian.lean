module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksCore.Tactic.StacksAttribute

/-!
# Graded modules over a sheaf of graded algebras form an abelian category

Let `R` be a sheaf of rings on a site `(C, J)` and let `A` be a sheaf of `ℤ`-graded
`R`-algebras. [Stacks, Tag 0FR0](https://stacks.math.columbia.edu/tag/0FR0) says that the
category `Mod(A)` of right graded `A`-modules is abelian, that it has arbitrary direct sums,
and that the functor `M ↦ Mⁿ` taking a graded module to its degree-`n` component commutes with
all colimits — kernels, cokernels and direct sums all being formed degreewise.

This file proves those three statements. The category, its preadditive structure and the
functor `M ↦ Mⁿ` are those of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedDegreeColimits.lean`, as is the reduction
of "`pieceFunctor` commutes with all colimits" to the degreewise coproduct and cokernel facts;
what is added here is those facts and the abelian structure they produce.

## Main definitions

* `SheafOfModules.PreGradedModule` is a right graded `A`-module whose homogeneous pieces are
  only *presheaves* of modules, and `SheafOfModules.PreGradedModule.sheafify` is its degreewise
  sheafification. `SheafOfModules.PreGradedModule.transfer` is the general transport of a
  graded-module structure along a degreewise locally bijective map into sheaves.
* `Stacks.quotPresheaf` is the sectionwise quotient of a presheaf of modules by the image of a
  morphism, and `SheafOfModules.directSumPresheaf` the sectionwise direct sum of a family of
  presheaves of modules.
* `SheafOfModules.kerSubmodule` and `SheafOfModules.kerObj` are the sectionwise kernel of a
  morphism of sheaves of modules.
* `SheafOfModules.GradedModule.ker`, `SheafOfModules.GradedModule.coker` and
  `SheafOfModules.GradedModule.directSum` are the degreewise kernel, cokernel and direct sum of
  graded modules.
* `Stacks.degCast` transports a term along an equality of integer degrees, and `Stacks.restr`
  is the restriction map of a presheaf of modules with the type of its target cleaned up; see
  the implementation notes.

## Main results

* `SheafOfModules.GradedModule.abelian` is Tag 0FR0's assertion that `Mod(A)` is abelian. It is
  obtained from the degreewise kernels (`GradedModule.kerIsLimit`) and cokernels
  (`GradedModule.cokerIsColimit`) together with
  `GradedModule.isIso_coimageImageComparison`, which holds because taking a homogeneous
  component preserves both and `SheafOfModules.{m} R` is itself abelian.
* `SheafOfModules.GradedModule.hasCoproducts` and
  `SheafOfModules.GradedModule.pieceFunctor_preservesCoproducts` are Tag 0FR0's assertion that
  `Mod(A)` has arbitrary direct sums, formed degreewise.
* `SheafOfModules.GradedModule.pieceFunctor_preservesColimits` is Tag 0FR0's assertion that
  `M ↦ Mⁿ` commutes with all colimits.
* `SheafOfModules.GradedModule.exists_kernel_degreewise` and
  `SheafOfModules.GradedModule.exists_cokernel_degreewise` package the degreewise kernel and
  cokernel in existential form: the object exists, each of its homogeneous pieces is a kernel
  respectively cokernel of the corresponding piece of `f`, and it has the universal property in
  the category of graded modules.

## Implementation notes

**The hypotheses, and why they are the source's.** Tag 0FR0 is stated for a ringed site, and
its proof defers the exactness of `Mod(O)` to Cohomology on Sites, where `Mod(O)` is a
Grothendieck abelian category; that in turn rests on the standing convention that a site admits
sheafification. In Lean that convention is not automatic, and the two conditions which make
`SheafOfModules.{m} R` abelian — `HasSheafify J AddCommGrpCat.{m}` and
`J.WEqualsLocallyBijective AddCommGrpCat.{m}` — are therefore hypotheses here. Nothing weaker
is assumed, and nothing is assumed about the site beyond them: in particular the site is
arbitrary, the base is an arbitrary sheaf of rings rather than the structure sheaf of a ringed
site, and the universes of the site, the ring, the algebra pieces and the module pieces are
independent.

**Universes.** The index type of a direct sum is `ι : Type m`, the module universe. This is
forced: `SheafOfModules.{m} R` has colimits of shape `K` only for `K` small relative to `m`, so
a direct sum indexed by a larger type does not exist. Correspondingly the *unconditional*
statement `PreservesColimits (pieceFunctor A n)` — which abbreviates
`PreservesColimitsOfSize.{s, s}` for `s` the hom universe of `SheafOfModules.{m} R`, and that
hom universe is `max u m` for a site `C : Type u` — holds at module universe `max u m`, not at
a module universe free of `u`. `pieceFunctor_preservesColimitsOfSize` records the same content
with the size universe free, and that is the form to use when the module universe is not of
that shape.

**Degreewise constructions and sheafification.** A cokernel or a direct sum of sheaves of
modules has no description on sections — it is a sheafification — so the action of `A` on it
cannot be written down directly, which is the one real obstacle to forming kernels, cokernels
and direct sums degreewise. The route taken is to build the construction first at the level of
presheaves, where it *is* sectionwise, as a `PreGradedModule`, and then to transport the action
along the degreewise sheafification maps. The transport is `PreGradedModule.transfer`; it works
because a bilinear map into a sheaf does not see a local bijection in its first variable, which
is `Stacks.BilinearMap.extend` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Algebras.lean`. Kernels need none of this: the
presheaf kernel of a morphism of sheaves is already a sheaf, so the kernel is built directly as
a `SheafOfModules.Submodule`.

**`Stacks.restr` and `Stacks.degCast`.** Both exist to keep `rw` usable. The restriction map of
a presheaf of modules has target `(ModuleCat.restrictScalars _).obj (M.obj V)`, which is only
*definitionally* `M.obj V`; a term that puts `M.map f x` where `M.obj V` is expected elaborates
fine but is not type-correct at the transparency `rw` uses to build its motive, so rewriting
such a goal fails. `Stacks.restr` is the same function with the clean target type. Similarly
the associativity and unit laws of a graded module relate sections in degrees `(n + i) + j` and
`n + (i + j)`, which are propositionally but not definitionally equal; those laws are stated
with `HEq` upstream, and `Stacks.degCast` turns them into equations that can be rewritten.

## References

* [Stacks Project, Tag 0FR0](https://stacks.math.columbia.edu/tag/0FR0)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w t a m v u

/-! ### Transport along an equality of degrees -/

namespace Stacks

/-- Transport of a term along an equality of integer degrees. -/
def degCast {F : ℤ → Sort*} {i j : ℤ} (h : i = j) (x : F i) : F j := by subst h; exact x

@[simp]
theorem degCast_rfl {F : ℤ → Sort*} {i : ℤ} (x : F i) : degCast (F := F) rfl x = x := rfl

theorem heq_degCast {F : ℤ → Sort*} {i j : ℤ} (h : i = j) (x : F i) :
    HEq (degCast (F := F) h x) x := by subst h; rfl

theorem heq_of_degCast_eq {F : ℤ → Sort*} {i j : ℤ} (h : i = j) {x : F i} {y : F j}
    (hxy : degCast (F := F) h x = y) : HEq x y :=
  (heq_degCast h x).symm.trans (heq_of_eq hxy)

theorem degCast_eq_of_heq {F : ℤ → Sort*} {i j : ℤ} (h : i = j) {x : F i} {y : F j}
    (hxy : HEq x y) : degCast (F := F) h x = y := by subst h; exact eq_of_heq hxy

/-- Transport along an equality of degrees commutes with any degreewise family of functions. -/
theorem degCast_map {F G : ℤ → Sort*} (φ : ∀ k, F k → G k) {i j : ℤ} (h : i = j) (x : F i) :
    degCast (F := G) h (φ i x) = φ j (degCast (F := F) h x) := by subst h; rfl

/-- Transport along an equality of degrees commutes with a degreewise family of functions of two
arguments, the second of which does not depend on the degree. -/
theorem degCast_map₂ {F G : ℤ → Sort*} {E : Sort*} (φ : ∀ k, F k → E → G k) {i j : ℤ} (h : i = j)
    (x : F i) (e : E) : degCast (F := G) h (φ i x e) = φ j (degCast (F := F) h x) e := by
  subst h; rfl

section Restr

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{t}}

/-- The restriction map of a presheaf of modules, read as a map `M.obj U → M.obj V` rather than
as a map into the restriction of scalars of `M.obj V`.

The two are the same function and the two target types are definitionally equal, but only after
unfolding `ModuleCat.restrictScalars`; a term that mentions `M.map f x` in a position expecting
`M.obj V` is therefore not type-correct at the transparency `rw` uses when it builds its motive.
Stating the restriction maps through `restr` keeps every rewrite below on type-correct terms. -/
noncomputable def restr (M : PresheafOfModules.{m} R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : M.obj U) : M.obj V :=
  M.map f x

theorem restr_sections (M : PresheafOfModules.{m} R) (s : M.sections) {U V : Cᵒᵖ} (f : U ⟶ V) :
    restr M f (s.eval U) = s.eval V :=
  PresheafOfModules.sections_property s f

theorem restr_app {M N : PresheafOfModules.{m} R} (φ : M ⟶ N) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : M.obj U) : φ.app V (restr M f x) = restr N f (φ.app U x) :=
  PresheafOfModules.naturality_apply φ f x

end Restr

end Stacks

/-! ### Postcomposition of a bilinear map -/

namespace Stacks.BilinearMap

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{t}}

theorem restr_bil {M : PresheafOfModules.{m} R} {N : PresheafOfModules.{a} R}
    {P : PresheafOfModules.{w} R} (β : BilinearMap M N P) {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.obj U)
    (y : N.obj U) : restr P f (β.app U x y) = β.app V (restr M f x) (restr N f y) :=
  β.naturality f x y

/- `Stacks.BilinearMap.postcomp` is not redeclared here: it is defined, at the same generality
(three independent module universes), in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor`, and that module is imported
instead, since a second declaration would make the two modules impossible to co-import. -/

end Stacks.BilinearMap

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- Transport along an equality of degrees commutes with the restriction maps of a degreewise
family of sheaves of modules. -/
theorem degCast_restrict (X : ℤ → SheafOfModules.{m} R) {i j : ℤ} (h : i = j) {U V : Cᵒᵖ}
    (f : U ⟶ V) (x : (X i).val.obj U) :
    Stacks.restr (X j).val f (Stacks.degCast (F := fun k ↦ (X k).val.obj U) h x)
      = Stacks.degCast (F := fun k ↦ (X k).val.obj V) h (Stacks.restr (X i).val f x) := by
  subst h; rfl

/-- Transport along an equality of degrees commutes with a degreewise family of morphisms from
presheaves of modules to sheaves of modules. -/
theorem degCast_app (X : ℤ → PresheafOfModules.{m} R.obj) (Y : ℤ → SheafOfModules.{m} R)
    (φ : ∀ n, X n ⟶ (Y n).val) {i j : ℤ} (h : i = j) (U : Cᵒᵖ) (x : (X i).obj U) :
    (φ j).app U (Stacks.degCast (F := fun k ↦ (X k).obj U) h x)
      = Stacks.degCast (F := fun k ↦ (Y k).val.obj U) h ((φ i).app U x) := by
  subst h; rfl

namespace GradedModule

variable {A : GradedAlgebra.{t, a} R}

/-- The action of a graded module, bundled as a bilinear map of sheaves of modules. -/
def smulBil (M : GradedModule.{t, a, m} A) (n i : ℤ) :
    Stacks.BilinearMap (M.piece n).val (A.piece i).val (M.piece (n + i)).val where
  app := M.smul n i
  map_smul_left := M.smul_smul_left n i
  map_smul_right := M.smul_smul_right n i
  naturality := M.smul_naturality n i

@[simp]
theorem smulBil_app (M : GradedModule.{t, a, m} A) (n i : ℤ) (U : Cᵒᵖ)
    (x : (M.piece n).val.obj U) (y : (A.piece i).val.obj U) :
    (M.smulBil n i).app U x y = M.smul n i U x y := rfl

end GradedModule

/-! ### Graded modules whose pieces are presheaves of modules -/

/-- A right graded `A`-module whose homogeneous pieces are only *presheaves* of modules.

This is the same data as `SheafOfModules.GradedModule` with the sheaf conditions dropped from
the pieces. It is the shape in which the degreewise constructions of Tag 0FR0 — the degreewise
cokernel and the degreewise direct sum — are first available: both are formed sectionwise at
the level of presheaves, and only afterwards sheafified. The associativity and unit laws are
stated with the transport `Stacks.degCast` rather than with `HEq`, which is how the
constructions below supply them. -/
structure PreGradedModule (A : GradedAlgebra.{t, a} R) where
  /-- The presheaf of modules in each degree. -/
  piece : ℤ → PresheafOfModules.{m} R.obj
  /-- The action, as a bilinear map of presheaves of modules. -/
  smulBil (n i : ℤ) : Stacks.BilinearMap (piece n) (A.piece i).val (piece (n + i))
  /-- The action is associative. -/
  smulBil_assoc (n i j : ℤ) (U : Cᵒᵖ) (x : (piece n).obj U) (y : (A.piece i).val.obj U)
      (z : (A.piece j).val.obj U) :
    Stacks.degCast (F := fun k ↦ (piece k).obj U) (add_assoc n i j)
        ((smulBil (n + i) j).app U ((smulBil n i).app U x y) z)
      = (smulBil n (i + j)).app U x ((A.mul i j).app U y z)
  /-- The degree-zero unit of the algebra acts as the identity. -/
  smulBil_one (n : ℤ) (U : Cᵒᵖ) (x : (piece n).obj U) :
    Stacks.degCast (F := fun k ↦ (piece k).obj U) (add_zero n)
      ((smulBil n 0).app U x (A.one.eval U)) = x

namespace PreGradedModule

variable {A : GradedAlgebra.{t, a} R} (P : PreGradedModule.{t, a, m} A)
  (S : ℤ → SheafOfModules.{m} R) (α : ∀ n, P.piece n ⟶ (S n).val)
  [∀ n, PresheafOfModules.IsLocallySurjective J (α n)]
  [∀ n, PresheafOfModules.IsLocallyInjective J (α n)]

/-- The action transported from a presheaf-level graded module to a degreewise sheafification
of it, as a bilinear map of sheaves of modules. -/
noncomputable def transferBil (n i : ℤ) :
    Stacks.BilinearMap (S n).val (A.piece i).val (S (n + i)).val :=
  Stacks.BilinearMap.extend (S (n + i)).isSheaf (α n) ((P.smulBil n i).postcomp (α (n + i)))

@[simp]
theorem transferBil_app (n i : ℤ) (U : Cᵒᵖ) (x : (P.piece n).obj U)
    (y : (A.piece i).val.obj U) :
    (P.transferBil S α n i).app U ((α n).app U x) y =
      (α (n + i)).app U ((P.smulBil n i).app U x y) :=
  Stacks.BilinearMap.extendVal_app (S (n + i)).isSheaf (α n)
    ((P.smulBil n i).postcomp (α (n + i))) x y

/-- **Transport of a graded-module structure along a degreewise local bijection.** If the
homogeneous pieces of a presheaf-level graded module `P` have degreewise locally bijective
maps into sheaves of modules `S`, then `S` carries a unique graded-module structure for which
those maps are compatible with the actions.

This is the step that makes the degreewise constructions of Tag 0FR0 available in the category
of sheaves: a cokernel or a direct sum of sheaves of modules has no sectionwise description, so
its action cannot be written down directly, but the presheaf-level construction it sheafifies
does, and bilinear maps into a sheaf do not see the difference. -/
noncomputable def transfer : GradedModule.{t, a, m} A where
  piece := S
  smul n i U := (P.transferBil S α n i).app U
  smul_smul_left n i := (P.transferBil S α n i).map_smul_left
  smul_smul_right n i := (P.transferBil S α n i).map_smul_right
  smul_naturality n i := (P.transferBil S α n i).naturality
  smul_mul n i j U x y z := by
    refine Stacks.heq_of_degCast_eq (F := fun k ↦ (S k).val.obj U) (add_assoc n i j) ?_
    refine Stacks.eq_of_forall_lift (S (n + (i + j))).isSheaf.isSeparated (α n) x _ _ ?_
    intro V f p hp
    have hp' : (α n).app V p = Stacks.restr (S n).val f x := hp
    change Stacks.restr (S (n + (i + j))).val f _ = Stacks.restr (S (n + (i + j))).val f _
    rw [degCast_restrict S (add_assoc n i j) f,
      (P.transferBil S α (n + i) j).restr_bil f, (P.transferBil S α n i).restr_bil f,
      (P.transferBil S α n (i + j)).restr_bil f, (A.mul i j).restr_bil f, ← hp',
      P.transferBil_app, P.transferBil_app, P.transferBil_app,
      ← degCast_app P.piece S α (add_assoc n i j) V, P.smulBil_assoc]
  smul_one n U x := by
    refine Stacks.heq_of_degCast_eq (F := fun k ↦ (S k).val.obj U) (add_zero n) ?_
    refine Stacks.eq_of_forall_lift (S n).isSheaf.isSeparated (α n) x _ _ ?_
    intro V f p hp
    have hp' : (α n).app V p = Stacks.restr (S n).val f x := hp
    change Stacks.restr (S n).val f _ = Stacks.restr (S n).val f _
    rw [degCast_restrict S (add_zero n) f, (P.transferBil S α n 0).restr_bil f,
      Stacks.restr_sections, ← hp', P.transferBil_app,
      ← degCast_app P.piece S α (add_zero n) V, P.smulBil_one]

@[simp]
theorem transfer_piece : (P.transfer S α).piece = S := rfl

@[simp]
theorem transfer_smul (n i : ℤ) (U : Cᵒᵖ) (x : (S n).val.obj U)
    (y : (A.piece i).val.obj U) :
    (P.transfer S α).smul n i U x y = (P.transferBil S α n i).app U x y := rfl

/-- The transported action is the only one compatible with the given degreewise maps: a family
of bilinear maps on `S` agreeing with the action of `P` along `α` is `transferBil`. -/
theorem transferBil_eq
    (β : ∀ n i, Stacks.BilinearMap (S n).val (A.piece i).val (S (n + i)).val)
    (hβ : ∀ (n i : ℤ) (U : Cᵒᵖ) (x : (P.piece n).obj U) (y : (A.piece i).val.obj U),
      (β n i).app U ((α n).app U x) y = (α (n + i)).app U ((P.smulBil n i).app U x y))
    (n i : ℤ) : β n i = P.transferBil S α n i :=
  Stacks.BilinearMap.compLeft_injective (S (n + i)).isSheaf.isSeparated (α n) (by
    refine Stacks.BilinearMap.ext fun U x y => ?_
    rw [Stacks.BilinearMap.compLeft_app, Stacks.BilinearMap.compLeft_app, hβ,
      P.transferBil_app])

/-- A degreewise family of morphisms out of a transported graded module is a homomorphism of
graded modules as soon as it is compatible with the presheaf-level action. -/
theorem hom_map_smul (T : GradedModule.{t, a, m} A) (g : ∀ n, S n ⟶ T.piece n)
    (h : ∀ (n i : ℤ) (U : Cᵒᵖ) (x : (P.piece n).obj U) (y : (A.piece i).val.obj U),
      (g (n + i)).val.app U ((α (n + i)).app U ((P.smulBil n i).app U x y))
        = T.smul n i U ((g n).val.app U ((α n).app U x)) y)
    (n i : ℤ) (U : Cᵒᵖ) (x : (S n).val.obj U) (y : (A.piece i).val.obj U) :
    (g (n + i)).val.app U ((P.transfer S α).smul n i U x y)
      = T.smul n i U ((g n).val.app U x) y := by
  refine Stacks.BilinearMap.app_eq_of_isLocallySurjective
    (T.piece (n + i)).isSheaf.isSeparated (α n)
    ((P.transferBil S α n i).postcomp (g (n + i)).val)
    ((T.smulBil n i).compLeft (g n).val) ?_ U x y
  intro V p y'
  rw [Stacks.BilinearMap.postcomp_app, Stacks.BilinearMap.compLeft_app,
    P.transferBil_app]
  exact h n i V p y'

end PreGradedModule

end SheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

namespace PreGradedModule

variable {A : GradedAlgebra.{t, a} R} (P : PreGradedModule.{t, a, m} A)

section HomEquiv

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] (S : ℤ → SheafOfModules.{m} R)
  (α : ∀ n, P.piece n ⟶ (S n).val)
  [∀ n, PresheafOfModules.IsLocallySurjective J (α n)]
  [∀ n, PresheafOfModules.IsLocallyInjective J (α n)]

/-- **The universal property of a degreewise local bijection.** Morphisms of sheaves of modules
out of a transported homogeneous piece are the same as morphisms of presheaves of modules out of
the piece it is transported from. -/
noncomputable def transferHomEquiv (n : ℤ) (T : SheafOfModules.{m} R) :
    (S n ⟶ T) ≃ (P.piece n ⟶ T.val) :=
  (fullyFaithfulForget R).homEquiv.trans
    (PresheafOfModules.homEquivOfIsLocallyBijective (f := α n) T.isSheaf)

@[simp]
theorem transferHomEquiv_apply (n : ℤ) (T : SheafOfModules.{m} R) (φ : S n ⟶ T) :
    P.transferHomEquiv S α n T φ = α n ≫ φ.val := rfl

theorem transferHomEquiv_symm_apply (n : ℤ) (T : SheafOfModules.{m} R)
    (ψ : P.piece n ⟶ T.val) :
    α n ≫ ((P.transferHomEquiv S α n T).symm ψ).val = ψ :=
  (P.transferHomEquiv S α n T).apply_symm_apply ψ

theorem hom_ext_of_comp (n : ℤ) (T : SheafOfModules.{m} R) {φ ψ : S n ⟶ T}
    (h : α n ≫ φ.val = α n ≫ ψ.val) : φ = ψ :=
  (P.transferHomEquiv S α n T).injective h

end HomEquiv

section Sheafify

variable [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- The degreewise sheafification of a presheaf-level graded module. -/
noncomputable def sheafifyPiece (n : ℤ) : SheafOfModules.{m} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj (P.piece n)

/-- The canonical map from a homogeneous piece to its sheafification. -/
noncomputable def toSheafifyPiece (n : ℤ) : P.piece n ⟶ (P.sheafifyPiece n).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app (P.piece n)

theorem toPresheaf_map_toSheafifyPiece (n : ℤ) :
    (PresheafOfModules.toPresheaf R.obj).map (P.toSheafifyPiece n)
      = CategoryTheory.toSheafify J (P.piece n).presheaf := rfl

instance (n : ℤ) : PresheafOfModules.IsLocallySurjective J (P.toSheafifyPiece n) := by
  have : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map
      (P.toSheafifyPiece n)) := by
    rw [P.toPresheaf_map_toSheafifyPiece n]
    exact (J.W_toSheafify (P.piece n).presheaf).isLocallySurjective
  exact this

instance (n : ℤ) : PresheafOfModules.IsLocallyInjective J (P.toSheafifyPiece n) := by
  have : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R.obj).map
      (P.toSheafifyPiece n)) := by
    rw [P.toPresheaf_map_toSheafifyPiece n]
    exact (J.W_toSheafify (P.piece n).presheaf).isLocallyInjective
  exact this

/-- **The sheafification of a presheaf-level graded module**: the degreewise sheafification of
its pieces, with the unique action for which the sheafification maps are compatible. -/
noncomputable def sheafify : GradedModule.{t, a, m} A :=
  P.transfer P.sheafifyPiece P.toSheafifyPiece

@[simp]
theorem sheafify_piece (n : ℤ) : P.sheafify.piece n = P.sheafifyPiece n := rfl

theorem sheafify_smul (n i : ℤ) (U : Cᵒᵖ) (x : (P.piece n).obj U)
    (y : (A.piece i).val.obj U) :
    P.sheafify.smul n i U ((P.toSheafifyPiece n).app U x) y
      = (P.toSheafifyPiece (n + i)).app U ((P.smulBil n i).app U x y) :=
  P.transferBil_app _ _ n i U x y

end Sheafify

end PreGradedModule

end SheafOfModules

/-! ### Degreewise kernels -/

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- The sectionwise kernel of a morphism of sheaves of modules, as a submodule of the source. -/
noncomputable def kerSubmodule {X Y : SheafOfModules.{m} R} (g : X ⟶ Y) : X.Submodule where
  obj U := LinearMap.ker (g.val.app U).hom
  map {U V} f x hx := by
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_comap, LinearMap.mem_ker]
    exact (Stacks.restr_app g.val f x).trans
      (by rw [hx]; exact map_zero (Y.val.map f).hom)
  isSheaf {U} s hs := by
    rw [LinearMap.mem_ker]
    refine Y.isSheaf.isSeparated U.unop _ hs _ 0 ?_
    intro V f hf
    have hf' : (g.val.app (Opposite.op V)).hom (Stacks.restr X.val f.op s) = 0 := hf
    change Stacks.restr Y.val f.op ((g.val.app U).hom s) = Stacks.restr Y.val f.op 0
    rw [← Stacks.restr_app g.val f.op s, hf']
    exact (map_zero (Y.val.map f.op).hom).symm

/-- A section lies in the sectionwise kernel exactly when the morphism kills it. -/
theorem mem_kerSubmodule {X Y : SheafOfModules.{m} R} (g : X ⟶ Y) (U : Cᵒᵖ) (x : X.val.obj U) :
    x ∈ (kerSubmodule g).obj U ↔ g.val.app U x = 0 :=
  LinearMap.mem_ker

/-- The kernel of a morphism of sheaves of modules, as a sheaf of modules. -/
noncomputable def kerObj {X Y : SheafOfModules.{m} R} (g : X ⟶ Y) : SheafOfModules.{m} R :=
  (kerSubmodule g).toSheafOfModules

/-- The inclusion of the kernel of a morphism of sheaves of modules into its source. -/
noncomputable def kerIota {X Y : SheafOfModules.{m} R} (g : X ⟶ Y) : kerObj g ⟶ X :=
  (kerSubmodule g).ι

/-- The inclusion of the kernel is a monomorphism: it is sectionwise injective. -/
instance mono_kerIota {X Y : SheafOfModules.{m} R} (g : X ⟶ Y) : Mono (kerIota g) :=
  inferInstanceAs (Mono (kerSubmodule g).ι)

/-- The inclusion of the kernel is, on sections, the inclusion of a submodule. -/
@[simp]
theorem kerIota_val_app {X Y : SheafOfModules.{m} R} (g : X ⟶ Y) (U : Cᵒᵖ)
    (z : (kerObj g).val.obj U) : (kerIota g).val.app U z = z.val := rfl

/-- The inclusion of the kernel is annihilated by the morphism. -/
theorem kerIota_comp {X Y : SheafOfModules.{m} R} (g : X ⟶ Y) : kerIota g ≫ g = 0 := by
  ext U z
  exact z.2

/-- The factorization of a morphism annihilated by `g` through the kernel of `g`. -/
noncomputable def kerLift {X Y Z : SheafOfModules.{m} R} {g : X ⟶ Y} (h : Z ⟶ X)
    (hh : h ≫ g = 0) : Z ⟶ kerObj g :=
  ⟨{ app := fun U ↦ ModuleCat.ofHom (LinearMap.codRestrict _ (h.val.app U).hom
       (fun z ↦ ConcreteCategory.congr_hom (congrArg (fun φ : Z ⟶ Y ↦ φ.val.app U) hh) z))
     naturality := fun {U V} f ↦ by
       ext z
       exact Subtype.ext (Stacks.restr_app h.val f z) }⟩

/-- On sections, the factorization through the kernel is the given morphism. -/
@[simp]
theorem kerLift_val_app {X Y Z : SheafOfModules.{m} R} {g : X ⟶ Y} (h : Z ⟶ X)
    (hh : h ≫ g = 0) (U : Cᵒᵖ) (z : Z.val.obj U) :
    ((kerLift h hh).val.app U z).val = h.val.app U z := rfl

/-- The factorization through the kernel does factor the given morphism. -/
theorem kerLift_comp {X Y Z : SheafOfModules.{m} R} {g : X ⟶ Y} (h : Z ⟶ X)
    (hh : h ≫ g = 0) : kerLift h hh ≫ kerIota g = h := by
  ext U z
  rfl

/-- The sectionwise kernel is a kernel in the category of sheaves of modules. -/
noncomputable def kerIsLimit {X Y : SheafOfModules.{m} R} (g : X ⟶ Y) :
    IsLimit (KernelFork.ofι (kerIota g) (kerIota_comp g)) :=
  KernelFork.IsLimit.ofι _ _ (fun h hh ↦ kerLift h hh) (fun h hh ↦ kerLift_comp h hh)
    (fun h hh m hm ↦ by rw [← cancel_mono (kerIota g), hm, kerLift_comp])

namespace GradedModule

variable {A : GradedAlgebra.{t, a} R}

/-- The action of the graded algebra on a section of the degree-`n` kernel lands in the
degree-`n + i` kernel. -/
theorem smul_mem_ker {M N : GradedModule.{t, a, m} A} (f : M ⟶ N) (n i : ℤ) (U : Cᵒᵖ)
    (x : (kerObj (f.app n)).val.obj U) (y : (A.piece i).val.obj U) :
    M.smul n i U x.val y ∈ (kerSubmodule (f.app (n + i))).obj U := by
  rw [mem_kerSubmodule, f.map_smul,
    (mem_kerSubmodule (f.app n) U x.val).mp x.2, map_zero, AddMonoidHom.zero_apply]

/-- The degreewise kernel of a homomorphism of graded modules, with the restricted action. -/
noncomputable def ker {M N : GradedModule.{t, a, m} A} (f : M ⟶ N) :
    GradedModule.{t, a, m} A where
  piece n := kerObj (f.app n)
  smul n i U := AddMonoidHom.mk'
    (fun x ↦ AddMonoidHom.mk' (fun y ↦ ⟨M.smul n i U x.val y, smul_mem_ker f n i U x y⟩)
      (fun y y' ↦ Subtype.ext (map_add (M.smul n i U x.val) y y')))
    (fun x x' ↦ AddMonoidHom.ext fun y ↦ Subtype.ext
      (congrArg (fun q : (A.piece i).val.obj U →+ (M.piece (n + i)).val.obj U ↦ q y)
        (map_add (M.smul n i U) x.val x'.val)))
  smul_smul_left n i U r x y := Subtype.ext (M.smul_smul_left n i U r x.val y)
  smul_smul_right n i U r x y := Subtype.ext (M.smul_smul_right n i U r x.val y)
  smul_naturality n i {_ _} g x y := Subtype.ext (M.smul_naturality n i g x.val y)
  smul_mul n i j U x y z := by
    refine Stacks.heq_of_degCast_eq
      (F := fun k ↦ ((kerObj (f.app k)).val.obj U : Type m)) (add_assoc n i j) ?_
    refine Subtype.ext ?_
    refine (Stacks.degCast_map (F := fun k ↦ ((kerObj (f.app k)).val.obj U : Type m))
      (G := fun k ↦ ((M.piece k).val.obj U : Type m)) (fun _ w ↦ w.val)
      (add_assoc n i j) _).symm.trans ?_
    exact Stacks.degCast_eq_of_heq _ (M.smul_mul n i j U x.val y z)
  smul_one n U x := by
    refine Stacks.heq_of_degCast_eq
      (F := fun k ↦ ((kerObj (f.app k)).val.obj U : Type m)) (add_zero n) ?_
    refine Subtype.ext ?_
    refine (Stacks.degCast_map (F := fun k ↦ ((kerObj (f.app k)).val.obj U : Type m))
      (G := fun k ↦ ((M.piece k).val.obj U : Type m)) (fun _ w ↦ w.val)
      (add_zero n) _).symm.trans ?_
    exact Stacks.degCast_eq_of_heq _ (M.smul_one n U x.val)

/-- The inclusion of the degreewise kernel into the source. -/
noncomputable def kerι {M N : GradedModule.{t, a, m} A} (f : M ⟶ N) : ker f ⟶ M where
  app n := kerIota (f.app n)
  map_smul _ _ _ _ _ := rfl

/-- The inclusion of the degreewise kernel is annihilated by the homomorphism. -/
theorem kerι_comp {M N : GradedModule.{t, a, m} A} (f : M ⟶ N) : kerι f ≫ f = 0 :=
  Hom.ext fun n ↦ kerIota_comp (f.app n)

/-- A homomorphism of graded modules annihilated by `f` is annihilated by `f` in every
degree. -/
theorem comp_eq_zero_app {M N P : GradedModule.{t, a, m} A} {f : M ⟶ N} {h : P ⟶ M}
    (hh : h ≫ f = 0) (n : ℤ) : h.app n ≫ f.app n = 0 :=
  congrArg (fun φ : P ⟶ N ↦ φ.app n) hh

/-- The degreewise kernel is a kernel in the category of graded modules. -/
noncomputable def kerIsLimit {M N : GradedModule.{t, a, m} A} (f : M ⟶ N) :
    IsLimit (KernelFork.ofι (kerι f) (kerι_comp f)) :=
  KernelFork.IsLimit.ofι _ _
    (fun h hh ↦
      { app := fun n ↦ kerLift (h.app n) (comp_eq_zero_app hh n)
        map_smul := fun n i U x y ↦ Subtype.ext (h.map_smul n i U x y) })
    (fun h hh ↦ Hom.ext fun n ↦ kerLift_comp (h.app n) (comp_eq_zero_app hh n))
    (fun h hh _m hm ↦ Hom.ext fun n ↦ (cancel_mono (kerIota (f.app n))).mp
      ((congrArg (fun φ : _ ⟶ M ↦ φ.app n) hm).trans
        (kerLift_comp (h.app n) (comp_eq_zero_app hh n)).symm))

/-- Graded modules over a sheaf of graded algebras have kernels, formed degreewise. -/
instance hasKernels : HasKernels (GradedModule.{t, a, m} A) where
  has_limit f := ⟨⟨⟨_, kerIsLimit f⟩⟩⟩

/-- Taking a fixed homogeneous component preserves kernels: the degreewise kernel fork of a
homomorphism of graded modules is sent to the kernel fork of its degree-`n` component. -/
instance pieceFunctor_preservesKernel {M N : GradedModule.{t, a, m} A} (f : M ⟶ N) (n : ℤ) :
    PreservesLimit (parallelPair f 0) (pieceFunctor.{t, a, m} A n) := by
  refine preservesLimit_of_preserves_limit_cone (kerIsLimit f) ?_
  exact (isLimitMapConeForkEquiv' (pieceFunctor.{t, a, m} A n) (kerι_comp f)).symm
    (_root_.SheafOfModules.kerIsLimit (f.app n))

end GradedModule

end SheafOfModules

/-! ### Degreewise cokernels -/

namespace Stacks

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{t}}
variable {X Y : PresheafOfModules.{m} R} (g : X ⟶ Y)

/-- The sectionwise image of a morphism of presheaves of modules. -/
def imgSub (U : Cᵒᵖ) : Submodule (R.obj U) (Y.obj U) :=
  LinearMap.range (g.app U).hom

theorem mem_imgSub {U : Cᵒᵖ} (x : X.obj U) : (g.app U) x ∈ imgSub g U := ⟨x, rfl⟩

/-- The restriction maps of the sectionwise quotient by the image of `g`. -/
noncomputable def quotMap {U V : Cᵒᵖ} (f : U ⟶ V) :
    (Y.obj U ⧸ imgSub g U) →ₗ[R.obj U]
      ((ModuleCat.restrictScalars (R.map f).hom).obj
        (ModuleCat.of (R.obj V) (Y.obj V ⧸ imgSub g V))) :=
  Submodule.liftQ _ (Y.map f ≫
      (ModuleCat.restrictScalars (R.map f).hom).map
        (ModuleCat.ofHom (Submodule.mkQ (imgSub g V)))).hom (by
    rintro y ⟨x, rfl⟩
    have h : (g.app V).hom (X.map f x) = Y.map f (g.app U x) :=
      PresheafOfModules.naturality_apply g f x
    simp only [LinearMap.mem_ker]
    change (Submodule.mkQ (imgSub g V)) (Y.map f (g.app U x)) = 0
    rw [← h, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨X.map f x, rfl⟩)

/-- The sectionwise quotient of a presheaf of modules by the image of a morphism. This is the
presheaf-level cokernel of `g`; the cokernel of sheaves of modules is its sheafification. -/
noncomputable def quotPresheaf : PresheafOfModules.{m} R where
  obj U := ModuleCat.of (R.obj U) (Y.obj U ⧸ imgSub g U)
  map {U V} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
      (ModuleCat.of (R.obj V) (Y.obj V ⧸ imgSub g V))) (quotMap g f)
  map_id U := by
    apply ModuleCat.hom_ext
    refine Submodule.linearMap_qext _ ?_
    apply LinearMap.ext
    intro y
    simp [quotMap]
    rfl
  map_comp {U V W} f₁ f₂ := by
    apply ModuleCat.hom_ext
    refine Submodule.linearMap_qext _ ?_
    apply LinearMap.ext
    intro y
    simp [quotMap]
    rfl

/-- The projection of a presheaf of modules onto the quotient by the image of `g`. -/
noncomputable def quotπ : Y ⟶ quotPresheaf g where
  app U := ModuleCat.ofHom (Y := (quotPresheaf g).obj U) (Submodule.mkQ (imgSub g U))
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    rfl

theorem quotπ_surjective (U : Cᵒᵖ) : Function.Surjective ((quotπ g).app U) := by
  intro q
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (imgSub g U) q
  exact ⟨y, rfl⟩

theorem quotπ_eq_zero_iff {U : Cᵒᵖ} (y : Y.obj U) :
    (quotπ g).app U y = 0 ↔ y ∈ imgSub g U :=
  Submodule.Quotient.mk_eq_zero (imgSub g U)

@[simp]
theorem quotπ_app_comp_apply {U : Cᵒᵖ} (x : X.obj U) : (quotπ g).app U ((g.app U) x) = 0 :=
  (quotπ_eq_zero_iff g _).2 (mem_imgSub g x)

@[simp]
theorem restr_quotπ {U V : Cᵒᵖ} (f : U ⟶ V) (y : Y.obj U) :
    restr (quotPresheaf g) f ((quotπ g).app U y) = (quotπ g).app V (restr Y f y) :=
  (restr_app (quotπ g) f y).symm

theorem comp_quotπ : g ≫ quotπ g = 0 := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact quotπ_app_comp_apply g x

/-- A morphism of presheaves of modules killed by `g` descends to the quotient. -/
noncomputable def quotDesc {T : PresheafOfModules.{m} R} (φ : Y ⟶ T) (hφ : g ≫ φ = 0) :
    quotPresheaf g ⟶ T where
  app U := ModuleCat.ofHom (X := (quotPresheaf g).obj U) (Y := T.obj U)
    (Submodule.liftQ (imgSub g U) (φ.app U).hom (by
      rintro y ⟨x, rfl⟩
      simp only [LinearMap.mem_ker]
      exact DFunLike.congr_fun (congrArg (fun ψ : X ⟶ T => (ψ.app U).hom) hφ) x))
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    refine Submodule.linearMap_qext _ ?_
    apply LinearMap.ext
    intro y
    exact PresheafOfModules.naturality_apply φ f y

@[simp]
theorem quotDesc_app {T : PresheafOfModules.{m} R} (φ : Y ⟶ T) (hφ : g ≫ φ = 0) (U : Cᵒᵖ)
    (y : Y.obj U) :
    (quotDesc g φ hφ).app U ((quotπ g).app U y) = φ.app U y := rfl

theorem quotπ_comp_quotDesc {T : PresheafOfModules.{m} R} (φ : Y ⟶ T) (hφ : g ≫ φ = 0) :
    quotπ g ≫ quotDesc g φ hφ = φ := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rfl

theorem quot_hom_ext {T : PresheafOfModules.{m} R} {ψ₁ ψ₂ : quotPresheaf g ⟶ T}
    (h : quotπ g ≫ ψ₁ = quotπ g ≫ ψ₂) : ψ₁ = ψ₂ := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  obtain ⟨y, rfl⟩ := quotπ_surjective g U q
  exact DFunLike.congr_fun (congrArg (fun ψ : Y ⟶ T => (ψ.app U).hom) h) y

/-- A bilinear map out of `Y` which is killed by `g` in the first variable descends to the
quotient of `Y` by the image of `g`. -/
noncomputable def BilinearMap.quotDescBil {N : PresheafOfModules.{a} R}
    {P : PresheafOfModules.{w} R} (β : BilinearMap Y N P)
    (hβ : ∀ (U : Cᵒᵖ) (x : X.obj U) (y : N.obj U), β.app U ((g.app U) x) y = 0) :
    BilinearMap (quotPresheaf g) N P where
  app U := QuotientAddGroup.lift (imgSub g U).toAddSubgroup (β.app U) (by
    rintro z ⟨x, rfl⟩
    ext y
    exact hβ U x y)
  map_smul_left U r q y := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (imgSub g U) q
    exact β.map_smul_left U r z y
  map_smul_right U r q y := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (imgSub g U) q
    exact β.map_smul_right U r z y
  naturality {U V} f q y := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (imgSub g U) q
    exact β.naturality f z y

@[simp]
theorem BilinearMap.quotDescBil_app {N : PresheafOfModules.{a} R}
    {P : PresheafOfModules.{w} R} (β : BilinearMap Y N P)
    (hβ : ∀ (U : Cᵒᵖ) (x : X.obj U) (y : N.obj U), β.app U ((g.app U) x) y = 0) (U : Cᵒᵖ)
    (z : Y.obj U) (y : N.obj U) :
    (BilinearMap.quotDescBil g β hβ).app U ((quotπ g).app U z) y = β.app U z y := rfl

end Stacks

namespace SheafOfModules

namespace GradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
variable {A : GradedAlgebra.{t, a} R} {M N : GradedModule.{t, a, m} A} (f : M ⟶ N)

/-- The presheaf-level cokernel of a morphism of graded modules: the degreewise sectionwise
quotient by the image, with the action induced from the target. -/
noncomputable def preCoker : PreGradedModule.{t, a, m} A where
  piece n := Stacks.quotPresheaf (f.app n).val
  smulBil n i := Stacks.BilinearMap.quotDescBil (f.app n).val
    ((N.smulBil n i).postcomp (Stacks.quotπ (f.app (n + i)).val)) (by
      intro U x y
      rw [Stacks.BilinearMap.postcomp_app, GradedModule.smulBil_app, ← f.map_smul]
      exact Stacks.quotπ_app_comp_apply _ _)
  smulBil_assoc n i j U x y z := by
    obtain ⟨x, rfl⟩ := Stacks.quotπ_surjective (f.app n).val U x
    rw [Stacks.BilinearMap.quotDescBil_app, Stacks.BilinearMap.postcomp_app,
      Stacks.BilinearMap.quotDescBil_app, Stacks.BilinearMap.postcomp_app,
      Stacks.BilinearMap.quotDescBil_app, Stacks.BilinearMap.postcomp_app,
      Stacks.degCast_map
        (fun k (w : (N.piece k).val.obj U) ↦ (Stacks.quotπ (f.app k).val).app U w)]
    exact congrArg _ (Stacks.degCast_eq_of_heq _ (N.smul_mul n i j U x y z))
  smulBil_one n U x := by
    obtain ⟨x, rfl⟩ := Stacks.quotπ_surjective (f.app n).val U x
    rw [Stacks.BilinearMap.quotDescBil_app, Stacks.BilinearMap.postcomp_app,
      Stacks.degCast_map
        (fun k (w : (N.piece k).val.obj U) ↦ (Stacks.quotπ (f.app k).val).app U w)]
    exact congrArg _ (Stacks.degCast_eq_of_heq _ (N.smul_one n U x))

@[simp]
theorem preCoker_smulBil_quotπ (n i : ℤ) (U : Cᵒᵖ) (x : (N.piece n).val.obj U)
    (y : (A.piece i).val.obj U) :
    ((preCoker f).smulBil n i).app U ((Stacks.quotπ (f.app n).val).app U x) y
      = (Stacks.quotπ (f.app (n + i)).val).app U (N.smul n i U x y) := rfl

end GradedModule

end SheafOfModules

namespace SheafOfModules

/-- Equal morphisms of sheaves of modules agree on every section. -/
private theorem val_app_congr {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{t}} {X Y : SheafOfModules.{m} R} {φ ψ : X ⟶ Y} (h : φ = ψ) (U : Cᵒᵖ)
    (x : X.val.obj U) : φ.val.app U x = ψ.val.app U x :=
  congrArg (fun ρ : X ⟶ Y ↦ ρ.val.app U x) h

namespace GradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
variable {A : GradedAlgebra.{t, a} R} {M N : GradedModule.{t, a, m} A} (f : M ⟶ N)
variable [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **The cokernel of a morphism of graded modules**, formed degreewise: in each degree it is
the sheafification of the sectionwise quotient by the image. -/
noncomputable def coker : GradedModule.{t, a, m} A := (preCoker f).sheafify

/-- The canonical projection onto the degreewise cokernel. -/
noncomputable def cokerπ : N ⟶ coker f where
  app n := ⟨Stacks.quotπ (f.app n).val ≫ (preCoker f).toSheafifyPiece n⟩
  map_smul n i U x y := by
    have h := (preCoker f).sheafify_smul n i U ((Stacks.quotπ (f.app n).val).app U x) y
    rw [preCoker_smulBil_quotπ] at h
    exact h.symm

@[simp]
theorem cokerπ_app_val_app (n : ℤ) (U : Cᵒᵖ) (x : (N.piece n).val.obj U) :
    ((cokerπ f).app n).val.app U x
      = ((preCoker f).toSheafifyPiece n).app U ((Stacks.quotπ (f.app n).val).app U x) := rfl

theorem cokerπ_comp : f ≫ cokerπ f = 0 := by
  refine GradedModule.Hom.ext fun n => SheafOfModules.hom_ext ?_
  have h1 : (f.app n).val ≫ Stacks.quotπ (f.app n).val = 0 := Stacks.comp_quotπ (f.app n).val
  have h2 : ((f.app n).val ≫ Stacks.quotπ (f.app n).val) ≫
      (preCoker f).toSheafifyPiece n = 0 := by
    rw [h1]
    exact Limits.zero_comp
  exact (Category.assoc _ _ _).symm.trans h2

theorem cokerπ_app_comp (n : ℤ) : f.app n ≫ (cokerπ f).app n = 0 :=
  comp_eq_zero_app (cokerπ_comp f) n

/-- The descent of a morphism out of the degree-`n` piece of `N` killed by `f.app n` to the
degree-`n` piece of the cokernel. -/
noncomputable def cokerPieceDesc {T : SheafOfModules.{m} R} (n : ℤ) (φ : N.piece n ⟶ T)
    (hφ : f.app n ≫ φ = 0) : (coker f).piece n ⟶ T :=
  ((preCoker f).transferHomEquiv (preCoker f).sheafifyPiece
    (preCoker f).toSheafifyPiece n T).symm
      (Stacks.quotDesc (f.app n).val φ.val (PresheafOfModules.hom_ext fun U =>
        congrArg (fun ψ : M.piece n ⟶ T => ψ.val.app U) hφ))

theorem toSheafifyPiece_comp_cokerPieceDesc {T : SheafOfModules.{m} R} (n : ℤ)
    (φ : N.piece n ⟶ T) (hφ : f.app n ≫ φ = 0) :
    (preCoker f).toSheafifyPiece n ≫ (cokerPieceDesc f n φ hφ).val
      = Stacks.quotDesc (f.app n).val φ.val (PresheafOfModules.hom_ext fun U =>
          congrArg (fun ψ : M.piece n ⟶ T => ψ.val.app U) hφ) :=
  (preCoker f).transferHomEquiv_symm_apply (preCoker f).sheafifyPiece
    (preCoker f).toSheafifyPiece n T _

theorem cokerπ_app_comp_cokerPieceDesc {T : SheafOfModules.{m} R} (n : ℤ)
    (φ : N.piece n ⟶ T) (hφ : f.app n ≫ φ = 0) :
    (cokerπ f).app n ≫ cokerPieceDesc f n φ hφ = φ := by
  refine SheafOfModules.hom_ext ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans (congrArg (fun ψ : Stacks.quotPresheaf (f.app n).val ⟶ T.val =>
    Stacks.quotπ (f.app n).val ≫ ψ) (toSheafifyPiece_comp_cokerPieceDesc f n φ hφ)) ?_
  exact Stacks.quotπ_comp_quotDesc _ _ _

theorem cokerPiece_hom_ext {T : SheafOfModules.{m} R} (n : ℤ)
    {ψ₁ ψ₂ : (coker f).piece n ⟶ T} (h : (cokerπ f).app n ≫ ψ₁ = (cokerπ f).app n ≫ ψ₂) :
    ψ₁ = ψ₂ := by
  refine (preCoker f).hom_ext_of_comp (preCoker f).sheafifyPiece
    (preCoker f).toSheafifyPiece n T (Stacks.quot_hom_ext (f.app n).val ?_)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact congrArg (fun φ : N.piece n ⟶ T => φ.val) h

/-- Each homogeneous piece of the degreewise cokernel is a cokernel of the corresponding piece
of `f` in the category of sheaves of modules. -/
noncomputable def cokerPieceIsColimit (n : ℤ) :
    IsColimit (CokernelCofork.ofπ ((cokerπ f).app n) (cokerπ_app_comp f n)) :=
  CokernelCofork.IsColimit.ofπ _ _ (fun {_} φ hφ => cokerPieceDesc f n φ hφ)
    (fun {_} φ hφ => cokerπ_app_comp_cokerPieceDesc f n φ hφ)
    (fun {_} φ hφ _ψ hψ => cokerPiece_hom_ext f n
      (hψ.trans (cokerπ_app_comp_cokerPieceDesc f n φ hφ).symm))

/-- On a section coming from the target, the descent to the cokernel piece is the given
morphism. -/
theorem cokerPieceDesc_toSheafifyPiece_quotπ {T : SheafOfModules.{m} R} (n : ℤ)
    (φ : N.piece n ⟶ T) (hφ : f.app n ≫ φ = 0) (U : Cᵒᵖ) (z : (N.piece n).val.obj U) :
    (cokerPieceDesc f n φ hφ).val.app U
        (((preCoker f).toSheafifyPiece n).app U ((Stacks.quotπ (f.app n).val).app U z))
      = φ.val.app U z :=
  val_app_congr (cokerπ_app_comp_cokerPieceDesc f n φ hφ) U z

/-- The descent of a homomorphism of graded modules killed by `f` to the degreewise cokernel. -/
noncomputable def cokerDesc {T : GradedModule.{t, a, m} A} (φ : N ⟶ T) (hφ : f ≫ φ = 0) :
    coker f ⟶ T where
  app n := cokerPieceDesc f n (φ.app n) (congrArg (fun ψ : M ⟶ T => ψ.app n) hφ)
  map_smul n i U x y := by
    refine (preCoker f).hom_map_smul (preCoker f).sheafifyPiece (preCoker f).toSheafifyPiece T
      (fun n' => cokerPieceDesc f n' (φ.app n') (congrArg (fun ψ : M ⟶ T => ψ.app n') hφ))
      (fun n' i' V q y' => ?_) n i U x y
    obtain ⟨z, rfl⟩ := Stacks.quotπ_surjective (f.app n').val V q
    have e1 := cokerPieceDesc_toSheafifyPiece_quotπ f (n' + i') (φ.app (n' + i'))
      (congrArg (fun ψ : M ⟶ T => ψ.app (n' + i')) hφ) V (N.smul n' i' V z y')
    have e2 := cokerPieceDesc_toSheafifyPiece_quotπ f n' (φ.app n')
      (congrArg (fun ψ : M ⟶ T => ψ.app n') hφ) V z
    rw [preCoker_smulBil_quotπ]
    exact e1.trans ((φ.map_smul n' i' V z y').trans
      (congrArg (fun w : (T.piece n').val.obj V => T.smul n' i' V w y') e2.symm))

theorem cokerπ_comp_cokerDesc {T : GradedModule.{t, a, m} A} (φ : N ⟶ T) (hφ : f ≫ φ = 0) :
    cokerπ f ≫ cokerDesc f φ hφ = φ :=
  GradedModule.Hom.ext fun n =>
    cokerπ_app_comp_cokerPieceDesc f n (φ.app n) (comp_eq_zero_app hφ n)

theorem coker_hom_ext {T : GradedModule.{t, a, m} A} {ψ₁ ψ₂ : coker f ⟶ T}
    (h : cokerπ f ≫ ψ₁ = cokerπ f ≫ ψ₂) : ψ₁ = ψ₂ :=
  GradedModule.Hom.ext fun n =>
    cokerPiece_hom_ext f n (congrArg (fun φ : N ⟶ T => φ.app n) h)

/-- **The degreewise cokernel is a cokernel in the category of graded modules.** -/
noncomputable def cokerIsColimit :
    IsColimit (CokernelCofork.ofπ (cokerπ f) (cokerπ_comp f)) :=
  CokernelCofork.IsColimit.ofπ _ _ (fun {_} φ hφ => cokerDesc f φ hφ)
    (fun {_} φ hφ => cokerπ_comp_cokerDesc f φ hφ)
    (fun {_} φ hφ _ψ hψ => coker_hom_ext f (hψ.trans (cokerπ_comp_cokerDesc f φ hφ).symm))

/-- Graded modules over a sheaf of graded algebras have cokernels, formed degreewise. -/
instance hasCokernels : HasCokernels (GradedModule.{t, a, m} A) where
  has_colimit g := ⟨⟨⟨_, cokerIsColimit g⟩⟩⟩

/-- Taking a fixed homogeneous component preserves cokernels: the degreewise cokernel cofork of
a homomorphism of graded modules is sent to the cokernel cofork of its degree-`n` component. -/
instance pieceFunctor_preservesCokernel (n : ℤ) :
    PreservesColimit (parallelPair f 0) (pieceFunctor.{t, a, m} A n) := by
  refine preservesColimit_of_preserves_colimit_cocone (cokerIsColimit f) ?_
  exact (isColimitMapCoconeCoforkEquiv' (pieceFunctor.{t, a, m} A n) (cokerπ_comp f)).symm
    (cokerPieceIsColimit f n)

end GradedModule

end SheafOfModules

/-! ### Componentwise isomorphisms and the coimage-image comparison -/

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- Applying the inverse of an isomorphism of sheaves of modules to a section. -/
theorem inv_val_app_val_app {X Y : SheafOfModules.{m} R} (φ : X ⟶ Y) [IsIso φ] (U : Cᵒᵖ)
    (x : X.val.obj U) : (inv φ).val.app U (φ.val.app U x) = x :=
  val_app_congr (IsIso.hom_inv_id φ) U x

/-- Applying an isomorphism of sheaves of modules to a section of the inverse image. -/
theorem val_app_inv_val_app {X Y : SheafOfModules.{m} R} (φ : X ⟶ Y) [IsIso φ] (U : Cᵒᵖ)
    (y : Y.val.obj U) : φ.val.app U ((inv φ).val.app U y) = y :=
  val_app_congr (IsIso.inv_hom_id φ) U y

namespace GradedModule

variable {A : GradedAlgebra.{t, a} R}

/-- The degreewise inverse of a homomorphism of graded modules all of whose homogeneous
components are isomorphisms. -/
noncomputable def homInv {M N : GradedModule.{t, a, m} A} (f : M ⟶ N)
    (hf : ∀ n, IsIso (f.app n)) : N ⟶ M where
  app n := haveI := hf n; inv (f.app n)
  map_smul n i U y b := by
    have := hf n
    have := hf (n + i)
    calc (inv (f.app (n + i))).val.app U (N.smul n i U y b)
        = (inv (f.app (n + i))).val.app U ((f.app (n + i)).val.app U
            (M.smul n i U ((inv (f.app n)).val.app U y) b)) := by
          rw [f.map_smul, val_app_inv_val_app]
      _ = M.smul n i U ((inv (f.app n)).val.app U y) b := inv_val_app_val_app _ _ _

/-- A homomorphism of graded modules whose homogeneous components are all isomorphisms is an
isomorphism. -/
theorem isIso_of_componentwise {M N : GradedModule.{t, a, m} A} (f : M ⟶ N)
    (hf : ∀ n, IsIso (f.app n)) : IsIso f := by
  refine ⟨homInv f hf, Hom.ext fun n => ?_, Hom.ext fun n => ?_⟩
  · have := hf n
    exact IsIso.hom_inv_id (f.app n)
  · have := hf n
    exact IsIso.inv_hom_id (f.app n)

/-- Taking a fixed homogeneous component is an additive functor. -/
instance pieceFunctor_additive (A : GradedAlgebra.{t, a} R) (n : ℤ) :
    (pieceFunctor.{t, a, m} A n).Additive where
  map_add := rfl

section Abelian

variable [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- The coimage-image comparison of a homomorphism of graded modules is an isomorphism, because
it is one in each homogeneous degree: taking a homogeneous component preserves kernels and
cokernels, and sheaves of modules form an abelian category. -/
theorem isIso_coimageImageComparison {M N : GradedModule.{t, a, m} A} (f : M ⟶ N) :
    IsIso (Abelian.coimageImageComparison f) := by
  refine isIso_of_componentwise _ fun n => ?_
  have h := Abelian.PreservesCoimageImageComparison.iso (pieceFunctor.{t, a, m} A n) f
  change IsIso ((pieceFunctor.{t, a, m} A n).map (Abelian.coimageImageComparison f))
  rw [Arrow.isIso_iff_isIso_of_isIso h.hom]
  infer_instance

end Abelian

end GradedModule

end SheafOfModules

/-! ### The degreewise kernel and cokernel, in existential form -/

namespace SheafOfModules

namespace GradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : GradedAlgebra.{t, a} R}

/-- **Kernels of graded modules are formed degreewise.** The kernel exists, each of its
homogeneous pieces is a kernel of the corresponding piece of `f`, and it has the universal
property in the category of graded modules. -/
theorem exists_kernel_degreewise {M N : GradedModule.{t, a, m} A} (f : M ⟶ N) :
    ∃ (K : GradedModule.{t, a, m} A) (i : K ⟶ M) (hi : ∀ n : ℤ, i.app n ≫ f.app n = 0),
      (∀ n : ℤ, Nonempty (IsLimit (KernelFork.ofι (i.app n) (hi n)))) ∧
      (∀ (P : GradedModule.{t, a, m} A) (g : P ⟶ M),
        (∀ n : ℤ, g.app n ≫ f.app n = 0) → ∃! h : P ⟶ K, h ≫ i = g) := by
  refine ⟨ker f, kerι f, fun n => kerIota_comp (f.app n),
    fun n => ⟨_root_.SheafOfModules.kerIsLimit (f.app n)⟩, fun P g hg => ?_⟩
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' (kerIsLimit f) g (Hom.ext hg)
  exact ⟨l, hl, fun h hh => Fork.IsLimit.hom_ext (kerIsLimit f) (hh.trans hl.symm)⟩

variable [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **Cokernels of graded modules are formed degreewise.** The cokernel exists, each of its
homogeneous pieces is a cokernel of the corresponding piece of `f`, and it has the universal
property in the category of graded modules. -/
theorem exists_cokernel_degreewise {M N : GradedModule.{t, a, m} A} (f : M ⟶ N) :
    ∃ (Q : GradedModule.{t, a, m} A) (p : N ⟶ Q) (hp : ∀ n : ℤ, f.app n ≫ p.app n = 0),
      (∀ n : ℤ, Nonempty (IsColimit (CokernelCofork.ofπ (p.app n) (hp n)))) ∧
      (∀ (P : GradedModule.{t, a, m} A) (g : N ⟶ P),
        (∀ n : ℤ, f.app n ≫ g.app n = 0) → ∃! h : Q ⟶ P, p ≫ h = g) := by
  refine ⟨coker f, cokerπ f, cokerπ_app_comp f,
    fun n => ⟨cokerPieceIsColimit f n⟩, fun P g hg => ?_⟩
  obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' (cokerIsColimit f) g (Hom.ext hg)
  exact ⟨l, hl, fun h hh => Cofork.IsColimit.hom_ext (cokerIsColimit f) (hh.trans hl.symm)⟩

end GradedModule

end SheafOfModules

/-! ### Degreewise direct sums -/

namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- The restriction map of a presheaf of modules along an identity is the identity. -/
theorem restr_id (M : PresheafOfModules.{m} R.obj) (U : Cᵒᵖ) (x : M.obj U) :
    Stacks.restr M (𝟙 U) x = x := by
  change (M.presheaf.map (𝟙 U)) x = x
  rw [M.presheaf.map_id]
  rfl

/-- Restriction along a composite is the composite of the restrictions. -/
theorem restr_comp (M : PresheafOfModules.{m} R.obj) {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (x : M.obj U) : Stacks.restr M (f ≫ g) x = Stacks.restr M g (Stacks.restr M f x) :=
  M.map_comp_apply f g x

/-- The restriction maps of a presheaf of modules are additive. -/
theorem restr_add (M : PresheafOfModules.{m} R.obj) {U V : Cᵒᵖ} (f : U ⟶ V) (x y : M.obj U) :
    Stacks.restr M f (x + y) = Stacks.restr M f x + Stacks.restr M f y :=
  map_add (ConcreteCategory.hom (M.map f)) x y

/-- The restriction maps of a presheaf of modules are semilinear. -/
theorem restr_smul (M : PresheafOfModules.{m} R.obj) {U V : Cᵒᵖ} (f : U ⟶ V) (r : R.obj.obj U)
    (x : M.obj U) : Stacks.restr M f (r • x) = R.obj.map f r • Stacks.restr M f x :=
  M.map_smul f r x

section DirectSum

variable {ι : Type m}


/-- Classical decidable equality on an index type, at low priority, so that the sectionwise
direct sums below need no decidability hypothesis on their index type. -/
noncomputable local instance (priority := low) decidableEqIndex : DecidableEq ι :=
  Classical.decEq ι

section Presheaf

variable (X : ι → PresheafOfModules.{m} R.obj)

/-- The restriction map of the sectionwise direct sum of a family of presheaves of modules: on
the `i`-th summand it is the restriction map of `X i` followed by the `i`-th inclusion. -/
noncomputable def directSumPresheafMap {U V : Cᵒᵖ} (f : U ⟶ V) :
    ModuleCat.of (R.obj.obj U) (DirectSum ι fun j ↦ (X j).obj U) ⟶
      (ModuleCat.restrictScalars (R.obj.map f).hom).obj
        (ModuleCat.of (R.obj.obj V) (DirectSum ι fun j ↦ (X j).obj V)) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (R.obj.map f).hom).obj
      (ModuleCat.of (R.obj.obj V) (DirectSum ι fun j ↦ (X j).obj V)))
    (DirectSum.toModule (R.obj.obj U) ι _ fun i ↦
      { toFun := fun x ↦ DirectSum.lof (R.obj.obj V) ι (fun j ↦ (X j).obj V) i
          (Stacks.restr (X i) f x)
        map_add' := fun x y ↦ by rw [restr_add, map_add]; rfl
        map_smul' := fun r x ↦ by rw [restr_smul, map_smul]; rfl })

/-- The restriction map of the sectionwise direct sum, evaluated on the `i`-th summand. -/
theorem directSumPresheafMap_lof {U V : Cᵒᵖ} (f : U ⟶ V) (i : ι) (x : (X i).obj U) :
    (directSumPresheafMap X f (DirectSum.lof (R.obj.obj U) ι (fun j ↦ (X j).obj U) i x) :
        DirectSum ι fun j ↦ (X j).obj V)
      = DirectSum.lof (R.obj.obj V) ι (fun j ↦ (X j).obj V) i (Stacks.restr (X i) f x) := by
  change DirectSum.toModule (R.obj.obj U) ι _ _
      (DirectSum.lof (R.obj.obj U) ι (fun j ↦ (X j).obj U) i x) = _
  exact DirectSum.toModule_lof (R.obj.obj U) (M := fun j ↦ (X j).obj U) i x

/-- The sectionwise direct sum of a family of presheaves of modules. -/
@[sga "3 I 3.1.1" "partial"]
noncomputable def directSumPresheaf : PresheafOfModules.{m} R.obj where
  obj U := ModuleCat.of (R.obj.obj U) (DirectSum ι fun j ↦ (X j).obj U)
  map f := directSumPresheafMap X f
  map_id U := by
    refine ModuleCat.hom_ext (DirectSum.linearMap_ext _ fun i ↦ LinearMap.ext fun x ↦ ?_)
    refine (directSumPresheafMap_lof X (𝟙 U) i x).trans ?_
    rw [restr_id]
    rfl
  map_comp {U V W} f g := by
    refine ModuleCat.hom_ext (DirectSum.linearMap_ext _ fun i ↦ LinearMap.ext fun x ↦ ?_)
    have h1 : (directSumPresheafMap X f
        (DirectSum.lof (R.obj.obj U) ι (fun j ↦ (X j).obj U) i x) :
          DirectSum ι fun j ↦ (X j).obj V)
        = DirectSum.lof (R.obj.obj V) ι (fun j ↦ (X j).obj V) i (Stacks.restr (X i) f x) :=
      directSumPresheafMap_lof X f i x
    have h2 := directSumPresheafMap_lof X g i (Stacks.restr (X i) f x)
    refine (directSumPresheafMap_lof X (f ≫ g) i x).trans ?_
    rw [restr_comp]
    exact ((congrArg (fun y : DirectSum ι fun j ↦ (X j).obj V ↦
      directSumPresheafMap X g y) h1).trans h2).symm

/-- The inclusion of the `i`-th summand into the sectionwise direct sum. -/
noncomputable def directSumPresheafι (i : ι) : X i ⟶ directSumPresheaf X where
  app U := ModuleCat.ofHom (DirectSum.lof (R.obj.obj U) ι (fun j ↦ (X j).obj U) i)
  naturality {U V} f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    exact (directSumPresheafMap_lof X f i x).symm

@[simp]
theorem directSumPresheafι_app (i : ι) (U : Cᵒᵖ) (x : (X i).obj U) :
    (directSumPresheafι X i).app U x = DirectSum.of (fun j ↦ (X j).obj U) i x := rfl

/-- The restriction maps of the sectionwise direct sum, as additive maps between the direct
sums of sections. Stating them at this type, rather than at the type of sections of
`SheafOfModules.directSumPresheaf`, keeps every term below type-correct without unfolding
`SheafOfModules.directSumPresheaf`. -/
noncomputable def directSumPresheafRestr {U V : Cᵒᵖ} (f : U ⟶ V) :
    (DirectSum ι fun j ↦ (X j).obj U) →+ DirectSum ι fun j ↦ (X j).obj V :=
  AddMonoidHom.mk' (Stacks.restr (directSumPresheaf X) f) (restr_add (directSumPresheaf X) f)

/-- Restriction in the sectionwise direct sum, on the `i`-th summand. -/
@[simp]
theorem directSumPresheafRestr_of {U V : Cᵒᵖ} (f : U ⟶ V) (i : ι) (x : (X i).obj U) :
    directSumPresheafRestr X f (DirectSum.of (fun j ↦ (X j).obj U) i x)
      = DirectSum.of (fun j ↦ (X j).obj V) i (Stacks.restr (X i) f x) :=
  directSumPresheafMap_lof X f i x

variable {T : PresheafOfModules.{m} R.obj}

/-- The morphism out of a sectionwise direct sum determined by a family of morphisms out of
the summands. -/
noncomputable def directSumPresheafDesc (φ : ∀ i, X i ⟶ T) : directSumPresheaf X ⟶ T where
  app U := ModuleCat.ofHom (Y := T.obj U) (DirectSum.toModule (R.obj.obj U) ι (T.obj U)
    fun i ↦ ((φ i).app U).hom)
  naturality {U V} f := by
    refine ModuleCat.hom_ext (DirectSum.linearMap_ext _ fun i ↦ LinearMap.ext fun x ↦ ?_)
    have hU : DirectSum.toModule (R.obj.obj U) ι (T.obj U)
        (fun k ↦ ((φ k).app U).hom)
        (DirectSum.lof (R.obj.obj U) ι (fun j ↦ (X j).obj U) i x) = (φ i).app U x :=
      DirectSum.toModule_lof (R.obj.obj U) (M := fun j ↦ (X j).obj U) i x
    have hV : DirectSum.toModule (R.obj.obj V) ι (T.obj V)
        (fun k ↦ ((φ k).app V).hom)
        (DirectSum.lof (R.obj.obj V) ι (fun j ↦ (X j).obj V) i (Stacks.restr (X i) f x))
        = (φ i).app V (Stacks.restr (X i) f x) :=
      DirectSum.toModule_lof (R.obj.obj V) (M := fun j ↦ (X j).obj V) i _
    refine Eq.trans (congrArg (fun y : DirectSum ι fun j ↦ (X j).obj V ↦
      DirectSum.toModule (R.obj.obj V) ι (T.obj V)
        (fun k ↦ ((φ k).app V).hom) y)
      (directSumPresheafMap_lof X f i x)) ?_
    rw [hV, Stacks.restr_app]
    exact (congrArg (fun y : T.obj U ↦ Stacks.restr T f y) hU).symm

/-- A morphism out of a sectionwise direct sum, evaluated on the `i`-th summand. -/
@[simp]
theorem directSumPresheafDesc_app_of (φ : ∀ i, X i ⟶ T) (i : ι) (U : Cᵒᵖ)
    (x : (X i).obj U) : (directSumPresheafDesc X φ).app U
      (DirectSum.of (fun j ↦ (X j).obj U) i x) = (φ i).app U x := by
  change DirectSum.toModule (R.obj.obj U) ι (T.obj U) (fun k ↦ ((φ k).app U).hom)
      (DirectSum.lof (R.obj.obj U) ι (fun j ↦ (X j).obj U) i x) = _
  exact DirectSum.toModule_lof (R.obj.obj U) (M := fun j ↦ (X j).obj U) i x

/-- The defining property of `SheafOfModules.directSumPresheafDesc`. -/
@[reassoc (attr := simp)]
theorem directSumPresheafι_desc (φ : ∀ i, X i ⟶ T) (i : ι) :
    directSumPresheafι X i ≫ directSumPresheafDesc X φ = φ i :=
  PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦
    directSumPresheafDesc_app_of X φ i U x)

/-- Two morphisms out of a sectionwise direct sum agree as soon as they agree on every
summand. -/
theorem directSumPresheaf_hom_ext {α β : directSumPresheaf X ⟶ T}
    (h : ∀ i, directSumPresheafι X i ≫ α = directSumPresheafι X i ≫ β) : α = β :=
  PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext
    (DirectSum.linearMap_ext _ fun i ↦ LinearMap.ext fun x ↦
      congrArg (fun ψ : X i ⟶ T ↦ ψ.app U x) (h i))

end Presheaf

namespace GradedModule

variable {A : GradedAlgebra.{t, a} R} (M : ι → GradedModule.{t, a, m} A)

/-- Transport along an equality of degrees preserves zero, for a degreewise family of direct
sums of homogeneous pieces. -/
theorem degCast_dsum_zero (U : Cᵒᵖ) {n n' : ℤ} (h : n = n') :
    Stacks.degCast (F := fun l ↦ DirectSum ι fun k ↦ ((M k).piece l).val.obj U) h
      (0 : DirectSum ι fun k ↦ ((M k).piece n).val.obj U) = 0 := by
  subst h; rfl

/-- Transport along an equality of degrees is additive, for a degreewise family of direct sums
of homogeneous pieces. -/
theorem degCast_dsum_add (U : Cᵒᵖ) {n n' : ℤ} (h : n = n')
    (x y : DirectSum ι fun k ↦ ((M k).piece n).val.obj U) :
    Stacks.degCast (F := fun l ↦ DirectSum ι fun k ↦ ((M k).piece l).val.obj U) h (x + y)
      = Stacks.degCast (F := fun l ↦ DirectSum ι fun k ↦ ((M k).piece l).val.obj U) h x
        + Stacks.degCast (F := fun l ↦ DirectSum ι fun k ↦ ((M k).piece l).val.obj U) h y := by
  subst h; rfl

/-- Transport along an equality of degrees commutes with the inclusion of a summand. -/
theorem degCast_dsum_of (U : Cᵒᵖ) (k : ι) {n n' : ℤ} (h : n = n')
    (x : ((M k).piece n).val.obj U) :
    Stacks.degCast (F := fun l ↦ DirectSum ι fun k' ↦ ((M k').piece l).val.obj U) h
        (DirectSum.of (fun k' ↦ ((M k').piece n).val.obj U) k x)
      = DirectSum.of (fun k' ↦ ((M k').piece n').val.obj U) k
        (Stacks.degCast (F := fun l ↦ ((M k).piece l).val.obj U) h x) := by
  subst h; rfl

/-- Transport of a summand along an equality of degrees, when the summands are `HEq`. -/
private theorem degCast_dsum_of_eq_of_heq (U : Cᵒᵖ) (k : ι) {n n' : ℤ} (h : n = n')
    {x : ((M k).piece n).val.obj U} {y : ((M k).piece n').val.obj U} (hxy : HEq x y) :
    Stacks.degCast (F := fun l ↦ DirectSum ι fun k' ↦ ((M k').piece l).val.obj U) h
        (DirectSum.of (fun k' ↦ ((M k').piece n).val.obj U) k x)
      = DirectSum.of (fun k' ↦ ((M k').piece n').val.obj U) k y := by
  rw [degCast_dsum_of]
  exact congrArg _ (Stacks.degCast_eq_of_heq _ hxy)

/-- The action of a graded module commutes with restriction. -/
theorem smul_restr (N : GradedModule.{t, a, m} A) (n i : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : (N.piece n).val.obj U) (y : (A.piece i).val.obj U) :
    Stacks.restr (N.piece (n + i)).val f (N.smul n i U x y)
      = N.smul n i V (Stacks.restr (N.piece n).val f x) (Stacks.restr (A.piece i).val f y) :=
  N.smul_naturality n i f x y

/-- The `k`-th component of the action of the sectionwise direct sum of a family of graded
modules: act on the `k`-th summand, then include it again. -/
noncomputable def preDirectSumSmulComp (n i : ℤ) (U : Cᵒᵖ) (k : ι) :
    ((M k).piece n).val.obj U →+
      (A.piece i).val.obj U →+ DirectSum ι fun l ↦ ((M l).piece (n + i)).val.obj U :=
  (AddMonoidHom.compHom
    (DirectSum.of (fun l ↦ ((M l).piece (n + i)).val.obj U) k)).comp ((M k).smul n i U)

/-- The action of the sectionwise direct sum of a family of graded modules, on sections over
one object of the site. -/
noncomputable def preDirectSumSmulApp (n i : ℤ) (U : Cᵒᵖ) :
    (DirectSum ι fun k ↦ ((M k).piece n).val.obj U) →+
      (A.piece i).val.obj U →+ DirectSum ι fun k ↦ ((M k).piece (n + i)).val.obj U :=
  DirectSum.toAddMonoid (preDirectSumSmulComp M n i U)

/-- The action of the sectionwise direct sum, on the `k`-th summand. -/
@[simp]
theorem preDirectSumSmulApp_of (n i : ℤ) (U : Cᵒᵖ) (k : ι) (x : ((M k).piece n).val.obj U)
    (y : (A.piece i).val.obj U) :
    preDirectSumSmulApp M n i U (DirectSum.of (fun l ↦ ((M l).piece n).val.obj U) k x) y
      = DirectSum.of (fun l ↦ ((M l).piece (n + i)).val.obj U) k ((M k).smul n i U x y) :=
  congrArg
    (fun ψ : (A.piece i).val.obj U →+ DirectSum ι fun l ↦ ((M l).piece (n + i)).val.obj U ↦ ψ y)
    (DirectSum.toAddMonoid_of (preDirectSumSmulComp M n i U) k x)

/-- The action of the sectionwise direct sum is linear in the module variable. -/
theorem preDirectSumSmulApp_smul_left (n i : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U)
    (x : DirectSum ι fun k ↦ ((M k).piece n).val.obj U) (y : (A.piece i).val.obj U) :
    preDirectSumSmulApp M n i U (r • x) y = r • preDirectSumSmulApp M n i U x y := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of k x =>
    rw [← DirectSum.of_smul, preDirectSumSmulApp_of, preDirectSumSmulApp_of,
      (M k).smul_smul_left]
    exact DirectSum.of_smul _ k r _
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx', smul_add]

/-- The action of the sectionwise direct sum is linear in the algebra variable. -/
theorem preDirectSumSmulApp_smul_right (n i : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U)
    (x : DirectSum ι fun k ↦ ((M k).piece n).val.obj U) (y : (A.piece i).val.obj U) :
    preDirectSumSmulApp M n i U x (r • y) = r • preDirectSumSmulApp M n i U x y := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of k x =>
    rw [preDirectSumSmulApp_of, preDirectSumSmulApp_of, (M k).smul_smul_right]
    exact DirectSum.of_smul _ k r _
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx', smul_add]

/-- The action of the sectionwise direct sum commutes with restriction. -/
theorem preDirectSumSmulApp_restr (n i : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : DirectSum ι fun k ↦ ((M k).piece n).val.obj U) (y : (A.piece i).val.obj U) :
    directSumPresheafRestr (fun k ↦ ((M k).piece (n + i)).val) f
        (preDirectSumSmulApp M n i U x y)
      = preDirectSumSmulApp M n i V
        (directSumPresheafRestr (fun k ↦ ((M k).piece n).val) f x)
        (Stacks.restr (A.piece i).val f y) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | of k x =>
    rw [preDirectSumSmulApp_of, directSumPresheafRestr_of, directSumPresheafRestr_of,
      preDirectSumSmulApp_of, smul_restr]
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']

/-- The action of the sectionwise direct sum of a family of graded modules, as a bilinear map
of presheaves of modules. -/
noncomputable def preDirectSumSmul (n i : ℤ) :
    Stacks.BilinearMap (directSumPresheaf fun k ↦ ((M k).piece n).val) (A.piece i).val
      (directSumPresheaf fun k ↦ ((M k).piece (n + i)).val) where
  app U := preDirectSumSmulApp M n i U
  map_smul_left U r x y := preDirectSumSmulApp_smul_left M n i U r x y
  map_smul_right U r x y := preDirectSumSmulApp_smul_right M n i U r x y
  naturality f x y := preDirectSumSmulApp_restr M n i f x y

/-- The action of the sectionwise direct sum, as a bilinear map, on the `k`-th summand. -/
@[simp]
theorem preDirectSumSmul_app_of (n i : ℤ) (U : Cᵒᵖ) (k : ι) (x : ((M k).piece n).val.obj U)
    (y : (A.piece i).val.obj U) :
    (preDirectSumSmul M n i).app U (DirectSum.of (fun l ↦ ((M l).piece n).val.obj U) k x) y
      = DirectSum.of (fun l ↦ ((M l).piece (n + i)).val.obj U) k ((M k).smul n i U x y) :=
  preDirectSumSmulApp_of M n i U k x y

/-- The action of the sectionwise direct sum is associative. -/
theorem preDirectSumSmulApp_assoc (n i j : ℤ) (U : Cᵒᵖ)
    (x : DirectSum ι fun k ↦ ((M k).piece n).val.obj U) (y : (A.piece i).val.obj U)
    (z : (A.piece j).val.obj U) :
    Stacks.degCast (F := fun l ↦ DirectSum ι fun k ↦ ((M k).piece l).val.obj U)
        (add_assoc n i j)
        (preDirectSumSmulApp M (n + i) j U (preDirectSumSmulApp M n i U x y) z)
      = preDirectSumSmulApp M n (i + j) U x ((A.mul i j).app U y z) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply, degCast_dsum_zero]
  | of k x =>
    rw [preDirectSumSmulApp_of, preDirectSumSmulApp_of, preDirectSumSmulApp_of]
    exact degCast_dsum_of_eq_of_heq M U k _ ((M k).smul_mul n i j U x y z)
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, degCast_dsum_add, hx, hx']

/-- The degree-zero unit of the algebra acts as the identity on the sectionwise direct sum. -/
theorem preDirectSumSmulApp_one (n : ℤ) (U : Cᵒᵖ)
    (x : DirectSum ι fun k ↦ ((M k).piece n).val.obj U) :
    Stacks.degCast (F := fun l ↦ DirectSum ι fun k ↦ ((M k).piece l).val.obj U) (add_zero n)
      (preDirectSumSmulApp M n 0 U x (A.one.eval U)) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply, degCast_dsum_zero]
  | of k x =>
    rw [preDirectSumSmulApp_of]
    exact degCast_dsum_of_eq_of_heq M U k _ ((M k).smul_one n U x)
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, degCast_dsum_add, hx, hx']

/-- **The degreewise direct sum of a family of graded modules, before sheafifying.** Its
homogeneous piece in degree `n` is the sectionwise direct sum of the degree-`n` pieces, and the
action is the direct sum of the actions. -/
noncomputable def preDirectSum : PreGradedModule.{t, a, m} A where
  piece n := directSumPresheaf fun k ↦ ((M k).piece n).val
  smulBil n i := preDirectSumSmul M n i
  smulBil_assoc n i j U x y z := preDirectSumSmulApp_assoc M n i j U x y z
  smulBil_one n U x := preDirectSumSmulApp_one M n U x

@[simp]
theorem preDirectSum_piece (n : ℤ) :
    (preDirectSum M).piece n = directSumPresheaf fun k ↦ ((M k).piece n).val := rfl

section Sheafify

variable [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **The degreewise direct sum of a set-indexed family of graded modules**: the degreewise
sheafification of the sectionwise direct sum. -/
noncomputable def directSum : GradedModule.{t, a, m} A := (preDirectSum M).sheafify

@[simp]
theorem directSum_piece (n : ℤ) :
    (directSum M).piece n = (preDirectSum M).sheafifyPiece n := rfl

/-- The sheafification map of the degree-`n` piece of the sectionwise direct sum. Its declared
source and target are the ones every statement below needs, so that no term has to be
type-checked through the definition of `SheafOfModules.GradedModule.preDirectSum`. -/
noncomputable def toDirectSumPiece (n : ℤ) :
    directSumPresheaf (fun l ↦ ((M l).piece n).val) ⟶ ((directSum M).piece n).val :=
  (preDirectSum M).toSheafifyPiece n

/-- The inclusion of one summand into the degreewise direct sum. -/
noncomputable def directSumι (k : ι) : M k ⟶ directSum M where
  app n := ⟨directSumPresheafι (fun l ↦ ((M l).piece n).val) k ≫ toDirectSumPiece M n⟩
  map_smul n i U x y := by
    refine Eq.symm (Eq.trans ((preDirectSum M).sheafify_smul n i U
      (DirectSum.of (fun l ↦ ((M l).piece n).val.obj U) k x) y) ?_)
    exact congrArg (fun w ↦ ((preDirectSum M).toSheafifyPiece (n + i)).app U w)
      (preDirectSumSmulApp_of M n i U k x y)

@[simp]
theorem directSumι_app_val (k : ι) (n : ℤ) :
    ((directSumι M k).app n).val
      = directSumPresheafι (fun l ↦ ((M l).piece n).val) k ≫ toDirectSumPiece M n := rfl

/-- The morphism out of a homogeneous piece of the degreewise direct sum determined by a family
of morphisms out of the summands. -/
noncomputable def directSumPieceDesc (n : ℤ) (T : SheafOfModules.{m} R)
    (ψ : ∀ k, (M k).piece n ⟶ T) : (directSum M).piece n ⟶ T :=
  ((preDirectSum M).transferHomEquiv (preDirectSum M).sheafifyPiece
    (preDirectSum M).toSheafifyPiece n T).symm
    (directSumPresheafDesc (fun l ↦ ((M l).piece n).val) fun k ↦ (ψ k).val)

/-- The defining property of `SheafOfModules.GradedModule.directSumPieceDesc`. -/
theorem toDirectSumPiece_desc (n : ℤ) (T : SheafOfModules.{m} R)
    (ψ : ∀ k, (M k).piece n ⟶ T) :
    toDirectSumPiece M n ≫ (directSumPieceDesc M n T ψ).val
      = directSumPresheafDesc (fun l ↦ ((M l).piece n).val) fun k ↦ (ψ k).val :=
  (preDirectSum M).transferHomEquiv_symm_apply (preDirectSum M).sheafifyPiece
    (preDirectSum M).toSheafifyPiece n T _

/-- Two morphisms out of a homogeneous piece of the degreewise direct sum agree as soon as they
agree after the sheafification map. -/
theorem directSumPiece_hom_ext (n : ℤ) (T : SheafOfModules.{m} R)
    {φ ψ : (directSum M).piece n ⟶ T}
    (h : toDirectSumPiece M n ≫ φ.val = toDirectSumPiece M n ≫ ψ.val) : φ = ψ :=
  (preDirectSum M).hom_ext_of_comp (preDirectSum M).sheafifyPiece
    (preDirectSum M).toSheafifyPiece n T h

/-- The canonical map to the degree-`n` piece of the degreewise direct sum, as an additive map
defined on the direct sum of sections itself. -/
noncomputable def toSheafifyDirectSum (n : ℤ) (U : Cᵒᵖ) :
    (DirectSum ι fun k ↦ ((M k).piece n).val.obj U) →+ ((directSum M).piece n).val.obj U :=
  AddMonoidHom.mk' (fun x ↦ (toDirectSumPiece M n).app U x)
    (fun x y ↦ map_add (ConcreteCategory.hom ((toDirectSumPiece M n).app U)) x y)

@[simp]
theorem toSheafifyDirectSum_of (n : ℤ) (U : Cᵒᵖ) (k : ι) (x : ((M k).piece n).val.obj U) :
    toSheafifyDirectSum M n U (DirectSum.of (fun l ↦ ((M l).piece n).val.obj U) k x)
      = ((directSumι M k).app n).val.app U x := rfl

/-- The defining property of `SheafOfModules.GradedModule.directSumPieceDesc`. -/
@[reassoc (attr := simp)]
theorem directSumι_desc (n : ℤ) (T : SheafOfModules.{m} R) (ψ : ∀ k, (M k).piece n ⟶ T)
    (k : ι) : (directSumι M k).app n ≫ directSumPieceDesc M n T ψ = ψ k :=
  SheafOfModules.hom_ext (by
    rw [SheafOfModules.comp_val, directSumι_app_val, Category.assoc, toDirectSumPiece_desc,
      directSumPresheafι_desc])

/-- **Each homogeneous piece of the degreewise direct sum is a coproduct** in the category of
sheaves of modules. -/
noncomputable def directSumPieceIsColimit (n : ℤ) :
    IsColimit (Cofan.mk ((directSum M).piece n) fun k ↦ (directSumι M k).app n) :=
  Cofan.IsColimit.mk _ (fun T ↦ directSumPieceDesc M n T.pt T.inj)
    (fun T k ↦ directSumι_desc M n T.pt T.inj k)
    (fun T m hm ↦ directSumPiece_hom_ext M n T.pt (by
      rw [toDirectSumPiece_desc]
      refine directSumPresheaf_hom_ext (X := fun l ↦ ((M l).piece n).val) fun k ↦ ?_
      rw [directSumPresheafι_desc, ← Category.assoc, ← directSumι_app_val,
        ← SheafOfModules.comp_val]
      exact congrArg SheafOfModules.Hom.val (hm k)))

/-- A degreewise family of morphisms out of the degreewise direct sum which is compatible with
the inclusions of the summands is automatically compatible with the action. -/
theorem directSumDesc_map_smul (T : GradedModule.{t, a, m} A) (φ : ∀ k, M k ⟶ T)
    (g : ∀ n, (directSum M).piece n ⟶ T.piece n)
    (c : ∀ (n : ℤ) (k : ι), (directSumι M k).app n ≫ g n = (φ k).app n)
    (n i : ℤ) (U : Cᵒᵖ) (x : DirectSum ι fun k ↦ ((M k).piece n).val.obj U)
    (y : (A.piece i).val.obj U) :
    (g (n + i)).val.app U (toSheafifyDirectSum M (n + i) U (preDirectSumSmulApp M n i U x y))
      = T.smul n i U ((g n).val.app U (toSheafifyDirectSum M n U x)) y := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | of k x₀ =>
    rw [preDirectSumSmulApp_of, toSheafifyDirectSum_of, toSheafifyDirectSum_of]
    refine (val_app_congr (c (n + i) k) U _).trans ?_
    refine ((φ k).map_smul n i U x₀ y).trans ?_
    exact congrArg (fun w : (T.piece n).val.obj U ↦ T.smul n i U w y)
      (val_app_congr (c n k) U x₀).symm
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']

/-- **The degreewise direct sum is the coproduct** in the category of graded modules. -/
noncomputable def directSumIsColimit : IsColimit (Cofan.mk (directSum M) (directSumι M)) :=
  Cofan.IsColimit.mk _
    (fun T ↦
      { app := fun n ↦ directSumPieceDesc M n (T.pt.piece n) fun k ↦ (T.inj k).app n
        map_smul := fun n i U x y ↦
          (preDirectSum M).hom_map_smul (preDirectSum M).sheafifyPiece
            (preDirectSum M).toSheafifyPiece T.pt
            (fun p ↦ directSumPieceDesc M p (T.pt.piece p) fun k ↦ (T.inj k).app p)
            (fun p j V w z ↦ directSumDesc_map_smul M T.pt T.inj _
              (fun q k ↦ directSumι_desc M q (T.pt.piece q) _ k) p j V w z)
            n i U x y })
    (fun T k ↦ Hom.ext fun n ↦ directSumι_desc M n (T.pt.piece n) _ k)
    (fun T m hm ↦ Hom.ext fun n ↦ directSumPiece_hom_ext M n (T.pt.piece n) (by
      rw [toDirectSumPiece_desc]
      refine directSumPresheaf_hom_ext (X := fun l ↦ ((M l).piece n).val) fun k ↦ ?_
      rw [directSumPresheafι_desc, ← Category.assoc, ← directSumι_app_val,
        ← SheafOfModules.comp_val]
      exact congrArg (fun ρ : M k ⟶ T.pt ↦ (ρ.app n).val) (hm k)))

/-- **Graded modules over a sheaf of graded algebras have arbitrary direct sums**, formed
degreewise. -/
@[stacks 0FR0 "direct_sums"]
instance hasCoproducts : HasColimitsOfShape (Discrete ι) (GradedModule.{t, a, m} A) where
  has_colimit F := by
    have : HasColimit (Discrete.functor (F.obj ∘ Discrete.mk)) :=
      HasColimit.mk ⟨_, directSumIsColimit (F.obj ∘ Discrete.mk)⟩
    exact hasColimit_of_iso Discrete.natIsoFunctor

/-- **Taking a fixed homogeneous component commutes with set-indexed direct sums.** -/
@[stacks 0FR0 "direct_sums"]
instance pieceFunctor_preservesCoproducts (n : ℤ) :
    PreservesColimitsOfShape (Discrete ι) (pieceFunctor.{t, a, m} A n) := by
  have : ∀ f : ι → GradedModule.{t, a, m} A,
      PreservesColimit (Discrete.functor f) (pieceFunctor.{t, a, m} A n) := fun f ↦
    preservesColimit_of_preserves_colimit_cocone (directSumIsColimit f)
      ((isColimitMapCoconeCofanMkEquiv (pieceFunctor A n) f (directSumι f)).symm
        (directSumPieceIsColimit f n))
  exact preservesColimitsOfShape_of_discrete _

end Sheafify

end GradedModule

end DirectSum

end SheafOfModules

/-! ### The abelian structure, and colimits -/

namespace SheafOfModules

namespace GradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : GradedAlgebra.{t, a} R}
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- Graded modules have finite direct sums, a special case of arbitrary ones. -/
instance hasFiniteCoproducts : HasFiniteCoproducts (GradedModule.{t, a, m} A) :=
  hasFiniteCoproducts_of_hasCoproducts.{m} (GradedModule.{t, a, m} A)

/-- Graded modules have finite biproducts, hence finite products and a zero object. -/
instance hasFiniteBiproducts : HasFiniteBiproducts (GradedModule.{t, a, m} A) :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- **The category of right graded modules over a sheaf of graded algebras is abelian.**

Kernels and cokernels are formed degreewise, and the coimage-image comparison of a homomorphism
is an isomorphism because it is one in each homogeneous degree. -/
@[stacks 0FR0 "abelian"]
noncomputable instance abelian : Abelian (GradedModule.{t, a, m} A) := by
  have : ∀ {X Y : GradedModule.{t, a, m} A} (f : X ⟶ Y),
      IsIso (Abelian.coimageImageComparison f) := fun f => isIso_coimageImageComparison f
  exact Abelian.ofCoimageImageComparisonIsIso

/-- Graded modules have all colimits of the size of the module universe: they have direct sums
and coequalizers. -/
instance hasColimitsOfSize : HasColimitsOfSize.{m, m} (GradedModule.{t, a, m} A) :=
  have : HasCoequalizers (GradedModule.{t, a, m} A) :=
    Preadditive.hasCoequalizers_of_hasCokernels
  has_colimits_of_hasCoequalizers_and_coproducts.{m}

/-- Taking a fixed homogeneous component commutes with all colimits of the size of the module
universe. This is Tag 0FR0's colimit statement with the size universe left free; see
`pieceFunctor_preservesColimits` for the unconditional form. -/
theorem pieceFunctor_preservesColimitsOfSize' (n : ℤ) :
    PreservesColimitsOfSize.{m, m} (pieceFunctor.{t, a, m} A n) :=
  pieceFunctor_preservesColimitsOfSize A n

end GradedModule

end SheafOfModules

namespace SheafOfModules

namespace GradedModule

universe m'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  (A : GradedAlgebra.{t, a} R)
  [HasSheafify J AddCommGrpCat.{max u m'}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u m'}]

/-- **Taking a fixed homogeneous component of a graded module commutes with all colimits.**

The module universe is `max u m'` for a site `C : Type u`, because that is the hom universe of
`SheafOfModules.{max u m'} R` and `PreservesColimits` quantifies over diagrams of that size;
`pieceFunctor_preservesColimitsOfSize'` is the same content with the size universe free. -/
@[stacks 0FR0 "degree_preserves_colimits"]
instance pieceFunctor_preservesColimits (n : ℤ) :
    PreservesColimits (pieceFunctor.{t, a, max u m'} A n) :=
  pieceFunctor_preservesColimitsOfSize A n

end GradedModule

end SheafOfModules
