module

public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.StructureSheaf

/-!
# The dual of the structure sheaf is the structure sheaf

Let `X` be a scheme.  The dual `𝒪_X^∨ = SheafHom(𝒪_X, 𝒪_X)` of the structure sheaf is a copy of
`𝒪_X`: a local endomorphism of `𝒪_U` is multiplication by its value at `1`.  This file turns
that section-level statement, which is
`StacksFrontier/AlgebraicGeometry/ReflexiveHull/StructureSheaf.lean`'s `eq_smul_unitFunctional`,
into the isomorphism of sheaves of modules itself.

Neither integrality nor local Noetherianity of `X` is used, and no coherence hypothesis: the
isomorphism exists for an arbitrary scheme.

## Why this is wanted

The remaining input of the reflexive-hull adjunction of
[Stacks, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH) was the first assertion
of [Stacks, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ) at `𝒢 = 𝒪_X`, recorded as
`HasLocalKernelPresentationDual` in
`StacksFrontier/AlgebraicGeometry/ReflexiveHull/CoherentDual.lean`: that the dual of a module of
finite presentation is, locally, the kernel of a map between two finite direct sums of copies of
`𝒪_X`.  Dualizing a presentation `𝒪_U^{⊕ m} ⟶ 𝒪_U^{⊕ n} ⟶ F|_U ⟶ 0` produces the kernel of a map
between `SheafHom(𝒪_U^{⊕ n}, 𝒪_U)` and `SheafHom(𝒪_U^{⊕ m}, 𝒪_U)`, so the statement of Tag 01CQ
is reached only after those two internal Homs have been identified with `𝒪_U^{⊕ n}` and
`𝒪_U^{⊕ m}`.  The present file is the rank-one case of that identification over a scheme.

**Two claims that used to stand here are struck.**  The input is no longer missing: it is
`Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf_hasLocalKernelPresentation` of
`StacksFrontier/AlgebraicGeometry/ReflexiveHull/LocalKernelPresentation.lean`, unconditional for
every scheme.  And the passage from rank one to finite rank does **not** need the first-variable
continuity of the internal Hom at sheaf level (Tag 03EN): it is
`Stacks.PresheafOfModules.InternalHom.internalHomBiproductIso`, which splits a finite biproduct
in the first variable using nothing but additivity and contravariant functoriality of
precomposition.  No sheafification and no smallness condition appears in it.

Consequently this file is **off** the route to Tag 01CQ, and `unitDualIso` is not used by it:
the rank-one identification that the dualized presentation consumes is
`Stacks.PresheafOfModules.InternalHom.unitInternalHomIso` of
`StacksFrontier/AlgebraicGeometry/InternalHomCokernel/Unit.lean`, the formula-free version over
an arbitrary site.  What this file supplies is the explicit section formula over a scheme, which
is what the reflexivity arguments of `StructureSheaf.lean` and `DualStalk.lean` consume.

`StructureSheaf.lean` deliberately avoided this isomorphism, proving reflexivity of `𝒪_X` by
exhibiting a two-sided inverse of `toDoubleDual` instead; its implementation notes say so.  That
was the cheaper route to reflexivity, but it leaves `𝒪_X^∨` uncomputed, and the computation is
what a dualized presentation needs.

## Main definitions

* `unitToDual X`: the morphism `𝒪_X ⟶ 𝒪_X^∨` sending a function to multiplication by it.
* `dualToUnit X`: the morphism `𝒪_X^∨ ⟶ 𝒪_X` evaluating a functional at the unit section.
* `unitDualIso X`: the resulting isomorphism `𝒪_X^∨ ≅ 𝒪_X`.

## Main results

* `dualToUnit_unitToDual` and `unitToDual_dualToUnit`: the two morphisms are mutually inverse.
  The second is `eq_smul_unitFunctional`, and it is the only step with content.
* `isIso_dualToUnit` and `isIso_unitToDual`.
* `evalAt_unitFunctional_oneSection`: the identity functional takes the unit section to the unit
  section, which is the normalization that makes the two morphisms inverse rather than merely
  mutually inverse up to a unit.

## Implementation notes

Both morphisms are built with `dualPairing_ext` and the pairing lemmas of
`StacksFrontier/AlgebraicGeometry/Reflexive/Basic.lean` rather than by rewriting under the
restriction maps of the internal-Hom presheaf.  The reason is the restriction map of
`dualSheaf`: a section of `𝒪_X^∨` over `U` is a
morphism over the slice site `Over U`, and its restriction along `i : V ⟶ U` is reindexing by
`Over.map i`, which is definitionally but not syntactically the morphism over `Over V`.  Stating
each step as an equality of pairings keeps every rewrite inside `Γ(X, -)`, where the only lemma
needed is functoriality of `X.presheaf`.

`unitToDual X` is `a ↦ a • unitFunctional X U` rather than a separately constructed
multiplication morphism: the identity functional is already a section of `𝒪_X^∨` over every open,
and the module structure on those sections supplies the multiplication.  That is what makes the
`𝒪_X(U)`-linearity of `unitToDual X` a one-line consequence of `mul_smul`.

## References

* [Stacks Project, Tag 0AVU](https://stacks.math.columbia.edu/tag/0AVU)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

variable (X : Scheme.{u})

/-! ### The identity functional is normalized -/

/-- The identity functional takes the unit section to the unit section. -/
@[simp] public theorem evalAt_unitFunctional_oneSection (U : X.Opens) :
    evalAt (unitModule X) (unitFunctional X U) (oneSection X U) = oneSection X U :=
  rfl

/-! ### Multiplication by a function, as a functional -/

/-- Multiplication by the function `a`, as a local functional on the structure sheaf: the
multiple of the identity functional by `a`. -/
public noncomputable def mulFunctional {U : X.Opens} (a : Γ(X, U)) :
    Γ(dualSheaf (unitModule X), U) :=
  a • unitFunctional X U

/-- Multiplication by a function is the multiple of the identity functional by it. -/
public theorem mulFunctional_def {U : X.Opens} (a : Γ(X, U)) :
    mulFunctional X a = a • unitFunctional X U :=
  rfl

/-- Multiplication by a function is additive in the function. -/
public theorem mulFunctional_add {U : X.Opens} (a b : Γ(X, U)) :
    mulFunctional X (a + b) = mulFunctional X a + mulFunctional X b :=
  add_smul a b _

/-- Multiplication by a product is the multiple of multiplication by the second factor. -/
public theorem mulFunctional_mul {U : X.Opens} (r a : Γ(X, U)) :
    mulFunctional X (r * a) = r • mulFunctional X a :=
  mul_smul r a _

/-- Multiplication by a restricted function is the restriction of multiplication. -/
public theorem map_mulFunctional {U V : X.Opens} (hle : V ≤ U) (a : Γ(X, U)) :
    (dualSheaf (unitModule X)).presheaf.map (homOfLE hle).op (mulFunctional X a) =
      mulFunctional X (X.presheaf.map (homOfLE hle).op a) := by
  refine dualPairing_ext (F := unitModule X) (fun W x => ?_)
  rw [mulFunctional_def, mulFunctional_def, dualPairing_map, dualPairing_smul,
    dualPairing_smul, dualPairing_unitFunctional, dualPairing_unitFunctional]
  congr 1
  change (X.presheaf.map (W.hom ≫ homOfLE hle).op).hom a =
    (X.presheaf.map W.hom.op).hom ((X.presheaf.map (homOfLE hle).op).hom a)
  rw [op_comp, X.presheaf.map_comp]
  rfl

/-- Evaluating multiplication by `a` at the unit section returns `a`. -/
@[simp] public theorem evalAt_mulFunctional {U : X.Opens} (a : Γ(X, U)) :
    evalAt (unitModule X) (mulFunctional X a) (oneSection X U) = a := by
  rw [mulFunctional_def, evalAt_smul, evalAt_unitFunctional_oneSection]
  exact mul_one a

/-! ### The two morphisms -/

/-- **Multiplication, as a morphism `𝒪_X ⟶ 𝒪_X^∨`.**  A function `a` over `U` is sent to the
functional "multiply by `a`". -/
public noncomputable def unitToDual : unitModule X ⟶ dualSheaf (unitModule X) where
  val :=
    { app := fun U => ModuleCat.homAddEquiv.symm
        { toFun := fun a => mulFunctional X (U := U.unop) a
          map_add' := fun a b => mulFunctional_add X a b
          map_smul' := fun r a => mulFunctional_mul X r a }
      naturality := fun {U V} i => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        have hle : V.unop ≤ U.unop := leOfHom i.unop
        have hi : i = (homOfLE hle).op := Subsingleton.elim _ _
        subst hi
        change mulFunctional X ((X.presheaf.map (homOfLE hle).op).hom a) =
          (dualSheaf (unitModule X)).presheaf.map (homOfLE hle).op (mulFunctional X a)
        exact (map_mulFunctional X hle a).symm }

/-- The morphism `𝒪_X ⟶ 𝒪_X^∨`, read off on sections. -/
@[simp] public theorem unitToDual_app {U : X.Opens} (a : Γ(unitModule X, U)) :
    Scheme.Modules.Hom.app (unitToDual X) U a = mulFunctional X a :=
  rfl

/-- **Evaluation at the unit section, as a morphism `𝒪_X^∨ ⟶ 𝒪_X`.** -/
public noncomputable def dualToUnit : dualSheaf (unitModule X) ⟶ unitModule X where
  val :=
    { app := fun U => ModuleCat.homAddEquiv.symm
        { toFun := fun t => evalAt (unitModule X) (V := U.unop) t (oneSection X U.unop)
          map_add' := fun t t' => evalAt_add (unitModule X) t t' _
          map_smul' := fun a t => evalAt_smul (unitModule X) a t _ }
      naturality := fun {U V} i => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro t
        have hle : V.unop ≤ U.unop := leOfHom i.unop
        have hi : i = (homOfLE hle).op := Subsingleton.elim _ _
        subst hi
        change evalAt (unitModule X)
            ((dualSheaf (unitModule X)).presheaf.map (homOfLE hle).op t)
            (oneSection X V.unop) = _
        rw [← map_oneSection X (homOfLE hle), evalAt_map (unitModule X) hle t]
        rfl }

/-- The morphism `𝒪_X^∨ ⟶ 𝒪_X`, read off on sections. -/
@[simp] public theorem dualToUnit_app {U : X.Opens} (t : Γ(dualSheaf (unitModule X), U)) :
    Scheme.Modules.Hom.app (dualToUnit X) U t = evalAt (unitModule X) t (oneSection X U) :=
  rfl

/-! ### They are mutually inverse -/

/-- A composite of module morphisms is the identity once it is on sections. -/
private theorem comp_eq_id_of_app {M N : X.Modules} (f : M ⟶ N) (g : N ⟶ M)
    (h : ∀ (U : X.Opens) (x : Γ(M, U)),
      Scheme.Modules.Hom.app g U (Scheme.Modules.Hom.app f U x) = x) :
    f ≫ g = 𝟙 M := by
  refine Scheme.Modules.hom_ext _ _ (fun U => ?_)
  ext x
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app]
  exact h U x

/-- Multiplying by `a` and then evaluating at `1` returns `a`. -/
public theorem dualToUnit_unitToDual :
    unitToDual X ≫ dualToUnit X = 𝟙 (unitModule X) :=
  comp_eq_id_of_app X _ _ fun _ a => evalAt_mulFunctional X a

/-- Evaluating a functional at `1` and then multiplying by the result returns the functional.
This is `eq_smul_unitFunctional`, and it is the only step of the isomorphism with content. -/
public theorem unitToDual_dualToUnit :
    dualToUnit X ≫ unitToDual X = 𝟙 (dualSheaf (unitModule X)) :=
  comp_eq_id_of_app X _ _ fun _ t => (eq_smul_unitFunctional X t).symm

/-- **The dual of the structure sheaf of a scheme is the structure sheaf.**  The isomorphism is
evaluation at the unit section, with multiplication as its inverse. -/
public noncomputable def unitDualIso : dualSheaf (unitModule X) ≅ unitModule X where
  hom := dualToUnit X
  inv := unitToDual X
  hom_inv_id := unitToDual_dualToUnit X
  inv_hom_id := dualToUnit_unitToDual X

/-- Evaluation at the unit section is an isomorphism. -/
public theorem isIso_dualToUnit : IsIso (dualToUnit X) :=
  ⟨unitToDual X, unitToDual_dualToUnit X, dualToUnit_unitToDual X⟩

/-- Multiplication is an isomorphism `𝒪_X ≅ 𝒪_X^∨`. -/
public theorem isIso_unitToDual : IsIso (unitToDual X) :=
  ⟨dualToUnit X, dualToUnit_unitToDual X, unitToDual_dualToUnit X⟩

end Stacks.AlgebraicGeometry.ReflexiveModules

end
