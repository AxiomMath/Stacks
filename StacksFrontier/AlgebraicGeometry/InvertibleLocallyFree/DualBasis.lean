module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyTrivialInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleLocallyFree.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import StacksCore.Tactic.StacksAttribute

/-!
# Clause 1 of Tag 0B8M, unconditionally, through the dual sheaf

Let `𝒪` be a presheaf of commutative rings on a site `(C, J)` whose underlying presheaf of rings
is a sheaf. Clause 1 of [Stacks, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M) says that a
sheaf of `𝒪`-modules which is finite locally free of rank one is invertible.

`StacksFrontier/AlgebraicGeometry/InvertibleLocallyFree/Basic.lean` proves that such a sheaf is
invertible *on each member of a covering of the terminal object*, and leaves the passage to the
whole site as the named hypothesis
`Stacks.InvertibleLocallyFree.InvertibleIsLocal`. This file discharges clause 1 **without** that
hypothesis, by taking the route the source itself takes: the dual sheaf. The inverse of `L` is
not glued from local pieces at all — it is `L^∨ = SheafHom(L, 𝒪)`, a global construction — and
the pairing `L^∨ ⊗ L ⟶ 𝒪` is an isomorphism because it is one locally. So no descent of the
*object* is needed, and `InvertibleIsLocal` is not on the path to clause 1.

Everything downstream of the pairing is already in the library:
`Stacks.SheafOfModules.isInvertible_of_dualBasisOne` takes a family of objects covering the
terminal object together with a rank-one dual basis on each, and concludes invertibility. Its
stated missing input is the conversion of a rank-one local trivialization into that dual-basis
data. This file supplies exactly that conversion, in
`Stacks.InvertibleLocallyFree.dualBasisOneOfIso`, and reads off clause 1.

## Main definitions

* `Stacks.InvertibleLocallyFree.basisSection`: the section of `L` over `U` cut out by a
  trivialization `L|_U ≅ 𝒪|_U`, namely the preimage of `1`.
* `Stacks.InvertibleLocallyFree.lamOfIso`: the trivialization read as a section of the dual
  `L^∨` over `U`. A morphism `L|_U ⟶ 𝒪|_U` of sheaves of modules on the slice site *is* such a
  section; see the implementation notes.
* `Stacks.InvertibleLocallyFree.dualBasisOneOfIso`: the rank-one dual basis assembled from a
  trivialization.

## Main results

* `Stacks.InvertibleLocallyFree.isInvertible_of_isFiniteLocallyFreeOfRank_one`: **clause 1 of
  Tag 0B8M**, unconditionally, for `AlgebraicGeometry.SheafOfModules.IsInvertible`.
* `Stacks.InvertibleLocallyFree.stacksIsInvertible_iff_isInvertible`: those two predicates agree.
  The repository carries both, with identical bodies, and both already carry the Tag 01CS
  attribute; this is the bridge between them, and it is what lets the dual-sheaf machinery —
  which is stated for the `Stacks.SheafOfModules` copy — discharge a goal phrased with the
  `AlgebraicGeometry.SheafOfModules` copy, which is the one every consumer in the repository
  uses.
* `Stacks.InvertibleLocallyFree.resSection_basisSection` and
  `Stacks.InvertibleLocallyFree.span_basisSection`: the two facts about a trivialization that the
  dual-basis axioms need — the basis section restricts to the preimage of `1` on every object of
  the slice site, and it spans with the trivialization as coordinate.

## Implementation notes

**Why no gluing is needed.** The three properties making `tensorLeft L` an equivalence do each
descend only against effective descent for sheaves of modules, which is why
`InvertibleIsLocal` looks like it needs a stack. But clause 1 does not go that way. An inverse
object is produced outright as `L^∨`, and the only local-to-global step left is that a morphism
of sheaves which is locally bijective becomes an isomorphism after sheafification — which is
`Stacks.SheafOfModules.isIso_sheafify_map_evaluationPresheaf`, and needs no descent theory.
`InvertibleIsLocal` is therefore simply not a dependency of clause 1.  It is itself proved, by a
separate route that likewise uses no descent theory, as
`Stacks.SheafOfModules.invertibleIsLocal`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleLocalDual.lean:588`).

**A trivialization is literally a section of the dual.** A section of `L^∨` over `U` is, by
Tag 03EM, a morphism `(restrFun 𝒪 U).obj L.val ⟶ (restrFun 𝒪 U).obj 𝒪.val` of presheaves of
modules on the slice site. Mathlib's restriction `L.over U` is `PresheafOfModules.pushforward`
along `Over.forget U`, and `Stacks.restrFun` is the same functor, so `(L.over U).val` and
`(restrFun 𝒪 U).obj L.val` are equal by `rfl`, and likewise for the structure sheaf. Hence
`φ.hom.val` of a trivialization `φ : L.over U ≅ 𝒪|_U` *is* a section of the dual with no
transport. `lamOfIso` exists only to pin that type: `dualApp` takes an argument whose type is
spelled `(dualSheaf 𝒪 h𝒪 L).val.obj (op U)`, and handing it `φ.hom.val` directly leaves a goal
that is not type-correct at `implicit` transparency, so `rw` fails on it.

**The two ring spellings.** `(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
  h𝒪).obj.obj (op V.unop.left)` and
`((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U).obj.obj V` are the same
  ring, but
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` is a plain `def`, so instance search
  connects neither to the other
nor to `𝒪.obj (op V.unop.left)`. The numeral `1` is therefore always written with an ascription
to a spelling that carries the instances, and `inv_app_eq_smul` is proved entirely in the
restricted spelling and then transported into the unrestricted one by `exact`, which checks at
default transparency, rather than by `rw`, which does not. No transparency pragma and no
`set_option` is used.

**Universes (forced, and reported).** The module and ring universe is `max u v` for a site
`C : Type u` with `Category.{v} C`. This is not a choice made here: `Stacks.internalHom` of
Tag 03EM is stated for `PresheafOfModules.{max u v}`, because a section of the internal hom over
`U` is a morphism of presheaves of modules on `C/U` and so lives in `Type (max u v)`, and
`Stacks.SheafOfModules.TensorSheafification` identifies the ring universe with the module universe.
  Clause 1 is therefore proved
here at `w = max u v`, whereas
`Stacks.InvertibleLocallyFree.exists_coversTop_isInvertible_over_of_isFiniteLocallyFreeOfRank_one`
is stated for an arbitrary section universe `w`. The constraint is inherited from the dual sheaf
and is recorded rather than hidden; on the site of opens of a space `X : TopCat.{u}` the hom
universe is `0` and `max u v = u`, which is the universe those statements already use.

**Extra instance hypotheses relative to the conditional version.**
`isInvertible_of_isFiniteLocallyFreeOfRank_one_of_invertibleIsLocal` needs sheafification only on
the slice sites, because global invertibility is handed to it by its hypothesis. The theorem here
additionally needs sheafification on `(C, J)` itself — `HasWeakSheafify J AddCommGrpCat` and
`J.WEqualsLocallyBijective AddCommGrpCat` — because it sheafifies the evaluation pairing. These
are the standing hypotheses under which the invertibility vocabulary of Tag 01CS is defined at
all, not new mathematical assumptions. `J.HasSheafCompose (forget₂ CommRingCat RingCat)` is
*not* needed: the pairing is sheafified through
  `Stacks.SheafOfModules.TensorSheafification.sheafify`, whose use here does not
reach the comparison that hypothesis governs.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite

universe v u

namespace Stacks.InvertibleLocallyFree

open Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}
  {h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪)}

section Components

variable {U : C} {R' : Sheaf (J.over U) RingCat.{max u v}}
  {A B : SheafOfModules.{max u v} R'}

/-- Components of morphisms of sheaves of modules on a slice site compose to the identity when the
morphisms do. -/
private theorem app_app_apply_of_comp_eq_id {f : A ⟶ B} {g : B ⟶ A} (h : f ≫ g = 𝟙 A)
    (X : (Over U)ᵒᵖ) (y : A.val.obj X) : (g.val.app X).hom ((f.val.app X).hom y) = y := by
  have h' : f.val.app X ≫ g.val.app X = 𝟙 _ := by
    rw [← PresheafOfModules.comp_app, ← SheafOfModules.comp_val, h,
      SheafOfModules.id_val, PresheafOfModules.id_app]
  exact congrArg (fun m : A.val.obj X ⟶ A.val.obj X => m.hom y) h'

/-- The components of an isomorphism of sheaves of modules on a slice site are mutually
inverse, one way round. -/
theorem app_inv_app_hom (φ : A ≅ B) (X : (Over U)ᵒᵖ) (y : A.val.obj X) :
    (φ.inv.val.app X).hom ((φ.hom.val.app X).hom y) = y :=
  app_app_apply_of_comp_eq_id φ.hom_inv_id X y

/-- The components of an isomorphism of sheaves of modules on a slice site are mutually
inverse, the other way round. -/
theorem app_hom_app_inv (φ : A ≅ B) (X : (Over U)ᵒᵖ) (y : B.val.obj X) :
    (φ.hom.val.app X).hom ((φ.inv.val.app X).hom y) = y :=
  app_app_apply_of_comp_eq_id φ.inv_hom_id X y

end Components

section DualBasis

variable (𝒪 h𝒪) {U : C}
  {L : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
  (φ : L.over U ≅ SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
    h𝒪).over U))

/-- The morphism of the slice site from an object `V` of `C/U` to the terminal object `𝟙_U`.
Restriction along it is restriction from `U` to `V.left`. -/
abbrev toTerm (V : (Over U)ᵒᵖ) : (op (Over.mk (𝟙 U)) : (Over U)ᵒᵖ) ⟶ V :=
  (Over.homMk V.unop.hom (by simp) : V.unop ⟶ Over.mk (𝟙 U)).op

/-- **The basis section cut out by a trivialization**: the preimage of `1` under
`φ : L|_U ≅ 𝒪|_U`, read at the terminal object of the slice site. -/
noncomputable def basisSection : L.val.obj (op U) :=
  (φ.inv.val.app (op (Over.mk (𝟙 U)))).hom
    (1 : ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U).obj.obj (op
      (Over.mk (𝟙 U))))

/-- **The trivialization, read as a section of the dual.** A morphism of sheaves of modules on
the slice site is a section of `L^∨` over `U`. -/
noncomputable def lamOfIso : (dualSheaf 𝒪 h𝒪 L).val.obj (op U) := φ.hom.val

/-- The section `lamOfIso φ` of the dual sheaf evaluates, on an object `V` of the slice site,
as the component of `φ.hom` at `V`. -/
@[simp]
lemma dualApp_lamOfIso (V : (Over U)ᵒᵖ) (g : L.val.obj (op V.unop.left)) :
    dualApp (L := L) (lamOfIso 𝒪 h𝒪 φ) V g = (φ.hom.val.app V).hom g := rfl

/-- The basis section restricts, on every object of the slice site, to the preimage of `1` under
`φ`. -/
theorem resSection_basisSection (V : (Over U)ᵒᵖ) :
    resSection V (basisSection 𝒪 h𝒪 φ)
      = (φ.inv.val.app V).hom
          (1 : ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U).obj.obj V)
            := by
  have hnat := PresheafOfModules.naturality_apply φ.inv.val (toTerm V)
    (1 : ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U).obj.obj (op
      (Over.mk (𝟙 U))))
  rw [basisSection, show resSection V ((φ.inv.val.app (op (Over.mk (𝟙 U)))).hom
      (1 : ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U).obj.obj (op
        (Over.mk (𝟙 U)))))
      = ((L.over U).val.map (toTerm V)).hom
        ((φ.inv.val.app (op (Over.mk (𝟙 U)))).hom
          (1 : ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U).obj.obj
            (op (Over.mk (𝟙 U))))) from rfl, ← hnat]
  congr 1
  exact PresheafOfModules.unit_map_one _ (toTerm V)

/-- The inverse of a trivialization is determined by where it sends `1`: it is linear over the
restricted structure sheaf, so its value on `c` is `c` times its value on `1`. -/
theorem inv_app_eq_smul (V : (Over U)ᵒᵖ)
    (c : ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U).obj.obj V) :
    (φ.inv.val.app V).hom c
      = c • (φ.inv.val.app V).hom
          (1 : ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U).obj.obj V)
            := by
  have h := map_smul (φ.inv.val.app V).hom c
    (1 : ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U).obj.obj V)
  rw [smul_eq_mul, mul_one] at h
  exact h

/-- **The basis section spans, with the trivialization as coordinate.** Every section of `L`
over an object of the slice site is its own `φ`-value times the restricted basis section. -/
theorem span_basisSection (V : (Over U)ᵒᵖ) (g : L.val.obj (op V.unop.left)) :
    dualApp (L := L) (lamOfIso 𝒪 h𝒪 φ) V g • resSection V (basisSection 𝒪 h𝒪 φ) = g := by
  rw [resSection_basisSection]
  exact (inv_app_eq_smul 𝒪 h𝒪 φ V _).symm.trans (app_inv_app_hom φ V g)

/-- **A rank-one trivialization yields a rank-one dual basis.** This is the input that
`Stacks.SheafOfModules.isInvertible_of_dualBasisOne` was stated to be waiting for. -/
noncomputable def dualBasisOneOfIso : DualBasisOne 𝒪 h𝒪 L U where
  e := basisSection 𝒪 h𝒪 φ
  lam := lamOfIso 𝒪 h𝒪 φ
  span := span_basisSection 𝒪 h𝒪 φ
  eval_self := app_hom_app_inv φ (op (Over.mk (𝟙 U))) _

end DualBasis

section Bridge

variable (𝒪 h𝒪)

/-- **The repository's two invertibility predicates agree.**
`Stacks.SheafOfModules.IsInvertible` and `AlgebraicGeometry.SheafOfModules.IsInvertible` are
separate classes with identical bodies, both carrying the Tag 01CS attribute. The dual-sheaf
machinery is stated for the first and every consumer in the repository uses the second, so the
bridge is needed to connect them; it is nothing but reassembling the witness. -/
theorem stacksIsInvertible_iff_isInvertible
    (L : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
      :
    Stacks.SheafOfModules.IsInvertible 𝒪 h𝒪 L ↔
      AlgebraicGeometry.SheafOfModules.IsInvertible 𝒪 h𝒪 L := by
  constructor <;> rintro ⟨F, hF, ⟨a⟩⟩ <;> exact ⟨F, hF, ⟨⟨a.ι, a.bijective⟩⟩⟩

end Bridge

section Main

variable (𝒪 h𝒪)
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{max u v}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- **Clause 1 of Stacks Tag 0B8M.** A sheaf of modules that is finite locally free of rank one
is invertible, with invertibility read as
`AlgebraicGeometry.SheafOfModules.IsInvertible` — the predicate every consumer in this
repository uses.

This is unconditional. It does **not** use
`Stacks.InvertibleLocallyFree.InvertibleIsLocal` (which is itself proved, as
`Stacks.SheafOfModules.invertibleIsLocal`): clause 1 does not need
descent of the inverse object, because the inverse is the dual sheaf `L^∨ = SheafHom(L, 𝒪)` and
the only local-to-global step is that a locally bijective pairing is inverted by sheafification.
See the module documentation for the forced universe constraint `w = max u v`, inherited from
the internal hom of Tag 03EM. -/
@[stacks 0B8M "(1)"]
theorem isInvertible_of_isFiniteLocallyFreeOfRank_one
    (L : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank L 1] :
    AlgebraicGeometry.SheafOfModules.IsInvertible 𝒪 h𝒪 L :=
  (stacksIsInvertible_iff_isInvertible 𝒪 h𝒪 L).mp
    (Stacks.SheafOfModules.isInvertible_of_isFiniteLocallyFreeOfRank_one 𝒪 h𝒪 L)

end Main

end Stacks.InvertibleLocallyFree

end
