module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerStalk
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksCore.Tactic.StacksAttribute

/-!
# Stalks of the exterior algebra and of the exterior powers of a presheaf of modules

Let `R` be a presheaf of commutative rings on a topological space `X` and `F` a presheaf of
`R`-modules. This file proves that forming the exterior algebra, and forming the `n`-th exterior
power, commute with taking the stalk at a point `x : X`:

* `PresheafOfModules.extAlgStalkRingEquiv` : the stalk of the presheaf of rings
  `U ↦ ⋀_{R(U)}(F(U))` is `⋀_{R_x}(F_x)`;
* `PresheafOfModules.extPowStalkEquiv` : the stalk of the presheaf of modules
  `U ↦ ⋀ⁿ_{R(U)}(F(U))` — that is, of `PresheafOfModules.extPow n F` — is `⋀ⁿ_{R_x}(F_x)`, as a
  module over the stalk ring `R_x`.

The comparison is pinned on germs of wedge products by
`PresheafOfModules.extPowStalkL_germ_ιMulti`: the germ of `s₀ ∧ ⋯ ∧ s_{n-1}` goes to the wedge
of the germs. Since wedges of vectors span the exterior power
(`ExteriorAlgebra.ιMulti_span_fixedDegree`) that formula determines the isomorphism, which is
what makes it the *canonical* one Stacks Tags 01CG and 01CH assert. This is the exterior
analogue of `PresheafOfModules.symPowStalkEquiv`, and it is the point-local half of the exterior
assertion of those two tags.

## Main definitions

* `PresheafOfModules.extAlg` : the presheaf of **rings** — not of commutative rings: the exterior
  algebra is not commutative — whose sections over `U` are `⋀_{R(U)}(F(U))`, with
  `ExteriorAlgebra.mapₛₗ` of the restriction maps as its restriction maps.
* `PresheafOfModules.extAlgGerm` : the germ map of `extAlg F`, as a ring homomorphism whose
  source is spelled as the exterior algebra itself.
* `PresheafOfModules.extAlgStalkDesc` : base change along the germ maps,
  `(⋀ F)ₓ ⟶ ⋀_{R_x}(F_x)`, obtained from the colimit computing the stalk.
* `PresheafOfModules.extAlgStalkRingHom`, `PresheafOfModules.extStalkAlgebra` and
  `PresheafOfModules.ιExtStalkL` : the `R_x`-algebra structure on `(⋀ F)ₓ` induced by the
  structure map `R ⟶ extAlg F`, and the `R_x`-linear degree-one generator `F_x →ₗ (⋀ F)ₓ`. These
  are the data the universal property of the exterior algebra consumes.
* `PresheafOfModules.extAlgStalkLift` : the `R_x`-algebra map `⋀_{R_x}(F_x) ⟶ (⋀ F)ₓ` lifting
  `ιExtStalkL`, which exists because `ιExtStalkL` is square-zero
  (`PresheafOfModules.ιExtStalkL_sq_zero`).
* `PresheafOfModules.extPowStalkDesc` and `PresheafOfModules.extPowStalkL` : the same base change
  in degree `n`, as a morphism of abelian groups and as an `R_x`-linear map.

## Main results

* `PresheafOfModules.extAlgStalkRingEquiv` : **the exterior algebra commutes with stalks.**
  `extAlgStalkDesc` and `extAlgStalkLift` are mutually inverse: that is
  `extAlgStalkLift_extAlgStalkDesc` and `extAlgStalkDesc_extAlgStalkLift`, each proved by
  `ExteriorAlgebra.ringHom_ext` after reducing to a germ with `TopCat.Presheaf.exists_germ_eq`.
* `PresheafOfModules.extPowStalkEquiv` : **the `n`-th exterior power commutes with stalks.**
  Injectivity (`extPowStalkL_injective`) is deduced from injectivity of `extAlgStalkDesc`
  together with `TopCat.Presheaf.germ_eq`; surjectivity (`extPowStalkL_surjective`) from
  `ExteriorAlgebra.ιMulti_span_fixedDegree`, after choosing one open neighbourhood on which
  representatives of all `n` germs are defined simultaneously.
* `PresheafOfModules.extPowStalkL_germ_ιMulti` : **the comparison sends the germ of a wedge of
  `n` local sections to the wedge of the germs.** This is the formula the comparison of the
  exterior assertion of Tag 01CH is specified by.
* `PresheafOfModules.extPowStalkEquivOfStalkIso` and
  `PresheafOfModules.extPowStalkEquivOfStalkIso_germ_ιMulti` : the same, transported along any
  morphism out of `extPow n F` which is a stalk isomorphism — in particular along the
  sheafification unit, which is the form in which the exterior assertion of Tag 01CH is
  consumed.

## Implementation notes

**Two structural differences from the symmetric case.** Both are real, and each costs a
construction that `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerStalk` does not
need.

1. *The exterior algebra is not commutative.* So `extAlg F` is a presheaf valued in `RingCat`,
   not in `CommRingCat`, and its stalk is a colimit in `RingCat`. The scalars, however, are the
   stalk of `R` in `CommRingCat`, because that is the ring over which Mathlib puts a module
   structure on the stalk of `F`. The two are bridged by
   `SemilinearStalk.commStalkRingEquiv`, which is exactly the statement that
   `forget₂ CommRingCat RingCat` preserves the filtered colimit computing the stalk;
   `extAlgStalkRingHom` is the composite, and `extStalkAlgebra` is `RingHom.toAlgebra'` applied
   to it — `toAlgebra'`, not `toAlgebra`, since the target is noncommutative, so the centrality
   of the image has to be checked, which `extAlgStalkRingHom_central` does on germs.
2. *`ExteriorAlgebra.lift` carries a square-zero side condition.* `SymmetricAlgebra.lift`
   consumes a linear map and nothing else; `ExteriorAlgebra.lift` consumes a linear map `f`
   together with `∀ m, f m * f m = 0`. For `ιExtStalkL` that condition is `ιExtStalkL_sq_zero`,
   and it is checked **on germs**: every element of the stalk of `F` is a germ
   (`TopCat.Presheaf.exists_germ_eq`), the generator of a germ is the germ of a generator, and
   `ExteriorAlgebra.ι_sq_zero` holds sectionwise, so the square is the germ of zero.

**Why the whole exterior algebra and not only the degree-`n` piece.** Exactly as in the
symmetric case. Surjectivity of the degree-`n` comparison is elementary — a finite family of
germs has a common open neighbourhood — but injectivity is not: a local section of `⋀ⁿ` whose
germ-wise base change vanishes must already vanish on a smaller open, and that is precisely the
statement that `⋀` commutes with the filtered colimit computing the stalk. The ungraded exterior
algebra is where the universal property is available, so it is proved there
(`extAlgStalkRingEquiv`) and transported down to degree `n` through the inclusion
`⋀ⁿ_{R(U)}(F(U)) ⊆ ⋀_{R(U)}(F(U))`, which is injective on stalks because it is injective
sectionwise.

**Wedges, not products.** The symmetric file states its germ formula with `∏ i, ι (s i)`, a
`Finset.prod`, which needs a commutative monoid. `ExteriorAlgebra R M` is not one, so the
spanning family here is `ExteriorAlgebra.ιMulti R n`, whose value at `v` is the ordered product
`(List.ofFn fun i => ι R (v i)).prod`. Its subtype-valued companion
`exteriorPower.ιMulti R n`, landing in `⋀[R]^n M` rather than in the algebra, is what
`extPowStalkL_germ_ιMulti` is stated with, so that formula is an equation *in the exterior
power* and needs no coercion to the ambient algebra.

**The degree is always a variable.** Every statement about `extPow`, `ExteriorAlgebra.powMapₛₗ`
or `exteriorPower.ιMulti` below keeps `n` a variable and is instantiated only at the point of
use. `ExteriorAlgebra R M` is a `CliffordAlgebra` quotient of `TensorAlgebra R M`, and with a
numeral degree `whnf` unfolds the exterior power through `Submodule.mul` and `Submodule.span`
into that quotient. As recorded for the symmetric case, this is fatal in a *statement*, not only
in a proof.

**Two spellings of the same type.** The sections of `extAlg F` over `U` are
`↑((extAlg F).obj (op U))`, and `ExteriorAlgebra ((R ⋙ forget₂ _ _).obj (op U)) (F.obj (op U))`
is the same type definitionally but not syntactically; `rw` works at a transparency at which the
first spelling's multiplication is not the second's, so `map_mul` does not fire through it.
`extAlgGerm` exists to ascribe the second spelling, and `ιExtStalkFun` and `extPowStalkFun` do
the same for the targets of the two `colimit.desc` morphisms, whose codomains are
`AddCommGrpCat.of` of the type one actually wants. All three are definitional renames.

**Universes, forced not chosen.** `X : TopCat.{u}`, `R : X.Presheaf CommRingCat.{u}` and
`F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)` is the single combination at which
Mathlib's `Module (R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)` instance
(`Mathlib/Algebra/Category/ModuleCat/Stalk.lean`) exists, so the module universe is forced equal
to the ring universe and to the universe of the space. Nothing is narrowed relative to that
instance; this is the same constraint recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness` and in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerStalk`.

**What is tagged here, and what is not.** The `@[stacks 01CH]` attribute below is carried by
`extPowStalkEquivOfStalkIso` together with `extPowStalkEquivOfStalkIso_germ_ιMulti`, which is
the exterior degreewise assertion of the tag in the form it is consumed: for a sheaf of modules
on a ringed space whose `n`-th exterior power is presented as a sheafification of the sectionwise
exterior powers, the stalk is `⋀ⁿ` of the stalk, by the canonical map carrying germs of wedges to
wedges of germs. The symmetric counterparts of that clause are tagged in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricStalkSheaf` (degreewise) and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraStalkUngraded` (ungraded), and the exterior
ungraded clause is tagged in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded`, which also bundles the
clause below for a sheaf of graded algebras as `SheafOfModules.exteriorPowerStalkEquiv`.

Note what Tag 01CH literally says, so that the clause comment is not read as more than it is: the
source states three *ungraded* isomorphisms, `T(F)ₓ ≅ T(Fₓ)`, `Sym(F)ₓ ≅ Sym(Fₓ)` and
`⋀(F)ₓ ≅ ⋀(Fₓ)`. The degreewise statement is not one of them; it is the clause this library has
chosen to record the tag by in each of the two symmetric files above, and this file follows that
convention and names its clause the same way.

The ungraded exterior assertion is therefore **not** tagged here, even though
`extAlgStalkRingEquiv` is exactly `(⋀ F)ₓ ≅ ⋀(Fₓ)`: that is the statement for a *presheaf* of
modules, and the sheaf `⋀(M)` of the source is the coproduct of its graded pieces, so passing to
it needs `SheafOfModules.stalkCoprodEquiv`, which this file does not use. That passage is
carried out in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded`, where
`SheafOfModules.exteriorAlgebra_stalk` is the ungraded exterior clause and carries the tag, so
nothing is owed for it any longer.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace PresheafOfModules

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (x : X)

/-! ### The presheaf of sectionwise exterior algebras -/

/-- The presheaf of rings whose sections over `U` are `⋀_{O(U)}(F(U))`. The exterior algebra is
not commutative, so this is valued in `RingCat`, where its symmetric counterpart
`PresheafOfModules.symAlg` is valued in `CommRingCat`. -/
noncomputable def extAlg : X.Presheaf RingCat.{u} where
  obj U := RingCat.of
    (ExteriorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U) (F.obj U))
  map {U _} f := RingCat.ofHom
    (ExteriorAlgebra.mapₛₗ ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map f).hom
      (F.restrictₛₗ f))
  map_id U := by
    refine RingCat.hom_ext (RingHom.ext fun y => ?_)
    exact ExteriorAlgebra.mapₛₗ_eq_self (F.restrictₛₗ (𝟙 U))
      (fun r => congrArg (fun φ : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U ⟶
          (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U => (ConcreteCategory.hom φ) r)
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map_id U))
      (fun m => F.map_id_apply_ungraded U m) y
  map_comp {U _ W} f g := by
    refine RingCat.hom_ext (RingHom.ext fun y => ?_)
    exact ExteriorAlgebra.mapₛₗ_eq_comp (F.restrictₛₗ f) (F.restrictₛₗ g) (F.restrictₛₗ (f ≫ g))
      (fun r => congrArg (fun φ : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U ⟶
          (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj W => (ConcreteCategory.hom φ) r)
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map_comp f g))
      (fun m => F.map_comp_apply f g m) y

/-- The restriction maps of `extAlg F` are `ExteriorAlgebra.mapₛₗ` of the restriction maps of `R`
and of `F`. -/
@[simp]
theorem extAlg_map_apply {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
    (y : ExteriorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U) (F.obj U)) :
    (extAlg F).map f y =
      ExteriorAlgebra.mapₛₗ ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map f).hom
        (F.restrictₛₗ f) y := rfl

/-- The germ map of `extAlg F` as a ring homomorphism out of the sectionwise exterior algebra.
This is `TopCat.Presheaf.germ` with its source spelled as the exterior algebra itself rather
than as the value of a functor; the two are definitionally equal, but the first spelling is the
one in which the ring structure used by `map_mul` is found by instance search. -/
noncomputable def extAlgGerm (U : Opens X) (hx : x ∈ U) :
    ExteriorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) (F.obj (op U)) →+*
      ↑((extAlg F).stalk x) :=
  ((extAlg F).germ U x hx).hom

/-- `extAlgGerm` agrees with the germ map of `extAlg F`. -/
theorem extAlgGerm_eq (U : Opens X) (hx : x ∈ U)
    (y : ExteriorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
      (F.obj (op U))) :
    extAlgGerm F x U hx y = (extAlg F).germ U x hx y := rfl

/-- The cocone on the diagram computing the stalk of `extAlg F` whose component at an open
neighbourhood `U` of `x` is base change along the germ maps of `R` and of `F`. -/
noncomputable def extAlgStalkCocone :
    Limits.Cocone ((OpenNhds.inclusion x).op ⋙ extAlg F) where
  pt := RingCat.of
    (ExteriorAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x))
  ι :=
    { app := fun U => RingCat.ofHom
        (ExteriorAlgebra.mapₛₗ (R.germ U.unop.1 x U.unop.2).hom
          (germₛₗ F x U.unop.1 U.unop.2))
      naturality := fun U V f => by
        refine RingCat.hom_ext (RingHom.ext fun y => ?_)
        exact (ExteriorAlgebra.mapₛₗ_eq_comp
          (F.restrictₛₗ ((OpenNhds.inclusion x).op.map f))
          (germₛₗ F x V.unop.1 V.unop.2) (germₛₗ F x U.unop.1 U.unop.2)
          (fun r => (TopCat.Presheaf.germ_res_apply' R
            ((OpenNhds.inclusion x).op.map f) x V.unop.2 r).symm)
          (fun m => (TopCat.Presheaf.germ_res_apply' F.presheaf
            ((OpenNhds.inclusion x).op.map f) x V.unop.2 m).symm) y).symm }

/-- Base change of the exterior algebra along the germ maps, out of the stalk of the presheaf of
sectionwise exterior algebras. -/
noncomputable def extAlgStalkDesc :
    (extAlg F).stalk x ⟶
      RingCat.of (ExteriorAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)) :=
  Limits.colimit.desc _ (extAlgStalkCocone F x)

/-- On the germ of a section `y`, `extAlgStalkDesc` is base change of `y` along the germ maps. -/
@[simp]
theorem extAlgStalkDesc_germ (U : Opens X) (hx : x ∈ U)
    (y : ExteriorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
      (F.obj (op U))) :
    extAlgStalkDesc F x (extAlgGerm F x U hx y) =
      ExteriorAlgebra.mapₛₗ (R.germ U x hx).hom (germₛₗ F x U hx) y := by
  have h := Limits.colimit.ι_desc (extAlgStalkCocone F x) (op ⟨U, hx⟩)
  exact congrArg (fun g : (extAlg F).obj (op U) ⟶ (extAlgStalkCocone F x).pt =>
    ConcreteCategory.hom g y) h

/-! ### The structure map and the degree-one generator on stalks -/

/-- The structure map `O ⟶ ⋀(F)` of the presheaf of sectionwise exterior algebras. Its source is
`R ⋙ forget₂ CommRingCat RingCat`, since `extAlg F` is a presheaf of rings. -/
noncomputable def extAlgUnit : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⟶ extAlg F where
  app U := RingCat.ofHom
    (algebraMap ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U)
      (ExteriorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U) (F.obj U)))
  naturality _ _ f := by
    refine RingCat.hom_ext (RingHom.ext fun r => ?_)
    exact (ExteriorAlgebra.mapₛₗ_algebraMap
      ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map f).hom (F.restrictₛₗ f) r).symm

/-- The structure map on stalks, as a ring homomorphism from the `CommRingCat`-valued stalk of
`R`. It is the `RingCat`-valued stalk of `extAlgUnit F`, precomposed with the comparison
`SemilinearStalk.commStalkRingEquiv` identifying `R_x` with the `RingCat`-valued stalk of
`R ⋙ forget₂ CommRingCat RingCat`. -/
noncomputable def extAlgStalkRingHom : ↑(R.stalk x) →+* ↑((extAlg F).stalk x) :=
  (((TopCat.Presheaf.stalkFunctor RingCat.{u} x).map (extAlgUnit F)).hom).comp
    (SemilinearStalk.commStalkRingEquiv R x).symm.toRingHom

/-- `extAlgStalkRingHom` sends the germ of `r` to the germ of the image of `r` in the sectionwise
exterior algebra. -/
@[simp]
theorem extAlgStalkRingHom_germ (U : Opens X) (hx : x ∈ U) (r : ↑(R.obj (op U))) :
    extAlgStalkRingHom F x (R.germ U x hx r) =
      extAlgGerm F x U hx (algebraMap
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
        (ExteriorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
          (F.obj (op U))) r) := by
  have hcomm : (SemilinearStalk.commStalkRingEquiv R x).symm (R.germ U x hx r) =
      TopCat.Presheaf.germ (C := RingCat.{u}) (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})
        U x hx r :=
    (SemilinearStalk.commStalkRingEquiv R x).symm_apply_eq.2
      (SemilinearStalk.commStalkRingEquiv_germ R x U hx r).symm
  refine Eq.trans (congrArg
    (fun z => ((TopCat.Presheaf.stalkFunctor RingCat.{u} x).map (extAlgUnit F)).hom z) hcomm) ?_
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx (extAlgUnit F) r

/-- Two elements of stalks of presheaves at `x` are germs of sections over one common open. -/
private theorem exists_germ_eq_germ_eq {C : Type (u + 1)} [Category.{u} C] [Limits.HasColimits C]
    {FC : C → C → Type*} {CC : C → Type u} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory.{u} C FC] [Limits.PreservesFilteredColimits (forget C)]
    {D : Type (u + 1)} [Category.{u} D] [Limits.HasColimits D]
    {FD : D → D → Type*} {CD : D → Type u} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory.{u} D FD] [Limits.PreservesFilteredColimits (forget D)]
    {X : TopCat.{u}} (P : X.Presheaf C) (Q : X.Presheaf D) {x : X}
    (a : ToType (P.stalk x)) (b : ToType (Q.stalk x)) :
    ∃ (U : Opens X) (hx : x ∈ U) (a' : ToType (P.obj (op U))) (b' : ToType (Q.obj (op U))),
      P.germ U x hx a' = a ∧ Q.germ U x hx b' = b := by
  obtain ⟨U₁, h₁, a₀, rfl⟩ := P.exists_germ_eq a
  obtain ⟨U₂, hle, h₂, b₀, rfl⟩ := Q.exists_le_germ_eq b h₁
  exact ⟨U₂, h₂, P.map (homOfLE hle).op a₀, b₀, TopCat.Presheaf.germ_res_apply .., rfl⟩

/-- Centrality of the image of `extAlgStalkRingHom` on a germ, which is where it is true for a
reason: the structure map of the sectionwise exterior algebras has central image by
`Algebra.commutes`, and the germ map is a ring homomorphism. -/
theorem extAlgStalkRingHom_germ_central (U : Opens X) (hx : x ∈ U)
    (r : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
    (y : ExteriorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
      (F.obj (op U))) :
    extAlgStalkRingHom F x (R.germ U x hx r) * extAlgGerm F x U hx y =
      extAlgGerm F x U hx y * extAlgStalkRingHom F x (R.germ U x hx r) := by
  rw [extAlgStalkRingHom_germ, ← map_mul (extAlgGerm F x U hx),
    ← map_mul (extAlgGerm F x U hx)]
  exact congrArg (extAlgGerm F x U hx) (Algebra.commutes r y)

/-- The image of `extAlgStalkRingHom` is central. Every element of either stalk is a germ, and on
germs this is `extAlgStalkRingHom_germ_central`.

The reduction is finished with `exact` rather than `rw`: the two spellings
`extAlgGerm F x W hW y` and `(extAlg F).germ W x hW y` of the same germ are definitionally but
not syntactically equal, so a rewrite strands one of them. -/
theorem extAlgStalkRingHom_central (c : ↑(R.stalk x)) (z : ↑((extAlg F).stalk x)) :
    extAlgStalkRingHom F x c * z = z * extAlgStalkRingHom F x c := by
  obtain ⟨U, hU, r₀, y₀, rfl, rfl⟩ := exists_germ_eq_germ_eq R (extAlg F) c z
  exact extAlgStalkRingHom_germ_central F x U hU r₀ y₀

/-- The stalk of the presheaf of sectionwise exterior algebras, as an algebra over the stalk of
the presheaf of rings. `RingHom.toAlgebra'` rather than `RingHom.toAlgebra`, because the target
is not commutative. -/
noncomputable instance extStalkAlgebra : Algebra ↑(R.stalk x) ↑((extAlg F).stalk x) :=
  (extAlgStalkRingHom F x).toAlgebra' (extAlgStalkRingHom_central F x)

/-- The algebra map of `extStalkAlgebra` is `extAlgStalkRingHom`. -/
theorem algebraMap_extStalkAlgebra :
    algebraMap ↑(R.stalk x) ↑((extAlg F).stalk x) = extAlgStalkRingHom F x := rfl

/-- The algebra map of `extStalkAlgebra` sends the germ of `r` to the germ of the image of `r` in
the sectionwise exterior algebra. -/
@[simp]
theorem algebraMap_extStalkAlgebra_germ (U : Opens X) (hx : x ∈ U) (r : ↑(R.obj (op U))) :
    algebraMap ↑(R.stalk x) ↑((extAlg F).stalk x) (R.germ U x hx r) =
      extAlgGerm F x U hx (algebraMap
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
        (ExteriorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
          (F.obj (op U))) r) :=
  extAlgStalkRingHom_germ F x U hx r

/-- The cocone whose component at an open neighbourhood `U` of `x` sends a section of `F` to the
germ of its degree-one image in `⋀_{O(U)}(F(U))`. -/
noncomputable def ιExtStalkCocone :
    Limits.Cocone ((OpenNhds.inclusion x).op ⋙ F.presheaf) where
  pt := AddCommGrpCat.of ↑((extAlg F).stalk x)
  ι :=
    { app := fun U => AddCommGrpCat.ofHom
        (((extAlg F).germ U.unop.1 x U.unop.2).hom.toAddMonoidHom.comp
          (ExteriorAlgebra.ι
            ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U.unop.1))
            (M := F.obj (op U.unop.1))).toAddMonoidHom)
      naturality := fun U V f => by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m => ?_)
        exact Eq.trans
          (congrArg (fun z : ExteriorAlgebra
              ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op V.unop.1))
              (F.obj (op V.unop.1)) => (extAlg F).germ V.unop.1 x V.unop.2 z)
            (ExteriorAlgebra.mapₛₗ_ι
              ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map
                ((OpenNhds.inclusion x).op.map f)).hom
              (F.restrictₛₗ ((OpenNhds.inclusion x).op.map f)) m).symm)
          (TopCat.Presheaf.germ_res_apply' (extAlg F)
            ((OpenNhds.inclusion x).op.map f) x V.unop.2
            (ExteriorAlgebra.ι ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U.unop.1))
              (M := F.obj (op U.unop.1)) m)) }

/-- The additive map from the stalk of `F` to the stalk of the presheaf of sectionwise exterior
algebras, sending the germ of a section to the germ of its degree-one image. -/
noncomputable def ιExtStalkAdd :
    TopCat.Presheaf.stalk F.presheaf x ⟶ AddCommGrpCat.of ↑((extAlg F).stalk x) :=
  Limits.colimit.desc _ (ιExtStalkCocone F x)

/-- `ιExtStalkAdd` sends the germ of `m` to the germ of `ExteriorAlgebra.ι _ m`. -/
@[simp]
theorem ιExtStalkAdd_germ (U : Opens X) (hx : x ∈ U) (m : F.obj (op U)) :
    ιExtStalkAdd F x (TopCat.Presheaf.germ F.presheaf U x hx m) =
      extAlgGerm F x U hx (ExteriorAlgebra.ι
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) m) := by
  have h := Limits.colimit.ι_desc (ιExtStalkCocone F x) (op ⟨U, hx⟩)
  exact congrArg (fun g : F.presheaf.obj (op U) ⟶ (ιExtStalkCocone F x).pt =>
    ConcreteCategory.hom g m) h

/-- The underlying function of `ιExtStalkAdd`, with its codomain spelled as the stalk ring. -/
noncomputable def ιExtStalkFun (m : ↑(TopCat.Presheaf.stalk F.presheaf x)) :
    ↑((extAlg F).stalk x) :=
  ιExtStalkAdd F x m

/-- `ιExtStalkFun` sends the germ of `m` to the germ of `ExteriorAlgebra.ι _ m`. -/
@[simp]
theorem ιExtStalkFun_germ (U : Opens X) (hx : x ∈ U) (m : F.obj (op U)) :
    ιExtStalkFun F x (TopCat.Presheaf.germ F.presheaf U x hx m) =
      extAlgGerm F x U hx (ExteriorAlgebra.ι
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) m) :=
  ιExtStalkAdd_germ F x U hx m

/-- `ιExtStalkFun` commutes with scalar multiplication of a germ by a germ over the same open. -/
theorem ιExtStalkFun_germ_smul (U : Opens X) (hx : x ∈ U)
    (a : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) (b : F.obj (op U)) :
    ιExtStalkFun F x (R.germ U x hx a • TopCat.Presheaf.germ F.presheaf U x hx b) =
      R.germ U x hx a • ιExtStalkFun F x (TopCat.Presheaf.germ F.presheaf U x hx b) := by
  have h₁ : ιExtStalkFun F x (R.germ U x hx a • TopCat.Presheaf.germ F.presheaf U x hx b) =
      extAlgGerm F x U hx (ExteriorAlgebra.ι
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) (a • b)) := by
    rw [← F.germ_smul x U hx a b]
    exact ιExtStalkFun_germ F x U hx (a • b)
  have h₂ : ExteriorAlgebra.ι ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
        (M := F.obj (op U)) (a • b) =
      algebraMap ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
          (ExteriorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
            (F.obj (op U))) a *
        ExteriorAlgebra.ι ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) b := by
    rw [map_smul, Algebra.smul_def]
  rw [h₁, h₂, map_mul (extAlgGerm F x U hx), ιExtStalkFun_germ, Algebra.smul_def,
    algebraMap_extStalkAlgebra_germ]

/-- `ιExtStalkFun` is `R_x`-equivariant. -/
theorem ιExtStalkFun_smul (r : ↑(R.stalk x)) (m : ↑(TopCat.Presheaf.stalk F.presheaf x)) :
    ιExtStalkFun F x (r • m) = r • ιExtStalkFun F x m := by
  obtain ⟨U, hU, r₀, m₀, rfl, rfl⟩ := exists_germ_eq_germ_eq R F.presheaf r m
  exact ιExtStalkFun_germ_smul F x U hU _ _

/-- The degree-one generator on stalks: the linear map from the stalk of `F` to the stalk of the
presheaf of sectionwise exterior algebras. -/
noncomputable def ιExtStalkL :
    ↑(TopCat.Presheaf.stalk F.presheaf x) →ₗ[↑(R.stalk x)] ↑((extAlg F).stalk x) where
  toFun := ιExtStalkFun F x
  map_add' m m' := map_add _ m m'
  map_smul' r m := ιExtStalkFun_smul F x r m

/-- `ιExtStalkL` sends the germ of `m` to the germ of `ExteriorAlgebra.ι _ m`. -/
@[simp]
theorem ιExtStalkL_germ (U : Opens X) (hx : x ∈ U) (m : F.obj (op U)) :
    ιExtStalkL F x (TopCat.Presheaf.germ F.presheaf U x hx m) =
      extAlgGerm F x U hx (ExteriorAlgebra.ι
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) m) :=
  ιExtStalkFun_germ F x U hx m

/-- The degree-one generator on stalks is square-zero on a germ, which is where it is true for a
reason: the generator of a germ is the germ of a generator, and `ExteriorAlgebra.ι_sq_zero` holds
sectionwise, so the square is the germ of zero. -/
theorem ιExtStalkL_germ_sq_zero (U : Opens X) (hx : x ∈ U) (m : F.obj (op U)) :
    ιExtStalkL F x (TopCat.Presheaf.germ F.presheaf U x hx m) *
      ιExtStalkL F x (TopCat.Presheaf.germ F.presheaf U x hx m) = 0 := by
  rw [ιExtStalkL_germ, ← map_mul (extAlgGerm F x U hx), ExteriorAlgebra.ι_sq_zero, map_zero]

/-- **The degree-one generator on stalks is square-zero.** This is the side condition
`ExteriorAlgebra.lift` carries and `SymmetricAlgebra.lift` does not. Every element of the stalk
of `F` is a germ, and on germs this is `ιExtStalkL_germ_sq_zero`.

The germ case is a separate declaration, not a `have` inside this proof. The section `m₀` that
`TopCat.Presheaf.exists_germ_eq` produces is typed `F.presheaf.obj (op U)`, while the `m` of
`ιExtStalkL_germ` is typed `F.obj (op U)`; the two are definitionally equal, so a goal mixing
them elaborates but is not type-correct at `implicit` transparency, and `rw` then refuses to
rewrite `ExteriorAlgebra.ι_sq_zero` underneath. Stating the germ case where it *is* type-correct
and crossing the boundary once, with the defeq-tolerant `exact`, avoids that entirely. -/
theorem ιExtStalkL_sq_zero (m : ↑(TopCat.Presheaf.stalk F.presheaf x)) :
    ιExtStalkL F x m * ιExtStalkL F x m = 0 := by
  obtain ⟨U, hU, m₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf m
  exact ιExtStalkL_germ_sq_zero F x U hU m₀

/-- The algebra map from the exterior algebra of the stalk to the stalk of the presheaf of
sectionwise exterior algebras, induced by the degree-one generator on stalks. -/
noncomputable def extAlgStalkLift :
    ExteriorAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x) →ₐ[↑(R.stalk x)]
      ↑((extAlg F).stalk x) :=
  ExteriorAlgebra.lift ↑(R.stalk x) ⟨ιExtStalkL F x, ιExtStalkL_sq_zero F x⟩

/-- `extAlgStalkLift` restricts to `ιExtStalkL` on degree-one elements. -/
@[simp]
theorem extAlgStalkLift_ι (m : ↑(TopCat.Presheaf.stalk F.presheaf x)) :
    extAlgStalkLift F x (ExteriorAlgebra.ι _ m) = ιExtStalkL F x m :=
  ExteriorAlgebra.lift_ι_apply _ (ιExtStalkL F x) (ιExtStalkL_sq_zero F x) m

/-! ### The two base-change maps are mutually inverse -/

/-- `extAlgStalkDesc` sends the germ of the scalar `r` to the scalar given by the germ of `r`. -/
@[simp]
theorem extAlgStalkDesc_extAlgGerm_algebraMap (U : Opens X) (hU : x ∈ U)
    (r : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) :
    extAlgStalkDesc F x (extAlgGerm F x U hU
        (algebraMap ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
          (ExteriorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
            (F.obj (op U))) r)) =
      algebraMap ↑(R.stalk x)
        (ExteriorAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x))
        (R.germ U x hU r) := by
  rw [extAlgStalkDesc_germ]
  exact ExteriorAlgebra.mapₛₗ_algebraMap _ _ r

/-- `extAlgStalkDesc` sends the germ of `ExteriorAlgebra.ι _ m` to `ExteriorAlgebra.ι _` of the
germ of `m`. -/
@[simp]
theorem extAlgStalkDesc_extAlgGerm_ι (U : Opens X) (hU : x ∈ U) (m : F.obj (op U)) :
    extAlgStalkDesc F x (extAlgGerm F x U hU
        (ExteriorAlgebra.ι ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) m)) =
      ExteriorAlgebra.ι ↑(R.stalk x) (TopCat.Presheaf.germ F.presheaf U x hU m) := by
  rw [extAlgStalkDesc_germ]
  exact ExteriorAlgebra.mapₛₗ_ι _ _ m

/-- `extAlgStalkLift` is a left inverse of `extAlgStalkDesc` on germs. -/
theorem extAlgStalkLift_extAlgStalkDesc_germ (U : Opens X) (hU : x ∈ U)
    (y : ExteriorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
      (F.obj (op U))) :
    extAlgStalkLift F x (extAlgStalkDesc F x (extAlgGerm F x U hU y)) =
      extAlgGerm F x U hU y := by
  have key : (extAlgStalkLift F x).toRingHom.comp
      (((extAlgStalkDesc F x).hom).comp (extAlgGerm F x U hU)) = extAlgGerm F x U hU := by
    refine ExteriorAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
    · exact ((congrArg (fun z => extAlgStalkLift F x z)
          (extAlgStalkDesc_extAlgGerm_algebraMap F x U hU r)).trans
        ((extAlgStalkLift F x).commutes (R.germ U x hU r))).trans
        (algebraMap_extStalkAlgebra_germ F x U hU r)
    · exact ((congrArg (fun z => extAlgStalkLift F x z)
          (extAlgStalkDesc_extAlgGerm_ι F x U hU m)).trans
        (extAlgStalkLift_ι F x (TopCat.Presheaf.germ F.presheaf U x hU m))).trans
        (ιExtStalkL_germ F x U hU m)
  exact DFunLike.congr_fun key y

/-- `extAlgStalkLift` is a left inverse of `extAlgStalkDesc`. -/
theorem extAlgStalkLift_extAlgStalkDesc (z : ↑((extAlg F).stalk x)) :
    extAlgStalkLift F x (extAlgStalkDesc F x z) = z := by
  obtain ⟨U, hU, y, rfl⟩ := TopCat.Presheaf.exists_germ_eq (extAlg F) z
  exact extAlgStalkLift_extAlgStalkDesc_germ F x U hU y

/-- `extAlgStalkLift` is a right inverse of `extAlgStalkDesc`. -/
theorem extAlgStalkDesc_extAlgStalkLift
    (z : ExteriorAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)) :
    extAlgStalkDesc F x (extAlgStalkLift F x z) = z := by
  have key : ((extAlgStalkDesc F x).hom).comp (extAlgStalkLift F x).toRingHom =
      RingHom.id (ExteriorAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)) := by
    refine ExteriorAlgebra.ringHom_ext (fun s => ?_) (fun m => ?_)
    · obtain ⟨U, hU, r, rfl⟩ := R.exists_germ_eq s
      exact ((congrArg (fun z => extAlgStalkDesc F x z)
            (((extAlgStalkLift F x).commutes (R.germ U x hU r)).trans
              (algebraMap_extStalkAlgebra_germ F x U hU r))).trans
          (extAlgStalkDesc_extAlgGerm_algebraMap F x U hU r))
    · obtain ⟨U, hU, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf m
      exact ((congrArg (fun z => extAlgStalkDesc F x z)
            ((extAlgStalkLift_ι F x (TopCat.Presheaf.germ F.presheaf U x hU b)).trans
              (ιExtStalkL_germ F x U hU b))).trans
          (extAlgStalkDesc_extAlgGerm_ι F x U hU b))
  exact DFunLike.congr_fun key z

/-- **The exterior algebra commutes with stalks.** The stalk at `x` of the presheaf of
sectionwise exterior algebras of `F` is the exterior algebra of the stalk of `F` over the stalk
of the presheaf of rings. -/
noncomputable def extAlgStalkRingEquiv :
    ↑((extAlg F).stalk x) ≃+*
      ExteriorAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x) :=
  RingEquiv.ofBijective (extAlgStalkDesc F x).hom
    ⟨Function.LeftInverse.injective (extAlgStalkLift_extAlgStalkDesc F x),
      Function.RightInverse.surjective (extAlgStalkDesc_extAlgStalkLift F x)⟩

/-- `extAlgStalkDesc` is injective. -/
theorem extAlgStalkDesc_injective : Function.Injective (extAlgStalkDesc F x) :=
  Function.LeftInverse.injective (extAlgStalkLift_extAlgStalkDesc F x)

/-! ### The stalk of the presheaf of sectionwise exterior powers -/

/-- The cocone on the diagram computing the stalk of `extPow n F` whose component at an open
neighbourhood `U` of `x` is base change of the `n`-th exterior power along the germ maps. -/
noncomputable def extPowStalkCocone (n : ℕ) :
    Limits.Cocone ((OpenNhds.inclusion x).op ⋙ (extPow n F).presheaf) where
  pt := AddCommGrpCat.of
    (⋀[↑(R.stalk x)]^n ↑(TopCat.Presheaf.stalk F.presheaf x))
  ι :=
    { app := fun U => AddCommGrpCat.ofHom
        (ExteriorAlgebra.powMapₛₗ n (R.germ U.unop.1 x U.unop.2).hom
          (germₛₗ F x U.unop.1 U.unop.2)).toAddMonoidHom
      naturality := fun U V f => by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun y => Subtype.ext ?_)
        exact (ExteriorAlgebra.mapₛₗ_eq_comp
          (F.restrictₛₗ ((OpenNhds.inclusion x).op.map f))
          (germₛₗ F x V.unop.1 V.unop.2) (germₛₗ F x U.unop.1 U.unop.2)
          (fun r => (TopCat.Presheaf.germ_res_apply' R
            ((OpenNhds.inclusion x).op.map f) x V.unop.2 r).symm)
          (fun m => (TopCat.Presheaf.germ_res_apply' F.presheaf
            ((OpenNhds.inclusion x).op.map f) x V.unop.2 m).symm) _).symm }

/-- Base change of the `n`-th exterior power along the germ maps, out of the stalk of the
presheaf of sectionwise exterior powers. -/
noncomputable def extPowStalkDesc (n : ℕ) :
    TopCat.Presheaf.stalk (extPow n F).presheaf x ⟶ AddCommGrpCat.of
      (⋀[↑(R.stalk x)]^n ↑(TopCat.Presheaf.stalk F.presheaf x)) :=
  Limits.colimit.desc _ (extPowStalkCocone F x n)

/-- The underlying function of `extPowStalkDesc`, with its codomain spelled as the exterior
power of the stalk. -/
noncomputable def extPowStalkFun (n : ℕ)
    (t : ↑(TopCat.Presheaf.stalk (extPow n F).presheaf x)) :
    ⋀[↑(R.stalk x)]^n ↑(TopCat.Presheaf.stalk F.presheaf x) :=
  extPowStalkDesc F x n t

/-- On the germ of a section `y`, `extPowStalkFun` is base change of `y` along the germ maps. -/
@[simp]
theorem extPowStalkFun_germ (n : ℕ) (U : Opens X) (hx : x ∈ U) (y : (extPow n F).obj (op U)) :
    extPowStalkFun F x n (TopCat.Presheaf.germ (extPow n F).presheaf U x hx y) =
      ExteriorAlgebra.powMapₛₗ n (R.germ U x hx).hom (germₛₗ F x U hx) y := by
  have h := Limits.colimit.ι_desc (extPowStalkCocone F x n) (op ⟨U, hx⟩)
  exact congrArg (fun g : (extPow n F).presheaf.obj (op U) ⟶ (extPowStalkCocone F x n).pt =>
    ConcreteCategory.hom g y) h

/-- `extPowStalkFun` commutes with scalar multiplication of a germ by a germ over the same open. -/
theorem extPowStalkFun_germ_smul (n : ℕ) (U : Opens X) (hx : x ∈ U)
    (a : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) (y : (extPow n F).obj (op U)) :
    extPowStalkFun F x n (R.germ U x hx a •
        TopCat.Presheaf.germ (extPow n F).presheaf U x hx y) =
      R.germ U x hx a •
        extPowStalkFun F x n (TopCat.Presheaf.germ (extPow n F).presheaf U x hx y) := by
  rw [← (extPow n F).germ_smul x U hx a y, extPowStalkFun_germ, extPowStalkFun_germ]
  exact map_smulₛₗ (ExteriorAlgebra.powMapₛₗ n (R.germ U x hx).hom (germₛₗ F x U hx)) a y

/-- `extPowStalkFun` is `R_x`-equivariant. -/
theorem extPowStalkFun_smul (n : ℕ) (r : ↑(R.stalk x))
    (t : ↑(TopCat.Presheaf.stalk (extPow n F).presheaf x)) :
    extPowStalkFun F x n (r • t) = r • extPowStalkFun F x n t := by
  obtain ⟨U, hU, r₀, y₀, rfl, rfl⟩ := exists_germ_eq_germ_eq R (extPow n F).presheaf r t
  exact extPowStalkFun_germ_smul F x n U hU _ _

/-- **The comparison map of the exterior assertion of Stacks 01CG and 01CH at a point**: base
change of the `n`-th exterior power along the germ maps, as a linear map from the stalk of the
presheaf of sectionwise exterior powers of `F` to the `n`-th exterior power of the stalk of
`F`. -/
noncomputable def extPowStalkL (n : ℕ) :
    ↑(TopCat.Presheaf.stalk (extPow n F).presheaf x) →ₗ[↑(R.stalk x)]
      ⋀[↑(R.stalk x)]^n ↑(TopCat.Presheaf.stalk F.presheaf x) where
  toFun := extPowStalkFun F x n
  map_add' t t' := map_add _ t t'
  map_smul' r t := extPowStalkFun_smul F x n r t

/-- On the germ of a section `y`, `extPowStalkL` is base change of `y` along the germ maps. -/
@[simp]
theorem extPowStalkL_germ (n : ℕ) (U : Opens X) (hx : x ∈ U) (y : (extPow n F).obj (op U)) :
    extPowStalkL F x n (TopCat.Presheaf.germ (extPow n F).presheaf U x hx y) =
      ExteriorAlgebra.powMapₛₗ n (R.germ U x hx).hom (germₛₗ F x U hx) y :=
  extPowStalkFun_germ F x n U hx y

/-! ### The comparison map is bijective -/

/-- If base change of a local section of `⋀ⁿ F` along the germ maps vanishes, then its germ
vanishes. This is the injectivity half of the exterior assertion of Stacks 01CG/01CH at a point:
it is where the exterior algebra has to be known to commute with the filtered colimit computing
the stalk, and it is deduced from `extAlgStalkDesc_injective`. -/
theorem germ_eq_zero_of_extMapₛₗ_eq_zero (n : ℕ) (U : Opens X) (hU : x ∈ U)
    (y : ⋀[(R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)]^n (F.obj (op U)))
    (h : ExteriorAlgebra.mapₛₗ (R.germ U x hU).hom (germₛₗ F x U hU)
      (y : ExteriorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
        (F.obj (op U))) = 0) :
    TopCat.Presheaf.germ (extPow n F).presheaf U x hU y = 0 := by
  have h0 : extAlgGerm F x U hU
      (y : ExteriorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
        (F.obj (op U))) = extAlgGerm F x U hU 0 := by
    refine extAlgStalkDesc_injective F x ?_
    rw [extAlgStalkDesc_germ, extAlgStalkDesc_germ, h, map_zero]
  obtain ⟨W, hW, iU, iV, heq⟩ := TopCat.Presheaf.germ_eq (extAlg F) x hU hU
    (y : ExteriorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
      (F.obj (op U))) 0
    ((extAlgGerm_eq F x U hU _).symm.trans (h0.trans (extAlgGerm_eq F x U hU 0)))
  have hy : (extPow n F).presheaf.map iU.op y = 0 :=
    Subtype.ext (heq.trans (map_zero _))
  refine (TopCat.Presheaf.germ_res_apply (extPow n F).presheaf iU x hW y).symm.trans ?_
  rw [hy, map_zero]

/-- `extPowStalkL` is injective. -/
theorem extPowStalkL_injective (n : ℕ) : Function.Injective (extPowStalkL F x n) := by
  refine (injective_iff_map_eq_zero (extPowStalkL F x n)).2 fun t ht => ?_
  obtain ⟨U, hU, y, rfl⟩ := TopCat.Presheaf.exists_germ_eq (extPow n F).presheaf t
  refine germ_eq_zero_of_extMapₛₗ_eq_zero F x n U hU y ?_
  exact (ExteriorAlgebra.powMapₛₗ_coe n (R.germ U x hU).hom (germₛₗ F x U hU) y).symm.trans
    (congrArg Subtype.val ((extPowStalkL_germ F x n U hU y).symm.trans ht))

/-- **The comparison on a wedge of local sections.** The germ of `s₀ ∧ ⋯ ∧ s_{n-1}` goes to the
wedge of the germs. Since such wedges span the exterior power
(`ExteriorAlgebra.ιMulti_span_fixedDegree`), this determines the comparison map, and it is what
makes the isomorphism of Stacks 01CH canonical rather than merely existent. -/
theorem extPowStalkL_germ_ιMulti (n : ℕ) (U : Opens X) (hx : x ∈ U)
    (s : Fin n → F.obj (op U)) :
    extPowStalkL F x n (TopCat.Presheaf.germ (extPow n F).presheaf U x hx
        (exteriorPower.ιMulti
          ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) n s)) =
      exteriorPower.ιMulti ↑(R.stalk x) n
        fun i => TopCat.Presheaf.germ F.presheaf U x hx (s i) := by
  refine Subtype.ext ?_
  refine (congrArg Subtype.val (extPowStalkL_germ F x n U hx _)).trans ?_
  refine (ExteriorAlgebra.powMapₛₗ_coe n (R.germ U x hx).hom (germₛₗ F x U hx) _).trans ?_
  refine Eq.trans (congrArg (ExteriorAlgebra.mapₛₗ (R.germ U x hx).hom (germₛₗ F x U hx))
    (exteriorPower.ιMulti_apply_coe _ n s)) ?_
  refine (ExteriorAlgebra.mapₛₗ_ιMulti (R.germ U x hx).hom (germₛₗ F x U hx) n s).trans ?_
  exact (exteriorPower.ιMulti_apply_coe ↑(R.stalk x) n _).symm

/-- `extPowStalkL` is surjective. -/
theorem extPowStalkL_surjective (n : ℕ) : Function.Surjective (extPowStalkL F x n) := by
  have hwedge : ∀ s : Fin n → ↑(TopCat.Presheaf.stalk F.presheaf x),
      ExteriorAlgebra.ιMulti ↑(R.stalk x) n s ∈
        Submodule.map
          (⋀[↑(R.stalk x)]^n ↑(TopCat.Presheaf.stalk F.presheaf x)).subtype
          (LinearMap.range (extPowStalkL F x n)) := by
    intro s
    choose U hU t ht using fun i : Fin n => TopCat.Presheaf.exists_germ_eq F.presheaf (s i)
    have hW : x ∈ (⨅ i, U i : Opens X) := by
      have h : x ∈ (↑(⨅ i, U i) : Set X) := by
        rw [Opens.coe_iInf]
        exact Set.mem_iInter.2 hU
      exact h
    refine Submodule.mem_map.2 ⟨extPowStalkL F x n
      (TopCat.Presheaf.germ (extPow n F).presheaf (⨅ i, U i : Opens X) x hW
        (exteriorPower.ιMulti
          ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op (⨅ i, U i : Opens X))) n
          fun i => F.map (homOfLE (iInf_le U i)).op (t i))), ⟨_, rfl⟩, ?_⟩
    refine Eq.trans (congrArg Subtype.val (extPowStalkL_germ_ιMulti F x n
      (⨅ i, U i : Opens X) hW (fun i => F.map (homOfLE (iInf_le U i)).op (t i)))) ?_
    refine (exteriorPower.ιMulti_apply_coe ↑(R.stalk x) n _).trans ?_
    exact congrArg (ExteriorAlgebra.ιMulti ↑(R.stalk x) n) (funext fun i =>
      (TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE (iInf_le U i)) x hW (t i)).trans (ht i))
  have hspan : ∀ q ∈ Submodule.span ↑(R.stalk x)
        (Set.range (ExteriorAlgebra.ιMulti ↑(R.stalk x) n
          (M := ↑(TopCat.Presheaf.stalk F.presheaf x)))),
      q ∈ Submodule.map
        (⋀[↑(R.stalk x)]^n ↑(TopCat.Presheaf.stalk F.presheaf x)).subtype
        (LinearMap.range (extPowStalkL F x n)) := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem w hw => obtain ⟨s, rfl⟩ := hw; exact hwedge s
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul r a _ ha => exact Submodule.smul_mem _ r ha
  intro z
  obtain ⟨w, hw, hwz⟩ := hspan (z : ExteriorAlgebra ↑(R.stalk x)
    ↑(TopCat.Presheaf.stalk F.presheaf x))
    (by rw [ExteriorAlgebra.ιMulti_span_fixedDegree]; exact z.2)
  obtain ⟨v, hv⟩ := hw
  exact ⟨v, Subtype.ext ((congrArg Subtype.val hv).trans hwz)⟩

/-- **Exterior powers commute with stalks.** For a presheaf of modules `F` over a presheaf of
commutative rings `R` on a topological space, the stalk at `x` of the presheaf of sectionwise
exterior powers `U ↦ ⋀ⁿ_{R(U)}(F(U))` is the `n`-th exterior power of the stalk `F_x` over the
stalk ring `R_x`. The isomorphism is base change along the germ maps, and
`extPowStalkL_germ_ιMulti` identifies it on germs of wedges of local sections. -/
noncomputable def extPowStalkEquiv (n : ℕ) :
    ↑(TopCat.Presheaf.stalk (extPow n F).presheaf x) ≃ₗ[↑(R.stalk x)]
      ⋀[↑(R.stalk x)]^n ↑(TopCat.Presheaf.stalk F.presheaf x) :=
  LinearEquiv.ofBijective (extPowStalkL F x n)
    ⟨extPowStalkL_injective F x n, extPowStalkL_surjective F x n⟩

/-- `extPowStalkEquiv` is `extPowStalkL` as a function. -/
@[simp]
theorem extPowStalkEquiv_apply (n : ℕ) (t : ↑(TopCat.Presheaf.stalk (extPow n F).presheaf x)) :
    extPowStalkEquiv F x n t = extPowStalkL F x n t := rfl

/-! ### Transport along a morphism which is a stalk isomorphism -/

/-- **The stalk of a sheafification of the sectionwise exterior powers.** If `φ` exhibits `Q` as
having the same stalks as the presheaf `U ↦ ⋀ⁿ_{R(U)}(F(U))` — which the sheafification unit
does, by `PresheafOfModules.isIso_stalkFunctor_map_toSheafify` — then the stalk of `Q` at `x` is
`⋀ⁿ_{R_x}(F_x)`.

This is the form the exterior assertion of Stacks Tag 01CH is consumed in: the degree-`n`
exterior power of a sheaf of modules on a ringed space *is* the sheafification of the sectionwise
exterior powers, so taking `Q` to be that sheafification and `φ` its unit computes the stalk of
`⋀ⁿ F`. The isomorphism is pinned by `extPowStalkEquivOfStalkIso_germ_ιMulti`, which is the
reason this and not an abstract uniqueness isomorphism is what the tag asserts. -/
@[stacks 01CH "the exterior assertion in each graded degree `n`: `(⋀ⁿ M)ₓ ≅ ⋀ⁿ(Mₓ)`, with the \
isomorphism pinned by `extPowStalkEquivOfStalkIso_germ_ιMulti` as the map carrying the germ of a \
wedge of local sections to the wedge of their germs. The symmetric assertion is \
`PresheafOfModules.symPowStalkEquivOfStalkIso`. The graded-to-ungraded passage is not proved \
here; it is `SheafOfModules.exteriorAlgebra_stalk` in \
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded`, which is the ungraded \
`⋀(M)ₓ ≅ ⋀(Mₓ)` that the source actually asserts.", ega "0 4.1.5" "more general"]
noncomputable def extPowStalkEquivOfStalkIso (n : ℕ)
    {Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (φ : extPow n F ⟶ Q)
    (h : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((toPresheaf _).map φ))) :
    ↑(TopCat.Presheaf.stalk Q.presheaf x) ≃ₗ[↑(R.stalk x)]
      ⋀[↑(R.stalk x)]^n ↑(TopCat.Presheaf.stalk F.presheaf x) :=
  (stalkLinearEquiv x φ h).symm.trans (extPowStalkEquiv F x n)

/-- **The comparison of `extPowStalkEquivOfStalkIso` on a wedge of local sections**: the germ of
the image of `s₀ ∧ ⋯ ∧ s_{n-1}` goes to the wedge of the germs. Together with
`ExteriorAlgebra.ιMulti_span_fixedDegree` this determines the isomorphism. -/
theorem extPowStalkEquivOfStalkIso_germ_ιMulti (n : ℕ)
    {Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (φ : extPow n F ⟶ Q)
    (h : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((toPresheaf _).map φ)))
    (U : Opens X) (hx : x ∈ U) (s : Fin n → F.obj (op U)) :
    extPowStalkEquivOfStalkIso F x n φ h (TopCat.Presheaf.germ Q.presheaf U x hx
        (φ.app (op U) (exteriorPower.ιMulti
          ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) n s))) =
      exteriorPower.ιMulti ↑(R.stalk x) n
        fun i => TopCat.Presheaf.germ F.presheaf U x hx (s i) := by
  refine Eq.trans (congrArg (extPowStalkEquiv F x n)
    ((stalkLinearEquiv x φ h).symm_apply_eq.2 (stalkMapL_germ x φ U hx _).symm)) ?_
  exact extPowStalkL_germ_ιMulti F x n U hx s

end PresheafOfModules

end
