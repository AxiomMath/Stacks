module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IdealTorsionFree
public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Basic
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.StalkLength
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact

/-!
# The length of a module at a point, across the two spellings of the stalk

`Stacks.AlgebraicGeometry.ComponentDegrees.stalkLength` is the length of the stalk of a module
over the stalk of `AlgebraicGeometry.Scheme.ringCatSheaf`, the `RingCat`-valued structure sheaf.
Every statement that *feeds* the dévissage of [Stacks, Tag 0AYW] instead measures the stalk over
the `CommRingCat`-valued local ring `X.presheaf.stalk x`: the multiplicity of a component is
`Module.length (X.presheaf.stalk ξ) (X.presheaf.stalk ξ)`, and the fibre rank of a module at a
generic point is a `Module.finrank` over that same ring. This file identifies the two, and draws
the two consequences the dévissage consumes.

## Main results

The elided prefix is `Stacks.AlgebraicGeometry.ComponentDegrees`.

* `stalkLength_eq_length_grpStalk` — **the identification.** `stalkLength ℱ x` is the length of
  the abelian-group stalk `ℱ_x` over `X.presheaf.stalk x`, with its canonical germ-compatible
  module structure.
* `stalkLength_unit` and `stalkLength_unit_eq_componentMultiplicity` — the length of the
  structure sheaf at `x` is the length of the local ring over itself; at a generic point of a
  one-dimensional component of a scheme proper over a field that is the multiplicity of the
  component.
* `stalkLength_eq_fiberRank_genericPoint` — at the generic point of an integral scheme the
  length of a module of finite type is its fibre rank there.
* `componentMultiplicity_eq_sum_stalkLength_of_filtration` — **the weights of a dévissage of
  `𝒪_X` add up to the multiplicity of a component**: along a finite monotone chain of
  subobjects of `𝒪_X` from `⊥` to `⊤`, the sum at `ξ` of the lengths of the successive
  quotients is `componentMultiplicity X ξ`.

## Implementation notes

**Why this is not a `rw`.** The two stalks of the structure sheaf — the `RingCat`-valued
`TopCat.Presheaf.stalk X.ringCatSheaf.obj x` and the `CommRingCat`-valued
`X.presheaf.stalk x` — are different filtered colimits of the same diagram, identified by
`Stacks.RingedSpace.ringStalkCommIso`. That isomorphism is surjective, so
`length_eq_of_surjective_smul_eq` transfers the length as soon as the two scalar actions on the
single abelian group `ℱ_x` are related by it, which is the germ computation of the proof below.
Every `rw` that closes that computation fails with *"the target expression is not type-correct
under the `implicit` transparency level"*, because `AlgebraicGeometry.Scheme.ringCatSheaf` is a
reducible `abbrev` while `structureSheafRing` is only `@[instance_reducible]`, so the motive `rw`
builds does not typecheck at the transparency it uses. The proof therefore never rewrites across
the seam: each side of the identity is computed into the common value
`germ_x(a • n)` by a separate `have`, and the two are joined by `Eq.trans`, which checks
conversion at default transparency where the two spellings do agree. For the same reason the
three module structures in play are supplied as explicit arguments — `letI iR`, `letI iS` and
the `@`-applications — rather than left to instance search, which runs at `instances`
transparency and cannot see through `CategoryTheory.sheafCompose`.

**Three module structures, two of them equal.** The abelian group `ℱ_x` carries
`Module (TopCat.Presheaf.stalk X.ringCatSheaf.obj x)` from
`AlgebraicGeometry.SheafOfModules.stalkObj`, and two structures over `X.presheaf.stalk x`:
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`, a global instance built by hand, and
`Stacks.SheafOfModules.FlatShortExact.stalkModule`, Mathlib's presheaf-of-modules stalk
instance. Both are germ-compatible, so they are equal — `stalkModule_eq_flatStalkModule`, which
is `Stacks.SheafOfModules.FlatShortExact.germCompatibleModule_unique`. The identification is
stated at the first, because that is where
`Stacks.IdealTorsion.unitStalkLinearEquiv` trivialises the stalk of `𝒪_X`; it is used at the
second, because that is where `AlgebraicGeometry.Scheme.Modules.fiberRank` is evaluated.

**No Stacks attribute is attached.** Nothing of [Stacks, Tag 0AYW] is proved here; this is the
bridge its dévissage crosses, and the two statements it crosses to.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 00IX](https://stacks.math.columbia.edu/tag/00IX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.ComponentDegrees

/-! ### The identification of the two spellings -/

/-- **The two germ-compatible module structures on the stalk agree.** Both
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` and
`Stacks.SheafOfModules.FlatShortExact.stalkModule` make every germ map semilinear over the ring
germ, and a germ-compatible structure on a stalk is unique. -/
theorem stalkModule_eq_flatStalkModule {X : Scheme.{u}} (F : X.Modules) (x : X) :
    stalkModule X.toRingedSpace F.val x =
      Stacks.SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace) F x :=
  Stacks.SheafOfModules.FlatShortExact.germCompatibleModule_unique
    (X := X.toRingedSpace) F x _ _
    (fun U hx r m => stalkModule_germ_smul X.toRingedSpace F.val x U hx r m)
    (Stacks.SheafOfModules.FlatShortExact.stalkModule_germCompatible
      (X := X.toRingedSpace) F x)

/-- **The length of `ℱ` at `x` is the length of the abelian-group stalk `ℱ_x` over the local
ring `X.presheaf.stalk x`.** The two stalks of the structure sheaf are identified by
`Stacks.RingedSpace.ringStalkCommIso`, which is surjective, and the two actions it relates agree
on germs. -/
theorem stalkLength_eq_length_grpStalk {X : Scheme.{u}} (F : X.Modules) (x : X) :
    stalkLength F x =
      @Module.length (X.presheaf.stalk x) (grpStalk X.toRingedSpace F.val x) _ _
        (stalkModule X.toRingedSpace F.val x) := by
  let iR : Module (TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x)
      (grpStalk X.toRingedSpace F.val x) :=
    (SheafOfModules.stalkObj X.ringCatSheaf x F).isModule
  let iS : Module (X.presheaf.stalk x) (grpStalk X.toRingedSpace F.val x) :=
    stalkModule X.toRingedSpace F.val x
  have hsurj : Function.Surjective
      (Stacks.RingedSpace.ringStalkCommIso X.toRingedSpace x).hom.hom :=
    (ConcreteCategory.bijective_of_isIso
      (Stacks.RingedSpace.ringStalkCommIso X.toRingedSpace x).hom).surjective
  refine @length_eq_of_surjective_smul_eq
    (TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x)
    (X.presheaf.stalk x) _ _
    (Stacks.RingedSpace.ringStalkCommIso X.toRingedSpace x).hom.hom hsurj
    (grpStalk X.toRingedSpace F.val x) _ iR iS ?_
  intro ρ s
  obtain ⟨Ur, hxr, a, ha⟩ := TopCat.Presheaf.exists_germ_eq X.ringCatSheaf.obj ρ
  obtain ⟨Um, hxm, n, hn⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf s
  set U : Opens X := Ur ⊓ Um
  have hxU : x ∈ U := ⟨hxr, hxm⟩
  let iUr : U ⟶ Ur := homOfLE inf_le_left
  let iUm : U ⟶ Um := homOfLE inf_le_right
  let a' : X.ringCatSheaf.obj.obj (op U) := (X.ringCatSheaf.obj.map iUr.op).hom a
  let n' : F.val.obj (op U) := (F.val.presheaf.map iUm.op).hom n
  have hga : (TopCat.Presheaf.germ (C := RingCat.{u}) X.ringCatSheaf.obj U x hxU).hom a' = ρ :=
    (TopCat.Presheaf.germ_res_apply _ iUr x hxU a).trans ha
  have hgn : (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) F.val.presheaf U x hxU).hom n'
      = s :=
    (TopCat.Presheaf.germ_res_apply _ iUm x hxU n).trans hn
  have hR : ρ • s
      = (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) F.val.presheaf U x hxU).hom (a' • n') := by
    rw [← hga, ← hgn]
    exact (SheafOfModules.germ_hom_smul X.ringCatSheaf x F.val U hxU a' n').symm
  have hφ : ((Stacks.RingedSpace.ringStalkCommIso X.toRingedSpace x).hom.hom ρ :
        X.presheaf.stalk x)
      = (X.presheaf.germ U x hxU).hom a' := by
    rw [← hga]
    exact Stacks.RingedSpace.ringStalkCommIso_germ X.toRingedSpace x U hxU a'
  have hL : ∀ t : X.presheaf.stalk x, t = (X.presheaf.germ U x hxU).hom a' →
      t • s = (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) F.val.presheaf U x hxU).hom
        (a' • n') := by
    rintro t rfl
    rw [← hgn]
    exact (stalkModule_germ_smul X.toRingedSpace F.val x U hxU a' n').symm
  exact (hL _ hφ).trans hR.symm

/-- The identification of `stalkLength_eq_length_grpStalk`, at Mathlib's stalk module
structure. -/
theorem stalkLength_eq_length_flatStalk {X : Scheme.{u}} (F : X.Modules) (x : X) :
    stalkLength F x =
      @Module.length (X.presheaf.stalk x) (grpStalk X.toRingedSpace F.val x) _ _
        (Stacks.SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace) F x) :=
  (stalkLength_eq_length_grpStalk F x).trans
    (congrArg (fun i => @Module.length (X.presheaf.stalk x)
      (grpStalk X.toRingedSpace F.val x) _ _ i) (stalkModule_eq_flatStalkModule F x))

/-! ### The structure sheaf, and the multiplicity of a component -/

/-- **The length of the structure sheaf at `x` is the length of the local ring over itself.**
The stalk of `𝒪_X` as a module over itself is the local ring, by
`Stacks.IdealTorsion.unitStalkLinearEquiv`. -/
theorem stalkLength_unit {X : Scheme.{u}} (x : X) :
    stalkLength (SheafOfModules.unit X.ringCatSheaf) x =
      Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) :=
  (stalkLength_eq_length_grpStalk (SheafOfModules.unit X.ringCatSheaf) x).trans
    (Stacks.IdealTorsion.unitStalkLinearEquiv X.toRingedSpace x).length_eq

/-- **At a generic point of a one-dimensional component of a scheme proper over a field, the
length of the structure sheaf is the multiplicity of the component.** -/
theorem stalkLength_unit_eq_componentMultiplicity (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (ξ : genericPointsOne X) :
    stalkLength (SheafOfModules.unit X.ringCatSheaf) ξ.1 =
      (componentMultiplicity X ξ : ℕ∞) :=
  (stalkLength_unit ξ.1).trans (componentMultiplicity_cast k f ξ).symm

/-! ### The generic point of an integral scheme, and the fibre rank -/

/-- **At the generic point of an integral scheme the length of a module of finite type is its
fibre rank there.** The local ring at the generic point is the function field, so the length of a
finitely generated stalk over it is its dimension, and the base change defining the fibre rank
changes nothing. -/
theorem stalkLength_eq_fiberRank_genericPoint {Z : Scheme.{u}} [IsIntegral Z] (F : Z.Modules)
    [F.IsFiniteType] :
    stalkLength F (genericPoint (Z : Type u)) =
      (Scheme.Modules.fiberRank F (genericPoint (Z : Type u)) : ℕ∞) := by
  let iM : Module (Z.presheaf.stalk (genericPoint (Z : Type u)))
      (grpStalk Z.toRingedSpace F.val (genericPoint (Z : Type u))) :=
    Stacks.SheafOfModules.FlatShortExact.stalkModule (X := Z.toRingedSpace) F
      (genericPoint (Z : Type u))
  let : Field (ToType (Z.presheaf.stalk (genericPoint (Z : Type u)))) :=
    inferInstanceAs (Field Z.functionField)
  let : Module.Finite (Z.presheaf.stalk (genericPoint (Z : Type u)))
      (grpStalk Z.toRingedSpace F.val (genericPoint (Z : Type u))) :=
    _root_.SheafOfModules.finite_stalk Z.sheaf F (genericPoint (Z : Type u))
  refine (stalkLength_eq_length_flatStalk F (genericPoint (Z : Type u))).trans ?_
  rw [Module.length_eq_finrank]
  exact congrArg _ (Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk F).symm

/-! ### The weights of a dévissage add up to the multiplicity -/

/-- **The weights of a dévissage of `𝒪_X` add up to the multiplicity of a component.** If
`⊥ = G 0 ⊆ ⋯ ⊆ G n = ⊤` is a finite monotone chain of subobjects of a module isomorphic to the
structure sheaf — for instance the one [Stacks, Tag 01YF] produces for `𝒪_X` — then the sum at
the generic point `ξ` of a one-dimensional component of the lengths of its successive quotients
is the multiplicity of that component. This is the half of [Stacks, Tag 0AYW] that turns a
dévissage of `𝒪_X` into the weights of the component formula.

The module carrying the filtration is a variable rather than `SheafOfModules.unit
X.ringCatSheaf` itself, with the identification supplied as an isomorphism: at the literal unit
module the lattice instances of `⊥` and `⊤` on `CategoryTheory.Subobject` are beyond instance
search, while a dévissage obtained from [Stacks, Tag 01YF] carries them already. -/
theorem componentMultiplicity_eq_sum_stalkLength_of_filtration (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (ξ : genericPointsOne X)
    {F : X.Modules} (e : F ≅ SheafOfModules.unit X.ringCatSheaf) {n : ℕ}
    (G : Fin (n + 1) → Subobject F) (hG : Monotone G)
    (hstart : G 0 = ⊥) (hfinish : G (Fin.last n) = ⊤) :
    (componentMultiplicity X ξ : ℕ∞) =
      ∑ j : Fin n, stalkLength (filtrationQuotient G hG j) ξ.1 :=
  (((stalkLength_of_iso e ξ.1).trans
      (stalkLength_unit_eq_componentMultiplicity k f ξ)).symm).trans
    (stalkLength_eq_sum_of_subobject_filtration F G hG hstart hfinish ξ.1)

end Stacks.AlgebraicGeometry.ComponentDegrees

end
