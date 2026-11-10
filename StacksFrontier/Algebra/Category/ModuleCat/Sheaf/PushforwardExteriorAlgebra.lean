module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorDeterminantBundleIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceExteriorAlgebra
import StacksCore.Tactic.StacksAttribute

/-!
# Comparing an exterior algebra with the source site's own, along a pushforward of sites

Let `G : Cs ⥤ Ct` be a continuous and cocontinuous functor of sites, `O♯` a sheaf of commutative
rings on the target site, `M` a sheaf of modules over the underlying sheaf of rings, and `A` a
sheaf of graded algebras with a square-zero degree-one generator `gen : M ⟶ A.piece 1`. This
file provides the material for comparing the pushforward `G_*A` with a graded algebra of `G_*M`
on the source site, in a form that carries the **algebra structure** and not only a degreewise
isomorphism of sheaves of modules.

`Stacks.SheafOfModules.exteriorPowerPushforwardIso`
(`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras`) already compares
`G_*(⋀ⁿ M)` with `⋀ⁿ(G_*M)` for an arbitrary pair of exterior algebras, but it is assembled
from the two universal properties and carries no compatibility with the multiplication
`A.exterior.mul 1 n` or with the generator `A.exteriorGenerator`, which is what
`SheafOfModules.TensorExteriorSymmetricAlgebras.IsExteriorAnnihilated` is phrased in. This file
is the pushforward twin of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceExteriorAlgebra`, which does the same for the
restriction to a slice site: the comparison is made through the model both sides are
sheafifications of, the degreewise sheafification of the sectionwise exterior power, where it is
componentwise the identity, so the generator and the multiplication match on the nose.

## Main definitions

* `SheafOfModules.GradedAlgebra.pushforwardAlg`: the pushforward `G_*A` of a sheaf of graded
  algebras along a continuous functor of sites, with no change of scalars. It is
  `SheafOfModules.GradedAlgebra.pushforward` at the identity change of scalars, so that the
  pushed-forward sheaf of rings is the target rather than an argument.
* `SheafOfModules.pushforwardGen`: the degree-one generator pushed forward, a degree-one
  generator of `G_*A`.
* `SheafOfModules.pushforwardRestrictIso`, `extPowPushforwardPresheafIso` and
  `sectionwiseExtPowPushforwardIso`: the comparison of the source site's own sheafified
  sectionwise exterior power with the pushforward of the one over the target site, written as a
  composite of its legs.
* `SheafOfModules.exteriorPushforwardIso`: the comparison of `G_*A` with an arbitrary exterior
  algebra of `G_*M` on the source site, as the degreewise comparison of two algebras universal
  for the same property.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAnnihilatorPushforwardHom` and
  `exteriorAnnihilatorPushforward`: the morphism from the pushforward of `annₙ(M)` to
  `annₙ(G_*M)` induced by a generator- and multiplication-compatible comparison, and its
  instance at the canonical comparison.

## Main results

* `SheafOfModules.squareZero_pushforwardGen`: the pushed-forward generator is still square-zero.
* `SheafOfModules.pushforwardSheafifyHom_sheafifyUnit` and
  `sectionwiseExtPowPushforwardIso_hom_sheafifyUnit`: **the comparison carries the unit-image of
  a local section over an object `V` of the source site to the unit-image of that section over
  `G V`.** This is the computation that a compatibility with the algebra structure reduces to,
  both sides of such a compatibility being determined by their values on unit-images.
* `SheafOfModules.homogeneousProd_pushforward` and `exteriorDescSq_pushforward_app`: the ordered
  product of degree-one sections of `G_*A` is the ordered product in `A` over `G V`, and **the
  comparison homomorphism over the source site is the pushforward of the one over the target
  site**, read through `sectionwiseExtPowPushforwardIso`.
* `SheafOfModules.isIso_exteriorDescSq_pushforward_app`: for an exterior algebra `A` of `M` the
  comparison homomorphism is invertible in every degree; in a negative degree both sides are
  zero objects.
* `SheafOfModules.isExteriorAlgebra_pushforward`: **the pushforward of an exterior algebra of
  `M` is an exterior algebra of `G_*M`**, on the pushed-forward generator. This is the statement
  with the algebra structure that `Stacks.SheafOfModules.exteriorPowerPushforwardIso` does not
  carry.
* `SheafOfModules.exteriorPushforwardIso_generator`, `exteriorPushforwardIso_mul` and
  `exteriorPushforwardIso_one`: the resulting comparison is compatible with the generators, the
  multiplications and the units. They come from
  `SheafOfModules.GradedAlgebra.IsUniversal.pieceIso_generator`, `pieceIso_mul` and
  `pieceIso_one` with no further work, and they are what makes the hypotheses of
  `exteriorAnnihilatorPushforwardHom` dischargeable.
* `SheafOfModules.TensorExteriorSymmetricAlgebras`
  `.isExteriorAnnihilated_of_pushforwardComparison`: **a generator- and multiplication-compatible
  comparison across `G` carries exterior annihilated sections to exterior annihilated
  sections.**

## Implementation notes

**Why the restriction to a slice site and the pushforward are two developments and not one.**
`Stacks.SheafOfModules.SliceSheafification.sheafifyOverIso`,
`PresheafOfModules.extPowOverIso` and `Stacks.SheafOfModules.sectionwiseExteriorPowerOverIso`
are the cases `G := Over.forget U` of
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyIso`,
`PresheafOfModules.extPowPushforwardIso` and
`Stacks.SheafOfModules.sectionwiseExteriorPowerPushforwardIso`, and
`SheafOfModules.GradedAlgebra.over` is the case `G := Over.forget U` of
`GradedAlgebra.pushforwardAlg` here. Correspondingly every statement of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceExteriorAlgebra` is the case
`G := Over.forget U` of a statement here, with the same proof. Restating the slice file as
corollaries of this one would remove the duplication; it is not done here because
the slice statements are consumed and because the two spellings of the restricted sheaf of
rings, `R.over U` against `pushforwardRingSheaf (J.over U) (Over.forget U) R`, have to be
reconciled first.

**The same three expensive definitional unfoldings, in the same places.** The implementation
notes of the slice file apply verbatim.

1. The defeq `PresheafOfModules.sitePushforward G = presheafPushforwardFunctor` is `rfl` and
   cheap at an arbitrary presheaf of modules (`sitePushforward_eq_presheafPushforwardFunctor`),
   but at a **concrete** `PresheafOfModules.extPow` it is a query on the two module structures on
   `⋀ⁿ` and it exceeds the heartbeat budget. It is affordable inside the `≪≫` of
   `Stacks.SheafOfModules.sectionwiseExteriorPowerPushforwardIso`, where the two sides are
   sheafifications, and it is **not** affordable as the type of an argument: passing
   `Hom.app (extPowPushforwardIso G n M.val).inv V z` to
   `pushforwardSheafifyHom_sheafifyUnit` times out at `isDefEq`.
   `pushforwardRestrictIso` discharges the query once, abstractly, exactly as
   `SheafOfModules.sliceRestrictIso` does for the slice site, and
   `extPowPushforwardPresheafIso` is the leg every concrete use goes through.
2. `rw` cannot cross the two defeq-but-distinct spellings of the pushed-forward sheaf of rings,
   `pushforwardRingSheaf Js G (toRingCat Jt O♯)` and
   `toRingCat Js (Stacks.SheafOfModules.pushforwardCommRingSheaf Js G)`: the slice file's `rw`
   chain in `isExteriorAnnihilated_of_comparison` fails here with a target that is not
   type-correct at `implicit` transparency. The repair is the one the slice file documents for
   its own crossing — the chain is written in term mode, as `Eq.trans` of `congrArg`s, which is
   defeq-tolerant.
3. Every implicit argument is named at each application. In particular the sheaf of commutative
   rings of `TensorExteriorSymmetricAlgebras` must be supplied: with `G_*F` as the module
   argument, inferring it is the higher-order problem
   `toRingCat Js ?O♯ =?= pushforwardRingSheaf Js G (toRingCat Jt O♯)`, which does not resolve.
   This is the discipline recorded in
   `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras`.

**What a cross-site `determinantIsoOfComparison` would need, and why this file stops at a
morphism.** `SheafOfModules.TensorExteriorSymmetricAlgebras.determinantIsoOfComparison` compares
the determinants of two bundles **on one site**, and three separate things obstruct a version
across `G`, of which `exteriorAnnihilatorPushforwardHom` resolves only the first half of the
first.

* `IsExteriorAnnihilated` quantifies over *every* arrow out of the object. An arrow `V ⟶ W` of
  the source site gives an arrow `G V ⟶ G W`, so the condition over `G V` implies the condition
  over `V` and the morphism of this file exists for an arbitrary continuous `G`. The converse
  reads the condition over `G V` off the arrows in the image of `G` alone, and that needs `G` to
  be essentially surjective.
* `exteriorAnnihilatorIso` is built with `SheafOfModules.Submodule.factorThru` in both
  directions, and in the backwards direction the source has to be presented as a submodule of
  `G_*(⋀ⁿ F)`. The pushforward of a `SheafOfModules.Submodule` is a submodule of the pushforward
  sectionwise, but its `isSheaf` field asks that membership over `G V` follow from membership on
  a `Js`-covering sieve of `V`, which is cover-preservation of `G` — not a consequence of
  continuity.
* `determinant` is a **coproduct** over the degrees, and `sheafPushforwardFunctor` is a right
  adjoint, which need not preserve coproducts. So even with the annihilators identified
  degreewise there is no comparison of `G_*det(F)` with `det(G_*F)`.

All three hold when `G` is an equivalence of sites, which is the case
`TopologicalSpace.Opens.overEquivalence` that Tag 0FJN needs; none of them is available in the
generality of this file's hypotheses, and no weakening of `IsExteriorAnnihilated` would make a
general-`G` statement true. A second route for Tag 0FJN avoids the question entirely: at
constant rank `r` the determinant *is* the top exterior power
(`SheafOfModules.TensorExteriorSymmetricAlgebras.determinantIsoExteriorPower`), and that is
carried across `G` by `SheafOfModules.exteriorPushforwardIso` alone.

**No compiler option is set and no heartbeat limit is raised.** Every defeq here is at the
default budget.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite PresheafOfModules
  Stacks.SheafOfModules.PushforwardSheafification

universe w t a v u v' u'

namespace SheafOfModules

section GradedPushforward

variable {Cs : Type u} [Category.{v} Cs] {Ct : Type u'} [Category.{v'} Ct]
  (Js : GrothendieckTopology Cs) {Jt : GrothendieckTopology Ct} (G : Cs ⥤ Ct)
  [G.IsContinuous Js Jt] {R : Sheaf Jt RingCat.{t}}

/-- The pushforward `G_*A` of a sheaf of graded algebras along a continuous functor of sites,
with no change of scalars: its homogeneous pieces are the pushforwards of those of `A`, and its
multiplication and unit are those of `A` read on the objects `G V`.

This is `SheafOfModules.GradedAlgebra.pushforward` at the identity homomorphism of
`pushforwardRingSheaf Js G R`, which is the change of scalars that changes nothing; the two
are equal by `rfl`. The abbreviation exists because the pushforward of a sheaf of rings is
then the *target* of the construction rather than an argument of it, which is the shape the
exterior-algebra comparison below is stated at. -/
noncomputable def GradedAlgebra.pushforwardAlg (A : GradedAlgebra.{t, a} R) :
    GradedAlgebra.{t, a} (pushforwardRingSheaf Js G R) :=
  GradedAlgebra.pushforward.{t, a} (𝟙 (pushforwardRingSheaf Js G R)) A

@[simp]
theorem GradedAlgebra.pushforwardAlg_piece (A : GradedAlgebra.{t, a} R) (n : ℤ) :
    (GradedAlgebra.pushforwardAlg.{t, a} Js G A).piece n =
      (sheafPushforwardFunctor.{a} Js G R).obj (A.piece n) := rfl

@[simp]
theorem GradedAlgebra.pushforwardAlg_mul_app (A : GradedAlgebra.{t, a} R) (i j : ℤ)
    (V : Csᵒᵖ) : ((GradedAlgebra.pushforwardAlg.{t, a} Js G A).mul i j).app V =
      (A.mul i j).app (G.op.obj V) := rfl

@[simp]
theorem GradedAlgebra.pushforwardAlg_one_eval (A : GradedAlgebra.{t, a} R) (V : Csᵒᵖ) :
    (GradedAlgebra.pushforwardAlg.{t, a} Js G A).one.eval V = A.one.eval (G.op.obj V) := rfl

end GradedPushforward

section Pushforward

open _root_.SheafOfModules.GradedAlgebra

variable {Cs : Type u} [Category.{v} Cs] {Ct : Type u'} [Category.{v'} Ct]
  (Js : GrothendieckTopology Cs) {Jt : GrothendieckTopology Ct} (G : Cs ⥤ Ct)
  [G.IsContinuous Js Jt] [G.IsCocontinuous Js Jt]
  {Osharp : Sheaf Jt CommRingCat.{w}}
  [Jt.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Js.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Jt.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Jt AddCommGrpCat.{w}]
  [Js.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Js AddCommGrpCat.{w}]
  (M : SheafOfModules.{w} (toRingCat Jt Osharp))
  (A : GradedAlgebra.{w, w} (toRingCat Jt Osharp)) (gen : M ⟶ A.piece 1)
  (hgen : GradedAlgebra.SquareZero gen)

/-- The degree-one generator pushed forward along `G`. -/
noncomputable def pushforwardGen :
    (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj M ⟶
      (GradedAlgebra.pushforwardAlg.{w, w} Js G A).piece 1 :=
  (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).map gen

include hgen in
omit [G.IsCocontinuous Js Jt] [Js.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [Jt.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify Jt AddCommGrpCat]
  [Js.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify Js AddCommGrpCat] in
theorem squareZero_pushforwardGen :
    GradedAlgebra.SquareZero (pushforwardGen.{w} Js G M A gen) :=
  fun V x => hgen (G.op.obj V) x

omit [G.IsCocontinuous Js Jt] [Js.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [Jt.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify Jt AddCommGrpCat]
  [Js.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify Js AddCommGrpCat] in
/-- Pushforward of a presheaf of modules along `G`, in the two spellings used by
`PresheafOfModules.extPowPushforwardIso` and by
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyHom`, is the same
functor. -/
theorem sitePushforward_eq_presheafPushforwardFunctor :
    sitePushforward G (O := Osharp.obj) =
      presheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp) := rfl

/-- Pushforward along `G` in the two spellings, as an isomorphism. It is the identity: the two
functors are equal (`SheafOfModules.sitePushforward_eq_presheafPushforwardFunctor`). Stated for
an arbitrary presheaf of modules, so that the defeq query between the two module structures is
discharged once, abstractly, rather than at each concrete exterior power; see the implementation
notes. -/
noncomputable def pushforwardRestrictIso (P : PresheafOfModules.{w} (toRingCat Jt Osharp).obj) :
    (sitePushforward G (O := Osharp.obj)).obj P ≅
      (presheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj P := Iso.refl _

omit [G.IsCocontinuous Js Jt] [Js.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [Jt.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify Jt AddCommGrpCat]
  [Js.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify Js AddCommGrpCat] in
theorem pushforwardRestrictIso_hom_apply (P : PresheafOfModules.{w} (toRingCat Jt Osharp).obj)
    (V : Csᵒᵖ) (z : ((sitePushforward G (O := Osharp.obj)).obj P).obj V) :
    Hom.app (pushforwardRestrictIso.{w} Js G (Osharp := Osharp) P).hom V z = z := rfl

/-- The presheaf of sectionwise exterior powers of the pushforward of `M` compared with the
pushforward of the presheaf of sectionwise exterior powers of `M`, in the spelling of
pushforward that
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyHom` consumes. -/
noncomputable def extPowPushforwardPresheafIso (n : ℕ) :=
  (extPowPushforwardIso (O := Osharp.obj) G n M.val).symm ≪≫
    pushforwardRestrictIso.{w} Js G (Osharp := Osharp) (extPow n M.val)

omit [G.IsCocontinuous Js Jt] [Js.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [Jt.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify Jt AddCommGrpCat]
  [Js.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify Js AddCommGrpCat] in
/-- `SheafOfModules.extPowPushforwardPresheafIso` is the identity on sections. -/
theorem extPowPushforwardPresheafIso_hom_apply (n : ℕ) (V : Csᵒᵖ)
    (z : (extPow (O := G.op ⋙ Osharp.obj) n
      ((sitePushforward G (O := Osharp.obj)).obj M.val)).obj V) :
    Hom.app (extPowPushforwardPresheafIso.{w} Js G M n).hom V z =
      Hom.app (extPowPushforwardIso (O := Osharp.obj) G n M.val).inv V z := rfl

/-- **Pushforward commutes with the sheafified sectionwise exterior power.** This is
`Stacks.SheafOfModules.sectionwiseExteriorPowerPushforwardIso` read backwards, written as the
composite of its two legs so that its type is the type of that composite; see the
implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceExteriorAlgebra`. -/
noncomputable def sectionwiseExtPowPushforwardIso (n : ℕ) :=
  (PresheafOfModules.sheafification.{w}
        (𝟙 (pushforwardRingSheaf Js G (toRingCat Jt Osharp)).obj)).mapIso
      (extPowPushforwardPresheafIso.{w} Js G M n) ≪≫
    pushforwardSheafifyIso.{w} Js G (toRingCat Jt Osharp) (extPow n M.val)

omit [Js.HasSheafCompose (forget₂ CommRingCat RingCat)] in
theorem sectionwiseExtPowPushforwardIso_hom_val_app (n : ℕ) (V : Csᵒᵖ)
    (x : ((PresheafOfModules.sheafification.{w}
      (𝟙 (pushforwardRingSheaf Js G (toRingCat Jt Osharp)).obj)).obj
        (extPow (O := G.op ⋙ Osharp.obj) n
          ((sitePushforward G (O := Osharp.obj)).obj M.val))).val.obj V) :
    (sectionwiseExtPowPushforwardIso.{w} Js G M n).hom.val.app V x =
      (pushforwardSheafifyHom.{w} Js G (toRingCat Jt Osharp) (extPow n M.val)).val.app V
        (((PresheafOfModules.sheafification.{w}
              (𝟙 (pushforwardRingSheaf Js G (toRingCat Jt Osharp)).obj)).map
            (extPowPushforwardPresheafIso.{w} Js G M n).hom).val.app V x) := rfl

omit [G.IsCocontinuous Js Jt] [Js.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The comparison morphism adjoint to the pushed-forward sheafification unit, read on the
unit-image of a local section: it is the unit-image of the same section over `G V`. -/
theorem pushforwardSheafifyHom_sheafifyUnit (P : PresheafOfModules.{w} (toRingCat Jt Osharp).obj)
    (V : Csᵒᵖ)
    (y : ((presheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj P).obj V) :
    (pushforwardSheafifyHom.{w} Js G (toRingCat Jt Osharp) P).val.app V
        (Hom.app (sheafifyUnit (𝟙 (pushforwardRingSheaf Js G (toRingCat Jt Osharp)).obj)
          ((presheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj P)) V y) =
      Hom.app (sheafifyUnit (𝟙 (toRingCat Jt Osharp).obj) P) (G.op.obj V) y :=
  sheafificationHomEquiv_symm_app
    (R₀ := (pushforwardRingSheaf Js G (toRingCat Jt Osharp)).obj)
    (Rs := pushforwardRingSheaf Js G (toRingCat Jt Osharp))
    (𝟙 (pushforwardRingSheaf Js G (toRingCat Jt Osharp)).obj)
    (P := (presheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj P)
    (T := (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj
      ((PresheafOfModules.sheafification.{w} (𝟙 (toRingCat Jt Osharp).obj)).obj P))
    (pushforwardUnit.{w} Js G (toRingCat Jt Osharp) P) V y

omit [Js.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The comparison carries the unit-image of a local section of the sectionwise exterior power
over an object of the source site to the unit-image of that section over its image under
`G`.** -/
theorem sectionwiseExtPowPushforwardIso_hom_sheafifyUnit (n : ℕ) (V : Csᵒᵖ)
    (z : (extPow (O := G.op ⋙ Osharp.obj) n
      ((sitePushforward G (O := Osharp.obj)).obj M.val)).obj V) :
    (sectionwiseExtPowPushforwardIso.{w} Js G M n).hom.val.app V
        (Hom.app (sheafifyUnit (𝟙 (pushforwardRingSheaf Js G (toRingCat Jt Osharp)).obj)
          (extPow (O := G.op ⋙ Osharp.obj) n
            ((sitePushforward G (O := Osharp.obj)).obj M.val))) V z) =
      Hom.app (sheafifyUnit (𝟙 (toRingCat Jt Osharp).obj) (extPow n M.val)) (G.op.obj V)
        (Hom.app (extPowPushforwardPresheafIso.{w} Js G M n).hom V z) := by
  refine Eq.trans (sectionwiseExtPowPushforwardIso_hom_val_app.{w} Js G M n V _) ?_
  refine Eq.trans (congrArg (fun t =>
    (pushforwardSheafifyHom.{w} Js G (toRingCat Jt Osharp) (extPow n M.val)).val.app V t)
    (PresheafOfModules.unit_naturality_apply
      (R₀ := (pushforwardRingSheaf Js G (toRingCat Jt Osharp)).obj)
      (R := pushforwardRingSheaf Js G (toRingCat Jt Osharp))
      (α := 𝟙 (pushforwardRingSheaf Js G (toRingCat Jt Osharp)).obj)
      (extPowPushforwardPresheafIso.{w} Js G M n).hom V z)) ?_
  have h := pushforwardSheafifyHom_sheafifyUnit.{w} Js G (extPow n M.val) V
    (Hom.app (extPowPushforwardPresheafIso.{w} Js G M n).hom V z)
  exact h

omit [G.IsCocontinuous Js Jt] [Js.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [Jt.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify Jt AddCommGrpCat]
  [Js.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify Js AddCommGrpCat] in
/-- The ordered product of degree-one sections in the pushed-forward graded algebra is the
ordered product in `A` over the image of the object under `G`. -/
theorem homogeneousProd_pushforward (V : Csᵒᵖ) (n : ℕ)
    (z : Fin n → ((GradedAlgebra.pushforwardAlg.{w, w} Js G A).piece 1).val.obj V) :
    Stacks.GradedAlgebra.homogeneousProd.{v, u, w, w}
        (O := (_root_.Stacks.SheafOfModules.pushforwardCommRingSheaf Js G (Osharp := Osharp)).obj)
        (GradedAlgebra.pushforwardAlg.{w, w} Js G A).toPresheafGradedAlgebra V n z =
      Stacks.GradedAlgebra.homogeneousProd.{v', u', w, w} (O := Osharp.obj)
        A.toPresheafGradedAlgebra (G.op.obj V) n z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact congrArg (fun y => (A.mul (n : ℤ) 1).app (G.op.obj V) y
        (z (Fin.last n))) (ih fun i => z i.castSucc)

include hgen in
/-- **The comparison homomorphism over the source site is the pushforward of the one over the
target site**, read through the comparison of the two sectionwise models. Both sides are
morphisms out of a sheafification, so they are determined by their values on the unit-image of a
local section (`PresheafOfModules.sheafification_hom_ext`), and there by their values on a wedge
of local sections (`ExteriorAlgebra.powExtₛₗ`). On such a wedge both sides are the ordered
product of the images of those sections under the generator — on the left by
`SheafOfModules.exteriorDescSq_sheafifyUnit_ιMulti` over the source site, on the right by
`SheafOfModules.sectionwiseExtPowPushforwardIso_hom_sheafifyUnit` followed by the same lemma over
the target site — and the two ordered products agree by
`SheafOfModules.homogeneousProd_pushforward`. -/
theorem exteriorDescSq_pushforward_app (n : ℕ) :
    (exteriorDescSq (J := Js)
        (Osharp := _root_.Stacks.SheafOfModules.pushforwardCommRingSheaf Js G
          (Osharp := Osharp))
        ((sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj M)
        (GradedAlgebra.pushforwardAlg.{w, w} Js G A) (pushforwardGen.{w} Js G M A gen)
        (squareZero_pushforwardGen.{w} Js G M A gen hgen)).app (n : ℤ) =
      (sectionwiseExtPowPushforwardIso.{w} Js G M n).hom ≫
        (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).map
          ((exteriorDescSq M A gen hgen).app (n : ℤ)) := by
  refine PresheafOfModules.sheafification_hom_ext
    (PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext ?_)
  refine ExteriorAlgebra.powExtₛₗ fun s => ?_
  have hL := exteriorDescSq_sheafifyUnit_ιMulti (J := Js)
    (Osharp := _root_.Stacks.SheafOfModules.pushforwardCommRingSheaf Js G (Osharp := Osharp))
    ((sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj M)
    (GradedAlgebra.pushforwardAlg.{w, w} Js G A) (pushforwardGen.{w} Js G M A gen)
    (squareZero_pushforwardGen.{w} Js G M A gen hgen) n V s
  have hR := sectionwiseExtPowPushforwardIso_hom_sheafifyUnit.{w} Js G M n V
    (exteriorPower.ιMulti _ n s)
  have hR2 := exteriorDescSq_sheafifyUnit_ιMulti M A gen hgen n (G.op.obj V) s
  refine Eq.trans hL (Eq.symm ?_)
  refine Eq.trans (congrArg (fun z =>
    ((sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).map
      ((exteriorDescSq M A gen hgen).app (n : ℤ))).val.app V z) hR) ?_
  exact Eq.trans hR2 (homogeneousProd_pushforward.{w} Js G A V n _).symm

end Pushforward

section PushforwardUniversal

open _root_.SheafOfModules.GradedAlgebra

variable {Cs : Type u} [Category.{v} Cs] {Ct : Type u'} [Category.{v'} Ct]
  (Js : GrothendieckTopology Cs) {Jt : GrothendieckTopology Ct} (G : Cs ⥤ Ct)
  [G.IsContinuous Js Jt] [G.IsCocontinuous Js Jt]
  {Osharp : Sheaf Jt CommRingCat.{w}}
  [Jt.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Js.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Jt.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Jt AddCommGrpCat.{w}]
  [Js.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Js AddCommGrpCat.{w}]
  (M : SheafOfModules.{w} (toRingCat Jt Osharp))
  (A : GradedAlgebra.{w, w} (toRingCat Jt Osharp)) (gen : M ⟶ A.piece 1)
  (hA : GradedAlgebra.IsExteriorAlgebra A gen)

include hA in
/-- **The comparison homomorphism over the source site is invertible in every degree.** In a
nonnegative degree this is `SheafOfModules.exteriorDescSq_pushforward_app` together with the
invertibility over the target site; in a negative degree both source and target are zero
objects. -/
theorem isIso_exteriorDescSq_pushforward_app (n : ℤ) :
    IsIso ((exteriorDescSq (J := Js)
      (Osharp := _root_.Stacks.SheafOfModules.pushforwardCommRingSheaf Js G (Osharp := Osharp))
        ((sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj M)
        (GradedAlgebra.pushforwardAlg.{w, w} Js G A) (pushforwardGen.{w} Js G M A gen)
        (squareZero_pushforwardGen.{w} Js G M A gen hA.1)).app n) := by
  by_cases hn : n < 0
  · refine CategoryTheory.Limits.IsZero.isIso ?_ ?_ _
    · rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
      ext V x
      exact sectionwiseExteriorAlgebra_piece_eq_zero_of_neg Js
        (𝟙 (_root_.Stacks.SheafOfModules.pushforwardCommRingSheaf Js G
          (Osharp := Osharp)).obj)
        ((sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj M).val hn V x
    · rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
      ext V y
      exact exteriorPiece_eq_zero_of_neg M A gen hA hn (G.op.obj V) y
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 hn)
    have he : (exteriorDescSq M A gen hA.1).app (m : ℤ) =
        (exteriorPieceIso M A gen hA (m : ℤ)).hom := rfl
    rw [exteriorDescSq_pushforward_app.{w} Js G M A gen hA.1 m, he]
    exact IsIso.comp_isIso' (Iso.isIso_hom _)
      (((sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).mapIso
        (exteriorPieceIso M A gen hA (m : ℤ))).isIso_hom)

include hA in
/-- **The pushforward of an exterior algebra along a continuous and cocontinuous functor of
sites is an exterior algebra of the pushforward of the sheaf of modules**, on the pushed-forward
generator. This is the statement that carries the algebra structure, and it is what
`Stacks.SheafOfModules.exteriorPowerPushforwardIso` lacks: with it,
`SheafOfModules.GradedAlgebra.IsUniversal.pieceIso` compares `G_*A` degreewise with any exterior
algebra of `G_*M` on the source site, compatibly with the generators
(`SheafOfModules.GradedAlgebra.IsUniversal.pieceIso_generator`), with the multiplications
(`pieceIso_mul`) and with the units (`pieceIso_one`). -/
theorem isExteriorAlgebra_pushforward :
    GradedAlgebra.IsExteriorAlgebra (GradedAlgebra.pushforwardAlg.{w, w} Js G A)
      (pushforwardGen.{w} Js G M A gen) := by
  set e := sheafifySectionsIso (J := Js)
    (Osharp := _root_.Stacks.SheafOfModules.pushforwardCommRingSheaf Js G (Osharp := Osharp))
    ((sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj M)
  have huniv := GradedAlgebra.IsExteriorAlgebra.of_desc_isIso
    (isExteriorAlgebra_sectionwiseExteriorAlgebra Js
      (𝟙 (_root_.Stacks.SheafOfModules.pushforwardCommRingSheaf Js G (Osharp := Osharp)).obj)
      ((sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj M).val)
    (e.hom ≫ pushforwardGen.{w} Js G M A gen)
    (GradedAlgebra.squareZero_comp _ (squareZero_pushforwardGen.{w} Js G M A gen hA.1))
    (fun n => isIso_exteriorDescSq_pushforward_app.{w} Js G M A gen hA n)
  have h2 := GradedAlgebra.IsExteriorAlgebra.comp_iso huniv e.inv e.isIso_inv
  have h3 : e.inv ≫ e.hom ≫ pushforwardGen.{w} Js G M A gen = pushforwardGen.{w} Js G M A gen :=
    Iso.inv_hom_id_assoc _ _
  rwa [h3] at h2

variable (B : GradedAlgebra.{w, w} (toRingCat Js
    (_root_.Stacks.SheafOfModules.pushforwardCommRingSheaf Js G (Osharp := Osharp))))
  (gen' : (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj M ⟶ B.piece 1)
  (hB : GradedAlgebra.IsExteriorAlgebra B gen')

/-- **Pushforward commutes with the exterior algebra, compatibly with the algebra structure.**
This is `Stacks.SheafOfModules.exteriorPowerPushforwardIso` again, but obtained from a universal
property of `G_*A` itself, so that the compatibilities below come with it. -/
noncomputable def exteriorPushforwardIso (n : ℤ) :
    (GradedAlgebra.pushforwardAlg.{w, w} Js G A).piece n ≅ B.piece n :=
  GradedAlgebra.IsUniversal.pieceIso
    (isExteriorAlgebra_pushforward.{w} Js G M A gen hA).isUniversal hB.isUniversal n

/-- The comparison of exterior algebras along a pushforward carries one generator to the
other. -/
theorem exteriorPushforwardIso_generator :
    pushforwardGen.{w} Js G M A gen ≫
        (exteriorPushforwardIso.{w} Js G M A gen hA B gen' hB 1).hom = gen' :=
  GradedAlgebra.IsUniversal.pieceIso_generator _ _

/-- The comparison of exterior algebras along a pushforward is multiplicative on homogeneous
local sections. -/
theorem exteriorPushforwardIso_mul (i j : ℤ) (V : Csᵒᵖ)
    (x : ((GradedAlgebra.pushforwardAlg.{w, w} Js G A).piece i).val.obj V)
    (y : ((GradedAlgebra.pushforwardAlg.{w, w} Js G A).piece j).val.obj V) :
    (exteriorPushforwardIso.{w} Js G M A gen hA B gen' hB (i + j)).hom.val.app V
        (((GradedAlgebra.pushforwardAlg.{w, w} Js G A).mul i j).app V x y) =
      (B.mul i j).app V
        ((exteriorPushforwardIso.{w} Js G M A gen hA B gen' hB i).hom.val.app V x)
        ((exteriorPushforwardIso.{w} Js G M A gen hA B gen' hB j).hom.val.app V y) :=
  GradedAlgebra.IsUniversal.pieceIso_mul _ _ i j V x y

/-- The comparison of exterior algebras along a pushforward carries the unit to the unit. -/
theorem exteriorPushforwardIso_one (V : Csᵒᵖ) :
    (exteriorPushforwardIso.{w} Js G M A gen hA B gen' hB 0).hom.val.app V
        ((GradedAlgebra.pushforwardAlg.{w, w} Js G A).one.eval V) = B.one.eval V :=
  GradedAlgebra.IsUniversal.pieceIso_one _ _ V

end PushforwardUniversal

namespace TensorExteriorSymmetricAlgebras

section Annihilator

variable {Cs : Type u} [Category.{v} Cs] {Ct : Type u'} [Category.{v'} Ct]
  (Js : GrothendieckTopology Cs) {Jt : GrothendieckTopology Ct} (G : Cs ⥤ Ct)
  [G.IsContinuous Js Jt]
  {Osharp : Sheaf Jt CommRingCat.{w}}
  [Jt.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Js.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Jt.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Jt AddCommGrpCat.{w}]
  [Js.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Js AddCommGrpCat.{w}]
  {F : SheafOfModules.{w} (toRingCat Jt Osharp)}
  (A : TensorExteriorSymmetricAlgebras Jt F)
  (B : TensorExteriorSymmetricAlgebras
    (Osharp := _root_.Stacks.SheafOfModules.pushforwardCommRingSheaf Js G (Osharp := Osharp))
    Js ((sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj F))
  (φ : ∀ i : ℤ, (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj
    (A.exterior.piece i) ≅ B.exterior.piece i)
  (hgen : (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).map A.exteriorGenerator ≫
    (φ 1).hom = B.exteriorGenerator)
  (hmul : ∀ (i j : ℤ) (V : Csᵒᵖ)
      (x : ((sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj
        (A.exterior.piece i)).val.obj V)
      (y : ((sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj
        (A.exterior.piece j)).val.obj V),
    (φ (i + j)).hom.val.app V ((A.exterior.mul i j).app (G.op.obj V) x y) =
      (B.exterior.mul i j).app V ((φ i).hom.val.app V x) ((φ j).hom.val.app V y))

include hgen hmul

/-- **A generator- and multiplication-compatible comparison across a pushforward of sites
carries exterior annihilated sections to exterior annihilated sections.** This is
`SheafOfModules.TensorExteriorSymmetricAlgebras.isExteriorAnnihilated_of_comparison` with the
two bundles on different sites: an arrow `V ⟶ W` of the source site and a degree-one section
over `W` are an arrow `G V ⟶ G W` and a degree-one section over `G W`, so the condition on the
target site, which quantifies over *all* arrows out of `G V`, implies the condition on the
source site, which sees only the arrows in the image of `G`. The converse is not available;
see the implementation notes. -/
theorem isExteriorAnnihilated_of_pushforwardComparison (n : ℕ) {V : Csᵒᵖ}
    {x : (A.exteriorPower n).val.obj (G.op.obj V)} (hx : A.IsExteriorAnnihilated n x) :
    B.IsExteriorAnnihilated n ((φ (n : ℤ)).hom.val.app V x) := by
  intro W f m
  have hres : (B.exteriorPower n).val.restrictₛₗ f ((φ (n : ℤ)).hom.val.app V x) =
      (φ (n : ℤ)).hom.val.app W ((A.exteriorPower n).val.restrictₛₗ (G.op.map f) x) :=
    (PresheafOfModules.naturality_apply (φ (n : ℤ)).hom.val f x).symm
  have hm : B.exteriorGenerator.val.app W m =
      (φ 1).hom.val.app W (A.exteriorGenerator.val.app (G.op.obj W) m) :=
    (hom_congr_app_apply hgen W m).symm
  refine Eq.trans (congrArg (fun t => (B.exterior.mul 1 (n : ℤ)).app W
    (B.exteriorGenerator.val.app W m) t) hres) ?_
  refine Eq.trans (congrArg (fun t => (B.exterior.mul 1 (n : ℤ)).app W t
    ((φ (n : ℤ)).hom.val.app W ((A.exteriorPower n).val.restrictₛₗ (G.op.map f) x))) hm) ?_
  refine Eq.trans (hmul 1 (n : ℤ) W (A.exteriorGenerator.val.app (G.op.obj W) m)
    ((A.exteriorPower n).val.restrictₛₗ (G.op.map f) x)).symm ?_
  refine Eq.trans (congrArg (fun t => (φ (1 + (n : ℤ))).hom.val.app W t)
    (hx (G.op.obj W) (G.op.map f) m)) ?_
  exact map_zero _

/-- The values of the pushforward of `annₙ(F)` in `⋀ⁿ(G_*F)` lie in `annₙ(G_*F)`: this is the
hypothesis of `SheafOfModules.Submodule.factorThru` for the cross-site comparison. -/
theorem pushforward_ι_mem_exteriorAnnihilator (n : ℕ) (V : Csᵒᵖ)
    (y : ((sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj
      (A.exteriorAnnihilator n).toSheafOfModules).val.obj V) :
    (((sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).map
          (A.exteriorAnnihilator n).ι ≫ (φ (n : ℤ)).hom).val.app V y) ∈
      (B.exteriorAnnihilator n).obj V :=
  (mem_exteriorAnnihilator_obj B n _).mpr
    (isExteriorAnnihilated_of_pushforwardComparison Js G A B φ hgen hmul n (V := V)
      (x := (A.exteriorAnnihilator n).ι.val.app (G.op.obj V) y)
      ((mem_exteriorAnnihilator_obj A n _).mp
        (Submodule.ι_val_app_mem (A.exteriorAnnihilator n) (G.op.obj V) y)))

/-- **The pushforward of `annₙ(F)` maps to `annₙ(G_*F)`.** The cross-site half of
`SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAnnihilatorIso` that is available for an
arbitrary continuous functor of sites; it is the degree-`n` summand of a comparison of the two
determinants, and the three further things such a comparison needs are listed in the
implementation notes. -/
noncomputable def exteriorAnnihilatorPushforwardHom (n : ℕ) :
    (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj
        (A.exteriorAnnihilator n).toSheafOfModules ⟶
      (B.exteriorAnnihilator n).toSheafOfModules :=
  (B.exteriorAnnihilator n).factorThru
    ((sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).map
      (A.exteriorAnnihilator n).ι ≫ (φ (n : ℤ)).hom)
    (pushforward_ι_mem_exteriorAnnihilator Js G A B φ hgen hmul n)

@[reassoc (attr := simp)]
theorem exteriorAnnihilatorPushforwardHom_ι (n : ℕ) :
    exteriorAnnihilatorPushforwardHom Js G A B φ hgen hmul n ≫ (B.exteriorAnnihilator n).ι =
      (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).map
        (A.exteriorAnnihilator n).ι ≫ (φ (n : ℤ)).hom :=
  Submodule.factorThru_ι _ _ _

section Canonical

variable [G.IsCocontinuous Js Jt]

/-- **The canonical cross-site comparison of the exterior algebras**: the degreewise comparison
of `G_*(⋀ F)` with the exterior algebra of `G_*F` chosen by `B`, obtained from the universal
property of `G_*(⋀ F)` (`SheafOfModules.isExteriorAlgebra_pushforward`). -/
noncomputable def exteriorPushforwardComparison (i : ℤ) :
    (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj (A.exterior.piece i) ≅
      B.exterior.piece i :=
  exteriorPushforwardIso.{w} Js G F A.exterior A.exteriorGenerator
    A.exterior_isExteriorAlgebra B.exterior B.exteriorGenerator B.exterior_isExteriorAlgebra i

/-- **The canonical cross-site comparison carries `annₙ(F)` into `annₙ(G_*F)`.** This is the
instance of `exteriorAnnihilatorPushforwardHom` whose two compatibility hypotheses were, before
`SheafOfModules.isExteriorAlgebra_pushforward`, not dischargeable: they are
`SheafOfModules.exteriorPushforwardIso_generator` and `exteriorPushforwardIso_mul`. -/
noncomputable def exteriorAnnihilatorPushforward (n : ℕ) :
    (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj
        (A.exteriorAnnihilator n).toSheafOfModules ⟶
      (B.exteriorAnnihilator n).toSheafOfModules :=
  exteriorAnnihilatorPushforwardHom Js G A B (exteriorPushforwardComparison Js G A B)
    (exteriorPushforwardIso_generator.{w} Js G F A.exterior A.exteriorGenerator
      A.exterior_isExteriorAlgebra B.exterior B.exteriorGenerator B.exterior_isExteriorAlgebra)
    (fun i j V x y => exteriorPushforwardIso_mul.{w} Js G F A.exterior A.exteriorGenerator
      A.exterior_isExteriorAlgebra B.exterior B.exteriorGenerator B.exterior_isExteriorAlgebra
      i j V x y) n

omit hgen hmul in
@[reassoc (attr := simp)]
theorem exteriorAnnihilatorPushforward_ι (n : ℕ) :
    exteriorAnnihilatorPushforward Js G A B n ≫ (B.exteriorAnnihilator n).ι =
      (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).map
          (A.exteriorAnnihilator n).ι ≫
        (exteriorPushforwardComparison Js G A B (n : ℤ)).hom :=
  Submodule.factorThru_ι _ _ _

end Canonical

end Annihilator

end TensorExteriorSymmetricAlgebras

end SheafOfModules

end
