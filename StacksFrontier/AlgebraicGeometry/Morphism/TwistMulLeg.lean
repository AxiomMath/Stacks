module

public import StacksFrontier.AlgebraicGeometry.TwistMultCompat.Generic

/-!
# Multiplicative families of morphisms, and the transport of one along a leg

This file is the generic half of the graded-algebra clause of Tag 07ZG. Nothing below mentions
`AlgebraicGeometry.Proj`, a twisting sheaf or a graded ring: the objects are modules on arbitrary
schemes and the morphisms are free. That is deliberate, and it is the discipline
`StacksFrontier/AlgebraicGeometry/TwistMultCompat/Generic.lean` records: at the concrete types of
Tag 07ZG the elaborator cannot afford to decompose a composite of pseudofunctoriality components
against free morphisms more than once per declaration, so every step is taken here instead, where
the decomposition is free.

## The normal form

Write `pbMul f mul` for the inverse image of a morphism-level product along `f`, with the Tag 01CD
comparison cancelled off the source, so that it is again a morphism *out of a tensor product
sheaf*. The statement "the family `a` carries the product `mulP` to the product `mulQ`" is then an
equation between two morphisms out of one tensor product sheaf,

`mulP ≫ a (m + n) = (a m ⊗ a n) ≫ mulQ`,

with `⊗` spelled as the action on morphisms of the uncurried
`Stacks.SheafOfModules.Tensor.sheafTensor`. Every lemma below
is of that shape, and they compose: `mul_comp` concatenates two of them, `mul_inv` inverts one
whose family is invertible, and `mul_pullback` applies the inverse image functor to one.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistMulLeg.pbMul`: the inverse image of a morphism-level product,
  read out of the tensor product sheaf of the inverse images.
* `Stacks.AlgebraicGeometry.TwistMulLeg.legIso`: **the four-factor leg identification.** For a
  factorisation `k ≫ h = ρ ≫ hU ≫ c` and an identification `χ` of `c^*M` with `N`, the
  identification of `k^*h^*M` with `ρ^*hU^*N` built from the two pseudofunctoriality
  isomorphisms, the congruence isomorphism of the factorisation, and `χ`.

  This is the shape of `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartSourceIso` and of
  `chartTargetIso` **on the nose** — both are `legIso` by `rfl`, which is what makes the whole
  transport affordable: the "factor-by-factor identification of `relativeTwistChart` with its
  four factors" that the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Morphism/TwistMulChart.lean` record as missing is not a theorem
  to be proved but a definition to be stated in the right generality.

## Main results

* `Stacks.AlgebraicGeometry.TwistMulLeg.mul_comp`, `mul_inv`, `mul_id`: multiplicative families
  compose, invert and contain the identity.
* `Stacks.AlgebraicGeometry.TwistMulLeg.mul_pullbackComp` and `mul_pullbackCongr`: the
  pseudofunctoriality and congruence isomorphisms of the inverse image are multiplicative for the
  pulled-back products.
* `Stacks.AlgebraicGeometry.TwistMulLeg.mul_pullback`: the inverse image of a multiplicative
  family is multiplicative, and `map_eq_of_mul_pullback` reads such a statement back as an
  equation between two inverse images of composites — the shape in which a locality reduction
  consumes it.
* `Stacks.AlgebraicGeometry.TwistMulLeg.leg_mul`: **the leg transport.** If `χ` carries the
  inverse image along `c` of a product `mulY` to a product `mulV`, then `legIso` carries the
  twice-iterated inverse image of `mulY` along `k` and `h` to the twice-iterated inverse image of
  `mulV` along `ρ` and `hU`.

## Implementation notes

**No retraction is needed.** `Stacks.AlgebraicGeometry.TwistMultCompat.transport_six`, the
six-factor transport Tag 01NO uses, takes a retraction `k ≫ j = 𝟙` of a second morphism out of
the middle scheme, and the implementation notes of
`StacksFrontier/AlgebraicGeometry/Morphism/TwistMulChart.lean` record that Tag 07ZG has no such
retraction — the domain of definition of a general `ψ` over an affine open is a proper open of the
spectrum — and conclude that "a sibling of `transport_six` for two legs over one isomorphism is
owed". It is not. `transport_six` needs the retraction because it lands on modules living on the
*outer* scheme, which it reaches by identifying an inverse image with the identity. `leg_mul`
lands on `ρ^*hU^*N` and identifies nothing, so it applies to one leg at a time with no hypothesis
beyond the factorisation; the two legs of Tag 07ZG are then two instances of it, joined by
`mul_comp` and `mul_inv`. The conjugating isomorphism `ρ` enters as an ordinary morphism and its
invertibility is never used here.

**The category algebra is done at `{C : Type*} [Category C]` and the sheaf content is isolated.**
`mul_comp_gen`, `mul_inv_gen`, `mul_id_gen` and `swap_of_inv` take the tensor product only as an
unconstrained object with unconstrained morphisms between the tensor objects, so that `rw` and
`simp only [Category.assoc]` can be used in their proofs; at `X.Modules` they cannot, because
`AlgebraicGeometry.Scheme.Modules` is a `def` and the category instance is therefore invisible at
the transparency a rewrite builds its motive at. The functoriality of the tensor product then
enters exactly three times, as the `htab`/`htt`/`ht` hypotheses of those three lemmas, discharged
by `Stacks.AlgebraicGeometry.TwistMultTransport.tensorSheafMap_comp` and `tensorSheafMap_id`.
This is the device `StacksFrontier/AlgebraicGeometry/TwistMultTransport/Structural.lean` records for
the same reason.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.TwistMultTransport
open Stacks.AlgebraicGeometry.TwistMultCompat

namespace Stacks.AlgebraicGeometry.TwistMulLeg

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-! ### The category algebra, at the level of variables

A "product" is here nothing but a morphism out of an unconstrained object, and a "family" nothing
but a morphism between two such objects together with a morphism between the two targets. The
four lemmas of this section are therefore statements about an arbitrary category, and their proofs
may use `rw`. -/

section Generic

variable {C : Type*} [Category C]

/-- **Two-sided cancellation.** From a commuting square `ab ≫ x = c ≫ e`, a left inverse `uv` of
`ab` and a right inverse `d` of `e`, the square with `ab` and `e` inverted commutes. -/
public theorem swap_of_inv {P Q R T : C} {ab : P ⟶ Q} {uv : Q ⟶ P} {x : Q ⟶ R} {c : P ⟶ T}
    {e : T ⟶ R} {d : R ⟶ T} (huv : uv ≫ ab = 𝟙 Q) (hed : e ≫ d = 𝟙 T)
    (h : ab ≫ x = c ≫ e) : uv ≫ c = x ≫ d := by
  calc uv ≫ c = uv ≫ (c ≫ (e ≫ d)) := by rw [hed, Category.comp_id]
    _ = (uv ≫ (c ≫ e)) ≫ d := by simp only [Category.assoc]
    _ = x ≫ d := by rw [← h, ← Category.assoc, huv, Category.id_comp]

/-- **A naturality square conjugated by the two components of an isomorphism.** Both isomorphisms
are explicit arguments, which is load-bearing: given them, the four objects of `swap_of_inv` are
fixed and only the two sides of the square are unified. Reached instead by unification — with the
cancellation facts supplied as separate hypotheses — the same step reports `(deterministic)
timeout at whnf` at the concrete types below, because the tensor product sheaf has two spellings
there (a three-argument application and an application of the bifunctor) and the elaborator
converts one against the other while searching. -/
public theorem conj_nat_gen {P Q R T : C} (i : P ≅ Q) (j : T ≅ R) {c : P ⟶ T} {x : Q ⟶ R}
    (h : i.hom ≫ x = c ≫ j.hom) : i.inv ≫ c = x ≫ j.inv :=
  swap_of_inv i.inv_hom_id j.hom_inv_id h

/-- **A family whose tensor component is the identity is multiplicative for one product.** -/
public theorem mul_id_gen {TP Pmn : C} (mulP : TP ⟶ Pmn) {t : TP ⟶ TP} (ht : t = 𝟙 TP) :
    mulP ≫ 𝟙 Pmn = t ≫ mulP := by
  rw [ht, Category.comp_id, Category.id_comp]

/-- **Two multiplicative families compose**, the tensor component of the composite being supplied
as a hypothesis so that the functoriality of the tensor product is used outside this lemma. -/
public theorem mul_comp_gen {TP TQ TR Pmn Qmn Rmn : C} {mulP : TP ⟶ Pmn} {mulQ : TQ ⟶ Qmn}
    {mulR : TR ⟶ Rmn} {ta : TP ⟶ TQ} {tb : TQ ⟶ TR} {tab : TP ⟶ TR}
    {amn : Pmn ⟶ Qmn} {bmn : Qmn ⟶ Rmn} (htab : tab = ta ≫ tb)
    (ha : mulP ≫ amn = ta ≫ mulQ) (hb : mulQ ≫ bmn = tb ≫ mulR) :
    mulP ≫ (amn ≫ bmn) = tab ≫ mulR := by
  rw [htab, ← Category.assoc, ha, Category.assoc, hb, Category.assoc]

/-- **The inverse of a multiplicative family of isomorphisms is multiplicative**, the inverse
tensor component being supplied as a one-sided inverse of the given one. -/
public theorem mul_inv_gen {TP TQ Pmn Qmn : C} {mulP : TP ⟶ Pmn} {mulQ : TQ ⟶ Qmn}
    {t : TP ⟶ TQ} {t' : TQ ⟶ TP} {amn : Pmn ≅ Qmn} (htt : t' ≫ t = 𝟙 TQ)
    (ha : mulP ≫ amn.hom = t ≫ mulQ) : mulQ ≫ amn.inv = t' ≫ mulP := by
  rw [Iso.comp_inv_eq, Category.assoc, ha, ← Category.assoc, htt, Category.id_comp]

/-- **A two-factor composite cancelled against the composite of the two inverses.** -/
public theorem comp_comp_cancel {Aa Bb Dd : C} {ph : Aa ⟶ Bb} {pi : Bb ⟶ Aa} {qh : Bb ⟶ Dd}
    {qi : Dd ⟶ Bb} (hp : ph ≫ pi = 𝟙 Aa) (hq : qh ≫ qi = 𝟙 Bb) :
    (ph ≫ qh) ≫ (qi ≫ pi) = 𝟙 Aa := by
  rw [Category.assoc, ← Category.assoc qh qi pi, hq, Category.id_comp, hp]

/-- The same with the two composites interchanged. -/
public theorem comp_comp_cancel' {Aa Bb Dd : C} {ph : Aa ⟶ Bb} {pi : Bb ⟶ Aa} {qh : Bb ⟶ Dd}
    {qi : Dd ⟶ Bb} (hp : pi ≫ ph = 𝟙 Bb) (hq : qi ≫ qh = 𝟙 Dd) :
    (qi ≫ pi) ≫ (ph ≫ qh) = 𝟙 Dd :=
  comp_comp_cancel hq hp

/-- **The multiplicativity of a family, for products presented as `u ≫ m`.**

This is the one piece of category algebra the concrete lemmas below are built from, and it is
stated here rather than unfolded at the concrete types on purpose.

**The two products are variables and their splittings are hypotheses**, which is load-bearing.
`pbMul` is by definition the composite `u ≫ m`, but its *declared* type spells the tensor product
sheaf as `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` over
`Stacks.RingedSpace.structureSheafRing`, while the type of its first factor — a component of
`Stacks.PullbackTensorIso.pullbackTensorIso` — spells it as an application of the bifunctor
`Stacks.RingedSpace.tensorSheaf` over `Stacks.RingedSpace.structureRingSheaf`. The two are
definitionally equal and print almost alike, and converting one against the other inside a goal of
this size costs the whole deterministic budget: with `mulP` and `mulQ` written as `u ≫ m` in the
conclusion, both concrete applications below reported `(deterministic) timeout at whnf` at the
`exact`. Taking the splittings as hypotheses confines that conversion to `pbMul_eq`, which is one
`rfl` in a declaration of its own, and leaves nothing to convert here. -/
public theorem mul_of_split_gen {TP TQ Ap Aq Pmn Qmn : C} {mulP : TP ⟶ Pmn} {mulQ : TQ ⟶ Qmn}
    {u : TP ⟶ Ap} {m : Ap ⟶ Pmn} {u' : TQ ⟶ Aq} {m' : Aq ⟶ Qmn}
    {t : TP ⟶ TQ} {amn : Pmn ⟶ Qmn} {a : Ap ⟶ Aq}
    (hP : mulP = u ≫ m) (hQ : mulQ = u' ≫ m')
    (hu : u ≫ a = t ≫ u') (hm : m ≫ amn = a ≫ m') :
    mulP ≫ amn = t ≫ mulQ := by
  rw [hP, hQ, Category.assoc, hm, ← Category.assoc, hu, Category.assoc]

/-- **A multiplication square whose source product is given with the forward comparison in
front.** This is the shape in which the chart's multiplication square is available: the inverse
image of the product, followed by the identification, equals the forward Tag 01CD comparison
followed by the rest. Cancelling the comparison turns it into the normal form.

The isomorphism is an explicit argument because `i.inv` cannot be solved for `i` by
unification. -/
public theorem mul_of_comparison_gen {TP Ap Pmn Qq : C} {mulP : TP ⟶ Pmn} (i : Ap ≅ TP)
    {M : Ap ⟶ Pmn} {amn : Pmn ⟶ Qq} {R : TP ⟶ Qq} (hP : mulP = i.inv ≫ M)
    (h : M ≫ amn = i.hom ≫ R) : mulP ≫ amn = R := by
  rw [hP, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- **A multiplication square with the forward comparison in front and the target product given
split.** The shape of Tag 01MY's multiplicativity clause at the chart: the family is conjugated by
the two Tag 01CD comparisons of the two legs. Cancelling both turns it into the normal form. -/
public theorem mul_of_comparison_split_gen {TP Ap Pmn TQ Aq Qmn : C} {mulP : TP ⟶ Pmn}
    {mulQ : TQ ⟶ Qmn} (i : Ap ≅ TP) (j : Aq ≅ TQ) {M : Ap ⟶ Pmn} {amn : Pmn ⟶ Qmn}
    {t : TP ⟶ TQ} {M' : Aq ⟶ Qmn} (hP : mulP = i.inv ≫ M) (hQ : mulQ = j.inv ≫ M')
    (h : M ≫ amn = (i.hom ≫ t ≫ j.inv) ≫ M') : mulP ≫ amn = t ≫ mulQ := by
  rw [hP, hQ, Category.assoc, h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- **A functor carries a commuting square to a commuting square.** -/
public theorem map_sq_gen {D : Type*} [Category D] (F : C ⥤ D) {Aa Bb Aa' Bb' : C}
    {a : Aa ⟶ Bb} {b : Bb ⟶ Bb'} {c : Aa ⟶ Aa'} {d : Aa' ⟶ Bb'} (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d :=
  ((F.map_comp a b).symm.trans (congrArg F.map h)).trans (F.map_comp c d)

/-- **A multiplicative square for the images under a functor, read back as the image of a
square.** The two products `pP` and `pQ` on the target side are given split as an inverse
comparison followed by the image of a product, and the comparisons are natural for `t`; then the
square `pP ≫ F.map amn = t' ≫ pQ` is the image under `F` of the square on the source side. The
splittings and the naturality are hypotheses for the reason recorded on `mul_of_split_gen`. -/
public theorem map_eq_of_split_gen {D : Type*} [Category D] (F : C ⥤ D) {SP SQ Pmn Qmn : C}
    {TP TQ : D} {mulP : SP ⟶ Pmn} {mulQ : SQ ⟶ Qmn} {t : SP ⟶ SQ} {amn : Pmn ⟶ Qmn}
    (i : F.obj SP ≅ TP) (j : F.obj SQ ≅ TQ) {t' : TP ⟶ TQ} {pP : TP ⟶ F.obj Pmn}
    {pQ : TQ ⟶ F.obj Qmn} (hP : pP = i.inv ≫ F.map mulP) (hQ : pQ = j.inv ≫ F.map mulQ)
    (hn : F.map t ≫ j.hom = i.hom ≫ t') (h : pP ≫ F.map amn = t' ≫ pQ) :
    F.map (mulP ≫ amn) = F.map (t ≫ mulQ) := by
  have hP' : F.map mulP = i.hom ≫ pP := by rw [hP, Iso.hom_inv_id_assoc]
  have hQ' : F.map mulQ = j.hom ≫ pQ := by rw [hQ, Iso.hom_inv_id_assoc]
  rw [F.map_comp, F.map_comp, hP', hQ', Category.assoc, h, ← Category.assoc, ← hn,
    Category.assoc]

end Generic

/-! ### The inverse image of a morphism-level product -/

variable {W Z Y T V X : Scheme.{u}}

/-- **The inverse image of a morphism-level product along `f`.** The inverse Tag 01CD comparison
between the tensor product of the inverse images and the inverse image of the tensor product,
followed by the inverse image of the product; the comparison is invertible unconditionally, which
is what makes the definition possible.

`Stacks.AlgebraicGeometry.Tag07ZGTwist.pullbackRelativeTwistMul` is this at the glued twist
algebra, and is equal to it by `rfl`. -/
public def pbMul (f : X ⟶ Y) {Pm Pn Pmn : Y.Modules}
    (mul : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (Pm)).obj (Pn)) ⟶ Pmn) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X.toRingedSpace)).presheaf,
      ((X.toRingedSpace)).IsSheaf⟩).obj (((Scheme.Modules.pullback f).obj Pm))).obj
      (((Scheme.Modules.pullback f).obj Pn))) ⟶
      (Scheme.Modules.pullback f).obj Pmn :=
  (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).inv.app (Pm, Pn) ≫
    (Scheme.Modules.pullback f).map mul

/-- **`pbMul` split into its two factors.** True by `rfl`, and stated as a declaration of its own
so that the conversion between the two spellings of the tensor product sheaf is paid here, once,
with nothing else in the budget; see the implementation note on `mul_of_split_gen`. -/
public theorem pbMul_eq (f : X ⟶ Y) {Pm Pn Pmn : Y.Modules}
    (mul : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (Pm)).obj (Pn)) ⟶ Pmn) :
    pbMul f mul =
      (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).inv.app (Pm, Pn) ≫
        (Scheme.Modules.pullback f).map mul := rfl

/-- The forward Tag 01CD comparison composed with `pbMul` is the inverse image of the product. -/
public theorem comparison_comp_pbMul (f : X ⟶ Y) {Pm Pn Pmn : Y.Modules}
    (mul : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (Pm)).obj (Pn)) ⟶ Pmn) :
    (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app (Pm, Pn) ≫
        pbMul f mul = (Scheme.Modules.pullback f).map mul :=
  Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans
      (congrArg (fun k => k ≫ (Scheme.Modules.pullback f).map mul)
        (Iso.hom_inv_id_app
          (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom) (Pm, Pn)))
      (Category.id_comp _))

/-! ### Multiplicative families at the tensor product sheaf -/

section Algebra

variable {Pm Pn Pmn Qm Qn Qmn Rm Rn Rmn : X.Modules}

/-- **The identity family is multiplicative.** -/
public theorem mul_id (mulP : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
  ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (Pm)).obj (Pn)) ⟶ Pmn) :
    mulP ≫ 𝟙 Pmn = ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map (((𝟙 Pm), (𝟙 Pn)) : (_, _) ⟶
      (_, _))) ≫ mulP :=
  mul_id_gen mulP (tensorSheafMap_id X.toRingedSpace Pm Pn)

/-- **Two multiplicative families compose.** -/
public theorem mul_comp {mulP : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
  ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (Pm)).obj (Pn)) ⟶ Pmn}
    {mulQ : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (Qm)).obj (Qn)) ⟶ Qmn}
    {mulR : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (Rm)).obj (Rn)) ⟶ Rmn}
    {am : Pm ⟶ Qm} {an : Pn ⟶ Qn} {amn : Pmn ⟶ Qmn}
    {bm : Qm ⟶ Rm} {bn : Qn ⟶ Rn} {bmn : Qmn ⟶ Rmn}
    (ha : mulP ≫ amn = ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X.toRingedSpace)).presheaf,
      ((X.toRingedSpace)).IsSheaf⟩)).map ((am, an) : (_, _) ⟶ (_, _))) ≫ mulQ)
    (hb : mulQ ≫ bmn = ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X.toRingedSpace)).presheaf,
      ((X.toRingedSpace)).IsSheaf⟩)).map ((bm, bn) : (_, _) ⟶ (_, _))) ≫ mulR) :
    mulP ≫ (amn ≫ bmn) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map (((am ≫ bm), (an ≫ bn)) :
        (_, _) ⟶ (_, _))) ≫ mulR :=
  mul_comp_gen (tensorSheafMap_comp X.toRingedSpace am bm an bn) ha hb

/-- **The inverse of a multiplicative family of isomorphisms is multiplicative.** -/
public theorem mul_inv {mulP : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
  ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (Pm)).obj (Pn)) ⟶ Pmn}
    {mulQ : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (Qm)).obj (Qn)) ⟶ Qmn}
    (am : Pm ≅ Qm) (an : Pn ≅ Qn) (amn : Pmn ≅ Qmn)
    (ha : mulP ≫ amn.hom = ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((X.toRingedSpace)).presheaf,
      ((X.toRingedSpace)).IsSheaf⟩)).map ((am.hom, an.hom) : (_, _) ⟶ (_, _))) ≫ mulQ) :
    mulQ ≫ amn.inv = ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map ((am.inv, an.inv) : (_, _) ⟶
      (_, _))) ≫ mulP :=
  mul_inv_gen
    ((tensorSheafMap_comp X.toRingedSpace am.inv am.hom an.inv an.hom).symm.trans
      ((congrArg ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map (X := (Qm, Qn)) (Y := (Qm, Qn)))
          (Prod.ext am.inv_hom_id an.inv_hom_id)).trans
        (tensorSheafMap_id X.toRingedSpace Qm Qn)))
    ha

end Algebra

/-! ### The structural isomorphisms of the inverse image are multiplicative -/

/-- **The congruence isomorphism of a factorisation is multiplicative.** Discharged by `subst`,
after which the component is the identity and nothing is converted; this is the device
`Stacks.AlgebraicGeometry.TwistMultTransport.transport_congr_step` records. -/
public theorem mul_pullbackCongr {f g : X ⟶ Y} (hf : f = g) {Pm Pn Pmn : Y.Modules}
    (mul : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (Pm)).obj (Pn)) ⟶ Pmn) :
    pbMul f mul ≫ (Scheme.Modules.pullbackCongr hf).hom.app Pmn =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map
        ((((Scheme.Modules.pullbackCongr hf).hom.app Pm), ((Scheme.Modules.pullbackCongr hf).hom.app
        Pn)) : (_, _) ⟶ (_, _))) ≫ pbMul g mul := by
  subst hf
  refine Eq.trans (congrArg (fun z => pbMul f mul ≫ z) (pullbackCongr_rfl_hom_app f Pmn)) ?_
  refine Eq.trans (mul_id (pbMul f mul)) ?_
  exact congrArg (fun z => z ≫ pbMul f mul)
    (congrArg ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
          (X := ((Scheme.Modules.pullback f).obj Pm, (Scheme.Modules.pullback f).obj Pn))
          (Y := ((Scheme.Modules.pullback f).obj Pm, (Scheme.Modules.pullback f).obj Pn)))
      (Prod.ext (pullbackCongr_rfl_hom_app f Pm).symm (pullbackCongr_rfl_hom_app f Pn).symm))

/-- **The inverse Tag 01CD comparison for a composite, against the pseudofunctoriality
isomorphism.** The `inv`-direction of `Stacks.AlgebraicGeometry.TwistMultCompat`'s
`comparison_pullbackComp_hom`, obtained from it by `conj_nat_gen` at the composite isomorphism
whose factors are the two comparisons. Its own declaration: the `whnf` cost of the conversion
between the two spellings of the tensor product sheaf is cumulative over a declaration, and this
step and `pullbackComp_hom_split` do not both fit beside `mul_of_split_gen`. -/
public theorem conj_comparison_pullbackComp (k : W ⟶ Z) (h : Z ⟶ Y) (Pm Pn : Y.Modules) :
    (Stacks.PullbackTensorIso.pullbackTensorIso k.toLRSHom.toShHom).inv.app
          ((Scheme.Modules.pullback h).obj Pm, (Scheme.Modules.pullback h).obj Pn) ≫
        ((Scheme.Modules.pullback k).map
            ((Stacks.PullbackTensorIso.pullbackTensorIso
              h.toLRSHom.toShHom).inv.app (Pm, Pn)) ≫
          (Scheme.Modules.pullbackComp k h).hom.app
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩))).obj (Pm, Pn))) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((W.toRingedSpace)).presheaf, ((W.toRingedSpace)).IsSheaf⟩)).map
        ((((Scheme.Modules.pullbackComp k h).hom.app Pm), ((Scheme.Modules.pullbackComp k h).hom.app
        Pn)) : (_, _) ⟶ (_, _))) ≫
        (Stacks.PullbackTensorIso.pullbackTensorIso
          (k ≫ h).toLRSHom.toShHom).inv.app (Pm, Pn) :=
  (Category.assoc _ _ _).symm.trans
    (conj_nat_gen
      ((Scheme.Modules.pullback k).mapIso
          ((Stacks.PullbackTensorIso.pullbackTensorIso h.toLRSHom.toShHom).app (Pm, Pn)) ≪≫
        (Stacks.PullbackTensorIso.pullbackTensorIso k.toLRSHom.toShHom).app
          ((Scheme.Modules.pullback h).obj Pm, (Scheme.Modules.pullback h).obj Pn))
      ((Stacks.PullbackTensorIso.pullbackTensorIso (k ≫ h).toLRSHom.toShHom).app (Pm, Pn))
      (comparison_pullbackComp_hom k h Pm Pn))

/-- **The inverse image along `k` of `pbMul h mul`, followed by the pseudofunctoriality
isomorphism**, split as the comparison factor followed by the inverse image of the product along
the composite. This is the naturality of the pseudofunctoriality isomorphism at the product, with
the leading comparison factor pulled out. -/
public theorem pullbackComp_hom_split (k : W ⟶ Z) (h : Z ⟶ Y) {Pm Pn Pmn : Y.Modules}
    (mul : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (Pm)).obj (Pn)) ⟶ Pmn) :
    (Scheme.Modules.pullback k).map (pbMul h mul) ≫
        (Scheme.Modules.pullbackComp k h).hom.app Pmn =
      ((Scheme.Modules.pullback k).map
            ((Stacks.PullbackTensorIso.pullbackTensorIso
              h.toLRSHom.toShHom).inv.app (Pm, Pn)) ≫
          (Scheme.Modules.pullbackComp k h).hom.app
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩))).obj (Pm, Pn))) ≫
        (Scheme.Modules.pullback (k ≫ h)).map mul :=
  (congrArg
      (fun z => (Scheme.Modules.pullback k).map z ≫
        (Scheme.Modules.pullbackComp k h).hom.app Pmn)
      (pbMul_eq h mul)).trans
    ((congrArg (fun z => z ≫ (Scheme.Modules.pullbackComp k h).hom.app Pmn)
          ((Scheme.Modules.pullback k).map_comp _ _)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg
            (fun z => (Scheme.Modules.pullback k).map
              ((Stacks.PullbackTensorIso.pullbackTensorIso
                h.toLRSHom.toShHom).inv.app (Pm, Pn)) ≫ z)
            ((Scheme.Modules.pullbackComp k h).hom.naturality mul)).trans
          (Category.assoc _ _ _).symm)))

/-- **The pseudofunctoriality isomorphism is multiplicative**: it carries the twice-iterated
inverse image of a product to the inverse image of the product along the composite. -/
public theorem mul_pullbackComp (k : W ⟶ Z) (h : Z ⟶ Y) {Pm Pn Pmn : Y.Modules}
    (mul : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (Pm)).obj (Pn)) ⟶ Pmn) :
    pbMul k (pbMul h mul) ≫ (Scheme.Modules.pullbackComp k h).hom.app Pmn =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((W.toRingedSpace)).presheaf, ((W.toRingedSpace)).IsSheaf⟩)).map
        ((((Scheme.Modules.pullbackComp k h).hom.app Pm), ((Scheme.Modules.pullbackComp k h).hom.app
        Pn)) : (_, _) ⟶ (_, _))) ≫ pbMul (k ≫ h) mul :=
  mul_of_split_gen (pbMul_eq k (pbMul h mul)) (pbMul_eq (k ≫ h) mul)
    (conj_comparison_pullbackComp k h Pm Pn) (pullbackComp_hom_split k h mul)

/-- **The inverse Tag 01CD comparison is natural in its two module arguments.** The `inv`
counterpart of `Stacks.AlgebraicGeometry.TwistMultCompat.comparison_tensorSheafMap_nat`. -/
public theorem conj_comparison_tensorSheafMap (f : X ⟶ Y) {Pm Pn Qm Qn : Y.Modules}
    (am : Pm ⟶ Qm) (an : Pn ⟶ Qn) :
    (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).inv.app (Pm, Pn) ≫
        (Scheme.Modules.pullback f).map (((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((Y.toRingedSpace)).presheaf,
          ((Y.toRingedSpace)).IsSheaf⟩)).map ((am, an) : (_, _) ⟶ (_, _)))) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map
        ((((Scheme.Modules.pullback f).map am), ((Scheme.Modules.pullback f).map an)) : (_, _) ⟶ (_,
        _))) ≫
        (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).inv.app (Qm, Qn) :=
  conj_nat_gen
    ((Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).app (Pm, Pn))
    ((Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).app (Qm, Qn))
    (comparison_tensorSheafMap_nat f am an).symm

/-- **The inverse image of a multiplicative family is multiplicative.** -/
public theorem mul_pullback (f : X ⟶ Y) {Pm Pn Pmn Qm Qn Qmn : Y.Modules}
    {mulP : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (Pm)).obj (Pn)) ⟶ Pmn}
    {mulQ : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (Qm)).obj (Qn)) ⟶ Qmn}
    {am : Pm ⟶ Qm} {an : Pn ⟶ Qn} {amn : Pmn ⟶ Qmn}
    (ha : mulP ≫ amn = ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((Y.toRingedSpace)).presheaf,
      ((Y.toRingedSpace)).IsSheaf⟩)).map ((am, an) : (_, _) ⟶ (_, _))) ≫ mulQ) :
    pbMul f mulP ≫ (Scheme.Modules.pullback f).map amn =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map
        ((((Scheme.Modules.pullback f).map am), ((Scheme.Modules.pullback f).map an)) : (_, _) ⟶ (_,
        _))) ≫ pbMul f mulQ :=
  mul_of_split_gen (pbMul_eq f mulP) (pbMul_eq f mulQ)
    (conj_comparison_tensorSheafMap f am an)
    (map_sq_gen (Scheme.Modules.pullback f) ha)

/-- **A multiplicative square for inverse images, read back as an equation between two inverse
images.** This is the shape in which a locality reduction on the pieces of an open consumes the
square: both sides are the inverse image along `f` of a composite on the base. -/
public theorem map_eq_of_mul_pullback (f : X ⟶ Y) {Pm Pn Pmn Qm Qn Qmn : Y.Modules}
    (mulP : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (Pm)).obj (Pn)) ⟶ Pmn)
    (mulQ : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (Qm)).obj (Qn)) ⟶ Qmn)
    (am : Pm ⟶ Qm) (an : Pn ⟶ Qn) (amn : Pmn ⟶ Qmn)
    (h : pbMul f mulP ≫ (Scheme.Modules.pullback f).map amn =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map
        ((((Scheme.Modules.pullback f).map am), ((Scheme.Modules.pullback f).map an)) : (_, _) ⟶ (_,
        _))) ≫ pbMul f mulQ) :
    (Scheme.Modules.pullback f).map (mulP ≫ amn) =
      (Scheme.Modules.pullback f).map (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨((Y.toRingedSpace)).presheaf,
        ((Y.toRingedSpace)).IsSheaf⟩)).map ((am, an) : (_, _) ⟶ (_, _))) ≫ mulQ) :=
  map_eq_of_split_gen (Scheme.Modules.pullback f)
    ((Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).app (Pm, Pn))
    ((Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).app (Qm, Qn))
    (pbMul_eq f mulP) (pbMul_eq f mulQ) (comparison_tensorSheafMap_nat f am an) h

/-! ### The leg identification, and its multiplicativity -/

/-- **The four-factor leg identification.** For a factorisation `k ≫ h = ρ ≫ hU ≫ c` of a
morphism of schemes and an identification `χ` of the inverse image of `M` along `c` with `N`, the
identification of `k^*h^*M` with `ρ^*hU^*N` assembled from the two pseudofunctoriality
isomorphisms of the inverse image, the congruence isomorphism of the factorisation, and `χ`.

`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartSourceIso` and `chartTargetIso` are both instances of
this by `rfl`: `chartSourceIso` is the leg of `r_ψ` along the chart of `Proj_S(A)` over an affine
open of the base, and `chartTargetIso` the leg of the inclusion of `U(ψ)` along the chart of
`Proj_S(B)`. The two legs conjugate by the *same* isomorphism `ρ`, which is why one lemma about a
single leg serves for both. -/
public def legIso (k : W ⟶ Z) (h : Z ⟶ Y) (ρ : W ⟶ T) (hU : T ⟶ V) (c : V ⟶ Y)
    (e : k ≫ h = ρ ≫ hU ≫ c) {M : Y.Modules} {N : V.Modules}
    (χ : (Scheme.Modules.pullback c).obj M ≅ N) :
    (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback h).obj M) ≅
      (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback hU).obj N) :=
  (Scheme.Modules.pullbackComp k h).app M ≪≫
    (Scheme.Modules.pullbackCongr e).app M ≪≫
    ((Scheme.Modules.pullbackComp ρ (hU ≫ c)).app M).symm ≪≫
    (Scheme.Modules.pullback ρ).mapIso
      (((Scheme.Modules.pullbackComp hU c).app M).symm ≪≫
        (Scheme.Modules.pullback hU).mapIso χ)

/-- **The inner two factors of the leg are multiplicative.** The pseudofunctoriality isomorphism
of `hU ≫ c` read backwards, followed by the inverse image along `hU` of `χ`, carries the inverse
image of `mulY` along `hU ≫ c` to the inverse image of `mulV` along `hU`. -/
public theorem legInner_mul (hU : T ⟶ V) (c : V ⟶ Y)
    {Mm Mn Mmn : Y.Modules} {Nm Nn Nmn : V.Modules}
    (mulY : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (Mm)).obj (Mn)) ⟶ Mmn)
    (mulV : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((V.toRingedSpace)).presheaf, ((V.toRingedSpace)).IsSheaf⟩).obj (Nm)).obj (Nn)) ⟶ Nmn)
    (χm : (Scheme.Modules.pullback c).obj Mm ≅ Nm)
    (χn : (Scheme.Modules.pullback c).obj Mn ≅ Nn)
    (χmn : (Scheme.Modules.pullback c).obj Mmn ≅ Nmn)
    (hχ : pbMul c mulY ≫ χmn.hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((V.toRingedSpace)).presheaf, ((V.toRingedSpace)).IsSheaf⟩)).map ((χm.hom, χn.hom) : (_, _)
        ⟶ (_, _))) ≫ mulV) :
    pbMul (hU ≫ c) mulY ≫
        (((Scheme.Modules.pullbackComp hU c).app Mmn).symm ≪≫
          (Scheme.Modules.pullback hU).mapIso χmn).hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((T.toRingedSpace)).presheaf, ((T.toRingedSpace)).IsSheaf⟩)).map
        (((((Scheme.Modules.pullbackComp hU c).app Mm).symm ≪≫
            (Scheme.Modules.pullback hU).mapIso χm).hom, (((Scheme.Modules.pullbackComp hU c).app
              Mn).symm ≪≫
            (Scheme.Modules.pullback hU).mapIso χn).hom) : (_, _) ⟶ (_, _))) ≫
        pbMul hU mulV :=
  mul_comp
    (mul_inv ((Scheme.Modules.pullbackComp hU c).app Mm)
      ((Scheme.Modules.pullbackComp hU c).app Mn)
      ((Scheme.Modules.pullbackComp hU c).app Mmn)
      (mul_pullbackComp hU c mulY))
    (mul_pullback hU hχ)

/-- **The leg transport.** If `χ` carries the inverse image of `mulY` along `c` to `mulV`, then
the leg identification carries the twice-iterated inverse image of `mulY` along `k` and `h` to the
twice-iterated inverse image of `mulV` along `ρ` and `hU`.

The four factors are discharged in turn: `mul_pullbackComp` for the pseudofunctoriality of
`k ≫ h`, `mul_pullbackCongr` for the factorisation, `mul_inv` of `mul_pullbackComp` for the
pseudofunctoriality of `ρ ≫ hU ≫ c` read backwards, and `mul_pullback` of `legInner_mul` for the
inverse image along `ρ` of the inner two. No hypothesis beyond the factorisation `e` is used; in
particular `ρ` need not be invertible. -/
public theorem leg_mul (k : W ⟶ Z) (h : Z ⟶ Y) (ρ : W ⟶ T) (hU : T ⟶ V) (c : V ⟶ Y)
    (e : k ≫ h = ρ ≫ hU ≫ c)
    {Mm Mn Mmn : Y.Modules} {Nm Nn Nmn : V.Modules}
    (mulY : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (Mm)).obj (Mn)) ⟶ Mmn)
    (mulV : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((V.toRingedSpace)).presheaf, ((V.toRingedSpace)).IsSheaf⟩).obj (Nm)).obj (Nn)) ⟶ Nmn)
    (χm : (Scheme.Modules.pullback c).obj Mm ≅ Nm)
    (χn : (Scheme.Modules.pullback c).obj Mn ≅ Nn)
    (χmn : (Scheme.Modules.pullback c).obj Mmn ≅ Nmn)
    (hχ : pbMul c mulY ≫ χmn.hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((V.toRingedSpace)).presheaf, ((V.toRingedSpace)).IsSheaf⟩)).map ((χm.hom, χn.hom) : (_, _)
        ⟶ (_, _))) ≫ mulV) :
    pbMul k (pbMul h mulY) ≫ (legIso k h ρ hU c e χmn).hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((W.toRingedSpace)).presheaf, ((W.toRingedSpace)).IsSheaf⟩)).map (((legIso k h ρ hU c e
        χm).hom, (legIso k h ρ hU c e χn).hom) : (_, _) ⟶ (_, _))) ≫
        pbMul ρ (pbMul hU mulV) :=
  mul_comp (mul_pullbackComp k h mulY)
    (mul_comp (mul_pullbackCongr e mulY)
      (mul_comp
        (mul_inv ((Scheme.Modules.pullbackComp ρ (hU ≫ c)).app Mm)
          ((Scheme.Modules.pullbackComp ρ (hU ≫ c)).app Mn)
          ((Scheme.Modules.pullbackComp ρ (hU ≫ c)).app Mmn)
          (mul_pullbackComp ρ (hU ≫ c) mulY))
        (mul_pullback ρ (legInner_mul hU c mulY mulV χm χn χmn hχ))))

end Stacks.AlgebraicGeometry.TwistMulLeg

end
