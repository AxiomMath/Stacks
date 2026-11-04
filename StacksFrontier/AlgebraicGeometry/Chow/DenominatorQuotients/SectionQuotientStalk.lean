module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.DenominatorActionStalk
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.StalkFractionalIdeal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BoxProductRightOperator

/-!
# The stalk of the second denominator quotient

Let `X` be a scheme, `L` and `F` sheaves of `𝒪_X`-modules and `s` a meromorphic section of `L`
with ideal of denominators `I`. The second canonical map of
[Stacks, Tag 02P2](https://stacks.math.columbia.edu/tag/02P2) is multiplication by `s` from the
product `I F` into `F ⊗ L`, and the second denominator quotient `Q₂ = (F ⊗ L) / s(I F)` of
[Stacks, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW) is its cokernel. This file computes
the stalk of `Q₂` at a point: for an invertible `L` it is

  `(Q₂)_x ≅ F_x / J · F_x`,   `J = Ideal.fractionalProductIdeal a b`

for a local ratio `a / b` of `s` at `x`. Together with
`Stacks.Chow.DenominatorStalk.denominatorQuotientStalkLinearEquivDenominatorIdeal`, which is the
same statement for the first quotient with `Ideal.denominatorIdeal a b` in place of `J`, and with
**one and the same ratio `a / b`**, that is the input of part (4) of Tag 02SW: the length formula
of [Stacks, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH) —
`Ideal.length_fractionalProduct_quotient_sub_length_denominator_quotient` — computes exactly the
difference of the colengths of those two ideals.

Three steps make up the computation, and only the first is specific to the second quotient.

* The product `I F` is the image of the action `I ⊗ F ⟶ F`, so the second canonical map is
  determined by one equation: precomposed with the epimorphism onto that image it is
  `AlgebraicGeometry.denominatorIdealSectionTensor`, the map `I ⊗ F ⟶ F ⊗ L` sending `d ⊗ n` to
  `n ⊗ (d s)`. The stalk of an epimorphism is surjective, so the range of the stalk of the second
  canonical map is the range of the stalk of that composite — for *any* map satisfying the
  equation.
* On the germ of a local pure tensor the stalk of `denominatorIdealSectionTensor` is the product
  of the germ of `n` with the germ of `d s`, and the germs of `d s` are the fractional product
  ideal of the germs of `a` and `b` times a trivializing germ of `L`, by
  `Stacks.Chow.DenominatorStalk.mem_mulGerms_iff_coord_mem`.
* Tensoring with an invertible module does nothing to a stalk:
  `Stacks.InvertibleStalk.tensorStalkRightEquiv` identifies `(F ⊗ L)_x` with `F_x` and carries
  the product of `n` with the trivializing germ back to `n`, so the range of the stalk of the
  second canonical map is carried to `J · F_x`.

## Main definitions

* `Stacks.Chow.DenominatorStalk.sectionTensorStalk` — the stalk at `x` of
  `AlgebraicGeometry.denominatorIdealSectionTensor`, as a linear map over the local ring.
* `Stacks.Chow.DenominatorStalk.sectionQuotientStalkLinearEquiv` — the displayed identification,
  for an arbitrary map satisfying the factorization equation of the second canonical map.
* `Stacks.Chow.DenominatorStalk.denominatorSectionQuotientStalkLinearEquivFractionalProductIdeal`
  — the same at `Stacks.Chow.denominatorSectionQuotient`, that is at `Q₂` itself.

## Main results

* `Stacks.Chow.DenominatorStalk.denominatorIdealSectionTensor_val_app_toTensorSheafSection` and
  `Stacks.Chow.DenominatorStalk.sectionTensorStalk_germ_tmul` — multiplication by `s` on a local
  pure tensor, on sections and on germs: `d ⊗ n ↦ n ⊗ (d s)`.
* `Stacks.Chow.DenominatorStalk.map_range_sectionTensorStalk_eq_smul` — the range of the stalk of
  that map, transported to `F_x` by a trivializing basis of `L`, is the fractional product ideal
  acting on `F_x`.
* `Stacks.Chow.DenominatorStalk.range_stalkLinearMap_eq_range_sectionTensorStalk` and
  `Stacks.Chow.DenominatorStalk.map_range_stalkLinearMap_eq_smul` — the same for any map
  satisfying the factorization equation, in particular for the second canonical map.
* `Stacks.Chow.DenominatorStalk.exists_affineOpen_map_range_stalkLinearMap_eq` — around every
  point there is an affine open carrying a ratio for which the ranges of the stalks of **both**
  canonical maps are the two colon ideals of that ratio acting on `F_x`. Its only hypothesis
  beyond the factorization equation is that `L` is invertible.
* `Stacks.Chow.DenominatorStalk.exists_affineOpen_nonempty_denominatorQuotientStalkLinearEquivs` —
  the same for the two quotients themselves: around every point there is an affine open and a
  ratio `a / b` with `(Q₁)_x ≅ F_x / (I a b) F_x` and `(Q₂)_x ≅ F_x / (J a b) F_x`.
* `Stacks.Chow.DenominatorStalk.length_denominatorQuotientStalk`,
  `Stacks.Chow.DenominatorStalk.length_denominatorSectionQuotientStalk` and
  `Stacks.Chow.DenominatorStalk.exists_affineOpen_length_denominatorQuotientStalk_eq` — the same
  two identifications as equalities of `Module.length`, which is the form the length formula of
  [Stacks, Tag 02QH] consumes.

## Implementation notes

The hypothesis budget of everything up to
`Stacks.Chow.DenominatorStalk.map_range_stalkLinearMap_eq_smul` is **invertibility of `L` and the
factorization equation, and nothing else**: no Noetherian hypothesis, no coherence, no condition
on associated points and no generic point. That is deliberate and is why the second canonical map
appears as a variable `f` together with the equation it satisfies rather than as
`AlgebraicGeometry.denominatorIdealTimesModuleMul`. The local Noetherianity, coherence,
no-embedded-points and full-support hypotheses of Tag 02P2 enter only where `Q₂` is *formed* —
`Stacks.Chow.denominatorSectionQuotient` does not exist without them, because the second
canonical map does not — so in
`denominatorSectionQuotientStalkLinearEquivFractionalProductIdeal` and
`exists_affineOpen_nonempty_denominatorQuotientStalkLinearEquivs` they are the arguments that
build the morphism and are used for nothing else. The passage to lengths adds nothing to that
budget: `LinearEquiv.length_eq` is Mathlib's, in `Mathlib.RingTheory.Length`, and it has no
finiteness hypothesis at all, because `Module.length` is the Krull dimension of the submodule
lattice valued in `ℕ∞` rather than a cardinality of a composition series. The Noetherian and
finiteness conditions that [Stacks, Tag 02QH] needs are conditions of *that formula*, not of this
transfer, and they are discharged where the formula is applied.

The sections-level formula for `denominatorIdealSectionTensor` is the composite of
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection` with
`Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap_app_toTensorSheafSection`; the two
constraints of the monoidal structure appearing in the definition of that map,
`Stacks.SheafOfModules.Invertible.tensorProductBifunctor.map` and
`Stacks.SheafOfModules.Invertible.tensorProductBraiding`, are the same terms as
`tensorSheafMap` and `tensorSheafSwap` of a ringed space, so the two formulas apply by `exact`.
This is the analogue for the second canonical map of
`Stacks.SheafOfModules.denominatorIdealAction_val_app_toTensorSheafSection`, which plays that
role for the first.

The import of
`StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BoxProductRightOperator` is there for
`tensorSheafSwap_app_toTensorSheafSection` alone, and is the one oddity in the layering of this
file: that lemma is about
`Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap`, which is *defined* in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations`, so its natural home is beside
its subject rather than in a file about the box product of modules of differentials. Moving it
there would drop this edge; it is left alone deliberately, as a shared file is not worth editing
for one import, and this paragraph is the pointer for whoever next reorganises that area.

Two definitionally equal `Module (X.presheaf.stalk x) (F.presheaf.stalk x)` instances are in the
import closure — `AlgebraicGeometry.Scheme.Modules.moduleStalk` and
`AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf` — and instance search does not cross
between them, so `rewrite` inside a membership statement about
`Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)` reports that it did not find the pattern.
Every such step here is therefore an `Eq.trans`, a `congrArg` or an `Eq.mpr` with the equation
passed as an argument, and the two inclusions of the range computation follow the pattern of
`Stacks.Chow.DenominatorStalk.range_denominatorIdealActionStalk`: the equation is stated in a
`have` of its own, where no membership is involved, and only then rewritten.

`open AlgebraicGeometry hiding denominatorIdeal denominatorIdealι denominatorIdealMul` is
required, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.DenominatorActionStalk`: the three names
are ambiguous between `Stacks.DenominatorIdeal` and `AlgebraicGeometry`. The statements here use
the `AlgebraicGeometry` spelling throughout, and the hypotheses supplied by
`Stacks.DenominatorMul.exists_affineOpen_denominator_presentations` are in the
`Stacks.DenominatorIdeal` spelling; the crossing is a `rfl`, and the two names are left alone.

## References

* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02P2](https://stacks.math.columbia.edu/tag/02P2)
* [Stacks Project, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry hiding denominatorIdeal denominatorIdealι denominatorIdealMul
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.SheafOfModules.TensorPresentations (tensorSheafSwap_app_toTensorSheafSection)
open Stacks.InvertibleStalk (tensorStalkRightEquiv tensorStalkRightEquiv_tensorStalkTmul')

universe u

namespace Stacks.Chow.DenominatorStalk

variable (X : Scheme.{u}) (L F : X.Modules)
  (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)

/-- The ideal of denominators at the declared type `X.Modules`, written with the
`AlgebraicGeometry` spelling of `denominatorIdeal`. It is needed for the same reason as the
namesake in `StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.DenominatorActionStalk`: the
module structure on the stalk of a sheaf of modules on a scheme is found by instance search only
at this declared type, and a type ascription on a term does not reach instance search, which
re-infers the type from the term. The `Stacks.DenominatorIdeal` spelling is deliberately *not*
used: a statement mixing the two has to unfold both, which exhausts the heartbeat budget of a
single declaration at `whnf`. -/
private abbrev denominatorIdealSectionModules : X.Modules :=
  AlgebraicGeometry.denominatorIdeal X L s

/-- The stalk at `x` of the map `I ⊗ F ⟶ F ⊗ L` sending `d ⊗ n` to `n ⊗ (d s)`, as a linear map
over the local ring. The second canonical map of [Stacks, Tag 02P2] is this one factored through
the image of the action of `I` on `F`, so the two have the same range on every stalk. -/
abbrev sectionTensorStalk (x : X) :
    (Stacks.Chow.denominatorIdealTensorModule L F s).presheaf.stalk x →ₗ[X.presheaf.stalk x]
      (Scheme.Modules.tensorObj F L).presheaf.stalk x :=
  AlgebraicGeometry.stalkLinearMap (Stacks.Chow.denominatorIdealTensorModule L F s)
    (Scheme.Modules.tensorObj F L) (AlgebraicGeometry.denominatorIdealSectionTensor X L F s) x

/-- **Multiplication by `s` on a local pure tensor, on sections.** The map
`AlgebraicGeometry.denominatorIdealSectionTensor` is the functoriality of the sheaf tensor product
applied to multiplication by `s`, followed by the symmetry constraint; on a local pure tensor the
first step is
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection` and the
second is `Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap_app_toTensorSheafSection`.
This is the analogue for the second canonical map of
`Stacks.SheafOfModules.denominatorIdealAction_val_app_toTensorSheafSection`. -/
theorem denominatorIdealSectionTensor_val_app_toTensorSheafSection (W : Opens X)
    (d : (AlgebraicGeometry.denominatorIdeal X L s).val.obj (op W)) (n : F.val.obj (op W)) :
    ((AlgebraicGeometry.denominatorIdealSectionTensor X L F s).val.app (op W)).hom
        (toTensorSheafSection X.toRingedSpace (AlgebraicGeometry.denominatorIdeal X L s) F (op W)
          (d ⊗ₜ[X.presheaf.obj (op W)] n))
      = toTensorSheafSection X.toRingedSpace F L (op W)
          (n ⊗ₜ[X.presheaf.obj (op W)]
            ((AlgebraicGeometry.denominatorIdealMul X L s).val.app (op W)).hom d) := by
  refine Eq.trans (congrArg (fun z => ((Stacks.SheafOfModules.Invertible.tensorProductBraiding
      X.sheaf.obj X.ringCatSheaf.property L F).hom.val.app (op W)).hom z)
    (tensorSheafMap_app_toTensorSheafSection X.toRingedSpace
      (AlgebraicGeometry.denominatorIdeal X L s) F L F
      (AlgebraicGeometry.denominatorIdealMul X L s) (𝟙 F) W d n)) ?_
  exact tensorSheafSwap_app_toTensorSheafSection X.toRingedSpace L F W _ n

/-- **Multiplication by `s` on the germ of a local pure tensor.** It is the product in
`(F ⊗ L)_x` of the germ of the section of `F` with the germ of its product with `s`, by the
sections-level formula together with the compatibility of the product of Tag 01CB with germs. -/
theorem sectionTensorStalk_germ_tmul (x : X) (W : Opens X) (hxW : x ∈ W)
    (d : (AlgebraicGeometry.denominatorIdeal X L s).val.obj (op W)) (n : F.val.obj (op W)) :
    sectionTensorStalk X L F s x
        ((Stacks.Chow.denominatorIdealTensorModule L F s).presheaf.germ W x hxW
          (toTensorSheafSection X.toRingedSpace (AlgebraicGeometry.denominatorIdeal X L s) F
            (op W) (d ⊗ₜ[X.presheaf.obj (op W)] n))) =
      AlgebraicGeometry.tensorStalkTmul F L x (F.presheaf.germ W x hxW n)
        (L.presheaf.germ W x hxW
          (((AlgebraicGeometry.denominatorIdealMul X L s).val.app (op W)).hom d)) := by
  refine (AlgebraicGeometry.stalkLinearMap_germ _ (Scheme.Modules.tensorObj F L)
    (AlgebraicGeometry.denominatorIdealSectionTensor X L F s) W x hxW _).trans ?_
  refine Eq.trans (congrArg
    (ConcreteCategory.hom ((Scheme.Modules.tensorObj F L).presheaf.germ W x hxW))
    (denominatorIdealSectionTensor_val_app_toTensorSheafSection X L F s W d n)) ?_
  exact (AlgebraicGeometry.tensorStalkTmul_germ F L x W hxW n _).symm

variable {X L F s}

/-- Two local sections, restricted to the intersection of their domains, keep their germs, and the
restriction of `d` is still sent to the restriction of its product with `s`. -/
private theorem exists_restrict_inf_germ_eq {x : X} {W₁ W₂ : Opens X} (hxW₁ : x ∈ W₁)
    (hxW₂ : x ∈ W₂) (d₁ : (denominatorIdealSectionModules X L s).val.obj (op W₁))
    (n₂ : F.val.obj (op W₂)) :
    ∃ (d : (denominatorIdealSectionModules X L s).val.obj (op (W₁ ⊓ W₂)))
      (n : F.val.obj (op (W₁ ⊓ W₂))),
      (denominatorIdealSectionModules X L s).presheaf.germ (W₁ ⊓ W₂) x ⟨hxW₁, hxW₂⟩ d =
        (denominatorIdealSectionModules X L s).presheaf.germ W₁ x hxW₁ d₁ ∧
      F.presheaf.germ (W₁ ⊓ W₂) x ⟨hxW₁, hxW₂⟩ n = F.presheaf.germ W₂ x hxW₂ n₂ ∧
      ((AlgebraicGeometry.denominatorIdealMul X L s).val.app (op (W₁ ⊓ W₂))).hom d =
        L.presheaf.map (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)).op
          (((AlgebraicGeometry.denominatorIdealMul X L s).val.app (op W₁)).hom d₁) :=
  ⟨_, _, (denominatorIdealSectionModules X L s).presheaf.germ_res_apply _ x _ d₁,
    F.presheaf.germ_res_apply (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)) x _ n₂,
    PresheafOfModules.naturality_apply (AlgebraicGeometry.denominatorIdealMul X L s).val
      (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)).op d₁⟩

/-- The image of a pure tensor of stalks, transported to `F_x` by a trivializing basis of `L`,
lies in the ideal of the germs of the products `d s` acting on `F_x`: representing the two factors
on a common neighbourhood exhibits the preimage of the tensor as the germ of a local pure tensor,
by `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso_germ`. -/
private theorem mem_smul_of_tensorStalkIso_symm_tmul {x : X} {m : L.presheaf.stalk x}
    (hm : Stacks.Divisors.IsStalkBasis L x m) {J : Ideal (X.presheaf.stalk x)}
    (hJ : ∀ z : L.presheaf.stalk x, z ∈ mulGerms X L s x → hm.coord z ∈ J)
    (p : (denominatorIdealSectionModules X L s).presheaf.stalk x) (q : F.presheaf.stalk x) :
    tensorStalkRightEquiv F hm (sectionTensorStalk X L F s x
        ((tensorStalkIso X.toRingedSpace x (AlgebraicGeometry.denominatorIdeal X L s) F).symm
          (p ⊗ₜ[X.presheaf.stalk x] q))) ∈
      J • (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)) := by
  obtain ⟨W₁, hxW₁, d₁, hd₁⟩ := (denominatorIdealSectionModules X L s).presheaf.exists_germ_eq p
  obtain ⟨W₂, hxW₂, n₂, hn₂⟩ := F.presheaf.exists_germ_eq q
  obtain ⟨d, n, hpd, hqn, -⟩ := exists_restrict_inf_germ_eq (L := L) (s := s) hxW₁ hxW₂ d₁ n₂
  have hxW : x ∈ W₁ ⊓ W₂ := ⟨hxW₁, hxW₂⟩
  replace hpd : grpGerm X.toRingedSpace (AlgebraicGeometry.denominatorIdeal X L s).val x
      (W₁ ⊓ W₂) hxW d = p := hpd.trans hd₁
  replace hqn : grpGerm X.toRingedSpace F.val x (W₁ ⊓ W₂) hxW n = q := hqn.trans hn₂
  have hiso := (tensorStalkIso_germ X.toRingedSpace x
      (AlgebraicGeometry.denominatorIdeal X L s) F (W₁ ⊓ W₂) hxW d n).trans
    (by rw [hpd, hqn])
  have hsymm : (tensorStalkIso X.toRingedSpace x
        (AlgebraicGeometry.denominatorIdeal X L s) F).symm (p ⊗ₜ[X.presheaf.stalk x] q) =
      (Stacks.Chow.denominatorIdealTensorModule L F s).presheaf.germ (W₁ ⊓ W₂) x hxW
        (toTensorSheafSection X.toRingedSpace (AlgebraicGeometry.denominatorIdeal X L s) F
          (op (W₁ ⊓ W₂)) (d ⊗ₜ[X.presheaf.obj (op (W₁ ⊓ W₂))] n)) :=
    (LinearEquiv.symm_apply_eq _).2 hiso.symm
  have key := (congrArg (fun w => tensorStalkRightEquiv F hm (sectionTensorStalk X L F s x w))
      hsymm).trans
    (congrArg (fun w => tensorStalkRightEquiv F hm w)
      (sectionTensorStalk_germ_tmul X L F s x (W₁ ⊓ W₂) hxW d n))
  rw [key, tensorStalkRightEquiv_tensorStalkTmul' F hm _ _]
  exact Submodule.smul_mem_smul
    (hJ _ ⟨W₁ ⊓ W₂, hxW, _, ⟨d, rfl⟩, rfl⟩) Submodule.mem_top

/-- A germ of a product `d s`, read in the coordinate of a trivializing basis, carries the stalk
of `F` into the transported range: the germ and the element of the stalk are represented on a
common neighbourhood and recombined into a single local pure tensor there. -/
private theorem smul_mem_map_range {x : X} {m : L.presheaf.stalk x}
    (hm : Stacks.Divisors.IsStalkBasis L x m) {y : X.presheaf.stalk x}
    (hy : y • m ∈ mulGerms X L s x) (n : F.presheaf.stalk x) :
    y • n ∈ Submodule.map (tensorStalkRightEquiv F hm).toLinearMap
      (LinearMap.range (sectionTensorStalk X L F s x)) := by
  obtain ⟨W₁, hxW₁, t, ⟨d₁, rfl⟩, ht⟩ := hy
  obtain ⟨W₂, hxW₂, n₂, hn₂⟩ := F.presheaf.exists_germ_eq n
  obtain ⟨d, n', hpd, hqn, hres⟩ := exists_restrict_inf_germ_eq (L := L) (s := s) hxW₁ hxW₂ d₁ n₂
  have hxW : x ∈ W₁ ⊓ W₂ := ⟨hxW₁, hxW₂⟩
  replace hqn : F.presheaf.germ (W₁ ⊓ W₂) x hxW n' = n := hqn.trans hn₂
  have hgz : L.presheaf.germ (W₁ ⊓ W₂) x hxW
      (((AlgebraicGeometry.denominatorIdealMul X L s).val.app (op (W₁ ⊓ W₂))).hom d) =
      y • m := by
    rw [hres]
    exact (L.presheaf.germ_res_apply _ x hxW _).trans ht
  refine Submodule.mem_map.2 ⟨sectionTensorStalk X L F s x
    ((Stacks.Chow.denominatorIdealTensorModule L F s).presheaf.germ (W₁ ⊓ W₂) x hxW
      (toTensorSheafSection X.toRingedSpace (AlgebraicGeometry.denominatorIdeal X L s) F
        (op (W₁ ⊓ W₂)) (d ⊗ₜ[X.presheaf.obj (op (W₁ ⊓ W₂))] n'))), ⟨_, rfl⟩, ?_⟩
  show tensorStalkRightEquiv F hm (sectionTensorStalk X L F s x _) = y • n
  rw [sectionTensorStalk_germ_tmul X L F s x (W₁ ⊓ W₂) hxW d n',
    tensorStalkRightEquiv_tensorStalkTmul' F hm _ _, hgz, hqn]
  exact congrArg (fun c : X.presheaf.stalk x => c • n) (hm.coord_smul y)

/-- **The range of the stalk of multiplication by `s` on `I ⊗ F`, transported to the stalk of `F`
by a trivializing basis of `L`, is the ideal of the coordinates of the germs of the products
`d s`, acting on `F_x`.** The hypothesis holds with
`J = Ideal.fractionalProductIdeal (germ a) (germ b)` for a local ratio `a / b` of `s`, by
`Stacks.Chow.DenominatorStalk.mem_mulGerms_iff_coord_mem`. -/
theorem map_range_sectionTensorStalk_eq_smul {x : X} {m : L.presheaf.stalk x}
    (hm : Stacks.Divisors.IsStalkBasis L x m) {J : Ideal (X.presheaf.stalk x)}
    (hJ : ∀ z : L.presheaf.stalk x, z ∈ mulGerms X L s x ↔ hm.coord z ∈ J) :
    Submodule.map (tensorStalkRightEquiv F hm).toLinearMap
        (LinearMap.range (sectionTensorStalk X L F s x)) =
      J • (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)) := by
  refine le_antisymm ?_ ?_
  · rintro z hz
    obtain ⟨w, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_map.1 hz
    clear hz
    obtain ⟨t, rfl⟩ : ∃ t, (tensorStalkIso X.toRingedSpace x
        (AlgebraicGeometry.denominatorIdeal X L s) F).symm t = v :=
      ⟨tensorStalkIso X.toRingedSpace x (AlgebraicGeometry.denominatorIdeal X L s) F v,
        LinearEquiv.symm_apply_apply _ _⟩
    show tensorStalkRightEquiv F hm (sectionTensorStalk X L F s x _) ∈ _
    induction t using TensorProduct.induction_on with
    | zero =>
        have h1 : tensorStalkRightEquiv F hm (sectionTensorStalk X L F s x
            ((tensorStalkIso X.toRingedSpace x
              (AlgebraicGeometry.denominatorIdeal X L s) F).symm 0)) = 0 := by
          rw [map_zero]
          exact (congrArg (fun w => tensorStalkRightEquiv F hm w)
            ((sectionTensorStalk X L F s x).map_zero)).trans
              (tensorStalkRightEquiv F hm).map_zero
        rw [h1]
        exact Submodule.zero_mem _
    | add a b ha hb =>
        have h2 : tensorStalkRightEquiv F hm (sectionTensorStalk X L F s x
              ((tensorStalkIso X.toRingedSpace x
                (AlgebraicGeometry.denominatorIdeal X L s) F).symm (a + b))) =
            tensorStalkRightEquiv F hm (sectionTensorStalk X L F s x
                ((tensorStalkIso X.toRingedSpace x
                  (AlgebraicGeometry.denominatorIdeal X L s) F).symm a)) +
              tensorStalkRightEquiv F hm (sectionTensorStalk X L F s x
                ((tensorStalkIso X.toRingedSpace x
                  (AlgebraicGeometry.denominatorIdeal X L s) F).symm b)) := by
          rw [map_add]
          exact (congrArg (fun w => tensorStalkRightEquiv F hm w)
            ((sectionTensorStalk X L F s x).map_add _ _)).trans
              ((tensorStalkRightEquiv F hm).map_add _ _)
        rw [h2]
        exact Submodule.add_mem _ ha hb
    | tmul p q => exact mem_smul_of_tensorStalkIso_symm_tmul hm (fun z hz => (hJ z).1 hz) p q
  · refine Submodule.smul_le.2 fun r hr n _ => ?_
    refine smul_mem_map_range hm ((hJ (r • m)).2 ?_) n
    exact Eq.mpr (congrArg (fun z : X.presheaf.stalk x => z ∈ J) (hm.coord_smul r)) hr

/-- **The second canonical map of [Stacks, Tag 02P2] and multiplication by `s` on `I ⊗ F` have the
same range on every stalk.** The product `I F` is by definition the image of the action of `I` on
`F`, so by the equation characterising the second canonical map that map precomposed with the
epimorphism onto that image is multiplication by `s` on `I ⊗ F`; and the stalk map of an
epimorphism is surjective. Stated for an arbitrary `f` satisfying that equation, which is all the
construction of `AlgebraicGeometry.denominatorIdealTimesModuleMul` guarantees and all that is
needed. -/
theorem range_stalkLinearMap_eq_range_sectionTensorStalk
    (f : Stacks.Chow.denominatorIdealTimesModuleDecl L F s ⟶ Scheme.Modules.tensorObj F L)
    (hf : Abelian.factorThruImage (AlgebraicGeometry.denominatorIdealAction X L F s) ≫ f =
      AlgebraicGeometry.denominatorIdealSectionTensor X L F s)
    (x : X) :
    LinearMap.range (AlgebraicGeometry.stalkLinearMap
        (Stacks.Chow.denominatorIdealTimesModuleDecl L F s)
        (Scheme.Modules.tensorObj F L) f x) =
      LinearMap.range (sectionTensorStalk X L F s x) := by
  have hepiS := (Abelian.imageStrongEpiMonoFactorisation
    (AlgebraicGeometry.denominatorIdealAction X L F s)).e_strong_epi.epi
  have hepi : @Epi X.Modules _ (Stacks.Chow.denominatorIdealTensorModule L F s)
      (Stacks.Chow.denominatorIdealTimesModuleDecl L F s)
      (Abelian.factorThruImage (AlgebraicGeometry.denominatorIdealAction X L F s)) :=
    Stacks.Chow.epi_modules _ hepiS
  have hsurj := Stacks.Chow.surjective_stalkLinearMap_of_epi
    (Abelian.factorThruImage (AlgebraicGeometry.denominatorIdealAction X L F s)) hepi x
  refine Eq.trans (Stacks.Chow.range_stalkLinearMap_comp
    (Abelian.factorThruImage (AlgebraicGeometry.denominatorIdealAction X L F s)) f x hsurj).symm ?_
  exact congrArg (fun g => LinearMap.range (AlgebraicGeometry.stalkLinearMap
    (Stacks.Chow.denominatorIdealTensorModule L F s) (Scheme.Modules.tensorObj F L) g x)) hf

/-- **The range of the stalk of the second canonical map of [Stacks, Tag 02P2], transported to the
stalk of `F` by a trivializing basis of `L`.** -/
theorem map_range_stalkLinearMap_eq_smul
    (f : Stacks.Chow.denominatorIdealTimesModuleDecl L F s ⟶ Scheme.Modules.tensorObj F L)
    (hf : Abelian.factorThruImage (AlgebraicGeometry.denominatorIdealAction X L F s) ≫ f =
      AlgebraicGeometry.denominatorIdealSectionTensor X L F s)
    {x : X} {m : L.presheaf.stalk x} (hm : Stacks.Divisors.IsStalkBasis L x m)
    {J : Ideal (X.presheaf.stalk x)}
    (hJ : ∀ z : L.presheaf.stalk x, z ∈ mulGerms X L s x ↔ hm.coord z ∈ J) :
    Submodule.map (tensorStalkRightEquiv F hm).toLinearMap
        (LinearMap.range (AlgebraicGeometry.stalkLinearMap
          (Stacks.Chow.denominatorIdealTimesModuleDecl L F s)
          (Scheme.Modules.tensorObj F L) f x)) =
      J • (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)) :=
  (congrArg (Submodule.map (tensorStalkRightEquiv F hm).toLinearMap)
      (range_stalkLinearMap_eq_range_sectionTensorStalk f hf x)).trans
    (map_range_sectionTensorStalk_eq_smul hm hJ)

/-- **The stalk of the cokernel of the second canonical map of [Stacks, Tag 02P2] is the quotient
of the stalk of `F` by an ideal acting on it.** The ideal is the one of the coordinates of the
germs of the products `d s`, which for a local ratio `a / b` of `s` is
`Ideal.fractionalProductIdeal` of its germs. The identification is
`Stacks.Chow.cokernelStalkLinearEquiv` composed with
`Stacks.Chow.DenominatorStalk.map_range_stalkLinearMap_eq_smul`, the transport being
`Stacks.InvertibleStalk.tensorStalkRightEquiv`: the stalk of the cokernel is the quotient of
`(F ⊗ L)_x` by the range of the stalk of the map, and tensoring with an invertible module does
nothing to a stalk. -/
def sectionQuotientStalkLinearEquiv
    (f : Stacks.Chow.denominatorIdealTimesModuleDecl L F s ⟶ Scheme.Modules.tensorObj F L)
    (hf : Abelian.factorThruImage (AlgebraicGeometry.denominatorIdealAction X L F s) ≫ f =
      AlgebraicGeometry.denominatorIdealSectionTensor X L F s)
    {x : X} {m : L.presheaf.stalk x} (hm : Stacks.Divisors.IsStalkBasis L x m)
    {J : Ideal (X.presheaf.stalk x)}
    (hJ : ∀ z : L.presheaf.stalk x, z ∈ mulGerms X L s x ↔ hm.coord z ∈ J) :
    (F.presheaf.stalk x ⧸ (J • (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x))) :
        Type u)
      ≃ₗ[X.presheaf.stalk x] (cokernel f).presheaf.stalk x :=
  (Submodule.Quotient.equiv
      (LinearMap.range (AlgebraicGeometry.stalkLinearMap
        (Stacks.Chow.denominatorIdealTimesModuleDecl L F s)
        (Scheme.Modules.tensorObj F L) f x))
      (J • (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)))
      (tensorStalkRightEquiv F hm)
      (map_range_stalkLinearMap_eq_smul f hf hm hJ)).symm.trans
    (Stacks.Chow.cokernelStalkLinearEquiv f x)

/-- **Around every point of a scheme there is an affine open on which the meromorphic section is a
ratio `a / b` such that the ranges of the stalks of the two canonical maps of [Stacks, Tag 02P2]
are the two colon ideals of that ratio acting on the stalk of `F`** — `Ideal.denominatorIdeal` for
the first and `Ideal.fractionalProductIdeal` for the second, the second after transport by the
trivializing basis. The affine open, the ratio and the basis come from
`Stacks.DenominatorMul.exists_affineOpen_denominator_presentations`; the hypotheses are that `L`
is invertible and the equation characterising the second canonical map, and nothing else. -/
theorem exists_affineOpen_map_range_stalkLinearMap_eq
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (Stacks.DenominatorIdeal.O X).property L)
    (f : Stacks.Chow.denominatorIdealTimesModuleDecl L F s ⟶ Scheme.Modules.tensorObj F L)
    (hf : Abelian.factorThruImage (AlgebraicGeometry.denominatorIdealAction X L F s) ≫ f =
      AlgebraicGeometry.denominatorIdealSectionTensor X L F s)
    (x : X) :
    ∃ (V : Opens X) (hxV : x ∈ V), IsAffineOpen V ∧
      ∃ (a b : Γ(X, V)) (e : Γ(L, V))
        (hm : Stacks.Divisors.IsStalkBasis L x (L.presheaf.germ V x hxV e)),
        b ∈ nonZeroDivisors Γ(X, V) ∧
        LinearMap.range (denominatorIdealActionStalk X L F s x) =
            Ideal.denominatorIdeal (X.presheaf.germ V x hxV a) (X.presheaf.germ V x hxV b) •
              (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)) ∧
          Submodule.map (tensorStalkRightEquiv F hm).toLinearMap
              (LinearMap.range (AlgebraicGeometry.stalkLinearMap
                (Stacks.Chow.denominatorIdealTimesModuleDecl L F s)
                (Scheme.Modules.tensorObj F L) f x)) =
            Ideal.fractionalProductIdeal
                (X.presheaf.germ V x hxV a) (X.presheaf.germ V x hxV b) •
              (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)) := by
  obtain ⟨V, hxV, hVaff, a, b, e, hb, hm, hι, hmul⟩ :=
    Stacks.DenominatorMul.exists_affineOpen_denominator_presentations X L s hL x
  exact ⟨V, hxV, hVaff, a, b, e, hm, hb,
    range_denominatorIdealActionStalk_eq_denominatorIdeal_smul X L F s hVaff hι hxV,
    map_range_stalkLinearMap_eq_smul f hf hm
      (mem_mulGerms_iff_coord_mem X L s hVaff hmul hxV hm)⟩

/-- The second denominator quotient `Q₂` of [Stacks, Tag 02SW], at the declared type `X.Modules`.
The hypotheses are those of `Stacks.Chow.denominatorSectionQuotient`, which are the hypotheses
under which the second canonical map of [Stacks, Tag 02P2] is constructed at all; they are used
for nothing else here. -/
abbrev denominatorSectionQuotientDecl (L F : X.Modules)
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf L) [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) [F.IsCoherent]
    (hF : AlgebraicGeometry.HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ) :
    X.Modules :=
  Stacks.Chow.denominatorSectionQuotient X L F s hL hs hF hSupp

/-- **The stalk of the second denominator quotient of [Stacks, Tag 02SW] is the quotient of the
stalk of `F` by the fractional product ideal of the germs of a local ratio.** This is
`Stacks.Chow.DenominatorStalk.sectionQuotientStalkLinearEquiv` at the second canonical map of
[Stacks, Tag 02P2] — whose defining equation is exactly the subtype property of
`AlgebraicGeometry.denominatorIdealTimesModuleMul` — with the ideal supplied by
`Stacks.Chow.DenominatorStalk.mem_mulGerms_iff_coord_mem`, so that the submodule divided out is
presented by `Ideal.fractionalProductIdeal`, which is the form the length formula of
[Stacks, Tag 02QH] is stated in.

It is the counterpart of
`Stacks.Chow.DenominatorStalk.denominatorQuotientStalkLinearEquivDenominatorIdeal`, and the two
can be had for one and the same ratio: see
`Stacks.Chow.DenominatorStalk.exists_affineOpen_nonempty_denominatorQuotientStalkLinearEquivs`. -/
def denominatorSectionQuotientStalkLinearEquivFractionalProductIdeal
    [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) [F.IsCoherent]
    (hF : AlgebraicGeometry.HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
    {V : Opens X} (hV : IsAffineOpen V) {a b : Γ(X, V)} {e : Γ(L, V)}
    (hbas : ∀ g : Γ(X, V),
      Set.range (ConcreteCategory.hom
          ((AlgebraicGeometry.denominatorIdealMul X L s).val.app (op (X.basicOpen g)))) =
        (fun y : Γ(X, X.basicOpen g) =>
            y • L.presheaf.map (homOfLE (X.basicOpen_le g)).op e) ''
          {y : Γ(X, X.basicOpen g) | ∃ u : Γ(X, X.basicOpen g),
            y * algebraMap Γ(X, V) Γ(X, X.basicOpen g) b =
              algebraMap Γ(X, V) Γ(X, X.basicOpen g) a * u})
    {x : X} (hx : x ∈ V)
    (hm : Stacks.Divisors.IsStalkBasis L x (L.presheaf.germ V x hx e)) :
    (F.presheaf.stalk x ⧸
        (Ideal.fractionalProductIdeal (X.presheaf.germ V x hx a) (X.presheaf.germ V x hx b) •
          (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x))) : Type u)
      ≃ₗ[X.presheaf.stalk x]
        (denominatorSectionQuotientDecl L F s hL hs hF hSupp).presheaf.stalk x :=
  sectionQuotientStalkLinearEquiv
    (AlgebraicGeometry.denominatorIdealTimesModuleMul X L F s hL hs hF hSupp).val
    (AlgebraicGeometry.denominatorIdealTimesModuleMul X L F s hL hs hF hSupp).property hm
    (mem_mulGerms_iff_coord_mem X L s hV hbas hx hm)

/-- **Around every point of a scheme there is an affine open on which the meromorphic section is a
ratio `a / b` such that both denominator quotients of [Stacks, Tag 02SW] have, at that point, the
stalk of `F` modulo the corresponding colon ideal of that ratio:**

  `(Q₁)_x ≅ F_x / (I a b) F_x`,   `(Q₂)_x ≅ F_x / (J a b) F_x`,

with `I = Ideal.denominatorIdeal` and `J = Ideal.fractionalProductIdeal`. The ratio is *the same*
on both sides, which is what part (4) of Tag 02SW needs: the length formula of
[Stacks, Tag 02QH] computes the difference of the colengths of those two ideals of a single
ratio. -/
theorem exists_affineOpen_nonempty_denominatorQuotientStalkLinearEquivs
    [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) [F.IsCoherent]
    (hF : AlgebraicGeometry.HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
    (x : X) :
    ∃ (V : Opens X) (hxV : x ∈ V), IsAffineOpen V ∧ ∃ a b : Γ(X, V),
      a ∈ nonZeroDivisors Γ(X, V) ∧ b ∈ nonZeroDivisors Γ(X, V) ∧
      Nonempty ((F.presheaf.stalk x ⧸
            (Ideal.denominatorIdeal (X.presheaf.germ V x hxV a) (X.presheaf.germ V x hxV b) •
              (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x))) : Type u)
          ≃ₗ[X.presheaf.stalk x]
            (Stacks.Chow.denominatorQuotientDecl L F s).presheaf.stalk x) ∧
        Nonempty ((F.presheaf.stalk x ⧸
            (Ideal.fractionalProductIdeal
                (X.presheaf.germ V x hxV a) (X.presheaf.germ V x hxV b) •
              (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x))) : Type u)
          ≃ₗ[X.presheaf.stalk x]
            (denominatorSectionQuotientDecl L F s hL hs hF hSupp).presheaf.stalk x) := by
  obtain ⟨V, hxV, hVaff, a, b, e, ha, hb, hm, hι, hmul⟩ :=
    Stacks.DenominatorMul.exists_affineOpen_denominator_presentations_of_isRegular X L s hL hs x
  exact ⟨V, hxV, hVaff, a, b, ha, hb,
    ⟨denominatorQuotientStalkLinearEquivDenominatorIdeal X L F s hVaff hι hxV⟩,
    ⟨denominatorSectionQuotientStalkLinearEquivFractionalProductIdeal
      hL hs hF hSupp hVaff hmul hxV hm⟩⟩

/-! ### The two identifications as equalities of lengths

The length formula of [Stacks, Tag 02QH] is stated about `Module.length` of the two quotients of
`F_x`, so a consumer wants the identifications above as equalities of lengths rather than as
isomorphisms. `LinearEquiv.length_eq` turns each into one, and it assumes **nothing**:
`Module.length` is the Krull dimension of the submodule lattice, valued in `ℕ∞`, so the equality
holds whether or not the lengths are finite, and none of the finiteness that Tag 02QH itself
needs enters here. The three statements below therefore carry exactly the hypotheses of the
identifications they transport and no others. -/

/-- **The length of the stalk of the second denominator quotient is the colength of the
fractional product ideal of the germs of a local ratio.** This is
`Stacks.Chow.DenominatorStalk.denominatorSectionQuotientStalkLinearEquivFractionalProductIdeal`
read through `LinearEquiv.length_eq`, which needs no finiteness hypothesis. -/
theorem length_denominatorSectionQuotientStalk
    [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) [F.IsCoherent]
    (hF : AlgebraicGeometry.HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
    {V : Opens X} (hV : IsAffineOpen V) {a b : Γ(X, V)} {e : Γ(L, V)}
    (hbas : ∀ g : Γ(X, V),
      Set.range (ConcreteCategory.hom
          ((AlgebraicGeometry.denominatorIdealMul X L s).val.app (op (X.basicOpen g)))) =
        (fun y : Γ(X, X.basicOpen g) =>
            y • L.presheaf.map (homOfLE (X.basicOpen_le g)).op e) ''
          {y : Γ(X, X.basicOpen g) | ∃ u : Γ(X, X.basicOpen g),
            y * algebraMap Γ(X, V) Γ(X, X.basicOpen g) b =
              algebraMap Γ(X, V) Γ(X, X.basicOpen g) a * u})
    {x : X} (hx : x ∈ V)
    (hm : Stacks.Divisors.IsStalkBasis L x (L.presheaf.germ V x hx e)) :
    Module.length (X.presheaf.stalk x)
        ((denominatorSectionQuotientDecl L F s hL hs hF hSupp).presheaf.stalk x) =
      Module.length (X.presheaf.stalk x)
        (F.presheaf.stalk x ⧸
          (Ideal.fractionalProductIdeal (X.presheaf.germ V x hx a) (X.presheaf.germ V x hx b) •
            (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)))) :=
  (denominatorSectionQuotientStalkLinearEquivFractionalProductIdeal
    hL hs hF hSupp hV hbas hx hm).length_eq.symm

/-- **The length of the stalk of the first denominator quotient is the colength of the denominator
ideal of the germs of a local ratio.** The counterpart of
`Stacks.Chow.DenominatorStalk.length_denominatorSectionQuotientStalk` for the first quotient,
obtained the same way from
`Stacks.Chow.DenominatorStalk.denominatorQuotientStalkLinearEquivDenominatorIdeal`. -/
theorem length_denominatorQuotientStalk {V : Opens X} (hV : IsAffineOpen V) {a b : Γ(X, V)}
    (hbas : ∀ f : Γ(X, V),
      Set.range (ConcreteCategory.hom
          ((Stacks.DenominatorIdeal.denominatorIdealι X L s).val.app (op (X.basicOpen f)))) =
        {g : Γ(X, X.basicOpen f) | ∃ v : Γ(X, X.basicOpen f),
          g * algebraMap Γ(X, V) Γ(X, X.basicOpen f) a =
            algebraMap Γ(X, V) Γ(X, X.basicOpen f) b * v})
    {x : X} (hx : x ∈ V) :
    Module.length (X.presheaf.stalk x)
        ((Stacks.Chow.denominatorQuotientDecl L F s).presheaf.stalk x) =
      Module.length (X.presheaf.stalk x)
        (F.presheaf.stalk x ⧸
          (Ideal.denominatorIdeal (X.presheaf.germ V x hx a) (X.presheaf.germ V x hx b) •
            (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)))) :=
  (denominatorQuotientStalkLinearEquivDenominatorIdeal X L F s hV hbas hx).length_eq.symm

/-- **Around every point of a scheme there is an affine open and a ratio `a / b` for which the
lengths of the stalks of the two denominator quotients of [Stacks, Tag 02SW] are the colengths of
the two colon ideals of that ratio.** This is
`Stacks.Chow.DenominatorStalk.exists_affineOpen_nonempty_denominatorQuotientStalkLinearEquivs`
with both isomorphisms turned into equalities of lengths, which is the form the length formula of
[Stacks, Tag 02QH] consumes: its left-hand side is the difference of the two colengths, for one
and the same `a` and `b`. -/
theorem exists_affineOpen_length_denominatorQuotientStalk_eq
    [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) [F.IsCoherent]
    (hF : AlgebraicGeometry.HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
    (x : X) :
    ∃ (V : Opens X) (hxV : x ∈ V), IsAffineOpen V ∧ ∃ a b : Γ(X, V),
      a ∈ nonZeroDivisors Γ(X, V) ∧ b ∈ nonZeroDivisors Γ(X, V) ∧
      Module.length (X.presheaf.stalk x)
            ((Stacks.Chow.denominatorQuotientDecl L F s).presheaf.stalk x) =
          Module.length (X.presheaf.stalk x)
            (F.presheaf.stalk x ⧸
              (Ideal.denominatorIdeal (X.presheaf.germ V x hxV a) (X.presheaf.germ V x hxV b) •
                (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)))) ∧
        Module.length (X.presheaf.stalk x)
            ((denominatorSectionQuotientDecl L F s hL hs hF hSupp).presheaf.stalk x) =
          Module.length (X.presheaf.stalk x)
            (F.presheaf.stalk x ⧸
              (Ideal.fractionalProductIdeal
                  (X.presheaf.germ V x hxV a) (X.presheaf.germ V x hxV b) •
                (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)))) := by
  obtain ⟨V, hxV, hVaff, a, b, e, ha, hb, hm, hι, hmul⟩ :=
    Stacks.DenominatorMul.exists_affineOpen_denominator_presentations_of_isRegular X L s hL hs x
  exact ⟨V, hxV, hVaff, a, b, ha, hb,
    length_denominatorQuotientStalk hVaff hι hxV,
    length_denominatorSectionQuotientStalk hL hs hF hSupp hVaff hmul hxV hm⟩

end Stacks.Chow.DenominatorStalk

end
