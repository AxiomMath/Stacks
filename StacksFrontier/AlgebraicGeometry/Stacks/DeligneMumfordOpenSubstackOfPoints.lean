module

public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordLocusPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.StabilizerPreservingLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.AlgebraicClosureSite

/-!
# An open substack is Deligne–Mumford when its field-valued points are

Let `𝒳` be an algebraic stack and `𝒰 ⊂ 𝒳` an open substack. Suppose every field-valued point
`x` of `𝒰` has a refinement `y` (a field-valued point with an arrow `y ⟶ x`, so the same point of
`|𝒳|`) whose automorphism group algebraic space `G_y` is unramified over the field of `y`. Then
every object of `𝒰` has unramified automorphism group algebraic space, so `𝒰` is DM
(**Stacks 050D**, part (5)), it lies in the Deligne–Mumford locus of `𝒳` (**Stacks 0DSM**), inside
any largest DM open substack of `𝒳`, and it is a Deligne–Mumford stack (**Stacks 03YO**) by
**Stacks 06N3**.

This is the formal half of the proof of Stacks 0E7A: there `𝒳 = Curves`, `𝒰 = 𝓜̄`, the
refinement of a point `Spec k → 𝓜̄` classifying `X` is the point `Spec k̄ → 𝓜̄` classifying
`X_{k̄}` ("we may first replace `k` by the algebraic closure"), and `G_y` is unramified because
`Der_{k̄}(𝒪_{X_{k̄}}, 𝒪_{X_{k̄}}) = 0` (Stacks 0E6G, 0E69).

## Proof

The objects of `𝒳` whose automorphism group algebraic space is unramified form an open substack
`𝒜` (`AlgebraicGeometry.Stack.automorphismLocusSubstack`, from Stacks 0DSJ). A point of `|𝒰|`
is represented by a field-valued point `x` of `𝒰`; its refinement `y` represents the same point of
`|𝒳|` and lies in `𝒜`, so `|𝒰| ⊆ |𝒜|`. Open substacks are determined by their points
(`AlgebraicGeometry.Stack.OpenSubstack.property_le_of_pointSet_subset`, Stacks 06FJ), so
`𝒰 ⊆ 𝒜`. The automorphism group algebraic spaces of objects of `𝒰` are those computed in `𝒳`,
so `𝒰` is DM by `AlgebraicGeometry.Stack.isAbsolutelyDM_iff_forall_automorphismLocus`.

## Main results

All in the namespace `AlgebraicGeometry.Stack`:

* `OpenSubstack.property_le_automorphismLocus_of_fieldValuedPoint`: `𝒰` lies in the unramified
  automorphism locus.
* `OpenSubstack.isAbsolutelyDM_of_fieldValuedPoint`: `𝒰` is DM.
* `OpenSubstack.property_le_dmLocus_of_fieldValuedPoint`: `𝒰` lies in the Deligne–Mumford locus.
* `OpenSubstack.isDeligneMumfordStack_of_fieldValuedPoint`: `𝒰` is a Deligne–Mumford stack.
* `OpenSubstack.le_and_isAbsolutelyDM_and_isDeligneMumfordStack_of_fieldValuedPoint`: all of it
  at once, relative to a largest DM open substack `𝒲` of `𝒳` (the shape of Stacks 0DSW (1) at
  `𝒳 = Curves`): `𝒰 ⊆ 𝒲`, `𝒰` is DM, and `𝒰` is Deligne–Mumford.
* `FieldValuedPoint.exists_isAlgClosed_hom`: every field-valued point is refined by one over an
  algebraically closed field.
* `OpenSubstack.hasUnramifiedRefinements_of_isAlgClosed`: it suffices to test field-valued points
  over algebraically closed fields.
* `OpenSubstack.le_and_isAbsolutelyDM_and_isDeligneMumfordStack_of_isAlgClosed`: Stacks 0E7A from
  its pointwise input, for `𝓜̄_g ⊆ 𝓜̄ ⊆ Curves^{DM}` (unregistered).

## References

* [Stacks Project, Tag 0E7A](https://stacks.math.columbia.edu/tag/0E7A)
* [Stacks Project, Tag 0DSM](https://stacks.math.columbia.edu/tag/0DSM)
* [Stacks Project, Tag 0DSN](https://stacks.math.columbia.edu/tag/0DSN)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 03YO](https://stacks.math.columbia.edu/tag/03YO)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-! ### Refinement of a field-valued point by an algebraically closed one -/

namespace FieldValuedPoint

/-- **Every field-valued point has a refinement over an algebraically closed field.** The point
`Spec k → 𝒳` is refined by `Spec k̄ → Spec k → 𝒳`, where `k̄` is an algebraic closure of `k`:
its object is the pullback of the object of the point along `Spec k̄ → Spec k`, which lies in the
site because `k̄` is no larger than `max(#k, ℵ₀)`. -/
theorem exists_isAlgClosed_hom (x : FieldValuedPoint B S hS 𝒳.val.val) :
    ∃ y : FieldValuedPoint B S hS 𝒳.val.val, IsAlgClosed y.carrier ∧ Nonempty (y.obj ⟶ x.obj) := by
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.property.isFibered
  let K := AlgebraicClosure x.carrier
  have hK : B.Contains (Spec (.of K)) :=
    BigFppfSite.contains_spec_algebraicClosure B x.carrier
      (contains_spectrum_fieldValuedPoint B S hS x)
  let a : Spec (.of K) ⟶ B.inclusion.obj x.base.left :=
    Spec.map (CommRingCat.ofHom (algebraMap x.carrier K)) ≫ x.isSpec.inv
  let b : B.obj hK ⟶ x.base.left := B.inclusion.preimage a
  let base : BigFppfOver B S hS := Over.mk (b ≫ x.base.hom)
  let e : base ⟶ x.base := Over.homMk b rfl
  refine ⟨{ carrier := K
            base := base
            isSpec := Iso.refl _
            obj := Functor.IsPreFibered.pullbackObj x.over e
            «over» := Functor.IsPreFibered.pullbackObj_proj x.over e },
    inferInstanceAs (IsAlgClosed (AlgebraicClosure x.carrier)),
    ⟨Functor.IsPreFibered.pullbackMap x.over e⟩⟩

end FieldValuedPoint

namespace OpenSubstack

/-- Every field-valued point of `𝒰` has a refinement whose automorphism group algebraic space is
unramified over its field: the hypothesis of this file. -/
def HasUnramifiedRefinements (U : OpenSubstack 𝒳) : Prop :=
  ∀ x : FieldValuedPoint B S hS 𝒳.val.val, U.property x.obj →
    ∃ y : FieldValuedPoint B S hS 𝒳.val.val,
      Nonempty (y.obj ⟶ x.obj) ∧ IsUnramifiedAutomorphismGroupSpace B S hS 𝒳 y

/-- **It suffices to test points over algebraically closed fields.** If every field-valued point
of `𝒰` over an algebraically closed field has unramified automorphism group algebraic space, then
every field-valued point of `𝒰` has such a refinement: the one over an algebraic closure of its
field, which lies in `𝒰` because `𝒰` is closed under arrows into it
(`AlgebraicGeometry.Stack.OpenSubstack.prop_of_hom`). This is "we may first replace
`k` by the algebraic closure" in the proof of Stacks 0E7A. -/
theorem hasUnramifiedRefinements_of_isAlgClosed (U : OpenSubstack 𝒳)
    (hU : ∀ y : FieldValuedPoint B S hS 𝒳.val.val, IsAlgClosed y.carrier → U.property y.obj →
      IsUnramifiedAutomorphismGroupSpace B S hS 𝒳 y) :
    U.HasUnramifiedRefinements B S hS := fun x hx => by
  obtain ⟨y, hy, ⟨a⟩⟩ := FieldValuedPoint.exists_isAlgClosed_hom B S hS x
  exact ⟨y, ⟨a⟩, hU y hy (prop_of_hom B S hS U a hx)⟩

/-- **An open substack lies in the unramified automorphism locus when its field-valued points
do, up to refinement.** -/
theorem property_le_automorphismLocus_of_fieldValuedPoint (U : OpenSubstack 𝒳)
    (hU : U.HasUnramifiedRefinements B S hS) :
    U.property ≤ automorphismLocus B S hS (@_root_.AlgebraicGeometry.Unramified) 𝒳 := by
  let A : OpenSubstack 𝒳 := automorphismLocusSubstack B S hS _ 𝒳 _
    (unramifiedLocus_spec B S hS 𝒳).1 (unramifiedLocus_spec B S hS 𝒳).2
  refine property_le_of_pointSet_subset B S hS (U := U) (V := A) fun p hp => ?_
  obtain ⟨x, hx, rfl⟩ := (mem_pointSet_iff B S hS U p).1 hp
  obtain ⟨y, ⟨f⟩, hy⟩ := hU x hx
  refine (mem_pointSet_iff B S hS A _).2
    ⟨y, (automorphismLocus_obj_iff B S hS 𝒳 _ y).2 hy, ?_⟩
  exact (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val.val 𝒳.val.property y x).2
    ⟨y, ⟨𝟙 _⟩, ⟨f⟩⟩

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **An open substack is DM when its field-valued points have unramified automorphism groups,
up to refinement.** -/
theorem isAbsolutelyDM_of_fieldValuedPoint (U : OpenSubstack 𝒳)
    (hU : U.HasUnramifiedRefinements B S hS) :
    AlgebraicStacks.IsAbsolutelyDM B S hS hZ U.toAlgebraicStack :=
  (isAbsolutelyDM_iff_forall_automorphismLocus B S hS hZ U.toAlgebraicStack).mpr fun y =>
    (automorphismLocus_toAlgebraicStack_iff B S hS _ 𝒳 U y).mpr
      (property_le_automorphismLocus_of_fieldValuedPoint B S hS U hU y.obj y.property)

/-- **Such an open substack lies in the Deligne–Mumford locus** (Stacks 0DSM). -/
theorem property_le_dmLocus_of_fieldValuedPoint (U : OpenSubstack 𝒳)
    (hU : U.HasUnramifiedRefinements B S hS) :
    U.property ≤ dmLocus B S hS hZ 𝒳 :=
  le_dmLocus B S hS hZ 𝒳 U (isAbsolutelyDM_of_fieldValuedPoint B S hS hZ U hU)

/-- **Such an open substack is a Deligne–Mumford stack** (Stacks 03YO), by Stacks 06N3. -/
theorem isDeligneMumfordStack_of_fieldValuedPoint (hZ : B.Contains (⊤_ Scheme.{u}))
    (U : OpenSubstack 𝒳)
    (hU : U.HasUnramifiedRefinements B S hS) :
    IsDeligneMumfordStack.{u, w} B S hS U.toAlgebraicStack.val.val :=
  existsEtalePresentationOfIsAbsolutelyDM B S hS hZ U.toAlgebraicStack
    (isAbsolutelyDM_of_fieldValuedPoint B S hS hZ U hU)

/-- **The formal half of Stacks 0E7A.** Let `𝒲` be a largest DM open substack of `𝒳` (the shape of
Stacks 0DSW (1) at `𝒳 = Curves`, where `𝒲 = Curves^{DM}`), and let `𝒰` be an open substack whose
field-valued points have, up to refinement, unramified automorphism group algebraic spaces.
Then `𝒰 ⊆ 𝒲`, `𝒰` is DM (Stacks 050D) and `𝒰` is a Deligne–Mumford stack (Stacks 03YO). -/
theorem le_and_isAbsolutelyDM_and_isDeligneMumfordStack_of_fieldValuedPoint
    (W : OpenSubstack 𝒳)
    (hW : ∀ V : OpenSubstack 𝒳, AlgebraicStacks.IsAbsolutelyDM B S hS hZ V.toAlgebraicStack →
      V.property ≤ W.property)
    (U : OpenSubstack 𝒳) (hU : U.HasUnramifiedRefinements B S hS) :
    U.property ≤ W.property ∧
      AlgebraicStacks.IsAbsolutelyDM B S hS hZ U.toAlgebraicStack ∧
      IsDeligneMumfordStack.{u, w} B S hS U.toAlgebraicStack.val.val :=
  ⟨hW U (isAbsolutelyDM_of_fieldValuedPoint B S hS hZ U hU),
    isAbsolutelyDM_of_fieldValuedPoint B S hS hZ U hU,
    isDeligneMumfordStack_of_fieldValuedPoint B S hS hZ U hU⟩

/-- Refinements pass to a smaller open substack. -/
theorem HasUnramifiedRefinements.of_le {U V : OpenSubstack 𝒳} (h : V.property ≤ U.property)
    (hU : U.HasUnramifiedRefinements B S hS) : V.HasUnramifiedRefinements B S hS :=
  fun x hx => hU x (h _ hx)

/-- **Stacks 0E7A, from the vanishing of infinitesimal automorphisms at geometric points.** Let
`𝒲` be a largest DM open substack of `𝒳` (Stacks 0DSW (1) at `𝒳 = Curves`: `𝒲 = Curves^{DM}`),
and let `𝒱 ⊆ 𝒰` be open substacks (`𝓜̄_g ⊆ 𝓜̄`). Suppose every field-valued point of `𝒰` over an
algebraically closed field has unramified automorphism group algebraic space (at `𝒰 = 𝓜̄` this is
Stacks 0E76 (2), 0E6G and 0E69). Then `𝒰` and `𝒱` are open substacks of `𝒲`, DM (Stacks 050D)
and Deligne–Mumford stacks (Stacks 03YO).

Unregistered: at `𝒳 = Curves` the inputs are the open substacks `𝓜̄`, `𝓜̄_g` and `Curves^{DM}` of
the algebraic stack of curves (Stacks 0D5A, 0E76, 0E78, 0DSW) and the pointwise hypothesis
(Stacks 0E76 (2), 0E6G, 0E69). -/
theorem le_and_isAbsolutelyDM_and_isDeligneMumfordStack_of_isAlgClosed
    (hZ : B.Contains (⊤_ Scheme.{u})) (W : OpenSubstack 𝒳)
    (hW : ∀ V : OpenSubstack 𝒳, AlgebraicStacks.IsAbsolutelyDM B S hS hZ V.toAlgebraicStack →
      V.property ≤ W.property)
    (U V : OpenSubstack 𝒳) (hVU : V.property ≤ U.property)
    (hU : ∀ y : FieldValuedPoint B S hS 𝒳.val.val, IsAlgClosed y.carrier → U.property y.obj →
      IsUnramifiedAutomorphismGroupSpace B S hS 𝒳 y) :
    (U.property ≤ W.property ∧
      AlgebraicStacks.IsAbsolutelyDM B S hS hZ U.toAlgebraicStack ∧
      IsDeligneMumfordStack.{u, w} B S hS U.toAlgebraicStack.val.val) ∧
    (V.property ≤ W.property ∧
      AlgebraicStacks.IsAbsolutelyDM B S hS hZ V.toAlgebraicStack ∧
      IsDeligneMumfordStack.{u, w} B S hS V.toAlgebraicStack.val.val) :=
  have hR := hasUnramifiedRefinements_of_isAlgClosed B S hS U hU
  ⟨le_and_isAbsolutelyDM_and_isDeligneMumfordStack_of_fieldValuedPoint B S hS hZ W hW U hR,
    le_and_isAbsolutelyDM_and_isDeligneMumfordStack_of_fieldValuedPoint B S hS hZ W hW V
      (hR.of_le B S hS hVU)⟩

end OpenSubstack

end AlgebraicGeometry.Stack

end
