module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraDescentSitePushforward

/-!
# Descent of a sheaf of graded algebras along an identified quotient

Let `O` be a sheaf of rings on a site, let `α₁ : O ⟶ R₁` and `α₂ : O ⟶ R₂` be two locally
surjective morphisms out of it, and let `θ : R₁ ⟶ R₂` satisfy `α₁ ≫ θ = α₂`: two presentations
of one quotient of `O`, identified. A sheaf of graded `O`-algebras annihilated by the kernel
descends along each of them, to a sheaf of graded `R₁`-algebras and to a sheaf of graded
`R₂`-algebras. `SheafOfModules.GradedAlgebra.descend` is taken along a *named* morphism of
sheaves of rings, so an isomorphism of its targets does not by itself move the descended
algebra; this file moves it.

## Main definitions

* `SheafOfModules.GradedAlgebra.scalarRestrict`: restriction of scalars of a sheaf of graded
  algebras along a morphism of sheaves of rings on the same site. Every field is the
  corresponding field of the original: restriction of scalars leaves the underlying presheaves
  untouched, and the two linearity laws of the multiplication are the original ones at the image
  scalar.
* `Stacks.SheafOfModules.ChangeOfRings.liftedSheafRingIso`: **the module-level transport** — the
  restriction of scalars along `θ` of the descent of `G` along `α₂` is its descent along `α₁`.
* `SheafOfModules.GradedAlgebra.descendRingIsoHom` and `descendRingIso`: **the transport**, as a
  unital homomorphism of sheaves of graded `R₁`-algebras which is the identity on local sections,
  and as an isomorphism.

## Main results

* `Stacks.SheafOfModules.ChangeOfRings.liftedSMul_ringIso`: **the computation the transport rests
  on** — the action of `θ(b)` lifted through `α₂` is the action of `b` lifted through `α₁`.
* `Stacks.SheafOfModules.ChangeOfRings.ker_eq_ker_of_ringIso`: when the comparison is an
  isomorphism the two quotient maps have the same kernel, so one annihilation hypothesis serves
  for both descents.
* `SheafOfModules.GradedAlgebra.scalarRestrictHomEquiv`: **restriction of scalars along a locally
  surjective morphism is fully faithful on sheaves of modules**, whence
  `SheafOfModules.GradedAlgebra.UnitalHom.scalarRestrictEquiv`, the resulting bijection on unital
  homomorphisms of sheaves of graded algebras.
* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.of_scalarRestrict`: **the universal property of
  an exterior algebra crosses a change of the ring sheaf**, in the direction which has the
  universal property over the smaller ring and wants it over the larger.
* `SheafOfModules.GradedAlgebra.isExteriorAlgebra_descend_of_ringIso`: **the conclusion** — if
  the descent of `A` along `α₁` is an exterior algebra on a degree-one generator, then so is its
  descent along `α₂`, on the generator read through the transport.

## Why this is wanted

It is the first of the two steps the gluing of [Stacks, Tag 0BQY] still owes, as recorded on
`Stacks.AlgebraicGeometry.RegularIdealSheaf.forall_isIso_extComparison_of_isKoszulSequenceExactOn`.
The local statements of that tag are proved on a restricted ringed space `X.restrict U`, where
the quotient of the structure sheaf is formed as `Stacks.Sites.quotientRingSheaf` of a sheaf of
ideals; the gluing runs over the slice site, where the quotient is instead the pushforward of the
slice quotient. `Stacks.SheafOfModules.openSubspaceRingQuotientIso` identifies those two sheaves
of rings compatibly with their quotient maps, which is exactly the hypothesis `α₁ ≫ θ = α₂`
below; what was missing was the passage from that identification to the two descended algebras,
and to the universal property of an exterior algebra over each.

## Implementation notes

**Nothing here needs `θ` to be an isomorphism except `ker_eq_ker_of_ringIso`.** The module-level
computation `liftedSMul_ringIso` holds for an arbitrary `θ` with `α₁ ≫ θ = α₂`: local
surjectivity of `α₂` is what makes the lifted action on the left-hand side exist, and the two
annihilation hypotheses are supplied separately rather than derived from one another, so that a
consumer holding each quotient's own annihilation statement may use it as it stands.

**Restriction of scalars is fully faithful, and that is the whole content of the crossing.**
`PresheafOfModules.restrictHomEquivOfIsLocallySurjective` is the bijection on morphisms for a
locally surjective morphism of presheaves of rings with sheaf target, and an isomorphism is in
particular locally surjective. A unital homomorphism of sheaves of graded algebras is a
degreewise morphism of sheaves of modules together with two conditions on local sections, and the
bijection is the identity on local sections, so both conditions transport unchanged and so does
the square-zero condition on a generator. The universal property then crosses with no transport
of its own: a test algebra over the larger ring restricts to one over the smaller, and the unique
homomorphism out of the universal algebra is carried back by the bijection.

**No `@[stacks]` attribute.** Nothing here is a clause of Tag 0BQY, whose statement is about the
comparison `⋀ⁱ(Ext¹) ⟶ Extⁱ`; this is one of the two transports its gluing step consumes. The
0BQY caveats in `StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtExteriorLocal`
record the state.

## References

* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u t a

namespace Stacks.SheafOfModules.ChangeOfRings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O R₁ R₂ : Sheaf J RingCat.{t}}
  (α₁ : O ⟶ R₁) [Presheaf.IsLocallySurjective J α₁.hom]
  (α₂ : O ⟶ R₂) [Presheaf.IsLocallySurjective J α₂.hom]
  (θ : R₁ ⟶ R₂) (hθ : α₁ ≫ θ = α₂)

omit [Presheaf.IsLocallySurjective J α₁.hom] [Presheaf.IsLocallySurjective J α₂.hom] in
include hθ in
/-- The two quotient maps agree on sections, after the comparison: the image of a section of `O`
under `α₂` is the image under `θ` of its image under `α₁`. -/
theorem hom_app_comp (V : Cᵒᵖ) (b : O.obj.obj V) :
    (θ.hom.app V).hom ((α₁.hom.app V).hom b) = (α₂.hom.app V).hom b :=
  congrArg (fun ψ : O ⟶ R₂ => (ψ.hom.app V).hom b) hθ

omit [Presheaf.IsLocallySurjective J α₁.hom] [Presheaf.IsLocallySurjective J α₂.hom] in
include hθ in
/-- **The two kernels agree when the comparison is an isomorphism.** A section of `O` killed by
one of two quotient maps identified by an isomorphism of their targets is killed by the other,
so a single annihilation hypothesis serves for both descents. -/
theorem ker_eq_ker_of_ringIso (e : R₁ ≅ R₂) (hθ' : θ = e.hom) (V : Cᵒᵖ) :
    RingHom.ker (α₂.hom.app V).hom = RingHom.ker (α₁.hom.app V).hom := by
  subst hθ'
  refine le_antisymm (fun b hb => ?_) (fun b hb => ?_)
  · rw [RingHom.mem_ker] at hb ⊢
    have hcancel : (e.inv.hom.app V).hom ((e.hom.hom.app V).hom ((α₁.hom.app V).hom b)) =
        (α₁.hom.app V).hom b :=
      ConcreteCategory.congr_hom
        (congrArg (fun ψ : R₁ ⟶ R₁ => ψ.hom.app V) e.hom_inv_id) ((α₁.hom.app V).hom b)
    refine hcancel.symm.trans ?_
    rw [hom_app_comp α₁ α₂ e.hom hθ V b, hb]
    exact map_zero _
  · rw [RingHom.mem_ker] at hb ⊢
    rw [← hom_app_comp α₁ α₂ e.hom hθ V b, hb]
    exact map_zero _

section Module

variable (G : _root_.SheafOfModules.{a} O)
  (hG₁ : ∀ (V : Cᵒᵖ) (b : O.obj.obj V), b ∈ RingHom.ker (α₁.hom.app V).hom →
    ∀ m : G.val.obj V, b • m = 0)
  (hG₂ : ∀ (V : Cᵒᵖ) (b : O.obj.obj V), b ∈ RingHom.ker (α₂.hom.app V).hom →
    ∀ m : G.val.obj V, b • m = 0)

include hθ in
/-- **The computation the transport rests on.** The action on a section of `G` of the image under
`θ` of a section `b` of `R₁`, lifted through `α₂`, is the action of `b` itself lifted through
`α₁`.

Both sides are amalgamations of local products. Over a member of the image sieve of `b` under
`α₁` carrying a lift `c`, the identity `α₁ ≫ θ = α₂` makes `c` a lift of `θ(b)` as well, and
both sides restrict there to the action of `c`; `G` is a sheaf, hence separated. -/
theorem liftedSMul_ringIso (V : Cᵒᵖ) (b : R₁.obj.obj V) (m : G.val.obj V) :
    liftedSMul α₂ G hG₂ ((θ.hom.app V).hom b) m = liftedSMul α₁ G hG₁ b m := by
  refine sections_ext G (Presheaf.imageSieve_mem J α₁.hom b) (fun W g hg => ?_)
  obtain ⟨c, hc⟩ := hg
  have hc₂ : (α₂.hom.app (op W)).hom c = (R₂.obj.map g.op).hom ((θ.hom.app V).hom b) := by
    rw [← hom_app_comp α₁ α₂ θ hθ (op W) c, hc]
    exact ConcreteCategory.congr_hom (θ.hom.naturality g.op) b
  rw [map_liftedSMul α₂ G hG₂ _ m g c hc₂, map_liftedSMul α₁ G hG₁ b m g c hc]

/-- The identity of the common underlying presheaf of abelian groups, read as a morphism from the
restriction of scalars along `θ` of the descent along `α₂` to the descent along `α₁`. -/
def ringIsoLiftedPresheafId :
    ((PresheafOfModules.restrictScalars.{a} θ.hom).obj
        (liftedSheaf α₂ G hG₂).val).presheaf ⟶ (liftedSheaf α₁ G hG₁).val.presheaf :=
  𝟙 _

include hθ in
/-- **The module-level transport.** The restriction of scalars along `θ` of the descent of `G`
along `α₂` is the descent of `G` along `α₁`: the same presheaf of abelian groups, with the same
`R₁`-action. -/
def liftedSheafRingIso :
    (_root_.SheafOfModules.restrictScalars.{a} θ).obj (liftedSheaf α₂ G hG₂) ≅
      liftedSheaf α₁ G hG₁ where
  hom := ⟨PresheafOfModules.homMk (ringIsoLiftedPresheafId α₁ α₂ θ G hG₁ hG₂)
    (fun V b m => liftedSMul_ringIso α₁ α₂ θ hθ G hG₁ hG₂ V b m)⟩
  inv := ⟨PresheafOfModules.homMk
    (M₂ := ((_root_.SheafOfModules.restrictScalars.{a} θ).obj (liftedSheaf α₂ G hG₂)).val)
    (ringIsoLiftedPresheafId α₁ α₂ θ G hG₁ hG₂)
    (fun V b m => (liftedSMul_ringIso α₁ α₂ θ hθ G hG₁ hG₂ V b m).symm)⟩
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

include hθ in
/-- The forward map of `liftedSheafRingIso` is the identity on local sections. -/
@[simp]
theorem liftedSheafRingIso_hom_val_app (V : Cᵒᵖ)
    (m : ((_root_.SheafOfModules.restrictScalars.{a} θ).obj (liftedSheaf α₂ G hG₂)).val.obj V) :
    (liftedSheafRingIso α₁ α₂ θ hθ G hG₁ hG₂).hom.val.app V m = m :=
  rfl

end Module

end Stacks.SheafOfModules.ChangeOfRings

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R S : Sheaf J RingCat.{t}}

/-- **Restriction of scalars of a sheaf of graded algebras along a morphism of sheaves of rings
on the same site.** The homogeneous pieces are the restrictions of scalars of those of `A`, whose
sections are literally the sections of `A`, and the multiplication and the unit are those of `A`:
restriction of scalars changes only the action of the scalars, and the two linearity laws of the
multiplication are the original ones at the image scalar. -/
def scalarRestrict (θ : S ⟶ R) (A : GradedAlgebra.{t, a} R) : GradedAlgebra.{t, a} S where
  piece n := (_root_.SheafOfModules.restrictScalars.{a} θ).obj (A.piece n)
  mul i j :=
    { app V := (A.mul i j).app V
      map_smul_left V r x y := (A.mul i j).map_smul_left V ((θ.hom.app V).hom r) x y
      map_smul_right V r x y := (A.mul i j).map_smul_right V ((θ.hom.app V).hom r) x y
      naturality f x y := (A.mul i j).naturality f x y }
  one := A.one
  mul_assoc i j k V x y z := A.mul_assoc i j k V x y z
  one_mul i V x := A.one_mul i V x
  mul_one i V x := A.mul_one i V x

/-- The homogeneous piece of degree `n` of the restriction of scalars is the restriction of
scalars of the piece of degree `n` of the original. -/
@[simp]
theorem scalarRestrict_piece (θ : S ⟶ R) (A : GradedAlgebra.{t, a} R) (n : ℤ) :
    (scalarRestrict θ A).piece n =
      (_root_.SheafOfModules.restrictScalars.{a} θ).obj (A.piece n) :=
  rfl

/-- The multiplication of the restriction of scalars is that of the original, on local
sections. -/
theorem scalarRestrict_mul_app (θ : S ⟶ R) (A : GradedAlgebra.{t, a} R) (i j : ℤ) (V : Cᵒᵖ)
    (x : (A.piece i).val.obj V) (y : (A.piece j).val.obj V) :
    ((scalarRestrict θ A).mul i j).app V x y = (A.mul i j).app V x y :=
  rfl

/-- The unit of the restriction of scalars is that of the original, on sections. -/
theorem scalarRestrict_one_eval (θ : S ⟶ R) (A : GradedAlgebra.{t, a} R) (V : Cᵒᵖ) :
    (scalarRestrict θ A).one.eval V = A.one.eval V :=
  rfl

section Hom

variable {A B : GradedAlgebra.{t, a} R}

/-- **The restriction of scalars of a unital homomorphism of sheaves of graded algebras.** Each
component is the restriction of scalars of the corresponding component, and the two
compatibilities are the original ones, the restricted algebra having the same multiplication and
the same unit on sections. -/
def UnitalHom.scalarRestrict (θ : S ⟶ R) (g : UnitalHom A B) :
    UnitalHom (GradedAlgebra.scalarRestrict θ A) (GradedAlgebra.scalarRestrict θ B) where
  app n := (_root_.SheafOfModules.restrictScalars.{a} θ).map (g.app n)
  map_mul i j V x y := g.map_mul i j V x y
  map_one V := g.map_one V

/-- The degree-`n` component of the restriction of scalars of `g` is the restriction of scalars
of the degree-`n` component of `g`. -/
@[simp]
theorem UnitalHom.scalarRestrict_app (θ : S ⟶ R) (g : UnitalHom A B) (n : ℤ) :
    (g.scalarRestrict θ).app n = (_root_.SheafOfModules.restrictScalars.{a} θ).map (g.app n) :=
  rfl

/-- **The restriction of scalars of a degree-one generator.** -/
abbrev genScalarRestrict (θ : S ⟶ R) {M : _root_.SheafOfModules.{a} R} (ι : M ⟶ A.piece 1) :
    (_root_.SheafOfModules.restrictScalars.{a} θ).obj M ⟶
      (GradedAlgebra.scalarRestrict θ A).piece 1 :=
  (_root_.SheafOfModules.restrictScalars.{a} θ).map ι

/-- **A square-zero degree-one generator restricts to a square-zero degree-one generator**, and
conversely: the condition is one on local sections, which restriction of scalars leaves
unchanged. -/
theorem squareZero_scalarRestrict_iff (θ : S ⟶ R) {M : _root_.SheafOfModules.{a} R}
    (ι : M ⟶ A.piece 1) :
    SquareZero (A := GradedAlgebra.scalarRestrict θ A) (genScalarRestrict θ ι) ↔
      SquareZero ι :=
  Iff.rfl

end Hom

section FullyFaithful

variable (θ : S ⟶ R) [Presheaf.IsLocallySurjective J θ.hom]

/-- **Restriction of scalars along a locally surjective morphism of sheaves of rings is fully
faithful.** This is `PresheafOfModules.restrictHomEquivOfIsLocallySurjective` read on sheaves of
modules, where the sheaf hypothesis on the target is automatic. -/
def scalarRestrictHomEquiv (M N : _root_.SheafOfModules.{a} R) :
    (M ⟶ N) ≃ ((_root_.SheafOfModules.restrictScalars.{a} θ).obj M ⟶
      (_root_.SheafOfModules.restrictScalars.{a} θ).obj N) where
  toFun f := (_root_.SheafOfModules.restrictScalars.{a} θ).map f
  invFun g :=
    ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective (α := θ.hom)
      N.isSheaf).symm g.val⟩
  left_inv f := _root_.SheafOfModules.hom_ext
    ((PresheafOfModules.restrictHomEquivOfIsLocallySurjective (α := θ.hom)
      N.isSheaf).symm_apply_apply f.val)
  right_inv g := _root_.SheafOfModules.hom_ext
    ((PresheafOfModules.restrictHomEquivOfIsLocallySurjective (α := θ.hom)
      N.isSheaf).apply_symm_apply g.val)

section Lift

variable {A B : GradedAlgebra.{t, a} R}

/-- **A unital homomorphism of the restrictions of scalars comes from a unital homomorphism.**
Each component is lifted by `scalarRestrictHomEquiv`, which is the identity on local sections, so
multiplicativity and unitality are the given ones unchanged. -/
def UnitalHom.scalarRestrictLift
    (g : UnitalHom (GradedAlgebra.scalarRestrict θ A) (GradedAlgebra.scalarRestrict θ B)) :
    UnitalHom A B where
  app n := (scalarRestrictHomEquiv θ (A.piece n) (B.piece n)).symm (g.app n)
  map_mul i j V x y := g.map_mul i j V x y
  map_one V := g.map_one V

/-- **The bijection on unital homomorphisms of sheaves of graded algebras.** -/
def UnitalHom.scalarRestrictEquiv :
    UnitalHom A B ≃
      UnitalHom (GradedAlgebra.scalarRestrict θ A) (GradedAlgebra.scalarRestrict θ B) where
  toFun g := g.scalarRestrict θ
  invFun g := g.scalarRestrictLift θ
  left_inv g := UnitalHom.ext fun n =>
    (scalarRestrictHomEquiv θ (A.piece n) (B.piece n)).symm_apply_apply (g.app n)
  right_inv g := UnitalHom.ext fun n =>
    (scalarRestrictHomEquiv θ (A.piece n) (B.piece n)).apply_symm_apply (g.app n)

/-- **Extending a generator is detected after restriction of scalars.** A unital homomorphism
carries `ι` to `κ` exactly when its restriction of scalars carries the restricted `ι` to the
restricted `κ`, restriction of scalars being faithful. -/
theorem genScalarRestrict_comp_app_iff {M : _root_.SheafOfModules.{a} R} (ι : M ⟶ A.piece 1)
    (κ : M ⟶ B.piece 1) (f : UnitalHom A B) :
    genScalarRestrict θ ι ≫ (f.scalarRestrict θ).app 1 = genScalarRestrict θ κ ↔
      ι ≫ f.app 1 = κ := by
  rw [← (scalarRestrictHomEquiv θ M (B.piece 1)).injective.eq_iff]
  exact (Eq.congr_left ((_root_.SheafOfModules.restrictScalars.{a} θ).map_comp ι (f.app 1))).symm

/-- **The universal property of an exterior algebra crosses a change of the ring sheaf.** If the
restriction of scalars of `A` along a locally surjective `θ : S ⟶ R` is the exterior algebra of
the restriction of scalars of `M` on the restricted generator, then `A` is the exterior algebra
of `M` on `ι`.

Nothing is transported. A test algebra `B` over `R` with a square-zero degree-one generator `κ`
restricts to one over `S` with the restricted generator, which is again square zero
(`squareZero_scalarRestrict_iff`); the universal property over `S` produces a unique unital
homomorphism of the restrictions extending the restricted generator; and
`SheafOfModules.GradedAlgebra.UnitalHom.scalarRestrictEquiv` carries that bijectively back,
compatibly with extending the generator by `genScalarRestrict_comp_app_iff`. -/
theorem IsExteriorAlgebra.of_scalarRestrict {M : _root_.SheafOfModules.{a} R}
    {ι : M ⟶ A.piece 1}
    (h : IsExteriorAlgebra (GradedAlgebra.scalarRestrict θ A) (genScalarRestrict θ ι)) :
    IsExteriorAlgebra A ι := by
  refine ⟨(squareZero_scalarRestrict_iff θ ι).1 h.1, fun B κ hκ => ?_⟩
  obtain ⟨g, hg, hg'⟩ := h.2 (GradedAlgebra.scalarRestrict θ B) (genScalarRestrict θ κ)
    ((squareZero_scalarRestrict_iff θ κ).2 hκ)
  refine ⟨(UnitalHom.scalarRestrictEquiv θ).symm g, ?_, fun f hf => ?_⟩
  · refine (genScalarRestrict_comp_app_iff θ ι κ _).1 ?_
    rw [show ((UnitalHom.scalarRestrictEquiv θ).symm g).scalarRestrict θ = g from
      (UnitalHom.scalarRestrictEquiv θ).apply_symm_apply g]
    exact hg
  · refine (UnitalHom.scalarRestrictEquiv θ).injective ?_
    rw [(UnitalHom.scalarRestrictEquiv θ).apply_symm_apply]
    exact hg' _ ((genScalarRestrict_comp_app_iff θ ι κ f).2 hf)

end Lift

end FullyFaithful

section Descend

open Stacks.SheafOfModules.ChangeOfRings

variable {O R₁ R₂ : Sheaf J RingCat.{t}}
  (α₁ : O ⟶ R₁) [Presheaf.IsLocallySurjective J α₁.hom]
  (α₂ : O ⟶ R₂) [Presheaf.IsLocallySurjective J α₂.hom]
  (θ : R₁ ⟶ R₂) (hθ : α₁ ≫ θ = α₂)
  (A : GradedAlgebra.{t, t} O)
  (hA₁ : ∀ (n : ℤ) (V : Cᵒᵖ) (b : O.obj.obj V), b ∈ RingHom.ker (α₁.hom.app V).hom →
    ∀ m : (A.piece n).val.obj V, b • m = 0)
  (hA₂ : ∀ (n : ℤ) (V : Cᵒᵖ) (b : O.obj.obj V), b ∈ RingHom.ker (α₂.hom.app V).hom →
    ∀ m : (A.piece n).val.obj V, b • m = 0)

include hθ in
/-- **The transport.** The restriction of scalars along `θ` of the descent of `A` along `α₂` is
the descent of `A` along `α₁`, identified by a unital homomorphism which is the identity on
local sections.

The two algebras have the same pieces by
`Stacks.SheafOfModules.ChangeOfRings.liftedSheafRingIso`, and the multiplication and the unit of
each are those of `A`, so the two laws are `rfl`. -/
def descendRingIsoHom :
    UnitalHom (scalarRestrict θ (descend α₂ A hA₂)) (descend α₁ A hA₁) where
  app n := (liftedSheafRingIso α₁ α₂ θ hθ (A.piece n) (hA₁ n) (hA₂ n)).hom
  map_mul _ _ _ _ _ := rfl
  map_one _ := rfl

include hθ in
/-- The transport is the identity on local sections. -/
theorem descendRingIsoHom_app_val_app (n : ℤ) (V : Cᵒᵖ)
    (x : ((scalarRestrict θ (descend α₂ A hA₂)).piece n).val.obj V) :
    ((descendRingIsoHom α₁ α₂ θ hθ A hA₁ hA₂).app n).val.app V x = x :=
  rfl

include hθ in
/-- **Every degree of the transport is an isomorphism.** -/
instance isIso_descendRingIsoHom_app (n : ℤ) :
    IsIso ((descendRingIsoHom α₁ α₂ θ hθ A hA₁ hA₂).app n) :=
  (liftedSheafRingIso α₁ α₂ θ hθ (A.piece n) (hA₁ n) (hA₂ n)).isIso_hom

include hθ in
/-- **The transport, as an isomorphism of sheaves of graded `R₁`-algebras.** -/
def descendRingIso :
    scalarRestrict θ (descend α₂ A hA₂) ≅ descend α₁ A hA₁ where
  hom := (descendRingIsoHom α₁ α₂ θ hθ A hA₁ hA₂).toHom
  inv := (descendRingIsoHom α₁ α₂ θ hθ A hA₁ hA₂).inverse.toHom
  hom_inv_id := by
    refine Hom.ext fun n => ?_
    simpa using IsIso.hom_inv_id ((descendRingIsoHom α₁ α₂ θ hθ A hA₁ hA₂).app n)
  inv_hom_id := by
    refine Hom.ext fun n => ?_
    simpa using IsIso.inv_hom_id ((descendRingIsoHom α₁ α₂ θ hθ A hA₁ hA₂).app n)

include hθ in
/-- **The conclusion: the universal property of an exterior algebra crosses an identification of
the quotient along which the algebra is descended.** Let `ι : M ⟶ (descend α₂ A hA₂).piece 1` be
a degree-one generator of the descent of `A` along `α₂`, over the ring sheaf `R₂`. If the
restriction of scalars of `ι` along `θ`, read through the transport, makes the descent of `A`
along `α₁` the exterior algebra of the restriction of scalars of `M`, then the descent of `A`
along `α₂` is the exterior algebra of `M` on `ι` itself.

Two steps. The degreewise isomorphism `descendRingIsoHom` carries the universal property from
the descent along `α₁` to the restriction of scalars along `θ` of the descent along `α₂`
(`SheafOfModules.GradedAlgebra.IsUniversal.ofDegreewiseIso`), and
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.of_scalarRestrict` lifts it off that restriction
of scalars, which is where the full faithfulness of restriction of scalars is used. -/
theorem isExteriorAlgebra_descend_of_ringIso [Presheaf.IsLocallySurjective J θ.hom]
    {M : _root_.SheafOfModules.{t} R₂} {ι : M ⟶ (descend α₂ A hA₂).piece 1}
    (h : IsExteriorAlgebra (descend α₁ A hA₁)
      (genScalarRestrict θ ι ≫ (descendRingIsoHom α₁ α₂ θ hθ A hA₁ hA₂).app 1)) :
    IsExteriorAlgebra (descend α₂ A hA₂) ι := by
  have : ∀ n, IsIso ((descendRingIsoHom α₁ α₂ θ hθ A hA₁ hA₂).inverse.app n) :=
    fun n => inferInstanceAs
      (IsIso (inv ((descendRingIsoHom α₁ α₂ θ hθ A hA₁ hA₂).app n)))
  refine IsExteriorAlgebra.of_scalarRestrict θ ?_
  have key := h.isUniversal.ofDegreewiseIso
    (descendRingIsoHom α₁ α₂ θ hθ A hA₁ hA₂).inverse
    (h.1.compUnitalHom (descendRingIsoHom α₁ α₂ θ hθ A hA₁ hA₂).inverse)
  rwa [Category.assoc, UnitalHom.inverse_app, IsIso.hom_inv_id, Category.comp_id] at key

end Descend

end SheafOfModules.GradedAlgebra

end
