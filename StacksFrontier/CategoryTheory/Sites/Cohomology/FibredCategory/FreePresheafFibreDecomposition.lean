module

public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.DerivedColimits

/-!
# The free abelian presheaf on an object, restricted to a fibre

Let `p : 𝒳 ⥤ 𝒮` be a functor with a choice of pullbacks and let `U'` be an object of `𝒳`, lying
over `V' = p(U')`. Fix an object `V` of `𝒮`. Every morphism `a : x ⟶ U'` out of an object `x` of
the fibre `𝒳_V` factors uniquely as `x ⟶ h^* U' ⟶ U'`, where `h : V ⟶ V'` is the morphism of the
base that `a` lies over, `h^* U' ⟶ U'` is the chosen strongly cartesian lift of `h` at `U'`, and
the first factor is a morphism of the fibre `𝒳_V`. Consequently the set of morphisms `x ⟶ U'` is
the disjoint union, over `h : V ⟶ V'`, of the sets of morphisms `x ⟶ h^* U'` of the fibre.

Applying this index-wise to free abelian groups decomposes the free abelian presheaf on `U'`,
restricted to the fibre at `V`, as a direct sum over `h : V ⟶ V'` of the free abelian presheaves
on the chosen pullbacks `h^* U'`:

```
F_{U'}|_{𝒳_V} ≅ ⨁_{h : V ⟶ V'} F_{h^* U'}
```

Since each summand has acyclic simplicial replacement, the homology of the fibre at `V` with
coefficients in the restricted free abelian presheaf vanishes in every positive degree.

## Main definitions

* `CategoryTheory.Functor.Fiber.baseHom`: the morphism of the base underlying a morphism between
  objects of two fibres.
* `CategoryTheory.Functor.ChoiceOfPullbacks.pullbackObj` and `pullbackHom`: the chosen pullback
  `h^* U'` of an object of the total category along a morphism of the base, and its chosen
  strongly cartesian lift `h^* U' ⟶ U'`.
* `CategoryTheory.Functor.ChoiceOfPullbacks.fiberFactor`: the first factor of the unique
  factorisation of `a : x ⟶ U'` through the chosen cartesian lift.
* `CategoryTheory.Functor.ChoiceOfPullbacks.homEquivSigma`: that unique factorisation, as a
  bijection.
* `Stacks.Sites.FibredCategory.freeFiberSummandIncl` and
  `Stacks.Sites.FibredCategory.freeFiberDirectSumDesc`: the summands of the decomposition and the
  morphism out of their direct sum.
* `Stacks.Sites.FibredCategory.freePresheafFiberDecomposition`: the decomposition itself.

## Main results

* `Stacks.CategoryHomology.categoryHomology_isZero_of_iso` and
  `Stacks.CategoryHomology.categoryHomology_isZero_of_replacementComplex_homology_isZero`:
  vanishing of `H_n(C, F)` only depends on `F` up to isomorphism, and follows from vanishing of
  the homology of the simplicial replacement complex.
* `Stacks.Sites.FibredCategory.directSumPresheafIncl_comp_freePresheafFiberDecomposition_inv`:
  the decomposition is compatible with the summand inclusions.
* `Stacks.Sites.FibredCategory.categoryHomology_fiberRestriction_isZero`: the homology of the
  fibre at `V` with coefficients in the restriction of the universe-lifted free abelian presheaf
  on `U'` vanishes in every positive degree.

## Implementation notes

Everything is stated for a bare functor `p : 𝒳 ⥤ 𝒮` together with a choice of pullbacks
(`CategoryTheory.Functor.ChoiceOfPullbacks`), rather than for the bundled
`Stacks.Sites.FibredCategory.FibredCategorySituation`: the ringed structure of the base plays no
part, and a choice of pullbacks is weaker than fibredness together with the canonical choice
(`CategoryTheory.Functor.chosenPullbacks`), which is the instance the bundled situation uses. The
final vanishing statement mentions no choice of pullbacks at all and is therefore stated for a
fibred `p`.

**The dependent factorisation.** The target of the first factor of `a : x ⟶ U'` depends on the
base morphism `a` lies over, so the factorisation is packaged as an element of a sigma type and
its uniqueness as an equality there
(`CategoryTheory.Functor.ChoiceOfPullbacks.sigma_baseHom_fiberFactor_eq`). Stating the uniqueness
with the base morphism and the first factor as independent variables is what allows the base
morphism to be substituted away; with the composite substituted first, the substitution would be
circular.

**Universes.** The index set of the decomposition is a set of morphisms of the base, so it lives
in the morphism universe `v₁` of `𝒮`, while `Stacks.CategoryHomology.directSumPresheaf` requires
the index set and the coefficient groups to live in one and the same universe. The coefficients
are therefore taken in `AddCommGrpCat.{max u₂ v₁ v}` — written
`uliftFreeRepresentablePresheaf.{u₂, max v₁ v}`, which is the generality in which
`Stacks.Sites.FibredCategory.fiberHomologyPresheaf` is formed — and the index set is the morphism
set lifted there.

**Decidable equality on the index.** `DirectSum.of` carries a `DecidableEq` instance on the index
set, and the definitions below and their computation rules must use the *same* term. It is taken
as a hypothesis rather than produced by `Classical.decEq` inside each declaration, so that the
instances agree by construction; the final vanishing statement does not mention it and supplies
it with `classical`.

## References

* [Stacks Project, Tag 08PJ](https://stacks.math.columbia.edu/tag/08PJ)
* [Stacks Project, Tag 02XN](https://stacks.math.columbia.edu/tag/02XN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

-- `Fiber` and `Fiber.fiberInclusion` are plain `def`s, so goals mentioning an object of a fibre or
-- its image in `𝒳` are not type-correct at `implicit` transparency and `rw`/`simp` refuse them.
attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {p : 𝒳 ⥤ 𝒮}

/-- The morphism of the base underlying a morphism `a : x ⟶ x'` between objects of the fibres of
`p` over `V` and over `W`: the image `p(a)`, read through the structure equalities of the two
fibres. -/
def Fiber.baseHom {V W : 𝒮} (x : p.Fiber V) (x' : p.Fiber W) (a : x.1 ⟶ x'.1) : V ⟶ W :=
  eqToHom x.2.symm ≫ p.map a ≫ eqToHom x'.2

/-- A morphism between objects of fibres lies over the morphism of the base it induces. -/
instance Fiber.isHomLift_baseHom {V W : 𝒮} (x : p.Fiber V) (x' : p.Fiber W) (a : x.1 ⟶ x'.1) :
    p.IsHomLift (Fiber.baseHom x x' a) a :=
  inferInstanceAs (p.IsHomLift (eqToHom x.2.symm ≫ p.map a ≫ eqToHom x'.2) a)

/-- The morphism of the base underlying a morphism that lies over a given morphism is that
morphism. -/
lemma Fiber.baseHom_eq_of_isHomLift {V W : 𝒮} (x : p.Fiber V) (x' : p.Fiber W) {a : x.1 ⟶ x'.1}
    (h : V ⟶ W) [p.IsHomLift h a] : Fiber.baseHom x x' a = h :=
  (IsHomLift.fac p h a).symm

namespace ChoiceOfPullbacks

variable (c : p.ChoiceOfPullbacks)

/-- The chosen pullback `h^* U'` of an object `U'` of the total category along a morphism
`h : V ⟶ p(U')` of the base, as an object of the fibre at `V`. -/
abbrev pullbackObj (U' : 𝒳) {V : 𝒮} (h : V ⟶ p.obj U') : p.Fiber V :=
  c.obj h (Fiber.mk rfl)

/-- The chosen strongly cartesian lift `h^* U' ⟶ U'` of a morphism `h : V ⟶ p(U')` of the base. -/
abbrev pullbackHom (U' : 𝒳) {V : 𝒮} (h : V ⟶ p.obj U') : (c.pullbackObj U' h).1 ⟶ U' :=
  c.map h (Fiber.mk rfl)

/-- The first factor of the unique factorisation of `a : x ⟶ x'` through the chosen cartesian
lift of the base morphism that `a` lies over: a morphism of the fibre at `V`. -/
def fiberFactor {V W : 𝒮} (x : p.Fiber V) (x' : p.Fiber W) (a : x.1 ⟶ x'.1) :
    x ⟶ c.obj (Fiber.baseHom x x' a) x' :=
  ⟨IsStronglyCartesian.map p (Fiber.baseHom x x' a) (c.map (Fiber.baseHom x x' a) x')
    (Category.id_comp _).symm a, inferInstance⟩

/-- The factorisation defining `CategoryTheory.Functor.ChoiceOfPullbacks.fiberFactor`. -/
@[reassoc (attr := simp)]
lemma fiberFactor_fac {V W : 𝒮} (x : p.Fiber V) (x' : p.Fiber W) (a : x.1 ⟶ x'.1) :
    Fiber.fiberInclusion.map (c.fiberFactor x x' a) ≫ c.map (Fiber.baseHom x x' a) x' = a :=
  IsStronglyCartesian.fac p (Fiber.baseHom x x' a) (c.map (Fiber.baseHom x x' a) x')
    (Category.id_comp _).symm a

/-- A morphism of the fibre at `V` followed by the chosen cartesian lift of `h : V ⟶ W` lies over
`h`. -/
instance isHomLift_comp_map {V W : 𝒮} {x : p.Fiber V} {x' : p.Fiber W} (h : V ⟶ W)
    (β : x ⟶ c.obj h x') :
    p.IsHomLift h (Fiber.fiberInclusion.map β ≫ c.map h x') :=
  have : p.IsHomLift (𝟙 V) (Fiber.fiberInclusion.map β) := β.2
  have : p.IsStronglyCartesian h (c.map h x') := c.isStronglyCartesian h x'
  inferInstance

/-- **The unique factorisation through the chosen cartesian lift.** A morphism of the fibre at `V`
into the chosen pullback `h^* x'`, followed by the chosen cartesian lift `h^* x' ⟶ x'`, is the
factorisation of its own composite: the composite lies over `h`, and the universal property of the
cartesian lift determines the first factor. -/
lemma sigma_baseHom_fiberFactor_eq {V W : 𝒮} {x : p.Fiber V} {x' : p.Fiber W} (a : x.1 ⟶ x'.1)
    {h : V ⟶ W} (β : x ⟶ c.obj h x')
    (hβ : Fiber.fiberInclusion.map β ≫ c.map h x' = a) :
    (⟨Fiber.baseHom x x' a, c.fiberFactor x x' a⟩ :
      (k : V ⟶ W) × (x ⟶ c.obj k x')) = ⟨h, β⟩ := by
  have hb : Fiber.baseHom x x' a = h := by
    rw [← hβ]
    exact Fiber.baseHom_eq_of_isHomLift x x' h
  subst hb
  have huniq : Fiber.fiberInclusion.map β =
      Fiber.fiberInclusion.map (c.fiberFactor x x' a) :=
    IsStronglyCartesian.map_uniq p (Fiber.baseHom x x' a)
      (c.map (Fiber.baseHom x x' a) x') (Category.id_comp _).symm a
      (Fiber.fiberInclusion.map β) hβ
  exact congrArg
    (fun y : x ⟶ c.obj (Fiber.baseHom x x' a) x' =>
      (⟨Fiber.baseHom x x' a, y⟩ : (k : V ⟶ W) × (x ⟶ c.obj k x')))
    (Fiber.hom_ext huniq.symm)

/-- **The unique factorisation through the chosen cartesian lifts, as a bijection.** Morphisms
`x ⟶ x'` from an object of the fibre at `V` to an object of the fibre at `W` are in bijection with
pairs of a morphism `h : V ⟶ W` of the base and a morphism `x ⟶ h^* x'` of the fibre at `V`. -/
def homEquivSigma {V W : 𝒮} (x : p.Fiber V) (x' : p.Fiber W) :
    (x.1 ⟶ x'.1) ≃ ((h : V ⟶ W) × (x ⟶ c.obj h x')) where
  toFun a := ⟨Fiber.baseHom x x' a, c.fiberFactor x x' a⟩
  invFun t := Fiber.fiberInclusion.map t.2 ≫ c.map t.1 x'
  left_inv a := c.fiberFactor_fac x x' a
  right_inv t := c.sigma_baseHom_fiberFactor_eq _ t.2 rfl

/-- The bijection of `CategoryTheory.Functor.ChoiceOfPullbacks.homEquivSigma` is natural in the
source: precomposing with a morphism of the fibre at `V` leaves the base morphism unchanged and
precomposes the first factor. -/
lemma homEquivSigma_naturality {V W : 𝒮} {y x : p.Fiber V} (f : y ⟶ x) (x' : p.Fiber W)
    (a : x.1 ⟶ x'.1) :
    c.homEquivSigma y x' (Fiber.fiberInclusion.map f ≫ a) =
      ⟨(c.homEquivSigma x x' a).1, f ≫ (c.homEquivSigma x x' a).2⟩ :=
  c.sigma_baseHom_fiberFactor_eq _ (f ≫ c.fiberFactor x x' a) (by
    rw [Functor.map_comp, Category.assoc, fiberFactor_fac])

end ChoiceOfPullbacks

end CategoryTheory.Functor

namespace Stacks.CategoryHomology

universe u v

/-- Vanishing of the homology of a small category in a fixed degree depends on the coefficient
presheaf only through its isomorphism class. -/
theorem categoryHomology_isZero_of_iso {C : Type u} [SmallCategory C]
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} (e : F ≅ G) (n : ℕ)
    (h : IsZero (categoryHomology.{u, v} G n)) : IsZero (categoryHomology.{u, v} F n) :=
  h.of_iso
    (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _).leftDerived n).mapIso e)

/-- **Stacks 08PG.** The homology `H_n(C, F)` vanishes as soon as the homology of the simplicial
replacement complex of `F` does. -/
theorem categoryHomology_isZero_of_replacementComplex_homology_isZero {C : Type u}
    [SmallCategory C] (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ)
    (h : IsZero ((simplicialReplacementComplex F).homology n)) :
    IsZero (categoryHomology.{u, v} F n) :=
  h.of_iso (categoryHomologyReplacementIso.{u, v} F n)

end Stacks.CategoryHomology


namespace Stacks.Sites.FibredCategory

open CategoryHomology

universe uC uD vD v

variable {C : Type uC} [SmallCategory C] {D : Type uD} [Category.{vD} D] {p : C ⥤ D}
  (c : p.ChoiceOfPullbacks)

-- `Fiber` and `Fiber.fiberInclusion` are plain `def`s, so goals mentioning an object of a fibre or
-- its image in `C` are not type-correct at `implicit` transparency and `rw`/`simp` refuse them.
attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

/-- The summand inclusion of the decomposition attached to `h : V ⟶ p(U')`, before free abelian
groups are taken: postcomposition with the chosen cartesian lift `h^* U' ⟶ U'` sends a morphism
of the fibre at `V` into `h^* U'` to a morphism of the total category into `U'`. -/
def fiberHomPostcomp (U' : C) {V : D} (h : V ⟶ p.obj U') :
    yoneda.obj (c.pullbackObj U' h) ⟶
      (Functor.Fiber.fiberInclusion (p := p) (S := V)).op ⋙ yoneda.obj U' where
  app x := TypeCat.ofHom fun β : x.unop ⟶ c.pullbackObj U' h =>
    Functor.Fiber.fiberInclusion.map β ≫ c.pullbackHom U' h
  naturality _ _ _ := by
    ext β
    exact Category.assoc _ _ _

/-- The summand inclusion of the decomposition attached to `h : V ⟶ p(U')`: the free abelian
presheaf on the chosen pullback `h^* U'` maps to the restriction to the fibre at `V` of the free
abelian presheaf on `U'`, by postcomposition with the chosen cartesian lift. -/
def freeFiberSummandIncl (U' : C) {V : D} (h : V ⟶ p.obj U') :
    uliftFreeRepresentablePresheaf.{uC, max vD v} (c.pullbackObj U' h) ⟶
      (Functor.Fiber.fiberInclusion (p := p) (S := V)).op ⋙
        uliftFreeRepresentablePresheaf.{uC, max vD v} U' :=
  Functor.whiskerRight (fiberHomPostcomp c U' h)
    (AddCommGrpCat.free.{uC} ⋙ replacementUliftFunctor.{uC, max vD v})

/-- The summand inclusion sends the generator attached to a morphism `β : x ⟶ h^* U'` of the fibre
to the generator attached to its composite with the chosen cartesian lift. -/
lemma freeFiberSummandIncl_app_of (U' : C) {V : D} (h : V ⟶ p.obj U') (x : p.Fiber V)
    (β : x ⟶ c.pullbackObj U' h) :
    (freeFiberSummandIncl.{uC, uD, vD, v} c U' h).app (op x)
        (ULift.up (FreeAbelianGroup.of β)) =
      ULift.up (FreeAbelianGroup.of
        (Functor.Fiber.fiberInclusion.map β ≫ c.pullbackHom U' h)) :=
  rfl

section Decomposition

variable (U' : C) (V : D) [DecidableEq (ULift.{max uC v, vD} (V ⟶ p.obj U'))]

/-- The morphism out of the direct sum of the summands: the free abelian presheaves on the chosen
pullbacks `h^* U'`, summed over the morphisms `h : V ⟶ p(U')` of the base, map to the restriction
to the fibre at `V` of the free abelian presheaf on `U'`. -/
def freeFiberDirectSumDesc :
    directSumPresheaf (fun h : ULift.{max uC v, vD} (V ⟶ p.obj U') =>
        uliftFreeRepresentablePresheaf.{uC, max vD v} (c.pullbackObj U' h.down)) ⟶
      (Functor.Fiber.fiberInclusion (p := p) (S := V)).op ⋙
        uliftFreeRepresentablePresheaf.{uC, max vD v} U' :=
  directSumPresheafDesc _ fun h => freeFiberSummandIncl.{uC, uD, vD, v} c U' h.down

/-- On a section of the summand indexed by `h`, the morphism out of the direct sum is the summand
inclusion attached to `h`. -/
lemma freeFiberDirectSumDesc_app_of (h : ULift.{max uC v, vD} (V ⟶ p.obj U'))
    (x : (p.Fiber V)ᵒᵖ)
    (y : ((uliftFreeRepresentablePresheaf.{uC, max vD v}
      (c.pullbackObj U' h.down)).obj x : Type (max uC vD v))) :
    (freeFiberDirectSumDesc.{uC, uD, vD, v} c U' V).app x
        (DirectSum.of (fun j : ULift.{max uC v, vD} (V ⟶ p.obj U') =>
          ((uliftFreeRepresentablePresheaf.{uC, max vD v}
            (c.pullbackObj U' j.down)).obj x : Type (max uC vD v))) h y) =
      (freeFiberSummandIncl.{uC, uD, vD, v} c U' h.down).app x y :=
  directSumPresheafDesc_app_of
    (fun j : ULift.{max uC v, vD} (V ⟶ p.obj U') =>
      uliftFreeRepresentablePresheaf.{uC, max vD v} (c.pullbackObj U' j.down))
    (fun j => freeFiberSummandIncl.{uC, uD, vD, v} c U' j.down) h x y

/-- The morphism out of the direct sum restricts on each summand to the summand inclusion. -/
lemma directSumPresheafIncl_comp_freeFiberDirectSumDesc
    (h : ULift.{max uC v, vD} (V ⟶ p.obj U')) :
    directSumPresheafIncl _ h ≫ freeFiberDirectSumDesc.{uC, uD, vD, v} c U' V =
      freeFiberSummandIncl.{uC, uD, vD, v} c U' h.down :=
  NatTrans.ext (funext fun x => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun y =>
    freeFiberDirectSumDesc_app_of c U' V h x y))

/-- The inverse of the decomposition at an object `x` of the fibre at `V`: the generator attached
to a morphism `a : x ⟶ U'` goes to the generator attached to the first factor of `a`, in the
summand indexed by the base morphism that `a` lies over. -/
def freeFiberDecompInvApp (x : p.Fiber V) :
    ULift.{max vD v} (FreeAbelianGroup (x.1 ⟶ U')) →+
      (⨁ h : ULift.{max uC v, vD} (V ⟶ p.obj U'),
        ((uliftFreeRepresentablePresheaf.{uC, max vD v}
          (c.pullbackObj U' h.down)).obj (op x) : Type (max uC vD v))) :=
  (FreeAbelianGroup.lift fun a : x.1 ⟶ U' =>
      DirectSum.of
        (fun j : ULift.{max uC v, vD} (V ⟶ p.obj U') =>
          ((uliftFreeRepresentablePresheaf.{uC, max vD v}
            (c.pullbackObj U' j.down)).obj (op x) : Type (max uC vD v)))
        (ULift.up (c.homEquivSigma x (Functor.Fiber.mk rfl) a).1)
        (ULift.up (FreeAbelianGroup.of
          (c.homEquivSigma x (Functor.Fiber.mk rfl) a).2))).comp
    AddEquiv.ulift.toAddMonoidHom

/-- The inverse of the decomposition, on a generator. -/
lemma freeFiberDecompInvApp_of (x : p.Fiber V) (a : x.1 ⟶ U') :
    freeFiberDecompInvApp.{uC, uD, vD, v} c U' V x (ULift.up (FreeAbelianGroup.of a)) =
      DirectSum.of
        (fun j : ULift.{max uC v, vD} (V ⟶ p.obj U') =>
          ((uliftFreeRepresentablePresheaf.{uC, max vD v}
            (c.pullbackObj U' j.down)).obj (op x) : Type (max uC vD v)))
        (ULift.up (c.homEquivSigma x (Functor.Fiber.mk rfl) a).1)
        (ULift.up (FreeAbelianGroup.of
          (c.homEquivSigma x (Functor.Fiber.mk rfl) a).2)) :=
  FreeAbelianGroup.lift_apply_of _ a

/-- The morphism out of the direct sum sends the generator of the summand indexed by `t.1`
attached to `t.2` to the generator attached to the composite of `t.2` with the chosen cartesian
lift. -/
private lemma freeFiberDirectSumDesc_app_of_sigma (x : p.Fiber V)
    (t : (k : V ⟶ p.obj U') × (x ⟶ c.obj k (Functor.Fiber.mk rfl))) :
    (freeFiberDirectSumDesc.{uC, uD, vD, v} c U' V).app (op x)
        (DirectSum.of (fun j : ULift.{max uC v, vD} (V ⟶ p.obj U') =>
          ((uliftFreeRepresentablePresheaf.{uC, max vD v}
            (c.pullbackObj U' j.down)).obj (op x) : Type (max uC vD v)))
          (ULift.up t.1) (ULift.up (FreeAbelianGroup.of t.2))) =
      ULift.up (FreeAbelianGroup.of
        (Functor.Fiber.fiberInclusion.map t.2 ≫ c.pullbackHom U' t.1)) :=
  (freeFiberDirectSumDesc_app_of c U' V _ (op x) _).trans
    (freeFiberSummandIncl_app_of c U' _ x t.2)

/-- Two additive maps out of a lifted free abelian group agree if they agree on generators. -/
private lemma ulift_freeAbelianGroup_hom_ext {α : Type*} {M : Type*} [AddCommGroup M]
    {f g : ULift.{v} (FreeAbelianGroup α) →+ M}
    (h : ∀ a, f (ULift.up (FreeAbelianGroup.of a)) = g (ULift.up (FreeAbelianGroup.of a))) :
    f = g :=
  (AddMonoidHom.cancel_right (f := (AddEquiv.ulift (α := FreeAbelianGroup α)).symm.toAddMonoidHom)
    (AddEquiv.ulift (α := FreeAbelianGroup α)).symm.surjective).mp
    (FreeAbelianGroup.lift_ext _ _ h)

/-- Going out of the direct sum and back is the identity: the generator of the summand indexed by
`h` attached to `β : x ⟶ h^* U'` maps to the generator attached to the composite
`x ⟶ h^* U' ⟶ U'`, whose unique factorisation is `β` over `h`. -/
lemma freeFiberDecompInvApp_comp_app (x : p.Fiber V) :
    (freeFiberDecompInvApp.{uC, uD, vD, v} c U' V x).comp
        ((freeFiberDirectSumDesc.{uC, uD, vD, v} c U' V).app (op x)).hom =
      AddMonoidHom.id _ := by
  refine DirectSum.addHom_ext' fun h => ?_
  refine ulift_freeAbelianGroup_hom_ext fun β => ?_
  have hfac : c.homEquivSigma x (Functor.Fiber.mk rfl)
      (Functor.Fiber.fiberInclusion.map β ≫ c.pullbackHom U' h.down) = ⟨h.down, β⟩ :=
    c.sigma_baseHom_fiberFactor_eq _ β rfl
  have hdesc := freeFiberDirectSumDesc_app_of_sigma c U' V x ⟨h.down, β⟩
  refine (congrArg (freeFiberDecompInvApp.{uC, uD, vD, v} c U' V x) hdesc).trans ?_
  refine (freeFiberDecompInvApp_of c U' V x _).trans ?_
  dsimp only
  erw [hfac]
  rfl

/-- Going into the direct sum and back out is the identity: the generator attached to
`a : x ⟶ U'` maps to the generator attached to the defining factorisation of `a`, whose composite
is `a`. -/
lemma app_comp_freeFiberDecompInvApp (x : p.Fiber V) :
    (((freeFiberDirectSumDesc.{uC, uD, vD, v} c U' V).app (op x)).hom).comp
        (freeFiberDecompInvApp.{uC, uD, vD, v} c U' V x) =
      AddMonoidHom.id _ := by
  refine ulift_freeAbelianGroup_hom_ext fun a => ?_
  exact (congrArg ((freeFiberDirectSumDesc.{uC, uD, vD, v} c U' V).app (op x))
    (freeFiberDecompInvApp_of c U' V x a)).trans
    ((freeFiberDirectSumDesc_app_of_sigma c U' V x _).trans
      (congrArg (fun b : x.1 ⟶ U' => ULift.up (FreeAbelianGroup.of b))
        (c.fiberFactor_fac x (Functor.Fiber.mk rfl) a)))

/-- The morphism out of the direct sum is an isomorphism at every object of the fibre: the two
round trips are the two halves of the unique factorisation through the chosen cartesian lift. -/
instance isIso_freeFiberDirectSumDesc_app (x : (p.Fiber V)ᵒᵖ) :
    IsIso ((freeFiberDirectSumDesc.{uC, uD, vD, v} c U' V).app x) :=
  ⟨AddCommGrpCat.ofHom (freeFiberDecompInvApp.{uC, uD, vD, v} c U' V x.unop),
    AddCommGrpCat.hom_ext (freeFiberDecompInvApp_comp_app c U' V x.unop),
    AddCommGrpCat.hom_ext (app_comp_freeFiberDecompInvApp c U' V x.unop)⟩

/-- The morphism out of the direct sum is an isomorphism of presheaves. -/
instance isIso_freeFiberDirectSumDesc :
    IsIso (freeFiberDirectSumDesc.{uC, uD, vD, v} c U' V) :=
  NatIso.isIso_of_isIso_app _

/-- **The free abelian presheaf on `U'`, restricted to the fibre at `V`, is the direct sum over
the morphisms `h : V ⟶ p(U')` of the base of the free abelian presheaves on the chosen pullbacks
`h^* U'`.** Every morphism from an object of the fibre at `V` into `U'` factors uniquely through
the chosen cartesian lift of the base morphism it lies over, so the generators of the left-hand
side are indexed by the disjoint union of the index sets of the summands. -/
def freePresheafFiberDecomposition :
    (Functor.Fiber.fiberInclusion (p := p) (S := V)).op ⋙
        uliftFreeRepresentablePresheaf.{uC, max vD v} U' ≅
      directSumPresheaf (fun h : ULift.{max uC v, vD} (V ⟶ p.obj U') =>
        uliftFreeRepresentablePresheaf.{uC, max vD v} (c.pullbackObj U' h.down)) :=
  (asIso (freeFiberDirectSumDesc.{uC, uD, vD, v} c U' V)).symm

/-- The decomposition is inverse to the morphism assembled from the summand inclusions. -/
lemma freePresheafFiberDecomposition_inv :
    (freePresheafFiberDecomposition.{uC, uD, vD, v} c U' V).inv =
      freeFiberDirectSumDesc.{uC, uD, vD, v} c U' V :=
  rfl

/-- The decomposition is compatible with the summand inclusions: composing the inclusion of the
summand indexed by `h` with the inverse of the decomposition gives the summand inclusion attached
to `h`. -/
lemma directSumPresheafIncl_comp_freePresheafFiberDecomposition_inv
    (h : ULift.{max uC v, vD} (V ⟶ p.obj U')) :
    directSumPresheafIncl _ h ≫ (freePresheafFiberDecomposition.{uC, uD, vD, v} c U' V).inv =
      freeFiberSummandIncl.{uC, uD, vD, v} c U' h.down :=
  directSumPresheafIncl_comp_freeFiberDirectSumDesc c U' V h

end Decomposition

/-- **The higher homology of a fibre with coefficients in a restricted free abelian presheaf
vanishes.** For a fibred category `p : C ⥤ D`, an object `U'` of `C` and an object `V` of `D`, the
homology of the fibre at `V` with coefficients in the restriction of the universe-lifted free
abelian presheaf on `U'` is zero in every positive degree: that restriction is a direct sum of
free abelian presheaves on the chosen pullbacks of `U'`, each of which has acyclic simplicial
replacement. -/
theorem categoryHomology_fiberRestriction_isZero [p.IsFibered] (U' : C) (V : D) (n : ℕ) :
    IsZero (categoryHomology.{uC, max vD v}
      ((Functor.Fiber.fiberInclusion (p := p) (S := V)).op ⋙
        uliftFreeRepresentablePresheaf.{uC, max vD v} U') (n + 1)) := by
  classical
  refine categoryHomology_isZero_of_iso.{uC, max vD v}
    (freePresheafFiberDecomposition.{uC, uD, vD, v} (Functor.chosenPullbacks p) U' V)
    (n + 1) ?_
  refine categoryHomology_isZero_of_replacementComplex_homology_isZero.{uC, max vD v} _
    (n + 1) ?_
  exact replacementComplex_homology_isZero_of_directSum _ n fun h =>
    uliftFreeRepresentablePresheaf_homology_isZero.{uC, max vD v} _ n

end Stacks.Sites.FibredCategory

end
