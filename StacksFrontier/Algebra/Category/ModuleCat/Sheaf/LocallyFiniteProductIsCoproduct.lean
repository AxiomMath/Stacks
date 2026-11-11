module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.Grp.Colimits
public import StacksFrontier.Topology.Sheaves.LocallyFiniteCoproductSections

/-!
# A product of sheaves of modules with locally finitely many nonzero factors is a coproduct

Let `R` be a sheaf of rings on a site `(C, J)` and let `M : I → SheafOfModules R` be a family of
sheaves of modules such that every object `V` of `C` carries a covering sieve on whose members
all but finitely many of the `M i` have no nonzero sections. Then a product `P` of the family,
together with the canonical injections (the identity in the own factor and zero in the others),
is also a coproduct of the family.

The point is the one behind Tag 02FT. Let `Q` be the coproduct of the underlying presheaves of
modules, which is computed objectwise. Over a member `W` of one of the covering sieves the
comparison `Q(W) ⟶ P(W)` is the inclusion of a direct sum of modules with finitely many
nonzero summands into their product, hence an isomorphism. So the comparison `Q ⟶ P` is a
locally bijective morphism of presheaves of modules, and morphisms out of it into a sheaf of
modules are the same as morphisms out of `Q`, that is families of morphisms out of the `M i`
(`CategoryTheory.PresheafOfModules.homEquivOfIsLocallyBijective`).

Unlike `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocallyFiniteCoproductOnASite.lean` the
index type and all universes are arbitrary, subject only to the index type being small for the
universe of the modules, and no sheafification of presheaves of modules is used: the argument
needs neither the existence of the coproduct in sheaves of modules nor a sheafification functor.

## Main definitions

* `Stacks.SheafOfModules.LocallyFiniteProduct.IsLocallyFinitelyNonzero`: every object of the site
  has a covering sieve on whose members all but finitely many members of the family have no
  nonzero sections.
* `Stacks.SheafOfModules.LocallyFiniteProduct.deltaInj`: the canonical injection of `M i` into
  a product `P` of the family.

## Main results

* `Stacks.SheafOfModules.LocallyFiniteProduct.isColimitCofanDeltaInj`: for such a family the
  product `P` with the canonical injections is a coproduct.

## References

* [Stacks Project, Tag 02FT](https://stacks.math.columbia.edu/tag/02FT)
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

namespace Stacks.SheafOfModules.LocallyFiniteProduct

universe v₁ u₁ u v t

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  {I : Type t} (M : I → SheafOfModules.{v} R)

/-- Every object of the site has a covering sieve on whose members all but finitely many members
of the family have no nonzero sections. -/
def IsLocallyFinitelyNonzero : Prop :=
  ∀ V : C, ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (g : W ⟶ V), T g →
    ∃ S : Finset I, ∀ i ∉ S, IsZero ((M i).val.obj (op W))

variable {P : SheafOfModules.{v} R} (π : ∀ i, P ⟶ M i)
  (hP : IsLimit (Fan.mk P π))

open scoped Classical in
/-- The canonical injection of `M i` into the product `P` of the family: its `j`-th component is
the identity for `j = i` and zero otherwise. -/
def deltaInj (i : I) : M i ⟶ P :=
  hP.lift (Fan.mk (M i) fun j => if h : i = j then eqToHom (congrArg M h) else 0)

/-- The `i`-th component of the `i`-th canonical injection is the identity. -/
@[simp]
theorem deltaInj_comp_π_self (i : I) : deltaInj R M π hP i ≫ π i = 𝟙 (M i) := by
  rw [deltaInj]
  refine (hP.fac _ ⟨i⟩).trans ?_
  simp

/-- The `j`-th component of the `i`-th canonical injection vanishes for `j ≠ i`. -/
@[simp]
theorem deltaInj_comp_π_ne {i j : I} (h : i ≠ j) : deltaInj R M π hP i ≫ π j = 0 := by
  rw [deltaInj]
  refine (hP.fac _ ⟨j⟩).trans ?_
  simp [h]

variable [Small.{v} I]

/-- Abelian groups have colimits indexed by a type small for their universe. -/
instance : HasColimitsOfShape (Discrete I) AddCommGrpCat.{v} :=
  hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{v} I)).symm

/-- The coproduct of the underlying presheaves of modules, computed objectwise. -/
abbrev presCoprod : PresheafOfModules.{v} R.obj := ∐ fun i => (M i).val

/-- The comparison morphism of presheaves of modules from the objectwise coproduct to the
sections of the product `P`. -/
def presToProd : presCoprod R M ⟶ P.val :=
  Sigma.desc fun i => (deltaInj R M π hP i).val

/-- The `i`-th leg of the objectwise coproduct, followed by the comparison morphism, is the
`i`-th canonical injection. -/
theorem ι_presToProd (i : I) :
    Sigma.ι (fun k => (M k).val) i ≫ presToProd R M π hP = (deltaInj R M π hP i).val :=
  Sigma.ι_desc _ _

/-- If all but finitely many members of the family have no nonzero sections over `W`, then the
comparison morphism is an isomorphism over `W`: a direct sum and a product of a family of
modules with only finitely many nonzero members agree. -/
theorem isIso_presToProd_app (W : C) (S : Finset I)
    (hS : ∀ i ∉ S, IsZero ((M i).val.obj (op W))) :
    IsIso ((presToProd R M π hP).app (op W)) := by
  have hc := isColimitOfHasCoproductOfPreservesColimit
    (PresheafOfModules.evaluation R.obj (op W)) (fun i => (M i).val)
  have hl := isLimitOfPreserves (SheafOfModules.evaluation.{v} R (op W)) hP
  refine Stacks.isIso_of_isZero_of_notMem
    (A := fun i => (M i).val.obj (op W))
    (fun i => (Sigma.ι (fun k => (M k).val) i).app (op W))
    (fun i => (π i).val.app (op W))
    (fun g h hgh => Cofan.IsColimit.hom_ext hc g h hgh)
    (fun g h hgh => hl.hom_ext (by rintro ⟨i⟩; exact hgh i))
    _ (fun i => ?_) (fun i j hij => ?_) S hS
  · have h1 : (Sigma.ι (fun k => (M k).val) i ≫ presToProd R M π hP) ≫ (π i).val = 𝟙 _ := by
      rw [ι_presToProd, ← SheafOfModules.comp_val, deltaInj_comp_π_self]
      rfl
    exact congrArg (fun φ : (M i).val ⟶ (M i).val => φ.app (op W)) h1
  · have h1 : (Sigma.ι (fun k => (M k).val) i ≫ presToProd R M π hP) ≫ (π j).val = 0 := by
      rw [ι_presToProd, ← SheafOfModules.comp_val, deltaInj_comp_π_ne R M π hP hij]
      rfl
    exact congrArg (fun φ : (M i).val ⟶ (M j).val => φ.app (op W)) h1

/-- For a family with locally finitely many nonzero members, every object of the site carries a
covering sieve on whose members the comparison morphism of presheaves is an isomorphism. -/
theorem exists_sieve_isIso_presToProd_app (h : IsLocallyFinitelyNonzero R M) (V : C) :
    ∃ T : Sieve V, T ∈ J V ∧
      ∀ ⦃W : C⦄ (g : W ⟶ V), T g → IsIso ((presToProd R M π hP).app (op W)) := by
  obtain ⟨T, hT, hfin⟩ := h V
  refine ⟨T, hT, fun {W} g hg => ?_⟩
  obtain ⟨S, hS⟩ := hfin g hg
  exact isIso_presToProd_app R M π hP W S hS

/-- Where the comparison morphism of presheaves is an isomorphism, the underlying map of abelian
groups is bijective. -/
theorem bijective_toPresheaf_presToProd_app {W : C}
    (hiso : IsIso ((presToProd R M π hP).app (op W))) :
    Function.Bijective
      (((PresheafOfModules.toPresheaf R.obj).map (presToProd R M π hP)).app (op W)) :=
  ConcreteCategory.bijective_of_isIso ((presToProd R M π hP).app (op W))

/-- The comparison morphism of presheaves is locally injective. -/
theorem isLocallyInjective_presToProd (h : IsLocallyFinitelyNonzero R M) :
    PresheafOfModules.IsLocallyInjective J (presToProd R M π hP) where
  equalizerSieve_mem {V} x y hxy := by
    obtain ⟨T, hT, hiso⟩ := exists_sieve_isIso_presToProd_app R M π hP h V.unop
    refine J.superset_covering ?_ hT
    intro W g hg
    refine (bijective_toPresheaf_presToProd_app R M π hP (hiso g hg)).1 ?_
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]

/-- The comparison morphism of presheaves is locally surjective. -/
theorem isLocallySurjective_presToProd (h : IsLocallyFinitelyNonzero R M) :
    PresheafOfModules.IsLocallySurjective J (presToProd R M π hP) where
  imageSieve_mem {V} s := by
    obtain ⟨T, hT, hiso⟩ := exists_sieve_isIso_presToProd_app R M π hP h V
    refine J.superset_covering ?_ hT
    intro W g hg
    exact (bijective_toPresheaf_presToProd_app R M π hP (hiso g hg)).2 _

variable [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- **The product is a coproduct.** For a family of sheaves of modules with locally finitely
many nonzero members, a product `P` of the family together with the canonical injections
`deltaInj` is a coproduct of the family. -/
def isColimitCofanDeltaInj (h : IsLocallyFinitelyNonzero R M) :
    IsColimit (Cofan.mk P (deltaInj R M π hP)) := by
  have := isLocallyInjective_presToProd R M π hP h
  have := isLocallySurjective_presToProd R M π hP h
  let e := fun T : SheafOfModules.{v} R =>
    PresheafOfModules.homEquivOfIsLocallyBijective (J := J) (presToProd R M π hP) T.isSheaf
  refine Cofan.IsColimit.mk _
    (fun t => ⟨(e t.pt).symm (Sigma.desc fun i => (t.inj i).val)⟩) (fun t j => ?_)
    (fun t m hm => ?_)
  · apply SheafOfModules.hom_ext
    change (deltaInj R M π hP j).val ≫ (e t.pt).symm (Sigma.desc fun i => (t.inj i).val) = _
    rw [← ι_presToProd, Category.assoc]
    change Sigma.ι (fun k => (M k).val) j ≫ (e t.pt) ((e t.pt).symm _) = _
    rw [Equiv.apply_symm_apply, Sigma.ι_desc]
  · apply SheafOfModules.hom_ext
    change m.val = (e t.pt).symm (Sigma.desc fun i => (t.inj i).val)
    rw [Equiv.eq_symm_apply]
    refine Sigma.hom_ext _ _ fun i => ?_
    change Sigma.ι (fun k => (M k).val) i ≫ presToProd R M π hP ≫ m.val = _
    rw [← Category.assoc, ι_presToProd, Sigma.ι_desc, ← SheafOfModules.comp_val]
    exact congrArg SheafOfModules.Hom.val (hm i)

end Stacks.SheafOfModules.LocallyFiniteProduct
