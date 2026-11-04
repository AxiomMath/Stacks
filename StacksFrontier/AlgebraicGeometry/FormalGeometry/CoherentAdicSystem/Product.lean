module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Transition

/-!
# Finite products of coherent adic systems

Let `X` be a scheme and `ℐ` a quasi-coherent sheaf of ideals on `X`. The category `Coh(X, ℐ)` of
coherent adic systems along `ℐ` is a full subcategory of `ℕᵒᵖ ⥤ X.Modules`, and this file shows
that it has finite products, computed levelwise: the product of finitely many coherent adic
systems is the levelwise product of the underlying inverse systems, and that levelwise product
is again a coherent adic system.

Each of the three defining clauses survives the passage to a finite limit for its own reason.
Coherence is preserved because coherent sheaves of modules form a weak Serre subcategory, so they
contain the zero object and are closed under extensions, hence under binary biproducts and so
under all finite products. The annihilation clause is preserved because the projections of a
limit cone are jointly monic, and each of them carries `ℐ ⁿ⁺¹` of the apex into `ℐ ⁿ⁺¹` of a
factor, which vanishes. The transition clause is preserved because `M ↦ M / ℐ ⁿ⁺¹ M` is an
additive functor, hence preserves finite products: applying it to the evaluated limit cone at
level `n + 1` and composing with the factorwise identifications `F_{n+1} / ℐ ⁿ⁺¹ F_{n+1} ≅ F_n`
produces a second limit cone over the diagram at level `n`, and the two apexes agree.

## Main definitions

* `Stacks.Algebraization.idealPowerQuotientFunctor` — the functor `M ↦ M / ℐ ⁿ M` on sheaves of
  modules over a scheme.

## Main results

* `Stacks.Coherent.isCoherent_of_isLimit` — a finite product of coherent sheaves of modules is
  coherent.
* `Stacks.Coherent.isCoherentAdicSystem_of_product` — the apex of a limit cone over a finite
  discrete diagram of coherent adic systems is again a coherent adic system.
* `Stacks.Coherent.createsLimitsOfShapeDiscrete` — the inclusion of `Coh(X, ℐ)` into
  `ℕᵒᵖ ⥤ X.Modules` creates finite products, which is the precise form of "the product is
  computed levelwise".
* `Stacks.Coherent.hasFiniteProducts` and
  `Stacks.Coherent.preservesFiniteProducts_coherentAdicSystemsι` — `Coh(X, ℐ)` has finite
  products and the inclusion preserves them.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed: term `n` represents the Stacks source's
`F_{n+1}`, which is why the annihilating exponent at `n` is `n + 1`.

`AlgebraicGeometry.Scheme.Modules` is a definition rather than an abbreviation for
`SheafOfModules X.ringCatSheaf`, and the subsheaf attached to a `SheafOfModules.Submodule` is an
object of the latter. The zero morphism out of such a subsheaf therefore cannot be written down
directly, which is why `Stacks.Algebraization.submodule_eq_bot_of_isLimit` quantifies over an
object `T` of `X.Modules` internally instead of naming that morphism in its statement. For the
same reason several proofs below are explicit chains of `Category.assoc` and `congrArg` where a
rewrite would be more natural: a goal mentioning `(idealPowerMultiple I n M).ι` is not
type-correct at the transparency `rw` builds its motive at.

Coherence of a finite product is obtained from the weak Serre package for the root coherence
predicate, `SheafOfModules.coherentModules_isWeakSerreClass`, rather than
declared as an instance on the object property `fun M : X.Modules => M.IsCoherent`: instance
resolution does not reliably unify against a coherence property stated as a lambda, so the
closure facts are supplied as theorems and installed locally where they are used.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-! ### Submodules of the apex of a limit cone -/

section Submodule

variable {X : Scheme.{u}}

/-- A submodule of a sheaf of modules all of whose sections vanish is the zero submodule. -/
public theorem submodule_eq_bot_of_forall_eq_zero {M : X.Modules} (S : M.Submodule)
    (h : ∀ (U : (TopologicalSpace.Opens X)ᵒᵖ) (x : Γ(M, U.unop)),
      x ∈ S.toSubmodule.obj U → x = 0) :
    S = ⊥ := by
  refine le_antisymm (SheafOfModules.Submodule.le_iff.mpr fun U x hx => ?_) bot_le
  rw [h U x hx]
  exact Submodule.zero_mem _

/-- A submodule of the apex of a limit cone vanishes as soon as every projection of the cone
kills it: the projections of a limit cone are jointly monic, so a subsheaf contained in all of
their kernels has zero inclusion, hence no nonzero sections. -/
public theorem submodule_eq_bot_of_isLimit {J : Type*} [Category J] {D : J ⥤ X.Modules}
    {c : Cone D} (hc : IsLimit c) (S : c.pt.Submodule)
    (h : ∀ j, S ≤ kernelSubmodule (c.π.app j)) :
    S = ⊥ := by
  have hjoint : ∀ (T : X.Modules) (p : T ⟶ c.pt), (∀ j, p ≫ c.π.app j = 0) → p = 0 :=
    fun _ p hp => hc.hom_ext fun j => (hp j).trans zero_comp.symm
  have hι := hjoint _ S.ι fun j => by
    refine Scheme.Modules.hom_ext _ _ fun V => ?_
    ext x
    have hx := SheafOfModules.Submodule.le_iff.mp (h j) (op V) x.property
    rw [kernelSubmodule_toSubmodule_obj] at hx
    exact hx
  exact submodule_eq_bot_of_forall_eq_zero S fun U x hx =>
    congrArg (fun t => t.app U.unop ⟨x, hx⟩) hι

end Submodule

/-! ### The ideal-power quotient as a functor -/

section QuotientFunctor

variable {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)

/-- The functor `M ↦ M / ℐ ⁿ M` on sheaves of modules over a scheme. -/
public def idealPowerQuotientFunctor : X.Modules ⥤ X.Modules where
  obj M := idealPowerQuotient I n M
  map f := idealPowerQuotientMap I I n n le_rfl f
  map_id M := idealPowerQuotientMap_id I n M
  map_comp f g := idealPowerQuotientMap_comp I n f g

/-- The functor `idealPowerQuotientFunctor I n` sends `M` to `M / ℐ ⁿ M`. -/
@[simp]
public theorem idealPowerQuotientFunctor_obj (M : X.Modules) :
    (idealPowerQuotientFunctor I n).obj M = idealPowerQuotient I n M :=
  rfl

/-- The functor `idealPowerQuotientFunctor I n` sends a morphism to its reduction modulo `ℐ ⁿ`. -/
@[simp]
public theorem idealPowerQuotientFunctor_map {M N : X.Modules} (f : M ⟶ N) :
    (idealPowerQuotientFunctor I n).map f = idealPowerQuotientMap I I n n le_rfl f :=
  rfl

/-- Reduction modulo `ℐ ⁿ` is additive in the morphism, because the quotient projection is an
epimorphism and intertwines the two sides. -/
public theorem idealPowerQuotientMap_add {M N : X.Modules} (f g : M ⟶ N) :
    idealPowerQuotientMap I I n n le_rfl (f + g) =
      idealPowerQuotientMap I I n n le_rfl f + idealPowerQuotientMap I I n n le_rfl g := by
  refine (cancel_epi (cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι)).1 ?_
  rw [idealPowerQuotientMap_π, Preadditive.comp_add (C := X.Modules),
    idealPowerQuotientMap_π, idealPowerQuotientMap_π,
    Preadditive.add_comp (C := X.Modules)]

/-- The functor `M ↦ M / ℐ ⁿ M` is additive. -/
public instance idealPowerQuotientFunctor_additive :
    (idealPowerQuotientFunctor I n).Additive where
  map_add := idealPowerQuotientMap_add I n _ _

end QuotientFunctor

end Stacks.Algebraization

namespace Stacks.Coherent

/-! ### Coherence of a finite product -/

section Coherence

variable (X : Scheme.{u})

/-- Coherent sheaves of modules on a scheme are closed under finite products.

They contain the zero object and are closed under extensions, being a weak Serre subcategory, so
they are closed under binary biproducts; a binary product in an additive category is a binary
biproduct, and finite products are built from binary products and the terminal object. -/
public theorem isClosedUnderFiniteProducts_isCoherent :
    ObjectProperty.IsClosedUnderFiniteProducts
      (fun M : X.Modules => _root_.SheafOfModules.IsCoherent.{u} M) := by
  set P : ObjectProperty X.Modules := fun M => _root_.SheafOfModules.IsCoherent.{u} M
  have : P.IsWeakSerreClass :=
    _root_.SheafOfModules.coherentModules_isWeakSerreClass
  have : P.IsClosedUnderBinaryProducts :=
    ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
      rintro _ ⟨F, hF⟩
      exact P.prop_of_iso
        ((biprod.isoProd (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)).trans
          (HasLimit.isoOfNatIso (diagramIsoPair F)).symm)
        (P.prop_biprod (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)))
  exact ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- **A finite product of coherent sheaves of modules is coherent.** -/
public theorem isCoherent_of_isLimit {J : Type*} [Finite J] {D : Discrete J ⥤ X.Modules}
    {c : Cone D} (hc : IsLimit c)
    (h : ∀ j, _root_.SheafOfModules.IsCoherent.{u} (D.obj j)) :
    _root_.SheafOfModules.IsCoherent.{u} c.pt := by
  have := isClosedUnderFiniteProducts_isCoherent X
  exact (show ObjectProperty X.Modules from
    fun M => _root_.SheafOfModules.IsCoherent.{u} M).prop_of_isLimit hc h

end Coherence

/-! ### The levelwise product of coherent adic systems -/

section Product

variable {X : Scheme.{u}} (I : X.IdealSheafData) {J : Type} [Finite J]
  (D : Discrete J ⥤ CoherentAdicSystems I)
  (c : Cone (D ⋙ ObjectProperty.ι (IsCoherentAdicSystem I)))

/-- Evaluating a limit cone of inverse systems at a level is again a limit cone: limits in a
functor category are computed levelwise. -/
public def isLimitMapConeEvaluation (hc : IsLimit c) (n : ℕ) :
    IsLimit (((evaluation ℕᵒᵖ X.Modules).obj (op n)).mapCone c) :=
  isLimitOfPreserves _ hc

/-- Every term of the levelwise product of finitely many coherent adic systems is coherent. -/
public theorem isCoherent_of_product (hc : IsLimit c) (n : ℕ) :
    _root_.SheafOfModules.IsCoherent.{u} (c.pt.obj (op n)) :=
  isCoherent_of_isLimit X (isLimitMapConeEvaluation I D c hc n)
    fun j => (D.obj j).property.isCoherent n

/-- `ℐ ⁿ⁺¹` annihilates the `n`-th term of the levelwise product of finitely many coherent adic
systems: each projection of the evaluated limit cone carries `ℐ ⁿ⁺¹` of the apex into `ℐ ⁿ⁺¹` of
a factor, which vanishes, and the projections are jointly monic. -/
public theorem idealPowerMultiple_of_product_eq_bot (hc : IsLimit c) (n : ℕ) :
    idealPowerMultiple I (n + 1) (c.pt.obj (op n)) = ⊥ :=
  submodule_eq_bot_of_isLimit (isLimitMapConeEvaluation I D c hc n) _ fun j =>
    idealPowerMultiple_le_sheafSubmoduleComap I (n + 1) _ ⊥
      ((D.obj j).property.idealPowerMultiple_eq_bot n).le

/-- The `n`-th term of the levelwise product of finitely many coherent adic systems is the
quotient of the `(n + 1)`-st by `ℐ ⁿ⁺¹`, compatibly with the transition map.

The functor `M ↦ M / ℐ ⁿ⁺¹ M` is additive, hence preserves finite products, so it carries the
limit cone at level `n + 1` to a limit cone; postcomposing with the factorwise identifications
`F_{n+1} / ℐ ⁿ⁺¹ F_{n+1} ≅ F_n` turns that into a limit cone over the diagram at level `n`, whose
apex is therefore canonically identified with the `n`-th term. -/
public theorem exists_quotientIso_of_product (hc : IsLimit c) (n : ℕ) :
    ∃ e : idealPowerQuotient I (n + 1) (c.pt.obj (op (n + 1))) ≅ c.pt.obj (op n),
      cokernel.π (C := X.Modules)
          (idealPowerMultiple I (n + 1) (c.pt.obj (op (n + 1)))).ι ≫ e.hom =
        c.pt.map (homOfLE (Nat.le_succ n)).op := by
  let G := D ⋙ ObjectProperty.ι (IsCoherentAdicSystem I)
  let E : ℕ → (ℕᵒᵖ ⥤ X.Modules) ⥤ X.Modules :=
    fun m => (evaluation ℕᵒᵖ X.Modules).obj (op m)
  let Q := idealPowerQuotientFunctor I (n + 1)
  let ec : (G ⋙ E (n + 1)) ⋙ Q ≅ G ⋙ E n :=
    Discrete.natIso fun j => (D.obj j).property.quotientIso n
  let cq := Q.mapCone ((E (n + 1)).mapCone c)
  have hq : IsLimit ((Cone.postcompose ec.hom).obj cq) :=
    (IsLimit.postcomposeHomEquiv ec cq).symm
      (isLimitOfPreserves Q (isLimitMapConeEvaluation I D c hc (n + 1)))
  have hcn := isLimitMapConeEvaluation I D c hc n
  refine ⟨hq.conePointUniqueUpToIso hcn, hcn.hom_ext fun j => ?_⟩
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => cokernel.π (C := X.Modules)
      (idealPowerMultiple I (n + 1) (c.pt.obj (op (n + 1)))).ι ≫ t)
    (IsLimit.conePointUniqueUpToIso_hom_comp hq hcn j)).trans ?_
  change cokernel.π (C := X.Modules)
        (idealPowerMultiple I (n + 1) (c.pt.obj (op (n + 1)))).ι ≫
      (idealPowerQuotientMap I I (n + 1) (n + 1) le_rfl ((c.π.app j).app (op (n + 1))) ≫
        ((D.obj j).property.quotientIso n).hom) =
    c.pt.map (homOfLE (Nat.le_succ n)).op ≫ (c.π.app j).app (op n)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ ((D.obj j).property.quotientIso n).hom)
    (idealPowerQuotientMap_π I I (n + 1) (n + 1) le_rfl
      ((c.π.app j).app (op (n + 1))))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => (c.π.app j).app (op (n + 1)) ≫ t)
    ((D.obj j).property.cokernel_π_comp_quotientIso n)).trans ?_
  exact ((c.π.app j).naturality (homOfLE (Nat.le_succ n)).op).symm

/-- **A finite product of coherent adic systems is a coherent adic system.** -/
public theorem isCoherentAdicSystem_of_product (hc : IsLimit c) :
    IsCoherentAdicSystem I c.pt :=
  ⟨isCoherent_of_product I D c hc, idealPowerMultiple_of_product_eq_bot I D c hc,
    exists_quotientIso_of_product I D c hc⟩

end Product

/-! ### Finite products in the category of coherent adic systems -/

section HasProducts

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **The inclusion of coherent adic systems into inverse systems of sheaves of modules creates
finite products.** This is the precise sense in which the product in `Coh(X, ℐ)` is computed
levelwise: it is the levelwise product of the underlying inverse systems. -/
public instance createsLimitsOfShapeDiscrete (J : Type) [Finite J] :
    CreatesLimitsOfShape (Discrete J) (ObjectProperty.ι (IsCoherentAdicSystem I)) where
  CreatesLimit {D} :=
    createsLimitFullSubcategoryInclusion' D (limit.isLimit _)
      (isCoherentAdicSystem_of_product I D _ (limit.isLimit _))

/-- **The category of coherent adic systems has finite products.** -/
public instance hasFiniteProducts : HasFiniteProducts (CoherentAdicSystems I) where
  out _ :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
      (ObjectProperty.ι (IsCoherentAdicSystem I))

/-- The inclusion of coherent adic systems into inverse systems of sheaves of modules preserves
finite products, since it creates them. -/
public instance preservesFiniteProducts_coherentAdicSystemsι :
    PreservesFiniteProducts (ObjectProperty.ι (IsCoherentAdicSystem I)) where
  preserves _ := inferInstance

end HasProducts

end Stacks.Coherent

end
