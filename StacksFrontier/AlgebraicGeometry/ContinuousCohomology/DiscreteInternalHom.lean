module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.DiscreteCompletedGroupAlgebraModule
public import StacksFrontier.Algebra.Module.CharacterModule.Finite
public import StacksFrontier.Algebra.Homology.DerivedCategory.Opposite
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree

/-!
# The internal hom `Hom_ℤ(V, W)` of discrete modules, over the completed group algebra

Let `R` be a finite ring, not necessarily commutative, and `Q` a compact topological group. For a
continuous discrete `R`-`Q`-module `V` and a continuous discrete `ℤ`-`Q`-module `W`, the group
`Hom_ℤ(V, W)` of additive maps carries

* the conjugation action of `Q`, `(q · φ)(v) = q · φ(q⁻¹ · v)`, and
* the `Rᵐᵒᵖ`-module structure `(op r · φ)(v) = φ(r · v)`,

and these make it a module over the completed group algebra `Rᵐᵒᵖ[[Q]]`: an element `x` acts on
`φ` at `v` through the discrete module `Hom_ℤ(S, W)`, for any finite `Q`-stable `R`-submodule `S`
of `V` containing `v` (`Stacks.ContinuousCohomology.internalHom_smul_apply_of_mem`). The module
`Hom_ℤ(V, W)` is not discrete in general: for `W = ℚ/ℤ` it is the profinite Pontryagin dual of
`V`. Its action is the limit of the actions on the discrete modules `Hom_ℤ(S, W)`.

With `W = ℚ/ℤ` this is the character dual `V^∨ = Hom(V, ℚ/ℤ)` of the "trivial duality" of
[Stacks, Section 03VI], read as a module over `Rᵐᵒᵖ[[Q]]`. The contragredient `V ↦ V^∨` is exact,
and its derived functor computes `H^m(K^∨) ≅ (H^{-m} K)^∨`.

## Main definitions

* `Stacks.ContinuousCohomology.InternalHomAction.addMonoidHomMulOppositeModule` (scoped
  instance): `(op r • φ)(a) = φ(r • a)` on `A →+ B`.
* `Stacks.ContinuousCohomology.orbitSpan`: the finite `Q`-stable submodule spanned by the orbit of
  an element.
* `Stacks.ContinuousCohomology.restrictedHomObj`: `Hom_ℤ(S, W)` as a discrete
  `Rᵐᵒᵖ`-`Q`-module, for `S` finite and `Q`-stable.
* `Stacks.ContinuousCohomology.internalHomModule`: the `Rᵐᵒᵖ[[Q]]`-module structure on
  `Hom_ℤ(V, W)`.
* `Stacks.ContinuousCohomology.internalHom`: the bifunctor
  `(Mod_{R,Q})ᵒᵖ ⥤ Mod_{ℤ,Q} ⥤ ModuleCat Rᵐᵒᵖ[[Q]]`.
* `Stacks.ContinuousCohomology.contragredient`: the contragredient `V ↦ V^∨ = Hom_ℤ(V, ℚ/ℤ)`.
* `Stacks.ContinuousCohomology.derivedContragredient`: the derived contragredient
  `D(Mod_{R,Q})ᵒᵖ ⥤ D(Rᵐᵒᵖ[[Q]])`.

## Main results

* `Stacks.ContinuousCohomology.internalHom_smul_apply_of_mem`: `(x • φ)(v)` is computed on any
  finite `Q`-stable submodule containing `v`.
* `Stacks.ContinuousCohomology.internalHom_of_smul_apply`: a group element acts by conjugation.
* `Stacks.ContinuousCohomology.internalHom_const_op_smul_apply`: a constant acts through the
  source.
* `Stacks.ContinuousCohomology.preservesHomology_contragredient`: the contragredient is exact.

## References

* [Stacks Project, Section 03VI](https://stacks.math.columbia.edu/tag/03VI)
* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupHomology

universe u v w w' w''

namespace Stacks.ContinuousCohomology

/-! ### `Rᵐᵒᵖ` acting on additive maps out of an `R`-module -/

namespace InternalHomAction

variable (R : Type u) [Ring R] (A : Type*) (B : Type*) [AddCommGroup A] [Module R A]
  [AddCommGroup B]

/-- **`Rᵐᵒᵖ` acts on `A →+ B` through the source**: `(op r • φ)(a) = φ(r • a)`. -/
scoped instance addMonoidHomMulOppositeModule : Module Rᵐᵒᵖ (A →+ B) where
  smul r φ := φ.comp
    { toFun a := r.unop • a
      map_zero' := smul_zero _
      map_add' := smul_add _ }
  one_smul φ := AddMonoidHom.ext fun a ↦ congrArg φ (one_smul R a)
  mul_smul r s φ := AddMonoidHom.ext fun a ↦ by
    change φ ((r * s).unop • a) = φ (s.unop • r.unop • a)
    rw [MulOpposite.unop_mul, mul_smul]
  smul_zero _ := AddMonoidHom.ext fun _ ↦ rfl
  smul_add _ _ _ := AddMonoidHom.ext fun _ ↦ rfl
  add_smul r s φ := AddMonoidHom.ext fun a ↦ by
    change φ ((r + s).unop • a) = φ (r.unop • a) + φ (s.unop • a)
    rw [MulOpposite.unop_add, add_smul, map_add]
  zero_smul φ := AddMonoidHom.ext fun a ↦ by
    change φ ((0 : Rᵐᵒᵖ).unop • a) = 0
    rw [MulOpposite.unop_zero, zero_smul, map_zero]

/-- `(op r • φ)(a) = φ(r • a)`. -/
lemma addMonoidHomMulOppositeModule_smul_apply (r : Rᵐᵒᵖ) (φ : A →+ B) (a : A) :
    (r • φ) a = φ (r.unop • a) :=
  rfl

end InternalHomAction

open scoped InternalHomAction

/-! ### Finite stable submodules -/

section Orbit

variable (R : Type u) [Ring R] {Q : Type v} [Group Q] [TopologicalSpace Q]
  (V : Stacks.Injectives.ContinuousModule.{u, v, w} R Q)

/-- A submodule stable under `Q`. -/
def IsStableSubmodule (S : Submodule R V.obj.obj.V) : Prop :=
  ∀ (q : Q), ∀ s ∈ S, (V.obj.obj.ρ q).asHom.hom s ∈ S

/-- **The `R`-span of the orbit of `v`.** -/
def orbitSpan (v : V.obj.obj.V) : Submodule R V.obj.obj.V :=
  Submodule.span R (Set.range fun q : Q ↦ (V.obj.obj.ρ q).asHom.hom v)

/-- An element lies in the span of its orbit. -/
lemma mem_orbitSpan_self (v : V.obj.obj.V) : v ∈ orbitSpan R V v :=
  Submodule.subset_span ⟨1, continuousModuleRho_one_apply R V v⟩

/-- Equal additive maps on `orbitSpan v` agree at `v`. -/
private theorem congr_fun_orbitSpan {A : Type*} [AddZeroClass A] {v : V.obj.obj.V}
    {f g : orbitSpan R V v →+ A} (h : f = g) :
    f ⟨v, mem_orbitSpan_self R V v⟩ = g ⟨v, mem_orbitSpan_self R V v⟩ :=
  DFunLike.congr_fun h _

/-- The span of an orbit is stable under `Q`. -/
lemma isStableSubmodule_orbitSpan (v : V.obj.obj.V) :
    IsStableSubmodule R V (orbitSpan R V v) := by
  intro q s hs
  have hle : (orbitSpan R V v).map (V.obj.obj.ρ q).asHom.hom ≤ orbitSpan R V v := by
    rw [orbitSpan, Submodule.map_span_le]
    rintro _ ⟨q', rfl⟩
    exact Submodule.subset_span ⟨q * q', continuousModuleRho_mul_apply R V q q' v⟩
  exact hle ⟨s, hs, rfl⟩

/-- The span of the orbit of `v` lies in every `Q`-stable submodule containing `v`. -/
lemma orbitSpan_le {S : Submodule R V.obj.obj.V} (hS : IsStableSubmodule R V S)
    {v : V.obj.obj.V} (hv : v ∈ S) : orbitSpan R V v ≤ S := by
  rw [orbitSpan, Submodule.span_le]
  rintro _ ⟨q, rfl⟩
  exact hS q v hv

/-- The supremum of two `Q`-stable submodules is `Q`-stable. -/
lemma isStableSubmodule_sup {S T : Submodule R V.obj.obj.V} (hS : IsStableSubmodule R V S)
    (hT : IsStableSubmodule R V T) : IsStableSubmodule R V (S ⊔ T) := by
  intro q x hx
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact Submodule.add_mem_sup (hS q s hs) (hT q t ht)

variable [IsTopologicalGroup Q] [CompactSpace Q] [Finite R]

/-- The orbit span is finite: the orbit is finite, `Q` being compact, and `R` is finite. -/
instance finite_orbitSpan (v : V.obj.obj.V) : Finite (orbitSpan R V v) := by
  obtain ⟨U, hU⟩ := exists_mem_fixedSubmodule R V v
  haveI : Finite (Q ⧸ (U.toOpenSubgroup : Subgroup Q)) := inferInstance
  let f : Q ⧸ (U.toOpenSubgroup : Subgroup Q) → V.obj.obj.V := fun c ↦
    Quotient.liftOn' c (fun q ↦ (V.obj.obj.ρ q).asHom.hom v) fun a b hab ↦ by
      rw [QuotientGroup.leftRel_apply] at hab
      have hb : b = a * (a⁻¹ * b) := by group
      rw [hb, continuousModuleRho_mul_apply, hU _ hab]
  have hrange : (Set.range fun q : Q ↦ (V.obj.obj.ρ q).asHom.hom v) = Set.range f := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩; exact ⟨QuotientGroup.mk q, rfl⟩
    · rintro ⟨c, rfl⟩
      induction c using QuotientGroup.induction_on with
      | H q => exact ⟨q, rfl⟩
  have hfin : (Set.range fun q : Q ↦ (V.obj.obj.ρ q).asHom.hom v).Finite := by
    rw [hrange]; exact Set.finite_range f
  haveI : Module.Finite R (orbitSpan R V v) :=
    Module.Finite.iff_fg.mpr (Submodule.fg_span hfin)
  exact Module.finite_of_finite R

end Orbit

/-! ### `Hom_ℤ(S, W)` as a discrete module, for `S` finite -/

section Restricted

variable (R : Type u) [Ring R] {Q : Type v} [Group Q] [TopologicalSpace Q]
  (V : Stacks.Injectives.ContinuousModule.{u, v, w} R Q)
  (W : Stacks.Injectives.ContinuousModule.{0, v, w'} ℤ Q)

/-- `q⁻¹` acting on a stable submodule, as an `R`-linear map. -/
def stableRestrict {S : Submodule R V.obj.obj.V} (hS : IsStableSubmodule R V S) (q : Q) :
    S →ₗ[R] S :=
  LinearMap.restrict (V.obj.obj.ρ q).asHom.hom fun s hs ↦ hS q s hs

/-- Conjugation by `q` on `Hom_ℤ(S, W)`: `φ ↦ q · φ(q⁻¹ · -)`. -/
def restrictedHomConj {S : Submodule R V.obj.obj.V} (hS : IsStableSubmodule R V S) (q : Q) :
    (S →+ W.obj.obj.V) →ₗ[Rᵐᵒᵖ] (S →+ W.obj.obj.V) where
  toFun φ := (W.obj.obj.ρ q).asHom.hom.toAddMonoidHom.comp
    (φ.comp (stableRestrict R V hS q⁻¹).toAddMonoidHom)
  map_add' φ ψ := AddMonoidHom.ext fun s ↦
    map_add (W.obj.obj.ρ q).asHom.hom (φ (stableRestrict R V hS q⁻¹ s)) (ψ (stableRestrict R V hS q⁻¹ s))
  map_smul' r φ := AddMonoidHom.ext fun s ↦ by
    change (W.obj.obj.ρ q).asHom.hom (φ (r.unop • (stableRestrict R V hS q⁻¹ s))) =
      (W.obj.obj.ρ q).asHom.hom (φ (stableRestrict R V hS q⁻¹ (r.unop • s)))
    rw [LinearMap.map_smul]

/-- `(q · φ)(s) = q · φ(q⁻¹ · s)`. -/
lemma restrictedHomConj_apply {S : Submodule R V.obj.obj.V} (hS : IsStableSubmodule R V S)
    (q : Q) (φ : S →+ W.obj.obj.V) (s : S) :
    restrictedHomConj R V W hS q φ s =
      (W.obj.obj.ρ q).asHom.hom (φ ⟨(V.obj.obj.ρ q⁻¹).asHom.hom s, hS _ _ s.2⟩) :=
  rfl

/-- **The conjugation action of `Q` on `Hom_ℤ(S, W)`**: `(q · φ)(s) = q · φ(q⁻¹ · s)`. -/
def restrictedHomRep {S : Submodule R V.obj.obj.V} (hS : IsStableSubmodule R V S) :
    Representation Rᵐᵒᵖ Q (S →+ W.obj.obj.V) where
  toFun q := restrictedHomConj R V W hS q
  map_one' := by
    refine LinearMap.ext fun φ ↦ AddMonoidHom.ext fun s ↦ ?_
    change (W.obj.obj.ρ 1).asHom.hom (φ (stableRestrict R V hS 1⁻¹ s)) = φ s
    rw [continuousModuleRho_one_apply]
    congr 1
    apply Subtype.ext
    change (V.obj.obj.ρ 1⁻¹).asHom.hom s.1 = s.1
    rw [inv_one, continuousModuleRho_one_apply]
  map_mul' g h := by
    refine LinearMap.ext fun φ ↦ AddMonoidHom.ext fun s ↦ ?_
    change (W.obj.obj.ρ (g * h)).asHom.hom (φ (stableRestrict R V hS (g * h)⁻¹ s)) =
      (W.obj.obj.ρ g).asHom.hom ((W.obj.obj.ρ h).asHom.hom
        (φ (stableRestrict R V hS h⁻¹ (stableRestrict R V hS g⁻¹ s))))
    rw [continuousModuleRho_mul_apply]
    congr 3
    apply Subtype.ext
    change (V.obj.obj.ρ (g * h)⁻¹).asHom.hom s.1 = (V.obj.obj.ρ h⁻¹).asHom.hom ((V.obj.obj.ρ g⁻¹).asHom.hom s.1)
    rw [mul_inv_rev, continuousModuleRho_mul_apply]

/-- `(q · φ)(s) = q · φ(q⁻¹ · s)`. -/
lemma restrictedHomRep_apply {S : Submodule R V.obj.obj.V} (hS : IsStableSubmodule R V S)
    (q : Q) (φ : S →+ W.obj.obj.V) (s : S) :
    restrictedHomRep R V W hS q φ s =
      (W.obj.obj.ρ q).asHom.hom (φ ⟨(V.obj.obj.ρ q⁻¹).asHom.hom s, hS _ _ s.2⟩) :=
  restrictedHomConj_apply R V W hS q φ s

open scoped Stacks.DiscreteModuleTopology in
/-- **The conjugation action on `Hom_ℤ(S, W)` is continuous for `S` finite**: a map is fixed by
any element fixing the finitely many points of `S` and their images. -/
lemma isContinuous_restrictedHomRep [IsTopologicalGroup Q] {S : Submodule R V.obj.obj.V}
    (hS : IsStableSubmodule R V S) [Finite S] :
    (Stacks.GroupCohomology.actionOfRepresentation Rᵐᵒᵖ Q (S →+ W.obj.obj.V)
      (restrictedHomRep R V W hS)).IsContinuous := by
  rw [Stacks.GroupCohomology.isContinuous_actionOfRepresentation_iff]
  intro φ
  let H : Subgroup Q :=
    { carrier := {q | restrictedHomRep R V W hS q φ = φ}
      mul_mem' := fun {a b} ha hb ↦ by
        change restrictedHomRep R V W hS (a * b) φ = φ
        rw [map_mul, Module.End.mul_apply, show restrictedHomRep R V W hS b φ = φ from hb, ha]
      one_mem' := by
        change restrictedHomRep R V W hS 1 φ = φ
        rw [map_one]; rfl
      inv_mem' := fun {a} ha ↦ by
        change restrictedHomRep R V W hS a⁻¹ φ = φ
        conv_lhs => rw [← (show restrictedHomRep R V W hS a φ = φ from ha)]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
  change IsOpen (H : Set Q)
  let O : Set Q := ⋂ s : S, ({q | (V.obj.obj.ρ q).asHom.hom s = s} ∩
    {q | (W.obj.obj.ρ q).asHom.hom (φ s) = φ s})
  have hO : IsOpen O := isOpen_iInter_of_finite fun s ↦
    (Stacks.GroupCohomology.isOpen_stabilizer R Q V s).inter
      (Stacks.GroupCohomology.isOpen_stabilizer ℤ Q W (φ s))
  have h1 : (1 : Q) ∈ O := Set.mem_iInter.mpr fun s ↦
    ⟨continuousModuleRho_one_apply R V s, continuousModuleRho_one_apply ℤ W (φ s)⟩
  refine Subgroup.isOpen_of_mem_nhds H (Filter.mem_of_superset (hO.mem_nhds h1) ?_)
  intro q hq
  have hq' := Set.mem_iInter.mp hq
  change restrictedHomRep R V W hS q φ = φ
  ext s
  rw [restrictedHomRep_apply]
  have hinv : (V.obj.obj.ρ q⁻¹).asHom.hom s = s := by
    conv_lhs => rw [← (hq' s).1]
    rw [← continuousModuleRho_mul_apply, inv_mul_cancel, continuousModuleRho_one_apply]
  have hs : (⟨(V.obj.obj.ρ q⁻¹).asHom.hom s, hS _ _ s.2⟩ : S) = s := Subtype.ext hinv
  rw [hs]
  exact (hq' s).2

variable [IsTopologicalGroup Q]

/-- **`Hom_ℤ(S, W)` as a discrete `Rᵐᵒᵖ`-`Q`-module**, for `S` finite and `Q`-stable. -/
def restrictedHomObj {S : Submodule R V.obj.obj.V} (hS : IsStableSubmodule R V S) [Finite S] :
    Stacks.Injectives.ContinuousModule.{u, v, max w w'} Rᵐᵒᵖ Q :=
  Stacks.GroupCohomology.ofRepresentation (restrictedHomRep R V W hS)
    (isContinuous_restrictedHomRep R V W hS)

/-- A morphism of discrete modules from an `Rᵐᵒᵖ`-linear `Q`-equivariant map. -/
def restrictedHomMk {S : Submodule R V.obj.obj.V} (hS : IsStableSubmodule R V S) [Finite S]
    {V' : Stacks.Injectives.ContinuousModule.{u, v, w} R Q}
    {W' : Stacks.Injectives.ContinuousModule.{0, v, w'} ℤ Q}
    {S' : Submodule R V'.obj.obj.V} (hS' : IsStableSubmodule R V' S') [Finite S']
    (f : (S →+ W.obj.obj.V) →ₗ[Rᵐᵒᵖ] (S' →+ W'.obj.obj.V))
    (hf : ∀ (q : Q) (φ : S →+ W.obj.obj.V),
      f (restrictedHomRep R V W hS q φ) = restrictedHomRep R V' W' hS' q (f φ)) :
    restrictedHomObj R V W hS ⟶ restrictedHomObj R V' W' hS' :=
  (Stacks.GroupCohomology.homEquiv Rᵐᵒᵖ Q _ _).symm ⟨f, hf⟩

end Restricted

/-! ### The action of `Rᵐᵒᵖ[[Q]]` on `Hom_ℤ(V, W)` -/

section Action

variable (R : Type u) [Ring R] [Finite R] {Q : Type v} [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q]
  (V : Stacks.Injectives.ContinuousModule.{u, v, w} R Q)
  (W : Stacks.Injectives.ContinuousModule.{0, v, w'} ℤ Q)

/-- The restriction `Hom_ℤ(S, W) → Hom_ℤ(T, W)` along an inclusion of stable submodules, as a
morphism of discrete modules. -/
def restrictedHomRestrict {S T : Submodule R V.obj.obj.V} (hS : IsStableSubmodule R V S)
    (hT : IsStableSubmodule R V T) [Finite S] [Finite T] (h : T ≤ S) :
    restrictedHomObj R V W hS ⟶ restrictedHomObj R V W hT :=
  restrictedHomMk R V W hS hT
    { toFun φ := φ.comp (Submodule.inclusion h).toAddMonoidHom
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    fun _ _ ↦ rfl

/-- The `Rᵐᵒᵖ[[Q]]`-action on a restriction. -/
def restrictedSMul {S : Submodule R V.obj.obj.V} (hS : IsStableSubmodule R V S) [Finite S]
    (x : CompletedGroupAlgebra Rᵐᵒᵖ Q) (φ : S →+ W.obj.obj.V) : S →+ W.obj.obj.V :=
  discreteSMul Rᵐᵒᵖ (restrictedHomObj R V W hS) x φ

section Axioms

variable {S : Submodule R V.obj.obj.V} (hS : IsStableSubmodule R V S) [Finite S]

omit [Finite R] in
/-- The unit of `Rᵐᵒᵖ[[Q]]` acts trivially on `Hom_ℤ(S, W)`. -/
lemma restrictedSMul_one (φ : S →+ W.obj.obj.V) : restrictedSMul R V W hS 1 φ = φ :=
  discreteSMul_one Rᵐᵒᵖ (restrictedHomObj R V W hS) φ

omit [Finite R] in
/-- `(x * y) • φ = x • (y • φ)` on `Hom_ℤ(S, W)`. -/
lemma restrictedSMul_mul (x y : CompletedGroupAlgebra Rᵐᵒᵖ Q) (φ : S →+ W.obj.obj.V) :
    restrictedSMul R V W hS (x * y) φ =
      restrictedSMul R V W hS x (restrictedSMul R V W hS y φ) :=
  discreteSMul_mul Rᵐᵒᵖ (restrictedHomObj R V W hS) x y φ

omit [Finite R] in
/-- `(x + y) • φ = x • φ + y • φ` on `Hom_ℤ(S, W)`. -/
lemma restrictedSMul_add_left (x y : CompletedGroupAlgebra Rᵐᵒᵖ Q) (φ : S →+ W.obj.obj.V) :
    restrictedSMul R V W hS (x + y) φ = restrictedSMul R V W hS x φ + restrictedSMul R V W hS y φ :=
  discreteSMul_add_left Rᵐᵒᵖ (restrictedHomObj R V W hS) x y φ

omit [Finite R] in
/-- `0 • φ = 0` on `Hom_ℤ(S, W)`. -/
lemma restrictedSMul_zero_left (φ : S →+ W.obj.obj.V) : restrictedSMul R V W hS 0 φ = 0 :=
  discreteSMul_zero_left Rᵐᵒᵖ (restrictedHomObj R V W hS) φ

omit [Finite R] in
/-- `x • (φ + ψ) = x • φ + x • ψ` on `Hom_ℤ(S, W)`. -/
lemma restrictedSMul_add_right (x : CompletedGroupAlgebra Rᵐᵒᵖ Q) (φ ψ : S →+ W.obj.obj.V) :
    restrictedSMul R V W hS x (φ + ψ) = restrictedSMul R V W hS x φ + restrictedSMul R V W hS x ψ :=
  discreteSMul_add_right Rᵐᵒᵖ (restrictedHomObj R V W hS) x φ ψ

omit [Finite R] in
/-- `x • 0 = 0` on `Hom_ℤ(S, W)`. -/
lemma restrictedSMul_zero_right (x : CompletedGroupAlgebra Rᵐᵒᵖ Q) :
    restrictedSMul R V W hS x (0 : S →+ W.obj.obj.V) = 0 :=
  discreteSMul_zero_right Rᵐᵒᵖ (restrictedHomObj R V W hS) x

omit [Finite R] in
/-- The group element `q ∈ Rᵐᵒᵖ[[Q]]` acts on `Hom_ℤ(S, W)` by conjugation. -/
lemma restrictedSMul_of (q : Q) (φ : S →+ W.obj.obj.V) :
    restrictedSMul R V W hS (CompletedGroupAlgebra.of q) φ = restrictedHomRep R V W hS q φ :=
  discreteSMul_of Rᵐᵒᵖ (restrictedHomObj R V W hS) q φ

omit [Finite R] in
/-- The constant `r ∈ Rᵐᵒᵖ[[Q]]` acts on `Hom_ℤ(S, W)` through its `Rᵐᵒᵖ`-module structure. -/
lemma restrictedSMul_const (r : Rᵐᵒᵖ) (φ : S →+ W.obj.obj.V) :
    restrictedSMul R V W hS (CompletedGroupAlgebra.const r) φ = r • φ :=
  discreteSMul_const Rᵐᵒᵖ (restrictedHomObj R V W hS) r φ

end Axioms

omit [Finite R] in
/-- The action of `Rᵐᵒᵖ[[Q]]` commutes with restriction `Hom_ℤ(S, W) → Hom_ℤ(T, W)` along an
inclusion `T ≤ S` of finite `Q`-stable submodules. -/
lemma restrictedSMul_restrict {S T : Submodule R V.obj.obj.V} (hS : IsStableSubmodule R V S)
    (hT : IsStableSubmodule R V T) [Finite S] [Finite T] (h : T ≤ S)
    (x : CompletedGroupAlgebra Rᵐᵒᵖ Q) (φ : S →+ W.obj.obj.V) :
    (restrictedSMul R V W hS x φ).comp (Submodule.inclusion h).toAddMonoidHom =
      restrictedSMul R V W hT x (φ.comp (Submodule.inclusion h).toAddMonoidHom) :=
  discreteSMul_map Rᵐᵒᵖ Q (restrictedHomRestrict R V W hS hT h) x φ

/-- **The action of `x ∈ Rᵐᵒᵖ[[Q]]` on `φ ∈ Hom_ℤ(V, W)`**, at `v`: through the discrete module
`Hom_ℤ(S, W)` for `S` the span of the orbit of `v`. -/
def internalHomSMulFun (x : CompletedGroupAlgebra Rᵐᵒᵖ Q) (φ : V.obj.obj.V →+ W.obj.obj.V)
    (v : V.obj.obj.V) : W.obj.obj.V :=
  restrictedSMul R V W (isStableSubmodule_orbitSpan R V v) x
    (φ.comp (orbitSpan R V v).subtype.toAddMonoidHom) ⟨v, mem_orbitSpan_self R V v⟩

/-- **The action at `v` is computed on any finite stable submodule containing `v`.** -/
theorem internalHomSMulFun_eq_of_mem {S : Submodule R V.obj.obj.V}
    (hS : IsStableSubmodule R V S) [Finite S] (x : CompletedGroupAlgebra Rᵐᵒᵖ Q)
    (φ : V.obj.obj.V →+ W.obj.obj.V) {v : V.obj.obj.V} (hv : v ∈ S) :
    internalHomSMulFun R V W x φ v =
      restrictedSMul R V W hS x (φ.comp S.subtype.toAddMonoidHom) ⟨v, hv⟩ :=
  (congr_fun_orbitSpan R V (restrictedSMul_restrict R V W hS (isStableSubmodule_orbitSpan R V v)
    (orbitSpan_le R V hS hv) x (φ.comp S.subtype.toAddMonoidHom))).symm

/-- `x • φ` as an additive map. -/
def internalHomSMul (x : CompletedGroupAlgebra Rᵐᵒᵖ Q) (φ : V.obj.obj.V →+ W.obj.obj.V) :
    V.obj.obj.V →+ W.obj.obj.V where
  toFun := internalHomSMulFun R V W x φ
  map_zero' := by
    rw [internalHomSMulFun_eq_of_mem R V W (isStableSubmodule_orbitSpan R V 0) x φ
      (Submodule.zero_mem _)]
    exact map_zero (restrictedSMul R V W (isStableSubmodule_orbitSpan R V 0) x
      (φ.comp (orbitSpan R V 0).subtype.toAddMonoidHom))
  map_add' v v' := by
    let S := orbitSpan R V v ⊔ orbitSpan R V v'
    have hS : IsStableSubmodule R V S := isStableSubmodule_sup R V
      (isStableSubmodule_orbitSpan R V v) (isStableSubmodule_orbitSpan R V v')
    haveI : Finite S := by
      haveI : Module.Finite R (orbitSpan R V v) := Module.Finite.of_finite
      haveI : Module.Finite R (orbitSpan R V v') := Module.Finite.of_finite
      exact Module.finite_of_finite R
    have hv : v ∈ S := Submodule.mem_sup_left (mem_orbitSpan_self R V v)
    have hv' : v' ∈ S := Submodule.mem_sup_right (mem_orbitSpan_self R V v')
    rw [internalHomSMulFun_eq_of_mem R V W hS x φ (S.add_mem hv hv'),
      internalHomSMulFun_eq_of_mem R V W hS x φ hv, internalHomSMulFun_eq_of_mem R V W hS x φ hv']
    exact map_add (restrictedSMul R V W hS x (φ.comp S.subtype.toAddMonoidHom)) ⟨v, hv⟩ ⟨v', hv'⟩

/-- The restriction of `x • φ` to a finite `Q`-stable submodule `S` is `x` acting on the
restriction of `φ` in `Hom_ℤ(S, W)`. -/
lemma internalHomSMul_comp_subtype {S : Submodule R V.obj.obj.V}
    (hS : IsStableSubmodule R V S) [Finite S] (x : CompletedGroupAlgebra Rᵐᵒᵖ Q)
    (φ : V.obj.obj.V →+ W.obj.obj.V) :
    (internalHomSMul R V W x φ).comp S.subtype.toAddMonoidHom =
      restrictedSMul R V W hS x (φ.comp S.subtype.toAddMonoidHom) :=
  AddMonoidHom.ext fun s ↦ internalHomSMulFun_eq_of_mem R V W hS x φ s.2

/-- **The `Rᵐᵒᵖ[[Q]]`-module structure of `Hom_ℤ(V, W)`.** -/
@[instance_reducible]
def internalHomModule : Module (CompletedGroupAlgebra Rᵐᵒᵖ Q) (V.obj.obj.V →+ W.obj.obj.V) where
  smul := internalHomSMul R V W
  one_smul φ := AddMonoidHom.ext fun v ↦
    DFunLike.congr_fun (restrictedSMul_one R V W (isStableSubmodule_orbitSpan R V v)
      (φ.comp (orbitSpan R V v).subtype.toAddMonoidHom)) ⟨v, mem_orbitSpan_self R V v⟩
  mul_smul x y φ := AddMonoidHom.ext fun v ↦
    (DFunLike.congr_fun (restrictedSMul_mul R V W (isStableSubmodule_orbitSpan R V v) x y
      (φ.comp (orbitSpan R V v).subtype.toAddMonoidHom)) ⟨v, mem_orbitSpan_self R V v⟩).trans
      (congrArg (fun ψ ↦ restrictedSMul R V W (isStableSubmodule_orbitSpan R V v) x ψ
          ⟨v, mem_orbitSpan_self R V v⟩)
        (internalHomSMul_comp_subtype R V W (isStableSubmodule_orbitSpan R V v) y φ).symm)
  smul_zero x := AddMonoidHom.ext fun v ↦
    DFunLike.congr_fun (restrictedSMul_zero_right R V W (isStableSubmodule_orbitSpan R V v) x)
      ⟨v, mem_orbitSpan_self R V v⟩
  smul_add x φ ψ := AddMonoidHom.ext fun v ↦
    DFunLike.congr_fun (restrictedSMul_add_right R V W (isStableSubmodule_orbitSpan R V v) x
      (φ.comp (orbitSpan R V v).subtype.toAddMonoidHom)
      (ψ.comp (orbitSpan R V v).subtype.toAddMonoidHom)) ⟨v, mem_orbitSpan_self R V v⟩
  add_smul x y φ := AddMonoidHom.ext fun v ↦
    DFunLike.congr_fun (restrictedSMul_add_left R V W (isStableSubmodule_orbitSpan R V v) x y
      (φ.comp (orbitSpan R V v).subtype.toAddMonoidHom)) ⟨v, mem_orbitSpan_self R V v⟩
  zero_smul φ := AddMonoidHom.ext fun v ↦
    DFunLike.congr_fun (restrictedSMul_zero_left R V W (isStableSubmodule_orbitSpan R V v)
      (φ.comp (orbitSpan R V v).subtype.toAddMonoidHom)) ⟨v, mem_orbitSpan_self R V v⟩

/-- **`(x • φ)(v)` is computed on any finite stable submodule `S ∋ v`**, through the discrete
module `Hom_ℤ(S, W)`. -/
theorem internalHom_smul_apply_of_mem {S : Submodule R V.obj.obj.V}
    (hS : IsStableSubmodule R V S) [Finite S] (x : CompletedGroupAlgebra Rᵐᵒᵖ Q)
    (φ : V.obj.obj.V →+ W.obj.obj.V) {v : V.obj.obj.V} (hv : v ∈ S) :
    (letI := internalHomModule R V W; x • φ) v =
      restrictedSMul R V W hS x (φ.comp S.subtype.toAddMonoidHom) ⟨v, hv⟩ :=
  internalHomSMulFun_eq_of_mem R V W hS x φ hv

/-- **A group element acts by conjugation**: `(q • φ)(v) = q · φ(q⁻¹ · v)`. -/
theorem internalHom_of_smul_apply (q : Q) (φ : V.obj.obj.V →+ W.obj.obj.V) (v : V.obj.obj.V) :
    (letI := internalHomModule R V W; CompletedGroupAlgebra.of (Λ := Rᵐᵒᵖ) q • φ) v =
      (W.obj.obj.ρ q).asHom.hom (φ ((V.obj.obj.ρ q⁻¹).asHom.hom v)) :=
  congr_fun_orbitSpan R V (restrictedSMul_of R V W (isStableSubmodule_orbitSpan R V v) q
    (φ.comp (orbitSpan R V v).subtype.toAddMonoidHom))

/-- **A constant acts through the source**: `(op r • φ)(v) = φ(r • v)`. -/
theorem internalHom_const_op_smul_apply (r : R) (φ : V.obj.obj.V →+ W.obj.obj.V)
    (v : V.obj.obj.V) :
    (letI := internalHomModule R V W;
      CompletedGroupAlgebra.const (G := Q) (MulOpposite.op r) • φ) v =
      φ (r • v) :=
  congr_fun_orbitSpan R V (restrictedSMul_const R V W (isStableSubmodule_orbitSpan R V v)
    (MulOpposite.op r)
    (φ.comp (orbitSpan R V v).subtype.toAddMonoidHom))

end Action

/-! ### Functoriality -/

section Functor

variable (R : Type u) [Ring R] [Finite R] (Q : Type v) [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q]

/-- `Hom_ℤ(V, W)` as an `Rᵐᵒᵖ[[Q]]`-module. -/
def internalHomObj (V : Stacks.Injectives.ContinuousModule.{u, v, w} R Q)
    (W : Stacks.Injectives.ContinuousModule.{0, v, w'} ℤ Q) :
    ModuleCat.{max w w'} (CompletedGroupAlgebra Rᵐᵒᵖ Q) :=
  letI := internalHomModule R V W
  ModuleCat.of _ (V.obj.obj.V →+ W.obj.obj.V)

/-- **Postcomposition with an equivariant additive map `W → W'` commutes with the action**, for
`W` and `W'` in any two universes. -/
lemma internalHom_postcomp_smul_of_addMonoidHom
    (V : Stacks.Injectives.ContinuousModule.{u, v, w} R Q)
    {W : Stacks.Injectives.ContinuousModule.{0, v, w'} ℤ Q}
    {W' : Stacks.Injectives.ContinuousModule.{0, v, w''} ℤ Q} (g : W.obj.obj.V →+ W'.obj.obj.V)
    (hg : ∀ (q : Q) (a : W.obj.obj.V), g ((W.obj.obj.ρ q).asHom.hom a) = (W'.obj.obj.ρ q).asHom.hom (g a))
    (x : CompletedGroupAlgebra Rᵐᵒᵖ Q) (φ : V.obj.obj.V →+ W.obj.obj.V) :
    g.comp (internalHomSMul R V W x φ) = internalHomSMul R V W' x (g.comp φ) := by
  refine AddMonoidHom.ext fun v ↦ ?_
  have hS := isStableSubmodule_orbitSpan R V v
  let post : (orbitSpan R V v →+ W.obj.obj.V) →ₗ[Rᵐᵒᵖ] (orbitSpan R V v →+ W'.obj.obj.V) :=
    { toFun ψ := g.comp ψ
      map_add' _ _ := AddMonoidHom.comp_add _ _ _
      map_smul' _ _ := rfl }
  exact congr_fun_orbitSpan R V (show (g.comp
      (restrictedSMul R V W hS x (φ.comp (orbitSpan R V v).subtype.toAddMonoidHom)) :
        orbitSpan R V v →+ W'.obj.obj.V) = restrictedSMul R V W' hS x
      (g.comp (φ.comp (orbitSpan R V v).subtype.toAddMonoidHom))
    from discreteSMul_map_linear Rᵐᵒᵖ Q (N := restrictedHomObj R V W hS)
      (N' := restrictedHomObj R V W' hS) post
      (fun q (ψ : orbitSpan R V v →+ W.obj.obj.V) ↦ AddMonoidHom.ext fun s ↦
        hg q (ψ ⟨(V.obj.obj.ρ q⁻¹).asHom.hom s, hS _ _ s.2⟩)) x _)

/-- Postcomposition with a morphism `W ⟶ W'` commutes with the action. -/
lemma internalHom_postcomp_smul (V : Stacks.Injectives.ContinuousModule.{u, v, w} R Q)
    {W W' : Stacks.Injectives.ContinuousModule.{0, v, w'} ℤ Q} (g : W ⟶ W')
    (x : CompletedGroupAlgebra Rᵐᵒᵖ Q) (φ : V.obj.obj.V →+ W.obj.obj.V) :
    g.hom.hom.hom.hom.toAddMonoidHom.comp (internalHomSMul R V W x φ) =
      internalHomSMul R V W' x (g.hom.hom.hom.hom.toAddMonoidHom.comp φ) :=
  internalHom_postcomp_smul_of_addMonoidHom R Q V g.hom.hom.hom.hom.toAddMonoidHom
    (fun q a ↦ ConcreteCategory.congr_hom (g.hom.hom.comm q) a) x φ

omit [Finite R] [IsTopologicalGroup Q] [CompactSpace Q] in
/-- The image of the orbit span under a morphism lies in the orbit span of the image. -/
lemma map_orbitSpan_le {V V' : Stacks.Injectives.ContinuousModule.{u, v, w} R Q} (f : V ⟶ V')
    (v : V.obj.obj.V) :
    (orbitSpan R V v).map f.hom.hom.hom.hom ≤ orbitSpan R V' (f.hom.hom.hom.hom v) := by
  rw [orbitSpan, Submodule.map_span_le]
  rintro _ ⟨q, rfl⟩
  exact Submodule.subset_span ⟨q, (ConcreteCategory.congr_hom (f.hom.hom.comm q) v).symm⟩

/-- Precomposition with a morphism `V ⟶ V'` commutes with the action. -/
lemma internalHom_precomp_smul {V V' : Stacks.Injectives.ContinuousModule.{u, v, w} R Q}
    (f : V ⟶ V') (W : Stacks.Injectives.ContinuousModule.{0, v, w'} ℤ Q)
    (x : CompletedGroupAlgebra Rᵐᵒᵖ Q) (φ : V'.obj.obj.V →+ W.obj.obj.V) :
    (internalHomSMul R V' W x φ).comp f.hom.hom.hom.hom.toAddMonoidHom =
      internalHomSMul R V W x (φ.comp f.hom.hom.hom.hom.toAddMonoidHom) := by
  refine AddMonoidHom.ext fun v ↦ ?_
  have hS := isStableSubmodule_orbitSpan R V v
  have hS' := isStableSubmodule_orbitSpan R V' (f.hom.hom.hom.hom v)
  let fS : orbitSpan R V v →ₗ[R] orbitSpan R V' (f.hom.hom.hom.hom v) :=
    (f.hom.hom.hom.hom.domRestrict _).codRestrict _ fun s ↦
      map_orbitSpan_le R Q f v ⟨s.1, s.2, rfl⟩
  let pre : restrictedHomObj R V' W hS' ⟶ restrictedHomObj R V W hS :=
    restrictedHomMk R V' W hS' hS
      { toFun ψ := ψ.comp fS.toAddMonoidHom
        map_add' _ _ := rfl
        map_smul' r ψ := AddMonoidHom.ext fun s ↦ by
          change ψ (r.unop • fS s) = ψ (fS (r.unop • s))
          rw [LinearMap.map_smul] }
      fun q ψ ↦ AddMonoidHom.ext fun s ↦ by
        change (W.obj.obj.ρ q).asHom.hom (ψ (stableRestrict R V' hS' q⁻¹ (fS s))) =
          (W.obj.obj.ρ q).asHom.hom (ψ (fS (stableRestrict R V hS q⁻¹ s)))
        congr 2
        exact Subtype.ext (ConcreteCategory.congr_hom (f.hom.hom.comm q⁻¹) s.1).symm
  exact congr_fun_orbitSpan R V (show ((restrictedSMul R V' W hS' x
      (φ.comp (orbitSpan R V' (f.hom.hom.hom.hom v)).subtype.toAddMonoidHom)).comp
        fS.toAddMonoidHom : orbitSpan R V v →+ W.obj.obj.V) = restrictedSMul R V W hS x
      ((φ.comp (orbitSpan R V' (f.hom.hom.hom.hom v)).subtype.toAddMonoidHom).comp
        fS.toAddMonoidHom)
    from discreteSMul_map Rᵐᵒᵖ Q pre x _)

/-- **The internal hom `(V, W) ↦ Hom_ℤ(V, W)`**, contravariant in the discrete `R`-`Q`-module
`V` and covariant in the discrete `ℤ`-`Q`-module `W`, valued in `Rᵐᵒᵖ[[Q]]`-modules. -/
def internalHom :
    (Stacks.Injectives.ContinuousModule.{u, v, w} R Q)ᵒᵖ ⥤
      Stacks.Injectives.ContinuousModule.{0, v, w'} ℤ Q ⥤
        ModuleCat.{max w w'} (CompletedGroupAlgebra Rᵐᵒᵖ Q) where
  obj V :=
    { obj W := internalHomObj R Q V.unop W
      map {W W'} g :=
        letI := internalHomModule R V.unop W
        letI := internalHomModule R V.unop W'
        ModuleCat.ofHom
          { toFun φ := g.hom.hom.hom.hom.toAddMonoidHom.comp φ
            map_add' _ _ := AddMonoidHom.comp_add _ _ _
            map_smul' x φ := internalHom_postcomp_smul R Q V.unop g x φ }
      map_id _ := rfl
      map_comp _ _ := rfl }
  map {V V'} f :=
    { app W :=
        letI := internalHomModule R V.unop W
        letI := internalHomModule R V'.unop W
        ModuleCat.ofHom
          { toFun φ := φ.comp f.unop.hom.hom.hom.hom.toAddMonoidHom
            map_add' _ _ := rfl
            map_smul' x φ := internalHom_precomp_smul R Q f.unop W x φ }
      naturality _ _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

end Functor

/-! ### The contragredient `V ↦ V^∨ = Hom(V, ℚ/ℤ)` -/

section Contragredient

variable (R : Type u) [Ring R] [Finite R] (Q : Type v) [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q]

open scoped Stacks.DiscreteModuleTopology in
/-- **`ℚ/ℤ` with the trivial action of `Q`**, as a discrete `ℤ`-`Q`-module. -/
def trivialRatCircle : Stacks.Injectives.ContinuousModule.{0, v, 0} ℤ Q :=
  Stacks.GroupCohomology.ofRepresentation (Representation.trivial ℤ Q (AddCircle (1 : ℚ)))
    ((Stacks.GroupCohomology.isContinuous_actionOfRepresentation_iff _).mpr fun _ ↦ by
      simp only [Representation.trivial_apply, Set.ofPred_true, isOpen_univ])

variable [CompactSpace Q]

/-- **The contragredient `V ↦ V^∨ = Hom_ℤ(V, ℚ/ℤ)`** of discrete `R`-`Q`-modules, valued in
`Rᵐᵒᵖ[[Q]]`-modules: `(q · χ)(v) = χ(q⁻¹ v)` and `(op r · χ)(v) = χ(r v)`. Its carrier is the
character module `CharacterModule V`. -/
def contragredient :
    (Stacks.Injectives.ContinuousModule.{u, v, w} R Q)ᵒᵖ ⥤
      ModuleCat.{w} (CompletedGroupAlgebra Rᵐᵒᵖ Q) :=
  (internalHom.{u, v, w, 0} R Q).flip.obj (trivialRatCircle Q)

open scoped Stacks.DiscreteModuleTopology in
/-- **`ℚ/ℤ` with the trivial action, in the module universe `w`**: `ULift (AddCircle 1)`. -/
def trivialRatCircleULift : Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q :=
  Stacks.GroupCohomology.ofRepresentation
    (Representation.trivial ℤ Q (ULift.{w} (AddCircle (1 : ℚ))))
    ((Stacks.GroupCohomology.isContinuous_actionOfRepresentation_iff _).mpr fun _ ↦ by
      simp only [Representation.trivial_apply, Set.ofPred_true, isOpen_univ])

/-- **The contragredient computed with `ℚ/ℤ` lifted to the module universe**:
`Hom(V, ℚ/ℤ) ≅ Hom(V, ULift (ℚ/ℤ))` by `φ ↦ ULift.up ∘ φ`, naturally in `V`. -/
def contragredientULiftIso :
    contragredient.{u, v, w} R Q ≅ (internalHom.{u, v, w, w} R Q).flip.obj
      (trivialRatCircleULift.{v, w} Q) :=
  NatIso.ofComponents
    (fun V ↦
      letI := internalHomModule R V.unop (trivialRatCircle Q)
      letI := internalHomModule R V.unop (trivialRatCircleULift.{v, w} Q)
      LinearEquiv.toModuleIso
        { toFun φ := (AddEquiv.ulift.{0, w} (α := AddCircle (1 : ℚ))).symm.toAddMonoidHom.comp φ
          invFun ψ := (AddEquiv.ulift.{0, w} (α := AddCircle (1 : ℚ))).toAddMonoidHom.comp ψ
          map_add' _ _ := AddMonoidHom.comp_add _ _ _
          map_smul' x φ := internalHom_postcomp_smul_of_addMonoidHom R Q V.unop
            (W := trivialRatCircle Q) (W' := trivialRatCircleULift.{v, w} Q)
            (AddEquiv.ulift.{0, w} (α := AddCircle (1 : ℚ))).symm.toAddMonoidHom
            (fun _ _ ↦ rfl) x φ
          left_inv _ := rfl
          right_inv _ := rfl })
    (fun _ ↦ rfl)

/-- The contragredient is additive. -/
instance contragredient_additive : (contragredient.{u, v, w} R Q).Additive where
  map_add {X _ f g} := by
    apply ModuleCat.hom_ext; apply LinearMap.ext
    intro (χ : X.unop.obj.obj.V →+ AddCircle (1 : ℚ))
    exact AddMonoidHom.ext fun v ↦ map_add χ (f.unop.hom.hom.hom.hom v) (g.unop.hom.hom.hom.hom v)

/-- **The contragredient is exact**, `ℚ/ℤ` being an injective abelian group. -/
theorem preservesHomology_contragredient : (contragredient.{u, v, w} R Q).PreservesHomology := by
  refine ((Functor.exact_tfae (contragredient.{u, v, w} R Q)).out 2 3).mp fun S hS ↦ ?_
  have := Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat.{u, v, w} R Q
  have := Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat.{u, v, w} R Q
  have : (Stacks.Injectives.continuousModuleUnderlying.{u, v, w} R Q).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hU : (S.unop.map (Stacks.Injectives.continuousModuleUnderlying.{u, v, w} R Q)).Exact :=
    hS.unop.map _
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hU ⊢
  exact CharacterModule.exact_dual_of_exact (R := ℤ)
    (S.g.unop.hom.hom.hom.hom.toAddMonoidHom.toIntLinearMap)
    (S.f.unop.hom.hom.hom.hom.toAddMonoidHom.toIntLinearMap) hU

/-- The contragredient preserves finite limits. -/
instance preservesFiniteLimits_contragredient :
    PreservesFiniteLimits (contragredient.{u, v, w} R Q) :=
  have := preservesHomology_contragredient.{u, v, w} R Q
  Functor.preservesFiniteLimits_of_preservesHomology _

/-- The contragredient preserves finite colimits. -/
instance preservesFiniteColimits_contragredient :
    PreservesFiniteColimits (contragredient.{u, v, w} R Q) :=
  have := preservesHomology_contragredient.{u, v, w} R Q
  Functor.preservesFiniteColimits_of_preservesHomology _

attribute [local instance] HasDerivedCategory.standard

/-- **The derived contragredient** `D(Mod_{R,Q})ᵒᵖ ⥤ D(Rᵐᵒᵖ[[Q]])`: the duality
`D(𝒜)ᵒᵖ ≌ D(𝒜ᵒᵖ)` followed by the exact contragredient applied to complexes. -/
def derivedContragredient :
    (DerivedCategory (Stacks.Injectives.ContinuousModule.{u, v, w} R Q))ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{w} (CompletedGroupAlgebra Rᵐᵒᵖ Q)) :=
  (DerivedCategory.derivedOpEquivalence
      (C := Stacks.Injectives.ContinuousModule.{u, v, w} R Q)).functor ⋙
    (contragredient.{u, v, w} R Q).mapDerivedCategory

/-- **The cohomology of the derived contragredient**: `H^m(K^∨) ≅ (H^n K)^∨` for `m + n = 0`,
naturally in `K`. -/
def derivedContragredientHomologyIso (m n : ℤ) (hmn : m + n = 0) :
    derivedContragredient.{u, v, w} R Q ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{w} (CompletedGroupAlgebra Rᵐᵒᵖ Q)) m ≅
      (DerivedCategory.homologyFunctor
        (Stacks.Injectives.ContinuousModule.{u, v, w} R Q) n).op ⋙
        contragredient.{u, v, w} R Q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.derivedOpEquivalence
        (C := Stacks.Injectives.ContinuousModule.{u, v, w} R Q)).functor
      ((contragredient.{u, v, w} R Q).mapDerivedCategoryHomologyFunctorIso m) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.derivedHomologyOpNatIso' m n hmn)
      (contragredient.{u, v, w} R Q)

/-- **The derived contragredient of a complex** is the contragredient of the complex read
backwards: `(Q E)^∨ ≅ Q(E^∨)`, where `E^∨` is `contragredient` applied termwise to the cochain
complex of `(Mod_{R,Q})ᵒᵖ` obtained from `E` by `CochainComplex.opEquivalence`. -/
def derivedContragredientQIso
    (E : CochainComplex (Stacks.Injectives.ContinuousModule.{u, v, w} R Q) ℤ) :
    (derivedContragredient.{u, v, w} R Q).obj (Opposite.op (DerivedCategory.Q.obj E)) ≅
      DerivedCategory.Q.obj (((contragredient.{u, v, w} R Q).mapHomologicalComplex _).obj
        ((CochainComplex.opEquivalence
          (Stacks.Injectives.ContinuousModule.{u, v, w} R Q)).functor.obj (Opposite.op E))) :=
  (contragredient.{u, v, w} R Q).mapDerivedCategory.mapIso
      ((DerivedCategory.derivedOpEquivalence
          (C := Stacks.Injectives.ContinuousModule.{u, v, w} R Q)).functor.mapIso
        ((DerivedCategory.Q (C := Stacks.Injectives.ContinuousModule.{u, v, w} R Q)).op.mapIso
          ((CochainComplex.opEquivalence
            (Stacks.Injectives.ContinuousModule.{u, v, w} R Q)).unitIso.app (Opposite.op E))) ≪≫
        (DerivedCategory.opQCompDerivedOpEquivalenceFunctorIso
          (C := Stacks.Injectives.ContinuousModule.{u, v, w} R Q)).app
          ((CochainComplex.opEquivalence
            (Stacks.Injectives.ContinuousModule.{u, v, w} R Q)).functor.obj (Opposite.op E))) ≪≫
    (contragredient.{u, v, w} R Q).mapDerivedCategoryFactors.app _

end Contragredient

end Stacks.ContinuousCohomology

end
