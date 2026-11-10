module

public import Mathlib.LinearAlgebra.TensorAlgebra.Grading
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraStalkUngraded
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraInhabitant
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.DirectSumGrading

/-!
# Stalks of the tensor algebra and of the tensor powers of a presheaf of modules

Let `R` be a presheaf of commutative rings on a topological space `X` and `F` a presheaf of
`R`-modules. This file proves that forming the tensor algebra, and forming the `n`-th tensor
power, commute with taking the stalk at a point `x : X`:

* `PresheafOfModules.tensorAlgStalkRingEquiv` : the stalk of the presheaf of rings
  `U ↦ T_{R(U)}(F(U))` is `T_{R_x}(F_x)`;
* `PresheafOfModules.tensorPowStalkEquiv` : the stalk of the presheaf of modules
  `U ↦ Tⁿ_{R(U)}(F(U))` — that is, of `PresheafOfModules.tensorPow n F` — is `Tⁿ_{R_x}(F_x)`, as
  a module over the stalk ring `R_x`.

The comparison sends the germ of `s₀ ⊗ ⋯ ⊗ s_{n-1}` to the tensor of the germs
(`PresheafOfModules.tensorPowStalkL_germ_ιMulti`). Since such tensors span the tensor power
(`TensorAlgebra.span_range_ιMulti`), that formula determines the isomorphism. The same statements
are then deduced for a sheaf of modules on a space with a sheaf of commutative rings.

## Main definitions

* `TensorAlgebra.ιMulti` : the canonical multilinear map `(Fin n → M) → T_R(M)` sending `v` to
  the ordered product `ι(v 0) ⋯ ι(v (n-1))`, and `TensorAlgebra.ιMultiPow` its corestriction to
  the degree-`n` homogeneous piece `TensorAlgebra.gradedPiece R n M`.
* `TensorAlgebra.directSumGradedPieceEquiv` : the decomposition of the tensor algebra into its
  homogeneous pieces, `(⨁ n, Tⁿ_R(M)) ≃ₗ[R] T_R(M)`.
* `PresheafOfModules.tensorAlg` : the presheaf of rings whose sections over `U` are
  `T_{R(U)}(F(U))`, with `TensorAlgebra.mapₛₗ` of the restriction maps as its restriction maps.
* `PresheafOfModules.tensorAlgGerm` : the germ map of `tensorAlg F`, as a ring homomorphism whose
  source is spelled as the tensor algebra itself.
* `PresheafOfModules.tensorAlgStalkDesc` : base change along the germ maps,
  `(T F)ₓ ⟶ T_{R_x}(F_x)`, obtained from the colimit computing the stalk.
* `PresheafOfModules.tensorAlgStalkRingHom`, `PresheafOfModules.tensorStalkAlgebra` and
  `PresheafOfModules.ιTensorStalkL` : the `R_x`-algebra structure on `(T F)ₓ` induced by the
  structure map `R ⟶ tensorAlg F`, and the `R_x`-linear degree-one generator `F_x →ₗ (T F)ₓ`.
* `PresheafOfModules.tensorAlgStalkLift` : the `R_x`-algebra map `T_{R_x}(F_x) ⟶ (T F)ₓ` lifting
  `ιTensorStalkL`.
* `PresheafOfModules.tensorPowStalkDesc` and `PresheafOfModules.tensorPowStalkL` : the same base
  change in degree `n`, as a morphism of abelian groups and as an `R_x`-linear map.

## Main results

* `TensorAlgebra.span_range_ιMulti` : the ordered tensors of `n` vectors span the degree-`n`
  piece of the tensor algebra.
* `PresheafOfModules.tensorAlgStalkRingEquiv` : the tensor algebra commutes with stalks.
* `PresheafOfModules.tensorPowStalkEquiv` : the `n`-th tensor power commutes with stalks.
* `PresheafOfModules.tensorPowStalkL_germ_ιMulti` : the comparison sends the germ of a tensor
  of `n` local sections to the tensor of the germs.
* `PresheafOfModules.tensorPowStalkEquivOfStalkIso` and
  `PresheafOfModules.tensorPowStalkEquivOfStalkIso_germ_ιMulti` : the same, transported along any
  morphism out of `tensorPow n F` which is a stalk isomorphism.
* `SheafOfModules.tensorPower_stalk` : for a sheaf of modules `M` and a tensor algebra `A` of `M`,
  `(Tⁿ M)ₓ ≅ Tⁿ_{O_x}(M_x)`, by an isomorphism sending the germ of an ordered tensor of local
  sections to the ordered tensor of the germs.
* `SheafOfModules.tensorAlgebra_stalk` : the ungraded statement `T(M)ₓ ≅ T_{O_x}(M_x)`, with the
  same description on germs.

## Implementation notes

The tensor algebra is not commutative, so `tensorAlg F` is a presheaf valued in `RingCat` and its
stalk is a colimit in `RingCat`, while the scalars are the stalk of `R` in `CommRingCat`. The two
are bridged by `SemilinearStalk.commStalkRingEquiv`; `tensorStalkAlgebra` is
`RingHom.toAlgebra'` applied to `tensorAlgStalkRingHom`, whose image is central
(`tensorAlgStalkRingHom_central`).

Injectivity of the degree-`n` comparison is deduced from the ungraded statement
`tensorAlgStalkRingEquiv` through the inclusion `Tⁿ_{R(U)}(F(U)) ⊆ T_{R(U)}(F(U))`, which is
injective on stalks because it is injective sectionwise; surjectivity holds because a finite
family of germs has a common open neighbourhood.

`TensorAlgebra R M` is not a commutative monoid, so the spanning family is
`TensorAlgebra.ιMulti R n`, whose value at `v` is the ordered product
`(List.ofFn fun i => ι R (v i)).prod`. Its subtype-valued companion `TensorAlgebra.ιMultiPow R n`
lands in `TensorAlgebra.gradedPiece R n M`, so `tensorPowStalkL_germ_ιMulti` is an equation in the
tensor power.

Instance search does not find `DirectSum.Decomposition (fun n => gradedPiece R n M)` through the
reducible abbreviation `TensorAlgebra.gradedPiece`, so `TensorAlgebra.decompositionGradedPiece`
records Mathlib's instance by `inferInstanceAs`.

Every statement about `tensorPow`, `TensorAlgebra.powMapₛₗ` or `TensorAlgebra.ιMulti` keeps the
degree `n` a variable: `TensorAlgebra.gradedPiece R n M` is a `Submodule.pow`, and with `n` a
numeral `whnf` unfolds it through `Submodule.mul` and `Submodule.span`.

The sections of `tensorAlg F` over `U` are `↑((tensorAlg F).obj (op U))`, and
`TensorAlgebra ((R ⋙ forget₂ _ _).obj (op U)) (F.obj (op U))` is the same type definitionally but
not syntactically, so `map_mul` does not fire through it under `rw`. `tensorAlgGerm`,
`ιTensorStalkFun` and `tensorPowStalkFun` ascribe the second spelling; all three are definitional
renames.

The universes `X : TopCat.{u}`, `R : X.Presheaf CommRingCat.{u}` and
`F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)` are the single combination at which
Mathlib's `Module (R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)` instance exists.

The ungraded sheaf-level statement is assembled in `SheafOfModules.tensorAlgebraStalkEquiv` from
`SheafOfModules.natStalkCoprodEquiv` (the stalk of a coproduct of sheaves of modules is the direct
sum of the stalks, Tag 01AH), the degreewise `SheafOfModules.tensorPowerStalkEquiv` and
`TensorAlgebra.directSumGradedPieceEquiv`.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

open scoped Pointwise DirectSum

universe u

/-! ### Ordered tensors of vectors, and the grading of the tensor algebra -/

namespace TensorAlgebra

section IotaMulti

variable {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]

/-- The ordered tensor of `n` vectors, as a multilinear map into the tensor algebra: `v` goes
to the ordered product `ι(v 0) ⋯ ι(v (n-1))`. -/
noncomputable def ιMulti (R : Type*) [CommSemiring R] (n : ℕ) {M : Type*} [AddCommMonoid M]
    [Module R M] : MultilinearMap R (fun _ : Fin n => M) (TensorAlgebra R M) :=
  (MultilinearMap.mkPiAlgebraFin R n (TensorAlgebra R M)).compLinearMap fun _ =>
    TensorAlgebra.ι R

/-- `ιMulti R n v` is the ordered product of the `ι R (v i)`. -/
theorem ιMulti_apply (n : ℕ) (v : Fin n → M) :
    ιMulti R n v = (List.ofFn fun i => TensorAlgebra.ι R (v i)).prod := by
  simp [ιMulti, MultilinearMap.mkPiAlgebraFin_apply]

/-- The ordered tensor of no vectors is `1`. -/
@[simp]
theorem ιMulti_zero_apply (v : Fin 0 → M) : ιMulti R 0 v = 1 := by
  simp [ιMulti_apply]

/-- The ordered tensor of `n + 1` vectors splits off its first factor on the left. -/
theorem ιMulti_succ_apply (n : ℕ) (v : Fin (n + 1) → M) :
    ιMulti R (n + 1) v = TensorAlgebra.ι R (v 0) * ιMulti R n (Fin.tail v) := by
  rw [ιMulti_apply, ιMulti_apply, List.ofFn_succ]
  simp [Fin.tail]

/-- The set of degree-one generators times the set of ordered tensors of `n` vectors is the set
of ordered tensors of `n + 1` vectors. -/
theorem range_ι_mul_range_ιMulti (n : ℕ) :
    Set.range (TensorAlgebra.ι R (M := M)) * Set.range (ιMulti R n (M := M)) =
      Set.range (ιMulti R (n + 1) (M := M)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro z ⟨a, ⟨m, rfl⟩, b, ⟨v, rfl⟩, rfl⟩
    exact ⟨Fin.cons m v, by rw [ιMulti_succ_apply, Fin.cons_zero, Fin.tail_cons]⟩
  · rintro z ⟨w, rfl⟩
    exact ⟨TensorAlgebra.ι R (w 0), ⟨w 0, rfl⟩, ιMulti R n (Fin.tail w), ⟨Fin.tail w, rfl⟩,
      (ιMulti_succ_apply n w).symm⟩

/-- The ordered tensors of `n` vectors span the degree-`n` piece of the tensor algebra. -/
theorem span_range_ιMulti (n : ℕ) :
    Submodule.span R (Set.range (ιMulti R n (M := M))) = gradedPiece R n M := by
  have hrange : Submodule.span R (Set.range (TensorAlgebra.ι R (M := M))) =
      LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) := by
    rw [LinearMap.range_eq_map, ← Submodule.span_univ, Submodule.map_span, Set.image_univ]
  change Submodule.span R (Set.range (ιMulti R n (M := M))) =
    LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ n
  induction n with
  | zero =>
      have h : Set.range (ιMulti R 0 (M := M)) = {1} := by
        refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨fun i => i.elim0, ιMulti_zero_apply _⟩, ?_⟩
        rintro z ⟨v, rfl⟩
        exact ιMulti_zero_apply v
      rw [h, pow_zero, Submodule.one_eq_span]
  | succ n ih =>
      rw [pow_succ', ← ih, ← hrange, Submodule.span_mul_span, range_ι_mul_range_ιMulti]

/-- The ordered tensor of `n` vectors lies in the degree-`n` piece of the tensor algebra. -/
theorem ιMulti_mem_gradedPiece (n : ℕ) (v : Fin n → M) : ιMulti R n v ∈ gradedPiece R n M := by
  rw [← span_range_ιMulti]
  exact Submodule.subset_span ⟨v, rfl⟩

/-- The ordered tensor of `n` vectors, as an element of the degree-`n` tensor power: the
corestriction of `TensorAlgebra.ιMulti` along `TensorAlgebra.ιMulti_mem_gradedPiece`. -/
noncomputable def ιMultiPow (R : Type*) [CommSemiring R] (n : ℕ) {M : Type*} [AddCommMonoid M]
    [Module R M] : MultilinearMap R (fun _ : Fin n => M) (gradedPiece R n M) :=
  (ιMulti R n).codRestrict (gradedPiece R n M) (ιMulti_mem_gradedPiece n)

/-- The value of `ιMultiPow` in the tensor algebra is `ιMulti`. -/
@[simp]
theorem ιMultiPow_coe (n : ℕ) (v : Fin n → M) :
    (ιMultiPow R n v : TensorAlgebra R M) = ιMulti R n v := rfl

/-- Base change carries an ordered tensor of vectors to the ordered tensor of their images. -/
theorem mapₛₗ_ιMulti {S : Type*} [CommSemiring S] {N : Type*} [AddCommMonoid N] [Module S N]
    (φ : R →+* S) (u : M →ₛₗ[φ] N) (n : ℕ) (v : Fin n → M) :
    mapₛₗ φ u (ιMulti R n v) = ιMulti S n fun i => u (v i) := by
  rw [ιMulti_apply, ιMulti_apply, map_list_prod (mapₛₗ φ u), List.map_ofFn]
  exact congrArg (fun g : Fin n → TensorAlgebra S N => (List.ofFn g).prod)
    (funext fun i => mapₛₗ_ι φ u (v i))

end IotaMulti

/-! ### The decomposition of the tensor algebra into its homogeneous pieces -/

section Grading

variable (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M]

/-- Mathlib's `TensorAlgebra.gradedAlgebra` decomposition, at the spelling
`TensorAlgebra.gradedPiece`. -/
instance decompositionGradedPiece : DirectSum.Decomposition (fun n : ℕ => gradedPiece R n M) :=
  inferInstanceAs (DirectSum.Decomposition
    ((LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ ·) : ℕ → Submodule R _))

/-- The decomposition of the tensor algebra into its tensor powers, as an `R`-linear
equivalence `(⨁ n, Tⁿ_R(M)) ≃ₗ[R] T_R(M)`. -/
noncomputable def directSumGradedPieceEquiv :
    (⨁ n : ℕ, gradedPiece R n M) ≃ₗ[R] TensorAlgebra R M :=
  (DirectSum.decomposeLinearEquiv (fun n : ℕ => gradedPiece R n M)).symm

/-- `directSumGradedPieceEquiv` sends an element of the degree-`n` summand to itself. -/
@[simp]
theorem directSumGradedPieceEquiv_lof (n : ℕ) (y : gradedPiece R n M) :
    directSumGradedPieceEquiv R M (DirectSum.lof R ℕ (fun k => gradedPiece R k M) n y) = y :=
  DirectSum.decomposeLinearEquiv_symm_lof (fun n : ℕ => gradedPiece R n M) n y

end Grading

end TensorAlgebra

namespace PresheafOfModules

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (x : X)

/-! ### The presheaf of sectionwise tensor algebras -/

/-- The presheaf of rings whose sections over `U` are `T_{O(U)}(F(U))`. -/
noncomputable def tensorAlg : X.Presheaf RingCat.{u} where
  obj U := RingCat.of
    (TensorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U) (F.obj U))
  map {U _} f := RingCat.ofHom
    (TensorAlgebra.mapₛₗ ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map f).hom
      (F.restrictₛₗ f))
  map_id U := by
    refine RingCat.hom_ext (RingHom.ext fun y => ?_)
    exact TensorAlgebra.mapₛₗ_eq_self (F.restrictₛₗ (𝟙 U))
      (fun r => congrArg (fun φ : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U ⟶
          (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U => (ConcreteCategory.hom φ) r)
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map_id U))
      (fun m => F.map_id_apply_ungraded U m) y
  map_comp {U _ W} f g := by
    refine RingCat.hom_ext (RingHom.ext fun y => ?_)
    exact TensorAlgebra.mapₛₗ_eq_comp (F.restrictₛₗ f) (F.restrictₛₗ g) (F.restrictₛₗ (f ≫ g))
      (fun r => congrArg (fun φ : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U ⟶
          (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj W => (ConcreteCategory.hom φ) r)
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map_comp f g))
      (fun m => F.map_comp_apply f g m) y

/-- The restriction maps of `tensorAlg F` are `TensorAlgebra.mapₛₗ` of the restriction maps of
`R` and `F`. -/
@[simp]
theorem tensorAlg_map_apply {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
    (y : TensorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U) (F.obj U)) :
    (tensorAlg F).map f y =
      TensorAlgebra.mapₛₗ ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map f).hom
        (F.restrictₛₗ f) y := rfl

/-- The germ map of `tensorAlg F` as a ring homomorphism out of the sectionwise tensor algebra,
with its source spelled as the tensor algebra itself. -/
noncomputable def tensorAlgGerm (U : Opens X) (hx : x ∈ U) :
    TensorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) (F.obj (op U)) →+*
      ↑((tensorAlg F).stalk x) :=
  ((tensorAlg F).germ U x hx).hom

/-- `tensorAlgGerm` is the germ map of `tensorAlg F`. -/
theorem tensorAlgGerm_eq (U : Opens X) (hx : x ∈ U)
    (y : TensorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
      (F.obj (op U))) :
    tensorAlgGerm F x U hx y = (tensorAlg F).germ U x hx y := rfl

/-- The cocone on the diagram computing the stalk of `tensorAlg F` whose component at an open
neighbourhood `U` of `x` is base change along the germ maps of `R` and of `F`. -/
noncomputable def tensorAlgStalkCocone :
    Limits.Cocone ((OpenNhds.inclusion x).op ⋙ tensorAlg F) where
  pt := RingCat.of
    (TensorAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x))
  ι :=
    { app := fun U => RingCat.ofHom
        (TensorAlgebra.mapₛₗ (R.germ U.unop.1 x U.unop.2).hom
          (germₛₗ F x U.unop.1 U.unop.2))
      naturality := fun U V f => by
        refine RingCat.hom_ext (RingHom.ext fun y => ?_)
        exact (TensorAlgebra.mapₛₗ_eq_comp
          (F.restrictₛₗ ((OpenNhds.inclusion x).op.map f))
          (germₛₗ F x V.unop.1 V.unop.2) (germₛₗ F x U.unop.1 U.unop.2)
          (fun r => (TopCat.Presheaf.germ_res_apply' R
            ((OpenNhds.inclusion x).op.map f) x V.unop.2 r).symm)
          (fun m => (TopCat.Presheaf.germ_res_apply' F.presheaf
            ((OpenNhds.inclusion x).op.map f) x V.unop.2 m).symm) y).symm }

/-- Base change of the tensor algebra along the germ maps, out of the stalk of the presheaf of
sectionwise tensor algebras. -/
noncomputable def tensorAlgStalkDesc :
    (tensorAlg F).stalk x ⟶
      RingCat.of (TensorAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)) :=
  Limits.colimit.desc _ (tensorAlgStalkCocone F x)

/-- `tensorAlgStalkDesc` sends the germ of a local section `y` to the base change of `y` along the
germ maps. -/
@[simp]
theorem tensorAlgStalkDesc_germ (U : Opens X) (hx : x ∈ U)
    (y : TensorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
      (F.obj (op U))) :
    tensorAlgStalkDesc F x (tensorAlgGerm F x U hx y) =
      TensorAlgebra.mapₛₗ (R.germ U x hx).hom (germₛₗ F x U hx) y := by
  have h := Limits.colimit.ι_desc (tensorAlgStalkCocone F x) (op ⟨U, hx⟩)
  exact congrArg (fun g : (tensorAlg F).obj (op U) ⟶ (tensorAlgStalkCocone F x).pt =>
    ConcreteCategory.hom g y) h

/-! ### The structure map and the degree-one generator on stalks -/

/-- The structure map `O ⟶ T(F)` of the presheaf of sectionwise tensor algebras. Its source is
`R ⋙ forget₂ CommRingCat RingCat`, since `tensorAlg F` is a presheaf of rings. -/
noncomputable def tensorAlgUnit : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⟶ tensorAlg F where
  app U := RingCat.ofHom
    (algebraMap ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U)
      (TensorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U) (F.obj U)))
  naturality _ _ f := by
    refine RingCat.hom_ext (RingHom.ext fun r => ?_)
    exact (TensorAlgebra.mapₛₗ_algebraMap
      ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map f).hom (F.restrictₛₗ f) r).symm

/-- The structure map on stalks, as a ring homomorphism from the `CommRingCat`-valued stalk of
`R`: the `RingCat`-valued stalk of `tensorAlgUnit F`, precomposed with
`SemilinearStalk.commStalkRingEquiv`. -/
noncomputable def tensorAlgStalkRingHom : ↑(R.stalk x) →+* ↑((tensorAlg F).stalk x) :=
  (((TopCat.Presheaf.stalkFunctor RingCat.{u} x).map (tensorAlgUnit F)).hom).comp
    (SemilinearStalk.commStalkRingEquiv R x).symm.toRingHom

/-- `tensorAlgStalkRingHom` sends the germ of a local section `r` of `R` to the germ of its image
under the structure map. -/
@[simp]
theorem tensorAlgStalkRingHom_germ (U : Opens X) (hx : x ∈ U) (r : ↑(R.obj (op U))) :
    tensorAlgStalkRingHom F x (R.germ U x hx r) =
      tensorAlgGerm F x U hx (algebraMap
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
        (TensorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
          (F.obj (op U))) r) := by
  have hcomm : (SemilinearStalk.commStalkRingEquiv R x).symm (R.germ U x hx r) =
      TopCat.Presheaf.germ (C := RingCat.{u}) (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})
        U x hx r :=
    (SemilinearStalk.commStalkRingEquiv R x).symm_apply_eq.2
      (SemilinearStalk.commStalkRingEquiv_germ R x U hx r).symm
  refine Eq.trans (congrArg
    (fun z => ((TopCat.Presheaf.stalkFunctor RingCat.{u} x).map (tensorAlgUnit F)).hom z)
    hcomm) ?_
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx (tensorAlgUnit F) r

/-- The image under `tensorAlgStalkRingHom` of a germ commutes with every germ. -/
theorem tensorAlgStalkRingHom_germ_central (U : Opens X) (hx : x ∈ U)
    (r : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
    (y : TensorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
      (F.obj (op U))) :
    tensorAlgStalkRingHom F x (R.germ U x hx r) * tensorAlgGerm F x U hx y =
      tensorAlgGerm F x U hx y * tensorAlgStalkRingHom F x (R.germ U x hx r) := by
  rw [tensorAlgStalkRingHom_germ, ← map_mul (tensorAlgGerm F x U hx),
    ← map_mul (tensorAlgGerm F x U hx)]
  exact congrArg (tensorAlgGerm F x U hx) (Algebra.commutes r y)

/-- The image of `tensorAlgStalkRingHom` is central. -/
theorem tensorAlgStalkRingHom_central (c : ↑(R.stalk x)) (z : ↑((tensorAlg F).stalk x)) :
    tensorAlgStalkRingHom F x c * z = z * tensorAlgStalkRingHom F x c := by
  obtain ⟨U₁, h₁, r₀, hr⟩ := R.exists_germ_eq c
  obtain ⟨U₂, h₂, y₀, hy⟩ := TopCat.Presheaf.exists_germ_eq (tensorAlg F) z
  have hmem : x ∈ U₁ ⊓ U₂ := ⟨h₁, h₂⟩
  have hr' : R.germ (U₁ ⊓ U₂) x hmem (R.map (homOfLE inf_le_left).op r₀) = c := by
    rw [TopCat.Presheaf.germ_res_apply R (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) x hmem r₀]
    exact hr
  have hy' : (tensorAlg F).germ (U₁ ⊓ U₂) x hmem
      ((tensorAlg F).map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op y₀) = z := by
    rw [TopCat.Presheaf.germ_res_apply (tensorAlg F)
      (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) x hmem y₀]
    exact hy
  rw [← hr', ← hy']
  exact tensorAlgStalkRingHom_germ_central F x (U₁ ⊓ U₂) hmem
    (R.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op r₀)
    ((tensorAlg F).map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op y₀)

/-- The stalk of the presheaf of sectionwise tensor algebras, as an algebra over the stalk of the
presheaf of rings. -/
noncomputable instance tensorStalkAlgebra : Algebra ↑(R.stalk x) ↑((tensorAlg F).stalk x) :=
  (tensorAlgStalkRingHom F x).toAlgebra' (tensorAlgStalkRingHom_central F x)

/-- The algebra map of `tensorStalkAlgebra` is `tensorAlgStalkRingHom`. -/
theorem algebraMap_tensorStalkAlgebra :
    algebraMap ↑(R.stalk x) ↑((tensorAlg F).stalk x) = tensorAlgStalkRingHom F x := rfl

/-- The algebra map of `tensorStalkAlgebra` sends the germ of a local section `r` of `R` to the
germ of its image under the structure map. -/
@[simp]
theorem algebraMap_tensorStalkAlgebra_germ (U : Opens X) (hx : x ∈ U) (r : ↑(R.obj (op U))) :
    algebraMap ↑(R.stalk x) ↑((tensorAlg F).stalk x) (R.germ U x hx r) =
      tensorAlgGerm F x U hx (algebraMap
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
        (TensorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
          (F.obj (op U))) r) :=
  tensorAlgStalkRingHom_germ F x U hx r

/-- The cocone whose component at an open neighbourhood `U` of `x` sends a section of `F` to the
germ of its degree-one image in `T_{O(U)}(F(U))`. -/
noncomputable def ιTensorStalkCocone :
    Limits.Cocone ((OpenNhds.inclusion x).op ⋙ F.presheaf) where
  pt := AddCommGrpCat.of ↑((tensorAlg F).stalk x)
  ι :=
    { app := fun U => AddCommGrpCat.ofHom
        (((tensorAlg F).germ U.unop.1 x U.unop.2).hom.toAddMonoidHom.comp
          (TensorAlgebra.ι
            ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U.unop.1))
            (M := F.obj (op U.unop.1))).toAddMonoidHom)
      naturality := fun U V f => by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m => ?_)
        exact Eq.trans
          (congrArg (fun z : TensorAlgebra
              ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op V.unop.1))
              (F.obj (op V.unop.1)) => (tensorAlg F).germ V.unop.1 x V.unop.2 z)
            (TensorAlgebra.mapₛₗ_ι
              ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map
                ((OpenNhds.inclusion x).op.map f)).hom
              (F.restrictₛₗ ((OpenNhds.inclusion x).op.map f)) m).symm)
          (TopCat.Presheaf.germ_res_apply' (tensorAlg F)
            ((OpenNhds.inclusion x).op.map f) x V.unop.2
            (TensorAlgebra.ι ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U.unop.1))
              (M := F.obj (op U.unop.1)) m)) }

/-- The additive map from the stalk of `F` to the stalk of the presheaf of sectionwise tensor
algebras, sending the germ of a section to the germ of its degree-one image. -/
noncomputable def ιTensorStalkAdd :
    TopCat.Presheaf.stalk F.presheaf x ⟶ AddCommGrpCat.of ↑((tensorAlg F).stalk x) :=
  Limits.colimit.desc _ (ιTensorStalkCocone F x)

/-- `ιTensorStalkAdd` sends the germ of a section `m` of `F` to the germ of `ι m`. -/
@[simp]
theorem ιTensorStalkAdd_germ (U : Opens X) (hx : x ∈ U) (m : F.obj (op U)) :
    ιTensorStalkAdd F x (TopCat.Presheaf.germ F.presheaf U x hx m) =
      tensorAlgGerm F x U hx (TensorAlgebra.ι
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) m) := by
  have h := Limits.colimit.ι_desc (ιTensorStalkCocone F x) (op ⟨U, hx⟩)
  exact congrArg (fun g : F.presheaf.obj (op U) ⟶ (ιTensorStalkCocone F x).pt =>
    ConcreteCategory.hom g m) h

/-- The underlying function of `ιTensorStalkAdd`, with its codomain spelled as the stalk ring. -/
noncomputable def ιTensorStalkFun (m : ↑(TopCat.Presheaf.stalk F.presheaf x)) :
    ↑((tensorAlg F).stalk x) :=
  ιTensorStalkAdd F x m

/-- `ιTensorStalkFun` sends the germ of a section `m` of `F` to the germ of `ι m`. -/
@[simp]
theorem ιTensorStalkFun_germ (U : Opens X) (hx : x ∈ U) (m : F.obj (op U)) :
    ιTensorStalkFun F x (TopCat.Presheaf.germ F.presheaf U x hx m) =
      tensorAlgGerm F x U hx (TensorAlgebra.ι
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) m) :=
  ιTensorStalkAdd_germ F x U hx m

/-- `ιTensorStalkFun` commutes with the action of germs of sections of `R` on germs of sections of
`F`. -/
theorem ιTensorStalkFun_germ_smul (U : Opens X) (hx : x ∈ U)
    (a : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) (b : F.obj (op U)) :
    ιTensorStalkFun F x (R.germ U x hx a • TopCat.Presheaf.germ F.presheaf U x hx b) =
      R.germ U x hx a • ιTensorStalkFun F x (TopCat.Presheaf.germ F.presheaf U x hx b) := by
  have h₁ : ιTensorStalkFun F x (R.germ U x hx a • TopCat.Presheaf.germ F.presheaf U x hx b) =
      tensorAlgGerm F x U hx (TensorAlgebra.ι
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) (a • b)) := by
    rw [← F.germ_smul x U hx a b]
    exact ιTensorStalkFun_germ F x U hx (a • b)
  have h₂ : TensorAlgebra.ι ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
        (M := F.obj (op U)) (a • b) =
      algebraMap ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
          (TensorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
            (F.obj (op U))) a *
        TensorAlgebra.ι ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) b := by
    rw [map_smul, Algebra.smul_def]
  rw [h₁, h₂, map_mul (tensorAlgGerm F x U hx), ιTensorStalkFun_germ, Algebra.smul_def,
    algebraMap_tensorStalkAlgebra_germ]

/-- A germ of a section of `R` and a germ of a section of a presheaf `P` at `x` can be represented
over a common open neighbourhood. -/
private theorem exists_germ_eq_germ_eq (P : X.Presheaf AddCommGrpCat.{u}) (r : ↑(R.stalk x))
    (t : ↑(P.stalk x)) :
    ∃ (U : Opens X) (hx : x ∈ U) (a : R.obj (op U)) (b : P.obj (op U)),
      R.germ U x hx a = r ∧ P.germ U x hx b = t := by
  obtain ⟨U₁, h₁, r₀, hr⟩ := R.exists_germ_eq r
  obtain ⟨U₂, hle, h₂, y₀, hy⟩ := TopCat.Presheaf.exists_le_germ_eq P t h₁
  exact ⟨U₂, h₂, R.map (homOfLE hle).op r₀, y₀,
    by rw [TopCat.Presheaf.germ_res_apply]; exact hr, hy⟩

/-- `ιTensorStalkFun` is `R_x`-linear. -/
theorem ιTensorStalkFun_smul (r : ↑(R.stalk x)) (m : ↑(TopCat.Presheaf.stalk F.presheaf x)) :
    ιTensorStalkFun F x (r • m) = r • ιTensorStalkFun F x m := by
  obtain ⟨U, hU, a, b, rfl, rfl⟩ := exists_germ_eq_germ_eq x F.presheaf r m
  exact ιTensorStalkFun_germ_smul F x U hU a b

/-- The degree-one generator on stalks: the linear map from the stalk of `F` to the stalk of the
presheaf of sectionwise tensor algebras. -/
noncomputable def ιTensorStalkL :
    ↑(TopCat.Presheaf.stalk F.presheaf x) →ₗ[↑(R.stalk x)] ↑((tensorAlg F).stalk x) where
  toFun := ιTensorStalkFun F x
  map_add' m m' := map_add _ m m'
  map_smul' r m := ιTensorStalkFun_smul F x r m

/-- `ιTensorStalkL` sends the germ of a section `m` of `F` to the germ of `ι m`. -/
@[simp]
theorem ιTensorStalkL_germ (U : Opens X) (hx : x ∈ U) (m : F.obj (op U)) :
    ιTensorStalkL F x (TopCat.Presheaf.germ F.presheaf U x hx m) =
      tensorAlgGerm F x U hx (TensorAlgebra.ι
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) m) :=
  ιTensorStalkFun_germ F x U hx m

/-- The algebra map from the tensor algebra of the stalk to the stalk of the presheaf of
sectionwise tensor algebras, induced by the degree-one generator on stalks. -/
noncomputable def tensorAlgStalkLift :
    TensorAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x) →ₐ[↑(R.stalk x)]
      ↑((tensorAlg F).stalk x) :=
  TensorAlgebra.lift ↑(R.stalk x) (ιTensorStalkL F x)

/-- `tensorAlgStalkLift` restricts to `ιTensorStalkL` on degree-one generators. -/
@[simp]
theorem tensorAlgStalkLift_ι (m : ↑(TopCat.Presheaf.stalk F.presheaf x)) :
    tensorAlgStalkLift F x (TensorAlgebra.ι _ m) = ιTensorStalkL F x m :=
  TensorAlgebra.lift_ι_apply (ιTensorStalkL F x) m

/-! ### The two base-change maps are mutually inverse -/

/-- `tensorAlgStalkDesc` sends the germ of the image of a local section `r` of `R` under the
structure map to the image of the germ of `r` in `T_{R_x}(F_x)`. -/
@[simp]
theorem tensorAlgStalkDesc_tensorAlgGerm_algebraMap (U : Opens X) (hU : x ∈ U)
    (r : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) :
    tensorAlgStalkDesc F x (tensorAlgGerm F x U hU
        (algebraMap ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
          (TensorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
            (F.obj (op U))) r)) =
      algebraMap ↑(R.stalk x)
        (TensorAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x))
        (R.germ U x hU r) := by
  rw [tensorAlgStalkDesc_germ]
  exact TensorAlgebra.mapₛₗ_algebraMap _ _ r

/-- `tensorAlgStalkDesc` sends the germ of `ι m` to `ι` of the germ of `m`. -/
@[simp]
theorem tensorAlgStalkDesc_tensorAlgGerm_ι (U : Opens X) (hU : x ∈ U) (m : F.obj (op U)) :
    tensorAlgStalkDesc F x (tensorAlgGerm F x U hU
        (TensorAlgebra.ι ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) m)) =
      TensorAlgebra.ι ↑(R.stalk x) (TopCat.Presheaf.germ F.presheaf U x hU m) := by
  rw [tensorAlgStalkDesc_germ]
  exact TensorAlgebra.mapₛₗ_ι _ _ m

/-- `tensorAlgStalkLift` is a left inverse of `tensorAlgStalkDesc` on germs. -/
theorem tensorAlgStalkLift_tensorAlgStalkDesc_germ (U : Opens X) (hU : x ∈ U)
    (y : TensorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
      (F.obj (op U))) :
    tensorAlgStalkLift F x (tensorAlgStalkDesc F x (tensorAlgGerm F x U hU y)) =
      tensorAlgGerm F x U hU y := by
  have key : (tensorAlgStalkLift F x).toRingHom.comp
      (((tensorAlgStalkDesc F x).hom).comp (tensorAlgGerm F x U hU)) =
      tensorAlgGerm F x U hU := by
    refine TensorAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
    · exact ((congrArg (fun z => tensorAlgStalkLift F x z)
          (tensorAlgStalkDesc_tensorAlgGerm_algebraMap F x U hU r)).trans
        ((tensorAlgStalkLift F x).commutes (R.germ U x hU r))).trans
        (algebraMap_tensorStalkAlgebra_germ F x U hU r)
    · exact ((congrArg (fun z => tensorAlgStalkLift F x z)
          (tensorAlgStalkDesc_tensorAlgGerm_ι F x U hU m)).trans
        (tensorAlgStalkLift_ι F x (TopCat.Presheaf.germ F.presheaf U x hU m))).trans
        (ιTensorStalkL_germ F x U hU m)
  exact DFunLike.congr_fun key y

/-- `tensorAlgStalkLift` is a left inverse of `tensorAlgStalkDesc`. -/
theorem tensorAlgStalkLift_tensorAlgStalkDesc (z : ↑((tensorAlg F).stalk x)) :
    tensorAlgStalkLift F x (tensorAlgStalkDesc F x z) = z := by
  obtain ⟨U, hU, y, rfl⟩ := TopCat.Presheaf.exists_germ_eq (tensorAlg F) z
  exact tensorAlgStalkLift_tensorAlgStalkDesc_germ F x U hU y

/-- `tensorAlgStalkLift` is a right inverse of `tensorAlgStalkDesc`. -/
theorem tensorAlgStalkDesc_tensorAlgStalkLift
    (z : TensorAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)) :
    tensorAlgStalkDesc F x (tensorAlgStalkLift F x z) = z := by
  have key : ((tensorAlgStalkDesc F x).hom).comp (tensorAlgStalkLift F x).toRingHom =
      RingHom.id (TensorAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)) := by
    refine TensorAlgebra.ringHom_ext (fun s => ?_) (fun m => ?_)
    · obtain ⟨U, hU, r, rfl⟩ := R.exists_germ_eq s
      exact ((congrArg (fun z => tensorAlgStalkDesc F x z)
            (((tensorAlgStalkLift F x).commutes (R.germ U x hU r)).trans
              (algebraMap_tensorStalkAlgebra_germ F x U hU r))).trans
          (tensorAlgStalkDesc_tensorAlgGerm_algebraMap F x U hU r))
    · obtain ⟨U, hU, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf m
      exact ((congrArg (fun z => tensorAlgStalkDesc F x z)
            ((tensorAlgStalkLift_ι F x (TopCat.Presheaf.germ F.presheaf U x hU b)).trans
              (ιTensorStalkL_germ F x U hU b))).trans
          (tensorAlgStalkDesc_tensorAlgGerm_ι F x U hU b))
  exact DFunLike.congr_fun key z

/-- The stalk at `x` of the presheaf of sectionwise tensor algebras of `F` is the tensor algebra
of the stalk of `F` over the stalk of the presheaf of rings. -/
noncomputable def tensorAlgStalkRingEquiv :
    ↑((tensorAlg F).stalk x) ≃+*
      TensorAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x) :=
  RingEquiv.ofBijective (tensorAlgStalkDesc F x).hom
    ⟨Function.LeftInverse.injective (tensorAlgStalkLift_tensorAlgStalkDesc F x),
      Function.RightInverse.surjective (tensorAlgStalkDesc_tensorAlgStalkLift F x)⟩

/-- `tensorAlgStalkDesc` is injective. -/
theorem tensorAlgStalkDesc_injective : Function.Injective (tensorAlgStalkDesc F x) :=
  Function.LeftInverse.injective (tensorAlgStalkLift_tensorAlgStalkDesc F x)

/-! ### The stalk of the presheaf of sectionwise tensor powers -/

/-- The cocone on the diagram computing the stalk of `tensorPow n F` whose component at an open
neighbourhood `U` of `x` is base change of the `n`-th tensor power along the germ maps. -/
noncomputable def tensorPowStalkCocone (n : ℕ) :
    Limits.Cocone ((OpenNhds.inclusion x).op ⋙ (tensorPow n F).presheaf) where
  pt := AddCommGrpCat.of
    (TensorAlgebra.gradedPiece ↑(R.stalk x) n ↑(TopCat.Presheaf.stalk F.presheaf x))
  ι :=
    { app := fun U => AddCommGrpCat.ofHom
        (TensorAlgebra.powMapₛₗ n (R.germ U.unop.1 x U.unop.2).hom
          (germₛₗ F x U.unop.1 U.unop.2)).toAddMonoidHom
      naturality := fun U V f => by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun y => Subtype.ext ?_)
        exact (TensorAlgebra.mapₛₗ_eq_comp
          (F.restrictₛₗ ((OpenNhds.inclusion x).op.map f))
          (germₛₗ F x V.unop.1 V.unop.2) (germₛₗ F x U.unop.1 U.unop.2)
          (fun r => (TopCat.Presheaf.germ_res_apply' R
            ((OpenNhds.inclusion x).op.map f) x V.unop.2 r).symm)
          (fun m => (TopCat.Presheaf.germ_res_apply' F.presheaf
            ((OpenNhds.inclusion x).op.map f) x V.unop.2 m).symm) _).symm }

/-- Base change of the `n`-th tensor power along the germ maps, out of the stalk of the presheaf
of sectionwise tensor powers. -/
noncomputable def tensorPowStalkDesc (n : ℕ) :
    TopCat.Presheaf.stalk (tensorPow n F).presheaf x ⟶ AddCommGrpCat.of
      (TensorAlgebra.gradedPiece ↑(R.stalk x) n ↑(TopCat.Presheaf.stalk F.presheaf x)) :=
  Limits.colimit.desc _ (tensorPowStalkCocone F x n)

/-- The underlying function of `tensorPowStalkDesc`, with its codomain spelled as the tensor
power of the stalk. -/
noncomputable def tensorPowStalkFun (n : ℕ)
    (t : ↑(TopCat.Presheaf.stalk (tensorPow n F).presheaf x)) :
    TensorAlgebra.gradedPiece ↑(R.stalk x) n ↑(TopCat.Presheaf.stalk F.presheaf x) :=
  tensorPowStalkDesc F x n t

/-- `tensorPowStalkFun` sends the germ of a local section `y` of `tensorPow n F` to the base change
of `y` along the germ maps. -/
@[simp]
theorem tensorPowStalkFun_germ (n : ℕ) (U : Opens X) (hx : x ∈ U)
    (y : (tensorPow n F).obj (op U)) :
    tensorPowStalkFun F x n (TopCat.Presheaf.germ (tensorPow n F).presheaf U x hx y) =
      TensorAlgebra.powMapₛₗ n (R.germ U x hx).hom (germₛₗ F x U hx) y := by
  have h := Limits.colimit.ι_desc (tensorPowStalkCocone F x n) (op ⟨U, hx⟩)
  exact congrArg (fun g : (tensorPow n F).presheaf.obj (op U) ⟶ (tensorPowStalkCocone F x n).pt =>
    ConcreteCategory.hom g y) h

/-- `tensorPowStalkFun` commutes with the action of germs of sections of `R`. -/
theorem tensorPowStalkFun_germ_smul (n : ℕ) (U : Opens X) (hx : x ∈ U)
    (a : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
    (y : (tensorPow n F).obj (op U)) :
    tensorPowStalkFun F x n (R.germ U x hx a •
        TopCat.Presheaf.germ (tensorPow n F).presheaf U x hx y) =
      R.germ U x hx a •
        tensorPowStalkFun F x n (TopCat.Presheaf.germ (tensorPow n F).presheaf U x hx y) := by
  rw [← (tensorPow n F).germ_smul x U hx a y, tensorPowStalkFun_germ, tensorPowStalkFun_germ]
  exact map_smulₛₗ (TensorAlgebra.powMapₛₗ n (R.germ U x hx).hom (germₛₗ F x U hx)) a y

/-- `tensorPowStalkFun` is `R_x`-linear. -/
theorem tensorPowStalkFun_smul (n : ℕ) (r : ↑(R.stalk x))
    (t : ↑(TopCat.Presheaf.stalk (tensorPow n F).presheaf x)) :
    tensorPowStalkFun F x n (r • t) = r • tensorPowStalkFun F x n t := by
  obtain ⟨U, hU, a, b, rfl, rfl⟩ := exists_germ_eq_germ_eq x (tensorPow n F).presheaf r t
  exact tensorPowStalkFun_germ_smul F x n U hU a b

/-- Base change of the `n`-th tensor power along the germ maps, as a linear map from the stalk of
the presheaf of sectionwise tensor powers of `F` to the `n`-th tensor power of the stalk of
`F`. -/
noncomputable def tensorPowStalkL (n : ℕ) :
    ↑(TopCat.Presheaf.stalk (tensorPow n F).presheaf x) →ₗ[↑(R.stalk x)]
      TensorAlgebra.gradedPiece ↑(R.stalk x) n ↑(TopCat.Presheaf.stalk F.presheaf x) where
  toFun := tensorPowStalkFun F x n
  map_add' t t' := map_add _ t t'
  map_smul' r t := tensorPowStalkFun_smul F x n r t

/-- `tensorPowStalkL` sends the germ of a local section `y` of `tensorPow n F` to the base change
of `y` along the germ maps. -/
@[simp]
theorem tensorPowStalkL_germ (n : ℕ) (U : Opens X) (hx : x ∈ U)
    (y : (tensorPow n F).obj (op U)) :
    tensorPowStalkL F x n (TopCat.Presheaf.germ (tensorPow n F).presheaf U x hx y) =
      TensorAlgebra.powMapₛₗ n (R.germ U x hx).hom (germₛₗ F x U hx) y :=
  tensorPowStalkFun_germ F x n U hx y

/-! ### The comparison map is bijective -/

/-- If base change of a local section of `Tⁿ F` along the germ maps vanishes, then its germ
vanishes. -/
theorem germ_eq_zero_of_tensorMapₛₗ_eq_zero (n : ℕ) (U : Opens X) (hU : x ∈ U)
    (y : TensorAlgebra.gradedPiece ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) n
      (F.obj (op U)))
    (h : TensorAlgebra.mapₛₗ (R.germ U x hU).hom (germₛₗ F x U hU)
      (y : TensorAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
        (F.obj (op U))) = 0) :
    TopCat.Presheaf.germ (tensorPow n F).presheaf U x hU y = 0 := by
  have h0 : tensorAlgGerm F x U hU ↑y = tensorAlgGerm F x U hU 0 := by
    refine tensorAlgStalkDesc_injective F x ?_
    rw [tensorAlgStalkDesc_germ, tensorAlgStalkDesc_germ, h, map_zero]
  obtain ⟨W, hW, iU, iV, heq⟩ := TopCat.Presheaf.germ_eq (tensorAlg F) x hU hU _ 0
    ((tensorAlgGerm_eq F x U hU _).symm.trans (h0.trans (tensorAlgGerm_eq F x U hU 0)))
  have hy : (tensorPow n F).presheaf.map iU.op y = 0 :=
    Subtype.ext (heq.trans (map_zero _))
  refine (TopCat.Presheaf.germ_res_apply (tensorPow n F).presheaf iU x hW y).symm.trans ?_
  rw [hy, map_zero]

/-- `tensorPowStalkL` is injective. -/
theorem tensorPowStalkL_injective (n : ℕ) : Function.Injective (tensorPowStalkL F x n) := by
  refine (injective_iff_map_eq_zero (tensorPowStalkL F x n)).2 fun t ht => ?_
  obtain ⟨U, hU, y, rfl⟩ := TopCat.Presheaf.exists_germ_eq (tensorPow n F).presheaf t
  refine germ_eq_zero_of_tensorMapₛₗ_eq_zero F x n U hU y ?_
  exact (TensorAlgebra.powMapₛₗ_coe n (R.germ U x hU).hom (germₛₗ F x U hU) y).symm.trans
    (congrArg Subtype.val ((tensorPowStalkL_germ F x n U hU y).symm.trans ht))

/-- The comparison sends the germ of `s₀ ⊗ ⋯ ⊗ s_{n-1}` to the ordered tensor of the germs. -/
theorem tensorPowStalkL_germ_ιMulti (n : ℕ) (U : Opens X) (hx : x ∈ U)
    (s : Fin n → F.obj (op U)) :
    tensorPowStalkL F x n (TopCat.Presheaf.germ (tensorPow n F).presheaf U x hx
        (TensorAlgebra.ιMultiPow
          ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) n s)) =
      TensorAlgebra.ιMultiPow ↑(R.stalk x) n
        fun i => TopCat.Presheaf.germ F.presheaf U x hx (s i) := by
  refine Subtype.ext ?_
  refine (congrArg Subtype.val (tensorPowStalkL_germ F x n U hx _)).trans ?_
  exact (TensorAlgebra.powMapₛₗ_coe n (R.germ U x hx).hom (germₛₗ F x U hx) _).trans
    (TensorAlgebra.mapₛₗ_ιMulti (R.germ U x hx).hom (germₛₗ F x U hx) n s)

/-- `tensorPowStalkL` is surjective. -/
theorem tensorPowStalkL_surjective (n : ℕ) : Function.Surjective (tensorPowStalkL F x n) := by
  have hle : _root_.Submodule.span ↑(R.stalk x)
        (Set.range (TensorAlgebra.ιMulti ↑(R.stalk x) n
          (M := ↑(TopCat.Presheaf.stalk F.presheaf x)))) ≤
      _root_.Submodule.map
        (TensorAlgebra.gradedPiece ↑(R.stalk x) n
          ↑(TopCat.Presheaf.stalk F.presheaf x)).subtype
        (LinearMap.range (tensorPowStalkL F x n)) := by
    refine _root_.Submodule.span_le.2 ?_
    rintro _ ⟨s, rfl⟩
    choose U hU t ht using fun i : Fin n => TopCat.Presheaf.exists_germ_eq F.presheaf (s i)
    have hW : x ∈ (⨅ i, U i : Opens X) := by
      rw [← SetLike.mem_coe, Opens.coe_iInf]
      exact Set.mem_iInter.2 hU
    refine _root_.Submodule.mem_map.2 ⟨tensorPowStalkL F x n
      (TopCat.Presheaf.germ (tensorPow n F).presheaf (⨅ i, U i : Opens X) x hW
        (TensorAlgebra.ιMultiPow
          ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op (⨅ i, U i : Opens X))) n
          fun i => F.map (homOfLE (iInf_le U i)).op (t i))), ⟨_, rfl⟩, ?_⟩
    refine Eq.trans (congrArg Subtype.val (tensorPowStalkL_germ_ιMulti F x n
      (⨅ i, U i : Opens X) hW (fun i => F.map (homOfLE (iInf_le U i)).op (t i)))) ?_
    exact congrArg (TensorAlgebra.ιMulti ↑(R.stalk x) n) (funext fun i =>
      (TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE (iInf_le U i)) x hW (t i)).trans (ht i))
  intro z
  obtain ⟨w, hw, hwz⟩ := hle (by rw [TensorAlgebra.span_range_ιMulti]; exact z.2 :
    (z : TensorAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)) ∈ _)
  obtain ⟨v, hv⟩ := hw
  exact ⟨v, Subtype.ext ((congrArg Subtype.val hv).trans hwz)⟩

/-- For a presheaf of modules `F` over a presheaf of commutative rings `R` on a topological
space, the stalk at `x` of the presheaf of sectionwise tensor powers `U ↦ Tⁿ_{R(U)}(F(U))` is the
`n`-th tensor power of the stalk `F_x` over the stalk ring `R_x`, by base change along the germ
maps. -/
noncomputable def tensorPowStalkEquiv (n : ℕ) :
    ↑(TopCat.Presheaf.stalk (tensorPow n F).presheaf x) ≃ₗ[↑(R.stalk x)]
      TensorAlgebra.gradedPiece ↑(R.stalk x) n ↑(TopCat.Presheaf.stalk F.presheaf x) :=
  LinearEquiv.ofBijective (tensorPowStalkL F x n)
    ⟨tensorPowStalkL_injective F x n, tensorPowStalkL_surjective F x n⟩

/-- The underlying map of `tensorPowStalkEquiv` is `tensorPowStalkL`. -/
@[simp]
theorem tensorPowStalkEquiv_apply (n : ℕ)
    (t : ↑(TopCat.Presheaf.stalk (tensorPow n F).presheaf x)) :
    tensorPowStalkEquiv F x n t = tensorPowStalkL F x n t := rfl

/-! ### Transport along a morphism which is a stalk isomorphism -/

/-- If `φ` exhibits `Q` as having the same stalks as the presheaf `U ↦ Tⁿ_{R(U)}(F(U))`, then
the stalk of `Q` at `x` is `Tⁿ_{R_x}(F_x)`. -/
noncomputable def tensorPowStalkEquivOfStalkIso (n : ℕ)
    {Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (φ : tensorPow n F ⟶ Q)
    (h : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((toPresheaf _).map φ))) :
    ↑(TopCat.Presheaf.stalk Q.presheaf x) ≃ₗ[↑(R.stalk x)]
      TensorAlgebra.gradedPiece ↑(R.stalk x) n ↑(TopCat.Presheaf.stalk F.presheaf x) :=
  (stalkLinearEquiv x φ h).symm.trans (tensorPowStalkEquiv F x n)

/-- `tensorPowStalkEquivOfStalkIso` sends the germ of the image of `s₀ ⊗ ⋯ ⊗ s_{n-1}` to the
ordered tensor of the germs. -/
theorem tensorPowStalkEquivOfStalkIso_germ_ιMulti (n : ℕ)
    {Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (φ : tensorPow n F ⟶ Q)
    (h : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((toPresheaf _).map φ)))
    (U : Opens X) (hx : x ∈ U) (s : Fin n → F.obj (op U)) :
    tensorPowStalkEquivOfStalkIso F x n φ h (TopCat.Presheaf.germ Q.presheaf U x hx
        (φ.app (op U) (TensorAlgebra.ιMultiPow
          ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) n s))) =
      TensorAlgebra.ιMultiPow ↑(R.stalk x) n
        fun i => TopCat.Presheaf.germ F.presheaf U x hx (s i) := by
  refine Eq.trans (congrArg (tensorPowStalkEquiv F x n)
    ((stalkLinearEquiv x φ h).symm_apply_eq.2 (stalkMapL_germ x φ U hx _).symm)) ?_
  exact tensorPowStalkL_germ_ιMulti F x n U hx s

end PresheafOfModules

/-! ### Transporting the tensor-algebra universal property along an isomorphism -/

namespace SheafOfModules.GradedAlgebra

section Transport

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {A : GradedAlgebra.{u, u} R} {M N : SheafOfModules.{u} R}

/-- If `A` is a tensor algebra of `M` with degree-one generator `gen` and `e : N ≅ M`, then `A`
is a tensor algebra of `N` with degree-one generator `e.hom ≫ gen`. -/
theorem IsTensorAlgebra.comp_iso {gen : M ⟶ A.piece 1} (hA : IsTensorAlgebra A gen) (e : N ≅ M) :
    IsTensorAlgebra A (e.hom ≫ gen) := by
  refine ⟨trivial, fun B κ _ => ?_⟩
  obtain ⟨g, hg, hgu⟩ := hA.2 B (e.inv ≫ κ) trivial
  refine ⟨g, ?_, fun g' hg' => hgu g' ?_⟩
  · simp only [Category.assoc, hg]
    simp
  · simp only [Category.assoc] at hg'
    simp only [← hg', ← Category.assoc, e.inv_hom_id, Category.id_comp]

end Transport

end SheafOfModules.GradedAlgebra

/-! ### Tag 01CH, tensor clause, for a sheaf of modules -/

open CategoryTheory.Limits CategoryTheory.Sheaf

namespace SheafOfModules

section TensorSheaf

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}

/-- If `e` identifies `N` with the sheafification of `U ↦ Tⁿ_{O♯(U)}(F(U))`, then the stalk of
`N` at `x` is the `n`-th tensor power of the stalk of `F`. -/
noncomputable def tensorPowStalkEquivOfIso
    {F : PresheafOfModules.{u} (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})} (n : ℕ)
    {N : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (e : N ≅ (PresheafOfModules.moduleSheafification (Opens.grothendieckTopology ↥X)
      (𝟙 Osharp.obj)).obj (PresheafOfModules.tensorPow n F))
    (x : ↥X) :
    ↑(TopCat.Presheaf.stalk N.val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      TensorAlgebra.gradedPiece ↑(TopCat.Presheaf.stalk Osharp.obj x) n
        ↑(TopCat.Presheaf.stalk F.presheaf x) :=
  ((valStalkLinearEquivOfIso e x).trans (sheafifyStalkLinearEquiv
    (PresheafOfModules.tensorPow n F) x).symm).trans
    (PresheafOfModules.tensorPowStalkEquiv F x n)

/-- `tensorPowStalkEquivOfIso n e x` is `valStalkLinearEquivOfIso e x`, followed by the inverse of
`sheafifyStalkLinearEquiv`, followed by `PresheafOfModules.tensorPowStalkEquiv`. -/
theorem tensorPowStalkEquivOfIso_apply
    {F : PresheafOfModules.{u} (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})} (n : ℕ)
    {N : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (e : N ≅ (PresheafOfModules.moduleSheafification (Opens.grothendieckTopology ↥X)
      (𝟙 Osharp.obj)).obj (PresheafOfModules.tensorPow n F))
    (x : ↥X) (t : ↑(TopCat.Presheaf.stalk N.val.presheaf x)) :
    tensorPowStalkEquivOfIso n e x t =
      PresheafOfModules.tensorPowStalkEquiv F x n
        ((sheafifyStalkLinearEquiv (PresheafOfModules.tensorPow n F) x).symm
          (valStalkLinearEquivOfIso e x t)) := rfl

/-- `tensorPowStalkEquivOfIso` sends the germ of the image in `N` of a local section `y` of
`U ↦ Tⁿ_{O♯(U)}(F(U))` (under the sheafification unit followed by `e.inv`) to the base change of
`y` along the germ maps. -/
theorem tensorPowStalkEquivOfIso_germ
    {F : PresheafOfModules.{u} (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})} (n : ℕ)
    {N : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (e : N ≅ (PresheafOfModules.moduleSheafification (Opens.grothendieckTopology ↥X)
      (𝟙 Osharp.obj)).obj (PresheafOfModules.tensorPow n F))
    (x : ↥X) (U : Opens ↥X) (hx : x ∈ U) (y : (PresheafOfModules.tensorPow n F).obj (op U)) :
    tensorPowStalkEquivOfIso n e x (TopCat.Presheaf.germ N.val.presheaf U x hx
        (PresheafOfModules.Hom.app e.inv.val (op U)
          (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
            (toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj))
            (PresheafOfModules.tensorPow n F)) (op U) y))) =
      PresheafOfModules.tensorPowStalkEquiv F x n
        (TopCat.Presheaf.germ (PresheafOfModules.tensorPow n F).presheaf U x hx y) := by
  refine Eq.trans (tensorPowStalkEquivOfIso_apply n e x _) (congrArg _ ?_)
  rw [LinearEquiv.symm_apply_eq, valStalkLinearEquivOfIso_germ, sheafifyStalkLinearEquiv_germ]
  exact congrArg _ (SheafOfModules.hom_congr_app_apply e.inv_hom_id (op U) _)

/-- `tensorPowStalkEquivOfIso` sends the germ of the image of `s₀ ⊗ ⋯ ⊗ s_{n-1}` to the ordered
tensor of the germs of the `sᵢ`. -/
theorem tensorPowStalkEquivOfIso_germ_ιMulti
    {F : PresheafOfModules.{u} (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})} (n : ℕ)
    {N : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (e : N ≅ (PresheafOfModules.moduleSheafification (Opens.grothendieckTopology ↥X)
      (𝟙 Osharp.obj)).obj (PresheafOfModules.tensorPow n F))
    (x : ↥X) (U : Opens ↥X) (hx : x ∈ U) (s : Fin n → F.obj (op U)) :
    tensorPowStalkEquivOfIso n e x (TopCat.Presheaf.germ N.val.presheaf U x hx
        (PresheafOfModules.Hom.app e.inv.val (op U)
          (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
              (toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj))
              (PresheafOfModules.tensorPow n F)) (op U)
            (TensorAlgebra.ιMultiPow
              ((Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) n s)))) =
      TensorAlgebra.ιMultiPow ↑(TopCat.Presheaf.stalk Osharp.obj x) n
        fun i => TopCat.Presheaf.germ F.presheaf U x hx (s i) :=
  (tensorPowStalkEquivOfIso_germ n e x U hx _).trans
    (PresheafOfModules.tensorPowStalkL_germ_ιMulti F x n U hx s)

variable {M : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
  (gen : M ⟶ A.piece 1) (hA : GradedAlgebra.IsTensorAlgebra A gen)

/-- The degree-`n` piece of a tensor algebra `A` of `M` is the sheafification of the presheaf
`U ↦ Tⁿ_{O♯(U)}(M(U))`. -/
noncomputable def tensorAlgPieceIso (n : ℤ) :
    (sectionwiseTensorAlgebra (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj) M.val).piece n ≅
      A.piece n :=
  (isTensorAlgebra_sectionwiseTensorAlgebra (Opens.grothendieckTopology ↥X)
    (𝟙 Osharp.obj) M.val).pieceIso (hA.comp_iso (sheafifySectionsIso M)) n

/-- For a tensor algebra `A` of a sheaf of modules `M`, the stalk at `x` of the degree-`n` tensor
power `A.piece n` is the `n`-th tensor power of the stalk `M_x` over the stalk ring `O_x`. -/
noncomputable def tensorPowerStalkEquiv (n : ℕ) (x : ↥X) :
    ↑(TopCat.Presheaf.stalk (A.piece (n : ℤ)).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      TensorAlgebra.gradedPiece ↑(TopCat.Presheaf.stalk Osharp.obj x) n
        ↑(TopCat.Presheaf.stalk M.val.presheaf x) :=
  tensorPowStalkEquivOfIso n (tensorAlgPieceIso A gen hA (n : ℤ)).symm x

/-- `tensorPowerStalkEquiv` sends the germ at `x` of the local section of `Tⁿ M` obtained from
`s₀ ⊗ ⋯ ⊗ s_{n-1}` by the sheafification unit followed by `SheafOfModules.tensorAlgPieceIso` to
the ordered tensor of the germs of the `sᵢ`. -/
theorem tensorPowerStalkEquiv_germ_ιMulti (n : ℕ) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (s : Fin n → M.val.obj (op U)) :
    tensorPowerStalkEquiv A gen hA n x
        (TopCat.Presheaf.germ (A.piece (n : ℤ)).val.presheaf U x hx
          (PresheafOfModules.Hom.app (tensorAlgPieceIso A gen hA (n : ℤ)).hom.val (op U)
            (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
                (toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj))
                (PresheafOfModules.tensorPow n M.val)) (op U)
              (TensorAlgebra.ιMultiPow
                ((Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) n s)))) =
      TensorAlgebra.ιMultiPow ↑(TopCat.Presheaf.stalk Osharp.obj x) n
        fun i => TopCat.Presheaf.germ M.val.presheaf U x hx (s i) :=
  tensorPowStalkEquivOfIso_germ_ιMulti n (tensorAlgPieceIso A gen hA (n : ℤ)).symm x U hx s

include hA in
/-- For a sheaf of modules `M` on a topological space with a sheaf of commutative rings `O♯`, a
tensor algebra `A` of `M` in the sense of Section 17.21, and a point `x`, there is an isomorphism
of `O_x`-modules

`(Tⁿ M)ₓ ≅ Tⁿ_{O_x}(M_x)`

sending the germ of every local section coming from an ordered tensor `s₀ ⊗ ⋯ ⊗ s_{n-1}` to the
ordered tensor of the germs of the `sᵢ`. -/
@[stacks 01CH "the tensor assertion in each graded degree `n`: `(Tⁿ M)ₓ ≅ Tⁿ(Mₓ)` for a sheaf of \
modules, with the isomorphism pinned down by its values on germs of ordered tensors of local \
sections. The ungraded `T(M)ₓ ≅ T(Mₓ)` is `SheafOfModules.tensorAlgebra_stalk`; the symmetric \
assertions are `SheafOfModules.symmetricPower_stalk` and \
`SheafOfModules.symmetricAlgebra_stalk`; the exterior assertion is not carried here"]
theorem tensorPower_stalk (n : ℕ) (x : ↥X) :
    ∃ cmp : ↑(TopCat.Presheaf.stalk (A.piece (n : ℤ)).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        TensorAlgebra.gradedPiece ↑(TopCat.Presheaf.stalk Osharp.obj x) n
          ↑(TopCat.Presheaf.stalk M.val.presheaf x),
      ∀ (U : Opens ↥X) (hx : x ∈ U) (s : Fin n → M.val.obj (op U)),
        cmp (TopCat.Presheaf.germ (A.piece (n : ℤ)).val.presheaf U x hx
              (PresheafOfModules.Hom.app (tensorAlgPieceIso A gen hA (n : ℤ)).hom.val (op U)
                (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
                    (toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj))
                    (PresheafOfModules.tensorPow n M.val)) (op U)
                  (TensorAlgebra.ιMultiPow
                    ((Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) n s)))) =
          TensorAlgebra.ιMultiPow ↑(TopCat.Presheaf.stalk Osharp.obj x) n
            fun i => TopCat.Presheaf.germ M.val.presheaf U x hx (s i) :=
  ⟨tensorPowerStalkEquiv A gen hA n x,
    fun U hx s => tensorPowerStalkEquiv_germ_ιMulti A gen hA n x U hx s⟩

/-! ### Tag 01CH for the ungraded tensor algebra of a sheaf of modules -/

/-- For a tensor algebra `A` of a sheaf of modules `M`, the stalk at `x` of the sheaf of modules
`∐ n, Tⁿ M` underlying `T(M)` is the tensor algebra of the stalk `M_x` over the stalk ring
`O_x`. -/
noncomputable def tensorAlgebraStalkEquiv (x : ↥X) :
    ↑(TopCat.Presheaf.stalk (∐ fun n : ℕ => A.piece (n : ℤ)).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      TensorAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk M.val.presheaf x) :=
  ((natStalkCoprodEquiv (fun n : ℕ => A.piece (n : ℤ)) x).symm.trans
      (DirectSum.congrLinearEquiv fun n : ℕ => tensorPowerStalkEquiv A gen hA n x)).trans
    (TensorAlgebra.directSumGradedPieceEquiv ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk M.val.presheaf x))

/-- `tensorAlgebraStalkEquiv` sends the germ at `x` of the image under the degree-`n` coproduct
injection of the local section of `Tⁿ M` coming from `s₀ ⊗ ⋯ ⊗ s_{n-1}` to the ordered tensor of
the germs of the `sᵢ`. -/
theorem tensorAlgebraStalkEquiv_germ_ιMulti (x : ↥X) (n : ℕ) (U : Opens ↥X) (hx : x ∈ U)
    (s : Fin n → M.val.obj (op U)) :
    tensorAlgebraStalkEquiv A gen hA x
        (TopCat.Presheaf.germ (∐ fun m : ℕ => A.piece (m : ℤ)).val.presheaf U x hx
          ((Sigma.ι (fun m : ℕ => A.piece (m : ℤ)) n).val.app (op U)
            (PresheafOfModules.Hom.app (tensorAlgPieceIso A gen hA (n : ℤ)).hom.val (op U)
              (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
                  (toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj))
                  (PresheafOfModules.tensorPow n M.val)) (op U)
                (TensorAlgebra.ιMultiPow
                  ((Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) n s))))) =
      TensorAlgebra.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n
        fun i => TopCat.Presheaf.germ M.val.presheaf U x hx (s i) := by
  have h1 (z : (A.piece (n : ℤ)).val.obj (op U)) :
      TopCat.Presheaf.germ (∐ fun m : ℕ => A.piece (m : ℤ)).val.presheaf U x hx
        ((Sigma.ι (fun m : ℕ => A.piece (m : ℤ)) n).val.app (op U) z) =
      natStalkCoprodEquiv (fun m : ℕ => A.piece (m : ℤ)) x (DirectSum.of _ n
        (TopCat.Presheaf.germ (A.piece (n : ℤ)).val.presheaf U x hx z)) := by
    rw [natStalkCoprodEquiv_of]
    exact (PresheafOfModules.stalkMapL_germ x
      (Sigma.ι (fun m : ℕ => A.piece (m : ℤ)) n).val U hx z).symm
  rw [h1]
  simp only [tensorAlgebraStalkEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, DirectSum.coe_congrLinearEquiv,
    ← DirectSum.lof_eq_of ↑(TopCat.Presheaf.stalk Osharp.obj x), DirectSum.lmap_lof,
    LinearEquiv.coe_coe, TensorAlgebra.directSumGradedPieceEquiv_lof]
  exact congrArg Subtype.val (tensorPowerStalkEquiv_germ_ιMulti A gen hA n x U hx s)

include hA in
/-- For a sheaf of modules `M` on a topological space with a sheaf of commutative rings `O♯`, a
tensor algebra `A` of `M` in the sense of Section 17.21, and a point `x`, there is an isomorphism
of `O_x`-modules

`T(M)ₓ ≅ T_{O_x}(M_x)`,

where `T(M)` is the coproduct `∐ n, Tⁿ M` of the homogeneous pieces of `A`, sending the germ of
every local section coming from an ordered tensor `s₀ ⊗ ⋯ ⊗ s_{n-1}`, in every degree `n`, to the
ordered tensor of the germs of the `sᵢ`. -/
@[stacks 01CH "the ungraded tensor assertion `T(M)ₓ ≅ T(Mₓ)`, with the isomorphism pinned down \
by its values on germs of ordered tensors of local sections in every degree. The degreewise \
`(Tⁿ M)ₓ ≅ Tⁿ(Mₓ)` is `SheafOfModules.tensorPower_stalk`; the symmetric assertions are \
`SheafOfModules.symmetricPower_stalk` and `SheafOfModules.symmetricAlgebra_stalk`; the exterior \
assertion is not carried here"]
theorem tensorAlgebra_stalk (x : ↥X) :
    ∃ cmp : ↑(TopCat.Presheaf.stalk (∐ fun n : ℕ => A.piece (n : ℤ)).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        TensorAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk M.val.presheaf x),
      ∀ (n : ℕ) (U : Opens ↥X) (hx : x ∈ U) (s : Fin n → M.val.obj (op U)),
        cmp (TopCat.Presheaf.germ (∐ fun m : ℕ => A.piece (m : ℤ)).val.presheaf U x hx
            ((Sigma.ι (fun m : ℕ => A.piece (m : ℤ)) n).val.app (op U)
              (PresheafOfModules.Hom.app (tensorAlgPieceIso A gen hA (n : ℤ)).hom.val (op U)
                (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
                    (toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj))
                    (PresheafOfModules.tensorPow n M.val)) (op U)
                  (TensorAlgebra.ιMultiPow
                    ((Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) n s))))) =
          TensorAlgebra.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n
            fun i => TopCat.Presheaf.germ M.val.presheaf U x hx (s i) :=
  ⟨tensorAlgebraStalkEquiv A gen hA x,
    fun n U hx s => tensorAlgebraStalkEquiv_germ_ιMulti A gen hA x n U hx s⟩

end TensorSheaf

end SheafOfModules

/-! ### The comparison for a package of the three algebras, and on a ringed space -/

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {G : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- For a package of the three algebras of Section 17.21, the stalk of the degree-`n` tensor
power `Tⁿ G` supplied by the package is `Tⁿ` of the stalk of `G`. -/
noncomputable def tensorPowerStalkEquiv
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G) (n : ℕ) (x : ↥X) :
    ↑(TopCat.Presheaf.stalk (A.tensor.piece (n : ℤ)).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      TensorAlgebra.gradedPiece ↑(TopCat.Presheaf.stalk Osharp.obj x) n
        ↑(TopCat.Presheaf.stalk G.val.presheaf x) :=
  SheafOfModules.tensorPowerStalkEquiv A.tensor A.tensorGenerator A.tensor_isTensorAlgebra n x

/-- For a package of the three algebras of Section 17.21, the stalk of the sheaf of modules
`tensorAlgebraSheaf` underlying `T(G)` is the tensor algebra of the stalk of `G`. -/
noncomputable def tensorAlgebraStalkEquiv
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G) (x : ↥X) :
    ↑(TopCat.Presheaf.stalk A.tensorAlgebraSheaf.val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      TensorAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk G.val.presheaf x) :=
  SheafOfModules.tensorAlgebraStalkEquiv A.tensor A.tensorGenerator A.tensor_isTensorAlgebra x

end SheafOfModules.TensorExteriorSymmetricAlgebras

namespace SheafOfModules

open AlgebraicGeometry RingedSpaceModuleAdjunction

/- The two declarations below state the ring as the stalk of `Y.sheaf.obj`, while the module they
are about -- a piece of `SheafOfModules.ringedSpaceAlgebras Y G` -- lives over the presheaf of
rings `Y.presheaf ⋙ forget₂ _ _` that `structureSheafRing Y` reduces to. Mathlib's
`PresheafOfModules` stalk-module instance is keyed on that second spelling, and reaching it from
the first needs `AlgebraicGeometry.SheafedSpace.sheaf` unfolded, which is semireducible: the
instance is synthesised for `Y.presheaf` and is *not* synthesised for `Y.sheaf.obj`, while
`inferInstanceAs` between the two succeeds, so the two are defeq and only instance *search*
cannot bridge them. Raising the projection's transparency for these two declarations is the whole
repair; the statements are untouched. The search fails because the sheaf of rings of a ringed
space is an `instance_reducible` definition rather than a `reducible` one, and the budget cannot be
raised here since this project forbids `set_option`. -/
attribute [local implicit_reducible] AlgebraicGeometry.SheafedSpace.sheaf

/-- For the chosen package `SheafOfModules.ringedSpaceAlgebras` of the three algebras of
Section 17.21, the stalk of the degree-`n` tensor power of a sheaf of modules on a ringed space is
`Tⁿ` of the stalk. -/
noncomputable def ringedSpaceTensorPowerStalkEquiv (Y : RingedSpace.{u, u})
    (G : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥Y.carrier) Y.sheaf))
    (n : ℕ) (x : ↥Y.carrier) :
    ↑(TopCat.Presheaf.stalk ((ringedSpaceAlgebras Y G).tensor.piece (n : ℤ)).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Y.sheaf.obj x)]
      ↥(TensorAlgebra.gradedPiece ↑(TopCat.Presheaf.stalk Y.sheaf.obj x) n
        ↑(TopCat.Presheaf.stalk G.val.presheaf x)) :=
  TensorExteriorSymmetricAlgebras.tensorPowerStalkEquiv (ringedSpaceAlgebras Y G) n x

/-- For the chosen package `SheafOfModules.ringedSpaceAlgebras` of the three algebras of
Section 17.21, the stalk of the tensor algebra of a sheaf of modules on a ringed space is the
tensor algebra of the stalk. -/
noncomputable def ringedSpaceTensorAlgebraStalkEquiv (Y : RingedSpace.{u, u})
    (G : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥Y.carrier) Y.sheaf))
    (x : ↥Y.carrier) :
    ↑(TopCat.Presheaf.stalk (ringedSpaceAlgebras Y G).tensorAlgebraSheaf.val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Y.sheaf.obj x)]
      TensorAlgebra ↑(TopCat.Presheaf.stalk Y.sheaf.obj x)
        ↑(TopCat.Presheaf.stalk G.val.presheaf x) :=
  TensorExteriorSymmetricAlgebras.tensorAlgebraStalkEquiv (ringedSpaceAlgebras Y G) x

end SheafOfModules

end
