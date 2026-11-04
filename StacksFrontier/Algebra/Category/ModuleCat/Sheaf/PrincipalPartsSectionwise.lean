module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import StacksFrontier.RingTheory.DifferentialOperator.PrincipalParts

/-!
# The presheaf of sectionwise principal parts

Let `φ : O₁ ⟶ O₂` be a morphism of presheaves of commutative rings on a site and let `F` be
a presheaf of `O₂`-modules. Stacks Tag 0G3U asserts that the sheaf of principal parts of
order `k` of `F^#` relative to `O₂^# / O₁^#` is the sheaf associated to the presheaf
`U ↦ Pᵏ_{O₂(U)/O₁(U)}(F(U))` of sectionwise modules of principal parts.

This file constructs that presheaf, together with its sectionwise universal differential
operator, and proves the sectionwise half of the statement: at every object `X` the pair
consisting of the value of the presheaf at `X` and the value of the operator at `X` *is* a
module of principal parts of order `k` of `F X` relative to `O₁(X) → O₂(X)`, in the sense
of `LinearMap.IsUniversalDifferentialOperatorOfOrderLE` (Stacks 09CL). The comparison with
the sheaf of principal parts of `F^#` is
`Stacks.Sheaves.PrincipalParts.principalPartsSheafification`.

## Main definitions

* `Stacks.ModuleOfPrincipalParts`: a module of principal parts of order `k` of an
  `S`-module `M` relative to a ring map `R → S`, bundled with its universal differential
  operator. `Stacks.nonempty_moduleOfPrincipalParts` is Stacks 09CK in this bundled form.
* `Stacks.Sheaves.PrincipalParts.sectionData`: a chosen such module at every object.
* `Stacks.Sheaves.PrincipalParts.sectionRestriction`: the restriction maps.
* `Stacks.Sheaves.PrincipalParts.sectionwisePrincipalParts`: the resulting presheaf of
  `O₂`-modules.
* `Stacks.Sheaves.PrincipalParts.sectionwiseUniversalOperator`: its universal differential
  operator, as a morphism of the underlying presheaves of abelian groups.

## Main results

* `LinearMap.isDifferentialOperatorOfOrderLE_of_eq_comp`: precomposing a differential
  operator of order at most `k` with a semilinear map of modules along a ring map gives
  again an operator of order at most `k`, for the scalars acting through that ring map.
* `LinearMap.existsUnique_comp_eq_of_isUniversal`: transport of a universal differential
  operator along a map of base rings — the comparison map is unique.
* `Stacks.Sheaves.PrincipalParts.existsUnique_sectionRestriction`: the characteristic
  property of the restriction maps.
* `Stacks.Sheaves.PrincipalParts.isUniversal_sectionwiseUniversalOperator` and its
  packaged form `Stacks.Sheaves.PrincipalParts.sectionwisePrincipalPartsData`: sectionwise
  universality.

## Implementation notes

The sectionwise modules are specified by the universal property of principal parts
(Stacks 09CL) rather than by a choice of quotient presentation: `sectionData` picks, at
each object, some pair `(P, D)` with the universal property, whose existence is Stacks 09CK
(`LinearMap.exists_universal_isDifferentialOperatorOfOrderLE`), and the restriction maps are
the unique maps of `existsUnique_sectionRestriction`.

Because `ModuleOfPrincipalParts` is obtained by a choice, the `R`-module structure on its
carrier would otherwise be arbitrary; the fields `op` and `isUniversal` therefore pin it to
`Module.compHom _ (algebraMap R S)`, which is the only structure compatible with the
`S`-structure. That makes the statements here definitionally comparable to ones written with
`Module.compHom _ (φ.app X).hom`.

## References

* [Stacks Project, Tag 0G3U](https://stacks.math.columbia.edu/tag/0G3U)
* [Stacks Project, Tag 09CK](https://stacks.math.columbia.edu/tag/09CK), existence of a
  module of principal parts, and [Tag 09CL](https://stacks.math.columbia.edu/tag/09CL), its
  universal property.
-/

@[expose] public section

open CategoryTheory

universe v v₁ u u₁ w₁ w₂ w₃ w₄

namespace LinearMap

/-- Precomposition with a semilinear map preserves the order of a differential operator. -/
theorem isDifferentialOperatorOfOrderLE_of_eq_comp
    {R S R' S' : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [CommRing R'] [CommRing S'] [Algebra R' S']
    {M M' N : Type*}
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup M'] [Module R' M'] [Module S' M'] [IsScalarTower R' S' M']
    [AddCommGroup N] [Module R' N] [Module S' N] [IsScalarTower R' S' N]
    [Module R N] [Module S N] [IsScalarTower R S N]
    (σ : S →+* S') (hσ : ∀ (g : S) (n : N), g • n = σ g • n)
    (u : M →+ M') (hu : ∀ (g : S) (m : M), u (g • m) = σ g • u m) :
    ∀ (k : ℕ) {D : M' →ₗ[R'] N} (_ : D.IsDifferentialOperatorOfOrderLE S' k)
      {E : M →ₗ[R] N} (_ : ∀ m, E m = D (u m)),
      E.IsDifferentialOperatorOfOrderLE S k := by
  intro k
  induction k with
  | zero =>
      intro D hD E hE g m
      rw [hE, hE, hu, hD, hσ]
  | succ k ih =>
      intro D hD E hE g
      refine ih (D := D ∘ₗ Algebra.lsmul R' R' M' (σ g) - Algebra.lsmul R' R' N (σ g) ∘ₗ D)
        (hD (σ g)) ?_
      intro m
      simp only [sub_apply, comp_apply, Algebra.lsmul_coe, hE, hu, hσ]

/-- Transport of a universal differential operator along a map of base rings. -/
theorem existsUnique_comp_eq_of_isUniversal
    {R : Type w₁} {S : Type w₂} {R' S' : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [CommRing R'] [CommRing S'] [Algebra R' S']
    {M : Type w₃} {P : Type w₄} {M' : Type*} {P' : Type (max w₂ w₃ w₄)}
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
    [AddCommGroup M'] [Module R' M'] [Module S' M'] [IsScalarTower R' S' M']
    [AddCommGroup P'] [Module R' P'] [Module S' P'] [IsScalarTower R' S' P']
    [Module R P'] [Module S P'] [IsScalarTower R S P']
    (σ : S →+* S') (ρ : R →+* R')
    (hσ : ∀ (g : S) (n : P'), g • n = σ g • n)
    (hρσ : ∀ r : R, σ (algebraMap R S r) = algebraMap R' S' (ρ r))
    (u : M →+ M') (hu : ∀ (g : S) (m : M), u (g • m) = σ g • u m)
    {k : ℕ} {D : M →ₗ[R] P} (hD : D.IsUniversalDifferentialOperatorOfOrderLE S k)
    {D' : M' →ₗ[R'] P'} (hD' : D'.IsDifferentialOperatorOfOrderLE S' k) :
    ∃! α : P →ₗ[S] P', ∀ m, α (D m) = D' (u m) := by
  have hRP' : ∀ (r : R) (n : P'), r • n = ρ r • n := by
    intro r n
    rw [← IsScalarTower.algebraMap_smul S r n, hσ, hρσ, IsScalarTower.algebraMap_smul]
  let E : M →ₗ[R] P' :=
    { toFun := fun m ↦ D' (u m)
      map_add' := fun m m' ↦ by simp
      map_smul' := fun r m ↦ by
        dsimp
        rw [← IsScalarTower.algebraMap_smul S r m, hu, hρσ,
          IsScalarTower.algebraMap_smul, map_smul, hRP'] }
  exact hD.2 E (isDifferentialOperatorOfOrderLE_of_eq_comp σ hσ u hu k hD' (E := E)
    (fun _ ↦ rfl))

end LinearMap

namespace Stacks

/-- A *module of principal parts of order `k`* of an `S`-module `M` relative to a ring map
`R → S`, packaged with its universal differential operator. -/
structure ModuleOfPrincipalParts (R : Type w₁) (S : Type w₂) (M : Type w₃) [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (k : ℕ) where
  /-- The underlying module. -/
  carrier : Type (max w₂ w₃)
  [addCommGroup : AddCommGroup carrier]
  [module : Module S carrier]
  /-- The universal differential operator of order at most `k`. -/
  op : letI : Module R carrier := Module.compHom carrier (algebraMap R S)
    M →ₗ[R] carrier
  /-- `op` exhibits `carrier` as a module of principal parts of order `k`. -/
  isUniversal :
    letI : Module R carrier := Module.compHom carrier (algebraMap R S)
    letI : IsScalarTower R S carrier := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    LinearMap.IsUniversalDifferentialOperatorOfOrderLE S k op

attribute [instance] ModuleOfPrincipalParts.addCommGroup ModuleOfPrincipalParts.module

/-- **Stacks 09CK**, in bundled form: a module of principal parts of order `k` exists. -/
instance nonempty_moduleOfPrincipalParts (R : Type w₁) (S : Type w₂) (M : Type w₃) [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (k : ℕ) : Nonempty (ModuleOfPrincipalParts R S M k) := by
  obtain ⟨P, _, i, _, tw, D, hD, h⟩ :=
    LinearMap.exists_universal_isDifferentialOperatorOfOrderLE.{w₁, w₂, w₃, max w₂ w₃}
      (R := R) (S := S) (M := M) k
  have hmod : i = Module.compHom P (algebraMap R S) :=
    Module.ext' _ _ fun r x ↦ (IsScalarTower.algebraMap_smul S r x).symm
  subst hmod
  let _ : Module R P := Module.compHom P (algebraMap R S)
  refine ⟨⟨P, D, hD, ?_⟩⟩
  intro N _ _ _ _ E hE
  obtain ⟨hinj, hrange⟩ := h N
  obtain ⟨α, hα⟩ : E ∈ Set.range (fun α : P →ₗ[S] N ↦ α.restrictScalars R ∘ₗ D) :=
    hrange ▸ hE
  refine ⟨α, fun m ↦ by rw [← hα]; rfl, fun β hβ ↦ hinj ?_⟩
  ext m
  exact (hβ m).trans (congrFun (congrArg DFunLike.coe hα) m).symm

namespace Sheaves.PrincipalParts

section Construction

variable {C : Type u₁} [Category.{v₁} C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{u}}
  [∀ X : Cᵒᵖ, Algebra (O₁.obj X) (O₂.obj X)] (φ : O₁ ⟶ O₂)
  (F : PresheafOfModules.{max u w₃} (O₂ ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
  [∀ X : Cᵒᵖ, Module (O₁.obj X) (F.obj X)]
  [∀ X : Cᵒᵖ, IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X)]
  (k : ℕ)

/-- A chosen module of principal parts of order `k` of the sections of `F` over `X`,
relative to the ring map `O₁(X) → O₂(X)`. -/
noncomputable def sectionData (X : Cᵒᵖ) :
    Stacks.ModuleOfPrincipalParts (O₁.obj X) (O₂.obj X) (F.obj X) k :=
  Classical.arbitrary _

/-- The characteristic property of the restriction maps of the presheaf of sectionwise
principal parts: there is exactly one additive map, semilinear for the restriction of
scalars, which commutes with the sectionwise universal differential operators. -/
theorem existsUnique_sectionRestriction
    (hφ : ∀ (X : Cᵒᵖ) (r : O₁.obj X),
      algebraMap (O₁.obj X) (O₂.obj X) r = (φ.app X).hom r)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ∃! a : (sectionData (O₁ := O₁) F k X).carrier →+ (sectionData (O₁ := O₁) F k Y).carrier,
      (∀ (r : O₂.obj X) (x : (sectionData (O₁ := O₁) F k X).carrier),
          a (r • x) = (O₂.map f).hom r • a x) ∧
        ∀ m : F.obj X, a ((sectionData (O₁ := O₁) F k X).op m) =
          (sectionData (O₁ := O₁) F k Y).op (F.map f m) := by
  let _ : Module (O₁.obj X) (sectionData (O₁ := O₁) F k X).carrier :=
    Module.compHom _ (algebraMap (O₁.obj X) (O₂.obj X))
  let _ : IsScalarTower (O₁.obj X) (O₂.obj X) (sectionData (O₁ := O₁) F k X).carrier :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Module (O₁.obj Y) (sectionData (O₁ := O₁) F k Y).carrier :=
    Module.compHom _ (algebraMap (O₁.obj Y) (O₂.obj Y))
  let _ : IsScalarTower (O₁.obj Y) (O₂.obj Y) (sectionData (O₁ := O₁) F k Y).carrier :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Module (O₂.obj X) (sectionData (O₁ := O₁) F k Y).carrier :=
    Module.compHom _ (O₂.map f).hom
  let _ : Module (O₁.obj X) (sectionData (O₁ := O₁) F k Y).carrier :=
    Module.compHom _ ((O₂.map f).hom.comp (algebraMap (O₁.obj X) (O₂.obj X)))
  let _ : IsScalarTower (O₁.obj X) (O₂.obj X) (sectionData (O₁ := O₁) F k Y).carrier :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  obtain ⟨α, hα, huniq⟩ := LinearMap.existsUnique_comp_eq_of_isUniversal
    (R := O₁.obj X) (S := O₂.obj X) (R' := O₁.obj Y) (S' := O₂.obj Y)
    (M := F.obj X) (P := (sectionData (O₁ := O₁) F k X).carrier)
    (M' := F.obj Y) (P' := (sectionData (O₁ := O₁) F k Y).carrier)
    (O₂.map f).hom (O₁.map f).hom (fun _ _ ↦ rfl)
    (fun r ↦ by
      rw [hφ, hφ]
      exact (ConcreteCategory.congr_hom (φ.naturality f) r).symm)
    (F.map f).hom.toAddMonoidHom (fun g m ↦ F.map_smul f g m)
    (sectionData (O₁ := O₁) F k X).isUniversal
    (sectionData (O₁ := O₁) F k Y).isUniversal.1
  refine ⟨α.toAddMonoidHom, ⟨fun r x ↦ α.map_smul r x, hα⟩, ?_⟩
  rintro a ⟨ha₁, ha₂⟩
  have hβ : ({ toFun := a, map_add' := a.map_add, map_smul' := ha₁ } :
      (sectionData (O₁ := O₁) F k X).carrier →ₗ[O₂.obj X]
        (sectionData (O₁ := O₁) F k Y).carrier) = α := huniq _ ha₂
  exact AddMonoidHom.ext fun x ↦ congrFun (congrArg DFunLike.coe hβ) x

variable (hφ : ∀ (X : Cᵒᵖ) (r : O₁.obj X),
  algebraMap (O₁.obj X) (O₂.obj X) r = (φ.app X).hom r)

/-- The restriction map of the presheaf of sectionwise principal parts: the unique
semilinear additive map commuting with the sectionwise universal operators. -/
noncomputable def sectionRestriction {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (sectionData (O₁ := O₁) F k X).carrier →+ (sectionData (O₁ := O₁) F k Y).carrier :=
  (existsUnique_sectionRestriction φ F k hφ f).choose

/-- The restriction maps of the presheaf of sectionwise principal parts are semilinear
for the restriction of scalars along `O₂`. -/
lemma sectionRestriction_smul {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : O₂.obj X)
    (x : (sectionData (O₁ := O₁) F k X).carrier) :
    sectionRestriction φ F k hφ f (r • x) =
      (O₂.map f).hom r • sectionRestriction φ F k hφ f x :=
  (existsUnique_sectionRestriction φ F k hφ f).choose_spec.1.1 r x

/-- The restriction maps commute with the sectionwise universal differential operators. -/
lemma sectionRestriction_op {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : F.obj X) :
    sectionRestriction φ F k hφ f ((sectionData (O₁ := O₁) F k X).op m) =
      (sectionData (O₁ := O₁) F k Y).op (F.map f m) :=
  (existsUnique_sectionRestriction φ F k hφ f).choose_spec.1.2 m

/-- Any semilinear additive map commuting with the sectionwise universal operators is the
restriction map. -/
lemma eq_sectionRestriction {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (a : (sectionData (O₁ := O₁) F k X).carrier →+ (sectionData (O₁ := O₁) F k Y).carrier)
    (h₁ : ∀ (r : O₂.obj X) (x : (sectionData (O₁ := O₁) F k X).carrier),
      a (r • x) = (O₂.map f).hom r • a x)
    (h₂ : ∀ m : F.obj X, a ((sectionData (O₁ := O₁) F k X).op m) =
      (sectionData (O₁ := O₁) F k Y).op (F.map f m)) :
    a = sectionRestriction φ F k hφ f :=
  (existsUnique_sectionRestriction φ F k hφ f).choose_spec.2 a ⟨h₁, h₂⟩

/-- The restriction map along an identity is the identity. -/
lemma sectionRestriction_id (X : Cᵒᵖ) :
    sectionRestriction φ F k hφ (𝟙 X) = AddMonoidHom.id _ :=
  (eq_sectionRestriction φ F k hφ (𝟙 X) (AddMonoidHom.id _)
    (fun r x ↦ by simp) (fun m ↦ by simp)).symm

/-- The restriction maps compose. -/
lemma sectionRestriction_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sectionRestriction φ F k hφ (f ≫ g) =
      (sectionRestriction φ F k hφ g).comp (sectionRestriction φ F k hφ f) :=
  (eq_sectionRestriction φ F k hφ (f ≫ g) _
    (fun r x ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, sectionRestriction_smul]
      rw [O₂.map_comp]
      rfl)
    (fun m ↦
      (congrArg (sectionRestriction φ F k hφ g) (sectionRestriction_op φ F k hφ f m)).trans
        ((sectionRestriction_op φ F k hφ g (F.map f m)).trans
          (congrArg (fun x ↦ (sectionData (O₁ := O₁) F k Z).op x)
            (PresheafOfModules.map_comp_apply F f g m).symm)))).symm

/-- The underlying presheaf of abelian groups of the presheaf of sectionwise principal
parts. -/
noncomputable def principalPartsPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{max u w₃} where
  obj X := AddCommGrpCat.of (sectionData (O₁ := O₁) F k X).carrier
  map f := AddCommGrpCat.ofHom (sectionRestriction φ F k hφ f)
  map_id X := by
    rw [sectionRestriction_id]
    rfl
  map_comp f g := by
    rw [sectionRestriction_comp]
    rfl

/-- The sections of the presheaf of sectionwise principal parts over `X` form a module
over the sections of `O₂` over `X`. -/
noncomputable instance instModulePrincipalPartsPresheaf (X : Cᵒᵖ) :
    Module ((O₂ ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj X)
      ((principalPartsPresheaf φ F k hφ).obj X) :=
  inferInstanceAs (Module (O₂.obj X) (sectionData (O₁ := O₁) F k X).carrier)

/-- The presheaf of sectionwise modules of principal parts of order `k` of `F`, relative
to `φ`. -/
noncomputable def sectionwisePrincipalParts :
    PresheafOfModules.{max u w₃} (O₂ ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  PresheafOfModules.ofPresheaf (principalPartsPresheaf φ F k hφ)
    (fun {_ _} f r m ↦ sectionRestriction_smul φ F k hφ f r m)

/-- The sectionwise universal differential operator of order at most `k`, as a morphism of
the underlying presheaves of abelian groups. -/
noncomputable def sectionwiseUniversalOperator :
    F.presheaf ⟶ (sectionwisePrincipalParts φ F k hφ).presheaf where
  app X := AddCommGrpCat.ofHom (sectionData (O₁ := O₁) F k X).op.toAddMonoidHom
  naturality := fun {_ _} f ↦ by
    ext m
    exact (sectionRestriction_op φ F k hφ f m).symm

/-- The sectionwise universal operator acts on sections as the chosen universal
differential operator. -/
@[simp]
lemma sectionwiseUniversalOperator_app_apply (X : Cᵒᵖ) (m : F.obj X) :
    ((sectionwiseUniversalOperator φ F k hφ).app X).hom m =
      (sectionData (O₁ := O₁) F k X).op m :=
  rfl

/-- **Sectionwise universality.** At every object `X`, the presheaf of sectionwise principal
parts evaluated at `X`, together with the value at `X` of the sectionwise universal
operator, is a module of principal parts of order `k` of `F X` relative to the ring map
`O₁(X) → O₂(X)`. -/
theorem isUniversal_sectionwiseUniversalOperator (X : Cᵒᵖ) :
    letI : Module (O₁.obj X) ((sectionwisePrincipalParts φ F k hφ).obj X) :=
      Module.compHom _ (algebraMap (O₁.obj X) (O₂.obj X))
    letI : IsScalarTower (O₁.obj X) (O₂.obj X)
        ((sectionwisePrincipalParts φ F k hφ).obj X) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    ∃ d : F.obj X →ₗ[O₁.obj X] (sectionwisePrincipalParts φ F k hφ).obj X,
      (∀ x, d x = ((sectionwiseUniversalOperator φ F k hφ).app X).hom x) ∧
        d.IsUniversalDifferentialOperatorOfOrderLE (O₂.obj X) k :=
  ⟨(sectionData (O₁ := O₁) F k X).op, fun _ ↦ rfl,
    (sectionData (O₁ := O₁) F k X).isUniversal⟩

end Construction

/-- For a morphism `φ : O₁ ⟶ O₂` of presheaves of commutative rings on a site and a
presheaf `F` of `O₂`-modules, there are a presheaf `P` of `O₂`-modules and a morphism
`D : F.presheaf ⟶ P.presheaf` of the underlying presheaves of abelian groups such that, at
every object `X`, the pair `(P X, D X)` is a module of principal parts of order `k` of
`F X` relative to `O₁(X) → O₂(X)`. -/
noncomputable def sectionwisePrincipalPartsData {C : Type u₁} [Category.{v₁} C]
    {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : O₁ ⟶ O₂)
    (F : PresheafOfModules.{max u u₁ v₁ v}
      (O₂ ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (k : ℕ) :
    Σ' P : PresheafOfModules.{max u u₁ v₁ v}
        (O₂ ⋙ forget₂ CommRingCat.{u} RingCat.{u}),
      Σ' D : F.presheaf ⟶ P.presheaf,
        ∀ X : Cᵒᵖ,
          letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
          letI : Module (O₁.obj X) (F.obj X) :=
            Module.compHom (F.obj X) (φ.app X).hom
          letI : Module (O₁.obj X) (P.obj X) :=
            Module.compHom (P.obj X) (φ.app X).hom
          letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
            IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
          letI : IsScalarTower (O₁.obj X) (O₂.obj X) (P.obj X) :=
            IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
          ∃ d : F.obj X →ₗ[O₁.obj X] P.obj X,
            (∀ x, d x = (D.app X).hom x) ∧
              d.IsUniversalDifferentialOperatorOfOrderLE (O₂.obj X) k := by
  letI : ∀ X : Cᵒᵖ, Algebra (O₁.obj X) (O₂.obj X) := fun X ↦ (φ.app X).hom.toAlgebra
  letI : ∀ X : Cᵒᵖ, Module (O₁.obj X) (F.obj X) :=
    fun X ↦ Module.compHom (F.obj X) (φ.app X).hom
  letI : ∀ X : Cᵒᵖ, IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    fun _ ↦ IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hφ : ∀ (X : Cᵒᵖ) (r : O₁.obj X),
      algebraMap (O₁.obj X) (O₂.obj X) r = (φ.app X).hom r := fun _ _ ↦ rfl
  exact ⟨sectionwisePrincipalParts.{v₁, u, u₁, max u₁ v₁ v} φ F k hφ,
    sectionwiseUniversalOperator.{v₁, u, u₁, max u₁ v₁ v} φ F k hφ,
    fun X ↦ isUniversal_sectionwiseUniversalOperator.{v₁, u, u₁, max u₁ v₁ v} φ F k hφ X⟩

end Sheaves.PrincipalParts

end Stacks

end
