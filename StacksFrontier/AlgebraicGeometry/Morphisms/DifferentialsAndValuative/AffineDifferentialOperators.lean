module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DifferentialOperators
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialOperatorsOrder
public import StacksFrontier.RingTheory.DifferentialOperator.Defs
public import StacksFrontier.RingTheory.DifferentialOperator.Localization
public import StacksFrontier.Topology.Sheaves.Basis.Equivalence

/-!
# Differential operators on affine schemes

For a ring map `R → A`, differential operators between modules on `Spec A` are
completely determined by their action on global sections, provided that the source
module is quasi-coherent.

## Main definitions

* `extendAdditive`: the morphism of presheaves extending a differential operator on
  global sections of a quasi-coherent module.
* `sectionwiseDiffOpEquiv`: evaluation on global sections, as a bijection from sectionwise
  differential operators to differential operators on global sections.

## Main results

* `globalDiffOpEquiv`: differential operators on an affine scheme correspond to
  differential operators between their modules of global sections.

## Implementation notes

The bijection is an equivalence of the subtypes of operators satisfying the order bound,
together with the statement that its forward map is evaluation on global sections. The scalar
actions on global sections are transported through the canonical isomorphism
`Γ(Spec A, ⊤) ≅ A`.

## References

* [Stacks Project, Tag 0G44](https://stacks.math.columbia.edu/tag/0G44)
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AffineDiffOp

open TopologicalSpace

/-! ### Sections over an open of `PrimeSpectrum A`

The module and algebra structures on the sections of sheaves on `Spec A`, over an open of
`Opens (PrimeSpectrum A)`. -/

/-- Mathlib's module structure on the sections of a sheaf of modules on `Spec A`. -/
@[instance_reducible]
noncomputable def moduleSectionsAux {A : CommRingCat.{u}} (F : (Spec A).Modules)
    (V : (Spec A).Opens) : Module Γ(Spec A, V) Γ(F, V) := inferInstance

/-- Mathlib's algebra structure on the sections of the structure sheaf of `Spec A`. -/
@[instance_reducible]
noncomputable def algebraSectionsAux {A : CommRingCat.{u}} (V : (Spec A).Opens) :
    Algebra A Γ(Spec A, V) := inferInstance

/-- Mathlib's `A`-module structure on the sections of a sheaf of modules on `Spec A`. -/
@[instance_reducible]
noncomputable def moduleBaseSectionsAux {A : CommRingCat.{u}} (F : (Spec A).Modules)
    (V : (Spec A).Opens) : Module A Γ(F, V) := inferInstance

/-- Mathlib's scalar tower on the sections of a sheaf of modules on `Spec A`. -/
theorem isScalarTowerSectionsAux {A : CommRingCat.{u}} (F : (Spec A).Modules)
    (V : (Spec A).Opens) : IsScalarTower A Γ(Spec A, V) Γ(F, V) := inferInstance

/-- The basic open subset of `Spec A` attached to an element of `A`, as an open of `Spec A`. -/
def specBasicOpen {A : CommRingCat.{u}} (f : A) : (Spec A).Opens := PrimeSpectrum.basicOpen f

/-- `specBasicOpen f` is the basic open `PrimeSpectrum.basicOpen f`. -/
@[simp]
theorem specBasicOpen_eq {A : CommRingCat.{u}} (f : A) :
    specBasicOpen f = PrimeSpectrum.basicOpen f := rfl

/-- The basic opens form a basis of the topology of `Spec A`. -/
theorem isBasis_specBasicOpen {A : CommRingCat.{u}} :
    TopologicalSpace.Opens.IsBasis (Set.range (specBasicOpen (A := A))) :=
  PrimeSpectrum.isBasis_basic_opens

/-- The sections of the structure sheaf of `Spec A` over a basic open are the localization of
`A` away from the defining element. -/
instance isLocalizationSpecBasicOpen {A : CommRingCat.{u}} (f : A) :
    IsLocalization (Submonoid.powers f) Γ(Spec A, specBasicOpen f) :=
  StructureSheaf.IsLocalization.to_basicOpen A f

/-- Restriction of sections of a presheaf of modules is semilinear, stated for the underlying
additive-group-valued presheaf. -/
theorem presheaf_map_smul {C : Type*} [Category* C] {O : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} O) {U V : Cᵒᵖ} (i : U ⟶ V) (r : O.obj U) (m : M.obj U) :
    M.presheaf.map i (r • m) = O.map i r • M.presheaf.map i m :=
  M.map_smul i r m

/-- Restriction of sections of a sheaf of modules on a scheme is semilinear, stated for
`Scheme.Modules.presheaf`. -/
theorem modules_presheaf_map_smul {X : Scheme.{u}} (F : X.Modules) {U V : X.Opens}
    (i : V ≤ U) (r : Γ(X, U)) (m : Γ(F, U)) :
    F.presheaf.map (homOfLE i).op (r • m) =
      X.presheaf.map (homOfLE i).op r • F.presheaf.map (homOfLE i).op m :=
  F.val.map_smul _ r m

/-- The sections of a sheaf of modules on `Spec A` are a module over the sections of the
structure sheaf, with the open written at `Opens (PrimeSpectrum A)`. -/
noncomputable instance moduleSections {A : CommRingCat.{u}} (F : (Spec A).Modules)
    (U : Opens (PrimeSpectrum A)) : Module Γ(Spec A, U) Γ(F, U) := moduleSectionsAux F U

/-- The sections of the structure sheaf of `Spec A` form an `A`-algebra, with the open written
at `Opens (PrimeSpectrum A)`. -/
noncomputable instance algebraSections {A : CommRingCat.{u}} (U : Opens (PrimeSpectrum A)) :
    Algebra A Γ(Spec A, U) := algebraSectionsAux U

/-- The sections of a sheaf of modules on `Spec A` form an `A`-module, with the open written at
`Opens (PrimeSpectrum A)`. -/
noncomputable instance moduleBaseSections {A : CommRingCat.{u}} (F : (Spec A).Modules)
    (U : Opens (PrimeSpectrum A)) : Module A Γ(F, U) := moduleBaseSectionsAux F U

/-- The scalar tower on the sections of a sheaf of modules on `Spec A`, with the open written at
`Opens (PrimeSpectrum A)`. -/
instance isScalarTowerSections {A : CommRingCat.{u}} (F : (Spec A).Modules)
    (U : Opens (PrimeSpectrum A)) : IsScalarTower A Γ(Spec A, U) Γ(F, U) :=
  isScalarTowerSectionsAux F U

section

open TopologicalSpace

/-- Every section of the presheaf pullback of `O` along `f` over an open `U` is the restriction
to `U` of the image of a section of `O` over some open `V` with `U ≤ f⁻¹ V`. -/
lemma pullback_exists_rep {X Y : TopCat.{u}} (f : X ⟶ Y)
    (O : TopCat.Presheaf RingCat.{u} Y) (U : Opens X)
    (a : ((TopCat.Presheaf.pullback RingCat f).obj O).obj (.op U)) :
    ∃ (V : Opens Y) (h : U ≤ (Opens.map f).obj V) (b : O.obj (.op V)),
      ((TopCat.Presheaf.pullback RingCat f).obj O).map (homOfLE h).op
        (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f).unit.app O).app
          (.op V) b) = a := by
  obtain ⟨V, b, hb⟩ := Limits.Concrete.isColimit_exists_rep _
    ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit O (.op U)) a
  refine ⟨V.left.unop, V.hom.unop.le, b, ?_⟩
  exact hb

/-- The adjoint of a morphism `g : O ⟶ f_* Q` of sheaves under the sheaf pullback-pushforward
adjunction is the comparison isomorphism `TopCat.Sheaf.pullbackIso` followed by the
sheafification of the adjoint of `g` under the presheaf pullback-pushforward adjunction. -/
lemma pullback_lift_eq {X Y : TopCat.{u}} (f : X ⟶ Y)
    (O : TopCat.Sheaf RingCat.{u} Y) (Q : TopCat.Sheaf RingCat.{u} X)
    (g : O ⟶ (TopCat.Sheaf.pushforward RingCat f).obj Q) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat f).homEquiv _ _).symm g =
      (TopCat.Sheaf.pullbackIso RingCat f).hom.app O ≫
        ((sheafificationAdjunction (Opens.grothendieckTopology X) RingCat).homEquiv _ _).symm
          (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f).homEquiv _ _).symm
            g.hom) := by
  apply (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat f).homEquiv _ _ |>.injective
  simp only [Equiv.apply_symm_apply]
  rw [(TopCat.Sheaf.pullbackPushforwardAdjunction RingCat f).homEquiv_naturality_right
    ((TopCat.Sheaf.pullbackIso RingCat f).hom.app O)
    (((sheafificationAdjunction (Opens.grothendieckTopology X) RingCat).homEquiv _ _).symm
      (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f).homEquiv _ _).symm g.hom))]
  simp only [TopCat.Sheaf.pullbackIso, TopCat.Sheaf.pullbackPushforwardAdjunction,
    Functor.sheafPullbackConstruction.sheafPullbackIso]
  refine Eq.trans ?_ (congrArg (fun m => m ≫ (TopCat.Sheaf.pushforward RingCat f).map
      (((sheafificationAdjunction (Opens.grothendieckTopology X) RingCat).homEquiv _ _).symm
        (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f).homEquiv _ _).symm g.hom)))
    (Adjunction.homEquiv_leftAdjointUniq_hom_app
      (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat f)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) RingCat
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) O)).symm
  refine Eq.trans ?_ (Adjunction.homEquiv_unit ..)
  apply Sheaf.hom_ext
  simp only [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
    Adjunction.restrictFullyFaithful, Adjunction.comp_homEquiv,
    Equiv.trans, Iso.homCongr, Functor.FullyFaithful.homEquiv,
    TopCat.Presheaf.pullbackPushforwardAdjunction]
  show g.hom = (((Opens.map f).op.lanAdjunction RingCat).homEquiv _ _)
    (((sheafificationAdjunction (Opens.grothendieckTopology X) RingCat).homEquiv _ _)
      (((sheafificationAdjunction (Opens.grothendieckTopology X) RingCat).homEquiv _ _).symm
        ((((Opens.map f).op.lanAdjunction RingCat).homEquiv _ _).symm g.hom)))
  simp only [Equiv.apply_symm_apply]
  exact (Equiv.apply_symm_apply _ _).symm

/-- Let `g : O ⟶ f_* Q` be a morphism of sheaves. Locally around each point of `U`, the image
of a section of the pullback of `O` over `U` under the adjoint of `g` is the restriction of the
image under `g` of a section of `O`. -/
lemma pullback_image_locally {X Y : TopCat.{u}} (f : X ⟶ Y)
    (O : TopCat.Sheaf RingCat.{u} Y) (Q : TopCat.Sheaf RingCat.{u} X)
    (g : O ⟶ (TopCat.Sheaf.pushforward RingCat f).obj Q)
    (U : Opens X) (a : ((TopCat.Sheaf.pullback RingCat f).obj O).obj.obj (.op U))
    (x : X) (hx : x ∈ U) :
    ∃ (W : Opens X) (hW : W ≤ U) (V : Opens Y)
      (hV : W ≤ (Opens.map f).obj V) (b : O.obj.obj (.op V)), x ∈ W ∧
      Q.obj.map (homOfLE hW).op
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat f).homEquiv _ _).symm
          g).hom.app (.op U) a) =
      Q.obj.map (homOfLE hV).op (g.hom.app (.op V) b) := by
  let P := (TopCat.Presheaf.pullback RingCat f).obj O.obj
  let e := (TopCat.Sheaf.pullbackIso RingCat f).app O
  let ψ := ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f).homEquiv _ _).symm g.hom
  let L := ((sheafificationAdjunction (Opens.grothendieckTopology X) RingCat).homEquiv _ _).symm ψ
  obtain ⟨W, hW, ⟨b, hb⟩, hxW⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff (toSheafify (Opens.grothendieckTopology X) P)).mp
      (by change CategoryTheory.Presheaf.IsLocallySurjective _ _; infer_instance)
      U (e.hom.hom.app (.op U) a) x hx
  obtain ⟨V, hV, c, hc⟩ := pullback_exists_rep f O.obj W b
  refine ⟨W, hW, V, hV, c, hxW, ?_⟩
  rw [pullback_lift_eq]
  show Q.obj.map (homOfLE hW).op (L.hom.app (.op U) (e.hom.hom.app (.op U) a)) = _
  rw [show Q.presheaf.map (homOfLE hW).op (L.hom.app (.op U) (e.hom.hom.app (.op U) a)) =
      L.hom.app (.op W) ((sheafify (Opens.grothendieckTopology X) P).map (homOfLE hW).op
        (e.hom.hom.app (.op U) a)) from
    (ConcreteCategory.congr_hom (L.hom.naturality (homOfLE hW).op)
      (e.hom.hom.app (.op U) a)).symm]
  change (toSheafify (Opens.grothendieckTopology X) P).app (.op W) b =
    (sheafify (Opens.grothendieckTopology X) P).map (homOfLE hW).op
      (e.hom.hom.app (.op U) a) at hb
  rw [← hb]
  show (toSheafify (Opens.grothendieckTopology X) P ≫ L.hom).app (.op W) b = _
  have ht : toSheafify (Opens.grothendieckTopology X) P ≫ L.hom = ψ :=
    (sheafificationAdjunction (Opens.grothendieckTopology X) RingCat).homEquiv _ _
      |>.apply_symm_apply ψ
  rw [ht, ← hc, ← ConcreteCategory.comp_apply, ψ.naturality, ConcreteCategory.comp_apply]
  have he : (TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f).unit.app O.obj ≫
      (TopCat.Presheaf.pushforward RingCat f).map ψ = g.hom :=
    (TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f).homEquiv _ _ |>.apply_symm_apply g.hom
  exact congrArg (fun t => Q.obj.map (homOfLE hV).op (t.app (.op V) c)) he

/-- The map on sections induced by `Spec.map f` sends the image of `r : R` to the image of
`f r`. -/
lemma specMap_algebraMap {R A : CommRingCat.{u}} (f : R ⟶ A)
    (V : (Spec R).Opens) (W : (Spec A).Opens) (e : W ≤ Spec.map f ⁻¹ᵁ V) (r : R) :
    (Spec.map f).appLE V W e (algebraMap R Γ(Spec R, V) r) =
      algebraMap A Γ(Spec A, W) (f r) := by
  have h := congrArg (fun m => m.hom r) (StructureSheaf.toOpen_comp_comap f.hom V)
  exact congrArg (fun a => (Spec A).presheaf.map (homOfLE e).op a) h

/-- If an additive map `D` commutes with multiplication by `a` and by `b`, multiplication by
`b` is injective on the target, and `c * b = a`, then `D` commutes with multiplication by
`c`. -/
lemma commutes_of_mul {S M N : Type*} [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module S M] [Module S N]
    (D : M →+ N) (a b c : S) (ha : ∀ x, D (a • x) = a • D x)
    (hb : ∀ x, D (b • x) = b • D x)
    (hinj : Function.Injective fun x : N => b • x) (he : c * b = a) (x : M) :
    D (c • x) = c • D x := by
  apply hinj
  show b • D (c • x) = b • (c • D x)
  rw [← hb, smul_smul, mul_comm b c, he, ha, smul_smul, mul_comm b c, he]

/-- A morphism of presheaves `F ⟶ G` of modules on `Spec A` commuting with the action of `R`
on every open commutes with the action of the sections of the structure sheaf of `Spec R`
through `Spec.map f`. -/
lemma natural_commutes_appLE {R A : CommRingCat.{u}} (f : R ⟶ A)
    (F G : (Spec A).Modules) (D : F.presheaf ⟶ G.presheaf)
    (hD : ∀ (r : R) (W : (Spec A).Opens) (x : Γ(F, W)),
      D.app (.op W) (f r • x) = f r • D.app (.op W) x)
    (V : (Spec R).Opens) (W : (Spec A).Opens) (e : W ≤ Spec.map f ⁻¹ᵁ V)
    (a : Γ(Spec R, V)) (s : Γ(F, W)) :
    D.app (.op W) ((Spec.map f).appLE V W e a • s) =
      (Spec.map f).appLE V W e a • D.app (.op W) s := by
  apply TopCat.Presheaf.IsSheaf.section_ext G.isSheaf
  intro x hx
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hr⟩ :=
    isBasis_specBasicOpen.exists_subset_of_mem_open
      (show PrimeSpectrum.comap f.hom x ∈ V from e hx) V.2
  let W' := W ⊓ Spec.map f ⁻¹ᵁ specBasicOpen r
  have hW : W' ≤ W := inf_le_left
  have he : W' ≤ Spec.map f ⁻¹ᵁ specBasicOpen r := inf_le_right
  have hxW : x ∈ W' := ⟨hx, hxr⟩
  refine ⟨W', hW, hxW, ?_⟩
  let a' : Γ(Spec R, specBasicOpen r) := (Spec R).presheaf.map (homOfLE hr).op a
  obtain ⟨⟨b, t⟩, ht⟩ := IsLocalization.surj (Submonoid.powers r) a'
  obtain ⟨n, hn⟩ := t.2
  have hreg : Function.Injective fun y : Γ(G, W') => (f t : A) • y := by
    rw [← hn, map_pow]
    exact (Scheme.Modules.isSMulRegular_of_le_basicOpen (M := G)
      (show W' ≤ specBasicOpen (f r) from he)).pow n
  have hres : (Spec A).presheaf.map (homOfLE hW).op ((Spec.map f).appLE V W e a) =
      (Spec.map f).appLE (specBasicOpen r) W' he a' := by
    have h₁ := (Spec.map f).appLE_map e (homOfLE hW).op
    have h₂ := (Spec.map f).map_appLE he (homOfLE hr).op
    exact (congrArg (fun m => m.hom a) h₁).trans (congrArg (fun m => m.hom a) h₂).symm
  have hmul : (Spec.map f).appLE (specBasicOpen r) W' he a' *
      algebraMap A Γ(Spec A, W') (f t) = algebraMap A Γ(Spec A, W') (f b) := by
    have h := congrArg (fun z => (Spec.map f).appLE (specBasicOpen r) W' he z) ht
    simpa only [map_mul, specMap_algebraMap] using h
  have hnat (z : Γ(F, W)) := congrArg (fun m => m.hom z) (D.naturality (homOfLE hW).op)
  change ∀ z, D.app (.op W') (F.presheaf.map (homOfLE hW).op z) =
    G.presheaf.map (homOfLE hW).op (D.app (.op W) z) at hnat
  show G.presheaf.map (homOfLE hW).op (D.app (.op W) (_ • s)) =
    G.presheaf.map (homOfLE hW).op (_ • D.app (.op W) s)
  rw [← hnat, modules_presheaf_map_smul F, modules_presheaf_map_smul G, ← hnat, hres]
  apply commutes_of_mul (D.app (.op W')).hom
    (algebraMap A Γ(Spec A, W') (f b)) (algebraMap A Γ(Spec A, W') (f t)) _
  · intro z
    simpa only [IsScalarTower.algebraMap_smul] using hD b W' z
  · intro z
    simpa only [IsScalarTower.algebraMap_smul] using hD t W' z
  · simpa only [IsScalarTower.algebraMap_smul] using hreg
  · exact hmul

/-- A differential operator of order at most `k` over an `S`-algebra `T` is a differential
operator of order at most `k` over `S`. -/
lemma order_restrict {S T M N : Type*} [CommRing S] [CommRing T]
    [Algebra S T] [AddCommGroup M] [AddCommGroup N]
    [Module S M] [Module T M] [IsScalarTower S T M]
    [Module S N] [Module T N] [IsScalarTower S T N]
    {D : M →ₗ[ℤ] N} {k : ℕ} (hD : D.IsDifferentialOperatorOfOrderLE T k) :
    D.IsDifferentialOperatorOfOrderLE S k := by
  induction k generalizing D with
  | zero =>
    intro s m
    simpa only [IsScalarTower.algebraMap_smul] using hD (algebraMap S T s) m
  | succ k ih =>
    intro s
    apply ih
    have hm : Algebra.lsmul ℤ ℤ M (algebraMap S T s) = Algebra.lsmul ℤ ℤ M s := by
      ext x
      exact IsScalarTower.algebraMap_smul T s x
    have hn : Algebra.lsmul ℤ ℤ N (algebraMap S T s) = Algebra.lsmul ℤ ℤ N s := by
      ext x
      exact IsScalarTower.algebraMap_smul T s x
    simpa only [hm, hn] using hD (algebraMap S T s)

/-- An `S`-linear map composed after a differential operator of order at most `k` is a
differential operator of order at most `k`. -/
lemma order_postcomp {S M N P : Type*} [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module S M] [Module S N] [Module S P]
    {D : M →ₗ[ℤ] N} {k : ℕ} (hD : D.IsDifferentialOperatorOfOrderLE S k)
    (g : N →ₗ[S] P) :
    (g.restrictScalars ℤ ∘ₗ D).IsDifferentialOperatorOfOrderLE S k := by
  induction k generalizing D with
  | zero =>
    intro s x
    show g (D (s • x)) = s • g (D x)
    rw [hD, map_smul]
  | succ k ih =>
    intro s
    have heq :
        (g.restrictScalars ℤ ∘ₗ D) ∘ₗ Algebra.lsmul ℤ ℤ M s -
          Algebra.lsmul ℤ ℤ P s ∘ₗ (g.restrictScalars ℤ ∘ₗ D) =
        g.restrictScalars ℤ ∘ₗ
          (D ∘ₗ Algebra.lsmul ℤ ℤ M s - Algebra.lsmul ℤ ℤ N s ∘ₗ D) := by
      ext x
      simp
    rw [heq]
    exact ih (hD s)

/-- A differential operator of order at most `k` composed after an `S`-linear map is a
differential operator of order at most `k`. -/
lemma order_precomp {S M N P : Type*} [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module S M] [Module S N] [Module S P]
    {D : N →ₗ[ℤ] P} {k : ℕ} (hD : D.IsDifferentialOperatorOfOrderLE S k)
    (f : M →ₗ[S] N) :
    (D ∘ₗ f.restrictScalars ℤ).IsDifferentialOperatorOfOrderLE S k := by
  induction k generalizing D with
  | zero =>
    intro s x
    show D (f (s • x)) = s • D (f x)
    rw [map_smul, hD]
  | succ k ih =>
    intro s
    have heq :
        (D ∘ₗ f.restrictScalars ℤ) ∘ₗ Algebra.lsmul ℤ ℤ M s -
          Algebra.lsmul ℤ ℤ P s ∘ₗ (D ∘ₗ f.restrictScalars ℤ) =
        (D ∘ₗ Algebra.lsmul ℤ ℤ N s - Algebra.lsmul ℤ ℤ P s ∘ₗ D) ∘ₗ
          f.restrictScalars ℤ := by
      ext x
      simp
    rw [heq]
    exact ih (hD s)

/-- Let `f : M → M'` be a localization at `T` and let the elements of `T` act injectively on
`N`. Two differential operators `M' → N` of order at most `k` that agree on the image of `f`
are equal. -/
lemma order_ext_localized {S M M' N : Type*} [CommRing S]
    [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N]
    [Module S M] [Module S M'] [Module S N]
    (T : Submonoid S) (f : M →ₗ[S] M') [IsLocalizedModule T f]
    (hinj : ∀ s : T, Function.Injective fun x : N => (s : S) • x)
    {k : ℕ} {D E : M' →ₗ[ℤ] N}
    (hD : D.IsDifferentialOperatorOfOrderLE S k)
    (hE : E.IsDifferentialOperatorOfOrderLE S k)
    (he : ∀ m, D (f m) = E (f m)) : D = E := by
  induction k generalizing D E with
  | zero =>
    ext x
    obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj T f x
    apply hinj s
    show (s : S) • D x = (s : S) • E x
    rw [← hD, ← hE, ← Submonoid.smul_def, hs, he]
  | succ k ih =>
    have hc (s : S) :
        D ∘ₗ Algebra.lsmul ℤ ℤ M' s - Algebra.lsmul ℤ ℤ N s ∘ₗ D =
        E ∘ₗ Algebra.lsmul ℤ ℤ M' s - Algebra.lsmul ℤ ℤ N s ∘ₗ E := by
      apply ih (hD s) (hE s)
      intro m
      show D (s • f m) - s • D (f m) = E (s • f m) - s • E (f m)
      rw [← map_smul, he, he]
    ext x
    obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj T f x
    apply hinj s
    have h := LinearMap.congr_fun (hc s) x
    change D ((s : S) • x) - (s : S) • D x =
      E ((s : S) • x) - (s : S) • E x at h
    rw [← Submonoid.smul_def, hs, he] at h
    exact sub_right_injective h

/-- Let `f : M → M'` be a localization at `T`, with `S'` the localization of `S` at `T`. For a
differential operator `D : M → N` of order at most `k` over `S` and an `S`-linear map
`g : N → N'` to an `S'`-module, there is a unique differential operator `E : M' → N'` of order
at most `k` over `S'` with `E ∘ f = g ∘ D`. -/
lemma existsUnique_extension_to
    {S S' M M' N N' : Type*} [CommRing S] [CommRing S'] [Algebra S S']
    [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [AddCommGroup N']
    [Module S M] [Module S M'] [Module S' M'] [IsScalarTower S S' M']
    [Module S N] [Module S N'] [Module S' N'] [IsScalarTower S S' N']
    (T : Submonoid S) [IsLocalization T S']
    (f : M →ₗ[S] M') [IsLocalizedModule T f]
    {k : ℕ} {D : M →ₗ[ℤ] N} (hD : D.IsDifferentialOperatorOfOrderLE S k)
    (g : N →ₗ[S] N') :
    ∃! E : M' →ₗ[ℤ] N', E.IsDifferentialOperatorOfOrderLE S' k ∧
      E ∘ₗ f.restrictScalars ℤ = g.restrictScalars ℤ ∘ₗ D := by
  have : IsLocalizedModule T (LinearMap.id : N' →ₗ[S] N') :=
    isLocalizedModule_id T N' S'
  simpa only [LinearMap.restrictScalars_id, LinearMap.id_comp] using
    (order_postcomp hD g).existsUnique_extension (S' := S') T f (LinearMap.id : N' →ₗ[S] N')

/-- For quasi-coherent `F` on `Spec A`, restriction from `⊤` to `specBasicOpen f` is the
localization of `Γ(F, ⊤)` away from `f`. -/
private theorem isLocalizedModule_away_restrict_top {A : CommRingCat.{u}} (F : (Spec A).Modules)
    [F.IsQuasicoherent] (f : A) :
    IsLocalizedModule.Away f (((modulesSpecToSheaf.obj F).obj.map
      (homOfLE (le_top : specBasicOpen f ≤ ⊤)).op).hom : Γ(F, ⊤) →ₗ[A] Γ(F, specBasicOpen f)) :=
  (isIso_fromTildeΓ_iff_isLocalizing F).mp
    (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent F) f

/-- Elements of `Submonoid.powers f` act injectively on the sections of a module `G` over a basic
open contained in `specBasicOpen f`. -/
private theorem smul_injective_powers_of_le {A : CommRingCat.{u}} (G : (Spec A).Modules)
    {f g : A} (hfg : specBasicOpen g ≤ specBasicOpen f) (s : Submonoid.powers f) :
    Function.Injective fun x : Γ(G, specBasicOpen g) => (s : A) • x := by
  obtain ⟨n, hn⟩ := s.2
  rw [← hn]
  exact (Scheme.Modules.isSMulRegular_of_le_basicOpen (M := G) hfg).pow n

/-- For quasi-coherent `F` on `Spec A`, the extension of a differential operator
`D : Γ(F, ⊤) → Γ(G, ⊤)` of order at most `k` over `A` to the differential operator of order at
most `k` on sections over the basic open `specBasicOpen f` that is compatible with restriction
from `⊤`. -/
noncomputable def basicExtension
    {A : CommRingCat.{u}} (F G : (Spec A).Modules)
    [F.IsQuasicoherent] (k : ℕ) (D : Γ(F, ⊤) →ₗ[ℤ] Γ(G, ⊤))
    (hD : D.IsDifferentialOperatorOfOrderLE A k) (f : A) :
    {E : Γ(F, specBasicOpen f) →ₗ[ℤ] Γ(G, specBasicOpen f) //
      E.IsDifferentialOperatorOfOrderLE Γ(Spec A, specBasicOpen f) k ∧
      ∀ x, E (F.presheaf.map (homOfLE le_top).op x) =
        G.presheaf.map (homOfLE le_top).op (D x)} := by
  let fm : Γ(F, ⊤) →ₗ[A] Γ(F, specBasicOpen f) := ((modulesSpecToSheaf.obj F).obj.map
    (homOfLE (le_top : specBasicOpen f ≤ ⊤)).op).hom
  let gn : Γ(G, ⊤) →ₗ[A] Γ(G, specBasicOpen f) := ((modulesSpecToSheaf.obj G).obj.map
    (homOfLE (le_top : specBasicOpen f ≤ ⊤)).op).hom
  have : IsLocalizedModule.Away f fm :=
    (isIso_fromTildeΓ_iff_isLocalizing F).mp
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent F) f
  let h := existsUnique_extension_to
    (S' := Γ(Spec A, specBasicOpen f)) (Submonoid.powers f) fm hD gn
  exact ⟨Classical.choose h, (Classical.choose_spec h).1.1,
    fun x => LinearMap.congr_fun (Classical.choose_spec h).1.2 x⟩

/-- The operators `basicExtension` commute with restriction from `specBasicOpen f` to a smaller
basic open `specBasicOpen g`. -/
lemma basicExtension_naturality
    {A : CommRingCat.{u}} (F G : (Spec A).Modules) [F.IsQuasicoherent]
    (k : ℕ) (D : Γ(F, ⊤) →ₗ[ℤ] Γ(G, ⊤))
    (hD : D.IsDifferentialOperatorOfOrderLE A k) (f g : A)
    (hfg : specBasicOpen g ≤ specBasicOpen f)
    (x : Γ(F, specBasicOpen f)) :
    (basicExtension F G k D hD g).1 (F.presheaf.map (homOfLE hfg).op x) =
      G.presheaf.map (homOfLE hfg).op ((basicExtension F G k D hD f).1 x) := by
  let fm : Γ(F, ⊤) →ₗ[A] Γ(F, specBasicOpen f) :=
    ((modulesSpecToSheaf.obj F).obj.map (homOfLE le_top).op).hom
  have : IsLocalizedModule.Away f fm := isLocalizedModule_away_restrict_top F f
  let fr : Γ(F, specBasicOpen f) →ₗ[A] Γ(F, specBasicOpen g) :=
    ((modulesSpecToSheaf.obj F).obj.map (homOfLE hfg).op).hom
  let gr : Γ(G, specBasicOpen f) →ₗ[A] Γ(G, specBasicOpen g) :=
    ((modulesSpecToSheaf.obj G).obj.map (homOfLE hfg).op).hom
  have he := order_ext_localized (Submonoid.powers f) fm (smul_injective_powers_of_le G hfg)
    (order_precomp (order_restrict (S := A) (basicExtension F G k D hD g).2.1) fr)
    (order_postcomp (order_restrict (S := A) (basicExtension F G k D hD f).2.1) gr) ?_
  · exact LinearMap.congr_fun he x
  · intro m
    show (basicExtension F G k D hD g).1
        (F.presheaf.map (homOfLE hfg).op (F.presheaf.map (homOfLE le_top).op m)) =
      G.presheaf.map (homOfLE hfg).op
        ((basicExtension F G k D hD f).1 (F.presheaf.map (homOfLE le_top).op m))
    rw [(basicExtension F G k D hD f).2.2]
    simp only [← Functor.map_comp_apply]
    exact (basicExtension F G k D hD g).2.2 m

/-- For quasi-coherent `F` on `Spec A`, the morphism of presheaves of abelian groups `F ⟶ G`
whose component over each basic open `specBasicOpen f` is `basicExtension F G k D hD f`. -/
noncomputable def extendAdditive
    {A : CommRingCat.{u}} (F G : (Spec A).Modules) [F.IsQuasicoherent]
    (k : ℕ) (D : Γ(F, ⊤) →ₗ[ℤ] Γ(G, ⊤))
    (hD : D.IsDifferentialOperatorOfOrderLE A k) : F.presheaf ⟶ G.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom F.presheaf ((SheafOfModules.toSheaf _).obj G)
    isBasis_specBasicOpen
    { app f := AddCommGrpCat.ofHom (basicExtension F G k D hD f.unop).1.toAddMonoidHom
      naturality f g i := by
        ext x
        exact basicExtension_naturality F G k D hD f.unop g.unop i.unop.hom.le x }

/-- Over a basic open `specBasicOpen f`, `extendAdditive` is `basicExtension`. -/
lemma extendAdditive_basic
    {A : CommRingCat.{u}} (F G : (Spec A).Modules) [F.IsQuasicoherent]
    (k : ℕ) (D : Γ(F, ⊤) →ₗ[ℤ] Γ(G, ⊤))
    (hD : D.IsDifferentialOperatorOfOrderLE A k) (f : A)
    (x : Γ(F, specBasicOpen f)) :
    (extendAdditive F G k D hD).app (.op (specBasicOpen f)) x =
      (basicExtension F G k D hD f).1 x := by
  let e := TopCat.Sheaf.restrictHomEquivHom F.presheaf ((SheafOfModules.toSheaf _).obj G)
    isBasis_specBasicOpen
  have h := e.symm_apply_apply
    { app f := AddCommGrpCat.ofHom (basicExtension F G k D hD f.unop).1.toAddMonoidHom
      naturality f g i := by
        ext x
        exact basicExtension_naturality F G k D hD f.unop g.unop i.unop.hom.le x }
  exact congrArg (fun a => (a.app (.op f)).hom x) h

/-- On global sections, `extendAdditive F G k D hD` is `D`. -/
lemma extendAdditive_top
    {A : CommRingCat.{u}} (F G : (Spec A).Modules) [F.IsQuasicoherent]
    (k : ℕ) (D : Γ(F, ⊤) →ₗ[ℤ] Γ(G, ⊤))
    (hD : D.IsDifferentialOperatorOfOrderLE A k) (x : Γ(F, ⊤)) :
    (extendAdditive F G k D hD).app (.op ⊤) x = D x := by
  apply TopCat.Presheaf.IsSheaf.section_ext G.isSheaf
  intro p hp
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hpf, hf⟩ :=
    isBasis_specBasicOpen.exists_subset_of_mem_open hp
      (show IsOpen (⊤ : (Spec A).Opens).carrier from isOpen_univ)
  refine ⟨_, hf, hpf, ?_⟩
  exact (congrArg (fun a => a.hom x) ((extendAdditive F G k D hD).naturality
    (homOfLE hf).op)).symm.trans ((extendAdditive_basic F G k D hD f _).trans
    ((basicExtension F G k D hD f).2.2 x))

/-- For quasi-coherent `F` on `Spec A`, two morphisms of presheaves `F ⟶ G` whose components
over every basic open are differential operators of order at most `k` over `A` are equal if
they agree on global sections. -/
lemma additiveHom_ext
    {A : CommRingCat.{u}} {F G : (Spec A).Modules} [F.IsQuasicoherent]
    (k : ℕ) (D E : F.presheaf ⟶ G.presheaf)
    (hD : ∀ f : A,
      LinearMap.IsDifferentialOperatorOfOrderLE A k
        (D.app (.op (specBasicOpen f))).hom.toIntLinearMap)
    (hE : ∀ f : A,
      LinearMap.IsDifferentialOperatorOfOrderLE A k
        (E.app (.op (specBasicOpen f))).hom.toIntLinearMap)
    (he : D.app (.op ⊤) = E.app (.op ⊤)) : D = E := by
  apply (TopCat.Sheaf.restrictHomEquivHom F.presheaf ((SheafOfModules.toSheaf _).obj G)
    isBasis_specBasicOpen).symm.injective
  ext f x
  let a : A := f.unop
  let fm : Γ(F, ⊤) →ₗ[A] Γ(F, specBasicOpen a) :=
    ((modulesSpecToSheaf.obj F).obj.map (homOfLE le_top).op).hom
  have : IsLocalizedModule.Away a fm := isLocalizedModule_away_restrict_top F a
  have h := order_ext_localized (Submonoid.powers a) fm
    (smul_injective_powers_of_le G le_rfl) (hD a) (hE a)
    (fun m => by
      show D.app _ (F.presheaf.map (homOfLE le_top).op m) =
        E.app _ (F.presheaf.map (homOfLE le_top).op m)
      have h₁ := congrArg (fun a => a.hom m)
        (D.naturality (homOfLE (le_top : specBasicOpen a ≤ ⊤)).op)
      have h₂ := congrArg (fun a => a.hom m)
        (E.naturality (homOfLE (le_top : specBasicOpen a ≤ ⊤)).op)
      rw [he] at h₁
      exact h₁.trans h₂.symm)
  exact LinearMap.congr_fun h x

/-- The restriction `D.slice Y` of a natural raw operator `D` is natural. -/
lemma raw_slice_natural {X : TopCat.{u}} {O : TopCat.Sheaf RingCat.{u} X}
    {F G : SheafOfModules.{u} O}
    {U : TopologicalSpace.Opens X} {D : DiffOp.RawOp F G U} (hD : D.IsNatural) (Y : Over U) :
    (D.slice Y).IsNatural := by
  intro Z Z' h s
  exact hD (Over.mk (Z.hom ≫ Y.hom)) (Over.mk (Z'.hom ≫ Y.hom))
    (Over.homMk h.left (by simp)) s

/-- The commutator of a natural raw operator with multiplication by a section `g` is
natural. -/
lemma raw_commutator_natural {X : TopCat.{u}} {O : TopCat.Sheaf RingCat.{u} X}
    {F G : SheafOfModules.{u} O}
    {U : TopologicalSpace.Opens X} {D : DiffOp.RawOp F G U} (hD : D.IsNatural)
    (g : O.obj.obj (.op U)) :
    (DiffOp.RawOp.commutator g D).IsNatural := by
  intro Y Y' h s
  have hg : O.obj.map h.left.op
      (O.obj.map Y'.hom.op g) = O.obj.map Y.hom.op g := by
    simp only [← Functor.map_comp_apply, ← op_comp, Over.w h]
  have eF : F.val.presheaf.map h.left.op (O.obj.map Y'.hom.op g • s) =
      O.obj.map Y.hom.op g • F.val.presheaf.map h.left.op s :=
    (presheaf_map_smul F.val h.left.op _ s).trans
      (congrArg (fun r => r • F.val.presheaf.map h.left.op s) hg)
  have eD : G.val.presheaf.map h.left.op (D Y' (O.obj.map Y'.hom.op g • s)) =
      D Y (O.obj.map Y.hom.op g • F.val.presheaf.map h.left.op s) :=
    (hD Y Y' h _).symm.trans (congrArg (fun z => D Y z) eF)
  have eG : G.val.presheaf.map h.left.op (O.obj.map Y'.hom.op g • D Y' s) =
      O.obj.map Y.hom.op g • D Y (F.val.presheaf.map h.left.op s) :=
    ((presheaf_map_smul G.val h.left.op _ (D Y' s)).trans
        (congrArg (fun r => r • G.val.presheaf.map h.left.op (D Y' s)) hg)).trans
      (congrArg (fun z => O.obj.map Y.hom.op g • z) (hD Y Y' h s).symm)
  show D Y (O.obj.map Y.hom.op g • F.val.presheaf.map h.left.op s) -
      O.obj.map Y.hom.op g • D Y (F.val.presheaf.map h.left.op s) =
    G.val.presheaf.map h.left.op
      (D Y' (O.obj.map Y'.hom.op g • s) - O.obj.map Y'.hom.op g • D Y' s)
  exact ((map_sub (G.val.presheaf.map h.left.op).hom _ _).trans
    (congrArg₂ (fun x y => x - y) eD eG)).symm

/-- At the identity of `Y.left`, the commutator of `D.slice Y` with multiplication by `g` is
`D Y ∘ g - g ∘ D Y`. -/
lemma commutator_section_id {X : TopCat.{u}} {O : TopCat.Sheaf RingCat.{u} X}
    {F G : SheafOfModules.{u} O}
    {U : TopologicalSpace.Opens X} (D : DiffOp.RawOp F G U) (Y : Over U)
    (g : O.obj.obj (.op Y.left)) :
    ((DiffOp.RawOp.commutator g (D.slice Y)) (Over.mk (𝟙 Y.left))).toIntLinearMap =
      (D Y).toIntLinearMap ∘ₗ Algebra.lsmul ℤ ℤ (F.val.obj (.op Y.left)) g -
        Algebra.lsmul ℤ ℤ (G.val.obj (.op Y.left)) g ∘ₗ (D Y).toIntLinearMap := by
  ext x
  show D (Over.mk ((𝟙 Y.left) ≫ Y.hom)) ((O.obj.map (𝟙 (.op Y.left))) g • x) -
      (O.obj.map (𝟙 (.op Y.left))) g • D (Over.mk ((𝟙 Y.left) ≫ Y.hom)) x =
    D Y (g • x) - g • D Y x
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- Let `B` be a basis of opens. If the components of a natural raw operator `D` on `U` over
the members of `B` contained in `U` are differential operators of order at most `k`, then so
is every component of `D`. -/
lemma rawOrder_of_basic {X : TopCat.{u}} {O : TopCat.Sheaf RingCat.{u} X}
    {F G : SheafOfModules.{u} O} {ι : Type*} (B : ι → TopologicalSpace.Opens X)
    (hB : TopologicalSpace.Opens.IsBasis (Set.range B))
    {U : TopologicalSpace.Opens X} {k : ℕ} (D : DiffOp.RawOp F G U) (hnat : D.IsNatural)
    (hb : ∀ (f : ι) (hf : B f ≤ U),
      (D (Over.mk (homOfLE hf))).toIntLinearMap.IsDifferentialOperatorOfOrderLE
        (O.obj.obj (.op (B f))) k) (Y : Over U) :
    (D Y).toIntLinearMap.IsDifferentialOperatorOfOrderLE (O.obj.obj (.op Y.left)) k := by
  induction k generalizing U with
  | zero =>
    intro g s
    apply TopCat.Presheaf.IsSheaf.section_ext (F := G.val.presheaf) G.isSheaf
    intro p hp
    obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hpf, hf⟩ :=
      hB.exists_subset_of_mem_open hp Y.left.2
    refine ⟨_, hf, hpf, ?_⟩
    let Z : Over U := Over.mk (homOfLE (hf.trans Y.hom.le))
    let i : Z ⟶ Y := Over.homMk (homOfLE hf)
    show G.val.presheaf.map i.left.op (D Y (g • s)) =
      G.val.presheaf.map i.left.op (g • D Y s)
    rw [← hnat Z Y i, presheaf_map_smul F.val, presheaf_map_smul G.val, ← hnat Z Y i]
    exact hb f (hf.trans Y.hom.le) _ _
  | succ k ih =>
    intro g
    have h := ih (DiffOp.RawOp.commutator g (D.slice Y))
      (raw_commutator_natural (raw_slice_natural hnat Y) g) (fun f hf => ?_)
      (Over.mk (𝟙 Y.left))
    · rwa [commutator_section_id] at h
    · exact hb f (hf.trans Y.hom.le) (O.obj.map (homOfLE hf).op g)

/-- Every component `D Y` of a differential operator of order at most `k` relative to `φ` is
a differential operator of order at most `k` over the sections of `O'` over `Y.left`. -/
lemma rawOrder_section {X : TopCat.{u}}
    {O O' : TopCat.Sheaf RingCat.{u} X} (φ : O ⟶ O')
    {F G : SheafOfModules.{u} O'} {U : TopologicalSpace.Opens X} {k : ℕ} (D : DiffOp.RawOp F G U)
    (hD : DiffOp.IsDiffOpOfOrder φ k D) (Y : Over U) :
    (D Y).toIntLinearMap.IsDifferentialOperatorOfOrderLE (O'.obj.obj (.op Y.left)) k := by
  induction k generalizing U with
  | zero => exact hD.2 Y
  | succ k ih =>
    intro g
    have h := ih _ (hD.2.2 Y g) (Over.mk (𝟙 Y.left))
    change LinearMap.IsDifferentialOperatorOfOrderLE _ k
      (DiffOp.RawOp.commutator g (D.slice Y) (Over.mk (𝟙 Y.left))).toIntLinearMap at h
    rwa [commutator_section_id] at h

/-- If the sections of `O'` are commutative, a natural `O`-linear raw operator whose
components are differential operators of order at most `k` over the sections of `O'` is a
differential operator of order at most `k` relative to `φ`. -/
lemma rawOrder_of_sections {X : TopCat.{u}}
    {O O' : TopCat.Sheaf RingCat.{u} X} (φ : O ⟶ O')
    (hcomm : ∀ (U : (TopologicalSpace.Opens X)ᵒᵖ) (r s : O'.obj.obj U), r * s = s * r)
    {F G : SheafOfModules.{u} O'} {U : TopologicalSpace.Opens X} {k : ℕ}
    (D : DiffOp.RawOp F G U) (hnat : D.IsNatural) (hlin : D.IsO1Linear φ)
    (hsec : ∀ Y : Over U,
      (D Y).toIntLinearMap.IsDifferentialOperatorOfOrderLE (O'.obj.obj (.op Y.left)) k) :
    DiffOp.IsDiffOpOfOrder φ k D := by
  induction k generalizing U with
  | zero => exact ⟨hnat, hsec⟩
  | succ k ih =>
    refine ⟨hnat, hlin, fun Y g => ?_⟩
    apply ih (DiffOp.RawOp.commutator g (D.slice Y))
      (raw_commutator_natural (raw_slice_natural hnat Y) g)
    · intro Z a s
      let W : Over U := Over.mk (Z.hom ≫ Y.hom)
      let c := O'.obj.map Z.hom.op g
      show D W (c • (DiffOp.sectionRingHom φ (.op W.left) a • s)) -
          c • D W (DiffOp.sectionRingHom φ (.op W.left) a • s) =
        DiffOp.sectionRingHom φ (.op W.left) a • (D W (c • s) - c • D W s)
      have hF : c • (DiffOp.sectionRingHom φ (.op W.left) a • s) =
          DiffOp.sectionRingHom φ (.op W.left) a • (c • s) := by
        rw [smul_smul, smul_smul, hcomm]
      have hG : c • (DiffOp.sectionRingHom φ (.op W.left) a • D W s) =
          DiffOp.sectionRingHom φ (.op W.left) a • (c • D W s) := by
        rw [smul_smul, smul_smul, hcomm]
      rw [hF, hlin W a, hlin W a, hG, smul_sub]
    · intro Z
      exact hsec (Over.mk (Z.hom ≫ Y.hom)) (O'.obj.map Z.hom.op g)

/-- The restriction to `U` of a morphism of presheaves is a natural raw operator. -/
lemma natural_raw {X : TopCat.{u}} {O : TopCat.Sheaf RingCat.{u} X}
    {F G : SheafOfModules.{u} O} (D : F.val.presheaf ⟶ G.val.presheaf)
    (U : TopologicalSpace.Opens X) :
    (DiffOp.GlobalOp.restrict (fun V => (D.app V).hom) U).IsNatural := by
  intro Y Y' h s
  exact congrArg (fun a => a.hom s) (D.naturality h.left.op)

/-- Over every open `U`, `extendAdditive` is a differential operator of order at most `k` over
`Γ(Spec A, U)`. -/
lemma extendAdditive_order
    {A : CommRingCat.{u}} (F G : (Spec A).Modules) [F.IsQuasicoherent]
    (k : ℕ) (D : Γ(F, ⊤) →ₗ[ℤ] Γ(G, ⊤))
    (hD : D.IsDifferentialOperatorOfOrderLE A k) (U : (Spec A).Opens) :
    ((extendAdditive F G k D hD).app (.op U)).hom.toIntLinearMap.IsDifferentialOperatorOfOrderLE
      Γ(Spec A, U) k := by
  apply rawOrder_of_basic specBasicOpen isBasis_specBasicOpen
    (DiffOp.GlobalOp.restrict (fun V => ((extendAdditive F G k D hD).app V).hom) U)
    (natural_raw _ U) (fun f hf => ?_) (Over.mk (𝟙 U))
  have he :
      ((extendAdditive F G k D hD).app (.op (specBasicOpen f))).hom.toIntLinearMap =
        (basicExtension F G k D hD f).1 := by
    ext x
    exact extendAdditive_basic F G k D hD f x
  show ((extendAdditive F G k D hD).app (.op (specBasicOpen f))).hom.toIntLinearMap
    |>.IsDifferentialOperatorOfOrderLE Γ(Spec A, specBasicOpen f) k
  rw [he]
  exact (basicExtension F G k D hD f).2.1

/-- If its restrictions to every open are `O`-linear through `φ`, then `extendAdditive` is a
global differential operator of order at most `k` relative to `φ`. -/
lemma extendAdditive_relative_order
    {A : CommRingCat.{u}} (F G : (Spec A).Modules) [F.IsQuasicoherent]
    (k : ℕ) (D : Γ(F, ⊤) →ₗ[ℤ] Γ(G, ⊤))
    (hD : D.IsDifferentialOperatorOfOrderLE A k)
    {O : TopCat.Sheaf RingCat.{u} (Spec A)} (φ : O ⟶ (Spec A).ringCatSheaf)
    (hlin : ∀ U : (Spec A).Opens,
      (DiffOp.GlobalOp.restrict
        (fun V => ((extendAdditive F G k D hD).app V).hom) U).IsO1Linear φ) :
    DiffOp.IsGlobalDiffOpOfOrder φ k (fun V => ((extendAdditive F G k D hD).app V).hom) := by
  intro U
  exact rawOrder_of_sections φ (fun V r s => mul_comm (G := Γ(Spec A, V.unop)) r s) _
    (natural_raw _ U) (hlin U) (fun Y => extendAdditive_order F G k D hD Y.left)

/-- A global differential operator of order at most `k` relative to `φ`, as a morphism of
presheaves of abelian groups. -/
noncomputable def globalNatural {A : CommRingCat.{u}}
    {O : TopCat.Sheaf RingCat.{u} (Spec A)} (φ : O ⟶ (Spec A).ringCatSheaf)
    {F G : (Spec A).Modules} {k : ℕ} (D : DiffOp.GlobalOp F G)
    (hD : DiffOp.IsGlobalDiffOpOfOrder φ k D) : F.presheaf ⟶ G.presheaf where
  app U := AddCommGrpCat.ofHom (D U)
  naturality U V i := by
    ext s
    exact DiffOp.RawOp.isNatural_of_isDiffOpOfOrder φ k _ (hD ⊤)
      (Over.mk (homOfLE (le_top : V.unop ≤ ⊤)))
      (Over.mk (homOfLE (le_top : U.unop ≤ ⊤))) (Over.homMk i.unop) s

/-- For quasi-coherent `F` on `Spec A`, two global differential operators `F → G` of order at
most `k` relative to `φ` that agree on global sections are equal. -/
lemma globalDiffOp_ext {A : CommRingCat.{u}}
    {O : TopCat.Sheaf RingCat.{u} (Spec A)} (φ : O ⟶ (Spec A).ringCatSheaf)
    {F G : (Spec A).Modules} [F.IsQuasicoherent] {k : ℕ}
    {D E : DiffOp.GlobalOp F G} (hD : DiffOp.IsGlobalDiffOpOfOrder φ k D)
    (hE : DiffOp.IsGlobalDiffOpOfOrder φ k E)
    (he : D (.op ⊤) = E (.op ⊤)) : D = E := by
  have h := additiveHom_ext k (globalNatural φ D hD) (globalNatural φ E hE)
    (fun f => order_restrict (S := A) (T := Γ(Spec A, specBasicOpen f))
      (rawOrder_section φ _ (hD (specBasicOpen f)) (Over.mk (𝟙 _))))
    (fun f => order_restrict (S := A) (T := Γ(Spec A, specBasicOpen f))
      (rawOrder_section φ _ (hE (specBasicOpen f)) (Over.mk (𝟙 _))))
    (congrArg AddCommGrpCat.ofHom he)
  funext U
  exact congrArg (fun T => (T.app U).hom) h

/-- If `D` commutes with multiplication by `a : A`, so does `basicExtension F G k D hD f`. -/
lemma basicExtension_smul
    {A : CommRingCat.{u}} (F G : (Spec A).Modules) [F.IsQuasicoherent]
    (k : ℕ) (D : Γ(F, ⊤) →ₗ[ℤ] Γ(G, ⊤))
    (hD : D.IsDifferentialOperatorOfOrderLE A k) (a : A)
    (ha : ∀ x, D (a • x) = a • D x) (f : A)
    (x : Γ(F, specBasicOpen f)) :
    (basicExtension F G k D hD f).1 (a • x) = a • (basicExtension F G k D hD f).1 x := by
  let fm : Γ(F, ⊤) →ₗ[A] Γ(F, specBasicOpen f) :=
    ((modulesSpecToSheaf.obj F).obj.map (homOfLE le_top).op).hom
  have : IsLocalizedModule.Away f fm := isLocalizedModule_away_restrict_top F f
  have hE := order_restrict (S := A) (basicExtension F G k D hD f).2.1
  have he := order_ext_localized (Submonoid.powers f) fm (smul_injective_powers_of_le G le_rfl)
    (order_precomp hE (Algebra.lsmul A A Γ(F, specBasicOpen f) a))
    (order_postcomp hE (Algebra.lsmul A A Γ(G, specBasicOpen f) a)) ?_
  · exact LinearMap.congr_fun he x
  · intro m
    show (basicExtension F G k D hD f).1 (a • fm m) =
      a • (basicExtension F G k D hD f).1 (fm m)
    rw [← fm.map_smul]
    show (basicExtension F G k D hD f).1 (F.presheaf.map (homOfLE le_top).op (a • m)) =
      a • (basicExtension F G k D hD f).1 (F.presheaf.map (homOfLE le_top).op m)
    rw [(basicExtension F G k D hD f).2.2, (basicExtension F G k D hD f).2.2, ha]
    exact Scheme.Modules.map_smul_Spec _ _ _

/-- If `D` commutes with multiplication by `a : A`, so does every component of
`extendAdditive F G k D hD`. -/
lemma extendAdditive_smul
    {A : CommRingCat.{u}} (F G : (Spec A).Modules) [F.IsQuasicoherent]
    (k : ℕ) (D : Γ(F, ⊤) →ₗ[ℤ] Γ(G, ⊤))
    (hD : D.IsDifferentialOperatorOfOrderLE A k) (a : A)
    (ha : ∀ x, D (a • x) = a • D x) (U : (Spec A).Opens) (s : Γ(F, U)) :
    (extendAdditive F G k D hD).app (.op U) (a • s) =
      a • (extendAdditive F G k D hD).app (.op U) s := by
  apply TopCat.Presheaf.IsSheaf.section_ext G.isSheaf
  intro p hp
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hpf, hf⟩ :=
    isBasis_specBasicOpen.exists_subset_of_mem_open hp U.2
  refine ⟨_, hf, hpf, ?_⟩
  have hn (t : Γ(F, U)) := congrArg (fun b => b.hom t)
    ((extendAdditive F G k D hD).naturality (homOfLE hf).op)
  show G.presheaf.map (homOfLE hf).op ((extendAdditive F G k D hD).app (.op U) (a • s)) =
    G.presheaf.map (homOfLE hf).op (a • (extendAdditive F G k D hD).app (.op U) s)
  change ∀ t, (extendAdditive F G k D hD).app (.op (specBasicOpen f))
    (F.presheaf.map (homOfLE hf).op t) =
      G.presheaf.map (homOfLE hf).op ((extendAdditive F G k D hD).app (.op U) t) at hn
  have eF : F.presheaf.map (homOfLE hf).op (a • s) =
      a • F.presheaf.map (homOfLE hf).op s :=
    Scheme.Modules.map_smul_Spec (homOfLE hf).op a s
  have eG : G.presheaf.map (homOfLE hf).op (a • (extendAdditive F G k D hD).app (.op U) s) =
      a • G.presheaf.map (homOfLE hf).op ((extendAdditive F G k D hD).app (.op U) s) :=
    Scheme.Modules.map_smul_Spec (homOfLE hf).op a _
  refine (hn _).symm.trans (Eq.trans ?_ eG.symm)
  refine (congrArg (fun z =>
    ((extendAdditive F G k D hD).app (.op (specBasicOpen f))).hom z) eF).trans ?_
  refine (extendAdditive_basic F G k D hD f _).trans ?_
  refine (basicExtension_smul F G k D hD a ha f _).trans ?_
  exact congrArg (fun z => a • z)
    ((extendAdditive_basic F G k D hD f _).symm.trans (hn s))

/-- An `R`-linear map is a differential operator of order at most `k` over `S` if and only if
its underlying `ℤ`-linear map is. -/
lemma order_toInt_iff
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S M] [IsScalarTower R S M]
    [Module R N] [Module S N] [IsScalarTower R S N]
    (D : M →ₗ[R] N) (k : ℕ) :
    D.toAddMonoidHom.toIntLinearMap.IsDifferentialOperatorOfOrderLE S k ↔
      D.IsDifferentialOperatorOfOrderLE S k := by
  induction k generalizing D with
  | zero => rfl
  | succ k ih =>
    exact forall_congr' fun s => ih
      (D ∘ₗ Algebra.lsmul R R M s - Algebra.lsmul R R N s ∘ₗ D)

/-- For quasi-coherent `F` on `Spec A`, evaluation on global sections is a bijection from the
morphisms of presheaves `F ⟶ G` that are differential operators of order at most `k` over
`Γ(Spec A, U)` on every open `U` to the differential operators `Γ(F, ⊤) → Γ(G, ⊤)` of order at
most `k` over `A`. -/
noncomputable def sectionwiseDiffOpEquiv
    {A : CommRingCat.{u}} (F G : (Spec A).Modules) [F.IsQuasicoherent] (k : ℕ) :
    {D : F.presheaf ⟶ G.presheaf // ∀ U : (Spec A).Opens,
      (D.app (.op U)).hom.toIntLinearMap.IsDifferentialOperatorOfOrderLE Γ(Spec A, U) k} ≃
    {D : Γ(F, ⊤) →ₗ[ℤ] Γ(G, ⊤) // D.IsDifferentialOperatorOfOrderLE A k} where
  toFun D := ⟨(D.1.app (.op ⊤)).hom.toIntLinearMap,
    order_restrict (S := A) (T := Γ(Spec A, ⊤)) (D.2 ⊤)⟩
  invFun D := ⟨extendAdditive F G k D.1 D.2, extendAdditive_order F G k D.1 D.2⟩
  left_inv D := by
    apply Subtype.ext
    apply additiveHom_ext k
    · intro f
      exact order_restrict (S := A) (T := Γ(Spec A, specBasicOpen f))
        (extendAdditive_order F G k _ _ _)
    · intro f
      exact order_restrict (S := A) (T := Γ(Spec A, specBasicOpen f)) (D.2 _)
    · ext x
      exact extendAdditive_top F G k _ _ x
  right_inv D := by
    apply Subtype.ext
    ext x
    exact extendAdditive_top F G k _ _ x

end

section

/-- A morphism of presheaves `F ⟶ G` on `Spec A` commuting with the action of `R` is linear
over the pullback of the structure sheaf of `Spec R` along `Spec.map f`. -/
lemma natural_relative_linear {R A : CommRingCat.{u}} (f : R ⟶ A)
    (F G : (Spec A).Modules) (D : F.presheaf ⟶ G.presheaf)
    (hD : ∀ (r : R) (W : (Spec A).Opens) (x : Γ(F, W)),
      D.app (.op W) (f r • x) = f r • D.app (.op W) x)
    (U : (Spec A).Opens) :
    (DiffOp.GlobalOp.restrict (fun V => (D.app V).hom) U).IsO1Linear
      ((Spec.map f).relativeStructureSheafMap) := by
  intro Y a s
  apply TopCat.Presheaf.IsSheaf.section_ext G.isSheaf
  intro x hx
  obtain ⟨W, hW, V, hV, b, hxW, hb⟩ := pullback_image_locally (Spec.map f).base
    (Spec R).ringCatSheaf (Spec A).ringCatSheaf (Spec.map f).toRingCatSheafHom Y.left a x hx
  refine ⟨W, hW, hxW, ?_⟩
  change (Spec A).presheaf.map (homOfLE hW).op
      (DiffOp.sectionRingHom ((Spec.map f).relativeStructureSheafMap) (.op Y.left) a) =
    (Spec.map f).appLE V W hV b at hb
  have hn (z : Γ(F, Y.left)) := congrArg (fun m => m.hom z) (D.naturality (homOfLE hW).op)
  change ∀ z, D.app (.op W) (F.presheaf.map (homOfLE hW).op z) =
    G.presheaf.map (homOfLE hW).op (D.app (.op Y.left) z) at hn
  have e1 : F.presheaf.map (homOfLE hW).op
        (DiffOp.sectionRingHom ((Spec.map f).relativeStructureSheafMap) (.op Y.left) a • s) =
      (Spec.map f).appLE V W hV b • F.presheaf.map (homOfLE hW).op s :=
    (modules_presheaf_map_smul F hW _ s).trans
      (congrArg (fun r => r • F.presheaf.map (homOfLE hW).op s) hb)
  have e2 : G.presheaf.map (homOfLE hW).op
        (@SMul.smul Γ(Spec A, Y.left) Γ(G, Y.left) inferInstance
          (DiffOp.sectionRingHom ((Spec.map f).relativeStructureSheafMap) (.op Y.left) a)
          (D.app (.op Y.left) s)) =
      (Spec.map f).appLE V W hV b •
        G.presheaf.map (homOfLE hW).op (D.app (.op Y.left) s) :=
    (modules_presheaf_map_smul G hW _ (D.app (.op Y.left) s)).trans
      (congrArg (fun r => r • G.presheaf.map (homOfLE hW).op (D.app (.op Y.left) s)) hb)
  show G.presheaf.map (homOfLE hW).op (D.app (.op Y.left) (_ • s)) =
    G.presheaf.map (homOfLE hW).op
      (@SMul.smul Γ(Spec A, Y.left) Γ(G, Y.left) inferInstance
        (DiffOp.sectionRingHom ((Spec.map f).relativeStructureSheafMap) (.op Y.left) a)
        (D.app (.op Y.left) s))
  refine (hn _).symm.trans (Eq.trans ?_ e2.symm)
  refine (congrArg (fun z => (D.app (.op W)).hom z) e1).trans ?_
  exact (natural_commutes_appLE f F G D hD V W hV b _).trans
    (congrArg (fun z => (Spec.map f).appLE V W hV b • z) (hn s))

/-- The image of `f r` in `Γ(Spec A, U)` is the image of a section over `U` of the pullback of
the structure sheaf of `Spec R` along `Spec.map f`. -/
lemma algebraMap_mem_range_relative {R A : CommRingCat.{u}} (f : R ⟶ A)
    (U : (Spec A).Opens) (r : R) :
    ∃ a, DiffOp.sectionRingHom ((Spec.map f).relativeStructureSheafMap) (.op U) a =
      algebraMap A Γ(Spec A, U) (f r) := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (Spec.map f).base
  let P := (TopCat.Sheaf.pullback RingCat (Spec.map f).base).obj (Spec R).ringCatSheaf
  let φ := (Spec.map f).relativeStructureSheafMap
  let η := adj.unit.app (Spec R).ringCatSheaf
  have e : U ≤ Spec.map f ⁻¹ᵁ ⊤ := by simp
  let a := η.hom.app (.op ⊤) (algebraMap R Γ(Spec R, ⊤) r)
  refine ⟨P.obj.map (homOfLE e).op a, ?_⟩
  have he : η ≫ (TopCat.Sheaf.pushforward RingCat (Spec.map f).base).map φ =
      (Spec.map f).toRingCatSheafHom := adj.homEquiv _ _ |>.apply_symm_apply _
  show φ.hom.app (.op U) (P.obj.map (homOfLE e).op a) = _
  rw [show φ.hom.app (.op U) (P.presheaf.map (homOfLE e).op a) =
      (Spec A).presheaf.map (homOfLE e).op (φ.hom.app (.op (Spec.map f ⁻¹ᵁ ⊤)) a) from
    ConcreteCategory.congr_hom (φ.hom.naturality (homOfLE e).op) a]
  have h := congrArg (fun m => m.hom.app (.op ⊤) (algebraMap R Γ(Spec R, ⊤) r)) he
  change φ.hom.app (.op (Spec.map f ⁻¹ᵁ ⊤)) a =
    (Spec.map f).app ⊤ (algebraMap R Γ(Spec R, ⊤) r) at h
  rw [h]
  exact specMap_algebraMap f ⊤ U e r

/-- A global differential operator relative to `Spec.map f : Spec A ⟶ Spec R` commutes with
the action of `R` on every open. -/
lemma globalDiffOp_smul_base {R A : CommRingCat.{u}} (f : R ⟶ A)
    {F G : (Spec A).Modules} {k : ℕ} {D : DiffOp.GlobalOp F G}
    (hD : DiffOp.IsGlobalDiffOpOfOrder ((Spec.map f).relativeStructureSheafMap) k D)
    (U : (Spec A).Opens) (r : R) (s : Γ(F, U)) :
    D (.op U) (f r • s) =
      @SMul.smul A Γ(G, U) inferInstance (f r) (D (.op U) s) := by
  obtain ⟨a, ha⟩ := algebraMap_mem_range_relative f U r
  have h := DiffOp.RawOp.isO1Linear_of_isDiffOpOfOrder _ k _ (hD U)
    (Over.mk (𝟙 U)) a s
  simp only [Over.mk_left] at h
  rw [ha] at h
  change D (.op U) (algebraMap A Γ(Spec A, U) (f r) • s) =
    @SMul.smul Γ(Spec A, U) Γ(G, U) inferInstance
      (algebraMap A Γ(Spec A, U) (f r)) (D (.op U) s) at h
  rw [IsScalarTower.algebraMap_smul] at h
  exact h.trans (IsScalarTower.algebraMap_smul (M := Γ(G, U)) Γ(Spec A, U) (f r) _)

/-- Over every open, `globalNatural φ D hD` is a differential operator of order at most `k`
over `A`. -/
lemma globalNatural_order_base {A : CommRingCat.{u}}
    {O : TopCat.Sheaf RingCat.{u} (Spec A)} (φ : O ⟶ (Spec A).ringCatSheaf)
    {F G : (Spec A).Modules} {k : ℕ} (D : DiffOp.GlobalOp F G)
    (hD : DiffOp.IsGlobalDiffOpOfOrder φ k D) (U : (Spec A).Opens) :
    ((globalNatural φ D hD).app (.op U)).hom.toIntLinearMap.IsDifferentialOperatorOfOrderLE A k :=
  order_restrict (S := A) (T := Γ(Spec A, U))
    (rawOrder_section φ _ (hD U) (Over.mk (𝟙 U)))

/-- For quasi-coherent `F` on `Spec A`, evaluation on global sections is a bijection from the
differential operators `F → G` of order at most `k` relative to `Spec A ⟶ Spec R` to the
`R`-linear differential operators `Γ(F, ⊤) → Γ(G, ⊤)` of order at most `k` over `A`. -/
noncomputable def affineGlobalDiffOpEquiv
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (F G : (Spec (.of A)).Modules) [F.IsQuasicoherent] (k : ℕ) :
    letI _modAF : Module A Γ(F, ⊤) :=
      Module.compHom _ (Scheme.ΓSpecIso (.of A)).inv.hom
    letI _modAG : Module A Γ(G, ⊤) :=
      Module.compHom _ (Scheme.ΓSpecIso (.of A)).inv.hom
    letI _modRF : Module R Γ(F, ⊤) := Module.compHom _ (algebraMap R A)
    letI _modRG : Module R Γ(G, ⊤) := Module.compHom _ (algebraMap R A)
    letI _towerF : IsScalarTower R A Γ(F, ⊤) := IsScalarTower.of_compHom R A _
    letI _towerG : IsScalarTower R A Γ(G, ⊤) := IsScalarTower.of_compHom R A _
    {e :
      {D : DiffOp.GlobalOp F G //
        DiffOp.IsGlobalDiffOpOfOrder
          (Scheme.Hom.relativeStructureSheafMap
            (Spec.map (CommRingCat.ofHom (algebraMap R A)))) k D} ≃
        {D : Γ(F, ⊤) →ₗ[R] Γ(G, ⊤) //
          D.IsDifferentialOperatorOfOrderLE A k} //
      ∀ D x, (e D).1 x = D.1 (.op ⊤) x} := by
  letI _modAF : Module A Γ(F, ⊤) :=
    Module.compHom _ (Scheme.ΓSpecIso (.of A)).inv.hom
  letI _modAG : Module A Γ(G, ⊤) :=
    Module.compHom _ (Scheme.ΓSpecIso (.of A)).inv.hom
  letI _modRF : Module R Γ(F, ⊤) := Module.compHom _ (algebraMap R A)
  letI _modRG : Module R Γ(G, ⊤) := Module.compHom _ (algebraMap R A)
  letI _towerF : IsScalarTower R A Γ(F, ⊤) := IsScalarTower.of_compHom R A _
  letI _towerG : IsScalarTower R A Γ(G, ⊤) := IsScalarTower.of_compHom R A _
  let f := CommRingCat.ofHom (algebraMap R A)
  let φ := (Spec.map f).relativeStructureSheafMap
  let forwardMap (D : DiffOp.GlobalOp F G) (hD : DiffOp.IsGlobalDiffOpOfOrder φ k D) :
      Γ(F, ⊤) →ₗ[R] Γ(G, ⊤) :=
    { __ := D (.op ⊤)
      map_smul' r x := by exact globalDiffOp_smul_base f hD ⊤ r x }
  have forward_order (D : DiffOp.GlobalOp F G) (hD : DiffOp.IsGlobalDiffOpOfOrder φ k D) :
      (forwardMap D hD).IsDifferentialOperatorOfOrderLE A k :=
    (order_toInt_iff _ k).mp (globalNatural_order_base φ D hD ⊤)
  let inverseMap (D : Γ(F, ⊤) →ₗ[R] Γ(G, ⊤))
      (hD : D.IsDifferentialOperatorOfOrderLE A k) :=
    extendAdditive F G k D.toAddMonoidHom.toIntLinearMap ((order_toInt_iff (S := A) D k).mpr hD)
  have inverse_order (D : Γ(F, ⊤) →ₗ[R] Γ(G, ⊤))
      (hD : D.IsDifferentialOperatorOfOrderLE A k) :
      DiffOp.IsGlobalDiffOpOfOrder φ k (fun V => ((inverseMap D hD).app V).hom) := by
    apply extendAdditive_relative_order
    intro U
    apply natural_relative_linear f
    intro r W x
    exact extendAdditive_smul F G k D.toAddMonoidHom.toIntLinearMap
      ((order_toInt_iff (S := A) D k).mpr hD) (algebraMap R A r) (fun x => D.map_smul r x) W x
  refine ⟨{
    toFun := fun D => ⟨forwardMap D.1 D.2, forward_order D.1 D.2⟩
    invFun := fun D => ⟨fun V => ((inverseMap D.1 D.2).app V).hom, inverse_order D.1 D.2⟩
    left_inv := ?_
    right_inv := ?_ }, fun D x => rfl⟩
  · intro D
    apply Subtype.ext
    apply globalDiffOp_ext φ
      (inverse_order (forwardMap D.1 D.2) (forward_order D.1 D.2)) D.2
    ext x
    exact extendAdditive_top F G k _ _ x
  · intro D
    apply Subtype.ext
    ext x
    exact extendAdditive_top F G k _ _ x


/-- On an affine scheme, taking global sections gives a bijection from differential operators
of order at most `k` between sheaves to differential operators of order at most `k` between the
corresponding modules. The source sheaf is required to be quasi-coherent; the target sheaf is
arbitrary. -/
@[stacks 0G44]
noncomputable def globalDiffOpEquiv
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (F G : (Spec (.of A)).Modules) [F.IsQuasicoherent] (k : ℕ) :
    letI _modAF : Module A Γ(F, ⊤) :=
      Module.compHom _ (Scheme.ΓSpecIso (.of A)).inv.hom
    letI _modAG : Module A Γ(G, ⊤) :=
      Module.compHom _ (Scheme.ΓSpecIso (.of A)).inv.hom
    letI _modRF : Module R Γ(F, ⊤) := Module.compHom _ (algebraMap R A)
    letI _modRG : Module R Γ(G, ⊤) := Module.compHom _ (algebraMap R A)
    letI _towerF : IsScalarTower R A Γ(F, ⊤) := IsScalarTower.of_compHom R A _
    letI _towerG : IsScalarTower R A Γ(G, ⊤) := IsScalarTower.of_compHom R A _
    {e :
      {D : DiffOp.GlobalOp F G //
        DiffOp.IsGlobalDiffOpOfOrder
          (Scheme.Hom.relativeStructureSheafMap
            (Spec.map (CommRingCat.ofHom (algebraMap R A)))) k D} ≃
        {D : Γ(F, ⊤) →ₗ[R] Γ(G, ⊤) //
          D.IsDifferentialOperatorOfOrderLE A k} //
      ∀ D x, (e D).1 x = D.1 (.op ⊤) x} :=
  affineGlobalDiffOpEquiv F G k

end

end AlgebraicGeometry.AffineDiffOp
