module

public import StacksFrontier.Deformation.Representation.TangentSelfExt.ExtensionModules
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Deformation.Representation.InfinitesimalAutomorphisms
public import StacksFrontier.Deformation.Schlessinger.AssociatedFunctor
public import StacksFrontier.Deformation.Schlessinger.AssociatedTangentSpace
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses

/-!
# Self-extensions associated to deformations over the dual numbers

Base change along the augmentation of the dual numbers, the self-extension and pair
extension associated to a deformation, the existence of a deformation realising a given
self-extension, and the uniqueness of the extension class of an associated self-extension.
-/

@[expose] public noncomputable section

open CategoryTheory
open Deformation

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] HasExt.standard

universe u w m

namespace Deformation

attribute [local instance] coefficientOppositeModule

attribute [local instance] coefficientCentralScalar

-- The deformation category of a representation is spelled through
-- `deformationCategoryProjection` and `squareZeroExtensionRestriction`, and the module over the
-- monoid algebra through `Rep.toModuleMonoidAlgebra`, so the `Module` and `IsHomLift` instance
-- arguments of a goal about them are only found after unfolding those heads.
attribute [local implicit_reducible] Rep.equivalenceModuleMonoidAlgebra
  Rep.toModuleMonoidAlgebra deformationCategoryProjection representationProjection
  squareZeroExtensionRestriction

/-- A base change along the augmentation of the dual numbers is surjective. -/
theorem dualNumber_baseChange_surjective
    {k M N ι : Type*} [CommRing k]
    [AddCommGroup M] [Module (DualNumber k) M]
    [AddCommGroup N] [Module k N]
    [Algebra (DualNumber k) k] [Module (DualNumber k) N]
    [IsScalarTower (DualNumber k) k N]
    (hmap : ∀ r : DualNumber k, algebraMap (DualNumber k) k r = r.fst)
    (b : Module.Basis ι (DualNumber k) M)
    (g : M →ₗ[DualNumber k] N) (hg : IsBaseChange k g) :
    Function.Surjective g := by
  intro v
  let c := hg.basis b
  let z : ι →₀ DualNumber k := (c.repr v).mapRange TrivSqZeroExt.inl (by simp)
  refine ⟨b.repr.symm z, c.repr.injective ?_⟩
  ext i
  rw [hg.basis_repr_comp_apply]
  simp only [LinearEquiv.apply_symm_apply, hmap, z]
  rfl

/-- An element of a free dual-number module dies in the base change along the
augmentation exactly when it is annihilated by `ε`. -/
theorem dualNumber_baseChange_eq_zero_iff
    {k M N ι : Type*} [CommRing k]
    [AddCommGroup M] [Module (DualNumber k) M]
    [AddCommGroup N] [Module k N]
    [Algebra (DualNumber k) k] [Module (DualNumber k) N]
    [IsScalarTower (DualNumber k) k N]
    (hmap : ∀ r : DualNumber k, algebraMap (DualNumber k) k r = r.fst)
    (b : Module.Basis ι (DualNumber k) M)
    (g : M →ₗ[DualNumber k] N) (hg : IsBaseChange k g) (x : M) :
    g x = 0 ↔ (DualNumber.eps : DualNumber k) • x = 0 := by
  have hc : g x = 0 ↔ ∀ i, (b.repr x i).fst = 0 := by
    rw [← (hg.basis b).repr.map_eq_zero_iff]
    simp only [Finsupp.ext_iff, Finsupp.zero_apply, hg.basis_repr_comp_apply, hmap]
  rw [hc, ← b.repr.map_eq_zero_iff]
  simp only [map_smul, Finsupp.ext_iff, Finsupp.coe_smul, Pi.smul_apply,
    Finsupp.zero_apply, smul_eq_mul]
  constructor
  · intro h i
    apply TrivSqZeroExt.ext <;>
      simp only [TrivSqZeroExt.fst_mul, dualNumber_snd_mul, DualNumber.fst_eps,
        DualNumber.snd_eps, zero_mul, one_mul, zero_add, h i,
        TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero]
  · intro h i
    have := congrArg TrivSqZeroExt.snd (h i)
    simpa only [dualNumber_snd_mul, DualNumber.fst_eps, DualNumber.snd_eps,
      zero_mul, one_mul, zero_add, TrivSqZeroExt.snd_zero] using this

/-- Multiplication by `ε` on a free dual-number module is exact at the middle: an
element is annihilated by `ε` exactly when it is divisible by `ε`. -/
theorem dualNumber_eps_exact
    {k M ι : Type*} [CommRing k]
    [AddCommGroup M] [Module (DualNumber k) M]
    (b : Module.Basis ι (DualNumber k) M) (x : M) :
    (DualNumber.eps : DualNumber k) • x = 0 ↔
      ∃ y : M, (DualNumber.eps : DualNumber k) • y = x := by
  constructor
  · intro hx
    let z : ι →₀ DualNumber k := (b.repr x).mapRange
      (fun r ↦ TrivSqZeroExt.inl r.snd) (by simp)
    refine ⟨b.repr.symm z, b.repr.injective ?_⟩
    apply Finsupp.ext
    intro i
    have h := congrArg (fun y ↦ (b.repr y i).snd) hx
    have hi : (b.repr x i).fst = 0 := by
      simpa only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
        dualNumber_snd_mul, DualNumber.fst_eps, DualNumber.snd_eps,
        zero_mul, one_mul, zero_add, map_zero, Finsupp.zero_apply,
        TrivSqZeroExt.snd_zero] using h
    simp only [map_smul, LinearEquiv.apply_symm_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    apply TrivSqZeroExt.ext <;>
      simp only [z, TrivSqZeroExt.fst_mul, dualNumber_snd_mul,
        DualNumber.fst_eps, DualNumber.snd_eps, zero_mul, one_mul, zero_add, hi]
    all_goals rfl
  · rintro ⟨y, rfl⟩
    rw [smul_smul]
    rw [dualNumber_eps_mul_eps]
    exact zero_smul (DualNumber k) y

/-- A surjection whose kernel is both the kernel and the image of a square-zero
endomorphism factors that endomorphism through an injection of the quotient. -/
theorem exists_injective_of_exact_endomorphism
    {k M N : Type*} [Field k]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (g : M →ₗ[k] N) (t : M →ₗ[k] M) (hg : Function.Surjective g)
    (hker : ∀ x, g x = 0 ↔ t x = 0)
    (ht : ∀ x, t x = 0 ↔ ∃ y, t y = x) :
    ∃ f : N →ₗ[k] M, Function.Injective f ∧
      LinearMap.range f = LinearMap.ker g ∧ f.comp g = t := by
  obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hg)
  have hgs (x : N) : g (s x) = x := LinearMap.congr_fun hs x
  let f := t.comp s
  have hfg (x : M) : f (g x) = t x := by
    have hx : g (s (g x) - x) = 0 := by rw [map_sub, hgs, sub_self]
    have := (hker _).1 hx
    simpa only [map_sub, sub_eq_zero, f, LinearMap.comp_apply] using this
  refine ⟨f, ?_, ?_, LinearMap.ext hfg⟩
  · exact LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun x hx ↦
      (hgs x).symm.trans ((hker _).2 hx))
  · ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker, hker, ht]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨s v, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨g y, hfg y⟩

/-- An extension of a representation by itself associated to a deformation over the dual
numbers: its quotient is the special-fibre map, its inclusion is multiplication by `ε`,
and the middle term has the restricted group-algebra action. -/
public def IsAssociatedSelfExtension
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    (x : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      (Deformation.augmentedDualNumbers (Λ := Λ) (k := k)))
    (M : ModuleCat (MonoidAlgebra k Γ))
    (f : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀) ⟶ M)
    (g : M ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀)) : Prop :=
  let X := x.1.left
  let hbase : X.base = Deformation.augmentedDualNumbers (Λ := Λ) (k := k) := x.2
  let ι : k → X.base := fun a ↦ hbase.symm ▸ TrivSqZeroExt.inl a
  let ε : X.base := hbase.symm ▸ DualNumber.eps
  ∃ e : M ≃+ X.carrier,
    (∀ (a : k) (z : M), e ((MonoidAlgebra.single (1 : Γ) a : MonoidAlgebra k Γ) • z) = ι a • e z) ∧
    (∀ (γ : Γ) (z : M), e ((MonoidAlgebra.single γ 1 : MonoidAlgebra k Γ) • z) =
      X.action γ (e z)) ∧
    (∀ z : M, g.hom z = x.1.hom.map (e z)) ∧
    (∀ z : M, e (f.hom (g.hom z)) = ε • e z)

/-- A morphism from the augmented dual numbers to the residue-field object is the
augmentation: it reads off the constant coordinate. -/
lemma dualNumbers_to_specialFiberBase_apply
    {Λ k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    (f : Deformation.augmentedDualNumbers (Λ := Λ) (k := k) ⟶
      (Deformation.Examples.residueFieldBase Λ k))
    (r : DualNumber k) : f.hom r = r.fst := by
  have h := f.residue_comm r
  rw [Deformation.Examples.residueFieldBase_residueEquiv_residue] at h
  exact h.trans (Deformation.augmentationResidueEquiv_residue Λ k
    (Deformation.dualNumbersOver Λ k)
    (Deformation.squareZeroExtension_mem_artinianLocalOver Λ k (FGModuleCat.of k k)) r)

/-- A morphism from the rank-two square-zero extension to the residue-field object is
the augmentation: it reads off the constant coordinate. -/
lemma squareZero_pair_to_specialFiberBase_apply
    {Λ k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    (f : (Deformation.artinianSquareZeroExtensionFunctor Λ k).obj
      (FGModuleCat.of k (k × k)) ⟶
      (Deformation.Examples.residueFieldBase Λ k))
    (r : TrivSqZeroExt k (k × k)) : f.hom r = r.fst := by
  have h := f.residue_comm r
  rw [Deformation.Examples.residueFieldBase_residueEquiv_residue] at h
  exact h.trans (by
    exact Deformation.squareZeroExtensionArtinian_residue Λ k
      (FGModuleCat.of k (k × k)) r)

/-- The augmentation of the dual numbers, as a morphism of Artinian local algebras onto
the residue-field object. -/
noncomputable def dualNumbersReduction
    {Λ k : Type*} [CommRing Λ] [Field k] [Algebra Λ k] :
    Deformation.augmentedDualNumbers (Λ := Λ) (k := k) ⟶
      (Deformation.Examples.residueFieldBase Λ k) where
  hom := (Deformation.dualNumbersOver Λ k).hom.hom
  isLocal := ⟨fun r hr ↦ TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hr⟩
  residue_comm r := by
    rw [Deformation.Examples.residueFieldBase_residueEquiv_residue]
    exact (Deformation.augmentationResidueEquiv_residue Λ k
      (Deformation.dualNumbersOver Λ k)
      (Deformation.squareZeroExtension_mem_artinianLocalOver Λ k (FGModuleCat.of k k)) r).symm

/-- A sequence of representations that is exact and short exact on underlying linear maps
gives a short exact sequence of group-algebra modules. -/
private theorem shortExact_map_equivalence_functor
    {k Γ : Type*} [Field k] [Group Γ] {A B C : Rep k Γ} (F : A ⟶ B) (G : B ⟶ C)
    (hfi : Function.Injective F.hom.toLinearMap) (hfr : LinearMap.range F.hom.toLinearMap =
      LinearMap.ker G.hom.toLinearMap) (hgs : Function.Surjective G.hom.toLinearMap) :
    ∃ hfg : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.map F ≫
      (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.map G = 0,
      (ShortComplex.mk _ _ hfg).ShortExact := by
  have hzero : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.map F ≫
      (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.map G = 0 := by
    ext v
    change G.hom.toLinearMap (F.hom.toLinearMap v) = 0
    exact LinearMap.mem_ker.1 (hfr ▸ LinearMap.mem_range_self F.hom.toLinearMap v)
  refine ⟨hzero, ShortComplex.ShortExact.mk' ?_ ((ModuleCat.mono_iff_injective _).2 hfi)
    ((ModuleCat.epi_iff_surjective _).2 hgs)⟩
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact (show Function.Exact F.hom.toLinearMap G.hom.toLinearMap from
    LinearMap.exact_iff.2 hfr.symm)

-- Nested scalar restrictions and the group-algebra equivalence require more elaboration.
/-- Every deformation of `ρ₀` over the dual numbers has an associated self-extension:
a short exact sequence of group-algebra modules whose middle term is the deformation. -/
theorem exists_associatedSelfExtension
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    (x : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      (Deformation.augmentedDualNumbers (Λ := Λ) (k := k))) :
    ∃ (M : ModuleCat (MonoidAlgebra k Γ))
      (f : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
        (Rep.of ρ₀) ⟶ M)
      (g : M ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
        (Rep.of ρ₀)) (hfg : f ≫ g = 0),
      (ShortComplex.mk f g hfg).ShortExact ∧
        IsAssociatedSelfExtension V ρ₀ x M f g := by
  rcases x with ⟨⟨X, Y, α⟩, hx⟩
  rcases X with @⟨A, M, hadd, hmod, hfin, hproj, ρ⟩
  change A = Deformation.augmentedDualNumbers at hx
  cases hx
  let : Module (DualNumber k) M := hmod
  let : Module.Finite (DualNumber k) M := hfin
  let : Module.Projective (DualNumber k) M := hproj
  let : IsLocalRing (DualNumber k) :=
    (Deformation.augmentedDualNumbers (Λ := Λ) (k := k)).isLocalRing
  have hbase (r : DualNumber k) : α.base.hom r = r.fst :=
    dualNumbers_to_specialFiberBase_apply α.base r
  let β : DualNumber k →+* k := α.base.hom.toRingHom
  let : Algebra (DualNumber k) k := β.toAlgebra
  let : Module (DualNumber k) V := Module.compHom V β
  let : IsScalarTower (DualNumber k) k V :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let gd : M →ₗ[DualNumber k] V :=
    Deformation.restrictAddHom β α.map α.map_smul
  have hgd : IsBaseChange k gd := α.isBaseChange
  let : Module.Free (DualNumber k) M := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis (DualNumber k) M
  have hsurj : Function.Surjective gd := dualNumber_baseChange_surjective hbase b gd hgd
  let : Module k M := Module.compHom M (algebraMap k (DualNumber k))
  let : IsScalarTower k (DualNumber k) M :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let q : M →+ V := α.map
  let ρd : Representation (DualNumber k) Γ M := ρ
  let gk : M →ₗ[k] V :=
    { q with
      map_smul' := fun a z ↦ by
        change q ((TrivSqZeroExt.inl a : DualNumber k) • z) = a • q z
        have hh : q ((TrivSqZeroExt.inl a : DualNumber k) • z) =
            β (TrivSqZeroExt.inl a) • q z := α.map_smul _ _
        exact hh.trans (congrArg (fun c : k ↦ c • q z) (hbase _)) }
  let t : M →ₗ[k] M :=
    { toFun := fun z ↦ (DualNumber.eps : DualNumber k) • z
      map_add' := smul_add _
      map_smul' := fun a z ↦ smul_comm _ _ _ }
  obtain ⟨fk, hfi, hfr, hfg⟩ := exists_injective_of_exact_endomorphism gk t hsurj
    (dualNumber_baseChange_eq_zero_iff hbase b gd hgd) (dualNumber_eps_exact b)
  have hfg_apply (z : M) : fk (gk z) = (DualNumber.eps : DualNumber k) • z :=
    LinearMap.congr_fun hfg z
  have hsurjk : Function.Surjective gk := hsurj
  let ρk : Representation k Γ M :=
    { toFun := fun γ ↦ (ρd γ).restrictScalars k
      map_one' := by ext z; exact LinearMap.congr_fun ρd.map_one z
      map_mul' := fun γ δ ↦ by ext z; exact LinearMap.congr_fun (ρd.map_mul γ δ) z }
  let F : Rep.of ρ₀ ⟶ Rep.of ρk := Rep.ofHom
    { __ := fk
      isIntertwining' := fun γ ↦ by
        ext v
        obtain ⟨z, rfl⟩ := hsurjk v
        change fk (ρ₀ γ (gk z)) = ρd γ (fk (gk z))
        have heq : gk (ρd γ z) = ρ₀ γ (gk z) := α.equivariant γ z
        rw [← heq, hfg_apply, hfg_apply, map_smul] }
  let G : Rep.of ρk ⟶ Rep.of ρ₀ := Rep.ofHom
    { __ := gk
      isIntertwining' := fun γ ↦ by ext z; exact α.equivariant γ z }
  let R := (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor
  let f := R.map F
  let g := R.map G
  obtain ⟨hzero, hexact⟩ := shortExact_map_equivalence_functor F G hfi hfr hsurjk
  refine ⟨R.obj (Rep.of ρk), f, g, hzero, hexact, ?_⟩
  · refine ⟨ρk.asModuleEquiv.toAddEquiv, ?_, ?_, fun _ ↦ rfl, hfg_apply⟩
    · intro a z
      change ρk.asModuleEquiv ((MonoidAlgebra.single 1 a) • z) =
        (TrivSqZeroExt.inl a : DualNumber k) • ρk.asModuleEquiv z
      rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single,
        ρk.map_one]
      rfl
    · intro γ z
      change ρk.asModuleEquiv ((MonoidAlgebra.single γ 1) • z) =
        ρd γ (ρk.asModuleEquiv z)
      rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single_one]
      rfl

/-- The two-variable analogue of `IsAssociatedSelfExtension`, for a deformation over the
square-zero extension by the rank-two module: the inclusion is split into the two
coordinate radicals. -/
def IsAssociatedPairExtension
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    (x : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      ((Deformation.artinianSquareZeroExtensionFunctor Λ k).obj
        (FGModuleCat.of k (k × k))))
    (M : ModuleCat (MonoidAlgebra k Γ))
    (f : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of (ρ₀.prod ρ₀)) ⟶ M)
    (g : M ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀)) : Prop :=
    let hbase : x.1.left.base = (Deformation.artinianSquareZeroExtensionFunctor Λ k).obj
      (FGModuleCat.of k (k × k)) := x.2
    ∃ e : M ≃+ x.1.left.carrier,
      (∀ (a : k) (z : M), e ((MonoidAlgebra.single (1 : Γ) a :
        MonoidAlgebra k Γ) • z) =
          (hbase.symm ▸ (show (Deformation.artinianSquareZeroExtensionFunctor Λ k).obj
            (FGModuleCat.of k (k × k)) from TrivSqZeroExt.inl a)) • e z) ∧
      (∀ (γ : Γ) (z : M), e ((MonoidAlgebra.single γ 1 :
        MonoidAlgebra k Γ) • z) = x.1.left.action γ (e z)) ∧
      (∀ z, g.hom z = x.1.hom.map (e z)) ∧
      (∀ z, e (f.hom (x.1.hom.map (e z), 0)) =
        (hbase.symm ▸ (show (Deformation.artinianSquareZeroExtensionFunctor Λ k).obj
          (FGModuleCat.of k (k × k)) from TrivSqZeroExt.inr (1, 0))) • e z) ∧
      (∀ z, e (f.hom (0, x.1.hom.map (e z))) =
        (hbase.symm ▸ (show (Deformation.artinianSquareZeroExtensionFunctor Λ k).obj
          (FGModuleCat.of k (k × k)) from TrivSqZeroExt.inr (0, 1))) • e z)

/-- Every deformation of `ρ₀` over the rank-two square-zero extension has an associated
pair extension of the twofold product of `ρ₀` by itself. -/
theorem exists_associatedPairExtension
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    (x : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      ((Deformation.artinianSquareZeroExtensionFunctor Λ k).obj
        (FGModuleCat.of k (k × k)))) :
    ∃ (M : ModuleCat (MonoidAlgebra k Γ))
      (f : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
        (Rep.of (ρ₀.prod ρ₀)) ⟶ M)
      (g : M ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
        (Rep.of ρ₀)) (hfg : f ≫ g = 0),
      (ShortComplex.mk f g hfg).ShortExact ∧
        IsAssociatedPairExtension V ρ₀ x M f g := by
  rcases x with ⟨⟨X, Y, α⟩, hx⟩
  rcases X with @⟨A, M, hadd, hmod, hfin, hproj, ρ⟩
  change A = (Deformation.artinianSquareZeroExtensionFunctor Λ k).obj
    (FGModuleCat.of k (k × k)) at hx
  cases hx
  let : Module (TrivSqZeroExt k (k × k)) M := hmod
  let : Module.Finite (TrivSqZeroExt k (k × k)) M := hfin
  let : Module.Projective (TrivSqZeroExt k (k × k)) M := hproj
  let : IsLocalRing (TrivSqZeroExt k (k × k)) :=
    ((Deformation.artinianSquareZeroExtensionFunctor Λ k).obj
      (FGModuleCat.of k (k × k))).isLocalRing
  have hbase (r : TrivSqZeroExt k (k × k)) : α.base.hom r = r.fst :=
    squareZero_pair_to_specialFiberBase_apply α.base r
  let β : TrivSqZeroExt k (k × k) →+* k := α.base.hom.toRingHom
  let : Algebra (TrivSqZeroExt k (k × k)) k := β.toAlgebra
  let : Module (TrivSqZeroExt k (k × k)) V := Module.compHom V β
  let : IsScalarTower (TrivSqZeroExt k (k × k)) k V :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let gd : M →ₗ[TrivSqZeroExt k (k × k)] V :=
    Deformation.restrictAddHom β α.map α.map_smul
  have hgd : IsBaseChange k gd := α.isBaseChange
  let : Module.Free (TrivSqZeroExt k (k × k)) M := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis (TrivSqZeroExt k (k × k)) M
  let : Module k M := Module.compHom M (algebraMap k (TrivSqZeroExt k (k × k)))
  let : IsScalarTower k (TrivSqZeroExt k (k × k)) M :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let q : M →+ V := α.map
  let gk : M →ₗ[k] V :=
    { q with
      map_smul' := fun a z ↦ by
        change q ((TrivSqZeroExt.inl a : TrivSqZeroExt k (k × k)) • z) = a • q z
        have hh : q ((TrivSqZeroExt.inl a : TrivSqZeroExt k (k × k)) • z) =
            β (TrivSqZeroExt.inl a) • q z := α.map_smul _ _
        exact hh.trans (congrArg (fun c : k ↦ c • q z) (hbase _)) }
  obtain ⟨fk, hfi, hfr, s, hs, hf⟩ :=
    exists_squareZero_pair_kernelMap hbase b gd hgd gk (fun _ ↦ rfl)
  have hsurjk : Function.Surjective gk := by
    intro v
    exact ⟨s v, hs v⟩
  let ρd : Representation (TrivSqZeroExt k (k × k)) Γ M := ρ
  let ρk : Representation k Γ M :=
    { toFun := fun γ ↦ (ρd γ).restrictScalars k
      map_one' := by ext z; exact LinearMap.congr_fun ρd.map_one z
      map_mul' := fun γ δ ↦ by ext z; exact LinearMap.congr_fun (ρd.map_mul γ δ) z }
  let F : Rep.of (ρ₀.prod ρ₀) ⟶ Rep.of ρk := Rep.ofHom
    { __ := fk
      isIntertwining' := fun γ ↦ by
        apply LinearMap.ext
        intro v
        change fk ((ρ₀ γ v.1, ρ₀ γ v.2)) = ρd γ (fk v)
        rw [hf, hf]
        exact (squareZero_pair_kernelMap_equivariant hbase b gd hgd
          s (fun v ↦ (hs v).trans rfl) (ρd γ) (ρ₀ γ).toAddMonoidHom
          (fun z ↦ α.equivariant γ z) v).symm }
  let G : Rep.of ρk ⟶ Rep.of ρ₀ := Rep.ofHom
    { __ := gk
      isIntertwining' := fun γ ↦ by ext z; exact α.equivariant γ z }
  let R := (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor
  let f := R.map F
  let g := R.map G
  obtain ⟨hzero, hexact⟩ := shortExact_map_equivalence_functor F G hfi hfr hsurjk
  have hann (c : TrivSqZeroExt k (k × k)) (hc : ∀ x, gd x = 0 → c • x = 0) (z : M) :
      c • s (gk z) = c • z := by
    have hz : gd (s (gk z) - z) = 0 := by
      change gk (s (gk z) - z) = 0
      rw [map_sub, hs, sub_self]
    simpa only [smul_sub, sub_eq_zero] using hc _ hz
  refine ⟨R.obj (Rep.of ρk), f, g, hzero, hexact, ?_⟩
  · refine ⟨ρk.asModuleEquiv.toAddEquiv, ?_, ?_, fun _ ↦ rfl, ?_, ?_⟩
    · intro a z
      change ρk.asModuleEquiv ((MonoidAlgebra.single 1 a) • z) =
        (TrivSqZeroExt.inl a : TrivSqZeroExt k (k × k)) • ρk.asModuleEquiv z
      rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single,
        ρk.map_one]
      rfl
    · intro γ z
      change ρk.asModuleEquiv ((MonoidAlgebra.single γ 1) • z) =
        ρd γ (ρk.asModuleEquiv z)
      rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single_one]
      rfl
    · intro z
      change fk (gk z, 0) = _
      rw [hf]
      simp only [map_zero, smul_zero, add_zero]
      exact hann _ (fun x hx ↦
        (squareZero_pair_radical_annihilates_kernel hbase b gd hgd x hx).1) z
    · intro z
      change fk (0, gk z) = _
      rw [hf]
      simp only [map_zero, smul_zero, zero_add]
      exact hann _ (fun x hx ↦
        (squareZero_pair_radical_annihilates_kernel hbase b gd hgd x hx).2) z

/-- Every short exact self-extension of `ρ₀` over the group algebra arises from a
deformation of `ρ₀` over the dual numbers. -/
theorem exists_deformation_of_selfExtension
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    (M : ModuleCat.{m} (MonoidAlgebra k Γ))
    (f : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀) ⟶ M)
    (g : M ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀))
    (hfg : f ≫ g = 0) (hexact : (ShortComplex.mk f g hfg).ShortExact) :
    ∃ x : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      (Deformation.augmentedDualNumbers (Λ := Λ) (k := k)),
      IsAssociatedSelfExtension V ρ₀ x M f g := by
  let R := Rep.ofModuleMonoidAlgebra (k := k) (G := Γ)
  let U := R.obj M
  let F : Rep.of ρ₀ ⟶ U := (Rep.unitIso (Rep.of ρ₀)).hom ≫ R.map f
  let G : U ⟶ Rep.of ρ₀ := R.map g ≫ (Rep.unitIso (Rep.of ρ₀)).inv
  let fk : V →ₗ[k] U := F.hom.toLinearMap
  let gk : U →ₗ[k] V := G.hom.toLinearMap
  have hgf : gk.comp fk = 0 := by
    ext v
    exact congrArg (fun q ↦ q.hom v) hfg
  have hfi : Function.Injective fk := (ModuleCat.mono_iff_injective f).1 hexact.mono_f
  have hgs : Function.Surjective gk := (ModuleCat.epi_iff_surjective g).1 hexact.epi_g
  have hker : LinearMap.range fk = LinearMap.ker gk := by
    symm
    apply LinearMap.exact_iff.1
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hexact.exact
  have hfρ (γ : Γ) : fk.comp (ρ₀ γ) = (U.ρ γ).comp fk := F.hom.isIntertwining' γ
  have hgρ (γ : Γ) : gk.comp (U.ρ γ) = (ρ₀ γ).comp gk := G.hom.isIntertwining' γ
  let := extensionDualNumberModule fk gk hgf
  let : Module.Finite (DualNumber k) U :=
    extensionDualNumberModule_finite fk gk hgf hker hgs
  let : Module.Free (DualNumber k) U :=
    extensionDualNumberModule_free fk gk hgf hfi hker hgs
  let X : Deformation.RepresentationCategory.{u, w, w, m} Λ k Γ := by
    refine {
      base := Deformation.augmentedDualNumbers (Λ := Λ) (k := k)
      carrier := U
      addCommGroup := inferInstanceAs (AddCommGroup U)
      module := ?_
      finite := ?_
      projective := ?_
      action := ?_ }
    · change Module (DualNumber k) U
      exact extensionDualNumberModule fk gk hgf
    · change Module.Finite (DualNumber k) U
      exact extensionDualNumberModule_finite fk gk hgf hker hgs
    · change Module.Projective (DualNumber k) U
      infer_instance
    · change Representation (DualNumber k) Γ U
      exact extensionLiftedRepresentation ρ₀ U.ρ fk gk hgf hfρ hgρ
  have hgsml (r : DualNumber k) (z : U) :
      gk (r • z) = r.fst • gk z := by
    rw [extensionDualNumberModule_smul fk gk hgf]
    change gk (r.fst • z + r.snd • fk (gk z)) = _
    rw [map_add, map_smul, map_smul,
      show gk (fk (gk z)) = 0 from LinearMap.congr_fun hgf _, smul_zero, add_zero]
  let α : X ⟶ Deformation.RepresentationCategory.specialFiber
      (Λ := Λ) V ρ₀ := by
    dsimp only [X, Deformation.RepresentationCategory.specialFiber]
    refine {
      base := dualNumbersReduction (Λ := Λ) (k := k)
      map := gk.toAddMonoidHom
      map_smul := hgsml
      equivariant := fun γ z ↦ LinearMap.congr_fun (hgρ γ) z
      isBaseChange := ?_ }
    let : Algebra (DualNumber k) k :=
      (dualNumbersReduction (Λ := Λ) (k := k)).hom.toAlgebra
    let : Module (DualNumber k) V := Module.compHom V
      (dualNumbersReduction (Λ := Λ) (k := k)).hom.toRingHom
    let : IsScalarTower (DualNumber k) k V :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    exact extensionDualNumberModule_isBaseChange (fun _ ↦ rfl) fk gk hgf hker hgs _
      (fun _ ↦ rfl)
  refine ⟨⟨Over.mk α, ?_⟩, ?_⟩
  · dsimp [deformationCategoryProjection, representationProjection, X]
  · refine ⟨(RestrictScalars.addEquiv k (MonoidAlgebra k Γ) M).symm, ?_, ?_, ?_, ?_⟩
    · intro a z
      exact (extensionDualNumberModule_inl_smul fk gk hgf a
        ((RestrictScalars.addEquiv k (MonoidAlgebra k Γ) M).symm z)).symm
    · intro γ z
      rfl
    · intro z
      rfl
    · intro z
      exact (extensionDualNumberModule_eps_smul fk gk hgf z).symm

/-- Two self-extensions associated to the same deformation have the same extension class. -/
theorem associatedSelfExtension_extClass_eq
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    (x : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      (Deformation.augmentedDualNumbers (Λ := Λ) (k := k)))
    {M M' : ModuleCat (MonoidAlgebra k Γ)}
    {f : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀) ⟶ M}
    {g : M ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀)}
    {f' : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀) ⟶ M'}
    {g' : M' ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀)}
    {hfg : f ≫ g = 0} {hfg' : f' ≫ g' = 0}
    (h : (ShortComplex.mk f g hfg).ShortExact)
    (h' : (ShortComplex.mk f' g' hfg').ShortExact)
    (hx : IsAssociatedSelfExtension V ρ₀ x M f g)
    (hx' : IsAssociatedSelfExtension V ρ₀ x M' f' g') :
    h.extClass = h'.extClass := by
  obtain ⟨e, he₁, heΓ, heq, heε⟩ := hx
  obtain ⟨e', he₁', heΓ', heq', heε'⟩ := hx'
  let a : M ≃+ M' := e.trans e'.symm
  have ha (z : M) : e' (a z) = e z := e'.apply_symm_apply _
  have h₁ (c : k) (z : M) :
      a ((MonoidAlgebra.single 1 c : MonoidAlgebra k Γ) • z) =
        (MonoidAlgebra.single 1 c : MonoidAlgebra k Γ) • a z := by
    apply e'.injective
    rw [ha, he₁, he₁', ha]
  have hΓ (γ : Γ) (z : M) :
      a ((MonoidAlgebra.single γ 1 : MonoidAlgebra k Γ) • z) =
        (MonoidAlgebra.single γ 1 : MonoidAlgebra k Γ) • a z := by
    apply e'.injective
    rw [ha, heΓ, heΓ', ha]
  let l : M ≃ₗ[MonoidAlgebra k Γ] M' :=
    { a with
      map_smul' := fun r z ↦ by
        change a (r • z) = r • a z
        induction r using MonoidAlgebra.induction_linear with
        | zero => simp only [zero_smul, map_zero]
        | add r s hr hs => simp only [add_smul, map_add, hr, hs]
        | single γ c =>
          rw [show MonoidAlgebra.single γ c =
              (MonoidAlgebra.single γ 1 : MonoidAlgebra k Γ) *
                MonoidAlgebra.single 1 c by simp, mul_smul, hΓ, h₁, mul_smul] }
  have hq (z : M) : g'.hom (l z) = g.hom z := by
    rw [heq', heq]
    exact congrArg x.1.hom.map (ha z)
  have hi : f ≫ l.toModuleIso.hom = f' := by
    ext v
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective g).1 h.epi_g v
    apply e'.injective
    change e' (a (f.hom (g.hom z))) = e' (f'.hom (g.hom z))
    rw [ha, heε, ← hq, heε']
    exact congrArg _ (ha z).symm
  exact (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum _ _ _).2.1
    _ _ _ _ _ _ _ _ h h' |>.2 ⟨l.toModuleIso, hi, by ext z; exact hq z⟩

end Deformation
