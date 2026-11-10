module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackKernelMorphism
public import StacksFrontier.Deformation.Artin.FiniteDimensional.KernelTangent

/-!
# The tangent space of `Coh_{X/Y}` is bounded by `T(Y)` and `Ext¹(𝒢₀, 𝒢₀)`

Let `D` be the situation of Stacks 08KB, `x₀ = (Spec k, g₀, 𝒢₀)` an object of `Coh_{X/Y}` over a
field `k`, and `φ : 𝓕_{Coh_{X/Y}, k, x₀} ⟶ 𝓕_{Y, k, y₀}` the `1`-morphism forgetting the module.
A class in the kernel of the tangent map of `φ` at `k[M]` is the class of a deformation with a
trivial base, and the class of its extension `0 ⟶ 𝒢₀ ⊗ M ⟶ r_*ℱ ⟶ 𝒢₀ ⟶ 0` in
`Ext¹(𝒢₀, 𝒢₀ ⊗ M)` depends only on the tangent class
(`AlgebraicGeometry.Space.CoherentSituation.extensionClass_kernelExtension_comp` at the identity),
is natural in `M` (the same lemma at a linear map) and determines the tangent class
(`AlgebraicGeometry.Space.CoherentSituation.exists_morphism_of_extensionClass_eq`). So the
tangent module of `𝓕_{Coh_{X/Y}, k, x₀}` at `M` is finite-dimensional as soon as the tangent
module of `𝓕_{Y, k, y₀}` at `M` and `Ext¹(𝒢₀, 𝒢₀ ⊗ M)` are
(`Deformation.finiteDimensional_tangentModuleAt_of_ker`). This is the tangent half of the proof
of Stacks 08W8.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.kernelClass`: the extension class of a tangent class
  in the kernel of the tangent map to `Y`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.finiteDimensional_tangentModuleAt_cohDef`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation Deformation.Artin

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe w' u

/-- The `kᵐᵒᵖ`-module structure on a `k`-module `V` over a field, with `op a` acting as `a`. -/
local instance {k : Type u} [Field k] (V : FGModuleCat.{u} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

/-- The action of `k` on a `k`-module `V` over a field is central. -/
local instance {k : Type u} [Field k] (V : FGModuleCat.{u} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

namespace AlgebraicGeometry.Space

namespace CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

attribute [local instance] cohCategory predefCategory

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
  (x₀ : CoherentObject D)
  (hx₀ : D.cohQ.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  [HasExt.{w'} (Modules.{u, u} B S hS (D.space x₀.T).1 (D.space x₀.T).2)]

/-! ### The extension class of a deformation with a trivial base -/

section DeformationObject

variable {M N : FGModuleCat.{u} k}

/-- The extension class of a deformation over `k[M]` with a trivial base, at a chosen trivial
base (`AlgebraicGeometry.Space.CoherentSituation.trivialBase_unique`: there is only one). -/
def defExtClass (d : DeformationObject iΛ D.cohQ x₀ hx₀)
    (hd : d.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (h : D.HasTrivialBase' iΛ x₀ hx₀ M d hd) :
    letI := D.residueLinear iΛ x₀ hx₀
    Abelian.Ext x₀.F (ModuleDeformation.copowerObj x₀.F M) 1 :=
  letI := D.residueLinear iΛ x₀ hx₀
  (D.kernelExtension iΛ x₀ hx₀ M d hd h.choose h.choose_spec).extensionClass

/-- **Naturality of the extension class of a deformation with a trivial base.** -/
theorem defExtClass_comp {d e : DeformationObject iΛ D.cohQ x₀ hx₀}
    (hd : d.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (he : e.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj N)
    (h : D.HasTrivialBase' iΛ x₀ hx₀ M d hd) (h' : D.HasTrivialBase' iΛ x₀ hx₀ N e he)
    (f : M ⟶ N) (m : DeformationMorphism iΛ D.cohQ x₀ hx₀ d e)
    (hm : m.ringHom = eqToHom hd ≫ (squareZeroExtensionArtinian.{u, u, u} Λ k).map f ≫
      eqToHom he.symm) :
    letI := D.residueLinear iΛ x₀ hx₀
    (D.defExtClass iΛ x₀ hx₀ d hd h).comp
        (Abelian.Ext.mk₀ ((ModuleDeformation.copowerFunctor x₀.F).map f)) (add_zero 1) =
      D.defExtClass iΛ x₀ hx₀ e he h' :=
  D.extensionClass_kernelExtension_comp hd he m hm h.choose h.choose_spec h'.choose
    h'.choose_spec

/-- The extension class of a deformation with a trivial base is invariant under morphisms over
the identity of `k[M]`. -/
theorem defExtClass_eq_of_morphism {d e : DeformationObject iΛ D.cohQ x₀ hx₀}
    (hd : d.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (he : e.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (h : D.HasTrivialBase' iΛ x₀ hx₀ M d hd) (h' : D.HasTrivialBase' iΛ x₀ hx₀ M e he)
    (m : DeformationMorphism iΛ D.cohQ x₀ hx₀ d e) (hm : m.ringHom = eqToHom (hd.trans he.symm)) :
    D.defExtClass iΛ x₀ hx₀ d hd h = D.defExtClass iΛ x₀ hx₀ e he h' := by
  let := D.residueLinear iΛ x₀ hx₀
  have key := D.defExtClass_comp iΛ x₀ hx₀ hd he h h' (𝟙 M) m (by
    rw [hm, CategoryTheory.Functor.map_id, Category.id_comp, eqToHom_trans])
  rw [CategoryTheory.Functor.map_id] at key
  exact (Abelian.Ext.comp_mk₀_id (D.defExtClass iΛ x₀ hx₀ d hd h)).symm.trans key

/-- **The extension class of a deformation with a trivial base determines it up to a morphism
over the identity of `k[M]`.** -/
theorem exists_morphism_of_defExtClass_eq {d e : DeformationObject iΛ D.cohQ x₀ hx₀}
    (hd : d.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (he : e.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (h : D.HasTrivialBase' iΛ x₀ hx₀ M d hd) (h' : D.HasTrivialBase' iΛ x₀ hx₀ M e he)
    (hc : D.defExtClass iΛ x₀ hx₀ d hd h = D.defExtClass iΛ x₀ hx₀ e he h') :
    ∃ m : DeformationMorphism iΛ D.cohQ x₀ hx₀ d e, m.ringHom = eqToHom (hd.trans he.symm) :=
  D.exists_morphism_of_extensionClass_eq iΛ x₀ hx₀ d e hd he h.choose h.choose_spec h'.choose
    h'.choose_spec hc

end DeformationObject

/-! ### The extension class of a tangent class in the kernel -/

section Fiber

variable {M N : FGModuleCat.{u} k}

omit [HasExt.{w'} (Modules.{u, u} B S hS (D.space x₀.T).1 (D.space x₀.T).2)] in
/-- The algebra of the deformation of an object of the fibre over `k[M]`. -/
theorem fiber_algebra
    (x : (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection).p.Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)) :
    ((D.cohDef iΛ x₀ hx₀).objects x.1).algebra =
      (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M :=
  ((D.cohDef iΛ x₀ hx₀).object_projection x.1).symm.trans x.2

/-- The extension class of an object of the fibre over `k[M]` with a trivial base. -/
abbrev fiberExtClass
    (x : (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection).p.Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
    (h : D.HasTrivialBase iΛ x₀ hx₀ M x) :
    letI := D.residueLinear iΛ x₀ hx₀
    Abelian.Ext x₀.F (ModuleDeformation.copowerObj x₀.F M) 1 :=
  D.defExtClass iΛ x₀ hx₀ ((D.cohDef iΛ x₀ hx₀).objects x.1) (D.fiber_algebra iΛ x₀ hx₀ x) h

omit [HasExt.{w'} (Modules.{u, u} B S hS (D.space x₀.T).1 (D.space x₀.T).2)] in
/-- A morphism of the predeformation category over `k[f]` is a morphism of deformations over
`k[f]`. -/
theorem ringHom_eq_of_isHomLift {M N : FGModuleCat.{u} k} (f : M ⟶ N)
    (x : (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection).p.Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
    (y : (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection).p.Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj N))
    (a : x.1 ⟶ y.1)
    [(D.cohDef iΛ x₀ hx₀).projection.IsHomLift
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map f) a] :
    ((D.cohDef iΛ x₀ hx₀).morphisms _ _ a).ringHom =
      eqToHom (D.fiber_algebra iΛ x₀ hx₀ x) ≫ (squareZeroExtensionArtinian.{u, u, u} Λ k).map f ≫
        eqToHom (D.fiber_algebra iΛ x₀ hx₀ y).symm :=
  IsHomLift.fac' (D.cohDef iΛ x₀ hx₀).projection _ a

/-- **The extension class is an invariant of the object of the fibre up to isomorphism.** -/
theorem fiberExtClass_eq_of_iso
    (x y : (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection).p.Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
    (hx : D.HasTrivialBase iΛ x₀ hx₀ M x) (hy : D.HasTrivialBase iΛ x₀ hx₀ M y) (e : x ≅ y) :
    D.fiberExtClass iΛ x₀ hx₀ x hx = D.fiberExtClass iΛ x₀ hx₀ y hy := by
  have : (D.cohDef iΛ x₀ hx₀).projection.IsHomLift
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map (𝟙 M)) e.hom.1 := by
    rw [CategoryTheory.Functor.map_id]
    exact e.hom.2
  exact D.defExtClass_eq_of_morphism iΛ x₀ hx₀ _ _ hx hy _
    ((D.ringHom_eq_of_isHomLift iΛ x₀ hx₀ (𝟙 M) x y e.hom.1).trans (by
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
      exact eqToHom_trans _ _))

variable (h𝓕 : IsDeformationCategory.{u, u, u} (D.cohDef iΛ x₀ hx₀).projection)
  (h𝓖 : IsDeformationCategory.{u, u, u} (D.baseDef iΛ x₀ hx₀).projection)

/-- A chosen representative of a tangent class. -/
abbrev tangentRep (M : FGModuleCat.{u} k)
    (t : ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection)
      h𝓕 M)) :
    (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection).p.Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M) :=
  (tangentClassAt_surjective.{u, u, u} _ h𝓕 M t).choose

omit [HasExt.{w'} (Modules.{u, u} B S hS (D.space x₀.T).1 (D.space x₀.T).2)] in
/-- The tangent class of the chosen representative of a tangent class `t` is `t`. -/
theorem tangentClassAt_tangentRep (M : FGModuleCat.{u} k)
    (t : ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection)
      h𝓕 M)) :
    tangentClassAt.{u, u, u} _ h𝓕 M (D.tangentRep iΛ x₀ hx₀ h𝓕 M t) = t :=
  (tangentClassAt_surjective.{u, u, u} _ h𝓕 M t).choose_spec

open Classical in
/-- **The extension class of a tangent class in the kernel of the tangent map to `Y`**, and `0`
outside the kernel. -/
def kernelClass (M : FGModuleCat.{u} k)
    (t : ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection)
      h𝓕 M)) :
    letI := D.residueLinear iΛ x₀ hx₀
    Abelian.Ext x₀.F (ModuleDeformation.copowerObj x₀.F M) 1 :=
  letI := D.residueLinear iΛ x₀ hx₀
  if ht : tangentMapAt.{u, u, u} h𝓕 h𝓖 (D.cohToBase iΛ x₀ hx₀) M t = 0 then
    D.fiberExtClass iΛ x₀ hx₀ (D.tangentRep iΛ x₀ hx₀ h𝓕 M t)
      (D.hasTrivialBase_of_tangentMapAt_eq_zero iΛ x₀ hx₀ M h𝓕 h𝓖 _
        ((congrArg _ (D.tangentClassAt_tangentRep iΛ x₀ hx₀ h𝓕 M t)).trans ht))
  else 0

/-- **The extension class of a tangent class in the kernel is computed by any representative.** -/
theorem kernelClass_tangentClassAt
    (x : (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection).p.Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
    (hx : tangentMapAt.{u, u, u} h𝓕 h𝓖 (D.cohToBase iΛ x₀ hx₀) M
      (tangentClassAt.{u, u, u} _ h𝓕 M x) = 0) :
    D.kernelClass iΛ x₀ hx₀ h𝓕 h𝓖 M (tangentClassAt.{u, u, u} _ h𝓕 M x) =
      D.fiberExtClass iΛ x₀ hx₀ x
        (D.hasTrivialBase_of_tangentMapAt_eq_zero iΛ x₀ hx₀ M h𝓕 h𝓖 x hx) := by
  rw [kernelClass, dite_eq_left hx]
  obtain ⟨e⟩ := (tangentClassAt_eq_iff.{u, u, u} _ h𝓕 M _ x).1
    (D.tangentClassAt_tangentRep iΛ x₀ hx₀ h𝓕 M _)
  exact D.fiberExtClass_eq_of_iso iΛ x₀ hx₀ _ _ _ _ e

/-- **Naturality of the extension class on the kernel.** -/
theorem kernelClass_map (f : M ⟶ N)
    (t : ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection)
      h𝓕 M))
    (ht : tangentMapAt.{u, u, u} h𝓕 h𝓖 (D.cohToBase iΛ x₀ hx₀) M t = 0) :
    letI := D.residueLinear iΛ x₀ hx₀
    D.kernelClass iΛ x₀ hx₀ h𝓕 h𝓖 N (((associatedTangentSpaceModuleStructure.{u, u, u}
        (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection) h𝓕.predeformation
        (tangentConditionS2.{u, u, u} h𝓕)).functor.map f) t) =
      ((ModuleDeformation.extCoefficientFunctor x₀.F
        (ModuleDeformation.copowerFunctor (k := k) x₀.F) 1).map f)
        (D.kernelClass iΛ x₀ hx₀ h𝓕 h𝓖 M t) := by
  let := D.residueLinear iΛ x₀ hx₀
  obtain ⟨x, rfl⟩ := tangentClassAt_surjective.{u, u, u} _ h𝓕 M t
  let P := Deformation.chosenPushforwardsAtOfCofiberedInGroupoids h𝓕.predeformation.cofibered x.1
  let c : Under ((D.cohDef iΛ x₀ hx₀).projection.obj x.1) :=
    Under.mk (eqToHom x.2 ≫ (squareZeroExtensionArtinian.{u, u, u} Λ k).map f)
  let y : (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection).p.Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj N) := ⟨(P.obj c).1, (P.obj c).2⟩
  let a : x.1 ⟶ y.1 := P.inclusion c
  have : (D.cohDef iΛ x₀ hx₀).projection.IsHomLift
      (eqToHom x.2 ≫ (squareZeroExtensionArtinian.{u, u, u} Λ k).map f) a :=
    (P.inclusion_cocartesian c).toIsHomLift
  have : (D.cohDef iΛ x₀ hx₀).projection.IsHomLift
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map f) a :=
    (IsHomLift.lift_eqToHom_comp_iff (p := (D.cohDef iΛ x₀ hx₀).projection)
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map f) a x.2).1 inferInstance
  have : (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection).p.IsHomLift
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map f) a := this
  have hmap := tangentModuleAt_map_tangentClassAt.{u, u, u} h𝓕 f x y a
  have hy : tangentMapAt.{u, u, u} h𝓕 h𝓖 (D.cohToBase iΛ x₀ hx₀) N
      (tangentClassAt.{u, u, u} _ h𝓕 N y) = 0 := by
    rw [← hmap, tangentMapAt_naturality h𝓕 h𝓖, ht, map_zero]
  rw [hmap, D.kernelClass_tangentClassAt iΛ x₀ hx₀ h𝓕 h𝓖 y hy,
    D.kernelClass_tangentClassAt iΛ x₀ hx₀ h𝓕 h𝓖 x ht]
  exact (D.defExtClass_comp iΛ x₀ hx₀ _ _ _ _ f _
    (D.ringHom_eq_of_isHomLift iΛ x₀ hx₀ f x y a)).symm

/-- **The extension class is injective on the kernel.** -/
theorem kernelClass_injective
    (t t' : ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection)
      h𝓕 M))
    (ht : tangentMapAt.{u, u, u} h𝓕 h𝓖 (D.cohToBase iΛ x₀ hx₀) M t = 0)
    (ht' : tangentMapAt.{u, u, u} h𝓕 h𝓖 (D.cohToBase iΛ x₀ hx₀) M t' = 0)
    (h : D.kernelClass iΛ x₀ hx₀ h𝓕 h𝓖 M t = D.kernelClass iΛ x₀ hx₀ h𝓕 h𝓖 M t') : t = t' := by
  obtain ⟨x, rfl⟩ := tangentClassAt_surjective.{u, u, u} _ h𝓕 M t
  obtain ⟨x', rfl⟩ := tangentClassAt_surjective.{u, u, u} _ h𝓕 M t'
  rw [D.kernelClass_tangentClassAt iΛ x₀ hx₀ h𝓕 h𝓖 x ht,
    D.kernelClass_tangentClassAt iΛ x₀ hx₀ h𝓕 h𝓖 x' ht'] at h
  obtain ⟨m, hm⟩ := D.exists_morphism_of_defExtClass_eq iΛ x₀ hx₀ _ _ _ _ h
  let φ : x.1 ⟶ x'.1 := ((D.cohDef iΛ x₀ hx₀).morphisms _ _).symm m
  have hφ₀ : (D.cohDef iΛ x₀ hx₀).projection.map φ = eqToHom (x.2.trans x'.2.symm) := by
    have e := (D.cohDef iΛ x₀ hx₀).morphism_projection φ
    rwa [Equiv.apply_symm_apply, hm] at e
  have hφ : (D.cohDef iΛ x₀ hx₀).projection.map φ =
      eqToHom x.2 ≫ 𝟙 _ ≫ eqToHom x'.2.symm := by
    rwa [Category.id_comp, eqToHom_trans]
  have hlift : (D.cohDef iΛ x₀ hx₀).projection.IsHomLift (𝟙 _) φ :=
    IsHomLift.of_fac' _ _ _ x.2 x'.2 hφ
  have : IsIso ((D.cohDef iΛ x₀ hx₀).projection.map φ) := by
    rw [hφ₀]
    exact Iso.isIso_hom (eqToIso (x.2.trans x'.2.symm))
  have : IsIso φ := isIso_of_isCofiberedInGroupoids_of_map_isIso h𝓕.predeformation.cofibered φ
  exact (tangentClassAt_eq_iff.{u, u, u} _ h𝓕 M x x').2
    ⟨fiberIsoOfVertical x x' (asIso φ) hlift⟩

/-- **Stacks 08W8, the tangent space, from its two bounds.** The tangent module of
`𝓕_{Coh_{X/Y}, k, x₀}` at `M` is finite-dimensional as soon as the tangent module of
`𝓕_{Y, k, y₀}` at `M` and `Ext¹(𝒢₀, 𝒢₀ ⊗ M)` are. -/
theorem finiteDimensional_tangentModuleAt_cohDef (M : FGModuleCat.{u} k)
    [FiniteDimensional k ↥(tangentModuleAt.{u, u, u}
      (BasedCategory.ofFunctor (D.baseDef iΛ x₀ hx₀).projection) h𝓖 M)]
    [hExt : letI := D.residueLinear iΛ x₀ hx₀
      FiniteDimensional k (Abelian.Ext x₀.F (ModuleDeformation.copowerObj x₀.F M) 1)] :
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u}
      (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection) h𝓕 M) := by
  let := D.residueLinear iΛ x₀ hx₀
  have : FiniteDimensional k ((ModuleDeformation.extCoefficientFunctor x₀.F
      (ModuleDeformation.copowerFunctor (k := k) x₀.F) 1).obj M) := hExt
  exact finiteDimensional_tangentModuleAt_of_ker h𝓕 h𝓖 (D.cohToBase iΛ x₀ hx₀)
    (ModuleDeformation.extCoefficientFunctor x₀.F
      (ModuleDeformation.copowerFunctor (k := k) x₀.F) 1)
    (D.kernelClass iΛ x₀ hx₀ h𝓕 h𝓖)
    (fun f t ht => D.kernelClass_map iΛ x₀ hx₀ h𝓕 h𝓖 f t ht) M
    (fun t t' ht ht' h => D.kernelClass_injective iΛ x₀ hx₀ h𝓕 h𝓖 t t' ht ht' h)

end Fiber

end CoherentSituation

end AlgebraicGeometry.Space

end
