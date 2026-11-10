module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import StacksFrontier.AlgebraicGeometry.Modules.AffineSections
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Rlim

/-!
# The tower of sections of the cohomology sheaves of an inverse system

Let `X` be a scheme and let `K` be an inverse system of objects of the derived category of
`𝒪_X`-modules indexed by the natural numbers. For a degree `q` and an open `U ⊆ X`, taking
sections over `U` of the degree-`q` cohomology sheaves turns `K` into an inverse system of
abelian groups.

On an *affine* open this tower inherits surjectivity: if the cohomology sheaves are
quasi-coherent and the transition maps `H^q(K_{n+1}) → H^q(K_n)` are epimorphisms, then the
maps on sections over `U` are surjective, because a surjection of quasi-coherent modules on an
affine scheme is surjective on global sections. A surjective tower is Mittag-Leffler, so its
first derived inverse limit vanishes.

## Main definitions

* `AlgebraicGeometry.sectionsTower`: the inverse system of abelian groups of sections over an
  open of the degree-`q` cohomology sheaves of an inverse system in the derived category.

## Main results

* `AlgebraicGeometry.isZero_firstDerivedLimit_sections`: on an affine open, a tower of
  quasi-coherent cohomology sheaves with epimorphic transitions has vanishing first derived
  inverse limit of sections.

## Implementation notes

An object of the derived category with quasi-coherent cohomology is described by the object
together with quasi-coherence of each of its cohomology sheaves, rather than as an object of a
subcategory, so that the statement applies to an arbitrary inverse system. The surjectivity
hypothesis is expressed by epimorphisms in the category of `𝒪_X`-modules. The derived limit is
taken in the two-term product model `Rlim.firstDerivedLimit` of inverse systems of abelian
groups.

## References

* [Stacks Project, Tag 0A0J](https://stacks.math.columbia.edu/tag/0A0J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

universe u

/-- The inverse system of abelian groups of sections over an open `U` of a scheme `X` of the
degree-`q` cohomology sheaves of an inverse system `K` in the derived category of
`𝒪_X`-modules. -/
public noncomputable abbrev sectionsTower (X : Scheme.{u})
    (K : ℕᵒᵖ ⥤ DerivedCategory.{u + 1} X.Modules) (q : ℤ) (U : X.Opens) :
    Rlim.InvSystemAb.{u} :=
  K ⋙ DerivedCategory.homologyFunctor X.Modules q ⋙
    SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙
      forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U))) AddCommGrpCat.{u}

/-- A surjection of quasi-coherent `𝒪_X`-modules is surjective on sections over an affine
open. -/
private theorem epi_app_of_isAffineOpen {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) (hf : Epi f) : Epi (f.val.app (op U)) := by
  let i : Spec (.of Γ(X, U)) ⟶ X := hU.isoSpec.inv ≫ U.ι
  let g := (Scheme.Modules.restrictFunctor i).map f
  have hsurj : Function.Surjective (fun x =>
      (g.val.app (op (⊤ : (Spec (.of Γ(X, U))).Opens))) x) :=
    (ModuleCat.epi_iff_surjective (moduleSpecΓFunctor.map g)).1 (epi_moduleSpecΓFunctor_map g)
  have hrange : i ''ᵁ (⊤ : (Spec (.of Γ(X, U))).Opens) = U := by
    change (hU.isoSpec.inv ≫ U.ι) ''ᵁ (⊤ : (Spec (.of Γ(X, U))).Opens) = U
    rw [Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
  let e := (eqToIso hrange).symm.op
  have hnat (x : ((Scheme.Modules.restrictFunctor i).obj M).val.obj
      (op (⊤ : (Spec (.of Γ(X, U))).Opens))) :
      N.val.map e.hom (g.val.app (op (⊤ : (Spec (.of Γ(X, U))).Opens)) x) =
        f.val.app (op U) (M.val.map e.hom x) :=
    congrArg (fun k => k x) (f.val.naturality e.hom).symm
  refine (ModuleCat.epi_iff_surjective (f.val.app (op U))).2 fun y => ?_
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.restrictAppIso i N ⊤ ≪≫ N.presheaf.mapIso e).hom).2 y
  obtain ⟨x, hx⟩ := hsurj z
  exact ⟨(Scheme.Modules.restrictAppIso i M ⊤ ≪≫ M.presheaf.mapIso e).hom x,
    (hnat x).symm.trans (congrArg (N.val.map e.hom) hx)⟩

/-- Each transition map of `sectionsTower` on an affine open is an epimorphism. -/
private theorem epi_sectionsTower_map_succ (X : Scheme.{u})
    (K : ℕᵒᵖ ⥤ DerivedCategory.{u + 1} X.Modules) (q : ℤ)
    (hqc : ∀ n : ℕ,
      ((DerivedCategory.homologyFunctor X.Modules q).obj (K.obj ⟨n⟩)).IsQuasicoherent)
    (hsurj : ∀ n : ℕ,
      Epi ((DerivedCategory.homologyFunctor X.Modules q).map
        (K.map (homOfLE (Nat.le_succ n)).op)))
    (U : X.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    Epi ((sectionsTower X K q U).map (homOfLE (Nat.le_succ n)).op) := by
  have := hqc (n + 1)
  have := hqc n
  have : Epi ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map
      ((DerivedCategory.homologyFunctor X.Modules q).map (K.map (homOfLE (Nat.le_succ n)).op))) :=
    epi_app_of_isAffineOpen U hU _ (hsurj n)
  exact Functor.map_epi
    (forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U))) AddCommGrpCat) _

/-- Every transition map of `sectionsTower` on an affine open is an epimorphism. -/
private theorem epi_sectionsTower_map (X : Scheme.{u})
    (K : ℕᵒᵖ ⥤ DerivedCategory.{u + 1} X.Modules) (q : ℤ)
    (hqc : ∀ n : ℕ,
      ((DerivedCategory.homologyFunctor X.Modules q).obj (K.obj ⟨n⟩)).IsQuasicoherent)
    (hsurj : ∀ n : ℕ,
      Epi ((DerivedCategory.homologyFunctor X.Modules q).map
        (K.map (homOfLE (Nat.le_succ n)).op)))
    (U : X.Opens) (hU : IsAffineOpen U) {i j : ℕᵒᵖ} (f : i ⟶ j) :
    Epi ((sectionsTower X K q U).map f) := by
  let A := sectionsTower X K q U
  have htrans (a b : ℕ) (hab : b ≤ a) : Epi (A.map (homOfLE hab).op) := by
    induction a, hab using Nat.le_induction with
    | base => simpa using (show Epi (𝟙 (A.obj (op b))) from inferInstance)
    | @succ a hab ih =>
      rw [show (homOfLE (hab.trans (Nat.le_succ a))).op =
          (homOfLE (Nat.le_succ a)).op ≫ (homOfLE hab).op from Subsingleton.elim _ _,
        Functor.map_comp]
      exact epi_comp' (epi_sectionsTower_map_succ X K q hqc hsurj U hU a) ih
  rw [Subsingleton.elim f (homOfLE f.unop.le).op]
  exact htrans _ _ _

/-- On an affine open, an inverse system in the derived category with quasi-coherent cohomology
and epimorphic transition maps on cohomology has vanishing first derived inverse limit of
sections. -/
public theorem isZero_firstDerivedLimit_sections (X : Scheme.{u})
    (K : ℕᵒᵖ ⥤ DerivedCategory.{u + 1} X.Modules) (q : ℤ)
    (hqc : ∀ n : ℕ,
      ((DerivedCategory.homologyFunctor X.Modules q).obj (K.obj ⟨n⟩)).IsQuasicoherent)
    (hsurj : ∀ n : ℕ,
      Epi ((DerivedCategory.homologyFunctor X.Modules q).map
        (K.map (homOfLE (Nat.le_succ n)).op)))
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsZero (Rlim.firstDerivedLimit (sectionsTower X K q U)) := by
  let A := sectionsTower X K q U
  have hML : (A ⋙ forget Ab.{u}).IsMittagLeffler :=
    Functor.isMittagLeffler_of_surjective _ fun _ _ f =>
      (AddCommGrpCat.epi_iff_surjective _).1 (epi_sectionsTower_map X K q hqc hsurj U hU f)
  obtain ⟨RF, α, hRF, _, _, hMLzero, _, _, _, _, _, hAny, _⟩ :=
    Rlim.lim_hasRightDerivedFunctor_and_computations.{u}
  obtain ⟨e⟩ := hAny RF α hRF A
  exact (hMLzero A hML).of_iso e.symm

end AlgebraicGeometry

end
