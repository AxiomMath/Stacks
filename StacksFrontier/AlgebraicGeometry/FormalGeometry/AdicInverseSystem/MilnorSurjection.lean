module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.LimitTopology
public import
  StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.HgroupAndUnboundedDerivedSections

/-!
# The Milnor surjection for an adic inverse system, in module-valued cohomology

Let `X` be a scheme and `(F_n)` an adic inverse system of quasi-coherent `𝒪_X`-modules with
inverse limit `F = lim F_n`. [Stacks, Tag 0EI8] produces a short exact sequence
`0 → R¹ lim H^{p-1}(X, F_n) → H^p(X, F) → lim_n H^p(X, F_n) → 0`; in particular the comparison
map `H^p(X, F) → lim_n H^p(X, F_n)` is surjective. This file proves that surjectivity for the
model of cohomology in which the limit is a `Γ(X, 𝒪_X)`-module, namely
`Stacks.Algebraization.AdicInverseSystem.moduleCohomologyFunctor`, where the comparison map is
`Stacks.Algebraization.AdicInverseSystem.limitComparison`.

## Main definitions

* `Stacks.Algebraization.AdicInverseSystem.rhoTop` — the identity of `Γ(X, 𝒪_X)`, read as the
  structure map of `Γ(X, 𝒪_X)` as a base ring for derived sections.
* `Stacks.Algebraization.AdicInverseSystem.moduleCohomologyIsoHomologyDerivedSectionsOver` —
  `H^p(X, -)` in `Γ(X, 𝒪_X)`-modules is the degree-`p` cohomology of `RΓ(X, -)` over
  `Γ(X, 𝒪_X)`.

## Main results

* `Stacks.Algebraization.AdicInverseSystem.surjective_limitComparison_moduleCohomologyFunctor` —
  the comparison map `H^p(X, lim F_n) → lim_n H^p(X, F_n)` is surjective.
* `Stacks.Algebraization.AdicInverseSystem.limitComparison_comp_isoOfNatIso` and
  `Stacks.Algebraization.AdicInverseSystem.epi_limitComparison_of_natIso` — the comparison map
  is natural in the functor computing cohomology, so its surjectivity only depends on that
  functor up to isomorphism.

## Implementation notes

The degree runs over `ℕ`: `moduleCohomologyFunctor` is a right derived functor, so the negative
degrees of the source carry no information.

## References

* [Stacks Project, Tag 0EI8](https://stacks.math.columbia.edu/tag/0EI8)
* [Stacks Project, Tag 0BKS](https://stacks.math.columbia.edu/tag/0BKS)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray (sectionsOverOpen)
open Stacks.Cohomology.DerivedSectionsOverBase

namespace Stacks.Algebraization.AdicInverseSystem

attribute [local instance] HasDerivedCategory.standard

/-! ### Cohomology over the ring of global functions -/

/-- The identity of `Γ(X, 𝒪_X)`, as a ring homomorphism from `Γ(X, 𝒪_X)` to the sections of the
structure sheaf of the underlying ringed space over the whole space. -/
public def rhoTop (X : Scheme.{u}) :
    Γ(X, ⊤) →+* (structureSheafRing X.toRingedSpace).obj.obj
      (op (⊤ : Opens X.toRingedSpace.carrier)) :=
  RingHom.id _

/-- **`H^p(X, -)` in `Γ(X, 𝒪_X)`-modules is the cohomology of unbounded derived sections over
`Γ(X, 𝒪_X)`.** The right derived functor of global sections taken in `Γ(X, 𝒪_X)`-modules is the
degree-`p` cohomology of `RΓ(X, -) : D(𝒪_X) ⥤ D(Γ(X, 𝒪_X))` applied to a module placed in degree
zero, naturally in the module. -/
public def moduleCohomologyIsoHomologyDerivedSectionsOver (X : Scheme.{u}) (p : ℕ) :
    DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0 ⋙
        derivedSectionsOver X.toRingedSpace (rhoTop X) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) (p : ℤ) ≅
      moduleCohomologyFunctor X p :=
  letI : (ModuleCat.restrictScalars.{u} (rhoTop X)).PreservesHomology :=
    Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars _
  Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
      (sectionsOver X.toRingedSpace (rhoTop X))
      (derivedSectionsOver X.toRingedSpace (rhoTop X))
      (derivedSectionsOverUnit X.toRingedSpace (rhoTop X))
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective _) p ≪≫
    (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
      (sectionsOverOpen X.toRingedSpace ⊤) (ModuleCat.restrictScalars.{u} (rhoTop X))
      (sectionsOver X.toRingedSpace (rhoTop X)) (Iso.refl _) p).symm ≪≫
    Functor.isoWhiskerLeft ((sectionsOverOpen X.toRingedSpace ⊤).rightDerived p)
      (ModuleCat.restrictScalarsId'.{u} (rhoTop X) rfl) ≪≫
    Functor.rightUnitor _

/-! ### Products and the comparison morphism -/

section PiComparison

variable {C D : Type*} [Category C] [Category D]

/-- The comparison `H(∏ Xₙ) ⟶ ∏ H(Xₙ)` carries the image of a `Pi.lift` to the `Pi.lift` of the
images. -/
private theorem piComparison_map_piLift (H : C ⥤ D) (X : ℕ → C) [HasProduct X]
    [HasProduct fun n => H.obj (X n)] {Y : C} (w : ∀ n, Y ⟶ X n) :
    H.map (Pi.lift w) ≫ piComparison H X = Pi.lift fun n => H.map (w n) := by
  refine Pi.hom_ext _ _ fun n => ?_
  rw [Category.assoc, piComparison_comp_π, ← H.map_comp, Pi.lift_π, Pi.lift_π]

/-- The comparison `H(∏ Xₙ) ⟶ ∏ H(Xₙ)` conjugates the difference map `1 - shift` of an inverse
system into the difference map of the system of images. -/
private theorem piComparison_conj_piLiftSub [Preadditive C] [Preadditive D] (H : C ⥤ D)
    [H.Additive] (X : ℕ → C) [HasProduct X] [HasProduct fun n => H.obj (X n)]
    (τ : ∀ n, X (n + 1) ⟶ X n) :
    H.map (Pi.lift fun n => Pi.π X n - Pi.π X (n + 1) ≫ τ n) ≫ piComparison H X =
      piComparison H X ≫ Pi.lift fun n => Pi.π (fun n => H.obj (X n)) n -
        Pi.π (fun n => H.obj (X n)) (n + 1) ≫ H.map (τ n) := by
  rw [piComparison_map_piLift]
  refine Pi.hom_ext _ _ fun n => ?_
  rw [Pi.lift_π, Category.assoc, Pi.lift_π, Preadditive.comp_sub, piComparison_comp_π,
    H.map_sub, H.map_comp, ← Category.assoc, piComparison_comp_π]

/-- If the `n`-th component of `pm : Z ⟶ ∏ Xₙ` is `g`, then the `n`-th component of
`RG.map pm ≫ piComparison RG X` is `RG.map g`. -/
private theorem map_comp_piComparison_comp_π (RG : C ⥤ D) (X : ℕ → C) [HasProduct X]
    [HasProduct fun n => RG.obj (X n)] {Z : C} (pm : Z ⟶ ∏ᶜ X) (n : ℕ) {g : Z ⟶ X n}
    (hg : pm ≫ Pi.π X n = g) :
    (RG.map pm ≫ piComparison RG X) ≫ Pi.π (fun n => RG.obj (X n)) n = RG.map g := by
  rw [Category.assoc, piComparison_comp_π, ← RG.map_comp, hg]

end PiComparison

/-! ### The projection of the Milnor sequence is an epimorphism -/

/-- **The projection of the Milnor sequence of a derived limit is an epimorphism.** Let
`K ⟶ ∏ Kₙ ⟶ ∏ Kₙ ⟶ K⟦1⟧` be the defining distinguished triangle of a derived limit in `D(R)`,
with structural morphism `a`. Any morphism from `Hʳ(K)` to `lim_n Hʳ(Kₙ)` whose composites with
the limit projections are the maps induced by `a` is an epimorphism.

This is the surjection of [Stacks, Tag 07KY]. -/
private theorem epi_of_homologyLimitLegs {R : Type u} [CommRing R]
    (F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} R)) [HasProduct fun n : ℕ => F.obj ⟨n⟩]
    (K : DerivedCategory (ModuleCat.{u} R))
    (a : K ⟶ ∏ᶜ fun n : ℕ => F.obj ⟨n⟩)
    (b : (∏ᶜ fun n : ℕ => F.obj ⟨n⟩) ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a (Pi.lift fun n : ℕ =>
        Pi.π (fun n : ℕ => F.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ => F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) b ∈
      distTriang (DerivedCategory (ModuleCat.{u} R)))
    (r : ℤ)
    (c : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) r).obj K ⟶
      limit (F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R) r))
    (hc : ∀ n : ℕ,
      c ≫ limit.π (F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R) r) ⟨n⟩ =
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) r).map
          (a ≫ Pi.π (fun n : ℕ => F.obj ⟨n⟩) n)) :
    Epi c := by
  let X : ℕ → DerivedCategory (ModuleCat.{u} R) := fun n => F.obj ⟨n⟩
  let d : (∏ᶜ X) ⟶ ∏ᶜ X := Pi.lift fun n : ℕ =>
    Pi.π X n - Pi.π X (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
  let T := Triangle.mk a d b
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) r
  let δ₀ := Pi.lift fun n : ℕ =>
    Pi.π (fun n => H.obj (X n)) n - Pi.π (fun n => H.obj (X n)) (n + 1) ≫
      H.map (F.map (homOfLE (Nat.le_succ n)).op)
  have := Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    (A := ModuleCat.{u} R) (I := ℕ)
  have := Stacks.DerivedProducts.isIso_piComparison_homologyFunctor X r
  let e₀ := asIso (piComparison H X)
  have hd₀ : H.map d ≫ e₀.hom = e₀.hom ≫ δ₀ := piComparison_conj_piLiftSub H X _
  have had : a ≫ d = 0 := comp_distTriang_mor_zero₁₂ T hT
  have ha : (H.map a ≫ e₀.hom) ≫ δ₀ = 0 := by
    rw [Category.assoc, ← hd₀, ← Category.assoc, ← H.map_comp, had, H.map_zero, zero_comp]
  let q₀ := kernel.lift δ₀ (H.map a ≫ e₀.hom) ha
  let eLim : limit (F ⋙ H) ≅ kernel δ₀ :=
    (inverseSystemLimitKernelForkIsLimit (F ⋙ H)).conePointUniqueUpToIso (limit.isLimit _)
  have hcurr : (ShortComplex.mk (H.map a ≫ e₀.hom) δ₀ ha).Exact := by
    apply ShortComplex.exact_of_iso _ (DerivedCategory.HomologySequence.exact₂ T hT r)
    exact ShortComplex.isoMk (Iso.refl _) e₀ e₀ (by simp [T, H])
      (by simpa [T, H] using hd₀.symm)
  have hq₀ : Epi q₀ := hcurr.epi_kernelLift
  have heLim : eLim.hom ≫ kernel.ι δ₀ = Pi.lift (fun n : ℕ => limit.π (F ⋙ H) ⟨n⟩) :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  have hcq : c = q₀ ≫ eLim.inv := by
    refine limit.hom_ext fun n => ?_
    have h2 : (q₀ ≫ eLim.inv) ≫ limit.π (F ⋙ H) n =
        H.map a ≫ H.map (Pi.π X n.unop) := by
      have hk : eLim.inv ≫ Pi.lift (fun n : ℕ => limit.π (F ⋙ H) ⟨n⟩) = kernel.ι δ₀ := by
        rw [← heLim, Iso.inv_hom_id_assoc]
      have h3 : (q₀ ≫ eLim.inv) ≫ Pi.lift (fun n : ℕ => limit.π (F ⋙ H) ⟨n⟩) =
          H.map a ≫ e₀.hom := by
        rw [Category.assoc, hk]
        exact kernel.lift_ι _ _ _
      have h4 := congrArg (fun f => f ≫ Pi.π (fun n => H.obj (X n)) n.unop) h3
      simpa [e₀, X, Functor.comp_obj] using h4
    rw [hc n.unop, Functor.map_comp]
    exact h2.symm
  rw [hcq]
  exact epi_comp _ _

/-! ### The comparison transported along an isomorphism of cohomology functors -/

/-- The comparison map `H(lim Fₙ) ⟶ lim_n H(Fₙ)` is natural in the functor `H` computing
cohomology. -/
public theorem limitComparison_comp_isoOfNatIso {R : Type u} [CommRing R]
    (S : AdicInverseSystem.{u}) {H H' : S.X.Modules ⥤ ModuleCat.{u} R} (Φ : H ≅ H') :
    limitComparison S H ≫
        (HasLimit.isoOfNatIso (Functor.isoWhiskerLeft S.system Φ)).hom =
      (Φ.app S.limitModule).hom ≫ limitComparison S H' := by
  refine limit.hom_ext fun n => ?_
  simp only [Category.assoc]
  rw [HasLimit.isoOfNatIso_hom_π, ← Category.assoc, limitComparison_comp_π,
    limitComparison_comp_π]
  exact Φ.hom.naturality _

/-- Whether the comparison map `H(lim Fₙ) ⟶ lim_n H(Fₙ)` is an epimorphism only depends on the
functor `H` computing cohomology up to isomorphism. -/
public theorem epi_limitComparison_of_natIso {R : Type u} [CommRing R]
    (S : AdicInverseSystem.{u}) {H H' : S.X.Modules ⥤ ModuleCat.{u} R} (Φ : H ≅ H')
    (h : Epi (limitComparison S H)) : Epi (limitComparison S H') := by
  have h1 : Epi (limitComparison S H ≫
      (HasLimit.isoOfNatIso (Functor.isoWhiskerLeft S.system Φ)).hom) := inferInstance
  rw [limitComparison_comp_isoOfNatIso S Φ] at h1
  exact epi_of_epi (Φ.app S.limitModule).hom _

/-! ### The Milnor surjection -/

/-- **The Milnor surjection of an adic inverse system, in module-valued cohomology.** For an
adic inverse system `(Fₙ)` of quasi-coherent modules on a scheme `X`, with inverse limit
`F = lim Fₙ`, the canonical comparison map

`H^p(X, F) ⟶ lim_n H^p(X, Fₙ)`

is surjective. Here `H^p(X, -)` is `moduleCohomologyFunctor X p`, the `p`-th right derived
functor of global sections taken in `Γ(X, 𝒪_X)`-modules, and the comparison map is
`limitComparison`. -/
@[stacks 0EI8 "surjectivity of the comparison onto the limit, module-valued cohomology"]
public theorem surjective_limitComparison_moduleCohomologyFunctor (S : AdicInverseSystem.{u})
    (p : ℕ) :
    Function.Surjective (limitComparison S (moduleCohomologyFunctor S.X p)).hom := by
  obtain ⟨hprod, pmap, hpleg, δ, hT⟩ :=
    Stacks.Cohomology.SpaceInverseLimits.exists_distTriang_single_limit_of_isBasis
      S.X.toRingedSpace S.system S.X.affineOpens S.X.isBasis_affineOpens
      (fun V hV n q hq => by
        have : (S.system.obj ⟨n⟩).IsQuasicoherent := S.isQuasicoherent ⟨n⟩
        exact Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen S.X
          (S.system.obj ⟨n⟩) V hV q hq)
      (fun V hV =>
        Stacks.Cohomology.SpaceInverseLimits.epi_inverseLimitDifference_of_surjective _
          (fun n => S.surjective_transition_app ⟨V, hV⟩ n))
  have := hprod
  have := SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing S.X.toRingedSpace)
  obtain ⟨hprod2, δ2, hT2⟩ := Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor
    (sectionsOver S.X.toRingedSpace (rhoTop S.X))
    (derivedSectionsOver S.X.toRingedSpace (rhoTop S.X))
    (derivedSectionsOverUnit S.X.toRingedSpace (rhoTop S.X))
    (S.system ⋙ DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing S.X.toRingedSpace)) 0)
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing S.X.toRingedSpace)) 0).obj S.limitModule)
    pmap ⟨δ, hT⟩
  have := hprod2
  have hepi : Epi (limitComparison S
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing S.X.toRingedSpace)) 0 ⋙
        derivedSectionsOver S.X.toRingedSpace (rhoTop S.X) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(S.X, ⊤)) (p : ℤ))) := by
    refine @epi_of_homologyLimitLegs _ _
      ((S.system ⋙ DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing S.X.toRingedSpace)) 0) ⋙
        derivedSectionsOver S.X.toRingedSpace (rhoTop S.X)) hprod2
      ((derivedSectionsOver S.X.toRingedSpace (rhoTop S.X)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing S.X.toRingedSpace)) 0).obj S.limitModule))
      _ δ2 hT2 (p : ℤ) _ fun n => ?_
    exact (limitComparison_comp_π S _ ⟨n⟩).trans
      (congrArg (DerivedCategory.homologyFunctor
        (ModuleCat.{u} Γ(S.X, ⊤)) (p : ℤ)).map
        (map_comp_piComparison_comp_π _ _ pmap n (hpleg n))).symm
  have := epi_limitComparison_of_natIso S
    (moduleCohomologyIsoHomologyDerivedSectionsOver S.X p) hepi
  rw [← LinearMap.range_eq_top]
  exact ModuleCat.range_eq_top_of_epi _

end Stacks.Algebraization.AdicInverseSystem

end

end
