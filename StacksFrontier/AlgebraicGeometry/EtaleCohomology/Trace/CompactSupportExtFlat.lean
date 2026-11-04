module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleFlatTensorExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroStalkTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkFlatTensorExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChangeFiber

/-!
# Tensoring with `(j_! K)|_{X̄_k̄}` is exact when `K` has flat stalks

Let `j : U ⟶ X` be an open immersion, `g : Y ⟶ X` a morphism of schemes and `K` a sheaf of
`Λ`-modules on `U_étale` whose stalks at geometric points are flat. The stalk of the inverse image
`g⁻¹ j_! K` at a geometric point `s` of `Y` is the stalk of `j_! K` at `g ∘ s`, which is the stalk
of `K` at the lift of `g ∘ s` to `U` when there is one and zero otherwise. These stalks are
therefore flat, so `- ⊗ g⁻¹ j_! K` is exact on Mathlib's small étale site of `Y`
(`Stacks.EtaleCohomology.preservesFiniteLimits_tensorRight_etaleModules_of_flat`).

Applied with `g` the projection `X̄_k̄ ⟶ X̄` of the geometric fibre of a compactification and
`K` a level of the `ℓ`-adic sheaf `ℱ_ρ` of a continuous representation, read on Mathlib's site,
this gives the exactness of `- ⊗ (j_! K)|_{X̄_k̄}`.

## Main results

All in the namespace `Stacks.EtaleCohomology`.

* `flat_sheafFiber_ulift_inverseImage`: flatness of the stalks of an inverse image, at the
  universe-lifted points.
* `flat_sheafFiber_extensionByZero`: flatness of the stalks of an extension by zero along an open
  immersion.
* `preservesFiniteLimits_tensorRight_inverseImage_extensionByZero`: `- ⊗ g⁻¹ j_! K` is exact.
* `flat_sheafFiber_sheafEquiv_representationLevelSheaf`: the levels of `ℱ_ρ`, read on Mathlib's
  small étale site, have flat stalks.
* `preservesFiniteLimits_tensorRight_compactification_representationLevelSheaf`:
  `- ⊗ (j_! ℱ_{ρ,k})|_{X̄_k̄}` is exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section General

attribute [local instance] moduleCat_hasLimitsOfSize Sheaf.monoidalCategory

variable (Λ : Type) [CommRing Λ]

/-- **Stalks of an inverse image at the lifted points.** For `g : Y ⟶ X` and a geometric point
`s` of `Y`, the stalk of `g⁻¹ G` at the universe lift of the point at `s` is flat as soon as the
stalk of `G` at `g ∘ s` is. -/
theorem flat_sheafFiber_ulift_inverseImage {X Y : Scheme.{u}} (g : Y ⟶ X) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) (G : EtaleModules.{u, 0} Λ X)
    (hG : Module.Flat Λ ((Scheme.pointSmallEtale (s ≫ g)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj G)) :
    Module.Flat Λ (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj ((etaleModuleInverseImage.{u, 0} Λ g).obj G)) :=
  Module.Flat.of_linearEquiv
    (((Scheme.pointSmallEtale s).sheafFiberUliftNatIso (ModuleCat.{u + 1} Λ)).app _ ≪≫
      (etaleModuleStalkPullbackIso.{u, 0} Λ g s).app G).toLinearEquiv

/-- **Stalks of an extension by zero are flat.** Let `j : U ⟶ X` be an open immersion and `K` a
sheaf of `Λ`-modules on `U_étale`. The stalk of `j_! K` at a geometric point `x` of `X` is flat
provided the stalk of `K` at every lift of `x` to `U` is: it is that stalk if `x` lies in `U`
and zero otherwise. -/
theorem flat_sheafFiber_extensionByZero {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) (K : EtaleModules.{u, 0} Λ U)
    (hK : ∀ t : Spec (.of Ω) ⟶ U, t ≫ j = x →
      Module.Flat Λ ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj K)) :
    Module.Flat Λ ((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j).obj K)) := by
  have hx : Set.range x = {x default} := Set.range_unique
  by_cases h : x default ∈ Set.range j
  · have hr : Set.range x ⊆ Set.range j := hx ▸ Set.singleton_subset_iff.2 h
    obtain ⟨t, rfl⟩ : ∃ t, t ≫ j = x := ⟨_, IsOpenImmersion.lift_fac j x hr⟩
    have : Module.Flat Λ ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
        ((𝟭 (EtaleModules.{u, 0} Λ U)).obj K)) := hK t rfl
    exact Module.Flat.of_linearEquiv
      (((etaleModuleStalkPullbackIso.{u, 0} Λ j t).app _).symm ≪≫
        (Scheme.pointSmallEtale t).sheafFiber.mapIso
          ((extensionByZeroInverseImageIso.{u, 0} Λ j).app K)).toLinearEquiv
  · have hd : Disjoint (Set.range x) (Set.range j) := by
      rwa [hx, Set.disjoint_singleton_left]
    have hz := Functor.map_isZero ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber
      (A := ModuleCat.{u + 1} Λ)) (isZero_etaleModuleInverseImage_extensionByZero_of_disjoint.{u, 0}
        Λ x j hd K)
    have e := (etaleModuleStalkPullbackIso.{u, 0} Λ x (𝟙 _)).app
      ((etaleModuleExtensionByZero.{u, 0} Λ j).obj K)
    rw [Category.id_comp] at e
    have := ModuleCat.subsingleton_of_isZero (hz.of_iso e.symm)
    infer_instance

/-- **Tensoring with `g⁻¹ j_! K` is exact.** Let `j : U ⟶ X` be an open immersion, `g : Y ⟶ X`
a morphism of schemes and `K` a sheaf of `Λ`-modules on `U_étale` whose stalks at all geometric
points with algebraically closed residue field are flat. Then `- ⊗ g⁻¹ j_! K` is additive, left
exact and right exact on sheaves of `Λ`-modules on `Y_étale`. -/
theorem preservesFiniteLimits_tensorRight_inverseImage_extensionByZero {U X Y : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (g : Y ⟶ X)
    [(Y.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal]
    (K : EtaleModules.{u, 0} Λ U)
    (hK : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ U),
      Module.Flat Λ ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj K)) :
    (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ g).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j).obj K))).Additive ∧
      PreservesFiniteLimits (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ g).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j).obj K))) ∧
      PreservesFiniteColimits (MonoidalCategory.tensorRight
        ((etaleModuleInverseImage.{u, 0} Λ g).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j).obj K))) := by
  refine preservesFiniteLimits_tensorRight_etaleModules_of_flat Λ Y
    (Ω := fun y : Y ↦ (GeometricPoint.ofPoint Y y).residueField)
    (fun y ↦ (GeometricPoint.ofPoint Y y).hom) ?_ _ fun y ↦
      flat_sheafFiber_ulift_inverseImage Λ g _ _ <|
        flat_sheafFiber_extensionByZero Λ j _ K fun t _ ↦ hK _ t
  exact Set.eq_univ_of_forall fun y ↦
    Set.mem_iUnion.2 ⟨y, default, GeometricPoint.ofPoint_liesOver Y y⟩

end General

section Representation

attribute [local instance] moduleCat_hasLimitsOfSize Sheaf.monoidalCategory

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ) (k : ℕ)

/-- **The levels of `ℱ_ρ` on Mathlib's small étale site have flat stalks.** The `k`-th level
`ℱ_{ρ,k}` of the `ℓ`-adic sheaf of a continuous representation `ρ`, transported to Mathlib's small
étale site along `AlgebraicGeometry.SmallEtale.sheafEquiv`, has free, hence flat, stalks over
`ℤ/ℓ^kℤ` at every geometric point with algebraically closed residue field: the two stalk functors
agree (`AlgebraicGeometry.sheafFiberIsoOfAdjOfFiberIso`) and the stalk on the site of Stacks 021B
is `(ℤ/ℓ^kℤ)^r` (`Stacks.EtaleCohomology.flat_sheafFiber_representationLevelSheaf`). -/
theorem flat_sheafFiber_sheafEquiv_representationLevelSheaf {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.1) :
    Module.Flat (ZMod (ℓ ^ k)) ((Scheme.pointSmallEtale t).sheafFiber
      (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k))) |>.obj
        ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).functor.obj
          (representationLevelSheaf B X x
            (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k))) := by
  let s : GeometricPoint X.1 := ⟨Ω, t⟩
  have := flat_sheafFiber_representationLevelSheaf B X x ρ hρ k s
  exact Module.Flat.of_linearEquiv ((sheafFiberIsoOfAdjOfFiberIso
    (geometricPointSitePoint B X.1 X.2 s) (Scheme.pointSmallEtale s.hom)
    (SmallEtale.toEtaleSite B X.1 X.2) (toEtaleSiteFiberIso B X.1 X.2 s)
    (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).toAdjunction).app
      _).toLinearEquiv

/-- **Tensoring with `(j_! ℱ_{ρ,k})|_{X̄_k̄}` is exact.** For `X` over a field `k` with a
compactification `j : X ⟶ X̄` over `k` and an extension field `k̄` of `k`, the tensor product
with the inverse image on `X̄_k̄` of the extension by zero of the `k`-th level of `ℱ_ρ` (read on
Mathlib's small étale site) is additive, left exact and right exact on sheaves of
`ℤ/ℓ^kℤ`-modules on `X̄_k̄`. -/
theorem preservesFiniteLimits_tensorRight_compactification_representationLevelSheaf
    {K : Type u} [Field K] (f : X.1 ⟶ Spec (.of K)) (j : CompactificationOf (Over.mk f))
    (kbar : Type u) [Field kbar] [Algebra K kbar] :
    haveI := isMonoidal_W_etaleModules (ZMod (ℓ ^ k)) (fieldBaseChange (Over.mk j.toBase) kbar)
    (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ k))
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ k)) j.immersion).obj
          ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).functor.obj
            (representationLevelSheaf B X x
              (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k))))).Additive ∧
      PreservesFiniteLimits (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0}
        (ZMod (ℓ ^ k)) (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ k)) j.immersion).obj
          ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).functor.obj
            (representationLevelSheaf B X x
              (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k))))) ∧
      PreservesFiniteColimits (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0}
        (ZMod (ℓ ^ k)) (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ k)) j.immersion).obj
          ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).functor.obj
            (representationLevelSheaf B X x
              (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k))))) :=
  have := isMonoidal_W_etaleModules (ZMod (ℓ ^ k)) (fieldBaseChange (Over.mk j.toBase) kbar)
  preservesFiniteLimits_tensorRight_inverseImage_extensionByZero (ZMod (ℓ ^ k)) j.immersion
    (fieldBaseChangeProj (Over.mk j.toBase) kbar) _
    fun _ _ _ t ↦ flat_sheafFiber_sheafEquiv_representationLevelSheaf B X x ρ hρ k t

end Representation

end Stacks.EtaleCohomology

end
