module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageLocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentAbelian

/-!
# Locally quasi-coherent modules at a larger module universe (Stacks 06WM (2), (3))

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids.  Stacks 06WM (2), (3) say that the
locally quasi-coherent étale sheaves of `𝒪_𝒳`-modules (Stacks 06WJ) are closed under kernels,
cokernels and extensions in `Mod(𝒳_ét, 𝒪_𝒳)`.  The library proves this in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentAbelian` and
`…LocallyQuasicoherentClosure` with module sections in the universe `u` of the schemes.  The
stacks chapters need it one universe up: the underlying category of an algebraic stack has its
objects in `Type (u + 1)`, so the direct images of modules on algebraic stacks have their sections
in `Type (u + 1)`, which is where the conditions of Stacks 0771 are read.

This file proves the same closure properties at the module universe `max (u + 1) m`, for every
`m`.  The proof is the source's: local quasi-coherence is quasi-coherence of the restrictions
`x^*F|_{U_ét}`, restriction to a small étale site is exact, and quasi-coherent modules on the small
étale site of a scheme have the closure properties at that universe
(`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentLargeSections`).
What has to be redone at the larger universe is the exactness of the restriction: its right
exactness goes through the comparison between sheafifying and restricting
(`Stacks.SheafOfModules.sheafificationRestrictScalarsPushforwardIso`), which is universe-free,
but the library assembles it at module universe `u`.

## Main results

* `AlgebraicGeometry.Stack.preservesFiniteLimits_restrictSheafToSmallEtale_freeModuleUniverse`
  and
  `AlgebraicGeometry.Stack.preservesColimitsOfShape_restrictSheafToSmallEtale_freeModuleUniverse`:
  the restriction to a small étale site is exact at the module universe `max (u + 1) m`.
* `AlgebraicGeometry.Stack.isClosedUnderKernels_isLocallyQuasicoherent_freeModuleUniverse`,
  `AlgebraicGeometry.Stack.isClosedUnderCokernels_isLocallyQuasicoherent_freeModuleUniverse`,
  `AlgebraicGeometry.Stack.isClosedUnderExtensions_isLocallyQuasicoherent_freeModuleUniverse` and
  `AlgebraicGeometry.Stack.containsZero_isLocallyQuasicoherent_freeModuleUniverse`: **Stacks 06WM
  (2), (3)** at that universe, the last three given sheafification on the associated étale site.
* `AlgebraicGeometry.Stack.isWeakSerreClass_isLocallyQuasicoherent_succ`: for a category fibred in
  groupoids with objects in `Type (u + 1)` and morphisms in `Type u`, local quasi-coherence is a
  weak Serre class in `Mod(𝒳_ét, 𝒪_𝒳)` at module universe `u + 1`, with no hypothesis.

## Implementation notes

The fppf reading of these closure properties, inside `Mod(𝒪_𝒳) = Mod(𝒳_fppf, 𝒪_𝒳)`, is not a
consequence of local quasi-coherence alone: an fppf cokernel is the fppf sheafification of the
étale one, which is an fppf sheaf by Stacks 0771 (1) only in the presence of the flat base change
property.  It is therefore left to the flat base change half of Stacks 0771 (2).

No `stacks` attribute is carried: Stacks 06WM is registered at the universe of the schemes.

## References

* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

section Limits

/-- Restriction of presheaves of modules to the small étale site of the scheme below `x`
preserves finite limits at the module universe `max (u + 1) m`. -/
theorem preservesFiniteLimits_restrictModuleToSmallEtaleFunctor_freeModuleUniverse (x : 𝒳)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    PreservesFiniteLimits
      (restrictModuleToSmallEtaleFunctor.{u, v, w, max (u + 1) m} B E h S hS p hp τ hτ x) := by
  refine ⟨fun _ _ _ => ⟨⟨fun hc =>
    ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ fun X => ?_⟩⟩⟩⟩
  have := isEquivalence_overPost B S hS p hp x
  exact isLimitOfPreserves (ModuleCat.restrictScalars _)
    (isLimitOfPreserves (PresheafOfModules.evaluation _ _) hc)

/-- **The restriction of étale sheaves of modules to a small étale site is left exact** at the
module universe `max (u + 1) m`: finite limits are computed on underlying presheaves of modules
on both sides. -/
theorem preservesFiniteLimits_restrictSheafToSmallEtale_freeModuleUniverse (x : 𝒳) :
    PreservesFiniteLimits
      (restrictSheafToSmallEtale.{u, v, w, max (u + 1) m} B E h S hS p hp x) := by
  have := preservesFiniteLimits_restrictModuleToSmallEtaleFunctor_freeModuleUniverse.{u, v, w, m}
    B E h S hS p hp x (etaleTopology B) (etaleTopology_le_topology B)
  have : PreservesFiniteLimits (restrictSheafToSmallEtale.{u, v, w, max (u + 1) m}
      B E h S hS p hp x ⋙ SheafOfModules.forget _) := by
    rw [restrictSheafToSmallEtale_comp_forget]
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.forget _)

end Limits

/-- Abelian presheaves on the small étale site of a scheme have a sheafification at the module
universe `max (u + 1) m`: the site has objects in `Type (u + 1)` and morphisms in `Type u`. -/
theorem hasSheafify_smallEtale_freeModuleUniverse (T : Scheme.{u}) (hT : E.Contains T) :
    HasSheafify (SmallEtale.topology E T hT) AddCommGrpCat.{max (u + 1) m} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{max (u + 1) m, u, u + 1} _

/-- On the small étale site of a scheme, at the module universe `max (u + 1) m`, the morphisms
inverted by sheafification are the locally bijective ones. -/
theorem wEqualsLocallyBijective_smallEtale_freeModuleUniverse (T : Scheme.{u})
    (hT : E.Contains T) :
    (SmallEtale.topology E T hT).WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) m} :=
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max (u + 1) m,
    u + 1, u} _

attribute [local instance 2000] hasSheafify_smallEtale_freeModuleUniverse
  wEqualsLocallyBijective_smallEtale_freeModuleUniverse

/-- Restriction of presheaves of modules to the small étale site of the scheme below `x`
preserves colimits at the module universe `max (u + 1) m`: after evaluation it is a reindexing
followed by a restriction of scalars, which is a left adjoint. -/
theorem preservesColimitsOfShape_restrictModuleToSmallEtaleFunctor_freeModuleUniverse (x : 𝒳)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) (K : Type*) [Category* K]
    [HasColimitsOfShape K AddCommGrpCat.{max (u + 1) m}] :
    PreservesColimitsOfShape K
      (restrictModuleToSmallEtaleFunctor.{u, v, w, max (u + 1) m} B E h S hS p hp τ hτ x) := by
  refine ⟨⟨fun hc => ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ fun X => ?_⟩⟩⟩
  have := isEquivalence_overPost B S hS p hp x
  exact isColimitOfPreserves (ModuleCat.restrictScalars _)
    (isColimitOfPreserves (PresheafOfModules.evaluation _ _) hc)

section Colimits

variable [HasWeakSheafify (associatedTopology B S hS p (etaleTopology B))
    AddCommGrpCat.{max (u + 1) m}]
  [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective
    AddCommGrpCat.{max (u + 1) m}]

/-- Sheafification of presheaves of modules on the associated étale site of `𝒳`, at the module
universe `max (u + 1) m`. -/
noncomputable abbrev etaleSheafificationFreeModuleUniverse :
    PresheafOfModules.{max (u + 1) m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj ⥤
      SheafOfModules.{max (u + 1) m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)) :=
  PresheafOfModules.sheafification.{max (u + 1) m}
    (𝟙 (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)

/-- The sheafification adjunction of the associated étale site of `𝒳`, at the module universe
`max (u + 1) m`. -/
noncomputable abbrev etaleSheafificationAdjunctionFreeModuleUniverse :
    etaleSheafificationFreeModuleUniverse.{u, v, w, m} B S hS p hp ⊣ SheafOfModules.forget _ :=
  PresheafOfModules.sheafificationAdjunction.{max (u + 1) m}
    (𝟙 (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)

section Comparison

variable (x : 𝒳)

/-- Sheafification of presheaves of modules on the small étale site of the scheme below `x`, at
the module universe `max (u + 1) m`. -/
noncomputable abbrev smallEtaleSheafificationFreeModuleUniverse :
    PresheafOfModules.{max (u + 1) m} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x)).obj ⥤
      SheafOfModules.{max (u + 1) m} (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x)) :=
  PresheafOfModules.sheafification.{max (u + 1) m}
    (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj)

/-- The sheafification adjunction of the small étale site of the scheme below `x`, at the module
universe `max (u + 1) m`. -/
noncomputable abbrev smallEtaleSheafificationAdjunctionFreeModuleUniverse :
    smallEtaleSheafificationFreeModuleUniverse.{u, v, w, m} B E h S hS p x ⊣
      SheafOfModules.forget _ :=
  PresheafOfModules.sheafificationAdjunction.{max (u + 1) m}
    (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj)

/-- The unit of the sheafification adjunction of the associated étale site of `𝒳` at the module
universe `max (u + 1) m`, with its target written as the underlying presheaf of the
sheafification. -/
noncomputable def etaleSheafificationUnitFreeModuleUniverse
    (M : PresheafOfModules.{max (u + 1) m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj) :
    M ⟶ ((PresheafOfModules.sheafification.{max (u + 1) m}
      (𝟙 (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)).obj)).obj M).val :=
  (PresheafOfModules.sheafificationAdjunction.{max (u + 1) m}
    (𝟙 (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)).unit.app M

/-- Naturality of `etaleSheafificationUnitFreeModuleUniverse`: for a morphism `f : M ⟶ N` of
presheaves of modules, `f` followed by the unit at `N` equals the unit at `M` followed by the
underlying morphism of presheaves of the sheafification of `f`. -/
theorem etaleSheafificationUnitFreeModuleUniverse_naturality
    {M N : PresheafOfModules.{max (u + 1) m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj} (f : M ⟶ N) :
    f ≫ etaleSheafificationUnitFreeModuleUniverse B S hS p hp N =
      etaleSheafificationUnitFreeModuleUniverse B S hS p hp M ≫
        ((PresheafOfModules.sheafification.{max (u + 1) m}
          (𝟙 (ringStructureSheafCore B S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B)).obj)).map f).val :=
  (PresheafOfModules.sheafificationAdjunction.{max (u + 1) m}
    (𝟙 (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)).unit.naturality f

/-- The component at `M` of `restrictSheafificationComparisonFreeModuleUniverse`: the transpose
of the restriction of the sheafification unit, at the module universe `max (u + 1) m`. -/
noncomputable def restrictSheafificationComparisonAppFreeModuleUniverse
    (M : PresheafOfModules.{max (u + 1) m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj) :
    (PresheafOfModules.sheafification.{max (u + 1) m}
        (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj)).obj
        ((restrictModuleToSmallEtaleFunctor.{u, v, w, max (u + 1) m} B E h S hS p hp
          (etaleTopology B) (etaleTopology_le_topology B) x).obj M) ⟶
      (restrictSheafToSmallEtale.{u, v, w, max (u + 1) m} B E h S hS p hp x).obj
        ((PresheafOfModules.sheafification.{max (u + 1) m}
          (𝟙 (ringStructureSheafCore B S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B)).obj)).obj M) :=
  ((PresheafOfModules.sheafificationAdjunction.{max (u + 1) m}
      (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj)).homEquiv _
      ((restrictSheafToSmallEtale.{u, v, w, max (u + 1) m} B E h S hS p hp x).obj
        ((PresheafOfModules.sheafification.{max (u + 1) m}
          (𝟙 (ringStructureSheafCore B S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B)).obj)).obj M))).symm
    ((restrictModuleToSmallEtaleFunctor.{u, v, w, max (u + 1) m} B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) x).map
        (etaleSheafificationUnitFreeModuleUniverse B S hS p hp M))

/-- The comparison between sheafifying and then restricting to the small étale site of the scheme
below `x`, and restricting and then sheafifying, at the module universe `max (u + 1) m`. -/
noncomputable def restrictSheafificationComparisonFreeModuleUniverse :
    restrictModuleToSmallEtaleFunctor.{u, v, w, max (u + 1) m} B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) x ⋙
      smallEtaleSheafificationFreeModuleUniverse.{u, v, w, m} B E h S hS p x ⟶
      etaleSheafificationFreeModuleUniverse.{u, v, w, m} B S hS p hp ⋙
        restrictSheafToSmallEtale.{u, v, w, max (u + 1) m} B E h S hS p hp x where
  app M := restrictSheafificationComparisonAppFreeModuleUniverse B E h S hS p hp x M
  naturality {M N} f := by
    let G := restrictModuleToSmallEtaleFunctor.{u, v, w, max (u + 1) m} B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) x
    let adjU := smallEtaleSheafificationAdjunctionFreeModuleUniverse.{u, v, w, m} B E h S hS p x
    let R := restrictSheafToSmallEtale.{u, v, w, max (u + 1) m} B E h S hS p hp x
    let L := etaleSheafificationFreeModuleUniverse.{u, v, w, m} B S hS p hp
    let η := etaleSheafificationUnitFreeModuleUniverse.{u, v, w, m} B S hS p hp
    have h₁ := (adjU.homEquiv_naturality_left_symm (Y := R.obj (L.obj N)) (G.map f)
      (G.map (η N))).symm
    have h₂ := (adjU.homEquiv_naturality_right_symm (Y := R.obj (L.obj M))
      (Y' := R.obj (L.obj N)) (G.map (η M)) (R.map (L.map f)))
    have h₃ : G.map f ≫ (G.map (η N) : G.obj N ⟶ (SheafOfModules.forget _).obj (R.obj (L.obj N))) =
        (G.map (η M) : G.obj M ⟶ (SheafOfModules.forget _).obj (R.obj (L.obj M))) ≫
          (SheafOfModules.forget _).map (R.map (L.map f)) :=
      (G.map_comp f (η N)).symm.trans
        ((congrArg G.map (etaleSheafificationUnitFreeModuleUniverse_naturality B S hS p hp f)).trans
          (G.map_comp _ _))
    exact h₁.trans ((congrArg (adjU.homEquiv _ _).symm h₃).trans h₂)

include h in
/-- The component of `restrictSheafificationComparisonFreeModuleUniverse` at a presheaf of modules
is the isomorphism `Stacks.SheafOfModules.sheafificationRestrictScalarsPushforwardIso` of
Stacks 06W1. -/
theorem isIso_restrictSheafificationComparisonAppFreeModuleUniverse
    (M : PresheafOfModules.{max (u + 1) m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj) :
    IsIso (restrictSheafificationComparisonAppFreeModuleUniverse B E h S hS p hp x M) := by
  let hx := isEquivalence_overPost B S hS p hp x
  let K := associatedTopology B S hS p (etaleTopology B)
  let J := SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)
  let q := smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget x
  obtain ⟨hq₁, hq₂⟩ := isContinuous_and_isCocontinuous_restrictToSmallEtale B E h S hS p hp x
  have hqc : q.IsContinuous J K := hq₁
  have hqcc : q.IsCocontinuous J K := hq₂
  let i := Stacks.SheafOfModules.sheafificationRestrictScalarsPushforwardIso J K q
    (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x))
    (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))
    (localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B)).hom M
  have e : restrictSheafificationComparisonAppFreeModuleUniverse B E h S hS p hp x M = i.hom := by
    exact Adjunction.homEquiv_counit _ _ _ _
  rw [e]
  exact Iso.isIso_hom _

/-- The comparison `restrictSheafificationComparisonFreeModuleUniverse` is an isomorphism. -/
theorem isIso_restrictSheafificationComparisonFreeModuleUniverse :
    IsIso (restrictSheafificationComparisonFreeModuleUniverse B E h S hS p hp x) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _
    (restrictSheafificationComparisonFreeModuleUniverse B E h S hS p hp x)
    (isIso_restrictSheafificationComparisonAppFreeModuleUniverse B E h S hS p hp x)

end Comparison

/-- **The restriction of étale sheaves of modules to a small étale site preserves colimits** at
the module universe `max (u + 1) m`, given sheafification on the associated étale site of `𝒳`
there; the small étale site of a scheme has it outright. -/
theorem preservesColimitsOfShape_restrictSheafToSmallEtale_freeModuleUniverse (x : 𝒳)
    (K : Type*) [Category* K] [HasColimitsOfShape K AddCommGrpCat.{max (u + 1) m}] :
    PreservesColimitsOfShape K
      (restrictSheafToSmallEtale.{u, v, w, max (u + 1) m} B E h S hS p hp x) := by
  have := isIso_restrictSheafificationComparisonFreeModuleUniverse B E h S hS p hp x
  have := preservesColimitsOfShape_restrictModuleToSmallEtaleFunctor_freeModuleUniverse.{u, v, w, m}
    B E h S hS p hp x (etaleTopology B) (etaleTopology_le_topology B) K
  have : PreservesColimitsOfShape K
      (etaleSheafificationFreeModuleUniverse.{u, v, w, m} B S hS p hp ⋙
        restrictSheafToSmallEtale.{u, v, w, max (u + 1) m} B E h S hS p hp x) :=
    preservesColimitsOfShape_of_natIso
      (asIso (restrictSheafificationComparisonFreeModuleUniverse B E h S hS p hp x))
  exact (etaleSheafificationAdjunctionFreeModuleUniverse.{u, v, w, m} B S hS p
    hp).preservesColimitsOfShape_of_comp_reflector _ K

/-- **The restriction of étale sheaves of modules to a small étale site is right exact** at the
module universe `max (u + 1) m`. -/
theorem preservesFiniteColimits_restrictSheafToSmallEtale_freeModuleUniverse (x : 𝒳) :
    PreservesFiniteColimits
      (restrictSheafToSmallEtale.{u, v, w, max (u + 1) m} B E h S hS p hp x) :=
  ⟨fun K _ _ => preservesColimitsOfShape_restrictSheafToSmallEtale_freeModuleUniverse
    B E h S hS p hp x K⟩

end Colimits

/-! ### Closure properties of local quasi-coherence at a free module universe -/

/-- The restriction of étale sheaves of modules to a small étale site preserves zero morphisms, at
every module universe: it does not change sections. -/
theorem preservesZeroMorphisms_restrictSheafToSmallEtale (x : 𝒳) :
    (restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x).PreservesZeroMorphisms :=
  ⟨fun _ _ => rfl⟩

/-- Local quasi-coherence (Stacks 06WJ) at the module universe `max (u + 1) m` is invariant under
isomorphism of étale sheaves of modules. -/
theorem isClosedUnderIsomorphisms_isLocallyQuasicoherent_freeModuleUniverse :
    (isLocallyQuasicoherent.{u, v, w, max (u + 1) m} B E h S hS
      p hp).IsClosedUnderIsomorphisms where
  of_iso {F G} e hF := (isLocallyQuasicoherent_iff B E h S hS p hp G).2 fun x =>
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((restrictSheafToSmallEtale B E h S hS p hp x).mapIso e)
      ((isLocallyQuasicoherent_iff B E h S hS p hp F).1 hF x)

/-- **Local quasi-coherence is closed under kernels** at the module universe `max (u + 1) m`: the
restriction to a small étale site is left exact there, and quasi-coherent modules on the small
étale site of a scheme are closed under kernels at that universe. -/
theorem isClosedUnderKernels_isLocallyQuasicoherent_freeModuleUniverse :
    (isLocallyQuasicoherent.{u, v, w, max (u + 1) m} B E h S hS p hp).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hF, hG⟩
    refine (isLocallyQuasicoherent_iff B E h S hS p hp _).2 fun x => ?_
    let r := restrictSheafToSmallEtale.{u, v, w, max (u + 1) m} B E h S hS p hp x
    have := preservesZeroMorphisms_restrictSheafToSmallEtale.{u, v, w, max (u + 1) m}
      B E h S hS p hp x
    have := preservesFiniteLimits_restrictSheafToSmallEtale_freeModuleUniverse.{u, v, w, m}
      B E h S hS p hp x
    have := SmallEtale.isClosedUnderKernels_isQuasicoherentOnSite_freeModuleUniverse.{m} B E h
      (p.obj x).left.1 (contains_base B E h S hS p x)
    exact (SheafOfModules.isQuasicoherentOnSite _).prop_of_isLimit_kernelFork
      ((KernelFork.isLimitMapConeEquiv k r) (isLimitOfPreserves r hk))
      ((isLocallyQuasicoherent_iff B E h S hS p hp _).1 hF x)
      ((isLocallyQuasicoherent_iff B E h S hS p hp _).1 hG x)

section Sheafification

variable [HasSheafify (associatedTopology B S hS p (etaleTopology B))
    AddCommGrpCat.{max (u + 1) m}]
  [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective
    AddCommGrpCat.{max (u + 1) m}]

/-- **Local quasi-coherence is closed under cokernels** at the module universe `max (u + 1) m`,
given sheafification on the associated étale site of `𝒳` there: the restriction to a small étale
site is right exact, and quasi-coherent modules on the small étale site of a scheme are closed
under cokernels at that universe. -/
theorem isClosedUnderCokernels_isLocallyQuasicoherent_freeModuleUniverse :
    (isLocallyQuasicoherent.{u, v, w, max (u + 1) m} B E h S hS p hp).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hF, hG⟩
    refine (isLocallyQuasicoherent_iff B E h S hS p hp _).2 fun x => ?_
    let r := restrictSheafToSmallEtale.{u, v, w, max (u + 1) m} B E h S hS p hp x
    have := preservesZeroMorphisms_restrictSheafToSmallEtale.{u, v, w, max (u + 1) m}
      B E h S hS p hp x
    have := preservesFiniteColimits_restrictSheafToSmallEtale_freeModuleUniverse.{u, v, w, m}
      B E h S hS p hp x
    have := SmallEtale.isClosedUnderCokernels_isQuasicoherentOnSite_freeModuleUniverse.{m} B E h
      (p.obj x).left.1 (contains_base B E h S hS p x)
    exact (SheafOfModules.isQuasicoherentOnSite _).prop_of_isColimit_cokernelCofork
      ((CokernelCofork.isColimitMapCoconeEquiv k r) (isColimitOfPreserves r hk))
      ((isLocallyQuasicoherent_iff B E h S hS p hp _).1 hF x)
      ((isLocallyQuasicoherent_iff B E h S hS p hp _).1 hG x)

/-- **Stacks 06WM (3) at the module universe `max (u + 1) m`, the extension case**: the middle term
of a short exact sequence of étale sheaves of modules on `𝒳` whose outer terms are locally
quasi-coherent is locally quasi-coherent.  The restriction to the small étale site of the scheme
below an object is exact, so it carries the sequence to a short exact sequence there, and an
extension of quasi-coherent modules on the small étale site of a scheme is quasi-coherent. -/
theorem isClosedUnderExtensions_isLocallyQuasicoherent_freeModuleUniverse :
    (isLocallyQuasicoherent.{u, v, w, max (u + 1) m} B E h S hS p hp).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {T} hT h₁ h₃ := by
    let : Abelian (SheafOfModules.{max (u + 1) m} (ringStructureSheafCore B S hS p hp
        (etaleTopology B) (etaleTopology_le_topology B))) :=
      SheafOfModules.instAbelian.{max (u + 1) m, w, u, v} _
    refine (isLocallyQuasicoherent_iff B E h S hS p hp _).2 fun x => ?_
    let : HasSheafify (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
        AddCommGrpCat.{max (u + 1) m} :=
      hasSheafify_smallEtale_freeModuleUniverse.{u, m} E _ _
    let : Abelian (SheafOfModules.{max (u + 1) m} (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x))) :=
      SheafOfModules.instAbelian.{max (u + 1) m, u, u, u + 1} _
    let r := restrictSheafToSmallEtale.{u, v, w, max (u + 1) m} B E h S hS p hp x
    have := preservesZeroMorphisms_restrictSheafToSmallEtale.{u, v, w, max (u + 1) m}
      B E h S hS p hp x
    have := preservesFiniteLimits_restrictSheafToSmallEtale_freeModuleUniverse.{u, v, w, m}
      B E h S hS p hp x
    have := preservesFiniteColimits_restrictSheafToSmallEtale_freeModuleUniverse.{u, v, w, m}
      B E h S hS p hp x
    have := SmallEtale.isClosedUnderExtensions_isQuasicoherentOnSite_freeModuleUniverse.{m} B E h
      (p.obj x).left.1 (contains_base B E h S hS p x)
    exact (SheafOfModules.isQuasicoherentOnSite _).prop_X₂_of_shortExact (hT.map_of_exact r)
      ((isLocallyQuasicoherent_iff B E h S hS p hp _).1 h₁ x)
      ((isLocallyQuasicoherent_iff B E h S hS p hp _).1 h₃ x)

/-- **Local quasi-coherence contains a zero object** at the module universe `max (u + 1) m`: the
restrictions of a zero module are zero, and a zero module on a site is quasi-coherent. -/
theorem containsZero_isLocallyQuasicoherent_freeModuleUniverse :
    (isLocallyQuasicoherent.{u, v, w, max (u + 1) m} B E h S hS p hp).ContainsZero := by
  let : Abelian (SheafOfModules.{max (u + 1) m} (ringStructureSheafCore B S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B))) :=
    SheafOfModules.instAbelian.{max (u + 1) m, w, u, v} _
  obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := SheafOfModules.{max (u + 1) m}
    (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
  refine ⟨Z, hZ, (isLocallyQuasicoherent_iff B E h S hS p hp _).2 fun x => ?_⟩
  have := preservesZeroMorphisms_restrictSheafToSmallEtale.{u, v, w, max (u + 1) m}
    B E h S hS p hp x
  exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
    ((restrictSheafToSmallEtale.{u, v, w, max (u + 1) m} B E h S hS p hp x).map_isZero hZ)

end Sheafification

/-! ### Categories whose objects lie in `Type (u + 1)`, at module universe `u + 1` -/

section Succ

variable {𝒵 : Type (u + 1)} [Category.{u} 𝒵] (r : 𝒵 ⥤ BigFppfOver B S hS)
  (hr : r.IsFiberedInGroupoids)

/-- **Stacks 06WM (2), cokernel clause, at module universe `u + 1`** for a category fibred in
groupoids whose objects lie in `Type (u + 1)` and whose morphisms lie in `Type u` (the
underlying category of an algebraic stack): a cokernel of étale sheaves of modules between
locally quasi-coherent ones is locally quasi-coherent.  Sheafification on the associated étale
site at that universe holds outright, the site being essentially small there. -/
theorem isClosedUnderCokernels_isLocallyQuasicoherent_succ :
    (isLocallyQuasicoherent.{u, u + 1, u, u + 1} B E h S hS r hr).IsClosedUnderCokernels :=
  let _ := hasSheafify_associatedTopology_of_category_succ B S hS r
  let _ := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS r
  isClosedUnderCokernels_isLocallyQuasicoherent_freeModuleUniverse.{u, u + 1, u, u}
    B E h S hS r hr

/-- **Stacks 06WM (3), the extension case, at module universe `u + 1`** for a category fibred in
groupoids whose objects lie in `Type (u + 1)` and whose morphisms lie in `Type u`. -/
theorem isClosedUnderExtensions_isLocallyQuasicoherent_succ :
    (isLocallyQuasicoherent.{u, u + 1, u, u + 1} B E h S hS r hr).IsClosedUnderExtensions :=
  let _ := hasSheafify_associatedTopology_of_category_succ B S hS r
  let _ := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS r
  isClosedUnderExtensions_isLocallyQuasicoherent_freeModuleUniverse.{u, u + 1, u, u}
    B E h S hS r hr

/-- Local quasi-coherence at module universe `u + 1` contains a zero object, for a category fibred
in groupoids whose objects lie in `Type (u + 1)` and whose morphisms lie in `Type u`. -/
theorem containsZero_isLocallyQuasicoherent_succ :
    (isLocallyQuasicoherent.{u, u + 1, u, u + 1} B E h S hS r hr).ContainsZero :=
  let _ := hasSheafify_associatedTopology_of_category_succ B S hS r
  let _ := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS r
  containsZero_isLocallyQuasicoherent_freeModuleUniverse.{u, u + 1, u, u} B E h S hS r hr

/-- The étale sheaves of modules at module universe `u + 1` on a category fibred in groupoids whose
objects lie in `Type (u + 1)` and whose morphisms lie in `Type u` form an abelian category: the
associated étale site is essentially small at that universe, so it has sheafification. -/
@[instance_reducible]
noncomputable def abelian_etaleModuleSheavesSucc :
    Abelian (SheafOfModules.{u + 1} (ringStructureSheafCore B S hS r hr (etaleTopology B)
      (etaleTopology_le_topology B))) :=
  letI := hasSheafify_associatedTopology_of_category_succ B S hS r
  letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS r
  SheafOfModules.instAbelian.{u + 1, u, u, u + 1} _

/-- **Stacks 06WM (2), (3) at module universe `u + 1`: local quasi-coherence is a weak Serre class
in `Mod(𝒳_ét, 𝒪_𝒳)`** (Stacks 0754), for a category fibred in groupoids whose objects lie in
`Type (u + 1)` and whose morphisms lie in `Type u` — the underlying category of an algebraic
stack.  This is the locally quasi-coherent half of Stacks 0771 (2) at the universe where the
direct images of modules on algebraic stacks live. -/
theorem isWeakSerreClass_isLocallyQuasicoherent_succ :
    letI := abelian_etaleModuleSheavesSucc B S hS r hr
    (isLocallyQuasicoherent.{u, u + 1, u, u + 1} B E h S hS r hr).IsWeakSerreClass :=
  let _ := abelian_etaleModuleSheavesSucc B S hS r hr
  let _ := containsZero_isLocallyQuasicoherent_succ B E h S hS r hr
  let _ := isClosedUnderIsomorphisms_isLocallyQuasicoherent_freeModuleUniverse.{u, u + 1, u, u}
    B E h S hS r hr
  let _ := isClosedUnderKernels_isLocallyQuasicoherent_freeModuleUniverse.{u, u + 1, u, u}
    B E h S hS r hr
  let _ := isClosedUnderCokernels_isLocallyQuasicoherent_succ B E h S hS r hr
  let _ := isClosedUnderExtensions_isLocallyQuasicoherent_succ B E h S hS r hr
  { }

end Succ

end AlgebraicGeometry.Stack

end
