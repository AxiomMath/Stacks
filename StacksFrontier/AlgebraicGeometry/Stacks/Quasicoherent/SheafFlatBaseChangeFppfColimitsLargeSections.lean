module

public import StacksFrontier.AlgebraicGeometry.ProEtale.CompactGeneration
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentEtaleLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentIsLocallyQuasicoherentLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFppfWeakSerreLargeSections
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.SequentialColimitsOfCoproducts
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleSections

/-!
# Stacks 0771 (5) for the fppf modules at module universe `u + 1`

Let `𝒳` be a category fibred in groupoids over `(Sch/S)_{fppf}` whose objects lie in
`Type (u + 1)` and whose morphisms lie in `Type u`, the seating of an algebraic stack. This file
proves that the faithful class `LQCoh^fbc(𝒪_𝒳)` — locally quasi-coherent (Stacks 06WJ) with the
flat base change property of Stacks 0762 read with the pullback of sheaves — is **closed under
direct sums and under colimits of sequences in the sheaves of modules on the fppf site at module
universe `u + 1`**: the corresponding case of Stacks 0771 (5).

## Implementation notes

At a module universe above the universe of the schemes an étale sheaf of modules which is
cartesian on flat arrows between objects over affine schemes
(`AlgebraicGeometry.Stack.IsCartesianOnFlatAffineArrows`) lies in `LQCoh^fbc(𝒪_𝒳)`: its
restrictions to the small étale sites are cartesian between affine objects, hence quasi-coherent
(`SmallEtale.isQuasicoherentOnSite_of_bijective_restrictionBaseChange_freeModuleUniverse`, in the
namespace `AlgebraicGeometry`), and cartesianness is the flat base change property
(`AlgebraicGeometry.Stack.hasSheafFlatBaseChangePropertyUnivLE_iff_isCartesianOnFlatAffineArrows`).

*Direct sums.* An object over an affine scheme is quasi-compact in the fppf site, so the sections
of a direct sum over it are the direct sum of the sections (Stacks 0935). The base change maps
`𝒪(x) ⊗_{𝒪(y)} F(y) ⟶ F(x)` along a flat arrow between such objects are natural in `F` and
`𝒪(x) ⊗_{𝒪(y)} -` commutes with direct sums, so the base change map of a direct sum is the direct
sum of the base change maps.

*Sequences.* The colimit of `F₀ ⟶ F₁ ⟶ ⋯` is the cokernel of `1 - shift` on `⨁ₙ Fₙ`, and the
class is a weak Serre subcategory (Stacks 0771 (2), in the namespace `AlgebraicGeometry.Stack`:
`isWeakSerreClass_isLocallyQuasicoherentWithSheafFlatBaseChange_fppf_succ`).

## Main results

* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_isColimit_evaluation`: the base change
  map of the point of a cocone whose evaluations at both ends are colimits is invertible when
  those of the diagram are.

In the namespace `AlgebraicGeometry.Stack`:

* `isLocallyQuasicoherent_of_isCartesianOnFlatAffineArrows_freeModuleUniverse` and
  `isLocallyQuasicoherentWithSheafFlatBaseChange_of_isCartesianOnFlatAffineArrows`: an étale sheaf
  of modules cartesian on flat arrows between objects over affine schemes is locally
  quasi-coherent, and lies in `LQCoh^fbc(𝒪_𝒳)`.
* `isClosedUnderColimitsOfShape_discrete_isLocallyQuasicoherentWithSheafFlatBaseChange_fppf_succ`
  and `isClosedUnderColimitsOfShape_nat_isLocallyQuasicoherentWithSheafFlatBaseChange_fppf_succ`:
  `LQCoh^fbc(𝒪_𝒳)` is closed under direct sums and under colimits of sequences.
* `isClosedUnderColimitsOfShape_nat_locallyQuasicoherentSheafFlatBaseChangeFppfModulesSucc`: the
  closure under colimits of sequences for an algebraic stack.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w m t w'

namespace Stacks.PresheafOfModules

/-- **The base change map of the point of a cocone of presheaves of modules is invertible when
those of the diagram are**, as soon as the cocone evaluates to a colimit at both ends of the
arrow. The cocone need not be a colimit of presheaves. -/
theorem isIso_restrictionBaseChange_of_isColimit_evaluation
    {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{w}}
    {D : Type t} [Category.{w'} D]
    {K : D ⥤ PresheafOfModules.{max m w} (R ⋙ forget₂ CommRingCat RingCat)} (c : Cocone K)
    {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (hX : IsColimit ((PresheafOfModules.evaluation _ X).mapCocone c))
    (hY : IsColimit ((PresheafOfModules.evaluation _ Y).mapCocone c))
    (h : ∀ i, IsIso (restrictionBaseChange (K.obj i) f)) :
    IsIso (restrictionBaseChange c.pt f) := by
  let a := restrictionBaseChangeNatTrans.{u, v, w, m} R f
  have : ∀ i, IsIso ((Functor.whiskerLeft K a).app i) := h
  have : IsIso (Functor.whiskerLeft K a) := NatIso.isIso_of_isIso_app _
  have : PreservesColimitsOfSize.{w', t}
      (ModuleCat.extendScalars.{w, w, max m w} (R := R.obj X) (S := R.obj Y) (R.map f).hom) :=
    (ModuleCat.extendRestrictScalarsAdj (R.map f).hom).leftAdjoint_preservesColimits
  have hT : IsColimit ((PresheafOfModules.evaluation (R ⋙ forget₂ CommRingCat RingCat) X ⋙
      ModuleCat.extendScalars (R := R.obj X) (S := R.obj Y) (R.map f).hom).mapCocone c) :=
    isColimitOfPreserves (ModuleCat.extendScalars (R.map f).hom) hX
  let e := IsColimit.coconePointsIsoOfNatIso hT hY (asIso (Functor.whiskerLeft K a))
  have he : e.hom = a.app c.pt := hT.hom_ext fun k => by
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    exact (a.naturality (c.ι.app k)).symm
  change IsIso (a.app c.pt)
  rw [← he]
  infer_instance

end Stacks.PresheafOfModules

namespace AlgebraicGeometry.Stack

open Stacks.PresheafOfModules

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

section Cartesian

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- **An étale sheaf of modules cartesian on flat arrows between objects over affine schemes is
locally quasi-coherent** (Stacks 06WJ), at module universe `max (u + 1) v w m`: the index functor
sends a morphism of affine objects of a small étale site to an arrow of `𝒳` over an étale, hence
flat, morphism of affine schemes, so each restriction to a small étale site is cartesian between
affine objects, hence quasi-coherent (Descent, Proposition 03DX (2)). -/
theorem isLocallyQuasicoherent_of_isCartesianOnFlatAffineArrows_freeModuleUniverse
    (G : PresheafOfModules.{max (u + 1) v w m}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hG : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) G.presheaf)
    (hc : IsCartesianOnFlatAffineArrows.{u, v, w, m} B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) G) :
    IsLocallyQuasicoherent B E h S hS p hp G := by
  refine ⟨hG, fun x => ⟨restrictModuleToSmallEtale_isSheaf B E h S hS p hp x G hG, ?_⟩⟩
  refine SmallEtale.isQuasicoherentOnSite_of_bijective_restrictionBaseChange_freeModuleUniverse.{
    max v w m} B E h _ _ _ fun {T T'} g hT hT' => ?_
  refine (bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff_freeModuleUniverse.{u, v,
    w, m} B E h S hS p hp G x g).2 ?_
  have := etale_etaleIndex_map B E h S hS p hp x g
  have hf : Flat ((BigFppfOver.toScheme B S hS).map
      (p.map ((etaleIndex B E h S hS p hp x).map g))) := inferInstance
  exact hc _ hf (isAffine_etaleIndex_obj B E h S hS p hp x T hT)
    (isAffine_etaleIndex_obj B E h S hS p hp x T' hT')

/-- **An étale sheaf of modules cartesian on flat arrows between objects over affine schemes lies
in `LQCoh^fbc(𝒪_𝒳)`**, at module universe `max (u + 1) v w m`. -/
theorem isLocallyQuasicoherentWithSheafFlatBaseChange_of_isCartesianOnFlatAffineArrows
    (G : PresheafOfModules.{max (u + 1) v w m}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hG : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) G.presheaf)
    (hc : IsCartesianOnFlatAffineArrows.{u, v, w, m} B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) G) :
    IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, max (u + 1) v w m}
      B E h S hS p hp G :=
  have hL := isLocallyQuasicoherent_of_isCartesianOnFlatAffineArrows_freeModuleUniverse
    B E h S hS p hp G hG hc
  ⟨hL, (hasSheafFlatBaseChangePropertyUnivLE_iff_isCartesianOnFlatAffineArrows.{u, v, w, m}
    B E h S hS p hp G hL).2 hc⟩

end Cartesian

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

-- the abelian structure of the library on sheaves of modules whose sections contain the site
-- would be met first by instance search here, with a universe constraint it cannot solve
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

section Succ

variable {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- **Stacks 0771 (5), direct sums, for the fppf modules at module universe `u + 1`**: a direct
sum of sheaves of modules on the fppf site of `𝒳` in `LQCoh^fbc(𝒪_𝒳)` lies in `LQCoh^fbc(𝒪_𝒳)`.
Over an object lying over an affine scheme, which is quasi-compact, sections commute with the
direct sum (Stacks 0935), so the base change maps of the direct sum along flat arrows between such
objects are invertible. -/
theorem
    isClosedUnderColimitsOfShape_discrete_isLocallyQuasicoherentWithSheafFlatBaseChange_fppf_succ
    (ι : Type w') [HasColimitsOfShape (Discrete ι) AddCommGrpCat.{u + 1}] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (C := SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
      (fun F => IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u + 1}
        B E h S hS p hp F.val) (Discrete ι) where
  colimitsOfShape_le := by
    rintro X ⟨c⟩
    let R := ringStructureSheafCore B S hS p hp B.topology le_rfl
    let J := associatedTopology B S hS p B.topology
    have hev : ∀ x : 𝒳, IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) →
        IsColimit ((PresheafOfModules.evaluation _ (op x)).mapCocone
          ((SheafOfModules.forget R).mapCocone c.cocone)) := by
      intro x hx
      have hqc : J.IsQuasiCompactObject x :=
        GrothendieckTopology.isQuasiCompactObject_of_finite_refinements J x fun Sv hSv => by
          obtain ⟨n, W, g, hg, hcov⟩ :=
            BigFppfOver.hasFiniteSubcovering_associatedTopology B S hS p hp x hx Sv hSv
          exact ⟨n, W, g, hcov, hg⟩
      have := Stacks.Sites.sheafOfModules_sections_preserves_coproducts J R x hqc ι
      exact isColimitOfReflects (forget₂ (ModuleCat _) AddCommGrpCat.{u + 1})
        (isColimitOfPreserves (SheafOfModules.toSheaf.{u + 1} R ⋙
          (sheafSections J AddCommGrpCat.{u + 1}).obj (op x)) c.isColimit)
    have hsh : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B))
        X.val.presheaf :=
      X.isSheaf.of_le (associatedTopology_mono B S hS p (etaleTopology_le_topology B))
    refine isLocallyQuasicoherentWithSheafFlatBaseChange_of_isCartesianOnFlatAffineArrows.{u, u + 1,
      u, u} B E h S hS p hp X.val hsh fun x y φ hφ hx hy => ?_
    rw [← ConcreteCategory.isIso_iff_bijective]
    refine isIso_restrictionBaseChange_of_isColimit_evaluation
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      ((SheafOfModules.forget R).mapCocone c.cocone) φ.op (hev y hy) (hev x hx) fun i => ?_
    have hi := c.prop_diag_obj i
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (hasSheafFlatBaseChangePropertyUnivLE_iff_isCartesianOnFlatAffineArrows.{u, u + 1, u, u}
      B E h S hS p hp (c.diag.obj i).val hi.1).1 hi.2 φ hφ hx hy

/-- **Stacks 0771 (5), colimits of sequences, for the fppf modules at module universe `u + 1`**:
the colimit of a sequence of sheaves of modules on the fppf site of `𝒳` in `LQCoh^fbc(𝒪_𝒳)` lies
in `LQCoh^fbc(𝒪_𝒳)`. It is the cokernel of `1 - shift` on the direct sum, and the class is a weak
Serre subcategory closed under direct sums. -/
theorem isClosedUnderColimitsOfShape_nat_isLocallyQuasicoherentWithSheafFlatBaseChange_fppf_succ :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (C := SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
      (fun F => IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u + 1}
        B E h S hS p hp F.val) ℕ :=
  have := isWeakSerreClass_isLocallyQuasicoherentWithSheafFlatBaseChange_fppf_succ
    B E h S hS p hp
  have :=
    isClosedUnderColimitsOfShape_discrete_isLocallyQuasicoherentWithSheafFlatBaseChange_fppf_succ
      B E h S hS p hp ℕ
  ObjectProperty.isClosedUnderColimitsOfShape_nat_of_isClosedUnderCokernels _

end Succ

/-- **Stacks 0771 (5), colimits of sequences, for `Mod(𝒪_𝒳)` at module universe `u + 1`, for an
algebraic stack**: `LQCoh^fbc(𝒪_𝒳)` is closed under colimits over `ℕ` in the sheaves of modules
on the fppf site with sections in `Type (u + 1)`. -/
instance isClosedUnderColimitsOfShape_nat_locallyQuasicoherentSheafFlatBaseChangeFppfModulesSucc
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (C := SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids B.topology le_rfl))
      (lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒳) ℕ :=
  isClosedUnderColimitsOfShape_nat_isLocallyQuasicoherentWithSheafFlatBaseChange_fppf_succ
    B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids

end AlgebraicGeometry.Stack

end
