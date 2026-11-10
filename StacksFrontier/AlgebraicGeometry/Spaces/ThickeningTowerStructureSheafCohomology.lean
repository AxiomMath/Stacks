module

public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningTowerStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.CechAmitsurSmallSites
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.LimitOfSheafTower
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongACoefficientFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingAlongAFunctorEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DenseSubsiteSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# The sheaf `W ↦ lim Γ(Wₙ, 𝒪)` has no higher cohomology

Let `F ≅ yoneda.obj V` be a represented algebraic space over `S` and `V ⟶ X₀ ⟶ X₁ ⟶ ⋯` a tower of
thickenings of the scheme underlying `V`. The presheaves `W ↦ Γ(Wₙ, 𝒪)` of
`StacksFrontier.AlgebraicGeometry.Spaces.ThickeningTowerStructureSheaf`, given the discrete
topology, are sheaves of topological rings on the affine étale site of `F`, and so is their limit
`𝒪 : W ↦ lim Γ(Wₙ, 𝒪)`. This file proves that the abelian sheaf underlying `𝒪` has vanishing
cohomology in positive degrees, on the affine étale site of `F` and on its small étale site, as
the proof of Stacks 0DEL does:

1. a covering of an affine chart is refined by a finite one, and finite coverings are stable
   under the fibre products of the site, so by Stacks 03F9 it suffices to show that the Čech
   cohomology of `𝒪` on a finite covering vanishes in positive degrees;
2. the Čech complex of `𝒪` is the inverse limit of the Čech complexes of the sheaves
   `W ↦ Γ(Wₙ, 𝒪)`, and on a finite covering these are the Čech complexes of the structure sheaf of
   the affine scheme `Wₙ` for the lifted covering, a standard étale covering, which are exact in
   positive degrees by Stacks 03FJ — the faithfully flat descent of Stacks 023M;
3. the transition maps of the inverse system are surjective, being restrictions along closed
   immersions of affine schemes, so the limit is exact as well, by the Mittag-Leffler argument.

## Main definitions

* `AlgebraicGeometry.Space.towerTopRingsSystem`: the inverse system of the sheaves of discrete
  topological rings `W ↦ Γ(Wₙ, 𝒪)`.
* `AlgebraicGeometry.Space.towerStructureSheafAffine`: its limit `W ↦ lim Γ(Wₙ, 𝒪)`, a sheaf of
  topological rings on the affine étale site of `F`.
* `AlgebraicGeometry.Space.towerStructureSheaf`: the corresponding sheaf of topological rings on
  the small étale site of `F`, through the equivalence of topoi of Stacks 04JS.

## Main results

* `AlgebraicGeometry.Space.isZero_cechCohomology_towerStructureSheafAffine`: the Čech cohomology
  of `𝒪` on a finite covering vanishes in positive degrees.
* `AlgebraicGeometry.Space.subsingleton_sheafH_towerStructureSheafAffine`: the cohomology of `𝒪`
  on the affine étale site vanishes in positive degrees.
* `AlgebraicGeometry.Space.subsingleton_sheafH_towerStructureSheaf`: the cohomology of `𝒪` on the
  small étale site vanishes in positive degrees.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CechSite

universe x u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS} (e : F ≅ yoneda.obj V)
  (T : ThickeningTower ((BigFppfOver.toScheme B S hS).obj V))

/-! ### Finite coverings of the affine étale site -/

section Coverings

variable (B S hS F)

/-- **A covering sieve of an affine chart contains a covering family of the affine étale site.**
The image of the sieve in the small étale site is covering, by Stacks 04JS, and is refined there
by a finite family of affine charts. -/
theorem AffineEtale.exists_isCovering_le (hF : IsAlgebraicSpace B S hS F)
    {X : AffineEtale B S hS F} {R : Sieve X} (hR : R ∈ AffineEtale.topology B S hS F X) :
    ∃ E : PreZeroHypercover.{u + 1} X, AffineEtale.IsCovering B S hS F ⟨X, E⟩ ∧
      ∀ i, R (E.f i) := by
  have hd : (AffineEtale.inclusion B S hS F).IsDenseSubsite
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  have hR' : R.functorPushforward (AffineEtale.inclusion B S hS F) ∈
      SmallEtale.topology B S hS F ((AffineEtale.inclusion B S hS F).obj X) :=
    Functor.IsDenseSubsite.functorPushforward_mem_iff.2 hR
  obtain ⟨P, hP, hPR⟩ := AffineEtale.exists_covering_refining_pullback B S hS F hR' (𝟙 _)
  obtain ⟨E, rfl, hE⟩ := (AffineEtale.mem_precoverage_iff B S hS F).mp hP
  refine ⟨E, hE, fun i ↦ ?_⟩
  obtain ⟨Y, g, h, hg, hh⟩ := hPR (E.f i) ⟨i⟩
  have : E.f i = (AffineEtale.inclusion B S hS F).preimage h ≫ g := by
    apply (AffineEtale.inclusion B S hS F).map_injective
    rw [Functor.map_comp, Functor.map_preimage, ← hh, Category.comp_id]
  rw [this]
  exact R.downward_closed hg _

/-- The underlying morphisms of schemes of a covering family of affine charts are jointly
surjective. -/
theorem AffineEtale.jointlySurjective_of_isCovering {X : AffineEtale B S hS F}
    {E : PreZeroHypercover.{u + 1} X} (hE : AffineEtale.IsCovering B S hS F ⟨X, E⟩) :
    ∀ x : (AffineEtale.toScheme B S hS F).obj X, ∃ i,
      ∃ y : (AffineEtale.toScheme B S hS F).obj (E.X i),
        (AffineEtale.toScheme B S hS F).map (E.f i) y = x := by
  have hcov := (Scheme.presieve₀_mem_precoverage_iff
    ((E.map (AffineEtale.toSchemes B S hS F)).map B.inclusion)).mp hE.1.2
  exact fun x ↦ hcov.1 x

/-- The covering families used for the Čech computation: finite families indexed in `Type u`,
generating a covering sieve, whose underlying morphisms of schemes are jointly surjective. -/
def finiteCoverings (X : AffineEtale B S hS F) :
    Set { E : PreZeroHypercover.{u} X // E.sieve₀ ∈ AffineEtale.topology B S hS F X } :=
  {E | Finite E.1.I₀ ∧ ∀ x : (AffineEtale.toScheme B S hS F).obj X, ∃ i,
      ∃ y : (AffineEtale.toScheme B S hS F).obj (E.1.X i),
        (AffineEtale.toScheme B S hS F).map (E.1.f i) y = x}

/-- The iterated fibre products of a family of affine charts exist. -/
theorem finiteCoverings_hasProducts :
    ∀ {U : AffineEtale B S hS F}
      (E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ AffineEtale.topology B S hS F U }),
      E ∈ finiteCoverings B S hS F U → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        HasProduct (fun a ↦ Over.mk (E.1.f (i a))) :=
  fun E _ p i ↦ Stacks.Sites.hasProduct_fibreProducts E.1 (fun _ _ _ ↦ inferInstance) p i

/-- **The finite coverings are cofinal.** -/
theorem finiteCoverings_cofinal (hF : IsAlgebraicSpace B S hS F) :
    ∀ U ∈ (Set.univ : Set (AffineEtale B S hS F)), ∀ R ∈ AffineEtale.topology B S hS F U,
      ∃ E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ AffineEtale.topology B S hS F U },
        E ∈ finiteCoverings B S hS F U ∧ E.1.sieve₀ ≤ R := by
  intro U _ R hR
  obtain ⟨E, hE, hER⟩ := AffineEtale.exists_isCovering_le B S hS F hF hR
  have _ : Finite E.I₀ := hE.2
  obtain ⟨n, ⟨eqv⟩⟩ := Finite.exists_equiv_fin E.I₀
  let eqv' : ULift.{u} (Fin n) ≃ E.I₀ := Equiv.ulift.trans eqv.symm
  let E' : PreZeroHypercover.{u} U := E.restrictIndex eqv'
  have hpre : E'.presieve₀ = E.presieve₀ := E.presieve₀_restrictIndex_equiv eqv'
  have hmem : E'.sieve₀ ∈ AffineEtale.topology B S hS F U := by
    change Sieve.generate E'.presieve₀ ∈ AffineEtale.topology B S hS F U
    rw [hpre]
    exact Precoverage.generate_mem_toGrothendieck
      ((AffineEtale.mem_precoverage_iff B S hS F).mpr ⟨E, rfl, hE⟩)
  refine ⟨⟨E', hmem⟩, ⟨inferInstanceAs (Finite (ULift.{u} (Fin n))), fun x ↦ ?_⟩, ?_⟩
  · obtain ⟨i, y, hy⟩ := AffineEtale.jointlySurjective_of_isCovering B S hS F hE x
    obtain ⟨j, rfl⟩ := eqv'.surjective i
    exact ⟨j, y, hy⟩
  · rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff]
    rintro Y g ⟨j⟩
    exact hER (eqv' j)

end Coverings

/-! ### The abelian sheaves of the tower and their Čech cohomology -/

/-- The abelian presheaf `W ↦ Γ(Wₙ, 𝒪)`, read through the small étale site of the stage `Xₙ`. -/
noncomputable abbrev towerSections (n : ℕ) : (AffineEtale B S hS F)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (towerLift e T n).op ⋙ ((Scheme.Etale.forget (T.stage.obj n)).op ⋙
    globalFunctionsAddPresheaf (T.stage.obj n))

/-- **The lift of a finite covering is a standard étale covering.** -/
theorem isSmallEtaleStandardCovering_map_towerLift (n : ℕ) {W : AffineEtale B S hS F}
    (E : PreZeroHypercover.{u} W) (hfin : Finite E.I₀)
    (hsurj : ∀ x : (AffineEtale.toScheme B S hS F).obj W, ∃ i,
      ∃ y : (AffineEtale.toScheme B S hS F).obj (E.X i),
        (AffineEtale.toScheme B S hS F).map (E.f i) y = x) :
    IsSmallEtaleStandardCovering (T.stage.obj n) (E.map (towerLift e T n)) := by
  refine ⟨isAffine_towerLift_obj_left e T n W, ⟨hfin, fun i ↦ isAffine_towerLift_obj_left e T n _,
    ?_, fun i ↦ ?_⟩⟩
  · refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
    obtain ⟨i, y, hy⟩ := T.lift_jointlySurjective n
      (fun i ↦ (representedAffineChartEtale e).map (E.f i)) (fun x ↦ hsurj x) x
    exact Set.mem_iUnion.mpr ⟨i, y, hy⟩
  · exact inferInstanceAs (Etale ((towerLift e T n).map (E.f i)).left)

/-- Vanishing of Čech cohomology transports along an isomorphism of coefficient presheaves. -/
private theorem isZero_cechCohomology_of_iso {C : Type*} [Category C] {A : Type*} [Category A]
    [Abelian A] [HasProducts.{u} A] {X : C} {E : PreZeroHypercover.{u} X}
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    {F G : Cᵒᵖ ⥤ A} (i : F ≅ G) {p : ℕ} (h : IsZero (cechCohomology E F p)) :
    IsZero (cechCohomology E G p) :=
  h.of_iso ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) p).mapIso
    ((Stacks.CechSite.cechComplexFunctor E).mapIso i)).symm

/-- **The Čech cohomology of `W ↦ Γ(Wₙ, 𝒪)` on a finite covering vanishes in positive degrees.**
The lifted covering is a standard étale covering of the affine scheme `Wₙ`, the lift preserves
fibre products, and the presheaf is the structure sheaf of `Xₙ` on its small étale site, so this
is Stacks 03FJ. -/
theorem isZero_cechCohomology_towerSections (n : ℕ) {W : AffineEtale B S hS F}
    (E : PreZeroHypercover.{u} W) (hfin : Finite E.I₀)
    (hsurj : ∀ x : (AffineEtale.toScheme B S hS F).obj W, ∃ i,
      ∃ y : (AffineEtale.toScheme B S hS F).obj (E.X i),
        (AffineEtale.toScheme B S hS F).map (E.f i) y = x)
    [∀ (q : ℕ) (i : Fin (q + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology E (towerSections e T n) p) := by
  let L := towerLift e T n
  let I : (T.stage.obj n).Etaleᵒᵖ ⥤ AddCommGrpCat.{u} :=
    (Scheme.Etale.forget (T.stage.obj n)).op ⋙ globalFunctionsAddPresheaf (T.stage.obj n)
  have h₀ := isZero_cechCohomology_succ_quasiCoherentPresheaf_smallEtale (T.stage.obj n)
    (Scheme.unitModule (T.stage.obj n)) (E.map L)
    (isSmallEtaleStandardCovering_map_towerLift e T n E hfin hsurj) p hp
  have h₁ : IsZero (cechCohomology (E.map L) I p) :=
    isZero_cechCohomology_of_iso (Functor.isoWhiskerLeft (Scheme.Etale.forget (T.stage.obj n)).op
      (quasiCoherentPresheafUnitIso (T.stage.obj n))) h₀
  have hcomp : ∀ (q : ℕ) (i : Fin (q + 1) → E.I₀), IsIso (cechProductMapOfFunctor L E q i) := by
    intro q i
    let _ : PreservesLimit (Discrete.functor (fun a ↦ Over.mk (E.f (i a))))
        (Over.post (X := W) L) :=
      Stacks.Sites.preservesLimit_fibreProducts_overPost L E
        (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) q i
    exact isIso_cechProductMapOfFunctor L E q i
  exact cechCohomology_isZero_of_isZero_of_functor L E I hcomp p h₁

/-! ### The sheaf of topological rings `W ↦ lim Γ(Wₙ, 𝒪)` -/

/-- The inverse system of the presheaves of discrete topological rings `W ↦ Γ(Wₙ, 𝒪)`, with
their values raised one universe. -/
noncomputable def towerTopRingsSystem :
    ℕᵒᵖ ⥤ ((AffineEtale B S hS F)ᵒᵖ ⥤ TopCommRingCat.{u + 1}) :=
  towerRingsSystem e T ⋙
    (Functor.whiskeringRight _ _ _).obj TopCommRingCat.discreteULiftFunctor.{u + 1}

/-- **`W ↦ Γ(Wₙ, 𝒪)` is a sheaf of discrete topological rings.** It is a sheaf of rings, and the
covering sieves of the affine étale site contain finite covering families. -/
theorem isSheaf_towerTopRingsSystem_obj (hF : IsAlgebraicSpace B S hS F) (n : ℕᵒᵖ) :
    Presheaf.IsSheaf (AffineEtale.topology B S hS F) ((towerTopRingsSystem e T).obj n) :=
  TopCommRingCat.isSheaf_comp_discreteULiftFunctor.{u + 1, u, u, u + 1, u + 1} _
    (towerRings e T n.unop) (isSheaf_towerRings_forget e T n.unop) (fun X R hR ↦ by
      obtain ⟨E, hE, hER⟩ := AffineEtale.exists_isCovering_le B S hS F hF hR
      exact ⟨E.I₀, hE.2, E.X, E.f, hER, Precoverage.generate_mem_toGrothendieck
        ((AffineEtale.mem_precoverage_iff B S hS F).mpr ⟨E, rfl, hE⟩)⟩)

/-- The inverse system of the sheaves of discrete topological rings `W ↦ Γ(Wₙ, 𝒪)`. -/
noncomputable def towerSheafSystem (hF : IsAlgebraicSpace B S hS F) :
    ℕᵒᵖ ⥤ Sheaf (AffineEtale.topology B S hS F) TopCommRingCat.{u + 1} :=
  ObjectProperty.lift _ (towerTopRingsSystem e T) (isSheaf_towerTopRingsSystem_obj e T hF)

/-- **The sheaf `W ↦ lim Γ(Wₙ, 𝒪)` of topological rings on the affine étale site of `F`**: the
inverse limit of the sheaves of discrete rings `W ↦ Γ(Wₙ, 𝒪)`, so that its sections over `W`
carry the inverse-limit topology. -/
noncomputable def towerStructureSheafAffine (hF : IsAlgebraicSpace B S hS F) :
    Sheaf (AffineEtale.topology B S hS F) TopCommRingCat.{u + 1} :=
  limit (towerSheafSystem e T hF)

/-- The functor from topological rings to their additive groups. -/
abbrev topCommRingToAddCommGrp : TopCommRingCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  forget₂ TopCommRingCat CommRingCat ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

/-- The functor `topCommRingToAddCommGrp` preserves limits of size `u + 1`. -/
instance preservesLimitsOfSize_topCommRingToAddCommGrp :
    PreservesLimitsOfSize.{u + 1, u + 1} topCommRingToAddCommGrp.{u} := by
  unfold topCommRingToAddCommGrp
  infer_instance

/-- The functor `topCommRingToAddCommGrp` preserves limits indexed by categories in universe
`0`. -/
instance preservesLimitsOfSize_zero_topCommRingToAddCommGrp :
    PreservesLimitsOfSize.{0, 0} topCommRingToAddCommGrp.{u} :=
  preservesSmallestLimits_of_preservesLimits _

/-- For every Grothendieck topology on the affine étale site of `F`, composing a sheaf of
topological rings with `topCommRingToAddCommGrp` gives a sheaf of abelian groups. -/
instance (J : GrothendieckTopology (AffineEtale B S hS F)) :
    J.HasSheafCompose topCommRingToAddCommGrp.{u} := by
  have : PreservesLimitsOfSize.{u, u + 1} topCommRingToAddCommGrp.{u} :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  infer_instance

/-- The inverse system of the abelian presheaves underlying `W ↦ Γ(Wₙ, 𝒪)`. -/
noncomputable abbrev towerAbSystem :
    ℕᵒᵖ ⥤ ((AffineEtale B S hS F)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  towerTopRingsSystem e T ⋙ (Functor.whiskeringRight _ _ _).obj topCommRingToAddCommGrp

/-- The abelian presheaf underlying `W ↦ Γ(Wₙ, 𝒪)` is `W ↦ Γ(Wₙ, 𝒪)` read through the small étale
site of `Xₙ`, with its sections raised one universe. -/
noncomputable def towerAbSystemObjIso (n : ℕ) :
    (towerAbSystem e T).obj (op n) ≅ towerSections e T n ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The limit cone of the abelian presheaves underlying `W ↦ lim Γ(Wₙ, 𝒪)`. -/
noncomputable def towerAbCone (hF : IsAlgebraicSpace B S hS F) : Cone (towerAbSystem e T) :=
  ((Functor.whiskeringRight _ _ _).obj topCommRingToAddCommGrp).mapCone
    ((sheafToPresheaf _ _).mapCone (limit.cone (towerSheafSystem e T hF)))

/-- **The abelian presheaf underlying `W ↦ lim Γ(Wₙ, 𝒪)` is the limit of those underlying
`W ↦ Γ(Wₙ, 𝒪)`**: the forgetful functors preserve limits. -/
noncomputable def isLimitTowerAbCone (hF : IsAlgebraicSpace B S hS F) :
    IsLimit (towerAbCone e T hF) :=
  isLimitOfPreserves _ (isLimitOfPreserves _ (limit.isLimit _))

/-- The cone point of `AlgebraicGeometry.Space.towerAbCone` is the abelian presheaf underlying
`W ↦ lim Γ(Wₙ, 𝒪)`. -/
theorem towerAbCone_pt (hF : IsAlgebraicSpace B S hS F) :
    (towerAbCone e T hF).pt =
      ((sheafCompose _ topCommRingToAddCommGrp).obj (towerStructureSheafAffine e T hF)).obj :=
  rfl

/-- **The Čech cohomology of `W ↦ lim Γ(Wₙ, 𝒪)` on a finite covering vanishes in positive
degrees.** It is the limit of the Čech cohomology of the sheaves `W ↦ Γ(Wₙ, 𝒪)`, which vanishes
by Stacks 03FJ, and the transition maps are surjective. -/
theorem isZero_cechCohomology_towerStructureSheafAffine (hF : IsAlgebraicSpace B S hS F)
    {W : AffineEtale B S hS F} (E : PreZeroHypercover.{u} W)
    (hcov : E.sieve₀ ∈ AffineEtale.topology B S hS F W) (hfin : Finite E.I₀)
    (hsurj : ∀ x : (AffineEtale.toScheme B S hS F).obj W, ∃ i,
      ∃ y : (AffineEtale.toScheme B S hS F).obj (E.X i),
        (AffineEtale.toScheme B S hS F).map (E.f i) y = x)
    [∀ (q : ℕ) (i : Fin (q + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology E
      ((sheafCompose _ topCommRingToAddCommGrp).obj (towerStructureSheafAffine e T hF)).obj p) := by
  refine isZero_cechCohomology_of_isLimit_tower E (AffineEtale.topology B S hS F) hcov
    (towerAbSystem e T) (towerAbCone e T hF) (isLimitTowerAbCone e T hF) (fun n ↦ ?_)
    (fun n q hq ↦ ?_) (fun n W' ↦ ?_) p hp
  · exact ((sheafCompose _ topCommRingToAddCommGrp).obj ((towerSheafSystem e T hF).obj (op n))).2
  · have : AddCommGrpCat.uliftFunctor.{u + 1, u}.PreservesHomology :=
      Functor.preservesHomologyOfExact _
    have h' := isZero_cechCohomology_comp_coefficients E AddCommGrpCat.uliftFunctor.{u + 1, u}
      (towerSections e T n) q (isZero_cechCohomology_towerSections e T n E hfin hsurj q hq)
    exact isZero_cechCohomology_of_iso (towerAbSystemObjIso e T n).symm h'
  · intro y
    obtain ⟨x, hx⟩ := surjective_towerRingsTransition e T n (op W') y.down
    refine ⟨ULift.up x, ?_⟩
    change TopCommRingCat.DiscreteULift.up (((towerRingsSystem e T).map
      (homOfLE (Nat.le_succ n)).op).app (op W') x) = y
    rw [towerRingsSystem_map_succ]
    exact congrArg ULift.up hx

/-! ### The terminal chart -/

/-- The étale chart `yoneda.obj V ≅ F` of `F` given by the identification `e` itself. -/
noncomputable def representedTerminalChart : SmallEtale B S hS F :=
  ⟨CostructuredArrow.mk e.inv, by
    have h := FormalSpace.isEtaleChart_yoneda_map B S hS (𝟙 V)
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
    rw [CategoryTheory.Functor.map_id] at h
    refine (isEtaleChart_comp_iso_iff B S hS e e.inv).1 ?_
    rwa [Iso.inv_hom_id]⟩

/-- **The chart `e` is a terminal object of the small étale site of `F`**: a chart of `F` maps to
it by the morphism of the site it determines through `e`, and by no other. -/
noncomputable def isTerminalRepresentedTerminalChart : IsTerminal (representedTerminalChart e) :=
  IsTerminal.ofUniqueHom
    (fun W ↦ ObjectProperty.homMk (CostructuredArrow.homMk (chartToRepresented e W) (by
      change yoneda.map (chartToRepresented e W) ≫ e.inv = W.obj.hom
      rw [yoneda_map_chartToRepresented, Category.assoc, Iso.hom_inv_id, Category.comp_id])))
    (fun W m ↦ by
      apply ObjectProperty.hom_ext
      refine CostructuredArrow.hom_ext _ _ ?_
      apply yoneda.map_injective
      change yoneda.map m.hom.left = yoneda.map (chartToRepresented e W)
      rw [yoneda_map_chartToRepresented]
      have hw : yoneda.map m.hom.left ≫ e.inv = W.obj.hom := CostructuredArrow.w m.hom
      exact ((Category.comp_id _).symm.trans
        (congrArg (yoneda.map m.hom.left ≫ ·) e.inv_hom_id.symm)).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ e.hom) hw)))

/-- The terminal chart, as an affine chart when `V` is affine. -/
noncomputable def representedTerminalAffineChart
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) : AffineEtale B S hS F :=
  ⟨representedTerminalChart e, hV⟩

/-- The terminal chart is a terminal object of the affine étale site. -/
noncomputable def isTerminalRepresentedTerminalAffineChart
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    IsTerminal (representedTerminalAffineChart e hV) :=
  IsTerminal.ofUniqueHom
    (fun W ↦ ObjectProperty.homMk ((isTerminalRepresentedTerminalChart e).from W.obj))
    (fun _ _ ↦ ObjectProperty.hom_ext _ ((isTerminalRepresentedTerminalChart e).hom_ext _ _))

/-! ### Vanishing of the cohomology -/

/-- **The cohomology of `W ↦ lim Γ(Wₙ, 𝒪)` on the affine étale site vanishes in positive
degrees.** This is Stacks 03F9 for the finite coverings of the affine étale site, which are
cofinal and stable under fibre products, with the Čech vanishing of
`AlgebraicGeometry.Space.isZero_cechCohomology_towerStructureSheafAffine`, read at the terminal
chart. -/
theorem subsingleton_sheafH_towerStructureSheafAffine (hF : IsAlgebraicSpace B S hS F)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    [HasExt.{x} (Sheaf (AffineEtale.topology B S hS F) AddCommGrpCat.{u + 1})]
    (p : ℕ) (hp : 0 < p) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ topCommRingToAddCommGrp).obj (towerStructureSheafAffine e T hF)) p) :=
  subsingleton_sheafH_of_cechCohomology_isZero.{x, 0} (AffineEtale.topology B S hS F) Set.univ
    (finiteCoverings B S hS F) (finiteCoverings_hasProducts B S hS F)
    (fun _ _ ↦ ⟨trivial, fun _ ↦ trivial, fun _ _ ↦ trivial⟩)
    (finiteCoverings_cofinal B S hS F hF) _
    (fun E hE q hq ↦ by
      let := finiteCoverings_hasProducts B S hS F E hE
      exact isZero_cechCohomology_towerStructureSheafAffine e T hF E.1 E.2 hE.1 hE.2 q hq)
    (isTerminalRepresentedTerminalAffineChart e hV) trivial p hp

/-- The limits over the comma categories of the inclusion of the affine étale site exist in
topological rings and in abelian groups one universe up. -/
instance hasLimitsOfShape_structuredArrow_affineEtaleInclusion
    (Y : (SmallEtale B S hS F)ᵒᵖ) (A : Type (u + 2)) [Category.{u + 1} A] [HasLimits A] :
    HasLimitsOfShape (StructuredArrow Y (AffineEtale.inclusion B S hS F).op) A := by
  have : HasLimitsOfSize.{u, u + 1} A := hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  infer_instance

/-- **The sheaf `W ↦ lim Γ(Wₙ, 𝒪)` on the small étale site of `F`**: the sheaf of topological
rings on the small étale site whose restriction to the affine charts is
`AlgebraicGeometry.Space.towerStructureSheafAffine`, through the equivalence of topoi of
Stacks 04JS. -/
noncomputable def towerStructureSheaf (hF : IsAlgebraicSpace B S hS F) :
    Sheaf (SmallEtale.topology B S hS F) TopCommRingCat.{u + 1} :=
  have : (AffineEtale.inclusion B S hS F).IsDenseSubsite
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  (Functor.IsDenseSubsite.sheafEquiv (AffineEtale.topology B S hS F)
    (SmallEtale.topology B S hS F) (AffineEtale.inclusion B S hS F)
    TopCommRingCat.{u + 1}).functor.obj
    (towerStructureSheafAffine e T hF)

/-- The restriction of `AlgebraicGeometry.Space.towerStructureSheaf` to the affine charts is
`AlgebraicGeometry.Space.towerStructureSheafAffine`. -/
noncomputable def towerStructureSheafRestrictionIso (hF : IsAlgebraicSpace B S hS F) :
    have : (AffineEtale.inclusion B S hS F).IsDenseSubsite
        (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) :=
      (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
    ((AffineEtale.inclusion B S hS F).sheafPushforwardContinuous TopCommRingCat.{u + 1}
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F)).obj
        (towerStructureSheaf e T hF) ≅ towerStructureSheafAffine e T hF :=
  have : (AffineEtale.inclusion B S hS F).IsDenseSubsite
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  (Functor.IsDenseSubsite.sheafEquiv (AffineEtale.topology B S hS F)
    (SmallEtale.topology B S hS F) (AffineEtale.inclusion B S hS F)
      TopCommRingCat.{u + 1}).unitIso.symm.app (towerStructureSheafAffine e T hF)

/-- For every Grothendieck topology on the small étale site of `F`, composing a sheaf of
topological rings with `topCommRingToAddCommGrp` gives a sheaf of abelian groups. -/
instance (J : GrothendieckTopology (SmallEtale B S hS F)) :
    J.HasSheafCompose topCommRingToAddCommGrp.{u} := by
  have : PreservesLimitsOfSize.{u, u + 1} topCommRingToAddCommGrp.{u} :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  infer_instance

/-- **The cohomology of `W ↦ lim Γ(Wₙ, 𝒪)` on the small étale site of `F` vanishes in positive
degrees.** The affine étale site is a dense subsite of the small étale site containing its
terminal object (Stacks 04JS), so the two have the same cohomology, and on the affine étale site
the cohomology vanishes by
`AlgebraicGeometry.Space.subsingleton_sheafH_towerStructureSheafAffine`. -/
theorem subsingleton_sheafH_towerStructureSheaf (hF : IsAlgebraicSpace B S hS F)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    [HasExt.{x} (Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u + 1})]
    (p : ℕ) (hp : 0 < p) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ topCommRingToAddCommGrp).obj (towerStructureSheaf e T hF)) p) := by
  have : (AffineEtale.inclusion B S hS F).IsDenseSubsite
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  let : HasExt.{u + 1} (Sheaf (AffineEtale.topology B S hS F) AddCommGrpCat.{u + 1}) :=
    Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, u}
  open Stacks.Cohomology.DenseSubsiteSheaf in
  refine subsingleton_H_of_subsingleton_H_restriction_of_isDenseSubsite
    (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) (AffineEtale.inclusion B S hS F)
    (isTerminalRepresentedTerminalAffineChart e hV) (isTerminalRepresentedTerminalChart e) _ p ?_
  let i : ((AffineEtale.inclusion B S hS F).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F)).obj
        ((sheafCompose _ topCommRingToAddCommGrp).obj (towerStructureSheaf e T hF)) ≅
      (sheafCompose _ topCommRingToAddCommGrp).obj (towerStructureSheafAffine e T hF) :=
    (sheafCompose _ topCommRingToAddCommGrp).mapIso (towerStructureSheafRestrictionIso e T hF)
  exact (((Abelian.extFunctor p).obj (op ((constantSheaf (AffineEtale.topology B S hS F)
    AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))))).mapIso
      i).addCommGroupIsoToAddEquiv.subsingleton_congr.mpr
        (subsingleton_sheafH_towerStructureSheafAffine e T hF hV p hp)

end AlgebraicGeometry.Space

end
