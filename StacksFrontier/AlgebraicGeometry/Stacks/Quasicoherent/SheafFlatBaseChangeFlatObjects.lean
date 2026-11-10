module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleChartPullbackConservative
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatObjectArrowFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedSmallEtaleSheafInvComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentEtaleLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangePropertySheafified

/-!
# The flat base change property holds along every arrow between flat objects

Let `𝒳` be an algebraic stack and let `F` be a sheaf of `𝒪_𝒳`-modules on `𝒳_étale` which is
locally quasi-coherent (**Stacks 06WJ**) and has the flat base change property of
**Stacks 0762** — the comparison map `c_φ : f_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of **Stacks 06WC**,
for the pullback of sheaves, is an isomorphism for every arrow `φ` lying over a flat morphism of
schemes.  This file proves that `c_φ` is then an isomorphism for **every arrow between flat
objects** of `𝒳` (**Stacks 0787**), whether or not the morphism of schemes below it is flat.

This is the input of **Stacks 07B1** (1)(b) and (2)(b): on the flat-fppf site every arrow is one
between flat objects, so there `F` is cartesian.

## The argument

By `AlgebraicGeometry.Stack.FlatFppf.exists_flat_factorization`, étale-locally on the source an
arrow `φ : y ⟶ x` between flat objects factors as `κ ≫ φ = χ ≫ π₂` with `χ ≫ π₁ = κ`, where `κ`
lies over an étale morphism and `π₁`, `π₂` over flat ones.  Write `θ_ψ` for the comparison of an
arrow `ψ` read as a morphism of sheaves (`AlgebraicGeometry.Stack.sheafifiedRestrictComparison`).
The composition law **Stacks 075D** (1) for `θ`
(`AlgebraicGeometry.Stack.sheafifiedRestrictComparison_comp`) gives two out of three:

* `θ_{π₁}` and `θ_κ = θ_{χ ≫ π₁}` are isomorphisms, hence so is `θ_χ`;
* `θ_χ` and `θ_{π₂}` are, hence so is `θ_{χ ≫ π₂} = θ_{κ ≫ φ}`;
* `θ_κ` and `θ_{κ ≫ φ}` are, hence so is the pullback of `θ_φ` along `κ`.

Pullback along the étale arrows `κ` of a jointly surjective family is jointly conservative
(`AlgebraicGeometry.SmallEtale.isIso_of_isIso_pullback_map_of_coversTop`), so `θ_φ` is an
isomorphism.

## Main results

* `AlgebraicGeometry.Stack.isIso_sheafifiedRestrictComparison_of_comp_left`,
  `AlgebraicGeometry.Stack.isIso_sheafifiedRestrictComparison_comp` and
  `AlgebraicGeometry.Stack.isIso_sheafifiedPullbackComparison_map_of_comp`: two out of three for
  the comparisons.
* `AlgebraicGeometry.Stack.isIso_of_isIso_sheafifiedPullbackComparison_map`: joint
  conservativity of the pullbacks along a jointly surjective family of étale arrows.
* `AlgebraicGeometry.Stack.isIso_sheafifiedRestrictComparison_of_flatObject`: the comparison is an
  isomorphism along every arrow between flat objects.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

section TwoOutOfThree

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)
  {x z z' : 𝒳} (ψ : z' ⟶ z) (φ : z ⟶ x)
  (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
      (contains_base B E h S hS p x))
    (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B) F).presheaf)
  (hMz : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
      (contains_base B E h S hS p z))
    (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B) F).presheaf)
  (hMz' : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z').left.1
      (contains_base B E h S hS p z'))
    (restrictModuleToSmallEtale B E h S hS p hp z' (etaleTopology B)
      (etaleTopology_le_topology B) F).presheaf)

include hMx in
/-- **Two out of three, first form**: if the comparisons along `φ` and along `ψ ≫ φ` are
isomorphisms, so is the comparison along `ψ`. -/
theorem isIso_sheafifiedRestrictComparison_of_comp_left
    [hφ : IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ hMz)]
    [hψφ : IsIso (sheafifiedRestrictComparison B E h S hS p hp F (ψ ≫ φ) hMz')] :
    IsIso (sheafifiedRestrictComparison B E h S hS p hp F ψ hMz') := by
  have w := sheafifiedRestrictComparison_comp B E h S hS p hp F ψ φ hMx hMz hMz'
  have h₁ := Iso.isIso_hom ((sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) ψ).mapIso
    (@asIso _ _ _ _ (sheafifiedRestrictComparison B E h S hS p hp F φ hMz) hφ))
  have h₃ := Iso.isIso_hom (((sheafifiedPullbackComparisonCompIso B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) ψ φ).app (restrictModuleToSmallEtaleSheaf B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) F x hMx)) ≪≫
    @asIso _ _ _ _ (sheafifiedRestrictComparison B E h S hS p hp F (ψ ≫ φ) hMz') hψφ)
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ h₁ h₃ w

include hMx in
/-- **Two out of three, second form**: if the comparisons along `φ` and along `ψ` are
isomorphisms, so is the comparison along `ψ ≫ φ`. -/
theorem isIso_sheafifiedRestrictComparison_comp
    [hφ : IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ hMz)]
    [hψ : IsIso (sheafifiedRestrictComparison B E h S hS p hp F ψ hMz')] :
    IsIso (sheafifiedRestrictComparison B E h S hS p hp F (ψ ≫ φ) hMz') := by
  have w := (sheafifiedRestrictComparison_comp B E h S hS p hp F ψ φ hMx hMz hMz').symm
  have h₂ := Iso.isIso_hom ((sheafifiedPullbackComparisonCompIso B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) ψ φ).app (restrictModuleToSmallEtaleSheaf B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) F x hMx))
  have h₃ := Iso.isIso_hom ((sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) ψ).mapIso
    (@asIso _ _ _ _ (sheafifiedRestrictComparison B E h S hS p hp F φ hMz) hφ) ≪≫
    @asIso _ _ _ _ (sheafifiedRestrictComparison B E h S hS p hp F ψ hMz') hψ)
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ h₂ h₃ w

include hMx in
/-- **Two out of three, third form**: if the comparisons along `ψ` and along `ψ ≫ φ` are
isomorphisms, so is the pullback along `ψ` of the comparison along `φ`. -/
theorem isIso_sheafifiedPullbackComparison_map_of_comp
    [hψ : IsIso (sheafifiedRestrictComparison B E h S hS p hp F ψ hMz')]
    [hψφ : IsIso (sheafifiedRestrictComparison B E h S hS p hp F (ψ ≫ φ) hMz')] :
    IsIso ((sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) ψ).map
        (sheafifiedRestrictComparison B E h S hS p hp F φ hMz)) := by
  have w := sheafifiedRestrictComparison_comp B E h S hS p hp F ψ φ hMx hMz hMz'
  have h₃ := Iso.isIso_hom (((sheafifiedPullbackComparisonCompIso B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) ψ φ).app (restrictModuleToSmallEtaleSheaf B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) F x hMx)) ≪≫
    @asIso _ _ _ _ (sheafifiedRestrictComparison B E h S hS p hp F (ψ ≫ φ) hMz') hψφ)
  exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ hψ h₃ w

end TwoOutOfThree

section Conservative

variable {𝒳 : Type v} [Category.{w} 𝒳]

/-- **The pullbacks along a jointly surjective family of étale arrows are jointly
conservative.**  If arrows `φ i : y i ⟶ x` of `𝒳` lie over étale morphisms of schemes which are
jointly surjective, and a morphism `α` of sheaves of modules on the small étale site of the scheme
below `x` becomes an isomorphism after the sheafified Stacks 06WC pullback along every `φ i`, then
`α` is an isomorphism.

The sheafified pullback along `φ i` is the pullback of sheaves of modules along the morphism of
ringed small étale sites of the chart of `φ i`
(`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonIso`), and those are jointly conservative
for a family of charts covering the final object
(`AlgebraicGeometry.SmallEtale.isIso_of_isIso_pullback_map_of_coversTop`). -/
theorem isIso_of_isIso_sheafifiedPullbackComparison_map (p : 𝒳 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (x : 𝒳) {I : Type (u + 1)} (y : I → 𝒳) (φ : ∀ i, y i ⟶ x)
    (hetale : ∀ i, Etale (B.inclusion.map (p.map (φ i)).left))
    (hcov : ∀ t : B.inclusion.obj (p.obj x).left,
      ∃ i, t ∈ Set.range (B.inclusion.map (p.map (φ i)).left))
    {M N : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x))} (α : M ⟶ N)
    (hα : ∀ i, IsIso ((sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) (φ i)).map α)) :
    IsIso α := by
  have etaleFamily : ∀ (X : Scheme.{u}) (hX : E.Contains X) {W : SmallEtale E X hX}
      (D : PreZeroHypercover.{u + 1} W),
      (D.map (SmallEtale.toScheme E X hX)).presieve₀ ∈
        Scheme.etalePrecoverage ((SmallEtale.toScheme E X hX).obj W) →
      Sieve.generate D.presieve₀ ∈ SmallEtale.topology E X hX W := by
    intro X hX W D hD
    let H := SmallEtale.inclusion E X hX ⋙ Over.forget (E.obj X hX)
    have hDbig : IsEtaleCovering ⟨H.obj W, D.map H⟩ := hD
    obtain ⟨⟨T, R⟩, hR, ht, hcomb⟩ := E.exists_covering_rep ⟨H.obj W, D.map H⟩ hDbig
    cases ht
    obtain ⟨β, hX', hf⟩ := hcomb.2
    have he (i : R.I₀) : Etale (E.inclusion.map (R.f i)) :=
      ((Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).1 hR.1).2 i
    let G : PreZeroHypercover.{u + 1} W :=
      { I₀ := R.I₀
        X i := ⟨Over.mk (R.f i ≫ W.obj.hom), by
          change Etale (E.inclusion.map (R.f i ≫ W.obj.hom))
          rw [E.inclusion.map_comp]
          have := he i
          infer_instance⟩
        f i := ObjectProperty.homMk (Over.homMk (R.f i)) }
    have hG : SmallEtale.IsCovering E X hX ⟨W, G⟩ := hR
    apply (SmallEtale.topology E X hX).superset_covering _
      ((SmallEtale.precoverage E X hX).generate_mem_toGrothendieck
        ((SmallEtale.mem_precoverage_iff E X hX).2 ⟨G, rfl, hG⟩))
    apply (Sieve.generate_le_iff _ _).2
    rintro Y f ⟨i⟩
    let g : G.X i ⟶ D.X (β i) := ObjectProperty.homMk
      (Over.homMk (eqToHom (hX' i)) (by
        change eqToHom (hX' i) ≫ (D.X (β i)).obj.hom = R.f i ≫ W.obj.hom
        rw [hf i]
        simp only [Category.assoc]
        congr 1
        exact (D.f (β i)).hom.w.symm))
    have hcomp : g ≫ D.f (β i) = G.f i := by
      ext
      exact congrArg (fun k => E.inclusion.map k) (hf i).symm
    rw [← hcomp]
    exact (Sieve.generate D.presieve₀).downward_closed
      (Sieve.le_generate _ _ _ (Presieve.ofArrows.mk _)) g
  have hcovTop : (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)).CoversTop
      (fun i => etaleChart B E h S hS p (φ i) (hetale i)) := by
    let hx := contains_base B E h S hS p x
    let V : I → SmallEtale E (p.obj x).left.1 hx :=
      fun i => etaleChart B E h S hS p (φ i) (hetale i)
    let W := SmallEtale.final E (p.obj x).left.1 hx
    let D : PreZeroHypercover.{u + 1} W :=
      { I₀ := I
        X := V
        f := fun i => ObjectProperty.homMk
          (Over.homMk (V i).obj.hom (by simp [W, SmallEtale.final])) }
    have hD : Sieve.generate D.presieve₀ ∈ SmallEtale.topology E (p.obj x).left.1 hx W :=
      etaleFamily (p.obj x).left.1 hx D
        ((Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mpr ⟨hcov, fun i => (V i).property⟩)
    exact (GrothendieckTopology.coversTop_iff_of_isTerminal _ W
      (SmallEtale.finalIsTerminal E (p.obj x).left.1 hx) V).2
      ((SmallEtale.topology E (p.obj x).left.1 hx).superset_covering
        (Sieve.ofArrows_le_ofObjects D.X D.f) hD)
  exact SmallEtale.isIso_of_isIso_pullback_map_of_coversTop E (p.obj x).left.1
    (contains_base B E h S hS p x) (fun i => etaleChart B E h S hS p (φ i) (hetale i))
    hcovTop α fun i =>
      (NatIso.isIso_map_iff (sheafifiedPullbackComparisonIso B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) (φ i)) α).1 (hα i)

end Conservative

section FlatObjects

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)

/-- **The flat base change property along every arrow between flat objects.**  Let `𝒳` be an
algebraic stack and `F` an `𝒪_𝒳`-module on `𝒳_étale` which is locally quasi-coherent and has the
flat base change property of **Stacks 0762** (for the pullback of sheaves).  Then for every arrow
`φ : y ⟶ x` between flat objects of `𝒳` the comparison map of **Stacks 06WC**, read as a morphism
of sheaves, is an isomorphism — whether or not the morphism of schemes below `φ` is flat.

See the module documentation for the argument. -/
theorem isIso_sheafifiedRestrictComparison_of_flatObject
    (hF : IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F)
    {y x : 𝒳.val.val.obj} (hy : flatObject B S hS 𝒳.val y) (hx : flatObject B S hS 𝒳.val x)
    (φ : y ⟶ x)
    (hMy : Presheaf.IsSheaf (SmallEtale.topology E (𝒳.val.val.p.obj y).left.1
        (contains_base B E h S hS 𝒳.val.val.p y))
      (restrictModuleToSmallEtale B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids y
        (etaleTopology B) (etaleTopology_le_topology B) F).presheaf) :
    IsIso (sheafifiedRestrictComparison B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F φ
      hMy) := by
  set p := 𝒳.val.val.p
  have hfib := 𝒳.val.isFiberedInGroupoids
  -- the restriction at every object is a sheaf
  have hM : ∀ z : 𝒳.val.val.obj, Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
      (contains_base B E h S hS p z))
      (restrictModuleToSmallEtale B E h S hS p hfib z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf := fun z => (hF.1.2 z).choose
  -- the comparison along a flat arrow is an isomorphism
  have hflat : ∀ {a b : 𝒳.val.val.obj} (ψ : a ⟶ b),
      Flat (B.inclusion.map (p.map ψ).left) →
        IsIso (sheafifiedRestrictComparison B E h S hS p hfib F ψ (hM a)) := fun {a b} ψ hψ =>
    (isIso_sheafifiedRestrictModulePullbackComparison_iff B E h S hS p hfib (etaleTopology B)
      (etaleTopology_le_topology B) ψ F (hM a)).2 (hF.2 ψ hψ)
  obtain ⟨I, W, e, he, hjs, hfac⟩ := FlatFppf.exists_flat_factorization B S hS 𝒳 hy hx φ
  choose y' w κ χ π₁ π₂ hκ hπ₁ hπ₂ h₁ h₂ using hfac
  have hetale : ∀ i, Etale (B.inclusion.map (p.map (κ i)).left) := fun i =>
    etale_map_left_of_isHomLift B S hS p _ (he i) (κ i) (hκ i)
  have hcov : ∀ t : B.inclusion.obj (p.obj y).left,
      ∃ i, t ∈ Set.range (B.inclusion.map (p.map (κ i)).left) := fun t =>
    let ⟨i, hi⟩ := hjs t
    ⟨i, range_map_left_of_isHomLift B S hS p (κ i) (hκ i) hi⟩
  refine isIso_of_isIso_sheafifiedPullbackComparison_map B E h S hS p hfib y y' κ hetale hcov _
    fun i => ?_
  have hκiso := hflat (κ i) inferInstance
  have hχπ₁ : IsIso (sheafifiedRestrictComparison B E h S hS p hfib F (χ i ≫ π₁ i)
      (hM (y' i))) := by
    rwa [h₁ i]
  have hχ := @isIso_sheafifiedRestrictComparison_of_comp_left B E h S hS _ _ p hfib F _ _ _
    (χ i) (π₁ i) (hM y) (hM (w i)) (hM (y' i)) (hflat (π₁ i) (hπ₁ i)) hχπ₁
  have hχπ₂ := @isIso_sheafifiedRestrictComparison_comp B E h S hS _ _ p hfib F _ _ _
    (χ i) (π₂ i) (hM x) (hM (w i)) (hM (y' i)) (hflat (π₂ i) (hπ₂ i)) hχ
  have hκφ : IsIso (sheafifiedRestrictComparison B E h S hS p hfib F (κ i ≫ φ)
      (hM (y' i))) := by
    rwa [← h₂ i]
  exact @isIso_sheafifiedPullbackComparison_map_of_comp B E h S hS _ _ p hfib F _ _ _
    (κ i) φ (hM x) hMy (hM (y' i)) hκiso hκφ

end FlatObjects

end AlgebraicGeometry.Stack
