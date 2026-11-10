module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.AcyclicCoveringFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.InverseLimitOfAcyclicTower
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.AcyclicObject

/-! # Cohomology of a derived inverse limit over an acyclic covering family, on a large site

`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedLimit/AcyclicCoveringFamily.lean` proves the
content of [Stacks, Tag 0A09] for a ringed site `X : RingedSite.{u, u, u}`, whose objects,
morphisms, structure rings and modules share one universe.  The argument does not use that: what
it uses is the sheafification locality
`PresheafOfModules.isIso_sheafification_map_of_isIso_evaluation`, stated for a sheaf of rings and
abelian groups at one universe `w`, the Milnor sequence of Tag 0BKX and the comparison square of
Tag 0BKW, all of which are stated at arbitrary universes of the objects and morphisms of the
site.  This file runs the same argument for `X : RingedSite.{u, v, w}`, with the modules at the
universe `w` of the structure rings.

The case that needs it is the small étale site of an algebraic space, whose objects live in
`Type (u + 1)` and whose morphisms live in `Type u`; that is where [Stacks, Tag 0D3E] applies
Tag 0A09.

The vanishing of `R¹lim` is stated in terms of
`Stacks.Cohomology.SiteInverseLimits.sectionsFunctor`, the sections over an object with the
module structure forgotten, which is defined at every universe profile.

## Main results

* `Stacks.Cohomology.DerivedLimitAcyclic.LargeSite.isIso_cohomologyLimitComparison`: the
  comparison from the degree-`q` cohomology sheaf of a derived limit to the inverse limit of the
  degree-`q` cohomology sheaves is an isomorphism.
* `Stacks.Cohomology.DerivedLimitAcyclic.LargeSite.isLimit_cohomology_of_isDerivedLimit`: the
  content of Tag 0A09 on such a site, with Tag 0BKZ supplied, and the product of the system an
  instance argument.

## References

* [Stacks Project, Tag 0A09](https://stacks.math.columbia.edu/tag/0A09)
* [Stacks Project, Tag 0BKW](https://stacks.math.columbia.edu/tag/0BKW)
* [Stacks Project, Tag 0BKX](https://stacks.math.columbia.edu/tag/0BKX)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry

universe u v w g

namespace Stacks.Cohomology.DerivedLimitAcyclic.LargeSite

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.HypercohomologyEdge
open Stacks.DerivedLimit
open Stacks.Cohomology.DerivedLimitAcyclic (cohomologyPresheafComparison
  isIso_evaluation_cohomologyPresheafComparison cokernelInverseSystemDifferenceIso
  mapCokernelInverseSystemDifferenceIso isIso_map_unit_app)

variable (X : RingedSite.{u, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- The system of degree-`q` hypercohomology modules over `U` of an inverse system of objects
of the derived category of `O`-modules. -/
abbrev hypercohomologySystem (U : X.C)
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (q : ℤ) :
    ℕᵒᵖ ⥤ ModuleCat.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) :=
  K ⋙ derivedSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U ⋙
    DerivedCategory.homologyFunctor
      (ModuleCat.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) q

/-- Where the hypercohomology edge morphism is invertible at every term of the system, the
vanishing of the first derived inverse limit of the sections of the cohomology sheaves transfers
to the vanishing of the cokernel of the difference map on hypercohomology.

This is what feeds the Milnor sequence of Tag 0BKX: that sequence presents `R¹lim` of the
hypercohomology system as this cokernel, so the hypothesis of Tag 0A09, which is about sections
of the cohomology sheaves, reaches it only across the edge morphism. -/
lemma isZero_cokernel_difference_hypercohomologySystem (U : X.C)
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (q : ℤ)
    (hedge : ∀ n : ℕ,
      IsIso ((hypercohomologyEdge (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U q).app
        (K.obj ⟨n⟩)))
    (hlimOne : IsZero (Rlim.firstDerivedLimit
      (K ⋙ DerivedCategory.homologyFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q ⋙
        Stacks.Cohomology.SiteInverseLimits.sectionsFunctor X U))) :
    IsZero (cokernel (inverseSystemDifference (hypercohomologySystem X U K q))) := by
  let G := forget₂ (ModuleCat.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))
    AddCommGrpCat.{w}
  let A := K ⋙ DerivedCategory.homologyFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q ⋙
    Stacks.Cohomology.SiteInverseLimits.sectionsFunctor X U
  let α := Functor.whiskerLeft K
    (Functor.whiskerRight (hypercohomologyEdge (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U q) G)
  have hα (n : ℕᵒᵖ) : IsIso (α.app n) := by
    have := hedge n.unop
    dsimp only [α, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  let e : hypercohomologySystem X U K q ⋙ G ≅ A :=
    NatIso.ofComponents (fun n ↦ have := hα n; asIso (α.app n)) fun f ↦ α.naturality f
  have hzero :
      IsZero (G.obj (cokernel (inverseSystemDifference (hypercohomologySystem X U K q)))) :=
    hlimOne.of_iso (mapCokernelInverseSystemDifferenceIso (hypercohomologySystem X U K q) G ≪≫
      cokernelInverseSystemDifferenceIso e ≪≫ cokernelIsoOfEq (Rlim.delta_eq_lift A).symm)
  refine (IsZero.iff_id_eq_zero _).2 (G.map_injective ?_)
  rw [G.map_id, G.map_zero]
  exact (IsZero.iff_id_eq_zero _).1 hzero

/-- Sections over `U` of the comparison from the degree-`q` cohomology presheaf of a derived
limit to the limit of the degree-`q` cohomology presheaves of the system is invertible, as soon
as the hypercohomology edge morphisms in degree `q - 1` are and the first derived inverse limit
of the degree-`(q-1)` sections vanishes.

The Milnor sequence of Tag 0BKX identifies these sections with the limit of the hypercohomology
modules up to the `R¹lim` term, and that term is the cokernel killed by
`isZero_cokernel_difference_hypercohomologySystem`. -/
lemma isIso_evaluation_cohomologyLimitMap (U : X.C)
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang
          (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (q : ℤ)
    (hedge : ∀ n : ℕ,
      IsIso ((hypercohomologyEdge (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U (q - 1)).app
        (K.obj ⟨n⟩)))
    (hlimOne : IsZero (Rlim.firstDerivedLimit
      (K ⋙ DerivedCategory.homologyFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (q - 1) ⋙
        Stacks.Cohomology.SiteInverseLimits.sectionsFunctor X U)))
    (a : (derivedSectionsPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        DerivedCategory.homologyFunctor
          (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q).obj L ⟶
      limit (K ⋙ derivedSectionsPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        DerivedCategory.homologyFunctor
          (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q))
    (ha : ∀ n : ℕ, a ≫ limit.π _ ⟨n⟩ =
      (derivedSectionsPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        DerivedCategory.homologyFunctor
          (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q).map
          (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) :
    IsIso ((PresheafOfModules.evaluation
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op U)).map a) := by
  let RG := derivedSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  let P := derivedSectionsPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
    DerivedCategory.homologyFunctor
      (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q
  let E := PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op U)
  let H := DerivedCategory.homologyFunctor
    (ModuleCat.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) q
  obtain ⟨hprod, ar, br, htr, har, ep, i, r, hz, hep, hi, hseq, hr⟩ :=
    exists_milnor_shortExact_derivedSections
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U K L p hp q
  have : IsIso r := hseq.isIso_g_iff.mpr
    (isZero_cokernel_difference_hypercohomologySystem X U K (q - 1) hedge hlimOne)
  let e := sectionsEvaluationIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U q
  let eK : (K ⋙ P) ⋙ E ≅ (K ⋙ RG) ⋙ H := Functor.isoWhiskerLeft K e
  let t : E.obj (limit (K ⋙ P)) ≅ limit ((K ⋙ RG) ⋙ H) :=
    preservesLimitIso E (K ⋙ P) ≪≫ HasLimit.isoOfNatIso eK
  have ht : E.map a ≫ t.hom = e.hom.app L ≫ r := by
    refine limit.hom_ext fun n ↦ ?_
    obtain ⟨n⟩ := n
    simp only [t, Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π,
      preservesLimitIso_hom_π_assoc]
    rw [← Category.assoc, ← E.map_comp, ha n, hr n]
    exact e.hom.naturality (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)
  have : IsIso (E.map a ≫ t.hom) := by
    rw [ht]
    infer_instance
  exact IsIso.of_isIso_comp_right (E.map a) t.hom

/-- The degree-`q` cohomology presheaf functor: the degree-`q` cohomology of derived sections
taken over every object of the site at once. -/
abbrev cohomologyPresheafFunctor (q : ℤ) :
    DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj :=
  derivedSectionsPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
    DerivedCategory.homologyFunctor
      (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q

/-- The comparison from the degree-`q` cohomology presheaf of a derived limit to the underlying
presheaf of the inverse limit of the degree-`q` cohomology sheaves, assembled from a cone map `a`
into the limit of the cohomology presheaves and the sheafification comparison. -/
def limitComparisonPresheaf
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (q : ℤ)
    (a : (cohomologyPresheafFunctor X q).obj L ⟶ limit (K ⋙ cohomologyPresheafFunctor X q)) :
    (cohomologyPresheafFunctor X q).obj L ⟶
      (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
        (limit (K ⋙ DerivedCategory.homologyFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q)) :=
  a ≫ limMap (Functor.whiskerLeft K
        (cohomologyPresheafComparison (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q) :
      K ⋙ cohomologyPresheafFunctor X q ⟶
        (K ⋙ DerivedCategory.homologyFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q) ⋙
          SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ≫
    (preservesLimitIso (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (K ⋙ DerivedCategory.homologyFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q)).inv

/-- Sections over a member of the covering collection of the comparison
`limitComparisonPresheaf` are invertible. All three of its factors are: the cone map by the
Milnor sequence, the sheafification comparison by Tag 0BKZ, and the product comparison because
the forgetful functor preserves limits. -/
theorem isIso_evaluation_limitComparisonPresheaf
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang
          (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (B : ObjectProperty X.C)
    (hedge : ∀ U, B U → ∀ (m : ℤ) (n : ℕ),
      IsIso ((hypercohomologyEdge (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U m).app
        (K.obj ⟨n⟩)))
    (hlimOne : ∀ U, B U → ∀ m : ℤ,
      IsZero (Rlim.firstDerivedLimit
        (K ⋙ DerivedCategory.homologyFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m ⋙
          Stacks.Cohomology.SiteInverseLimits.sectionsFunctor X U)))
    (q : ℤ)
    (a : (cohomologyPresheafFunctor X q).obj L ⟶ limit (K ⋙ cohomologyPresheafFunctor X q))
    (ha : ∀ n : ℕ, a ≫ limit.π _ ⟨n⟩ =
      (cohomologyPresheafFunctor X q).map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n))
    (U : X.C) (hU : B U) :
    IsIso ((PresheafOfModules.evaluation
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op U)).map
      (limitComparisonPresheaf X K L q a)) := by
  let E := PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op U)
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q
  let ηK : K ⋙ cohomologyPresheafFunctor X q ⟶
      (K ⋙ H) ⋙ SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
    Functor.whiskerLeft K
      (cohomologyPresheafComparison (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q)
  have hA : IsIso (E.map a) :=
    isIso_evaluation_cohomologyLimitMap X U K L p hp q
      (fun n ↦ hedge U hU (q - 1) n) (hlimOne U hU (q - 1)) a ha
  have hW : IsIso (Functor.whiskerRight ηK E) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    exact isIso_evaluation_cohomologyPresheafComparison
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U q (K.obj n)
      (hedge U hU q n.unop)
  have hM : IsIso (E.map (limMap ηK)) :=
    Stacks.HomologyComparison.isIso_map_limMap_of_isIso_whiskerRight E ηK
  have hsplit : E.map (limitComparisonPresheaf X K L q a) =
      E.map a ≫ E.map (limMap ηK) ≫
        E.map (preservesLimitIso
          (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (K ⋙ H)).inv := by
    rw [show limitComparisonPresheaf X K L q a =
        a ≫ limMap ηK ≫
          (preservesLimitIso
            (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (K ⋙ H)).inv
        from rfl,
      E.map_comp, E.map_comp]
  change IsIso (E.map (limitComparisonPresheaf X K L q a))
  rw [hsplit]
  exact IsIso.comp_isIso' hA (IsIso.comp_isIso' hM inferInstance)

/-- The sheafification of `limitComparisonPresheaf` is an isomorphism: it is invertible on
sections over every member of a collection covering the site. -/
theorem isIso_sheafification_map_limitComparisonPresheaf
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang
          (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (B : ObjectProperty X.C) (hB : X.J.HasEnoughObjects B)
    (hedge : ∀ U, B U → ∀ (m : ℤ) (n : ℕ),
      IsIso ((hypercohomologyEdge (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U m).app
        (K.obj ⟨n⟩)))
    (hlimOne : ∀ U, B U → ∀ m : ℤ,
      IsZero (Rlim.firstDerivedLimit
        (K ⋙ DerivedCategory.homologyFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m ⋙
          Stacks.Cohomology.SiteInverseLimits.sectionsFunctor X U)))
    (q : ℤ)
    (a : (cohomologyPresheafFunctor X q).obj L ⟶ limit (K ⋙ cohomologyPresheafFunctor X q))
    (ha : ∀ n : ℕ, a ≫ limit.π _ ⟨n⟩ =
      (cohomologyPresheafFunctor X q).map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) :
    IsIso ((PresheafOfModules.sheafification
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
      (limitComparisonPresheaf X K L q a)) :=
  PresheafOfModules.isIso_sheafification_map_of_isIso_evaluation hB _
    fun U hU ↦ isIso_evaluation_limitComparisonPresheaf X K L p hp B hedge hlimOne q a ha U hU

/-- The comparison from the degree-`q` cohomology sheaf of a derived limit to the inverse limit
of the degree-`q` cohomology sheaves of the system is an isomorphism, as soon as the
hypercohomology edge morphisms over a covering collection are invertible and the first derived
inverse limits of the sections there vanish.

This is the content of Tag 0A09. The comparison of cohomology presheaves is an isomorphism after
sheafification, and the Tag 0BKW square then transports that to the comparison of cohomology
sheaves, the sheafification of the unit factor being invertible because the counit of
sheafification is. -/
theorem isIso_cohomologyLimitComparison
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang
          (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (B : ObjectProperty X.C) (hB : X.J.HasEnoughObjects B)
    (hedge : ∀ U, B U → ∀ (m : ℤ) (n : ℕ),
      IsIso ((hypercohomologyEdge (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U m).app
        (K.obj ⟨n⟩)))
    (hlimOne : ∀ U, B U → ∀ m : ℤ,
      IsZero (Rlim.firstDerivedLimit
        (K ⋙ DerivedCategory.homologyFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m ⋙
          Stacks.Cohomology.SiteInverseLimits.sectionsFunctor X U)))
    (q : ℤ)
    (a : (cohomologyPresheafFunctor X q).obj L ⟶ limit (K ⋙ cohomologyPresheafFunctor X q))
    (b : (DerivedCategory.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).obj L ⟶
      limit (K ⋙ DerivedCategory.homologyFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q))
    (ha : ∀ n : ℕ, a ≫ limit.π _ ⟨n⟩ =
      (cohomologyPresheafFunctor X q).map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n))
    (hb : ∀ n : ℕ, b ≫ limit.π _ ⟨n⟩ =
      (DerivedCategory.homologyFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).map
        (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) :
    IsIso b := by
  let P := cohomologyPresheafFunctor X q
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q
  let F := SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let S := PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
  let η := cohomologyPresheafComparison (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q
  let ηK : K ⋙ P ⟶ (K ⋙ H) ⋙ F := Functor.whiskerLeft K η
  let t := preservesLimitIso F (K ⋙ H)
  have hfac : η.app L ≫ F.map b = limitComparisonPresheaf X K L q a := by
    rw [show limitComparisonPresheaf X K L q a = a ≫ limMap ηK ≫ t.inv from rfl]
    refine (cancel_mono t.hom).1 (limit.hom_ext fun n ↦ ?_)
    obtain ⟨n⟩ := n
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [preservesLimitIso_hom_π, ← F.map_comp, hb n, limMap_π, ← Category.assoc, ha n]
    exact (η.naturality (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)).symm
  have hunit : IsIso (S.map (η.app L)) := by
    rw [show S.map (η.app L) =
        S.map (adj.unit.app (P.obj L)) ≫
          S.map (F.map
            ((sheafificationCohomologyPresheafIso
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q).hom.app L)) from
      S.map_comp _ _]
    have h₁ : IsIso (S.map (adj.unit.app (P.obj L))) :=
      isIso_map_unit_app adj (P.obj L) inferInstance
    have h₂ : IsIso (S.map (F.map
        ((sheafificationCohomologyPresheafIso
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q).hom.app L))) := inferInstance
    exact IsIso.comp_isIso' h₁ h₂
  have hcomp : IsIso (S.map (η.app L) ≫ S.map (F.map b)) := by
    rw [← S.map_comp, hfac]
    exact isIso_sheafification_map_limitComparisonPresheaf X K L p hp B hB hedge hlimOne q a ha
  have hFb : IsIso (S.map (F.map b)) := IsIso.of_isIso_comp_left (S.map (η.app L)) _
  have hFb' : IsIso (((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
      PresheafOfModules.restrictScalars (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)) ⋙
        S).map b) := hFb
  have e : (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
      PresheafOfModules.restrictScalars (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)) ⋙
        PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) ≅
          𝟭 _ :=
    NatIso.ofComponents (fun M ↦ asIso (adj.counit.app M)) fun f ↦ adj.counit.naturality f
  exact (NatIso.isIso_map_iff e b).1 hFb'

/-- **Stacks Project Tag 0A09, modulo Tag 0BKZ.** Cohomology commutes with a derived inverse
limit if there is a covering collection on which all positive cohomology of the cohomology
sheaves vanishes and the towers of their sections have vanishing first derived inverse limit.

The hypothesis `h0BKZ` is the statement of Tag 0BKZ: the hypercohomology edge morphism is
invertible on an object of the covering collection as soon as the cohomology sheaves are acyclic
there. It is the only input this proof takes beyond the hypotheses of Tag 0A09 itself, and
`Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover` discharges
it; the tag therefore sits on
`Stacks.Cohomology.DerivedLimitAcyclic.isLimit_cohomology_of_isDerivedLimit_of_acyclic_cover`. -/
theorem cohomology_isLimit_of_isDerivedLimit_of_acyclic_cover
    [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (hL : IsDerivedLimit K L)
    (B : ObjectProperty X.C)
    (hB : X.J.HasEnoughObjects B)
    (hacyclic : ∀ U, B U → ∀ q : ℤ, ∀ n : ℕ, ∀ r : ℕ, 0 < r →
      IsZero (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (op U)).rightDerived r).obj
        ((DerivedCategory.homologyFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).obj
          (K.obj ⟨n⟩))))
    (hlimOne : ∀ U, B U → ∀ q : ℤ,
      IsZero (Rlim.firstDerivedLimit
        (K ⋙ DerivedCategory.homologyFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q ⋙
          Stacks.Cohomology.SiteInverseLimits.sectionsFunctor X U)))
    (h0BKZ : ∀ M : DerivedCategory
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)), ∀ U, B U →
      (∀ V, B V → ∀ r : ℕ, 0 < r → ∀ m : ℤ,
        IsZero (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (op V)).rightDerived r).obj
          ((DerivedCategory.homologyFunctor
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m).obj M))) →
      ∀ m : ℤ, IsIso ((hypercohomologyEdge (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U m).app M))
    (q : ℤ) :
    ∃ p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩,
      (∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
        Triangle.mk p (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
              K.map (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang
            (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) ∧
      ∃ τ : (Functor.const ℕᵒᵖ).obj
          ((DerivedCategory.homologyFunctor
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).obj L) ⟶
          K ⋙ DerivedCategory.homologyFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q,
        (∀ n : ℕ, τ.app ⟨n⟩ =
          (DerivedCategory.homologyFunctor
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).map
            (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) ∧
        Nonempty (IsLimit (Cone.mk _ τ)) := by
  obtain ⟨p, δ, hδ⟩ := hL
  have hedge : ∀ U, B U → ∀ (m : ℤ) (n : ℕ),
      IsIso ((hypercohomologyEdge (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U m).app
        (K.obj ⟨n⟩)) := fun U hU m n ↦
    h0BKZ (K.obj ⟨n⟩) U hU (fun V hV r hr i ↦ hacyclic V hV i n r hr) m
  obtain ⟨a, b, c, ha, hb, hc, hsquare⟩ :=
    Stacks.Cohomology.DerivedLimitDiagram.cohomologyDerivedLimitDiagram X K L p ⟨δ, hδ⟩ q
  have hbIso : IsIso b :=
    isIso_cohomologyLimitComparison X K L p ⟨δ, hδ⟩ B hB hedge hlimOne q a b ha hb
  refine ⟨p, ⟨δ, hδ⟩, (Functor.const ℕᵒᵖ).map b ≫ (limit.cone (K ⋙
    DerivedCategory.homologyFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q)).π, fun n ↦ hb n, ?_⟩
  exact ⟨IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (asIso b).symm fun n ↦ by simp)⟩

/-- **The content of Stacks Tag 0A09 on a ringed site whose objects may live above its
morphisms.**  Cohomology commutes with a derived inverse limit if there is a class of objects
covering the site on which all positive cohomology of the cohomology sheaves vanishes and the
towers of their sections have vanishing first derived inverse limit.  Tag 0BKZ,
`Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover`, is
supplied; the product of the system, which the derived-limit triangle names, is an instance
argument. -/
theorem isLimit_cohomology_of_isDerivedLimit
    [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (hL : IsDerivedLimit K L)
    (B : ObjectProperty X.C)
    (hB : X.J.HasEnoughObjects B)
    (hacyclic : ∀ U, B U → ∀ q : ℤ, ∀ n : ℕ, ∀ r : ℕ, 0 < r →
      IsZero (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (op U)).rightDerived r).obj
        ((DerivedCategory.homologyFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).obj
          (K.obj ⟨n⟩))))
    (hlimOne : ∀ U, B U → ∀ q : ℤ,
      IsZero (Rlim.firstDerivedLimit
        (K ⋙ DerivedCategory.homologyFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q ⋙
          Stacks.Cohomology.SiteInverseLimits.sectionsFunctor X U)))
    (q : ℤ) :
    ∃ p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩,
      (∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
        Triangle.mk p (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
              K.map (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang
            (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) ∧
      ∃ τ : (Functor.const ℕᵒᵖ).obj
          ((DerivedCategory.homologyFunctor
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).obj L) ⟶
          K ⋙ DerivedCategory.homologyFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q,
        (∀ n : ℕ, τ.app ⟨n⟩ =
          (DerivedCategory.homologyFunctor
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).map
            (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) ∧
        Nonempty (IsLimit (Cone.mk _ τ)) :=
  cohomology_isLimit_of_isDerivedLimit_of_acyclic_cover X K L hL B hB hacyclic hlimOne
    (fun M U hU hvan m ↦
      isIso_hypercohomologyEdge_app_of_acyclic_cover
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U M B hB hvan hU m) q

end Stacks.Cohomology.DerivedLimitAcyclic.LargeSite

end
