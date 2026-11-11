module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.InverseLimitOfAcyclicTower
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationConvergenceAcyclicCover
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Rlim

/-!
# Derived inverse limits with quasi-coherent cohomology on an algebraic space

Let `S` be a scheme, let `X` be an algebraic space over `S` and work on the small étale ringed
site of `X`.

* If `E` is an object of `D_QCoh(𝒪_X)` then the canonical map `E ⟶ R lim τ_{≥ -n} E` into a
  derived limit of the tower of canonical truncations from below is an isomorphism.
* If `(K_n)` is an inverse system of `D_QCoh(𝒪_X)` whose transition maps on cohomology sheaves
  are surjective, then the ordinary inverse limit `lim H^q(K_n)`, placed in degree zero, is
  already the derived inverse limit of the system `n ↦ H^q(K_n)`, and `lim H^q(K_n)` has no
  higher cohomology on an affine étale chart.

Both arguments are the source's.  The affine étale charts cover the small étale site, and on an
affine chart a quasi-coherent module has no higher cohomology and a surjection of quasi-coherent
modules is surjective on sections; feeding that into the site-theoretic criteria of Tags 0D6P
and 0BKY gives the three statements.  Surjectivity on sections makes each tower of sections over
an affine chart Mittag-Leffler, so its first derived inverse limit vanishes, which is the
remaining input of Tag 0BKY.

## Main results

* `AlgebraicGeometry.Space.isZero_firstDerivedLimit_sectionsSystem_of_isAffineChart`: the tower
  of sections of the degree-`q` cohomology sheaves over an affine chart has vanishing `R¹ lim`.
* `AlgebraicGeometry.Space.isIso_of_isDerivedLimit_truncGETower`: Stacks 08F6 at a free module
  universe, from its inputs on the affine étale charts.
* `AlgebraicGeometry.Space.isDerivedLimit_single_limit_homology`: Stacks 0D3E, clause (2), in the
  same form.
* `AlgebraicGeometry.Space.isZero_cohomology_limit_homology_of_isAffineChart`: Stacks 0D3E,
  clause (3), in the same form.

The tags are registered on the forms with those inputs supplied, at the module universe of the
structure rings:
`AlgebraicGeometry.Space.isIso_of_isDerivedLimit_truncGETower_ringUniverse` (08F6) and the
three clauses of 0D3E, all in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentDerivedLimitsCohomology.lean`.

## Implementation notes

*The inputs, and why they are arguments.*  The statements here are given at a free module
universe `m`, and three inputs are explicit arguments.  At the module universe `u` of the
structure rings each of them is a theorem of this library, and the registered forms of the tags
supply them there.

* `hcover` is the statement that every étale chart of `X` is covered, in the small étale
  topology, by affine étale charts.  The library has the cover-dense form of this — the
  inclusion of the affine étale charts is a special cocontinuous functor,
  `AlgebraicGeometry.Space.AffineEtale.inclusion_isSpecialCocontinuous`, Stacks 04JS — but
  `CategoryTheory.GrothendieckTopology.HasEnoughObjects` indexes its covering families in the
  morphism universe `u` of the site, whereas the covering families produced there are indexed in
  `u + 1`; the reindexed form is `AlgebraicGeometry.Space.hasEnoughObjects_isAffineChart`.
* `h03DW` and `h03DWab` are the two readings — in modules over the sections of the structure
  sheaf, and in abelian groups — of the vanishing of the higher cohomology of a quasi-coherent
  module on an affine étale chart.  That is the étale-site analogue of Serre's criterion
  (Stacks 01XB), namely Stacks 03DW, equivalently Descent, Proposition 03DX (2).  At module
  universe `u` they are `AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isAffineChart`
  and `AlgebraicGeometry.Space.isZero_rightDerived_sectionsFunctor_of_isAffineChart`.  The two
  readings are separate arguments because the two site-theoretic
  criteria used below phrase acyclicity in the two different ways and the library has no
  comparison of the derived functors of the two sections functors at this universe profile.
* `h03DWepi` is the surjectivity face of the same Stacks 03DW: a surjection of quasi-coherent
  modules is surjective on the sections over an affine étale chart.  At module universe `u` it
  is `AlgebraicGeometry.Space.epi_sectionsFunctor_map_of_isQuasicoherentOnSite`.

None of the three mentions the object `E` or the system `(K_n)` of the conclusions; each is a
statement about quasi-coherent modules and affine charts alone.

*Universes.*  The small étale site of an algebraic space has objects in `Type (u + 1)` and
morphisms in `Type u`, so its ringed site is an `AlgebraicGeometry.RingedSite.{u + 1, u, u}`;
the module universe `m` stays free, as in
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory`.  The two sheafification hypotheses and
Grothendieck abelianness of the modules are instance arguments for the same reason as there: the
library supplies them at module universe `u`, and the statements are given at a free one.

*Membership in `D_QCoh`.*  Quasi-coherence of the cohomology sheaves is carried as a hypothesis
on each cohomology sheaf rather than by placing the objects in the full subcategory
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory`, so that the statements apply to an
arbitrary object and an arbitrary inverse system of the ambient derived category; for an object
of the subcategory the hypothesis is its defining property.  A derived limit is presented by its
structural morphism to the product together with the distinguished triangle characterising it,
and the canonical map out of `E` is pinned down by requiring its composites with the product
projections to be the truncation maps.

## References

* [Stacks Project, Tag 08F6](https://stacks.math.columbia.edu/tag/08F6)
* [Stacks Project, Tag 0D3E](https://stacks.math.columbia.edu/tag/0D3E)
* [Stacks Project, Tag 0D6P](https://stacks.math.columbia.edu/tag/0D6P)
* [Stacks Project, Tag 0BKY](https://stacks.math.columbia.edu/tag/0BKY)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u m g

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-! ### The tower of sections over an affine chart -/

section Sections

/-- Every transition map of the tower of sections over an affine étale chart of the degree-`q`
cohomology sheaves of an inverse system with quasi-coherent cohomology is surjective. -/
private theorem epi_sectionsSystem_map_of_isAffineChart
    (K : ℕᵒᵖ ⥤ DerivedCategory (Modules.{u, m} B S hS F hF)) (q : ℤ)
    (hqc : ∀ n : ℕ, ((DerivedCategory.homologyFunctor
      (Modules.{u, m} B S hS F hF) q).obj (K.obj ⟨n⟩)).IsQuasicoherentOnSite)
    (hsurj : ∀ n : ℕ, Epi ((DerivedCategory.homologyFunctor
      (Modules.{u, m} B S hS F hF) q).map (K.map (homOfLE (Nat.le_succ n)).op)))
    (h03DWepi : ∀ U : SmallEtale B S hS F, IsAffineChart B S hS F U →
      ∀ M N : Modules.{u, m} B S hS F hF, M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
      ∀ f : M ⟶ N, Epi f →
        Epi ((Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
          (smallEtaleRingedSite B S hS F hF) U).map f))
    (U : SmallEtale B S hS F) (hU : IsAffineChart B S hS F U) {i j : ℕᵒᵖ} (f : i ⟶ j) :
    Epi ((Stacks.Cohomology.SiteInverseLimits.sectionsSystem
      (smallEtaleRingedSite B S hS F hF)
      (K ⋙ DerivedCategory.homologyFunctor (Modules.{u, m} B S hS F hF) q) U).map f) := by
  set A := Stacks.Cohomology.SiteInverseLimits.sectionsSystem
    (smallEtaleRingedSite B S hS F hF)
    (K ⋙ DerivedCategory.homologyFunctor (Modules.{u, m} B S hS F hF) q) U with hA
  have hstep (n : ℕ) : Epi (A.map (homOfLE (Nat.le_succ n)).op) :=
    h03DWepi U hU _ _ (hqc (n + 1)) (hqc n) _ (hsurj n)
  have htrans (a b : ℕ) (hab : b ≤ a) : Epi (A.map (homOfLE hab).op) := by
    induction a, hab using Nat.le_induction with
    | base => simpa using (show Epi (𝟙 (A.obj (op b))) from inferInstance)
    | @succ a hab ih =>
      have hcomp : (homOfLE (hab.trans (Nat.le_succ a))).op =
          (homOfLE (Nat.le_succ a)).op ≫ (homOfLE hab).op := Subsingleton.elim _ _
      rw [hcomp, Functor.map_comp]
      exact epi_comp' (hstep a) ih
  have hle : j.unop ≤ i.unop := f.unop.le
  have hf : f = (homOfLE hle).op := Subsingleton.elim _ _
  rw [hf]
  exact htrans i.unop j.unop hle

/-- **The tower of sections over an affine étale chart is Mittag-Leffler.** For an inverse system
in the derived category of `𝒪_X`-modules with quasi-coherent cohomology and surjective transition
maps on cohomology, the tower of sections over an affine étale chart of the degree-`q` cohomology
sheaves has vanishing first derived inverse limit.

This is the remaining hypothesis of Tag 0BKY; the surjectivity of the maps on sections is the
argument `h03DWepi`, and a surjective tower of abelian groups is Mittag-Leffler. -/
theorem isZero_firstDerivedLimit_sectionsSystem_of_isAffineChart
    (K : ℕᵒᵖ ⥤ DerivedCategory (Modules.{u, m} B S hS F hF)) (q : ℤ)
    (hqc : ∀ n : ℕ, ((DerivedCategory.homologyFunctor
      (Modules.{u, m} B S hS F hF) q).obj (K.obj ⟨n⟩)).IsQuasicoherentOnSite)
    (hsurj : ∀ n : ℕ, Epi ((DerivedCategory.homologyFunctor
      (Modules.{u, m} B S hS F hF) q).map (K.map (homOfLE (Nat.le_succ n)).op)))
    (h03DWepi : ∀ U : SmallEtale B S hS F, IsAffineChart B S hS F U →
      ∀ M N : Modules.{u, m} B S hS F hF, M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
      ∀ f : M ⟶ N, Epi f →
        Epi ((Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
          (smallEtaleRingedSite B S hS F hF) U).map f))
    (U : SmallEtale B S hS F) (hU : IsAffineChart B S hS F U) :
    IsZero (Rlim.firstDerivedLimit (Stacks.Cohomology.SiteInverseLimits.sectionsSystem
      (smallEtaleRingedSite B S hS F hF)
      (K ⋙ DerivedCategory.homologyFunctor (Modules.{u, m} B S hS F hF) q) U)) := by
  set A := Stacks.Cohomology.SiteInverseLimits.sectionsSystem
    (smallEtaleRingedSite B S hS F hF)
    (K ⋙ DerivedCategory.homologyFunctor (Modules.{u, m} B S hS F hF) q) U with hA
  have hML : (A ⋙ forget AddCommGrpCat.{m}).IsMittagLeffler :=
    Functor.isMittagLeffler_of_surjective _ fun _ _ f =>
      (AddCommGrpCat.epi_iff_surjective _).1
        (epi_sectionsSystem_map_of_isAffineChart B S hS F hF K q hqc hsurj h03DWepi U hU f)
  obtain ⟨RF, α, hRF, -, -, hMLzero, -, -, -, -, -, hAny, -⟩ :=
    Rlim.lim_hasRightDerivedFunctor_and_computations.{m}
  obtain ⟨e⟩ := hAny RF α hRF A
  exact (hMLzero A hML).of_iso e.symm

end Sections

/-! ### Convergence of the truncation tower -/

/-- **Stacks Project, Tag 08F6, at a free module universe.** Let `S` be a scheme, let `X` be an
algebraic space over `S` and let `E` be an object of `D_QCoh(𝒪_X)`. Then the canonical map from `E`
to a derived limit `L` of the tower `n ↦ τ_{≥ -n} E` of canonical truncations from below is an
isomorphism.

The derived limit is presented by its structural morphism `p` to the product of the tower and
the distinguished triangle `hL` characterising it; the map `c` out of `E` is the canonical one
because its composites with the product projections are required to be the truncation maps.

This is Spaltenstein's local criterion in the form
`Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic`, Tag 0D6P with
`d = 0`, applied on the small étale site of `X`: the affine étale charts cover it, which is the
argument `hcover`, and a quasi-coherent module has no higher cohomology on an affine chart,
which is the argument `h03DW`.  The registered form, with both supplied at the module universe of
the structure rings, is
`AlgebraicGeometry.Space.isIso_of_isDerivedLimit_truncGETower_ringUniverse`, in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentDerivedLimitsCohomology.lean`. -/
theorem isIso_of_isDerivedLimit_truncGETower
    [EnoughInjectives (Modules.{u, m} B S hS F hF)]
    (E : DerivedCategory (Modules.{u, m} B S hS F hF))
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, m} B S hS F hF) q).obj E).IsQuasicoherentOnSite)
    (hcover : (smallEtaleRingedSite B S hS F hF).J.HasEnoughObjects
      (IsAffineChart B S hS F))
    (h03DW : ∀ U : SmallEtale B S hS F, IsAffineChart B S hS F U →
      ∀ M : Modules.{u, m} B S hS F hF, M.IsQuasicoherentOnSite → ∀ p : ℕ, 0 < p →
        IsZero (((SheafOfModules.evaluation.{m}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
          (op U)).rightDerived p).obj M))
    [HasProduct fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (Modules.{u, m} B S hS F hF) E).obj ⟨n⟩]
    (L : DerivedCategory (Modules.{u, m} B S hS F hF))
    (c : E ⟶ L)
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (Modules.{u, m} B S hS F hF) E).obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (Modules.{u, m} B S hS F hF) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hL : Triangle.mk p (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
        (Modules.{u, m} B S hS F hF) E).obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
          (Modules.{u, m} B S hS F hF) E).obj ⟨n⟩) (n + 1) ≫
          (Stacks.DerivedLimit.truncGETower
            (Modules.{u, m} B S hS F hF) E).map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (Modules.{u, m} B S hS F hF)))
    (hc : ∀ n : ℕ, c ≫ p ≫ Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (Modules.{u, m} B S hS F hF) E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c :=
  Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) E
    (IsAffineChart B S hS F) hcover
    (fun V hV r hr i => h03DW V hV _ (hE i) r hr)
    L c p δ hL hc

/-! ### The inverse limit of the cohomology sheaves -/

section Limits

variable [IsGrothendieckAbelian.{g} (Modules.{u, m} B S hS F hF)]

/-- **Stacks Project, Tag 0D3E, clause (2), at a free module universe.** Let `(K_n)` be an inverse
system of `D_QCoh(𝒪_X)` on an algebraic space `X` whose transition maps `H^q(K_{n+1}) ⟶ H^q(K_n)` on
cohomology sheaves are surjective. Then `R lim H^q(K_n) = lim H^q(K_n)`: the ordinary inverse limit
of the degree-`q` cohomology sheaves, placed in degree zero, is a derived inverse limit of the
system of those sheaves.

This is the first conclusion of Tag 0BKY,
`Stacks.Cohomology.SiteInverseLimits.isDerivedLimit_single_limit_of_acyclic_cover`, on the small
étale site of `X`. -/
theorem isDerivedLimit_single_limit_homology
    (K : ℕᵒᵖ ⥤ DerivedCategory (Modules.{u, m} B S hS F hF))
    (hqc : ∀ (n : ℕ) (q : ℤ), ((DerivedCategory.homologyFunctor
      (Modules.{u, m} B S hS F hF) q).obj (K.obj ⟨n⟩)).IsQuasicoherentOnSite)
    (hsurj : ∀ (n : ℕ) (q : ℤ), Epi ((DerivedCategory.homologyFunctor
      (Modules.{u, m} B S hS F hF) q).map (K.map (homOfLE (Nat.le_succ n)).op)))
    (hcover : (smallEtaleRingedSite B S hS F hF).J.HasEnoughObjects
      (IsAffineChart B S hS F))
    (h03DWab : ∀ U : SmallEtale B S hS F, IsAffineChart B S hS F U →
      ∀ M : Modules.{u, m} B S hS F hF, M.IsQuasicoherentOnSite → ∀ p : ℕ, 0 < p →
        IsZero (((Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
          (smallEtaleRingedSite B S hS F hF) U).rightDerived p).obj M))
    (h03DWepi : ∀ U : SmallEtale B S hS F, IsAffineChart B S hS F U →
      ∀ M N : Modules.{u, m} B S hS F hF, M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
      ∀ f : M ⟶ N, Epi f →
        Epi ((Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
          (smallEtaleRingedSite B S hS F hF) U).map f))
    (q : ℤ) :
    ∃ h : HasProduct (fun n : ℕ =>
        ((K ⋙ DerivedCategory.homologyFunctor (Modules.{u, m} B S hS F hF) q) ⋙
          DerivedCategory.singleFunctor (Modules.{u, m} B S hS F hF) 0).obj ⟨n⟩),
      @IsDerivedLimit (DerivedCategory (Modules.{u, m} B S hS F hF)) _ _ _ _ _ _
        ((K ⋙ DerivedCategory.homologyFunctor (Modules.{u, m} B S hS F hF) q) ⋙
          DerivedCategory.singleFunctor (Modules.{u, m} B S hS F hF) 0) h
        ((DerivedCategory.singleFunctor (Modules.{u, m} B S hS F hF) 0).obj
          (limit (K ⋙ DerivedCategory.homologyFunctor
            (Modules.{u, m} B S hS F hF) q))) :=
  Stacks.Cohomology.SiteInverseLimits.isDerivedLimit_single_limit_of_acyclic_cover
    (smallEtaleRingedSite B S hS F hF)
    (K ⋙ DerivedCategory.homologyFunctor (Modules.{u, m} B S hS F hF) q)
    (IsAffineChart B S hS F) hcover
    (fun V hV n r hr => h03DWab V hV _ (hqc n q) r hr)
    (fun V hV => isZero_firstDerivedLimit_sectionsSystem_of_isAffineChart
      B S hS F hF K q (fun n => hqc n q) (fun n => hsurj n q) h03DWepi V hV)

/-- **Stacks Project, Tag 0D3E, clause (3), at a free module universe.** Under the same hypotheses,
for every affine étale chart `U` of `X` and every `p > 0` we have `H^p(U, lim H^q(K_n)) = 0`.

This is the second conclusion of Tag 0BKY,
`Stacks.Cohomology.SiteInverseLimits.isZero_cohomology_limit_of_acyclic_cover`, on the small
étale site of `X`.  The source states the vanishing for an affine open of `X`; every affine open
is an affine object of the small étale site, and the statement is given for all of them, as the
source's own proof does. -/
theorem isZero_cohomology_limit_homology_of_isAffineChart
    (K : ℕᵒᵖ ⥤ DerivedCategory (Modules.{u, m} B S hS F hF))
    (hqc : ∀ (n : ℕ) (q : ℤ), ((DerivedCategory.homologyFunctor
      (Modules.{u, m} B S hS F hF) q).obj (K.obj ⟨n⟩)).IsQuasicoherentOnSite)
    (hsurj : ∀ (n : ℕ) (q : ℤ), Epi ((DerivedCategory.homologyFunctor
      (Modules.{u, m} B S hS F hF) q).map (K.map (homOfLE (Nat.le_succ n)).op)))
    (hcover : (smallEtaleRingedSite B S hS F hF).J.HasEnoughObjects
      (IsAffineChart B S hS F))
    (h03DWab : ∀ U : SmallEtale B S hS F, IsAffineChart B S hS F U →
      ∀ M : Modules.{u, m} B S hS F hF, M.IsQuasicoherentOnSite → ∀ p : ℕ, 0 < p →
        IsZero (((Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
          (smallEtaleRingedSite B S hS F hF) U).rightDerived p).obj M))
    (h03DWepi : ∀ U : SmallEtale B S hS F, IsAffineChart B S hS F U →
      ∀ M N : Modules.{u, m} B S hS F hF, M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
      ∀ f : M ⟶ N, Epi f →
        Epi ((Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
          (smallEtaleRingedSite B S hS F hF) U).map f))
    (q : ℤ) (U : SmallEtale B S hS F) (hU : IsAffineChart B S hS F U)
    (p : ℕ) (hp : 0 < p) :
    IsZero (((Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
      (smallEtaleRingedSite B S hS F hF) U).rightDerived p).obj
      (limit (K ⋙ DerivedCategory.homologyFunctor
        (Modules.{u, m} B S hS F hF) q))) :=
  Stacks.Cohomology.SiteInverseLimits.isZero_cohomology_limit_of_acyclic_cover
    (smallEtaleRingedSite B S hS F hF)
    (K ⋙ DerivedCategory.homologyFunctor (Modules.{u, m} B S hS F hF) q)
    (IsAffineChart B S hS F) hcover
    (fun V hV n r hr => h03DWab V hV _ (hqc n q) r hr)
    (fun V hV => isZero_firstDerivedLimit_sectionsSystem_of_isAffineChart
      B S hS F hF K q (fun n => hqc n q) (fun n => hsurj n q) h03DWepi V hV)
    U hU p hp

end Limits

end AlgebraicGeometry.Space

end
