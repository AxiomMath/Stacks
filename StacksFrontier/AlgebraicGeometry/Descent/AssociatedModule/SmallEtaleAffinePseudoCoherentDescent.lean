module

public import StacksFrontier.AlgebraicGeometry.AmpleEventualGeneration.Affine
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineSchemeTruncationLiftFree
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleBoundedAbove
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleConePropagationQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedConservativity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedFiniteTypeDescent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.TopCohomologyFinitenessSites
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.SliceApproximationBridge
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.TopDegreeInduction

/-!
# Clause (2) ⇒ (1) of Stacks 08HE on an affine scheme, for quasi-coherent cohomology

Let `S` be a scheme contained in a big étale site, let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the
comparison of Stacks 08H7, and let `E` be an object of `D(𝒪_S)` whose cohomology sheaves are
quasi-coherent.  **On an affine `S`, if `ε^*E` is `m`-pseudo-coherent then so is `E`.**

This is the file that *runs* the induction
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_descentStep`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/TopDegreeInduction.lean`).
The predicate `P` the recursion carries is

> `P F` := "`ε^*F` is `m`-pseudo-coherent" **and** "every cohomology sheaf of `F` is
> quasi-coherent",

and its step is the triangle datum
`AlgebraicGeometry.SmallEtale.exists_distTriang_free_of_lift_smallEtale_quasicoherent`, which
carries exactly that `P` to the third vertex.

## The chain, and what each link costs

1. **Boundedness.**  `AlgebraicGeometry.SmallEtale`
   `.exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom_of_isAffine` puts `ε^*E` in `D⁻` on the
   small étale site of an affine, and `AlgebraicGeometry.SmallEtale`
   `.isZero_homology_associatedModule_iff` — the zero-detection assertion of Stacks 08H8 —
   carries the bound back to `E`.  **This is where affineness is spent**, and it is spent as
   quasi-compactness: the finite-refinement proviso of the general boundedness step is
   discharged on the small étale site of a quasi-compact scheme.
2. **Finite type of the top cohomology.**  Stacks 08FX on the small étale ringed site,
   `AlgebraicGeometry.SmallEtale.isFiniteType_homology_smallEtaleRingedSite`, at the degree `n`
   the induction is at; `m`-pseudo-coherence is moved up to `n` by
   `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_mono_general`.  The conclusion is carried
   across `ε` by `AlgebraicGeometry.SmallEtale`
   `.isFiniteType_homology_of_isFiniteType_homology_associatedModule`, the converse of Stacks
   08HD for a quasi-coherent module.
3. **The surjection `𝒪_S^{⊕t} ⟶ Hⁿ(E)`, globally.**  `Stacks.AmpleEventualGeneration`
   `.isFinGen_of_isAffine` — Stacks 01PB on the whole of an affine scheme — gives finitely many
   *global* generating sections of a quasi-coherent module of finite type.  **This is the second
   thing affineness buys, and it is what makes the induction runnable at all**: the general local
   surjection `SheafOfModules.exists_coversTop_epi_free_of_isFiniteType` produces an epimorphism
   only onto a restriction `Hⁿ(E)|_V`, and a recursion whose step shrinks the scheme cannot be
   run by `isPseudoCoherentFrom_of_descentStep`, whose step must produce a triangle on the
   ambient site.  (The source shrinks at every step; this is how that is avoided.)
4. **The lift.**  `AlgebraicGeometry.exists_lift_truncGEπ_zero_single_free_of_isAffineOpen_top`
   lifts the resulting `𝒪_S^{⊕t}[0] ⟶ τ^{≥0}(E⟦n⟧)` to `E⟦n⟧` with nothing shrunk.  **This is
   where quasi-coherence of the cohomology sheaves is spent**, and it is not avoidable: the lift
   exists because the obstruction group vanishes on an affine, which is a statement about
   quasi-coherent modules.
5. **The step datum and the recursion**, as above.

## Why quasi-coherence is a hypothesis here and not in Stacks 08HE

Stacks 08HE carries no quasi-coherence hypothesis.  Its proof shrinks `S` again at every stage of
the induction ("passing to an open covering, choose a surjection … and lift it locally"), so the
lift it uses is a local one and needs nothing of quasi-coherence.  The recursion in this
development does not change its ambient site — the obstruction is recorded in the implementation
notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/TopDegreeInduction.lean`, item 2,
which asks for a form of the induction hypothesis stable under passing to a slice and is not
built — so the lift has to be global, and a global lift on an affine is exactly what
quasi-coherence provides.  **What is proved here is therefore the quasi-coherent case**, which is
the case Stacks 0DII consumes, `E` there lying in `D_QCoh(𝒪_X)`; see "What 0DII still owes", item
1, in `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/RelativeAbsolute.lean`,
which states the narrow form in precisely these words.

## The derived-category model is pinned on the Zariski side

`AlgebraicGeometry.exists_lift_truncGEπ_zero_single_free_of_isAffineOpen_top` is stated under a
file-level `attribute [local instance] HasDerivedCategory.standard`, so the model appears in its
statement and cannot be exchanged afterwards.  The two statements of this file that consume it
therefore take `D(𝒪_S)` at that same model, re-taken here as the named
`AlgebraicGeometry.Scheme.standardZariskiHasDerivedCategory` so that a consumer can supply it to
the family binders of the locality capstone and meet these statements on the same term.  It has
to be given a priority: the library carries a *second*, inequivalent model at
`SheafOfModules.hasDerivedCategory`, one universe lower, and without the priority that one is
synthesized and the lift does not apply.  Everything model-independent in this file keeps a free
`HasDerivedCategory` binder; the étale side is free throughout.

## Main results

* `AlgebraicGeometry.SmallEtale.isFiniteType_homology_of_isPseudoCoherentFromSmallEtale`: step 2.
* `AlgebraicGeometry.SmallEtale.exists_isZero_homology_gt_of_isPseudoCoherentFromSmallEtale`:
  step 1 — on an affine scheme, `E` is bounded above.
* `AlgebraicGeometry.SmallEtale.exists_distTriang_affine_of_isPseudoCoherentFromSmallEtale`:
  **the step of the induction, discharged on an affine chart** — steps 2, 3, 4 and the step
  datum.
* **Clause (2) ⇒ (1) of Stacks 08HE on an affine scheme, for quasi-coherent cohomology**:
  `AlgebraicGeometry.SmallEtale.isPseudoCoherentFrom_of_isPseudoCoherentFromSmallEtale_of_isAffine`

## Implementation notes

No `@[stacks]` attribute is attached to anything here.  Clause (2) ⇒ (1) of Stacks 08HE is not
proved in the generality the tag states — see above — and the three registrations of Stacks 0DII
in this library stay where they are.

The global instance `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is switched off for
this file.  It states the abelian structure of `SheafOfModules.{max u v r w} O` at a module
universe which is a `max` of the site universes; the small étale site has its objects in
`Type (u + 1)` while the modules here have sections in `Type u`, so instance search against it
leaves the stuck universe constraint `u =?= max (u + 1) ?w` and the `HasDerivedCategory` binders
fail to elaborate.  The abelian structure actually used is Mathlib's, at the pinned universes.

## References

* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FV](https://stacks.math.columbia.edu/tag/08FV)
* [Stacks Project, Tag 08FX](https://stacks.math.columbia.edu/tag/08FX)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 08HD](https://stacks.math.columbia.edu/tag/08HD)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u d d'

namespace AlgebraicGeometry

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-! ### Two model-independent steps -/

section Generic

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (Y : Scheme.{u}) (hY : B.Contains Y)
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B Y hY))]

/-- **Finite type of the cohomology of `E` in the degree the induction is at.**  Let `ε^*E` be
`m`-pseudo-coherent, let `m ≤ n`, let `Hⁿ(E)` be quasi-coherent and let the cohomology of `E`
vanish above `n`.  Then `Hⁿ(E)` is of finite type.

`m`-pseudo-coherence of `ε^*E` is moved up to `n`-pseudo-coherence by
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_mono_general`; exactness of `ε^*` carries the
vanishing of `Hʲ(E)` above `n` to `Hʲ(ε^*E)`, through
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` at `ε^*`; Stacks 08FX on the small étale
ringed site then makes `Hⁿ(ε^*E)` of finite type, and the converse of Stacks 08HD for a
quasi-coherent module brings that back across `ε`. -/
public theorem isFiniteType_homology_of_isPseudoCoherentFromSmallEtale
    (F : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O))) (m n : ℤ)
    (hmn : m ≤ n)
    (hE : IsPseudoCoherentFromSmallEtale B Y hY F m)
    (_hqc : SheafOfModules.IsQuasicoherent ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O)) n).obj F))
    (hvan : ∀ j : ℤ, n < j →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O)) j).obj F)) :
    SheafOfModules.IsFiniteType ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O)) n).obj F) := by
  have hEn : IsPseudoCoherentFromSmallEtale B Y hY F n :=
    RingedSite.isPseudoCoherentFrom_mono_general (X := smallEtaleRingedSite B Y hY) _ hE hmn
  exact @isFiniteType_homology_of_isFiniteType_homology_associatedModule.{d, d', u} B Y hY
    (inferInstance : HasDerivedCategory.{d}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O)))
    inferInstance F n
    (isFiniteType_homology_smallEtaleRingedSite B Y hY _ n hEn
      (fun j hj => (@isZero_homology_associatedModule_iff.{u, d, d'} B Y hY
        (inferInstance : HasDerivedCategory.{d}
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O)))
        inferInstance F j).2 (hvan j hj)))

/-- **On an affine scheme, `m`-pseudo-coherence of `ε^*E` bounds `E` above.**  This is the
reduction that produces the natural number the induction on the cohomological gap runs on.

`AlgebraicGeometry.SmallEtale.exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom_of_isAffine`
puts the complex witnessing `m`-pseudo-coherence of `ε^*E` in `D⁻` — the finite-refinement
proviso of the general boundedness step being a theorem on the small étale site of a
quasi-compact scheme — and `AlgebraicGeometry.SmallEtale.isZero_homology_associatedModule_iff`,
the zero-detection assertion of Stacks 08H8, carries the vanishing back to `E`.

Affineness is used only through quasi-compactness; no quasi-coherence is needed. -/
public theorem exists_isZero_homology_gt_of_isPseudoCoherentFromSmallEtale
    [_root_.AlgebraicGeometry.IsAffine Y]
    (F : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O))) (m : ℤ)
    (hE : IsPseudoCoherentFromSmallEtale B Y hY F m) :
    ∃ b : ℤ, ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O)) j).obj F) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  obtain ⟨b, hb⟩ :=
    exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom_of_isAffine B Y hY K m hK
  refine ⟨b, fun j hj => ?_⟩
  refine (@isZero_homology_associatedModule_iff.{u, d, d'} B Y hY
    (inferInstance : HasDerivedCategory.{d}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O)))
    inferInstance F j).1 ?_
  exact IsZero.of_iso ((DerivedCategory.isLE_iff _ b).1 hb j hj)
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheaf B Y hY)) j).mapIso e).symm

end SmallEtale

variable (Y : Scheme.{u})
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O))]

/-- **Quasi-coherence of the cohomology sheaves survives a shift.**  `Hᵠ(E⟦n⟧)` is `Hⁿ⁺ᵠ(E)` by
`CategoryTheory.Functor.shiftIso` at the degree-zero homology functor, so it is quasi-coherent
whenever every cohomology sheaf of `E` is.

This is what the affine-chart lifting step asks of `E⟦n⟧`, the induction having quasi-coherence
of the cohomology of `E` itself. -/
public theorem Scheme.isQuasicoherent_homology_shift
    (F : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O))) (n : ℤ)
    (hQ : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O)) j).obj F).IsQuasicoherent)
    (q : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O)) q).obj
        (F⟦n⟧)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (((DerivedCategory.homologyFunctor
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O)) 0).shiftIso
        n q (n + q) rfl).app F).symm
    (hQ (n + q))

end Generic

/-! ### The model the affine-chart lifting step is stated at -/

/-- **The standard model of `D(𝒪_Y)`**, named so that it can be re-taken with
`attribute [local instance]` and supplied to a family binder.

`AlgebraicGeometry.exists_lift_truncGEπ_zero_single_free_of_isAffineOpen_top` is stated under
`attribute [local instance] CategoryTheory.HasDerivedCategory.standard` at
`AlgebraicGeometry.Scheme.Modules`, so that model is visible in its statement and the statements
that consume it have to use the same one.  `AlgebraicGeometry.Scheme.Modules` is a plain `def`
and does not reduce at instance transparency, which is why the value is taken there and the type
is written at the `AlgebraicGeometry.RingedSite.ringSheaf` spelling the pseudo-coherence
predicate of Stacks 08FT uses. -/
@[instance_reducible] public def Scheme.standardZariskiHasDerivedCategory (Y : Scheme.{u}) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O)) :=
  HasDerivedCategory.standard Y.Modules

/-- **The standard model of `D(𝒪_Y|_W)` on a Zariski slice.**  The recursion
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_descentStep` asks for a model on every
slice of the ambient site, at the same universe as the ambient one; this supplies it at the
universe `AlgebraicGeometry.Scheme.standardZariskiHasDerivedCategory` lives in. -/
@[instance_reducible] public def Scheme.standardZariskiOverHasDerivedCategory (Y : Scheme.{u})
    (W : Y.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O).over W)) :=
  HasDerivedCategory.standard _

attribute [local instance 100000] Scheme.standardZariskiHasDerivedCategory
  Scheme.standardZariskiOverHasDerivedCategory

/-! ### The induction, run on an affine chart -/

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (Y : Scheme.{u}) (hY : B.Contains Y)
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B Y hY))]
  [_root_.AlgebraicGeometry.IsAffine Y]

/-- **The step of the induction of Stacks 08HE (2) ⇒ (1), discharged on an affine scheme.**  Let
`F` be an object of `D(𝒪_Y)` on an affine `Y` with `ε^*F` `m`-pseudo-coherent, quasi-coherent
cohomology sheaves and no cohomology above `n ≥ m`.  Then there is a distinguished triangle whose
second vertex is `F`, whose first vertex is `m`-pseudo-coherent, and whose third vertex has no
cohomology in any degree `≥ n` and again has `m`-pseudo-coherent pullback along `ε` and
quasi-coherent cohomology sheaves.

That is exactly what `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_descentStep` asks of
its step for the predicate `P` of Stacks 0DII.  The three geometric inputs are the finite type of
`Hⁿ(F)`, the *global* surjection onto it from a finite free module — Stacks 01PB on an affine,
`Stacks.AmpleEventualGeneration.isFinGen_of_isAffine` — and the affine-chart lift
`AlgebraicGeometry.exists_lift_truncGEπ_zero_single_free_of_isAffineOpen_top`; the triangle
itself is
`AlgebraicGeometry.SmallEtale.exists_distTriang_free_of_lift_smallEtale_quasicoherent`. -/
public theorem exists_distTriang_affine_of_isPseudoCoherentFromSmallEtale (m n : ℤ) (hmn : m ≤ n)
    (F : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O)))
    (hE : IsPseudoCoherentFromSmallEtale B Y hY F m)
    (hQ : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O)) j).obj F).IsQuasicoherent)
    (hvan : ∀ j : ℤ, n < j →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O)) j).obj F)) :
    ∃ T : Triangle (DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O))),
      T ∈ distTriang (DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O))) ∧
        Nonempty (T.obj₂ ≅ F) ∧ Y.zariskiRingedSite.IsPseudoCoherentFrom T.obj₁ m ∧
          (IsPseudoCoherentFromSmallEtale B Y hY T.obj₃ m ∧
            ∀ j : ℤ, ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O)) j).obj
                T.obj₃).IsQuasicoherent) ∧
            ∀ j : ℤ, n ≤ j →
              IsZero ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u}
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O)) j).obj
                  T.obj₃) := by
  have : DerivedCategory.IsLE F n := (DerivedCategory.isLE_iff F n).2 hvan
  have hft := isFiniteType_homology_of_isPseudoCoherentFromSmallEtale B Y hY F m n hmn hE
    (hQ n) hvan
  obtain ⟨σ, hσ⟩ :=
    Stacks.AmpleEventualGeneration.isFinGen_of_isAffine (X := Y) _ (hQ n) hft
  have : Finite σ.I := hσ
  obtain ⟨f, hf⟩ := exists_lift_truncGEπ_zero_single_free_of_isAffineOpen_top Y (F⟦n⟧)
    (Scheme.isQuasicoherent_homology_shift Y F n hQ) (isAffineOpen_top Y) σ.I
    (DerivedCategory.singleMapTruncGEZeroShift F n σ.π)
  obtain ⟨T, hT, h2, h1, h3e, h3q, h3z⟩ :=
    exists_distTriang_free_of_lift_smallEtale_quasicoherent B Y hY m n F σ.I σ.π σ.epi f hf hE hQ
  exact ⟨T, hT, h2, h1, ⟨h3e, h3q⟩, h3z⟩

/-- **Clause (2) ⇒ (1) of Stacks 08HE on an affine scheme, for an object with quasi-coherent
cohomology.**  Let `Y` be an affine scheme and let `E` be an object of `D(𝒪_Y)` whose cohomology
sheaves are quasi-coherent.  If `ε^*E` is `m`-pseudo-coherent on the small étale site of `Y`,
then `E` is `m`-pseudo-coherent on the small Zariski site of `Y`.

This is the first application of
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_descentStep`.  The predicate carried by the
recursion is the conjunction of the two standing hypotheses, its step is
`AlgebraicGeometry.SmallEtale.exists_distTriang_affine_of_isPseudoCoherentFromSmallEtale` above,
and the degree the recursion starts from is the bound of
`AlgebraicGeometry.SmallEtale.exists_isZero_homology_gt_of_isPseudoCoherentFromSmallEtale`. -/
public theorem isPseudoCoherentFrom_of_isPseudoCoherentFromSmallEtale_of_isAffine (m : ℤ)
    (F : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O)))
    (hE : IsPseudoCoherentFromSmallEtale B Y hY F m)
    (hQ : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O)) j).obj F).IsQuasicoherent) :
    Y.zariskiRingedSite.IsPseudoCoherentFrom F m := by
  obtain ⟨b, hb⟩ := exists_isZero_homology_gt_of_isPseudoCoherentFromSmallEtale B Y hY F m hE
  refine RingedSite.isPseudoCoherentFrom_of_descentStep Y.zariskiRingedSite m
    (fun G => IsPseudoCoherentFromSmallEtale B Y hY G m ∧
      ∀ j : ℤ, ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.O)) j).obj G).IsQuasicoherent)
    (fun G n hmn hPG hvan => ?_) F b hb ⟨hE, hQ⟩
  obtain ⟨T, hT, h2, h1, hP3, h3z⟩ :=
    exists_distTriang_affine_of_isPseudoCoherentFromSmallEtale B Y hY m n hmn G hPG.1 hPG.2 hvan
  exact ⟨T, hT, h2, h1, hP3, h3z⟩

end SmallEtale

end AlgebraicGeometry

end
