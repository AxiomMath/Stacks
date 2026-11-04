module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleZariskiCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ZariskiRefinement
public import StacksFrontier.RingTheory.Henselian.Criteria
public import StacksFrontier.RingTheory.Spectrum.Prime.Profinite
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.AboveTheDimension
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.ProfiniteSpaces

/-!
# Étale cohomology of an affine scheme all of whose points are closed

Let `S` be an affine scheme whose points are all closed and whose residue fields are all
separably closed. Then every abelian sheaf on the small étale site of `S` has vanishing
cohomology in positive degree.

## Main results

* `AlgebraicGeometry.etaleSectionsIsoZariskiRestrictionSections` — étale global sections is
  Zariski global sections of the Zariski restriction.
* `AlgebraicGeometry.preservesEpimorphisms_etaleSections` — étale global sections is right
  exact on a scheme with profinite underlying space and strictly henselian local rings.
* `AlgebraicGeometry.projective_constantSheaf_smallEtale` — the constant abelian sheaf on
  `ULift ℤ` is projective on such a scheme.
* `AlgebraicGeometry.subsingleton_etaleCohomology_of_isProfinite` — positive-degree étale
  cohomology vanishes on such a scheme.
* `AlgebraicGeometry.subsingleton_etaleCohomology_of_closed_points` and
  `AlgebraicGeometry.subsingleton_etaleCohomology_of_closed_points'` — the same for an affine
  scheme with only closed points and separably closed residue fields.

## Implementation notes

Global sections on the small étale site is the composite of the direct image along
`ε : S_ét ⟶ S_Zar`, exact when the local rings are strictly henselian, with Zariski global
sections, exact when the underlying space is profinite; on an affine scheme all of whose points
are closed both hold, the local rings having Krull dimension zero.

The small étale site is Mathlib's `AlgebraicGeometry.Scheme.Etale`, which is the site carrying
the Zariski comparison `AlgebraicGeometry.zariskiRestrictionFunctor`. The terminal object used
to read global sections off the site is `(opensToEtale S).obj ⊤` rather than `.mk (𝟙 S)`,
because it is that object at which the Zariski restriction is evaluated.

## References

* [Stacks Project, Tag 09AY](https://stacks.math.columbia.edu/tag/09AY)
* [Stacks Project, Tag 09AX](https://stacks.math.columbia.edu/tag/09AX)
* [Stacks Project, Tag 04MG](https://stacks.math.columbia.edu/tag/04MG)
* [Stacks Project, Tag 06RS](https://stacks.math.columbia.edu/tag/06RS)
* [Stacks Project, Tag 0A3F](https://stacks.math.columbia.edu/tag/0A3F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v w

namespace AlgebraicGeometry

/-- **Étale global sections is Zariski global sections of the Zariski restriction.** Evaluating
an étale abelian sheaf at the terminal object `(opensToEtale X).obj ⊤` is the same as evaluating
its direct image along `ε : X_ét ⟶ X_Zar` on the whole space. -/
public def etaleSectionsIsoZariskiRestrictionSections (X : Scheme.{u})
    [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat.{v}] :
    zariskiRestrictionFunctor.{u, v} X ⋙
        (sheafSections (Opens.grothendieckTopology ↑X) AddCommGrpCat.{v}).obj
          (op (⊤ : Opens ↑X)) ≅
      (sheafSections (Scheme.smallEtaleTopology X) AddCommGrpCat.{v}).obj
        (op ((opensToEtale X).obj (⊤ : X.Opens))) :=
  Functor.isoWhiskerRight
    ((Functor.isoWhiskerLeft
      ((opensToEtale X).sheafPushforwardContinuous AddCommGrpCat.{v}
        (Opens.grothendieckTopology ↑X) (Scheme.smallEtaleTopology X))
      (asIso (sheafificationAdjunction (Opens.grothendieckTopology ↑X)
        AddCommGrpCat.{v}).counit)).trans (Functor.rightUnitor _))
    ((sheafSections (Opens.grothendieckTopology ↑X) AddCommGrpCat.{v}).obj
      (op (⊤ : Opens ↑X)))

/-- **Étale global sections is right exact** on a scheme whose underlying space is profinite
and whose local rings are strictly henselian. -/
public theorem preservesEpimorphisms_etaleSections (X : Scheme.{u})
    (hlocal : ∀ x : X, StrictlyHenselianLocalRing ↥(X.presheaf.stalk x))
    (hprof : IsProfiniteStacks ↑X)
    [HasSheafify (Scheme.smallEtaleTopology X) AddCommGrpCat.{max u v}]
    [(Scheme.smallEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] :
    ((sheafSections (Scheme.smallEtaleTopology X) AddCommGrpCat.{max u v}).obj
      (op ((opensToEtale X).obj (⊤ : X.Opens)))).PreservesEpimorphisms := by
  let : EssentiallySmall.{max u v} X.Opens := inferInstance
  let : HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat.{max u v} :=
    hasSheafifyEssentiallySmallSite.{u, max u v, u, (max u v) + 1, max u v} _ _
  let : (Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat.{max u v} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, max u v, u,
      (max u v) + 1, max u v} _
  have h₁ : PreservesFiniteColimits (zariskiRestrictionFunctor.{u, max u v} X) :=
    zariskiRestrictionFunctor_preservesFiniteColimits_of_strictlyHenselian X hlocal
  have h₂ : ((sheafSections (Opens.grothendieckTopology ↑X) AddCommGrpCat.{max u v}).obj
      (op (⊤ : Opens ↑X))).PreservesEpimorphisms :=
    Stacks.CohomologyVanishing.preservesEpimorphisms_globalSections_of_isProfiniteStacks hprof
  have h₃ : (zariskiRestrictionFunctor.{u, max u v} X ⋙
      (sheafSections (Opens.grothendieckTopology ↑X) AddCommGrpCat.{max u v}).obj
        (op (⊤ : Opens ↑X))).PreservesEpimorphisms := inferInstance
  exact Functor.PreservesEpimorphisms.of_iso (etaleSectionsIsoZariskiRestrictionSections X)

/-- **The constant abelian sheaf on `ULift ℤ` is projective** on the small étale site of a
scheme whose underlying space is profinite and whose local rings are strictly henselian. -/
public theorem projective_constantSheaf_smallEtale (X : Scheme.{u})
    (hlocal : ∀ x : X, StrictlyHenselianLocalRing ↥(X.presheaf.stalk x))
    (hprof : IsProfiniteStacks ↑X)
    [HasSheafify (Scheme.smallEtaleTopology X) AddCommGrpCat.{max u v}]
    [(Scheme.smallEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] :
    Projective ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{max u v}).obj
      (AddCommGrpCat.of (ULift.{max u v} ℤ))) :=
  have := preservesEpimorphisms_etaleSections.{u, v} X hlocal hprof
  (constantSheafAdj (Scheme.smallEtaleTopology X) AddCommGrpCat.{max u v}
    (isTerminal_opensToEtale_top X)).map_projective _ Stacks.CohomologyVanishing.intProjective

/-- **Positive-degree étale cohomology vanishes** on a scheme whose underlying space is
profinite and whose local rings are strictly henselian. -/
public theorem subsingleton_etaleCohomology_of_isProfinite (X : Scheme.{u})
    (hlocal : ∀ x : X, StrictlyHenselianLocalRing ↥(X.presheaf.stalk x))
    (hprof : IsProfiniteStacks ↑X)
    [HasSheafify (Scheme.smallEtaleTopology X) AddCommGrpCat.{max u v}]
    [(Scheme.smallEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasExt.{w} (Sheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{max u v})]
    (F : Sheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{max u v}) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w, max u v} F q) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have := projective_constantSheaf_smallEtale.{u, v} X hlocal hprof
  exact Abelian.Ext.subsingleton_of_projective _ _ n

section Affine

variable (S : Scheme.{u}) [IsAffine S]

/-- On an affine scheme all of whose points are closed, every prime of the ring of global
sections is maximal. -/
private theorem isMaximal_of_closed_points
    (hclosed : ∀ x : S, IsClosed ({x} : Set S)) (q : PrimeSpectrum Γ(S, ⊤)) :
    q.asIdeal.IsMaximal := by
  have himage : IsClosed (S.isoSpec.hom.homeomorph ''
      ({S.isoSpec.hom.homeomorph.symm q} : Set S)) :=
    S.isoSpec.hom.homeomorph.isClosedMap _ (hclosed _)
  rw [Set.image_singleton, S.isoSpec.hom.homeomorph.apply_symm_apply q] at himage
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp himage

/-- A localization at a prime of a ring all of whose primes are maximal is a henselian local
ring. -/
private theorem henselian_atPrime_of_isMaximal {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) (hall : ∀ q : PrimeSpectrum R, q.asIdeal.IsMaximal) :
    HenselianLocalRing (Localization.AtPrime p.asIdeal) := by
  let L := Localization.AtPrime p.asIdeal
  let : IsLocalRing L := Localization.AtPrime.isLocalRing p.asIdeal
  have hprime : ∀ q : PrimeSpectrum L, q.asIdeal = IsLocalRing.maximalIdeal L := by
    intro q
    let qR := IsLocalization.AtPrime.orderIsoOfPrime L p.asIdeal ⟨q.asIdeal, q.2⟩
    have hqeq : qR.1 = p.asIdeal :=
      (hall ⟨qR.1, qR.2.1⟩).eq_of_le (hall p).ne_top qR.2.2
    exact (Localization.AtPrime.eq_maximalIdeal_iff_under_eq (I := p.asIdeal)).1 hqeq
  have : Ring.KrullDimLE 0 L := Ring.krullDimLE_zero_iff.mpr <| by
    intro I hI
    rw [show I = IsLocalRing.maximalIdeal L from hprime ⟨I, hI⟩]
    infer_instance
  exact henselianLocalRing_of_krullDimLE_zero L

/-- The local rings of an affine scheme with only closed points and separably closed residue
fields are strictly henselian. -/
private theorem strictlyHenselian_stalk_of_closed_points
    (hclosed : ∀ x : S, IsClosed ({x} : Set S))
    (hsep : ∀ x : S, IsSepClosed ↥(S.residueField x)) (x : S) :
    StrictlyHenselianLocalRing ↥(S.presheaf.stalk x) := by
  let p : PrimeSpectrum Γ(S, ⊤) := S.isoSpec.hom x
  let e := ((asIso (S.isoSpec.hom.stalkMap x)).symm.trans
    (AlgebraicGeometry.Spec.stalkIso (CommRingCat.of Γ(S, ⊤)) p)).commRingCatIsoToRingEquiv
  let : HenselianLocalRing (Localization.AtPrime p.asIdeal) :=
    henselian_atPrime_of_isMaximal p (isMaximal_of_closed_points S hclosed)
  let : HenselianLocalRing ↥(S.presheaf.stalk x) := HenselianLocalRing.of_ringEquiv e.symm
  let : IsSepClosed (IsLocalRing.ResidueField ↥(S.presheaf.stalk x)) := hsep x
  exact StrictlyHenselianLocalRing.mk

/-- The underlying space of an affine scheme all of whose points are closed is profinite. -/
private theorem isProfiniteStacks_of_closed_points
    (hclosed : ∀ x : S, IsClosed ({x} : Set S)) :
    IsProfiniteStacks ↑S := by
  obtain ⟨hc, ht, hd⟩ := ((spec_profinite_tfae ↥Γ(S, ⊤)).out 6 1 rfl rfl).mp
    fun q hq => isMaximal_of_closed_points S hclosed ⟨q, hq⟩
  let : CompactSpace (PrimeSpectrum ↥Γ(S, ⊤)) := hc
  let : T2Space (PrimeSpectrum ↥Γ(S, ⊤)) := ht
  let : TotallyDisconnectedSpace (PrimeSpectrum ↥Γ(S, ⊤)) := hd
  let e : PrimeSpectrum ↥Γ(S, ⊤) ≃ₜ ↑S := S.isoSpec.hom.homeomorph.symm
  exact (isProfiniteStacks_iff_compact_t2_totallyDisconnected ↑S).2
    ⟨e.compactSpace, e.t2Space, e.totallyDisconnectedSpace⟩

/-- **Positive-degree étale cohomology vanishes on an affine scheme all of whose points are
closed and all of whose residue fields are separably closed.** -/
@[stacks 09AY]
public theorem subsingleton_etaleCohomology_of_closed_points
    (hclosed : ∀ x : S, IsClosed ({x} : Set S))
    (hsep : ∀ x : S, IsSepClosed ↥(S.residueField x))
    [HasSheafify (Scheme.smallEtaleTopology S) AddCommGrpCat.{max u v}]
    [(Scheme.smallEtaleTopology S).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasExt.{w} (Sheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{max u v})]
    (F : Sheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{max u v}) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w, max u v} F q) :=
  subsingleton_etaleCohomology_of_isProfinite.{u, v} S
    (strictlyHenselian_stalk_of_closed_points S hclosed hsep)
    (isProfiniteStacks_of_closed_points S hclosed) F q hq

/-- **Positive-degree étale cohomology vanishes on an affine scheme all of whose points are
closed and all of whose residue fields are separably closed**, for abelian sheaves at the
coefficient universe `u + 1` of the small étale site itself. -/
@[stacks 09AY "at the coefficient universe of the small étale site"]
public theorem subsingleton_etaleCohomology_of_closed_points'
    (hclosed : ∀ x : S, IsClosed ({x} : Set S))
    (hsep : ∀ x : S, IsSepClosed ↥(S.residueField x))
    [HasExt.{w} (Sheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})]
    (F : Sheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w, u + 1} F q) :=
  subsingleton_etaleCohomology_of_closed_points.{u, u + 1} S hclosed hsep F q hq

end Affine

end AlgebraicGeometry

end
