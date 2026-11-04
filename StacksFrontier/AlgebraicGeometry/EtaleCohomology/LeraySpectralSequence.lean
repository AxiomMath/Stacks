module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardAcyclic.Sections
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackSections
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.GrothendieckSequenceAbuts
import StacksCore.Tactic.StacksAttribute

/-!
# The Leray spectral sequence for the small étale site

Let `f : X ⟶ Y` be a morphism in a big étale site and let `F` be an abelian sheaf on the small
étale site of `X`. There is a cohomological spectral sequence

```
E₂^{p,q} = H^p_ét(Y, R^q f_* F)  ⟹  H^{p+q}_ét(X, F),
```

the Grothendieck spectral sequence of the composition

```
Ab(X_ét) --f_*--> Ab(Y_ét) --Γ(Y, -)--> Ab
```

of direct image with global sections. The only input beyond the general machinery is that the
direct image of an injective abelian étale sheaf is acyclic for global sections on the target,
which is the second assertion of Stacks 03QB.

Global sections on the small étale site of a scheme are the sections over its final object
`Y / Y`, and the composite `Γ(Y, -) ∘ f_*` is the sections over the base change `X ×_Y Y`,
which is again a final object; so that composite is global sections on `X`, and the abutment
of the spectral sequence is the étale cohomology of `X`.

## Main definitions

* `AlgebraicGeometry.smallEtaleGlobalSections` — global sections of an abelian sheaf on the
  small étale site, i.e. sections over the final object.
* `AlgebraicGeometry.smallEtalePushforwardCompSectionsIso` — sections of a direct image over
  an object are sections over its étale base change.
* `AlgebraicGeometry.smallEtaleBaseChangeFinalSectionsIso` — sections over the base change of
  the final object are global sections.
* `AlgebraicGeometry.smallEtalePushforwardCompGlobalSectionsIso` — global sections on the
  target composed with direct image are global sections on the source.

## Main results

* `AlgebraicGeometry.exists_abutsTo_leraySpectralSequence_smallEtale_sections` — the spectral
  sequence `H^p(V, R^q f_* F) ⟹ H^{p+q}(X ×_Y V, F)` for an object `V` of the small étale site
  of the target.
* `AlgebraicGeometry.exists_abutsTo_leraySpectralSequence_smallEtale` — **the Leray spectral
  sequence for the small étale site**, with its second page and its abutment; the case of the
  final object.

## Implementation notes

Étale cohomology is taken here in its derived-functor form: `H^p_ét(Y, G)` is the `p`-th right
derived functor of global sections, evaluated at `G`, and `R^q f_*` is the `q`-th right derived
functor of direct image, both in the `ℤ`-indexed convention
`CategoryTheory.Functor.rightDerivedPlus` fixed by Stacks 05U4. This is the convention in which
the acyclicity input of Stacks 03QB is stated, and the one the Grothendieck spectral sequence
produces, so no change of indexing is needed anywhere.

The spectral sequence itself is the one of Stacks 015N, packaged with its convergence clause as
`CategoryTheory.SpectralSequence.AbutsTo`. That packaging is stated for arbitrary abelian
categories and arbitrary additive functors, so the étale case is an instantiation: the two
functors are direct image and global sections, and the acyclicity hypothesis is supplied by
`AlgebraicGeometry.pushforward_injective_rightAcyclic_sections`.

Sections of a direct image over an object `V` are *definitionally* the sections of the original
sheaf over the base change `X ×_Y V`, the underlying presheaf of a direct image being
restriction along the base-change functor; `smallEtalePushforwardCompSectionsIso` is therefore
the identity isomorphism. What is not definitional is that `X ×_Y Y` is a final object of the
small étale site of `X`, which is
`AlgebraicGeometry.smallEtaleBaseChange_finalIsTerminal`; the resulting isomorphism of global
sections functors is moved onto the derived functors by
`Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedPlusNatIsoOfIso`.

## References

* [Stacks Project, Tag 03QC](https://stacks.math.columbia.edu/tag/03QC)
* [Stacks Project, Tag 03QB](https://stacks.math.columbia.edu/tag/03QB)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 021D](https://stacks.math.columbia.edu/tag/021D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

-- As in `AlgebraicGeometry.pushforward_injective_rightAcyclic_sections`, raising the priority
-- of this instance is what lets the right derived functors below be found; at the default
-- priority the search times out.
attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (B : BigEtaleSite.{u})

/-- Global sections of an abelian sheaf on the small étale site of a scheme `X`: the sections
over the final object `X / X` of that site. -/
public abbrev smallEtaleGlobalSections (X : B.Scheme) :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1} :=
  (sheafSections (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}).obj
    (op (SmallEtale.final B X.obj X.property))

/-- Global sections on the small étale site are additive in the sheaf. -/
public instance smallEtaleSectionsAtFinal_additive (X : B.Scheme) :
    (smallEtaleGlobalSections B X).Additive where
  map_add := by intros; rfl

variable {X Y : B.Scheme} (f : X ⟶ Y)

/-- Sections of a direct image over an object `V` of the small étale site of `Y` are the
sections of the original sheaf over the base change `X ×_Y V`: the underlying presheaf of a
direct image is restriction along the base-change functor. -/
public def smallEtalePushforwardCompSectionsIso (V : SmallEtale B Y.obj Y.property) :
    Stacks.HigherDirectImage.pushforward.{u, u + 1} B f ⋙
        (sheafSections (SmallEtale.topology B Y.obj Y.property)
          AddCommGrpCat.{u + 1}).obj (op V) ≅
      (sheafSections (SmallEtale.topology B X.obj X.property)
        AddCommGrpCat.{u + 1}).obj (op ((smallEtaleBaseChange B f).obj V)) :=
  Iso.refl _

/-- Sections over the base change `X ×_Y Y` of the final object of the small étale site of `Y`
are global sections on the small étale site of `X`: that base change is again a final
object. -/
public def smallEtaleBaseChangeFinalSectionsIso :
    (sheafSections (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}).obj
        (op ((smallEtaleBaseChange B f).obj (SmallEtale.final B Y.obj Y.property))) ≅
      smallEtaleGlobalSections B X :=
  (sheafSections (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}).mapIso
    (((smallEtaleBaseChange_finalIsTerminal B f).uniqueUpToIso
      (SmallEtale.finalIsTerminal B X.obj X.property)).symm.op)

/-- Global sections on the small étale site of `Y` composed with direct image along `f` are
global sections on the small étale site of `X`. -/
public def smallEtalePushforwardCompGlobalSectionsIso :
    Stacks.HigherDirectImage.pushforward.{u, u + 1} B f ⋙ smallEtaleGlobalSections B Y ≅
      smallEtaleGlobalSections B X :=
  smallEtalePushforwardCompSectionsIso B f (SmallEtale.final B Y.obj Y.property) ≪≫
    smallEtaleBaseChangeFinalSectionsIso B f

section SpectralSequence

variable [HasSheafify (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}]
  [HasSheafify (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}]
  [EnoughInjectives (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
  [EnoughInjectives (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})]

/-- **The Leray spectral sequence over an étale object of the target.** For an object `V` of
the small étale site of `Y` and an abelian sheaf `F` on the small étale site of `X` there is a
cohomological spectral sequence with second page

```
E₂^{p,q} ≅ H^p(V, R^q f_* F)
```

abutting to the graded family `n ↦ H^n(X ×_Y V, F)`.

This is the Grothendieck spectral sequence of [Stacks, Tag 015N] for the composition of direct
image with sections over `V`, whose acyclicity hypothesis is the second assertion of
[Stacks, Tag 03QB]. The abutment is the cohomology over `X ×_Y V` because sections of a direct
image over `V` are sections over `X ×_Y V`. -/
@[sga "4 VII 1.5" "more general",
  sga "4½ Arcata 2.3.4" "more general",
  sga "4½ Th_finitude 1.3" "partial"]
public theorem exists_abutsTo_leraySpectralSequence_smallEtale_sections
    (V : SmallEtale B Y.obj Y.property)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 0,
      (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
        (((sheafSections (SmallEtale.topology B Y.obj Y.property)
            AddCommGrpCat.{u + 1}).obj (op V)).rightDerivedPlus p).obj
          ((Stacks.HigherDirectImage.pushforward.{u, u + 1} B f).rightDerivedPlus q |>.obj
            F))) ∧
      SpectralSequence.AbutsTo E (fun n =>
        (((sheafSections (SmallEtale.topology B X.obj X.property)
          AddCommGrpCat.{u + 1}).obj
            (op ((smallEtaleBaseChange B f).obj V))).rightDerivedPlus n).obj F) := by
  obtain ⟨K, hrest⟩ := Functor.exists_abutsTo_homology_rightDerivedFunctorPlus_comp
    (Stacks.HigherDirectImage.pushforward.{u, u + 1} B f)
    ((sheafSections (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}).obj (op V))
    (fun I hI => by
      have := hI
      exact pushforward_injective_rightAcyclic_sections B f I V)
    ((DerivedCategory.Plus.singleFunctor
      (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) 0).obj F)
  obtain ⟨E, -, hE₂, habuts⟩ :=
    hrest _ (fun _ _ => rfl) _ (fun _ _ _ => rfl) _ (fun _ _ _ => rfl)
  refine ⟨E, hE₂, habuts.of_iso fun n => ?_⟩
  exact (Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedPlusNatIsoOfIso
    (smallEtalePushforwardCompSectionsIso B f V) n).app F

/-- **The Leray spectral sequence for the small étale site** (Stacks 03QC). Let `f : X ⟶ Y` be
a morphism in a big étale site and let `F` be an abelian sheaf on the small étale site of `X`.
There is a cohomological spectral sequence with second page

```
E₂^{p,q} ≅ H^p_ét(Y, R^q f_* F),
```

the étale cohomology of `Y` with coefficients in the higher direct images of `F`, which abuts
to the graded family `n ↦ H^n_ét(X, F)` of étale cohomology groups of `X`: some finite
decreasing filtration of each `H^n_ét(X, F)` has the terms `E_∞^{p,n-p}` as its graded pieces.

Both the second page and the abutment are taken in the derived-functor form of étale
cohomology, `CategoryTheory.Functor.rightDerivedPlus` of global sections, and `R^q f_*` is the
`q`-th right derived functor of direct image.

This is `exists_abutsTo_leraySpectralSequence_smallEtale_sections` for the final object of the
small étale site of `Y`, whose base change is a final object of the small étale site of `X`. -/
@[stacks 03QC,
  sga "4½ Arcata 2.3.4" "first spectral sequence",
  sga "4 V 5.3" "small étale sites",
  sga "4 V 5.4" "étale sites, Z = point",
  sga "4 VII 1.5" "H^p(Y,R^qf_*F) SS",
  sga "4 IX 4.2" "more general",
  sga "4½ Th_finitude 1.3" "partial"]
public theorem exists_abutsTo_leraySpectralSequence_smallEtale
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 0,
      (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
        ((smallEtaleGlobalSections B Y).rightDerivedPlus p).obj
          ((Stacks.HigherDirectImage.pushforward.{u, u + 1} B f).rightDerivedPlus q |>.obj
            F))) ∧
      SpectralSequence.AbutsTo E
        (fun n => ((smallEtaleGlobalSections B X).rightDerivedPlus n).obj F) := by
  obtain ⟨E, hE₂, habuts⟩ := exists_abutsTo_leraySpectralSequence_smallEtale_sections B f
    (SmallEtale.final B Y.obj Y.property) F
  refine ⟨E, hE₂, habuts.of_iso fun n => ?_⟩
  exact (Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedPlusNatIsoOfIso
    (smallEtaleBaseChangeFinalSectionsIso B f) n).app F

end SpectralSequence

end AlgebraicGeometry

end
