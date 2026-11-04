module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.EqualityLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.ZariskiHypothesis

/-!
# The injectivity half of Tag 09ZF, reduced to local agreement over the closed subscheme

Let `i : Z ⟶ X` be a morphism of schemes satisfying hypothesis (1) of
[Stacks, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF): restriction of global sections
along `i` is bijective for every sheaf of sets on the Zariski site of `X`. Then two global
sections of a sheaf of sets on the small étale site of `X` are equal as soon as, near every point
of `Z`, they agree over *some* object of the small étale site whose image contains that point.

Both inputs are already available. The open subscheme over which two global sections agree is
`Stacks.EtaleCohomology.globalSectionEqOpen`, and local agreement near every point of `Z` says
exactly that this open contains the image of `i`; hypothesis (1) then forces it to be all of `X`
by `Stacks.EtaleCohomology.eq_top_of_zariskiGlobalSectionsMap_surjective`, and two global sections
agreeing over `X` itself are equal.

This file also factors the comparison map of Tag 09ZF through its presheaf-level part. The two
outer maps of `Stacks.EtaleCohomology.smallEtaleGlobalSectionsMapAt` are components of natural
isomorphisms, so injectivity of the comparison is equivalent to injectivity of
`Stacks.EtaleCohomology.smallEtaleGlobalSectionPullback`, the composite of the unit of the left
Kan extension, restriction along the morphism out of the final object, and the sheafification map.
That reduces the injectivity half of the tag to a single statement: equality of the presheaf-level
pullbacks of two global sections implies local agreement near every point of `Z`.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleGlobalSectionPullback` — the presheaf-level pullback of a
  global section of an étale sheaf along `i`, i.e. the comparison map of Tag 09ZF with the two
  identifications of global sections with sections over a final object removed.

## Main results

* `Stacks.EtaleCohomology.smallEtaleGlobalSectionsMapAt_apply` — the comparison map is that
  pullback conjugated by the two identifications.
* `Stacks.EtaleCohomology.injective_smallEtaleGlobalSectionsMapAt_iff` — the comparison map is
  injective exactly when the presheaf-level pullback is.
* `Stacks.EtaleCohomology.eq_of_forall_exists_globalSectionEqAt` — under hypothesis (1) of Tag
  09ZF, two global sections agreeing near every point of `Z` are equal.
* `Stacks.EtaleCohomology.injective_smallEtaleGlobalSectionsMapAt_of_zariski` — under hypothesis
  (1), the comparison map of Tag 09ZF is injective as soon as equality of presheaf-level pullbacks
  implies local agreement near every point of `Z`.

## Implementation notes

The factorization of the comparison map is definitional: `smallEtaleGlobalSectionsMapAt` is
literally that five-fold composite, so `smallEtaleGlobalSectionsMapAt_apply` is `rfl`.

Only surjectivity of the Zariski restriction maps is used, which is why the hypothesis is stated
with `Function.Surjective` rather than the `Function.Bijective` of the tagged statement; a user holding the
bijectivity hypothesis supplies `fun G ↦ (h G).2`.

## References

* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace

universe u v

namespace Stacks.EtaleCohomology

variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-- **Under hypothesis (1) of Tag 09ZF, local agreement near `Z` implies equality.** If
restriction of global sections along `i : Z ⟶ X` is surjective for every sheaf of sets on the
Zariski site of `X`, then two global sections of a sheaf of sets on the small étale site of `X`
which agree, near every point of `Z`, over some object of the site whose image contains that
point, are equal.

Local agreement says the open equality locus of the two sections contains the image of `i`;
hypothesis (1) forces that open to be all of `X`, and then the sections agree over `X`. -/
public theorem eq_of_forall_exists_globalSectionEqAt
    (hZar : ∀ G : Sheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v)),
      Function.Surjective (zariskiGlobalSectionsMap.{u, v} i G))
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))
    {a b : F.obj.obj (op (terminal X.Etale))}
    (hloc : ∀ z : Z, ∃ W : X.Etale,
      GlobalSectionEqAt F a b W ∧ i.base z ∈ smallEtaleImage W) :
    a = b := by
  refine eq_of_globalSectionEqOpen_eq_top F
    (eq_top_of_zariskiGlobalSectionsMap_surjective i hZar ?_)
  rintro x ⟨z, rfl⟩
  exact (mem_globalSectionEqOpen_iff F a b _).mpr (hloc z)

variable (g : terminal Z.Etale ⟶ (smallEtaleBaseChange i).obj (terminal X.Etale))
  (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))

/-- The presheaf-level pullback along `i` of a global section of a sheaf on the small étale site
of `X`: the unit of the left Kan extension at the final object of `X.Etale`, then restriction
along `g`, then the sheafification map at the final object of `Z.Etale`. -/
public def smallEtaleGlobalSectionPullback (a : F.obj.obj (op (terminal X.Etale))) :
    ((smallEtaleInverseImage.{u, v} i).obj F).obj.obj (op (terminal Z.Etale)) :=
  ((toSheafify (Scheme.smallEtaleTopology Z)
    ((smallEtaleBaseChange i).op.lan.obj F.obj)).app (op (terminal Z.Etale)))
      ((((smallEtaleBaseChange i).op.lan.obj F.obj).map g.op)
        ((((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op (terminal X.Etale))) a))

/-- The comparison map of Tag 09ZF is the presheaf-level pullback, conjugated by the two
identifications of global sections with sections over a final object. -/
public theorem smallEtaleGlobalSectionsMapAt_apply
    (s : (Sheaf.Γ (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))).obj F) :
    smallEtaleGlobalSectionsMapAt.{u, v} i g F s =
      ((Sheaf.ΓNatIsoSheafSections (Scheme.smallEtaleTopology Z)
        (Type (max (u + 1) v)) terminalIsTerminal).inv.app
          ((smallEtaleInverseImage i).obj F))
        (smallEtaleGlobalSectionPullback.{u, v} i g F
          (((Sheaf.ΓNatIsoSheafSections (Scheme.smallEtaleTopology X)
            (Type (max (u + 1) v)) terminalIsTerminal).hom.app F) s)) :=
  rfl

/-- The comparison map of Tag 09ZF is injective exactly when the presheaf-level pullback is: the
two maps conjugating them are components of natural isomorphisms. -/
public theorem injective_smallEtaleGlobalSectionsMapAt_iff :
    Function.Injective (smallEtaleGlobalSectionsMapAt.{u, v} i g F) ↔
      Function.Injective (smallEtaleGlobalSectionPullback.{u, v} i g F) := by
  have hX : Function.Bijective ((Sheaf.ΓNatIsoSheafSections (Scheme.smallEtaleTopology X)
      (Type (max (u + 1) v)) terminalIsTerminal).hom.app F) :=
    (isIso_iff_bijective _).mp inferInstance
  have hZ : Function.Bijective ((Sheaf.ΓNatIsoSheafSections (Scheme.smallEtaleTopology Z)
      (Type (max (u + 1) v)) terminalIsTerminal).inv.app
        ((smallEtaleInverseImage.{u, v} i).obj F)) :=
    (isIso_iff_bijective _).mp inferInstance
  constructor
  · intro h a b hab
    obtain ⟨s, rfl⟩ := hX.2 a
    obtain ⟨t, rfl⟩ := hX.2 b
    refine congrArg _ (h ?_)
    rw [smallEtaleGlobalSectionsMapAt_apply, smallEtaleGlobalSectionsMapAt_apply, hab]
  · intro h s t hst
    rw [smallEtaleGlobalSectionsMapAt_apply, smallEtaleGlobalSectionsMapAt_apply] at hst
    exact hX.1 (h (hZ.1 hst))

/-- **The injectivity half of Tag 09ZF, reduced to one statement.** Under hypothesis (1) of the
tag — restriction of global sections along `i` is surjective for every sheaf of sets on the
Zariski site of `X` — the comparison map on étale global sections is injective as soon as two
global sections with the same presheaf-level pullback agree, near every point of `Z`, over some
object of the small étale site whose image contains that point. -/
public theorem injective_smallEtaleGlobalSectionsMapAt_of_zariski
    (hZar : ∀ G : Sheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v)),
      Function.Surjective (zariskiGlobalSectionsMap.{u, v} i G))
    (hloc : ∀ a b : F.obj.obj (op (terminal X.Etale)),
      smallEtaleGlobalSectionPullback.{u, v} i g F a =
          smallEtaleGlobalSectionPullback.{u, v} i g F b →
        ∀ z : Z, ∃ W : X.Etale, GlobalSectionEqAt F a b W ∧ i.base z ∈ smallEtaleImage W) :
    Function.Injective (smallEtaleGlobalSectionsMapAt.{u, v} i g F) :=
  (injective_smallEtaleGlobalSectionsMapAt_iff i g F).mpr fun a b hab ↦
    eq_of_forall_exists_globalSectionEqAt i hZar F (hloc a b hab)

end Stacks.EtaleCohomology

end
