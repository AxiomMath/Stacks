module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedPointInductionComparison

/-!
# Algebraization of formal sections, II: the global sections of a coherent module

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `U = Spec(A) ∖ V(𝔞)` and let `F` be a
coherent module on `U`. Stacks 0EG2 compares sections of `F` on *arbitrarily small* open
neighbourhoods of the formal locus `U ∩ V(I)` with the compatible families of sections of
`F / Iⁿ F` on all of `U`, that is, it makes

`Stacks.Algebraization.comparisonMap A I 𝔞 F : colim_V Γ(V, F) ⟶ lim_n Γ(U, F / Iⁿ F)`

an isomorphism under

1. `A` is `I`-adically complete and has a dualizing complex, and
2. whenever `x` is an associated point of `F` outside `V(I)` whose closure meets `V(I)` outside
   `V(𝔞)`, every `z ∈ closure {x} ∩ V(𝔞)` has `dim(𝒪_{closure {x}, z}) > cd(A, I) + 1`.

Stacks 0EIG upgrades the source of that comparison from the colimit to the honest global
sections `H⁰(U, F)`, under the additional

3. `depth(F_x) ≥ 2` for every `x ∈ U` whose closure meets `V(I)` only inside `V(𝔞)`.

That upgrade is what this file proves. The point is purely local-to-global: a neighbourhood `V`
of the formal locus misses only points `x` of `U` whose closure meets `V(I)` inside `V(𝔞)` —
otherwise the closure of `x` would contain a point of `U ∩ V(I) ⊆ V`, forcing `x` itself into
the open `V` — so condition (3) applies at every point of `U ∖ V` and Hartogs extension for
coherent modules of depth at least two, Stacks 0E9I, identifies `Γ(V, F)` with `Γ(U, F)`. Every
transition of the colimit system is then an isomorphism, so the colimit inclusion of `U` itself
is an isomorphism, and the composite with the comparison map of Stacks 0EG2 is the arrow of
Stacks 0EIG.

## Main definitions

* `Stacks.Algebraization.FormalSectionsII.topNearVanishing` — `U` itself, the largest
  neighbourhood of the formal locus, which is the initial object of the index category.
* `Stacks.Algebraization.FormalSectionsII.globalToFormalSections` — the arrow
  `H⁰(U, F) ⟶ lim H⁰(U, F / Iⁿ F)` of Stacks 0EIG.
* `Stacks.Algebraization.FormalSectionsII.DepthTwoOffFormalLocus` — condition (3). Conditions
  (1) and (2) are the library's own, from Stacks 0EIF and Stacks 0EG2: `IsAdicComplete`,
  `Dualizing.IsDualizingComplex` and
  `Stacks.Algebraization.AssociatedPointsClosureDimensionBound`.

## Main results

* `Stacks.Algebraization.FormalSectionsII.closure_inter_zeroLocus_subset_of_notMem` — a point of
  `U` outside a neighbourhood of the formal locus has its closure meeting `V(I)` only inside
  `V(𝔞)`. This is the step that turns condition (3) into a depth hypothesis on `U ∖ V`.
* `Stacks.Algebraization.FormalSectionsII.isIso_sectionsNearVanishing_map_fromTop` — under
  condition (3) restriction `Γ(U, F) ⟶ Γ(V, F)` is an isomorphism, by Stacks 0E9I.
* `Stacks.Algebraization.FormalSectionsII.isIso_colimit_ι_topNearVanishing` — when all those
  restrictions are isomorphisms the colimit inclusion of `U` is an isomorphism.
* `Stacks.Algebraization.FormalSectionsII.globalToFormalSections_proj` — the arrow of Stacks 0EIG
  is canonical: its `n`-th component is reduction modulo `Iⁿ` on all of `U`.
* `Stacks.Algebraization.FormalSectionsII.isIso_globalToFormalSections` — **Stacks 0EIG**.

## Implementation notes

### Nothing of Stacks 0EG2 is assumed here

Stacks 0EG2 is *applied*, not carried: conditions (1) and (2) of Stacks 0EIG assemble into
`Stacks.Algebraization.BootstrapHypotheses` and
`Stacks.Algebraization.isIso_comparisonMap` makes the comparison map an isomorphism. Condition
(3) is used, and used only, for the collapse of the colimit.

What `Stacks.Algebraization.isIso_comparisonMap` itself carries —
`Stacks.Algebraization.SerreOneAlternativeComparison` (Stacks 0EIF),
`Stacks.Algebraization.MiddleComparisonOfShortExact` (the middle clause of Stacks 0H48) and
`Stacks.Algebraization.AssociatedPointSplitting` (the short exact sequence the source assembles
from Stacks 0BK0, 0DX3 and 0AW0) — is passed through unchanged, in the generality in which that
statement asks for it. None of the three mentions the global sections `Γ(U, F)`, so none is the
conclusion of Stacks 0EIG; and because they are precisely the hypotheses the library's
Stacks 0EG2 already carries, Stacks 0EIG as stated here adds no assumption of its own on top of
conditions (1), (2) and (3).

Condition (2) is `Stacks.Algebraization.AssociatedPointsClosureDimensionBound`, the chapter's
own transcription, not a copy: the dimension of `𝒪_{closure {x}, z}` is
`Stacks.Algebraization.closureLocalDimension`, the Krull dimension of the interval of primes
between `x` and `z`, compared with `cd(A, I) + 1` in `EInt` through
`Stacks.Algebraization.krullDimToEInt`, and the hypothesis `closure {x} ∩ V(I) ⊄ V(𝔞)` is the
existence of a prime containing `x` and `I` but not `𝔞`.

### Why the colimit collapses

The index category `Stacks.Algebraization.OpensNearVanishing` is ordered by *reverse*
inclusion, so `U` itself is its initial object and there is a canonical arrow
`topNearVanishing ⟶ V` for every neighbourhood `V`. Its morphisms are `PLift`s of a
proposition, hence unique, which is all that
`Stacks.Algebraization.FormalSectionsII.isIso_colimit_ι_topNearVanishing` uses: the inverses of
the restrictions assemble into a cocone because the triangle over the initial object commutes
on the nose.

Condition (3) is transcribed with the same `Module` structure on the stalk of `F` that
Stacks 0E9I uses, namely
`PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier`, so that the
depth hypothesis of that statement is matched on the nose and no bridge between two stalk module
structures is needed.

## References

* [Stacks Project, Tag 0EIG](https://stacks.math.columbia.edu/tag/0EIG)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 0H48](https://stacks.math.columbia.edu/tag/0H48)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization.FormalSectionsII

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (I a : Ideal A)
  (F : (complementZeroLocus A a : Scheme).Modules)

/-! ### The largest neighbourhood of the formal locus -/

/-- `U = Spec(A) ∖ V(𝔞)` itself, as the largest neighbourhood of the formal locus `U ∩ V(I)`.
Since `Stacks.Algebraization.OpensNearVanishing` is ordered by reverse inclusion, this is the
initial object of that index category. -/
def topNearVanishing : OpensNearVanishing A I a :=
  ⟨⊤, fun _ _ => trivial⟩

/-- The canonical arrow from `U` to a neighbourhood `V` of the formal locus. -/
def fromTopNearVanishing (V : OpensNearVanishing A I a) : topNearVanishing A I a ⟶ V :=
  ⟨le_top⟩

/-- Any two parallel arrows of `Stacks.Algebraization.OpensNearVanishing` agree: an arrow is a
`PLift` of a proposition. -/
theorem hom_ext_opensNearVanishing {V W : OpensNearVanishing A I a} (f g : V ⟶ W) : f = g :=
  congrArg PLift.up (proof_irrel f.down g.down)

/-! ### The colimit over the neighbourhoods collapses -/

/-- **The colimit over the neighbourhoods of the formal locus collapses to its value on `U`**
whenever every restriction `Γ(U, F) ⟶ Γ(V, F)` is an isomorphism.

The inverses of those restrictions form a cocone, because `U` is the initial object of the
index category and that category's parallel arrows agree; the induced arrow out of the colimit
is a two-sided inverse of the colimit inclusion of `U`. -/
theorem isIso_colimit_ι_topNearVanishing
    (h : ∀ V : OpensNearVanishing A I a,
      IsIso ((sectionsNearVanishing A I a F).map (fromTopNearVanishing A I a V))) :
    IsIso (colimit.ι (sectionsNearVanishing A I a F) (topNearVanishing A I a)) := by
  have hmapcomp : ∀ {V W : OpensNearVanishing A I a} (f : V ⟶ W),
      (sectionsNearVanishing A I a F).map (fromTopNearVanishing A I a V) ≫
          (sectionsNearVanishing A I a F).map f =
        (sectionsNearVanishing A I a F).map (fromTopNearVanishing A I a W) := by
    intro V W f
    rw [← Functor.map_comp]
    exact congrArg (sectionsNearVanishing A I a F).map
      (hom_ext_opensNearVanishing A I a _ _)
  let c : Cocone (sectionsNearVanishing A I a F) :=
    { pt := (sectionsNearVanishing A I a F).obj (topNearVanishing A I a)
      ι :=
      { app := fun V =>
          inv ((sectionsNearVanishing A I a F).map (fromTopNearVanishing A I a V))
        naturality := fun V W f => by
          have key : (sectionsNearVanishing A I a F).map f ≫
              inv ((sectionsNearVanishing A I a F).map (fromTopNearVanishing A I a W)) =
                inv ((sectionsNearVanishing A I a F).map
                  (fromTopNearVanishing A I a V)) := by
            rw [← cancel_epi ((sectionsNearVanishing A I a F).map
              (fromTopNearVanishing A I a V)), ← Category.assoc, hmapcomp f]
            simp
          simpa using key } }
  refine ⟨colimit.desc (sectionsNearVanishing A I a F) c, ?_, ?_⟩
  · have htop : fromTopNearVanishing A I a (topNearVanishing A I a) = 𝟙 _ :=
      hom_ext_opensNearVanishing A I a _ _
    rw [colimit.ι_desc]
    show inv ((sectionsNearVanishing A I a F).map
      (fromTopNearVanishing A I a (topNearVanishing A I a))) = 𝟙 _
    simp [htop]
  · refine colimit.hom_ext fun V => ?_
    rw [← Category.assoc, colimit.ι_desc]
    show inv ((sectionsNearVanishing A I a F).map (fromTopNearVanishing A I a V)) ≫
      colimit.ι (sectionsNearVanishing A I a F) (topNearVanishing A I a) = _
    rw [Category.comp_id, ← colimit.w (sectionsNearVanishing A I a F)
      (fromTopNearVanishing A I a V), ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-! ### Condition (3) and the Hartogs step -/

/-- **Condition (3) of Stacks 0EIG.** For every point `x` of `U = Spec(A) ∖ V(𝔞)` whose closure
meets `V(I)` only inside `V(𝔞)`, the stalk of `F` at `x` has depth at least `2`. -/
def DepthTwoOffFormalLocus : Prop :=
  ∀ x : (complementZeroLocus A a : Scheme),
    closure ({(x.1 : PrimeSpectrum A)} : Set (PrimeSpectrum A)) ∩
        PrimeSpectrum.zeroLocus (I : Set A) ⊆ PrimeSpectrum.zeroLocus (a : Set A) →
      let M := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
      letI : Module ((complementZeroLocus A a : Scheme).presheaf.stalk x) M :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          F.val x
      (2 : ℕ∞) ≤ Module.depth ((complementZeroLocus A a : Scheme).presheaf.stalk x)
        (IsLocalRing.maximalIdeal ((complementZeroLocus A a : Scheme).presheaf.stalk x)) M

/-- **A point of `U` outside a neighbourhood `V` of the formal locus has its closure meeting
`V(I)` only inside `V(𝔞)`.**

Were there a prime `y ⊇ x` with `I ≤ y` and `𝔞 ⊄ y`, then `y` would be a point of
`U ∩ V(I)`, hence of `V`; but `y` lies in the closure of `x` and `V` is open, so `x` would lie
in `V` as well. This is the step that lets condition (3) of Stacks 0EIG apply at every point of
`U ∖ V`. -/
theorem closure_inter_zeroLocus_subset_of_notMem (V : OpensNearVanishing A I a)
    {x : (complementZeroLocus A a : Scheme)} (hx : x ∉ V.openSet) :
    closure ({(x.1 : PrimeSpectrum A)} : Set (PrimeSpectrum A)) ∩
        PrimeSpectrum.zeroLocus (I : Set A) ⊆ PrimeSpectrum.zeroLocus (a : Set A) := by
  intro y hy
  by_contra hya
  let yX : (complementZeroLocus A a : Scheme) := ⟨y, hya⟩
  have hyI : I ≤ y.asIdeal :=
    SetLike.coe_subset_coe.mp ((PrimeSpectrum.mem_zeroLocus y (I : Set A)).1 hy.2)
  have hyV : yX ∈ V.openSet := V.contains_vanishing yX hyI
  have hspec : x ⤳ yX :=
    (subtype_specializes_iff x yX).2 (specializes_iff_mem_closure.mpr hy.1)
  exact hx (hspec.mem_open V.openSet.isOpen hyV)

/-- **Restriction from `U` to a neighbourhood of the formal locus is an isomorphism**, under
condition (3) of Stacks 0EIG.

By `Stacks.Algebraization.FormalSectionsII.closure_inter_zeroLocus_subset_of_notMem` condition
(3) bounds the depth of `F` below by `2` at every point of `U ∖ V`, which is the hypothesis of
Hartogs extension for coherent modules, Stacks 0E9I, in the form
`AlgebraicGeometry.restriction_bijective_of_depth_ge_two`. -/
theorem isIso_sectionsNearVanishing_map_fromTop [IsNoetherianRing A] [F.IsCoherent]
    (hdepth : DepthTwoOffFormalLocus A I a F) (V : OpensNearVanishing A I a) :
    IsIso ((sectionsNearVanishing A I a F).map (fromTopNearVanishing A I a V)) := by
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  exact AlgebraicGeometry.restriction_bijective_of_depth_ge_two _ F V.openSet
    fun x hx => hdepth x (closure_inter_zeroLocus_subset_of_notMem A I a V hx)

/-! ### The arrow of Stacks 0EIG -/

/-- **The arrow of Stacks 0EIG**, from the global sections `H⁰(U, F)` of `F` on
`U = Spec(A) ∖ V(𝔞)` to the compatible families of sections of `F / Iⁿ F` on `U`. It is the
comparison map of Stacks 0EG2 precomposed with the colimit inclusion of the largest
neighbourhood `U` of the formal locus. -/
def globalToFormalSections : Γ(F, ⊤) ⟶ limit (formalSections A I a F) :=
  colimit.ι (sectionsNearVanishing A I a F) (topNearVanishing A I a) ≫ comparisonMap A I a F

/-- **The arrow of Stacks 0EIG is canonical**: its `n`-th component is reduction modulo `Iⁿ` of
a global section of `F` on `U`, not an arbitrary arrow into the limit. -/
@[stacks 0EIG "canonicality of the displayed arrow: its n-th component is reduction mod I^n"]
theorem globalToFormalSections_proj (n : ℕ) :
    globalToFormalSections A I a F ≫ limit.π (formalSections A I a F) (op n) =
      (adicProj (idealSheafNearVanishing A I a) F (op n)).app ⊤ := by
  have hres : ((quotientSystemNearVanishing A I a F).obj (op n)).presheaf.map
        (homOfLE (show (⊤ : (complementZeroLocus A a : Scheme).Opens) ≤ ⊤ from le_top)).op =
      𝟙 ((formalSections A I a F).obj (op n)) :=
    ((quotientSystemNearVanishing A I a F).obj (op n)).presheaf.map_id (op ⊤)
  have h : colimit.ι (sectionsNearVanishing A I a F) (topNearVanishing A I a) ≫
      comparisonMap A I a F ≫ limit.π (formalSections A I a F) (op n) ≫
        ((quotientSystemNearVanishing A I a F).obj (op n)).presheaf.map
          (homOfLE (show (⊤ : (complementZeroLocus A a : Scheme).Opens) ≤ ⊤ from le_top)).op =
      (adicProj (idealSheafNearVanishing A I a) F (op n)).app ⊤ :=
    comparisonMap_restrict A I a F (topNearVanishing A I a) n
  rw [hres] at h
  have hπ : limit.π (formalSections A I a F) (op n) ≫
      𝟙 ((formalSections A I a F).obj (op n)) = limit.π (formalSections A I a F) (op n) :=
    Category.comp_id _
  have key : colimit.ι (sectionsNearVanishing A I a F) (topNearVanishing A I a) ≫
      comparisonMap A I a F ≫ limit.π (formalSections A I a F) (op n) =
      (adicProj (idealSheafNearVanishing A I a) F (op n)).app ⊤ :=
    (congrArg (fun k => colimit.ι (sectionsNearVanishing A I a F) (topNearVanishing A I a) ≫
      comparisonMap A I a F ≫ k) hπ).symm.trans h
  rw [globalToFormalSections]
  exact (Category.assoc _ _ _).trans key

/-- **Stacks 0EIG.** Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` and let `F` be a coherent
module on `U = Spec(A) ∖ V(𝔞)`. Assume

1. `A` is `I`-adically complete and has a dualizing complex,
2. whenever `x` is an associated point of `F` outside `V(I)` whose closure meets `V(I)` outside
   `V(𝔞)`, every `z ∈ closure {x} ∩ V(𝔞)` has `dim(𝒪_{closure {x}, z}) > cd(A, I) + 1`, and
3. `depth(F_x) ≥ 2` for every `x ∈ U` whose closure meets `V(I)` only inside `V(𝔞)`.

Then `H⁰(U, F) ⟶ lim H⁰(U, F / Iⁿ F)` is an isomorphism.

What is proved here is the content of Stacks 0EIG over Stacks 0EG2: a point of `U` missed by a
neighbourhood `V` of the formal locus has its closure meeting `V(I)` only inside `V(𝔞)`, so
condition (3) bounds the depth of `F` below by `2` on all of `U ∖ V`, Hartogs extension for
coherent modules — Stacks 0E9I — makes every restriction `Γ(U, F) ⟶ Γ(V, F)` an isomorphism,
and the colimit therefore collapses onto its value at `U`.

Conditions (1) and (2) are consumed only by `Stacks.Algebraization.isIso_comparisonMap`, the
library's Stacks 0EG2, which is *applied* here: they assemble into its
`Stacks.Algebraization.BootstrapHypotheses` on the nose. The three remaining arguments are that
statement's own carried hypotheses, passed through unchanged and granting nothing about
Stacks 0EIG:

* `Stacks.Algebraization.SerreOneAlternativeComparison` grants Stacks 0EIF — the comparison map
  is an isomorphism for a coherent module that additionally satisfies the third condition of
  that lemma, the condition Stacks 0EG2 removes;
* `Stacks.Algebraization.MiddleComparisonOfShortExact` grants the middle clause of
  Stacks 0H48 — the middle comparison of a short exact sequence is an isomorphism once the
  outer two are;
* `Stacks.Algebraization.AssociatedPointSplitting` grants the short exact sequence the source
  assembles from Stacks 0BK0, 0DX3 and 0AW0, in which no comparison map occurs at all.

None of the three mentions the global sections `Γ(U, F)`, so none of them is this conclusion;
and since they are exactly the hypotheses the library's Stacks 0EG2 already carries, this
statement adds no assumption of its own beyond conditions (1), (2) and (3). -/
@[stacks 0EIG "H^0(U,F) = lim H^0(U,F/I^nF); 0EG2 applied, its 3 hypotheses passed through"]
theorem isIso_globalToFormalSections [IsNoetherianRing A] [F.IsCoherent]
    (hIa : I ≤ a) (hcomplete : IsAdicComplete I A)
    (hdualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (hdim : AssociatedPointsClosureDimensionBound A I a F)
    (hdepth : DepthTwoOffFormalLocus A I a F)
    (hEIF : SerreOneAlternativeComparison.{u}) (h48 : MiddleComparisonOfShortExact.{u})
    (hsplit : AssociatedPointSplitting A I a) :
    IsIso (globalToFormalSections A I a F) := by
  rw [globalToFormalSections]
  exact IsIso.comp_isIso'
    (isIso_colimit_ι_topNearVanishing A I a F
      (isIso_sectionsNearVanishing_map_fromTop A I a F hdepth))
    (isIso_comparisonMap A I a F ⟨hIa, hcomplete, hdualizing, hdim⟩ hEIF h48 hsplit)

end Stacks.Algebraization.FormalSectionsII

end
