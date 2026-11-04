module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.ShriekConstantFree
public import StacksCore.Tactic.StacksAttribute

/-!
# Constructible sheaves of modules are the finite cokernels of extensions by zero

Let `X` be a quasi-compact and quasi-separated scheme and `Λ` a Noetherian ring. A sheaf of
`Λ`-modules on `X_étale` is constructible exactly when it is the cokernel of a map
`⊕_j j_{V_j!}Λ ⟶ ⊕_i j_{U_i!}Λ` between finite direct sums of extensions by zero of constant free
rank-one module sheaves, the `U_i` and `V_j` being quasi-compact and quasi-separated — indeed
affine — objects of `X_étale`.

## Main results

* `AlgebraicGeometry.isConstructibleModuleSheaf_of_hasFiniteShriekPresentation` — a sheaf with a
  finite shriek presentation by constructible generators is constructible.
* `AlgebraicGeometry.hasFiniteShriekPresentation_of_isConstructibleModuleSheaf` — a constructible
  sheaf that is a quotient of a finite direct sum of the generators has a finite shriek
  presentation by them.
* `AlgebraicGeometry.hasFiniteShriekPresentation_qcqs_of_affine` — the affine presentation is a
  quasi-compact quasi-separated one.
* `AlgebraicGeometry.isConstructibleModuleSheaf_iff_hasFiniteShriekPresentation` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_iff_affineShriekPresentation` — **Stacks 095N** at
  its two presentations, the quasi-compact quasi-separated one and the affine one.

## Implementation notes

Both directions rest on the weak Serre property of the constructible sheaves of `Λ`-modules,
`AlgebraicGeometry.SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf` (Stacks 03RZ (3)): a
finite direct sum is an iterated extension of its summands, and the kernel and the cokernel of a
map between constructible sheaves are constructible.

Two inputs are carried as explicit hypotheses rather than proved, each a Stacks result this library
does not have at this site.

`hshriek` is the sheaves-of-modules case of **Stacks 03S8**, that `j_{U!}Λ` is constructible for
`U` a quasi-compact quasi-separated object of `X_étale`. The library has part (1) of that tag,
`AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda`, for sheaves of *sets*; by
`AlgebraicGeometry.moduleShriekConstantIsoFree` the module form is the free module sheaf on that
sheaf of sets, and nothing in the library carries constructibility across the free-module functor.

`hgen` is the finite generation step of the proof of Stacks 095N: a constructible sheaf of
`Λ`-modules is a quotient of a finite direct sum of extensions by zero. Its infinite form is
proved — `AlgebraicGeometry.epi_desc_moduleShriekConstant` surjects the direct sum over *all* pairs
of an étale object and a section of the sheaf over it onto the sheaf — and what `hgen` adds is that
finitely many pairs suffice. In the source that is the compactness of the constructible topology of
the spectral space `X`, applied to the supports of the cokernels of the partial sums; those
supports are constructible subsets by `AlgebraicGeometry.isConstructible_support_moduleSheaf`
(Stacks 09YS (3)), but that their intersection is empty is the finite generation of the geometric
stalks, which is not available here.

Granting `hgen`, the passage from a surjection to a presentation is what is proved below: the
kernel of a surjection from a finite direct sum of constructible generators is constructible, so
`hgen` applies to it again, and the composite of that second surjection with the inclusion of the
kernel has the given sheaf as its cokernel.

The universes are those of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.ShriekConstantPresentable`: the small
étale site of `B : BigEtaleSite.{u}` is a `Type (u + 1)` with `Category.{u}`, so the ring and the
module both live in `Type (u + 1)` and the universe lift occurring in
`AlgebraicGeometry.HasFiniteShriekPresentation` is a lift inside one universe, removed by
`ModuleCat.uliftFunctorSelfIso`.

## References

* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 09YS](https://stacks.math.columbia.edu/tag/09YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type (u + 1)) [CommRing R]

/-- A finite shriek presentation by affine étale objects is one by quasi-compact quasi-separated
étale objects: an affine scheme is a quasi-compact and quasi-separated space. -/
public theorem hasFiniteShriekPresentation_qcqs_of_affine
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
    (h : HasFiniteShriekPresentation.{u, u + 1, u + 1} B X R
      (SmallEtale.IsAffine B X.1 X.property) F) :
    HasFiniteShriekPresentation.{u, u + 1, u + 1} B X R
      (fun W ↦ CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj W) ∧
        QuasiSeparatedSpace ((SmallEtale.toScheme B X.1 X.property).obj W)) F := by
  have := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B X R
  obtain ⟨n, m, U, V, hU, hV, f, e⟩ := h
  refine ⟨n, m, U, V, fun i => ?_, fun j => ?_, f, e⟩
  · have := hU i
    exact ⟨inferInstance, inferInstance⟩
  · have := hV j
    exact ⟨inferInstance, inferInstance⟩

variable [IsNoetherianRing R]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) (ModuleCat.{u + 1} R)]

/-- The constructible sheaves of `R`-modules on `X_étale`, as a property of objects of the category
of sheaves of `R`-modules, at the universes of this file. -/
private abbrev constructibleModuleSheaves :
    ObjectProperty (Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)) :=
  fun F => IsConstructibleModuleSheaf B X R F

/-- The constructible sheaves of `R`-modules form a weak Serre subcategory; this is Stacks 03RZ (3)
with its coefficient universe pinned to the one of this file. -/
private instance isWeakSerreClass_constructibleModuleSheaves :
    (constructibleModuleSheaves B X R).IsWeakSerreClass :=
  SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, u + 1, u + 1} B X R

/-- A weak Serre subcategory is closed under finite coproducts: a binary coproduct is a binary
biproduct, hence an extension of one summand by the other. -/
private instance isClosedUnderFiniteCoproducts_constructibleModuleSheaves :
    (constructibleModuleSheaves B X R).IsClosedUnderFiniteCoproducts := by
  have : (constructibleModuleSheaves B X R).IsClosedUnderBinaryCoproducts :=
    ObjectProperty.IsClosedUnderColimitsOfShape.mk' (fun _ ⟨G, hG⟩ =>
      (constructibleModuleSheaves B X R).prop_of_iso
        ((biprod.isoCoprod _ _).trans (HasColimit.isoOfNatIso (diagramIsoPair G)).symm)
        ((constructibleModuleSheaves B X R).prop_biprod (hG ⟨.left⟩) (hG ⟨.right⟩)))
  exact ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

/-- A finite direct sum of the generators `j_{U!}Λ`, at objects satisfying `P`, is constructible. -/
private theorem isConstructibleModuleSheaf_sigma_moduleShriekConstant {n : ℕ}
    (P : SmallEtale B X.1 X.property → Prop)
    (hshriek : ∀ U : SmallEtale B X.1 X.property, P U →
      IsConstructibleModuleSheaf B X R (moduleShriekConstant.{u, u + 1, u + 1} B X R U))
    (U : Fin n → SmallEtale B X.1 X.property) (hU : ∀ i, P (U i)) :
    IsConstructibleModuleSheaf B X R
      (∐ fun i => moduleShriekConstant.{u, u + 1, u + 1} B X R (U i)) :=
  (constructibleModuleSheaves B X R).prop_coproduct fun i => hshriek _ (hU i)

/-- The universe lift of a sheaf, as occurring in `AlgebraicGeometry.HasFiniteShriekPresentation`,
is isomorphic to the underlying presheaf: at the universes of this file it is a lift inside one
universe. -/
private def uliftPresheafIso
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)) :
    F.obj ⋙ ModuleCat.uliftFunctor.{u + 1} R ≅ F.obj :=
  Functor.isoWhiskerLeft F.obj (ModuleCat.uliftFunctorSelfIso.{u + 1, u + 1} R) ≪≫
    F.obj.rightUnitor

/-- An isomorphism of underlying presheaves with the universe lift of a sheaf is an isomorphism of
sheaves. -/
private def isoOfPresheafIsoULift
    {G F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)}
    (e : G.obj ≅ F.obj ⋙ ModuleCat.uliftFunctor.{u + 1} R) : G ≅ F :=
  (sheafToPresheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)).preimageIso
    (e ≪≫ uliftPresheafIso B X R F)

/-- **The direction of Stacks 095N from a presentation to constructibility.** A sheaf of
`R`-modules with a finite shriek presentation whose generators `j_{U!}Λ` are constructible is
constructible: the two direct sums are finite, hence constructible, and the cokernel of a map
between constructible sheaves is constructible.

The hypothesis `hshriek` is the sheaves-of-modules case of Stacks 03S8. -/
public theorem isConstructibleModuleSheaf_of_hasFiniteShriekPresentation
    (P : SmallEtale B X.1 X.property → Prop)
    (hshriek : ∀ U : SmallEtale B X.1 X.property, P U →
      IsConstructibleModuleSheaf B X R (moduleShriekConstant.{u, u + 1, u + 1} B X R U))
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
    (h : HasFiniteShriekPresentation.{u, u + 1, u + 1} B X R P F) :
    IsConstructibleModuleSheaf B X R F := by
  have := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B X R
  obtain ⟨n, m, U, V, hU, hV, f, ⟨e⟩⟩ := h
  exact (constructibleModuleSheaves B X R).prop_of_iso (isoOfPresheafIsoULift B X R e)
    ((constructibleModuleSheaves B X R).prop_cokernel f
      (isConstructibleModuleSheaf_sigma_moduleShriekConstant B X R P hshriek V hV)
      (isConstructibleModuleSheaf_sigma_moduleShriekConstant B X R P hshriek U hU))

/-- **The direction of Stacks 095N from constructibility to a presentation**, granting `hgen`, that
every constructible sheaf of `R`-modules is a quotient of a finite direct sum of the generators
`j_{U!}Λ` at objects satisfying `P`.

Given a surjection `p : ⊕_i j_{U_i!}Λ ⟶ F`, its kernel is constructible, being the kernel of a map
between constructible sheaves, so `hgen` surjects a second finite direct sum `q` onto it. The
composite `q ≫ ker p` has cokernel `F`, because `p` is a cokernel of `ker p` and precomposing with
an epimorphism does not change a cokernel.

The hypotheses are `hshriek`, the sheaves-of-modules case of Stacks 03S8, and `hgen`; see the
module documentation. -/
public theorem hasFiniteShriekPresentation_of_isConstructibleModuleSheaf
    (P : SmallEtale B X.1 X.property → Prop)
    (hshriek : ∀ U : SmallEtale B X.1 X.property, P U →
      IsConstructibleModuleSheaf B X R (moduleShriekConstant.{u, u + 1, u + 1} B X R U))
    (hgen : ∀ G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R),
      IsConstructibleModuleSheaf B X R G →
        ∃ (n : ℕ) (U : Fin n → SmallEtale B X.1 X.property), (∀ i, P (U i)) ∧
          ∃ p : (∐ fun i => moduleShriekConstant.{u, u + 1, u + 1} B X R (U i)) ⟶ G, Epi p)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
    (hF : IsConstructibleModuleSheaf B X R F) :
    HasFiniteShriekPresentation.{u, u + 1, u + 1} B X R P F := by
  have := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B X R
  obtain ⟨n, U, hU, p, hp⟩ := hgen F hF
  have hsrc := isConstructibleModuleSheaf_sigma_moduleShriekConstant B X R P hshriek U hU
  have hker : IsConstructibleModuleSheaf B X R (kernel p) :=
    (constructibleModuleSheaves B X R).prop_kernel p hsrc hF
  obtain ⟨m, V, hV, q, hq⟩ := hgen (kernel p) hker
  refine ⟨n, m, U, V, hU, hV, q ≫ kernel.ι p, ⟨?_⟩⟩
  have hcolim : IsColimit (CokernelCofork.ofπ (f := q ≫ kernel.ι p) p
      (by rw [Category.assoc, kernel.condition, comp_zero])) :=
    isCokernelEpiComp (c := CokernelCofork.ofπ p (kernel.condition p))
      (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _)) q rfl
  have eF : cokernel (q ≫ kernel.ι p) ≅ F :=
    (colimit.isColimit _).coconePointUniqueUpToIso hcolim
  exact (sheafToPresheaf (SmallEtale.topology B X.1 X.property)
      (ModuleCat.{u + 1} R)).mapIso eF ≪≫ (uliftPresheafIso B X R F).symm

/-- **Stacks 095N, the quasi-compact quasi-separated presentation.** Let `X` be a quasi-compact and
quasi-separated scheme and `Λ` a Noetherian ring. A sheaf of `Λ`-modules on `X_étale` is
constructible exactly when it is the cokernel of a map between finite direct sums of extensions by
zero of constant free rank-one module sheaves at quasi-compact and quasi-separated objects of
`X_étale`.

The hypotheses `hshriek` and `hgen` are carried; see the module documentation. -/
@[stacks 095N "quasi-compact quasi-separated presentation, carrying as explicit hypotheses the \
sheaves-of-modules case of Stacks 03S8 (hshriek), that an extension by zero of a constant free \
rank-one module sheaf is constructible, and the finite generation step of the proof (hgen), that a \
constructible sheaf of modules is a quotient of a finite direct sum of such sheaves"]
public theorem isConstructibleModuleSheaf_iff_hasFiniteShriekPresentation
    [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    (hshriek : ∀ U : SmallEtale B X.1 X.property,
      CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj U) →
      QuasiSeparatedSpace ((SmallEtale.toScheme B X.1 X.property).obj U) →
      IsConstructibleModuleSheaf B X R (moduleShriekConstant.{u, u + 1, u + 1} B X R U))
    (hgen : ∀ G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R),
      IsConstructibleModuleSheaf B X R G →
        ∃ (n : ℕ) (U : Fin n → SmallEtale B X.1 X.property),
          (∀ i, CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj (U i)) ∧
            QuasiSeparatedSpace ((SmallEtale.toScheme B X.1 X.property).obj (U i))) ∧
          ∃ p : (∐ fun i => moduleShriekConstant.{u, u + 1, u + 1} B X R (U i)) ⟶ G, Epi p)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)) :
    IsConstructibleModuleSheaf B X R F ↔
      HasFiniteShriekPresentation.{u, u + 1, u + 1} B X R
        (fun W ↦ CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj W) ∧
          QuasiSeparatedSpace ((SmallEtale.toScheme B X.1 X.property).obj W)) F :=
  ⟨hasFiniteShriekPresentation_of_isConstructibleModuleSheaf B X R _
      (fun _ hW => hshriek _ hW.1 hW.2) hgen F,
    isConstructibleModuleSheaf_of_hasFiniteShriekPresentation B X R _
      (fun _ hW => hshriek _ hW.1 hW.2) F⟩

/-- **Stacks 095N, the affine presentation.** The étale objects of the presentation may be taken
affine: a sheaf of `Λ`-modules on `X_étale` is constructible exactly when it is the cokernel of a
map between finite direct sums of extensions by zero of constant free rank-one module sheaves at
affine objects of `X_étale`.

The hypotheses `hshriek` and `hgen` are carried; see the module documentation. The refinement of a
covering sieve of `X_étale` by a finite family with affine sources, which is what makes the affine
form of `hgen` reachable, is
`AlgebraicGeometry.SmallEtale.exists_finite_affine_refinement_of_mem_topology`. -/
@[stacks 095N "affine presentation, carrying as explicit hypotheses the sheaves-of-modules case of \
Stacks 03S8 at affine objects (hshriek) and the finite generation step of the proof by affine \
objects (hgen)"]
public theorem isConstructibleModuleSheaf_iff_affineShriekPresentation
    [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    (hshriek : ∀ U : SmallEtale B X.1 X.property, SmallEtale.IsAffine B X.1 X.property U →
      IsConstructibleModuleSheaf B X R (moduleShriekConstant.{u, u + 1, u + 1} B X R U))
    (hgen : ∀ G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R),
      IsConstructibleModuleSheaf B X R G →
        ∃ (n : ℕ) (U : Fin n → SmallEtale B X.1 X.property),
          (∀ i, SmallEtale.IsAffine B X.1 X.property (U i)) ∧
          ∃ p : (∐ fun i => moduleShriekConstant.{u, u + 1, u + 1} B X R (U i)) ⟶ G, Epi p)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)) :
    IsConstructibleModuleSheaf B X R F ↔
      HasFiniteShriekPresentation.{u, u + 1, u + 1} B X R
        (SmallEtale.IsAffine B X.1 X.property) F :=
  ⟨hasFiniteShriekPresentation_of_isConstructibleModuleSheaf B X R _ hshriek hgen F,
    isConstructibleModuleSheaf_of_hasFiniteShriekPresentation B X R _ hshriek F⟩

end AlgebraicGeometry

end
