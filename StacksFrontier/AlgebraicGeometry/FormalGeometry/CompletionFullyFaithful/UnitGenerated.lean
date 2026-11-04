module

public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.NoetherianCoherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.DepthCriterion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.InternalHomCriterion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalPullback
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAmple
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic

/-!
# Full faithfulness of the completion functor on modules resolved by the structure sheaf

Let `X` be a locally Noetherian scheme and `I ⊆ 𝒪_X` a quasi-coherent ideal sheaf. Condition (3)
of [Stacks, Tag 0EKP] says that `Γ(X, F) ⟶ lim_n Γ(X, F / Iⁿ F)` is an isomorphism, and condition
(4) says that the completion functor `Coh(𝒪_X) ⟶ Coh(X, I)` of Stacks 0880 is fully faithful on
the finite locally free objects. This file proves the implication (3) `⟹` (4) between them, for a
single pair of coherent modules and in a form that is stronger in both arguments: condition (3)
is assumed at the *target* `F` only, and the *source* `G` is arbitrary coherent provided it is
resolved by the structure sheaf.

On a *quasi-affine* locally Noetherian scheme that resolution hypothesis is then discharged for
every coherent module, and the resulting implication is strengthened once more: condition (3) at
the structure sheaf alone already gives condition (4) in full. The step from `𝒪_X` to all finite
locally free modules is duality, through the identification of condition (4) at `(G, 𝒪_X)` with
condition (3) at `G^∨` of
`Stacks.Algebraization.bijective_completionFunctor_map_iff_isIso_globalSectionsToLimit`.

The source's proof of (3) `⟹` (4) applies condition (3) to the internal hom `SheafHom(G, F)` and
quotes Cohomology of Schemes, Lemma 0882. The proof here uses 0882 as well, but only through the
adjunction `Stacks.Algebraization.completionHomLimitEquiv`, which identifies a morphism of
completions `G^∧ ⟶ F^∧` with a morphism `G ⟶ lim_n F / Iⁿ F`; under that identification the
completion of a morphism is its composite with
`Stacks.Algebraization.completionToLimit`, so condition (4) at the pair `(G, F)` becomes
bijectivity of postcomposition with that one map on morphisms out of `G`. Condition (3) at `F` is
exactly the same bijectivity on morphisms out of `𝒪_X`, because morphisms out of the structure
sheaf are global sections. What remains is the passage from `𝒪_X` to `G`, which is a diagram
chase requiring no exactness of `Γ` and no universally exact sequence: bijectivity of
postcomposition with a fixed map is inherited by a coproduct of objects that have it, and by the
target of a presentation whose two terms have it.

## Main definitions

* `Stacks.Algebraization.unitHomEquivSections` — morphisms out of the structure sheaf are global
  sections.
* `Stacks.Algebraization.HasUnitPresentation` — a module admits a presentation
  `E' ⟶ E ⟶ M ⟶ 0` by direct sums of copies of the structure sheaf.

## Main results

* `Stacks.Algebraization.bijective_comp_right_of_iso`,
  `Stacks.Algebraization.bijective_comp_right_of_isColimit` and
  `Stacks.Algebraization.bijective_comp_right_of_presentation` — the three steps of the chase, in
  an arbitrary category: bijectivity of postcomposition with a fixed morphism is invariant under
  isomorphism of the source, passes to a coproduct, and passes from a presentation to the object
  presented. Only the last needs zero morphisms, and none needs an abelian category.
* `Stacks.Algebraization.bijective_comp_right_unit_of_isIso` — postcomposition with `c` is
  bijective on morphisms out of `𝒪_X` exactly when `c` is bijective on global sections.
* `Stacks.Algebraization.bijective_completionFunctor_map_iff_bijective_comp` — the completion
  functor on a hom set is postcomposition with `completionToLimit`.
* `Stacks.Algebraization.bijective_completionFunctor_map_of_isIso_globalSectionsToLimit` —
  **the implication (3) `⟹` (4) of [Stacks, Tag 0EKP]**, at one pair of coherent modules.
* `Stacks.Algebraization.exists_epi_unit_biproduct_of_isQuasiAffine` — on a quasi-affine scheme
  every quasi-coherent module of finite type is a quotient of a finite direct sum of copies of
  the structure sheaf: clause (8) of Stacks 01Q3 at the ample module `𝒪_X`.
* `Stacks.Algebraization.hasUnitPresentation_of_isQuasiAffine` — on a quasi-affine locally
  Noetherian scheme every coherent module *is* resolved by the structure sheaf.
* `Stacks.Algebraization.isIso_globalSectionsToLimit_of_isFiniteLocallyFree` — condition (3) at
  the structure sheaf implies condition (3) at every finite locally free coherent module, on a
  quasi-affine locally Noetherian scheme.
* `Stacks.Algebraization.completionFullyFaithfulOnFiniteLocallyFree_of_isIso_globalSectionsToLimit`
  — **condition (3) at the structure sheaf implies condition (4) of [Stacks, Tag 0EKP]**, on a
  quasi-affine locally Noetherian scheme.

## Implementation notes

The three steps of the chase are stated for an arbitrary category and an arbitrary morphism `c`,
which is all they use; in particular the surjectivity step needs only that `e` is an epimorphism
which is a cokernel of `d`, so no exactness properties of the category are involved.

`AlgebraicGeometry.Scheme.Modules` and `SheafOfModules X.ringCatSheaf` are two presentations of
one category, definitionally equal but not interchangeable for instance search: a zero morphism
between objects typed at the second presentation is not found. The summands of the direct sums in
`Stacks.Algebraization.HasUnitPresentation` are therefore given as a family of objects of
`X.Modules` each *isomorphic to* the structure sheaf rather than as the structure sheaf itself,
and `bijective_comp_right_of_iso` absorbs the difference. For the same reason
`bijective_completionFunctor_map_iff_bijective_comp` is assembled in term mode: `rw` does not
cross between the two presentations.

## How the presentation hypothesis is discharged

`bijective_completionFunctor_map_of_isIso_globalSectionsToLimit` asks for a presentation of the
source by direct sums of copies of `𝒪_X`. On a quasi-affine locally Noetherian scheme both halves
of such a presentation come from clause (8) of Stacks 01Q3 at `𝒪_X`, applied twice: first to the
module, then to the kernel of the epimorphism obtained. The clause needs its input quasi-coherent
of finite type, and that is how coherence is handled throughout here — by Stacks 01XZ, in the
scheme-level form
`Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_iff_isQuasicoherent_and_isFiniteType`, coherence
on a locally Noetherian scheme *is* quasi-coherence together with finite type, so no coherence
predicate of a site ever has to be transported. The direct sum produced by the clause
is finite locally free, by
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isBilimit_const` applied to the bilimit
bicone the clause delivers, hence quasi-coherent of finite type; the kernel is then
quasi-coherent by `Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel` and of finite type
by `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_kernel`, which is Stacks 01BY (2) on a
locally Noetherian scheme. The factorization property of the presentation holds because an
epimorphism in an abelian category is a cokernel of its kernel, `CategoryTheory.Abelian.epiDesc`.

## Duality

Condition (4) at the pair `(G, 𝒪_X)` is condition (3) at `SheafHom(G, 𝒪_X)`, and that internal
hom is the dual sheaf `G^∨` of `StacksFrontier/AlgebraicGeometry/Reflexive/Basic.lean` on the nose:
`(internalHomCoherent X G (unitCoherentModule X)).obj` and
`Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf (coherentObj G)` are definitionally equal, so
the identification needs no transport. Taking `G = F^∨`, which is again finite locally free by
Stacks 0FA7, condition (3) is obtained at `F^∨∨`, and a finite locally free coherent module on a
locally Noetherian scheme is reflexive. Carrying condition (3) back along that isomorphism is
`Stacks.Algebraization.isIso_globalSectionsToLimit_of_iso` (from
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.DepthCriterion`).

## References

* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Algebraization

/-! ### The chase -/

section Categorical

variable {C : Type*} [Category C]

/-- Injectivity of postcomposition with `c` passes from the source of an epimorphism to its
target. -/
public theorem injective_comp_right_of_epi {F L K E : C} (c : F ⟶ L) (q : E ⟶ K) [Epi q]
    (h : Function.Injective fun φ : E ⟶ F => φ ≫ c) :
    Function.Injective fun φ : K ⟶ F => φ ≫ c := by
  intro φ₁ φ₂ hh
  have hh' : φ₁ ≫ c = φ₂ ≫ c := hh
  refine (cancel_epi q).1 (h (show (q ≫ φ₁) ≫ c = (q ≫ φ₂) ≫ c from ?_))
  rw [Category.assoc, Category.assoc, hh']

/-- Bijectivity of postcomposition with `c` only depends on the isomorphism class of the
source. -/
public theorem bijective_comp_right_of_iso {A A' F L : C} (eA : A ≅ A') (c : F ⟶ L)
    (h : Function.Bijective fun φ : A' ⟶ F => φ ≫ c) :
    Function.Bijective fun φ : A ⟶ F => φ ≫ c := by
  refine ⟨injective_comp_right_of_epi c eA.inv h.1, fun ψ => ?_⟩
  obtain ⟨φ, hφ : φ ≫ c = eA.inv ≫ ψ⟩ := h.2 (eA.inv ≫ ψ)
  refine ⟨eA.hom ≫ φ, show (eA.hom ≫ φ) ≫ c = ψ from ?_⟩
  rw [Category.assoc, hφ, ← Category.assoc, eA.hom_inv_id, Category.id_comp]

/-- Postcomposition with `c` is bijective on morphisms out of a coproduct as soon as it is
bijective on morphisms out of each summand. -/
public theorem bijective_comp_right_of_isColimit {ι : Type*} {Y : ι → C}
    (t : Cocone (Discrete.functor Y)) (ht : IsColimit t) {F L : C} (c : F ⟶ L)
    (h : ∀ j : Discrete ι, Function.Bijective fun φ : (Discrete.functor Y).obj j ⟶ F => φ ≫ c) :
    Function.Bijective fun φ : t.pt ⟶ F => φ ≫ c := by
  refine ⟨fun φ₁ φ₂ (hh : φ₁ ≫ c = φ₂ ≫ c) => ht.hom_ext fun j => (h j).1
    (show (t.ι.app j ≫ φ₁) ≫ c = (t.ι.app j ≫ φ₂) ≫ c by
      rw [Category.assoc, Category.assoc, hh]), fun ψ => ?_⟩
  choose φ hφ using fun j : Discrete ι => (h j).2 (t.ι.app j ≫ ψ)
  refine ⟨ht.desc ⟨F, Discrete.natTrans φ⟩, show _ ≫ c = ψ from ht.hom_ext fun j => ?_⟩
  rw [← Category.assoc, ht.fac]
  exact hφ j

variable [HasZeroMorphisms C]

/-- **Postcomposition with `c` is bijective on an object presented by objects on which it is
bijective.** If `E' --d--> E --e--> G` is a presentation, that is `e` is an epimorphism which is a
cokernel of `d`, then bijectivity of postcomposition with `c` on morphisms out of `E` together
with injectivity on morphisms out of `E'` give bijectivity on morphisms out of `G`. -/
public theorem bijective_comp_right_of_presentation {F L G E E' : C} (c : F ⟶ L)
    (d : E' ⟶ E) (e : E ⟶ G) [Epi e] (hde : d ≫ e = 0)
    (hcoker : ∀ φ : E ⟶ F, d ≫ φ = 0 → ∃ χ : G ⟶ F, e ≫ χ = φ)
    (hE : Function.Bijective fun φ : E ⟶ F => φ ≫ c)
    (hE' : Function.Injective fun φ : E' ⟶ F => φ ≫ c) :
    Function.Bijective fun φ : G ⟶ F => φ ≫ c := by
  refine ⟨injective_comp_right_of_epi c e hE.1, fun ψ => ?_⟩
  obtain ⟨φ, hφ : φ ≫ c = e ≫ ψ⟩ := hE.2 (e ≫ ψ)
  have hz : d ≫ φ = 0 := by
    refine hE' (show (d ≫ φ) ≫ c = (0 : E' ⟶ F) ≫ c from ?_)
    rw [Category.assoc, hφ, ← Category.assoc, hde, zero_comp, zero_comp]
  obtain ⟨χ, hχ⟩ := hcoker φ hz
  refine ⟨χ, show χ ≫ c = ψ from (cancel_epi e).1 ?_⟩
  rw [← Category.assoc, hχ, hφ]

end Categorical

/-! ### Presentations by the structure sheaf -/

section Presentation

variable {X : Scheme.{u}}

/-- Morphisms out of the structure sheaf, as global sections. -/
public def unitHomEquivSections (M : X.Modules) :
    ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) ≃ Γ(M, (⊤ : X.Opens)) where
  toFun := globalSectionOfHom M
  invFun := homOfGlobalSection M
  left_inv := homOfGlobalSection_globalSectionOfHom M
  right_inv := globalSectionOfHom_homOfGlobalSection M

/-- **Postcomposition with `c` is bijective on morphisms out of the structure sheaf as soon as
`c` is bijective on global sections.** Morphisms out of the structure sheaf are global sections,
and under that identification postcomposition with `c` is the map `c` induces on global
sections. -/
public theorem bijective_comp_right_unit_of_isIso {M N : X.Modules} (c : M ⟶ N)
    (h : IsIso ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map c)) :
    Function.Bijective
      fun φ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M => φ ≫ c := by
  have hbij : Function.Bijective
      ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map c) :=
    ConcreteCategory.bijective_of_isIso _
  have hcomp : (fun φ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M => φ ≫ c) =
      (unitHomEquivSections N).symm ∘
        ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map c) ∘
          (unitHomEquivSections M) := by
    refine funext fun φ => ?_
    exact ((unitHomEquivSections N).symm_apply_apply (φ ≫ c)).symm.trans
      (congrArg (unitHomEquivSections N).symm (globalSectionOfHom_comp M φ c))
  rw [hcomp]
  exact (unitHomEquivSections N).symm.bijective.comp
    (hbij.comp (unitHomEquivSections M).bijective)

/-- **A presentation of a module by direct sums of copies of the structure sheaf**: a map `d`
between two such direct sums together with an epimorphism out of the target of `d` which is a
cokernel of `d`. The summands are given as a family isomorphic to the structure sheaf rather
than as the structure sheaf itself, which keeps the direct sums typed at
`AlgebraicGeometry.Scheme.Modules` rather than at the other presentation of that category. -/
public def HasUnitPresentation (M : X.Modules) : Prop :=
  ∃ (ι κ : Type u) (Y : ι → X.Modules) (Y' : κ → X.Modules)
    (_ : ∀ i, Nonempty (Y i ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules)))
    (_ : ∀ i, Nonempty (Y' i ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules)))
    (t : Cocone (Discrete.functor Y)) (_ : IsColimit t)
    (t' : Cocone (Discrete.functor Y')) (_ : IsColimit t')
    (d : t'.pt ⟶ t.pt) (e : t.pt ⟶ M) (_ : Epi e),
    d ≫ e = 0 ∧ ∀ (T : X.Modules) (φ : t.pt ⟶ T), d ≫ φ = 0 → ∃ χ : M ⟶ T, e ≫ χ = φ

/-- **Postcomposition with `c` is bijective on morphisms out of a module presented by the
structure sheaf as soon as it is bijective on morphisms out of the structure sheaf itself.** -/
public theorem bijective_comp_right_of_hasUnitPresentation {M : X.Modules}
    (hM : HasUnitPresentation M) {F L : X.Modules} (c : F ⟶ L)
    (h : Function.Bijective
      fun φ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ F => φ ≫ c) :
    Function.Bijective fun φ : M ⟶ F => φ ≫ c := by
  obtain ⟨ι, κ, Y, Y', hY, hY', t, ht, t', ht', d, e, he, hde, hcoker⟩ := hM
  have hE : Function.Bijective fun φ : t.pt ⟶ F => φ ≫ c :=
    bijective_comp_right_of_isColimit t ht c fun j =>
      bijective_comp_right_of_iso (hY j.as).some c h
  have hE' : Function.Bijective fun φ : t'.pt ⟶ F => φ ≫ c :=
    bijective_comp_right_of_isColimit t' ht' c fun j =>
      bijective_comp_right_of_iso (hY' j.as).some c h
  exact bijective_comp_right_of_presentation c d e hde (hcoker F) hE hE'.1

end Presentation

/-! ### Full faithfulness of the completion functor from the theorem on formal functions -/

section Completion

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
  (G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- **The completion functor on a hom set is postcomposition with the map into the limit of the
completion.** The identification of the two is `completionHomLimitEquiv`, the adjunction of
Stacks 0882, under which the completion of a morphism is the composite of that morphism with
`completionToLimit`. -/
public theorem bijective_completionFunctor_map_iff_bijective_comp :
    Function.Bijective ((completionFunctor X I).map :
        (G ⟶ F) → ((completionFunctor X I).obj G ⟶ (completionFunctor X I).obj F)) ↔
      Function.Bijective
        (fun φ : coherentObj G ⟶ coherentObj F => φ ≫ completionToLimit X I F) := by
  have hhom : Function.Bijective (fun g : G ⟶ F => g.hom) :=
    ⟨fun _ _ e => ObjectProperty.hom_ext _ e, fun g => ⟨ObjectProperty.homMk g, rfl⟩⟩
  have hmap : ((completionFunctor X I).map :
        (G ⟶ F) → ((completionFunctor X I).obj G ⟶ (completionFunctor X I).obj F)) =
      (fun ψ => completionHomLimitEquiv (I := I) G ((completionFunctor X I).obj F) ψ) ∘
        ((fun φ : coherentObj G ⟶ coherentObj F => φ ≫ completionToLimit X I F) ∘
          (fun g : G ⟶ F => g.hom)) :=
    funext fun g => (completionHomLimitEquiv_comp_completionToLimit I G F g).symm
  exact (congrArg Function.Bijective hmap).to_iff.trans
    (((completionHomLimitEquiv (I := I) G
          ((completionFunctor X I).obj F)).bijective.of_comp_iff' _).trans
      (Function.Bijective.of_comp_iff _ hhom))

/-- **The implication (3) implies (4) of [Stacks, Tag 0EKP], for a single pair of coherent
modules and in a strengthened form.** Let `X` be a locally Noetherian scheme and `I` a
quasi-coherent ideal sheaf. If the comparison of the theorem on formal functions in degree zero
`Γ(X, F) ⟶ lim_n Γ(X, F / Iⁿ F)` is an isomorphism for a coherent module `F`, then the completion
functor is bijective on the morphisms from `G` to `F` for *every* coherent module `G` admitting a
presentation by direct sums of copies of the structure sheaf.

The source's argument for (3) implies (4) goes the other way round: it applies condition (3) to
the internal hom `SheafHom(G, F)` and quotes Stacks 0882. Here condition (3) is used at `F`
alone, and `G` is resolved: morphisms out of the structure sheaf are global sections, so the
hypothesis says exactly that postcomposition with `completionToLimit` is bijective on morphisms
out of `𝒪_X`; that passes to direct sums of copies of `𝒪_X` because a coproduct is one, and from
a presentation `E' ⟶ E ⟶ G` to `G` itself because `e` is epic and is a cokernel of `d`. -/
public theorem bijective_completionFunctor_map_of_isIso_globalSectionsToLimit
    (hF : IsIso (globalSectionsToLimit I F)) (hG : HasUnitPresentation (coherentObj G)) :
    Function.Bijective ((completionFunctor X I).map :
      (G ⟶ F) → ((completionFunctor X I).obj G ⟶ (completionFunctor X I).obj F)) :=
  (bijective_completionFunctor_map_iff_bijective_comp I G F).2
    (bijective_comp_right_of_hasUnitPresentation hG (completionToLimit X I F)
      (bijective_comp_right_unit_of_isIso (completionToLimit X I F)
        (isIso_evaluation_completionToLimit I F hF)))

end Completion

/-! ### Presentations on a quasi-affine scheme -/

section QuasiAffine

variable {X : Scheme.{u}}

/-- On a quasi-affine scheme every quasi-coherent module of finite type is a quotient of a finite
direct sum of copies of the structure sheaf, and that direct sum is finite locally free. This is
clause (8) of Stacks 01Q3 at the ample module `𝒪_X` (Stacks 01QE), whose tensor powers are again
`𝒪_X`, together with `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isBilimit_const`
for the direct sum. -/
public theorem exists_epi_unit_biproduct_of_isQuasiAffine (hX : X.IsQuasiAffine) (G : X.Modules)
    (hqc : G.IsQuasicoherent)
    (hft : _root_.SheafOfModules.IsFiniteType.{u, u, u} G) :
    ∃ (ι : Type u) (_ : Finite ι) (Y : ι → X.Modules)
      (_ : ∀ i, Nonempty (Y i ≅ Stacks.Ample.unitModule X))
      (t : Cocone (Discrete.functor Y)) (_ : IsColimit t) (p : t.pt ⟶ G), Epi p ∧
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
          (R := X.ringCatSheaf) t.pt := by
  obtain ⟨-, hgen⟩ :=
    Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_exists_epi_biproduct_of_isAmple
      (Stacks.Ample.unitModule X)
      (Stacks.Ample.isAmple_unitModule_of_isQuasiAffine X hX)
  obtain ⟨n, ι, hfin, -, b, hb, p, hp⟩ := hgen G hqc hft
  have hrank := Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule
    X (Stacks.Ample.tensorPowModule X (Stacks.Ample.unitModule X) (-n))
  have hflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) (Stacks.Ample.tensorPowModule X (Stacks.Ample.unitModule X) (-n)) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      (M := Stacks.Ample.tensorPowModule X (Stacks.Ample.unitModule X) (-n)) (r := 1) (hM := hrank)
  exact ⟨ι, hfin, _, fun _ => ⟨(Stacks.Ample.unitTensorPowIso X (-n)).symm⟩, b.toCocone,
    hb.isColimit, p, hp,
    AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isBilimit_const (hfin := hfin) _
      (hM := hflf) hb⟩

/-- **Every coherent module on a quasi-affine locally Noetherian scheme has a presentation by
direct sums of copies of the structure sheaf.** Clause (8) of Stacks 01Q3 at `𝒪_X` presents the
module as a quotient of a finite direct sum of copies of `𝒪_X`; that direct sum is finite locally
free, hence quasi-coherent of finite type, so the kernel of the presentation is quasi-coherent
(a kernel of quasi-coherent modules is quasi-coherent) and of finite type (Stacks 01BY (2) on a
locally Noetherian scheme), and the clause applies to it in turn. The two epimorphisms compose
into the required `d`, and the factorization property holds because an epimorphism in an abelian
category is a cokernel of its kernel. -/
public theorem hasUnitPresentation_of_isQuasiAffine [IsLocallyNoetherian X]
    (hX : X.IsQuasiAffine) (M : X.Modules) (hqc : M.IsQuasicoherent)
    (hft : _root_.SheafOfModules.IsFiniteType.{u, u, u} M) :
    HasUnitPresentation M := by
  obtain ⟨ι, hfin, Y, hY, t, ht, p, hp, hflf⟩ :=
    exists_epi_unit_biproduct_of_isQuasiAffine hX M hqc hft
  obtain ⟨htqc, htft⟩ :=
    Stacks.AlgebraicGeometry.CoherentKernel.isQuasicoherent_isFiniteType_of_isFiniteLocallyFree
      (h := hflf) t.pt
  obtain ⟨κ, -, Y', hY', t', ht', q, hq, -⟩ :=
    exists_epi_unit_biproduct_of_isQuasiAffine hX (kernel p)
      (Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel p)
      (Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_kernel p)
  refine ⟨ι, κ, Y, Y', hY, hY', t, ht, t', ht', q ≫ kernel.ι p, p, hp, ?_, ?_⟩
  · rw [Category.assoc, kernel.condition, comp_zero]
  · intro T φ hφ
    have h0 : kernel.ι p ≫ φ = 0 := by
      refine (cancel_epi q).1 ?_
      rw [← Category.assoc, hφ, comp_zero]
    exact ⟨Abelian.epiDesc p φ h0, Abelian.comp_epiDesc p φ h0⟩

end QuasiAffine

/-! ### Condition (3) for the finite locally free modules, by duality -/

section Duality

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)

/-- **The comparison of the theorem on formal functions is an isomorphism exactly when the global
sections of the canonical map into the limit sheaf form one.** The two differ by the
identification `globalSectionsLimitIso` of the global sections of the limit with the limit of the
global sections. -/
public theorem isIso_globalSectionsToLimit_iff
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    IsIso (globalSectionsToLimit I F) ↔
      IsIso ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map
        (completionToLimit X I F)) :=
  ⟨isIso_evaluation_completionToLimit I F, fun h =>
    (congrArg IsIso (globalSectionsToLimit_eq I F)).to_iff.2
      (((@asIso _ _ _ _ _ h) ≪≫ globalSectionsLimitIso I F).isIso_hom)⟩

/-- **The dual of a finite locally free coherent module, as a coherent module.** The dual of a
finite locally free module is finite locally free (Stacks 0FA7), and on a locally Noetherian
scheme a finite locally free module is coherent. -/
public def dualCoherentModule
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) F.obj) :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
  haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf F.obj) :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf F.obj hF
  ⟨Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf F.obj,
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree X _⟩

/-- A finite locally free coherent module on a quasi-affine locally Noetherian scheme has a
presentation by direct sums of copies of the structure sheaf. -/
private theorem hasUnitPresentation_of_isFiniteLocallyFree (hX : X.IsQuasiAffine)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) F.obj) :
    HasUnitPresentation (coherentObj F) := by
  have : _root_.SheafOfModules.IsCoherent F.obj := F.property
  have hqcft :=
    Stacks.AlgebraicGeometry.CoherentKernel.isQuasicoherent_isFiniteType_of_isFiniteLocallyFree
      (h := hF) F.obj
  exact hasUnitPresentation_of_isQuasiAffine hX F.obj hqcft.1 hqcft.2

/-- **Condition (3) of [Stacks, Tag 0EKP] at the structure sheaf implies condition (3) at every
finite locally free coherent module**, on a quasi-affine locally Noetherian scheme.

The argument is duality. Condition (3) at `𝒪_X` gives, by
`bijective_completionFunctor_map_of_isIso_globalSectionsToLimit` and the presentation of
`hasUnitPresentation_of_isQuasiAffine`, that the completion functor is bijective on the morphisms
from any coherent module `G` into `𝒪_X`; by
`bijective_completionFunctor_map_iff_isIso_globalSectionsToLimit` that is condition (3) at
`SheafHom(G, 𝒪_X) = G^∨`. Taking `G = F^∨`, which is again finite locally free by Stacks 0FA7,
yields condition (3) at `F^∨∨`, and `F` is reflexive because it is finite locally free. -/
public theorem isIso_globalSectionsToLimit_of_isFiniteLocallyFree (hX : X.IsQuasiAffine)
    (hunit : IsIso (globalSectionsToLimit I (unitCoherentModule X)))
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) F.obj) :
    IsIso (globalSectionsToLimit I F) := by
  have hdflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf F.obj) :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf F.obj hF
  have hpres : HasUnitPresentation (coherentObj (dualCoherentModule F hF)) :=
    hasUnitPresentation_of_isFiniteLocallyFree hX (dualCoherentModule F hF) hdflf
  have hbij := bijective_completionFunctor_map_of_isIso_globalSectionsToLimit I
    (dualCoherentModule F hF) (unitCoherentModule X) hunit hpres
  have h3 := (bijective_completionFunctor_map_iff_isIso_globalSectionsToLimit I
    (dualCoherentModule F hF) (unitCoherentModule X)).1 hbij
  have hrefl : Stacks.AlgebraicGeometry.ReflexiveModules.IsReflexive F.obj :=
    Stacks.FundamentalGroup.ExtendedEtale.isReflexive_of_isFiniteLocallyFree F.obj
      ((Scheme.Modules.isFiniteLocallyFree_iff F.obj).2 hF)
  have e : F.obj ≅
      (internalHomCoherent X (dualCoherentModule F hF) (unitCoherentModule X)).obj :=
    @asIso _ _ _ _ (Stacks.AlgebraicGeometry.ReflexiveModules.toDoubleDual F.obj) hrefl
  exact isIso_globalSectionsToLimit_of_iso I (ObjectProperty.isoMk _ e).symm h3

/-- **Condition (3) of [Stacks, Tag 0EKP] at the structure sheaf implies condition (4)**, on a
quasi-affine locally Noetherian scheme: if the comparison
`Γ(X, 𝒪_X) ⟶ lim_n Γ(X, 𝒪_X / Iⁿ)` is an isomorphism, then the completion functor of Stacks 0880
is fully faithful on the finite locally free coherent modules.

Condition (3) propagates from `𝒪_X` to every finite locally free coherent module by
`isIso_globalSectionsToLimit_of_isFiniteLocallyFree`, and from there
`bijective_completionFunctor_map_of_isIso_globalSectionsToLimit` applies at each pair, the source
being presented by `hasUnitPresentation_of_isQuasiAffine`. -/
public theorem completionFullyFaithfulOnFiniteLocallyFree_of_isIso_globalSectionsToLimit
    (hX : X.IsQuasiAffine)
    (hunit : IsIso (globalSectionsToLimit I (unitCoherentModule X))) :
    CompletionFullyFaithfulOnFiniteLocallyFree X I := by
  intro F G hFfree hGfree
  exact bijective_completionFunctor_map_of_isIso_globalSectionsToLimit I F G
    (isIso_globalSectionsToLimit_of_isFiniteLocallyFree I hX hunit G hGfree)
    (hasUnitPresentation_of_isFiniteLocallyFree hX F hFfree)

end Duality

end Stacks.Algebraization

end
