module

public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.FibreImmersion
public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.FibreMorphismRestrict
public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.RestrictRestrict
public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Generation
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctions
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.VanishingSystemImmersion.Restriction

/-!
# Stacks Tag 0D2N from the lifting of a generating family off the fibre

[Stacks, Tag 0D2N] says that an invertible module `ℒ` on a scheme `X` proper over a locally
Noetherian base `S`, ample on the scheme-theoretic fibre `X_y` over a point `y : S`, is relatively
ample over some open neighbourhood of `y`.  This file assembles that statement from the one input
the repository does not yet have: **the lifting property**, that for all large `d` every finite
family of global sections of `(f.fiberι y)^*(ℒ ^⊗ d)` is the restriction to the fibre of a family
of sections of `ℒ ^⊗ d` over `f ⁻¹ᵁ U`, for some open `U ∋ y`.  That property is assertion (B) of
[Stacks, Tag 0D2M] after the reduction to the local ring of the base; it is treated separately and
is taken here as the hypothesis `hlift` of
`Stacks.AmpleFibreNeighbourhood.exists_mem_isRelativelyAmple_of_exists_lift`.

Everything else in the source's proof is already in the repository, and this file only puts the
pieces in the order the source does.

## Main results

* `Stacks.AmpleFibreNeighbourhood.exists_mem_isRelativelyAmple_of_exists_lift`: **[Stacks, Tag
  0D2N] from the lifting property.** For `f : X ⟶ S` proper onto a locally Noetherian base and
  `ℒ` invertible on `X` and ample on the fibre `X_y`, the point `y` has an open neighbourhood
  `V ⊆ S` with `ℒ|_{f⁻¹V}` ample relative to `f⁻¹V ⟶ V`.
* `Stacks.AmpleFibreNeighbourhood.exists_mem_generatesStalks_restrict`: **the shrinking step of
  the source's proof, for sections given over the preimage of a neighbourhood.** If the family of
  restrictions to `X_y` of sections of an invertible `ℳ` over `f ⁻¹ᵁ U` generates the stalks of
  `ℳ|_{X_y}`, then some open `W` of `U` has the property that the family generates the stalks of
  `ℳ|_{f⁻¹U}` over the whole of `(f ∣_ U)⁻¹W`.
* `Stacks.AmpleFibreNeighbourhood.fibreToRestrict` and
  `Stacks.AmpleFibreNeighbourhood.fibreToRestrictRestrict`, with
  `fibreToRestrict_comp_ι`, `fibreToRestrictRestrict_comp_ι`, `comp_fibreToRestrictRestrict` and
  `exists_isPreimmersion_fibreToRestrictRestrict_comp`: the fibre `X_y` as a scheme over
  `f ⁻¹ᵁ U` and over `(f ∣_ U)⁻¹W`, compatibly with the inclusions into `X` and with the
  structure morphism to `Spec κ(y)`.
* `Stacks.AmpleFibreNeighbourhood.liftedFamilyIso` and
  `Stacks.AmpleFibreNeighbourhood.app_liftedFamilyIso`: the comparison that carries the
  restriction to `X_y` of a section of `ℒ ^⊗ d` over `f ⁻¹ᵁ U` to the restriction, to `X_y`, of
  the same section read as a global section of the twisted module on `(f ∣_ U)⁻¹W`.  This is the
  computation that identifies the family produced on the fibre with the one the endgame consumes.
* `Stacks.AmpleFibreNeighbourhood.pullbackCompIsoOfEq`, with
  `app_pullbackCompIsoOfEq_pullbackSection` and `app_pullbackCompIsoOfEq`: the comparison of
  `p^*q^*ℳ` with `v^*ℳ` for a factorization `v = p ≫ q`, and the two statements that it carries a
  twofold restriction of a section to the restriction along `v`.
* `Stacks.AmpleFibreNeighbourhood.injective_base_of_iso` and
  `Stacks.AmpleFibreNeighbourhood.injective_base_comp`: injectivity on points of an isomorphism
  of schemes and of a composite, proved by hand because the morphisms they are applied to below
  live over a point written as a structure literal, where instance resolution does not see
  through the identification of the carrier of `U.toScheme` with `U`.

## The route, step by step, and where each input lives

Write `𝒪(d) := Stacks.Ample.tensorPowModule X L d` and `ℒ_y := ℒ|_{X_y}`.

1. **The family on the fibre, [Stacks, Tag 01VS].**  The statement
   `exists_generatesStalks_isImmersion_toProjectiveSpaceOver_of_isAmple` of this namespace
   (`AmpleFibreNeighbourhood/FibreImmersion.lean`), applied to the structure morphism
   `f.fiberToSpecResidueField y` of the fibre and to `ℒ_y`, gives a `d₀ ≥ 1` such that every
   `d ≥ d₀` admits an `r` and a family `t : Fin (r+1) → Γ((ℒ_y) ^⊗ d, ⊤)` generating the stalks
   whose attached morphism `X_y ⟶ ℙʳ_{κ(y)}` ([Stacks, Tag 01ND],
   `Stacks.ProjectiveFromSections.toProjectiveSpaceOver`) is an immersion.  Its hypothesis
   `LocallyOfFiniteType (f.fiberToSpecResidueField y)` is an instance, the fibre being a base
   change of the proper `f`; invertibility of `ℒ_y` is [Stacks, Tag 0B8P],
   `Stacks.InvertiblePullback.isInvertibleModule_pullback`.

2. **The two spellings of the twisted module on the fibre.**  `t` lives on `(ℒ_y) ^⊗ d` while
   `hlift` speaks of `(f.fiberι y)^*𝒪(d)`; the two are identified by
   `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso`, at an integer
   exponent, and generation of the stalks is invariant under that identification by
   `Stacks.ProductFamilyTwist.generatesStalks_congr`.

3. **The lift.**  `hlift` is applied at a `d : ℕ` which is at least `1`, at least the `d₀` of
   step 1 and at least the `d₀` of `hlift`, to the family of step 2.  It returns an open `U ∋ y`
   and `a : Fin (r+1) → Γ(𝒪(d), f ⁻¹ᵁ U)` restricting on the fibre to that family.

4. **Shrinking the base so that the lifted family generates everywhere.**
   `Stacks.AmpleFibreNeighbourhood.exists_mem_generatesStalks_restrict` below packages
   `Stacks.AmpleFibreNeighbourhood.exists_mem_generatesStalks_pullbackGlobalSections`
   (`FibreImmersion.lean`, the sentence "`X_y ⊆ U = ⋃ X_{sᵢ}`, and since `X ⟶ Y` is closed we can
   find an open neighbourhood `V` of `y` with `f⁻¹(V) ⊆ U`" of the source) for sections given only
   over `f ⁻¹ᵁ U`.  The hypothesis of that lemma — at every point of the fibre some member of the
   family does not vanish — is read off generation on `X_y` through
   `Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks`,
   `Stacks.RatioPullback.nvOpen_pullbackGlobalSections` ([Stacks, Tag 0H78]) and
   `AlgebraicGeometry.Scheme.Hom.range_fiberι`, the fibre of `f ∣_ U` being identified with the
   fibre of `f` by `Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso`.  The output is an
   open `W` of `U.toScheme`.

5. **The endgame, over the twice-restricted morphism.**
   `Stacks.AmpleFibreNeighbourhood.exists_mem_isRelativelyAmple_toProjectiveSpaceOver`
   (`FibreImmersion.lean`) is applied to `(f ∣_ U) ∣_ W` and to the lifted family carried onto
   `((ℒ|_{f⁻¹U})|_{(f ∣_ U)⁻¹W}) ^⊗ d` by two further applications of
   `pullbackTensorPowModuleIntIso`.  Its hypothesis — finiteness of the set-theoretic fibres of
   the attached morphism `φ` over the points of `ℙʳ` above the base point — is discharged by
   `Stacks.AmpleFibreNeighbourhood.subsingleton_preimage_of_fibreFactorization`, which asks only
   for an injective factorization of the restriction of `φ` to the fibre and not for an immersion.
   That factorization is `Stacks.ProjectiveFromSections.comp_toProjectiveSpaceOver` applied along
   `Stacks.AmpleFibreNeighbourhood.fibreToRestrictRestrict`, whose attached morphism to
   `ℙʳ_{κ(y)}` is the immersion of step 1: that identification is
   `Stacks.AmpleFibreNeighbourhood.app_liftedFamilyIso` turned into an equality of morphisms by
   `Stacks.AmpleFibreNeighbourhood.toProjectiveSpaceOver_congr` and
   `Stacks.AmpleFibreNeighbourhood.toProjectiveSpaceOver_congr_family`.  Injectivity of the second
   factor comes from `AlgebraicGeometry.isPullback_projectiveSpaceOverMap`, which presents
   `AlgebraicGeometry.projectiveSpaceOverMap r u` as a base change of the preimmersion `u` that
   `Stacks.AmpleFibreNeighbourhood.exists_isPreimmersion_fibreToRestrictRestrict_comp` produces.

6. **Back to an open of `S`.**  The conclusion of step 5 is relative ampleness over an open of
   `W.toScheme`, three restrictions deep.  Two applications of
   `Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_morphismRestrict_image`
   (`AmpleFibreNeighbourhood/RestrictRestrict.lean`) collapse `((f ∣_ U) ∣_ W) ∣_ V'` to
   `f ∣_ (U.ι ''ᵁ (W.ι ''ᵁ V'))`, which is the open of `S` the statement asks for.

## No attribute, and why

**No `@[stacks]` attribute is attached here.**  The statement below is [Stacks, Tag 0D2N] with
assertion (B) of [Stacks, Tag 0D2M] — in the shape in which the proof of Tag 0D2N consumes it —
still a hypothesis, so it is not yet the assertion of the tag.  The attribute is attached
downstream, on the statement that results once `hlift` has been discharged.

## References

* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Ample Stacks.AmpleProjectiveImmersion
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence (pullbackTensorPowModuleIntIso)
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.ProjectiveFromSections

universe u

namespace Stacks.AmpleFibreNeighbourhood

/-! ### Three pieces of bookkeeping -/

/-- **Restricting a global section along a morphism, over the whole source, is
`AlgebraicGeometry.pullbackGlobalSections`.**  Both sides are the image of the section under the
unit of `f^* ⊣ f_*`, read over `⊤`: for `AlgebraicGeometry.Scheme.Modules.pullbackSection` that is
`AlgebraicGeometry.Scheme.Modules.pullbackSection_top`, the restriction map it postcomposes with
being the identity because both opens are `⊤`, and for `AlgebraicGeometry.pullbackGlobalSections`
it is `AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_unit`.

Both spellings occur among the inputs of this file — the lifting hypothesis delivers a
`pullbackSection` over `f ⁻¹ᵁ U`, while the shrinking lemma and
`Stacks.ProjectiveFromSections.comp_toProjectiveSpaceOver` speak of `pullbackGlobalSections` — so
the bridge between them is used repeatedly below. -/
theorem pullbackSection_top_eq_pullbackGlobalSections {X Y : Scheme.{u}} (g : Y ⟶ X)
    (M : X.Modules) (h : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ (⊤ : X.Opens)) (s : Γ(M, ⊤)) :
    Scheme.Modules.pullbackSection g M ⊤ ⊤ h s = pullbackGlobalSections g M s :=
  (Scheme.Modules.pullbackSection_top g M h s).trans
    (SectionsEqualizer.pullbackGlobalSections_unit g M s).symm

/-- **An identity between global sections across an isomorphism of modules, read backwards.**  If
`e` carries `x` to `z` then `e⁻¹` carries `z` back to `x`.  This is
`AlgebraicGeometry.SectionsEqualizer.moduleIso_hom_inv_app` applied to `e.symm`, whose homonym in
the other direction is `private` where it is proved. -/
theorem app_inv_of_app_hom {Z : Scheme.{u}} {A B : Z.Modules} (e : A ≅ B) {x : Γ(A, ⊤)}
    {z : Γ(B, ⊤)} (h : e.hom.app ⊤ x = z) : e.inv.app ⊤ z = x :=
  (congrArg (fun w => e.inv.app ⊤ w) h.symm).trans
    (SectionsEqualizer.moduleIso_hom_inv_app e.symm x)

/-- **The [Stacks, Tag 01ND] morphism depends on the generating family and not on the proof that
it generates.**  Two generating families that are equal as families define the same morphism to
projective space over the base: substituting the equality leaves two proofs of one proposition,
and those are equal by proof irrelevance.

This is the companion of `Stacks.AmpleFibreNeighbourhood.toProjectiveSpaceOver_congr`, which moves
the family across an isomorphism of the module carrying it; here the module is fixed and only the
description of the family changes, which is what happens when a computation rewrites each
member. -/
theorem toProjectiveSpaceOver_congr_family {X S : Scheme.{u}} (f : X ⟶ S) {r : ℕ}
    {M : X.Modules} [IsInvertibleModule X M] {s s' : Fin (r + 1) → Γ(M, ⊤)} (hss : s = s')
    (hs : GeneratesStalks s) (hs' : GeneratesStalks s') :
    toProjectiveSpaceOver s hs f = toProjectiveSpaceOver s' hs' f := by
  subst hss
  rfl

/-- **The underlying map of an isomorphism of schemes is injective.**  Its inverse's underlying
map is a left inverse, by `CategoryTheory.Iso.hom_inv_id`.

This is stated for an arbitrary isomorphism, and used below at the identifications of fibres
`Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso`.  It is proved rather than obtained from
the instance `AlgebraicGeometry.IsPreimmersion`, which an isomorphism of course is, because the
fibres in question are taken at a point written as `⟨y, hyU⟩`, and instance resolution does not
see through the identification of the carrier of `U.toScheme` with `U` at the transparency it
uses — the same obstruction recorded in `AmpleFibreNeighbourhood/FibreMorphismRestrict.lean`. -/
theorem injective_base_of_iso {A B : Scheme.{u}} (e : A ≅ B) : Function.Injective e.hom.base := by
  have h : Function.LeftInverse e.inv.base e.hom.base := fun p => by simp
  exact h.injective

/-- **The underlying map of a composite of morphisms with injective underlying maps is
injective.**  Stated separately so that it can be applied to composites whose factors live over
points written as structure literals, where `simp` on the composite is unreliable. -/
theorem injective_base_comp {A B C : Scheme.{u}} (g : A ⟶ B) (h : B ⟶ C)
    (hg : Function.Injective g.base) (hh : Function.Injective h.base) :
    Function.Injective (g ≫ h).base :=
  fun _ _ hpq => hg (hh (by simpa using hpq))

/-! ### Restricting a section along a factorized morphism -/

/-- **The comparison of `p^*q^*ℳ` with `v^*ℳ` for a factorization `v = p ≫ q`.**  It is the
pseudofunctoriality isomorphism `AlgebraicGeometry.Scheme.Modules.pullbackComp` followed by the
transport `AlgebraicGeometry.Scheme.Modules.pullbackCongr` along the equality of morphisms.

Both comparisons the assembly of [Stacks, Tag 0D2N] needs are of this shape: the fibre `X_y` maps
into `f ⁻¹ᵁ U` compatibly with `f.fiberι y`
(`Stacks.AmpleFibreNeighbourhood.fibreToRestrict_comp_ι`), and into `(f ∣_ U)⁻¹W` compatibly with
that map (`Stacks.AmpleFibreNeighbourhood.fibreToRestrictRestrict_comp_ι`). -/
def pullbackCompIsoOfEq {A B C : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C) {v : A ⟶ C}
    (hv : p ≫ q = v) (M : C.Modules) :
    (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj M) ≅
      (Scheme.Modules.pullback v).obj M :=
  (Scheme.Modules.pullbackComp p q).app M ≪≫ (Scheme.Modules.pullbackCongr hv).app M

/-- **`Stacks.AmpleFibreNeighbourhood.pullbackCompIsoOfEq` carries a twofold restriction of a
section to the restriction along the composite.**  A section of `ℳ` over an open `V` of `C`,
restricted to the whole preimage of `V` under `q` and then restricted along `p`, becomes the
restriction of the section along `v = p ≫ q`.

This is `AlgebraicGeometry.Scheme.Modules.pullbackSection_comp` followed by
`AlgebraicGeometry.Scheme.Modules.pullbackSection_congr`, with
`Stacks.AmpleFibreNeighbourhood.pullbackSection_top_eq_pullbackGlobalSections` turning the outer
restriction into the global-sections map. -/
theorem app_pullbackCompIsoOfEq_pullbackSection {A B C : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C)
    {v : A ⟶ C} (hv : p ≫ q = v) (M : C.Modules) (V : C.Opens)
    (hq : (⊤ : B.Opens) ≤ q ⁻¹ᵁ V) (hvV : (⊤ : A.Opens) ≤ v ⁻¹ᵁ V) (s : Γ(M, V)) :
    (pullbackCompIsoOfEq p q hv M).hom.app ⊤
        (pullbackGlobalSections p ((Scheme.Modules.pullback q).obj M)
          (Scheme.Modules.pullbackSection q M V ⊤ hq s)) =
      Scheme.Modules.pullbackSection v M V ⊤ hvV s := by
  have hpq : (⊤ : A.Opens) ≤ (p ≫ q) ⁻¹ᵁ V := by rwa [hv]
  have hptop : (⊤ : A.Opens) ≤ p ⁻¹ᵁ (⊤ : B.Opens) := by simp
  exact Eq.trans
    (congrArg
      (fun z => ((Scheme.Modules.pullbackCongr hv).app M).hom.app ⊤
        (((Scheme.Modules.pullbackComp p q).app M).hom.app ⊤ z))
      (pullbackSection_top_eq_pullbackGlobalSections p
        ((Scheme.Modules.pullback q).obj M) hptop
        (Scheme.Modules.pullbackSection q M V ⊤ hq s)).symm)
    (Eq.trans
      (congrArg (fun z => ((Scheme.Modules.pullbackCongr hv).app M).hom.app ⊤ z)
        (Scheme.Modules.pullbackSection_comp p q M V ⊤ ⊤ hq hptop hpq s))
      (Scheme.Modules.pullbackSection_congr hv M V ⊤ hpq hvV s))

/-- **The global-sections case of
`Stacks.AmpleFibreNeighbourhood.app_pullbackCompIsoOfEq_pullbackSection`.**  Restricting a global
section along `q` and then along `p` is restricting it along `v = p ≫ q`, once
`Stacks.AmpleFibreNeighbourhood.pullbackCompIsoOfEq` has identified the two modules.  It is
`AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp` followed by
`AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_congr`. -/
theorem app_pullbackCompIsoOfEq {A B C : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C) {v : A ⟶ C}
    (hv : p ≫ q = v) (M : C.Modules) (s : Γ(M, ⊤)) :
    (pullbackCompIsoOfEq p q hv M).hom.app ⊤
        (pullbackGlobalSections p ((Scheme.Modules.pullback q).obj M)
          (pullbackGlobalSections q M s)) =
      pullbackGlobalSections v M s :=
  (congrArg (fun z => ((Scheme.Modules.pullbackCongr hv).app M).hom.app ⊤ z)
      (SectionsEqualizer.pullbackGlobalSections_comp p q M s)).trans
    (SectionsEqualizer.pullbackGlobalSections_congr hv M s)

/-- The inverse comparison carries the restriction along `v = p ≫ q` to the twofold restriction. -/
private theorem inv_app_pullbackCompIsoOfEq_pullbackSection {A B C : Scheme.{u}} (p : A ⟶ B)
    (q : B ⟶ C) {v : A ⟶ C} (hv : p ≫ q = v) (M : C.Modules) (V : C.Opens)
    (hq : (⊤ : B.Opens) ≤ q ⁻¹ᵁ V) (hvV : (⊤ : A.Opens) ≤ v ⁻¹ᵁ V) (s : Γ(M, V)) :
    (pullbackCompIsoOfEq p q hv M).inv.app ⊤ (Scheme.Modules.pullbackSection v M V ⊤ hvV s) =
      pullbackGlobalSections p ((Scheme.Modules.pullback q).obj M)
        (Scheme.Modules.pullbackSection q M V ⊤ hq s) :=
  app_inv_of_app_hom _ (app_pullbackCompIsoOfEq_pullbackSection p q hv M V hq hvV s)

/-! ### The fibre as a scheme over the restrictions of `f` -/

variable {X S : Scheme.{u}}

/-- **The fibre `X_y` as a scheme over `f ⁻¹ᵁ U`, for `U` an open neighbourhood of `y`.**  The
whole of `X_y` lies over `y ∈ U`, hence inside `f ⁻¹ᵁ U`; concretely the morphism is the
identification `Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso` of `X_y` with the fibre
of `f ∣_ U` at `y`, followed by the inclusion of that fibre into `f ⁻¹ᵁ U`. -/
def fibreToRestrict (f : X ⟶ S) (y : S) {U : S.Opens} (hyU : y ∈ U) :
    f.fiber y ⟶ (f ⁻¹ᵁ U).toScheme :=
  (fiberMorphismRestrictIso f U y hyU).inv ≫ (f ∣_ U).fiberι (⟨y, hyU⟩ : U.toScheme)

/-- `Stacks.AmpleFibreNeighbourhood.fibreToRestrict`, followed by the inclusion of `f ⁻¹ᵁ U` into
`X`, is the inclusion `f.fiberι y` of the fibre.  This is
`Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso_inv_comp_fiberι`. -/
theorem fibreToRestrict_comp_ι (f : X ⟶ S) (y : S) {U : S.Opens} (hyU : y ∈ U) :
    fibreToRestrict f y hyU ≫ (f ⁻¹ᵁ U).ι = f.fiberι y := by
  show ((fiberMorphismRestrictIso f U y hyU).inv ≫
    (f ∣_ U).fiberι (⟨y, hyU⟩ : U.toScheme)) ≫ (f ⁻¹ᵁ U).ι = f.fiberι y
  rw [Category.assoc]
  exact fiberMorphismRestrictIso_inv_comp_fiberι f U y hyU

/-- **The fibre `X_y` as a scheme over `(f ∣_ U)⁻¹W`, for `W` an open of `U.toScheme` containing
`y`.**  It is `Stacks.AmpleFibreNeighbourhood.fibreToRestrict` one level further down: the two
identifications of fibres of `Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso` followed by
the inclusion of the fibre of `(f ∣_ U) ∣_ W` into `(f ∣_ U)⁻¹W`. -/
def fibreToRestrictRestrict (f : X ⟶ S) (y : S) {U : S.Opens} (hyU : y ∈ U)
    {W : U.toScheme.Opens} (hyW : (⟨y, hyU⟩ : U.toScheme) ∈ W) :
    f.fiber y ⟶ ((f ∣_ U) ⁻¹ᵁ W).toScheme :=
  (fiberMorphismRestrictIso f U y hyU).inv ≫
    (fiberMorphismRestrictIso (f ∣_ U) W (⟨y, hyU⟩ : U.toScheme) hyW).inv ≫
      ((f ∣_ U) ∣_ W).fiberι (⟨⟨y, hyU⟩, hyW⟩ : W.toScheme)

/-- `Stacks.AmpleFibreNeighbourhood.fibreToRestrictRestrict`, followed by the inclusion of
`(f ∣_ U)⁻¹W` into `f ⁻¹ᵁ U`, is `Stacks.AmpleFibreNeighbourhood.fibreToRestrict`.  This is
`Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso_inv_comp_fiberι` for `f ∣_ U` and `W`. -/
theorem fibreToRestrictRestrict_comp_ι (f : X ⟶ S) (y : S) {U : S.Opens} (hyU : y ∈ U)
    {W : U.toScheme.Opens} (hyW : (⟨y, hyU⟩ : U.toScheme) ∈ W) :
    fibreToRestrictRestrict f y hyU hyW ≫ ((f ∣_ U) ⁻¹ᵁ W).ι = fibreToRestrict f y hyU := by
  show ((fiberMorphismRestrictIso f U y hyU).inv ≫
        (fiberMorphismRestrictIso (f ∣_ U) W (⟨y, hyU⟩ : U.toScheme) hyW).inv ≫
          ((f ∣_ U) ∣_ W).fiberι (⟨⟨y, hyU⟩, hyW⟩ : W.toScheme)) ≫ ((f ∣_ U) ⁻¹ᵁ W).ι =
      (fiberMorphismRestrictIso f U y hyU).inv ≫ (f ∣_ U).fiberι (⟨y, hyU⟩ : U.toScheme)
  simp only [Category.assoc]
  rw [fiberMorphismRestrictIso_inv_comp_fiberι (f ∣_ U) W (⟨y, hyU⟩ : U.toScheme) hyW]

/-- **`Stacks.AmpleFibreNeighbourhood.fibreToRestrictRestrict` is the inclusion of the fibre of
`(f ∣_ U) ∣_ W`, read through the two identifications of fibres.**  Composing it with the two
isomorphisms `Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso` cancels them, by
`CategoryTheory.Iso.hom_inv_id`. -/
theorem comp_fibreToRestrictRestrict (f : X ⟶ S) (y : S) {U : S.Opens} (hyU : y ∈ U)
    {W : U.toScheme.Opens} (hyW : (⟨y, hyU⟩ : U.toScheme) ∈ W) :
    (fiberMorphismRestrictIso (f ∣_ U) W (⟨y, hyU⟩ : U.toScheme) hyW).hom ≫
        (fiberMorphismRestrictIso f U y hyU).hom ≫ fibreToRestrictRestrict f y hyU hyW =
      ((f ∣_ U) ∣_ W).fiberι (⟨⟨y, hyU⟩, hyW⟩ : W.toScheme) := by
  show (fiberMorphismRestrictIso (f ∣_ U) W (⟨y, hyU⟩ : U.toScheme) hyW).hom ≫
      (fiberMorphismRestrictIso f U y hyU).hom ≫
        (fiberMorphismRestrictIso f U y hyU).inv ≫
          (fiberMorphismRestrictIso (f ∣_ U) W (⟨y, hyU⟩ : U.toScheme) hyW).inv ≫
            ((f ∣_ U) ∣_ W).fiberι (⟨⟨y, hyU⟩, hyW⟩ : W.toScheme) =
    ((f ∣_ U) ∣_ W).fiberι (⟨⟨y, hyU⟩, hyW⟩ : W.toScheme)
  simp only [Iso.hom_inv_id_assoc]

/-- **`Stacks.AmpleFibreNeighbourhood.fibreToRestrictRestrict` lies over a preimmersion
`Spec κ(y) ⟶ W.toScheme`.**  The fibre of `f` at `y`, mapped into `(f ∣_ U)⁻¹W` and then down to
`W.toScheme`, is the structure morphism `X_y ⟶ Spec κ(y)` followed by a morphism
`Spec κ(y) ⟶ W.toScheme`, which is moreover a preimmersion.

The morphism is produced, not named, and the residue field of `W.toScheme` at `y` is never
mentioned: `AlgebraicGeometry.Scheme.fromSpecResidueField` at `y` has range the single point `y`
(`AlgebraicGeometry.Scheme.range_fromSpecResidueField`), which lies in the range of the open
immersion `W.ι ≫ U.ι`, so `AlgebraicGeometry.IsOpenImmersion.lift` factors it through
`W.toScheme`.  That factor is a preimmersion by
`AlgebraicGeometry.IsPreimmersion.of_comp`, its composite with `W.ι ≫ U.ι` being
`AlgebraicGeometry.Scheme.fromSpecResidueField`, which is one.

The square itself is checked after composing with the monomorphism `W.ι ≫ U.ι`
(`CategoryTheory.cancel_mono`), where both sides become `f.fiberι y ≫ f`: on the left by
`AlgebraicGeometry.morphismRestrict_ι` twice together with
`Stacks.AmpleFibreNeighbourhood.fibreToRestrictRestrict_comp_ι` and
`Stacks.AmpleFibreNeighbourhood.fibreToRestrict_comp_ι`, on the right by
`AlgebraicGeometry.Scheme.Hom.fiber_fac` and
`AlgebraicGeometry.IsOpenImmersion.lift_fac`.

This is the square `Stacks.ProjectiveFromSections.comp_toProjectiveSpaceOver` consumes: it
compares the morphism to `ℙʳ_{κ(y)}` attached to a family on the fibre with the one attached to a
family on `(f ∣_ U)⁻¹W`, and the preimmersion is what makes the comparison morphism
`AlgebraicGeometry.projectiveSpaceOverMap r u` injective on points. -/
theorem exists_isPreimmersion_fibreToRestrictRestrict_comp (f : X ⟶ S) (y : S) {U : S.Opens}
    (hyU : y ∈ U) {W : U.toScheme.Opens} (hyW : (⟨y, hyU⟩ : U.toScheme) ∈ W) :
    ∃ u : Spec (S.residueField y) ⟶ W.toScheme, IsPreimmersion u ∧
      fibreToRestrictRestrict f y hyU hyW ≫ ((f ∣_ U) ∣_ W) =
        f.fiberToSpecResidueField y ≫ u := by
  have hyim : y ∈ Set.range (W.ι ≫ U.ι).base :=
    ⟨(⟨⟨y, hyU⟩, hyW⟩ : W.toScheme), rfl⟩
  have hrange : Set.range (S.fromSpecResidueField y).base ⊆
      Set.range (W.ι ≫ U.ι).base := by
    rw [Scheme.range_fromSpecResidueField]
    exact Set.singleton_subset_iff.mpr hyim
  have hfac : IsOpenImmersion.lift (W.ι ≫ U.ι) (S.fromSpecResidueField y) hrange ≫
      (W.ι ≫ U.ι) = S.fromSpecResidueField y :=
    IsOpenImmersion.lift_fac (W.ι ≫ U.ι) (S.fromSpecResidueField y) hrange
  refine ⟨IsOpenImmersion.lift (W.ι ≫ U.ι) (S.fromSpecResidueField y) hrange, ?_, ?_⟩
  · have : IsPreimmersion (IsOpenImmersion.lift (W.ι ≫ U.ι) (S.fromSpecResidueField y) hrange ≫
        (W.ι ≫ U.ι)) := by
      rw [hfac]
      infer_instance
    exact IsPreimmersion.of_comp _ (W.ι ≫ U.ι)
  · rw [← cancel_mono (W.ι ≫ U.ι)]
    simp only [Category.assoc, hfac, morphismRestrict_ι_assoc, morphismRestrict_ι]
    rw [← Scheme.Hom.fiber_fac, ← fibreToRestrict_comp_ι f y hyU,
      ← fibreToRestrictRestrict_comp_ι f y hyU hyW]
    simp only [Category.assoc]

/-! ### Carrying the lifted family onto the twice-restricted scheme -/

/-- **`(ℒ|_{f⁻¹U}|_{(f ∣_ U)⁻¹W}) ^⊗ d` is `(ℒ ^⊗ d)|_{f⁻¹U}|_{(f ∣_ U)⁻¹W}`**, for an integer
exponent `d`.  Two applications of
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso`, one for each of
the two open immersions. -/
def restrictRestrictTwistIso (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L] {U : S.Opens}
    (W : U.toScheme.Opens) (d : ℤ) :
    (Scheme.Modules.pullback ((f ∣_ U) ⁻¹ᵁ W).ι).obj
        ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj (tensorPowModule X L d)) ≅
      tensorPowModule ((f ∣_ U) ⁻¹ᵁ W).toScheme
        (pullbackModule ((f ∣_ U) ⁻¹ᵁ W).ι (pullbackModule (f ⁻¹ᵁ U).ι L)) d :=
  (Scheme.Modules.pullback ((f ∣_ U) ⁻¹ᵁ W).ι).mapIso
      (pullbackTensorPowModuleIntIso (f ⁻¹ᵁ U).ι L d) ≪≫
    pullbackTensorPowModuleIntIso ((f ∣_ U) ⁻¹ᵁ W).ι (pullbackModule (f ⁻¹ᵁ U).ι L) d

/-- **The comparison of `(ℒ ^⊗ d)|_{X_y}` with the restriction to `X_y` of the twisted module of
the twice-restricted scheme.**  It is `Stacks.AmpleFibreNeighbourhood.pullbackCompIsoOfEq` for the
two factorizations `Stacks.AmpleFibreNeighbourhood.fibreToRestrict_comp_ι` and
`Stacks.AmpleFibreNeighbourhood.fibreToRestrictRestrict_comp_ι`, followed by
`Stacks.AmpleFibreNeighbourhood.restrictRestrictTwistIso` pulled back to the fibre.

What it is for is `Stacks.AmpleFibreNeighbourhood.app_liftedFamilyIso`: a section of `ℒ ^⊗ d` over
`f ⁻¹ᵁ U` has two restrictions to `X_y`, the direct one and the one that goes through
`(f ∣_ U)⁻¹W`, and this isomorphism carries the first to the second. -/
def liftedFamilyIso (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L] (y : S) {U : S.Opens}
    (hyU : y ∈ U) {W : U.toScheme.Opens} (hyW : (⟨y, hyU⟩ : U.toScheme) ∈ W) (d : ℤ) :
    (Scheme.Modules.pullback (f.fiberι y)).obj (tensorPowModule X L d) ≅
      (Scheme.Modules.pullback (fibreToRestrictRestrict f y hyU hyW)).obj
        (tensorPowModule ((f ∣_ U) ⁻¹ᵁ W).toScheme
          (pullbackModule ((f ∣_ U) ⁻¹ᵁ W).ι (pullbackModule (f ⁻¹ᵁ U).ι L)) d) :=
  (pullbackCompIsoOfEq (fibreToRestrict f y hyU) (f ⁻¹ᵁ U).ι
        (fibreToRestrict_comp_ι f y hyU) (tensorPowModule X L d)).symm ≪≫
    (pullbackCompIsoOfEq (fibreToRestrictRestrict f y hyU hyW) ((f ∣_ U) ⁻¹ᵁ W).ι
          (fibreToRestrictRestrict_comp_ι f y hyU hyW)
          ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj (tensorPowModule X L d))).symm ≪≫
      (Scheme.Modules.pullback (fibreToRestrictRestrict f y hyU hyW)).mapIso
        (restrictRestrictTwistIso f L W d)

/-- **The two restrictions to `X_y` of a section of `ℒ ^⊗ d` over `f ⁻¹ᵁ U` agree**, under
`Stacks.AmpleFibreNeighbourhood.liftedFamilyIso`.  On the left the section is restricted straight
to the fibre; on the right it is first read as a global section of `(ℒ ^⊗ d)|_{f⁻¹U}`, then
restricted to `(f ∣_ U)⁻¹W` and carried onto the twisted module there by
`Stacks.AmpleFibreNeighbourhood.restrictRestrictTwistIso`, and only then restricted to the fibre.

Each of the three steps is one of the lemmas above:
`Stacks.AmpleFibreNeighbourhood.app_pullbackCompIsoOfEq_pullbackSection` for the passage through
`f ⁻¹ᵁ U`, `Stacks.AmpleFibreNeighbourhood.app_pullbackCompIsoOfEq` for the passage through
`(f ∣_ U)⁻¹W`, and `AlgebraicGeometry.pullbackGlobalSections_natural` for the twisting
isomorphism; `Stacks.AmpleFibreNeighbourhood.app_inv_of_app_hom` reads the first two backwards.

This is the identity that makes the family the proof of [Stacks, Tag 0D2N] chooses on the fibre —
whose attached morphism to `ℙʳ_{κ(y)}` is an immersion — the restriction to the fibre of the
family the endgame of the proof consumes on `(f ∣_ U)⁻¹W`. -/
theorem app_liftedFamilyIso (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L] (y : S)
    {U : S.Opens} (hyU : y ∈ U) {W : U.toScheme.Opens} (hyW : (⟨y, hyU⟩ : U.toScheme) ∈ W)
    (d : ℤ) (hU : (⊤ : (f ⁻¹ᵁ U).toScheme.Opens) ≤ (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U))
    (a : Γ(tensorPowModule X L d, f ⁻¹ᵁ U)) :
    (liftedFamilyIso f L y hyU hyW d).hom.app ⊤
        (Scheme.Modules.pullbackSection (f.fiberι y) (tensorPowModule X L d) (f ⁻¹ᵁ U) ⊤
          (Stacks.FormalFunctions.top_le_preimage_fiberι f y U hyU) a) =
      pullbackGlobalSections (fibreToRestrictRestrict f y hyU hyW)
        (tensorPowModule ((f ∣_ U) ⁻¹ᵁ W).toScheme
          (pullbackModule ((f ∣_ U) ⁻¹ᵁ W).ι (pullbackModule (f ⁻¹ᵁ U).ι L)) d)
        ((restrictRestrictTwistIso f L W d).hom.app ⊤
          (pullbackGlobalSections ((f ∣_ U) ⁻¹ᵁ W).ι
            ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj (tensorPowModule X L d))
            (Scheme.Modules.pullbackSection (f ⁻¹ᵁ U).ι (tensorPowModule X L d)
              (f ⁻¹ᵁ U) ⊤ hU a))) := by
  have h1 := inv_app_pullbackCompIsoOfEq_pullbackSection (fibreToRestrict f y hyU) (f ⁻¹ᵁ U).ι
    (fibreToRestrict_comp_ι f y hyU) (tensorPowModule X L d) (f ⁻¹ᵁ U) hU
    (Stacks.FormalFunctions.top_le_preimage_fiberι f y U hyU) a
  have h2 := app_inv_of_app_hom
    (pullbackCompIsoOfEq (fibreToRestrictRestrict f y hyU hyW) ((f ∣_ U) ⁻¹ᵁ W).ι
      (fibreToRestrictRestrict_comp_ι f y hyU hyW)
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj (tensorPowModule X L d)))
    (app_pullbackCompIsoOfEq (fibreToRestrictRestrict f y hyU hyW) ((f ∣_ U) ⁻¹ᵁ W).ι
      (fibreToRestrictRestrict_comp_ι f y hyU hyW)
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj (tensorPowModule X L d))
      (Scheme.Modules.pullbackSection (f ⁻¹ᵁ U).ι (tensorPowModule X L d) (f ⁻¹ᵁ U) ⊤ hU a))
  calc (liftedFamilyIso f L y hyU hyW d).hom.app ⊤
          (Scheme.Modules.pullbackSection (f.fiberι y) (tensorPowModule X L d) (f ⁻¹ᵁ U) ⊤
            (Stacks.FormalFunctions.top_le_preimage_fiberι f y U hyU) a)
      = ((Scheme.Modules.pullback (fibreToRestrictRestrict f y hyU hyW)).mapIso
            (restrictRestrictTwistIso f L W d)).hom.app ⊤
          ((pullbackCompIsoOfEq (fibreToRestrictRestrict f y hyU hyW) ((f ∣_ U) ⁻¹ᵁ W).ι
              (fibreToRestrictRestrict_comp_ι f y hyU hyW)
              ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj
                (tensorPowModule X L d))).inv.app ⊤
            ((pullbackCompIsoOfEq (fibreToRestrict f y hyU) (f ⁻¹ᵁ U).ι
                (fibreToRestrict_comp_ι f y hyU) (tensorPowModule X L d)).inv.app ⊤
              (Scheme.Modules.pullbackSection (f.fiberι y) (tensorPowModule X L d)
                (f ⁻¹ᵁ U) ⊤
                (Stacks.FormalFunctions.top_le_preimage_fiberι f y U hyU) a))) := rfl
    _ = ((Scheme.Modules.pullback (fibreToRestrictRestrict f y hyU hyW)).mapIso
            (restrictRestrictTwistIso f L W d)).hom.app ⊤
          (pullbackGlobalSections (fibreToRestrictRestrict f y hyU hyW)
            ((Scheme.Modules.pullback ((f ∣_ U) ⁻¹ᵁ W).ι).obj
              ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj (tensorPowModule X L d)))
            (pullbackGlobalSections ((f ∣_ U) ⁻¹ᵁ W).ι
              ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj (tensorPowModule X L d))
              (Scheme.Modules.pullbackSection (f ⁻¹ᵁ U).ι (tensorPowModule X L d)
                (f ⁻¹ᵁ U) ⊤ hU a))) := by
        rw [h1, h2]
    _ = _ := (pullbackGlobalSections_natural (fibreToRestrictRestrict f y hyU hyW)
        (restrictRestrictTwistIso f L W d).hom _).symm

/-! ### Shrinking the base for sections given over the preimage of a neighbourhood -/

/-- **The shrinking step of [Stacks, Tag 0D2N], for a family of sections given over `f ⁻¹ᵁ U`.**
Let `f : X ⟶ S` be universally closed, let `ℳ` be an invertible `𝒪_X`-module, let `U` be an open
neighbourhood of `y : S`, and let `a` be a family of sections of `ℳ` over `f ⁻¹ᵁ U` whose
restrictions to the fibre `X_y` generate the stalks of `ℳ|_{X_y}`.  Then some open `W` of
`U.toScheme` contains `y` and is such that the family, read as global sections of `ℳ|_{f⁻¹U}`,
generates the stalks of its restriction to `(f ∣_ U)⁻¹W`.

This is the sentence "`X_y ⊆ U = ⋃ X_{sᵢ}`, and since `X ⟶ Y` is closed we can find an open
neighbourhood `V` of `y` with `f⁻¹(V) ⊆ U`" of the source:
`Stacks.AmpleFibreNeighbourhood.exists_mem_generatesStalks_pullbackGlobalSections` of
`AmpleFibreNeighbourhood/FibreImmersion.lean` does exactly that, applied here to `f ∣_ U` and to
the global sections of `ℳ|_{f⁻¹U}` obtained from `a`.  What is added is its hypothesis, that at
every point of the fibre of `f ∣_ U` over `y` some member of the family does not vanish.  That is
read off the generation hypothesis on `X_y`: a point of `f ⁻¹ᵁ U` over `y` lies in the range of
the inclusion of that fibre (`AlgebraicGeometry.Scheme.Hom.range_fiberι`), hence in the range of
`Stacks.AmpleFibreNeighbourhood.fibreToRestrict`, the identification of fibres being an
isomorphism and so surjective on points; a generating family of an invertible module does not
vanish identically at any point
(`Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks`); and the nonvanishing
open of a restricted section is the preimage of the nonvanishing open
(`Stacks.RatioPullback.nvOpen_pullbackGlobalSections`, [Stacks, Tag 0H78]). -/
theorem exists_mem_generatesStalks_restrict (f : X ⟶ S) [UniversallyClosed f] (M : X.Modules)
    [IsInvertibleModule X M] (y : S) {U : S.Opens} (hyU : y ∈ U)
    (hU : (⊤ : (f ⁻¹ᵁ U).toScheme.Opens) ≤ (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U)) {κ : Type*}
    (a : κ → Γ(M, f ⁻¹ᵁ U))
    (hgen : GeneratesStalks fun i => Scheme.Modules.pullbackSection (f.fiberι y) M (f ⁻¹ᵁ U) ⊤
      (Stacks.FormalFunctions.top_le_preimage_fiberι f y U hyU) (a i)) :
    ∃ W : U.toScheme.Opens, (⟨y, hyU⟩ : U.toScheme) ∈ W ∧
      GeneratesStalks fun i => pullbackGlobalSections ((f ∣_ U) ⁻¹ᵁ W).ι
        ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M)
        (Scheme.Modules.pullbackSection (f ⁻¹ᵁ U).ι M (f ⁻¹ᵁ U) ⊤ hU (a i)) := by
  classical
  have hres := fun i => (inv_app_pullbackCompIsoOfEq_pullbackSection (fibreToRestrict f y hyU)
    (f ⁻¹ᵁ U).ι (fibreToRestrict_comp_ι f y hyU) M (f ⁻¹ᵁ U) hU
    (Stacks.FormalFunctions.top_le_preimage_fiberι f y U hyU) (a i)).symm
  have hgen' : GeneratesStalks fun i => pullbackGlobalSections (fibreToRestrict f y hyU)
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M)
      (Scheme.Modules.pullbackSection (f ⁻¹ᵁ U).ι M (f ⁻¹ᵁ U) ⊤ hU (a i)) := by
    rw [funext hres]
    exact Stacks.ProductFamilyTwist.generatesStalks_congr
      (pullbackCompIsoOfEq (fibreToRestrict f y hyU) (f ⁻¹ᵁ U).ι
        (fibreToRestrict_comp_ι f y hyU) M).symm hgen
  have hsurj : Function.Surjective (fiberMorphismRestrictIso f U y hyU).inv.base :=
    fun p => ⟨(fiberMorphismRestrictIso f U y hyU).hom.base p, by
      simpa using congrArg (fun q => q.base p) (fiberMorphismRestrictIso f U y hyU).hom_inv_id⟩
  refine exists_mem_generatesStalks_pullbackGlobalSections (f ∣_ U)
    ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M)
    (fun i => Scheme.Modules.pullbackSection (f ⁻¹ᵁ U).ι M (f ⁻¹ᵁ U) ⊤ hU (a i))
    (⟨y, hyU⟩ : U.toScheme) fun x hx => ?_
  obtain ⟨z₀, hz₀⟩ := (Scheme.Hom.range_fiberι (f ∣_ U) (⟨y, hyU⟩ : U.toScheme)).ge hx
  obtain ⟨z, hz⟩ := hsurj z₀
  obtain ⟨i, hi⟩ := exists_mem_nvCover_of_generatesStalks _ hgen' z
  refine ⟨i, ?_⟩
  have heq := Stacks.RatioPullback.nvOpen_pullbackGlobalSections (fibreToRestrict f y hyU)
    ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M)
    (Scheme.Modules.pullbackSection (f ⁻¹ᵁ U).ι M (f ⁻¹ᵁ U) ⊤ hU (a i))
  have hi' : (fibreToRestrict f y hyU).base z ∈
      nvOpen ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M)
        (Scheme.Modules.pullbackSection (f ⁻¹ᵁ U).ι M (f ⁻¹ᵁ U) ⊤ hU (a i)) :=
    cast (congrArg (fun O : (f.fiber y).Opens => z ∈ O) heq) hi
  have hbase : (fibreToRestrict f y hyU).base z = x := by
    have hcomp : (fibreToRestrict f y hyU).base z =
        ((f ∣_ U).fiberι (⟨y, hyU⟩ : U.toScheme)).base
          ((fiberMorphismRestrictIso f U y hyU).inv.base z) := by
      show ((fiberMorphismRestrictIso f U y hyU).inv ≫
        (f ∣_ U).fiberι (⟨y, hyU⟩ : U.toScheme)).base z = _
      simp
    rw [hcomp, hz, hz₀]
  rwa [hbase] at hi'

/-! ### Stacks Tag 0D2N from the lifting property -/

/-- **[Stacks, Tag 0D2N], from the lifting of a generating family off the fibre.**  Let
`f : X ⟶ S` be proper with `S` locally Noetherian, let `ℒ` be an invertible `𝒪_X`-module whose
restriction `ℒ_y` to the scheme-theoretic fibre `X_y` over a point `y : S` is ample, and suppose
that for all large `d` every finite family of global sections of `(f.fiberι y)^*(ℒ ^⊗ d)` is the
restriction to `X_y` of a family of sections of `ℒ ^⊗ d` over `f ⁻¹ᵁ U`, for some open
neighbourhood `U` of `y`.  Then `y` has an open neighbourhood `V ⊆ S` such that `ℒ|_{f⁻¹V}` is
ample relative to `f ∣_ V`.

The conclusion is the assertion of [Stacks, Tag 0D2N] verbatim, and the hypothesis `hlift` is the
one input the source's proof takes from [Stacks, Tag 0D2M]: it is assertion (B) of that tag, after
the reduction of a general locally Noetherian base to the local ring at `y`, in the form the proof
consumes.  See the route note at the head of this file for the declaration that carries out
each of the six steps.  **No `@[stacks]` attribute is attached here**, because `hlift` is still a
hypothesis; the attribute goes on the statement that results once it is discharged. -/
theorem exists_mem_isRelativelyAmple_of_exists_lift (f : X ⟶ S) [IsProper f]
    [IsLocallyNoetherian S] (L : X.Modules) [IsInvertibleModule X L] (y : S)
    (hL : IsAmple (f.fiber y) (pullbackModule (f.fiberι y) L))
    (hlift : ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ (k : ℕ)
      (t : Fin k → Γ((Scheme.Modules.pullback (f.fiberι y)).obj (tensorPowModule X L d), ⊤)),
      ∃ (U : S.Opens) (hy : y ∈ U)
        (a : Fin k → Γ(tensorPowModule X L d, f ⁻¹ᵁ U)),
        ∀ i, Scheme.Modules.pullbackSection (f.fiberι y) (tensorPowModule X L d) (f ⁻¹ᵁ U) ⊤
            (Stacks.FormalFunctions.top_le_preimage_fiberι f y U hy) (a i) = t i) :
    ∃ V : S.Opens, y ∈ V ∧
      Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ V)
        (pullbackModule (f ⁻¹ᵁ V).ι L) := by
  classical
  obtain ⟨dlift, hlift⟩ := hlift
  -- Step 1: the generating family on the fibre whose attached morphism is an immersion.
  obtain ⟨d₁, -, hall⟩ :=
    exists_generatesStalks_isImmersion_toProjectiveSpaceOver_of_isAmple
      (f.fiberToSpecResidueField y) (pullbackModule (f.fiberι y) L) hL
  obtain ⟨d, hd1, hdd₁, hdl⟩ : ∃ d : ℕ, 1 ≤ d ∧ d₁ ≤ d ∧ dlift ≤ (d : ℤ) :=
    ⟨max d₁ (max 1 dlift.toNat), le_trans (le_max_left 1 _) (le_max_right d₁ _),
      le_max_left _ _,
      le_trans (Int.self_le_toNat dlift)
        (by exact_mod_cast le_trans (le_max_right 1 dlift.toNat) (le_max_right d₁ _))⟩
  obtain ⟨r, t, ht, himm⟩ := hall d hdd₁
  -- Steps 2 and 3: match the two spellings of the twisted module, and lift the family.
  obtain ⟨U, hyU, a, ha⟩ := hlift (d : ℤ) hdl (r + 1)
    fun i => (pullbackTensorPowModuleIntIso (f.fiberι y) L (d : ℤ)).inv.app ⊤ (t i)
  have hU : (⊤ : (f ⁻¹ᵁ U).toScheme.Opens) ≤ (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) := by simp
  -- Step 4: shrink the base so that the lifted family generates everywhere.
  obtain ⟨W, hyW, hgenW⟩ := exists_mem_generatesStalks_restrict f
    (tensorPowModule X L (d : ℤ)) y hyU hU a
    (by
      rw [funext ha]
      exact Stacks.ProductFamilyTwist.generatesStalks_congr
        (pullbackTensorPowModuleIntIso (f.fiberι y) L (d : ℤ)).symm ht)
  -- Step 5: the endgame, over the twice-restricted morphism.
  have hgen₂ : GeneratesStalks fun i => (restrictRestrictTwistIso f L W (d : ℤ)).hom.app ⊤
      (pullbackGlobalSections ((f ∣_ U) ⁻¹ᵁ W).ι
        ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj (tensorPowModule X L (d : ℤ)))
        (Scheme.Modules.pullbackSection (f ⁻¹ᵁ U).ι (tensorPowModule X L (d : ℤ))
          (f ⁻¹ᵁ U) ⊤ hU (a i))) :=
    Stacks.ProductFamilyTwist.generatesStalks_congr (restrictRestrictTwistIso f L W (d : ℤ))
      hgenW
  have hgenpb := generatesStalks_pullbackGlobalSections'
    (fibreToRestrictRestrict f y hyU hyW) _ _ hgen₂
  have hgenβ : GeneratesStalks fun i =>
      ((pullbackTensorPowModuleIntIso (f.fiberι y) L (d : ℤ)).symm ≪≫
        liftedFamilyIso f L y hyU hyW (d : ℤ)).hom.app ⊤ (t i) :=
    Stacks.ProductFamilyTwist.generatesStalks_congr
      ((pullbackTensorPowModuleIntIso (f.fiberι y) L (d : ℤ)).symm ≪≫
        liftedFamilyIso f L y hyU hyW (d : ℤ)) ht
  have hQ : (fun i => pullbackGlobalSections (fibreToRestrictRestrict f y hyU hyW)
        (tensorPowModule ((f ∣_ U) ⁻¹ᵁ W).toScheme
          (pullbackModule ((f ∣_ U) ⁻¹ᵁ W).ι (pullbackModule (f ⁻¹ᵁ U).ι L)) (d : ℤ))
        ((restrictRestrictTwistIso f L W (d : ℤ)).hom.app ⊤
          (pullbackGlobalSections ((f ∣_ U) ⁻¹ᵁ W).ι
            ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj (tensorPowModule X L (d : ℤ)))
            (Scheme.Modules.pullbackSection (f ⁻¹ᵁ U).ι (tensorPowModule X L (d : ℤ))
              (f ⁻¹ᵁ U) ⊤ hU (a i))))) =
      fun i => ((pullbackTensorPowModuleIntIso (f.fiberι y) L (d : ℤ)).symm ≪≫
        liftedFamilyIso f L y hyU hyW (d : ℤ)).hom.app ⊤ (t i) := by
    funext i
    have h := app_liftedFamilyIso f L y hyU hyW (d : ℤ) hU (a i)
    rw [ha i] at h
    exact h.symm
  have hpsi := (toProjectiveSpaceOver_congr_family (f.fiberToSpecResidueField y) hQ
      hgenpb hgenβ).trans
    (toProjectiveSpaceOver_congr (f.fiberToSpecResidueField y)
      ((pullbackTensorPowModuleIntIso (f.fiberι y) L (d : ℤ)).symm ≪≫
        liftedFamilyIso f L y hyU hyW (d : ℤ)) t ht hgenβ)
  have : IsImmersion (toProjectiveSpaceOver _ hgenpb (f.fiberToSpecResidueField y)) := by
    rw [show toProjectiveSpaceOver _ hgenpb (f.fiberToSpecResidueField y) =
      toProjectiveSpaceOver t ht (f.fiberToSpecResidueField y) from hpsi]
    exact himm
  obtain ⟨u, hu, hsq⟩ := exists_isPreimmersion_fibreToRestrictRestrict_comp f y hyU hyW
  have := hu
  have : IsPreimmersion (projectiveSpaceOverMap r u) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_projectiveSpaceOverMap r u).flip inferInstance
  have hcomp := comp_toProjectiveSpaceOver _ hgen₂ ((f ∣_ U) ∣_ W) hsq hgenpb
  have hcomm : ((fiberMorphismRestrictIso (f ∣_ U) W (⟨y, hyU⟩ : U.toScheme) hyW).hom ≫
        (fiberMorphismRestrictIso f U y hyU).hom ≫
          toProjectiveSpaceOver _ hgenpb (f.fiberToSpecResidueField y)) ≫
        projectiveSpaceOverMap r u =
      ((f ∣_ U) ∣_ W).fiberι (⟨⟨y, hyU⟩, hyW⟩ : W.toScheme) ≫
        toProjectiveSpaceOver _ hgen₂ ((f ∣_ U) ∣_ W) := by
    rw [Category.assoc, Category.assoc, hcomp, reassoc_of% comp_fibreToRestrictRestrict]
  have hinjfib : ∀ p : W.toScheme, Function.Injective (((f ∣_ U) ∣_ W).fiberι p).base :=
    fun p => (((f ∣_ U) ∣_ W).fiberι p).isEmbedding.injective
  have hinjψ : Function.Injective
      ((fiberMorphismRestrictIso (f ∣_ U) W (⟨y, hyU⟩ : U.toScheme) hyW).hom ≫
        (fiberMorphismRestrictIso f U y hyU).hom ≫
          toProjectiveSpaceOver _ hgenpb (f.fiberToSpecResidueField y)).base :=
    injective_base_comp _ _
      (injective_base_of_iso (fiberMorphismRestrictIso (f ∣_ U) W (⟨y, hyU⟩ : U.toScheme) hyW))
      (injective_base_comp _ _ (injective_base_of_iso (fiberMorphismRestrictIso f U y hyU))
        (toProjectiveSpaceOver _ hgenpb (f.fiberToSpecResidueField y)).isEmbedding.injective)
  obtain ⟨V₃, hy₃, hamp⟩ := exists_mem_isRelativelyAmple_toProjectiveSpaceOver ((f ∣_ U) ∣_ W)
    (pullbackModule ((f ∣_ U) ⁻¹ᵁ W).ι (pullbackModule (f ⁻¹ᵁ U).ι L)) hd1 _ hgen₂
    (⟨⟨y, hyU⟩, hyW⟩ : W.toScheme) fun z hz => Set.Subsingleton.finite
      (subsingleton_preimage_of_fibreFactorization
        (toProjectiveSpaceOver _ hgen₂ ((f ∣_ U) ∣_ W))
        (toProjectiveSpaceOver_fst _ hgen₂ ((f ∣_ U) ∣_ W)) (⟨⟨y, hyU⟩, hyW⟩ : W.toScheme)
        (((f ∣_ U) ∣_ W).fiberι (⟨⟨y, hyU⟩, hyW⟩ : W.toScheme))
        (((f ∣_ U) ∣_ W).range_fiberι (⟨⟨y, hyU⟩, hyW⟩ : W.toScheme))
        (hinjfib (⟨⟨y, hyU⟩, hyW⟩ : W.toScheme))
        ((fiberMorphismRestrictIso (f ∣_ U) W (⟨y, hyU⟩ : U.toScheme) hyW).hom ≫
          (fiberMorphismRestrictIso f U y hyU).hom ≫
            toProjectiveSpaceOver _ hgenpb (f.fiberToSpecResidueField y))
        (projectiveSpaceOverMap r u) hcomm
        (projectiveSpaceOverMap r u).isEmbedding.injective hinjψ hz)
  -- Step 6: carry the conclusion back to an open of `S`.
  refine ⟨U.ι ''ᵁ (W.ι ''ᵁ V₃), ⟨⟨y, hyU⟩, ⟨⟨⟨y, hyU⟩, hyW⟩, hy₃, rfl⟩, rfl⟩, ?_⟩
  exact isRelativelyAmple_morphismRestrict_image f L (W.ι ''ᵁ V₃)
    (isRelativelyAmple_morphismRestrict_image (f ∣_ U) (pullbackModule (f ⁻¹ᵁ U).ι L) V₃ hamp)

end Stacks.AmpleFibreNeighbourhood

end
