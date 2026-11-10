module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentSections
public import StacksFrontier.Cotangent.SheavesOfRings.HomologyZero

/-!
# The canonical map from the cotangent complex to the naive cotangent complex

Let `f : A ⟶ B` be a homomorphism of sheaves of commutative rings on a site and let `P_•` be the
standard resolution of `B` over `A`.  Writing `I` for the kernel of the augmentation
`P₀ ⟶ B`, the naive cotangent complex of that presentation is the two-term complex

`I/I² ⟶ B ⊗_{P₀} Ω_{P₀/A}`

and the cotangent complex `L_{B/A}` is the alternating-face complex of
`Ω_{P_•/A} ⊗_{P_•} B`.  This file constructs the canonical map of the source's diagram,

```
L_{B/A}    …  ⟶  Ω_{P₂/A} ⊗ B  ⟶  Ω_{P₁/A} ⊗ B  ⟶  Ω_{P₀/A} ⊗ B
                       ↓                ↓                ↓
NL_{B/A}   …  ⟶       0        ⟶     I/I²       ⟶  Ω_{P₀/A} ⊗ B
```

degreewise together with its two commuting squares.

## Main definitions

* `CategoryTheory.Sheaf.naiveSequence`: the conormal sequence
  `I/I² ⟶ B ⊗_{P₀} Ω_{P₀/A} ⟶ Ω_{B/A} ⟶ 0` of the presentation of `B` by the degree-zero term
  of the standard resolution, whose first two terms are the naive cotangent complex.
* `CategoryTheory.Sheaf.naiveComparisonZero`: the degree-zero component of the comparison,
  `d p ⊗ b ↦ b ⊗ d p`.
* `CategoryTheory.Sheaf.faceDifference`: the local section `d₀ x - d₁ x` of `I`.
* `CategoryTheory.Sheaf.naiveComparisonNegOne`: the degree `-1` component of the comparison,
  `d x ⊗ b ↦ b · [d₀ x - d₁ x]`.

## Main results

* `Stacks.Sites.Conormal.conormalClass_add`, `Stacks.Sites.Conormal.conormalClass_smul`,
  `Stacks.Sites.Conormal.conormalClass_zero` and
  `Stacks.Sites.Conormal.conormalClass_map`: the local conormal class `f mod I²` is additive in
  `f`, semilinear over the presentation, sends `0` to `0`, and commutes with restriction.
* `CategoryTheory.Sheaf.naiveComparisonNegOne_conormalClass`: the degree `-1` component sends a
  pure differential `d x` to the class of `d₀ x - d₁ x` in `I/I²`.
* `CategoryTheory.Sheaf.naiveComparisonNegOne_comp_conormal`: the lower square.  Following the
  degree `-1` component by the differential `I/I² ⟶ B ⊗_{P₀} Ω_{P₀/A}` of the naive complex is
  the difference of the two faces followed by the degree-zero component, which is the
  differential of the cotangent complex out of degree `-1`.
* `CategoryTheory.Sheaf.naiveComparisonNegOne_faceSum`: the upper square.  The degree `-1`
  component annihilates the alternating sum of the three faces `P₂ ⇶ P₁`, which is the
  differential of the cotangent complex into degree `-1`.

## Implementation notes

The naive cotangent complex of the source is built from the presentation `A[B] ⟶ B`, and `A[B]`
is the degree-zero term `P₀` of the standard resolution.  Here that presentation is taken to be
`P₀ ⟶ B` itself, so that no comparison of two constructions of a free algebra sheaf is needed:
`Stacks.Sites.Conormal.conormalSequence` applies to any locally surjective presentation, and the
augmentation `P₀ ⟶ B` is even surjective on sections, the variables of the free algebra
providing a set-theoretic section (`CategoryTheory.Sheaf.augSection`).  The resulting complex is
therefore the source's `NL_{B/A}` with the free algebra spelled by the standard resolution
rather than by `Stacks.Sites.FreeAlgebra.freeAlgebraSheaf`; the canonical isomorphism between
those two presentations of `B` is not constructed here, so the comparison is not transported to
`Stacks.SheafOfModules.naiveCotangentComplex`.

Both components are obtained from the universal property of the base-changed differentials:
`CategoryTheory.Sheaf.CotangentSimplicialModuleData.derivationEquiv` identifies morphisms out of
`Ω_{P_n/A} ⊗_{P_n} B` with `A`-derivations of `P_n`, so each component is specified by what it
does to a local section, and the two squares become equalities of derivations.  The degree-zero
component is the derivation `p ↦ 1 ⊗ d p`, whose three defining identities are the
`tensorDifferential` lemmas of `NaiveCotangentSections`; the degree `-1` component is the
derivation `x ↦ [d₀ x - d₁ x]`, whose Leibniz rule is the identity
`d₀(xy) - d₁(xy) = d₀x · (d₀y - d₁y) + d₁y · (d₀x - d₁x)` read modulo `I²`.

Only the degree `-1` and degree `0` components carry content: in simplicial degree `n ≥ 2` the
naive complex is zero, and the upper square is exactly the statement that the comparison is a
map of complexes there.

### What this file does not prove

Tag 08US also asserts that the canonical map identifies the naive cotangent complex with the
truncation `τ_{≥ -1} L_{B/A}`, that is, that it induces isomorphisms on the cohomology sheaves
`H⁰` and `H^{-1}`.  The source proves this by comparing with the chaotic topology, which needs
the inverse-image theorem for the naive cotangent complex (Tag 08TZ).  That tag IS formalized
in this library, as `Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso`; what is not
carried here is the comparison with the chaotic topology that transports the ring-level
isomorphisms of Tag 08UP along it, and neither half of the induced isomorphism is proved here.

## References

* [Stacks Project, Tag 08US](https://stacks.math.columbia.edu/tag/08US)
* [Stacks Project, Tag 08UP](https://stacks.math.columbia.edu/tag/08UP), the same comparison for
  a homomorphism of commutative rings.
* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS), the cotangent complex.
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal sequence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v w z

/-! ### Local sections of the conormal sheaf -/

namespace Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (R A B : Sheaf J CommRingCat.{w}) (a : R ⟶ A) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective J φ.hom] (X : Cᵒᵖ)

omit [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The local conormal class is additive. -/
theorem conormalClass_add (x y : kernelIdeal φ.hom X) :
    conormalClass.{v, u, w, z} J R A B a φ X (x + y) =
      conormalClass.{v, u, w, z} J R A B a φ X x +
        conormalClass.{v, u, w, z} J R A B a φ X y :=
  (congrArg (toAssociatedModule.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) X)
    (map_add (kernelIdeal φ.hom X).toCotangent x y)).trans
    (toAssociatedModule_add.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) X _ _)

omit [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The local conormal class of the zero section is zero. -/
theorem conormalClass_zero :
    conormalClass.{v, u, w, z} J R A B a φ X (0 : kernelIdeal φ.hom X) = 0 := by
  have h := conormalClass_add.{u, v, w, z} J R A B a φ X 0 0
  rw [add_zero] at h
  exact add_left_cancel ((add_zero _).trans h).symm

omit [HasWeakSheafify J CommRingCat.{w}] in
/-- The local conormal class is semilinear over the presentation: scaling a section of the
kernel by a section `p` of `A` scales its class by the image of `p` in `B`. -/
theorem conormalClass_smul (p : A.obj.obj X) (x : kernelIdeal φ.hom X) :
    conormalClass.{v, u, w, z} J R A B a φ X (p • x) =
      (φ.hom.app X).hom p • conormalClass.{v, u, w, z} J R A B a φ X x := by
  refine Eq.trans (congrArg (toAssociatedModule.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) X)
    (show (kernelIdeal φ.hom X).toCotangent (p • x) =
      (Ideal.Quotient.mk (kernelIdeal φ.hom X) p) •
        (kernelIdeal φ.hom X).toCotangent x from ?_)) ?_
  · exact ((kernelIdeal φ.hom X).toCotangent.map_smul p x).trans
      (quotient_mk_smul_cotangent (kernelIdeal φ.hom X) p _).symm
  · exact toAssociatedModule_smul.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) X _ _

omit [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The local conormal class commutes with restriction of local sections. -/
theorem conormalClass_map {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : kernelIdeal φ.hom X)
    (y : kernelIdeal φ.hom Y) (h : (y : A.obj.obj Y) = A.obj.map g (x : A.obj.obj X)) :
    conormalClass.{v, u, w, z} J R A B a φ Y y =
      (conormalSequence.{v, u, w, z} J R A B a φ).X₁.val.map g
        (conormalClass.{v, u, w, z} J R A B a φ X x) := by
  refine Eq.trans (congrArg (toAssociatedModule.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) Y)
    (show (kernelIdeal φ.hom Y).toCotangent y =
      (conormalPresheaf φ.hom).map g ((kernelIdeal φ.hom X).toCotangent x) from ?_)) ?_
  · exact (congrArg (kernelIdeal φ.hom Y).toCotangent (Subtype.ext h)).trans
      (cotangentMap_toCotangent (kernelIdeal φ.hom X) (kernelIdeal φ.hom Y)
        (A.obj.map g).hom (map_kernel φ.hom g) x).symm
  · exact toAssociatedModule_map.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) g _

end Stacks.Sites.Conormal

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-! ### The presentation of `B` by the degree-zero term of the standard resolution -/

/-- The augmentation `P₀ ⟶ B` of the standard resolution is surjective on local sections: the
variables of the free algebra provide a set-theoretic section. -/
theorem augSections_surjective (U : Cᵒᵖ) :
    Function.Surjective ((resolutionAugmentation J f (op ⦋0⦌)).hom.app U) :=
  fun b => ⟨augSection J f U b, augSections_augSection J f U b⟩

/-- **The augmentation `P_n ⟶ B` of the standard resolution is surjective on local sections in
every simplicial degree.** The augmentation is a map of simplicial objects into a constant one,
so its naturality along the unique `⦋n⦌ ⟶ ⦋0⦌` factors the degree-zero augmentation as
`P₀ ⟶ P_n ⟶ B`; the degree-zero augmentation is surjective on local sections because the
variables of the free algebra provide a set-theoretic section, and a composite that is
surjective has a surjective last factor. -/
theorem resolutionAugmentation_surjective (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    Function.Surjective ((resolutionAugmentation J f n).hom.app U) := by
  have hnat : (standardResolution J f).left.map (SimplexCategory.const n.unop ⦋0⦌ 0).op ≫
      (standardResolution J f).hom.app n = (standardResolution J f).hom.app (op ⦋0⦌) :=
    ((standardResolution J f).hom.naturality
      (SimplexCategory.const n.unop ⦋0⦌ 0).op).trans (Category.comp_id _)
  intro b
  refine ⟨((standardResolution J f).left.map
    (SimplexCategory.const n.unop ⦋0⦌ 0).op).right.hom.app U (augSection J f U b), ?_⟩
  refine Eq.trans (comp_sections ((standardResolution J f).left.map
    (SimplexCategory.const n.unop ⦋0⦌ 0).op) ((standardResolution J f).hom.app n) U
      (augSection J f U b)).symm ?_
  rw [hnat]
  exact augSections_augSection J f U b

/-- The augmentation `P₀ ⟶ B` of the standard resolution is locally surjective. -/
instance augmentation_isLocallySurjective :
    Presheaf.IsLocallySurjective J (resolutionAugmentation J f (op ⦋0⦌)).hom :=
  Presheaf.isLocallySurjective_of_surjective J _ fun U => augSections_surjective J f U

/-- The augmentation `P_n ⟶ B` of the standard resolution is locally surjective in every
simplicial degree, being surjective on sections by
`CategoryTheory.Sheaf.resolutionAugmentation_surjective`. -/
instance resolutionAugmentation_isLocallySurjective (n : SimplexCategoryᵒᵖ) :
    Presheaf.IsLocallySurjective J (resolutionAugmentation J f n).hom :=
  Presheaf.isLocallySurjective_of_surjective J _ fun U => resolutionAugmentation_surjective J f n U

/-- The conormal sequence `I/I² ⟶ B ⊗_{P₀} Ω_{P₀/A} ⟶ Ω_{B/A} ⟶ 0` of the presentation of `B`
by the degree-zero term of the standard resolution.  Its first two terms, with the left-hand
map as differential, are the naive cotangent complex of `f`. -/
noncomputable abbrev naiveSequence : ShortComplex (targetModules J B) :=
  Stacks.Sites.Conormal.conormalSequence.{v, u, max u v w, u} J A
    (resolutionTerm J f (op ⦋0⦌)) B (resolutionBase J f (op ⦋0⦌))
    (resolutionAugmentation J f (op ⦋0⦌))

/-! ### Derivations and morphisms out of the base-changed differentials -/

/-- The derivation corepresented by a morphism out of the degree-`n` term of the base-changed
simplicial module is the universal one followed by that morphism, read on local sections. -/
theorem derivationEquiv_val_app (n : SimplexCategoryᵒᵖ) (M : targetModules J B)
    (h : (cotangentSimplicialModule J f).object.obj n ⟶ M) (U : Cᵒᵖ)
    (x : (resolutionTerm J f n).obj.obj U) :
    ((cotangentSimplicialModule J f).derivationEquiv n M h).d x =
      h.val.app U (((cotangentSimplicialModule J f).universalDerivation n).d x) := by
  rw [CotangentSimplicialModuleData.derivationEquiv_eq_postcomp]
  rfl

/-- Two morphisms out of the degree-`n` term agreeing on derivations are equal. -/
theorem hom_ext_of_derivationEquiv (n : SimplexCategoryᵒᵖ) {M : targetModules J B}
    {h₁ h₂ : (cotangentSimplicialModule J f).object.obj n ⟶ M}
    (hd : ∀ (U : Cᵒᵖ) (x : (resolutionTerm J f n).obj.obj U),
      ((cotangentSimplicialModule J f).derivationEquiv n M h₁).d x =
        ((cotangentSimplicialModule J f).derivationEquiv n M h₂).d x) : h₁ = h₂ :=
  ((cotangentSimplicialModule J f).derivationEquiv n M).injective
    (PresheafOfModulesOfCommRing.Derivation.ext (funext fun U => AddMonoidHom.ext (hd U)))

/-- A face of the standard resolution acts on derivations by precomposition. -/
theorem derivationEquiv_delta (n : ℕ) (M : targetModules J B) (k : Fin (n + 2))
    (h : (cotangentSimplicialModule J f).object.obj (op ⦋n⦌) ⟶ M) (U : Cᵒᵖ)
    (x : (resolutionTerm J f (op ⦋n + 1⦌)).obj.obj U) :
    ((cotangentSimplicialModule J f).derivationEquiv (op ⦋n + 1⦌) M
        ((cotangentSimplicialModule J f).object.δ k ≫ h)).d x =
      ((cotangentSimplicialModule J f).derivationEquiv (op ⦋n⦌) M h).d
        (((standardResolution J f).left.δ k).right.hom.app U x) :=
  (cotangentSimplicialModule J f).simplex_naturality (SimplexCategory.δ k).op M h U x

/-- A face-composed morphism, read on a pure differential, is the derivation of the original
morphism at the face of the section. -/
private theorem delta_comp_val_app (n : ℕ) (M : targetModules J B) (k : Fin (n + 2))
    (h : (cotangentSimplicialModule J f).object.obj (op ⦋n⦌) ⟶ M) (U : Cᵒᵖ)
    (x : (resolutionTerm J f (op ⦋n + 1⦌)).obj.obj U) :
    ((cotangentSimplicialModule J f).object.δ k ≫ h).val.app U
        (((cotangentSimplicialModule J f).universalDerivation (op ⦋n + 1⦌)).d x) =
      ((cotangentSimplicialModule J f).derivationEquiv (op ⦋n⦌) M h).d
        (((standardResolution J f).left.δ k).right.hom.app U x) :=
  (derivationEquiv_val_app J f (op ⦋n + 1⦌) M _ U x).symm.trans
    (derivationEquiv_delta J f n M k h U x)

/-! ### The degree-zero component -/

/-- The local section `1 ⊗ d p` of the middle term `B ⊗_{P₀} Ω_{P₀/A}` of the conormal
sequence. -/
noncomputable abbrev tensorDifferentialSections (U : Cᵒᵖ)
    (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) : (naiveSequence J f).X₂.val.obj U :=
  Stacks.Sites.Conormal.tensorDifferential.{v, u, max u v w, u} J A
    (resolutionTerm J f (op ⦋0⦌)) B (resolutionBase J f (op ⦋0⦌))
    (resolutionAugmentation J f (op ⦋0⦌)) U p

/-- The local section `1 ⊗ d p` commutes with restriction of local sections. -/
theorem tensorDifferentialSections_map {U V : Cᵒᵖ} (g : U ⟶ V)
    (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    tensorDifferentialSections J f V ((resolutionTerm J f (op ⦋0⦌)).obj.map g p) =
      (naiveSequence J f).X₂.val.map g (tensorDifferentialSections J f U p) := by
  refine Eq.trans (congrArg (Stacks.Sites.Conormal.toAssociatedModule.{v, u, max u v w, u} J
    (resolutionTerm J f (op ⦋0⦌)) B (resolutionAugmentation J f (op ⦋0⦌))
    (Stacks.Sites.Conormal.tensorPresheaf (resolutionAugmentation J f (op ⦋0⦌)).hom
      (resolutionBase J f (op ⦋0⦌)).hom) V) ?_)
    (Stacks.Sites.Conormal.toAssociatedModule_map.{v, u, max u v w, u} J
      (resolutionTerm J f (op ⦋0⦌)) B (resolutionAugmentation J f (op ⦋0⦌)) _ g _)
  refine Eq.trans ?_ (TensorProduct.map_tmul _ _ _ _).symm
  exact congrArg₂ (fun b (ω : (Stacks.Sites.Conormal.differentialsPresheaf
      (resolutionBase J f (op ⦋0⦌)).hom).obj V) =>
        b ⊗ₜ[(resolutionTerm J f (op ⦋0⦌)).obj.obj V] ω)
    (map_one ((Stacks.Sites.Conormal.quotientPresheaf
      (resolutionAugmentation J f (op ⦋0⦌)).hom).map g).hom).symm
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
      (resolutionBase J f (op ⦋0⦌)).hom g p).symm

/-- The universal derivation `p ↦ 1 ⊗ d p` of `P₀` with values in the middle term
`B ⊗_{P₀} Ω_{P₀/A}` of the conormal sequence. -/
noncomputable def tensorDifferentialDerivation :
    resolutionDerivations J f (op ⦋0⦌) (naiveSequence J f).X₂ where
  d {U} := AddMonoidHom.mk' (tensorDifferentialSections J f U) fun x y =>
    Stacks.Sites.Conormal.tensorDifferential_add.{v, u, max u v w, u} J A
      (resolutionTerm J f (op ⦋0⦌)) B (resolutionBase J f (op ⦋0⦌))
      (resolutionAugmentation J f (op ⦋0⦌)) U x y
  d_mul {U} x y := by
    change tensorDifferentialSections J f U (x * y) =
      (resolutionAugmentation J f (op ⦋0⦌)).hom.app U x •
        (show (naiveSequence J f).X₂.val.obj U from tensorDifferentialSections J f U y) +
      (resolutionAugmentation J f (op ⦋0⦌)).hom.app U y •
        (show (naiveSequence J f).X₂.val.obj U from tensorDifferentialSections J f U x)
    exact Stacks.Sites.Conormal.tensorDifferential_mul.{v, u, max u v w, u} J A
      (resolutionTerm J f (op ⦋0⦌)) B (resolutionBase J f (op ⦋0⦌))
      (resolutionAugmentation J f (op ⦋0⦌)) U x y
  d_map {U V} g x := tensorDifferentialSections_map J f g x
  d_app {U} r :=
    Stacks.Sites.Conormal.tensorDifferential_coefficient.{v, u, max u v w, u} J A
      (resolutionTerm J f (op ⦋0⦌)) B (resolutionBase J f (op ⦋0⦌))
      (resolutionAugmentation J f (op ⦋0⦌)) U r

/-- The degree-zero component of the comparison, `d p ⊗ b ↦ b ⊗ d p`: the morphism
`Ω_{P₀/A} ⊗_{P₀} B ⟶ B ⊗_{P₀} Ω_{P₀/A}` corepresented by the derivation `p ↦ 1 ⊗ d p`. -/
noncomputable def naiveComparisonZero :
    (cotangentSimplicialModule J f).object.obj (op ⦋0⦌) ⟶ (naiveSequence J f).X₂ :=
  ((cotangentSimplicialModule J f).derivationEquiv (op ⦋0⦌) (naiveSequence J f).X₂).symm
    (tensorDifferentialDerivation J f)

/-- The degree-zero component sends a pure differential `d p` to `1 ⊗ d p`. -/
theorem derivationEquiv_naiveComparisonZero (U : Cᵒᵖ)
    (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    ((cotangentSimplicialModule J f).derivationEquiv (op ⦋0⦌) (naiveSequence J f).X₂
        (naiveComparisonZero J f)).d p = tensorDifferentialSections J f U p :=
  congrArg (fun D : resolutionDerivations J f (op ⦋0⦌) (naiveSequence J f).X₂ => D.d (X := U) p)
    (Equiv.apply_symm_apply _ (tensorDifferentialDerivation J f))

/-! ### The difference of the two faces -/

/-- Each face `P₁ ⟶ P₀` carries the structure map of `P₁` to the structure map of `P₀`. -/
theorem faceSections_resolutionBase (k : Fin 2) (U : Cᵒᵖ) (r : A.obj.obj U) :
    faceSections J f k U ((resolutionBase J f (op ⦋1⦌)).hom.app U r) =
      (resolutionBase J f (op ⦋0⦌)).hom.app U r :=
  congrArg (fun t : A ⟶ resolutionTerm J f (op ⦋0⦌) => t.hom.app U r)
    (Under.w ((standardResolution J f).left.δ k))

/-- Each face commutes with restriction of local sections. -/
theorem faceSections_map (k : Fin 2) {U V : Cᵒᵖ} (g : U ⟶ V)
    (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    faceSections J f k V ((resolutionTerm J f (op ⦋1⦌)).obj.map g x) =
      (resolutionTerm J f (op ⦋0⦌)).obj.map g (faceSections J f k U x) :=
  NatTrans.naturality_apply (F := (resolutionTerm J f (op ⦋1⦌)).obj)
    (G := (resolutionTerm J f (op ⦋0⦌)).obj) ((standardResolution J f).left.δ k).right.hom g x

/-- The difference `d₀ x - d₁ x` of the two faces, as a local section of the kernel `I` of the
augmentation `P₀ ⟶ B`: the two faces have the same composite with the augmentation, so the
difference is annihilated by it. -/
noncomputable def faceDifference (U : Cᵒᵖ) (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    Stacks.Sites.Conormal.kernelIdeal (resolutionAugmentation J f (op ⦋0⦌)).hom U :=
  ⟨faceSections J f 0 U x - faceSections J f 1 U x, by
    refine RingHom.mem_ker.mpr ?_
    have hsub : augSections J f U (faceSections J f 0 U x - faceSections J f 1 U x) =
        augSections J f U (faceSections J f 0 U x) -
          augSections J f U (faceSections J f 1 U x) := map_sub _ _ _
    have heq : augSections J f U (faceSections J f 0 U x) =
        augSections J f U (faceSections J f 1 U x) :=
      (augSections_faceSections J f 0 U x).trans (augSections_faceSections J f 1 U x).symm
    change augSections J f U (faceSections J f 0 U x - faceSections J f 1 U x) = 0
    rw [hsub, heq, sub_self]⟩

/-- The underlying local section of `P₀` of the difference of the two faces is `d₀ x - d₁ x`. -/
theorem faceDifference_coe (U : Cᵒᵖ) (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    ((faceDifference J f U x : Stacks.Sites.Conormal.kernelIdeal
        (resolutionAugmentation J f (op ⦋0⦌)).hom U) :
      (resolutionTerm J f (op ⦋0⦌)).obj.obj U) =
      faceSections J f 0 U x - faceSections J f 1 U x := rfl

/-- The difference of the two faces is additive. -/
theorem faceDifference_add (U : Cᵒᵖ) (x y : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    faceDifference J f U (x + y) = faceDifference J f U x + faceDifference J f U y := by
  refine Subtype.ext ?_
  simp only [AddMemClass.coe_add, faceDifference_coe, map_add]
  ring

/-- The difference of the two faces commutes with subtraction. -/
theorem faceDifference_sub (U : Cᵒᵖ) (x y : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    faceDifference J f U (x - y) = faceDifference J f U x - faceDifference J f U y := by
  refine Subtype.ext ?_
  simp only [AddSubgroupClass.coe_sub, faceDifference_coe, map_sub]
  ring

/-- The Leibniz rule for the difference of the two faces:
`d₀(xy) - d₁(xy) = d₀x · (d₀y - d₁y) + d₁y · (d₀x - d₁x)`. -/
theorem faceDifference_mul (U : Cᵒᵖ) (x y : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    faceDifference J f U (x * y) =
      faceSections J f 0 U x • faceDifference J f U y +
        faceSections J f 1 U y • faceDifference J f U x := by
  refine Subtype.ext ?_
  simp only [AddMemClass.coe_add, SetLike.val_smul, faceDifference_coe, map_mul, smul_eq_mul]
  ring

/-- The difference of the two faces vanishes on the image of the structure map `A ⟶ P₁`. -/
theorem faceDifference_resolutionBase (U : Cᵒᵖ) (r : A.obj.obj U) :
    faceDifference J f U ((resolutionBase J f (op ⦋1⦌)).hom.app U r) = 0 := by
  refine Subtype.ext ?_
  rw [ZeroMemClass.coe_zero, faceDifference_coe, faceSections_resolutionBase,
    faceSections_resolutionBase, sub_self]

/-- The difference of the two faces commutes with restriction of local sections. -/
theorem faceDifference_map {U V : Cᵒᵖ} (g : U ⟶ V)
    (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    ((faceDifference J f V ((resolutionTerm J f (op ⦋1⦌)).obj.map g x) :
        Stacks.Sites.Conormal.kernelIdeal (resolutionAugmentation J f (op ⦋0⦌)).hom V) :
      (resolutionTerm J f (op ⦋0⦌)).obj.obj V) =
      (resolutionTerm J f (op ⦋0⦌)).obj.map g
        ((faceDifference J f U x : Stacks.Sites.Conormal.kernelIdeal
          (resolutionAugmentation J f (op ⦋0⦌)).hom U) :
          (resolutionTerm J f (op ⦋0⦌)).obj.obj U) := by
  rw [faceDifference_coe, faceDifference_coe, faceSections_map, faceSections_map,
    show (resolutionTerm J f (op ⦋0⦌)).obj.map g
        (faceSections J f 0 U x - faceSections J f 1 U x) =
      (resolutionTerm J f (op ⦋0⦌)).obj.map g (faceSections J f 0 U x) -
        (resolutionTerm J f (op ⦋0⦌)).obj.map g (faceSections J f 1 U x) from map_sub _ _ _]

/-! ### The degree `-1` component -/

/-- The conormal class of a local section of the kernel `I` of the augmentation `P₀ ⟶ B`. -/
noncomputable def conormalClassSection (U : Cᵒᵖ)
    (y : Stacks.Sites.Conormal.kernelIdeal (resolutionAugmentation J f (op ⦋0⦌)).hom U) :
    (naiveSequence J f).X₁.val.obj U :=
  Stacks.Sites.Conormal.conormalClass.{v, u, max u v w, u} J A
    (resolutionTerm J f (op ⦋0⦌)) B (resolutionBase J f (op ⦋0⦌))
    (resolutionAugmentation J f (op ⦋0⦌)) U y

/-- The conormal class of a local section of `I` is additive. -/
theorem conormalClassSection_add (U : Cᵒᵖ)
    (y y' : Stacks.Sites.Conormal.kernelIdeal (resolutionAugmentation J f (op ⦋0⦌)).hom U) :
    conormalClassSection J f U (y + y') =
      conormalClassSection J f U y + conormalClassSection J f U y' :=
  Stacks.Sites.Conormal.conormalClass_add J A (resolutionTerm J f (op ⦋0⦌)) B
    (resolutionBase J f (op ⦋0⦌)) (resolutionAugmentation J f (op ⦋0⦌)) U y y'

/-- The conormal class of the zero section of `I` is zero. -/
theorem conormalClassSection_zero (U : Cᵒᵖ) :
    conormalClassSection J f U 0 = 0 :=
  Stacks.Sites.Conormal.conormalClass_zero J A (resolutionTerm J f (op ⦋0⦌)) B
    (resolutionBase J f (op ⦋0⦌)) (resolutionAugmentation J f (op ⦋0⦌)) U

/-- The conormal class is semilinear: scaling a section of `I` by a section `p` of `P₀` scales its
class by the image of `p` in `B`. -/
theorem conormalClassSection_smul (U : Cᵒᵖ) (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U)
    (y : Stacks.Sites.Conormal.kernelIdeal (resolutionAugmentation J f (op ⦋0⦌)).hom U) :
    conormalClassSection J f U (p • y) =
      augSections J f U p • conormalClassSection J f U y :=
  Stacks.Sites.Conormal.conormalClass_smul J A (resolutionTerm J f (op ⦋0⦌)) B
    (resolutionBase J f (op ⦋0⦌)) (resolutionAugmentation J f (op ⦋0⦌)) U p y

/-- The conormal class commutes with restriction of local sections. -/
theorem conormalClassSection_map {U V : Cᵒᵖ} (g : U ⟶ V)
    (y : Stacks.Sites.Conormal.kernelIdeal (resolutionAugmentation J f (op ⦋0⦌)).hom U)
    (y' : Stacks.Sites.Conormal.kernelIdeal (resolutionAugmentation J f (op ⦋0⦌)).hom V)
    (h : (y' : (resolutionTerm J f (op ⦋0⦌)).obj.obj V) =
      (resolutionTerm J f (op ⦋0⦌)).obj.map g (y : (resolutionTerm J f (op ⦋0⦌)).obj.obj U)) :
    conormalClassSection J f V y' =
      (naiveSequence J f).X₁.val.map g (conormalClassSection J f U y) :=
  Stacks.Sites.Conormal.conormalClass_map J A (resolutionTerm J f (op ⦋0⦌)) B
    (resolutionBase J f (op ⦋0⦌)) (resolutionAugmentation J f (op ⦋0⦌)) g y y' h

/-- The conormal class `[d₀ x - d₁ x]` of the difference of the two faces: the value on a local
section of `P₁` of the degree `-1` component of the comparison. -/
noncomputable def naiveClass (U : Cᵒᵖ) (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    (naiveSequence J f).X₁.val.obj U :=
  conormalClassSection J f U (faceDifference J f U x)

/-- The class `[d₀ x - d₁ x]` is additive in `x`. -/
theorem naiveClass_add (U : Cᵒᵖ) (x y : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    naiveClass J f U (x + y) = naiveClass J f U x + naiveClass J f U y :=
  (congrArg (conormalClassSection J f U) (faceDifference_add J f U x y)).trans
    (conormalClassSection_add J f U _ _)

/-- The class `[d₀ x - d₁ x]` vanishes when `d₀ x - d₁ x` does. -/
theorem naiveClass_eq_zero (U : Cᵒᵖ) (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U)
    (h : faceDifference J f U x = 0) : naiveClass J f U x = 0 :=
  (congrArg (conormalClassSection J f U) h).trans (conormalClassSection_zero J f U)

/-- The derivation `x ↦ [d₀ x - d₁ x]` of `P₁` with values in the conormal sheaf `I/I²`. -/
noncomputable def naiveClassDerivation :
    resolutionDerivations J f (op ⦋1⦌) (naiveSequence J f).X₁ where
  d {U} := AddMonoidHom.mk' (naiveClass J f U) (naiveClass_add J f U)
  d_mul {U} x y := by
    change naiveClass J f U (x * y) =
      (resolutionAugmentation J f (op ⦋1⦌)).hom.app U x •
        (naiveClass J f U y : (naiveSequence J f).X₁.val.obj U) +
      (resolutionAugmentation J f (op ⦋1⦌)).hom.app U y •
        (naiveClass J f U x : (naiveSequence J f).X₁.val.obj U)
    refine Eq.trans (congrArg (conormalClassSection J f U) (faceDifference_mul J f U x y)) ?_
    refine Eq.trans (conormalClassSection_add J f U _ _) ?_
    refine Eq.trans (congrArg₂ (fun s t : (naiveSequence J f).X₁.val.obj U => s + t)
      (conormalClassSection_smul J f U _ _) (conormalClassSection_smul J f U _ _)) ?_
    exact congrArg₂ (fun s t : B.obj.obj U =>
        s • (naiveClass J f U y : (naiveSequence J f).X₁.val.obj U) +
          t • (naiveClass J f U x : (naiveSequence J f).X₁.val.obj U))
      (augSections_faceSections J f 0 U x) (augSections_faceSections J f 1 U y)
  d_map {U V} g x :=
    conormalClassSection_map J f g _ _ (faceDifference_map J f g x)
  d_app {U} r := naiveClass_eq_zero J f U _ (faceDifference_resolutionBase J f U r)

/-- **The degree `-1` component of the canonical map of Tag 08US**: the morphism
`Ω_{P₁/A} ⊗_{P₁} B ⟶ I/I²` corepresented by the derivation `x ↦ [d₀ x - d₁ x]`. -/
noncomputable def naiveComparisonNegOne :
    (cotangentSimplicialModule J f).object.obj (op ⦋1⦌) ⟶ (naiveSequence J f).X₁ :=
  ((cotangentSimplicialModule J f).derivationEquiv (op ⦋1⦌) (naiveSequence J f).X₁).symm
    (naiveClassDerivation J f)

/-- The degree `-1` component sends a pure differential `d x` to the class of `d₀ x - d₁ x`
in `I/I²`. -/
theorem derivationEquiv_naiveComparisonNegOne (U : Cᵒᵖ)
    (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    ((cotangentSimplicialModule J f).derivationEquiv (op ⦋1⦌) (naiveSequence J f).X₁
        (naiveComparisonNegOne J f)).d x = naiveClass J f U x :=
  congrArg (fun D : resolutionDerivations J f (op ⦋1⦌) (naiveSequence J f).X₁ => D.d (X := U) x)
    (Equiv.apply_symm_apply _ (naiveClassDerivation J f))

/-- **Stacks 08US, the degree `-1` component of the canonical map.** On the pure differential
`d x` of a local section `x` of `P₁`, the comparison is the class of `d₀ x - d₁ x` in `I/I²`;
the general local section `d x ⊗ b` goes to `b` times that class. -/
@[stacks 08US "the degree `-1` component of the canonical map `L_{B/A} → NL_{B/A}`, with its
value `[d₀ x - d₁ x]` on a pure differential. Hypotheses beyond the source: the naive cotangent
complex is realized as the conormal sequence of the presentation `P₀ ⟶ B` by the degree-zero
term of the standard resolution, and the identification of that presentation with
`Stacks.Sites.FreeAlgebra.canonicalPresentation` is not carried. The identification of the naive
complex with the truncation `τ_{≥ -1} L_{B/A}` is NOT proved: the source proves it by comparison
with the chaotic topology, and that comparison is not carried. Tag 08TZ, which it uses, IS
formalized, as `Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso`"]
theorem naiveComparisonNegOne_conormalClass (U : Cᵒᵖ)
    (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    (naiveComparisonNegOne J f).val.app U
        (((cotangentSimplicialModule J f).universalDerivation (op ⦋1⦌)).d x) =
      conormalClassSection J f U (faceDifference J f U x) :=
  (derivationEquiv_val_app J f (op ⦋1⦌) (naiveSequence J f).X₁
    (naiveComparisonNegOne J f) U x).symm.trans
      (derivationEquiv_naiveComparisonNegOne J f U x)

/-- The conormal class of a local section of `I` commutes with subtraction. -/
theorem conormalClassSection_sub (U : Cᵒᵖ)
    (y y' : Stacks.Sites.Conormal.kernelIdeal (resolutionAugmentation J f (op ⦋0⦌)).hom U) :
    conormalClassSection J f U (y - y') =
      conormalClassSection J f U y - conormalClassSection J f U y' := by
  refine eq_sub_of_add_eq (Eq.trans (conormalClassSection_add J f U (y - y') y').symm ?_)
  exact congrArg (conormalClassSection J f U) (sub_add_cancel y y')

/-- The class `[d₀ x - d₁ x]` commutes with subtraction in `x`. -/
theorem naiveClass_sub (U : Cᵒᵖ) (x y : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    naiveClass J f U (x - y) = naiveClass J f U x - naiveClass J f U y :=
  (congrArg (conormalClassSection J f U) (faceDifference_sub J f U x y)).trans
    (conormalClassSection_sub J f U _ _)

/-! ### The two commuting squares -/

/-- Subtraction of morphisms of sheaves of modules is computed on local sections. -/
theorem sub_val_app {M N : targetModules J B} (h₁ h₂ : M ⟶ N) (U : Cᵒᵖ) (y : M.val.obj U) :
    (h₁ - h₂).val.app U y = h₁.val.app U y - h₂.val.app U y := rfl

/-- Addition of morphisms of sheaves of modules is computed on local sections. -/
theorem add_val_app {M N : targetModules J B} (h₁ h₂ : M ⟶ N) (U : Cᵒᵖ) (y : M.val.obj U) :
    (h₁ + h₂).val.app U y = h₁.val.app U y + h₂.val.app U y := rfl

/-- The zero morphism of sheaves of modules vanishes on local sections. -/
theorem zero_val_app {M N : targetModules J B} (U : Cᵒᵖ) (y : M.val.obj U) :
    (0 : M ⟶ N).val.app U y = 0 := rfl

/-- **Stacks 08US, the lower commuting square.** Following the degree `-1` component by the
differential `I/I² ⟶ B ⊗_{P₀} Ω_{P₀/A}` of the naive cotangent complex is the difference of the
two faces `Ω_{P₁/A} ⊗ B ⇉ Ω_{P₀/A} ⊗ B` followed by the degree-zero component.  The difference
of the two faces is the differential of the cotangent complex out of degree `-1`, so this is the
lower square of the comparison diagram: the differential of the naive complex sends
`[d₀ x - d₁ x]` to `1 ⊗ d(d₀ x - d₁ x)`. -/
@[stacks 08US "the lower commuting square: the degree `-1` component composed with the
differential of the naive cotangent complex is the difference of the two faces composed with the
degree-zero component. Hypotheses beyond the source: the naive cotangent complex is realized as
the conormal sequence of the presentation `P₀ ⟶ B` by the degree-zero term of the standard
resolution, and the differential of `L_{B/A}` appears as the difference of the two face maps of
the base-changed simplicial module rather than transported through
`CategoryTheory.Sheaf.cotangentComplex_degreeIso`"]
theorem naiveComparisonNegOne_comp_conormal :
    naiveComparisonNegOne J f ≫ (naiveSequence J f).f =
      (cotangentSimplicialModule J f).object.δ 0 ≫ naiveComparisonZero J f -
        (cotangentSimplicialModule J f).object.δ 1 ≫ naiveComparisonZero J f := by
  refine hom_ext_of_derivationEquiv J f (op ⦋1⦌) fun U x => ?_
  have hleft : ((cotangentSimplicialModule J f).derivationEquiv (op ⦋1⦌)
      (naiveSequence J f).X₂
        (naiveComparisonNegOne J f ≫ (naiveSequence J f).f)).d x =
      tensorDifferentialSections J f U
        ((faceDifference J f U x : Stacks.Sites.Conormal.kernelIdeal
          (resolutionAugmentation J f (op ⦋0⦌)).hom U) :
          (resolutionTerm J f (op ⦋0⦌)).obj.obj U) := by
    refine Eq.trans (derivationEquiv_val_app J f (op ⦋1⦌) (naiveSequence J f).X₂ _ U x) ?_
    refine Eq.trans (congrArg ((naiveSequence J f).f.val.app U)
      (naiveComparisonNegOne_conormalClass J f U x)) ?_
    exact Stacks.Sites.Conormal.conormalSequence_f_class J A (resolutionTerm J f (op ⦋0⦌)) B
      (resolutionBase J f (op ⦋0⦌)) (resolutionAugmentation J f (op ⦋0⦌)) U _
  have hface (k : Fin 2) :
      ((cotangentSimplicialModule J f).object.δ k ≫ naiveComparisonZero J f).val.app U
          (((cotangentSimplicialModule J f).universalDerivation (op ⦋1⦌)).d x) =
        tensorDifferentialSections J f U (faceSections J f k U x) :=
    (delta_comp_val_app J f 0 (naiveSequence J f).X₂ k (naiveComparisonZero J f) U x).trans
      (derivationEquiv_naiveComparisonZero J f U (faceSections J f k U x))
  have hright : ((cotangentSimplicialModule J f).derivationEquiv (op ⦋1⦌)
      (naiveSequence J f).X₂
        ((cotangentSimplicialModule J f).object.δ 0 ≫ naiveComparisonZero J f -
          (cotangentSimplicialModule J f).object.δ 1 ≫ naiveComparisonZero J f)).d x =
      tensorDifferentialSections J f U (faceSections J f 0 U x) -
        tensorDifferentialSections J f U (faceSections J f 1 U x) := by
    refine Eq.trans (derivationEquiv_val_app J f (op ⦋1⦌) (naiveSequence J f).X₂ _ U x) ?_
    exact (sub_val_app J _ _ U _).trans (congrArg₂ Sub.sub (hface 0) (hface 1))
  refine hleft.trans (Eq.trans ?_ hright.symm)
  refine Eq.trans (congrArg (tensorDifferentialSections J f U)
    (faceDifference_coe J f U x)) ?_
  exact map_sub ((tensorDifferentialDerivation J f).d (X := U))
    (faceSections J f 0 U x) (faceSections J f 1 U x)

/-- The simplicial identities make the alternating sum of three local sections of `P₁` coming
from a local section of `P₂` lie in `I²`: its difference of faces vanishes. -/
theorem faceDifference_alternating (U : Cᵒᵖ)
    (y₀ y₁ y₂ : (resolutionTerm J f (op ⦋1⦌)).obj.obj U)
    (h₀ : faceSections J f 0 U y₁ = faceSections J f 0 U y₀)
    (h₁ : faceSections J f 0 U y₂ = faceSections J f 1 U y₀)
    (h₂ : faceSections J f 1 U y₂ = faceSections J f 1 U y₁) :
    faceDifference J f U (y₀ - y₁ + y₂) = 0 := by
  refine Subtype.ext ?_
  simp only [ZeroMemClass.coe_zero, faceDifference_coe, map_add, map_sub]
  linear_combination (norm := ring_nf) -h₀ + h₁ - h₂

/-- **Stacks 08US, the upper commuting square.** The degree `-1` component annihilates the
alternating sum of the three faces `Ω_{P₂/A} ⊗ B ⟶ Ω_{P₁/A} ⊗ B`, which is the differential of
the cotangent complex into degree `-1`.  The naive cotangent complex is zero in degree `-2`, so
this is exactly the commutation of the comparison with that differential. -/
@[stacks 08US "the upper commuting square: the degree `-1` component annihilates the alternating
sum of the three faces, which is the differential of `L_{B/A}` into degree `-1`, the naive
cotangent complex being zero in degree `-2`. Hypotheses beyond the source: the naive cotangent
complex is realized as the conormal sequence of the presentation `P₀ ⟶ B` by the degree-zero term
of the standard resolution, and the differential of `L_{B/A}` appears as the alternating sum of
the face maps of the base-changed simplicial module rather than transported through
`CategoryTheory.Sheaf.cotangentComplex_degreeIso`"]
theorem naiveComparisonNegOne_faceSum :
    ((cotangentSimplicialModule J f).object.δ (0 : Fin 3) -
        (cotangentSimplicialModule J f).object.δ (1 : Fin 3) +
        (cotangentSimplicialModule J f).object.δ (2 : Fin 3)) ≫
      naiveComparisonNegOne J f = 0 := by
  refine hom_ext_of_derivationEquiv J f (op ⦋2⦌) fun U x => ?_
  have hzero : ((cotangentSimplicialModule J f).derivationEquiv (op ⦋2⦌)
      (naiveSequence J f).X₁ 0).d x = 0 :=
    (derivationEquiv_val_app J f (op ⦋2⦌) (naiveSequence J f).X₁ 0 U x).trans
      (zero_val_app J U _)
  have hface (k : Fin 3) :
      ((cotangentSimplicialModule J f).object.δ k ≫ naiveComparisonNegOne J f).val.app U
          (((cotangentSimplicialModule J f).universalDerivation (op ⦋2⦌)).d x) =
        naiveClass J f U (((standardResolution J f).left.δ k).right.hom.app U x) :=
    (delta_comp_val_app J f 1 (naiveSequence J f).X₁ k (naiveComparisonNegOne J f) U x).trans
      (derivationEquiv_naiveComparisonNegOne J f U _)
  have hcomp : ((cotangentSimplicialModule J f).object.δ (0 : Fin 3) -
        (cotangentSimplicialModule J f).object.δ (1 : Fin 3) +
        (cotangentSimplicialModule J f).object.δ (2 : Fin 3)) ≫
      naiveComparisonNegOne J f =
      (cotangentSimplicialModule J f).object.δ (0 : Fin 3) ≫ naiveComparisonNegOne J f -
        (cotangentSimplicialModule J f).object.δ (1 : Fin 3) ≫ naiveComparisonNegOne J f +
        (cotangentSimplicialModule J f).object.δ (2 : Fin 3) ≫ naiveComparisonNegOne J f := by
    rw [Preadditive.add_comp, Preadditive.sub_comp]
  refine Eq.trans (derivationEquiv_val_app J f (op ⦋2⦌) (naiveSequence J f).X₁ _ U x) ?_
  refine Eq.trans (congrArg (fun h => h.val.app U
    (((cotangentSimplicialModule J f).universalDerivation (op ⦋2⦌)).d x)) hcomp) ?_
  refine Eq.trans ((add_val_app J _ _ U _).trans
    (congrArg (· + _) (sub_val_app J _ _ U _))) (Eq.trans ?_ hzero.symm)
  rw [hface 0, hface 1, hface 2]
  have hδ (i j : Fin 2) (hij : i ≤ j) :=
    congrArg (fun t : (standardResolution J f).left.obj (op ⦋2⦌) ⟶
        (standardResolution J f).left.obj (op ⦋0⦌) => t.right.hom.app U x)
      ((standardResolution J f).left.δ_comp_δ hij)
  refine Eq.trans ?_ (naiveClass_eq_zero J f U _
    (faceDifference_alternating J f U _ _ _ (hδ 0 0 le_rfl) (hδ 0 1 (by decide))
      (hδ 1 1 le_rfl)))
  exact ((naiveClass_add J f U _ _).trans
    (congrArg (· + naiveClass J f U
      (((standardResolution J f).left.δ (2 : Fin 3)).right.hom.app U x))
      (naiveClass_sub J f U _ _))).symm

end CategoryTheory.Sheaf

end
