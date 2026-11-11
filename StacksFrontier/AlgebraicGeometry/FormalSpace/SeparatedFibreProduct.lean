module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanCriterionPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealMapToSpec
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProductFactorisation

/-!
# Fibre products of affine formal algebraic spaces over a separated formal algebraic space

Let `S` be a scheme contained in a big fppf site `B` and let `X ⟶ Z` and `Y ⟶ Z` be morphisms
of formal algebraic spaces over `S` with `Z` separated. **Stacks 0AN3** says that `X ×_Z Y` is
an affine formal algebraic space when `X` and `Y` are (clause (1)), that it is moreover McQuillan
when `X` and `Y` are (clause (2)), and that when `X`, `Y` and `Z` are all McQuillan, presented by
the weakly admissible topological rings `A`, `B` and `C`, the fibre product is presented by the
completed tensor product `A ⊗̂_C B` (clause (3)).

This file carries clauses (1) and (2) under the hypotheses of the source: `Z` is a *formal
algebraic space*, not merely an fppf sheaf, and nothing beyond its separatedness is assumed of
it. The general version `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_pullback` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct` carries, besides separatedness,
the hypothesis `AlgebraicGeometry.FormalSpace.HasRepresentableRelativeProducts` that the fibre
product over `Z` of two represented sheaves is again represented. For a formal algebraic space
that is a theorem — it is the representability clause of **Stacks 0AIP** — so under the source's
own hypotheses the extra conjunct disappears.

Clause (2) is proved the way the source proves it: a closed immersion of an affine scheme of the
site into `X ×_Z Y` factors through the fibre product over `Z` of two affine thickening stages,
one of each factor, and that fibre product is closed-immersed in the spectrum of the tensor
product over `ℤ` of the two coordinate rings because `Z` is separated. Composing with the two
closed immersions of the stages into the spectra of the two presenting rings exhibits
`X ×_Z Y ⟶ Spec (A ⊗_ℤ B)` as a witness of McQuillanness.

Clause (3) is **not** in this file: see the implementation notes.

## Main results

* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace`:
  **Stacks 0AN3, clause (1)**, under the source's hypotheses.
* `…isAffineFormalAlgebraicSpace_pullback_of_isAffineFormalAlgebraicSpace`: clause (1) over an
  affine formal algebraic space, where both hypotheses on the base are theorems.
* `AlgebraicGeometry.FormalSpace.hasAffineClosedImmersionCriterion_pullback`:
  **Stacks 0AN3, clause (2)**, with McQuillanness in the form of condition (2) of
  **Stacks 0AIC** on both sides.
* `AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_pullback`: the same clause with
  the conclusion in the form of condition (4) of **Stacks 0AIC**, which is the predicate
  **Stacks 0AID** names McQuillan in this library.

## Implementation notes

Representability of the relative products of `Z` is deduced from representability of the
absolute diagonal of `Z`, which is
`AlgebraicGeometry.FormalSpace.relativelyRepresentable_diag_of_isFormalAlgebraicSpace`, by
`CategoryTheory.Functor.relativelyRepresentable.of_diag`; that step needs the sheafified Yoneda
embedding to be full and to preserve binary products, both of which hold because the big fppf
site is subcanonical.

Separatedness of `Z` is `AlgebraicGeometry.FormalSpace.IsSeparated`, clause (2) of
**Stacks 0AJ6**, which is one of the two equivalent conditions that **Stacks 0AJ7** takes as the
definition of a separated formal algebraic space. The hypothesis that `X` and `Y` are formal
algebraic spaces is not stated separately: an affine formal algebraic space is one.

McQuillanness is read off **Stacks 0AIC**, whose five conditions the source takes as equivalent
and whose equivalence this library generates: the implication graph over the five conditions is
strongly connected. Clause (2) is stated with condition (2) of 0AIC — an affine formal
algebraic space with a morphism to the spectrum of a ring, turning every closed immersion of an
affine scheme of the site into a closed immersion — on both sides, which makes the hypothesis
and the conclusion one and the same notion. Condition (4), the predicate 0AID names McQuillan
here, follows from it by the implications (2) ⟹ (5) ⟹ (4) that the library carries, and the
converse arrow (4) ⟹ (2) is available as
`AlgebraicGeometry.FormalSpace.hasAffineClosedImmersionCriterion_of_hasSomeSurjectivePresentation`;
the condition-(4) form is stated here only as a conclusion, which is a choice of shape rather
than a consequence of what is available.

Clause (3) is not proved. Beyond this file it would need: the open ideals
`ker (A ⊗̂_C B ⟶ A/I ⊗_C B/J)` of
`StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.QuotientLimit` to be
recognised as weak ideals of definition of `A ⊗̂_C B` and shown cofinal among them, with their
quotients identified with `A/I ⊗_C B/J`; and an interchange
`colim_I X_I ×_Z colim_J Y_J ≅ colim_{I, J} (X_I ×_Z Y_J)` in two filtered variables, of which
`StacksFrontier.AlgebraicGeometry.FormalSpace.StageBaseChangeColimit` carries only the one-variable
case. None of that is in the library.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AJ6](https://stacks.math.columbia.edu/tag/0AJ6)
* [Stacks Project, Tag 0AJ7](https://stacks.math.columbia.edu/tag/0AJ7)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The fibre product of two affine formal algebraic spaces over an affine formal algebraic
space is an affine formal algebraic space.** Over such a base no hypothesis is left: the
relative products of an affine formal algebraic space are represented, by the representability
clause of **Stacks 0AIP** for it, and an affine formal algebraic space is separated in the
sense of clause (2) of **Stacks 0AJ6**. -/
theorem isAffineFormalAlgebraicSpace_pullback_of_isAffineFormalAlgebraicSpace
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hZ : IsAffineFormalAlgebraicSpace B S hS Z)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y) :
    IsAffineFormalAlgebraicSpace B S hS (pullback p q) :=
  isAffineFormalAlgebraicSpace_pullback B S hS p q
    (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hZ)
    (IsAffineFormalAlgebraicSpace.isSeparated B S hS hZ) hX hY

/-! ### Clause (2): the McQuillan case -/

section McQuillan

open scoped TensorProduct

/-- The ring map corresponding to a morphism of schemes into the spectrum of a ring. -/
private noncomputable abbrev specHomOf {R : CommRingCat.{u}} {T : Scheme.{u}}
    (h : T ⟶ Spec R) : R ⟶ Γ(T, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ h.appTop

/-- A morphism of schemes into the spectrum of a ring is recovered from the ring map it
induces on global sections. -/
private theorem toSpecΓ_specHomOf {R : CommRingCat.{u}} {T : Scheme.{u}} (h : T ⟶ Spec R) :
    T.toSpecΓ ≫ Spec.map (specHomOf h) = h := by
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

/-- A closed immersion of an affine scheme into the spectrum of a ring is surjective on global
sections. -/
private theorem surjective_specHomOf {R : CommRingCat.{u}} {T : Scheme.{u}} (h : T ⟶ Spec R)
    [_root_.AlgebraicGeometry.IsClosedImmersion h] :
    Function.Surjective (specHomOf h).hom.toIntAlgHom := by
  obtain ⟨-, hs⟩ := _root_.AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine h
  change Function.Surjective ((Scheme.ΓSpecIso R).inv ≫ h.appTop).hom
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  exact hs.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).2

/-- The ring map out of the tensor product over `ℤ` determined by two morphisms of schemes
into two spectra. -/
private noncomputable abbrev tensorHom {A₁ A₂ : CommRingCat.{u}} {T : Scheme.{u}}
    (h₁ : T ⟶ Spec A₁) (h₂ : T ⟶ Spec A₂) :
    (↥A₁ ⊗[ℤ] ↥A₂) →+* ↥Γ(T, ⊤) :=
  (Algebra.TensorProduct.lift (specHomOf h₁).hom.toIntAlgHom (specHomOf h₂).hom.toIntAlgHom
    (fun _ _ ↦ Commute.all _ _)).toRingHom

/-- Postcomposing a morphism into the spectrum of a ring with a morphism of schemes
postcomposes the ring map out of the tensor product over `ℤ`. -/
private theorem tensorHom_comp {A₁ A₂ : CommRingCat.{u}} {T T' : Scheme.{u}} (u : T' ⟶ T)
    (h₁ : T ⟶ Spec A₁) (h₂ : T ⟶ Spec A₂) :
    tensorHom (u ≫ h₁) (u ≫ h₂) = u.appTop.hom.comp (tensorHom h₁ h₂) := by
  refine RingHom.ext fun w ↦ ?_
  induction w with
  | tmul a b =>
    simp only [tensorHom, specHomOf, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul,
      RingHom.toIntAlgHom_coe, RingHom.coe_comp, Function.comp_apply]
    exact (map_mul _ _ _).symm
  | add w₁ w₂ hw₁ hw₂ => simp only [map_add, hw₁, hw₂]

/-- The ring map out of the tensor product over `ℤ` attached to two morphisms into spectra
which factor through two further morphisms is the map attached to those further morphisms,
composed with the tensor product of the two factorisations. -/
private theorem tensorHom_comp_eq {A₁ A₂ : CommRingCat.{u}} {T T₁ T₂ : Scheme.{u}}
    (u₁ : T ⟶ T₁) (u₂ : T ⟶ T₂) (k₁ : T₁ ⟶ Spec A₁) (k₂ : T₂ ⟶ Spec A₂)
    (w : ↥A₁ ⊗[ℤ] ↥A₂) :
    tensorHom (u₁ ≫ k₁) (u₂ ≫ k₂) w =
      (Algebra.TensorProduct.lift u₁.appTop.hom.toIntAlgHom u₂.appTop.hom.toIntAlgHom
          (fun _ _ ↦ Commute.all _ _))
        (Algebra.TensorProduct.map (specHomOf k₁).hom.toIntAlgHom
          (specHomOf k₂).hom.toIntAlgHom w) := by
  induction w with
  | tmul a b =>
    simp only [tensorHom, specHomOf, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.map_tmul, RingHom.toIntAlgHom_coe, RingHom.coe_comp,
      Function.comp_apply]
  | add w₁ w₂ hw₁ hw₂ => simp only [map_add, hw₁, hw₂]

/-- The morphism into the spectrum of the tensor product over `ℤ` of two rings determined by
two morphisms into their spectra. -/
private noncomputable def tensorApp {A₁ A₂ : CommRingCat.{u}} {T : Scheme.{u}}
    (h₁ : T ⟶ Spec A₁) (h₂ : T ⟶ Spec A₂) :
    T ⟶ Spec (CommRingCat.of (↥A₁ ⊗[ℤ] ↥A₂)) :=
  T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (tensorHom h₁ h₂))

/-- The morphism into the spectrum of the tensor product is natural in the source. -/
private theorem comp_tensorApp {A₁ A₂ : CommRingCat.{u}} {T T' : Scheme.{u}} (u : T' ⟶ T)
    (h₁ : T ⟶ Spec A₁) (h₂ : T ⟶ Spec A₂) :
    u ≫ tensorApp h₁ h₂ = tensorApp (u ≫ h₁) (u ≫ h₂) := by
  have key : CommRingCat.ofHom (tensorHom h₁ h₂) ≫ u.appTop =
      CommRingCat.ofHom (tensorHom (u ≫ h₁) (u ≫ h₂)) := by
    refine CommRingCat.hom_ext ?_
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, tensorHom_comp]
  rw [tensorApp, tensorApp, ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc,
    ← Spec.map_comp, key]

/-- The morphism into the spectrum of the tensor product out of an affine scheme is a closed
immersion as soon as the ring map it is built from is surjective. -/
private theorem isClosedImmersion_tensorApp {A₁ A₂ : CommRingCat.{u}} {T : Scheme.{u}}
    [IsAffine T] (h₁ : T ⟶ Spec A₁) (h₂ : T ⟶ Spec A₂)
    (hsurj : Function.Surjective (tensorHom h₁ h₂)) :
    _root_.AlgebraicGeometry.IsClosedImmersion (tensorApp h₁ h₂) := by
  have _ :
      _root_.AlgebraicGeometry.IsClosedImmersion (Spec.map (CommRingCat.ofHom (tensorHom h₁ h₂))) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ hsurj
  rw [tensorApp]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) _ _).mpr
      inferInstance

/-- The morphism of a fibre product of fppf sheaves to the spectrum of the tensor product over
`ℤ` of two rings receiving the two factors. -/
private noncomputable def mapToSchemeTensor {X Y Z : FppfSheaf B S hS}
    (p : X ⟶ Z) (q : Y ⟶ Z) {A₁ A₂ : CommRingCat.{u}}
    (m₁ : MapToScheme B S hS (Spec A₁) X) (m₂ : MapToScheme B S hS (Spec A₂) Y) :
    MapToScheme B S hS (Spec (CommRingCat.of (↥A₁ ⊗[ℤ] ↥A₂))) (pullback p q) where
  app T g := tensorApp (m₁.app T (g ≫ pullback.fst p q)) (m₂.app T (g ≫ pullback.snd p q))
  app_naturality T T' u g := by
    rw [comp_tensorApp, Category.assoc, Category.assoc,
      m₁.app_naturality T T' u (g ≫ pullback.fst p q),
      m₂.app_naturality T T' u (g ≫ pullback.snd p q)]

/-- **Stacks 0AN3, clause (2).** Let `X ⟶ Z` and `Y ⟶ Z` be morphisms of fppf sheaves on the
big fppf site of `S` with `Z` a separated formal algebraic space. If `X` and `Y` are McQuillan
affine formal algebraic spaces, then so is the fibre product `X ×_Z Y`.

McQuillanness is here condition (2) of **Stacks 0AIC**: an affine formal algebraic space
together with a morphism to the spectrum of a ring through which every closed
immersion of an affine scheme of the site composes to a closed immersion of schemes. The ring
witnessing the conclusion is the tensor product over `ℤ` of the two rings witnessing the
hypotheses, which is the ring the source's proof uses. -/
theorem hasAffineClosedImmersionCriterion_pullback
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hZsep : IsSeparated B S hS Z)
    (hX : HasAffineClosedImmersionCriterionMapToSpec B S hS X)
    (hY : HasAffineClosedImmersionCriterionMapToSpec B S hS Y) :
    HasAffineClosedImmersionCriterionMapToSpec B S hS (pullback p q) := by
  classical
  obtain ⟨hXaff, A₁, m₁, hm₁⟩ := hX
  obtain ⟨hYaff, A₂, m₂, hm₂⟩ := hY
  have hZrep := hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hZ
  refine ⟨isAffineFormalAlgebraicSpace_pullback B S hS p q hZrep hZsep hXaff hYaff,
    CommRingCat.of (↥A₁ ⊗[ℤ] ↥A₂), mapToSchemeTensor B S hS p q m₁ m₂, ?_⟩
  intro T g hg
  obtain ⟨T₁, T₂, h₁, h₂, u₁, u₂, hci₁, hci₂, hfst, hsnd, hsurj⟩ :=
    exists_isClosedImmersion_factorisation_pullback B S hS p q hZrep hZsep hXaff hYaff T hg
  have _ : ∀ T' : BigAffineFppf B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj T')) := fun T' ↦ T'.property
  have _ := hm₁ T₁ h₁ hci₁
  have _ := hm₂ T₂ h₂ hci₂
  refine isClosedImmersion_tensorApp _ _ ?_
  rw [hfst, hsnd, m₁.app_naturality, m₂.app_naturality]
  intro z
  obtain ⟨y, hy⟩ := hsurj z
  obtain ⟨x, hx⟩ := Algebra.TensorProduct.map_surjective
    ((specHomOf (m₁.app ((BigAffineFppf.inclusion B S hS).obj T₁) h₁)).hom.toIntAlgHom)
    ((specHomOf (m₂.app ((BigAffineFppf.inclusion B S hS).obj T₂) h₂)).hom.toIntAlgHom)
    (surjective_specHomOf (m₁.app ((BigAffineFppf.inclusion B S hS).obj T₁) h₁))
    (surjective_specHomOf (m₂.app ((BigAffineFppf.inclusion B S hS).obj T₂) h₂)) y
  exact ⟨x, by rw [tensorHom_comp_eq, hx, hy]⟩

/-- **Stacks 0AN3, clause (2), in the form of condition (4) of Stacks 0AIC.** The fibre product
of two McQuillan affine formal algebraic spaces over a separated formal algebraic space is an
affine formal algebraic space some presentation of which by affine thickenings has surjective
section-ring projections.

This is the predicate `AlgebraicGeometry.FormalSpace.HasSomeSurjectivePresentation` that
**Stacks 0AID** names "McQuillan" in this library, and it is the hypothesis as well as the
conclusion: condition (4) gives condition (2) by
`AlgebraicGeometry.FormalSpace.hasAffineClosedImmersionCriterion_of_hasSomeSurjectivePresentation`,
and condition (2) gives condition (4) back by the implications (2) ⟹ (5) ⟹ (4) of
**Stacks 0AIC**. -/
theorem hasSomeSurjectivePresentation_pullback
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hZsep : IsSeparated B S hS Z)
    (hX : HasSomeSurjectivePresentation B S hS X)
    (hY : HasSomeSurjectivePresentation B S hS Y) :
    HasSomeSurjectivePresentation B S hS (pullback p q) :=
  (HasAffineClosedImmersionCriterionMapToSpec.hasAllSurjectivePresentations B S hS
    (hasAffineClosedImmersionCriterion_pullback B S hS p q hZ hZsep
      (hasAffineClosedImmersionCriterion_of_hasSomeSurjectivePresentation B S hS hX)
      (hasAffineClosedImmersionCriterion_of_hasSomeSurjectivePresentation B S hS
        hY))).hasSomeSurjectivePresentation B S hS

end McQuillan

end AlgebraicGeometry.FormalSpace

end
