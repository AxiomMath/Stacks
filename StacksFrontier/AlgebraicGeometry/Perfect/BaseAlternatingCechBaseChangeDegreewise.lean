module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsBaseChange

/-!
# The degreewise components of the Čech base-change isomorphism

`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.baseAlternatingCechComplexBaseChangeIso` of
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatGlobalSectionsBaseChange.lean` is an
isomorphism of `ℤ`-indexed complexes of `A'`-modules

`(- ⊗_A A') (baseAlternatingCechComplex f U F) ≅ baseAlternatingCechComplex f' (g⁻¹ U) (g^* F)`,

built as a four-fold composite of two instances of `baseAlternatingCechComplexIsoExtend`, the
comparison `Stacks.DerivedIndexing.mapExtendIso` of extension by zero with a functor applied
termwise, and the extension by zero of the `ℕ`-indexed comparison
`Stacks.Cech.alternatingCechModuleComplexBaseChangeIso`. Nothing in that file says what the
composite *is* in a single degree, so no identity between composites of these isomorphisms can
be checked.

This file supplies the two statements that make such a check possible: a closed form for the
component in a nonnegative degree, and a degreewise uniqueness principle which says that the
nonnegative degrees are all there is to check.

## Main results

* `Stacks.DerivedIndexing.mapExtendIso_inv_f_comp_extendMap_f_comp_extendXIso` and
  `Stacks.DerivedIndexing.map_f_comp_mapExtendIso_inv_f_comp_extendMap_f_comp`: for an additive
  `G` and a morphism `ψ` out of the termwise image of `G`, the comparison `mapExtendIso`
  followed by the extension by zero of `ψ` has, in a degree in the range of the embedding, the
  component of `ψ` conjugated by the comparisons `HomologicalComplex.extendXIso` — bare, and
  flanked by two identifications of the extensions by zero with other complexes, which is the
  shape in which the transport of an `ℕ`-indexed comparison to the `ℤ`-indexed models occurs.
  Abstract: the embedding, the shapes, the categories and the degree are arbitrary.
* `…ProperFlatGlobalSections.baseAlternatingCechComplexIsoExtend_hom_f_comp_extendXIso`: in a
  nonnegative degree the identification of the `A`-linear model with the extension by zero of
  the `ℕ`-indexed alternating Čech complex is, through `HomologicalComplex.extendXIso`, exactly
  `baseAlternatingCechComplexXIso`.
* `…ProperFlatGlobalSections.baseAlternatingCechComplexBaseChangeIso_hom_f_comp_XIso` and
  `…ProperFlatGlobalSections.baseAlternatingCechComplexBaseChangeIso_hom_f`: **in a nonnegative
  degree `m` the base-change isomorphism is the `ℕ`-level degreewise comparison
  `Stacks.Cech.alternatingCechModuleObjBaseChangeIso` of
  `StacksFrontier/AlgebraicGeometry/Modules/AlternatingCechModuleBaseChange.lean`**, conjugated by
  the two degree isomorphisms `baseAlternatingCechComplexXIso` — the source one extended along
  `φ`. The second is the closed form of the first.
* `…ProperFlatGlobalSections.hom_ext_baseAlternatingCechComplex`: **two morphisms of
  `ℤ`-indexed complexes into `baseAlternatingCechComplex f U hU F` which agree in every
  nonnegative degree are equal.** The source is arbitrary, so this applies to the composites of
  the isomorphisms above.

Together these reduce an identity between composites of the `ℤ`-indexed base-change
isomorphisms to an identity at the `ℕ` level: the uniqueness principle leaves only the degrees
`(m : ℤ)` for `m : ℕ`, and the closed form rewrites the component there as the `ℕ`-level
comparison.

## Implementation notes

**Why the negative degrees are free.** The target `baseAlternatingCechComplex f U hU F` is the
restriction of scalars of an extension by zero along `ComplexShape.embeddingUpNat`, so it
vanishes in every negative degree — `isZero_baseAlternatingCechComplex_X_of_neg` — and
`CategoryTheory.Limits.IsZero.eq_of_tgt` closes those degrees for any pair of morphisms into it.
The degrees of `ℤ` are exhausted by the nonnegative ones and the negative ones, which is the
only case distinction in `hom_ext_baseAlternatingCechComplex`.

**Every proof argument appearing in a statement is supplied by a named lemma, never by `rfl`.**
Two of the proof obligations occurring as arguments of the definitions compared here —
`ComplexShape.embeddingUpNat.f m = (m : ℤ)` for `HomologicalComplex.extendXIso`, and
`(fun i => g ⁻¹ᵁ U i) i = g ⁻¹ᵁ U (Equiv.refl _ i)` for `Stacks.Cech.cechBaseChangeData` — hold
by `rfl`, but the *term* `rfl` elaborates against them to `@rfl _ a` with `a` the left-hand
side, whose type is therefore not syntactically the expected one. Both definitions then fail to
typecheck at reducible transparency, which is the transparency at which `rw` revalidates the
goal, and every rewrite is refused with "did not find an occurrence" and an application type
mismatch underneath. `ComplexShape.embeddingUpNat_f` and `preimage_eq_preimage_equivRefl` are
used instead: being theorems, their types are the declared ones.

**The `A`-linear model is compared through an abstract lemma, not by rewriting in place.** The
`Γ(X, 𝒪_X)`-linear complex `Stacks.Cohomology.CechSheaf.alternatingModuleComplex ⊤ U hU F` takes
`X.ringCatSheaf` for a sheaf on the Grothendieck topology of the opens of `X`, and that
identification of types does not hold at reducible transparency either, so no `rw` can run on a
goal mentioning it. `Stacks.DerivedIndexing.mapExtendIso_inv_f_comp_extendMap_f_comp_extendXIso`
is therefore stated and proved for an arbitrary additive functor between arbitrary preadditive
categories, where the obstruction is absent, and
`baseAlternatingCechComplexIsoExtend_hom_f_comp_extendXIso` applies it in term position, where
default transparency is in force. This is the same discipline as the `congrArg` proofs of the
differential identities in `ProperFlatGlobalSections.lean`. For the same reason that abstract
lemma is stated with `HomologicalComplex.extend` and `HomologicalComplex.extendMap` rather than
with `ComplexShape.Embedding.extendFunctor`: the two spellings of the extended complex are not
reducibly equal, so a goal mixing them admits no rewriting either.

**The four-fold composite is never split in the goal.** It is matched, up to definitional
equality, against the left-hand side of
`Stacks.DerivedIndexing.map_f_comp_mapExtendIso_inv_f_comp_extendMap_f_comp`, which is the same
four factors with the four complexes abstract; that is why the application is a single
`Eq.trans` and no tactic ever sees a goal in which
`(((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj K).X p` and
`(ModuleCat.extendScalars φ).obj (K.X p)` both occur. The two identifications of the models that
flank the composite enter the abstract lemma as the data `a` and `b`, and the degree
isomorphism of the target enters as the morphism `y` with the hypothesis
`hy : b.f i' ≫ y = (L.extendXIso e h).hom`, which for the model at hand is exactly
`baseAlternatingCechComplexIsoExtend_hom_f_comp_extendXIso` read through
`CategoryTheory.Iso.inv_comp_eq`.

**Two statements of the same equality.** The `ℕ`-level factor is the comparison carried by
`Stacks.Cech.cechBaseChangeData`, and its component is `Stacks.Cech`'s degreewise
`alternatingCechModuleObjBaseChangeIso` by `rfl`. Rewriting by that identity inside the proof
would exchange a morphism for one whose type is only definitionally the same, so
`baseAlternatingCechComplexBaseChangeIso_hom_f_comp_XIso` is instead *stated* with the
degreewise isomorphism and proved by the preceding theorem unchanged.

**The `ℤ`-indexed models still need `HasDerivedCategory.standard`** at the raised priority of
the two files this builds on: without it the derived categories appearing in the ambient
development do not unify.

## References

* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.DerivedIndexing

/-- **The degreewise component, in a degree in the range of the embedding, of the comparison
used to transport an `ℕ`-indexed morphism of complexes to the `ℤ`-indexed extensions by zero.**
For an additive functor `G`, the comparison `mapExtendIso` followed by the extension by zero
along `e` of a morphism `ψ : (G.mapHomologicalComplex c).obj K ⟶ L` has, in the degree `e.f i`,
the component `ψ.f i`, conjugated by the two identifications `HomologicalComplex.extendXIso` of
the terms of the extensions. -/
lemma mapExtendIso_inv_f_comp_extendMap_f_comp_extendXIso {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] [HasZeroObject C] [HasZeroObject D] (G : C ⥤ D) [G.Additive]
    (e : c.Embedding c') {K : HomologicalComplex C c} {L : HomologicalComplex D c}
    (ψ : (G.mapHomologicalComplex c).obj K ⟶ L) {i : ι} {i' : ι'} (h : e.f i = i') :
    ((mapExtendIso G e K).inv.f i' ≫ (HomologicalComplex.extendMap ψ e).f i') ≫
        (L.extendXIso e h).hom =
      G.map (K.extendXIso e h).hom ≫ ψ.f i := by
  rw [mapExtendIso_inv_f_eq G e K h, HomologicalComplex.extendMap_f ψ e h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The degreewise component of a transport of an `ℕ`-indexed morphism of complexes to the
`ℤ`-indexed extensions by zero, as it actually occurs.** The transport is a four-fold composite:
the termwise image under `G` of an identification `a` of the source with an extension by zero,
the comparison `mapExtendIso`, the extension by zero of the `ℕ`-indexed morphism `ψ`, and an
identification `b` of the extension by zero of the target with the target. Read through a
morphism `y` which identifies the term of `b`'s target with the term of `L` — the hypothesis
`hy` — its component in the degree `e.f i` is the component `ψ.f i`, precomposed with the
termwise image of `a`'s component read through `HomologicalComplex.extendXIso`.

Abstract for the reason given at
`mapExtendIso_inv_f_comp_extendMap_f_comp_extendXIso`: in the application the two spellings
`HomologicalComplex.extend` and `ComplexShape.Embedding.extendFunctor` of an extension by zero
both occur, and are not reducibly equal, so no rewriting can be done on the goal. -/
lemma map_f_comp_mapExtendIso_inv_f_comp_extendMap_f_comp {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] [HasZeroObject C] [HasZeroObject D] (G : C ⥤ D) [G.Additive]
    (e : c.Embedding c') {K : HomologicalComplex C c} {L : HomologicalComplex D c}
    {B : HomologicalComplex C c'} {B' : HomologicalComplex D c'}
    (a : B ⟶ K.extend e) (ψ : (G.mapHomologicalComplex c).obj K ⟶ L) (b : L.extend e ⟶ B')
    {i : ι} {i' : ι'} (h : e.f i = i') (y : B'.X i' ⟶ L.X i)
    (hy : b.f i' ≫ y = (L.extendXIso e h).hom) :
    (((G.mapHomologicalComplex c').map a).f i' ≫ (mapExtendIso G e K).inv.f i' ≫
          (HomologicalComplex.extendMap ψ e).f i' ≫ b.f i') ≫ y =
      G.map (a.f i' ≫ (K.extendXIso e h).hom) ≫ ψ.f i := by
  rw [Functor.mapHomologicalComplex_map_f, G.map_comp, mapExtendIso_inv_f_eq G e K h,
    HomologicalComplex.extendMap_f ψ e h]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc, hy, Iso.inv_hom_id, Category.comp_id]

end Stacks.DerivedIndexing

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

attribute [local instance 10000] HasDerivedCategory.standard

section Model

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  {I : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (F : X.Modules)

/-- **In a nonnegative degree, the identification of the `A`-linear model with the extension by
zero of the `ℕ`-indexed alternating Čech complex is `baseAlternatingCechComplexXIso`.** Read
through Mathlib's comparison `HomologicalComplex.extendXIso` for the degree `(m : ℤ)`, the
complex-level isomorphism `baseAlternatingCechComplexIsoExtend` has the degree isomorphism of
`ProperFlatGlobalSections` for its component.

The `ℕ`-indexed comparison `alternatingCechModuleComplexIso` it is built from is degreewise the
identity, so nothing survives of it; the content is that the comparison of the extension by
zero with the termwise functor contributes nothing either. -/
theorem baseAlternatingCechComplexIsoExtend_hom_f_comp_extendXIso (m : ℕ) :
    (baseAlternatingCechComplexIsoExtend f U hU F).hom.f (m : ℤ) ≫
        ((Stacks.Cech.alternatingCechModuleComplex f U F).extendXIso
          ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f m)).hom =
      (baseAlternatingCechComplexXIso f U hU F m).hom :=
  (Stacks.DerivedIndexing.mapExtendIso_inv_f_comp_extendMap_f_comp_extendXIso
      (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom)
      ComplexShape.embeddingUpNat (alternatingCechModuleComplexIso f U hU F).hom
      (ComplexShape.embeddingUpNat_f m)).trans
    (Category.comp_id _)

/-- **Two morphisms of `ℤ`-indexed complexes into the `A`-linear Čech model which agree in every
nonnegative degree are equal.** The model vanishes in negative degrees, so there is nothing to
check there. The source is an arbitrary complex, so this applies to any composite of the
`ℤ`-indexed base-change isomorphisms. -/
theorem hom_ext_baseAlternatingCechComplex {K : CochainComplex (ModuleCat.{u} A) ℤ}
    (α β : K ⟶ baseAlternatingCechComplex f U hU F)
    (h : ∀ m : ℕ, α.f (m : ℤ) = β.f (m : ℤ)) : α = β := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  by_cases hp : ∃ m : ℕ, (m : ℤ) = p
  · obtain ⟨m, rfl⟩ := hp
    exact h m
  · refine (isZero_baseAlternatingCechComplex_X_of_neg f U hU F p ?_).eq_of_tgt _ _
    by_contra hcon
    exact hp ⟨p.toNat, Int.toNat_of_nonneg (not_lt.mp hcon)⟩

end Model

section BaseChange

/-- **The inverse-image family is the inverse-image family reindexed by the identity.** This is
the hypothesis `U' i = g ⁻¹ᵁ U (e i)` of `Stacks.Cech.cechBaseChangeData` for `U' = g ⁻¹ᵁ U` and
`e = Equiv.refl`. It holds by `rfl`, and is stated as a theorem because the term `rfl` does not
have this type syntactically; see the implementation notes. -/
theorem preimage_eq_preimage_equivRefl {X X' : Scheme.{u}} (g : X' ⟶ X) {I : Type u}
    (U : I → X.Opens) (i : I) :
    g ⁻¹ᵁ U i = g ⁻¹ᵁ U ((Equiv.refl I) i) :=
  rfl

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  {X X' : Scheme.{u}} {f : X ⟶ Spec (.of A)} [IsSeparated f] {f' : X' ⟶ Spec (.of A')}
  {g : X' ⟶ X} (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
  (F : X.Modules) [F.IsQuasicoherent] {I : Type u} [Finite I]
  (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))

/-- **In a nonnegative degree the `ℤ`-indexed Čech base-change isomorphism is the `ℕ`-indexed
comparison carried by `Stacks.Cech.cechBaseChangeData`.** For every `m : ℕ`, the component of
`baseAlternatingCechComplexBaseChangeIso` in degree `(m : ℤ)`, followed by the degree
isomorphism of the target model, is the extension of scalars along `φ` of the degree isomorphism
of the source model, followed by the degree-`m` component of the `ℕ`-indexed comparison.

This is the whole content of the four-fold composite in a single degree: the two
`baseAlternatingCechComplexIsoExtend` factors contribute the two degree isomorphisms, and the
comparisons `HomologicalComplex.extendXIso` that the two middle factors introduce cancel. -/
theorem baseAlternatingCechComplexBaseChangeIso_hom_f_comp_alternatingIso (m : ℕ) :
    (baseAlternatingCechComplexBaseChangeIso φ hsq F U hU hUaff).hom.f (m : ℤ) ≫
        (baseAlternatingCechComplexXIso f' (fun i => g ⁻¹ᵁ U i) (top_eq_iSup_preimage g U hU)
          ((Scheme.Modules.pullback g).obj F) m).hom =
      (ModuleCat.extendScalars.{u, u, u} φ).map
          (baseAlternatingCechComplexXIso f U hU F m).hom ≫
        (Stacks.Cech.cechBaseChangeData φ f f' g hsq F U hUaff (fun i => g ⁻¹ᵁ U i)
          (Equiv.refl I) (preimage_eq_preimage_equivRefl g U)).alternatingIso.hom.f m := by
  have hA := baseAlternatingCechComplexIsoExtend_hom_f_comp_extendXIso f U hU F m
  have hA' := baseAlternatingCechComplexIsoExtend_hom_f_comp_extendXIso f'
    (fun i => g ⁻¹ᵁ U i) (top_eq_iSup_preimage g U hU) ((Scheme.Modules.pullback g).obj F) m
  have key : (baseAlternatingCechComplexIsoExtend f' (fun i => g ⁻¹ᵁ U i)
          (top_eq_iSup_preimage g U hU) ((Scheme.Modules.pullback g).obj F)).inv.f (m : ℤ) ≫
        (baseAlternatingCechComplexXIso f' (fun i => g ⁻¹ᵁ U i) (top_eq_iSup_preimage g U hU)
          ((Scheme.Modules.pullback g).obj F) m).hom =
      ((Stacks.Cech.alternatingCechModuleComplex f' (fun i => g ⁻¹ᵁ U i)
        ((Scheme.Modules.pullback g).obj F)).extendXIso ComplexShape.embeddingUpNat
          (ComplexShape.embeddingUpNat_f m)).hom :=
    (Iso.inv_comp_eq (HomologicalComplex.Hom.isoApp
      (baseAlternatingCechComplexIsoExtend f' (fun i => g ⁻¹ᵁ U i)
        (top_eq_iSup_preimage g U hU) ((Scheme.Modules.pullback g).obj F)) (m : ℤ))).2 hA'.symm
  refine Eq.trans (Stacks.DerivedIndexing.map_f_comp_mapExtendIso_inv_f_comp_extendMap_f_comp
      (ModuleCat.extendScalars.{u, u, u} φ) ComplexShape.embeddingUpNat
      (baseAlternatingCechComplexIsoExtend f U hU F).hom
      (Stacks.Cech.cechBaseChangeData φ f f' g hsq F U hUaff (fun i => g ⁻¹ᵁ U i)
        (Equiv.refl I) (preimage_eq_preimage_equivRefl g U)).alternatingIso.hom
      (baseAlternatingCechComplexIsoExtend f' (fun i => g ⁻¹ᵁ U i)
        (top_eq_iSup_preimage g U hU) ((Scheme.Modules.pullback g).obj F)).inv
      (ComplexShape.embeddingUpNat_f m)
      (baseAlternatingCechComplexXIso f' (fun i => g ⁻¹ᵁ U i) (top_eq_iSup_preimage g U hU)
        ((Scheme.Modules.pullback g).obj F) m).hom key) ?_
  exact congrArg (fun t => (ModuleCat.extendScalars.{u, u, u} φ).map t ≫
    (Stacks.Cech.cechBaseChangeData φ f f' g hsq F U hUaff (fun i => g ⁻¹ᵁ U i)
      (Equiv.refl I) (preimage_eq_preimage_equivRefl g U)).alternatingIso.hom.f m) hA

/-- **In a nonnegative degree the `ℤ`-indexed Čech base-change isomorphism is the `ℕ`-indexed
degreewise comparison `Stacks.Cech.alternatingCechModuleObjBaseChangeIso`.** This is
`baseAlternatingCechComplexBaseChangeIso_hom_f_comp_alternatingIso` with the component of the
`ℕ`-indexed comparison written out; the two statements are definitionally the same. -/
theorem baseAlternatingCechComplexBaseChangeIso_hom_f_comp_XIso (m : ℕ) :
    (baseAlternatingCechComplexBaseChangeIso φ hsq F U hU hUaff).hom.f (m : ℤ) ≫
        (baseAlternatingCechComplexXIso f' (fun i => g ⁻¹ᵁ U i) (top_eq_iSup_preimage g U hU)
          ((Scheme.Modules.pullback g).obj F) m).hom =
      (ModuleCat.extendScalars.{u, u, u} φ).map
          (baseAlternatingCechComplexXIso f U hU F m).hom ≫
        (Stacks.Cech.alternatingCechModuleObjBaseChangeIso g U (fun i => g ⁻¹ᵁ U i)
          (Equiv.refl I) F (preimage_eq_preimage_equivRefl g U) φ f f'
          (fun W => Stacks.Cech.baseRingHom_comp_app φ f f' g hsq W) hsq hUaff m).hom :=
  baseAlternatingCechComplexBaseChangeIso_hom_f_comp_alternatingIso φ hsq F U hU hUaff m

/-- **The closed form of the component of `baseAlternatingCechComplexBaseChangeIso` in a
nonnegative degree**: the `ℕ`-level degreewise comparison, conjugated by the two degree
isomorphisms of the models. -/
theorem baseAlternatingCechComplexBaseChangeIso_hom_f (m : ℕ) :
    (baseAlternatingCechComplexBaseChangeIso φ hsq F U hU hUaff).hom.f (m : ℤ) =
      ((ModuleCat.extendScalars.{u, u, u} φ).map
            (baseAlternatingCechComplexXIso f U hU F m).hom ≫
          (Stacks.Cech.alternatingCechModuleObjBaseChangeIso g U (fun i => g ⁻¹ᵁ U i)
            (Equiv.refl I) F (preimage_eq_preimage_equivRefl g U) φ f f'
            (fun W => Stacks.Cech.baseRingHom_comp_app φ f f' g hsq W) hsq hUaff m).hom) ≫
        (baseAlternatingCechComplexXIso f' (fun i => g ⁻¹ᵁ U i) (top_eq_iSup_preimage g U hU)
          ((Scheme.Modules.pullback g).obj F) m).inv :=
  (Iso.eq_comp_inv _).2
    (baseAlternatingCechComplexBaseChangeIso_hom_f_comp_XIso φ hsq F U hU hUaff m)

end BaseChange

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end
