module

public import Mathlib.CategoryTheory.Localization.Adjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPushforwardComposition
public import StacksFrontier.CategoryTheory.Functor.Derived.DerivableOfInverts

/-!
# The derived pushforward and the derived pullback of an exact pair

Let `f` be a morphism of ringed sites, presented by a continuous functor `u : C' ⥤ C` in the
direction opposite to `f` together with the structure map `σ : R' ⟶ f_*R`, let `A` be a sheaf of
differential graded `R`-algebras on the source, `B` one of differential graded `R'`-algebras on
the target, and `φ : B ⟶ f_*A` a homomorphism. Suppose that the direct image and a pullback of
right differential graded modules both carry quasi-isomorphisms to quasi-isomorphisms. Then
neither functor needs resolving: `K(f_*)` and `K(f^*)` invert the quasi-isomorphisms of the
homotopy categories after localization, so each factors through the derived category, and the
factorisation *is* the derived extension in the sense of
[Stacks, Tag 05S9](https://stacks.math.columbia.edu/tag/05S9) — the ind-object, resp.
pro-object, computing the derived value is constant.

This file carries that out. It produces `Rf_*`, `Lf^*`, their comparison maps `β` and `α`, a
term of `SheafOfModules.DifferentialGradedModule.DerivedPushPullData`, and the adjunction
`Lf^* ⊣ Rf_*` of [Stacks, Tag 0FTR](https://stacks.math.columbia.edu/tag/0FTR) — the last
*without* the calculus-of-fractions hypotheses that
`exists_adjunction_derivedPullback_derivedPushforward_of_hasCalculusOfFractions` needs over an
arbitrary site, because for an exact pair the adjunction is the localization of the adjunction
`K(f^*) ⊣ K(f_*)` rather than a comparison of derived extensions.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.derivedPushforwardOfInverts` is `Rf_*`, the functor
  induced on the derived categories by `K(f_*)`, and
  `SheafOfModules.DifferentialGradedModule.pushforwardComparisonIsoOfInverts` is its comparison
  map `β : K(f_*) ⋙ Q' ≅ Q ⋙ Rf_*`, which here is an isomorphism.
* `SheafOfModules.DifferentialGradedModule.derivedPullbackOfInverts` is `Lf^*` and
  `SheafOfModules.DifferentialGradedModule.pullbackComparisonIsoOfInverts` is its comparison map
  `α : Q' ⋙ Lf^* ≅ K(f^*) ⋙ Q`.
* `SheafOfModules.DifferentialGradedModule.derivedPushPullDataOfInverts` is the resulting
  `DerivedPushPullData`.
* `SheafOfModules.DifferentialGradedModule.adjunctionOfInverts` is `Lf^* ⊣ Rf_*`.
* `SheafOfModules.DifferentialGradedModule.derivedPushforwardIsoOfInverts` identifies `Rf_*`
  with *any* carried derived pushforward: for an exact pair the constructed functor is, up to
  isomorphism, the only right derived extension of `K(f_*)`.

## Main results

* `SheafOfModules.DifferentialGradedModule.isInvertedBy_homotopyPushforwardFunctor_comp` and
  `...isInvertedBy_homotopyPullbackFunctor_comp`: the two hypotheses of the construction, read
  off the module-level statement that the functor carries quasi-isomorphisms of the underlying
  complexes of sheaves of modules to quasi-isomorphisms.
* `...isInvertedBy_homotopyPushforwardFunctor_comp_of_preservesHomology`, in the same namespace:
  the first hypothesis holds as soon as the direct image of sheaves of modules preserves
  homology.
* `SheafOfModules.DifferentialGradedModule.quasiIso_pushforwardFunctor_map`: the direct image of
  differential graded modules carries quasi-isomorphisms to quasi-isomorphisms as soon as the
  direct image of sheaves of modules preserves homology, since the underlying complex of `f_*M`
  is the degreewise direct image of the underlying complex of `M`.
* `SheafOfModules.DifferentialGradedModule.lifting_derivedPushforwardOfInverts` and
  `...lifting_derivedPullbackOfInverts`: each of the two functors lifts the corresponding
  homotopy-category functor through the localization, which is what pins it down up to
  isomorphism.
* `SheafOfModules.DifferentialGradedModule.derivedPushforwardOfInverts_obj_iso` and
  `...derivedPullbackOfInverts_obj_iso`: the computation. On the image of a differential graded
  module, `Rf_*`, resp. `Lf^*`, is the direct image, resp. the pullback, of that module.
* `SheafOfModules.DifferentialGradedModule.isIso_pushforwardComparison`: for an exact pair the
  comparison map `β` of a carried derived pushforward is an isomorphism, so that carried functor
  also lifts `K(f_*)` through the localization.

## Implementation notes

**What is assumed and what is constructed.** The two hypotheses are that
`K(f_*) ⋙ Q'` and `K(f^*) ⋙ Q` invert the quasi-isomorphisms; they are conditions on the
morphism and the pullback datum, not stand-ins for the conclusion, and
`quasiIso_pushforwardFunctor_map` discharges the first one from exactness of the direct image of
sheaves of modules. Everything else — the two functors, the two comparison maps, the two
derived-value conditions of Stacks 05S9 and the adjunction — is constructed.

**Why the derived-value conditions hold.** The index category `K/Qis` of the ind-object has the
identity of `K` as an *initial* object, and all the transition maps of the ind-object are
invertible, so the ind-object is constant; this is
`CategoryTheory.Functor.valueCoconeOfInverts` of
`StacksFrontier/CategoryTheory/Functor/Derived/DerivableOfInverts.lean`, and
`CategoryTheory.Functor.exists_isRightDerivedValueAt_of_isInvertedBy` packages it, together with
the identification of the value with `Rf_*(Q K)` through `β`, in exactly the shape the fields of
`DerivedPushPullData` ask for. The pullback side is the dual.

**The adjunction needs no calculus of fractions.** `CategoryTheory.Adjunction.localization`
descends an adjunction to the localizations as soon as both functors factor through them, which
here they do by construction; the two `CategoryTheory.CatCommSq` instances it asks for are the
two comparison isomorphisms. By contrast
`exists_adjunction_derivedPullback_derivedPushforward_of_hasCalculusOfFractions` works with
derived extensions which are only pinned pointwise, and for that it needs the two Ore
conditions.

**The pullback is still carried, the direct image is not.** As in
`DifferentialGradedPushforward.lean`, `f^*` is the datum `PullbackData` together with its
differential graded extension `PullbackData.HomotopyExtension`, because
`f^*M = f⁻¹M ⊗_{f⁻¹B} A` cannot be written down in this development; `f_*` is the constructed
`pushforwardFunctor`.

## References

* [Stacks Project, Tag 0FTR](https://stacks.math.columbia.edu/tag/0FTR)
* [Stacks Project, Tag 0FTP](https://stacks.math.columbia.edu/tag/0FTP)
* [Stacks Project, Tag 0FTG](https://stacks.math.columbia.edu/tag/0FTG)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
* [Stacks Project, Tag 05S9](https://stacks.math.columbia.edu/tag/05S9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a a' m v u v' u'

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J' AddCommGrpCat.{m}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m}]
  {u : C' ⥤ C} [u.IsContinuous J' J] {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {A : DifferentialGradedAlgebra.{t, a} R} {B : DifferentialGradedAlgebra.{t, a'} R'}
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ B A}

/-! ### The two hypotheses -/

/-- If the direct image of right differential graded modules carries quasi-isomorphisms of the
underlying complexes of sheaves of modules to quasi-isomorphisms, then `K(f_*)` followed by the
localization inverts the quasi-isomorphisms of the homotopy category. -/
theorem isInvertedBy_homotopyPushforwardFunctor_comp
    (hφ : ∀ {M N : DifferentialGradedModule.{t, a, m} A} (g : M ⟶ N),
      QuasiIso g.toHomologicalComplex →
        QuasiIso ((pushforwardFunctor.{t, a, m} φ).map g).toHomologicalComplex) :
    (quasiIsomorphisms.{t, a, m} A).IsInvertedBy
      (homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{t, a', m} B) := by
  intro K L ψ hψ
  have hc := (HomotopyCategory.quotient A).map_preimage (X := K.as) (Y := L.as) ψ
  have hiso : IsIso ((toDerivedCategory.{t, a', m} B).map
      ((HomotopyCategory.quotient B).map ((pushforwardFunctor.{t, a, m} φ).map
        ((HomotopyCategory.quotient A).preimage ψ)))) :=
    Localization.inverts (toDerivedCategory.{t, a', m} B) (quasiIsomorphisms.{t, a', m} B) _
      ((quasiIsomorphisms_quotient_map_iff _).2 (hφ _ (hψ _ hc)))
  dsimp only [Functor.comp_map]
  rw [← hc]
  exact hiso

omit [u.IsContinuous J' J] in
/-- If a pullback of right differential graded modules carries quasi-isomorphisms of the
underlying complexes of sheaves of modules to quasi-isomorphisms, then `K(f^*)` followed by the
localization inverts the quasi-isomorphisms of the homotopy category. -/
theorem isInvertedBy_homotopyPullbackFunctor_comp (P : PullbackData φ) (E : P.HomotopyExtension)
    (hP : ∀ {M N : DifferentialGradedModule.{t, a', m} B} (g : M ⟶ N),
      QuasiIso g.toHomologicalComplex → QuasiIso (P.map g).toHomologicalComplex) :
    (quasiIsomorphisms.{t, a', m} B).IsInvertedBy
      (homotopyPullbackFunctor P E ⋙ toDerivedCategory.{t, a, m} A) := by
  intro K L ψ hψ
  have hc := (HomotopyCategory.quotient B).map_preimage (X := K.as) (Y := L.as) ψ
  have hiso : IsIso ((toDerivedCategory.{t, a, m} A).map
      ((HomotopyCategory.quotient A).map
        (P.functor.map ((HomotopyCategory.quotient B).preimage ψ)))) :=
    Localization.inverts (toDerivedCategory.{t, a, m} A) (quasiIsomorphisms.{t, a, m} A) _
      ((quasiIsomorphisms_quotient_map_iff _).2 (hP _ (hψ _ hc)))
  dsimp only [Functor.comp_map]
  rw [← hc]
  exact hiso

/-- The direct image of right differential graded modules carries quasi-isomorphisms to
quasi-isomorphisms as soon as the direct image of sheaves of modules preserves homology: the
underlying complex of `f_*M` is the degreewise direct image of the underlying complex of `M`,
and the direct image of a morphism is its degreewise direct image. -/
theorem quasiIso_pushforwardFunctor_map
    (hex : (sitePushforward u σ :
      SheafOfModules.{m} R ⥤ SheafOfModules.{m} R').PreservesHomology)
    {M N : DifferentialGradedModule.{t, a, m} A} (g : M ⟶ N)
    (hg : QuasiIso g.toHomologicalComplex) :
    QuasiIso ((pushforwardFunctor.{t, a, m} φ).map g).toHomologicalComplex :=
  inferInstanceAs (QuasiIso (((sitePushforward u σ :
    SheafOfModules.{m} R ⥤ SheafOfModules.{m} R').mapHomologicalComplex
      (ComplexShape.up ℤ)).map g.toHomologicalComplex))

/-- **The first hypothesis, read off exactness of the direct image of sheaves of modules.** If
the direct image of sheaves of modules along `f` preserves homology then `K(f_*)` followed by the
localization inverts the quasi-isomorphisms, by `quasiIso_pushforwardFunctor_map`. -/
theorem isInvertedBy_homotopyPushforwardFunctor_comp_of_preservesHomology
    (hex : (sitePushforward u σ :
      SheafOfModules.{m} R ⥤ SheafOfModules.{m} R').PreservesHomology) :
    (quasiIsomorphisms.{t, a, m} A).IsInvertedBy
      (homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{t, a', m} B) :=
  isInvertedBy_homotopyPushforwardFunctor_comp (quasiIso_pushforwardFunctor_map hex)

/-! ### The two functors and their comparison maps -/

section Construction

variable (hpush : (quasiIsomorphisms.{t, a, m} A).IsInvertedBy
  (homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{t, a', m} B))

/-- **The derived pushforward of an exact pair**: the functor `Rf_* : D(A, d) ⥤ D(B, d)` induced
on the derived categories by `K(f_*)`, which needs no resolving because it already inverts the
quasi-isomorphisms. -/
noncomputable def derivedPushforwardOfInverts :
    derivedCategory.{t, a, m} A ⥤ derivedCategory.{t, a', m} B :=
  Localization.lift _ hpush (toDerivedCategory.{t, a, m} A)

/-- The comparison map `β : K(f_*) ⋙ Q' ⟶ Q ⋙ Rf_*` of the derived pushforward of an exact
pair, which here is an isomorphism: `Rf_*` computes the direct image on the nose. -/
noncomputable def pushforwardComparisonIsoOfInverts :
    homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{t, a', m} B ≅
      toDerivedCategory.{t, a, m} A ⋙ derivedPushforwardOfInverts hpush :=
  (Localization.fac _ hpush (toDerivedCategory.{t, a, m} A)).symm

/-- `Rf_*` lifts `K(f_*)` followed by the localization, by the comparison isomorphism. This is
what identifies it, up to isomorphism, among the functors out of the derived category. -/
noncomputable instance lifting_derivedPushforwardOfInverts :
    Localization.Lifting (toDerivedCategory.{t, a, m} A) (quasiIsomorphisms.{t, a, m} A)
      (homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{t, a', m} B)
      (derivedPushforwardOfInverts hpush) :=
  ⟨(pushforwardComparisonIsoOfInverts hpush).symm⟩

/-- **The computation of the derived pushforward**: on the image in the derived category of a
right differential graded `A`-module `M`, the derived pushforward of an exact pair is the image
of the direct image `f_*M`. -/
noncomputable def derivedPushforwardOfInverts_obj_iso (M : DifferentialGradedModule.{t, a, m} A) :
    (derivedPushforwardOfInverts hpush).obj ((toDerivedCategory.{t, a, m} A).obj
        ((HomotopyCategory.quotient A).obj M)) ≅
      (toDerivedCategory.{t, a', m} B).obj ((HomotopyCategory.quotient B).obj
        ((pushforwardFunctor.{t, a, m} φ).obj M)) :=
  ((pushforwardComparisonIsoOfInverts hpush).app ((HomotopyCategory.quotient A).obj M)).symm

include hpush in
/-- **For an exact pair the comparison map of a carried derived pushforward is an
isomorphism.** Let `Rf_*` be any functor carrying the derived-value condition of
[Stacks, Tag 05S9](https://stacks.math.columbia.edu/tag/05S9) for `K(f_*)`, with comparison map
`β : K(f_*) ⋙ Q' ⟶ Q ⋙ Rf_*`. If `K(f_*)` followed by the localization inverts the
quasi-isomorphisms then `β` is invertible. Indeed at an object `K` the condition writes
`β` at the index `𝟙 K` as the coprojection of the value cocone there, followed by the
identification of the value with `Rf_*(QK)` and by `Rf_*` of an invertible morphism; and the
coprojections of a value of a right derived functor of a functor inverting the class are
themselves invertible. -/
theorem isIso_pushforwardComparison {P : PullbackData φ} {E : P.HomotopyExtension}
    (D : DerivedPushPullData P E) : IsIso D.pushforwardComparison := by
  have := quasiIsomorphisms_isMultiplicative.{t, a, m} A
  have happ : ∀ K : HomotopyCategory.{t, a, m} A, IsIso (D.pushforwardComparison.app K) := by
    intro K
    obtain ⟨c, hc, ε, hcompat⟩ := D.isRightDerived K
    let s₀ : (quasiIsomorphisms.{t, a, m} A).Under ⊤ K :=
      MorphismProperty.Under.mk ⊤ (𝟙 K) (MorphismProperty.id_mem _ K)
    have : IsIso ((toDerivedCategory.{t, a, m} A).map s₀.hom) :=
      Localization.inverts (toDerivedCategory.{t, a, m} A) (quasiIsomorphisms.{t, a, m} A) _
        s₀.prop
    change IsIso (D.pushforwardComparison.app s₀.right)
    rw [← hcompat s₀]
    exact IsIso.comp_isIso' (hc.isIso_ι_app hpush s₀) (IsIso.comp_isIso' ε.isIso_hom inferInstance)
  exact NatIso.isIso_of_isIso_app _

/-- **For an exact pair every carried derived pushforward is the constructed one.** Both lift
`K(f_*)` followed by the localization — the carried one because its comparison map is an
isomorphism — and a functor out of a localization is determined up to isomorphism by what it
lifts. -/
noncomputable def derivedPushforwardIsoOfInverts {P : PullbackData φ} {E : P.HomotopyExtension}
    (D : DerivedPushPullData P E) :
    derivedPushforwardOfInverts hpush ≅ D.derivedPushforward := by
  haveI := isIso_pushforwardComparison hpush D
  letI : Localization.Lifting (toDerivedCategory.{t, a, m} A) (quasiIsomorphisms.{t, a, m} A)
      (homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{t, a', m} B)
      D.derivedPushforward :=
    ⟨(asIso D.pushforwardComparison).symm⟩
  exact Localization.liftNatIso (toDerivedCategory.{t, a, m} A) (quasiIsomorphisms.{t, a, m} A)
    (homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{t, a', m} B)
    (homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{t, a', m} B)
    (derivedPushforwardOfInverts hpush) D.derivedPushforward (Iso.refl _)

variable {P : PullbackData φ} {E : P.HomotopyExtension}
  (hpull : (quasiIsomorphisms.{t, a', m} B).IsInvertedBy
    (homotopyPullbackFunctor P E ⋙ toDerivedCategory.{t, a, m} A))

/-- **The derived pullback of an exact pair**: the functor `Lf^* : D(B, d) ⥤ D(A, d)` induced on
the derived categories by `K(f^*)`, which needs no resolving because it already inverts the
quasi-isomorphisms. -/
noncomputable def derivedPullbackOfInverts :
    derivedCategory.{t, a', m} B ⥤ derivedCategory.{t, a, m} A :=
  Localization.lift _ hpull (toDerivedCategory.{t, a', m} B)

/-- The comparison map `α : Q' ⋙ Lf^* ⟶ K(f^*) ⋙ Q` of the derived pullback of an exact pair,
which here is an isomorphism: `Lf^*` computes the pullback on the nose. -/
noncomputable def pullbackComparisonIsoOfInverts :
    toDerivedCategory.{t, a', m} B ⋙ derivedPullbackOfInverts hpull ≅
      homotopyPullbackFunctor P E ⋙ toDerivedCategory.{t, a, m} A :=
  Localization.fac _ hpull (toDerivedCategory.{t, a', m} B)

/-- `Lf^*` lifts `K(f^*)` followed by the localization, by the comparison isomorphism. This is
what identifies it, up to isomorphism, among the functors out of the derived category. -/
noncomputable instance lifting_derivedPullbackOfInverts :
    Localization.Lifting (toDerivedCategory.{t, a', m} B) (quasiIsomorphisms.{t, a', m} B)
      (homotopyPullbackFunctor P E ⋙ toDerivedCategory.{t, a, m} A)
      (derivedPullbackOfInverts hpull) :=
  ⟨pullbackComparisonIsoOfInverts hpull⟩

/-- **The computation of the derived pullback**: on the image in the derived category of a right
differential graded `B`-module `M`, the derived pullback of an exact pair is the image of the
pullback `f^*M`. -/
noncomputable def derivedPullbackOfInverts_obj_iso (M : DifferentialGradedModule.{t, a', m} B) :
    (derivedPullbackOfInverts hpull).obj ((toDerivedCategory.{t, a', m} B).obj
        ((HomotopyCategory.quotient B).obj M)) ≅
      (toDerivedCategory.{t, a, m} A).obj ((HomotopyCategory.quotient A).obj (P.obj M)) :=
  (pullbackComparisonIsoOfInverts hpull).app ((HomotopyCategory.quotient B).obj M)

/-- **The content of `DerivedPushPullData` for an exact pair**: the derived pushforward and the
derived pullback, with their comparison maps and with the derived-value conditions of
[Stacks, Tag 05S9](https://stacks.math.columbia.edu/tag/05S9). Both ind-objects are constant, so
the conditions hold with the identity as index and as retraction. -/
noncomputable def derivedPushPullDataOfInverts : DerivedPushPullData P E where
  derivedPushforward := derivedPushforwardOfInverts hpush
  pushforwardComparison := (pushforwardComparisonIsoOfInverts hpush).hom
  derivedPullback := derivedPullbackOfInverts hpull
  pullbackComparison := (pullbackComparisonIsoOfInverts hpull).hom
  isRightDerived K := by
    have := quasiIsomorphisms_isMultiplicative.{t, a, m} A
    exact Functor.exists_isRightDerivedValueAt_of_isInvertedBy hpush _ _
      (pushforwardComparisonIsoOfInverts hpush) K
  isLeftDerived M := by
    have := quasiIsomorphisms_isMultiplicative.{t, a', m} B
    exact Functor.exists_isLeftDerivedValueAt_of_isInvertedBy hpull _ _
      (pullbackComparisonIsoOfInverts hpull) M

/-- The derived pushforward of `derivedPushPullDataOfInverts` is `derivedPushforwardOfInverts`. -/
@[simp]
theorem derivedPushPullDataOfInverts_derivedPushforward :
    (derivedPushPullDataOfInverts hpush hpull).derivedPushforward =
      derivedPushforwardOfInverts hpush :=
  rfl

/-- The derived pullback of `derivedPushPullDataOfInverts` is `derivedPullbackOfInverts`. -/
@[simp]
theorem derivedPushPullDataOfInverts_derivedPullback :
    (derivedPushPullDataOfInverts hpush hpull).derivedPullback =
      derivedPullbackOfInverts hpull :=
  rfl

/-- **Stacks 0FTR for an exact pair**: the derived pullback is left adjoint to the derived
pushforward. For an exact pair this is the localization of the adjunction `K(f^*) ⊣ K(f_*)` of
homotopy categories, so — unlike
`exists_adjunction_derivedPullback_derivedPushforward_of_hasCalculusOfFractions`, which compares
two derived extensions pinned only pointwise — it needs no calculus of fractions, and the
adjunction is produced rather than merely asserted to exist. -/
noncomputable def adjunctionOfInverts :
    derivedPullbackOfInverts hpull ⊣ derivedPushforwardOfInverts hpush := by
  letI : CatCommSq (homotopyPullbackFunctor P E) (toDerivedCategory.{t, a', m} B)
      (toDerivedCategory.{t, a, m} A) (derivedPullbackOfInverts hpull) :=
    ⟨(pullbackComparisonIsoOfInverts hpull).symm⟩
  letI : CatCommSq (homotopyPushforwardFunctor φ) (toDerivedCategory.{t, a, m} A)
      (toDerivedCategory.{t, a', m} B) (derivedPushforwardOfInverts hpush) :=
    ⟨pushforwardComparisonIsoOfInverts hpush⟩
  exact (homotopyPullbackPushforwardAdjunction P E).localization
    (toDerivedCategory.{t, a', m} B) (quasiIsomorphisms.{t, a', m} B)
    (toDerivedCategory.{t, a, m} A) (quasiIsomorphisms.{t, a, m} A) _ _

end Construction

end DifferentialGradedModule

end SheafOfModules

end
