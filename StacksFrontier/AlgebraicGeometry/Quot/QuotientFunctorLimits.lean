module

public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorPullback

/-!
# Limit preservation of the functor of finitely presented quotients, from descent

Let `f : X ⟶ Y` and `F` be the data of an `AlgebraicGeometry.Space.QuotientSituation` with `f`
quasi-compact and quasi-separated and `F` of finite presentation. This file shows that the
functor `Q^{fp}_{F/X/Y}` of finitely presented quotients is *limit preserving* as soon as
finitely presented flat quotients, their isomorphisms and homomorphisms of finitely presented
modules descend along directed limits `T = lim T_i` of affine test schemes over `Y`: the
comparison

`colim Q^{fp}_{F/X/Y}(T_i) ⟶ Q^{fp}_{F/X/Y}(T)`

is then a bijection. This is the predicate `AlgebraicGeometry.LimitPreserving` for the functor
`AlgebraicGeometry.Space.QuotientSituation.finitePresentationQuotientsFunctor`.

The three descent statements are the predicates below, stated for modules on the base changes
`X_{T_i}` and homomorphisms between them, and they are hypotheses of the main result. Without
them the conclusion fails in general: Stacks 082Q as written (no finiteness on `f`) is false,
see `not_forall_finitePresentationQuotientsFunctor_limitPreserving`. Stacks 082Q, corrected by
also asking `f` to be locally of finite presentation, is
`finitePresentationQuotientsFunctor_limitPreserving_of_isLocallyOfFinitePresentation`. Both are in
the namespace `AlgebraicGeometry.Space.QuotientSituation`.

## Main definitions

* `AlgebraicGeometry.Space.QuotientSituation.testScheme`: the underlying-scheme functor on the
  test schemes over `Y`, relative to which limit preservation is read.
* `AlgebraicGeometry.Space.PullbackPreservesFinitePresentationEverywhere`: the inverse image of
  a module of finite presentation along any morphism of algebraic spaces is of finite
  presentation.
* `AlgebraicGeometry.Space.QuotientSituation.FlatQuotientsDescendToStage`: a finitely presented
  quotient of `F_T`, flat over `T`, is the pullback of a finitely presented quotient of `F_{T_i}`
  flat over `T_i` at some stage.
* `AlgebraicGeometry.Space.QuotientSituation.FlatQuotientIsosDescendToStage`: an isomorphism
  between the pullbacks to `T` of two finitely presented quotients at a stage comes from an
  isomorphism at a later stage, compatible with the projections after pullback to `T`.
* `AlgebraicGeometry.Space.QuotientSituation.EventualModuleMapEqOverBaseChangeSystem`: two
  morphisms of finitely presented modules at a stage whose inverse images to the limit agree have
  equal inverse images at a later stage.

## Main results

* `CategoryTheory.Abelian.exists_iso_of_kernelSubobject_eq`: two epimorphisms out of one object
  with the same kernel subobject differ by an isomorphism of their targets commuting with them.
* `CategoryTheory.Functor.conjSubobject_conjSubobject_eq_of_iso_comp`: two conjugate quotients
  agree after a further conjugation as soon as an isomorphism intertwines their projections
  after the further inverse image.
* `AlgebraicGeometry.Space.QuotientSituation.finitePresentationQuotientsFunctor_limitPreserving`:
  the functor `Q^{fp}_{F/X/Y}` is limit preserving, given the three descent statements.

## Implementation notes

A quotient of `F_T` is recorded by its kernel, a subobject of `F_T`, while the descent hypotheses
speak of epimorphisms out of `F_T`. The translation in both directions is
`CategoryTheory.Abelian.exists_iso_of_kernelSubobject_eq` together with
`CategoryTheory.Limits.kernelSubobject_eq_of_comp_mono`. Joint surjectivity and eventual equality
are assembled into a colimit cocone by `CategoryTheory.Limits.Types.FilteredColimit.isColimitOf'`.

The pullback of `F_{T_i}` along `X_T ⟶ X_{T_i}` is identified with `F_T` by
`AlgebraicGeometry.Space.QuotientSituation.baseChangeComparison`, so every statement about a
homomorphism out of `F_T` obtained from one out of `F_{T_i}` carries that comparison.

The isomorphism given by `FlatQuotientIsosDescendToStage` intertwines the two projections only
after inverse image to `X_T`; `EventualModuleMapEqOverBaseChangeSystem` then makes them agree at a
further stage, through `CategoryTheory.Functor.conjSubobject_conjSubobject_eq_of_iso_comp`.

## References

* [Stacks Project, Tag 082Q](https://stacks.math.columbia.edu/tag/082Q)
* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 0CZL](https://stacks.math.columbia.edu/tag/0CZL)
* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 05LI](https://stacks.math.columbia.edu/tag/05LI)
* [Stacks Project, Tag 02JO](https://stacks.math.columbia.edu/tag/02JO)
* [Stacks Project, Tag 07SH](https://stacks.math.columbia.edu/tag/07SH)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w w'

namespace CategoryTheory.Abelian

variable {C : Type*} [Category* C] [Abelian C]

/-- An epimorphism `p` is the projection onto the cokernel of its kernel subobject followed by
`cokernelKernelSubobjectIso p`. -/
theorem cokernel_π_kernelSubobject_comp {A X : C} (p : A ⟶ X) [Epi p] :
    cokernel.π (kernelSubobject p).arrow ≫ (cokernelKernelSubobjectIso p).hom = p := by
  rw [← cokernelKernelSubobjectIso_inv_comp p, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- An epimorphism is the projection onto the quotient by its kernel subobject, for any
presentation of that kernel subobject. -/
private theorem exists_iso_cokernel_of_kernelSubobject_eq {A X : C} (W : Subobject A) (p : A ⟶ X)
    [Epi p] (hp : kernelSubobject p = W) :
    ∃ e : cokernel W.arrow ≅ X, cokernel.π W.arrow ≫ e.hom = p := by
  subst hp
  exact ⟨cokernelKernelSubobjectIso p, cokernel_π_kernelSubobject_comp p⟩

/-- Two epimorphisms out of the same object with the same kernel subobject differ by an
isomorphism of their targets carrying one to the other. -/
theorem exists_iso_of_kernelSubobject_eq {A X Y : C} (p : A ⟶ X) (p' : A ⟶ Y) [Epi p] [Epi p']
    (h : kernelSubobject p = kernelSubobject p') : ∃ e : X ≅ Y, p ≫ e.hom = p' := by
  obtain ⟨e₁, he₁⟩ := exists_iso_cokernel_of_kernelSubobject_eq (kernelSubobject p) p rfl
  obtain ⟨e₂, he₂⟩ := exists_iso_cokernel_of_kernelSubobject_eq (kernelSubobject p) p' h.symm
  have h₁ : p ≫ e₁.inv = cokernel.π (kernelSubobject p).arrow :=
    (Iso.comp_inv_eq e₁).mpr he₁.symm
  refine ⟨e₁.symm ≪≫ e₂, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, h₁, he₂]

end CategoryTheory.Abelian

namespace CategoryTheory.Functor

variable {C : Type*} {D₁ : Type*} {D₂ : Type*} {D₃ : Type*} [Category* C] [Category* D₁]
  [Category* D₂] [Category* D₃] [Abelian D₁] [Abelian D₂] [Abelian D₃]
  {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂}

/-- Let `ψ` be an epimorphism out of `P₁ M`, and suppose the image of `ψ` under `L`, read through
the comparison `e` at its source and through an isomorphism `α` at its target, is a morphism `p`
out of `P₂ M`. Then the conjugate of the kernel subobject of `ψ` is the kernel subobject of
`p`. -/
theorem conjSubobject_kernelSubobject_eq (e : P₂ ≅ P₁ ⋙ L) {M : C} {N : D₁}
    (ψ : P₁.obj M ⟶ N) [Epi ψ] {Q : D₂} (p : P₂.obj M ⟶ Q) (α : L.obj N ≅ Q)
    (hα : e.hom.app M ≫ L.map ψ ≫ α.hom = p) :
    conjSubobject e (Limits.kernelSubobject ψ) = Limits.kernelSubobject p := by
  have hmap : L.map (Limits.cokernel.π (Limits.kernelSubobject ψ).arrow) ≫
      L.map (Abelian.cokernelKernelSubobjectIso ψ).hom = L.map ψ := by
    rw [← L.map_comp, Abelian.cokernel_π_kernelSubobject_comp]
  refine (Limits.kernelSubobject_eq_of_comp_mono _ p
    (L.map (Abelian.cokernelKernelSubobjectIso ψ).hom ≫ α.hom) ?_).symm
  dsimp only [conjQuotientProjection]
  simp only [Category.assoc]
  rwa [← Category.assoc _ _ α.hom, hmap]

/-- If the images under `L` of the projections of `P₁ M` onto its quotients by two subobjects
differ by an isomorphism of their targets, then the two conjugate subobjects of `P₂ M` are
equal. -/
theorem conjSubobject_eq_of_iso_comp (e : P₂ ≅ P₁ ⋙ L) {M : C} (K K' : Subobject (P₁.obj M))
    (ι : L.obj (Limits.cokernel K.arrow) ≅ L.obj (Limits.cokernel K'.arrow))
    (h : L.map (Limits.cokernel.π K.arrow) ≫ ι.hom = L.map (Limits.cokernel.π K'.arrow)) :
    conjSubobject e K = conjSubobject e K' := by
  refine (Limits.kernelSubobject_eq_of_comp_mono (conjQuotientProjection e K)
    (conjQuotientProjection e K') ι.hom ?_).symm
  dsimp only [conjQuotientProjection]
  rw [Category.assoc, h]

/-- If two subobjects of `P₁ M` have the same conjugate, the images under `L` of the projections
of `P₁ M` onto the two quotients differ by an isomorphism of their targets. -/
theorem exists_iso_of_conjSubobject_eq [L.PreservesEpimorphisms] (e : P₂ ≅ P₁ ⋙ L) {M : C}
    (K K' : Subobject (P₁.obj M)) (h : conjSubobject e K = conjSubobject e K') :
    ∃ ι : L.obj (Limits.cokernel K.arrow) ≅ L.obj (Limits.cokernel K'.arrow),
      L.map (Limits.cokernel.π K.arrow) ≫ ι.hom = L.map (Limits.cokernel.π K'.arrow) := by
  obtain ⟨ι, hι⟩ := Abelian.exists_iso_of_kernelSubobject_eq (conjQuotientProjection e K)
    (conjQuotientProjection e K') h
  refine ⟨ι, ?_⟩
  have hcomp : e.hom.app M ≫ L.map (Limits.cokernel.π K.arrow) ≫ ι.hom =
      e.hom.app M ≫ L.map (Limits.cokernel.π K'.arrow) := by
    dsimp only [conjQuotientProjection] at hι
    rwa [← Category.assoc]
  exact (cancel_epi (e.hom.app M)).mp hcomp

/-- Let `K, K'` be subobjects of `P₁ M` and `ι` an isomorphism between the images under `L` of
their quotients. If the images under `L'` of `L.map (cokernel.π K.arrow) ≫ ι.hom` and of
`L.map (cokernel.π K'.arrow)` agree, then the conjugates of `K` and `K'` along `e` have the same
conjugate along `e'`. -/
theorem conjSubobject_conjSubobject_eq_of_iso_comp {P₃ : C ⥤ D₃} {L' : D₂ ⥤ D₃}
    [L.PreservesEpimorphisms] (e : P₂ ≅ P₁ ⋙ L) (e' : P₃ ≅ P₂ ⋙ L') {M : C}
    (K K' : Subobject (P₁.obj M))
    (ι : L.obj (Limits.cokernel K.arrow) ≅ L.obj (Limits.cokernel K'.arrow))
    (h : L'.map (L.map (Limits.cokernel.π K.arrow) ≫ ι.hom) =
      L'.map (L.map (Limits.cokernel.π K'.arrow))) :
    conjSubobject e' (conjSubobject e K) = conjSubobject e' (conjSubobject e K') := by
  have hπ : ∀ K : Subobject (P₁.obj M), Limits.cokernel.π (conjSubobject e K).arrow =
      e.hom.app M ≫ L.map (Limits.cokernel.π K.arrow) ≫ (conjSubobjectCokernelIso e K).inv := by
    intro K
    rw [← Category.assoc, ← show conjQuotientProjection e K =
      e.hom.app M ≫ L.map (Limits.cokernel.π K.arrow) from rfl,
      ← cokernel_π_comp_conjSubobjectCokernelIso_hom e K, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  refine conjSubobject_eq_of_iso_comp e' (conjSubobject e K) (conjSubobject e K')
    (L'.mapIso (conjSubobjectCokernelIso e K ≪≫ ι ≪≫
      (conjSubobjectCokernelIso e K').symm)) ?_
  rw [Functor.mapIso_hom, ← L'.map_comp, hπ K, hπ K']
  simp only [L'.map_comp, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc] at h ⊢
  rw [← Category.assoc (L'.map _) (L'.map ι.hom), h]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

/-- The inverse image of a module of finite presentation along any morphism of algebraic spaces
over `S` is again of finite presentation. -/
def PullbackPreservesFinitePresentationEverywhere (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2),
    M.IsFinitePresentationOnSite →
      ((modulePullback B S hS f).obj M).IsFinitePresentationOnSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

/-- The scheme of the big fppf site underlying a test scheme over `Y`, as a functor. -/
abbrev testScheme : SchemesOver D.Y ⥤ Scheme.{u} :=
  CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙ BigFppfOver.toScheme B S hS

/-- If inverse images preserve finite presentation and `F` is of finite presentation, then the
base change of `F` to any test scheme over `Y` is of finite presentation. -/
theorem baseChangeModule_isFinitePresentationOnSite
    (hfpall : PullbackPreservesFinitePresentationEverywhere B S hS)
    (hF : D.F.IsFinitePresentationOnSite) (T : SchemesOver D.Y) :
    (D.baseChangeModule T).IsFinitePresentationOnSite :=
  hfpall (D.sourceProjection T) D.F hF

/-! ### Descent along a limit of test schemes -/

/-- For a cofiltered inverse system `E` of affine test schemes over `Y` whose limit on underlying
schemes is the affine test scheme `c.pt`, with `f` quasi-compact and quasi-separated and the base
changes of `F` of finite presentation, every finitely presented quotient of `F_{c.pt}` which is
flat over `c.pt` is, up to isomorphism, the pullback of a finitely presented quotient of
`F_{E i}` flat over `E i` at some stage `i`.

A quotient is recorded by an epimorphism out of the base change of `F`, and
`AlgebraicGeometry.Space.QuotientSituation.baseChangeComparison` identifies the pullback of
`F_{E i}` to `X_{c.pt}` with `F_{c.pt}`. -/
def FlatQuotientsDescendToStage (I : Type (max w w')) [Category.{w'} I] [IsCofiltered I] :
    Prop :=
  ∀ (E : I ⥤ SchemesOver D.Y) (c : Cone E), IsLimit (D.testScheme.mapCone c) →
    (∀ i, IsAffine (D.testScheme.obj (E.obj i))) → IsAffine (D.testScheme.obj c.pt) →
    IsQuasiCompact B S hS D.f.hom → IsQuasiSeparated B S hS D.f.hom →
    (D.baseChangeModule c.pt).IsFinitePresentationOnSite →
    (∀ i, (D.baseChangeModule (E.obj i)).IsFinitePresentationOnSite) →
    ∀ (Q : Modules.{u, u} B S hS (D.space c.pt).1 (D.space c.pt).2)
      (p : D.baseChangeModule c.pt ⟶ Q), Epi p → Q.IsFinitePresentationOnSite →
      IsFlatOver B S hS (D.space c.pt).2 (D.projection c.pt).hom Q →
      ∃ (i : I) (N : Modules.{u, u} B S hS (D.space (E.obj i)).1 (D.space (E.obj i)).2)
        (ψ : D.baseChangeModule (E.obj i) ⟶ N),
        Epi ψ ∧ N.IsFinitePresentationOnSite ∧
          IsFlatOver B S hS (D.space (E.obj i)).2 (D.projection (E.obj i)).hom N ∧
          ∃ α : (modulePullback B S hS (D.relativeMap (c.π.app i))).obj N ≅ Q,
            (D.baseChangeComparison (c.π.app i)).hom.app D.F ≫
              (modulePullback B S hS (D.relativeMap (c.π.app i))).map ψ ≫ α.hom = p

/-- In the setting of `AlgebraicGeometry.Space.QuotientSituation.FlatQuotientsDescendToStage`:
if two finitely presented quotients of `F_{E i}` at a stage `i` become isomorphic, compatibly
with their projections, after pullback to `X_{c.pt}`, then there are a transition morphism
`g : E j ⟶ E i` and an isomorphism between their pullbacks along `g` which is compatible with the
projections after further pullback to `X_{c.pt}`. -/
def FlatQuotientIsosDescendToStage (I : Type (max w w')) [Category.{w'} I] [IsCofiltered I] :
    Prop :=
  ∀ (E : I ⥤ SchemesOver D.Y) (c : Cone E), IsLimit (D.testScheme.mapCone c) →
    (∀ i, IsAffine (D.testScheme.obj (E.obj i))) → IsAffine (D.testScheme.obj c.pt) →
    IsQuasiCompact B S hS D.f.hom → IsQuasiSeparated B S hS D.f.hom →
    (D.baseChangeModule c.pt).IsFinitePresentationOnSite →
    (∀ i, (D.baseChangeModule (E.obj i)).IsFinitePresentationOnSite) →
    ∀ (i : I) (N N' : Modules.{u, u} B S hS (D.space (E.obj i)).1 (D.space (E.obj i)).2)
      (p : D.baseChangeModule (E.obj i) ⟶ N) (p' : D.baseChangeModule (E.obj i) ⟶ N'),
      Epi p → Epi p' → N.IsFinitePresentationOnSite → N'.IsFinitePresentationOnSite →
      ∀ ι : (modulePullback B S hS (D.relativeMap (c.π.app i))).obj N ≅
          (modulePullback B S hS (D.relativeMap (c.π.app i))).obj N',
        (modulePullback B S hS (D.relativeMap (c.π.app i))).map p ≫ ι.hom =
            (modulePullback B S hS (D.relativeMap (c.π.app i))).map p' →
          ∃ (j : I) (g : j ⟶ i) (ι' : (modulePullback B S hS (D.relativeMap (E.map g))).obj N ≅
              (modulePullback B S hS (D.relativeMap (E.map g))).obj N'),
            (modulePullback B S hS (D.relativeMap (c.π.app j))).map
                ((modulePullback B S hS (D.relativeMap (E.map g))).map p ≫ ι'.hom) =
              (modulePullback B S hS (D.relativeMap (c.π.app j))).map
                ((modulePullback B S hS (D.relativeMap (E.map g))).map p')

/-- For a cofiltered inverse system `E` of affine test schemes over `Y` with affine limit `c.pt`
and `f` quasi-compact and quasi-separated, two morphisms of finitely presented modules on the
base change `X_{E i}` whose inverse images along the projection `X_{c.pt} ⟶ X_{E i}` agree
already have equal inverse images along the base change of a transition morphism
`E j ⟶ E i`. -/
def EventualModuleMapEqOverBaseChangeSystem (I : Type (max w w')) [Category.{w'} I]
    [IsCofiltered I] : Prop :=
  ∀ (E : I ⥤ SchemesOver D.Y) (c : Cone E), IsLimit (D.testScheme.mapCone c) →
    (∀ i, IsAffine (D.testScheme.obj (E.obj i))) → IsAffine (D.testScheme.obj c.pt) →
    IsQuasiCompact B S hS D.f.hom → IsQuasiSeparated B S hS D.f.hom →
    ∀ (i : I) (M N : Modules.{u, u} B S hS (D.space (E.obj i)).1 (D.space (E.obj i)).2),
      M.IsFinitePresentationOnSite → N.IsFinitePresentationOnSite → ∀ φ ψ : M ⟶ N,
        (modulePullback B S hS (D.relativeMap (c.π.app i))).map φ =
            (modulePullback B S hS (D.relativeMap (c.π.app i))).map ψ →
          ∃ (j : I) (g : j ⟶ i),
            (modulePullback B S hS (D.relativeMap (E.map g))).map φ =
              (modulePullback B S hS (D.relativeMap (E.map g))).map ψ

/-! ### Limit preservation -/

/-- Assume that `f` is quasi-compact and quasi-separated and that `F` is of finite presentation.
Assume also the coherence of module pushforwards (`ModulePushforwardCoherence`), that inverse
images preserve modules of finite presentation, and that along directed limits of affine test
schemes over `Y` finitely presented flat quotients (`FlatQuotientsDescendToStage`), isomorphisms
between them (`FlatQuotientIsosDescendToStage`) and equality of homomorphisms of finitely
presented modules (`EventualModuleMapEqOverBaseChangeSystem`) descend to a stage. Then the functor
`Q^{fp}_{F/X/Y}` of finitely presented quotients is limit preserving: for every directed system of
affine test schemes over `Y` with affine limit `T = lim T_i`, the comparison
`colim Q^{fp}_{F/X/Y}(T_i) ⟶ Q^{fp}_{F/X/Y}(T)` is a bijection.

The finiteness conditions on `f` and `F` alone do not give the conclusion
(`not_forall_finitePresentationQuotientsFunctor_limitPreserving`). Stacks 082Q, corrected, is
`finitePresentationQuotientsFunctor_limitPreserving_of_isLocallyOfFinitePresentation`. -/
theorem finitePresentationQuotientsFunctor_limitPreserving
    (hc : ModulePushforwardCoherence B S hS)
    (hfpall : PullbackPreservesFinitePresentationEverywhere B S hS)
    (hdesc : ∀ (I : Type (max w w')) [Category.{w'} I] [IsCofiltered I],
      D.FlatQuotientsDescendToStage I)
    (hrigid : ∀ (I : Type (max w w')) [Category.{w'} I] [IsCofiltered I],
      D.FlatQuotientIsosDescendToStage I)
    (hfaith : ∀ (I : Type (max w w')) [Category.{w'} I] [IsCofiltered I],
      D.EventualModuleMapEqOverBaseChangeSystem I)
    (hqcf : IsQuasiCompact B S hS D.f.hom) (hqsf : IsQuasiSeparated B S hS D.f.hom)
    (hF : D.F.IsFinitePresentationOnSite) :
    LimitPreserving.{u, u + 1, w, w', u + 1, u} D.testScheme
      D.finitePresentationQuotientsFunctor := by
  intro I _ _ E c hlim haff hpt
  have hfpc : (D.baseChangeModule c.pt).IsFinitePresentationOnSite :=
    D.baseChangeModule_isFinitePresentationOnSite hfpall hF c.pt
  have hfpi : ∀ i, (D.baseChangeModule (E.obj i)).IsFinitePresentationOnSite := fun i =>
    D.baseChangeModule_isFinitePresentationOnSite hfpall hF (E.obj i)
  refine ⟨Types.FilteredColimit.isColimitOf' _ _ ?_ ?_⟩
  · rintro ⟨K, hK⟩
    have : (D.quotientModule c.pt K).IsFinitePresentationOnSite := hK.2
    obtain ⟨i, N, ψ, hψ, hNfp, hNflat, α, hα⟩ :=
      hdesc I E c hlim haff hpt hqcf hqsf hfpc hfpi (D.quotientModule c.pt K)
        (D.quotientProjection c.pt K) inferInstance hK.2 hK.1.2
    have := hψ
    have := hNfp
    have hcoker : cokernel (kernelSubobject ψ).arrow ≅ N := Abelian.cokernelKernelSubobjectIso ψ
    have hmem : kernelSubobject ψ ∈ D.finitePresentationQuotients (E.obj i) :=
      ⟨⟨SheafOfModules.IsQuasicoherentOnSite.of_iso hcoker.symm
          (SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite N),
        IsFlatOver.of_iso B S hS (D.space (E.obj i)).2 hcoker.symm hNflat⟩,
        SheafOfModules.IsFinitePresentationOnSite.of_iso hcoker.symm hNfp⟩
    have hval : K = D.quotientPullback (c.π.app i) (kernelSubobject ψ) :=
      (kernelSubobject_cokernel_π K).symm.trans
        (Functor.conjSubobject_kernelSubobject_eq (D.baseChangeComparison (c.π.app i)) ψ
          (D.quotientProjection c.pt K) α hα).symm
    exact ⟨op i, ⟨kernelSubobject ψ, hmem⟩, Subtype.ext hval⟩
  · rintro ⟨i⟩ ⟨K, hK⟩ ⟨K', hK'⟩ heq
    have hpull : D.quotientPullback (c.π.app i) K = D.quotientPullback (c.π.app i) K' :=
      congrArg Subtype.val heq
    have : (D.quotientModule (E.obj i) K).IsFinitePresentationOnSite := hK.2
    have : (D.quotientModule (E.obj i) K').IsFinitePresentationOnSite := hK'.2
    obtain ⟨ι, hι⟩ := Functor.exists_iso_of_conjSubobject_eq
      (D.baseChangeComparison (c.π.app i)) K K' hpull
    obtain ⟨j, g, ι', hι'⟩ :=
      hrigid I E c hlim haff hpt hqcf hqsf hfpc hfpi i (D.quotientModule (E.obj i) K)
        (D.quotientModule (E.obj i) K') (D.quotientProjection (E.obj i) K)
        (D.quotientProjection (E.obj i) K') inferInstance inferInstance hK.2 hK'.2 ι hι
    obtain ⟨k, e, hke⟩ :=
      hfaith I E c hlim haff hpt hqcf hqsf j
        ((modulePullback B S hS (D.relativeMap (E.map g))).obj (D.baseChangeModule (E.obj i)))
        ((modulePullback B S hS (D.relativeMap (E.map g))).obj
          (D.quotientModule (E.obj i) K'))
        (hfpall (D.relativeMap (E.map g)) _ (hfpi i))
        (hfpall (D.relativeMap (E.map g)) _ hK'.2)
        ((modulePullback B S hS (D.relativeMap (E.map g))).map
          (D.quotientProjection (E.obj i) K) ≫ ι'.hom)
        ((modulePullback B S hS (D.relativeMap (E.map g))).map
          (D.quotientProjection (E.obj i) K')) hι'
    have hval : D.quotientPullback (E.map (e ≫ g)) K =
        D.quotientPullback (E.map (e ≫ g)) K' := by
      rw [E.map_comp, D.quotientPullback_comp hc, D.quotientPullback_comp hc]
      exact Functor.conjSubobject_conjSubobject_eq_of_iso_comp
        (D.baseChangeComparison (E.map g)) (D.baseChangeComparison (E.map e)) K K' ι' hke
    exact ⟨op k, (e ≫ g).op, Subtype.ext hval⟩

end QuotientSituation

end AlgebraicGeometry.Space

end
