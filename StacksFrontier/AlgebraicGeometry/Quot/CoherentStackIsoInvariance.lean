module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackCanonical
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaBaseChange
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaPresheafProduct

/-!
# `Coh_{X/Y}` depends on `X` over `Y` only up to isomorphism

Let `f : X ⟶ Y` be a finitely presented morphism of algebraic spaces over `S`, the standing data
of Stacks 08KB, and let `e : X' ≅ X` be an isomorphism of algebraic spaces with
`f' = e ≫ f`. Then the stacks of coherent sheaves with proper support `Coh_{X'/Y}` and
`Coh_{X/Y}` are equivalent as categories over the big fppf site of `S`: an object `(T, F)` of
`Coh_{X'/Y}` goes to `(T, (e_T⁻¹)^*F)`, where `e_T : X'_T ≅ X_T` is the induced isomorphism of
base changes. Consequently one of them is an algebraic stack exactly when the other is.

The construction is that of the top row of the square of Stacks 08LP
(`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackBaseChangeUnconditional.lean`), with the
comparison of the two base changes replaced by `e_T`.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.isoSituation`: the standing datum `f' : X' ⟶ Y`.
* `AlgebraicGeometry.Space.CoherentSituation.isoSpaceIso`: the comparison `X'_T ≅ X_T`.
* `AlgebraicGeometry.Space.CoherentSituation.isoFunctor`: the functor `Coh_{X'/Y} ⥤ Coh_{X/Y}`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isoEquivalenceOver`: the functor is an equivalence
  over the site.
* `AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_isoSituation_iff`: algebraicity
  of `Coh_{X'/Y}` and of `Coh_{X/Y}` are equivalent.

## References

* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08LP](https://stacks.math.columbia.edu/tag/08LP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u w

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The base change `X_T` of `f : X ⟶ Y` along a test scheme is a fibre product. -/
theorem isPullback_baseChangeSpace {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (T : SchemesOver Y) :
    IsPullback (baseChangeProjection f T) (baseChangeInclusion f T) f T.hom :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS f ((schemesOverToOver Y).obj T).hom

namespace CoherentSituation

variable (D : CoherentSituation B S hS) {X' : AlgebraicSpaces B S hS} (f' : X' ⟶ D.Y)
  (hf' : IsFinitePresentation B S hS f'.hom)

/-- The standing datum `f' : X' ⟶ Y` with the same target as `D`. -/
abbrev isoSituation : CoherentSituation B S hS where
  X := X'
  Y := D.Y
  f := f'
  finitePresentation := hf'

variable {D f'} (e : X' ≅ D.X) (he : e.hom ≫ D.f = f')

include he in
/-- The base change `X'_T` is a fibre product of `f` with the test scheme, through `e`. -/
theorem isPullback_isoSituation_space (T : SchemesOver D.Y) :
    IsPullback (baseChangeProjection f' T ≫ e.hom) (baseChangeInclusion f' T) D.f T.hom := by
  have h₁ := isPullback_baseChangeSpace f' T
  have h₂ : IsPullback e.hom f' D.f (𝟙 D.Y) :=
    IsPullback.of_horiz_isIso (CommSq.mk (by rw [he, Category.comp_id]))
  simpa using h₁.paste_horiz h₂

/-- **The comparison `X'_T ≅ X_T`** of the two base changes along a test scheme. -/
def isoSpaceIso (T : SchemesOver D.Y) :
    baseChangeSpace f' T ≅ D.space T :=
  (isPullback_isoSituation_space e he T).isoIsPullback _ _ (isPullback_baseChangeSpace D.f T)

/-- The comparison `X'_T ≅ X_T` commutes with the projections to `X'` and `X` through `e`. -/
@[reassoc (attr := simp)]
theorem isoSpaceIso_hom_projection (T : SchemesOver D.Y) :
    (isoSpaceIso e he T).hom ≫ baseChangeProjection D.f T =
      baseChangeProjection f' T ≫ e.hom :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The comparison `X'_T ≅ X_T` commutes with the maps to the test scheme. -/
@[reassoc (attr := simp)]
theorem isoSpaceIso_hom_inclusion (T : SchemesOver D.Y) :
    (isoSpaceIso e he T).hom ≫ baseChangeInclusion D.f T = baseChangeInclusion f' T :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The inverse comparison `X_T ≅ X'_T` commutes with the maps to the test scheme. -/
@[reassoc (attr := simp)]
theorem isoSpaceIso_inv_inclusion (T : SchemesOver D.Y) :
    (isoSpaceIso e he T).inv ≫ baseChangeInclusion f' T = baseChangeInclusion D.f T := by
  rw [Iso.inv_comp_eq, isoSpaceIso_hom_inclusion]

/-- **The comparison is natural in the test scheme.** -/
theorem isoSpaceIso_hom_naturality {T T' : SchemesOver D.Y} (h : T ⟶ T') :
    baseChangeMap f' h ≫ (isoSpaceIso e he T').hom =
      (isoSpaceIso e he T).hom ≫ baseChangeMap D.f h := by
  refine baseChange_hom_ext D.f ?_ ?_
  · simp only [Category.assoc, isoSpaceIso_hom_projection, baseChangeMap_comp_projection,
      baseChangeMap_comp_projection_assoc]
  · simp only [Category.assoc, isoSpaceIso_hom_inclusion, baseChangeMap_comp_inclusion,
      isoSpaceIso_hom_inclusion_assoc]

/-- The comparison, read with its inverse, is natural in the test scheme. -/
theorem isoSpaceIso_inv_naturality {T T' : SchemesOver D.Y} (h : T ⟶ T') :
    (isoSpaceIso e he T).inv ≫ baseChangeMap f' h =
      baseChangeMap D.f h ≫ (isoSpaceIso e he T').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← isoSpaceIso_hom_naturality e he h,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The inverse comparison sits in a cartesian square over the identity of the test scheme. -/
theorem isPullback_isoSpaceIso_inv (T : SchemesOver D.Y) :
    IsPullback (isoSpaceIso e he T).inv (baseChangeInclusion D.f T)
      (baseChangeInclusion f' T) (𝟙 _) :=
  IsPullback.of_horiz_isIso (CommSq.mk (by simp))

/-- The comparison sits in a cartesian square over the identity of the test scheme. -/
theorem isPullback_isoSpaceIso_hom (T : SchemesOver D.Y) :
    IsPullback (isoSpaceIso e he T).hom (baseChangeInclusion f' T)
      (baseChangeInclusion D.f T) (𝟙 _) :=
  IsPullback.of_horiz_isIso (CommSq.mk (by simp))

/-- **The comparison of the two iterated inverse images along the square of a morphism of test
schemes.** -/
def isoModuleSquare {T T' : SchemesOver D.Y} (h : T ⟶ T') :
    modulePullback B S hS (isoSpaceIso e he T').inv ⋙
        modulePullback B S hS (baseChangeMap D.f h) ≅
      modulePullback B S hS (baseChangeMap f' h) ⋙
        modulePullback B S hS (isoSpaceIso e he T).inv :=
  modulePullbackSquare B S hS rfl (isoSpaceIso_inv_naturality e he h)

variable (hc : ModulePushforwardCoherence B S hS)

/-- The comparison is compatible with the unit law of Stacks 03LU. -/
theorem isoModuleSquare_id (T : SchemesOver D.Y) :
    isoModuleSquare e he (𝟙 T) ≪≫
        Functor.isoWhiskerRight ((isoSituation D f' hf').idComparison hc T)
          (modulePullback B S hS (isoSpaceIso e he T).inv) ≪≫
        Functor.leftUnitor (modulePullback B S hS (isoSpaceIso e he T).inv) =
      Functor.isoWhiskerLeft (modulePullback B S hS (isoSpaceIso e he T).inv)
          (D.idComparison hc T) ≪≫
        Functor.rightUnitor (modulePullback B S hS (isoSpaceIso e he T).inv) :=
  modulePullbackSquare_id hc (baseChangeMap_id D.f T) (baseChangeMap_id f' T) rfl
    (isoSpaceIso_inv_naturality e he (𝟙 T))

/-- The comparison at a composite, with the composite of the two induced morphisms of base
changes written out. -/
theorem isoModuleSquare_comp_eq {T T' T'' : SchemesOver D.Y} (h : T ⟶ T') (h' : T' ⟶ T'') :
    isoModuleSquare e he (h ≫ h') =
      modulePullbackSquare B S hS
        (rfl : baseChangeMap D.f (h ≫ h') ≫ (isoSpaceIso e he T'').inv = _)
        (isoSpaceIso_inv_naturality e he (h ≫ h')) :=
  rfl

/-- The inverse image along the inverse comparison is fully faithful. -/
def fullyFaithful_modulePullback_isoSpaceIso (T : SchemesOver D.Y) :
    (modulePullback B S hS (isoSpaceIso e he T).inv).FullyFaithful :=
  (hc.modulePullbackEquivalence (isoSpaceIso e he T).symm).fullyFaithfulFunctor

/-! ### Transport of objects and morphisms -/

variable (hst : ModulePullbackStabilityOfFinitePresentation B S hS)

/-- **The object of `Coh_{X/Y}` attached to an object of `Coh_{X'/Y}`**: the same test scheme and
the inverse image of the module along the inverse comparison `X_T ⟶ X'_T`. -/
def isoObject (A : CoherentObject (isoSituation D f' hf')) : CoherentObject D where
  T := A.T
  F := (modulePullback B S hS (isoSpaceIso e he A.T).inv).obj A.F
  finitePresentation :=
    hst.finitePresentation (isoSpaceIso e he A.T).inv A.F A.finitePresentation
  quasicoherent :=
    have := hst.finitePresentation (isoSpaceIso e he A.T).inv A.F A.finitePresentation
    inferInstance
  flat :=
    hst.flat (isPullback_isoSpaceIso_inv e he A.T) A.F A.finitePresentation A.flat
  properSupport := by
    obtain ⟨hp, hU, hproper⟩ := A.properSupport
    have := A.finitePresentation
    obtain ⟨hU', hproper'⟩ := hst.properSupport (isPullback_isoSpaceIso_inv e he A.T) hp
      A.F A.quasicoherent inferInstance hU hproper
    exact ⟨(isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (isPullback_isoSpaceIso_inv e he A.T) hp, hU', hproper'⟩

/-- The transported object lives over the same test scheme. -/
@[simp]
theorem isoObject_T (A : CoherentObject (isoSituation D f' hf')) :
    (isoObject hf' e he hst A).T = A.T :=
  rfl

/-- The module of the transported object is the inverse image along the inverse comparison. -/
theorem isoObject_F (A : CoherentObject (isoSituation D f' hf')) :
    (isoObject hf' e he hst A).F =
      (modulePullback B S hS (isoSpaceIso e he A.T).inv).obj A.F :=
  rfl

/-- **The morphism of `Coh_{X/Y}` attached to a morphism of `Coh_{X'/Y}`**: the same base map and
the comparison of modules conjugated by the comparison of base changes. -/
def isoHom {A A' : CoherentObject (isoSituation D f' hf')} (m : CoherentHom A A') :
    CoherentHom (isoObject hf' e he hst A) (isoObject hf' e he hst A') where
  base := m.base
  fibre := Functor.conjFibre (isoModuleSquare e he m.base) m.fibre
  isIso_fibre := by
    have := m.isIso_fibre
    exact Functor.isIso_conjFibre (isoModuleSquare e he m.base) m.fibre

/-- The transported morphism has the same base map. -/
@[simp]
theorem isoHom_base {A A' : CoherentObject (isoSituation D f' hf')} (m : CoherentHom A A') :
    (isoHom hf' e he hst m).base = m.base :=
  rfl

/-- The module map of the transported morphism is the conjugate by `isoModuleSquare`. -/
theorem isoHom_fibre {A A' : CoherentObject (isoSituation D f' hf')} (m : CoherentHom A A') :
    (isoHom hf' e he hst m).fibre = Functor.conjFibre (isoModuleSquare e he m.base) m.fibre :=
  rfl

/-- The unit comparison of `D` at the test scheme of a transported object is that at the original
test scheme. -/
theorem idComparison_isoObject (A : CoherentObject (isoSituation D f' hf')) :
    D.idComparison hc (isoObject hf' e he hst A).T = D.idComparison hc A.T :=
  rfl

/-- **Transport along the comparison preserves identities.** -/
theorem isoHom_id (A : CoherentObject (isoSituation D f' hf')) :
    isoHom hf' e he hst (CoherentHom.id hc A) = CoherentHom.id hc (isoObject hf' e he hst A) := by
  have hcomp : HEq ((D.idComparison hc A.T).hom.app
        ((modulePullback B S hS (isoSpaceIso e he A.T).inv).obj A.F))
      ((D.idComparison hc (isoObject hf' e he hst A).T).hom.app
        (isoObject hf' e he hst A).F) := by
    rw [isoObject_F hf' e he hst A, idComparison_isoObject hf' e he hc hst A]
    exact HEq.rfl
  refine coherentHom_eq_of_heq rfl ?_
  refine HEq.trans (heq_of_eq ((isoHom_fibre hf' e he hst (CoherentHom.id hc A)).trans
      ((congrArg (Functor.conjFibre (isoModuleSquare e he (𝟙 A.T)))
          (CoherentHom.id_fibre hc A)).trans
        (Functor.conjFibre_id (isoModuleSquare e he (𝟙 A.T))
          ((isoSituation D f' hf').idComparison hc A.T)
          (D.idComparison hc A.T)
          (isoModuleSquare_id hf' e he hc A.T) A.F)))) ?_
  exact HEq.trans hcomp (heq_of_eq (CoherentHom.id_fibre hc (isoObject hf' e he hst A)).symm)

include hc in
/-- **Transport along the comparison preserves composition.** -/
theorem isoHom_comp {A A' A'' : CoherentObject (isoSituation D f' hf')} (m : CoherentHom A A')
    (n : CoherentHom A' A'') :
    isoHom hf' e he hst (m.comp n) = (isoHom hf' e he hst m).comp (isoHom hf' e he hst n) := by
  refine coherentHom_eq_of_heq rfl (heq_of_eq ?_)
  refine (isoHom_fibre hf' e he hst (m.comp n)).trans ?_
  refine (congrArg (Functor.conjFibre (isoModuleSquare e he (m.base ≫ n.base)))
    (CoherentHom.comp_fibre m n)).trans ?_
  refine (congrArg (fun σ => Functor.conjFibre σ
      (Functor.fibreComp ((isoSituation D f' hf').compComparison m.base n.base) m.fibre n.fibre))
    (isoModuleSquare_comp_eq e he m.base n.base)).trans ?_
  refine (Functor.conjFibre_fibreComp ((isoSituation D f' hf').compComparison m.base n.base)
    (D.compComparison m.base n.base)
    (isoModuleSquare e he m.base) (isoModuleSquare e he n.base) _
    (modulePullbackSquare_comp hc
      (baseChangeMap_comp D.f m.base n.base).symm
      (baseChangeMap_comp f' m.base n.base).symm rfl
      (isoSpaceIso_inv_naturality e he m.base) rfl
      (isoSpaceIso_inv_naturality e he n.base) rfl
      (isoSpaceIso_inv_naturality e he (m.base ≫ n.base)))
    m.fibre n.fibre).trans ?_
  refine (congrArg (fun a => Functor.fibreComp (D.compComparison m.base n.base) a
      (Functor.conjFibre (isoModuleSquare e he n.base) n.fibre))
    (isoHom_fibre hf' e he hst m).symm).trans ?_
  refine (congrArg (fun b => Functor.fibreComp (D.compComparison m.base n.base)
      (isoHom hf' e he hst m).fibre b)
    (isoHom_fibre hf' e he hst n).symm).trans ?_
  exact (CoherentHom.comp_fibre (isoHom hf' e he hst m) (isoHom hf' e he hst n)).symm

/-! ### The functor -/

/-- **The functor `Coh_{X'/Y} ⥤ Coh_{X/Y}`** of the comparison `X'_T ≅ X_T`. -/
def isoFunctor (cd : CoherentCategoryData hc D)
    (cd' : CoherentCategoryData hc (isoSituation D f' hf')) :
    @Functor (CoherentObject (isoSituation D f' hf')) cd'.category (CoherentObject D)
      cd.category :=
  letI : Category.{u + 1} (CoherentObject (isoSituation D f' hf')) := cd'.category
  letI : Category.{u + 1} (CoherentObject D) := cd.category
  { obj := isoObject hf' e he hst
    map := fun {A A'} m => (Equiv.cast (cd.hom_type _ _)).symm
      (isoHom hf' e he hst ((Equiv.cast (cd'.hom_type A A')) m))
    map_id := fun A => by
      refine (Equiv.cast (cd.hom_type _ _)).injective ?_
      rw [Equiv.apply_symm_apply, cd'.identity, cd.identity]
      exact isoHom_id hf' e he hc hst A
    map_comp := fun {A A' A''} m n => by
      refine (Equiv.cast (cd.hom_type _ _)).injective ?_
      rw [Equiv.apply_symm_apply, cd.composition, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply, cd'.composition]
      exact isoHom_comp hf' e he hc hst _ _ }

/-- On morphisms, `isoFunctor` is `isoHom` read through the identifications of the hom types. -/
theorem isoFunctor_cast (cd : CoherentCategoryData hc D)
    (cd' : CoherentCategoryData hc (isoSituation D f' hf'))
    {A A' : CoherentObject (isoSituation D f' hf')} :
    letI : Category.{u + 1} (CoherentObject (isoSituation D f' hf')) := cd'.category
    letI : Category.{u + 1} (CoherentObject D) := cd.category
    ∀ m : A ⟶ A',
      (Equiv.cast (cd.hom_type _ _)) ((isoFunctor hf' e he hc hst cd cd').map m) =
        isoHom hf' e he hst ((Equiv.cast (cd'.hom_type A A')) m) :=
  fun _ => Equiv.apply_symm_apply _ _

/-- The functor commutes with the projections to the site on the nose. -/
theorem isoFunctor_comp_projection (cd : CoherentCategoryData hc D)
    (cd' : CoherentCategoryData hc (isoSituation D f' hf')) :
    letI : Category.{u + 1} (CoherentObject (isoSituation D f' hf')) := cd'.category
    letI : Category.{u + 1} (CoherentObject D) := cd.category
    isoFunctor hf' e he hc hst cd cd' ⋙ coherentSiteProjection cd = coherentSiteProjection cd' := by
  let _ : Category.{u + 1} (CoherentObject (isoSituation D f' hf')) := cd'.category
  let _ : Category.{u + 1} (CoherentObject D) := cd.category
  refine CategoryTheory.Functor.ext (fun A => rfl) (fun A A' m => ?_)
  show ((Equiv.cast (cd.hom_type _ _)) ((isoFunctor hf' e he hc hst cd cd').map m)).base.left =
    𝟙 _ ≫ ((Equiv.cast (cd'.hom_type A A')) m).base.left ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id, isoFunctor_cast hf' e he hc hst cd cd' m]
  rfl

include hc in
/-- Transport of morphisms along the comparison is injective. -/
theorem isoHom_injective {A A' : CoherentObject (isoSituation D f' hf')} :
    Function.Injective (isoHom hf' e he hst (A := A) (A' := A')) := by
  intro m n h
  have hb : m.base = n.base :=
    congrArg (fun k : CoherentHom (isoObject hf' e he hst A) (isoObject hf' e he hst A') =>
      k.base) h
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨nb, nf, ni⟩ := n
  change mb = nb at hb
  subst hb
  refine coherentHom_eq_of_heq rfl (heq_of_eq ?_)
  refine Functor.conjFibre_injective (isoModuleSquare e he mb)
    (fullyFaithful_modulePullback_isoSpaceIso e he hc A.T) ?_
  have hmid : (isoHom hf' e he hst (⟨mb, mf, mi⟩ : CoherentHom A A')).fibre =
      (isoHom hf' e he hst (⟨mb, nf, ni⟩ : CoherentHom A A')).fibre :=
    eq_of_heq (heq_fibre_of_eq h)
  exact ((isoHom_fibre hf' e he hst (⟨mb, mf, mi⟩ : CoherentHom A A')).symm.trans hmid).trans
    (isoHom_fibre hf' e he hst (⟨mb, nf, ni⟩ : CoherentHom A A'))

include hc in
/-- Every morphism between transported objects is the transport of a morphism. -/
theorem exists_isoHom {A A' : CoherentObject (isoSituation D f' hf')}
    (m : CoherentHom (isoObject hf' e he hst A) (isoObject hf' e he hst A')) :
    ∃ k : CoherentHom A A', isoHom hf' e he hst k = m := by
  obtain ⟨mb, mf, mi⟩ := m
  have hE := fullyFaithful_modulePullback_isoSpaceIso e he hc A.T
  refine ⟨⟨mb, Functor.conjFibreInv (isoModuleSquare e he mb) hE mf,
    Functor.isIso_conjFibreInv (isoModuleSquare e he mb) hE mf mi⟩, ?_⟩
  refine coherentHom_eq_of_heq rfl (heq_of_eq ?_)
  refine (isoHom_fibre hf' e he hst _).trans ?_
  exact Functor.conjFibre_conjFibreInv (isoModuleSquare e he mb) hE mf

/-- The functor `Coh_{X'/Y} ⥤ Coh_{X/Y}` is faithful. -/
theorem isoFunctor_faithful (cd : CoherentCategoryData hc D)
    (cd' : CoherentCategoryData hc (isoSituation D f' hf')) :
    letI : Category.{u + 1} (CoherentObject (isoSituation D f' hf')) := cd'.category
    letI : Category.{u + 1} (CoherentObject D) := cd.category
    (isoFunctor hf' e he hc hst cd cd').Faithful := by
  let _ : Category.{u + 1} (CoherentObject (isoSituation D f' hf')) := cd'.category
  let _ : Category.{u + 1} (CoherentObject D) := cd.category
  constructor
  intro A A' m n h
  refine (Equiv.cast (cd'.hom_type A A')).injective ?_
  refine isoHom_injective hf' e he hc hst ?_
  rw [← isoFunctor_cast hf' e he hc hst cd cd' m, ← isoFunctor_cast hf' e he hc hst cd cd' n]
  exact congrArg (Equiv.cast (cd.hom_type _ _)) h

/-- The functor `Coh_{X'/Y} ⥤ Coh_{X/Y}` is full. -/
theorem isoFunctor_full (cd : CoherentCategoryData hc D)
    (cd' : CoherentCategoryData hc (isoSituation D f' hf')) :
    letI : Category.{u + 1} (CoherentObject (isoSituation D f' hf')) := cd'.category
    letI : Category.{u + 1} (CoherentObject D) := cd.category
    (isoFunctor hf' e he hc hst cd cd').Full := by
  let _ : Category.{u + 1} (CoherentObject (isoSituation D f' hf')) := cd'.category
  let _ : Category.{u + 1} (CoherentObject D) := cd.category
  constructor
  intro A A' m
  obtain ⟨k, hk⟩ := exists_isoHom hf' e he hc hst ((Equiv.cast (cd.hom_type _ _)) m)
  refine ⟨(Equiv.cast (cd'.hom_type A A')).symm k, ?_⟩
  refine (Equiv.cast (cd.hom_type _ _)).injective ?_
  rw [isoFunctor_cast hf' e he hc hst cd cd', Equiv.apply_symm_apply, hk]
  rfl

/-- The object of `Coh_{X'/Y}` whose transport is a given object of `Coh_{X/Y}`. -/
def isoPreimage (A : CoherentObject D) : CoherentObject (isoSituation D f' hf') where
  T := A.T
  F := (modulePullback B S hS (isoSpaceIso e he A.T).hom).obj A.F
  finitePresentation :=
    hst.finitePresentation (isoSpaceIso e he A.T).hom A.F A.finitePresentation
  quasicoherent :=
    have := hst.finitePresentation (isoSpaceIso e he A.T).hom A.F A.finitePresentation
    inferInstance
  flat :=
    hst.flat (isPullback_isoSpaceIso_hom e he A.T) A.F A.finitePresentation A.flat
  properSupport := by
    obtain ⟨hp, hU, hproper⟩ := A.properSupport
    have := A.finitePresentation
    obtain ⟨hU', hproper'⟩ := hst.properSupport (isPullback_isoSpaceIso_hom e he A.T) hp
      A.F A.quasicoherent inferInstance hU hproper
    exact ⟨(isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (isPullback_isoSpaceIso_hom e he A.T) hp, hU', hproper'⟩

/-- The vertical comparison of the transport of the preimage with the given object. -/
def isoPreimageHom (A : CoherentObject D) :
    CoherentHom A (isoObject hf' e he hst (isoPreimage hf' e he hst A)) where
  base := 𝟙 _
  fibre := ((D.idComparison hc A.T).app _ ≪≫
    ((hc.modulePullbackEquivalence (isoSpaceIso e he A.T)).unitIso.app A.F).symm).hom
  isIso_fibre := Iso.isIso_hom _

/-! ### The equivalence over the site -/

/-- **The transport functor is an equivalence over the site**, in the witness form of
`CategoryTheory.Functor.IsEquivalenceOver`: it is fully faithful, commutes with the projections,
and every object of `Coh_{X/Y}` is vertically isomorphic to a transport. -/
theorem nonempty_isEquivalenceOver_isoFunctor (cd : CoherentCategoryData hc D)
    (cd' : CoherentCategoryData hc (isoSituation D f' hf')) :
    letI : Category.{u + 1} (CoherentObject (isoSituation D f' hf')) := cd'.category
    letI : Category.{u + 1} (CoherentObject D) := cd.category
    Nonempty (IsEquivalenceOver (coherentSiteProjection cd')
      (coherentSiteProjection cd) (isoFunctor hf' e he hc hst cd cd')) := by
  let _ : Category.{u + 1} (CoherentObject (isoSituation D f' hf')) := cd'.category
  let _ : Category.{u + 1} (CoherentObject D) := cd.category
  have := isoFunctor_full hf' e he hc hst cd cd'
  have := isoFunctor_faithful hf' e he hc hst cd cd'
  refine nonempty_isEquivalenceOver_of_forall_verticalObjPreimage _ _ _
    (isoFunctor_comp_projection hf' e he hc hst cd cd') fun y => ?_
  let φ : y ⟶ (isoFunctor hf' e he hc hst cd cd').obj (isoPreimage hf' e he hst y) :=
    (Equiv.cast (cd.hom_type _ _)).symm (isoPreimageHom hf' e he hc hst y)
  have hφ : (coherentSiteProjection cd).map φ = 𝟙 _ := by
    show ((Equiv.cast (cd.hom_type _ _)) ((Equiv.cast (cd.hom_type _ _)).symm
      (isoPreimageHom hf' e he hc hst y))).base.left = _
    rw [Equiv.apply_symm_apply]
    rfl
  have hfib : Functor.IsFiberedInGroupoids (coherentSiteProjection cd) := by
    rw [← coherentSiteProjection_eq cd]
    exact coherentProjection_isFiberedInGroupoids' hc cd
  have hvert : (coherentSiteProjection cd).IsHomLift (𝟙 ((coherentSiteProjection cd).obj y)) φ :=
    IsHomLift.of_fac' _ _ _ rfl rfl (by
      rw [hφ]
      simp only [eqToHom_refl, Category.id_comp]
      exact (eqToHom_refl _ _).symm)
  have hiso : IsIso φ := Functor.isIso_of_isHomLift_id' (coherentSiteProjection cd) hfib φ hvert
  refine ⟨isoPreimage hf' e he hst y, rfl, asIso φ, ?_⟩
  show (coherentSiteProjection cd).map φ = _
  rw [hφ]
  rfl

/-- **`Coh_{X'/Y}` and `Coh_{X/Y}` are equivalent over the site.** -/
def isoEquivalenceOver (e : X' ≅ D.X) (he : e.hom ≫ D.f = f') :
    StacksRepresentableCFG.EquivalenceOver (isoSituation D f' hf').coherentCFG.val.p
      D.coherentCFG.val.p :=
  letI : Category.{u + 1} (CoherentObject (isoSituation D f' hf')) :=
    (isoSituation D f' hf').categoryData.category
  letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  StacksRepresentableCFG.EquivalenceOver.ofIsEquivalenceOver
    (nonempty_isEquivalenceOver_isoFunctor hf' e he (modulePushforwardCoherence B S hS)
      (modulePullbackStabilityOfFinitePresentation B S hS) D.categoryData
      (isoSituation D f' hf').categoryData).some

include he in
/-- **Algebraicity of `Coh_{X/Y}` depends on `X` over `Y` only up to isomorphism.** -/
theorem isAlgebraicStack_isoSituation_iff :
    Stack.IsAlgebraicStack.{u, w} B S hS (isoSituation D f' hf').coherentCFG.val ↔
      Stack.IsAlgebraicStack.{u, w} B S hS D.coherentCFG.val :=
  ⟨Stack.isAlgebraicStack_of_equivalenceOver B S hS (isoEquivalenceOver hf' e he),
    Stack.isAlgebraicStack_of_equivalenceOver B S hS (isoEquivalenceOver hf' e he).symm⟩

end CoherentSituation

end AlgebraicGeometry.Space

end
