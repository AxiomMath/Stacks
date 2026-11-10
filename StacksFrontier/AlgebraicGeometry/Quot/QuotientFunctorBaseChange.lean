module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePullbackPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Changing the base algebraic space of the functor of quotients (Stacks 08IT)

In Situation 082M let `B' ⟶ B` be a morphism of algebraic spaces over `S`.  Set
`X' = X ×_B B'` and let `F'` be the pullback of `F` to `X'`.  This is again the standing data
of Stacks 082M, so it has its own set of quotients `Q_{F'/X'/B'}(T)` for every scheme `T`
over `B'`, and Stacks 08IT records that for such a `T`

`Q_{F'/X'/B'}(T) = Q_{F/X/B}(T)`,

the right-hand side reading `T` as a scheme over `B` through `T ⟶ B' ⟶ B`, with the same
remark for the finite-presentation subfunctor `Q^{fp}`.

The two sides of that equation are sets of subobjects of two *different* modules — `F'_T` on
`X'_T = X' ×_{B'} T` and `F_T` on `X_T = X ×_B T` — because `X'_T` and `X_T` are two models of
one fibre product rather than one object.  What is proved here is therefore that the canonical
identification of those two models carries one set onto the other, bijectively and with the
quotients matched.

## Main definitions

* `AlgebraicGeometry.Space.IsFlatOverInvariantUnderPullbackIso` and
  `AlgebraicGeometry.Space.IsFinitePresentationOnSiteInvariantUnderPullbackIso`: invariance of
  flatness over a test object and of finite presentation under the inverse image along an
  isomorphism of algebraic spaces.
* `AlgebraicGeometry.Space.QuotientSituation.baseChangedSource`,
  `AlgebraicGeometry.Space.QuotientSituation.baseChangedSourceProjection` and
  `AlgebraicGeometry.Space.QuotientSituation.baseChangedMorphism`: the space `X' = X ×_B B'`,
  the projection `X' ⟶ X` along which `F` is pulled back, and the structure morphism
  `X' ⟶ B'`.
* `AlgebraicGeometry.Space.QuotientSituation.baseChangedSituation`: **Stacks 08IT**, the
  standing data of `F'/X'/B'`.
* `AlgebraicGeometry.Space.QuotientSituation.baseChangeFiberIso`: the pasted-pullback
  identification `X'_T ≅ X_T`.
* `AlgebraicGeometry.Space.QuotientSituation.baseChangeModuleIso`: under it, `F'_T` is the
  inverse image of `F_T`.
* `AlgebraicGeometry.Space.QuotientSituation.baseChangeSubobjectEquiv`: the induced bijection
  of the two lattices of subobjects, i.e. of the two sets of quotients before the conditions
  of Stacks 082M are imposed.
* `CategoryTheory.Subobject.transportEquiv`: the subobjects of an object and of its image
  under an equivalence of categories correspond.

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.baseChangeQuotientModuleIso`: the quotient
  `F'_T/K'` named by a subobject `K'` is the inverse image of the quotient `F_T/K` named by the
  corresponding subobject `K`.
* `AlgebraicGeometry.Space.QuotientSituation.mem_quotients_baseChange_iff` and
  `AlgebraicGeometry.Space.QuotientSituation.quotients_baseChange`: **Stacks 08IT**, the
  equality `Q_{F'/X'/B'}(T) = Q_{F/X/B}(T)`, as a membership criterion and as an equality of
  sets under the bijection.
* `AlgebraicGeometry.Space.QuotientSituation.quotientsBaseChangeEquiv`: the same equality read
  as a bijection of the two sets.
* `AlgebraicGeometry.Space.QuotientSituation.mem_finitePresentationQuotients_baseChange_iff`,
  `AlgebraicGeometry.Space.QuotientSituation.finitePresentationQuotients_baseChange` and
  `AlgebraicGeometry.Space.QuotientSituation.finitePresentationQuotientsBaseChangeEquiv`:
  **Stacks 08IT**, the source's "similar remarks apply to `Q^{fp}`".
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_iso_iff`,
  `AlgebraicGeometry.Space.isFlatOver_modulePullback_iso_iff` and
  `AlgebraicGeometry.Space.isFinitePresentationOnSite_modulePullback_iso_iff`: quasi-coherence,
  flatness over a test object and finite presentation are invariant under the inverse image
  along an isomorphism of algebraic spaces.
* `AlgebraicGeometry.Space.QuotientSituation.quotients_canonicalBaseChange` and
  `AlgebraicGeometry.Space.QuotientSituation.finitePresentationQuotients_canonicalBaseChange`:
  **Stacks 08IT** for the canonical base-changed situation
  `AlgebraicGeometry.Space.QuotientSituation.canonicalBaseChangedSituation`, with no hypotheses.

## Implementation notes

The inverse image along the identification `X'_T ≅ X_T` is an equivalence of the two categories
of modules by the pseudofunctoriality `AlgebraicGeometry.Space.ModulePushforwardCoherence` of the
direct images of Stacks 03LU, and this equivalence carries subobjects to subobjects and quotients
to quotients.  The first group of declarations takes such a datum `hc`, the quasi-coherence `hF`
of `F'` and the two transport predicates as arguments; the `canonical` declarations specialize
them to `AlgebraicGeometry.Space.modulePushforwardCoherence`, Stacks 03GA,
`AlgebraicGeometry.Space.isFlatOver_modulePullback_iso_iff` and
`AlgebraicGeometry.Space.isFinitePresentationOnSite_modulePullback_iso_iff`.

The statements are pointwise in the test scheme `T`, as in the source.

## References

* [Stacks Project, Tag 08IT](https://stacks.math.columbia.edu/tag/08IT)
* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 08JW](https://stacks.math.columbia.edu/tag/08JW)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- The `𝒪_{X_T}`-modules here have their sections in the universe `u` of the schemes, which the
-- ambient-universe abelian structure `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` cannot
-- describe; left in place it is selected ahead of `SheafOfModules.instAbelian` and leaves the
-- module universe of every subobject and cokernel below unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-! ### Transporting subobjects and their quotients across an equivalence -/

namespace CategoryTheory.Subobject

universe v₁ v₂ w₁ w₂

variable {C : Type w₁} [Category.{v₁} C] {D : Type w₂} [Category.{v₂} D]

/-- An equivalence between two lattices of subobjects is a bijection of their underlying
types: a lattice of subobjects is partially ordered, so two of its objects joined by an
isomorphism are equal. -/
def equivOfLatticeEquivalence {X : C} {Y : D} (E : Subobject X ≌ Subobject Y) :
    Subobject X ≃ Subobject Y where
  toFun := E.functor.obj
  invFun := E.inverse.obj
  left_inv K := le_antisymm (leOfHom (E.unitIso.inv.app K)) (leOfHom (E.unitIso.hom.app K))
  right_inv L := le_antisymm (leOfHom (E.counitIso.hom.app L)) (leOfHom (E.counitIso.inv.app L))

/-- An equivalence of categories identifies the subobjects of an object with the subobjects of
its image. -/
def congrEquiv (E : C ≌ D) (X : C) : Subobject X ≃ Subobject (E.functor.obj X) :=
  equivOfLatticeEquivalence (lowerEquivalence (MonoOver.congr X E))

/-- `congrEquiv E X` sends the subobject `mk f` to `mk (E.functor.map f)`. -/
@[simp]
theorem congrEquiv_mk (E : C ≌ D) {X Z : C} (f : Z ⟶ X) [Mono f] :
    congrEquiv E X (mk f) = mk (E.functor.map f) := rfl

/-- **The subobjects of `X` and of `Y` correspond** when `Y` is identified with the image of
`X` under an equivalence of categories: the equivalence carries a subobject of `X` to one of
its image, and the identification carries that to a subobject of `Y`. -/
def transportEquiv (E : C ≌ D) {X : C} {Y : D} (ι : E.functor.obj X ≅ Y) :
    Subobject X ≃ Subobject Y :=
  (congrEquiv E X).trans (mapIsoToOrderIso ι).toEquiv

/-- `transportEquiv E ι` sends the subobject `mk f` to `mk (E.functor.map f ≫ ι.hom)`. -/
@[simp]
theorem transportEquiv_mk (E : C ≌ D) {X : C} {Y : D} (ι : E.functor.obj X ≅ Y) {Z : C}
    (f : Z ⟶ X) [Mono f] :
    transportEquiv E ι (mk f) = mk (E.functor.map f ≫ ι.hom) := by
  rw [transportEquiv, Equiv.trans_apply, congrEquiv_mk]
  exact map_mk _ _

/-- The transported subobject, written with `CategoryTheory.Subobject.mk`. -/
theorem transportEquiv_eq_mk (E : C ≌ D) {X : C} {Y : D} (ι : E.functor.obj X ≅ Y)
    (K : Subobject X) :
    transportEquiv E ι K = mk (E.functor.map K.arrow ≫ ι.hom) := by
  rw [← transportEquiv_mk, mk_arrow]

variable [Abelian C] [Abelian D]

/-- The quotient by a subobject presented as `CategoryTheory.Subobject.mk` is the cokernel of
the presenting monomorphism itself. -/
def cokernelMkArrowIso {X Z : C} (f : Z ⟶ X) [Mono f] :
    cokernel (mk f).arrow ≅ cokernel f :=
  cokernelIsoOfEq (underlyingIso_hom_comp_eq_mk f).symm ≪≫
    cokernelEpiComp (underlyingIso f).hom f

/-- **The quotients by corresponding subobjects correspond.**  The quotient of `Y` by the
transport of a subobject `K` of `X` is the image under the equivalence of the quotient of `X`
by `K`. -/
def cokernelTransportEquivIso (E : C ≌ D) {X : C} {Y : D} (ι : E.functor.obj X ≅ Y)
    (K : Subobject X) :
    cokernel (transportEquiv E ι K).arrow ≅ E.functor.obj (cokernel K.arrow) :=
  eqToIso (congrArg (fun L : Subobject Y ↦ cokernel L.arrow)
      (transportEquiv_eq_mk E ι K)) ≪≫
    cokernelMkArrowIso _ ≪≫ cokernelCompIsIso (E.functor.map K.arrow) ι.hom ≪≫
    (PreservesCokernel.iso E.functor K.arrow).symm

end CategoryTheory.Subobject

namespace AlgebraicGeometry.Space

universe u

/-! ### Transport along an isomorphism of algebraic spaces -/

/-- Flatness over a test object in the chartwise sense of Stacks 05VV is invariant under the
inverse image along an isomorphism `e : X' ≅ X` of algebraic spaces over that test object: a
module `M` on `X` is flat over `Z` relative to `g` exactly when a module on `X'` isomorphic to
the inverse image of `M` along `e` is flat over `Z` relative to `e ≫ g`. -/
def IsFlatOverInvariantUnderPullbackIso (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : Prop :=
  ∀ {X X' Z : AlgebraicSpaces B S hS} (e : X' ≅ X) (g : X ⟶ Z) (g' : X' ⟶ Z),
    e.hom ≫ g = g' →
      ∀ (M : Modules.{u, u} B S hS X.1 X.2) (N : Modules.{u, u} B S hS X'.1 X'.2),
        (N ≅ (modulePullback B S hS e.hom).obj M) →
          (IsFlatOver B S hS X'.2 g'.hom N ↔ IsFlatOver B S hS X.2 g.hom M)

/-- Finite presentation on the small étale site is invariant under the inverse image along an
isomorphism of algebraic spaces: a module `M` on `X` is of finite presentation exactly when a
module on `X'` isomorphic to the inverse image of `M` along `e : X' ≅ X` is. -/
def IsFinitePresentationOnSiteInvariantUnderPullbackIso (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : Prop :=
  ∀ {X X' : AlgebraicSpaces B S hS} (e : X' ≅ X)
    (M : Modules.{u, u} B S hS X.1 X.2) (N : Modules.{u, u} B S hS X'.1 X'.2),
    (N ≅ (modulePullback B S hS e.hom).obj M) →
      (N.IsFinitePresentationOnSite ↔ M.IsFinitePresentationOnSite)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site over `S`
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_QuotientFunctorBaseChange :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Shortcut for pullbacks of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_QuotientFunctorBaseChange
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Quasi-coherence along an isomorphism -/

/-- **Quasi-coherence is invariant under the inverse image along an isomorphism of algebraic
spaces.**  An isomorphism is étale, so Stacks 03GA along an étale morphism applies to it and to
its inverse with no further input, and the inverse image along the inverse undoes the inverse
image along the isomorphism up to the unit of the induced equivalence. -/
theorem isQuasicoherentOnSite_modulePullback_iso_iff (hc : ModulePushforwardCoherence B S hS)
    {X X' : AlgebraicSpaces B S hS} (e : X' ≅ X) (M : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePullback B S hS e.hom).obj M).IsQuasicoherentOnSite ↔ M.IsQuasicoherentOnSite := by
  refine ⟨fun h ↦ ?_, fun h ↦ isQuasicoherentOnSite_modulePullback_of_isEtale B S hS e.hom
    (isEtale_of_isIso B S hS e.hom.hom) M h⟩
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((hc.modulePullbackEquivalence e).unitIso.app M).symm ?_
  exact isQuasicoherentOnSite_modulePullback_of_isEtale B S hS e.inv
    (isEtale_of_isIso B S hS e.inv.hom) _ h

/-- **Flatness over a test object is invariant under the inverse image along an isomorphism of
algebraic spaces.**  An isomorphism `e : X' ≅ X` is surjective on points
(`AlgebraicGeometry.Space.isSurjective_of_isIso`) and flat, being étale
(`AlgebraicGeometry.Space.isEtale_of_isIso`, `AlgebraicGeometry.Space.isFlat_of_isEtale`), so
Stacks 05VY compares a quasi-coherent module `M` on `X`, flat over `Z` relative to `g`, with
its inverse image on `X'`, flat over `Z` relative to `e.hom ≫ g`. -/
theorem isFlatOver_modulePullback_iso_iff {X X' Z : AlgebraicSpaces B S hS} (e : X' ≅ X)
    (g : X ⟶ Z) (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) :
    IsFlatOver B S hS X'.2 (e.hom ≫ g).hom ((modulePullback B S hS e.hom).obj M) ↔
      IsFlatOver B S hS X.2 g.hom M := by
  have := hM
  exact (isFlatOver_modulePullback_iff_of_isSurjective_of_isFlat B S hS e.hom g M
    (isSurjective_of_isIso B S hS e.hom.hom)
    (isFlat_of_isEtale B S hS (isEtale_of_isIso B S hS e.hom.hom))).symm

/-- **Finite presentation on the small étale site is invariant under the inverse image along an
isomorphism of algebraic spaces.**  The inverse image of a module of finite presentation along
an arbitrary morphism is of finite presentation,
`AlgebraicGeometry.Space.isFinitePresentationOnSite_modulePullback`; applying that to the
inverse of the isomorphism and undoing the round trip with the unit of the induced equivalence
gives the other direction. -/
theorem isFinitePresentationOnSite_modulePullback_iso_iff {X X' : AlgebraicSpaces B S hS}
    (e : X' ≅ X) (M : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePullback B S hS e.hom).obj M).IsFinitePresentationOnSite ↔
      M.IsFinitePresentationOnSite := by
  refine ⟨fun h ↦ ?_, fun h ↦ isFinitePresentationOnSite_modulePullback B S hS e.hom M h⟩
  refine SheafOfModules.IsFinitePresentationOnSite.of_iso
    (((modulePushforwardCoherence B S hS).modulePullbackEquivalence e).unitIso.app M).symm ?_
  exact isFinitePresentationOnSite_modulePullback B S hS e.inv _ h

namespace QuotientSituation

/-- A set `Q` is the image of `P` under a bijection `e` once `e` matches membership. -/
private theorem eq_image_equiv_of_mem_iff {α β : Type*} (e : α ≃ β) {P : Set α} {Q : Set β}
    (h : ∀ K, e K ∈ Q ↔ K ∈ P) : Q = e '' P := by
  ext L
  rw [Set.mem_image_equiv, ← h, Equiv.apply_symm_apply]

/-- Quasi-coherence of a module `N ≅ P`, with `P ↔ M` quasi-coherent, is invisible in a
conjunction whose other conjunct is only compared for quasi-coherent `M`. -/
private theorem isQuasicoherentOnSite_and_congr {X X' : AlgebraicSpaces B S hS}
    {N P : Modules.{u, u} B S hS X'.1 X'.2} {M : Modules.{u, u} B S hS X.1 X.2} (i : N ≅ P)
    (hqc : P.IsQuasicoherentOnSite ↔ M.IsQuasicoherentOnSite) {a b : Prop}
    (h : M.IsQuasicoherentOnSite → (a ↔ b)) :
    N.IsQuasicoherentOnSite ∧ a ↔ M.IsQuasicoherentOnSite ∧ b := by
  have hN : N.IsQuasicoherentOnSite ↔ M.IsQuasicoherentOnSite :=
    ⟨fun h ↦ hqc.1 (SheafOfModules.IsQuasicoherentOnSite.of_iso i h),
      fun h ↦ SheafOfModules.IsQuasicoherentOnSite.of_iso i.symm (hqc.2 h)⟩
  exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨hN.1 h₁, (h (hN.1 h₁)).1 h₂⟩,
    fun ⟨h₁, h₂⟩ ↦ ⟨hN.2 h₁, (h h₁).2 h₂⟩⟩

variable (D : QuotientSituation B S hS) {Y' : AlgebraicSpaces B S hS} (p : Y' ⟶ D.Y)

/-! ### The base-changed situation -/

/-- The source `X' = X ×_B B'` of the base-changed situation of Stacks 08IT. -/
abbrev baseChangedSource : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS D.f p

/-- The projection `X' ⟶ X`, along which the module is pulled back. -/
def baseChangedSourceProjection : D.baseChangedSource p ⟶ D.X :=
  ObjectProperty.homMk (pullback.fst D.f.hom p.hom)

/-- The structure morphism `f' : X' ⟶ B'` of the base-changed situation. -/
def baseChangedMorphism : D.baseChangedSource p ⟶ Y' :=
  ObjectProperty.homMk (pullback.snd D.f.hom p.hom)

/-- The module `F'`, the pullback of `F` to `X' = X ×_B B'`. -/
abbrev baseChangedSourceModule :
    Modules.{u, u} B S hS (D.baseChangedSource p).1 (D.baseChangedSource p).2 :=
  (modulePullback B S hS (D.baseChangedSourceProjection p)).obj D.F

/-- **Stacks 08IT.**  The standing data of Stacks 082M obtained by changing the base algebraic
space along `p : B' ⟶ B`: its source is `X' = X ×_B B'`, its morphism the second projection,
and its module the pullback `F'` of `F` along the first projection.  Its functor of quotients
is the `Q_{F'/X'/B'}` of the source.  It takes the quasi-coherence `hF` of `F'` as an
argument. -/
def baseChangedSituation (hF : (D.baseChangedSourceModule p).IsQuasicoherentOnSite) :
    QuotientSituation B S hS where
  X := D.baseChangedSource p
  Y := Y'
  f := D.baseChangedMorphism p
  F := D.baseChangedSourceModule p
  quasicoherent := hF

variable (hF : (D.baseChangedSourceModule p).IsQuasicoherentOnSite)

/-! ### The identification of the two base changes -/

/-- The pasted-pullback identification `X'_T ≅ X_T` of the base change of `X'` along a test
scheme `T` over `B'` with the base change of `X` along the same scheme, read over `B`. -/
def baseChangeFiberIso (T : SchemesOver Y') :
    (D.baseChangedSituation p hF).space T ≅ D.space ((CostructuredArrow.map p).obj T) :=
  ObjectProperty.isoMk _ (pullbackLeftPullbackSndIso D.f.hom p.hom T.hom.hom)

/-- The identification `X'_T ≅ X_T` commutes with the projections `X_T ⟶ X` to the source of the
morphism, `AlgebraicGeometry.Space.QuotientSituation.sourceProjection`: it is a morphism
over `X`. -/
@[reassoc (attr := simp)]
theorem baseChangeFiberIso_hom_comp_sourceProjection (T : SchemesOver Y') :
    (D.baseChangeFiberIso p hF T).hom ≫ D.sourceProjection ((CostructuredArrow.map p).obj T) =
      (D.baseChangedSituation p hF).sourceProjection T ≫ D.baseChangedSourceProjection p := by
  refine ObjectProperty.hom_ext _ ?_
  exact pullbackLeftPullbackSndIso_hom_fst _ _ _

/-- The identification `X'_T ≅ X_T` commutes with the projections `X_T ⟶ T` to the test scheme,
`AlgebraicGeometry.Space.QuotientSituation.projection`. -/
@[reassoc (attr := simp)]
theorem baseChangeFiberIso_hom_comp_projection (T : SchemesOver Y') :
    (D.baseChangeFiberIso p hF T).hom ≫ D.projection ((CostructuredArrow.map p).obj T) =
      (D.baseChangedSituation p hF).projection T := by
  refine ObjectProperty.hom_ext _ ?_
  exact pullbackLeftPullbackSndIso_hom_snd _ _ _

/-- **Under the identification `X'_T ≅ X_T` the module `F'_T` is the inverse image of `F_T`.**
Both are the inverse image of `F` along the two sides of the commuting square of
`AlgebraicGeometry.Space.QuotientSituation.baseChangeFiberIso_hom_comp_sourceProjection`, so
the comparison of Stacks 03LU for that square identifies them. -/
def baseChangeModuleIso (T : SchemesOver Y') :
    (modulePullback B S hS (D.baseChangeFiberIso p hF T).hom).obj
        (D.baseChangeModule ((CostructuredArrow.map p).obj T)) ≅
      (D.baseChangedSituation p hF).baseChangeModule T :=
  (modulePullbackSquare B S hS
    (D.baseChangeFiberIso_hom_comp_sourceProjection p hF T) rfl).app D.F

/-- The equivalence of the two categories of modules induced by the identification
`X'_T ≅ X_T`: by the pseudofunctoriality of Stacks 03LU, the inverse image along an
isomorphism of algebraic spaces is an equivalence. -/
def baseChangeModulesEquivalence (hc : ModulePushforwardCoherence B S hS)
    (T : SchemesOver Y') :
    Modules.{u, u} B S hS (D.space ((CostructuredArrow.map p).obj T)).1
        (D.space ((CostructuredArrow.map p).obj T)).2 ≌
      Modules.{u, u} B S hS ((D.baseChangedSituation p hF).space T).1
        ((D.baseChangedSituation p hF).space T).2 :=
  hc.modulePullbackEquivalence (D.baseChangeFiberIso p hF T)

/-- **The two sets of quotients of Stacks 08IT live on identified lattices.**  The subobjects
of `F_T` and the subobjects of `F'_T` correspond, by the equivalence of the two categories of
modules induced by `X'_T ≅ X_T` followed by the identification of `F'_T` with the inverse image
of `F_T`. -/
def baseChangeSubobjectEquiv (hc : ModulePushforwardCoherence B S hS) (T : SchemesOver Y') :
    Subobject (D.baseChangeModule ((CostructuredArrow.map p).obj T)) ≃
      Subobject ((D.baseChangedSituation p hF).baseChangeModule T) :=
  Subobject.transportEquiv (D.baseChangeModulesEquivalence p hF hc T)
    (D.baseChangeModuleIso p hF T)

/-- **The quotients themselves correspond.**  The quotient `F'_T/K'` named by the subobject
corresponding to `K` is the inverse image along `X'_T ≅ X_T` of the quotient `F_T/K`. -/
def baseChangeQuotientModuleIso (hc : ModulePushforwardCoherence B S hS) (T : SchemesOver Y')
    (K : Subobject (D.baseChangeModule ((CostructuredArrow.map p).obj T))) :
    (D.baseChangedSituation p hF).quotientModule T
        (D.baseChangeSubobjectEquiv p hF hc T K) ≅
      (modulePullback B S hS (D.baseChangeFiberIso p hF T).hom).obj
        (D.quotientModule ((CostructuredArrow.map p).obj T) K) :=
  Subobject.cokernelTransportEquivIso (D.baseChangeModulesEquivalence p hF hc T)
    (D.baseChangeModuleIso p hF T) K

/-! ### The identification of the two sets of quotients -/

/-- **Stacks 08IT.**  For a test scheme `T` over `B'` a subobject of `F'_T` is an element of
`Q_{F'/X'/B'}(T)` exactly when the corresponding subobject of `F_T` is an element of
`Q_{F/X/B}(T)`, where on the right `T` is read as a scheme over `B` through `T ⟶ B' ⟶ B`.
Quasi-coherence moves across the identification because an isomorphism of algebraic spaces is
étale; flatness over `T` moves by the hypothesis `hflat`. -/
theorem mem_quotients_baseChange_iff (hc : ModulePushforwardCoherence B S hS)
    (hflat : IsFlatOverInvariantUnderPullbackIso B S hS) (T : SchemesOver Y')
    (K : Subobject (D.baseChangeModule ((CostructuredArrow.map p).obj T))) :
    D.baseChangeSubobjectEquiv p hF hc T K ∈ (D.baseChangedSituation p hF).quotients T ↔
      K ∈ D.quotients ((CostructuredArrow.map p).obj T) := by
  have hqc := (isQuasicoherentOnSite_modulePullback_iso_iff hc (D.baseChangeFiberIso p hF T)
    (D.quotientModule ((CostructuredArrow.map p).obj T) K))
  exact isQuasicoherentOnSite_and_congr (D.baseChangeQuotientModuleIso p hF hc T K) hqc fun _ ↦
    hflat (D.baseChangeFiberIso p hF T) (D.projection ((CostructuredArrow.map p).obj T))
      ((D.baseChangedSituation p hF).projection T)
      (D.baseChangeFiberIso_hom_comp_projection p hF T) _ _
      (D.baseChangeQuotientModuleIso p hF hc T K)

/-- **Stacks 08IT.**  `Q_{F'/X'/B'}(T) = Q_{F/X/B}(T)`: the canonical bijection of the two
lattices of subobjects carries the set of quotients of Stacks 082M for `F/X/B` at `T`, read as
a scheme over `B`, onto the one for `F'/X'/B'` at `T`, read as a scheme over `B'`. -/
theorem quotients_baseChange (hc : ModulePushforwardCoherence B S hS)
    (hflat : IsFlatOverInvariantUnderPullbackIso B S hS) (T : SchemesOver Y') :
    (D.baseChangedSituation p hF).quotients T =
      D.baseChangeSubobjectEquiv p hF hc T ''
        D.quotients ((CostructuredArrow.map p).obj T) := by
  exact eq_image_equiv_of_mem_iff _ (D.mem_quotients_baseChange_iff p hF hc hflat T)

/-- **Stacks 08IT.**  The equality `Q_{F'/X'/B'}(T) = Q_{F/X/B}(T)` read as a bijection of the
two sets. -/
def quotientsBaseChangeEquiv (hc : ModulePushforwardCoherence B S hS)
    (hflat : IsFlatOverInvariantUnderPullbackIso B S hS) (T : SchemesOver Y') :
    D.quotients ((CostructuredArrow.map p).obj T) ≃
      (D.baseChangedSituation p hF).quotients T :=
  (D.baseChangeSubobjectEquiv p hF hc T).subtypeEquiv fun K ↦
    (D.mem_quotients_baseChange_iff p hF hc hflat T K).symm

/-! ### The finite-presentation subfunctor -/

/-- **Stacks 08IT**, the source's "similar remarks apply to `Q^{fp}`", in membership form: a
subobject of `F'_T` is an element of `Q^{fp}_{F'/X'/B'}(T)` exactly when the corresponding
subobject of `F_T` is an element of `Q^{fp}_{F/X/B}(T)`. -/
theorem mem_finitePresentationQuotients_baseChange_iff (hc : ModulePushforwardCoherence B S hS)
    (hflat : IsFlatOverInvariantUnderPullbackIso B S hS)
    (hfp : IsFinitePresentationOnSiteInvariantUnderPullbackIso B S hS) (T : SchemesOver Y')
    (K : Subobject (D.baseChangeModule ((CostructuredArrow.map p).obj T))) :
    D.baseChangeSubobjectEquiv p hF hc T K ∈
        (D.baseChangedSituation p hF).finitePresentationQuotients T ↔
      K ∈ D.finitePresentationQuotients ((CostructuredArrow.map p).obj T) := by
  exact and_congr (D.mem_quotients_baseChange_iff p hF hc hflat T K)
    (hfp (D.baseChangeFiberIso p hF T) _ _ (D.baseChangeQuotientModuleIso p hF hc T K))

/-- **Stacks 08IT**, the source's "similar remarks apply to `Q^{fp}`":
`Q^{fp}_{F'/X'/B'}(T) = Q^{fp}_{F/X/B}(T)` under the canonical bijection of the two lattices of
subobjects. -/
theorem finitePresentationQuotients_baseChange (hc : ModulePushforwardCoherence B S hS)
    (hflat : IsFlatOverInvariantUnderPullbackIso B S hS)
    (hfp : IsFinitePresentationOnSiteInvariantUnderPullbackIso B S hS) (T : SchemesOver Y') :
    (D.baseChangedSituation p hF).finitePresentationQuotients T =
      D.baseChangeSubobjectEquiv p hF hc T ''
        D.finitePresentationQuotients ((CostructuredArrow.map p).obj T) := by
  exact eq_image_equiv_of_mem_iff _
    (D.mem_finitePresentationQuotients_baseChange_iff p hF hc hflat hfp T)

/-- **Stacks 08IT.**  The equality `Q^{fp}_{F'/X'/B'}(T) = Q^{fp}_{F/X/B}(T)` read as a
bijection of the two sets. -/
def finitePresentationQuotientsBaseChangeEquiv (hc : ModulePushforwardCoherence B S hS)
    (hflat : IsFlatOverInvariantUnderPullbackIso B S hS)
    (hfp : IsFinitePresentationOnSiteInvariantUnderPullbackIso B S hS) (T : SchemesOver Y') :
    D.finitePresentationQuotients ((CostructuredArrow.map p).obj T) ≃
      (D.baseChangedSituation p hF).finitePresentationQuotients T :=
  (D.baseChangeSubobjectEquiv p hF hc T).subtypeEquiv fun K ↦
    (D.mem_finitePresentationQuotients_baseChange_iff p hF hc hflat hfp T K).symm

/-! ### The identification at the canonical data

Here `hF` is Stacks 03GA, `hc` is `AlgebraicGeometry.Space.modulePushforwardCoherence`, and the
two transports are `AlgebraicGeometry.Space.isFlatOver_modulePullback_iso_iff` (Stacks 05VY, for
a quasi-coherent module) and
`AlgebraicGeometry.Space.isFinitePresentationOnSite_modulePullback_iso_iff`. -/

/-- The pullback `F'` of `F` to `X' = X ×_B B'` is quasi-coherent, by Stacks 03GA. -/
theorem isQuasicoherentOnSite_baseChangedSourceModule :
    (D.baseChangedSourceModule p).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (D.baseChangedSourceProjection p) D.F D.quasicoherent

/-- The standing data of Stacks 082M obtained by changing the base algebraic space along
`p : B' ⟶ B`: source `X' = X ×_B B'`, morphism the second projection, module the pullback `F'` of
`F`, quasi-coherent by Stacks 03GA. -/
@[stacks 08IT "the base-changed situation F'/X'/B'"]
abbrev canonicalBaseChangedSituation : QuotientSituation B S hS :=
  D.baseChangedSituation p (D.isQuasicoherentOnSite_baseChangedSourceModule p)

/-- **The quotients themselves correspond**, at the canonical pseudofunctoriality datum: the
quotient `F'_T/K'` named by the subobject corresponding to `K` is the inverse image along
`X'_T ≅ X_T` of the quotient `F_T/K`. -/
@[stacks 08IT "the identification of the quotients themselves, F'_T/K' = F_T/K under \
X'_T ≅ X_T"]
def canonicalBaseChangeQuotientModuleIso (T : SchemesOver Y')
    (K : Subobject (D.baseChangeModule ((CostructuredArrow.map p).obj T))) :
    (D.canonicalBaseChangedSituation p).quotientModule T
        (D.baseChangeSubobjectEquiv p (D.isQuasicoherentOnSite_baseChangedSourceModule p)
          (modulePushforwardCoherence B S hS) T K) ≅
      (modulePullback B S hS
          (D.baseChangeFiberIso p (D.isQuasicoherentOnSite_baseChangedSourceModule p) T).hom).obj
        (D.quotientModule ((CostructuredArrow.map p).obj T) K) :=
  D.baseChangeQuotientModuleIso p _ (modulePushforwardCoherence B S hS) T K

/-- **Flatness over the test scheme moves across the identification `X'_T ≅ X_T`.**  The
quotient `F'_T/K'` is flat over `T` exactly when `F_T/K` is, for `F_T/K` quasi-coherent, by
`AlgebraicGeometry.Space.isFlatOver_modulePullback_iso_iff` applied to the commuting triangle of
`AlgebraicGeometry.Space.QuotientSituation.baseChangeFiberIso_hom_comp_projection`. -/
theorem isFlatOver_quotientModule_baseChange_iff (T : SchemesOver Y')
    (K : Subobject (D.baseChangeModule ((CostructuredArrow.map p).obj T)))
    (hK : (D.quotientModule ((CostructuredArrow.map p).obj T) K).IsQuasicoherentOnSite) :
    IsFlatOver B S hS ((D.canonicalBaseChangedSituation p).space T).2
        ((D.canonicalBaseChangedSituation p).projection T).hom
        ((D.canonicalBaseChangedSituation p).quotientModule T
          (D.baseChangeSubobjectEquiv p (D.isQuasicoherentOnSite_baseChangedSourceModule p)
            (modulePushforwardCoherence B S hS) T K)) ↔
      IsFlatOver B S hS (D.space ((CostructuredArrow.map p).obj T)).2
        (D.projection ((CostructuredArrow.map p).obj T)).hom
        (D.quotientModule ((CostructuredArrow.map p).obj T) K) := by
  rw [isFlatOver_iff_of_iso B S hS _ _ (D.canonicalBaseChangeQuotientModuleIso p T K),
    ← D.baseChangeFiberIso_hom_comp_projection p
      (D.isQuasicoherentOnSite_baseChangedSourceModule p) T]
  exact isFlatOver_modulePullback_iso_iff
    (D.baseChangeFiberIso p (D.isQuasicoherentOnSite_baseChangedSourceModule p) T)
    (D.projection ((CostructuredArrow.map p).obj T))
    (D.quotientModule ((CostructuredArrow.map p).obj T) K) hK

/-- For a test scheme `T` over `B'` a subobject of `F'_T` is an element of `Q_{F'/X'/B'}(T)`
exactly when the corresponding subobject of `F_T` is an element of `Q_{F/X/B}(T)`, where on the
right `T` is read as a scheme over `B` through `T ⟶ B' ⟶ B`. -/
@[stacks 08IT "the identification Q(F'/X'/B')(T) = Q(F/X/B)(T), in membership form"]
theorem mem_quotients_canonicalBaseChange_iff (T : SchemesOver Y')
    (K : Subobject (D.baseChangeModule ((CostructuredArrow.map p).obj T))) :
    D.baseChangeSubobjectEquiv p (D.isQuasicoherentOnSite_baseChangedSourceModule p)
        (modulePushforwardCoherence B S hS) T K ∈
        (D.canonicalBaseChangedSituation p).quotients T ↔
      K ∈ D.quotients ((CostructuredArrow.map p).obj T) := by
  have hqc := isQuasicoherentOnSite_modulePullback_iso_iff (modulePushforwardCoherence B S hS)
    (D.baseChangeFiberIso p (D.isQuasicoherentOnSite_baseChangedSourceModule p) T)
    (D.quotientModule ((CostructuredArrow.map p).obj T) K)
  exact isQuasicoherentOnSite_and_congr (D.canonicalBaseChangeQuotientModuleIso p T K) hqc
    (D.isFlatOver_quotientModule_baseChange_iff p T K)

/-- `Q_{F'/X'/B'}(T) = Q_{F/X/B}(T)`: the canonical bijection of the two lattices of subobjects
carries the set of quotients of Stacks 082M for `F/X/B` at `T`, read as a scheme over `B`, onto the
one for `F'/X'/B'` at `T`, read as a scheme over `B'`. -/
@[stacks 08IT "the identification Q(F'/X'/B')(T) = Q(F/X/B)(T)"]
theorem quotients_canonicalBaseChange (T : SchemesOver Y') :
    (D.canonicalBaseChangedSituation p).quotients T =
      D.baseChangeSubobjectEquiv p (D.isQuasicoherentOnSite_baseChangedSourceModule p)
          (modulePushforwardCoherence B S hS) T ''
        D.quotients ((CostructuredArrow.map p).obj T) := by
  exact eq_image_equiv_of_mem_iff _ (D.mem_quotients_canonicalBaseChange_iff p T)

/-- The equality `Q_{F'/X'/B'}(T) = Q_{F/X/B}(T)` read as a bijection of the two sets. -/
@[stacks 08IT "the bijection Q(F'/X'/B')(T) ≃ Q(F/X/B)(T)"]
def quotientsCanonicalBaseChangeEquiv (T : SchemesOver Y') :
    D.quotients ((CostructuredArrow.map p).obj T) ≃
      (D.canonicalBaseChangedSituation p).quotients T :=
  (D.baseChangeSubobjectEquiv p (D.isQuasicoherentOnSite_baseChangedSourceModule p)
      (modulePushforwardCoherence B S hS) T).subtypeEquiv fun K ↦
    (D.mem_quotients_canonicalBaseChange_iff p T K).symm

/-- The same identification for `Q^{fp}`, in membership form: a subobject of `F'_T` is an element
of `Q^{fp}_{F'/X'/B'}(T)` exactly when the corresponding subobject of `F_T` is an element of
`Q^{fp}_{F/X/B}(T)`. -/
@[stacks 08IT "the same identification for the finite-presentation subfunctor, in membership \
form"]
theorem mem_finitePresentationQuotients_canonicalBaseChange_iff (T : SchemesOver Y')
    (K : Subobject (D.baseChangeModule ((CostructuredArrow.map p).obj T))) :
    D.baseChangeSubobjectEquiv p (D.isQuasicoherentOnSite_baseChangedSourceModule p)
        (modulePushforwardCoherence B S hS) T K ∈
        (D.canonicalBaseChangedSituation p).finitePresentationQuotients T ↔
      K ∈ D.finitePresentationQuotients ((CostructuredArrow.map p).obj T) := by
  have hq := D.mem_quotients_canonicalBaseChange_iff p T K
  have hfpK := isFinitePresentationOnSite_modulePullback_iso_iff
    (D.baseChangeFiberIso p (D.isQuasicoherentOnSite_baseChangedSourceModule p) T)
    (D.quotientModule ((CostructuredArrow.map p).obj T) K)
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨hq.1 h₁, hfpK.1 (SheafOfModules.IsFinitePresentationOnSite.of_iso
      (D.canonicalBaseChangeQuotientModuleIso p T K) h₂)⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨hq.2 h₁, SheafOfModules.IsFinitePresentationOnSite.of_iso
      (D.canonicalBaseChangeQuotientModuleIso p T K).symm (hfpK.2 h₂)⟩

/-- The same identification for `Q^{fp}`: `Q^{fp}_{F'/X'/B'}(T) = Q^{fp}_{F/X/B}(T)` under the
canonical bijection of the two lattices of subobjects. -/
@[stacks 08IT "the same identification for the finite-presentation subfunctor"]
theorem finitePresentationQuotients_canonicalBaseChange (T : SchemesOver Y') :
    (D.canonicalBaseChangedSituation p).finitePresentationQuotients T =
      D.baseChangeSubobjectEquiv p (D.isQuasicoherentOnSite_baseChangedSourceModule p)
          (modulePushforwardCoherence B S hS) T ''
        D.finitePresentationQuotients ((CostructuredArrow.map p).obj T) := by
  exact eq_image_equiv_of_mem_iff _
    (D.mem_finitePresentationQuotients_canonicalBaseChange_iff p T)

/-- The equality `Q^{fp}_{F'/X'/B'}(T) = Q^{fp}_{F/X/B}(T)` read as a bijection of the two sets. -/
@[stacks 08IT "the bijection for the finite-presentation subfunctor"]
def finitePresentationQuotientsCanonicalBaseChangeEquiv (T : SchemesOver Y') :
    D.finitePresentationQuotients ((CostructuredArrow.map p).obj T) ≃
      (D.canonicalBaseChangedSituation p).finitePresentationQuotients T :=
  (D.baseChangeSubobjectEquiv p (D.isQuasicoherentOnSite_baseChangedSourceModule p)
      (modulePushforwardCoherence B S hS) T).subtypeEquiv fun K ↦
    (D.mem_finitePresentationQuotients_canonicalBaseChange_iff p T K).symm

end QuotientSituation

end AlgebraicGeometry.Space

end
