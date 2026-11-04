module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Functor.Flat
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteOverSmoothFactorization
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Pullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentSite
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# Transporting the data of a dévissage

This file collects the comparisons used to move the data of a one-step dévissage, and of a
stage of a complete dévissage, along an isomorphism of the source and along a cartesian
square: the inverse image of a free module, the invariance of the support of a module under
an isomorphism, the comparison of the fibres of the two vertical morphisms of a cartesian
square, the behaviour of generic points under continuous surjections and open embeddings, and
the dévissage data carried along an isomorphism of the source over the base.

It also carries a whole complete dévissage along an isomorphism of the source over the base and
along an isomorphism of the base matching the base points. The first of the two leaves every
stage but the first untouched, because a later stage dévisses a cokernel on the smooth scheme of
its predecessor, which the transport does not move; the second changes every stage, since the
structure morphism of each smooth scheme is composed with the inverse of the isomorphism, and is
therefore a recursion down the chain.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pullbackFreeIso`: the inverse image of the free module on
  `I` is the free module on `I`.
* `AlgebraicGeometry.fiberMapOfIsPullback`: for a cartesian square with vertical morphisms
  `g'` and `g` and lower horizontal morphism `h`, the morphism `g'.fiber s' ⟶ g.fiber (h s')`
  of scheme-theoretic fibres.
* `AlgebraicGeometry.Scheme.Modules.pushforwardInvIsoPullback`: the direct image along the
  inverse of an isomorphism is the inverse image along the isomorphism.
* `AlgebraicGeometry.fiberIsoOfSourceIso` and
  `AlgebraicGeometry.fiberSupportHomeoOfSourceIso`: the fibres, and the supports of the
  modules on them, carried along an isomorphism of the source over the base.
* `AlgebraicGeometry.OneStepDevissage.ofSourceIso`,
  `AlgebraicGeometry.OneStepDevissageAt.ofSourceIso` and
  `AlgebraicGeometry.DevissageStage.ofSourceIso`: a one-step dévissage, a one-step dévissage
  at a point, and a stage of a complete dévissage, carried along an isomorphism of the source
  over the base.
* `AlgebraicGeometry.OneStepDevissageAt.ofModuleIso` and
  `AlgebraicGeometry.OneStepDevissageAt.ofClosedModuleIso`: a one-step dévissage at a point
  carried along an isomorphism of the module being dévissed, and along an isomorphism of the
  module on the closed subscheme.
* `AlgebraicGeometry.OneStepDevissage.ofModuleIso` and
  `AlgebraicGeometry.DevissageStage.ofModuleIso`: a one-step dévissage and a stage of a complete
  dévissage, carried along an isomorphism of the module being dévissed.
* `AlgebraicGeometry.DevissageChain.ofSourceIso`,
  `AlgebraicGeometry.PointedDevissageStage.ofSourceIso`,
  `AlgebraicGeometry.PointedDevissageChain.ofSourceIso`,
  `AlgebraicGeometry.NonemptyCompleteDevissage.ofSourceIso`,
  `AlgebraicGeometry.NonemptyCompleteDevissageAt.ofSourceIso` and
  `AlgebraicGeometry.CompleteDevissageAt.ofSourceIso`: a whole complete dévissage carried along
  an isomorphism of the source over the base, and along one matching a chosen point of the new
  source with the point the dévissage is taken at. Only the first stage of the chain changes,
  since every later stage dévisses a cokernel on the smooth scheme, which the transport leaves
  untouched.
* `AlgebraicGeometry.suppPullbackHomeoOfIso`: the supports of the two inverse images of a
  module along two morphisms whose sources are identified over the common target.
* `AlgebraicGeometry.fiberIsoOfBaseIso` and `AlgebraicGeometry.fiberIsoOfBaseIsoPoint`: the
  fibre of a morphism over a point of the base, carried along an isomorphism of the base.
* `AlgebraicGeometry.OneStepDevissage.ofBaseIso`,
  `AlgebraicGeometry.OneStepDevissageAt.ofBaseIso` and
  `AlgebraicGeometry.DevissageStage.ofBaseIso`: a one-step dévissage, a one-step dévissage at a
  point, and a stage of a complete dévissage, carried along an isomorphism of the base.
* `AlgebraicGeometry.DevissageChain.ofBaseIso`,
  `AlgebraicGeometry.NonemptyCompleteDevissage.ofBaseIso`,
  `AlgebraicGeometry.PointedDevissageStage.ofBaseIso`,
  `AlgebraicGeometry.PointedDevissageChain.ofBaseIso`,
  `AlgebraicGeometry.NonemptyCompleteDevissageAt.ofBaseIso` and
  `AlgebraicGeometry.CompleteDevissageAt.ofBaseIso`: a whole complete dévissage carried along
  an isomorphism of the base, with new structure morphism `f ≫ d.inv`.
* `AlgebraicGeometry.DevissageChain.ofBaseIsoHom`,
  `AlgebraicGeometry.NonemptyCompleteDevissage.ofBaseIsoHom`,
  `AlgebraicGeometry.PointedDevissageChain.ofBaseIsoHom`,
  `AlgebraicGeometry.NonemptyCompleteDevissageAt.ofBaseIsoHom` and
  `AlgebraicGeometry.CompleteDevissageAt.ofBaseIsoHom`: the same, with the structure morphism
  over the new base prescribed by any `f' : X ⟶ S'` with `f' ≫ d.hom = f`.
* `AlgebraicGeometry.DevissageChain.ofModuleIso`,
  `AlgebraicGeometry.PointedDevissageChain.ofModuleIso`,
  `AlgebraicGeometry.NonemptyCompleteDevissage.ofModuleIso`,
  `AlgebraicGeometry.NonemptyCompleteDevissageAt.ofModuleIso` and
  `AlgebraicGeometry.CompleteDevissageAt.ofModuleIso`: a whole complete dévissage carried along
  an isomorphism of the module being dévissed. Only the first stage of the chain changes, since
  every later stage dévisses a cokernel which the transport leaves untouched.

## Main results

* `SheafOfModules.mem_supp_iff_of_iso`: a point lies in the support of a module on a scheme
  exactly when it lies in the support of any isomorphic module.
* `SheafOfModules.isFiniteType_of_iso`, `SheafOfModules.isQuasicoherent_of_iso` and
  `Stacks.Modules.isQuasicoherent_pullback`: the two finiteness conditions under isomorphism
  and under inverse image.
* `AlgebraicGeometry.surjective_fiberMapOfIsPullback` and
  `AlgebraicGeometry.fiberMapOfIsPullback_genericPoint`: the comparison of fibres attached to
  a cartesian square is surjective and carries the generic point to the generic point.
* `IsGenericPoint.map_eq_of_surjective` and `IsGenericPoint.map_eq_of_isOpenEmbedding`: a
  continuous surjection, and an open embedding into an irreducible space, carry the generic
  point to the generic point.
* `AlgebraicGeometry.isIso_pullback_map_fromSpecResidueField`: a morphism of modules which
  becomes invertible over the residue field of the image of a point has an inverse image
  which becomes invertible over the residue field of that point.
* `topologicalKrullDimAt_congr`: the local dimension of a subspace at a point depends only on
  the underlying subset.
* `AlgebraicGeometry.supp_pullback_eq_preimage_of_iso`,
  `AlgebraicGeometry.topologicalKrullDim_supp_pullback_of_iso` and
  `AlgebraicGeometry.topologicalKrullDimAt_supp_pullback_of_iso`: the support of the inverse
  image of a module, its dimension and its local dimension depend on the morphism only up to an
  isomorphism of its source over the target.
* `AlgebraicGeometry.DevissageStage.ofSourceIso_coker`: the cokernel of the free-module map of a
  stage is unchanged by the transport along an isomorphism of the source.
* `AlgebraicGeometry.PointedDevissageStage.g_y`: the distinguished point of the smooth scheme of
  a pointed stage lies over the base point of the dévissage.
* `AlgebraicGeometry.topologicalKrullDim_fiber_of_baseIso`,
  `AlgebraicGeometry.topologicalKrullDim_fiberSupport_of_baseIso` and
  `AlgebraicGeometry.topologicalKrullDimAt_fiberSupport_of_baseIso`: the dimension of a fibre,
  the dimension of the support of the module on it and that dimension taken locally at a point
  are unchanged by an isomorphism of the base.
* `AlgebraicGeometry.purelyTranscendental_residueField_of_baseIso`: the pure transcendence of
  the residue field of the distinguished point of the smooth scheme over the residue field of
  the base point survives an isomorphism of the base.
* `AlgebraicGeometry.mem_fiberSupport_iff_mem_fiberSupport`: whether a point lies in the support
  of the module on its fibre does not depend on the morphism to the base.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.pullbackFreeIso` is Mathlib's
`SheafOfModules.pullbackObjFreeIso` for the ring-sheaf morphism induced by a morphism of
schemes; it is given a name because the two instances its Mathlib form requires — the right
adjointness of the direct image and the finality of the inverse-image functor on opens — are
always available for a morphism of schemes, and supplying them at every use obscures the
statements.

The comparison of fibres attached to a cartesian square is the canonical morphism of fibre
products: a fibre is the fibre product with the spectrum of the residue field of the base
point, and the square induces a map of those data. It is surjective because it is, up to the
cartesian square of the fibres over the residue fields, a base change of a morphism between
spectra of fields.

Carrying a one-step dévissage along an isomorphism `e` of the source changes only the closed
immersion, which is composed with `e.inv`; the closed subscheme, the smooth scheme, the
finite and smooth morphisms and the module on the closed subscheme are unchanged, and the
projections of the construction are therefore definitional. The identification of the module
is composed with the affine base-change isomorphism of the square exhibiting `e` as an
isomorphism over the source, and the fibre-dimension condition is transported by the
homeomorphism of fibre supports.

The structure morphism produced by the transport along an isomorphism `d` of the base is
`f ≫ d.inv` rather than an arbitrary `f' : X ⟶ S'` with `f' ≫ d.hom = f`. The two differ by the
identity isomorphism of the source, so the `ofBaseIsoHom` family is the `ofBaseIso` family
followed by `AlgebraicGeometry.DevissageChain.ofSourceIso` for `Iso.refl`; prescribing the
morphism in the recursion instead would make the structure morphism of every stage a parameter
of it, and the recursion is what the base transport is for.

The comparison of the fibres under an isomorphism of the base is the canonical morphism of
fibre products attached to the cartesian square exhibiting `f ≫ d.inv` as the base change of
`f` along `d.hom`; it is an isomorphism because its three components are. Every clause of a
one-step dévissage except the fibre-dimension condition is carried by it formally, and that
condition is carried by the resulting homeomorphism of fibre supports. The pure transcendence
of the residue field at the distinguished point is the one clause of a one-step dévissage *at a
point* whose base field changes: the two algebra structures on `Y.residueField y` differ by the
residue-field isomorphism induced by `d`, and
`Stacks.Flatness.purelyTranscendental_of_ringEquiv_base` transports pure transcendence along
exactly such a change of base field.

`SheafOfModules.isFiniteType_of_iso`, `SheafOfModules.isQuasicoherent_of_iso` and
`Stacks.Modules.isQuasicoherent_pullback` are the specializations to modules on a scheme of
results stated over a general site or ringed space; they exist because those results have
universe parameters in front of their instance arguments, or are stated for the ringed-space
inverse image, so that neither applies without help at a scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry

universe u

/-! ### Free modules -/

namespace AlgebraicGeometry.Scheme.Modules

/-- The inverse image of the free module on `I` along a morphism of schemes is the free module
on `I`. -/
def pullbackFreeIso {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.free (R := Y.ringCatSheaf) I) ≅
      SheafOfModules.free (R := X.ringCatSheaf) I :=
  haveI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs ((Scheme.Modules.pushforward f).IsRightAdjoint)
  haveI : (Opens.map f.base).Final := final_of_representablyFlat _
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I

/-- The inverse image of a free module is natural in the indexing type. -/
lemma pullbackFreeIso_hom_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) {I J : Type u}
    (u : I → J) :
    (Scheme.Modules.pullback f).map (SheafOfModules.freeMap (R := Y.ringCatSheaf) u) ≫
        (pullbackFreeIso f J).hom =
      (pullbackFreeIso f I).hom ≫ SheafOfModules.freeMap (R := X.ringCatSheaf) u :=
  haveI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs ((Scheme.Modules.pushforward f).IsRightAdjoint)
  haveI : (Opens.map f.base).Final := final_of_representablyFlat _
  SheafOfModules.pullbackObjFreeIso_hom_naturality f.toRingCatSheafHom u

end AlgebraicGeometry.Scheme.Modules

/-- A functor sends a composite to an isomorphism as soon as it sends both factors to
isomorphisms. This is the form in which invertibility of an inverse image of a long composite
is checked factor by factor. -/
lemma CategoryTheory.Functor.isIso_map_comp {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) {A B E : C} (p : A ⟶ B) (q : B ⟶ E) (hp : IsIso (G.map p))
    (hq : IsIso (G.map q)) : IsIso (G.map (p ≫ q)) := by
  have := hp
  have := hq
  rw [G.map_comp]
  infer_instance

namespace SheafOfModules

/-- Reindexing the free module on `Fin m` along an equality `m = n` is the identification of
the two free modules. -/
lemma freeMap_finCast_eq_eqToHom {Y : AlgebraicGeometry.Scheme.{u}} {m n : ℕ} (hmn : m = n) :
    freeMap (R := Y.ringCatSheaf)
        (fun i : ULift.{u} (Fin m) => ULift.up (Fin.cast hmn i.down)) =
      eqToHom (congrArg (fun k => free (R := Y.ringCatSheaf) (ULift.{u} (Fin k))) hmn) := by
  subst hmn
  change freeMap (R := Y.ringCatSheaf) id = 𝟙 _
  exact (freeFunctor_map (𝟙 (ULift.{u} (Fin m)))).symm.trans (freeFunctor.map_id _)

/-- Reindexing the free module on `Fin m` along the reflexivity equality is the identity. -/
lemma freeMap_finCast_rfl {Y : AlgebraicGeometry.Scheme.{u}} {m : ℕ} :
    freeMap (R := Y.ringCatSheaf)
      (fun i : ULift.{u} (Fin m) => ULift.up (Fin.cast rfl i.down)) = 𝟙 _ := by
  exact (freeMap_finCast_eq_eqToHom rfl).trans (eqToHom_refl _ _)

end SheafOfModules

/-! ### Local dimension -/

/-- The local dimension of a subspace at one of its points depends only on the underlying
subset. -/
lemma topologicalKrullDimAt_congr {T : Type u} [TopologicalSpace T] {A B : Set T} (hAB : A = B)
    {x : T} (ha : x ∈ A) (hb : x ∈ B) :
    topologicalKrullDimAt A ⟨x, ha⟩ = topologicalKrullDimAt B ⟨x, hb⟩ := by
  subst hAB
  rfl

/-! ### Supports -/

namespace SheafOfModules

/-- A point lies in the support of a module on a scheme if and only if it lies in the support
of any isomorphic module. -/
lemma mem_supp_iff_of_iso {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (x : X) : x ∈ supp M ↔ x ∈ supp N := by
  rw [mem_supp_iff_nontrivial_stalk (F := M) x, mem_supp_iff_nontrivial_stalk (F := N) x]
  have hmap : IsIso e.hom.mapPresheaf :=
    inferInstanceAs (IsIso ((AlgebraicGeometry.Scheme.Modules.toPresheaf X).map e.hom))
  have hstalk : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map e.hom.mapPresheaf) :=
    inferInstance
  have es : M.presheaf.stalk x ≃ N.presheaf.stalk x :=
    Equiv.ofBijective
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map e.hom.mapPresheaf))
      (ConcreteCategory.bijective_of_isIso _)
  exact es.nontrivial_congr

/-! ### Finiteness and quasi-coherence -/

/-- Being of finite type is invariant under isomorphism of modules on a scheme. This is
`Stacks.SheafOfModules.Site.isFiniteType_of_iso`, whose universe parameters precede its
instance arguments and therefore have to be supplied by hand at this site. -/
lemma isFiniteType_of_iso {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (hM : M.IsFiniteType) : N.IsFiniteType :=
  Stacks.SheafOfModules.Site.isFiniteType_of_iso.{u, u, u} (R := X.ringCatSheaf) e hM

/-- Quasi-coherence is invariant under isomorphism of modules on a scheme. -/
lemma isQuasicoherent_of_iso {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (hM : M.IsQuasicoherent) : N.IsQuasicoherent :=
  (isQuasicoherent X.ringCatSheaf).prop_of_iso e hM

end SheafOfModules

/-! ### Generic points -/

/-- A continuous surjection carries a generic point of the whole space to a generic point of the
whole target. -/
private lemma isGenericPoint_univ_map_of_surjective {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {x : α} {f : α → β} (hf : Continuous f) (hfs : Function.Surjective f)
    (hx : IsGenericPoint x Set.univ) : IsGenericPoint (f x) Set.univ := by
  simpa only [Set.image_univ_of_surjective hfs, closure_univ] using hx.image hf

/-- A continuous surjection carries the generic point of its source to the generic point of
its target. -/
lemma IsGenericPoint.map_eq_of_surjective {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [T0Space β] {x : α} {y : β} {f : α → β} (hf : Continuous f)
    (hfs : Function.Surjective f) (hx : IsGenericPoint x Set.univ)
    (hy : IsGenericPoint y Set.univ) : f x = y :=
  (isGenericPoint_univ_map_of_surjective hf hfs hx).eq hy

/-- An open embedding into an irreducible space carries the generic point of its source to the
generic point of its target. -/
lemma IsGenericPoint.map_eq_of_isOpenEmbedding {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [T0Space β] [PreirreducibleSpace β] {a : α} {b : β} {j : α → β}
    (hj : Topology.IsOpenEmbedding j) (ha : IsGenericPoint a Set.univ)
    (hb : IsGenericPoint b Set.univ) : j a = b := by
  have hdense : Dense (Set.range j) :=
    (by simpa only [Set.image_univ] using hj.isOpenMap Set.univ isOpen_univ :
      IsOpen (Set.range j)).dense ⟨j a, a, rfl⟩
  refine IsGenericPoint.eq ?_ hb
  simpa only [Set.image_univ, hdense.closure_eq] using ha.image hj.continuous

/-! ### Fibres of a cartesian square -/

namespace AlgebraicGeometry

variable {Y Y' S S' : Scheme.{u}} {pY : Y' ⟶ Y} {g' : Y' ⟶ S'} {g : Y ⟶ S} {h : S' ⟶ S}

/-- For a cartesian square with vertical morphisms `g'`, `g` and lower horizontal morphism
`h`, the canonical morphism from the fibre of `g'` over `s'` to the fibre of `g` over
`h s'`. -/
def fiberMapOfIsPullback (hsq : IsPullback pY g' g h) (s' : S') :
    g'.fiber s' ⟶ g.fiber (h s') :=
  pullback.map _ _ _ _ pY (Spec.map (h.residueFieldMap s')) h hsq.w.symm (by simp)

@[reassoc]
lemma fiberMapOfIsPullback_comp_fiberι (hsq : IsPullback pY g' g h) (s' : S') :
    fiberMapOfIsPullback hsq s' ≫ g.fiberι (h s') = g'.fiberι s' ≫ pY := by
  dsimp [fiberMapOfIsPullback, Scheme.Hom.fiber, Scheme.Hom.fiberι]
  rw [pullback.lift_fst]

/-- The comparison of fibres attached to a cartesian square is surjective: it is the base
change of the morphism of spectra of residue fields, which is surjective because those
spectra are single points. -/
lemma surjective_fiberMapOfIsPullback (hsq : IsPullback pY g' g h) (s' : S') :
    Function.Surjective (fiberMapOfIsPullback hsq s').base := by
  have hres : Surjective (Spec.map (h.residueFieldMap s')) :=
    ⟨Function.surjective_to_subsingleton _⟩
  have : Surjective (fiberMapOfIsPullback hsq s') :=
    MorphismProperty.of_isPullback
      (isPullback_fiberToSpecResidueField_of_isPullback hsq s').flip hres
  exact (fiberMapOfIsPullback hsq s').surjective

/-- The comparison of fibres attached to a cartesian square of morphisms with geometrically
irreducible fibres carries the generic point of the fibre of `g'` to the generic point of the
fibre of `g`. -/
lemma fiberMapOfIsPullback_genericPoint (hsq : IsPullback pY g' g h) {s : S} {s' : S'}
    (hs : h s' = s) [GeometricallyIrreducible g] [GeometricallyIrreducible g']
    {η : g'.fiber s'} (hη : IsGenericPoint η Set.univ) {ξ : g.fiber s}
    (hξ : IsGenericPoint ξ Set.univ) :
    fiberMapOfIsPullback hsq s' η = (fiberIsoOfEq g hs).inv ξ := by
  exact IsGenericPoint.map_eq_of_surjective (fiberMapOfIsPullback hsq s').continuous
    (surjective_fiberMapOfIsPullback hsq s') hη
    (isGenericPoint_univ_map_of_surjective (fiberIsoOfEq g hs).inv.continuous
      (fiberIsoOfEq g hs).inv.surjective hξ)

/-- If a morphism of modules becomes an isomorphism over the residue field of the image of
`y'`, then its inverse image becomes an isomorphism over the residue field of `y'`. -/
lemma isIso_pullback_map_fromSpecResidueField {Y Y' : Scheme.{u}} (j : Y' ⟶ Y)
    {M N : Y.Modules} (α : M ⟶ N) (y' : Y')
    (hα : IsIso ((Scheme.Modules.pullback (Y.fromSpecResidueField (j y'))).map α)) :
    IsIso ((Scheme.Modules.pullback (Y'.fromSpecResidueField y')).map
      ((Scheme.Modules.pullback j).map α)) := by
  have := hα
  have hcomp : IsIso ((Scheme.Modules.pullback
      (Spec.map (j.residueFieldMap y') ≫ Y.fromSpecResidueField (j y'))).map α) :=
    (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp
      (Spec.map (j.residueFieldMap y')) (Y.fromSpecResidueField (j y'))) α).mp
        (inferInstanceAs (IsIso ((Scheme.Modules.pullback
          (Spec.map (j.residueFieldMap y'))).map
            ((Scheme.Modules.pullback (Y.fromSpecResidueField (j y'))).map α))))
  refine (NatIso.isIso_map_iff
    (Scheme.Modules.pullbackComp (Y'.fromSpecResidueField y') j) α).mpr ?_
  rwa [← j.SpecMap_residueFieldMap_fromSpecResidueField y']

/-! ### Supports under a comparison of the sources -/

/-- Two morphisms with the same target whose sources are identified by an isomorphism over that
target have inverse images of a module whose supports correspond: the first is the inverse
image of the second. -/
lemma supp_pullback_eq_preimage_of_iso {A B W : Scheme.{u}} {p : A ⟶ W} {q : B ⟶ W} (φ : A ≅ B)
    (hφ : φ.hom ≫ q = p) (F : W.Modules) [F.IsFiniteType] :
    SheafOfModules.supp ((Scheme.Modules.pullback p).obj F) =
      (φ.hom : A → B) ⁻¹' SheafOfModules.supp ((Scheme.Modules.pullback q).obj F) := by
  have hcoe : ((q : B → W) ∘ (φ.hom : A → B)) = (p : A → W) := by rw [← hφ]; rfl
  rw [Stacks.Modules.supp_pullback, Stacks.Modules.supp_pullback, ← Set.preimage_comp, hcoe]

/-- The homeomorphism of the supports of the two inverse images of a module along two
morphisms whose sources are identified by an isomorphism over the common target. -/
def suppPullbackHomeoOfIso {A B W : Scheme.{u}} {p : A ⟶ W} {q : B ⟶ W} (φ : A ≅ B)
    (hφ : φ.hom ≫ q = p) (F : W.Modules) [F.IsFiniteType] :
    SheafOfModules.supp ((Scheme.Modules.pullback p).obj F) ≃ₜ
      SheafOfModules.supp ((Scheme.Modules.pullback q).obj F) :=
  φ.hom.homeomorph.subtype fun a => by
    rw [supp_pullback_eq_preimage_of_iso φ hφ F]; exact Iff.rfl

/-- The dimension of the support of an inverse image of a module depends only on the morphism
up to an isomorphism of its source over the target. -/
lemma topologicalKrullDim_supp_pullback_of_iso {A B W : Scheme.{u}} {p : A ⟶ W} {q : B ⟶ W}
    (φ : A ≅ B) (hφ : φ.hom ≫ q = p) (F : W.Modules) [F.IsFiniteType] :
    topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback p).obj F)) =
      topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback q).obj F)) :=
  IsHomeomorph.topologicalKrullDim_eq _ (suppPullbackHomeoOfIso φ hφ F).isHomeomorph

/-- The local dimension of the support of an inverse image of a module at a point is carried
along an isomorphism of the source over the target. -/
lemma topologicalKrullDimAt_supp_pullback_of_iso {A B W : Scheme.{u}} {p : A ⟶ W} {q : B ⟶ W}
    (φ : A ≅ B) (hφ : φ.hom ≫ q = p) (F : W.Modules) [F.IsFiniteType] (a : A)
    (ha : a ∈ SheafOfModules.supp ((Scheme.Modules.pullback p).obj F))
    (ha' : φ.hom a ∈ SheafOfModules.supp ((Scheme.Modules.pullback q).obj F)) :
    topologicalKrullDimAt (SheafOfModules.supp ((Scheme.Modules.pullback p).obj F)) ⟨a, ha⟩ =
      topologicalKrullDimAt
        (SheafOfModules.supp ((Scheme.Modules.pullback q).obj F)) ⟨φ.hom a, ha'⟩ :=
  (topologicalKrullDimAt_eq_of_homeomorph (suppPullbackHomeoOfIso φ hφ F) ⟨a, ha⟩).trans rfl

/-! ### Isomorphisms of the source -/

section SourceIso

variable {X X' S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S} {F : X.Modules} {F' : X'.Modules}

/-- The direct image along the inverse of an isomorphism of schemes is the inverse image
along the isomorphism. -/
def Scheme.Modules.pushforwardInvIsoPullback (e : X' ≅ X) (F : X.Modules) :
    (Scheme.Modules.pushforward e.inv).obj F ≅ (Scheme.Modules.pullback e.hom).obj F :=
  ((Scheme.Modules.restrictFunctorAdjCounitIso e.hom).app
      ((Scheme.Modules.pushforward e.inv).obj F)).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback e.hom).app
      ((Scheme.Modules.pushforward e.hom).obj ((Scheme.Modules.pushforward e.inv).obj F)) ≪≫
    (Scheme.Modules.pullback e.hom).mapIso
      ((Scheme.Modules.pushforwardComp e.inv e.hom).app F ≪≫
        (Scheme.Modules.pushforwardCongr e.inv_hom_id).app F ≪≫
        (Scheme.Modules.pushforwardId X).app F)

/-- An isomorphism `e : X' ≅ X` over `S` induces an isomorphism of the fibres over any point
of `S`. -/
def fiberIsoOfSourceIso (e : X' ≅ X) (he : e.hom ≫ f = f') (t : S) :
    f'.fiber t ≅ f.fiber t := by
  let m : f'.fiber t ⟶ f.fiber t :=
    pullback.map f' (S.fromSpecResidueField t) f (S.fromSpecResidueField t)
      e.hom (𝟙 _) (𝟙 S) (by simp only [Category.comp_id]; exact he.symm) (by simp)
  haveI : IsIso m := by
    change IsIso (pullback.map f' (S.fromSpecResidueField t) f (S.fromSpecResidueField t)
      e.hom (𝟙 _) (𝟙 S) _ _)
    infer_instance
  exact asIso m

@[reassoc]
lemma fiberIsoOfSourceIso_hom_comp_fiberι (e : X' ≅ X) (he : e.hom ≫ f = f') (t : S) :
    (fiberIsoOfSourceIso e he t).hom ≫ f.fiberι t = f'.fiberι t ≫ e.hom := by
  dsimp only [fiberIsoOfSourceIso, Scheme.Hom.fiberι, pullback.map]
  exact pullback.lift_fst _ _ _

/-- An isomorphism of the source over `S`, compatible with an identification of the two
modules, induces a homeomorphism of the supports of the two modules on the fibres. -/
def fiberSupportHomeoOfSourceIso [F.IsFiniteType] (e : X' ≅ X) (he : e.hom ≫ f = f')
    (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') (t : S) :
    SheafOfModules.supp ((Scheme.Modules.pullback (f'.fiberι t)).obj F') ≃ₜ
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι t)).obj F) := by
  have hFT : ((Scheme.Modules.pullback (f.fiberι t)).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType (f.fiberι t).toLRSHom.toShHom F
  have hmod : (Scheme.Modules.pullback (fiberIsoOfSourceIso e he t).hom).obj
      ((Scheme.Modules.pullback (f.fiberι t)).obj F) ≅
      (Scheme.Modules.pullback (f'.fiberι t)).obj F' :=
    (Scheme.Modules.pullbackComp (fiberIsoOfSourceIso e he t).hom (f.fiberι t)).app F ≪≫
      (Scheme.Modules.pullbackCongr (fiberIsoOfSourceIso_hom_comp_fiberι e he t)).app F ≪≫
      ((Scheme.Modules.pullbackComp (f'.fiberι t) e.hom).app F).symm ≪≫
      (Scheme.Modules.pullback (f'.fiberι t)).mapIso eF
  refine (fiberIsoOfSourceIso e he t).hom.homeomorph.subtype fun a => ?_
  rw [← SheafOfModules.mem_supp_iff_of_iso hmod a,
    Stacks.Modules.supp_pullback (fiberIsoOfSourceIso e he t).hom]
  rfl

@[simp]
lemma fiberSupportHomeoOfSourceIso_coe [F.IsFiniteType] (e : X' ≅ X) (he : e.hom ≫ f = f')
    (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') (t : S)
    (a : SheafOfModules.supp ((Scheme.Modules.pullback (f'.fiberι t)).obj F')) :
    (fiberSupportHomeoOfSourceIso e he eF t a).val = (fiberIsoOfSourceIso e he t).hom a.val :=
  rfl

/-- The support of the module on a fibre has the same dimension before and after an
isomorphism of the source over `S`. -/
lemma topologicalKrullDim_fiberSupport_of_sourceIso [F.IsFiniteType] (e : X' ≅ X)
    (he : e.hom ≫ f = f') (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') (t : S) :
    topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback (f'.fiberι t)).obj F'))
      = topologicalKrullDim
        (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι t)).obj F)) :=
  IsHomeomorph.topologicalKrullDim_eq _
    (fiberSupportHomeoOfSourceIso e he eF t).isHomeomorph

/-- Membership of a point in the support of the module on its fibre is carried across an
isomorphism of the source over `S`. -/
lemma mem_fiberSupport_iff_of_sourceIso [F.IsFiniteType] [F'.IsFiniteType] (e : X' ≅ X)
    (he : e.hom ≫ f = f') (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') (x' : X') :
    f'.asFiber x' ∈
        SheafOfModules.supp ((Scheme.Modules.pullback (f'.fiberι (f' x'))).obj F') ↔
      f.asFiber (e.hom x') ∈
        SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f (e.hom x')))).obj F) := by
  subst he
  rw [Stacks.Modules.supp_pullback, Stacks.Modules.supp_pullback,
    ← SheafOfModules.supp_eq_of_iso eF, Stacks.Modules.supp_pullback]
  simp only [Set.mem_preimage, Scheme.Hom.fiberι_asFiber]

/-- The local dimension of the support of the module on its fibre at a point is carried
across an isomorphism of the source over `S`. -/
lemma topologicalKrullDimAt_fiberSupport_of_sourceIso [F.IsFiniteType] (e : X' ≅ X)
    (he : e.hom ≫ f = f') (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') (x' : X')
    (hm : f'.asFiber x' ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f'.fiberι (f' x'))).obj F'))
    (hm' : f.asFiber (e.hom x') ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f (e.hom x')))).obj F)) :
    topologicalKrullDimAt
        (SheafOfModules.supp ((Scheme.Modules.pullback (f'.fiberι (f' x'))).obj F'))
        ⟨f'.asFiber x', hm⟩ =
      topologicalKrullDimAt
        (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f (e.hom x')))).obj F))
        ⟨f.asFiber (e.hom x'), hm'⟩ := by
  subst he
  have hval : (fiberSupportHomeoOfSourceIso (f := f) e rfl eF ((e.hom ≫ f) x')
      ⟨(e.hom ≫ f).asFiber x', hm⟩).val = f.asFiber (e.hom x') := by
    apply (f.fiberι ((e.hom ≫ f) x')).isEmbedding.injective
    rw [fiberSupportHomeoOfSourceIso_coe, ← Scheme.Hom.comp_apply,
      fiberIsoOfSourceIso_hom_comp_fiberι, Scheme.Hom.comp_apply,
      Scheme.Hom.fiberι_asFiber]
    exact (f.fiberι_asFiber (e.hom x')).symm
  refine Eq.trans (topologicalKrullDimAt_eq_of_homeomorph
    (fiberSupportHomeoOfSourceIso (f := f) e rfl eF ((e.hom ≫ f) x')) ⟨_, hm⟩) ?_
  exact congrArg _ (Subtype.ext hval)

variable [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
  [LocallyOfFiniteType f'] [F'.IsQuasicoherent] [F'.IsFiniteType]

/-- A one-step dévissage is carried along an isomorphism `e : X' ≅ X` of its source over `S`,
compatible with an identification of the two modules. The closed subscheme, the smooth
scheme and the finite and smooth morphisms are unchanged; only the closed immersion is
composed with `e.inv`. -/
def OneStepDevissage.ofSourceIso (e : X' ≅ X) (he : e.hom ≫ f = f')
    (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') {s : S} (D : OneStepDevissage f F s) :
    OneStepDevissage f' F' s := by
  haveI : IsClosedImmersion D.i := D.closed_immersion
  haveI : LocallyOfFinitePresentation D.i := D.finite_presentation.1
  haveI : QuasiCompact D.i := D.finite_presentation.2.1
  haveI : QuasiSeparated D.i := D.finite_presentation.2.2
  haveI : D.G.IsQuasicoherent := D.quasi_coherent_G
  haveI : IsAffine X := D.affine_X
  have hsq : IsPullback (𝟙 D.Z) (D.i ≫ e.inv) D.i e.hom := by
    apply IsPullback.of_horiz_isIso
    exact ⟨by simp [Category.assoc]⟩
  haveI : IsIso ((AffinePushforward.baseChangeNatTrans hsq.w).app D.G) :=
    AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom hsq D.G
  exact
    { Z := D.Z
      Y := D.Y
      i := D.i ≫ e.inv
      π := D.π
      g := D.g
      G := D.G
      quasi_coherent_G := D.quasi_coherent_G
      finite_type_G := D.finite_type_G
      over_base := by
        calc
          (D.i ≫ e.inv) ≫ f' = (D.i ≫ e.inv) ≫ e.hom ≫ f := by rw [he]
          _ = D.i ≫ f := by simp
          _ = D.π ≫ D.g := D.over_base
      affine_X := IsAffine.of_isIso e.hom
      affine_S := D.affine_S
      affine_Z := D.affine_Z
      affine_Y := D.affine_Y
      closed_immersion := inferInstance
      finite_presentation := ⟨inferInstance, inferInstance, inferInstance⟩
      module_iso := eF.symm ≪≫ (Scheme.Modules.pullback e.hom).mapIso D.module_iso ≪≫
        asIso ((AffinePushforward.baseChangeNatTrans hsq.w).app D.G) ≪≫
        (Scheme.Modules.pushforward (D.i ≫ e.inv)).mapIso
          ((Scheme.Modules.pullbackId D.Z).app D.G)
      finite := D.finite
      smooth := D.smooth
      geometrically_irreducible := D.geometrically_irreducible
      fiber_dimension := fun t => (D.fiber_dimension t).trans
        (topologicalKrullDim_fiberSupport_of_sourceIso e he eF s).symm }

@[simp] lemma OneStepDevissage.ofSourceIso_Z (e : X' ≅ X) (he : e.hom ≫ f = f')
    (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') {s : S} (D : OneStepDevissage f F s) :
    (OneStepDevissage.ofSourceIso e he eF D).Z = D.Z := rfl

@[simp] lemma OneStepDevissage.ofSourceIso_Y (e : X' ≅ X) (he : e.hom ≫ f = f')
    (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') {s : S} (D : OneStepDevissage f F s) :
    (OneStepDevissage.ofSourceIso e he eF D).Y = D.Y := rfl

@[simp] lemma OneStepDevissage.ofSourceIso_i (e : X' ≅ X) (he : e.hom ≫ f = f')
    (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') {s : S} (D : OneStepDevissage f F s) :
    (OneStepDevissage.ofSourceIso e he eF D).i = D.i ≫ e.inv := rfl

@[simp] lemma OneStepDevissage.ofSourceIso_π (e : X' ≅ X) (he : e.hom ≫ f = f')
    (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') {s : S} (D : OneStepDevissage f F s) :
    (OneStepDevissage.ofSourceIso e he eF D).π = D.π := rfl

@[simp] lemma OneStepDevissage.ofSourceIso_g (e : X' ≅ X) (he : e.hom ≫ f = f')
    (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') {s : S} (D : OneStepDevissage f F s) :
    (OneStepDevissage.ofSourceIso e he eF D).g = D.g := rfl

@[simp] lemma OneStepDevissage.ofSourceIso_G (e : X' ≅ X) (he : e.hom ≫ f = f')
    (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') {s : S} (D : OneStepDevissage f F s) :
    (OneStepDevissage.ofSourceIso e he eF D).G = D.G := rfl

/-- A one-step dévissage at a point is carried along an isomorphism of its source over `S`,
compatible with an identification of the two modules. -/
def OneStepDevissageAt.ofSourceIso (e : X' ≅ X) (he : e.hom ≫ f = f')
    (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') {x : X} {x' : X'} (hx : e.hom x' = x)
    (P : OneStepDevissageAt f F x) : OneStepDevissageAt f' F' x' := by
  subst he
  subst hx
  have hm : (e.hom ≫ f).asFiber x' ∈ SheafOfModules.supp
      ((Scheme.Modules.pullback ((e.hom ≫ f).fiberι ((e.hom ≫ f) x'))).obj F') :=
    (mem_fiberSupport_iff_of_sourceIso (f := f) e rfl eF x').mpr P.mem_fiber_support
  exact
    { toOneStepDevissage := OneStepDevissage.ofSourceIso e rfl eF P.toOneStepDevissage
      mem_fiber_support := hm
      dimension :=
        (topologicalKrullDimAt_fiberSupport_of_sourceIso (f := f) e rfl eF x' hm
            P.mem_fiber_support).trans
          (P.dimension.trans
            (topologicalKrullDim_fiberSupport_of_sourceIso (f := f) e rfl eF _).symm)
      z := P.z
      y := P.y
      i_z := by
        change e.inv (P.toOneStepDevissage.i P.z) = x'
        rw [P.i_z]
        exact congrArg (fun k : X' ⟶ X' => k x') e.hom_inv_id
      π_z := P.π_z
      g_y := P.g_y
      fiber_eq_singleton := P.fiber_eq_singleton
      residueField_purelyTranscendental := P.residueField_purelyTranscendental }

/-- A stage of a complete dévissage is carried along an isomorphism of its source over `S`,
compatible with an identification of the two modules: the rank and the free-module map are
unchanged. -/
def DevissageStage.ofSourceIso (e : X' ≅ X) (he : e.hom ≫ f = f')
    (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') {s : S} (D : DevissageStage f F s) :
    DevissageStage f' F' s where
  oneStep := OneStepDevissage.ofSourceIso e he eF D.oneStep
  rank := D.rank
  alpha := D.alpha
  genericPoint := D.genericPoint
  genericPoint_spec := D.genericPoint_spec
  genericFiber_isIso := D.genericFiber_isIso

end SourceIso

/-! ### Isomorphisms of the source of a complete dévissage -/

section ChainSourceIso

variable {X X' S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S} {F : X.Modules} {F' : X'.Modules}
  [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent] [ht : F.IsFiniteType]
  [hl' : LocallyOfFiniteType f'] [hq' : F'.IsQuasicoherent] [ht' : F'.IsFiniteType]

/-- The cokernel of the free-module map of a stage is unchanged by
`AlgebraicGeometry.DevissageStage.ofSourceIso`: the smooth scheme, the finite morphism, the
module on the closed subscheme and the free-module map are all untouched, so the rest of a
chain of stages can be reused verbatim after the transport. -/
lemma DevissageStage.ofSourceIso_coker {s : S} (e : X' ≅ X) (he : e.hom ≫ f = f')
    (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') (D : DevissageStage f F s) :
    (D.ofSourceIso e he eF).coker = D.coker := rfl

/-- A chain of stages of a complete dévissage is carried along an isomorphism of its source
over `S`, compatible with an identification of the two modules: only the first stage changes,
because every later stage dévisses the cokernel of the previous one, which
`AlgebraicGeometry.DevissageStage.ofSourceIso_coker` leaves alone. -/
def DevissageChain.ofSourceIso {s : S} (e : X' ≅ X) (he : e.hom ≫ f = f')
    (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F')
    (C : DevissageChain s X f F hl hq ht) : DevissageChain s X' f' F' hl' hq' ht' :=
  match C with
  | .last stage hzero => .last (stage.ofSourceIso e he eF) hzero
  | .more stage hqC htC hlY tail => .more (stage.ofSourceIso e he eF) hqC htC hlY tail

/-- A complete dévissage of `F/X/S` over `s` is carried along an isomorphism of its source over
`S`, compatible with an identification of the two modules. -/
def NonemptyCompleteDevissage.ofSourceIso {s : S} (e : X' ≅ X) (he : e.hom ≫ f = f')
    (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F')
    (D : NonemptyCompleteDevissage f F s) : NonemptyCompleteDevissage f' F' s :=
  ⟨D.chain.ofSourceIso e he eF⟩

/-- The one-step dévissage underlying the transport of a one-step dévissage at a point along an
isomorphism of the source is the transport of the underlying one-step dévissage. This is the
definitional equation the pointed stages are glued along. -/
lemma OneStepDevissageAt.ofSourceIso_toOneStepDevissage (e : X' ≅ X)
    (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') (x' : X')
    (P : OneStepDevissageAt f F (e.hom x')) :
    (P.ofSourceIso (f' := e.hom ≫ f) e rfl eF rfl).toOneStepDevissage =
      OneStepDevissage.ofSourceIso e rfl eF P.toOneStepDevissage := rfl

/-- The distinguished point of the smooth scheme of a pointed stage lies over the base point of
the dévissage. -/
lemma PointedDevissageStage.g_y {s : S} {x : X} {stage : DevissageStage f F s}
    (P : PointedDevissageStage f F s x stage) (hx : f x = s) : stage.oneStep.g P.y = s := by
  cases hx
  cases stage with
  | mk step rank alpha genericPoint genericPoint_spec genericFiber_isIso =>
    cases P with
    | mk atPoint sameOneStep y sameY =>
      cases sameOneStep
      cases sameY
      exact atPoint.g_y

/-- The distinguished points of a stage survive the transport along an isomorphism of the source
over `S`: the one-step dévissage at the current point is transported by
`AlgebraicGeometry.OneStepDevissageAt.ofSourceIso`, and the smooth scheme, which carries the
distinguished target point, is unchanged. -/
def PointedDevissageStage.ofSourceIso (e : X' ≅ X) (he : e.hom ≫ f = f')
    (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') {s : S} {x : X} {x' : X'}
    (hx : e.hom x' = x) (hfx : f x = s) {stage : DevissageStage f F s}
    (P : PointedDevissageStage f F s x stage) :
    PointedDevissageStage f' F' s x' (stage.ofSourceIso e he eF) where
  atPoint := P.atPoint.ofSourceIso e he eF hx
  sameOneStep := by
    subst he
    subst hx
    subst hfx
    exact heq_of_eq (congrArg (OneStepDevissage.ofSourceIso e rfl eF)
      (eq_of_heq P.sameOneStep))
  y := P.y
  sameY := by
    subst he
    subst hx
    exact P.sameY

/-- The compatible distinguished points of a chain of stages survive the transport of the chain
along an isomorphism of the source over `S`: only the first stage is affected, and the rest of
the chain is reused. -/
def PointedDevissageChain.ofSourceIso (e : X' ≅ X) (he : e.hom ≫ f = f')
    (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') {s : S} {x : X} {x' : X'}
    (hx : e.hom x' = x) (hfx : f x = s) {C : DevissageChain s X f F hl hq ht}
    (P : PointedDevissageChain s X f F hl hq ht x C) :
    PointedDevissageChain s X' f' F' hl' hq' ht' x' (C.ofSourceIso e he eF) :=
  match C, P with
  | .last _ _, .last _ stage hzero pointed =>
    .last x' (stage.ofSourceIso e he eF) hzero (pointed.ofSourceIso e he eF hx hfx)
  | .more _ _ _ _ _, .more _ stage hqC htC hlY tail pointed pt =>
    .more x' (stage.ofSourceIso e he eF) hqC htC hlY tail
      (pointed.ofSourceIso e he eF hx hfx) pt

/-- A complete dévissage of `F/X/S` at `x` is carried along an isomorphism `e : X' ≅ X` of its
source over `S`, compatible with an identification of the two modules, to a complete dévissage
at any point of `X'` above `x`. -/
def NonemptyCompleteDevissageAt.ofSourceIso (e : X' ≅ X) (he : e.hom ≫ f = f')
    (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') {x : X} {x' : X'} (hx : e.hom x' = x)
    (D : NonemptyCompleteDevissageAt f F x) : NonemptyCompleteDevissageAt f' F' x' := by
  subst he
  subst hx
  exact
    { toNonemptyCompleteDevissage := D.toNonemptyCompleteDevissage.ofSourceIso e rfl eF
      pointed := D.pointed.ofSourceIso e rfl eF rfl rfl }

/-- A complete dévissage of `F/X/S` at `x`, empty or not, is carried along an isomorphism of its
source over `S`, compatible with an identification of the two modules. -/
def CompleteDevissageAt.ofSourceIso (e : X' ≅ X) (he : e.hom ≫ f = f')
    (eF : (Scheme.Modules.pullback e.hom).obj F ≅ F') {x : X} {x' : X'} (hx : e.hom x' = x)
    (D : CompleteDevissageAt f F x) : CompleteDevissageAt f' F' x' :=
  match D with
  | .empty hzero =>
    .empty (((Scheme.Modules.pullback e.hom).map_isZero hzero).of_iso eF.symm)
  | .nonempty data => .nonempty (data.ofSourceIso e he eF hx)

end ChainSourceIso

/-! ### Isomorphisms of the modules -/

section ModuleIso

variable {X S : Scheme.{u}} {f : X ⟶ S} {F F' : X.Modules} [LocallyOfFiniteType f]
  [F.IsQuasicoherent] [F.IsFiniteType] [F'.IsQuasicoherent] [F'.IsFiniteType]

/-- A one-step dévissage at `x` of `F` is a one-step dévissage at `x` of any module isomorphic
to `F`: only the identification of the module with the direct image changes. -/
def OneStepDevissageAt.ofModuleIso {x : X} (D : OneStepDevissageAt f F x) (e : F' ≅ F) :
    OneStepDevissageAt f F' x :=
  have hsupp : SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F') =
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) :=
    SheafOfModules.supp_eq_of_iso ((Scheme.Modules.pullback (f.fiberι (f x))).mapIso e)
  { D with
    toOneStepDevissage :=
      { D.toOneStepDevissage with
        module_iso := e ≪≫ D.toOneStepDevissage.module_iso
        fiber_dimension := fun t => (D.toOneStepDevissage.fiber_dimension t).trans
          (congrArg (fun T : Set (f.fiber (f x)) => topologicalKrullDim T) hsupp).symm }
    mem_fiber_support := hsupp.ge D.mem_fiber_support
    dimension := (topologicalKrullDimAt_congr hsupp _ D.mem_fiber_support).trans
      (D.dimension.trans
        (congrArg (fun T : Set (f.fiber (f x)) => topologicalKrullDim T) hsupp).symm) }

/-- A one-step dévissage at `x` whose module on the closed subscheme has been replaced by an
isomorphic one: the identification of the module with the direct image is composed with the
direct image of the isomorphism. -/
def OneStepDevissageAt.ofClosedModuleIso {x : X} (D : OneStepDevissageAt f F x)
    (G : D.toOneStepDevissage.Z.Modules) (hq : G.IsQuasicoherent) (ht : G.IsFiniteType)
    (e : G ≅ D.toOneStepDevissage.G) : OneStepDevissageAt f F x :=
  { D with
    toOneStepDevissage :=
      { D.toOneStepDevissage with
        G := G
        quasi_coherent_G := hq
        finite_type_G := ht
        module_iso := D.toOneStepDevissage.module_iso ≪≫
          (Scheme.Modules.pushforward D.toOneStepDevissage.i).mapIso e.symm } }

@[simp]
lemma OneStepDevissageAt.ofClosedModuleIso_G {x : X} (D : OneStepDevissageAt f F x)
    (G : D.toOneStepDevissage.Z.Modules) (hq : G.IsQuasicoherent) (ht : G.IsFiniteType)
    (e : G ≅ D.toOneStepDevissage.G) :
    (D.ofClosedModuleIso G hq ht e).toOneStepDevissage.G = G := rfl

/-- A one-step dévissage of `F/X/S` over `s` is a one-step dévissage of any isomorphic module:
only the identification of the module with the direct image changes. -/
def OneStepDevissage.ofModuleIso {s : S} (D : OneStepDevissage f F s) (e : F' ≅ F) :
    OneStepDevissage f F' s :=
  { D with
    module_iso := e ≪≫ D.module_iso
    fiber_dimension := fun t => (D.fiber_dimension t).trans
      (congrArg (fun T : Set (f.fiber s) => topologicalKrullDim T)
        (SheafOfModules.supp_eq_of_iso
          ((Scheme.Modules.pullback (f.fiberι s)).mapIso e))).symm }

@[simp] lemma OneStepDevissage.ofModuleIso_Z {s : S} (D : OneStepDevissage f F s) (e : F' ≅ F) :
    (D.ofModuleIso e).Z = D.Z := rfl

@[simp] lemma OneStepDevissage.ofModuleIso_Y {s : S} (D : OneStepDevissage f F s) (e : F' ≅ F) :
    (D.ofModuleIso e).Y = D.Y := rfl

@[simp] lemma OneStepDevissage.ofModuleIso_i {s : S} (D : OneStepDevissage f F s) (e : F' ≅ F) :
    (D.ofModuleIso e).i = D.i := rfl

@[simp] lemma OneStepDevissage.ofModuleIso_π {s : S} (D : OneStepDevissage f F s) (e : F' ≅ F) :
    (D.ofModuleIso e).π = D.π := rfl

@[simp] lemma OneStepDevissage.ofModuleIso_g {s : S} (D : OneStepDevissage f F s) (e : F' ≅ F) :
    (D.ofModuleIso e).g = D.g := rfl

@[simp] lemma OneStepDevissage.ofModuleIso_G {s : S} (D : OneStepDevissage f F s) (e : F' ≅ F) :
    (D.ofModuleIso e).G = D.G := rfl

/-- A stage of a complete dévissage of `F` is a stage of a complete dévissage of any isomorphic
module. The rank, the free-module map and the generic point are untouched: they live on the
closed subscheme and the smooth scheme of the one-step dévissage, which do not change. -/
def DevissageStage.ofModuleIso {s : S} (D : DevissageStage f F s) (e : F' ≅ F) :
    DevissageStage f F' s :=
  { D with oneStep := D.oneStep.ofModuleIso e }

@[simp] lemma DevissageStage.ofModuleIso_oneStep {s : S} (D : DevissageStage f F s)
    (e : F' ≅ F) : (D.ofModuleIso e).oneStep = D.oneStep.ofModuleIso e := rfl

@[simp] lemma DevissageStage.ofModuleIso_rank {s : S} (D : DevissageStage f F s) (e : F' ≅ F) :
    (D.ofModuleIso e).rank = D.rank := rfl

/-- The cokernel of the free-module map of a stage is unchanged by
`AlgebraicGeometry.DevissageStage.ofModuleIso`, so the rest of a chain of stages can be reused
verbatim after the transport. -/
lemma DevissageStage.ofModuleIso_coker {s : S} (D : DevissageStage f F s) (e : F' ≅ F) :
    (D.ofModuleIso e).coker = D.coker := rfl

end ModuleIso

/-! ### Isomorphisms of the module of a complete dévissage -/

section ChainModuleIso

variable {X S : Scheme.{u}} {s : S} {f : X ⟶ S} {F F' : X.Modules}
  [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent] [ht : F.IsFiniteType]
  [hq' : F'.IsQuasicoherent] [ht' : F'.IsFiniteType]

/-- A chain of stages of a complete dévissage of `F` is one of any isomorphic module: only the
first stage changes, because every later stage dévisses the cokernel of the previous one, which
`AlgebraicGeometry.DevissageStage.ofModuleIso_coker` leaves alone. -/
def DevissageChain.ofModuleIso (C : DevissageChain s X f F hl hq ht) (e : F' ≅ F) :
    DevissageChain s X f F' hl hq' ht' :=
  match C with
  | .last stage hzero => .last (stage.ofModuleIso e) hzero
  | .more stage hqC htC hlY tail => .more (stage.ofModuleIso e) hqC htC hlY tail

/-- A complete dévissage of `F/X/S` over `s` is one of any isomorphic module. -/
def NonemptyCompleteDevissage.ofModuleIso (D : NonemptyCompleteDevissage f F s) (e : F' ≅ F) :
    NonemptyCompleteDevissage f F' s :=
  ⟨D.chain.ofModuleIso e⟩

/-- The distinguished points of a stage survive the transport along an isomorphism of the
module: the one-step dévissage at the current point is transported by
`AlgebraicGeometry.OneStepDevissageAt.ofModuleIso`, which changes nothing the identification of
the stage with it mentions. -/
def PointedDevissageStage.ofModuleIso {x : X} {stage : DevissageStage f F (f x)}
    (P : PointedDevissageStage f F (f x) x stage) (e : F' ≅ F) :
    PointedDevissageStage f F' (f x) x (stage.ofModuleIso e) where
  atPoint := P.atPoint.ofModuleIso e
  sameOneStep :=
    heq_of_eq (congrArg (fun A : OneStepDevissage f F (f x) => A.ofModuleIso e)
      (eq_of_heq P.sameOneStep))
  y := P.y
  sameY := P.sameY

/-- The compatible distinguished points of a chain of stages survive the transport of the chain
along an isomorphism of the module: only the first stage is affected, and the rest of the chain
is reused. -/
def PointedDevissageChain.ofModuleIso {x : X} {C : DevissageChain (f x) X f F hl hq ht}
    (P : PointedDevissageChain (f x) X f F hl hq ht x C) (e : F' ≅ F) :
    PointedDevissageChain (f x) X f F' hl hq' ht' x (C.ofModuleIso e) :=
  match C, P with
  | .last _ _, .last x stage hzero pointed =>
    .last x (stage.ofModuleIso e) hzero (pointed.ofModuleIso e)
  | .more _ _ _ _ _, .more x stage hqC htC hlY tail pointed pt =>
    .more x (stage.ofModuleIso e) hqC htC hlY tail (pointed.ofModuleIso e) pt

/-- A complete dévissage of `F/X/S` at `x` is one of any isomorphic module. -/
def NonemptyCompleteDevissageAt.ofModuleIso {x : X} (D : NonemptyCompleteDevissageAt f F x)
    (e : F' ≅ F) : NonemptyCompleteDevissageAt f F' x where
  toNonemptyCompleteDevissage := D.toNonemptyCompleteDevissage.ofModuleIso e
  pointed := D.pointed.ofModuleIso e

/-- A complete dévissage of `F/X/S` at `x`, empty or not, is one of any isomorphic module. -/
def CompleteDevissageAt.ofModuleIso {x : X} (D : CompleteDevissageAt f F x) (e : F' ≅ F) :
    CompleteDevissageAt f F' x :=
  match D with
  | .empty hzero => .empty (hzero.of_iso e)
  | .nonempty data => .nonempty (data.ofModuleIso e)

end ChainModuleIso

/-! ### Fibres under an isomorphism of the base -/

section Fiber

variable {X S S' : Scheme.{u}} {f : X ⟶ S} {f' : X ⟶ S'}

/-- The square exhibiting a morphism over `S'` as the base change of a morphism over `S` along
an isomorphism `d : S' ≅ S` of the bases. -/
lemma isPullback_of_baseIso (d : S' ≅ S) (hd : f' ≫ d.hom = f) :
    IsPullback (𝟙 X) f' f d.hom := by
  apply IsPullback.of_horiz_isIso
  exact ⟨by rw [hd, Category.id_comp]⟩

/-- The fibre of `f' : X ⟶ S'` over `t`, carried along an isomorphism `d : S' ≅ S` of the base
to the fibre of `f` over `d.hom t`. -/
def fiberIsoOfBaseIso (d : S' ≅ S) (hd : f' ≫ d.hom = f) (t : S') :
    f'.fiber t ≅ f.fiber (d.hom t) := by
  let m : f'.fiber t ⟶ f.fiber (d.hom t) :=
    pullback.map f' (S'.fromSpecResidueField t) f (S.fromSpecResidueField (d.hom t))
      (𝟙 X) (Spec.map (d.hom.residueFieldMap t)) d.hom (by rw [hd, Category.id_comp])
      (d.hom.SpecMap_residueFieldMap_fromSpecResidueField t).symm
  haveI : IsIso m := by
    change IsIso (pullback.map f' (S'.fromSpecResidueField t) f
      (S.fromSpecResidueField (d.hom t)) (𝟙 X) (Spec.map (d.hom.residueFieldMap t)) d.hom _ _)
    infer_instance
  exact asIso m

@[reassoc]
lemma fiberIsoOfBaseIso_hom_comp_fiberι (d : S' ≅ S) (hd : f' ≫ d.hom = f) (t : S') :
    (fiberIsoOfBaseIso d hd t).hom ≫ f.fiberι (d.hom t) = f'.fiberι t := by
  dsimp only [fiberIsoOfBaseIso, Scheme.Hom.fiberι, pullback.map]
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The dimension of a fibre is unchanged by an isomorphism of the base. -/
lemma topologicalKrullDim_fiber_of_baseIso (d : S' ≅ S) (hd : f' ≫ d.hom = f) (t : S') :
    topologicalKrullDim (f'.fiber t) = topologicalKrullDim (f.fiber (d.hom t)) :=
  IsHomeomorph.topologicalKrullDim_eq _ (fiberIsoOfBaseIso d hd t).hom.homeomorph.isHomeomorph

/-- The fibre of `f'` over `s'`, carried along an isomorphism of the base matching `s'` with
`s`, is the fibre of `f` over `s`. -/
def fiberIsoOfBaseIsoPoint (d : S' ≅ S) (hd : f' ≫ d.hom = f) {s : S} {s' : S'}
    (hs : d.hom s' = s) : f'.fiber s' ≅ f.fiber s := by
  subst hs
  exact fiberIsoOfBaseIso d hd s'

@[reassoc]
lemma fiberIsoOfBaseIsoPoint_hom_comp_fiberι (d : S' ≅ S) (hd : f' ≫ d.hom = f) {s : S}
    {s' : S'} (hs : d.hom s' = s) :
    (fiberIsoOfBaseIsoPoint d hd hs).hom ≫ f.fiberι s = f'.fiberι s' := by
  subst hs
  exact fiberIsoOfBaseIso_hom_comp_fiberι d hd s'

/-- The comparison of fibres attached to an isomorphism of the base does not move the points of
the source: a point of the fibre of `f` over `s` and its preimage have the same image in `X`. -/
lemma fiberIsoOfBaseIsoPoint_inv_fiberι (d : S' ≅ S) (hd : f' ≫ d.hom = f) {s : S} {s' : S'}
    (hs : d.hom s' = s) (p : f.fiber s) :
    f'.fiberι s' ((fiberIsoOfBaseIsoPoint d hd hs).inv p) = f.fiberι s p := by
  have h := congrArg (fun k : f'.fiber s' ⟶ X => k ((fiberIsoOfBaseIsoPoint d hd hs).inv p))
    (fiberIsoOfBaseIsoPoint_hom_comp_fiberι d hd hs)
  simp only [Scheme.Hom.comp_apply] at h
  have h2 : (fiberIsoOfBaseIsoPoint d hd hs).hom
      ((fiberIsoOfBaseIsoPoint d hd hs).inv p) = p := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    simp
  rw [← h, h2]

/-- The point of the fibre representing `x`, carried along an isomorphism of the base. -/
lemma fiberIsoOfBaseIsoPoint_hom_asFiber (d : S' ≅ S) (hd : f' ≫ d.hom = f) (x : X)
    (hs : d.hom (f' x) = f x) :
    (fiberIsoOfBaseIsoPoint d hd hs).hom (f'.asFiber x) = f.asFiber x := by
  apply (f.fiberι (f x)).isEmbedding.injective
  rw [← Scheme.Hom.comp_apply, fiberIsoOfBaseIsoPoint_hom_comp_fiberι,
    Scheme.Hom.fiberι_asFiber, Scheme.Hom.fiberι_asFiber]

/-- The image of a point of `X` under `d.hom` composed with `f'` is its image under `f`. -/
lemma baseIso_hom_apply_of_baseIso (d : S' ≅ S) (hd : f' ≫ d.hom = f) (x : X) :
    d.hom (f' x) = f x :=
  congrArg (fun k : X ⟶ S => k x) hd

/-- Whether a point lies in the support of the module on its fibre does not depend on the
morphism to the base: both conditions say that the point lies in the support of the module. -/
lemma mem_fiberSupport_iff_mem_fiberSupport {X S T : Scheme.{u}} (p : X ⟶ S) (q : X ⟶ T)
    (F : X.Modules) [F.IsFiniteType] (x : X) :
    p.asFiber x ∈ SheafOfModules.supp ((Scheme.Modules.pullback (p.fiberι (p x))).obj F) ↔
      q.asFiber x ∈ SheafOfModules.supp ((Scheme.Modules.pullback (q.fiberι (q x))).obj F) := by
  rw [Stacks.Modules.supp_pullback, Stacks.Modules.supp_pullback]
  simp only [Set.mem_preimage, Scheme.Hom.fiberι_asFiber]

/-- The dimension of the support of the module on the distinguished fibre is unchanged by an
isomorphism of the base. -/
lemma topologicalKrullDim_fiberSupport_of_baseIso (d : S' ≅ S) (hd : f' ≫ d.hom = f) {s : S}
    {s' : S'} (hs : d.hom s' = s) (F : X.Modules) [F.IsFiniteType] :
    topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback (f'.fiberι s')).obj F)) =
      topologicalKrullDim
        (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) :=
  topologicalKrullDim_supp_pullback_of_iso (fiberIsoOfBaseIsoPoint d hd hs)
    (fiberIsoOfBaseIsoPoint_hom_comp_fiberι d hd hs) F

/-- The local dimension of the support of the module on its fibre at a point is unchanged by an
isomorphism of the base. -/
lemma topologicalKrullDimAt_fiberSupport_of_baseIso (d : S' ≅ S) (hd : f' ≫ d.hom = f)
    (F : X.Modules) [F.IsFiniteType] (x : X)
    (hm : f'.asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f'.fiberι (f' x))).obj F))
    (hm' : f.asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)) :
    topologicalKrullDimAt
        (SheafOfModules.supp ((Scheme.Modules.pullback (f'.fiberι (f' x))).obj F))
        ⟨f'.asFiber x, hm⟩ =
      topologicalKrullDimAt
        (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
        ⟨f.asFiber x, hm'⟩ := by
  have hs : d.hom (f' x) = f x := baseIso_hom_apply_of_baseIso d hd x
  have hval : (fiberIsoOfBaseIsoPoint d hd hs).hom (f'.asFiber x) = f.asFiber x :=
    fiberIsoOfBaseIsoPoint_hom_asFiber d hd x hs
  refine Eq.trans (topologicalKrullDimAt_supp_pullback_of_iso (fiberIsoOfBaseIsoPoint d hd hs)
    (fiberIsoOfBaseIsoPoint_hom_comp_fiberι d hd hs) F (f'.asFiber x) hm (hval ▸ hm')) ?_
  exact congrArg _ (Subtype.ext hval)

end Fiber

/-! ### Residue fields under an isomorphism of the base -/

/-- The residue-field maps of the two directions of an isomorphism of schemes compose to the
identification of the residue fields at the two spellings of a point. -/
lemma residueFieldMap_hom_comp_inv_of_iso {S S' : Scheme.{u}} (d : S' ≅ S) (a : S)
    (ha : d.hom (d.inv a) = a) :
    d.hom.residueFieldMap (d.inv a) ≫ d.inv.residueFieldMap a =
      (S.residueFieldCongr ha).hom :=
  (Scheme.residueFieldMap_comp d.inv d.hom a).symm.trans
    ((Scheme.Hom.residueFieldMap_congr d.inv_hom_id a).trans
      ((congrArg (fun q => (S.residueFieldCongr ha).hom ≫ q)
        (Scheme.residueFieldMap_id (X := S) a)).trans (Category.comp_id _)))

/-- **Pure transcendence of the residue field at the distinguished point survives an
isomorphism of the base.** The residue field of `y` is an algebra over the residue field of the
base point through the structure morphism; replacing the base by an isomorphic one replaces
that base field by an isomorphic one, compatibly with the two algebra structures. -/
lemma purelyTranscendental_residueField_of_baseIso {Y S S' : Scheme.{u}} (d : S' ≅ S)
    (g : Y ⟶ S) (y : Y) {t : S} (ht : g y = t) {t' : S'} (hs : d.hom t' = t)
    (ht' : (g ≫ d.inv) y = t')
    (h : letI : Algebra (S.residueField t) (Y.residueField y) :=
        ((S.residueFieldCongr ht).inv ≫ g.residueFieldMap y).hom.toAlgebra
      PurelyTranscendental (S.residueField t) (Y.residueField y)) :
    letI : Algebra (S'.residueField t') (Y.residueField y) :=
        ((S'.residueFieldCongr ht').inv ≫ (g ≫ d.inv).residueFieldMap y).hom.toAlgebra
    PurelyTranscendental (S'.residueField t') (Y.residueField y) := by
  subst ht
  subst ht'
  set φold : S.residueField (g y) ⟶ Y.residueField y :=
    (S.residueFieldCongr (rfl : g y = g y)).inv ≫ g.residueFieldMap y with hφold
  set φnew : S'.residueField ((g ≫ d.inv) y) ⟶ Y.residueField y :=
    (S'.residueFieldCongr (rfl : (g ≫ d.inv) y = (g ≫ d.inv) y)).inv ≫
      (g ≫ d.inv).residueFieldMap y with hφnew
  set α : S.residueField (g y) ⟶ S'.residueField ((g ≫ d.inv) y) :=
    (S.residueFieldCongr hs).inv ≫ d.hom.residueFieldMap ((g ≫ d.inv) y) with hα
  have : IsIso α := by rw [hα]; infer_instance
  have hpath : α ≫ φnew = φold := by
    rw [hα, hφnew, hφold]
    simp only [Scheme.residueFieldCongr_refl, Iso.refl_inv, Category.id_comp, Category.assoc]
    have hs' : d.hom (d.inv (g y)) = g y := hs
    change (S.residueFieldCongr hs').inv ≫ d.hom.residueFieldMap (d.inv (g y)) ≫
        (g ≫ d.inv).residueFieldMap y = g.residueFieldMap y
    rw [Scheme.residueFieldMap_comp g d.inv y,
      ← Category.assoc (d.hom.residueFieldMap (d.inv (g y))),
      residueFieldMap_hom_comp_inv_of_iso d (g y) hs', Iso.inv_hom_id_assoc]
  let eBase := (asIso α).symm.commRingCatIsoToRingEquiv
  let : Algebra (S.residueField (g y)) (Y.residueField y) := φold.hom.toAlgebra
  let : Algebra (S'.residueField ((g ≫ d.inv) y)) (Y.residueField y) := φnew.hom.toAlgebra
  refine Stacks.Flatness.purelyTranscendental_of_ringEquiv_base eBase ?_ h
  intro a
  have hbase : α.hom (eBase a) = a := by
    change (asIso α).hom ((asIso α).inv a) = a
    exact (asIso α).inv_hom_id_apply a
  calc algebraMap (S'.residueField ((g ≫ d.inv) y)) (Y.residueField y) a
      = φnew.hom (α.hom (eBase a)) := by rw [hbase]; rfl
    _ = (α ≫ φnew).hom (eBase a) := rfl
    _ = φold.hom (eBase a) := congrArg
        (fun q : S.residueField (g y) ⟶ Y.residueField y => q.hom (eBase a)) hpath
    _ = algebraMap (S.residueField (g y)) (Y.residueField y) (eBase a) := rfl

/-! ### One-step dévissages under an isomorphism of the base -/

section OneStep

variable {X S S' : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
  [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent] [ht : F.IsFiniteType]

/-- Postcomposing with the inverse of an isomorphism preserves being locally of finite type.
This is the instance found by type-class resolution, named so that the two places a chain
transport mentions it produce the same term. -/
lemma locallyOfFiniteType_comp_iso_inv {Y : Scheme.{u}} (g : Y ⟶ S) (d : S' ≅ S)
    (h : LocallyOfFiniteType g) : LocallyOfFiniteType (g ≫ d.inv) :=
  haveI := h
  inferInstance

/-- Invertibility of the inverse image of a morphism of modules over the residue field of a
point depends only on the point. -/
lemma isIso_pullback_map_fromSpecResidueField_congr {Y : Scheme.{u}} {M N : Y.Modules}
    (α : M ⟶ N) {a b : Y} (hab : a = b)
    (hα : IsIso ((Scheme.Modules.pullback (Y.fromSpecResidueField b)).map α)) :
    IsIso ((Scheme.Modules.pullback (Y.fromSpecResidueField a)).map α) := by
  subst hab
  exact hα

/-- An isomorphism of schemes carries the generic point of its target to the generic point of
its source. -/
lemma isGenericPoint_iso_inv {A B : Scheme.{u}} (φ : A ≅ B) {ξ : B}
    (hξ : IsGenericPoint ξ Set.univ) : IsGenericPoint ((φ.inv : B → A) ξ) Set.univ :=
  isGenericPoint_univ_map_of_surjective φ.inv.continuous φ.inv.surjective hξ

/-- A one-step dévissage is carried along an isomorphism `d : S' ≅ S` of its base matching `s'`
with `s`. The closed subscheme, the smooth scheme, the closed immersion, the finite morphism
and the module on the closed subscheme are unchanged; the two structure morphisms are composed
with `d.inv`. -/
def OneStepDevissage.ofBaseIso (d : S' ≅ S) {s : S} {s' : S'} (hs : d.hom s' = s)
    (D : OneStepDevissage f F s) : OneStepDevissage (f ≫ d.inv) F s' where
  Z := D.Z
  Y := D.Y
  i := D.i
  π := D.π
  g := D.g ≫ d.inv
  G := D.G
  quasi_coherent_G := D.quasi_coherent_G
  finite_type_G := D.finite_type_G
  over_base := by
    simpa only [Category.assoc] using congrArg (fun k : D.Z ⟶ S => k ≫ d.inv) D.over_base
  affine_X := D.affine_X
  affine_S :=
    haveI := D.affine_S
    IsAffine.of_isIso d.hom
  affine_Z := D.affine_Z
  affine_Y := D.affine_Y
  closed_immersion := D.closed_immersion
  finite_presentation := D.finite_presentation
  module_iso := D.module_iso
  finite := D.finite
  smooth :=
    MorphismProperty.of_isPullback (isPullback_of_baseIso (f := D.g) d (by simp))
      (P := @Smooth) D.smooth
  geometrically_irreducible :=
    MorphismProperty.of_isPullback (isPullback_of_baseIso (f := D.g) d (by simp))
      (P := @GeometricallyIrreducible) D.geometrically_irreducible
  fiber_dimension := fun t => by
    rw [topologicalKrullDim_fiber_of_baseIso (f := D.g) d (by simp) t]
    refine (D.fiber_dimension (d.hom t)).trans ?_
    exact (topologicalKrullDim_fiberSupport_of_baseIso d (by simp) hs F).symm

@[simp] lemma OneStepDevissage.ofBaseIso_Z (d : S' ≅ S) {s : S} {s' : S'} (hs : d.hom s' = s)
    (D : OneStepDevissage f F s) : (D.ofBaseIso d hs).Z = D.Z := rfl

@[simp] lemma OneStepDevissage.ofBaseIso_Y (d : S' ≅ S) {s : S} {s' : S'} (hs : d.hom s' = s)
    (D : OneStepDevissage f F s) : (D.ofBaseIso d hs).Y = D.Y := rfl

@[simp] lemma OneStepDevissage.ofBaseIso_i (d : S' ≅ S) {s : S} {s' : S'} (hs : d.hom s' = s)
    (D : OneStepDevissage f F s) : (D.ofBaseIso d hs).i = D.i := rfl

@[simp] lemma OneStepDevissage.ofBaseIso_π (d : S' ≅ S) {s : S} {s' : S'} (hs : d.hom s' = s)
    (D : OneStepDevissage f F s) : (D.ofBaseIso d hs).π = D.π := rfl

@[simp] lemma OneStepDevissage.ofBaseIso_g (d : S' ≅ S) {s : S} {s' : S'} (hs : d.hom s' = s)
    (D : OneStepDevissage f F s) : (D.ofBaseIso d hs).g = D.g ≫ d.inv := rfl

@[simp] lemma OneStepDevissage.ofBaseIso_G (d : S' ≅ S) {s : S} {s' : S'} (hs : d.hom s' = s)
    (D : OneStepDevissage f F s) : (D.ofBaseIso d hs).G = D.G := rfl

/-- A one-step dévissage at a point is carried along an isomorphism of its base; the base point
of the transported dévissage is the image of the point under the new structure morphism. -/
def OneStepDevissageAt.ofBaseIso (d : S' ≅ S) {x : X} (D : OneStepDevissageAt f F x) :
    OneStepDevissageAt (f ≫ d.inv) F x where
  toOneStepDevissage := D.toOneStepDevissage.ofBaseIso d (by simp)
  mem_fiber_support :=
    (mem_fiberSupport_iff_mem_fiberSupport f (f ≫ d.inv) F x).mp D.mem_fiber_support
  dimension :=
    (topologicalKrullDimAt_fiberSupport_of_baseIso d (by simp) F x
        ((mem_fiberSupport_iff_mem_fiberSupport f (f ≫ d.inv) F x).mp D.mem_fiber_support)
        D.mem_fiber_support).trans
      (D.dimension.trans
        (topologicalKrullDim_fiberSupport_of_baseIso d (by simp) (by simp) F).symm)
  z := D.z
  y := D.y
  i_z := D.i_z
  π_z := D.π_z
  g_y := congrArg (fun t : S => (d.inv : S → S') t) D.g_y
  fiber_eq_singleton := D.fiber_eq_singleton
  residueField_purelyTranscendental :=
    purelyTranscendental_residueField_of_baseIso d D.toOneStepDevissage.g D.y D.g_y (by simp)
      (congrArg (fun t : S => (d.inv : S → S') t) D.g_y)
      D.residueField_purelyTranscendental

/-- The one-step dévissage underlying the transport of a one-step dévissage at a point along an
isomorphism of the base is the transport of the underlying one-step dévissage. This is the
definitional equation the pointed stages are glued along. -/
lemma OneStepDevissageAt.ofBaseIso_toOneStepDevissage (d : S' ≅ S) {x : X}
    (hsx : d.hom ((f ≫ d.inv) x) = f x) (D : OneStepDevissageAt f F x) :
    (D.ofBaseIso d).toOneStepDevissage = D.toOneStepDevissage.ofBaseIso d hsx := rfl

/-- A stage of a complete dévissage is carried along an isomorphism of its base: the rank and
the free-module map are unchanged, and the generic point of the distinguished fibre is carried
by the comparison of the fibres. -/
def DevissageStage.ofBaseIso (d : S' ≅ S) {s : S} {s' : S'} (hs : d.hom s' = s)
    (D : DevissageStage f F s) : DevissageStage (f ≫ d.inv) F s' where
  oneStep := D.oneStep.ofBaseIso d hs
  rank := D.rank
  alpha := D.alpha
  genericPoint :=
    ((fiberIsoOfBaseIsoPoint (f := D.oneStep.g) d (by simp) hs).inv : _ → _) D.genericPoint
  genericPoint_spec := isGenericPoint_iso_inv _ D.genericPoint_spec
  genericFiber_isIso :=
    isIso_pullback_map_fromSpecResidueField_congr D.alpha
      (fiberIsoOfBaseIsoPoint_inv_fiberι (f := D.oneStep.g) d (by simp) hs D.genericPoint)
      D.genericFiber_isIso

@[simp] lemma DevissageStage.ofBaseIso_oneStep (d : S' ≅ S) {s : S} {s' : S'}
    (hs : d.hom s' = s) (D : DevissageStage f F s) :
    (D.ofBaseIso d hs).oneStep = D.oneStep.ofBaseIso d hs := rfl

@[simp] lemma DevissageStage.ofBaseIso_rank (d : S' ≅ S) {s : S} {s' : S'} (hs : d.hom s' = s)
    (D : DevissageStage f F s) : (D.ofBaseIso d hs).rank = D.rank := rfl

/-- The cokernel of the free-module map of a stage is unchanged by
`AlgebraicGeometry.DevissageStage.ofBaseIso`: the smooth scheme, the finite morphism, the module
on the closed subscheme and the free-module map are all untouched. -/
lemma DevissageStage.ofBaseIso_coker (d : S' ≅ S) {s : S} {s' : S'} (hs : d.hom s' = s)
    (D : DevissageStage f F s) : (D.ofBaseIso d hs).coker = D.coker := rfl

end OneStep

/-! ### Complete dévissages under an isomorphism of the base -/

section Chain

variable {S S' : Scheme.{u}} {s : S} {s' : S'}

/-- A chain of stages of a complete dévissage is carried along an isomorphism of its base. In
contrast with the transport along an isomorphism of the source, every stage changes: the
structure morphism of each smooth scheme is composed with `d.inv`. -/
def DevissageChain.ofBaseIso (d : S' ≅ S) (hs : d.hom s' = s) {X : Scheme.{u}} {f : X ⟶ S}
    {F : X.Modules} {hl : LocallyOfFiniteType f} {hq : F.IsQuasicoherent}
    {ht : F.IsFiniteType} (C : DevissageChain s X f F hl hq ht) :
    DevissageChain s' X (f ≫ d.inv) F (locallyOfFiniteType_comp_iso_inv f d hl) hq ht :=
  match C with
  | .last stage hzero =>
    letI := hl
    letI := hq
    letI := ht
    .last (stage.ofBaseIso d hs) hzero
  | .more stage hqC htC hlY tail =>
    letI := hl
    letI := hq
    letI := ht
    letI := hqC
    letI := htC
    .more (stage.ofBaseIso d hs) hqC htC
      (locallyOfFiniteType_comp_iso_inv stage.oneStep.g d hlY) (tail.ofBaseIso d hs)

/-- A complete dévissage of `F/X/S` over `s` is carried along an isomorphism of its base. -/
def NonemptyCompleteDevissage.ofBaseIso (d : S' ≅ S) (hs : d.hom s' = s) {X : Scheme.{u}}
    {f : X ⟶ S} {F : X.Modules} [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent]
    [ht : F.IsFiniteType] (D : NonemptyCompleteDevissage f F s) :
    @NonemptyCompleteDevissage X S' (f ≫ d.inv) F s'
      (locallyOfFiniteType_comp_iso_inv f d hl) hq ht :=
  ⟨D.chain.ofBaseIso d hs⟩

/-- The distinguished points of a stage survive the transport along an isomorphism of the base:
the one-step dévissage at the current point is transported by
`AlgebraicGeometry.OneStepDevissageAt.ofBaseIso`, and the smooth scheme, which carries the
distinguished target point, is unchanged. -/
def PointedDevissageStage.ofBaseIso (d : S' ≅ S) {X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] {x : X}
    (hs : d.hom s' = s) (hfx : f x = s) {stage : DevissageStage f F s}
    (P : PointedDevissageStage f F s x stage) :
    PointedDevissageStage (f ≫ d.inv) F s' x (stage.ofBaseIso d hs) where
  atPoint := P.atPoint.ofBaseIso d
  sameOneStep := by
    subst hfx
    obtain rfl : s' = (f ≫ d.inv) x := by
      have h1 : (d.hom ≫ d.inv) s' = s' := by rw [d.hom_inv_id]; simp
      change s' = (d.inv : S → S') (f x)
      rw [← hs]
      exact h1.symm
    exact heq_of_eq (congrArg (OneStepDevissage.ofBaseIso d hs) (eq_of_heq P.sameOneStep))
  y := P.y
  sameY := P.sameY

/-- The compatible distinguished points of a chain of stages survive the transport of the chain
along an isomorphism of the base. -/
def PointedDevissageChain.ofBaseIso (d : S' ≅ S) (hs : d.hom s' = s) {X : Scheme.{u}}
    {f : X ⟶ S} {F : X.Modules} {hl : LocallyOfFiniteType f} {hq : F.IsQuasicoherent}
    {ht : F.IsFiniteType} {x : X} (hfx : f x = s) {C : DevissageChain s X f F hl hq ht}
    (P : PointedDevissageChain s X f F hl hq ht x C) :
    PointedDevissageChain s' X (f ≫ d.inv) F (locallyOfFiniteType_comp_iso_inv f d hl) hq ht x
      (C.ofBaseIso d hs) :=
  match C, P with
  | .last _ _, .last _ stage hzero pointed =>
    letI := hl
    letI := hq
    letI := ht
    .last x (stage.ofBaseIso d hs) hzero (pointed.ofBaseIso d hs hfx)
  | .more _ _ _ _ _, .more _ stage hqC htC hlY tail pointed pt =>
    letI := hl
    letI := hq
    letI := ht
    letI := hqC
    letI := htC
    .more x (stage.ofBaseIso d hs) hqC htC
      (locallyOfFiniteType_comp_iso_inv stage.oneStep.g d hlY) (tail.ofBaseIso d hs)
      (pointed.ofBaseIso d hs hfx) (pt.ofBaseIso d hs (pointed.g_y hfx))

/-- A complete dévissage of `F/X/S` at `x` is carried along an isomorphism of its base. -/
def NonemptyCompleteDevissageAt.ofBaseIso (d : S' ≅ S) {X : Scheme.{u}} {f : X ⟶ S}
    {F : X.Modules} [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent]
    [ht : F.IsFiniteType] {x : X} (D : NonemptyCompleteDevissageAt f F x) :
    @NonemptyCompleteDevissageAt X S' (f ≫ d.inv) F x
      (locallyOfFiniteType_comp_iso_inv f d hl) hq ht where
  toNonemptyCompleteDevissage :=
    ⟨D.toNonemptyCompleteDevissage.chain.ofBaseIso d (by simp)⟩
  pointed := D.pointed.ofBaseIso d (by simp) rfl

/-- A complete dévissage of `F/X/S` at `x`, empty or not, is carried along an isomorphism of its
base. -/
def CompleteDevissageAt.ofBaseIso (d : S' ≅ S) {X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent] [ht : F.IsFiniteType] {x : X}
    (D : CompleteDevissageAt f F x) :
    @CompleteDevissageAt X S' (f ≫ d.inv) F x
      (locallyOfFiniteType_comp_iso_inv f d hl) hq ht :=
  match D with
  | .empty hzero => .empty hzero
  | .nonempty data => .nonempty (data.ofBaseIso d)

end Chain

/-! ### Isomorphisms of the base with a prescribed structure morphism -/

section BaseIsoHom

/-- A morphism to the new base which becomes the old one after the isomorphism of the bases is
the old one composed with the inverse of that isomorphism. -/
lemma eq_comp_inv_of_baseIso {X S S' : Scheme.{u}} {f : X ⟶ S} {f' : X ⟶ S'} (d : S' ≅ S)
    (hf : f' ≫ d.hom = f) : f ≫ d.inv = f' := by
  rw [← hf, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The identification of the inverse image of a module along the identity with the module,
in the spelling the transport along the identity isomorphism of the source asks for. -/
def pullbackReflIso (X : Scheme.{u}) (F : X.Modules) :
    (Scheme.Modules.pullback (Iso.refl X).hom).obj F ≅ F :=
  (Scheme.Modules.pullbackId X).app F

variable {X S S' : Scheme.{u}} {s : S} {s' : S'} {f : X ⟶ S} {f' : X ⟶ S'} {F : X.Modules}
  [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent] [ht : F.IsFiniteType]
  [hl' : LocallyOfFiniteType f']

/-- A chain of stages of a complete dévissage is carried along an isomorphism of its base to a
chain along any prescribed structure morphism over the new base: the canonical transport is
followed by the transport along the identity isomorphism of the source. -/
def DevissageChain.ofBaseIsoHom (d : S' ≅ S) (hs : d.hom s' = s) (hf : f' ≫ d.hom = f)
    (C : DevissageChain s X f F hl hq ht) : DevissageChain s' X f' F hl' hq ht :=
  letI := locallyOfFiniteType_comp_iso_inv f d hl
  (C.ofBaseIso d hs).ofSourceIso (Iso.refl X)
    ((Category.id_comp (f ≫ d.inv)).trans (eq_comp_inv_of_baseIso d hf)) (pullbackReflIso X F)

/-- A complete dévissage of `F/X/S` over `s` is carried along an isomorphism of its base to one
along any prescribed structure morphism over the new base. -/
def NonemptyCompleteDevissage.ofBaseIsoHom (d : S' ≅ S) (hs : d.hom s' = s)
    (hf : f' ≫ d.hom = f) (D : NonemptyCompleteDevissage f F s) :
    NonemptyCompleteDevissage f' F s' :=
  ⟨D.chain.ofBaseIsoHom d hs hf⟩

/-- The compatible distinguished points of a chain of stages survive the transport along an
isomorphism of the base to any prescribed structure morphism over the new base. -/
def PointedDevissageChain.ofBaseIsoHom (d : S' ≅ S) (hs : d.hom s' = s) (hf : f' ≫ d.hom = f)
    {x : X} (hfx : f x = s) {C : DevissageChain s X f F hl hq ht}
    (P : PointedDevissageChain s X f F hl hq ht x C) :
    PointedDevissageChain s' X f' F hl' hq ht x (C.ofBaseIsoHom d hs hf) :=
  letI := locallyOfFiniteType_comp_iso_inv f d hl
  (P.ofBaseIso d hs hfx).ofSourceIso (Iso.refl X)
    ((Category.id_comp (f ≫ d.inv)).trans (eq_comp_inv_of_baseIso d hf)) (pullbackReflIso X F)
    rfl
    (by
      have h1 : (d.hom ≫ d.inv) s' = s' := by rw [d.hom_inv_id]; rfl
      change (d.inv : S → S') (f x) = s'
      rw [hfx, ← hs]
      exact h1)

/-- A complete dévissage of `F/X/S` at `x` is carried along an isomorphism of its base to one
along any prescribed structure morphism over the new base. -/
def NonemptyCompleteDevissageAt.ofBaseIsoHom (d : S' ≅ S) (hf : f' ≫ d.hom = f) {x : X}
    (D : NonemptyCompleteDevissageAt f F x) : NonemptyCompleteDevissageAt f' F x where
  toNonemptyCompleteDevissage :=
    ⟨D.toNonemptyCompleteDevissage.chain.ofBaseIsoHom d
      (baseIso_hom_apply_of_baseIso d hf x) hf⟩
  pointed := D.pointed.ofBaseIsoHom d (baseIso_hom_apply_of_baseIso d hf x) hf rfl

/-- A complete dévissage of `F/X/S` at `x`, empty or not, is carried along an isomorphism of its
base to one along any prescribed structure morphism over the new base. -/
def CompleteDevissageAt.ofBaseIsoHom (d : S' ≅ S) (hf : f' ≫ d.hom = f) {x : X}
    (D : CompleteDevissageAt f F x) : CompleteDevissageAt f' F x :=
  match D with
  | .empty hzero => .empty hzero
  | .nonempty data => .nonempty (data.ofBaseIsoHom d hf)

end BaseIsoHom

end AlgebraicGeometry

end
