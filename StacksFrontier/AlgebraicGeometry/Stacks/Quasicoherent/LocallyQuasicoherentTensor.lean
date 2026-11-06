module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.SmallEtaleTensorProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.MixedTensorQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCover
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallToBigTopos
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.CategoryTheory.Sites.LocallySmallSheafification

/-!
# Tensor products of locally quasi-coherent modules (Stacks 06WM, clause (4))

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `F` and `G` be sheaves
of modules over its structure sheaf which are locally quasi-coherent in the sense of
Stacks 06WJ. Clause (4) of Stacks 06WM says that their tensor product, formed in
`Mod(𝒳_ét, 𝒪_𝒳)`, is again locally quasi-coherent.

Local quasi-coherence is a condition on the restrictions to the small étale sites of the
schemes below the objects of `𝒳`, so the proof is a commutation: the restriction at an object
`x` of the tensor product of `F` and `G` is the tensor product, formed on the small étale site
of the scheme below `x`, of the restrictions of `F` and of `G`. The tensor product on a site is
the sheafification of the objectwise one, and the commutation splits accordingly. The objectwise
half is sectionwise and definitional once the scalars have been moved, which is
`PresheafOfModules.restrictScalarsTensorObjIso`. The sheafification half holds because the
restriction functor of Stacks 06W1 is continuous *and* cocontinuous for the small étale and the
associated étale topologies, so the restricted sheafification unit is still locally bijective,
and sheafification of presheaves of modules is the localization at the locally bijective maps;
that is `Stacks.SheafOfModules.sheafificationRestrictScalarsPushforwardIso`. Quasi-coherence of
the resulting tensor product on the small étale site is then the ringed-site statement
`Stacks.Modules.isQuasicoherentOnSite_sheafificationTensorObjUlift`.

## Main definitions

* `PresheafOfModules.restrictScalarsTensorObjIso`: restriction of scalars along an isomorphism
  of presheaves of commutative rings commutes with the objectwise tensor product.
* `Stacks.SheafOfModules.sheafificationRestrictScalarsPushforwardIso`: restriction along a
  continuous cocontinuous functor of sites, followed by a change of scalars, carries the
  sheafification of a presheaf of modules to the sheafification of the restriction.
* `AlgebraicGeometry.Stack.etaleTensorSheaf`: the tensor product of two sheaves of modules on
  the associated étale site of a category fibred in groupoids.
* `AlgebraicGeometry.Stack.restrictModuleTensorObjIso`: restriction to a small étale site
  carries an objectwise tensor product to the objectwise tensor product of the restrictions.
* `AlgebraicGeometry.Stack.restrictModuleEtaleTensorSheafIso`: restriction to a small étale site
  carries the tensor product to the tensor product of the restrictions.

## Main results

* `AlgebraicGeometry.Stack.isContinuous_and_isCocontinuous_restrictToSmallEtale`: the
  restriction functor of Stacks 06W1 is continuous and cocontinuous for the small étale
  topology and the associated étale topology.
* `AlgebraicGeometry.Stack.isSheaf_restrictModule_etaleTensorSheaf`: the restriction of the
  tensor product to the small étale site of the scheme below an object is a sheaf there.
* `AlgebraicGeometry.Stack.hasSheafify_etaleAssociatedTopology` and
  `AlgebraicGeometry.Stack.wEqualsLocallyBijective_etaleAssociatedTopology`: abelian presheaves on
  the associated étale site of `𝒳` sheafify, with locally bijective weak equivalences.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_tensorSheaf`: **Stacks 06WM, clause (4)**.

## Implementation notes

This file proves clause (4) of Stacks 06WM. Clauses (1) to (3) — colimits, the abelian
structure, two-out-of-three in a short exact sequence — are in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentClosure`, and clause (5),
internal homs, in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentInternalHom`.  Clauses
(2) and (3) are also reached a second way, through the closure instances that make local
quasi-coherence a weak Serre class, in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentWeakSerre`, which reuses
`AlgebraicGeometry.Stack.isContinuous_and_isCocontinuous_restrictToSmallEtale` from this file.

The statements of the isomorphisms that make up the restriction comparison are written through
`AlgebraicGeometry.Stack.restrictModuleToSmallEtale` and
`AlgebraicGeometry.Stack.etaleTensorSheaf` rather than spelled out as pushforwards, changes of
scalars and sheafifications. That is not cosmetic. `AlgebraicGeometry.Stack.structureSheaf` and
its ring form `AlgebraicGeometry.Stack.ringStructureSheafCore` are built by tactic blocks, so
leaving a comparison of their presheaves to unification makes `whnf` unfold a tactic-generated
term, which costs several times the default heartbeat budget. Naming each spelling and composing
the named isomorphisms in term mode confines that identification to one declaration apiece.

The tensor product is a sheafification, so forming it needs sheafification of abelian presheaves
on the associated étale site, and the comparison with the small étale site needs its weak
equivalences to be the locally bijective maps. Both hold with no hypothesis on `𝒳`: every slice
`𝒳/x` is essentially small in the universe of the schemes by Stacks 06W0, which is what
`AlgebraicGeometry.Stack.hasSheafify_etaleAssociatedTopology` and
`AlgebraicGeometry.Stack.wEqualsLocallyBijective_etaleAssociatedTopology` consume. The
intermediate comparisons are stated over those two instances as instance arguments; the statement
of clause (4) supplies them itself. On the small étale site, which is always essentially small,
they are `AlgebraicGeometry.smallEtale_hasSheafify` and
`AlgebraicGeometry.smallEtale_wEqualsLocallyBijective`.

The universe of the sections is the universe `u` of the schemes, and the ringed-site input is
the mixed-universe statement
`Stacks.Modules.isQuasicoherentOnSite_sheafificationTensorObjUlift` rather than the
single-universe `Stacks.SheafOfModules.isQuasicoherentOnSite_tensorSheaf`. That is forced: the
objects of the small étale site of a scheme lie in `Type (u + 1)`, and the single-universe
statement needs the coefficient rings to lie in a universe containing the objects of the site,
which `u` does not. The mixed statement asks instead that the *sets* of sections of the
structure sheaf form a sheaf, which on the small étale site is
`AlgebraicGeometry.SmallEtale.structure_isSheaf` pushed through
`CategoryTheory.hasSheafCompose_forget_ringCat_of_essentiallySmall`.

`AlgebraicGeometry.Stack.structureRingPresheaf_isSheaf` identifies the coefficient sheaf of
rings of the associated site with the structure sheaf of a ringed site, which is what makes the
Tag 05NA tensor product applicable. The same identification is made in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FibredTensorProduct.lean` for the
five-valued `AlgebraicGeometry.SiteKind` presentation of the five associated topologies; the one
here is for the presentation by an arbitrary topology on the underlying category of schemes
coarser than the fppf one, which is the presentation local quasi-coherence is stated in.

`Stacks.SheafOfModules.sheafificationRestrictScalarsPushforwardIso` generalizes
`Stacks.SliceAlgebra.sheafificationRestrictionIso`, which is the case of no change of scalars:
here the source site carries a second sheaf of rings, mapping to the restriction of the one
downstairs, and the modules are taken over it. That generality is what the restriction of
Stacks 06W1 needs, its two structure presheaves being identified by an isomorphism and not an
equality.

## References

* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06W1](https://stacks.math.columbia.edu/tag/06W1)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

open scoped TensorProduct

universe u v w u₁ v₁ u₂ v₂ r m

namespace AlgebraicGeometry

/-- The topology of the big étale category over a scheme contained in a big étale site is the
localization, at that scheme, of the topology generated by the comap of the étale precoverage of
all schemes. -/
theorem bigEtaleOver_topology_eq_comap (E : BigEtaleSite.{u}) (U : Scheme.{u})
    (hU : E.Contains U) :
    BigEtaleOver.topology E U hU =
      (Scheme.etalePrecoverage.comap E.inclusion).toGrothendieck.over (E.obj U hU) := by
  rw [bigEtaleOver_topology_eq E U hU]
  exact congrArg (fun J : GrothendieckTopology E.Scheme => J.over (E.obj U hU))
    (congrArg Precoverage.toGrothendieck (bigEtalePrecoverage_eq_comap E))

/-- Changing the size cutoff of the bounded category of schemes along an equality of cardinals
is continuous and cocontinuous for the étale topologies localized at a scheme, both halves
being trivial: the change of category is the identity functor. -/
theorem isContinuous_and_isCocontinuous_overPost_ιOfLE {κ κ' : Cardinal.{u}} (hκ : κ = κ')
    (U : Scheme.{u}) (hU : U.size < κ) :
    let F := ObjectProperty.ιOfLE (P := schemeSizeBelow κ) (P' := schemeSizeBelow κ')
      (by intro X hX; simpa [hκ] using hX)
    let J := (Scheme.etalePrecoverage.comap (schemeBelowInclusion κ)).toGrothendieck
    let K := (Scheme.etalePrecoverage.comap (schemeBelowInclusion κ')).toGrothendieck
    (Over.post (X := ⟨U, hU⟩) F).IsContinuous (J.over ⟨U, hU⟩) (K.over (F.obj ⟨U, hU⟩)) ∧
      (Over.post (X := ⟨U, hU⟩) F).IsCocontinuous (J.over ⟨U, hU⟩)
        (K.over (F.obj ⟨U, hU⟩)) := by
  subst hκ
  dsimp only
  let J := ((Scheme.etalePrecoverage.comap (schemeBelowInclusion κ)).toGrothendieck).over
    (⟨U, hU⟩ : SchemeBelow κ)
  show (𝟭 (Over (⟨U, hU⟩ : SchemeBelow κ))).IsContinuous J J ∧
    (𝟭 (Over (⟨U, hU⟩ : SchemeBelow κ))).IsCocontinuous J J
  exact ⟨inferInstance, inferInstance⟩

/-- The inclusion of the small étale site of a scheme into the big étale category over it is
continuous and cocontinuous: it is, up to isomorphism, the postcomposition functor of
Stacks 021F along the identity, which is both. -/
theorem isContinuous_and_isCocontinuous_smallEtaleInclusionOver (E : BigEtaleSite.{u})
    (U : Scheme.{u}) (hU : E.Contains U) :
    (SmallEtale.inclusion E U hU).IsContinuous (SmallEtale.topology E U hU)
        (BigEtaleOver.topology E U hU) ∧
      (SmallEtale.inclusion E U hU).IsCocontinuous (SmallEtale.topology E U hU)
        (BigEtaleOver.topology E U hU) := by
  let i := SmallEtale.inclusion E U hU
  have hi : smallEtaleToBigEtaleFunctor E (E.obj U hU) (E.obj U hU) (𝟙 (E.obj U hU)) ≅ i :=
    Functor.isoWhiskerLeft i (Over.mapId (E.obj U hU)) ≪≫ Functor.rightUnitor i
  have hc := smallEtaleToBigEtaleFunctor_isContinuous E (E.obj U hU) (E.obj U hU)
    (𝟙 (E.obj U hU))
  have hcc := smallEtaleToBigEtaleFunctor_isCocontinuous E (E.obj U hU) (E.obj U hU)
    (𝟙 (E.obj U hU))
  exact ⟨Functor.isContinuous_of_iso hi _ _, Functor.IsCocontinuous.of_iso hi⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.Stack

/-- The change of size cutoff from a big étale site to a big fppf site with the same cutoff is
continuous and cocontinuous from the big étale topology over a scheme to the localized big étale
topology of the fppf site: both topologies are generated by the comap of the étale precoverage
of all schemes, and the cutoffs agree. -/
theorem isContinuous_and_isCocontinuous_overPost_cutoff (B : BigFppfSite.{u})
    (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff) (U : Scheme.{u}) (hU : E.Contains U) :
    let F := ObjectProperty.ιOfLE (P := schemeSizeBelow E.cutoff)
      (P' := schemeSizeBelow B.cutoff) (by intro X hX; simpa [h] using hX)
    (Over.post (X := E.obj U hU) F).IsContinuous (BigEtaleOver.topology E U hU)
        ((etaleTopology B).over (B.obj (show B.Contains U from by simpa [h] using hU))) ∧
      (Over.post (X := E.obj U hU) F).IsCocontinuous (BigEtaleOver.topology E U hU)
        ((etaleTopology B).over (B.obj (show B.Contains U from by simpa [h] using hU))) := by
  dsimp only
  rw [bigEtaleOver_topology_eq_comap E U hU, etaleTopology_eq_comap B]
  exact isContinuous_and_isCocontinuous_overPost_ιOfLE h U hU

/-- The small étale inclusion of Stacks 06W1 is continuous and cocontinuous from the small
étale topology of `U` to the big étale topology of the fppf site localized at `U`: it is the
inclusion into the big étale category over `U` followed by the change of size cutoff. -/
theorem isContinuous_and_isCocontinuous_smallEtaleInclusion (B : BigFppfSite.{u})
    (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff) (U : Scheme.{u}) (hU : E.Contains U) :
    (smallEtaleInclusion B E h U hU).IsContinuous (SmallEtale.topology E U hU)
        ((etaleTopology B).over (B.obj (show B.Contains U from by simpa [h] using hU))) ∧
      (smallEtaleInclusion B E h U hU).IsCocontinuous (SmallEtale.topology E U hU)
        ((etaleTopology B).over (B.obj (show B.Contains U from by simpa [h] using hU))) := by
  let F := ObjectProperty.ιOfLE (P := schemeSizeBelow E.cutoff)
    (P' := schemeSizeBelow B.cutoff) (by intro X hX; simpa [h] using hX)
  let i := SmallEtale.inclusion E U hU
  let J := SmallEtale.topology E U hU
  let K := BigEtaleOver.topology E U hU
  let L := (etaleTopology B).over (B.obj (show B.Contains U from by simpa [h] using hU))
  obtain ⟨hi₁, hi₂⟩ := isContinuous_and_isCocontinuous_smallEtaleInclusionOver E U hU
  obtain ⟨hj₁, hj₂⟩ := isContinuous_and_isCocontinuous_overPost_cutoff B E h U hU
  exact ⟨Functor.isContinuous_comp i (Over.post F) J K L,
    isCocontinuous_comp i (Over.post F) J K (L := L)⟩

/-- **Stacks 06W1.** The restriction functor from the small étale site of the scheme below an
object `x` to the fibred category is continuous and cocontinuous for the small étale topology
and the associated étale topology.

Continuity is what makes the restriction of an étale sheaf a sheaf, as in
`AlgebraicGeometry.Stack.restrictToSmallEtale_isSheaf`. Cocontinuity is what makes restriction
commute with sheafification, and so with the tensor product. Both are assembled from the small
étale inclusion and the localization equivalence of Stacks 06W0, whose quasi-inverse is a dense
subsite inclusion for the two localized topologies. -/
theorem isContinuous_and_isCocontinuous_restrictToSmallEtale (B : BigFppfSite.{u})
    (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (x : 𝒳) :
    letI := isEquivalence_overPost B S hS p hp x
    let q := smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
      (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget x
    let J := SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)
    let K := associatedTopology B S hS p (etaleTopology B)
    q.IsContinuous J K ∧ q.IsCocontinuous J K := by
  let hx := isEquivalence_overPost B S hS p hp x
  dsimp only
  let hU : E.Contains (p.obj x).left.1 := contains_base B E h S hS p x
  let i := smallEtaleInclusion B E h (p.obj x).left.1 hU
  let b := Over.post (X := x) (p ⋙ Over.forget (B.obj hS))
  let J := SmallEtale.topology E (p.obj x).left.1 hU
  let K := associatedTopology B S hS p (etaleTopology B)
  let L := (etaleTopology B).over (p.obj x).left
  obtain ⟨hi₁, hi₂⟩ :=
    isContinuous_and_isCocontinuous_smallEtaleInclusion B E h (p.obj x).left.1 hU
  have h₁ : i.IsContinuous J L := hi₁
  have h₂ : i.IsCocontinuous J L := hi₂
  have h₃ : b.IsDenseSubsite (K.over x) L := by
    rw [← inducedTopology_overPost B S hS p hp (etaleTopology B) x]
    infer_instance
  have h₄ : b.inv.IsDenseSubsite L (K.over x) := by
    rw [← inducedTopology_overPost B S hS p hp (etaleTopology B) x]
    exact (inferInstance : b.asEquivalence.symm.functor.IsDenseSubsite L
      (b.asEquivalence.symm.inverse.inducedTopology L))
  have h₅ : (b.inv ⋙ Over.forget x).IsContinuous L K :=
    Functor.isContinuous_comp _ _ L (K.over x) K
  have h₆ : (b.inv ⋙ Over.forget x).IsCocontinuous L K :=
    isCocontinuous_comp _ _ L (K.over x) (L := K)
  exact ⟨Functor.isContinuous_comp _ _ J L K, isCocontinuous_comp _ _ J L (L := K)⟩

end AlgebraicGeometry.Stack

namespace ModuleCat

/-- An isomorphism of rings identifies the tensor product of two modules over the target with
the tensor product, over the source, of their restrictions of scalars: both are the tensor
product of the same two abelian groups, the scalars acting through the isomorphism. -/
noncomputable def restrictScalarsTensorEquiv (A A' : CommRingCat.{r})
    (e : (forget₂ CommRingCat RingCat).obj A ≅ (forget₂ CommRingCat RingCat).obj A')
    (M N : ModuleCat.{r} A') :
    (ModuleCat.restrictScalars e.hom.hom).obj M ⊗[A]
        (ModuleCat.restrictScalars e.hom.hom).obj N ≃ₗ[A]
      (ModuleCat.restrictScalars e.hom.hom).obj (M ⊗ N) := by
  let er := e.ringCatIsoToRingEquiv
  letI : RingHomInvPair er.toRingHom er.symm.toRingHom :=
    ⟨er.symm_toRingHom_comp_toRingHom, er.toRingHom_comp_symm_toRingHom⟩
  letI : RingHomInvPair er.symm.toRingHom er.toRingHom :=
    ⟨er.toRingHom_comp_symm_toRingHom, er.symm_toRingHom_comp_toRingHom⟩
  let f : (ModuleCat.restrictScalars e.hom.hom).obj M ≃ₛₗ[er.toRingHom] M :=
    { Equiv.refl _ with map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let g : (ModuleCat.restrictScalars e.hom.hom).obj N ≃ₛₗ[er.toRingHom] N :=
    { Equiv.refl _ with map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let t := TensorProduct.congr (R := A) (R₂ := A') (σ₁₂ := er.toRingHom) f g
  exact { __ := t.toAddEquiv, map_smul' := t.map_smul' }

end ModuleCat

namespace PresheafOfModules

/-- Restriction of scalars along an isomorphism of presheaves of commutative rings commutes with
the objectwise tensor product of presheaves of modules: on sections it is
`ModuleCat.restrictScalarsTensorEquiv`, and the restriction maps agree on pure tensors by
construction. -/
noncomputable def restrictScalarsTensorObjIso {C : Type u₁} [Category.{v₁} C]
    (R R' : Cᵒᵖ ⥤ CommRingCat.{r})
    (e : R ⋙ forget₂ CommRingCat RingCat ≅ R' ⋙ forget₂ CommRingCat RingCat)
    (M N : PresheafOfModules.{r} (R' ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModules.restrictScalars e.hom).obj M ⊗
        (PresheafOfModules.restrictScalars e.hom).obj N ≅
      (PresheafOfModules.restrictScalars e.hom).obj (M ⊗ N) := by
  refine PresheafOfModules.isoMk (fun X =>
    (ModuleCat.restrictScalarsTensorEquiv (R.obj X) (R'.obj X) (e.app X)
      (M.obj X) (N.obj X)).toModuleIso) ?_
  intro X Y f
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a b
  change ModuleCat.restrictScalarsTensorEquiv (R.obj Y) (R'.obj Y) (e.app Y)
      (M.obj Y) (N.obj Y) (M.map f a ⊗ₜ[R.obj Y] N.map f b) =
    (M ⊗ N).map f (ModuleCat.restrictScalarsTensorEquiv (R.obj X) (R'.obj X) (e.app X)
      (M.obj X) (N.obj X) (a ⊗ₜ[R.obj X] b))
  rfl

/-- The universe lift of the sections of a presheaf of modules into a universe they already lie
in is isomorphic to the presheaf itself. -/
noncomputable def uliftObjSelfIso {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{r}}
    (M : PresheafOfModules.{m} R) : M.uliftObj.{_, _, _, _, m} ≅ M :=
  PresheafOfModules.isoMk (fun X => (ULift.moduleEquiv (R := R.obj X)).toModuleIso)
    (fun {X Y} f => by ext a; rfl)

end PresheafOfModules

namespace Stacks.SheafOfModules

/-- **Restriction along a continuous cocontinuous functor of sites, followed by a change of
scalars, carries the sheafification of a presheaf of modules to the sheafification of the
restriction.** The restriction of the sheafification unit is still locally bijective on sections,
because restriction along a cocontinuous functor preserves local injectivity and local
surjectivity, and sheafification of presheaves of modules is the localization at the maps that
are locally bijective on sections; so the sheafification of the restriction is the restriction,
which is already a sheaf by continuity.

The change of scalars is along an arbitrary morphism from a sheaf of rings on the source site to
the restriction of the one on the target site; it is invisible on sections, which is why it does
not enter the argument. -/
noncomputable def sheafificationRestrictScalarsPushforwardIso {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (q : C ⥤ D) [q.IsContinuous J K] [q.IsCocontinuous J K]
    (S : Sheaf J RingCat.{r}) (R : Sheaf K RingCat.{r}) (α : S.obj ⟶ q.op ⋙ R.obj)
    [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify K AddCommGrpCat.{m}] [K.WEqualsLocallyBijective AddCommGrpCat.{m}]
    (M : PresheafOfModules.{m} R.obj) :
    (PresheafOfModules.sheafification (R := S) (𝟙 S.obj)).obj
        ((PresheafOfModules.pushforward₀ q R.obj ⋙
          PresheafOfModules.restrictScalars α).obj M) ≅
      (⟨(PresheafOfModules.pushforward₀ q R.obj ⋙
            PresheafOfModules.restrictScalars α).obj
          ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj M).val,
        q.op_comp_isSheaf_of_isSheaf J K _
          ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj M).isSheaf⟩ :
        SheafOfModules S) := by
  let P := PresheafOfModules.pushforward₀ q R.obj ⋙ PresheafOfModules.restrictScalars α
  let H := (PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj M
  let H' : SheafOfModules S := ⟨P.obj H.val, q.op_comp_isSheaf_of_isSheaf J K _ H.isSheaf⟩
  let η := (PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 R.obj)).unit.app M
  let μ : P.obj M ⟶ H'.val := P.map η
  have hμ : J.W ((PresheafOfModules.toPresheaf S.obj).map μ) := by
    change J.W (Functor.whiskerLeft q.op (CategoryTheory.toSheafify K M.presheaf))
    have h₁ : Presheaf.IsLocallyInjective K (CategoryTheory.toSheafify K M.presheaf) :=
      (K.W_toSheafify M.presheaf).isLocallyInjective
    have h₂ : Presheaf.IsLocallySurjective K (CategoryTheory.toSheafify K M.presheaf) :=
      (K.W_toSheafify M.presheaf).isLocallySurjective
    have h₃ := Presheaf.isLocallyInjective_whisker J K q
      (CategoryTheory.toSheafify K M.presheaf)
    have h₄ := Presheaf.isLocallySurjective_whisker J K q
      (CategoryTheory.toSheafify K M.presheaf)
    exact J.W_of_isLocallyBijective _
  let L := PresheafOfModules.sheafification (R := S) (𝟙 S.obj)
  haveI : IsIso (L.map μ) := by
    rw [← MorphismProperty.isomorphisms.iff]
    exact (congrArg (fun W => W μ)
      (PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
        (R := S) (𝟙 S.obj))).mp hμ
  exact asIso (L.map μ) ≪≫
    (asIso ((PresheafOfModules.sheafificationAdjunction (R := S) (𝟙 S.obj)).counit)).app H'

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Stack

open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The ring presheaf underlying the commutative structure sheaf of an associated site of the
fibred category is a sheaf for that topology: it is the coefficient sheaf of rings of
Stacks 06TV. Naming the identification is what makes the Tag 05NA tensor product applicable to
the associated site. -/
theorem structureRingPresheaf_isSheaf (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    Presheaf.IsSheaf (associatedTopology B S hS p τ)
      (structureRingPresheaf (structureSheaf B S hS p hp τ hτ).obj) :=
  (ringStructureSheafCore B S hS p hp τ hτ).property

/-- The tensor product, in the category of sheaves of modules on the associated étale site of a
category fibred in groupoids, of two sheaves of modules over its structure sheaf: the
sheafification, for that topology, of their objectwise tensor product.

This is the tensor product of Tag 05NA formed at the structure sheaf of the associated étale
site, written out as the sheafification of the objectwise tensor product rather than through
the canonical bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor`;
`AlgebraicGeometry.Stack.etaleTensorSheaf_eq` records that the two spellings agree. Writing it
out is what lets the restriction comparison below be applied without unfolding anything. -/
noncomputable def etaleTensorSheaf
    [HasWeakSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
    [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))) :
    SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)) :=
  (PresheafOfModules.sheafification
      (R := ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))
      (𝟙 (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)).obj)).obj
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      F.val G.val)

/-- The tensor product on the associated étale site is the tensor product of Tag 05NA, formed at
the structure sheaf of that site. -/
theorem etaleTensorSheaf_eq
    [HasWeakSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
    [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))) :
    etaleTensorSheaf B S hS p hp F G =
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        (structureSheaf B S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B))).obj F).obj G :=
  rfl

/-- The presheaf of commutative rings of global functions on the small étale site of the scheme
below an object `x`: the structure sheaf of that site of Stacks 03DU, before commutativity is
forgotten.

Its composite with `CategoryTheory.forget₂ CommRingCat RingCat` is the underlying presheaf of
`AlgebraicGeometry.SmallEtale.structureSheaf`, so it is the coefficient presheaf of the ringed
site whose quasi-coherent modules local quasi-coherence refers to. -/
noncomputable abbrev localCommStructurePresheaf (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
    (x : 𝒳) :
    (SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x))ᵒᵖ ⥤ CommRingCat.{u} :=
  ((SmallEtale.inclusion E (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
    Over.post E.inclusion) ⋙ Over.forget (p.obj x).left.1).op ⋙ Scheme.Γ

/-- The restriction to the small étale site of the scheme below an object `x` carries the
objectwise tensor product of two presheaves of modules on the associated étale site to the
objectwise tensor product there of their restrictions.

Restriction along the functor of Stacks 06W1 is sectionwise, and restriction of scalars along
the isomorphism `AlgebraicGeometry.Stack.localStructurePresheafIso` of the two structure
presheaves commutes with the objectwise tensor product by
`PresheafOfModules.restrictScalarsTensorObjIso`; the universe lift of the sections is removed by
`PresheafOfModules.uliftObjSelfIso`.

Both sides are written through `AlgebraicGeometry.Stack.restrictModuleToSmallEtale` rather than
spelled out as a pushforward followed by a change of scalars. That is what keeps the consumers
cheap: identifying the two spellings of the restriction forces the unfolding of the tactic-built
`AlgebraicGeometry.Stack.ringStructureSheafCore`, and this declaration pays for it once. -/
noncomputable def restrictModuleTensorObjIso (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
    (x : 𝒳)
    (F G : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj) :
    (PresheafOfModules.tensorObj
        (O := localCommStructurePresheaf B S hS p E h x)
        (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
          (etaleTopology_le_topology B) F)
        (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
          (etaleTopology_le_topology B) G)).uliftSections.{u} ≅
      restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B)
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj
          (R := (structureSheaf B S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B)).obj) F G) :=
  letI := isEquivalence_overPost B S hS p hp x
  PresheafOfModules.uliftObjSelfIso _ ≪≫
    PresheafOfModules.restrictScalarsTensorObjIso
      (localCommStructurePresheaf B S hS p E h x)
      ((smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
        (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget x).op ⋙
        (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      (localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B)) _ _

/-- The restriction of the tensor product to the small étale site of the scheme below an object
`x` is a sheaf there: the restriction functor of Stacks 06W1 is continuous for the small étale
topology and the associated étale topology, and moving the scalars does not change the
sections. -/
theorem isSheaf_restrictModule_etaleTensorSheaf
    (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
    [HasWeakSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
    [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (x : 𝒳) :
    Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) (etaleTensorSheaf B S hS p hp F G).val).presheaf := by
  let hx := isEquivalence_overPost B S hS p hp x
  obtain ⟨hq₁, -⟩ := isContinuous_and_isCocontinuous_restrictToSmallEtale B E h S hS p hp x
  rw [restrictModuleToSmallEtale_presheaf]
  exact (smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
      (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv ⋙
        Over.forget x).op_comp_isSheaf_of_isSheaf _ _ _
    (etaleTensorSheaf B S hS p hp F G).isSheaf

/-- Sheafifying the restricted objectwise tensor product on the small étale site of the scheme
below an object `x` gives the restriction of the tensor product formed on the associated étale
site.

This is `Stacks.SheafOfModules.sheafificationRestrictScalarsPushforwardIso` for the restriction
functor of Stacks 06W1, which is continuous and cocontinuous by
`AlgebraicGeometry.Stack.isContinuous_and_isCocontinuous_restrictToSmallEtale`, applied to the
objectwise tensor product. -/
noncomputable def sheafificationRestrictModuleTensorObjIso
    (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
    [HasWeakSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
    [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (x : 𝒳) :
    (PresheafOfModules.sheafification
        (R := SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x))
        (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1
          (contains_base B E h S hS p x)).obj)).obj
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B)
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj
          (R := (structureSheaf B S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B)).obj) F.val G.val)) ≅
      (⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
            (etaleTopology_le_topology B) (etaleTensorSheaf B S hS p hp F G).val,
          isSheaf_restrictModule_etaleTensorSheaf B S hS p hp E h F G x⟩ :
        SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
          (contains_base B E h S hS p x))) := by
  let hx := isEquivalence_overPost B S hS p hp x
  let K := associatedTopology B S hS p (etaleTopology B)
  let J := SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)
  let q := smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget x
  obtain ⟨hq₁, hq₂⟩ := isContinuous_and_isCocontinuous_restrictToSmallEtale B E h S hS p hp x
  have hqc : q.IsContinuous J K := hq₁
  have hqcc : q.IsCocontinuous J K := hq₂
  exact Stacks.SheafOfModules.sheafificationRestrictScalarsPushforwardIso J K q
    (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x))
    (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))
    (localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B)).hom
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (structureSheaf B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)).obj) F.val G.val)

/-- The restriction to the small étale site of the scheme below an object `x` of the tensor
product formed on the associated étale site is the tensor product, formed on that small étale
site, of the restrictions of the two factors.

Both tensor products are the sheafification of an objectwise tensor product, and the
commutation splits accordingly: `AlgebraicGeometry.Stack.restrictModuleTensorObjIso` for the
objectwise half and `AlgebraicGeometry.Stack.sheafificationRestrictModuleTensorObjIso` for the
sheafification half. -/
noncomputable def restrictModuleEtaleTensorSheafIso
    (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
    [HasWeakSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
    [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (x : 𝒳) :
    (PresheafOfModules.sheafification
        (R := SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x))
        (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1
          (contains_base B E h S hS p x)).obj)).obj
      ((PresheafOfModules.tensorObj
        (O := localCommStructurePresheaf B S hS p E h x)
        (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
          (etaleTopology_le_topology B) F.val)
        (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
          (etaleTopology_le_topology B) G.val)).uliftSections.{u}) ≅
      (⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
            (etaleTopology_le_topology B) (etaleTensorSheaf B S hS p hp F G).val,
          isSheaf_restrictModule_etaleTensorSheaf B S hS p hp E h F G x⟩ :
        SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
          (contains_base B E h S hS p x))) :=
  (PresheafOfModules.sheafification
      (R := SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x))
      (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj)).mapIso
    (restrictModuleTensorObjIso B S hS p hp E h x F.val G.val) ≪≫
  sheafificationRestrictModuleTensorObjIso B S hS p hp E h F G x

/-- The restriction of the tensor product to the small étale site of the scheme below an object
`x` is quasi-coherent there, when the two factors are locally quasi-coherent.

It is the tensor product on that site of the two restrictions, by
`AlgebraicGeometry.Stack.restrictModuleEtaleTensorSheafIso`, and those are quasi-coherent by
local quasi-coherence of the factors; quasi-coherence of a tensor product on a ringed site is
`Stacks.Modules.isQuasicoherentOnSite_sheafificationTensorObjUlift`. -/
theorem isQuasicoherentOnSite_restrictModule_etaleTensorSheaf
    (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
    [HasWeakSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
    [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (hF : IsLocallyQuasicoherent B E h S hS p hp F.val)
    (hG : IsLocallyQuasicoherent B E h S hS p hp G.val) (x : 𝒳) :
    (⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
          (etaleTopology_le_topology B) (etaleTensorSheaf B S hS p hp F G).val,
        isSheaf_restrictModule_etaleTensorSheaf B S hS p hp E h F G x⟩ :
      SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x))).IsQuasicoherentOnSite := by
  let J := SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)
  have h𝒪 : Presheaf.IsSheaf J
      (structureRingPresheaf (localCommStructurePresheaf B S hS p E h x)) :=
    SmallEtale.structure_isSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)
  have hset : Presheaf.IsSheaf J
      (structureRingPresheaf (localCommStructurePresheaf B S hS p E h x) ⋙ forget RingCat.{u}) :=
    (CategoryTheory.hasSheafCompose_forget_ringCat_of_essentiallySmall.{u, u + 1, u} J).isSheaf _
      h𝒪
  have hQC := Stacks.Modules.isQuasicoherentOnSite_sheafificationTensorObjUlift
    (J := J) (𝒪 := localCommStructurePresheaf B S hS p E h x) h𝒪 hset
    ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B) F.val, (hF.2 x).choose⟩
    ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B) G.val, (hG.2 x).choose⟩
    (hF.2 x).choose_spec (hG.2 x).choose_spec
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (restrictModuleEtaleTensorSheafIso B S hS p hp E h F G x) hQC

/-! ### Sheafification on the associated étale site

Every slice `𝒳/x` is essentially small in the universe of the schemes, by Stacks 06W0
(`AlgebraicGeometry.FibredSite.essentiallySmall_over`), so abelian presheaves on the associated
étale site with sections in that universe have a sheafification and its weak equivalences are
the locally bijective maps; no smallness of `𝒳` itself is needed. -/

include hp in
/-- Abelian presheaves on the associated étale site of `𝒳`, with sections in the universe of the
schemes, have a sheafification. -/
theorem hasSheafify_etaleAssociatedTopology :
    HasSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u} :=
  have : ∀ x : 𝒳, EssentiallySmall.{u} (Over x) := FibredSite.essentiallySmall_over B S hS p hp
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall_over _

include hp in
/-- The weak equivalences of the sheafification of abelian presheaves on the associated étale
site of `𝒳`, with sections in the universe of the schemes, are the locally bijective maps. -/
theorem wEqualsLocallyBijective_etaleAssociatedTopology :
    (associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  have : ∀ x : 𝒳, EssentiallySmall.{u} (Over x) := FibredSite.essentiallySmall_over B S hS p hp
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall_over _

/-- The tensor product on the associated étale site of two locally quasi-coherent sheaves of
modules is locally quasi-coherent, for the spelling of that tensor product as the sheafification
of the objectwise one. -/
theorem isLocallyQuasicoherent_etaleTensorSheaf
    (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
    [HasWeakSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
    [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (hF : IsLocallyQuasicoherent B E h S hS p hp F.val)
    (hG : IsLocallyQuasicoherent B E h S hS p hp G.val) :
    IsLocallyQuasicoherent B E h S hS p hp (etaleTensorSheaf B S hS p hp F G).val :=
  ⟨(etaleTensorSheaf B S hS p hp F G).isSheaf, fun x =>
    ⟨isSheaf_restrictModule_etaleTensorSheaf B S hS p hp E h F G x,
      isQuasicoherentOnSite_restrictModule_etaleTensorSheaf B S hS p hp E h F G hF hG x⟩⟩

/-- **Stacks 06WM**, clause (4). The tensor product in `Mod(𝒳_ét, 𝒪_𝒳)` of two locally
quasi-coherent sheaves of modules on a category fibred in groupoids is locally quasi-coherent.

The tensor product is the sheafification, for the associated étale topology, of the objectwise
tensor product. Its restriction to the small étale site of the scheme below an object `x` is the
tensor product there of the restrictions of the two factors, by
`AlgebraicGeometry.Stack.restrictModuleEtaleTensorSheafIso`: restriction commutes with the
objectwise tensor product because that is sectionwise, and with sheafification because the
restriction functor of Stacks 06W1 is cocontinuous as well as continuous. Quasi-coherence of a
tensor product on a ringed site is
`Stacks.Modules.isQuasicoherentOnSite_sheafificationTensorObjUlift`. -/
@[stacks 06WM "(4): the tensor product in Mod(𝒳_ét, 𝒪_𝒳) of two locally quasi-coherent \
modules is locally quasi-coherent"]
theorem isLocallyQuasicoherent_tensorSheaf
    (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (hF : IsLocallyQuasicoherent B E h S hS p hp F.val)
    (hG : IsLocallyQuasicoherent B E h S hS p hp G.val) :
    letI := hasSheafify_etaleAssociatedTopology B S hS p hp
    letI := wEqualsLocallyBijective_etaleAssociatedTopology B S hS p hp
    IsLocallyQuasicoherent B E h S hS p hp
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
        (structureSheaf B S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B))).obj F).obj G).val :=
  let := hasSheafify_etaleAssociatedTopology B S hS p hp
  let := wEqualsLocallyBijective_etaleAssociatedTopology B S hS p hp
  isLocallyQuasicoherent_etaleTensorSheaf B S hS p hp E h F G hF hG

end AlgebraicGeometry.Stack

end
