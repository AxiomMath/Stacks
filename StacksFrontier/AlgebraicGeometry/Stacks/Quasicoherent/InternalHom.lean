module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Smallness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Modules
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCover

/-!
# Internal Hom of quasi-coherent modules on a category fibred in groupoids

Let `p : 𝒳 ⥤ (Sch/S)` be a category fibred in groupoids over the big fppf category of schemes
over `S`.  Its associated site carries the structure sheaf of Stacks 06TV, so it is a ringed
site, and the internal Hom of sheaves of modules on a ringed site is the one of Stacks 03EM.
Stacks 06WN asserts of that internal Hom that it is quasi-coherent when the source is finite
locally free and both arguments are quasi-coherent, and that its underlying presheaf of
modules does not depend on which of the associated topologies is used.

This file proves the first assertion on the fppf associated site and the second for all five
associated topologies, on which the internal Hom presheaves are equal on the nose. It also
shows that sheafification into abelian groups transports along an equivalence of categories to
the induced topology, and that finite local freeness in the sense of Stacks 03DL(2) implies it in
the sense of Stacks 01C6(2).

## Main definitions

* `AlgebraicGeometry.FibredSite.ringedSite`: the associated site of `p` for one of the five
  topologies, equipped with the structure sheaf, as a ringed site.

## Main results

* `CategoryTheory.Functor.hasWeakSheafify_inducedTopology` and
  `CategoryTheory.Functor.wEqualsLocallyBijective_inducedTopology`: sheafification into abelian
  groups, and locally bijective weak equivalences, transport along an equivalence of categories
  to the induced topology.
* `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite`: a module
  that is finite locally free in the sense of Stacks 03DL(2) is finite locally free in the sense
  of Stacks 01C6(2).
* `AlgebraicGeometry.FibredSite.internalHomSheaf_val_eq_fppf`: the internal Hom of two
  quasi-coherent modules has the same underlying presheaf of modules on each of the five
  associated sites.
* `AlgebraicGeometry.FibredSite.internalHomSheaf_isQuasicoherent`: the internal Hom of a finite
  locally free quasi-coherent module into a quasi-coherent module is quasi-coherent on the fppf
  associated site.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w v' w' u₁

namespace CategoryTheory.Functor

variable {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
  (b : C ⥤ D) [b.IsEquivalence] (K : GrothendieckTopology D)

/-- The quasi-inverse of an equivalence of categories is a dense subsite of the topology the
equivalence induces. -/
private theorem inv_isDenseSubsite_inducedTopology :
    b.inv.IsDenseSubsite K (b.inducedTopology K) :=
  inferInstanceAs (b.asEquivalence.symm.functor.IsDenseSubsite K
    (b.asEquivalence.symm.inverse.inducedTopology K))

/-- Pushing sheaves of abelian groups forward along the quasi-inverse of an equivalence of
categories is an equivalence onto the sheaves for the induced topology. -/
private theorem inv_sheafPushforwardContinuous_isEquivalence
    [b.inv.IsDenseSubsite K (b.inducedTopology K)] :
    (b.inv.sheafPushforwardContinuous AddCommGrpCat.{u} K
      (b.inducedTopology K)).IsEquivalence := by
  have : b.asEquivalence.inverse.IsDenseSubsite K (b.inducedTopology K) :=
    inferInstanceAs (b.inv.IsDenseSubsite K (b.inducedTopology K))
  show (b.asEquivalence.sheafCongr (b.inducedTopology K) K
    AddCommGrpCat.{u}).functor.IsEquivalence
  infer_instance

/-- Sheafification into abelian groups transports along an equivalence of categories to the
topology the equivalence induces. -/
public theorem hasWeakSheafify_inducedTopology [HasWeakSheafify K AddCommGrpCat.{u}] :
    HasWeakSheafify (b.inducedTopology K) AddCommGrpCat.{u} := by
  have := inv_isDenseSubsite_inducedTopology b K
  have := inv_sheafPushforwardContinuous_isEquivalence.{u} b K
  exact IsDenseSubsite.hasWeakSheafify_of_isEquivalence K _ b.inv _

/-- Having the locally bijective maps as weak equivalences transports along an equivalence of
categories to the topology the equivalence induces. -/
public theorem wEqualsLocallyBijective_inducedTopology
    [HasWeakSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (b.inducedTopology K).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  have := inv_isDenseSubsite_inducedTopology b K
  have := inv_sheafPushforwardContinuous_isEquivalence.{u} b K
  exact GrothendieckTopology.WEqualsLocallyBijective.transport _ K b.inv
    (IsDenseSubsite.coverPreserving K _ b.inv)

end CategoryTheory.Functor

namespace AlgebraicGeometry

namespace SheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}

/-- A finite free sheaf of modules has a generating family of sections which is finite and
whose associated projection from the free module on it is an isomorphism. -/
private theorem finiteFree_generatingSections
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J RingCat.{u}) (F : _root_.SheafOfModules.{u} R)
    (hF : _root_.SheafOfModules.IsFiniteFree R F) :
    ∃ q : F.GeneratingSections, IsIso q.π ∧ q.IsFiniteType := by
  classical
  obtain ⟨n, ι, ⟨hι⟩⟩ := (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit R F).mp hF
  let c : Cofan (fun _ : ULift.{u} (Fin n) => _root_.SheafOfModules.unit R) :=
    Cofan.mk F (fun i => ι i.down)
  let hc : IsColimit c := hι.whiskerEquivalence (Discrete.equivalence Equiv.ulift)
  let e : _root_.SheafOfModules.free (R := R) (ULift.{u} (Fin n)) ≅ F :=
    (_root_.SheafOfModules.isColimitFreeCofan _).coconePointUniqueUpToIso hc
  let q : F.GeneratingSections :=
    { I := ULift.{u} (Fin n)
      s := F.freeHomEquiv e.hom
      epi := by rw [Equiv.symm_apply_apply]; infer_instance }
  refine ⟨q, ?_, ⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩⟩
  show IsIso (F.freeHomEquiv.symm (F.freeHomEquiv e.hom))
  rw [Equiv.symm_apply_apply]; infer_instance

/-- Finite local freeness in the covering-family sense of Stacks 03DL(2) gives finite local
freeness in the local-generators sense of Stacks 01C6(2). -/
public theorem isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite {R : Sheaf J RingCat.{u}}
    [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : _root_.SheafOfModules.{u} R) (hF : F.IsFiniteLocallyFreeOnSite) :
    IsFiniteLocallyFree F := by
  classical
  let P := fun U : C => _root_.SheafOfModules.IsFiniteFree (R.over U) (F.over U)
  have generators (i : {U : C // P U}) :
      ∃ q : (F.over i.val).GeneratingSections, IsIso q.π ∧ q.IsFiniteType :=
    finiteFree_generatingSections _ _ i.property
  let q : F.LocalGeneratorsData :=
    { I := {U : C // P U}
      X := Subtype.val
      coversTop U := by
        obtain ⟨I, V, f, hf, hV⟩ := hF U
        refine J.superset_covering ((Sieve.generate_le_iff _ _).mpr ?_) hf
        rintro W g ⟨i⟩
        exact ⟨⟨V i, hV i⟩, ⟨𝟙 _⟩⟩
      generators i := (generators i).choose }
  exact ⟨q, ⟨fun i => (generators i).choose_spec.1⟩,
    ⟨fun i => (generators i).choose_spec.2⟩⟩

end SheafOfModules

namespace FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- The associated site of a category fibred in groupoids over the schemes over `S`, for one of
the five topologies, equipped with the structure sheaf of Stacks 06TV, as a ringed site. -/
public noncomputable def ringedSite (hp : p.IsFiberedInGroupoids) (τ : SiteKind) :
    RingedSite.{v, w, u} where
  C := 𝒳
  J := BigFppfOver.associatedTopology B S hS p τ
  O := structureSheaf B S hS p hp τ

/-- The coefficient sheaf of rings of the ringed site of a category fibred in groupoids is the
one over which its quasi-coherent modules are taken. -/
@[simp] public theorem ringSheaf_ringedSite (hp : p.IsFiberedInGroupoids) (τ : SiteKind) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS p hp τ).O) =
      ringStructureSheafCore B S hS p hp τ :=
  rfl

/-- The internal Hom of two quasi-coherent modules on a category fibred in groupoids has the
same underlying presheaf of modules on each of the five associated sites as on the fppf one; in
particular on the Zariski and étale ones. -/
@[stacks 06WN "internal_homs"]
public theorem internalHomSheaf_val_eq_fppf (hp : p.IsFiberedInGroupoids) (τ : SiteKind)
    (F G : quasicoherentModules.{u, v, w, u} B S hS p hp) :
    ((ringedSite B S hS p hp τ).internalHomSheaf
        ((toSiteModules B S hS p hp τ).obj F)
        ((toSiteModules B S hS p hp τ).obj G)).val =
      ((ringedSite B S hS p hp .fppf).internalHomSheaf F.obj G.obj).val :=
  rfl

/-- The internal Hom of a finite locally free quasi-coherent module into a quasi-coherent module
on a category fibred in groupoids is quasi-coherent on the fppf associated site. -/
@[stacks 06WN "internal_homs"]
public theorem internalHomSheaf_isQuasicoherent (hp : p.IsFiberedInGroupoids)
    (F G : quasicoherentModules.{u, v, w, u} B S hS p hp)
    (hF : SheafOfModules.IsFiniteLocallyFreeOnSite F.obj) :
    ((ringedSite B S hS p hp .fppf).internalHomSheaf F.obj G.obj).IsQuasicoherentOnSite := by
  have h1 (x : 𝒳) := hasWeakSheafify_over B S hS p hp .fppf x
  have h2 (x : 𝒳) := wEqualsLocallyBijective_over B S hS p hp .fppf x
  exact @RingedSite.internalHomSheaf_isQuasicoherent (ringedSite B S hS p hp .fppf)
    F.obj G.obj h1 h2 F.property G.property
    (@SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite 𝒳 _ _ _ h1 h2 F.obj hF)

end FibredSite

end AlgebraicGeometry

end
