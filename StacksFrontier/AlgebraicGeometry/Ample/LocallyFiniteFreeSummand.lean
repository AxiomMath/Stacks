module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import Mathlib.Topology.Sheaves.Module
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import StacksFrontier.Topology.Sheaves.RingedSpace.Basic
public import StacksFrontier.Topology.Sheaves.Modules.Invertible

/-!
# Invertible modules are locally finite-free summands

Let `(X, 𝒪_X)` be a ringed space and `L` an invertible `𝒪_X`-module, that is, one for which
tensoring by `L` is an autoequivalence of `𝒪_X`-modules (Tag 01CS). This file proves the
finite-presentation half of Tag 0B8K: near every point of `X` the restriction of `L` to a
suitable open neighbourhood is a direct summand of a finite free module.

The argument is the one in the Stacks Project. A tensor inverse `N` with `L ⊗ N ≅ 𝒪_X` exists
because the tensor functor is essentially surjective. Since the tensor product is a
sheafification, the section of `L ⊗ N` corresponding to `1` is, near any point `x`, represented
by a finite sum `∑ sᵢ ⊗ tᵢ` of pure tensors over some open `U ∋ x`. The two maps
`s ↦ (ψ(s ⊗ t₁), …, ψ(s ⊗ tₙ))` and `(a₁, …, aₙ) ↦ ∑ aᵢ sᵢ` between `L|_U` and `𝒪_U^{⊕n}`
compose to the automorphism `s ↦ ∑ ψ(s ⊗ tᵢ) sᵢ` of `L|_U`, so `L|_U` is a retract of a finite
free module.

## Main definitions

* `Stacks.SheafOfModules.LocallyFiniteFree.ringSheaf` regards the commutative structure sheaf
  as a sheaf of rings.
* `Stacks.SheafOfModules.LocallyFiniteFree.toRingSheafHom` is the map of ring sheaves
  associated to a morphism of ringed spaces.
* `Stacks.SheafOfModules.LocallyFiniteFree.modulePullback` is the induced pullback functor on
  module sheaves.

## Main results

* `Stacks.SheafOfModules.LocallyFiniteFree.isRightAdjoint_pushforward_toRingSheafHom_ofRestrict`:
  pushforward along the inclusion of an open subspace is a right adjoint, its left adjoint
  being restriction to that open subspace. Pullback along an open immersion is therefore
  available with no further hypotheses.
* `Stacks.SheafOfModules.LocallyFiniteFree.isLocallyFiniteFreeSummand_of_isInvertible` states
  that every invertible module has this property.

## Implementation notes

Locality is expressed pointwise by open neighbourhoods. Restriction to an open `U` is pullback
along the open-subspace inclusion, and the finite free module of rank `n` is
`SheafOfModules.free (ULift (Fin n))`; the universe lift does not change its rank. Being a
direct summand is represented by a categorical retract. The smallness of the underlying space
and that of its rings are independent.

The composite automorphism of `L|_U` is built functorially out of the tensor functor of Tag
01CS: `tensorRightUnitor`, `tensorAssoc` and `tensorSelfBraid` transport the presheaf monoidal
and symmetric structures through `Stacks.SheafOfModules.TensorSheafification.sheafify`, and the
  `_pure` lemmas record the
effect of each on a pure tensor of sections. Mathlib's own monoidal lemmas for
`PresheafOfModules` are proved by `rfl`, which is what lets those lemmas be discharged by
`sheafify_map_toSheafify_apply` alone.

Two places need a helper stated at an abstract category or at the global module objects, rather
than at the module category over the slice site: `nonempty_retract_of_iso` and `tmulRight`. The
reason is that `SheafOfModules.over` and `Sheaf.over` present the restricted sheaf of rings
through several semireducible definitions, so instance synthesis at the slice types cannot see
that they agree with the restriction of `𝒪_X`; applying a helper whose binders are the literal
general types reduces the obligation to a term-level definitional equality.

## References

* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
  TopologicalSpace AlgebraicGeometry

namespace Stacks.SheafOfModules.LocallyFiniteFree

universe u w

section Generic

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {A B : _root_.SheafOfModules.{u} R}

/-- The inverse of an isomorphism of sheaves of modules undoes it on sections. Stated here so
that the only transparency-sensitive step is the application of this lemma. -/
private lemma inv_app_hom_apply (e : A ≅ B) (V : Cᵒᵖ) (a : A.val.obj V) :
    (e.inv.val.app V).hom ((e.hom.val.app V).hom a) = a :=
  congrArg (fun g : A ⟶ A => (g.val.app V).hom a) e.hom_inv_id

/-- Evaluating a finite sum of maps of sheaves of modules on a section. -/
private lemma sum_app_apply {ι : Type*} (s : Finset ι) (f : ι → (A ⟶ B)) (V : Cᵒᵖ)
    (x : A.val.obj V) :
    (((∑ i ∈ s, f i).val.app V).hom) x = ∑ i ∈ s, ((f i).val.app V).hom x := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    rfl
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
    simp

end Generic

variable [Limits.PreservesLimitsOfSize.{w, w} (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The underlying sheaf of rings of a ringed space, with independent universes for
the space and for the rings.

This is **the same construction** as `structureSheafRing`
(`StacksFrontier/Topology/Sheaves/Functors/Module/RingedSpace.lean`), and at `w = u` the same
term: both are `⟨X.presheaf ⋙ forget₂ CommRingCat RingCat, _⟩`, the two sheaf-condition
proofs being irrelevant. It is kept as a separate declaration for exactly one reason, which is
not a difference of value but a difference of domain: this development, and the statement of
Stacks 0B8K it ends at, are stated for `RingedSpace.{u, w}` with the universe of the space
independent of the universe of the rings, whereas `structureSheafRing` is pinned to
`RingedSpace.{u, u}`. That pinning is forced, not stylistic — the file that hosts
`structureSheafRing` founds the pushforward/pullback adjunction on
`PresheafOfModules.instIsRightAdjointPushforward`, which Mathlib states only for two
`SmallCategory` sites in a single universe, so the whole `RingedSpaceModuleAdjunction`
development identifies the carrier, ring and module universes. Collapsing this file to
`{u, u}` in order to delete this abbrev would narrow the `@[stacks 0B8K]` statement, so
it is not done.

Because this is an `abbrev` and `structureSheafRing` is `@[reducible]`, and both have the
reducible normal form `⟨X.presheaf ⋙ forget₂ _ _, _⟩`, instance synthesis and unification do
cross between them freely whenever `w` and `u` agree; no bridge lemma is needed or wanted. -/
abbrev ringSheaf (X : RingedSpace.{u, w}) :
    Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u} :=
  ⟨X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u},
    Presheaf.isSheaf_comp_of_isSheaf _ X.presheaf
      (forget₂ CommRingCat.{u} RingCat.{u}) X.IsSheaf⟩

/-- Any invertible module sheaf admits a tensor inverse: some `N` with `L ⊗ N ≅ 𝒪`. -/
theorem exists_tensor_inverse
    (X : RingedSpace.{u, w}) (L : _root_.SheafOfModules.{u} (ringSheaf X))
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ X.presheaf
        (forget₂ CommRingCat.{u} RingCat.{u}) X.IsSheaf) L) :
    ∃ N : _root_.SheafOfModules.{u} (ringSheaf X),
      Nonempty (((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
          ⟨X.presheaf, X.IsSheaf⟩).obj L).obj N ≅
        _root_.SheafOfModules.unit (ringSheaf X)) := by
  obtain ⟨F, hF, ⟨a⟩⟩ := hL.exists_tensorFunctor
  have : F.IsEquivalence := hF
  refine ⟨F.objPreimage (_root_.SheafOfModules.unit (ringSheaf X)), ⟨?_⟩⟩
  exact ((a.uniqueIso (AlgebraicGeometry.SheafOfModules.tensorLeftFunctorUniversal
      X.presheaf _ L)).app _).symm ≪≫ F.objObjPreimageIso _

omit [Limits.PreservesLimitsOfSize.{w, w} (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- A section of a presheaf of abelian groups that is locally in the image of `f` is, near any
given point, the restriction of an actual section of the source. -/
private lemma exists_local_preimage_at_point
    {X : TopCat.{w}}
    {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    (f : P ⟶ Q)
    (s : ToType (Q.obj (Opposite.op ⊤)))
    (hcov : Presheaf.imageSieve f s ∈ Opens.grothendieckTopology X ⊤)
    (x : X) :
    ∃ (U : Opens X) (_hx : x ∈ U) (i : U ⟶ ⊤)
      (t : ToType (P.obj (Opposite.op U))),
      f.app (Opposite.op U) t = Q.map i.op s := by
  have hmem := Opens.mem_grothendieckTopology (T := X) (U := ⊤)
    (S := Presheaf.imageSieve f s)
  obtain ⟨U, i, hi, hx⟩ := hmem.mp hcov x (by simp)
  obtain ⟨t, ht⟩ := hi
  exact ⟨U, hx, i, t, ht⟩

/-- Near any point, the section of `L ⊗ N` corresponding to `1` under a tensor-inverse
isomorphism is represented by a finite sum of pure tensors. -/
lemma exists_local_finite_tensor_representation
    (X : RingedSpace.{u, w}) (L N : _root_.SheafOfModules.{u} (ringSheaf X))
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (e : ((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).obj L).obj N ≅
      _root_.SheafOfModules.unit (ringSheaf X)) (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (k : ℕ)
      (m : Fin k → ToType (L.val.obj (Opposite.op U)))
      (n : Fin k → ToType (N.val.obj (Opposite.op U))),
      ((AlgebraicGeometry.SheafOfModules.tensorLeftFunctorUniversal X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ X.presheaf
          (forget₂ CommRingCat.{u} RingCat.{u}) X.IsSheaf) L).ι.app N).app
          (Opposite.op U) (∑ i, m i ⊗ₜ[X.presheaf.obj (Opposite.op U)] n i) =
        (e.inv.val.app (Opposite.op U)).hom
          (1 : (ringSheaf X).obj.obj (Opposite.op U)) := by
  let hO := Presheaf.isSheaf_comp_of_isSheaf _ X.presheaf
    (forget₂ CommRingCat.{u} RingCat.{u}) X.IsSheaf
  let R := ringSheaf X
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj L
  let a := AlgebraicGeometry.SheafOfModules.tensorLeftFunctorUniversal X.presheaf hO L
  let _ : MonoidalCategory (PresheafOfModules.{u} R.obj) := by
    change MonoidalCategory
      (PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    infer_instance
  let P := (tensorLeft L.val).obj N.val
  let σ := (PresheafOfModules.toPresheaf R.obj).map (a.ι.app N)
  have hσ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) σ := by
    change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X.carrier) P.presheaf)
    infer_instance
  let s := (e.inv.val.app (Opposite.op ⊤)).hom
    (1 : R.obj.obj (Opposite.op ⊤))
  have hcov : Presheaf.imageSieve σ s ∈ Opens.grothendieckTopology X.carrier ⊤ :=
    hσ.imageSieve_mem s
  obtain ⟨U, hx, i, t, ht⟩ := exists_local_preimage_at_point σ s hcov x
  obtain ⟨k, m, n, htensor⟩ :=
    TensorProduct.exists_sum_tmul_eq (R := X.presheaf.obj (Opposite.op U)) t
  refine ⟨U, hx, k, m, n, ?_⟩
  have h := ht
  change (σ.app (Opposite.op U)).hom t =
    ((T.obj N).val.map i.op).hom s at h
  rw [htensor] at h
  have hn := PresheafOfModules.naturality_apply e.inv.val i.op
    (1 : R.obj.obj (Opposite.op ⊤))
  have hunit : ((_root_.SheafOfModules.unit R).val.map i.op).hom
      (1 : R.obj.obj (Opposite.op ⊤)) = (1 : R.obj.obj (Opposite.op U)) := by
    change ((PresheafOfModules.unit R.obj).map i.op)
      (1 : R.obj.obj (Opposite.op ⊤)) = (1 : R.obj.obj (Opposite.op U))
    exact PresheafOfModules.unit_map_one R.obj i.op
  have hrestrict : ((T.obj N).val.map i.op).hom s =
      (e.inv.val.app (Opposite.op U)).hom (1 : R.obj.obj (Opposite.op U)) := by
    calc
      _ = (e.inv.val.app (Opposite.op U)).hom
          (((_root_.SheafOfModules.unit R).val.map i.op).hom
            (1 : R.obj.obj (Opposite.op ⊤))) := hn.symm
      _ = _ := congrArg (e.inv.val.app (Opposite.op U)).hom hunit
  change (σ.app (Opposite.op U)).hom
      (∑ j, m j ⊗ₜ[X.presheaf.obj (Opposite.op U)] n j) = _
  exact h.trans hrestrict

/-- The morphism of sheaves of rings induced by a morphism of ringed spaces. -/
noncomputable def toRingSheafHom {X Y : RingedSpace.{u, w}} (f : X ⟶ Y) :
    ringSheaf Y ⟶
      ((Opens.map f.hom.base).sheafPushforwardContinuous _ _ _).obj (ringSheaf X) where
  hom := Functor.whiskerRight f.hom.c _

/-- Pullback of sheaves of modules along a morphism of ringed spaces. -/
noncomputable def modulePullback {X Y : RingedSpace.{u, w}} (f : X ⟶ Y)
    [(_root_.SheafOfModules.pushforward.{u} (toRingSheafHom f)).IsRightAdjoint] :
    _root_.SheafOfModules.{u} (ringSheaf Y) ⥤ _root_.SheafOfModules.{u} (ringSheaf X) :=
  _root_.SheafOfModules.pullback.{u} (toRingSheafHom f)

/-- Restriction of sheaves of modules to an open subspace, as pushforward along the
continuous functor induced by the open embedding. -/
private noncomputable def siteRestrict (X : RingedSpace.{u, w})
    (U : Opens X) :
    _root_.SheafOfModules.{u} (ringSheaf X) ⥤
      _root_.SheafOfModules.{u} (ringSheaf (X.restrict U.isOpenEmbedding)) := by
  let j := X.ofRestrict U.isOpenEmbedding
  let h : Topology.IsOpenEmbedding j.hom.base :=
    (SheafedSpace.IsOpenImmersion.ofRestrict X U.isOpenEmbedding).base_open
  let F := h.functor
  letI : F.IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      (Opens.grothendieckTopology X.carrier) := h.functor_isContinuous
  exact _root_.SheafOfModules.pushforward (F := F) (𝟙 _)

/-- Restriction to an open subspace is left adjoint to pushforward along the open
immersion. -/
private noncomputable def siteRestrictAdjunction (X : RingedSpace.{u, w})
    (U : Opens X) :
    siteRestrict X U ⊣
      _root_.SheafOfModules.pushforward.{u}
        (toRingSheafHom (X.ofRestrict U.isOpenEmbedding)) := by
  let j := X.ofRestrict U.isOpenEmbedding
  let h : Topology.IsOpenEmbedding j.hom.base :=
    (SheafedSpace.IsOpenImmersion.ofRestrict X U.isOpenEmbedding).base_open
  let F := h.functor
  let G := Opens.map j.hom.base
  let adj : F ⊣ G := h.isOpenMap.adjunction
  letI : F.IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      (Opens.grothendieckTopology X.carrier) := h.functor_isContinuous
  letI : G.IsContinuous
      (Opens.grothendieckTopology X.carrier)
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier) := by
    infer_instance
  let R := ringSheaf X
  let S := ringSheaf (X.restrict U.isOpenEmbedding)
  let φ : S ⟶ (F.sheafPushforwardContinuous RingCat _ _).obj R := 𝟙 _
  let ψ : R ⟶ (G.sheafPushforwardContinuous RingCat _ _).obj S := toRingSheafHom j
  have h1 : Functor.whiskerRight (NatTrans.op adj.counit) R.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    ext V x
    rfl
  have h2 : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit) S.obj = 𝟙 S.obj := by
    ext V x
    change (R.obj.map (adj.counit.app (F.obj V.unop)).op ≫
      R.obj.map (F.map (adj.unit.app V.unop)).op) x = x
    rw [← Functor.map_comp, ← op_comp]
    have htri := adj.left_triangle_components V.unop
    rw [htri]
    exact CategoryTheory.Functor.map_id_apply R.obj (Opposite.op (F.obj V.unop)) x
  change _root_.SheafOfModules.pushforward φ ⊣ _root_.SheafOfModules.pushforward ψ
  exact _root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ h1 h2

/-- Pushforward of sheaves of modules along the inclusion of an open subspace is a right
adjoint: restriction to the open subspace is its left adjoint, by
`Stacks.SheafOfModules.LocallyFiniteFree.siteRestrictAdjunction`. Consequently the pullback
functor `Stacks.SheafOfModules.LocallyFiniteFree.modulePullback` along an open immersion is
unconditionally available. -/
instance isRightAdjoint_pushforward_toRingSheafHom_ofRestrict
    (X : RingedSpace.{u, w}) (U : Opens X) :
    (_root_.SheafOfModules.pushforward.{u}
      (toRingSheafHom (X.ofRestrict U.isOpenEmbedding))).IsRightAdjoint :=
  (siteRestrictAdjunction X U).isRightAdjoint

/-- Mathlib's equivalence between modules over the restricted site and modules over the
slice site identifies the slice restriction functor with `siteRestrict`. -/
private noncomputable def overFunctorIsoSiteRestrict
    (X : RingedSpace.{u, w}) (U : Opens X) :
    _root_.SheafOfModules.overFunctor (ringSheaf X) U ⋙
      (U.sheafOfModulesEquivOver (ringSheaf X)).functor ≅ siteRestrict X U := by
  haveI : ((Opens.overEquivalence U).symm.functor).IsContinuous
      (Opens.grothendieckTopology U)
      ((Opens.grothendieckTopology X.carrier).over U) := inferInstance
  haveI : (Over.forget U).IsContinuous
      ((Opens.grothendieckTopology X.carrier).over U)
      (Opens.grothendieckTopology X.carrier) := inferInstance
  have hcont : ((Opens.overEquivalence U).symm.functor ⋙ Over.forget U).IsContinuous
      (Opens.grothendieckTopology U)
      (Opens.grothendieckTopology X.carrier) :=
    Functor.isContinuous_comp _ _ _ ((Opens.grothendieckTopology X.carrier).over U) _
  refine _root_.SheafOfModules.pushforwardComp _ _ ≪≫
    _root_.SheafOfModules.pushforwardCongr ?_
  ext W x
  rfl

/-- The restriction of a module sheaf to an open, computed through the slice site, agrees
with its pullback along the open immersion. -/
private noncomputable def overFunctorIsoPullback
    (X : RingedSpace.{u, w}) (U : Opens X)
    (M : _root_.SheafOfModules.{u} (ringSheaf X)) :
    ((U.sheafOfModulesEquivOver (ringSheaf X)).functor.obj (M.over U)) ≅
      (modulePullback (X.ofRestrict U.isOpenEmbedding)).obj M :=
  (overFunctorIsoSiteRestrict X U).app M ≪≫
    ((siteRestrictAdjunction X U).leftAdjointUniq
      (_root_.SheafOfModules.pullbackPushforwardAdjunction
        (toRingSheafHom (X.ofRestrict U.isOpenEmbedding)))).app M

/-- A section of `M` over `U` as a global section of the restriction of `M` to the slice
site over `U`. -/
private noncomputable def sectionOver
    (X : RingedSpace.{u, w}) (M : _root_.SheafOfModules.{u} (ringSheaf X))
    (U : Opens X) (m : M.val.presheaf.obj (Opposite.op U)) :
    (M.over U).sections :=
  PresheafOfModules.sectionsMk
    (fun V => M.val.presheaf.map V.unop.hom.op m)
    (by
      intro V W f
      change M.val.presheaf.map ((Over.forget U).map f.unop).op
        (M.val.presheaf.map V.unop.hom.op m) =
          M.val.presheaf.map W.unop.hom.op m
      calc
        _ = M.val.presheaf.map
            (V.unop.hom.op ≫ ((Over.forget U).map f.unop).op) m := by
              rw [Functor.map_comp]
              rfl
        _ = M.val.presheaf.map W.unop.hom.op m := by
              congr 1)

omit [Limits.PreservesLimitsOfSize.{w, w} (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Sheafification of abelian-group-valued presheaves is available on the slice site over an
open `U`, because it is available on the open subspace `U`. -/
private lemma hasWeakSheafifyOver
    (X : RingedSpace.{u, w}) (U : Opens X)
    [HasWeakSheafify
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier) AddCommGrpCat.{u}] :
    HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) AddCommGrpCat.{u} := by
  let J := (Opens.grothendieckTopology X.carrier).over U
  let K := Opens.grothendieckTopology U
  let _ : HasWeakSheafify K AddCommGrpCat.{u} := by
    change HasWeakSheafify
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier) AddCommGrpCat.{u}
    infer_instance
  let E := U.overEquivalence
  let S := U.sheafEquivOver (A := AddCommGrpCat.{u})
  let F := E.op.congrLeft.functor ⋙ presheafToSheaf K AddCommGrpCat.{u} ⋙ S.inverse
  let h : S.functor ⋙ sheafToPresheaf K AddCommGrpCat.{u} ⋙
      E.op.congrLeft.inverse ≅ sheafToPresheaf J AddCommGrpCat.{u} :=
    NatIso.ofComponents (fun G => Functor.isoWhiskerRight E.op.unitIso.symm G.obj)
      (by
        intro G H f
        ext V x
        exact CategoryTheory.congr_fun
          (f.hom.naturality ((E.op.unitIso.symm).hom.app V)).symm x)
  let adj : F ⊣ sheafToPresheaf J AddCommGrpCat.{u} :=
    ((E.op.congrLeft.toAdjunction.comp
      (sheafificationAdjunction K AddCommGrpCat.{u})).comp
      S.symm.toAdjunction).ofNatIsoRight h
  exact ⟨F, ⟨adj⟩⟩

omit [Limits.PreservesLimitsOfSize.{w, w} (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Weak equivalences agree with the locally bijective maps on the slice site over an open `U`,
because they do so on the open subspace `U`. -/
private lemma wEqualsLocallyBijectiveOver
    (X : RingedSpace.{u, w}) (U : Opens X)
    [(Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier).WEqualsLocallyBijective
      AddCommGrpCat.{u}] :
    ((Opens.grothendieckTopology X.carrier).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u} := by
  let J := (Opens.grothendieckTopology X.carrier).over U
  let K := Opens.grothendieckTopology U
  let E := U.overEquivalence
  have : K.WEqualsLocallyBijective AddCommGrpCat.{u} := by
    change (Opens.grothendieckTopology
      (X.restrict U.isOpenEmbedding).carrier).WEqualsLocallyBijective AddCommGrpCat.{u}
    infer_instance
  have : (E.inverse.sheafPushforwardContinuous AddCommGrpCat.{u} K J).EssSurj := by
    change (E.sheafCongr J K AddCommGrpCat.{u}).functor.EssSurj
    infer_instance
  exact GrothendieckTopology.WEqualsLocallyBijective.transport J K E.inverse
    (Functor.IsDenseSubsite.coverPreserving K J E.inverse)

/-- The map from the finite free module of rank `n` to the restriction of `L` determined by
`n` sections of `L` over `U`. -/
private noncomputable def freeToOver
    (X : RingedSpace.{u, w}) (L : _root_.SheafOfModules.{u} (ringSheaf X))
    (U : Opens X) (n : ℕ)
    [HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) AddCommGrpCat.{u}]
    [((Opens.grothendieckTopology X.carrier).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    (s : Fin n → L.val.obj (Opposite.op U)) :
    _root_.SheafOfModules.free (R := (ringSheaf X).over U) (ULift.{u} (Fin n)) ⟶
      L.over U :=
  (L.over U).freeHomEquiv.symm (fun i => sectionOver X L U (s i.down))

/-- The free module on `I` over the slice site corresponds to the free module on `I` over the
open subspace. -/
private noncomputable def freeOverToRestrictedIso
    (X : RingedSpace.{u, w}) (U : Opens X) (I : Type u)
    [HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) AddCommGrpCat.{u}]
    [((Opens.grothendieckTopology X.carrier).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    [HasWeakSheafify
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier).WEqualsLocallyBijective
      AddCommGrpCat.{u}] :
    (U.sheafOfModulesEquivOver (ringSheaf X)).functor.obj
        (_root_.SheafOfModules.free (R := (ringSheaf X).over U) I) ≅
      _root_.SheafOfModules.free (R := ringSheaf (X.restrict U.isOpenEmbedding)) I := by
  let E := U.sheafOfModulesEquivOver (ringSheaf X)
  haveI : PreservesColimitsOfShape (Discrete I) E.functor := inferInstance
  exact ((_root_.SheafOfModules.isColimitFreeCofan
    (R := ringSheaf (X.restrict U.isOpenEmbedding)) I).coconePointsIsoOfNatIso
      (isColimitOfPreserves E.functor
        (_root_.SheafOfModules.isColimitFreeCofan (R := (ringSheaf X).over U) I))
      (Discrete.natIso fun _ => Iso.refl _)).symm

omit [Limits.PreservesLimitsOfSize.{w, w} (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- A one-sided inverse pair transports along isomorphisms of its two ends, so the target is a
retract of the source. Stated for an abstract category so that all instance synthesis happens
here rather than at the two different-looking but definitionally equal module categories over
an open subspace. -/
private lemma nonempty_retract_of_iso {C : Type*} [Category C] {A B A' B' : C}
    (eA : A ≅ A') (eB : B ≅ B') (i : A ⟶ B) (r : B ⟶ A) (h : i ≫ r = 𝟙 A) :
    Nonempty (Retract A' B') :=
  ⟨{ i := eA.inv ≫ i ≫ eB.hom
     r := eB.inv ≫ r ≫ eA.hom
     retract := by
       rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc i, h,
         Category.id_comp, eA.inv_hom_id] }⟩

/-- A split epimorphism from a free module onto the restriction of `L` exhibits the pullback of
`L` to the open subspace as a retract of a free module. -/
private lemma retract_of_splitEpi_over
    (X : RingedSpace.{u, w}) (L : _root_.SheafOfModules.{u} (ringSheaf X))
    (U : Opens X) (I : Type u)
    [HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) AddCommGrpCat.{u}]
    [((Opens.grothendieckTopology X.carrier).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    [HasWeakSheafify
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    (f : _root_.SheafOfModules.free (R := (ringSheaf X).over U) I ⟶ L.over U)
    [IsSplitEpi f] :
    Nonempty (Retract ((modulePullback (X.ofRestrict U.isOpenEmbedding)).obj L)
      (_root_.SheafOfModules.free (R := ringSheaf (X.restrict U.isOpenEmbedding)) I)) := by
  let E := U.sheafOfModulesEquivOver (ringSheaf X)
  let eL := overFunctorIsoPullback X U L
  let eF := freeOverToRestrictedIso X U I
  let sf := (inferInstance : IsSplitEpi f).exists_splitEpi.some
  have hmap : E.functor.map sf.section_ ≫ E.functor.map f = 𝟙 _ := by
    simpa only [← Functor.map_comp, sf.id] using E.functor.map_id (L.over U)
  exact nonempty_retract_of_iso eL eF _ _ hmap

/-- Tensoring on the right by `N` as an endofunctor of sheaves of modules. -/
noncomputable def tensorRightFunctor
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (N : _root_.SheafOfModules.{u} (ringSheaf X)) :
    _root_.SheafOfModules.{u} (ringSheaf X) ⥤ _root_.SheafOfModules.{u} (ringSheaf X) :=
  _root_.SheafOfModules.forget (ringSheaf X) ⋙ tensorRight N.val ⋙
    Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf (ringSheaf X).property

/-- Naturality of the sheafification unit, read on sections. -/
private lemma sheafify_map_toSheafify_apply
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {P Q : PresheafOfModules.{u} (ringSheaf X).obj} (f : P ⟶ Q)
    (W : Opens X) (x : P.obj (Opposite.op W)) :
    (((Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf (ringSheaf X).property).map
      f).val.app
      (Opposite.op W)).hom
        (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
          P).app
          (Opposite.op W)).hom x) =
      ((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
        Q).app
        (Opposite.op W)).hom ((f.app (Opposite.op W)).hom x) := by
  have h := (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction X.presheaf
    (ringSheaf X).property).unit.naturality f
  exact (congrArg (fun q => (q.app (Opposite.op W)).hom x) h).symm

/-- The counit of the sheafification adjunction undoes the unit on sections of a sheaf. -/
private lemma sheafify_counit_toSheafify_apply
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (M : _root_.SheafOfModules.{u} (ringSheaf X)) (W : Opens X)
    (m : M.val.obj (Opposite.op W)) :
    (((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction X.presheaf
      (ringSheaf X).property).counit.app M).val.app (Opposite.op W)).hom
        (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
          M.val).app
          (Opposite.op W)).hom m) = m := by
  have h := (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction X.presheaf
    (ringSheaf X).property).right_triangle_components M
  exact congrArg (fun q => (q.app (Opposite.op W)).hom m) h

/-- Tensoring on the right by `N` acts on a pure tensor of sections in the obvious way. -/
lemma tensorRightFunctor_map_pure
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (A B N : _root_.SheafOfModules.{u} (ringSheaf X)) (f : A ⟶ B)
    (W : Opens X) (a : A.val.obj (Opposite.op W))
    (n : N.val.obj (Opposite.op W)) :
    (((tensorRightFunctor X N).map f).val.app (Opposite.op W)).hom
      (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
        (A.val ⊗ N.val)).app (Opposite.op W)).hom
          (a ⊗ₜ[X.presheaf.obj (Opposite.op W)] n)) =
      (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
        (B.val ⊗ N.val)).app (Opposite.op W)).hom
          (((f.val.app (Opposite.op W)).hom a) ⊗ₜ[X.presheaf.obj (Opposite.op W)] n)) :=
  sheafify_map_toSheafify_apply X (f.val ▷ N.val) W
    (a ⊗ₜ[X.presheaf.obj (Opposite.op W)] n)

/-- Tensoring on the left by `L` acts on a pure tensor of sections in the obvious way. -/
private lemma tensorLeftFunctor_map_pure
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L A B : _root_.SheafOfModules.{u} (ringSheaf X)) (f : A ⟶ B)
    (W : Opens X) (l : L.val.obj (Opposite.op W))
    (a : A.val.obj (Opposite.op W)) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).obj L).map f).val.app (Opposite.op W)).hom
      (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
        (L.val ⊗ A.val)).app (Opposite.op W)).hom
          (l ⊗ₜ[X.presheaf.obj (Opposite.op W)] a)) =
      (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
        (L.val ⊗ B.val)).app (Opposite.op W)).hom
          (l ⊗ₜ[X.presheaf.obj (Opposite.op W)]
            ((f.val.app (Opposite.op W)).hom a))) :=
  sheafify_map_toSheafify_apply X (L.val ◁ f.val) W
    (l ⊗ₜ[X.presheaf.obj (Opposite.op W)] a)

/-- Tensoring `L` with the structure sheaf gives back `L`. -/
noncomputable def tensorRightUnitor
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L : _root_.SheafOfModules.{u} (ringSheaf X)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj L).obj
        (_root_.SheafOfModules.unit (ringSheaf X)) ≅ L := by
  have : IsIso (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction X.presheaf (ringSheaf
    X).property).counit := by
    change IsIso
      (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf X).obj)).counit
    infer_instance
  exact (Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf (ringSheaf
    X).property).mapIso
      (MonoidalCategoryStruct.rightUnitor
        (C := PresheafOfModules.{u} (ringSheaf X).obj) L.val) ≪≫
    (asIso (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction X.presheaf (ringSheaf
      X).property).counit).app L

/-- The right unitor sends the pure tensor `m ⊗ r` to `z` as soon as the presheaf right unitor
does. -/
private lemma tensorRightUnitor_hom_toSheafify_of_rightUnitor
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L : _root_.SheafOfModules.{u} (ringSheaf X)) (W : Opens X)
    (m : L.val.obj (Opposite.op W)) (r : (ringSheaf X).obj.obj (Opposite.op W))
    (z : L.val.obj (Opposite.op W))
    (hρ : ((ρ_ L.val).hom.app (Opposite.op W)).hom
      (m ⊗ₜ[X.presheaf.obj (Opposite.op W)] r) = z) :
    ((tensorRightUnitor X L).hom.val.app (Opposite.op W)).hom
      (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
        (L.val ⊗ (_root_.SheafOfModules.unit (ringSheaf X)).val)).app (Opposite.op W)).hom
          (m ⊗ₜ[X.presheaf.obj (Opposite.op W)] r)) = z := by
  have h1 := sheafify_map_toSheafify_apply X (ρ_ L.val).hom W
    (m ⊗ₜ[X.presheaf.obj (Opposite.op W)] r)
  change (((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction X.presheaf
      (ringSheaf X).property).counit.app L).val.app (Opposite.op W)).hom
    ((((Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf (ringSheaf X).property).map
        (ρ_ L.val).hom).val.app (Opposite.op W)).hom
      (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
        (L.val ⊗ (_root_.SheafOfModules.unit (ringSheaf X)).val)).app
          (Opposite.op W)).hom
        (m ⊗ₜ[X.presheaf.obj (Opposite.op W)] r))) = z
  rw [hρ] at h1
  exact (congrArg (fun z => (((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction
    X.presheaf
    (ringSheaf X).property).counit.app L).val.app (Opposite.op W)).hom z) h1).trans
      (sheafify_counit_toSheafify_apply X L W z)

/-- The right unitor sends the pure tensor `m ⊗ 1` to `m`. -/
lemma tensorRightUnitor_hom_toSheafify_apply
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L : _root_.SheafOfModules.{u} (ringSheaf X)) (W : Opens X)
    (m : L.val.obj (Opposite.op W)) :
    ((tensorRightUnitor X L).hom.val.app (Opposite.op W)).hom
      (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
        (L.val ⊗ (_root_.SheafOfModules.unit (ringSheaf X)).val)).app (Opposite.op W)).hom
          (m ⊗ₜ[X.presheaf.obj (Opposite.op W)]
            (1 : (ringSheaf X).obj.obj (Opposite.op W)))) = m :=
  tensorRightUnitor_hom_toSheafify_of_rightUnitor X L W m 1 m
    ((ModuleCat.MonoidalCategory.rightUnitor_hom_apply m 1).trans (one_smul _ m))

/-- The right unitor sends the pure tensor `m ⊗ r` to `r • m`. -/
lemma tensorRightUnitor_hom_toSheafify_smul
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L : _root_.SheafOfModules.{u} (ringSheaf X)) (W : Opens X)
    (m : L.val.obj (Opposite.op W)) (r : (ringSheaf X).obj.obj (Opposite.op W)) :
    ((tensorRightUnitor X L).hom.val.app (Opposite.op W)).hom
      (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
        (L.val ⊗ (_root_.SheafOfModules.unit (ringSheaf X)).val)).app (Opposite.op W)).hom
          (m ⊗ₜ[X.presheaf.obj (Opposite.op W)] r)) = r • m :=
  tensorRightUnitor_hom_toSheafify_of_rightUnitor X L W m r _
    (ModuleCat.MonoidalCategory.rightUnitor_hom_apply m r)

/-- The inverse of the right unitor sends `m` to the pure tensor `m ⊗ 1`. -/
lemma tensorRightUnitor_inv_apply
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L : _root_.SheafOfModules.{u} (ringSheaf X)) (W : Opens X)
    (m : L.val.obj (Opposite.op W)) :
    ((tensorRightUnitor X L).inv.val.app (Opposite.op W)).hom m =
      (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
        (L.val ⊗ (_root_.SheafOfModules.unit (ringSheaf X)).val)).app (Opposite.op W)).hom
          (m ⊗ₜ[X.presheaf.obj (Opposite.op W)]
            (1 : (ringSheaf X).obj.obj (Opposite.op W)))) := by
  let q := ((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
        (L.val ⊗ (_root_.SheafOfModules.unit (ringSheaf X)).val)).app (Opposite.op W)).hom
          (m ⊗ₜ[X.presheaf.obj (Opposite.op W)]
            (1 : (ringSheaf X).obj.obj (Opposite.op W)))
  have hq : ((tensorRightUnitor X L).hom.val.app (Opposite.op W)).hom q = m :=
    tensorRightUnitor_hom_toSheafify_apply X L W m
  exact (congrArg (fun z => ((tensorRightUnitor X L).inv.val.app (Opposite.op W)).hom z)
    hq).symm.trans (inv_app_hom_apply (tensorRightUnitor X L) (Opposite.op W) q)

/-- Associativity of the tensor product of sheaves of modules, in the form needed here:
`(L ⊗ M) ⊗ N ≅ L ⊗ (M ⊗ N)`. -/
noncomputable def tensorAssoc
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L M N : _root_.SheafOfModules.{u} (ringSheaf X)) :
    (tensorRightFunctor X N).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
            ⟨X.presheaf, X.IsSheaf⟩).obj L).obj M) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj L).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
            ⟨X.presheaf, X.IsSheaf⟩).obj M).obj N) := by
  let S := Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf (ringSheaf X).property
  let η := Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
  have h1 : IsIso (S.map (η (L.val ⊗ M.val) ▷ N.val)) :=
    Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight X.presheaf (ringSheaf
      X).property
      (η (L.val ⊗ M.val)) N.val
      (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify X.presheaf
        (ringSheaf X).property
        (L.val ⊗ M.val))
  have h2 : IsIso (S.map (L.val ◁ η (M.val ⊗ N.val))) :=
    Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerLeft X.presheaf (ringSheaf
      X).property
      L.val (η (M.val ⊗ N.val))
      (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify X.presheaf
        (ringSheaf X).property
        (M.val ⊗ N.val))
  exact (@asIso _ _ _ _ (S.map (η (L.val ⊗ M.val) ▷ N.val)) h1).symm ≪≫
    S.mapIso (MonoidalCategoryStruct.associator
      (C := PresheafOfModules.{u} (ringSheaf X).obj) L.val M.val N.val) ≪≫
    @asIso _ _ _ _ (S.map (L.val ◁ η (M.val ⊗ N.val))) h2

/-- The associativity isomorphism sends `(l ⊗ m) ⊗ n` to `l ⊗ (m ⊗ n)`. -/
lemma tensorAssoc_hom_pure
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L M N : _root_.SheafOfModules.{u} (ringSheaf X)) (W : Opens X)
    (l : L.val.obj (Opposite.op W)) (m : M.val.obj (Opposite.op W))
    (n : N.val.obj (Opposite.op W)) :
    ((tensorAssoc X L M N).hom.val.app (Opposite.op W)).hom
      (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
            ⟨X.presheaf, X.IsSheaf⟩).obj L).obj M).val ⊗ N.val)).app
          (Opposite.op W)).hom
        ((((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
          (L.val ⊗ M.val)).app (Opposite.op W)).hom
            (l ⊗ₜ[X.presheaf.obj (Opposite.op W)] m)) ⊗ₜ[X.presheaf.obj (Opposite.op W)] n)) =
      (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
        (L.val ⊗ (((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
            ⟨X.presheaf, X.IsSheaf⟩).obj M).obj N).val)).app
          (Opposite.op W)).hom
        (l ⊗ₜ[X.presheaf.obj (Opposite.op W)]
          (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
            (M.val ⊗ N.val)).app (Opposite.op W)).hom
            (m ⊗ₜ[X.presheaf.obj (Opposite.op W)] n)))) := by
  let S := Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf (ringSheaf X).property
  let η := Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
  let f := η (L.val ⊗ M.val) ▷ N.val
  let a := (MonoidalCategoryStruct.associator
    (C := PresheafOfModules.{u} (ringSheaf X).obj) L.val M.val N.val).hom
  let b := L.val ◁ η (M.val ⊗ N.val)
  let q := (l ⊗ₜ[X.presheaf.obj (Opposite.op W)] m) ⊗ₜ[X.presheaf.obj (Opposite.op W)] n
  have hf : IsIso (S.map f) :=
    Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight X.presheaf (ringSheaf
      X).property
      (η (L.val ⊗ M.val)) N.val
      (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify X.presheaf
        (ringSheaf X).property
        (L.val ⊗ M.val))
  have hfq : (f.app (Opposite.op W)).hom q =
      (((η (L.val ⊗ M.val)).app (Opposite.op W)).hom
        (l ⊗ₜ[X.presheaf.obj (Opposite.op W)] m)) ⊗ₜ[X.presheaf.obj (Opposite.op W)] n := rfl
  have haq : (a.app (Opposite.op W)).hom q =
      l ⊗ₜ[X.presheaf.obj (Opposite.op W)]
        (m ⊗ₜ[X.presheaf.obj (Opposite.op W)] n) := rfl
  have hbq : (b.app (Opposite.op W)).hom
      (l ⊗ₜ[X.presheaf.obj (Opposite.op W)] (m ⊗ₜ[X.presheaf.obj (Opposite.op W)] n)) =
      l ⊗ₜ[X.presheaf.obj (Opposite.op W)]
        (((η (M.val ⊗ N.val)).app (Opposite.op W)).hom
          (m ⊗ₜ[X.presheaf.obj (Opposite.op W)] n)) := rfl
  have hfSrc := sheafify_map_toSheafify_apply X f W q
  have ha := sheafify_map_toSheafify_apply X a W q
  have hb := sheafify_map_toSheafify_apply X b W
    (l ⊗ₜ[X.presheaf.obj (Opposite.op W)] (m ⊗ₜ[X.presheaf.obj (Opposite.op W)] n))
  rw [hfq] at hfSrc
  rw [haq] at ha
  rw [hbq] at hb
  have hinv := (congrArg (fun z => ((inv (S.map f)).val.app (Opposite.op W)).hom z)
      hfSrc).symm.trans
    (inv_app_hom_apply (asIso (S.map f)) (Opposite.op W)
      (((η ((L.val ⊗ M.val) ⊗ N.val)).app (Opposite.op W)).hom q))
  exact (congrArg (fun z => (((S.map b).val.app (Opposite.op W)).hom
      (((S.map a).val.app (Opposite.op W)).hom z))) hinv).trans
    ((congrArg (fun z => ((S.map b).val.app (Opposite.op W)).hom z) ha).trans hb)

/-- The braiding of `L` with itself, transported to the tensor product of sheaves. -/
noncomputable def tensorSelfBraid
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L : _root_.SheafOfModules.{u} (ringSheaf X)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).obj L).obj L ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
          ⟨X.presheaf, X.IsSheaf⟩).obj L).obj L :=
  (Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf (ringSheaf X).property).mapIso
    (BraidedCategory.braiding (C := PresheafOfModules.{u} (ringSheaf X).obj) L.val L.val)

/-- The braiding swaps the two factors of a pure tensor. -/
lemma tensorSelfBraid_hom_pure
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L : _root_.SheafOfModules.{u} (ringSheaf X)) (W : Opens X)
    (l m : L.val.obj (Opposite.op W)) :
    ((tensorSelfBraid X L).hom.val.app (Opposite.op W)).hom
      (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
        (L.val ⊗ L.val)).app (Opposite.op W)).hom
          (l ⊗ₜ[X.presheaf.obj (Opposite.op W)] m)) =
      (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
        (L.val ⊗ L.val)).app (Opposite.op W)).hom
          (m ⊗ₜ[X.presheaf.obj (Opposite.op W)] l)) :=
  sheafify_map_toSheafify_apply X
    (BraidedCategory.braiding (C := PresheafOfModules.{u} (ringSheaf X).obj) L.val L.val).hom W
    (l ⊗ₜ[X.presheaf.obj (Opposite.op W)] m)

/-- The automorphism of `L ⊗ (L ⊗ N)` swapping the first two factors. -/
noncomputable def tensorSwapFirstTwo
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L N : _root_.SheafOfModules.{u} (ringSheaf X)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj L).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
            ⟨X.presheaf, X.IsSheaf⟩).obj L).obj N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj L).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
            ⟨X.presheaf, X.IsSheaf⟩).obj L).obj N) :=
  (tensorAssoc X L L N).symm ≪≫
    (tensorRightFunctor X N).mapIso (tensorSelfBraid X L) ≪≫
    tensorAssoc X L L N

/-- The swap of the first two factors acts as expected on an iterated pure tensor. -/
lemma tensorSwapFirstTwo_hom_pure
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L N : _root_.SheafOfModules.{u} (ringSheaf X)) (W : Opens X)
    (m s : L.val.obj (Opposite.op W)) (t : N.val.obj (Opposite.op W)) :
    ((tensorSwapFirstTwo X L N).hom.val.app (Opposite.op W)).hom
      (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
        (L.val ⊗ (((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
            ⟨X.presheaf, X.IsSheaf⟩).obj L).obj N).val)).app (Opposite.op W)).hom
        (m ⊗ₜ[X.presheaf.obj (Opposite.op W)]
          (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
            (L.val ⊗ N.val)).app (Opposite.op W)).hom
            (s ⊗ₜ[X.presheaf.obj (Opposite.op W)] t)))) =
      (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
        (L.val ⊗ (((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
            ⟨X.presheaf, X.IsSheaf⟩).obj L).obj N).val)).app (Opposite.op W)).hom
        (s ⊗ₜ[X.presheaf.obj (Opposite.op W)]
          (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
            (L.val ⊗ N.val)).app (Opposite.op W)).hom
            (m ⊗ₜ[X.presheaf.obj (Opposite.op W)] t)))) := by
  let A := ((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩).obj L).obj L
  let η := Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
  let inner (a b : L.val.obj (Opposite.op W)) :=
    ((η (L.val ⊗ L.val)).app (Opposite.op W)).hom
      (a ⊗ₜ[X.presheaf.obj (Opposite.op W)] b)
  let raw (a b : L.val.obj (Opposite.op W)) :=
    ((η (A.val ⊗ N.val)).app (Opposite.op W)).hom
      (inner a b ⊗ₜ[X.presheaf.obj (Opposite.op W)] t)
  have h1 := tensorAssoc_hom_pure X L L N W m s t
  have h1inv := (congrArg
      (fun z => ((tensorAssoc X L L N).inv.val.app (Opposite.op W)).hom z) h1).symm.trans
    (inv_app_hom_apply (tensorAssoc X L L N) (Opposite.op W) (raw m s))
  have h2 : (((tensorRightFunctor X N).map (tensorSelfBraid X L).hom).val.app
      (Opposite.op W)).hom (raw m s) = raw s m := by
    have h := tensorRightFunctor_map_pure X A A N (tensorSelfBraid X L).hom W
      (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
        (L.val ⊗ L.val)).app (Opposite.op W)).hom
        (m ⊗ₜ[X.presheaf.obj (Opposite.op W)] s)) t
    exact h.trans (congrArg (fun z => ((η (A.val ⊗ N.val)).app (Opposite.op W)).hom
      (z ⊗ₜ[X.presheaf.obj (Opposite.op W)] t)) (tensorSelfBraid_hom_pure X L W m s))
  have h3 := tensorAssoc_hom_pure X L L N W s m t
  exact (congrArg (fun z => ((tensorAssoc X L L N).hom.val.app (Opposite.op W)).hom
      ((((tensorRightFunctor X N).map (tensorSelfBraid X L).hom).val.app
        (Opposite.op W)).hom z)) h1inv).trans
    ((congrArg (fun z => ((tensorAssoc X L L N).hom.val.app (Opposite.op W)).hom z) h2).trans h3)

/-- The automorphism of `L` determined by a tensor inverse `N` of `L` together with a
trivialisation of `L ⊗ N`. -/
noncomputable def tensorTwistAutomorphism
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L N : _root_.SheafOfModules.{u} (ringSheaf X))
    (e : ((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).obj L).obj N ≅
      _root_.SheafOfModules.unit (ringSheaf X)) : L ≅ L :=
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj L
  (tensorRightUnitor X L).symm ≪≫ T.mapIso e.symm ≪≫
    tensorSwapFirstTwo X L N ≪≫ T.mapIso e ≪≫ tensorRightUnitor X L

/-- Pairing with a fixed section `nW` of `N` over `W`, as a map of modules of sections. Stated
at the global module objects so that all instance synthesis happens here. -/
private noncomputable def tmulRight
    (X : RingedSpace.{u, w}) (L N : _root_.SheafOfModules.{u} (ringSheaf X))
    (W : Opens X) (nW : N.val.obj (Opposite.op W)) :
    L.val.obj (Opposite.op W) ⟶ (L.val ⊗ N.val).obj (Opposite.op W) :=
  ModuleCat.ofHom
    ((TensorProduct.mk (X.presheaf.obj (Opposite.op W))
      (L.val.obj (Opposite.op W)) (N.val.obj (Opposite.op W))).flip nW)

/-- A section `n` of the tensor inverse `N` over `U` gives, by pairing and trivialising, a
map from the restriction of `L` to `U` to the structure sheaf of the slice site. -/
private noncomputable def evalOver
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L N : _root_.SheafOfModules.{u} (ringSheaf X))
    (e : ((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).obj L).obj N ≅
      _root_.SheafOfModules.unit (ringSheaf X))
    (U : Opens X) (n : N.val.obj (Opposite.op U)) :
    L.over U ⟶ _root_.SheafOfModules.unit ((ringSheaf X).over U) := by
  let a := AlgebraicGeometry.SheafOfModules.tensorLeftFunctorUniversal X.presheaf
    (ringSheaf X).property L
  let ψ := e.hom.val
  refine ⟨PresheafOfModules.Hom.mk (fun V => ?_) ?_⟩
  · exact tmulRight X L N V.unop.left (N.val.map V.unop.hom.op n) ≫
      (a.ι.app N).app (Opposite.op V.unop.left) ≫ ψ.app (Opposite.op V.unop.left)
  · intro V W f
    ext m
    let v := V.unop.left
    let w := W.unop.left
    let h : Opposite.op v ⟶ Opposite.op w := ((Over.forget U).map f.unop).op
    let mv : L.val.obj (Opposite.op v) := m
    let nV : N.val.obj (Opposite.op v) := (N.val.map V.unop.hom.op).hom n
    have hn : (N.val.map h).hom nV = (N.val.map W.unop.hom.op).hom n := by
      change (N.val.presheaf.map h) ((N.val.presheaf.map V.unop.hom.op) n) =
        (N.val.presheaf.map W.unop.hom.op) n
      calc
        _ = N.val.presheaf.map (V.unop.hom.op ≫ h) n := by
          rw [Functor.map_comp]
          rfl
        _ = _ := by congr 1
    have hτ := PresheafOfModules.Monoidal.tensorObj_map_tmul h mv nV
    have ha := PresheafOfModules.naturality_apply (a.ι.app N) h
      (mv ⊗ₜ[X.presheaf.obj (Opposite.op v)] nV)
    have hψ := PresheafOfModules.naturality_apply ψ h
      (((a.ι.app N).app (Opposite.op v)).hom
        (mv ⊗ₜ[X.presheaf.obj (Opposite.op v)] nV))
    exact (congrArg (fun z => (ψ.app (Opposite.op w)).hom
          (((a.ι.app N).app (Opposite.op w)).hom
            ((L.val.map h).hom mv ⊗ₜ[X.presheaf.obj (Opposite.op w)] z))) hn).symm.trans
      ((congrArg (fun z => (ψ.app (Opposite.op w)).hom
            (((a.ι.app N).app (Opposite.op w)).hom z)) hτ).symm.trans
        ((congrArg (ψ.app (Opposite.op w)).hom ha).trans hψ))

/-- The map from the restriction of `L` to the free module of rank `n` determined by `n`
sections of the tensor inverse `N`. -/
private noncomputable def overToFree
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (U : Opens X) (n : ℕ)
    [HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) AddCommGrpCat.{u}]
    [((Opens.grothendieckTopology X.carrier).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    (L N : _root_.SheafOfModules.{u} (ringSheaf X))
    (e : ((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).obj L).obj N ≅
      _root_.SheafOfModules.unit (ringSheaf X))
    (t : Fin n → N.val.obj (Opposite.op U)) :
    L.over U ⟶ _root_.SheafOfModules.free (R := (ringSheaf X).over U) (ULift.{u} (Fin n)) :=
  ∑ i : Fin n, evalOver X L N e U (t i) ≫ _root_.SheafOfModules.ιFree (ULift.up i)

/-- The `i`-th component of `freeToOver` is the map classifying the `i`-th section. -/
private lemma ιFree_freeToOver
    (X : RingedSpace.{u, w}) (L : _root_.SheafOfModules.{u} (ringSheaf X))
    (U : Opens X) (n : ℕ)
    [HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) AddCommGrpCat.{u}]
    [((Opens.grothendieckTopology X.carrier).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    (s : Fin n → L.val.obj (Opposite.op U)) (i : Fin n) :
    _root_.SheafOfModules.ιFree (R := (ringSheaf X).over U) (ULift.up i) ≫
      freeToOver X L U n s =
        (L.over U).unitHomEquiv.symm (sectionOver X L U (s i)) := by
  rw [← _root_.SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  simp only [freeToOver, Equiv.apply_symm_apply]

/-- Pairing a section of `L` over `W` against a section of a tensor inverse `N` over `W`: form
the pure tensor, push it into the sheaf tensor product and read the result in the structure
sheaf through the trivialisation `e` of `L ⊗ N`.

The pairing is `𝒪(W)`-bilinear and natural in `W`, since each of the three steps is. -/
noncomputable def pairing
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L N : _root_.SheafOfModules.{u} (ringSheaf X))
    (e : ((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).obj L).obj N ≅
      _root_.SheafOfModules.unit (ringSheaf X))
    (W : Opens X) (m : L.val.obj (Opposite.op W)) (nW : N.val.obj (Opposite.op W)) :
    (ringSheaf X).obj.obj (Opposite.op W) :=
  (e.hom.val.app (Opposite.op W)).hom
    ((((AlgebraicGeometry.SheafOfModules.tensorLeftFunctorUniversal X.presheaf
      (ringSheaf X).property L).ι.app N).app (Opposite.op W)).hom
      (m ⊗ₜ[X.presheaf.obj (Opposite.op W)] nW))

/-- The twist automorphism of `L`, evaluated on a section over an open `W` lying under `U`.

If the section of `L ⊗ N` corresponding to `1` is represented over `U` by the finite sum of
pure tensors `∑ i, s i ⊗ t i`, then pairing a section `m` of `L` over `W` against each `t i`
and scaling the matching `s i` recovers the twist automorphism applied to `m`. This is the
local "dual basis" identity: it makes `freeToOver` a split epimorphism, and it is what shows
the nonvanishing locus of a section to be open (Tag 01CY). -/
theorem tensorTwistAutomorphism_hom_app_apply
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L N : _root_.SheafOfModules.{u} (ringSheaf X))
    (e : ((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).obj L).obj N ≅
      _root_.SheafOfModules.unit (ringSheaf X))
    (U : Opens X) (n : ℕ)
    (s : Fin n → L.val.obj (Opposite.op U))
    (t : Fin n → N.val.obj (Opposite.op U))
    (hsum :
      ((AlgebraicGeometry.SheafOfModules.tensorLeftFunctorUniversal X.presheaf
        (ringSheaf X).property L).ι.app N).app
          (Opposite.op U) (∑ i, s i ⊗ₜ[X.presheaf.obj (Opposite.op U)] t i) =
        (e.inv.val.app (Opposite.op U)).hom
          (1 : (ringSheaf X).obj.obj (Opposite.op U)))
    {W : Opens X} (j : Opposite.op U ⟶ Opposite.op W)
    (m : L.val.obj (Opposite.op W)) :
    ((tensorTwistAutomorphism X L N e).hom.val.app (Opposite.op W)).hom m =
      ∑ i : Fin n,
        pairing X L N e W m ((N.val.map j).hom (t i)) •
          ((L.val.map j).hom (s i) : L.val.obj (Opposite.op W)) := by
  let a := AlgebraicGeometry.SheafOfModules.tensorLeftFunctorUniversal X.presheaf
    (ringSheaf X).property L
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj L
  let B := T.obj N
  let η := Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf (ringSheaf X).property
  let mv : L.val.obj (Opposite.op W) := m
  let sv (i : Fin n) : L.val.obj (Opposite.op W) := (L.val.map j).hom (s i)
  let tw (i : Fin n) : N.val.obj (Opposite.op W) := (N.val.map j).hom (t i)
  let ev (i : Fin n) : (ringSheaf X).obj.obj (Opposite.op W) :=
    (e.hom.val.app (Opposite.op W)).hom
      (((a.ι.app N).app (Opposite.op W)).hom
        (mv ⊗ₜ[X.presheaf.obj (Opposite.op W)] tw i))
  let q (i : Fin n) : B.val.obj (Opposite.op W) :=
    ((η (L.val ⊗ N.val)).app (Opposite.op W)).hom
      (sv i ⊗ₜ[X.presheaf.obj (Opposite.op W)] tw i)
  -- The defining relation, restricted to `W`.
  have hmap : ((L.val ⊗ N.val).map j).hom
      (∑ i : Fin n, s i ⊗ₜ[X.presheaf.obj (Opposite.op U)] t i) =
        ∑ i : Fin n, sv i ⊗ₜ[X.presheaf.obj (Opposite.op W)] tw i :=
    (map_sum ((L.val ⊗ N.val).map j).hom
        (fun i => s i ⊗ₜ[X.presheaf.obj (Opposite.op U)] t i) Finset.univ).trans
      (Finset.sum_congr rfl fun i _ =>
        PresheafOfModules.Monoidal.tensorObj_map_tmul j (s i) (t i))
  have hunit : (((_root_.SheafOfModules.unit (ringSheaf X)).val.map j).hom
      (1 : (ringSheaf X).obj.obj (Opposite.op U))) =
      (1 : (ringSheaf X).obj.obj (Opposite.op W)) :=
    PresheafOfModules.unit_map_one (ringSheaf X).obj j
  have he := PresheafOfModules.naturality_apply e.inv.val j
    (1 : (ringSheaf X).obj.obj (Opposite.op U))
  have hn := PresheafOfModules.naturality_apply (a.ι.app N) j
    (∑ i : Fin n, s i ⊗ₜ[X.presheaf.obj (Opposite.op U)] t i)
  have hsumW : ((a.ι.app N).app (Opposite.op W)).hom
      (∑ i : Fin n, sv i ⊗ₜ[X.presheaf.obj (Opposite.op W)] tw i) =
        (e.inv.val.app (Opposite.op W)).hom
          (1 : (ringSheaf X).obj.obj (Opposite.op W)) :=
    (congrArg (fun z => ((a.ι.app N).app (Opposite.op W)).hom z) hmap).symm.trans
      (hn.trans ((congrArg (fun z => (B.val.map j).hom z) hsum).trans
        (he.symm.trans (congrArg (e.inv.val.app (Opposite.op W)).hom hunit))))
  have hq : (∑ i : Fin n, q i) =
      (e.inv.val.app (Opposite.op W)).hom
        (1 : (ringSheaf X).obj.obj (Opposite.op W)) :=
    (map_sum ((a.ι.app N).app (Opposite.op W)).hom _ _).symm.trans hsumW
  -- The twist automorphism, computed on the section `m`.
  have e1 : ((tensorRightUnitor X L).inv.val.app (Opposite.op W)).hom m =
      ((η (L.val ⊗ (_root_.SheafOfModules.unit (ringSheaf X)).val)).app
        (Opposite.op W)).hom
        (mv ⊗ₜ[X.presheaf.obj (Opposite.op W)]
          (1 : (ringSheaf X).obj.obj (Opposite.op W))) :=
    tensorRightUnitor_inv_apply X L W mv
  have e2 := tensorLeftFunctor_map_pure X L
    (_root_.SheafOfModules.unit (ringSheaf X)) B e.inv W mv
    (1 : (ringSheaf X).obj.obj (Opposite.op W))
  have e3 : ((η (L.val ⊗ B.val)).app (Opposite.op W)).hom
        (mv ⊗ₜ[X.presheaf.obj (Opposite.op W)]
          ((e.inv.val.app (Opposite.op W)).hom
            (1 : (ringSheaf X).obj.obj (Opposite.op W)))) =
      ∑ i : Fin n, ((η (L.val ⊗ B.val)).app (Opposite.op W)).hom
        (mv ⊗ₜ[X.presheaf.obj (Opposite.op W)] q i) := by
    rw [← hq, TensorProduct.tmul_sum]
    exact map_sum ((η (L.val ⊗ B.val)).app (Opposite.op W)).hom _ Finset.univ
  have e4 : ((tensorSwapFirstTwo X L N).hom.val.app (Opposite.op W)).hom
        (∑ i : Fin n, ((η (L.val ⊗ B.val)).app (Opposite.op W)).hom
          (mv ⊗ₜ[X.presheaf.obj (Opposite.op W)] q i)) =
      ∑ i : Fin n, ((η (L.val ⊗ B.val)).app (Opposite.op W)).hom
        (sv i ⊗ₜ[X.presheaf.obj (Opposite.op W)]
          ((η (L.val ⊗ N.val)).app (Opposite.op W)).hom
            (mv ⊗ₜ[X.presheaf.obj (Opposite.op W)] tw i)) :=
    (map_sum ((tensorSwapFirstTwo X L N).hom.val.app (Opposite.op W)).hom _
        Finset.univ).trans
      (Finset.sum_congr rfl fun i _ =>
        tensorSwapFirstTwo_hom_pure X L N W mv (sv i) (tw i))
  have e5 : ((T.map e.hom).val.app (Opposite.op W)).hom
        (∑ i : Fin n, ((η (L.val ⊗ B.val)).app (Opposite.op W)).hom
          (sv i ⊗ₜ[X.presheaf.obj (Opposite.op W)]
            ((η (L.val ⊗ N.val)).app (Opposite.op W)).hom
              (mv ⊗ₜ[X.presheaf.obj (Opposite.op W)] tw i))) =
      ∑ i : Fin n,
        ((η (L.val ⊗ (_root_.SheafOfModules.unit (ringSheaf X)).val)).app
          (Opposite.op W)).hom
          (sv i ⊗ₜ[X.presheaf.obj (Opposite.op W)]
            (e.hom.val.app (Opposite.op W)).hom
              (((η (L.val ⊗ N.val)).app (Opposite.op W)).hom
                (mv ⊗ₜ[X.presheaf.obj (Opposite.op W)] tw i))) :=
    (map_sum ((T.map e.hom).val.app (Opposite.op W)).hom _ Finset.univ).trans
      (Finset.sum_congr rfl fun i _ =>
        tensorLeftFunctor_map_pure X L B (_root_.SheafOfModules.unit (ringSheaf X)) e.hom W
          (sv i) _)
  have e6 : ((tensorRightUnitor X L).hom.val.app (Opposite.op W)).hom
        (∑ i : Fin n,
          ((η (L.val ⊗ (_root_.SheafOfModules.unit (ringSheaf X)).val)).app
            (Opposite.op W)).hom
            (sv i ⊗ₜ[X.presheaf.obj (Opposite.op W)]
              (e.hom.val.app (Opposite.op W)).hom
                (((η (L.val ⊗ N.val)).app (Opposite.op W)).hom
                  (mv ⊗ₜ[X.presheaf.obj (Opposite.op W)] tw i)))) =
      ∑ i : Fin n, ev i • sv i :=
    (map_sum ((tensorRightUnitor X L).hom.val.app (Opposite.op W)).hom _ Finset.univ).trans
      (Finset.sum_congr rfl fun i _ =>
        tensorRightUnitor_hom_toSheafify_smul X L W (sv i) _)
  have htwist : ((tensorTwistAutomorphism X L N e).hom.val.app (Opposite.op W)).hom mv =
      ∑ i : Fin n, ev i • sv i :=
    (congrArg (fun z => ((tensorRightUnitor X L).hom.val.app (Opposite.op W)).hom
        (((T.map e.hom).val.app (Opposite.op W)).hom
          (((tensorSwapFirstTwo X L N).hom.val.app (Opposite.op W)).hom
            (((T.map e.inv).val.app (Opposite.op W)).hom z)))) e1).trans
      ((congrArg (fun z => ((tensorRightUnitor X L).hom.val.app (Opposite.op W)).hom
          (((T.map e.hom).val.app (Opposite.op W)).hom
            (((tensorSwapFirstTwo X L N).hom.val.app (Opposite.op W)).hom z)))
        (e2.trans e3)).trans
        ((congrArg (fun z => ((tensorRightUnitor X L).hom.val.app (Opposite.op W)).hom
            (((T.map e.hom).val.app (Opposite.op W)).hom z)) e4).trans
          ((congrArg (fun z => ((tensorRightUnitor X L).hom.val.app
            (Opposite.op W)).hom z) e5).trans e6)))
  exact htwist

/-- The composite of `overToFree` with `freeToOver` is the restriction of the twist
automorphism of `L`: this is the computation that makes `freeToOver` a split epimorphism. -/
private lemma overToFree_comp_freeToOver
    (X : RingedSpace.{u, w})
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L N : _root_.SheafOfModules.{u} (ringSheaf X))
    (e : ((Stacks.SheafOfModules.Tensor.sheafTensor.{w, w, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).obj L).obj N ≅
      _root_.SheafOfModules.unit (ringSheaf X))
    (U : Opens X) (n : ℕ)
    [HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) AddCommGrpCat.{u}]
    [((Opens.grothendieckTopology X.carrier).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    (s : Fin n → L.val.obj (Opposite.op U))
    (t : Fin n → N.val.obj (Opposite.op U))
    (hsum :
      ((AlgebraicGeometry.SheafOfModules.tensorLeftFunctorUniversal X.presheaf
        (ringSheaf X).property L).ι.app N).app
          (Opposite.op U) (∑ i, s i ⊗ₜ[X.presheaf.obj (Opposite.op U)] t i) =
        (e.inv.val.app (Opposite.op U)).hom
          (1 : (ringSheaf X).obj.obj (Opposite.op U))) :
    overToFree X U n L N e t ≫ freeToOver X L U n s =
      ((_root_.SheafOfModules.overFunctor (ringSheaf X) U).mapIso
        (tensorTwistAutomorphism X L N e)).hom := by
  have hgf : overToFree X U n L N e t ≫ freeToOver X L U n s =
      ∑ i : Fin n, evalOver X L N e U (t i) ≫
        (L.over U).unitHomEquiv.symm (sectionOver X L U (s i)) := by
    rw [overToFree, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Category.assoc, ιFree_freeToOver]
  ext V m
  refine Eq.trans ?_ (tensorTwistAutomorphism_hom_app_apply X L N e U n s t hsum
    (W := V.unop.left) V.unop.hom.op m).symm
  rw [hgf]
  exact sum_app_apply _ _ V m

/-- **Stacks Project, Tag 0B8K.** An invertible sheaf of modules is locally a direct
summand of a finite free sheaf. -/
@[stacks 0B8K "locally_finite_free_summand"]
theorem isLocallyFiniteFreeSummand_of_isInvertible
    (X : RingedSpace.{u, w}) (L : _root_.SheafOfModules.{u} (ringSheaf X))
    [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U : Opens X,
      HasWeakSheafify (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
        AddCommGrpCat.{u}]
    [∀ U : Opens X,
      (Opens.grothendieckTopology
        (X.restrict U.isOpenEmbedding).carrier).WEqualsLocallyBijective
        AddCommGrpCat.{u}]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ X.presheaf
        (forget₂ CommRingCat.{u} RingCat.{u}) X.IsSheaf) L) :
    ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (n : ℕ),
      Nonempty (Retract ((modulePullback (X.ofRestrict U.isOpenEmbedding)).obj L)
        (_root_.SheafOfModules.free (ULift.{u} (Fin n)))) := by
  obtain ⟨N, ⟨e⟩⟩ := exists_tensor_inverse X L hL
  intro x
  obtain ⟨U, hx, n, s, t, hsum⟩ :=
    exists_local_finite_tensor_representation X L N e x
  have : HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U)
      AddCommGrpCat.{u} := hasWeakSheafifyOver X U
  have : ((Opens.grothendieckTopology X.carrier).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u} := wEqualsLocallyBijectiveOver X U
  let f := freeToOver X L U n s
  let g := overToFree X U n L N e t
  have hgf : g ≫ f =
      ((_root_.SheafOfModules.overFunctor (ringSheaf X) U).mapIso
        (tensorTwistAutomorphism X L N e)).hom :=
    overToFree_comp_freeToOver X L N e U n s t hsum
  have hiso : IsIso (g ≫ f) := by
    rw [hgf]
    infer_instance
  have : IsSplitEpi f := ⟨⟨{
    section_ := inv (g ≫ f) ≫ g
    id := by rw [Category.assoc, IsIso.inv_hom_id] }⟩⟩
  exact ⟨U, hx, n, retract_of_splitEpi_over X L U (ULift.{u} (Fin n)) f⟩

end Stacks.SheafOfModules.LocallyFiniteFree












end
