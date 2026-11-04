module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Topology.Sheaves.Module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksCore.Tactic.StacksAttribute

/-!
# Direct summands of finite locally free sheaves of modules

On a ringed space whose structure-sheaf stalks are local rings, a direct summand of a finite
locally free sheaf of modules is again finite locally free.

## Main results

* `Stacks.SheafOfModules.isFiniteLocallyFree_of_retract`: a retract of a finite locally free
  sheaf of modules is finite locally free when every stalk of the structure sheaf is a local
  ring.
* `Stacks.SheafOfModules.presentationOfRetractFree`: a retract of a free sheaf of modules is
  presented by the complementary idempotent; with a finite index type that presentation is
  finite, so such a retract is of finite presentation.

## Implementation notes

A direct summand is recorded by a categorical `Retract`, whose section followed by its
retraction is the identity.

Two models of the restriction of a sheaf of modules to an open set occur. A
`SheafOfModules.LocalGeneratorsData` trivialises `F.over U` on the slice site over `U`, while
`LocallyFreeRank.Trivialization`, and with it the stalk computation
`LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp`, is stated for
`LocallyFreeRank.restrictMod`, the pushforward along the open-inclusion functor
`Opens U ⥤ Opens X`. `TopologicalSpace.Opens.sheafOfModulesEquivOver` is the equivalence
between the two, and `SheafOfModules.mapFreeIso` carries free sheaves to free sheaves across
it, so a trivialisation in the second model is built from a free presentation in the first by
`trivializationOfFreeIso`. No comparison of ranks is needed, because the generators of a
finite-type local generators datum are already indexed by a finite type.

Scalars are a second bookkeeping layer: the stalk computation is over the stalk of the sheaf
of commutative rings, whereas a sheaf of modules lives over the underlying sheaf of rings.
The two stalks are identified by `SemilinearStalk.commStalkRingEquiv`, compatibly with the
two actions by `SemilinearStalk.comm_smul_eq`, and a linear equivalence onto
a free module is transported along that identification by `linearEquivOfRingEquiv`, which is
pure module theory and mentions no sheaf.

## References

* [Stacks Project, Tag 0BCI](https://stacks.math.columbia.edu/tag/0BCI)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.SheafOfModules

/-- Transport of a linear equivalence onto a free module along a ring equivalence of the
scalars whose two actions on the source agree. -/
private noncomputable def linearEquivOfRingEquiv
    {S K M ι : Type u} [Ring S] [Ring K] [AddCommGroup M] [Module S M] [Module K M]
    (eR : S ≃+* K) (hscalar : ∀ (s : S) (m : M), eR s • m = s • m)
    (e : M ≃ₗ[K] (ι →₀ K)) : M ≃ₗ[S] (ι →₀ S) := by
  letI : Module S K := Module.compHom K eR.toRingHom
  let e' : M ≃ₗ[S] (ι →₀ K) :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' s m := calc
        e (s • m) = e (eR s • m) := by rw [hscalar]
        _ = eR s • e m := e.map_smul _ _
        _ = s • e m := rfl }
  let ce : K ≃ₗ[S] S :=
    { toFun := eR.symm
      invFun := eR
      left_inv := eR.apply_symm_apply
      right_inv := eR.symm_apply_apply
      map_add' := eR.symm.map_add
      map_smul' := by
        intro s c
        change eR.symm (eR s * c) = s * eR.symm c
        apply eR.injective
        simp }
  exact e'.trans (Finsupp.mapRange.linearEquiv (α := ι) ce)

/-- A trivialisation of `F` on an open set where `F` is free: the isomorphism
`free I ≅ F.over U` on the slice site over `U` is transported to the site `Opens U` by
`TopologicalSpace.Opens.sheafOfModulesEquivOver`, which carries the free sheaf to the free
sheaf on the same index type. -/
private noncomputable def trivializationOfFreeIso
    {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    {F : _root_.SheafOfModules.{u} R} (U : Opens X) (I : Type u)
    (e : _root_.SheafOfModules.free I ≅ F.over U) :
    LocallyFreeRank.Trivialization X R F U where
  ι := I
  iso :=
    (_root_.SheafOfModules.mapFreeIso (U.sheafOfModulesEquivOver R).functor I
        (U.sheafOfModulesEquivOverUnit R) ≪≫
      (U.sheafOfModulesEquivOver R).functor.mapIso e ≪≫
      (show (U.sheafOfModulesEquivOver R).functor.obj (F.over U) ≅
        LocallyFreeRank.restrictMod X U R F from Iso.refl _)).symm

/-- Where a sheaf of modules is free on an open set, its stalk is free on the same index
type over the stalk of the sheaf of commutative rings. -/
private lemma exists_stalk_linearEquiv_of_freeIso
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (H : _root_.SheafOfModules.{u} (LocallyFreeRank.toRingSheaf X O))
    (U : Opens X) (I : Type u)
    (e : _root_.SheafOfModules.free I ≅ H.over U) (x : X) (hx : x ∈ U) :
    Nonempty (ToType (TopCat.Presheaf.stalk H.val.presheaf x)
      ≃ₗ[ToType (TopCat.Presheaf.stalk O.obj x)]
      (I →₀ ToType (TopCat.Presheaf.stalk O.obj x))) :=
  LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp X O H x hx
    (trivializationOfFreeIso U I e)

/-- The stalk maps of a retract of sheaves of modules split the stalk. -/
private lemma stalkLMap_comp_eq_id
    {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    {F H : _root_.SheafOfModules.{u} R}
    (i : F ⟶ H) (r : H ⟶ F) (hir : i ≫ r = 𝟙 F) (x : X) :
    (LocallyFreeRank.stalkLMap r.val x).comp (LocallyFreeRank.stalkLMap i.val x) =
      LinearMap.id := by
  have hval : i.val ≫ r.val = 𝟙 F.val := congrArg _root_.SheafOfModules.Hom.val hir
  set si := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf R.obj).map i.val) with hsi
  set sr := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf R.obj).map r.val) with hsr
  have hmorph : si ≫ sr = 𝟙 _ := by
    rw [hsi, hsr, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      hval, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  ext m
  have hm := congrArg (fun φ ↦ (ConcreteCategory.hom φ) m) hmorph
  have hEval := ConcreteCategory.comp_apply (C := AddCommGrpCat.{u}) si sr m
  have hId := ConcreteCategory.id_apply (C := AddCommGrpCat.{u})
    (X := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      ((PresheafOfModules.toPresheaf R.obj).obj F.val)) (x := m)
  exact hEval.symm.trans (hm.trans hId)

/-- A retract of a free sheaf of modules is presented by the complementary idempotent. -/
noncomputable def presentationOfRetractFree
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {F : _root_.SheafOfModules.{u} R} {I : Type u}
    (i : F ⟶ _root_.SheafOfModules.free I) (r : _root_.SheafOfModules.free I ⟶ F)
    (hir : i ≫ r = 𝟙 F) : F.Presentation := by
  let f := 𝟙 (_root_.SheafOfModules.free (R := R) I) - r ≫ i
  have hfg : f ≫ r = 0 := by simp [f, hir]
  exact _root_.SheafOfModules.presentationOfIsCokernelFree f r hfg <|
    Limits.CokernelCofork.IsColimit.ofπ r hfg
      (fun k _ ↦ i ≫ k)
      (fun k hk ↦ by
        change (𝟙 _ - r ≫ i) ≫ k = 0 at hk
        rw [Preadditive.sub_comp, Category.id_comp, sub_eq_zero] at hk
        simpa only [Category.assoc] using hk.symm)
      (fun k _ m hm ↦ by
        rw [← Category.id_comp m, ← hir, Category.assoc, hm])

/-- The presentation of a retract of a free sheaf of modules on a *finite* index type is
finite: both its generators and its relations are indexed by that type. -/
instance presentationOfRetractFree_isFinite
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {F : _root_.SheafOfModules.{u} R} {I : Type u} [Finite I]
    (i : F ⟶ _root_.SheafOfModules.free I) (r : _root_.SheafOfModules.free I ⟶ F)
    (hir : i ≫ r = 𝟙 F) : (presentationOfRetractFree i r hir).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite I)⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite I)⟩

/-- A retract of a finite locally free sheaf of modules is finitely presented. -/
private lemma isFinitePresentation_of_retract
    {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    {F H : _root_.SheafOfModules.{u} R}
    (i : F ⟶ H) (r : H ⟶ F) (hir : i ≫ r = 𝟙 F)
    (hH : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := R) H) :
    F.IsFinitePresentation := by
  classical
  obtain ⟨q, hq, hqf⟩ := hH.exists_isFiniteLocallyFreeData
  have : q.IsLocallyFreeData := hq
  have : q.IsFiniteType := hqf
  let σ : F.QuasicoherentData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      presentation j := by
        have hπ : IsIso (q.generators j).π := hq.isIso j
        refine presentationOfRetractFree
          ((_root_.SheafOfModules.overFunctor R (q.X j)).map i ≫ inv (q.generators j).π)
          ((q.generators j).π ≫ (_root_.SheafOfModules.overFunctor R (q.X j)).map r) ?_
        rw [Category.assoc, IsIso.inv_hom_id_assoc, ← CategoryTheory.Functor.map_comp, hir,
          CategoryTheory.Functor.map_id] }
  refine { exists_quasicoherentData := ⟨σ,
    _root_.SheafOfModules.QuasicoherentData.IsFinitePresentation.mk (q := σ) (fun j ↦ ?_)⟩ }
  dsimp [σ]
  have : Finite (q.generators j).I := (hqf.isFiniteType j).finite
  infer_instance

/-- The stalk of a retract of a finite locally free sheaf of modules is a finite free module
over the stalk of the underlying sheaf of rings. -/
private lemma exists_free_stalk_of_retract
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    {F H : _root_.SheafOfModules.{u} (LocallyFreeRank.toRingSheaf X O)}
    (i : F ⟶ H) (r : H ⟶ F) (hir : i ≫ r = 𝟙 F)
    (hH : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (R := LocallyFreeRank.toRingSheaf X O) H)
    (hloc : ∀ y : X, IsLocalRing (ToType (TopCat.Presheaf.stalk O.obj y))) (x : X) :
    ∃ n : ℕ, Nonempty
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)
        ≃ₗ[ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (LocallyFreeRank.toRingSheaf X O).obj x)]
        (ULift.{u} (Fin n) →₀ ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (LocallyFreeRank.toRingSheaf X O).obj x))) := by
  classical
  let S := ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
    (LocallyFreeRank.toRingSheaf X O).obj x)
  let K := ToType (TopCat.Presheaf.stalk O.obj x)
  let eR : S ≃+* K := SemilinearStalk.commStalkRingEquiv O.obj x
  let _ : CommRing S :=
    { (inferInstance : Ring S) with
      mul_comm := fun a b ↦ eR.injective (by simp only [map_mul, mul_comm]) }
  have : IsLocalRing K := hloc x
  have : IsLocalRing S := eR.symm.isLocalRing
  obtain ⟨q, hq, hqf⟩ := hH.exists_isFiniteLocallyFreeData
  obtain ⟨j, hxj⟩ := ((Opens.coversTop_iff (X : Type u) q.X).mp q.coversTop).exists_mem x
  have hfin : Finite (q.generators j).I := (hqf.isFiniteType j).finite
  have hiso : IsIso (q.generators j).π := hq.isIso j
  obtain ⟨eH⟩ := exists_stalk_linearEquiv_of_freeIso O H (q.X j) (q.generators j).I
    (asIso (q.generators j).π) x hxj
  have eH' : ToType (TopCat.Presheaf.stalk H.val.presheaf x) ≃ₗ[S]
      ((q.generators j).I →₀ S) :=
    linearEquivOfRingEquiv eR
      (fun s m ↦ SemilinearStalk.comm_smul_eq O.obj x H.val s m) eH
  let bH := (Finsupp.basisSingleOne (R := S) (ι := (q.generators j).I)).map eH'.symm
  have : Module.Free S (ToType (TopCat.Presheaf.stalk H.val.presheaf x)) :=
    Module.Free.of_basis bH
  have : Module.Finite S (ToType (TopCat.Presheaf.stalk H.val.presheaf x)) :=
    Module.Finite.of_basis bH
  let iS := LocallyFreeRank.stalkLMap i.val x
  let rS := LocallyFreeRank.stalkLMap r.val x
  have hsplit : rS.comp iS = LinearMap.id := stalkLMap_comp_eq_id i r hir x
  have hsurj : Function.Surjective rS := fun y ↦
    ⟨iS y, congrArg (fun f : _ →ₗ[S] _ ↦ f y) hsplit⟩
  have : Module.Projective S (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
    Module.Projective.of_split iS rS hsplit
  have : Module.Flat S (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
    Module.Flat.of_retract iS rS hsplit
  have : Module.Finite S (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
    Module.Finite.of_surjective rS hsurj
  have : Module.Free S (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
    Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis S (ToType (TopCat.Presheaf.stalk F.val.presheaf x))
  have : Finite (Module.Free.ChooseBasisIndex S
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x))) := Module.Finite.finite_basis b
  let _ : Fintype (Module.Free.ChooseBasisIndex S
    (ToType (TopCat.Presheaf.stalk F.val.presheaf x))) := Fintype.ofFinite _
  exact ⟨_, ⟨b.repr.trans ((Finsupp.domLCongr (Fintype.equivFin _)).trans
    (Finsupp.domLCongr Equiv.ulift.symm))⟩⟩

/-- Pushing the canonical generating sections of a free sheaf of modules along an isomorphism
gives generating sections whose own projection is an isomorphism. -/
private lemma isIso_ofEpi_free_generatingSections_π
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {N : _root_.SheafOfModules.{u} R} (I : Type u)
    (p : _root_.SheafOfModules.free I ⟶ N) [IsIso p] :
    IsIso ((_root_.SheafOfModules.free.generatingSections I).ofEpi p).π := by
  have h₁ : IsIso (_root_.SheafOfModules.free.generatingSections (R := R) I).π :=
    inferInstance
  rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ ‹IsIso p›

/-- Pushing the canonical generating sections of a free sheaf of modules on a finite index type
along an epimorphism gives generating sections of finite type. -/
private lemma isFiniteType_ofEpi_free_generatingSections
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {N : _root_.SheafOfModules.{u} R} (I : Type u) [Finite I]
    (p : _root_.SheafOfModules.free I ⟶ N) [Epi p] :
    ((_root_.SheafOfModules.free.generatingSections I).ofEpi p).IsFiniteType :=
  ⟨inferInstanceAs (Finite I)⟩

/-- The local generators datum assembled from free charts around every point. -/
private noncomputable def freeChartsData
    {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (F : _root_.SheafOfModules.{u} R) (U : X → Opens X) (n : X → ℕ)
    (hxU : ∀ x, x ∈ U x)
    (he : ∀ x, Nonempty (F.over (U x) ≅ _root_.SheafOfModules.free (ULift.{u} (Fin (n x))))) :
    F.LocalGeneratorsData where
  I := X
  X := U
  coversTop := (Opens.coversTop_iff (X : Type u) U).mpr <|
    Opens.ext <| Set.eq_univ_of_forall fun x ↦ le_iSup U x (hxU x)
  generators := fun x ↦
    (_root_.SheafOfModules.free.generatingSections
      (ULift.{u} (Fin (n x)))).ofEpi (he x).some.inv

/-- A sheaf of modules that is free of finite rank on an open neighbourhood of every point is
finite locally free. -/
private lemma isFiniteLocallyFree_of_free_charts
    {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (F : _root_.SheafOfModules.{u} R) (U : X → Opens X) (n : X → ℕ)
    (hxU : ∀ x, x ∈ U x)
    (he : ∀ x, Nonempty (F.over (U x) ≅ _root_.SheafOfModules.free (ULift.{u} (Fin (n x))))) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := R) F := by
  classical
  exact (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u}
    (C := Opens X) (M := F)) ⟨freeChartsData F U n hxU he,
      { isIso := fun x ↦ isIso_ofEpi_free_generatingSections_π _ (he x).some.inv },
      { isFiniteType := fun x ↦ isFiniteType_ofEpi_free_generatingSections _ (he x).some.inv }⟩

/-- **Stacks Project, Tag 0BCI.** A direct summand of a finite locally free sheaf of modules
on a ringed space whose structure-sheaf stalks are local rings is finite locally free. -/
@[stacks 0BCI, sga "6 I 2.15.1" "ringed space case"]
theorem isFiniteLocallyFree_of_retract
    {X : TopCat.{u}} {O : TopCat.Sheaf CommRingCat.{u} X}
    [∀ x : X, IsLocalRing (ToType (O.presheaf.stalk x))]
    {F H : _root_.SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat RingCat)).obj O)}
    (hF : Nonempty (@Retract (_root_.SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat RingCat)).obj O))
      _root_.SheafOfModules.instCategory F H))
    (hH : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (R := (sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat RingCat)).obj O) H) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (R := (sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat RingCat)).obj O) F := by
  classical
  obtain ⟨i, r, hir⟩ := hF.some
  have hchart : ∀ x : X, ∃ U : Opens X, ∃ m : ℕ, x ∈ U ∧
      Nonempty (F.over U ≅ _root_.SheafOfModules.free (ULift.{u} (Fin m))) := by
    intro x
    obtain ⟨m, hx⟩ := exists_free_stalk_of_retract O i r hir hH (fun y ↦ inferInstance) x
    obtain ⟨U, hxU, e⟩ := exists_iso_free_over_of_stalk_iso_free F
      (isFinitePresentation_of_retract i r hir hH) x m hx
    exact ⟨U, m, hxU, e⟩
  choose U n hxU he using hchart
  exact isFiniteLocallyFree_of_free_charts F U n hxU he

end Stacks.SheafOfModules
