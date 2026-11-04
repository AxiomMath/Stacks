module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaGoodBaseChange.StalkGoodInput
public import StacksFrontier.Homology.Eta.Perfect.BoundedComplexPerfectModel
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackFromTheStalkCriterion
public import StacksFrontier.Topology.Sheaves.Modules.StalkRestrictOpenExactness

/-!
# The stalk inputs of the goodness form of Tag 0F9X

`Stacks.IdealTorsion.Eta.quasiIso_comp_pullbackEtaMap_of_forall_stalk_good` asks, at every point
of the source, for a good finite free model of the stalk complex together with K-flatness of the
stalk complexes of `F^•` and `P^•` and flatness of the terms of the former.  This file supplies
those three inputs from global hypotheses, so that what is left is exactly the goodness of the
triple read at the stalks.

## Main results

* `Stacks.IdealTorsion.Eta.moduleGrpStalk_eq_stalkModuleFunctor_isModule`: **the two
  `𝒪_{X,x}`-module structures on the stalk of a sheaf of modules agree** — the
  germ-representative one and the restriction of scalars along
  `SemilinearStalk.commStalkIso` of the module over the `RingCat`-valued
  stalk.
* `Stacks.IdealTorsion.Eta.flat_stalkModuleFunctor_obj_of_isFlat`: hence a flat sheaf of modules
  has flat stalks in the spelling the décalage calculus uses.
* `Stacks.IdealTorsion.Eta.kFlat_stalkComplex_of_isKFlat`: the stalk complex of a K-flat complex
  of sheaves of modules is K-flat, in the `Stacks.IdealTorsion.Eta.stalkComplex` spelling over
  the `CommRingCat`-valued stalk.
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory

open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk grpStalk stalkModule)

open Stacks.RingedSpace (pullbackFunctor commStalkGermMap)

universe u

namespace Stacks.IdealTorsion.Eta

variable (X : RingedSpace.{u}) (x : X.carrier)

/-- **The two `𝒪_{X,x}`-module structures on the stalk of a sheaf of modules agree.**  One is the
germ-representative structure `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`, which
`Stacks.IdealTorsion.Eta.moduleGrpStalk` restates at the
`Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf` spelling; the other is restriction of scalars
along `SemilinearStalk.commStalkIso` of the module over the `RingCat`-valued stalk, which is the
structure `Stacks.IdealTorsion.Eta.stalkModuleFunctor` carries.

The comparison for the *structure sheaf* is `Stacks.SheafOfModules.stalkModule_eq`, which
identifies the germ-representative structure with Mathlib's; the remaining half is
`SemilinearStalk.comm_smul_eq`, the agreement of the `CommRingCat`- and
`RingCat`-valued stalk actions through `commStalkRingEquiv`. -/
theorem moduleGrpStalk_eq_stalkModuleFunctor_isModule
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :
    moduleGrpStalk X M x = ((stalkModuleFunctor X x).obj M).isModule := by
  change stalkModule X M.val x = _
  rw [Stacks.SheafOfModules.stalkModule_eq X M.val x]
  refine Module.ext' _ _ fun r m => ?_
  have hs : SemilinearStalk.commStalkRingEquiv X.presheaf x
      ((SemilinearStalk.commStalkIso X.presheaf x).inv.hom r) = r :=
    (SemilinearStalk.commStalkRingEquiv X.presheaf x).apply_symm_apply r
  have h := SemilinearStalk.comm_smul_eq X.presheaf x M.val
    ((SemilinearStalk.commStalkIso X.presheaf x).inv.hom r) m
  rw [hs] at h
  exact h

/-- **A flat sheaf of modules has flat stalks, in the spelling the décalage calculus uses.**
`Stacks.IdealTorsion.stalk_flat_of_isFlat` is this statement for the germ-representative module
structure on the stalk; the two structures agree by
`Stacks.IdealTorsion.Eta.moduleGrpStalk_eq_stalkModuleFunctor_isModule`, and flatness depends on
a module structure only through its value. -/
theorem flat_stalkModuleFunctor_obj_of_isFlat
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) M) :
    Module.Flat (ringStalk X x) ((stalkModuleFunctor X x).obj M) := by
  have h := Stacks.IdealTorsion.stalk_flat_of_isFlat X M hM x
  -- `h` carries the module structure at the definiens of `moduleGrpStalk`, so the equation of
  -- module structures is restated there for the rewrite to find it
  rw [show Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X M.val x =
      ((stalkModuleFunctor X x).obj M).isModule from
    moduleGrpStalk_eq_stalkModuleFunctor_isModule X x M] at h
  exact h

/-- **K-flatness of a degreewise-applied composite is K-flatness of the two factors applied in
turn.**  `(H ⋙ R).mapHomologicalComplex c` and the composite of the two `mapHomologicalComplex`es
agree by `rfl`; everything here is a variable, so that the single `isDefEq` the application
performs is that unfolding and not a descent into either factor.  This is the device
`Stacks.IdealTorsion.Reduction.quasiIso_mapHomologicalComplex_of_comp` uses for the
quasi-isomorphism analogue, and for the same reason: applied with the stalk functor in place it
runs out of heartbeats at `whnf`. -/
private theorem kFlat_mapHomologicalComplex_comp {C D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Preadditive C] [CategoryTheory.Category D] [CategoryTheory.Preadditive D]
    {S : Type u} [CommRing S] (H : C ⥤ D) [H.PreservesZeroMorphisms]
    (R : D ⥤ ModuleCat.{u} S) [R.PreservesZeroMorphisms] (K : CochainComplex C ℤ)
    (h : CochainComplex.KFlat.{u, u} ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) :
    CochainComplex.KFlat.{u, u}
      (((H ⋙ R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := h

/-- **The stalk complex of a K-flat complex of sheaves of modules is K-flat.**  This is the
stalk criterion for K-flatness (Stacks 06YB), in the form
`Stacks.SheafOfModules.KFlatPullback.stalkCriterion`, read over the `CommRingCat`-valued stalk
`𝒪_{X,x}` rather than over the `RingCat`-valued stalk of the sheaf of rings: the two differ by
restriction of scalars along the comparison `SemilinearStalk.commStalkIso`, and restriction of
scalars along a ring isomorphism preserves K-flatness
(`AlgebraicGeometry.kFlat_restrictScalars_ringEquiv`). -/
theorem kFlat_stalkComplex_of_isKFlat
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) ℤ)
    (hF : Stacks.SheafOfModules.IsKFlat X.sheaf F) :
    CochainComplex.KFlat.{u, u} (stalkComplex X x F) := by
  have h0 := Stacks.SheafOfModules.KFlatPullback.stalkCriterion.kFlatStalkwise_of_kFlat X F hF x
  have h1 := @AlgebraicGeometry.kFlat_restrictScalars_ringEquiv
    (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x))
    (ToType (ringStalk X x))
    (AlgebraicGeometry.RingedSpace.commRing_stalk_tensorRingSheaf X x) inferInstance
    (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm _ h0
  -- `Stacks.SheafOfModules.Tensor.ringSheaf` is a `def`, so the ring structure on the stalk of
  -- its sections is not reached by unfolding and Mathlib's generic instance for restriction of
  -- scalars is unreachable here; the theorem is applied with `@` and that one instance given as
  -- the proof `exact?` finds for it, which is `rfl` on each object.
  exact @kFlat_mapHomologicalComplex_comp _ _ _ _ _ _ _ _
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) x) inferInstance
    (ModuleCat.restrictScalars (SemilinearStalk.commStalkIso X.presheaf x).inv.hom :
      ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x) ⥤
          ModuleCat.{u} (ringStalk X x))
    { map_zero := fun _ ↦ congrFun rfl } F h1

/-! ### The goodness form of Tag 0F9X with the three stalk inputs discharged -/

section GoodModel

attribute [local instance 10000] HasDerivedCategory.standard

variable {X' Y' : RingedSpace.{u}} (f : X' ⟶ Y')
  (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.sheaf))
  (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y'.sheaf)) [Mono ι]
  [Stacks.SheafOfModules.IsInvertible Y'.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Y'.sheaf).property I]
  [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.sheaf))
    (pullbackIdealIncl f I ι)]
  (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.sheaf)) ℤ)
  (hF : ∀ n : ℤ, IsIdealTorsionFree Y' ι (F.X n))

include hF in
/-- **The comparison of décalages at a presentation is a quasi-isomorphism as soon as every
stalk complex of `F^•` has a good finite free model**, with no flatness hypothesis on `f`.

What is asked at a point `z` of `X` is exactly goodness read at the stalk: a generator `a` of
`I_{f(z)}` whose germ generates `(f^*I)_z`, and a bounded complex `C` of finite free
`𝒪_{Y,f(z)}`-modules representing `F^•_{f(z)}` in `D(𝒪_{Y,f(z)})` whose determinantal ideals
`I_i(C, a)` are all principal.  The remaining hypotheses of
`Stacks.IdealTorsion.Eta.quasiIso_comp_pullbackEtaMap_of_forall_stalk_good` are discharged from
global ones: the derived isomorphism is realized by a quasi-isomorphism of complexes because
`C` is K-projective (`StacksDraft.Perfect.exists_quasiIso_of_iso_Q`), K-flatness of the stalk
complexes of `F^•` and `P^•` comes from K-flatness of `F^•` and `P^•` themselves
(`Stacks.IdealTorsion.Eta.kFlat_stalkComplex_of_isKFlat`), and flatness of the terms of the
stalk complex of `F^•` comes from flatness of the terms of `F^•`
(`Stacks.IdealTorsion.Eta.flat_stalkModuleFunctor_obj_of_isFlat`). -/
theorem quasiIso_comp_pullbackEtaMap_of_forall_stalk_goodModel
    (hF' : ∀ n : ℤ,
      IsIdealTorsionFree X' (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n))
    (hreglY : IsLocallyGeneratedByRegular Y' ι)
    (hreglX : IsLocallyGeneratedByRegular X' (pullbackIdealIncl f I ι))
    (hFflat : ∀ n : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y'.sheaf) (F.X n))
    (hFkf : Stacks.SheafOfModules.IsKFlat Y'.sheaf F)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.sheaf)) ℤ)
    (hPkf : Stacks.SheafOfModules.IsKFlat Y'.sheaf P)
    (p : P ⟶ etaObj Y' I ι F hF) (hp : QuasiIso p)
    (hgood : ∀ z : X', ∃ (a : ringStalk Y' (f.hom.base z))
        (_ : GeneratesStalkIdeal Y' ι (f.hom.base z) a)
        (_ : GeneratesStalkIdeal X' (pullbackIdealIncl f I ι) z (commStalkGermMap f z a))
        (C : BoundedComplex (ringStalk Y' (f.hom.base z))),
        (∀ i : ℤ, (idealI C a i).IsPrincipal) ∧
          Nonempty (DerivedCategory.Q.obj C.toCochainComplex ≅
            DerivedCategory.Q.obj (stalkComplex Y' (f.hom.base z) F))) :
    QuasiIso (((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map p ≫
      pullbackEtaMap f I ι F hF hF') := by
  refine quasiIso_comp_pullbackEtaMap_of_forall_stalk_good f I ι F hF hF' hreglY hreglX P p hp
    fun z => ?_
  obtain ⟨a, ha, hb, C, hI, ⟨e⟩⟩ := hgood z
  obtain ⟨ψ, hψ⟩ := StacksDraft.Perfect.exists_quasiIso_of_iso_Q C
    (stalkComplex Y' (f.hom.base z) F) e
  exact ⟨a, ha, hb, C, ψ, hI, hψ,
    kFlat_stalkComplex_of_isKFlat Y' (f.hom.base z) F hFkf,
    fun i => flat_stalkModuleFunctor_obj_of_isFlat Y' (f.hom.base z) (F.X i) (hFflat i),
    kFlat_stalkComplex_of_isKFlat Y' (f.hom.base z) P hPkf⟩

end GoodModel

end Stacks.IdealTorsion.Eta

end
