module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionTwistCompat

/-!
# The canonical Frobenius trace is invariant under closed immersions

Step 2 of the proof of [Stacks, Tag 03UG], global side: for a closed immersion `i : Z ⟶ Y` of
schemes over a finite field `k` and a bounded below complex `M` on `Z_étale`, the trace of the
canonical endomorphism of `RΓ(Y_k̄, (i_* M)|_{Y_k̄})` is that of `RΓ(Z_k̄, M|_{Z_k̄})`.

## Main results

* `CategoryTheory.Functor.perfectDerivedTrace_derivedTwistEndo_baseChange_eq`: the abstract form,
  for a base change isomorphism `β : I ⋙ g ≅ g' ⋙ G` intertwining two twists.
* `Stacks.EtaleCohomology.perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

universe u r v u₁ v₁

namespace CategoryTheory.Functor

section BaseChange

variable {R : Type r} [Ring R] {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  {C C' D : Type u₁} [Category.{v₁} C] [Category.{v₁} C'] [Category.{v₁} D] [Abelian C]
  [Abelian C'] [Abelian D] [EnoughInjectives C] [EnoughInjectives C'] [EnoughInjectives D]
  (P : C ⥤ C) (F₁ : C ⥤ D) (P' : C' ⥤ C') (F₁' : C' ⥤ D) (F₂ : D ⥤ ModuleCat.{max r v} R)
  (G : C' ⥤ C) (I : A ⥤ B) (g : B ⥤ C) (g' : A ⥤ C')
  [P.Additive] [F₁.Additive] [P'.Additive] [F₁'.Additive] [F₂.Additive] [G.Additive]
  [I.Additive] [g.Additive] [g'.Additive]
  [P.PreservesInjectiveObjects] [P'.PreservesInjectiveObjects] [F₁.PreservesInjectiveObjects]
  [F₁'.PreservesInjectiveObjects] [G.PreservesInjectiveObjects]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (θ : P ⋙ F₁ ≅ F₁) (θ' : P' ⋙ F₁' ≅ F₁') (γ : G ⋙ F₁ ≅ F₁') (ρ : P' ⋙ G ⟶ G ⋙ P)
  (hθ : ∀ X, F₁.map (ρ.app X) ≫ θ.hom.app (G.obj X) ≫ γ.hom.app X =
    γ.hom.app (P'.obj X) ≫ θ'.hom.app X)
  (β : I ⋙ g ≅ g' ⋙ G) (tw : g ⟶ g ⋙ P) (tw' : g' ⟶ g' ⋙ P')
  (hβ : ∀ X, β.hom.app X ≫ G.map (tw'.app X) ≫ ρ.app (g'.obj X) =
    tw.app (I.obj X) ≫ P.map (β.hom.app X))

/-- The base change isomorphism `β : I ⋙ g ≅ g' ⋙ G`, degreewise on a bounded below complex. -/
def baseChangePlusIso (M : CochainComplex.Plus A) :
    g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M) ≅
      G.mapCochainComplexPlus.obj (g'.mapCochainComplexPlus.obj M) where
  hom := ObjectProperty.homMk ((NatTrans.mapHomologicalComplex β.hom (ComplexShape.up ℤ)).app M.obj)
  inv := ObjectProperty.homMk ((NatTrans.mapHomologicalComplex β.inv (ComplexShape.up ℤ)).app M.obj)
  hom_inv_id := by
    ext n : 2
    exact β.hom_inv_id_app _
  inv_hom_id := by
    ext n : 2
    exact β.inv_hom_id_app _

include G γ β in
/-- **Perfectness is invariant under a base change isomorphism**: `RF₂(RF₁(g(I M)))` is perfect if
and only if `RF₂(RF₁'(g' M))` is. -/
theorem isPerfect_baseChange_iff (M : CochainComplex.Plus A) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj
          (g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M)))))) ↔
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj
          (g'.mapCochainComplexPlus.obj M))))) := by
  let E := DerivedCategory.Plus.ι.mapIso (F₂.rightDerivedFunctorPlus.mapIso
    (F₁.rightDerivedFunctorPlus.mapIso (DerivedCategory.Plus.Q.mapIso
      (baseChangePlusIso G I g g' β M))))
  exact ⟨fun h => (isPerfect_rightDerived_map_iff (F₁ := F₁) (F₁' := F₁') (F₂ := F₂) (G := G)
      (γ := γ) _).1 (StacksDraft.Perfect.isPerfect_of_iso E.symm h),
    fun h => StacksDraft.Perfect.isPerfect_of_iso E ((isPerfect_rightDerived_map_iff (F₁ := F₁)
      (F₁' := F₁') (F₂ := F₂) (G := G) (γ := γ) _).2 h)⟩

include hθ hβ in
/-- **The twisted trace is invariant under a base change isomorphism.**  Let `β : I ⋙ g ≅ g' ⋙ G`
carry the twist `tw : g ⟶ g ⋙ P` to the twist `tw' : g' ⟶ g' ⋙ P'` through `ρ`, with `G` exact and
preserving injectives and `γ`, `ρ` compatible with `θ`, `θ'`.  Then for a bounded below complex `M`
the trace of the derived twisted endomorphism of `RF₂(RF₁(g(I M)))` attached to `tw` is that of
`RF₂(RF₁'(g' M))` attached to `tw'`. -/
theorem perfectDerivedTrace_derivedTwistEndo_baseChange_eq (M : CochainComplex.Plus A)
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj
          (g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M)))))))
    (hK' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj
          (g'.mapCochainComplexPlus.obj M)))))) :
    perfectDerivedTrace R ⟨_, hK⟩ (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ
        (g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M))
        (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex tw (ComplexShape.up ℤ)).app
          (I.mapCochainComplexPlus.obj M).obj)))) =
      perfectDerivedTrace R ⟨_, hK'⟩ (DerivedCategory.Plus.ι.map (derivedTwistEndo P' F₁' F₂ θ'
        (g'.mapCochainComplexPlus.obj M)
        (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex tw' (ComplexShape.up ℤ)).app
          M.obj)))) := by
  let e := baseChangePlusIso G I g g' β M
  let E := DerivedCategory.Plus.ι.mapIso (F₂.rightDerivedFunctorPlus.mapIso
    (F₁.rightDerivedFunctorPlus.mapIso (DerivedCategory.Plus.Q.mapIso e)))
  have hL : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (F₂.rightDerivedFunctorPlus.obj (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj
        (G.mapCochainComplexPlus.obj (g'.mapCochainComplexPlus.obj M)))))) :=
    StacksDraft.Perfect.isPerfect_of_iso E.symm hK
  refine (perfectDerivedTrace_congr R ⟨_, hK⟩ ⟨_, hL⟩ E _ _ ?_).trans
    (perfectDerivedTrace_derivedTwistEndo_map_eq P F₁ P' F₁' F₂ G θ θ' γ ρ hθ _ _ hL hK')
  simp only [E, Functor.mapIso_hom, ← Functor.map_comp]
  congr 1
  refine derivedTwistEndo_naturality P F₁ F₂ θ e.hom _ _ (congrArg DerivedCategory.Plus.Q.map ?_)
  ext n : 2
  exact (hβ (M.obj.X n)).symm

end BaseChange

end CategoryTheory.Functor

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {Z Y : Over (Spec (.of k))}
  (i : Z ⟶ Y) (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- For a closed immersion `i`, the direct image along `fieldBaseChangeMap i kbar` is exact and the
base change map for `i_*` is an isomorphism. -/
private theorem directImage_exact_and_isIso_baseChange {k : Type u} [Field k]
    {Z Y : Over (Spec (.of k))} (i : Z ⟶ Y) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsClosedImmersion i.left] :
    (PreservesFiniteLimits (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap i kbar)) ∧
      PreservesFiniteColimits (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap i kbar))) ∧
    IsIso (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar)
      (fieldBaseChangeProj Y kbar) (fieldBaseChangeProj Z kbar)
      (fieldBaseChangeMap_comp_fst i kbar)) := by
  have := isClosedImmersion_fieldBaseChangeMap i kbar
  exact ⟨(exactFunctor_iff _).1
    (etaleModuleDirectImage_exact_of_isIntegralHom Λ (fieldBaseChangeMap i kbar)),
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
      (fun N => isIso_etaleModuleBaseChange_fieldBaseChangeMap Λ i kbar N)⟩

/-- **Step 2 of [Stacks, Tag 03UG]: the canonical Frobenius trace is invariant under closed
immersions.**  For a closed immersion `i : Z ⟶ Y` over `k` and a bounded below complex `M` of
sheaves of `Λ`-modules on `Z_étale`, with `RΓ(Y_k̄, (i_* M)|_{Y_k̄})` and `RΓ(Z_k̄, M|_{Z_k̄})`
perfect, the traces of the canonical endomorphisms induced by the geometric Frobenius agree. -/
theorem perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage
    [IsClosedImmersion i.left] (M : CochainComplex.Plus (EtaleModules.{u, r} Λ Z.left))
    (hY : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar
            ((etaleModuleDirectImage.{u, r} Λ i.left).mapCochainComplexPlus.obj M))))))
    (hZ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Z.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Z kbar M))))) :
    CategoryTheory.FilteredDerived.perfectDerivedTrace Λ ⟨_, hY⟩ (DerivedCategory.Plus.ι.map
        (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard
          ((etaleModuleDirectImage.{u, r} Λ i.left).mapCochainComplexPlus.obj M))) =
      CategoryTheory.FilteredDerived.perfectDerivedTrace Λ ⟨_, hZ⟩ (DerivedCategory.Plus.ι.map
        (frobeniusRestrictionCohomologyEndo.{u, r} Λ Z kbar p q hcard M)) := by
  obtain ⟨⟨_, _⟩, _⟩ := directImage_exact_and_isIso_baseChange Λ i kbar
  rw [frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo,
    frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo]
  exact Functor.perfectDerivedTrace_derivedTwistEndo_baseChange_eq _ _ _ _ _ _ _ _ _
    (etaleModuleDirectImageComp.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
    (etaleModuleDirectImageComp.{u, r} Λ (geometricFrobeniusBaseChange Z kbar p q hcard)
      (pullback.snd Z.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Z kbar p q hcard).symm)
    (etaleModuleDirectImageComp.{u, r} Λ (fieldBaseChangeMap i kbar)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (fieldBaseChangeMap_comp_snd i kbar).symm)
    (directImageTwistTransfer Λ (fieldBaseChangeMap i kbar)
      (geometricFrobeniusBaseChange Z kbar p q hcard)
      (geometricFrobeniusBaseChange Y kbar p q hcard)
      (geometricFrobeniusBaseChange_comp_fieldBaseChangeMap i p q hcard kbar))
    (directImageTwistTransfer_compat Λ (fieldBaseChangeMap i kbar)
      (geometricFrobeniusBaseChange Z kbar p q hcard)
      (geometricFrobeniusBaseChange Y kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_fieldBaseChangeMap i p q hcard kbar)
      (fieldBaseChangeMap_comp_snd i kbar).symm
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm
      (geometricFrobeniusBaseChange_comp_toBase Z kbar p q hcard).symm)
    (asIso (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar)
      (fieldBaseChangeProj Y kbar) (fieldBaseChangeProj Z kbar)
      (fieldBaseChangeMap_comp_fst i kbar)))
    (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard)
    (frobeniusBaseChangeTwist.{u, r} Λ Z kbar p q hcard)
    (etaleModuleBaseChange_comp_frobeniusBaseChangeTwist Λ i p q hcard kbar) M hY hZ

omit [Fintype k] in
/-- For a closed immersion `i : Z ⟶ Y` over `k`, `RΓ(Y_k̄, (i_* M)|_{Y_k̄})` is perfect if and only
if `RΓ(Z_k̄, M|_{Z_k̄})` is. -/
theorem isPerfect_frobeniusRestriction_directImage_iff [Finite k] [IsClosedImmersion i.left]
    (M : CochainComplex.Plus (EtaleModules.{u, r} Λ Z.left)) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar
            ((etaleModuleDirectImage.{u, r} Λ i.left).mapCochainComplexPlus.obj M))))) ↔
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Z.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Z kbar M)))) := by
  have := Fintype.ofFinite k
  obtain ⟨⟨_, _⟩, _⟩ := directImage_exact_and_isIso_baseChange Λ i kbar
  exact Functor.isPerfect_baseChange_iff (F₁ := etaleModuleDirectImage.{u, r} Λ
      (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (F₁' := etaleModuleDirectImage.{u, r} Λ (pullback.snd Z.hom (specAlgebraMap k kbar)))
    (F₂ := etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (G := etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap i kbar))
    (I := etaleModuleDirectImage.{u, r} Λ i.left)
    (g := etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar))
    (g' := etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Z kbar))
    (γ := etaleModuleDirectImageComp.{u, r} Λ (fieldBaseChangeMap i kbar)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (fieldBaseChangeMap_comp_snd i kbar).symm)
    (β := asIso (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar)
      (fieldBaseChangeProj Y kbar) (fieldBaseChangeProj Z kbar)
      (fieldBaseChangeMap_comp_fst i kbar))) M

end Stacks.EtaleCohomology

end
