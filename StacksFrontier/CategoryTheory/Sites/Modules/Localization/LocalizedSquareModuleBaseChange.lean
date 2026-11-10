module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOfToposHomExactPullback
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.ElementRestrictionAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizationSquareMate
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RelocalizedMorphismComparison
public import StacksFrontier.CategoryTheory.Adjunction.MateOverFaithful
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateCompTransfer
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Adjunction.MateTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardComparison
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesCompare

/-!
# The module base change map of the localization square of Stacks 04IF

Let `(f, f♯) : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi, let `G` be a sheaf of
sets on `D` and put `F = f⁻¹G`. Stacks 04IF forms the square
```
  (Sh(C)/F, O_F) --j_F--> (Sh(C), O)
        | f'                   | f
        v                      v
  (Sh(D)/G, O'_G) --j_G--> (Sh(D), O')
```
of ringed topoi, commuting up to the 2-isomorphism `s` of
`AlgebraicGeometry.RingedToposHom.localizedRingedToposSquare`, and asserts `f'_* j_F^* = j_G^* f_*`
on sheaves of modules. This file proves that the comparison which a 2-commutative square
canonically carries, the **base change map** `j_G^* f_* ⟶ f'_* j_F^*` of sheaves of modules
(`AlgebraicGeometry.RingedToposHom.TwoIso.moduleBaseChange`, the mate of the identification
`(f')^* j_G^* ≅ j_F^* f^*` of pullbacks), is an isomorphism.

## Main results

All names below are in the namespace `AlgebraicGeometry`.

* `RingedToposHom.isIso_moduleBaseChange_localizedRingedToposSquare`: the base change map of
  sheaves of modules of the square of Stacks 04IF is an isomorphism.
* `RingedToposHom.TwoIso.isIso_moduleBaseChange_app_of_unit`: for an arbitrary 2-commutative
  square, the base change map of sheaves of modules is an isomorphism as soon as the horizontal
  pullbacks lie over the inverse images of sheaves of sets compatibly with the units and the base
  change map of sheaves of sets is an isomorphism.
* `RingedToposHom.TwoIso.moduleSheafFunctor_map_conjugateEquiv_squarePullbackIso_hom_app`: the
  identification of pullbacks around a 2-commutative square is conjugate to the inverse of the
  2-isomorphism, on underlying sheaves of sets.
* `RingedTopos.exists_pullbackModules_iso_unit_localization`: the adjunction `j^* ⊣ j_*` of a
  localization morphism lies over `j⁻¹ ⊣ j_*`.
* `RingedToposHom.mateEquiv_localizationCompPushforwardIso_inv`: on sheaves of sets, the inverse
  of Stacks 04IF's comparison of direct images is the mate of the inverse of the 2-isomorphism of
  the square.

## References

* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.Sheaves.RingedToposModules

universe w w' w'' v u v' u' v'' u''

section Conjugate

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
    {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (φ : RingedToposHom X Y) (ψ : RingedToposHom Y Z) (χ : RingedToposHom X Z)
  (τ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
  (hτ : fSharpSetComp φ ψ ≫
      τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
    fSharpSet χ)

/-- The comparison `χ^* ≅ ψ^* ⋙ φ^*` of pullbacks is conjugate to the comparison
`φ_* ⋙ ψ_* ≅ χ_*` of direct images it is built from. -/
theorem conjugateEquiv_pullbackModulesCompIso_hom :
    conjugateEquiv ((pullbackAdjPushforwardModules ψ).comp (pullbackAdjPushforwardModules φ))
        (pullbackAdjPushforwardModules χ) (pullbackModulesCompIso φ ψ χ τ hτ).hom =
      (pushforwardModulesCompIso φ ψ χ τ hτ).hom := by
  have h := conjugateEquiv_comp
    ((pullbackAdjPushforwardModules ψ).comp (pullbackAdjPushforwardModules φ))
    ((pullbackAdjPushforwardModules χ).ofNatIsoRight (pushforwardModulesCompIso φ ψ χ τ hτ).symm)
    (pullbackAdjPushforwardModules χ) (pullbackModulesCompIso φ ψ χ τ hτ).hom (𝟙 _)
  rw [Category.id_comp, Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight_id] at h
  rw [← h]
  have h1 : conjugateEquiv
      ((pullbackAdjPushforwardModules ψ).comp (pullbackAdjPushforwardModules φ))
      ((pullbackAdjPushforwardModules χ).ofNatIsoRight (pushforwardModulesCompIso φ ψ χ τ hτ).symm)
      (pullbackModulesCompIso φ ψ χ τ hτ).hom = 𝟙 _ := by
    simp [pullbackModulesCompIso, Adjunction.leftAdjointUniq, conjugateIsoEquiv]
  rw [h1, Category.id_comp, Iso.symm_inv]

/-- The inverse comparison of pullbacks is conjugate to the inverse comparison of direct
images. -/
theorem conjugateEquiv_pullbackModulesCompIso_inv :
    conjugateEquiv (pullbackAdjPushforwardModules χ)
        ((pullbackAdjPushforwardModules ψ).comp (pullbackAdjPushforwardModules φ))
        (pullbackModulesCompIso φ ψ χ τ hτ).inv =
      (pushforwardModulesCompIso φ ψ χ τ hτ).inv := by
  have h := conjugateEquiv_comp (pullbackAdjPushforwardModules χ)
    ((pullbackAdjPushforwardModules χ).ofNatIsoRight (pushforwardModulesCompIso φ ψ χ τ hτ).symm)
    ((pullbackAdjPushforwardModules ψ).comp (pullbackAdjPushforwardModules φ))
    (𝟙 _) (pullbackModulesCompIso φ ψ χ τ hτ).inv
  rw [Category.comp_id, Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight_hom] at h
  rw [← h]
  have h1 : conjugateEquiv
      ((pullbackAdjPushforwardModules χ).ofNatIsoRight (pushforwardModulesCompIso φ ψ χ τ hτ).symm)
      ((pullbackAdjPushforwardModules ψ).comp (pullbackAdjPushforwardModules φ))
      (pullbackModulesCompIso φ ψ χ τ hτ).inv = 𝟙 _ := by
    simp [pullbackModulesCompIso, Adjunction.leftAdjointUniq, conjugateIsoEquiv]
  rw [h1, Category.comp_id, Iso.symm_hom]

end Conjugate

section Underlying

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]

/-- The underlying sheaf of sets of the direct image of a sheaf of modules is the direct image of
the underlying sheaf of sets, naturally in the module. -/
noncomputable def pushforwardModulesUnderlyingIso (φ : RingedToposHom X Y) :
    pushforwardModules φ ⋙ Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≅
      Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        φ.toToposHom.pushforward :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun α ↦
    (Category.comp_id _).trans ((moduleSheafFunctor_map_pushforwardModules_map φ α).trans
      (Category.id_comp _).symm))

end Underlying

end Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.RingedToposHom.TwoIso

universe u

variable {X' X Y' Y : RingedTopos.{u, u, u}}
  [X'.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y'.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  {f : RingedToposHom X Y} {g : RingedToposHom Y' Y} {f' : RingedToposHom X' Y'}
  {g' : RingedToposHom X' X} (s : TwoIso (g.comp f') (f.comp g'))

omit [Y'.J.HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- The comparison of direct images built from the 2-isomorphism `s` is `s⁻¹` on underlying
sheaves of sets. -/
theorem moduleSheafFunctor_map_pushforwardModulesCompIso_squarePushforwardIso_hom_app
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso g'.toModulesHom
          f.toModulesHom (g.comp f').toModulesHom (squarePushforwardIso s)
          (fSharpSetComp_squarePushforwardIso s)).hom.app N) =
      s.e.inv.app
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)).obj N) := by
  rw [Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_pushforwardModulesCompIso_hom_app,
    squarePushforwardIso]
  exact Category.id_comp (s.e.inv.app _)

/-- The comparison of direct images for the genuine composite `g ∘ f'` is the identity on
underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_pushforwardModulesCompIso_toModulesHomPushforwardIso_inv_app
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso f'.toModulesHom
          g.toModulesHom (g.comp f').toModulesHom (toModulesHomPushforwardIso f' g)
          (fSharpSetComp_toModulesHomPushforwardIso f' g)).inv.app N) =
      𝟙 (g.toToposHom.pushforward.obj (f'.toToposHom.pushforward.obj
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)).obj N))) :=
  Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_pushforwardModulesCompInv _ _ _ _ _
    (fSharpSetComp_toModulesHomPushforwardIso f' g)

/-- **The pullback square of a 2-commutative square of ringed topoi is conjugate to its
pushforward square.** The conjugate of `m : (f')^* g^* ≅ (g')^* f^*`, for the composite
adjunctions `f^* (g')^* ⊣ g'_* f_*` and `g^* (f')^* ⊣ f'_* g_*` of the four-field readings, is
the inverse of the 2-isomorphism `s` on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_conjugateEquiv_squarePullbackIso_hom_app
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((conjugateEquiv
          ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom).comp
            (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g'.toModulesHom))
          ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g.toModulesHom).comp
            (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f'.toModulesHom))
          (squarePullbackIso s).hom).app N) =
      s.e.inv.app
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)).obj N) := by
  have hc := conjugateEquiv_comp
    ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom).comp
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g'.toModulesHom))
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules (g.comp f').toModulesHom)
    ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g.toModulesHom).comp
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f'.toModulesHom))
    (squareCompIsoRight s).hom (squareCompIsoLeft (g := g) (f' := f')).inv
  have hm : (squarePullbackIso s).hom =
      (squareCompIsoLeft (g := g) (f' := f')).inv ≫ (squareCompIsoRight s).hom := rfl
  have hK1 := Stacks.Sheaves.RingedToposModules.conjugateEquiv_pullbackModulesCompIso_inv
    f'.toModulesHom g.toModulesHom (g.comp f').toModulesHom (toModulesHomPushforwardIso f' g)
    (fSharpSetComp_toModulesHomPushforwardIso f' g)
  have hK2 := Stacks.Sheaves.RingedToposModules.conjugateEquiv_pullbackModulesCompIso_hom
    g'.toModulesHom f.toModulesHom (g.comp f').toModulesHom (squarePushforwardIso s)
    (fSharpSetComp_squarePushforwardIso s)
  rw [hm, ← hc, hK1, hK2, NatTrans.comp_app]
  exact ((CategoryTheory.Functor.map_comp _ _ _).trans (congrArg₂ (· ≫ ·)
    (moduleSheafFunctor_map_pushforwardModulesCompIso_squarePushforwardIso_hom_app s N)
    (moduleSheafFunctor_map_pushforwardModulesCompIso_toModulesHomPushforwardIso_inv_app
      (g := g) (f' := f') N))).trans
    (Category.comp_id
      (s.e.inv.app
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)).obj N)))

/-- The base change map of sheaves of modules of a 2-commutative square, computed with the
adjunctions of the four-field readings: it differs from the one computed with the adjunctions of
the two-field morphisms by the identifications `toModulesPushforwardIso` of the direct images. -/
theorem moduleBaseChange_app_eq
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (moduleBaseChange s).app M =
      g.toModulesHom.pullbackModules.map (f.toModulesPushforwardIso.inv.app M) ≫
        (mateEquiv (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom)
          (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f'.toModulesHom)
          (squarePullbackIso s).hom).app M ≫
        f'.toModulesPushforwardIso.hom.app (g'.toModulesHom.pullbackModules.obj M) := by
  have h := mateEquiv_ofNatIsoRight
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom)
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f'.toModulesHom)
    f.toModulesPushforwardIso f'.toModulesPushforwardIso (squarePullbackIso s).hom
    (TwoSquare.mk _ _ _ _ (Functor.whiskerRight f.toModulesPushforwardIso.inv
        g.toModulesHom.pullbackModules ≫
      (mateEquiv (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom)
          (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f'.toModulesHom)
          (squarePullbackIso s).hom) ≫
      Functor.whiskerLeft g'.toModulesHom.pullbackModules f'.toModulesPushforwardIso.hom))
    (fun _ ↦ rfl)
  unfold moduleBaseChange
  exact NatTrans.congr_app h.symm M

/-- The base change map of sheaves of modules of a 2-commutative square is invertible at `M` as
soon as the base change map computed with the adjunctions of the four-field readings is. -/
theorem isIso_moduleBaseChange_app_of_isIso
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (h : IsIso ((mateEquiv
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom)
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f'.toModulesHom)
      (squarePullbackIso s).hom).app M)) :
    IsIso ((moduleBaseChange s).app M) := by
  rw [moduleBaseChange_app_eq]
  infer_instance

/-- The base change map of sheaves of modules of a 2-commutative square, followed by the mates
correspondence for the two horizontal adjunctions, is the inverse of `s` on underlying sheaves of
sets. -/
theorem moduleSheafFunctor_map_mateEquiv_mateEquiv_squarePullbackIso_hom_app
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((mateEquiv
          (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g'.toModulesHom)
          (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g.toModulesHom)
          (mateEquiv
            (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom)
            (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f'.toModulesHom)
            (squarePullbackIso s).hom)).app N) =
      s.e.inv.app
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)).obj N) :=
  (congrArg (fun t ↦ (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map (NatTrans.app t N))
    (iterated_mateEquiv_conjugateEquiv _ _ _ _ _)).trans
    (moduleSheafFunctor_map_conjugateEquiv_squarePullbackIso_hom_app s N)

/-- `moduleSheafFunctor_map_mateEquiv_mateEquiv_squarePullbackIso_hom_app`, with the
identifications of the underlying sheaves of sets of the direct images written out. -/
theorem moduleSheafFunctor_map_mateEquiv_mateEquiv_squarePullbackIso_hom_app'
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((mateEquiv
          (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g'.toModulesHom)
          (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g.toModulesHom)
          (mateEquiv
            (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom)
            (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f'.toModulesHom)
            (squarePullbackIso s).hom)).app N) ≫
      (Stacks.Sheaves.RingedToposModules.pushforwardModulesUnderlyingIso g.toModulesHom).hom.app
          ((Stacks.Sheaves.RingedToposModules.pushforwardModules f'.toModulesHom).obj N) ≫
        g.toModulesHom.toToposHom.pushforward.map
          ((Stacks.Sheaves.RingedToposModules.pushforwardModulesUnderlyingIso
            f'.toModulesHom).hom.app N) =
      (Stacks.Sheaves.RingedToposModules.pushforwardModulesUnderlyingIso f.toModulesHom).hom.app
          ((Stacks.Sheaves.RingedToposModules.pushforwardModules g'.toModulesHom).obj N) ≫
        f.toModulesHom.toToposHom.pushforward.map
          ((Stacks.Sheaves.RingedToposModules.pushforwardModulesUnderlyingIso
            g'.toModulesHom).hom.app N) ≫
        (TwoSquare.mk g'.toModulesHom.toToposHom.pushforward f'.toModulesHom.toToposHom.pushforward
          f.toModulesHom.toToposHom.pushforward g.toModulesHom.toToposHom.pushforward
          s.e.inv).app
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)).obj N) := by
  have hE := moduleSheafFunctor_map_mateEquiv_mateEquiv_squarePullbackIso_hom_app s N
  have hL :
      (Stacks.Sheaves.RingedToposModules.pushforwardModulesUnderlyingIso g.toModulesHom).hom.app
          ((Stacks.Sheaves.RingedToposModules.pushforwardModules f'.toModulesHom).obj N) ≫
        g.toModulesHom.toToposHom.pushforward.map
          ((Stacks.Sheaves.RingedToposModules.pushforwardModulesUnderlyingIso
            f'.toModulesHom).hom.app N) = 𝟙 _ :=
    (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have hR :
      (Stacks.Sheaves.RingedToposModules.pushforwardModulesUnderlyingIso f.toModulesHom).hom.app
          ((Stacks.Sheaves.RingedToposModules.pushforwardModules g'.toModulesHom).obj N) ≫
        f.toModulesHom.toToposHom.pushforward.map
          ((Stacks.Sheaves.RingedToposModules.pushforwardModulesUnderlyingIso
            g'.toModulesHom).hom.app N) = 𝟙 _ :=
    (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  exact ((congrArg (_ ≫ ·) hL).trans ((Category.comp_id _).trans hE)).trans
    ((Category.id_comp _).symm.trans ((reassoc_of% hR) _).symm)

/-- **A criterion for the module base change map of a 2-commutative square to be invertible.**
Suppose the pullbacks of sheaves of modules along `g` and `g'` lie over the inverse images of
sheaves of sets compatibly with the units, and that the base change map of sheaves of sets of the
square, the mate of `s⁻¹`, is invertible. Then the base change map `g^* f_* ⟶ f'_* (g')^*` of
sheaves of modules is invertible. -/
theorem isIso_moduleBaseChange_app_of_unit
    (hg : ∃ ρ : g.toModulesHom.pullbackModules ⋙
        Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O) ≅
      Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⋙
        g.toModulesHom.toToposHom.inverseImage,
      ∀ N, (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
            g.toModulesHom).unit.app N) ≫
          g.toModulesHom.toToposHom.pushforward.map (ρ.hom.app N) =
        g.toModulesHom.toToposHom.adj.unit.app
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj N))
    (hg' : ∃ ρ' : g'.toModulesHom.pullbackModules ⋙
        Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X'.O) ≅
      Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        g'.toModulesHom.toToposHom.inverseImage,
      ∀ N, (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
          ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
            g'.toModulesHom).unit.app N) ≫
          g'.toModulesHom.toToposHom.pushforward.map (ρ'.hom.app N) =
        g'.toModulesHom.toToposHom.adj.unit.app
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj N))
    (hset : ∀ S, IsIso (((mateEquiv g'.toToposHom.adj g.toToposHom.adj).symm
      (TwoSquare.mk g'.toToposHom.pushforward f'.toToposHom.pushforward f.toToposHom.pushforward
        g.toToposHom.pushforward s.e.inv)).app S))
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    IsIso ((moduleBaseChange s).app M) := by
  obtain ⟨ρ, hρ⟩ := hg
  obtain ⟨ρ', hρ'⟩ := hg'
  refine isIso_moduleBaseChange_app_of_isIso s M ?_
  have key := Adjunction.map_mateEquiv_symm_natTrans_app
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g.toModulesHom)
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g'.toModulesHom)
    g.toModulesHom.toToposHom.adj g'.toModulesHom.toToposHom.adj
    (mateEquiv (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g'.toModulesHom)
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g.toModulesHom)
      (mateEquiv (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom)
        (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f'.toModulesHom)
        (squarePullbackIso s).hom))
    (TwoSquare.mk g'.toModulesHom.toToposHom.pushforward f'.toModulesHom.toToposHom.pushforward
        f.toModulesHom.toToposHom.pushforward g.toModulesHom.toToposHom.pushforward s.e.inv)
    (Stacks.Sheaves.RingedToposModules.pushforwardModulesUnderlyingIso f.toModulesHom)
    (Stacks.Sheaves.RingedToposModules.pushforwardModulesUnderlyingIso f'.toModulesHom)
    (Stacks.Sheaves.RingedToposModules.pushforwardModulesUnderlyingIso g.toModulesHom)
    (Stacks.Sheaves.RingedToposModules.pushforwardModulesUnderlyingIso g'.toModulesHom) ρ ρ'
    (fun N ↦ (congrArg (_ ≫ ·) (Category.id_comp _)).trans (hρ N))
    (fun N ↦ (congrArg (_ ≫ ·) (Category.id_comp _)).trans (hρ' N))
    (moduleSheafFunctor_map_mateEquiv_mateEquiv_squarePullbackIso_hom_app' s) M
  rw [Equiv.symm_apply_apply] at key
  have hiso : IsIso ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)).map
      ((mateEquiv (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom)
        (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f'.toModulesHom)
        (squarePullbackIso s).hom).app M)) := by
    rw [key]
    have : IsIso (((mateEquiv g'.toModulesHom.toToposHom.adj g.toModulesHom.toToposHom.adj).symm
        (TwoSquare.mk g'.toModulesHom.toToposHom.pushforward f'.toModulesHom.toToposHom.pushforward
          f.toModulesHom.toToposHom.pushforward g.toModulesHom.toToposHom.pushforward
          s.e.inv)).app
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M)) :=
      hset ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M)
    infer_instance
  exact isIso_of_reflects_iso _
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O))

end AlgebraicGeometry.RingedToposHom.TwoIso

namespace AlgebraicGeometry.RingedToposHom

universe u

variable {X Y : RingedTopos.{u, u, u}} (f : RingedToposHom X Y) (G : Y.Topos)

/-- **Stacks 04IF on sheaves of sets, as a mate.** The inverse of the comparison
`j_F⁻¹ ⋙ f'_* ≅ f_* ⋙ j_G⁻¹` of direct images of sheaves of sets has, for the adjunctions of the
two localization morphisms, the inverse of the 2-isomorphism of the localization square as its
mate. -/
theorem mateEquiv_localizationCompPushforwardIso_inv :
    mateEquiv (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.adj
        (Y.localizationMorphism G).toToposHom.adj
        (TwoSquare.mk f.toToposHom.pushforward
          (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage
          (Y.localizationMorphism G).toToposHom.inverseImage
          (f.localized G).toToposHom.pushforward (f.localizationCompPushforwardIso G).inv) =
      TwoSquare.mk (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.pushforward
        (f.localized G).toToposHom.pushforward f.toToposHom.pushforward
        (Y.localizationMorphism G).toToposHom.pushforward
        (f.localizedRingedToposSquare G).e.inv := by
  have h := iterated_mateEquiv_conjugateEquiv f.toToposHom.adj (localizedToposMorphism f G).adj
    (Y.localizationMorphism G).toToposHom.adj
    (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.adj
    (TwoSquare.mk (Y.localizationMorphism G).toToposHom.inverseImage f.toToposHom.inverseImage
          (localizedToposMorphism f G).inverseImage
          (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage
          (f.inverseImageCompLocalizationIso G).inv)
  rwa [f.mateEquiv_inverseImageCompLocalizationIso_inv G] at h

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.RingedTopos

universe u

variable (Z : RingedTopos.{u, u, u}) (H : Z.Topos)

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
  Stacks.Sheaves.RingedToposModules

/-- The retyping of restriction of scalars along the structure map of the localization is the
identity on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_eqToIso_restrictScalars_fSharp_localization_eq_inv_app
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (Z.localizedRingedTopos H).O)) :
    (Sheaf.moduleSheafFunctor (inverseImageRingSheaf (Z.localizationMorphism H).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))).map
      ((eqToIso (restrictScalars_fSharp_localization_eq Z H)).inv.app M) = 𝟙 _ := by
  have h1 := congrArg (Sheaf.moduleSheafFunctor (inverseImageRingSheaf
      (Z.localizationMorphism H).toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))).map
    (eqToHom_app (restrictScalars_fSharp_localization_eq Z H).symm M)
  exact (h1.trans (eqToHom_map _ _)).trans (eqToHom_refl _ _)

/-- Stacks 04IE's identification of the inverse image with restriction, followed by the
retyping of restriction of scalars, is the identity on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_restrictionModuleIso_hom_app_comp_eqToIso_inv_app
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    (Sheaf.moduleSheafFunctor (inverseImageRingSheaf (Z.localizationMorphism H).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))).map
      ((restrictionModuleIso (elementTopology Z H) Z.J (elementProjection Z H)
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).hom.app N ≫
        (eqToIso (restrictScalars_fSharp_localization_eq Z H)).inv.app
          ((restrictionModules (elementTopology Z H) Z.J (elementProjection Z H)
            (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj N)) = 𝟙 _ :=
  (CategoryTheory.Functor.map_comp _ _ _).trans
    ((congrArg₂ (· ≫ ·)
      (moduleSheafFunctor_map_restrictionModuleIso_hom_app (elementTopology Z H) Z.J
        (elementProjection Z H) (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) N)
      (moduleSheafFunctor_map_eqToIso_restrictScalars_fSharp_localization_eq_inv_app Z H _)).trans
      (Category.id_comp _))

/-- The unit of the inverse-image adjunction followed by the direct image of the identification
of the inverse image with restriction is the unit of `j⁻¹ ⊣ j_*` on underlying sheaves. -/
theorem moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app_comp_restriction
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      ((inverseImageAdjDirectImageModules (localizationMorphism Z H).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).unit.app N ≫
        (directImageModules (localizationMorphism Z H).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
          ((restrictionModuleIso (elementTopology Z H) Z.J (elementProjection Z H)
            (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).hom.app N ≫
            (eqToIso (restrictScalars_fSharp_localization_eq Z H)).inv.app _)) =
      (Z.localizationMorphism H).toToposHom.adj.unit.app
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj N) :=
  (moduleSheafFunctor_map_unit_app_comp_directImageModules_map
      (localizationMorphism Z H).toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) N
      ((restrictionModuleIso (elementTopology Z H) Z.J (elementProjection Z H)
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).hom.app N ≫
        (eqToIso (restrictScalars_fSharp_localization_eq Z H)).inv.app _)).trans
    ((congrArg (fun x ↦ (Z.localizationMorphism H).toToposHom.adj.unit.app
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj N) ≫
          (Z.localizationMorphism H).toToposHom.pushforward.map x)
        (moduleSheafFunctor_map_restrictionModuleIso_hom_app_comp_eqToIso_inv_app Z H N)).trans
      ((congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)))

/-- **The unit of `j^* ⊣ j_*` for the localization, read on underlying sheaves of sets.** The
unit of the adjunction of Stacks 03D7, followed by `j_*` of Stacks 04IE's identification of `j^*`
with restriction, is the unit of `j⁻¹ ⊣ j_*` on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_unit_app_localizationModulePullbackIso
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          (localizationMorphism Z H).toRingedToposModulesHom).unit.app N ≫
        (Stacks.Sheaves.RingedToposModules.pushforwardModules
          (localizationMorphism Z H).toRingedToposModulesHom).map
          ((localizationModulePullbackIso Z H).hom.app N)) =
      (Z.localizationMorphism H).toToposHom.adj.unit.app
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj N) :=
  (congrArg (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      (pullbackAdjPushforwardModules_unit_app_localizationModulePullbackIso Z H N)).trans
    (moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app_comp_restriction Z H N)

/-- Restriction of sheaves of modules to the site of elements is the inverse image along the
localization morphism on underlying sheaves of sets, naturally in the module. -/
noncomputable def elementRestrictionModuleSheafIso :
    SheafOfModules.pushforward (F := elementProjection Z H) (J := elementTopology Z H) (K := Z.J)
        (elementModuleRingHom Z H) ⋙
      Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (Z.localizedRingedTopos H).O) ≅
      Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) ⋙
        (Z.localizationMorphism H).toToposHom.inverseImage :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun φ ↦
    (Category.comp_id _).trans ((moduleSheafFunctor_map_elementRestriction_map Z H _ φ).trans
      (Category.id_comp _).symm))

/-- **The pullback of modules along a localization morphism lies over the inverse image of
sheaves of sets, compatibly with the units.** For any four-field reading `φ` of the
localization morphism, there is an identification of the underlying sheaf of sets of `φ^* N`
with `φ⁻¹` of the underlying sheaf of sets of `N` under which the unit of `φ^* ⊣ φ_*` is the
unit of `φ⁻¹ ⊣ φ_*`. -/
theorem exists_pullbackModules_iso_unit_localization
    (φ : Stacks.Sheaves.RingedToposModules.RingedToposHom (Z.localizedRingedTopos H) Z)
    (hφ : φ = (localizationMorphism Z H).toRingedToposModulesHom) :
    ∃ ρ : φ.pullbackModules ⋙
        Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf (Z.localizedRingedTopos H).O) ≅
      Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) ⋙
        φ.toToposHom.inverseImage,
      ∀ N, (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
          ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules φ).unit.app N) ≫
          φ.toToposHom.pushforward.map (ρ.hom.app N) =
        φ.toToposHom.adj.unit.app
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj N) := by
  subst hφ
  refine ⟨Functor.isoWhiskerRight (localizationModulePullbackIso Z H) _ ≪≫
    elementRestrictionModuleSheafIso Z H, fun N ↦ ?_⟩
  refine Eq.trans ?_ (moduleSheafFunctor_map_unit_app_localizationModulePullbackIso Z H N)
  rw [CategoryTheory.Functor.map_comp]
  congr 1

end AlgebraicGeometry.RingedTopos

namespace AlgebraicGeometry.RingedToposHom

universe u

variable {X Y : RingedTopos.{u, u, u}} (f : RingedToposHom X Y) (G : Y.Topos)

/-- The base change map of sheaves of sets of the localization square of Stacks 04IF, the mate
of the inverse of its 2-isomorphism, is the inverse of Stacks 04IF's comparison of direct images,
hence invertible. -/
theorem isIso_mateEquiv_symm_localizedRingedToposSquare_app
    (S : X.Topos) :
    IsIso (((mateEquiv (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.adj
        (Y.localizationMorphism G).toToposHom.adj).symm
      (TwoSquare.mk
        (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.pushforward
        (f.localized G).toToposHom.pushforward f.toToposHom.pushforward
        (Y.localizationMorphism G).toToposHom.pushforward
        (f.localizedRingedToposSquare G).e.inv)).app S) := by
  rw [← mateEquiv_localizationCompPushforwardIso_inv, Equiv.symm_apply_apply]
  exact inferInstanceAs (IsIso ((f.localizationCompPushforwardIso G).inv.app S))

/-- **The module base change map of the localization square of Stacks 04IF is an isomorphism.**
For a morphism of ringed topoi `f : (Sh(C), O) ⟶ (Sh(D), O')`, a sheaf of sets `G` on `D` and
`F = f⁻¹G`, the base change map `j_G^* f_* ⟶ f'_* j_F^*` of sheaves of modules of the square of
Stacks 04IF, formed by `f`, its localization `f'` and the two localization morphisms, is an
isomorphism at every sheaf of `O`-modules. -/
theorem isIso_moduleBaseChange_localizedRingedToposSquare
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    IsIso ((TwoIso.moduleBaseChange (f.localizedRingedToposSquare G)).app M) :=
  TwoIso.isIso_moduleBaseChange_app_of_unit (f.localizedRingedToposSquare G)
    (RingedTopos.exists_pullbackModules_iso_unit_localization Y G _
      (toModulesHom_eq_toRingedToposModulesHom (Y.localizationMorphism G)))
    (RingedTopos.exists_pullbackModules_iso_unit_localization X
      (f.toToposHom.inverseImage.obj G) _
      (toModulesHom_eq_toRingedToposModulesHom
        (X.localizationMorphism (f.toToposHom.inverseImage.obj G))))
    (isIso_mateEquiv_symm_localizedRingedToposSquare_app f G) M

end AlgebraicGeometry.RingedToposHom
