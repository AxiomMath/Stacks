module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSmoothModelGalois

/-!
# The Galois action on `H^i_c(X_k̄, F)` is the pullback action on the smooth model

Let `X` be a geometrically connected smooth curve over a field `k`, `j : X ⟶ X̄` a
compactification over `k`, `k̄` an algebraically closed extension of `k` and
`C = Stacks.EtaleCohomology.geometricSmoothModel f j k̄` the smooth projective model of `X_k̄`,
with `f̄ : C ⟶ X̄_k̄` and `q = f̄ ≫ pr : C ⟶ X̄`.  For a sheaf `F` of `Λ`-modules on `X`,
`H^i_c(X_k̄, F) = H^i(X̄_k̄, (j_! F)|_{X̄_k̄})` (Remark 03UI (2)) carries the action of
`σ ∈ Aut_k(k̄)` induced by `s_σ = id_{X̄} × Spec σ`
(`Stacks.EtaleCohomology.galoisCompactSupportGroupAction`), and
`H^i(C, j_{C!}(F|_{X_k̄}))` carries the pullback action of `s̃_σ = id_{C'} × Spec σ`
(`Stacks.EtaleCohomology.geometricSmoothModelGaloisAction`).  This file proves that the
identification `H^i_c(X_k̄, F) ≅ H^i(C, j_{C!}(F|_{X_k̄}))`
(`Stacks.EtaleCohomology.galoisCompactSupportSmoothModelIso`) carries the first action to the
second, and that the second is natural in `F`.

The proof has two steps.

1. On `X̄_k̄`: the action defined through the derived category, `RΓ` of the twist
   `C|_{X̄_k̄} ⟶ R(s_σ)_*(C|_{X̄_k̄})`, is, on a complex concentrated in degree zero, the pullback
   action `H^i(X̄_k̄, α)` followed by `H^i(X̄_k̄, (s_σ)_* -) ≅ H^i(X̄_k̄, -)` of
   `Stacks.EtaleCohomology.integralSelfMapCohomologyEndo`, for `α` the self-map twist of
   `(j_! F)|_{X̄_k̄}` (`Stacks.EtaleCohomology.galoisCompactSupportGroupAction_comp_singleIso`).
   The input is that the derived-functor unit of the exact `(s_σ)_*` at a complex in degree zero
   is the comparison `(s_σ)_*(M)[0] ≅ R(s_σ)_*(M[0])`
   (`Stacks.EtaleCohomology.mapCochainComplexPlusDerivedUnit_app_singlePlus`).
2. From `X̄_k̄` to `C`: the restriction map `(j_! F)|_{X̄_k̄} ⟶ f̄_* q^{-1}(j_! F)` intertwines the
   two self-map twists (`Stacks.EtaleCohomology.selfMapTwist_comp_map_selfMapRestriction`), so
   the naturality of the pullback action and its compatibility with the direct image along the
   finite `f̄` (`Stacks.EtaleCohomology.integralSelfMapCohomologyEndo_directImage`) carry the
   action of `s_σ` to that of `s̃_σ`.

## Main results

* `Stacks.EtaleCohomology.galoisCompactSupportGroupAction_comp_singleIso`.
* `Stacks.EtaleCohomology.galoisCompactSupportSmoothModelIso_hom_galoisAction`.
* `Stacks.EtaleCohomology.geometricSmoothModelGaloisAction_naturality`.

## Implementation notes

The rearrangements are chains of `Eq.trans`, `congrArg` and `Category.assoc` rather than
rewrites: the objects carry two spellings each (`fieldBaseChangeProj (Over.mk j.toBase) k̄`
versus `pullback.fst j.toBase _`, `(P ⋙ S).obj` versus `S.obj (P.obj _)`), and a `rw` across
them builds a motive that is not type-correct at the transparency the rewriters use.

## References

* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI), item (2).
* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe w u

namespace Stacks.EtaleCohomology

/-! ### The derived-functor unit of an exact functor on a complex in degree zero -/

section Generic

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- **The derived-functor unit of an exact functor at a complex concentrated in degree zero**
is the identification `S(M[0]) ≅ (S M)[0]` followed by the comparison
`(S M)[0] ≅ RS(M[0])`. -/
theorem mapCochainComplexPlusDerivedUnit_app_singlePlus [EnoughInjectives A] (S : A ⥤ B)
    [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S] (M : A) :
    (Functor.mapCochainComplexPlusDerivedUnit S).app
        ((Stacks.DerivedIndexing.singlePlusFunctor A 0).obj M) =
      DerivedCategory.Plus.Q.map (mapCochainComplexPlusSinglePlusIso S M).hom ≫
        (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso S 0).hom.app M := by
  have h1 : DerivedCategory.Plus.Q.map ((Stacks.DerivedIndexing.mapSinglePlus S 0).app M) ≫
      (Functor.mapCochainComplexPlusDerivedUnit S).app
        ((Stacks.DerivedIndexing.singlePlusFunctor A 0).obj M) =
      (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso S 0).hom.app M := by
    have h := Stacks.DerivedIndexing.singleDerivedUnit_zero S M
    rw [Stacks.DerivedIndexing.singleDerivedUnit] at h
    exact h.trans (congrArg (fun t => NatTrans.app t M)
      (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso_hom S)).symm
  have h0 : (mapCochainComplexPlusSinglePlusIso S M).hom ≫
      (Stacks.DerivedIndexing.mapSinglePlus S 0).app M = 𝟙 _ :=
    ObjectProperty.hom_ext _
      ((HomologicalComplex.singleMapHomologicalComplex S (ComplexShape.up ℤ) 0).hom_inv_id_app M)
  let Q := DerivedCategory.Plus.Q (C := B)
  refine (Category.id_comp _).symm.trans ?_
  refine (congrArg (· ≫ _) ((congrArg Q.map h0).trans (Q.map_id _)).symm).trans ?_
  refine (congrArg (· ≫ _) (Q.map_comp _ _)).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h1)

omit [HasDerivedCategory A] in
/-- **A twist `τ : P ⟶ P ⋙ S` on a complex in degree zero, derived**: the degreewise twist of
`P(M[0])` followed by the derived-functor unit of the exact `S` is, through
`P(M[0]) ≅ (P M)[0]`, the twist `τ_M` placed in degree zero followed by
`(S P M)[0] ≅ RS((P M)[0])`. -/
theorem twist_comp_mapCochainComplexPlusDerivedUnit_singlePlus [EnoughInjectives B] (P : A ⥤ B)
    (S : B ⥤ B) [P.Additive] [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (τ : P ⟶ P ⋙ S) (M : A) :
    DerivedCategory.Plus.Q.map (ObjectProperty.homMk
        (X := P.mapCochainComplexPlus.obj ((Stacks.DerivedIndexing.singlePlusFunctor A 0).obj M))
        (Y := S.mapCochainComplexPlus.obj (P.mapCochainComplexPlus.obj
          ((Stacks.DerivedIndexing.singlePlusFunctor A 0).obj M)))
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
          ((Stacks.DerivedIndexing.singlePlusFunctor A 0).obj M).obj)) ≫
        (Functor.mapCochainComplexPlusDerivedUnit S).app
          (P.mapCochainComplexPlus.obj ((Stacks.DerivedIndexing.singlePlusFunctor A 0).obj M)) ≫
        S.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (mapCochainComplexPlusSinglePlusIso P M).hom) =
      DerivedCategory.Plus.Q.map (mapCochainComplexPlusSinglePlusIso P M).hom ≫
        (DerivedCategory.Plus.singleFunctor B 0).map (τ.app M) ≫
        (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso S 0).hom.app (P.obj M) := by
  have hn := (Functor.mapCochainComplexPlusDerivedUnit S).naturality
    (mapCochainComplexPlusSinglePlusIso P M).hom
  dsimp only [Functor.comp_map] at hn
  have hs := mapHomologicalComplex_singlePlus_comp P S τ M
  let Q := DerivedCategory.Plus.Q (C := B)
  have key := ((congrArg (Q.map _ ≫ ·) (Q.map_comp _ _).symm).trans
    (Q.map_comp _ _).symm).trans ((congrArg Q.map hs).trans (Q.map_comp _ _))
  refine (congrArg (Q.map _ ≫ ·) hn.symm).trans ?_
  refine (congrArg (fun t => Q.map _ ≫ Q.map _ ≫ t)
    (mapCochainComplexPlusDerivedUnit_app_singlePlus S (P.obj M))).trans ?_
  refine (congrArg (Q.map _ ≫ ·) (Category.assoc _ _ _).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) key).trans ?_
  exact Category.assoc _ _ _

end Generic

/-! ### The Galois action on the cohomology of `(j_! F)|_{X̄_k̄}` -/

section Single

attribute [local instance] HasDerivedCategory.standard
attribute [local instance high] etaleModules_hasSheafify

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosed kbar] (Λ : Type) [Ring Λ] (σ : kbar ≃ₐ[k] kbar)

/-- `Stacks.EtaleCohomology.integralSelfMapCohomologyEndo` written through the derived global
sections. -/
theorem integralSelfMapCohomologyEndo_eq {Y : Scheme.{u}} (φ : Y ⟶ Y) [IsIntegralHom φ]
    (N : EtaleModules.{u, 0} Λ Y) (α : N ⟶ (etaleModuleDirectImage.{u, 0} Λ φ).obj N) (i : ℤ) :
    integralSelfMapCohomologyEndo Λ φ N α i =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
        ((etaleModuleDerivedGlobalSections.{u, 0} Λ Y).map
            ((DerivedCategory.Plus.singleFunctor _ 0).map α) ≫
          (etaleModuleDerivedGlobalSections.{u, 0} Λ Y).map
            ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
              (etaleModuleDirectImage.{u, 0} Λ φ) 0).hom.app N) ≫
          (etaleModuleDerivedGlobalSectionsCompIso.{u, 0} Λ φ).inv.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj N)) :=
  show (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
        ((etaleModuleDerivedGlobalSections.{u, 0} Λ Y).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map α)) ≫
      (integralDirectImageCohomologyIso Λ φ N i).hom = _ from
  (congrArg (_ ≫ ·) (integralDirectImageCohomologyIso_hom_eq Λ φ N i)).trans
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map_comp _ _).symm

omit [IsAlgClosed kbar] in
/-- **The action of `σ` on `RΓ(X̄_k̄, (L[0])|_{X̄_k̄})`** is, through
`(L[0])|_{X̄_k̄} ≅ (L|_{X̄_k̄})[0]`, the self-map twist of `L|_{X̄_k̄}` in degree zero followed
by `RΓ(X̄_k̄, (s_σ)_* -) ≅ RΓ(X̄_k̄, -)`. -/
theorem galoisRestrictionCohomologyEndo_singlePlus
    (L : EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) :
    galoisRestrictionCohomologyEndo.{u, 0} Λ (Over.mk j.toBase) kbar σ
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj L) ≫
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar)).map
        (DerivedCategory.Plus.Q.map (mapCochainComplexPlusSinglePlusIso
          (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)) L).hom) =
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar)).map
          (DerivedCategory.Plus.Q.map (mapCochainComplexPlusSinglePlusIso
            (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar))
              L).hom) ≫
        (etaleModuleDerivedGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar)).map
            ((DerivedCategory.Plus.singleFunctor
              (EtaleModules.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar)) 0).map
              ((selfMapTwist.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)
                (galoisBaseChange (Over.mk j.toBase) kbar σ)
                (galoisBaseChange_comp_fst (Over.mk j.toBase) kbar σ)).app L)) ≫
          (etaleModuleDerivedGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar)).map
            ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
              (etaleModuleDirectImage.{u, 0} Λ (galoisBaseChange (Over.mk j.toBase) kbar σ))
                0).hom.app
                ((etaleModuleInverseImage.{u, 0} Λ
                  (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj L)) ≫
          (etaleModuleDerivedGlobalSectionsCompIso.{u, 0} Λ
            (galoisBaseChange (Over.mk j.toBase) kbar σ)).inv.app
            ((DerivedCategory.Plus.singleFunctor
              (EtaleModules.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar)) 0).obj
              ((etaleModuleInverseImage.{u, 0} Λ
                (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj L)) := by
  have hex := etaleModuleDirectImage_exact_of_isIntegralHom Λ
    (galoisBaseChange (Over.mk j.toBase) kbar σ)
  have := hex.1
  have := hex.2
  let RΓ := etaleModuleDerivedGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar)
  have hn := (etaleModuleDerivedGlobalSectionsCompIso.{u, 0} Λ
    (galoisBaseChange (Over.mk j.toBase) kbar σ)).inv.naturality
      (DerivedCategory.Plus.Q.map (mapCochainComplexPlusSinglePlusIso
        (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)) L).hom)
  dsimp only [Functor.comp_map] at hn
  have h2 := twist_comp_mapCochainComplexPlusDerivedUnit_singlePlus
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar))
    (etaleModuleDirectImage.{u, 0} Λ (galoisBaseChange (Over.mk j.toBase) kbar σ))
    (selfMapTwist.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)
      (galoisBaseChange (Over.mk j.toBase) kbar σ)
      (galoisBaseChange_comp_fst (Over.mk j.toBase) kbar σ)) L
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) hn.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) ((RΓ.map_comp _ _).symm.trans (congrArg RΓ.map
    ((Category.assoc _ _ _).trans h2)))).trans ?_
  refine (congrArg (· ≫ _) ((RΓ.map_comp _ _).trans
    (congrArg (_ ≫ ·) (RΓ.map_comp _ _)))).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))

omit [IsAlgClosed kbar] in
/-- **The Galois action on `H^i_c(X_k̄, F)` is the pullback action of `s_σ` on
`H^i(X̄_k̄, (j_! F)|_{X̄_k̄})`**, linearized by the self-map twist of the restriction along
`X̄_k̄ ⟶ X̄`, through `Stacks.EtaleCohomology.galoisCompactSupportSingleIso`. -/
theorem galoisCompactSupportGroupAction_comp_singleIso (F : EtaleModules.{u, 0} Λ X) (i : ℤ) :
    galoisCompactSupportGroupAction.{u, 0} Λ f j kbar σ
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) i ≫
        (galoisCompactSupportSingleIso f j kbar Λ F i).hom =
      (galoisCompactSupportSingleIso f j kbar Λ F i).hom ≫
        integralSelfMapCohomologyEndo Λ (galoisBaseChange (Over.mk j.toBase) kbar σ)
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))
          ((selfMapTwist.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)
            (galoisBaseChange (Over.mk j.toBase) kbar σ)
            (galoisBaseChange_comp_fst (Over.mk j.toBase) kbar σ)).app
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) i := by
  let P := etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)
  let E := etaleModuleExtensionByZero.{u, 0} Λ j.immersion
  let RΓ := etaleModuleDerivedGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar)
  let Q := DerivedCategory.Plus.Q (C := EtaleModules.{u, 0} Λ
    (fieldBaseChange (Over.mk j.toBase) kbar))
  let Hm := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i
  let ψ := (mapCochainComplexPlusSinglePlusIso E F).hom
  let ι := (mapCochainComplexPlusSinglePlusIso P (E.obj F)).hom
  have hI : (galoisCompactSupportSingleIso f j kbar Λ F i).hom =
      Hm.map (RΓ.map (Q.map (P.mapCochainComplexPlus.map ψ)) ≫ RΓ.map (Q.map ι)) :=
    congrArg Hm.map ((congrArg RΓ.map (Q.map_comp _ _)).trans (RΓ.map_comp _ _))
  have hN := galoisRestrictionCohomologyEndo_naturality.{u, 0} Λ (Over.mk j.toBase) kbar σ ψ
  have hS := galoisRestrictionCohomologyEndo_singlePlus f j kbar Λ σ (E.obj F)
  have key := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ RΓ.map (Q.map ι)) hN).trans
    ((Category.assoc _ _ _).trans ((congrArg (RΓ.map (Q.map (P.mapCochainComplexPlus.map ψ)) ≫ ·)
      hS).trans (Category.assoc _ _ _).symm)))
  refine (congrArg (_ ≫ ·) hI).trans ?_
  refine (Hm.map_comp _ _).symm.trans ?_
  refine (congrArg Hm.map key).trans ?_
  refine (Hm.map_comp _ _).trans ?_
  exact congrArg₂ (· ≫ ·) hI.symm (integralSelfMapCohomologyEndo_eq Λ _ _ _ i).symm

end Single

/-- The diagram chase of `galoisCompactSupportSmoothModelIso_hom_galoisAction`. -/
private lemma conjugation_chase {D : Type*} [Category D] {A B C₁ C₂ E : D} (act : A ⟶ A)
    (si : A ⟶ B) (eN : B ⟶ B) (t₁ : B ⟶ C₁) (t₂ : C₁ ⟶ C₂) (eC : C₂ ⟶ C₂) (ι : C₂ ⟶ E)
    (aC : E ⟶ E) (hH : act ≫ si = si ≫ eN) (hT : eN ≫ t₁ ≫ t₂ = t₁ ≫ t₂ ≫ eC)
    (hA : ι ≫ aC = eC ≫ ι) :
    act ≫ si ≫ t₁ ≫ t₂ ≫ ι = (si ≫ t₁ ≫ t₂ ≫ ι) ≫ aC := by
  rw [reassoc_of% hH, reassoc_of% hT, Category.assoc, Category.assoc, Category.assoc, hA]

/-- Naturality transported along isomorphisms intertwining the actions. -/
private lemma naturality_of_conjugation_chase {D : Type*} [Category D] {A A' B B' : D}
    (e : A ≅ B) (e' : A' ≅ B') (act : A ⟶ A) (act' : A' ⟶ A') (aC : B ⟶ B) (aC' : B' ⟶ B')
    (m : A ⟶ A') (M : B ⟶ B') (hF : act ≫ e.hom = e.hom ≫ aC)
    (hF' : act' ≫ e'.hom = e'.hom ≫ aC') (hS : m ≫ e'.hom = e.hom ≫ M)
    (hG : act ≫ m = m ≫ act') :
    aC ≫ M = M ≫ aC' := by
  rw [← cancel_epi e.hom, ← reassoc_of% hF, ← hS, reassoc_of% hG, hF', reassoc_of% hS]

/-! ### From `X̄_k̄` to the smooth model -/

section SmoothModel

attribute [local instance] HasDerivedCategory.standard
attribute [local instance high] etaleModules_hasSheafify

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] (Λ : Type) [Ring Λ] (σ : kbar ≃ₐ[k] kbar)

/-- **The restriction map to the smooth model intertwines the two twists**: the self-map twist
of `(j_! F)|_{X̄_k̄}` along `s_σ`, followed by `(s_σ)_*` of the restriction map
`(j_! F)|_{X̄_k̄} ⟶ f̄_* q^{-1}(j_! F)`, is the restriction map followed by `f̄_*` of the twist of
`q^{-1}(j_! F)` along `s̃_σ` and `f̄_* (s̃_σ)_* ⟶ (s_σ)_* f̄_*`. -/
theorem selfMapTwist_comp_geometricSmoothModelRestriction (F : EtaleModules.{u, 0} Λ X) :
    (selfMapTwist.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))
        (galoisBaseChange (Over.mk j.toBase) kbar σ)
        (galoisBaseChange_comp_fst (Over.mk j.toBase) kbar σ)).app
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F) ≫
      (etaleModuleDirectImage.{u, 0} Λ (galoisBaseChange (Over.mk j.toBase) kbar σ)).map
        (geometricSmoothModelRestriction f j kbar Λ F) =
    geometricSmoothModelRestriction f j kbar Λ F ≫
      (etaleModuleDirectImage.{u, 0} Λ (geometricSmoothModel f j kbar).fb).map
        ((selfMapTwist.{u, 0} Λ (geometricSmoothModelProj f j kbar)
          (geometricSmoothModelGaloisAut f j kbar σ)
          (geometricSmoothModelGaloisAut_comp_proj f j kbar σ)).app
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ≫
      (directImageTwistTransfer Λ (geometricSmoothModel f j kbar).fb
        (geometricSmoothModelGaloisAut f j kbar σ) (galoisBaseChange (Over.mk j.toBase) kbar σ)
        (geometricSmoothModelGaloisAut_fb f j kbar σ)).app
          ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) :=
  selfMapTwist_comp_map_selfMapRestriction Λ (pullback.fst j.toBase (specAlgebraMap k kbar))
    (geometricSmoothModel f j kbar).fb (geometricSmoothModelProj f j kbar) rfl
    (galoisBaseChange (Over.mk j.toBase) kbar σ)
    (galoisBaseChange_comp_fst (Over.mk j.toBase) kbar σ)
    (geometricSmoothModelGaloisAut f j kbar σ)
    (geometricSmoothModelGaloisAut_comp_proj f j kbar σ)
    (geometricSmoothModelGaloisAut_fb f j kbar σ)
    ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)

/-- **`H^i(X̄_k̄, (j_! F)|_{X̄_k̄}) ⟶ H^i(C, q^{-1}(j_! F))` intertwines the pullback actions** of
`s_σ` and `s̃_σ`: the restriction map followed by `H^i(X̄_k̄, f̄_* -) ≅ H^i(C, -)`. -/
theorem integralSelfMapCohomologyEndo_comp_geometricSmoothModelRestriction
    (F : EtaleModules.{u, 0} Λ X) (i : ℤ) :
    integralSelfMapCohomologyEndo Λ (galoisBaseChange (Over.mk j.toBase) kbar σ) _
        ((selfMapTwist.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))
          (galoisBaseChange (Over.mk j.toBase) kbar σ)
          (galoisBaseChange_comp_fst (Over.mk j.toBase) kbar σ)).app
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) i ≫
      ((etaleModuleGlobalSections.{u, 0} Λ
          (pullback j.toBase (specAlgebraMap k kbar))).rightDerivedPlus
          i).map (geometricSmoothModelRestriction f j kbar Λ F) ≫
        (integralDirectImageCohomologyIso Λ (geometricSmoothModel f j kbar).fb _ i).hom =
    ((etaleModuleGlobalSections.{u, 0} Λ
          (pullback j.toBase (specAlgebraMap k kbar))).rightDerivedPlus
          i).map (geometricSmoothModelRestriction f j kbar Λ F) ≫
        (integralDirectImageCohomologyIso Λ (geometricSmoothModel f j kbar).fb _ i).hom ≫
      integralSelfMapCohomologyEndo Λ (geometricSmoothModelGaloisAut f j kbar σ) _
        ((selfMapTwist.{u, 0} Λ (geometricSmoothModelProj f j kbar)
          (geometricSmoothModelGaloisAut f j kbar σ)
          (geometricSmoothModelGaloisAut_comp_proj f j kbar σ)).app
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) i := by
  have hb := integralSelfMapCohomologyEndo_naturality Λ (galoisBaseChange (Over.mk j.toBase) kbar σ)
    _ _ _ (selfMapTwist_comp_geometricSmoothModelRestriction f j kbar Λ σ F) i
  have hc := integralSelfMapCohomologyEndo_directImage Λ (geometricSmoothModelGaloisAut f j kbar σ)
    (geometricSmoothModel f j kbar).fb (galoisBaseChange (Over.mk j.toBase) kbar σ)
    (geometricSmoothModelGaloisAut_fb f j kbar σ)
    ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))
    ((selfMapTwist.{u, 0} Λ (geometricSmoothModelProj f j kbar)
      (geometricSmoothModelGaloisAut f j kbar σ)
      (geometricSmoothModelGaloisAut_comp_proj f j kbar σ)).app
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) i
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hb).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hc)))

/-- `galoisCompactSupportSmoothModelIso` through the restriction map to the smooth model and
`q^{-1}(j_! F) ≅ j_{C!}(F|_{X_k̄})`. -/
theorem galoisCompactSupportSmoothModelIso_hom_eq_restriction (F : EtaleModules.{u, 0} Λ X)
    (i : ℤ) :
    (galoisCompactSupportSmoothModelIso f j kbar Λ F i).hom =
      (galoisCompactSupportSingleIso f j kbar Λ F i).hom ≫
        ((etaleModuleGlobalSections.{u, 0} Λ (pullback j.toBase (specAlgebraMap k
            kbar))).rightDerivedPlus i).map (geometricSmoothModelRestriction f j kbar Λ F) ≫
        (integralDirectImageCohomologyIso Λ (geometricSmoothModel f j kbar).fb _ i).hom ≫
        ((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
          i).map (geometricSmoothModelInverseImageIso f j kbar Λ F).hom := by
  let R := (etaleModuleGlobalSections.{u, 0} Λ (pullback j.toBase (specAlgebraMap k
    kbar))).rightDerivedPlus i
  have h1 : R.map ((compactificationFieldBaseChangeExtensionByZeroIso Λ f j kbar).inv.app F) ≫
      R.map (extensionByZeroGeometricSmoothModelIso f j kbar Λ
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F)).hom =
      R.map (geometricSmoothModelRestriction f j kbar Λ F) ≫
        R.map ((etaleModuleDirectImage.{u, 0} Λ (geometricSmoothModel f j kbar).fb).map
          (geometricSmoothModelInverseImageIso f j kbar Λ F).hom) :=
    (R.map_comp _ _).symm.trans ((congrArg R.map
      (geometricSmoothModelRestriction_comp_inverseImageIso f j kbar Λ F).symm).trans
        (R.map_comp _ _))
  have h2 := integralDirectImageCohomologyIso_hom_naturality.{u, 0} Λ
    (geometricSmoothModel f j kbar).fb (geometricSmoothModelInverseImageIso f j kbar Λ F).hom i
  refine (galoisCompactSupportSmoothModelIso_hom f j kbar Λ F i).trans ?_
  refine congrArg (_ ≫ ·) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h1).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h2)

/-- `geometricSmoothModelGaloisAction` read through `q^{-1}(j_! F) ≅ j_{C!}(F|_{X_k̄})`. -/
theorem inverseImageIso_comp_geometricSmoothModelGaloisAction (F : EtaleModules.{u, 0} Λ X)
    (i : ℤ) :
    ((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
          i).map (geometricSmoothModelInverseImageIso f j kbar Λ F).hom ≫
        geometricSmoothModelGaloisAction f j kbar Λ σ F i =
      integralSelfMapCohomologyEndo Λ (geometricSmoothModelGaloisAut f j kbar σ) _
          ((selfMapTwist.{u, 0} Λ (geometricSmoothModelProj f j kbar)
            (geometricSmoothModelGaloisAut f j kbar σ)
            (geometricSmoothModelGaloisAut_comp_proj f j kbar σ)).app
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) i ≫
        ((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
          i).map (geometricSmoothModelInverseImageIso f j kbar Λ F).hom := by
  let R := (etaleModuleGlobalSections.{u, 0} Λ
    (geometricSmoothModel f j kbar).Vb).rightDerivedPlus i
  exact (R.mapIso (geometricSmoothModelInverseImageIso f j kbar Λ F)).hom_inv_id_assoc _

/-- **The Galois action on `H^i_c(X_k̄, F)` is the pullback action of `s̃_σ` on the smooth model**:
under `H^i_c(X_k̄, F) ≅ H^i(C, j_{C!}(F|_{X_k̄}))`
(`Stacks.EtaleCohomology.galoisCompactSupportSmoothModelIso`) the action of `σ ∈ Aut_k(k̄)`
induced by `id_{X̄} × Spec σ` on `X̄_k̄` is the action
`Stacks.EtaleCohomology.geometricSmoothModelGaloisAction` induced by
`s̃_σ = id_{C'} × Spec σ` on `C`. -/
theorem galoisCompactSupportSmoothModelIso_hom_galoisAction (F : EtaleModules.{u, 0} Λ X)
    (i : ℤ) :
    galoisCompactSupportGroupAction Λ f j kbar σ
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) i ≫
        (galoisCompactSupportSmoothModelIso f j kbar Λ F i).hom =
      (galoisCompactSupportSmoothModelIso f j kbar Λ F i).hom ≫
        geometricSmoothModelGaloisAction f j kbar Λ σ F i := by
  have hE := galoisCompactSupportSmoothModelIso_hom_eq_restriction f j kbar Λ F i
  exact (congrArg (_ ≫ ·) hE).trans ((conjugation_chase _ _ _ _ _ _ _ _
    (galoisCompactSupportGroupAction_comp_singleIso f j kbar Λ σ F i)
    (integralSelfMapCohomologyEndo_comp_geometricSmoothModelRestriction f j kbar Λ σ F i)
    (inverseImageIso_comp_geometricSmoothModelGaloisAction f j kbar Λ σ F i)).trans
      (congrArg (· ≫ _) hE.symm))

/-- **The Galois action on the smooth model is natural in `F`.** -/
theorem geometricSmoothModelGaloisAction_naturality {F F' : EtaleModules.{u, 0} Λ X} (g : F ⟶ F')
    (i : ℤ) :
    geometricSmoothModelGaloisAction f j kbar Λ σ F i ≫
        ((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
            i).map
          ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).map
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map g)) =
      ((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
            i).map
          ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).map
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map g)) ≫
        geometricSmoothModelGaloisAction f j kbar Λ σ F' i :=
  naturality_of_conjugation_chase _ _ _ _ _ _ _ _
    (galoisCompactSupportSmoothModelIso_hom_galoisAction f j kbar Λ σ F i)
    (galoisCompactSupportSmoothModelIso_hom_galoisAction f j kbar Λ σ F' i)
    (galoisCompactSupportSmoothModelIso_hom_naturality f j kbar Λ g i)
    (galoisCompactSupportGroupAction_naturality.{u, 0} Λ f j kbar σ
      ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map g) i)

end SmoothModel

end Stacks.EtaleCohomology

end
