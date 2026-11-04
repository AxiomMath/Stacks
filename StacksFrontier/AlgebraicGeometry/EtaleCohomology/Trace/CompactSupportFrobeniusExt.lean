module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportExt
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedTwistEdge

/-!
# The canonical geometric Frobenius on `Hⁱ_c(X_k̄, K)`, read on the cohomology of `X̄_k̄`

Let `k` be a finite field, `X` a `k`-scheme with a compactification `j : X ⟶ X̄`, `k̄` an
extension of `k`, `Y = X̄_k̄` with structure morphism `g : Y ⟶ Spec k̄`, and `π̄ : Y ⟶ Y` the base
change of the geometric Frobenius of `X̄`. The canonical endomorphism `π_X^*` of
`RΓ_c(X_k̄, K) = RΓ(Spec k̄, Rg_*((j_! K)|_Y))` of
`Stacks.EtaleCohomology.canonicalCompactSupportFrobenius` is, by construction, the derived
endomorphism `CategoryTheory.Functor.derivedTwistEndo` attached to the twist
`τ : (j_! K)|_Y ⟶ π̄_*((j_! K)|_Y)` (the base change of the Frobenius descent isomorphism of
[Stacks, Tag 03SR]), with `P = π̄_*`, `F₁ = g_*` and `F₂ = Γ(Spec k̄, -)`
(`canonicalCompactSupportFrobenius_eq_derivedTwistEndo`).

For `K` a single sheaf, read on `Hⁱ_c(X_k̄, K) ≅ Hⁱ(Y, N)`, `N = (j_! K)|_Y`
(`Stacks.EtaleCohomology.compactSupportFrobeniusSingleIso`), it is therefore `τ` on `Hⁱ(Y, -)`
followed by the degreewise comparison `Hⁱ(Y, π̄_* N) ⟶ Rⁱ(π̄_* ⋙ Γ(Y, -))(N)` of
[Stacks, Tag 015M] and the map induced by `Γ(Y, π̄_* -) ≅ Γ(Y, -)`
(`compactSupportFrobeniusSingleIso_conj_canonicalCompactSupportFrobeniusGroup`). This is the
derived half of the identification, in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), of the canonical Frobenius on
`Ext^i(Λ, N)` with the twisted action `Stacks.ExtCup.twistAction`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The composition isomorphism `π̄_* ⋙ g_* ≅ g_*` for the base change `π̄` of the geometric
Frobenius over `g : X̄_k̄ ⟶ Spec k̄`. -/
abbrev frobeniusDirectImageComp :
    etaleModuleDirectImage.{u, 0} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard) ⋙
        etaleModuleDirectImage.{u, 0} Λ
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) ≅
      etaleModuleDirectImage.{u, 0} Λ
        (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) :=
  etaleModuleDirectImageComp.{u, 0} Λ
    (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)
    (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
    (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
    (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard).symm

/-- **The canonical Frobenius is a derived twist endomorphism**: the endomorphism of
`RΓ(Spec k̄, Rg_*(C|_{X̄_k̄}))` attached to the twist `C|_{X̄_k̄} ⟶ π̄_*(C|_{X̄_k̄})` with
`P = π̄_*`, `F₁ = g_*` and `F₂ = Γ(Spec k̄, -)`. -/
theorem canonicalCompactSupportFrobenius_eq_derivedTwistEndo
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q hcard K =
      Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, 0} Λ
          (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} Λ
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
        (frobeniusDirectImageComp Λ f j kbar p q hcard)
        ((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K))
        (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex
          (frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk j.toBase) kbar p q hcard)
            (ComplexShape.up ℤ)).app
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
                K).obj)) :=
  rfl

/-- Pasting two squares, abstract in the objects. -/
private lemma twist_single_aux {A : Type*} [Category* A] {X₀ X₁ Y₀ Y₁ Y₂ Z₂ : A}
    {a : X₀ ⟶ Y₀} {τ₀ : X₀ ⟶ X₁} {b : X₁ ⟶ Y₁} {τ₁ : Y₀ ⟶ Y₁} {c : Y₁ ⟶ Y₂} {d : Y₀ ⟶ Z₂}
    {e : Z₂ ⟶ Y₂} (h1 : a ≫ τ₁ = τ₀ ≫ b) (h2 : τ₁ ≫ c = d ≫ e) :
    τ₀ ≫ (b ≫ c) = (a ≫ d) ≫ e := by
  rw [← reassoc_of% h1, h2, Category.assoc]

/-- The twist `t : I ⟶ I ⋙ P` applied degreewise to an object placed in degree zero is `t` at that
object, placed in degree zero. -/
private lemma mapHomologicalComplex_twist_single {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Preadditive B] [HasZeroObject A] [HasZeroObject B] (I : A ⥤ B) (P : B ⥤ B)
    [I.Additive] [P.Additive] (t : I ⟶ I ⋙ P) (Z : A) :
    (NatTrans.mapHomologicalComplex t (ComplexShape.up ℤ)).app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj Z) ≫
      (P.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex I (ComplexShape.up ℤ) 0).hom.app Z) =
    (HomologicalComplex.singleMapHomologicalComplex I (ComplexShape.up ℤ) 0).hom.app Z ≫
      (HomologicalComplex.single B (ComplexShape.up ℤ) 0).map (t.app Z) ≫
      (HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) 0).inv.app
        (I.obj Z) := by
  ext n
  by_cases hn : n = 0
  · subst hn
    have hnat := t.naturality (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Z).hom
    simp only [Functor.comp_map] at hnat
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]
    rw [reassoc_of% hnat]
    congr 2
    exact (Iso.inv_hom_id_assoc _ _).symm
  · refine IsZero.eq_of_tgt ?_ _ _
    exact P.map_isZero (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (I.obj Z) n hn)

/-- **The twist commutes with placing in degree zero**, through the identification of a functor of
a complex in degree zero with the complex in degree zero of the functor. -/
private lemma homMk_twist_comp_map_singleIso {A' A B : Type*} [Category* A'] [Category* A]
    [Category* B] [Abelian A'] [Abelian A] [Abelian B] (E : A' ⥤ A) (I : A ⥤ B) (P : B ⥤ B)
    [E.Additive] [I.Additive] [P.Additive] (t : I ⟶ I ⋙ P) (K : A') :
    ObjectProperty.homMk ((NatTrans.mapHomologicalComplex t (ComplexShape.up ℤ)).app
          (E.mapCochainComplexPlus.obj
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj K)).obj) ≫
        P.mapCochainComplexPlus.map
          (I.mapCochainComplexPlus.mapIso (mapCochainComplexPlusSinglePlusIso E K) ≪≫
            mapCochainComplexPlusSinglePlusIso I (E.obj K)).hom =
      (I.mapCochainComplexPlus.mapIso (mapCochainComplexPlusSinglePlusIso E K) ≪≫
          mapCochainComplexPlusSinglePlusIso I (E.obj K)).hom ≫
        Functor.singleTwist P (t.app (E.obj K)) := by
  have h1 := (NatTrans.mapHomologicalComplex t (ComplexShape.up ℤ)).naturality
    ((HomologicalComplex.singleMapHomologicalComplex E (ComplexShape.up ℤ) 0).hom.app K)
  have h2 := mapHomologicalComplex_twist_single I P t (E.obj K)
  rw [Iso.trans_hom, Functor.map_comp, Functor.mapIso_hom]
  refine ObjectProperty.hom_ext _ ?_
  exact twist_single_aux h1 h2

/-- The identification of the restriction of `j_!` of a sheaf placed in degree zero with the
restriction placed in degree zero, as in
`Stacks.EtaleCohomology.compactSupportFrobeniusSingleIso`. -/
abbrev compactSupportSingleRestrictionIso (K : EtaleModules.{u, 0} Λ X) :
    (etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj K)) ≅
      (Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K)) :=
  (etaleModuleInverseImage.{u, 0} Λ
    (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.mapIso
      (mapCochainComplexPlusSinglePlusIso (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) K) ≪≫
    mapCochainComplexPlusSinglePlusIso
      (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar))
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K)

/-- The twist of the restriction of `j_! K` placed in degree zero is the twist of the restriction
of `j_! K`, placed in degree zero. -/
theorem singleTwist_compactSupportSingleRestrictionIso (K : EtaleModules.{u, 0} Λ X) :
    ObjectProperty.homMk ((NatTrans.mapHomologicalComplex
          (frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk j.toBase) kbar p q hcard)
            (ComplexShape.up ℤ)).app
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
                ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj K)).obj) ≫
        (etaleModuleDirectImage.{u, 0} Λ
          (geometricFrobeniusBaseChange
            (Over.mk j.toBase) kbar p q hcard)).mapCochainComplexPlus.map
          (compactSupportSingleRestrictionIso Λ f j kbar K).hom =
      (compactSupportSingleRestrictionIso Λ f j kbar K).hom ≫
        Functor.singleTwist (etaleModuleDirectImage.{u, 0} Λ
          (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
          ((frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk j.toBase) kbar p q hcard).app
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K)) :=
  homMk_twist_comp_map_singleIso _ _ _ _ K

/-- Conjugating an image under a functor by an isomorphism that a naturality square moves across,
abstract in the objects. -/
private lemma conj_naturality_aux {A B : Type*} [Category* A] [Category* B] (G : A ⥤ B)
    {W X Y Z : A} {c : W ⟶ X} {r' : X ⟶ Y} {d : Y ⟶ Y} {r : Y ⟶ X} {d' : X ⟶ X} {ci : X ⟶ Z}
    (hnat : d ≫ r = r ≫ d') (hri : r' ≫ r = 𝟙 X) :
    G.map (c ≫ r') ≫ G.map d ≫ G.map (r ≫ ci) = G.map (c ≫ d' ≫ ci) := by
  rw [← G.map_comp, ← G.map_comp]
  congr 1
  simp only [Category.assoc]
  rw [reassoc_of% hnat, reassoc_of% hri]

/-- **The canonical Frobenius on `Hⁱ_c(X_k̄, K)`, read on `Hⁱ(X̄_k̄, N)`**, `N = (j_! K)|_{X̄_k̄}`,
for a sheaf `K` placed in degree zero: it is the twist `τ : N ⟶ π̄_* N` on `Hⁱ(X̄_k̄, -)`, followed
by the degreewise comparison of [Stacks, Tag 015M] for `π̄_*` and global sections, and by the map
induced by `Γ(X̄_k̄, π̄_* -) ≅ Γ(X̄_k̄, -)`. -/
theorem compactSupportFrobeniusSingleIso_conj_canonicalCompactSupportFrobeniusGroup
    (K : EtaleModules.{u, 0} Λ X) (i : ℤ) :
    (compactSupportFrobeniusSingleIso Λ f j kbar K i).inv ≫
        canonicalCompactSupportFrobeniusGroup.{u, 0} Λ f j kbar p q hcard
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj K) i ≫
        (compactSupportFrobeniusSingleIso Λ f j kbar K i).hom =
      ((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).rightDerivedPlus
          i).map ((frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk j.toBase) kbar p q hcard).app
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K)) ≫
        (Stacks.DerivedIndexing.rightDerivedPlusEdge
          (etaleModuleDirectImage.{u, 0} Λ
            (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
          (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar)) i).app
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K)) ≫
        (Stacks.DerivedIndexing.rightDerivedPlusNatTrans
          (Functor.twistEdgeIso
            (etaleModuleDirectImage.{u, 0} Λ
              (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
            (etaleModuleDirectImage.{u, 0} Λ
              (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
            (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
            (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar))
            (frobeniusDirectImageComp Λ f j kbar p q hcard)
            (etaleModuleGlobalSectionsDirectImageIso
              (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) Λ)).hom i).app
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K)) := by
  have hL1 := Functor.homologyMap_derivedTwistEndo_single
    (etaleModuleDirectImage.{u, 0} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
    (etaleModuleDirectImage.{u, 0} Λ (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
    (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar))
    (frobeniusDirectImageComp Λ f j kbar p q hcard)
    (etaleModuleGlobalSectionsDirectImageIso
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) Λ)
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K))
    ((frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk j.toBase) kbar p q hcard).app
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K)) i
  have hnat := Functor.derivedTwistEndo_naturality
    (etaleModuleDirectImage.{u, 0} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
    (etaleModuleDirectImage.{u, 0} Λ (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
    (frobeniusDirectImageComp Λ f j kbar p q hcard)
    (compactSupportSingleRestrictionIso Λ f j kbar K).hom _ _
    (congrArg DerivedCategory.Plus.Q.map
      (singleTwist_compactSupportSingleRestrictionIso Λ f j kbar p q hcard K))
  refine Eq.trans ?_ hL1
  exact conj_naturality_aux (DerivedCategory.Plus.homologyFunctor _ i) hnat
    (Iso.inv_hom_id _)

end Stacks.EtaleCohomology
