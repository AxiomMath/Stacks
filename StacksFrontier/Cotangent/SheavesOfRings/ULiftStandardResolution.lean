module

public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftSite
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageStandardResolutionComparison
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseSheafification

/-!
# Lifting the universe of the sections and the standard resolution

Let `A` be a sheaf of commutative rings on a site, with sections in a universe `max u v w`
containing the universes of the objects and of the morphisms of the site. Raising the universe
of its sections by `ULift` (the functor
`sheafCompose J AlgebraicGeometry.SheafOfModules.commRingCatULift`, written `↑` below) is
compatible with the free–forgetful adjunction for sheaves of algebras: `↑` commutes with the
forgetful functors to sheaves of sets on the nose, and the free `↑A`-algebra sheaf on the lift of
a sheaf of sets `E` is the lift of the free `A`-algebra sheaf on `E`. Consequently the lift of the
standard resolution of a homomorphism `a : A ⟶ B` is the standard resolution of `↑a`.

## Main definitions

* `Stacks.UniverseLift.hasSheafCompose_commRingCatULift`: raising the universe of the section
  rings preserves sheaves of commutative rings, as an instance, so that `↑` is `sheafCompose`.
* `CategoryTheory.Sheaf.forgetAlgebraSheafULiftIso`: the commuting square of forgetful functors.
* `CategoryTheory.Sheaf.freeAlgebraSheafULiftIso`: the commuting square of free algebra
  functors, `↑A[↑E] ≅ ↑(A[E])`.
* `CategoryTheory.Sheaf.standardResolutionULiftIso`: the lift of the standard resolution of `a`
  is the standard resolution of `↑a`.
* `CategoryTheory.Sheaf.resolutionULiftIso`: its degreewise form, as isomorphisms of sheaves of
  commutative rings.

## Main results

* `CategoryTheory.Sheaf.W_whiskerRight_commRingCatULift`: raising the universe of the sections
  preserves the morphisms of presheaves of commutative rings inverted by sheafification.
* `CategoryTheory.Sheaf.freeAlgebraSheafULiftIso_unit`: the free comparison is compatible with the
  units of the two free–forgetful adjunctions.
* `CategoryTheory.Sheaf.resolutionULiftIso_base`, `resolutionULiftIso_augmentation` and
  `resolutionULiftIso_naturality`: the degreewise comparison is a map of `↑A`-algebras over
  `↑B`, natural in the simplicial variable.

## References

* [Stacks Project, Tag 08SR](https://stacks.math.columbia.edu/tag/08SR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open AlgebraicGeometry.SheafOfModules (commRingCatULift)

attribute [local implicit_reducible] CategoryTheory.Under.post

namespace Stacks.UniverseLift

/-- Raising the universe of the section rings preserves sheaves of commutative rings, on any
site. -/
instance hasSheafCompose_commRingCatULift.{r, z, v₁, u₁} {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose AlgebraicGeometry.SheafOfModules.commRingCatULift.{r, z} :=
  ⟨fun P hP ↦ isSheaf_comp_commRingCatULift P hP⟩

end Stacks.UniverseLift

namespace CategoryTheory.Sheaf

universe u v w w'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-! ## Raising the universe preserves the maps inverted by sheafification -/

section W

variable {P Q : Cᵒᵖ ⥤ CommRingCat.{max u v w}} (f : P ⟶ Q)

/-- Raising the universe of the sections of a morphism of presheaves of commutative rings
preserves local injectivity. -/
theorem isLocallyInjective_whiskerRight_commRingCatULift
    [Presheaf.IsLocallyInjective J f] :
    Presheaf.IsLocallyInjective J
      (Functor.whiskerRight f commRingCatULift.{max u v w, w'}) where
  equalizerSieve_mem {X} x y h := by
    have hs : Presheaf.equalizerSieve (F := P ⋙ commRingCatULift.{max u v w, w'}) x y =
        Presheaf.equalizerSieve (F := P) x.down y.down := by
      ext V i
      simp only [Presheaf.equalizerSieve_apply]
      exact ⟨fun h => congrArg ULift.down h, fun h => congrArg ULift.up h⟩
    rw [hs]
    exact Presheaf.equalizerSieve_mem J f x.down y.down (congrArg ULift.down h)

/-- Raising the universe of the sections of a morphism of presheaves of commutative rings
preserves local surjectivity. -/
theorem isLocallySurjective_whiskerRight_commRingCatULift
    [Presheaf.IsLocallySurjective J f] :
    Presheaf.IsLocallySurjective J
      (Functor.whiskerRight f commRingCatULift.{max u v w, w'}) where
  imageSieve_mem {X} s := by
    have hs : Presheaf.imageSieve
        (Functor.whiskerRight f commRingCatULift.{max u v w, w'}) s =
        Presheaf.imageSieve f s.down := by
      ext V i
      simp only [Presheaf.imageSieve_apply]
      exact ⟨fun ⟨t, ht⟩ => ⟨t.down, congrArg ULift.down ht⟩,
        fun ⟨t, ht⟩ => ⟨ULift.up t, congrArg ULift.up ht⟩⟩
    rw [hs]
    exact Presheaf.imageSieve_mem J f s.down

/-- **Raising the universe of the sections preserves the morphisms inverted by
sheafification**, for morphisms of presheaves of commutative rings on a site whose universes are
contained in that of the sections. -/
theorem W_whiskerRight_commRingCatULift (hf : J.W f) :
    J.W (Functor.whiskerRight f commRingCatULift.{max u v w, w'}) := by
  let := wEqualsLocallyBijective_commRingCat.{u, v, w} J
  let := wEqualsLocallyBijective_commRingCat.{u, v, max w w'} J
  have := hf.isLocallyInjective
  have := hf.isLocallySurjective
  have := isLocallyInjective_whiskerRight_commRingCatULift.{u, v, w, w'} J f
  have := isLocallySurjective_whiskerRight_commRingCatULift.{u, v, w, w'} J f
  exact J.W_of_isLocallyBijective _

end W

/-! ## Polynomial rings with lifted coefficients and variables -/

section Polynomial

universe t t'

/-- Ring maps out of the universe lift of a polynomial algebra are maps out of the lift of the
coefficient ring together with maps out of the lift of the set of variables. -/
theorem bijective_uliftMvPolynomialHom {R σ : Type t} [CommRing R]
    (T : CommRingCat.{max t t'}) : Function.Bijective
      (fun g : commRingCatULift.{t, t'}.obj (CommRingCat.of (MvPolynomial σ R)) ⟶ T =>
        (commRingCatULift.{t, t'}.map (CommRingCat.ofHom MvPolynomial.C) ≫ g,
          uliftFunctor.{t', t}.map (↾fun i : σ => (MvPolynomial.X i : MvPolynomial σ R)) ≫
            (forget CommRingCat.{max t t'}).map g)) := by
  constructor
  · intro g h eq
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj eq
    have hgh : g.hom.comp ULift.ringEquiv.symm.toRingHom =
        h.hom.comp ULift.ringEquiv.symm.toRingHom :=
      MvPolynomial.ringHom_ext (fun r => ConcreteCategory.congr_hom h₁ (ULift.up r))
        (fun i => ConcreteCategory.congr_hom h₂ ⟨i⟩)
    ext x
    exact RingHom.congr_fun hgh x.down
  · intro p
    refine ⟨CommRingCat.ofHom ((MvPolynomial.eval₂Hom
      (p.1.hom.comp ULift.ringEquiv.symm.toRingHom) (fun i => p.2 ⟨i⟩)).comp
        ULift.ringEquiv.toRingHom), Prod.ext ?_ ?_⟩
    · ext r
      exact MvPolynomial.eval₂_C _ _ _
    · ext i
      exact MvPolynomial.eval₂_X _ _ _

end Polynomial


/-! ## The free algebra sheaf and the universe lift -/

section Free

variable (A : Sheaf J CommRingCat.{max u v w})

/-- The square of forgetful functors and universe lifts commutes: the underlying sheaf of sets of
the lift of a sheaf of `A`-algebras is the lift of its underlying sheaf of sets. -/
@[implicit_reducible]
noncomputable def forgetAlgebraSheafULiftIso :
    Under.post (X := A) (sheafCompose J commRingCatULift.{max u v w, w'}) ⋙
        forgetAlgebraSheaf.{v, u, max w w'} J
          ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A) ≅
      forgetAlgebraSheaf.{v, u, w} J A ⋙ sheafCompose J uliftFunctor.{w', max u v w} :=
  NatIso.ofComponents (fun X => Iso.refl ((sheafCompose J uliftFunctor.{w', max u v w}).obj
    ((forgetAlgebraSheaf.{v, u, w} J A).obj X))) (fun {_ _} _ =>
    (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The comparison `↑A[↑E] ⟶ ↑(A[E])` of the free algebra sheaves: the mate of the forgetful
square `forgetAlgebraSheafULiftIso` along the two free–forgetful adjunctions. -/
noncomputable def freeAlgebraSheafULiftHom :
    sheafCompose J uliftFunctor.{w', max u v w} ⋙
        freeAlgebraSheaf.{v, u, max w w'} J
            ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A) ⟶
      freeAlgebraSheaf.{v, u, w} J A ⋙
        Under.post (X := A) (sheafCompose J commRingCatULift.{max u v w, w'}) :=
  ((mateEquiv (freeAlgebraSheafAdjunction.{v, u, w} J A)
    (freeAlgebraSheafAdjunction.{v, u, max w w'} J
      ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A))).symm
        (TwoSquare.mk _ _ _ _ (forgetAlgebraSheafULiftIso.{u, v, w, w'} J A).inv)).natTrans

/-- The comparison of the free algebra sheaves carries the unit of the free–forgetful adjunction
of `↑A` to the lift of the unit of that of `A`. -/
theorem freeAlgebraSheafULiftHom_unit (E : Sheaf J (Type (max u v w))) :
    (sheafCompose J uliftFunctor.{w', max u v w}).map
        ((freeAlgebraSheafAdjunction.{v, u, w} J A).unit.app E) ≫
      (forgetAlgebraSheafULiftIso.{u, v, w, w'} J A).inv.app
        ((freeAlgebraSheaf.{v, u, w} J A).obj E) =
    (freeAlgebraSheafAdjunction.{v, u, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A)).unit.app
          ((sheafCompose J uliftFunctor.{w', max u v w}).obj E) ≫
      (forgetAlgebraSheaf.{v, u, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A)).map
          ((freeAlgebraSheafULiftHom.{u, v, w, w'} J A).app E) :=
  unit_mateEquiv_symm _ _ _ E

/-- **The comparison of the free algebra sheaves is invertible**: `↑A[↑E] ≅ ↑(A[E])`. -/
instance isIso_freeAlgebraSheafULiftHom_app (E : Sheaf J (Type (max u v w))) :
    IsIso ((freeAlgebraSheafULiftHom.{u, v, w, w'} J A).app E) := by
  let A' := (sheafCompose J commRingCatULift.{max u v w, w'}).obj A
  let E' := (sheafCompose J uliftFunctor.{w', max u v w}).obj E
  let S := (freeAlgebraSheaf.{v, u, w} J A).obj E
  let S' := (freeAlgebraSheaf.{v, u, max w w'} J A').obj E'
  let η := (freeAlgebraSheafAdjunction.{v, u, w} J A).unit.app E
  let η' := (freeAlgebraSheafAdjunction.{v, u, max w w'} J A').unit.app E'
  let g := ((freeAlgebraSheafULiftHom.{u, v, w, w'} J A).app E).right
  let Qs := Stacks.Sites.FreeAlgebra.polynomialPresheaf J A E.obj
  let bs := Stacks.Sites.FreeAlgebra.polynomialCoefficientMap J A E.obj
  let xs := Stacks.Sites.FreeAlgebra.polynomialVariable J A E.obj
  let cs : Qs ⟶ S.right.obj :=
    Stacks.Sites.FreeAlgebra.polynomialEvaluation J A S.right E.obj S.hom η.hom
  have hbs : bs ≫ cs = S.hom.hom := by
    ext U r
    exact MvPolynomial.eval₂_C _ _ _
  have hxs : xs ≫ Functor.whiskerRight cs (forget _) = 𝟙 _ ≫ η.hom := by
    ext U e
    exact MvPolynomial.eval₂_X _ _ _
  have hcs : J.W cs := W_of_freeAlgebraSheaf.{u, v, w} J A E E.obj (𝟙 _)
    (ObjectProperty.isLocal_of_isIso _ _) Qs bs xs cs hbs hxs
    (bijective_presheafHom_of_sectionwise.{u, v, w} A.obj Qs E.obj bs xs
      (fun _ T => bijective_mvPolynomialHom T))
  let Qb := Qs ⋙ commRingCatULift.{max u v w, w'}
  let bb : A'.obj ⟶ Qb := Functor.whiskerRight bs commRingCatULift.{max u v w, w'}
  let xb : E'.obj ⟶ Qb ⋙ forget _ :=
    Functor.whiskerRight xs uliftFunctor.{w', max u v w}
  have hQb := bijective_presheafHom_of_sectionwise.{u, v, max w w'} A'.obj Qb E'.obj bb xb
    (fun _ T => bijective_uliftMvPolynomialHom.{max u v w, w'} T)
  obtain ⟨cb, hcb⟩ := (hQb S'.right.obj).surjective (S'.hom.hom, η'.hom)
  obtain ⟨hcb₁, hcb₂⟩ := Prod.mk.inj hcb
  have hcbW : J.W cb := W_of_freeAlgebraSheaf.{u, v, max w w'} J A' E' E'.obj (𝟙 _)
    (ObjectProperty.isLocal_of_isIso _ _) Qb bb xb cb hcb₁
    (hcb₂.trans (Category.id_comp _).symm) hQb
  have hunit := freeAlgebraSheafULiftHom_unit.{u, v, w, w'} J A E
  have hsq : cb ≫ g.hom =
      Functor.whiskerRight cs commRingCatULift.{max u v w, w'} := by
    apply (hQb _).injective
    apply Prod.ext
    · have e₁ : bb ≫ cb ≫ g.hom = S'.hom.hom ≫ g.hom := by rw [← Category.assoc, hcb₁]
      have e₂ : S'.hom.hom ≫ g.hom =
          Functor.whiskerRight S.hom.hom commRingCatULift.{max u v w, w'} :=
        congrArg (fun k => k.hom) (Under.w ((freeAlgebraSheafULiftHom.{u, v, w, w'} J A).app E))
      have e₃ : bb ≫ Functor.whiskerRight cs commRingCatULift.{max u v w, w'} =
          Functor.whiskerRight S.hom.hom commRingCatULift.{max u v w, w'} :=
        (Functor.whiskerRight_comp bs cs _).symm.trans
          (congrArg (fun k => Functor.whiskerRight k commRingCatULift.{max u v w, w'}) hbs)
      exact e₁.trans (e₂.trans e₃.symm)
    · have hL : xb ≫ Functor.whiskerRight (cb ≫ g.hom) (forget _) =
          η'.hom ≫ Functor.whiskerRight g.hom (forget _) := by
        rw [Functor.whiskerRight_comp, ← Category.assoc]
        exact congrArg (· ≫ Functor.whiskerRight g.hom (forget _)) hcb₂
      have hR : xb ≫ Functor.whiskerRight
          (Functor.whiskerRight cs commRingCatULift.{max u v w, w'}) (forget _) =
          Functor.whiskerRight (xs ≫ Functor.whiskerRight cs (forget _))
            uliftFunctor.{w', max u v w} := by
        ext U x
        rfl
      have hU := congrArg (fun k => k.hom) hunit
      refine hL.trans (hU.symm.trans (Eq.trans ?_ hR.symm))
      rw [hxs]
      ext U x
      rfl
  have hW : J.W g.hom := MorphismProperty.of_precomp _ cb g.hom hcbW
    (hsq ▸ W_whiskerRight_commRingCatULift.{u, v, w, w'} J cs hcs)
  have : IsIso ((Under.forget _).map ((freeAlgebraSheafULiftHom.{u, v, w, w'} J A).app E)) :=
    (J.W_sheafToPresheaf_map_iff_isIso g).mp hW
  exact isIso_of_reflects_iso _ (Under.forget _)

/-- **The square of free algebra sheaves**: the lift of the free `A`-algebra sheaf on a sheaf of
sets `E` is the free `↑A`-algebra sheaf on the lift of `E`, `↑(A[E]) ≅ ↑A[↑E]`. -/
noncomputable def freeAlgebraSheafULiftIso :
    freeAlgebraSheaf.{v, u, w} J A ⋙
        Under.post (X := A) (sheafCompose J commRingCatULift.{max u v w, w'}) ≅
      sheafCompose J uliftFunctor.{w', max u v w} ⋙
        freeAlgebraSheaf.{v, u, max w w'} J
            ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A) :=
  (NatIso.ofComponents (fun E => asIso ((freeAlgebraSheafULiftHom.{u, v, w, w'} J A).app E))
    (fun g => (freeAlgebraSheafULiftHom.{u, v, w, w'} J A).naturality g)).symm

/-- The square of free algebra sheaves is compatible with the units of the two free–forgetful
adjunctions: with `forgetAlgebraSheafULiftIso` it is a commuting square of adjunctions. -/
theorem freeAlgebraSheafULiftIso_unit (E : Sheaf J (Type (max u v w))) :
    (sheafCompose J uliftFunctor.{w', max u v w}).map
        ((freeAlgebraSheafAdjunction.{v, u, w} J A).unit.app E) ≫
      (forgetAlgebraSheafULiftIso.{u, v, w, w'} J A).inv.app
        ((freeAlgebraSheaf.{v, u, w} J A).obj E) ≫
      (forgetAlgebraSheaf.{v, u, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A)).map
          ((freeAlgebraSheafULiftIso.{u, v, w, w'} J A).hom.app E) =
    (freeAlgebraSheafAdjunction.{v, u, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A)).unit.app
          ((sheafCompose J uliftFunctor.{w', max u v w}).obj E) := by
  have h : (freeAlgebraSheafULiftHom.{u, v, w, w'} J A).app E ≫
      (freeAlgebraSheafULiftIso.{u, v, w, w'} J A).hom.app E = 𝟙 _ :=
    (freeAlgebraSheafULiftIso.{u, v, w, w'} J A).inv_hom_id_app E
  rw [← Category.assoc, freeAlgebraSheafULiftHom_unit, Category.assoc, ← Functor.map_comp, h]
  exact (congrArg (_ ≫ ·) ((forgetAlgebraSheaf.{v, u, max w w'} J
    ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A)).map_id _)).trans (Category.comp_id _)

/-- The comparison of the two free–forgetful comonads induced by the commuting square of
adjunctions. -/
noncomputable def standardResolutionComonadULiftIso :
    (standardResolutionComonad.{v, u, w} J A : Under A ⥤ Under A) ⋙
        Under.post (X := A) (sheafCompose J commRingCatULift.{max u v w, w'}) ≅
      Under.post (X := A) (sheafCompose J commRingCatULift.{max u v w, w'}) ⋙
        (standardResolutionComonad.{v, u, max w w'} J
            ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A) :
          Under ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A) ⥤
            Under ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A)) :=
  Adjunction.comonadSquareIso (F := freeAlgebraSheaf.{v, u, w} J A)
    (U := forgetAlgebraSheaf.{v, u, w} J A)
    (F' := freeAlgebraSheaf.{v, u, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A))
    (U' := forgetAlgebraSheaf.{v, u, max w w'} J
      ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A))
    (L := sheafCompose J uliftFunctor.{w', max u v w})
    (H := Under.post (X := A) (sheafCompose J commRingCatULift.{max u v w, w'}))
    (freeAlgebraSheafULiftIso.{u, v, w, w'} J A) (forgetAlgebraSheafULiftIso.{u, v, w, w'} J A)

/-- The comparison of the two free–forgetful comonads commutes with their counits. -/
lemma standardResolutionComonadULiftIso_counit (X : Under A) :
    (standardResolutionComonadULiftIso.{u, v, w, w'} J A).hom.app X ≫
        (standardResolutionComonad.{v, u, max w w'} J
          ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A)).ε.app
          ((Under.post (X := A) (sheafCompose J commRingCatULift.{max u v w, w'})).obj X) =
      (Under.post (X := A) (sheafCompose J commRingCatULift.{max u v w, w'})).map
        ((standardResolutionComonad.{v, u, w} J A).ε.app X) :=
  Adjunction.comonadSquareIso_counit
    (freeAlgebraSheafAdjunction.{v, u, w} J A)
    (freeAlgebraSheafAdjunction.{v, u, max w w'} J
      ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A))
    (freeAlgebraSheafULiftIso.{u, v, w, w'} J A) (forgetAlgebraSheafULiftIso.{u, v, w, w'} J A)
    (freeAlgebraSheafULiftIso_unit.{u, v, w, w'} J A) X

/-- The comparison of the two free–forgetful comonads commutes with their
comultiplications. -/
lemma standardResolutionComonadULiftIso_comul (X : Under A) :
    (Under.post (X := A) (sheafCompose J commRingCatULift.{max u v w, w'})).map
          ((standardResolutionComonad.{v, u, w} J A).δ.app X) ≫
        (standardResolutionComonadULiftIso.{u, v, w, w'} J A).hom.app
          ((standardResolutionComonad.{v, u, w} J A : Under A ⥤ Under A).obj X) ≫
        (standardResolutionComonad.{v, u, max w w'} J
            ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A) :
            Under ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A) ⥤
              Under ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A)).map
          ((standardResolutionComonadULiftIso.{u, v, w, w'} J A).hom.app X) =
      (standardResolutionComonadULiftIso.{u, v, w, w'} J A).hom.app X ≫
        (standardResolutionComonad.{v, u, max w w'} J
          ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A)).δ.app
          ((Under.post (X := A) (sheafCompose J commRingCatULift.{max u v w, w'})).obj X) :=
  Adjunction.comonadSquareIso_comul
    (freeAlgebraSheafAdjunction.{v, u, w} J A)
    (freeAlgebraSheafAdjunction.{v, u, max w w'} J
      ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A))
    (freeAlgebraSheafULiftIso.{u, v, w, w'} J A) (forgetAlgebraSheafULiftIso.{u, v, w, w'} J A)
    (freeAlgebraSheafULiftIso_unit.{u, v, w, w'} J A) X

end Free

/-! ## The lift of the standard resolution -/

section Resolution

variable {A B : Sheaf J CommRingCat.{max u v w}} (a : A ⟶ B)

/-- The lift of the degree-`n` term of the standard resolution of `a` is the degree-`n` term of
the standard resolution of `↑a`. -/
@[implicit_reducible]
noncomputable def standardResolutionULiftTermIso (n : ℕ) :
    (Under.post (X := A) (sheafCompose J commRingCatULift.{max u v w, w'})).obj
        ((standardResolution.{v, u, w} J a).left.obj (op ⦋n⦌)) ≅
      (standardResolution.{v, u, max w w'} J
          ((sheafCompose J commRingCatULift.{max u v w, w'}).map a)).left.obj (op ⦋n⦌) :=
  Functor.transportObjIso (Under.post (X := A) (sheafCompose J commRingCatULift.{max u v w, w'}))
    (standardResolution_obj.{v, u, w} J a n)
    (standardResolution_obj.{v, u, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).map a) n)
    (Functor.iterateCompIsoObj (standardResolutionComonadULiftIso.{u, v, w, w'} J A) (n + 1) rfl)

/-- The termwise comparison commutes with the face maps. -/
lemma standardResolutionULiftTermIso_delta (n : ℕ) (j : Fin (n + 2)) :
    (Under.post (X := A) (sheafCompose J commRingCatULift.{max u v w, w'})).map
        ((standardResolution.{v, u, w} J a).left.δ j) ≫
        (standardResolutionULiftTermIso.{u, v, w, w'} J a n).hom =
      (standardResolutionULiftTermIso.{u, v, w, w'} J a (n + 1)).hom ≫
        (standardResolution.{v, u, max w w'} J
            ((sheafCompose J commRingCatULift.{max u v w, w'}).map a)).left.δ j :=
  Functor.transportObjIso_naturality (Under.post (X := A)
      (sheafCompose J commRingCatULift.{max u v w, w'}))
    (standardResolution_obj.{v, u, w} J a (n + 1))
    (standardResolution_obj.{v, u, w} J a n)
    (standardResolution_obj.{v, u, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).map a)
        (n + 1))
    (standardResolution_obj.{v, u, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).map a) n)
    (Functor.iterateCompIsoObj (standardResolutionComonadULiftIso.{u, v, w, w'} J A) (n + 2) rfl)
    (Functor.iterateCompIsoObj (standardResolutionComonadULiftIso.{u, v, w, w'} J A) (n + 1) rfl)
    (standardResolution_delta.{u, v, w} J a n j)
    (standardResolution_delta.{u, v, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).map a) n j)
    (Functor.iterateCompIsoObj_godementFace
      (standardResolutionComonadULiftIso.{u, v, w, w'} J A)
      (standardResolutionComonad.{v, u, w} J A).ε
      (standardResolutionComonad.{v, u, max w w'} J
          ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A)).ε
      (standardResolutionComonadULiftIso_counit.{u, v, w, w'} J A) (n + 1) j rfl)

/-- The termwise comparison commutes with the degeneracy maps. -/
lemma standardResolutionULiftTermIso_sigma (n : ℕ) (j : Fin (n + 1)) :
    (Under.post (X := A) (sheafCompose J commRingCatULift.{max u v w, w'})).map
        ((standardResolution.{v, u, w} J a).left.σ j) ≫
        (standardResolutionULiftTermIso.{u, v, w, w'} J a (n + 1)).hom =
      (standardResolutionULiftTermIso.{u, v, w, w'} J a n).hom ≫
        (standardResolution.{v, u, max w w'} J
            ((sheafCompose J commRingCatULift.{max u v w, w'}).map a)).left.σ j :=
  Functor.transportObjIso_naturality (Under.post (X := A)
      (sheafCompose J commRingCatULift.{max u v w, w'}))
    (standardResolution_obj.{v, u, w} J a n)
    (standardResolution_obj.{v, u, w} J a (n + 1))
    (standardResolution_obj.{v, u, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).map a) n)
    (standardResolution_obj.{v, u, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).map a)
        (n + 1))
    (Functor.iterateCompIsoObj (standardResolutionComonadULiftIso.{u, v, w, w'} J A) (n + 1) rfl)
    (Functor.iterateCompIsoObj (standardResolutionComonadULiftIso.{u, v, w, w'} J A) (n + 2) rfl)
    (standardResolution_sigma.{u, v, w} J a n j)
    (standardResolution_sigma.{u, v, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).map a) n j)
    (Functor.iterateCompIsoObj_godementDegeneracy
      (standardResolutionComonadULiftIso.{u, v, w, w'} J A)
      (standardResolutionComonad.{v, u, w} J A).δ
      (standardResolutionComonad.{v, u, max w w'} J
          ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A)).δ
      (standardResolutionComonadULiftIso_comul.{u, v, w, w'} J A) n j rfl)

/-- **The lift of the standard resolution of `a` is the standard resolution of `↑a`**, as
simplicial sheaves of `↑A`-algebras. -/
noncomputable def standardResolutionULiftIso :
    (standardResolution.{v, u, w} J a).left ⋙ Under.post (X := A)
        (sheafCompose J commRingCatULift.{max u v w, w'}) ≅
      (standardResolution.{v, u, max w w'} J
          ((sheafCompose J commRingCatULift.{max u v w, w'}).map a)).left :=
  SimplicialObject.isoCompOfFacesAndDegeneracies
    (Under.post (X := A) (sheafCompose J commRingCatULift.{max u v w, w'}))
    (standardResolution.{v, u, w} J a).left
    (standardResolution.{v, u, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).map a)).left
    (standardResolutionULiftTermIso.{u, v, w, w'} J a)
    (standardResolutionULiftTermIso_delta.{u, v, w, w'} J a)
    (standardResolutionULiftTermIso_sigma.{u, v, w, w'} J a)

/-- The components of the simplicial comparison are the termwise comparisons. -/
lemma standardResolutionULiftIso_hom_app (n : ℕ) :
    (standardResolutionULiftIso.{u, v, w, w'} J a).hom.app (op ⦋n⦌) =
      (standardResolutionULiftTermIso.{u, v, w, w'} J a n).hom :=
  rfl

/-- In degree zero the termwise comparison carries the augmentation of the standard resolution of
`↑a` to the lift of the augmentation of the standard resolution of `a`. -/
lemma standardResolutionULiftTermIso_augmentation_zero :
    (standardResolutionULiftTermIso.{u, v, w, w'} J a 0).hom ≫
        (standardResolution.{v, u, max w w'} J
            ((sheafCompose J commRingCatULift.{max u v w, w'}).map a)).hom.app (op ⦋0⦌) =
      (Under.post (X := A) (sheafCompose J commRingCatULift.{max u v w, w'})).map
          ((standardResolution.{v, u, w} J a).hom.app (op ⦋0⦌)) ≫ 𝟙 _ :=
  Functor.transportObjIso_hom_comp_counit
    (standardResolutionComonadULiftIso.{u, v, w, w'} J A)
    (standardResolutionComonad.{v, u, w} J A).ε
    (standardResolutionComonad.{v, u, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A)).ε
    (standardResolutionComonadULiftIso_counit.{u, v, w, w'} J A)
    (standardResolution_obj.{v, u, w} J a 0)
    (standardResolution_obj.{v, u, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).map a) 0) rfl
    (standardResolution_augmentation_app_zero.{u, v, w} J a)
    (standardResolution_augmentation_app_zero.{u, v, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).map a)) rfl

/-- The simplicial comparison of the standard resolutions is compatible with their augmentations
in every degree. -/
lemma standardResolutionULiftIso_hom_app_comp_augmentation (n : ℕ) :
    (standardResolutionULiftIso.{u, v, w, w'} J a).hom.app (op ⦋n⦌) ≫
        (standardResolution.{v, u, max w w'} J
            ((sheafCompose J commRingCatULift.{max u v w, w'}).map a)).hom.app (op ⦋n⦌) =
      (Under.post (X := A) (sheafCompose J commRingCatULift.{max u v w, w'})).map
          ((standardResolution.{v, u, w} J a).hom.app (op ⦋n⦌)) := by
  refine (SimplicialObject.hom_comp_toConst_of_zero
    (SimplicialObject.mapToConst (Under.post (X := A)
        (sheafCompose J commRingCatULift.{max u v w, w'}))
      (standardResolution.{v, u, w} J a).hom)
    (standardResolution.{v, u, max w w'} J
        ((sheafCompose J commRingCatULift.{max u v w, w'}).map a)).hom
    (standardResolutionULiftIso.{u, v, w, w'} J a) (𝟙 _) ?_ n).trans (Category.comp_id _)
  rw [standardResolutionULiftIso_hom_app.{u, v, w, w'}]
  exact standardResolutionULiftTermIso_augmentation_zero.{u, v, w, w'} J a

/-- The comparison of the standard resolutions of `a` and of `↑a` in a simplicial degree, as an
isomorphism of sheaves of commutative rings `↑P_n ≅ P_n(↑a)`. -/
noncomputable def resolutionULiftIso (n : SimplexCategoryᵒᵖ) :
    (sheafCompose J commRingCatULift.{max u v w, w'}).obj (resolutionTerm.{u, v, w} J a n) ≅
        resolutionTerm.{u, v, max w w'} J
            ((sheafCompose J commRingCatULift.{max u v w, w'}).map a) n :=
  (Under.forget ((sheafCompose J commRingCatULift.{max u v w, w'}).obj A)).mapIso
      ((standardResolutionULiftIso.{u, v, w, w'} J a).app n)

/-- The degreewise comparison of the standard resolutions is a map of `↑A`-algebras. -/
lemma resolutionULiftIso_base (n : SimplexCategoryᵒᵖ) :
    (sheafCompose J commRingCatULift.{max u v w, w'}).map (resolutionBase.{u, v, w} J a n) ≫
        (resolutionULiftIso.{u, v, w, w'} J a n).hom =
      resolutionBase.{u, v, max w w'} J
          ((sheafCompose J commRingCatULift.{max u v w, w'}).map a) n :=
  Under.w ((standardResolutionULiftIso.{u, v, w, w'} J a).hom.app n)

/-- The degreewise comparison of the standard resolutions is compatible with the
augmentations. -/
lemma resolutionULiftIso_augmentation (n : SimplexCategoryᵒᵖ) :
    (resolutionULiftIso.{u, v, w, w'} J a n).hom ≫
        resolutionAugmentation.{u, v, max w w'} J
            ((sheafCompose J commRingCatULift.{max u v w, w'}).map a) n =
      (sheafCompose J commRingCatULift.{max u v w, w'}).map
          (resolutionAugmentation.{u, v, w} J a n) :=
  congrArg (fun k ↦ k.right)
    (standardResolutionULiftIso_hom_app_comp_augmentation.{u, v, w, w'} J a n.unop.len)

/-- The degreewise comparison of the standard resolutions is natural in the simplicial
variable. -/
lemma resolutionULiftIso_naturality {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) :
    (sheafCompose J commRingCatULift.{max u v w, w'}).map
        ((standardResolution.{v, u, w} J a).left.map g).right ≫
        (resolutionULiftIso.{u, v, w, w'} J a j).hom =
      (resolutionULiftIso.{u, v, w, w'} J a i).hom ≫
        ((standardResolution.{v, u, max w w'} J
            ((sheafCompose J commRingCatULift.{max u v w, w'}).map a)).left.map g).right :=
  congrArg (fun k ↦ k.right) ((standardResolutionULiftIso.{u, v, w, w'} J a).hom.naturality g)

end Resolution

end CategoryTheory.Sheaf

end
