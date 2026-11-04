module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroIntegralDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionFrobeniusTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionFrobeniusTraceInvariance
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionTwistCompat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DerivedTwistComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusAdditivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportOpenRestriction

/-!
# `RΓ` of the geometric fibre along an integral morphism, Frobenius-equivariantly

Let `i : Z ⟶ Y` be an integral morphism of schemes over a finite field `k` (a closed immersion,
or a finite morphism) and let `k̄` be an extension of `k`.  For a bounded below complex `M` of
sheaves of `Λ`-modules on `Z_étale`,

`RΓ(Z_k̄, M|_{Z_k̄}) ≅ RΓ(Y_k̄, (i_* M)|_{Y_k̄})`,

naturally in `M` and compatibly with the canonical geometric Frobenius endomorphisms of the two
sides: the base change map `(i_* M)|_{Y_k̄} ⟶ (i_k̄)_*(M|_{Z_k̄})` is an isomorphism (integral base
change), it carries the Frobenius twist of `Y` to `(i_k̄)_*` of that of `Z`, and the direct image
along the integral morphism `i_k̄` is exact and preserves injectives, so that
`RΓ(Y_k̄, R(i_k̄)_* -) = RΓ(Z_k̄, -)` (`CategoryTheory.Functor.twistTransportIso`).

For a closed immersion `i : Z ⟶ X` and a compactification `j : X ⟶ X̄` this gives the closed half
of the excision step in the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Deligne, Weil II 3.3) to curves:

`RΓ_c(Z_k̄, K) ≅ RΓ_c(X_k̄, i_* K)`,

for the compactification of `Z` induced by `j`
(`AlgebraicGeometry.CompactificationOf.restrictClosed`), Frobenius-equivariantly and naturally in
`K`: `j_! i_* ≅ ι_* t_!` for the closure `ι : Z̄ ⟶ X̄` of `Z` and the open immersion `t : Z ⟶ Z̄`.

## Main definitions

* `Stacks.EtaleCohomology.frobeniusRestrictionDirectImageIso`:
  `RΓ(Z_k̄, M|_{Z_k̄}) ≅ RΓ(Y_k̄, (i_* M)|_{Y_k̄})`.
* `Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyRestrictClosedIso`:
  `RΓ_c(Z_k̄, K) ≅ RΓ_c(X_k̄, i_* K)`.

## Main results

* `Stacks.EtaleCohomology.frobeniusRestrictionDirectImageIso_hom_frobenius`,
  `Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyRestrictClosedIso_hom_frobenius`: the
  identifications commute with the canonical Frobenius.
* `Stacks.EtaleCohomology.frobeniusRestrictionDirectImageIso_hom_naturality`,
  `Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyRestrictClosedIso_hom_naturality`: they
  are natural in the complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u u₁ v₁

namespace CategoryTheory.Functor

section BaseChangeTwist

attribute [local instance] HasDerivedCategory.standard

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  {C C' D : Type u₁} [Category.{v₁} C] [Category.{v₁} C'] [Category.{v₁} D] [Abelian C]
  [Abelian C'] [Abelian D] [EnoughInjectives C] [EnoughInjectives D] {E : Type*} [Category* E]
  [Abelian E]
  (P : C ⥤ C) (F₁ : C ⥤ D) (F₂ : D ⥤ E) (P' : C' ⥤ C') (G : C' ⥤ C) (I : A ⥤ B) (g : B ⥤ C)
  (g' : A ⥤ C') [P.Additive] [F₁.Additive] [F₂.Additive] [P'.Additive] [G.Additive]
  [I.Additive] [g.Additive] [g'.Additive] [P.PreservesInjectiveObjects]
  (θ : P ⋙ F₁ ≅ F₁) (ρ : P' ⋙ G ⟶ G ⋙ P) (β : I ⋙ g ≅ g' ⋙ G) (tw : g ⟶ g ⋙ P)
  (tw' : g' ⟶ g' ⋙ P')

omit [EnoughInjectives C] in
/-- The base change isomorphism `β : I ⋙ g ≅ g' ⋙ G`, degreewise, is natural in the complex. -/
lemma baseChangePlusIso_hom_naturality {M M' : CochainComplex.Plus A} (φ : M ⟶ M') :
    g.mapCochainComplexPlus.map (I.mapCochainComplexPlus.map φ) ≫
        (baseChangePlusIso G I g g' β M').hom =
      (baseChangePlusIso G I g g' β M).hom ≫
        G.mapCochainComplexPlus.map (g'.mapCochainComplexPlus.map φ) := by
  ext n : 2
  exact β.hom.naturality (φ.hom.f n)

/-- **A base change isomorphism intertwines the twisted endomorphisms.**  If `β : I ⋙ g ≅ g' ⋙ G`
carries the twist `tw : g ⟶ g ⋙ P` to the twist `G(tw') ≫ ρ`, then on `RF₂(RF₁(-))` the
isomorphism induced by `β` carries the derived twisted endomorphism attached to `tw` to the one
attached to `G(tw') ≫ ρ`. -/
lemma derivedTwistEndo_baseChangePlusIso
    (hβ : ∀ X, β.hom.app X ≫ G.map (tw'.app X) ≫ ρ.app (g'.obj X) =
      tw.app (I.obj X) ≫ P.map (β.hom.app X)) (M : CochainComplex.Plus A) :
    derivedTwistEndo P F₁ F₂ θ (g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M))
        (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex tw (ComplexShape.up ℤ)).app
          (I.mapCochainComplexPlus.obj M).obj)) ≫
      F₂.rightDerivedFunctorPlus.map (F₁.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map (baseChangePlusIso G I g g' β M).hom)) =
    F₂.rightDerivedFunctorPlus.map (F₁.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map (baseChangePlusIso G I g g' β M).hom)) ≫
      derivedTwistEndo P F₁ F₂ θ (G.mapCochainComplexPlus.obj (g'.mapCochainComplexPlus.obj M))
        (G.mapCochainComplexPlus.map (ObjectProperty.homMk (X := g'.mapCochainComplexPlus.obj M)
          (Y := P'.mapCochainComplexPlus.obj (g'.mapCochainComplexPlus.obj M))
          ((NatTrans.mapHomologicalComplex tw' (ComplexShape.up ℤ)).app M.obj)) ≫
          ObjectProperty.homMk
            (X := G.mapCochainComplexPlus.obj (P'.mapCochainComplexPlus.obj
              (g'.mapCochainComplexPlus.obj M)))
            (Y := P.mapCochainComplexPlus.obj (G.mapCochainComplexPlus.obj
              (g'.mapCochainComplexPlus.obj M)))
            ((NatTrans.mapHomologicalComplex ρ _).app (g'.mapCochainComplexPlus.obj M).obj)) := by
  refine derivedTwistEndo_naturality P F₁ F₂ θ _ _ _ (congrArg DerivedCategory.Plus.Q.map ?_)
  ext n : 2
  exact (hβ (M.obj.X n)).symm

end BaseChangeTwist

end CategoryTheory.Functor

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Integral

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {Z Y : Over (Spec (.of k))}
  (i : Z ⟶ Y) [IsIntegralHom i.left] (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The base change map `(i_* M)|_{Y_k̄} ≅ (i_k̄)_*(M|_{Z_k̄})` of an integral morphism over `k`,
degreewise on a bounded below complex. -/
def integralFieldBaseChangeComplexIso (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left)) :
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj M) ≅
      (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar)).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj
          M) :=
  haveI := isIso_etaleModuleBaseChange_fieldBaseChangeMap_of_isIntegralHom Λ i kbar
  Functor.baseChangePlusIso (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar))
    (etaleModuleDirectImage.{u, 0} Λ i.left)
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar))
    (asIso (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar) (fieldBaseChangeProj Y kbar)
      (fieldBaseChangeProj Z kbar) (fieldBaseChangeMap_comp_fst i kbar))) M

/-- The base change map is natural in the complex. -/
lemma integralFieldBaseChangeComplexIso_hom_naturality
    {M M' : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left)} (φ : M ⟶ M') :
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map
        ((etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.map φ) ≫
      (integralFieldBaseChangeComplexIso Λ i kbar M').hom =
    (integralFieldBaseChangeComplexIso Λ i kbar M).hom ≫
      (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar)).mapCochainComplexPlus.map
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.map
          φ) := by
  have := isIso_etaleModuleBaseChange_fieldBaseChangeMap_of_isIntegralHom Λ i kbar
  exact Functor.baseChangePlusIso_hom_naturality _ _ _ _ _ φ

omit [Fintype k] in
/-- The base change to `k̄` of an integral morphism over `k` is integral. -/
lemma isIntegralHom_fieldBaseChangeMap : IsIntegralHom (fieldBaseChangeMap i kbar) :=
  MorphismProperty.of_isPullback (isPullback_fieldBaseChangeMap i kbar).flip ‹_›

/-- The direct image along an integral morphism preserves finite limits and colimits. -/
private lemma preservesFiniteLimits_and_colimits_directImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] :
    PreservesFiniteLimits (etaleModuleDirectImage.{u, 0} Λ f) ∧
      PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} Λ f) :=
  (exactFunctor_iff _).1 (etaleModuleDirectImage_exact_of_isIntegralHom Λ f)

/-- **`RΓ(Z_k̄, M|_{Z_k̄}) ≅ RΓ(Y_k̄, (i_* M)|_{Y_k̄})`** for an integral morphism `i : Z ⟶ Y` over
`k`: `RΓ(Z_k̄, -) = RΓ(Y_k̄, (i_k̄)_* -)`, the direct image `(i_k̄)_*` being exact and preserving
injectives, followed by the inverse of the base change isomorphism. -/
def frobeniusRestrictionDirectImageIso (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left)) :
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Z.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Z kbar M)) ≅
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar
            ((etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj M))) :=
  haveI := isIntegralHom_fieldBaseChangeMap i kbar
  haveI : PreservesFiniteLimits (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar)) :=
    ((exactFunctor_iff _).1
      (etaleModuleDirectImage_exact_of_isIntegralHom Λ (fieldBaseChangeMap i kbar))).1
  haveI : PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar)) :=
    ((exactFunctor_iff _).1
      (etaleModuleDirectImage_exact_of_isIntegralHom Λ (fieldBaseChangeMap i kbar))).2
  Functor.twistTransportIso
      (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
      (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
      (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar))
      (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Z.hom (specAlgebraMap k kbar)))
      (etaleModuleDirectImageComp.{u, 0} Λ (fieldBaseChangeMap i kbar)
        (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
        (fieldBaseChangeMap_comp_snd i kbar).symm)
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj
        M) ≪≫
    ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).mapIso
        (DerivedCategory.Plus.Q.mapIso (integralFieldBaseChangeComplexIso Λ i kbar M)))).symm

/-- A square with isomorphisms as vertical sides, read backwards. -/
public lemma comp_inv_eq_inv_comp_of_hom_comm {D : Type*} [Category* D] {X Y X' Y' : D}
    (e : X ≅ Y) (e' : X' ≅ Y') (a : Y ⟶ Y') (b : X ⟶ X') (h : b ≫ e'.hom = e.hom ≫ a) :
    a ≫ e'.inv = e.inv ≫ b := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- Pasting a naturality square with a square of functorial maps. -/
public lemma comp_comp_eq_comp_comp_of_squares {D : Type*} [Category* D]
    {A₀ A₁ B₀ B₁ C₀ C₁ : D} (a : A₀ ⟶ A₁)
    (e₀ : A₀ ⟶ B₀) (e₁ : A₁ ⟶ B₁) (d : B₀ ⟶ B₁) (b₀ : B₀ ⟶ C₀) (b₁ : B₁ ⟶ C₁) (c : C₀ ⟶ C₁)
    (h₁ : a ≫ e₁ = e₀ ≫ d) (h₃ : d ≫ b₁ = b₀ ≫ c) : a ≫ e₁ ≫ b₁ = (e₀ ≫ b₀) ≫ c := by
  rw [reassoc_of% h₁, h₃, Category.assoc]

/-- **The identification is natural in the complex.** -/
theorem frobeniusRestrictionDirectImageIso_hom_naturality
    {M M' : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left)} (φ : M ⟶ M') :
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Z.hom (specAlgebraMap k kbar))).map
          ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Z kbar).map φ)) ≫
      (frobeniusRestrictionDirectImageIso Λ i kbar M').hom =
    (frobeniusRestrictionDirectImageIso Λ i kbar M).hom ≫
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
          ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar).map
            ((etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.map φ))) := by
  have := isIntegralHom_fieldBaseChangeMap i kbar
  obtain ⟨_, _⟩ := preservesFiniteLimits_and_colimits_directImage Λ (fieldBaseChangeMap i kbar)
  have hT := Functor.twistTransportIso_hom_naturality
    (F₁ := etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (F₂ := etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
    (Φ := etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar))
    (F₁' := etaleModuleDirectImage.{u, 0} Λ (pullback.snd Z.hom (specAlgebraMap k kbar)))
    (κ := etaleModuleDirectImageComp.{u, 0} Λ (fieldBaseChangeMap i kbar)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (fieldBaseChangeMap_comp_snd i kbar).symm)
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.map φ)
  have hB := integralFieldBaseChangeComplexIso_hom_naturality Λ i kbar φ
  refine comp_comp_eq_comp_comp_of_squares _ _ _ _ _ _ _ hT ((Iso.comp_inv_eq _).2 ?_)
  rw [Category.assoc]
  refine (Iso.eq_inv_comp _).2 ?_
  symm
  show (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map _ ≫
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map _ =
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map _ ≫
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  simp only [Functor.mapIso_hom, ← Functor.map_comp]
  dsimp only [fieldBaseChangeRestrictionFunctor, Functor.comp_map]
  rw [← Functor.map_comp, hB]

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The identification `(π̄_Z)_* ⋙ (i_k̄)_* ≅ (i_k̄)_* ⋙ (π̄_Y)_*` of the direct images along the
two sides of `π̄_Z ≫ i_k̄ = i_k̄ ≫ π̄_Y`. -/
abbrev fieldBaseChangeMapFrobeniusTwistIso :
    etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Z kbar p q hcard) ⋙
        etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar) ≅
      etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar) ⋙
        etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard) :=
  etaleModuleDirectImageComp.{u, 0} Λ _ _ _ rfl ≪≫
    (etaleModuleDirectImageComp.{u, 0} Λ _ _ _
      (geometricFrobeniusBaseChange_comp_fieldBaseChangeMap i p q hcard kbar)).symm

omit [IsIntegralHom i.left] in
/-- The Frobenius base change twist `M|_{Z_k̄} ⟶ (π̄_Z)_*(M|_{Z_k̄})`, as a morphism of bounded
below complexes. -/
abbrev zTwist (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left)) :
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj M ⟶
      (etaleModuleDirectImage.{u, 0} Λ
          (geometricFrobeniusBaseChange Z kbar p q hcard)).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj
          M) :=
  ObjectProperty.homMk ((NatTrans.mapHomologicalComplex
    (frobeniusBaseChangeTwist.{u, 0} Λ Z kbar p q hcard) (ComplexShape.up ℤ)).app M.obj)

/-- **The identification `RΓ(Z_k̄, M|_{Z_k̄}) ≅ RΓ(Y_k̄, (i_* M)|_{Y_k̄})` commutes with the
canonical geometric Frobenius.** -/
theorem frobeniusRestrictionDirectImageIso_hom_frobenius
    (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left)) :
    frobeniusRestrictionCohomologyEndo.{u, 0} Λ Z kbar p q hcard M ≫
        (frobeniusRestrictionDirectImageIso Λ i kbar M).hom =
      (frobeniusRestrictionDirectImageIso Λ i kbar M).hom ≫
        frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard
          ((etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj M) := by
  have := isIntegralHom_fieldBaseChangeMap i kbar
  obtain ⟨_, _⟩ := preservesFiniteLimits_and_colimits_directImage Λ (fieldBaseChangeMap i kbar)
  rw [frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo,
    frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo]
  have hT := Functor.derivedTwistEndo_transport
    (P := etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
    (F₁ := etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (F₂ := etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
    (Φ := etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar))
    (F₁' := etaleModuleDirectImage.{u, 0} Λ (pullback.snd Z.hom (specAlgebraMap k kbar)))
    (κ := etaleModuleDirectImageComp.{u, 0} Λ (fieldBaseChangeMap i kbar)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (fieldBaseChangeMap_comp_snd i kbar).symm)
    (P' := etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Z kbar p q hcard))
    (θ := etaleModuleDirectImageComp.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
    (θ' := etaleModuleDirectImageComp.{u, 0} Λ (geometricFrobeniusBaseChange Z kbar p q hcard)
      (pullback.snd Z.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Z kbar p q hcard).symm)
    (ρ := fieldBaseChangeMapFrobeniusTwistIso Λ i kbar p q hcard)
    (fun X => directImageTwistTransfer_compat Λ (fieldBaseChangeMap i kbar)
      (geometricFrobeniusBaseChange Z kbar p q hcard)
      (geometricFrobeniusBaseChange Y kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_fieldBaseChangeMap i p q hcard kbar)
      (fieldBaseChangeMap_comp_snd i kbar).symm
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm
      (geometricFrobeniusBaseChange_comp_toBase Z kbar p q hcard).symm X)
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj M)
    (zTwist Λ kbar p q hcard M)
  have := isIso_etaleModuleBaseChange_fieldBaseChangeMap_of_isIntegralHom Λ i kbar
  have hN := Functor.derivedTwistEndo_baseChangePlusIso
    (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
    (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
    (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Z kbar p q hcard))
    (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar))
    (etaleModuleDirectImage.{u, 0} Λ i.left)
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar))
    (etaleModuleDirectImageComp.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
    (fieldBaseChangeMapFrobeniusTwistIso Λ i kbar p q hcard).hom
    (asIso (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar) (fieldBaseChangeProj Y kbar)
      (fieldBaseChangeProj Z kbar) (fieldBaseChangeMap_comp_fst i kbar)))
    (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard)
    (frobeniusBaseChangeTwist.{u, 0} Λ Z kbar p q hcard)
    (etaleModuleBaseChange_comp_frobeniusBaseChangeTwist Λ i p q hcard kbar) M
  exact comp_comp_eq_comp_comp_of_squares _ _ _ _ _ _ _ hT
    (comp_inv_eq_inv_comp_of_hom_comm _ _ _ _ hN)

end Integral

/-! ### The closed half of excision for `RΓ_c` -/

section Closed

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [QuasiCompact f] (j : CompactificationOf (Over.mk f)) {Z : Scheme.{u}}
  (i : Z ⟶ X) [IsClosedImmersion i] (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The closure `ι : Z̄ ⟶ X̄` of `Z` in the compactification, as a morphism over `k`. -/
abbrev restrictClosedOverHom :
    Over.mk (j.restrictClosed i).toBase ⟶ Over.mk j.toBase :=
  Over.homMk (j.closedSpaceι i) rfl

/-- The closure `ι : Z̄ ⟶ X̄` of `Z` in the compactification is an integral morphism. -/
instance : IsIntegralHom (restrictClosedOverHom f j i).left :=
  (inferInstance : IsIntegralHom (j.closedSpaceι i))

/-- `j_! i_* K ≅ ι_* t_! K`, degreewise on a bounded below complex, for the closure
`ι : Z̄ ⟶ X̄` of `Z` and the open immersion `t : Z ⟶ Z̄`. -/
def extensionByZeroDirectImagePlusIso (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z)) :
    (etaleModuleDirectImage.{u, 0} Λ (restrictClosedOverHom f j i).left).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, 0} Λ
          (j.restrictClosed i).immersion).mapCochainComplexPlus.obj K) ≅
      (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ i).mapCochainComplexPlus.obj K) :=
  ObjectProperty.isoMk _ ((NatIso.mapHomologicalComplex
    (etaleModuleExtensionByZeroDirectImageIso.{u, 0} Λ i (j.closedImmersion i).toImage j.immersion
      (j.closedSpaceι i) (j.isPullback_restrictClosed i)).symm _).app K.obj)

/-- **`RΓ_c(Z_k̄, K) ≅ RΓ_c(X_k̄, i_* K)`** for a closed immersion `i : Z ⟶ X` and the
compactification of `Z` induced by a compactification `j` of `X`. -/
def compactSupportFrobeniusCohomologyRestrictClosedIso
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z)) :
    compactSupportFrobeniusCohomology.{u, 0} Λ (i ≫ f) (j.restrictClosed i) kbar K ≅
      compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
        ((etaleModuleDirectImage.{u, 0} Λ i).mapCochainComplexPlus.obj K) :=
  frobeniusRestrictionDirectImageIso Λ (restrictClosedOverHom f j i) kbar
      ((etaleModuleExtensionByZero.{u, 0} Λ
        (j.restrictClosed i).immersion).mapCochainComplexPlus.obj K) ≪≫
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).mapIso
        ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk j.toBase) kbar).mapIso
          (extensionByZeroDirectImagePlusIso Λ f j i K)))

/-- **The identification `RΓ_c(Z_k̄, K) ≅ RΓ_c(X_k̄, i_* K)` is natural in `K`.** -/
theorem compactSupportFrobeniusCohomologyRestrictClosedIso_hom_naturality
    {K K' : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z)} (φ : K ⟶ K') :
    (compactSupportFrobeniusFunctor.{u, 0} Λ (i ≫ f) (j.restrictClosed i) kbar).map φ ≫
        (compactSupportFrobeniusCohomologyRestrictClosedIso Λ f j i kbar K').hom =
      (compactSupportFrobeniusCohomologyRestrictClosedIso Λ f j i kbar K).hom ≫
        (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
          ((etaleModuleDirectImage.{u, 0} Λ i).mapCochainComplexPlus.map φ) := by
  have h₁ := frobeniusRestrictionDirectImageIso_hom_naturality Λ (restrictClosedOverHom f j i) kbar
    ((etaleModuleExtensionByZero.{u, 0} Λ (j.restrictClosed i).immersion).mapCochainComplexPlus.map
      φ)
  have h₂ :
      (etaleModuleDirectImage.{u, 0} Λ (restrictClosedOverHom f j i).left).mapCochainComplexPlus.map
        ((etaleModuleExtensionByZero.{u, 0} Λ
          (j.restrictClosed i).immersion).mapCochainComplexPlus.map φ) ≫
          (extensionByZeroDirectImagePlusIso Λ f j i K').hom =
      (extensionByZeroDirectImagePlusIso Λ f j i K).hom ≫
        (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.map
          ((etaleModuleDirectImage.{u, 0} Λ i).mapCochainComplexPlus.map φ) := by
    ext n : 2
    exact (etaleModuleExtensionByZeroDirectImageIso.{u, 0} Λ i (j.closedImmersion i).toImage
      j.immersion (j.closedSpaceι i) (j.isPullback_restrictClosed i)).inv.naturality (φ.hom.f n)
  have h₃ := congrArg (fun t => (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
    ((etaleModuleDerivedDirectImage.{u, 0} Λ
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).map
        ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk j.toBase) kbar).map t))) h₂
  simp only [Functor.map_comp] at h₃
  exact comp_comp_eq_comp_comp_of_squares _ _ _ _ _ _ _ h₁ h₃

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The identification `RΓ_c(Z_k̄, K) ≅ RΓ_c(X_k̄, i_* K)` commutes with the canonical geometric
Frobenius.** -/
theorem compactSupportFrobeniusCohomologyRestrictClosedIso_hom_frobenius
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z)) :
    canonicalCompactSupportFrobenius.{u, 0} Λ (i ≫ f) (j.restrictClosed i) kbar p q hcard K ≫
        (compactSupportFrobeniusCohomologyRestrictClosedIso Λ f j i kbar K).hom =
      (compactSupportFrobeniusCohomologyRestrictClosedIso Λ f j i kbar K).hom ≫
        canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q hcard
          ((etaleModuleDirectImage.{u, 0} Λ i).mapCochainComplexPlus.obj K) := by
  have h₁ := frobeniusRestrictionDirectImageIso_hom_frobenius Λ (restrictClosedOverHom f j i) kbar
    p q hcard
    ((etaleModuleExtensionByZero.{u, 0} Λ (j.restrictClosed i).immersion).mapCochainComplexPlus.obj
      K)
  have h₂ := frobeniusRestrictionCohomologyEndo_naturality (Λ := Λ) (Over.mk j.toBase) kbar p q
    hcard (extensionByZeroDirectImagePlusIso Λ f j i K).hom
  exact comp_comp_eq_comp_comp_of_squares _ _ _ _ _ _ _ h₁ h₂.symm

end Closed

end Stacks.EtaleCohomology

end
