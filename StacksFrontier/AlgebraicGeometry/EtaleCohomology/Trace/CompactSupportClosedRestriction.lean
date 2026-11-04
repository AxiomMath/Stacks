module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionFrobeniusTraceInvariance
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusPowerEndo

/-!
# `RΓ_c` of a closed subscheme, Frobenius-equivariantly

Let `j : X ⟶ X̄` be a compactification of `X` over a finite field `k` and `i : Z ⟶ X` a closed
immersion.  The scheme-theoretic image `Z̄` of `j ∘ i` is a closed subscheme `ι : Z̄ ⟶ X̄`, and the
open immersion `t : Z ⟶ Z̄` is a compactification of `Z`
(`AlgebraicGeometry.CompactificationOf.restrictClosed`); the square formed by `i`, `t`, `j` and `ι`
is cartesian (`AlgebraicGeometry.CompactificationOf.isPullback_restrictClosed`), so
`j_! ∘ i_* ≅ ι_* ∘ t_!` (`Stacks.EtaleCohomology.etaleModuleExtensionByZeroDirectImageIso`).  The
base change map `(ι_* M)|_{X̄_k̄} ⟶ (ι_k̄)_*(M|_{Z̄_k̄})` along the closed immersion `ι` is an
isomorphism (`Stacks.EtaleCohomology.isIso_etaleModuleBaseChange_fieldBaseChangeMap`), and
`(ι_k̄)_*` is exact, so `RΓ(X̄_k̄, (ι_k̄)_* N) = RΓ(Z̄_k̄, N)`.  Hence

`RΓ_c(Z_k̄, L) = RΓ(Z̄_k̄, (t_! L)|_{Z̄_k̄}) ≅ RΓ(X̄_k̄, (ι_* t_! L)|_{X̄_k̄})
  ≅ RΓ(X̄_k̄, (j_! i_* L)|_{X̄_k̄}) = RΓ_c(X_k̄, i_* L)`.

The base change map carries the canonical Frobenius twist of `X̄` to that of `Z̄`
(`Stacks.EtaleCohomology.etaleModuleBaseChange_comp_frobeniusBaseChangeTwist`), so the
identification commutes with the canonical geometric Frobenius `π^*` of both sides.

## Main definitions

* `CategoryTheory.Functor.baseChangeTwistTransportIso`: the abstract comparison
  `RF₂(RF₁'(g' M)) ≅ RF₂(RF₁(g(I M)))` attached to an exact functor `G` preserving injectives and a
  base change isomorphism `I ⋙ g ≅ g' ⋙ G`.
* `Stacks.EtaleCohomology.frobeniusRestrictionCohomologyDirectImageIso`: for a closed immersion
  `ι : Z̄ ⟶ Y` over `k`, `RΓ(Z̄_k̄, M|_{Z̄_k̄}) ≅ RΓ(Y_k̄, (ι_* M)|_{Y_k̄})`.
* `Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyClosedImmersionIso`:
  `RΓ_c(Z_k̄, L) ≅ RΓ_c(X_k̄, i_* L)` for the induced compactification of `Z`.

## Main results

* `CategoryTheory.Functor.derivedTwistEndo_comp_baseChangeTwistTransportIso_hom`: the abstract
  comparison intertwines the twisted endomorphisms.
* `CategoryTheory.Functor.derivedTwistEndo_mapCochainComplexPlus_naturality`: the endomorphism
  induced by a natural twist is natural in the complex.
* `Stacks.EtaleCohomology.frobeniusRestrictionCohomologyDirectImageIso_hom_frobenius` and
  `Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyClosedImmersionIso_hom_frobenius`: the
  identifications commute with the canonical Frobenius.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r u₁ v₁

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Functor

/-! ### Transport of a twisted endomorphism along a base change isomorphism -/

section BaseChangeTransport

/-- Conjugating an intertwined endomorphism by a composite with an inverse. -/
private lemma comp_inv_of_intertwine {D : Type*} [Category* D] {X₀ X₁ X₂ : D} (t : X₀ ⟶ X₁)
    (r : X₂ ≅ X₁) (a : X₀ ⟶ X₀) (b : X₁ ⟶ X₁) (c : X₂ ⟶ X₂) (h₁ : a ≫ t = t ≫ b)
    (h₂ : c ≫ r.hom = r.hom ≫ b) : a ≫ (t ≫ r.inv) = (t ≫ r.inv) ≫ c := by
  rw [← Category.assoc, h₁, Category.assoc, Category.assoc]
  refine whisker_eq t ?_
  rw [Iso.eq_inv_comp, ← reassoc_of% h₂, Iso.hom_inv_id, Category.comp_id]

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  {C C' D : Type u₁} {E : Type*} [Category.{v₁} C] [Category.{v₁} C'] [Category.{v₁} D]
  [Category* E] [Abelian C] [Abelian C'] [Abelian D] [Abelian E] [EnoughInjectives C]
  [EnoughInjectives C'] [EnoughInjectives D]
  (F₁ : C ⥤ D) (F₂ : D ⥤ E) (G : C' ⥤ C) (F₁' : C' ⥤ D) (I : A ⥤ B) (g : B ⥤ C) (g' : A ⥤ C')
  [F₁.Additive] [F₂.Additive] [G.Additive] [F₁'.Additive] [I.Additive] [g.Additive] [g'.Additive]
  [F₁.PreservesInjectiveObjects] [F₁'.PreservesInjectiveObjects] [G.PreservesInjectiveObjects]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (γ : G ⋙ F₁ ≅ F₁') (β : I ⋙ g ≅ g' ⋙ G)

/-- **The comparison `RF₂(RF₁'(g' M)) ≅ RF₂(RF₁(g(I M)))`** attached to an exact functor `G`
preserving injectives with `γ : G ⋙ F₁ ≅ F₁'` and a base change isomorphism
`β : I ⋙ g ≅ g' ⋙ G`: the transport isomorphism `RF₂(RF₁'(g' M)) ≅ RF₂(RF₁(G(g' M)))` followed by
the inverse of `RF₂ ∘ RF₁` of `β`, degreewise. -/
def baseChangeTwistTransportIso (M : CochainComplex.Plus A) :
    F₂.rightDerivedFunctorPlus.obj (F₁'.rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj (g'.mapCochainComplexPlus.obj M))) ≅
      F₂.rightDerivedFunctorPlus.obj (F₁.rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj
          (g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M)))) :=
  twistTransportIso F₁ F₂ G F₁' γ (g'.mapCochainComplexPlus.obj M) ≪≫
    (F₂.rightDerivedFunctorPlus.mapIso (F₁.rightDerivedFunctorPlus.mapIso
      (DerivedCategory.Plus.Q.mapIso (baseChangePlusIso G I g g' β M)))).symm

variable (P : C ⥤ C) (P' : C' ⥤ C') [P.Additive] [P'.Additive] [P.PreservesInjectiveObjects]
  [P'.PreservesInjectiveObjects] (θ : P ⋙ F₁ ≅ F₁) (θ' : P' ⋙ F₁' ≅ F₁') (ρ : P' ⋙ G ≅ G ⋙ P)
  (tw : g ⟶ g ⋙ P) (tw' : g' ⟶ g' ⋙ P')

/-- **The base change comparison intertwines the twisted endomorphisms.**  If `β` carries the
twist `tw` of `g ∘ I` to `G` of the twist `tw'` of `g'` followed by `ρ : P' ⋙ G ≅ G ⋙ P`, and `γ`,
`ρ` are compatible with `θ`, `θ'`, then the comparison
`RF₂(RF₁'(g' M)) ≅ RF₂(RF₁(g(I M)))` carries the endomorphism induced by `tw'` to the one induced
by `tw`. -/
theorem derivedTwistEndo_comp_baseChangeTwistTransportIso_hom
    (hθ : ∀ X, F₁.map (ρ.hom.app X) ≫ θ.hom.app (G.obj X) ≫ γ.hom.app X =
      γ.hom.app (P'.obj X) ≫ θ'.hom.app X)
    (hβ : ∀ X, β.hom.app X ≫ G.map (tw'.app X) ≫ ρ.hom.app (g'.obj X) =
      tw.app (I.obj X) ≫ P.map (β.hom.app X))
    (M : CochainComplex.Plus A) :
    derivedTwistEndo P' F₁' F₂ θ' (g'.mapCochainComplexPlus.obj M)
        (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex tw' (ComplexShape.up ℤ)).app
          M.obj)) ≫ (baseChangeTwistTransportIso F₁ F₂ G F₁' I g g' γ β M).hom =
      (baseChangeTwistTransportIso F₁ F₂ G F₁' I g g' γ β M).hom ≫
        derivedTwistEndo P F₁ F₂ θ (g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M))
          (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex tw (ComplexShape.up ℤ)).app
            (I.mapCochainComplexPlus.obj M).obj)) := by
  have hT := derivedTwistEndo_transport (P := P) (F₁ := F₁) (F₂ := F₂) (Φ := G) (F₁' := F₁')
    (κ := γ) (P' := P') (θ := θ) (θ' := θ') (ρ := ρ) hθ (g'.mapCochainComplexPlus.obj M)
    (ObjectProperty.homMk (Y := P'.mapCochainComplexPlus.obj (g'.mapCochainComplexPlus.obj M))
      ((NatTrans.mapHomologicalComplex tw' (ComplexShape.up ℤ)).app M.obj))
  have hN := derivedTwistEndo_naturality P F₁ F₂ θ (baseChangePlusIso G I g g' β M).hom
    (ObjectProperty.homMk (Y := P.mapCochainComplexPlus.obj
        (g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M)))
      ((NatTrans.mapHomologicalComplex tw (ComplexShape.up ℤ)).app
        (I.mapCochainComplexPlus.obj M).obj))
    (G.mapCochainComplexPlus.map (ObjectProperty.homMk
        (Y := P'.mapCochainComplexPlus.obj (g'.mapCochainComplexPlus.obj M))
        ((NatTrans.mapHomologicalComplex tw' (ComplexShape.up ℤ)).app M.obj)) ≫
      transportTwistMap P G P' ρ (g'.mapCochainComplexPlus.obj M))
    (congrArg DerivedCategory.Plus.Q.map (by
      ext n : 2
      exact (hβ (M.obj.X n)).symm))
  exact comp_inv_of_intertwine _ _ _ _ _ hT hN

omit [F₁.PreservesInjectiveObjects] in
/-- **A twisted endomorphism built from a natural twist is natural**: for `tw : g ⟶ g ⋙ P` and
a morphism `φ : K ⟶ L` of bounded below complexes, `RF₂(RF₁(g φ))` intertwines the endomorphisms
of `RF₂(RF₁(g K))` and `RF₂(RF₁(g L))` induced by `tw`. -/
theorem derivedTwistEndo_mapCochainComplexPlus_naturality {K L : CochainComplex.Plus B}
    (φ : K ⟶ L) :
    derivedTwistEndo P F₁ F₂ θ (g.mapCochainComplexPlus.obj K)
        (ObjectProperty.homMk (Y := P.mapCochainComplexPlus.obj (g.mapCochainComplexPlus.obj K))
          ((NatTrans.mapHomologicalComplex tw (ComplexShape.up ℤ)).app K.obj)) ≫
        F₂.rightDerivedFunctorPlus.map (F₁.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (g.mapCochainComplexPlus.map φ))) =
      F₂.rightDerivedFunctorPlus.map (F₁.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (g.mapCochainComplexPlus.map φ))) ≫
        derivedTwistEndo P F₁ F₂ θ (g.mapCochainComplexPlus.obj L)
          (ObjectProperty.homMk (Y := P.mapCochainComplexPlus.obj (g.mapCochainComplexPlus.obj L))
            ((NatTrans.mapHomologicalComplex tw (ComplexShape.up ℤ)).app L.obj)) :=
  derivedTwistEndo_naturality P F₁ F₂ θ _ _ _ (congrArg DerivedCategory.Plus.Q.map (by
    ext n : 2
    exact (tw.naturality (φ.hom.f n)).symm))

end BaseChangeTransport

end CategoryTheory.Functor

namespace Stacks.EtaleCohomology

/-! ### Closed immersion invariance of `RΓ(Y_k̄, (-)|_{Y_k̄})` -/

section DirectImage

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {Z Y : Over (Spec (.of k))}
  (i : Z ⟶ Y) [IsClosedImmersion i.left] (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **`RΓ(Z_k̄, M|_{Z_k̄}) ≅ RΓ(Y_k̄, (i_* M)|_{Y_k̄})`** for a closed immersion `i : Z ⟶ Y` of
schemes over `k`: the identification `RΓ(Z_k̄, N) = RΓ(Y_k̄, (i_k̄)_* N)` for the exact functor
`(i_k̄)_*`, followed by the inverse of the base change isomorphism
`(i_* M)|_{Y_k̄} ≅ (i_k̄)_*(M|_{Z_k̄})`. -/
def frobeniusRestrictionCohomologyDirectImageIso
    (M : CochainComplex.Plus (EtaleModules.{u, r} Λ Z.left)) :
    (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Z.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Z kbar M)) ≅
      (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar
            ((etaleModuleDirectImage.{u, r} Λ i.left).mapCochainComplexPlus.obj M))) :=
  haveI := isClosedImmersion_fieldBaseChangeMap i kbar
  haveI : PreservesFiniteLimits (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap i kbar)) :=
    ((exactFunctor_iff _).1
      (etaleModuleDirectImage_exact_of_isIntegralHom Λ (fieldBaseChangeMap i kbar))).1
  haveI : PreservesFiniteColimits (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap i kbar)) :=
    ((exactFunctor_iff _).1
      (etaleModuleDirectImage_exact_of_isIntegralHom Λ (fieldBaseChangeMap i kbar))).2
  haveI : IsIso (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar)
      (fieldBaseChangeProj Y kbar) (fieldBaseChangeProj Z kbar)
      (fieldBaseChangeMap_comp_fst i kbar)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
      (fun N ↦ isIso_etaleModuleBaseChange_fieldBaseChangeMap Λ i kbar N)
  Functor.baseChangeTwistTransportIso
    (etaleModuleDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap i kbar))
    (etaleModuleDirectImage.{u, r} Λ (pullback.snd Z.hom (specAlgebraMap k kbar)))
    (etaleModuleDirectImage.{u, r} Λ i.left)
    (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar))
    (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Z kbar))
    (etaleModuleDirectImageComp.{u, r} Λ (fieldBaseChangeMap i kbar)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (fieldBaseChangeMap_comp_snd i kbar).symm)
    (asIso (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar)
      (fieldBaseChangeProj Y kbar) (fieldBaseChangeProj Z kbar)
      (fieldBaseChangeMap_comp_fst i kbar))) M

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The comparison `(i_k̄)_* π̄_{Z,*} ≅ π̄_{Y,*} (i_k̄)_*` of the direct images along the two sides
of `π̄_Z ≫ i_k̄ = i_k̄ ≫ π̄_Y`; its underlying morphism is
`Stacks.EtaleCohomology.directImageTwistTransfer`. -/
abbrev fieldBaseChangeMapTwistIso :
    etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Z kbar p q hcard) ⋙
        etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap i kbar) ≅
      etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap i kbar) ⋙
        etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard) :=
  etaleModuleDirectImageComp.{u, r} Λ _ _ _ rfl ≪≫
    (etaleModuleDirectImageComp.{u, r} Λ _ _ _
      (geometricFrobeniusBaseChange_comp_fieldBaseChangeMap i p q hcard kbar)).symm

/-- The direct image along `i_k̄` is exact and the base change map for `i` and `i_k̄` is an
isomorphism. -/
private lemma fieldBaseChangeMap_exact_and_isIso {k : Type u} [Field k]
    {Z Y : Over (Spec (.of k))} (i : Z ⟶ Y) [IsClosedImmersion i.left] (kbar : Type u) [Field kbar]
    [Algebra k kbar] :
    PreservesFiniteLimits (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap i kbar)) ∧
      PreservesFiniteColimits (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap i kbar)) ∧
      IsIso (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar)
        (fieldBaseChangeProj Y kbar) (fieldBaseChangeProj Z kbar)
        (fieldBaseChangeMap_comp_fst i kbar)) := by
  have := isClosedImmersion_fieldBaseChangeMap i kbar
  have h := (exactFunctor_iff _).1
    (etaleModuleDirectImage_exact_of_isIntegralHom Λ (fieldBaseChangeMap i kbar))
  exact ⟨h.1, h.2, @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
    (fun N ↦ isIso_etaleModuleBaseChange_fieldBaseChangeMap Λ i kbar N)⟩

/-- **The identification `RΓ(Z_k̄, M|_{Z_k̄}) ≅ RΓ(Y_k̄, (i_* M)|_{Y_k̄})` commutes with the
canonical geometric Frobenius.** -/
theorem frobeniusRestrictionCohomologyDirectImageIso_hom_frobenius
    (M : CochainComplex.Plus (EtaleModules.{u, r} Λ Z.left)) :
    frobeniusRestrictionCohomologyEndo.{u, r} Λ Z kbar p q hcard M ≫
        (frobeniusRestrictionCohomologyDirectImageIso Λ i kbar M).hom =
      (frobeniusRestrictionCohomologyDirectImageIso Λ i kbar M).hom ≫
        frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard
          ((etaleModuleDirectImage.{u, r} Λ i.left).mapCochainComplexPlus.obj M) := by
  obtain ⟨_, _, _⟩ := fieldBaseChangeMap_exact_and_isIso Λ i kbar
  rw [frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo,
    frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo]
  exact Functor.derivedTwistEndo_comp_baseChangeTwistTransportIso_hom
    (F₁ := etaleModuleDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (F₂ := etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (G := etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap i kbar))
    (F₁' := etaleModuleDirectImage.{u, r} Λ (pullback.snd Z.hom (specAlgebraMap k kbar)))
    (I := etaleModuleDirectImage.{u, r} Λ i.left)
    (g := etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar))
    (g' := etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Z kbar))
    (γ := etaleModuleDirectImageComp.{u, r} Λ (fieldBaseChangeMap i kbar)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (fieldBaseChangeMap_comp_snd i kbar).symm)
    (β := asIso (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar)
      (fieldBaseChangeProj Y kbar) (fieldBaseChangeProj Z kbar)
      (fieldBaseChangeMap_comp_fst i kbar)))
    (P := etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
    (P' := etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Z kbar p q hcard))
    (θ := etaleModuleDirectImageComp.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
    (θ' := etaleModuleDirectImageComp.{u, r} Λ (geometricFrobeniusBaseChange Z kbar p q hcard)
      (pullback.snd Z.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Z kbar p q hcard).symm)
    (ρ := fieldBaseChangeMapTwistIso Λ i kbar p q hcard)
    (tw := frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard)
    (tw' := frobeniusBaseChangeTwist.{u, r} Λ Z kbar p q hcard)
    (directImageTwistTransfer_compat Λ (fieldBaseChangeMap i kbar)
      (geometricFrobeniusBaseChange Z kbar p q hcard)
      (geometricFrobeniusBaseChange Y kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_fieldBaseChangeMap i p q hcard kbar)
      (fieldBaseChangeMap_comp_snd i kbar).symm
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm
      (geometricFrobeniusBaseChange_comp_toBase Z kbar p q hcard).symm)
    (etaleModuleBaseChange_comp_frobeniusBaseChangeTwist Λ i p q hcard kbar) M

end DirectImage

/-! ### `RΓ_c` of a closed subscheme -/

section CompactSupport

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [QuasiCompact f] (j : CompactificationOf (Over.mk f)) {Z : Scheme.{u}}
  (i : Z ⟶ X) [IsClosedImmersion i] (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The closed immersion `ι : Z̄ ⟶ X̄` of the compactification induced on `Z` into the given
compactification, as a morphism of schemes over `k`. -/
abbrev restrictClosedSpaceHom : Over.mk (j.restrictClosed i).toBase ⟶ Over.mk j.toBase :=
  Over.homMk (j.closedSpaceι i)

/-- The underlying morphism of `restrictClosedSpaceHom f j i` is a closed immersion. -/
instance : IsClosedImmersion (restrictClosedSpaceHom f j i).left :=
  inferInstanceAs (IsClosedImmersion (j.closedSpaceι i))

/-- `j_! (i_* L) ≅ ι_* (t_! L)` degreewise on a bounded below complex, for the cartesian square of
`i`, the open immersion `t : Z ⟶ Z̄` of the induced compactification, `j` and `ι : Z̄ ⟶ X̄`. -/
abbrev extensionByZeroDirectImagePlusBaseChangeIso
    (L : CochainComplex.Plus (EtaleModules.{u, r} Λ Z)) :
    (etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj
        ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj L) ≅
      (etaleModuleDirectImage.{u, r} Λ (j.closedSpaceι i)).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, r} Λ
          (j.closedImmersion i).toImage).mapCochainComplexPlus.obj L) :=
  Functor.baseChangePlusIso (etaleModuleDirectImage.{u, r} Λ (j.closedSpaceι i))
    (etaleModuleDirectImage.{u, r} Λ i) (etaleModuleExtensionByZero.{u, r} Λ j.immersion)
    (etaleModuleExtensionByZero.{u, r} Λ (j.closedImmersion i).toImage)
    (etaleModuleExtensionByZeroDirectImageIso.{u, r} Λ i (j.closedImmersion i).toImage
      j.immersion (j.closedSpaceι i) (j.isPullback_restrictClosed i)) L

/-- **`RΓ_c(Z_k̄, L) ≅ RΓ_c(X_k̄, i_* L)`** for a closed immersion `i : Z ⟶ X` and the
compactification of `Z` induced by a compactification `j` of `X`
(`AlgebraicGeometry.CompactificationOf.restrictClosed`): the closed immersion invariance
`RΓ(Z̄_k̄, (t_! L)|_{Z̄_k̄}) ≅ RΓ(X̄_k̄, (ι_* t_! L)|_{X̄_k̄})`, followed by
`ι_* t_! ≅ j_! i_*`. -/
def compactSupportFrobeniusCohomologyClosedImmersionIso
    (L : CochainComplex.Plus (EtaleModules.{u, r} Λ Z)) :
    compactSupportFrobeniusCohomology.{u, r} Λ (i ≫ f) (j.restrictClosed i) kbar L ≅
      compactSupportFrobeniusCohomology.{u, r} Λ f j kbar
        ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj L) :=
  frobeniusRestrictionCohomologyDirectImageIso Λ (restrictClosedSpaceHom f j i) kbar
      ((etaleModuleExtensionByZero.{u, r} Λ (j.closedImmersion i).toImage).mapCochainComplexPlus.obj
        L) ≪≫
    ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).mapIso
      ((etaleModuleDerivedDirectImage.{u, r} Λ
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).mapIso
        (DerivedCategory.Plus.Q.mapIso
          ((etaleModuleInverseImage.{u, r} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.mapIso
              (extensionByZeroDirectImagePlusBaseChangeIso Λ f j i L))))).symm

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The identification `RΓ_c(Z_k̄, L) ≅ RΓ_c(X_k̄, i_* L)` commutes with the canonical
geometric Frobenius.** -/
theorem compactSupportFrobeniusCohomologyClosedImmersionIso_hom_frobenius
    (L : CochainComplex.Plus (EtaleModules.{u, r} Λ Z)) :
    canonicalCompactSupportFrobenius.{u, r} Λ (i ≫ f) (j.restrictClosed i) kbar p q hcard L ≫
        (compactSupportFrobeniusCohomologyClosedImmersionIso Λ f j i kbar L).hom =
      (compactSupportFrobeniusCohomologyClosedImmersionIso Λ f j i kbar L).hom ≫
        canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard
          ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj L) := by
  have hA := frobeniusRestrictionCohomologyDirectImageIso_hom_frobenius Λ
    (restrictClosedSpaceHom f j i) kbar p q hcard
    ((etaleModuleExtensionByZero.{u, r} Λ (j.closedImmersion i).toImage).mapCochainComplexPlus.obj
      L)
  have hR := Functor.derivedTwistEndo_mapCochainComplexPlus_naturality
    (F₁ := etaleModuleDirectImage.{u, r} Λ
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
    (F₂ := etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (g := etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar))
    (P := etaleModuleDirectImage.{u, r} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
    (θ := etaleModuleDirectImageComp.{u, r} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard).symm)
    (tw := frobeniusBaseChangeTwist.{u, r} Λ (Over.mk j.toBase) kbar p q hcard)
    (extensionByZeroDirectImagePlusBaseChangeIso Λ f j i L).hom
  exact Functor.comp_inv_of_intertwine _ _ _ _ _ hA hR

end CompactSupport

end Stacks.EtaleCohomology

end
