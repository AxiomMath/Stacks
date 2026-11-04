module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSmoothModelNatural

/-!
# `H²_c` of a map of sheaves of `ℤ/n`-modules on `X_k̄`, and its trace

Let `X` be a smooth curve over a field `k`, `j : X ⟶ X̄` a compactification, `k̄` an algebraically
closed extension of `k`, and `ψ : R →+* Λ` a morphism of rings (in the Trace Formula chapter,
`R = ℤ/n` and `Λ` a finite ring of order `n`, possibly noncommutative). For a sheaf `F` of
`Λ`-modules and a sheaf `G` of `R`-modules on `X`, an `R`-linear map
`φ : res_ψ(F|_{X_k̄}) ⟶ G|_{X_k̄}` on `X_k̄` induces a map
`H²_c(X_k̄, F) ⟶ H²_c(X_k̄, G)` (`Stacks.EtaleCohomology.galoisCompactSupportRestrictScalarsMap`):
the cohomology `H²_c(X_k̄, F) = H²(X̄_k̄, (j_! F)|_{X̄_k̄})` read over `R` through the cohomology
of the underlying abelian sheaf, followed by `H²(X̄_k̄, -)` of the map
`res_ψ((j_! F)|_{X̄_k̄}) ≅ j'_!(res_ψ(F|_{X_k̄})) ⟶ j'_!(G|_{X_k̄}) ≅ (j_! G)|_{X̄_k̄}`
(`Stacks.EtaleCohomology.compactSupportCoefficientMap`), `j' : X_k̄ ⟶ X̄_k̄` the base change
of `j`.

Read in abelian groups through the derived comparisons `res_ℤ Hⁱ(-, -) ≅ Hⁱ(-, res_ℤ -)` over `Λ`
and over `R`, the map is `H²(X̄_k̄, -)` of the map of sheaves of abelian groups underlying the map
above (`Stacks.EtaleCohomology.galoisCompactSupportRestrictScalarsMap_int`): it is computed on
injective resolutions read as complexes of abelian groups.

## Main definitions

* `Stacks.EtaleCohomology.compactSupportCoefficientMap`.
* `Stacks.EtaleCohomology.galoisCompactSupportRestrictScalarsMap`.
* `Stacks.EtaleCohomology.restrictScalarsIntCompIso` — `res_ℤ N ≅ res_ℤ(res_ψ N)` on sheaves of
  `ℤ`-modules, the identity on sections.

## Main results

* `Stacks.EtaleCohomology.rightDerivedPlusRestrictScalarsIntIso_restrictScalars` — the coefficient
  change `Hⁱ(Y, N) ≃+ Hⁱ(Y, res_ψ N)` read through the derived comparisons with `ℤ`.
* `Stacks.EtaleCohomology.galoisCompactSupportRestrictScalarsMap_int`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Frobenius

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.EtaleCohomology.etaleModulesEnoughInjectivesZeroTraceTwist
  Stacks.EtaleCohomology.moduleCatHasColimitsOfSizeSmallEtale
  Stacks.EtaleCohomology.hasGlobalSectionsFunctorSmallEtaleModuleCat

namespace Stacks.EtaleCohomology

section IntComparison

variable {R Λ : Type} [Ring R] [Ring Λ] (ψ : R →+* Λ) (Y : Scheme.{u})

/-- **`res_ℤ N ≅ res_ℤ (res_ψ N)`** for a sheaf `N` of `Λ`-modules: the two sheaves of `ℤ`-modules
underlying `N` and `res_ψ N` agree, through the identity on sections
(`ModuleCat.restrictScalarsComp'`). -/
def restrictScalarsIntCompIso (N : EtaleModules.{u, 0} Λ Y) :
    (etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj N ≅
      (etaleModuleRestrictScalars (Int.castRingHom R) Y).obj
        ((etaleModuleRestrictScalars ψ Y).obj N) :=
  ObjectProperty.isoMk _ (Functor.isoWhiskerLeft N.obj
    (ModuleCat.restrictScalarsComp'.{u + 1} (Int.castRingHom R) ψ (Int.castRingHom Λ)
      (RingHom.ext_int _ _)))

/-- The identity on sections `res_ℤ N ≅ res_ℤ (res_ψ N)` is the identity of the underlying
abelian sheaf. -/
theorem underlyingAbelian_map_restrictScalarsIntCompIso_hom (N : EtaleModules.{u, 0} Λ Y) :
    (etaleModuleUnderlyingAbelian Y ℤ).map (restrictScalarsIntCompIso ψ Y N).hom =
      (underlyingAbelianRestrictScalarsIso ψ Y N).inv := by
  ext U x
  rfl

/-- **A `ℤ`-linear map `res_ℤ N ⟶ res_ℤ N'` is `R`-linear** when `ℤ →+* R` is surjective (for
instance `R = ℤ/n`): the map `res_ψ N ⟶ N'` of sheaves of `R`-modules with the same sections. -/
def restrictScalarsIntLift (hR : Function.Surjective (Int.castRingHom R))
    {N : EtaleModules.{u, 0} Λ Y} {N' : EtaleModules.{u, 0} R Y}
    (θ : (etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj N ⟶
      (etaleModuleRestrictScalars (Int.castRingHom R) Y).obj N') :
    (etaleModuleRestrictScalars ψ Y).obj N ⟶ N' :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom
        (X := (ModuleCat.restrictScalars.{u + 1} ψ).obj (N.obj.obj U)) (Y := N'.obj.obj U)
        { toFun := fun x => (θ.hom.app U).hom x
          map_add' := fun a b => map_add (θ.hom.app U).hom a b
          map_smul' := fun r x => by
            obtain ⟨z, rfl⟩ := hR r
            let t : N.obj.obj U → N'.obj.obj U := fun x => (θ.hom.app U).hom x
            change t (ψ (z : R) • x) = (z : R) • t x
            rw [map_intCast]
            exact (θ.hom.app U).hom.map_smul z x }
      naturality := fun U V g => by
        ext x
        exact ConcreteCategory.congr_hom (θ.hom.naturality g) x }

/-- `res_ℤ` of the lift is the given `ℤ`-linear map, through the identity on sections
`res_ℤ N ≅ res_ℤ (res_ψ N)`. -/
theorem restrictScalarsIntLift_spec (hR : Function.Surjective (Int.castRingHom R))
    {N : EtaleModules.{u, 0} Λ Y} {N' : EtaleModules.{u, 0} R Y}
    (θ : (etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj N ⟶
      (etaleModuleRestrictScalars (Int.castRingHom R) Y).obj N') :
    (restrictScalarsIntCompIso ψ Y N).hom ≫
        (etaleModuleRestrictScalars (Int.castRingHom R) Y).map (restrictScalarsIntLift ψ Y hR θ) =
      θ := by
  ext U x
  rfl

/-- **The lift is unique**: an `R`-linear map is determined by its underlying `ℤ`-linear map. -/
theorem restrictScalarsIntLift_unique (hR : Function.Surjective (Int.castRingHom R))
    {N : EtaleModules.{u, 0} Λ Y} {N' : EtaleModules.{u, 0} R Y}
    (θ : (etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj N ⟶
      (etaleModuleRestrictScalars (Int.castRingHom R) Y).obj N')
    (θ' : (etaleModuleRestrictScalars ψ Y).obj N ⟶ N')
    (h : (restrictScalarsIntCompIso ψ Y N).hom ≫
        (etaleModuleRestrictScalars (Int.castRingHom R) Y).map θ' = θ) :
    θ' = restrictScalarsIntLift ψ Y hR θ := by
  subst h
  ext U x
  rfl

variable [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The coefficient change `Hⁱ(Y, N) ≃+ Hⁱ(Y, res_ψ N)` through the derived comparisons with
`ℤ`**: read through `res_ℤ Hⁱ(Y, -) ≅ Hⁱ(Y, res_ℤ -)` over `R` and over `Λ`, it is `Hⁱ(Y, -)` of
the identity on sections `res_ℤ N ≅ res_ℤ (res_ψ N)`. -/
theorem rightDerivedPlusRestrictScalarsIntIso_restrictScalars (N : EtaleModules.{u, 0} Λ Y) (i : ℕ)
    (y : ((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).obj N) :
    (rightDerivedPlusRestrictScalarsIntIso Y ((etaleModuleRestrictScalars ψ Y).obj N) i).hom.hom
        (etaleModuleCohomologyRestrictScalars ψ Y N i y) =
      (((etaleModuleGlobalSections.{u, 0} ℤ Y).rightDerivedPlus (i : ℤ)).map
        (restrictScalarsIntCompIso ψ Y N).hom).hom
          ((rightDerivedPlusRestrictScalarsIntIso Y N i).hom.hom y) := by
  let E : ∀ P : EtaleModules.{u, 0} ℤ Y,
      ((etaleModuleGlobalSections.{u, 0} ℤ Y).rightDerivedPlus (i : ℤ)).obj P ≃+
        Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian Y ℤ).obj P) i := fun P =>
    ((forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).mapIso (Iso.refl _) ≪≫
      etaleModuleRightDerivedPlusIsoExt ℤ Y P i).addCommGroupIsoToAddEquiv.trans
      (extConstantIntAddEquivSheafH Y P i)
  have hE : ∀ (S : Type) [Ring S] (P : EtaleModules.{u, 0} S Y)
      (z : ((etaleModuleGlobalSections.{u, 0} S Y).rightDerivedPlus (i : ℤ)).obj P),
      etaleModuleCohomologyAddEquivSheafH Y P i z =
        E _ ((rightDerivedPlusRestrictScalarsIntIso Y P i).hom.hom z) := fun _ _ _ _ => rfl
  have hEn : ∀ {P P' : EtaleModules.{u, 0} ℤ Y} (g : P ⟶ P')
      (z : ((etaleModuleGlobalSections.{u, 0} ℤ Y).rightDerivedPlus (i : ℤ)).obj P),
      E P' ((((etaleModuleGlobalSections.{u, 0} ℤ Y).rightDerivedPlus (i : ℤ)).map g).hom z) =
        Sheaf.H.map ((etaleModuleUnderlyingAbelian Y ℤ).map g) i (E P z) := by
    intro P P' g z
    have hB := congrArg (fun f => f.hom z)
      (etaleModuleRightDerivedPlusIsoExt_hom_naturality Y g i)
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at hB
    exact (congrArg (extConstantIntAddEquivSheafH Y P' i) hB).trans
      (extConstantIntAddEquivSheafH_naturality Y g i _)
  apply (E _).injective
  rw [← hE, etaleModuleCohomologyAddEquivSheafH_restrictScalars, hEn, hE,
    underlyingAbelian_map_restrictScalarsIntCompIso_hom]

end IntComparison

section Bridge

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  {R Λ : Type} [Ring R] [Ring Λ] (ψ : R →+* Λ)

/-- **The map `res_ψ((j_! F)|_{X̄_k̄}) ⟶ (j_! G)|_{X̄_k̄}` induced by
`φ : res_ψ(F|_{X_k̄}) ⟶ G|_{X_k̄}`**: `(j_! F)|_{X̄_k̄} ≅ j'_!(F|_{X_k̄})` (Tag 03S6),
`res_ψ j'_! ≅ j'_! res_ψ`, `j'_!(φ)`, and `j'_!(G|_{X_k̄}) ≅ (j_! G)|_{X̄_k̄}`. -/
def compactSupportCoefficientMap (F : EtaleModules.{u, 0} Λ X) (G : EtaleModules.{u, 0} R X)
    (φ : (etaleModuleRestrictScalars ψ (pullback f (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst f (specAlgebraMap k kbar))).obj G) :
    (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G) :=
  (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).map
      ((compactificationFieldBaseChangeExtensionByZeroIso Λ f j kbar).inv.app F) ≫
    (etaleModuleExtensionByZeroRestrictScalars ψ
        (compactificationFieldBaseChangeImmersion f j kbar)).inv.app
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F) ≫
    (etaleModuleExtensionByZero.{u, 0} R
        (compactificationFieldBaseChangeImmersion f j kbar)).map φ ≫
    (compactificationFieldBaseChangeExtensionByZeroIso R f j kbar).hom.app G

/-- **The map `H²_c(X_k̄, F) ⟶ H²_c(X_k̄, G)` induced by a map
`θ : res_ψ((j_! F)|_{X̄_k̄}) ⟶ (j_! G)|_{X̄_k̄}` on `X̄_k̄`**:
`H²_c(X_k̄, F) = H²(X̄_k̄, (j_! F)|_{X̄_k̄})`, the coefficient change
`H²(X̄_k̄, N) ≃+ H²(X̄_k̄, res_ψ N)` through the underlying abelian sheaf, and `H²(X̄_k̄, θ)`. -/
def galoisCompactSupportRestrictScalarsMapOfBar (F : EtaleModules.{u, 0} Λ X)
    (G : EtaleModules.{u, 0} R X)
    (θ : (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)) :
    galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) ((2 : ℕ) : ℤ) →+
      galoisCompactSupportCohomologyGroup.{u, 0} R f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj G) ((2 : ℕ) : ℤ) where
  toFun x := (galoisCompactSupportSingleIso f j kbar R G ((2 : ℕ) : ℤ)).inv.hom
    ((((etaleModuleGlobalSections.{u, 0} R
        (pullback j.toBase (specAlgebraMap k kbar))).rightDerivedPlus ((2 : ℕ) : ℤ)).map θ).hom
      (etaleModuleCohomologyRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar)) _ 2
        ((galoisCompactSupportSingleIso f j kbar Λ F ((2 : ℕ) : ℤ)).hom.hom x)))
  map_zero' := by rw [map_zero, map_zero, map_zero, map_zero]
  map_add' a b := by rw [map_add, map_add, map_add, map_add]

/-- Through `H²_c(X_k̄, G) ≅ H²(X̄_k̄, (j_! G)|_{X̄_k̄})`, the image of `x` under the map induced
by `θ` is `H²(X̄_k̄, θ)` applied to the coefficient change of the image of `x` in
`H²(X̄_k̄, (j_! F)|_{X̄_k̄})`. -/
theorem galoisCompactSupportRestrictScalarsMapOfBar_apply (F : EtaleModules.{u, 0} Λ X)
    (G : EtaleModules.{u, 0} R X)
    (θ : (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G))
    (x : galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) ((2 : ℕ) : ℤ)) :
    (galoisCompactSupportSingleIso f j kbar R G ((2 : ℕ) : ℤ)).hom.hom
        (galoisCompactSupportRestrictScalarsMapOfBar f j kbar ψ F G θ x) =
      (((etaleModuleGlobalSections.{u, 0} R
          (pullback j.toBase (specAlgebraMap k kbar))).rightDerivedPlus ((2 : ℕ) : ℤ)).map θ).hom
        (etaleModuleCohomologyRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar)) _ 2
          ((galoisCompactSupportSingleIso f j kbar Λ F ((2 : ℕ) : ℤ)).hom.hom x)) := by
  show (galoisCompactSupportSingleIso f j kbar R G ((2 : ℕ) : ℤ)).hom.hom
      ((galoisCompactSupportSingleIso f j kbar R G ((2 : ℕ) : ℤ)).inv.hom _) = _
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.inv_hom_id, ModuleCat.hom_id,
    LinearMap.id_apply]

/-- **`H²_c(X_k̄, F) ⟶ H²_c(X_k̄, G)` read in abelian groups is computed on injective
resolutions.** Through `H²_c(X_k̄, -) = H²(X̄_k̄, (j_! -)|_{X̄_k̄})` and the derived comparisons
`res_ℤ H²(X̄_k̄, -) ≅ H²(X̄_k̄, res_ℤ -)` over `Λ` and over `R`
(`Stacks.EtaleCohomology.rightDerivedPlusRestrictScalarsIntIso`), the map induced by `θ` is
`H²(X̄_k̄, -)` of the map of sheaves of `ℤ`-modules
`res_ℤ((j_! F)|) ≅ res_ℤ(res_ψ (j_! F)|) ⟶ res_ℤ((j_! G)|)`: the identity on sections
(`Stacks.EtaleCohomology.restrictScalarsIntCompIso`) followed by `res_ℤ θ`. -/
theorem galoisCompactSupportRestrictScalarsMapOfBar_int (F : EtaleModules.{u, 0} Λ X)
    (G : EtaleModules.{u, 0} R X)
    (θ : (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G))
    (x : galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) ((2 : ℕ) : ℤ)) :
    (rightDerivedPlusRestrictScalarsIntIso (pullback j.toBase (specAlgebraMap k kbar))
        ((etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)) 2).hom.hom
        ((galoisCompactSupportSingleIso f j kbar R G ((2 : ℕ) : ℤ)).hom.hom
          (galoisCompactSupportRestrictScalarsMapOfBar f j kbar ψ F G θ x)) =
      (((etaleModuleGlobalSections.{u, 0} ℤ
          (pullback j.toBase (specAlgebraMap k kbar))).rightDerivedPlus
        ((2 : ℕ) : ℤ)).map ((restrictScalarsIntCompIso ψ (pullback j.toBase (specAlgebraMap k kbar))
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))).hom ≫
          (etaleModuleRestrictScalars (Int.castRingHom R)
            (pullback j.toBase (specAlgebraMap k kbar))).map θ)).hom
        ((rightDerivedPlusRestrictScalarsIntIso (pullback j.toBase (specAlgebraMap k kbar))
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) 2).hom.hom
          ((galoisCompactSupportSingleIso f j kbar Λ F ((2 : ℕ) : ℤ)).hom.hom x)) := by
  rw [galoisCompactSupportRestrictScalarsMapOfBar_apply]
  generalize (galoisCompactSupportSingleIso f j kbar Λ F ((2 : ℕ) : ℤ)).hom.hom x = y
  have hn := congrArg (fun g => g.hom
      (etaleModuleCohomologyRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar)) _ 2 y))
    (rightDerivedPlusRestrictScalarsIntIso_hom_naturality
      (pullback j.toBase (specAlgebraMap k kbar)) θ ((2 : ℕ) : ℤ))
  have h2 := rightDerivedPlusRestrictScalarsIntIso_restrictScalars ψ
    (pullback j.toBase (specAlgebraMap k kbar))
    ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) 2 y
  exact hn.trans ((congrArg (((etaleModuleGlobalSections.{u, 0} ℤ
      (pullback j.toBase (specAlgebraMap k kbar))).rightDerivedPlus ((2 : ℕ) : ℤ)).map
        ((etaleModuleRestrictScalars (Int.castRingHom R)
          (pullback j.toBase (specAlgebraMap k kbar))).map θ)).hom h2).trans
    (congrArg (fun g => ModuleCat.Hom.hom g ((rightDerivedPlusRestrictScalarsIntIso
        (pullback j.toBase (specAlgebraMap k kbar))
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) 2).hom.hom y))
      (Functor.map_comp ((etaleModuleGlobalSections.{u, 0} ℤ
          (pullback j.toBase (specAlgebraMap k kbar))).rightDerivedPlus ((2 : ℕ) : ℤ))
        (restrictScalarsIntCompIso ψ (pullback j.toBase (specAlgebraMap k kbar))
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))).hom
        ((etaleModuleRestrictScalars (Int.castRingHom R)
          (pullback j.toBase (specAlgebraMap k kbar))).map θ))).symm)

/-- **The `ℤ`-form for a `ℤ`-linear map on `X̄_k̄`.** For `ℤ →+* R` surjective and a `ℤ`-linear
`θ : res_ℤ((j_! F)|_{X̄_k̄}) ⟶ res_ℤ((j_! G)|_{X̄_k̄})`, the map induced by its `R`-linear lift
(`Stacks.EtaleCohomology.restrictScalarsIntLift`), read in abelian groups through the derived
comparisons with `ℤ`, is `H²(X̄_k̄, θ)`. -/
theorem galoisCompactSupportRestrictScalarsMapOfBar_int_lift
    (hR : Function.Surjective (Int.castRingHom R)) (F : EtaleModules.{u, 0} Λ X)
    (G : EtaleModules.{u, 0} R X)
    (θ : (etaleModuleRestrictScalars (Int.castRingHom Λ)
          (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ⟶
      (etaleModuleRestrictScalars (Int.castRingHom R)
          (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)))
    (x : galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) ((2 : ℕ) : ℤ)) :
    (rightDerivedPlusRestrictScalarsIntIso (pullback j.toBase (specAlgebraMap k kbar))
        ((etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)) 2).hom.hom
        ((galoisCompactSupportSingleIso f j kbar R G ((2 : ℕ) : ℤ)).hom.hom
          (galoisCompactSupportRestrictScalarsMapOfBar f j kbar ψ F G
            (restrictScalarsIntLift ψ _ hR θ) x)) =
      (((etaleModuleGlobalSections.{u, 0} ℤ
          (pullback j.toBase (specAlgebraMap k kbar))).rightDerivedPlus ((2 : ℕ) : ℤ)).map θ).hom
        ((rightDerivedPlusRestrictScalarsIntIso (pullback j.toBase (specAlgebraMap k kbar))
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) 2).hom.hom
          ((galoisCompactSupportSingleIso f j kbar Λ F ((2 : ℕ) : ℤ)).hom.hom x)) := by
  rw [galoisCompactSupportRestrictScalarsMapOfBar_int, restrictScalarsIntLift_spec]

/-- **The map `H²_c(X_k̄, F) ⟶ H²_c(X_k̄, G)` induced by `φ : res_ψ(F|_{X_k̄}) ⟶ G|_{X_k̄}`**:
`Stacks.EtaleCohomology.galoisCompactSupportRestrictScalarsMapOfBar` of
`Stacks.EtaleCohomology.compactSupportCoefficientMap`. -/
abbrev galoisCompactSupportRestrictScalarsMap (F : EtaleModules.{u, 0} Λ X)
    (G : EtaleModules.{u, 0} R X)
    (φ : (etaleModuleRestrictScalars ψ (pullback f (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst f (specAlgebraMap k kbar))).obj G) :
    galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) ((2 : ℕ) : ℤ) →+
      galoisCompactSupportCohomologyGroup.{u, 0} R f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj G) ((2 : ℕ) : ℤ) :=
  galoisCompactSupportRestrictScalarsMapOfBar f j kbar ψ F G
    (compactSupportCoefficientMap f j kbar ψ F G φ)

/-- `Stacks.EtaleCohomology.galoisCompactSupportRestrictScalarsMapOfBar_int` for
`Stacks.EtaleCohomology.galoisCompactSupportRestrictScalarsMap`. -/
theorem galoisCompactSupportRestrictScalarsMap_int (F : EtaleModules.{u, 0} Λ X)
    (G : EtaleModules.{u, 0} R X)
    (φ : (etaleModuleRestrictScalars ψ (pullback f (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst f (specAlgebraMap k kbar))).obj G)
    (x : galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) ((2 : ℕ) : ℤ)) :
    (rightDerivedPlusRestrictScalarsIntIso (pullback j.toBase (specAlgebraMap k kbar))
        ((etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)) 2).hom.hom
        ((galoisCompactSupportSingleIso f j kbar R G ((2 : ℕ) : ℤ)).hom.hom
          (galoisCompactSupportRestrictScalarsMap f j kbar ψ F G φ x)) =
      (((etaleModuleGlobalSections.{u, 0} ℤ
          (pullback j.toBase (specAlgebraMap k kbar))).rightDerivedPlus
        ((2 : ℕ) : ℤ)).map ((restrictScalarsIntCompIso ψ (pullback j.toBase (specAlgebraMap k kbar))
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))).hom ≫
          (etaleModuleRestrictScalars (Int.castRingHom R)
            (pullback j.toBase (specAlgebraMap k kbar))).map
            (compactSupportCoefficientMap f j kbar ψ F G φ))).hom
        ((rightDerivedPlusRestrictScalarsIntIso (pullback j.toBase (specAlgebraMap k kbar))
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) 2).hom.hom
          ((galoisCompactSupportSingleIso f j kbar Λ F ((2 : ℕ) : ℤ)).hom.hom x)) :=
  galoisCompactSupportRestrictScalarsMapOfBar_int f j kbar ψ F G _ x

end Bridge

end Stacks.EtaleCohomology

end
