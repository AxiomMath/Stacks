module

public import StacksFrontier.AlgebraicGeometry.AffineDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineOpenDerivedStalk
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsOverLerayComp
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardArbitraryTarget
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeComparisonComposition
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeTranspose

/-!
# Derived global sections commute with base change, from base change of the pushforward

Let
```
X' --g'--> X
|f'        |f
Spec R' --> Spec R
```
be a commutative square of schemes, the bottom arrow being `g = Spec φ` for a ring map
`φ : R ⟶ R'`, with `f` quasi-compact and quasi-separated. Let `K` be an object of `D(𝒪_X)` with
quasi-coherent cohomology sheaves, `M` an object of `D(𝒪_{X'})` and `h : Lg'^*K ⟶ M`. If the
derived base change map `Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` followed by `Rf'_* h` is an isomorphism,
then so is the canonical map

`RΓ(X, K) ⊗_R^𝐋 R' ⟶ RΓ(X', M)`,

the derived base-change map adjoint to `RΓ(X, K) ⟶ RΓ(X, Rg'_* Lg'^* K) ⟶ RΓ(X, Rg'_* M) =
φ^* RΓ(X', M)`.

## Main results

* `AlgebraicGeometry.isIso_derivedBaseChangeComparison_of_isIso_derivedBaseChangeMap` — the
  statement above.
* `AlgebraicGeometry.isQuasicoherent_homology_derivedPushforward_ringedSpace_of_qcqs` — part (1)
  of [Stacks, Tag 08D5] for the derived pushforward of ringed spaces, at every model.
* `AlgebraicGeometry.derivedRestrictScalarsComp_id_left_hom_app` and
  `AlgebraicGeometry.derivedRestrictScalarsComp_id_right_hom_app` — the identification
  `AlgebraicGeometry.restrictScalarsIdDerivedIso` of derived restriction of scalars along the
  identity with the identity is compatible with
  `StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp`.
* `AlgebraicGeometry.derivedGlobalSectionsOver_leray_baseChange_compat` — the Leray
  identifications around the square are compatible.
* `CategoryTheory.baseChange_leray_compat` — the compatibility of the Leray identifications
  around a square of pushforwards, at variable functors.
* `CategoryTheory.isIso_homEquiv_symm_of_baseChange` — invertibility of a transpose along
  compatible Leray identifications, at variable functors.

## Implementation notes

The diagram chase is carried out at variables (`CategoryTheory.baseChange_leray_compat` and
`CategoryTheory.isIso_homEquiv_symm_of_baseChange`), where every functor is a variable: the
derived pullback of ringed spaces is an `abbrev` of a constructive total derived functor, and a
kernel comparison of `Lg^*(Rf_* K)` with `(Rf_* ⋙ Lg^*) K` at the concrete functors unfolds it
and times out. Every concrete hypothesis is therefore produced in
exactly the spelling its variable form expects: the base change map is used through
`Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap` and its transpose through
`Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap_unit_fac`, both at variable
adjunctions (`AlgebraicGeometry.isIso_homEquiv_symm_of_derivedBaseChangeMap`); the comparison
of the two iterated pushforwards is used at the level of natural transformations; the two Leray
identifications of the common composite are related by `HEq`; and the compatibility of the Leray
identifications is packaged as the definition `CategoryTheory.LerayBaseChangeCompat`, so that
its concrete statement is elaborated from its arguments alone.

All derived categories are at `HasDerivedCategory.standard`, scoped to each declaration that
needs it: the derived pushforward of ringed spaces, its composition isomorphisms, the derived
base change map and `StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison` are only
stated there.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0CTE](https://stacks.math.columbia.edu/tag/0CTE)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w₁ w₂ u

namespace CategoryTheory

variable {DX DX' DS DS' MR MR' : Type*} [Category DX] [Category DX'] [Category DS]
  [Category DS'] [Category MR] [Category MR']
  {Rf : DX ⥤ DS} {Rf' : DX' ⥤ DS'} {Rg' : DX' ⥤ DX} {Rg : DS' ⥤ DS}
  {Γf : DX ⥤ MR} {Γf' : DX' ⥤ MR'} {ΓR : DS ⥤ MR} {ΓR' : DS' ⥤ MR'}
  {I : MR ⥤ MR} {I' : MR' ⥤ MR'} {Φ : MR' ⥤ MR}

/-- The compatibility of Leray identifications `ℓf`, `ℓf'`, `ℓg`, `ℓg'` around a square of
pushforwards with comparison `cmp`, at `M`: `ℓf` and `ℓg'` read through `e : I ≅ 𝟭` agree with
`cmp`, `ℓg` and `ℓf'` read through `e' : I' ≅ 𝟭`. -/
def LerayBaseChangeCompat (e : I ≅ 𝟭 MR) (e' : I' ≅ 𝟭 MR')
    (ℓf : Rf ⋙ ΓR ≅ Γf ⋙ I) (ℓf' : Rf' ⋙ ΓR' ≅ Γf' ⋙ I') (ℓg : Rg ⋙ ΓR ≅ ΓR' ⋙ Φ)
    (ℓg' : Rg' ⋙ Γf ≅ Γf' ⋙ Φ) (cmp : Rg' ⋙ Rf ⟶ Rf' ⋙ Rg) (M : DX') : Prop :=
  ℓf.hom.app (Rg'.obj M) ≫ I.map (ℓg'.hom.app M) ≫ e.hom.app (Φ.obj (Γf'.obj M)) =
    ΓR.map (cmp.app M) ≫ ℓg.hom.app (Rf'.obj M) ≫
      Φ.map (ℓf'.hom.app M ≫ e'.hom.app (Γf'.obj M))

/-- **The two Leray squares of a square of pushforwards are compatible**, at variables. Given
Leray identifications `ℓf : Rf ⋙ ΓR ≅ Γf ⋙ I`, `ℓf' : Rf' ⋙ ΓR' ≅ Γf' ⋙ I'`,
`ℓg : Rg ⋙ ΓR ≅ ΓR' ⋙ Φ`, `ℓg' : Rg' ⋙ Γf ≅ Γf' ⋙ Φ`, isomorphisms `e : I ≅ 𝟭`, `e' : I' ≅ 𝟭`,
and two factorizations `cA : Rg' ⋙ Rf ≅ Rk`, `cB : Rf' ⋙ Rg ≅ Rk'` of a composite whose Leray
identifications `LA`, `LB` are the composites of the factors (`hA`, `hB`) and agree up to the
transport along `Rk = Rk'` (`hT`), the comparison `cmp = cA ≫ eqToHom ≫ cB⁻¹` carries `ℓf`
and `ℓg'` to `ℓg` and `ℓf'`, once `rA`, `rB` are identified with `e`, `e'` (`h₂`, `h₃`). -/
theorem baseChange_leray_compat {Rk Rk' : DX' ⥤ DS}
    (e : I ≅ 𝟭 MR) (e' : I' ≅ 𝟭 MR')
    (ℓf : Rf ⋙ ΓR ≅ Γf ⋙ I) (ℓf' : Rf' ⋙ ΓR' ≅ Γf' ⋙ I') (ℓg : Rg ⋙ ΓR ≅ ΓR' ⋙ Φ)
    (ℓg' : Rg' ⋙ Γf ≅ Γf' ⋙ Φ) (cmp : Rg' ⋙ Rf ⟶ Rf' ⋙ Rg)
    (cA : Rg' ⋙ Rf ≅ Rk) (cB : Rf' ⋙ Rg ≅ Rk') (LA : Rk ⋙ ΓR ≅ Γf' ⋙ Φ)
    (LB : Rk' ⋙ ΓR ≅ Γf' ⋙ Φ) (rA : Φ ⋙ I ≅ Φ) (rB : I' ⋙ Φ ≅ Φ) (M : DX')
    (pF : Rk = Rk')
    (hA : LA.hom.app M = ΓR.map (cA.inv.app M) ≫ ℓf.hom.app (Rg'.obj M) ≫
      I.map (ℓg'.hom.app M) ≫ rA.hom.app (Γf'.obj M))
    (hB : LB.hom.app M = ΓR.map (cB.inv.app M) ≫ ℓg.hom.app (Rf'.obj M) ≫
      Φ.map (ℓf'.hom.app M) ≫ rB.hom.app (Γf'.obj M))
    (hT : LA.hom.app M ≍ LB.hom.app M)
    (hcmp : cmp = cA.hom ≫ eqToHom pF ≫ cB.inv)
    (h₂ : rA.hom.app (Γf'.obj M) = e.hom.app (Φ.obj (Γf'.obj M)))
    (h₃ : rB.hom.app (Γf'.obj M) = Φ.map (e'.hom.app (Γf'.obj M))) :
    LerayBaseChangeCompat e e' ℓf ℓf' ℓg ℓg' cmp M := by
  unfold LerayBaseChangeCompat
  subst pF
  have hcmp' : cmp.app M = cA.hom.app M ≫ cB.inv.app M := by
    rw [hcmp, eqToHom_refl, Category.id_comp, NatTrans.comp_app]
  have hA' : ΓR.map (cA.hom.app M) ≫ LA.hom.app M = ℓf.hom.app (Rg'.obj M) ≫
      I.map (ℓg'.hom.app M) ≫ rA.hom.app (Γf'.obj M) := by
    rw [hA, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
  rw [← h₂, ← hA', eq_of_heq hT, hB, hcmp', h₃, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]

/-- **Invertibility transported along compatible Leray identifications**, at variable
functors. With the Leray identifications of `baseChange_leray_compat`, satisfying its
conclusion `hAB`, a base change map `bc : Lg Rf K ⟶ Rf' Lg' K` transposed along `Lg ⊣ Rg` to
`Rf(η'_K) ≫ cmp` (`hu`), and a map `h : Lg' K ⟶ M` with `bc ≫ Rf' h` invertible: if the
transpose under `Lφ ⊣ Φ` of the map `ΓR(η_P) ≫ ℓg` at `P = Rf K` is invertible, so is the
transpose of `Γf(η'_K ≫ Rg' h) ≫ ℓg'`. -/
theorem isIso_homEquiv_symm_of_baseChange {Lg' : DX ⥤ DX'} {Lg : DS ⥤ DS'}
    (adjg' : Lg' ⊣ Rg') (adjg : Lg ⊣ Rg) {Lφ : MR ⥤ MR'} (adjφ : Lφ ⊣ Φ)
    (e : I ≅ 𝟭 MR) (e' : I' ≅ 𝟭 MR')
    (ℓf : Rf ⋙ ΓR ≅ Γf ⋙ I) (ℓf' : Rf' ⋙ ΓR' ≅ Γf' ⋙ I') (ℓg : Rg ⋙ ΓR ≅ ΓR' ⋙ Φ)
    (ℓg' : Rg' ⋙ Γf ≅ Γf' ⋙ Φ) (cmp : Rg' ⋙ Rf ⟶ Rf' ⋙ Rg)
    (K : DX) (M : DX') (h : Lg'.obj K ⟶ M) (bc : Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K))
    (hu : Rf.map (adjg'.unit.app K) ≫ cmp.app (Lg'.obj K) =
      adjg.unit.app (Rf.obj K) ≫ Rg.map bc)
    (hAB : LerayBaseChangeCompat e e' ℓf ℓf' ℓg ℓg' cmp M)
    (hD1 : IsIso ((adjφ.homEquiv _ _).symm
      (ΓR.map (adjg.unit.app (Rf.obj K)) ≫ ℓg.hom.app (Lg.obj (Rf.obj K)))))
    (hbc : IsIso (bc ≫ Rf'.map h)) :
    IsIso ((adjφ.homEquiv _ _).symm
      (Γf.map (adjg'.unit.app K ≫ Rg'.map h) ≫ ℓg'.hom.app M)) := by
  let ι := ℓf.app K ≪≫ e.app (Γf.obj K)
  let b := ℓf'.app M ≪≫ e'.app (Γf'.obj M)
  have key : ι.hom ≫ Γf.map (adjg'.unit.app K ≫ Rg'.map h) ≫ ℓg'.hom.app M =
      (ΓR.map (adjg.unit.app (Rf.obj K)) ≫ ℓg.hom.app (Lg.obj (Rf.obj K))) ≫
        Φ.map (ΓR'.map (bc ≫ Rf'.map h) ≫ b.hom) := by
    have h₁ := e.hom.naturality (Γf.map (adjg'.unit.app K ≫ Rg'.map h) ≫ ℓg'.hom.app M)
    have h₂ := ℓf.hom.naturality (adjg'.unit.app K ≫ Rg'.map h)
    have h₃ := cmp.naturality h
    have h₄ := ℓg.hom.naturality (bc ≫ Rf'.map h)
    simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at h₁ h₂ h₃ h₄
    have h₅ : Rf.map (adjg'.unit.app K ≫ Rg'.map h) ≫ cmp.app M =
        adjg.unit.app (Rf.obj K) ≫ Rg.map (bc ≫ Rf'.map h) := by
      rw [Functor.map_comp, Category.assoc, h₃, ← Category.assoc, hu, Category.assoc,
        ← Rg.map_comp]
    simp only [ι, b, Iso.trans_hom, Iso.app_hom, Category.assoc]
    calc ℓf.hom.app K ≫ e.hom.app (Γf.obj K) ≫ Γf.map (adjg'.unit.app K ≫ Rg'.map h) ≫
          ℓg'.hom.app M
        = (ℓf.hom.app K ≫ I.map (Γf.map (adjg'.unit.app K ≫ Rg'.map h))) ≫
            I.map (ℓg'.hom.app M) ≫ e.hom.app (Φ.obj (Γf'.obj M)) := by
          rw [← h₁, Functor.map_comp]
          simp only [Category.assoc]
      _ = ΓR.map (Rf.map (adjg'.unit.app K ≫ Rg'.map h)) ≫ ΓR.map (cmp.app M) ≫
            ℓg.hom.app (Rf'.obj M) ≫ Φ.map (ℓf'.hom.app M ≫ e'.hom.app (Γf'.obj M)) := by
          rw [← h₂, Category.assoc, show _ = _ from hAB]
      _ = ΓR.map (adjg.unit.app (Rf.obj K)) ≫ ΓR.map (Rg.map (bc ≫ Rf'.map h)) ≫
            ℓg.hom.app (Rf'.obj M) ≫ Φ.map (ℓf'.hom.app M ≫ e'.hom.app (Γf'.obj M)) := by
          rw [← Functor.map_comp_assoc, h₅, Functor.map_comp_assoc]
      _ = _ := by
          rw [reassoc_of% h₄]
          simp only [Functor.map_comp, Category.assoc]
  have hΨ : Γf.map (adjg'.unit.app K ≫ Rg'.map h) ≫ ℓg'.hom.app M = ι.inv ≫
      (ΓR.map (adjg.unit.app (Rf.obj K)) ≫ ℓg.hom.app (Lg.obj (Rf.obj K))) ≫
        Φ.map (ΓR'.map (bc ≫ Rf'.map h) ≫ b.hom) := by
    rw [← key, Iso.inv_hom_id_assoc]
  rw [hΨ, Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm]
  have := hbc
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hD1 inferInstance)

end CategoryTheory

namespace AlgebraicGeometry

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

/-! ### Quasi-coherence of the derived pushforward -/

/-- **Part (1) of [Stacks, Tag 08D5] for the derived pushforward of ringed spaces, at every
model.** For a quasi-compact quasi-separated morphism of schemes `f : X ⟶ Y` and an object `E`
of `D(𝒪_X)` with quasi-coherent cohomology sheaves, the cohomology sheaves of `Rf_* E` are
quasi-coherent. Here `Rf_*` is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward`, the right adjoint of
[Stacks, Tag 079W]. -/
theorem isQuasicoherent_homology_derivedPushforward_ringedSpace_of_qcqs {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj E).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
      i).obj ((derivedPushforward f.toLRSHom.toShHom).obj E)).IsQuasicoherent := by
  let C := SheafOfModules.{u} (structureSheafRing X.toRingedSpace)
  let K := DerivedCategory.Q.objPreimage E
  let eQ : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have hK : ∀ n : ℤ, (K.homology n).IsQuasicoherent := fun n =>
    (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)).prop_of_iso
      (((DerivedCategory.homologyFunctor C n).mapIso eQ).symm ≪≫
        (DerivedCategory.homologyFunctorFactors C n).app K) (hE n)
  obtain ⟨I, s, hI, hs⟩ := exists_quasiIso_isKInjective X.toRingedSpace K
  have hsQ : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := C) s).2 hs
  have hu := isIso_derivedPushforwardUnit_app_of_isKInjective f.toLRSHom.toShHom I hI
  let eE : DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I) ≅ E :=
    (DerivedCategory.quotientCompQhIso C).app I ≪≫ (asIso (DerivedCategory.Q.map s)).symm ≪≫ eQ
  exact (SheafOfModules.isQuasicoherent (structureSheafRing Y.toRingedSpace)).prop_of_iso
    (((DerivedCategory.homologyFunctorFactors _ i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso
        (((DerivedCategory.quotientCompQhIso _).app _).symm ≪≫
          @asIso _ _ _ _ ((derivedPushforwardUnit f.toLRSHom.toShHom).app
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)) hu ≪≫
          (derivedPushforward f.toLRSHom.toShHom).mapIso eE))
    (isQuasicoherent_homology_modulePushforward_of_qcqs_anyTarget f hK s hI hs i)

/-! ### Restriction of scalars along the identity -/

/-- A functor carries the componentwise inverse followed by the forward map of an isomorphism of
functors to the identity. -/
private theorem map_inv_app_comp_map_hom_app {C D E : Type*} [Category C] [Category D]
    [Category E] (F : D ⥤ E) {G H : C ⥤ D} (α : G ≅ H) (X : C) :
    F.map (α.inv.app X) ≫ F.map (α.hom.app X) = 𝟙 _ := by
  rw [← F.map_comp, α.inv_hom_id_app, F.map_id]

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The inverse of `AlgebraicGeometry.restrictScalarsIdDerivedIso` at the class of a complex: the
canonical factorization of derived restriction of scalars, followed by the degreewise comparison
`AlgebraicGeometry.restrictScalarsIdComplexIso`. -/
theorem restrictScalarsIdDerivedIso_inv_app_Q (R : Type u) [CommRing R]
    (E : CochainComplex (ModuleCat.{u} R) ℤ) :
    (restrictScalarsIdDerivedIso (RingHom.id R) rfl).inv.app (DerivedCategory.Q.obj E) =
      (ModuleCat.restrictScalars.{u} (RingHom.id R)).mapDerivedCategoryFactors.hom.app E ≫
        DerivedCategory.Q.map
          (X := ((ModuleCat.restrictScalars.{u} (RingHom.id R)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E) (Y := E)
          ((restrictScalarsIdComplexIso (RingHom.id R) rfl).hom.app E) := by
  rw [← cancel_epi ((restrictScalarsIdDerivedIso (RingHom.id R) rfl).hom.app
    (DerivedCategory.Q.obj E)), Iso.hom_inv_id_app, restrictScalarsIdDerivedIso_hom_app_Q,
    Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  rfl

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`derivedRestrictScalarsComp` with the identity first is `restrictScalarsIdDerivedIso`.** For
`φ : R ⟶ R'`, the comparison `φ^* ⋙ (id_R)^* ≅ φ^*` of
`StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp` is
`AlgebraicGeometry.restrictScalarsIdDerivedIso` at `φ^* Y`. -/
theorem derivedRestrictScalarsComp_id_left_hom_app {R R' : Type u} [CommRing R] [CommRing R']
    (φ : R →+* R') (w : φ = φ.comp (RingHom.id R)) (Y : DerivedCategory (ModuleCat.{u} R')) :
    (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} (RingHom.id R) φ φ w).hom.app
        Y =
      (restrictScalarsIdDerivedIso (RingHom.id R) rfl).inv.app
        ((ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.obj Y) := by
  suffices H : (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
      (RingHom.id R) φ φ w).hom =
      Functor.whiskerLeft (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory
        (restrictScalarsIdDerivedIso (RingHom.id R) rfl).inv by
    simpa using NatTrans.congr_app H Y
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R') (ComplexShape.up ℤ)) (fun E => ?_)
  have hF := StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp_factors.{u, u}
    (RingHom.id R) φ φ w E
  have he := restrictScalarsIdDerivedIso_inv_app_Q R
    (((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex _).obj E)
  have hn := (restrictScalarsIdDerivedIso (RingHom.id R) rfl).inv.naturality
    ((ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors.hom.app E)
  have hc : (StacksDraft.DerivedInverseLimit.restrictScalarsComplexComp.{u, u}
      (RingHom.id R) φ φ w).hom.app E =
      (restrictScalarsIdComplexIso (RingHom.id R) rfl).hom.app
        (((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex _).obj E) := by
    ext n x
    rfl
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map] at hn he
  simp only [Functor.whiskerLeft_app]
  have h₂ : (restrictScalarsIdDerivedIso (RingHom.id R) rfl).inv.app
      ((ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.obj (DerivedCategory.Q.obj E)) =
      ((ModuleCat.restrictScalars.{u} (RingHom.id R)).mapDerivedCategory.map
          ((ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors.hom.app E) ≫
        (restrictScalarsIdDerivedIso (RingHom.id R) rfl).inv.app
          (DerivedCategory.Q.obj
            (((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex _).obj E))) ≫
          (ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors.inv.app E := by
    rw [hn]
    simp
  rw [← cancel_epi ((ModuleCat.restrictScalars.{u} (RingHom.id R)).mapDerivedCategoryFactors.inv.app
      (((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex _).obj E) ≫
    (ModuleCat.restrictScalars.{u} (RingHom.id R)).mapDerivedCategory.map
      ((ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors.inv.app E)), Category.assoc,
    hF, h₂, he, hc]
  simp only [Category.assoc, reassoc_of%
    (map_inv_app_comp_map_hom_app (ModuleCat.restrictScalars.{u} (RingHom.id R)).mapDerivedCategory
      (ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors E),
    Iso.inv_hom_id_app_assoc]

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`derivedRestrictScalarsComp` with the identity second is `φ^*` of
`restrictScalarsIdDerivedIso`.** For `φ : R ⟶ R'`, the comparison `(id_{R'})^* ⋙ φ^* ≅ φ^*` of
`StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp` is `φ^*` of
`AlgebraicGeometry.restrictScalarsIdDerivedIso`. -/
theorem derivedRestrictScalarsComp_id_right_hom_app {R R' : Type u} [CommRing R] [CommRing R']
    (φ : R →+* R') (w : φ = (RingHom.id R').comp φ) (Y : DerivedCategory (ModuleCat.{u} R')) :
    (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} φ (RingHom.id R') φ
        w).hom.app Y =
      (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.map
        ((restrictScalarsIdDerivedIso (RingHom.id R') rfl).inv.app Y) := by
  suffices H : (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
      φ (RingHom.id R') φ w).hom =
      Functor.whiskerRight (restrictScalarsIdDerivedIso (RingHom.id R') rfl).inv
        (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory by
    simpa using NatTrans.congr_app H Y
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R') (ComplexShape.up ℤ)) (fun E => ?_)
  have hF := StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp_factors.{u, u}
    φ (RingHom.id R') φ w E
  have he := restrictScalarsIdDerivedIso_inv_app_Q R' E
  have hc : (StacksDraft.DerivedInverseLimit.restrictScalarsComplexComp.{u, u}
      φ (RingHom.id R') φ w).hom.app E =
      ((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex _).map
        ((restrictScalarsIdComplexIso (RingHom.id R') rfl).hom.app E) := by
    ext n x
    rfl
  have hi := ((ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors.inv.naturality
    ((restrictScalarsIdComplexIso (RingHom.id R') rfl).hom.app E)).symm
  simp only [Functor.comp_obj, Functor.comp_map] at hi
  simp only [Functor.whiskerRight_app]
  rw [← cancel_epi ((ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors.inv.app
      (((ModuleCat.restrictScalars.{u} (RingHom.id R')).mapHomologicalComplex _).obj E) ≫
    (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.map
      ((ModuleCat.restrictScalars.{u} (RingHom.id R')).mapDerivedCategoryFactors.inv.app E)),
    Category.assoc, hF, he, hc, Functor.map_comp]
  simp only [Category.assoc]
  convert hi.symm using 3 <;> first | rfl | exact (reassoc_of%
    (map_inv_app_comp_map_hom_app (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory
      (ModuleCat.restrictScalars.{u} (RingHom.id R')).mapDerivedCategoryFactors E)) _

/-! ### The main result -/

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The linear Leray identifications of
`AlgebraicGeometry.derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso` along two
equal morphisms `k₁ = k₂` agree, as morphisms with (equal but not syntactically equal) sources.
-/
theorem derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso_congr_hom_app
    {A A' : Type u} [CommRing A] [CommRing A'] {X X' : Scheme.{u}} {k₁ k₂ : X' ⟶ X}
    (hk : k₁ = k₂) (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of A')) (φ : A →+* A')
    (h₁ : k₁ ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))
    (h₂ : k₂ ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ)) (M : DerivedCategory X'.Modules) :
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso k₁ f f' φ h₁).hom.app M ≍
      (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso k₂ f f' φ h₂).hom.app M := by
  subst hk
  rfl

/-- A scheme `f : X ⟶ Spec R` lies over `Spec R` along the identity of `R`. -/
theorem comp_id_eq_comp_specMap_id {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) :
    f ≫ 𝟙 (Spec (.of R)) = f ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
  rw [show CommRingCat.ofHom (RingHom.id R) = 𝟙 (CommRingCat.of R) from rfl, Spec.map_id]

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The Leray identifications of a square over `Spec R' ⟶ Spec R` are compatible.** For
`X' --g'--> X` over `Spec R' --Spec φ--> Spec R` via `f'` and `f`, the Leray identification of
`g'`, read over `R` through the Leray identification `RΓ(X, -) = RΓ(Spec R, Rf_* -)` of `f`, is
the comparison `Rf_* Rg'_* ⟶ Rg_* Rf'_*` of the two iterated derived pushforwards followed by the
Leray identifications of `g = Spec φ` and of `f'`. -/
theorem derivedGlobalSectionsOver_leray_baseChange_compat
    {R R' : Type u} [CommRing R] [CommRing R'] (φ : R →+* R') {X X' : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (f' : X' ⟶ Spec (.of R')) (g' : X' ⟶ X)
    (sq : g' ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ)) (M : DerivedCategory X'.Modules) :
    CategoryTheory.LerayBaseChangeCompat (restrictScalarsIdDerivedIso (RingHom.id R) rfl).symm
      (restrictScalarsIdDerivedIso (RingHom.id R') rfl).symm
      (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso f (𝟙 _) f (RingHom.id R)
        (comp_id_eq_comp_specMap_id f))
      (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso f' (𝟙 _) f' (RingHom.id R')
        (comp_id_eq_comp_specMap_id f'))
      (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso
        (Spec.map (CommRingCat.ofHom φ)) (𝟙 _) (𝟙 _) φ (specMap_comp_id_eq φ))
      (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso g' f f' φ sq)
      (Stacks.Cohomology.DerivedBaseChange.Mate.derivedPushforwardComparisonSquare
        (derivedAdjunction f.toLRSHom.toShHom) (derivedAdjunction f'.toLRSHom.toShHom)
        (derivedAdjunction (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)
        (derivedAdjunction g'.toLRSHom.toShHom)
        (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g'.toLRSHom.toShHom
          f'.toLRSHom.toShHom f.toLRSHom.toShHom (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom
          (congrArg (fun k => k.toLRSHom.toShHom) sq))
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g'.toLRSHom.toShHom
          f.toLRSHom.toShHom)).natTrans M := by
  let g := Spec.map (CommRingCat.ofHom φ)
  have sq' : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom := congrArg (fun k => k.toLRSHom.toShHom) sq
  have hk' : (g' ≫ f) ≫ 𝟙 (Spec (.of R)) = f' ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [Category.comp_id, sq]
  have hk'' : (f' ≫ g) ≫ 𝟙 (Spec (.of R)) = f' ≫ Spec.map (CommRingCat.ofHom φ) :=
    Category.comp_id _
  have hA := derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso_comp g' f
    (𝟙 (Spec (.of R))) f f' (RingHom.id R) φ φ (RingHom.comp_id φ).symm
    (comp_id_eq_comp_specMap_id f) sq hk' M
  have hB := derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso_comp f' g
    (𝟙 (Spec (.of R))) (𝟙 (Spec (.of R'))) f' φ (RingHom.id R') φ (RingHom.id_comp φ).symm
    (specMap_comp_id_eq φ) (comp_id_eq_comp_specMap_id f') hk'' M
  have hT := derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso_congr_hom_app sq
    (𝟙 (Spec (.of R))) f' φ hk' hk'' M
  have hcmp :=
    Stacks.Cohomology.DerivedBaseChange.derivedPushforwardComparisonSquare_natTrans_eq_compIso
      g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq'
  have h₂ := derivedRestrictScalarsComp_id_left_hom_app φ (RingHom.comp_id φ).symm
    ((derivedGlobalSectionsOver f').obj M)
  have h₃ := derivedRestrictScalarsComp_id_right_hom_app φ (RingHom.id_comp φ).symm
    ((derivedGlobalSectionsOver f').obj M)
  exact CategoryTheory.baseChange_leray_compat (restrictScalarsIdDerivedIso (RingHom.id R) rfl).symm
    (restrictScalarsIdDerivedIso (RingHom.id R') rfl).symm
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso f (𝟙 _) f (RingHom.id R)
      (comp_id_eq_comp_specMap_id f))
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso f' (𝟙 _) f' (RingHom.id R')
      (comp_id_eq_comp_specMap_id f'))
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso g (𝟙 _) (𝟙 _) φ
      (specMap_comp_id_eq φ))
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso g' f f' φ sq)
    (Stacks.Cohomology.DerivedBaseChange.Mate.derivedPushforwardComparisonSquare
      (derivedAdjunction f.toLRSHom.toShHom) (derivedAdjunction f'.toLRSHom.toShHom)
      (derivedAdjunction g.toLRSHom.toShHom) (derivedAdjunction g'.toLRSHom.toShHom)
      (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g'.toLRSHom.toShHom
        f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq')
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g'.toLRSHom.toShHom
        f.toLRSHom.toShHom)).natTrans
    (derivedPushforwardCompIso g'.toLRSHom.toShHom f.toLRSHom.toShHom)
    (derivedPushforwardCompIso f'.toLRSHom.toShHom g.toLRSHom.toShHom)
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (g' ≫ f) (𝟙 _) f' φ hk')
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (f' ≫ g) (𝟙 _) f' φ hk'')
    (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} (RingHom.id R) φ φ
      (RingHom.comp_id φ).symm)
    (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} φ (RingHom.id R') φ
      (RingHom.id_comp φ).symm)
    M _ hA hB hT hcmp h₂ h₃

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `CategoryTheory.isIso_homEquiv_symm_of_baseChange` for the derived base change map
`Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap` of a square of derived
adjunctions on ringed spaces, whose transpose along the bottom is
`Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap_unit_fac`. Stated at variable
functors. -/
theorem isIso_homEquiv_symm_of_derivedBaseChangeMap {X' X S' S : RingedSpace.{u, u}}
    {Lf : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {Lg : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))}
    {Lf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing S')) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    {Lg' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    {Lc : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    {Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
    {Rf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))}
    {Rg : DerivedCategory (SheafOfModules.{u} (structureSheafRing S')) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
    {Rg' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg')
    (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
    {MR MR' : Type*} [Category MR] [Category MR']
    {Γf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤ MR}
    {Γf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ⥤ MR'}
    {ΓR : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤ MR}
    {ΓR' : DerivedCategory (SheafOfModules.{u} (structureSheafRing S')) ⥤ MR'}
    {I : MR ⥤ MR} {I' : MR' ⥤ MR'} {Φ : MR' ⥤ MR} {Lφ : MR ⥤ MR'} (adjφ : Lφ ⊣ Φ)
    (e : I ≅ 𝟭 MR) (e' : I' ≅ 𝟭 MR')
    (ℓf : Rf ⋙ ΓR ≅ Γf ⋙ I) (ℓf' : Rf' ⋙ ΓR' ≅ Γf' ⋙ I') (ℓg : Rg ⋙ ΓR ≅ ΓR' ⋙ Φ)
    (ℓg' : Rg' ⋙ Γf ≅ Γf' ⋙ Φ)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))) (h : Lg'.obj K ⟶ M)
    (hAB : CategoryTheory.LerayBaseChangeCompat e e' ℓf ℓf' ℓg ℓg'
      (Stacks.Cohomology.DerivedBaseChange.Mate.derivedPushforwardComparisonSquare adjf adjf'
        adjg adjg' eg ef).natTrans M)
    (hD1 : IsIso ((adjφ.homEquiv _ _).symm
      (ΓR.map (adjg.unit.app (Rf.obj K)) ≫ ℓg.hom.app (Lg.obj (Rf.obj K)))))
    (hbc : IsIso (Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap adjf adjf' eg ef K ≫
      Rf'.map h)) :
    IsIso ((adjφ.homEquiv _ _).symm
      (Γf.map (adjg'.unit.app K ≫ Rg'.map h) ≫ ℓg'.hom.app M)) :=
  CategoryTheory.isIso_homEquiv_symm_of_baseChange adjg' adjg adjφ e e' ℓf ℓf' ℓg ℓg'
    (Stacks.Cohomology.DerivedBaseChange.Mate.derivedPushforwardComparisonSquare adjf adjf'
      adjg adjg' eg ef).natTrans K M h
    (Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap adjf adjf' eg ef K)
    (Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap_unit_fac adjf adjf' adjg adjg'
      eg ef K) hAB hD1 hbc

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`RΓ(X, K) ⊗_R^𝐋 R' ≅ RΓ(X', M)`, from base change of the derived pushforward.** Let
`X' --g'--> X` lie over `Spec R' --Spec φ--> Spec R` via `f'` and `f` (the square `sq`), with `f`
quasi-compact and quasi-separated, let `K` be an object of `D(𝒪_X)` with quasi-coherent
cohomology sheaves, `M` an object of `D(𝒪_{X'})` and `h : Lg'^* K ⟶ M`. If the derived base change
map `Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` of [Stacks, Tag 08HY] followed by `Rf'_* h` is an isomorphism,
then so is the derived base-change map

`RΓ(X, K) ⊗_R^𝐋 R' ⟶ RΓ(X', M)`

adjoint to `RΓ(X, K) ⟶ RΓ(X, Rg'_* Lg'^* K) ⟶ RΓ(X, Rg'_* M) = φ^* RΓ(X', M)`, the image of the
unit of `Lg'^* ⊣ Rg'_*` and of `Rg'_* h`, followed by the linear Leray identification.

No cartesian hypothesis on the square is needed. -/
theorem isIso_derivedBaseChangeComparison_of_isIso_derivedBaseChangeMap
    {R R' : Type u} [CommRing R] [CommRing R'] (φ : R →+* R') {X X' : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [QuasiCompact f] [QuasiSeparated f] (f' : X' ⟶ Spec (.of R'))
    (g' : X' ⟶ X) (sq : g' ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))
    (K : DerivedCategory X.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj K).IsQuasicoherent)
    (M : DerivedCategory X'.Modules) (h : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ M)
    (hbc : IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g'.toLRSHom.toShHom
      f'.toLRSHom.toShHom f.toLRSHom.toShHom (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom
      (congrArg (fun k => k.toLRSHom.toShHom) sq) K ≫
        (derivedPushforward f'.toLRSHom.toShHom).map h)) :
    IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, u, u} φ
      ((derivedGlobalSectionsOver f).map
          ((derivedAdjunction g'.toLRSHom.toShHom).unit.app K ≫
            (derivedPushforward g'.toLRSHom.toShHom).map h) ≫
        (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso g' f f' φ sq).hom.app
          M)) := by
  let g := Spec.map (CommRingCat.ofHom φ)
  have sq' : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom := congrArg (fun k => k.toLRSHom.toShHom) sq
  let P : DerivedCategory (Spec (.of R)).Modules := (derivedPushforward f.toLRSHom.toShHom).obj K
  have hP : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj P).IsQuasicoherent :=
    isQuasicoherent_homology_derivedPushforward_ringedSpace_of_qcqs f K hK
  have hD1 := isIso_derivedBaseChangeComparison_affineBaseChangeMap φ P hP
  have hAB := derivedGlobalSectionsOver_leray_baseChange_compat φ f f' g' sq M
  exact isIso_homEquiv_symm_of_derivedBaseChangeMap (derivedAdjunction f.toLRSHom.toShHom)
    (derivedAdjunction f'.toLRSHom.toShHom) (derivedAdjunction g.toLRSHom.toShHom)
    (derivedAdjunction g'.toLRSHom.toShHom)
    (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g'.toLRSHom.toShHom
      f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq')
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g'.toLRSHom.toShHom
      f.toLRSHom.toShHom) _
    (restrictScalarsIdDerivedIso (RingHom.id R) rfl).symm
    (restrictScalarsIdDerivedIso (RingHom.id R') rfl).symm
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso f (𝟙 _) f (RingHom.id R)
      (comp_id_eq_comp_specMap_id f))
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso f' (𝟙 _) f' (RingHom.id R')
      (comp_id_eq_comp_specMap_id f'))
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso g (𝟙 _) (𝟙 _) φ
      (specMap_comp_id_eq φ))
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso g' f f' φ sq)
    K M h hAB hD1 hbc

end AlgebraicGeometry

end
