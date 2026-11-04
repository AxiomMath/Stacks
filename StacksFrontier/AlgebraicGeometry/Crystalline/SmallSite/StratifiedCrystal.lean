module

public import StacksFrontier.AlgebraicGeometry.Crystalline.PairStratification
public import StacksFrontier.AlgebraicGeometry.Crystalline.StratifiedDescent
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineBaseChangeCriterion
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineModuleComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineQuasicoherentSheaf
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceLevelProducts
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceSystemAffine
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.WholeSpaceCosimplicialModule

/-!
# The crystal of a stratified module over the system of [Stacks, Tag 07JN]

The quasi-inverse of the functor of [Stacks, Lemma 60.17.3, Tag 07JG] in the proof of
[Stacks, Proposition 60.17.4, Tag 07JH] attaches to an affine object `(U, T, δ)` of `Cris(X/S)`
with a morphism `f : (U, T, δ) ⟶ (X, T_e, δ)` the module `M ⊗_{D,f} Γ(T, 𝒪_T)`, and compares two
choices of `f` by a comparison `c_{f,g}` satisfying a cocycle condition.  This module does that
descent for an arbitrary stratified module over the system `(X, T(n)_e, δ(n))` of
[Stacks, Tag 07JN] and extends the result from the affine subsite to all of `Cris(X/S)`.

## Main definitions

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `wholeSpaceDescentSystem` — the system of [Stacks, Tag 07JN] as a descent system
  (`Crystalline.StratifiedDescent.System`) on the affine subsite: the levels `T(n)_e` are
  products of `T(0)_e` for affine test objects and every affine object maps to some `T(0)_e`
  ([Stacks, Tag 07HP]).
* `stratAffineSheaf`, `stratSheaf`, `stratCrystal` — the descended sheaf on the affine subsite,
  its extension to `Cris(X/S)` and the resulting crystal in quasi-coherent modules.
* `StratModule`, `stratCrystalFunctor` — the category of stratified modules and the functor to
  `QuasiCoherentCrystal S`.
* `pairStratFunctor` — the Taylor stratification of a pair, as a functor from pairs to stratified
  modules.

## Main results

* `bijective_affineBaseChange_iff_of_iso` — bijectivity of the base changes of sections is
  invariant under isomorphism of presheaves of modules.
* `isQuasicoherentOnSite_stratSheaf` — the sheaf of a stratified module is quasi-coherent.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline.StratifiedDescent

variable (S : GlobalCrystallineSituation.{u}) [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

/-- The ring sheaf of global sections of the ambient schemes, on the affine subsite, valued in
commutative rings. -/
noncomputable abbrev affineSectionsRing : (AffineCrystallineThickening S)ᵒᵖ ⥤ CommRingCat.{u} :=
  (affineι S ⋙ CrystallineThickening.ι S).op ⋙ GlobalCrystallineSituation.structureSheaf S

/-- The level `T(n)_e` of the system of [Stacks, Tag 07JN], as an object of the affine subsite. -/
noncomputable abbrev affineLevel (n e : ℕ) : AffineCrystallineThickening S :=
  ⟨((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e, isAffineObject_wholeSpaceSystem hp n e⟩

/-- The completed envelope `D` of [Stacks, Tag 07J8]. -/
noncomputable abbrev envD : Type u := ((wholeSpaceEnvelopeRing hp).obj ⦋0⦌ : Type u)

/-- **The system of [Stacks, Tag 07JN] as a descent system on the affine subsite**: the levels
`T(0)_e`, `T(1)_e`, `T(2)_e` with their vertices, which are products for affine test objects
(`...SmallSite.bijective_wholeSpaceVertices`), the level maps, the reductions
`D → Γ(T(0)_e, 𝒪)` and the pointings of [Stacks, Tag 07HP]
(`...SmallSite.exists_forall_le_hom_wholeSpaceLevel`). -/
noncomputable abbrev wholeSpaceDescentSystem :
    System (AffineCrystallineThickening S) (affineSectionsRing S) (envD S hp) where
  T0 e := affineLevel S hp 0 e
  T1 e := affineLevel S hp 1 e
  T2 e := affineLevel S hp 2 e
  v e j := ObjectProperty.homMk (wholeSpaceVertex S hp 1 e j)
  w e j := ObjectProperty.homMk (wholeSpaceVertex S hp 2 e j)
  bijective_v A e := by
    have h := bijective_wholeSpaceVertices hp A.property 1 e
    refine ⟨fun x y hxy ↦ ?_, fun g ↦ ?_⟩
    · exact InducedCategory.hom_ext (h.1 (funext fun j ↦ congrArg InducedCategory.Hom.hom
        (congrFun hxy j)))
    · obtain ⟨x, hx⟩ := h.2 fun j ↦ (g j).hom
      exact ⟨ObjectProperty.homMk x, funext fun j ↦ InducedCategory.hom_ext (congrFun hx j)⟩
  bijective_w A e := by
    have h := bijective_wholeSpaceVertices hp A.property 2 e
    refine ⟨fun x y hxy ↦ ?_, fun g ↦ ?_⟩
    · exact InducedCategory.hom_ext (h.1 (funext fun j ↦ congrArg InducedCategory.Hom.hom
        (congrFun hxy j)))
    · obtain ⟨x, hx⟩ := h.2 fun j ↦ (g j).hom
      exact ⟨ObjectProperty.homMk x, funext fun j ↦ InducedCategory.hom_ext (congrFun hx j)⟩
  lev e := ObjectProperty.homMk (((wholeSpaceSystem S hp).obj (op ⦋0⦌)).map
    (homOfLE (Nat.le_succ e)))
  a e := levelSectionsScalars hp ⦋0⦌ e
  a_lev e := by
    ext r
    change ((structureSheaf S).obj.map _).hom (levelSectionsScalars hp ⦋0⦌ (e + 1) r) =
      levelSectionsScalars hp ⦋0⦌ e r
    rw [levelSectionsScalars_eq_envelopeLevelRingLimitEquiv hp ⦋0⦌ (e + 1) r,
      levelSectionsScalars_eq_envelopeLevelRingLimitEquiv hp ⦋0⦌ e r]
    exact (envelopeLevelRingLimitEquiv hp 0
      ((wholeSpaceSystemEnvelopeRingEquiv hp 0).symm r)).property (homOfLE (Nat.le_succ e))
  exists_pointing A := by
    obtain ⟨N, hN⟩ := exists_forall_le_hom_wholeSpaceLevel hp A.property
    exact ⟨N, ⟨ObjectProperty.homMk (hN N le_rfl).some⟩⟩

/-! ### Bijectivity of the affine base change is invariant under isomorphism -/

section Iso

variable {S}

omit [IsAffine S.X] [IsAffine S.S.scheme] in
open scoped TensorProduct in
/-- **An isomorphism of presheaves of modules on the affine subsite intertwines the base changes of
sections**, so bijectivity of one is bijectivity of the other. -/
theorem bijective_affineBaseChange_iff_of_iso {N N' : PresheafOfModules.{u}
      (affineStructureSheaf S).obj} (e : N ≅ N') {A B : AffineCrystallineThickening S}
    (k : A ⟶ B) :
    Function.Bijective (affineBaseChange N k) ↔ Function.Bijective (affineBaseChange N' k) := by
  let eB : N.obj (op B) ≃ₗ[affineSectionRing B] N'.obj (op B) :=
    ((PresheafOfModules.evaluation _ (op B)).mapIso e).toLinearEquiv
  let eA : N.obj (op A) ≃ N'.obj (op A) :=
    ((PresheafOfModules.evaluation _ (op A)).mapIso e).toLinearEquiv.toEquiv
  let α : affineRingAlong k ⊗[affineSectionRing B] N.obj (op B) ≃ₗ[affineRingAlong k]
      affineRingAlong k ⊗[affineSectionRing B] N'.obj (op B) :=
    LinearEquiv.baseChange (affineSectionRing B) (affineRingAlong k) _ _ eB
  have key : ∀ t, affineBaseChange N' k (α t) = eA (affineBaseChange N k t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
        rw [map_zero, map_zero, map_zero]
        exact (map_zero (e.hom.app (op A)).hom).symm
    | tmul r x =>
        rw [LinearEquiv.baseChange_tmul, affineBaseChange_tmul, affineBaseChange_tmul]
        exact (((e.hom.app (op A)).hom.map_smul r _).trans
          (congrArg (r • ·) (PresheafOfModules.naturality_apply e.hom k.op x))).symm
    | add x y hx hy =>
        rw [map_add, map_add, hx, hy, map_add]
        exact (map_add (e.hom.app (op A)).hom _ _).symm
  have hfun : ⇑(affineBaseChange N k) = eA.symm ∘ affineBaseChange N' k ∘ α := by
    funext t
    simp only [Function.comp_apply, key, Equiv.symm_apply_apply]
  rw [hfun, EquivLike.comp_bijective, EquivLike.bijective_comp]

end Iso

/-! ### The sheaf of a stratified module -/

section Sheaf

variable {S hp} {M : Type u} [AddCommGroup M] [Module (envD S hp) M]
  (E : Stratification (wholeSpaceDescentSystem S hp) M)

/-- **The descended presheaf of a stratified module**, on the affine subsite, as a presheaf of
modules over the restriction of `𝒪_{X/S}`. -/
noncomputable def stratAffinePresheaf : PresheafOfModules.{u} (affineStructureSheaf S).obj :=
  E.presheaf

/-- **Its base changes are bijective**, which is `Crystalline.StratifiedDescent.Stratification`
`.bijective_semilinearBaseChange_restrict`. -/
theorem bijective_affineBaseChange_stratAffinePresheaf {A B : AffineCrystallineThickening S}
    (k : A ⟶ B) : Function.Bijective (affineBaseChange (stratAffinePresheaf E) k) :=
  E.bijective_semilinearBaseChange_restrict k

/-- **The descended sheaf of a stratified module** on the affine subsite. -/
noncomputable def stratAffineSheaf : SheafOfModules.{u} (affineStructureSheaf S) :=
  sheafOfBijectiveAffineBaseChange (stratAffinePresheaf E)
    (bijective_affineBaseChange_stratAffinePresheaf E)

/-- **The sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` of a stratified module**: the extension of the
descended sheaf from the affine subsite, `...SmallSite.affineModuleEquivalence`. -/
noncomputable def stratSheaf : SheafOfModules.{u} (structureSheaf S) :=
  (affineModuleEquivalence S).inverse.obj (stratAffineSheaf E)

/-- **The sheaf of a stratified module is quasi-coherent**: its base changes between affine
objects are those of the descended sheaf, which are bijective, and
`...SmallSite.isQuasicoherentOnSite_of_bijective_crysBaseChange` applies. -/
theorem isQuasicoherentOnSite_stratSheaf : (stratSheaf E).IsQuasicoherentOnSite := by
  refine isQuasicoherentOnSite_of_bijective_crysBaseChange _ fun {A B} k hA hB ↦ ?_
  let k' : (⟨A, hA⟩ : AffineCrystallineThickening S) ⟶ ⟨B, hB⟩ := ObjectProperty.homMk k
  let N := (SheafOfModules.forget _).obj ((Stacks.DenseSubsiteModules.moduleRestriction
    (affineTopology S) (smallTopology S) (affineι S) (structureSheaf S)).obj (stratSheaf E))
  have heq : ⇑(crysBaseChange (stratSheaf E) k) = ⇑(affineBaseChange N k') := by
    funext t
    induction t using TensorProduct.induction_on with
    | zero =>
        exact (map_zero (crysBaseChange (stratSheaf E) k)).trans
          (map_zero (affineBaseChange N k')).symm
    | tmul r x => rfl
    | add x y hx hy =>
        exact (map_add (crysBaseChange (stratSheaf E) k) x y).trans
          ((congrArg₂ (· + ·) hx hy).trans (map_add (affineBaseChange N k') x y).symm)
  rw [heq]
  exact (bijective_affineBaseChange_iff_of_iso ((SheafOfModules.forget _).mapIso
    (affineModuleEquivalenceInverseObjRestrictionIso S (stratAffineSheaf E))).symm k').mp
    (bijective_affineBaseChange_stratAffinePresheaf E k')

/-- **The crystal in quasi-coherent modules of a stratified module.** -/
noncomputable def stratCrystal : QuasiCoherentCrystal S where
  obj := stratSheaf E
  property := ⟨isQuasicoherentOnSite_stratSheaf E,
    isSheafCrystal_of_isQuasicoherentOnSite _ (isQuasicoherentOnSite_stratSheaf E)⟩

/-- **The sections of the crystal of a stratified module over an affine object are the descended
sections**, through the counit of `...SmallSite.affineModuleEquivalence`. -/
noncomputable def stratSectionsEquiv (A : AffineCrystallineThickening S) :=
  ((PresheafOfModules.evaluation _ (op A)).mapIso ((SheafOfModules.forget _).mapIso
    (affineModuleEquivalenceInverseObjRestrictionIso S (stratAffineSheaf E)))).toLinearEquiv

/-- The identification of the sections commutes with restriction along a morphism of affine
objects. -/
theorem stratSectionsEquiv_restrict {A A' : AffineCrystallineThickening S} (k : A' ⟶ A)
    (x : (stratSheaf E).val.obj (op A.obj)) :
    stratSectionsEquiv E A' ((stratSheaf E).val.map k.hom.op x) =
      E.restrict k (stratSectionsEquiv E A x) :=
  PresheafOfModules.naturality_apply ((SheafOfModules.forget _).map
    (affineModuleEquivalenceInverseObjRestrictionIso S (stratAffineSheaf E)).hom) k.op x

end Sheaf

/-! ### The category of stratified modules and the functor to crystals -/

/-- **A stratified module over the system of [Stacks, Tag 07JN]**: a module over the completed
envelope `D` with a stratification relative to the levels `T(0)_e`. -/
structure StratModule where
  /-- The module. -/
  carrier : Type u
  /-- Its additive group structure. -/
  [addCommGroup : AddCommGroup carrier]
  /-- Its module structure over `D`. -/
  [module : Module (envD S hp) carrier]
  /-- The stratification. -/
  strat : Stratification (wholeSpaceDescentSystem S hp) carrier

attribute [instance] StratModule.addCommGroup StratModule.module

namespace StratModule

variable {S hp}

/-- A morphism of stratified modules: a `D`-linear map commuting with the stratifications. -/
@[ext] structure Hom (X Y : StratModule S hp) where
  /-- The underlying linear map. -/
  toLinearMap : X.carrier →ₗ[envD S hp] Y.carrier
  /-- It commutes with the stratifications. -/
  comm : ∀ e m, Y.strat.str e (toLinearMap m) =
    LinearMap.lTensor _ toLinearMap (X.strat.str e m)

/-- Stratified modules form a category. -/
noncomputable instance instCategoryStratModule : Category (StratModule S hp) where
  Hom X Y := StratModule.Hom X Y
  id X := ⟨LinearMap.id, fun e m ↦ by rw [LinearMap.lTensor_id]; rfl⟩
  comp {X Y Z} f g := ⟨g.toLinearMap ∘ₗ f.toLinearMap, fun e m ↦ by
    rw [LinearMap.comp_apply, g.comm, f.comm, ← LinearMap.comp_apply (LinearMap.lTensor _ _),
      ← LinearMap.lTensor_comp]⟩
  id_comp f := Hom.ext (LinearMap.id_comp _)
  comp_id f := Hom.ext (LinearMap.comp_id _)
  assoc f g h := Hom.ext (LinearMap.comp_assoc _ _ _)

/-- The linear map underlying the identity morphism is the identity. -/
@[simp] theorem id_toLinearMap (X : StratModule S hp) :
    Hom.toLinearMap (𝟙 X) = LinearMap.id := rfl

/-- The linear map underlying a composite is the composite of the underlying linear maps. -/
@[simp] theorem comp_toLinearMap {X Y Z : StratModule S hp} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.toLinearMap (f ≫ g) = Hom.toLinearMap g ∘ₗ Hom.toLinearMap f := rfl

/-- Two morphisms of stratified modules with the same underlying map are equal. -/
@[ext] theorem hom_ext {X Y : StratModule S hp} {f g : X ⟶ Y}
    (h : Hom.toLinearMap f = Hom.toLinearMap g) : f = g := Hom.ext h

end StratModule

variable {S hp}

/-- The morphism of descended sheaves on the affine subsite induced by a morphism of stratified
modules. -/
noncomputable def stratAffineSheafMap {X Y : StratModule S hp} (f : X ⟶ Y) :
    stratAffineSheaf X.strat ⟶ stratAffineSheaf Y.strat :=
  ⟨X.strat.presheafMap Y.strat (StratModule.Hom.toLinearMap f) (StratModule.Hom.comm f)⟩

/-- **The functor from stratified modules to crystals in quasi-coherent modules on
`Cris(X/S)`.** -/
noncomputable def stratCrystalFunctor : StratModule S hp ⥤ QuasiCoherentCrystal S where
  obj X := stratCrystal X.strat
  map f := ObjectProperty.homMk ((affineModuleEquivalence S).inverse.map (stratAffineSheafMap f))
  map_id X := by
    refine InducedCategory.hom_ext ?_
    change (affineModuleEquivalence S).inverse.map (stratAffineSheafMap (𝟙 X)) = 𝟙 _
    rw [show stratAffineSheafMap (𝟙 X) = 𝟙 _ from
      SheafOfModules.Hom.ext (X.strat.presheafMap_id _), CategoryTheory.Functor.map_id]
  map_comp {X Y Z} f g := by
    refine InducedCategory.hom_ext ?_
    change (affineModuleEquivalence S).inverse.map (stratAffineSheafMap (f ≫ g)) =
      (affineModuleEquivalence S).inverse.map (stratAffineSheafMap f) ≫
        (affineModuleEquivalence S).inverse.map (stratAffineSheafMap g)
    rw [← CategoryTheory.Functor.map_comp]
    congr 1
    exact SheafOfModules.Hom.ext (X.strat.presheafMap_comp Y.strat Z.strat _ _ _ _ _)

/-! ### From pairs to stratified modules -/

section PairFunctor

universe v uI

variable {ι : Type uI} [DecidableEq ι] (T : TaylorData (wholeSpaceDescentSystem S hp) ι)
  {Omega : Type v} [AddCommGroup Omega] [Module (envD S hp) Omega] {dx : ι → Omega}
  {dd : envD S hp → Omega} {coord : ι → (Omega →ₗ[envD S hp] envD S hp)}
  (hc : IsCoordinateDual dx coord)
  (hfamD : IsThetaMonomialFamily (envD S hp) (fun i ↦ T.delta (Finsupp.single i 1))
    (fun K ↦ T.delta K))
  (hdelta : ∀ i f, coord i (dd f) = -T.delta (Finsupp.single i 1) f)

/-- **The Taylor stratification as a functor from pairs to stratified modules.** -/
noncomputable def pairStratFunctor :
    Pair.{u, v, uI, u} T.p (envD S hp) Omega dx dd ⥤ StratModule S hp where
  obj P := ⟨P.carrier, pairStratification T P hc hfamD hdelta⟩
  map {P _} φ := ⟨φ.toLinearMap, pairStr_map T P hc hfamD hdelta φ⟩
  map_id _ := StratModule.hom_ext rfl
  map_comp _ _ := StratModule.hom_ext rfl

end PairFunctor

end Crystalline.GlobalCrystallineSituation.SmallSite

end
