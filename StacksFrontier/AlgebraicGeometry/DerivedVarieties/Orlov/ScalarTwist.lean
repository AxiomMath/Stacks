module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.BoxPairings
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverField.SpecFieldScalars
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ConvolutionPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
public import StacksFrontier.CategoryTheory.Linear.ScalarObjectBiproducts
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.Counterexample

/-!
# A linear functor of perfect complexes commutes with twisting by vector spaces

Let `k` be a field, `X` and `Y` schemes over `k` with structure morphisms `f` and `g`, and
`F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` a `k`-linear functor. For a perfect `V` on `Spec k` write
`V ⊗ G = L f^* V ⊗^𝐋 G`. Then `F(V ⊗ G) ≅ V ⊗ F(G)` naturally in `G`, and naturally in `V` for
morphisms between finite direct sums of copies of `𝒪_{Spec k}[0]`. This is the identification
`F(Γ(X, 𝓕 ⊗ ℰᵢ) ⊗_k 𝒢ᵢ) = Γ(X, 𝓕 ⊗ ℰᵢ) ⊗_k F(𝒢ᵢ)` of [Stacks, Section 0G07].

## Main definitions

* `AlgebraicGeometry.perfectTwist`: `G ↦ L f^* V ⊗^𝐋 G` on `D_perf(𝒪_X)`.
* `AlgebraicGeometry.twistThenApply`, `AlgebraicGeometry.applyThenTwist`: the functors
  `Φ₁ : V ↦ (G ↦ F(V ⊗ G))` and `Φ₂ : V ↦ (G ↦ V ⊗ F(G))` from `D_perf(𝒪_{Spec k})` to the
  category of functors `D_perf(𝒪_X) ⥤ D(𝒪_Y)`.

## Main results

* `AlgebraicGeometry.twistApply_comm`: for finite direct sums `V`, `V'` of copies of
  `𝒪_{Spec k}[0]`, the isomorphisms `F(V ⊗ -) ≅ V ⊗ F(-)` commute with the maps induced by any
  `φ : V ⟶ V'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

variable {k : Type u} [Field k]

section Twist

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- `G ↦ L f^* V ⊗^𝐋 G` on perfect complexes, for a perfect `V` on `Spec k`. -/
def perfectTwist (V : PerfectDerivedCategory (Spec (.of k))) :
    PerfectDerivedCategory X ⥤ PerfectDerivedCategory X :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj
      ((dpull f).obj V.obj))
    (fun G ↦ isPerfect_dtenR _ _
      (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback.{u} _ _ V.property) G.property)

/-- The morphism of twists induced by a morphism of perfect complexes on `Spec k`. -/
def perfectTwistMap {V V' : PerfectDerivedCategory (Spec (.of k))} (φ : V ⟶ V') :
    perfectTwist f V ⟶ perfectTwist f V' where
  app G := ObjectProperty.homMk
    (((derivedTensorProductFunctor X.toRingedSpace.sheaf).map ((dpull f).map φ.hom)).app G.obj)
  naturality G G' γ := by
    ext
    exact ((derivedTensorProductFunctor X.toRingedSpace.sheaf).map
      ((dpull f).map φ.hom)).naturality γ.hom

/-- The twist `L f^* V ⊗^𝐋 -` induced by the identity of `V` is the identity. -/
theorem tensorMap_dpullMap_id (V : PerfectDerivedCategory (Spec (.of k))) :
    (derivedTensorProductFunctor X.toRingedSpace.sheaf).map ((dpull f).map (𝟙 V : V ⟶ V).hom) =
      𝟙 _ :=
  (congrArg (derivedTensorProductFunctor X.toRingedSpace.sheaf).map
    ((dpull f).map_id V.obj)).trans ((derivedTensorProductFunctor X.toRingedSpace.sheaf).map_id _)

/-- The twist `L f^* (-) ⊗^𝐋 -` sends a composite `φ ≫ ψ` to the composite of the twists. -/
theorem tensorMap_dpullMap_comp {V V' V'' : PerfectDerivedCategory (Spec (.of k))} (φ : V ⟶ V')
    (ψ : V' ⟶ V'') :
    (derivedTensorProductFunctor X.toRingedSpace.sheaf).map ((dpull f).map (φ ≫ ψ).hom) =
      (derivedTensorProductFunctor X.toRingedSpace.sheaf).map ((dpull f).map φ.hom) ≫
        (derivedTensorProductFunctor X.toRingedSpace.sheaf).map ((dpull f).map ψ.hom) :=
  (congrArg (derivedTensorProductFunctor X.toRingedSpace.sheaf).map
    ((dpull f).map_comp φ.hom ψ.hom)).trans
      ((derivedTensorProductFunctor X.toRingedSpace.sheaf).map_comp _ _)

/-- `perfectTwistMap` sends the identity of `V` to the identity of `perfectTwist f V`. -/
theorem perfectTwistMap_id (V : PerfectDerivedCategory (Spec (.of k))) :
    perfectTwistMap f (𝟙 V) = 𝟙 _ := by
  ext G
  exact NatTrans.congr_app (tensorMap_dpullMap_id f V) G.obj

/-- `perfectTwistMap` sends a composite `φ ≫ ψ` to the composite of the induced morphisms. -/
theorem perfectTwistMap_comp {V V' V'' : PerfectDerivedCategory (Spec (.of k))} (φ : V ⟶ V')
    (ψ : V' ⟶ V'') : perfectTwistMap f (φ ≫ ψ) = perfectTwistMap f φ ≫ perfectTwistMap f ψ := by
  ext G
  exact NatTrans.congr_app (tensorMap_dpullMap_comp f φ ψ) G.obj

end Twist

section Linearity

variable (Z : Over (Spec (.of k)))

/-- The structure morphism of a `k`-scheme, as a morphism to `Spec k` over `Spec k`. -/
def toSpecFieldOver : Z ⟶ specFieldOver k := Over.homMk Z.hom (by simp)

/-- For `r : k`, `L p^*(r • φ) ⊗^𝐋 C = r • (L p^* φ ⊗^𝐋 C)`, where `p` is the structure morphism
of `Z`. -/
theorem tensorMap_dpullMap_app_smul (r : k) {V V' : DerivedCategory (Spec (.of k)).Modules}
    (φ : V ⟶ V') (C : DerivedCategory Z.left.Modules) :
    letI : Linear k (Spec (.of k)).Modules := modulesLinear k (specFieldOver k)
    letI : Linear k (Stacks.DerivedTensor.RingedSite.Modules Z.left.toRingedSpace.sheaf) :=
      modulesLinear k Z
    ((derivedTensorProductFunctor Z.left.toRingedSpace.sheaf).map
        ((dpull Z.hom).map (r • φ))).app C =
      r • ((derivedTensorProductFunctor Z.left.toRingedSpace.sheaf).map
        ((dpull Z.hom).map φ)).app C := by
  let : Linear k (Spec (.of k)).Modules := modulesLinear k (specFieldOver k)
  let : Linear k (SheafOfModules (structureSheafRing (Spec (.of k)).toRingedSpace)) :=
    modulesLinear k (specFieldOver k)
  let := modulesLinear k Z
  let : Linear k (SheafOfModules (structureSheafRing Z.left.toRingedSpace)) := modulesLinear k Z
  let : Linear k (Stacks.DerivedTensor.RingedSite.Modules Z.left.toRingedSpace.sheaf) :=
    modulesLinear k Z
  have h₁ : (dpull Z.hom).Linear k := derivedPullback_linear k (toSpecFieldOver Z)
  have h₂ := derivedTensor_flip_obj_linear k Z C
  change ((derivedTensorProductFunctor Z.left.toRingedSpace.sheaf).flip.obj C).map
      ((dpull Z.hom).map (r • φ)) =
    r • ((derivedTensorProductFunctor Z.left.toRingedSpace.sheaf).flip.obj C).map
      ((dpull Z.hom).map φ)
  rw [h₁.map_smul]
  exact h₂.map_smul _ _

/-- `L p^*(φ + ψ) ⊗^𝐋 C = L p^* φ ⊗^𝐋 C + L p^* ψ ⊗^𝐋 C`, where `p` is the structure morphism
of `Z`. -/
theorem tensorMap_dpullMap_app_add {V V' : DerivedCategory (Spec (.of k)).Modules}
    (φ ψ : V ⟶ V') (C : DerivedCategory Z.left.Modules) :
    ((derivedTensorProductFunctor Z.left.toRingedSpace.sheaf).map
        ((dpull Z.hom).map (φ + ψ))).app C =
      ((derivedTensorProductFunctor Z.left.toRingedSpace.sheaf).map ((dpull Z.hom).map φ)).app C +
      ((derivedTensorProductFunctor Z.left.toRingedSpace.sheaf).map
        ((dpull Z.hom).map ψ)).app C := by
  change ((derivedTensorProductFunctor Z.left.toRingedSpace.sheaf).flip.obj C).map
      ((dpull Z.hom).map (φ + ψ)) = _
  rw [Functor.map_add]
  exact (derivedTensorFlipAdditive Z.left C).map_add

end Linearity

section Functors

variable {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (F : PerfectDerivedCategory X ⥤ PerfectDerivedCategory Y)

/-- `Φ₁ : V ↦ (G ↦ F(V ⊗ G))`. -/
def twistThenApply :
    PerfectDerivedCategory (Spec (.of k)) ⥤ (PerfectDerivedCategory X ⥤ DerivedCategory Y.Modules)
    where
  obj V := perfectTwist f V ⋙ F ⋙ ObjectProperty.ι _
  map φ := Functor.whiskerRight (perfectTwistMap f φ) (F ⋙ ObjectProperty.ι _)
  map_id V := by
    simp only [perfectTwistMap_id, Functor.whiskerRight_id']
  map_comp φ ψ := by
    simp only [perfectTwistMap_comp, Functor.whiskerRight_comp]

/-- `Φ₂ : V ↦ (G ↦ V ⊗ F(G))`. -/
def applyThenTwist :
    PerfectDerivedCategory (Spec (.of k)) ⥤ (PerfectDerivedCategory X ⥤ DerivedCategory Y.Modules)
    where
  obj V := F ⋙ ObjectProperty.ι _ ⋙ (derivedTensorProductFunctor Y.toRingedSpace.sheaf).obj
    ((dpull g).obj V.obj)
  map φ := Functor.whiskerLeft (F ⋙ ObjectProperty.ι _)
    ((derivedTensorProductFunctor Y.toRingedSpace.sheaf).map ((dpull g).map φ.hom))
  map_id V := by
    rw [tensorMap_dpullMap_id g V]
    exact Functor.whiskerLeft_id' _
  map_comp φ ψ := by
    rw [tensorMap_dpullMap_comp g φ ψ]
    exact Functor.whiskerLeft_comp _ _ _

end Functors

section Instances

variable (A B : Over (Spec (.of k)))
  (F : PerfectDerivedCategory A.left ⥤ PerfectDerivedCategory B.left)

/-- The functor `applyThenTwist B.hom F` is additive. -/
instance applyThenTwist_additive : (applyThenTwist B.hom F).Additive where
  map_add {_ _ φ ψ} := by
    ext G
    exact tensorMap_dpullMap_app_add B φ.hom ψ.hom _

/-- The functor `applyThenTwist B.hom F` is `k`-linear. -/
theorem applyThenTwist_linear :
    letI : Linear k (Spec (.of k)).Modules := modulesLinear k (specFieldOver k)
    letI : Linear k B.left.Modules := modulesLinear k B
    (applyThenTwist B.hom F).Linear k := by
  let : Linear k (Spec (.of k)).Modules := modulesLinear k (specFieldOver k)
  let : Linear k B.left.Modules := modulesLinear k B
  exact ⟨fun φ r ↦ by
    ext G
    exact tensorMap_dpullMap_app_smul B r φ.hom _⟩

/-- For additive `F`, the functor `twistThenApply A.hom F` is additive. -/
instance twistThenApply_additive [F.Additive] : (twistThenApply A.hom F).Additive where
  map_add {_ _ φ ψ} := by
    ext G
    change (F.map (ObjectProperty.homMk _)).hom =
      (F.map (ObjectProperty.homMk _) + F.map (ObjectProperty.homMk _)).hom
    rw [← F.map_add]
    congr 2
    ext
    exact tensorMap_dpullMap_app_add A φ.hom ψ.hom _

/-- For `k`-linear `F`, the functor `twistThenApply A.hom F` is `k`-linear. -/
theorem twistThenApply_linear [F.Additive]
    (hF : letI := modulesLinear k A; letI := modulesLinear k B; F.Linear k) :
    letI : Linear k (Spec (.of k)).Modules := modulesLinear k (specFieldOver k)
    letI : Linear k B.left.Modules := modulesLinear k B
    (twistThenApply A.hom F).Linear k := by
  let : Linear k (Spec (.of k)).Modules := modulesLinear k (specFieldOver k)
  let : Linear k A.left.Modules := modulesLinear k A
  let : Linear k B.left.Modules := modulesLinear k B
  exact ⟨fun φ r ↦ by
    ext G
    change (F.map (ObjectProperty.homMk _)).hom = (r • F.map (ObjectProperty.homMk _)).hom
    rw [← hF.map_smul]
    congr 2
    ext
    exact tensorMap_dpullMap_app_smul A r φ.hom _⟩

end Instances

section Unit

/-- `L p^*(𝒪[0]) ⊗^𝐋 - ≅ 𝟭`: twisting by the pulled back structure sheaf is the identity. -/
def unitTwistIso {Z S : Scheme.{u}} (p : Z ⟶ S) :
    (derivedTensorProductFunctor Z.toRingedSpace.sheaf).obj ((dpull p).obj
      ((DerivedCategory.singleFunctor S.Modules 0).obj (SheafOfModules.unit S.ringCatSheaf))) ≅
      𝟭 _ :=
  letI := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Z.toRingedSpace.sheaf
  (derivedTensorProductFunctor Z.toRingedSpace.sheaf).mapIso
      (Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso p.toLRSHom.toShHom) ≪≫
    NatIso.ofComponents (fun G ↦ λ_ G) (fun g ↦ leftUnitor_naturality g)

/-- `O_{Spec k}[0]` as a perfect object. -/
abbrev perfectUnitSpecField : PerfectDerivedCategory (Spec (.of k)) :=
  ⟨(DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
    (SheafOfModules.unit (Spec (.of k)).ringCatSheaf), DescentSituation.isPerfect_unitObj _⟩

/-- Twisting perfect complexes by `𝒪_{Spec k}[0]` is the identity. -/
def perfectTwistUnitIso {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    perfectTwist f (perfectUnitSpecField (k := k)) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun G ↦ ObjectProperty.isoMk _ ((unitTwistIso f).app G.obj))
    (fun γ ↦ by
      ext
      exact (unitTwistIso f).hom.naturality γ.hom)

variable {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (F : PerfectDerivedCategory X ⥤ PerfectDerivedCategory Y)

/-- `Φ₁(𝒪[0]) ≅ Φ₂(𝒪[0])`: both are `F` up to the unit isomorphisms. -/
def twistApplyUnitIso :
    (twistThenApply f F).obj (perfectUnitSpecField (k := k)) ≅
      (applyThenTwist g F).obj (perfectUnitSpecField (k := k)) :=
  Functor.isoWhiskerRight (perfectTwistUnitIso f) (F ⋙ ObjectProperty.ι _) ≪≫
    Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (F ⋙ ObjectProperty.ι _) (unitTwistIso g).symm

end Unit

section Main

variable (A B : Over (Spec (.of k)))
  (F : PerfectDerivedCategory A.left ⥤ PerfectDerivedCategory B.left)
  [F.Additive] (hF : letI := modulesLinear k A; letI := modulesLinear k B; F.Linear k)

include hF in
/-- For finite direct sums `V`, `V'` of copies of `𝒪_{Spec k}[0]` and any `φ : V ⟶ V'`, the
isomorphisms `F(V ⊗ -) ≅ V ⊗ F(-)` of [Stacks, Section 0G07] commute with the maps induced by
`φ`. -/
theorem twistApply_comm {V V' : PerfectDerivedCategory (Spec (.of k))} {n m : ℕ}
    (e : V ≅ ⨁ fun _ : Fin n => (perfectUnitSpecField (k := k)))
    (e' : V' ≅ ⨁ fun _ : Fin m => (perfectUnitSpecField (k := k))) (φ : V ⟶ V') :
    letI : Linear k (Spec (.of k)).Modules := modulesLinear k (specFieldOver k)
    (twistThenApply A.hom F).map φ ≫ (Linear.scalarBiproductIso (twistThenApply A.hom F)
        (applyThenTwist B.hom F) (twistApplyUnitIso A.hom B.hom F) e').hom =
      (Linear.scalarBiproductIso (twistThenApply A.hom F) (applyThenTwist B.hom F)
        (twistApplyUnitIso A.hom B.hom F) e).hom ≫ (applyThenTwist B.hom F).map φ := by
  let : Linear k (Spec (.of k)).Modules := modulesLinear k (specFieldOver k)
  let : Linear k B.left.Modules := modulesLinear k B
  have := twistThenApply_linear A B F hF
  have := applyThenTwist_linear A B F
  have : HasFiniteBiproducts (PerfectDerivedCategory A.left ⥤ DerivedCategory B.left.Modules) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  refine Linear.scalarBiproductIso_comm k (twistThenApply A.hom F) (applyThenTwist B.hom F)
    (twistApplyUnitIso A.hom B.hom F) (fun ψ ↦ ?_) e e' φ
  obtain ⟨r, hr⟩ := exists_eq_smul_id_specFieldOver_single k ψ.hom
  exact ⟨r, by ext; exact hr⟩

end Main

end AlgebraicGeometry
