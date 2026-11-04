module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CartesianRestrictModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AssociatedModuleBaseChangeFinalSections
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQcqsPushforward
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.EtaleRestrictModulePullbackComparison

/-!
# A module in `LQCoh^fbc` is cartesian over the flat arrows between affine objects

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `F` a locally quasi-coherent
presheaf of `𝒪_𝒳`-modules (**Stacks 06WJ**). Let `e : x₁ ⟶ x₂` be an arrow of `𝒳` lying over a
flat morphism `f : U₁ ⟶ U₂` of affine schemes, along which the comparison map
`c_e : f_{small}^*(F|_{U₂,ét}) ⟶ F|_{U₁,ét}` of **Stacks 06WC** is an isomorphism of sheaves (the
flat base change property of **Stacks 0762** at `e`). This file proves, at module universe `u`,
that `F` is *cartesian* along `e`: the base-change comparison

`𝒪(x₁) ⊗_{𝒪(x₂)} F(x₂) ⟶ F(x₁)`

is bijective.

## The argument

Let `𝓕` be a quasi-coherent `𝒪_{U₂}`-module with `𝓕^a ≅ F|_{U₂,ét}` (the module below `x₂` of the
proof of **Stacks 076T**, `AlgebraicGeometry.Stack.QuasicoherentBelow`). The identification of
Stacks 076T, `AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified`, reads `F(x₂)` as `Γ(U₂, 𝓕)`
(along `𝟙 x₂`) and `F(x₁)` as `Γ(U₁, f^*𝓕)` (along `e`); both identifications are linear
(`AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified_hom_smul`) and they carry the
restriction map of `F` along `e` to the restriction map of the presheaf of **Stacks 03DS**, by
their cocycle condition (`AlgebraicGeometry.Stack.LiftedSectionsCocycleOfSheafified`, proved in
the library). That restriction map is a base change because `f` is flat and `U₂` is affine
(**Stacks 02KH** in degree zero, `AlgebraicGeometry.exists_isBaseChange_pullbackSectionsMap`),
and being a base change transfers along the two linear identifications.

## Main results

* `Stack.bijective_restrictionBaseChange_of_isIso_sheafifiedRestrictComparison`:
  the statement above, for a single arrow.
* `Stack.bijective_restrictionBaseChange_of_isLocallyQuasicoherentWithSheafFlatBaseChange`:
  a module in `LQCoh^fbc(𝒪_𝒳)` is cartesian over every arrow lying over a flat morphism of affine
  schemes.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **Flat base change along an arrow between affine objects makes the module cartesian there.**
Let `F` be a locally quasi-coherent presheaf of modules on `𝒳` and `e : x₁ ⟶ x₂` an arrow lying
over a flat morphism of affine schemes along which the comparison map of Stacks 06WC is an
isomorphism of sheaves. Then `𝒪(x₁) ⊗_{𝒪(x₂)} F(x₂) ⟶ F(x₁)` is bijective. -/
theorem bijective_restrictionBaseChange_of_isIso_sheafifiedRestrictComparison
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hlqc : IsLocallyQuasicoherent B E h S hS p hp F) {x₁ x₂ : 𝒳} (e : x₁ ⟶ x₂)
    (hflat : Flat (B.inclusion.map (p.map e).left))
    (h₁ : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₁)))
    (h₂ : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₂)))
    (hiso : IsIso (sheafifiedRestrictComparison B E h S hS p hp F e (hlqc.2 _).choose)) :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      (commRestrictModule B S hS p hp (etaleTopology B) (etaleTopology_le_topology B) F)
      e.op) := by
  classical
  obtain ⟨d⟩ := nonempty_quasicoherentBelow B E h S hS p hp F hlqc x₂
  have := d.isQuasicoherent
  have hcoc : LiftedSectionsCocycleOfSheafified B E h S hS p hp :=
    liftedSectionsCocycleOfSheafified_of_factorFourSquare B E h S hS p hp
      (liftedSectionsFactorFourSquareOfSheafified_of_compat B E h S hS p hp
        (associatedModuleBaseChangeFinalSectionsCompat B E h S hS p hp))
  have hid : IsIso (sheafifiedRestrictComparison B E h S hS p hp F (𝟙 x₂)
      (hlqc.2 _).choose) :=
    isIso_sheafifiedRestrictComparison_of_etale B E h S hS p hp (𝟙 x₂)
      (by simp only [CategoryTheory.Functor.map_id, Over.id_left]; infer_instance) F _
  let L₁ := liftedSectionsIsoOfSheafified B E h S hS p hp F hlqc e d.val d.isQuasicoherent
    d.isSheaf d.iso hiso
  let L₂ := liftedSectionsIsoOfSheafified B E h S hS p hp F hlqc (𝟙 x₂) d.val
    d.isQuasicoherent d.isSheaf d.iso hid
  have hnat := hcoc F hlqc d.val d.isQuasicoherent d.isSheaf d.iso e (𝟙 x₂) e
    (Category.comp_id e).symm hid hiso
  -- the presheaf of Stacks 03DS of the module below `x₂`, at the two objects
  let V : Scheme.{u} := (p.obj x₂).left.1
  let Y₁ : BigFppfOver B V (p.obj x₂).left.2 := Over.mk ((p ⋙ Over.forget (B.obj hS)).map e)
  let Y₂ : BigFppfOver B V (p.obj x₂).left.2 :=
    Over.mk ((p ⋙ Over.forget (B.obj hS)).map (𝟙 x₂))
  let k : Y₁ ⟶ Y₂ := Over.homMk ((p ⋙ Over.forget (B.obj hS)).map e) (by simp [Y₁, Y₂])
  let W₁ : Over V := (Over.post B.inclusion).obj Y₁
  let W₂ : Over V := (Over.post B.inclusion).obj Y₂
  let g : W₁ ⟶ W₂ := (Over.post B.inclusion).map k
  have : IsAffine W₁.left := h₁
  have : IsAffine W₂.left := h₂
  have : Flat g.left := hflat
  have H : IsPullback g.left (𝟙 W₁.left) (𝟙 W₂.left) g.left :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  obtain ⟨ρ, hρ, hbc⟩ := exists_isBaseChange_pullbackSectionsMap d.val g H
  -- the rings and the module structures
  let R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj
  let M := commRestrictModule B S hS p hp (etaleTopology B) (etaleTopology_le_topology B) F
  let A₁ := R.obj (op x₁)
  let A₂ := R.obj (op x₂)
  let : Algebra A₂ A₁ := (R.map e.op).hom.toAlgebra
  let : Module A₂ (M.obj (op x₂)) := inferInstanceAs
    (Module ((R ⋙ forget₂ CommRingCat RingCat).obj (op x₂)) (M.obj (op x₂)))
  let : Module A₁ (M.obj (op x₁)) := inferInstanceAs
    (Module ((R ⋙ forget₂ CommRingCat RingCat).obj (op x₁)) (M.obj (op x₁)))
  let : Module A₂ (M.obj (op x₁)) := Module.compHom _ (R.map e.op).hom
  have : IsScalarTower A₂ A₁ (M.obj (op x₁)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let G₁ := Γ((Scheme.Modules.pullback W₁.hom).obj d.val, ⊤)
  let G₂ := Γ((Scheme.Modules.pullback W₂.hom).obj d.val, ⊤)
  let : Module A₂ G₂ := (inferInstance : Module Γ(W₂.left, ⊤) G₂)
  let : Module A₁ G₁ := (inferInstance : Module Γ(W₁.left, ⊤) G₁)
  let : Module A₂ G₁ := Module.compHom _ (R.map e.op).hom
  have : IsScalarTower A₂ A₁ G₁ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let ρA : G₂ →ₗ[A₂] G₁ := ρ
  -- the identifications of Stacks 076T, as additive equivalences
  let o₁ := (quasiCoherentPresheaf V d.val).objIso (op W₁)
  let o₂ := (quasiCoherentPresheaf V d.val).objIso (op W₂)
  let a₁ : M.obj (op x₁) ≃+ G₁ := (L₁ ≪≫ o₁).addCommGroupIsoToAddEquiv
  let a₂ : M.obj (op x₂) ≃+ G₂ := (L₂ ≪≫ o₂).addCommGroupIsoToAddEquiv
  have hl : ∀ {y : 𝒳} (φ : y ⟶ x₂)
      (hφ : IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ (hlqc.2 _).choose))
      (r : R.obj (op y)) (s : M.obj (op y)),
      let L := liftedSectionsIsoOfSheafified B E h S hS p hp F hlqc φ d.val d.isQuasicoherent
        d.isSheaf d.iso hφ
      let W := (Over.post B.inclusion).obj (Over.mk ((p ⋙ Over.forget _).map φ))
      let o := (quasiCoherentPresheaf V d.val).objIso (op W)
      o.hom (L.hom (r • s)) = (show Γ(W.left, ⊤) from r) • o.hom (L.hom s) := by
    intro y φ hφ r s L W o
    rw [show L.hom (r • s) = _ from liftedSectionsIsoOfSheafified_hom_smul B E h S hS p hp F hlqc
      φ d.val d.isQuasicoherent d.isSheaf d.iso hφ r s]
    exact (o.addCommGroupIsoToAddEquiv.linearEquiv Γ(W.left, ⊤)).map_smul r _
  have hl₁ : ∀ (r : A₁) (s : M.obj (op x₁)), a₁ (r • s) = r • a₁ s := hl e hiso
  have hl₂ : ∀ (r : A₂) (s : M.obj (op x₂)), a₂ (r • s) = r • a₂ s := hl (𝟙 x₂) hid
  let eN : M.obj (op x₁) ≃ₗ[A₁] G₁ := { a₁ with map_smul' := hl₁ }
  let eM : M.obj (op x₂) ≃ₗ[A₂] G₂ := { a₂ with map_smul' := hl₂ }
  let gF : M.obj (op x₂) →ₗ[A₂] M.obj (op x₁) :=
    { toFun := fun s => M.map e.op s
      map_add' := fun s t => map_add (M.map e.op).hom s t
      map_smul' := fun r s => M.map_smul e.op r s }
  let P := (quasiCoherentPresheaf V d.val).functor
  let L₁' : F.presheaf.obj (op x₁) ≅ P.obj (op W₁) := L₁
  let L₂' : F.presheaf.obj (op x₂) ≅ P.obj (op W₂) := L₂
  simp only [overPostSectionsPresheaf, BigFppfOver.sectionsPresheafOfModules_presheaf,
    Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at hnat
  have hnat' : F.presheaf.map e.op ≫ L₁'.hom = L₂'.hom ≫ P.map g.op := hnat
  have h2 := (quasiCoherentPresheaf V d.val).map_objIso g.op
  have hcomm' : ∀ s : F.presheaf.obj (op x₂),
      ρ (((quasiCoherentPresheaf V d.val).objIso (op W₂)).hom (L₂'.hom s)) =
        ((quasiCoherentPresheaf V d.val).objIso (op W₁)).hom
          (L₁'.hom (F.presheaf.map e.op s)) := by
    intro s
    have h1 : L₁'.hom (F.presheaf.map e.op s) = P.map g.op (L₂'.hom s) :=
      congrArg (fun t => t s) hnat'
    have h3 := congrArg (fun t => t (((quasiCoherentPresheaf V d.val).objIso (op W₂)).hom
      (L₂'.hom s))) h2
    simp only [ConcreteCategory.comp_apply, Iso.hom_inv_id_apply, Quiver.Hom.unop_op] at h3
    rw [h1, hρ]
    convert h3.symm using 3
  have hcomm : ρA.comp eM.toLinearMap = (eN.restrictScalars A₂).comp gF :=
    LinearMap.ext hcomm'
  exact Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_isBaseChange M e.op gF
    (fun _ => rfl) ((IsBaseChange.iff_of_equiv_comm eM eN hcomm).2 hbc)

/-- **A module in `LQCoh^fbc(𝒪_𝒳)` is cartesian over the flat arrows between objects over affine
schemes**, at module universe `u`: for an arrow `e : x₁ ⟶ x₂` of `𝒳` lying over a flat morphism
of affine schemes, `𝒪(x₁) ⊗_{𝒪(x₂)} F(x₂) ⟶ F(x₁)` is bijective. The flat base change property
of Stacks 0762 makes the comparison along `e` an isomorphism of sheaves, and
`AlgebraicGeometry.Stack.bijective_restrictionBaseChange_of_isIso_sheafifiedRestrictComparison`
applies. -/
theorem bijective_restrictionBaseChange_of_isLocallyQuasicoherentWithSheafFlatBaseChange
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hF : IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, u} B E h S hS p hp F)
    {x₁ x₂ : 𝒳} (e : x₁ ⟶ x₂)
    (hflat : Flat (B.inclusion.map (p.map e).left))
    (h₁ : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₁)))
    (h₂ : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₂))) :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      (commRestrictModule B S hS p hp (etaleTopology B) (etaleTopology_le_topology B) F)
      e.op) :=
  bijective_restrictionBaseChange_of_isIso_sheafifiedRestrictComparison B E h S hS p hp F hF.1 e
    hflat h₁ h₂ ((isIso_sheafifiedRestrictModulePullbackComparison_iff B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) e F (hF.1.2 _).choose).2 (hF.2 e hflat))

end AlgebraicGeometry.Stack
