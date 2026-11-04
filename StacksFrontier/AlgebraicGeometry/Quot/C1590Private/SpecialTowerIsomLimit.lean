module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SpecialTowerSpaceLimit
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.CategoryTheory.Sites.Stack.MorPresheafOfLifts

/-!
# Morphisms of a stack with algebraic `Isom` along étale limit towers

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S` whose `Isom` sheaves are
algebraic spaces (condition (2) of Stacks 045G), and let `Wₙ ⟶ U` be an étale limit tower
(`AlgebraicGeometry.C1590Private.IsEtaleLimitTower`). For objects `x`, `y` over `U`, compatible
morphisms `x|_{Wₙ} ⟶ y` over `Wₙ ⟶ U` come from exactly one morphism `x ⟶ y` over `U`: the
`Isom` space commutes with the limit
(`AlgebraicGeometry.C1590Private.IsEtaleLimitTower.algebraicSpace_existsUnique`). This is the full
faithfulness of restriction to the levels in step (F) of the special-tower argument.

## Main results

* `AlgebraicGeometry.C1590Private.IsEtaleLimitTower.existsUnique_mor`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Functor

universe u v w

namespace AlgebraicGeometry.C1590Private

/-- The fibres of a category fibred in groupoids are groupoids. -/
theorem isGroupoid_fiber {𝒞 : Type*} {𝒮 : Type*} [Category 𝒞] [Category 𝒮] (p : 𝒮 ⥤ 𝒞)
    (hp : p.IsFiberedInGroupoids) (T : 𝒞) : IsGroupoid (p.Fiber T) where
  all_isIso {a b} m := by
    have : p.IsHomLift (𝟙 T) m.1 := m.2
    have : p.IsStronglyCartesian (𝟙 T) m.1 := hp.isStronglyCartesian_homLift _ _
    have : IsIso m.1 := IsStronglyCartesian.isIso_of_base_isIso p (𝟙 T) m.1
    exact ⟨⟨inv m.1, inferInstance⟩, Fiber.hom_ext (IsIso.hom_inv_id m.1),
      Fiber.hom_ext (IsIso.inv_hom_id m.1)⟩

/-- The system of chosen cartesian lifts of an object of a fibred category. -/
def chosenLiftSystem {𝒞 : Type*} {𝒮 : Type*} [Category 𝒞] [Category 𝒮] (p : 𝒮 ⥤ 𝒞)
    [p.IsFibered] {U : 𝒞} (x : p.Fiber U) : CartesianLiftSystem p x where
  obj f := (pullbackFiber p x f.hom).1
  hom f := IsPreFibered.pullbackMap x.2 f.hom
  isStronglyCartesian _ := inferInstance
  trans h := pullbackFiberMap p x h
  trans_isHomLift _ := inferInstance
  trans_hom h := pullbackFiberMap_fac p x h

/-- The bijection of sections induced by an isomorphism `F ⋙ uliftFunctor ≅ E.inverse.op ⋙ G ⋙
uliftFunctor` of presheaves along an equivalence `E`. -/
def transportSectionsEquiv {C D : Type*} [Category C] [Category D] (E : C ≌ D)
    {F : Dᵒᵖ ⥤ Type u} {G : Cᵒᵖ ⥤ Type v}
    (e : F ⋙ uliftFunctor.{v, u} ≅ (E.inverse.op ⋙ G) ⋙ uliftFunctor.{u, v}) (g : C) :
    F.obj (op (E.functor.obj g)) ≃ G.obj (op g) :=
  Equiv.ulift.symm.trans ((e.app (op (E.functor.obj g))).toEquiv.trans
    (Equiv.ulift.trans (G.mapIso (E.unitIso.app g).op).toEquiv))

/-- `transportSectionsEquiv` is natural. -/
theorem map_transportSectionsEquiv {C D : Type*} [Category C] [Category D] (E : C ≌ D)
    {F : Dᵒᵖ ⥤ Type u} {G : Cᵒᵖ ⥤ Type v}
    (e : F ⋙ uliftFunctor.{v, u} ≅ (E.inverse.op ⋙ G) ⋙ uliftFunctor.{u, v}) {g₁ g₂ : C}
    (h : g₁ ⟶ g₂) (a : F.obj (op (E.functor.obj g₂))) :
    G.map h.op (transportSectionsEquiv E e g₂ a) =
      transportSectionsEquiv E e g₁ (F.map (E.functor.map h).op a) := by
  have h1 := congrArg (fun k => k (ULift.up.{v} a)) (e.hom.naturality (E.functor.map h).op)
  have h2 : h ≫ E.unitIso.hom.app g₂ = E.unitIso.hom.app g₁ ≫ E.inverse.map (E.functor.map h) :=
    E.unitIso.hom.naturality h
  show G.map h.op (G.map (E.unitIso.hom.app g₂).op
      (ULift.down (e.hom.app _ (ULift.up.{v} a)))) =
    G.map (E.unitIso.hom.app g₁).op
      (ULift.down (e.hom.app _ (ULift.up.{v} (F.map (E.functor.map h).op a))))
  have h1' : ULift.down (e.hom.app (op (E.functor.obj g₁))
      (ULift.up.{v} (F.map (E.functor.map h).op a))) =
      G.map (E.inverse.map (E.functor.map h)).op
        (ULift.down (e.hom.app (op (E.functor.obj g₂)) (ULift.up.{v} a))) :=
    congrArg ULift.down h1
  rw [h1', ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
    ← op_comp, h2]

/-- A section restricts to a transported section exactly when its transport restricts to it. -/
theorem map_eq_transportSectionsEquiv_symm_iff {C D : Type*} [Category C] [Category D]
    (E : C ≌ D) {F : Dᵒᵖ ⥤ Type u} {G : Cᵒᵖ ⥤ Type v}
    (e : F ⋙ uliftFunctor.{v, u} ≅ (E.inverse.op ⋙ G) ⋙ uliftFunctor.{u, v}) {g₁ g₂ : C}
    (h : g₁ ⟶ g₂) (a : F.obj (op (E.functor.obj g₂))) (b : G.obj (op g₁)) :
    F.map (E.functor.map h).op a = (transportSectionsEquiv E e g₁).symm b ↔
      G.map h.op (transportSectionsEquiv E e g₂ a) = b := by
  rw [map_transportSectionsEquiv]
  exact (transportSectionsEquiv E e g₁).eq_symm_apply

section Tower

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
  {U : BigFppfOver B S hS} {W : ℕ → BigFppfOver B S hS} {κ : ∀ n, W n ⟶ U}
  {ℓ : ∀ n, W n ⟶ W (n + 1)}

/-- **Full faithfulness of restriction to the levels of an étale limit tower**. For a category
fibred in groupoids whose `Isom` sheaves are algebraic spaces and objects `x`, `y` over the top `U`
of an étale limit tower, compatible morphisms `x|_{Wₙ} ⟶ y` over `Wₙ ⟶ U` come from exactly one
morphism `x|_U ⟶ y` over `U`. -/
theorem IsEtaleLimitTower.existsUnique_mor (hW : IsEtaleLimitTower W κ ℓ)
    (hI : Stack.IsAlgebraicSpaceIsomPresheaf B S hS 𝒳) [𝒳.val.p.IsFibered]
    (x y : 𝒳.val.p.Fiber U) (ψ : ∀ n, (pullbackFiber 𝒳.val.p x (κ n)).1 ⟶ y.1)
    (hψ : ∀ n, 𝒳.val.p.IsHomLift (κ n) (ψ n))
    (hc : ∀ n, pullbackFiberMap 𝒳.val.p x
      (Over.homMk (ℓ n) (hW.comp n) : Over.mk (κ n) ⟶ Over.mk (κ (n + 1))) ≫ ψ (n + 1) = ψ n) :
    ∃! φ : (pullbackFiber 𝒳.val.p x (𝟙 U)).1 ⟶ y.1, 𝒳.val.p.IsHomLift (𝟙 U) φ ∧
      ∀ n, pullbackFiberMap 𝒳.val.p x
        (Over.homMk (κ n) (Category.comp_id _) : Over.mk (κ n) ⟶ Over.mk (𝟙 U)) ≫ φ = ψ n := by
  obtain ⟨F, hFa, ⟨e⟩⟩ := hI U x y
  have : IsAffine U.left.1 := hW.isAffine
  let p := 𝒳.val.p
  let G := p.isomPresheaf x y
  let L := chosenLiftSystem p x
  have hg := isGroupoid_fiber p 𝒳.isFiberedInGroupoids
  let E := Over.iteratedSliceEquiv U
  let σ := transportSectionsEquiv E (G := G) e
  let sec : ∀ n, G.obj (op (Over.mk (κ n))) := fun n =>
    ⟨(L.morPresheafEquiv y (Over.mk (κ n))).symm ⟨ψ n, hψ n⟩, (hg _).all_isIso _⟩
  have hsec : ∀ n, G.map (Over.homMk (ℓ n) (hW.comp n) :
      Over.mk (κ n) ⟶ Over.mk (κ (n + 1))).op (sec (n + 1)) = sec n := fun n => by
    refine Subtype.ext ((L.morPresheafEquiv y (Over.mk (κ n))).injective (Subtype.ext ?_))
    refine (L.morPresheafEquiv_morRestrict y _ _).trans ?_
    simp only [sec, Equiv.apply_symm_apply]
    exact hc n
  let s' : ∀ n, F.obj (op (sliceLevel κ n)) := fun n => (σ (Over.mk (κ n))).symm (sec n)
  have hs' : ∀ n, F.map (sliceℓ hW.comp n).op (s' (n + 1)) = s' n := fun n =>
    (map_eq_transportSectionsEquiv_symm_iff E e
      (Over.homMk (ℓ n) (hW.comp n) : Over.mk (κ n) ⟶ Over.mk (κ (n + 1))) _ (sec n)).2
      (by simpa only [s', σ, Equiv.apply_symm_apply] using hsec n)
  obtain ⟨t, ht, htu⟩ := hW.slice.algebraicSpace_existsUnique hFa s' hs'
  let top : Over U := Over.mk (𝟙 U)
  let jn : ∀ n, (Over.mk (κ n) : Over U) ⟶ top := fun n => Over.homMk (κ n) (Category.comp_id _)
  let φ := L.morPresheafEquiv y top (σ top t).1
  have key : ∀ (m : G.obj (op top)) n,
      (L.morPresheafEquiv y (Over.mk (κ n)) (G.map (jn n).op m).1).1 =
        pullbackFiberMap p x (jn n) ≫ (L.morPresheafEquiv y top m.1).1 := fun m n =>
    L.morPresheafEquiv_morRestrict y (jn n) m.1
  have hsecv : ∀ n, (L.morPresheafEquiv y (Over.mk (κ n)) (sec n).1).1 = ψ n := fun n =>
    congrArg Subtype.val (Equiv.apply_symm_apply (L.morPresheafEquiv y (Over.mk (κ n))) _)
  have hlev : ∀ (m : G.obj (op top)) n, G.map (jn n).op m = sec n ↔
      pullbackFiberMap p x (jn n) ≫ (L.morPresheafEquiv y top m.1).1 = ψ n := fun m n => by
    rw [← key]
    refine ⟨fun h => by rw [h, hsecv n], fun h => Subtype.ext
      ((L.morPresheafEquiv y _).injective (Subtype.ext (h.trans (hsecv n).symm)))⟩
  have hFσ : ∀ (a : F.obj (op (E.functor.obj top))) n, F.map (E.functor.map (jn n)).op a = s' n ↔
      G.map (jn n).op (σ top a) = sec n := fun a n =>
    map_eq_transportSectionsEquiv_symm_iff E e (jn n) a (sec n)
  refine ⟨φ.1, ⟨φ.2, fun n => (hlev _ n).1 ((hFσ t n).1 (ht n))⟩, fun φ' ⟨hφ'1, hφ'2⟩ => ?_⟩
  let m' : G.obj (op top) := ⟨(L.morPresheafEquiv y top).symm ⟨φ', hφ'1⟩, (hg _).all_isIso _⟩
  have hm' : (L.morPresheafEquiv y top m'.1).1 = φ' :=
    congrArg Subtype.val (Equiv.apply_symm_apply (L.morPresheafEquiv y top) _)
  have : (σ top).symm m' = t := htu _ fun n => (hFσ _ n).2 <| by
    rw [Equiv.apply_symm_apply, hlev, hm']
    exact hφ'2 n
  rw [← hm', (σ top).symm_apply_eq.mp this]

end Tower

end AlgebraicGeometry.C1590Private

end
