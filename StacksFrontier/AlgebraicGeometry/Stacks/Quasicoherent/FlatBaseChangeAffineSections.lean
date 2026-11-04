module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafFlatBaseChangeSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRingChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineCharts
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesian
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentSectionsBaseChange

/-!
# Sections of a module with the flat base change property over a flat morphism of affines

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be fibred in groupoids and `ℱ` a module in `LQCoh^{fbc}(𝒪_𝒳)`.
This file proves that the restriction map of `ℱ` along an arrow `n : y ⟶ x` lying over a flat
morphism of affine schemes is a base change: `𝒪(y) ⊗_{𝒪(x)} ℱ(x) ⟶ ℱ(y)` is bijective.

The identification of sections of Stacks 076T,
`AlgebraicGeometry.Stack.liftedSectionsIsoOfInv`, identifies `ℱ(z)` with `Γ(W, g^*𝓕)` for every
arrow `z ⟶ x` lying over `g : W ⟶ U`, where `𝓕` is the quasi-coherent `𝒪_U`-module with
`𝓕^a ≅ ℱ|_{U_ét}`.  It is linear (`AlgebraicGeometry.Stack.liftedSectionsIsoOfInv_hom_smul`) and
intertwines the restriction maps (`AlgebraicGeometry.Stack.liftedSectionsIsoOfInv_cocycle`), so
the cartesian property of the presheaf of Stacks 03DS between affine objects transports to `ℱ`.

## Main results

* `Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_addEquiv`: the base-change
  comparison of a restriction map is bijective as soon as it is for a restriction map of another
  presheaf of modules identified with it by semilinear additive identifications.
* `AlgebraicGeometry.Stack.liftedSectionsIsoOfInv_hom_smul`: the identification of sections of
  Stacks 076T is linear.
* `Stack.bijective_restrictionBaseChange_of_locallyQuasicoherentFlatBaseChangeSheaf`: a member
  of `LQCoh^{fbc}(𝒪_𝒳)` is cartesian along arrows over flat morphisms of affines.

## References

* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u v w v' w'

namespace Stacks.PresheafOfModules

/-- The additive equivalence `B ⊗[A] N ≃+ B' ⊗[A'] N'` induced by ring equivalences `A ≃+* A'`,
`B ≃+* B'` compatible with the algebra maps and a semilinear additive equivalence `N ≃+ N'`. -/
private def tensorAddEquivOfRingEquiv {A B A' B' N N' : Type*} [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B'] [Algebra A B] [Algebra A' B'] [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A' N'] (ρA : A ≃+* A') (ρB : B ≃+* B')
    (hρ : ∀ a, ρB (algebraMap A B a) = algebraMap A' B' (ρA a)) (θ : N ≃+ N')
    (hθ : ∀ (a : A) (n : N), θ (a • n) = ρA a • θ n) :
    TensorProduct A B N ≃+ TensorProduct A' B' N' :=
  let E : TensorProduct A B N →+ TensorProduct A' B' N' :=
    TensorProduct.liftAddHom
      { toFun := fun c =>
          { toFun := fun m => ρB c ⊗ₜ[A'] θ m
            map_zero' := by rw [map_zero, TensorProduct.tmul_zero]
            map_add' := fun m m' => by rw [map_add, TensorProduct.tmul_add] }
        map_zero' := by ext m; simp
        map_add' := fun b b' => by ext m; simp [TensorProduct.add_tmul] }
      (fun a b m => by
        change ρB (a • b) ⊗ₜ[A'] θ m = ρB b ⊗ₜ[A'] θ (a • m)
        rw [hθ, Algebra.smul_def, map_mul, ← TensorProduct.smul_tmul, Algebra.smul_def]
        congr 1
        exact congrArg (· * ρB b) (hρ a))
  let E' : TensorProduct A' B' N' →+ TensorProduct A B N :=
    TensorProduct.liftAddHom
      { toFun := fun c =>
          { toFun := fun m => ρB.symm c ⊗ₜ[A] θ.symm m
            map_zero' := by rw [map_zero, TensorProduct.tmul_zero]
            map_add' := fun m m' => by rw [map_add, TensorProduct.tmul_add] }
        map_zero' := by ext m; simp
        map_add' := fun b b' => by ext m; simp [TensorProduct.add_tmul] }
      (fun a b m => by
        change ρB.symm (a • b) ⊗ₜ[A] θ.symm m = ρB.symm b ⊗ₜ[A] θ.symm (a • m)
        have hm : a • m = θ (ρA.symm a • θ.symm m) := by
          rw [hθ, ρA.apply_symm_apply, θ.apply_symm_apply]
        have ha : ρB.symm (a • b) = ρA.symm a • ρB.symm b := by
          rw [ρB.symm_apply_eq, Algebra.smul_def, Algebra.smul_def, map_mul, ρB.apply_symm_apply]
          exact congrArg (· * b) ((congrArg _ (ρA.apply_symm_apply a)).symm.trans (hρ _).symm)
        rw [hm, θ.symm_apply_apply, ha]
        exact TensorProduct.smul_tmul _ _ _)
  { toFun := E
    invFun := E'
    left_inv := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => rw [map_add, map_add, hz, hw]
      | tmul c m =>
        change ρB.symm (ρB c) ⊗ₜ[A] θ.symm (θ m) = c ⊗ₜ m
        rw [ρB.symm_apply_apply, θ.symm_apply_apply]
    right_inv := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => rw [map_add, map_add, hz, hw]
      | tmul c m =>
        change ρB (ρB.symm c) ⊗ₜ[A'] θ (θ.symm m) = c ⊗ₜ m
        rw [ρB.apply_symm_apply, θ.apply_symm_apply]
    map_add' := map_add E }

open scoped ChangeOfRings in
/-- **Cartesianness transported along semilinear identifications.**  Let `M` and `P` be presheaves
of modules over presheaves of commutative rings `R` and `R'` on two categories, `f : X ⟶ Y` and
`g : X' ⟶ Y'`, and identify the rings `R X ≅ R' X'`, `R Y ≅ R' Y'` compatibly with the restriction
maps, and the sections `M X ≃ P X'`, `M Y ≃ P Y'` additively and semilinearly, intertwining the
two restriction maps.  If the base-change comparison `R' Y' ⊗_{R' X'} P X' ⟶ P Y'` is bijective,
so is `R Y ⊗_{R X} M X ⟶ M Y`. -/
theorem bijective_restrictionBaseChange_of_addEquiv
    {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
    {R : Cᵒᵖ ⥤ CommRingCat.{u}} {R' : Dᵒᵖ ⥤ CommRingCat.{u}}
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (P : PresheafOfModules.{u} (R' ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) {X' Y' : Dᵒᵖ} (g : X' ⟶ Y')
    (ρX : R.obj X ≃+* R'.obj X') (ρY : R.obj Y ≃+* R'.obj Y')
    (hρ : ∀ c, ρY (R.map f c) = R'.map g (ρX c))
    (θX : M.obj X ≃+ P.obj X') (θY : M.obj Y ≃+ P.obj Y')
    (hX : ∀ (c : R.obj X) (m : M.obj X), θX (c • m) = ρX c • θX m)
    (hY : ∀ (c : R.obj Y) (m : M.obj Y), θY (c • m) = ρY c • θY m)
    (hcomm : ∀ m, θY (M.map f m) = P.map g (θX m))
    (hP : Function.Bijective (restrictionBaseChange P g)) :
    Function.Bijective (restrictionBaseChange M f) := by
  let := (R.map f).hom.toAlgebra
  let := (R'.map g).hom.toAlgebra
  let E := tensorAddEquivOfRingEquiv ρX ρY hρ θX hX
  have key : ∀ z, θY (restrictionBaseChange M f z) = restrictionBaseChange P g (E z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
      exact ((congrArg θY (map_zero (restrictionBaseChange M f).hom)).trans
        (map_zero θY)).trans ((congrArg (restrictionBaseChange P g) (map_zero E)).trans
          (map_zero (restrictionBaseChange P g).hom)).symm
    | add z w hz hw =>
      exact ((congrArg θY (map_add (restrictionBaseChange M f).hom z w)).trans
        (map_add θY _ _)).trans ((congrArg₂ (· + ·) hz hw).trans
        ((congrArg (restrictionBaseChange P g) (map_add E z w)).trans
          (map_add (restrictionBaseChange P g).hom _ _)).symm)
    | tmul c m =>
      refine (congrArg θY (restrictionBaseChange_tmul M f c m)).trans ?_
      refine ((hY _ _).trans (congrArg (ρY c • ·) (hcomm m))).trans ?_
      exact (restrictionBaseChange_tmul P g (ρY c) (θX m)).symm
  refine ⟨fun z w hzw => E.injective (hP.1 ?_), fun y => ?_⟩
  · exact ((key z).symm.trans (congrArg θY hzw)).trans (key w)
  · obtain ⟨t, ht⟩ := hP.2 (θY y)
    exact ⟨E.symm t, θY.injective (((key _).trans (congrArg _ (E.apply_symm_apply t))).trans ht)⟩

/-- A commuting square of abelian groups between the restriction maps of two presheaves of
modules, read on elements through `CategoryTheory.Iso.addCommGroupIsoToAddEquiv`. -/
theorem addCommGroupIsoToAddEquiv_map_apply_of_comm
    {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
    {R : Cᵒᵖ ⥤ CommRingCat.{u}} {R' : Dᵒᵖ ⥤ CommRingCat.{u}}
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (P : PresheafOfModules.{u} (R' ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) {X' Y' : Dᵒᵖ} (g : X' ⟶ Y')
    (θX : M.presheaf.obj X ≅ P.presheaf.obj X') (θY : M.presheaf.obj Y ≅ P.presheaf.obj Y')
    (h : M.presheaf.map f ≫ θY.hom = θX.hom ≫ P.presheaf.map g) (m : M.obj X) :
    θY.addCommGroupIsoToAddEquiv (M.map f m) = P.map g (θX.addCommGroupIsoToAddEquiv m) :=
  ConcreteCategory.congr_hom h m

end Stacks.PresheafOfModules

namespace Stacks.Sites

open _root_.AlgebraicGeometry

/-- **The last two factors of the identification of sections of Stacks 076T are semilinear.**
For `X` over `S`, `A` over `X.left` and an arrow `e : Y ⟶ (Over.map X.hom).obj A` of schemes over
`S`, the base change `Γ(A, A⁺(X⁺F)) ⟶ Γ(A, (A ≫ X)⁺F)` followed by the pullback map along `e` on
sections carries the action of `c ∈ Γ(A, 𝒪_A)` to the action of `e.left.appTop c`.  This
composite is, by definition, the inverse of `Stacks.Sites.quasiCoherentPresheafBaseChangeIso`
followed by the restriction of the presheaf of Tag 03DS along `e`. -/
theorem quasiCoherentPresheafBaseChangeIso_inv_map_smul {S : Scheme.{u}}
    (F : S.Modules) [F.IsQuasicoherent] (X : Over S) (A : Over X.left) {Y : Over S}
    (e : Y ⟶ (Over.map X.hom).obj A) (c : Γ(A.left, ⊤))
    (m : Γ((Scheme.Modules.pullback A.hom).obj ((Scheme.Modules.pullback X.hom).obj F), ⊤)) :
    pullbackSectionsMap F e
        (((Scheme.Modules.pullbackComp A.hom X.hom).hom.app F).app ⊤ (c • m)) =
      e.left.appTop c • pullbackSectionsMap F e
        (((Scheme.Modules.pullbackComp A.hom X.hom).hom.app F).app ⊤ m) := by
  rw [Scheme.Modules.Hom.app_smul, pullbackSectionsMap_smul]

/-- The pullback of global functions along a morphism equal to the identity is the identity. -/
theorem appTop_apply_of_eq_id {T : Scheme.{u}} (f : T ⟶ T) (hf : f = 𝟙 T) (c : Γ(T, ⊤)) :
    f.appTop c = c := by
  subst hf
  rfl

end Stacks.Sites

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **A locally quasi-coherent module is cartesian along an arrow lying over an étale morphism of
affine schemes.**  For `f : y ⟶ x` in `𝒳` with `p(x)`, `p(y)` affine and the morphism of schemes
below `f` étale, the base-change comparison `𝒪(y) ⊗_{𝒪(x)} 𝒢(x) ⟶ 𝒢(y)` is bijective.

At the target `x` the restriction of Stacks 06WJ is quasi-coherent, hence cartesian between affine
objects (Descent, Proposition 03DX (2)), and `f` is isomorphic to the image of a morphism of
affine objects of the small étale site under the index functor of Stacks 06W1. -/
theorem bijective_restrictionBaseChange_of_isLocallyQuasicoherent_of_etale
    (G : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hG : IsLocallyQuasicoherent B E h S hS p hp G) {x y : 𝒳} (f : y ⟶ x)
    (hf : Etale (B.inclusion.map (p.map f).left))
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)))
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y))) :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      G f.op) := by
  obtain ⟨_, hqc⟩ := hG.2 x
  obtain ⟨e₁, e₂, hsq⟩ := exists_arrowIso_etaleIndex B E h S hS p hp f hf
  have hT : IsAffine ((SmallEtale.toScheme E _ _).obj (etaleChart B E h S hS p f hf)) := hy
  have hT' : IsAffine ((SmallEtale.toScheme E _ _).obj (etaleTop B E h S hS p x)) := hx
  have h1 := SmallEtale.bijective_restrictionBaseChange_of_isQuasicoherentOnSite E _ _ _ hqc
    hT hT' (etaleChartToTop B E h S hS p f hf)
  have h2 := (bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff B E h S hS p hp G
    x (etaleChartToTop B E h S hS p f hf)).1 h1
  exact (Stacks.PresheafOfModules.bijective_restrictionBaseChange_iff_of_arrowIso
    (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj) G
    ((etaleIndex B E h S hS p hp x).map (etaleChartToTop B E h S hS p f hf)).op
    f.op e₂.hom.op e₁.hom.op (by rw [← op_comp, ← op_comp, hsq])).1 h2

section Semilinear

variable (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)

/-- **The identification `F(z) ≅ Γ(W_ét, F|_{W_ét})` is linear.**  Moving a section of `F` at
`z` to the final object of the small étale site of the scheme below `z` carries the action of a
global function to the action of the same function, read on the final object. -/
theorem restrictModuleToSmallEtaleFinalIso_inv_smul_etale (z : 𝒳)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (c : ((ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj.obj (op z) : Type u)) (s : F.obj (op z)) :
    (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).inv (c • s) =
      (show ((SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z)).obj.obj
        (op (smallEtaleFinal B E h S hS p z)) : Type u) from c) •
      (show (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).obj (op (smallEtaleFinal B E h S hS p z)) from
        (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).inv s) := by
  show F.map _ (c • s) = _
  rw [PresheafOfModules.map_smul]
  have hc : ((ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj.map
        (smallEtaleFinalObjectIso B E h S hS p hp z).op.hom).hom c =
      ((localStructurePresheafIso B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B)).hom.app (op (smallEtaleFinal B E h S hS p z))).hom c := by
    rw [localStructurePresheafIso_hom_app]
    let := isEquivalence_overPost B S hS p hp z
    have hl : (p.map (smallEtaleFinalObjectIso B E h S hS p hp z).hom).left =
        ((Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counit.app
          ((smallEtaleInclusion B E h (p.obj z).left.1
            (contains_base B E h S hS p z)).obj (smallEtaleFinal B E h S hS p z))).left := by
      have h1 := Over.w ((Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counit.app
          ((smallEtaleInclusion B E h (p.obj z).left.1
            (contains_base B E h S hS p z)).obj (smallEtaleFinal B E h S hS p z)))
      have h2 := Over.w ((IsTerminal.isTerminalObj (Over.post (X := z)
        (p ⋙ Over.forget (B.obj hS))).inv _
        (isTerminal_smallEtaleInclusion_obj_final B E h S hS p z)).uniqueUpToIso
          Over.mkIdTerminal).hom
      show (p.map ((IsTerminal.isTerminalObj (Over.post (X := z)
        (p ⋙ Over.forget (B.obj hS))).inv _
        (isTerminal_smallEtaleInclusion_obj_final B E h S hS p z)).uniqueUpToIso
          Over.mkIdTerminal).hom.left).left = _
      rw [(Category.comp_id _).symm.trans h2]
      exact h1.symm.trans (Category.comp_id _)
    show (Scheme.Γ.map (B.inclusion.map (p.map
      (smallEtaleFinalObjectIso B E h S hS p hp z).hom).left).op).hom c =
      (Scheme.Γ.map (B.inclusion.map
        ((Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counit.app
          ((smallEtaleInclusion B E h (p.obj z).left.1
            (contains_base B E h S hS p z)).obj (smallEtaleFinal B E h S hS p z))).left).op).hom c
    rw [hl]
    rfl
  rw [hc]
  rfl

/-- **Factors 2 and 3 of the identification of sections of Stacks 076T are linear.**  On the final
object of the small étale site of the scheme `W` below `z`, the identification
`F|_{W_ét} ≅ (g^*𝓕)^a` of `AlgebraicGeometry.Stack.liftedSmallEtaleIsoOfInv` followed by the
identification of `(g^*𝓕)^a` with the presheaf of sections of `g^*𝓕` is linear over the
functions on the final object. -/
theorem liftedSmallEtaleIsoOfInv_associatedModulePresheafIso_smul {x z : 𝒳} (φ : z ⟶ x)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (𝓕 : (p.obj x).left.1.Modules) [h𝓕 : 𝓕.IsQuasicoherent]
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMz : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
        (contains_base B E h S hS p z))
      (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ⟶
      restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F x hMx)
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU)]
    (c : ((SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z)).obj.obj
        (op (smallEtaleFinal B E h S hS p z)) : Type u))
    (m : (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).obj (op (smallEtaleFinal B E h S hS p z))) :
    (show (SmallEtale.sectionsPresheafOfModules E (p.obj z).left.1 (contains_base B E h S hS p z)
        ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).obj
          (op (smallEtaleFinal B E h S hS p z)) from
      (SmallEtale.associatedModulePresheafIso E (p.obj z).left.1 (contains_base B E h S hS p z)
        ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).hom.app
          (op (smallEtaleFinal B E h S hS p z))
        ((liftedSmallEtaleIsoOfInv B E h S hS p hp F φ 𝓕 hMx hMz eU).hom.app
          (op (smallEtaleFinal B E h S hS p z)) (c • m))) =
      c • (show (SmallEtale.sectionsPresheafOfModules E (p.obj z).left.1
          (contains_base B E h S hS p z)
          ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).obj
            (op (smallEtaleFinal B E h S hS p z)) from
        (SmallEtale.associatedModulePresheafIso E (p.obj z).left.1 (contains_base B E h S hS p z)
          ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).hom.app
            (op (smallEtaleFinal B E h S hS p z))
          ((liftedSmallEtaleIsoOfInv B E h S hS p hp F φ 𝓕 hMx hMz eU).hom.app
            (op (smallEtaleFinal B E h S hS p z)) m)) := by
  have h2 := ((((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map
      (inv (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU))).app
        (op (smallEtaleFinal B E h S hS p z))).hom.map_smul c m)
  have h3 := (((SmallEtale.associatedModuleIsoSectionsPresheaf E (p.obj z).left.1
      (contains_base B E h S hS p z)
      ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).hom.app
        (op (smallEtaleFinal B E h S hS p z))).hom.map_smul c)
  exact (congrArg (fun y => ((SmallEtale.associatedModuleIsoSectionsPresheaf E (p.obj z).left.1
      (contains_base B E h S hS p z)
      ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).hom.app
        (op (smallEtaleFinal B E h S hS p z))).hom y) h2).trans (h3 _)

/-- **The identification of sections of Stacks 076T is linear.**  For `φ : z ⟶ x`,
`AlgebraicGeometry.Stack.liftedSectionsIsoOfInv` carries the action of a function
`c ∈ 𝒪(z) = Γ(W, 𝒪_W)` on `F(z)` to its action on `Γ(W, g^*𝓕)`.  It is the composite of five
factors, each semilinear: the passage to the final object of the small étale site
(`AlgebraicGeometry.Stack.restrictModuleToSmallEtaleFinalIso_inv_smul_etale`), factors 2 and 3
(`AlgebraicGeometry.Stack.liftedSmallEtaleIsoOfInv_associatedModulePresheafIso_smul`) and the
base change of sections followed by a restriction along an arrow with identity left component
(`Stacks.Sites.quasiCoherentPresheafBaseChangeIso_inv_map_smul`). -/
theorem liftedSectionsIsoOfInv_hom_smul {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules) [h𝓕 : 𝓕.IsQuasicoherent]
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMz : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
        (contains_base B E h S hS p z))
      (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom)]
    (c : ((ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj.obj (op z) : Type u)) (s : F.obj (op z)) :
    (show ((BigFppfOver.sectionsPresheafOfModules B (p.obj x).left.1 (p.obj x).left.2 𝓕).obj
          (op (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ))) : Type u) from
        (liftedSectionsIsoOfInv B E h S hS p hp F φ 𝓕 h𝓕 hMx hMz eU).hom (c • s)) =
      (show ((BigFppfOver.structureSheaf B (p.obj x).left.1 (p.obj x).left.2).obj.obj
          (op (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ))) : Type u) from c) •
        (show ((BigFppfOver.sectionsPresheafOfModules B (p.obj x).left.1 (p.obj x).left.2 𝓕).obj
          (op (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ))) : Type u) from
          (liftedSectionsIsoOfInv B E h S hS p hp F φ 𝓕 h𝓕 hMx hMz eU).hom s) := by
  have e1 := restrictModuleToSmallEtaleFinalIso_inv_smul_etale B E h S hS p hp z F c s
  have e23 := liftedSmallEtaleIsoOfInv_associatedModulePresheafIso_smul B E h S hS p hp φ F 𝓕
    hMx hMz eU.hom
    (show ((SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z)).obj.obj
        (op (smallEtaleFinal B E h S hS p z)) : Type u) from c)
    ((restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).inv s)
  let A := (SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
    (smallEtaleFinal B E h S hS p z)
  let X : Over (p.obj x).left.1 := Over.mk (B.inclusion.map (p.map φ).left)
  let eo : (Over.post B.inclusion).obj (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ)) ≅
      (Over.map X.hom).obj A :=
    Over.isoMk (Iso.refl _) (by simp [A, X, smallEtaleFinal, SmallEtale.final, Over.post])
  let F23 := fun m => (SmallEtale.associatedModulePresheafIso E (p.obj z).left.1
      (contains_base B E h S hS p z)
      ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).hom.app
        (op (smallEtaleFinal B E h S hS p z))
      ((liftedSmallEtaleIsoOfInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom).hom.app
        (op (smallEtaleFinal B E h S hS p z)) m)
  have e45 := Stacks.Sites.quasiCoherentPresheafBaseChangeIso_inv_map_smul 𝓕 X A eo.hom
    (show Γ(A.left, ⊤) from c) (F23 ((restrictModuleToSmallEtaleFinalIso B E h S hS p hp z
      (etaleTopology B) (etaleTopology_le_topology B) F).inv s))
  exact (congrArg (fun y => pullbackSectionsMap 𝓕 eo.hom
      (((Scheme.Modules.pullbackComp A.hom X.hom).hom.app 𝓕).app ⊤ y))
      ((congrArg F23 e1).trans e23)).trans
    (e45.trans (congrArg (· • _) (Stacks.Sites.appTop_apply_of_eq_id eo.hom.left rfl _)))

end Semilinear

/-- **Cartesianness of `F` along `n` from cartesianness of the presheaf of Stacks 03DS.**  For an
arrow `n : y ⟶ x` and a quasi-coherent `𝒪_U`-module `𝓕` identified with `F|_{U_ét}`, if the
identifications of sections of Stacks 076T at `𝟙 x` and at `n` are defined, the restriction map
of `F` along `n` is a base change as soon as the restriction map of the presheaf of modules
`T ↦ Γ(T, T.hom⁺ 𝓕)` along the arrow of the big fppf site of `U` below `n` is: the two
identifications of sections are linear and intertwine the two restriction maps (the cocycle
condition). -/
theorem bijective_restrictionBaseChange_of_liftedSectionsIsoOfInv
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    {x y : 𝒳} (n : y ⟶ x) (𝓕 : (p.obj x).left.1.Modules) [h𝓕 : 𝓕.IsQuasicoherent]
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMy : Presheaf.IsSheaf (SmallEtale.topology E (p.obj y).left.1
        (contains_base B E h S hS p y))
      (restrictModuleToSmallEtale B E h S hS p hp y (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F (𝟙 x) 𝓕 hMx hMx eU.hom)]
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F n 𝓕 hMx hMy eU.hom)]
    (hcoc : F.presheaf.map n.op ≫
        (liftedSectionsIsoOfInv B E h S hS p hp F n 𝓕 h𝓕 hMx hMy eU).hom =
      (liftedSectionsIsoOfInv B E h S hS p hp F (𝟙 x) 𝓕 h𝓕 hMx hMx eU).hom ≫
        (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map
          (belowArrowSite B S hS p n (𝟙 x) n (Category.comp_id n).symm).op)
    (hP : Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange
      (R := BigFppfOver.commStructurePresheaf B (p.obj x).left.1 (p.obj x).left.2)
      (BigFppfOver.sectionsPresheafOfModules B (p.obj x).left.1 (p.obj x).left.2 𝓕)
      (belowArrowSite B S hS p n (𝟙 x) n (Category.comp_id n).symm).op)) :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      F n.op) :=
  Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_addEquiv
    (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (R' := BigFppfOver.commStructurePresheaf B (p.obj x).left.1 (p.obj x).left.2)
    F (BigFppfOver.sectionsPresheafOfModules B (p.obj x).left.1 (p.obj x).left.2 𝓕)
    n.op (belowArrowSite B S hS p n (𝟙 x) n (Category.comp_id n).symm).op
    (RingEquiv.refl _) (RingEquiv.refl _) (fun _ => rfl)
    (liftedSectionsIsoOfInv B E h S hS p hp F (𝟙 x) 𝓕 h𝓕 hMx hMx eU).addCommGroupIsoToAddEquiv
    (liftedSectionsIsoOfInv B E h S hS p hp F n 𝓕 h𝓕 hMx hMy eU).addCommGroupIsoToAddEquiv
    (liftedSectionsIsoOfInv_hom_smul B E h S hS p hp F (𝟙 x) 𝓕 hMx hMx eU)
    (liftedSectionsIsoOfInv_hom_smul B E h S hS p hp F n 𝓕 hMx hMy eU)
    (Stacks.PresheafOfModules.addCommGroupIsoToAddEquiv_map_apply_of_comm
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      (R' := BigFppfOver.commStructurePresheaf B (p.obj x).left.1 (p.obj x).left.2) F
      (BigFppfOver.sectionsPresheafOfModules B (p.obj x).left.1 (p.obj x).left.2 𝓕) n.op
      (belowArrowSite B S hS p n (𝟙 x) n (Category.comp_id n).symm).op
      (liftedSectionsIsoOfInv B E h S hS p hp F (𝟙 x) 𝓕 h𝓕 hMx hMx eU)
      (liftedSectionsIsoOfInv B E h S hS p hp F n 𝓕 h𝓕 hMx hMy eU) hcoc)
    hP

/-- **A module in `LQCoh^{fbc}(𝒪_𝒳)` is cartesian along an arrow lying over a flat morphism of
affine schemes.**  For `n : y ⟶ x` lying over a flat morphism with `p(x)`, `p(y)` affine, the
identifications of sections of Stacks 076T at `𝟙 x` and `n` are defined by the flat base change
property, and transport the cartesian property of the presheaf of Stacks 03DS between affine
objects (`AlgebraicGeometry.BigFppfOver.bijective_restrictionBaseChange_sectionsPresheafOfModules`)
to `ℱ`. -/
theorem bijective_restrictionBaseChange_of_locallyQuasicoherentFlatBaseChangeSheaf
    (ℱ : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (hℱ : locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp ℱ) {x y : 𝒳} (n : y ⟶ x)
    (hn : Flat (B.inclusion.map (p.map n).left))
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)))
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y))) :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      ℱ.val n.op) := by
  obtain ⟨hlqc, hfbc⟩ := hℱ
  obtain ⟨d⟩ := nonempty_quasicoherentBelow B E h S hS p hp ℱ.val hlqc x
  have := d.isQuasicoherent
  obtain ⟨hMy, -⟩ := hlqc.2 y
  have : IsIso (liftedSmallEtaleSheafInv B E h S hS p hp ℱ.val n d.val d.isSheaf hMy
      d.iso.hom) :=
    isIso_liftedSmallEtaleSheafInv_of_isIso_sheafifiedRestrictComparison B E h S hS p hp ℱ.val
      n d.val d.isSheaf hMy d.iso.hom (Iso.isIso_hom d.iso) (hfbc n hn)
  have : IsIso (liftedSmallEtaleSheafInv B E h S hS p hp ℱ.val (𝟙 x) d.val d.isSheaf
      d.isSheaf d.iso.hom) :=
    isIso_liftedSmallEtaleSheafInv_of_isIso_sheafifiedRestrictComparison B E h S hS p hp ℱ.val
      (𝟙 x) d.val d.isSheaf d.isSheaf d.iso.hom (Iso.isIso_hom d.iso)
      (hfbc (𝟙 x) (by rw [p.map_id]; exact inferInstanceAs (Flat (𝟙 _))))
  have hcoc := liftedSectionsIsoOfInv_cocycle B E h S hS p hp ℱ.val d.val d.isQuasicoherent
    d.isSheaf d.iso n (𝟙 x) n (Category.comp_id n).symm d.isSheaf hMy
  have hP := BigFppfOver.bijective_restrictionBaseChange_sectionsPresheafOfModules B
    (p.obj x).left.1 (p.obj x).left.2 d.val
    (belowArrowSite B S hS p n (𝟙 x) n (Category.comp_id n).symm) hy hx
  exact bijective_restrictionBaseChange_of_liftedSectionsIsoOfInv B E h S hS p hp ℱ.val n d.val
    d.isSheaf hMy d.iso hcoc hP

end AlgebraicGeometry.Stack
