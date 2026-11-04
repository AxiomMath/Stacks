module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsCorepresentable
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandNoSliceSheafify
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RestrictScalarsBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineGlobalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorFlatFppf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtalePullbackFinalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineCharts

/-!
# Flat base change on sections over affine objects

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `𝓕` an `𝒪_𝒳`-module on
`𝒳_étale` which is locally quasi-coherent (**Stacks 06WJ**) and has the flat base change property
(**Stacks 0762**).  For an arrow `φ : z ⟶ x` of `𝒳` lying over a flat morphism of *affine*
schemes `Z ⟶ U`, the base-change comparison `Γ(Z, 𝒪) ⊗_{Γ(U, 𝒪)} 𝓕(x) ⟶ 𝓕(z)` is an
isomorphism.

## The argument

The flat base change property says that the comparison map `c_φ : a^*(𝓕|_{U_ét}) ⟶ 𝓕|_{Z_ét}` of
**Stacks 06WC** is locally bijective.  Composition with it is therefore a bijection on maps into
any sheaf `L` of modules on `Z_ét`, and through the pullback–direct image adjunction the
restriction `𝓕|_{Z_ét}` corepresents `L ↦ Hom(𝓕|_{U_ét}, a_*L)`.  Both restrictions are
quasi-coherent on the small étale sites of affine schemes, so maps out of them are maps out of
their sections over the final objects; and every module over the ring of global functions on `Z` is
the sections of a sheaf of modules.  The corepresentability of base change through global sections,
`ModuleCat.isIso_extendScalars_homEquiv_symm_of_corepresents`, then says that the comparison on
global sections is an isomorphism.

## Main results

* `ModuleCat.isIso_extendScalars_homEquiv_symm_of_ringSquare`: base change comparisons agree
  across a square of rings with invertible vertical maps.
* `AlgebraicGeometry.Stack.isIso_extendScalars_app_of_bijective_comp_pushforward`: a comparison
  into a direct image which corepresents is an isomorphism after base change on sections over an
  affine terminal object.
* `AlgebraicGeometry.Stack.isIso_extendScalars_restrictModulePushforwardComparison_final`: the
  statement on the small étale sites.
* `AlgebraicGeometry.Stack.isIso_restrictionBaseChange_of_flat`: **affine flat base change** for
  a module which is locally quasi-coherent with the flat base change property.
* `AlgebraicGeometry.Stack.isCartesianAlongFlatAffine_of_lqcohSheafFbcFppfModules`: every object
  of `LQCoh^fbc(𝒪_𝒳)` is cartesian along flat arrows between affine objects (the step R2 of the
  proof of **Stacks 0779**).

## References

* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace ModuleCat

open scoped TensorProduct ChangeOfRings

variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]

/-- The adjoint transpose of a linear map `M ⟶ f_* N` under extension and restriction of scalars
sends `b ⊗ m` to `b • g m`. -/
theorem extendRestrictScalarsAdj_homEquiv_symm_tmul (f : A →+* B) {M : ModuleCat.{u} A}
    {N : ModuleCat.{u} B} (g : M ⟶ (ModuleCat.restrictScalars f).obj N) (b : B) (m : M) :
    ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm g (b ⊗ₜ[A, f] m) = b • g m := by
  let adj := ModuleCat.extendRestrictScalarsAdj f
  have hone : ((adj.homEquiv _ _).symm g) ((1 : B) ⊗ₜ[A, f] m) = g m :=
    congrArg (fun k => k m) ((adj.homEquiv _ _).apply_symm_apply g)
  have hsm := ((adj.homEquiv _ _).symm g).hom.map_smul b ((1 : B) ⊗ₜ[A, f] m)
  exact (congrArg (fun c => ((adj.homEquiv _ _).symm g).hom (c ⊗ₜ[A, f] m))
    (mul_one b).symm).trans (hsm.trans (congrArg (fun z => b • z) hone))

/-- **Base change comparisons agree across a square of rings with invertible vertical maps.**
Let `f : A ⟶ B` and `r : C ⟶ D` be ring maps and `α : A ⟶ C`, `β : B ⟶ D` bijective ring maps
with `β ∘ f = r ∘ α`.  An `r`-semilinear map `g : P ⟶ Q` is also `f`-semilinear once the scalars
of `P` and `Q` are restricted along `α` and `β`; if its base change `B ⊗_A P ⟶ Q` along `f` is an
isomorphism, so is its base change `D ⊗_C P ⟶ Q` along `r`. -/
theorem isIso_extendScalars_homEquiv_symm_of_ringSquare (f : A →+* B) (r : C →+* D)
    (α : A →+* C) (β : B →+* D) (hα : Function.Bijective α) (hβ : Function.Bijective β)
    (hsq : ∀ t, β (f t) = r (α t)) {P : ModuleCat.{u} C} {Q : ModuleCat.{u} D}
    (g : P ⟶ (ModuleCat.restrictScalars r).obj Q)
    (n : (ModuleCat.restrictScalars α).obj P ⟶
      (ModuleCat.restrictScalars f).obj ((ModuleCat.restrictScalars β).obj Q))
    (hn : ∀ x, n x = g x)
    (h : IsIso (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm n)) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj r).homEquiv _ _).symm g) := by
  let _ : Module A B := Module.compHom _ f
  let _ : Module C D := Module.compHom _ r
  let _ : Module A P := Module.compHom _ α
  let u := Stacks.RingSquare.tensorMap (P := P) f r (RingEquiv.ofBijective α hα)
    (RingEquiv.ofBijective β hβ) hsq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  have hu : Function.Bijective u := Stacks.RingSquare.bijective_tensorMap _ _ _ _ _ _ _ _
  let bf := ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm n
  let br := ((ModuleCat.extendRestrictScalarsAdj r).homEquiv _ _).symm g
  have hcomp : ∀ z, br.hom (u z) = bf.hom z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact (congrArg _ (map_zero u)).trans (br.hom.map_zero.trans bf.hom.map_zero.symm)
    | tmul c x =>
      refine (extendRestrictScalarsAdj_homEquiv_symm_tmul r g (β c) x).trans ?_
      refine Eq.trans ?_ (extendRestrictScalarsAdj_homEquiv_symm_tmul f n c x).symm
      exact congrArg (fun y => β c • (show Q from y)) (hn x).symm
    | add z w hz hw =>
      exact (congrArg _ (map_add u z w)).trans ((br.hom.map_add _ _).trans
        ((congrArg₂ (· + ·) hz hw).trans (bf.hom.map_add z w).symm))
  have hbf : Function.Bijective bf.hom := ConcreteCategory.bijective_of_isIso bf
  refine (ConcreteCategory.isIso_iff_bijective br).2 ⟨fun y y' hy => ?_, fun y => ?_⟩
  · obtain ⟨z, rfl⟩ := hu.2 y
    obtain ⟨z', rfl⟩ := hu.2 y'
    have : bf.hom z = bf.hom z' := (hcomp z).symm.trans (hy.trans (hcomp z'))
    rw [hbf.1 this]
  · obtain ⟨z, rfl⟩ := hbf.2 y
    exact ⟨u z, hcomp z⟩

end ModuleCat

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The ring of sections of the structure sheaf of a small étale site over an object is
commutative, being the ring of sections of the commutative structure presheaf. -/
theorem smallEtaleStructureSheaf_mul_comm (T : Scheme.{u}) (hT : E.Contains T)
    (W : (SmallEtale E T hT)ᵒᵖ) (a b : (SmallEtale.structureSheaf E T hT).obj.obj W) :
    a * b = b * a :=
  mul_comm (G := (SmallEtale.commStructurePresheaf E T hT).obj W) a b

/-- A ring whose multiplication is commutative, as a commutative ring with the given ring
structure, so that modules over the ring are modules over the commutative ring with no
transport. -/
abbrev commRingOfMulComm (A : Type*) [Ring A] (h : ∀ a b : A, a * b = b * a) : CommRing A :=
  { toRing := ‹Ring A›, mul_comm := h }

/-- **A comparison into a direct image which corepresents is an isomorphism after base change on
sections over an affine terminal object.**  Let `a : T' ⟶ T` be a morphism of schemes, `N` and
`K` sheaves of modules on the small étale sites of `T` and `T'` which are cartesian between affine
objects, and `κ : N ⟶ a_* K` a map such that composition with it is a bijection
`Hom(K, L) ≃ Hom(N, a_* L)` for every sheaf of modules `L` on `T'_ét`.  For an affine terminal
object `t` of `T_ét` whose base change is again affine and terminal, the base change of the
sections of `κ` over `t` is an isomorphism. -/
theorem isIso_extendScalars_app_of_bijective_comp_pushforward {T T' : Scheme.{u}}
    {hT : E.Contains T} {hT' : E.Contains T'}
    (a : E.obj T' hT' ⟶ E.obj T hT)
    (θ : (SmallEtale.structureSheaf E T hT).obj ⟶
      (smallEtaleBaseChange E a).op ⋙ (SmallEtale.structureSheaf E T' hT').obj)
    (N : SheafOfModules.{u} (SmallEtale.structureSheaf E T hT))
    (K : SheafOfModules.{u} (SmallEtale.structureSheaf E T' hT'))
    (hN : SmallEtale.IsCartesianOnAffines E T hT N)
    (hK : SmallEtale.IsCartesianOnAffines E T' hT' K)
    (κ : N.val ⟶ (PresheafOfModules.pushforward.{u} θ).obj K.val)
    (hκ : ∀ L : SheafOfModules.{u} (SmallEtale.structureSheaf E T' hT'),
      Function.Bijective (fun u : K ⟶ L => κ ≫ (PresheafOfModules.pushforward.{u} θ).map u.val))
    {t : SmallEtale E T hT} (ht : IsTerminal t)
    (hta : AlgebraicGeometry.IsAffine ((SmallEtale.toScheme E T hT).obj t))
    (ht' : IsTerminal ((smallEtaleBaseChange E a).obj t))
    (hta' : AlgebraicGeometry.IsAffine
      ((SmallEtale.toScheme E T' hT').obj ((smallEtaleBaseChange E a).obj t))) :
    letI := commRingOfMulComm _ (smallEtaleStructureSheaf_mul_comm E T hT (op t))
    letI := commRingOfMulComm (((smallEtaleBaseChange E a).op ⋙
      (SmallEtale.structureSheaf E T' hT').obj).obj (op t))
      (smallEtaleStructureSheaf_mul_comm E T' hT'
        ((smallEtaleBaseChange E a).op.obj (op t)))
    IsIso (((ModuleCat.extendRestrictScalarsAdj.{u} (θ.app (op t)).hom).homEquiv _ _).symm
      (κ.app (op t))) := by
  let := commRingOfMulComm _ (smallEtaleStructureSheaf_mul_comm E T hT (op t))
  let := commRingOfMulComm (((smallEtaleBaseChange E a).op ⋙
    (SmallEtale.structureSheaf E T' hT').obj).obj (op t))
    (smallEtaleStructureSheaf_mul_comm E T' hT'
      ((smallEtaleBaseChange E a).op.obj (op t)))
  let G : SheafOfModules.{u} (SmallEtale.structureSheaf E T' hT') ⥤
      PresheafOfModules.{u} (SmallEtale.structureSheaf E T hT).obj :=
    SheafOfModules.forget _ ⋙ PresheafOfModules.pushforward.{u} θ
  let ΓD : SheafOfModules.{u} (SmallEtale.structureSheaf E T' hT') ⥤
      ModuleCat.{u} (((smallEtaleBaseChange E a).op ⋙
        (SmallEtale.structureSheaf E T' hT').obj).obj (op t)) :=
    SheafOfModules.evaluation _ ((smallEtaleBaseChange E a).op.obj (op t))
  have : (smallEtaleBaseChange E a).IsContinuous (SmallEtale.topology E T hT)
      (SmallEtale.topology E T' hT') := smallEtaleBaseChange_isContinuous E a
  -- maps out of `N` are determined by sections over `t`
  have h₂ : ∀ L, Function.Bijective (fun u : N.val ⟶ G.obj L => u.app (op t)) := fun L =>
    SmallEtale.bijective_app_of_isTerminal_of_isCartesianOnAffines E T hT N
      (G.obj L) ((smallEtaleBaseChange E a).op_comp_isSheaf _ _ ⟨L.val.presheaf, L.isSheaf⟩)
      hN ht hta
  -- maps out of `K` are determined by sections over the base change of `t`
  have h₃ : ∀ L, Function.Bijective (fun u : K ⟶ L => ΓD.map u) := fun L =>
    SmallEtale.bijective_val_app_of_isTerminal_of_isCartesianOnAffines E T' hT' K L
      hK ht' hta'
  obtain ⟨L₁, ⟨e⟩⟩ := SmallEtale.exists_sheafOfModules_sections_iso_structureSheaf E T'
    hT' ht' hta' ((ModuleCat.extendScalars (θ.app (op t)).hom).obj (N.val.obj (op t)))
  refine ModuleCat.isIso_extendScalars_homEquiv_symm_of_corepresents' (θ.app (op t)).hom ΓD
    (N.val.obj (op t)) (κ.app (op t)) (fun L => ?_) h₃ e
  exact (h₂ L).comp (hκ L)

/-- For an `𝒪_𝒳`-module with the flat base change property and an arrow `φ : z ⟶ x` lying over a
flat morphism `a : Z ⟶ U`, composition with the comparison `𝓕|_{U_ét} ⟶ a_*(𝓕|_{Z_ét})` of
**Stacks 06W2** is a bijection `Hom(𝓕|_{Z_ét}, L) ≃ Hom(𝓕|_{U_ét}, a_* L)` for every sheaf of
modules `L` on `Z_ét`: through the pullback–direct image adjunction it is composition with the
comparison `a^*(𝓕|_{U_ét}) ⟶ 𝓕|_{Z_ét}` of **Stacks 06WC**, which is locally bijective. -/
theorem bijective_comp_restrictModulePushforwardComparison
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp F)
    {z x : 𝒳} (φ : z ⟶ x) (hφ : Flat (B.inclusion.map (p.map φ).left))
    (L : SheafOfModules.{u}
      (SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z))) :
    Function.Bijective (fun u : restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F ⟶ L.val =>
      restrictModulePushforwardComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) F ≫
      (PresheafOfModules.pushforward.{u} (smallEtaleStructureComparison B E h S hS p hp φ
        (etaleTopology B) (etaleTopology_le_topology B))).map u) := by
  let c := restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
    (etaleTopology_le_topology B) F
  obtain ⟨hinj, hsurj⟩ := hF.2 φ hφ
  have : PresheafOfModules.IsLocallyInjective
      (SmallEtale.topology E (p.obj z).left.1 (contains_base B E h S hS p z)) c := hinj
  have : PresheafOfModules.IsLocallySurjective
      (SmallEtale.topology E (p.obj z).left.1 (contains_base B E h S hS p z)) c := hsurj
  let adj := PresheafOfModules.pullbackPushforwardAdjunction.{u}
    (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B))
  have hfac : (fun u : restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F ⟶ L.val =>
      restrictModulePushforwardComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) F ≫
      (PresheafOfModules.pushforward.{u} (smallEtaleStructureComparison B E h S hS p hp φ
        (etaleTopology B) (etaleTopology_le_topology B))).map u) =
      (adj.homEquiv _ _) ∘ (fun v => c ≫ v) := by
    funext u
    simp only [Function.comp_apply]
    rw [Adjunction.homEquiv_naturality_right, restrictModulePullbackComparisonUnivLE_adjunct]
  rw [hfac]
  exact (adj.homEquiv _ _).bijective.comp
    (Stacks.Sites.homEquivOfIsLocallyBijective c L.isSheaf).bijective

/-- **Flat base change on global sections, on the small étale sites.**  For an arrow `φ : z ⟶ x`
lying over a flat morphism of affine schemes `Z ⟶ U`, and an `𝒪_𝒳`-module which is locally
quasi-coherent with the flat base change property, the base change along `Γ(U) ⟶ Γ(Z ×_U U)` of
the map of global sections underlying the comparison of **Stacks 06W2** is an isomorphism. -/
theorem isIso_extendScalars_restrictModulePushforwardComparison_final
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp F)
    {z x : 𝒳} (φ : z ⟶ x) (hφ : Flat (B.inclusion.map (p.map φ).left))
    (hx : IsAffine ((SmallEtale.toScheme E (p.obj x).left.1 (contains_base B E h S hS p x)).obj
      (smallEtaleFinal B E h S hS p x)))
    (hz : IsAffine ((SmallEtale.toScheme E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
      ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj
        (smallEtaleFinal B E h S hS p x)))) :
    letI := commRingOfMulComm _ (smallEtaleStructureSheaf_mul_comm E (p.obj x).left.1
      (contains_base B E h S hS p x) (op (smallEtaleFinal B E h S hS p x)))
    letI := commRingOfMulComm
      (((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op ⋙
      (SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z)).obj).obj
        (op (smallEtaleFinal B E h S hS p x)))
      (smallEtaleStructureSheaf_mul_comm E (p.obj z).left.1 (contains_base B E h S hS p z)
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op.obj
          (op (smallEtaleFinal B E h S hS p x))))
    IsIso (((ModuleCat.extendRestrictScalarsAdj.{u}
        ((smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B)).app (op (smallEtaleFinal B E h S hS p x))).hom).homEquiv
        _ _).symm
      ((restrictModulePushforwardComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) F).app (op (smallEtaleFinal B E h S hS p x)))) := by
  refine isIso_extendScalars_app_of_bijective_comp_pushforward E
    (smallEtaleBaseMorphism B E h S hS p φ) _ ⟨_, (hF.1.2 x).1⟩ ⟨_, (hF.1.2 z).1⟩ ?_ ?_ _ ?_
    (SmallEtale.finalIsTerminal E _ _) hx
    (smallEtaleBaseChange_finalIsTerminal E (smallEtaleBaseMorphism B E h S hS p φ)) hz
  · exact SmallEtale.isCartesianOnAffines_of_isQuasicoherentOnSite E _ _ _ (hF.1.2 x).2
  · exact SmallEtale.isCartesianOnAffines_of_isQuasicoherentOnSite E _ _ _ (hF.1.2 z).2
  · exact fun L => (bijective_comp_restrictModulePushforwardComparison B E h S hS p hp F hF φ hφ
      L).comp ⟨fun _ _ h => SheafOfModules.hom_ext h, fun v => ⟨⟨v⟩, rfl⟩⟩

/-- **Affine flat base change for `LQCoh^fbc` (the step R2 of Stacks 0779).**  Let `𝓕` be an
`𝒪_𝒳`-module which is locally quasi-coherent with the flat base change property, and let
`φ : z ⟶ x` be an arrow of `𝒳` lying over a flat morphism of affine schemes `Z ⟶ U`.  Then the
base-change comparison `𝒪(z) ⊗_{𝒪(x)} 𝓕(x) ⟶ 𝓕(z)` is an isomorphism.

On the small étale sites this is
`AlgebraicGeometry.Stack.isIso_extendScalars_restrictModulePushforwardComparison_final`; the
comparison of Stacks 06W2 at the final object is restriction of `𝓕` along an arrow of `𝒳` which
is isomorphic to `φ` (`AlgebraicGeometry.Stack.exists_restrictionComparisonLift`), and the rings
of the two small étale sites are identified with those of `𝒳` by Stacks 06W9. -/
theorem isIso_restrictionBaseChange_of_flat
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp F)
    {z x : 𝒳} (φ : z ⟶ x) (hφ : Flat (B.inclusion.map (p.map φ).left))
    (hz : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)))
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x))) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      F φ.op) := by
  let := isEquivalence_overPost B S hS p hp z
  let := isEquivalence_overPost B S hS p hp x
  have hZ' : IsTerminal ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj
      (smallEtaleFinal B E h S hS p x)) :=
    smallEtaleBaseChange_finalIsTerminal E (smallEtaleBaseMorphism B E h S hS p φ)
  obtain ⟨φ', hfac, hbase⟩ :=
    exists_restrictionComparisonLift B E h S hS p hp φ (smallEtaleFinal B E h S hS p x)
  -- the small étale statement
  have hx' : IsAffine ((SmallEtale.toScheme E (p.obj x).left.1
      (contains_base B E h S hS p x)).obj (smallEtaleFinal B E h S hS p x)) := hx
  have hz' : IsAffine ((SmallEtale.toScheme E (p.obj z).left.1
      (contains_base B E h S hS p z)).obj
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj
          (smallEtaleFinal B E h S hS p x))) := by
    let e := hZ'.uniqueUpToIso (SmallEtale.finalIsTerminal E (p.obj z).left.1
      (contains_base B E h S hS p z))
    have : IsAffine ((SmallEtale.toScheme E (p.obj z).left.1
        (contains_base B E h S hS p z)).obj (smallEtaleFinal B E h S hS p z)) := hz
    exact IsAffine.of_isIso ((SmallEtale.toScheme E _ _).map e.hom)
  let := commRingOfMulComm _ (smallEtaleStructureSheaf_mul_comm E (p.obj x).left.1
    (contains_base B E h S hS p x) (op (smallEtaleFinal B E h S hS p x)))
  let := commRingOfMulComm
    (((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op ⋙
      (SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z)).obj).obj
        (op (smallEtaleFinal B E h S hS p x)))
    (smallEtaleStructureSheaf_mul_comm E (p.obj z).left.1 (contains_base B E h S hS p z)
      ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op.obj
        (op (smallEtaleFinal B E h S hS p x))))
  have hsm := isIso_extendScalars_restrictModulePushforwardComparison_final B E h S hS p hp F hF
    φ hφ hx' hz'
  -- the comparison at the final object is restriction along `φ'`, on the module and the ring
  have hmod := restrictionPushforwardComparison_app B E h S hS p hp φ F.presheaf
    (smallEtaleFinal B E h S hS p x) φ' hfac hbase
  have hring := restrictionPushforwardComparison_app B E h S hS p hp φ
    (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj
    (smallEtaleFinal B E h S hS p x) φ' hfac hbase
  let ιx := localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
    (etaleTopology_le_topology B)
  let ιz := localStructurePresheafIso B E h S hS p hp z (etaleTopology B)
    (etaleTopology_le_topology B)
  have hsq : ∀ t, (ιz.hom.app
      ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op.obj
        (op (smallEtaleFinal B E h S hS p x)))).hom
      ((smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B)).app (op (smallEtaleFinal B E h S hS p x)) t) =
      ((structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj.map
        φ'.op).hom ((ιx.hom.app (op (smallEtaleFinal B E h S hS p x))).hom t) := fun t => by
    have hcancel := ConcreteCategory.congr_hom (ιz.inv_hom_id_app
      ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op.obj
        (op (smallEtaleFinal B E h S hS p x))))
      ((restrictionPushforwardComparison B E h S hS p hp φ (ringStructureSheafCore B S hS p hp
        (etaleTopology B) (etaleTopology_le_topology B)).obj).app
          (op (smallEtaleFinal B E h S hS p x))
        ((ιx.hom.app (op (smallEtaleFinal B E h S hS p x))) t))
    simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at hcancel
    exact hcancel.trans (ConcreteCategory.congr_hom hring _)
  have key : IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      F φ'.op) := by
    refine ModuleCat.isIso_extendScalars_homEquiv_symm_of_ringSquare
      (f := ((smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B)).app (op (smallEtaleFinal B E h S hS p x))).hom)
      (α := (ιx.hom.app (op (smallEtaleFinal B E h S hS p x))).hom)
      (β := (ιz.hom.app
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op.obj
          (op (smallEtaleFinal B E h S hS p x)))).hom)
      (r := ((structureSheaf B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)).obj.map φ'.op).hom) ?_ ?_ hsq (F.map φ'.op)
      ((restrictModulePushforwardComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) F).app (op (smallEtaleFinal B E h S hS p x))) ?_ ?_
    · exact ConcreteCategory.bijective_of_isIso
        (ιx.hom.app (op (smallEtaleFinal B E h S hS p x)))
    · exact ConcreteCategory.bijective_of_isIso
        (ιz.hom.app
          ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op.obj
            (op (smallEtaleFinal B E h S hS p x))))
    · exact fun y => ConcreteCategory.congr_hom hmod y
    · exact hsm
  -- `φ'` is isomorphic to `φ` as an arrow
  have hterm : ∀ {X : 𝒳} {Y : Over X}, IsTerminal Y → IsIso Y.hom := fun {X Y} hY => by
    let e := hY.uniqueUpToIso Over.mkIdTerminal
    have : IsIso e.hom.left := ((Over.forget X).mapIso e).isIso_hom
    have hw : Y.hom = e.hom.left := by simpa using (Over.w e.hom).symm
    rw [hw]
    infer_instance
  have hinc : ∀ (w : 𝒳) [(Over.post (X := w) (p ⋙ Over.forget (B.obj hS))).IsEquivalence]
      (Y : SmallEtale E (p.obj w).left.1 (contains_base B E h S hS p w)),
      IsTerminal Y → IsIso ((Over.post (X := w) (p ⋙ Over.forget (B.obj hS))).inv.obj
        ((smallEtaleInclusion B E h (p.obj w).left.1 (contains_base B E h S hS p w)).obj Y)).hom :=
    fun w _ Y hY => hterm (IsTerminal.isTerminalObj _ _
      ((isTerminal_smallEtaleInclusion_obj_final B E h S hS p w).ofIso
        ((smallEtaleInclusion B E h _ _).mapIso
          (hY.uniqueUpToIso (SmallEtale.finalIsTerminal E _ _))).symm))
  have hy := hinc x _ (SmallEtale.finalIsTerminal E _ _)
  have hx'' := hinc z _ hZ'
  refine (ConcreteCategory.isIso_iff_bijective _).2
    ((Stacks.PresheafOfModules.bijective_restrictionBaseChange_iff_of_arrowIso
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj) F
      φ.op φ'.op ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.obj
        ((smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)).obj
          (smallEtaleFinal B E h S hS p x))).hom.op
      ((Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).inv.obj
        ((smallEtaleInclusion B E h (p.obj z).left.1 (contains_base B E h S hS p z)).obj
          ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj
            (smallEtaleFinal B E h S hS p x)))).hom.op ?_).2
      ((ConcreteCategory.isIso_iff_bijective _).1 key))
  rw [← op_comp, ← op_comp, hfac]

/-- **Every object of `LQCoh^fbc(𝒪_𝒳)` is cartesian along flat arrows between affine objects**
(the step R2 of the proof of **Stacks 0779**): for an arrow `φ : z ⟶ x` of `𝒳` lying over a flat
morphism of affine schemes, `𝒪(z) ⊗_{𝒪(x)} 𝓕(x) ⟶ 𝓕(z)` is an isomorphism. -/
theorem isCartesianAlongFlatAffine_of_lqcohSheafFbcFppfModules {𝒴 : AlgebraicStacks.{u, w} B S hS}
    (F : fppfModules B S hS 𝒴) (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴 F) :
    IsCartesianAlongFlatAffine B S hS 𝒴 F := fun _ _ φ hφ hz hx =>
  isIso_restrictionBaseChange_of_flat B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids F.val hF
    φ hφ hz hx

end AlgebraicGeometry.Stack

end
