module

public import StacksFrontier.Deformation.PredeformationTangent.DerivationMap
public import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace

/-!
# Linearity of the derivation map

For a predeformation category satisfying Schlessinger's condition (S2), pushforward of the
distinguished object along a derivation gives a linear map to the associated tangent-space
functor.

## Main results

* `Deformation.derivationMap_linear` identifies the derivation map with a linear map into the
  canonical vector-space structure of Tag 06IH.

## Implementation notes

The target is presented at the canonical Artinian square-zero extension. The
isomorphism-class quotient underlying the associated functor is identified with the skeleton
of the corresponding fibre, as in the construction of `gamma` in
`Deformation.DerivationMapAndAction`. The square-zero extension carries the coordinates of
`Deformation.squareZeroCoordinates`, so its vector-space structure agrees with Tag 06IH.

Linearity is proved by comparing the derivation map at `V` with its value at `V × V`, using
that the derivation map is natural in `V`: the sum of two derivations is the image of a single
derivation into `V × V` along the addition map, and scalar multiplication is the image along
the corresponding scalar endomorphism.

## References

* [Stacks Project, Tag 06SU](https://stacks.math.columbia.edu/tag/06SU)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory

universe u w u₁ v₁ uR uC vC uM

attribute [local instance] derivationMapModuleMulOpposite derivationMapIsCentralScalar
  derivationMapModuleOfAlgebra derivationMapIsScalarTower
  derivationMapIsScalarTowerMulOpposite

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsPredeformationCategory 𝓕.p)
    (A₀ : ArtinianLocalAlgCat.{u, w, w} Λ k) (i₀ : A₀ ≃ₐ[Λ] k)
    (hi₀ : ∀ a : A₀, A₀.residueEquiv (IsLocalRing.residue A₀ a) = i₀ a)
    (x₀ : 𝓕.obj) (hx₀ : 𝓕.p.obj x₀ = A₀)

/-- Morphisms out of an Artinian local algebra with residue field `k` are determined by their
values on the image of `i.symm`. -/
private theorem artinianHom_ext_of_symm {A B : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (i : A ≃ₐ[Λ] k) {f g : A ⟶ B} (h : ∀ a, f.hom (i.symm a) = g.hom (i.symm a)) : f = g := by
  apply ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  simpa using h (i a)

/-- The class of the pushforward of the distinguished object along the derivation map. -/
noncomputable def derivationClassMap (V : FGModuleCat.{w} k) (D : Derivation Λ k V) :
    (isomorphismClasses 𝓕 h𝓕.cofibered).obj
      ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj V) :=
  (isomorphismClasses 𝓕 h𝓕.cofibered).map
    ((squareZeroDerivationMapAndAction.{u, w, w, u₁, v₁} 𝓕.p h𝓕 A₀ i₀ hi₀ V x₀ hx₀).baseMap D)
    (classOf 𝓕 h𝓕.cofibered ⟨x₀, hx₀⟩)

/-- The derivation map in the canonical square-zero coordinates is natural in the vector
space. -/
theorem squareZeroDerivationMapAndAction_baseMap_natural
    {V W : FGModuleCat.{w} k} (f : V ⟶ W) (D : Derivation Λ k V) :
    (squareZeroDerivationMapAndAction.{u, w, w, u₁, v₁}
          𝓕.p h𝓕 A₀ i₀ hi₀ W x₀ hx₀).baseMap (f.hom.hom.compDer D) =
      (squareZeroDerivationMapAndAction.{u, w, w, u₁, v₁}
          𝓕.p h𝓕 A₀ i₀ hi₀ V x₀ hx₀).baseMap D ≫
        (squareZeroExtensionArtinian.{u, w, w} Λ k).map f := by
  let dV := squareZeroDerivationMapAndAction.{u, w, w, u₁, v₁} 𝓕.p h𝓕 A₀ i₀ hi₀ V x₀ hx₀
  let dW := squareZeroDerivationMapAndAction.{u, w, w, u₁, v₁} 𝓕.p h𝓕 A₀ i₀ hi₀ W x₀ hx₀
  apply artinianHom_ext_of_symm i₀
  intro a
  have hW := dW.baseMap_apply (f.hom.hom.compDer D) a
  have hV := dV.baseMap_apply D a
  show (dW.baseMap (f.hom.hom.compDer D)).hom (i₀.symm a) =
    (dV.baseMap D ≫ (squareZeroExtensionArtinian.{u, w, w} Λ k).map f).hom (i₀.symm a)
  rw [hW, ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply, hV]
  show TrivSqZeroExt.inl a + TrivSqZeroExt.inr (f.hom.hom (D a)) =
    TrivSqZeroExt.map f.hom.hom (TrivSqZeroExt.inl a + TrivSqZeroExt.inr (D a))
  rw [map_add, TrivSqZeroExt.map_inl, TrivSqZeroExt.map_inr]

/-- The class of the derivation pushforward is natural in the vector space. -/
theorem derivationClassMap_natural
    {V W : FGModuleCat.{w} k} (f : V ⟶ W) (D : Derivation Λ k V) :
    derivationClassMap 𝓕 h𝓕 A₀ i₀ hi₀ x₀ hx₀ W (f.hom.hom.compDer D) =
      (isomorphismClasses 𝓕 h𝓕.cofibered).map
        ((squareZeroExtensionArtinian.{u, w, w} Λ k).map f)
        (derivationClassMap 𝓕 h𝓕 A₀ i₀ hi₀ x₀ hx₀ V D) := by
  dsimp only [derivationClassMap]
  rw [squareZeroDerivationMapAndAction_baseMap_natural]
  simp only [Functor.map_comp]
  rfl

/-- Any choice of derivation data in the canonical square-zero coordinates has the same
derivation map, namely the class of the pushforward. -/
theorem derivationClassMap_eq_gamma {V : FGModuleCat.{w} k}
    (hiV : ∀ a : (squareZeroExtensionArtinian.{u, w, w} Λ k).obj V,
      ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj V).residueEquiv
        (IsLocalRing.residue ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj V) a) =
          (TrivSqZeroExt.fstHom Λ k V) (squareZeroCoordinates.{u, w, w} V a))
    (d : DerivationMapAndAction 𝓕.p A₀
      ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj V) i₀
      (squareZeroCoordinates.{u, w, w} V) hi₀ hiV x₀ hx₀)
    (D : Derivation Λ k V) :
    derivationClassMap 𝓕 h𝓕 A₀ i₀ hi₀ x₀ hx₀ V D =
      cast (isomorphismClasses_obj 𝓕 h𝓕.cofibered
        ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj V)).symm (d.gamma D) := by
  have hbase : d.baseMap D =
      (squareZeroDerivationMapAndAction.{u, w, w, u₁, v₁} 𝓕.p h𝓕 A₀ i₀ hi₀ V x₀ hx₀).baseMap D := by
    apply artinianHom_ext_of_symm i₀
    intro a
    exact (d.baseMap_eq D a).trans
      ((squareZeroDerivationMapAndAction.{u, w, w, u₁, v₁}
        𝓕.p h𝓕 A₀ i₀ hi₀ V x₀ hx₀).baseMap_eq D a).symm
  obtain ⟨y, φ, hfac, hγ⟩ := d.gamma_pushforward D
  have hφ : 𝓕.p.IsHomLift (d.baseMap D) φ :=
    IsHomLift.of_fac' 𝓕.p (d.baseMap D) φ hx₀ y.2 hfac
  have hmap := map_classOf 𝓕 h𝓕.cofibered (d.baseMap D) ⟨x₀, hx₀⟩ y φ
  have hy := classOf_eq 𝓕 h𝓕.cofibered y
  have hEq := isomorphismClasses_obj 𝓕 h𝓕.cofibered
    ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj V)
  have hcast : cast hEq (classOf 𝓕 h𝓕.cofibered y) = d.gamma D := by
    simpa using hy.trans hγ
  have hy' : classOf 𝓕 h𝓕.cofibered y = cast hEq.symm (d.gamma D) := by
    rw [← hcast]
    simp
  dsimp only [derivationClassMap]
  rw [← hbase]
  exact hmap.trans hy'

/-- Transporting along an equality of set-valued functors commutes with the functorial
action. -/
theorem functor_map_cast {R : Type uR} [CommRing R]
    {C : Type uC} [Category.{vC} C] [Preadditive C] [CategoryTheory.Linear R C]
    {F G : C ⥤ Type uM} (e : F = G) {X Y : C} (f : X ⟶ Y) (x : G.obj X) :
    cast (congrArg (fun H : C ⥤ Type uM => H.obj Y) e).symm (G.map f x) =
      F.map f (cast (congrArg (fun H : C ⥤ Type uM => H.obj X) e).symm x) := by
  cases e
  rfl

/-- **Stacks Project, Tag 06SU.** The map `γ_V` defined by pushforward along derivations is
linear for the canonical vector-space structure on the associated functor. -/
@[stacks 06SU "gamma_linear"]
theorem derivationMap_linear
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered)))
    (V : FGModuleCat.{w} k)
    (hiV : ∀ a : (squareZeroExtensionArtinian.{u, w, w} Λ k).obj V,
      ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj V).residueEquiv
        (IsLocalRing.residue ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj V) a) =
          (TrivSqZeroExt.fstHom Λ k V) (squareZeroCoordinates.{u, w, w} V a))
    (d : DerivationMapAndAction 𝓕.p A₀
      ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj V) i₀
      (squareZeroCoordinates.{u, w, w} V) hi₀ hiV x₀ hx₀) :
    let L := (associatedTangentSpaceModuleStructureUnlifted 𝓕 h𝓕 hS2).functor
    let AV := (squareZeroExtensionArtinian.{u, w, w} Λ k).obj V
    let hcarrier : ((L.obj V : ModuleCat.{u₁} k) : Type u₁) =
        (isomorphismClasses 𝓕 h𝓕.cofibered).obj AV :=
      congrArg (fun H : FGModuleCat.{w} k ⥤ Type u₁ ↦ H.obj V)
        (associatedTangentSpaceModuleStructureUnlifted 𝓕 h𝓕 hS2).forget_comp
    ∃ γ : Derivation Λ k V →ₗ[k] ((L.obj V : ModuleCat.{u₁} k) : Type u₁),
      ∀ D : Derivation Λ k V,
        γ D = cast hcarrier.symm
          (cast (isomorphismClasses_obj 𝓕 h𝓕.cofibered AV).symm (d.gamma D)) := by
  let M := associatedTangentSpaceModuleStructureUnlifted 𝓕 h𝓕 hS2
  let carrierEq (W : FGModuleCat.{w} k) :
      ((M.functor.obj W : ModuleCat.{u₁} k) : Type u₁) =
        (isomorphismClasses 𝓕 h𝓕.cofibered).obj
          ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj W) :=
    congrArg (fun H : FGModuleCat.{w} k ⥤ Type u₁ => H.obj W) M.forget_comp
  let γfun (W : FGModuleCat.{w} k) (D : Derivation Λ k W) :
      ((M.functor.obj W : ModuleCat.{u₁} k) : Type u₁) :=
    cast (carrierEq W).symm (derivationClassMap 𝓕 h𝓕 A₀ i₀ hi₀ x₀ hx₀ W D)
  have hnat {W Z : FGModuleCat.{w} k} (f : W ⟶ Z) (D : Derivation Λ k W)
      (D' : Derivation Λ k Z) (hD : f.hom.hom.compDer D = D') :
      γfun Z D' = (M.functor.map f) (γfun W D) := by
    subst hD
    dsimp only [γfun]
    rw [derivationClassMap_natural]
    exact functor_map_cast (R := k) M.forget_comp f
      (derivationClassMap 𝓕 h𝓕 A₀ i₀ hi₀ x₀ hx₀ W D)
  refine ⟨{ toFun := γfun V
            map_add' := ?_
            map_smul' := ?_ }, ?_⟩
  · intro D E
    let W := V.obj.carrier
    let : AddCommGroup W := V.obj.isAddCommGroup
    let : Module k W := V.obj.isModule
    let : Module.Finite k W := V.property
    let P : FGModuleCat.{w} k := prodFGModule k V V
    let f₁ : P ⟶ V := prodFst k V V
    let f₂ : P ⟶ V := prodSnd k V V
    let Dpair : Derivation Λ k (P.obj.carrier) :=
      { toLinearMap := LinearMap.prod D.toLinearMap E.toLinearMap
        map_one_eq_zero' := by
          show (D 1, E 1) = (0, 0)
          simp
        leibniz' a b := Prod.ext (D.leibniz a b) (E.leibniz a b) }
    have hn₁ := hnat f₁ Dpair D (Derivation.ext fun _ => rfl)
    have hn₂ := hnat f₂ Dpair E (Derivation.ext fun _ => rfl)
    have hnsum := hnat (f₁ + f₂) Dpair (D + E) (Derivation.ext fun _ => rfl)
    calc
      γfun V (D + E) = (M.functor.map (f₁ + f₂)) (γfun P Dpair) := hnsum
      _ = (M.functor.map f₁) (γfun P Dpair) + (M.functor.map f₂) (γfun P Dpair) :=
        congrArg (fun q : M.functor.obj P ⟶ M.functor.obj V => q (γfun P Dpair))
          (Functor.map_add M.functor)
      _ = γfun V D + γfun V E := by rw [← hn₁, ← hn₂]
  · intro r D
    let f : V ⟶ V := r • 𝟙 V
    have hn := hnat f D (r • D) (Derivation.ext fun _ => rfl)
    calc
      γfun V (r • D) = (M.functor.map (r • 𝟙 V)) (γfun V D) := hn
      _ = r • γfun V D := by
        rw [Functor.map_smul]
        simp
  · intro D
    show γfun V D = _
    dsimp only [γfun]
    rw [derivationClassMap_eq_gamma 𝓕 h𝓕 A₀ i₀ hi₀ x₀ hx₀ hiV d D]

end

end Deformation
