module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSquare
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SectionOfQuotient
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeInG
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleChartGlue

/-!
# The pullback `ψ'` of a map `ψ` given by a unital homomorphism, along a morphism of test objects

Let `ρ` be a restriction datum of Stacks 084A for graded algebras `Â T z` at the scheme points
`z : T ⟶ X` of a presheaf `X`. A map `ψ` over the identity of a scheme point `f : Z ⟶ X`, of the
shape the restriction of a pair `(ℒ, ψ)` on `X` to `Z` has, is the map `twistingOfUnitalHom` of a
unital homomorphism `Ψ : f^*𝒜 ⟶ ⨁_n ℒ^{⊗ n}` read through the identification
`(𝟙_Z)^*(f^*𝒜) = f^*𝒜`. For a morphism `τ : X' ⟶ Z` of test objects the pullback `ψ'` of `ψ`
to the square `X' = X' ⟶ Z` (`AlgebraicGeometry.Space.GradedAlgebraRestriction.squareTwisting`,
read over the identity of `X'`) is then, degreewise, the same identification on `X'`, followed by
the restriction map `(f ∘ τ)^*𝒜 ⟶ τ^*(f^*𝒜)` of the datum, the pullback `τ^*Ψ` and the comparison
`τ^*(ℒ^{⊗ n}) ≅ (τ^*ℒ)^{⊗ n}` of the tensor powers.

## Main results

* `AlgebraicGeometry.Space.GradedAlgebraRestriction.squareTwisting_id_twistingOfUnitalHom_app`:
  the degreewise formula for `ψ'`.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.twistingOfUnitalHom_eq_squareTwisting_id`:
  if a unital homomorphism `Ψ'` at `f ∘ τ` is degreewise the restriction map, `τ^*Ψ`, the
  comparison of the tensor powers and the Laurent algebra map of `e : τ^*ℒ ≅ ℒ'`, then its map is
  `ψ'` transported along `e`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.compComparison_id_comp_map_comp_inv` and
  `…compComparison_map_eqToHom_pullbackId`: the two unit coherences of the contraction of an
  iterated pullback used for it.

These are a step of the restriction of `(ℒ, ψ)` to the scheme points of an algebraic space in
Stacks 0D2Z.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProj

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {T S S' : Scheme.{u}}

/-- The components of a map `ψ` read over an equal base morphism: the given components, after the
identification of the two inverse images. -/
theorem Twisting.congrBase_app
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
    {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    {g g' : T ⟶ S} (h : g = g') (ψ : Twisting g A d L) (i : ℤ) :
    (Twisting.congrBase h ψ).app i =
      eqToHom (congrArg (fun k : T ⟶ S => (pullbackFunctor (ringedSpaceHom k)).obj
        (A.piece (i * d))) h.symm) ≫ ψ.app i := by
  subst h
  rw [eqToHom_refl, Category.id_comp]
  rfl

/-- **The contraction of an iterated pullback along the identity is undone by its inverse**:
for morphisms `h`, `h'` out of `T`, conjugating the inverse image along `𝟙_T` of a morphism
`c : h^*M ⟶ h'^*N` by the two contractions `(𝟙_T ∘ h)^*M ⟶ (𝟙_T)^*(h^*M)` and
`(𝟙_T ∘ h')^*N ⟶ (𝟙_T)^*(h'^*N)` returns `c`. -/
theorem compComparison_id_comp_map_comp_inv (h : T ⟶ S) (h' : T ⟶ S')
    (M : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace))
    (N : SheafOfModules.{u} (structureRingSheaf S'.toRingedSpace))
    (c : (pullbackFunctor (ringedSpaceHom h)).obj M ⟶
      (pullbackFunctor (ringedSpaceHom h')).obj N) :
    compComparison (𝟙 T) h M ≫ (pullbackFunctor (ringedSpaceHom (𝟙 T))).map c ≫
      inv (compComparison (𝟙 T) h' N) = c := by
  have e1 := compComparison_id h M
  have e2 := compComparison_id h' N
  have hn := (Stacks.PullbackTensorCoherence.pullbackIdIso T.toRingedSpace).hom.naturality c
  rw [IsIso.inv_eq_of_hom_inv_id e2]
  refine (congrArg (fun z => compComparison (𝟙 T) h M ≫ z) hn).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ (𝟭 _).map c) e1).trans ?_
  exact Category.id_comp c

/-- `compComparison_id_comp_map_comp_inv`, with two morphisms and a tail. -/
theorem compComparison_id_comp_map_comp_map_comp_inv_assoc (h : T ⟶ S) (h' : T ⟶ S')
    (M : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace))
    (N : SheafOfModules.{u} (structureRingSheaf S'.toRingedSpace))
    {P : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    {Q : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (a : (pullbackFunctor (ringedSpaceHom h)).obj M ⟶ P)
    (b : P ⟶ (pullbackFunctor (ringedSpaceHom h')).obj N)
    (r : (pullbackFunctor (ringedSpaceHom (𝟙 T ≫ h'))).obj N ⟶ Q) :
    compComparison (𝟙 T) h M ≫ (pullbackFunctor (ringedSpaceHom (𝟙 T))).map a ≫
      (pullbackFunctor (ringedSpaceHom (𝟙 T))).map b ≫ inv (compComparison (𝟙 T) h' N) ≫ r =
      a ≫ b ≫ r := by
  rw [← Functor.map_comp_assoc, reassoc_of% compComparison_id_comp_map_comp_inv h h' M N (a ≫ b)]
  exact Category.assoc _ _ _

/-- **The contraction of an iterated pullback along `g ≫ 𝟙_S`, followed by the inverse image of
the identification `(𝟙_S)^* ≅ 𝟭`, is the identity**, read degreewise with a transport of the
degree. -/
theorem compComparison_map_eqToHom_pullbackId (g : T ⟶ S)
    (M : ℤ → SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)) {k i : ℤ} (hk : k = i)
    {P : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)} (c : M i ⟶ P) :
    compComparison g (𝟙 S) (M k) ≫ (pullbackFunctor (ringedSpaceHom g)).map
        (eqToHom (congrArg (fun n => (pullbackFunctor (ringedSpaceHom (𝟙 S))).obj (M n)) hk) ≫
          (Scheme.Modules.pullbackId S).hom.app (M i) ≫ c) =
      eqToHom (by rw [Category.comp_id, hk]) ≫ (pullbackFunctor (ringedSpaceHom g)).map c := by
  subst hk
  have h' : (Scheme.Modules.pullbackComp g (𝟙 S)).inv.app (M k) ≫
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId S).hom.app (M k)) =
        eqToHom (by rw [Category.comp_id]; rfl) := by
    have h := NatTrans.congr_app (Scheme.Modules.pseudofunctor_left_unitality g) (M k)
    exact Eq.trans (Category.comp_id _).symm (Eq.trans (Category.assoc _ _ _)
      (h.trans (eqToHom_app _ _)))
  have e : compComparison g (𝟙 S) (M k) ≫ (pullbackFunctor (ringedSpaceHom g)).map
      ((Scheme.Modules.pullbackId S).hom.app (M k)) = eqToHom (by rw [Category.comp_id]; rfl) :=
    (congrArg (fun z => z ≫ (pullbackFunctor (ringedSpaceHom g)).map
      ((Scheme.Modules.pullbackId S).hom.app (M k)))
        (compComparison_eq_pullbackComp_inv g (𝟙 S) (M k))).trans h'
  refine (congrArg (fun z => compComparison g (𝟙 S) (M k) ≫
    (pullbackFunctor (ringedSpaceHom g)).map z) (Category.id_comp _)).trans ?_
  refine (congrArg (fun z => compComparison g (𝟙 S) (M k) ≫ z)
    ((pullbackFunctor (ringedSpaceHom g)).map_comp _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (fun z => z ≫ (pullbackFunctor (ringedSpaceHom g)).map c) e

/-- The identification of the inverse images along two equal morphisms, as a transport. -/
theorem pullbackCongr_hom_app_eq_eqToHom {f f' : T ⟶ S} (h : f = f')
    (M : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)) :
    (Scheme.Modules.pullbackCongr h).hom.app M =
      eqToHom (congrArg (fun m => (pullbackFunctor (ringedSpaceHom m)).obj M) h) := by
  subst h
  rfl

/-- `compComparison_map_eqToHom_pullbackId`, with a tail. -/
theorem compComparison_map_eqToHom_pullbackId_assoc (g : T ⟶ S)
    (M : ℤ → SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)) {k i : ℤ} (hk : k = i)
    {P : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)} (c : M i ⟶ P)
    {Q : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (r : (pullbackFunctor (ringedSpaceHom g)).obj P ⟶ Q) :
    compComparison g (𝟙 S) (M k) ≫ (pullbackFunctor (ringedSpaceHom g)).map
        (eqToHom (congrArg (fun n => (pullbackFunctor (ringedSpaceHom (𝟙 S))).obj (M n)) hk) ≫
          (Scheme.Modules.pullbackId S).hom.app (M i) ≫ c) ≫ r =
      eqToHom (by rw [Category.comp_id, hk]) ≫ (pullbackFunctor (ringedSpaceHom g)).map c ≫ r :=
  by rw [← Category.assoc, compComparison_map_eqToHom_pullbackId g M hk c, Category.assoc]

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

namespace CategoryTheory

/-- Reassociating a composite of six morphisms. -/
theorem comp_assoc_six {C : Type*} [Category* C] {a b c d e f g : C} (p : a ⟶ b) (q : b ⟶ c)
    (r : c ⟶ d) (s : d ⟶ e) (t : e ⟶ f) (v : f ⟶ g) :
    (p ≫ q ≫ r ≫ s ≫ t) ≫ v = p ≫ q ≫ r ≫ s ≫ t ≫ v := by
  simp only [Category.assoc]

/-- Two composites `eqToHom ≫ φ₁ ≫ φ₂ ≫ eqToHom ≫ r` of a degreewise family of morphisms, at two
equal degrees, agree. -/
theorem eqToHom_comp_comp_comp_eqToHom_comp {C : Type*} [Category* C] {F G H : ℤ → C}
    (φ₁ : ∀ n, F n ⟶ G n) (φ₂ : ∀ n, G n ⟶ H n) {k i : ℤ} (hk : k = i) {W : C}
    (r : H i ⟶ W) (p : F k = F k) (q : H k = H i) (p' : F k = F i) :
    eqToHom p ≫ φ₁ k ≫ φ₂ k ≫ eqToHom q ≫ r = eqToHom p' ≫ φ₁ i ≫ φ₂ i ≫ r := by
  subst hk
  simp

end CategoryTheory

namespace AlgebraicGeometry.Space.GradedAlgebraRestriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Â : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X) →
      SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T)}
    (ρ : GradedAlgebraRestriction (GradedAlgebraPoints.ofQuasicoherentFamily Â))
    (hc : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      B.Contains (relativeProj (Â T f)).scheme)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)

/-- **Restricting along the identity and then along `τ` is restricting along `τ`**, degreewise:
the inverse of the restriction map along `𝟙_{X'}` at a point `g₁` equal to `g`, followed by the
restriction map along `τ` to `g₁`, is the identification `(𝟙_{X'})^* ≅ 𝟭` followed by the
restriction map along `τ` to `g`. This is the identity coherence of the datum. -/
theorem inv_restrict_id_comp_restrict_assoc {Z X' : BigFppfOver B S hS} (τ : X' ⟶ Z)
    (f : yoneda.obj Z ⟶ X) (g g₁ : yoneda.obj X' ⟶ X) (h₁ : yoneda.map (𝟙 X') ≫ g = g₁)
    (h₂ : yoneda.map τ ≫ f = g₁) (hg : yoneda.map τ ≫ f = g) (n : ℤ)
    {W : SheafOfModules.{u}
      (Stacks.RingedSpace.structureRingSheaf ((BigFppfOver.toScheme B S hS).obj X').toRingedSpace)}
    (r : (pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).obj
      ((situationAlgebra (Â Z f)).piece n) ⟶ W) :
    @inv _ _ _ _ ((ρ.restrict (𝟙 X') g g₁ h₁).app n) (ρ.isIso_restrict_app _ _ _ _ n) ≫
        (ρ.restrict τ f g₁ h₂).app n ≫ r =
      eqToHom (congrArg (fun m => (pullbackFunctor (ringedSpaceHom m)).obj
          ((situationAlgebra (Â X' g)).piece n)) ((BigFppfOver.toScheme B S hS).map_id X')) ≫
        (Scheme.Modules.pullbackId _).hom.app ((situationAlgebra (Â X' g)).piece n) ≫
          (ρ.restrict τ f g hg).app n ≫ r := by
  obtain rfl : g₁ = g := h₂.symm.trans hg
  have h := congrArg (fun φ => SheafOfModules.GradedAlgebra.UnitalHom.app φ n) (ρ.restrict_id X' g₁)
  have hinv := @IsIso.inv_eq_of_hom_inv_id _ _ _ _ _ (ρ.isIso_restrict_app _ _ _ h₁ n) _ h
  refine (congrArg (fun z => z ≫ (ρ.restrict τ f g₁ h₂).app n ≫ r) hinv).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun z => z ≫ (Scheme.Modules.pullbackId _).hom.app
    ((situationAlgebra (Â X' g₁)).piece n) ≫ (ρ.restrict τ f g₁ hg).app n ≫ r)
    ((baseAlgebraCongrHom_app _ _ n).trans (pullbackCongr_hom_app_eq_eqToHom _ _))

/-- **The pullback `ψ'` of a map `ψ` given by a unital homomorphism, to the square
`X' = X' ⟶ Z` over `τ : X' ⟶ Z`, degreewise.** For `ψ` the map over `𝟙_Z` of a unital
homomorphism `Ψ : f^*𝒜 ⟶ ⨁_n ℒ^{⊗ n}` read through `(𝟙_Z)^*(f^*𝒜) = f^*𝒜`, the degree-`i`
component of `ψ'`, read over `𝟙_{X'}`, is the identification `(𝟙_{X'})^*((f ∘ τ)^*𝒜) = (f ∘ τ)^*𝒜`,
the restriction map `(f ∘ τ)^*𝒜 ⟶ τ^*(f^*𝒜)` of the datum, the pullback `τ^*Ψ` and the comparison
`τ^*(ℒ^{⊗ i}) ≅ (τ^*ℒ)^{⊗ i}` of the tensor powers. -/
theorem squareTwisting_id_twistingOfUnitalHom_app {Z X' : BigFppfOver B S hS}
    {f : yoneda.obj Z ⟶ X}
    {L : SheafOfModules.{u}
      (Stacks.RingedSpace.structureRingSheaf ((BigFppfOver.toScheme B S hS).obj Z).toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj Z).toRingedSpace.presheaf
      (isSheafStruct _) L]
    (Ψ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra (Â Z f)) (laurent L))
    (τ : X' ⟶ Z) (g : yoneda.obj X' ⟶ X) (hsq : yoneda.map (𝟙 X') ≫ g = yoneda.map τ ≫ f)
    (hg : yoneda.map τ ≫ f = g) (i : ℤ) :
    (Twisting.congrBase ((BigFppfOver.toScheme B S hS).map_id X')
      (ρ.squareTwisting hc hX (Stacks.RelativeProj.twistingOfUnitalHom
        (𝟙 ((BigFppfOver.toScheme B S hS).obj Z)) (situationAlgebra (Â Z f)) L
        ((Stacks.Conormal.gradedPullbackId (situationAlgebra (Â Z f))).comp Ψ))
        g (𝟙 X') τ hsq)).app i =
      eqToHom (congrArg (fun k : ℤ => (pullbackFunctor (ringedSpaceHom
          (𝟙 ((BigFppfOver.toScheme B S hS).obj X')))).obj ((situationAlgebra (Â X' g)).piece k))
          (mul_one i)) ≫
        (Scheme.Modules.pullbackId _).hom.app ((situationAlgebra (Â X' g)).piece i) ≫
          (ρ.restrict τ f g hg).app i ≫
            (pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
              (Ψ.app i) ≫
              laurentPullback ((BigFppfOver.toScheme B S hS).map τ) L i := by
  rw [Twisting.congrBase_app]
  unfold squareTwisting
  rw [Twisting.congrBase_app, Twisting.baseChangeUp_app]
  unfold squareTwistingAtPoint squarePullbackDown Twisting.algebraTransport Twisting.baseChangeDown
    Twisting.baseChangeDownApp
  dsimp only
  refine (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _
    (Twisting.congrBase_app _ _ i))))))).trans ?_
  refine (whisker_eq _ (whisker_eq _ (compComparison_id_comp_map_comp_map_comp_inv_assoc _ _ _ _
    _ _ _))).trans ?_
  refine (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _
    (compComparison_map_eqToHom_pullbackId_assoc ((BigFppfOver.toScheme B S hS).map τ)
      (situationAlgebra (Â Z f)).piece (mul_one i) (Ψ.app i) _)))))).trans ?_
  refine (whisker_eq _ (whisker_eq _ (inv_restrict_id_comp_restrict_assoc ρ τ f g _ _ _ hg
    (i * 1) _))).trans ?_
  refine (eqToHom_trans_assoc _ _ _).trans ?_
  refine (eqToHom_trans_assoc _ _ _).trans ?_
  refine (whisker_eq _ (whisker_eq _ (whisker_eq _ (eqToHom_trans_assoc _ _ _)))).trans ?_
  exact eqToHom_comp_comp_comp_eqToHom_comp
    (F := fun n => (pullbackFunctor (ringedSpaceHom
      (𝟙 ((BigFppfOver.toScheme B S hS).obj X')))).obj ((situationAlgebra (Â X' g)).piece n))
    (G := fun n => (situationAlgebra (Â X' g)).piece n)
    (H := fun n => (pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).obj
      ((situationAlgebra (Â Z f)).piece n))
    (fun n => (Scheme.Modules.pullbackId _).hom.app ((situationAlgebra (Â X' g)).piece n))
    (fun n => (ρ.restrict τ f g hg).app n) (mul_one i) _ _ _ _

/-- **The pullback of a map `ψ` given by a unital homomorphism is given by a unital
homomorphism**: if a unital homomorphism `Ψ' : g^*𝒜 ⟶ ⨁_n ℒ'^{⊗ n}` at the point `g = f ∘ τ` is,
degreewise, the restriction map `(f ∘ τ)^*𝒜 ⟶ τ^*(f^*𝒜)`, the pullback `τ^*Ψ`, the comparison
`τ^*(ℒ^{⊗ i}) ≅ (τ^*ℒ)^{⊗ i}` and the Laurent algebra map of `e : τ^*ℒ ≅ ℒ'`, then its map over
`𝟙_{X'}` is the pullback `ψ'` of the map of `Ψ` to the square `X' = X' ⟶ Z`, read over `𝟙_{X'}`
and transported along `e`. -/
theorem twistingOfUnitalHom_eq_squareTwisting_id {Z X' : BigFppfOver B S hS}
    {f : yoneda.obj Z ⟶ X}
    {L : SheafOfModules.{u}
      (Stacks.RingedSpace.structureRingSheaf ((BigFppfOver.toScheme B S hS).obj Z).toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj Z).toRingedSpace.presheaf
      (isSheafStruct _) L]
    (Ψ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra (Â Z f)) (laurent L))
    (τ : X' ⟶ Z) (g : yoneda.obj X' ⟶ X) (hsq : yoneda.map (𝟙 X') ≫ g = yoneda.map τ ≫ f)
    (hg : yoneda.map τ ≫ f = g)
    {L' : SheafOfModules.{u}
      (Stacks.RingedSpace.structureRingSheaf ((BigFppfOver.toScheme B S hS).obj X').toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B S hS).obj X').toRingedSpace.presheaf (isSheafStruct _) L']
    (Ψ' : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra (Â X' g)) (laurent L'))
    (e : (pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).obj L ≅ L')
    (h : ∀ i : ℤ, (ρ.restrict τ f g hg).app i ≫
      (pullbackFunctor (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map (Ψ.app i) ≫
        laurentPullback ((BigFppfOver.toScheme B S hS).map τ) L i ≫
          (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso e i).hom =
        Ψ'.app i) :
    Stacks.RelativeProj.twistingOfUnitalHom (𝟙 ((BigFppfOver.toScheme B S hS).obj X'))
        (situationAlgebra (Â X' g)) L'
        ((Stacks.Conormal.gradedPullbackId (situationAlgebra (Â X' g))).comp Ψ') =
      (Twisting.congrBase ((BigFppfOver.toScheme B S hS).map_id X')
        (ρ.squareTwisting hc hX (Stacks.RelativeProj.twistingOfUnitalHom
          (𝟙 ((BigFppfOver.toScheme B S hS).obj Z)) (situationAlgebra (Â Z f)) L
          ((Stacks.Conormal.gradedPullbackId (situationAlgebra (Â Z f))).comp Ψ))
          g (𝟙 X') τ hsq)).congrModule e := by
  refine Twisting.ext fun i => ?_
  have hG := ρ.squareTwisting_id_twistingOfUnitalHom_app hc hX Ψ τ g hsq hg i
  have k1 := congrArg (fun z => z ≫
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso e i).hom) hG
  have k2 := k1.trans (comp_assoc_six _ _ _ _ _ _)
  have k3 := k2.trans (whisker_eq _ (whisker_eq _ (h i)))
  exact k3.symm

end AlgebraicGeometry.Space.GradedAlgebraRestriction

end
