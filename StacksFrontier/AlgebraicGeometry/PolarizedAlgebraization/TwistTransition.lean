module

public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.ChartTransition
public import StacksFrontier.AlgebraicGeometry.TwistExistence.BasisUnique
public import StacksFrontier.AlgebraicGeometry.ProjTwistGradedAlgebra.Basic

/-!
# Composites of base changes of relative `Proj`, on the Serre twists

Let `𝓑` be a quasi-coherent graded algebra on a scheme `S`, and for `i = 1, 2` let `gᵢ : Tᵢ ⟶ S`
be morphisms with `ψᵢ : gᵢ^* 𝓑 ⟶ 𝒜ᵢ` isomorphisms of graded algebras, so that
`cᵢ : Proj_{Tᵢ}(𝒜ᵢ) ⟶ Proj_{Tᵢ}(gᵢ^* 𝓑) ⟶ Proj_S(𝓑)` is a base change of `Proj_S(𝓑)`
([Stacks, Tags 07ZJ, 01O3]). Let `t : T₁ ⟶ T₂` with `t ≫ g₂ = g₁` and `α : t^* 𝒜₂ ⟶ 𝒜₁` an
isomorphism, giving `M : Proj_{T₁}(𝒜₁) ⟶ Proj_{T₂}(𝒜₂)` with `M ≫ c₂ = c₁`. If `ψ₁` is `α`
after `t^* ψ₂`, then the two comparisons of Serre twists
`c₁^* (⨁ 𝒪(d)) ⟶ ⨁ 𝒪(d)` — the one of `c₁`, and the one of `c₂` pulled back along `M` followed by
the one of `M` — agree.

The proof is the rigidity of the twists of a relative `Proj` ([Stacks, Tag 01NR], in the form
`Stacks.AlgebraicGeometry.TwistExistenceBasis.eq_glueHom`): an endomorphism of the graded algebra
of twists fixing the homogeneous sections is the identity.

## Main results

* `Stacks.PolarizedAlgebraization.eq_one_of_psi`: an endomorphism of the twist algebra of a
  relative `Proj` commuting with the homogeneous-section maps is the identity.
* `Stacks.PolarizedAlgebraization.baseChangeTwistHom_eq_comp`: the composition law.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 07ZJ](https://stacks.math.columbia.edu/tag/07ZJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.ProjectiveDeformation
open Stacks.AlgebraicGeometry.Tag07ZGTwist
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap (psiU)
open Stacks.AlgebraicGeometry.SectionRingBaseChange (unitApp unitApp_naturality unitApp_map
  hom_app_map map_map_homOfLE)

universe u

namespace Stacks.PolarizedAlgebraization

section Rigidity

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- **An endomorphism of the graded algebra of twists of `Proj_S(A)` which commutes with the
homogeneous-section maps is the identity** ([Stacks, Tag 01NR], second uniqueness assertion). -/
theorem eq_one_of_psi (f : twistAlgebra A ⟶ twistAlgebra A)
    (hf : ∀ n : ℕ, (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ n ≫
      (Scheme.Modules.pushforward (relativeProj A).toBase).map (f.app (n : ℤ)) =
        (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ n) :
    f = 𝟙 _ := by
  let D : Stacks.AlgebraicGeometry.TwistExistenceBasis.BasisTwistData A
      {U : S.Opens | IsAffineOpen U} :=
    Stacks.AlgebraicGeometry.TwistExistenceBasis.BasisTwistData.ofTwistData
      (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra A)
  exact (Stacks.AlgebraicGeometry.TwistExistenceBasis.eq_glueHom (D := D) (E := D) (f := f)
    S.isBasis_affineOpens (fun _ h => h) hf).trans
    (Stacks.AlgebraicGeometry.TwistExistenceBasis.eq_glueHom (D := D) (E := D) (f := 𝟙 _)
      S.isBasis_affineOpens (fun _ h => h) fun n => by ext U x; rfl).symm

/-- `eq_one_of_psi` with the hypothesis read on sections: if maps out of each `A_n` are determined
by their values on a set of sections over an open `V n`, it suffices that the endomorphism fix the
images under `ψ` of those sections. -/
theorem eq_one_of_psi_on (f : twistAlgebra A ⟶ twistAlgebra A) (V : ℕ → S.Opens)
    (sects : ∀ n : ℕ, Set Γ(A.piece (n : ℤ), V n))
    (hdet : ∀ (n : ℕ) {F : S.Modules} (φ φ' : A.piece (n : ℤ) ⟶ F),
      (∀ s ∈ sects n, φ.app (V n) s = φ'.app (V n) s) → φ = φ')
    (hfix : ∀ (n : ℕ), ∀ s ∈ sects n,
      Scheme.Modules.Hom.app (f.app (n : ℤ)) ((relativeProj A).toBase ⁻¹ᵁ V n)
        (psiU A n (V n) s) = psiU A n (V n) s) :
    f = 𝟙 _ :=
  eq_one_of_psi A f fun n => hdet n _ _ fun s hs => hfix n s hs

end Rigidity

section Chase

variable {P₁ P₂ X : Scheme.{u}}

/-- Four restrictions of sections of a module compose to one. -/
theorem map_map_map_map_homOfLE {Z : Scheme.{u}} (N : Z.Modules) {W₀ W₁ W₂ W₃ W₄ : Z.Opens}
    (h₁ : W₀ ≤ W₁) (h₂ : W₁ ≤ W₂) (h₃ : W₂ ≤ W₃) (h₄ : W₃ ≤ W₄) (h : W₀ ≤ W₄) (x : Γ(N, W₄)) :
    N.presheaf.map (homOfLE h₁).op (N.presheaf.map (homOfLE h₂).op
        (N.presheaf.map (homOfLE h₃).op (N.presheaf.map (homOfLE h₄).op x))) =
      N.presheaf.map (homOfLE h).op x := by
  rw [map_map_homOfLE N h₃ h₄ (h₃.trans h₄), map_map_homOfLE N h₂ (h₃.trans h₄)
    (h₂.trans (h₃.trans h₄)), map_map_homOfLE N h₁ _ h]

/-- The splitting of the inverse image along `M ≫ c₂` followed by `M^* F` sends the inverse image
of a section to the inverse image along `M` of `F` applied to the inverse image along `c₂`. -/
private theorem pullbackComp_inv_map_unitApp (M : P₁ ⟶ P₂) (c₂ : P₂ ⟶ X) (G : X.Modules)
    {H₂ : P₂.Modules} (F : (Scheme.Modules.pullback c₂).obj G ⟶ H₂) (O : X.Opens) (x : Γ(G, O)) :
    ((Scheme.Modules.pullbackComp M c₂).inv.app G ≫ (Scheme.Modules.pullback M).map F).app
        ((M ≫ c₂) ⁻¹ᵁ O) (unitApp (M ≫ c₂) G O x) =
      unitApp M H₂ (c₂ ⁻¹ᵁ O) (F.app (c₂ ⁻¹ᵁ O) (unitApp c₂ G O x)) :=
  (congrArg _ (Scheme.Modules.pullbackComp_inv_unit M c₂ G O x)).trans
    (unitApp_naturality M F (c₂ ⁻¹ᵁ O) (unitApp c₂ G O x))

/-- **The composite comparison through a factorization, on the inverse image of a section.** For
`c₁ = M ≫ c₂`, transporting the inverse image along `c₁` of a section to the inverse image along
`M ≫ c₂`, splitting it into the two inverse images, applying `M^* F` and then `τ`, is applying `F`
to the inverse image along `c₂`, then `τ` to the inverse image along `M`. -/
theorem comp_app_unitApp_of_eq (M : P₁ ⟶ P₂) (c₂ : P₂ ⟶ X) (c₁ : P₁ ⟶ X) (hc : M ≫ c₂ = c₁)
    (G : X.Modules) {H₂ : P₂.Modules} {H₁ : P₁.Modules}
    (F : (Scheme.Modules.pullback c₂).obj G ⟶ H₂) (τ : (Scheme.Modules.pullback M).obj H₂ ⟶ H₁)
    (O : X.Opens) (x : Γ(G, O)) :
    ((Scheme.Modules.pullbackCongr hc.symm).hom.app G ≫
        (Scheme.Modules.pullbackComp M c₂).inv.app G ≫
        (Scheme.Modules.pullback M).map F ≫ τ).app (c₁ ⁻¹ᵁ O) (unitApp c₁ G O x) =
      H₁.presheaf.map (homOfLE (by rw [← hc]; exact le_rfl)).op
        (τ.app (M ⁻¹ᵁ (c₂ ⁻¹ᵁ O))
          (unitApp M H₂ (c₂ ⁻¹ᵁ O) (F.app (c₂ ⁻¹ᵁ O) (unitApp c₂ G O x)))) := by
  subst hc
  have e := pullbackComp_inv_map_unitApp M c₂ G F O x
  have hid : (homOfLE (show (M ≫ c₂) ⁻¹ᵁ O ≤ M ⁻¹ᵁ (c₂ ⁻¹ᵁ O) from le_rfl)).op = 𝟙 _ :=
    Subsingleton.elim _ _
  calc _ = τ.app (M ⁻¹ᵁ (c₂ ⁻¹ᵁ O)) (((Scheme.Modules.pullbackComp M c₂).inv.app G ≫
          (Scheme.Modules.pullback M).map F).app ((M ≫ c₂) ⁻¹ᵁ O) (unitApp (M ≫ c₂) G O x)) := rfl
    _ = τ.app (M ⁻¹ᵁ (c₂ ⁻¹ᵁ O))
          (unitApp M H₂ (c₂ ⁻¹ᵁ O) (F.app (c₂ ⁻¹ᵁ O) (unitApp c₂ G O x))) := by
        rw [e]
    _ = _ := by
        rw [hid]
        simp only [Scheme.Hom.comp_base, TopologicalSpace.Opens.map_comp_obj,
          CategoryTheory.Functor.map_id, AddCommGrpCat.hom_id]
        rfl

/-- The composite of the transport along `c₁ = M ≫ c₂`, the splitting of the inverse image and
`M^* F` followed by `τ`, as a homomorphism of graded algebras `c₁^* G ⟶ H₁`. -/
def gradedCompThrough (M : P₁ ⟶ P₂) (c₂ : P₂ ⟶ X) (c₁ : P₁ ⟶ X) (hc : M ≫ c₂ = c₁)
    (G : Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra X)
    {H₂ : Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra P₂}
    {H₁ : Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra P₁}
    (F : Stacks.Conormal.gradedPullback c₂ G ⟶ H₂)
    (τ : Stacks.Conormal.gradedPullback M H₂ ⟶ H₁) :
    Stacks.Conormal.gradedPullback c₁ G ⟶ H₁ :=
  (Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso G
      hc.symm).hom ≫
    (Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso G M c₂).inv ≫
    Stacks.RingedSpace.pullbackGradedAlgebraMap M.toLRSHom.toShHom F ≫ τ

/-- **`gradedCompThrough` in one degree** is the composite of modules it is built from. -/
theorem gradedCompThrough_app (M : P₁ ⟶ P₂) (c₂ : P₂ ⟶ X) (c₁ : P₁ ⟶ X) (hc : M ≫ c₂ = c₁)
    (G : Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra X)
    {H₂ : Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra P₂}
    {H₁ : Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra P₁}
    (F : Stacks.Conormal.gradedPullback c₂ G ⟶ H₂)
    (τ : Stacks.Conormal.gradedPullback M H₂ ⟶ H₁) (n : ℤ) :
    (gradedCompThrough M c₂ c₁ hc G F τ).app n =
      (Scheme.Modules.pullbackCongr hc.symm).hom.app (G.piece n) ≫
        (Scheme.Modules.pullbackComp M c₂).inv.app (G.piece n) ≫
        (Scheme.Modules.pullback M).map (F.app n) ≫ τ.app n :=
  rfl

/-- **`comp_app_unitApp_of_eq` for homomorphisms of graded algebras**: the composite of the
transport along `c₁ = M ≫ c₂`, the splitting of the inverse image, the inverse image along `M` of
`F` and then `τ`, read in one degree on the inverse image along `c₁` of a section. -/
theorem gradedComp_app_unitApp_of_eq (M : P₁ ⟶ P₂) (c₂ : P₂ ⟶ X) (c₁ : P₁ ⟶ X)
    (hc : M ≫ c₂ = c₁)
    (G : Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra X)
    {H₂ : Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra P₂}
    {H₁ : Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra P₁}
    (F : Stacks.Conormal.gradedPullback c₂ G ⟶ H₂)
    (τ : Stacks.Conormal.gradedPullback M H₂ ⟶ H₁) (n : ℤ) (O : X.Opens) (x : Γ(G.piece n, O)) :
    Scheme.Modules.Hom.app ((gradedCompThrough M c₂ c₁ hc G F τ).app n)
        (c₁ ⁻¹ᵁ O) (unitApp c₁ (G.piece n) O x) =
      (Scheme.Modules.presheaf (X := P₁) (H₁.piece n)).map (homOfLE (by rw [← hc]; exact le_rfl)).op
        (Scheme.Modules.Hom.app (τ.app n) (M ⁻¹ᵁ (c₂ ⁻¹ᵁ O))
          (unitApp M (H₂.piece n) (c₂ ⁻¹ᵁ O)
            (Scheme.Modules.Hom.app (F.app n) (c₂ ⁻¹ᵁ O) (unitApp c₂ (G.piece n) O x)))) :=
  comp_app_unitApp_of_eq M c₂ c₁ hc (G.piece n) (F.app n) (τ.app n) O x

end Chase

section Restriction

/-- A morphism of modules fixing the restriction of a section to an open with the same points
fixes the section. -/
theorem app_eq_of_app_map_eq {Z : Scheme.{u}} {N : Z.Modules} (φ : N ⟶ N) {W U : Z.Opens}
    (hWU : W ≤ U) (hUW : U ≤ W) (P : Γ(N, U))
    (h : φ.app W (N.presheaf.map (homOfLE hWU).op P) = N.presheaf.map (homOfLE hWU).op P) :
    φ.app U P = P := by
  rw [hom_app_map] at h
  have h' := congrArg (N.presheaf.map (homOfLE hUW).op) h
  rw [map_map_homOfLE N hUW hWU le_rfl, map_map_homOfLE N hUW hWU le_rfl] at h'
  have hid : (homOfLE (le_refl U)).op = 𝟙 _ := Subsingleton.elim _ _
  rw [hid, CategoryTheory.Functor.map_id] at h'
  exact h'

/-- A morphism into a direct image followed by the direct image of an endomorphism, on
sections. -/
theorem comp_pushforward_map_app {Z Y : Scheme.{u}} (p : Z ⟶ Y) {M : Y.Modules} {N : Z.Modules}
    (ψ : M ⟶ (Scheme.Modules.pushforward p).obj N) (φ : N ⟶ N) (U : Y.Opens) (x : Γ(M, U)) :
    (ψ ≫ (Scheme.Modules.pushforward p).map φ).app U x = φ.app (p ⁻¹ᵁ U) (ψ.app U x) :=
  rfl

end Restriction

section Uniqueness

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- **Two homomorphisms into the twist algebra, the first an isomorphism, agree as soon as they
agree on enough sections.** Let `F₁, F₂ : G ⟶ ⨁ 𝒪(d)` be homomorphisms of graded algebras on
`Proj_S(A)` with `F₁` an isomorphism. Suppose that maps out of each `A_n` are determined by their
values on a set of sections over `V n`, and that for each such section `s` there is a section
`y n s` of `G_n`, over an open `W n` with the same points as `π^{-1}(V n)`, which both `F₁` and
`F₂` carry to the restriction of `ψ(s)`. Then `F₁ = F₂`. -/
theorem eq_of_psi_on {G : Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra
      (relativeProj A).scheme} (F₁ F₂ : G ⟶ twistAlgebra A) (hF₁ : ∀ n : ℤ, IsIso (F₁.app n))
    (V : ℕ → S.Opens) (W : ℕ → (relativeProj A).scheme.Opens)
    (hW : ∀ n, W n ≤ (relativeProj A).toBase ⁻¹ᵁ V n)
    (hWr : ∀ n, (relativeProj A).toBase ⁻¹ᵁ V n ≤ W n)
    (ι : ℕ → Type u) (sec : ∀ n : ℕ, ι n → Γ(A.piece (n : ℤ), V n))
    (hdet : ∀ (n : ℕ) {F : S.Modules} (φ φ' : A.piece (n : ℤ) ⟶ F),
      (∀ i, φ.app (V n) (sec n i) = φ'.app (V n) (sec n i)) → φ = φ')
    (y : ∀ n : ℕ, ι n → Γ(G.piece (n : ℤ), W n))
    (h₁ : ∀ (n : ℕ) (i : ι n), Scheme.Modules.Hom.app (F₁.app (n : ℤ)) (W n) (y n i) =
      (relativeTwist A n).presheaf.map (homOfLE (hW n)).op (psiU A n (V n) (sec n i)))
    (h₂ : ∀ (n : ℕ) (i : ι n), Scheme.Modules.Hom.app (F₂.app (n : ℤ)) (W n) (y n i) =
      (relativeTwist A n).presheaf.map (homOfLE (hW n)).op (psiU A n (V n) (sec n i))) :
    F₁ = F₂ := by
  let e := SheafOfModules.GradedAlgebra.isoOfIsIsoApp F₁ hF₁
  have key : e.inv ≫ F₂ = 𝟙 _ := by
    refine eq_one_of_psi_on A _ V (fun n => Set.range (sec n))
      (fun n F φ φ' h => hdet n φ φ' fun i => h _ ⟨i, rfl⟩) ?_
    rintro n _ ⟨i, rfl⟩
    refine app_eq_of_app_map_eq (N := relativeTwist A n) ((e.inv ≫ F₂).app (n : ℤ)) (hW n)
      (hWr n) _ ?_
    have hinv : Scheme.Modules.Hom.app (e.inv.app (n : ℤ)) (W n)
        (Scheme.Modules.Hom.app (e.hom.app (n : ℤ)) (W n) (y n i)) = y n i :=
      congrArg (fun φ => Scheme.Modules.Hom.app (SheafOfModules.GradedAlgebra.Hom.app φ n) (W n)
        (y n i)) e.hom_inv_id
    refine Eq.trans ?_ (h₂ n i)
    exact congrArg (Scheme.Modules.Hom.app (F₂.app (n : ℤ)) (W n))
      ((congrArg (Scheme.Modules.Hom.app (e.inv.app (n : ℤ)) (W n)) (h₁ n i).symm).trans hinv)
  have := (Iso.inv_comp_eq e).mp key
  rw [Category.comp_id] at this
  exact SheafOfModules.GradedAlgebra.Hom.ext fun n =>
    congrArg (fun φ => SheafOfModules.GradedAlgebra.Hom.app φ n) this.symm

end Uniqueness

section Composite

variable {S T₁ T₂ : Scheme.{u}} {𝓑 : SheafGradedAlgebra S}
  {A₁ : SheafGradedAlgebra T₁} {A₂ : SheafGradedAlgebra T₂}
  {g₁ : T₁ ⟶ S} {g₂ : T₂ ⟶ S} {t : T₁ ⟶ T₂}

/-- The base change morphism `Proj_{T}(𝒜) ⟶ Proj_{T}(g^* 𝓑) ⟶ Proj_S(𝓑)` of an isomorphism
`ψ : g^* 𝓑 ⟶ 𝒜` of graded algebras ([Stacks, Tags 07ZJ, 01O3]). -/
abbrev baseChangeMor {S T : Scheme.{u}} {𝓑 : SheafGradedAlgebra S} {A : SheafGradedAlgebra T}
    {g : T ⟶ S} (ψ : SheafGradedAlgebraHom (𝓑.pullback g) A) (hψ : ∀ n : ℤ, IsIso (ψ.app n)) :
    (relativeProj A).scheme ⟶ (relativeProj 𝓑).scheme :=
  projMapOfEventuallyIso ψ (Filter.Eventually.of_forall fun d => hψ d) ≫
    Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom 𝓑 g

/-- The comparison of Serre twists along `baseChangeMor`. -/
abbrev baseChangeTwist {S T : Scheme.{u}} {𝓑 : SheafGradedAlgebra S} {A : SheafGradedAlgebra T}
    {g : T ⟶ S} (ψ : SheafGradedAlgebraHom (𝓑.pullback g) A) (hψ : ∀ n : ℤ, IsIso (ψ.app n)) :
    Stacks.Conormal.gradedPullback (baseChangeMor ψ hψ) (twistAlgebra 𝓑) ⟶ twistAlgebra A :=
  baseChangeTwistHom ψ (Filter.Eventually.of_forall fun d => hψ d)

/-- The components of an isomorphism of sheaves of graded algebras are isomorphisms. -/
theorem isIso_app_of_iso {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {A B : SheafOfModules.GradedAlgebra.{u, u} R} (e : A ≅ B)
    (n : ℤ) : IsIso (e.hom.app n) :=
  ⟨e.inv.app n, congrArg (fun φ => SheafOfModules.GradedAlgebra.Hom.app φ n) e.hom_inv_id,
    congrArg (fun φ => SheafOfModules.GradedAlgebra.Hom.app φ n) e.inv_hom_id⟩

/-- **The comparison of Serre twists along `baseChangeMor` is an isomorphism in every degree.** -/
theorem isIso_baseChangeTwist_app {S T : Scheme.{u}} {𝓑 : SheafGradedAlgebra S}
    {A : SheafGradedAlgebra T} {g : T ⟶ S} (ψ : SheafGradedAlgebraHom (𝓑.pullback g) A)
    (hψ : ∀ n : ℤ, IsIso (ψ.app n)) (n : ℤ) : IsIso ((baseChangeTwist ψ hψ).app n) := by
  have hev : ∀ᶠ d : ℕ in Filter.atTop, IsIso (ψ.app (d : ℤ)) :=
    Filter.Eventually.of_forall fun d => hψ d
  have hθ := isIso_relativeTwistMap_of_eventually_isIso ψ hev n
  have ha : IsIso ((Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso
      (twistAlgebra 𝓑) (projMapOfEventuallyIso ψ hev)
      (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom 𝓑 g)).inv.app n) :=
    isIso_app_of_iso
      (Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso
        (twistAlgebra 𝓑) (projMapOfEventuallyIso ψ hev)
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom 𝓑 g)).symm n
  have hb : IsIso ((Stacks.RingedSpace.pullbackGradedAlgebraMap
      (projMapOfEventuallyIso ψ hev).toLRSHom.toShHom
      (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pulledTwistIso 𝓑 g).hom).app n) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _
      (isIso_app_of_iso (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pulledTwistIso 𝓑 g) n)
  have hc : IsIso ((projTwistHom ψ hev).app n) := by
    unfold projTwistHom
    rw [projTwistHomOf_app]
    refine @IsIso.comp_isIso' _ _ _ _ _ _ _
      (inferInstanceAs (IsIso ((Scheme.Modules.pullbackComp _ _).app _).inv)) ?_
    refine @IsIso.comp_isIso' _ _ _ _ _ _ _ (Functor.map_isIso _ _) ?_
    refine @IsIso.comp_isIso' _ _ _ _ _ _ _
      (inferInstanceAs (IsIso ((Scheme.Modules.pullbackComp _ _).app _).hom)) ?_
    refine @IsIso.comp_isIso' _ _ _ _ _ _ _
      (inferInstanceAs (IsIso ((Scheme.Modules.pullbackCongr _).app _).hom)) ?_
    exact inferInstanceAs (IsIso ((Scheme.Modules.pullbackId _).app _).hom)
  exact @IsIso.comp_isIso' _ _ _ _ _ _ _ ha (@IsIso.comp_isIso' _ _ _ _ _ _ _ hb hc)

variable (ψ₁ : SheafGradedAlgebraHom (𝓑.pullback g₁) A₁)
  (ψ₂ : SheafGradedAlgebraHom (𝓑.pullback g₂) A₂) (α : SheafGradedAlgebraHom (A₂.pullback t) A₁)
  (hψ₁ : ∀ n : ℤ, IsIso (ψ₁.app n)) (hψ₂ : ∀ n : ℤ, IsIso (ψ₂.app n))
  (hα : ∀ n : ℤ, IsIso (α.app n))
  (hc : baseChangeMor α hα ≫ baseChangeMor ψ₂ hψ₂ = baseChangeMor ψ₁ hψ₁)

/-- **The comparison of degree-one twists along `baseChangeMor`**, at the spelling of inverse
images of modules. -/
def twistComparisonOne {S T : Scheme.{u}} {𝓑 : SheafGradedAlgebra S} {A : SheafGradedAlgebra T}
    {g : T ⟶ S} (ψ : SheafGradedAlgebraHom (𝓑.pullback g) A) (hψ : ∀ n : ℤ, IsIso (ψ.app n)) :
    (Scheme.Modules.pullback (baseChangeMor ψ hψ)).obj (relativeTwist 𝓑 1) ⟶ relativeTwist A 1 :=
  (baseChangeTwist ψ hψ).app 1

/-- The comparison of degree-one twists along `baseChangeMor` is an isomorphism. -/
theorem isIso_twistComparisonOne {S T : Scheme.{u}} {𝓑 : SheafGradedAlgebra S}
    {A : SheafGradedAlgebra T} {g : T ⟶ S} (ψ : SheafGradedAlgebraHom (𝓑.pullback g) A)
    (hψ : ∀ n : ℤ, IsIso (ψ.app n)) : IsIso (twistComparisonOne ψ hψ) :=
  isIso_baseChangeTwist_app ψ hψ 1

/-- **`ψ₁` is `α` after `t^* ψ₂`**, degreewise on the pieces of `𝓑`, through `g₁ = g₂ ∘ t`. Named
so that a concrete instance is stated, and checked, at the spelling of the pieces used here. -/
def IsCompatTriple (hg : t ≫ g₂ = g₁) : Prop :=
  ∀ k : ℤ, (Scheme.Modules.pullbackCongr hg).hom.app (𝓑.piece k) ≫ ψ₁.app k =
    (Scheme.Modules.pullbackComp t g₂).inv.app (𝓑.piece k) ≫
      (Scheme.Modules.pullback t).map (ψ₂.app k) ≫ α.app k

/-- The comparison of Serre twists along `c₁ = M ≫ c₂`, through `M`: the one of `c₂` pulled back
along `M`, followed by the one of `M`. -/
def compositeTwist :
    Stacks.Conormal.gradedPullback (baseChangeMor ψ₁ hψ₁) (twistAlgebra 𝓑) ⟶ twistAlgebra A₁ :=
  gradedCompThrough (baseChangeMor α hα) (baseChangeMor ψ₂ hψ₂) (baseChangeMor ψ₁ hψ₁) hc
    (twistAlgebra 𝓑) (baseChangeTwist ψ₂ hψ₂) (baseChangeTwist α hα)

/-- **`compositeTwist` in one degree**: the comparison along `c₂` pulled back along `M`, after the
splitting of the inverse image, followed by the comparison along `M`. -/
theorem compositeTwist_app (n : ℤ) :
    (compositeTwist ψ₁ ψ₂ α hψ₁ hψ₂ hα hc).app n =
      (Scheme.Modules.pullbackCongr hc.symm).hom.app ((twistAlgebra 𝓑).piece n) ≫
        (Scheme.Modules.pullbackComp (baseChangeMor α hα) (baseChangeMor ψ₂ hψ₂)).inv.app
          ((twistAlgebra 𝓑).piece n) ≫
        (Scheme.Modules.pullback (baseChangeMor α hα)).map ((baseChangeTwist ψ₂ hψ₂).app n) ≫
        (baseChangeTwist α hα).app n :=
  gradedCompThrough_app _ _ _ hc _ _ _ n

/-- **`compositeTwist` on the homogeneous sections**: it carries the inverse image of `ψ_𝓑(a)` to
the restriction of `ψ_{𝒜₁}(ψ₁(g₁^* a))`, provided `ψ₁` is `α` after `t^* ψ₂`. -/
theorem compositeTwist_app_unitApp_psiU (hg : t ≫ g₂ = g₁)
    (hcompat : IsCompatTriple ψ₁ ψ₂ α hg)
    (d : ℕ) (V : S.Opens) (a : Γ(𝓑.piece (d : ℤ), V)) :
    Scheme.Modules.Hom.app ((compositeTwist ψ₁ ψ₂ α hψ₁ hψ₂ hα hc).app (d : ℤ))
        (baseChangeMor ψ₁ hψ₁ ⁻¹ᵁ ((relativeProj 𝓑).toBase ⁻¹ᵁ V))
        (unitApp (baseChangeMor ψ₁ hψ₁) ((twistAlgebra 𝓑).piece (d : ℤ))
          ((relativeProj 𝓑).toBase ⁻¹ᵁ V) (psiU 𝓑 d V a)) =
      (relativeTwist A₁ d).presheaf.map
        (homOfLE (baseChangeTwist_preimage_le ψ₁ (Filter.Eventually.of_forall fun d => hψ₁ d) V)).op
        (psiU A₁ d (g₁ ⁻¹ᵁ V) ((ψ₁.app (d : ℤ)).app (g₁ ⁻¹ᵁ V)
          (unitApp g₁ (𝓑.piece (d : ℤ)) V a))) := by
  have hev₁ : ∀ᶠ d : ℕ in Filter.atTop, IsIso (ψ₁.app (d : ℤ)) :=
    Filter.Eventually.of_forall fun d => hψ₁ d
  have hev₂ : ∀ᶠ d : ℕ in Filter.atTop, IsIso (ψ₂.app (d : ℤ)) :=
    Filter.Eventually.of_forall fun d => hψ₂ d
  have hevα : ∀ᶠ d : ℕ in Filter.atTop, IsIso (α.app (d : ℤ)) :=
    Filter.Eventually.of_forall fun d => hα d
  -- the factorization through `M`
  have s0 := gradedComp_app_unitApp_of_eq (baseChangeMor α hα) (baseChangeMor ψ₂ hψ₂)
    (baseChangeMor ψ₁ hψ₁) hc (twistAlgebra 𝓑) (baseChangeTwist ψ₂ hψ₂)
    (baseChangeTwist α hα) (d : ℤ) ((relativeProj 𝓑).toBase ⁻¹ᵁ V) (psiU 𝓑 d V a)
  -- the comparison of `c₂` on the section
  have sD := baseChangeTwistHom_app_unitApp_psiU ψ₂ hev₂ d V a
  -- the comparison of `M` on the section
  have sG : Scheme.Modules.Hom.app ((baseChangeTwist α hα).app (d : ℤ))
      (baseChangeMor α hα ⁻¹ᵁ ((relativeProj A₂).toBase ⁻¹ᵁ (g₂ ⁻¹ᵁ V)))
      (unitApp (baseChangeMor α hα) (relativeTwist A₂ d) ((relativeProj A₂).toBase ⁻¹ᵁ (g₂ ⁻¹ᵁ V))
        (psiU A₂ d (g₂ ⁻¹ᵁ V) ((ψ₂.app (d : ℤ)).app (g₂ ⁻¹ᵁ V)
          (unitApp g₂ (𝓑.piece (d : ℤ)) V a)))) = _ :=
    baseChangeTwistHom_app_unitApp_psiU α _ d (g₂ ⁻¹ᵁ V)
      ((ψ₂.app (d : ℤ)).app (g₂ ⁻¹ᵁ V) (unitApp g₂ (𝓑.piece (d : ℤ)) V a))
  -- `ψ₁` is `α` after `t^* ψ₂`, on the section
  have sH0 := congrArg (fun φ => Scheme.Modules.Hom.app φ ((t ≫ g₂) ⁻¹ᵁ V)
    (unitApp (t ≫ g₂) (𝓑.piece (d : ℤ)) V a)) (hcompat (d : ℤ))
  have hH : t ⁻¹ᵁ (g₂ ⁻¹ᵁ V) ≤ g₁ ⁻¹ᵁ V := by rw [← hg]; exact le_rfl
  have sH : (α.app (d : ℤ)).app (t ⁻¹ᵁ (g₂ ⁻¹ᵁ V)) (unitApp t (A₂.piece (d : ℤ)) (g₂ ⁻¹ᵁ V)
      ((ψ₂.app (d : ℤ)).app (g₂ ⁻¹ᵁ V) (unitApp g₂ (𝓑.piece (d : ℤ)) V a))) =
      (A₁.piece (d : ℤ)).presheaf.map (homOfLE hH).op
        ((ψ₁.app (d : ℤ)).app (g₁ ⁻¹ᵁ V) (unitApp g₁ (𝓑.piece (d : ℤ)) V a)) := by
    have l1 := Stacks.AlgebraicGeometry.TwistMulLeg.pullbackCongr_hom_app_unitApp hg
      (𝓑.piece (d : ℤ)) V a
    have l2 := pullbackComp_inv_map_unitApp t g₂ (𝓑.piece (d : ℤ)) (ψ₂.app (d : ℤ)) V a
    change (ψ₁.app (d : ℤ)).app ((t ≫ g₂) ⁻¹ᵁ V)
        (((Scheme.Modules.pullbackCongr hg).hom.app (𝓑.piece (d : ℤ))).app ((t ≫ g₂) ⁻¹ᵁ V)
          (unitApp (t ≫ g₂) (𝓑.piece (d : ℤ)) V a)) =
      (α.app (d : ℤ)).app ((t ≫ g₂) ⁻¹ᵁ V)
        (((Scheme.Modules.pullbackComp t g₂).inv.app (𝓑.piece (d : ℤ)) ≫
          (Scheme.Modules.pullback t).map (ψ₂.app (d : ℤ))).app ((t ≫ g₂) ⁻¹ᵁ V)
          (unitApp (t ≫ g₂) (𝓑.piece (d : ℤ)) V a)) at sH0
    rw [l1, l2] at sH0
    exact sH0.symm.trans (hom_app_map (ψ₁.app (d : ℤ)) hH (unitApp g₁ (𝓑.piece (d : ℤ)) V a))
  unfold compositeTwist
  refine s0.trans ?_
  rw [sD]
  have hD : baseChangeMor ψ₂ hψ₂ ⁻¹ᵁ ((relativeProj 𝓑).toBase ⁻¹ᵁ V) ≤
      (relativeProj A₂).toBase ⁻¹ᵁ (g₂ ⁻¹ᵁ V) := baseChangeTwist_preimage_le ψ₂ hev₂ V
  have eE := unitApp_map (baseChangeMor α hα) (relativeTwist A₂ d) hD
    (psiU A₂ d (g₂ ⁻¹ᵁ V) ((ψ₂.app (d : ℤ)).app (g₂ ⁻¹ᵁ V) (unitApp g₂ (𝓑.piece (d : ℤ)) V a)))
  dsimp only [relativeTwist, twistAlgebra] at eE ⊢
  rw [eE]
  have eF := hom_app_map ((baseChangeTwist α hα).app (d : ℤ))
    ((baseChangeMor α hα).preimage_mono hD)
    (unitApp (baseChangeMor α hα) (relativeTwist A₂ d)
      ((relativeProj A₂).toBase ⁻¹ᵁ (g₂ ⁻¹ᵁ V))
      (psiU A₂ d (g₂ ⁻¹ᵁ V) ((ψ₂.app (d : ℤ)).app (g₂ ⁻¹ᵁ V) (unitApp g₂ (𝓑.piece (d : ℤ)) V a))))
  refine (congrArg _ eF).trans ?_
  refine (congrArg _ (congrArg _ sG)).trans ?_
  rw [sH]
  have eI := hom_app_map
    ((Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra A₁).ψ d) hH
    ((ψ₁.app (d : ℤ)).app (g₁ ⁻¹ᵁ V) (unitApp g₁ (𝓑.piece (d : ℤ)) V a))
  refine (congrArg _ (congrArg _ (congrArg _ eI))).trans ?_
  exact map_map_map_map_homOfLE (relativeTwist A₁ d) _ _ _
    ((relativeProj A₁).toBase.preimage_mono hH) _ _

include hc in
/-- **The composition law of the comparisons of Serre twists of base changes of relative
`Proj`.** If `ψ₁` is `α` after `t^* ψ₂`, and maps out of `g₁^* 𝓑_n` are determined by the
inverse images of global sections, then the comparison of twists of `c₁ = M ≫ c₂` is the
comparison of `c₂` pulled back along `M`, followed by that of `M`. -/
theorem baseChangeTwist_eq_compositeTwist (hg : t ≫ g₂ = g₁)
    (hcompat : IsCompatTriple ψ₁ ψ₂ α hg)
    (hext : ∀ (n : ℕ) {F : T₁.Modules}
      (φ φ' : (Scheme.Modules.pullback g₁).obj (𝓑.piece (n : ℤ)) ⟶ F),
      (∀ b : Γ(𝓑.piece (n : ℤ), ⊤),
        φ.app (g₁ ⁻¹ᵁ ⊤) (unitApp g₁ (𝓑.piece (n : ℤ)) ⊤ b) =
        φ'.app (g₁ ⁻¹ᵁ ⊤) (unitApp g₁ (𝓑.piece (n : ℤ)) ⊤ b)) → φ = φ') :
    baseChangeTwist ψ₁ hψ₁ = compositeTwist ψ₁ ψ₂ α hψ₁ hψ₂ hα hc := by
  have hev₁ : ∀ᶠ d : ℕ in Filter.atTop, IsIso (ψ₁.app (d : ℤ)) :=
    Filter.Eventually.of_forall fun d => hψ₁ d
  have hext' : ∀ (n : ℕ) {F : T₁.Modules} (φ φ' : A₁.piece (n : ℤ) ⟶ F),
      (∀ b : Γ(𝓑.piece (n : ℤ), ⊤),
        φ.app (g₁ ⁻¹ᵁ ⊤) ((ψ₁.app (n : ℤ)).app (g₁ ⁻¹ᵁ ⊤) (unitApp g₁ (𝓑.piece (n : ℤ)) ⊤ b)) =
        φ'.app (g₁ ⁻¹ᵁ ⊤) ((ψ₁.app (n : ℤ)).app (g₁ ⁻¹ᵁ ⊤)
          (unitApp g₁ (𝓑.piece (n : ℤ)) ⊤ b))) → φ = φ' := by
    intro n F φ φ' h
    have : IsIso (ψ₁.app (n : ℤ)) := hψ₁ n
    rw [← cancel_epi (ψ₁.app (n : ℤ))]
    exact hext n _ _ h
  refine eq_of_psi_on A₁ _ _ (isIso_baseChangeTwist_app ψ₁ hψ₁) (fun _ => g₁ ⁻¹ᵁ ⊤)
    (fun _ => baseChangeMor ψ₁ hψ₁ ⁻¹ᵁ ((relativeProj 𝓑).toBase ⁻¹ᵁ ⊤))
    (fun _ => baseChangeTwist_preimage_le ψ₁ hev₁ ⊤) (fun _ _ _ => trivial)
    (fun n => Γ(𝓑.piece (n : ℤ), ⊤))
    (fun n b => (ψ₁.app (n : ℤ)).app (g₁ ⁻¹ᵁ ⊤) (unitApp g₁ (𝓑.piece (n : ℤ)) ⊤ b))
    (fun n F φ φ' h => hext' n φ φ' h)
    (fun n b => unitApp (baseChangeMor ψ₁ hψ₁) ((twistAlgebra 𝓑).piece (n : ℤ))
        ((relativeProj 𝓑).toBase ⁻¹ᵁ ⊤) (psiU 𝓑 n ⊤ b))
    (fun n b => baseChangeTwistHom_app_unitApp_psiU ψ₁ hev₁ n ⊤ b)
    (fun n b => compositeTwist_app_unitApp_psiU ψ₁ ψ₂ α hψ₁ hψ₂ hα hc hg hcompat n ⊤ b)

/-- **The comparison of degree-one twists along `c₁ = M ≫ c₂`** is the one along `c₂` pulled back
along `M`, followed by the one along `M`. -/
theorem twistComparisonOne_eq (hg : t ≫ g₂ = g₁) (hcompat : IsCompatTriple ψ₁ ψ₂ α hg)
    (hext : ∀ (n : ℕ) {F : T₁.Modules}
      (φ φ' : (Scheme.Modules.pullback g₁).obj (𝓑.piece (n : ℤ)) ⟶ F),
      (∀ b : Γ(𝓑.piece (n : ℤ), ⊤),
        φ.app (g₁ ⁻¹ᵁ ⊤) (unitApp g₁ (𝓑.piece (n : ℤ)) ⊤ b) =
        φ'.app (g₁ ⁻¹ᵁ ⊤) (unitApp g₁ (𝓑.piece (n : ℤ)) ⊤ b)) → φ = φ') :
    twistComparisonOne ψ₁ hψ₁ =
      (Scheme.Modules.pullbackCongr hc.symm).hom.app ((twistAlgebra 𝓑).piece 1) ≫
        (Scheme.Modules.pullbackComp (baseChangeMor α hα) (baseChangeMor ψ₂ hψ₂)).inv.app
          ((twistAlgebra 𝓑).piece 1) ≫
        (Scheme.Modules.pullback (baseChangeMor α hα)).map (twistComparisonOne ψ₂ hψ₂) ≫
        twistComparisonOne α hα :=
  (congrArg (fun F => F.app 1)
    (baseChangeTwist_eq_compositeTwist ψ₁ ψ₂ α hψ₁ hψ₂ hα hc hg hcompat hext)).trans
    (compositeTwist_app ψ₁ ψ₂ α hψ₁ hψ₂ hα hc 1)

/-- `twistComparisonOne_eq` for any spelling `(M, μ)` of the transition and its comparison of
twists, so that a concrete instance is checked by unfolding definitions only. -/
theorem twistComparisonOne_eq_of
    (M : (relativeProj A₁).scheme ⟶ (relativeProj A₂).scheme)
    (μ : (Scheme.Modules.pullback M).obj (relativeTwist A₂ 1) ⟶ relativeTwist A₁ 1)
    (hMμ : (⟨M, μ⟩ : Σ M' : (relativeProj A₁).scheme ⟶ (relativeProj A₂).scheme,
        (Scheme.Modules.pullback M').obj (relativeTwist A₂ 1) ⟶ relativeTwist A₁ 1) =
      ⟨baseChangeMor α hα, twistComparisonOne α hα⟩)
    (hc' : M ≫ baseChangeMor ψ₂ hψ₂ = baseChangeMor ψ₁ hψ₁)
    (hg : t ≫ g₂ = g₁) (hcompat : IsCompatTriple ψ₁ ψ₂ α hg)
    (hext : ∀ (n : ℕ) {F : T₁.Modules}
      (φ φ' : (Scheme.Modules.pullback g₁).obj (𝓑.piece (n : ℤ)) ⟶ F),
      (∀ b : Γ(𝓑.piece (n : ℤ), ⊤),
        φ.app (g₁ ⁻¹ᵁ ⊤) (unitApp g₁ (𝓑.piece (n : ℤ)) ⊤ b) =
        φ'.app (g₁ ⁻¹ᵁ ⊤) (unitApp g₁ (𝓑.piece (n : ℤ)) ⊤ b)) → φ = φ') :
    twistComparisonOne ψ₁ hψ₁ =
      (Scheme.Modules.pullbackCongr hc'.symm).hom.app ((twistAlgebra 𝓑).piece 1) ≫
        (Scheme.Modules.pullbackComp M (baseChangeMor ψ₂ hψ₂)).inv.app
          ((twistAlgebra 𝓑).piece 1) ≫
        (Scheme.Modules.pullback M).map (twistComparisonOne ψ₂ hψ₂) ≫ μ := by
  obtain ⟨rfl, h⟩ := Sigma.mk.inj hMμ
  obtain rfl := eq_of_heq h
  exact twistComparisonOne_eq ψ₁ ψ₂ α hψ₁ hψ₂ hα hc' hg hcompat hext

end Composite

end Stacks.PolarizedAlgebraization

end
