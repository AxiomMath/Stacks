module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.MonodromyEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisTrivializationExists
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.UnibranchConstantModuleFiltration

/-!
# A locally constant sheaf has finitely many pairwise orthogonal simple quotients

Let `X` be an irreducible, geometrically unibranch scheme with a geometric point `x`, `Λ` a
finite commutative ring and `N` a finite type locally constant sheaf of `Λ`-modules on
`X_étale`. Let `(F i)` be a family of finite type locally constant sheaves whose monodromy
modules are simple `Λ`-modules, pairwise orthogonal: every morphism `F i ⟶ F j` with `i ≠ j`
vanishes. If every `F i` receives a nonzero morphism from `N`, the family is finite
(`AlgebraicGeometry.finite_of_ne_zero_hom_of_orthogonal`).

## Main results

* `AlgebraicGeometry.monodromyAction_map_zero_hom`: the monodromy module functor sends the zero
  morphism to zero.
* `AlgebraicGeometry.monodromyAction_map_hom_ne_zero`: the monodromy of a nonzero morphism of
  finite type locally constant sheaves is nonzero.
* `AlgebraicGeometry.finite_of_ne_zero_hom_of_orthogonal`: a family of pairwise orthogonal finite
  type locally constant sheaves with simple monodromy, each receiving a nonzero morphism from `N`,
  is finite.
* `AlgebraicGeometry.isSimpleModule_monodromyAction_of_trivialization`,
  `AlgebraicGeometry.isSimpleModule_monodromyAction_of_inverseImage_iso`: the monodromy module of a
  finite type locally constant sheaf which is constant with simple value on one nonempty étale
  `X`-scheme is simple.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite

universe u r

namespace AlgebraicGeometry

section Zero

variable {X : Scheme.{u}} [ConnectedSpace X] {x : GeometricPoint X} {Λ : Type r} [Ring Λ]

/-- **The monodromy module functor sends the zero morphism to zero.** -/
theorem monodromyAction_map_zero_hom (F G : (X.Etale)ᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ) :
    ((monodromyAction x).map (0 : F ⟶ G)).hom = 0 := by
  apply colimit.hom_ext
  intro A
  refine (monodromyAction_map_ι (0 : F ⟶ G) A).trans ?_
  rw [NatTrans.app_zero, zero_comp]
  exact comp_zero.symm

end Zero

section Finite

variable {X : Scheme.{u}} [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)
  (x : GeometricPoint X) {Λ : Type r} [CommRing Λ]

include hX in
/-- **The monodromy of a nonzero morphism of finite type locally constant sheaves is nonzero.** -/
theorem monodromyAction_map_hom_ne_zero
    {F F' : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)}
    (hF : ftlcProperty X Λ F) (hF' : ftlcProperty X Λ F') {φ : F ⟶ F'} (hφ : φ ≠ 0) :
    ((monodromyAction x).map φ.hom).hom ≠ 0 := by
  intro h0
  obtain ⟨A, M, M', ⟨e⟩, ⟨e'⟩⟩ :=
    exists_common_galoisTrivialization (trivializedByPointedGaloisCovers hX x Λ) hF hF'
  refine hφ (GaloisTrivialization.hom_ext hX e e' (Action.hom_ext _ _ ?_))
  rw [h0]
  exact (monodromyAction_map_zero_hom F.obj F'.obj).symm

include hX in
/-- **A locally constant sheaf has finitely many pairwise orthogonal simple quotients.** Let `N`
and the `F i` be finite type locally constant sheaves of modules over a finite commutative ring
`Λ` on an irreducible, geometrically unibranch scheme, the monodromy modules of the `F i` being
simple. If every morphism `F i ⟶ F j` with `i ≠ j` vanishes and every `F i` receives a nonzero
morphism from `N`, the index type is finite. -/
theorem finite_of_ne_zero_hom_of_orthogonal [Finite Λ]
    (N : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)) (hN : ftlcProperty X Λ N)
    {ι : Type*} (F : ι → Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ))
    (hF : ∀ i, ftlcProperty X Λ (F i))
    (hsimple : ∀ i, IsSimpleModule Λ ((monodromyAction x).obj (F i).obj).V)
    (φ : ∀ i, N ⟶ F i) (hφ : ∀ i, φ i ≠ 0)
    (horth : ∀ i j, i ≠ j → ∀ g : F i ⟶ F j, g = 0) : Finite ι := by
  let V := ((monodromyAction x).obj N.obj).V
  obtain ⟨A, M, hM, ⟨e⟩⟩ := trivializedByPointedGaloisCovers hX x Λ N hN
  have := hM
  have hVfin : Module.Finite Λ V := e.finite_monodromy hX
  have : Finite V := Module.finite_of_finite Λ
  have : Finite (Submodule Λ V) :=
    Finite.of_injective (fun P : Submodule Λ V ↦ (P : Set V)) SetLike.coe_injective
  let ρ : ∀ i, V →ₗ[Λ] ((monodromyAction x).obj (F i).obj).V := fun i ↦
    ((monodromyAction x).map (φ i).hom).hom.hom
  have hρ0 : ∀ i, ρ i ≠ 0 := fun i h ↦
    monodromyAction_map_hom_ne_zero hX x hN (hF i) (hφ i) (ModuleCat.hom_ext h)
  have hρsurj : ∀ i, Function.Surjective (ρ i) := fun i ↦ by
    have := hsimple i
    rw [← LinearMap.range_eq_top]
    exact (eq_bot_or_eq_top (LinearMap.range (ρ i))).resolve_left
      (fun h ↦ hρ0 i (LinearMap.range_eq_bot.1 h))
  refine Finite.of_injective (fun i ↦ LinearMap.ker (ρ i)) fun i j hij ↦ ?_
  by_contra hne
  have hle : LinearMap.ker (ρ i) ≤ LinearMap.ker (ρ j) := le_of_eq hij
  let g : ((monodromyAction x).obj (F i).obj).V →ₗ[Λ] ((monodromyAction x).obj (F j).obj).V :=
    (LinearMap.ker (ρ i)).liftQ (ρ j) hle ∘ₗ
      ((ρ i).quotKerEquivOfSurjective (hρsurj i)).symm.toLinearMap
  have hg : ∀ v, g (ρ i v) = ρ j v := fun v ↦ by
    change (LinearMap.ker (ρ i)).liftQ (ρ j) hle
      (((ρ i).quotKerEquivOfSurjective (hρsurj i)).symm (ρ i v)) = ρ j v
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  have hcomm : ∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)) (ψ : N ⟶ G)
      (σ : EtaleFundamentalGroup X x) (v : V),
      ((monodromyAction x).map ψ.hom).hom.hom ((((monodromyAction x).obj N.obj).ρ σ).asHom.hom v) =
        (((monodromyAction x).obj G.obj).ρ σ).asHom.hom
          (((monodromyAction x).map ψ.hom).hom.hom v) :=
    fun G ψ σ v ↦ ConcreteCategory.congr_hom (((monodromyAction x).map ψ.hom).comm σ) v
  let gA : (monodromyAction x).obj (F i).obj ⟶ (monodromyAction x).obj (F j).obj :=
    { hom := ModuleCat.ofHom g
      comm := fun σ ↦ by
        ext w
        obtain ⟨v, rfl⟩ := hρsurj i w
        change g ((((monodromyAction x).obj (F i).obj).ρ σ).asHom.hom (ρ i v)) =
          (((monodromyAction x).obj (F j).obj).ρ σ).asHom.hom (g (ρ i v))
        rw [hg, ← hcomm (F i) (φ i) σ v]
        change g (ρ i _) = _
        rw [hg]
        exact hcomm (F j) (φ j) σ v }
  obtain ⟨B, Mi, Mj, ⟨ei⟩, ⟨ej⟩⟩ :=
    exists_common_galoisTrivialization (trivializedByPointedGaloisCovers hX x Λ) (hF i) (hF j)
  obtain ⟨ψ, hψ⟩ := GaloisTrivialization.exists_hom hX ei ej gA
  have hψ0 : ψ = 0 := horth i j hne ψ
  have hg0 : g = 0 := by
    have h1 : gA.hom = ((monodromyAction x).map ψ.hom).hom := by rw [hψ]
    have h2 : ψ.hom = 0 := by rw [hψ0]; rfl
    rw [h2, monodromyAction_map_zero_hom] at h1
    exact congrArg ModuleCat.Hom.hom h1
  apply hρ0 j
  ext v
  rw [← hg v, hg0]
  rfl

include hX in
/-- **A locally constant sheaf with one simple local value has simple monodromy.** If a finite type
locally constant sheaf `F` on an irreducible, geometrically unibranch scheme is constant with value
a simple module `E` on one nonempty étale `X`-scheme `U`, its monodromy module is simple. -/
theorem isSimpleModule_monodromyAction_of_trivialization
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)) (hF : ftlcProperty X Λ F)
    {U : X.Etale} [Nonempty U.left] {E : ModuleCat.{max (u + 1) r} Λ} [IsSimpleModule Λ E]
    (eU : (constantSheaf (X.smallEtaleTopology.over U) (ModuleCat.{max (u + 1) r} Λ)).obj E ≅
      (X.smallEtaleTopology.overPullback _ U).obj F) :
    IsSimpleModule Λ ((monodromyAction x).obj F.obj).V := by
  obtain ⟨A, M, -, ⟨e⟩⟩ := trivializedByPointedGaloisCovers hX x Λ F hF
  have : IrreducibleSpace ((PointedGaloisCover.toEtale x).obj A).left := A.irreducibleSpace hX
  obtain ⟨Z, hZ, ρ, ⟨c⟩⟩ := exists_irreducible_over_both hX (U := U)
    ((PointedGaloisCover.toEtale x).obj A)
  have := hZ
  let eM : M ≃ₗ[Λ] ((monodromyAction x).obj F.obj).V :=
    (e.sectionsEquiv hX).trans (e.monodromyEquiv hX)
  let eME : M ≃ₗ[Λ] E := (trivSectionEquiv e ρ).trans (trivSectionEquiv eU c).symm
  exact IsSimpleModule.congr (eM.symm.trans eME)

include hX in
/-- `AlgebraicGeometry.isSimpleModule_monodromyAction_of_trivialization`, the trivialization being
given on the inverse image to a nonempty étale `X`-scheme `W`. -/
theorem isSimpleModule_monodromyAction_of_inverseImage_iso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)) (hF : ftlcProperty X Λ F)
    (W : X.Etale) [Nonempty W.left] {E : ModuleCat.{max (u + 1) r} Λ} [IsSimpleModule Λ E]
    (eW : (Stacks.EtaleCohomology.etaleModuleInverseImage.{u, r} Λ W.hom).obj F ≅
      (constantSheaf W.left.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj E) :
    IsSimpleModule Λ ((monodromyAction x).obj F.obj).V :=
  isSimpleModule_monodromyAction_of_trivialization hX x F hF
    (Stacks.EtaleCohomology.overPullbackIsoConstantOfEtaleModuleInverseImage Λ W F E eW)

end Finite

end AlgebraicGeometry

end
