module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsConormalMapScaling
public import StacksFrontier.Deformation.Examples.Geometric.SpacesFiniteDimensionalResidueFieldAction

/-!
# Pushing an infinitesimal automorphism along `ε ↦ c ε` multiplies its map by `c`

Let `X'` be the total space of the pushforward `xε` of a point of the deformation category of an
algebraic space `X` over `k` to an object `Aε` of `𝒞_Λ` with a dual-number coordinate, `G ⊆ X'`
its special fibre and `π : X' ⟶ X` the retraction.  A fibre automorphism `a` of `xε` corresponds to
the map `θ_a : e₀^*Ω_{X/k} ⟶ 𝒞_{G/X'}` with `θ_a · π = a ≫ π`
(`Deformation.Examples.spaceAutToHom`, [Stacks Project, Tag 061D]).  Let `s : Aε ⟶ Aε` multiply the
maximal ideal by an element `c'` of residue `c`, and let `j : xε ⟶ xε` lie over `s` and fix the
pushforward `i : x₀ ⟶ xε`.  The pushforward `b` of `a` along `j` satisfies `J ≫ A = B ≫ J` on total
spaces, where `J` is the space component of `j`, and `J ≫ π = π`; so

`B ≫ π = J ≫ A ≫ π = J ≫ (θ_a · π) = (θ_a ≫ c·) · π`,

the last step by the precomposition law of the action ([Stacks Project, Tag 0CK6],
`AlgebraicGeometry.Space.comp_derivationMove`) and the computation of the conormal map of `J` as
multiplication by `c` (`Deformation.Examples.conormalMap_spaceSpecialSubspace_eq_comp_globalSmul`).
Hence `θ_b = θ_a ≫ c·`.

## Main results

* `AlgebraicGeometry.Space.comp_derivationMove_top_of_conormalMap_eq`: precomposition with a
  self-map fixing `Z` whose conormal map is that of the identity followed by an endomorphism `μ`
  of the conormal module turns `θ · c` into `(θ ≫ μ) · (a ≫ c)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Space Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

universe u


namespace AlgebraicGeometry.Space

attribute [local irreducible] modulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X W T : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (hZ : IsFirstOrderThickening B S hS X Z.1) (q : W ⟶ T)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨(topSubspace B S hS W).1.toFunctor, (topSubspace B S hS W).2.1⟩ : AlgebraicSpaces B S hS))
  (c : X ⟶ W)
  (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W (topSubspace B S hS W))

/-- **Precomposition with a self-map of `X` fixing `Z`, with a twisted conormal map, on the
action.**  If `a : X ⟶ X` restricts to the identity of `Z` and its conormal map is the conormal map
of the identity after `𝟙^*μ` for an endomorphism `μ` of `𝒞_{Z/X}`, then
`a ≫ (θ · c) = (θ ≫ μ) · (a ≫ c)`.  At `μ = 𝟙` this is
`AlgebraicGeometry.Space.comp_derivationMove_top`. -/
theorem comp_derivationMove_top_of_conormalMap_eq (a : X ⟶ X)
    (ha : subspaceInclusion B S hS X Z ≫ a = 𝟙 _ ≫ subspaceInclusion B S hS X Z)
    (hid : subspaceInclusion B S hS X Z ≫ 𝟙 X = 𝟙 _ ≫ subspaceInclusion B S hS X Z)
    (μ : conormalModule B S hS X Z ⟶ conormalModule B S hS X Z)
    (hcm : conormalMap B S hS Z Z a (𝟙 _) ha =
      (modulePullback B S hS (𝟙 _)).map μ ≫ conormalMap B S hS Z Z (𝟙 X) (𝟙 _) hid)
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W (topSubspace B S hS W) ≫ q)) ⟶
      conormalModule B S hS X Z)
    (hac : subspaceInclusion B S hS X Z ≫ a ≫ c =
      e₀ ≫ subspaceInclusion B S hS W (topSubspace B S hS W)) :
    a ≫ derivationMove B S hS Z (topSubspace B S hS W) e₀ q hZ c hc θ (c ≫ q) rfl =
      derivationMove B S hS Z (topSubspace B S hS W) e₀ q hZ (a ≫ c) hac (θ ≫ μ)
        ((a ≫ c) ≫ q) rfl := by
  have hW := isFirstOrderThickening_topSubspace B S hS W
  have h1 := comp_derivationMove B S hS Z Z (topSubspace B S hS W) a (𝟙 _) e₀ ha q hZ hZ hW
    c hc θ (c ≫ q) rfl
  have h4 := comp_derivationMove B S hS Z Z (topSubspace B S hS W) (𝟙 X) (𝟙 _) e₀ hid q hZ hZ
    hW (a ≫ c) hac (θ ≫ μ) ((a ≫ c) ≫ q) rfl
  refine h1.trans (Eq.trans ?_ (h4.symm.trans (Category.id_comp _)))
  apply derivationMove_congr_of_eq
  · rw [hcm, Functor.map_comp, Category.assoc]
    rfl
  · exact (Category.id_comp (a ≫ c)).symm
  · rw [Category.id_comp, Category.assoc]

end AlgebraicGeometry.Space

namespace Deformation.Examples

attribute [local irreducible] modulePullback

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

variable {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
  {x₀ : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
    (residueFieldObject.{u, u, u} Λ k)}
  {xε : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber Aε}
  {g : residueFieldObject.{u, u, u} Λ k ⟶ Aε} {e : Aε ⟶ residueFieldObject.{u, u, u} Λ k}
  (hpair : IsCanonicalDualNumberPair g e)
  (i : x₀.1 ⟶ xε.1)

/-- The space component of a self-arrow of `xε`, as a self-map of the total space. -/
abbrev spaceSelfArrowMap (j : xε.1 ⟶ xε.1) :
    spaceTotalSpace B hΛ hSpec xε.1.left ⟶ spaceTotalSpace B hΛ hSpec xε.1.left :=
  ObjectProperty.homMk j.left.map

/-- A self-arrow of `xε` fixing `i` does not change the retraction `π`. -/
theorem spaceSelfArrowMap_comp_spaceRetraction (j : xε.1 ⟶ xε.1) (hj0 : i ≫ j = i) :
    spaceSelfArrowMap B hΛ hSpec X hX toK j ≫ spaceRetraction B hΛ hSpec X hX toK i =
      spaceRetraction B hΛ hSpec X hX toK i := by
  apply ObjectProperty.hom_ext
  show j.left.map ≫ i.left.map ≫ _ = i.left.map ≫ _
  rw [← Category.assoc]
  exact congrArg (· ≫ _) (congrArg (fun m : x₀.1 ⟶ xε.1 => m.left.map) hj0)

/-- A self-arrow of `xε` lies over the morphism of spectra of its base component. -/
theorem spaceSelfArrowMap_comp_spaceTotalToBase (j : xε.1 ⟶ xε.1) :
    spaceSelfArrowMap B hΛ hSpec X hX toK j ≫ spaceTotalToBase B hΛ hSpec xε.1.left =
      spaceTotalToBase B hΛ hSpec xε.1.left ≫
        schemeSpaceMap (spaceBaseOverMap B hΛ hSpec j.left.base) :=
  ObjectProperty.hom_ext _ j.left.cartesian.w

/-- **Pushing a fibre automorphism forward along a self-arrow, on total spaces**:
`J ≫ a = a_* ≫ J`. -/
theorem spaceSelfArrowMap_comp_spaceAutHom
    (hp : IsCofiberedInGroupoids (spaceDeformationProjection B hΛ hSpec X hX toK))
    (s : Aε ⟶ Aε) (j : xε.1 ⟶ xε.1)
    (hj : (spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift s j) (a : Aut xε) :
    spaceSelfArrowMap B hΛ hSpec X hX toK j ≫ spaceAutHom B hΛ hSpec X hX toK a =
      spaceAutHom B hΛ hSpec X hX toK (pushforwardAutomorphism hp s j hj a) ≫
        spaceSelfArrowMap B hΛ hSpec X hX toK j :=
  ObjectProperty.hom_ext _
    (congrArg (fun m : xε.1 ⟶ xε.1 => m.left.map)
      (hom_comp_eq_comp_pushforwardEndomorphism hp s j hj a))

/-- **Pushing a fibre automorphism forward along a self-arrow over a rescaling multiplies its map
by the scalar.**  Let `j : xε ⟶ xε` lie over `s` and fix `i`, and let the base component of `j`
multiply the kernel of the residue map by `c'`.  Then the map `θ` of the pushforward of a fibre
automorphism `a` along `j` is the map of `a` followed by multiplication by `c'` on `𝒞_{G/X'}`. -/
theorem spaceAutToHom_pushforwardAutomorphism
    (hp : IsCofiberedInGroupoids (spaceDeformationProjection B hΛ hSpec X hX toK))
    (s : Aε ⟶ Aε) (j : xε.1 ⟶ xε.1)
    (hj : (spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift s j) (hj0 : i ≫ j = i)
    (c' : xε.1.left.base)
    (hσ : ∀ x ∈ RingHom.ker xε.1.hom.base.hom.toRingHom, j.left.base.hom x = c' * x)
    (a : Aut xε) :
    spaceAutToHom B hΛ hSpec X hX toK hpair i (pushforwardAutomorphism hp s j hj a) =
      spaceAutToHom B hΛ hSpec X hX toK hpair i a ≫
        familySpecialConormalSmul B hΛ hSpec xε.1.left xε.1.hom.base c' := by
  obtain ⟨hk, hann⟩ := (exists_epsilon_spacePoint B hΛ hSpec X hX toK hpair (xε := xε)).choose_spec
  have hG := isFirstOrderThickening_spacePointSpecial B hΛ hSpec X hX toK (xε := xε) hpair
  have hσε := hσ _ (hk ▸ Ideal.mem_span_singleton_self _)
  have hsqJ := subspaceInclusion_comp_of_fixes B hΛ hSpec X hX toK
    (spaceSelfArrowMap B hΛ hSpec X hX toK j) (spaceSpecialMap_comp B hΛ hSpec X hX toK j)
  have hcm := conormalMap_spaceSpecialSubspace_eq_map_familySpecialConormalSmul B hΛ hSpec
    xε.1.left xε.1.hom.base _ hk hann hG
    (spaceSelfArrowMap_comp_spaceTotalToBase B hΛ hSpec X hX toK j) c' hσε hsqJ
    (subspaceInclusion_comp_id_special B hΛ hSpec X hX toK)
  have hJπ := spaceSelfArrowMap_comp_spaceRetraction B hΛ hSpec X hX toK i j hj0
  have hBJ := spaceSelfArrowMap_comp_spaceAutHom B hΛ hSpec X hX toK hp s j hj a
  have hac : subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec xε.1.left)
        (spacePointSpecial B hΛ hSpec X hX toK xε.1) ≫ spaceSelfArrowMap B hΛ hSpec X hX toK j ≫
        spaceRetraction B hΛ hSpec X hX toK i =
      spaceRetractionSpecial B hΛ hSpec X hX toK i ≫
        subspaceInclusion B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
          (topSubspace B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)) := by
    rw [hJπ]; exact spaceRetractionSpecial_spec B hΛ hSpec X hX toK i
  have hmove := comp_derivationMove_top_of_conormalMap_eq B (Spec (.of Λ)) hΛ
    (X := spaceTotalSpace B hΛ hSpec xε.1.left) (W := spaceOf B hΛ X hX)
    (T := schemeSpace (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))
    (spaceSpecialSubspace B hΛ hSpec xε.1.left xε.1.hom.base) hG
    (spaceStructureMap B hΛ hSpec X hX toK)
    (spaceRetractionSpecial B hΛ hSpec X hX toK i) (spaceRetraction B hΛ hSpec X hX toK i)
    (spaceRetractionSpecial_spec B hΛ hSpec X hX toK i) (spaceSelfArrowMap B hΛ hSpec X hX toK j)
    hsqJ (subspaceInclusion_comp_id_special B hΛ hSpec X hX toK)
    (familySpecialConormalSmul B hΛ hSpec xε.1.left xε.1.hom.base c') hcm
    (spaceAutToHom B hΛ hSpec X hX toK hpair i a) hac
  apply (spaceLiftsEquiv B hΛ hSpec X hX toK hpair i).injective
  apply TopLifts.ext
  rw [spaceLiftsEquiv_spaceAutToHom]
  calc spaceAutHom B hΛ hSpec X hX toK (pushforwardAutomorphism hp s j hj a) ≫
        spaceRetraction B hΛ hSpec X hX toK i
      = spaceAutHom B hΛ hSpec X hX toK (pushforwardAutomorphism hp s j hj a) ≫
          spaceSelfArrowMap B hΛ hSpec X hX toK j ≫ spaceRetraction B hΛ hSpec X hX toK i := by
        rw [hJπ]
    _ = spaceSelfArrowMap B hΛ hSpec X hX toK j ≫
          (spaceLiftsEquiv B hΛ hSpec X hX toK hpair i
            (spaceAutToHom B hΛ hSpec X hX toK hpair i a)).1 := by
        rw [spaceLiftsEquiv_spaceAutToHom B hΛ hSpec X hX toK hpair i a, ← Category.assoc, ← hBJ,
          Category.assoc]
    _ = _ := hmove
    _ = _ := derivationMove_congr_of_eq B (Spec (.of Λ)) hΛ _ hG _ _ rfl hJπ _
          (spaceRetractionSpecial_spec B hΛ hSpec X hX toK i)
          (congrArg (· ≫ spaceStructureMap B hΛ hSpec X hX toK) hJπ) rfl rfl

/-- `modulePullbackHomAddEquivOfIso` sends a map `f` to its pullback `α^*f`. -/
theorem modulePullbackHomAddEquivOfIso_apply' {Y Y' : AlgebraicSpaces B (Spec (.of Λ)) hΛ}
    (α : Y' ≅ Y) (M N : Space.Modules.{u, u} B (Spec (.of Λ)) hΛ Y.1 Y.2) (f : M ⟶ N) :
    modulePullbackHomAddEquivOfIso B hΛ α M N f =
      (modulePullback B (Spec (.of Λ)) hΛ α.hom).map f :=
  rfl

/-- `homAddEquivOfIso a b` sends a map `f` to its conjugate `a⁻¹ ≫ f ≫ b`. -/
theorem homAddEquivOfIso_apply' {C : Type*} [Category C] [Preadditive C] {M M' N N' : C}
    (a : M ≅ M') (b : N ≅ N') (f : M ⟶ N) : homAddEquivOfIso a b f = a.inv ≫ f ≫ b.hom :=
  rfl

/-- **Transport of a twisted map along an isomorphism of algebraic spaces.**  For the composite
`θ ↦ (α^*)⁻¹(src ≫ θ ≫ tgt)` of conjugation by isomorphisms and the inverse of `α^*`, a map
`θ ≫ μ` goes to the image of `θ` followed by `ν`, as soon as `μ ≫ tgt = tgt ≫ α^*ν`. -/
theorem homAddEquivOfIso_trans_modulePullbackHomAddEquivOfIso_symm_comp
    {Y Y' : AlgebraicSpaces B (Spec (.of Λ)) hΛ} (α : Y' ≅ Y)
    {M N : Space.Modules.{u, u} B (Spec (.of Λ)) hΛ Y.1 Y.2}
    {M' C : Space.Modules.{u, u} B (Spec (.of Λ)) hΛ Y'.1 Y'.2}
    (src : (modulePullback B (Spec (.of Λ)) hΛ α.hom).obj M ≅ M')
    (tgt : C ≅ (modulePullback B (Spec (.of Λ)) hΛ α.hom).obj N)
    (θ : M' ⟶ C) (μ : C ⟶ C) (ν : N ⟶ N)
    (hμν : μ ≫ tgt.hom = tgt.hom ≫ (modulePullback B (Spec (.of Λ)) hΛ α.hom).map ν) :
    ((homAddEquivOfIso src.symm tgt).trans (modulePullbackHomAddEquivOfIso B hΛ α M N).symm)
        (θ ≫ μ) =
      ((homAddEquivOfIso src.symm tgt).trans (modulePullbackHomAddEquivOfIso B hΛ α M N).symm)
        θ ≫ ν := by
  apply (modulePullbackHomAddEquivOfIso B hΛ α M N).injective
  rw [AddEquiv.trans_apply, AddEquiv.apply_symm_apply, AddEquiv.trans_apply,
    modulePullbackHomAddEquivOfIso_apply', Functor.map_comp,
    ← modulePullbackHomAddEquivOfIso_apply', AddEquiv.apply_symm_apply, homAddEquivOfIso_apply',
    homAddEquivOfIso_apply', Category.assoc, Category.assoc, Category.assoc, hμν]

omit hSpec in
/-- **Pulling back a function along a composite with the morphism of spectra of a map of `𝒞_Λ`**
is pulling back its image. -/
theorem pullbackToGlobalFunctions_comp_spaceBaseOverMap
    (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
    (Y : AlgebraicSpaces B (Spec (.of Λ)) hΛ) {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (q : Y ⟶ schemeSpace (spaceBaseOver B hΛ hSpec A')) (φ : A ⟶ A') (a : A) :
    pullbackToGlobalFunctions B (Spec (.of Λ)) hΛ Y (spaceBaseOver B hΛ hSpec A)
        (q ≫ schemeSpaceMap (spaceBaseOverMap B hΛ hSpec φ))
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      pullbackToGlobalFunctions B (Spec (.of Λ)) hΛ Y (spaceBaseOver B hΛ hSpec A') q
        ((Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom (φ.hom a)) := by
  rw [pullbackToGlobalFunctions_comp_schemeSpaceMap, toScheme_map_spaceBaseOverMap]
  have h := congrArg (fun ψ => ψ.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ.hom.toRingHom))
  change (Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom (φ.hom a) =
    (Spec.map (CommRingCat.ofHom φ.hom.toRingHom)).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) at h
  exact (congrArg (pullbackToGlobalFunctions B (Spec (.of Λ)) hΛ Y
    (spaceBaseOver B hΛ hSpec A') q) h).symm

/-- **The function `c'` on the special fibre is the function `c` pulled back from `Spec k`**, for
`c'` of residue `c`. -/
theorem familySpecialBaseFunction_eq_pullbackToGlobalFunctions (c' : xε.1.left.base) :
    familySpecialBaseFunction B hΛ hSpec xε.1.left xε.1.hom.base c' =
      pullbackToGlobalFunctions B (Spec (.of Λ)) hΛ
        (spacePointSpecialSpace B hΛ hSpec X hX toK (xε := xε))
        (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))
        ((spaceSpecialIso B hΛ hSpec X hX toK i).hom ≫ spaceStructureMap B hΛ hSpec X hX toK)
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (xε.1.hom.base.hom c')) := by
  have hq : subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec xε.1.left)
        (spaceSpecialSubspace B hΛ hSpec xε.1.left xε.1.hom.base) ≫
        spaceTotalToBase B hΛ hSpec xε.1.left =
      ((spaceSpecialIso B hΛ hSpec X hX toK i).hom ≫ spaceStructureMap B hΛ hSpec X hX toK) ≫
        schemeSpaceMap (spaceBaseOverMap B hΛ hSpec xε.1.hom.base) := by
    apply ObjectProperty.hom_ext
    refine (spacePointSpecial_ι_comp_toBase B hΛ hSpec X hX toK xε.1).trans ?_
    refine congrArg (· ≫ yoneda.map (spaceBaseOverMap B hΛ hSpec xε.1.hom.base)) ?_
    exact (spacePointSpecial_ι_comp_retraction_comp_toK B hΛ hSpec X hX toK i).symm.trans
      (Category.assoc _ _ _).symm
  unfold familySpecialBaseFunction
  rw [hq]
  exact pullbackToGlobalFunctions_comp_spaceBaseOverMap B hΛ hSpec _ _ _ c'

/-- The source identification of `Deformation.Examples.spaceLiftHomAddEquiv`:
`π|_G^*Ω_{X/k} ≅ e₀^*Ω_{⊤/k}`. -/
def spaceLiftSrcIso :
    (modulePullback B (Spec (.of Λ)) hΛ (spaceSpecialIso B hΛ hSpec X hX toK i).hom).obj
      (sheafOfDifferentials B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK)) ≅
      (modulePullback B (Spec (.of Λ)) hΛ (spaceRetractionSpecial B hΛ hSpec X hX toK i)).obj
        (sheafOfDifferentials B (Spec (.of Λ)) hΛ
          (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
            (topSubspace B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)) ≫
            spaceStructureMap B hΛ hSpec X hX toK)) :=
  haveI := isIso_topDifferentialsMap B hΛ hSpec X hX toK
  eqToIso (congrArg (fun h => (modulePullback B (Spec (.of Λ)) hΛ h).obj
      (sheafOfDifferentials B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK)))
      (spaceSpecialIso_hom_eq B hΛ hSpec X hX toK i)) ≪≫
    ((modulePullbackCompIso B (Spec (.of Λ)) hΛ (spaceRetractionSpecial B hΛ hSpec X hX toK i)
      (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
        (topSubspace B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)))).app
      (sheafOfDifferentials B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK))).symm ≪≫
    (modulePullback B (Spec (.of Λ)) hΛ (spaceRetractionSpecial B hΛ hSpec X hX toK i)).mapIso
      (asIso (topDifferentialsMap B hΛ hSpec X hX toK))

/-- The target identification of `Deformation.Examples.spaceLiftHomAddEquiv`:
`𝒞_{G/X'} ≅ π|_G^*𝒪_X`. -/
def spaceLiftTgtIso :
    conormalModule B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec xε.1.left)
        (spacePointSpecial B hΛ hSpec X hX toK xε.1) ≅
      (modulePullback B (Spec (.of Λ)) hΛ (spaceSpecialIso B hΛ hSpec X hX toK i).hom).obj
        (spaceStructureModule B hΛ (spaceOf B hΛ X hX)) :=
  spaceSpecialConormalIsoUnit B hΛ hSpec xε.1.left xε.1.hom.base
      (exists_epsilon_spacePoint B hΛ hSpec X hX toK hpair (xε := xε)).choose
      (exists_epsilon_spacePoint B hΛ hSpec X hX toK hpair (xε := xε)).choose_spec.1
      (exists_epsilon_spacePoint B hΛ hSpec X hX toK hpair (xε := xε)).choose_spec.2
      (isFirstOrderThickening_spacePointSpecial B hΛ hSpec X hX toK hpair) ≪≫
    (modulePullbackUnitIso B (Spec (.of Λ)) hΛ (spaceSpecialIso B hΛ hSpec X hX toK i).hom).symm

/-- `Deformation.Examples.spaceLiftHomAddEquiv`, through its two identifications. -/
theorem spaceLiftHomAddEquiv_eq :
    spaceLiftHomAddEquiv B hΛ hSpec X hX toK hpair i =
      (homAddEquivOfIso (spaceLiftSrcIso B hΛ hSpec X hX toK i).symm
        (spaceLiftTgtIso B hΛ hSpec X hX toK hpair i)).trans
        (modulePullbackHomAddEquivOfIso B hΛ (spaceSpecialIso B hΛ hSpec X hX toK i) _ _).symm :=
  rfl

omit [Field k] [Algebra Λ k] in
/-- The sections of the structure sheaf of `X` commute, in the unbundled form
`Stacks.Cohomology.SiteModules.globalSmul` takes. -/
instance spaceOfStructureRingSheaf_isMulCommutative
    (U : (SmallEtale B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX).1)ᵒᵖ) :
    IsMulCommutative ((structureRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).obj.obj U) :=
  structureRingSheaf_isMulCommutative B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX) U

/-- **On the side of `Hom(Ω_{X/k}, 𝒪_X)`, multiplication by `c'` on `𝒞_{G/X'}` is multiplication by
the residue of `c'`**, read through the identification
`Deformation.Examples.spaceLiftHomAddEquiv`. -/
theorem spaceLiftHomAddEquiv_comp_familySpecialConormalSmul
    (θ : SpaceLiftHom B hΛ hSpec X hX toK i) (c' : xε.1.left.base) :
    spaceLiftHomAddEquiv B hΛ hSpec X hX toK hpair i
        (θ ≫ familySpecialConormalSmul B hΛ hSpec xε.1.left xε.1.hom.base c') =
      spaceLiftHomAddEquiv B hΛ hSpec X hX toK hpair i θ ≫
        globalSmul (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))
          (spaceResidueFieldRingHom B hΛ hSpec X hX toK (xε.1.hom.base.hom c'))
          (spaceStructureModule B hΛ (spaceOf B hΛ X hX)) := by
  have hS1 := modulePullback_map_globalSmul_of_chartDiagramPullback B (Spec (.of Λ)) hΛ
    (spaceSpecialIso B hΛ hSpec X hX toK i).hom
    (spaceResidueFieldRingHom B hΛ hSpec X hX toK (xε.1.hom.base.hom c'))
    (familySpecialBaseFunction B hΛ hSpec xε.1.left xε.1.hom.base c')
    (fun d => by
      rw [familySpecialBaseFunction_eq_pullbackToGlobalFunctions B hΛ hSpec X hX toK i]
      exact chartDiagramPullback_pullbackToGlobalFunctions B (Spec (.of Λ)) hΛ
        (spaceSpecialIso B hΛ hSpec X hX toK i).hom
        (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)) (spaceStructureMap B hΛ hSpec X hX toK)
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (xε.1.hom.base.hom c')) d)
    (spaceStructureModule B hΛ (spaceOf B hΛ X hX))
  have hμν : ∀ φ : conormalModule B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec xε.1.left)
        (spacePointSpecial B hΛ hSpec X hX toK xε.1) ⟶
      (modulePullback B (Spec (.of Λ)) hΛ (spaceSpecialIso B hΛ hSpec X hX toK i).hom).obj
        (spaceStructureModule B hΛ (spaceOf B hΛ X hX)),
      familySpecialConormalSmul B hΛ hSpec xε.1.left xε.1.hom.base c' ≫ φ =
        φ ≫ (modulePullback B (Spec (.of Λ)) hΛ (spaceSpecialIso B hΛ hSpec X hX toK i).hom).map
          (globalSmul (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))
          (spaceResidueFieldRingHom B hΛ hSpec X hX toK (xε.1.hom.base.hom c'))
            (spaceStructureModule B hΛ (spaceOf B hΛ X hX))) := fun φ => by
    rw [hS1]; exact (comp_globalSmul _ _ φ).symm
  rw [spaceLiftHomAddEquiv_eq]
  exact homAddEquivOfIso_trans_modulePullbackHomAddEquivOfIso_symm_comp B hΛ
    (spaceSpecialIso B hΛ hSpec X hX toK i) _ (spaceLiftTgtIso B hΛ hSpec X hX toK hpair i) θ
    (familySpecialConormalSmul B hΛ hSpec xε.1.left xε.1.hom.base c') _ (hμν _)

omit [Algebra Λ k] in
/-- An element of the maximal ideal of a ring with a dual-number coordinate is a multiple of `ε`
in that coordinate. -/
theorem eq_inl_mul_eps_of_fst_eq_zero (z : DualNumber k) (hz : TrivSqZeroExt.fst z = 0) :
    z = TrivSqZeroExt.inl (TrivSqZeroExt.snd z) * DualNumber.eps := by
  ext <;> simp [hz]

/-- **A dual-number scaling multiplies the maximal ideal by a lift of the scalar.**  If in a
dual-number coordinate `φ` the endomorphism `s` fixes `k` and sends `ε` to `c ε`, then `s`
multiplies every element of the maximal ideal by `φ⁻¹(c)`, an element of residue `c`. -/
theorem exists_mul_of_dualNumberScaling {A : ArtinianLocalAlgCat.{u, u, u} Λ k} (c : k)
    (s : A ⟶ A)
    (hs : ∃ φ : A ≃ₐ[Λ] DualNumber k,
      (∀ t : A, (φ t).1 = A.residueEquiv (IsLocalRing.residue A t)) ∧
      (∀ t : k, φ (s.hom (φ.symm (TrivSqZeroExt.inl t))) = TrivSqZeroExt.inl t) ∧
      φ (s.hom (φ.symm DualNumber.eps)) = c • DualNumber.eps) :
    ∃ c' : A, A.residueEquiv (IsLocalRing.residue A c') = c ∧
      ∀ x ∈ IsLocalRing.maximalIdeal A, s.hom x = c' * x := by
  obtain ⟨φ, h1, h2, h3⟩ := hs
  refine ⟨φ.symm (TrivSqZeroExt.inl c), ?_, fun x hx => ?_⟩
  · rw [← h1, AlgEquiv.apply_symm_apply]
    rfl
  · have hx0 : TrivSqZeroExt.fst (φ x) = 0 :=
      (h1 x).trans (by rw [(IsLocalRing.residue_eq_zero_iff x).2 hx, map_zero])
    have hxe := eq_inl_mul_eps_of_fst_eq_zero (φ x) hx0
    apply φ.injective
    have hsx : s.hom x = s.hom (φ.symm (TrivSqZeroExt.inl (TrivSqZeroExt.snd (φ x)))) *
        s.hom (φ.symm DualNumber.eps) := by
      rw [← map_mul, ← map_mul, ← hxe, AlgEquiv.symm_apply_apply]
    rw [hsx, map_mul, h2, h3, map_mul, AlgEquiv.apply_symm_apply, hxe]
    ext <;> simp

/-- The data of a scaling transported along an equality of objects of `𝒞_Λ`. -/
theorem exists_mul_of_eq {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (h : A = A')
    (s : A' ⟶ A') (c : k) {c' : A'} (hres : A'.residueEquiv (IsLocalRing.residue A' c') = c)
    (hs : ∀ x ∈ IsLocalRing.maximalIdeal A', s.hom x = c' * x) :
    ∃ c'' : A, A.residueEquiv (IsLocalRing.residue A c'') = c ∧
      ∀ x ∈ IsLocalRing.maximalIdeal A, (eqToHom h ≫ s ≫ eqToHom h.symm).hom x = c'' * x := by
  subst h
  refine ⟨c', hres, fun x hx => ?_⟩
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hs x hx

end Deformation.Examples

end
