module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FlatDeformation.InverseImageSections
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceFundamentalTriangle
public import StacksFrontier.AlgebraicGeometry.Thickenings.FirstOrderConormalInclusion

/-!
# The inverse image of a first order thickening of the base
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap
  sheafAdjunction structureSheafMap)
open Stacks.Sheaves.RingedSpaceCotangent (baseStructureMap)

universe u

namespace Stacks.Thickenings.FlatDeformation

section RingedSpace

variable {X S S' : RingedSpace.{u, u}} (t : S ⟶ S') (f : X ⟶ S)

/-- The comorphism of a morphism of ringed spaces on sections over `W`. -/
abbrev comorphism (W : Opens S') : S'.presheaf.obj (op W) ⟶
    S.presheaf.obj (op ((Opens.map t.hom.base).obj W)) :=
  t.hom.c.app (op W)

/-- The reduction `(t ∘ f)⁻¹𝒪_{S'} ⟶ f⁻¹𝒪_S` sends the image under the unit of a section of
`𝒪_{S'}` to the image under the unit of the restriction of that section to `S`. -/
theorem baseStructureMap_pullbackUnitApp (W : Opens S') (j : S'.presheaf.obj (op W)) :
    (baseStructureMap f t).hom.app (op ((Opens.map (f ≫ t).hom.base).obj W))
        (pullbackUnitApp (f ≫ t).hom.base S'.sheaf W j) =
      pullbackUnitApp f.hom.base S.sheaf ((Opens.map t.hom.base).obj W) (comorphism t W j) := by
  have h : (sheafAdjunction (f ≫ t)).homEquiv _ _ (baseStructureMap f t) =
      structureSheafMap t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map
          ((sheafAdjunction f).unit.app S.sheaf) :=
    Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_unit] at h
  exact congr($(h).hom.app (op W) j)

/-- The comorphism commutes with restriction. -/
theorem comorphism_restrict {W W' : Opens S'} (h : W' ≤ W) (j : S'.presheaf.obj (op W)) :
    comorphism t W' (S'.presheaf.map (homOfLE h).op j) =
      S.presheaf.map (homOfLE ((Opens.map t.hom.base).monotone h)).op (comorphism t W j) :=
  ConcreteCategory.congr_hom (t.hom.c.naturality (homOfLE h).op) j

/-- If `a` restricts to the unit image of `j₀` on `V₀`, it restricts to the unit image of the
restriction of `j₀` to a smaller open `W` on any `V ≤ V₀` mapping into `W`. -/
private theorem map_eq_pullbackUnitApp_restrict {U V V₀ : Opens X} {W W₀ : Opens S'}
    (hVU : V ≤ U) (hV₀U : V₀ ≤ U) (hVV₀ : V ≤ V₀)
    (hV₀W₀ : V₀ ≤ (Opens.map (f ≫ t).hom.base).obj W₀)
    (hVW : V ≤ (Opens.map (f ≫ t).hom.base).obj W) (hWW₀ : W ≤ W₀)
    (a : (inverseImageSheaf (f ≫ t)).presheaf.obj (op U)) (j₀ : S'.presheaf.obj (op W₀))
    (hres : (inverseImageSheaf (f ≫ t)).presheaf.map (homOfLE hV₀U).op a =
      (inverseImageSheaf (f ≫ t)).presheaf.map (homOfLE hV₀W₀).op
        (pullbackUnitApp (f ≫ t).hom.base S'.sheaf W₀ j₀)) :
    (inverseImageSheaf (f ≫ t)).presheaf.map (homOfLE hVU).op a =
      (inverseImageSheaf (f ≫ t)).presheaf.map (homOfLE hVW).op
        (pullbackUnitApp (f ≫ t).hom.base S'.sheaf W (S'.presheaf.map (homOfLE hWW₀).op j₀)) :=
  ((presheaf_map_map _ hV₀U hVV₀ a).symm.trans
    ((congrArg _ hres).trans (presheaf_map_map _ _ _ _))).trans
    ((presheaf_map_map _ _ hVW _).symm.trans
      (congrArg _ (pullbackUnitApp_restrict (f ≫ t).hom.base S'.sheaf hWW₀ j₀)))

variable {t} (ht : Topology.IsInducing t.hom.base)
include ht

/-- A section of `𝒪_{S'}` whose restriction to `S` has zero germ at a point has zero restriction
to `S` over an open of `S'` around it. -/
theorem exists_comorphism_eq_zero_of_germ (W₀ : Opens S') (j₀ : S'.presheaf.obj (op W₀)) (y : S)
    (hy : y ∈ (Opens.map t.hom.base).obj W₀)
    (h : S.presheaf.germ ((Opens.map t.hom.base).obj W₀) y hy (comorphism t W₀ j₀) = 0) :
    ∃ (W : Opens S') (hW : W ≤ W₀), t.hom.base y ∈ W ∧
      comorphism t W (S'.presheaf.map (homOfLE hW).op j₀) = 0 := by
  obtain ⟨N, hyN, i₁, i₂, hN⟩ := TopCat.Presheaf.germ_eq S.presheaf y hy hy
    (comorphism t W₀ j₀) 0 (h.trans (map_zero _).symm)
  rw [map_zero] at hN
  obtain ⟨W₁, hW₁, hW₁N⟩ := ht.isOpen_iff.mp N.2
  have hle : (Opens.map t.hom.base).obj (W₀ ⊓ ⟨W₁, hW₁⟩) ≤ N := fun z hz => by
    have : z ∈ t.hom.base ⁻¹' W₁ := hz.2
    rw [hW₁N] at this
    exact this
  refine ⟨W₀ ⊓ ⟨W₁, hW₁⟩, inf_le_left, ⟨leOfHom i₁ hyN, ?_⟩, ?_⟩
  · show y ∈ t.hom.base ⁻¹' W₁
    rw [hW₁N]
    exact hyN
  · have hnat := congr($(t.hom.c.naturality (homOfLE (inf_le_left : W₀ ⊓ ⟨W₁, hW₁⟩ ≤ W₀)).op) j₀)
    refine hnat.trans ?_
    have e : (Opens.map t.hom.base).op.map (homOfLE (inf_le_left : W₀ ⊓ ⟨W₁, hW₁⟩ ≤ W₀)).op =
        i₁.op ≫ (homOfLE hle).op := rfl
    show (S.presheaf.map _) (comorphism t W₀ j₀) = 0
    rw [e, Functor.map_comp, CommRingCat.comp_apply, hN, map_zero]

/-- **A local section of `(t ∘ f)⁻¹𝒪_{S'}` killed by the reduction is, near each point, the image
under the unit of a section of `𝒪_{S'}` whose restriction to `S` vanishes.** -/
theorem exists_eq_pullbackUnitApp_of_baseStructureMap_eq_zero (U : Opens X)
    (a : (inverseImageSheaf (f ≫ t)).presheaf.obj (op U))
    (ha : (baseStructureMap f t).hom.app (op U) a = 0) (x : X) (hx : x ∈ U) :
    ∃ (W : Opens S') (_ : (f ≫ t).hom.base x ∈ W) (j : S'.presheaf.obj (op W))
      (_ : comorphism t W j = 0) (V : Opens X) (_ : x ∈ V) (hVU : V ≤ U)
      (hVW : V ≤ (Opens.map (f ≫ t).hom.base).obj W),
      (inverseImageSheaf (f ≫ t)).presheaf.map (homOfLE hVU).op a =
        (inverseImageSheaf (f ≫ t)).presheaf.map (homOfLE hVW).op
          (pullbackUnitApp (f ≫ t).hom.base S'.sheaf W j) := by
  obtain ⟨W₀, hW₀, j₀, V₀, hxV₀, hV₀U, hV₀W, hres⟩ :=
    exists_eq_pullbackUnitApp (f ≫ t).hom.base S'.sheaf U a x hx
  have h0 : (inverseImageSheaf f).presheaf.map (homOfLE hV₀W).op
      ((baseStructureMap f t).hom.app _ (pullbackUnitApp (f ≫ t).hom.base S'.sheaf W₀ j₀)) =
        0 := by
    refine (sheafHom_app_map (baseStructureMap f t) hV₀W _).symm.trans ?_
    refine (congrArg ((baseStructureMap f t).hom.app (op V₀)) hres.symm).trans ?_
    refine (sheafHom_app_map (baseStructureMap f t) hV₀U a).trans ?_
    rw [ha, map_zero]
  replace h0 := (congrArg ((inverseImageSheaf f).presheaf.map (homOfLE hV₀W).op)
    (baseStructureMap_pullbackUnitApp t f W₀ j₀)).symm.trans h0
  have hgerm : (inverseImageSheaf f).presheaf.germ
      ((Opens.map f.hom.base).obj ((Opens.map t.hom.base).obj W₀)) x hW₀
      (pullbackUnitApp f.hom.base S.sheaf _ (comorphism t W₀ j₀)) = 0 := by
    exact (TopCat.Presheaf.germ_res_apply (inverseImageSheaf f).presheaf (homOfLE hV₀W) x hxV₀
      _).symm.trans ((congrArg ((inverseImageSheaf f).presheaf.germ V₀ x hxV₀) h0).trans
        (map_zero _))
  have hgerm' := germ_eq_zero_of_germ_pullbackUnitApp f.hom.base S.sheaf _ x hW₀ _ hgerm
  obtain ⟨W, hWW₀, hxW, hj⟩ := exists_comorphism_eq_zero_of_germ ht W₀ j₀ (f.hom.base x) hW₀
    hgerm'
  have hVW : V₀ ⊓ (Opens.map (f ≫ t).hom.base).obj W ≤ (Opens.map (f ≫ t).hom.base).obj W :=
    inf_le_right
  refine ⟨W, hxW, S'.presheaf.map (homOfLE hWW₀).op j₀, hj,
    V₀ ⊓ (Opens.map (f ≫ t).hom.base).obj W, ⟨hxV₀, hxW⟩, inf_le_left.trans hV₀U, hVW, ?_⟩
  exact map_eq_pullbackUnitApp_restrict t f _ hV₀U inf_le_left hV₀W hVW hWW₀ a j₀ hres

omit ht in
/-- **The reduction `(t ∘ f)⁻¹𝒪_{S'} ⟶ f⁻¹𝒪_S` is locally surjective** as soon as every section
of `𝒪_S` is, near each point, the restriction of a section of `𝒪_{S'}`. -/
theorem isLocallySurjective_baseStructureMap
    (hsurj : ∀ (N : Opens S) (r : S.presheaf.obj (op N)) (y : S) (_ : y ∈ N),
      ∃ (W : Opens S') (_ : t.hom.base y ∈ W) (j : S'.presheaf.obj (op W)) (M : Opens S)
        (_ : y ∈ M) (hMN : M ≤ N) (hMW : M ≤ (Opens.map t.hom.base).obj W),
        S.presheaf.map (homOfLE hMN).op r = S.presheaf.map (homOfLE hMW).op (comorphism t W j)) :
    TopCat.Presheaf.IsLocallySurjective (baseStructureMap f t).hom := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U a x hx
  obtain ⟨N, hN, r, V₀, hxV₀, hV₀U, hV₀N, hres⟩ :=
    exists_eq_pullbackUnitApp f.hom.base S.sheaf U a x hx
  obtain ⟨W, hW, j, M, hyM, hMN, hMW, hj⟩ := hsurj N r (f.hom.base x) hN
  have hV : V₀ ⊓ (Opens.map f.hom.base).obj M ≤ (Opens.map (f ≫ t).hom.base).obj W :=
    inf_le_right.trans ((Opens.map f.hom.base).monotone hMW)
  refine ⟨V₀ ⊓ (Opens.map f.hom.base).obj M, inf_le_left.trans hV₀U,
    ⟨(inverseImageSheaf (f ≫ t)).presheaf.map (homOfLE hV).op
      (pullbackUnitApp (f ≫ t).hom.base S'.sheaf W j), ?_⟩, ⟨hxV₀, hyM⟩⟩
  refine (sheafHom_app_map (baseStructureMap f t) hV _).trans ?_
  refine (congrArg _ (baseStructureMap_pullbackUnitApp t f W j)).trans ?_
  show _ = (inverseImageSheaf f).presheaf.map _ a
  refine (presheaf_map_map _ ((Opens.map f.hom.base).monotone hMW) inf_le_right _).symm.trans ?_
  refine (congrArg _ (pullbackUnitApp_restrict f.hom.base S.sheaf hMW _)).trans ?_
  refine (congrArg (fun z => (inverseImageSheaf f).presheaf.map _
    (pullbackUnitApp f.hom.base S.sheaf M z)) hj.symm).trans ?_
  refine (congrArg _ (pullbackUnitApp_restrict f.hom.base S.sheaf hMN r).symm).trans ?_
  refine (presheaf_map_map _ _ _ _).trans ?_
  refine (presheaf_map_map _ hV₀N inf_le_left _).symm.trans ?_
  exact (congrArg _ hres.symm).trans (presheaf_map_map _ _ _ _)

/-- **The kernel of the reduction `(t ∘ f)⁻¹𝒪_{S'} ⟶ f⁻¹𝒪_S` has square zero on sections** as soon
as the kernel of `𝒪_{S'} ⟶ t_*𝒪_S` has. -/
theorem mul_eq_zero_of_baseStructureMap_eq_zero
    (hsq : ∀ (W : Opens S') (j j' : S'.presheaf.obj (op W)), comorphism t W j = 0 →
      comorphism t W j' = 0 → j * j' = 0)
    (U : Opens X) (a b : (inverseImageSheaf (f ≫ t)).presheaf.obj (op U))
    (ha : (baseStructureMap f t).hom.app (op U) a = 0)
    (hb : (baseStructureMap f t).hom.app (op U) b = 0) : a * b = 0 := by
  refine TopCat.Presheaf.section_ext (inverseImageSheaf (f ≫ t)) U (a * b) 0 fun x hx => ?_
  obtain ⟨W, hW, j, hj, V, hxV, hVU, hVW, hres⟩ :=
    exists_eq_pullbackUnitApp_of_baseStructureMap_eq_zero f ht U a ha x hx
  obtain ⟨W', hW', j', hj', V', hxV', hV'U, hV'W', hres'⟩ :=
    exists_eq_pullbackUnitApp_of_baseStructureMap_eq_zero f ht U b hb x hx
  have hWW : W ⊓ W' ≤ W := inf_le_left
  have hWW' : W ⊓ W' ≤ W' := inf_le_right
  have hz : S'.presheaf.map (homOfLE hWW).op j * S'.presheaf.map (homOfLE hWW').op j' = 0 :=
    hsq _ _ _ (by rw [comorphism_restrict, hj, map_zero])
      (by rw [comorphism_restrict, hj', map_zero])
  have hle : V ⊓ V' ≤ (Opens.map (f ≫ t).hom.base).obj (W ⊓ W') :=
    le_inf (inf_le_left.trans hVW) (inf_le_right.trans hV'W')
  have ea := map_eq_pullbackUnitApp_restrict t f (inf_le_left.trans hVU) hVU inf_le_left hVW hle
    hWW a j hres
  have eb := map_eq_pullbackUnitApp_restrict t f (inf_le_right.trans hV'U) hV'U inf_le_right
    hV'W' hle hWW' b j' hres'
  have hab : (inverseImageSheaf (f ≫ t)).presheaf.map
      (homOfLE (inf_le_left.trans hVU : V ⊓ V' ≤ U)).op (a * b) = 0 := by
    refine (map_mul _ a b).trans ?_
    refine (congrArg₂ (· * ·) ea eb).trans ?_
    refine (map_mul _ _ _).symm.trans ?_
    refine (congrArg _ (map_mul _ _ _).symm).trans ?_
    refine (congrArg (fun z => (inverseImageSheaf (f ≫ t)).presheaf.map (homOfLE hle).op
      (pullbackUnitApp (f ≫ t).hom.base S'.sheaf _ z)) hz).trans ?_
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  exact (TopCat.Presheaf.germ_res_apply (inverseImageSheaf (f ≫ t)).presheaf
    (homOfLE (inf_le_left.trans hVU : V ⊓ V' ≤ U)) x ⟨hxV, hxV'⟩ _).symm.trans
    ((congrArg _ hab).trans ((map_zero _).trans (map_zero _).symm))

end RingedSpace

/-! ### The case of a first order thickening of schemes -/

section Scheme

variable {X S S' : Scheme.{u}} (t : S ⟶ S') (f : X ⟶ S)

/-- Every section of the structure sheaf of the closed subscheme is, near each point, the
restriction of a section of the ambient structure sheaf. -/
theorem exists_comorphism_eq_of_isClosedImmersion [IsClosedImmersion t] (N : S.Opens)
    (r : Γ(S, N)) (y : S) (hy : y ∈ N) :
    ∃ (W : S'.Opens) (_ : t.base y ∈ W) (j : Γ(S', W)) (M : S.Opens)
      (_ : y ∈ M) (hMN : M ≤ N) (hMW : M ≤ t ⁻¹ᵁ W),
      S.presheaf.map (homOfLE hMN).op r =
        S.presheaf.map (homOfLE hMW).op (comorphism t.toLRSHom.toShHom W j) := by
  obtain ⟨g, hg⟩ := t.stalkMap_surjective y (S.presheaf.germ N y hy r)
  obtain ⟨W, hW, j, rfl⟩ := TopCat.Presheaf.exists_germ_eq S'.presheaf g
  rw [Scheme.Hom.germ_stalkMap_apply] at hg
  obtain ⟨M, hyM, i₁, i₂, hM⟩ := TopCat.Presheaf.germ_eq S.presheaf y hW hy _ _ hg
  exact ⟨W, hW, j, M, hyM, leOfHom i₂, leOfHom i₁, hM.symm⟩

/-- On a first order thickening of schemes, two sections of the ambient structure sheaf killed by
the comorphism multiply to zero. -/
theorem mul_eq_zero_of_comorphism [IsClosedImmersion t] (hst : t.ker ^ 2 = ⊥) (W : S'.Opens)
    (j j' : Γ(S', W)) (hj : comorphism t.toLRSHom.toShHom W j = 0)
    (hj' : comorphism t.toLRSHom.toShHom W j' = 0) : j * j' = 0 := by
  have h := Ideal.mul_mem_mul (RingHom.mem_ker.mpr hj) (RingHom.mem_ker.mpr hj')
  have h2 : RingHom.ker (comorphism t.toLRSHom.toShHom W).hom *
      RingHom.ker (comorphism t.toLRSHom.toShHom W).hom = ⊥ := by
    rw [← pow_two]
    exact ker_app_sq_eq_bot t hst W
  rw [h2] at h
  exact h

end Scheme

end Stacks.Thickenings.FlatDeformation
