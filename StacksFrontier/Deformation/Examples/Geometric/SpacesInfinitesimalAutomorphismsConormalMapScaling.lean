module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsEpsilonMulScaling
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackComparisonUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalMapAgreement

/-!
# The conormal map of a self-map of a family over a rescaling of the base

Let `X'` be the total space of a flat family over an object `A` of `𝒞_Λ` with a dual-number
coordinate `ε`, `G ⊆ X'` its special fibre, and `J : X' ⟶ X'` a self-map restricting to the
identity of `G` and lying over the morphism of spectra of an endomorphism `σ` of `A` with
`σ(ε) = c ε`.  Then the conormal map of the square `(J, 𝟙_G)` of [Stacks Project, Tag 04CP] is the
conormal map of the identity followed by multiplication by the function `c` on `G`:

`conormalMap(J) = conormalMap(𝟙) ≫ c·`.

The conormal module is `𝒞 = i^*𝓘_G`, and `i^*(ε·) : i^*𝒪_{X'} ⟶ 𝒞` is an isomorphism
(`AlgebraicGeometry.Space.isIso_modulePullback_map_of_isColimit`), so it suffices to compare the
two sides after it.  There the conormal map of a square is its comparison isomorphism followed by
`i^*` of the map of defining ideals, the comparison is natural, and the map of defining ideals
after `J^*(ε·)` is computed by
`Deformation.Examples.modulePullback_map_specialEpsilonMul_comp_idealSheafMap`; the remaining
identifications of inverse images of the structure sheaf are coherent
(`AlgebraicGeometry.Space.modulePullbackTriangle_hom_app_unit_comp`), and multiplication by the
function `c` on `X'` pulls back to multiplication by the function `c` on `G`
(`AlgebraicGeometry.Space.modulePullback_map_globalSmul_of_chartDiagramPullback`).

## Main results

* `AlgebraicGeometry.Space.conormalPullbackCompIso_hom_app_unit_comp`: the comparison of a square
  on the structure sheaf, followed by the identifications of inverse images of the structure
  sheaf, does not depend on the upper edge of the square.
* `Deformation.Examples.conormalMap_spaceSpecialSubspace_eq_comp_globalSmul`: the displayed
  equation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Space Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

universe u


namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The identification of inverse images of the structure sheaf along two equal morphisms,
through the transport of inverse images along the equality. -/
theorem eqToIso_hom_app_unit_comp_modulePullbackUnitIso {X Y : AlgebraicSpaces B S hS}
    {F₁ F₂ : Y ⟶ X} (h : F₁ = F₂) :
    (eqToIso (congrArg (fun F => modulePullback B S hS F) h)).hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS X)) ≫
      (modulePullbackUnitIso B S hS F₂).hom = (modulePullbackUnitIso B S hS F₁).hom := by
  subst h
  exact Category.id_comp _

/-- A component of a composite of three natural isomorphisms, the last one inverted, followed by
a morphism. -/
theorem iso_trans_trans_symm_hom_app_comp {C D : Type*} [Category C] [Category D]
    {F₁ F₂ F₃ F₄ : C ⥤ D} (A : F₁ ≅ F₂) (E : F₂ ≅ F₃) (R : F₄ ≅ F₃) (M : C) {N : D}
    (m : F₄.obj M ⟶ N) :
    (A ≪≫ E ≪≫ R.symm).hom.app M ≫ m = A.hom.app M ≫ E.hom.app M ≫ R.inv.app M ≫ m := by
  simp

section Square

attribute [local irreducible] modulePullback

variable {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
    (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ f (subspaceInclusion B S hS X' Z'))

/-- **The comparison of a square on the structure sheaf.**  The comparison
`f^*i'^* ≅ i^*g^*` of the square at `𝒪_{X'}`, followed by the identifications of `g^*𝒪_{X'}` and of
`i^*𝒪_X` with the structure sheaves, is the comparison `f^*i'^* ≅ (f ≫ i')^*` followed by the
identification of `(f ≫ i')^*𝒪_{X'}`: it does not depend on `g`. -/
theorem conormalPullbackCompIso_hom_app_unit_comp :
    (conormalPullbackCompIso B S hS Z Z' g f hsq).hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS X')) ≫
      (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
        (modulePullbackUnitIso B S hS g).hom ≫
      (modulePullbackUnitIso B S hS (subspaceInclusion B S hS X Z)).hom =
    (modulePullbackCompIso B S hS f (subspaceInclusion B S hS X' Z')).hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS X')) ≫
      (modulePullbackUnitIso B S hS
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ f
          (subspaceInclusion B S hS X' Z'))).hom := by
  have htri := modulePullbackTriangle_hom_app_unit_comp B S hS
    (subspaceInclusion B S hS X Z) g (c := subspaceInclusion B S hS X Z ≫ g) rfl
  rw [modulePullbackTriangle_rfl] at htri
  rw [conormalPullbackCompIso_eq]
  refine (iso_trans_trans_symm_hom_app_comp _ _ _ _ _).trans ?_
  refine congrArg ((modulePullbackCompIso B S hS f (subspaceInclusion B S hS X' Z')).hom.app
    (SheafOfModules.unit (structureRingSheaf B S hS X')) ≫ ·) ?_
  rw [Iso.symm_hom] at htri
  exact (congrArg ((eqToIso (congrArg (fun h => modulePullback B S hS h) hsq.symm)).hom.app
    (SheafOfModules.unit (structureRingSheaf B S hS X')) ≫ ·) htri).trans
    (eqToIso_hom_app_unit_comp_modulePullbackUnitIso B S hS hsq.symm)

end Square

end AlgebraicGeometry.Space

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (P : FlatAlgebraicSpaceFamily B hΛ hSpec) (f : P.base ⟶ residueFieldBase Λ k)

/-- The sections of the structure sheaf of the special fibre commute. -/
instance familySpecialStructureRingSheaf_isMulCommutative
    (U : (SmallEtale B (Spec (.of Λ)) hΛ (spaceSpecialSpace B hΛ hSpec P f).1)ᵒᵖ) :
    IsMulCommutative
      ((structureRingSheaf B (Spec (.of Λ)) hΛ (spaceSpecialSpace B hΛ hSpec P f)).obj.obj U) :=
  structureRingSheaf_isMulCommutative B (Spec (.of Λ)) hΛ (spaceSpecialSpace B hΛ hSpec P f) U

/-- **An element of the base ring, as a global function on the special fibre**: its pullback along
`G ⊆ X' ⟶ Spec A`. -/
def familySpecialBaseFunction (a : P.base) :
    GlobalSectionRing (structureRingSheaf B (Spec (.of Λ)) hΛ
      (spaceSpecialSpace B hΛ hSpec P f)) :=
  pullbackToGlobalFunctions B (Spec (.of Λ)) hΛ (spaceSpecialSpace B hΛ hSpec P f)
    (spaceBaseOver B hΛ hSpec P.base)
    (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
      (spaceSpecialSubspace B hΛ hSpec P f) ≫ spaceTotalToBase B hΛ hSpec P)
    ((Scheme.ΓSpecIso (CommRingCat.of P.base)).inv.hom a)

/-- The inverse image along `G ⊆ X'` of multiplication by the function `a` is multiplication by
the function `a`. -/
theorem modulePullback_map_globalSmul_familyBaseFunction (a : P.base)
    (M : Space.Modules.{u, u} B (Spec (.of Λ)) hΛ P.space P.algebraic) :
    (modulePullback B (Spec (.of Λ)) hΛ (subspaceInclusion B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec P) (spaceSpecialSubspace B hΛ hSpec P f))).map
        (globalSmul _ (familyBaseFunction B hΛ hSpec P a) M) =
      globalSmul _ (familySpecialBaseFunction B hΛ hSpec P f a) _ :=
  modulePullback_map_globalSmul_of_chartDiagramPullback B (Spec (.of Λ)) hΛ
    (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
      (spaceSpecialSubspace B hΛ hSpec P f))
    (familyBaseFunction B hΛ hSpec P a) (familySpecialBaseFunction B hΛ hSpec P f a)
    (fun d => chartDiagramPullback_pullbackToGlobalFunctions B (Spec (.of Λ)) hΛ
      (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (spaceSpecialSubspace B hΛ hSpec P f))
      (spaceBaseOver B hΛ hSpec P.base) (spaceTotalToBase B hΛ hSpec P)
      ((Scheme.ΓSpecIso (CommRingCat.of P.base)).inv.hom a) d) M

/-- The element `1` of the base ring gives the function `1` on the special fibre. -/
theorem familySpecialBaseFunction_one : familySpecialBaseFunction B hΛ hSpec P f 1 = 1 := by
  rw [familySpecialBaseFunction, map_one, map_one]
  rfl

/-- Multiplication by the function `1` on the special fibre is the identity. -/
theorem globalSmul_familySpecialBaseFunction_one
    (M : Space.Modules.{u, u} B (Spec (.of Λ)) hΛ (spaceSpecialSpace B hΛ hSpec P f).1
      (spaceSpecialSpace B hΛ hSpec P f).2) :
    globalSmul _ (familySpecialBaseFunction B hΛ hSpec P f 1) M = 𝟙 M := by
  rw [familySpecialBaseFunction_one]
  exact globalSmul_one _ M

/-- **Multiplication by an element of the base ring on the conormal module of the special
fibre**: multiplication by its pullback to the special fibre. -/
def familySpecialConormalSmul (a : P.base) :
    conormalModule B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (spaceSpecialSubspace B hΛ hSpec P f) ⟶
      conormalModule B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (spaceSpecialSubspace B hΛ hSpec P f) :=
  globalSmul _ (familySpecialBaseFunction B hΛ hSpec P f a) _

/-- The inverse image along the identity of multiplication by an element of the base ring is
multiplication by it. -/
theorem modulePullback_id_map_familySpecialConormalSmul (a : P.base) :
    (modulePullback B (Spec (.of Λ)) hΛ (𝟙 (spaceSpecialSpace B hΛ hSpec P f))).map
        (familySpecialConormalSmul B hΛ hSpec P f a) =
      globalSmul _ (familySpecialBaseFunction B hΛ hSpec P f a) _ :=
  modulePullback_map_globalSmul_of_chartDiagramPullback B (Spec (.of Λ)) hΛ
    (𝟙 (spaceSpecialSpace B hΛ hSpec P f))
    (familySpecialBaseFunction B hΛ hSpec P f a) (familySpecialBaseFunction B hΛ hSpec P f a)
    (fun d => (chartDiagramPullback_pullbackToGlobalFunctions B (Spec (.of Λ)) hΛ
      (𝟙 (spaceSpecialSpace B hΛ hSpec P f)) (spaceBaseOver B hΛ hSpec P.base)
      (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (spaceSpecialSubspace B hΛ hSpec P f) ≫ spaceTotalToBase B hΛ hSpec P)
      ((Scheme.ΓSpecIso (CommRingCat.of P.base)).inv.hom a) d).trans
      (congrArg (fun g => (pullbackToGlobalFunctions B (Spec (.of Λ)) hΛ
        (spaceSpecialSpace B hΛ hSpec P f) (spaceBaseOver B hΛ hSpec P.base) g
        ((Scheme.ΓSpecIso (CommRingCat.of P.base)).inv.hom a)).1 (op d.U))
        (Category.id_comp _)))
    (conormalModule B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
      (spaceSpecialSubspace B hΛ hSpec P f))

variable (εA : P.base) (hk : RingHom.ker f.hom.toRingHom = Ideal.span {εA})

section Conormal

attribute [local irreducible] modulePullback

/-- **The conormal map of a self-map over a rescaling, after the identification
`i^*𝒪_{X'} ≅ 𝒞_{G/X'}`.**  For `J` over `Spec σ` with `σ(ε) = c ε` and restricting to the identity
of `G`, the conormal map of `(J, 𝟙_G)` after `𝟙^*i^*(ε·)` is the comparison of the square on the
structure sheaf, then multiplication by the function `c` on `G`, then `i^*(ε·)`. -/
theorem modulePullback_map_specialEpsilonMul_comp_conormalMap
    {σ : P.base ⟶ P.base}
    {J : spaceTotalSpace B hΛ hSpec P ⟶ spaceTotalSpace B hΛ hSpec P}
    (hJ : J ≫ spaceTotalToBase B hΛ hSpec P =
      spaceTotalToBase B hΛ hSpec P ≫ schemeSpaceMap (spaceBaseOverMap B hΛ hSpec σ))
    (c : P.base) (hσ : σ.hom εA = c * εA)
    (hsq : subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (spaceSpecialSubspace B hΛ hSpec P f) ≫ J =
      𝟙 (spaceSpecialSpace B hΛ hSpec P f) ≫ subspaceInclusion B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec P) (spaceSpecialSubspace B hΛ hSpec P f)) :
    (modulePullback B (Spec (.of Λ)) hΛ (𝟙 (spaceSpecialSpace B hΛ hSpec P f))).map
        ((modulePullback B (Spec (.of Λ)) hΛ (subspaceInclusion B (Spec (.of Λ)) hΛ
          (spaceTotalSpace B hΛ hSpec P) (spaceSpecialSubspace B hΛ hSpec P f))).map
          (specialEpsilonMul B hΛ hSpec P f εA hk)) ≫
        conormalMap B (Spec (.of Λ)) hΛ (spaceSpecialSubspace B hΛ hSpec P f)
          (spaceSpecialSubspace B hΛ hSpec P f) J (𝟙 _) hsq =
      ((conormalPullbackCompIso B (Spec (.of Λ)) hΛ (spaceSpecialSubspace B hΛ hSpec P f)
          (spaceSpecialSubspace B hΛ hSpec P f) J (𝟙 _) hsq).hom.app
          (SheafOfModules.unit (structureRingSheaf B (Spec (.of Λ)) hΛ
            (spaceTotalSpace B hΛ hSpec P))) ≫
        (modulePullback B (Spec (.of Λ)) hΛ (subspaceInclusion B (Spec (.of Λ)) hΛ
          (spaceTotalSpace B hΛ hSpec P) (spaceSpecialSubspace B hΛ hSpec P f))).map
          (modulePullbackUnitIso B (Spec (.of Λ)) hΛ J).hom) ≫
        globalSmul _ (familySpecialBaseFunction B hΛ hSpec P f c) _ ≫
        (modulePullback B (Spec (.of Λ)) hΛ (subspaceInclusion B (Spec (.of Λ)) hΛ
          (spaceTotalSpace B hΛ hSpec P) (spaceSpecialSubspace B hΛ hSpec P f))).map
          (specialEpsilonMul B hΛ hSpec P f εA hk) := by
  let iP := modulePullback B (Spec (.of Λ)) hΛ (subspaceInclusion B (Spec (.of Λ)) hΛ
    (spaceTotalSpace B hΛ hSpec P) (spaceSpecialSubspace B hΛ hSpec P f))
  let ε := specialEpsilonMul B hΛ hSpec P f εA hk
  let cmp := conormalPullbackCompIso B (Spec (.of Λ)) hΛ (spaceSpecialSubspace B hΛ hSpec P f)
    (spaceSpecialSubspace B hΛ hSpec P f) J (𝟙 _) hsq
  let I := idealSheafMap B (Spec (.of Λ)) hΛ (spaceSpecialSubspace B hΛ hSpec P f)
    (spaceSpecialSubspace B hΛ hSpec P f) J (𝟙 _) hsq
  let A0 := (modulePullback B (Spec (.of Λ)) hΛ (𝟙 (spaceSpecialSpace B hΛ hSpec P f))).map
    (iP.map ε)
  let CI := cmp.hom.app (definingIdealSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
    (spaceSpecialSubspace B hΛ hSpec P f)).toSheafOfModules
  let CO := cmp.hom.app (SheafOfModules.unit (structureRingSheaf B (Spec (.of Λ)) hΛ
    (spaceTotalSpace B hΛ hSpec P)))
  let PJ := iP.map ((modulePullback B (Spec (.of Λ)) hΛ J).map ε)
  let U := iP.map (modulePullbackUnitIso B (Spec (.of Λ)) hΛ J).hom
  let GS := globalSmul _ (familySpecialBaseFunction B hΛ hSpec P f c)
    (iP.obj (SheafOfModules.unit (structureRingSheaf B (Spec (.of Λ)) hΛ
      (spaceTotalSpace B hΛ hSpec P))))
  let GX := globalSmul _ (familyBaseFunction B hΛ hSpec P c)
    (SheafOfModules.unit (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)))
  have hnat : A0 ≫ CI = CO ≫ PJ := cmp.hom.naturality ε
  have h2 : (modulePullback B (Spec (.of Λ)) hΛ J).map ε ≫ I =
      (modulePullbackUnitIso B (Spec (.of Λ)) hΛ J).hom ≫ GX ≫ ε :=
    modulePullback_map_specialEpsilonMul_comp_idealSheafMap B hΛ hSpec P hJ f εA hk c hσ
      (𝟙 _) hsq
  have h3 : iP.map GX = GS := modulePullback_map_globalSmul_familyBaseFunction B hΛ hSpec P f c
    (SheafOfModules.unit (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)))
  have h2' : PJ ≫ iP.map I = U ≫ GS ≫ iP.map ε :=
    (iP.map_comp ((modulePullback B (Spec (.of Λ)) hΛ J).map ε) I).symm.trans
      ((congrArg iP.map h2).trans
        ((iP.map_comp (modulePullbackUnitIso B (Spec (.of Λ)) hΛ J).hom (GX ≫ ε)).trans
          (congrArg (U ≫ ·) ((iP.map_comp GX ε).trans (congrArg (· ≫ iP.map ε) h3)))))
  exact (Category.assoc A0 CI (iP.map I)).symm.trans ((congrArg (· ≫ iP.map I) hnat).trans
    ((Category.assoc CO PJ (iP.map I)).trans ((congrArg (CO ≫ ·) h2').trans
      (Category.assoc CO U (GS ≫ iP.map ε)).symm)))

/-- The identity of the total space lies over the identity of the base. -/
theorem id_comp_spaceTotalToBase_eq :
    𝟙 (spaceTotalSpace B hΛ hSpec P) ≫ spaceTotalToBase B hΛ hSpec P =
      spaceTotalToBase B hΛ hSpec P ≫ schemeSpaceMap (spaceBaseOverMap B hΛ hSpec (𝟙 P.base)) := by
  rw [spaceBaseOverMap_id, Category.id_comp]
  apply ObjectProperty.hom_ext
  show P.toBase = P.toBase ≫ yoneda.map (𝟙 _)
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

variable (hann : ∀ a : P.base, εA * a = 0 ↔ a ∈ Ideal.span {εA})
  (hG : IsFirstOrderThickening B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
      (spaceSpecialSubspace B hΛ hSpec P f).1)

include hk hann hG in
/-- **The conormal map of a self-map of the total space over a rescaling `ε ↦ c ε` of the base,
restricting to the identity of the special fibre, is the conormal map of the identity followed by
multiplication by the function `c`.** -/
theorem conormalMap_spaceSpecialSubspace_eq_comp_globalSmul
    {σ : P.base ⟶ P.base}
    {J : spaceTotalSpace B hΛ hSpec P ⟶ spaceTotalSpace B hΛ hSpec P}
    (hJ : J ≫ spaceTotalToBase B hΛ hSpec P =
      spaceTotalToBase B hΛ hSpec P ≫ schemeSpaceMap (spaceBaseOverMap B hΛ hSpec σ))
    (c : P.base) (hσ : σ.hom εA = c * εA)
    (hsq : subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (spaceSpecialSubspace B hΛ hSpec P f) ≫ J =
      𝟙 (spaceSpecialSpace B hΛ hSpec P f) ≫ subspaceInclusion B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec P) (spaceSpecialSubspace B hΛ hSpec P f))
    (hid : subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (spaceSpecialSubspace B hΛ hSpec P f) ≫ 𝟙 _ =
      𝟙 (spaceSpecialSpace B hΛ hSpec P f) ≫ subspaceInclusion B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec P) (spaceSpecialSubspace B hΛ hSpec P f)) :
    conormalMap B (Spec (.of Λ)) hΛ (spaceSpecialSubspace B hΛ hSpec P f)
        (spaceSpecialSubspace B hΛ hSpec P f) J (𝟙 _) hsq =
      globalSmul _ (familySpecialBaseFunction B hΛ hSpec P f c) _ ≫
        conormalMap B (Spec (.of Λ)) hΛ (spaceSpecialSubspace B hΛ hSpec P f)
          (spaceSpecialSubspace B hΛ hSpec P f) (𝟙 _) (𝟙 _) hid := by
  let iP := modulePullback B (Spec (.of Λ)) hΛ (subspaceInclusion B (Spec (.of Λ)) hΛ
    (spaceTotalSpace B hΛ hSpec P) (spaceSpecialSubspace B hΛ hSpec P f))
  let ε := specialEpsilonMul B hΛ hSpec P f εA hk
  let E := iP.map ε
  have hE : IsIso E := isIso_modulePullback_map_of_isColimit B (Spec (.of Λ)) hΛ ε
    (definingIdealSheaf_ι_comp_specialEpsilonMul B hΛ hSpec P f εA hk hG)
    (isColimitSpecialEpsilonMul B hΛ hSpec P f εA hk hann hG)
  let A0 := (modulePullback B (Spec (.of Λ)) hΛ (𝟙 (spaceSpecialSpace B hΛ hSpec P f))).map E
  have hA0 : IsIso A0 := by
    have := hE
    exact Functor.map_isIso
      (modulePullback B (Spec (.of Λ)) hΛ (𝟙 (spaceSpecialSpace B hΛ hSpec P f))) E
  have hA0e : Epi A0 := @IsIso.epi_of_iso _ _ _ _ A0 hA0
  refine (@cancel_epi _ _ _ _ _ A0 hA0e _ _).1 ?_
  have hJe := modulePullback_map_specialEpsilonMul_comp_conormalMap B hΛ hSpec P f εA hk hJ c hσ hsq
  have h1e := modulePullback_map_specialEpsilonMul_comp_conormalMap B hΛ hSpec P f εA hk
    (id_comp_spaceTotalToBase_eq B hΛ hSpec P) 1 (one_mul εA).symm hid
  have hcJ := conormalPullbackCompIso_hom_app_unit_comp B (Spec (.of Λ)) hΛ
    (spaceSpecialSubspace B hΛ hSpec P f) (spaceSpecialSubspace B hΛ hSpec P f) J (𝟙 _) hsq
  have hc1 := conormalPullbackCompIso_hom_app_unit_comp B (Spec (.of Λ)) hΛ
    (spaceSpecialSubspace B hΛ hSpec P f) (spaceSpecialSubspace B hΛ hSpec P f) (𝟙 _) (𝟙 _) hid
  let ui := modulePullbackUnitIso B (Spec (.of Λ)) hΛ (subspaceInclusion B (Spec (.of Λ)) hΛ
    (spaceTotalSpace B hΛ hSpec P) (spaceSpecialSubspace B hΛ hSpec P f))
  have hmono : Mono ui.hom := @IsIso.mono_of_iso _ _ _ _ ui.hom (Iso.isIso_hom ui)
  have hX := (@cancel_mono _ _ _ _ _ ui.hom hmono _ _).1
    (((Category.assoc _ _ _).trans (hcJ.trans hc1.symm)).trans (Category.assoc _ _ _).symm)
  rw [globalSmul_familySpecialBaseFunction_one, Category.id_comp] at h1e
  have eA := comp_globalSmul (structureRingSheaf B (Spec (.of Λ)) hΛ
    (spaceSpecialSpace B hΛ hSpec P f)) (familySpecialBaseFunction B hΛ hSpec P f c) A0
  refine hJe.trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ E) (comp_globalSmul _ _ _)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  rw [hX]
  exact (congrArg (fun m => globalSmul _ (familySpecialBaseFunction B hΛ hSpec P f c) _ ≫ m)
    h1e.symm).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ conormalMap B (Spec (.of Λ)) hΛ (spaceSpecialSubspace B hΛ hSpec P f)
          (spaceSpecialSubspace B hΛ hSpec P f) (𝟙 _) (𝟙 _) hid) eA.symm).trans
        (Category.assoc _ _ _)))

include hk hann hG in
/-- **The conormal map of a self-map over a rescaling `ε ↦ c ε`** is the inverse image along the
identity of multiplication by `c` on `𝒞_{G/X'}`, followed by the conormal map of the identity. -/
theorem conormalMap_spaceSpecialSubspace_eq_map_familySpecialConormalSmul
    {σ : P.base ⟶ P.base}
    {J : spaceTotalSpace B hΛ hSpec P ⟶ spaceTotalSpace B hΛ hSpec P}
    (hJ : J ≫ spaceTotalToBase B hΛ hSpec P =
      spaceTotalToBase B hΛ hSpec P ≫ schemeSpaceMap (spaceBaseOverMap B hΛ hSpec σ))
    (c : P.base) (hσ : σ.hom εA = c * εA)
    (hsq : subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (spaceSpecialSubspace B hΛ hSpec P f) ≫ J =
      𝟙 (spaceSpecialSpace B hΛ hSpec P f) ≫ subspaceInclusion B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec P) (spaceSpecialSubspace B hΛ hSpec P f))
    (hid : subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (spaceSpecialSubspace B hΛ hSpec P f) ≫ 𝟙 _ =
      𝟙 (spaceSpecialSpace B hΛ hSpec P f) ≫ subspaceInclusion B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec P) (spaceSpecialSubspace B hΛ hSpec P f)) :
    conormalMap B (Spec (.of Λ)) hΛ (spaceSpecialSubspace B hΛ hSpec P f)
        (spaceSpecialSubspace B hΛ hSpec P f) J (𝟙 _) hsq =
      (modulePullback B (Spec (.of Λ)) hΛ (𝟙 (spaceSpecialSpace B hΛ hSpec P f))).map
          (familySpecialConormalSmul B hΛ hSpec P f c) ≫
        conormalMap B (Spec (.of Λ)) hΛ (spaceSpecialSubspace B hΛ hSpec P f)
          (spaceSpecialSubspace B hΛ hSpec P f) (𝟙 _) (𝟙 _) hid := by
  rw [modulePullback_id_map_familySpecialConormalSmul]
  exact conormalMap_spaceSpecialSubspace_eq_comp_globalSmul B hΛ hSpec P f εA hk hann hG hJ c hσ
    hsq hid

end Conormal

end Deformation.Examples

end
