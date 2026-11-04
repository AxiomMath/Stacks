module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.FlatCoverCriteria
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.FlatPullbackUnit

/-!
# Objects of `D_QCoh` that are trivial after two flat pullbacks with covering images

Let `g₁ : Z₁ ⟶ X` and `g₂ : Z₂ ⟶ X` be flat morphisms whose images cover `X`, and let
`K ∈ D_QCoh(𝒪_X)` with `Lg_i^*K ≅ 𝒪_{Z_i}[0]`. Then `K` is concentrated in degree zero: `K ≅ L[0]`
for a quasi-coherent `L` with `g_i^*L ≅ 𝒪_{Z_i}` (flat pullback commutes with cohomology, and a
module vanishing after both pullbacks is zero). This is the third step of the stage lemma in the
proof of the second sentence of [Stacks, Tag 0EA2].

## Main results

* `AlgebraicGeometry.DualizingDivisor.exists_iso_singleQuasiCoherent_of_pullback_iso`
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public section

open CategoryTheory Limits Stacks.Duality

universe u

namespace AlgebraicGeometry.DualizingDivisor

variable {X Z₁ Z₂ : Scheme.{u}} (g₁ : Z₁ ⟶ X) (g₂ : Z₂ ⟶ X) [Flat g₁] [Flat g₂]

/-- The cohomology sheaves of `Lg^*K` are those of `𝒪_Z[0]` when `Lg^*K ≅ 𝒪_Z[0]`, read as
`g^*H^i(K)`. -/
noncomputable def pullbackHomologyIsoOfIso {Z : Scheme.{u}} (g : Z ⟶ X) [Flat g]
    (K : quasiCoherentDerivedCategory X) (e : (quasiCoherentDerivedPullback' g).obj K ≅ unitQC Z)
    (i : ℤ) :
    (Scheme.Modules.pullback g).obj ((DerivedCategory.homologyFunctor X.Modules i).obj K.obj) ≅
      (DerivedCategory.homologyFunctor Z.Modules i).obj
        ((DerivedCategory.singleFunctor Z.Modules 0).obj (SheafOfModules.unit Z.ringCatSheaf)) :=
  (homologyQuasiCoherentDerivedPullbackIso g K i).symm ≪≫
    (DerivedCategory.homologyFunctor Z.Modules i).mapIso ((ObjectProperty.ι _).mapIso e)

/-- **An object of `D_QCoh(𝒪_X)` trivial after two flat pullbacks with covering images is a
module in degree zero**, and that module is trivial after both pullbacks. -/
theorem exists_iso_singleQuasiCoherent_of_pullback_iso
    (hcov : ∀ x : X, x ∈ Set.range g₁ ∨ x ∈ Set.range g₂) (K : quasiCoherentDerivedCategory X)
    (e₁ : (quasiCoherentDerivedPullback' g₁).obj K ≅ unitQC Z₁)
    (e₂ : (quasiCoherentDerivedPullback' g₂).obj K ≅ unitQC Z₂) :
    ∃ (L : X.Modules) (hL : L.IsQuasicoherent),
      Nonempty (K ≅ singleQuasiCoherent L hL 0) ∧
      Nonempty ((Scheme.Modules.pullback g₁).obj L ≅ SheafOfModules.unit Z₁.ringCatSheaf) ∧
      Nonempty ((Scheme.Modules.pullback g₂).obj L ≅ SheafOfModules.unit Z₂.ringCatSheaf) := by
  have hz : ∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K.obj) := by
    intro i hi
    have hs : ∀ (Z : Scheme.{u}), IsZero ((DerivedCategory.homologyFunctor Z.Modules i).obj
        ((DerivedCategory.singleFunctor Z.Modules 0).obj (Scheme.unitModule Z))) :=
      fun Z => by
        rcases hi.lt_or_gt with h | h
        · exact DerivedCategory.isZero_of_isGE _ 0 i h
        · exact DerivedCategory.isZero_of_isLE _ 0 i h
    exact isZero_of_isZero_pullback_of_cover g₁ g₂ hcov
      ((hs Z₁).of_iso (pullbackHomologyIsoOfIso g₁ K e₁ i))
      ((hs Z₂).of_iso (pullbackHomologyIsoOfIso g₂ K e₂ i))
  have : K.obj.IsGE 0 := (DerivedCategory.isGE_iff _ _).2 fun i hi => hz i hi.ne
  have : K.obj.IsLE 0 := (DerivedCategory.isLE_iff _ _).2 fun i hi => hz i hi.ne'
  obtain ⟨Y, ⟨φ⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K.obj 0
  let ψ : Y ≅ (DerivedCategory.homologyFunctor X.Modules 0).obj K.obj :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app Y).symm ≪≫
      (DerivedCategory.homologyFunctor X.Modules 0).mapIso φ.symm
  have hY : Y.IsQuasicoherent := (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso ψ.symm
    (K.property 0)
  let pu : ∀ {Z : Scheme.{u}} (g : Z ⟶ X) [Flat g],
      ((quasiCoherentDerivedPullback' g).obj K ≅ unitQC Z) →
      ((Scheme.Modules.pullback g).obj Y ≅ SheafOfModules.unit Z.ringCatSheaf) :=
    fun {Z} g _ e => (Scheme.Modules.pullback g).mapIso ψ ≪≫ pullbackHomologyIsoOfIso g K e 0 ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso Z.Modules 0).app _
  exact ⟨Y, hY, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso φ⟩, ⟨pu g₁ e₁⟩, ⟨pu g₂ e₂⟩⟩

end AlgebraicGeometry.DualizingDivisor

end
