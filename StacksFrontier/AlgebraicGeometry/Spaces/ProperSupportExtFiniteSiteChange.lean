module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSupportExtFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteChangeTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalizeSiteChange
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType

/-!
# Ext and Hom of a coherent module with proper support over a test scheme which is a field

Let `X` be an algebraic space over `S` with a morphism `p : X ⟶ T` locally of finite type to an
object `T` of the big fppf site whose scheme is `Spec k` for a field `k`, and let `G` be a coherent
`𝒪_X`-module whose support is proper over `T`. Then `Hom(G, G)` and `Ext¹(G, G)` are
finite-dimensional over `k`, for the `k`-linear structure in which `c ∈ k` acts by its pullback
along `p`.

Read through the change of base site of Stacks 04SG, `X` is an algebraic space `X'` over `Spec k`,
`G` is a coherent module on `X'` with support proper over `Spec k` (Stacks 0CZD), and the
equivalence of module categories is `k`-linear; so this is
`AlgebraicGeometry.Space.finiteDimensional_ext_one_and_hom_of_hasProperSupport` on `X'`.

## Main results

* `AlgebraicGeometry.Space.baseRingHom_eq_targetScalars`: the scalars from the base `Spec k` are
  the pullbacks of functions along the structure morphism.
* `AlgebraicGeometry.Space.finiteDimensional_ext_one_and_hom_of_hasProperSupport_of_toScheme_eq`:
  `Hom(G, G)` and `Ext¹(G, G)` are finite-dimensional over `k` when `T` is `Spec k`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Abelian

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology modulesLinear

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

/-- **The scalars from the base `Spec k` are the pullbacks of functions along the structure
morphism.** -/
theorem baseRingHom_eq_targetScalars (X : AlgebraicSpaces B (Spec (.of k)) hk)
    (f : X ⟶ schemeSpace (baseTerminal B (Spec (.of k)) hk)) (c : k) :
    baseRingHom k B hk X.1 X.2 c =
      targetScalars B (Spec (.of k)) hk f ((Scheme.ΓSpecIso (.of k)).inv c) := by
  refine Subtype.ext (funext fun U => ?_)
  have h2 : (chartToTarget B (Spec (.of k)) hk f U.unop).left = U.unop.1.left.hom := by
    simpa using Over.w (chartToTarget B (Spec (.of k)) hk f U.unop)
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ Scheme.Γ.map ((B.inclusion.map
      ((SmallEtale.toOver B (Spec (.of k)) hk X.1).obj U.unop).hom).op)).hom c =
    ((B.inclusion.map (chartToTarget B (Spec (.of k)) hk f U.unop).left).appTop).hom
      ((Scheme.ΓSpecIso (.of k)).inv c)
  rw [h2]
  rfl

variable {k B} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An algebraic space locally of finite type over a test scheme which is the spectrum of a
Noetherian ring is locally Noetherian.** -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_toScheme_eq {R : Type u} [CommRing R]
    [IsNoetherianRing R]
    (X : AlgebraicSpaces B S hS) {T : BigFppfOver B S hS} (p : X ⟶ schemeSpace T)
    (hp : IsLocallyOfFiniteType B S hS p.hom)
    (e : (BigFppfOver.toScheme B S hS).obj T = Spec (.of R)) :
    HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V) :=
  isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2 (schemeSpace T).2 p.hom hp
    ((exists_atlas_iff_of_representable B S hS _ (fun V : Scheme.{u} => IsLocallyNoetherian V) T
      (Iso.refl _)).2 (by
        rw [e]
        exact (AlgebraicGeometry.isLocallyNoetherian_Spec (R := .of R)).2 inferInstance))

/-- **Hom and Ext¹ of a coherent module with support proper over a test scheme which is the
spectrum of a field are finite-dimensional over the field**, for the `k`-linear structure given
by `ψ`, the pullback of functions along `p`. -/
theorem finiteDimensional_ext_one_and_hom_of_hasProperSupport_of_toScheme_eq
    (X : AlgebraicSpaces B S hS) {T : BigFppfOver B S hS} (p : X ⟶ schemeSpace T)
    (hp : IsLocallyOfFiniteType B S hS p.hom)
    (e : (BigFppfOver.toScheme B S hS).obj T = Spec (.of k))
    (ψ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (hψ : ∀ c, ψ c = targetScalars B S hS p (((Scheme.ΓSpecIso (.of k)).inv ≫
      (eqToHom e).appTop).hom c))
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : IsCoherent B S hS X.1 X.2 G)
    (hsupp : HasProperSupport B S hS X.2 (schemeSpace T).2 p.hom hp
      ((SheafOfModules.toSheaf _).obj G)) :
    letI : HasExt.{u + 1} (Modules.{u, u} B S hS X.1 X.2) := HasExt.standard _
    letI := Stacks.SheafOfModules.linearOver _ ψ
    FiniteDimensional k (Ext G G 1) ∧ FiniteDimensional k (G ⟶ G) := by
  obtain ⟨⟨Tk, hTk⟩, ⟨⟨⟩⟩, h⟩ := T
  change Tk = Spec (.of k) at e
  subst e
  have hψ' : ∀ c, ψ c = targetScalars B S hS p ((Scheme.ΓSpecIso (.of k)).inv c) := fun c =>
    (hψ c).trans (by rw [eqToHom_refl]; rfl)
  let π : X ⟶ schemeSpace (Over.mk (show B.obj hTk ⟶ B.obj hS from h)) := p
  have : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_toScheme_eq X p hp rfl⟩
  let f' := siteChangeStructure X π
  have hf' := (isLocallyOfFiniteType_siteChangeStructure_iff X π).2 hp
  let Ψ := siteChangeModules B X π
  have hGc' := (isCoherent_siteChangeModules_iff X π G).2 hG
  have hqc : G.IsQuasicoherentOnSite := hG.toIsQuasicoherentOnSite
  have := hG.toIsCoherentOnSite
  have hft := isFiniteTypeOnSite_of_isCoherentOnSite B S hS X G
  have hsupp' := (hasProperSupport_siteChangeModules_iff X π hp G hqc hft).2 hsupp
  obtain ⟨h₁, h₀⟩ := finiteDimensional_ext_one_and_hom_of_hasProperSupport k B hTk f' hf'
    (Ψ.obj G) hGc' hsupp'
  let : HasExt.{u + 1} (Modules.{u, u} B S hS X.1 X.2) := HasExt.standard _
  let : HasExt.{u + 1} (Modules.{u, u} B (Spec (.of k)) hTk (siteChangeSpace B X π).1
    (siteChangeSpace B X π).2) := HasExt.standard _
  let := Stacks.SheafOfModules.linearOver _ ψ
  have : Ψ.Additive := Functor.additive_of_preserves_binary_products Ψ
  have hΨ : Ψ.Linear k := Stacks.SheafOfModules.linear_of_map_globalSmul ψ
    (baseRingHom k B hTk (siteChangeSpace B X π).1 (siteChangeSpace B X π).2) Ψ fun c M => by
      rw [hψ' c, baseRingHom_eq_targetScalars k B hTk (siteChangeSpace B X π) f' c]
      exact siteChangeModules_map_globalSmul B X π f' _ M
  refine ⟨?_, ?_⟩
  · let E := Ψ.asEquivalence
    let L := E.inverse
    have : E.functor.Linear k := hΨ
    have : L.Additive := Functor.additive_of_preserves_binary_products L
    have hsurj : Function.Surjective (Deformation.ModuleDeformation.extTransfer (k := k) L
        (E.unitIso.app G).symm (E.unitIso.app G).symm 1) := by
      intro x
      obtain ⟨E', ι, q, w, hS', rfl⟩ :=
        (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum _ G G).1 x
      exact Deformation.ModuleDeformation.extClass_mem_range_extTransfer L hS'
        (E.unitIso.app G).symm (E.unitIso.app E').symm (E.unitIso.app G).symm
    have : Module.Finite k (Ext (E.functor.obj G) (E.functor.obj G) 1) := h₁
    exact Module.Finite.of_surjective _ hsurj
  · exact FiniteDimensional.of_injective (Ψ.mapLinearMap k (X := G) (Y := G))
      fun a b hab => Ψ.map_injective hab

end AlgebraicGeometry.Space

end
