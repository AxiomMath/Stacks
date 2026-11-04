module

public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerFibreSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeBLinear
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangePushforwardTensorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated

/-!
# The twisted Euler characteristic is constant along morphisms of `Coh_{X/B}`

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation, `L` an invertible
`𝒪_X`-module and `m : (T, 𝓕) ⟶ (T', 𝓕')` a morphism of `Coh_{X/B}` lying over `h : T ⟶ T'`.  For
every point `t ∈ T` and every `n ∈ ℤ`,

`χ(X_t, 𝓕_t ⊗ L_t^{⊗ n}) = χ(X_{h(t)}, 𝓕'_{h(t)} ⊗ L_{h(t)}^{⊗ n})`.

## Main definitions

* `AlgebraicGeometry.Space.CoherentHom.fibreBaseChangeDiagram`: the cartesian square
  `X_t ⟶ X_{h(t)}` over `Spec κ(t) ⟶ Spec κ(h(t))` of a morphism of `Coh_{X/B}`, as data of
  Stacks 073J.

## Main results

* `AlgebraicGeometry.Space.BaseChangeDiagram.finrank_affineCohomologyTarget_eq`: **flat base
  change preserves the dimensions of cohomology along a field extension**: if the two bases of
  the cartesian square of Stacks 073J are the spectra of fields, then
  `dim_K Hⁱ(X', 𝓕') = dim_k Hⁱ(X, 𝓕)`.
* `AlgebraicGeometry.Space.globalSectionsRingHom_eq_comp_baseChartBaseRingHom`: the ring map
  `Γ(V, 𝒪_V) ⟶ Γ(F, 𝒪_F)` of a morphism to a scheme is pullback of global functions along it,
  read through the identity chart of the scheme.
* `AlgebraicGeometry.Space.CoherentHom.twistedEuler_eq`: **the twisted Euler characteristic of
  an object of `Coh_{X/B}` at `t` is the one of its target under a morphism at `h(t)`.**

## References

* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TensorProduct Stacks.Cohomology.SiteModules
open Stacks.SheafOfModules.Tensor (ringSheaf)

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

/-- Dimensions over a ring do not change when the ring is replaced by an isomorphic one: for a
ring isomorphism `e : k ≃ K` and a ring map `φ : K ⟶ R`, an `R`-module has the same dimension
over `k` through `φ ∘ e` as over `K` through `φ`. -/
theorem ModuleCat.finrank_restrictScalars_comp_ringEquiv {k K R : Type*} [CommRing k]
    [CommRing K] [Ring R] (e : k ≃+* K) (φ : K →+* R) (N : ModuleCat R) :
    Module.finrank k ((ModuleCat.restrictScalars (φ.comp e.toRingHom)).obj N) =
      Module.finrank K ((ModuleCat.restrictScalars φ).obj N) :=
  congrArg Cardinal.toNat
    (rank_eq_of_equiv_equiv (M := (ModuleCat.restrictScalars (φ.comp e.toRingHom)).obj N)
      (M₁ := (ModuleCat.restrictScalars φ).obj N) e (AddEquiv.refl _) e.bijective
      (fun _ _ => rfl))

/-- Restricting scalars twice is restricting scalars along the composite, so dimensions over
the source ring agree. -/
theorem ModuleCat.finrank_restrictScalars_restrictScalars {k K R : Type*} [CommRing k]
    [Ring K] [Ring R] (ψ : k →+* K) (φ : K →+* R) (N : ModuleCat R) :
    Module.finrank k ((ModuleCat.restrictScalars ψ).obj ((ModuleCat.restrictScalars φ).obj N)) =
      Module.finrank k ((ModuleCat.restrictScalars (φ.comp ψ)).obj N) :=
  LinearEquiv.finrank_eq
    { toFun := fun x => x
      invFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Flat base change of dimensions along a field extension -/

namespace BaseChangeDiagram

/-- **Flat base change preserves the dimensions of cohomology along a field extension.**  For
the cartesian square of Stacks 073J with `g` flat, `f` quasi-compact and quasi-separated, and the
two bases affine with coordinate rings `A` and `B` which are fields, the cohomology `Hⁱ(X', 𝓕')`
has the same dimension over `B` as `Hⁱ(X, 𝓕)` over `A`. -/
theorem finrank_affineCohomologyTarget_eq (D : BaseChangeDiagram B S hS)
    (hg : IsFlat B S hS D.g.hom) (hqc : IsQuasiCompact B S hS D.f.hom)
    (hqs : IsQuasiSeparated B S hS D.f.hom)
    (V₀ : SmallEtale B S hS D.Y.1) [IsIso V₀.obj.hom] [IsAffine (chartScheme V₀)]
    (V₀' : SmallEtale B S hS D.Y'.1) [IsIso V₀'.obj.hom] [IsAffine (chartScheme V₀')]
    (hA : IsField (baseChartRing B S hS D.Y V₀)) (hB : IsField (baseChartRing B S hS D.Y' V₀'))
    (i : ℕ) :
    Module.finrank (baseChartRing B S hS D.Y' V₀')
        ((baseChartRestrictScalars B S hS D.Y' (isTerminal_of_isIso_chart B S hS D.Y' V₀')).obj
          (D.affineCohomologyTarget i)) =
      Module.finrank (baseChartRing B S hS D.Y V₀) (D.affineCohomologyOverBaseChart V₀ i) := by
  let := baseChartAlgebra B S hS D.g V₀ V₀'
  let : Field (baseChartRing B S hS D.Y V₀) := hA.toField
  have : Nontrivial (baseChartRing B S hS D.Y' V₀') := ⟨hB.exists_pair_ne⟩
  rw [← LinearEquiv.finrank_eq (D.affineCohomologyBaseChangeIsoBase V₀ V₀'
    (BigFppfSite.contains_terminal B) hg hqc hqs i).toLinearEquiv]
  exact Module.finrank_baseChange

end BaseChangeDiagram

/-! ### The ring map of a morphism to a scheme, through the identity chart -/

section GlobalSections

/-- The identity chart of the algebraic space of a scheme `V`, the chart presenting it as the
scheme `V`. -/
def schemeSpaceSelfChart (V : BigFppfOver B S hS) :
    SmallEtale B S hS ((schemeSpaceFunctor B S hS).obj V).1 :=
  selfChart B S hS V

/-- The identity chart of the algebraic space of a scheme presents it as a scheme. -/
instance isIso_schemeSpaceSelfChart_hom (V : BigFppfOver B S hS) :
    IsIso (schemeSpaceSelfChart V).obj.hom :=
  inferInstanceAs (IsIso (𝟙 (yoneda.obj V)))

/-- The scheme of the identity chart of the algebraic space of a scheme `V` is `V`, so it is
affine when `V` is. -/
instance isAffine_chartScheme_schemeSpaceSelfChart (V : BigFppfOver B S hS)
    [h : IsAffine ((BigFppfOver.toScheme B S hS).obj V)] :
    IsAffine (chartScheme (schemeSpaceSelfChart V)) :=
  h

/-- **The ring map `Γ(V, 𝒪_V) ⟶ Γ(F, 𝒪_F)` of a morphism to a scheme, through the identity
chart.**  The ring map `AlgebraicGeometry.Space.globalSectionsRingHom` attached to a morphism
`φ : X ⟶ V` from an algebraic space to a scheme over `S` is the comparison of global function
rings of Stacks 0732 along `φ`, precomposed with the identification of the functions on `V` with
the global functions on the algebraic space of `V` given by its identity chart. -/
theorem globalSectionsRingHom_eq_comp_baseChartBaseRingHom (X : AlgebraicSpaces B S hS)
    (V : BigFppfOver B S hS) (φ : X ⟶ (schemeSpaceFunctor B S hS).obj V) :
    globalSectionsRingHom B S hS X.1 X.2 φ.hom =
      (globalSectionsRingHomSite B S hS φ).comp
        (baseChartBaseRingHom B S hS ((schemeSpaceFunctor B S hS).obj V)
          (isTerminal_of_isIso_chart B S hS _ (schemeSpaceSelfChart V))) := by
  ext a U
  have h := baseChartRingHom_apply B S hS φ
    (isTerminal_of_isIso_chart B S hS _ (schemeSpaceSelfChart V)) U.unop a
  have hc : ∀ W : SmallEtale B S hS X.1, chartToScheme B S hS X.1 φ.hom W =
      baseChartHom B S hS φ (schemeSpaceSelfChart V) W := by
    intro W
    apply yoneda.map_injective
    have e₂ : CategoryTheory.inv (schemeSpaceSelfChart V).obj.hom = 𝟙 _ := by
      change CategoryTheory.inv (𝟙 (yoneda.obj V)) = 𝟙 _
      simp
    have e₁ := yoneda_map_baseChartHom B S hS φ (schemeSpaceSelfChart V) W
    refine (Yoneda.fullyFaithful.map_preimage (W.obj.hom ≫ φ.hom)).trans (Eq.trans ?_ e₁.symm)
    rw [e₂]
    exact (Category.comp_id (W.obj.hom ≫ φ.hom)).symm.trans (Category.assoc _ _ _)
  change (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (chartToScheme B S hS X.1 φ.hom U.unop)).op).hom a = _
  rw [hc U.unop]
  exact h.symm

/-- **Dimensions over a field mapping to the global functions of a scheme.**  For a morphism
`φ : X ⟶ V` from an algebraic space to a scheme and a ring isomorphism `e : k ≃ Γ(V, 𝒪_V)`, a
`Γ(X, 𝒪_X)`-module has the same dimension over `k` through
`AlgebraicGeometry.Space.globalSectionsRingHom` as over `Γ(V, 𝒪_V)` through the comparison of
Stacks 0732 and the identity chart of `V`. -/
theorem finrank_restrictScalars_globalSectionsRingHom (X : AlgebraicSpaces B S hS)
    (V : BigFppfOver B S hS) (φ : X ⟶ (schemeSpaceFunctor B S hS).obj V) {k : Type u}
    [CommRing k] (e : k ≃+* Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (N : ModuleCat.{u + 1}
      (GlobalSectionRing (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) :
    Module.finrank k ((ModuleCat.restrictScalars
        ((globalSectionsRingHom B S hS X.1 X.2 φ.hom).comp e.toRingHom)).obj N) =
      Module.finrank (baseChartRing B S hS ((schemeSpaceFunctor B S hS).obj V)
          (schemeSpaceSelfChart V))
        ((baseChartRestrictScalars B S hS ((schemeSpaceFunctor B S hS).obj V)
          (isTerminal_of_isIso_chart B S hS _ (schemeSpaceSelfChart V))).obj
          ((globalSectionsRestrictScalars B S hS φ).obj N)) := by
  rw [globalSectionsRingHom_eq_comp_baseChartBaseRingHom]
  exact (ModuleCat.finrank_restrictScalars_comp_ringEquiv e _ N).trans
    (ModuleCat.finrank_restrictScalars_restrictScalars _ _ N).symm

end GlobalSections

/-! ### The twisted Euler characteristic along a morphism of `Coh_{X/B}` -/

namespace CoherentHom

variable {D : CoherentSituation B S hS} {A A' : CoherentObject D}

/-- The cartesian square `X_t ⟶ X_{h(t)}` over `Spec κ(t) ⟶ Spec κ(h(t))` of a morphism of
`Coh_{X/B}`, with the coefficient `𝓕'_{h(t)} ⊗ (L^{⊗ n})_{h(t)}` on `X_{h(t)}`, as data of
Stacks 073J. -/
def fibreBaseChangeDiagram (m : CoherentHom A A') (t : A.testScheme)
    (M : Modules.{u, u} B S hS D.X.1 D.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property M] :
    BaseChangeDiagram B S hS where
  X' := A.fibreSpace t
  X := A'.fibreSpace (m.baseScheme t)
  Y' := (schemeSpaceFunctor B S hS).obj (A.pointScheme t)
  Y := (schemeSpaceFunctor B S hS).obj (A'.pointScheme (m.baseScheme t))
  g' := m.fibreMap t
  f' := D.projection (A.pointTest t)
  f := D.projection (A'.pointTest (m.baseScheme t))
  g := (schemeSpaceFunctor B S hS).map (m.pointSchemeMap t)
  isPullback := m.isPullback_fibreMap t
  F := ((Stacks.SheafOfModules.Tensor.sheafTensor
    (smallEtaleRingedSite B S hS (A'.fibreSpace (m.baseScheme t)).1
      (A'.fibreSpace (m.baseScheme t)).2).O).obj
      (A'.fibreModule (m.baseScheme t))).obj
    ((modulePullback B S hS (baseChangeProjection D.f (A'.pointTest (m.baseScheme t)))).obj M)
  isQuasicoherent := A'.isQuasicoherentOnSite_fibreTwistedModule (m.baseScheme t) M

/-- **The twisted Euler characteristic is constant along morphisms of `Coh_{X/B}`.**  For a
morphism `m : (T, 𝓕) ⟶ (T', 𝓕')` of `Coh_{X/B}` over `h : T ⟶ T'`, an invertible `𝒪_X`-module
`L`, a point `t ∈ T` and `n ∈ ℤ`,
`χ(X_t, 𝓕_t ⊗ L_t^{⊗ n}) = χ(X_{h(t)}, 𝓕'_{h(t)} ⊗ L_{h(t)}^{⊗ n})`. -/
theorem twistedEuler_eq (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (m : CoherentHom A A') (t : A.testScheme) (n : ℤ) :
    CoherentObject.twistedEuler L A t n = CoherentObject.twistedEuler L A' (m.baseScheme t) n := by
  let E := m.fibreBaseChangeDiagram t (invertibleTensorPower B S hS D.X.1 D.X.2 L n)
  let e (T : Scheme.{u}) (x : T) :=
    (Scheme.ΓSpecIso (CommRingCat.of (T.residueField x))).commRingCatIsoToRingEquiv
  have hfld : ∀ (T : Scheme.{u}) (x : T), IsField Γ(Spec (CommRingCat.of (T.residueField x)), ⊤) :=
    fun T x => MulEquiv.isField (Field.toIsField (T.residueField x)) (e T x).toMulEquiv
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (A.pointScheme t)) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (A.testScheme.residueField t))))
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (A'.pointScheme (m.baseScheme t))) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of
      (A'.testScheme.residueField (m.baseScheme t)))))
  unfold CoherentObject.twistedEuler
  rw [eulerCharacteristicAlong_congr B S hS _ _ _ _ (m.fibreTwistedModuleIso t _),
    eulerCharacteristicAlong_eq_finsum_rightDerived,
    eulerCharacteristicAlong_eq_finsum_rightDerived]
  congr 1
  funext i
  congr 2
  have key := @BaseChangeDiagram.finrank_affineCohomologyTarget_eq _ _ _ E
    (m.isFlat_pointSchemeMap t) (D.isQuasiCompact_projection _) (D.isQuasiSeparated_projection _)
    (schemeSpaceSelfChart _) (isIso_schemeSpaceSelfChart_hom _)
    (isAffine_chartScheme_schemeSpaceSelfChart _)
    (schemeSpaceSelfChart _) (isIso_schemeSpaceSelfChart_hom _)
    (isAffine_chartScheme_schemeSpaceSelfChart _)
    (hfld A'.testScheme (m.baseScheme t)) (hfld A.testScheme t) i
  exact (finrank_restrictScalars_globalSectionsRingHom E.X' (A.pointScheme t) E.f'
      (e A.testScheme t).symm _).trans
    (key.trans (finrank_restrictScalars_globalSectionsRingHom E.X
      (A'.pointScheme (m.baseScheme t)) E.f (e A'.testScheme (m.baseScheme t)).symm _).symm)

end CoherentHom

end AlgebraicGeometry.Space

end
