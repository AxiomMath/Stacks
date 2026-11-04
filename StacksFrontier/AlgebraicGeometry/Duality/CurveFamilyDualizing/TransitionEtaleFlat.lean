module

public import StacksFrontier.AlgebraicGeometry.Duality.CurveFamilyDualizing.TransitionEtaleCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.CurveFamilyDualizing.TransitionTransport
public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportFlatBaseChangeLocallyBounded
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexCompositeGlue

/-!
# Transport of a relative dualizing complex along a flat cartesian diagonal square

Let `D` be a diagonal open of `f : Y ⟶ T` and `D'` one of `f' : X' ⟶ T'`, with diagonals
`Δ : Y ⟶ W` and `Δ' : X' ⟶ W'`, and let `e : X' ⟶ Y`, `w : W' ⟶ W` be such that
`w ≫ pr₁|_W = pr₁|_{W'} ≫ e` and the square

```
X' --Δ'--> W'
|          |
e          w
v          v
Y  --Δ---> W
```

is cartesian, with `w` flat. If `(K, ξ)` is a relative dualizing complex for `f` on `W` and
`Le^*K` is `T'`-perfect, then `(Le^*K, ξ')` is a relative dualizing complex for `f'` on `W'`, where
`ξ'` is the transport of `ξ` along the square through *any* identification
`Lw^*Δ_*𝒪_Y ≅ Δ'_*𝒪_{X'}`
(`AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isRelativeDualizingComplex_xiTransport_of_flat`).

## The proof

By Stacks 0E2M, flat base change for sheaf Hom with exact support,
`Le^* R ℰom(𝒪_Y, L pr₁^*K|_W) ⟶ R ℰom(𝒪_{X'}, Lw^*L pr₁^*K|_W)` is an isomorphism; here it is used
at the locally bounded below object `L pr₁^*K|_W`, through Stacks 0E2L and 0GM7. The identification
`Lw^*Δ_*𝒪_Y ≅ Δ'_*𝒪_{X'}` built from the base change isomorphism of Stacks 0E23 which the map of
Stacks 0E2K is built from (`AlgebraicGeometry.Scheme.Hom.DiagonalOpen.flatDiagIso`) makes the
adjunct of the transported map the pullback of the adjunct of `ξ` followed by the map of
Stacks 0E2K (`AlgebraicGeometry.Scheme.Hom.DiagonalOpen.diagonalAdjunct_xiTransport_flatDiagIso`);
since `ξ` is, up to an automorphism, a generator with invertible adjunct, the transported map has
invertible adjunct, hence satisfies the diagonal condition. A different identification changes the
transported map by an automorphism of `Δ'_*𝒪_{X'}`, which the diagonal condition does not see.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Duality.TwistedInverseImageDuality
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- **The adjunct of a transported map**, with every object a variable. For adjunctions
`F ⊣ R`, `F' ⊣ R'`, functors `Lf`, `Lg` and an identification `ε : Lg ⋙ F' ≅ F ⋙ Lf`, the
adjunct of `ξ : Δ ⟶ L` transported to `Δ'` (through `δ : Δ ≅ F O`, `ε`, `ν : Lg O ≅ O'`,
`δ' : Δ' ≅ F' O'`) and to `L'` (through `P`) is `ν⁻¹` followed by `Lg` of the adjunct of `ξ`, by
the base change map built from `ε`, and by `R' P`. -/
theorem CategoryTheory.Adjunction.homEquiv_transport_chase {𝒵 𝒳 𝒵' 𝒳' : Type*} [Category 𝒵]
    [Category 𝒳] [Category 𝒵'] [Category 𝒳'] {F : 𝒵 ⥤ 𝒳} {R : 𝒳 ⥤ 𝒵} (adj : F ⊣ R)
    {F' : 𝒵' ⥤ 𝒳'} {R' : 𝒳' ⥤ 𝒵'} (adj' : F' ⊣ R') (Lf : 𝒳 ⥤ 𝒳') (Lg : 𝒵 ⥤ 𝒵')
    (ε : Lg ⋙ F' ≅ F ⋙ Lf) {O : 𝒵} {O' : 𝒵'} (ν : Lg.obj O ≅ O') {Δ : 𝒳} {Δ' : 𝒳'}
    (δ : Δ ≅ F.obj O) (δ' : Δ' ≅ F'.obj O') {L : 𝒳} {L' : 𝒳'} (P : Lf.obj L ≅ L')
    (ξ : Δ ⟶ L) :
    adj'.homEquiv _ _ (δ'.inv ≫ (Lf.mapIso δ ≪≫ (ε.app O).symm ≪≫ F'.mapIso ν ≪≫ δ'.symm).inv ≫
        Lf.map ξ ≫ P.hom) =
      ν.inv ≫ Lg.map (adj.homEquiv _ _ (δ.inv ≫ ξ)) ≫
        adj'.homEquiv _ _ (ε.hom.app (R.obj L) ≫ Lf.map (adj.counit.app L)) ≫ R'.map P.hom := by
  apply (adj'.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm,
    Equiv.symm_apply_apply]
  have hn := ε.hom.naturality (adj.homEquiv _ _ (δ.inv ≫ ξ))
  simp only [Functor.comp_map] at hn
  have hc : F.map (adj.homEquiv _ _ (δ.inv ≫ ξ)) ≫ adj.counit.app L = δ.inv ≫ ξ :=
    (adj.homEquiv_counit _ _ _).symm.trans (Equiv.symm_apply_apply _ _)
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [reassoc_of% hn, ← Lf.map_comp_assoc (F.map _) (adj.counit.app L), hc]
  simp

/-- Transport of `a ≫ ξ` through one identification is transport of `ξ` through another,
precomposed with an automorphism, with every object a variable. -/
theorem CategoryTheory.Iso.transport_iso_comp_chase {𝒞 𝒞' : Type*} [Category 𝒞] [Category 𝒞']
    (G : 𝒞 ⥤ 𝒞') {Δ L : 𝒞} {Δ' L' : 𝒞'} (e₁ e₂ : G.obj Δ ≅ Δ') (a : Δ ≅ Δ) (ξ : Δ ⟶ L)
    (P : G.obj L ⟶ L') :
    e₁.inv ≫ G.map (a.hom ≫ ξ) ≫ P = (e₁.symm ≪≫ G.mapIso a ≪≫ e₂).hom ≫ e₂.inv ≫ G.map ξ ≫ P := by
  simp

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

attribute [local instance] DiagonalOpen.isOpenImmersion DiagonalOpen.isClosedImmersion

variable {Y T X' T' : Scheme.{u}} {f : Y ⟶ T} {f' : X' ⟶ T'} (D : DiagonalOpen f)
  (D' : DiagonalOpen f') {e : X' ⟶ Y} {w : D'.W ⟶ D.W} (sq : IsPullback D'.diag e w D.diag)
  (htor : TorIndependent D.diag w)

/-- The standard model of `D(𝒪_T)`, for `letI`. -/
local macro "stdᴰ[" T:term "]" : term => `(HasDerivedCategory.standard (StrictlyPerfect.OXMod $T))

/-- The standard models of `D(𝒪_{T|_U})` for all opens `U` of `T`, for `letI`. -/
local macro "stdOpens[" T:term "]" : term =>
  `(fun (U : TopologicalSpace.Opens ($T).carrier) =>
    HasDerivedCategory.standard (StrictlyPerfect.OXMod (($T).restrict U.isOpenEmbedding)))

/-- **The identification `Lw^*Δ_*𝒪_Y ≅ Δ'_*𝒪_{X'}` of a cartesian diagonal square**, through
the Tor-independent base change isomorphism `Ri'_* ∘ Le^* ≅ Lw^* ∘ Ri_*` of Stacks 0E23 at
`𝒪_Y[0]` that the map of Stacks 0E2K is built from, followed by `Le^*𝒪_Y ≅ 𝒪_{X'}`. -/
def flatDiagIso : (pull w).obj D.diagonalObject ≅ D'.diagonalObject :=
  letI (Z : RingedSpace.{u, u}) (A : Abelian (SheafOfModules (structureSheafRing Z))) :=
    @HasDerivedCategory.standard (SheafOfModules (structureSheafRing Z)) _ A
  (pull w).mapIso D.diagonalObjectIso ≪≫
    ((Stacks.Duality.ExactSupportBaseChange.pushforwardBaseChangeIso sq htor).app
      (structureSingle Y)).symm ≪≫
    (RingedSpaceModuleAdjunction.modulePushforward
      (Stacks.Duality.ExactSupportBaseChange.closedQuotientOfBaseChange
        sq).i).mapDerivedCategory.mapIso
      (Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso e.toLRSHom.toShHom) ≪≫
    D'.diagonalObjectIso.symm

/-- **The adjunct of the transported map**: through `flatDiagIso`, the adjunct
`𝒪_{X'}[0] ⟶ R ℰom(𝒪_{X'}, L pr₁^*(Le^*K)|_{W'})` of the transport of `ξ` is `Le^*` of the
adjunct of `ξ`, followed by the map of Stacks 0E2K and by the identification
`Lw^*(L pr₁^*K|_W) ≅ L pr₁^*(Le^*K)|_{W'}`. -/
theorem diagonalAdjunct_xiTransport_flatDiagIso (hw : w ≫ D.proj = D'.proj ≫ e) (K : Std Y)
    (ξ : (D.diagonalObject : Std D.W) ⟶ (pull D.proj).obj K) :
    D'.diagonalAdjunct ((pull e).obj K)
        (D.xiTransport D' e w hw (D.flatDiagIso D' sq htor) K ξ) =
      (Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso e.toLRSHom.toShHom).inv ≫
        (pull e).map (D.diagonalAdjunct K ξ) ≫
        (Stacks.Duality.ExactSupportBaseChange.baseChangeSheafHomExactSupportMap sq htor).app
          (D.derivedPullbackProj K) ≫
        (Stacks.Duality.ExactSupportBaseChange.closedQuotientOfBaseChange
          sq).derivedSheafHomExactSupport.map (D.projPullIso D' e w hw K).hom :=
  letI (Z : RingedSpace.{u, u}) (A : Abelian (SheafOfModules (structureSheafRing Z))) :=
    @HasDerivedCategory.standard (SheafOfModules (structureSheafRing Z)) _ A
  Adjunction.homEquiv_transport_chase
    D.diagQuotient.derivedModulePushforwardSheafHomExactSupportAdjunction
    (Stacks.Duality.ExactSupportBaseChange.closedQuotientOfBaseChange
      sq).derivedModulePushforwardSheafHomExactSupportAdjunction
    (pull w) (pull e) (Stacks.Duality.ExactSupportBaseChange.pushforwardBaseChangeIso sq htor)
    (Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso e.toLRSHom.toShHom)
    D.diagonalObjectIso D'.diagonalObjectIso (D.projPullIso D' e w hw K) ξ

include sq in
/-- **Stacks 0E2M at a cartesian diagonal square: the transport of a relative dualizing complex
along a flat cartesian diagonal square is a relative dualizing complex.** If `(K, ξ)` is a relative
dualizing complex for `f` on `W`, the square `(Δ', e, w, Δ)` is cartesian with `w` flat, and
`Le^*K` is `T'`-perfect, then `(Le^*K, ξ')` is a relative dualizing complex for `f'` on `W'`, for
`ξ'` the transport of `ξ` through any identification `Lw^*Δ_*𝒪_Y ≅ Δ'_*𝒪_{X'}`. -/
theorem isRelativeDualizingComplex_xiTransport_of_flat [Flat f] [LocallyOfFinitePresentation f]
    [Flat f'] [LocallyOfFinitePresentation f'] [Flat w] (hw : w ≫ D.proj = D'.proj ≫ e)
    {K : Std Y} {ξ : (D.diagonalObject : Std D.W) ⟶ (pull D.proj).obj K}
    (hK : letI := stdᴰ[RingedSpace.inverseImage T.toRingedSpace f.base]
      letI := stdOpens[RingedSpace.inverseImage T.toRingedSpace f.base]
      IsRelativeDualizingComplex f
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage T.toRingedSpace f.base)) D K ξ)
    (hperf : letI := stdᴰ[X'.toRingedSpace]
      letI := stdᴰ[RingedSpace.inverseImage T'.toRingedSpace f'.base]
      letI := stdOpens[RingedSpace.inverseImage T'.toRingedSpace f'.base]
      IsPerfectRelativeTo f'
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage T'.toRingedSpace f'.base)) ((pull e).obj K))
    (eΔ : (pull w).obj D.diagonalObject ≅ D'.diagonalObject) :
    letI := stdᴰ[RingedSpace.inverseImage T'.toRingedSpace f'.base]
    letI := stdOpens[RingedSpace.inverseImage T'.toRingedSpace f'.base]
    IsRelativeDualizingComplex f'
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage T'.toRingedSpace f'.base)) D' ((pull e).obj K)
      (D.xiTransport D' e w hw eΔ K ξ) := by
  let := stdᴰ[RingedSpace.inverseImage T.toRingedSpace f.base]
  let := stdOpens[RingedSpace.inverseImage T.toRingedSpace f.base]
  let := stdᴰ[RingedSpace.inverseImage T'.toRingedSpace f'.base]
  let := stdOpens[RingedSpace.inverseImage T'.toRingedSpace f'.base]
  have htor : TorIndependent D.diag w := torIndependent_of_flat_right _ _
  have := D.pseudoCoherent_diag
  obtain ⟨e₀, a, hξ⟩ := D.exists_iso_comp_diagonalGenerator K ξ hK.isIso_diagonalAction
  open Stacks.Duality.ExactSupportBaseChange in
  have hbc :=
    isIso_baseChangeSheafHomExactSupportMap_app_of_flat_of_isLocallyBoundedBelow
      sq htor (D.derivedPullbackProj K)
      (D.isLocallyBoundedBelow_derivedPullbackProj K hK.isPerfectRelativeTo)
  have hadj : IsIso (D'.diagonalAdjunct ((pull e).obj K)
      (D.xiTransport D' e w hw (D.flatDiagIso D' sq htor) K (D.diagonalGenerator K e₀))) := by
    have h₀ := D.isIso_diagonalAdjunct_diagonalGenerator K e₀
    have h₁ : IsIso ((pull e).map (D.diagonalAdjunct K (D.diagonalGenerator K e₀))) :=
      Iso.isIso_hom ((pull e).mapIso (@asIso _ _ _ _ _ h₀))
    rw [D.diagonalAdjunct_xiTransport_flatDiagIso D' sq htor hw]
    exact IsIso.comp_isIso'
      (Iso.isIso_inv (Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso
        e.toLRSHom.toShHom))
      (IsIso.comp_isIso' h₁ (IsIso.comp_isIso' hbc (Iso.isIso_hom
        ((Stacks.Duality.ExactSupportBaseChange.closedQuotientOfBaseChange
          sq).derivedSheafHomExactSupport.mapIso (D.projPullIso D' e w hw K)))))
  have hG := D'.isIso_diagonalAction_of_isIso_diagonalAdjunct _ _ hadj
  have heq : D.xiTransport D' e w hw eΔ K ξ =
      (eΔ.symm ≪≫ (pull w).mapIso a ≪≫ D.flatDiagIso D' sq htor).hom ≫
        D.xiTransport D' e w hw (D.flatDiagIso D' sq htor) K (D.diagonalGenerator K e₀) := by
    unfold xiTransport
    rw [hξ]
    exact Iso.transport_iso_comp_chase _ _ _ _ _ _
  constructor
  · exact hperf
  · rw [heq]
    exact D'.isIso_diagonalAction_iso_comp hG _

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
