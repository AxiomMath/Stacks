module

public import StacksFrontier.AlgebraicGeometry.Descent.CubeFibreKunneth
public import StacksFrontier.AlgebraicGeometry.Descent.DescentLocusComparisonTrivial
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UnitSpreading
public import StacksFrontier.Homology.Perfect.FibreQuasiIsoSpreading
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.BaseChange

/-!
# The triviality locus of the theorem of the cube is open

Let `X`, `Y` be proper, flat, of finite presentation, with geometrically integral fibres over
`Spec A`, with sections `σ`, `τ`, and let `L` be an invertible module on `P = X ×_A Y` which is
trivial along the two faces `Y ⟶ P` and `X ⟶ P` through the sections. If `L` is trivial on the
fibre of `P` over a prime `p`, then `L` has a global section whose pullback to that fibre is
nonzero. This is the step of the proof of [Stacks, Tag 0BF4] that goes through [Stacks, Tag 0BF3]
and [Stacks, Tag 0BF2]: the chain map `(ρ₁, ρ₂ + u) : RΓ(P, L) ⊕ A → RΓ(Y, j₁^* L) ⊕ RΓ(X, j₂^* L)`
is an isomorphism on `H⁰` and injective on `H¹` on the fibre (the latter by Künneth).

## Main results

* `Stacks.Cube.exists_eq_smul_of_cocycle`: on a scheme over a field `K` with `Γ(𝒪) = K`, the
  degree-zero Čech cocycles of a module isomorphic to `𝒪` are the multiples of a generator.
* `Stacks.Cube.fibreTransport_sectionCochain`: through `fibreTransport`, the fibre of the Čech
  cochain of the section `e⁻¹ 1` of a trivial module is the cochain of its pullback.
* `Stacks.Cube.exists_section_pullback_ne_zero`: under the hypotheses above, `L` has a global
  section whose pullback to the fibre over `p` is nonzero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections AlgebraicGeometry.DescentLocusComparison

open scoped ChangeOfRings

universe u

namespace Stacks.Cube

attribute [local instance 10000] HasDerivedCategory.standard

/-- **On a scheme over a field with only constant functions, the degree-zero Čech cocycles of a
module isomorphic to `𝒪` are the multiples of a generator.** Let `f₀ : X₀ ⟶ Spec K` with
`K ⟶ Γ(X₀, 𝒪)` bijective, `F ≅ 𝒪_{X₀}`, `W = X₀` and `g₀ ∈ Γ(F, W)` mapping to `1`. Then every
alternating `0`-cocycle on a cover of `W` is `k • g₀` restricted, for some `k ∈ K`, and `g₀`
restricted is nonzero. -/
theorem exists_eq_smul_of_cocycle {K : Type u} [Field K] {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (.of K)) (hΓ : Function.Bijective (Stacks.Cech.globalRingHom f₀).hom)
    {I : Type u} (U : I → X₀.Opens) {W : X₀.Opens} (hW : W = ⊤) (hUW : ∀ i, U i ≤ W)
    (hcov : W ≤ ⨆ i, U i) (F : X₀.Modules) (ε : F ≅ Scheme.unitModule X₀) (g₀ : Γ(F, W))
    (hg₀ : ε.hom.app W g₀ = (1 : Γ(X₀, W))) :
    letI := Stacks.Cech.sectionsModule f₀ F W
    letI := Stacks.Cech.cochainModule f₀ U F 0
    letI := Stacks.Cech.cochainModule f₀ U F 1
    (∀ c : Stacks.Cech.alternatingSubmodule f₀ U F 0,
        Stacks.Cech.alternatingCechModuleD f₀ U F 0 c = 0 →
        ∃ k : K, c = k • Stacks.Cech.sectionsToAlternatingₗ f₀ U F hUW g₀) ∧
      Stacks.Cech.sectionsToAlternatingₗ f₀ U F hUW g₀ ≠ 0 := by
  let := Stacks.Cech.sectionsModule f₀ F W
  let := Stacks.Cech.cochainModule f₀ U F 0
  let := Stacks.Cech.cochainModule f₀ U F 1
  have hb := bijective_baseRingHom_of_eq_top f₀ hW hΓ
  have hinj : Function.Injective (ε.hom.app W) := fun s t hst => by
    have h1 := Stacks.Cech.iso_inv_app_hom_app ε W s
    have h2 := Stacks.Cech.iso_inv_app_hom_app ε W t
    rw [← h1, ← h2, hst]
  have hsmul : ∀ (k : K) (s : Γ(F, W)), ε.hom.app W (k • s) =
      (show Γ(X₀, W) from (Stacks.Cech.baseRingHom f₀ W).hom k *
        (show Γ(X₀, W) from ε.hom.app W s)) := fun k s =>
    Scheme.Modules.Hom.app_smul ε.hom ((Stacks.Cech.baseRingHom f₀ W).hom k) s
  refine ⟨fun c hc => ?_, fun h0 => ?_⟩
  · have hr := Stacks.Cech.range_sectionsToAlternatingₗ f₀ U F hUW hcov
    obtain ⟨s, rfl⟩ : c ∈ LinearMap.range (Stacks.Cech.sectionsToAlternatingₗ f₀ U F hUW) :=
      hr ▸ LinearMap.mem_ker.2 hc
    obtain ⟨k, hk⟩ := hb.2 (ε.hom.app W s)
    refine ⟨k, ?_⟩
    rw [← map_smul]
    congr 1
    refine hinj ?_
    rw [hsmul, hg₀]
    exact ((mul_one _).trans hk).symm
  · have h1 := Stacks.Cech.sectionsToAlternatingₗ_injective f₀ U F hUW hcov
      (h0.trans (map_zero _).symm)
    have h2 : (1 : Γ(X₀, W)) = 0 := by
      rw [← hg₀, h1]
      exact (ε.hom.app W).hom.map_zero
    exact one_ne_zero (hb.1 ((map_one _).trans (h2.trans (map_zero _).symm)))


section Generator

variable {A K : Type u} [CommRing A] [Field K] (ψ : A →+* K) {X X₀ : Scheme.{u}}
  {f : X ⟶ Spec (.of A)} [IsSeparated f] {f₀ : X₀ ⟶ Spec (.of K)} {g : X₀ ⟶ X}
  (hsq : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom ψ)))
  (hΓ : Function.Bijective (Stacks.Cech.globalRingHom f₀).hom)
  (F : X.Modules) [F.IsQuasicoherent] {I : Type u} [Finite I] [LinearOrder I]
  (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
  (e : F ≅ Scheme.unitModule X)

omit [LinearOrder I] in
/-- The fibre of the Čech model of the section `e⁻¹ 1` of a trivial module, through
`fibreTransport`, is the restriction of its pullback. -/
theorem fibreTransport_sectionCochain :
    letI : Algebra A K := ψ.toAlgebra
    (fibreTransport ψ hsq F U hU hUaff 0).hom (show (StacksDraft.Perfect.extendScalarsCx ψ
        (baseAlternatingCechComplex f U hU F)).X 0 from (1 : K) ⊗ₜ[A, ψ]
        sectionCochain f U hU F (e.inv.app ⊤ (1 : Γ(X, ⊤))) (1 : A)) =
      Stacks.Cech.sectionsToAlternatingₗ f₀ (fun i => g ⁻¹ᵁ U i)
        ((Scheme.Modules.pullback g).obj F)
        (Stacks.Cech.preimage_le_of_le U (fun _ => le_top) g (fun i => g ⁻¹ᵁ U i) (Equiv.refl I)
          (preimage_eq_preimage_equivRefl g U))
        (Stacks.Cech.pullbackSections g F ⊤ (e.inv.app ⊤ (1 : Γ(X, ⊤)))) := by
  let : Algebra A K := ψ.toAlgebra
  let := Stacks.Cech.sectionsModule f F ⊤
  have h2 := fibreTransport_one_tmul ψ hsq F U hU hUaff 0
    (sectionCochain f U hU F (e.inv.app ⊤ (1 : Γ(X, ⊤))) (1 : A))
  have h3 : (baseAlternatingCechComplexXIso f U hU F 0).hom
      (sectionCochain f U hU F (e.inv.app ⊤ (1 : Γ(X, ⊤))) (1 : A)) =
      Stacks.Cech.sectionsToAlternatingₗ f U F (fun _ => le_top) (e.inv.app ⊤ (1 : Γ(X, ⊤))) := by
    refine (Iso.inv_hom_id_apply (baseAlternatingCechComplexXIso f U hU F 0) _).trans ?_
    exact congrArg (Stacks.Cech.sectionsToAlternatingₗ f U F (fun _ => le_top))
      (one_smul A _)
  refine h2.trans ((congrArg _ h3).trans ?_)
  exact Stacks.Cech.alternatingCochainBaseChangeₗ_sectionsToAlternatingₗ f U F
    (fun _ => le_top) g (fun i => g ⁻¹ᵁ U i) (Equiv.refl I) (preimage_eq_preimage_equivRefl g U)
    ψ f₀ (fun W => Stacks.Cech.baseRingHom_comp_app ψ f f₀ g hsq W) _

omit [F.IsQuasicoherent] in
/-- The pullback of the section `e⁻¹ 1` maps to `1` under the pulled back trivialisation. -/
theorem pullbackUnitIso_pullbackSections_inv_one {T : Scheme.{u}} (h : T ⟶ X) :
    ((Scheme.Modules.pullback h).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso h).hom.app (h ⁻¹ᵁ ⊤)
      (Stacks.Cech.pullbackSections h F ⊤ (e.inv.app ⊤ (1 : Γ(X, ⊤)))) =
        (show Γ(Scheme.unitModule T, h ⁻¹ᵁ ⊤) from (1 : Γ(T, h ⁻¹ᵁ ⊤))) := by
  change (Scheme.Modules.pullbackUnitIso h).hom.app (h ⁻¹ᵁ ⊤)
    (((Scheme.Modules.pullback h).map e.hom).app (h ⁻¹ᵁ ⊤)
      (Stacks.Cech.pullbackSections h F ⊤ (e.inv.app ⊤ (1 : Γ(X, ⊤))))) = _
  refine (congrArg (fun z => (Scheme.Modules.pullbackUnitIso h).hom.app (h ⁻¹ᵁ ⊤) z)
    (Stacks.Cech.pullbackSections_naturality h e.hom ⊤ _).symm).trans ?_
  refine (congrArg (fun z => (Scheme.Modules.pullbackUnitIso h).hom.app (h ⁻¹ᵁ ⊤)
    (Stacks.Cech.pullbackSections h _ ⊤ z))
    (AlgebraicGeometry.SectionsEqualizer.moduleIso_hom_inv_app e _)).trans ?_
  exact (Stacks.Cech.pullbackUnitIso_hom_app_pullbackSections h ⊤ (1 : Γ(X, ⊤))).trans
    (map_one (h.app ⊤).hom)

omit [LinearOrder I] in
  /-- A degree-zero fibre cochain is a cocycle iff its image under `fibreTransport` is. -/
  private theorem d_eq_zero_iff_fibreTransport (y : (StacksDraft.Perfect.extendScalarsCx ψ
      (baseAlternatingCechComplex f U hU F)).X 0) :
    (StacksDraft.Perfect.extendScalarsCx ψ (baseAlternatingCechComplex f U hU F)).d 0 1 y = 0 ↔
      Stacks.Cech.alternatingCechModuleD f₀ (fun i => g ⁻¹ᵁ U i)
        ((Scheme.Modules.pullback g).obj F) 0
        ((fibreTransport ψ hsq F U hU hUaff 0).hom y) = 0 := by
  have hd := fibreTransport_d_apply ψ hsq F U hU hUaff 0 y
  refine ⟨fun hy => hd.symm.trans ?_, fun hy => ?_⟩
  · change (fibreTransport ψ hsq F U hU hUaff (0 + 1)).hom
      ((StacksDraft.Perfect.extendScalarsCx ψ _).d 0 1 y) = 0
    rw [show (StacksDraft.Perfect.extendScalarsCx ψ _).d 0 1 y = 0 from hy, map_zero]
  · exact (ConcreteCategory.bijective_of_isIso (fibreTransport ψ hsq F U hU hUaff 1).hom).1
      ((hd.trans hy).trans (map_zero _).symm)

include hsq hUaff hΓ in
omit [LinearOrder I] in
/-- **The fibre of the Čech model of a trivial module has its degree-zero cocycles spanned by the
generator.** For `F ≅ 𝒪_X` over `Spec A` and a field-valued point whose fibre has only constant
functions, every degree-zero cocycle of the fibre of the Čech model of `F` is a multiple of
`1 ⊗ s`, for `s` the cochain of the section `e⁻¹ 1`, and `1 ⊗ s ≠ 0`. -/
theorem fibre_sectionCochain_generator :
    (∀ y : (StacksDraft.Perfect.extendScalarsCx ψ (baseAlternatingCechComplex f U hU F)).X 0,
      (StacksDraft.Perfect.extendScalarsCx ψ (baseAlternatingCechComplex f U hU F)).d 0 1 y = 0 →
        ∃ c : K, y = c • (show (StacksDraft.Perfect.extendScalarsCx ψ
          (baseAlternatingCechComplex f U hU F)).X 0 from (1 : K) ⊗ₜ[A, ψ]
          sectionCochain f U hU F (e.inv.app ⊤ (1 : Γ(X, ⊤))) (1 : A))) ∧
      (show (StacksDraft.Perfect.extendScalarsCx ψ (baseAlternatingCechComplex f U hU F)).X 0 from
        (1 : K) ⊗ₜ[A, ψ] sectionCochain f U hU F (e.inv.app ⊤ (1 : Γ(X, ⊤))) (1 : A)) ≠ 0 := by
  set τ := fibreTransport ψ hsq F U hU hUaff
  obtain ⟨hgen, hne⟩ := exists_eq_smul_of_cocycle f₀ hΓ (fun i => g ⁻¹ᵁ U i) g.preimage_top
    (Stacks.Cech.preimage_le_of_le U (fun _ => le_top) g (fun i => g ⁻¹ᵁ U i) (Equiv.refl I)
      (preimage_eq_preimage_equivRefl g U))
    ((top_eq_iSup_preimage g U hU) ▸ le_top) ((Scheme.Modules.pullback g).obj F)
    ((Scheme.Modules.pullback g).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso g)
    (Stacks.Cech.pullbackSections g F ⊤ (e.inv.app ⊤ (1 : Γ(X, ⊤))))
    (pullbackUnitIso_pullbackSections_inv_one F e g)
  have hτs := fibreTransport_sectionCochain ψ hsq F U hU hUaff e
  refine ⟨fun y hy => ?_, fun h0 => hne ?_⟩
  · obtain ⟨c, hc⟩ := hgen ((τ 0).hom y) ((d_eq_zero_iff_fibreTransport ψ hsq F U hU hUaff y).1 hy)
    refine ⟨c, (ConcreteCategory.bijective_of_isIso (τ 0).hom).1 ?_⟩
    rwa [map_smul, hτs]
  · rw [← hτs, h0, map_zero]
    rfl

end Generator

section Face

variable {A K : Type u} [CommRing A] [Field K] (χ : A →+* K)
  {X X' X₀ X'₀ : Scheme.{u}} (a : X' ⟶ X)
  {f : X ⟶ Spec (.of A)} {f' : X' ⟶ Spec (.of A)} (ha : a ≫ f = f')
  [IsSeparated f] [IsSeparated f']
  {f₀ : X₀ ⟶ Spec (.of K)} {f'₀ : X'₀ ⟶ Spec (.of K)} {q : X₀ ⟶ X} {q' : X'₀ ⟶ X'}
  (hsq : IsPullback q f₀ f (Spec.map (CommRingCat.ofHom χ)))
  (hsq' : IsPullback q' f'₀ f' (Spec.map (CommRingCat.ofHom χ)))
  (a₀ : X'₀ ⟶ X₀) (ha₀ : a₀ ≫ f₀ = f'₀) (hcomm : a₀ ≫ q = q' ≫ a)
  {I I' : Type u} [Finite I] [Finite I'] [LinearOrder I] [LinearOrder I']
  (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
  (W : I' → X'.Opens) (hW : (⊤ : X'.Opens) = ⨆ k, W k) (hWaff : ∀ k, IsAffineOpen (W k))
  (π : I' → I) (hWU : ∀ k, W k ≤ a ⁻¹ᵁ U (π k)) (F : X.Modules)
  [F.IsQuasicoherent] [((Scheme.Modules.pullback a).obj F).IsQuasicoherent]
  (e₀ : (Scheme.Modules.pullback q).obj F ≅ Scheme.unitModule X₀)

/-- The fibre generator of the Čech model of a module trivial on the fibre: the cochain of the
section `e₀⁻¹ 1`, transported back along `fibreTransport`. -/
def fibreGenerator :
    (StacksDraft.Perfect.extendScalarsCx χ (baseAlternatingCechComplex f U hU F)).X 0 :=
  (fibreTransport χ hsq F U hU hUaff 0).inv
    (Stacks.Cech.sectionsToAlternatingₗ f₀ (fun i => q ⁻¹ᵁ U i) ((Scheme.Modules.pullback q).obj F)
      (fun _ => le_top) (e₀.inv.app ⊤ (1 : Γ(X₀, ⊤))))

omit [LinearOrder I] in
  /-- `fibreTransport` sends the fibre generator to the cochain of the section `e₀⁻¹ 1`. -/
  private theorem fibreTransport_hom_fibreGenerator :
    (fibreTransport χ hsq F U hU hUaff 0).hom (fibreGenerator χ hsq U hU hUaff F e₀) =
      Stacks.Cech.sectionsToAlternatingₗ f₀ (fun i => q ⁻¹ᵁ U i)
        ((Scheme.Modules.pullback q).obj F) (fun _ => le_top) (e₀.inv.app ⊤ (1 : Γ(X₀, ⊤))) :=
  Iso.inv_hom_id_apply _ _

include hU in
omit [LinearOrder I] in
/-- **The degree-zero fibre cocycles are the multiples of the fibre generator**, which is a
cocycle. -/
theorem fibreGenerator_spec (hΓ : Function.Bijective (Stacks.Cech.globalRingHom f₀).hom) :
    (StacksDraft.Perfect.extendScalarsCx χ (baseAlternatingCechComplex f U hU F)).d 0 1
        (fibreGenerator χ hsq U hU hUaff F e₀) = 0 ∧
      ∀ y : (StacksDraft.Perfect.extendScalarsCx χ (baseAlternatingCechComplex f U hU F)).X 0,
        (StacksDraft.Perfect.extendScalarsCx χ (baseAlternatingCechComplex f U hU F)).d 0 1 y = 0 →
          ∃ c : K, y = c • fibreGenerator χ hsq U hU hUaff F e₀ := by
  have hcov : (⊤ : X₀.Opens) ≤ ⨆ i, q ⁻¹ᵁ U i := (top_eq_iSup_preimage q U hU).le
  obtain ⟨hgen, -⟩ := exists_eq_smul_of_cocycle f₀ hΓ (fun i => q ⁻¹ᵁ U i) rfl
    (fun _ => le_top) hcov ((Scheme.Modules.pullback q).obj F) e₀ (e₀.inv.app ⊤ (1 : Γ(X₀, ⊤)))
    (AlgebraicGeometry.SectionsEqualizer.moduleIso_hom_inv_app e₀ _)
  have hgτ := fibreTransport_hom_fibreGenerator χ hsq U hU hUaff F e₀
  have hr := Stacks.Cech.range_sectionsToAlternatingₗ f₀ (fun i => q ⁻¹ᵁ U i)
    ((Scheme.Modules.pullback q).obj F) (fun _ => le_top) hcov
  refine ⟨(d_eq_zero_iff_fibreTransport χ hsq F U hU hUaff _).2 ?_, fun y hy => ?_⟩
  · rw [hgτ]
    let := Stacks.Cech.sectionsModule f₀ ((Scheme.Modules.pullback q).obj F) ⊤
    let := Stacks.Cech.cochainModule f₀ (fun i => q ⁻¹ᵁ U i) ((Scheme.Modules.pullback q).obj F) 0
    let := Stacks.Cech.cochainModule f₀ (fun i => q ⁻¹ᵁ U i) ((Scheme.Modules.pullback q).obj F) 1
    exact LinearMap.mem_ker.1 (hr ▸ LinearMap.mem_range_self _ _)
  · obtain ⟨c, hc⟩ := hgen ((fibreTransport χ hsq F U hU hUaff 0).hom y)
      ((d_eq_zero_iff_fibreTransport χ hsq F U hU hUaff y).1 hy)
    refine ⟨c, (ConcreteCategory.bijective_of_isIso
      (fibreTransport χ hsq F U hU hUaff 0).hom).1 ?_⟩
    rwa [map_smul, hgτ]

/-- An alternating Čech cochain map applied to the restrictions of a section is the cochain of the
image section. -/
theorem alternatingCechModuleObjMap_sectionsToAlternatingₗ {T : Scheme.{u}}
    {h : T ⟶ Spec (.of K)} {J : Type u} (V : J → T.Opens) {G H : T.Modules} (t : G ⟶ H)
    {O : T.Opens} (hVO : ∀ j, V j ≤ O) (s : Γ(G, O)) :
    Stacks.Cech.alternatingCechModuleObjMap h V t 0
        (Stacks.Cech.sectionsToAlternatingₗ h V G hVO s) =
      Stacks.Cech.sectionsToAlternatingₗ h V H hVO (t.app O s) := by
  refine Subtype.ext (funext fun i => ?_)
  exact (AlgebraicGeometry.SectionsEqualizer.moduleHom_app_restrict t
    (homOfLE (Stacks.Cech.inter_le_of_le V hVO i)) s)

include hU hW hcomm ha₀ hWaff hsq' in
omit [LinearOrder I] [LinearOrder I'] in
/-- **The fibre of the chain map of Čech models does not kill the fibre generator** when the
fibre `X'₀` has only constant functions. -/
theorem fibreGenerator_map_ne_zero
    (hΓ' : Function.Bijective (Stacks.Cech.globalRingHom f'₀).hom) :
    ((ModuleCat.extendScalars.{u, u, u} χ).map
      ((cechModelPullbackMap a f f' ha U hU W hW π hWU F).f 0))
        (fibreGenerator χ hsq U hU hUaff F e₀) ≠ 0 := by
  intro h0
  set ψ := Stacks.Cech.pullbackSquareIso a q q' a₀ hcomm F
  have hcov' : (⊤ : X'₀.Opens) ≤ ⨆ k, q' ⁻¹ᵁ W k := (top_eq_iSup_preimage q' W hW).le
  have key := fibreTransport_cechModelPullbackMap χ a ha hsq hsq' a₀ ha₀ hcomm U hU hUaff W hW
    hWaff π hWU F 0 (fibreGenerator χ hsq U hU hUaff F e₀)
  have h0' : ((ModuleCat.extendScalars.{u, u, u} χ).map
      ((cechModelPullbackMap a f f' ha U hU W hW π hWU F).f ((0 : ℕ) : ℤ)))
        (fibreGenerator χ hsq U hU hUaff F e₀) = 0 := h0
  rw [h0', map_zero] at key
  rw [fibreTransport_hom_fibreGenerator,
    Stacks.Cech.alternatingCochainRefinementPullbackₗ_sectionsToAlternatingₗ a₀ _ _ π _ _
    f₀ f'₀ ha₀ (fun _ => le_top) (fun _ => le_of_le_of_eq le_top a₀.preimage_top.symm),
    alternatingCechModuleObjMap_sectionsToAlternatingₗ] at key
  have h1 := Stacks.Cech.sectionsToAlternatingₗ_injective f'₀ (fun k => q' ⁻¹ᵁ W k) _
    (fun _ => le_of_le_of_eq le_top a₀.preimage_top.symm)
    (le_of_eq_of_le a₀.preimage_top hcov') (key.symm.trans (map_zero _).symm)
  have h2 : Stacks.Cech.pullbackSections a₀ ((Scheme.Modules.pullback q).obj F) ⊤
      (e₀.inv.app ⊤ (1 : Γ(X₀, ⊤))) = 0 := by
    have := Stacks.Cech.iso_inv_app_hom_app ψ _ (Stacks.Cech.pullbackSections a₀ _ ⊤
      (e₀.inv.app ⊤ (1 : Γ(X₀, ⊤))))
    rw [← this, h1]
    exact (ψ.inv.app _).hom.map_zero
  have h3 := pullbackUnitIso_pullbackSections_inv_one ((Scheme.Modules.pullback q).obj F) e₀ a₀
  rw [h2] at h3
  have hb := bijective_baseRingHom_of_eq_top f'₀ (a₀.preimage_top) hΓ'
  refine one_ne_zero (hb.1 ((map_one _).trans ?_))
  refine (h3.symm.trans ?_).trans (map_zero _).symm
  exact (((Scheme.Modules.pullback a₀).mapIso e₀ ≪≫
    Scheme.Modules.pullbackUnitIso a₀).hom.app _).hom.map_zero

include hU hW hcomm ha₀ hWaff hsq' in
omit [LinearOrder I] [LinearOrder I'] in
/-- **A fibre cocycle whose image along a face is a coboundary pulls back to a coboundary.** -/
theorem exists_cechD_eq_cochainPullback
    (x : (StacksDraft.Perfect.extendScalarsCx χ (baseAlternatingCechComplex f U hU F)).X 1)
    (y : (StacksDraft.Perfect.extendScalarsCx χ
      (baseAlternatingCechComplex f' W hW ((Scheme.Modules.pullback a).obj F))).X 0)
    (hy : ((ModuleCat.extendScalars.{u, u, u} χ).map
        ((cechModelPullbackMap a f f' ha U hU W hW π hWU F).f 1)) x =
      (StacksDraft.Perfect.extendScalarsCx χ
        (baseAlternatingCechComplex f' W hW ((Scheme.Modules.pullback a).obj F))).d 0 1 y) :
    ∃ t : CechCochains.Cochain (fun k => q' ⁻¹ᵁ W k)
        ((Scheme.Modules.pullback a₀).obj ((Scheme.Modules.pullback q).obj F)).presheaf 0,
      CechCochains.cechD _ _ 0 t = Stacks.Cech.cochainPullback a₀ (fun i => q ⁻¹ᵁ U i)
        (fun k => q' ⁻¹ᵁ W k) π
        (Stacks.Cech.preimage_le_preimage_of_comm a q q' a₀ hcomm U W π hWU)
        ((Scheme.Modules.pullback q).obj F) 1
        ((fibreTransport χ hsq F U hU hUaff 1).hom x).1 := by
  set e := Stacks.Cech.pullbackSquareIso a q q' a₀ hcomm F
  set W₀ : I' → X'₀.Opens := fun k => q' ⁻¹ᵁ W k
  set T' := fibreTransport χ hsq' ((Scheme.Modules.pullback a).obj F) W hW hWaff
  set Y := (T' 0).hom y
  have hY : Stacks.Cech.alternatingCechModuleObjMap f'₀ W₀ e.hom 1
      (Stacks.Cech.alternatingCochainRefinementPullbackₗ a₀ (fun i => q ⁻¹ᵁ U i) W₀ π
        (Stacks.Cech.preimage_le_preimage_of_comm a q q' a₀ hcomm U W π hWU)
        ((Scheme.Modules.pullback q).obj F) f₀ f'₀ ha₀ 1
        ((fibreTransport χ hsq F U hU hUaff 1).hom x)) =
      (Stacks.Cech.alternatingCechModuleComplex f'₀ W₀
        ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback a).obj F))).d 0 (0 + 1) Y := by
    rw [← fibreTransport_cechModelPullbackMap χ a ha hsq hsq' a₀ ha₀ hcomm U hU hUaff W hW
      hWaff π hWU F 1 x]
    exact (congrArg (T' 1).hom hy).trans
      (fibreTransport_d_apply χ hsq' ((Scheme.Modules.pullback a).obj F) W hW hWaff 0 y)
  refine ⟨(Stacks.Cech.alternatingCechModuleObjMap f'₀ W₀ e.inv 0 Y).1, ?_⟩
  have hc := congr($((Stacks.Cech.alternatingCechModuleComplexMap f'₀ W₀ e.inv).comm 0 1) Y)
  simp only at hc
  have h1 : CechCochains.cechD W₀ _ 0 (Stacks.Cech.alternatingCechModuleObjMap f'₀ W₀ e.inv 0 Y).1 =
      ((Stacks.Cech.alternatingCechModuleComplexMap f'₀ W₀ e.inv).f 1
        ((Stacks.Cech.alternatingCechModuleComplex f'₀ W₀
          ((Scheme.Modules.pullback q').obj
            ((Scheme.Modules.pullback a).obj F))).d 0 1 Y)).1 :=
    congrArg Subtype.val hc
  rw [h1, ← hY]
  funext k
  exact Stacks.Cech.iso_inv_app_hom_app e _ _

end Face

section Main

/-- The unit module is flat over a flat morphism. -/
theorem isFlatOver_unitModule {T S : Scheme.{u}} (h : T ⟶ S) [Flat h] :
    IsFlatOver h.toLRSHom.toShHom (Scheme.unitModule T) := fun x =>
  (AlgebraicGeometry.MorphismOfGerms.flat_stalkMap_iff_isFlatOverAt_unit h x).1
    (Flat.stalkMap h x)

variable {A : Type u} [CommRing A] {X Y P : Scheme.{u}}
  {fX : X ⟶ Spec (.of A)} {fY : Y ⟶ Spec (.of A)} {r : P ⟶ X} {q : P ⟶ Y}

/-- **The affine core of the openness of the triviality locus in the theorem of the cube.**
Let `P = X ×_A Y` with `X`, `Y` proper, flat and locally of finite presentation over `A`, with
finite affine covers `U`, `V` (with affine finite intersections) and faces `j₁ : Y ⟶ P`,
`j₂ : X ⟶ P` through sections `σ`, `τ` landing in `U a₀`, `V b₀`. Let `L` be of finite
presentation and flat over `A`, trivial along both faces, and trivial on the fibre over a prime
`p` (given with its fibre product structure, its faces, and `Γ(𝒪) = κ(p)` on the three fibres).
Then `L` has a global section whose pullback to the fibre over `p` is nonzero. -/
theorem exists_section_pullback_ne_zero (H : IsPullback r q fX fY)
    [IsProper fX] [Flat fX] [LocallyOfFinitePresentation fX]
    [IsProper fY] [Flat fY] [LocallyOfFinitePresentation fY]
    (σ : Spec (.of A) ⟶ X) (τ : Spec (.of A) ⟶ Y) (hσ : σ ≫ fX = 𝟙 _) (_hτ : τ ≫ fY = 𝟙 _)
    (j₁ : Y ⟶ P) (hj₁r : j₁ ≫ r = fY ≫ σ) (hj₁q : j₁ ≫ q = 𝟙 Y)
    (j₂ : X ⟶ P) (hj₂r : j₂ ≫ r = 𝟙 X) (hj₂q : j₂ ≫ q = fX ≫ τ)
    (L : P.Modules) [L.IsFinitePresentation] (hL : IsFlatOver (r ≫ fX).toLRSHom.toShHom L)
    (e₁ : (Scheme.Modules.pullback j₁).obj L ≅ Scheme.unitModule Y)
    (e₂ : (Scheme.Modules.pullback j₂).obj L ≅ Scheme.unitModule X)
    {I J : Type u} [Finite I] [LinearOrder I] [Finite J] [LinearOrder J]
    (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
    (haffU : ∀ (m : ℕ) (a : Fin (m + 1) → I), IsAffineOpen (⨅ k, U (a k)))
    (V : J → Y.Opens) (hV : (⊤ : Y.Opens) = ⨆ j, V j) (hVaff : ∀ j, IsAffineOpen (V j))
    (haffV : ∀ (m : ℕ) (b : Fin (m + 1) → J), IsAffineOpen (⨅ k, V (b k)))
    (a₀ : I) (ha₀ : σ ⁻¹ᵁ U a₀ = ⊤) (b₀ : J) (hb₀ : τ ⁻¹ᵁ V b₀ = ⊤)
    (p : Ideal A) [p.IsPrime]
    {X₀ Y₀ P₀ : Scheme.{u}} {fX₀ : X₀ ⟶ Spec (.of p.ResidueField)}
    {fY₀ : Y₀ ⟶ Spec (.of p.ResidueField)} {π₀ : P₀ ⟶ Spec (.of p.ResidueField)}
    {gX : X₀ ⟶ X} {gY : Y₀ ⟶ Y} {gP : P₀ ⟶ P}
    (hsqX : IsPullback gX fX₀ fX (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    (hsqY : IsPullback gY fY₀ fY (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    (hsqP : IsPullback gP π₀ (r ≫ fX)
      (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    {r₀ : P₀ ⟶ X₀} {q₀ : P₀ ⟶ Y₀} (H₀ : IsPullback r₀ q₀ fX₀ fY₀) (hπ₀ : r₀ ≫ fX₀ = π₀)
    (hr₀ : r₀ ≫ gX = gP ≫ r) (hq₀ : q₀ ≫ gY = gP ≫ q)
    (σ₀ : Spec (.of p.ResidueField) ⟶ X₀) (hσ₀ : σ₀ ≫ fX₀ = 𝟙 _)
    (hσ₀g : σ₀ ≫ gX = Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)) ≫ σ)
    (τ₀ : Spec (.of p.ResidueField) ⟶ Y₀) (hτ₀ : τ₀ ≫ fY₀ = 𝟙 _)
    (hτ₀g : τ₀ ≫ gY = Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)) ≫ τ)
    (j₁₀ : Y₀ ⟶ P₀) (hj₁₀r : j₁₀ ≫ r₀ = fY₀ ≫ σ₀) (hj₁₀q : j₁₀ ≫ q₀ = 𝟙 Y₀)
    (hj₁₀g : j₁₀ ≫ gP = gY ≫ j₁)
    (j₂₀ : X₀ ⟶ P₀) (hj₂₀r : j₂₀ ≫ r₀ = 𝟙 X₀) (hj₂₀q : j₂₀ ≫ q₀ = fX₀ ≫ τ₀)
    (hj₂₀g : j₂₀ ≫ gP = gX ≫ j₂)
    (hΓX₀ : Function.Bijective (Stacks.Cech.globalRingHom fX₀).hom)
    (hΓY₀ : Function.Bijective (Stacks.Cech.globalRingHom fY₀).hom)
    (hΓP₀ : Function.Bijective (Stacks.Cech.globalRingHom π₀).hom)
    (e₀ : (Scheme.Modules.pullback gP).obj L ≅ Scheme.unitModule P₀) :
    ∃ s : Γ(L, ⊤), Stacks.Cech.pullbackSections gP L ⊤ s ≠ 0 := by
  classical
  have := Fintype.ofFinite I
  have := Fintype.ofFinite J
  set κ := p.ResidueField
  set χ := algebraMap A κ
  let : LinearOrder (I × J) := inferInstanceAs (LinearOrder (I ×ₗ J))
  have : L.IsQuasicoherent := Stacks.Modules.isQuasicoherent_of_isFinitePresentation L
  have : IsProper r := MorphismProperty.of_isPullback H.flip inferInstance
  have : LocallyOfFinitePresentation r := MorphismProperty.of_isPullback H.flip inferInstance
  have : Flat r := MorphismProperty.of_isPullback H.flip inferInstance
  set W : I × J → P.Opens := fun t => Stacks.Cech.Kunneth.box r q U V ![t.1] ![t.2] with hWdef
  have hboxaff : ∀ (m n : ℕ) (a : Fin (m + 1) → I) (b : Fin (n + 1) → J),
      IsAffineOpen (Stacks.Cech.Kunneth.box r q U V a b) := fun m n a b =>
    Stacks.AlgebraicGeometry.isAffineOpen_inf_preimage_of_isPullback H
      (isAffineOpen_top (Spec (.of A))) (haffU m a) (haffV n b) (by simp) (by simp)
  have hinterW : ∀ (m : ℕ) (t : Fin (m + 1) → I × J),
      CechCochains.inter W t = Stacks.Cech.Kunneth.box r q U V (Prod.fst ∘ t) (Prod.snd ∘ t) :=
    fun m t =>
    le_antisymm (Stacks.Cech.Kunneth.inter_le_box r q U V W (fun _ => le_rfl) t)
      (Stacks.Cech.Kunneth.box_le_inter r q U V W (fun _ => le_rfl) t)
  have hWaff : ∀ t, IsAffineOpen (W t) := fun t => hboxaff 0 0 _ _
  have haffW : ∀ (m : ℕ) (t : Fin (m + 1) → I × J), IsAffineOpen (⨅ k, W (t k)) := fun m t => by
    have := hinterW m t
    simp only [CechCochains.inter] at this
    rw [this]
    exact hboxaff m m _ _
  have hW : (⊤ : P.Opens) = ⨆ t, W t := by
    refine le_antisymm (fun x _ => ?_) le_top
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hU.le (Set.mem_univ (r x)))
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hV.le (Set.mem_univ (q x)))
    refine Opens.mem_iSup.2 ⟨(i, j), ⟨?_, ?_⟩⟩
    · change r x ∈ CechCochains.inter U ![i]
      rw [Stacks.Cech.Kunneth.inter_fin1]; exact hi
    · change q x ∈ CechCochains.inter V ![j]
      rw [Stacks.Cech.Kunneth.inter_fin1]; exact hj
  have hj₁f : j₁ ≫ r ≫ fX = fY := by
    rw [← Category.assoc, hj₁r, Category.assoc, hσ, Category.comp_id]
  have hj₂f : j₂ ≫ r ≫ fX = fX := by rw [← Category.assoc, hj₂r, Category.id_comp]
  have hWU₁ : ∀ b, V b ≤ j₁ ⁻¹ᵁ W (a₀, b) := fun b y hy => by
    refine ⟨?_, ?_⟩
    · change r (j₁ y) ∈ CechCochains.inter U ![a₀]
      rw [Stacks.Cech.Kunneth.inter_fin1, ← Scheme.Hom.comp_apply, hj₁r, Scheme.Hom.comp_apply]
      change fY y ∈ σ ⁻¹ᵁ U a₀
      rw [ha₀]; trivial
    · change q (j₁ y) ∈ CechCochains.inter V ![b]
      rw [Stacks.Cech.Kunneth.inter_fin1, ← Scheme.Hom.comp_apply, hj₁q]
      exact hy
  have hWU₂ : ∀ a, U a ≤ j₂ ⁻¹ᵁ W (a, b₀) := fun a y hy => by
    refine ⟨?_, ?_⟩
    · change r (j₂ y) ∈ CechCochains.inter U ![a]
      rw [Stacks.Cech.Kunneth.inter_fin1, ← Scheme.Hom.comp_apply, hj₂r]
      exact hy
    · change q (j₂ y) ∈ CechCochains.inter V ![b₀]
      rw [Stacks.Cech.Kunneth.inter_fin1, ← Scheme.Hom.comp_apply, hj₂q, Scheme.Hom.comp_apply]
      change fX y ∈ τ ⁻¹ᵁ V b₀
      rw [hb₀]; trivial
  set L₁ := (Scheme.Modules.pullback j₁).obj L
  set L₂ := (Scheme.Modules.pullback j₂).obj L
  have : L₁.IsQuasicoherent := Stacks.Modules.isQuasicoherent_of_isFinitePresentation L₁
  have : L₂.IsQuasicoherent := Stacks.Modules.isQuasicoherent_of_isFinitePresentation L₂
  have hL₁ : IsFlatOver fY.toLRSHom.toShHom L₁ :=
    (isFlatOver_iff_of_iso fY e₁).2 (isFlatOver_unitModule fY)
  have hL₂ : IsFlatOver fX.toLRSHom.toShHom L₂ :=
    (isFlatOver_iff_of_iso fX e₂).2 (isFlatOver_unitModule fX)
  set C := baseAlternatingCechComplex (r ≫ fX) W hW L
  set D₁ := baseAlternatingCechComplex fY V hV L₁
  set D₂ := baseAlternatingCechComplex fX U hU L₂
  set E := baseUnitComplex A
  set ρ₁ := cechModelPullbackMap j₁ (r ≫ fX) fY hj₁f W hW V hV (fun b => (a₀, b)) hWU₁ L
  set ρ₂ := cechModelPullbackMap j₂ (r ≫ fX) fX hj₂f W hW U hU (fun a => (a, b₀)) hWU₂ L
  set t₂ : Γ(L₂, ⊤) := e₂.inv.app ⊤ (1 : Γ(X, ⊤))
  set u := sectionModelMap fX U hU hU.le L₂ t₂
  set d : ℤ := (Fintype.card (I × J) : ℤ) + Fintype.card I + Fintype.card J
  have : C.IsStrictlyLE d :=
    CochainComplex.isStrictlyLE_of_le C (Fintype.card (I × J) : ℤ) d (by omega)
  have : D₁.IsStrictlyLE d :=
    CochainComplex.isStrictlyLE_of_le D₁ (Fintype.card J : ℤ) d (by omega)
  have : D₂.IsStrictlyLE d :=
    CochainComplex.isStrictlyLE_of_le D₂ (Fintype.card I : ℤ) d (by omega)
  have : ∀ i, Module.Flat A (C.X i) := flat_baseAlternatingCechComplex_X (r ≫ fX) W hW L hWaff hL
  have : ∀ i, Module.Flat A (D₁.X i) := flat_baseAlternatingCechComplex_X fY V hV L₁ hVaff hL₁
  have : ∀ i, Module.Flat A (D₂.X i) := flat_baseAlternatingCechComplex_X fX U hU L₂ hUaff hL₂
  have hCp : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj C) :=
    StacksDraft.Perfect.isPerfect_of_iso
      (alternatingCechIsoDerivedGlobalSectionsOverBase (r ≫ fX) W hW L haffW)
      (isPerfect_derivedGlobalSectionsOverBase_of_isProper (r ≫ fX) L hL)
  have hD₁p : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj D₁) :=
    StacksDraft.Perfect.isPerfect_of_iso
      (alternatingCechIsoDerivedGlobalSectionsOverBase fY V hV L₁ haffV)
      (isPerfect_derivedGlobalSectionsOverBase_of_isProper fY L₁ hL₁)
  have hD₂p : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj D₂) :=
    StacksDraft.Perfect.isPerfect_of_iso
      (alternatingCechIsoDerivedGlobalSectionsOverBase fX U hU L₂ haffU)
      (isPerfect_derivedGlobalSectionsOverBase_of_isProper fX L₂ hL₂)
  have ha₁₀ : j₁₀ ≫ π₀ = fY₀ := by
    rw [← hπ₀, ← Category.assoc, hj₁₀r, Category.assoc, hσ₀, Category.comp_id]
  have ha₂₀ : j₂₀ ≫ π₀ = fX₀ := by rw [← hπ₀, ← Category.assoc, hj₂₀r, Category.id_comp]
  have : IsAffineHom gX := MorphismProperty.of_isPullback hsqX.flip inferInstance
  have : IsAffineHom gY := MorphismProperty.of_isPullback hsqY.flip inferInstance
  have : IsAffineHom gP := MorphismProperty.of_isPullback hsqP.flip inferInstance
  set U₀ : I → X₀.Opens := fun i => gX ⁻¹ᵁ U i
  set V₀ : J → Y₀.Opens := fun j => gY ⁻¹ᵁ V j
  set W₀ : I × J → P₀.Opens := fun t => gP ⁻¹ᵁ W t
  have hinterU : ∀ {m : ℕ} (a : Fin m → I),
      CechCochains.inter U₀ a = gX ⁻¹ᵁ CechCochains.inter U a := fun a =>
    Stacks.Cech.inter_eq_preimage gX U U₀ (Equiv.refl I) (preimage_eq_preimage_equivRefl gX U) a
  have hinterV : ∀ {m : ℕ} (b : Fin m → J),
      CechCochains.inter V₀ b = gY ⁻¹ᵁ CechCochains.inter V b := fun b =>
    Stacks.Cech.inter_eq_preimage gY V V₀ (Equiv.refl J) (preimage_eq_preimage_equivRefl gY V) b
  have hbox₀ : ∀ {m n : ℕ} (a : Fin m → I) (b : Fin n → J),
      Stacks.Cech.Kunneth.box r₀ q₀ U₀ V₀ a b = gP ⁻¹ᵁ Stacks.Cech.Kunneth.box r q U V a b :=
    fun a b => by
      change r₀ ⁻¹ᵁ CechCochains.inter U₀ a ⊓ q₀ ⁻¹ᵁ CechCochains.inter V₀ b =
        gP ⁻¹ᵁ (r ⁻¹ᵁ CechCochains.inter U a ⊓ q ⁻¹ᵁ CechCochains.inter V b)
      rw [hinterU, hinterV, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hr₀, hq₀,
        Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
      rfl
  have hUa₀ : ∀ (m : ℕ) (a : Fin (m + 1) → I), IsAffineOpen (CechCochains.inter U₀ a) :=
    fun m a => by rw [hinterU]; exact (haffU m a).preimage gX
  have hVa₀ : ∀ (n : ℕ) (b : Fin (n + 1) → J), IsAffineOpen (CechCochains.inter V₀ b) :=
    fun n b => by rw [hinterV]; exact (haffV n b).preimage gY
  have hWa₀ : ∀ (m n : ℕ) (a : Fin (m + 1) → I) (b : Fin (n + 1) → J),
      IsAffineOpen (Stacks.Cech.Kunneth.box r₀ q₀ U₀ V₀ a b) :=
    fun m n a b => by rw [hbox₀]; exact (hboxaff m n a b).preimage gP
  have ha₀' : σ₀ ⁻¹ᵁ U₀ a₀ = ⊤ := by
    change σ₀ ⁻¹ᵁ (gX ⁻¹ᵁ U a₀) = ⊤
    rw [← Scheme.Hom.comp_preimage, hσ₀g, Scheme.Hom.comp_preimage, ha₀, Scheme.Hom.preimage_top]
  have hb₀' : τ₀ ⁻¹ᵁ V₀ b₀ = ⊤ := by
    change τ₀ ⁻¹ᵁ (gY ⁻¹ᵁ V b₀) = ⊤
    rw [← Scheme.Hom.comp_preimage, hτ₀g, Scheme.Hom.comp_preimage, hb₀, Scheme.Hom.preimage_top]
  set x₀ := fibreGenerator χ hsqP W hW hWaff L e₀
  obtain ⟨hx₀d, hα⟩ := fibreGenerator_spec χ hsqP W hW hWaff L e₀ hΓP₀
  obtain ⟨hβ₁, hy₁ne⟩ := fibre_sectionCochain_generator χ hsqY hΓY₀ L₁ V hV hVaff e₁
  obtain ⟨hβ₂, hy₂ne⟩ := fibre_sectionCochain_generator χ hsqX hΓX₀ L₂ U hU hUaff e₂
  have hγ := fibreGenerator_map_ne_zero χ j₁ hj₁f hsqP hsqY j₁₀ ha₁₀ hj₁₀g W hW hWaff V hV hVaff
    (fun b => (a₀, b)) hWU₁ L e₀ hΓY₀
  set eE := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)
  have hz : ∀ z : (StacksDraft.Perfect.extendScalarsCx χ E).X 0, ∃ c : κ,
      z = c • (show (StacksDraft.Perfect.extendScalarsCx χ E).X 0 from
        (1 : κ) ⊗ₜ[A, χ] eE.inv (1 : A)) := fun z => by
    obtain ⟨c, hc⟩ := exists_eq_tmul_of_generator χ (eE.inv (1 : A)) baseUnitComplex_gen z
    refine ⟨c, hc.trans ?_⟩
    exact ((ModuleCat.ExtendScalars.smul_tmul χ c 1 (eE.inv (1 : A))).trans
      (congrArg (fun k : κ => k ⊗ₜ[A, χ] eE.inv (1 : A)) (mul_one c))).symm
  have hu : (StacksDraft.Perfect.extendScalarsCxMap u χ).f 0
      (show (StacksDraft.Perfect.extendScalarsCx χ E).X 0 from
        (1 : κ) ⊗ₜ[A, χ] eE.inv (1 : A)) =
      (show (StacksDraft.Perfect.extendScalarsCx χ D₂).X 0 from
        (1 : κ) ⊗ₜ[A, χ] sectionCochain fX U hU L₂ t₂ (1 : A)) := by
    change ((ModuleCat.extendScalars.{u, u, u} χ).map (u.f 0)) _ = _
    rw [ModuleCat.ExtendScalars.map_tmul, sectionModelMap_f_zero_apply]
    rfl
  have h1 : ∀ x : (StacksDraft.Perfect.extendScalarsCx χ C).X 1,
      (StacksDraft.Perfect.extendScalarsCx χ C).d 1 2 x = 0 →
      ∀ (y₁ : (StacksDraft.Perfect.extendScalarsCx χ D₁).X 0)
        (y₂ : (StacksDraft.Perfect.extendScalarsCx χ D₂).X 0),
        (StacksDraft.Perfect.extendScalarsCxMap ρ₁ χ).f 1 x =
          (StacksDraft.Perfect.extendScalarsCx χ D₁).d 0 1 y₁ →
        (StacksDraft.Perfect.extendScalarsCxMap ρ₂ χ).f 1 x =
          (StacksDraft.Perfect.extendScalarsCx χ D₂).d 0 1 y₂ →
        ∃ w : (StacksDraft.Perfect.extendScalarsCx χ C).X 0,
          (StacksDraft.Perfect.extendScalarsCx χ C).d 0 1 w = x := by
    intro x hx y₁ y₂ hy₁ hy₂
    set T := fibreTransport χ hsqP L W hW hWaff
    set Z := (T 1).hom x
    have hZ : CechCochains.cechD W₀ ((Scheme.Modules.pullback gP).obj L).presheaf 1 Z.1 = 0 := by
      have h := fibreTransport_d_apply χ hsqP L W hW hWaff 1 x
      have hx' : (StacksDraft.Perfect.extendScalarsCx χ C).d ((1 : ℕ) : ℤ) ((1 + 1 : ℕ) : ℤ) x =
        0 := hx
      rw [hx', map_zero] at h
      exact congrArg Subtype.val h.symm
    have ht₁ := exists_cechD_eq_cochainPullback χ j₁ hj₁f hsqP hsqY j₁₀ ha₁₀ hj₁₀g W hW hWaff V
      hV hVaff (fun b => (a₀, b)) hWU₁ L x y₁ hy₁
    have ht₂ := exists_cechD_eq_cochainPullback χ j₂ hj₂f hsqP hsqX j₂₀ ha₂₀ hj₂₀g W hW hWaff U
      hU hUaff (fun a => (a, b₀)) hWU₂ L x y₂ hy₂
    obtain ⟨e', he'⟩ := Stacks.Cech.Kunneth.exists_cechD_eq_of_faces_of_iso H₀ U₀ V₀ W₀
      (fun t => (hbox₀ ![t.1] ![t.2]).le) (fun t => (hbox₀ ![t.1] ![t.2]).ge) hUa₀ hVa₀ hWa₀
      (top_eq_iSup_preimage gX U hU).le (top_eq_iSup_preimage gY V hV).le hΓX₀ hΓY₀
      σ₀ hσ₀ a₀ ha₀' j₁₀ hj₁₀r hj₁₀q τ₀ hτ₀ b₀ hb₀' j₂₀ hj₂₀r hj₂₀q
      (Stacks.Cech.preimage_le_preimage_of_comm j₁ gP gY j₁₀ hj₁₀g W V (fun b => (a₀, b)) hWU₁)
      (Stacks.Cech.preimage_le_preimage_of_comm j₂ gP gX j₂₀ hj₂₀g W U (fun a => (a, b₀)) hWU₂)
      ((Scheme.Modules.pullback gP).obj L) e₀ Z.1 hZ ht₁ ht₂
    refine ⟨(T 0).inv ⟨e', isAlternating_zero W₀ _ e'⟩, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (T 1).hom).1
    change (T (0 + 1)).hom ((StacksDraft.Perfect.extendScalarsCx χ C).d ((0 : ℕ) : ℤ)
      ((0 + 1 : ℕ) : ℤ) _) = (T 1).hom x
    rw [fibreTransport_d_apply]
    have hv : (T 0).hom ((T 0).inv ⟨e', isAlternating_zero W₀ _ e'⟩) =
        ⟨e', isAlternating_zero W₀ _ e'⟩ := Iso.inv_hom_id_apply _ _
    refine (congrArg _ hv).trans ?_
    exact Subtype.ext he'
  obtain ⟨a, ha, hsurj⟩ := StacksDraft.Perfect.exists_away_of_fibre_two_of_generators d hCp hD₁p
    hD₂p (isPerfect_baseUnitComplex A) (by omega) ρ₁ ρ₂ u p x₀ hx₀d hα _ hβ₁ _ hy₂ne hβ₂ _ hz hu
    hγ h1
  set Y₁ := sectionCochain fY V hV L₁ (e₁.inv.app ⊤ (1 : Γ(Y, ⊤))) (1 : A)
  have hY₁ : D₁.d 0 1 Y₁ = 0 :=
    congr($(sectionCochain_comp_d fY V hV hV.le L₁ (e₁.inv.app ⊤ (1 : Γ(Y, ⊤)))) (1 : A))
  obtain ⟨x, -, n, hx, hρx, -⟩ := hsurj Y₁ hY₁
  obtain ⟨s, hs⟩ : ∃ s : Γ(L, ⊤), (baseAlternatingCechComplexXIso (r ≫ fX) W hW L 0).hom x =
      Stacks.Cech.sectionsToAlternatingₗ (r ≫ fX) W L (fun _ => le_top) s := by
    let := Stacks.Cech.sectionsModule (r ≫ fX) L ⊤
    let := Stacks.Cech.cochainModule (r ≫ fX) W L 0
    let := Stacks.Cech.cochainModule (r ≫ fX) W L 1
    set xs : Stacks.Cech.alternatingSubmodule (r ≫ fX) W L 0 :=
      (baseAlternatingCechComplexXIso (r ≫ fX) W hW L 0).hom x with hxs
    have hxc : Stacks.Cech.alternatingCechModuleD (r ≫ fX) W L 0 xs = 0 := by
      have h := congr($(d_comp_baseAlternatingCechComplexXIso_hom (r ≫ fX) W hW L 0) x)
      have hx' : C.d ((0 : ℕ) : ℤ) ((0 + 1 : ℕ) : ℤ) x = 0 := hx
      rw [ConcreteCategory.comp_apply, hx', map_zero, ConcreteCategory.comp_apply,
        Stacks.Cech.alternatingCechModuleComplex_d] at h
      exact h.symm
    obtain ⟨s, hs⟩ : xs ∈
        LinearMap.range (Stacks.Cech.sectionsToAlternatingₗ (r ≫ fX) W L (fun _ => le_top)) :=
      (Stacks.Cech.range_sectionsToAlternatingₗ (r ≫ fX) W L (fun _ => le_top) hW.le) ▸
        LinearMap.mem_ker.2 hxc
    exact ⟨s, hs.symm⟩
  refine ⟨s, fun h0 => ?_⟩
  have hx0 : (show (StacksDraft.Perfect.extendScalarsCx χ C).X 0 from (1 : κ) ⊗ₜ[A, χ] x) = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (fibreTransport χ hsqP L W hW hWaff 0).hom).1
    rw [map_zero]
    let : Algebra A κ := χ.toAlgebra
    refine (fibreTransport_one_tmul χ hsqP L W hW hWaff 0 x).trans ?_
    rw [hs, Stacks.Cech.alternatingCochainBaseChangeₗ_sectionsToAlternatingₗ, h0, map_zero]
    rfl
  have himg : (StacksDraft.Perfect.extendScalarsCxMap ρ₁ χ).f 0
      (show (StacksDraft.Perfect.extendScalarsCx χ C).X 0 from (1 : κ) ⊗ₜ[A, χ] x) =
      χ a ^ n • (show (StacksDraft.Perfect.extendScalarsCx χ D₁).X 0 from
        (1 : κ) ⊗ₜ[A, χ] Y₁) := by
    change ((ModuleCat.extendScalars.{u, u, u} χ).map (ρ₁.f 0)) _ = _
    rw [ModuleCat.ExtendScalars.map_tmul, hρx]
    refine (TensorProduct.smul_tmul (R := A) (a ^ n)
      (show (ModuleCat.restrictScalars.{u} χ).obj (ModuleCat.of κ κ) from (1 : κ)) Y₁).symm.trans ?_
    refine Eq.trans ?_ (ModuleCat.ExtendScalars.smul_tmul χ (χ a ^ n) 1 Y₁).symm
    congr 1
    change χ (a ^ n) * 1 = χ a ^ n * 1
    rw [map_pow]
  rw [hx0, map_zero] at himg
  have hna : χ a ^ n ≠ 0 :=
    pow_ne_zero _ fun h => ha (Ideal.algebraMap_residueField_eq_zero.1 h)
  exact hy₁ne ((smul_eq_zero.1 himg.symm).resolve_left hna)

end Main

end Stacks.Cube

end
