module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactSupportDuality.CompactSupportCohomology
public import StacksFrontier.AlgebraicGeometry.Duality.CompactSupportDuality.ProperDuality
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentDuality

/-!
# Duality for compactly supported cohomology: the compactification

Let `p : U ⟶ Spec k` be separated of finite type over a field, with a compactification
`j : U ⟶ X`, `q : X ⟶ Spec k` proper. For `L ∈ D^b_{Coh}(𝒪_U)` and a vector space `V`
identified with `Hom_U(L, ω_X^•|_U)`, this file identifies the dual of `V` with
`Hom_{Pro}(𝒪_X, Rj_! L)`, by duality on the proper scheme `X` ([Stacks, Tag 0FVV] part (5),
`AlgebraicGeometry.bijective_compPairing_properTrace`) applied termwise to a Deligne system of
`L` ([Stacks, Tag 0G2H]), and then with `H^0_c(U, L) = Hom_{Pro}(𝒪_{Spec k}, Rg_! L)`; this is
the part of [Stacks, Tag 0G5A] that takes place on `X`.

## Main definitions

* `AlgebraicGeometry.compactificationDualizingObj`: `ω_X^•` as an object of `D^b_{Coh}(𝒪_X)`.
* `AlgebraicGeometry.compactificationTrace`: the trace `Hom_X(𝒪_X, ω_X^•) ⟶ k`.
* `AlgebraicGeometry.compactSupportDualityOfPoints`: the isomorphism `V^∨ ≅ H^i_c(U, L)` for `V`
  identified with `Hom_U(L[i], ω_X^•|_U)`.

## Main results

* `AlgebraicGeometry.bijective_compPairing_compactificationTrace`: perfectness of the
  composition pairing on `D^b_{Coh}(𝒪_X)`.
* `AlgebraicGeometry.isHomeomorph_compactSupportDualityOfPoints`: the duality isomorphism is a
  homeomorphism for the limit topologies.
* `AlgebraicGeometry.compactSupportDualityOfPoints_naturality`: the duality isomorphism is natural
  in `L`.

## Implementation notes

The derived categories are at `CategoryTheory.HasDerivedCategory.standard`, the model of
`AlgebraicGeometry.BoundedCoherentDerived`, of the Deligne systems of
`AlgebraicGeometry.DeligneSystem.values`, of `Stacks.Duality.boundedCoherentDuality`
([Stacks, Tag 0A89]) and of `moduleFinite_ext_of_proper` ([Stacks, Tag 0D0D]); it is named in
each statement that needs it by `letI`, inlined at elaboration.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Duality

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {U : Scheme.{u}} {p : U ⟶ Spec (CommRingCat.of k)}
  (c : CompactificationOf (Over.mk p))

attribute [local instance] linearModulesCompactification linearModulesSpecField

/-- The canonical `k`-linear structure on `𝒪_U`-modules. -/
local instance linearModulesSource : Linear k (Over.mk p).left.Modules :=
  modulesLinear k (Over.mk p)

/-- **`ω_X^•` is an object of `D^b_{Coh}(𝒪_X)`**: it is `R𝓗om(𝒪_X, ω_X^•)`, and `R𝓗om(-, ω_X^•)`
preserves `D^b_{Coh}(𝒪_X)` for a dualizing complex ([Stacks, Tag 0A89]). -/
theorem boundedCoherentDerived_standardRelativeDualizingComplex :
    boundedCoherentDerived c.space (standardRelativeDualizingComplex c.toBase) := by
  let _ := HasDerivedCategory.standard (SheafOfModules
    (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite c.space.sheaf).O))
  let _ := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
  let _ := HasDerivedCategory.standard c.space.Modules
  let _ := HasDerivedCategory.standard (Over.mk p).left.Modules
  have hO : DerivedCategoryB.derivedCategoryBBounded (A := c.space.Modules)
      (isCoherentSheaf c.space) (structureSheafBoundedCoherent c.space).obj :=
    (structureSheafBoundedCoherent c.space).property
  obtain ⟨⟨hb, ha⟩, hc⟩ := derivedCategoryBBounded_derivedSheafHom c.space
    (isDualizingComplex_standardRelativeDualizingComplex c.toBase) _ hO
  let e := RingedSite.derivedStructureSheafHomIso (Stacks.SheafOfModules.ringedSite c.space.sheaf)
    (standardRelativeDualizingComplex c.toBase)
  exact ⟨⟨DerivedCategoryB.isBoundedBelow_of_iso e hb, DerivedCategoryB.isBoundedAbove_of_iso e ha⟩,
    fun i => isCoherent_of_modulesIso ((DerivedCategory.homologyFunctor c.space.Modules i).mapIso e)
      (hc i)⟩

/-- `ω_X^•` as an object of `D^b_{Coh}(𝒪_X)`. -/
abbrev compactificationDualizingObj : BoundedCoherentDerived c.space :=
  letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
  letI := HasDerivedCategory.standard c.space.Modules
  letI := HasDerivedCategory.standard (Over.mk p).left.Modules
  ⟨standardRelativeDualizingComplex c.toBase,
    boundedCoherentDerived_standardRelativeDualizingComplex c⟩

/-- **The trace** `Hom_X(𝒪_X, ω_X^•) ⟶ k` on `D^b_{Coh}(𝒪_X)`, `AlgebraicGeometry.properTrace`. -/
def compactificationTrace :
    letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
    letI := HasDerivedCategory.standard c.space.Modules
    letI := HasDerivedCategory.standard (Over.mk p).left.Modules
    (unitBoundedCoherent c.space ⟶ compactificationDualizingObj c) →ₗ[k] k :=
  letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
  letI := HasDerivedCategory.standard c.space.Modules
  letI := HasDerivedCategory.standard (Over.mk p).left.Modules
  properTrace c.toBase ∘ₗ
    (boundedCoherentHomLinearEquiv (unitBoundedCoherent c.space)
      (compactificationDualizingObj c)).toLinearMap

/-- **[Stacks, Tag 0FVV] part (5) in degree zero on `D^b_{Coh}(𝒪_X)`**: for `N ∈ D^b_{Coh}(𝒪_X)`,
`g ↦ (a ↦ t(a ≫ g))` identifies `Hom_X(N, ω_X^•)` with the dual of `Hom_X(𝒪_X, N)`. -/
theorem bijective_compPairing_compactificationTrace (N : BoundedCoherentDerived c.space) :
    letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
    letI := HasDerivedCategory.standard c.space.Modules
    letI := HasDerivedCategory.standard (Over.mk p).left.Modules
    Function.Bijective (ProSeq.compPairing (compactificationTrace c) N) := by
  let _ := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
  let _ := HasDerivedCategory.standard c.space.Modules
  let _ := HasDerivedCategory.standard (Over.mk p).left.Modules
  have hN : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor c.space.Modules i).obj N.obj).IsQuasicoherent :=
    fun i => have := N.property.2 i; isQuasicoherent_of_isCoherent _
  let eN := boundedCoherentHomLinearEquiv (k := k) (unitBoundedCoherent c.space) N
  have hc : (ProSeq.compPairing (compactificationTrace c) N :
      (N ⟶ compactificationDualizingObj c) →
        Module.Dual k (unitBoundedCoherent c.space ⟶ N)) =
      eN.dualMap ∘ ProSeq.compPairing (properTrace c.toBase) N.obj ∘
        (boundedCoherentHomLinearEquiv (k := k) N (compactificationDualizingObj c)) := by
    funext g
    ext a
    simp only [Function.comp_apply, LinearEquiv.dualMap_apply, ProSeq.compPairing_apply_apply,
      compactificationTrace, LinearMap.comp_apply, LinearEquiv.coe_coe, eN]
    rw [boundedCoherentHomLinearEquiv_apply, boundedCoherentHomLinearEquiv_apply,
      boundedCoherentHomLinearEquiv_apply, ObjectProperty.FullSubcategory.comp_hom]
  rw [hc]
  exact eN.dualMap.bijective.comp ((bijective_compPairing_properTrace c.toBase N.obj hN).comp
    (boundedCoherentHomLinearEquiv (k := k) N _).bijective)

/-- **`Hom_X(𝒪_X, N)` is finite dimensional** for `N ∈ D^b_{Coh}(𝒪_X)`, `X` proper over `k`
([Stacks, Tag 0D0D]). -/
public instance finiteDimensional_unitBoundedCoherent_hom (N : BoundedCoherentDerived c.space) :
    letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
    letI := HasDerivedCategory.standard c.space.Modules
    letI := HasDerivedCategory.standard (Over.mk p).left.Modules
    FiniteDimensional k (unitBoundedCoherent c.space ⟶ N) := by
  let _ := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
  let _ := HasDerivedCategory.standard c.space.Modules
  let _ := HasDerivedCategory.standard (Over.mk p).left.Modules
  have : IsProper (Over.mk c.toBase).hom := inferInstanceAs (IsProper c.toBase)
  have h1 : Module.Finite k (derivedUnitObject c.space ⟶ (shiftFunctor _ (0 : ℤ)).obj N.obj) :=
    Stacks.AlgebraicGeometry.ProperSupportCoherent.moduleFinite_ext_of_proper
      (Over.mk c.toBase) (derivedUnitObject c.space) N.obj
      ⟨(unitBoundedCoherent c.space).property.1.2, (unitBoundedCoherent c.space).property.2⟩
      ⟨N.property.1.1, N.property.2⟩ 0
  have h2 : Module.Finite k (derivedUnitObject c.space ⟶ N.obj) :=
    Module.Finite.equiv (ProSeq.postcompLinearEquiv (k := k)
      ((shiftFunctorZero (DerivedCategory c.space.Modules) ℤ).app N.obj))
  exact Module.Finite.equiv (boundedCoherentHomLinearEquiv (unitBoundedCoherent c.space) N).symm

/-- Restriction `D^b_{Coh}(𝒪_X) ⥤ D^b_{Coh}(𝒪_U)` along the compactification is `k`-linear. -/
public lemma restrictBoundedCoherentLift_map_smul {N N' : BoundedCoherentDerived c.space}
    (a : k) (g : N ⟶ N') :
    letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
    letI := HasDerivedCategory.standard c.space.Modules
    letI := HasDerivedCategory.standard (Over.mk p).left.Modules
    (restrictBoundedCoherentLift c.immersion).map (a • g) =
      a • (restrictBoundedCoherentLift c.immersion).map g := by
  let _ := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
  let _ := HasDerivedCategory.standard c.space.Modules
  let _ := HasDerivedCategory.standard (Over.mk p).left.Modules
  have := mapDerivedCategory_restrictFunctor_linear c.toBase (Over.mk p).hom c.immersion
    (Over.w c.obj.hom)
  exact ObjectProperty.hom_ext _
    (Functor.map_smul (Scheme.Modules.restrictFunctor c.immersion).mapDerivedCategory a g.hom)

/-- The point `K ≅ K_n|_U ⟶ g|_U` of `Rj_! K` at `N` attached to `g : K_n ⟶ N`, as a `k`-linear map
in `g`. -/
def deligneClassLinearMap (L : BoundedCoherentDerived (Over.mk p).left) (n : ℕ)
    (N : BoundedCoherentDerived c.space) :
    letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
    letI := HasDerivedCategory.standard c.space.Modules
    letI := HasDerivedCategory.standard (Over.mk p).left.Modules
    (((DeligneSystem.values c.immersion).system L).obj (op n) ⟶ N) →ₗ[k]
      (L ⟶ (restrictBoundedCoherentLift c.immersion).obj N) :=
  letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
  letI := HasDerivedCategory.standard c.space.Modules
  letI := HasDerivedCategory.standard (Over.mk p).left.Modules
  { toFun g := ((DeligneSystem.values c.immersion).restrictIso L).inv.app (op n) ≫
      (restrictBoundedCoherentLift c.immersion).map g
    map_add' g g' := by rw [Functor.map_add, Preadditive.comp_add]
    map_smul' a g := by
      rw [restrictBoundedCoherentLift_map_smul, Linear.comp_smul]
      rfl }

variable {V : Type*} [AddCommGroup V] [Module k V]

/-- The linear maps `Hom(K_n, ω_X^•) ⟶ V` of the colimit `V = colim_n Hom(K_n, ω_X^•)`. -/
def pointsColimitMap (L : BoundedCoherentDerived (Over.mk p).left) (i : ℤ)
    (ρ : V ≃ₗ[k] (L⟦i⟧ ⟶ (restrictBoundedCoherentLift c.immersion).obj
      (compactificationDualizingObj c))) (n : ℕ) :
    letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
    letI := HasDerivedCategory.standard c.space.Modules
    letI := HasDerivedCategory.standard (Over.mk p).left.Modules
    (((DeligneSystem.values c.immersion).system (L⟦i⟧)).obj (op n) ⟶
      compactificationDualizingObj c) →ₗ[k] V :=
  letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
  letI := HasDerivedCategory.standard c.space.Modules
  letI := HasDerivedCategory.standard (Over.mk p).left.Modules
  ρ.symm.toLinearMap ∘ₗ deligneClassLinearMap c (L⟦i⟧) n (compactificationDualizingObj c)

/-- Under `ρ`, the image of `g : K_n ⟶ ω_X^•` by `pointsColimitMap` is the point of
`Rj_!(L[i])` at `ω_X^•` that `extensionByZeroIso` attaches to the stage-`n` class of `g`. -/
lemma pointsColimitMap_spec (L : BoundedCoherentDerived (Over.mk p).left) (i : ℤ)
    (ρ : V ≃ₗ[k] (L⟦i⟧ ⟶ (restrictBoundedCoherentLift c.immersion).obj
      (compactificationDualizingObj c))) (n : ℕ)
    (g : ((DeligneSystem.values c.immersion).system (L⟦i⟧)).obj (op n) ⟶
      compactificationDualizingObj c) :
    letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
    letI := HasDerivedCategory.standard c.space.Modules
    letI := HasDerivedCategory.standard (Over.mk p).left.Modules
    ρ.toEquiv (pointsColimitMap c L i ρ n g) =
      (extensionByZeroIso _ (DeligneSystem.values c.immersion).toAssignment (L⟦i⟧)).hom.unop.hom.app
        (compactificationDualizingObj c)
        ((Pro.seqHomColimIso _).inv.app _ (Pro.seqStage _ g)) :=
  (ρ.apply_symm_apply _).trans
    (ProSeq.extensionByZeroIso_hom_app_seqStage (DeligneSystem.values c.immersion) (L⟦i⟧) g).symm

/-- **Duality for compactly supported cohomology, on the compactification.** For
`L ∈ D^b_{Coh}(𝒪_U)`, `i ∈ ℤ` and a vector space `V` identified, `k`-linearly, with
`Hom_U(L[i], ω_X^•|_U)`, the dual of `V` is `H^i_c(U, L)`. -/
def compactSupportDualityOfPoints (L : BoundedCoherentDerived (Over.mk p).left) (i : ℤ)
    (ρ : V ≃ₗ[k] (L⟦i⟧ ⟶ (restrictBoundedCoherentLift c.immersion).obj
      (compactificationDualizingObj c))) :
    letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
    letI := HasDerivedCategory.standard c.space.Modules
    letI := HasDerivedCategory.standard (Over.mk p).left.Modules
    Module.Dual k V ≃ₗ[k] compactSupportCohomology c L i :=
  letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
  letI := HasDerivedCategory.standard c.space.Modules
  letI := HasDerivedCategory.standard (Over.mk p).left.Modules
  ProSeq.proDualityLinearEquiv (properPushforwardBoundedCoherent c.toBase)
    (structureSheafPushforwardHomLinearEquiv c)
    (fun g a => structureSheafPushforwardHomLinearEquiv_comp c g a) (compactificationTrace c)
    (extensionByZeroIso _ (DeligneSystem.values c.immersion).toAssignment (L⟦i⟧)) ρ.toEquiv
    (pointsColimitMap c L i ρ) (pointsColimitMap_spec c L i ρ)
    (fun _ => bijective_compPairing_compactificationTrace c _)

/-- **The duality isomorphism on the compactification is a homeomorphism**, for the limit
topology on the dual of `V` (`Module.Dual.limitTopology`) and the limit topology of
[Stacks, Section 0G59] on `H^i_c(U, L)`. -/
theorem isHomeomorph_compactSupportDualityOfPoints (L : BoundedCoherentDerived (Over.mk p).left)
    (i : ℤ) (ρ : V ≃ₗ[k] (L⟦i⟧ ⟶ (restrictBoundedCoherentLift c.immersion).obj
      (compactificationDualizingObj c))) :
    letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
    letI := HasDerivedCategory.standard c.space.Modules
    letI := HasDerivedCategory.standard (Over.mk p).left.Modules
    letI := Module.Dual.limitTopology k V
    IsHomeomorph (compactSupportDualityOfPoints c L i ρ) :=
  ProSeq.isHomeomorph_proDualityLinearEquiv (properPushforwardBoundedCoherent c.toBase)
    (structureSheafPushforwardHomLinearEquiv c)
    (fun g a => structureSheafPushforwardHomLinearEquiv_comp c g a) (compactificationTrace c)
    (extensionByZeroIso _ (DeligneSystem.values c.immersion).toAssignment (L⟦i⟧)) ρ.toEquiv
    (pointsColimitMap c L i ρ) (pointsColimitMap_spec c L i ρ)
    (fun _ => bijective_compPairing_compactificationTrace c _)

/-- **Naturality of the duality isomorphism on the compactification.** A morphism `f : L ⟶ L'`
and a linear map `φ : V' ⟶ V` compatible with the identifications
(`f[i] ≫ ρ' v' = ρ (φ v')`) carry `l ↦ l ∘ φ` to the map `H^i_c(U, L) ⟶ H^i_c(U, L')` induced
by `f`. -/
theorem compactSupportDualityOfPoints_naturality {L L' : BoundedCoherentDerived (Over.mk p).left}
    (f : L ⟶ L') (i : ℤ) {V' : Type*} [AddCommGroup V'] [Module k V']
    (ρ : V ≃ₗ[k] (L⟦i⟧ ⟶ (restrictBoundedCoherentLift c.immersion).obj
      (compactificationDualizingObj c)))
    (ρ' : V' ≃ₗ[k] (L'⟦i⟧ ⟶ (restrictBoundedCoherentLift c.immersion).obj
      (compactificationDualizingObj c)))
    (φ : V' →ₗ[k] V) (hφ : ∀ v' : V', f⟦i⟧' ≫ ρ' v' = ρ (φ v')) (l : Module.Dual k V) :
    letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
    letI := HasDerivedCategory.standard c.space.Modules
    letI := HasDerivedCategory.standard (Over.mk p).left.Modules
    compactSupportDualityOfPoints c L' i ρ' (l ∘ₗ φ) =
      compactSupportCohomologyMap c f i (compactSupportDualityOfPoints c L i ρ l) :=
  ProSeq.proDualityLinearEquiv_naturality (properPushforwardBoundedCoherent c.toBase)
    (structureSheafPushforwardHomLinearEquiv c)
    (fun g a => structureSheafPushforwardHomLinearEquiv_comp c g a) (compactificationTrace c)
    (extensionByZeroIso _ (DeligneSystem.values c.immersion).toAssignment (L⟦i⟧)) ρ.toEquiv
    (pointsColimitMap c L i ρ) (pointsColimitMap_spec c L i ρ)
    (fun _ => bijective_compPairing_compactificationTrace c _)
    (extensionByZeroIso _ (DeligneSystem.values c.immersion).toAssignment (L'⟦i⟧)) ρ'.toEquiv
    (pointsColimitMap c L' i ρ') (pointsColimitMap_spec c L' i ρ')
    (fun _ => bijective_compPairing_compactificationTrace c _)
    ((extensionByZeroOpenImmersion c.immersion).map (f⟦i⟧')) φ hφ l

end AlgebraicGeometry

end
