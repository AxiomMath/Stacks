module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorDegreeZero
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorHomologyEdge
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.BoundedBelowDerivedDirectImage
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Degree-zero hypercohomology of a derived direct image

Let `f : X ⟶ S` be a morphism of schemes and let `M` be an object of `D(𝒪_X)` with no cohomology
in negative degrees. Then the degree-zero hypercohomology of `Rf_*M` on `S` is the module of
global sections of `H^0(M)`:

`Hom_{D(𝒪_S)}(𝒪_S[0], Rf_*M) ≃ Γ(X, H^0(M))`,

naturally in `M`. This is the composite of three canonical identifications: for an object `Y` of
`D(𝒪_S)` with no cohomology in negative degrees, a morphism `𝒪_S[0] ⟶ Y` is the same as a
morphism `𝒪_S ⟶ H^0(Y)`; the edge map `H^0(Rf_*M) ⟶ f_*H^0(M)` is an isomorphism, `Rf_*` being
left t-exact and `R^0f_* = f_*` because `f_*` is left exact; and a morphism `𝒪_S ⟶ f_*N` is a
global section of `f_*N`, that is a global section of `N` over `f⁻¹(S) = X`. This is the
degree-zero identification used in [Stacks, Tag 0G5C].

For a complex `G` of modules concentrated in degrees `≥ 0` the degree-zero cohomology is the
kernel of `d^0 : G^0 ⟶ G^1`; we record the resulting monomorphism `H^0(G) ⟶ G^0` and, for modules
on a scheme, the description of its image on global sections as the sections killed by `d^0`.

## Main definitions

* `AlgebraicGeometry.derivedPushforwardHomologyEdge`: the edge transformation
  `H^0 ∘ Rf_* ⟶ f_* ∘ H^0`.
* `AlgebraicGeometry.derivedPushforwardHomEquiv`: the identification
  `Hom_{D(𝒪_S)}(𝒪_S[0], Rf_*M) ≃ Γ(X, H^0(M))` for `M` in `D^{≥ 0}(𝒪_X)`.
* `DerivedCategory.homologyZeroIsoCycles`: for a complex `G` strictly in degrees `≥ 0`, the
  isomorphism of `H^0(G)` with the cycles of `G` in degree `0`.
* `DerivedCategory.homologyZeroToX`: the resulting monomorphism `H^0(G) ⟶ G^0`.

## Main results

* `AlgebraicGeometry.derivedPushforwardHomEquiv_comp`: `derivedPushforwardHomEquiv` is natural
  in `M`.
* `DerivedCategory.homologyZeroToX_naturality`: `homologyZeroToX` is natural in `G`.
* `AlgebraicGeometry.mem_range_homologyZeroToX_app_top_iff`: a global section of `G^0` comes from
  a global section of `H^0(G)` if and only if `d^0` kills it.

## References

* [Stacks Project, Tag 0G5C](https://stacks.math.columbia.edu/tag/0G5C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The edge transformation of the derived direct image in degree zero**,
`H^0(Rf_*M) ⟶ f_*H^0(M)`, natural in `M`. It is `Stacks.DerivedFunctor.homologyEdge` for the
right derived functor `Rf_*` of the left exact functor `f_*`, the agreement `R^0f_* ≅ f_*` on
modules being `Stacks.DerivedFunctor.derivedDegreeNatIsoOfKInjective`. -/
def derivedPushforwardHomologyEdge :
    derivedPushforwardModules f ⋙ DerivedCategory.homologyFunctor S.Modules 0 ⟶
      DerivedCategory.homologyFunctor X.Modules 0 ⋙ Scheme.Modules.pushforward f :=
  Stacks.DerivedFunctor.homologyEdge (Scheme.Modules.pushforward f) (derivedPushforwardModules f)
    (fun Z n hZ ↦ Stacks.AlgebraicGeometry.ProperSupportCoherent.isGE_derivedPushforward f Z n hZ)
    0
    (Stacks.DerivedFunctor.derivedDegreeNatIsoOfKInjective (Scheme.Modules.pushforward f)
      (derivedPushforwardModules f) (derivedPushforwardModulesUnit f)
      (fun _ ↦ Stacks.AlgebraicGeometry.ProperSupportCoherent.isGE_derivedPushforward f _ 0
        inferInstance)
      (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian X.Modules) 0)

/-- The edge transformation is invertible at an object with no cohomology in negative degrees. -/
instance isIso_derivedPushforwardHomologyEdge_app (M : DerivedCategory X.Modules) [M.IsGE 0] :
    IsIso ((derivedPushforwardHomologyEdge f).app M) :=
  Stacks.DerivedFunctor.isIso_homologyEdge_app_of_isGE _ _ _ _ _ M

/-- **Degree-zero hypercohomology of `Rf_*M`.** For `M` in `D^{≥ 0}(𝒪_X)`, a morphism
`𝒪_S[0] ⟶ Rf_*M` in `D(𝒪_S)` is the same as a global section of `H^0(M)` on `X`.

It is the composite of `DerivedCategory.homologyFromSingle` (bijective because `Rf_*M` is in
`D^{≥ 0}`), the edge isomorphism `derivedPushforwardHomologyEdge`, and the identification of a
morphism `𝒪_S ⟶ f_*N` with a global section of `N`. -/
def derivedPushforwardHomEquiv (M : DerivedCategory X.Modules) (hM : M.IsGE 0) :
    ((DerivedCategory.singleFunctor S.Modules 0).obj (SheafOfModules.unit S.ringCatSheaf) ⟶
      (derivedPushforwardModules f).obj M) ≃
      Γ((DerivedCategory.homologyFunctor X.Modules 0).obj M, ⊤) :=
  haveI := hM
  haveI : ((derivedPushforwardModules f).obj M).IsGE 0 :=
    Stacks.AlgebraicGeometry.ProperSupportCoherent.isGE_derivedPushforward f M 0 hM
  (Equiv.ofBijective _ (DerivedCategory.bijective_homologyFromSingle_of_isGE (C := S.Modules)
      (SheafOfModules.unit S.ringCatSheaf) ((derivedPushforwardModules f).obj M) 0)).trans <|
    (asIso ((derivedPushforwardHomologyEdge f).app M)).homToEquiv.trans <|
    (SheafOfModules.unitHomEquiv _).trans <|
    Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal _ isTerminalTop

/-- The value of `derivedPushforwardHomEquiv`. -/
theorem derivedPushforwardHomEquiv_apply (M : DerivedCategory X.Modules) (hM : M.IsGE 0)
    (a : (DerivedCategory.singleFunctor S.Modules 0).obj (SheafOfModules.unit S.ringCatSheaf) ⟶
      (derivedPushforwardModules f).obj M) :
    derivedPushforwardHomEquiv f M hM a =
      Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal _ isTerminalTop
        (SheafOfModules.unitHomEquiv _
          (DerivedCategory.homologyFromSingle (C := S.Modules)
            (SheafOfModules.unit S.ringCatSheaf) ((derivedPushforwardModules f).obj M) 0 a ≫
            (derivedPushforwardHomologyEdge f).app M)) :=
  rfl

/-- **Naturality of `derivedPushforwardHomEquiv`.** Composing with `Rf_*g` corresponds to applying
`H^0(g)` to global sections. -/
theorem derivedPushforwardHomEquiv_comp {M M' : DerivedCategory X.Modules} (hM : M.IsGE 0)
    (hM' : M'.IsGE 0)
    (a : (DerivedCategory.singleFunctor S.Modules 0).obj (SheafOfModules.unit S.ringCatSheaf) ⟶
      (derivedPushforwardModules f).obj M) (g : M ⟶ M') :
    derivedPushforwardHomEquiv f M' hM' (a ≫ (derivedPushforwardModules f).map g) =
      ((DerivedCategory.homologyFunctor X.Modules 0).map g).app ⊤
        (derivedPushforwardHomEquiv f M hM a) := by
  have h2 : DerivedCategory.homologyFromSingle (C := S.Modules)
      (SheafOfModules.unit S.ringCatSheaf) ((derivedPushforwardModules f).obj M') 0
        (a ≫ (derivedPushforwardModules f).map g) ≫ (derivedPushforwardHomologyEdge f).app M' =
      (DerivedCategory.homologyFromSingle (C := S.Modules)
        (SheafOfModules.unit S.ringCatSheaf) ((derivedPushforwardModules f).obj M) 0 a ≫
          (derivedPushforwardHomologyEdge f).app M) ≫
        (Scheme.Modules.pushforward f).map ((DerivedCategory.homologyFunctor X.Modules 0).map g) :=
    (congrArg (· ≫ (derivedPushforwardHomologyEdge f).app M')
        (DerivedCategory.homologyFromSingle_comp _ _ _ a _)).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) ((derivedPushforwardHomologyEdge f).naturality g)).trans
          (Category.assoc _ _ _).symm
  rw [derivedPushforwardHomEquiv_apply, derivedPushforwardHomEquiv_apply]
  exact congrArg (fun x : SheafOfModules.unit S.ringCatSheaf ⟶ (Scheme.Modules.pushforward f).obj
      ((DerivedCategory.homologyFunctor X.Modules 0).obj M') ↦
    Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal _ isTerminalTop
      (SheafOfModules.unitHomEquiv _ x)) h2

end AlgebraicGeometry

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- For a complex `G` strictly in degrees `≥ 0`, the degree-zero cohomology of `G` in the
derived category is the cycles of `G` in degree `0`: nothing maps into degree `0`. -/
def homologyZeroIsoCycles (G : CochainComplex C ℤ) [G.IsStrictlyGE 0] :
    (homologyFunctor C 0).obj (Q.obj G) ≅ G.cycles 0 :=
  (homologyFunctorFactors C 0).app G ≪≫
    (G.isoHomologyπ (-1) 0 (by simp) ((G.isZero_of_isStrictlyGE 0 (-1)).eq_of_src _ _)).symm

/-- For a complex `G` strictly in degrees `≥ 0`, the inclusion `H^0(G) = ker(d^0) ⟶ G^0`. -/
def homologyZeroToX (G : CochainComplex C ℤ) [G.IsStrictlyGE 0] :
    (homologyFunctor C 0).obj (Q.obj G) ⟶ G.X 0 :=
  (homologyZeroIsoCycles G).hom ≫ G.iCycles 0

/-- `homologyZeroToX` read on the cycles. -/
@[reassoc (attr := simp)]
theorem homologyZeroIsoCycles_inv_comp_homologyZeroToX (G : CochainComplex C ℤ)
    [G.IsStrictlyGE 0] : (homologyZeroIsoCycles G).inv ≫ homologyZeroToX G = G.iCycles 0 := by
  simp [homologyZeroToX]

/-- `homologyZeroToX` lands in the kernel of `d^0`. -/
@[reassoc (attr := simp)]
theorem homologyZeroToX_d (G : CochainComplex C ℤ) [G.IsStrictlyGE 0] (n : ℤ) :
    homologyZeroToX G ≫ G.d 0 n = 0 := by
  simp [homologyZeroToX]

/-- `homologyZeroToX` is a monomorphism. -/
instance mono_homologyZeroToX (G : CochainComplex C ℤ) [G.IsStrictlyGE 0] :
    Mono (homologyZeroToX G) := by
  unfold homologyZeroToX
  infer_instance

/-- `homologyZeroIsoCycles` is natural in the complex. -/
@[reassoc]
theorem homologyZeroIsoCycles_hom_naturality {G G' : CochainComplex C ℤ} [G.IsStrictlyGE 0]
    [G'.IsStrictlyGE 0] (φ : G ⟶ G') :
    (homologyFunctor C 0).map (Q.map φ) ≫ (homologyZeroIsoCycles G').hom =
      (homologyZeroIsoCycles G).hom ≫ HomologicalComplex.cyclesMap φ 0 := by
  have key : HomologicalComplex.homologyMap φ 0 ≫ (G'.isoHomologyπ (-1) 0 (by simp)
      ((G'.isZero_of_isStrictlyGE 0 (-1)).eq_of_src _ _)).inv =
      (G.isoHomologyπ (-1) 0 (by simp) ((G.isZero_of_isStrictlyGE 0 (-1)).eq_of_src _ _)).inv ≫
        HomologicalComplex.cyclesMap φ 0 := by
    rw [← cancel_epi (G.homologyπ 0)]
    simp [HomologicalComplex.homologyπ_naturality_assoc]
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) (homologyFunctorFactors_hom_naturality φ 0)).trans <|
      (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) key).trans (Category.assoc _ _ _).symm

/-- `homologyZeroToX` is natural in the complex. -/
theorem homologyZeroToX_naturality {G G' : CochainComplex C ℤ} [G.IsStrictlyGE 0]
    [G'.IsStrictlyGE 0] (φ : G ⟶ G') :
    (homologyFunctor C 0).map (Q.map φ) ≫ homologyZeroToX G' = homologyZeroToX G ≫ φ.f 0 := by
  simp [homologyZeroToX, homologyZeroIsoCycles_hom_naturality_assoc]

end DerivedCategory

namespace AlgebraicGeometry

/-- **The global sections of `H^0(G)` are the global sections of `G^0` killed by `d^0`**, for a
complex `G` of modules on a scheme strictly in degrees `≥ 0`. -/
theorem mem_range_homologyZeroToX_app_top_iff {X : Scheme.{u}} (G : CochainComplex X.Modules ℤ)
    [G.IsStrictlyGE 0] (s : Γ(G.X 0, ⊤)) :
    s ∈ Set.range ((DerivedCategory.homologyZeroToX G).app ⊤) ↔ (G.d 0 1).app ⊤ s = 0 := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let e : ∀ N : X.Modules, (O ⟶ N) ≃ Γ(N, ⊤) := fun N ↦
    (SheafOfModules.unitHomEquiv N).trans
      (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal N isTerminalTop)
  have he : ∀ {N N' : X.Modules} (φ : O ⟶ N) (p : N ⟶ N'),
      e N' (φ ≫ p) = p.app ⊤ (e N φ) := fun _ _ ↦ rfl
  have he0 : ∀ N : X.Modules, e N 0 = 0 := fun N ↦ by
    rw [← comp_zero (f := (0 : O ⟶ N)) (Z := N), he]
    rfl
  constructor
  · rintro ⟨t, rfl⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      DerivedCategory.homologyZeroToX_d, Scheme.Modules.Hom.zero_app]
    rfl
  · intro hs
    obtain ⟨φ, rfl⟩ := (e (G.X 0)).surjective s
    have hφ : φ ≫ G.d 0 1 = 0 := (e _).injective (by rw [he, hs, he0])
    let ψ : O ⟶ (DerivedCategory.homologyFunctor X.Modules 0).obj (DerivedCategory.Q.obj G) :=
      G.liftCycles φ 1 (by simp) hφ ≫ (DerivedCategory.homologyZeroIsoCycles G).inv
    refine ⟨e _ ψ, ?_⟩
    rw [← he]
    congr 1
    simp [ψ]

end AlgebraicGeometry
