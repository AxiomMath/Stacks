module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomAffineLeafBaseChangeTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated

/-!
# The structure-sheaf leaf of Stacks 09RI, reduced to a directed system of affine representables

The leaf of the dévissage of Stacks 09RI clause (1) is the colimit statement, on the base-changed
system `U_i = X_i ×_{X₀} U` of an affine algebraic space `u : U ⟶ X₀`, for the pair
`(𝒪_U, L)` at every shift of `𝒪_U`, where `L` lies in `D_QCoh(𝒪_U)`.  This file reduces it to a
statement that mentions neither the descent situation nor `U`: for a directed system of affine
representables `V_j` over an affine representable `V₀` whose rings of global functions form a
filtered colimit, the colimit statement for the pair `(Φ(R[p]), Φ(N))` with `R = Γ(V₀, 𝒪)`,
`p ∈ ℤ` and `N ∈ D(R)` arbitrary, `Φ` being the derived associated-module functor.

The reduction chooses `U ≅ h_T` with `T` affine, passes to the affine models of the base changes
(`AlgebraicGeometry.Space.DescentSituation.shiftedIsColim_baseChangeSystem_of_affineModelSystem`),
identifies the pullback of the `n`-th shift of `𝒪_U` with `Φ(R[-n])`, and writes the pullback of
`L`, which is quasi-coherent by Stacks 08F4, as `Φ(N)` by Stacks 08H1.

## Main results

* `DescentSituation.shiftedIsColim_baseChangeSystem_unit_of_representedAffine`: the reduction.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 08F4](https://stacks.math.columbia.edu/tag/08F4)
* [Stacks Project, Lemma 75.13.6 (Tag 08H1)](https://stacks.math.columbia.edu/tag/08H1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : DescentSituation B S hS hZ I}

/-- The pullback of the `n`-th shift of the structure sheaf along an isomorphism onto an affine
representable is the structure sheaf of the representable in degree `-n`. -/
def unitShiftPullbackIso {V : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (k : (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ V)
    (n : ℤ) :
    representedAffineUnitObj B S hS T (-n) ≅
      (smallEtaleDerivedModulePullback B S hS k).obj
        (((DerivedCategory.singleFunctor (Modules.{u, u} B S hS V.1 V.2) 0).obj
          (SheafOfModules.unit _))⟦n⟧) :=
  letI := commShift_smallEtaleDerivedModulePullback B S hS k
  (representedAffineUnitObjShiftIso T n).symm ≪≫
    (shiftFunctor _ n).mapIso
      (representedAffineDerivedAssociatedSingleUnitIso B S hS T 0 ≪≫
        (smallEtaleDerivedModulePullbackUnitIso k).symm) ≪≫
    ((smallEtaleDerivedModulePullback B S hS k).commShiftIso n).symm.app _

/-- The transition morphism of the affine models attached to `i ≤ i` is the identity. -/
theorem affineModelSystem_map_refl {T : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (u : yoneda.obj T ⟶ (stagesSystem D).obj (op (baseStage D)))
    (hconv : SiteContainsBaseChangeLimits B S hS D.system) (i : D.Stages) :
    (affineModelSystem hT u hconv).map (le_refl i) = 𝟙 _ := by
  refine yoneda.map_injective ?_
  change yoneda.map (affineModelMap hT u (le_refl i)) = yoneda.map (𝟙 _)
  rw [yoneda_map_affineModelMap, Subsingleton.elim (homOfLE (le_refl i)).op (𝟙 (op i)),
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- **The structure-sheaf leaf of Stacks 09RI, reduced to a directed system of affine
representables.**  In Situation 09RH with `#I` below the cofinality of the cutoff, let
`g : U ⟶ X₀` be a morphism from an affine algebraic space and let `L ∈ D_QCoh(𝒪_U)`.  If over
every directed system of affine representables over an affine representable `V₀`, indexed by the
stages, whose rings of global functions form a filtered colimit and whose transition morphism at
`i ≤ i` is the identity, the colimit statement holds for
`(Φ(R[p]), Φ(N))` for all `p ∈ ℤ` and `N ∈ D(Γ(V₀, 𝒪))`, then the colimit statement on the
base-changed system of `g` holds for `(𝒪_U, L)` at every shift of `𝒪_U`. -/
theorem shiftedIsColim_baseChangeSystem_unit_of_representedAffine
    (hI : Cardinal.mk I < B.cutoff.ord.cof) {V : AlgebraicSpaces B S hS}
    (g : V ⟶ D.stage D.base) (hV : IsAffineSpace B S hS V.1) (L : derivedModules B S hS V)
    (hL : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS V.1 V.2) n).obj
      L).IsQuasicoherentOnSite)
    (hcore : ∀ {V₀ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V₀)]
      (Sys : RepresentedAffineSystem V₀ D.Stages), Sys.IsRingColimit →
        (∀ i, Sys.map (le_refl i) = 𝟙 _) → ∀ (p : ℤ)
            (N : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V₀, ⊤))),
          Sys.toLimitSystem.IsColim (canonicalPullbackData B S hS)
            (representedAffineUnitObj B S hS V₀ p)
            ((representedAffineDerivedAssociated B S hS V₀).obj N)) :
    PullbackData.LimitSystem.ShiftedIsColim (baseChangeSystem g)
      (smallEtaleDerivedPullbackData B S hS)
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS V.1 V.2) 0).obj
        (SheafOfModules.unit _)) L := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hV
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
  have hconv := D.siteContainsBaseChangeLimits_of_lt_cof hI
  have hP : (canonicalPullbackData B S hS).IsCoherent :=
    (DerivedPullbackComposition.canonical B S hS).isCoherent_toPullbackData
  set k := (baseChangeAffinePointIso (B := B) (S := S) (hS := hS) e).inv
  have hL' := derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS k L hL
  obtain ⟨N, ⟨eN⟩⟩ := exists_iso_representedAffineDerivedAssociated_of_qcohDerived B S hS T _ hL'
  refine shiftedIsColim_baseChangeSystem_of_affineModelSystem g hT e (e.inv ≫ g.hom) rfl hconv
    _ _ fun n => ?_
  exact ((hcore _ (isRingColimit_affineModelSystem hT (e.inv ≫ g.hom) hconv)
    (affineModelSystem_map_refl hT (e.inv ≫ g.hom) hconv) (-n) N).of_iso_fst
    hP (unitShiftPullbackIso k n)).of_iso_snd hP _ eN

end DescentSituation

end AlgebraicGeometry.Space

end
