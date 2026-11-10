module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.AssociatedSheafResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Factorization
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.LinearCupProductFamily
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietorisAndLimits.InverseSystemsOnASpace

/-!
# Existence of a choice of resolutions for the `A`-linear cup product

Let `(X, 𝒪_X)` be a ringed space, `A = Γ(X, 𝒪_X)`, and let `K` and `M` be complexes of
`𝒪_X`-modules.  The data recorded by `Stacks.Cohomology.LinearCupProductFamily.CupData` exists
as soon as `K` is K-injective with injective terms, and for an arbitrary `K` after replacing it
by such a resolution.

## Main definitions

* `Stacks.Cohomology.LinearCupProductFamily.assocAdjunction` — the adjunction
  `(- ⊗_A 𝒪_X) ⊣ Γ(X, -)` between the associated-sheaf functor and the sections over `X`.

## Main results

* `Stacks.Cohomology.LinearCupProductFamily.nonempty_cupData_of_isKInjective` — a choice of
  resolutions exists for a K-injective `K` with injective terms.
* `Stacks.Cohomology.LinearCupProductFamily.exists_cupData` — every complex `K` admits a
  quasi-isomorphism into a complex for which a choice of resolutions exists.

## Implementation notes

The field `cplxRes` of `CupData` is a map of complexes into `K` itself, whereas the source only
asks for a map into a complex representing `K` in the derived category. The gap is closed by
assuming `K` K-injective with injective terms, which makes the factorization of Tag 0G6V land in
`K` on the nose; `exists_cupData` recovers the statement for an arbitrary `K` by replacing it with
such a resolution first. For the same reason the K-injective complex receiving the K-flat complex
`cplx` can be taken to be `K`, so that `cplxToKinj` and `cplxRes` coincide.

Global sections with scalars restricted to `A`, as the right adjoint of the associated-sheaf
functor, is the functor `Stacks.Cohomology.LinearCupProductFamily.openSections X ⊤` on the
nose, which is why no comparison isomorphism between the two appears.

## References

* [Stacks Project, Tag 0G6X](https://stacks.math.columbia.edu/tag/0G6X)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Stacks Project, Tag 0G6V](https://stacks.math.columbia.edu/tag/0G6V)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 02N4](https://stacks.math.columbia.edu/tag/02N4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (Modules KFlat)
open Stacks.AssociatedSheaf
open Stacks.AssociatedSheaf.KFlatResolution (assocSheaf assocSheafComplex)
open Stacks.Cohomology.GlobalKunneth (baseRing)
open Stacks.Cohomology.SpaceInverseSystems (ringedSiteOfSpace)
open Stacks.SheafOfModules.Tensor

universe u

namespace Stacks.Cohomology.LinearCupProductFamily

variable (X : RingedSpace.{u, u})

/-! ### The associated sheaf of a module over the ring of global functions -/

/-- **`M ⊗_A 𝒪_X` is left adjoint to `Γ(X, -)`**, the sections over `X` with scalars
restricted to `A`. -/
def assocAdjunction : assocSheaf X ⊣ openSections X ⊤ :=
  associatedSheafAdjunction.{u, u} X (RingHom.id (baseRing X))

/-- **Sections of a complex of `𝒪_X`-modules over `X`**, as a complex of `A`-modules. -/
abbrev sectionsComplex :
    CochainComplex (Modules X) ℤ ⥤ CochainComplex (ModuleCat.{u} (baseRing X)) ℤ :=
  (openSections X ⊤).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The counit of `(- ⊗_A 𝒪_X) ⊣ Γ(X, -)` on complexes: the map `Γ(X, 𝒦) ⊗_A 𝒪_X ⟶ 𝒦`. -/
abbrev assocCounit (K : CochainComplex (Modules X) ℤ) :
    (assocSheafComplex X).obj ((sectionsComplex X).obj K) ⟶ K :=
  (NatTrans.mapHomologicalComplex (assocAdjunction X).counit (ComplexShape.up ℤ)).app K

/-- The unit of `(- ⊗_A 𝒪_X) ⊣ Γ(X, -)` on complexes: the map `T ⟶ Γ(X, T ⊗_A 𝒪_X)`. -/
abbrev assocUnit (T : CochainComplex (ModuleCat.{u} (baseRing X)) ℤ) :
    T ⟶ (sectionsComplex X).obj ((assocSheafComplex X).obj T) :=
  (NatTrans.mapHomologicalComplex (assocAdjunction X).unit (ComplexShape.up ℤ)).app T

variable {X}

/-- **The adjoint of the adjoint of a map is the map**, for the adjunction
`(- ⊗_A 𝒪_X) ⊣ Γ(X, -)` read on complexes: a map `t : T ⟶ Γ(X, 𝒦)` is recovered from the
associated map `T ⊗_A 𝒪_X ⟶ 𝒦` by applying `Γ(X, -)` and precomposing with the unit. -/
theorem assocUnit_comp_map_counit {K : CochainComplex (Modules X) ℤ}
    {T : CochainComplex (ModuleCat.{u} (baseRing X)) ℤ} (t : T ⟶ (sectionsComplex X).obj K) :
    assocUnit X T ≫ (sectionsComplex X).map
        ((assocSheafComplex X).map t ≫ assocCounit X K) = t :=
  HomologicalComplex.hom_ext _ _ fun i => by
    change (assocAdjunction X).unit.app (T.X i) ≫ (openSections X ⊤).map
      ((assocSheaf X).map (t.f i) ≫ (assocAdjunction X).counit.app (K.X i)) = t.f i
    simp

/-- **A map out of a K-flat complex of flat `𝒪_X`-modules factors, up to homotopy, through a K-flat
complex with flat terms mapping to the target by a quasi-isomorphism.** -/
private theorem exists_kFlat_isFlat_factorization {X : RingedSpace.{u, u}}
    {K L : CochainComplex (Modules X) ℤ} (a : K ⟶ L) (hK : KFlat X K)
    (hKflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (K.X i)) :
    ∃ (N : CochainComplex (Modules X) ℤ) (b : K ⟶ N) (c : N ⟶ L), KFlat X N ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (N.X i)) ∧
      QuasiIso c ∧ Nonempty (Homotopy a (b ≫ c)) :=
  let : (ringedSiteOfSpace X).J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  Stacks.SheafOfModules.exists_isKFlat_isFlat_factorization (ringedSiteOfSpace X) a hK hKflat

/-- **Being a quasi-isomorphism only depends on the homotopy class of a map:** a map of complexes
homotopic to a quasi-isomorphism is a quasi-isomorphism. -/
theorem quasiIso_of_homotopy {C : Type*} [Category C] [Preadditive C] [CategoryWithHomology C]
    {K L : CochainComplex C ℤ} {f g : K ⟶ L} (h : Homotopy f g) [QuasiIso g] : QuasiIso f := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap, h.homologyMap_eq]
  exact (quasiIsoAt_iff_isIso_homologyMap g i).1 inferInstance

/-! ### Existence of a choice of resolutions -/

/-- For a K-injective complex `K` with injective terms and an arbitrary complex `M` of
`𝒪_X`-modules, the resolutions needed for the `A`-linear cup product exist. -/
theorem nonempty_cupData_of_isKInjective (X : RingedSpace.{u, u})
    (K M : CochainComplex (Modules X) ℤ) (hK : K.IsKInjective)
    (hKinj : ∀ i : ℤ, Injective (K.X i)) :
    Nonempty (CupData X K M) := by
  have hG : IsGrothendieckAbelian.{u} (Modules X) :=
    SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing X)
  obtain ⟨T, t, hTkflat, hTflat, hTqi, hTassocKFlat, hTassocFlat⟩ :=
    Stacks.AssociatedSheaf.KFlatResolution.exists_kFlat_resolution_assocFlat X
      ((sectionsComplex X).obj K)
  obtain ⟨N, b, c, hN, hNflat, hc, ⟨hhom⟩⟩ :=
    exists_kFlat_isFlat_factorization ((assocSheafComplex X).map t ≫ assocCounit X K)
      hTassocKFlat hTassocFlat
  let I := (Stacks.Injectives.kInjectiveResolutionFunctor (Modules X)).obj M
  let J := (Stacks.Injectives.kInjectiveResolutionFunctor (Modules X)).obj
    (HomologicalComplex.mapBifunctor N I (sheafTensor X.sheaf) (ComplexShape.up ℤ))
  refine ⟨{
    T := T
    T_kFlat := hTkflat
    T_flat := hTflat
    cplx := N
    cplx_kFlat := hN
    cplx_flat := hNflat
    cplxRes := c
    cplxRes_quasiIso := hc
    kinj := K
    kinj_kInjective := hK
    kinj_injective := hKinj
    cplxToKinj := c
    cplxToKinj_quasiIso := hc
    toSections := assocUnit X T ≫ (sectionsComplex X).map b
    toSections_quasiIso := ?_
    inj := I
    inj_kInjective := inferInstance
    inj_injective := fun i => inferInstance
    injRes := (Stacks.Injectives.kInjectiveResolutionInclusion (Modules X)).app M
    injRes_quasiIso := inferInstance
    tgt := J
    tgt_kInjective := inferInstance
    tgt_injective := fun i => inferInstance
    toTgt := (Stacks.Injectives.kInjectiveResolutionInclusion (Modules X)).app _
    toTgt_quasiIso := inferInstance }⟩
  have key : Homotopy ((assocUnit X T ≫ (sectionsComplex X).map b) ≫ (sectionsComplex X).map c)
      t := by
    refine Homotopy.trans (Homotopy.ofEq ?_) (Homotopy.trans
      (((openSections X ⊤).mapHomotopy hhom.symm).compLeft (assocUnit X T))
      (Homotopy.ofEq (assocUnit_comp_map_counit t)))
    rw [Category.assoc, ← Functor.map_comp]
  exact quasiIso_of_homotopy key

/-- For arbitrary complexes `K` and `M` of `𝒪_X`-modules there is a quasi-isomorphism from `K` into
a complex for which the resolutions needed for the `A`-linear cup product exist; both complexes
therefore represent the same object of `D(𝒪_X)`. -/
theorem exists_cupData (X : RingedSpace.{u, u}) (K M : CochainComplex (Modules X) ℤ) :
    ∃ (K' : CochainComplex (Modules X) ℤ) (e : K ⟶ K'), QuasiIso e ∧
      Nonempty (CupData X K' M) := by
  have hG : IsGrothendieckAbelian.{u} (Modules X) :=
    SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing X)
  exact ⟨(Stacks.Injectives.kInjectiveResolutionFunctor (Modules X)).obj K,
    (Stacks.Injectives.kInjectiveResolutionInclusion (Modules X)).app K, inferInstance,
    nonempty_cupData_of_isKInjective X _ M inferInstance (fun i => inferInstance)⟩

end Stacks.Cohomology.LinearCupProductFamily

end
