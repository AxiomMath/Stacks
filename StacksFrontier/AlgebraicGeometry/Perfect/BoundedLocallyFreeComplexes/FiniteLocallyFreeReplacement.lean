module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.Defs
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.Triangulated
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionProperty
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeTFAE
public import StacksFrontier.AlgebraicGeometry.ColimitClose.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ImmersionIndependence
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.LocalTorAmplitude
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatOpcycles
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.Restriction
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeColimit
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FinitePresentationNextCohomology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite locally free replacement of a bounded below perfect complex

Let `X` be a quasi-compact and quasi-separated scheme with the resolution property. A bounded
below complex of quasi-coherent `O_X`-modules representing a perfect object of `D(O_X)` is the
target of a quasi-isomorphism from a bounded complex of finite locally free `O_X`-modules. This
is the converse direction to
`Stacks.Perfect.BoundedLocallyFreeComplexes.perfect_of_boundedFiniteLocallyFree`, which needs no
hypothesis on `X`.

## Main results

* `Stacks.Perfect.BoundedLocallyFreeComplexes.exists_boundedFiniteLocallyFree_quasiIso` is Tag
  0F8E: the bounded finite locally free replacement, together with the quasi-isomorphism onto
  the given complex.

## Implementation notes

The proof is the induction of the source on the width of a Tor-amplitude interval. The interval
is produced globally from perfectness and quasi-compactness: perfectness gives finite Tor
amplitude on the members of an open covering, compactness extracts a finite subcovering, and Tor
amplitude in a fixed interval is local on a covering. Tor amplitude is
`Stacks.Cohomology.TorAmplitude.HasTorAmplitude`, taken against the derived tensor product
`Stacks.Cohomology.TorAmplitude.derTensor` of Tag 06YU rather than against a hypothesised
bifunctor, so the statement below carries no derived-tensor-product data.

In the base case the cohomology in the single degree of the interval is finitely presented and
flat, hence finite locally free by Tag 05P2, and the cycles there resolve the complex. The
induction step covers the top cohomology by a finite locally free module, which the resolution
property supplies once that cohomology is seen to be of finite type: the cycles are the filtered
union of their finite type quasi-coherent submodules by Tag 01PG, and quasi-compactness makes one
of them surject onto the cohomology by Tag 01BB. Replacing the complex by the cone of the
resulting map shortens the interval by one.

## References

* [Stacks Project, Tag 0F8E](https://stacks.math.columbia.edu/tag/0F8E)
* [Stacks Project, Tag 0F86](https://stacks.math.columbia.edu/tag/0F86)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 08DN](https://stacks.math.columbia.edu/tag/08DN)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
-/

@[expose] public noncomputable section


open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.TorAmplitude

universe u v

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.TorAmplitude.restrictModules_preservesFiniteLimits
  Stacks.Cohomology.TorAmplitude.restrictModules_preservesFiniteColimits

/-- The kernel of a morphism of quasi-coherent `𝒪_X`-modules on a scheme is quasi-coherent. -/
private lemma kernel_isQuasicoherent (X : Scheme.{u}) {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel f

/-- The cokernel of a morphism of quasi-coherent `𝒪_X`-modules on a scheme is
quasi-coherent. -/
private lemma cokernel_isQuasicoherent (X : Scheme.{u}) {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (cokernel f).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel f

/-- The module of `n`-cocycles of a complex of quasi-coherent `𝒪_X`-modules is quasi-coherent:
it is the kernel of the differential out of degree `n`, and quasi-coherence passes to
kernels. -/
private lemma cycles_isQuasicoherent (X : Scheme.{u}) (F : CochainComplex X.Modules ℤ)
    (hFqc : ∀ i : ℤ, (F.X i).IsQuasicoherent) (n : ℤ) :
    (F.cycles n).IsQuasicoherent :=
  have h := hFqc n
  have h' := hFqc (n + 1)
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel (F.d n (n + 1)))
      (F.cyclesIsKernel n (n + 1) (by simp)))
    (Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel (F.d n (n + 1)))

/-- A quotient of an `𝒪_X`-module of finite type is of finite type: the images of local
generators of the source generate the target. -/
private lemma isFiniteType_of_epi {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [M.IsFiniteType] [Epi f] : N.IsFiniteType := by
  let M' : SheafOfModules X.ringCatSheaf := M
  let N' : SheafOfModules X.ringCatSheaf := N
  let f' : M' ⟶ N' := f
  have hf' : Epi f' := by change Epi f; exact ‹Epi f›
  have hM' : SheafOfModules.IsFiniteType.{u, u, u} M' := ‹M.IsFiniteType›
  exact Stacks.SheafOfModules.isFiniteType_of_epi.{u, u, u} f' hM'

/-- The degree `n` cycles of a cochain complex of quasi-coherent modules are quasi-coherent,
being the kernel of the differential leaving degree `n`. -/
private alias cycles_isQuasicoherent_aux := cycles_isQuasicoherent

/-- On a quasi-compact and quasi-separated scheme, a quasi-coherent module of cycles whose
homology is of finite type has a quasi-coherent submodule of finite type that already surjects
onto that homology. -/
private lemma exists_finiteType_cycle_subobject_epi
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (F : CochainComplex X.Modules ℤ)
    (hFqc : ∀ i : ℤ, (F.X i).IsQuasicoherent) (n : ℤ)
    (hHft : (F.homology n).IsFiniteType) :
    ∃ S : Subobject (F.cycles n), (S : X.Modules).IsQuasicoherent ∧
      (S : X.Modules).IsFiniteType ∧ Epi (S.arrow ≫ F.homologyπ n) := by
  classical
  let Z := F.cycles n
  let H := F.homology n
  have : Z.IsQuasicoherent := cycles_isQuasicoherent_aux X F hFqc n
  have : H.IsFiniteType := hHft
  let J := AlgebraicGeometry.FiniteTypeQuasicoherentSubobject Z
  let D := AlgebraicGeometry.finiteTypeQuasicoherentSubobjectFunctor Z
  let cD := AlgebraicGeometry.finiteTypeQuasicoherentSubobjectCocone Z
  have hcD : IsColimit cD :=
    AlgebraicGeometry.Tag01PGColimitClose.isColimit_finiteTypeQuasicoherentSubobjectCocone Z
  have : IsFiltered J := inferInstance
  have : HasImages X.Modules := inferInstance
  have : HasImageMaps X.Modules := inferInstance
  have : EssentiallySmall.{u} J := inferInstance
  have : FinallySmall.{u} J := finallySmall_of_essentiallySmall J
  obtain ⟨S₀, _, hS₀, eS₀, heS₀⟩ := FinallySmall.exists_of_isFiltered.{u} J
  have : IsFiltered S₀ := hS₀
  obtain ⟨ι, _, hιdir, hιne, r, hr⟩ := IsFiltered.exists_directed S₀
  let r' := r ⋙ eS₀
  have : eS₀.Final := heS₀
  have : r.Final := hr
  have : r'.Final := inferInstance
  let D' := r' ⋙ D
  let cD' := cD.whisker r'
  have hcD' : IsColimit cD' := (Functor.Final.isColimitWhiskerEquiv r' cD).symm hcD
  have : Nonempty ι := hιne
  have : IsDirectedOrder ι := hιdir
  let q : Z ⟶ H := F.homologyπ n
  have hqepi : Epi q := inferInstanceAs (Epi (F.homologyπ n))
  let α : D ⟶ (Functor.const J).obj H :=
    { app := fun i => i.obj.arrow ≫ q
      naturality := by
        intro i j f
        dsimp [D, AlgebraicGeometry.finiteTypeQuasicoherentSubobjectFunctor]
        calc
          (Subobject.underlying.map f.hom ≫ j.obj.arrow) ≫ q =
              i.obj.arrow ≫ q := by rw [Subobject.underlying_arrow f.hom]
          _ = (i.obj.arrow ≫ q) ≫ 𝟙 H := by simp }
  let α' : D' ⟶ (Functor.const ι).obj H := Functor.whiskerLeft r' α
  let A' : ι ⥤ Arrow X.Modules :=
    { obj i := Arrow.mk (α'.app i)
      map := fun f => Arrow.homMk (D'.map f) (𝟙 H) (by exact α'.naturality f)
      map_id := by intro i; ext <;> simp
      map_comp := by intro i j k f g; ext <;> simp }
  let I := A' ⋙ Limits.im
  let ρ : D' ⟶ I :=
    { app := fun i => factorThruImage (α'.app i)
      naturality := by
        intro i j f
        show D'.map f ≫ factorThruImage (α'.app j) =
          factorThruImage (α'.app i) ≫ image.map (A'.map f)
        exact (image.factor_map (A'.map f)).symm }
  let μ : I ⟶ (Functor.const ι).obj H :=
    { app := fun i => image.ι (α'.app i)
      naturality := by
        intro i j f
        show image.map (A'.map f) ≫ image.ι (α'.app j) =
          image.ι (α'.app i) ≫ 𝟙 H
        calc
          image.map (A'.map f) ≫ image.ι (α'.app j) =
              image.ι (α'.app i) ≫ (A'.map f).right := image.map_ι (A'.map f)
          _ = image.ι (α'.app i) ≫ 𝟙 H := by simp [A'] }
  let cμ : Cocone I := Cocone.mk H μ
  let g : colimit I ⟶ H := colimit.desc I cμ
  have hgι : ∀ i : ι, colimit.ι I i ≫ g = μ.app i := fun i => colimit.ι_desc cμ i
  have hιρ : ∀ i : ι, colimit.ι D' i ≫ (colim (J := ι) (C := X.Modules)).map ρ =
      ρ.app i ≫ colimit.ι I i := fun i => ι_colimMap ρ i
  have hιμ : ∀ i : ι, colimit.ι I i ≫ (colim (J := ι) (C := X.Modules)).map μ =
      μ.app i ≫ colimit.ι ((Functor.const ι).obj H) i := fun i => ι_colimMap μ i
  have hμapp : ∀ i : ι, Mono (μ.app i) := fun i => by
    show Mono (image.ι (α'.app i)); infer_instance
  have hμmono : Mono μ := NatTrans.mono_of_mono_app μ
  have hgmono : Mono g := by
    have : IsFiltered ι := isFiltered_of_directed_le_nonempty ι
    have : IsConnected ι := @IsFiltered.isConnected ι inferInstance inferInstance
    have : PreservesFiniteLimits (colim (J := ι) (C := X.Modules)) := inferInstance
    have hmap : Mono ((colim (J := ι) (C := X.Modules)).map μ) :=
      preserves_mono_of_preservesLimit _ μ
    let hcConst := isColimitConstCocone ι H
    let eConst : colimit ((Functor.const ι).obj H) ≅ H :=
      (colimit.isColimit ((Functor.const ι).obj H)).coconePointUniqueUpToIso hcConst
    have hconst : ∀ i : ι, colimit.ι ((Functor.const ι).obj H) i ≫ eConst.hom = 𝟙 H :=
      fun i => colimit.comp_coconePointUniqueUpToIso_hom hcConst i
    have hg' : g = ((colim (J := ι) (C := X.Modules)).map μ) ≫ eConst.hom := by
      refine colimit.hom_ext fun i => ?_
      calc
        colimit.ι I i ≫ g = μ.app i := hgι i
        _ = μ.app i ≫ 𝟙 H := (Category.comp_id _).symm
        _ = μ.app i ≫ colimit.ι ((Functor.const ι).obj H) i ≫ eConst.hom := by
          rw [hconst i]
        _ = (μ.app i ≫ colimit.ι ((Functor.const ι).obj H) i) ≫ eConst.hom :=
          (Category.assoc _ _ _).symm
        _ = (colimit.ι I i ≫ (colim (J := ι) (C := X.Modules)).map μ) ≫ eConst.hom := by
          rw [hιμ i]
        _ = colimit.ι I i ≫ ((colim (J := ι) (C := X.Modules)).map μ) ≫ eConst.hom :=
          Category.assoc _ _ _
    have hmono : Mono eConst.hom := inferInstance
    rw [hg']
    exact mono_comp _ _
  have hcomp : Epi (((colim (J := ι) (C := X.Modules)).map ρ) ≫ g) := by
    let cα : Cocone D' := Cocone.mk H α'
    have hdesc : colimit.desc D' cα =
        ((colimit.isColimit D').coconePointUniqueUpToIso hcD').hom ≫ q := by
      refine colimit.hom_ext fun i => ?_
      calc
        colimit.ι D' i ≫ colimit.desc D' cα = cα.ι.app i := colimit.ι_desc cα i
        _ = cD'.ι.app i ≫ q := rfl
        _ = (colimit.ι D' i ≫
            ((colimit.isColimit D').coconePointUniqueUpToIso hcD').hom) ≫ q := by
          rw [colimit.comp_coconePointUniqueUpToIso_hom hcD' i]
        _ = colimit.ι D' i ≫
            ((colimit.isColimit D').coconePointUniqueUpToIso hcD').hom ≫ q :=
          Category.assoc _ _ _
    have hmap : ((colim (J := ι) (C := X.Modules)).map ρ) ≫ g = colimit.desc D' cα := by
      refine colimit.hom_ext fun i => ?_
      rw [← Category.assoc, hιρ i, Category.assoc, hgι i, colimit.ι_desc]
      exact image.fac (α'.app i)
    rw [hmap, hdesc]
    exact @epi_comp _ _ _ _ _ ((colimit.isColimit D').coconePointUniqueUpToIso hcD').hom
      inferInstance q hqepi
  have hgEpi : Epi g := epi_of_epi ((colim (J := ι) (C := X.Modules)).map ρ) g
  have : IsIso g := isIso_of_mono_of_epi g
  have : CompactSpace X.toPresheafedSpace := inferInstance
  let I' : ι ⥤ SheafOfModules.{u} X.ringCatSheaf := I
  have : (colimit I').IsFiniteType :=
    (Stacks.SheafOfModules.isFiniteType_of_iso.{u} (asIso g).symm : (colimit I).IsFiniteType)
  obtain ⟨i, hi⟩ :=
    Stacks.SheafOfModules.exists_epi_to_colimit_of_isFiniteType (X := X.toPresheafedSpace)
      (R := X.ringCatSheaf) I'
  have hiEpi : Epi (colimit.ι I i) := hi
  have hStage : Epi ((r'.obj i).obj.arrow ≫ q) := by
    have hfac : factorThruImage (α'.app i) ≫ colimit.ι I i ≫ g = (r'.obj i).obj.arrow ≫ q :=
      (congrArg (fun t => factorThruImage (α'.app i) ≫ t) (hgι i)).trans
        (image.fac (α'.app i))
    have h1 : Epi (factorThruImage (α'.app i)) := inferInstance
    have h2 : Epi (colimit.ι I i ≫ g) :=
      @epi_comp _ _ _ _ _ (colimit.ι I i) hiEpi g hgEpi
    rw [← hfac]
    exact @epi_comp _ _ _ _ _ (factorThruImage (α'.app i)) h1 (colimit.ι I i ≫ g) h2
  exact ⟨(r'.obj i).obj, (r'.obj i).property.1, (r'.obj i).property.2, hStage⟩

/-- The map of complexes `P[-n] ⟶ F` determined by a map `π : P ⟶ Z^n(F)` into the
`n`-th cycles of `F`; in degree `n` it is `π` followed by the inclusion of cycles. -/
private noncomputable def singleToCycles
    {X : Scheme.{u}} (F : CochainComplex X.Modules ℤ) (n : ℤ)
    {P : X.Modules} (π : P ⟶ F.cycles n) :
    (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) n).obj P ⟶ F :=
  HomologicalComplex.mkHomFromSingle (π ≫ F.iCycles n) (by
      intro k hnk
      have hk : k = n + 1 := by
        have hk' : n + 1 = k := by simpa only [ComplexShape.up_Rel] using hnk
        omega
      subst k
      simp [Category.assoc])

/-- Under the canonical identification of `Z^n(P[-n])` with `P`, the map induced by
`singleToCycles F n π` on `n`-th cycles is `π` itself. -/
private lemma cyclesMap_singleToCycles
    {X : Scheme.{u}} (F : CochainComplex X.Modules ℤ) (n : ℤ)
    {P : X.Modules} (π : P ⟶ F.cycles n) :
    (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n P).inv ≫
        HomologicalComplex.cyclesMap (singleToCycles F n π) n = π := by
  apply (cancel_mono (F.iCycles n)).1
  calc
    ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n P).inv ≫
          HomologicalComplex.cyclesMap (singleToCycles F n π) n) ≫ F.iCycles n =
        (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n P).inv ≫
          ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) n).obj P).iCycles n ≫
            (singleToCycles F n π).f n := by
          rw [Category.assoc, HomologicalComplex.cyclesMap_i]
    _ = π ≫ F.iCycles n := by
        simp [singleToCycles]

/-- If `π : P ⟶ Z^n(F)` induces an epimorphism onto `H^n(F)`, then `P[-n] ⟶ F` is
surjective on `H^n`. -/
private lemma epi_homologyMap_singleToCycles
    {X : Scheme.{u}} (F : CochainComplex X.Modules ℤ) (n : ℤ)
    {P : X.Modules} (π : P ⟶ F.cycles n)
    (hπ : Epi (π ≫ F.homologyπ n)) :
    Epi (HomologicalComplex.homologyMap (singleToCycles F n π) n) := by
  set A := (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) n).obj P
  set e := HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n P
  have hcycles : e.inv ≫ HomologicalComplex.cyclesMap (singleToCycles F n π) n = π :=
    cyclesMap_singleToCycles F n π
  have hcyclesEpi : Epi
      (HomologicalComplex.cyclesMap (singleToCycles F n π) n ≫ F.homologyπ n) := by
    have hcomp : Epi
        (e.inv ≫ HomologicalComplex.cyclesMap (singleToCycles F n π) n ≫
          F.homologyπ n) := by
      rw [← Category.assoc, hcycles]
      exact hπ
    have : Epi e.inv := IsIso.epi_of_iso e.inv
    exact (epi_comp_iff_of_epi e.inv _).1 hcomp
  have hmap := HomologicalComplex.homologyπ_naturality (singleToCycles F n π) n
  have hcompEpi : Epi (A.homologyπ n ≫
      HomologicalComplex.homologyMap (singleToCycles F n π) n) := by
    rw [hmap]
    exact hcyclesEpi
  have : Epi (A.homologyπ n) := inferInstance
  exact (epi_comp_iff_of_epi (A.homologyπ n) _).1 hcompEpi

/-- If `π : P ⟶ Z^n(F)` induces an isomorphism onto `H^n(F)` and `F` has no cohomology
outside degree `n`, then `P[-n] ⟶ F` is a quasi-isomorphism. -/
private lemma quasiIso_singleToCycles
    {X : Scheme.{u}} (F : CochainComplex X.Modules ℤ) (n : ℤ)
    {P : X.Modules} (π : P ⟶ F.cycles n)
    (hπ : IsIso (π ≫ F.homologyπ n))
    (hvanish : ∀ i : ℤ, i ≠ n → IsZero (F.homology i)) :
    QuasiIso (singleToCycles F n π) := by
  refine (quasiIso_iff _).2 fun i => (quasiIsoAt_iff_isIso_homologyMap _ i).2 ?_
  by_cases hi : i = n
  · subst i
    set A := (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) n).obj P with hA
    set e := HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n P with he
    have hAπ : IsIso (A.homologyπ n) :=
      A.isIso_homologyπ (n - 1) n (by simp)
        ((HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n P (n - 1)
          (by omega)).eq_of_src _ _)
    have key : (e.inv ≫ A.homologyπ n) ≫
        HomologicalComplex.homologyMap (singleToCycles F n π) n = π ≫ F.homologyπ n := by
      rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
        cyclesMap_singleToCycles]
    have hcomp : IsIso ((e.inv ≫ A.homologyπ n) ≫
        HomologicalComplex.homologyMap (singleToCycles F n π) n) := by
      rw [key]; exact hπ
    exact IsIso.of_isIso_comp_left (e.inv ≫ A.homologyπ n)
      (HomologicalComplex.homologyMap (singleToCycles F n π) n)
  · exact IsZero.isIso
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) n P i hi)
      (hvanish i hi) _

open CategoryTheory.Pretriangulated CochainComplex in
/-- If `g : E ⟶ C(α)` is a quasi-isomorphism, then the cone of the composite
`E ⟶ C(α) ⟶ A⟦1⟧`, shifted back by one, is quasi-isomorphic to `F`. -/
private lemma exists_quasiIso_from_shifted_mappingCone
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    {A F E : CochainComplex C ℤ} (α : A ⟶ F)
    (g : E ⟶ CochainComplex.mappingCone α) [QuasiIso g] :
    ∃ f : (CochainComplex.mappingCone
        (g ≫ (CochainComplex.mappingCone.triangle α).mor₃))⟦(-1 : ℤ)⟧ ⟶ F, QuasiIso f := by
  let q : CochainComplex C ℤ ⥤ HomotopyCategory C (ComplexShape.up ℤ) :=
    HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let δ : E ⟶ A⟦(1 : ℤ)⟧ := g ≫ (mappingCone.triangle α).mor₃
  let T₁ := mappingCone.triangleh δ
  let T₂ := q.mapTriangle.obj (mappingCone.triangle α).rotate.rotate
  have hT₁ : T₁ ∈ distinguishedTriangles :=
    HomotopyCategory.mappingCone_triangleh_distinguished δ
  have hT₂ : T₂ ∈ distinguishedTriangles :=
    isomorphic_distinguished _ (rot_of_distTriang _ (rot_of_distTriang _
        (HomotopyCategory.mappingCone_triangleh_distinguished α))) _
      ((q.mapTriangleRotateIso.app _).symm ≪≫
        (rotate _).mapIso (q.mapTriangleRotateIso.app _).symm)
  have key : T₁.mor₁ ≫ 𝟙 T₂.obj₂ = q.map g ≫ T₂.mor₁ :=
    (Category.comp_id _).trans (q.map_comp g _)
  let φ : T₁ ⟶ T₂ :=
    completeDistinguishedTriangleMorphism T₁ T₂ hT₁ hT₂ (q.map g) (𝟙 _) key
  have h₁ : IsIso (DerivedCategory.Qh.map φ.hom₁) := by
    show IsIso (DerivedCategory.Qh.map (q.map g))
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) g).mpr inferInstance
  have h₂ : IsIso (DerivedCategory.Qh.map φ.hom₂) := by
    show IsIso (DerivedCategory.Qh.map (𝟙 _))
    infer_instance
  have h₃ : IsIso (DerivedCategory.Qh.map φ.hom₃) :=
    isIso₃_of_isIso₁₂ (DerivedCategory.Qh.mapTriangle.map φ)
      (DerivedCategory.Qh.map_distinguished _ hT₁)
      (DerivedCategory.Qh.map_distinguished _ hT₂) h₁ h₂
  let f : CochainComplex.mappingCone δ ⟶ F⟦(1 : ℤ)⟧ := q.preimage φ.hom₃
  have hmap : q.map f = φ.hom₃ := Functor.map_preimage _ _
  have hf : QuasiIso f := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso C f).mp
    apply (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) f).mp
    show IsIso (DerivedCategory.Qh.map (q.map f))
    rwa [hmap]
  have hfin : QuasiIso (f⟦(-1 : ℤ)⟧' ≫ (shiftShiftNeg F (1 : ℤ)).hom) := inferInstance
  exact ⟨f⟦(-1 : ℤ)⟧' ≫ (shiftShiftNeg F (1 : ℤ)).hom, hfin⟩

open CategoryTheory.Pretriangulated CochainComplex in
/-- If `Hⁿ(α)` is surjective and `Hⁿ⁺¹(A) = 0`, then the cone of `α` has vanishing `n`-th
homology. -/
private lemma isZero_homology_mappingCone_of_epi
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    {A F : CochainComplex C ℤ} (α : A ⟶ F) (n : ℤ)
    [Epi (HomologicalComplex.homologyMap α n)]
    (hA : IsZero (A.homology (n + 1))) :
    IsZero ((CochainComplex.mappingCone α).homology n) := by
  let T := mappingCone.triangle α
  have hT := DerivedCategory.mappingCone_triangle_distinguished α
  have hex := homologyMap_exact₃_of_distTriang T hT n (n + 1) rfl
  refine hex.isZero_X₂ ?_ (hA.eq_of_tgt _ _)
  show HomologicalComplex.homologyMap (mappingCone.inr α) n = 0
  rw [← cancel_epi (HomologicalComplex.homologyMap α n), comp_zero]
  exact homologyMap_comp_eq_zero_of_distTriang T hT n

open CategoryTheory.Pretriangulated CochainComplex in
/-- If `Hⁿ(F) = 0` and `Hⁿ⁺¹(A) = 0`, then the cone of `α : A ⟶ F` has vanishing `n`-th
homology. -/
private lemma isZero_homology_mappingCone_of_isZero
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    {A F : CochainComplex C ℤ} (α : A ⟶ F) (n : ℤ)
    (hF : IsZero (F.homology n)) (hA : IsZero (A.homology (n + 1))) :
    IsZero ((CochainComplex.mappingCone α).homology n) := by
  have hex := homologyMap_exact₃_of_distTriang (CochainComplex.mappingCone.triangle α)
    (DerivedCategory.mappingCone_triangle_distinguished α) n (n + 1) rfl
  exact hex.isZero_X₂ (hF.eq_of_src _ _) (hA.eq_of_tgt _ _)

/-- The mapping cone of a morphism of bounded-below cochain complexes is bounded below. -/
private lemma plus_mappingCone
    {C : Type u} [Category.{v} C] [Abelian C]
    {A F : CochainComplex C ℤ} (α : A ⟶ F)
    (hA : CochainComplex.plus C A) (hF : CochainComplex.plus C F) :
    CochainComplex.plus C (CochainComplex.mappingCone α) := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hF
  let : A.IsStrictlyGE a := ha
  let : F.IsStrictlyGE b := hb
  exact ⟨min (a - 1) b,
    CochainComplex.isStrictlyGE_mappingCone α a b _ (by omega) (by omega)⟩

/-- The mapping cone of a morphism of bounded-above cochain complexes is bounded above. -/
private lemma minus_mappingCone
    {C : Type u} [Category.{v} C] [Abelian C]
    {A F : CochainComplex C ℤ} (α : A ⟶ F)
    (hA : CochainComplex.minus C A) (hF : CochainComplex.minus C F) :
    CochainComplex.minus C (CochainComplex.mappingCone α) := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hF
  let : A.IsStrictlyLE a := ha
  let : F.IsStrictlyLE b := hb
  exact ⟨max a b,
    CochainComplex.isStrictlyLE_mappingCone α a b _ (by omega) (by omega)⟩

/-- The mapping cone of a morphism of complexes of quasi-coherent modules on a scheme has
quasi-coherent terms, since `C(α)ⁱ ≅ Aⁱ⁺¹ ⊞ Fⁱ`. -/
private lemma mappingCone_isQuasicoherent {X : Scheme.{u}}
    {A F : CochainComplex X.Modules ℤ} (α : A ⟶ F)
    (hA : ∀ i : ℤ, (A.X i).IsQuasicoherent)
    (hF : ∀ i : ℤ, (F.X i).IsQuasicoherent) (i : ℤ) :
    ((CochainComplex.mappingCone α).X i).IsQuasicoherent := by
  let : (A.X (i + 1)).IsQuasicoherent := hA (i + 1)
  let : (F.X i).IsQuasicoherent := hF i
  have : (A.X (i + 1) ⊞ F.X i).IsQuasicoherent :=
    AlgebraicGeometry.directSum_isQuasicoherent_scheme _ _
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (HomologicalComplex.homotopyCofiber.XIsoBiprod α i (i + 1) rfl).symm inferInstance

/-- A finite locally free module on a scheme is flat. -/
private lemma isFlat_of_isFiniteLocallyFree (X : Scheme.{u}) (P : X.Modules)
    (hP : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) P) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) P := by
  have : P.IsFinitePresentation := Stacks.FiniteLocallyFree.isFinitePresentation P
  have : P.IsQuasicoherent := _root_.isQuasicoherent_of_isFinitePresentation P
  have h : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) P ∧
      P.IsFinitePresentation :=
    ((Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae P).out 4 1).mp hP
  exact h.1

/-- A zero module on a scheme is finite locally free. -/
private lemma isFiniteLocallyFree_of_isZero (X : Scheme.{u}) (M : X.Modules) (hM : IsZero M) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) M :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u}
    (finiteLocallyFree_of_isZero X M hM).exists_isFiniteLocallyFreeData

/-- A finite locally free module placed in a single degree gives a complex all of whose terms
are finite locally free. -/
private lemma isFiniteLocallyFree_single_terms (X : Scheme.{u}) (P : X.Modules) (b : ℤ)
    (hP : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) P) (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf)
      (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) b).obj P).X i) := by
  by_cases hi : i = b
  · subst i
    exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) b P).symm (h := hP)
  · exact isFiniteLocallyFree_of_isZero X _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) b P i hi)

/-- In a complex of flat `O_X`-modules which vanishes in degree `n + 1` and whose cohomology in
degree `n` vanishes, the cycles in degree `n - 1` form a flat module. -/
private lemma isFlat_cycles_of_isZero_homology (X : Scheme.{u})
    (K : CochainComplex X.Modules ℤ) (n : ℤ)
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (K.X i))
    (hnext : IsZero (K.X (n + 1))) (hhom : IsZero (K.homology n)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (K.cycles (n - 1)) := by
  have hex : K.ExactAt n :=
    (HomologicalComplex.exactAt_iff_isZero_homology K n).2 hhom
  have : Epi (K.toCycles (n - 1) n) := by
    have hn : (ComplexShape.up ℤ).prev n = n - 1 := by simp
    rw [← hn]
    exact hex.epi_toCycles
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (K.iCycles (n - 1)) (K.toCycles (n - 1) n) (by
      rw [← cancel_mono (K.iCycles n), Category.assoc, K.toCycles_i,
        K.iCycles_d, zero_comp])
  have hS : S.ShortExact := by
    refine { exact := ?_ }
    apply ShortComplex.exact_of_f_is_kernel
    exact isKernelOfComp (K.iCycles n) (K.d (n - 1) n)
      (K.cyclesIsKernel (n - 1) n (by simp)) S.zero (K.toCycles_i (n - 1) n)
  have : IsIso (K.iCycles n) := K.isIso_iCycles n (n + 1) (by simp) (hnext.eq_of_tgt _ _)
  exact Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_left_of_shortExact X.sheaf S hS
    (hflat (n - 1)) (BoundedFlatRepresentative.isFlat_of_iso (asIso (K.iCycles n)).symm (hflat n))

/-- A complex of flat `O_X`-modules concentrated in `[a, b]` whose top cohomology vanishes has
Tor amplitude in `[a, b - 1]`: its truncation below `b` is still a complex of flat modules, and
it still represents the same object of `D(O_X)`. -/
private lemma hasTorAmplitude_of_flat_of_isZero_top_homology (X : Scheme.{u})
    (K : CochainComplex X.Modules ℤ) (a b : ℤ) (hab : a < b)
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (K.X i))
    (hterms : ∀ i : ℤ, i ∉ Set.Icc a b → IsZero (K.X i))
    (hhom : IsZero (K.homology b)) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj K) a (b - 1) := by
  let T := K.truncLE (b - 1)
  have hcycles : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := X.sheaf) (K.cycles (b - 1)) :=
    isFlat_cycles_of_isZero_homology X K b hflat (hterms (b + 1) (by simp)) hhom
  have hflatT (i : ℤ) : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := X.sheaf) (T.X i) := by
    by_cases hi : i < b - 1
    · exact BoundedFlatRepresentative.isFlat_of_iso
        (K.truncLEXIso (b - 1) i hi).symm (hflat i)
    by_cases heq : i = b - 1
    · subst i
      exact BoundedFlatRepresentative.isFlat_of_iso
        (K.truncLEXIsoCycles (b - 1)).symm hcycles
    · have hgt : b - 1 < i := by omega
      exact FlatOpcycles.isFlat_of_isZero _
        (T.isZero_of_isStrictlyLE (b - 1) i hgt)
  have htermsT (i : ℤ) (hi : i ∉ Set.Icc a (b - 1)) : IsZero (T.X i) := by
    by_cases hlt : i < a
    · have hib : i < b - 1 := by omega
      exact (hterms i (by simp only [Set.mem_Icc]; omega)).of_iso
        (K.truncLEXIso (b - 1) i hib)
    · have hgt : b - 1 < i := by simp only [Set.mem_Icc] at hi; omega
      exact T.isZero_of_isStrictlyLE (b - 1) i hgt
  have : K.IsLE (b - 1) := (K.isLE_iff (b - 1)).2 (fun i hi => by
    by_cases hib : i = b
    · subst i
      exact (HomologicalComplex.exactAt_iff_isZero_homology K b).2 hhom
    · have hzero : IsZero (K.X i) := hterms i (by simp only [Set.mem_Icc]; omega)
      exact ShortComplex.exact_of_isZero_X₂ _ hzero)
  have hiso : IsIso (DerivedCategory.Q.map (K.ιTruncLE (b - 1))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules _).2 inferInstance
  have e : DerivedCategory.Q.obj T ≅ DerivedCategory.Q.obj K := @asIso _ _ _ _ _ hiso
  exact (BoundedFlatRepresentative.hasTorAmplitude_iff_exists_flat_representative
    (DerivedCategory.Q.obj K) a (b - 1) (by omega)).2 ⟨T, hflatT, htermsT, ⟨e⟩⟩

/-- **A finite locally free module placed in a single degree is a perfect object of `D(O_X)`.**
It is a bounded complex of finite locally free modules, hence lies in the image of `K^b(A)`. -/
private lemma isPerfect_single_isFiniteLocallyFree (X : Scheme.{u}) (P : X.Modules)
    (hP : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) P) (b : ℤ) :
    IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) b).obj P)) := by
  classical
  let A := (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) b).obj P
  have hflf : ∀ i : ℤ,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := X.ringCatSheaf) (A.X i) :=
    isFiniteLocallyFree_single_terms X P b hP
  let E : BoundedFiniteLocallyFreeHomotopyCategory X :=
    ⟨(HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj A,
      (ObjectProperty.strictMap_iff _ _ _).2
        ⟨A, ⟨⟨⟨b, inferInstance⟩, ⟨b, inferInstance⟩⟩, hflf⟩, rfl⟩⟩
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
    ((DerivedCategory.quotientCompQhIso X.Modules).app A)
    (perfect_of_boundedFiniteLocallyFree X E)

/-- **The mapping cone of a map of perfect objects is perfect.** It is the third vertex of the
distinguished triangle of the cone. -/
private lemma isPerfect_mappingCone {X : Scheme.{u}}
    {A F : CochainComplex X.Modules ℤ} (α : A ⟶ F)
    (hA : IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj A))
    (hF : IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj F)) :
    IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj
      (CochainComplex.mappingCone α : CochainComplex X.Modules ℤ)) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle α))
    (DerivedCategory.mappingCone_triangle_distinguished α) hA hF

/-- **A finite locally free module placed in degree `b` has Tor amplitude in `[b, b]`.** It is
its own flat representative, concentrated in that degree. -/
private lemma hasTorAmplitude_single_isFiniteLocallyFree (X : Scheme.{u}) (P : X.Modules)
    (hP : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) P) (b : ℤ) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) b).obj P))
      b b := by
  classical
  let K := (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) b).obj P
  have hflat (i : ℤ) : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := X.sheaf) (K.X i) :=
    isFlat_of_isFiniteLocallyFree X _ (isFiniteLocallyFree_single_terms X P b hP i)
  have hterms (i : ℤ) (hi : i ∉ Set.Icc b b) : IsZero (K.X i) := by
    have hib : i ≠ b := by simp only [Set.mem_Icc] at hi; omega
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) b P i hib
  exact (BoundedFlatRepresentative.hasTorAmplitude_iff_exists_flat_representative
    (DerivedCategory.Q.obj K) b b le_rfl).2 ⟨K, hflat, hterms, ⟨Iso.refl _⟩⟩

/-- **Tor amplitude propagates to a mapping cone.** If the source has Tor amplitude in
`[a + 1, b + 1]` and the target in `[a, b]`, then the cone has Tor amplitude in `[a, b]`. -/
private lemma hasTorAmplitude_mappingCone {X : Scheme.{u}}
    {A F : CochainComplex X.Modules ℤ} (α : A ⟶ F) (a b : ℤ)
    (hA : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj A) (a + 1) (b + 1))
    (hF : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj F) a b) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj
        (CochainComplex.mappingCone α : CochainComplex X.Modules ℤ)) a b := by
  have h := @TorAmplitude.hasTorAmplitude_obj₃ _ _ _ _
    (FlatOpcycles.tensorSingleFunctor X.toRingedSpace)
    (fun M => (derTensor X.toRingedSpace).commShift_left
      ((DerivedCategory.singleFunctor _ 0).obj M))
    (fun M => (derTensor X.toRingedSpace).exact_left
      ((DerivedCategory.singleFunctor _ 0).obj M))
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle α))
    (DerivedCategory.mappingCone_triangle_distinguished α) a b
    (fun M i hi => hA M i (by simp only [Set.mem_Icc, not_and_or, not_le]; omega))
    (fun M i hi => hF M i (by simp only [Set.mem_Icc, not_and_or, not_le]; omega))
  exact fun M i hi => h M i (by simp only [Set.mem_Icc, not_and_or, not_le] at hi; omega)

/-- **Vanishing top cohomology shortens a Tor-amplitude interval.** An object with Tor amplitude
in `[a, b]` whose cohomology in degree `b` vanishes has Tor amplitude in `[a, b - 1]`. -/
private lemma hasTorAmplitude_of_isZero_top_homology {X : Scheme.{u}}
    (K : DerivedCategory X.Modules) (a b : ℤ) (hab : a < b)
    (hK : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace K a b)
    (hzero : IsZero ((DerivedCategory.homologyFunctor X.Modules b).obj K)) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace K a (b - 1) := by
  obtain ⟨L, hflat, hterms, ⟨e⟩⟩ :=
    (BoundedFlatRepresentative.hasTorAmplitude_iff_exists_flat_representative
      K a b hab.le).mp hK
  have hzeroL : IsZero (L.homology b) :=
    hzero.of_iso (((DerivedCategory.homologyFunctorFactors X.Modules b).app L).symm ≪≫
      (DerivedCategory.homologyFunctor X.Modules b).mapIso e)
  exact FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1}
    (hasTorAmplitude_of_flat_of_isZero_top_homology X L a b hab hflat hterms hzeroL) e.symm

/-- An object of `D(O_X)` with Tor amplitude in `[a, b]` has vanishing cohomology in every
degree outside `[a, b]`. -/
private lemma isZero_homology_of_hasTorAmplitude (X : Scheme.{u})
    (F : CochainComplex X.Modules ℤ) (a b : ℤ) (_hab : a ≤ b)
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj F) a b)
    (i : ℤ) (hi : i ∉ Set.Icc a b) : IsZero (F.homology i) :=
  (Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.isZero_homology_of_hasTorAmplitude
    (DerivedCategory.Q.obj F) a b hamp i hi).of_iso
      ((DerivedCategory.homologyFunctorFactors X.Modules i).app F).symm

/-- Tor amplitude concentrated in the single degree `a` makes the cohomology in that degree a
flat `O_X`-module: a flat representative concentrated in degree `a` has that term as its
cohomology. -/
private lemma isFlat_homology_of_hasTorAmplitude_singleton (X : Scheme.{u})
    (F : CochainComplex X.Modules ℤ) (a : ℤ)
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj F) a a) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (F.homology a) := by
  obtain ⟨K, hflat, hzero, ⟨e⟩⟩ :=
    (BoundedFlatRepresentative.hasTorAmplitude_iff_exists_flat_representative
      (DerivedCategory.Q.obj F) a a le_rfl).mp hamp
  have hd₁ : (K.sc a).f = 0 :=
    (hzero ((ComplexShape.up ℤ).prev a) (by simp)).eq_of_src _ _
  have hd₂ : (K.sc a).g = 0 :=
    (hzero ((ComplexShape.up ℤ).next a) (by simp)).eq_of_tgt _ _
  let e₀ : K.homology a ≅ K.X a :=
    (ShortComplex.HomologyData.ofZeros (K.sc a) hd₁ hd₂).left.homologyIso
  let e₁ : K.homology a ≅ F.homology a :=
    ((DerivedCategory.homologyFunctorFactors X.Modules a).app K).symm ≪≫
      (DerivedCategory.homologyFunctor X.Modules a).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors X.Modules a).app F
  exact Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.isFlat_of_iso
    (e₀.symm ≪≫ e₁) (hflat a)

/-- **Stacks 05P2.** A quasi-coherent module of cycles whose cohomology is flat and finitely
presented is finite locally free, when the incoming differential vanishes: the cycles are then
isomorphic to the cohomology. -/
private lemma isFiniteLocallyFree_cycles_of_isFlat_homology (X : Scheme.{u})
    (F : CochainComplex X.Modules ℤ) (n : ℤ)
    (hqc : (F.cycles n).IsQuasicoherent)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      (F.homology n))
    (hfp : (F.homology n).IsFinitePresentation)
    (hd : F.d (n - 1) n = 0) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (F.cycles n) := by
  have : IsIso (F.homologyπ n) := F.isIso_homologyπ (n - 1) n (by simp) hd
  let e := asIso (F.homologyπ n)
  have : (F.cycles n).IsQuasicoherent := hqc
  have hh : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      (F.cycles n) ∧ (F.cycles n).IsFinitePresentation :=
    ⟨Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.isFlat_of_iso e.symm hflat,
      (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e.symm hfp⟩
  exact ((Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae (F.cycles n)).out 1 4).mp hh

/-- On a compact space, an open covering indexed by `I` and carrying integers `a i, b i` admits a
subfamily that still covers and whose intervals `[a i, b i]` are all contained in one interval
`[A, B]`. -/
private lemma exists_reindexed_cover_uniform_interval
    {T : Type u} [TopologicalSpace T] [CompactSpace T] {I : Type*}
    (U : I → Opens T) (hU : iSup U = ⊤) (a b : I → ℤ) :
    ∃ (A B : ℤ) (J : Type u) (ix : J → I), iSup (fun j => U (ix j)) = ⊤ ∧
      ∀ j : J, A ≤ a (ix j) ∧ b (ix j) ≤ B := by
  classical
  have hpt : ∀ x : T, ∃ i, x ∈ U i := fun x =>
    Opens.mem_iSup.mp (show x ∈ iSup U from by rw [hU]; trivial)
  choose ix hix using hpt
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : T => (U (ix x) : Set T))
    (fun x => (U (ix x)).2) (fun x _ => Set.mem_iUnion.mpr ⟨x, hix x⟩)
  refine ⟨-(s.sup fun y => (a (ix y)).natAbs : ℕ), (s.sup fun y => (b (ix y)).natAbs : ℕ),
    {y : T // y ∈ s}, fun y => ix y.1, ?_, fun y => ?_⟩
  · refine le_antisymm le_top fun x _ => Opens.mem_iSup.mpr ?_
    have hx := hs (Set.mem_univ x)
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨⟨y, hy⟩, hxy⟩
  · dsimp only
    have h₁ : ((a (ix y.1)).natAbs : ℤ) ≤ ((s.sup fun z => (a (ix z)).natAbs : ℕ) : ℤ) :=
      Int.ofNat_le.mpr (Finset.le_sup (f := fun z => (a (ix z)).natAbs) y.2)
    have h₂ : ((b (ix y.1)).natAbs : ℤ) ≤ ((s.sup fun z => (b (ix z)).natAbs : ℕ) : ℤ) :=
      Int.ofNat_le.mpr (Finset.le_sup (f := fun z => (b (ix z)).natAbs) y.2)
    omega

/-- **A perfect object of `D(O_X)` on a quasi-compact ringed space has Tor amplitude in a single
global interval.** Perfectness gives finite Tor amplitude locally, compactness shrinks the
covering to a finite subfamily, and widening the finitely many intervals to a common one lets the
locality of Tor amplitude glue them. -/
@[sga "6 III 4.2" "partial"]
private lemma exists_hasTorAmplitude_of_isPerfect
    (X : RingedSpace.{u, u}) [CompactSpace X.carrier]
    (K : DerivedCategory (OXMod.{u} X)) (hK : IsPerfect.{u, u, u + 1} K) :
    ∃ a b : ℤ, a ≤ b ∧
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude X K a b := by
  classical
  have hloc0 : ∃ (I : Type u) (U : I → Opens X.carrier), iSup U = ⊤ ∧
      ∀ i : I, ∃ a b : ℤ, Stacks.Cohomology.TorAmplitude.HasTorAmplitude.{u, u + 1}
        (X.restrict (U i).isOpenEmbedding)
        ((AlgebraicGeometry.RingedSpace.derivedRestrictModules X (U i)).obj K) a b :=
    Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_isPerfect (X := X) K hK
  obtain ⟨I, U, hU, hloc⟩ := hloc0
  choose a₀ b₀ hamp using hloc
  obtain ⟨A, B, J, ix, hcov, hbd⟩ := exists_reindexed_cover_uniform_interval U hU a₀ b₀
  refine ⟨A, max A B, le_max_left _ _,
    Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top _ K _ _
      (fun j => U (ix j)) hcov fun j => ?_⟩
  exact Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_mono.{u, u + 1}
    (hamp (ix j)) (hbd j).1 ((hbd j).2.trans (le_max_right A B))

/-- **A bounded-below perfect complex on a quasi-compact scheme has Tor amplitude in an interval
whose left end also bounds its nonzero terms.** Intersecting a global Tor-amplitude interval with
a degree below which the complex vanishes gives such a pair. -/
@[sga "6 III 4.2" "Quasi-compact clause"]
private lemma exists_torAmplitude_with_lower_term_bound
    (X : Scheme.{u}) [CompactSpace X] (F : CochainComplex X.Modules ℤ)
    (hFplus : CochainComplex.plus X.Modules F)
    (hFperf : IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj F)) :
    ∃ a b : ℤ, a ≤ b ∧ F.IsStrictlyGE a ∧
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
        (DerivedCategory.Q.obj F) a b := by
  obtain ⟨c, hc⟩ := (CochainComplex.plus_iff _ F).mp hFplus
  obtain ⟨a, b, -, hamp⟩ := exists_hasTorAmplitude_of_isPerfect X.toRingedSpace _ hFperf
  refine ⟨min c a, max b (min c a), le_max_right _ _,
    F.isStrictlyGE_of_ge _ c (min_le_left c a),
    Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_mono.{u, u + 1} hamp
      (min_le_right c a) (le_max_left b (min c a))⟩

/-- A perfect object of the derived category of `𝒪_X`-modules on a scheme is
pseudo-coherent. -/
@[sga "6 I 5.8" "special case"]
private lemma isPseudoCoherent_of_isPerfect (X : Scheme.{u}) (K : DerivedCategory X.Modules)
    (hK : IsPerfect (X := X.toRingedSpace) K) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K :=
  (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
    (X := X.toRingedSpace) K).mp
      (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect K hK)

/-- The top nonvanishing cohomology sheaf of a perfect complex of `𝒪_X`-modules is of finite
type. -/
private lemma isFiniteType_homology_of_isPerfect (X : Scheme.{u})
    (F : CochainComplex X.Modules ℤ)
    (hFperf : IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj F)) (n : ℤ)
    (hvanish : ∀ i : ℤ, n < i → IsZero (F.homology i)) :
    (F.homology n).IsFiniteType := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := isPseudoCoherent_of_isPerfect X (DerivedCategory.Q.obj F) hFperf
  have hpc : AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace)
      (DerivedCategory.Q.obj F) n := ⟨K, hK n, ⟨eK⟩⟩
  have hv : ∀ i : ℤ, n < i →
      IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj (DerivedCategory.Q.obj F)) :=
    fun i hi => (hvanish i hi).of_iso ((DerivedCategory.homologyFunctorFactors X.Modules i).app F)
  have h : ((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor X.Modules n).obj
      F).IsFiniteType :=
    AlgebraicGeometry.RingedSpace.isFiniteType_homology_of_isPseudoCoherentFrom
      (X := X.toRingedSpace) (DerivedCategory.Q.obj F) n hpc hv
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    ((DerivedCategory.homologyFunctorFactors X.Modules n).app F)

/-- The top nonvanishing cohomology sheaf of a perfect complex of `𝒪_X`-modules is finitely
presented. -/
private lemma isFinitePresentation_homology_of_isPerfect (X : Scheme.{u})
    (F : CochainComplex X.Modules ℤ)
    (hFperf : IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj F)) (n : ℤ)
    (hvanish : ∀ i : ℤ, n < i → IsZero (F.homology i)) :
    (F.homology n).IsFinitePresentation := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := isPseudoCoherent_of_isPerfect X (DerivedCategory.Q.obj F) hFperf
  have hpc : AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace)
      (DerivedCategory.Q.obj F) (n - 1) := ⟨K, hK (n - 1), ⟨eK⟩⟩
  have hv : ∀ i : ℤ, n - 1 + 1 < i →
      IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj (DerivedCategory.Q.obj F)) :=
    fun i hi => (hvanish i (by omega)).of_iso
      ((DerivedCategory.homologyFunctorFactors X.Modules i).app F)
  have h := AlgebraicGeometry.RingedSpace.isFinitePresentation_homology_of_isPseudoCoherentFrom
    (X := X.toRingedSpace) (DerivedCategory.Q.obj F) (n - 1) hpc hv
  simp only [sub_add_cancel] at h
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctorFactors X.Modules n).app F) h

/-- **The base case of Stacks 0F8E.** A bounded-below perfect complex of quasi-coherent modules
with Tor amplitude concentrated in the single degree `a` is quasi-isomorphic to its module of
`a`-cycles placed in degree `a`, and that module is finite locally free. -/
private lemma exists_singleton_amplitude_replacement (X : Scheme.{u})
    (F : CochainComplex X.Modules ℤ) (hFqc : ∀ i : ℤ, (F.X i).IsQuasicoherent)
    (hFperf : IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj F))
    (a : ℤ) (hFge : F.IsStrictlyGE a)
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj F) a a) :
    ∃ (E : CochainComplex X.Modules ℤ) (f : E ⟶ F),
      (E.IsStrictlyGE a ∧ E.IsStrictlyLE a) ∧
        (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
          (R := X.ringCatSheaf) (E.X i)) ∧ QuasiIso f := by
  have hd : F.d (a - 1) a = 0 :=
    (F.isZero_of_isStrictlyGE a (a - 1) (by omega)).eq_of_src _ _
  have hzero (i : ℤ) (hi : i ≠ a) : IsZero (F.homology i) :=
    isZero_homology_of_hasTorAmplitude X F a a le_rfl hamp i (by simp only [Set.mem_Icc]; omega)
  have hiso : IsIso (𝟙 (F.cycles a) ≫ F.homologyπ a) := by
    rw [Category.id_comp]
    exact F.isIso_homologyπ (a - 1) a (by simp) hd
  refine ⟨(HomologicalComplex.single X.Modules (ComplexShape.up ℤ) a).obj (F.cycles a),
    singleToCycles F a (𝟙 _),
    ⟨(CochainComplex.isStrictlyGE_iff _ a).2 fun i hi =>
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (F.cycles a) i (by omega),
      (CochainComplex.isStrictlyLE_iff _ a).2 fun i hi =>
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (F.cycles a) i (by omega)⟩,
    isFiniteLocallyFree_single_terms X _ a
      (isFiniteLocallyFree_cycles_of_isFlat_homology X F a
        (cycles_isQuasicoherent X F hFqc a)
        (isFlat_homology_of_hasTorAmplitude_singleton X F a hamp)
        (isFinitePresentation_homology_of_isPerfect X F hFperf a
          fun i hi => hzero i (by omega)) hd),
    quasiIso_singleToCycles F a _ hiso hzero⟩

/-- A finite locally free module on a scheme is quasi-coherent, being finitely presented. -/
private lemma isQuasicoherent_of_isFiniteLocallyFree (X : Scheme.{u}) (M : X.Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) M) :
    M.IsQuasicoherent := by
  have hM' : Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := X.ringCatSheaf) M :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u}
      hM.exists_isFiniteLocallyFreeData
  have hfpM : M.IsFinitePresentation := Stacks.FiniteLocallyFree.isFinitePresentation M
  obtain ⟨σ, -⟩ := hfpM.1
  exact σ.isQuasicoherent

/-- **The resolution property applied to the cycles.** A finite locally free module maps to the
`n`-cycles of a complex of quasi-coherent modules so that the composite to `H^n` is surjective,
whenever `H^n` is of finite type. -/
private lemma exists_finiteLocallyFree_cycle_epi
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [AlgebraicGeometry.HasResolutionProperty X]
    (F : CochainComplex X.Modules ℤ)
    (hFqc : ∀ i : ℤ, (F.X i).IsQuasicoherent) (n : ℤ)
    (hHft : (F.homology n).IsFiniteType) :
    ∃ P : X.Modules,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) P ∧
        ∃ π : P ⟶ F.cycles n, Epi (π ≫ F.homologyπ n) := by
  obtain ⟨S, hSqc, hSft, hSepi⟩ :=
    exists_finiteType_cycle_subobject_epi X F hFqc n hHft
  have _ : (S : X.Modules).IsQuasicoherent := hSqc
  have _ : (S : X.Modules).IsFiniteType := hSft
  obtain ⟨P, hP, π, hπ⟩ :=
    AlgebraicGeometry.HasResolutionProperty.exists_finiteLocallyFree_quotient
      (X := X) (F := (S : X.Modules))
  exact ⟨P, hP, π ≫ S.arrow, by simpa only [Category.assoc] using epi_comp' hπ hSepi⟩

/-- **The induction step's one-step reduction.** Below the top nonvanishing degree `b`, a finite
locally free module maps to the `b`-cycles so that the cone of the induced map from it, placed
in degree `b`, has vanishing cohomology in every degree at least `b`. -/
private lemma exists_finiteLocallyFree_single_cone_vanishes_above
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [AlgebraicGeometry.HasResolutionProperty X]
    (F : CochainComplex X.Modules ℤ)
    (hFqc : ∀ i : ℤ, (F.X i).IsQuasicoherent)
    (hFperf : IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj F))
    (b : ℤ) (hFzero : ∀ i : ℤ, b < i → IsZero (F.homology i)) :
    ∃ P : X.Modules,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) P ∧
        ∃ π : P ⟶ F.cycles b, ∀ i : ℤ, b ≤ i →
          IsZero ((CochainComplex.mappingCone (singleToCycles F b π)).homology i) := by
  obtain ⟨P, hP, π, hπ⟩ := exists_finiteLocallyFree_cycle_epi X F hFqc b
    (isFiniteType_homology_of_isPerfect X F hFperf b hFzero)
  have hα := epi_homologyMap_singleToCycles F b π hπ
  refine ⟨P, hP, π, fun i hi => ?_⟩
  have hsingle := HomologicalComplex.isZero_single_obj_homology
    (ComplexShape.up ℤ) b P (i + 1) (by omega)
  obtain rfl | hi := hi.eq_or_lt
  · exact isZero_homology_mappingCone_of_epi (singleToCycles F b π) b hsingle
  · exact isZero_homology_mappingCone_of_isZero (singleToCycles F b π) i
      (hFzero i hi) hsingle

/-- **The induction of Stacks 0F8E.** A bounded-below perfect complex of quasi-coherent modules
with Tor amplitude in `[a, a + n]` admits a quasi-isomorphism onto it from a complex of finite
locally free modules concentrated in degrees `[a, a + n]`. -/
private lemma exists_replacement_of_amplitude
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [AlgebraicGeometry.HasResolutionProperty X] (n : ℕ) :
    ∀ (a : ℤ) (F : CochainComplex X.Modules ℤ),
      (∀ i : ℤ, (F.X i).IsQuasicoherent) →
      IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj F) →
      F.IsStrictlyGE a →
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
        (DerivedCategory.Q.obj F) a (a + n) →
      ∃ (E : CochainComplex X.Modules ℤ) (f : E ⟶ F),
        (E.IsStrictlyGE a ∧ E.IsStrictlyLE (a + n)) ∧
          (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
            (R := X.ringCatSheaf) (E.X i)) ∧ QuasiIso f := by
  induction n with
  | zero =>
    intro a F hqc hp hge ht
    simpa only [Nat.cast_zero, add_zero] using
      exists_singleton_amplitude_replacement X F hqc hp a hge (by simpa using ht)
  | succ n ih =>
    intro a F hqc hp hge ht
    set b : ℤ := a + ((n + 1 : ℕ) : ℤ) with hbdef
    have hbval : b = a + (n : ℤ) + 1 := by rw [hbdef]; push_cast; ring
    have hab : a < b := by omega
    have htb : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
        (DerivedCategory.Q.obj F) a b := ht
    obtain ⟨P, hP, π, hz⟩ := exists_finiteLocallyFree_single_cone_vanishes_above
      X F hqc hp b (fun i hi => isZero_homology_of_hasTorAmplitude X F a b hab.le htb i
        (by simp only [Set.mem_Icc, not_and_or, not_le]; omega))
    set A : CochainComplex X.Modules ℤ :=
      (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) b).obj P with hAdef
    set α : A ⟶ F := singleToCycles F b π with hαdef
    set C : CochainComplex X.Modules ℤ := CochainComplex.mappingCone α with hCdef
    have hAterms := isFiniteLocallyFree_single_terms X P b hP
    have hAge : A.IsStrictlyGE b := (CochainComplex.isStrictlyGE_iff A b).2
      (fun i hi => HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) b P i (by omega))
    have hCle : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
        (DerivedCategory.Q.obj C) a (b - 1) := by
      refine hasTorAmplitude_of_isZero_top_homology (DerivedCategory.Q.obj C) a b hab ?_ ?_
      · exact hasTorAmplitude_mappingCone α a b
          (Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_mono.{u, u + 1}
            (hasTorAmplitude_single_isFiniteLocallyFree X P hP b)
            (by omega) (by omega)) htb
      · exact (hz b le_rfl).of_iso ((DerivedCategory.homologyFunctorFactors X.Modules b).app C)
    have hCqc (i : ℤ) : (C.X i).IsQuasicoherent :=
      mappingCone_isQuasicoherent α (fun j => isQuasicoherent_of_isFiniteLocallyFree X _
        (hAterms j)) hqc i
    have hCp := isPerfect_mappingCone α (isPerfect_single_isFiniteLocallyFree X P hP b) hp
    have hCge : C.IsStrictlyGE a := by
      have := hAge
      have := hge
      exact CochainComplex.isStrictlyGE_mappingCone α b a a hab le_rfl
    obtain ⟨E, g, ⟨hEge, hEle⟩, hEterms, hg⟩ :=
      ih a C hCqc hCp hCge (by convert hCle using 2; omega)
    have _ := hg
    set δ := g ≫ (CochainComplex.mappingCone.triangle α).mor₃ with hδdef
    set S : CochainComplex X.Modules ℤ := (CochainComplex.mappingCone δ)⟦(-1 : ℤ)⟧ with hSdef
    obtain ⟨f, hf⟩ := exists_quasiIso_from_shifted_mappingCone α g
    have e (i : ℤ) : S.X i ≅ E.X i ⊞ A.X i :=
      CochainComplex.shiftFunctorObjXIso _ (-1) i (i - 1) (by omega) ≪≫
        HomologicalComplex.homotopyCofiber.XIsoBiprod δ (i - 1) i (by simp) ≪≫
          biprod.mapIso (Iso.refl _)
            (CochainComplex.shiftFunctorObjXIso A 1 (i - 1) i (by omega))
    have _ := hEge
    have _ := hEle
    have hzS (i : ℤ) (hi : i < a ∨ b < i) : IsZero (S.X i) := by
      refine IsZero.of_iso ?_ (e i)
      refine (biprod_isZero_iff _ _).2 ⟨?_, ?_⟩
      · rcases hi with hi | hi
        · exact E.isZero_of_isStrictlyGE a i hi
        · exact E.isZero_of_isStrictlyLE (a + n) i (by omega)
      · exact HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) b P i (by omega)
    have hSterms (i : ℤ) : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
        (R := X.ringCatSheaf) (S.X i) := by
      by_cases hi : i = b
      · exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
          (isoZeroBiprod (Y := A.X i)
            (E.isZero_of_isStrictlyLE (a + n) i (by omega)) ≪≫ (e i).symm) (h := hAterms i)
      · exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
          (isoBiprodZero (X := E.X i)
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) b P i hi) ≪≫
              (e i).symm) (h := hEterms i)
    refine ⟨S, f, ⟨(CochainComplex.isStrictlyGE_iff S a).2 (fun i hi => hzS i (.inl hi)),
      (CochainComplex.isStrictlyLE_iff S b).2
        (fun i hi => hzS i (.inr hi))⟩, hSterms, hf⟩

/-- **Stacks Project, Tag 0F8E.** On a quasi-compact and quasi-separated scheme with the
resolution property, a bounded below complex of quasi-coherent modules representing a perfect
object of the derived category receives a quasi-isomorphism from a bounded complex of finite
locally free modules. -/
@[stacks 0F8E]
theorem exists_boundedFiniteLocallyFree_quasiIso (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [AlgebraicGeometry.HasResolutionProperty X]
    (F : CochainComplex X.Modules ℤ)
    (hFplus : CochainComplex.plus X.Modules F)
    (hFqc : ∀ i : ℤ, (F.X i).IsQuasicoherent)
    (hFperf : IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj F)) :
    ∃ (E : CochainComplex X.Modules ℤ) (f : E ⟶ F),
      boundedFiniteLocallyFreeComplex X E ∧ QuasiIso f := by
  obtain ⟨a, b, hab, hge, hamp⟩ := exists_torAmplitude_with_lower_term_bound X F hFplus hFperf
  have hb : a + (((b - a).toNat : ℕ) : ℤ) = b := by omega
  obtain ⟨E, f, ⟨hEge, hEle⟩, hEterms, hf⟩ :=
    exists_replacement_of_amplitude X (b - a).toNat a F hFqc hFperf hge (by rw [hb]; exact hamp)
  exact ⟨E, f, ⟨⟨⟨a, hEge⟩, ⟨_, hEle⟩⟩,
    fun i => AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u}
      (hEterms i).exists_isFiniteLocallyFreeData⟩, hf⟩

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
