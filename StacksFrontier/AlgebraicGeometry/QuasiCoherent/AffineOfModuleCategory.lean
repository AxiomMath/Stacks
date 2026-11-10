module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.LinearAlgebra.Center
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerConstraints
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitFinitePresentationSite
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneIff.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.AlgebraicGeometry.QcohPushforwardOpen.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.CompactObjects
public import StacksFrontier.AlgebraicGeometry.QuasicoherentExtension.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.Affine
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.VanishingCriterion
public import StacksFrontier.AlgebraicGeometry.SerreCriterionH1.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.Topology.Sheaves.Cohomology.Extensions.FirstCohomologyAndExtensions
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksFrontier.Topology.Sheaves.Modules.Invertible
public import StacksFrontier.Topology.Sheaves.Skyscraper.Modules
import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact

/-!
# Affineness of a scheme whose quasi-coherent modules form a module category

A quasi-compact and quasi-separated scheme `X` whose category of quasi-coherent
`𝒪_X`-modules is equivalent to the category of modules over a commutative ring is affine.
The argument runs through the object of `QCoh(𝒪_X)` corresponding to the ring regarded as a
module over itself: it is of finite presentation, projective, a separator, and its
endomorphisms commute, and those four properties force it to be finite locally free of rank
one. Tensoring by such a module is an equivalence of `QCoh(𝒪_X)`, so the structure sheaf is
projective as well, every first cohomology group of a quasi-coherent ideal sheaf vanishes,
and Serre's criterion applies.

## Main results

* `AlgebraicGeometry.AffineOfModuleCategory.isAffine_of_quasicoherentModules_equivalent_moduleCat`:
  **Stacks 0GPI**.

## References

* [Stacks Project, Tag 0GPI](https://stacks.math.columbia.edu/tag/0GPI)
-/

@[expose] public section

open CategoryTheory
open Module LinearMap
open CategoryTheory.Limits MonoidalCategory
open TensorProduct

universe u v

namespace AlgebraicGeometry.AffineOfModuleCategory

open AlgebraicGeometry TopologicalSpace

/- The elaborator must see through the following abbreviations for the proofs below to
typecheck: the structure sheaf of a scheme, its category of modules, the sheafified tensor
product and the unit object are each reached through a chain of definitions that the
`implicit` transparency level does not unfold on its own, so instances stated at one
spelling are not found at another. -/
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  PresheafOfModules.presheaf SheafOfModules.unit PresheafOfModules.unit
  AlgebraicGeometry.Scheme.residueField
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
  Stacks.SheafOfModules.TensorSheafification.sheafify
  PresheafOfModules.sheafificationAdjunction CategoryTheory.Abelian.extFunctorObj
  AlgebraicGeometry.Scheme.Modules.overEquiv AlgebraicGeometry.Scheme.Modules.fromTildeΓ
  AlgebraicGeometry.Scheme.Modules.restrictFunctor CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

attribute [local implicit_reducible] SheafOfModules.GeneratingSections.ofEpi in
/-- **A finitely presented module whose stalks at the closed points are free of rank `r` is
finite locally free of rank `r`**, on a compact `T₀` space: each closed point has an open
neighbourhood on which the module is free, and these neighbourhoods cover, since every nonempty
closed subset of a compact `T₀` space contains a closed point. -/
theorem isFiniteLocallyFreeOfRank_of_closedPoint_stalks
    {X : TopCat.{u}} [CompactSpace X] [T0Space X] {R : TopCat.Sheaf RingCat.{u} X}
    (M : SheafOfModules.{u} R) (hM : M.IsFinitePresentation) (r : ℕ)
    (h : ∀ x : X, IsClosed ({x} : Set X) → Nonempty
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x) ≃ₗ[ToType (R.presheaf.stalk x)]
        (ULift.{u} (Fin r) →₀ ToType (R.presheaf.stalk x)))) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens X)
      (J := Opens.grothendieckTopology X) M r := by
  classical
  let I := {x : X // IsClosed ({x} : Set X)}
  choose U hx he using fun x : I =>
    Stacks.SheafOfModules.exists_iso_free_over_of_stalk_iso_free M hM x.1 r (h x.1 x.2)
  let e (i : I) := (he i).some
  have hU : (Opens.grothendieckTopology X).CoversTop U := by
    rw [Opens.coversTop_iff, IsOpenCover, eq_top_iff]
    intro x _
    by_contra hn
    have hclosed : IsClosed ((↑(⨆ i, U i) : Set X)ᶜ) := (⨆ i, U i).isOpen.isClosed_compl
    obtain ⟨y, hy, hyc⟩ := hclosed.exists_closed_singleton ⟨x, hn⟩
    exact hy (Opens.mem_iSup.mpr ⟨⟨y, hyc⟩, hx ⟨y, hyc⟩⟩)
  let q : SheafOfModules.LocalGeneratorsData.{u} M :=
    { I := I
      X := U
      coversTop := hU
      generators := fun i =>
        (SheafOfModules.free.generatingSections (ULift.{u} (Fin r))).ofEpi (e i).inv }
  refine @AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.mk.{u, u, u}
    (Opens X) _ (Opens.grothendieckTopology X) R _ _ M r ⟨q, ?_, ?_⟩
  · constructor
    intro i
    change IsIso ((SheafOfModules.free.generatingSections
      (ULift.{u} (Fin r))).ofEpi (e i).inv).π
    simp only [SheafOfModules.GeneratingSections.ofEpi_π,
      SheafOfModules.free.generatingSections_π]
    exact (e i).isIso_inv
  · intro i
    exact ⟨Equiv.ulift⟩

private alias isFiniteLocallyFreeOfRank_of_closed_stalks :=
    isFiniteLocallyFreeOfRank_of_closedPoint_stalks

attribute [local implicit_reducible] TopCat.Sheaf

private theorem endomorphism_map_surjective_of_projective_of_epi_unit
    {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (P : C) [Projective P] [Epi (adj.unit.app P)] :
    Function.Surjective (F.map : (P ⟶ P) → (F.obj P ⟶ F.obj P)) := by
  intro f
  let g := Projective.factorThru (adj.homEquiv P (F.obj P) f) (adj.unit.app P)
  refine ⟨g, (adj.homEquiv P (F.obj P)).injective ?_⟩
  rw [adj.homEquiv_unit]
  calc
    adj.unit.app P ≫ G.map (F.map g) = g ≫ adj.unit.app P :=
      (adj.unit.naturality g).symm
    _ = (adj.homEquiv P (F.obj P)) f := Projective.factorThru_comp _ _

private theorem endomorphisms_commute_of_projective_of_epi_unit
    {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (P : C) [Projective P] [Epi (adj.unit.app P)]
    (hP : ∀ f g : P ⟶ P, f ≫ g = g ≫ f)
    (f g : F.obj P ⟶ F.obj P) : f ≫ g = g ≫ f := by
  obtain ⟨f, rfl⟩ := endomorphism_map_surjective_of_projective_of_epi_unit adj P f
  obtain ⟨g, rfl⟩ := endomorphism_map_surjective_of_projective_of_epi_unit adj P g
  simp only [← F.map_comp, hP f g]

private theorem free_of_residueField_dual_lifts
    (R M : Type*) [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (hlift : ∀ f : M →ₗ[R] IsLocalRing.ResidueField R,
      ∃ g : M →ₗ[R] R, ∀ m, IsLocalRing.residue R (g m) = f m) :
    Module.Free R M := by
  classical
  let k := IsLocalRing.ResidueField R
  let V := k ⊗[R] M
  let b := Module.finBasis k V
  let ι := Fin (Module.finrank k V)
  let t : M →ₗ[R] V := TensorProduct.mk R k M 1
  have ht : Function.Surjective t :=
    TensorProduct.mk_surjective R M k IsLocalRing.residue_surjective
  choose v hv using fun i : ι => ht (b i)
  let c := Pi.basisFun R ι
  let g : (ι → R) →ₗ[R] M := c.constr R v
  have hg : Function.Surjective g := by
    apply LinearMap.range_eq_top.mp
    rw [Module.Basis.constr_range]
    exact IsLocalRing.span_eq_top_of_tmul_eq_basis v b hv
  choose l hl using fun i : ι => hlift (((b.coord i).restrictScalars R).comp t)
  let f : M →ₗ[R] (ι → R) := LinearMap.pi l
  let q : (ι → R) →ₗ[R] (ι → k) :=
    LinearMap.pi (fun i => (Algebra.linearMap R k).comp (LinearMap.proj i))
  have hcomp : q.comp (f.comp g) = q := by
    apply c.ext
    intro j
    ext i
    change IsLocalRing.residue R (l i (g (c j))) = IsLocalRing.residue R (c j i)
    rw [show g (c j) = v j from c.constr_basis R v j, hl i]
    change b.coord i (t (v j)) = _
    rw [hv j]
    by_cases hij : j = i <;> simp [c, Module.Basis.coord_apply,
      Module.Basis.repr_self, Pi.basisFun_apply, hij]
  let t' : (ι → R) →ₗ[R] k ⊗[R] (ι → R) := TensorProduct.mk R k (ι → R) 1
  have hqm (z : ι → R) : TensorProduct.piScalarRight R k k ι (t' z) = q z := by
    ext i
    simp [t', q, Algebra.smul_def]
  have hA : Function.Surjective (f.comp g) := by
    apply LinearMap.range_eq_top.mp
    apply IsLocalRing.map_tensorProduct_mk_eq_top.mp
    rw [← LinearMap.range_comp]
    apply LinearMap.range_eq_top.mpr
    intro z
    obtain ⟨y, rfl⟩ := TensorProduct.mk_surjective R (ι → R) k
      IsLocalRing.residue_surjective z
    refine ⟨y, ?_⟩
    apply (TensorProduct.piScalarRight R k k ι).injective
    change TensorProduct.piScalarRight R k k ι (t' (f (g y))) =
      TensorProduct.piScalarRight R k k ι (t' y)
    rw [hqm, hqm]
    exact DFunLike.congr_fun hcomp y
  have hinj : Function.Injective g := by
    intro a b hab
    exact OrzechProperty.injective_of_surjective_of_injective
      (LinearMap.id : (ι → R) →ₗ[R] (ι → R)) (f.comp g) Function.injective_id hA (congrArg f hab)
  exact Module.Free.of_equiv (LinearEquiv.ofBijective g ⟨hinj, hg⟩)

private theorem nonempty_equiv_finsupp_of_residueField_dual_lifts
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (r : ℕ)
    (hlift : ∀ f : M →ₗ[R] IsLocalRing.ResidueField R,
      ∃ g : M →ₗ[R] R, ∀ m, IsLocalRing.residue R (g m) = f m)
    (hrank : Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] M) = r) :
    Nonempty (M ≃ₗ[R] (ULift.{u} (Fin r) →₀ R)) := by
  let : Module.Free R M := free_of_residueField_dual_lifts R M hlift
  have hdim : Module.finrank R M = r := by
    rwa [Module.finrank_baseChange] at hrank
  exact ⟨((Module.finBasisOfFinrankEq R M hdim).reindex Equiv.ulift.symm).repr⟩

private theorem finrank_le_one_of_commutative_endomorphisms
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hcomm : ∀ f g : V →ₗ[K] V, Commute f g) : finrank K V ≤ 1 := by
  classical
  by_contra hn
  have hn2 : 2 ≤ finrank K V := by omega
  let b := Module.finBasis K V
  let i : Fin (finrank K V) := ⟨0, by omega⟩
  let j : Fin (finrank K V) := ⟨1, by omega⟩
  let _ : Nontrivial (Fin (finrank K V)) := Fin.nontrivial_iff_two_le.mpr hn2
  have hij : i ≠ j := by simp [i, j]
  let t : V →ₗ[K] V := LinearMap.transvection (b.coord i) (b j)
  have ht : ∃ a : Subring.center K, t = a • 1 := by
    apply LinearMap.commute_transvections_iff_of_basis b
    intro i' j' r hij'
    exact hcomm t ((b.coord i').transvection (r • b j'))
  obtain ⟨a, ha⟩ := ht
  have hj : b.coord j (t (b i)) = 1 := by
    simp [t, LinearMap.transvection.apply, Module.Basis.coord_apply,
      Module.Basis.repr_self, i, j]
  have hzero : b.coord j ((a • (1 : V →ₗ[K] V)) (b i)) = 0 := by
    simp [Subring.smul_def, Module.Basis.coord_apply, Module.Basis.repr_self, i, j]
  have hcommute := congrArg (fun f : V →ₗ[K] V => b.coord j (f (b i))) ha
  rw [hj, hzero] at hcommute
  exact one_ne_zero hcommute

private theorem finrank_eq_one_of_nontrivial_commutative_endomorphisms
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Nontrivial V] (hcomm : ∀ f g : V →ₗ[K] V, Commute f g) : finrank K V = 1 := by
  have hpos : 0 < finrank K V := Module.finrank_pos_iff.mpr inferInstance
  have hle := finrank_le_one_of_commutative_endomorphisms hcomm
  omega

private theorem nontrivial_of_moduleCat_isSeparator (K : Type u) [Field K]
    (M : ModuleCat.{u} K) (hM : IsSeparator M) : Nontrivial M := by
  by_contra hn
  have : Subsingleton M := not_nontrivial_iff_subsingleton.mp hn
  let N := ModuleCat.of K K
  have h : (𝟙 N : N ⟶ N) = 0 := by
    apply hM.def
    intro f
    have hf : f = 0 := by
      apply ModuleCat.hom_ext
      ext x
      rw [Subsingleton.elim x 0]
      simp
    simp [hf]
  have h' := congrArg (fun g : N ⟶ N => g.hom 1) h
  exact one_ne_zero h'

private theorem finrank_eq_one_of_projective_separator_of_epi_unit
    {C : Type*} [Category* C] (K : Type u) [Field K]
    {F : C ⥤ ModuleCat.{u} K} {G : ModuleCat.{u} K ⥤ C} [G.Faithful]
    (adj : F ⊣ G) (P : C) [Projective P] [Epi (adj.unit.app P)]
    [Module.Finite K (F.obj P)] (hsep : IsSeparator P)
    (hcomm : ∀ f g : P ⟶ P, f ≫ g = g ≫ f) :
    Module.finrank K (F.obj P) = 1 := by
  let : Nontrivial (F.obj P) :=
    nontrivial_of_moduleCat_isSeparator K _ (hsep.leftAdjoint_obj adj)
  apply finrank_eq_one_of_nontrivial_commutative_endomorphisms
  intro f g
  have h := endomorphisms_commute_of_projective_of_epi_unit adj P hcomm
    (ModuleCat.ofHom f) (ModuleCat.ofHom g)
  exact (congrArg ModuleCat.Hom.hom h).symm

private theorem end_comm_of_linearEquiv_to_regular
    {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    (e : M ≃ₗ[K] K) (f g : M →ₗ[K] M) : Commute f g := by
  let f' : Module.End K K := e.toLinearMap.comp (f.comp e.symm.toLinearMap)
  let g' : Module.End K K := e.toLinearMap.comp (g.comp e.symm.toLinearMap)
  have h (a : Module.End K K) (x : K) : a x = x * a 1 := by
    simpa using a.map_smul x 1
  apply LinearMap.ext
  intro x
  apply e.injective
  calc
    e (f (g x)) = f' (g' (e x)) := by simp [f', g']
    _ = g' (f' (e x)) := by
      rw [h f' (g' (e x)), h g' (e x), h g' (f' (e x)), h f' (e x)]
      ring_nf
    _ = e (g (f x)) := by simp [f', g']

private noncomputable def freeUnitCoyonedaIsoForget (T : Type u) [Ring T] :
    coyoneda.obj (Opposite.op ((ModuleCat.free T).obj PUnit.{u + 1})) ≅
      forget (ModuleCat.{u} T) :=
  NatIso.ofComponents
    (fun M =>
      (((ModuleCat.freeHomEquiv (R := T) (X := PUnit.{u + 1}) (M := M)).trans
        (TypeCat.homEquiv.trans
          ({ toFun := fun f => f PUnit.unit
             invFun := fun m => fun (_ : PUnit.{u + 1}) => m
             left_inv := by intro f; funext x; cases x; rfl
             right_inv := by intro m; rfl } : (PUnit.{u + 1} → M) ≃ M))).toIso))
    (by intro M N f; ext g; rfl)

private theorem freeUnit_isFinitelyPresentable (T : Type u) [Ring T] :
    IsFinitelyPresentable.{u} ((ModuleCat.free T).obj PUnit.{u + 1}) := by
  rw [isFinitelyPresentable_iff_preservesFilteredColimits]
  refine ⟨fun J _ _ => ?_⟩
  have : PreservesColimitsOfShape J (forget (ModuleCat.{u} T)) := inferInstance
  exact preservesColimitsOfShape_of_natIso (freeUnitCoyonedaIsoForget T).symm

private theorem regularModule_isFinitelyPresentable (T : Type u) [CommRing T] :
    IsFinitelyPresentable.{u} (ModuleCat.of T T) := by
  let : Fact (Cardinal.aleph0.IsRegular) := Cardinal.fact_isRegular_aleph0
  let : IsFinitelyPresentable.{u} ((ModuleCat.free T).obj PUnit.{u + 1}) :=
    freeUnit_isFinitelyPresentable T
  exact isCardinalPresentable_of_iso (ModuleCat.FreeMonoidal.εIso T).symm Cardinal.aleph0

private theorem regularModule_isSeparator (R : Type u) [Ring R] :
    IsSeparator (ModuleCat.of R R) := fun M N f g h => by
  simp only [ObjectProperty.singleton_iff, ModuleCat.hom_ext_iff, ModuleCat.hom_comp,
    LinearMap.ext_iff, LinearMap.coe_comp, Function.comp_apply, forall_eq'] at h
  ext m
  simpa using h (ModuleCat.ofHom (LinearMap.toSpanSingleton R M m)) 1

private theorem regularModule_end_commute (R : Type u) [CommRing R]
    (f g : ModuleCat.of R R ⟶ ModuleCat.of R R) : f ≫ g = g ≫ f :=
  ModuleCat.hom_ext (end_comm_of_linearEquiv_to_regular (LinearEquiv.refl R R) f.hom g.hom).eq.symm

private theorem annihilator_mono_of_separator (R : Type v) [CommRing R]
    (Q M : ModuleCat.{u} R) (hQ : IsSeparator Q) :
    Module.annihilator R Q ≤ Module.annihilator R M := by
  intro r hr
  apply Module.mem_annihilator.mpr
  intro m
  let φ : M ⟶ M := ModuleCat.ofHom (LinearMap.lsmul R M r)
  have hf (g : Q ⟶ M) : g ≫ φ = g ≫ 0 := by
    apply ModuleCat.hom_ext
    ext q
    change r • g.hom q = 0
    rw [← g.hom.map_smul, (Module.mem_annihilator.mp hr q)]
    simp
  have hφ : φ = 0 := hQ.def φ 0 hf
  have hlin : LinearMap.lsmul R M r = 0 := by
    have := congrArg ModuleCat.Hom.hom hφ
    simpa [φ] using this
  have hm := congrArg (fun f : Module.End R M => f m) hlin
  simpa [LinearMap.lsmul_apply] using hm

private theorem separator_annihilator_torsion (R : Type v) [CommRing R]
    (Q M : ModuleCat.{u} R) (hQ : IsSeparator Q) :
    Module.IsTorsionBySet R M (Module.annihilator R Q) := by
  intro m r
  exact (Module.mem_annihilator.mp
    (annihilator_mono_of_separator R Q M hQ r.property)) m

private noncomputable def scalarAction (R : Type v) [CommRing R] (Q : ModuleCat.{u} R) :
    R →+* Module.End R (Q : Type u) := (Algebra.lsmul R R Q).toRingHom

private theorem quotient_annihilator_small (R : Type v) [CommRing R]
    (Q : ModuleCat.{u} R) : Small.{u} (R ⧸ Module.annihilator R Q) := by
  let I := Module.annihilator R Q
  let f : R ⧸ I →+* Module.End R (Q : Type u) :=
    Ideal.Quotient.lift I (scalarAction R Q) (by
      intro r hr
      apply LinearMap.ext
      intro q
      simp [scalarAction, Algebra.lsmul_apply, Module.mem_annihilator.mp hr q])
  apply small_of_injective (f := f)
  intro a b hab
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply (Ideal.Quotient.eq (I := I)).2
  apply Module.mem_annihilator.mpr
  intro q
  have hrs : scalarAction R Q r = scalarAction R Q s := by simpa [f] using hab
  have hq := congrArg (fun z : Module.End R Q => z q) hrs
  rw [sub_smul]
  exact sub_eq_zero.mpr (by simpa [scalarAction, Algebra.lsmul_apply] using hq)

private theorem equivalence_source_separator (X : Scheme.{u}) (R : Type v) [CommRing R]
    (e : ModuleCat.{u} R ≌
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    IsSeparator (e.inverse.obj
      (CategoryTheory.separator
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)) := by
  let C := (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory
  let _ : IsGrothendieckAbelian C :=
    AlgebraicGeometry.quasicoherentModules_isGrothendieckAbelian X
  exact (isSeparator_separator C).of_equivalence e.symm

private noncomputable def quotientModuleFunctor (R : Type v) [CommRing R]
    (Q : ModuleCat.{u} R) (hQ : IsSeparator Q) : ModuleCat.{u} R ⥤
      ModuleCat.{u} (R ⧸ Module.annihilator R Q) where
  obj M := by
    letI : Module (R ⧸ Module.annihilator R Q) M :=
      (separator_annihilator_torsion R Q M hQ).module
    exact ModuleCat.of _ M
  map {M N} f := by
    let hM := separator_annihilator_torsion R Q M hQ
    let hN := separator_annihilator_torsion R Q N hQ
    letI : Module (R ⧸ Module.annihilator R Q) M := hM.module
    letI : Module (R ⧸ Module.annihilator R Q) N := hN.module
    let g : M →ₗ[R ⧸ Module.annihilator R Q] N := {
      toFun := f.hom
      map_add' := f.hom.map_add
      map_smul' := by
        intro s x
        refine Quotient.inductionOn' s ?_
        intro r
        simp only [RingHom.id_apply]
        change f.hom (Ideal.Quotient.mk (Module.annihilator R Q) r • x) =
          Ideal.Quotient.mk (Module.annihilator R Q) r • f.hom x
        rw [hM.mk_smul, hN.mk_smul]
        exact f.hom.map_smul r x }
    exact ModuleCat.ofHom g
  map_id M := by
    apply ModuleCat.hom_ext
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    rfl

private noncomputable def quotientUnitIsoApp (R : Type v) [CommRing R]
    (Q : ModuleCat.{u} R) (hQ : IsSeparator Q) (M : ModuleCat.{u} R) :
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Module.annihilator R Q))).obj
      ((quotientModuleFunctor R Q hQ).obj M)) ≅ M := by
  let hM := separator_annihilator_torsion R Q M hQ
  letI : Module (R ⧸ Module.annihilator R Q) M := hM.module
  let e : (((ModuleCat.restrictScalars (Ideal.Quotient.mk (Module.annihilator R Q))).obj
      ((quotientModuleFunctor R Q hQ).obj M) : Type u) ≃ₗ[R] (M : Type u)) := {
    toFun := fun x => x
    map_add' := by intros; rfl
    map_smul' := by
      intro r x
      change (Ideal.Quotient.mk (Module.annihilator R Q) r) • x = r • x
      exact hM.mk_smul r x
    invFun := fun x => x
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }
  exact e.toModuleIso

private noncomputable def quotientCounitIsoApp (R : Type v) [CommRing R]
    (Q : ModuleCat.{u} R) (hQ : IsSeparator Q)
    (N : ModuleCat.{u} (R ⧸ Module.annihilator R Q)) :
    (quotientModuleFunctor R Q hQ).obj
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Module.annihilator R Q))).obj N) ≅ N := by
  let M := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Module.annihilator R Q))).obj N
  let hM := separator_annihilator_torsion R Q M hQ
  letI : Module (R ⧸ Module.annihilator R Q) M := hM.module
  let e : ((M : Type u) ≃ₗ[R ⧸ Module.annihilator R Q] (N : Type u)) := {
    toFun := fun x => x
    map_add' := by intros; rfl
    map_smul' := by
      intro s x
      refine Quotient.inductionOn' s ?_
      intro r
      rfl
    invFun := fun x => x
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }
  exact e.toModuleIso

private noncomputable def quotientModuleEquivalence (R : Type v) [CommRing R]
    (Q : ModuleCat.{u} R) (hQ : IsSeparator Q) : ModuleCat.{u} R ≌
      ModuleCat.{u} (R ⧸ Module.annihilator R Q) where
  functor := quotientModuleFunctor R Q hQ
  inverse := ModuleCat.restrictScalars (Ideal.Quotient.mk (Module.annihilator R Q))
  unitIso := NatIso.ofComponents
    (fun M => (quotientUnitIsoApp R Q hQ M).symm) (by
      intro M N f
      apply ModuleCat.hom_ext
      rfl)
  counitIso := NatIso.ofComponents
    (fun N => quotientCounitIsoApp R Q hQ N) (by
      intro M N f
      apply ModuleCat.hom_ext
      rfl)
  functor_unitIso_comp := by
    intro M
    apply ModuleCat.hom_ext
    rfl

private noncomputable def quotientEquivalenceToQuasicoherent (X : Scheme.{u})
    (R : Type v) [CommRing R]
    (e : ModuleCat.{u} R ≌
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    ModuleCat.{u} (R ⧸ Module.annihilator R
      (e.inverse.obj (CategoryTheory.separator
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory))) ≌
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory := by
  let C := (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory
  let _ : IsGrothendieckAbelian C :=
    AlgebraicGeometry.quasicoherentModules_isGrothendieckAbelian X
  let Q := e.inverse.obj (CategoryTheory.separator C)
  have hQ : IsSeparator Q := equivalence_source_separator X R e
  exact (quotientModuleEquivalence R Q hQ).symm.trans e

private theorem equivalence_freeImage_isFinitePresentation (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (R : Type u)
    [CommRing R]
    (e : ModuleCat.{u} R ≌
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (e.functor.obj (ModuleCat.of R R)).obj.IsFinitePresentation := by
  let : Fact (Cardinal.aleph0.IsRegular) := Cardinal.fact_isRegular_aleph0
  let : IsFinitelyPresentable.{u} (ModuleCat.of R R) :=
    regularModule_isFinitelyPresentable R
  exact (AlgebraicGeometry.isFinitelyPresentable_iff_isFinitePresentation X _).mp
    (isCardinalPresentable_of_equivalence (ModuleCat.of R R) Cardinal.aleph0 e)

private theorem equivalence_freeImage_projective (X : Scheme.{u}) (R : Type u)
    [CommRing R]
    (e : ModuleCat.{u} R ≌
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    Projective (e.functor.obj (ModuleCat.of R R)) :=
  (e.map_projective_iff (ModuleCat.of R R)).2
    (ModuleCat.projective_of_free (Module.Basis.singleton Unit R))

private theorem equivalence_freeImage_separator (X : Scheme.{u}) (R : Type u)
    [CommRing R]
    (e : ModuleCat.{u} R ≌
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    IsSeparator (e.functor.obj (ModuleCat.of R R)) :=
  (regularModule_isSeparator R).of_equivalence e

private theorem equivalence_freeImage_end_commute (X : Scheme.{u}) (R : Type u)
    [CommRing R]
    (e : ModuleCat.{u} R ≌
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (f g : e.functor.obj (ModuleCat.of R R) ⟶ e.functor.obj (ModuleCat.of R R)) :
    f ≫ g = g ≫ f := by
  calc
    f ≫ g = e.functor.map (e.functor.preimage f ≫ e.functor.preimage g) := by simp
    _ = e.functor.map (e.functor.preimage g ≫ e.functor.preimage f) := by
      rw [regularModule_end_commute R (e.functor.preimage f) (e.functor.preimage g)]
    _ = g ≫ f := by simp

private theorem exists_finitelyPresented_projective_separator_of_equivalence
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (R : Type v) [CommRing R]
    (e : ModuleCat.{u} R ≌
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    ∃ P : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory,
      P.obj.IsFinitePresentation ∧ Projective P ∧ IsSeparator P ∧
        ∀ f g : P ⟶ P, f ≫ g = g ≫ f := by
  let C := (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory
  let _ : IsGrothendieckAbelian C :=
    AlgebraicGeometry.quasicoherentModules_isGrothendieckAbelian X
  let Q := e.inverse.obj (CategoryTheory.separator C)
  let S := R ⧸ Module.annihilator R Q
  let _ : Small.{u} S := quotient_annihilator_small R Q
  let e' : ModuleCat.{u} S ≌ C := quotientEquivalenceToQuasicoherent X R e
  let T := Shrink.{u} S
  let e'' : ModuleCat.{u} T ≌ C :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (Shrink.ringEquiv S)).symm.trans e'
  let P := e''.functor.obj (ModuleCat.of T T)
  have hPFinitePresentation : P.obj.IsFinitePresentation :=
    equivalence_freeImage_isFinitePresentation X T e''
  have hPProjective : Projective P := equivalence_freeImage_projective X T e''
  have hPSeparator : IsSeparator P := equivalence_freeImage_separator X T e''
  have hPEndCommute : ∀ f g : P ⟶ P, f ≫ g = g ≫ f :=
    equivalence_freeImage_end_commute X T e''
  exact ⟨P, hPFinitePresentation, hPProjective, hPSeparator, hPEndCommute⟩

section

open Scheme.Modules

private lemma isQuasicoherent_of_affine_restrict (X : Scheme.{u}) (M : X.Modules)
    (h : ∀ U : X.Opens, IsAffineOpen U → (M.restrict U.ι).IsQuasicoherent) :
    M.IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_restrict_affineOpens M
    fun V ↦ h V V.2

private alias preservesFiniteLimits_restrictFunctor :=
    Stacks.AffineTilde.preservesFiniteLimits_restrictFunctor

private theorem isQuasicoherent_middle_of_shortExact {X : Scheme.{u}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] : S.X₂.IsQuasicoherent := by
  apply isQuasicoherent_of_affine_restrict X S.X₂
  intro U hU
  have : IsAffine U.toScheme := hU
  have := preservesFiniteLimits_restrictFunctor U.ι
  have : (S.map (Scheme.Modules.restrictFunctor U.ι)).X₁.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor U.ι S.X₁
  have : (S.map (Scheme.Modules.restrictFunctor U.ι)).X₃.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor U.ι S.X₃
  exact Stacks.AlgebraicGeometry.QuasicoherentExtension.isQuasicoherent_middle_of_shortExact
    (S.map (Scheme.Modules.restrictFunctor U.ι))
    (hS.map_of_exact (Scheme.Modules.restrictFunctor U.ι))

private theorem isQuasicoherent_cokernel {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (cokernel f).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel f

private theorem epi_underlying_of_quasicoherent_epi {X : Scheme.{u}}
    {M N : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory}
    (f : M ⟶ N) [Epi f] : Epi f.hom := by
  have : M.obj.IsQuasicoherent := M.property
  have : N.obj.IsQuasicoherent := N.property
  let C : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
    ⟨cokernel f.hom, isQuasicoherent_cokernel f.hom⟩
  let p : N ⟶ C := ObjectProperty.homMk (cokernel.π f.hom)
  have hp : p = 0 := by
    apply (cancel_epi f).mp
    apply ObjectProperty.hom_ext
    exact (cokernel.condition f.hom).trans (by simp)
  exact CategoryTheory.Abelian.epi_of_cokernel_π_eq_zero _ (congrArg (fun g : N ⟶ C => g.hom) hp)

end

private theorem projective_of_fullyFaithful_on_fullSubcategory
    {C : Type*} [Category* C] (Q : ObjectProperty C) (F : C ⥤ C)
    [F.Full] [F.Faithful] [F.PreservesEpimorphisms]
    (hF : ∀ M : Q.FullSubcategory, Q (F.obj M.obj))
    (hEpi : ∀ {M N : Q.FullSubcategory} (f : M ⟶ N), Epi f → Epi f.hom)
    (P U : Q.FullSubcategory) [Projective P] (e : F.obj U.obj ≅ P.obj) :
    Projective U := by
  constructor
  intro A B f g hg
  let A' : Q.FullSubcategory := ⟨F.obj A.obj, hF A⟩
  let B' : Q.FullSubcategory := ⟨F.obj B.obj, hF B⟩
  let g' : A' ⟶ B' := ObjectProperty.homMk (F.map g.hom)
  have : Epi g.hom := hEpi g hg
  have : Epi g' := Q.ι.epi_of_epi_map (inferInstance : Epi (F.map g.hom))
  let f' : P ⟶ B' := ObjectProperty.homMk (e.inv ≫ F.map f.hom)
  let t : P ⟶ A' := Projective.factorThru f' g'
  refine ⟨ObjectProperty.homMk (F.preimage (e.hom ≫ t.hom)), ?_⟩
  apply ObjectProperty.hom_ext
  apply F.map_injective
  simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp,
    ObjectProperty.homMk_hom, Functor.map_preimage]
  have ht : t.hom ≫ F.map g.hom = e.inv ≫ F.map f.hom :=
    congrArg (fun f : P ⟶ B' => f.hom) (Projective.factorThru_comp f' g')
  rw [Category.assoc, ht, Iso.hom_inv_id_assoc]

private theorem projective_unit_of_projective_rank_one (X : Scheme.{u})
    (P : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    [projectiveP : Projective P]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens X)
      (J := Opens.grothendieckTopology X) P.obj 1] :
    Projective (⟨SheafOfModules.unit X.ringCatSheaf, inferInstance⟩ :
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) := by
  let F := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj P.obj
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property P.obj :=
    Stacks.InvertibleRankOneIff.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace P.obj
  have : F.IsEquivalence := Stacks.SheafOfModules.tensorLeftFunctor_isEquivalence
    X.sheaf.obj X.ringCatSheaf.property P.obj
  have hF (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
      (F.obj M.obj).IsQuasicoherent := by
    have hPq : P.obj.IsQuasicoherent := P.property
    have hMq : M.obj.IsQuasicoherent := M.property
    exact @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace P.obj M.obj hPq hMq
  let e : F.obj (SheafOfModules.unit X.ringCatSheaf) ≅ P.obj :=
    Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso
      X.sheaf.obj X.ringCatSheaf.property P.obj
  exact @projective_of_fullyFaithful_on_fullSubcategory
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) _
    (SheafOfModules.isQuasicoherent X.ringCatSheaf) F _ _ _ hF
    (fun f hf => @epi_underlying_of_quasicoherent_epi X _ _ f hf) P _ projectiveP e

private theorem ext_one_eq_zero_of_projective_fullSubcategory
    {C : Type*} [Category* C] [Abelian C] [HasExt C]
    (Q : ObjectProperty C)
    (hQ : ∀ (S : ShortComplex C), S.ShortExact → Q S.X₁ → Q S.X₃ → Q S.X₂)
    (P : Q.FullSubcategory) [Projective P] (N : C) (hN : Q N)
    (ξ : CategoryTheory.Abelian.Ext P.obj N 1) : ξ = 0 := by
  obtain ⟨E, i, p, w, hS, rfl⟩ :=
    (CategoryTheory.Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
      C P.obj N).1 ξ
  let E' : Q.FullSubcategory := ⟨E, hQ (ShortComplex.mk i p w) hS hN P.property⟩
  let p' : E' ⟶ P := ObjectProperty.homMk p
  have : Epi p' := Q.ι.epi_of_epi_map hS.epi_g
  let s := Projective.factorThru (𝟙 P) p'
  have hs : s.hom ≫ p = 𝟙 P.obj :=
    congrArg (fun f : P ⟶ P => f.hom) (Projective.factorThru_comp (𝟙 P) p')
  have h := congrArg (fun z : CategoryTheory.Abelian.Ext E N 1 =>
    (CategoryTheory.Abelian.Ext.mk₀ s.hom).comp z (zero_add 1)) hS.comp_extClass
  simpa only [← CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero,
    CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, hs,
    CategoryTheory.Abelian.Ext.mk₀_id_comp, CategoryTheory.Abelian.Ext.comp_zero] using h

section

attribute [local instance] CategoryTheory.HasExt.standard

private theorem isZero_H1_of_projective_unit (X : Scheme.{u})
    (hP : Projective (⟨SheafOfModules.unit X.ringCatSheaf, inferInstance⟩ :
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory))
    (N : X.Modules) [N.IsQuasicoherent] :
    IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj N) := by
  let Q := SheafOfModules.isQuasicoherent X.ringCatSheaf
  let P : Q.FullSubcategory := ⟨SheafOfModules.unit X.ringCatSheaf, inferInstance⟩
  have : Projective P := hP
  have hQ (S : ShortComplex X.Modules) (hS : S.ShortExact)
      (h₁ : Q S.X₁) (h₃ : Q S.X₃) : Q S.X₂ := by
    have : S.X₁.IsQuasicoherent := h₁
    have : S.X₃.IsQuasicoherent := h₃
    exact isQuasicoherent_middle_of_shortExact S hS
  have hsub : Subsingleton (CategoryTheory.Abelian.Ext.{u + 1}
      (SheafOfModules.unit X.ringCatSheaf) N 1) :=
    subsingleton_of_forall_eq 0 fun ξ =>
      ext_one_eq_zero_of_projective_fullSubcategory Q hQ P N inferInstance ξ
  have hH := @AddCommGrpCat.isZero_of_subsingleton _
    (@Equiv.subsingleton _ _ (Stacks.Cohomology.SpaceModules.extOneEquivFirstCohomology
      X.ringCatSheaf N).toEquiv.symm hsub)
  have hforget := hH.of_iso
    ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
      X.ringCatSheaf ⊤ 1).app N)
  have : Subsingleton ↑(((SheafOfModules.evaluation X.ringCatSheaf
      (Opposite.op ⊤)).rightDerived 1).obj N) :=
    AddCommGrpCat.subsingleton_of_isZero hforget
  exact ModuleCat.isZero_of_subsingleton _

private theorem isAffine_of_projective_unit (X : Scheme.{u}) [CompactSpace X]
    (hP : Projective (⟨SheafOfModules.unit X.ringCatSheaf, inferInstance⟩ :
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)) : IsAffine X := by
  apply Stacks.SerreCriterion.isAffine_of_forall_isZero_H1_ideal X
  intro I hI
  have : (Subobject.underlying.obj I).IsQuasicoherent := hI
  exact isZero_H1_of_projective_unit X hP _

end

noncomputable section

open Opposite

private theorem fieldModuleSheaf_isLocalizing {k : Type u} [Field k]
    (M : (Spec (.of k)).Modules) :
    AlgebraicGeometry.IsLocalizing
      (AlgebraicGeometry.modulesSpecToSheaf.obj M) := by
  intro f
  by_cases hf : f = 0
  · subst f
    have hbot : PrimeSpectrum.basicOpen (0 : k) = ⊥ :=
      (PrimeSpectrum.basicOpen_eq_bot_iff (0 : k)).2 ⟨1, by simp⟩
    rw [hbot]
    let N :=
      (AlgebraicGeometry.modulesSpecToSheaf.obj M).obj.obj
        (Opposite.op (⊥ : (Spec (.of k)).Opens))
    have hz : CategoryTheory.Limits.IsZero N :=
      (TopCat.Sheaf.isTerminalOfEmpty
        (AlgebraicGeometry.modulesSpecToSheaf.obj M)).isZero
    have hz' : Subsingleton N := ModuleCat.subsingleton_of_isZero hz
    refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
    · exact fun _ => (Module.End.isUnit_iff _).2
        ⟨fun _ _ _ => hz'.elim _ _, fun _ => ⟨0, hz'.elim _ _⟩⟩
    · intro y
      refine ⟨(0, ⟨0, ?_⟩), ?_⟩
      · exact ⟨1, by simp⟩
      · change (0 : k) • y = _
        exact hz'.elim _ _
    · intro x y _
      refine ⟨⟨0, ?_⟩, ?_⟩
      · exact ⟨1, by simp⟩
      · change (0 : k) • x = (0 : k) • y
        simp
  · have hu : IsUnit f := isUnit_iff_ne_zero.mpr hf
    have htop : PrimeSpectrum.basicOpen f = ⊤ := by
      ext x
      exact ⟨fun _ => trivial,
        fun _ h => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem x.asIdeal h hu)⟩
    rw [htop]
    let : IsLocalization (Submonoid.powers f) k :=
      IsLocalization.of_le_isUnit (S := Submonoid.powers f) (by
        intro x hx
        rcases (Submonoid.mem_powers_iff x f).mp hx with ⟨n, rfl⟩
        exact (IsUnit.mem_submonoid_iff _).2 (IsUnit.pow n hu))
    let N := (AlgebraicGeometry.modulesSpecToSheaf.obj M).obj.obj (Opposite.op ⊤)
    have hid : IsLocalizedModule (Submonoid.powers f) (LinearMap.id : N →ₗ[k] N) :=
      isLocalizedModule_id (S := Submonoid.powers f) (M := N) k
    let idOpen : (⊤ : (Spec (.of k)).Opens).leTop = 𝟙 ⊤ := Subsingleton.elim _ _
    have hOp :
        (⊤ : (Spec (.of k)).Opens).leTop.op = (𝟙 ⊤).op :=
      congrArg Opposite.op idOpen
    have : IsIso ((AlgebraicGeometry.modulesSpecToSheaf.obj M).obj.map
        (TopologicalSpace.Opens.leTop (⊤ : (Spec (.of k)).Opens)).op) := by
      rw [hOp]
      infer_instance
    let e : N ≃ₗ[k] N :=
      (asIso ((AlgebraicGeometry.modulesSpecToSheaf.obj M).obj.map
        (TopologicalSpace.Opens.leTop (⊤ : (Spec (.of k)).Opens)).op)).toLinearEquiv
    change IsLocalizedModule (Submonoid.powers f) (e.toLinearMap.comp LinearMap.id)
    exact IsLocalizedModule.of_linearEquiv (S := Submonoid.powers f) (f := LinearMap.id) e

private theorem fieldModuleSheaf_isQuasicoherent {k : Type u} [Field k]
    (M : (Spec (.of k)).Modules) : M.IsQuasicoherent := by
  rw [AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ,
    AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing]
  exact fieldModuleSheaf_isLocalizing M

private lemma mem_preimage_residue (X : Scheme.{u}) (x : X) (U : X.Opens)
    (y : Spec (X.residueField x)) : y ∈ (X.fromSpecResidueField x) ⁻¹ᵁ U ↔ x ∈ U := by
  change (X.fromSpecResidueField x) y ∈ U ↔ x ∈ U
  rw [Scheme.fromSpecResidueField_apply]

private lemma residue_germ_stalkClosedPointIso (X : Scheme.{u}) (x : X)
    (U : X.Opens) (hx : x ∈ U) (r : X.presheaf.obj (op U)) :
    (stalkClosedPointIso (X.residueField x)).hom
      ((Spec (X.residueField x)).presheaf.germ ((X.fromSpecResidueField x) ⁻¹ᵁ U)
        (IsLocalRing.closedPoint (X.residueField x))
        ((mem_preimage_residue X x U _).mpr hx) ((X.fromSpecResidueField x).app U r)) =
      (X.residue x) (X.presheaf.germ U x hx r) := by
  let f := X.fromSpecResidueField x
  have : IsLocalHom (X.residue x).hom :=
    IsLocalHom.of_surjective _ (X.residue_surjective x)
  have hy : f (IsLocalRing.closedPoint (X.residueField x)) ∈ U :=
    (mem_preimage_residue X x U _).mpr hx
  have h := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (X.residue x) U hy
  change X.presheaf.germ U (f (IsLocalRing.closedPoint (X.residueField x))) hy ≫
    (f.stalkMap _ ≫ (stalkClosedPointIso (X.residueField x)).hom) = _ at h
  have h' := congrArg (fun a => a ≫ (stalkClosedPointIso (X.residueField x)).hom)
    (f.germ_stalkMap U (IsLocalRing.closedPoint (X.residueField x)) hy)
  exact ConcreteCategory.congr_hom (h'.symm.trans ((Category.assoc _ _ _).trans h)) r

private def residueSkyscraper (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.residueField x)) : X.Modules :=
  Stacks.Modules.skyscraper X.sheaf x ((ModuleCat.restrictScalars (X.residue x).hom).obj N)

private def pointModule (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.residueField x)) : (Spec (X.residueField x)).Modules :=
  Stacks.Modules.skyscraper (Spec (X.residueField x)).sheaf
    (IsLocalRing.closedPoint (X.residueField x))
    ((ModuleCat.restrictScalars (stalkClosedPointIso (X.residueField x)).hom.hom).obj N)

private def pushforwardPointModuleIso (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.residueField x)) :
    (Scheme.Modules.pushforward (X.fromSpecResidueField x)).obj (pointModule X x N) ≅
      residueSkyscraper X x N where
  hom := ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun s h => s ⟨(mem_preimage_residue X x U.unop _).mpr h.down⟩
          map_zero' := rfl
          map_add' := by intros; rfl }
      naturality := by intros; rfl }
    (by
      intro U r s
      funext h
      change (stalkClosedPointIso (X.residueField x)).hom
        ((Spec (X.residueField x)).presheaf.germ _ _ _
          ((X.fromSpecResidueField x).app U.unop r)) • s _ =
        (X.residue x) (X.presheaf.germ U.unop x h.down r) • s _
      rw [residue_germ_stalkClosedPointIso X x U.unop h.down r])⟩
  inv := ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun s h => s ⟨(mem_preimage_residue X x U.unop _).mp h.down⟩
          map_zero' := rfl
          map_add' := by intros; rfl }
      naturality := by intros; rfl }
    (by
      intro U r s
      funext h
      change (X.residue x) (X.presheaf.germ U.unop x _ r) • s _ =
        (stalkClosedPointIso (X.residueField x)).hom
          ((Spec (X.residueField x)).presheaf.germ _ _ _
            ((X.fromSpecResidueField x).app U.unop r)) • s _
      rw [residue_germ_stalkClosedPointIso X x U.unop
        ((mem_preimage_residue X x U.unop _).mp h.down) r])⟩
  hom_inv_id := by ext U s; rfl
  inv_hom_id := by ext U s; rfl

private theorem residueSkyscraper_isQuasicoherent (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) (N : ModuleCat.{u} (X.residueField x)) :
    (residueSkyscraper X x N).IsQuasicoherent := by
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have : (pointModule X x N).IsQuasicoherent := fieldModuleSheaf_isQuasicoherent _
  have h := AlgebraicGeometry.pushforward_isQuasicoherent
    (X.fromSpecResidueField x)
    (pointModule X x N)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (pushforwardPointModuleIso X x N) h

/-- The stalk at `x` of an `𝒪_X`-module is a module over the local ring `𝒪_{X,x}`. -/
local instance (X : Scheme.{u}) (M : X.Modules) (x : X) :
    Module ↑(X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk M.val.presheaf x) :=
  Stacks.Modules.stalkModule X.sheaf x M

/-- The residue field `κ(x)` is an algebra over the local ring `𝒪_{X,x}` through the residue
map. -/
local instance (X : Scheme.{u}) (x : X) :
    Algebra ↑(X.presheaf.stalk x) ↑(X.residueField x) := (X.residue x).hom.toAlgebra

private theorem epi_skyscraperHomEquiv_symm (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) (M : X.Modules)
    (N : ModuleCat.{u} (X.presheaf.stalk x))
    (f : ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(X.presheaf.stalk x)] N)
    (hf : Function.Surjective f) :
    Epi ((Stacks.Modules.skyscraperHomEquiv X.sheaf x N M).symm f) := by
  apply (SheafOfModules.toSheaf.{u} X.ringCatSheaf).epi_of_epi_map
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t y hy
  by_cases hxy : y = x
  · subst y
    obtain ⟨m, hm⟩ := hf (t ⟨hy⟩)
    obtain ⟨V, hxV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
    refine ⟨U ⊓ V, inf_le_left, ⟨M.val.map (homOfLE inf_le_right).op s, ?_⟩, hy, hxV⟩
    funext h
    change f (TopCat.Presheaf.germ M.val.presheaf (U ⊓ V) x h.down
      (M.val.map (homOfLE inf_le_right).op s)) = t _
    exact (congrArg f (TopCat.Presheaf.germ_res_apply M.val.presheaf
      (homOfLE (inf_le_right : U ⊓ V ≤ V)) x h.down s)).trans hm
  · let W : X.Opens := ⟨{x}ᶜ, hx.isOpen_compl⟩
    refine ⟨U ⊓ W, inf_le_left, ⟨0, ?_⟩, hy, ?_⟩
    · funext h
      exact False.elim (h.down.2 (Set.mem_singleton x))
    · exact hxy

private def residueFiber (X : Scheme.{u}) (x : X) :
    X.Modules ⥤ ModuleCat.{u} (X.residueField x) :=
  Stacks.Modules.stalkSheafFunctor X.sheaf x ⋙ ModuleCat.extendScalars (X.residue x).hom

private def residueAdjunction (X : Scheme.{u}) (x : X) :
    residueFiber X x ⊣
      ModuleCat.restrictScalars (X.residue x).hom ⋙ Stacks.Modules.skyscraperFunctor X.sheaf x :=
  (Stacks.Modules.stalkSkyscraperAdjunction X.sheaf x).comp
    (ModuleCat.extendRestrictScalarsAdj (X.residue x).hom)

private def quasicoherentResidueSkyscraper (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) : ModuleCat.{u} (X.residueField x) ⥤
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory where
  obj N := ⟨residueSkyscraper X x N, residueSkyscraper_isQuasicoherent X x hx N⟩
  map f := ObjectProperty.homMk
    ((Stacks.Modules.skyscraperFunctor X.sheaf x).map
      ((ModuleCat.restrictScalars (X.residue x).hom).map f))
  map_id _ := by apply ObjectProperty.hom_ext; rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    exact (ModuleCat.restrictScalars (X.residue x).hom ⋙
      Stacks.Modules.skyscraperFunctor X.sheaf x).map_comp _ _

private def quasicoherentResidueAdjunction (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ residueFiber X x ⊣
      quasicoherentResidueSkyscraper X x hx :=
  (residueAdjunction X x).restrictFullyFaithful
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).fullyFaithfulι
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

private theorem quasicoherentResidueSkyscraper_faithful (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) : (quasicoherentResidueSkyscraper X x hx).Faithful where
  map_injective {M N} f g h := by
    apply ModuleCat.hom_ext
    ext m
    exact congrArg (fun f : (quasicoherentResidueSkyscraper X x hx).obj M ⟶
      (quasicoherentResidueSkyscraper X x hx).obj N =>
        f.hom.val.app (op ⊤) (fun _ => m) ⟨trivial⟩) h

private theorem residueAdjunction_unit_epi (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) (M : X.Modules) :
    Epi ((residueAdjunction X x).unit.app M) := by
  let A := Stacks.Modules.stalkSheafFunctor X.sheaf x
  let a := ModuleCat.extendRestrictScalarsAdj (X.residue x).hom
  have h : (residueAdjunction X x).unit.app M =
      (Stacks.Modules.skyscraperHomEquiv X.sheaf x
        ((ModuleCat.restrictScalars (X.residue x).hom).obj
          ((ModuleCat.extendScalars (X.residue x).hom).obj (A.obj M))) M).symm
        (a.unit.app (A.obj M)).hom := by
    ext U s
    funext h
    rfl
  rw [h]
  exact epi_skyscraperHomEquiv_symm X x hx _ _ _ <| TensorProduct.mk_surjective
    (X.presheaf.stalk x) (A.obj M) (X.residueField x) (X.residue_surjective x)

private theorem quasicoherentResidueAdjunction_unit_epi (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X))
    (P : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    Epi ((quasicoherentResidueAdjunction X x hx).unit.app P) := by
  apply (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.epi_of_epi_map
  have h : ((quasicoherentResidueAdjunction X x hx).unit.app P).hom =
      (residueAdjunction X x).unit.app P.obj := by
    have h := (residueAdjunction X x).map_restrictFullyFaithful_unit_app
      (L := (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ residueFiber X x)
      (R := quasicoherentResidueSkyscraper X x hx)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).fullyFaithfulι
      (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _) P
    refine h.trans ?_
    ext U s
    funext h
    rfl
  change Epi ((quasicoherentResidueAdjunction X x hx).unit.app P).hom
  rw [h]
  exact residueAdjunction_unit_epi X x hx P.obj

private theorem residueField_dual_lifts_of_projective (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X))
    (P : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) [Projective P] :
    ∀ f : ↑(TopCat.Presheaf.stalk P.obj.val.presheaf x) →ₗ[↑(X.presheaf.stalk x)]
      IsLocalRing.ResidueField (X.presheaf.stalk x),
      ∃ g : ↑(TopCat.Presheaf.stalk P.obj.val.presheaf x) →ₗ[↑(X.presheaf.stalk x)]
        ↑(X.presheaf.stalk x), ∀ m, IsLocalRing.residue (X.presheaf.stalk x) (g m) = f m := by
  let O : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
    ⟨SheafOfModules.unit X.ringCatSheaf, inferInstance⟩
  let N : ModuleCat.{u} (X.residueField x) := ModuleCat.of _ (X.residueField x)
  let N' := (ModuleCat.restrictScalars (X.residue x).hom).obj N
  let K : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
    ⟨residueSkyscraper X x N, residueSkyscraper_isQuasicoherent X x hx N⟩
  let e : ↑(TopCat.Presheaf.stalk O.obj.val.presheaf x) ≃ₗ[↑(X.presheaf.stalk x)]
      ↑(X.presheaf.stalk x) := Stacks.Ample.unitStalkEquiv X x
  let qLin : ↑(TopCat.Presheaf.stalk O.obj.val.presheaf x) →ₗ[↑(X.presheaf.stalk x)]
      IsLocalRing.ResidueField (X.presheaf.stalk x) :=
    (Algebra.linearMap _ _).comp e.toLinearMap
  let q : O ⟶ K := ObjectProperty.homMk
    ((Stacks.Modules.skyscraperHomEquiv X.sheaf x N' O.obj).symm qLin)
  have : Epi q.hom := epi_skyscraperHomEquiv_symm X x hx O.obj N' qLin
    ((IsLocalRing.residue_surjective).comp e.surjective)
  have : Epi q := (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.epi_of_epi_map
    (inferInstance : Epi q.hom)
  intro f
  let f' : P ⟶ K := ObjectProperty.homMk
    ((Stacks.Modules.skyscraperHomEquiv X.sheaf x N' P.obj).symm f)
  let s := Projective.factorThru f' q
  refine ⟨e.toLinearMap.comp
    (Stacks.Modules.stalkLinearMap s.hom.val), ?_⟩
  intro m
  obtain ⟨U, hU, z, rfl⟩ := TopCat.Presheaf.exists_germ_eq P.obj.val.presheaf m
  have h := congrArg (fun g : P ⟶ K => g.hom.val.app (op U) z ⟨hU⟩)
    (Projective.factorThru_comp f' q)
  change qLin (TopCat.Presheaf.germ O.obj.val.presheaf U x hU
    (s.hom.val.app (op U) z)) = f (TopCat.Presheaf.germ P.obj.val.presheaf U x hU z) at h
  change qLin (Stacks.Modules.stalkLinearMap s.hom.val
    (TopCat.Presheaf.germ P.obj.val.presheaf U x hU z)) = _
  rw [Stacks.Modules.stalkLinearMap_germ]
  exact h

private theorem residueFiber_finrank_eq_one (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X))
    (P : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    [P.obj.IsFinitePresentation] [Projective P] (hP : IsSeparator P)
    (hcomm : ∀ f g : P ⟶ P, f ≫ g = g ≫ f) :
    Module.finrank (X.residueField x) ((residueFiber X x).obj P.obj) = 1 := by
  have : Module.Finite ↑(X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk P.obj.val.presheaf x) :=
    SheafOfModules.finite_stalk X.sheaf P.obj x
  have : Module.Finite (X.residueField x)
      (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ residueFiber X x).obj P) :=
    inferInstanceAs (Module.Finite (X.residueField x)
      ((X.residueField x) ⊗[↑(X.presheaf.stalk x)]
        ↑(TopCat.Presheaf.stalk P.obj.val.presheaf x)))
  have := quasicoherentResidueSkyscraper_faithful X x hx
  have := quasicoherentResidueAdjunction_unit_epi X x hx P
  exact finrank_eq_one_of_projective_separator_of_epi_unit (X.residueField x)
    (quasicoherentResidueAdjunction X x hx) P hP hcomm

/-- A linear identification of the stalk of a module on a scheme with a free module over the local
ring `𝒪_{X,x}` is one over the `RingCat`-valued stalk of the ring sheaf, the two stalk rings being
identified by `SemilinearStalk.commStalkRingEquiv`. -/
def stalkLinearEquivOverRingCatStalk {X : Scheme.{u}} (M : X.Modules) (x : X)
    {ι : Type u}
    (e : ↑(TopCat.Presheaf.stalk M.val.presheaf x) ≃ₗ[↑(X.presheaf.stalk x)]
      (ι →₀ ↑(X.presheaf.stalk x))) :
    ↑(TopCat.Presheaf.stalk M.val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk X.ringCatSheaf.obj x)]
      (ι →₀ ↑(TopCat.Presheaf.stalk X.ringCatSheaf.obj x)) := by
  let a : ↑(TopCat.Presheaf.stalk X.ringCatSheaf.obj x) ≃+* ↑(X.presheaf.stalk x) :=
    SemilinearStalk.commStalkRingEquiv X.presheaf x
  let b := e.toAddEquiv.trans (Finsupp.mapRange.addEquiv a.symm.toAddEquiv)
  refine { __ := b, map_smul' := ?_ }
  intro r m
  ext i
  have hsm : r • m = a r • m :=
    (SemilinearStalk.comm_smul_eq X.presheaf x M.val r m).symm
  change a.symm (e (r • m) i) = r * a.symm (e m i)
  rw [hsm, e.map_smul]
  change a.symm (a r * e m i) = r * a.symm (e m i)
  rw [map_mul, RingEquiv.symm_apply_apply]

private def stalkLinearEquivRingCat {X : Scheme.{u}} (M : X.Modules) (x : X)
    {ι : Type u}
    (e : ↑(TopCat.Presheaf.stalk M.val.presheaf x) ≃ₗ[↑(X.presheaf.stalk x)]
      (ι →₀ ↑(X.presheaf.stalk x))) :
    ↑(TopCat.Presheaf.stalk M.val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk X.ringCatSheaf.obj x)]
      (ι →₀ ↑(TopCat.Presheaf.stalk X.ringCatSheaf.obj x)) :=
  stalkLinearEquivOverRingCatStalk M x e

private theorem isFiniteLocallyFreeOfRank_one_of_projective_separator
    (X : Scheme.{u}) [CompactSpace X]
    (P : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    [P.obj.IsFinitePresentation] [Projective P] (hP : IsSeparator P)
    (hcomm : ∀ f g : P ⟶ P, f ≫ g = g ≫ f) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens X)
      (J := Opens.grothendieckTopology X) P.obj 1 := by
  apply isFiniteLocallyFreeOfRank_of_closed_stalks P.obj inferInstance 1
  intro x hx
  have : Module.Finite ↑(X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk P.obj.val.presheaf x) :=
    SheafOfModules.finite_stalk X.sheaf P.obj x
  have he := nonempty_equiv_finsupp_of_residueField_dual_lifts
    ↑(X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk P.obj.val.presheaf x) 1
    (residueField_dual_lifts_of_projective X x hx P)
    (residueFiber_finrank_eq_one X x hx P hP hcomm)
  exact he.map (stalkLinearEquivRingCat P.obj x)

end

/-- **Stacks Project, Tag 0GPI.** A quasi-compact and quasi-separated scheme whose category
of quasi-coherent modules is equivalent to the category of modules over a commutative ring
is affine.

The commutativity of `R` is a reading of the tag's `a ring`. It is used through the separator
`P`, whose endomorphism ring must be commutative for the rank of `P` to be forced to be `1`. -/
@[stacks 0GPI "`[CommRing R]` reads the tag's `a ring`: the rank-one step needs `End P` \
  commutative. For noncommutative `R` the conclusion still holds by Morita equivalence \
  (`Mod (M₂ k) ≌ Mod k`), but that rank-one step fails outright."]
public theorem isAffine_of_quasicoherentModules_equivalent_moduleCat
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (R : Type v) [CommRing R]
    (e : ModuleCat.{u} R ≌
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    IsAffine X := by
  obtain ⟨P, hPFinitePresentation, hPProjective, hPSeparator, hPEndCommute⟩ :=
    exists_finitelyPresented_projective_separator_of_equivalence X R e
  have : P.obj.IsFinitePresentation := hPFinitePresentation
  have : Projective P := hPProjective
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens X)
      (J := Opens.grothendieckTopology X) P.obj 1 :=
    isFiniteLocallyFreeOfRank_one_of_projective_separator X P hPSeparator hPEndCommute
  exact isAffine_of_projective_unit X (projective_unit_of_projective_rank_one X P)

/-- **Stacks Project, Tag 0GPI**, with the equivalence written in the orientation of the source:
a quasi-compact and quasi-separated scheme whose category of quasi-coherent modules is equivalent
to the category of modules over a commutative ring is affine.

As for the mirror form, the commutativity of `R` is a reading of the tag's `a ring`. -/
@[stacks 0GPI "the hypothesis in the orientation of the source, `QCoh(𝒪_X) ≌ Mod R`; \
  `[CommRing R]` reads the tag's `a ring`, exactly as for the mirror form \
  `isAffine_of_quasicoherentModules_equivalent_moduleCat`"]
public theorem isAffine_of_quasicoherentModules_equivalence_moduleCat
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (R : Type v) [CommRing R]
    (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
      ModuleCat.{u} R) :
    IsAffine X :=
  isAffine_of_quasicoherentModules_equivalent_moduleCat X R e.symm


end AlgebraicGeometry.AffineOfModuleCategory

