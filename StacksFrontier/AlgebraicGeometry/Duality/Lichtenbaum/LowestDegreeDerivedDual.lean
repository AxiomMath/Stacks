module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedBiduality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomBoundedBelow
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom

/-!
# The lowest cohomology sheaf of `R𝓗om(G, L)`

Let `X` be a scheme, `G` an `𝒪_X`-module and `L ∈ D(𝒪_X)` with `H^j(L) = 0` for `j < b`. Then
`R𝓗om(G, L)` has no cohomology below degree `b` and `H^b(R𝓗om(G, L)) = 𝓗om(G, H^b(L))`. This file
proves the consequence of that identification which [Stacks, Tag 0G5E] uses: if `H^b(L)` has no
local section over `W` vanishing on `W ∩ V`, then `H^b(R𝓗om(G, L))` has no global section
vanishing on `V`. In the source this is "`𝓗om(G, ω_X)` is torsion free, hence has no nonzero
sections vanishing on a nonempty open".

## Main results

* `Stacks.Duality.Lichtenbaum.sheafHomComplex_section_eq_zero`: the statement for the internal Hom
  complex `𝓗om^•(E, J)` out of a complex `E` concentrated in degree zero, on the nose.
* `Stacks.Duality.Lichtenbaum.homology_derivedDualInto_section_eq_zero`: the statement for the
  derived internal Hom `R𝓗om(G, L)`.

## Implementation notes

`L` is represented by a K-injective complex `J` concentrated in degrees `≥ b`, so that
`R𝓗om(G, L)` is the internal Hom complex `𝓗om^•(G, J)` (`RingedSite.derivedSheafHomComparison`),
which is concentrated in degrees `≥ b`. Its `b`-th cohomology sheaf is therefore its sheaf of
`b`-cocycles. A `b`-cocycle over `⊤` is, through the description of sections of the internal Hom
complex by cochains of the restricted complexes (`RingedSite.SheafHomComplex.sectionsIso`), a
morphism `φ : G ⟶ J^b` with `d_J ∘ φ = 0`; its values are sections of `J^b` killed by `d_J`, that
is sections of `Ker(J^b ⟶ J^{b+1}) = H^b(L)`, and restriction of `φ` to `V` restricts these values
(`RingedSite.SheafHomComplex.restrict_natural`). Rather than building the sheaf isomorphism
`H^b(R𝓗om(G, L)) ≅ 𝓗om(G, H^b(L))`, the argument is run on these sections, which is all that
is used.

The derived category is the standard model `HasDerivedCategory.standard`, the one at which
`RingedSite.derivedDualInto` and `Stacks.Duality.boundedCoherentDuality` are stated; it is named
explicitly. The computations take place in `Stacks.SheafOfModules.StructureSheafModules X.sheaf`,
the spelling of `X.Modules` at which the internal Hom complex is built.

## References

* [Stacks Project, Tag 0G5E](https://stacks.math.columbia.edu/tag/0G5E)
* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u

namespace Stacks.Duality.Lichtenbaum

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.RingedSite

variable {X : Scheme.{u}}

/-- **A global `b`-cocycle of `𝓗om^•(E, J)` vanishing on `V` is zero**, for `E` concentrated in
degree zero, provided no section of `J^b` over an open `W` which is killed by `d_J` and vanishes
on `W ∩ V` is nonzero. Such a cocycle is a morphism `φ : E^0 ⟶ J^b` with `d_J ∘ φ = 0`; each of
its values is a section of `J^b` killed by `d_J`, vanishing on `W ∩ V` because `φ|_V = 0`. -/
theorem sheafHomComplex_section_eq_zero (E J : CochainComplex X.Modules ℤ)
    (hE : ∀ p, p ≠ 0 → IsZero (E.X p)) (b : ℤ) (V : X.Opens)
    (hJ : ∀ (W : X.Opens) (y : (J.X b).val.obj (op W)),
      (J.d b (b + 1)).val.app (op W) y = 0 →
        (J.X b).val.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op y = 0 → y = 0)
    (s : ((sheafHomComplex (Stacks.SheafOfModules.ringedSite X.sheaf) E J).obj.X b).val.obj
      (op (⊤ : X.Opens)))
    (hd : ((sheafHomComplex (Stacks.SheafOfModules.ringedSite X.sheaf) E J).obj.d b
      (b + 1)).val.app (op ⊤) s = 0)
    (hs : ((sheafHomComplex (Stacks.SheafOfModules.ringedSite X.sheaf) E J).obj.X b).val.map
      (homOfLE (le_top : V ≤ ⊤)).op s = 0) :
    s = 0 := by
  let H := sheafHomComplex (Stacks.SheafOfModules.ringedSite X.sheaf) E J
  let e := H.sectionsIso (⊤ : X.Opens)
  let c : Cochain _ _ b := (AddCommGrpCat.Hom.hom (e.hom.f b)) s
  have hδ : δ b (b + 1) c = 0 := by
    have h := ConcreteCategory.congr_hom (e.hom.comm b (b + 1)) s
    have h2 : (AddCommGrpCat.Hom.hom
        (((Stacks.SheafOfModules.ringedSite X.sheaf).sectionComplex H.obj ⊤).d b (b + 1))) s = 0 :=
      hd
    have h3 : δ b (b + 1) c = (AddCommGrpCat.Hom.hom (e.hom.f (b + 1)))
        ((AddCommGrpCat.Hom.hom
          (((Stacks.SheafOfModules.ringedSite X.sheaf).sectionComplex H.obj ⊤).d b (b + 1))) s) :=
      h
    rw [h3, h2]
    exact map_zero _
  suffices hc : c = 0 by
    exact (Iso.hom_inv_id_apply (HomologicalComplex.Hom.isoApp e b) s).symm.trans
      ((congrArg (AddCommGrpCat.Hom.hom (e.inv.f b)) hc).trans (map_zero _))
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [Cochain.zero_v]
  by_cases hp : p = 0
  · subst hp
    obtain rfl : q = b := by omega
    ext W' x
    have hcd : c.v 0 q hpq ≫
        ((Stacks.SheafOfModules.ringedSite X.sheaf).restrictComplex J ⊤).d q (q + 1) = 0 := by
      have h1 := Cochain.congr_v hδ 0 (q + 1) (by omega)
      rw [δ_v q (q + 1) rfl c 0 (q + 1) _ q 1 (by omega) (by omega), Cochain.zero_v] at h1
      have hz : ((Stacks.SheafOfModules.ringedSite X.sheaf).restrictComplex E ⊤).d 0 1 = 0 :=
        ((SheafOfModules.overFunctor _ _).map_isZero (hE 1 one_ne_zero)).eq_of_tgt _ _
      rwa [hz, zero_comp, smul_zero, add_zero] at h1
    refine (hJ W'.unop.left _ ?_ ?_).trans rfl
    · exact congrArg (fun φ => (φ.val.app W') x) hcd
    · have hnat := PresheafOfModules.naturality_apply (c.v 0 q hpq).val
        (Over.homMk (homOfLE (inf_le_left : W'.unop.left ⊓ V ≤ W'.unop.left))
          (Subsingleton.elim _ _) :
          Over.mk (homOfLE (inf_le_right : W'.unop.left ⊓ V ≤ V) ≫
            homOfLE (le_top : V ≤ ⊤)) ⟶ W'.unop).op x
      have hres := H.restrict_natural (homOfLE (le_top : V ≤ ⊤)) q 0 q hpq s
        (homOfLE (inf_le_right : W'.unop.left ⊓ V ≤ V))
        ((E.X 0).val.map (homOfLE (inf_le_left : W'.unop.left ⊓ V ≤ W'.unop.left)).op x)
      have h0 : Cochain.v ((AddCommGrpCat.Hom.hom ((H.sectionsIso V).hom.f q))
          ((H.obj.X q).val.map (homOfLE (le_top : V ≤ ⊤)).op s)) 0 q hpq = 0 := by
        have hs' : (H.obj.X q).val.map (homOfLE (le_top : V ≤ ⊤)).op s = 0 := hs
        rw [hs']
        exact Cochain.congr_v (map_zero (AddCommGrpCat.Hom.hom ((H.sectionsIso V).hom.f q))) _ _ _
      rw [h0] at hres
      exact hnat.symm.trans (hres.trans rfl)
  · exact ((SheafOfModules.overFunctor _ _).map_isZero (hE p hp)).eq_of_src _ _

/-- A cohomologically bounded-below object of the derived category of an abelian category with
enough injectives has a K-injective representative concentrated in degrees `≥ b` on the nose. -/
theorem exists_isStrictlyGE_isKInjective_iso {A : Type (u + 1)} [Category.{u} A] [Abelian A]
    [EnoughInjectives A] [HasDerivedCategory A] (L : DerivedCategory A) (b : ℤ)
    (hL : ∀ j < b, IsZero ((DerivedCategory.homologyFunctor A j).obj L)) :
    ∃ J : CochainComplex A ℤ, J.IsStrictlyGE b ∧ J.IsKInjective ∧
      Nonempty (DerivedCategory.Q.obj J ≅ L) := by
  have : L.IsGE b := (DerivedCategory.isGE_iff L b).2 hL
  obtain ⟨C, hC, ⟨iC⟩⟩ := L.exists_iso_Q_obj_of_isGE b
  obtain ⟨J, -, hJ⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE b C
  exact ⟨J.cocomplex, hJ, CochainComplex.isKInjective_of_injective J.cocomplex b,
    ⟨(asIso (DerivedCategory.Q.map J.ι)).symm ≪≫ iC.symm⟩⟩

/-- A section killed by a morphism of sheaves of modules comes from its kernel: kernels of
sheaves of modules are computed object by object. -/
theorem exists_app_eq_of_isLimit {C : Type*} [Category C] {Jt : GrothendieckTopology C}
    {R : Sheaf Jt RingCat.{u}} {M N K : SheafOfModules.{u} R} {f : M ⟶ N} {ι : K ⟶ M}
    {w : ι ≫ f = 0} (h : IsLimit (KernelFork.ofι ι w)) (W : Cᵒᵖ) (y : M.val.obj W)
    (hy : f.val.app W y = 0) : ∃ z : K.val.obj W, ι.val.app W z = y := by
  have : (SheafOfModules.evaluation R W).Additive := ⟨rfl⟩
  have hl := KernelFork.mapIsLimit _ h (SheafOfModules.evaluation R W)
  let k : ModuleCat.of (R.obj.obj W) (R.obj.obj W) ⟶ (SheafOfModules.evaluation R W).obj M :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton (R.obj.obj W) (M.val.obj W) y)
  have hk : k ≫ (SheafOfModules.evaluation R W).map f = 0 := by
    ext
    exact ((f.val.app W).hom.map_smul (1 : R.obj.obj W) y).trans (by rw [hy, smul_zero]; rfl)
  obtain ⟨l, hl'⟩ := KernelFork.IsLimit.lift' hl k hk
  exact ⟨l.hom 1, (congrArg (fun φ => φ.hom (1 : R.obj.obj W)) hl').trans (one_smul _ y)⟩

/-- A monomorphism of sheaves of modules has no nonzero section sent to zero. -/
private theorem eq_zero_of_app_eq_zero {C : Type*} [Category C] {Jt : GrothendieckTopology C}
    {R : Sheaf Jt RingCat.{u}} {M N : SheafOfModules.{u} R} (f : M ⟶ N) [Mono f] {W : Cᵒᵖ}
    {y : M.val.obj W} (h : f.val.app W y = 0) : y = 0 :=
  Stacks.SheafOfModules.injective_app_of_mono f W (h.trans (map_zero _).symm)

/-- A morphism of sheaves of modules sends a section whose restriction vanishes to one whose
restriction vanishes. -/
private theorem map_app_eq_zero_of_map_eq_zero {C : Type*} [Category C]
    {Jt : GrothendieckTopology C} {R : Sheaf Jt RingCat.{u}} {M N : SheafOfModules.{u} R}
    (f : M ⟶ N) {W W' : Cᵒᵖ} (i : W ⟶ W') {y : M.val.obj W} (h : M.val.map i y = 0) :
    N.val.map i (f.val.app W y) = 0 :=
  (PresheafOfModules.naturality_apply f.val i y).symm.trans ((congrArg _ h).trans (map_zero _))

/-- **The lowest cohomology sheaf of `R𝓗om(G, L)` has no global section vanishing on `V`**, when
`L` has no cohomology below degree `b` and `H^b(L)` has no local section over `W` vanishing on
`W ∩ V`.

Represent `L` by a K-injective complex `J` concentrated in degrees `≥ b`. Then
`R𝓗om(G, L) = 𝓗om^•(G, J)` is concentrated in degrees `≥ b`, so its `b`-th cohomology sheaf is the
sheaf of `b`-cocycles, a subsheaf of `𝓗om^•(G, J)^b`; and a `b`-cocycle is a morphism
`G ⟶ J^b` landing in `Ker(J^b ⟶ J^{b+1}) = H^b(L)`
(`Stacks.Duality.Lichtenbaum.sheafHomComplex_section_eq_zero`). -/
theorem homology_derivedDualInto_section_eq_zero (G : X.Modules)
    (L : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules)) (b : ℤ)
    (hL : ∀ j < b, IsZero ((@DerivedCategory.homologyFunctor X.Modules _ _
      (HasDerivedCategory.standard X.Modules) j).obj L))
    (V : X.Opens)
    (hLb : ∀ (W : X.Opens) (z : Γ((@DerivedCategory.homologyFunctor X.Modules _ _
        (HasDerivedCategory.standard X.Modules) b).obj L, W)),
      ((@DerivedCategory.homologyFunctor X.Modules _ _
        (HasDerivedCategory.standard X.Modules) b).obj L).presheaf.map
          (homOfLE (inf_le_left : W ⊓ V ≤ W)).op z = 0 → z = 0)
    (σ : Γ((@DerivedCategory.homologyFunctor X.Modules _ _
        (HasDerivedCategory.standard X.Modules) b).obj
      (RingedSite.derivedDualInto (Stacks.SheafOfModules.ringedSite X.sheaf) L
        ((@DerivedCategory.singleFunctor X.Modules _ _
          (HasDerivedCategory.standard X.Modules) 0).obj G)), ⊤))
    (hσ : ((@DerivedCategory.homologyFunctor X.Modules _ _
        (HasDerivedCategory.standard X.Modules) b).obj
      (RingedSite.derivedDualInto (Stacks.SheafOfModules.ringedSite X.sheaf) L
        ((@DerivedCategory.singleFunctor X.Modules _ _
          (HasDerivedCategory.standard X.Modules) 0).obj G))).presheaf.map
            (homOfLE (le_top : V ≤ ⊤)).op σ = 0) :
    σ = 0 := by
  let : HasDerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf) :=
    HasDerivedCategory.standard _
  let L' : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf) := L
  obtain ⟨J, hJGE, hJinj, ⟨eJ⟩⟩ := exists_isStrictlyGE_isKInjective_iso L' b hL
  let E := (CochainComplex.singleFunctor
    (Stacks.SheafOfModules.StructureSheafModules X.sheaf) 0).obj G
  have : E.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff E 0).2 fun i hi =>
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  let C := (Stacks.SheafOfModules.sheafHomComplex X.sheaf E J).obj
  let eD : ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
      (op (DerivedCategory.Q.obj E))).obj L ≅ DerivedCategory.Q.obj C :=
    ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
        (op (DerivedCategory.Q.obj E))).mapIso eJ.symm ≪≫
      Stacks.SheafOfModules.derivedSheafHomComparison X.sheaf E J
  have hC0 : C.d (b - 1) b = 0 := by
    have : (show CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.SheafOfModules.ringedSite X.sheaf).O)) ℤ from E).IsStrictlyLE 0 :=
      (inferInstance : E.IsStrictlyLE 0)
    have : (show CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.SheafOfModules.ringedSite X.sheaf).O)) ℤ from J).IsStrictlyGE b := hJGE
    have := isStrictlyGE_sheafHomComplex (Stacks.SheafOfModules.ringedSite X.sheaf) E J 0 b
    exact (CochainComplex.isZero_of_isStrictlyGE
      (sheafHomComplex (Stacks.SheafOfModules.ringedSite X.sheaf) E J).obj (b - 0) (b - 1)
        (by omega)).eq_of_src _ _
  let ι₀ : (DerivedCategory.homologyFunctor _ b).obj
      (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
        (op (DerivedCategory.Q.obj E))).obj L) ≅ C.cycles b :=
    (DerivedCategory.homologyFunctor _ b).mapIso eD ≪≫
      (DerivedCategory.homologyFunctorFactors _ b).app C ≪≫
        (C.isoHomologyπ (b - 1) b (by simp) hC0).symm
  let φ := ι₀.hom ≫ C.iCycles b
  have hφd : φ ≫ C.d b (b + 1) = 0 := by simp [φ]
  have : Mono φ := mono_comp _ _
  have hJ0 : J.d (b - 1) b = 0 := (J.isZero_of_isStrictlyGE b (b - 1) (by omega)).eq_of_src _ _
  let ψ : J.cycles b ≅ (DerivedCategory.homologyFunctor _ b).obj L' :=
    J.isoHomologyπ (b - 1) b (by simp) hJ0 ≪≫
      ((DerivedCategory.homologyFunctorFactors _ b).app J).symm ≪≫
        (DerivedCategory.homologyFunctor _ b).mapIso eJ
  have hJ : ∀ (W : X.Opens) (y : (J.X b).val.obj (op W)),
      (J.d b (b + 1)).val.app (op W) y = 0 →
        (J.X b).val.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op y = 0 → y = 0 := by
    intro W y hy hyV
    obtain ⟨z, rfl⟩ := exists_app_eq_of_isLimit (J.cyclesIsKernel b (b + 1) (by simp)) (op W) y hy
    have hz : (J.cycles b).val.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op z = 0 := by
      refine eq_zero_of_app_eq_zero (W := op (W ⊓ V)) (J.iCycles b) ?_
      rw [PresheafOfModules.naturality_apply, hyV]
      rfl
    have hψ : ψ.hom.val.app (op W) z = 0 := by
      exact hLb W _ (map_app_eq_zero_of_map_eq_zero ψ.hom _ hz)
    rw [eq_zero_of_app_eq_zero ψ.hom hψ, map_zero]
  have hs : φ.val.app (op ⊤) σ = 0 := by
    refine sheafHomComplex_section_eq_zero E J
      (fun p hp => HomologicalComplex.isZero_single_obj_X _ _ _ _ hp) b V hJ _ ?_ ?_
    · exact (congrArg (fun t => t.val.app (op ⊤) σ) hφd).trans rfl
    · exact map_app_eq_zero_of_map_eq_zero φ _ hσ
  exact eq_zero_of_app_eq_zero φ hs

end Stacks.Duality.Lichtenbaum

end
