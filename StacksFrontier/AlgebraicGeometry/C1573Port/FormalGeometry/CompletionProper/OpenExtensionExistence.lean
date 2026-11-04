module

public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Sections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GrothendieckExistenceProper
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalAnnihilation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeCoherentDerivedHom
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Vanishing
public import StacksFrontier.AlgebraicGeometry.C1573Port.FormalGeometry.CoherentAdicSystem.OpenCoverLocal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Epi
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Abelian
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonInjectivity
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# Grothendieck existence with proper support on an open subscheme of a proper scheme

Let `A` be a Noetherian ring complete with respect to an ideal `I`, let `p : Y' ⟶ Spec A` be
proper and let `V` be an open subscheme of `Y'`. A coherent `I`-adic system `(𝓕_n)` on `V` whose
support is proper over `A` is the completion of a coherent `𝒪_V`-module with support proper over
`A`.

The argument is the one in the proof of Stacks 08BE: the direct images `j_*𝓕_n` along the
inclusion `j : V ⟶ Y'` form a coherent adic system on `Y'` (they are `𝓕_n` over `V` and zero away
from the support, which is closed in `Y'`), Stacks 088C algebraizes it to `𝓕'`, the support of
`𝓕'` lies in `V` because its trace on `V(I)` does and `I` lies in the Jacobson radical of `A`, and
`𝓕'|_V` is the module sought.

## Main results

All names are in the namespace `Stacks.Algebraization`.

* `C1573.exists_completion_iso_of_opens`: Grothendieck existence with proper support on an open
  subscheme of a proper scheme.
* `C1573.isCoherentAdicSystem_pushforward_of_isClosed_image`: the direct images of a coherent adic
  system on an open, supported on a subset closed in the ambient scheme, form a coherent adic
  system.
* `C1573.supp_subset_of_completion_iso`: the support of an algebraization on `Y'` lies in `V`.
-/

namespace Stacks.Algebraization.C1573
end Stacks.Algebraization.C1573

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)

open _root_.Stacks.Algebraization.C1573
variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {Y' : Scheme.{u}} (p : Y' ⟶ Spec (.of A)) [IsProper p] (V : Y'.Opens)

/-- The sections of a sheaf of modules over an open disjoint from its support vanish. -/
theorem C1573.subsingleton_sections_of_disjoint_supp {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (h : Disjoint (U : Set X) (SheafOfModules.supp M)) : Subsingleton Γ(M, U) := by
  refine ⟨fun s t => ?_⟩
  refine TopCat.Presheaf.IsSheaf.section_ext (Scheme.Modules.isSheaf M) (U := op U)
    fun x hx => ?_
  have hst : Subsingleton ↑(TopCat.Presheaf.stalk M.presheaf x) := by
    refine not_nontrivial_iff_subsingleton.mp fun hnt => ?_
    exact Set.disjoint_left.1 h hx ((SheafOfModules.mem_supp_iff_nontrivial_stalk M x).mpr hnt)
  obtain ⟨W, hxW, iU, iV, he⟩ := M.presheaf.germ_eq x hx hx s t (Subsingleton.elim _ _)
  exact ⟨W, leOfHom iU, hxW, by
    rw [Subsingleton.elim (homOfLE (leOfHom iU)) iU, he, Subsingleton.elim iV iU]⟩

/-- **The direct image along an open immersion of a module supported away from an open vanishes
on that open.** -/
theorem C1573.isZero_restrict_pushforward_of_disjoint {Y Y' : Scheme.{u}} (j : Y ⟶ Y')
    [IsOpenImmersion j] (M : Y.Modules) (V : Y'.Opens)
    (h : Disjoint ((j ⁻¹ᵁ V : Y.Opens) : Set Y) (SheafOfModules.supp M)) :
    IsZero ((Scheme.Modules.restrictFunctor V.ι).obj ((Scheme.Modules.pushforward j).obj M)) := by
  refine StacksTag09NE.module_isZero_of_sections_subsingleton _ fun W => ?_
  have h1 : Subsingleton Γ(M, j ⁻¹ᵁ (V.ι ''ᵁ W)) :=
    subsingleton_sections_of_disjoint_supp M _ (h.mono_left (fun y hy => by
      obtain ⟨w, -, hw⟩ := hy
      change j y ∈ V
      rw [← hw]
      exact w.2))
  have h2 : Subsingleton Γ((Scheme.Modules.pushforward j).obj M, V.ι ''ᵁ W) := h1
  exact ((((Scheme.Modules.pushforward j).obj M).restrictAppIso V.ι W).addCommGroupIsoToAddEquiv
    |>.subsingleton_congr).2 h2

/-- Isomorphic sheaves of modules have the same support. -/
alias C1573.supp_subset_of_iso :=
  Stacks.AlgebraicGeometry.IrreducibleDevissage.supp_subset_of_iso

/-- The support of the direct image along the inclusion of an open of a module supported in a
subset `T` lies in the image of `T`. -/
theorem C1573.supp_pushforward_subset {Y' : Scheme.{u}} (V : Y'.Opens) (M : V.toScheme.Modules)
    (T : Set V.toScheme) (hT : SheafOfModules.supp M ⊆ T) (hTcl : IsClosed (V.ι.base '' T)) :
    SheafOfModules.supp ((Scheme.Modules.pushforward V.ι).obj M) ⊆ V.ι.base '' T := by
  let Vc : Y'.Opens := ⟨(V.ι.base '' T)ᶜ, hTcl.isOpen_compl⟩
  have hz := isZero_restrict_pushforward_of_disjoint V.ι M Vc (Set.disjoint_left.2 fun y hy hys =>
    hy ⟨y, hT hys, rfl⟩)
  intro x hx
  by_contra hxT
  exact Stacks.Coherent.supp_subset_compl_of_isZero_restrict Vc _ hz hx hxT

/-- The support of the restriction to an open is the preimage of the support. -/
theorem C1573.supp_restrict_eq {X : Scheme.{u}} (V : X.Opens) (M : X.Modules) :
    SheafOfModules.supp ((Scheme.Modules.restrictFunctor V.ι).obj M) =
      V.ι.base ⁻¹' SheafOfModules.supp M := by
  ext y
  let φ := ((Scheme.Modules.restrictStalkNatIso V.ι y).app M).addCommGroupIsoToAddEquiv
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨φ a, fun h => ha (φ.injective (h.trans (map_zero _).symm))⟩
  · rintro ⟨a, ha⟩
    exact ⟨φ.symm a, fun h => ha (φ.symm.injective (h.trans (map_zero _).symm))⟩

/-- **Nakayama for the support of the first term of a completion.** A point of the support of a
coherent module `F` at which the ideal sheaf `J` vanishes lies in the support of `F / J F`, the
first term of the `J`-adic completion of `F`. -/
theorem C1573.mem_supp_completion_zero_of_le {X : Scheme.{u}} [IsLocallyNoetherian X]
    (J : X.IdealSheafData) (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    {x : X} (hx : x ∈ SheafOfModules.supp F.obj) (U : X.affineOpens) (hxU : x ∈ (U : Set X))
    (hq2 : J.ideal U ≤ (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal) :
    x ∈ SheafOfModules.supp (((completionFunctor X J).obj F).obj.obj (op 0)) := by
  have : F.obj.IsCoherent := F.property
  have hqc : F.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent F.obj
  have hft : F.obj.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType
  have h0c : (((completionFunctor X J).obj F).obj.obj (op 0)).IsCoherent :=
    ((completionFunctor X J).obj F).property.1 0
  have h0q : (((completionFunctor X J).obj F).obj.obj (op 0)).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  let M : X.Modules := F.obj
  have hfin : Module.Finite Γ(X, U.1) Γ(M, U.1) :=
    moduleFinite_sections_on_affine M U.1 U.2
  have hq1 := (Scheme.Modules.mem_support_sections_iff_mem_supp F.obj U x hxU).2 hx
  have hq3 : U.2.primeIdealOf ⟨x, hxU⟩ ∈ Module.support Γ(X, U.1)
      (Γ(M, U.1) ⧸ (J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)))) := by
    rw [Module.support_quotient]
    exact ⟨hq1, hq2⟩
  let N : X.Modules := ((completionFunctor X J).obj F).obj.obj (op 0)
  let φ : M ⟶ N := completionProjection X J F 0
  let π := Scheme.Modules.sectionsLinearMap φ U.1
  have hker0 := completionProjection_app_ker X J F 0 U
  have hker : LinearMap.ker π = J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
    ext y
    have := SetLike.ext_iff.1 hker0 y
    rwa [zero_add, pow_one] at this
  have hsurj : Function.Surjective π := completionProjection_app_surjective X J F 0 U
  have e := (Submodule.quotEquivOfEq _ _ hker.symm).trans (π.quotKerEquivOfSurjective hsurj)
  rw [e.support_eq] at hq3
  exact (Scheme.Modules.mem_support_sections_iff_mem_supp _ U x hxU).1 hq3

/-- **Every term of a coherent adic system is supported in the support of the first term.** If
the first term is supported in a closed subset `T`, so is every term. -/
theorem C1573.supp_coherentAdicSystem_obj_subset_supp_zero {X : Scheme.{u}} [IsLocallyNoetherian X]
    {J : X.IdealSheafData} (E : Stacks.Coherent.CoherentAdicSystems J) (T : Closeds X)
    (hT : SheafOfModules.supp (E.obj.obj (op 0)) ⊆ T) (n : ℕ) :
    SheafOfModules.supp (E.obj.obj (op n)) ⊆ T := by
  let W : X.Opens := T.compl
  have h0 : IsZero ((Scheme.Modules.restrictFunctor W.ι).obj (E.obj.obj (op 0))) := by
    refine StacksTag09NE.module_isZero_of_sections_subsingleton _ fun U => ?_
    have h1 : Subsingleton Γ(E.obj.obj (op 0), W.ι ''ᵁ U) :=
      subsingleton_sections_of_disjoint_supp _ _ (Set.disjoint_left.2 fun x hx hxs => by
        obtain ⟨w, -, rfl⟩ := hx
        exact w.2 (hT hxs))
    exact (((E.obj.obj (op 0)).restrictAppIso W.ι U).addCommGroupIsoToAddEquiv
      |>.subsingleton_congr).2 h1
  have hall := Stacks.Coherent.isZero_functor_of_isZero_obj_zero
    (Stacks.Coherent.isCoherentAdicSystem_restrict J W.ι E) h0
  have hn : IsZero ((Scheme.Modules.restrictFunctor W.ι).obj (E.obj.obj (op n))) :=
    hall.obj (op n)
  intro x hx
  by_contra hxT
  exact Stacks.Coherent.supp_subset_compl_of_isZero_restrict W _ hn hx hxT

omit [IsAdicComplete I A] in
open ZeroObject in
/-- **The direct images of a coherent adic system on an open subscheme, supported on a subset
closed in the ambient scheme, form a coherent adic system.** -/
theorem C1573.isCoherentAdicSystem_pushforward_of_isClosed_image
    (E : Stacks.Coherent.CoherentAdicSystems
      (letI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian p
       letI : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian (V.ι ≫ p)
       (baseIdealSheaf A I p).comap V.ι))
    (T : Closeds V.toScheme) (hT : SheafOfModules.supp (E.obj.obj (op 0)) ⊆ T)
    (hTcl : IsClosed (V.ι.base '' T)) :
    letI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian p
    Stacks.Coherent.IsCoherentAdicSystem (baseIdealSheaf A I p)
      (E.obj ⋙ Scheme.Modules.pushforward V.ι) := by
  let : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian p
  let : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian (V.ι ≫ p)
  let Vc : Y'.Opens := ⟨(V.ι.base '' T)ᶜ, hTcl.isOpen_compl⟩
  let U : ULift.{u} Bool → Y'.Opens := fun b => if b.down then V else Vc
  have hU : iSup U = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    by_cases hx : x ∈ V
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨true⟩, hx⟩
    · refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨false⟩, ?_⟩
      rintro ⟨y, -, rfl⟩
      exact hx y.2
  refine Stacks.Coherent.C1573.isCoherentAdicSystem_of_restrict _ _ U hU fun b => ?_
  rcases b with ⟨_ | _⟩
  · have hz : ∀ n, IsZero ((E.obj ⋙ Scheme.Modules.pushforward V.ι ⋙
        Scheme.Modules.restrictFunctor Vc.ι).obj (op n)) := fun n =>
      isZero_restrict_pushforward_of_disjoint V.ι _ Vc (Set.disjoint_left.2 fun y hy hys => hy
        ⟨y, supp_coherentAdicSystem_obj_subset_supp_zero E T hT n hys, rfl⟩)
    have hZ : IsZero (E.obj ⋙ Scheme.Modules.pushforward V.ι ⋙
        Scheme.Modules.restrictFunctor Vc.ι) :=
      Functor.isZero _ fun n => hz n.unop
    have : IsLocallyNoetherian Vc.toScheme := inferInstance
    have : HasFiniteBiproducts (Stacks.Coherent.CoherentAdicSystems
        ((baseIdealSheaf A I p).comap Vc.ι)) := HasFiniteBiproducts.of_hasFiniteProducts
    have : HasZeroObject (Stacks.Coherent.CoherentAdicSystems
        ((baseIdealSheaf A I p).comap Vc.ι)) := hasZeroObject_of_hasFiniteBiproducts _
    have h0 := (Stacks.Coherent.isZero_coherentAdicSystems_iff _
      (0 : Stacks.Coherent.CoherentAdicSystems ((baseIdealSheaf A I p).comap Vc.ι))).1
        (isZero_zero _)
    exact Stacks.Coherent.isCoherentAdicSystem_of_iso _ (h0.iso hZ)
      (0 : Stacks.Coherent.CoherentAdicSystems ((baseIdealSheaf A I p).comap Vc.ι)).property
  · have e : E.obj ≅ E.obj ⋙ Scheme.Modules.pushforward V.ι ⋙
        Scheme.Modules.restrictFunctor V.ι :=
      Functor.isoWhiskerLeft E.obj (Scheme.Modules.restrictFunctorAdjCounitIso V.ι).symm
    exact Stacks.Coherent.isCoherentAdicSystem_of_iso _ e E.property

omit [IsNoetherianRing A] in
/-- The image in `Y'` of a closed subset of `V` which is proper over `A` is closed. -/
theorem C1573.isClosed_image_of_isProperOver (T : Closeds V.toScheme)
    (hT : IsProperOver (V.ι ≫ p) T) :
    IsClosed (V.ι.base '' T) := by
  let K := Scheme.IdealSheafData.vanishingIdeal T
  have h1 : IsProper ((K.subschemeι ≫ V.ι) ≫ p) := by
    rw [Category.assoc]
    exact hT
  have h2 : IsProper (K.subschemeι ≫ V.ι) := IsProper.of_comp _ p
  have h3 := (K.subschemeι ≫ V.ι).isClosedMap.isClosed_range
  have h4 : Set.range (K.subschemeι ≫ V.ι).base = V.ι.base '' T := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, K.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rwa [h4] at h3

/-- **The support of an algebraization on `Y'` lies in `V`.** If the first term of the completion
of a coherent module `F'` on `Y'` is supported in the image of a closed subset `T` of `V` proper
over `A`, then the support of `F'` lies in `V`. -/
theorem C1573.supp_subset_of_completion_iso
    (F' : AlgebraicGeometry.SheafOfModules.CoherentModules Y'.ringCatSheaf)
    (T : Closeds V.toScheme) (_hT : IsProperOver (V.ι ≫ p) T)
    (h0 : SheafOfModules.supp (((letI : IsLocallyNoetherian Y' :=
      LocallyOfFiniteType.isLocallyNoetherian p
      completionFunctor Y' (baseIdealSheaf A I p)).obj F').obj.obj (op 0)) ⊆ V.ι.base '' T) :
    SheafOfModules.supp F'.obj ⊆ (V : Set Y') := by
  let : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian p
  intro y hy
  by_contra hyV
  have hcoh : F'.obj.IsCoherent := F'.property
  have hft : F'.obj.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType
  have hcl := @SheafOfModules.isClosed_supp _ Y'.ringCatSheaf F'.obj hft
  let C := SheafOfModules.supp F'.obj ∩ (V : Set Y')ᶜ
  have hCcl : IsClosed C := hcl.inter V.isOpen.isClosed_compl
  have hpC : IsClosed (p.base '' C) := p.isClosedMap _ hCcl
  obtain ⟨m, ⟨y', hy'C, rfl⟩, hm⟩ := hpC.exists_closed_singleton ⟨_, y, ⟨hy, hyV⟩, rfl⟩
  have hmax : (p.base y').asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 hm
  have hI : I ≤ (p.base y').asIdeal :=
    (IsAdicComplete.le_jacobson_bot I).trans (sInf_le ⟨bot_le, hmax⟩)
  obtain ⟨_, ⟨U, hU, rfl⟩, hy'U, -⟩ :=
    Y'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y') isOpen_univ
  let U' : Y'.affineOpens := ⟨U, hU⟩
  have hJ : (baseIdealSheaf A I p).ideal U' ≤ (U'.2.primeIdealOf ⟨y', hy'U⟩).asIdeal := by
    rw [Stacks.Cohomology.FormalFunctions.baseIdealSheaf_ideal, Ideal.map_le_iff_le_comap,
      Stacks.Cohomology.FormalFunctions.baseIdeal, Ideal.map_le_iff_le_comap]
    intro a ha
    refine Stacks.Algebraization.mem_primeIdealOf_of_notMem_basicOpen U' hy'U _ ?_
    rw [Scheme.basicOpen_res]
    rintro ⟨-, hb⟩
    have hb' : y' ∈ p ⁻¹ᵁ (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv a) := by
      rwa [Scheme.preimage_basicOpen]
    change p.base y' ∈ (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv a) at hb'
    rw [basicOpen_eq_of_affine] at hb'
    exact hb' (hI ha)
  have hmem := mem_supp_completion_zero_of_le (baseIdealSheaf A I p) F' hy'C.1 U' hy'U hJ
  obtain ⟨z, -, hz⟩ := h0 hmem
  exact hy'C.2 (hz ▸ z.2)

/-- **Grothendieck existence with proper support on an open subscheme of a proper scheme.** -/
theorem C1573.exists_completion_iso_of_opens :
    letI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian p
    letI : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian (V.ι ≫ p)
    ∀ E : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I (V.ι ≫ p)),
      HasProperSupport (V.ι ≫ p) (E.obj.obj (op 0)) →
      ∃ F : AlgebraicGeometry.SheafOfModules.CoherentModules V.toScheme.ringCatSheaf,
        HasProperSupport (V.ι ≫ p) F.obj ∧
          Nonempty ((Stacks.Algebraization.completionFunctor V.toScheme
            (baseIdealSheaf A I (V.ι ≫ p))).obj F ≅ E) := by
  let : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian p
  let : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian (V.ι ≫ p)
  have hJ : (baseIdealSheaf A I p).comap V.ι = baseIdealSheaf A I (V.ι ≫ p) :=
    Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap A I p V.ι
  rw [← hJ]
  intro E hE
  obtain ⟨T, hTsupp, hTp⟩ := hE
  have hTcl := isClosed_image_of_isProperOver A p V T hTp
  let E' : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I p) :=
    ⟨E.obj ⋙ Scheme.Modules.pushforward V.ι,
      isCoherentAdicSystem_pushforward_of_isClosed_image A I p V E T hTsupp.symm.le hTcl⟩
  have := isEquivalence_completionFunctor_of_isProper A I p
  obtain ⟨F', ⟨eF'⟩⟩ :=
    Functor.EssSurj.mem_essImage (F := completionFunctor Y' (baseIdealSheaf A I p)) E'
  let eF'o := (ObjectProperty.ι _).mapIso eF'
  have h0 : SheafOfModules.supp (((completionFunctor Y' (baseIdealSheaf A I p)).obj F').obj.obj
      (op 0)) ⊆ V.ι.base '' T :=
    (supp_subset_of_iso (eF'o.app (op 0))).trans
      (supp_pushforward_subset V (E.obj.obj (op 0)) T hTsupp.symm.le hTcl)
  have hsupp := supp_subset_of_completion_iso A I p V F' T hTp h0
  let F := restrictCoherentModules V.ι F'
  refine ⟨F, ?_, ⟨ObjectProperty.isoMk _ ?_⟩⟩
  · have hF'ft : F'.obj.IsFiniteType :=
      _root_.SheafOfModules.IsCoherent.isFiniteType (M := F'.obj)
    have hcl := @SheafOfModules.isClosed_supp _ Y'.ringCatSheaf F'.obj hF'ft
    let Z : Closeds V.toScheme := ⟨V.ι.base ⁻¹' SheafOfModules.supp F'.obj,
      hcl.preimage V.ι.continuous⟩
    refine ⟨Z, (supp_restrict_eq V F'.obj).symm, ?_⟩
    let K := Scheme.IdealSheafData.vanishingIdeal Z
    have hrange : Set.range (K.subschemeι ≫ V.ι).base = SheafOfModules.supp F'.obj := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, K.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      change V.ι '' (V.ι ⁻¹' SheafOfModules.supp F'.obj) = _
      rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
      exact Set.inter_eq_left.2 hsupp
    have : IsClosedImmersion (K.subschemeι ≫ V.ι) :=
      IsClosedImmersion.of_isPreimmersion _ (hrange ▸ hcl)
    change IsProper (K.subschemeι ≫ V.ι ≫ p)
    rw [← Category.assoc]
    infer_instance
  · exact (completionRestrictOpenIso V.ι (baseIdealSheaf A I p) F').symm ≪≫
      Functor.isoWhiskerRight eF'o (Scheme.Modules.restrictFunctor V.ι) ≪≫
      Functor.isoWhiskerLeft E.obj (Scheme.Modules.restrictFunctorAdjCounitIso V.ι)

end Stacks.Algebraization

end
