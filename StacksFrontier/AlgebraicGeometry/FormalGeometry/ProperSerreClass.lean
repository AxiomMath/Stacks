module

public import Mathlib.Algebra.Category.Grp.Zero
public import StacksCore.CategoryTheory.Abelian.SerreClass.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Abelian
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Epi
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# Properness over the base cuts Serre subcategories out of Coh(X, ℐ)

Let `S` be a Noetherian scheme, `f : X ⟶ S` a morphism of finite type and `ℐ` a quasi-coherent
ideal sheaf on `X`. Two conditions on a coherent adic system `(F_n)` along `ℐ` are of interest in
the algebraization theorems: that the support of its first term be proper over `S`, and that some
closed subscheme of `X` proper over `S` have its ideal sheaf annihilate every term. This file
shows that each cuts a Serre subcategory out of `Coh(X, ℐ)`.

Both arguments rest on the two levelwise consequences of a short exact sequence
`0 ⟶ (G_n) ⟶ (F_n) ⟶ (H_n) ⟶ 0` of coherent adic systems: that `G_n ⟶ F_n ⟶ H_n ⟶ 0` is exact
for every `n`, and that `G_n` is a quotient of `Ker(F_m ⟶ H_m)` for some `m ≥ n`. The second is
the substance: a monomorphism of coherent adic systems need not be levelwise injective, so a
subobject's terms are reached not inside the terms of the ambient system but as quotients of
levelwise kernels further up the system.

For the support condition the ambient properness is not needed levelwise at all. The terms of a
coherent adic system all have the same support, and restriction to an open subscheme is exact on
coherent adic systems, so on the open complement of the supports of the outer terms the restricted
middle system has vanishing first term, hence vanishes; the support of the middle term is
therefore contained in the union of the outer two, which is proper over `S` because a finite union
of closed subsets proper over the base is proper over the base.

For the annihilator condition the two levelwise facts are used directly. An ideal annihilating
every term of a system annihilates every term of a subobject and of a quotient. For an extension
one multiplies the two ideals: if `𝒥` kills the `G_n` and `𝒦` kills the `H_n` then `𝒥 · 𝒦` kills
the `F_n`, by right exactness at each level, and the closed subset cut out by `𝒥 · 𝒦` is the union
of the two closed subsets, which is again proper over the base.

## Main definitions

* `Stacks.Coherent.HasProperAnnihilator` — the ideal sheaf of some closed subscheme proper over
  the base annihilates every term of the system.

## Main results

* `Stacks.Coherent.isSerreClass_hasProperSupport` — the coherent adic systems whose first term
  has support proper over the base form a Serre subcategory of `Coh(X, ℐ)`.
* `Stacks.Coherent.isSerreClass_hasProperAnnihilator` — the coherent adic systems admitting a
  common annihilating closed subscheme proper over the base form a Serre subcategory of
  `Coh(X, ℐ)`.

## Implementation notes

Coherent adic systems are indexed by `ℕᵒᵖ` and zero-indexed, so the term at `op 0` is the first
term of the system and `∀ n : ℕ` ranges over all of its terms.

Noetherianity of `X` is not a hypothesis: it follows from Noetherianity of `S` together with the
two classes expressing that `f` is of finite type, and is introduced inside the statements because
the abelian structure on `Coh(X, ℐ)`, without which a Serre subcategory cannot be spoken of,
depends on it.

Properness of a closed subscheme is stated as properness of the composite of its immersion with
`f`, which is the condition verbatim; inside the proofs it is traded for properness of the
underlying closed subset, the two being equivalent because every closed subscheme structure on a
closed subset proper over the base is proper over the base.

## References

* [Stacks Project, Tag 0CYV](https://stacks.math.columbia.edu/tag/0CYV)
* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 02MP](https://stacks.math.columbia.edu/tag/02MP)
* [Stacks Project, Tag 0CYM](https://stacks.math.columbia.edu/tag/0CYM)
* [Stacks Project, Tag 0CYR](https://stacks.math.columbia.edu/tag/0CYR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry ZeroObject

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

/-! ### Vanishing of a sheaf of modules on an open away from its support -/

/-- A sheaf of modules all of whose stalks vanish is zero. -/
private lemma isZero_of_stalks_isZero {X : Scheme.{u}} (F : X.Modules)
    (hF : ∀ x : X, IsZero
      ((TopCat.Presheaf.stalkFunctor Ab.{u} x).obj F.val.presheaf)) : IsZero F := by
  refine (IsZero.iff_id_eq_zero F).2 ((SheafOfModules.toSheaf _).map_injective ?_)
  change (𝟙 ((SheafOfModules.toSheaf _).obj F)) = 0
  exact (IsZero.iff_id_eq_zero _).mp
    ((TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).2 hF)

/-- The restriction of a sheaf of modules to an open subscheme disjoint from its support is
zero. -/
private lemma isZero_restrictFunctor_obj_of_notMem_supp {X : Scheme.{u}} (U : X.Opens)
    (F : X.Modules) (h : ∀ y : U.toScheme, U.ι y ∉ SheafOfModules.supp F) :
    IsZero ((Scheme.Modules.restrictFunctor U.ι).obj F) := by
  refine isZero_of_stalks_isZero _ fun y => ?_
  have hOrig : IsZero
      ((TopCat.Presheaf.stalkFunctor Ab.{u} (U.ι y)).obj F.val.presheaf) := by
    refine (AddCommGrpCat.isZero_iff_subsingleton).mpr ⟨fun a b => ?_⟩
    have hz (a : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (U.ι y)) : a = 0 := by
      by_contra ha
      exact h y ⟨a, ha⟩
    exact (hz a).trans (hz b).symm
  exact hOrig.of_iso ((Scheme.Modules.restrictStalkNatIso U.ι y).app F)

/-- A section of a sheaf of modules at a point is zero in the stalk when the stalk vanishes, so the
point is outside the support. -/
private lemma notMem_supp_of_isZero_stalk {X : Scheme.{u}} (F : X.Modules) (x : X)
    (h : IsZero
      ((TopCat.Presheaf.stalkFunctor Ab.{u} x).obj ((Scheme.Modules.toPresheaf X).obj F))) :
    x ∉ SheafOfModules.supp F := by
  rintro ⟨a, ha⟩
  exact ha ((AddCommGrpCat.subsingleton_of_isZero h).elim a 0)

/-! ### Levelwise consequences of a short exact sequence of coherent adic systems -/

/-- Every term of a zero object of `Coh(X, ℐ)` is zero. -/
private lemma isZero_obj_obj_of_isZero {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (hF : IsZero F) (n : ℕ) : IsZero (F.obj.obj (op n)) :=
  Functor.map_isZero ((evaluation ℕᵒᵖ X.Modules).obj (op n))
    (Functor.map_isZero (ObjectProperty.ι (IsCoherentAdicSystem I)) hF)

/-- A coherent adic system whose first term vanishes is a zero object of `Coh(X, ℐ)`. -/
private lemma isZero_of_isZero_obj_op_zero {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (hF : IsZero (F.obj.obj (op 0))) : IsZero F :=
  (isZero_coherentAdicSystems_iff I F).2 (isZero_functor_of_isZero_obj_zero F.property hF)

section Levelwise

variable {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)

/-- The support of the middle term of an exact short complex of coherent adic systems is contained
in the union of the supports of the first terms of its outer two systems. -/
private lemma supp_middle_subset_of_exact
    (T : ShortComplex (CoherentAdicSystems I)) (hT : T.Exact) :
    SheafOfModules.supp (T.X₂.obj.obj (op 0)) ⊆
      SheafOfModules.supp (T.X₁.obj.obj (op 0)) ∪
        SheafOfModules.supp (T.X₃.obj.obj (op 0)) := by
  intro x hx
  by_contra hxUnion
  simp only [Set.mem_union, not_or] at hxUnion
  obtain ⟨hxF, hxH⟩ := hxUnion
  set F₀ := T.X₁.obj.obj (op 0)
  set H₀ := T.X₃.obj.obj (op 0)
  have : _root_.SheafOfModules.IsCoherent.{u} F₀ := T.X₁.property.isCoherent 0
  have : _root_.SheafOfModules.IsCoherent.{u} H₀ := T.X₃.property.isCoherent 0
  have : F₀.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType (M := F₀)
  have : H₀.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType (M := H₀)
  let UF : X.Opens := ⟨(SheafOfModules.supp F₀)ᶜ,
    isOpen_compl_iff.mpr (SheafOfModules.isClosed_supp F₀)⟩
  let UH : X.Opens := ⟨(SheafOfModules.supp H₀)ᶜ,
    isOpen_compl_iff.mpr (SheafOfModules.isClosed_supp H₀)⟩
  let U : X.Opens := UF ⊓ UH
  have hxU : x ∈ U.1 := ⟨hxF, hxH⟩
  let : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  let : CompactSpace U :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (U : Set X))
  let : IsNoetherian U.toScheme := AlgebraicGeometry.IsNoetherian.mk
  let R := restrictFunctor I U.ι
  obtain ⟨hlim, hcolim⟩ := (CategoryTheory.exactFunctor_iff R).1 (restrictFunctor_exact I U.ι)
  let : PreservesFiniteLimits R := hlim
  let : PreservesFiniteColimits R := hcolim
  have hmid : IsZero ((T.map R).X₂) := (hT.map R).isZero_of_both_isZero
    (isZero_of_isZero_obj_op_zero (I.comap U.ι) (R.obj T.X₁)
      (isZero_restrictFunctor_obj_of_notMem_supp U F₀ fun y => y.property.1))
    (isZero_of_isZero_obj_op_zero (I.comap U.ι) (R.obj T.X₃)
      (isZero_restrictFunctor_obj_of_notMem_supp U H₀ fun y => y.property.2))
  have hG₀' := isZero_obj_obj_of_isZero (I.comap U.ι) (R.obj T.X₂) hmid 0
  have hG₀x : IsZero ((TopCat.Presheaf.stalkFunctor Ab.{u} x).obj
      ((Scheme.Modules.toPresheaf X).obj (T.X₂.obj.obj (op 0)))) := by
    have h := Functor.map_isZero (TopCat.Presheaf.stalkFunctor Ab.{u} (⟨x, hxU⟩ : U.toScheme))
      (Functor.map_isZero (Scheme.Modules.toPresheaf U.toScheme) hG₀')
    exact h.of_iso
      ((Scheme.Modules.restrictStalkNatIso U.ι (⟨x, hxU⟩ : U.toScheme)).app
        (T.X₂.obj.obj (op 0))).symm
  exact notMem_supp_of_isZero_stalk _ x hG₀x hx

/-- **Right exactness at every level.** For a short exact sequence of coherent adic systems the
component of its second map at any level is a cokernel of the component of its first, so the
sequence of components is exact at its middle term and its second map is levelwise surjective. -/
private lemma exact_app_of_shortExact (T : ShortComplex (CoherentAdicSystems I))
    (hT : T.ShortExact) (n : ℕ) :
    ∃ h : T.f.hom.app (op n) ≫ T.g.hom.app (op n) = 0,
      (ShortComplex.mk _ _ h).Exact ∧ Epi (T.g.hom.app (op n)) := by
  have : Epi T.g := hT.epi_g
  have hzerohom : T.f.hom ≫ T.g.hom = 0 := congrArg InducedCategory.Hom.hom T.zero
  have hzero : T.f.hom.app (op n) ≫ T.g.hom.app (op n) = 0 :=
    congrArg (fun k : T.X₁.obj ⟶ T.X₃.obj => k.app (op n)) hzerohom
  let e : coherentAdicCokernel I T.f ≅ T.X₃ :=
    IsColimit.coconePointUniqueUpToIso (coherentAdicCokernelIsColimit I T.f) hT.exact.gIsCokernel
  have he : coherentAdicCokernelπ I T.f ≫ e.hom = T.g := by
    simpa using IsColimit.comp_coconePointUniqueUpToIso_hom
      (coherentAdicCokernelIsColimit I T.f) hT.exact.gIsCokernel WalkingParallelPair.one
  let eObj : cokernel T.f.hom ≅ T.X₃.obj := (ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso e
  have hehom : cokernel.π T.f.hom ≫ eObj.hom = T.g.hom :=
    congrArg (fun k : T.X₂ ⟶ T.X₃ => k.hom) he
  let φ : cokernel (T.f.hom.app (op n)) ≅ T.X₃.obj.obj (op n) :=
    (cokernelObjIso T.f.hom (op n)).symm ≪≫
      ((evaluation ℕᵒᵖ X.Modules).obj (op n)).mapIso eObj
  have hπ : cokernel.π (T.f.hom.app (op n)) ≫ (cokernelObjIso T.f.hom (op n)).inv =
      (cokernel.π T.f.hom).app (op n) := by
    rw [← app_comp_cokernelObjIso_hom T.f.hom (op n), Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hφ : cokernel.π (T.f.hom.app (op n)) ≫ φ.hom = T.g.hom.app (op n) := by
    have hcomp : φ.hom = (cokernelObjIso T.f.hom (op n)).inv ≫ eObj.hom.app (op n) := rfl
    rw [hcomp, ← Category.assoc, hπ]
    exact congrArg (fun k : T.X₂.obj ⟶ T.X₃.obj => k.app (op n)) hehom
  have hcolim : IsColimit (CokernelCofork.ofπ (T.g.hom.app (op n)) hzero) :=
    IsColimit.ofIsoColimit (cokernelIsCokernel (T.f.hom.app (op n))) (Cofork.ext φ hφ)
  exact ⟨hzero, ShortComplex.exact_of_g_is_cokernel _ hcolim, epi_of_isColimit_cofork hcolim⟩

/-- **The terms of a subobject are quotients of levelwise kernels.** For a short exact sequence of
coherent adic systems, each term of its left-hand system receives an epimorphism from the kernel
of a component of its second map at some level.

A monomorphism of coherent adic systems need not be levelwise injective, so this, rather than an
inclusion into the corresponding term of the ambient system, is how a subobject's terms are
reached: the left-hand system is the kernel, whose terms are the adic quotients of the stable
kernel images, and a stable kernel image is by construction the image of a levelwise kernel at a
high enough level. -/
private lemma exists_epi_kernel_app (T : ShortComplex (CoherentAdicSystems I))
    (hT : T.ShortExact) (n : ℕ) :
    ∃ m : ℕ, ∃ e : kernel (T.g.hom.app (op m)) ⟶ T.X₁.obj.obj (op n), Epi e := by
  have : Mono T.f := hT.mono_f
  obtain ⟨c, hc⟩ := kernelImageQuotients_eventuallyConstant I T.g n
  obtain ⟨eQ, -⟩ := hc (n + c) le_rfl
  let eK : T.X₁ ≅ coherentAdicKernel I T.g :=
    hT.exact.fIsKernel.conePointUniqueUpToIso (coherentAdicKernelIsLimit I T.g)
  let eKn := ((evaluation ℕᵒᵖ X.Modules).obj (op n)).mapIso
    ((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso eK)
  let q := kernel.ι (T.g.hom.app (op (kernelStableLevel I T.g (n + c)))) ≫
    T.X₂.obj.map (homOfLE (le_kernelStableLevel I T.g (n + c))).op
  let qimg : kernel (T.g.hom.app (op (kernelStableLevel I T.g (n + c)))) ⟶
      stableKernelImage I T.g (n + c) :=
    Abelian.factorThruImage q ≫ (Abelian.imageIsoImage q).hom
  have hqimg : Epi qimg :=
    epi_comp' (inferInstance : Epi (Abelian.factorThruImage q))
      (inferInstance : Epi (Abelian.imageIsoImage q).hom)
  refine ⟨kernelStableLevel I T.g (n + c),
    qimg ≫ cokernel.π ((Stacks.Algebraization.idealPowerMultiple I (n + 1)
      (stableKernelImage I T.g (n + c))).ι) ≫ eQ.hom ≫ eKn.inv, ?_⟩
  exact epi_comp' hqimg (epi_comp' coequalizer.π_epi
    (epi_comp' (inferInstance : Epi eQ.hom) (inferInstance : Epi eKn.inv)))

end Levelwise

/-! ### Annihilation of a sheaf of modules by an ideal sheaf -/

section Annihilator

variable {X : Scheme.{u}}

/-- An ideal sheaf annihilates a sheaf of modules exactly when each of its sections over an affine
open kills each section of the module there. -/
private lemma idealPowerMultiple_one_eq_bot_iff (J : X.IdealSheafData) (M : X.Modules) :
    Stacks.Algebraization.idealPowerMultiple J 1 M = ⊥ ↔
      ∀ (U : X.affineOpens) (a : Γ(X, U)), a ∈ J.ideal U → ∀ s : Γ(M, U), a • s = 0 := by
  simp only
    [Stacks.Algebraization.idealPowerMultiple_eq_bot_iff_affine_sections_annihilated, pow_one]

/-- For an exact sequence `M₁ ⟶ M₂ ⟶ M₃` of sheaves of modules, a section of `J` annihilating
`M₁` and a section of `𝒦` annihilating `M₃` have their product annihilating `M₂`.

A section of `M₂` killed by `b` lies, locally, in the image of `M₁`, where `a` kills it. -/
private lemma smul_smul_eq_zero_of_exact (T : ShortComplex X.Modules) (hT : T.Exact)
    (J K : X.IdealSheafData)
    (hJ : Stacks.Algebraization.idealPowerMultiple J 1 T.X₁ = ⊥)
    (hK : Stacks.Algebraization.idealPowerMultiple K 1 T.X₃ = ⊥)
    (U : X.affineOpens) (a : Γ(X, U)) (ha : a ∈ J.ideal U)
    (b : Γ(X, U)) (hb : b ∈ K.ideal U) (s : Γ(T.X₂, U)) :
    a • (b • s) = 0 := by
  classical
  have hbg : b • T.g.app U s = 0 :=
    (idealPowerMultiple_one_eq_bot_iff K T.X₃).mp hK U b hb _
  refine TopCat.Presheaf.IsSheaf.section_ext (U := op U.1) T.X₂.isSheaf fun x hx => ?_
  let G := PresheafOfModules.toPresheaf X.ringCatSheaf.obj
  let H := _root_.SheafOfModules.forget X.ringCatSheaf
  let Q₁ : TopCat.Presheaf AddCommGrpCat X := G.obj (H.obj T.X₁)
  let Q₂ : TopCat.Presheaf AddCommGrpCat X := G.obj (H.obj T.X₂)
  let Q₃ : TopCat.Presheaf AddCommGrpCat X := G.obj (H.obj T.X₃)
  have hxStalk :=
    (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact X.ringCatSheaf T).mp hT x
  let bsUQ : Q₂.obj (op U.1) := b • s
  have hker : (AlgebraicGeometry.SheafOfModules.stalkShortComplex
      X.ringCatSheaf T x).g.hom (Q₂.germ U.1 x hx bsUQ) = 0 := by
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (G.map (H.map T.g)))
      (Q₂.germ U.1 x hx bsUQ) = 0
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U.1 x hx (G.map (H.map T.g)) bsUQ]
    have hsection : (G.map (H.map T.g)).app (op U.1) bsUQ = 0 := by
      change T.g.app U.1 (b • s) = 0
      rw [Scheme.Modules.Hom.app_smul, hbg]
    rw [hsection]
    change ((Q₃.germ U.1 x hx).hom) 0 = 0
    exact (Q₃.germ U.1 x hx).hom.map_zero
  rw [ShortComplex.ab_exact_iff] at hxStalk
  obtain ⟨y, hy⟩ := hxStalk _ hker
  obtain ⟨V, hxV, t, ht⟩ := Q₁.exists_germ_eq y
  have hEq : Q₂.germ U.1 x hx bsUQ = Q₂.germ V x hxV (T.f.app V t) := by
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (G.map (H.map T.f))) y = _ at hy
    rw [← ht, TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV (G.map (H.map T.f)) t] at hy
    exact hy.symm
  obtain ⟨W, hxW, iWU, iWV, hW⟩ := Q₂.germ_eq x hx hxV bsUQ (T.f.app V t) hEq
  obtain ⟨-, ⟨A, hA, rfl⟩, hxA, hAW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.2
  let A' : X.affineOpens := ⟨A, hA⟩
  let jAW : A'.1 ⟶ W := homOfLE (show A'.1 ≤ W from hAW)
  let hAU : A'.1 ≤ U.1 := hAW.trans (leOfHom iWU)
  let qU : (op U.1) ⟶ op A'.1 := (jAW ≫ iWU).op
  let qV : (op V) ⟶ op A'.1 := (jAW ≫ iWV).op
  let aA : Γ(X, A') := (X.ringCatSheaf.obj.map qU).hom a
  let bA : Γ(X, A') := (X.ringCatSheaf.obj.map qU).hom b
  let sA : Γ(T.X₂, A') := T.X₂.presheaf.map qU s
  let tA : Γ(T.X₁, A') := Q₁.map qV t
  have haA : aA ∈ J.ideal A' := by
    have hmem := Ideal.mem_map_of_mem (X.presheaf.map qU).hom ha
    change (X.presheaf.map qU).hom a ∈ J.ideal A'
    rw [← Scheme.IdealSheafData.map_ideal J hAU]
    exact hmem
  have hkill : aA • tA = 0 :=
    (idealPowerMultiple_one_eq_bot_iff J T.X₁).mp hJ A' aA haA _
  have hEqA : bA • sA = T.f.app A' tA := by
    have hWA := congrArg (Q₂.map jAW.op) hW
    have hWA' : (T.X₂.presheaf.map qU) (b • s) = (T.X₂.presheaf.map qV) (T.f.app V t) := by
      convert hWA using 1 <;>
        (try simp only [qU, qV, op_comp, Functor.map_comp,
          AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]) <;> rfl
    calc
      bA • sA = (T.X₂.presheaf.map qU) (b • s) := by
        change (X.presheaf.map qU).hom b • (T.X₂.presheaf.map qU) s =
          (T.X₂.presheaf.map qU) (b • s)
        exact (Scheme.Modules.map_smul T.X₂ (jAW ≫ iWU) b s).symm
      _ = (T.X₂.presheaf.map qV) (T.f.app V t) := hWA'
      _ = T.f.app A' tA := by
        change (T.X₂.presheaf.map qV) (T.f.app V t) = T.f.app A' (Q₁.map qV t)
        exact (NatTrans.naturality_apply (T.f.mapPresheaf) qV t).symm
  have hzeroA : aA • (bA • sA) = 0 := by
    rw [hEqA, ← Scheme.Modules.Hom.app_smul, hkill, map_zero]
  refine ⟨A'.1, hAU, hxA, ?_⟩
  change T.X₂.presheaf.map (homOfLE hAU).op (a • (b • s)) =
    T.X₂.presheaf.map (homOfLE hAU).op 0
  simpa [aA, bA, sA, Scheme.Modules.map_smul, hzeroA]

/-- An ideal sheaf annihilates a zero sheaf of modules. -/
private lemma idealPowerMultiple_eq_bot_of_isZero (J : X.IdealSheafData) (M : X.Modules)
    (hM : IsZero M) : Stacks.Algebraization.idealPowerMultiple J 1 M = ⊥ := by
  refine (idealPowerMultiple_one_eq_bot_iff J M).2 fun U a _ s => ?_
  let E := _root_.SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  let : E.PreservesZeroMorphisms := ⟨by intros; ext; rfl⟩
  exact (ModuleCat.isZero_iff_subsingleton.mp (E.map_isZero hM)).elim _ _

/-- For an exact sequence `M₁ ⟶ M₂ ⟶ M₃` of sheaves of modules, the product of an ideal sheaf
annihilating `M₁` and one annihilating `M₃` annihilates `M₂`. -/
private lemma idealPowerMultiple_mul_eq_bot_of_exact (T : ShortComplex X.Modules) (hT : T.Exact)
    (J K : X.IdealSheafData)
    (hJ : Stacks.Algebraization.idealPowerMultiple J 1 T.X₁ = ⊥)
    (hK : Stacks.Algebraization.idealPowerMultiple K 1 T.X₃ = ⊥) :
    Stacks.Algebraization.idealPowerMultiple (J * K) 1 T.X₂ = ⊥ := by
  refine (idealPowerMultiple_one_eq_bot_iff _ _).2 fun U a ha s => ?_
  change a ∈ J.ideal U * K.ideal U at ha
  refine Submodule.mul_induction_on ha ?_ ?_
  · intro a ha b hb
    simpa only [mul_smul] using smul_smul_eq_zero_of_exact T hT J K hJ hK U a ha b hb s
  · intro a b ha hb
    simp only [add_smul, ha, hb, add_zero]

/-- Annihilation by an ideal sheaf passes to quotients. -/
private lemma idealPowerMultiple_eq_bot_of_epi (J : X.IdealSheafData) {M N : X.Modules}
    (p : M ⟶ N) [Epi p] (hM : Stacks.Algebraization.idealPowerMultiple J 1 M = ⊥) :
    Stacks.Algebraization.idealPowerMultiple J 1 N = ⊥ := by
  have hT : (ShortComplex.mk p (0 : N ⟶ 0) (by simp)).Exact :=
    (ShortComplex.exact_iff_epi _ rfl).2 inferInstance
  simpa using idealPowerMultiple_mul_eq_bot_of_exact _ hT J ⊤ hM
    (idealPowerMultiple_eq_bot_of_isZero ⊤ _ (isZero_zero _))

/-- Annihilation by an ideal sheaf passes to subobjects. -/
private lemma idealPowerMultiple_eq_bot_of_mono (J : X.IdealSheafData) {M N : X.Modules}
    (i : M ⟶ N) [Mono i] (hN : Stacks.Algebraization.idealPowerMultiple J 1 N = ⊥) :
    Stacks.Algebraization.idealPowerMultiple J 1 M = ⊥ := by
  have hT : (ShortComplex.mk (0 : 0 ⟶ M) i (by simp)).Exact :=
    (ShortComplex.exact_iff_mono _ rfl).2 inferInstance
  simpa using idealPowerMultiple_mul_eq_bot_of_exact _ hT ⊤ J
    (idealPowerMultiple_eq_bot_of_isZero ⊤ _ (isZero_zero _)) hN

end Annihilator

/-! ### Properness of a closed subscheme and of its closed subset -/

section Proper

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (J : X.IdealSheafData)

/-- A closed subscheme whose closed subset is proper over the base is proper over the base. -/
private lemma isProper_subschemeι_comp (h : IsProperOver f J.support) :
    IsProper (J.subschemeι ≫ f) :=
  (exists_isProper_iff_forall_isProper f J.support).1
    ((isProperOver_iff_exists_isProper f J.support).1 h) J rfl

/-- The closed subset of a closed subscheme proper over the base is proper over the base. -/
private lemma isProperOver_support (h : IsProper (J.subschemeι ≫ f)) :
    IsProperOver f J.support :=
  (isProperOver_iff_exists_isProper f J.support).2 ⟨J, rfl, h⟩

end Proper

/-! ### Systems whose first term has support proper over the base -/

/-- **[Stacks, Tag 0CYV], part (1).** The coherent adic systems along `ℐ` whose first term has
support proper over `S` form a Serre subcategory of `Coh(X, ℐ)`.

All terms of a coherent adic system have the same support, and the support of the middle term of a
short exact sequence is the union of the supports of the outer two, which is proper over `S`
because a finite union of closed subsets proper over the base is proper over the base. -/
@[stacks 0CYV "proper support"]
public theorem isSerreClass_hasProperSupport {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (I : X.IdealSheafData) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    letI : IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
    ObjectProperty.IsSerreClass (C := CoherentAdicSystems I)
      (fun F => Stacks.Algebraization.HasProperSupport f (F.obj.obj (op 0))) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
  set P : ObjectProperty (CoherentAdicSystems I) :=
    fun F => Stacks.Algebraization.HasProperSupport f (F.obj.obj (op 0)) with hP
  have hzero : P 0 := by
    have hlevel := isZero_obj_obj_of_isZero I 0 (isZero_zero _) 0
    have hsupp : SheafOfModules.supp ((0 : CoherentAdicSystems I).obj.obj (op 0)) = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun x => notMem_supp_of_isZero_stalk _ x
        (Functor.map_isZero (TopCat.Presheaf.stalkFunctor Ab.{u} x)
          (Functor.map_isZero (TopCat.Sheaf.forget Ab.{u} X)
            (Functor.map_isZero (SheafOfModules.toSheaf X.ringCatSheaf) hlevel)))
    exact ⟨⊥, by rw [hsupp]; rfl, isProperOver_bot f⟩
  refine (ObjectProperty.isSerreClass_iff_prop_X₂_of_exact P).2 ⟨⟨0, hzero⟩, ?_⟩
  intro T hT h₁ h₃
  obtain ⟨Z₁, hZ₁, hP₁⟩ := h₁
  obtain ⟨Z₃, hZ₃, hP₃⟩ := h₃
  have : _root_.SheafOfModules.IsCoherent.{u} (T.X₂.obj.obj (op 0)) := T.X₂.property.isCoherent 0
  have : (T.X₂.obj.obj (op 0)).IsFiniteType :=
    _root_.SheafOfModules.IsCoherent.isFiniteType (M := T.X₂.obj.obj (op 0))
  have hsup : IsProperOver f (Z₁ ⊔ Z₃) := isProperOver_sup f Z₁ Z₃ hP₁ hP₃
  refine ⟨⟨SheafOfModules.supp (T.X₂.obj.obj (op 0)),
    SheafOfModules.isClosed_supp _⟩, rfl, isProperOver_of_le f ?_ hsup⟩
  change SheafOfModules.supp (T.X₂.obj.obj (op 0)) ⊆ ((Z₁ ⊔ Z₃ : Closeds X) : Set X)
  simpa [hZ₁, hZ₃] using supp_middle_subset_of_exact I T hT

/-! ### Systems with a common annihilating closed subscheme proper over the base -/

/-- A coherent adic system has a *proper annihilator* when the ideal sheaf of some closed
subscheme of `X` proper over `S` annihilates every one of its terms. -/
public def HasProperAnnihilator {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (I : X.IdealSheafData) : ObjectProperty (CoherentAdicSystems I) :=
  fun F => ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧
    ∀ n : ℕ, Stacks.Algebraization.idealPowerMultiple J 1 (F.obj.obj (op n)) = ⊥

/-- **[Stacks, Tag 0CYV], part (2).** The coherent adic systems along `ℐ` admitting a closed
subscheme of `X` proper over `S` whose ideal sheaf annihilates every term form a Serre subcategory
of `Coh(X, ℐ)`.

An ideal sheaf annihilating every term of a system annihilates every term of a subobject and of a
quotient; for an extension the product of the two ideal sheaves works, and the closed subset it
cuts out is the union of the two, which is again proper over `S`. -/
@[stacks 0CYV "common proper annihilator"]
public theorem isSerreClass_hasProperAnnihilator {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (I : X.IdealSheafData) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    letI : IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
    (HasProperAnnihilator f I).IsSerreClass := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
  let : (HasProperAnnihilator f I).ContainsZero := ⟨0, isZero_zero _, by
    refine ⟨⊤, isProper_subschemeι_comp f ⊤ ?_, fun n => ?_⟩
    · rw [Scheme.IdealSheafData.support_top]
      exact isProperOver_bot f
    · exact idealPowerMultiple_eq_bot_of_isZero ⊤ _
        (isZero_obj_obj_of_isZero I 0 (isZero_zero _) n)⟩
  let : (HasProperAnnihilator f I).IsClosedUnderSubobjects := ⟨by
    intro A B i _ hB
    obtain ⟨J, hJ, hann⟩ := hB
    refine ⟨J, hJ, fun n => ?_⟩
    have hT : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
      ⟨ShortComplex.exact_cokernel i⟩
    obtain ⟨m, e, he⟩ := exists_epi_kernel_app I _ hT n
    have := he
    exact idealPowerMultiple_eq_bot_of_epi J e
      (idealPowerMultiple_eq_bot_of_mono J (kernel.ι ((cokernel.π i).hom.app (op m))) (hann m))⟩
  let : (HasProperAnnihilator f I).IsClosedUnderQuotients := ⟨by
    intro A B p _ hA
    obtain ⟨J, hJ, hann⟩ := hA
    refine ⟨J, hJ, fun n => ?_⟩
    have hT : (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact :=
      ⟨ShortComplex.exact_kernel p⟩
    obtain ⟨-, -, he⟩ := exact_app_of_shortExact I _ hT n
    have := he
    exact idealPowerMultiple_eq_bot_of_epi J (p.hom.app (op n)) (hann n)⟩
  let : (HasProperAnnihilator f I).IsClosedUnderExtensions := ⟨by
    intro T hT hG hH
    obtain ⟨JG, hJG, hAnnG⟩ := hG
    obtain ⟨JH, hJH, hAnnH⟩ := hH
    refine ⟨JG * JH, isProper_subschemeι_comp f _ ?_, fun n => ?_⟩
    · rw [Scheme.IdealSheafData.support_mul]
      exact isProperOver_sup f _ _ (isProperOver_support f JG hJG)
        (isProperOver_support f JH hJH)
    · obtain ⟨hzero, hexact, -⟩ := exact_app_of_shortExact I T hT n
      exact idealPowerMultiple_mul_eq_bot_of_exact (ShortComplex.mk _ _ hzero) hexact
        JG JH (hAnnG n) (hAnnH n)⟩
  exact ObjectProperty.IsSerreClass.mk

end Stacks.Coherent

end
