module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalNonzerodivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocusTagInjectivity
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.TorsionFreeRealization
public import StacksFrontier.Topology.Sheaves.Modules.PrincipalAdicLimitFinite
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietorisAndLimits.PrincipalAdicNonzerodivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Mono
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Depth
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel

/-!
# The comparison map at a principal formal locus, for a torsion-free module

Let `A` be a Noetherian ring, `f ∈ A`, `𝔞 ⊆ A` an ideal, `U = Spec(A) ∖ V(𝔞)` and `G` a coherent
`𝒪_U`-module. This file proves that the comparison map of Stacks 0EG2,

`colim_V Γ(V, G) ⟶ lim Γ(U, G / fⁿ G)`,

the colimit running over the opens `V ⊆ U` containing `U ∩ V(f)`, is an isomorphism as soon as
`A` is `f`-adically complete, no associated point of `G` lies in `V(f)` (so that `G` is
`f`-torsion free), and `Γ(U, G / fG)` is a finite `A`-module — the last condition being asked in
the form that the direct image of `G / fG` to `Spec A` is coherent. This is the sheaf form of the
argument of Stacks 0EIH, and it is the step of the first proof of Stacks 0H49 that settles the
modified module `F'` there.

## The argument

Injectivity is `Stacks.Algebraization.mono_comparisonMap`. For surjectivity:

* The quotients `G / f^(n+1) G` form a principal-adic inverse system in the sense of Stacks 0BLB
  (`complementAdicSystem`): condition (1) of Stacks 0H39 holds because the system is realized by
  the torsion-free module `G` itself. So the limit `N` of their global sections is a finite
  `A`-module, and the kernel of its first projection is `f N`.
* The tower `G / Iⁿ G` of ideal-power quotients for `I = (f) 𝒪_U`, which is what the comparison
  map is built from, is identified with the tower of cokernels of the powers of multiplication
  by `f` (`exists_quotientSystemNearVanishing_iso_powQuotient`).
* At a point `x` of `U ∩ V(f)`, every element of `N` is, up to an element of `A` outside the
  prime of `x`, the reduction of a global section of `G` plus a multiple of `f`
  (`exists_smul_mem_range_complementReduction_sup`). This uses that the germs of a
  quasi-coherent module on the quasi-compact `U` are fractions of global sections
  (`exists_smul_eq_germ`, `exists_smul_eq_zero_of_germ_eq_zero`). Nakayama's lemma at the prime of
  `x` removes the multiple of `f` (`exists_smul_eq_complementReduction`).
* Hence the ideal of those `c ∈ A` for which `c x` is the reduction of a global section is not
  contained in the prime of any point of `U ∩ V(f)`. Finitely many generators `cᵢ` of it give local
  solutions `cᵢ⁻¹ mᵢ` on the basic opens of the `cᵢ`; on the overlaps they differ by sections
  whose reductions all vanish, which vanish near `U ∩ V(f)` by Krull's intersection theorem, so
  the local solutions glue on a neighbourhood of the formal locus
  (`exists_section_complementProj_eq`).

## Main results

* `Stacks.Algebraization.isIso_comparisonMap_span_singleton_of_isCoherent_pushforward` — the
  comparison map is an isomorphism for an `f`-torsion-free coherent module whose quotient by `f`
  has coherent direct image to `Spec A`.
* `Stacks.Algebraization.exists_section_complementProj_eq` — every formal section is realized by
  a section on a neighbourhood of `U ∩ V(f)`.
* `Stacks.Algebraization.exists_smul_mem_of_forall_exists_smul_mem_sup` — Nakayama's lemma in the
  form used here.

## References

* [Stacks Project, Tag 0EIH](https://stacks.math.columbia.edu/tag/0EIH)
* [Stacks Project, Tag 0H49](https://stacks.math.columbia.edu/tag/0H49)
* [Stacks Project, Tag 0BLB](https://stacks.math.columbia.edu/tag/0BLB)
* [Stacks Project, Tag 0H39](https://stacks.math.columbia.edu/tag/0H39)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology
open Stacks.SheafOfModules (scalarAt scalarAt_apply)
open Stacks.Cohomology.InverseSystems.TorsionFreeDivisible

/-! ### A form of Nakayama's lemma -/

/-- **Nakayama's lemma, localized at a prime.** Let `M` be a finite module over a commutative
ring `R`, `P ⊆ M` a submodule, `𝔭` a prime and `f ∈ 𝔭`. If every element of `M` lies in
`P + fM` after multiplication by an element outside `𝔭`, then every element of `M` lies in `P`
after multiplication by an element outside `𝔭`: the localization of `M ⧸ P` at `𝔭` is a finite
module equal to its product with the maximal ideal, hence zero. -/
theorem exists_smul_mem_of_forall_exists_smul_mem_sup {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (p : Ideal R) [p.IsPrime]
    (P : Submodule R M) {f : R} (hf : f ∈ p)
    (h : ∀ y : M, ∃ s ∉ p, s • y ∈ P ⊔ LinearMap.range (LinearMap.lsmul R M f)) (x : M) :
    ∃ s ∉ p, s • x ∈ P := by
  let Q := M ⧸ P
  let L := LocalizedModule p.primeCompl Q
  let Rp := Localization.AtPrime p
  have hsub : Subsingleton L := by
    have htop : (⊤ : Submodule Rp L) ≤ IsLocalRing.maximalIdeal Rp • ⊤ := by
      intro ℓ _
      induction ℓ using LocalizedModule.induction_on with
      | h q t =>
        obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective P q
        obtain ⟨s, hs, hsy⟩ := h y
        obtain ⟨w, hw, z, ⟨y', rfl⟩, hsum⟩ := Submodule.mem_sup.1 hsy
        have hfm : algebraMap R Rp f ∈ IsLocalRing.maximalIdeal Rp := by
          rwa [IsLocalization.AtPrime.to_map_mem_maximal_iff Rp p]
        have hq : (⟨s, hs⟩ : p.primeCompl) • P.mkQ y = f • P.mkQ y' := by
          change P.mkQ (s • y) = P.mkQ (f • y')
          rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          have : s • y - f • y' = w := by
            rw [← hsum]
            simp
          rw [this]
          exact hw
        have key : LocalizedModule.mk (P.mkQ y) t =
            algebraMap R Rp f • LocalizedModule.mk (P.mkQ y') (⟨s, hs⟩ * t) := by
          rw [algebraMap_smul, LocalizedModule.smul'_mk, ← hq,
            LocalizedModule.mk_cancel_common_left]
        rw [key]
        exact Submodule.smul_mem_smul hfm Submodule.mem_top
    have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal Rp) ⊤
      (Module.Finite.fg_top) htop (IsLocalRing.maximalIdeal_le_jacobson _)
    exact subsingleton_of_forall_eq 0 fun ℓ => (Submodule.mem_bot Rp).1 (hbot ▸ Submodule.mem_top)
  obtain ⟨r, hr, hrx⟩ := LocalizedModule.subsingleton_iff.1 hsub (P.mkQ x)
  refine ⟨r, hr, ?_⟩
  rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hrx

/-- The rings of sections of the structure sheaf of a scheme, read as objects of `RingCat`, are
commutative. Instance search does not find this through the `CommRingCat` structure of
`Γ(X, U)`, and `Stacks.SheafOfModules.terminalSectionToEnd` needs it. -/
local instance mulCommutativeRingCatSheafOfScheme (X : Scheme.{u}) (U : (X.Opens)ᵒᵖ) :
    IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  ⟨⟨fun a b => mul_comm (G := Γ(X, U.unop)) a b⟩⟩

/-- A section that vanishes on an open vanishes on every smaller open. -/
private theorem presheaf_map_eq_zero_of_le {X : Scheme.{u}} {H : X.Modules} {Z Z' Z'' : X.Opens}
    {s : Γ(H, Z)} (k : Z'' ⟶ Z') (i : Z' ⟶ Z) (j : Z'' ⟶ Z) (hs : H.presheaf.map i.op s = 0) :
    H.presheaf.map j.op s = 0 := by
  rw [Subsingleton.elim j (k ≫ i), op_comp, H.presheaf.map_comp_apply, hs, map_zero]

/-- Naturality of a morphism of modules with respect to restriction of sections. -/
private theorem presheaf_map_app_apply {X : Scheme.{u}} {G K : X.Modules} (ψ : G ⟶ K)
    {Z Z' : X.Opens} (h : Z' ⟶ Z) (w : Γ(G, Z)) :
    K.presheaf.map h.op (ConcreteCategory.hom (Scheme.Modules.Hom.app ψ Z) w) =
      ConcreteCategory.hom (Scheme.Modules.Hom.app ψ Z') (G.presheaf.map h.op w) :=
  (ConcreteCategory.congr_hom (ψ.mapPresheaf.naturality h.op) w).symm

/-- An isomorphism of modules is injective on sections over every open. -/
private theorem injective_app_hom_of_iso {X : Scheme.{u}} {G K : X.Modules} (e : G ≅ K)
    (V : X.Opens) : Function.Injective (ConcreteCategory.hom (Scheme.Modules.Hom.app e.hom V)) :=
  Function.LeftInverse.injective (g := ConcreteCategory.hom (Scheme.Modules.Hom.app e.inv V))
    fun w => congrArg (fun φ => ConcreteCategory.hom (Scheme.Modules.Hom.app φ V) w) e.hom_inv_id

/-- The quotient `G / g⁰ G` has no nonzero sections. -/
private theorem subsingleton_sections_powQuotient_zero {X : Scheme.{u}}
    (g : End (𝟭 (SheafOfModules.{u} X.ringCatSheaf))) (G : X.Modules) (V : X.Opens) :
    Subsingleton Γ(powQuotient g G 0, V) := by
  have : Epi ((g ^ 0).asHom.app G) := by rw [pow_zero]; exact (inferInstance : Epi (𝟙 G))
  have hz : IsZero (powQuotient g G 0) := isZero_cokernel_of_epi _
  have hzero : ∀ w : Γ(powQuotient g G 0, V), w = 0 := fun w =>
    (congrArg (fun φ => ConcreteCategory.hom (Scheme.Modules.Hom.app φ V) w)
      (hz.eq_of_src (𝟙 _) 0)).trans rfl
  exact ⟨fun u v => (hzero u).trans (hzero v).symm⟩

section Scalars

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (a : Ideal A)

omit [IsNoetherianRing A] in
/-- A point of `U` lies in the basic open of the image of `s ∈ A` exactly when `s` is not in
its prime. -/
theorem mem_basicOpen_complementScalar_iff (x : (complementZeroLocus A a : Scheme)) (s : A) :
    x ∈ (complementZeroLocus A a : Scheme).basicOpen (complementTopScalars a s) ↔
      s ∉ x.1.asIdeal := by
  change x ∈ (complementZeroLocus A a : Scheme).basicOpen
      ((complementZeroLocus A a).ι.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv s)) ↔ _
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  exact Iff.rfl

omit [IsNoetherianRing A] in
/-- The germ at `x` of the image of `s ∈ A` is a unit when `s` is not in the prime of `x`. -/
theorem isUnit_germ_complementScalar (x : (complementZeroLocus A a : Scheme)) (s : A)
    (hs : s ∉ x.1.asIdeal) :
    IsUnit ((complementZeroLocus A a : Scheme).presheaf.germ ⊤ x trivial
      (complementTopScalars a s)) :=
  ((complementZeroLocus A a : Scheme).mem_basicOpen (complementTopScalars a s) x trivial).1
    ((mem_basicOpen_complementScalar_iff A a x s).2 hs)

omit [IsNoetherianRing A] in
/-- The local scalar of multiplication by `f` over `U` is the image of `f`. -/
theorem scalarAt_complementScalar_top (f : A) :
    scalarAt ((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a :
        Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))) ⊤ =
      complementTopScalars a f := by
  rw [scalarAt_apply]
  change ConcreteCategory.hom ((complementZeroLocus A a : Scheme).ringCatSheaf.obj.map
      (isTerminalTop.from (⊤ : (complementZeroLocus A a : Scheme).Opens)).op)
      (complementTopScalars a f) * 1 = _
  have h1 : (isTerminalTop.from (⊤ : (complementZeroLocus A a : Scheme).Opens)).op = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [h1, CategoryTheory.Functor.map_id, mul_one]
  rfl

omit [IsNoetherianRing A] in
/-- For a principal ideal the ideal sheaf `(f) 𝒪_U` of the formal locus is the principal ideal
sheaf generated by the scalar through which multiplication by `f` acts. -/
theorem idealSheafNearVanishing_span_singleton_eq_scalarIdealData (f : A) :
    idealSheafNearVanishing A (Ideal.span
        {f}) a = scalarIdealData ((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A
        a : Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))) := by
  change Scheme.IdealSheafData.ofIdealTop _ = Scheme.IdealSheafData.ofIdealTop _
  congr 1
  rw [scalarAt_complementScalar_top]
  change Ideal.map _ (Ideal.span {f}) = _
  rw [Ideal.map_span, Set.image_singleton]

omit [IsNoetherianRing A] in
/-- On the stalk at `x`, multiplication by `f` is multiplication by the germ of its image, the
stalk being a `Γ(U, 𝒪_U)`-module through the germ map. -/
theorem stalk_complementScalar_apply (f : A) (G : (complementZeroLocus A a : Scheme).Modules)
    (x : (complementZeroLocus A a : Scheme)) (z : G.presheaf.stalk x) :
    letI := affineStalkModule G ⊤ x trivial
    ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      (Scheme.Modules.Hom.mapPresheaf (((Stacks.SheafOfModules.terminalSectionToEnd
          (complementZeroLocus A a : Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a
          f))).asHom.app G))) z =
        complementTopScalars a f • z := by
  let := affineStalkModule G ⊤ x trivial
  let : Module ((complementZeroLocus A a : Scheme).presheaf.stalk x) (G.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := (complementZeroLocus A a : Scheme).presheaf) G.val x
  obtain ⟨V, hxV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf z
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV _ t).trans ?_
  have e1 : ConcreteCategory.hom (Scheme.Modules.Hom.app
      (((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a : Scheme).ringCatSheaf
      ⊤ isTerminalTop (complementTopScalars a f))).asHom.app G) V) t =
      scalarAt ((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a :
          Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))) V • t :=
    Stacks.SheafOfModules.scalarActionLocal _ G V t
  have e2 : scalarAt ((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a :
      Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))) V =
      (complementZeroLocus A a : Scheme).presheaf.map (homOfLE le_top).op
        (complementTopScalars a f) := by
    rw [Stacks.SheafOfModules.scalarAt_res _ (homOfLE (le_top : V ≤ ⊤)),
      scalarAt_complementScalar_top]
  change G.presheaf.germ V x hxV
      (ConcreteCategory.hom (Scheme.Modules.Hom.app (((Stacks.SheafOfModules.terminalSectionToEnd
          (complementZeroLocus A a : Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a
          f))).asHom.app G) V) t) = _
  rw [e1, e2]
  refine (PresheafOfModules.germ_smul G.val x V hxV _ t).trans ?_
  change _ = (complementZeroLocus A a : Scheme).presheaf.germ ⊤ x trivial
    (complementTopScalars a f) • G.presheaf.germ V x hxV t
  congr 1
  exact (complementZeroLocus A a : Scheme).presheaf.germ_res_apply (homOfLE le_top) x hxV _

omit [IsNoetherianRing A] in
/-- Multiplication by `f` is injective on the stalk at a point whose prime does not contain
`f`: there it is multiplication by a unit of the local ring. -/
theorem injective_stalk_complementMul (f : A) (G : (complementZeroLocus A a : Scheme).Modules)
    (x : (complementZeroLocus A a : Scheme)) (hx : f ∉ x.1.asIdeal) :
    Function.Injective (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      (Scheme.Modules.Hom.mapPresheaf (((Stacks.SheafOfModules.terminalSectionToEnd
          (complementZeroLocus A a : Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a
          f))).asHom.app G))) :
        G.presheaf.stalk x → G.presheaf.stalk x) := by
  let := affineStalkModule G ⊤ x trivial
  let : Module ((complementZeroLocus A a : Scheme).presheaf.stalk x) (G.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := (complementZeroLocus A a : Scheme).presheaf) G.val x
  intro (z : G.presheaf.stalk x) (w : G.presheaf.stalk x) hzw
  have h : (complementZeroLocus A a : Scheme).presheaf.germ ⊤ x trivial
        (complementTopScalars a f) • z =
      (complementZeroLocus A a : Scheme).presheaf.germ ⊤ x trivial
        (complementTopScalars a f) • w :=
    (stalk_complementScalar_apply A a f G x z).symm.trans
      (hzw.trans (stalk_complementScalar_apply A a f G x w))
  obtain ⟨c, hc⟩ := isUnit_germ_complementScalar A a x f hx
  rw [← hc] at h
  have key : ∀ y : G.presheaf.stalk x,
      y = (↑c⁻¹ : (complementZeroLocus A a : Scheme).presheaf.stalk x) •
        ((c : (complementZeroLocus A a : Scheme).presheaf.stalk x) • y) := fun y => by
    rw [smul_smul, Units.inv_mul, one_smul]
  rw [key z, key w, h]

/-- A module on `U` none of whose associated points lies in `V(f)` is `f`-torsion free:
multiplication by `f` is a monomorphism. -/
theorem mono_complementMul_app (f : A) (G : (complementZeroLocus A a : Scheme).Modules)
    [G.IsQuasicoherent]
    (hAss : ∀ x ∈ Stacks.Divisors.associatedPoints G, f ∉ x.1.asIdeal) :
    Mono (((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a :
        Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))).asHom.app G) := by
  refine mono_of_stalk_injective_on_weaklyAssociatedPoints (F := G) (G := G) _ fun x => ?_
  by_cases hx : x ∈ Stacks.Divisors.weaklyAssociatedPoints G
  · rw [← associatedPoints_eq_weaklyAssociatedPoints] at hx
    exact Or.inl (injective_stalk_complementMul A a f G x (hAss x hx))
  · exact Or.inr hx

/-! ### Germs of global sections on `U` -/

/-- A global section of a quasi-coherent module on `U` whose germ at `x` vanishes is killed by
an element of `A` outside the prime of `x`. The direct image to `Spec A` is quasi-coherent, `U`
being quasi-compact, and there the statement is the affine one. -/
theorem exists_smul_eq_zero_of_germ_eq_zero (G : (complementZeroLocus A a : Scheme).Modules)
    [G.IsQuasicoherent] (s : Γ(G, ⊤)) (x : (complementZeroLocus A a : Scheme))
    (h : G.presheaf.germ ⊤ x trivial s = 0) :
    ∃ b : A, b ∉ x.1.asIdeal ∧ complementTopScalars a b • s = 0 := by
  have : QuasiCompact (complementZeroLocus A a).ι := quasiCompact_U_ι (⟨A, a, a, le_rfl⟩)
  let j := (complementZeroLocus A a).ι
  let H := (Scheme.Modules.pushforward j).obj G
  obtain ⟨V, hxV, iU, iV, hres⟩ :=
    G.presheaf.germ_eq (U := ⊤) (V := ⊤) x trivial trivial s 0 (h.trans (map_zero _).symm)
  have hV0 : G.presheaf.map iU.op s = 0 := hres.trans (map_zero _)
  have hle : j ⁻¹ᵁ (j ''ᵁ V) ≤ V := (j.preimage_image_eq V).le
  have hH : H.presheaf.map (homOfLE (le_top : j ''ᵁ V ≤ ⊤)).op s = 0 := by
    rw [Scheme.Modules.pushforward_obj_presheaf_map]
    exact presheaf_map_eq_zero_of_le (homOfLE hle) iU _ hV0
  have hgerm : H.presheaf.germ ⊤ (j x) trivial s = 0 := by
    rw [← H.presheaf.germ_res_apply (homOfLE le_top) (j x)
      ((j.apply_mem_image_iff).2 hxV) s, hH, map_zero]
  obtain ⟨b, hb, hbs⟩ := (germ_eq_zero_iff_exists_smul_eq_zero H s (j x)).1 hgerm
  refine ⟨b, hb, ?_⟩
  have e : (⊤ : (Spec (CommRingCat.of A)).Opens).leTop.op = 𝟙 _ := Subsingleton.elim _ _
  have hbs' :=
    (Scheme.Modules.smul_Spec_def (M := H) (U := ⊤) b (show Γ(H, ⊤) from s)).symm.trans hbs
  rwa [e, CategoryTheory.Functor.map_id] at hbs'

/-- Every element of the stalk at `x` of a quasi-coherent module on `U` becomes the germ of a
global section after multiplication by an element of `A` outside the prime of `x`. As for
`exists_smul_eq_zero_of_germ_eq_zero`, this is the affine statement for the direct image to
`Spec A`. -/
theorem exists_smul_eq_germ (G : (complementZeroLocus A a : Scheme).Modules)
    [G.IsQuasicoherent] (x : (complementZeroLocus A a : Scheme)) (z : G.presheaf.stalk x) :
    letI := affineStalkModule G ⊤ x trivial
    ∃ b : A, b ∉ x.1.asIdeal ∧ ∃ m : Γ(G, ⊤),
      complementTopScalars a b • z = G.presheaf.germ ⊤ x trivial m := by
  let := affineStalkModule G ⊤ x trivial
  let : Module ((complementZeroLocus A a : Scheme).presheaf.stalk x) (G.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := (complementZeroLocus A a : Scheme).presheaf) G.val x
  have : QuasiCompact (complementZeroLocus A a).ι := quasiCompact_U_ι (⟨A, a, a, le_rfl⟩)
  let j := (complementZeroLocus A a).ι
  let H := (Scheme.Modules.pushforward j).obj G
  let : Module ((Spec (CommRingCat.of A)).presheaf.stalk (j x)) (H.presheaf.stalk (j x)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := (Spec (CommRingCat.of A)).presheaf) H.val (j x)
  obtain ⟨V, hxV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf z
  let W := j ''ᵁ V
  have hyW : j x ∈ W := (j.apply_mem_image_iff).2 hxV
  have hle : j ⁻¹ᵁ W ≤ V := (j.preimage_image_eq V).le
  let tG : Γ(G, j ⁻¹ᵁ W) := G.presheaf.map (homOfLE hle).op t
  let t' : Γ(H, W) := tG
  obtain ⟨b, hb, m, hm⟩ := spec_exists_global_multiple H (j x) (H.presheaf.germ W (j x) hyW t')
  refine ⟨b, hb, m, ?_⟩
  let c : Γ(Spec (CommRingCat.of A), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv b
  let cW : Γ(Spec (CommRingCat.of A), W) :=
    (Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op c
  have hm' : H.presheaf.germ W (j x) hyW (cW • t') = H.presheaf.germ ⊤ (j x) trivial m := by
    refine (PresheafOfModules.germ_smul H.val (j x) W hyW cW t').trans (Eq.trans ?_ hm)
    congr 1
    exact (Spec (CommRingCat.of A)).presheaf.germ_res_apply (homOfLE le_top) (j x) hyW c
  obtain ⟨W', hyW', iW, iT, heq⟩ :=
    H.presheaf.germ_eq (U := W) (V := ⊤) (j x) hyW trivial (cW • t') m hm'
  have hxW' : x ∈ j ⁻¹ᵁ W' := hyW'
  have heq' := congrArg (G.presheaf.germ (j ⁻¹ᵁ W') x hxW') heq
  rw [Scheme.Modules.pushforward_obj_presheaf_map, Scheme.Modules.pushforward_obj_presheaf_map]
    at heq'
  have heq'' := ((G.presheaf.germ_res_apply ((Opens.map j.base).map iW) x hxW' (cW • t')).symm.trans
    heq').trans (G.presheaf.germ_res_apply ((Opens.map j.base).map iT) x hxW' m)
  refine Eq.trans ?_ heq''
  change (complementZeroLocus A a : Scheme).presheaf.germ ⊤ x trivial (j.appTop c) •
      G.presheaf.germ V x hxV t =
        G.presheaf.germ (j ⁻¹ᵁ W) x hyW (j.app W cW • tG)
  refine Eq.trans ?_ (PresheafOfModules.germ_smul G.val x (j ⁻¹ᵁ W) hyW _ tG).symm
  congr 1
  · have hnat : j.app W cW = (complementZeroLocus A a : Scheme).presheaf.map
        ((Opens.map j.base).map (homOfLE (le_top : W ≤ ⊤))).op (j.app ⊤ c) := by
      change ConcreteCategory.hom ((Spec (CommRingCat.of A)).presheaf.map
          (homOfLE (le_top : W ≤ ⊤)).op ≫ j.app W) c = _
      rw [j.naturality]
      rfl
    change (complementZeroLocus A a : Scheme).presheaf.germ ⊤ x trivial (j.app ⊤ c) =
      (complementZeroLocus A a : Scheme).presheaf.germ (j ⁻¹ᵁ W) x hyW (j.app W cW)
    rw [hnat]
    exact ((complementZeroLocus A a : Scheme).presheaf.germ_res_apply _ x hyW _).symm
  · exact (G.presheaf.germ_res_apply (homOfLE hle) x hyW t).symm

/-! ### The inverse system of the quotients `G / fⁿ G` -/

omit [IsNoetherianRing A] in
/-- The quotients `G / f^(n+1) G` of an `f`-torsion-free module satisfy condition (1) of Stacks
0H39: they are realized by the torsion-free module `G` itself, which is condition (4). -/
theorem condition1_powQuotient (f : A) (G : (complementZeroLocus A a : Scheme).Modules)
    (hG : Mono (((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a :
        Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))).asHom.app G)) :
    Condition1 ((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a :
        Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f)))
      (fun n => powQuotient ((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a :
        Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))) G (n + 1))
      (fun n => quotientToQuotient ((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus
          A a : Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))) G (n + 1)) := by
  refine (stacks0H39_one_iff_two _ _ _).2 ((stacks0H39_two_iff_three _ _ _).2
    (stacks0H39_four_imp_three _ _ _ ⟨G, hG, fun n => Iso.refl _, fun n => ?_⟩))
  simp

/-- The principal-adic inverse system of Stacks 0BLB attached to an `f`-torsion-free module `G`
on `U` whose quotient `G / fG` has finitely generated global sections: its terms are the
quotients `G / f^(n+1) G`. -/
abbrev complementAdicSystem (f : A) (hcomplete : IsAdicComplete (Ideal.span {f}) A)
    (G : (complementZeroLocus A a : Scheme).Modules) (hG : Mono
        (((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a :
        Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))).asHom.app G))
    (hfin : Module.Finite A ((ModuleCat.restrictScalars (complementTopScalars a)).obj
      ((_root_.SheafOfModules.evaluation (complementZeroLocus A a : Scheme).ringCatSheaf (op ⊤)).obj
        (powQuotient ((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a :
            Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))) G 1)))) :
    Stacks.Modules.PrincipalAdicInverseSystem.{u, u} where
  X := (complementZeroLocus A a : Scheme)
  A := A
  noetherian := inferInstance
  f := f
  complete := hcomplete
  R := (complementZeroLocus A a : Scheme).ringCatSheaf
  mulCommutative := fun _ => inferInstance
  scalarMap := complementTopScalars a
  F n := powQuotient ((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a :
      Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))) G (n + 1)
  map n := quotientToQuotient ((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a
      : Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))) G (n + 1)
  finite_first := hfin
  condition := condition1_powQuotient A a f G hG

/-- The quotient projection `G ⟶ G / f^(n+1) G`. -/
abbrev complementProj (f : A)
    (G : SheafOfModules.{u} (complementZeroLocus A a : Scheme).ringCatSheaf) (n : ℕ) :
    G ⟶ powQuotient ((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a :
        Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))) G (n + 1) :=
  cokernel.π (C := SheafOfModules.{u} (complementZeroLocus A a : Scheme).ringCatSheaf)
    ((((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a : Scheme).ringCatSheaf ⊤
        isTerminalTop (complementTopScalars a f))) ^ (n + 1)).asHom.app G)

omit [IsNoetherianRing A] in
/-- The quotient projections are compatible with the transition maps. -/
theorem complementProj_comp_quotientToQuotient (f : A)
    (G : SheafOfModules.{u} (complementZeroLocus A a : Scheme).ringCatSheaf) (n : ℕ) :
    complementProj A a f G (n + 1) ≫ quotientToQuotient ((Stacks.SheafOfModules.terminalSectionToEnd
        (complementZeroLocus A a : Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a
        f))) G (n + 1) =
      complementProj A a f G n :=
  cokernel.π_desc _ _ _

variable (f : A) (hcomplete : IsAdicComplete (Ideal.span {f}) A)
  (G : (complementZeroLocus A a : Scheme).Modules) (hG : Mono
      (((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a : Scheme).ringCatSheaf
      ⊤ isTerminalTop (complementTopScalars a f))).asHom.app G))
  (hfin : Module.Finite A ((ModuleCat.restrictScalars (complementTopScalars a)).obj
    ((_root_.SheafOfModules.evaluation (complementZeroLocus A a : Scheme).ringCatSheaf
      (op ⊤)).obj (powQuotient ((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a
          : Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))) G 1))))

/-- The global sections of `G`, as an `A`-module. -/
abbrev complementSections : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (complementTopScalars a)).obj
    ((_root_.SheafOfModules.evaluation (complementZeroLocus A a : Scheme).ringCatSheaf
      (op ⊤)).obj G)

/-- The cone over the inverse system of `complementAdicSystem` given by reduction of global
sections. -/
def complementReductionCone :
    Cone (complementAdicSystem A a f hcomplete G hG hfin).globalSectionsSystem where
  pt := complementSections A a G
  π := NatTrans.ofOpSequence
    (fun n => (ModuleCat.restrictScalars (complementTopScalars a)).map
      ((_root_.SheafOfModules.evaluation (complementZeroLocus A a : Scheme).ringCatSheaf
        (op ⊤)).map (complementProj A a f G n)))
    (fun n => by
      simp only [Stacks.Modules.PrincipalAdicInverseSystem.globalSectionsSystem,
        Functor.ofOpSequence_map_homOfLE_succ, Functor.const_obj_map]
      refine (Category.id_comp _).trans ?_
      refine (congrArg (fun φ => (ModuleCat.restrictScalars (complementTopScalars a)).map
        ((_root_.SheafOfModules.evaluation (complementZeroLocus A a : Scheme).ringCatSheaf
          (op ⊤)).map φ)) (complementProj_comp_quotientToQuotient A a f G n).symm).trans ?_
      exact (congrArg (ModuleCat.restrictScalars (complementTopScalars a)).map
        ((_root_.SheafOfModules.evaluation (complementZeroLocus A a : Scheme).ringCatSheaf
          (op ⊤)).map_comp _ _)).trans ((ModuleCat.restrictScalars _).map_comp _ _))

/-- The reduction map from the global sections of `G` to the limit `N` of the global sections
of the quotients `G / f^(n+1) G`. -/
def complementReduction :
    complementSections A a G ⟶ (complementAdicSystem A a f hcomplete G hG hfin).M :=
  limit.lift _ (complementReductionCone A a f hcomplete G hG hfin)

/-- The components of the reduction map are the reductions of global sections. -/
theorem complementReduction_π (n : ℕ) (m : complementSections A a G) :
    (limit.π (complementAdicSystem A a f hcomplete G hG hfin).globalSectionsSystem (op n)).hom
        ((complementReduction A a f hcomplete G hG hfin).hom m) =
      Scheme.Modules.Hom.app (complementProj A a f G n) ⊤ m :=
  congrArg (fun φ => φ.hom m)
    (limit.lift_π (complementReductionCone A a f hcomplete G hG hfin) (op n))

omit [IsNoetherianRing A] in
/-- The map induced on stalks by a morphism of `𝒪_U`-modules is `Γ(U, 𝒪_U)`-linear for the
module structures on the stalks through the germ map. -/
theorem stalk_map_smul {G K : (complementZeroLocus A a : Scheme).Modules} (ψ : G ⟶ K)
    (x : (complementZeroLocus A a : Scheme)) (r : Γ((complementZeroLocus A a : Scheme), ⊤))
    (z : G.presheaf.stalk x) :
    letI := affineStalkModule G ⊤ x trivial
    letI := affineStalkModule K ⊤ x trivial
    ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map ψ.mapPresheaf) (r • z) =
      r • @id (K.presheaf.stalk x)
        (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map ψ.mapPresheaf) z) :=
  (schemeStalkLinearMap ψ x).map_smul _ z

/-- **The reductions are surjective near the formal locus, up to `f`.** At a point `x` of
`U ∩ V(f)`, every element `y` of the limit `N` becomes, after multiplication by an element of
`A` outside the prime of `x`, the sum of the reduction of a global section of `G` and a multiple
of `f`. The image of `y` in `Γ(U, G/fG)` is locally the image of a section of `G`, because
`G ⟶ G/fG` is surjective on stalks; that section extends to `U` after multiplication by an
element outside the prime; and the two global sections of `G/fG` then agree after a further such
multiplication. What is left over lies in the kernel of the first projection, which is `f N`. -/
theorem exists_smul_mem_range_complementReduction_sup [G.IsCoherent]
    (x : (complementZeroLocus A a : Scheme))
    (y : (complementAdicSystem A a f hcomplete G hG hfin).M) :
    ∃ s ∉ x.1.asIdeal, s • y ∈
      LinearMap.range (complementReduction A a f hcomplete G hG hfin).hom ⊔
        LinearMap.range
          (LinearMap.lsmul A (complementAdicSystem A a f hcomplete G hG hfin).M f) := by
  let S := complementAdicSystem A a f hcomplete G hG hfin
  let P0 : (complementZeroLocus A a :
      Scheme).Modules := powQuotient ((Stacks.SheafOfModules.terminalSectionToEnd
      (complementZeroLocus A a : Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a
      f))) G 1
  have : ((𝟭 (SheafOfModules.{u} (complementZeroLocus A a : Scheme).ringCatSheaf)).obj
      G).IsCoherent :=
    ‹G.IsCoherent›
  have : P0.IsCoherent := SheafOfModules.cokernel_isCoherent _
  have : P0.IsQuasicoherent := isQuasicoherent_of_isCoherent P0
  have : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  let := affineStalkModule G ⊤ x trivial
  let := affineStalkModule P0 ⊤ x trivial
  let π0 := (limit.π S.globalSectionsSystem (op 0)).hom
  let n1 : Γ(P0, ⊤) := π0 y
  let ρ : G ⟶ P0 := complementProj A a f G 0
  have hsurj : Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map ρ.mapPresheaf)) :=
    (AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap
      (complementProj A a f G 0)).1 coequalizer.π_epi x
  obtain ⟨z, hz⟩ := hsurj (P0.presheaf.germ ⊤ x trivial n1)
  obtain ⟨b, hb, m, hm⟩ := exists_smul_eq_germ A a G x z
  have h1 : P0.presheaf.germ ⊤ x trivial (Scheme.Modules.Hom.app ρ ⊤ m) =
      P0.presheaf.germ ⊤ x trivial (complementTopScalars a b • n1) := by
    refine (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial ρ.mapPresheaf m).symm.trans ?_
    rw [← hm]
    refine (stalk_map_smul A a ρ x (complementTopScalars a b) z).trans ?_
    refine (congrArg (fun w : P0.presheaf.stalk x => complementTopScalars a b • w) hz).trans ?_
    exact ((affineGerm P0 ⊤ x trivial).map_smul _ n1).symm
  have h2 : P0.presheaf.germ ⊤ x trivial
      (Scheme.Modules.Hom.app ρ ⊤ m - complementTopScalars a b • n1) = 0 := by
    rw [map_sub, h1, sub_self]
  obtain ⟨c, hc, hcz⟩ := exists_smul_eq_zero_of_germ_eq_zero A a P0 _ x h2
  let m' : complementSections A a G := m
  refine ⟨c * b, fun h => (x.1.isPrime.mem_or_mem h).elim hc hb, ?_⟩
  have hker : (c * b) • y - (complementReduction A a f hcomplete G hG hfin).hom (c • m') ∈
      LinearMap.range (LinearMap.lsmul A S.M f) := by
    rw [Stacks.Modules.PrincipalAdicInverseSystem.range_lsmul_eq_ker_firstProjection S]
    change π0 ((c * b) • y - (complementReduction A a f hcomplete G hG hfin).hom (c • m')) = 0
    have e1 : π0 ((c * b) • y) = complementTopScalars a (c * b) • n1 := π0.map_smul (c * b) y
    have e2 : π0 ((complementReduction A a f hcomplete G hG hfin).hom (c • m')) =
        complementTopScalars a c • Scheme.Modules.Hom.app ρ ⊤ m :=
      ((congrArg π0 ((complementReduction A a f hcomplete G hG hfin).hom.map_smul c m')).trans
        (π0.map_smul c _)).trans
        (congrArg (fun w : S.globalSectionsSystem.obj (op 0) => c • w)
          (complementReduction_π A a f hcomplete G hG hfin 0 m))
    refine (π0.map_sub _ _).trans ?_
    rw [e1, e2, map_mul, mul_smul]
    have h3 : (complementTopScalars a c • complementTopScalars a b • n1 -
        complementTopScalars a c • Scheme.Modules.Hom.app ρ ⊤ m : Γ(P0, ⊤)) = 0 := by
      rw [← smul_sub, ← neg_sub, smul_neg, hcz, neg_zero]
    exact h3
  have hsum : (c * b) • y = (complementReduction A a f hcomplete G hG hfin).hom (c • m') +
      ((c * b) • y - (complementReduction A a f hcomplete G hG hfin).hom (c • m')) := by
    abel
  rw [hsum]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) hker

/-- At a point `x` of `U ∩ V(f)`, every element of the limit `N` becomes the reduction of a
global section of `G` after multiplication by an element of `A` outside the prime of `x`: this
is `exists_smul_mem_range_complementReduction_sup` and Nakayama's lemma, `N` being finite by
Stacks 0BLB. -/
theorem exists_smul_eq_complementReduction [G.IsCoherent]
    (x : (complementZeroLocus A a : Scheme)) (hx : f ∈ x.1.asIdeal)
    (y : (complementAdicSystem A a f hcomplete G hG hfin).M) :
    ∃ s ∉ x.1.asIdeal, ∃ m : complementSections A a G,
      s • y = (complementReduction A a f hcomplete G hG hfin).hom m := by
  have : Module.Finite A (complementAdicSystem A a f hcomplete G hG hfin).M :=
    Stacks.Modules.PrincipalAdicInverseSystem.finite_limitGlobalSections
      (complementAdicSystem A a f hcomplete G hG hfin)
  have : x.1.asIdeal.IsPrime := x.1.isPrime
  obtain ⟨s, hs, m, hm⟩ := exists_smul_mem_of_forall_exists_smul_mem_sup x.1.asIdeal
    (LinearMap.range (complementReduction A a f hcomplete G hG hfin).hom) hx
    (exists_smul_mem_range_complementReduction_sup A a f hcomplete G hG hfin x) y
  exact ⟨s, hs, m, hm.symm⟩

omit [IsNoetherianRing A] in
/-- The tower of quotients `G / Iⁿ G` by the powers of the ideal sheaf `(f) 𝒪_U`, which is the
tower the comparison map of Stacks 0EG2 is built from, is the tower of cokernels of the powers
of multiplication by `f`, compatibly with the projections from `G`. -/
theorem exists_quotientSystemNearVanishing_iso_powQuotient (n : ℕ) :
    ∃ e : (quotientSystemNearVanishing A (Ideal.span {f}) a G).obj (op n) ≅
        powQuotient ((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a :
            Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))) G n,
      adicProj (idealSheafNearVanishing A (Ideal.span {f}) a) G (op n) ≫ e.hom =
        cokernel.π ((((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a :
            Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))) ^ n).asHom.app
          G) := by
  change ∃ e : cokernel (C := (complementZeroLocus A a : Scheme).Modules)
      (idealPowerMultiple (idealSheafNearVanishing A (Ideal.span {f}) a) n G).ι ≅ _,
    cokernel.π (C := (complementZeroLocus A a : Scheme).Modules)
      (idealPowerMultiple (idealSheafNearVanishing A (Ideal.span {f}) a) n G).ι ≫ e.hom = _
  rw [idealSheafNearVanishing_span_singleton_eq_scalarIdealData]
  exact principalPowerQuotientIso _ G n

/-- The neighbourhood `U` itself of the formal locus. -/
abbrev topNearVanishing (I : Ideal A) : OpensNearVanishing A I a :=
  ⟨⊤, fun _ _ => trivial⟩

/-- A global section of `G` whose reductions modulo every `f^(n+1)` vanish is killed by the
comparison at the neighbourhood `U` of the formal locus. -/
theorem comparisonAt_top_eq_zero_of_complementReduction_eq_zero (k : complementSections A a G)
    (hk : (complementReduction A a f hcomplete G hG hfin).hom k = 0) :
    ConcreteCategory.hom
      (comparisonAt A (Ideal.span {f}) a G (topNearVanishing A a (Ideal.span {f}))) k = 0 := by
  refine (comparisonAt_apply_eq_zero_iff A (Ideal.span {f}) a G
    (topNearVanishing A a (Ideal.span {f})) k).2 fun n => ?_
  obtain ⟨e, he⟩ := exists_quotientSystemNearVanishing_iso_powQuotient A a f G n.unop
  refine injective_app_hom_of_iso e ⊤ ((congrArg (fun φ =>
    ConcreteCategory.hom (Scheme.Modules.Hom.app φ ⊤) k) he).trans ?_ |>.trans (map_zero _).symm)
  obtain ⟨n⟩ := n
  cases n with
  | zero =>
    have := subsingleton_sections_powQuotient_zero (Stacks.SheafOfModules.terminalSectionToEnd
      (complementZeroLocus A a : Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))
      G ⊤
    exact Subsingleton.elim _ _
  | succ m =>
    have h := complementReduction_π A a f hcomplete G hG hfin m k
    rw [hk] at h
    exact h.symm.trans (map_zero _)

/-- **The kernel of the reductions vanishes along the formal locus.** A global section of `G`
whose reductions modulo every `f^(n+1)` vanish has vanishing germ at every point of `U ∩ V(f)`,
by Krull's intersection theorem in the form
`Stacks.Algebraization.germ_eq_zero_of_comparisonAt_apply_eq_zero`. -/
theorem germ_eq_zero_of_complementReduction_eq_zero [G.IsCoherent]
    (k : complementSections A a G) (hk : (complementReduction A a f hcomplete G hG hfin).hom k = 0)
    (x : (complementZeroLocus A a : Scheme)) (hx : f ∈ x.1.asIdeal) :
    G.presheaf.germ ⊤ x trivial k = 0 :=
  germ_eq_zero_of_comparisonAt_apply_eq_zero A (Ideal.span {f}) a G
    (topNearVanishing A a (Ideal.span {f})) k
    (comparisonAt_top_eq_zero_of_complementReduction_eq_zero A a f hcomplete G hG hfin k hk)
    (mem_support_baseIdealSheaf (Ideal.span {f}) _
      ((Ideal.span_singleton_le_iff_mem _).2 hx))

omit [IsNoetherianRing A] in
/-- The image of `c ∈ A` is a unit on any open contained in its basic open in `U`. -/
theorem isUnit_res_complementScalar (c : A) {W : (complementZeroLocus A a : Scheme).Opens}
    (hW : W ≤ (complementZeroLocus A a : Scheme).basicOpen (complementTopScalars a c)) :
    IsUnit ((complementZeroLocus A a : Scheme).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
      (complementTopScalars a c)) := by
  have h := (complementZeroLocus A a : Scheme).toRingedSpace.isUnit_res_basicOpen
    (complementTopScalars a c)
  have e : (homOfLE (le_top : W ≤ ⊤)).op =
      (homOfLE ((complementZeroLocus A a : Scheme).toRingedSpace.basicOpen_le
        (complementTopScalars a c))).op ≫ (homOfLE hW).op := Subsingleton.elim _ _
  rw [e]
  exact (congrArg IsUnit ((complementZeroLocus A a : Scheme).presheaf.map_comp_apply _ _ _)).mpr
    (h.map _)

omit [IsNoetherianRing A] in
/-- Restriction of sections from `U` to an open, composed with a further restriction. -/
theorem presheaf_map_top_comp_apply (H : (complementZeroLocus A a : Scheme).Modules)
    {Z Z' : (complementZeroLocus A a : Scheme).Opens} (h : Z' ≤ Z) (s : Γ(H, ⊤)) :
    H.presheaf.map (homOfLE h).op (H.presheaf.map (homOfLE (le_top : Z ≤ ⊤)).op s) =
      H.presheaf.map (homOfLE (le_top : Z' ≤ ⊤)).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

omit [IsNoetherianRing A] in
/-- The same for the structure sheaf. -/
theorem presheaf_map_top_comp_apply_ring
    {Z Z' : (complementZeroLocus A a : Scheme).Opens} (h : Z' ≤ Z)
    (s : Γ((complementZeroLocus A a : Scheme), ⊤)) :
    (complementZeroLocus A a : Scheme).presheaf.map (homOfLE h).op
        ((complementZeroLocus A a : Scheme).presheaf.map (homOfLE (le_top : Z ≤ ⊤)).op s) =
      (complementZeroLocus A a : Scheme).presheaf.map (homOfLE (le_top : Z' ≤ ⊤)).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

omit [IsNoetherianRing A] in
/-- A unit of `Γ(U, 𝒪_U)` over an open acts injectively on the sections of any module there. -/
theorem eq_of_smul_eq_smul_of_isUnit {H : (complementZeroLocus A a : Scheme).Modules}
    {Z : (complementZeroLocus A a : Scheme).Opens} {r : Γ((complementZeroLocus A a : Scheme), Z)}
    (hr : IsUnit r) {s s' : Γ(H, Z)} (h : r • s = r • s') : s = s' :=
  hr.smul_left_cancel.1 h

/-- **Algebraization of one formal section on a neighbourhood of the formal locus.** For every
element `x` of the limit `N`, there are an open `V ⊆ U` containing every point of `U ∩ V(f)`
and a section `t` of `G` over `V` whose reduction modulo every `f^(n+1)` is the restriction of
the corresponding component of `x`.

Near each point of the formal locus, some `c ∉ 𝔭` makes `c x` the reduction of a global
section `m`, and `t = c⁻¹ m` works on the basic open of `c`. The formal locus is quasi-compact,
so finitely many such opens cover it; on the overlaps the local solutions differ by sections
whose reductions all vanish, which vanish near the formal locus by Krull's intersection theorem,
so after shrinking each open to where these finitely many differences vanish the local solutions
glue. -/
theorem exists_section_complementProj_eq [G.IsCoherent]
    (x : (complementAdicSystem A a f hcomplete G hG hfin).M) :
    ∃ (V : (complementZeroLocus A a : Scheme).Opens) (t : Γ(G, V)),
      (∀ y : (complementZeroLocus A a : Scheme), f ∈ y.1.asIdeal → y ∈ V) ∧
      ∀ n : ℕ, Scheme.Modules.Hom.app (complementProj A a f G n) V t =
        ConcreteCategory.hom ((Scheme.Modules.presheaf (X := (complementZeroLocus A a : Scheme))
          (powQuotient ((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a :
              Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))) G (n + 1))).map
            (homOfLE le_top).op)
          ((limit.π (complementAdicSystem A a f hcomplete G hG hfin).globalSectionsSystem
            (op n)).hom x) := by
  classical
  let 𝒳 := (complementZeroLocus A a : Scheme)
  let S := complementAdicSystem A a f hcomplete G hG hfin
  let φM := (complementReduction A a f hcomplete G hG hfin).hom
  -- the ideal of the elements of `A` multiplying `x` into the image of the reductions
  let J : Ideal A := (LinearMap.range φM).comap (LinearMap.toSpanSingleton A S.M x)
  have hJ : ∀ c : A, c ∈ J ↔ ∃ m, φM m = c • x := fun c => Iff.rfl
  obtain ⟨T, hT⟩ : J.FG := IsNoetherian.noetherian J
  have hTJ : ∀ c ∈ T, c ∈ J := fun c hc => hT ▸ Ideal.subset_span hc
  choose! m hm using fun c (hc : c ∈ T) => (hJ c).1 (hTJ c hc)
  let W : T → 𝒳.Opens := fun i => 𝒳.basicOpen (complementTopScalars a i.1)
  let kk : T → T → complementSections A a G := fun i j => j.1 • m i.1 - i.1 • m j.1
  have hkk : ∀ i j, φM (kk i j) = 0 := fun i j => by
    simp only [kk, map_sub, map_smul, hm _ i.2, hm _ j.2, smul_smul, mul_comm, sub_self]
  let O : T × T → 𝒳.Opens := fun ij => germVanishingOpens G ⊤ (kk ij.1 ij.2)
  let V0 : 𝒳.Opens := (⨆ i, W i) ⊓ ⨅ ij, O ij
  have hV0 : ∀ y : 𝒳, f ∈ y.1.asIdeal → y ∈ V0 := by
    intro y hy
    refine ⟨?_, ?_⟩
    · obtain ⟨s, hs, m0, hm0⟩ := exists_smul_eq_complementReduction A a f hcomplete G hG hfin
        y hy x
      have : ∃ c ∈ T, c ∉ y.1.asIdeal := by
        by_contra hcon
        have hle : J ≤ y.1.asIdeal := hT ▸ Ideal.span_le.2 fun c hc =>
          by_contra fun h => hcon ⟨c, hc, h⟩
        exact hs (hle ((hJ s).2 ⟨m0, hm0.symm⟩))
      obtain ⟨c, hc, hcy⟩ := this
      exact (Opens.mem_iSup (s := W)).2
        ⟨⟨c, hc⟩, (mem_basicOpen_complementScalar_iff A a y c).2 hcy⟩
    · change y ∈ ((⨅ ij, O ij : 𝒳.Opens) : Set 𝒳)
      rw [Opens.coe_iInf, Set.mem_iInter]
      intro ij
      exact ⟨trivial, fun _ => germ_eq_zero_of_complementReduction_eq_zero A a f hcomplete G hG hfin
        (kk ij.1 ij.2) (hkk ij.1 ij.2) y hy⟩
  -- the local solutions
  let Oall : 𝒳.Opens := ⨅ ij, O ij
  let Vi : T → 𝒳.Opens := fun i => W i ⊓ Oall
  have hViW : ∀ i, Vi i ≤ W i := fun i => inf_le_left
  have hViO : ∀ i j, Vi i ≤ O (i, j) := fun i j => inf_le_right.trans (iInf_le O (i, j))
  let mm : T → Γ(G, ⊤) := fun i => m i.1
  let σ : T → Γ(𝒳, ⊤) := fun i => complementTopScalars a i.1
  let res : ∀ Z : 𝒳.Opens, Γ(G, ⊤) → Γ(G, Z) := fun Z s =>
    G.presheaf.map (homOfLE (le_top : Z ≤ ⊤)).op s
  let resR : ∀ Z : 𝒳.Opens, Γ(𝒳, ⊤) →+* Γ(𝒳, Z) := fun Z =>
    (𝒳.presheaf.map (homOfLE (le_top : Z ≤ ⊤)).op).hom
  have hunit : ∀ i, IsUnit (resR (Vi i) (σ i)) := fun i =>
    isUnit_res_complementScalar A a i.1 (hViW i)
  let t : ∀ i, Γ(G, Vi i) := fun i => (↑(hunit i).unit⁻¹ : Γ(𝒳, Vi i)) • res (Vi i) (mm i)
  have ht : ∀ i, resR (Vi i) (σ i) • t i = res (Vi i) (mm i) := fun i => by
    change ((hunit i).unit : Γ(𝒳, Vi i)) • _ = _
    rw [smul_smul, Units.mul_inv, one_smul]
  have hres_smul : ∀ (Z : 𝒳.Opens) (r : Γ(𝒳, ⊤)) (s : Γ(G, ⊤)),
      res Z (r • s) = resR Z r • res Z s :=
    fun Z r s => Scheme.Modules.map_smul G _ r s
  -- a local solution, restricted further, is still characterized by the same equation
  have hrestrict : ∀ i (Q : 𝒳.Opens) (hQ : Q ≤ Vi i),
      resR Q (σ i) • G.presheaf.map (homOfLE hQ).op (t i) = res Q (mm i) := fun i Q hQ =>
    (congrArg (· • G.presheaf.map (homOfLE hQ).op (t i))
      (presheaf_map_top_comp_apply_ring A a hQ (σ i)).symm).trans
      ((Scheme.Modules.map_smul G (homOfLE hQ) (resR (Vi i) (σ i)) (t i)).symm.trans
        ((congrArg (G.presheaf.map (homOfLE hQ).op) (ht i)).trans
          (presheaf_map_top_comp_apply A a G hQ (mm i))))
  have hkkG : ∀ i j, (kk i j : Γ(G, ⊤)) = σ j • mm i - σ i • mm j := fun i j => rfl
  -- compatibility on overlaps
  have hcompat : TopCat.Presheaf.IsCompatible G.presheaf Vi t := by
    intro i j
    let Q := Vi i ⊓ Vi j
    have hQi : Q ≤ Vi i := inf_le_left
    have hQj : Q ≤ Vi j := inf_le_right
    have hu : IsUnit (resR Q (σ i * σ j)) := by
      rw [map_mul]
      exact (isUnit_res_complementScalar A a i.1 (hQi.trans (hViW i))).mul
        (isUnit_res_complementScalar A a j.1 (hQj.trans (hViW j)))
    refine eq_of_smul_eq_smul_of_isUnit A a hu ?_
    have e1 : resR Q (σ i * σ j) • G.presheaf.map (homOfLE hQi).op (t i) = res Q (σ j • mm i) := by
      rw [map_mul, mul_comm, mul_smul, hrestrict i Q hQi, hres_smul]
    have e2 : resR Q (σ i * σ j) • G.presheaf.map (homOfLE hQj).op (t j) = res Q (σ i • mm j) := by
      rw [map_mul, mul_smul, hrestrict j Q hQj, hres_smul]
    change _ • G.presheaf.map (homOfLE hQi).op (t i) = _ • G.presheaf.map (homOfLE hQj).op (t j)
    rw [e1, e2, ← sub_eq_zero]
    have hO : Q ≤ germVanishingOpens G ⊤ (kk i j) := hQi.trans (hViO i j)
    have h0 := res_germVanishingOpens_eq_zero G ⊤ (kk i j)
    have h2 : G.presheaf.map (homOfLE (le_top : Q ≤ ⊤)).op (kk i j) = 0 :=
      presheaf_map_eq_zero_of_le (homOfLE hO) _ _ h0
    change G.presheaf.map (homOfLE (le_top : Q ≤ ⊤)).op (σ j • mm i) -
      G.presheaf.map (homOfLE (le_top : Q ≤ ⊤)).op (σ i • mm j) = 0
    rw [← map_sub]
    exact h2
  -- gluing
  have hVi0 : ∀ i, Vi i ≤ V0 := fun i => inf_le_inf (le_iSup W i) le_rfl
  have hcover : V0 ≤ iSup Vi := by
    rintro y ⟨hyW, hyO⟩
    obtain ⟨i, hi⟩ := (Opens.mem_iSup (s := W)).1 hyW
    exact (Opens.mem_iSup (s := Vi)).2 ⟨i, hi, hyO⟩
  obtain ⟨tt, htt, -⟩ := TopCat.Sheaf.existsUnique_gluing' (⟨G.presheaf, G.isSheaf⟩ :
      TopCat.Sheaf Ab.{u} 𝒳) Vi V0 (fun i => homOfLE (hVi0 i)) hcover t hcompat
  refine ⟨V0, tt, hV0, fun n => ?_⟩
  let P : 𝒳.Modules := powQuotient ((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus
      A a : Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))) G (n + 1)
  let pr : G ⟶ P := complementProj A a f G n
  let πn := (limit.π S.globalSectionsSystem (op n)).hom
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨P.presheaf, P.isSheaf⟩ : TopCat.Sheaf Ab.{u} 𝒳) Vi V0
    (fun i => homOfLE (hVi0 i)) hcover _ _ fun i => ?_
  change P.presheaf.map (homOfLE (hVi0 i)).op (Scheme.Modules.Hom.app pr V0 tt) =
    P.presheaf.map (homOfLE (hVi0 i)).op (P.presheaf.map (homOfLE (le_top : V0 ≤ ⊤)).op (πn x))
  rw [presheaf_map_app_apply, htt i]
  refine Eq.trans ?_ (presheaf_map_top_comp_apply A a P (hVi0 i) (πn x)).symm
  refine eq_of_smul_eq_smul_of_isUnit A a (hunit i) ?_
  rw [← Scheme.Modules.Hom.app_smul, ht i]
  change Scheme.Modules.Hom.app pr (Vi i) (G.presheaf.map (homOfLE (le_top : Vi i ≤ ⊤)).op
    (mm i)) = _
  rw [← presheaf_map_app_apply]
  let πx : Γ(P, ⊤) := πn x
  have hpi : Scheme.Modules.Hom.app pr ⊤ (mm i) = σ i • πx :=
    (complementReduction_π A a f hcomplete G hG hfin n (m i.1)).symm.trans
      ((congrArg πn (hm _ i.2)).trans (πn.map_smul _ x))
  rw [hpi]
  exact Scheme.Modules.map_smul P (homOfLE (le_top : Vi i ≤ ⊤)) (σ i) πx

/-- If the direct image to `Spec A` of `G / fG` is coherent, the global sections of `G / fG` form
a finite `A`-module. -/
theorem finite_sections_powQuotient_one_of_isCoherent (f : A)
    (G : (complementZeroLocus A a : Scheme).Modules)
    (hcoh : ((Scheme.Modules.pushforward (complementZeroLocus A a).ι).obj
      ((quotientSystemNearVanishing A (Ideal.span {f}) a G).obj (op 1))).IsCoherent) :
    Module.Finite A ((ModuleCat.restrictScalars (complementTopScalars a)).obj
      ((_root_.SheafOfModules.evaluation (complementZeroLocus A a : Scheme).ringCatSheaf
        (op ⊤)).obj (powQuotient ((Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A
            a : Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))) G 1))) := by
  let Q := (quotientSystemNearVanishing A (Ideal.span {f}) a G).obj (op 1)
  let H := (Scheme.Modules.pushforward (complementZeroLocus A a).ι).obj Q
  have : H.IsCoherent := hcoh
  obtain ⟨hHq, hHf⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent H
  have hH := moduleFinite_of_isFiniteType_qc (CommRingCat.of A) H
  let e1 := pushforwardGlobalSectionsIsoApp (⟨A, a, a, le_rfl⟩ : AlgebraizationSituation) Q
  have hQ : Module.Finite A ((ModuleCat.restrictScalars (complementTopScalars a)).obj
      ((_root_.SheafOfModules.evaluation (complementZeroLocus A a : Scheme).ringCatSheaf
        (op ⊤)).obj Q)) := by
    have : Module.Finite A ((Scheme.Modules.pushforward (⟨A, a, a, le_rfl⟩ :
        AlgebraizationSituation).U.ι ⋙
        moduleSpecΓFunctor (R := CommRingCat.of A)).obj Q) := hH
    exact Module.Finite.equiv e1.toLinearEquiv
  obtain ⟨e, -⟩ := exists_quotientSystemNearVanishing_iso_powQuotient A a f G 1
  exact Module.Finite.equiv ((ModuleCat.restrictScalars (complementTopScalars a)).mapIso
    ((_root_.SheafOfModules.evaluation (complementZeroLocus A a : Scheme).ringCatSheaf
      (op ⊤)).mapIso e)).toLinearEquiv

end Scalars

/-- **The comparison map at a principal formal locus, for a torsion-free module.** Let `A` be a
Noetherian ring, `f`-adically complete, and `G` a coherent module on `U = Spec(A) ∖ V(𝔞)` none of
whose associated points lies in `V(f)`. If the direct image to `Spec A` of `G / fG` is coherent,
that is, if `Γ(U, G / fG)` is a finite `A`-module, then the comparison map
`colim_V Γ(V, G) ⟶ lim Γ(U, G / fⁿ G)` of Stacks 0EG2 is an isomorphism.

This is the sheaf form of Stacks 0EIH: `f` is a nonzerodivisor on `G` because it is a unit at the
associated points, and the finiteness of `Γ(U, G / fG)` is the finiteness of `H¹_𝔞` of the
quotient in the source. -/
theorem isIso_comparisonMap_span_singleton_of_isCoherent_pushforward
    (A : Type u) [CommRing A] [IsNoetherianRing A] (a : Ideal A) (f : A)
    (hcomplete : IsAdicComplete (Ideal.span {f}) A)
    (F : (complementZeroLocus A a : Scheme).Modules) [F.IsCoherent]
    (hAss : ∀ x ∈ Stacks.Divisors.associatedPoints F, f ∉ x.1.asIdeal)
    (hcoh : ((Scheme.Modules.pushforward (complementZeroLocus A a).ι).obj
      ((quotientSystemNearVanishing A (Ideal.span {f}) a F).obj (op 1))).IsCoherent) :
    IsIso (comparisonMap A (Ideal.span {f}) a F) := by
  classical
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hG := mono_complementMul_app A a f F hAss
  have hfin := finite_sections_powQuotient_one_of_isCoherent A a f F hcoh
  let S := complementAdicSystem A a f hcomplete F hG hfin
  let Q := quotientSystemNearVanishing A (Ideal.span {f}) a F
  let J := idealSheafNearVanishing A (Ideal.span {f}) a
  let g := (Stacks.SheafOfModules.terminalSectionToEnd (complementZeroLocus A a :
      Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a f))
  choose e he using exists_quotientSystemNearVanishing_iso_powQuotient A a f F
  -- the identifications are compatible with the transition maps
  have hetr : ∀ n : ℕ, Q.map (homOfLE (Nat.le_succ n)).op ≫ (e n).hom =
      (e (n + 1)).hom ≫ quotientToQuotient g F n := by
    intro n
    have : Epi (adicProj J F (op (n + 1))) := coequalizer.π_epi
    refine (cancel_epi (adicProj J F (op (n + 1)))).1 ?_
    have h1 : adicProj J F (op (n + 1)) ≫ Q.map (homOfLE (Nat.le_succ n)).op =
        adicProj J F (op n) := adicProj_comp_map J F _
    have lhs : adicProj J F (op (n + 1)) ≫ Q.map (homOfLE (Nat.le_succ n)).op ≫ (e n).hom =
        cokernel.π ((g ^ n).asHom.app F) :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (e n).hom) h1).trans (he n))
    have rhs : adicProj J F (op (n + 1)) ≫ (e (n + 1)).hom ≫ quotientToQuotient g F n =
        cokernel.π ((g ^ n).asHom.app F) :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ quotientToQuotient g F n)
        (he (n + 1))).trans (cokernel.π_desc _ _ _))
    exact lhs.trans rhs.symm
  -- the formal section, read in the limit `N` of Stacks 0BLB
  have hsurj :
      Function.Surjective (ConcreteCategory.hom (comparisonMap A (Ideal.span {f}) a F)) := by
    rw [surjective_comparisonMap_iff]
    intro s
    let sc : ∀ n : ℕ, S.globalSectionsSystem.obj (op n) := fun n =>
      Scheme.Modules.Hom.app (e (n + 1)).hom ⊤
        (ConcreteCategory.hom (limit.π (formalSections A (Ideal.span {f}) a F) (op (n + 1))) s)
    have hsc : ∀ n, Scheme.Modules.Hom.app (quotientToQuotient g F (n + 1)) ⊤ (sc (n + 1)) =
        sc n := by
      intro n
      have hw := limit.w (formalSections A (Ideal.span {f}) a F) (homOfLE (Nat.le_succ (n + 1))).op
      have h1 := ConcreteCategory.congr_hom hw s
      change ConcreteCategory.hom
        (Scheme.Modules.Hom.app (Q.map (homOfLE (Nat.le_succ (n + 1))).op) ⊤)
        (ConcreteCategory.hom (limit.π (formalSections A (Ideal.span {f}) a F) (op (n + 2))) s) =
        ConcreteCategory.hom (limit.π (formalSections A (Ideal.span {f}) a F) (op (n + 1))) s at h1
      change ConcreteCategory.hom (Scheme.Modules.Hom.app ((e (n + 2)).hom ≫
        quotientToQuotient g F (n + 1)) ⊤)
        (ConcreteCategory.hom (limit.π (formalSections A (Ideal.span {f}) a F) (op (n + 2))) s) =
        ConcreteCategory.hom (Scheme.Modules.Hom.app (e (n + 1)).hom ⊤)
        (ConcreteCategory.hom (limit.π (formalSections A (Ideal.span {f}) a F) (op (n + 1))) s)
      rw [← hetr (n + 1), ← h1]
      rfl
    -- the element `x` of `N` with these components
    let cone : Cone S.globalSectionsSystem :=
      { pt := ModuleCat.of S.A S.A
        π := NatTrans.ofOpSequence
          (fun n => ModuleCat.ofHom (R := S.A) (X := S.A) (Y := S.globalSectionsSystem.obj (op n))
            (LinearMap.toSpanSingleton S.A (S.globalSectionsSystem.obj (op n)) (sc n)))
          (fun n => by
            refine (Category.id_comp _).trans ?_
            ext
            refine (one_smul S.A (sc n)).trans ?_
            refine Eq.trans ?_ (ConcreteCategory.comp_apply _ _ _).symm
            refine Eq.trans ?_ (congrArg _ (one_smul S.A (sc (n + 1))).symm)
            refine (hsc n).symm.trans ?_
            exact (ConcreteCategory.congr_hom
              (Functor.ofOpSequence_map_homOfLE_succ _ n) (sc (n + 1))).symm) }
    let x : S.M := (limit.lift S.globalSectionsSystem cone).hom (1 : S.A)
    have hx : ∀ n, (limit.π S.globalSectionsSystem (op n)).hom x = sc n := fun n => by
      have h := limit.lift_π cone (op n)
      exact (congrArg (fun φ => φ.hom (1 : S.A)) h).trans (one_smul S.A (sc n))
    obtain ⟨V, t, hV, ht⟩ := exists_section_complementProj_eq A a f hcomplete F hG hfin x
    let V' : OpensNearVanishing A (Ideal.span {f}) a :=
      ⟨V, fun y hy => hV y ((Ideal.span_singleton_le_iff_mem _).1 hy)⟩
    refine ⟨V', t, Concrete.limit_ext _ _ _ fun n => ?_⟩
    refine ((ConcreteCategory.comp_apply _ _ t).symm.trans (ConcreteCategory.congr_hom
      (comparisonAt_π A (Ideal.span {f}) a F V' n) t)).trans ?_
    refine (ConcreteCategory.comp_apply _ _ t).trans ?_
    suffices hproj : ConcreteCategory.hom (projNearVanishing A (Ideal.span {f}) a F V' n) t =
        ConcreteCategory.hom (resNearVanishing A (Ideal.span {f}) a F V' n)
          (ConcreteCategory.hom (limit.π (formalSections A (Ideal.span {f}) a F) n) s) by
      refine (congrArg (ConcreteCategory.hom (inv (resNearVanishing A (Ideal.span {f}) a F V' n)))
        hproj).trans ?_
      exact (ConcreteCategory.comp_apply _ _ _).symm.trans
        ((ConcreteCategory.congr_hom (IsIso.hom_inv_id _) _).trans (ConcreteCategory.id_apply _))
    obtain ⟨n⟩ := n
    apply injective_app_hom_of_iso (e n) V
    cases n with
    | zero =>
      have := subsingleton_sections_powQuotient_zero g F V
      exact Subsingleton.elim _ _
    | succ m =>
      have e1 : ConcreteCategory.hom (Scheme.Modules.Hom.app (e (m + 1)).hom V)
          (ConcreteCategory.hom (projNearVanishing A (Ideal.span {f}) a F V' (op (m + 1))) t) =
          Scheme.Modules.Hom.app (complementProj A a f F m) V t :=
        congrArg (fun φ => ConcreteCategory.hom (Scheme.Modules.Hom.app φ V) t) (he (m + 1))
      rw [e1, ht m, hx m]
      exact presheaf_map_app_apply (e (m + 1)).hom _ _
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨(ConcreteCategory.mono_iff_injective_of_preservesPullback _).1
    (mono_comparisonMap A (Ideal.span {f}) a F), hsurj⟩

end Stacks.Algebraization

end
