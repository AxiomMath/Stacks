module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.RingTheory.LocalRing.Module
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.HenselianProjectiveSections
public import StacksFrontier.AlgebraicGeometry.Fibres.ClosedFibreSections
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffineComparison
public import StacksFrontier.RingTheory.Module.Kaplansky
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange

/-!
# Flat finite modules over a henselian base as colimits of free modules

Let `A` be a henselian local ring, `R` a finitely presented `A`-algebra, `q ⊆ R` a prime over the
maximal ideal of `A` and `M` a finite `R`-module whose localization `M_q` is flat over `A`. Then
`M_q` is the colimit of a directed system of free `A`-modules whose transition maps are injective
modulo the maximal ideal of `A`. This is the geometric half of Stacks 05U7.

The system is that of the sections of `M^~` over the affine open neighbourhoods of `q` in
`Spec R` on which they are free, inside an open neighbourhood of `q` in which every associated
point of the closed fibre generalizes `q`. Such neighbourhoods are cofinal by Stacks 05MF over a
henselian base (`AlgebraicGeometry.exists_isAffineOpen_projective_sections_of_henselian`) and
Kaplansky's theorem (Stacks 0593); the colimit of the sections over a cofinal system of
neighbourhoods is the stalk `M_q`; and the reductions of the restriction maps are injective
because a section of the kernel would be supported away from `q` on the closed fibre
(`AlgebraicGeometry.mem_smul_top_of_map_mem_smul_top`).

## Main results

* `Module.exists_directed_colimit_of_compatible_legs`: a directed system of free modules with
  compatible, jointly surjective legs detecting vanishing presents the target as its colimit.
* `AlgebraicGeometry.exists_colimit_free_of_flat_localizedModule`: the statement above.

## References

* [Stacks Project, Tag 05U7](https://stacks.math.columbia.edu/tag/05U7)
* [Stacks Project, Tag 05MF](https://stacks.math.columbia.edu/tag/05MF)
* [Stacks Project, Tag 0593](https://stacks.math.columbia.edu/tag/0593)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u uM

namespace Module

/-- A linear map between modules which pulls `q ⊆ N` back into `p ⊆ M` induces an injective map of
quotients. -/
private theorem mapQ_injective_of_mem {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {p : Submodule R M} {q : Submodule R N} {g : M →ₗ[R] N}
    (hpq : p ≤ q.comap g) (h : ∀ y, g y ∈ q → y ∈ p) : Function.Injective (p.mapQ q g hpq) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  induction z using Submodule.Quotient.induction_on with
  | H y =>
    rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hz
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h y hz)

/-- **A directed system with compatible legs is a filtered colimit.** Let `(E i, ρ)` be a directed
system of free modules over a local ring `A`, indexed by a nonempty directed preorder, whose
transition maps are injective modulo the maximal ideal, and let `ψ i : E i → N` be compatible
`A`-linear maps which are jointly surjective and such that an element killed by `ψ i` is already
killed by some transition map. Then `N` is the colimit of a directed system of free `A`-modules,
with injective reductions modulo the maximal ideal, in the joint universe of `A` and `N`. -/
theorem exists_directed_colimit_of_compatible_legs {A : Type u} [CommRing A] [IsLocalRing A]
    {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (E : ι → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module A (E i)]
    (ρ : ∀ i j, i ≤ j → E i →ₗ[A] E j)
    (hid : ∀ i (y : E i), ρ i i le_rfl y = y)
    (hcomp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) (y : E i),
      ρ j k hjk (ρ i j hij y) = ρ i k (hij.trans hjk) y)
    (hfree : ∀ i, Module.Free A (E i))
    (hred : ∀ i j (h : i ≤ j), Function.Injective
      (Submodule.mapQ (maximalIdeal A • (⊤ : Submodule A (E i)))
        (maximalIdeal A • (⊤ : Submodule A (E j))) (ρ i j h)
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (ρ i j h))))
    {N : Type uM} [AddCommGroup N] [Module A N]
    (ψ : ∀ i, E i →ₗ[A] N) (hψ : ∀ i j (h : i ≤ j) (y : E i), ψ j (ρ i j h y) = ψ i y)
    (hsurj : ∀ n : N, ∃ i y, ψ i y = n)
    (hinj : ∀ i (y : E i), ψ i y = 0 → ∃ j, ∃ h : i ≤ j, ρ i j h y = 0) :
    ∃ (I : Type (max u uM)) (_ : Preorder I) (_ : IsDirectedOrder I) (_ : Nonempty I)
      (F : I ⥤ ModuleCat.{max u uM} A) (c : Cocone F),
      (∀ i, Module.Free A (F.obj i)) ∧
      (∀ {i j : I} (f : i ⟶ j), Function.Injective
        (Submodule.mapQ
          (maximalIdeal A • (⊤ : Submodule A (F.obj i)))
          (maximalIdeal A • (⊤ : Submodule A (F.obj j)))
          (F.map f).hom
          (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (F.map f).hom))) ∧
      Nonempty (IsColimit c) ∧
      Nonempty (c.pt ≅ ModuleCat.of A (ULift.{u} N)) := by
  let I := ULift.{uM} ι
  have hdir : IsDirectedOrder I :=
    ⟨fun a b => by
      obtain ⟨c, h1, h2⟩ := directed_of (· ≤ ·) a.down b.down
      exact ⟨⟨c⟩, h1, h2⟩⟩
  let e (i : ι) : ULift.{uM} (E i) ≃ₗ[A] E i := ULift.moduleEquiv
  let τ (i j : I) (h : i ≤ j) : ULift.{uM} (E i.down) →ₗ[A] ULift.{uM} (E j.down) :=
    (e j.down).symm.toLinearMap ∘ₗ ρ i.down j.down h ∘ₗ (e i.down).toLinearMap
  let F : I ⥤ ModuleCat.{max u uM} A :=
    { obj := fun i => ModuleCat.of A (ULift.{uM} (E i.down))
      map := fun {i j} h => ModuleCat.ofHom (τ i j (leOfHom h))
      map_id := fun i => by
        ext y
        exact hid i.down y.down
      map_comp := fun {i j k} f g => by
        ext y
        exact (hcomp i.down j.down k.down _ _ y.down).symm }
  let eN : ULift.{u} N ≃ₗ[A] N := ULift.moduleEquiv
  let c : Cocone F :=
    { pt := ModuleCat.of A (ULift.{u} N)
      ι :=
        { app := fun i => ModuleCat.ofHom
            (eN.symm.toLinearMap ∘ₗ ψ i.down ∘ₗ (e i.down).toLinearMap)
          naturality := fun {i j} f => by
            ext y
            exact ULift.ext (hψ i.down j.down (leOfHom f : i ≤ j) y.down) } }
  refine ⟨I, inferInstance, hdir, inferInstance, F, c, fun i => ?_, fun {i j} f => ?_, ?_,
    ⟨Iso.refl _⟩⟩
  · have := hfree i.down
    exact Module.Free.of_equiv (e i.down).symm
  · have hmem : ∀ (k : I) (y : ULift.{uM} (E k.down)), e k.down y ∈
        maximalIdeal A • (⊤ : Submodule A (E k.down)) ↔
          y ∈ maximalIdeal A • (⊤ : Submodule A (ULift.{uM} (E k.down))) := by
      intro k y
      have h : (maximalIdeal A • (⊤ : Submodule A (ULift.{uM} (E k.down)))).map
          (e k.down).toLinearMap = maximalIdeal A • (⊤ : Submodule A (E k.down)) := by
        rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
      rw [← h, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
    refine mapQ_injective_of_mem _ fun y hy => (hmem i y).mp ((Submodule.Quotient.mk_eq_zero _).mp
      ((injective_iff_map_eq_zero _).1 (hred i.down j.down (leOfHom f : i ≤ j)) _ ?_))
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (hmem j _).mpr hy
  · have := hdir
    have : PreservesColimit F (forget₂ (ModuleCat.{max u uM} A) AddCommGrpCat.{max u uM}) :=
      preservesColimit_of_preserves_colimit_cocone
        (ModuleCat.FilteredColimits.colimitCoconeIsColimit.{max u uM, u} F)
        (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit.{max u uM, max u uM}
          (F ⋙ forget₂ _ _))
    have : PreservesColimit F (forget (ModuleCat.{max u uM} A)) :=
      comp_preservesColimit (forget₂ (ModuleCat.{max u uM} A) AddCommGrpCat.{max u uM})
        (forget AddCommGrpCat.{max u uM})
    have : ReflectsColimit F (forget (ModuleCat.{max u uM} A)) :=
      reflectsColimit_of_reflectsIsomorphisms F _
    refine ⟨isColimitOfReflects (forget (ModuleCat.{max u uM} A)) ?_⟩
    refine Types.FilteredColimit.isColimitOf' _ _ (fun n => ?_) (fun i y₁ y₂ hy => ?_)
    · obtain ⟨i, y, hy⟩ := hsurj n.down
      exact ⟨⟨i⟩, ⟨y⟩, congrArg ULift.up hy.symm⟩
    · change ULift.{uM} (E i.down) at y₁ y₂
      have hy' : ψ i.down y₁.down = ψ i.down y₂.down := congrArg ULift.down hy
      have h0 : ψ i.down (y₁.down - y₂.down) = 0 := by
        rw [map_sub, hy', sub_self]
      obtain ⟨j, hij, hj⟩ := hinj i.down _ h0
      refine ⟨⟨j⟩, homOfLE hij, ?_⟩
      apply ULift.ext
      change ρ i.down j hij y₁.down = ρ i.down j hij y₂.down
      rwa [← sub_eq_zero, ← map_sub]

/-- A module over a local ring `A` is free if it is projective over a ring `B` isomorphic to `A`,
the two actions agreeing along the isomorphism. -/
private theorem free_of_projective_of_ringEquiv {A B M : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [AddCommGroup M] [Module A M] [Module B M] (σ : A ≃+* B)
    (hσ : ∀ (a : A) (m : M), a • m = σ a • m) [Module.Projective B M] : Module.Free A M := by
  let : RingHomInvPair (σ : A →+* B) (σ.symm : B →+* A) := ⟨σ.symm_comp, σ.comp_symm⟩
  let : RingHomInvPair (σ.symm : B →+* A) (σ : A →+* B) := ⟨σ.comp_symm, σ.symm_comp⟩
  have : Module.Projective A M := Module.Projective.of_equiv
    (({ toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
        map_add' := fun _ _ => rfl, map_smul' := hσ } : M ≃ₛₗ[(σ : A →+* B)] M).symm)
  exact Module.free_of_projective_of_isLocalRing

end Module

namespace AlgebraicGeometry

/-- For a local ring `A`, the map from the global sections of `Spec A` to the global sections of
the spectrum of the residue field at the closed point is surjective. -/
theorem fromSpecResidueField_closedPoint_appTop_surjective (A : Type u) [CommRing A]
    [IsLocalRing A] :
    Function.Surjective
      ((Spec (CommRingCat.of A)).fromSpecResidueField (closedPoint A)).appTop.hom := by
  set S := Spec (CommRingCat.of A)
  have hiso : IsIso (S.fromSpecStalk (closedPoint A)) := by
    rw [← Spec_stalkClosedPointIso]
    infer_instance
  change Function.Surjective (Spec.map (S.residue (closedPoint A)) ≫
    S.fromSpecStalk (closedPoint A)).appTop.hom
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  have : IsIso (S.fromSpecStalk (closedPoint A)).appTop :=
    inferInstanceAs (IsIso ((S.fromSpecStalk (closedPoint A)).app ⊤))
  refine Function.Surjective.comp ?_ (ConcreteCategory.bijective_of_isIso _).2
  have h' : (Spec.map (S.residue (closedPoint A))).appTop =
      (Scheme.ΓSpecIso _).hom ≫ S.residue (closedPoint A) ≫ (Scheme.ΓSpecIso _).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality (S.residue (closedPoint A)), Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [h', CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso _).2.comp
    ((Scheme.residue_surjective S _).comp (ConcreteCategory.bijective_of_isIso _).2)

/-- For a local ring `A` and a point `s` of `Spec A` at which the residue map on global sections
is surjective, `a ∈ A` lies in the maximal ideal iff its global section vanishes in `κ(s)`. -/
private theorem mem_maximalIdeal_iff_ΓSpecIso_inv_mem_ker {A : Type u} [CommRing A] [IsLocalRing A]
    (s : Spec (CommRingCat.of A))
    (hsurj : Function.Surjective ((Spec (CommRingCat.of A)).fromSpecResidueField s).appTop.hom)
    (a : A) :
    a ∈ maximalIdeal A ↔ (Scheme.ΓSpecIso (CommRingCat.of A)).inv a ∈
      RingHom.ker ((Spec (CommRingCat.of A)).fromSpecResidueField s).appTop.hom := by
  let σ := (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
  let κ := (Spec (CommRingCat.of A)).residueField s
  let h' : A →+* κ := (Scheme.ΓSpecIso κ).hom.hom.comp
    (((Spec (CommRingCat.of A)).fromSpecResidueField s).appTop.hom.comp (σ : A →+* _))
  have hs' : Function.Surjective h' :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso κ).hom).2.comp
      (hsurj.comp σ.surjective)
  rw [← IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective h' hs'),
    RingHom.mem_ker, RingHom.mem_ker]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso κ).hom).1

/-- The germ maps of `M^~` on `Spec R` are `R`-linear. -/
theorem tilde_germ_smul {R : CommRingCat.{u}} (M : ModuleCat.{u} R) {U : (Spec R).Opens}
    {x : Spec R} (hx : x ∈ U) (r : R) (s : Γ(tilde M, U)) :
    letI : Module R ((tilde M).presheaf.stalk x) :=
      AlgebraicGeometry.tilde.instModuleCarrierCarrierStalkAbPresheaf M x
    (tilde M).presheaf.germ U x hx (r • s) = r • (tilde M).presheaf.germ U x hx s := by
  rw [Scheme.Modules.smul_Spec_def]
  refine (PresheafOfModules.germ_smul (tilde M).val x U hx
    ((Spec R).presheaf.map U.leTop.op ((Scheme.ΓSpecIso R).inv r)) s).trans ?_
  have h2 : (Spec R).presheaf.germ U x hx
      ((Spec R).presheaf.map U.leTop.op ((Scheme.ΓSpecIso R).inv r)) =
      (Spec R).presheaf.germ ⊤ x trivial ((Scheme.ΓSpecIso R).inv r) :=
    (Spec R).presheaf.germ_res_apply U.leTop x hx _
  exact (congrArg (fun t => t • (tilde M).presheaf.germ U x hx s) h2).trans rfl

/-- For `Spec φ : Spec B ⟶ Spec A`, the scalar action of a global section of `Spec A` on the
sections of a module over an open of `Spec B` is the action of its image in `B`. -/
theorem smul_appLE_SpecMap_ΓSpecIso_inv {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (F : (Spec B).Modules) (U : (Spec B).Opens) (e : U ≤ Spec.map φ ⁻¹ᵁ ⊤) (a : A)
    (s : Γ(F, U)) :
    (Spec.map φ).appLE ⊤ U e ((Scheme.ΓSpecIso A).inv a) • s = φ a • s := by
  rw [Scheme.Modules.smul_Spec_def]
  congr 1
  have h := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality φ)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
  rw [Scheme.Hom.appLE, ConcreteCategory.comp_apply]
  exact congrArg (ConcreteCategory.hom ((Spec B).presheaf.map U.leTop.op)) h.symm

/-- Membership in `I • ⊤` is unchanged when the scalars are transported along a ring
isomorphism carrying `I` onto `J`. -/
theorem mem_smul_top_iff_of_ringEquiv {A B M : Type*} [CommRing A] [CommRing B]
    [AddCommGroup M] [Module A M] [Module B M] (σ : A ≃+* B)
    (hσ : ∀ (a : A) (y : M), a • y = σ a • y) (I : Ideal A) (J : Ideal B)
    (hIJ : ∀ a, a ∈ I ↔ σ a ∈ J) (x : M) :
    x ∈ I • (⊤ : Submodule A M) ↔ x ∈ J • (⊤ : Submodule B M) := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · refine Submodule.smul_induction_on (p := fun y => y ∈ J • (⊤ : Submodule B M)) hx
      (fun a ha m _ => ?_) (fun _ _ h1 h2 => Submodule.add_mem _ h1 h2)
    rw [hσ]
    exact Submodule.smul_mem_smul ((hIJ a).mp ha) trivial
  · refine Submodule.smul_induction_on (p := fun y => y ∈ I • (⊤ : Submodule A M)) hx
      (fun b hb m _ => ?_) (fun _ _ h1 h2 => Submodule.add_mem _ h1 h2)
    have hb' : σ.symm b ∈ I := (hIJ _).mpr (by rwa [RingEquiv.apply_symm_apply])
    rw [show b • m = σ.symm b • m by rw [hσ, RingEquiv.apply_symm_apply]]
    exact Submodule.smul_mem_smul hb' trivial

/-- **The geometric half of Stacks 05U7, over an algebra of finite presentation.** Let `A` be a
henselian local ring, let `R` be a finitely presented `A`-algebra, let `q ⊆ R` be a prime over
the maximal ideal of `A` and let `M` be a finite `R`-module whose localization `M_q` is flat over
`A`. Then any `A`-module isomorphic to `M_q` is the colimit of a directed system of free
`A`-modules whose transition maps are injective modulo the maximal ideal of `A`.

The system is that of the sections of `M^~` over the affine open neighbourhoods `U` of `q` in
`Spec R` with free sections, in a neighbourhood of `q` in which every associated point of the
closed fibre generalizes `q`. -/
theorem exists_colimit_free_of_flat_localizedModule {A : Type u} [CommRing A]
    [HenselianLocalRing A] {R : Type u} [CommRing R] [Algebra A R] [Algebra.FinitePresentation A R]
    (q : Ideal R) [q.IsPrime] (hq : q.comap (algebraMap A R) = maximalIdeal A)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module A M]
    [IsScalarTower A R M] (hflat : Module.Flat A (LocalizedModule q.primeCompl M))
    {N : Type uM} [AddCommGroup N] [Module A N]
    (eN : LocalizedModule q.primeCompl M ≃ₗ[A] N) :
    ∃ (I : Type (max u uM)) (_ : Preorder I) (_ : IsDirectedOrder I) (_ : Nonempty I)
      (F : I ⥤ ModuleCat.{max u uM} A) (c : Cocone F),
      (∀ i, Module.Free A (F.obj i)) ∧
      (∀ {i j : I} (f : i ⟶ j), Function.Injective
        (Submodule.mapQ
          (maximalIdeal A • (⊤ : Submodule A (F.obj i)))
          (maximalIdeal A • (⊤ : Submodule A (F.obj j)))
          (F.map f).hom
          (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (F.map f).hom))) ∧
      Nonempty (IsColimit c) ∧
      Nonempty (c.pt ≅ ModuleCat.of A (ULift.{u} N)) := by
  classical
  set AA := CommRingCat.of A
  set RR := CommRingCat.of R
  set φ : AA ⟶ RR := CommRingCat.ofHom (algebraMap A R) with hφ
  set S := Spec AA
  set f : Spec RR ⟶ S := Spec.map φ with hf
  set MM : ModuleCat RR := ModuleCat.of R M with hMM
  set F : (Spec RR).Modules := tilde MM with hF
  set x : Spec RR := (⟨q, inferInstance⟩ : PrimeSpectrum R) with hx
  have : LocallyOfFinitePresentation f := by
    rw [hf, HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  have : F.IsFiniteType := (tilde_isFiniteType_iff _).mpr (inferInstanceAs (Module.Finite R M))
  have hfx : f x = closedPoint A := PrimeSpectrum.ext hq
  have hflatx : IsFlatOverAt f.toLRSHom.toShHom F x :=
    (isFlatOverAt_spec_tilde_iff_flat_localizedModule φ MM rfl x).mpr hflat
  -- the base
  have : HenselianLocalRing (S.presheaf.stalk (f x)) := by
    rw [hfx]
    exact HenselianLocalRing.of_ringEquiv (stalkClosedPointIso AA).commRingCatIsoToRingEquiv.symm
  have : IsIso (S.fromSpecStalk (f x)) := by
    rw [hfx, ← Spec_stalkClosedPointIso]
    infer_instance
  have hsurj : Function.Surjective (S.fromSpecResidueField (f x)).appTop.hom := by
    rw [hfx]
    exact fromSpecResidueField_closedPoint_appTop_surjective A
  -- the neighbourhood in which the associated points of the closed fibre generalize `x`
  obtain ⟨X₀, hxX₀, hAss⟩ := exists_opens_associatedPoints_fiber_specializes f F x
  -- the scalars
  set σ : A ≃+* Γ(S, ⊤) := (Scheme.ΓSpecIso AA).symm.commRingCatIsoToRingEquiv with hσ
  let ψU : ∀ U : (Spec RR).Opens, A →+* Γ(Spec RR, U) := fun U =>
    (f.appLE ⊤ U (by simp)).hom.comp (σ : A →+* Γ(S, ⊤))
  let P : (Spec RR).Opens → Prop := fun U => IsAffineOpen U ∧ x ∈ U ∧ U ≤ X₀ ∧
    (let : Module A Γ(F, U) := Module.compHom _ (ψU U)
     Module.Free A Γ(F, U))
  have hcof : ∀ V : (Spec RR).Opens, x ∈ V → ∃ U, U ≤ V ∧ P U := by
    intro V hxV
    obtain ⟨U, hUaff, hxU, hUV, hproj⟩ :=
      exists_isAffineOpen_projective_sections_of_henselian f F x rfl hflatx (V ⊓ X₀) ⟨hxV, hxX₀⟩
    refine ⟨U, hUV.trans inf_le_left, hUaff, hxU, hUV.trans inf_le_right, ?_⟩
    let : Module Γ(S, ⊤) Γ(F, U) := Module.compHom _ (f.appLE ⊤ U (by simp)).hom
    let : Module A Γ(F, U) := Module.compHom _ (ψU U)
    exact Module.free_of_projective_of_ringEquiv σ fun _ _ => rfl
  -- the index: affine neighbourhoods inside `X₀` with free sections, ordered by reverse inclusion
  let ι := {U : ((Spec RR).Opens)ᵒᵈ // P (OrderDual.ofDual U)}
  let O : ι → (Spec RR).Opens := fun U => OrderDual.ofDual U.1
  have hle : ∀ U V : ι, U ≤ V → O V ≤ O U := fun U V h => h
  have : Nonempty ι := by
    obtain ⟨U, -, hU⟩ := hcof X₀ hxX₀
    exact ⟨⟨OrderDual.toDual U, hU⟩⟩
  have : IsDirectedOrder ι := ⟨fun U V => by
    obtain ⟨W, hW, hPW⟩ := hcof (O U ⊓ O V) ⟨U.2.2.1, V.2.2.1⟩
    exact ⟨⟨OrderDual.toDual W, hPW⟩, (hW.trans inf_le_left : W ≤ O U),
      (hW.trans inf_le_right : W ≤ O V)⟩⟩
  let instE : ∀ U : ι, Module A Γ(F, O U) := fun U => Module.compHom _ (ψU (O U))
  -- restriction is `A`-linear
  have hψres (U V : (Spec RR).Opens) (h : V ≤ U) (a : A) :
      (Spec RR).presheaf.map (homOfLE h).op (ψU U a) = ψU V a :=
    congrArg (fun φ => φ.hom (σ a))
      (Scheme.Hom.appLE_map f (U := ⊤) (V := U) (by simp) (homOfLE h).op)
  let ρ : ∀ U V : ι, U ≤ V → Γ(F, O U) →ₗ[A] Γ(F, O V) := fun U V h =>
    { toFun := F.presheaf.map (homOfLE (hle U V h)).op
      map_add' := map_add _
      map_smul' := fun a s => by
        change F.presheaf.map (homOfLE (hle U V h)).op (ψU (O U) a • s) =
          ψU (O V) a • F.presheaf.map (homOfLE (hle U V h)).op s
        rw [← hψres (O U) (O V) (hle U V h) a]
        exact F.val.map_smul (homOfLE (hle U V h)).op (ψU (O U) a) s }
  have hid : ∀ U (y : Γ(F, O U)), ρ U U le_rfl y = y := by
    intro U y
    change F.presheaf.map (homOfLE (hle U U le_rfl)).op y = y
    rw [show (homOfLE (hle U U le_rfl)).op = 𝟙 _ from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id]
    rfl
  have hcomp : ∀ U V W (hUV : U ≤ V) (hVW : V ≤ W) (y : Γ(F, O U)),
      ρ V W hVW (ρ U V hUV y) = ρ U W (hUV.trans hVW) y := by
    intro U V W hUV hVW y
    change F.presheaf.map (homOfLE (hle V W hVW)).op
        (F.presheaf.map (homOfLE (hle U V hUV)).op y) =
      F.presheaf.map (homOfLE (hle U W (hUV.trans hVW))).op y
    rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
    rfl
  -- the legs: the germ at `x`, read in `M_q` and then in `N`
  let : Module RR ((tilde MM).presheaf.stalk x) :=
    AlgebraicGeometry.tilde.instModuleCarrierCarrierStalkAbPresheaf MM x
  have : IsLocalizedModule x.asIdeal.primeCompl (tilde.toStalk MM x).hom :=
    tilde.instIsLocalizedModuleCarrierCarrierOfCarrierStalkAbPresheafPrimeComplAsIdealHomToStalk
      MM x
  let es : (tilde MM).presheaf.stalk x ≃ₗ[RR] LocalizedModule q.primeCompl M :=
    (IsLocalizedModule.iso x.asIdeal.primeCompl (tilde.toStalk MM x).hom).symm
  have hAR (a : A) (z : LocalizedModule q.primeCompl M) :
      (show RR from algebraMap A R a) • z = a • z := by
    induction z using LocalizedModule.induction_on with
    | h m t => rw [LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, algebraMap_smul]
  let ψ : ∀ U : ι, Γ(F, O U) →ₗ[A] N := fun U =>
    { toFun := fun t => eN (es (F.presheaf.germ (O U) x U.2.2.1 t))
      map_add' := fun t t' => by simp only [map_add]
      map_smul' := fun a t => by
        change eN (es (F.presheaf.germ (O U) x U.2.2.1 (ψU (O U) a • t))) =
          a • eN (es (F.presheaf.germ (O U) x U.2.2.1 t))
        let : Module RR Γ(F, O U) := open Scheme.Modules in
          instModuleCarrierCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecAbPresheafOp
        have k1 : ψU (O U) a • t = (show RR from algebraMap A R a) • t :=
          smul_appLE_SpecMap_ΓSpecIso_inv φ F (O U) _ a t
        have k2 : F.presheaf.germ (O U) x U.2.2.1 ((show RR from algebraMap A R a) • t) =
            (show RR from algebraMap A R a) • F.presheaf.germ (O U) x U.2.2.1 t :=
          tilde_germ_smul MM U.2.2.1 (show RR from algebraMap A R a) t
        rw [k1, k2, map_smul, hAR, map_smul] }
  have hψ : ∀ U V (h : U ≤ V) (y : Γ(F, O U)), ψ V (ρ U V h y) = ψ U y := by
    intro U V h y
    change eN (es (F.presheaf.germ (O V) x V.2.2.1
      (F.presheaf.map (homOfLE (hle U V h)).op y))) = eN (es (F.presheaf.germ (O U) x U.2.2.1 y))
    rw [TopCat.Presheaf.germ_res_apply]
  have hlsurj : ∀ n : N, ∃ U y, ψ U y = n := by
    intro n
    obtain ⟨V, hxV, t, ht⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf (es.symm (eN.symm n))
    obtain ⟨U, hUV, hPU⟩ := hcof V hxV
    refine ⟨⟨OrderDual.toDual U, hPU⟩, F.presheaf.map (homOfLE hUV).op t, ?_⟩
    change eN (es (F.presheaf.germ U x hPU.2.1 (F.presheaf.map (homOfLE hUV).op t))) = n
    rw [TopCat.Presheaf.germ_res_apply, ht, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  have hinj : ∀ U (y : Γ(F, O U)), ψ U y = 0 → ∃ V, ∃ h : U ≤ V, ρ U V h y = 0 := by
    intro U y hy
    have h0 : F.presheaf.germ (O U) x U.2.2.1 y = F.presheaf.germ (O U) x U.2.2.1 0 := by
      rw [map_zero]
      exact (LinearEquiv.map_eq_zero_iff _).mp ((LinearEquiv.map_eq_zero_iff _).mp hy)
    obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq F.presheaf x U.2.2.1 U.2.2.1 y 0 h0
    obtain ⟨V, hVW, hPV⟩ := hcof W hxW
    refine ⟨⟨OrderDual.toDual V, hPV⟩, (hVW.trans (leOfHom iU) : V ≤ O U), ?_⟩
    change F.presheaf.map (homOfLE (hVW.trans (leOfHom iU))).op y = 0
    rw [show (homOfLE (hVW.trans (leOfHom iU))).op = iU.op ≫ (homOfLE hVW).op from
      Subsingleton.elim _ _, CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply, hW,
      map_zero, map_zero]
  -- the kernel of `Γ(S, 𝒪_S) → κ(s)` is the maximal ideal
  set J := RingHom.ker (S.fromSpecResidueField (f x)).appTop.hom with hJ
  have hIJ : ∀ a, a ∈ maximalIdeal A ↔ σ a ∈ J :=
    mem_maximalIdeal_iff_ΓSpecIso_inv_mem_ker (f x) hsurj
  have hred : ∀ U V (h : U ≤ V), Function.Injective
      (Submodule.mapQ (maximalIdeal A • (⊤ : Submodule A Γ(F, O U)))
        (maximalIdeal A • (⊤ : Submodule A Γ(F, O V))) (ρ U V h)
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (ρ U V h))) := by
    intro U V h
    refine Module.mapQ_injective_of_mem _ fun y hy => ?_
    let : Module Γ(S, ⊤) Γ(F, O V) := Module.compHom _ (f.appLE ⊤ (O V) (by simp)).hom
    let : Module Γ(S, ⊤) Γ(F, O U) := Module.compHom _ (f.appLE ⊤ (O U) (by simp)).hom
    exact (mem_smul_top_iff_of_ringEquiv σ (fun _ _ => rfl) _ J hIJ _).mpr
      (mem_smul_top_of_map_mem_smul_top f x hsurj F U.2.1 V.2.1 (hle U V h) V.2.2.1
        (fun z hz hzU => hAss z hz (U.2.2.2.1 hzU)) y
        ((mem_smul_top_iff_of_ringEquiv σ (fun _ _ => rfl) _ J hIJ _).mp hy))
  exact Module.exists_directed_colimit_of_compatible_legs (fun U : ι => Γ(F, O U)) ρ hid hcomp
    (fun U => U.2.2.2.2) hred ψ hψ hlsurj hinj

end AlgebraicGeometry
